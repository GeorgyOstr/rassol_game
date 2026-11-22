// RASSOL: CYBER BRINE RUNNER — прототип неонового платформера.
// Банка рассола бегает по крышам киберпанк-города и кидается овощами в зверьков.
// SDL2 only: вся графика — векторные примитивы + аддитивное свечение,
// вся музыка и звуки синтезируются в аудио-колбэке.
#include <SDL2/SDL.h>

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <string>
#include <vector>

static constexpr int SW = 1280, SH = 720;
static constexpr float TS = 40.f;
static constexpr float PI = 3.14159265f;

static SDL_Color C(int r, int g, int b, int a = 255) { return SDL_Color{(Uint8)r, (Uint8)g, (Uint8)b, (Uint8)a}; }
static float clampf(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }
static float lerpf(float a, float b, float t) { return a + (b - a) * t; }

static std::mt19937 gen(1337);
static float frand(float a, float b) { return std::uniform_real_distribution<float>(a, b)(gen); }
static int irand(int a, int b) { return std::uniform_int_distribution<int>(a, b)(gen); }

// ============================================================================
// AUDIO: процедурная нагнетающая музыка (D minor, 132 BPM) + синт-звуки
// ============================================================================
namespace snd {
constexpr int SR = 48000;
constexpr float BPM = 132.f;
std::atomic<float> intensity{0.3f};
std::atomic<bool> musicOn{true};
SDL_AudioDeviceID dev = 0;

struct Voice { bool on = false; float t = 0, dur = 0, delay = 0, f = 0, fmul = 1, noise = 0, vol = 0, ph = 0; int wave = 0; };
Voice voices[48];
// SFX requests go through a lock-free single-producer/single-consumer ring,
// so the game thread never blocks on SDL_LockAudioDevice while the callback runs.
constexpr unsigned QN = 64;
Voice queue[QN];
std::atomic<unsigned> qHead{0}, qTail{0};

static uint32_t rs = 0x9E3779B9u;
inline float nrand() { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return (float)(rs & 0xFFFFFF) / 8388608.f - 1.f; }
inline float mtof(float m) { return 440.f * powf(2.f, (m - 69.f) / 12.f); }
inline float frac(float x) { return x - floorf(x); }

struct SVF {
    float lo = 0, bp = 0, hp = 0;
    void run(float in, float fc, float q) {
        float f = 2.f * sinf(PI * clampf(fc, 20.f, SR * 0.15f) / SR);
        hp = in - lo - q * bp; bp += f * hp; lo += f * bp;
    }
};

struct Music {
    long stepCount = -1; int sampleInStep = 0;
    int step = 0, bar = 0;
    float Is = 0.3f;
    float kickT = 9, snT = 9, hatT = 9, hatDecay = 60, hatVol = 0, bassT = 9, arpT = 9;
    float kickPh = 0, bassPh = 0, subPh = 0, arpPh = 0, padPh[6] = {}, dronePh = 0, lfo = 0, time = 0;
    float bassF = 50, arpF = 400, padF[3] = {100, 120, 150}, droneF = 300;
    float arpGain = 0, snOn = 0;
    SVF bassFl, snFl, hatFl, arpFl, padFl, riserFl;
    float dL[SR] = {}, dR[SR] = {}; int dpos = 0;

    void onStep() {
        stepCount++;
        step = (int)(stepCount % 16);
        bar = (int)((stepCount / 16) % 4);
        static const int roots[4] = {38, 34, 31, 33};  // D  Bb  G  A
        int root = roots[bar];
        int third = (bar == 3) ? 4 : 3;
        if (step % 4 == 0) { kickT = 0; kickPh = 0; }
        else { bassT = 0; bassF = mtof((float)root + ((step % 4 == 2) ? 12.f : 0.f)); }
        if ((step == 4 || step == 12) && Is > 0.2f) snT = 0;
        if (step == 15 && bar == 3 && Is > 0.6f) snT = 0;  // fill
        bool hat16 = Is > 0.55f;
        if (hat16 || step % 2 == 0) {
            hatT = 0;
            hatDecay = (step % 4 == 2) ? 14.f : 70.f;
            hatVol = (step % 4 == 2) ? 0.8f : (step % 2 ? 0.35f : 0.5f);
        }
        static const int arpSeq[8] = {0, 1, 2, 3, 4, 2, 3, 1};
        int notes[5] = {0, third, 7, 12, third + 12};
        arpT = 0; arpF = mtof((float)(root + 24 + notes[arpSeq[step % 8]]));
        if (step == 0) {
            padF[0] = mtof((float)root + 12); padF[1] = mtof((float)(root + 12 + third)); padF[2] = mtof((float)root + 19);
            droneF = mtof((float)root + 36);
        }
    }

    void render(float I, float& L, float& R) {
        const int SPS = (int)(SR * 60.f / BPM / 4.f);
        const float dt = 1.f / SR;
        if (sampleInStep == 0) onStep();
        float stepFrac = (float)sampleInStep / SPS;
        sampleInStep = (sampleInStep + 1) % SPS;
        Is += (I - Is) * 0.00003f;
        time += dt;

        // kick
        kickT += dt;
        float kf = 44.f + 130.f * expf(-kickT * 32.f);
        kickPh += kf * dt;
        float kick = kickT < 0.6f ? sinf(2 * PI * kickPh) * expf(-kickT * 6.5f) : 0.f;
        kick += (kickT < 0.004f ? nrand() * 0.4f : 0.f);
        float duck = 1.f - 0.8f * expf(-kickT * 9.f);

        // rolling bass
        bassT += dt;
        float benv = expf(-bassT * 10.f);
        bassPh += bassF * dt; subPh += bassF * 0.5f * dt;
        float saw = 2.f * frac(bassPh) - 1.f;
        bassFl.run(saw, 110.f + (250.f + 1700.f * Is) * benv, 0.35f);
        float bass = bassFl.lo * benv + sinf(2 * PI * subPh) * 0.5f * expf(-bassT * 5.f);

        // snare
        snT += dt;
        snFl.run(nrand(), 1900.f, 0.7f);
        float snare = (snFl.bp * 1.2f + sinf(2 * PI * 185.f * snT) * 0.5f * expf(-snT * 35.f)) * expf(-snT * 15.f);
        if (snT > 0.5f) snare = 0;

        // hats
        hatT += dt;
        hatFl.run(nrand(), 7000.f, 0.5f);
        float hat = hatFl.hp * expf(-hatT * hatDecay) * hatVol;

        // arp
        arpT += dt;
        arpPh += arpF * dt;
        float sq = frac(arpPh) < 0.5f ? 1.f : -1.f;
        arpFl.run(sq, 900.f + 3000.f * Is * expf(-arpT * 8.f), 0.5f);
        arpGain += ((Is > 0.45f ? 1.f : 0.f) - arpGain) * 0.00005f;
        float arp = arpFl.lo * expf(-arpT * 13.f) * arpGain;

        // pad (detuned saws)
        lfo += dt * 0.13f;
        float padIn = 0;
        for (int k = 0; k < 3; k++) {
            padPh[k * 2] += padF[k] * 1.003f * dt; padPh[k * 2 + 1] += padF[k] * 0.997f * dt;
            padIn += (2.f * frac(padPh[k * 2]) - 1.f) + (2.f * frac(padPh[k * 2 + 1]) - 1.f);
        }
        padFl.run(padIn * 0.15f, 600.f + 400.f * sinf(2 * PI * lfo) + 600.f * Is, 0.8f);
        float pad = padFl.lo;

        // eerie drone
        dronePh += droneF * (1.f + 0.004f * sinf(2 * PI * 5.f * time)) * dt;
        float drone = sinf(2 * PI * dronePh) * 0.035f * (0.4f + Is) * (0.6f + 0.4f * sinf(2 * PI * 0.25f * time));

        // riser on the last bar of the loop
        float riser = 0;
        if (bar == 3) {
            float p = (step + stepFrac) / 16.f;
            riserFl.run(nrand(), 400.f + 6500.f * p, 0.6f);
            riser = riserFl.bp * p * p * 0.25f * (0.3f + Is);
        }

        float send = arp * 0.5f + snare * 0.25f;
        int rp = (dpos - 3 * SPS + SR) % SR;
        float rl = dL[rp], rr = dR[rp];
        dL[dpos] = send + rr * 0.45f; dR[dpos] = rl * 0.45f;
        dpos = (dpos + 1) % SR;

        float core = kick * 0.85f + (bass * 0.42f + pad * 0.55f + drone) * duck + snare * 0.32f + riser;
        L = core + hat * 0.10f + arp * 0.13f + rl * 0.35f;
        R = core + hat * 0.14f + arp * 0.10f + rr * 0.35f;
    }
};
Music* M = nullptr;

void callback(void*, Uint8* stream, int len) {
    float* out = (float*)stream;
    int n = len / (int)(sizeof(float) * 2);
    float I = intensity.load();
    bool mOn = musicOn.load();
    const float dt = 1.f / SR;
    unsigned qt = qTail.load(std::memory_order_relaxed), qh = qHead.load(std::memory_order_acquire);
    for (; qt != qh; qt++) {
        for (auto& v : voices) if (!v.on) { v = queue[qt % QN]; break; }
    }
    qTail.store(qt, std::memory_order_release);
    for (int i = 0; i < n; i++) {
        float L = 0, R = 0;
        M->render(I, L, R);
        if (!mOn) { L = R = 0; }
        float s = 0;
        for (auto& v : voices) {
            if (!v.on) continue;
            if (v.delay > 0) { v.delay -= dt; continue; }
            float p = v.t / v.dur;
            if (p >= 1.f) { v.on = false; continue; }
            v.ph += v.f * dt;
            v.f *= v.fmul;
            v.ph -= floorf(v.ph);
            float o;
            if (v.wave == 0) o = sinf(2 * PI * v.ph);
            else if (v.wave == 1) o = frac(v.ph) < 0.5f ? 1.f : -1.f;
            else o = 2.f * frac(v.ph) - 1.f;
            o = o * (1.f - v.noise) + nrand() * v.noise;
            float env = (1.f - p) * (1.f - p) * std::min(1.f, v.t * 300.f);
            s += o * env * v.vol;
            v.t += dt;
        }
        L += s; R += s;
        out[i * 2] = tanhf(L * 1.1f) * 0.8f;
        out[i * 2 + 1] = tanhf(R * 1.1f) * 0.8f;
    }
}

void play(float f0, float f1, float dur, int wave, float noise, float vol, float delay = 0) {
    if (!dev) return;
    unsigned h = qHead.load(std::memory_order_relaxed);
    if (h - qTail.load(std::memory_order_acquire) >= QN) return;  // queue full: drop
    queue[h % QN] = Voice{true, 0, dur, delay, f0, powf(f1 / f0, 1.f / (dur * SR)), noise, vol, 0, wave};
    qHead.store(h + 1, std::memory_order_release);
}

void init() {
    M = new Music();
    SDL_AudioSpec want{}, have{};
    want.freq = SR; want.format = AUDIO_F32SYS; want.channels = 2; want.samples = 1024; want.callback = callback;
    dev = SDL_OpenAudioDevice(nullptr, 0, &want, &have, 0);
    if (!dev) { fprintf(stderr, "audio: %s\n", SDL_GetError()); return; }
    SDL_PauseAudioDevice(dev, 0);
}
}  // namespace snd

static void sfxThrow() { snd::play(900, 280, 0.12f, 1, 0.25f, 0.18f); }
static void sfxJump() { snd::play(260, 720, 0.14f, 0, 0.05f, 0.25f); }
static void sfxHit() { snd::play(320, 80, 0.12f, 1, 0.55f, 0.25f); }
static void sfxKill() { snd::play(700, 60, 0.32f, 2, 0.35f, 0.3f); snd::play(1400, 400, 0.12f, 1, 0.f, 0.1f, 0.03f); }
static void sfxHurt() { snd::play(160, 40, 0.45f, 2, 0.5f, 0.4f); }
static void sfxBoom() { snd::play(140, 25, 0.6f, 0, 0.85f, 0.55f); }
static void sfxBounce() { snd::play(500, 900, 0.06f, 0, 0.f, 0.12f); }
static void sfxLand() { snd::play(120, 60, 0.07f, 0, 0.6f, 0.12f); }
static void sfxSwitch() { snd::play(1200, 1600, 0.05f, 1, 0.f, 0.08f); }
static void sfxWin() {
    float n[6] = {62, 65, 69, 74, 77, 81};
    for (int i = 0; i < 6; i++) snd::play(snd::mtof(n[i]), snd::mtof(n[i]), 0.35f, 1, 0.f, 0.14f, i * 0.09f);
}

// ============================================================================
// RENDER HELPERS
// ============================================================================
static SDL_Renderer* R = nullptr;
static SDL_Texture *texGlow = nullptr, *texBar = nullptr, *texOverlay = nullptr;
static SDL_Texture* texLayer[3] = {};
static SDL_Texture *texSky = nullptr, *texTile = nullptr, *texScreen = nullptr;
static int layerH[3] = {SH, SH, SH};
static float camX = 0, camY = 0, shakeX = 0, shakeY = 0, camLook = 0;

static void blend(SDL_BlendMode m) { SDL_SetRenderDrawBlendMode(R, m); }
static void fillPoly(const std::vector<SDL_FPoint>& p, SDL_Color c) {
    if (p.size() < 3) return;
    static std::vector<SDL_Vertex> v; static std::vector<int> idx;
    v.clear(); idx.clear();
    for (auto& q : p) v.push_back(SDL_Vertex{q, c, SDL_FPoint{0, 0}});
    for (int i = 1; i + 1 < (int)p.size(); ++i) { idx.push_back(0); idx.push_back(i); idx.push_back(i + 1); }
    SDL_RenderGeometry(R, nullptr, v.data(), (int)v.size(), idx.data(), (int)idx.size());
}
static void line(float x1, float y1, float x2, float y2, float w, SDL_Color c) {
    float dx = x2 - x1, dy = y2 - y1, l = sqrtf(dx * dx + dy * dy);
    if (l < 1e-4f) return;
    float nx = -dy / l * w * 0.5f, ny = dx / l * w * 0.5f;
    fillPoly({{x1 + nx, y1 + ny}, {x2 + nx, y2 + ny}, {x2 - nx, y2 - ny}, {x1 - nx, y1 - ny}}, c);
}
static void stroke(const std::vector<SDL_FPoint>& p, float w, SDL_Color c, bool closed = true) {
    for (size_t i = 0; i + 1 < p.size(); i++) line(p[i].x, p[i].y, p[i + 1].x, p[i + 1].y, w, c);
    if (closed && p.size() > 2) line(p.back().x, p.back().y, p[0].x, p[0].y, w, c);
}
static void rect(float x, float y, float w, float h, SDL_Color c) {
    SDL_SetRenderDrawColor(R, c.r, c.g, c.b, c.a);
    SDL_FRect r{x, y, w, h};
    SDL_RenderFillRectF(R, &r);
}
static void glow(float x, float y, float rad, SDL_Color c, float k) {
    SDL_SetTextureColorMod(texGlow, c.r, c.g, c.b);
    SDL_SetTextureAlphaMod(texGlow, (Uint8)clampf(k * 255.f, 0, 255));
    SDL_FRect d{x - rad, y - rad, rad * 2, rad * 2};
    SDL_RenderCopyF(R, texGlow, nullptr, &d);
}
static void glowLine(float x1, float y1, float x2, float y2, float th, SDL_Color c, float k) {
    float dx = x2 - x1, dy = y2 - y1, len = sqrtf(dx * dx + dy * dy);
    SDL_SetTextureColorMod(texBar, c.r, c.g, c.b);
    SDL_SetTextureAlphaMod(texBar, (Uint8)clampf(k * 255.f, 0, 255));
    float cx = (x1 + x2) * 0.5f, cy = (y1 + y2) * 0.5f;
    SDL_FRect d{cx - len * 0.5f - th, cy - th, len + th * 2, th * 2};
    SDL_RenderCopyExF(R, texBar, nullptr, &d, atan2f(dy, dx) * 180.f / PI, nullptr, SDL_FLIP_NONE);
}
static void neonLine(float x1, float y1, float x2, float y2, SDL_Color c, float w = 2.f, float g = 0.6f) {
    blend(SDL_BLENDMODE_ADD);
    glowLine(x1, y1, x2, y2, 12, c, g);
    line(x1, y1, x2, y2, w, c);
    line(x1, y1, x2, y2, w * 0.4f, C(255, 255, 255, 140));
    blend(SDL_BLENDMODE_BLEND);
}

struct Xf {
    float x, y, sx = 1, sy = 1, rot = 0;
    SDL_FPoint operator()(float lx, float ly) const {
        lx *= sx; ly *= sy;
        float c = cosf(rot), s = sinf(rot);
        return SDL_FPoint{x + lx * c - ly * s, y + lx * s + ly * c};
    }
};
static std::vector<SDL_FPoint> ell(const Xf& xf, float lx, float ly, float rx, float ry, float r = 0, int seg = 18) {
    std::vector<SDL_FPoint> p; p.reserve(seg);
    float c = cosf(r), s = sinf(r);
    for (int i = 0; i < seg; i++) {
        float a = 2 * PI * i / seg, ex = rx * cosf(a), ey = ry * sinf(a);
        p.push_back(xf(lx + ex * c - ey * s, ly + ex * s + ey * c));
    }
    return p;
}
static void circle(float x, float y, float r, SDL_Color c) { fillPoly(ell(Xf{x, y}, 0, 0, r, r, 0, std::max(8, (int)(r * 1.5f))), c); }
static void tri(const Xf& xf, float ax, float ay, float bx, float by, float cx, float cy, SDL_Color c) { fillPoly({xf(ax, ay), xf(bx, by), xf(cx, cy)}, c); }
static std::vector<SDL_FPoint> roundRect(const Xf& xf, float x, float y, float w, float h, float r) {
    std::vector<SDL_FPoint> p;
    struct Cn { float cx, cy, a0; } cs[4] = {{x + w - r, y + h - r, 0}, {x + r, y + h - r, PI * 0.5f}, {x + r, y + r, PI}, {x + w - r, y + r, PI * 1.5f}};
    for (auto& cn : cs)
        for (int i = 0; i <= 4; i++) { float a = cn.a0 + PI * 0.5f * i / 4; p.push_back(xf(cn.cx + r * cosf(a), cn.cy + r * sinf(a))); }
    return p;
}

// ---------- 5x7 bitmap font ----------
static const char* FONT_CH = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ:-!/.+";
static const uint8_t FONT[][7] = {
    {0x0E,0x11,0x13,0x15,0x19,0x11,0x0E},{0x04,0x0C,0x04,0x04,0x04,0x04,0x0E},{0x0E,0x11,0x01,0x02,0x04,0x08,0x1F},
    {0x1F,0x02,0x04,0x02,0x01,0x11,0x0E},{0x02,0x06,0x0A,0x12,0x1F,0x02,0x02},{0x1F,0x10,0x1E,0x01,0x01,0x11,0x0E},
    {0x06,0x08,0x10,0x1E,0x11,0x11,0x0E},{0x1F,0x01,0x02,0x04,0x08,0x08,0x08},{0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E},
    {0x0E,0x11,0x11,0x0F,0x01,0x02,0x0C},{0x0E,0x11,0x11,0x1F,0x11,0x11,0x11},{0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E},
    {0x0E,0x11,0x10,0x10,0x10,0x11,0x0E},{0x1C,0x12,0x11,0x11,0x11,0x12,0x1C},{0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F},
    {0x1F,0x10,0x10,0x1E,0x10,0x10,0x10},{0x0E,0x11,0x10,0x17,0x11,0x11,0x0F},{0x11,0x11,0x11,0x1F,0x11,0x11,0x11},
    {0x0E,0x04,0x04,0x04,0x04,0x04,0x0E},{0x07,0x02,0x02,0x02,0x02,0x12,0x0C},{0x11,0x12,0x14,0x18,0x14,0x12,0x11},
    {0x10,0x10,0x10,0x10,0x10,0x10,0x1F},{0x11,0x1B,0x15,0x15,0x11,0x11,0x11},{0x11,0x11,0x19,0x15,0x13,0x11,0x11},
    {0x0E,0x11,0x11,0x11,0x11,0x11,0x0E},{0x1E,0x11,0x11,0x1E,0x10,0x10,0x10},{0x0E,0x11,0x11,0x11,0x15,0x12,0x0D},
    {0x1E,0x11,0x11,0x1E,0x14,0x12,0x11},{0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E},{0x1F,0x04,0x04,0x04,0x04,0x04,0x04},
    {0x11,0x11,0x11,0x11,0x11,0x11,0x0E},{0x11,0x11,0x11,0x11,0x11,0x0A,0x04},{0x11,0x11,0x11,0x15,0x15,0x15,0x0A},
    {0x11,0x11,0x0A,0x04,0x0A,0x11,0x11},{0x11,0x11,0x11,0x0A,0x04,0x04,0x04},{0x1F,0x01,0x02,0x04,0x08,0x10,0x1F},
    {0x00,0x0C,0x0C,0x00,0x0C,0x0C,0x00},{0x00,0x00,0x00,0x1F,0x00,0x00,0x00},{0x04,0x04,0x04,0x04,0x04,0x00,0x04},
    {0x01,0x01,0x02,0x04,0x08,0x10,0x10},{0x00,0x00,0x00,0x00,0x00,0x0C,0x0C},{0x00,0x04,0x04,0x1F,0x04,0x04,0x00},
};
static float textW(const std::string& s, float sc) { return s.size() * 6 * sc - sc; }
static void text(const std::string& s, float x, float y, float sc, SDL_Color c, bool center = false, float g = 0.f) {
    if (center) x -= textW(s, sc) * 0.5f;
    if (g > 0) {
        blend(SDL_BLENDMODE_ADD);
        for (size_t i = 0; i < s.size(); i++)
            if (s[i] != ' ') glow(x + i * 6 * sc + 2.5f * sc, y + 3.5f * sc, 6.f * sc, c, g);
    }
    blend(SDL_BLENDMODE_BLEND);
    SDL_SetRenderDrawColor(R, c.r, c.g, c.b, c.a);
    for (size_t i = 0; i < s.size(); i++) {
        const char* f = strchr(FONT_CH, toupper((unsigned char)s[i]));
        if (!f || s[i] == 0) continue;
        const uint8_t* gl = FONT[f - FONT_CH];
        for (int ry = 0; ry < 7; ry++)
            for (int rx = 0; rx < 5; rx++)
                if (gl[ry] & (0x10 >> rx)) {
                    SDL_FRect r{x + i * 6 * sc + rx * sc, y + ry * sc, sc, sc};
                    SDL_RenderFillRectF(R, &r);
                }
    }
}

// ---------- generated textures ----------
template <class F>
static SDL_Texture* makeTex(int w, int h, F fn, SDL_BlendMode bm) {
    std::vector<Uint8> px(w * h * 4);
    for (int y = 0; y < h; y++)
        for (int x = 0; x < w; x++) {
            SDL_Color c = fn(x, y);
            Uint8* p = &px[(y * w + x) * 4];
            p[0] = c.r; p[1] = c.g; p[2] = c.b; p[3] = c.a;
        }
    SDL_Texture* t = SDL_CreateTexture(R, SDL_PIXELFORMAT_RGBA32, SDL_TEXTUREACCESS_STATIC, w, h);
    SDL_UpdateTexture(t, nullptr, px.data(), w * 4);
    SDL_SetTextureBlendMode(t, bm);
    return t;
}

// Parallax building layer. Texture is cropped to the building band (no wasted
// transparent fill) and the atmospheric haze is baked into the colors, which is
// mathematically the same as the fullscreen haze rects we used to draw per frame.
static SDL_Color hazeCol(SDL_Color c, int passes) {
    const float a = 28.f / 255.f;
    for (int i = 0; i < passes; i++) {
        c.r = (Uint8)(c.r + (60 - c.r) * a); c.g = (Uint8)(c.g + (10 - c.g) * a); c.b = (Uint8)(c.b + (80 - c.b) * a);
    }
    return c;
}
static SDL_Texture* makeLayer(int idx) {
    const int LWpx = 1600;
    float minH = idx == 0 ? 260.f : idx == 1 ? 190.f : 130.f, maxH = idx == 0 ? 540.f : idx == 1 ? 430.f : 330.f;
    const int Ht = (int)maxH + 50;
    layerH[idx] = Ht;
    const int hz = 2 - idx;
    SDL_Texture* t = SDL_CreateTexture(R, SDL_PIXELFORMAT_RGBA8888, SDL_TEXTUREACCESS_TARGET, LWpx, Ht);
    SDL_SetTextureBlendMode(t, SDL_BLENDMODE_BLEND);
    SDL_SetRenderTarget(R, t);
    SDL_SetRenderDrawColor(R, 0, 0, 0, 0);
    SDL_RenderClear(R);
    std::mt19937 g(100 + idx);
    auto fr = [&](float a, float b) { return std::uniform_real_distribution<float>(a, b)(g); };
    auto hrect = [&](float x, float y, float w, float h, SDL_Color c) { rect(x, y, w, h, hazeCol(c, hz)); };
    SDL_Color base = idx == 0 ? C(30, 14, 60) : idx == 1 ? C(17, 9, 40) : C(9, 5, 22);
    SDL_Color pal[4] = {C(0, 240, 255), C(255, 40, 200), C(255, 220, 60), C(140, 80, 255)};
    float lit = idx == 0 ? 0.12f : idx == 1 ? 0.2f : 0.28f;
    float x = 0;
    blend(SDL_BLENDMODE_BLEND);
    while (x < LWpx) {
        float bw = fr(60, 170) * (idx == 2 ? 1.3f : 1.f);
        if (x + bw > LWpx) bw = LWpx - x;
        float bh = fr(minH, maxH), top = Ht - bh;
        hrect(x, top, bw, bh, base);
        hrect(x, top, bw, 2, C(pal[idx].r, pal[idx].g, pal[idx].b, 70));
        float ws = idx == 0 ? 0.7f : idx == 1 ? 0.85f : 1.f;
        for (float wy = top + 12; wy < Ht - 10; wy += 14 * ws)
            for (float wx = x + 6; wx < x + bw - 8; wx += 10 * ws)
                if (fr(0, 1) < lit) {
                    SDL_Color c = pal[(int)fr(0, 3.99f)];
                    c.a = (Uint8)fr(60, 200);
                    hrect(wx, wy, 4 * ws, 6 * ws, c);
                }
        if (fr(0, 1) < 0.35f && bw > 50) {
            SDL_Color c = pal[(int)fr(0, 3.99f)];
            float sx = x + fr(10, bw - 30), sy = top + fr(20, 120), sh2 = fr(40, 110);
            hrect(sx - 6, sy - 6, 22, sh2 + 12, C(c.r, c.g, c.b, 40));
            hrect(sx - 3, sy - 3, 16, sh2 + 6, C(c.r, c.g, c.b, 70));
            hrect(sx, sy, 10, sh2, C(c.r, c.g, c.b, 230));
            hrect(sx + 3, sy + 3, 4, sh2 - 6, C(255, 255, 255, 180));
        }
        if (fr(0, 1) < 0.4f) {
            float ax = x + bw * fr(0.2f, 0.8f);
            hrect(ax, top - 40, 2, 40, base);
            hrect(ax - 2, top - 44, 6, 4, C(255, 30, 60, 220));
        }
        x += bw + fr(0, 25);
    }
    SDL_SetRenderTarget(R, nullptr);
    return t;
}

// ============================================================================
// WORLD
// ============================================================================
static int LW = 240;
static constexpr int LH = 18;
static std::vector<uint8_t> tiles;  // 0 empty, 1 solid, 2 one-way platform
static int tileAt(int tx, int ty) {
    if (tx < 0 || tx >= LW) return 1;
    if (ty < 0 || ty >= LH) return 0;
    return tiles[ty * LW + tx];
}
static bool solid(int tx, int ty) { return tileAt(tx, ty) == 1; }
static int groundTop(int tx) {
    if (tx < 0 || tx >= LW) return -1;
    for (int ty = 0; ty < LH; ty++) if (tiles[ty * LW + tx] == 1) return ty;
    return -1;
}

static void moveBody(float& x, float& y, float w, float h, float& vx, float& vy, bool& onGround, bool& hitWall, bool drop, float dt) {
    hitWall = false;
    x += vx * dt;
    int ty0 = (int)floorf(y / TS), ty1 = (int)floorf((y + h - 0.01f) / TS);
    if (vx > 0) {
        int tx = (int)floorf((x + w) / TS);
        for (int ty = ty0; ty <= ty1; ty++) if (solid(tx, ty)) { x = tx * TS - w - 0.001f; vx = 0; hitWall = true; break; }
    } else if (vx < 0) {
        int tx = (int)floorf(x / TS);
        for (int ty = ty0; ty <= ty1; ty++) if (solid(tx, ty)) { x = (tx + 1) * TS + 0.001f; vx = 0; hitWall = true; break; }
    }
    float prevBottom = y + h;
    y += vy * dt;
    onGround = false;
    int tx0 = (int)floorf(x / TS), tx1 = (int)floorf((x + w - 0.01f) / TS);
    if (vy >= 0) {
        int ty = (int)floorf((y + h) / TS);
        for (int tx = tx0; tx <= tx1; tx++) {
            int t = tileAt(tx, ty);
            if (t == 1 || (t == 2 && !drop && prevBottom <= ty * TS + 1.f)) { y = ty * TS - h; vy = 0; onGround = true; break; }
        }
    } else {
        int ty = (int)floorf(y / TS);
        for (int tx = tx0; tx <= tx1; tx++) if (solid(tx, ty)) { y = (ty + 1) * TS; vy = 0; break; }
    }
}

enum Veg { CUCUMBER, TOMATO, CARROT, GARLIC, VEG_N };
struct VegInfo { const char* name; SDL_Color col; float speed, grav, cooldown; int dmg; };
static const VegInfo VEG[VEG_N] = {
    {"CUCUMBER", C(80, 255, 120), 1150, 500, 0.15f, 1},
    {"TOMATO", C(255, 60, 70), 760, 1500, 0.45f, 2},
    {"CARROT", C(255, 150, 30), 1350, 250, 0.32f, 2},
    {"GARLIC", C(220, 200, 255), 820, 1600, 0.26f, 1},
};

enum EType { RAT, PIGEON, RACCOON, CAT };
struct Enemy {
    int id; EType t; float x, y, w, h, vx = 0, vy = 0; int hp; float flash = 0, anim = 0, timer = 0, homeX = 0, baseY = 0, dash = 0;
    int dir = -1; bool onGround = false, hitWall = false, dead = false;
};
struct Proj { float x, y, vx, vy, rot, vr; int type; float life; int pierce, bounces; int hit[4]; int nhit; bool dead = false; };
struct Particle { float x, y, vx, vy, life, maxLife, size, grav, drag; SDL_Color c; int kind; };
struct Popup { float x, y, life; std::string s; SDL_Color c; };
struct Drop { float x, y, z, vz, speed, len; };

struct Player {
    float x = 0, y = 0, vx = 0, vy = 0, w = 28, h = 44;
    bool onGround = false, hitWall = false, jumpHeld = false;
    int hp = 5, facing = 1, veg = 0;
    float invuln = 0, coyote = 0, jumpBuf = 0, dropT = 0;
    float squash = 0, squashV = 0, slosh = 0, sloshV = 0, prevVx = 0;
    float cooldown = 0, blink = 3, run = 0, dripT = 0;
};

enum State { TITLE, PLAY, DEAD, WIN };
static State state = TITLE;
static Player P;
static std::vector<Enemy> enemies;
static std::vector<Proj> projs;
static std::vector<Particle> parts;
static std::vector<Popup> popups;
static std::vector<Drop> rain;
static int level = 1, score = 0, nextId = 1, combo = 0;
static float comboT = 0, hitstop = 0, trauma = 0, stateT = 0, gameT = 0, goalX = 0, hintT = 8;
static float aimX = 1, aimY = 0, mouseX = SW / 2, mouseY = SH / 2;
static bool mouseFire = false, keyFire = false, useMouseAim = true;

static void spawnP(float x, float y, float vx, float vy, float life, float size, SDL_Color c, int kind = 1, float grav = 600, float drag = 1.5f) {
    if (parts.size() > 2500) return;
    parts.push_back(Particle{x, y, vx, vy, life, life, size, grav, drag, c, kind});
}
static void burst(float x, float y, int n, SDL_Color c, float spd, int kind, float life = 0.6f, float size = 3, float grav = 600) {
    for (int i = 0; i < n; i++) {
        float a = frand(0, 2 * PI), s = frand(0.3f, 1.f) * spd;
        spawnP(x, y, cosf(a) * s, sinf(a) * s, life * frand(0.6f, 1.2f), size * frand(0.6f, 1.4f), c, kind, grav);
    }
}
static void popup(float x, float y, const std::string& s, SDL_Color c) { popups.push_back(Popup{x, y, 1.f, s, c}); }

static void genLevel(int lvl) {
    gen.seed(777 + lvl * 31);
    LW = 220 + lvl * 30;
    tiles.assign(LW * LH, 0);
    auto setT = [&](int tx, int ty, int v) { if (tx >= 0 && tx < LW && ty >= 0 && ty < LH) tiles[ty * LW + tx] = (uint8_t)v; };
    int x = 0, h = 3;
    while (x < LW - 16) {
        int len = (x < 12) ? 16 : irand(5, 12);
        int start = x;
        for (int i = 0; i < len && x < LW; i++, x++)
            for (int ty = LH - h; ty < LH; ty++) setT(x, ty, 1);
        if (x > 18 && frand(0, 1) < 0.65f) {
            int pl = irand(3, 6), px = start + irand(0, std::max(0, len - pl)), py = LH - h - irand(2, 3);
            for (int i = 0; i < pl; i++) setT(px + i, py, 2);
            if (frand(0, 1) < 0.4f && py - 3 > 3) {
                int px2 = px + irand(-2, 3), py2 = py - 3;
                for (int i = 0; i < irand(3, 5); i++) setT(px2 + i, py2, 2);
            }
        }
        if (x > 18 && frand(0, 1) < 0.15f) {  // neon pillar
            int px = start + len / 2;
            for (int i = 1; i <= 2; i++) setT(px, LH - h - i, 1);
        }
        if (x > 18) {
            if (frand(0, 1) < 0.55f) {
                int gap = irand(2, 3 + (lvl > 1 ? 1 : 0));
                if (gap >= 4) for (int i = 1; i < gap - 1; i++) setT(x + i, LH - h - 1, 2);
                x += gap;
            }
            h = std::clamp(h + irand(-2, 2), 2, 7);
        }
    }
    for (int tx = LW - 16; tx < LW; tx++)
        for (int ty = 0; ty < LH; ty++) setT(tx, ty, ty >= LH - 3 ? 1 : 0);
    goalX = (LW - 7) * TS;

    enemies.clear(); projs.clear(); parts.clear(); popups.clear();
    float density = std::min(0.22f + lvl * 0.05f, 0.5f);
    for (int tx = 24; tx < LW - 18; tx++) {
        if (frand(0, 1) > density / 1.0f * 0.5f) continue;
        int gt = groundTop(tx);
        if (gt < 0 || groundTop(tx - 1) != gt || groundTop(tx + 1) != gt) continue;
        float r = frand(0, 1);
        EType t = r < 0.38f ? RAT : r < 0.6f ? PIGEON : r < 0.8f ? CAT : RACCOON;
        Enemy e{};
        e.id = nextId++; e.t = t; e.dir = frand(0, 1) < 0.5f ? -1 : 1;
        switch (t) {
            case RAT: e.w = 34; e.h = 20; e.hp = 2; break;
            case PIGEON: e.w = 30; e.h = 24; e.hp = 1; break;
            case CAT: e.w = 36; e.h = 26; e.hp = 3; break;
            case RACCOON: e.w = 40; e.h = 34; e.hp = 4 + lvl / 2; break;
        }
        e.x = tx * TS + TS * 0.5f - e.w * 0.5f;
        e.y = gt * TS - e.h - (t == PIGEON ? frand(120, 200) : 0.f);
        e.homeX = e.x; e.baseY = e.y; e.timer = frand(0, 3);
        enemies.push_back(e);
        tx += irand(4, 8);
    }
}

static void respawnNear(float wx) {
    int tx = (int)(wx / TS);
    for (int t = tx; t > 1; t--) {
        int g = groundTop(t);
        if (g >= 0 && groundTop(t - 1) == g && groundTop(t + 1) == g) {
            P.x = t * TS + TS / 2 - P.w / 2; P.y = g * TS - P.h - 2; P.vx = P.vy = 0;
            return;
        }
    }
    P.x = 3 * TS; P.y = 5 * TS;
}

static void startLevel(bool fresh) {
    if (fresh) { level = 1; score = 0; }
    genLevel(level);
    P = Player{};
    P.hp = 5;
    respawnNear(4 * TS);
    camX = 0;
    state = PLAY; stateT = 0; hintT = level == 1 ? 9.f : 3.f;
}

// ============================================================================
// GAMEPLAY
// ============================================================================
static void addTrauma(float t) { trauma = std::min(1.f, trauma + t); }

static void hurtPlayer(float fromX) {
    if (P.invuln > 0 || state != PLAY) return;
    P.hp--;
    P.invuln = 1.3f;
    float dir = (P.x + P.w / 2 < fromX) ? -1.f : 1.f;
    P.vx = dir * 380; P.vy = -480;
    addTrauma(0.55f);
    hitstop = 0.05f;
    sfxHurt();
    float cx = P.x + P.w / 2, cy = P.y + P.h / 2;
    burst(cx, cy, 14, C(200, 250, 255), 420, 2, 0.6f, 4, 900);
    burst(cx, cy, 18, C(80, 230, 90), 300, 1, 0.7f, 3, 900);
    combo = 0;
    if (P.hp <= 0) {
        state = DEAD; stateT = 0;
        burst(cx, cy, 40, C(200, 250, 255), 600, 2, 1.0f, 5, 1000);
        burst(cx, cy, 60, C(80, 230, 90), 500, 1, 1.2f, 4, 1000);
        burst(cx, cy, 8, C(40, 140, 40), 350, 3, 1.5f, 6, 1100);
        sfxBoom();
        addTrauma(1.f);
    }
}

static void killEnemy(Enemy& e) {
    e.dead = true;
    combo++; comboT = 2.5f;
    int pts = (e.t == RACCOON ? 300 : e.t == CAT ? 200 : 100) * std::min(combo, 8);
    score += pts;
    SDL_Color c = e.t == RAT ? C(255, 60, 200) : e.t == PIGEON ? C(60, 220, 255) : e.t == CAT ? C(255, 230, 60) : C(255, 140, 40);
    float cx = e.x + e.w / 2, cy = e.y + e.h / 2;
    burst(cx, cy, 26, c, 520, 0, 0.5f, 3, 300);
    burst(cx, cy, 14, c, 260, 1, 0.8f, 4, 800);
    popup(cx, e.y - 10, "+" + std::to_string(pts) + (combo > 1 ? " X" + std::to_string(std::min(combo, 8)) : ""), c);
    addTrauma(0.22f);
    sfxKill();
}

static void damageEnemy(Enemy& e, int dmg, float kx) {
    if (e.dead) return;
    e.hp -= dmg; e.flash = 0.1f;
    if (e.t != PIGEON) { e.vx += kx * 160; if (e.onGround) e.vy = -180; }
    sfxHit();
    if (e.hp <= 0) killEnemy(e);
}

static void explode(float x, float y) {
    for (auto& e : enemies) {
        if (e.dead) continue;
        float dx = e.x + e.w / 2 - x, dy = e.y + e.h / 2 - y;
        if (dx * dx + dy * dy < 95 * 95) damageEnemy(e, 2, dx > 0 ? 1.f : -1.f);
    }
    burst(x, y, 40, C(255, 50, 60), 480, 1, 0.7f, 4, 900);
    burst(x, y, 20, C(255, 180, 120), 600, 0, 0.35f, 3, 200);
    for (int i = 0; i < 8; i++) spawnP(x, y, frand(-60, 60), frand(-60, 60), 0.35f, 30 + i * 4, C(255, 40, 60), 4, 0, 4);
    addTrauma(0.4f);
    sfxBoom();
}

static void throwVeg() {
    const VegInfo& vi = VEG[P.veg];
    float cx = P.x + P.w / 2, cy = P.y + 10;
    float dx = aimX, dy = aimY;
    Proj p{};
    p.x = cx + dx * 12; p.y = cy + dy * 12;
    p.vx = dx * vi.speed + P.vx * 0.3f;
    p.vy = dy * vi.speed + std::min(0.f, P.vy * 0.3f);
    p.type = P.veg; p.life = 3.f;
    p.rot = atan2f(dy, dx);
    p.vr = P.veg == CUCUMBER ? 18.f * (dx >= 0 ? 1 : -1) : P.veg == CARROT ? 0.f : frand(-12, 12);
    p.pierce = P.veg == CARROT ? 3 : 0;
    p.bounces = P.veg == GARLIC ? 4 : 0;
    projs.push_back(p);
    P.cooldown = vi.cooldown;
    P.vx -= dx * 40;
    P.sloshV -= dx * 120;
    P.squash = -0.08f;
    if (dx != 0) P.facing = dx > 0 ? 1 : -1;
    burst(p.x, p.y, 6, vi.col, 220, 0, 0.18f, 2, 0);
    sfxThrow();
}

static void updatePlayer(float dt, const Uint8* ks) {
    bool left = ks[SDL_SCANCODE_A] || ks[SDL_SCANCODE_LEFT];
    bool right = ks[SDL_SCANCODE_D] || ks[SDL_SCANCODE_RIGHT];
    bool down = ks[SDL_SCANCODE_S] || ks[SDL_SCANCODE_DOWN];
    float in = (right ? 1.f : 0.f) - (left ? 1.f : 0.f);
    const float maxV = 390, accG = 4200, accA = 2800, dec = 3600;
    float acc = P.onGround ? accG : accA;
    if (in != 0) {
        if (P.vx * in < 0) acc *= 1.6f;  // fast turnaround
        P.vx += in * acc * dt;
        if (fabsf(P.vx) > maxV) P.vx = lerpf(P.vx, in * maxV, std::min(1.f, 12 * dt));
        if (!useMouseAim) P.facing = in > 0 ? 1 : -1;
    } else {
        float d = (P.onGround ? dec : dec * 0.35f) * dt;
        if (fabsf(P.vx) <= d) P.vx = 0; else P.vx -= d * (P.vx > 0 ? 1 : -1);
    }

    P.coyote = P.onGround ? 0.1f : P.coyote - dt;
    P.jumpBuf -= dt;
    P.dropT -= dt;
    if (P.jumpBuf > 0 && P.coyote > 0) {
        if (down && P.onGround && tileAt((int)((P.x + P.w / 2) / TS), (int)((P.y + P.h + 2) / TS)) == 2) {
            P.dropT = 0.2f;
        } else {
            P.vy = -860; P.squash = 0.25f; sfxJump();
            burst(P.x + P.w / 2, P.y + P.h, 8, C(120, 255, 160), 160, 1, 0.35f, 2.5f, 300);
        }
        P.jumpBuf = 0; P.coyote = 0;
    }
    float g = 2400;
    if (P.jumpHeld && fabsf(P.vy) < 90) g *= 0.55f;  // apex hang
    if (P.vy > 0) g *= 1.15f;
    P.vy = std::min(P.vy + g * dt, 1250.f);

    bool was = P.onGround;
    float prevVy = P.vy;
    moveBody(P.x, P.y, P.w, P.h, P.vx, P.vy, P.onGround, P.hitWall, P.dropT > 0 || (down && P.jumpHeld), dt);
    if (!was && P.onGround && prevVy > 200) {
        P.squash = -std::min(0.32f, prevVy / 3500.f);
        if (prevVy > 500) { sfxLand(); burst(P.x + P.w / 2, P.y + P.h, 10, C(150, 120, 255), 200, 1, 0.3f, 2.5f, 200); }
    }

    // squash spring & brine slosh spring
    P.squashV += (-320 * P.squash - 16 * P.squashV) * dt;
    P.squash += P.squashV * dt;
    float ax = (P.vx - P.prevVx) / dt;
    P.prevVx = P.vx;
    P.sloshV += (-170 * P.slosh - 6 * P.sloshV - ax * 0.32f) * dt;
    P.slosh = clampf(P.slosh + P.sloshV * dt, -9, 9);

    P.invuln -= dt;
    P.cooldown -= dt;
    if (P.onGround && fabsf(P.vx) > 50) P.run += dt * fabsf(P.vx) * 0.03f;
}

static void updateEnemy(Enemy& e, float dt) {
    float pcx = P.x + P.w / 2, pcy = P.y + P.h / 2;
    float ecx = e.x + e.w / 2, ecy = e.y + e.h / 2;
    float dxp = pcx - ecx;
    e.timer += dt; e.anim += dt; e.flash -= dt;
    switch (e.t) {
        case RAT: {
            float target = e.dir * 150.f;
            e.vx = lerpf(e.vx, target, std::min(1.f, 6 * dt));
            break;
        }
        case CAT: {
            if (e.dash > 0) { e.dash -= dt; e.vx = e.dir * 520.f; }
            else {
                e.vx = lerpf(e.vx, e.dir * 60.f, std::min(1.f, 5 * dt));
                if (e.timer > 1.2f && fabsf(dxp) < 420 && fabsf(pcy - ecy) < 110) {
                    e.dir = dxp > 0 ? 1 : -1; e.dash = 0.55f; e.timer = 0; e.vy = -200;
                    snd::play(500, 1100, 0.15f, 2, 0.2f, 0.1f);
                }
            }
            break;
        }
        case RACCOON: {
            if (e.onGround) {
                e.vx = lerpf(e.vx, 0, std::min(1.f, 10 * dt));
                if (e.timer > 1.4f) {
                    e.timer = frand(0, 0.5f);
                    if (fabsf(dxp) < 600) e.dir = dxp > 0 ? 1 : -1;
                    e.vx = e.dir * 240.f; e.vy = -680;
                }
            }
            break;
        }
        case PIGEON: {
            float ty = e.baseY + sinf(e.timer * 3.f) * 25.f;
            if (fabsf(dxp) < 380) { ty = pcy - e.h / 2; e.dir = dxp > 0 ? 1 : -1; e.vx = lerpf(e.vx, e.dir * 210.f, std::min(1.f, 2 * dt)); }
            else {
                e.vx = lerpf(e.vx, e.dir * 110.f, std::min(1.f, 2 * dt));
                if ((e.x > e.homeX + 220 && e.dir > 0) || (e.x < e.homeX - 220 && e.dir < 0)) e.dir = -e.dir;
            }
            e.vy = (ty - e.y) * 2.2f;
            e.x += e.vx * dt; e.y += e.vy * dt;
            return;
        }
    }
    e.vy = std::min(e.vy + 2200 * dt, 1200.f);
    moveBody(e.x, e.y, e.w, e.h, e.vx, e.vy, e.onGround, e.hitWall, false, dt);
    if (e.t == RAT || (e.t == CAT && e.dash <= 0)) {
        float fx = e.dir > 0 ? e.x + e.w + 2 : e.x - 2;
        int t = tileAt((int)floorf(fx / TS), (int)floorf((e.y + e.h + 4) / TS));
        if (e.hitWall || (e.onGround && t == 0)) e.dir = -e.dir;
    } else if (e.t == CAT && e.hitWall) e.dir = -e.dir;
    if (e.y > LH * TS + 200) e.dead = true;
}

static void updateProj(Proj& p, float dt) {
    const VegInfo& vi = VEG[p.type];
    float px = p.x, py = p.y;
    p.vy += vi.grav * dt;
    p.x += p.vx * dt; p.y += p.vy * dt;
    p.life -= dt;
    if (p.type == CARROT) p.rot = atan2f(p.vy, p.vx); else p.rot += p.vr * dt;
    if (p.life <= 0 || p.y > LH * TS + 100) { p.dead = true; return; }
    if (solid((int)floorf(p.x / TS), (int)floorf(p.y / TS))) {
        if (p.type == GARLIC && p.bounces > 0) {
            p.bounces--;
            if (solid((int)floorf(px / TS), (int)floorf(p.y / TS))) { p.vx = -p.vx * 0.75f; p.x = px; }
            else { p.vy = -p.vy * 0.65f; p.y = py; p.vx *= 0.85f; }
            sfxBounce();
            burst(p.x, p.y, 4, vi.col, 150, 0, 0.2f, 2, 0);
        } else if (p.type == TOMATO) { explode(p.x, p.y); p.dead = true; return; }
        else {
            burst(px, py, 10, vi.col, 260, 1, 0.4f, 2.5f, 700);
            snd::play(300, 120, 0.06f, 0, 0.7f, 0.1f);
            p.dead = true; return;
        }
    }
    for (auto& e : enemies) {
        if (e.dead) continue;
        if (p.x + 8 < e.x || p.x - 8 > e.x + e.w || p.y + 8 < e.y || p.y - 8 > e.y + e.h) continue;
        bool already = false;
        for (int i = 0; i < p.nhit; i++) if (p.hit[i] == e.id) already = true;
        if (already) continue;
        float kx = p.vx > 0 ? 1.f : -1.f;
        burst(p.x, p.y, 8, vi.col, 300, 0, 0.25f, 2.5f, 200);
        if (p.type == TOMATO) { explode(p.x, p.y); p.dead = true; return; }
        damageEnemy(e, vi.dmg, kx);
        if (p.type == CARROT && p.pierce > 0 && p.nhit < 4) { p.pierce--; p.hit[p.nhit++] = e.id; continue; }
        if (p.type == GARLIC && p.bounces > 0 && p.nhit < 4) { p.hit[p.nhit++] = e.id; p.vy = -420; p.vx *= -0.5f; p.bounces--; return; }
        p.dead = true; return;
    }
}

static void updateParticles(float dt) {
    for (auto& q : parts) {
        float py = q.y;
        q.vy += q.grav * dt;
        float k = expf(-q.drag * dt);
        q.vx *= k; q.vy *= k;
        q.x += q.vx * dt; q.y += q.vy * dt;
        if (q.kind != 0 && q.kind != 4 && solid((int)floorf(q.x / TS), (int)floorf(q.y / TS))) { q.y = py; q.vy *= -0.3f; q.vx *= 0.6f; }
        q.life -= dt;
    }
    parts.erase(std::remove_if(parts.begin(), parts.end(), [](const Particle& q) { return q.life <= 0; }), parts.end());
}

static void stepGame(float dt, const Uint8* ks) {
    if (state == PLAY) {
        updatePlayer(dt, ks);
        if ((mouseFire || keyFire) && P.cooldown <= 0) throwVeg();
        for (auto& e : enemies) {
            if (e.dead || fabsf(e.x - P.x) > 1300) continue;
            updateEnemy(e, dt);
            if (!e.dead && P.x < e.x + e.w - 4 && P.x + P.w > e.x + 4 && P.y < e.y + e.h - 4 && P.y + P.h > e.y + 4)
                hurtPlayer(e.x + e.w / 2);
        }
        for (auto& p : projs) if (!p.dead) updateProj(p, dt);
        if (P.y > LH * TS + 80 && state == PLAY) {
            hurtPlayer(P.x);
            if (state == PLAY) { respawnNear(P.x); P.invuln = 1.5f; }
        }
        if (P.x + P.w / 2 > goalX && state == PLAY) {
            state = WIN; stateT = 0; score += 1000 * level + P.hp * 250; sfxWin();
            burst(goalX, P.y, 80, C(0, 240, 255), 700, 0, 0.9f, 3, 100);
        }
    }
    updateParticles(dt);
}

// ============================================================================
// DRAWING
// ============================================================================
static void drawSky() {
    SDL_Color top = C(6, 3, 20), mid = C(40, 8, 60), bot = C(90, 20, 90);
    std::vector<SDL_Vertex> v = {
        {{0, 0}, top, {0, 0}}, {{SW, 0}, top, {0, 0}}, {{SW, SH * 0.55f}, mid, {0, 0}}, {{0, SH * 0.55f}, mid, {0, 0}},
        {{0, SH}, bot, {0, 0}}, {{SW, SH}, bot, {0, 0}}};
    int idx[] = {0, 1, 2, 0, 2, 3, 3, 2, 5, 3, 5, 4};
    blend(SDL_BLENDMODE_NONE);
    SDL_RenderGeometry(R, nullptr, v.data(), 6, idx, 12);
    blend(SDL_BLENDMODE_BLEND);

    // synthwave sun
    float sx = 880, sy = 300, sr = 150;
    blend(SDL_BLENDMODE_ADD);
    glow(sx, sy, sr * 2.6f, C(255, 40, 160), 0.35f);
    blend(SDL_BLENDMODE_BLEND);
    std::vector<SDL_Vertex> sv; std::vector<int> si;
    sv.push_back({{sx, sy}, C(255, 120, 120), {0, 0}});
    for (int i = 0; i <= 48; i++) {
        float a = 2 * PI * i / 48, y = sy + sinf(a) * sr;
        float t = (y - (sy - sr)) / (2 * sr);
        sv.push_back({{sx + cosf(a) * sr, y}, C(255, (int)lerpf(230, 30, t), (int)lerpf(90, 150, t)), {0, 0}});
        if (i > 0) { si.push_back(0); si.push_back(i); si.push_back(i + 1); }
    }
    SDL_RenderGeometry(R, nullptr, sv.data(), (int)sv.size(), si.data(), (int)si.size());
    for (int i = 0; i < 7; i++) {
        float y = sy + 10 + i * i * 3.2f + i * 8, hgt = 2 + i * 1.6f;
        float t = clampf(y / SH, 0, 1);
        SDL_Color c = t < 0.55f ? C((int)lerpf(6, 40, t / 0.55f), (int)lerpf(3, 8, t / 0.55f), (int)lerpf(20, 60, t / 0.55f))
                                : C((int)lerpf(40, 90, (t - 0.55f) / 0.45f), (int)lerpf(8, 20, (t - 0.55f) / 0.45f), (int)lerpf(60, 90, (t - 0.55f) / 0.45f));
        rect(sx - sr - 2, y, sr * 2 + 4, hgt, c);
    }
}

static SDL_Texture* makeSky() {
    SDL_Texture* t = SDL_CreateTexture(R, SDL_PIXELFORMAT_RGBA8888, SDL_TEXTUREACCESS_TARGET, SW, SH);
    SDL_SetTextureBlendMode(t, SDL_BLENDMODE_NONE);
    SDL_SetRenderTarget(R, t);
    drawSky();
    rect(0, 0, SW, SH, C(60, 10, 80, 28));
    rect(0, 0, SW, SH, C(60, 10, 80, 28));
    SDL_SetRenderTarget(R, nullptr);
    return t;
}

static void drawLayers() {
    const float fac[3] = {0.08f, 0.22f, 0.42f};
    const float yoff[3] = {-10, 60, 150};
    for (int i = 0; i < 3; i++) {
        float off = -fmodf(camX * fac[i] + shakeX * 0.2f, 1600.f);
        if (off > 0) off -= 1600.f;
        float y = yoff[i] + SH - layerH[i];
        for (int k = 0; k < 2; k++) {
            SDL_FRect d{off + k * 1600.f, y, 1600.f, (float)layerH[i]};
            SDL_RenderCopyF(R, texLayer[i], nullptr, &d);
        }
    }
    // ground fog
    std::vector<SDL_Vertex> v = {
        {{0, SH * 0.6f}, C(255, 40, 200, 0), {0, 0}}, {{SW, SH * 0.6f}, C(255, 40, 200, 0), {0, 0}},
        {{SW, SH}, C(120, 30, 200, 70), {0, 0}}, {{0, SH}, C(120, 30, 200, 70), {0, 0}}};
    int idx[] = {0, 1, 2, 0, 2, 3};
    blend(SDL_BLENDMODE_ADD);
    SDL_RenderGeometry(R, nullptr, v.data(), 4, idx, 6);
    blend(SDL_BLENDMODE_BLEND);
}

static SDL_Color zoneCol(int tx) {
    int z = (tx / 30) % 3;
    return z == 0 ? C(0, 240, 255) : z == 1 ? C(255, 40, 200) : C(150, 90, 255);
}

static void drawTiles() {
    int tx0 = std::max(0, (int)floorf(camX / TS) - 1), tx1 = std::min(LW - 1, tx0 + SW / (int)TS + 3);
    float ox = -camX + shakeX, oy = -camY + shakeY;
    // bodies
    for (int ty = 0; ty < LH; ty++)
        for (int tx = tx0; tx <= tx1; tx++) {
            int t = tiles[ty * LW + tx];
            float x = tx * TS + ox, y = ty * TS + oy;
            if (t == 1) {
                SDL_FRect d{x, y, TS, TS};
                SDL_RenderCopyF(R, texTile, nullptr, &d);
                uint32_t hsh = (uint32_t)(tx * 73856093u ^ ty * 19349663u);
                if (hsh % 7 == 0) {
                    SDL_Color c = zoneCol(tx);
                    rect(x + 10 + hsh % 15, y + 12 + (hsh >> 4) % 15, 4, 3, C(c.r, c.g, c.b, 150));
                }
                if (!solid(tx, ty - 1)) rect(x, y, TS, 6, C(30, 20, 60));
            } else if (t == 2) {
                rect(x, y, TS, 10, C(25, 12, 50));
                rect(x + 6, y + 10, 3, 8, C(60, 40, 90, 160));
                rect(x + TS - 9, y + 10, 3, 8, C(60, 40, 90, 160));
            }
        }
    // edges (merged runs)
    for (int ty = 0; ty < LH; ty++) {
        int run = -1, runT = 0;
        for (int tx = tx0; tx <= tx1 + 1; tx++) {
            int t = tx <= tx1 ? tiles[ty * LW + tx] : 0;
            bool edge = (t == 1 && !solid(tx, ty - 1)) || t == 2;
            if (edge && run >= 0 && t != runT) {
                SDL_Color c = runT == 2 ? C(255, 220, 60) : zoneCol(run);
                neonLine(run * TS + ox, ty * TS + oy + 1, tx * TS + ox, ty * TS + oy + 1, c, runT == 2 ? 2.5f : 3.f);
                run = -1;
            }
            if (edge && run < 0) { run = tx; runT = t; }
            else if (!edge && run >= 0) {
                SDL_Color c = runT == 2 ? C(255, 220, 60) : zoneCol(run);
                neonLine(run * TS + ox, ty * TS + oy + 1, tx * TS + ox, ty * TS + oy + 1, c, runT == 2 ? 2.5f : 3.f);
                run = -1;
            }
        }
    }
    for (int tx = tx0; tx <= tx1; tx++) {
        for (int side = -1; side <= 1; side += 2) {
            int run = -1;
            for (int ty = 0; ty <= LH; ty++) {
                bool edge = ty < LH && solid(tx, ty) && !solid(tx + side, ty);
                if (edge && run < 0) run = ty;
                if (!edge && run >= 0) {
                    float x = (side < 0 ? tx * TS : (tx + 1) * TS) + ox;
                    SDL_Color c = zoneCol(tx);
                    c.r /= 2; c.g /= 2; c.b /= 2;
                    neonLine(x, run * TS + oy, x, std::min(ty, run + 3) * TS + oy, c, 2.f, 0.35f);
                    run = -1;
                }
            }
        }
    }
}

static void drawPortal() {
    float x = goalX - camX + shakeX, y = (LH - 3) * TS - camY + shakeY;
    float t = gameT;
    blend(SDL_BLENDMODE_ADD);
    glowLine(x, y, x, 0, 40, C(0, 240, 255), 0.25f + 0.1f * sinf(t * 4));
    glow(x, y - 70, 140, C(0, 200, 255), 0.5f);
    for (int i = 0; i < 3; i++) {
        float r = 50 + i * 14 + sinf(t * 3 + i) * 4;
        auto pts = ell(Xf{x, y - 70}, 0, 0, r * 0.55f, r, t * (i % 2 ? -1.5f : 1.f) * 0.3f, 32);
        stroke(pts, 3, i == 1 ? C(255, 40, 200) : C(0, 240, 255));
    }
    blend(SDL_BLENDMODE_BLEND);
    text("EXIT", x, y - 175, 3, C(200, 255, 255), true, 0.4f);
}

static void drawVeg(int type, float x, float y, float rot, float sc) {
    Xf xf{x, y, sc, sc, rot};
    SDL_Color c = VEG[type].col;
    blend(SDL_BLENDMODE_ADD);
    glow(x, y, 26 * sc, c, 0.55f);
    blend(SDL_BLENDMODE_BLEND);
    switch (type) {
        case CUCUMBER: {
            auto b = ell(xf, 0, 0, 12, 5);
            fillPoly(b, C(30, 140, 50));
            stroke(b, 1.5f, C(130, 255, 130));
            for (int i = -1; i <= 1; i++) circle(xf(i * 6.f, -1).x, xf(i * 6.f, -1).y, 1.2f * sc, C(200, 255, 200));
            break;
        }
        case TOMATO: {
            auto b = ell(xf, 0, 0, 8, 7.5f);
            fillPoly(b, C(220, 30, 45));
            stroke(b, 1.5f, C(255, 130, 130));
            for (int i = 0; i < 5; i++) {
                float a = i * 2 * PI / 5;
                tri(xf, 0, -6, cosf(a) * 5, -6 + sinf(a) * 2.5f - 1, cosf(a + 0.6f) * 2, -6 + sinf(a + 0.6f), C(60, 220, 80));
            }
            circle(xf(-3, -3).x, xf(-3, -3).y, 1.8f * sc, C(255, 220, 220, 200));
            break;
        }
        case CARROT: {
            std::vector<SDL_FPoint> b = {xf(15, 0), xf(-9, -5), xf(-9, 5)};
            fillPoly(b, C(240, 120, 20));
            stroke(b, 1.5f, C(255, 200, 100));
            for (int i = -1; i <= 1; i++) { auto a = xf(-9, i * 2.f), e = xf(-16, i * 5.f); line(a.x, a.y, e.x, e.y, 2 * sc, C(80, 230, 90)); }
            for (int i = 0; i < 2; i++) { auto a = xf(-2.f + i * 6, -3), e = xf(-2.f + i * 6, 0); line(a.x, a.y, e.x, e.y, 1, C(160, 70, 10)); }
            break;
        }
        case GARLIC: {
            auto b = ell(xf, 0, 1, 8, 7);
            fillPoly(b, C(235, 225, 250));
            stroke(b, 1.5f, C(190, 140, 255));
            tri(xf, -2.5f, -5, 2.5f, -5, 0, -12, C(220, 210, 240));
            for (int i = -1; i <= 1; i += 2) { auto a = xf(i * 3.f, -4), e = xf(i * 4.f, 6); line(a.x, a.y, e.x, e.y, 1, C(160, 130, 200)); }
            break;
        }
    }
}

static void drawPlayerAt(float cx, float by, float t, float aimx, float aimy) {
    float sy = 1 + P.squash, sx = 1 - P.squash * 0.6f;
    float tilt = clampf(P.vx / 390.f, -1, 1) * 0.08f;
    Xf xf{cx, by, sx, sy, tilt};
    const float W = 30, H = 40;
    blend(SDL_BLENDMODE_ADD);
    glow(cx, by - 22, 70, C(60, 255, 100), 0.35f);
    blend(SDL_BLENDMODE_BLEND);

    // glass body
    auto glass = roundRect(xf, -W / 2, -H, W, H, 7);
    fillPoly(glass, C(140, 220, 255, 45));

    // brine with slosh
    float lvl = -H * 0.74f + sinf(t * 2.3f) * 0.8f, s = P.slosh;
    float l = -W / 2 + 3, r = W / 2 - 3, b = -3, rr = 5;
    std::vector<SDL_FPoint> liq = {xf(l, lvl - s), xf(r, lvl + s)};
    for (int i = 0; i <= 4; i++) { float a = PI * 0.5f * i / 4; liq.push_back(xf(r - rr + rr * cosf(a), b - rr + rr * sinf(a))); }
    for (int i = 0; i <= 4; i++) { float a = PI * 0.5f + PI * 0.5f * i / 4; liq.push_back(xf(l + rr + rr * cosf(a), b - rr + rr * sinf(a))); }
    fillPoly(liq, C(70, 200, 60, 190));
    // pickles
    float bob = sinf(t * 3.f) * 1.2f;
    auto p1 = ell(xf, -6, -13 + bob, 4.2f, 10, 0.25f + s * 0.02f, 14);
    auto p2 = ell(xf, 6, -15 - bob, 4.2f, 10, -0.2f + s * 0.02f, 14);
    fillPoly(p1, C(35, 110, 30)); stroke(p1, 1.2f, C(140, 230, 90));
    fillPoly(p2, C(40, 125, 35)); stroke(p2, 1.2f, C(140, 230, 90));
    // dill
    { auto a = xf(0, -6), e = xf(2, -24); line(a.x, a.y, e.x, e.y, 1.2f, C(120, 200, 80)); }
    // bubbles
    for (int i = 0; i < 4; i++) {
        float bh = fmodf(t * (18 + i * 5) + i * 13, 24.f);
        auto q = xf(-9.f + i * 6, -4 - bh);
        circle(q.x, q.y, 1.4f, C(200, 255, 200, 160));
    }
    // surface line
    { auto a = xf(l, lvl - s), e = xf(r, lvl + s); blend(SDL_BLENDMODE_ADD); line(a.x, a.y, e.x, e.y, 2, C(160, 255, 140)); blend(SDL_BLENDMODE_BLEND); }

    // eyes
    float el = sqrtf(aimx * aimx + aimy * aimy) + 1e-4f;
    float ex = aimx / el * 2.f, ey = aimy / el * 2.f;
    bool blinking = fmodf(t, 3.7f) < 0.12f;
    for (int i = -1; i <= 1; i += 2) {
        auto q = xf(i * 6.f, -27);
        if (blinking) line(q.x - 4, q.y, q.x + 4, q.y, 2, C(20, 30, 20));
        else { circle(q.x, q.y, 4.8f, C(245, 255, 245)); circle(q.x + ex * sx, q.y + ey, 2.3f, C(10, 20, 10)); }
    }
    // glass outline + highlight
    blend(SDL_BLENDMODE_ADD);
    stroke(glass, 2, C(170, 240, 255, 230));
    { auto a = xf(-W / 2 + 5, -H + 9), e = xf(-W / 2 + 5, -12); line(a.x, a.y, e.x, e.y, 2, C(255, 255, 255, 120)); }
    blend(SDL_BLENDMODE_BLEND);
    // lid
    auto lid = roundRect(xf, -W / 2 - 2, -H - 8, W + 4, 9, 3);
    fillPoly(lid, C(70, 20, 80));
    blend(SDL_BLENDMODE_ADD);
    stroke(lid, 2, C(255, 60, 220));
    { auto a = xf(-W / 2, -H - 4), e = xf(W / 2, -H - 4); line(a.x, a.y, e.x, e.y, 1, C(255, 180, 240, 160)); }
    auto lc = xf(0, -H - 4);
    glow(lc.x, lc.y, 26, C(255, 60, 220), 0.4f);
    blend(SDL_BLENDMODE_BLEND);
}

static void drawPlayer() {
    if (P.invuln > 0 && fmodf(P.invuln, 0.14f) < 0.07f) return;
    float cx = P.x + P.w / 2 - camX + shakeX, by = P.y + P.h - camY + shakeY;
    drawPlayerAt(cx, by, gameT, aimX, aimY);
    // aim reticle
    if (useMouseAim && state == PLAY) {
        blend(SDL_BLENDMODE_ADD);
        SDL_Color c = VEG[P.veg].col;
        auto rp = ell(Xf{mouseX, mouseY}, 0, 0, 10, 10, gameT * 2, 4);
        stroke(rp, 2, c);
        glow(mouseX, mouseY, 20, c, 0.4f);
        for (int i = 1; i <= 5; i++) {
            float k = i / 6.f;
            circle(lerpf(cx, mouseX, k), lerpf(by - 30, mouseY, k), 1.5f, C(c.r, c.g, c.b, 90));
        }
        blend(SDL_BLENDMODE_BLEND);
    }
}

static void drawEnemy(const Enemy& e) {
    float cx = e.x + e.w / 2 - camX + shakeX, by = e.y + e.h - camY + shakeY;
    if (cx < -80 || cx > SW + 80) return;
    Xf xf{cx, by, (float)e.dir, 1, 0};
    bool fl = e.flash > 0;
    SDL_Color neon = e.t == RAT ? C(255, 60, 200) : e.t == PIGEON ? C(60, 220, 255) : e.t == CAT ? C(255, 230, 60) : C(255, 140, 40);
    SDL_Color body = fl ? C(255, 255, 255) : C(28, 10, 40);
    SDL_Color line2 = fl ? C(255, 255, 255) : neon;
    SDL_Color eye = C(255, 40, 60);
    float a = e.anim;
    blend(SDL_BLENDMODE_ADD);
    glow(cx, by - e.h / 2, e.w * 1.4f, neon, 0.3f);
    blend(SDL_BLENDMODE_BLEND);
    auto leg = [&](float lx, float ly, float ph) {
        auto p0 = xf(lx, ly), p1 = xf(lx + sinf(a * 14 + ph) * 4, 0);
        line(p0.x, p0.y, p1.x, p1.y, 2.5f, line2);
    };
    auto eyeAt = [&](float lx, float ly, float r, SDL_Color c) {
        auto q = xf(lx, ly);
        blend(SDL_BLENDMODE_ADD); glow(q.x, q.y, r * 5, c, 0.7f); blend(SDL_BLENDMODE_BLEND);
        circle(q.x, q.y, r, c);
    };
    switch (e.t) {
        case RAT: {
            std::vector<SDL_FPoint> tail;
            for (int i = 0; i <= 8; i++) tail.push_back(xf(-14.f - i * 2.6f, -7 + sinf(a * 8 + i * 0.7f) * 3 - i * 0.6f));
            stroke(tail, 2, line2, false);
            leg(-7, -4, 0); leg(7, -4, PI);
            auto bd = ell(xf, 0, -9, 15, 8); fillPoly(bd, body); stroke(bd, 2, line2);
            auto hd = ell(xf, 13, -10, 7.5f, 6, 0.2f); fillPoly(hd, body); stroke(hd, 2, line2);
            auto ear = ell(xf, 9, -17, 4, 4.5f); fillPoly(ear, body); stroke(ear, 2, line2);
            eyeAt(16, -12, 1.8f, eye);
            break;
        }
        case PIGEON: {
            float flap = sinf(a * 16);
            tri(xf, -2, -14, -16, -14 - 12 * flap, 6, -13, fl ? body : C(40, 80, 120));
            auto bd = ell(xf, 0, -11, 13, 8.5f); fillPoly(bd, body); stroke(bd, 2, line2);
            auto hd = ell(xf, 11, -18, 6, 6); fillPoly(hd, body); stroke(hd, 2, line2);
            tri(xf, 16, -19, 23, -17, 16, -15, C(255, 210, 60));
            tri(xf, -12, -10, -20, -6, -18, -13, line2);
            eyeAt(13, -19, 1.6f, eye);
            break;
        }
        case CAT: {
            std::vector<SDL_FPoint> tail;
            for (int i = 0; i <= 8; i++) tail.push_back(xf(-15.f - i * 1.6f, -11 - i * 2.4f + sinf(a * 4 + i * 0.5f) * 2));
            stroke(tail, 3, line2, false);
            float sp = e.dash > 0 ? 2.f : 1.f;
            leg(-9, -4, 0); leg(-4, -4, PI * sp); leg(5, -4, PI * 0.5f); leg(10, -4, PI * 1.5f);
            auto bd = ell(xf, 0, -11, 16, 8); fillPoly(bd, body); stroke(bd, 2, line2);
            tri(xf, 9, -23, 11, -32, 15, -25, line2);
            tri(xf, 16, -25, 20, -32, 21, -22, line2);
            auto hd = ell(xf, 15, -18, 8, 7); fillPoly(hd, body); stroke(hd, 2, line2);
            eyeAt(18, -19, 2.f, C(180, 255, 60));
            break;
        }
        case RACCOON: {
            for (int i = 0; i < 4; i++) {
                auto tp = ell(xf, -20.f - i * 5, -16.f - i * 4 + sinf(a * 5 + i) * 1.5f, 6, 4.5f, -0.6f);
                fillPoly(tp, fl ? body : (i % 2 ? C(30, 20, 20) : C(120, 90, 80))); stroke(tp, 1.5f, line2);
            }
            leg(-10, -5, 0); leg(10, -5, PI);
            auto bd = ell(xf, 0, -15, 19, 13); fillPoly(bd, body); stroke(bd, 2, line2);
            tri(xf, 10, -31, 12, -39, 17, -32, line2);
            tri(xf, 19, -32, 24, -38, 24, -29, line2);
            auto hd = ell(xf, 17, -24, 10, 9); fillPoly(hd, body); stroke(hd, 2, line2);
            auto mask = ell(xf, 19, -25, 8.5f, 3.5f); fillPoly(mask, C(5, 0, 10));
            eyeAt(17, -25, 1.8f, eye); eyeAt(22, -25, 1.8f, eye);
            circle(xf(27, -21).x, xf(27, -21).y, 2, C(20, 10, 20));
            break;
        }
    }
}

static void drawParticles() {
    blend(SDL_BLENDMODE_ADD);
    float ox = -camX + shakeX, oy = -camY + shakeY;
    for (auto& q : parts) {
        float k = clampf(q.life / q.maxLife, 0, 1);
        SDL_Color c = q.c; c.a = (Uint8)(255 * k);
        float x = q.x + ox, y = q.y + oy;
        switch (q.kind) {
            case 0: line(x, y, x - q.vx * 0.03f, y - q.vy * 0.03f, q.size * 0.7f, c); glow(x, y, q.size * 3, q.c, 0.3f * k); break;
            case 1: circle(x, y, q.size * sqrtf(k), c); glow(x, y, q.size * 4, q.c, 0.25f * k); break;
            case 2: { float a = q.life * 20; line(x - cosf(a) * q.size, y - sinf(a) * q.size, x + cosf(a) * q.size, y + sinf(a) * q.size, 1.5f, c); break; }
            case 3: {
                blend(SDL_BLENDMODE_BLEND);
                auto pk = ell(Xf{x, y}, 0, 0, q.size * 0.6f, q.size * 1.4f, q.life * 6, 12);
                fillPoly(pk, C(40, 130, 35, c.a)); stroke(pk, 1.2f, C(140, 230, 90, c.a));
                blend(SDL_BLENDMODE_ADD);
                break;
            }
            case 4: glow(x, y, q.size * (2 - k), q.c, 0.5f * k); break;
        }
    }
    blend(SDL_BLENDMODE_BLEND);
}

static void drawRain(bool front) {
    blend(SDL_BLENDMODE_ADD);
    for (auto& d : rain) {
        if ((d.z > 0.6f) != front) continue;
        float x = fmodf(d.x - camX * d.z, (float)SW + 100);
        if (x < -50) x += SW + 100;
        Uint8 a = (Uint8)(30 + 80 * d.z);
        line(x, d.y, x - d.len * 0.25f, d.y + d.len, 1.f + d.z, C(120, 160, 255, a));
    }
    blend(SDL_BLENDMODE_BLEND);
}

static void drawHeart(float x, float y, float s, bool full) {
    Xf xf{x, y, s, s};
    SDL_Color c = full ? C(255, 50, 120) : C(80, 30, 60);
    if (full) { blend(SDL_BLENDMODE_ADD); glow(x, y, 22 * s, c, 0.45f); blend(SDL_BLENDMODE_BLEND); }
    fillPoly(ell(xf, -4, -2, 5, 5), c);
    fillPoly(ell(xf, 4, -2, 5, 5), c);
    fillPoly({xf(-8.6f, 0), xf(8.6f, 0), xf(0, 10)}, c);
}

static void drawHUD() {
    for (int i = 0; i < 5; i++) drawHeart(34 + i * 34.f, 34, 1.2f, i < P.hp);
    text("LVL " + std::to_string(level), 22, 58, 3, C(150, 120, 255), false, 0.25f);
    char buf[32]; snprintf(buf, sizeof buf, "%07d", score);
    text(buf, SW / 2, 18, 5, C(0, 240, 255), true, 0.35f);
    if (combo > 1 && comboT > 0) text("COMBO X" + std::to_string(std::min(combo, 8)), SW / 2, 62, 3, C(255, 220, 60), true, 0.4f);

    for (int i = 0; i < VEG_N; i++) {
        float x = SW - 4 * 66.f - 14 + i * 66, y = 14;
        bool sel = i == P.veg;
        SDL_Color c = VEG[i].col;
        rect(x, y, 58, 58, C(10, 5, 25, 200));
        if (sel) {
            neonLine(x, y, x + 58, y, c, 2); neonLine(x, y + 58, x + 58, y + 58, c, 2);
            neonLine(x, y, x, y + 58, c, 2); neonLine(x + 58, y, x + 58, y + 58, c, 2);
            float cd = clampf(P.cooldown / VEG[i].cooldown, 0, 1);
            rect(x, y + 62, 58 * (1 - cd), 4, c);
        } else {
            SDL_Color d = C(c.r / 3, c.g / 3, c.b / 3);
            stroke({{x, y}, {x + 58, y}, {x + 58, y + 58}, {x, y + 58}}, 1.5f, d);
        }
        drawVeg(i, x + 29, y + 31, i == CARROT ? -0.6f : 0.3f, sel ? 1.6f : 1.3f);
        text(std::to_string(i + 1), x + 4, y + 4, 2, C(200, 200, 220, 180));
    }
    text(VEG[P.veg].name, SW - 4 * 66.f - 14 + 2 * 66 - 4, 88, 2, VEG[P.veg].col, true, 0.3f);

    // progress bar
    float px0 = 200, px1 = SW - 200, py = SH - 22;
    rect(px0, py, px1 - px0, 3, C(60, 40, 90, 200));
    float k = clampf((P.x) / goalX, 0, 1);
    rect(px0, py, (px1 - px0) * k, 3, C(80, 255, 120));
    blend(SDL_BLENDMODE_ADD);
    glow(lerpf(px0, px1, k), py + 1, 14, C(80, 255, 120), 0.8f);
    glow(px1, py + 1, 16, C(0, 240, 255), 0.8f);
    blend(SDL_BLENDMODE_BLEND);

    if (hintT > 0) {
        Uint8 a = (Uint8)(255 * clampf(hintT, 0, 1));
        text("A/D MOVE   SPACE JUMP   S+SPACE DROP", SW / 2, SH - 90, 2, C(200, 220, 255, a), true);
        text("MOUSE AIM + LMB THROW  /  J THROW   1-4 Q/E WHEEL: VEGGIES", SW / 2, SH - 66, 2, C(200, 220, 255, a), true);
    }
}

static void drawOverlayScreen() {
    if (state == TITLE) {
        rect(0, 0, SW, SH, C(5, 0, 15, 120));
        float p = sinf(gameT * 3) * 0.1f;
        text("RASSOL", SW / 2, 150, 16, C(90, 255, 120), true, 0.5f + p);
        text("CYBER BRINE RUNNER", SW / 2, 290, 5, C(255, 50, 200), true, 0.45f);
        P.squash = sinf(gameT * 4) * 0.06f;
        drawPlayerAt(SW / 2, 480, gameT, cosf(gameT), sinf(gameT * 0.7f));
        if (fmodf(gameT, 1.f) < 0.65f) text("PRESS ENTER", SW / 2, 540, 4, C(0, 240, 255), true, 0.5f);
        text("THROW VEGGIES AT THE CITY CRITTERS. REACH THE EXIT.", SW / 2, 610, 2, C(200, 190, 255), true);
        text("M: MUSIC  F: FULLSCREEN  ESC: QUIT", SW / 2, 640, 2, C(150, 140, 200), true);
    } else if (state == DEAD) {
        rect(0, 0, SW, SH, C(20, 0, 10, (int)std::min(170.f, stateT * 200)));
        text("JAR BROKEN", SW / 2, 230, 12, C(255, 40, 80), true, 0.55f);
        text("SCORE " + std::to_string(score), SW / 2, 370, 5, C(0, 240, 255), true, 0.4f);
        if (stateT > 1 && fmodf(gameT, 1.f) < 0.65f) text("PRESS R TO RETRY", SW / 2, 450, 4, C(255, 220, 60), true, 0.4f);
    } else if (state == WIN) {
        rect(0, 0, SW, SH, C(0, 10, 20, (int)std::min(150.f, stateT * 200)));
        text("LEVEL CLEAR", SW / 2, 220, 11, C(0, 240, 255), true, 0.55f);
        text("SCORE " + std::to_string(score), SW / 2, 360, 5, C(90, 255, 120), true, 0.4f);
        if (stateT > 1 && fmodf(gameT, 1.f) < 0.65f) text("PRESS ENTER FOR NEXT LEVEL", SW / 2, 440, 4, C(255, 220, 60), true, 0.4f);
    }
}

static void render() {
    SDL_RenderCopy(R, texSky, nullptr, nullptr);
    drawLayers();
    drawRain(false);
    drawTiles();
    drawPortal();
    for (auto& e : enemies) if (!e.dead) drawEnemy(e);
    for (auto& p : projs) {
        if (p.dead) continue;
        drawVeg(p.type, p.x - camX + shakeX, p.y - camY + shakeY, p.rot, 1.f);
    }
    if (state == PLAY || state == WIN) drawPlayer();
    drawParticles();
    drawRain(true);
    for (auto& pp : popups) {
        SDL_Color c = pp.c; c.a = (Uint8)(255 * clampf(pp.life * 1.5f, 0, 1));
        text(pp.s, pp.x - camX + shakeX, pp.y - camY + shakeY, 2, c, true, 0.3f * pp.life);
    }
    SDL_RenderCopy(R, texOverlay, nullptr, nullptr);
    if (state != TITLE) drawHUD();
    drawOverlayScreen();
}

// ============================================================================
// MAIN
// ============================================================================
int main(int argc, char** argv) {
    int smokeFrames = 0; const char* shotPath = nullptr;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--smoke") && i + 1 < argc) smokeFrames = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--shot") && i + 1 < argc) shotPath = argv[++i];
    }
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO | SDL_INIT_EVENTS) != 0) { fprintf(stderr, "SDL: %s\n", SDL_GetError()); return 1; }
    SDL_Window* win = SDL_CreateWindow("RASSOL: Cyber Brine Runner", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, SW, SH,
                                       SDL_WINDOW_RESIZABLE | SDL_WINDOW_ALLOW_HIGHDPI);
    const char* vs = getenv("RASSOL_VSYNC");
    bool useVsync = vs && vs[0] == '1';
    R = SDL_CreateRenderer(win, -1, SDL_RENDERER_ACCELERATED | (useVsync ? SDL_RENDERER_PRESENTVSYNC : 0) | SDL_RENDERER_TARGETTEXTURE);
    if (!R) R = SDL_CreateRenderer(win, -1, SDL_RENDERER_TARGETTEXTURE);
    if (!R) { fprintf(stderr, "renderer: %s\n", SDL_GetError()); return 1; }
    bool perf = getenv("RASSOL_PERF") != nullptr;
    if (perf) { SDL_RendererInfo ri; SDL_GetRendererInfo(R, &ri); fprintf(stderr, "renderer: %s  video: %s\n", ri.name, SDL_GetCurrentVideoDriver()); }

    texGlow = makeTex(128, 128, [](int x, int y) {
        float dx = (x - 63.5f) / 64.f, dy = (y - 63.5f) / 64.f, d = sqrtf(dx * dx + dy * dy);
        float a = clampf(1 - d, 0, 1); a = a * a * a;
        return C(255, 255, 255, (int)(a * 255));
    }, SDL_BLENDMODE_ADD);
    texBar = makeTex(128, 32, [](int x, int y) {
        float dy = (y - 15.5f) / 16.f, g = expf(-dy * dy * 5.f) - expf(-5.f);
        float ex = std::min(x, 127 - x) / 24.f; ex = clampf(ex, 0, 1);
        return C(255, 255, 255, (int)(clampf(g, 0, 1) * ex * 255));
    }, SDL_BLENDMODE_ADD);
    texOverlay = makeTex(SW, SH, [](int x, int y) {
        float dx = (x - SW / 2.f) / (SW / 2.f), dy = (y - SH / 2.f) / (SH / 2.f);
        float v = clampf(powf(sqrtf(dx * dx * 0.8f + dy * dy) / 1.3f, 2.4f), 0, 1) * 0.75f;
        float sl = (y % 3 == 0) ? 0.13f : 0.f;
        return C(0, 0, 5, (int)(clampf(v + sl, 0, 1) * 255));
    }, SDL_BLENDMODE_BLEND);
    for (int i = 0; i < 3; i++) texLayer[i] = makeLayer(i);
    texSky = makeSky();
    texTile = makeTex((int)TS, (int)TS, [](int x, int y) {
        bool border = x < 3 || y < 3 || x >= TS - 3 || y >= TS - 3;
        return border ? C(13, 8, 30) : C(20, 12, 44);
    }, SDL_BLENDMODE_NONE);
    // Everything is drawn into a fixed 1280x720 buffer and upscaled once, so
    // fullscreen 1080p/1440p costs no extra overdraw on an integrated GPU.
    texScreen = SDL_CreateTexture(R, SDL_PIXELFORMAT_RGBA8888, SDL_TEXTUREACCESS_TARGET, SW, SH);
    SDL_SetTextureBlendMode(texScreen, SDL_BLENDMODE_NONE);
    SDL_RenderSetLogicalSize(R, SW, SH);

    for (int i = 0; i < 220; i++)
        rain.push_back(Drop{frand(0, SW + 100.f), frand(0, SH), frand(0.1f, 1.f), 0, 0, 0});
    for (auto& d : rain) { d.speed = 700 + 900 * d.z; d.len = 8 + 18 * d.z; }

    snd::init();
    genLevel(1);
    P.x = 4 * TS; P.y = 10 * TS;

    float vsyncDt = 1.f / 60.f;
    SDL_DisplayMode dm;
    if (SDL_GetCurrentDisplayMode(std::max(0, SDL_GetWindowDisplayIndex(win)), &dm) == 0 && dm.refresh_rate > 0) vsyncDt = 1.f / dm.refresh_rate;
    float dtHist[4] = {vsyncDt, vsyncDt, vsyncDt, vsyncDt};
    unsigned dtIdx = 0;
    Uint64 freq = SDL_GetPerformanceFrequency(), last = SDL_GetPerformanceCounter();
    bool running = true;
    int frame = 0;
    float musicI = 0.3f;
    while (running) {
        SDL_Event ev;
        while (SDL_PollEvent(&ev)) {
            switch (ev.type) {
                case SDL_QUIT: running = false; break;
                case SDL_KEYDOWN: {
                    if (ev.key.repeat) break;
                    auto k = ev.key.keysym.sym;
                    if (k == SDLK_ESCAPE) running = false;
                    else if (k == SDLK_m) snd::musicOn = !snd::musicOn;
                    else if (k == SDLK_f || k == SDLK_F11) {
                        bool fs = SDL_GetWindowFlags(win) & SDL_WINDOW_FULLSCREEN_DESKTOP;
                        SDL_SetWindowFullscreen(win, fs ? 0 : SDL_WINDOW_FULLSCREEN_DESKTOP);
                    } else if (state == TITLE && (k == SDLK_RETURN || k == SDLK_SPACE)) startLevel(true);
                    else if (state == DEAD && stateT > 0.6f && (k == SDLK_r || k == SDLK_RETURN)) startLevel(true);
                    else if (state == WIN && stateT > 0.6f && k == SDLK_RETURN) { level++; startLevel(false); }
                    else if (state == PLAY) {
                        if (k == SDLK_SPACE || k == SDLK_w || k == SDLK_UP || k == SDLK_k) { P.jumpBuf = 0.13f; P.jumpHeld = true; }
                        else if (k == SDLK_j || k == SDLK_LSHIFT) { keyFire = true; useMouseAim = false; }
                        else if (k >= SDLK_1 && k <= SDLK_4) { P.veg = k - SDLK_1; sfxSwitch(); }
                        else if (k == SDLK_q) { P.veg = (P.veg + VEG_N - 1) % VEG_N; sfxSwitch(); }
                        else if (k == SDLK_e) { P.veg = (P.veg + 1) % VEG_N; sfxSwitch(); }
                    }
                    break;
                }
                case SDL_KEYUP: {
                    auto k = ev.key.keysym.sym;
                    if (k == SDLK_SPACE || k == SDLK_w || k == SDLK_UP || k == SDLK_k) {
                        P.jumpHeld = false;
                        if (P.vy < 0) P.vy *= 0.45f;  // variable jump height
                    }
                    if (k == SDLK_j || k == SDLK_LSHIFT) keyFire = false;
                    break;
                }
                case SDL_MOUSEBUTTONDOWN: if (ev.button.button == SDL_BUTTON_LEFT) { mouseFire = true; useMouseAim = true; } break;
                case SDL_MOUSEBUTTONUP: if (ev.button.button == SDL_BUTTON_LEFT) mouseFire = false; break;
                case SDL_MOUSEMOTION: mouseX = (float)ev.motion.x; mouseY = (float)ev.motion.y; useMouseAim = true; break;
                case SDL_MOUSEWHEEL:
                    if (state == PLAY) { P.veg = (P.veg + (ev.wheel.y > 0 ? VEG_N - 1 : 1)) % VEG_N; sfxSwitch(); }
                    break;
            }
        }

        Uint64 now = SDL_GetPerformanceCounter();
        float rawDt = (float)((double)(now - last) / (double)freq);
        last = now;
        // Frame pacing: measured frame times jitter by about 1ms around the vsync
        // period, which shows up as micro-stutter. Snap to whole vsync periods and
        // average the last 4 frames so motion advances by an even step each frame;
        // a missed vblank is then caught up over several frames, not in one jump.
        float snapped = std::min(rawDt, 0.1f);
        for (int k = 1; k <= 6; k++)
            if (fabsf(snapped - k * vsyncDt) < 0.0015f) { snapped = k * vsyncDt; break; }
        dtHist[dtIdx++ & 3] = snapped;
        float dt = std::min((dtHist[0] + dtHist[1] + dtHist[2] + dtHist[3]) * 0.25f, 0.05f);
        if (smokeFrames && !perf) dt = 1.f / 60.f;
        gameT += dt; stateT += dt; hintT -= dt; comboT -= dt;
        if (comboT <= 0) combo = 0;

        const Uint8* ks = SDL_GetKeyboardState(nullptr);

        // smoke-test autopilot: run right, jump, throw
        static Uint8 fakeKeys[SDL_NUM_SCANCODES];
        if (smokeFrames) {
            if (state == TITLE && frame > 5) startLevel(true);
            memset(fakeKeys, 0, sizeof fakeKeys);
            fakeKeys[SDL_SCANCODE_D] = 1;
            ks = fakeKeys;
            if (frame % 40 == 0) { P.jumpBuf = 0.13f; P.jumpHeld = true; }
            if (frame % 40 == 25) P.jumpHeld = false;
            mouseFire = true; mouseX = SW * 0.8f; mouseY = SH * 0.6f;
            if (frame % 90 == 0) P.veg = (P.veg + 1) % VEG_N;
            if (state == DEAD && stateT > 1) startLevel(true);
        }

        // aim
        if (useMouseAim) {
            float pcx = P.x + P.w / 2 - camX, pcy = P.y + 10 - camY;
            float dx = mouseX - pcx, dy = mouseY - pcy, l = sqrtf(dx * dx + dy * dy);
            if (l > 1) { aimX = dx / l; aimY = dy / l; }
            if (state == PLAY && fabsf(dx) > 4) P.facing = dx > 0 ? 1 : -1;
        } else {
            float l = sqrtf(1 + 0.18f * 0.18f);
            aimX = P.facing / l; aimY = -0.18f / l;
        }

        if (hitstop > 0) hitstop -= dt;
        else if (state == PLAY || state == DEAD || state == WIN) {
            int n = (int)ceilf(dt / (1.f / 240.f));
            float h = dt / n;
            for (int i = 0; i < n; i++) stepGame(h, ks);
        }
        projs.erase(std::remove_if(projs.begin(), projs.end(), [](const Proj& p) { return p.dead; }), projs.end());
        for (auto& pp : popups) { pp.y -= 50 * dt; pp.life -= dt; }
        popups.erase(std::remove_if(popups.begin(), popups.end(), [](const Popup& p) { return p.life <= 0; }), popups.end());

        // projectile trails + brine drips
        for (auto& p : projs) spawnP(p.x, p.y, 0, 0, 0.22f, 2.2f, VEG[p.type].col, 1, 0, 0);
        if (state == PLAY && P.onGround && fabsf(P.vx) > 220) {
            P.dripT -= dt;
            if (P.dripT <= 0) { P.dripT = 0.06f; spawnP(P.x + P.w / 2 - P.facing * 10, P.y + P.h - 4, -P.vx * 0.2f + frand(-40, 40), frand(-160, -60), 0.5f, 2, C(100, 255, 110), 1, 900); }
        }

        // camera
        if (state == TITLE) camX += 90 * dt;
        else if (state == PLAY) {
            // Look-ahead eases on its own slow spring: flipping the aim across the
            // jar used to yank the camera 220px within a few frames.
            camLook += (P.facing * 110 + P.vx * 0.18f - camLook) * (1 - expf(-2.5f * dt));
            float target = clampf(P.x + P.w / 2 - SW / 2 + camLook, 0, LW * TS - SW);
            camX += (target - camX) * (1 - expf(-7.f * dt));
        }
        trauma = std::max(0.f, trauma - dt * 1.6f);
        float sh = trauma * trauma * 16;
        shakeX = sh * (sinf(gameT * 71) + 0.5f * sinf(gameT * 113)) / 1.5f;
        shakeY = sh * (sinf(gameT * 83 + 1) + 0.5f * sinf(gameT * 127)) / 1.5f;

        for (auto& d : rain) {
            d.y += d.speed * dt; d.x -= d.speed * 0.25f * dt;
            if (d.y > SH) { d.y = -20; d.x = frand(0, SW + 100.f); }
            if (d.x < -50) d.x += SW + 100;
        }

        // music tension
        float target = 0.25f;
        if (state == PLAY) {
            int near = 0;
            for (auto& e : enemies) if (!e.dead && fabsf(e.x - P.x) < 650) near++;
            target = 0.38f + near * 0.12f + (P.hp <= 2 ? 0.25f : 0.f);
        } else if (state == DEAD) target = 0.1f;
        else if (state == WIN) target = 0.5f;
        musicI += (clampf(target, 0, 1) - musicI) * std::min(1.f, dt * 1.5f);
        snd::intensity = musicI;

        Uint64 tR0 = SDL_GetPerformanceCounter();
        SDL_SetRenderTarget(R, texScreen);
        render();
        SDL_SetRenderTarget(R, nullptr);
        SDL_SetRenderDrawColor(R, 0, 0, 0, 255);
        SDL_RenderClear(R);
        SDL_RenderCopy(R, texScreen, nullptr, nullptr);
        Uint64 tR1 = SDL_GetPerformanceCounter();
        frame++;
        if (smokeFrames && frame == smokeFrames - 1 && shotPath) {
            int w, h; SDL_GetRendererOutputSize(R, &w, &h);
            SDL_Surface* s = SDL_CreateRGBSurfaceWithFormat(0, w, h, 32, SDL_PIXELFORMAT_ARGB8888);
            SDL_RenderReadPixels(R, nullptr, SDL_PIXELFORMAT_ARGB8888, s->pixels, s->pitch);
            SDL_SaveBMP(s, shotPath);
            SDL_FreeSurface(s);
        }
        SDL_RenderPresent(R);
        if (perf) {
            Uint64 tP = SDL_GetPerformanceCounter();
            auto ms = [&](Uint64 a, Uint64 b) { return (double)(b - a) * 1000.0 / freq; };
            static int slow = 0; static double sDt = 0, mDt = 0, sUp = 0, sRe = 0, mRe = 0, sPr = 0, mPr = 0; static int cnt = 0;
            double up = ms(now, tR0), re = ms(tR0, tR1), pr = ms(tR1, tP);
            slow += rawDt > 1.f / 60.f; sDt += dt * 1000; mDt = std::max(mDt, (double)rawDt * 1000); sUp += up; sRe += re; mRe = std::max(mRe, re); sPr += pr; mPr = std::max(mPr, pr);
            if (++cnt == 120) {
                fprintf(stderr, "<60fps %d  dt %.2f rawmax %.2f  upd %.2f  rend %.2f/%.2f  present %.2f/%.2f  parts %zu\n", slow, sDt / cnt, mDt, sUp / cnt, sRe / cnt, mRe, sPr / cnt, mPr, parts.size());
                slow = 0; sDt = mDt = sUp = sRe = mRe = sPr = mPr = 0; cnt = 0;
            }
        }
        if (smokeFrames && frame >= smokeFrames) running = false;
        if (!useVsync) {
            // Own frame pacing: sleep most of the way, spin the last ~3ms (SDL_Delay oversleeps).
            static Uint64 next = 0;
            Uint64 period = (Uint64)(vsyncDt * freq), t = SDL_GetPerformanceCounter();
            if (next == 0 || t > next + period) next = t;
            next += period;
            for (;;) {
                t = SDL_GetPerformanceCounter();
                if (t >= next) break;
                double left = (double)(next - t) / freq;
                if (left > 0.004) SDL_Delay((Uint32)((left - 0.003) * 1000));
            }
        }
    }
    if (snd::dev) SDL_CloseAudioDevice(snd::dev);
    SDL_DestroyRenderer(R);
    SDL_DestroyWindow(win);
    SDL_Quit();
    return 0;
}
