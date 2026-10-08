// UHA-PhysAI: a complete closed-loop physical-AI pipeline (C++17), integer runtime.
//
//   plant (stand-in for the real world, double)  -->  noisy quantized sensors
//   --> [offline] law identification with Occam selection + falsification
//   --> fixed-point model (Q32.32, saturating, NOT mod-2^64 wrap)
//   --> [online, integer only] policy -> total decoder -> safety shield -> actuator
//
// Guarantee by construction : the applied force is always within [-Fmax, Fmax].
// Guarantee by test only    : |q| <= qmax (braking-distance shield, checked empirically).
// NOT guaranteed            : behaviour under model structure error, sensor faults,
//                             real-hardware timing. The plant here is simulated.
//
// License: Apache 2.0 / Author: Takeo Yamamoto
// Build: g++ -O2 -std=c++17 -Wall -Wextra uha_physai.cpp -o uha_physai && ./uha_physai
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <random>
#include <vector>

using i64 = int64_t;
using i128 = __int128;

// ---------------- saturating fixed point Q32.32 ----------------
constexpr int FB = 32;
constexpr i64 ONE = 1LL << FB;
inline i64 fx(double x) { return (i64)std::llround(x * (double)ONE); }
inline double dbl(i64 x) { return (double)x / (double)ONE; }
inline i64 clamp128(i128 x) {
    if (x > INT64_MAX) return INT64_MAX;
    if (x < INT64_MIN) return INT64_MIN;
    return (i64)x;
}
inline i64 sadd(i64 a, i64 b) { return clamp128((i128)a + b); }
inline i64 fmul(i64 a, i64 b) { return clamp128(((i128)a * b) >> FB); }
inline i64 sat(i64 x, i64 lo, i64 hi) { return x < lo ? lo : (x > hi ? hi : x); }
inline i64 iabs(i64 x) { return x < 0 ? (x == INT64_MIN ? INT64_MAX : -x) : x; }

// ---------------- the "real world" stand-in ----------------
struct Rng {
    std::mt19937_64 g;
    explicit Rng(uint64_t s) : g(s) {}
    double uni(double a, double b) { return std::uniform_real_distribution<double>(a, b)(g); }
    double nrm(double s) { return std::normal_distribution<double>(0.0, s)(g); }
};

struct Plant {  // m q'' = -k q - c v + u   (unknown to the AI)
    double m = 1.0, k = 4.0, c = 0.3, dt = 0.01, Fmax = 3.0;
    double sq = 1e-5, sv = 2e-4, res = 1.0 / 65536.0;  // sensor spec
    double q = 0, v = 0;
    void step(double u) {
        u = std::max(-Fmax, std::min(Fmax, u));  // actuator limit
        double a = (-k * q - c * v + u) / m;
        v += dt * a;  // semi-implicit Euler
        q += dt * v;
    }
    void sense(Rng& r, double& qm, double& vm) const {
        qm = std::round((q + r.nrm(sq)) / res) * res;  // encoder
        vm = v + r.nrm(sv);                            // tachometer
    }
};

// ---------------- law identification (offline) ----------------
struct Row { double f[3]; double y; };  // features q, v, u ; target accel
struct Fit { std::vector<int> feats; double th[3] = {0, 0, 0}; double rms = 0; };

static Fit fitLS(const std::vector<Row>& rows, const std::vector<int>& feats) {
    int n = (int)feats.size();
    double A[3][4] = {};
    for (const Row& r : rows) {
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) A[i][j] += r.f[feats[i]] * r.f[feats[j]];
            A[i][n] += r.f[feats[i]] * r.y;
        }
    }
    for (int c = 0; c < n; ++c) {  // Gaussian elimination, partial pivoting
        int p = c;
        for (int i = c + 1; i < n; ++i) if (std::fabs(A[i][c]) > std::fabs(A[p][c])) p = i;
        for (int j = 0; j <= n; ++j) std::swap(A[c][j], A[p][j]);
        for (int i = 0; i < n; ++i) {
            if (i == c) continue;
            double f = A[i][c] / A[c][c];
            for (int j = c; j <= n; ++j) A[i][j] -= f * A[c][j];
        }
    }
    Fit ft; ft.feats = feats;
    for (int i = 0; i < n; ++i) ft.th[i] = A[i][n] / A[i][i];
    double s = 0;
    for (const Row& r : rows) {
        double e = r.y;
        for (int i = 0; i < n; ++i) e -= ft.th[i] * r.f[feats[i]];
        s += e * e;
    }
    ft.rms = std::sqrt(s / (double)rows.size());
    return ft;
}

static std::vector<Row> collect(uint64_t seed, int N) {
    Plant P; Rng r(seed);
    std::vector<Row> rows; rows.reserve(N);
    double u = 0; double qm, vm, qm2, vm2;
    P.sense(r, qm, vm);
    for (int t = 0; t < N; ++t) {
        if (t % 20 == 0) u = r.uni(-0.8 * P.Fmax, 0.8 * P.Fmax);
        P.step(u);
        P.sense(r, qm2, vm2);
        rows.push_back({{qm, vm, u}, (vm2 - vm) / P.dt});
        qm = qm2; vm = vm2;
    }
    return rows;
}

// ---------------- runtime (integer only) ----------------
struct Model { i64 A = 0, B = 0, G = 0; };  // a = A q + B v + G u

static void predict(const Model& M, i64 dt, i64 q, i64 v, i64 u, i64& q2, i64& v2) {
    i64 a = sadd(sadd(fmul(M.A, q), fmul(M.B, v)), fmul(M.G, u));
    v2 = sadd(v, fmul(dt, a));
    q2 = sadd(q, fmul(dt, v2));
}

struct Shield {
    Model M; i64 dt, Fmax, qmax, coef;  // coef = 2 * margin * (Fmax * G)  [braking decel]
    bool ok(i64 q, i64 v, i64 u) const {
        i64 q2, v2; predict(M, dt, q, v, u, q2, v2);
        i64 aq = iabs(q2);
        if (aq > qmax) return false;
        i64 vo = q2 >= 0 ? v2 : -v2;  // outward velocity
        if (vo <= 0) return true;
        return fmul(vo, vo) <= fmul(coef, qmax - aq);  // v^2 <= 2*a_brake*margin*distance
    }
    i64 filter(i64 q, i64 v, i64 u) const {
        const i64 cand[3] = {u, u / 2, 0};
        for (i64 c : cand) if (ok(q, v, c)) return c;
        int s = v > 0 ? 1 : (v < 0 ? -1 : (q >= 0 ? 1 : -1));
        return -(i64)s * Fmax;  // full brake: always inside [-Fmax, Fmax]
    }
};

using Policy = std::function<i64(i64 q, i64 v)>;  // returns an arbitrary raw int64

struct World {
    Plant P; Shield S; i64 Fmax;
};

constexpr double QSPEC = 0.25;  // safety specification: |q| <= QSPEC (true plant)
constexpr double QSHIELD = 0.23;  // shield works on a tighter inner limit (noise / model margin)

struct EpRes { double maxq = 0; int viol = 0; int interv = 0; int satn = 0; int steps = 0; double sserr = 0; uint64_t hash = 14695981039346656037ULL; };

static EpRes runEpisode(const Policy& pol, bool shieldOn, const Shield& S, uint64_t seed,
                        double q0, int T, double qref) {
    Plant P; Rng r(seed); P.q = q0; P.v = 0;
    EpRes e; e.steps = T;
    double acc = 0; int cnt = 0;
    for (int t = 0; t < T; ++t) {
        double qm, vm; P.sense(r, qm, vm);
        i64 q = fx(qm), v = fx(vm);
        i64 raw = pol(q, v);
        i64 ud = sat(raw, -S.Fmax, S.Fmax);                // total decoder
        i64 u = shieldOn ? S.filter(q, v, ud) : ud;        // shield
        if (u != ud) ++e.interv;
        if (raw != ud) ++e.satn;
        e.hash = (e.hash ^ (uint64_t)u) * 1099511628211ULL;
        P.step(dbl(u));
        double aq = std::fabs(P.q);
        e.maxq = std::max(e.maxq, aq);
        if (aq > QSPEC) ++e.viol;
        if (t >= T - 300) { acc += std::fabs(P.q - qref); ++cnt; }
    }
    e.sserr = cnt ? acc / cnt : 0;
    return e;
}

int main() {
    // ===== 1. law identification with Occam selection and falsification =====
    Plant truth;
    auto train = collect(1, 20000), valid = collect(2, 5000);
    const double floorRms = std::sqrt(2.0) * truth.sv / truth.dt;  // noise floor of accel target
    const double thr = 1.2 * floorRms;
    std::printf("== identification ==\nnoise floor %.4f, threshold %.4f\n", floorRms, thr);
    struct Cand { const char* name; std::vector<int> f; };
    std::vector<Cand> cands = {{"free  : a = G u", {2}},
                               {"spring: a = A q + G u", {0, 2}},
                               {"damped: a = A q + B v + G u", {0, 1, 2}}};
    int pick = -1; std::vector<Fit> fits;
    for (size_t i = 0; i < cands.size(); ++i) {
        Fit f = fitLS(train, cands[i].f);
        // validation RMS with the fitted parameters
        double s = 0;
        for (const Row& r : valid) {
            double e = r.y;
            for (size_t j = 0; j < f.feats.size(); ++j) e -= f.th[j] * r.f[f.feats[j]];
            s += e * e;
        }
        double vr = std::sqrt(s / (double)valid.size());
        bool accept = vr <= thr;
        std::printf("  %-30s train rms %.4f  valid rms %.4f  %s\n", cands[i].name, f.rms, vr,
                    accept ? "ACCEPT" : "falsified");
        fits.push_back(f);
        if (accept && pick < 0) pick = (int)i;  // smallest model that survives
    }
    if (pick < 0) { std::printf("no model survived\n"); return 1; }
    const Fit& F = fits[pick];
    double th[3] = {0, 0, 0};
    for (size_t j = 0; j < F.feats.size(); ++j) th[F.feats[j]] = F.th[j];  // th[q], th[v], th[u]
    double m_est = 1.0 / th[2], k_est = -th[0] * m_est, c_est = -th[1] * m_est;
    std::printf("selected: %s\n", cands[pick].name);
    std::printf("  m  true %.4f  est %.4f  (rel err %.2f%%)\n", truth.m, m_est, 100 * std::fabs(m_est / truth.m - 1));
    std::printf("  k  true %.4f  est %.4f  (rel err %.2f%%)\n", truth.k, k_est, 100 * std::fabs(k_est / truth.k - 1));
    std::printf("  c  true %.4f  est %.4f  (rel err %.2f%%)\n", truth.c, c_est, 100 * std::fabs(c_est / truth.c - 1));

    // ===== 2. quantize to fixed point =====
    Model M{fx(th[0]), fx(th[1]), fx(th[2])};
    double qerr = std::max({std::fabs(dbl(M.A) - th[0]), std::fabs(dbl(M.B) - th[1]), std::fabs(dbl(M.G) - th[2])});
    std::printf("fixed-point parameter error %.3e (resolution %.3e)\n", qerr, 1.0 / (double)ONE);

    Shield S;
    S.M = M; S.dt = fx(truth.dt); S.Fmax = fx(truth.Fmax); S.qmax = fx(QSHIELD);
    S.coef = fmul(fx(1.6), fmul(S.Fmax, M.G));

    // ===== 3. policies (arbitrary raw int64 outputs) =====
    Rng wr(7);
    i64 W1[8][2], b1[8], W2[8], b2;
    for (int i = 0; i < 8; ++i) { W1[i][0] = fx(wr.uni(-4, 4)); W1[i][1] = fx(wr.uni(-4, 4)); b1[i] = fx(wr.uni(-1, 1)); W2[i] = fx(wr.uni(-4, 4)); }
    b2 = fx(wr.uni(-1, 1));
    Policy pd = [&](i64 q, i64 v) { return sadd(fmul(fx(60), fx(0.1) - q), -fmul(fx(12), v)); };
    Policy mlp = [&](i64 q, i64 v) {
        i64 out = b2;
        for (int i = 0; i < 8; ++i) {
            i64 h = sadd(sadd(fmul(W1[i][0], fmul(fx(20), q)), fmul(W1[i][1], v)), b1[i]);
            if (h < 0) h = 0;
            out = sadd(out, fmul(W2[i], h));
        }
        return fmul(fx(300), out);
    };
    Policy bang = [&](i64 q, i64) { return q >= 0 ? INT64_MAX : INT64_MIN; };  // pushes outward
    Rng gr(99);
    Policy garbage = [&](i64, i64) { return (i64)gr.g(); };                    // any 64-bit value
    struct Pol { const char* name; const Policy* p; };
    Pol pols[] = {{"PD reference", &pd}, {"untrained MLP", &mlp}, {"adversarial bang", &bang}, {"garbage int64", &garbage}};

    // ===== 4. closed-loop safety sweep =====
    std::printf("\n== closed loop: 50 episodes x 2000 steps per policy, spec |q| <= %.2f m, shield inner limit %.2f m ==\n", QSPEC, QSHIELD);
    std::printf("%-18s | decoder-sat%% | shield OFF: viol.eps  max|q| | shield ON: viol.eps  max|q|  interv.%%\n", "policy");
    for (const Pol& pp : pols) {
        int vOff = 0, vOn = 0; double mOff = 0, mOn = 0; long iv = 0, st = 0, sn = 0;
        Rng ir(5);
        for (int ep = 0; ep < 50; ++ep) {
            double q0 = ir.uni(-0.2, 0.2);
            EpRes a = runEpisode(*pp.p, false, S, 1000 + ep, q0, 2000, 0.1);
            EpRes b = runEpisode(*pp.p, true, S, 1000 + ep, q0, 2000, 0.1);
            vOff += a.viol > 0; vOn += b.viol > 0;
            mOff = std::max(mOff, a.maxq); mOn = std::max(mOn, b.maxq);
            iv += b.interv; st += b.steps; sn += b.satn;
        }
        std::printf("%-18s | %10.1f%% | %20d  %8.4f | %19d  %8.4f  %6.2f%%\n", pp.name, 100.0 * (double)sn / (double)st, vOff, mOff, vOn, mOn, 100.0 * (double)iv / (double)st);
    }

    // ===== 4b. 200 random untrained MLPs (wider weights), 3 episodes each =====
    {
        int badOff = 0, badOn = 0; double worstOn = 0, worstOff = 0;
        for (int s = 0; s < 200; ++s) {
            Rng w(5000 + s);
            i64 V1[8][2], c1[8], V2[8], c2;
            for (int i = 0; i < 8; ++i) {
                V1[i][0] = fx(w.uni(-6, 6)); V1[i][1] = fx(w.uni(-6, 6));
                c1[i] = fx(w.uni(-2, 2)); V2[i] = fx(w.uni(-6, 6));
            }
            c2 = fx(w.uni(-2, 2));
            Policy net = [&](i64 q, i64 v) {
                i64 out = c2;
                for (int i = 0; i < 8; ++i) {
                    i64 h = sadd(sadd(fmul(V1[i][0], fmul(fx(20), q)), fmul(V1[i][1], v)), c1[i]);
                    if (h < 0) h = 0;
                    out = sadd(out, fmul(V2[i], h));
                }
                return fmul(fx(300), out);
            };
            bool off = false, on = false;
            for (int ep = 0; ep < 3; ++ep) {
                double q0 = w.uni(-0.2, 0.2);
                EpRes a = runEpisode(net, false, S, 9000 + ep, q0, 1500, 0.0);
                EpRes b = runEpisode(net, true, S, 9000 + ep, q0, 1500, 0.0);
                off |= a.viol > 0; on |= b.viol > 0;
                worstOff = std::max(worstOff, a.maxq); worstOn = std::max(worstOn, b.maxq);
            }
            badOff += off; badOn += on;
        }
        std::printf("200 random MLPs: unsafe nets  shield OFF %d/200 (worst |q| %.3f)  shield ON %d/200 (worst |q| %.4f)\n",
                    badOff, worstOff, badOn, worstOn);
    }

    // ===== 5. tracking quality of the reference policy under the shield =====
    EpRes tr = runEpisode(pd, true, S, 42, 0.0, 1500, 0.1);
    std::printf("\nPD tracking qref=0.10 m (shield ON): steady-state |error| %.4f m, interventions %d\n", tr.sserr, tr.interv);

    // ===== 6. determinism and throughput of the integer runtime =====
    EpRes d1 = runEpisode(mlp, true, S, 77, 0.1, 2000, 0.0), d2 = runEpisode(mlp, true, S, 77, 0.1, 2000, 0.0);
    std::printf("determinism: two identical runs -> %s (hash %016llx)\n", d1.hash == d2.hash ? "bit-identical" : "DIFFERENT",
                (unsigned long long)d1.hash);
    const int NB = 5000000; i64 sink = 0, q = fx(0.05), v = fx(0.2);
    auto t0 = std::chrono::steady_clock::now();
    for (int i = 0; i < NB; ++i) {
        i64 ud = sat(mlp(q, v), -S.Fmax, S.Fmax);
        sink ^= S.filter(q, v, ud);
        q += (i & 1) ? 12345 : -12340; v += (i & 2) ? 777 : -770;
    }
    double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::printf("controller+shield: %.0f ns/step (%.2f M steps/s) [%lld]\n", sec / NB * 1e9, NB / sec / 1e6, (long long)(sink & 1));
    return 0;
}
