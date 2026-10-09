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
