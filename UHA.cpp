// License: Apache 2.0
// Author: Takeo Yamamoto

#include <immintrin.h>
#include <cstdint>
#include <array>
#include <iostream>
#include <chrono>

using U64  = std::uint64_t;
using U32  = std::uint32_t;
using Size = std::size_t;

// ===============================
// popcount (AVX2 ではスカラだが高速)
// ===============================
inline U32 popcount64(U64 x) {
    return static_cast<U32>(__builtin_popcountll(x));
}

// ===============================
// UHA n : Fin n → U64
// ===============================
template<Size N>
struct UVec {
    std::array<U64, N> v;
    UVec() { v.fill(0); }
    explicit UVec(const std::array<U64, N>& a) : v(a) {}
};

// ===============================
// SIMD XOR (UOp)
// ===============================
inline void xor_avx2(const U64* x, const U64* mask, U64* y) {
    __m256i vx   = _mm256_loadu_si256((__m256i*)x);
    __m256i vmask= _mm256_loadu_si256((__m256i*)mask);
    __m256i vy   = _mm256_xor_si256(vx, vmask);
    _mm256_storeu_si256((__m256i*)y, vy);
}

// ===============================
// SIMD norm (popcount × 4)
// ===============================
inline U32 norm_avx2(const U64* v) {
    // AVX2 には popcount SIMD が無いのでスカラで集計
    // それでも XOR が SIMD 化されているので高速
    U32 s = 0;
    for (int i = 0; i < 4; ++i)
        s += popcount64(v[i]);
    return s;
}

// ===============================
// UOp.apply (SIMD)
// ===============================
template<Size N>
inline void apply_simd(const UVec<N>& x,
                       const std::array<U64, N>& mask,
                       UVec<N>& y)
{
    xor_avx2(x.v.data(), mask.data(), y.v.data());
}

// ===============================
// norm (SIMD)
// ===============================
template<Size N>
inline U32 norm_simd(const UVec<N>& u) {
    return norm_avx2(u.v.data());
}

// ===============================
// UHA CPU: ノルム最小化探索（SIMD版）
// ===============================
template<Size N>
UVec<N> minimize_norm_simd(const UVec<N>& start,
                           const std::array<U64, N>& mask,
                           Size steps)
{
    UVec<N> best = start;
    UVec<N> cur  = start;
    UVec<N> tmp;

    U32 best_norm = norm_simd(cur);

    for (Size k = 0; k < steps; ++k) {
        apply_simd<N>(cur, mask, tmp);
        cur = tmp;

        U32 n = norm_simd(cur);
        if (n < best_norm) {
            best_norm = n;
            best = cur;
        }
    }
    return best;
}

// ===============================
// main
// ===============================
int main() {
    constexpr Size N = 4;
    constexpr Size STEPS = 100000000;

    UVec<N> x({{0xFFFFull, 0x0Full, 0xF0ull, 0xAAAAull}});
    std::array<U64, N> mask = {{0x00FFull, 0x00FFull, 0x00FFull, 0x00FFull}};

    std::cout << "norm(x) = " << norm_simd(x) << "\n";

    auto t0 = std::chrono::high_resolution_clock::now();
    auto best = minimize_norm_simd<N>(x, mask, STEPS);
    auto t1 = std::chrono::high_resolution_clock::now();

    std::chrono::duration<double> dt = t1 - t0;

    std::cout << "elapsed [s] = " << dt.count() << "\n";
    std::cout << "best_norm   = " << norm_simd(best) << "\n";

    return 0;
}
