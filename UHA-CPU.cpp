// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cstdint>
#include <array>
#include <iostream>
#include <chrono>

using U64 = std::uint64_t;

// ===============================
//  CPU popcount (C++17)
// ===============================
inline std::uint32_t popcount64(U64 x) {
    return __builtin_popcountll(x);
}

// ===============================
//  多元ベクトル
// ===============================
template<std::size_t N>
struct UVec {
    std::array<U64, N> v;

    UVec() { v.fill(0); }  // ★ゼロ初期化（重要）
    explicit UVec(const std::array<U64, N>& a) : v(a) {}
};

// ===============================
//  UOp: XOR
// ===============================
template<std::size_t N>
inline void apply(const UVec<N>& x, const std::array<U64, N>& mask, UVec<N>& y) {
    for (std::size_t i = 0; i < N; ++i)
        y.v[i] = x.v[i] ^ mask[i];
}

// ===============================
//  ノルム計算
// ===============================
template<std::size_t N>
inline std::uint32_t norm(const UVec<N>& u) {
    std::uint32_t s = 0;
    for (auto& x : u.v) s += popcount64(x);
    return s;
}

// ===============================
//  UHA CPU: ノルム最小化探索
// ===============================
template<std::size_t N>
UVec<N> minimize_norm(const UVec<N>& start, const std::array<U64, N>& mask, std::size_t steps) {
    UVec<N> best = start;
    UVec<N> cur  = start;
    UVec<N> tmp;  // ★ゼロ初期化されるので安全

    std::uint32_t best_norm = norm(best);

    for (std::size_t k = 0; k < steps; ++k) {
        apply<N>(cur, mask, tmp);
        cur = tmp;

        auto n = norm(cur);
        if (n < best_norm) {
            best_norm = n;
            best = cur;
        }
    }
    return best;
}

// ===============================
//  main
// ===============================
int main() {
    constexpr std::size_t N = 4;
    constexpr std::size_t STEPS = 100000000;

    UVec<N> x({{0xFFFFu, 0x0Fu, 0xF0u, 0xAAAAu}});
    std::array<U64, N> mask = {{0x00FFu, 0x00FFu, 0x00FFu, 0x00FFu}};

    std::cout << "norm(x) = " << norm(x) << "\n";

    auto t0 = std::chrono::high_resolution_clock::now();

    auto best = minimize_norm<N>(x, mask, STEPS);

    auto t1 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> dt = t1 - t0;

    std::cout << "elapsed [s] = " << dt.count() << "\n";
    std::cout << "best_norm   = " << norm(best) << "\n";

    return 0;
}
