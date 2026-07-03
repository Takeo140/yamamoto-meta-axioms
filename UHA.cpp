// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cstdint>
#include <array>
#include <iostream>
#include <chrono>

using U64 = std::uint64_t;

// C++17 popcount
inline std::uint32_t popcount64(U64 x) {
    return __builtin_popcountll(x);
}

template<std::size_t N>
struct UVec {
    std::array<U64, N> v;

    UVec() { v.fill(0); }
    explicit UVec(const std::array<U64, N>& a) : v(a) {}
};

// ノルム（popcount）
template<std::size_t N>
std::uint32_t norm(const UVec<N>& u) {
    std::uint32_t s = 0;
    for (const auto& x : u.v)
        s += popcount64(x);
    return s;
}

/*------------------------------------------------------------
  UltraCore HyperAlgebra の構造定数テンソル
  c[j][k] は UVec<N>（Lean の c j k : UHA n に対応）
------------------------------------------------------------*/
template<std::size_t N>
using CTensor = std::array<std::array<UVec<N>, N>, N>;

/*------------------------------------------------------------
  UHA の乗法： (x * y)_i = Σ_j Σ_k x_j y_k c[j][k].v[i]
------------------------------------------------------------*/
template<std::size_t N>
UVec<N> mul(const UVec<N>& x, const UVec<N>& y, const CTensor<N>& c) {
    UVec<N> out;

    for (std::size_t i = 0; i < N; ++i) {
        U64 acc = 0;

        for (std::size_t j = 0; j < N; ++j)
            for (std::size_t k = 0; k < N; ++k)
                acc ^= (x.v[j] & y.v[k] & c[j][k].v[i]);

        out.v[i] = acc;
    }
    return out;
}

/*------------------------------------------------------------
  離散ユニタリ作用素（XOR 型）
------------------------------------------------------------*/
template<std::size_t N>
struct UOp {
    std::array<U64, N> mask;

    explicit UOp(const std::array<U64, N>& m) : mask(m) {}

    UVec<N> apply(const UVec<N>& x) const {
        UVec<N> y;
        for (std::size_t i = 0; i < N; ++i)
            y.v[i] = x.v[i] ^ mask[i];
        return y;
    }
};

/*------------------------------------------------------------
  norm 最小化（探索）
------------------------------------------------------------*/
template<std::size_t N>
UVec<N> minimize_norm(const UVec<N>& start, const UOp<N>& op, std::size_t steps) {
    UVec<N> best = start;
    std::uint32_t best_norm = norm(best);

    UVec<N> cur = start;

    for (std::size_t k = 0; k < steps; ++k) {
        cur = op.apply(cur);
        auto n = norm(cur);
        if (n < best_norm) {
            best_norm = n;
            best = cur;
        }
    }
    return best;
}

int main() {
    constexpr std::size_t N = 4;
    constexpr std::size_t STEPS = 100000000;

    UVec<N> x({{0xFFFFu, 0x0Fu, 0xF0u, 0xAAAAu}});
    std::array<U64, N> mask = {{0x00FFu, 0x00FFu, 0x00FFu, 0x00FFu}};
    UOp<N> op(mask);

    std::cout << "norm(x) = " << norm(x) << "\n";

    auto y = op.apply(x);
    std::cout << "norm(y) = " << norm(y) << "\n";

    auto warm = minimize_norm(x, op, 1000);
    (void)warm;

    auto t0 = std::chrono::high_resolution_clock::now();

    UVec<N> cur = x;
    std::uint32_t best_norm = norm(cur);

    for (std::size_t k = 0; k < STEPS; ++k) {
        cur = op.apply(cur);
        auto n = norm(cur);
        if (n < best_norm) best_norm = n;
    }

    auto t1 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> dt = t1 - t0;

    double seconds = dt.count();
    double steps_per_sec = static_cast<double>(STEPS) / seconds;

    std::cout << "STEPS       = " << STEPS << "\n";
    std::cout << "elapsed [s] = " << seconds << "\n";
    std::cout << "steps/s     = " << steps_per_sec << "\n";
    std::cout << "best_norm   = " << best_norm << "\n";

    return 0;
}
