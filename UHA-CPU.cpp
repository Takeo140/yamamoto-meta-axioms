// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cstdint>
#include <array>
#include <iostream>
#include <chrono>

using U64  = std::uint64_t;
using U32  = std::uint32_t;
using Size = std::size_t;

// ===============================
//  CPU popcount (C++17)
// ===============================
inline U32 popcount64(U64 x) {
    return static_cast<U32>(__builtin_popcountll(x));
}

// ===============================
//  多元ベクトル UHA n
// ===============================
template<Size N>
struct UVec {
    std::array<U64, N> v;

    UVec() { v.fill(0); }
    explicit UVec(const std::array<U64, N>& a) : v(a) {}
};

// ===============================
//  UOp: XOR（離散ユニタリ）
// ===============================
template<Size N>
inline void apply(const UVec<N>& x,
                  const std::array<U64, N>& mask,
                  UVec<N>& y)
{
    for (Size i = 0; i < N; ++i)
        y.v[i] = x.v[i] ^ mask[i];
}

// ===============================
//  ノルム：Σ popcount(x_i)
// ===============================
template<Size N>
inline U32 norm(const UVec<N>& u) {
    U32 s = 0;
    for (const auto& x : u.v)
        s += popcount64(x);
    return s;
}

// ===============================
//  UHA CPU: ノルム最小化探索（Lean step 同型）
// ===============================
template<Size N>
UVec<N> minimize_norm(const UVec<N>& start,
                      const std::array<U64, N>& mask,
                      Size steps)
{
    UVec<N> best = start;
    UVec<N> cur  = start;
    UVec<N> tmp;   // ゼロ初期化済み

    U32 best_norm = norm(best);

    for (Size k = 0; k < steps; ++k) {
        apply<N>(cur, mask, tmp);
        cur = tmp;

        U32 n = norm(cur);
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
    constexpr Size N     = 4;
    constexpr Size STEPS = 100000000;

    UVec<N> x({{0xFFFFull, 0x0Full, 0xF0ull, 0xAAAAull}});
    std::array<U64, N> mask = {{0x00FFull, 0x00FFull, 0x00FFull, 0x00FFull}};

    std::cout << "norm(x) = " << norm(x) << "\n";

    auto t0 = std::chrono::high_resolution_clock::now();
    auto best = minimize_norm<N>(x, mask, STEPS);
    auto t1 = std::chrono::high_resolution_clock::now();

    std::chrono::duration<double> dt = t1 - t0;

    std::cout << "elapsed [s] = " << dt.count() << "\n";
    std::cout << "best_norm   = " << norm(best) << "\n";

    return 0;
}
