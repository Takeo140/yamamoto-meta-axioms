License Apache 2.0  Takeo Yamamoto

#include <cstdint>
#include <array>
#include <bit>
#include <iostream>

// ===============================
//  U64: 有限環（基本スカラー）
// ===============================
using U64 = std::uint64_t;

inline U64 uadd(U64 a, U64 b) { return a + b; }
inline U64 usub(U64 a, U64 b) { return a - b; }
inline U64 umul(U64 a, U64 b) { return a * b; }
inline U64 uxor(U64 a, U64 b) { return a ^ b; }

// ===============================
//  多元ベクトル UVec<N>
// ===============================
template<std::size_t N>
struct UVec {
    std::array<U64, N> v;

    UVec() = default;
    explicit UVec(const std::array<U64, N>& a) : v(a) {}

    U64& operator[](std::size_t i) { return v[i]; }
    const U64& operator[](std::size_t i) const { return v[i]; }
};

// ===============================
//  ノルム（popcount 和）
// ===============================
inline std::uint32_t norm(U64 x) {
    return std::popcount(x);
}

template<std::size_t N>
std::uint32_t norm(const UVec<N>& u) {
    std::uint32_t s = 0;
    for (auto& x : u.v) s += norm(x);
    return s;
}

// ===============================
//  UOp: ノルム保存作用素
// ===============================
template<std::size_t N>
struct UOp {
    std::array<U64, N> mask;

    explicit UOp(const std::array<U64, N>& m) : mask(m) {}

    UVec<N> apply(const UVec<N>& x) const {
        UVec<N> y;
        for (std::size_t i = 0; i < N; ++i) {
            y.v[i] = x.v[i] ^ mask[i];  // popcount ノルムを保存する例
        }
        return y;
    }
};

// ===============================
//  UHA 計算：ノルム最小化探索
// ===============================
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

// ===============================
//  main: 動作確認
// ===============================
int main() {
    constexpr std::size_t N = 4;

    UVec<N> x({{0xFFFFu, 0x0Fu, 0xF0u, 0xAAAAu}});
    std::array<U64, N> mask = {{0x00FFu, 0x00FFu, 0x00FFu, 0x00FFu}};
    UOp<N> op(mask);

    std::cout << "norm(x) = " << norm(x) << "\n";

    auto y = op.apply(x);
    std::cout << "norm(y) = " << norm(y) << "\n";

    auto best = minimize_norm(x, op, 1000);
    std::cout << "best norm = " << norm(best) << "\n";

    return 0;
}
