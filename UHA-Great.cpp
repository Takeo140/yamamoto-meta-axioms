// License: Apache 2.0
// Author: Takeo Yamamoto
// Formally verified specification mapped from Lean 4 (UltraCore Engine)

#ifndef ULTRACORE_UHA_HPP
#define ULTRACORE_UHA_HPP

#include <cstdint>
#include <array>
#include <functional>
#include <numeric>
#include <concepts>
#include <iostream>

namespace UltraCore {

using U64 = uint64_t;

/**
 * @brief n次元 離散代数キャリア (UltraCore HyperAlgebra)
 * ZMod(2^64) 上のベクトル空間。CPUレジスタの自然な溢れを利用するためModulo命令(%)ゼロ。
 */
template <std::size_t N>
struct alignas(64) UHA {
    std::array<U64, N> coords{};

    // 演算子オーバーロード (Branchless, Auto-Vectorizable)
    constexpr UHA operator+(const UHA& rhs) const noexcept {
        UHA res;
        #pragma unroll
        for (std::size_t i = 0; i < N; ++i) {
            res.coords[i] = this->coords[i] + rhs.coords[i];
        }
        return res;
    }

    constexpr UHA operator-(const UHA& rhs) const noexcept {
        UHA res;
        #pragma unroll
        for (std::size_t i = 0; i < N; ++i) {
            res.coords[i] = this->coords[i] - rhs.coords[i];
        }
        return res;
    }

    constexpr UHA operator-() const noexcept {
        UHA res;
        #pragma unroll
        for (std::size_t i = 0; i < N; ++i) {
            res.coords[i] = -this->coords[i];
        }
        return res;
    }

    constexpr UHA operator*(U64 scalar) const noexcept {
        UHA res;
        #pragma unroll
        for (std::size_t i = 0; i < N; ++i) {
            res.coords[i] = this->coords[i] * scalar;
        }
        return res;
    }

    constexpr bool operator==(const UHA& rhs) const noexcept = default;
};

/**
 * @brief 離散内積 (Inner Product)
 * Lean 4: def inner (x y : UHA n) : U64 := ∑ i, (x.coords i) * (y.coords i)
 */
template <std::size_t N>
[[nodiscard]] constexpr U64 inner(const UHA<N>& x, const UHA<N>& y) noexcept {
    U64 acc = 0;
    #pragma unroll
    for (std::size_t i = 0; i < N; ++i) {
        acc += x.coords[i] * y.coords[i];
    }
    return acc;
}

/**
 * @brief ノルム (Self-Inner Product) / エネルギー保存の測定値
 * Lean 4: def norm (x : UHA n) : U64 := inner x x
 */
template <std::size_t N>
[[nodiscard]] constexpr U64 norm(const UHA<N>& x) noexcept {
    return inner(x, x);
}

/**
 * @brief 構造定数 (c_jk^i) による多元代数の積 (Clifford代数, 複素数, 四元数等)
 * Lean 4: def mulWith (c : Fin n → Fin n → UHA n) (x y : UHA n) : UHA n
 */
template <std::size_t N, typename StructConstFunc>
requires std::is_invocable_r_v<UHA<N>, StructConstFunc, std::size_t, std::size_t>
[[nodiscard]] constexpr UHA<N> mulWith(StructConstFunc&& c, const UHA<N>& x, const UHA<N>& y) noexcept {
    UHA<N> res{};
    for (std::size_t j = 0; j < N; ++j) {
        for (std::size_t k = 0; k < N; ++k) {
            const U64 coeff = x.coords[j] * y.coords[k];
            const UHA<N> c_jk = c(j, k);
            #pragma unroll
            for (std::size_t i = 0; i < N; ++i) {
                res.coords[i] += coeff * c_jk.coords[i];
            }
        }
    }
    return res;
}

/**
 * @brief 2次元 離散複素数 (ZMod 2^64 上のガウス整数) 構造定数
 */
inline constexpr UHA<2> complex_c(std::size_t j, std::size_t k) noexcept {
    if (j == 0 && k == 0) return UHA<2>{{1, 0}}; //  1 * 1 =  1
    if (j == 0 && k == 1) return UHA<2>{{0, 1}}; //  1 * i =  i
    if (j == 1 && k == 0) return UHA<2>{{0, 1}}; //  i * 1 =  i
    if (j == 1 && k == 1) return UHA<2>{{static_cast<U64>(-1), 0}}; // i * i = -1 (0xFFFFFFFFFFFFFFFF)
    return UHA<2>{{0, 0}};
}

/**
 * @brief 離散複素数の乗算
 */
[[nodiscard]] inline constexpr UHA<2> complexMul(const UHA<2>& x, const UHA<2>& y) noexcept {
    return mulWith<2>(complex_c, x, y);
}

} // namespace UltraCore

#endif // ULTRACORE_UHA_HPP
