// MAC64 - Meta-Axiom Computation (64bit Edition)
// (c) Takeo Yamamoto
// Apache 2.0 License

#pragma once
#include <cstdint>
#include <vector>
#include <functional>
#include <optional>

// 64bit Program: uint64 → uint64
struct MAC64 {
    std::function<uint64_t(uint64_t)> run;
};

// 64bit CostDensity: (uint64, uint64) → double
using Cost64 = std::function<double(uint64_t, uint64_t)>;

// 離散作用：Σ L(x, f(x))
inline double action64(const Cost64& L,
                       const MAC64& p,
                       const std::vector<uint64_t>& xs) {
    double acc = 0.0;
    for (auto x : xs) {
        acc += L(x, p.run(x));
    }
    return acc;
}

// 仕様：uint64 × uint64 → bool
using Spec64 = std::function<bool(uint64_t, uint64_t)>;

// 整合性：∀x, φ(x, f(x))
inline bool consistent64(const Spec64& phi,
                         const MAC64& p,
                         const std::vector<uint64_t>& xs) {
    for (auto x : xs) {
        if (!phi(x, p.run(x))) return false;
    }
    return true;
}

// 多層状態：i ごとの 64bit 状態
template <typename Index>
struct LayeredState64 {
    std::vector<Index> indices;
    std::vector<uint64_t> states;
};

// レイヤーごとの部分プログラム
template <typename Index>
struct LayerProgram64 {
    std::function<uint64_t(const Index&, uint64_t)> runLayer;
};

// 全体プログラムへの束ね
template <typename Index>
LayeredState64<Index> toProgram64(const LayerProgram64<Index>& P,
                                  const LayeredState64<Index>& s) {
    LayeredState64<Index> out;
    out.indices = s.indices;
    out.states.reserve(s.states.size());
    for (size_t i = 0; i < s.states.size(); ++i) {
        out.states.push_back(P.runLayer(s.indices[i], s.states[i]));
    }
    return out;
}

// DualState：物理 → 数学（どちらも 64bit）
struct Dual64 {
    std::function<uint64_t(uint64_t)> toMath;
};

// 双対的一致条件
inline bool dualConsistent64(const Dual64& Phi,
                             const Dual64& Psi,
                             const MAC64& p_phys,
                             const MAC64& p_math,
                             const std::vector<uint64_t>& xs) {
    for (auto x : xs) {
        uint64_t phys_out = p_phys.run(x);
        uint64_t math_out = p_math.run(Phi.toMath(x));
        if (Psi.toMath(phys_out) != math_out) return false;
    }
    return true;
}

// 極値原理：作用を最小化する 64bit プログラム
inline std::optional<MAC64> optimalProgram64(
    const Cost64& L,
    const std::vector<uint64_t>& xs,
    const std::vector<MAC64>& candidates) {

    std::optional<MAC64> best;
    double bestCost = 0.0;

    for (const auto& p : candidates) {
        double cost = action64(L, p, xs);
        if (!best || cost < bestCost) {
            best = p;
            bestCost = cost;
        }
    }
    return best;
}
