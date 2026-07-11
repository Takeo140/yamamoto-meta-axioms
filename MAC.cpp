// Meta-Axiom Computation (MAC)
// (c) Takeo Yamamoto  Apache 2.0
// Minimal C++ core

#pragma once
#include <vector>
#include <functional>
#include <optional>
#include <numeric>

// Program: α → β
template <typename A, typename B>
struct Program {
    std::function<B(const A&)> run;
};

// CostDensity: α × β → ℝ
template <typename A, typename B>
using CostDensity = std::function<double(const A&, const B&)>;

// 離散作用：Σ L(x, f(x))
template <typename A, typename B>
double action(const CostDensity<A,B>& L,
              const Program<A,B>& p,
              const std::vector<A>& xs) {
    double acc = 0.0;
    for (const auto& x : xs) {
        acc += L(x, p.run(x));
    }
    return acc;
}

// Spec: α × β → Prop
template <typename A, typename B>
using Spec = std::function<bool(const A&, const B&)>;

// 整合性：∀x, φ(x, f(x))
template <typename A, typename B>
bool consistent(const Spec<A,B>& phi,
                const Program<A,B>& p,
                const std::vector<A>& xs) {
    for (const auto& x : xs) {
        if (!phi(x, p.run(x))) return false;
    }
    return true;
}

// 多層状態：インデックス i ごとの状態
template <typename Index, typename State>
struct LayeredState {
    std::vector<Index> indices;
    std::vector<State> states;
};

// レイヤーごとの部分プログラム
template <typename Index, typename A, typename B>
struct LayerProgram {
    std::function<B(const Index&, const A&)> runLayer;
};

// 全体プログラムへの束ね
template <typename Index, typename A, typename B>
LayeredState<Index,B> toProgram(const LayerProgram<Index,A,B>& P,
                                const LayeredState<Index,A>& s) {
    LayeredState<Index,B> out;
    out.indices = s.indices;
    out.states.reserve(s.states.size());
    for (std::size_t i = 0; i < s.states.size(); ++i) {
        out.states.push_back(P.runLayer(s.indices[i], s.states[i]));
    }
    return out;
}

// DualState：物理 → 数学
template <typename Phys, typename Math>
struct DualState {
    std::function<Math(const Phys&)> toMath;
};

// 物理プログラムと数学プログラムの双対的一致条件
template <typename APhys, typename AMath, typename BPhys, typename BMath>
bool dualConsistent(const DualState<APhys,AMath>& Phi,
                    const DualState<BPhys,BMath>& Psi,
                    const Program<APhys,BPhys>& p_phys,
                    const Program<AMath,BMath>& p_math,
                    const std::vector<APhys>& xs) {
    for (const auto& x : xs) {
        auto phys_out = p_phys.run(x);
        auto math_out = p_math.run(Phi.toMath(x));
        if (Psi.toMath(phys_out) != math_out) return false;
    }
    return true;
}

// 極値原理：候補集合上で作用を極小化するプログラム
template <typename A, typename B>
std::optional<Program<A,B>> optimalProgram(
    const CostDensity<A,B>& L,
    const std::vector<A>& xs,
    const std::vector<Program<A,B>>& candidates) {

    std::optional<Program<A,B>> best;
    double bestCost = 0.0;

    for (const auto& p : candidates) {
        double cost = action(L, p, xs);
        if (!best || cost < bestCost) {
            best = p;
            bestCost = cost;
        }
    }
    return best;
}
