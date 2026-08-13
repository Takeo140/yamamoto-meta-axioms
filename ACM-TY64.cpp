/*
  ACM-TY: Abstract Computation Model — Takeo Yamamoto
  Hardware-Native C++ Edition (UHA × BSCM × DIFD × GIFE)
  License: Apache 2.0
  Author: Takeo Yamamoto
*/

#include <iostream>
#include <vector>
#include <cstdint>
#include <functional>
#include <numeric>
#include <algorithm>

// 64bit基礎スカラー。オーバーフローはCPUのハードウェア仕様に従い自動ラップアラウンドする
using u64 = uint64_t;

/**************************************************************
 * 1. UltraCore HyperAlgebra (UHA) — Continuous Core
 **************************************************************/
struct UHA {
    std::vector<u64> coords;

    UHA() = default;
    explicit UHA(size_t n) : coords(n, 0) {}

    // SIMD並列化を意識したインプレース加算
    UHA add(const UHA& other) const {
        UHA res(coords.size());
        for (size_t i = 0; i < coords.size(); ++i) {
            res.coords[i] = coords[i] + other.coords[i];
        }
        return res;
    }

    UHA smul(u64 a) const {
        UHA res(coords.size());
        for (size_t i = 0; i < coords.size(); ++i) {
            res.coords[i] = a * coords[i];
        }
        return res;
    }

    // ゼロアロケーションでのノルム（内積）計算
    u64 norm() const {
        u64 acc = 0;
        for (u64 v : coords) {
            acc += (v * v);
        }
        return acc;
    }
};

/**************************************************************
 * 2. BSCM — Discrete Control Core (Bitwise Operations)
 **************************************************************/

// コラッツ的な挙動を、除算を使わず1クロックのビット演算(&, >>)で処理
inline u64 bscm_delta_fast(u64 s) {
    return (s & 1) == 0 ? (s >> 1) : ((s + 1) >> 1);
}

inline u64 bscm_control_step(u64 current_state, u64 external_input) {
    // uint64_tによる自然なラップアラウンドを利用 (mod 2^64)
    return bscm_delta_fast(current_state + external_input);
}

/**************************************************************
 * 3. DIFD — Fluid Core
 **************************************************************/
struct Flow {
    UHA vel;
    UHA press;
    u64 viscosity;
};

/**************************************************************
 * 4. GIFE — Field Engine (Optimized Memory Layout)
 **************************************************************/
struct Entity {
    u64 id;
    UHA state;
    u64 energy;
    u64 mood;
    u64 genome;
    u64 discrete;
    Flow flow;
};

struct Topology {
    // 隣接行列を1次元の連続配列としてフラットに保持（キャッシュヒット率向上）
    std::vector<u64> conn_matrix;
    u64 viscosity;
    u64 curvature;
};

struct FieldState {
    std::vector<Entity> entities;
    u64 entropy;
    Topology topology;
    Flow flow;
};

/**************************************************************
 * 5. Dynamics & Evolution Engine
 **************************************************************/
struct Engine {
    // Dynamics (関数ポインタ / std::function で外部から注入可能)
    std::function<Entity(const Entity&, u64)> updateEntity;
    std::function<Flow(const Flow&, const Topology&)> updateFlow;
    std::function<Topology(const Topology&, const std::vector<Entity>&)> updateTopology;
    std::function<u64(const FieldState&)> updateEntropy;

    // Evolution
    std::function<Entity(const Entity&)> mutate;
    std::function<Entity(const Entity&, u64)> adapt;

    // Takeo Evolution (環境適応型進化コア)
    bool use_takeo_evolution = false;
    std::function<u64(const Entity&, const FieldState&)> fitness;
    std::vector<Entity> diversity_pool;
};

/**************************************************************
 * 6. Unified Execution Step
 **************************************************************/

// 環境変化の検知
inline bool envChanged(const FieldState& prev, const FieldState& curr) {
    return prev.entropy != curr.entropy ||
           prev.topology.viscosity != curr.topology.viscosity ||
           prev.topology.curvature != curr.topology.curvature;
}

// 連続・離散の統合ステップ（1世代分）
FieldState stepClassic(const Engine& eng, const FieldState& s) {
    FieldState next_s = s;

    // 1. 個体レベルの更新 (UHA連続流体 + BSCM離散制御)
    for (auto& e : next_s.entities) {
        Entity base = eng.updateEntity(e, s.entropy);
        base.discrete = bscm_control_step(e.discrete, s.entropy);
        base.flow = eng.updateFlow(e.flow, s.topology);
        e = base;
    }

    // 2. 適応と変異
    for (auto& e : next_s.entities) {
        e = eng.adapt(e, s.entropy);
        e = eng.mutate(e);
    }

    // 3. 場全体の更新 (トポロジーとエントロピー)
    next_s.topology = eng.updateTopology(s.topology, next_s.entities);
    next_s.flow = eng.updateFlow(s.flow, next_s.topology);
    next_s.entropy = eng.updateEntropy(next_s);

    return next_s;
}

// Takeo Evolutionを含むメタステップ
FieldState step(const Engine& eng, const FieldState& s) {
    FieldState next = stepClassic(eng, s);

    // Takeo Evolution: 環境の劇的な変化時に多様性プールから最適解へ系をリセット
    if (eng.use_takeo_evolution && envChanged(s, next)) {
        if (!eng.diversity_pool.empty()) {
            Entity best = eng.diversity_pool[0];
            u64 max_fit = eng.fitness(best, next);
            
            for (size_t i = 1; i < eng.diversity_pool.size(); ++i) {
                u64 current_fit = eng.fitness(eng.diversity_pool[i], next);
                if (current_fit > max_fit) {
                    max_fit = current_fit;
                    best = eng.diversity_pool[i];
                }
            }
            // 最適エンティティで場を再構築
            next.entities.clear();
            next.entities.push_back(best);
        }
    }
    return next;
}
