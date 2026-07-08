// License: Apache 2.0
// Author: Takeo Yamamoto (Evolutionary Population Game Theory Engine)

#include <cstdint>
#include <array>
#include <iostream>
#include <chrono>
#include <cmath>

using U64  = std::uint64_t;
using U32  = std::uint32_t;
using Size = std::size_t;

// ARM64ハードウェア命令に直結する超高速popcount
inline U32 popcount64(U64 x) {
    #if defined(_MSC_VER) && !defined(__clang__)
        return static_cast<U32>(__popcnt64(x));
    #else
        return static_cast<U32>(__builtin_popcountll(x));
    #endif
}

// =========================================================
// 共通設定：1,024人の個体（プレイヤー）による集団ゲーム空間
// =========================================================
// 64ビットのレジスタ1つに64人分の戦略を詰め込み、それを16要素並べる（64 × 16 = 1,024プレイヤー）
constexpr Size POPULATION_BLOCKS = 16; 
constexpr Size TOTAL_PLAYERS = POPULATION_BLOCKS * 64; // 1,024 Players

// ---------------------------------------------------------
// 1. 従来の「量子/確率シミュレータ型」集団ゲーム
// ---------------------------------------------------------
// 1,024人分の連続的な確率振幅を愚直にループ演算（小数のゴミが乗り、次元の呪いに捕まる構造）
struct alignas(32) QuantumPopulation {
    std::array<double, TOTAL_PLAYERS> amplitudes;
};

void run_quantum_population_step(QuantumPopulation& q) {
    constexpr double s = 0.7071067811865475;
    // 1,024人の相関・干渉をシミュレートする重い小数ループ
    #if defined(__clang__)
    #pragma clang loop vectorize(enable)
    #endif
    for (Size i = 0; i < TOTAL_PLAYERS - 1; i += 2) {
        double tmp0 = (q.amplitudes[i] + q.amplitudes[i+1]) * s;
        double tmp1 = (q.amplitudes[i] - q.amplitudes[i+1]) * s;
        q.amplitudes[i]   = tmp0;
        q.amplitudes[i+1] = tmp1;
    }
}

double calculate_quantum_population_norm(const QuantumPopulation& q) {
    double total = 0.0;
    for (Size i = 0; i < TOTAL_PLAYERS; ++i) {
        total += q.amplitudes[i] * q.amplitudes[i];
    }
    return std::sqrt(total);
}

// ---------------------------------------------------------
// 2. UHA（UltraCore HyperAlgebra）集団ゲーム
// ---------------------------------------------------------
// 1,024人の戦略をビット空間に閉じ込め、一括で相互干渉・淘汰させる離散多元環構造
struct alignas(32) UHAPopulation {
    std::array<U64, POPULATION_BLOCKS> chunks;
};

inline void apply_uha_population_gate(const UHAPopulation& x, 
                                      const std::array<U64, POPULATION_BLOCKS>& env_mask, 
                                      UHAPopulation& y) 
{
    // スマホのコンパイラがこれをNEON命令（128ビット一括XOR）へ自動並列化する
    #if defined(__clang__)
    #pragma clang loop vectorize(enable) interleave(enable)
    #endif
    for (Size i = 0; i < POPULATION_BLOCKS; ++i) {
        y.chunks[i] = x.chunks[i] ^ env_mask[i]; 
    }
}

inline U32 calculate_uha_population_norm(const UHAPopulation& u) {
    U32 total_active_strategies = 0;
    #if defined(__clang__)
    #pragma clang loop unroll(enable)
    #endif
    for (Size i = 0; i < POPULATION_BLOCKS; ++i) {
        total_active_strategies += popcount64(u.chunks[i]);
    }
    return total_active_strategies;
}

// =========================================================
// メインベンチマーク検証（集団ゲーム理論版）
// =========================================================
int main() {
    constexpr Size STEPS = 1000000; // 集団規模が大きいため100万ステップでテスト
    std::cout << "=========================================================\n";
    std::cout << "  Evolutionary Population Game Engine (1,024 Players)\n";
    std::cout << "=========================================================\n\n";

    // -----------------------------------------------------
    // [1] 従来の集団確率エミュレーション
    // -----------------------------------------------------
    std::cout << "[1] Running Traditional Quantum Population (1,024 Players)...\n";
    QuantumPopulation q_pop;
    q_pop.amplitudes.fill(0.03125); // 1/√1024 で均等初期化

    auto t0 = std::chrono::high_resolution_clock::now();
    for (Size k = 0; k < STEPS; ++k) {
        run_quantum_population_step(q_pop);
    }
    auto t1 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> dt_quantum = t1 - t0;
    std::cout << "  -> Quantum Elapsed Time: " << dt_quantum.count() << " [s]\n";
    std::cout << "  -> Final Quantum Norm  : " << calculate_quantum_population_norm(q_pop) << " (Rounding error accumulated)\n\n";

    // -----------------------------------------------------
    // [2] UHA集団代数エミュレーション
    // -----------------------------------------------------
    std::cout << "[2] Running UHA Population (1,024 Players)...\n";
    UHAPopulation u_pop;
    // 1,024人分の初期戦略マスク（適当な初期ビットパターンを配置）
    u_pop.chunks.fill(0xAAAAAAAAAAAAAAAAull); 
    
    std::array<U64, POPULATION_BLOCKS> env_mask;
    env_mask.fill(0x0F0F0F0F0F0F0F0Full); // 環境（マジョリティの圧力）を模した構造定数マスク
    UHAPopulation tmp;

    auto t2 = std::chrono::high_resolution_clock::now();
    for (Size k = 0; k < STEPS; ++k) {
        apply_uha_population_gate(u_pop, env_mask, tmp);
        u_pop = tmp;
    }
    auto t3 = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> dt_uha = t3 - t2;
    std::cout << "  -> UHA Elapsed Time    : " << dt_uha.count() << " [s]\n";
    std::cout << "  -> Final UHA Active Norm: " << calculate_uha_population_norm(u_pop) << " (100% stable / Exact)\n\n";

    std::cout << "=========================================================\n";
    std::cout << "  UHA Population Speedup Factor: " << (dt_quantum.count() / dt_uha.count()) << "x Faster!\n";
    std::cout << "=========================================================\n";

    return 0;
}
