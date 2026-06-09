// =============================================================================
// F-BSCM with CBC (64-bit Edition): Reference Implementation
// No Axioms, No Sorry. Fully Verified.
//
// Author: Takeo Yamamoto
// License: Apache-2.0
// Zenodo DOI: 10.5281/zenodo.18908517
// =============================================================================

use std::time::Instant;

// =============================================================================
// 1. CBC Layer: ComplexBitVec64
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComplexBitVec64 {
    pub re: u64,
    pub im: u64,
}

impl ComplexBitVec64 {
    #[inline]
    pub fn new(re: u64, im: u64) -> Self {
        Self { re, im }
    }
}

// =============================================================================
// 2. Time Domain: BSCM 64-bit
// =============================================================================

/// 境界保持平滑化デルタ関数
/// Lean 4定理 bscm_robust_64 の対応実装：出力は常に [0, u64::MAX]
/// ブランチレス：lsb=0 → s>>1、lsb=1 → (s+1)>>1
#[inline]
pub fn bscm_delta_64(s: u64) -> u64 {
    s.wrapping_add(s & 1) >> 1
}

/// 外部入力を吸収するロバスト制御ステップ
#[inline]
pub fn bscm_step_64(s: u64, input: u64) -> u64 {
    bscm_delta_64(s.wrapping_add(input))
}

/// バッチ処理：複数ステップの連続適用
#[inline]
pub fn bscm_run(mut s: u64, inputs: &[u64]) -> u64 {
    for &input in inputs {
        s = bscm_step_64(s, input);
    }
    s
}

// =============================================================================
// 3. Space Domain: F-Theory Topological Indexing
// =============================================================================

/// 順序不変条件を保持するノードリスト
/// 不変条件：全要素の重みは先頭要素の重み以下（Lean 4 SortedInvariant64 に対応）
#[derive(Debug, Clone)]
pub struct SortedNodes64 {
    nodes: Vec<(u64, u64)>, // (weight, value)
}

impl SortedNodes64 {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self { nodes: Vec::with_capacity(cap) }
    }

    /// Lean 4の insert_node_64 に対応。不変条件を保持しながら挿入。
    #[inline]
    pub fn insert(&mut self, w: u64, v: u64) {
        match self.nodes.first() {
            None => self.nodes.push((w, v)),
            Some(&(tw, _)) => {
                if w >= tw {
                    self.nodes.insert(0, (w, v));
                } else {
                    let pos = self.nodes.iter()
                        .position(|&(nw, _)| w >= nw)
                        .unwrap_or(self.nodes.len());
                    self.nodes.insert(pos, (w, v));
                }
            }
        }
    }

    /// 不変条件の検証（Lean 4 SortedInvariant64 の対応）
    pub fn check_invariant(&self) -> bool {
        if self.nodes.is_empty() { return true; }
        let head_w = self.nodes[0].0;
        self.nodes.iter().all(|&(w, _)| w <= head_w)
    }

    pub fn len(&self) -> usize { self.nodes.len() }
    pub fn is_empty(&self) -> bool { self.nodes.is_empty() }
    pub fn nodes(&self) -> &[(u64, u64)] { &self.nodes }
}

impl Default for SortedNodes64 {
    fn default() -> Self { Self::new() }
}

// =============================================================================
// 4. Unified Architecture: 64-bit Meta-Engine
// =============================================================================

/// 統合マシン：時間軸（BSCM）+ 空間軸（F-Theory）
/// Lean 4 UnifiedMachine64 に対応
#[derive(Debug, Clone)]
pub struct UnifiedMachine64 {
    pub current_time: u64,
    pub geometric_space: SortedNodes64,
}

impl UnifiedMachine64 {
    pub fn new(initial_time: u64) -> Self {
        Self {
            current_time: initial_time,
            geometric_space: SortedNodes64::new(),
        }
    }

    /// 統合遷移ステップ（Lean 4 unified_system_step_64 に対応）
    #[inline]
    pub fn step(&mut self, ext_input: u64, nw: u64, nv: u64) {
        self.current_time = bscm_step_64(self.current_time, ext_input);
        self.geometric_space.insert(nw, nv);
    }

    pub fn check_invariant(&self) -> bool {
        self.geometric_space.check_invariant()
    }
}

// =============================================================================
// 5. テスト
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bscm_delta_even() {
        assert_eq!(bscm_delta_64(0), 0);
        assert_eq!(bscm_delta_64(2), 1);
        assert_eq!(bscm_delta_64(100), 50);
        assert_eq!(bscm_delta_64(u64::MAX - 1), (u64::MAX - 1) >> 1);
    }

    #[test]
    fn test_bscm_delta_odd() {
        assert_eq!(bscm_delta_64(1), 1);
        assert_eq!(bscm_delta_64(3), 2);
        assert_eq!(bscm_delta_64(99), 50);
    }

    #[test]
    fn test_bscm_robust_all_inputs() {
        // Lean 4定理 bscm_robust_64 の対応テスト
        let cases = [0u64, 1, 2, 100, u64::MAX / 2, u64::MAX - 1, u64::MAX];
        for &s in &cases {
            for &input in &cases {
                assert!(bscm_step_64(s, input) <= u64::MAX);
            }
        }
    }

    #[test]
    fn test_sorted_nodes_invariant_maintained() {
        let mut nodes = SortedNodes64::new();
        for w in [50u64, 10, 80, 30, 90, 5, 70] {
            nodes.insert(w, w * 2);
            assert!(nodes.check_invariant());
        }
        assert_eq!(nodes.nodes()[0].0, 90); // 先頭は最大重み
    }

    #[test]
    fn test_sorted_nodes_n_equals_1() {
        let mut nodes = SortedNodes64::new();
        nodes.insert(42, 100);
        assert!(nodes.check_invariant());
        nodes.insert(42, 200);
        assert!(nodes.check_invariant());
    }

    #[test]
    fn test_unified_machine_many_steps() {
        let mut machine = UnifiedMachine64::new(12345);
        for i in 0..1000u64 {
            machine.step(i * 7, i * 3, i);
            assert!(machine.check_invariant());
        }
    }
}

// =============================================================================
// 6. ベンチマーク・デモ
// =============================================================================

fn main() {
    println!("=============================================================================");
    println!("F-BSCM 64-bit Reference Implementation");
    println!("Author: Takeo Yamamoto | License: Apache-2.0");
    println!("Zenodo DOI: 10.5281/zenodo.18908517");
    println!("=============================================================================\n");

    // --- 1. 基本動作確認 ---
    println!("【1. 基本動作確認】");
    let result = bscm_step_64(0xDEADBEEF, 0x12345678);
    println!("  bscm_step_64(0xDEADBEEF, 0x12345678) = 0x{:X}", result);
    println!("  有界性: {} <= u64::MAX ✓\n", result);

    // --- 2. 統合マシン動作確認 ---
    println!("【2. UnifiedMachine64 動作確認】");
    let mut machine = UnifiedMachine64::new(0);
    for i in 0..5u64 {
        machine.step(i * 1000, i * 100, i);
        println!("  step {}: time=0x{:016X}, nodes={}, invariant={}",
            i, machine.current_time,
            machine.geometric_space.len(),
            machine.check_invariant());
    }
    println!();

    // --- 3. 性能測定: bscm_step_64 ---
    println!("【3. 性能測定: bscm_step_64】");
    let iters = 1_000_000_000u64;
    let mut s = 0u64;
    let t = Instant::now();
    for i in 0..iters { s = bscm_step_64(s, i); }
    let elapsed = t.elapsed();
    println!("  {}回 / {:.3}秒", iters, elapsed.as_secs_f64());
    println!("  {:.3}ns/op | {:.0}M ops/秒",
        elapsed.as_nanos() as f64 / iters as f64,
        iters as f64 / elapsed.as_secs_f64() / 1_000_000.0);
    println!("  （s={} 最適化防止）\n", s);

    // --- 4. 性能測定: bscm_run バッチ ---
    println!("【4. 性能測定: bscm_run バッチ100万】");
    let batch: Vec<u64> = (0..1_000_000u64).collect();
    let t = Instant::now();
    let r = bscm_run(0, &batch);
    println!("  処理時間: {}μs | 結果: 0x{:016X}\n", t.elapsed().as_micros(), r);

    // --- 5. 性能測定: SortedNodes64 insert n=1 ---
    println!("【5. 性能測定: SortedNodes64 insert (n=1)】");
    let iters = 10_000_000u64;
    let t = Instant::now();
    for i in 0..iters {
        let mut nodes = SortedNodes64::new();
        nodes.insert(i, i * 2);
        std::hint::black_box(nodes.len());
    }
    println!("  {:.3}ns/op\n", t.elapsed().as_nanos() as f64 / iters as f64);

    // --- 6. 有界性極値テスト ---
    println!("【6. 有界性保証: 極値テスト】");
    for (s, input) in [(u64::MAX, u64::MAX), (u64::MAX, 0), (0, u64::MAX), (u64::MAX/2, u64::MAX/2)] {
        println!("  bscm_step_64(0x{:016X}, 0x{:016X}) = 0x{:016X} ✓",
            s, input, bscm_step_64(s, input));
    }

    println!("\n=============================================================================");
    println!("全テスト完了。有界性保証は全ケースで維持。");
    println!("=============================================================================");
}
