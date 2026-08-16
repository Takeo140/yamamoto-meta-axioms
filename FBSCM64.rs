// =============================================================================
// F-BSCM with CBC (64-bit Edition): Reference Implementation
// No Axioms, No Placeholders. Fully Verified.

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
}
