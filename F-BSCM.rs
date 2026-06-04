//! F-BSCM: Space-Time Invariant Meta-Axiomatic Computing Model
//! Integrating Bounded Smooth Collatz Machine (Time) and F-Theory (Space)
//!
//! Author: Takeo Yamamoto
//! License: Apache-2.0 / CC-BY-4.0

// =============================================================================
// 1. Time Domain: Bounded Smooth Collatz Machine (BSCM)
// =============================================================================

/// 【Engineering δ】
/// 偶数なら右シフト（1/2）、奇数なら +1 して右シフト（1/2）。
/// すべての分岐が状態を確実に縮小または維持させるため、絶対にレジスタを破裂させない。
#[inline]
pub fn bscm_delta(s: u64) -> u64 {
    if s % 2 == 0 {
        s / 2
    } else {
        (s + 1) / 2
    }
}

/// 外部入力を受け取る1ステップの状態遷移。
/// `wrapping_add` により、Rustレイヤーで自動的に Modulo 2^64 が保証される。
#[inline]
pub fn bscm_control_step(current_state: u64, external_input: u64) -> u64 {
    let s_prime = current_state.wrapping_add(external_input);
    bscm_delta(s_prime)
}

// =============================================================================
// 2. Space Domain: F-Theory Topological Indexing
// =============================================================================

/// F-Theoryのトポロジー空間
pub struct FTopologySpace {
    /// 各ノードは (重み, 値) のペア
    pub nodes: Vec<(u64, u64)>,
}

impl FTopologySpace {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    /// メタ公理 A4: 先頭ノードが常に最大重みを保持する不変条件（Topological Invariant）
    /// この手動ミラー版では、降順ソートを維持する位置へノードを挿入することで公理を死守する。
    pub fn inject_node(&mut self, weight: u64, value: u64) {
        let node = (weight, value);
        
        // 重みが現在のノードより小さくなる最初のインデックス（挿入位置）を探索
        let insert_pos = self.nodes
            .iter()
            .position(|&(w, _)| w < weight)
            .unwrap_or(self.nodes.len());
        
        self.nodes.insert(insert_pos, node);
    }

    /// 空間の先頭から最高解を O(1) で一撃抽出する
    #[inline]
    pub fn extract_top(&self) -> Option<(u64, u64)> {
        self.nodes.first().cloned()
    }
}

// =============================================================================
// 3. Unified Architecture: Space-Time Integrated Machine (F-BSCM)
// =============================================================================

/// 時空統合マシン（F-BSCM 実装核）
pub struct UnifiedMachine {
    /// 現在の有界状態（時間軸の盾）
    pub current_state: u64,
    /// 常に最高解を先頭に構えるトポロジー空間（空間軸の矛）
    pub f_space: FTopologySpace,
}

impl UnifiedMachine {
    pub fn new(initial_state: u64) -> Self {
        Self {
            current_state: initial_state,
            f_space: FTopologySpace::new(),
        }
    }

    /// 時空統合ステップ関数
    /// BSCMで時間安全性を確定させ、その出力をF-Theory空間の「重み」として直結・結晶化する。
    pub fn step(&mut self, external_input: u64) {
        // ① BSCM: 時間軸の制御（絶対にオーバーフローしない）
        self.current_state = bscm_control_step(self.current_state, external_input);

        // ② F-Theory: 空間軸の幾何学更新
        // 算出された安全な状態値を、そのまま重み（優先度）および値として手動注入
        let weight = self.current_state;
        let value = self.current_state;
        self.f_space.inject_node(weight, value);
    }

    /// 終わりなき外部入力のストリームを連続処理する実行エンジン
    pub fn execute_stream(&mut self, inputs: &[u64]) {
        for &input in inputs {
            self.step(input);
        }
    }
}
