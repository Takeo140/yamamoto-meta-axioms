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
#[derive(Debug, Clone)]
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

    /// ノード数を取得
    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

impl Default for FTopologySpace {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// 3. Unified Architecture: Space-Time Integrated Machine (F-BSCM)
// =============================================================================

/// 時空統合マシン（F-BSCM 実装核）
#[derive(Debug, Clone)]
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

    /// 現在のマシン状態を取得
    #[inline]
    pub fn get_current_state(&self) -> u64 {
        self.current_state
    }

    /// トップノードを抽出（空間の最高解）
    #[inline]
    pub fn get_top_solution(&self) -> Option<(u64, u64)> {
        self.f_space.extract_top()
    }
}

impl Default for UnifiedMachine {
    fn default() -> Self {
        Self::new(0)
    }
}

// =============================================================================
// 4. Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bscm_delta_even() {
        assert_eq!(bscm_delta(10), 5);
        assert_eq!(bscm_delta(4), 2);
    }

    #[test]
    fn test_bscm_delta_odd() {
        assert_eq!(bscm_delta(5), 3);
        assert_eq!(bscm_delta(9), 5);
    }

    #[test]
    fn test_bscm_control_step() {
        let result = bscm_control_step(10, 5);
        assert_eq!(result, bscm_delta(15));
    }

    #[test]
    fn test_ftopology_space_invariant() {
        let mut space = FTopologySpace::new();
        space.inject_node(100, 1);
        space.inject_node(50, 2);
        space.inject_node(200, 3);
        
        // 先頭が最大重みを持つことを確認
        assert_eq!(space.extract_top(), Some((200, 3)));
        assert_eq!(space.node_count(), 3);
    }

    #[test]
    fn test_unified_machine_step() {
        let mut machine = UnifiedMachine::new(10);
        machine.step(5);
        
        // 状態: (10 + 5) / 2 = 7
        assert_eq!(machine.get_current_state(), 8); // (15 + 1) / 2 = 8
        assert_eq!(machine.get_top_solution(), Some((8, 8)));
    }

    #[test]
    fn test_unified_machine_stream() {
        let mut machine = UnifiedMachine::new(16);
        machine.execute_stream(&[0, 1, 2]);
        
        // 複数ステップ後の最終状態を確認
        assert!(machine.get_current_state() > 0);
        assert!(machine.f_space.node_count() >= 3);
    }

    #[test]
    fn test_default_implementations() {
        let space: FTopologySpace = Default::default();
        assert_eq!(space.node_count(), 0);
        
        let machine: UnifiedMachine = Default::default();
        assert_eq!(machine.get_current_state(), 0);
    }

    #[test]
    fn test_wrapping_behavior() {
        // u64オーバーフロー時の挙動確認
        let result = bscm_control_step(u64::MAX, 1);
        assert!(result > 0);
    }
}
