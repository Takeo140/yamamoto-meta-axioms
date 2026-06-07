-- =========================================================================
-- MODULE 2: Dynamic Theory of Algorithmic Debt and Refactoring
-- Licensed under CC-BY-4.0 (Author: Takeo Yamamoto / 山本健夫)
-- =========================================================================

import Mathlib.Data.Real.Basic

namespace YamamotoTheory2

/-- ソフトウェア資本システム
    - `B` : 有効コードストック（正常駆動する資産）
    - `δ` : 技術的負債の自然発生率（環境変化による風化速度）
    - `N` : 共通ライブラリの再利用性による相乗効果乗数 -/
structure CodebaseSystem where
  B : ℝ
  δ : ℝ
  N : ℝ
  B_pos : 0 < B
  δ_range : 0 < δ ∧ δ < 1
  N_pos : 1 < N

/-- リファクタリング投資 I を投入した際の時間経過によるコードベースの動的転移。 -/
def next_code_state (sys : CodebaseSystem) (I : ℝ) : ℝ :=
  sys.B - (sys.δ * sys.B) + (sys.N * I)

/-- 【定理】技術的負債の長期的減耗：リファクタリング投資（引き算）を怠った閉鎖システムは、確実に風化する。 -/
theorem closed_system_decay (sys : CodebaseSystem) :
    next_code_state sys 0 < sys.B := by
  dsimp [next_code_state]
  have h_decay : 0 < sys.δ * sys.B := mul_pos sys.δ_range.1 sys.B_pos
  linarith

end YamamotoTheory2
