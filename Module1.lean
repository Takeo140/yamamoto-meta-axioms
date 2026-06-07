-- =========================================================================
-- MODULE 1: Shannon Complexity Elimination Theory (Theoretical Layer)
-- Licensed under CC-BY-4.0 (Author: Takeo Yamamoto / 山本健夫)
-- =========================================================================

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators
open Real

namespace YamamotoTheory1

/-- アルゴリズムの実行状態（状態空間上の確率分布）。 -/
structure ComputationState (ι : Type) [Fintype ι] where
  p       : ι → ℝ
  hNonNeg : ∀ i, 0 ≤ p i
  hSum    : ∑ i, p i = 1

/-- 計算論的シャノンエントロピー H(s)：システムが内包する「複雑性・バグ・未確定な分岐」の総ビット長。 -/
noncomputable def computational_entropy {ι : Type} [Fintype ι] (s : ComputationState ι) : ℝ :=
  - ∑ i, s.p i * log (s.p i)

/-- 決定論的基底状態：すべての複雑性が排除され、確率1で仕様通り終了するバグゼロ状態。 -/
def deterministic_ground_state {ι : Type} [Fintype ι] [Nonempty ι] (target : ι) : ComputationState ι where
  p       := fun i => if i = target then 1 else 0
  hNonNeg := fun i => by split_ifs <;> linarith
  hSum    := by simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- 計算論的価値：最適化によってシステムから「引き算された複雑性」の総量。 -/
noncomputable def computational_value {ι : Type} [Fintype ι] (initial current : ComputationState ι) : ℝ :=
  computational_entropy initial - computational_entropy current

theorem deterministic_entropy_is_zero {ι : Type} [Fintype ι] [Nonempty ι] (target : ι) :
    computational_entropy (deterministic_ground_state target) = 0 := by
  unfold computational_entropy deterministic_ground_state; simp only [neg_eq_zero]
  have h_terms : ∀ i, (if i = target then (1:ℝ) else 0) * log (if i = target then 1 else 0) = 0 := by
    intro i; split_ifs with h <;> [simp [h, Real.log_one]; ring]
  apply Finset.sum_eq_zero; intro i _; exact h_terms i

lemma computational_entropy_nonneg {ι : Type} [Fintype ι] (s : ComputationState ι) : 0 ≤ computational_entropy s := by
  unfold computational_entropy; apply neg_nonneg.mpr; apply Finset.sum_nonpos; intro i _
  have hpi_le_one : s.p i ≤ 1 := by
    have h := Finset.single_le_sum (f := s.p) (fun j _ => s.hNonNeg j) (Finset.mem_univ i)
    linarith [s.hSum]
  have hlog : log (s.p i) ≤ 0 := by
    rcases (s.hNonNeg i).eq_or_gt with rfl | hpos <;> [simp [Real.log_zero]; exact Real.log_nonpos hpos.le hpi_le_one]
  exact mul_nonpos_of_nonneg_of_nonpos (s.hNonNeg i) hlog

/-- 【定理】複雑性排除の根本定理：完全な決定論的状態へ達したとき、創出価値は初期カオス量そのものに一致する。 -/
theorem maximum_value_at_ground_state {ι : Type} [Fintype ι] [Nonempty ι] (initial : ComputationState ι) (target : ι) :
    computational_value initial (deterministic_ground_state target) = computational_entropy initial := by
  unfold computational_value; rw [deterministic_entropy_is_zero]; ring

end YamamotoTheory1
