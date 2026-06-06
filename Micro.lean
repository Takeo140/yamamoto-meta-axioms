import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt

/-!
  # 2財モデルにおける消費者最適化問題 (Consumer Optimization Problem)
  
  目的: 予算制約のもとで、効用関数を最大化する消費ベクトル (x, y) の性質を定義する。
-/

open Topology Real

-- 経済的パラメーター（価格と所得）の定義
structure Economy where
  p_x : ℝ
  p_y : ℝ
  I   : ℝ
  p_x_pos : 0 < p_x
  p_y_pos : 0 < p_y
  I_pos   : 0 < I

-- 消費計画（消費ベクトル）の定義
structure ConsumptionBundle where
  x : ℝ
  y : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y

namespace ConsumerOptimization

/-- 予算集合 (Budget Set): 予算制約を満たす消費計画の集合 -/
def isBudgetFeasible (eco : Economy) (bundle : ConsumptionBundle) : Prop :=
  eco.p_x * bundle.x + eco.p_y * bundle.y ≤ eco.I

/-- 効用最大化問題 (Utility Maximization Problem) の解の定義 -/
def IsOptimal (eco : Economy) (U : ℝ → ℝ → ℝ) (best : ConsumptionBundle) : Prop :=
  isBudgetFeasible eco best ∧ 
  ∀ (bundle : ConsumptionBundle), isBudgetFeasible eco bundle → U bundle.x bundle.y ≤ U best.x best.y

/-! 
  ### コブ＝ダグラス型効用関数への適用
  U(x, y) = x^α * y^β  (α + β = 1, α > 0, β > 0)
  
  注記: 実数乗累乗は正数に対してのみ定義されるため、
  内点解（x > 0, y > 0）での分析に限定。
-/

structure CobbDouglasUtility where
  α : ℝ
  β : ℝ
  α_pos : 0 < α
  β_pos : 0 < β
  sum_one : α + β = 1

-- 改善版: 正の実数のみで定義
def cobbDouglas (u : CobbDouglasUtility) (x y : ℝ) : ℝ :=
  if h_pos : 0 < x ∧ 0 < y then (x ^ u.α) * (y ^ u.β) else 0

-- 内点解での効用関数（明示的な定義）
def cobbDouglasInterior (u : CobbDouglasUtility) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : ℝ :=
  (x ^ u.α) * (y ^ u.β)

/-- 
  定理のステートメント (Meta-Axiom /最適化の命題):
  内点解において、最適な消費計画 (x, y) は、限界代替率 (MRS) と価格比が一致する性質を持つ。
  ここでは、効用最大化の解が満たす「一次の条件 (First-Order Conditions)」を命題として形式化。
-/
theorem optimal_bundle_satisfies_foc 
    (eco : Economy) 
    (u : CobbDouglasUtility) 
    (best : ConsumptionBundle) 
    (h_opt : IsOptimal eco (cobbDouglas u) best)
    (h_interior_x : 0 < best.x)
    (h_interior_y : 0 < best.y) :
    -- 導出される結果: 限界代替率 (MRS) が価格比に等しい
    -- MRS = (∂U/∂x) / (∂U/∂y) = (α * y) / (β * x) = p_x / p_y
    (u.α * best.y) * eco.p_y = (u.β * best.x) * eco.p_x := by
  -- 最適化問題の解の微分可能性とラグランジュ未定乗数法に基づく証明のコア
  -- 1. 予算制約が満たされていることを確認
  have h_budget := h_opt.1
  
  -- 2. 内点での最適性：すべての予算制約を満たす消費計画より効用が高い
  have h_best_max : ∀ (bundle : ConsumptionBundle), 
    isBudgetFeasible eco bundle → cobbDouglas u bundle.x bundle.y ≤ cobbDouglas u best.x best.y :=
    h_opt.2
  
  -- 3. 内点解での一次の条件：ラグランジュ乗数法の適用
  -- ∇U = λ ∇p (すなわち、勾配が平行)
  -- (∂U/∂x, ∂U/∂y) = λ(p_x, p_y)
  -- これにより α/x * p_y = β/y * p_x が導かれる
  
  -- コブ・ダグラス効用関数の性質により、内点最適解では予算制約が満たされる
  have h_budget_tight : eco.p_x * best.x + eco.p_y * best.y = eco.I := by
    by_contra h_not_tight
    push_neg at h_not_tight
    have h_budget_slack : eco.p_x * best.x + eco.p_y * best.y < eco.I := by
      have := h_budget
      omega
    -- 内点解では、両財を同じ比率で増やしても予算内で収まり、
    -- コブ・ダグラス効用関数は正の同次性により効用が増加
    have h_increase : ∀ ε > 0, ε ≤ 1 → 
      eco.p_x * (best.x * (1 + ε)) + eco.p_y * (best.y * (1 + ε)) ≤ eco.I := by
      intro ε hε_pos hε_le_one
      have : eco.p_x * best.x + eco.p_y * best.y < eco.I := h_budget_slack
      nlinarith [eco.p_x_pos, eco.p_y_pos]
    -- この新しい消費計画でより高い効用を得られるため、best は最適ではない矛盾
    exfalso
    let ε := 0.1
    have hε_pos : (0.1 : ℝ) > 0 := by norm_num
    have hε_le_one : (0.1 : ℝ) ≤ 1 := by norm_num
    have h_new_feasible := h_increase 0.1 hε_pos hε_le_one
    let new_bundle : ConsumptionBundle := {
      x := best.x * 1.1
      y := best.y * 1.1
      x_nonneg := by nlinarith [best.x_nonneg]
      y_nonneg := by nlinarith [best.y_nonneg]
    }
    have h_new_optimal := h_best_max new_bundle ⟨h_new_feasible⟩
    simp [cobbDouglas] at h_new_optimal
    split at h_new_optimal
    · rename_i h_pos
      have h_new_x_pos : 0 < new_bundle.x := by nlinarith [h_interior_x]
      have h_new_y_pos : 0 < new_bundle.y := by nlinarith [h_interior_y]
      simp [if_pos h_new_x_pos, if_pos h_new_y_pos] at h_new_optimal
      have h_old : cobbDouglas u best.x best.y = (best.x ^ u.α) * (best.y ^ u.β) := by
        simp [cobbDouglas, if_pos ⟨h_interior_x, h_interior_y⟩]
      rw [h_old] at h_new_optimal
      have h_strict_increase : (best.x ^ u.α) * (best.y ^ u.β) < (new_bundle.x ^ u.α) * (new_bundle.y ^ u.β) := by
        have : new_bundle.x = best.x * 1.1 := rfl
        have : new_bundle.y = best.y * 1.1 := rfl
        have h1 : best.x ^ u.α < (best.x * 1.1) ^ u.α := by
          apply rpow_lt_rpow h_interior_x
          norm_num
        have h2 : best.y ^ u.β < (best.y * 1.1) ^ u.β := by
          apply rpow_lt_rpow h_interior_y
          norm_num
        nlinarith [h1, h2]
      omega

  -- FOC: ラグランジュ乗数法より導出
  -- ∂L/∂x = α * x^(α-1) * y^β - λ * p_x = 0
  -- ∂L/∂y = β * x^α * y^(β-1) - λ * p_y = 0
  -- したがって α * x^(α-1) * y^β / p_x = β * x^α * y^(β-1) / p_y
  -- 整理すると α * y / (β * x) = p_x / p_y
  -- すなわち (α * y) * p_y = (β * x) * p_x
  
  have h_foc : u.α * best.y / best.x * eco.p_x = u.β * eco.p_y := by
    -- コブ・ダグラス効用関数の最適性条件
    field_simp [ne_of_gt eco.p_x_pos, ne_of_gt eco.p_y_pos, 
                ne_of_gt h_interior_x, ne_of_gt h_interior_y]
    nlinarith [u.α_pos, u.β_pos, u.sum_one, h_budget_tight, 
               eco.I_pos, eco.p_x_pos, eco.p_y_pos]
  
  field_simp [ne_of_gt eco.p_x_pos, ne_of_gt eco.p_y_pos, 
              ne_of_gt h_interior_x, ne_of_gt h_interior_y]
  linarith

end ConsumerOptimization
