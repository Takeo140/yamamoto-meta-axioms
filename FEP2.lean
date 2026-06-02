import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace FreeEnergyPrinciple

/-!
# FEP Model Structure
- y: Sensory input (observation)
- μ: Internal state (generative model)
- σ: Precision (inverse variance, confidence)
-/

structure FEP_System :=
  (y : ℝ)
  (μ : ℝ)
  (σ : ℝ)
  (h_sigma : σ > 0)

/-!
# Variational Free Energy (VFE)
定義: VFE = 予測誤差の期待値 - エントロピー
VFE(μ) = (y - μ)^2 * (σ^2 / 2) - log(σ)
-/

def vfe (s : FEP_System) : ℝ :=
  (s.y - s.μ)^2 * (s.σ^2 / 2) - Real.log s.σ

/-!
# Minimization Theorem
最適な内部状態 μ_opt は観測値 y と一致する。
-/

theorem vfe_minimization (s : FEP_System) :
  ∃ (μ_opt : ℝ), ∀ (μ : ℝ), vfe {s with μ := μ_opt} ≤ vfe {s with μ := μ} := by
  use s.y
  intro μ
  dsimp [vfe]
  -- μ = y のとき予測誤差項は0になる
  have h_opt : (s.y - s.y)^2 * (s.σ^2 / 2) = 0 := by simp
  rw [h_opt]
  -- 任意の μ に対して (y - μ)^2 * (σ^2 / 2) ≥ 0 である
  have h_nonneg : 0 ≤ (s.y - μ)^2 * (s.σ^2 / 2) := by
    apply mul_nonneg
    exact pow_two_nonneg (s.y - μ)
    exact mul_nonneg (by linarith [s.h_sigma]) (by norm_num)
  exact le_add_of_nonneg_right h_nonneg

end FreeEnergyPrinciple
