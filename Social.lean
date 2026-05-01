import Mathlib.Analysis.SpecialFunctions.Log

structure Society where
  energy_consumption   : ℝ
  intellectual_density : ℝ
  is_active            : Prop

def is_low_energy_society (s : Society) : Prop :=
  s.energy_consumption < 1.0 ∧ s.intellectual_density > 10.0

theorem optimization_of_life (s : Society)
    (h1 : s.is_active)
    (h2 : s.energy_consumption > 10.0)
    : ∃ s' : Society, is_low_energy_society s' ∧ s'.intellectual_density > s.intellectual_density := by
  refine ⟨⟨0, max s.intellectual_density 10 + 1, s.is_active⟩, ?_, ?_⟩
  · constructor
    · norm_num
    · have : max s.intellectual_density 10 ≥ 10 := le_max_right _ _
      linarith
  · have : max s.intellectual_density 10 ≥ s.intellectual_density := le_max_left _ _
    linarith
