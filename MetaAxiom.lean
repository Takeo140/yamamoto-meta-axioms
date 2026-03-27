-- MetaAxiom.lean
-- Author: Takeo Yamamoto
-- License: CC BY 4.0
-- Replaces the prior circular axiom-based formulation.
-- A1–A4 are now type-level structures with substantive content.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

namespace MetaAxioms

-- ── A1: Extremum Principle ────────────────────────────────────────────────
-- L achieves a global minimum at x₀.
def IsMinimal {X : Type} (L : X → ℝ) (x₀ : X) : Prop :=
  ∀ x, L x₀ ≤ L x

-- ── A2: Topological Space ─────────────────────────────────────────────────
-- Topology is used substantively: L must be continuous.
structure TopologicalMinimum (X : Type) [TopologicalSpace X] where
  L   : X → ℝ
  x₀  : X
  hL  : Continuous L
  hMin : IsMinimal L x₀

-- ── A3: Logical Consistency ───────────────────────────────────────────────
-- C F holds, and C is falsifiable (not trivially ⊤).
structure IsConsistent {X : Type}
    (C : (X → ℝ) → Prop) (F : X → ℝ) : Prop where
  holds       : C F
  falsifiable : ∃ G : X → ℝ, ¬ C G

-- ── A4: Hierarchical Structure ────────────────────────────────────────────
-- Convex combination: weights non-negative, sum to 1.
structure MacroWeights (ι : Type) [Fintype ι] where
  w       : ι → ℝ
  hNonNeg : ∀ i, 0 ≤ w i
  hSum    : ∑ i, w i = 1

variable {ι : Type} [Fintype ι]

def MacroFunction
    (W : MacroWeights ι)
    (Fmicro : ι → (α → ℝ))
    (x : α) : ℝ :=
  ∑ i, W.w i * Fmicro i x

-- ── Integrated Framework ─────────────────────────────────────────────────
structure IntegratedFramework (X : Type) [TopologicalSpace X] where
  tm : TopologicalMinimum X
  C  : (X → ℝ) → Prop
  F  : X → ℝ
  hC : IsConsistent C F

-- ── Realization ───────────────────────────────────────────────────────────
def IsRealization {X : Type} [TopologicalSpace X]
    (M : IntegratedFramework X) (x₀ : X) : Prop :=
  M.tm.x₀ = x₀

-- ── Lemma: realized point is a global minimum ─────────────────────────────
lemma realization_is_minimal {X : Type} [TopologicalSpace X]
    (M : IntegratedFramework X) (x₀ : X)
    (hR : IsRealization M x₀) :
    IsMinimal M.tm.L x₀ := by
  rw [← hR]; exact M.tm.hMin

-- ── Lemma: MacroFunction inherits non-negativity ─────────────────────────
lemma macro_nonneg {ι : Type} [Fintype ι] {X : Type}
    (W : MacroWeights ι)
    (Fmicro : ι → X → ℝ)
    (hF : ∀ i x, 0 ≤ Fmicro i x)
    (x : X) :
    0 ≤ MacroFunction W Fmicro x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (W.hNonNeg i) (hF i x)

end MetaAxioms
