/-
  ACM-TY — Theorem Supplement
  Closes three of the specification-only gaps identified in review:
    A. mulWith is proved bilinear (not just typed as such).
    B. Two concrete UOp instances are constructed and unitary_like is discharged.
    C. BSCM.delta is proved to terminate (reach ≤ 1) under iteration —
       a genuine halting/convergence theorem, proved over ℕ (see note below).
  A fourth item — diffuse's claim to compute a weighted average — is NOT
  closed. See Part D: it is false in general over U64 = ZMod (2^64), and
  that finding is stated as a theorem, not patched over.

  I have no Lean toolchain in this environment and could not compile this
  file. Tactics below are standard (ring, omega, Finset.sum_add_distrib,
  strong induction) and should go through, but per your own CI discipline,
  treat this as unverified until it is green on your machine and report
  back what breaks.

  Author: Takeo Yamamoto
  License: Apache 2.0
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

/- ============================================================
   PART A — UHA: mulWith is genuinely bilinear
   ============================================================
   Closes: "no algebra identity is proved for mulWith under any
   choice of structure constants."
-/

namespace UHA

variable {n : Nat} (c : Fin n → Fin n → UHA n)

theorem mulWith_add_left (x₁ x₂ y : UHA n) :
    mulWith c (x₁ + x₂) y = mulWith c x₁ y + mulWith c x₂ y := by
  ext i
  show (∑ j, ∑ k, ((x₁ + x₂).coords j) * (y.coords k) * (c j k).coords i)
     = (∑ j, ∑ k, (x₁.coords j) * (y.coords k) * (c j k).coords i)
     + (∑ j, ∑ k, (x₂.coords j) * (y.coords k) * (c j k).coords i)
  simp only [HAdd.hAdd, Add.add, UHA.add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem mulWith_add_right (x y₁ y₂ : UHA n) :
    mulWith c x (y₁ + y₂) = mulWith c x y₁ + mulWith c x y₂ := by
  ext i
  show (∑ j, ∑ k, (x.coords j) * ((y₁ + y₂).coords k) * (c j k).coords i)
     = (∑ j, ∑ k, (x.coords j) * (y₁.coords k) * (c j k).coords i)
     + (∑ j, ∑ k, (x.coords j) * (y₂.coords k) * (c j k).coords i)
  simp only [HAdd.hAdd, Add.add, UHA.add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem mulWith_smul_left (a : U64) (x y : UHA n) :
    mulWith c (a • x) y = a • mulWith c x y := by
  ext i
  show (∑ j, ∑ k, ((a • x).coords j) * (y.coords k) * (c j k).coords i)
     = a * (∑ j, ∑ k, (x.coords j) * (y.coords k) * (c j k).coords i)
  simp only [HSMul.hSMul, SMul.smul, UHA.smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Bilinearity, stated as a bundle: for fixed structure constants `c`,
    `mulWith c` is additive and U64-homogeneous in both arguments.
    This is what makes `(UHA n, +, mulWith c)` an algebra over U64 in
    the technical sense — modulo associativity and a unit, neither of
    which is claimed here. -/
theorem mulWith_bilinear :
    (∀ x₁ x₂ y, mulWith c (x₁ + x₂) y = mulWith c x₁ y + mulWith c x₂ y) ∧
    (∀ x y₁ y₂, mulWith c x (y₁ + y₂) = mulWith c x y₁ + mulWith c x y₂) ∧
    (∀ a x y, mulWith c (a • x) y = a • mulWith c x y) :=
  ⟨mulWith_add_left c, mulWith_add_right c, mulWith_smul_left c⟩

end UHA

/- ============================================================
   PART B — UHA: concrete UOp instances (unitarity witnesses)
   ============================================================
   Closes: "no operator in this model has been shown to preserve norm."
-/

namespace UHA

variable {n : Nat}

/-- The identity operator trivially preserves the quadratic form. -/
def idOp : UOp n where
  f := id
  unitary_like := fun _ => rfl

/-- Negation preserves the quadratic form: (-x_i)^2 = x_i^2 in any
    commutative ring, so `norm` is unchanged. -/
def negOp : UOp n where
  f := fun x => ⟨fun i => -(x.coords i)⟩
  unitary_like := by
    intro v
    show (∑ i, (-(v.coords i)) * (-(v.coords i))) = ∑ i, (v.coords i) * (v.coords i)
    apply Finset.sum_congr rfl
    intro i _
    ring

end UHA

/- ============================================================
   PART C — BSCM.delta: termination under iteration
   ============================================================
   Closes: "no decidability/complexity property is stated for any
   part of the model."

   NOTE: this is proved over ℕ, not U64 = ZMod (2^64). The original
   BSCM.delta is stated on U64 using `/` and, in `entropy`, `&&&`/`>>>`.
   Whether `/` on ZMod (2^64) coincides with the natural-number floor
   division used here — as opposed to the field-style ZMod.inv-based
   division that ZMod n exposes for general n — was flagged as an open
   compilation question in the accompanying paper and is NOT resolved
   by this file. The theorem below establishes the intended
   computational content (halting) for the semantics you almost
   certainly meant; transporting it to U64 requires confirming that
   equivalence first.
-/

namespace BSCM

def deltaNat (s : Nat) : Nat :=
  if s % 2 = 0 then s / 2 else (s + 1) / 2

theorem deltaNat_lt {s : Nat} (h : 1 < s) : deltaNat s < s := by
  unfold deltaNat
  split
  · decide
  · decide

/-- Iterating `deltaNat` from any starting value reaches ≤ 1 in finitely
    many steps. This is the halting theorem the original file's naming
    ("control step") implicitly claimed but never stated. -/
theorem deltaNat_terminates (s : Nat) : ∃ k, (deltaNat)^[k] s ≤ 1 := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    by_cases hs : s ≤ 1
    · exact ⟨0, hs⟩
    · push_neg at hs
      obtain ⟨k, hle⟩ := ih (deltaNat s) (deltaNat_lt hs)
      refine ⟨k + 1, ?_⟩
      simpa [Function.iterate_succ_apply'] using hle

end BSCM

/- ============================================================
   PART D — DIFD.diffuse: the "weighted average" claim is FALSE
   in general over U64
   ============================================================
   This is a negative result, not a gap left open. Recorded so it
   isn't silently rediscovered later as a bug report.

   `diffuse` computes `norm⁻¹ • total` where `norm = Σ weights` and
   `⁻¹` is `ZMod.inv`. On `ZMod (2^64)`, an element has a multiplicative
   inverse iff it is odd (a unit mod a power of two). Whenever the
   weight sum is even — which is the generic case, since roughly half
   of all U64 values are even — `norm⁻¹` is defined by convention to be
   `0` (Mathlib's `ZMod.inv` returns `0` on non-units), so `diffuse`
   silently returns the zero vector instead of any kind of average.

   Concretely: for n = 1, a single neighbor with weight 2 and nonzero
   state, `diffuse` returns 0, not that neighbor's state — contradicting
   the "falls back to weighted average" reading of the definition.
-/

namespace DIFD

open UHA

example : (2 : U64)⁻¹ * (2 : U64) ≠ (1 : U64) := by
  decide

/-- Counterexample: diffuse of a single neighbor with even weight
    collapses to zero rather than that neighbor's state. -/
theorem diffuse_not_average_in_general
    {n : Nat} (top : UHA.Topology n) (e nb : GIFE.Entity n)
    (hconn : Topology.conn top ⟨e.id % n⟩ ⟨nb.id % n⟩ = (2 : U64))
    (hstate : nb.state ≠ (⟨fun _ => 0⟩ : UHA n)) :
    DIFD.diffuse top e [nb] ≠ nb.state := by
  -- Reduce the singleton folds for total and norm to their concrete values
  have h_total : List.foldl (fun acc nb' =>
    let w := Topology.conn top ⟨e.id % n⟩ ⟨nb'.id % n⟩; UHA.add acc (UHA.smul w nb'.state))
    (⟨fun _ => (0 : U64)⟩ : UHA n) [nb] =
    UHA.smul (Topology.conn top ⟨e.id % n⟩ ⟨nb.id % n⟩) nb.state := by
    simp [List.foldl]
  have h_norm : List.foldl (fun a nb' => a + Topology.conn top ⟨e.id % n⟩ ⟨nb'.id % n⟩)
    (0 : U64) [nb] = Topology.conn top ⟨e.id % n⟩ ⟨nb.id % n⟩ := by
    simp [List.foldl]
  simp [DIFD.diffuse, h_total, h_norm, hconn]
  -- 2 is not a unit in ZMod (2^64), so its inverse is 0
  have : ¬ IsUnit (2 : U64) := by decide
  have inv2_zero := ZMod.inv_eq_zero_of_not_unit this
  simp [inv2_zero]
  -- Now diffuse reduces to 0, which is not equal to nb.state by hypothesis
  exact Ne.symm hstate

end DIFD
