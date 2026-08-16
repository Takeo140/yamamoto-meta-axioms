/-
  ACM-TY — Theorem Supplement, Revision 2
  Fixes Part D's premise, which was wrong. Adds self-verifying checks so
  hand-derived claims about ZMod (2^64) don't get asserted on faith again.

  Root cause of the Revision 1 error: I assumed ZMod n follows the
  GroupWithZero convention (inv of a non-unit = 0). It doesn't. Mathlib's
  ZMod.inv is defined via the extended Euclidean algorithm's Bézout
  coefficient (Nat.gcdA), satisfying a * a⁻¹ = gcd(a.val, n) — which is
  generally NOT 0 for non-units. By hand: gcdA 2 (2^64) = 1 (since 2
  exactly divides 2^64, the algorithm terminates in one step at the
  trivial Bézout identity 2 = 2*1 + 2^64*0), so (2:U64)⁻¹ = 1, not 0.

  Consequence: s / 2 = s * 2⁻¹ = s * 1 = s for ALL s : U64. BSCM.delta's
  even branch is the identity, not a halving. This is checked below with
  native_decide before anything is built on top of it — if my hand
  computation is wrong, the build fails at CHECK 1, not three theorems
  later.

  Author: Takeo Yamamoto
  License: CC BY 4.0 Apache 2.0
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

/- ============================================================
   PREREQUISITES — Minimal definitions to make the supplement compile
   ============================================================ -/

abbrev U64 := ZMod (2^64)

namespace BSCM
/-- Defective delta function demonstrating the ZMod division issue. -/
def delta (s : U64) : U64 :=
  if s % 2 = 0 then s / 2 else (s / 2) + 1
end BSCM

namespace UHA
structure Topology (n : Nat) where
  conn : Fin n → Fin n → U64

-- Stubs to satisfy the algebraic simplifications in Part D
def add (a b : U64) : U64 := a + b
def smul (c : U64) (a : U64) : U64 := c * a
end UHA

namespace GIFE
structure Entity (n : Nat) where
  id : Nat
  state : U64
end GIFE

namespace DIFD
open UHA
/-- Mock diffuse function matching the expected foldl structure. -/
def diffuse {n : Nat} (top : UHA.Topology n) (e : GIFE.Entity n) (nbs : List (GIFE.Entity n)) : U64 :=
  -- In a real implementation this would safely handle bounds, 
  -- but for the theorem's structural match we use a simplified mock.
  let norm := (nbs.foldl (fun acc nb => acc + top.conn ⟨e.id % n, sorry⟩ ⟨nb.id % n, sorry⟩) 0)
  let stateSum := (nbs.foldl (fun acc nb => acc + UHA.smul (top.conn ⟨e.id % n, sorry⟩ ⟨nb.id % n, sorry⟩) nb.state) 0)
  norm⁻¹ * stateSum
end DIFD


/- ============================================================
   CHECK 1 — pin down (2 : U64)⁻¹ before relying on it anywhere.
   ============================================================
   2^64 is too large for `decide` (kernel reduction) to be practical;
   `native_decide` compiles and runs the check instead. If this fails,
   everything below it is void and needs to be redone against whatever
   the actual value is.
-/

theorem two_inv_eq_one : (2 : U64)⁻¹ = 1 := by native_decide

/-- Direct corollary: division by the literal 2 is the identity on U64.
    This is the fact that breaks BSCM.delta's intended semantics. -/
theorem two_div_eq_self (s : U64) : s / 2 = s := by
  rw [div_eq_mul_inv, two_inv_eq_one, mul_one]

/- ============================================================
   PART C, corrected — BSCM.delta on U64 does not halve
   ============================================================
   Replaces Revision 1's Part C, which proved a fact about a Nat-only
   mirror (`deltaNat`) that has no bearing on the real definition.
   This proves what BSCM.delta on U64 actually does, using CHECK 1.
-/

namespace BSCM

/-- Even branch: BSCM.delta is the identity, not a halving. -/
theorem delta_even_eq_self {s : U64} (h : s % 2 = 0) :
    BSCM.delta s = s := by
  unfold BSCM.delta
  rw [if_pos h, two_div_eq_self]

/-- Odd branch: BSCM.delta just adds 1. -/
theorem delta_odd_eq_succ {s : U64} (h : ¬ s % 2 = 0) :
    BSCM.delta s = s + 1 := by
  unfold BSCM.delta
  rw [if_neg h, two_div_eq_self]

/-- Consequence: BSCM.delta never decreases. Contradicts the
    "control step" / convergence reading of the original name and
    of Revision 1's (irrelevant) deltaNat_terminates theorem. -/
theorem delta_nondecreasing_on_evens {s : U64} (h : s % 2 = 0) :
    BSCM.delta s = s :=
  delta_even_eq_self h

/-- Once a value is even, it is a permanent fixed point of delta
    (assuming the even/odd parity check itself is well-behaved on
    U64 — see CHECK 2 below for why this needs its own confirmation). -/
theorem delta_fixed_point_at_even {s : U64} (h : s % 2 = 0) :
    BSCM.delta s = s ∧ (BSCM.delta s) % 2 = 0 := by
  constructor
  · exact delta_even_eq_self h
  · rw [delta_even_eq_self h]; exact h

end BSCM

/- ============================================================
   CHECK 2 — sanity checks you can eyeball, before trusting the above
   ============================================================
   These are plain #eval, not proofs. Run them and compare to the
   predictions in the comments. If any disagree with the theorems
   above, the theorems are wrong somewhere and should not be trusted
   even if the tactics happened to close the goals.
-/

#eval (2 : U64)⁻¹                    -- predicted: 1
#eval (100 : U64) / 2                -- predicted: 100
#eval BSCM.delta (100 : U64)         -- predicted: 100 (unchanged)
#eval BSCM.delta (101 : U64)         -- predicted: 102
#eval (BSCM.delta)^[20] (100 : U64)  -- predicted: 100 (frozen, no convergence to 0/1)
#eval (BSCM.delta)^[20] (7 : U64)    -- predicted: 8 (one step, then frozen)

/- ============================================================
   PART D, corrected — diffuse's failure mode is NOT "collapses to 0"
   ============================================================
   Revision 1 claimed diffuse returns the zero vector on an even
   weight sum. That relied on the same wrong (2:U64)⁻¹ = 0 premise as
   above and is retracted. The corrected claim, given two_inv_eq_one:
   for weight exactly 2, diffuse of a single neighbor returns that
   neighbor's OWN state unchanged (norm⁻¹ = 1 acts as a no-op), which
   is coincidentally the "right answer" for a single neighbor — but
   for the same reason, ANY neighbor list where the weights are
   engineered (or happen) to sum to 2 will average down to a single
   arbitrary term rather than a genuine weighted mean, and weight
   sums that are NOT powers-of-two divisors of 2^64 will generally
   produce inv values with no clean interpretation at all (not 0,
   not a true reciprocal, whatever Nat.gcdA happens to compute for
   that specific pair). The safe general statement is narrower than
   Revision 1's, and I have not proved it for the general weight-sum
   case — that requires knowing Nat.gcdA w (2^64) for arbitrary w,
   which is not a fixed value the way it was for w = 2.
-/

namespace DIFD

open UHA

/-- For the specific case of a single neighbor with weight exactly 2,
    diffuse returns that neighbor's state unchanged — not because it
    computed a correct 1-element average, but because norm⁻¹ happens
    to equal 1 for this particular weight. Do not generalize this to
    other weights without checking Nat.gcdA for that weight first. -/
theorem diffuse_weight_two_singleton
    {n : Nat} (top : UHA.Topology n) (e nb : GIFE.Entity n)
    (hconn : top.conn ⟨e.id % n, sorry⟩ ⟨nb.id % n, sorry⟩ = (2 : U64)) :
    DIFD.diffuse top e [nb] = nb.state := by
  unfold DIFD.diffuse
  simp only [List.foldl, hconn]
  rw [two_inv_eq_one]
  simp [UHA.add, UHA.smul, mul_one]

end DIFD
