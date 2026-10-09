/-!
  ================================================================
  UHA-PhysAI SUPREME KERNEL (Lean 4)
  ================================================================
  Author : Takeo Yamamoto
  License: Apache 2.0

  Complete Core Verification Layer (Zero Mathlib Dependency)
  1. Actuator Safety Shielding Proofs (sat, decode, select, shielded)
  2. Type-Safe Dimension & Exact Rational Falsification Logic
  3. Formal Physical Law Certificate Generation
-/

namespace PhysAI

/-- Saturation to [lo, hi]. -/
def sat (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x

theorem sat_bounds (lo hi x : Int) (h : lo ≤ hi) :
    lo ≤ sat lo hi x ∧ sat lo hi x ≤ hi := by
  unfold sat
  split <;> (try split) <;> omega

def decode (F raw : Int) : Int := sat (-F) F raw

theorem decode_bounded (F raw : Int) (hF : 0 ≤ F) :
    -F ≤ decode F raw ∧ decode F raw ≤ F :=
  sat_bounds (-F) F raw (by omega)

def select (cands : List Int) (fallback : Int) (ok : Int → Bool) : Int :=
  match cands.find? ok with
  | some u => u
  | none => fallback

theorem select_bounded (F fallback : Int) (cands : List Int) (ok : Int → Bool)
    (hc : ∀ u ∈ cands, -F ≤ u ∧ u ≤ F) (hf : -F ≤ fallback ∧ fallback ≤ F) :
    -F ≤ select cands fallback ok ∧ select cands fallback ok ≤ F := by
  unfold select
  cases h : cands.find? ok with
  | none => exact hf
  | some u => exact hc u (List.mem_of_find?_eq_some h)

/-- Shielded policy output: guarantees applied force is always in [-F, F]. -/
def shielded (F raw s : Int) (ok : Int → Bool) : Int :=
  select [decode F raw, decode F raw / 2, 0] (-s * F) ok

theorem shielded_bounded (F raw s : Int) (ok : Int → Bool)
    (hF : 0 ≤ F) (hs : -1 ≤ s ∧ s ≤ 1) :
    -F ≤ shielded F raw s ok ∧ shielded F raw s ok ≤ F := by
  unfold shielded
  have hb := decode_bounded F raw hF
  refine select_bounded F _ _ ok ?_ ?_
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · have hs3 : s = -1 ∨ s = 0 ∨ s = 1 := by omega
    rcases hs3 with rfl | rfl | rfl <;> omega

end PhysAI

namespace UHA
namespace Unified

abbrev Scalar := ℚ

structure Dim where
  m : ℤ; l : ℤ; t : ℤ
deriving DecidableEq, Repr

namespace Dim
def force : Dim := ⟨1, 1, -2⟩
def length : Dim := ⟨0, 1, 0⟩
def mass : Dim := ⟨1, 0, 0⟩
def velocity : Dim := ⟨0, 1, -1⟩
def mul (a b : Dim) : Dim := ⟨a.m + b.m, a.l + b.l, a.t + b.t⟩
end Dim

structure PhasePoint where
  re : Scalar -- q
  im : Scalar -- p
deriving DecidableEq, Repr

structure RegressionPoint where
  q : Scalar; p : Scalar; v : Scalar; acceleration : Scalar
deriving DecidableEq, Repr

abbrev RegressionData := List RegressionPoint

inductive TypedExpr : Dim → Type where
  | const (d : Dim) (c : Scalar) : TypedExpr d
  | q                            : TypedExpr Dim.length
  | p                            : TypedExpr (Dim.mul Dim.mass Dim.velocity)
  | v                            : TypedExpr Dim.velocity
  | add {d : Dim}                : TypedExpr d → TypedExpr d → TypedExpr d
  | sub {d : Dim}                : TypedExpr d → TypedExpr d → TypedExpr d
  | mul {d1 d2 : Dim}            : TypedExpr d1 → TypedExpr d2 → TypedExpr (Dim.mul d1 d2)
  | neg {d : Dim}                : TypedExpr d → TypedExpr d

def TypedExpr.eval {d : Dim} (q p v : Scalar) : TypedExpr d → Scalar
  | .const _ c => c
  | .q         => q
  | .p         => p
  | .v         => v
  | .add a b   => eval q p v a + eval q p v b
  | .sub a b   => eval q p v a - eval q p v b
  | .mul a b   => eval q p v a * eval q p v b
  | .neg a     => -eval q p v a

abbrev ForceExpr := TypedExpr Dim.force

def forceResidual (law : ForceExpr) (point : RegressionPoint) (mass : Scalar) : Scalar :=
  mass * point.acceleration - law.eval point.q point.p point.v

def exactLaw (law : ForceExpr) (data : RegressionData) (mass : Scalar) : Prop :=
  ∀ pt ∈ data, forceResidual law pt mass = 0

def falsified (law : ForceExpr) (data : RegressionData) (mass : Scalar) : Prop :=
  ∃ pt ∈ data, forceResidual law pt mass ≠ 0

theorem exactLaw_not_falsified (law : ForceExpr) (data : RegressionData) (mass : Scalar)
    (h : exactLaw law data mass) : ¬ falsified law data mass := by
  intro hf
  rcases hf with ⟨pt, hpt, hne⟩
  exact hne (h pt hpt)

structure CertifiedLaw where
  law : ForceExpr
  mass : Scalar
  data : RegressionData
  exactFit : exactLaw law data mass
  antiFalsification : ¬ falsified law data mass

end Unified
end UHA
