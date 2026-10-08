/-
  UHA-PhysAI safety layer — core Lean 4 only (no Mathlib, no lake project needed).
  Mirrors the integer runtime in uha_physai.cpp:
    raw policy output --decode--> force in [-F, F] --shield select--> applied force.
  Claim proved here: for ANY raw policy output, the applied force is within [-F, F].
  NOT proved here: the position bound |q| <= qmax (that is checked empirically in C++).

  Status: written but NOT compiled in the authoring environment.
          Check with:  lean PhysAI_Safety.lean

  License: Apache 2.0 / Author: Takeo Yamamoto
-/

namespace PhysAI

/-- Saturation to [lo, hi]. -/
def sat (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x

theorem sat_bounds (lo hi x : Int) (h : lo ≤ hi) :
    lo ≤ sat lo hi x ∧ sat lo hi x ≤ hi := by
  unfold sat
  split <;> (try split) <;> omega

/-- In-range inputs are untouched. -/
theorem sat_id (lo hi x : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) : sat lo hi x = x := by
  unfold sat
  split <;> (try split) <;> omega

/-- Total decoder: every raw integer becomes a valid force. -/
def decode (F raw : Int) : Int := sat (-F) F raw

theorem decode_bounded (F raw : Int) (hF : 0 ≤ F) :
    -F ≤ decode F raw ∧ decode F raw ≤ F :=
  sat_bounds (-F) F raw (by omega)

/-- Shield: first acceptable candidate, otherwise the fallback. -/
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

/-- Applied force: decoded policy output, its half, zero, or a full brake (-s * F). -/
def shielded (F raw s : Int) (ok : Int → Bool) : Int :=
  select [decode F raw, decode F raw / 2, 0] (-s * F) ok

/-- For any policy output, any shield predicate and any brake direction s ∈ {-1,0,1},
    the applied force stays within the actuator limits. -/
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
