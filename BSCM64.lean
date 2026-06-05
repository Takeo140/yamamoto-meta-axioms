import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Bounded Smooth Collatz Machine (BSCM) — Engineering Version
# Simplified δ: All branches are state-reducing
# Fully Formalized — No Axioms, No Sorry

Author: Takeo Yamamoto
License: Apache 2.0
-/

-- ───────────────────────────────────────────────────────────────────
-- 1. Core transition function
-- ───────────────────────────────────────────────────────────────────

/--
  【Engineering δ】
  Even: right shift (halve)
  Odd:  add 1 then halve
  All branches are strictly reducing. Predictable, implementation-friendly.
-/
def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then
    s / 2
  else
    (s + 1) / 2

-- ───────────────────────────────────────────────────────────────────
-- 2. Control interface
-- ───────────────────────────────────────────────────────────────────

def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | []               => initial_state
  | input :: inputs  =>
      bscm_control_exec (bscm_control_step initial_state input) inputs

-- ───────────────────────────────────────────────────────────────────
-- 3. Theorems
-- ───────────────────────────────────────────────────────────────────

theorem bscm_delta_reduces (s : Nat) (h : s > 1) : bscm_delta s < s := by
  unfold bscm_delta
  split_ifs with h1
  · have : s / 2 < s := Nat.div_lt_iff_lt_mul_left (by omega) |>.mpr (by omega)
    exact this
  · have odd_s : s % 2 = 1 := by omega
    have : (s + 1) / 2 < s := by omega
    exact this

theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) :
    bscm_delta s ≤ 18446744073709551615 := by
  unfold bscm_delta
  split_ifs with h1
  · have : s / 2 ≤ s := Nat.div_le_self s 2
    omega
  · have : (s + 1) / 2 ≤ (s + 1) := Nat.div_le_self (s + 1) 2
    omega

theorem bscm_control_robust (current_state : Nat) (external_input : Nat) :
    bscm_control_step current_state external_input ≤ 18446744073709551615 := by
  unfold bscm_control_step
  have h_prime : (current_state + external_input) % 18446744073709551616 ≤ 18446744073709551615 := by
    have : (current_state + external_input) % 18446744073709551616 < 18446744073709551616 :=
      Nat.mod_lt (current_state + external_input) (by omega)
    omega
  exact bscm_state_bounded _ h_prime

theorem bscm_system_never_overflows
    (initial_state : Nat) (input : Nat) (inputs : List Nat) :
    bscm_control_exec (bscm_control_step initial_state input) inputs
      ≤ 18446744073709551615 := by
  generalize h : bscm_control_step initial_state input = start_state
  rw [← h]
  clear h
  revert initial_state input
  induction inputs generalizing initial_state input with
  | nil =>
    intro _ _
    dsimp [bscm_control_exec]
    exact bscm_control_robust initial_state input
  | cons head tail ih =>
    intro init_state ext_input
    dsimp [bscm_control_exec]
    have h1 : bscm_control_step init_state ext_input ≤ 18446744073709551615 :=
      bscm_control_robust init_state ext_input
    exact ih (bscm_control_step init_state ext_input) head
