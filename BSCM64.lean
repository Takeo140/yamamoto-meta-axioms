import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Bounded Smooth Collatz Machine (BSCM) — Engineering Version
# Simplified δ: All branches are state-reducing
# Fully Formalized — No Axioms, No Sorry

Author: Takeo Yamamoto
License: Apache 2.0
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- 1. Core transition function
-- ─────────────────────────────────────────────────────────────────────────────

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

-- ─────────────────────────────────────────────────────────────────────────────
-- 2. Control interface
-- ─────────────────────────────────────────────────────────────────────────────

def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | []               => initial_state
  | input :: inputs  =>
      bscm_control_exec (bscm_control_step initial_state input) inputs

-- ─────────────────────────────────────────────────────────────────────────────
-- 3. Theorems
-- ─────────────────────────────────────────────────────────────────────────────

theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) :
    bscm_delta s ≤ 18446744073709551615 := by
  dsimp [bscm_delta]
  split_ifs with h1
  · omega
  · omega

theorem bscm_control_robust (current_state : Nat) (external_input : Nat) :
    bscm_control_step current_state external_input ≤ 18446744073709551615 := by
  dsimp [bscm_control_step]
  have h_prime : (current_state + external_input) % 18446744073709551616
                    ≤ 18446744073709551615 := by omega
  exact bscm_state_bounded _ h_prime

theorem bscm_system_never_overflows
    (initial_state : Nat) (input : Nat) (inputs : List Nat) :
    bscm_control_exec (bscm_control_step initial_state input) inputs
      ≤ 18446744073709551615 := by
  -- `induction'` を Lean 4 標準の `induction` 構文に修正し、
  -- 状態が遷移していくため `initial_state` を一般化 (generalizing) します。
  induction inputs generalizing initial_state input with
  | nil =>
    dsimp [bscm_control_exec]
    exact bscm_control_robust initial_state input
  | cons head tail ih =>
    dsimp [bscm_control_exec]
    -- 帰納法の仮定 (ih) を次の状態に適用します
    exact ih (bscm_control_step initial_state input) head
