-- Author: Takeo Yamamoto
-- License: Apache 2.0
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
/-!
# Bounded Smooth Collatz Machine (BSCM) — Engineering Version
# Simplified δ: All branches are state-reducing
# Fully Formalized — No Axioms, No Sorry
-/

-- ───────────────────────────────────────────────────────────────────
-- 1. Core transition function
-- ───────────────────────────────────────────────────────────────────

/-- Even: halve. Odd: (s+1)/2. Both branches strictly reduce s when s > 1. -/
def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then s / 2
  else (s + 1) / 2

-- ───────────────────────────────────────────────────────────────────
-- 2. Control interface
-- ───────────────────────────────────────────────────────────────────

def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | []              => initial_state
  | input :: inputs => bscm_control_exec (bscm_control_step initial_state input) inputs

-- ───────────────────────────────────────────────────────────────────
-- 3. Theorems
-- ───────────────────────────────────────────────────────────────────

/-- δ は s > 1 のとき strictly reducing -/
theorem bscm_delta_reduces (s : Nat) (h : s > 1) : bscm_delta s < s := by
  dsimp [bscm_delta]
  split_ifs with h1
  · -- 偶数: s / 2 < s  ①修正: Nat.div_lt_self を使用
    exact Nat.div_lt_self (by omega) (by omega)
  · -- 奇数: (s+1)/2 < s
    have : s % 2 = 1 := by omega
    omega

/-- δ は境界値 2^64-1 を保持する -/
theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) :
    bscm_delta s ≤ 18446744073709551615 := by
  dsimp [bscm_delta]            -- ③修正: unfold → dsimp
  split_ifs <;> omega

/-- 制御ステップは常に境界内に収まる -/
theorem bscm_control_robust (current_state : Nat) (external_input : Nat) :
    bscm_control_step current_state external_input ≤ 18446744073709551615 := by
  dsimp [bscm_control_step]     -- ③修正: unfold → dsimp
  apply bscm_state_bounded
  omega

/-- 任意の入力列に対してオーバーフローしない -/
theorem bscm_system_never_overflows
    (initial_state : Nat) (input : Nat) (inputs : List Nat) :
    bscm_control_exec (bscm_control_step initial_state input) inputs
      ≤ 18446744073709551615 := by
  -- ②修正: generalize 迂回を廃止し直接帰納法
  induction inputs generalizing initial_state input with
  | nil        =>
      dsimp [bscm_control_exec]
      exact bscm_control_robust initial_state input
  | cons head tail ih =>
      dsimp [bscm_control_exec]
      exact ih (bscm_control_step initial_state input) head
