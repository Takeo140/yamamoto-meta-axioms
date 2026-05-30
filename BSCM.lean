import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Theory of Bounded Smooth Collatz Machine (BSCM) — Engineering Version
# 16-bit, Monotone Reduction δ
# Fully Formalized — No Axioms, No Sorry

Author: Takeo Yamamoto
License: Apache 2.0
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- 1. Core: state space and transition function
-- ─────────────────────────────────────────────────────────────────────────────

/--
  【Engineering δ — 16-bit】
  Even: s / 2       (right shift)
  Odd:  (s + 1) / 2 (round-up shift)
  Both branches are strictly state-reducing. No perturbation term.
-/
def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then
    s / 2
  else
    (s + 1) / 2

/-- Step-execution trace -/
def bscm_exec (initial_state : Nat) : Nat → Nat
  | 0     => initial_state
  | n + 1 => bscm_delta (bscm_exec initial_state n)

-- ─────────────────────────────────────────────────────────────────────────────
-- 2. Core theorems: boundedness
-- ─────────────────────────────────────────────────────────────────────────────

/--
  【State-space invariance】
  δ maps any state in [0, 65535] back into [0, 65535].
-/
theorem bscm_state_bounded (s : Nat) (h : s ≤ 65535) : bscm_delta s ≤ 65535 := by
  dsimp [bscm_delta]
  split_ifs with h1
  · omega
  · omega

/--
  【Global safety invariance】
  For any initial state in [0, 65535] and any number of steps k,
  the machine never overflows.
-/
theorem bscm_machine_never_overflows
    (initial_state : Nat) (h_init : initial_state ≤ 65535) (k : Nat) :
    bscm_exec initial_state k ≤ 65535 := by
  induction k with
  | zero => exact h_init
  | succ k ih =>
    dsimp [bscm_exec]
    exact bscm_state_bounded (bscm_exec initial_state k) ih

-- ─────────────────────────────────────────────────────────────────────────────
-- 3. Halting decidability (完全に証明され、Axiom は不要になりました)
-- ─────────────────────────────────────────────────────────────────────────────

lemma bscm_delta_decreasing (s : Nat) (h : s > 1) : bscm_delta s < s := by
  dsimp [bscm_delta]
  split_ifs with h1
  · omega
  · omega

lemma bscm_delta_one : bscm_delta 1 = 1 := by
  dsimp [bscm_delta]
  rfl

/--
  Halting property: with the monotone δ, every positive state
  eventually reaches 1 (fixed point: δ(1) = 1).
  Proven via well-founded induction on `s`.
-/
theorem bscm_halting_property (initial_state : Nat) (h : initial_state > 0) :
    ∃ k : Nat, bscm_exec initial_state k = 1 := by
  induction' initial_state using Nat.strong_induction_on with s ih
  by_cases h_one : s = 1
  · use 0
    exact h_one
  · have h_gt : s > 1 := by omega
    have h_dec : bscm_delta s < s := bscm_delta_decreasing s h_gt
    have h_pos : bscm_delta s > 0 := by
      dsimp [bscm_delta]
      split_ifs <;> omega
    rcases ih (bscm_delta s) h_dec h_pos with ⟨k, hk⟩
    use k + 1
    dsimp [bscm_exec]
    -- bscm_exec (bscm_delta s) k と bscm_exec s (k + 1) の関係を整理
    have h_step : bscm_exec s (k + 1) = bscm_exec (bscm_delta s) k := by
      induction k with
      | zero => rfl
      | succ n ih_k =>
        dsimp [bscm_exec] at *
        rw [ih_k]
    rw [h_step, hk]

open Classical

/-- Total steps to reach the halting state -/
def bscm_halting_step (initial_state : Nat) (h : initial_state > 0) : Nat :=
  Nat.find (bscm_halting_property initial_state h)

/--
  【Complexity evaluator】
  Projects arbitrary input into the 16-bit state space,
  then returns the number of steps to reach state 1.
-/
def evaluate_bscm_complexity (input : Nat) : Nat :=
  if h_in : input = 0 then
    0
  else
    let initial_state := (input % 32768) * 2 + 1
    have h_state : initial_state > 0 := by omega
    bscm_halting_step initial_state h_state
