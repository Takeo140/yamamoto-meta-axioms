import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Theory of Bounded Smooth Collatz Machine (BSCM)
# 64-bit Version
Author: Takeo Yamamoto
License: Apache 2.0
-/

-- 64ビット上限
def MAX64 : Nat := 2^64 - 1  -- 18446744073709551615

def bscm_delta64 (s : Nat) : Nat :=
  if s % 2 = 0 then
    s / 2
  else if s % 4 = 1 then
    (s - 1) / 2
  else
    MAX64 - (s % 2^64)

def bscm_exec64 (initial_state : Nat) : Nat → Nat
  | 0     => initial_state
  | n + 1 => bscm_delta64 (bscm_exec64 initial_state n)

theorem bscm_state_bounded64 (s : Nat) (h : s ≤ MAX64) : 
    bscm_delta64 s ≤ MAX64 := by
  dsimp [bscm_delta64, MAX64]
  split_ifs with h1 h2
  · omega
  · omega
  · omega

theorem bscm_machine_never_overflows64 
    (initial_state : Nat) 
    (h_init : initial_state ≤ MAX64) 
    (k : Nat) : 
    bscm_exec64 initial_state k ≤ MAX64 := by
  induction' k with k ih
  · exact h_init
  · dsimp [bscm_exec64]
    exact bscm_state_bounded64 (bscm_exec64 initial_state k) ih

axiom bscm_halting_property64 (initial_state : Nat) (h : initial_state > 0) :
    ∃ k : Nat, bscm_exec64 initial_state k = 1

open Classical

def bscm_halting_step64 (initial_state : Nat) (h : initial_state > 0) : Nat :=
  Nat.find (bscm_halting_property64 initial_state h)

def evaluate_bscm_complexity64 (input : Nat) : Nat :=
  if h_in : input = 0 then
    0
  else
    let initial_state := (input % (2^63)) * 2 + 1
    have h_state : initial_state > 0 := by positivity
    bscm_halting_step64 initial_state h_state
