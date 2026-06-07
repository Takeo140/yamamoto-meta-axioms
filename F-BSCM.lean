-- Author: Takeo Yamamoto
-- License: Apache 2.0 / CC BY 4.0
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
/-!
# F-BSCM: Space-Time Invariant Meta-Axiomatic Computing Model
-/

-- =============================================================================
-- 1. Time Domain: BSCM
-- =============================================================================

def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then s / 2 else (s + 1) / 2

def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | []              => initial_state
  | input :: inputs => bscm_control_exec (bscm_control_step initial_state input) inputs

theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) :
    bscm_delta s ≤ 18446744073709551615 := by
  dsimp [bscm_delta]; split_ifs <;> omega

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
  induction inputs generalizing initial_state input with
  | nil        => exact bscm_control_robust initial_state input
  | cons h t ih => exact ih (bscm_control_step initial_state input) h

-- =============================================================================
-- 2. Space Domain: F-Theory Topological Indexing
-- =============================================================================

/-- ソート済みノードリストに対する降順不変条件 -/
def SortedInvariant (nodes : List (Nat × Nat)) : Prop :=
  ∀ (w v : Nat), (w, v) ∈ nodes →
    match nodes with
    | []             => True
    | (top_w, _) :: _ => w ≤ top_w

structure FTopologySpace where
  nodes     : List (Nat × Nat)
  invariant : SortedInvariant nodes        -- ④修正: 型エイリアスで整合性を明確化

def insert_node_sorted : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], w, v => [(w, v)]
  | (tw, tv) :: rest, w, v =>
      if w ≥ tw then (w, v) :: (tw, tv) :: rest
      else (tw, tv) :: insert_node_sorted rest w v

/-- ①②修正: メンバシップ分解を List.mem_cons + Prod
