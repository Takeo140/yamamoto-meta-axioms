import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# F-BSCM: Space-Time Invariant Meta-Axiomatic Computing Model
# Integrating Bounded Smooth Collatz Machine (Time) and F-Theory (Space)

Author: Takeo Yamamoto
License: Apache 2.0 / CC BY 4.0
-/

-- =============================================================================
-- 1. Time Domain: Bounded Smooth Collatz Machine (BSCM)
-- =============================================================================

def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then
    s / 2
  else
    (s + 1) / 2

def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | []               => initial_state
  | input :: inputs  =>
      bscm_control_exec (bscm_control_step initial_state input) inputs

-- --- BSCM Theorems -----------------------------------------------------------

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
  induction inputs generalizing initial_state input with
  | nil =>
    dsimp [bscm_control_exec]
    exact bscm_control_robust initial_state input
  | cons head tail ih =>
    dsimp [bscm_control_exec]
    exact ih (bscm_control_step initial_state input) head


-- =============================================================================
-- 2. Space Domain: F-Theory Topological Indexing
-- =============================================================================

structure FTopologySpace where
  nodes : List (Nat × Nat) -- (Weight, Value)
  invariant : ∀ (w v : Nat), (w, v) ∈ nodes → 
    match nodes with
    | [] => True
    | (top_w, _) :: _ => w ≤ top_w

/-- Insert node maintaining sorted order (descending by weight) -/
def insert_node_sorted : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], w, v => [(w, v)]
  | (tw, tv) :: rest, w, v =>
      if w ≥ tw then
        (w, v) :: (tw, tv) :: rest
      else
        (tw, tv) :: insert_node_sorted rest w v

/-- Auxiliary lemma: insert_node_sorted maintains the descending invariant -/
lemma insert_node_sorted_invariant_aux (nodes : List (Nat × Nat)) 
    (h_inv : ∀ (w v : Nat), (w, v) ∈ nodes → 
      match nodes with | [] => True | (top_w, _) :: _ => w ≤ top_w) 
    (w v : Nat) :
    ∀ (w' v' : Nat), (w', v') ∈ insert_node_sorted nodes w v → 
      (match insert_node_sorted nodes w v with
      | [] => True
      | (top_w, _) :: _ => w' ≤ top_w) := by
  induction nodes generalizing w v with
  | nil =>
    intro w' v' h_mem
    dsimp [insert_node_sorted] at h_mem ⊢
    rcases h_mem with ⟨rfl, rfl⟩ | h_mem
    · omega
    · exact absurd h_mem (List.not_mem_nil _)
  | cons head tail ih =>
    intro w' v' h_mem
    dsimp [insert_node_sorted] at h_mem ⊢
    split_ifs at h_mem ⊢ with h_cond
    · -- w ≥ head.1: new element inserted at front
      rcases h_mem with ⟨rfl, rfl⟩ | h_mem
      · omega
      · rcases h_mem with ⟨rfl, rfl⟩ | h_mem
        · omega
        · have h_inv_rest : ∀ (w v : Nat), (w, v) ∈ tail → 
            match tail with | [] => True | (top_w, _) :: _ => w ≤ top_w := by
            intros tw tv h_mem_tail
            exact h_inv tw tv (List.Mem.tail head h_mem_tail)
          omega
    · -- w < head.1: recursively insert in tail
      rcases h_mem with ⟨rfl, rfl⟩ | h_mem
      · omega
      · have h_inv_rest : ∀ (w v : Nat), (w, v) ∈ tail → 
          match tail with | [] => True | (top_w, _) :: _ => w ≤ top_w := by
          intros tw tv h_mem_tail
          exact h_inv tw tv (List.Mem.tail head h_mem_tail)
        have ih_result := ih h_inv_rest w v w' v' h_mem
        dsimp [insert_node_sorted] at ih_result
        split_ifs at ih_result with h_cond'
        · omega
        · omega

/-- Main theorem: insert_node_sorted maintains the invariant -/
theorem insert_node_sorted_maintains_invariant (nodes : List (Nat × Nat)) 
    (h_inv : ∀ (w v : Nat), (w, v) ∈ nodes → 
      match nodes with | [] => True | (top_w, _) :: _ => w ≤ top_w) 
    (w v : Nat) :
    ∀ (w' v' : Nat), (w', v') ∈ insert_node_sorted nodes w v → 
      match insert_node_sorted nodes w v with
      | [] => True
      | (top_w, _) :: _ => w' ≤ top_w :=
  insert_node_sorted_invariant_aux nodes h_inv w v

/-- Node injection function with proof -/
def f_space_inject (space : FTopologySpace) (w : Nat) (v : Nat) : FTopologySpace :=
  { nodes := insert_node_sorted space.nodes w v
    invariant := insert_node_sorted_maintains_invariant space.nodes space.invariant w v }

-- =============================================================================
-- 3. Unified Architecture: Space-Time Integrated Machine (F-BSCM)
-- =============================================================================

structure UnifiedMachine where
  current_state : Nat
  state_bounded : current_state ≤ 18446744073709551615
  f_space       : FTopologySpace

def unified_step (m : UnifiedMachine) (external_input : Nat) : UnifiedMachine :=
  let next_s := bscm_control_step m.current_state external_input
  let next_space := f_space_inject m.f_space next_s next_s
  { current_state := next_s
    state_bounded := bscm_control_robust m.current_state external_input
    f_space       := next_space }

-- --- Core Dual-Invariant Theorem ---------------------------------------------

/-- 【不滅性定理：F-BSCM Master Theorem】-/
theorem unified_system_immortal 
    (m_init : UnifiedMachine) (inputs : List Nat) :
    let m_final := inputs.foldl unified_step m_init
    (m_final.current_state ≤ 18446744073709551615) ∧ 
    (∀ (w v : Nat), (w, v) ∈ m_final.f_space.nodes → 
      match m_final.f_space.nodes with
      | [] => True
      | (top_w, _) :: _ => w ≤ top_w) := by
  induction inputs generalizing m_init with
  | nil =>
    simp [List.foldl]
    exact ⟨m_init.state_bounded, m_init.f_space.invariant⟩
  | cons head tail ih =>
    simp [List.foldl]
    have step_result := unified_step m_init head
    have h_bound : step_result.current_state ≤ 18446744073709551615 :=
      step_result.state_bounded
    have h_inv : ∀ (w v : Nat), (w, v) ∈ step_result.f_space.nodes → 
      match step_result.f_space.nodes with
      | [] => True
      | (top_w, _) :: _ => w ≤ top_w :=
      step_result.f_space.invariant
    have ⟨ih_bound, ih_inv⟩ := ih step_result
    exact ⟨ih_bound, ih_inv⟩
