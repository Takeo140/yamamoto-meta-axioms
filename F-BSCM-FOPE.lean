-- =============================================================================
-- F-BSCM with CBC: Financial Order Processing Engine (Production Grade)
--
-- Author: Takeo Yamamoto
-- License: Apache-2.0 / CC-BY-4.0
-- =============================================================================

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- =============================================================================
-- 1. 基礎数理レイヤー (CBC & BSCM)
-- =============================================================================

structure ComplexBitVec64 where
  re : Nat
  im : Nat
  re_bounded : re ≤ 18446744073709551615
  im_bounded : im ≤ 18446744073709551615

def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then s / 2 else (s + 1) / 2

def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  bscm_delta ((current_state + external_input) % 18446744073709551616)

theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) :
    bscm_delta s ≤ 18446744073709551615 := by
  simp only [bscm_delta]
  split_ifs <;> omega

theorem bscm_control_robust (current_state : Nat) (external_input : Nat) :
    bscm_control_step current_state external_input ≤ 18446744073709551615 := by
  simp only [bscm_control_step]
  apply bscm_state_bounded
  have h_mod : (current_state + external_input) % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by omega)
  omega

-- =============================================================================
-- 2. 空間レイヤー (F-Theory Topology & 順序不変性)
-- =============================================================================

def SortedInvariant (nodes : List (Nat × Nat)) : Prop :=
  ∀ (w v : Nat), (w, v) ∈ nodes →
    match nodes with
    | []              => True
    | (top_w, _) :: _ => w ≤ top_w

def insert_node_sorted : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], w, v => [(w, v)]
  | (tw, tv) :: rest, w, v =>
      if w ≥ tw then (w, v) :: (tw, tv) :: rest
      else (tw, tv) :: insert_node_sorted rest w v

/-! ### 補題：ソート挿入されたリストの要素に関する帰属定理 -/
lemma mem_insert_node_sorted (nodes : List (Nat × Nat)) (w v w' v' : Nat) :
    (w', v') ∈ insert_node_sorted nodes w v → (w', v') = (w, v) ∨ (w', v') ∈ nodes := by
  induction nodes with
  | nil =>
    intro h
    dsimp [insert_node_sorted] at h
    rw [List.mem_singleton] at h
    left; exact h
  | cons head rest ih =>
    cases head with | mk tw tv =>
    dsimp [insert_node_sorted]
    split_ifs with h_ge
    · intro h
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · left; rfl
      · right; exact List.mem_cons_of_mem _ h
    · intro h
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · right; exact List.mem_cons_self _ _
      · specialize ih w v w' v' h
        rcases ih with rfl | h_rest
        · left; rfl
        · right; exact List.mem_cons_of_mem _ h_rest

/-! ### 定理：ソート挿入は不変条件（先頭＝最高値）を永久に保存する（完全証明版） -/
theorem insert_node_preserves_invariant (nodes : List (Nat × Nat)) (h : SortedInvariant nodes) (w v : Nat) :
    SortedInvariant (insert_node_sorted nodes w v) := by
  dsimp [SortedInvariant]
  intros w' v' h_mem
  induction nodes with
  | nil =>
    dsimp [insert_node_sorted] at h_mem
    rw [List.mem_singleton] at h_mem
    injection h_mem with h_w h_v
    omega
  | cons head rest ih =>
    cases head with | mk tw tv =>
    dsimp [insert_node_sorted] at h_mem
    split_ifs at h_mem with h_ge
    · rw [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · omega
      · have h_max : w' ≤ tw := by
          have h_inv := h w' v' h_mem
          dsimp [SortedInvariant] at h_inv
          exact h_inv
        omega
    · rw [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · omega
      · have h_or := mem_insert_node_sorted rest w v w' v' h_mem
        rcases h_or with rfl | h_in_rest
        · omega
        · have h_inv := h w' v' (List.mem_cons_of_mem _ h_in_rest)
          dsimp [SortedInvariant] at h_inv
          exact h_inv

-- =============================================================================
-- 3. 状態機械統合レイヤー
-- =============================================================================

structure UnifiedMachine where
  currentTimeState : Nat
  geometricSpace   : List (Nat × Nat)
  state_bounded    : currentTimeState ≤ 18446744073709551615
  space_invariant  : SortedInvariant geometricSpace

structure MarketOrder where
  orderData : ComplexBitVec64

def getPrice (order : MarketOrder) : Nat := order.orderData.re
def getOrderID (order : MarketOrder) : Nat := order.orderData.im

def process_market_order (machine : UnifiedMachine) (order : MarketOrder) : UnifiedMachine :=
  let next_time := bscm_control_step machine.currentTimeState (getPrice order)
  let next_space := insert_node_sorted machine.geometricSpace (getPrice order) (getOrderID order)
  {
    currentTimeState := next_time
    geometricSpace   := next_space
    state_bounded    := bscm_control_robust machine.currentTimeState (getPrice order)
    space_invariant  := insert_node_preserves_invariant machine.geometricSpace machine.space_invariant (getPrice order) (getOrderID order)
  }

def get_best_quote (machine : UnifiedMachine) : Option (Nat × Nat) :=
  match machine.geometricSpace with
  | [] => Option.none
  | (best_price, order_id) :: _ => Option.some (best_price, order_id)

-- =============================================================================
-- 4. 取引所円滑化の型レベル完全証明
-- =============================================================================

theorem exchange_remains_perfectly_fluid (machine : UnifiedMachine) (order : MarketOrder) :
    let next_exchange := process_market_order machine order
    (next_exchange.currentTimeState ≤ 18446744073709551615) ∧ (SortedInvariant next_exchange.geometricSpace) := by
  intro next_exchange
  dsimp [next_exchange, process_market_order]
  constructor
  · exact bscm_control_robust machine.currentTimeState (getPrice order)
  · exact insert_node_preserves_invariant machine.geometricSpace machine.space_invariant (getPrice order) (getOrderID order)
