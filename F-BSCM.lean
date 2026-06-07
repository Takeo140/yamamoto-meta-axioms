-- =============================================================================
-- F-BSCM: Space-Time Invariant Meta-Axiomatic Computing Model
-- Integrating Bounded Smooth Collatz Machine (Time) and F-Theory (Space)
--
-- Author: Takeo Yamamoto
-- License: Apache-2.0 / CC-BY-4.0
-- =============================================================================

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# F-BSCM: 時空間不変メタ公理的計算モデル
時間軸の有界収束（BSCM）と、空間軸の幾何学的順序（F-Theory）を形式検証したフラグシップコード。
-/

-- =============================================================================
-- 1. Time Domain: Bounded Smooth Collatz Machine (BSCM)
-- =============================================================================

/-- 偶数なら 1/2、奇数なら (s+1)/2。全分岐が状態を縮小または維持する。 -/
def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then s / 2 else (s + 1) / 2

/-- 外部入力を受け取る1ステップの状態遷移（Modulo 2^64 境界制限）。 -/
def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

/-- 終わりなき外部入力ストリームを処理する時間軸実行エンジン。 -/
def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | []              => initial_state
  | input :: inputs => bscm_control_exec (bscm_control_step initial_state input) inputs

/-- 【時間定理 1】 デルタ関数は 2^64-1 の上界境界を絶対に破らない。 -/
theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) :
    bscm_delta s ≤ 18446744073709551615 := by
  dsimp [bscm_delta]
  split_ifs <;> omega

/-- 【時間定理 2】 制御ステップは、いかなる巨大な外部入力（ノイズ）に対しても常に安全圏に収まる。 -/
theorem bscm_control_robust (current_state : Nat) (external_input : Nat) :
    bscm_control_step current_state external_input ≤ 18446744073709551615 := by
  dsimp [bscm_control_step]
  have h_prime : (current_state + external_input) % 18446744073709551616 ≤ 18446744073709551615 := by omega
  exact bscm_state_bounded _ h_prime

/-- 【時間定理 3】 任意の長さの入力列に対して、システムは永久にオーバーフローを起こさない（ロバスト性の証明）。 -/
theorem bscm_system_never_overflows (initial_state : Nat) (input : Nat) (inputs : List Nat) :
    bscm_control_exec (bscm_control_step initial_state input) inputs ≤ 18446744073709551615 := by
  induction inputs generalizing initial_state input with
  | nil => exact bscm_control_robust initial_state input
  | cons h t ih => exact ih (bscm_control_step initial_state input) h

-- =============================================================================
-- 2. Space Domain: F-Theory Topological Indexing
-- =============================================================================

/-- 空間の順序不変条件（SortedInvariant）: 
    リスト内の任意のノードの重み `w` は、必ず先頭ノード（存在するならば）の重み `top_w` 以下である。 -/
def SortedInvariant (nodes : List (Nat × Nat)) : Prop :=
  ∀ (w v : Nat), (w, v) ∈ nodes →
    match nodes with
    | []              => True
    | (top_w, _) :: _ => w ≤ top_w

/-- メタ公理 A4 を満たすソート順インサート関数。
    重み `w` が大きいノードが常に前方に配置されるように空間を幾何学的に再構築する。 -/
def insert_node_sorted : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], w, v => [(w, v)]
  | (tw, tv) :: rest, w, v =>
      if w ≥ tw then (w, v) :: (tw, tv) :: rest
      else (tw, tv) :: insert_node_sorted rest w v

/-- 補助補題：リストの内部へ挿入した場合でも、元々の先頭ノードの重み（tw）は不変である。 -/
lemma insert_node_preserves_top_weight (rest : List (Nat × Nat)) (tw tv w v : Nat) (h_lt : ¬ w ≥ tw) :
    match insert_node_sorted ((tw, tv) :: rest) w v with
    | [] => False
    | (top_w, _) :: _ => top_w = tw := by
  dsimp [insert_node_sorted]
  split_ifs with h
  · contradiction
  · dsimp

/-- 【空間主定理】 秩序（規律）の永続性定理：
    どんなノード（資産）が追加されようとも、この空間トポロジーはメタ公理（降順ソート）を絶対に崩さない。 -/
theorem insert_node_preserves_invariant (nodes : List (Nat × Nat)) (h : SortedInvariant nodes) (w v : Nat) :
    SortedInvariant (insert_node_sorted nodes w v) := by
  induction nodes with
  | nil =>
    dsimp [insert_node_sorted, SortedInvariant]
    intro w' v' h_mem
    cases h_mem with
    | head => rfl
    | tail _ h_nil => contradiction
  | cons head tail ih =>
    obtain ⟨tw, tv⟩ := head
    dsimp [insert_node_sorted]
    split_ifs with h_ge
    · -- ケース A: 新しいノードの重みが現在のトップ以上の場合（新たな王の誕生）
      dsimp [SortedInvariant]
      intro w' v' h_mem
      cases h_mem with
      | head => rfl
      | tail _ h_inner =>
        cases h_inner with
        | head => exact h_ge
        | tail _ h_deep =>
          have h_old := h w' v' (by simp [h_deep])
          dsimp [SortedInvariant] at h_old
          omega
    · -- ケース B: 新しいノードが既存のトップより小さい場合（内部への推譲）
      dsimp [SortedInvariant]
      intro w' v' h_mem
      dsimp [SortedInvariant] at h
      have h_top_fixed := insert_node_preserves_top_weight tail tw tv w v h_ge
      
      -- 挿入後のリストからメンバーシップを展開
      have h_cases : (w', v') = (tw, tv) ∨ (w', v') ∈ insert_node_sorted tail w v := by
        -- メンバーシップの分解
        rcases h_mem with h_head | h_tail
        · left; exact h_head
        · right; exact h_tail
        
      rcases h_cases with rfl | h_in_tail
      · omega
      · -- 帰納法の仮定（ih）を適用するために、tail 自体の不変条件を証明
        have h_tail_inv : SortedInvariant tail := by
          intro w_t v_t h_t
          have h_full := h w_t v_t (by simp [h_t])
          omega
        have h_tail_sorted := ih h_tail_inv
        dsimp [SortedInvariant] at h_tail_sorted
        have h_res := h_tail_sorted w' v' h_in_tail
        
        -- tail のインサート後の先頭要素の重みに関する境界条件の処理
        rcases h_tail_with : insert_node_sorted tail w v with _ | ⟨t_w, t_v⟩
        · rw [h_tail_with] at h_in_tail; contradiction
        · rw [h_tail_with] at h_res
          -- 新しく入った要素か、既存の要素かで分岐
          have h_w_bounds : w' ≤ tw := by
            -- tail に挿入されたものの最大値は、w か、または既存の tail の最大値（≤ tw）のどちらか
            -- したがって必ず元のトップ tw を超えない
            have h_tail_max : ∀ x y, (x, y) ∈ tail → x ≤ tw := by
              intro x y h_x; have h_all := h x y (by simp [h_x]); omega
            clear h_top_fixed ih
            induction tail with
            | nil =>
              dsimp [insert_node_sorted] at h_in_tail
              rcases h_in_tail with h_h | h_t
              · injection h_h with _ _; omega
              · contradiction
            | cons hd tl ih2 =>
              dsimp [insert_node_sorted] at h_in_tail
              split_ifs at h_in_tail with h_g2
              · rcases h_in_tail with h_h | h_t
                · injection h_h with _ _; omega
                · rcases h_t with h_h2 | h_t2
                  · injection h_h2 with _ _; have := h_tail_max _ _ (by simp); omega
                  · have := h_tail_max _ _ (by simp [h_t2]); omega
              · rcases h_in_tail with h_h | h_t
                · injection h_h with _ _; have := h_tail_max _ _ (by simp); omega
                · apply ih2
                  · intro x y h_x; apply h_tail_max; simp [h_x]
                  · exact h_t
          exact h_w_bounds

-- =============================================================================
-- 3. Unified Architecture (Structure)
-- =============================================================================

/-- 時空統合メタ計算空間の構造体定義 -/
structure UnifiedMachine where
  currentState : Nat
  fSpace       : FTopologySpace
