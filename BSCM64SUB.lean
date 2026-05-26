import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Theory of Bounded Smooth Collatz Machine (BSCM) - 64-bit Control Theory Version
# Formalization of Robust Control and Boundedness on Finite-State Automata
# Fully Formalized Version — Absolutely No Axioms, No Sorry

Author: Takeo Yamamoto
License: Apache 2.0
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- 1. 計算機コア・モデル：状態空間と遷移関数の定義（完全無変更）
-- ─────────────────────────────────────────────────────────────────────────────

/-- 
  【64ビット版 BSCMの遷移関数 δ】
  状態空間 S を 64ビット（0 ≤ s ≤ 18446744073709551615）の有限集合として定義。
  純粋なビット操作のみで構成される決定論的コア。
-/
def bscm_delta (s : Nat) : Nat :=
  if s % 2 = 0 then
    s / 2                  -- 状態縮小（1ビット右シフト）
  else if s % 4 = 1 then
    (s - 1) / 2            -- 状態縮小（奇数ビットシフト）
  else
    18446744073709551615 - (s % 18446744073709551616) -- 状態攪乱（完全ビット反転）

-- ─────────────────────────────────────────────────────────────────────────────
-- 2. 汎用制御インターフェースの追加（物理入力・外乱の統合）
-- ─────────────────────────────────────────────────────────────────────────────

/--
  【汎用制御ステップ関数】
  現実の制御系（チップ等）に合わせ、外部からの爆発的な外乱（入力）を受け付けるラッパー。
  入力がどれほど巨大であっても、剰余演算によって瞬時に64ビット空間へ折りたたむ（衝撃吸収）。
-/
def bscm_control_step (current_state : Nat) (external_input : Nat) : Nat :=
  let s_prime := (current_state + external_input) % 18446744073709551616
  bscm_delta s_prime

/-- 外部入力の時系列（List）をクロック順に受け取って状態を順次更新していく制御トレース関数 -/
def bscm_control_exec (initial_state : Nat) : List Nat → Nat
  | [] => initial_state
  | input :: inputs => bscm_control_exec (bscm_control_step initial_state input) inputs

-- ─────────────────────────────────────────────────────────────────────────────
-- 3. 制御理論コア定理：絶対的堅牢性（大域的有界性の完全証明）
-- ─────────────────────────────────────────────────────────────────────────────

/-- コア単体における空間不変性定理（既存の証明を維持） -/
theorem bscm_state_bounded (s : Nat) (h : s ≤ 18446744073709551615) : bscm_delta s ≤ 18446744073709551615 := by
  dsimp [bscm_delta]
  split_ifs with h1 h2
  · omega
  · omega
  · omega

/--
  【BSCM 汎用制御ロバスト性定理】
  現在の状態がどうあろうと、また外部からどんな爆発的な入力（外乱）が飛び込んでこようとも、
  次のステップの状態は「絶対に」64ビットの上限を突破しないことの完全証明。
-/
theorem bscm_control_robust (current_state : Nat) (external_input : Nat) :
    bscm_control_step current_state external_input ≤ 18446744073709551615 := by
  dsimp [bscm_control_step]
  have h_prime : (current_state + external_input) % 18446744073709551616 ≤ 18446744073709551615 := by
    omega
  exact bscm_state_bounded ((current_state + external_input) % 18446744073709551616) h_prime

/-- 
  【大域的システム安全不変性定理】
  初期状態がどれほど異常な値（例：64ビット超過）であっても、またいかなる外乱時系列が注入されようとも、
  少なくとも1ステップ以上の制御介入（List が空でない）があれば、システムは永久に安全圏に拘束されることの帰納的証明。
-/
theorem bscm_system_never_overflows (initial_state : Nat) (input : Nat) (inputs : List Nat) :
    bscm_control_exec (bscm_control_step initial_state input) inputs ≤ 18446744073709551615 := by
  induction' inputs with head tail ih generalizing initial_state input
  · dsimp [bscm_control_exec]
    exact bscm_control_robust initial_state input
  · dsimp [bscm_control_exec]
    -- タイムステップが進んでも、前のステップの有界性を引き継いで omega と ih が自動解決
    exact ih (bscm_control_step initial_state input) head
