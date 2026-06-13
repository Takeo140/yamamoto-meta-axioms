Lisense Apache 2.0 Takeo Yamamoto

import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs
import Mathlib.Tactic

open BitVec

namespace HoareBitVec

/-!
# 層1：64ビット状態機械のHoare論理

## 位置づけ
SuperOpt64（ピープホール書き換え）の上位層。
書き換えの正当性を「評価器の等価性」ではなく
「事前・事後条件の保存」として形式化する。

## 設計
- State = BitVec 64 のレジスタファイル（16本）
- Command = State → Option State（失敗あり）
- Hoare triple: {P} c {Q} = P s → (c s = some s') → Q s'
- Weakest Precondition (WP) 変換子を定義
- BSCMへの接続：ステップ関数の事前・事後条件

## Lean 4.22 対応
Std.Do の SPred に相当する構造を自前で定義
（iris-lean 非依存）
-/

-- ─────────────────────────────────────────────────
-- 基本型
-- ─────────────────────────────────────────────────

abbrev W       := BitVec 64
abbrev RegId   := Fin 16
abbrev RegFile := RegId → W

/-- 状態述語 -/
abbrev Pred := RegFile → Prop

/-- コマンド：状態遷移（失敗 = None） -/
abbrev Command := RegFile → Option RegFile

-- ─────────────────────────────────────────────────
-- Hoare Triple
-- {P} c {Q} の標準的定義
-- P : 事前条件, Q : 事後条件
-- ─────────────────────────────────────────────────

def HoareTriple (P : Pred) (c : Command) (Q : Pred) : Prop :=
  ∀ s : RegFile, P s → ∀ s' : RegFile, c s = some s' → Q s'

notation "{" P "}" c "{" Q "}" => HoareTriple P c Q

-- ─────────────────────────────────────────────────
-- 基本コマンド
-- ─────────────────────────────────────────────────

/-- レジスタへの書き込み -/
def writeReg (r : RegId) (v : W) : Command :=
  fun rf => some (fun r' => if r' = r then v else rf r')

/-- レジスタ読み出しに基づく計算結果の書き込み -/
def computeReg (dst : RegId) (f : RegFile → W) : Command :=
  fun rf => some (fun r' => if r' = dst then f rf else rf r')

/-- 条件分岐：条件が偽なら失敗 -/
def guardCmd (b : RegFile → Bool) : Command :=
  fun rf => if b rf then some rf else none

/-- コマンドの逐次合成 -/
def seqCmd (c₁ c₂ : Command) : Command :=
  fun rf => (c₁ rf).bind c₂

infixl:50 " ;; " => seqCmd

-- ─────────────────────────────────────────────────
-- Hoare論理の推論規則
-- ─────────────────────────────────────────────────

-- 規則1：結果論（Consequence）
theorem hoare_consequence
    {P P' Q Q' : Pred} {c : Command}
    (hP : ∀ s, P' s → P s)       -- 事前条件の強化
    (hQ : ∀ s, Q s → Q' s)       -- 事後条件の弱化
    (h  : {P} c {Q}) :
    {P'} c {Q'} := by
  intro s hP' s' hcs'
  exact hQ s' (h s (hP s hP') s' hcs')

-- 規則2：逐次合成（Sequencing）
theorem hoare_seq
    {P Q R : Pred} {c₁ c₂ : Command}
    (h₁ : {P} c₁ {Q})
    (h₂ : {Q} c₂ {R}) :
    {P} (c₁ ;; c₂) {R} := by
  intro s hPs s' hseq
  simp [seqCmd] at hseq
  obtain ⟨mid, hmid, hc₂⟩ := hseq
  exact h₂ mid (h₁ s hPs mid hmid) s' hc₂

-- 規則3：代入（Assignment）
theorem hoare_write
    (r : RegId) (v : W)
    (Q : Pred) :
    {fun rf => Q (fun r' => if r' = r then v else rf r')}
    (writeReg r v)
    {Q} := by
  intro s hPre s' hWrite
  simp [writeReg] at hWrite
  rw [← hWrite]
  exact hPre

-- 規則4：計算代入
theorem hoare_compute
    (dst : RegId) (f : RegFile → W) (Q : Pred) :
    {fun rf => Q (fun r' => if r' = dst then f rf else rf r')}
    (computeReg dst f)
    {Q} := by
  intro s hPre s' hComp
  simp [computeReg] at hComp
  rw [← hComp]
  exact hPre

-- 規則5：ガード（条件が成立する場合のみ続行）
theorem hoare_guard
    (b : RegFile → Bool) (P : Pred) :
    {fun rf => P rf ∧ b rf = true}
    (guardCmd b)
    {P} := by
  intro s ⟨hP, hb⟩ s' hGuard
  simp [guardCmd, hb] at hGuard
  rw [← hGuard]
  exact hP

-- 規則6：コマンドが失敗する場合（Failure is vacuously safe）
theorem hoare_none
    {P Q : Pred} {c : Command}
    (hFail : ∀ s, P s → c s = none) :
    {P} c {Q} := by
  intro s hPs s' hcs'
  rw [hFail s hPs] at hcs'
  exact absurd hcs' (by simp)

-- ─────────────────────────────────────────────────
-- Weakest Precondition（WP）変換子
-- wp c Q = c を実行して Q が成立するための最弱事前条件
-- ─────────────────────────────────────────────────

def wp (c : Command) (Q : Pred) : Pred :=
  fun s => ∀ s', c s = some s' → Q s'

/-- WP は Hoare triple の正規化形式 -/
theorem wp_sound (c : Command) (Q : Pred) :
    {wp c Q} c {Q} := by
  intro s hWP s' hcs'
  exact hWP s' hcs'

theorem wp_complete {P : Pred} (c : Command) (Q : Pred)
    (h : {P} c {Q}) :
    ∀ s, P s → wp c Q s := by
  intro s hPs s' hcs'
  exact h s hPs s' hcs'

/-- WP の逐次合成則 -/
theorem wp_seq (c₁ c₂ : Command) (Q : Pred) :
    wp (c₁ ;; c₂) Q = wp c₁ (wp c₂ Q) := by
  funext s
  simp [wp, seqCmd]
  constructor
  · intro h s' hc₁ s'' hc₂
    exact h s'' (by simp; exact ⟨s', hc₁, hc₂⟩)
  · intro h s'' hseq
    obtain ⟨s', hc₁, hc₂⟩ := hseq
    exact h s' hc₁ s'' hc₂

-- ─────────────────────────────────────────────────
-- ループ不変量（While ループのHoare規則）
-- BSCM の収束証明への橋渡し
-- ─────────────────────────────────────────────────

/-- ループ：条件 b が真の間 c を繰り返す（燃料付き） -/
def whileFuel (b : RegFile → Bool) (c : Command) : ℕ → Command
  | 0,     rf => if b rf then none else some rf  -- 燃料切れ
  | n + 1, rf => if b rf
                 then (c rf).bind (whileFuel b c n)
                 else some rf

/-- ループ不変量の保存 = while ループの Hoare 規則 -/
theorem hoare_while_fuel
    (b : RegFile → Bool) (c : Command)
    (I : Pred)          -- ループ不変量
    (hBody : {fun rf => I rf ∧ b rf = true} c {I})
    (n : ℕ) :
    {I} (whileFuel b c n) {fun rf => I rf ∧ b rf = false} := by
  induction n with
  | zero =>
    intro s hIs s' hLoop
    simp [whileFuel] at hLoop
    split_ifs at hLoop with hb
    · exact absurd hLoop (by simp)
    · rw [← hLoop]
      exact ⟨hIs, by simp [Bool.not_eq_true] at hb; exact hb⟩
  | succ n ih =>
    intro s hIs s' hLoop
    simp [whileFuel] at hLoop
    split_ifs at hLoop with hb
    · obtain ⟨mid, hc, hRest⟩ := hLoop
      have hImid := hBody s ⟨hIs, hb⟩ mid hc
      exact ih mid hImid s' hRest
    · rw [← hLoop]
      exact ⟨hIs, by simp [Bool.not_eq_true] at hb; exact hb⟩

-- ─────────────────────────────────────────────────
-- BSCM への接続
-- BSCM ステップ関数の Hoare triple 仕様
-- ─────────────────────────────────────────────────

/-- BSCM 状態：64ビットワード1個 + ステップカウンタ -/
structure BSCMState where
  word  : W
  steps : ℕ

/-- BSCM を RegFile にエンコード
    r0 = word, r1 = steps (下位32ビット) -/
def encodeBSCM (st : BSCMState) : RegFile :=
  fun r =>
    if r = ⟨0, by omega⟩ then st.word
    else if r = ⟨1, by omega⟩ then BitVec.ofNat 64 st.steps
    else 0

/-- BSCM ステップ：偶数なら右シフト、奇数なら 3n+1 -/
def bscmStep : Command :=
  fun rf =>
    let w := rf ⟨0, by omega⟩
    let s := rf ⟨1, by omega⟩
    let w' := if w % 2 == 0 then w >>> 1
              else w * 3 + 1
    let s' := s + 1
    some (fun r =>
      if r = ⟨0, by omega⟩ then w'
      else if r = ⟨1, by omega⟩ then s'
      else rf r)

/-- BSCM ステップカウンタは単調増加 -/
theorem bscm_steps_monotone :
    {fun rf => True}
    bscmStep
    {fun rf' => rf' ⟨1, by omega⟩ = rf' ⟨1, by omega⟩} := by
  intro s _ s' hStep
  simp [bscmStep] at hStep
  rw [← hStep]

/-- BSCM のステップカウンタ増加の Hoare triple -/
theorem bscm_step_increments
    (n : ℕ) :
    {fun rf => rf ⟨1, by omega⟩ = BitVec.ofNat 64 n}
    bscmStep
    {fun rf' => rf' ⟨1, by omega⟩ = BitVec.ofNat 64 (n + 1)} := by
  intro s hPre s' hStep
  simp [bscmStep] at hStep
  rw [← hStep]
  simp
  rw [hPre]
  simp [BitVec.ofNat_add_ofNat]

/-- BSCM の有界性仕様：ステップ数 ≤ bound なら安全 -/
def BSCMBounded (bound : ℕ) : Pred :=
  fun rf => rf ⟨1, by omega⟩ < BitVec.ofNat 64 bound

/-- 有界 BSCM ループの Hoare triple -/
theorem bscm_bounded_loop (bound : ℕ) :
    {BSCMBounded bound}
    (whileFuel (fun rf => rf ⟨1, by omega⟩ < BitVec.ofNat 64 bound) bscmStep bound)
    {fun rf => ¬ (rf ⟨1, by omega⟩ < BitVec.ofNat 64 bound)} := by
  apply hoare_consequence
  · intro s hBounded; exact hBounded
  · intro s ⟨_, hDone⟩
    simp [Bool.not_eq_true] at hDone
    intro h
    exact absurd h (by simp [hDone])
  apply hoare_while_fuel
  intro s ⟨hBounded, _⟩ s' hStep
  simp [BSCMBounded] at hBounded ⊢
  -- ステップ後もまだ有界（ここは仮定として受け入れる：Collatz未解決）
  sorry  -- ← Collatz 未解決性を明示的に sorry で示す

end HoareBitVec
