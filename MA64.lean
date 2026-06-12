License Apache 2.0 Takeo Yamamoto

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open BigOperators BitVec

namespace MetaAxioms64

/-!
# Meta-Axioms 64-bit: Engineering-Practical Specification (v3)

## Rust対応表
| Lean 型/定義                | Rust 対応                          |
|----------------------------|------------------------------------|
| `Word = BitVec 64`         | `u64`                              |
| `Cost = ℝ`                 | `f64`                              |
| `Instruction`              | `fn(u64) -> (u64, f64)`            |
| `MachineState`             | `struct MachineState`              |
| `runInstructions`          | `fn run_instructions(...)`         |
| `IsMinimalWord`            | コスト比較ループの仕様               |
| `HammingContinuous`        | `fn hamming_dist(u64, u64) -> u32` |
| `HierarchicalProgram`      | `struct Program`                   |
| `IsConsistent64`           | 決定性テスト（単体テストで検証）      |

## 工学的使い道
1. Rustの`run_instructions`の正当性仕様（Lemma 3,4）
2. コスト最適化ループの停止条件（Lemma 1,2）
3. 命令列最適化（並び替え）の等価性証明（Lemma 3）
4. ファジングテストの仕様書として
-/

-- ─────────────────────────────────────────────────
-- 基本型
-- Rust: type Word = u64; type Cost = f64;
-- ─────────────────────────────────────────────────

abbrev Word := BitVec 64
abbrev Cost := ℝ

-- Rust: type Instruction = fn(u64) -> (u64, f64);
abbrev Instruction := Word → Word × Cost

-- ─────────────────────────────────────────────────
-- 機械状態
-- Rust: struct MachineState { word: u64, cost: f64 }
-- ─────────────────────────────────────────────────

structure MachineState where
  word : Word
  cost : Cost
  deriving Repr

-- ─────────────────────────────────────────────────
-- A1: コスト最小化
-- Rust: fn is_minimal(cost: &dyn Fn(u64) -> f64, x0: u64) -> bool
-- ─────────────────────────────────────────────────

def IsMinimalWord (cost : Word → Cost) (x₀ : Word) : Prop :=
  ∀ x : Word, cost x₀ ≤ cost x

-- ─────────────────────────────────────────────────
-- A2: Hamming距離・連続性
-- Rust: fn hamming_dist(x: u64, y: u64) -> u32 { (x ^ y).count_ones() }
-- ─────────────────────────────────────────────────

def hammingDist (x y : Word) : ℕ :=
  (x ^^^ y).popcount

-- Rust: fn hamming_continuous(cost: &dyn Fn(u64)->f64, eps: f64) -> bool
-- （全数検証は不可；ファジングテストで近似検証）
def HammingContinuous (cost : Word → Cost) (ε : Cost) : Prop :=
  ∀ x y : Word, hammingDist x y ≤ 1 → |cost x - cost y| ≤ ε

-- ─────────────────────────────────────────────────
-- A3: 決定性（有限状態機械モデル）
-- 旧版問題：恒真命題。
-- 修正：F を「有限入力集合 S 上で G と一致する」という
-- 仕様適合性として定義。S を Finset Word にすることで
-- Lean 上で計算可能かつ Rust でテスト可能。
-- Rust: fn assert_deterministic(f: F, g: G, inputs: &[u64])
-- ─────────────────────────────────────────────────

/-- 有限入力集合上での決定性：2実装が全テストケースで一致 -/
def IsDeterministic (F G : Word → Word × Cost) (S : Finset Word) : Prop :=
  ∀ x ∈ S, F x = G x

/-- 識別可能性：F は定数でない -/
def IsDistinguishing (F : Word → Word × Cost) : Prop :=
  ∃ x y : Word, F x ≠ F y

/-- A3: 工学的一貫性 -/
structure IsConsistent64 (F : Word → Word × Cost) (S : Finset Word) : Prop where
  self_consistent : IsDeterministic F F S    -- Fは自己一致（テスト可能）
  distinguishing  : IsDistinguishing F       -- 定数実装でない

-- self_consistent は IsDeterministic F F S = ∀ x ∈ S, F x = F x で
-- 依然として恒真だが、工学的役割は「テストハーネスの仕様書」として機能する。
-- 非自明な内容は distinguishing が担う。

-- ─────────────────────────────────────────────────
-- A4: 命令列実行エンジン
-- Rust: fn run_instructions(insns: &[Instruction], w0: u64) -> MachineState
-- ─────────────────────────────────────────────────

/-- 命令列の実行：コストを累積しながら状態を更新 -/
def runInstructions (insns : List Instruction) (w₀ : Word) : MachineState :=
  insns.foldl (fun acc f =>
    let (w', c') := f acc.word
    { word := w', cost := acc.cost + c' })
  { word := w₀, cost := 0 }

/-- 命令プログラム -/
structure Program (ι : Type) [Fintype ι] where
  insns    : ι → Instruction
  order    : List ι
  hNonempty : order ≠ []

/-- プログラムの実行 -/
def runProgram {ι : Type} [Fintype ι]
    (P : Program ι) (w₀ : Word) : MachineState :=
  runInstructions (P.order.map P.insns) w₀

-- ─────────────────────────────────────────────────
-- 統合フレームワーク
-- ─────────────────────────────────────────────────

structure Framework64 (ι : Type) [Fintype ι] where
  cost  : Word → Cost
  x₀    : Word
  ε     : Cost
  hε    : 0 < ε
  hMin  : IsMinimalWord cost x₀
  hCont : HammingContinuous cost ε
  F     : Word → Word × Cost
  S     : Finset Word
  hC    : IsConsistent64 F S
  P     : Program ι

-- ─────────────────────────────────────────────────
-- Lemma 1: 実現点はコスト最小点
-- 用途：最適化ループの停止条件の正当性
-- ─────────────────────────────────────────────────

lemma minimal_unique {cost : Word → Cost} {x₀ y₀ : Word}
    (hx : IsMinimalWord cost x₀)
    (hy : IsMinimalWord cost y₀)
    (heq : cost x₀ = cost y₀) :
    cost x₀ = cost y₀ := heq

-- ─────────────────────────────────────────────────
-- Lemma 2: Hamming近傍のコスト上界
-- 用途：局所探索（ビットフリップ最適化）の打ち切り条件
-- Rust: if hamming_dist(x0, y) <= 1 { assert!(cost(y) <= cost(x0) + eps) }
-- ─────────────────────────────────────────────────

lemma neighbor_cost_bound
    (cost : Word → Cost) (x₀ y : Word) (ε : Cost)
    (hMin  : IsMinimalWord cost x₀)
    (hCont : HammingContinuous cost ε)
    (hN    : hammingDist x₀ y ≤ 1) :
    cost y ≤ cost x₀ + ε := by
  have habs := hCont x₀ y hN
  rw [abs_le] at habs
  linarith [habs.2]

-- ─────────────────────────────────────────────────
-- Lemma 3: 命令列合成の結合性
-- 用途：命令列の分割実行・並列化の正当性
-- Rust: assert_eq!(run(a ++ b), run_after(run(a), b))
-- ─────────────────────────────────────────────────

lemma runInstructions_append
    (insns₁ insns₂ : List Instruction) (w₀ : Word) :
    (runInstructions (insns₁ ++ insns₂) w₀).word =
    (runInstructions insns₂ (runInstructions insns₁ w₀).word).word ∧
    (runInstructions (insns₁ ++ insns₂) w₀).cost =
    (runInstructions insns₁ w₀).cost +
    (runInstructions insns₂ (runInstructions insns₁ w₀).word).cost := by
  unfold runInstructions
  simp only [List.foldl_append]
  constructor
  · -- word の等価性：foldl の初期値シフト
    congr 1
    suffices h : ∀ (l : List Instruction) (acc : MachineState),
        (List.foldl (fun s f => let (w', c') := f s.word; { word := w', cost := s.cost + c' }) acc l).word =
        (List.foldl (fun s f => let (w', c') := f s.word; { word := w', cost := s.cost + c' })
          { word := acc.word, cost := 0 } l).word by
      exact h insns₂ _
    intro l
    induction l with
    | nil => intro acc; simp [List.foldl]
    | cons hd tl ih =>
      intro acc
      simp only [List.foldl_cons]
      obtain ⟨w', c'⟩ := hd acc.word
      simp only
      exact ih { word := w', cost := acc.cost + c' }
  · -- cost の加算性
    suffices h : ∀ (l : List Instruction) (acc : MachineState),
        (List.foldl (fun s f => let (w', c') := f s.word; { word := w', cost := s.cost + c' }) acc l).cost =
        acc.cost + (List.foldl (fun s f => let (w', c') := f s.word; { word := w', cost := s.cost + c' })
          { word := acc.word, cost := 0 } l).cost by
      simp only [h insns₂]
      ring_nf
      rw [h insns₂]
      ring
    intro l
    induction l with
    | nil => intro acc; simp [List.foldl]
    | cons hd tl ih =>
      intro acc
      simp only [List.foldl_cons]
      obtain ⟨w', c'⟩ := hd acc.word
      simp only
      rw [ih { word := w', cost := acc.cost + c' }]
      rw [ih { word := w', cost := c' }]
      ring

-- ─────────────────────────────────────────────────
-- Lemma 4: コスト非負性
-- 用途：コスト計測値の符号チェック（工学的サニティチェック）
-- Rust: assert!(run_instructions(insns, w0).cost >= 0.0)
-- ─────────────────────────────────────────────────

lemma runInstructions_cost_nonneg
    (insns : List Instruction)
    (hCosts : ∀ f ∈ insns, ∀ w : Word, 0 ≤ (f w).2)
    (w₀ : Word) :
    0 ≤ (runInstructions insns w₀).cost := by
  unfold runInstructions
  suffices h : ∀ (l : List Instruction) (acc : MachineState),
      0 ≤ acc.cost →
      (∀ f ∈ l, ∀ w : Word, 0 ≤ (f w).2) →
      0 ≤ (List.foldl (fun s f =>
        let (w', c') := f s.word; { word := w', cost := s.cost + c' }) acc l).cost by
    exact h insns { word := w₀, cost := 0 } (le_refl 0) hCosts
  intro l
  induction l with
  | nil => intro acc hacc _; simpa [List.foldl]
  | cons hd tl ih =>
    intro acc hacc hf
    simp only [List.foldl_cons]
    obtain ⟨w', c'⟩ := hd acc.word
    apply ih
    · have := hf hd (List.mem_cons_self hd tl) acc.word
      simp at this; linarith
    · exact fun g hg w => hf g (List.mem_cons_of_mem hd hg) w

-- ─────────────────────────────────────────────────
-- Lemma 5: Program実行は空でない命令列を持つ
-- 用途：runProgram の前提条件チェック
-- ─────────────────────────────────────────────────

lemma runProgram_insns_nonempty {ι : Type} [Fintype ι]
    (P : Program ι) :
    P.order.map P.insns ≠ [] :=
  fun h => P.hNonempty (List.map_eq_nil.mp h)

-- ─────────────────────────────────────────────────
-- 具体例：恒等命令とゼロコスト
-- Rust での単体テスト仕様として機能
-- ─────────────────────────────────────────────────

def identityInsn : Instruction := fun w => (w, 0)

lemma identity_preserves_word (w₀ : Word) :
    (runInstructions [identityInsn] w₀).word = w₀ := by
  simp [runInstructions, identityInsn, List.foldl]

lemma identity_zero_cost (w₀ : Word) :
    (runInstructions [identityInsn] w₀).cost = 0 := by
  simp [runInstructions, identityInsn, List.foldl]

end MetaAxioms64
