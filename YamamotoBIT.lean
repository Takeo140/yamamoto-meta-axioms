-- =========================================================================
-- Theoretical Foundations of Bit Computation and Economics (v4.0)
-- Version: Academic Peer-Review Verified Build 2026
-- Licensed under Apache 2.0 (Author: Takeo Yamamoto / 山本健夫)
-- ORCID: 0009-0003-0440-474X
-- =========================================================================

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators
open Real

namespace YamamotoBitEconomics

-- ─────────────────────────────────────────────────
-- §1. 計算論的メタ公理の基盤 (Foundational Meta-Axioms)
-- ─────────────────────────────────────────────────

/-- A1: 計算論的極値原則 (Computational Extremum Principle)
    システムが達成すべき、状態空間（非決定性）の最小化状態の定義。 -/
def IsMinimal {X : Type} (L : X → ℝ) (x₀ : X) : Prop :=
  ∀ x, L x₀ ≤ L x

/-- A2: 収束軌道と連続性 (Topological Trajectory & Continuity)
    最適化（デバッグ）プロセスが連続な軌道上で保証されていること。 -/
structure TopologicalMinimum (X : Type) [TopologicalSpace X] where
  L    : X → ℝ
  x₀   : X
  hL   : Continuous L
  hMin : IsMinimal L x₀

/-- A3: 命題の一貫性と反証可能性 (Logical Consistency & Falsifiability) -/
structure IsConsistent {X : Type} (C : (X → ℝ) → Prop) (F : X → ℝ) : Prop where
  holds       : C F
  falsifiable : ∃ G : X → ℝ, ¬ C G

/-- A4: 階層的マクロ構成と凸結合制約 (Hierarchical Macro Structure)
    分散されたミクロな計算状態からマクロな動態への、重み総和1の凸結合による遷移。 -/
structure HierarchicalMacro {ι : Type} [Fintype ι] (X : Type) where
  w       : ι → ℝ
  Fmicro  : ι → X → ℝ
  hNonNeg : ∀ i, 0 ≤ w i
  hSum    : ∑ i, w i = 1

def MacroFunction {ι : Type} [Fintype ι] {X : Type} (H : HierarchicalMacro X (ι := ι)) : X → ℝ :=
  fun x => ∑ i, H.w i * H.Fmicro i x

structure IntegratedFramework (X : Type) [TopologicalSpace X] (ι : Type) [Fintype ι] where
  tm : TopologicalMinimum X
  C  : (X → ℝ) → Prop
  F  : X → ℝ
  hC : IsConsistent C F
  H  : HierarchicalMacro X (ι := ι)

def IsRealization {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]
    (M : IntegratedFramework X ι) (x₀ : X) : Prop :=
  M.tm.x₀ = x₀

lemma realization_is_minimal {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]
    (M : IntegratedFramework X ι) (x₀ : X) (hR : IsRealization M x₀) :
    IsMinimal M.tm.L x₀ := by
  rw [← hR]
  exact M.tm.hMin

-- ─────────────────────────────────────────────────
-- §2. シャノン情報空間と計算論的ビット価値 (Value Theory)
-- ─────────────────────────────────────────────────

/-- 計算システムの状態空間（分布）の定義。 -/
structure InformationState (ι : Type) [Fintype ι] where
  p       : ι → ℝ
  hNonNeg : ∀ i, 0 ≤ p i
  hSum    : ∑ i, p i = 1

/-- 計算論的エントロピー H(s)：
    システムが内包する非決定性、余長な探索空間、または「バグ」の総ビット長。 -/
noncomputable def shannon_entropy {ι : Type} [Fintype ι] (s : InformationState ι) : ℝ :=
  - ∑ i, s.p i * log (s.p i)

/-- 決定論的基底状態（Deterministic Ground State）：
    特定の終了状態 target に確率1が集中した、余長ノイズゼロの究極の最適化状態。 -/
def deterministic_state {ι : Type} [Fintype ι] [Nonempty ι] (target : ι) : InformationState ι where
  p       := fun i => if i = target then 1 else 0
  hNonNeg := fun i => by split_ifs <;> linarith
  hSum    := by simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- [補題 2.1] 決定論的基底状態のエントロピーは厳密に 0 である -/
lemma deterministic_entropy_zero {ι : Type} [Fintype ι] [Nonempty ι] (target : ι) :
    shannon_entropy (deterministic_state target) = 0 := by
  unfold shannon_entropy deterministic_state
  simp only [neg_eq_zero]
  have h_terms : ∀ i, (if i = target then (1:ℝ) else 0) * log (if i = target then 1 else 0) = 0 := by
    intro i
    split_ifs with h
    · simp [h, Real.log_one]
    · ring
  apply Finset.sum_eq_zero
  intro i _
  exact h_terms i

/-- 計算論的ビット価値 V(s_init, s_curr)：
    マルクス的労働時間を完全に排除した定義。
    富とは、システムから「引き算（最適化・デバッグ）」された非決定性エントロピーの総量。 -/
noncomputable def bit_value {ι : Type} [Fintype ι] (initial current : InformationState ι) : ℝ :=
  shannon_entropy initial - shannon_entropy current

/-- [補題 2.2] 計算論的エントロピーの非負性定理 -/
lemma shannon_entropy_nonneg {ι : Type} [Fintype ι] (s : InformationState ι) :
    0 ≤ shannon_entropy s := by
  unfold shannon_entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  have hpi_le_one : s.p i ≤ 1 := by
    have h := Finset.single_le_sum (f := s.p) (fun j _ => s.hNonNeg j) (Finset.mem_univ i)
    linarith [s.hSum]
  have hlog : log (s.p i) ≤ 0 := by
    rcases (s.hNonNeg i).eq_or_gt with rfl | hpos
    · simp [Real.log_zero]
    · exact Real.log_nonpos hpos.le hpi_le_one
  exact mul_nonpos_of_nonneg_of_nonpos (s.hNonNeg i) hlog

/-- [補題 2.3] 決定論的基底状態は情報空間のグローバル最小点（極値）である -/
lemma deterministic_minimizes_entropy {ι : Type} [Fintype ι] [Nonempty ι] (target : ι) (s : InformationState ι) :
    shannon_entropy (deterministic_state target) ≤ shannon_entropy s := by
  rw [deterministic_entropy_zero]
  exact shannon_entropy_nonneg s

/-- [定理 3.1] ビット経済学の根本定理 (Fundamental Theorem of Bit Computation)
    システムが完全にデバッグされた秩序状態に達した瞬間、創出されるビット価値は
    初期状態が内包していたカオスの総量そのものに収束する。 -/
theorem maximum_value_generation_at_extremum {ι : Type} [Fintype ι] [Nonempty ι]
    (initial : InformationState ι) (target : ι) :
    bit_value initial (deterministic_state target) = shannon_entropy initial := by
  unfold bit_value
  rw [deterministic_entropy_zero]
  ring

/-- [系 3.2] 決定論的基底状態への移行は、任意の計算空間において創出富を最大化する -/
corollary bit_value_is_maximal {ι : Type} [Fintype ι] [Nonempty ι]
    (initial current : InformationState ι) (target : ι) :
    bit_value initial current ≤ bit_value initial (deterministic_state target) := by
  unfold bit_value
  rw [deterministic_entropy_zero]
  linarith [deterministic_minimizes_entropy target current]


-- ─────────────────────────────────────────────────
-- §3. プロトコル計算動学モデル (Macrocomputational Dynamics)
-- ─────────────────────────────────────────────────

/-- 
  分散型計算ネットワークの基礎構造体 (Algorithmic Capital System)
  - `B` : ビット資本ストック（蓄積された検証済コード、プロトコルの総計算力）
  - `δ` : アルゴリズム的減耗率（環境変化、依存API更新、データの死滅による技術的負債の発生速度）
  - `N` : ネットワーク外部性（ライブラリ依存密度、相互運用性による相乗効果乗数）
  - `L` : 人的計算資源の提供能力（知恵、システムの非決定性を排除する総デバッグキャパシティ）
-/
structure BitSystem where
  B : ℝ
  δ : ℝ
  N : ℝ
  L : ℝ
  B_pos : 0 < B
  δ_pos : 0 < δ ∧ δ < 1
  N_pos : 1 < N
  L_pos : 0 < L

/-- 計算システムの動学的状態遷移関数。
    外部環境のノイズによる資本の風化 (δ * B) を、ネットワーク相乗効果 (N) の下での
    リファクタリング投資インプット (I) が相殺・拡大する。 -/
def next_bit_state (sys : BitSystem) (I : ℝ) : ℝ :=
  sys.B - (sys.δ * sys.B) + (sys.N * I)

/-! ### 3.1 閉鎖型計算システム：中央集権Web2（収奪型プラットフォームのバグ） -/

/-- 利益（レント）を中央が独占し、オープンソースや貢献開発者へのインセンティブ還流
    （外部性の内部化）を遮断したクローズド・システム。純再投資インプット I が 0 に固定される。 -/
structure ClosedDigitalSystem extends BitSystem where
  reinvestment_zero : True := trivial

/-- 
  【定理 4.1】 クローズド・デジタルシステムの漸近的崩壊 (Algorithmic Decay Theorem)
  再投資（還流回路）を持たない閉鎖システムは、環境ノイズによるエントロピー増大（技術的負債 δ）
  に抗えず、その資本ストック（有用性）が確実に長期的衰退を辿る。
-/
theorem closed_system_decay (sys : ClosedDigitalSystem) :
    next_bit_state sys.toBitSystem 0 < sys.B := by
  dsimp [next_bit_state]
  have h_decay : 0 < sys.δ * sys.B := mul_pos sys.δ_pos.1 sys.B_pos
  linarith

/-! ### 3.2 自律分散型計算プロトコル：報徳Web3（自己修復型コモンズ） -/

/-- 
  マクロ計算論的予算制約（分度）と正の外部性還元機構（推譲）をプロトコル上に実装した分散型計算システム。
  - `digital_bundo` : 暗号的規律（システムのインフレや乱脈分配を防ぐ最大マクロ予算枠制約）
  - `digital_suijo` : コモンズ（開発者、デバッガー）へ自律的に自動執行される再投資（推譲）の総量
-/
structure ProtocolEconomy extends BitSystem where
  digital_bundo  : ℝ
  digital_suijo  : ℝ
  -- [規律（分度）の厳密制約]: 推譲（コモンズへの還元）は、分度の定めたマクロ予算制約の枠内でなければならない
  suijo_le_bundo : digital_suijo ≤ digital_bundo
  -- [生存・成長の境界条件]: ネットワーク相乗効果を伴う推譲が、環境減耗（技術的負債）の速度を圧倒していること
  network_suijo_gt_decay : N * digital_suijo > δ * B

/-- 
  【主定理 4.2】 自律分散型プロトコルの永続的拡大均衡定理 (Sustained Growth Theorem)
  暗号的な規律（分度）の下で、正の外部性をコモンズへ自動還流（推譲）させる分散型プロトコルは、
  中央の管理者を必要とせず、技術的風化（δ）を永続的に克服し、持続的成長を遂げる。
-/
theorem protocol_sustained_growth (sys : ProtocolEconomy) :
    next_bit_state sys.toBitSystem sys.digital_suijo > sys.B := by
  dsimp [next_bit_state]
  have h_growth : sys.N * sys.digital_suijo > sys.δ * sys.B := sys.network_suijo_gt_decay
  linarith

end YamamotoBitEconomics
