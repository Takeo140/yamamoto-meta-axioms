import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace MetaRepair

open Classical

/-- 塩基 -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq, Inhabited

/-- コドン -/
def Codon := Base × Base × Base
  deriving Repr, DecidableEq, Inhabited

/-- アミノ酸 -/
inductive AminoAcid : Type
  | aa1 | aa2 | aa3 | aa4
  deriving Repr, DecidableEq, Inhabited

/-- 翻訳 -/
def translate : Codon → AminoAcid
  | (Base.A, _, _) => AminoAcid.aa1
  | (Base.T, _, _) => AminoAcid.aa2
  | (Base.G, _, _) => AminoAcid.aa3
  | (Base.C, _, _) => AminoAcid.aa4

def translate_seq (s : List Codon) : List AminoAcid :=
  s.map translate

/-- アミノ酸距離（重み付き）-/
def aa_dist (a b : AminoAcid) : ℝ :=
  if a = b then 0 else 1

/-- 位置ごとの重要度（重み）-/
def weight (i : ℕ) : ℝ :=
  1 + (i : ℝ) / 10   -- 例：位置依存重み

/-- 重み付きタンパク質距離 -/
def protein_distance_w :
  List AminoAcid → List AminoAcid → ℝ
  | xs, ys =>
    (List.zip xs ys).enum.foldl
      (fun acc ⟨i, p⟩ =>
        acc + weight i * aa_dist p.1 p.2)
      0

/-- 機能距離 -/
def functional_distance (x y : List Codon) : ℝ :=
  protein_distance_w (translate_seq x) (translate_seq y)

/-- 発現効率（確率的モデル簡略化）-/
def expression_efficiency (m : List Codon) : ℝ :=
  1 / (1 + (m.length : ℝ))

/-- 安全性ペナルティ（長さ依存など）-/
def safety_penalty (m : List Codon) : ℝ :=
  (m.length : ℝ) / 100

/-- 総合コスト関数（これが核心）-/
def total_cost
  (target : List Codon)
  (m : List Codon) : ℝ :=
  functional_distance target m
  - expression_efficiency m
  + safety_penalty m

/-- 最適パッチ（定義）-/
def is_optimal
  (target : List Codon)
  (candidates : List (List Codon))
  (m : List Codon) : Prop :=
  m ∈ candidates ∧
  ∀ c ∈ candidates,
    total_cost target m ≤ total_cost target c

/-- 非空有限集合では最適解が存在 -/
theorem optimal_exists
  (target : List Codon)
  (candidates : List (List Codon))
  (h : candidates ≠ []) :
  ∃ m, is_optimal target candidates m := by
  classical
  induction candidates with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      refine ⟨c, ?h1, ?h2⟩
      · simp
      · intro x hx; simp at hx; cases hx; simp [hx]
    · have hne : cs ≠ [] := hcs
      obtain ⟨m, hm⟩ := ih hne
      by_cases hcmp :
        total_cost target c ≤ total_cost target m
      · refine ⟨c, ?h1, ?h2⟩
        · simp
        · intro x hx
          simp at hx
          cases hx with
          | inl hx => simp [hx]
          | inr hx =>
            have := hm.2 x hx
            exact le_trans hcmp this
      · refine ⟨m, ?h1, ?h2⟩
        · simp [hm.1]
        · intro x hx
          simp at hx
          cases hx with
          | inl hx =>
            have := hm.2 c (by simp)
            exact le_trans this (le_of_not_ge hcmp)
          | inr hx =>
            exact hm.2 x hx

/-- ε許容解 -/
def is_feasible
  (target : List Codon)
  (m : List Codon)
  (ε : ℝ) : Prop :=
  functional_distance target m ≤ ε

/-- 制約付き最適化 -/
def is_constrained_optimal
  (target : List Codon)
  (candidates : List (List Codon))
  (ε : ℝ)
  (m : List Codon) : Prop :=
  is_feasible target m ε ∧
  m ∈ candidates ∧
  ∀ c ∈ candidates,
    is_feasible target c ε →
    total_cost target m ≤ total_cost target c

/-- 制約付き最適解の存在 -/
theorem constrained_optimal_exists
  (target : List Codon)
  (candidates : List (List Codon))
  (ε : ℝ)
  (h : ∃ m ∈ candidates, is_feasible target m ε) :
  ∃ m, is_constrained_optimal target candidates ε m := by
  classical
  rcases h with ⟨m0, hm0, hfeas⟩
  let feasible :=
    candidates.filter (fun m => decide (is_feasible target m ε))
  have hne : feasible ≠ [] := by
    -- m0 が入るので非空
    have : m0 ∈ feasible := by
      simp [feasible, hm0, hfeas]
    intro hnil
    simp [hnil] at this
  obtain ⟨m, hm⟩ := optimal_exists target feasible hne
  refine ⟨m, ?_⟩
  constructor
  · -- feasible
    have : m ∈ feasible := hm.1
    simp [feasible] at this
    exact this
  constructor
  · -- 元集合にも属する
    have : m ∈ feasible := hm.1
    simp [feasible] at this
    exact this.1
  · -- 最適性
    intro c hc hfeas'
    have hc' : c ∈ feasible := by
      simp [feasible, hc, hfeas']
    exact hm.2 c hc'

end MetaRepair
