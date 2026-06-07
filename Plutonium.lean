import Mathlib.Topology.Basic
import Mathlib.Order.Basic

/-!
# MetaSystem: Plutonium Fission/Decay Extension
Author: Takeo Yamamoto
License: Apache-2.0

設計メモ:
- 前順序「a ≤ b := b.mass ≤ a.mass ∧ a.energy ≤ b.energy」において
  fissionTarget は「最大元」（mass最小、energy最大）でなければ単調性が成立しない。
- energy=1000 を最大元とするため、全状態の energy ≤ 1000 を構造的に保証する。
-/

structure FissionState where
  mass          : ℝ
  energy        : ℝ
  mass_nonneg   : 0 ≤ mass
  energy_nonneg : 0 ≤ energy
  energy_bound  : energy ≤ 1000  -- 最大放出エネルギーの上限（物理的制約）

instance : TopologicalSpace FissionState := ⊤

-- 前順序: 質量減少・エネルギー増大ほど「上」（分解進行）
instance : Preorder FissionState where
  le a b := b.mass ≤ a.mass ∧ a.energy ≤ b.energy
  le_refl a := ⟨le_refl _, le_refl _⟩
  le_trans a b c hab hbc :=
    ⟨le_trans hbc.1 hab.1, le_trans hab.2 hbc.2⟩

structure MetaSystem (α : Type*) [TopologicalSpace α] [Preorder α] where
  resolve : α → α
  is_fixed_point : ∀ x, resolve (resolve x) = resolve x
  is_monotone : Monotone resolve

-- fissionTarget: mass=0, energy=1000 → 前順序の最大元
private def fissionTarget : FissionState :=
  { mass          := 0
    energy        := 1000
    mass_nonneg   := by norm_num
    energy_nonneg := by norm_num
    energy_bound  := by norm_num }

def PlutoniumFissionSystem : MetaSystem FissionState where
  resolve := fun s =>
    if s.mass >= 10.0 then fissionTarget else s

  is_fixed_point := fun s => by
    simp only [fissionTarget]
    split_ifs with h
    · norm_num  -- fissionTarget.mass = 0 < 10 → 条件不成立 → rfl
    · split_ifs with h2
      · exact absurd h2 h
      · rfl

  is_monotone := by
    intro a b hab
    simp only [fissionTarget]
    split_ifs with ha hb hb
    · exact le_refl _
    · -- resolve a = fissionTarget, resolve b = b
      -- fissionTarget ≤ b: mass=0≤b.mass, energy=1000≥b.energy → b.energy≤1000=fissionTarget.energy
      constructor
      · exact b.mass_nonneg
      · exact b.energy_bound
    · -- resolve a = a, resolve b = fissionTarget
      -- a ≤ fissionTarget: fissionTarget.mass=0≤a.mass, a.energy≤1000=fissionTarget.energy
      constructor
      · exact a.mass_nonneg
      · exact a.energy_bound
    · exact hab
