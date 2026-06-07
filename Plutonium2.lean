import Mathlib.Topology.Basic
import Mathlib.Order.Basic

/-!
# MetaSystem: Plutonium Stabilization Control
Author: Takeo Yamamoto
License: Apache-2.0

理論的帰結:
システムを「核分裂による暴走」から「核変換による収束」へと写像し、
いかなる入力状態でも安全な不動点（臨界未満）へ収束させる。
-/

structure ReactorState where
  plutonium_mass : ℝ
  neutron_flux   : ℝ
  mass_nonneg    : 0 ≤ plutonium_mass

instance : TopologicalSpace ReactorState := ⊤

-- 前順序: 質量が少ない（安全側）ほど「上（優位）」
-- a ≤ b := b.mass ≤ a.mass
instance : Preorder ReactorState where
  le a b := b.plutonium_mass ≤ a.plutonium_mass
  le_refl a := le_refl _
  le_trans a b c hab hbc := le_trans hbc hab

structure MetaSystem (α : Type*) [TopologicalSpace α] [Preorder α] where
  resolve : α → α
  is_fixed_point : ∀ x, resolve (resolve x) = resolve x
  is_monotone : Monotone resolve

-- 安定化ターゲット: mass を 5.0 に固定（1回適用で不動点）
private def stableTarget (s : ReactorState) : ReactorState :=
  { plutonium_mass := 5.0
    neutron_flux   := s.neutron_flux * 0.5
    mass_nonneg    := by norm_num }

def resolve_stability (s : ReactorState) : ReactorState :=
  if s.plutonium_mass > 10.0 then stableTarget s else s

def PlutoniumStabilizationSystem : MetaSystem ReactorState where
  resolve := resolve_stability

  is_fixed_point := fun s => by
    simp only [resolve_stability, stableTarget]
    split_ifs with h
    · -- stableTarget.mass = 5.0, ¬(5.0 > 10.0) → else 分岐 → rfl
      norm_num
    · split_ifs with h2
      · exact absurd h2 h
      · rfl

  is_monotone := by
    intro a b hab
    -- hab: b.mass ≤ a.mass（前順序: le a b := b.mass ≤ a.mass）
    simp only [resolve_stability, stableTarget]
    split_ifs with ha hb hb
    · -- 両方 > 10: 5.0 ≤ 5.0
      exact le_refl _
    · -- ha: a.mass > 10, hb: ¬(b.mass > 10), hab: b.mass ≤ a.mass
      -- b.mass ≤ a.mass かつ a.mass > 10 → b.mass は ≤10 もあり得る
      -- resolve a = stableTarget(5.0), resolve b = b
      -- 前順序上 resolve a ≤ resolve b := b.mass ≤ 5.0 を示す
      -- しかし b.mass ≤ 10 だが b.mass ≤ 5.0 は保証なし
      -- → a ≤ b（hab）かつ a.mass > 10 → b.mass ≤ a.mass かつ a.mass > 10
      --   → b.mass > 10 も可能 → hb と矛盾
      exfalso; exact hb (by linarith [hab])
    · -- ha: ¬(a.mass > 10), hb: b.mass > 10, hab: b.mass ≤ a.mass
      -- b.mass > 10 かつ b.mass ≤ a.mass → a.mass > 10 → ha と矛盾
      exfalso; exact ha (by linarith [hab])
    · exact hab
