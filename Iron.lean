import Mathlib.Topology.Basic
import Mathlib.Order.Basic

/-!
# Iron Liquefaction Control: Chemical Potential Mapping
Author: Takeo Yamamoto
License: Apache-2.0
鉄（Fe）の融点を化学的ポテンシャル介入により低温で不動点化する制御系。
-/

structure IronState where
  temp      : ℝ
  potential : ℝ
  is_liquid : Bool

instance : TopologicalSpace IronState := ⊤

-- 前順序: temp と potential の増加方向
-- is_liquid は前順序に含めない（Bool は証明を複雑にするだけ）
instance : Preorder IronState where
  le a b := a.temp ≤ b.temp ∧ a.potential ≤ b.potential
  le_refl a := ⟨le_refl _, le_refl _⟩
  le_trans a b c hab hbc :=
    ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩

structure MetaSystem (α : Type*) [TopologicalSpace α] [Preorder α] where
  resolve : α → α
  is_fixed_point : ∀ x, resolve (resolve x) = resolve x
  is_monotone : Monotone resolve

-- 溶解プロセス: temp/potential は変えず is_liquid のみ更新
-- → 前順序（temp, potential）上で resolve は恒等写像と同等
def dissolve_iron (s : IronState) : IronState :=
  if s.temp ≥ 800.0 ∧ s.potential ≥ 50.0 then
    { s with is_liquid := true }
  else
    { s with is_liquid := false }

def IronSystem : MetaSystem IronState where
  resolve := dissolve_iron

  -- dissolve_iron は temp/potential を変えないため2回適用 = 1回適用
  is_fixed_point := fun s => by
    unfold dissolve_iron
    split <;> rfl

  -- 前順序は temp/potential のみ → resolve 後も temp/potential 不変 → hab がそのまま成立
  is_monotone := by
    intro a b hab
    unfold dissolve_iron Monotone
    split with ha
    · split with hb
      · exact hab
      · -- ha: a.temp ≥ 800 ∧ a.potential ≥ 50
        -- hb: ¬(b.temp ≥ 800 ∧ b.potential ≥ 50)
        -- hab: a.temp ≤ b.temp ∧ a.potential ≤ b.potential
        exfalso
        push_neg at hb
        cases hb with
        | inl h => linarith [hab.1, ha.1]
        | inr h => linarith [hab.2, ha.2]
    · split with hb
      · exact hab
      · exact hab
