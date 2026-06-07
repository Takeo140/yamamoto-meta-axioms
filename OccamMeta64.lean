import Mathlib.Order.Basic

/-!
# Yamamoto-64: Occam-Meta Kernel
Author: Takeo Yamamoto
License: Apache-2.0
64ビット環境向け計算理論基盤。
記述長(K)を最小化する不動点(Fixed Point)計算理論。
-/

structure State64 where
  val       : UInt64
  pot       : UInt64
  is_stable : Bool

def complexity (s : State64) : UInt64 :=
  s.val ^^^ s.pot

instance : Preorder State64 where
  le a b := complexity a ≤ complexity b
  le_refl a := le_refl _
  le_trans a b c hab hbc := le_trans hab hbc

def resolve_64 (s : State64) : State64 :=
  if s.val > 0x7FFFFFFFFFFFFFFF ∨ s.pot > 0x3FFFFFFFFFFFFFFF then
    { s with val := 0, pot := 0, is_stable := true }
  else
    { s with is_stable := true }

structure OccamMetaSystem where
  resolve        : State64 → State64
  is_fixed_point : ∀ x, resolve (resolve x) = resolve x
  is_minimal     : ∀ x, complexity (resolve x) ≤ complexity x

-- 補題: 0 は閾値を超えない
private lemma zero_not_over_threshold :
    ¬((0 : UInt64) > 0x7FFFFFFFFFFFFFFF ∨ (0 : UInt64) > 0x3FFFFFFFFFFFFFFF) := by
  simp [UInt64.lt_iff_toNat_lt, UInt64.toNat]

def GlobalOccam64 : OccamMetaSystem where
  resolve := resolve_64

  is_fixed_point := fun s => by
    simp only [resolve_64]
    split_ifs with h
    · -- 1回目: {val:=0, pot:=0, ...} → 2回目: 0 ≤ 閾値 → else → rfl
      simp [zero_not_over_threshold]
    · -- else ケース: val/pot 不変 → split_ifs で同じ分岐
      split_ifs with h2
      · exact absurd h2 h
      · rfl

  is_minimal := by
    intro x
    simp only [complexity, resolve_64]
    split_ifs with h
    · -- val=0, pot=0 → 0 ^^^ 0 = 0 ≤ x.val ^^^ x.pot
      simp [UInt64.zero_xor, UInt64.le_iff_toNat_le]
    · -- val/pot 不変 → le_refl
      exact le_refl _
