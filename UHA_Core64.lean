/-
  UHA-DComplex-64 Base Core (基底核)
  License: Apache 2.0
  Author: Takeo Yamamoto
-/
import Mathlib

open BigOperators

/-- 基本スカラー：U64 有限環 -/
abbrev U64 := ZMod (2^64)

/-- UltraCore HyperAlgebra の n 次元キャリア -/
@[ext]
structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

instance : Zero (UHA n) := ⟨⟨fun _ => 0⟩⟩
instance : Add (UHA n) := ⟨fun x y => ⟨fun i => x.coords i + y.coords i⟩⟩
instance : Neg (UHA n) := ⟨fun x => ⟨fun i => - x.coords i⟩⟩
instance : SMul U64 (UHA n) := ⟨fun a x => ⟨fun i => a * x.coords i⟩⟩

@[simp] theorem zero_coords (i : Fin n) : (0 : UHA n).coords i = 0 := rfl
@[simp] theorem add_coords (x y : UHA n) (i : Fin n) :
    (x + y).coords i = x.coords i + y.coords i := rfl
@[simp] theorem neg_coords (x : UHA n) (i : Fin n) :
    (-x).coords i = - x.coords i := rfl
@[simp] theorem smul_coords (a : U64) (x : UHA n) (i : Fin n) :
    (a • x).coords i = a * x.coords i := rfl

theorem add_comm' (x y : UHA n) : x + y = y + x := by
  ext i; simp [add_comm]

theorem add_assoc' (x y z : UHA n) : x + y + z = x + (y + z) := by
  ext i; simp [add_assoc]

theorem zero_add' (x : UHA n) : 0 + x = x := by
  ext i; simp

/-- 多元代数の乗法（構造定数 c を外部から与える） -/
def mulWith (c : Fin n → Fin n → UHA n) (x y : UHA n) : UHA n :=
  ⟨fun i => ∑ j, ∑ k, x.coords j * y.coords k * (c j k).coords i⟩

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  ∑ i, x.coords i * x.coords i

theorem norm_smul (a : U64) (x : UHA n) :
    norm (a • x) = (a * a) * norm x := by
  unfold norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_coords]
  ring

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

/-- 恒等作用素 -/
def UOp.id : UOp n := ⟨fun v => v, fun _ => rfl⟩

/-- 合成：ユニタリ作用素は合成で閉じる -/
def UOp.comp (g h : UOp n) : UOp n :=
  ⟨fun v => g.f (h.f v), fun v => by rw [g.unitary_like, h.unitary_like]⟩

end UHA

