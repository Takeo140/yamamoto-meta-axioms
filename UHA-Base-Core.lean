License Apache-2.0  Takeo Yamamoto
import Mathlib

open BigOperators

/-- 基本スカラー：64ビット符号なし整数環 (unsigned 64-bit mod 2^64) -/
abbrev U64 := ZMod (2^64)

/-- UltraCore HyperAlgebra の n 次元キャリア空間 -/
@[ext]
structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

-- 加法群およびスカラー倍のインスタンス定義
instance : Zero (UHA n) := ⟨⟨fun _ => 0⟩⟩
instance : Add (UHA n) := ⟨fun x y => ⟨fun i => x.coords i + y.coords i⟩⟩
instance : Neg (UHA n) := ⟨fun x => ⟨fun i => - x.coords i⟩⟩
instance : SMul U64 (UHA n) := ⟨fun a x => ⟨fun i => a * x.coords i⟩⟩

@[simp] theorem zero_coords (i : Fin n) : (0 : UHA n).coords i = 0 := rfl
@[simp] theorem add_coords (x y : UHA n) (i : Fin n) : (x + y).coords i = x.coords i + y.coords i := rfl
@[simp] theorem neg_coords (x : UHA n) (i : Fin n) : (-x).coords i = - x.coords i := rfl
@[simp] theorem smul_coords (a : U64) (x : UHA n) (i : Fin n) : (a • x).coords i = a * x.coords i := rfl

instance : AddCommGroup (UHA n) where
  add_assoc := fun x y z => by ext i; simp [add_assoc]
  zero_add := fun x => by ext i; simp
  add_zero := fun x => by ext i; simp
  add_comm := fun x y => by ext i; simp [add_comm]
  neg_add_cancel := fun x => by ext i; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module U64 (UHA n) where
  one_smul := fun x => by ext i; simp
  mul_smul := fun a b x => by ext i; simp [mul_assoc]
  smul_zero := fun a => by ext i; simp
  smul_add := fun a x y => by ext i; simp [mul_add]
  add_smul := fun a b x => by ext i; simp [add_mul]
  zero_smul := fun x => by ext i; simp

/-- 多元代数の乗法：外部から与えられる構造定数 c に基づく双線形積 -/
def mulWith (c : Fin n → Fin n → UHA n) (x y : UHA n) : UHA n :=
  ⟨fun i => ∑ j, ∑ k, x.coords j * y.coords k * (c j k).coords i⟩

/-- 対称双線形内積 -/
def inner (x y : UHA n) : U64 :=
  ∑ i, x.coords i * y.coords i

/-- 離散二次形式（自己内積によるノルム） -/
def norm (x : UHA n) : U64 :=
  ∑ i, x.coords i * x.coords i

theorem norm_eq_inner (x : UHA n) : norm x = inner x x := rfl

theorem inner_comm (x y : UHA n) : inner x y = inner y x :=
  Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem inner_add_left (x y z : UHA n) :
    inner (x + y) z = inner x z + inner y z := by
  unfold inner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

theorem inner_smul_left (a : U64) (x y : UHA n) :
    inner (a • x) y = a * inner x y := by
  unfold inner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_coords]
  ring

theorem norm_smul (a : U64) (x : UHA n) :
    norm (a • x) = (a * a) * norm x := by
  unfold norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_coords]
  ring

/-- ノルム保存作用素（ユニタリ型作用素の基底定義） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

/-- 恒等作用素 -/
def UOp.id : UOp n := ⟨fun v => v, fun _ => rfl⟩

/-- 作用素の合成：ノルム保存則は合成によって閉じている -/
def UOp.comp (g h : UOp n) : UOp n :=
  ⟨fun v => g.f (h.f v), fun v => by rw [g.unitary_like, h.unitary_like]⟩

end UHA
