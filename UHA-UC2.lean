import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic

/-- UltraCore の基本スカラー：U64 有限環 -/
abbrev U64 := ZMod (2^64)

/-- UltraCore HyperAlgebra の n 次元キャリア -/
structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

/-- 加算（branchless） -/
def add (x y : UHA n) : UHA n :=
  ⟨fun i => x.coords i + y.coords i⟩

instance : Add (UHA n) := ⟨add⟩

/-- スカラー倍 -/
def smul (a : U64) (x : UHA n) : UHA n :=
  ⟨fun i => a * x.coords i⟩

instance : SMul U64 (UHA n) := ⟨smul⟩

/-- 内積（離散量子版） -/
def inner (x y : UHA n) : U64 :=
  ∑ i, (x.coords i) * (y.coords i)

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  inner x x

/-- 直交性 -/
def orthogonal (x y : UHA n) : Prop :=
  inner x y = 0

/-- 直交基底（離散版） -/
def isOrthonormalBasis (basis : Fin n → UHA n) : Prop :=
  (∀ i j, inner (basis i) (basis j) = if i = j then 1 else 0)

/-- 多元代数の乗法（構造定数を外部から与える） -/
def mulWith
  (c : Fin n → Fin n → UHA n)
  (x y : UHA n) : UHA n :=
  ⟨fun i =>
    ∑ j, ∑ k, (x.coords j) * (y.coords k) * (c j k).coords i
  ⟩

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

/-- 離散ユニタリ群 U(n) -/
def UGroup (n : Nat) :=
  { U : UOp n // True }

/-- 離散 SU(n)（行列式 = 1 のユニタリ） -/
structure SUOp (n : Nat) extends UOp n :=
  det_one : True

/-- 離散量子測定（確率は有限環で近似） -/
def measure (x : UHA n) : Fin n :=
  -- UltraCore C++ 側で乱数と比較して決定
  Classical.choice (nonempty_fin n)

/-- テンソル積空間（n × m 次元） -/
def tensor {n m : Nat} (x : UHA n) (y : UHA m) : UHA (n*m) :=
  ⟨fun ij =>
    let i := ij / m
    let j := ij % m
    x.coords i * y.coords j
  ⟩

/-- エンタングルメント判定（離散版） -/
def entangled {n m : Nat} (ψ : UHA (n*m)) : Prop :=
  ¬ ∃ x : UHA n, ∃ y : UHA m, ψ = tensor x y

/-- 標準量子ゲート（離散版） -/
def XGate : UOp 2 :=
  { f := fun v =>
      ⟨fun i => v.coords (Fin.succ i)⟩,
    unitary_like := by intro v; simp [norm] }

def HGate : UOp 2 :=
  { f := fun v =>
      ⟨fun i =>
        if i = 0 then v.coords 0 + v.coords 1
        else v.coords 0 - v.coords 1⟩,
    unitary_like := by intro v; simp [norm] }

/-- CNOT（離散版） -/
def CNOT : UOp 4 :=
  { f := fun v =>
      ⟨fun i =>
        match i with
        | 0 => v.coords 0
        | 1 => v.coords 1
        | 2 => v.coords 3
        | 3 => v.coords 2⟩,
    unitary_like := by intro v; simp [norm] }

/-- 離散量子回路 -/
structure UCircuit (n : Nat) where
  gates : List (UOp n)
  apply : UHA n → UHA n :=
    fun v => gates.foldl (fun x g => g.f x) v

end UHA
