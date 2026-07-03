License Apache 2.0  Takeo Yamamoto
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

/-- 多元代数の乗法（構造定数を外部から与える） -/
def mulWith
  (c : Fin n → Fin n → UHA n)
  (x y : UHA n) : UHA n :=
  -- UltraCore の C++ 実装側で展開される部分
  ⟨fun i =>
    ∑ j, ∑ k, (x.coords j) * (y.coords k) * (c j k).coords i
  ⟩

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  ∑ i, (x.coords i) * (x.coords i)

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

end UHA
