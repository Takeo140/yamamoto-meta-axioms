License Apache 2.0  Takeo Yamamoto
/-!
# PracticalComplex64

実行向けの離散複素数線形代数。各成分は Lean の `Float`（通常の64ビット倍精度
浮動小数点）であり、有限精度の近似計算を行う。厳密証明ではなく、数値計算用途の
実装である。
-/

namespace PracticalComplex64

/-- 実部・虚部を倍精度浮動小数点で持つ複素数。 -/
structure Complex64 where
  re : Float
  im : Float
deriving Repr

def zero : Complex64 := ⟨0.0, 0.0⟩
def one : Complex64 := ⟨1.0, 0.0⟩

def add (x y : Complex64) : Complex64 := ⟨x.re + y.re, x.im + y.im⟩
def sub (x y : Complex64) : Complex64 := ⟨x.re - y.re, x.im - y.im⟩
def scale (a : Float) (x : Complex64) : Complex64 := ⟨a * x.re, a * x.im⟩
def conj (x : Complex64) : Complex64 := ⟨x.re, -x.im⟩

/-- 通常の複素数乗算。 -/
def mul (x y : Complex64) : Complex64 :=
  ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

/-- 絶対値の二乗。 -/
def normSq (x : Complex64) : Float := x.re * x.re + x.im * x.im

abbrev Vector := List Complex64
abbrev Matrix := List Vector

def zeroVector (n : Nat) : Vector := List.replicate n zero

/-! 長さが異なる入力は `none` で明示的に失敗させる。 -/
def vectorAdd : Vector → Vector → Option Vector
  | [], [] => some []
  | x :: xs, y :: ys => do
      let rest ← vectorAdd xs ys
      pure (add x y :: rest)
  | _, _ => none

/-! `y ← alpha * x + y`。 -/
def axpy (alpha : Complex64) : Vector → Vector → Option Vector
  | [], [] => some []
  | x :: xs, y :: ys => do
      let rest ← axpy alpha xs ys
      pure (add (mul alpha x) y :: rest)
  | _, _ => none

/-- エルミート内積 `Σ conj(xᵢ) * yᵢ`。 -/
def dot : Vector → Vector → Option Complex64
  | [], [] => some zero
  | x :: xs, y :: ys => do
      let tail ← dot xs ys
      pure (add (mul (conj x) y) tail)
  | _, _ => none

/-- 密行列とベクトルの積。各行の長さを検査する。 -/
def matVec (a : Matrix) (x : Vector) : Option Vector :=
  a.mapM (fun row => dot row x)

/-- 行列の各要素を実数スカラー倍する。 -/
def matrixScale (alpha : Float) (a : Matrix) : Matrix :=
  a.map (fun row => row.map (scale alpha))

/-- 対角行列を作る。 -/
def diagonal (d : Vector) : Matrix :=
  d.enum.map fun (row, value) =>
    d.enum.map fun (col, _) => if row = col then value else zero

/-- 2×2の単位行列。 -/
def identity2 : Matrix := [[one, zero], [zero, one]]

/-- 典型的な数値演算例: `identity2 * [1+2i, 3-1i]`。 -/
def example : Option Vector :=
  matVec identity2 [⟨1.0, 2.0⟩, ⟨3.0, -1.0⟩]

end PracticalComplex64
