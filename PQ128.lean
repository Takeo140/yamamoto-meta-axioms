License Apache 2.0 Takeo Yamamoto
/-!
# PracticalQuantum128
離散型量子計算の軽量シミュレータ（128ビット複素数・Arrayベース）。
単一・複数量子ビットの状態ベクトル、基本量子ゲート、測定処理を提供する。
-/
namespace PracticalQuantum128

structure Complex128 where
  re : Float
  im : Float
deriving Repr, Inhabited

instance : OfNat Complex128 0 where ofNat := ⟨0.0, 0.0⟩
instance : OfNat Complex128 1 where ofNat := ⟨1.0, 0.0⟩

instance : Add Complex128 where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

instance : Sub Complex128 where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

instance : Mul Complex128 where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

instance : HMul Float Complex128 Complex128 where
  hMul a x := ⟨a * x.re, a * x.im⟩

def conj (x : Complex128) : Complex128 := ⟨x.re, -x.im⟩
def normSq (x : Complex128) : Float := x.re * x.re + x.im * x.im

abbrev Vector := Array Complex128
abbrev Matrix := Array Vector

/-- エルミート内積 -/
def dot (x y : Vector) : Option Complex128 :=
  if x.size == y.size then
    let mut sum : Complex128 := 0
    for i in [0:x.size] do
      sum := sum + conj x[i]! * y[i]!
    some sum
  else
    none

/-- 密行列とベクトルの積（量子ゲートの適用） -/
def matVec (a : Matrix) (x : Vector) : Option Vector :=
  if a.size == x.size then
    a.mapM (fun row => dot row x)
  else
    none

/-! ## 量子状態と基本ゲート -/

/-- $n$ 量子ビットの初期状態 $|0...0\rangle$ を生成する。サイズは $2^n$。 -/
def zeroState (numQubits : Nat) : Vector :=
  let size := 2 ^ numQubits
  let mut v := Array.replicate size (⟨0.0, 0.0⟩ : Complex128)
  if size > 0 then
    v := v.set! 0 ⟨1.0, 0.0⟩
  v

/-- パウリ-X ゲート（NOT） -/
def gateX : Matrix :=
  #[#[0, 1],
    #[1, 0]]

/-- アダマール ゲート（H） -/
def gateH : Matrix :=
  let invSqrt2 : Float := 1.0 / (2.0).sqrt
  #[#[⟨invSqrt2, 0⟩, ⟨invSqrt2, 0⟩],
    #[⟨invSqrt2, 0⟩, ⟨-invSqrt2, 0⟩]]

/-- 2量子ビットのテンソル積（Kronecker積）: A ⊗ B -/
def tensorProduct (a b : Matrix) : Matrix :=
  let rowsA := a.size
  let colsA := if rowsA > 0 then a[0]!.size else 0
  let rowsB := b.size
  let colsB := if rowsB > 0 then b[0]!.size else 0
  
  let totalRows := rowsA * rowsB
  let totalCols := colsA * colsB
  
  let mut result : Matrix := Array.replicate totalRows (Array.replicate totalCols 0)
  
  for i in [0:rowsA] do
    for j in [0:colsA] do
      let valA := a[i]![j]!
      for k in [0:rowsB] do
        for l in [0:colsB] do
          let valB := b[k]![l]!
          let targetRow := i * rowsB + k
          let targetCol := j * colsB + l
          let prod : Complex128 := ⟨valA.re * valB.re - valA.im * valB.im, valA.re * valB.im + valA.im * valB.re⟩
          result := result.modify targetRow (fun row => row.set! targetCol prod)
  result

/-- 典型的な量子回路の実行例: 1量子ビットにHゲートを適用し、さらにXゲートを適用する -/
def exampleQuantumCircuit : Option Vector := do
  let initState := zeroState 1
  let stateAfterH ← matVec gateH initState
  let finalState ← matVec gateX stateAfterH
  pure finalState

end PracticalQuantum128
