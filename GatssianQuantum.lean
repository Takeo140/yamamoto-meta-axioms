License Apache 2.0  Takeo Yamamoto
import Mathlib

/-!
# ガウス整数による量子回路の厳密シミュレーション

振幅は Z[i] の元 a+bi（a b : Int）で持ち、浮動小数点を一切使わない。
Hadamard の 1/√2 は非正規化の H' = [[1,1],[1,-1]] で置き換え、
√2 の冪指数 k を `QState.k` に数える。

  実際の振幅 = amp[i] / (√2)^k
  測定確率   = N(amp[i]) / 2^k      （N(a+bi) = a² + b²、整数）

対応ゲート: X, Z, S, H', CNOT（T ゲートは Z[ζ₈] が必要なので未対応）。
-/

namespace GaussQ

/-- ガウス整数 a + b i -/
structure GI where
  re : Int
  im : Int
  deriving DecidableEq, Repr, Inhabited

namespace GI

def add (z w : GI) : GI := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : GI) : GI := ⟨-z.re, -z.im⟩
def mul (z w : GI) : GI := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- ノルム N(a+bi) = a² + b²（確率の分子になる整数） -/
def norm (z : GI) : Int := z.re * z.re + z.im * z.im

instance : Add GI := ⟨add⟩
instance : Neg GI := ⟨neg⟩
instance : Mul GI := ⟨mul⟩

def zero : GI := ⟨0, 0⟩
def one : GI := ⟨1, 0⟩
def I : GI := ⟨0, 1⟩

/-- ノルムは乗法的：振幅の積の確率は確率の積 -/
theorem norm_mul (z w : GI) : (GI.mul z w).norm = z.norm * w.norm := by
  cases z; cases w
  simp only [GI.norm, GI.mul]
  ring

/-- i² = -1 -/
theorem I_mul_I : GI.mul I I = ⟨-1, 0⟩ := by decide

end GI

/-- 量子状態：Z[i] 振幅のリスト（長さ 2^n）と √2 の冪指数 k -/
structure QState where
  amp : List GI
  k : Nat
  deriving DecidableEq, Repr

namespace QState

open GI

/-- |0…0⟩ -/
def init (n : Nat) : QState :=
  ⟨one :: List.replicate (2 ^ n - 1) zero, 0⟩

def get (s : QState) (i : Nat) : GI := s.amp.getD i zero

/-- 1量子ビットゲート（行列 [[m00,m01],[m10,m11]] を量子ビット q に作用） -/
def apply1 (m00 m01 m10 m11 : GI) (q : Nat) (s : QState) : QState :=
  let mask := 1 <<< q
  { s with
    amp := (List.range s.amp.length).map fun i =>
      if i.testBit q then
        m10 * s.get (i ^^^ mask) + m11 * s.get i
      else
        m00 * s.get i + m01 * s.get (i ||| mask) }

def X (q : Nat) (s : QState) : QState := apply1 zero one one zero q s
def Z (q : Nat) (s : QState) : QState := apply1 one zero zero (-one) q s
def S (q : Nat) (s : QState) : QState := apply1 one zero zero I q s

/-- 非正規化 Hadamard H' = [[1,1],[1,-1]]（H = H'/√2）。k を 1 増やす。 -/
def H (q : Nat) (s : QState) : QState :=
  let t := apply1 one one one (-one) q s
  { t with k := s.k + 1 }

/-- CNOT（制御 c、標的 t） -/
def CNOT (c t : Nat) (s : QState) : QState :=
  let mask := 1 <<< t
  { s with
    amp := (List.range s.amp.length).map fun i =>
      if i.testBit c then s.get (i ^^^ mask) else s.get i }

/-- 測定確率の分子 N(amp[i])。確率 = 分子 / 2^k。 -/
def weights (s : QState) : List Int := s.amp.map GI.norm

end QState

open QState

/-! ## 例1：Bell 状態 (|00⟩ + |11⟩)/√2 -/

def bell : QState := (init 2 |> H 0 |> CNOT 0 1)

example : bell.amp = [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩] := by decide
example : bell.k = 1 := by decide
/-- 確率：|00⟩ と |11⟩ が 1/2 ずつ（分子 1, 分母 2^1） -/
example : bell.weights = [1, 0, 0, 1] := by decide
/-- 全確率の和が 1（分子の和 = 2^k） -/
example : bell.weights.sum = 2 ^ bell.k := by decide

/-! ## 例2：GHZ 状態 (|000⟩ + |111⟩)/√2 -/

def ghz : QState := (init 3 |> H 0 |> CNOT 0 1 |> CNOT 1 2)

example : ghz.weights = [1, 0, 0, 0, 0, 0, 0, 1] := by decide
example : ghz.weights.sum = 2 ^ ghz.k := by decide

/-! ## 例3：干渉（H を2回で元に戻る） -/

def interfere : QState := (init 1 |> H 0 |> H 0)

/-- 振幅 [2, 0]、k = 2 なので 2/√2² = 1：|0⟩ に確率1で戻る -/
example : interfere.amp = [⟨2, 0⟩, ⟨0, 0⟩] := by decide
example : interfere.k = 2 := by decide
example : interfere.weights = [4, 0] := by decide   -- 4 / 2² = 1

/-! ## 例4：位相 i の効果（S ゲートを挟むと干渉が変わる） -/

def phase : QState := (init 1 |> H 0 |> S 0 |> H 0)

/-- 振幅 [1+i, 1-i]、k = 2。確率は 2/4 = 1/2 ずつ。 -/
example : phase.amp = [⟨1, 1⟩, ⟨1, -1⟩] := by decide
example : phase.weights = [2, 2] := by decide

/-- 比較：S² = Z なので H S S H は H Z H = X に相当し、|1⟩ に確率1。 -/
def phase2 : QState := (init 1 |> H 0 |> S 0 |> S 0 |> H 0)
example : phase2.weights = [0, 4] := by decide   -- 0/4 と 4/4

#eval bell
#eval ghz.weights
#eval phase.amp

end GaussQ
