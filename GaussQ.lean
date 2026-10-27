/-
  GaussQ: ガウス整数 Z[i] による量子回路の厳密シミュレーション
  License: Apache 2.0
  Author: Takeo Yamamoto
-/

import Mathlib

/-!
# ガウス整数による量子回路の厳密シミュレーション

振幅は Z[i] の元 a+bi（a b : Int）で持ち、浮動小数点を一切使わない。
Hadamard の 1/√2 は非正規化の H' = [[1,1],[1,-1]] で置き換え、
√2 の冪指数 k を `QState.k` に数える。

  実際の振幅 = amp[i] / (√2)^k
  測定確率   = N(amp[i]) / 2^k      （N(a+bi) = a² + b²、整数）

対応ゲート: X, Y, Z, S, S†, H', CNOT, CZ, SWAP, CCX（Toffoli）
未対応: T ゲート（Z[ζ₈] が必要。振幅環の拡張が要るため別モジュール扱い）。
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

/-- ノルムは非負 -/
theorem norm_nonneg (z : GI) : 0 ≤ z.norm :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- 符号反転でノルムは不変（位相 -1 は確率を変えない） -/
theorem norm_neg (z : GI) : (-z).norm = z.norm := by
  cases z with
  | mk a b =>
    show (-a) * (-a) + (-b) * (-b) = a * a + b * b
    ring

/-- i² = -1 -/
theorem I_mul_I : GI.mul I I = ⟨-1, 0⟩ := by decide

/-- N(i) = 1（位相 i は確率を変えない） -/
theorem norm_I : I.norm = 1 := by decide

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
def Y (q : Nat) (s : QState) : QState := apply1 zero (-I) I zero q s
def Z (q : Nat) (s : QState) : QState := apply1 one zero zero (-one) q s
def S (q : Nat) (s : QState) : QState := apply1 one zero zero I q s
/-- S†（S の逆） -/
def Sdg (q : Nat) (s : QState) : QState := apply1 one zero zero (-I) q s

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

/-- CZ（両方 1 の基底状態の符号を反転） -/
def CZ (c t : Nat) (s : QState) : QState :=
  { s with
    amp := (List.range s.amp.length).map fun i =>
      if i.testBit c && i.testBit t then -(s.get i) else s.get i }

/-- SWAP（CNOT 3 回） -/
def SWAP (a b : Nat) (s : QState) : QState :=
  s |> CNOT a b |> CNOT b a |> CNOT a b

/-- CCX（Toffoli：制御 c₁ c₂、標的 t） -/
def CCX (c₁ c₂ t : Nat) (s : QState) : QState :=
  let mask := 1 <<< t
  { s with
    amp := (List.range s.amp.length).map fun i =>
      if i.testBit c₁ && i.testBit c₂ then s.get (i ^^^ mask) else s.get i }

/-- 測定確率の分子 N(amp[i])。確率 = 分子 / 2^k。 -/
def weights (s : QState) : List Int := s.amp.map GI.norm

/-- 測定確率（有理数）：N(amp[i]) / 2^k -/
def prob (s : QState) (i : Nat) : ℚ := ((s.get i).norm : ℚ) / 2 ^ s.k

/-- 規格化されているか：分子の総和 = 2^k -/
def isNormalized (s : QState) : Bool := decide (s.weights.sum = 2 ^ s.k)

/-! ### ゲートの一般的性質（状態の長さと k） -/

theorem apply1_length (m00 m01 m10 m11 : GI) (q : Nat) (s : QState) :
    (apply1 m00 m01 m10 m11 q s).amp.length = s.amp.length := by
  simp [apply1]

theorem CNOT_length (c t : Nat) (s : QState) :
    (CNOT c t s).amp.length = s.amp.length := by
  simp [CNOT]

theorem CZ_length (c t : Nat) (s : QState) :
    (CZ c t s).amp.length = s.amp.length := by
  simp [CZ]

theorem CCX_length (c₁ c₂ t : Nat) (s : QState) :
    (CCX c₁ c₂ t s).amp.length = s.amp.length := by
  simp [CCX]

theorem H_length (q : Nat) (s : QState) :
    (H q s).amp.length = s.amp.length := by
  simp [H, apply1]

/-- H' だけが √2 の冪指数 k を増やす -/
theorem H_k (q : Nat) (s : QState) : (H q s).k = s.k + 1 := rfl

theorem X_k (q : Nat) (s : QState) : (X q s).k = s.k := rfl
theorem Y_k (q : Nat) (s : QState) : (Y q s).k = s.k := rfl
theorem Z_k (q : Nat) (s : QState) : (Z q s).k = s.k := rfl
theorem S_k (q : Nat) (s : QState) : (S q s).k = s.k := rfl
theorem CNOT_k (c t : Nat) (s : QState) : (CNOT c t s).k = s.k := rfl
theorem CZ_k (c t : Nat) (s : QState) : (CZ c t s).k = s.k := rfl
theorem CCX_k (c₁ c₂ t : Nat) (s : QState) : (CCX c₁ c₂ t s).k = s.k := rfl

theorem weights_length (s : QState) : s.weights.length = s.amp.length := by
  simp [weights]

theorem init_length (n : Nat) : (init n).amp.length = 2 ^ n := by
  have h := Nat.two_pow_pos n
  simp only [init, List.length_cons, List.length_replicate]
  omega

/-- 初期状態の確率分子の総和は 1（k = 0 なので 2^0 = 1） -/
theorem init_weights_sum (n : Nat) : (init n).weights.sum = 1 := by
  simp [init, weights, GI.norm, GI.one, GI.zero]

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

/-! ## 例5：追加ゲートの検証 -/

/-- Y|0⟩ = i|1⟩ -/
example : (init 1 |> Y 0).amp = [⟨0, 0⟩, ⟨0, 1⟩] := by decide

/-- S† は S の逆：H → S → S† は H だけの結果 [1, 1]（k = 1）に戻る -/
example : (init 1 |> H 0 |> S 0 |> Sdg 0).amp = [⟨1, 0⟩, ⟨1, 0⟩] := by decide

/-- CZ は |11⟩ の符号だけを反転する -/
example : (init 2 |> X 0 |> X 1 |> CZ 0 1).amp
    = [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩] := by decide

/-- SWAP：|01⟩（index 1）→ |10⟩（index 2） -/
example : (init 2 |> X 0 |> SWAP 0 1).weights = [0, 0, 1, 0] := by decide

/-- Toffoli：|110⟩ 相当の入力（制御 0,1 が立つ）→ 標的 2 が反転して index 7 -/
example : (init 3 |> X 0 |> X 1 |> CCX 0 1 2).weights = [0, 0, 0, 0, 0, 0, 0, 1] := by decide

/-! ## 例6：2量子ビット Grover（|11⟩ を探索）

H' を 6 回使うので k = 6。最終振幅は index 3 に -8、確率 = 64 / 2⁶ = 1。 -/

def grover2 : QState :=
  init 2 |> H 0 |> H 1 |> CZ 0 1 |> H 0 |> H 1
         |> X 0 |> X 1 |> CZ 0 1 |> X 0 |> X 1 |> H 0 |> H 1

example : grover2.k = 6 := by decide
example : grover2.amp = [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-8, 0⟩] := by decide
example : grover2.weights = [0, 0, 0, 64] := by decide
example : grover2.isNormalized = true := by decide

#eval bell
#eval ghz.weights
#eval phase.amp
#eval grover2.weights
#eval prob bell 0
#eval prob grover2 3

end GaussQ
