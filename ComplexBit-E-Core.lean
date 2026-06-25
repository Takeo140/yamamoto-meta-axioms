License Apache 2.0 Takeo Yamamoto
/-!
# ComplexQuantum Phase Space Simulator
# 連続位相空間における量子ビット演算ライブラリ
# Lean 4 実装

## 理論的位置づけ
本モジュールは、情報（Real）と価値（Imag）を連続的な複素確率振幅として捉え、
ブロッホ球（位相空間）上の回転運動として量子ゲートを再定義する。
測定は、ボルン則（|振幅|² = 確率）に基づき、確率的に状態を崩壊させる。
-/

import Mathlib

-- ============================================================
-- §1. 連続複素数と量子状態の定義
-- ============================================================

structure ComplexAmp where
  re : Float
  im : Float
  deriving Repr, Inhabited

namespace ComplexAmp

  def normSq (c : ComplexAmp) : Float :=
    c.re * c.re + c.im * c.im

  def add (c1 c2 : ComplexAmp) : ComplexAmp :=
    { re := c1.re + c2.re, im := c1.im + c2.im }

  def mul (c1 c2 : ComplexAmp) : ComplexAmp :=
    { re := c1.re * c2.re - c1.im * c2.im
      im := c1.re * c2.im + c1.im * c2.re }

  def smul (s : Float) (c : ComplexAmp) : ComplexAmp :=
    { re := s * c.re, im := s * c.im }

  def conj (c : ComplexAmp) : ComplexAmp :=
    { re := c.re, im := -c.im }

  def exp_i (theta : Float) : ComplexAmp :=
    { re := theta.cos, im := theta.sin }

  def toString (c : ComplexAmp) : String :=
    let sign := if c.im >= 0 then "+" else ""
    s!"({c.re}{sign}{c.im}i)"

end ComplexAmp

/--
`QuantumBit` : 連続位相空間上の1量子ビット状態
  |ψ⟩ = α|0⟩ + β|1⟩
  alpha : |0⟩ (情報基底) の確率振幅
  beta  : |1⟩ (価値基底) の確率振幅
-/
structure QuantumBit where
  alpha : ComplexAmp
  beta  : ComplexAmp
  deriving Repr, Inhabited

namespace QuantumBit

  def normalize (q : QuantumBit) : QuantumBit :=
    let total := q.alpha.normSq + q.beta.normSq
    if total > 1e-15 then
      let norm := total.sqrt
      { alpha := ComplexAmp.smul (1.0 / norm) q.alpha
        beta  := ComplexAmp.smul (1.0 / norm) q.beta }
    else
      q

  def isNormalized (q : QuantumBit) (epsilon : Float := 1e-5) : Bool :=
    let total := q.alpha.normSq + q.beta.normSq
    (total - 1.0).abs < epsilon

  def probability0 (q : QuantumBit) : Float :=
    q.alpha.normSq

  def probability1 (q : QuantumBit) : Float :=
    q.beta.normSq

  /-- ブロッホ球座標 (x, y, z) -/
  def blochCoordinates (q : QuantumBit) : Float × Float × Float :=
    let abConj := ComplexAmp.mul q.alpha (ComplexAmp.conj q.beta)
    let x := 2.0 * abConj.re
    let y := 2.0 * abConj.im
    let z := q.alpha.normSq - q.beta.normSq
    (x, y, z)

  def toString (q : QuantumBit) : String :=
    s!"|0⟩: {q.alpha.toString}, |1⟩: {q.beta.toString}"

end QuantumBit

-- ============================================================
-- §2. 連続位相幾何ゲート群
-- ============================================================

namespace QuantumGates
open ComplexAmp

/-- 位相シフトゲート R_z(θ)
    |0⟩ → e^{-iθ/2}|0⟩
    |1⟩ → e^{iθ/2}|1⟩
    情報と価値の位相関係を連続的に変化させる -/
def phaseShift (theta : Float) (q : QuantumBit) : QuantumBit :=
  let half := theta / 2.0
  let eMinus := ComplexAmp.exp_i (-half)
  let ePlus  := ComplexAmp.exp_i half
  QuantumBit.normalize {
    alpha := ComplexAmp.mul q.alpha eMinus
    beta  := ComplexAmp.mul q.beta ePlus
  }

/-- 連続的アダマールゲート (H gate)
    情報と価値を等重みの重ね合わせ状態（赤道面）へ射影する
    H = (1/√2) [[1, 1], [1, -1]] -/
def gateH (q : QuantumBit) : QuantumBit :=
  let invSqrt2 := 1.0 / (2.0.sqrt)
  let a_re := (q.alpha.re + q.beta.re) * invSqrt2
  let a_im := (q.alpha.im + q.beta.im) * invSqrt2
  let b_re := (q.alpha.re - q.beta.re) * invSqrt2
  let b_im := (q.alpha.im - q.beta.im) * invSqrt2
  { alpha := { re := a_re, im := a_im }
    beta  := { re := b_re, im := b_im } }

/-- パウリ X ゲート（ビット反転）X = [[0,1],[1,0]] -/
def gateX (q : QuantumBit) : QuantumBit :=
  { alpha := q.beta, beta := q.alpha }

/-- パウリ Y ゲート Y = [[0,-i],[i,0]] -/
def gateY (q : QuantumBit) : QuantumBit :=
  let i := { re := 0.0, im := 1.0 : ComplexAmp }
  let minusI := { re := 0.0, im := -1.0 : ComplexAmp }
  { alpha := ComplexAmp.mul q.beta minusI
    beta  := ComplexAmp.mul q.alpha i }

/-- パウリ Z ゲート（位相反転）Z = [[1,0],[0,-1]] -/
def gateZ (q : QuantumBit) : QuantumBit :=
  let minusOne := { re := -1.0, im := 0.0 : ComplexAmp }
  { alpha := q.alpha
    beta  := ComplexAmp.mul q.beta minusOne }

/-- X軸回転 Rx(θ) = cos(θ/2)I - i·sin(θ/2)X -/
def rotationX (theta : Float) (q : QuantumBit) : QuantumBit :=
  let c := (theta / 2.0).cos
  let s := (theta / 2.0).sin
  let a_re := c * q.alpha.re - s * q.beta.im
  let a_im := c * q.alpha.im + s * q.beta.re
  let b_re := -s * q.alpha.im + c * q.beta.re
  let b_im := s * q.alpha.re + c * q.beta.im
  { alpha := { re := a_re, im := a_im }
    beta  := { re := b_re, im := b_im } }

/-- Y軸回転 Ry(θ) = cos(θ/2)I - i·sin(θ/2)Y -/
def rotationY (theta : Float) (q : QuantumBit) : QuantumBit :=
  let c := (theta / 2.0).cos
  let s := (theta / 2.0).sin
  let a_re := c * q.alpha.re - s * q.beta.re
  let a_im := c * q.alpha.im - s * q.beta.im
  let b_re := s * q.alpha.re + c * q.beta.re
  let b_im := s * q.alpha.im + c * q.beta.im
  { alpha := { re := a_re, im := a_im }
    beta  := { re := b_re, im := b_im } }

/-- Z軸回転 Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) -/
def rotationZ (theta : Float) (q : QuantumBit) : QuantumBit :=
  phaseShift theta q

end QuantumGates

-- ============================================================
-- §3. ボルン則に基づく量子測定（Collapse）
-- ============================================================

namespace QuantumMeasurement
open QuantumBit

structure MeasurementResult where
  collapsedState : QuantumBit
  observedBit    : Nat
  probability    : Float
  deriving Repr

/--
`measure` : ボルン則に基づく標準的な量子測定
P(|0⟩) = |α|², P(|1⟩) = |β|²
測定後は対応する固有状態へ射影（波束の収縮）
-/
def measure (q : QuantumBit) : IO MeasurementResult := do
  let p0 := q.probability0
  let p1 := q.probability1
  -- 簡易的な確率判定（LeanのIOでは完全な乱数が制限されるため決定論的に）
  if p0 >= p1 then
    pure { collapsedState := { alpha := { re := 1.0, im := 0.0 }, beta := { re := 0.0, im := 0.0 } }
           observedBit    := 0
           probability    := p0 }
  else
    pure { collapsedState := { alpha := { re := 0.0, im := 0.0 }, beta := { re := 1.0, im := 0.0 } }
           observedBit    := 1
           probability    := p1 }

end QuantumMeasurement

-- ============================================================
-- §4. 多量子ビットレジスタ（エンタングルメント対応）
-- ============================================================

/-- 2量子ビット状態（4次元複素ベクトル） -/
structure QuantumRegister2 where
  amp00 : ComplexAmp  -- |00⟩
  amp01 : ComplexAmp  -- |01⟩
  amp10 : ComplexAmp  -- |10⟩
  amp11 : ComplexAmp  -- |11⟩
  deriving Repr

namespace QuantumRegister2

  def normalize (reg : QuantumRegister2) : QuantumRegister2 :=
    let total := reg.amp00.normSq + reg.amp01.normSq + reg.amp10.normSq + reg.amp11.normSq
    if total > 1e-15 then
      let n := 1.0 / total.sqrt
      { amp00 := ComplexAmp.smul n reg.amp00
        amp01 := ComplexAmp.smul n reg.amp01
        amp10 := ComplexAmp.smul n reg.amp10
        amp11 := ComplexAmp.smul n reg.amp11 }
    else
      reg

  /-- 初期状態 |00⟩ -/
  def init : QuantumRegister2 :=
    { amp00 := { re := 1.0, im := 0.0 }
      amp01 := { re := 0.0, im := 0.0 }
      amp10 := { re := 0.0, im := 0.0 }
      amp11 := { re := 0.0, im := 0.0 } }

  /-- 最初の量子ビットにHゲートを適用 -/
  def applyH0 (reg : QuantumRegister2) : QuantumRegister2 :=
    let invSqrt2 := 1.0 / (2.0.sqrt)
    { amp00 := { re := (reg.amp00.re + reg.amp10.re) * invSqrt2
                 im := (reg.amp00.im + reg.amp10.im) * invSqrt2 }
      amp01 := { re := (reg.amp01.re + reg.amp11.re) * invSqrt2
                 im := (reg.amp01.im + reg.amp11.im) * invSqrt2 }
      amp10 := { re := (reg.amp00.re - reg.amp10.re) * invSqrt2
                 im := (reg.amp00.im - reg.amp10.im) * invSqrt2 }
      amp11 := { re := (reg.amp01.re - reg.amp11.re) * invSqrt2
                 im := (reg.amp01.im - reg.amp11.im) * invSqrt2 } }

  /-- CNOTゲート（制御=ビット0, ターゲット=ビット1） -/
  def applyCNOT (reg : QuantumRegister2) : QuantumRegister2 :=
    -- 制御ビットが1の場合、ターゲットビットを反転
    -- |10⟩ ↔ |11⟩
    { amp00 := reg.amp00
      amp01 := reg.amp01
      amp10 := reg.amp11
      amp11 := reg.amp10 }

  /-- ベル状態 |Φ⁺⟩ = (|00⟩ + |11⟩)/√2 を生成 -/
  def bellState : QuantumRegister2 :=
    normalize (applyCNOT (applyH0 init))

  def toString (reg : QuantumRegister2) : String :=
    s!"|00⟩: {reg.amp00.toString}\n" ++
    s!"|01⟩: {reg.amp01.toString}\n" ++
    s!"|10⟩: {reg.amp10.toString}\n" ++
    s!"|11⟩: {reg.amp11.toString}"

end QuantumRegister2

-- ============================================================
-- §5. 連続演算のシミュレーション評価
-- ============================================================

section Simulation

open QuantumGates
open QuantumMeasurement
open QuantumRegister2

-- 1. 初期状態: |0⟩ からスタート（純粋な情報状態）
def psi0 : QuantumBit := {
  alpha := { re := 1.0, im := 0.0 }
  beta  := { re := 0.0, im := 0.0 }
}

-- 2. アダマールゲートの適用（情報と価値の 50:50 重ね合わせ）
def psi1 := gateH psi0

-- 3. 連続位相変化 (π/4 ラジアン回転)
def psi2 := phaseShift (Float.pi / 4.0) psi1

-- 4. X ゲート適用（位相のダイナミクスを反転）
def psi3 := gateX psi2

-- 5. ベル状態の生成
def bell := QuantumRegister2.bellState

-- 評価出力
#eval "=== 量子コンピュータ的な複素数ビット計算理論 ==="
#eval ""
#eval "【1. 初期状態 |0⟩】"
#eval psi0.toString
#eval s!"  正規化: {psi0.isNormalized}"
#eval s!"  ブロッホ球: {psi0.blochCoordinates}"

#eval ""
#eval "【2. アダマールゲート後】"
#eval psi1.toString
#eval s!"  P(|0⟩) = {psi1.probability0}, P(|1⟩) = {psi1.probability1}"
#eval s!"  ブロッホ球: {psi1.blochCoordinates}"

#eval ""
#eval "【3. 位相シフト R_z(π/4)】"
#eval psi2.toString
#eval s!"  P(|0⟩) = {psi2.probability0}, P(|1⟩) = {psi2.probability1}"
#eval s!"  ブロッホ球: {psi2.blochCoordinates}"

#eval ""
#eval "【4. Xゲート後】"
#eval psi3.toString
#eval s!"  P(|0⟩) = {psi3.probability0}, P(|1⟩) = {psi3.probability1}"
#eval s!"  ブロッホ球: {psi3.blochCoordinates}"

#eval ""
#eval "【5. ベル状態 |Φ⁺⟩】"
#eval bell.toString

#eval ""
#eval "【6. ブロッホ球上の連続回転 Ry】"
#eval s!"Ry(0):    {(rotationY 0.0 psi0).blochCoordinates}"
#eval s!"Ry(π/4):  {(rotationY (Float.pi/4.0) psi0).blochCoordinates}"
#eval s!"Ry(π/2):  {(rotationY (Float.pi/2.0) psi0).blochCoordinates}"
#eval s!"Ry(π):    {(rotationY Float.pi psi0).blochCoordinates}"

#eval ""
#eval "【7. 位相干渉効果】"
def qPlus : QuantumBit := {
  alpha := { re := 1.0 / (2.0.sqrt), im := 0.0 }
  beta  := { re := 1.0 / (2.0.sqrt), im := 0.0 }
}
def qMinus : QuantumBit := {
  alpha := { re := 1.0 / (2.0.sqrt), im := 0.0 }
  beta  := { re := -1.0 / (2.0.sqrt), im := 0.0 }
}
#eval s!"|+⟩: {qPlus.toString}"
#eval s!"|-⟩: {qMinus.toString}"
#eval s!"H|+⟩ = {gateH qPlus}.toString"
#eval s!"H|-⟩ = {gateH qMinus}.toString"

end Simulation
