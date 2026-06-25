/-!
# ComplexQuantum Phase Space Simulator
# 連続位相空間における量子ビット演算ライブラリ

Copyright (c) 2026 Yamamoto Takeo
ORCID: 0009-0003-0440-474X
License: Apache License 2.0 / CC BY 4.0

## 理論的位置づけ
本モジュールは、情報（Real）と価値（Imag）を連続的な複素確率振幅として捉え、
ブロッホ球（位相空間）上の回転運動として量子ゲートを再定義する。
測定は、最小作用の原理に基づき、確率が最大の経路へ状態を崩壊させる。
-/

/--
### §1. 連続複素数と量子状態の定義
-/
structure Complex where
  re : Float
  im : Float
  deriving Repr, Inhabited

namespace Complex
  def normSq (c : Complex) : Float :=
    c.re * c.re + c.im * c.im

  def add (c1 c2 : Complex) : Complex :=
    { re := c1.re + c2.re, im := c1.im + c2.im }

  def mul (c1 c2 : Complex) : Complex :=
    { re := c1.re * c2.re - c1.im * c2.im
      im := c1.re * c2.im + c1.im * c2.re }
end Complex

/--
`QuantumBit` : 連続位相空間上の1量子ビット状態
  alpha : |0⟩ (情報基底) の確率振幅
  beta  : |1⟩ (価値基底) の確率振幅
-/
structure QuantumBit where
  alpha : Complex
  beta  : Complex
  deriving Repr, Inhabited

namespace QuantumBit
  -- 状態の全確率（ノルムの総和）が 1.0 に正規化されているか検証
  def isNormalized (q : QuantumBit) (epsilon : Float := 1e-5) : Bool :=
    let total := q.alpha.normSq + q.beta.normSq
    (total - 1.0).abs < epsilon
end QuantumBit

/--
## §2. 連続位相幾何ゲート群
任意の回転角 `theta` を用いた、位相空間上の連続演算。
-/
namespace QuantumGates
open Complex

/-- 任意の位相シフトゲート (R_z ゲート)
    情報と価値の位相関係を連続的に変化させる -/
def phaseShift (theta : Float) (q : QuantumBit) : QuantumBit :=
  let rot := { re := theta.cos, im := theta.sin : Complex }
  { alpha := q.alpha
    beta  := Complex.mul q.beta rot }

/-- 連続的アダマールゲート (H gate)
    情報と価値を等重みの重ね合わせ状態（赤道面）へ射影する -/
def gateH (q : QuantumBit) : QuantumBit :=
  let invSqrt2 := 1.0 / (2.0.sqrt)
  let a_re := (q.alpha.re + q.beta.re) * invSqrt2
  let a_im := (q.alpha.im + q.beta.im) * invSqrt2
  let b_re := (q.alpha.re - q.beta.re) * invSqrt2
  let b_im := (q.alpha.im - q.beta.im) * invSqrt2
  { alpha := { re := a_re, im := a_im }
    beta  := { re := b_re, im := b_im } }

/-- パウリ X ゲート（ビット反転） -/
def gateX (q : QuantumBit) : QuantumBit :=
  { alpha := q.beta, beta := q.alpha }

end QuantumGates

/--
## §3. 極値原理による量子測定（Collapse）
位相空間において、作用積分（確率振幅の二乗ノルム）が
最大の経路へと系が非分岐的に決定（射影）されるプロセスをシミュレート。
-/
namespace ExtremalMeasurement
open QuantumBit

structure MeasurementResult where
  collapsedState : QuantumBit
  observedBit    : Nat

/--
`measureLeastAction` : 最小作用（最大確率）経路の選択アルゴリズム
古典的な乱数測定ではなく、決定論的に「現時点で最も作用の大きい（優位な）固有状態」
へと射影する極値原理モデル。
-/
def measureLeastAction (q : QuantumBit) : MeasurementResult :=
  let p0 := q.alpha.normSq
  let p1 := q.beta.normSq
  if p0 >= p1 then
    -- |0⟩ (情報優位) への崩壊
    { collapsedState := { alpha := { re := 1.0, im := 0.0 }, beta := { re := 0.0, im := 0.0 } }
      observedBit    := 0 }
  else
    -- |1⟩ (価値優位) への崩壊
    { collapsedState := { alpha := { re := 0.0, im := 0.0 }, beta := { re := 1.0, im := 0.0 } }
      observedBit    := 1 }

end ExtremalMeasurement

/--
## §4. 連続演算のシミュレーション評価
-/
section Simulation

open QuantumGates
open ExtremalMeasurement

-- 1. 初期状態: |0⟩ からスタート（純粋な情報状態）
def psi0 : QuantumBit := {
  alpha := { re := 1.0, im := 0.0 }
  beta  := { re := 0.0, im := 0.0 }
}

-- 2. アダマールゲートの適用（情報と価値の 50:50 重ね合わせ位相空間の生成）
def psi1 := gateH psi0
#eval psi1
-- 期待値: alpha = (0.707, 0), beta = (0.707, 0)

-- 3. 連続位相変化 (例: pi/4 = 0.785398 ラジアン回転)
-- これにより、複素平面上で「価値」の軸が連続的に傾く
def psi2 := phaseShift 0.785398 psi1
#eval psi2

-- 4. さらに X ゲートを適用し、位相のダイナミクスを反転
def psi3 := gateX psi2
#eval psi3

-- 5. 極値原理に基づく最終測定（作用最大経路への収縮）
def result := measureLeastAction psi3
#eval result.observedBit
#eval result.collapsedState

end Simulation
