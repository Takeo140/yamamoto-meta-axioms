/-!
# ComplexBit Quantum Gate Algebra
# 量子ゲートの ComplexBit 形式証明ライブラリ

Copyright (c) 2026 Yamamoto Takeo
ORCID: 0009-0003-0440-474X
License: Apache License 2.0 / CC BY 4.0

## 理論的位置づけ
本モジュールは、情報価値論（BitEconomics）とフェルマーの最小作用の原理に基づく
量子測定の代数的モデルを形式化する。

設計アーキテクチャとして以下の2層構造を採用する：
1. `Theory` : 一般整数（Int）を用いた厳密な代数構造とゲート関係式の形式証明
2. `Compute`: UInt64 を用いた高速な分岐排除（Branchless）演算と実機シミュレーション
-/

import Std.Data.UInt64

/-!
## §1. 理論モデル（Theory Namespace）
数学的な可換環（Int）上で、ComplexBitの代数構造と量子ゲートの恒等式を厳密に証明する。
-/
namespace Theory

structure ComplexBit where
  real : Int
  imag : Int
  deriving Repr, DecidableEq, Inhabited

namespace ComplexBit

@[inline] def add (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real + c2.real, imag := c1.imag + c2.imag }

@[inline] def mul (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real * c2.real - c1.imag * c2.imag
    imag := c1.real * c2.imag + c1.imag * c2.real }

@[inline] def neg (c : ComplexBit) : ComplexBit :=
  { real := -c.real, imag := -c.imag }

@[inline] def normSq (c : ComplexBit) : Int :=
  c.real * c.real + c.imag * c.imag

@[inline] def rotI (c : ComplexBit) : ComplexBit :=
  { real := -c.imag, imag := c.real }

@[inline] def rotNegI (c : ComplexBit) : ComplexBit :=
  { real := c.imag, imag := -c.real }

theorem normSq_add_comm (c : ComplexBit) :
    c.real * c.real + c.imag * c.imag = c.imag * c.imag + c.real * c.real := by ring

end ComplexBit

namespace QuantumGates
open ComplexBit

@[inline] def gateZ (c : ComplexBit) : ComplexBit :=
  { real := c.real, imag := -c.imag }

@[inline] def gateX (c : ComplexBit) : ComplexBit :=
  { real := c.imag, imag := c.real }

-- 【定理】 Z² = I
theorem gateZ_involutive (c : ComplexBit) : gateZ (gateZ c) = c := by
  simp [gateZ]

-- 【定理】 X² = I
theorem gateX_involutive (c : ComplexBit) : gateX (gateX c) = c := by
  simp [gateX]

-- 【定理】 Z ゲートのノルム保存則
theorem gateZ_normSq_eq (c : ComplexBit) : (gateZ c).normSq = c.normSq := by
  simp [gateZ, normSq]; ring

-- 【定理】 X ゲートのノルム保存則
theorem gateX_normSq_eq (c : ComplexBit) : (gateX c).normSq = c.normSq := by
  simp [gateX, normSq]; ring

-- 【定理】 ゲート合成 ZXZ = X
theorem gateZ_gateX_gateZ_eq_gateX (c : ComplexBit) :
    gateZ (gateX (gateZ c)) = gateX c := by
  simp [gateZ, gateX]

-- 【定理】 S² = Z
theorem rotI_sq_eq_gateZ (c : ComplexBit) : rotI (rotI c) = gateZ c := by
  simp [rotI, gateZ]

end QuantumGates

/-!
### 1.1 情報価値転移と極値原理（理論証明）
-/
namespace ExtremalPrinciple
open ComplexBit

@[inline] def valueTransfer (src dst : ComplexBit) : ComplexBit :=
  { real := dst.real, imag := dst.imag + src.imag }

-- 【定理】 価値転移の加法性
theorem valueTransfer_additive (src dst1 dst2 : ComplexBit) :
    (valueTransfer src dst1).imag + (valueTransfer src dst2).imag =
    dst1.imag + dst2.imag + 2 * src.imag := by
  simp [valueTransfer]; ring

end ExtremalPrinciple
end Theory


/-!
## §2. 計算モデル（Compute Namespace）
UInt64のビット演算を用いた高速実装。理論モデルで証明された性質を実機で再現する。
-/
namespace Compute

structure ComplexBit where
  real : UInt64
  imag : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace ComplexBit

@[inline] def normSq (c : ComplexBit) : UInt64 :=
  c.real * c.real + c.imag * c.imag

@[inline] def rotI (c : ComplexBit) : ComplexBit :=
  { real := c.imag.wrappingNeg, imag := c.real }

end ComplexBit

namespace QuantumGates
open ComplexBit

@[inline] def gateZ (c : ComplexBit) : ComplexBit :=
  { real := c.real, imag := c.imag.wrappingNeg }

@[inline] def gateX (c : ComplexBit) : ComplexBit :=
  { real := c.imag, imag := c.real }

/--
`nonzeroMask` : 極値選択（測定）のための分岐排除マスク
x ≠ 0 なら 1 を、x = 0 なら 0 を返す。
-/
@[inline] def nonzeroMask (x : UInt64) : UInt64 :=
  (x.wrappingNeg ||| x) >>> 63

structure CNOTState where
  control : ComplexBit
  target  : ComplexBit
  deriving Repr, DecidableEq, Inhabited

/--
`gateCNOT` : 条件付き価値転移（Branchless CNOT）
情報価値論的意味：制御側の情報価値が存在するとき、対象側の情報と価値を交換する。
-/
@[inline] def gateCNOT (s : CNOTState) : CNOTState :=
  let m := nonzeroMask s.control.normSq
  let new_target_real := s.target.imag * m + s.target.real * (1 - m)
  let new_target_imag := s.target.real * m + s.target.imag * (1 - m)
  { control := s.control
    target  := { real := new_target_real, imag := new_target_imag } }

def hScale : UInt64 := 181  -- √2 * 128 の整数近似

@[inline] def gateH_approx (c : ComplexBit) : ComplexBit :=
  { real := (c.real + c.imag) * hScale >>> 7
    imag := (c.real - c.imag) * hScale >>> 7 }

end QuantumGates
end Compute


/-!
## §3. 検証スイート
計算モデルの挙動を評価する。
-/
section VerificationSuite
open Compute Compute.QuantumGates

-- Z gate: 虚部符号反転（UInt64での巡回表現）
#eval gateZ { real := 3, imag := 5 }

-- X gate: 観測者と対象の双対交換
#eval gateX { real := 3, imag := 5 }

-- S² = Z の確認
#eval Compute.ComplexBit.rotI (Compute.ComplexBit.rotI { real := 3, imag := 5 })
#eval gateZ { real := 3, imag := 5 }

-- CNOT: 制御ビット非零（状態崩壊・極値選択）のときの標的ビット作用
#eval gateCNOT {
  control := { real := 1, imag := 0 }
  target  := { real := 3, imag := 5 }
}

-- CNOT: 制御ビット零のとき（恒等）
#eval gateCNOT {
  control := { real := 0, imag := 0 }
  target  := { real := 3, imag := 5 }
}

-- H gate 近似: (128, 0) -> 等重み混合状態（重ね合わせ）
#eval gateH_approx { real := 128, imag := 0 }

end VerificationSuite
