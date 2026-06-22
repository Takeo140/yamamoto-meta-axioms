-- =============================================================================
-- ComplexBit Ultra Core: High-Speed Pure Execution Artifact
-- 
-- Author: Takeo Yamamoto (ORCID: 0009-0003-0440-474X)
-- License: CC BY 4.0　Apache 2.0
-- =============================================================================

import Std.Data.UInt64

/-!
# 実行特化型エンジン (Pure Execution Artifact)
形式証明によって安全性が担保されたロジックから、純粋な演算部分のみを抽出。
Lean 4コンパイラを介してC/C++やRustから直接呼び出し可能なゼロオーバーヘッド・バイナリを生成します。
-/

-- ============================================================
-- §1. Memory-Aligned Structures (メモリレイアウト最適化構造体)
-- ============================================================

structure ComplexBit where
  real : UInt64
  imag : UInt64
  deriving Repr, DecidableEq, Inhabited

structure QuatBit where
  w : UInt64
  x : UInt64
  y : UInt64
  z : UInt64
  deriving Repr, DecidableEq, Inhabited

structure BSCMStateCB where
  state : ComplexBit
  bound : UInt64
  step  : UInt64
  deriving Repr

-- ============================================================
-- §2. Branchless Core Logic (完全分岐排除・ビット演算コア)
-- ============================================================

@[inline]
def nonzeroMask (x : UInt64) : UInt64 :=
  (x.wrappingNeg ||| x) >>> 63

@[inline]
def zeroMask (x : UInt64) : UInt64 :=
  1 - nonzeroMask x

@[inline, export branchless_add_c]
def branchlessAdd (val control delta : UInt64) : UInt64 :=
  val + delta * nonzeroMask control

@[inline, export branchless_select_c]
def branchlessSelect (control a b : UInt64) : UInt64 :=
  let m := nonzeroMask control
  a * m + b * (1 - m)

@[inline, export branchless_logic_fast_v2_c]
def branchlessLogicFastV2 (val : UInt64) (control : UInt64) : UInt64 :=
  branchlessAdd val control 1

-- ============================================================
-- §3. Complex & Quaternion Algebra (複素・四元数 代数演算)
-- ============================================================

namespace ComplexBit

@[inline, export complex_bit_add_c]
def add (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real + c2.real, imag := c1.imag + c2.imag }

@[inline, export complex_bit_mul_c]
def mul (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real * c2.real - c1.imag * c2.imag,
    imag := c1.real * c2.imag + c1.imag * c2.real }

@[inline]
def rotate90 (c : ComplexBit) : ComplexBit :=
  { real := c.imag.wrappingNeg, imag := c.real }

@[inline]
def normSq (c : ComplexBit) : UInt64 :=
  c.real * c.real + c.imag * c.imag

end ComplexBit

namespace QuatBit

@[inline, export quat_bit_mul_c]
def mul (q1 q2 : QuatBit) : QuatBit :=
  { w := q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z
    x := q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y
    y := q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x
    z := q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w }

end QuatBit

-- ============================================================
-- §4. BSCM Execution Engine (BSCM 実行エンジン)
-- ============================================================

/-- 
1ステップの実行。インライン化と完全分岐排除により、
パイプラインストール（CPUの分岐予測ミス）を物理的に回避します。
-/
@[inline]
def bscmStepCB (s : BSCMStateCB) : BSCMStateCB :=
  let n := s.state.real
  let odd_mask    := n &&& 1
  let even_result := n >>> 1
  let odd_result  := 3 * n + 1
  let next_n      := branchlessSelect odd_mask odd_result even_result
  
  { state := { real := next_n, imag := s.state.imag + 1 }
    bound := s.bound
    step  := s.step + 1 }

/-- 
外部からの呼び出し用エントリーポイント。
Rustの `for` ループと同等の、スタックを消費しない末尾再帰（Tail Call Optimization）処理。
-/
@[export bscm_run_cb_c]
def bscmRunCB (init : BSCMStateCB) (n : UInt64) : BSCMStateCB :=
  go init n
where
  @[specialize] go (s : BSCMStateCB) (remaining : UInt64) : BSCMStateCB :=
    if remaining == 0 || s.step >= s.bound then 
      s
    else
      go (bscmStepCB s) (remaining - 1)
