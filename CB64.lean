/-
ComplexBit Ultra Core: Unified Algebraic-Geometric Branchless Engine
with Complete Formal Verification (Practical Lean Edition)

Copyright (c) 2026 Yamamoto Takeo
License: Apache License 2.0 / CC BY 4.0
-/

import Lean.Data.Format
import Std.Tactic.BVDecide

/-- C/Rust の `u64` に対応する 64bit ビットベクトル -/
abbrev U64 := BitVec 64

/-! # §1. U64 ビット演算補題と branchless コア -/

namespace U64Lemmas

/--
【補題 1.1】非ゼロ U64 に対するビットトリック
`x ≠ 0` ならば `((-x) ||| x) >>> 63 = 1`
-/
theorem neg_or_self_msb (x : U64) (hx : x ≠ 0) :
    (-x ||| x) >>> 63 = 1 := by
  revert x hx
  bv_decide

/--
【補題 1.2】ゼロに対するビットトリック（自明ケース）
-/
@[simp] theorem neg_or_zero_msb : (- (0 : U64) ||| 0) >>> 63 = 0 := by
  bv_decide

/--
【補題 1.3】MSB の値は常に 0 または 1
-/
theorem msb_val_binary (x : U64) :
    (-x ||| x) >>> 63 = 0 ∨ (-x ||| x) >>> 63 = 1 := by
  bv_decide

end U64Lemmas

/-- 非ゼロ判定を 0/1 マスクに変換する branchless ビットトリック -/
@[inline] def nonzeroMask (x : U64) : U64 :=
  (-x ||| x) >>> 63

@[simp] theorem nonzeroMask_zero : nonzeroMask (0 : U64) = 0 := by
  simp [nonzeroMask]
  bv_decide

/-- 非ゼロならマスクは 1 になる -/
theorem nonzeroMask_nonzero (x : U64) (hx : x ≠ 0) : nonzeroMask x = 1 := by
  exact U64Lemmas.neg_or_self_msb x hx

/-- ゼロマスク：`nonzeroMask` の補集合 -/
@[inline] def zeroMask (x : U64) : U64 :=
  1 - nonzeroMask x

/-- 分岐排除選択器：`control ≠ 0` なら `a`、そうでなければ `b` を返す -/
@[inline] def branchlessSelect (control a b : U64) : U64 :=
  let m := nonzeroMask control
  a * m + b * (1 - m)

/-- `branchlessSelect` の正当性：`if control ≠ 0 then a else b` と一致 -/
theorem branchlessSelect_correct (control a b : U64) :
    branchlessSelect control a b = (if control ≠ 0 then a else b) := by
  simp only [branchlessSelect]
  by_cases h : control = 0
  · subst h
    simp [nonzeroMask_zero]
  · have hm : nonzeroMask control = 1 := nonzeroMask_nonzero control h
    simp [h, hm]

/-! # §2. ComplexBit：代数構造付き複素数ビット型 -/

structure ComplexBit where
  real : U64
  imag : U64
  deriving Repr, DecidableEq, Inhabited

namespace ComplexBit

/-- 複素数ビットの加算 -/
@[inline] def add (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real + c2.real, imag := c1.imag + c2.imag }

instance : Add ComplexBit := ⟨add⟩

/-- 複素数ビットの乗算（オーバーフロー込みの擬似複素数環） -/
@[inline] def mul (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real * c2.real - c1.imag * c2.imag
    imag := c1.real * c2.imag + c1.imag * c2.real }

instance : Mul ComplexBit := ⟨mul⟩

/-- 零元 -/
def zero : ComplexBit := { real := 0, imag := 0 }
instance : Zero ComplexBit := ⟨zero⟩

/-- 単位元（1） -/
def one : ComplexBit := { real := 1, imag := 0 }
instance : One ComplexBit := ⟨one⟩

/-- 虚数単位 `I` -/
def I : ComplexBit := { real := 0, imag := 1 }

/-- 符号反転 -/
@[inline] def neg (c : ComplexBit) : ComplexBit :=
  { real := -c.real, imag := -c.imag }
instance : Neg ComplexBit := ⟨neg⟩

/-- 実部だけから ComplexBit を作る -/
def ofReal (x : U64) : ComplexBit :=
  { real := x, imag := 0 }

/-- 虚部だけから ComplexBit を作る -/
def ofImag (y : U64) : ComplexBit :=
  { real := 0, imag := y }

/-- 共役複素数 -/
@[inline] def conj (c : ComplexBit) : ComplexBit :=
  { real := c.real, imag := -c.imag }

@[simp] theorem conj_conj (c : ComplexBit) : conj (conj c) = c := by
  simp only [conj, neg]
  constructor <;> simp [BitVec.neg_neg]

/-- 90度回転（`i` を掛けるのに対応） -/
@[inline] def rotate90 (c : ComplexBit) : ComplexBit :=
  { real := -c.imag, imag := c.real }

/-- `I² = -1`（虚数単位の定義的性質） -/
theorem I_sq : I * I = -1 := by
  simp only [I, mul, one, neg, HMul.hMul, Mul.mul]
  constructor <;> bv_decide

/-- 90度回転を 4 回繰り返すと元に戻る -/
theorem rotate90_four_eq_id (c : ComplexBit) :
    c.rotate90.rotate90.rotate90.rotate90 = c := by
  simp only [rotate90, neg]
  constructor <;> simp [BitVec.neg_neg]

end ComplexBit

/-! # §3. QuatBit：四元数ビット構造 -/

structure QuatBit where
  w : U64
  x : U64
  y : U64
  z : U64
  deriving Repr, DecidableEq, Inhabited

namespace QuatBit

def zero : QuatBit := { w := 0, x := 0, y := 0, z := 0 }
def one  : QuatBit := { w := 1, x := 0, y := 0, z := 0 }
instance : Zero QuatBit := ⟨zero⟩
instance : One  QuatBit := ⟨one⟩

/-- 符号反転（`ji_eq_neg_k` で必要） -/
@[inline] def neg (q : QuatBit) : QuatBit :=
  { w := -q.w, x := -q.x, y := -q.y, z := -q.z }
instance : Neg QuatBit := ⟨neg⟩

/-- Hamilton 積（オーバーフロー込み四元数積） -/
@[inline] def mul (q1 q2 : QuatBit) : QuatBit :=
  { w := q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z
    x := q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y
    y := q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x
    z := q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w }

instance : Mul QuatBit := ⟨mul⟩

def unitI : QuatBit := { w := 0, x := 1, y := 0, z := 0 }
def unitJ : QuatBit := { w := 0, x := 0, y := 1, z := 0 }
def unitK : QuatBit := { w := 0, x := 0, y := 0, z := 1 }

/-- `i * j = k` -/
theorem ij_eq_k : unitI * unitJ = unitK := by rfl

/-- `j * i = -k`（非可換性の例） -/
theorem ji_eq_neg_k : unitJ * unitI = -unitK := by rfl

/-- `i² = -1` -/
theorem unitI_sq : unitI * unitI = -one := by rfl

/-- `j² = -1` -/
theorem unitJ_sq : unitJ * unitJ = -one := by rfl

/-- `k² = -1` -/
theorem unitK_sq : unitK * unitK = -one := by rfl

end QuatBit

/-! # §4. BitLayer 型クラス：ビットレイヤー抽象 -/

class BitLayer (α : Type) where
  inject  : U64 → α
  extract : α → U64
  liftOp  : (U64 → U64) → α → α
  add     : α → α → α
  extract_inject : ∀ (x : U64), extract (inject x) = x

instance : BitLayer U64 where
  inject  := id
  extract := id
  liftOp  := id
  add     := (· + ·)
  extract_inject := fun _ => rfl

instance : BitLayer ComplexBit where
  inject  := fun x => { real := x, imag := 0 }
  extract := fun c => c.real
  liftOp  := fun f c => { real := f c.real, imag := c.imag }
  add     := ComplexBit.add
  extract_inject := fun _ => rfl

/-! # §5. BSCM：Bounded Smooth Collatz Machine（複素数ビット版） -/

structure BSCMStateCB where
  state : ComplexBit
  bound : U64
  step  : U64
  deriving Repr

/-- 1 ステップ分の Collatz 風更新（分岐排除＋バウンドチェック付き） -/
def bscmStepCB (s : BSCMStateCB) : Option BSCMStateCB :=
  if s.step ≥ s.bound then
    none
  else
    let n := s.state.real
    let odd_mask    := n &&& 1
    let even_result := n >>> 1
    let odd_result  := 3 * n + 1
    let next_n := branchlessSelect odd_mask odd_result even_result
    some {
      state := { real := next_n, imag := s.state.imag + 1 }
      bound := s.bound
      step  := s.step + 1
    }

/-- BSCM のステップ数に関する有界性定理 -/
theorem bscmStepCB_step_bounded (s : BSCMStateCB) :
    match bscmStepCB s with
    | none    => s.step ≥ s.bound
    | some s' => s'.step = s.step + 1 := by
  simp only [bscmStepCB]
  split_ifs with h
  · exact h
  · simp

/-- バウンドを超えたら `none` を返すことの直接証明 -/
theorem bscmStepCB_none_iff (s : BSCMStateCB) :
    bscmStepCB s = none ↔ s.step ≥ s.bound := by
  simp [bscmStepCB]
  split_ifs with h
  · simp [h]
  · simp [h]

/-! # §6. 動作確認用 example -/

-- branchlessSelect の基本動作
example : branchlessSelect (1 : U64) (10 : U64) (20 : U64) = 10 := by
  have hm : nonzeroMask (1 : U64) = 1 := nonzeroMask_nonzero 1 (by decide)
  simp [branchlessSelect, hm]

example : branchlessSelect (0 : U64) (10 : U64) (20 : U64) = 20 := by
  simp [branchlessSelect, nonzeroMask_zero]

-- conj の involution
example (c : ComplexBit) :
    ComplexBit.conj (ComplexBit.conj c) = c :=
  ComplexBit.conj_conj c

-- rotate90 の 4 周期性
example (c : ComplexBit) :
    c.rotate90.rotate90.rotate90.rotate90 = c :=
  ComplexBit.rotate90_four_eq_id c

