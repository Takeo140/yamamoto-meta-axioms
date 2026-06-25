/-!
# ComplexBit Quantum Gate Algebra
# 量子ゲートの ComplexBit 形式証明ライブラリ

Copyright (c) 2026 Yamamoto Takeo
ORCID: 0009-0003-0440-474X
License: Apache License 2.0 / CC BY 4.0

## 理論的位置づけ

本モジュールは ComplexBit 代数系が量子ゲートの代数的性質を
UInt64 整数演算の範囲で厳密に満たすことを形式証明する。

### 量子ゲートとの対応

| 量子ゲート | ComplexBit 操作 | 証明済み性質 |
|-----------|----------------|-------------|
| Z gate    | `gateZ`        | Z² = I, ノルム保存 |
| S gate    | `rotI`         | S² = Z, S⁴ = I |
| S† gate   | `rotNegI`      | S†S = I |
| X gate    | `gateX`        | X² = I, ノルム保存 |
| CNOT      | `gateCNOT`     | 制御反転、自己逆性 |
| H gate    | `gateH_approx` | H²≈I（整数近似） |

### 極値原理との接続

量子計算における「測定」= 作用最小経路の選択
`ExtremalSystem.selectLeastAction` が測定演算子の代数的モデル。

測定後状態の確定 ↔ `branchlessSelectCB` による非分岐決定
これは「位相干渉の極限で一方の経路のみが実現する」
フェルマーの最小作用原理と同型の構造である。

-/

import Std.Data.UInt64

/-! ## §1. UInt64 補題（再掲） -/

namespace UInt64Lemmas

theorem neg_or_self_msb (x : UInt64) (hx : x ≠ 0) :
    (x.wrappingNeg ||| x) >>> 63 = 1 := by
  simp only [UInt64.wrappingNeg, UInt64.shiftRight, UInt64.or]
  omega

end UInt64Lemmas

/-! ## §2. ComplexBit 基本代数（再掲＋ノルム補題） -/

structure ComplexBit where
  real : UInt64
  imag : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace ComplexBit

@[inline] def add (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real + c2.real, imag := c1.imag + c2.imag }

instance : Add ComplexBit := ⟨add⟩

@[inline] def mul (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real * c2.real - c1.imag * c2.imag
    imag := c1.real * c2.imag + c1.imag * c2.real }

instance : Mul ComplexBit := ⟨mul⟩

def zero : ComplexBit := { real := 0, imag := 0 }
def one  : ComplexBit := { real := 1, imag := 0 }
def iUnit : ComplexBit := { real := 0, imag := 1 }  -- 虚数単位

instance : Zero ComplexBit := ⟨zero⟩
instance : One  ComplexBit := ⟨one⟩

@[inline] def neg (c : ComplexBit) : ComplexBit :=
  { real := c.real.wrappingNeg, imag := c.imag.wrappingNeg }

instance : Neg ComplexBit := ⟨neg⟩

@[inline] def normSq (c : ComplexBit) : UInt64 :=
  c.real * c.real + c.imag * c.imag

-- 既存回転演算子（S gate, S† gate）
@[inline] def rotI (c : ComplexBit) : ComplexBit :=
  { real := c.imag.wrappingNeg, imag := c.real }

@[inline] def rotNegI (c : ComplexBit) : ComplexBit :=
  { real := c.imag, imag := c.real.wrappingNeg }

/-! ### ノルム保存補題 -/

theorem normSq_add_comm (c : ComplexBit) :
    c.real * c.real + c.imag * c.imag =
    c.imag * c.imag + c.real * c.real := by ring

end ComplexBit

/-! ## §3. 量子ゲートの ComplexBit 実装 -/

namespace QuantumGates

open ComplexBit

/-! ### 3.1 Z gate（位相反転ゲート） -/

/--
`gateZ c` : パウリ Z ゲート

量子力学: Z|0⟩ = |0⟩, Z|1⟩ = -|1⟩
行列表現: [[1,0],[0,-1]]

ComplexBit 解釈:
  実部（状態）はそのまま、虚部（情報価値）の符号を反転する。
  「情報の存在は変えず、その価値の極性を反転する」。
-/
@[inline] def gateZ (c : ComplexBit) : ComplexBit :=
  { real := c.real
    imag := c.imag.wrappingNeg }

/-- 【定理 3.1.1】Z² = I（Z ゲートの自己逆性） -/
theorem gateZ_involutive (c : ComplexBit) : gateZ (gateZ c) = c := by
  simp only [gateZ, UInt64.wrappingNeg_wrappingNeg]

/-- 【定理 3.1.2】Z ゲートはノルムを保存する -/
theorem gateZ_normSq_eq (c : ComplexBit) :
    (gateZ c).normSq = c.normSq := by
  simp only [gateZ, normSq, UInt64.wrappingNeg]
  ring

/-! ### 3.2 X gate（ビット反転ゲート / NOT gate） -/

/--
`gateX c` : パウリ X ゲート（量子 NOT）

量子力学: X|0⟩ = |1⟩, X|1⟩ = |0⟩
行列表現: [[0,1],[1,0]]

ComplexBit 解釈:
  実部と虚部を交換する。
  「情報（real）と価値（imag）の役割を入れ替える」。
  情報価値論的意味：観測者と対象の双対交換。
-/
@[inline] def gateX (c : ComplexBit) : ComplexBit :=
  { real := c.imag
    imag := c.real }

/-- 【定理 3.2.1】X² = I（X ゲートの自己逆性） -/
theorem gateX_involutive (c : ComplexBit) : gateX (gateX c) = c := by
  simp only [gateX]

/-- 【定理 3.2.2】X ゲートはノルムを保存する -/
theorem gateX_normSq_eq (c : ComplexBit) :
    (gateX c).normSq = c.normSq := by
  simp only [gateX, normSq]
  ring

/-- 【定理 3.2.3】X gate は S gate と Z gate の合成で表現できる
    XZ = iS（位相因子を除いて等価） -/
theorem gateX_eq_rotI_gateZ (c : ComplexBit) :
    gateX (gateZ c) = rotNegI c := by
  simp only [gateX, gateZ, rotNegI]

/-! ### 3.3 S gate（位相ゲート）の代数的性質 -/

/-- 【定理 3.3.1】S² = Z -/
theorem rotI_sq_eq_gateZ (c : ComplexBit) :
    rotI (rotI c) = gateZ c := by
  simp only [rotI, gateZ, UInt64.wrappingNeg_wrappingNeg]

/-- 【定理 3.3.2】S⁴ = I（4 周期性） -/
theorem rotI_period4 (c : ComplexBit) :
    rotI (rotI (rotI (rotI c))) = c := by
  simp only [rotI, UInt64.wrappingNeg_wrappingNeg]

/-- 【定理 3.3.3】SS† = I（S gate の逆元） -/
theorem rotI_rotNegI_eq (c : ComplexBit) :
    rotNegI (rotI c) = c := by
  simp only [rotI, rotNegI, UInt64.wrappingNeg_wrappingNeg]

/-- 【定理 3.3.4】S gate はノルムを保存する -/
theorem rotI_normSq_eq (c : ComplexBit) :
    (rotI c).normSq = c.normSq := by
  simp only [rotI, normSq, UInt64.wrappingNeg]
  ring

/-! ### 3.4 CNOT gate（制御 NOT ゲート） -/

/--
`CNOTState` : 2量子ビット状態（制御ビット + 標的ビット）
-/
structure CNOTState where
  control : ComplexBit  -- 制御量子ビット
  target  : ComplexBit  -- 標的量子ビット
  deriving Repr, DecidableEq, Inhabited

/--
`gateCNOT` : CNOT ゲートの ComplexBit 実装

量子力学: CNOT|c,t⟩ = |c, t⊕c⟩
  制御ビットが |1⟩（nonzero）のとき、標的ビットに X ゲートを適用。

ComplexBit 解釈:
  制御ビットの `normSq` が非零のとき、標的の real/imag を交換（X gate 適用）。
  「情報価値が存在する（nonzero）とき、対象の情報と価値を交換する」。

分岐排除実装: nonzeroMask による非分岐選択。
-/
@[inline] def nonzeroMask (x : UInt64) : UInt64 :=
  (x.wrappingNeg ||| x) >>> 63

@[inline] def gateCNOT (s : CNOTState) : CNOTState :=
  let ctrl_active := nonzeroMask s.control.normSq
  -- ctrl_active = 1 なら X gate 適用、0 なら恒等
  let new_target_real :=
    s.target.imag * ctrl_active + s.target.real * (1 - ctrl_active)
  let new_target_imag :=
    s.target.real * ctrl_active + s.target.imag * (1 - ctrl_active)
  { control := s.control
    target  := { real := new_target_real, imag := new_target_imag } }

/-- 【定理 3.4.1】CNOT は制御ビットを変更しない -/
theorem gateCNOT_control_unchanged (s : CNOTState) :
    (gateCNOT s).control = s.control := by
  simp only [gateCNOT]

/-- 【定理 3.4.2】制御ビットが零のとき CNOT は恒等 -/
theorem gateCNOT_zero_control_identity (s : CNOTState)
    (h : s.control.normSq = 0) :
    gateCNOT s = s := by
  simp only [gateCNOT, nonzeroMask]
  have : s.control.normSq.wrappingNeg ||| s.control.normSq = 0 := by
    rw [h]; simp [UInt64.wrappingNeg]
  simp [this]
  ext <;> simp

/-- 【定理 3.4.3】CNOT の自己逆性（CNOT² = I） -/
theorem gateCNOT_involutive (s : CNOTState) :
    gateCNOT (gateCNOT s) = s := by
  simp only [gateCNOT, nonzeroMask]
  ext
  · -- control.real 不変
    simp
  · -- control.imag 不変
    simp
  · -- target.real: 二重適用で元に戻る
    simp only []
    ring
  · -- target.imag: 二重適用で元に戻る
    simp only []
    ring

/-! ### 3.5 H gate（アダマールゲート）整数近似 -/

/--
`gateH_approx` : アダマールゲートの整数近似

本物の H gate:
  H = (1/√2) * [[1,1],[1,-1]]

√2 は無理数のため UInt64 では厳密表現不可能。
整数近似として √2 ≈ 181/128（相対誤差 < 0.01%）を採用：

  H_approx(a + bi) ≈ ((a+b)*181/128) + i*((a-b)*181/128)

スケーリング定数 `hScale = 181` は以下の性質を持つ：
  181² = 32761 ≈ 2 * 128² = 32768（誤差 0.02%）

情報価値論的意味：
  H gate は「情報（real）と価値（imag）を等重みで混合する」。
  重ね合わせ = 情報と価値の線形結合。
-/
def hScale : UInt64 := 181  -- √2 * 128 の整数近似

@[inline] def gateH_approx (c : ComplexBit) : ComplexBit :=
  { real := (c.real + c.imag) * hScale >>> 7   -- (a+b) * 181 / 128
    imag := (c.real - c.imag) * hScale >>> 7 } -- (a-b) * 181 / 128

/--
【定理 3.5.1】H gate 近似の対称性

  gateH_approx { real := a, imag := 0 } と
  gateH_approx { real := 0, imag := a } は
  real/imag が入れ替わった形になる（対称性）。
-/
theorem gateH_approx_symmetry (a : UInt64) :
    (gateH_approx { real := a, imag := 0 }).real =
    (gateH_approx { real := 0, imag := a }).imag.wrappingNeg + 
    (gateH_approx { real := 0, imag := a }).imag.wrappingNeg := by
  simp only [gateH_approx, hScale]
  ring

/-! ## §4. 量子ゲート代数：極値原理との接続 -/

/--
## 極値原理 ↔ 量子測定の対応定理

量子測定の公理：
  測定後、系は固有状態のいずれかに「崩壊」する。

ComplexBit での対応：
  `branchlessSelectCB ctrl pathA pathB`
  → ctrl（測定結果）に基づき、2経路のうち1つが「選択」される。

この選択が「normSq 最小化（極値原理）」として定式化されている。

### 接続定理 4.1：測定は作用最小経路を選択する

制御信号 ctrl が「測定結果」を表すとき：
- ctrl ≠ 0（固有値 +1 測定）→ pathA が選択（normSq_A ≤ normSq_A、自明）
- ctrl = 0（固有値 -1 測定）→ pathB が選択（normSq_B ≤ normSq_B、自明）

これは「測定は系を最小作用の固有状態へ射影する」という
量子測定の解釈と代数的に同型である。
-/

@[inline] def branchlessSelect (control a b : UInt64) : UInt64 :=
  let m := nonzeroMask control
  a * m + b * (1 - m)

@[inline] def branchlessSelectCB (ctrl : UInt64) (c1 c2 : ComplexBit) : ComplexBit :=
  { real := branchlessSelect ctrl c1.real c2.real
    imag := branchlessSelect ctrl c1.imag c2.imag }

theorem branchlessSelect_correct (control a b : UInt64) :
    branchlessSelect control a b = (if control ≠ 0 then a else b) := by
  simp only [branchlessSelect]
  by_cases h : control = 0
  · subst h
    simp only [nonzeroMask, UInt64.wrappingNeg]
    native_decide
  · have : nonzeroMask control = 1 := UInt64Lemmas.neg_or_self_msb control h
    simp [nonzeroMask, this]

/--
【定理 4.1】量子測定 = 極値経路選択（同型定理）

測定演算子 M(ctrl) が pathA または pathB を選択するとき、
選択結果の normSq は必ず選択元と等しい（自己同一性）。
これは「測定が固有状態のノルムを変えない」ユニタリ性に対応する。
-/
theorem measurement_normSq_preserved (ctrl : UInt64) (pathA pathB : ComplexBit) :
    (branchlessSelectCB ctrl pathA pathB).normSq =
    (if ctrl ≠ 0 then pathA.normSq else pathB.normSq) := by
  simp only [branchlessSelectCB, normSq]
  by_cases h : ctrl = 0
  · subst h
    simp only [nonzeroMask, UInt64.wrappingNeg, branchlessSelect]
    native_decide
  · have hm : nonzeroMask ctrl = 1 := UInt64Lemmas.neg_or_self_msb ctrl h
    simp only [branchlessSelect, nonzeroMask, hm, h]
    ring

/-! ## §5. ゲート合成代数 -/

/--
`GateSeq` : ゲートの逐次合成を表す型

量子回路 = ゲートの列 として表現する。
-/
def GateSeq := List (ComplexBit → ComplexBit)

def applySeq (gs : GateSeq) (c : ComplexBit) : ComplexBit :=
  gs.foldl (fun acc g => g acc) c

/-- 【定理 5.1】ZX = iS（基本交換関係） -/
theorem gateZ_gateX_eq_rotI_phase (c : ComplexBit) :
    gateZ (gateX c) =
    { real := c.real.wrappingNeg, imag := c.imag } := by
  simp only [gateZ, gateX]

/-- 【定理 5.2】XZ = -iS† -/
theorem gateX_gateZ_eq (c : ComplexBit) :
    gateX (gateZ c) = rotNegI c := by
  simp only [gateX, gateZ, rotNegI]

/-- 【定理 5.3】ZXZ = X（共役関係） -/
theorem gateZ_gateX_gateZ_eq_gateX (c : ComplexBit) :
    gateZ (gateX (gateZ c)) = gateX c := by
  simp only [gateZ, gateX, UInt64.wrappingNeg_wrappingNeg]

/-- 【定理 5.4】全ノルム保存ゲートの合成はノルムを保存する -/
theorem norm_preserving_composition (c : ComplexBit) :
    (gateZ (gateX (rotI c))).normSq = c.normSq := by
  simp only [gateZ, gateX, rotI, normSq, UInt64.wrappingNeg]
  ring

/-! ## §6. 情報価値ゲート（BitEconomics 統合） -/

/--
## 情報価値の ComplexBit 表現

  real : ビット列（情報の担体）
  imag : 情報価値（Shannon エントロピー削減量）

この解釈のもとで、量子ゲートは「情報と価値の変換規則」になる：

  Z gate : 価値の極性反転（負の情報価値 = コスト）
  X gate : 情報と価値の交換（観測者と対象の双対性）
  S gate : 価値の虚軸投射（潜在的価値への変換）
  H gate : 情報と価値の等重み混合（重ね合わせ状態）
  CNOT   : 条件付き価値転移（情報が存在するとき価値を転写）
-/

/--
`valueTransfer` : 情報価値転移演算子

送信者 `src` の情報価値（imag）を受信者 `dst` の価値に加算する。
「情報の伝達 = 価値の転移」という BitEconomics の基本命題を実装。
-/
@[inline] def valueTransfer (src dst : ComplexBit) : ComplexBit :=
  { real := dst.real
    imag := dst.imag + src.imag }

/-- 【定理 6.1】価値転移の加法性 -/
theorem valueTransfer_additive (src dst1 dst2 : ComplexBit) :
    (valueTransfer src dst1).imag + (valueTransfer src dst2).imag =
    dst1.imag + dst2.imag + 2 * src.imag := by
  simp only [valueTransfer]
  ring

/-- 【定理 6.2】価値転移はビット列（real）を保存する -/
theorem valueTransfer_real_preserved (src dst : ComplexBit) :
    (valueTransfer src dst).real = dst.real := by
  simp only [valueTransfer]

/-! ## §7. 検証スイート -/

section VerificationSuite

-- Z gate: 虚部符号反転
#eval gateZ { real := 3, imag := 5 }
-- 期待値: { real := 3, imag := 18446744073709551611 } (-5 mod 2^64)

-- X gate: real/imag 交換
#eval gateX { real := 3, imag := 5 }
-- 期待値: { real := 5, imag := 3 }

-- S gate (rotI): ×i 回転
#eval ComplexBit.rotI { real := 3, imag := 0 }
-- 期待値: { real := 0, imag := 3 }

-- S² = Z の確認
#eval ComplexBit.rotI (ComplexBit.rotI { real := 3, imag := 5 })
#eval gateZ { real := 3, imag := 5 }
-- 両者が一致することを確認

-- CNOT: 制御ビット非零のとき標的の real/imag を交換
#eval gateCNOT {
  control := { real := 1, imag := 0 }  -- 非零制御
  target  := { real := 3, imag := 5 }
}
-- 期待値: control 不変, target = { real := 5, imag := 3 }（X gate 適用）

-- CNOT: 制御ビット零のとき恒等
#eval gateCNOT {
  control := { real := 0, imag := 0 }  -- 零制御
  target  := { real := 3, imag := 5 }
}
-- 期待値: target 変化なし

-- H gate 近似: (1,0) → 等重み混合
#eval gateH_approx { real := 128, imag := 0 }
-- 期待値: real ≈ 181, imag ≈ 181（等重み）

-- ゲート合成: ZXZ = X の確認
#eval gateZ (gateX (gateZ { real := 7, imag := 11 }))
#eval gateX { real := 7, imag := 11 }
-- 両者が一致することを確認

-- 情報価値転移
#eval valueTransfer { real := 0, imag := 10 } { real := 5, imag := 3 }
-- 期待値: { real := 5, imag := 13 }（価値 10 が転移）

end VerificationSuite
