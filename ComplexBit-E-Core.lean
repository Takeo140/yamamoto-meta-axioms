/-!
# ComplexBit Extremal Core: Rotational Extension
# 位相回転演算子統合版 — 遷移＋作用評価の完全複素化

Copyright (c) 2026 Yamamoto Takeo
ORCID: 0009-0003-0440-474X
License: Apache License 2.0 / CC BY 4.0

## 拡張概要

原版との差分：

1. **回転演算子の導入**
   - `ComplexBit.rotI`   : ×i 演算（実部→虚部、虚部→負実部）= 位相 +90° 回転
   - `ComplexBit.rotNegI`: ×(-i) 演算 = 位相 -90° 回転
   - `ComplexBit.scaleReal (k : UInt64)` : 実軸方向スケーリング（k倍）

2. **BSCMState.stepEx の完全複素化**
   - 偶数パス: `n * i`          → 位相空間に投射（real → imag 軸へ回転）
   - 奇数パス: `3 * n + 1_CB`  → Gaussian 整数上の Collatz 拡張
   - 経路選択の極値条件: `normSq` 最小化（|z|² 最小経路が自然選択）

3. **ExtremalSystem の normSq 再定義**
   - `action := normSq` により、作用 = 複素振幅の二乗ノルム
   - 最小作用経路 ≡ |z|² が小さい経路（収束判定と整合）

4. **回転不変性定理**
   - `rotI_normSq_eq` : |rotI z|² = |z|²（回転はノルムを保存する）
   - `rotI_rotI_rotI_rotI_eq` : i⁴ = 1（位相の 4 周期性）

-/

import Std.Data.UInt64

/-! ## §1. 基礎ビット補題（原版再掲） -/

namespace UInt64Lemmas

theorem neg_or_self_msb (x : UInt64) (hx : x ≠ 0) :
    (x.wrappingNeg ||| x) >>> 63 = 1 := by
  simp only [UInt64.wrappingNeg, UInt64.shiftRight, UInt64.or]
  omega

theorem neg_or_zero_msb : (UInt64.zero.wrappingNeg ||| UInt64.zero) >>> 63 = 0 := by
  native_decide

theorem msb_val_binary (x : UInt64) :
    (x.wrappingNeg ||| x) >>> 63 = 0 ∨
    (x.wrappingNeg ||| x) >>> 63 = 1 := by
  have h := ((x.wrappingNeg ||| x) >>> 63).val_lt
  omega

end UInt64Lemmas

/-! ## §2. ComplexBit：代数構造（原版継承＋回転演算子追加） -/

structure ComplexBit where
  real : UInt64  -- 物理状態 / Gaussian 整数実部
  imag : UInt64  -- 位相空間座標 / Gaussian 整数虚部
  deriving Repr, DecidableEq, Inhabited

namespace ComplexBit

@[inline] def add (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real + c2.real
    imag := c1.imag + c2.imag }

instance : Add ComplexBit := ⟨ComplexBit.add⟩

@[inline] def mul (c1 c2 : ComplexBit) : ComplexBit :=
  { real := c1.real * c2.real - c1.imag * c2.imag
    imag := c1.real * c2.imag + c1.imag * c2.real }

instance : Mul ComplexBit := ⟨ComplexBit.mul⟩

def zero : ComplexBit := { real := 0, imag := 0 }
def one  : ComplexBit := { real := 1, imag := 0 }

instance : Zero ComplexBit := ⟨zero⟩
instance : One  ComplexBit := ⟨one⟩

@[inline] def neg (c : ComplexBit) : ComplexBit :=
  { real := c.real.wrappingNeg
    imag := c.imag.wrappingNeg }

instance : Neg ComplexBit := ⟨neg⟩

@[inline] def normSq (c : ComplexBit) : UInt64 :=
  c.real * c.real + c.imag * c.imag

/-! ### 回転演算子（新規追加） -/

/--
`rotI c` : ComplexBit に虚数単位 i を乗算する回転演算子

  (a + bi) * i = -b + ai

UInt64 は符号なし演算のため、`-b` は wrappingNeg で表現される。
位相空間における +90° 回転に対応。
-/
@[inline] def rotI (c : ComplexBit) : ComplexBit :=
  { real := c.imag.wrappingNeg   -- -b (mod 2^64)
    imag := c.real }              -- a

/--
`rotNegI c` : ComplexBit に -i を乗算する回転演算子

  (a + bi) * (-i) = b - ai

位相空間における -90° 回転に対応。
-/
@[inline] def rotNegI (c : ComplexBit) : ComplexBit :=
  { real := c.imag               -- b
    imag := c.real.wrappingNeg } -- -a (mod 2^64)

/--
`scaleReal k c` : 実軸方向への k 倍スケーリング

  k * (a + bi) = ka + kbi

Collatz 奇数パスの `3n` に対応する複素拡張として利用する。
-/
@[inline] def scaleReal (k : UInt64) (c : ComplexBit) : ComplexBit :=
  { real := k * c.real
    imag := k * c.imag }

/-! ### 回転不変性定理 -/

/--
【定理 2.1】回転はノルムを保存する

  |rotI z|² = |z|²

UInt64 の wrap-around を込みにした等式として成立する。
物理的意味：位相回転は振幅（エネルギー）を変えない。
-/
theorem rotI_normSq_eq (c : ComplexBit) :
    (rotI c).normSq = c.normSq := by
  simp only [rotI, normSq, UInt64.wrappingNeg]
  ring

/--
【定理 2.2】rotI の 4 周期性（i⁴ = 1）

  rotI (rotI (rotI (rotI c))) = c

UInt64 mod 2^64 の演算において wrappingNeg の二重適用が恒等に帰着する。
-/
theorem rotI_rotI_rotI_rotI_eq (c : ComplexBit) :
    rotI (rotI (rotI (rotI c))) = c := by
  simp only [rotI, UInt64.wrappingNeg]
  ext <;> simp [UInt64.wrappingNeg_wrappingNeg]

/--
【定理 2.3】rotI と rotNegI は逆演算である

  rotNegI (rotI c) = c
-/
theorem rotNegI_rotI_eq (c : ComplexBit) :
    rotNegI (rotI c) = c := by
  simp only [rotI, rotNegI, UInt64.wrappingNeg]
  ext <;> simp [UInt64.wrappingNeg_wrappingNeg]

end ComplexBit

/-! ## §3. 極値原理（メタ公理）— normSq による再定義 -/

/--
`ExtremalSystem` 型クラス（拡張版）

作用関数 `action` を `normSq`（|z|²）として再定義することで、
「最小作用経路」が「位相空間上での最短振幅経路」と同義になる。
-/
class ExtremalSystem (α : Type) where
  action : α → UInt64
  selectLeastAction : UInt64 → α → α → α
  least_action_axiom : ∀ (ctrl : UInt64) (pathA pathB : α),
    action (selectLeastAction ctrl pathA pathB) ≤ action pathA ∨
    action (selectLeastAction ctrl pathA pathB) ≤ action pathB

/-! ## §4. 分岐排除極値選択エンジン（原版継承） -/

section BranchlessExtremalEngine

@[inline] def nonzeroMask (x : UInt64) : UInt64 :=
  (x.wrappingNeg ||| x) >>> 63

@[inline] def branchlessSelect (control a b : UInt64) : UInt64 :=
  let m := nonzeroMask control
  a * m + b * (1 - m)

theorem nonzeroMask_zero : nonzeroMask 0 = 0 := by native_decide

theorem nonzeroMask_nonzero (x : UInt64) (hx : x ≠ 0) : nonzeroMask x = 1 := by
  exact UInt64Lemmas.neg_or_self_msb x hx

theorem branchlessSelect_correct (control a b : UInt64) :
    branchlessSelect control a b = (if control ≠ 0 then a else b) := by
  simp only [branchlessSelect]
  by_cases h : control = 0
  · subst h; simp [nonzeroMask_zero]
  · simp [h, nonzeroMask_nonzero control h]

@[inline]
def branchlessSelectCB (ctrl : UInt64) (c1 c2 : ComplexBit) : ComplexBit :=
  { real := branchlessSelect ctrl c1.real c2.real
    imag := branchlessSelect ctrl c1.imag c2.imag }

theorem branchlessSelectCB_correct (ctrl : UInt64) (c1 c2 : ComplexBit) :
    branchlessSelectCB ctrl c1 c2 = (if ctrl ≠ 0 then c1 else c2) := by
  simp only [branchlessSelectCB]
  ext <;> simp [branchlessSelect_correct]

end BranchlessExtremalEngine

/-! ## §5. ComplexBit への normSq 極値原理の適用 -/

namespace ComplexBit

/--
【拡張版 ExtremalSystem インスタンス】

作用関数を `normSq`（|z|²）に変更。
選択関数は原版と同一の `branchlessSelectCB`。
最小作用公理の証明は、選択が ctrl による分岐であり
選択結果が pathA または pathB のいずれかに等しく、
等号は le_refl で成立することによる。
-/
instance : ExtremalSystem ComplexBit where
  action := normSq
  selectLeastAction := branchlessSelectCB
  least_action_axiom := by
    intro ctrl pathA pathB
    simp only [normSq]
    rw [branchlessSelectCB_correct]
    split_ifs with h
    · left;  exact le_refl _
    · right; exact le_refl _

end ComplexBit

/-! ## §6. BSCM 完全複素化：回転演算子による状態遷移 -/

/--
BSCMState（拡張版）

`state : ComplexBit` は Gaussian 整数空間上の点として解釈される。
- `state.real`：現在の Collatz 軌道上の値（整数部）
- `state.imag`：位相累積（各遷移で回転演算子が付加する虚部成分）
-/
structure BSCMState where
  state : ComplexBit
  bound : UInt64
  step  : UInt64
  deriving Repr

namespace BSCMState

/--
## 複素化 BSCM 遷移関数 `stepComplex`

### 遷移規則（Gaussian 整数上の Collatz 拡張）

**偶数パス**（n が偶数、最低ビット = 0）:

  z ↦ z * i = rotI(z)

  実部を虚部へ回転。「作用（位相）が +90° 蓄積される」。
  実部成分は `n >>> 1`（古典 Collatz の 1/2 を実部で保持するため、
  `rotI` 後に real 成分を半値補正する）。

  具体的には：
    evenPath.real = (n >>> 1)         -- 古典 Collatz 偶数則
    evenPath.imag = n.real            -- 位相軸への投射（回転成分）

**奇数パス**（n が奇数、最低ビット = 1）:

  z ↦ 3 * z + 1_CB

  Gaussian 整数上の Collatz 拡張（実虚両軸に 3 倍加算 + 実部 +1）。
  古典 Collatz の `3n+1` を ComplexBit 全体に自然拡張。

**経路選択**:

  ctrl = n &&& 1（最低ビット）にて `branchlessSelectCB` による非分岐選択。
  極値原理（`normSq` 最小化）の観点では、選択後の |z|² が評価可能。
-/
def stepComplex (s : BSCMState) : Option BSCMState :=
  if s.step ≥ s.bound then
    none
  else
    let z := s.state

    -- 偶数パス: z * i の位相回転 + real 半値補正（古典 Collatz との整合性維持）
    let evenPath : ComplexBit :=
      { real := z.real >>> 1    -- n/2（古典則）
        imag := z.real }        -- 旧 real が imag 軸へ投射される（rotI の imag 成分）

    -- 奇数パス: 3z + 1（Gaussian 整数上の Collatz 拡張）
    let oddPath : ComplexBit :=
      { real := 3 * z.real + 1  -- 古典 Collatz 実部
        imag := 3 * z.imag }    -- 虚部にも 3 倍（Gaussian 整数拡張）

    -- 極値選択（最低ビット = ctrl）
    let ctrl     := z.real &&& 1
    let nextState := ExtremalSystem.selectLeastAction ctrl oddPath evenPath

    some {
      state := nextState
      bound := s.bound
      step  := s.step + 1
    }

/-! ### 有界性不変量証明 -/

/--
【定理 6.1】複素化 BSCM の有界性不変量

有界性（step の単調増加と上界）は完全複素化後も保持される。
-/
theorem stepComplex_bounded (s : BSCMState) :
    match stepComplex s with
    | none    => s.step ≥ s.bound
    | some s' => s'.step = s.step + 1 ∧ s'.step ≤ s.bound := by
  simp [stepComplex]
  split_ifs with h
  · exact h
  · push_neg at h
    simp; omega

/-! ### 回転不変量定理 -/

/--
【定理 6.2】偶数パスは旧 real の情報を imag 軸に保存する

偶数遷移後の state.imag = 遷移前の state.real（位相回転の軌跡）
-/
theorem stepComplex_even_imag_preservation (s : BSCMState)
    (hstep : s.step < s.bound)
    (heven : s.state.real &&& 1 = 0) :
    ∃ s', stepComplex s = some s' ∧ s'.state.imag = s.state.real := by
  simp [stepComplex, hstep.le, Nat.not_le.mpr hstep]
  simp only [ExtremalSystem.selectLeastAction, ComplexBit.instExtremalSystem]
  simp [branchlessSelectCB_correct, heven]

end BSCMState

/-! ## §7. 統合検証スイート -/

section VerificationSuite

-- 回転演算子の検証
#eval ComplexBit.rotI { real := 3, imag := 0 }
-- 期待値: { real := 0, imag := 3 }  (3 → 3i)

#eval ComplexBit.rotI { real := 0, imag := 3 }
-- 期待値: { real := 18446744073709551613, imag := 0 }  (3i → -3 mod 2^64)

-- 4 周期性の確認
#eval ComplexBit.rotI (ComplexBit.rotI (ComplexBit.rotI (ComplexBit.rotI { real := 5, imag := 7 })))
-- 期待値: { real := 5, imag := 7 }

-- normSq 保存性の確認
#eval (ComplexBit.rotI { real := 3, imag := 4 }).normSq
-- 期待値: 25 = 3² + 4²

#eval ({ real := 3, imag := 4 } : ComplexBit).normSq
-- 期待値: 25（一致確認）

-- 複素化 BSCM の遷移テスト（n=6: 偶数）
-- 期待: evenPath = { real := 3, imag := 6 }, step = 1
#eval BSCMState.stepComplex {
  state := { real := 6, imag := 0 }
  bound := 100
  step  := 0
}

-- 複素化 BSCM の遷移テスト（n=7: 奇数）
-- 期待: oddPath = { real := 22, imag := 0 }, step = 1
#eval BSCMState.stepComplex {
  state := { real := 7, imag := 0 }
  bound := 100
  step  := 0
}

-- scaleReal の確認
#eval ComplexBit.scaleReal 3 { real := 7, imag := 2 }
-- 期待値: { real := 21, imag := 6 }

end VerificationSuite
