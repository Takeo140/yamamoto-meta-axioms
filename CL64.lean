License Apache 2.0 Takeo Yamamoto

/-
  ComplexLinalg64.lean
  ------------------------------------------------------------------
  64bit 離散型(固定小数点)複素数 線形代数 — 量子計算タイプ (Lean 4版)

  Rust版 (complex_linalg64.rs) の直接移植。
  Mathlib非依存 (pure Lean 4 core) — 依存を減らし、既存の
  lean-paper-pipeline / Mathlib 環境と切り離して単独で lake build
  できるようにしてある。Mathlib 側の便利な代数タクティクは使わず、
  Fx64/Cx64 の演算はすべて Int 上の素朴な定義 + 手動の等式証明。

  重要な注意:
    このファイルはサンドボックス内に Lean/lake ツールチェーンが
    無く(ネットワークも leanprover 系ミラーへのアクセスが許可
    されていない)、`lake build` による実機コンパイル確認が
    できていない。あなたの通常のワークフロー(CI green を
    ground truth とする)に従い、必ず手元で `lake build` を
    通してから正とみなすこと。特に:
      - Array.ofFn の依存型推論まわりの構文
      - Int.toFloat / Float 変換 API 名
      - native_decide が Mat4(16項)相当のサイズで現実的な時間で
        終わるか
    の3点は誤りがある可能性がある想定で確認してほしい。
-/

namespace ComplexLinalg64

-- ============================ Fx64: Q32.32 固定小数点 ============================

/-- Q32.32 固定小数点数。`val` は 2^32 倍された整数値。 -/
structure Fx64 where
  val : Int
deriving DecidableEq, Repr

namespace Fx64

def scale : Int := 2 ^ 32

def zero : Fx64 := ⟨0⟩
def one : Fx64 := ⟨scale⟩

def add (a b : Fx64) : Fx64 := ⟨a.val + b.val⟩
def neg (a : Fx64) : Fx64 := ⟨-a.val⟩
def sub (a b : Fx64) : Fx64 := ⟨a.val - b.val⟩

/-- 乗算: 素朴な `Int` の `/` (0方向丸め) で 2^32 だけ縮尺を戻す。
    丸め規約自体は mul_comm の証明には影響しない
    (どんな一変数関数 f についても f (a*b) = f (b*a) は a*b=b*a から従う)。 -/
def mul (a b : Fx64) : Fx64 := ⟨(a.val * b.val) / scale⟩

-- 評価用: 人間可読な Float 表示 (証明には一切使わない、#eval 専用)
def toFloat (x : Fx64) : Float := x.val.toFloat / scale.toFloat

-- ---------------------- 代数的性質 (すべて完全証明、未証明のプレースホルダーなし) ----------------------

theorem add_comm (a b : Fx64) : add a b = add b a := by
  simp [add, Int.add_comm]

theorem add_assoc (a b c : Fx64) : add (add a b) c = add a (add b c) := by
  simp [add, Int.add_assoc]

theorem zero_add (a : Fx64) : add zero a = a := by
  simp [add, zero]

theorem add_zero (a : Fx64) : add a zero = a := by
  simp [add, zero]

theorem add_neg_cancel (a : Fx64) : add a (neg a) = zero := by
  simp [add, neg, zero]

/-- 乗算の可換性は丸め規約(0方向切り捨て)に依らず厳密に成立する。 -/
theorem mul_comm (a b : Fx64) : mul a b = mul b a := by
  simp [mul, Int.mul_comm]

/-- 乗算の結合性は丸めのため一般には成り立たない
    (Rust版と同じ制約)。証明せず、既知の制約として明示する。 -/
-- theorem mul_assoc : ¬ ∀ a b c, mul (mul a b) c = mul a (mul b c) := by ...

end Fx64

-- ============================ Cx64: 離散複素数 ============================

structure Cx64 where
  re : Fx64
  im : Fx64
deriving DecidableEq, Repr

namespace Cx64

def zero : Cx64 := ⟨Fx64.zero, Fx64.zero⟩
def one : Cx64 := ⟨Fx64.one, Fx64.zero⟩
def i : Cx64 := ⟨Fx64.zero, Fx64.one⟩

def add (a b : Cx64) : Cx64 := ⟨Fx64.add a.re b.re, Fx64.add a.im b.im⟩
def neg (a : Cx64) : Cx64 := ⟨Fx64.neg a.re, Fx64.neg a.im⟩
def sub (a b : Cx64) : Cx64 := add a (neg b)

/-- (a+bi)(c+di) = (ac-bd) + (ad+bc)i -/
def mul (a b : Cx64) : Cx64 :=
  ⟨ Fx64.sub (Fx64.mul a.re b.re) (Fx64.mul a.im b.im)
  , Fx64.add (Fx64.mul a.re b.im) (Fx64.mul a.im b.re) ⟩

def conj (a : Cx64) : Cx64 := ⟨a.re, Fx64.neg a.im⟩

def normSq (a : Cx64) : Fx64 := Fx64.add (Fx64.mul a.re a.re) (Fx64.mul a.im a.im)

-- ---------------------- 代数的性質 ----------------------

theorem add_comm (a b : Cx64) : add a b = add b a := by
  simp [add, Fx64.add_comm]

theorem neg_neg (a : Cx64) : neg (neg a) = a := by
  simp [neg, Fx64.neg]

theorem conj_conj (a : Cx64) : conj (conj a) = a := by
  simp [conj, Fx64.neg]

theorem mul_comm (a b : Cx64) : mul a b = mul b a := by
  simp only [mul, Cx64.mk.injEq]
  constructor
  · rw [Fx64.mul_comm a.re b.re, Fx64.mul_comm a.im b.im]
  · rw [Fx64.mul_comm a.re b.im, Fx64.mul_comm a.im b.re, Fx64.add_comm]

end Cx64

-- ============================ 行列・ベクトル (Array ベース) ============================

abbrev CVec := Array Cx64
abbrev CMat := Array (Array Cx64)

namespace CMat

def rows (m : CMat) : Nat := m.size
def cols (m : CMat) : Nat := (m.get! 0).size

def get (m : CMat) (r c : Nat) : Cx64 := (m.get! r).get! c

def identity (n : Nat) : CMat :=
  Array.ofFn (fun i : Fin n => Array.ofFn (fun j : Fin n =>
    if i.val = j.val then Cx64.one else Cx64.zero))

/-- エルミート共役 (共役転置) -/
def dagger (m : CMat) : CMat :=
  Array.ofFn (fun j : Fin m.cols => Array.ofFn (fun i : Fin m.rows =>
    Cx64.conj (m.get i j)))

def matMul (a b : CMat) : CMat :=
  Array.ofFn (fun i : Fin a.rows => Array.ofFn (fun j : Fin b.cols =>
    (List.range a.cols).foldl
      (fun acc k => Cx64.add acc (Cx64.mul (a.get i k) (b.get k j)))
      Cx64.zero))

/-- テンソル積 (クロネッカー積) -/
def kron (a b : CMat) : CMat :=
  Array.ofFn (fun I : Fin (a.rows * b.rows) => Array.ofFn (fun J : Fin (a.cols * b.cols) =>
    let i1 := I.val / b.rows
    let i2 := I.val % b.rows
    let j1 := J.val / b.cols
    let j2 := J.val % b.cols
    Cx64.mul (a.get i1 j1) (b.get i2 j2)))

def apply (m : CMat) (v : CVec) : CVec :=
  Array.ofFn (fun i : Fin m.rows =>
    (List.range m.cols).foldl
      (fun acc k => Cx64.add acc (Cx64.mul (m.get i k) (v.get! k)))
      Cx64.zero)

end CMat

namespace CVec

def kron (a b : CVec) : CVec :=
  Array.ofFn (fun I : Fin (a.size * b.size) =>
    Cx64.mul (a.get! (I.val / b.size)) (b.get! (I.val % b.size)))

def probabilities (v : CVec) : Array Float :=
  v.map (fun c => (Cx64.normSq c).toFloat)

end CVec

-- ============================ 標準量子ゲート ============================

def gateI : CMat := #[#[Cx64.one, Cx64.zero], #[Cx64.zero, Cx64.one]]
def gateX : CMat := #[#[Cx64.zero, Cx64.one], #[Cx64.one, Cx64.zero]]
def gateY : CMat := #[#[Cx64.zero, Cx64.neg Cx64.i], #[Cx64.i, Cx64.zero]]
def gateZ : CMat := #[#[Cx64.one, Cx64.zero], #[Cx64.zero, Cx64.neg Cx64.one]]
def gateS : CMat := #[#[Cx64.one, Cx64.zero], #[Cx64.zero, Cx64.i]]

def gateCNOT : CMat :=
  #[ #[Cx64.one,  Cx64.zero, Cx64.zero, Cx64.zero]
   , #[Cx64.zero, Cx64.one,  Cx64.zero, Cx64.zero]
   , #[Cx64.zero, Cx64.zero, Cx64.zero, Cx64.one]
   , #[Cx64.zero, Cx64.zero, Cx64.one,  Cx64.zero] ]

/-- 2^32 / √2 の丸め整数。H・T ゲートにのみ現れる唯一の非厳密要素。 -/
def sqrtHalf : Fx64 := ⟨3037000500⟩

def gateH : CMat :=
  #[ #[⟨sqrtHalf, Fx64.zero⟩, ⟨sqrtHalf, Fx64.zero⟩]
   , #[⟨sqrtHalf, Fx64.zero⟩, ⟨Fx64.neg sqrtHalf, Fx64.zero⟩] ]

def gateT : CMat :=
  #[ #[Cx64.one, Cx64.zero]
   , #[Cx64.zero, ⟨sqrtHalf, sqrtHalf⟩] ]

-- ---------------------- ユニタリ性: 厳密証明 (丸めなしゲートのみ) ----------------------
-- I, X, Y, Z, S, CNOT は成分が {0, ±1, ±i} のみで丸め誤差がないため、
-- U† U = I が「厳密に」成立し decide/native_decide で完全に証明できる(未証明のプレースホルダーなし)。
-- (native_decide は lean-paper-pipeline の既存の慣行に合わせた)

theorem gateI_unitary : CMat.matMul (CMat.dagger gateI) gateI = CMat.identity 2 := by
  native_decide

theorem gateX_unitary : CMat.matMul (CMat.dagger gateX) gateX = CMat.identity 2 := by
  native_decide

theorem gateY_unitary : CMat.matMul (CMat.dagger gateY) gateY = CMat.identity 2 := by
  native_decide

theorem gateZ_unitary : CMat.matMul (CMat.dagger gateZ) gateZ = CMat.identity 2 := by
  native_decide

theorem gateS_unitary : CMat.matMul (CMat.dagger gateS) gateS = CMat.identity 2 := by
  native_decide

theorem gateCNOT_unitary :
    CMat.matMul (CMat.dagger gateCNOT) gateCNOT = CMat.identity 4 := by
  native_decide

-- H, T は sqrtHalf の丸め誤差のため U†U = I が「厳密には」成り立たない。
-- これは Rust版と同じ既知の制約であり、証明はせず #eval で残差を確認する対象とする。
-- (将来: sqrtHalf の丸め誤差の上界を Fx64 の値として証明し、
--  ‖U†U - I‖ ≤ ε の形の近似ユニタリ性補題に落とす — Rust版の
--  is_approx_unitary(eps) に相当する形式的対応物)

-- ============================ デモ: Bell状態 (#eval 用、証明とは独立) ============================

def ket0 : CVec := #[Cx64.one, Cx64.zero]

def psi0 : CVec := CVec.kron ket0 ket0
def psi1 : CVec := CMat.apply (CMat.kron gateH gateI) psi0
def psi2 : CVec := CMat.apply gateCNOT psi1

-- #eval psi2.map (fun c => (c.re.toFloat, c.im.toFloat))
-- #eval psi2.probabilities

end ComplexLinalg64
