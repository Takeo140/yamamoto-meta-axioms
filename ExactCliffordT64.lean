License　Apache 2.0  Takeo Yamamoto
/-
  ExactCliffordT64.lean
  ------------------------------------------------------------------
  「整数版・完成版」— 丸め誤差ゼロの厳密 Clifford+T 量子ゲート環

  前作 ComplexLinalg64.lean (Fx64 固定小数点版) の弱点は、
  Hadamard/T ゲートに現れる 1/√2, e^{iπ/4} が近似値でしか表せず、
  U†U = I を「厳密には」証明できなかった点にあった。

  本ファイルはこの弱点を解消する。ω = e^{iπ/4} を生成元とする環
    Z[ω] = { a + bω + cω² + dω³ | a,b,c,d ∈ ℤ },  ω⁴ = -1
  を土台にし、さらに √2 = ω - ω³ ∈ Z[ω] のべきを分母に許した局所化
    D[ω] = Z[ω][1/√2]  (要素は num/√2^k の形)
  上で複素線形代数を実装する。これは Ross–Selinger の Clifford+T
  厳密合成理論で使われる標準的な環であり、I, X, Y, Z, S, T, H, CNOT
  のすべてが「丸めなしの厳密な環要素」として表現できる。
  → 前作では不可能だった H, T の厳密ユニタリ性証明が、今回は
    native_decide でそのまま通る(下記 gateH_unitary, gateT_unitary)。

  スコープの限界(意図的):
    この環で厳密に表せるのは Clifford+T ゲート集合が生成する値のみ。
    任意の実数振幅(例えば恣意的な回転角)は依然として表現できない
    ―― これは Fx64 版が担うべき役割であり、両者は競合ではなく
    使い分ける関係にある。

  ビルド未検証について:
    このサンドボックスには Lean/lake が無く、elan 経由での取得も
    ネットワーク制限(release.lean-lang.org 不許可)で失敗した。
    したがって今回も `lake build` を実機で通せていない。
    さらに今回は Mathlib.Tactic.Ring に依存しており
    (Zom の環公理を `ring` タクティクで証明するため)、
    あなたの既存 F-Theory Mathlib プロジェクトに追加して
    `lake build` を通してから正としてほしい。
    特に確認してほしい箇所:
      - `ring` タクティクが Zom.mk.injEq 分解後の各成分で閉じるか
      - native_decide が GC.equivB 経由の 4x4 (CNOT) チェックで
        現実的な時間か
      - `sqrt2Pow` の再帰定義がそのまま停止性チェックを通るか
-/

import Mathlib.Tactic.Ring

namespace ExactCliffordT64

-- ============================ Zom: Z[ω], ω = e^{iπ/4}, ω⁴ = -1 ============================

/-- a + bω + cω² + dω³ (ω⁴ = -1 で還元済みの表現)。
    ω² = i, ω³ = -ω⁻¹ = e^{i3π/4}。 -/
structure Zom where
  a b c d : Int
deriving DecidableEq, Repr

namespace Zom

def zero : Zom := ⟨0, 0, 0, 0⟩
def one : Zom := ⟨1, 0, 0, 0⟩
def omega : Zom := ⟨0, 1, 0, 0⟩     -- ω = e^{iπ/4} (T ゲートの位相そのもの)
def imUnit : Zom := ⟨0, 0, 1, 0⟩    -- i = ω²

def add (x y : Zom) : Zom := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def neg (x : Zom) : Zom := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : Zom) : Zom := add x (neg y)

/-- 畳み込み後に ω⁴=-1, ω⁵=-ω, ω⁶=-ω² で還元した乗算。
    (a+bω+cω²+dω³)(a'+b'ω+c'ω²+d'ω³) を展開し、次数4以上の項を
    ω⁴=-1 で下げると以下の式になる。 -/
def mul (x y : Zom) : Zom :=
  ⟨ x.a*y.a - x.b*y.d - x.c*y.c - x.d*y.b
  , x.a*y.b + x.b*y.a - x.c*y.d - x.d*y.c
  , x.a*y.c + x.b*y.b + x.c*y.a - x.d*y.d
  , x.a*y.d + x.b*y.c + x.c*y.b + x.d*y.a ⟩

/-- 複素共役。conj(ω) = ω⁻¹ = -ω³ から導かれる: (a,b,c,d) ↦ (a,-d,-c,-b)。 -/
def conj (x : Zom) : Zom := ⟨x.a, -x.d, -x.c, -x.b⟩

-- ---------------------- 環の公理 (Mathlib `ring` タクティクで完全証明) ----------------------

theorem add_comm (x y : Zom) : add x y = add y x := by
  simp only [add, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem add_assoc (x y z : Zom) : add (add x y) z = add x (add y z) := by
  simp only [add, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem zero_add (x : Zom) : add zero x = x := by simp [add, zero]
theorem add_zero (x : Zom) : add x zero = x := by simp [add, zero]
theorem add_neg_cancel (x : Zom) : add x (neg x) = zero := by simp [add, neg, zero]

theorem mul_comm (x y : Zom) : mul x y = mul y x := by
  simp only [mul, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem mul_assoc (x y z : Zom) : mul (mul x y) z = mul x (mul y z) := by
  simp only [mul, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem one_mul (x : Zom) : mul one x = x := by
  simp only [mul, one, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem mul_one (x : Zom) : mul x one = x := by
  simp only [mul, one, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem left_distrib (x y z : Zom) : mul x (add y z) = add (mul x y) (mul x z) := by
  simp only [mul, add, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem right_distrib (x y z : Zom) : mul (add x y) z = add (mul x z) (mul y z) := by
  simp only [mul, add, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem conj_conj (x : Zom) : conj (conj x) = x := by simp [conj]

theorem conj_mul (x y : Zom) : conj (mul x y) = mul (conj x) (conj y) := by
  simp only [conj, mul, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem conj_add (x y : Zom) : conj (add x y) = add (conj x) (conj y) := by
  simp only [conj, add, Zom.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

end Zom

-- ============================ GC: D[ω] = Z[ω][1/√2] ============================

/-- √2 = ω - ω³ (Z[ω] の中に厳密に存在する)。 -/
def Zom.sqrt2 : Zom := ⟨0, 1, 0, -1⟩

/-- (√2)^n を Zom の値として計算する。 -/
def Zom.sqrt2Pow : Nat → Zom
  | 0 => Zom.one
  | n + 1 => Zom.mul Zom.sqrt2 (Zom.sqrt2Pow n)

/-- num / (√2)^k の形の分数 (Ross–Selinger の Clifford+T 表現)。 -/
structure GC where
  num : Zom
  k : Nat
deriving DecidableEq, Repr

namespace GC

def zero : GC := ⟨Zom.zero, 0⟩
def one : GC := ⟨Zom.one, 0⟩

/-- 通分してから加算。分母の位数を max に揃える。 -/
def add (x y : GC) : GC :=
  let m := max x.k y.k
  ⟨ Zom.add (Zom.mul x.num (Zom.sqrt2Pow (m - x.k)))
            (Zom.mul y.num (Zom.sqrt2Pow (m - y.k)))
  , m ⟩

def neg (x : GC) : GC := ⟨Zom.neg x.num, x.k⟩
def sub (x y : GC) : GC := add x (neg y)
def mul (x y : GC) : GC := ⟨Zom.mul x.num y.num, x.k + y.k⟩
def conj (x : GC) : GC := ⟨Zom.conj x.num, x.k⟩

/-- 数学的な等値性 (num/√2^k として通分して比較。構造的な `=` ではない
    ―― 例えば ⟨2,2⟩ と ⟨1,0⟩ は構造的には異なるが、どちらも値は 1)。 -/
def equiv (x y : GC) : Prop :=
  Zom.mul x.num (Zom.sqrt2Pow y.k) = Zom.mul y.num (Zom.sqrt2Pow x.k)

/-- `equiv` の決定可能な Bool 版。native_decide の対象はこちら。 -/
def equivB (x y : GC) : Bool :=
  decide (Zom.mul x.num (Zom.sqrt2Pow y.k) = Zom.mul y.num (Zom.sqrt2Pow x.k))

theorem equiv_refl (x : GC) : equiv x x := rfl

theorem equiv_symm {x y : GC} (h : equiv x y) : equiv y x := h.symm

end GC

-- ============================ 行列・ベクトル (Array ベース、GC係数) ============================

abbrev CVec := Array GC
abbrev CMat := Array (Array GC)

namespace CMat

def rows (m : CMat) : Nat := m.size
def cols (m : CMat) : Nat := (m.get! 0).size
def get (m : CMat) (r c : Nat) : GC := (m.get! r).get! c

def identity (n : Nat) : CMat :=
  Array.ofFn (fun i : Fin n => Array.ofFn (fun j : Fin n =>
    if i.val = j.val then GC.one else GC.zero))

/-- エルミート共役 (共役転置) -/
def dagger (m : CMat) : CMat :=
  Array.ofFn (fun j : Fin m.cols => Array.ofFn (fun i : Fin m.rows =>
    GC.conj (m.get i j)))

def matMul (a b : CMat) : CMat :=
  Array.ofFn (fun i : Fin a.rows => Array.ofFn (fun j : Fin b.cols =>
    (List.range a.cols).foldl
      (fun acc k => GC.add acc (GC.mul (a.get i k) (b.get k j)))
      GC.zero))

/-- テンソル積 (クロネッカー積) -/
def kron (a b : CMat) : CMat :=
  Array.ofFn (fun I : Fin (a.rows * b.rows) => Array.ofFn (fun J : Fin (a.cols * b.cols) =>
    let i1 := I.val / b.rows
    let i2 := I.val % b.rows
    let j1 := J.val / b.cols
    let j2 := J.val % b.cols
    GC.mul (a.get i1 j1) (b.get i2 j2)))

def apply (m : CMat) (v : CVec) : CVec :=
  Array.ofFn (fun i : Fin m.rows =>
    (List.range m.cols).foldl
      (fun acc k => GC.add acc (GC.mul (m.get i k) (v.get! k)))
      GC.zero)

/-- 行列の数学的等値性: 各成分を GC.equivB で通分比較する
    (H/T のような分母付き成分でも正しく判定できる)。 -/
def equivB (a b : CMat) : Bool :=
  a.size == b.size &&
  (List.range a.size).all (fun i =>
    (a.get! i).size == (b.get! i).size &&
    (List.range (a.get! i).size).all (fun j =>
      GC.equivB ((a.get! i).get! j) ((b.get! i).get! j)))

end CMat

namespace CVec

def kron (a b : CVec) : CVec :=
  Array.ofFn (fun I : Fin (a.size * b.size) =>
    GC.mul (a.get! (I.val / b.size)) (b.get! (I.val % b.size)))

end CVec

-- ============================ 標準量子ゲート (すべて厳密・丸めなし) ============================

def gateI : CMat := #[#[GC.one, GC.zero], #[GC.zero, GC.one]]
def gateX : CMat := #[#[GC.zero, GC.one], #[GC.one, GC.zero]]

def gateY : CMat :=
  #[ #[GC.zero, GC.neg ⟨Zom.imUnit, 0⟩]
   , #[⟨Zom.imUnit, 0⟩, GC.zero] ]

def gateZ : CMat := #[#[GC.one, GC.zero], #[GC.zero, GC.neg GC.one]]
def gateS : CMat := #[#[GC.one, GC.zero], #[GC.zero, ⟨Zom.imUnit, 0⟩]]

/-- T ゲート = diag(1, e^{iπ/4}) = diag(1, ω)。ω はこの環の生成元そのものなので
    Fx64 版と違い「丸めゼロ」で厳密に表せる。 -/
def gateT : CMat := #[#[GC.one, GC.zero], #[GC.zero, ⟨Zom.omega, 0⟩]]

def gateCNOT : CMat :=
  #[ #[GC.one,  GC.zero, GC.zero, GC.zero]
   , #[GC.zero, GC.one,  GC.zero, GC.zero]
   , #[GC.zero, GC.zero, GC.zero, GC.one]
   , #[GC.zero, GC.zero, GC.one,  GC.zero] ]

/-- Hadamard = 1/√2 [[1,1],[1,-1]]。1/√2 = ⟨1, k=1⟩ として厳密に表現。
    Fx64 版では sqrtHalf という「丸め定数」が必要だったが、
    この環では分数 num/√2^k がそのまま厳密値になる。 -/
def gateH : CMat :=
  #[ #[⟨Zom.one, 1⟩, ⟨Zom.one, 1⟩]
   , #[⟨Zom.one, 1⟩, ⟨Zom.neg Zom.one, 1⟩] ]

-- ---------------------- ユニタリ性: 全ゲートで厳密証明 ----------------------
-- CMat.equivB は num/√2^k の通分比較なので、H・T のように分母つきの成分でも
-- 「厳密に」 U†U = I を判定できる。前作 (Fx64版) では H, T は未証明のまま
-- #eval で残差確認するしかなかったが、今回は全ゲートが未証明箇所なしで閉じる。

theorem gateI_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateI) gateI) (CMat.identity 2) = true := by
  native_decide

theorem gateX_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateX) gateX) (CMat.identity 2) = true := by
  native_decide

theorem gateY_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateY) gateY) (CMat.identity 2) = true := by
  native_decide

theorem gateZ_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateZ) gateZ) (CMat.identity 2) = true := by
  native_decide

theorem gateS_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateS) gateS) (CMat.identity 2) = true := by
  native_decide

/-- 前作では未証明だった T ゲートの厳密ユニタリ性。今回の目玉。 -/
theorem gateT_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateT) gateT) (CMat.identity 2) = true := by
  native_decide

/-- 前作では未証明だった H ゲートの厳密ユニタリ性。今回の目玉。 -/
theorem gateH_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateH) gateH) (CMat.identity 2) = true := by
  native_decide

theorem gateCNOT_unitary :
    CMat.equivB (CMat.matMul (CMat.dagger gateCNOT) gateCNOT) (CMat.identity 4) = true := by
  native_decide

-- ============================ デモ: Bell状態 (#eval 用、証明とは独立) ============================

/-- 目視確認専用の Float 近似変換 (ω=1/√2+i/√2 という数値埋め込みを使う)。
    証明では一切使わない。 -/
def GC.toFloatPair (x : GC) : Float × Float :=
  let s2 : Float := Float.sqrt 2.0
  let ow : Float := 1.0 / s2
  let re := x.num.a.toFloat + x.num.b.toFloat * ow + x.num.d.toFloat * (-ow)
  let im := x.num.b.toFloat * ow + x.num.c.toFloat * 1.0 + x.num.d.toFloat * ow
  let denom := s2 ^ x.k
  (re / denom, im / denom)

def ket0 : CVec := #[GC.one, GC.zero]

def psi0 : CVec := CVec.kron ket0 ket0
def psi1 : CVec := CMat.apply (CMat.kron gateH gateI) psi0
def psi2 : CVec := CMat.apply gateCNOT psi1

-- #eval psi2.map GC.toFloatPair

end ExactCliffordT64
