/-
  離散型量子計算核 基底核 (Base Core of the Discrete Quantum Computation Kernel)
  UHA-DComplex-64
  License: Apache 2.0
  Author: Takeo Yamamoto

  スカラー環は U64 = ZMod (2^64)（uint64_t の mod 2^64 演算と一致）。
  注意：この環は体ではなく零因子を持つ。norm は「保存量」であり、
  大きさ（閾値比較）や正規化の根拠としては使わないこと。
-/
import Mathlib

open BigOperators

/-- 基本スカラー：U64 有限環 -/
abbrev U64 := ZMod (2^64)

/-- UltraCore HyperAlgebra の n 次元キャリア -/
@[ext]
structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

instance : Zero (UHA n) := ⟨⟨fun _ => 0⟩⟩
instance : Add (UHA n) := ⟨fun x y => ⟨fun i => x.coords i + y.coords i⟩⟩
instance : Neg (UHA n) := ⟨fun x => ⟨fun i => - x.coords i⟩⟩
instance : SMul U64 (UHA n) := ⟨fun a x => ⟨fun i => a * x.coords i⟩⟩

@[simp] theorem zero_coords (i : Fin n) : (0 : UHA n).coords i = 0 := rfl
@[simp] theorem add_coords (x y : UHA n) (i : Fin n) :
    (x + y).coords i = x.coords i + y.coords i := rfl
@[simp] theorem neg_coords (x : UHA n) (i : Fin n) :
    (-x).coords i = - x.coords i := rfl
@[simp] theorem smul_coords (a : U64) (x : UHA n) (i : Fin n) :
    (a • x).coords i = a * x.coords i := rfl

instance : AddCommGroup (UHA n) where
  add_assoc := fun x y z => by ext i; simp [add_assoc]
  zero_add := fun x => by ext i; simp
  add_zero := fun x => by ext i; simp
  add_comm := fun x y => by ext i; simp [add_comm]
  neg_add_cancel := fun x => by ext i; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module U64 (UHA n) where
  one_smul := fun x => by ext i; simp
  mul_smul := fun a b x => by ext i; simp [mul_assoc]
  smul_zero := fun a => by ext i; simp
  smul_add := fun a x y => by ext i; simp [mul_add]
  add_smul := fun a b x => by ext i; simp [add_mul]
  zero_smul := fun x => by ext i; simp

/-- 多元代数の乗法（構造定数 c を外部から与える） -/
def mulWith (c : Fin n → Fin n → UHA n) (x y : UHA n) : UHA n :=
  ⟨fun i => ∑ j, ∑ k, x.coords j * y.coords k * (c j k).coords i⟩

/-- 内積（対称双線形形式） -/
def inner (x y : UHA n) : U64 :=
  ∑ i, x.coords i * y.coords i

/-- ノルム（量子状態の離散版）= 自己内積 -/
def norm (x : UHA n) : U64 :=
  ∑ i, x.coords i * x.coords i

theorem norm_eq_inner (x : UHA n) : norm x = inner x x := rfl

theorem inner_comm (x y : UHA n) : inner x y = inner y x :=
  Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem inner_add_left (x y z : UHA n) :
    inner (x + y) z = inner x z + inner y z := by
  unfold inner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

theorem inner_smul_left (a : U64) (x y : UHA n) :
    inner (a • x) y = a * inner x y := by
  unfold inner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_coords]
  ring

theorem norm_smul (a : U64) (x : UHA n) :
    norm (a • x) = (a * a) * norm x := by
  unfold norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_coords]
  ring

/-- ユニタリ作用素（量子ゲートの離散版）：ノルム保存 -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

/-- 恒等作用素 -/
def UOp.id : UOp n := ⟨fun v => v, fun _ => rfl⟩

/-- 合成：ノルム保存作用素は合成で閉じる -/
def UOp.comp (g h : UOp n) : UOp n :=
  ⟨fun v => g.f (h.f v), fun v => by rw [g.unitary_like, h.unitary_like]⟩

end UHA

/-! ===== 上位層：ゲート・回路・テンソル積 ===== -/

namespace UHA

variable {n : Nat}

/-! ## 状態：計算基底 -/

/-- 計算基底状態 |i⟩ -/
def basis (i : Fin n) : UHA n :=
  ⟨fun j => if j = i then 1 else 0⟩

theorem norm_basis (i : Fin n) : UHA.norm (basis i) = 1 := by
  unfold UHA.norm basis
  simp

/-! ## ゲート -/

/-- 置換ゲート（X, CNOT, SWAP）：座標の並べ替え -/
def permGate (σ : Equiv.Perm (Fin n)) : UOp n :=
  ⟨fun v => ⟨fun i => v.coords (σ.symm i)⟩, fun v => by
    unfold UHA.norm
    exact Equiv.sum_comp σ.symm (fun i => v.coords i * v.coords i)⟩

/-- 置換ゲートは内積を保存する -/
theorem permGate_inner (σ : Equiv.Perm (Fin n)) (x y : UHA n) :
    UHA.inner ((permGate σ).f x) ((permGate σ).f y) = UHA.inner x y := by
  unfold UHA.inner
  exact Equiv.sum_comp σ.symm (fun i => x.coords i * y.coords i)

/-- 置換ゲートは可逆（逆は σ.symm のゲート） -/
theorem permGate_inv (σ : Equiv.Perm (Fin n)) (v : UHA n) :
    (permGate σ.symm).f ((permGate σ).f v) = v := by
  ext i
  show v.coords (σ.symm (σ i)) = v.coords i
  simp

/-- 対角ゲート（Z, 離散位相）：u i * u i = 1 のとき -/
def diagGate (u : Fin n → U64) (hu : ∀ i, u i * u i = 1) : UOp n :=
  ⟨fun v => ⟨fun i => u i * v.coords i⟩, fun v => by
    unfold UHA.norm
    refine Finset.sum_congr rfl fun i _ => ?_
    show (u i * v.coords i) * (u i * v.coords i) = v.coords i * v.coords i
    calc (u i * v.coords i) * (u i * v.coords i)
        = (u i * u i) * (v.coords i * v.coords i) := by ring
      _ = v.coords i * v.coords i := by rw [hu i, one_mul]⟩

/-- 対角ゲートは内積を保存する -/
theorem diagGate_inner (u : Fin n → U64) (hu : ∀ i, u i * u i = 1) (x y : UHA n) :
    UHA.inner ((diagGate u hu).f x) ((diagGate u hu).f y) = UHA.inner x y := by
  unfold UHA.inner
  refine Finset.sum_congr rfl fun i _ => ?_
  show (u i * x.coords i) * (u i * y.coords i) = x.coords i * y.coords i
  calc (u i * x.coords i) * (u i * y.coords i)
      = (u i * u i) * (x.coords i * y.coords i) := by ring
    _ = x.coords i * y.coords i := by rw [hu i, one_mul]

/-- Pauli-X（次元 2） -/
def gateX : UOp 2 := permGate (Equiv.swap 0 1)

/-- Pauli-Z（次元 2） -/
def gateZ : UOp 2 :=
  diagGate ![1, -1] (by intro i; fin_cases i <;> simp)

/-- CNOT（次元 4）：|10⟩ ↔ |11⟩ -/
def gateCNOT : UOp 4 := permGate (Equiv.swap 2 3)

/-- SWAP（次元 4）：|01⟩ ↔ |10⟩ -/
def gateSWAP : UOp 4 := permGate (Equiv.swap 1 2)

/-! ## 回路 -/

/-- 回路 = ゲート列 -/
abbrev Circuit (n : Nat) := List (UOp n)

/-- 回路の実行（先頭のゲートから順に作用） -/
def runCircuit : Circuit n → UHA n → UHA n
  | [], v => v
  | g :: gs, v => runCircuit gs (g.f v)

/-- 任意の回路はノルムを保存する（核の中心定理） -/
theorem runCircuit_norm (c : Circuit n) (v : UHA n) :
    UHA.norm (runCircuit c v) = UHA.norm v := by
  induction c generalizing v with
  | nil => rfl
  | cons g gs ih =>
    simp only [runCircuit]
    rw [ih, g.unitary_like]

/-! ## 複合系：テンソル積 -/

/-- 状態のテンソル積（次元 n * m） -/
def kron {m : Nat} (x : UHA n) (y : UHA m) : UHA (n * m) :=
  ⟨fun k =>
    x.coords (finProdFinEquiv.symm k).1 * y.coords (finProdFinEquiv.symm k).2⟩

/-- テンソル積のノルムは積になる -/
theorem norm_kron {m : Nat} (x : UHA n) (y : UHA m) :
    UHA.norm (kron x y) = UHA.norm x * UHA.norm y := by
  calc UHA.norm (kron x y)
      = ∑ k : Fin (n * m),
          (x.coords (finProdFinEquiv.symm k).1 * y.coords (finProdFinEquiv.symm k).2) *
          (x.coords (finProdFinEquiv.symm k).1 * y.coords (finProdFinEquiv.symm k).2) := rfl
    _ = ∑ p : Fin n × Fin m,
          (x.coords p.1 * y.coords p.2) * (x.coords p.1 * y.coords p.2) := by
        rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))]
        simp only [Equiv.symm_apply_apply]
    _ = UHA.norm x * UHA.norm y := by
        rw [Fintype.sum_prod_type]
        unfold UHA.norm
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by ring

end UHA

/-! ===== 世界モデル層：行動・観測・遷移・ロールアウト ===== -/

namespace UHA

variable {n : Nat} {A O : Type}

/-- 世界モデル：状態は UHA n、行動 A ごとの遷移はノルム保存作用素、観測は O への写像 -/
structure WorldModel (n : Nat) (A O : Type) where
  step : A → UOp n
  obs : UHA n → O

/-- 行動列のロールアウト（先頭の行動から順に適用） -/
def WorldModel.rollout (W : WorldModel n A O) : List A → UHA n → UHA n
  | [], s => s
  | a :: as, s => W.rollout as ((W.step a).f s)

/-- 観測列：各時点（初期状態を含む）の観測 -/
def WorldModel.trace (W : WorldModel n A O) : List A → UHA n → List O
  | [], s => [W.obs s]
  | a :: as, s => W.obs s :: W.trace as ((W.step a).f s)

/-- 任意の行動列のロールアウトはノルムを保存する -/
theorem WorldModel.rollout_norm (W : WorldModel n A O) (as : List A) (s : UHA n) :
    UHA.norm (W.rollout as s) = UHA.norm s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [WorldModel.rollout]
    rw [ih, (W.step a).unitary_like]

/-- ロールアウトは行動列の連結で分解できる -/
theorem WorldModel.rollout_append (W : WorldModel n A O) (as bs : List A) (s : UHA n) :
    W.rollout (as ++ bs) s = W.rollout bs (W.rollout as s) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, WorldModel.rollout]
    exact ih _

/-- ロールアウトは量子計算核の回路実行と一致する -/
theorem WorldModel.rollout_eq_runCircuit (W : WorldModel n A O) (as : List A) (s : UHA n) :
    W.rollout as s = runCircuit (as.map W.step) s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, WorldModel.rollout, runCircuit]
    exact ih _

/-- 観測列の長さは 行動数 + 1 -/
theorem WorldModel.trace_length (W : WorldModel n A O) (as : List A) (s : UHA n) :
    (W.trace as s).length = as.length + 1 := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [WorldModel.trace, ih]

/-- 任意の不変量 P：各ステップで保たれるなら、ロールアウト全体で保たれる -/
theorem WorldModel.rollout_invariant (W : WorldModel n A O) (P : UHA n → Prop)
    (h : ∀ a s, P s → P ((W.step a).f s)) :
    ∀ (as : List A) (s : UHA n), P s → P (W.rollout as s)
  | [], _, hs => hs
  | a :: as, s, hs => WorldModel.rollout_invariant W P h as _ (h a s hs)

/-- 可逆な世界モデル：各行動に逆作用素がある -/
structure RevWorld (n : Nat) (A O : Type) extends WorldModel n A O where
  inv : A → UOp n
  inv_step : ∀ a v, (inv a).f ((step a).f v) = v

/-- 巻き戻し：最後に適用した行動から順に逆作用素を適用する -/
def RevWorld.rollback (W : RevWorld n A O) : List A → UHA n → UHA n
  | [], s => s
  | a :: as, s => (W.inv a).f (W.rollback as s)

/-- 巻き戻しはロールアウトを完全に元へ戻す（可逆性の証明） -/
theorem RevWorld.rollback_rollout (W : RevWorld n A O) (as : List A) (s : UHA n) :
    W.rollback as (W.toWorldModel.rollout as s) = s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [RevWorld.rollback, WorldModel.rollout]
    rw [ih]
    exact W.inv_step a s

/-! ### 具体例：2 量子ビット相当（次元 4）の置換世界 -/

/-- 行動 -/
inductive Act
  | cnot
  | swap
  | idle

/-- 行動に対応する座標置換 -/
def Act.perm : Act → Equiv.Perm (Fin 4)
  | .cnot => Equiv.swap 2 3
  | .swap => Equiv.swap 1 2
  | .idle => Equiv.refl _

/-- 置換世界：観測は第 0 座標。可逆で、ノルムを保存する -/
def permWorld : RevWorld 4 Act U64 where
  step a := permGate a.perm
  obs v := v.coords 0
  inv a := permGate a.perm.symm
  inv_step a v := permGate_inv a.perm v

end UHA

/-! ===== 物理AI層：離散複素数・閉ループ制御 ===== -/

namespace Phys

variable {n : Nat} {O : Type}

/-- 離散複素数 Z/2^64 Z 上の (実部, 虚部) -/
@[ext]
structure DC where
  re : U64
  im : U64

/-- 複素数の乗法（uint64_t のラップアラウンド演算と一致） -/
def DC.mul (a b : DC) : DC :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- 複素ノルムの二乗 re² + im² -/
def DC.normSq (z : DC) : U64 := z.re * z.re + z.im * z.im

/-- ノルムは乗法的（Brahmagupta–Fibonacci の恒等式） -/
theorem DC.normSq_mul (a b : DC) : DC.normSq (DC.mul a b) = DC.normSq a * DC.normSq b := by
  simp only [DC.normSq, DC.mul]
  ring

/-- 4 分の 1 回転の単位元 1, i, -1, -i -/
def DC.rot : Fin 4 → DC
  | 0 => ⟨1, 0⟩
  | 1 => ⟨0, 1⟩
  | 2 => ⟨-1, 0⟩
  | 3 => ⟨0, -1⟩

theorem DC.normSq_rot (k : Fin 4) : DC.normSq (DC.rot k) = 1 := by
  fin_cases k <;> simp [DC.normSq, DC.rot]

/-- 離散複素ベクトル（物理状態） -/
abbrev CVec (n : Nat) := Fin n → DC

/-- 複素ノルム（保存量） -/
def cnorm (v : CVec n) : U64 := ∑ i, DC.normSq (v i)

/-- 全成分を u 倍する -/
def rotate (u : DC) (v : CVec n) : CVec n := fun i => DC.mul u (v i)

/-- 単位元（normSq u = 1）による回転は複素ノルムを保存する -/
theorem cnorm_rotate (u : DC) (hu : DC.normSq u = 1) (v : CVec n) :
    cnorm (rotate u v) = cnorm v := by
  unfold cnorm rotate
  refine Finset.sum_congr rfl fun i _ => ?_
  show DC.normSq (DC.mul u (v i)) = DC.normSq (v i)
  rw [DC.normSq_mul, hu, one_mul]

/-- 物理世界：状態は複素ベクトル、観測は O への写像 -/
structure PhysWorld (n : Nat) (O : Type) where
  obs : CVec n → O

/-- 全域的な行動デコーダ：任意の 64 ビット整数が有効な回転に写る -/
def decode (x : U64) : Fin 4 := ⟨x.val % 4, Nat.mod_lt _ (by norm_num)⟩

/-- 閉ループ制御：観測 → 方策（生の整数を出力）→ デコード → 回転 -/
def PhysWorld.closedLoop (W : PhysWorld n O) (pol : O → U64) :
    Nat → CVec n → CVec n
  | 0, s => s
  | t + 1, s => W.closedLoop pol t (rotate (DC.rot (decode (pol (W.obs s)))) s)

/-- 安全性の核心：どんな方策・どんな地平でも複素ノルムは保存される -/
theorem PhysWorld.closedLoop_cnorm (W : PhysWorld n O) (pol : O → U64) :
    ∀ (t : Nat) (s : CVec n), cnorm (W.closedLoop pol t s) = cnorm s
  | 0, _ => rfl
  | t + 1, s => by
    simp only [PhysWorld.closedLoop]
    rw [PhysWorld.closedLoop_cnorm W pol t, cnorm_rotate _ (DC.normSq_rot _)]

/-! ### 例：4 成分の物理世界と 2 つの方策 -/

/-- 符号ビットによる象限：(0,0)→0, (1,0)→1, (1,1)→2, (0,1)→3 -/
def quad (z : DC) : Nat :=
  match decide (2^63 ≤ z.re.val), decide (2^63 ≤ z.im.val) with
  | false, false => 0
  | true, false => 1
  | true, true => 2
  | false, true => 3

/-- 手書きの制御器：成分 0 を象限 0 に戻す回転を出力 -/
def goodPolicy (z : DC) : U64 := (((4 - quad z) % 4 : Nat) : U64)

/-- 未学習ネットワークを想定した任意の整数線形出力（安全性は変わらない） -/
def randPolicy (z : DC) : U64 := 3 * z.re + 5 * z.im + 6

/-- 観測は成分 0 -/
def physWorld4 : PhysWorld 4 DC := ⟨fun v => v 0⟩

def pv0 : CVec 4 := fun i =>
  ([⟨9223372036854775813, 5⟩, ⟨-1, 3⟩, ⟨7, 0⟩, ⟨0, 4294967296⟩] : List DC).getD i.val ⟨0, 0⟩

def showC (v : CVec 4) : String :=
  String.intercalate " " ((List.finRange 4).map fun i => s!"{(v i).re.val},{(v i).im.val}")

end Phys

/-! ===== C++ 照合用テストベクトル生成 ===== -/

open UHA
open Phys

def ofList4 (a b c d : U64) : UHA 4 := ⟨![a, b, c, d]⟩

def showState (v : UHA 4) : String :=
  String.intercalate " " ((List.finRange 4).map fun i => toString (v.coords i).val)

def main : IO Unit := do
  let v := ofList4 9223372036854775813 (-1) 7 4294967296
  IO.println s!"v {showState v}"
  IO.println s!"norm {(UHA.norm v).val}"
  let w1 := gateCNOT.f v
  IO.println s!"cnot {showState w1}"
  let w2 := gateSWAP.f w1
  IO.println s!"swap {showState w2}"
  IO.println s!"norm {(UHA.norm w2).val}"
  let acts := [Act.cnot, Act.swap]
  let tr := permWorld.toWorldModel.trace acts v
  IO.println s!"trace {tr.map (·.val)}"
  let back := permWorld.rollback acts (permWorld.toWorldModel.rollout acts v)
  IO.println s!"rollback {showState back}"
  IO.println s!"pv {showC pv0}"
  IO.println s!"pcnorm {(cnorm pv0).val}"
  let g := physWorld4.closedLoop goodPolicy 3 pv0
  IO.println s!"pgood {showC g}"
  IO.println s!"pgoodnorm {(cnorm g).val}"
  let r := physWorld4.closedLoop randPolicy 3 pv0
  IO.println s!"prand {showC r}"
  IO.println s!"prandnorm {(cnorm r).val}"
