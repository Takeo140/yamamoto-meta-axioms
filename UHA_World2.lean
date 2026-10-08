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

/-! ===== C++ 照合用テストベクトル生成 ===== -/

open UHA

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
