/-!
  ACM-TY: Abstract Computation Model — 完全版 Lean 4 実装
  UHA × BSCM × DIFD × GIFE × Evolution
  License: Apache 2.0
  Author: Takeo Yamamoto

  層構造:
  * 基底核  : `U64 := ZMod (2^64)` 上の UHA（加群・双線形乗法・ノルム二乗）
  * 離散層  : BSCM（`ZMod.val` で ℕ に降ろして定義・定理つき）
  * 流体層  : DIFD（逆元を使わず、ℕ 上の重み付き平均で拡散を定義）
  * 場・力学・進化 : GIFE / Dynamics / Evolution / Takeo 進化
  * 統合    : Engine・step

  元コードからの意図的な変更点:
  * コメント記法を Lean の `/-! -/` に修正。
  * `<`、`/`、`%`、`>>>`、`&&&` は `.val : ℕ` 経由に置換（`ZMod (2^64)` には無いため）。
  * `norm⁻¹`（偶数に逆元なし）をやめ、ℕ 上の整数除算による重み付き平均に変更。
  * `Fin n` への `% n` は `[NeZero n]` と `idx` で定義。
  * 関数フィールドを持つ構造体の `deriving Repr` を削除。
  * `stepTakeo`: 環境が変化しないとき `prev` ではなく `curr` を返す（動力学が止まらないように）。
    変化時は `curr.entities ++ core.diversity` から最良個体を選び、個体群の先頭に置く。
  * `argmaxEntity` はダミー個体ではなく `Option` を返す。
-/

import Mathlib

open BigOperators

/-! ## 0. 基底環 -/

/-- 基底環：mod 2^64 の整数環。 -/
abbrev U64 := ZMod (2 ^ 64)

instance : NeZero (2 ^ 64 : ℕ) := ⟨by norm_num⟩

/-- 2^64 未満の自然数のキャストは値を保つ。 -/
theorem U64.val_natCast_of_lt {m : ℕ} (h : m < 2 ^ 64) : ((m : ℕ) : U64).val = m := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

/-! ## 1. UHA — UltraCore HyperAlgebra（連続核） -/

/-- n 個の座標を持つ U64 加群。 -/
abbrev UHA (n : ℕ) := Fin n → U64

namespace UHA

variable {n : ℕ}

/-- 座標の取り出し（`UHA n` は関数そのもの）。 -/
abbrev coords (x : UHA n) : Fin n → U64 := x

/-- 標準基底ベクトル。 -/
def single (i : Fin n) (a : U64) : UHA n :=
  Pi.single i a

/-- 多元代数乗法。構造定数 `c j k : UHA n` を外部から与える。 -/
def mulWith (c : Fin n → Fin n → UHA n) (x y : UHA n) : UHA n :=
  fun i => ∑ j : Fin n, ∑ k : Fin n, x j * y k * c j k i

theorem mulWith_add_left (c : Fin n → Fin n → UHA n) (x x' y : UHA n) :
    mulWith c (x + x') y = mulWith c x y + mulWith c x' y := by
  funext i
  simp only [mulWith, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem mulWith_add_right (c : Fin n → Fin n → UHA n) (x y y' : UHA n) :
    mulWith c x (y + y') = mulWith c x y + mulWith c x y' := by
  funext i
  simp only [mulWith, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem mulWith_smul_left (c : Fin n → Fin n → UHA n) (a : U64) (x y : UHA n) :
    mulWith c (a • x) y = a • mulWith c x y := by
  funext i
  simp only [mulWith, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mulWith_smul_right (c : Fin n → Fin n → UHA n) (a : U64) (x y : UHA n) :
    mulWith c x (a • y) = a • mulWith c x y := by
  funext i
  simp only [mulWith, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `mulWith c` を U64 上の双線形写像として束ねたもの。 -/
def mulBilin (c : Fin n → Fin n → UHA n) : UHA n →ₗ[U64] UHA n →ₗ[U64] UHA n :=
  LinearMap.mk₂ U64 (mulWith c)
    (mulWith_add_left c) (mulWith_smul_left c)
    (mulWith_add_right c) (mulWith_smul_right c)

@[simp] theorem mulBilin_apply (c : Fin n → Fin n → UHA n) (x y : UHA n) :
    mulBilin c x y = mulWith c x y := rfl

theorem mulWith_zero_left (c : Fin n → Fin n → UHA n) (y : UHA n) :
    mulWith c 0 y = 0 := by
  funext i
  simp [mulWith]

theorem mulWith_zero_right (c : Fin n → Fin n → UHA n) (x : UHA n) :
    mulWith c x 0 = 0 := by
  funext i
  simp [mulWith]

/-- 標準双線形形式。 -/
def dot (x y : UHA n) : U64 :=
  ∑ i : Fin n, x i * y i

/-- ノルム二乗。mod 2^64 の値であり、実数的な大きさではない。 -/
def normSq (x : UHA n) : U64 :=
  dot x x

theorem dot_comm (x y : UHA n) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot_add_left (x x' y : UHA n) :
    dot (x + x') y = dot x y + dot x' y := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_add_right (x y y' : UHA n) :
    dot x (y + y') = dot x y + dot x y' := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_smul_left (a : U64) (x y : UHA n) :
    dot (a • x) y = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_smul_right (a : U64) (x y : UHA n) :
    dot x (a • y) = a * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem normSq_zero : normSq (0 : UHA n) = 0 := by
  simp [normSq, dot]

theorem normSq_smul (a : U64) (x : UHA n) :
    normSq (a • x) = a * a * normSq x := by
  unfold normSq
  rw [dot_smul_left, dot_smul_right, mul_assoc]

theorem normSq_add (x y : UHA n) :
    normSq (x + y) = normSq x + 2 * dot x y + normSq y := by
  unfold normSq
  rw [dot_add_left, dot_add_right, dot_add_right, dot_comm y x]
  ring

theorem normSq_neg (x : UHA n) : normSq (-x) = normSq x := by
  have h : -x = (-1 : U64) • x := by simp
  rw [h, normSq_smul]
  ring

/-- ノルム二乗を保つ作用素（量子ゲートの離散版）。 -/
structure UOp (n : ℕ) where
  f : UHA n → UHA n
  preserves : ∀ v, normSq (f v) = normSq v

namespace UOp

/-- 恒等作用素。 -/
def id : UOp n := ⟨fun v => v, fun _ => rfl⟩

/-- 合成。 -/
def comp (g h : UOp n) : UOp n :=
  ⟨fun v => g.f (h.f v), fun v => by rw [g.preserves, h.preserves]⟩

@[simp] theorem id_f (v : UHA n) : (id : UOp n).f v = v := rfl

@[simp] theorem comp_f (g h : UOp n) (v : UHA n) :
    (comp g h).f v = g.f (h.f v) := rfl

theorem comp_id (g : UOp n) : comp g id = g := rfl

theorem id_comp (g : UOp n) : comp id g = g := rfl

end UOp

/-- 符号反転はノルム二乗を保つ。 -/
def negOp : UOp n := ⟨fun v => -v, normSq_neg⟩

/-- 座標の置換はノルム二乗を保つ。 -/
def permOp (σ : Equiv.Perm (Fin n)) : UOp n :=
  ⟨fun v i => v (σ i), fun v => by
    unfold normSq dot
    exact Equiv.sum_comp σ (fun i => v i * v i)⟩

end UHA

/-! ## 2. BSCM — Discrete Control Core（離散核）

  すべて `ZMod.val : ℕ` に降ろして定義する。 -/

namespace BSCM

/-- 離散状態更新：`⌈s/2⌉`（偶数なら `s/2`、奇数なら `(s+1)/2`）。 -/
def delta (s : U64) : U64 :=
  (((s.val + 1) / 2 : ℕ) : U64)

theorem delta_val (s : U64) : (delta s).val = (s.val + 1) / 2 := by
  have h : s.val < 2 ^ 64 := ZMod.val_lt s
  unfold delta
  apply U64.val_natCast_of_lt
  omega

theorem delta_val_le (s : U64) : (delta s).val ≤ s.val := by
  rw [delta_val]
  omega

/-- `s ≥ 2` なら厳密に減少する（停止性の核）。 -/
theorem delta_val_lt (s : U64) (h : 2 ≤ s.val) : (delta s).val < s.val := by
  rw [delta_val]
  omega

theorem delta_zero : delta 0 = 0 := by
  unfold delta
  simp

/-- `delta` の反復。 -/
def deltaIter : ℕ → U64 → U64
  | 0, s => s
  | k + 1, s => deltaIter k (delta s)

theorem deltaIter_val_le (k : ℕ) (s : U64) : (deltaIter k s).val ≤ s.val := by
  induction k generalizing s with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (ih (delta s)) (delta_val_le s)

/-- 外部入力付き制御ステップ（加算は mod 2^64）。 -/
def controlStep (current_state external_input : U64) : U64 :=
  delta (current_state + external_input)

/-- 簡易エントロピー指標（下位 2 バイトの和）。 -/
def entropy (s : U64) : U64 :=
  ((s.val % 256 + (s.val / 256) % 256 : ℕ) : U64)

theorem entropy_val (s : U64) : (entropy s).val = s.val % 256 + (s.val / 256) % 256 := by
  unfold entropy
  apply U64.val_natCast_of_lt
  omega

theorem entropy_val_le (s : U64) : (entropy s).val ≤ 510 := by
  rw [entropy_val]
  omega

end BSCM

/-! ## 3. GIFE — General Information Field Engine（場核） -/

structure Entity (n : ℕ) where
  id       : ℕ
  state    : UHA n
  energy   : U64
  mood     : U64
  genome   : U64
  discrete : U64

/-- Topology：接続行列による接続構造。 -/
structure Topology (n : ℕ) where
  conn      : Fin n → Fin n → U64
  viscosity : U64
  curvature : U64

structure FieldState (n : ℕ) where
  entities : List (Entity n)
  entropy  : U64
  topology : Topology n

/-- 自然数 `k` を `Fin n` の添字に写す（`n > 0` が必要）。 -/
def idx (n : ℕ) [NeZero n] (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

/-! ## 4. DIFD — Discrete Fluid Dynamics（流体核） -/

namespace DIFD

/-- 粘性クリップ（上限 10^6）。 -/
def clipViscosity (v : U64) : U64 :=
  if 1000000 < v.val then ((1000000 : ℕ) : U64) else v

/-- 渦度減衰。 -/
def decayVortex (c : U64) : U64 :=
  ((c.val / 2 : ℕ) : U64)

/-- 圧力正規化（上限 10^12）。 -/
def normalizePressure (p : U64) : U64 :=
  if 10 ^ 12 < p.val then ((10 ^ 12 : ℕ) : U64) else p

theorem clipViscosity_val_le (v : U64) : (clipViscosity v).val ≤ 1000000 ∨ clipViscosity v = v := by
  unfold clipViscosity
  split
  · left
    exact (U64.val_natCast_of_lt (by norm_num)).le
  · right; rfl

/-- CFL 条件（簡易版）：`normSq` は mod 2^64、比較は ℕ 上。 -/
def cfl {n : ℕ} (vel : UHA n) (visc : U64) : Bool :=
  decide (vel.normSq.val < visc.val * visc.val)

/-- `e` と近傍 `nb` の間の重み。 -/
def weight {n : ℕ} [NeZero n] (top : Topology n) (e nb : Entity n) : U64 :=
  top.conn (idx n e.id) (idx n nb.id)

/-- 離散拡散：近傍状態の重み付き平均。逆元は使わず、ℕ 上の整数除算で定義する。
    重みの総和が 0 のときは自分の状態を返す。 -/
def diffuse {n : ℕ} [NeZero n]
    (top : Topology n) (e : Entity n) (neighbors : List (Entity n)) : UHA n :=
  let W : ℕ := (neighbors.map (fun nb => (weight top e nb).val)).sum
  if W = 0 then e.state
  else fun i =>
    (((neighbors.map (fun nb => (weight top e nb).val * (nb.state i).val)).sum / W : ℕ) : U64)

theorem diffuse_nil {n : ℕ} [NeZero n] (top : Topology n) (e : Entity n) :
    diffuse top e [] = e.state := by
  simp [diffuse]

/-- 離散渦度。 -/
def vortex {n : ℕ} (top : Topology n) (e : Entity n) : UHA n :=
  decayVortex top.curvature • e.state

/-- 離散圧力。 -/
def pressure {n : ℕ} (ent : U64) (e : Entity n) : UHA n :=
  normalizePressure ent • e.state

/-- 流体更新則。CFL を満たさないときは状態を変えない。 -/
def fluidUpdate {n : ℕ} [NeZero n]
    (top : Topology n) (ent : U64) (e : Entity n) (neighbors : List (Entity n)) : UHA n :=
  let visc := clipViscosity top.viscosity
  let d    := diffuse top e neighbors
  let v    := vortex top e
  let p    := pressure ent e
  if cfl d visc then d + v + p else e.state

theorem fluidUpdate_of_not_cfl {n : ℕ} [NeZero n]
    (top : Topology n) (ent : U64) (e : Entity n) (neighbors : List (Entity n))
    (h : cfl (diffuse top e neighbors) (clipViscosity top.viscosity) = false) :
    fluidUpdate top ent e neighbors = e.state := by
  simp [fluidUpdate, h]

theorem fluidUpdate_of_cfl {n : ℕ} [NeZero n]
    (top : Topology n) (ent : U64) (e : Entity n) (neighbors : List (Entity n))
    (h : cfl (diffuse top e neighbors) (clipViscosity top.viscosity) = true) :
    fluidUpdate top ent e neighbors
      = diffuse top e neighbors + vortex top e + pressure ent e := by
  simp [fluidUpdate, h]

end DIFD

/-! ## 5. Dynamics & Evolution（力学核＋進化核） -/

structure Dynamics (n : ℕ) where
  updateEntity   : Entity n → U64 → Entity n
  updateEntropy  : FieldState n → U64
  updateTopology : Topology n → List (Entity n) → Topology n

structure Evolution (n : ℕ) where
  mutate : Entity n → Entity n
  select : List (Entity n) → List (Entity n)
  adapt  : Entity n → U64 → Entity n

structure EvolutionCore (n : ℕ) where
  fitness   : Entity n → FieldState n → U64
  diversity : List (Entity n)

/-! ## 6. BSCM ↔ UHA 統合（離散と連続の結合） -/

namespace Unified

variable {n : ℕ}

/-- 離散 → 連続。 -/
def discreteToContinuous (d : U64) (x : UHA n) : UHA n :=
  BSCM.entropy d • x

/-- 連続 → 離散。 -/
def continuousToDiscrete (x : UHA n) : U64 :=
  BSCM.controlStep x.normSq (BSCM.entropy x.normSq)

theorem normSq_discreteToContinuous (d : U64) (x : UHA n) :
    (discreteToContinuous d x).normSq = BSCM.entropy d * BSCM.entropy d * x.normSq :=
  UHA.normSq_smul _ _

end Unified

/-! ## 7. Engine & 統合ステップ -/

structure Engine (n : ℕ) where
  dynamics  : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)

/-- 統合 Entity 更新（DIFD + BSCM-UHA）。 -/
def updateEntityUnified {n : ℕ} [NeZero n]
    (dyn : Dynamics n) (top : Topology n) (ent : U64)
    (neighbors : List (Entity n)) (e : Entity n) : Entity n :=
  let fluidState := DIFD.fluidUpdate top ent e neighbors
  let contState  := Unified.discreteToContinuous e.discrete fluidState
  let newDisc    := Unified.continuousToDiscrete contState
  let base       := dyn.updateEntity e ent
  { base with state := contState, discrete := newDisc }

/-- 従来進化ステップ（GIFE + DIFD + Evolution + BSCM-UHA）。 -/
def stepClassic {n : ℕ} [NeZero n] (eng : Engine n) (s : FieldState n) : FieldState n :=
  let updated :=
    s.entities.map (fun e =>
      updateEntityUnified eng.dynamics s.topology s.entropy s.entities e)
  let adapted  := updated.map (fun e => eng.evolution.adapt e s.entropy)
  let selected := eng.evolution.select adapted
  let mutated  := selected.map eng.evolution.mutate
  let newTopology := eng.dynamics.updateTopology s.topology mutated
  let interimState : FieldState n :=
    { entities := mutated, entropy := s.entropy, topology := newTopology }
  let newEntropy := eng.dynamics.updateEntropy interimState
  { entities := mutated, entropy := newEntropy, topology := newTopology }

/-! ## 8. Takeo Evolution（環境変化時のみ進化） -/

/-- 環境（エントロピー・粘性・曲率）が変化したか。 -/
def envChanged {n : ℕ} (prev curr : FieldState n) : Bool :=
  decide (prev.entropy ≠ curr.entropy ∨
    prev.topology.viscosity ≠ curr.topology.viscosity ∨
    prev.topology.curvature ≠ curr.topology.curvature)

/-- 適応度が最大の個体（同点は先に現れた方）。空リストなら `none`。 -/
def argmax? {n : ℕ} (fit : Entity n → U64) : List (Entity n) → Option (Entity n)
  | []      => none
  | e :: es =>
    some (es.foldl (fun best cand => if (fit best).val < (fit cand).val then cand else best) e)

theorem argmax?_nil {n : ℕ} (fit : Entity n → U64) : argmax? fit [] = none := rfl

theorem argmax?_isSome {n : ℕ} (fit : Entity n → U64) (l : List (Entity n)) (h : l ≠ []) :
    (argmax? fit l).isSome = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons e es => simp [argmax?]

/-- Takeo モデル：環境変化時のみ進化を適用する。
    `curr` は動力学を進めた後の状態。変化がなければ `curr` をそのまま返す。 -/
def stepTakeo {n : ℕ}
    (core : EvolutionCore n) (prev curr : FieldState n) : FieldState n :=
  if envChanged prev curr then
    match argmax? (fun e => core.fitness e curr) (curr.entities ++ core.diversity) with
    | none      => curr
    | some best =>
      { curr with entities := best :: curr.entities.filter (fun e => e.id != best.id) }
  else curr

theorem stepTakeo_of_unchanged {n : ℕ}
    (core : EvolutionCore n) (prev curr : FieldState n)
    (h : envChanged prev curr = false) :
    stepTakeo core prev curr = curr := by
  simp [stepTakeo, h]

/-- 統合ステップ：Takeo 進化あり／なしを切り替える。 -/
def step {n : ℕ} [NeZero n] (eng : Engine n) (s : FieldState n) : FieldState n :=
  match eng.takeoCore with
  | none      => stepClassic eng s
  | some core => stepTakeo core s (stepClassic eng s)

theorem step_none {n : ℕ} [NeZero n] (eng : Engine n) (s : FieldState n)
    (h : eng.takeoCore = none) : step eng s = stepClassic eng s := by
  simp [step, h]

theorem step_some_unchanged {n : ℕ} [NeZero n] (eng : Engine n) (s : FieldState n)
    (core : EvolutionCore n) (h : eng.takeoCore = some core)
    (hc : envChanged s (stepClassic eng s) = false) :
    step eng s = stepClassic eng s := by
  simp [step, h, stepTakeo, hc]

/-- `k` ステップ進める。 -/
def run {n : ℕ} [NeZero n] (eng : Engine n) : ℕ → FieldState n → FieldState n
  | 0,     s => s
  | k + 1, s => run eng k (step eng s)

@[simp] theorem run_zero {n : ℕ} [NeZero n] (eng : Engine n) (s : FieldState n) :
    run eng 0 s = s := rfl

theorem run_succ {n : ℕ} [NeZero n] (eng : Engine n) (k : ℕ) (s : FieldState n) :
    run eng (k + 1) s = run eng k (step eng s) := rfl
