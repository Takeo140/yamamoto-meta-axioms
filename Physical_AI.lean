/-
  ACM-TY: Abstract Computation Model — Takeo Yamamoto
  UHA × BSCM × DIFD × GIFE × Evolution  +  Physical AI（群ロボット制御・fail-closed）
  License: Apache 2.0
  Author: Takeo Yamamoto
-/

import Mathlib
import WorldModel

open BigOperators
open Classical

namespace ACMTY

/-! ## 0. 基本定義 -/

abbrev U64 := WorldModel.U64

/-! ## 1. UHA — UltraCore HyperAlgebra（連続核） -/

structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

def zero : UHA n := ⟨fun _ => 0⟩

def add (x y : UHA n) : UHA n :=
  ⟨fun i => x.coords i + y.coords i⟩

instance : Add (UHA n) := ⟨add⟩

def smul (a : U64) (x : UHA n) : UHA n :=
  ⟨fun i => a * x.coords i⟩

instance : SMul U64 (UHA n) := ⟨smul⟩

/-- 多元代数乗法（構造定数 c を外部から与える） -/
def mulWith (c : Fin n → Fin n → UHA n) (x y : UHA n) : UHA n :=
  ⟨fun i => ∑ j : Fin n, ∑ k : Fin n, (x.coords j) * (y.coords k) * (c j k).coords i⟩

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  ∑ i : Fin n, (x.coords i) * (x.coords i)

theorem norm_zero : norm (zero : UHA n) = 0 := by
  simp [norm, zero]

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

end UHA

/-! ## 2. BSCM — Discrete Control Core（離散核）
    ZMod 上では `%` `/` `&&&` `>>>` が使えないため、`val : Nat` 経由で定義する。 -/

namespace BSCM

def delta (s : U64) : U64 :=
  let v := s.val
  if v % 2 = 0 then ((v / 2 : Nat) : U64) else (((v + 1) / 2 : Nat) : U64)

def controlStep (current_state external_input : U64) : U64 :=
  delta (current_state + external_input)

/-- 簡易エントロピー指標（下位2バイトの和） -/
def entropy (s : U64) : U64 :=
  let v := s.val
  ((v % 256 + (v / 256) % 256 : Nat) : U64)

end BSCM

/-! ## 3. GIFE — General Information Field Engine（場核） -/

structure Entity (n : Nat) where
  id       : Nat
  state    : UHA n
  energy   : U64
  mood     : U64
  genome   : U64
  discrete : U64

structure Topology (n : Nat) where
  connMatrix : Fin n → Fin n → U64
  viscosity  : U64
  curvature  : U64

namespace Topology

variable {n : Nat}

def conn (top : Topology n) (i j : Fin n) : U64 :=
  top.connMatrix i j

end Topology

structure FieldState (n : Nat) where
  entities : List (Entity n)
  entropy  : U64
  topology : Topology n

/-- id を Fin n に安全に写す（n = 0 なら none）。 -/
def idx? (n k : Nat) : Option (Fin n) :=
  if h : k % n < n then some ⟨k % n, h⟩ else none

def connAt {n : Nat} (top : Topology n) (a b : Nat) : U64 :=
  match idx? n a, idx? n b with
  | some i, some j => top.conn i j
  | _, _ => 0

/-! ## 4. DIFD — Discrete Fluid Dynamics（流体核） -/

namespace DIFD

variable {n : Nat}

def clipViscosity (v : U64) : U64 :=
  if v.val > 1000000 then (1000000 : U64) else v

def decayVortex (c : U64) : U64 :=
  ((c.val / 2 : Nat) : U64)

def normalizePressure (p : U64) : U64 :=
  if p.val > 10 ^ 12 then ((10 ^ 12 : Nat) : U64) else p

/-- CFL 条件（簡易版） -/
def cfl (vel : UHA n) (visc : U64) : Bool :=
  decide (vel.norm.val < (visc * visc).val)

/-- 離散拡散：隣接 Entity の UHA 状態を重み付き平均 -/
def diffuse (top : Topology n) (e : Entity n) (neighbors : List (Entity n)) : UHA n :=
  let total : UHA n :=
    neighbors.foldl
      (fun acc nb => UHA.add acc (UHA.smul (connAt top e.id nb.id) nb.state))
      UHA.zero
  let w : U64 :=
    neighbors.foldl (fun a nb => a + connAt top e.id nb.id) 0
  if w = 0 then e.state else UHA.smul w⁻¹ total

def vortex (top : Topology n) (e : Entity n) : UHA n :=
  UHA.smul (decayVortex top.curvature) e.state

def pressure (entropy : U64) (e : Entity n) : UHA n :=
  UHA.smul (normalizePressure entropy) e.state

def fluidUpdate (top : Topology n) (entropy : U64) (e : Entity n)
    (neighbors : List (Entity n)) : UHA n :=
  let visc := clipViscosity top.viscosity
  let d    := diffuse top e neighbors
  let v    := vortex top e
  let p    := pressure entropy e
  if cfl d visc then UHA.add (UHA.add d v) p else e.state

end DIFD

/-! ## 5. Dynamics & Evolution -/

structure Dynamics (n : Nat) where
  updateEntity   : Entity n → U64 → Entity n
  updateEntropy  : FieldState n → U64
  updateTopology : Topology n → List (Entity n) → Topology n

structure Evolution (n : Nat) where
  mutate : Entity n → Entity n
  select : List (Entity n) → List (Entity n)
  adapt  : Entity n → U64 → Entity n

structure EvolutionCore (n : Nat) where
  fitness   : Entity n → FieldState n → U64
  diversity : List (Entity n)

/-! ## 6. BSCM ↔ UHA 統合 -/

namespace Unified

variable {n : Nat}

def discreteToContinuous (d : U64) (x : UHA n) : UHA n :=
  UHA.smul (BSCM.entropy d) x

def continuousToDiscrete (x : UHA n) : U64 :=
  BSCM.controlStep x.norm (BSCM.entropy x.norm)

end Unified

/-! ## 7. Engine & 統合ステップ -/

structure Engine (n : Nat) where
  dynamics  : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)

def updateEntityUnified {n : Nat} (dyn : Dynamics n) (top : Topology n) (entropy : U64)
    (neighbors : List (Entity n)) (e : Entity n) : Entity n :=
  let fluidState := DIFD.fluidUpdate top entropy e neighbors
  let contState  := Unified.discreteToContinuous e.discrete fluidState
  let newDisc    := Unified.continuousToDiscrete contState
  let base       := dyn.updateEntity e entropy
  { base with state := contState, discrete := newDisc }

def stepClassic {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  let updated :=
    s.entities.map (fun e => updateEntityUnified eng.dynamics s.topology s.entropy s.entities e)
  let adapted  := updated.map (fun e => eng.evolution.adapt e s.entropy)
  let selected := eng.evolution.select adapted
  let mutated  := selected.map eng.evolution.mutate
  let newTopology := eng.dynamics.updateTopology s.topology mutated
  let interimState : FieldState n :=
    { entities := mutated, entropy := s.entropy, topology := newTopology }
  let newEntropy := eng.dynamics.updateEntropy interimState
  { entities := mutated, entropy := newEntropy, topology := newTopology }

/-! ## 8. Takeo Evolution（環境変化時のみ進化） -/

def envChanged {n : Nat} (prev curr : FieldState n) : Bool :=
  decide (prev.entropy ≠ curr.entropy ∨
    prev.topology.viscosity ≠ curr.topology.viscosity ∨
    prev.topology.curvature ≠ curr.topology.curvature)

def argmaxEntity {n : Nat} (core : EvolutionCore n) (env : FieldState n) : Entity n :=
  match core.diversity with
  | [] => { id := 0, state := UHA.zero, energy := 0, mood := 0, genome := 0, discrete := 0 }
  | e :: es =>
    es.foldl
      (fun best cand =>
        if (core.fitness best env).val < (core.fitness cand env).val then cand else best)
      e

def stepTakeo {n : Nat} (_eng : Engine n) (core : EvolutionCore n)
    (prev curr : FieldState n) : FieldState n :=
  if envChanged prev curr then
    { entities := [argmaxEntity core curr], entropy := curr.entropy, topology := curr.topology }
  else prev

def step {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  match eng.takeoCore with
  | none => stepClassic eng s
  | some core => stepTakeo eng core s (stepClassic eng s)

/-! ## 9. Physical AI — 群ロボット制御（fail-closed） -/

/-- 汎用ガード付き系：提案 (propose) は、センサが信頼でき、かつ
    提案後の状態が安全な場合だけ採用。それ以外は必ず fallback。 -/
structure Guarded (S : Type*) where
  propose : S → S
  fallback : S → S
  safe : S → Prop
  trusted : S → Prop                         -- センサ健全性
  fallback_safe : ∀ s, safe s → safe (fallback s)

noncomputable def Guarded.step {S : Type*} (G : Guarded S) (s : S) : S :=
  if G.trusted s ∧ G.safe (G.propose s) then G.propose s else G.fallback s

noncomputable def Guarded.run {S : Type*} (G : Guarded S) : Nat → S → S
  | 0, s => s
  | k + 1, s => Guarded.run G k (G.step s)

theorem Guarded.step_safe {S : Type*} (G : Guarded S) {s : S} (h : G.safe s) :
    G.safe (G.step s) := by
  unfold Guarded.step
  by_cases hc : G.trusted s ∧ G.safe (G.propose s)
  · rw [if_pos hc]
    exact hc.2
  · rw [if_neg hc]
    exact G.fallback_safe _ h

theorem Guarded.run_safe {S : Type*} (G : Guarded S) (k : Nat) :
    ∀ s, G.safe s → G.safe (G.run k s) := by
  induction k with
  | zero => intro s h; exact h
  | succ k ih =>
    intro s h
    show G.safe (G.run k (G.step s))
    exact ih _ (G.step_safe h)

/-- センサ不信 → 必ず fallback（fail-closed）。 -/
theorem Guarded.fail_closed_untrusted {S : Type*} (G : Guarded S) {s : S}
    (h : ¬ G.trusted s) : G.step s = G.fallback s := by
  unfold Guarded.step
  rw [if_neg (fun hc => h hc.1)]

/-- 提案が危険 → 決して採用されない。 -/
theorem Guarded.fail_closed_unsafe {S : Type*} (G : Guarded S) {s : S}
    (h : ¬ G.safe (G.propose s)) : G.step s = G.fallback s := by
  unfold Guarded.step
  rw [if_neg (fun hc => h hc.2)]

/-! ### 群ロボットの安全仕様 -/

structure SwarmLimits where
  vmax : Nat          -- 速度（ノルム）上限
  minEnergy : Nat     -- 最低バッテリー
  maxRobots : Nat     -- 台数上限

def swarmSafe {n : Nat} (lim : SwarmLimits) (s : FieldState n) : Prop :=
  s.entities.length ≤ lim.maxRobots ∧
  ∀ e ∈ s.entities, lim.minEnergy ≤ e.energy.val ∧ e.state.norm.val ≤ lim.vmax

/-- 緊急ブレーキ：全ロボットの状態（速度成分）をゼロにする。 -/
def brakeEntity {n : Nat} (e : Entity n) : Entity n := { e with state := UHA.zero }

def brake {n : Nat} (s : FieldState n) : FieldState n :=
  { s with entities := s.entities.map brakeEntity }

theorem brake_safe {n : Nat} (lim : SwarmLimits) {s : FieldState n}
    (h : swarmSafe lim s) : swarmSafe lim (brake s) := by
  unfold swarmSafe at h ⊢
  refine ⟨?_, ?_⟩
  · show (s.entities.map brakeEntity).length ≤ lim.maxRobots
    rw [List.length_map]
    exact h.1
  · intro e he
    have he' : e ∈ s.entities.map brakeEntity := he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he'
    refine ⟨(h.2 a ha).1, ?_⟩
    show (UHA.norm (UHA.zero : UHA n)).val ≤ lim.vmax
    rw [UHA.norm_zero, ZMod.val_zero]
    exact Nat.zero_le _

/-- ACM-TY エンジンを、安全ガード付き Physical AI として包む。 -/
noncomputable def swarmGuard {n : Nat} (eng : Engine n) (lim : SwarmLimits)
    (trusted : FieldState n → Prop) : Guarded (FieldState n) where
  propose := ACMTY.step eng
  fallback := brake
  safe := swarmSafe lim
  trusted := trusted
  fallback_safe := fun _ h => brake_safe lim h

/-- 総合保証：安全な群れは、何ステップ実行しても安全。 -/
theorem swarm_safe_forever {n : Nat} (eng : Engine n) (lim : SwarmLimits)
    (trusted : FieldState n → Prop) (k : Nat) (s : FieldState n)
    (h : swarmSafe lim s) : swarmSafe lim ((swarmGuard eng lim trusted).run k s) :=
  (swarmGuard eng lim trusted).run_safe k s h

/-! ### WorldModel / UHA への接続 -/

def Guarded.toWorldModel {S : Type*} {m : Nat} (G : Guarded S)
    (enc : WorldModel.WorldEncoding S m)
    (comp : WorldModel.UHAState m → WorldModel.UHAState m)
    (h : ∀ s, comp (enc.encode s) = enc.encode (G.step s)) :
    WorldModel.WorldModel S m where
  encoding := enc
  worldTransition := G.step
  computationalTransition := comp
  transition_commutes := h

theorem Guarded.worldIter_eq_run {S : Type*} {m : Nat} (G : Guarded S)
    (enc : WorldModel.WorldEncoding S m)
    (comp : WorldModel.UHAState m → WorldModel.UHAState m)
    (h : ∀ s, comp (enc.encode s) = enc.encode (G.step s)) (k : Nat) :
    ∀ s, WorldModel.worldIter (G.toWorldModel enc comp h) k s = G.run k s := by
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    show WorldModel.worldIter (G.toWorldModel enc comp h) k (G.step s) = G.run k (G.step s)
    exact ih (G.step s)

/-- 安全性 ＋ UHA 計算軌道と物理軌道の一致。 -/
theorem Guarded.guarantee {S : Type*} {m : Nat} (G : Guarded S)
    (enc : WorldModel.WorldEncoding S m)
    (comp : WorldModel.UHAState m → WorldModel.UHAState m)
    (h : ∀ s, comp (enc.encode s) = enc.encode (G.step s)) (k : Nat) (s : S)
    (hs : G.safe s) :
    G.safe (G.run k s) ∧
      WorldModel.compIter (G.toWorldModel enc comp h) k (enc.encode s) =
        enc.encode (G.run k s) := by
  refine ⟨G.run_safe k s hs, ?_⟩
  rw [← G.worldIter_eq_run enc comp h k s]
  exact WorldModel.compIter_encode (G.toWorldModel enc comp h) k s

/-! ## 10. 簡易テスト -/

def sampleUHA : UHA 4 :=
  ⟨fun i =>
    match i.1 with
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | _ => 4⟩

#eval (UHA.norm sampleUHA).val

end ACMTY
