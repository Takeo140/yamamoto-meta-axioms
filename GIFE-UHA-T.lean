/-
  General Information Field Engine + UHA Core + Takeo Evolution
  License: Apache 2.0
  Author: Takeo Yamamoto
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic

/-- UltraCore の基本スカラー：U64 有限環 -/
abbrev U64 := ZMod (2^64)

/-- UltraCore HyperAlgebra の n 次元キャリア -/
structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

/-- 加算（branchless） -/
def add (x y : UHA n) : UHA n :=
  ⟨fun i => x.coords i + y.coords i⟩

instance : Add (UHA n) := ⟨add⟩

/-- スカラー倍 -/
def smul (a : U64) (x : UHA n) : UHA n :=
  ⟨fun i => a * x.coords i⟩

instance : SMul U64 (UHA n) := ⟨smul⟩

/-- 多元代数の乗法（構造定数を外部から与える） -/
def mulWith
  (c : Fin n → Fin n → UHA n)
  (x y : UHA n) : UHA n :=
  ⟨fun i =>
    ∑ j : Fin n, ∑ k : Fin n, (x.coords j) * (y.coords k) * (c j k).coords i
  ⟩

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  ∑ i : Fin n, (x.coords i) * (x.coords i)

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, norm (f v) = norm v

end UHA

/-
  ここから汎用情報場エンジン（GIFE）
-/

/-- Entity：UHA を内部状態として持つ場の構成要素 -/
structure Entity (n : Nat) where
  id     : Nat
  state  : UHA n
  energy : U64
  mood   : U64
  genome : U64

/-- Topology：場の接続構造 -/
structure Topology (n : Nat) where
  conn      : Entity n → Entity n → U64
  viscosity : U64
  curvature : U64

/-- State：場の状態 -/
structure FieldState (n : Nat) where
  entities : List (Entity n)
  entropy  : U64
  topology : Topology n

/-- Dynamics：場の力学（UHA を内部計算核として使用） -/
structure Dynamics (n : Nat) where
  updateEntity :
    Entity n → U64 → Entity n
  updateEntropy :
    FieldState n → U64
  updateTopology :
    Topology n → List (Entity n) → Topology n

/-- Evolution：場の進化（UHA の状態を変異・適応させる） -/
structure Evolution (n : Nat) where
  mutate : Entity n → Entity n
  select : List (Entity n) → List (Entity n)
  adapt  : Entity n → U64 → Entity n

/-- Takeo型進化コア：環境変化時のみセレクトする -/
structure EvolutionCore (n : Nat) where
  fitness   : Entity n → FieldState n → U64
  diversity : List (Entity n)

/-- 汎用情報場エンジン（GIFE）＋ Takeo進化コア -/
structure Engine (n : Nat) where
  dynamics  : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)

/-- 場の自己計算ステップ（従来進化） -/
def stepClassic {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  let updated :=
    s.entities.map (fun e => eng.dynamics.updateEntity e s.entropy)

  let adapted :=
    updated.map (fun e => eng.evolution.adapt e s.entropy)

  let selected :=
    eng.evolution.select adapted

  let mutated :=
    selected.map eng.evolution.mutate

  let newTopology :=
    eng.dynamics.updateTopology s.topology mutated

  let newEntropy :=
    eng.dynamics.updateEntropy { entities := mutated, entropy := s.entropy, topology := newTopology }

  { entities := mutated, entropy := newEntropy, topology := newTopology }

/-
  Takeo進化：環境変化トリガー型セレクト
-/

/-- 環境の変化判定：ここでは entropy と topology のパラメータで見る -/
def envChanged {n : Nat} (prev curr : FieldState n) : Bool :=
  prev.entropy ≠ curr.entropy ∨
  prev.topology.viscosity ≠ curr.topology.viscosity ∨
  prev.topology.curvature ≠ curr.topology.curvature

/-- 多様性プールから、環境に対して最適な Entity を 1 つ選ぶ -/
def argmaxEntity {n : Nat}
  (core : EvolutionCore n)
  (env  : FieldState n) : Entity n :=
  match core.diversity with
  | []      =>
    -- 空プールの場合のフォールバック（適当にゼロ構造）
    { id := 0
    , state := ⟨fun _ => 0⟩
    , energy := 0
    , mood := 0
    , genome := 0 }
  | e :: es =>
    es.foldl
      (fun best cand =>
        if core.fitness cand env > core.fitness best env then cand else best)
      e

/-- Takeoモデル：環境が変わったときだけ多様性プールから最適 Entity を選ぶ -/
def stepTakeo {n : Nat}
  (eng  : Engine n)
  (core : EvolutionCore n)
  (prev : FieldState n)
  (curr : FieldState n) : FieldState n :=
  if envChanged prev curr then
    let best := argmaxEntity core curr
    { entities := [best]
    , entropy  := curr.entropy
    , topology := curr.topology }
  else
    -- 環境が変わらないなら進化しない（ダイナミクスも止めるならそのまま）
    prev

/-- 統合ステップ：takeoCore があれば Takeo進化、なければ従来進化 -/
def step {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  match eng.takeoCore with
  | none      => stepClassic eng s
  | some core =>
    -- ここでは「現在の環境 = 現在の FieldState」として扱う
    stepTakeo eng core s s

/-- 自動進化ストリーム -/
structure Stream (α : Type) :=
  (head : α)
  (tail : Unit → Stream α)

/-- 従来進化ストリーム -/
def evolutionClassic {n : Nat} (eng : Engine n) (s₀ : FieldState n) : Stream (FieldState n) :=
  let rec corec (s : FieldState n) : Stream (FieldState n) :=
    { head := s,
      tail := fun _ => corec (stepClassic eng s) }
  corec s₀

/-- Takeo進化ストリーム -/
def evolutionTakeo {n : Nat} (eng : Engine n) (core : EvolutionCore n) (s₀ : FieldState n) :
  Stream (FieldState n) :=
  let rec corec (prev : FieldState n) : Stream (FieldState n) :=
    let next := stepTakeo eng core prev prev
    { head := prev,
      tail := fun _ => corec next }
  corec s₀
