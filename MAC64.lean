/-
  MAC64 - Meta-Axiom Computation (64bit Edition, Lean version)
  (c) Takeo Yamamoto
  Apache 2.0 License
-/

import Std.Data.UInt

open Std

/-- 64bit Program: UInt64 → UInt64 -/
structure MAC64 where
  run : UInt64 → UInt64

/-- 64bit CostDensity: (UInt64, UInt64) → ℝ -/
def Cost64 :=
  UInt64 → UInt64 → ℝ

/-- 離散作用：Σ L(x, f(x)) -/
def action64 (L : Cost64) (p : MAC64) (xs : List UInt64) : ℝ :=
  xs.foldl (fun acc x => acc + L x (p.run x)) 0

/-- 仕様：UInt64 × UInt64 → Prop -/
def Spec64 :=
  UInt64 → UInt64 → Prop

/-- 整合性：∀x, φ(x, f(x)) -/
def consistent64 (φ : Spec64) (p : MAC64) (xs : List UInt64) : Prop :=
  ∀ x ∈ xs, φ x (p.run x)

/-- 多層状態：インデックスごとの 64bit 状態 -/
structure LayeredState64 (ι : Type) where
  indices : List ι
  states  : List UInt64

/-- レイヤーごとの部分プログラム -/
structure LayerProgram64 (ι : Type) where
  runLayer : ι → UInt64 → UInt64

/-- 全体プログラムへの束ね -/
def LayerProgram64.toProgram
  {ι : Type} (P : LayerProgram64 ι) :
  LayeredState64 ι → LayeredState64 ι :=
  fun s =>
    { indices := s.indices
    , states  :=
        (s.indices.zip s.states).map
          (fun (i, x) => P.runLayer i x)
    }

/-- DualState：物理 → 数学（どちらも 64bit） -/
structure Dual64 where
  toMath : UInt64 → UInt64

/-- 双対的一致条件 -/
def dualConsistent64
  (Φ Ψ : Dual64)
  (p_phys p_math : MAC64)
  (xs : List UInt64) : Prop :=
  ∀ x ∈ xs,
    Ψ.toMath (p_phys.run x) =
    p_math.run (Φ.toMath x)

/-- 極値原理：作用を最小化する 64bit プログラム -/
def optimalProgram64
  (L : Cost64)
  (xs : List UInt64)
  (candidates : List MAC64) : Option MAC64 :=
  candidates.foldl
    (fun best p =>
      match best with
      | none      => some p
      | some p₀   =>
        if action64 L p xs < action64 L p₀ xs
        then some p
        else best)
    none
