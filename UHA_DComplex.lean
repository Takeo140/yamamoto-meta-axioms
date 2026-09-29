/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto
  UHA-DComplex-64 Foundational Computational Core
  Discrete Complex Algebra — Exact Complex Kernel
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic

namespace UHA.DComplex

abbrev U64 := ZMod (2 ^ 64)

/-- 離散複素数 a + b·i, exact mod 2^64 -/
structure DU64 where
  re : U64
  im : U64
deriving DecidableEq, Repr, Inhabited

instance : Zero DU64 where zero := ⟨0, 0⟩
instance : One DU64 where one := ⟨1, 0⟩
instance : Add DU64 where add x y := ⟨x.re + y.re, x.im + y.im⟩
instance : Sub DU64 where sub x y := ⟨x.re - y.re, x.im - y.im⟩
instance : Neg DU64 where neg x := ⟨-x.re, -x.im⟩

def mulC (x y : DU64) : DU64 :=
  ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
instance : Mul DU64 where mul := mulC

def conjC (x : DU64) : DU64 := ⟨x.re, -x.im⟩
def normSq (x : DU64) : U64 := x.re * x.re + x.im * x.im

abbrev State (n : Nat) := Fin n → DU64
abbrev Coeff (n : Nat) := Fin n → Fin n → Fin n → DU64

def add {n} (x y : State n) : State n := fun i => x i + y i
def sub {n} (x y : State n) : State n := fun i => x i - y i
def smul {n} (a : DU64) (x : State n) : State n := fun i => mulC a (x i)

def mul {n} (C : Coeff n) (x y : State n) : State n :=
  fun i => Finset.sum Finset.univ fun j =>
    Finset.sum Finset.univ fun k =>
      mulC (mulC (x j) (y k)) (C j k i)

def F {n} (C : Coeff n) (x : State n) : State n := mul C x x
def step {n} (C : Coeff n) (x : State n) (a : DU64) : State n :=
  add x (smul a (sub (F C x) x))

inductive Control | run | halt deriving DecidableEq, Repr
def activity : Control → DU64 | .run => 1 | .halt => 0

abbrev PC := U64
def pcStep (pc : PC) : Control → PC | .run => pc + 1 | .halt => pc

structure CoreState (n : Nat) where pc : PC; state : State n; control : Control

def tick {n} (C : Coeff n) (s : CoreState n) : CoreState n :=
  { pc := pcStep s.pc s.control, state := step C s.state (activity s.control), control := s.control }

def run {n} (C : Coeff n) (k : Nat) (s : CoreState n) : CoreState n :=
  match k with | 0 => s | k+1 => run C k (tick C s)

-- 定理: HALTは完全凍結、RUNはFを実行
theorem step_zero {n} (C : Coeff n) (x : State n) : step C x 0 = x := by
  funext i; simp [step, add, sub, smul, mulC, zero]; cases (x i) with | mk re im => rfl
theorem step_one {n} (C : Coeff n) (x : State n) : step C x 1 = F C x := by
  funext i; simp [step, add, sub, smul, mulC]; 
  cases (F C x i) with | mk re1 im1 => cases (x i) with | mk re2 im2 =>
    simp [add_sub_cancel]

theorem tick_halt_fixed {n} (C : Coeff n) (pc : PC) (x : State n) :
  tick C ⟨pc, x, .halt⟩ = ⟨pc, x, .halt⟩ := by simp [tick, pcStep, step_zero]
theorem tick_run {n} (C : Coeff n) (pc : PC) (x : State n) :
  tick C ⟨pc, x, .run⟩ = ⟨pc + 1, F C x, .run⟩ := by simp [tick, pcStep, step_one]

def IsFixedPoint {n} (C : Coeff n) (x : State n) : Prop := F C x = x
def IsNormPreserving {n} (C : Coeff n) : Prop :=
  ∀ x, (Finset.sum Finset.univ fun i => normSq (F C x i)) = (Finset.sum Finset.univ fun i => normSq (x i))
def IsReversible (n) (C : Coeff n) : Prop := ∀ j k i, C j k i = conjC (C k j i)

structure Core (n : Nat) where coeff : Coeff n
def Core.init {n} (c : Core n) (pc : PC) (x : State n) : CoreState n := ⟨pc, x, .run⟩
def Core.tick {n} (c : Core n) (s : CoreState n) := tick c.coeff s
def Core.run {n} (c : Core n) (k : Nat) (s : CoreState n) := run c.coeff k s

end UHA.DComplex
