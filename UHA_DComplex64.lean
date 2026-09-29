/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto
  UHA-DComplex-64 Foundational Computational Core
  Discrete Complex Algebra — Exact Complex Kernel
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Basic

namespace UHA.DComplex

/-- 64-bit 符号なし整数環 (2^64 を法とする加群・環) -/
abbrev U64 := ZMod (2 ^ 64)

/-- 離散複素数 a + b·i, exact mod 2^64 -/
structure DU64 where
  re : U64
  im : U64
deriving DecidableEq, Repr, Inhabited

namespace DU64

extensionality

def add (x y : DU64) : DU64 := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : DU64) : DU64 := ⟨-x.re, -x.im⟩
def mul (x y : DU64) : DU64 := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def zero : DU64 := ⟨0, 0⟩
def one : DU64 := ⟨1, 0⟩

instance : Zero DU64 := ⟨zero⟩
instance : One DU64 := ⟨one⟩
instance : Add DU64 := ⟨add⟩
instance : Neg DU64 := ⟨neg⟩
instance : Sub DU64 := ⟨fun x y => add x (neg y)⟩
instance : Mul DU64 := ⟨mul⟩

/-- DU64 が可換環 (CommRing) の構造を持つことの証明 -/
instance : CommRing DU64 where
  add := (· + ·)
  add_assoc := fun a b c => by ext <;> simp [add_assoc]
  zero := 0
  zero_add := fun a => by ext <;> simp
  add_zero := fun a => by ext <;> simp
  add_comm := fun a b => by ext <;> simp [add_comm]
  mul := (· * ·)
  mul_assoc := fun a b c => by ext <;> simp [mul]; ring
  one := 1
  one_mul := fun a => by ext <;> simp [mul]
  mul_one := fun a => by ext <;> simp [mul]
  left_distrib := fun a b c => by ext <;> simp [mul, add]; ring
  right_distrib := fun a b c => by ext <;> simp [mul, add]; ring
  mul_comm := fun a b => by ext <;> simp [mul]; ring
  zero_mul := fun a => by ext <;> simp [mul]
  mul_zero := fun a => by ext <;> simp [mul]
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg := fun a b => rfl
  zmod_custom := by intro n; ext <;> rfl
  add_left_neg := fun a => by ext <;> simp

def conj (x : DU64) : DU64 := ⟨x.re, -x.im⟩
def normSq (x : DU64) : U64 := x.re * x.re + x.im * x.im

theorem normSq_eq_mul_conj (x : DU64) : (x * conj x).re = normSq x ∧ (x * conj x).im = 0 := by
  constructor
  · simp [mul, conj, normSq]; ring
  · simp [mul, conj]; ring

end DU64

-- State & Tensor definitions
abbrev State (n : Nat) := Fin n → DU64
abbrev Coeff (n : Nat) := Fin n → Fin n → Fin n → DU64

def add {n} (x y : State n) : State n := fun i => x i + y i
def sub {n} (x y : State n) : State n := fun i => x i - y i
def smul {n} (a : DU64) (x : State n) : State n := fun i => a * (x i)

def mul {n} (C : Coeff n) (x y : State n) : State n :=
  fun i => Finset.sum Finset.univ fun j =>
    Finset.sum Finset.univ fun k =>
      (x j * y k) * C j k i

def F {n} (C : Coeff n) (x : State n) : State n := mul C x x

def step {n} (C : Coeff n) (x : State n) (a : DU64) : State n :=
  add x (smul a (sub (F C x) x))

-- Control Architecture
inductive Control | run | halt deriving DecidableEq, Repr

def activity : Control → DU64
  | .run  => 1
  | .halt => 0

abbrev PC := U64

def pcStep (pc : PC) : Control → PC
  | .run  => pc + 1
  | .halt => pc

structure CoreState (n : Nat) where
  pc      : PC
  state   : State n
  control : Control

def tick {n} (C : Coeff n) (s : CoreState n) : CoreState n :=
  { pc      := pcStep s.pc s.control
  , state   := step C s.state (activity s.control)
  , control := s.control }

def run {n} (C : Coeff n) (k : Nat) (s : CoreState n) : CoreState n :=
  match k with
  | 0     => s
  | k + 1 => run C k (tick C s)

-- ==========================================
-- Theorems: Core Dynamics Verification
-- ==========================================

theorem step_zero {n} (C : Coeff n) (x : State n) : step C x 0 = x := by
  ext i
  simp [step, add, smul, activity]

theorem step_one {n} (C : Coeff n) (x : State n) : step C x 1 = F C x := by
  ext i
  simp [step, add, sub, smul, activity]

theorem tick_halt_fixed {n} (C : Coeff n) (pc : PC) (x : State n) :
    tick C ⟨pc, x, .halt⟩ = ⟨pc, x, .halt⟩ := by
  simp [tick, pcStep, activity, step_zero]

theorem tick_run {n} (C : Coeff n) (pc : PC) (x : State n) :
    tick C ⟨pc, x, .run⟩ = ⟨pc + 1, F C x, .run⟩ := by
  simp [tick, pcStep, activity, step_one]

-- System Properties & Analysis Criteria
def IsFixedPoint {n} (C : Coeff n) (x : State n) : Prop :=
  F C x = x

def IsNormPreserving {n} (C : Coeff n) : Prop :=
  ∀ x, (Finset.sum Finset.univ fun i => DU64.normSq (F C x i)) =
       (Finset.sum Finset.univ fun i => DU64.normSq (x i))

def IsHermitian (n) (C : Coeff n) : Prop :=
  ∀ j k i, C j k i = DU64.conj (C k j i)

structure Core (n : Nat) where
  coeff : Coeff n

def Core.init {n} (c : Core n) (pc : PC) (x : State n) : CoreState n :=
  ⟨pc, x, .run⟩

def Core.tick {n} (c : Core n) (s : CoreState n) : CoreState n :=
  tick c.coeff s

def Core.run {n} (c : Core n) (k : Nat) (s : CoreState n) : CoreState n :=
  run c.coeff k s

end UHA.DComplex
