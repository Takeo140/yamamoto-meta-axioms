/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto
  UHA-DComplex-64 Foundational Computational Core
  Discrete Complex Algebra — Exact Complex Kernel
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace UHA.DComplex

/-- 64-bit 符号なし整数環 (2^64 を法とする剰余環) -/
abbrev U64 := ZMod (2 ^ 64)

/-- 離散複素数 a + b·i, exact mod 2^64 -/
@[ext]
structure DU64 where
  re : U64
  im : U64
deriving DecidableEq, Repr, Inhabited

namespace DU64

instance : Zero DU64 := ⟨⟨0, 0⟩⟩
instance : One DU64 := ⟨⟨1, 0⟩⟩
instance : Add DU64 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg DU64 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul DU64 :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

@[simp] theorem zero_re : (0 : DU64).re = 0 := rfl
@[simp] theorem zero_im : (0 : DU64).im = 0 := rfl
@[simp] theorem one_re : (1 : DU64).re = 1 := rfl
@[simp] theorem one_im : (1 : DU64).im = 0 := rfl
@[simp] theorem add_re (x y : DU64) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : DU64) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : DU64) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : DU64) : (-x).im = -x.im := rfl
@[simp] theorem mul_re (x y : DU64) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : DU64) : (x * y).im = x.re * y.im + x.im * y.re := rfl

/-- DU64 が可換環 (CommRing) の構造を持つことの証明 -/
instance : CommRing DU64 where
  add := (· + ·)
  add_assoc := by intro a b c; ext <;> simp <;> ring
  zero := 0
  zero_add := by intro a; ext <;> simp
  add_zero := by intro a; ext <;> simp
  add_comm := by intro a b; ext <;> simp <;> ring
  neg := Neg.neg
  neg_add_cancel := by intro a; ext <;> simp
  mul := (· * ·)
  left_distrib := by intro a b c; ext <;> simp <;> ring
  right_distrib := by intro a b c; ext <;> simp <;> ring
  zero_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp
  mul_assoc := by intro a b c; ext <;> simp <;> ring
  one := 1
  one_mul := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp
  mul_comm := by intro a b; ext <;> simp <;> ring

def conj (x : DU64) : DU64 := ⟨x.re, -x.im⟩
def normSq (x : DU64) : U64 := x.re * x.re + x.im * x.im

theorem normSq_eq_mul_conj (x : DU64) :
    (x * conj x).re = normSq x ∧ (x * conj x).im = 0 := by
  constructor
  · simp only [mul_re, conj, normSq]; ring
  · simp only [mul_im, conj]; ring

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
  funext i
  simp [step, add, smul]

theorem step_one {n} (C : Coeff n) (x : State n) : step C x 1 = F C x := by
  funext i
  simp only [step, add, sub, smul, one_mul]
  ring

theorem tick_halt_fixed {n} (C : Coeff n) (pc : PC) (x : State n) :
    tick C ⟨pc, x, .halt⟩ = ⟨pc, x, .halt⟩ := by
  simp [tick, pcStep, activity, step_zero]

theorem tick_run {n} (C : Coeff n) (pc : PC) (x : State n) :
    tick C ⟨pc, x, .run⟩ = ⟨pc + 1, F C x, .run⟩ := by
  simp [tick, pcStep, activity, step_one]

-- System Properties & Analysis Criteria
def IsFixedPoint {n} (C : Coeff n) (x : State n) : Prop :=
  F C x = x

/-- 注意: normSq は mod 2^64 の値であり、通常のノルムのような順序・正値性は持たない -/
def IsNormPreserving {n} (C : Coeff n) : Prop :=
  ∀ x, (Finset.sum Finset.univ fun i => DU64.normSq (F C x i)) =
       (Finset.sum Finset.univ fun i => DU64.normSq (x i))

def IsHermitian (n) (C : Coeff n) : Prop :=
  ∀ j k i, C j k i = DU64.conj (C k j i)

structure Core (n : Nat) where
  coeff : Coeff n

def Core.init {n} (_c : Core n) (pc : PC) (x : State n) : CoreState n :=
  ⟨pc, x, .run⟩

-- 注意: `Core.tick` の本体で `tick` と書くと自分自身を指してしまうため、完全修飾名を使う
def Core.tick {n} (c : Core n) (s : CoreState n) : CoreState n :=
  UHA.DComplex.tick c.coeff s

def Core.run {n} (c : Core n) (k : Nat) (s : CoreState n) : CoreState n :=
  UHA.DComplex.run c.coeff k s

end UHA.DComplex

