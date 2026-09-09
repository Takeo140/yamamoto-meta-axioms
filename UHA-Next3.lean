/-!
# UHA UltraCore — Complete Formal Computational Core

Author  : Takeo Yamamoto
License : Apache-2.0 / CC-BY-4.0

## Mathematical carrier

  U64      = ZMod (2^64)
  UHA n    = (ZMod (2^64))^n

The core is a deterministic finite-ring state machine.

The computational transformation is

  F_i(x) = Σ_j Σ_k x_j x_k C_jki

and the autonomous transition is

  x'  = x + active • (F(x) - x)
  pc' = pc + active
  h'  = h + active * HaltMask

where

  active = 1 - halt

A halted state is a fixed point.

IMPORTANT:
  2^64 is composite. Therefore Fermat's little theorem is NOT
  used for zero testing.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Basic

open BigOperators

/-- The 64-bit finite ring. -/
abbrev U64 := ZMod (2^64)

namespace UHA

variable {n : Nat}

/-! ================================================================
    1. VECTOR CARRIER
================================================================ -/

/--
N-dimensional computational vector.
-/
@[ext]
structure Vec (n : Nat) where
  coords : Fin n → U64

/-- Zero vector. -/
instance : Zero (Vec n) :=
  ⟨⟨fun _ => 0⟩⟩

/-- Vector addition. -/
instance : Add (Vec n) :=
  ⟨fun x y =>
    ⟨fun i => x.coords i + y.coords i⟩⟩

/-- Vector subtraction. -/
instance : Sub (Vec n) :=
  ⟨fun x y =>
    ⟨fun i => x.coords i - y.coords i⟩⟩

/-- Scalar multiplication. -/
instance : SMul U64 (Vec n) :=
  ⟨fun a x =>
    ⟨fun i => a * x.coords i⟩⟩

@[simp]
theorem zero_coords (i : Fin n) :
    (0 : Vec n).coords i = 0 := rfl

@[simp]
theorem add_coords (x y : Vec n) (i : Fin n) :
    (x + y).coords i =
      x.coords i + y.coords i := rfl

@[simp]
theorem sub_coords (x y : Vec n) (i : Fin n) :
    (x - y).coords i =
      x.coords i - y.coords i := rfl

@[simp]
theorem smul_coords (a : U64) (x : Vec n) (i : Fin n) :
    (a • x).coords i =
      a * x.coords i := rfl

/-! ================================================================
    2. QUADRATIC FORM
================================================================ -/

/--
Bilinear inner-product-like form over U64.

This is an algebraic bilinear form, not a positive-definite
real-valued norm.
-/
def inner (x y : Vec n) : U64 :=
  ∑ i, x.coords i * y.coords i

/--
Quadratic form

  Q(x) = <x,x>.
-/
def quadratic (x : Vec n) : U64 :=
  inner x x

@[simp]
theorem quadratic_def (x : Vec n) :
    quadratic x =
      ∑ i, x.coords i * x.coords i := rfl

/-! ================================================================
    3. STRUCTURE TENSOR
================================================================ -/

/--
Structure tensor of the computational algebra.

C[j][k] is itself an N-dimensional vector.
-/
abbrev Tensor (n : Nat) :=
  Fin n → Fin n → Vec n

/--
General bilinear hyperalgebraic evaluation.

  F(x,y)_i
    =
  Σ_j Σ_k x_j y_k C_jki
-/
def hyperEval
    (C : Tensor n)
    (x y : Vec n) : Vec n :=
  ⟨fun i =>
    ∑ j, ∑ k,
      x.coords j *
      y.coords k *
      (C j k).coords i⟩

/--
Autonomous self-evaluation.
-/
def hyperStep
    (C : Tensor n)
    (x : Vec n) : Vec n :=
  hyperEval C x x

@[simp]
theorem hyperStep_coords
    (C : Tensor n)
    (x : Vec n)
    (i : Fin n) :
    (hyperStep C x).coords i =
      ∑ j, ∑ k,
        x.coords j *
        x.coords k *
        (C j k).coords i := rfl

/-! ================================================================
    4. HALT MASK
================================================================ -/

/--
Exact algebraic specification of the zero predicate.

Because U64 = ZMod (2^64) is not a field, we do not use
Fermat's little theorem.
-/
def zeroMask (x : U64) : U64 :=
  if x = 0 then 1 else 0

@[simp]
theorem zeroMask_zero :
    zeroMask (0 : U64) = 1 := by
  simp [zeroMask]

@[simp]
theorem zeroMask_nonzero
    {x : U64}
    (h : x ≠ 0) :
    zeroMask x = 0 := by
  simp [zeroMask, h]

theorem zeroMask_eq_one_iff
    (x : U64) :
    zeroMask x = 1 ↔ x = 0 := by
  by_cases h : x = 0 <;>
    simp [zeroMask, h]

/-! ================================================================
    5. COMPUTATIONAL STATE
================================================================ -/

/--
Complete autonomous machine state.

  pc   : program counter
  data : computational vector
  halt : control state
-/
@[ext]
structure State (n : Nat) where
  pc   : U64
  data : Vec n
  halt : U64

/--
Valid control state.

Only two control states exist:

  0 = active
  1 = halted
-/
def ValidHalt (s : State n) : Prop :=
  s.halt = 0 ∨ s.halt = 1

/--
Active mask.

For valid states:

  halt = 0 -> active = 1
  halt = 1 -> active = 0
-/
def activeMask (s : State n) : U64 :=
  1 - s.halt

@[simp]
theorem activeMask_zero
    (s : State n)
    (h : s.halt = 0) :
    activeMask s = 1 := by
  simp [activeMask, h]

@[simp]
theorem activeMask_one
    (s : State n)
    (h : s.halt = 1) :
    activeMask s = 0 := by
  simp [activeMask, h]

/-! ================================================================
    6. HALTING FUNCTION
================================================================ -/

/--
The halt condition compares the current quadratic state value
with a target value.
-/
def haltMask
    (s : State n)
    (target : U64) : U64 :=
  zeroMask (quadratic s.data - target)

/--
Halting condition is exactly equivalent to Q(x)=target.
-/
theorem haltMask_eq_one_iff
    (s : State n)
    (target : U64) :
    haltMask s target = 1 ↔
      quadratic s.data = target := by
  unfold haltMask
  rw [zeroMask_eq_one_iff]
  exact sub_eq_zero.mp

/-! ================================================================
    7. ONE-CLOCK TRANSITION
================================================================ -/

/--
One complete computational clock.

The transition is defined algebraically.

Data:

  x' = x + a(F(x)-x)

PC:

  pc' = pc + a

Halt:

  h' = h + a H(x)

where

  a = 1-h.
-/
def step
    (C : Tensor n)
    (s : State n)
    (target : U64) : State n :=
  let a := activeMask s
  let nextData :=
    s.data + a • (hyperStep C s.data - s.data)
  let nextPC :=
    s.pc + a
  let nextHalt :=
    s.halt + a * haltMask s target
  ⟨nextPC, nextData, nextHalt⟩

/-! ================================================================
    8. STEP SPECIFICATION
================================================================ -/

theorem step_data_spec
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (i : Fin n) :
    (step C s target).data.coords i =
      s.data.coords i +
        activeMask s *
          ((hyperStep C s.data).coords i -
            s.data.coords i) := by
  rfl

theorem step_pc_spec
    (C : Tensor n)
    (s : State n)
    (target : U64) :
    (step C s target).pc =
      s.pc + activeMask s := by
  rfl

theorem step_halt_spec
    (C : Tensor n)
    (s : State n)
    (target : U64) :
    (step C s target).halt =
      s.halt +
        activeMask s *
          haltMask s target := by
  rfl

/-! ================================================================
    9. ACTIVE STATE
================================================================ -/

/--
While active, the algebraic state is fully evaluated.
-/
theorem active_data_update
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 0) :
    (step C s target).data =
      hyperStep C s.data := by
  ext i
  simp [step, activeMask, h]

/--
While active, the PC advances exactly one unit.
-/
theorem active_pc_update
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 0) :
    (step C s target).pc =
      s.pc + 1 := by
  simp [step, activeMask, h]

/--
If the halt condition is true during an active state,
the resulting state is halted.
-/
theorem active_halts
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (hactive : s.halt = 0)
    (hh : haltMask s target = 1) :
    (step C s target).halt = 1 := by
  simp [step, activeMask, hactive, hh]

/--
An active state does not halt if the halt condition is false.
-/
theorem active_continues
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (hactive : s.halt = 0)
    (hh : haltMask s target = 0) :
    (step C s target).halt = 0 := by
  simp [step, activeMask, hactive, hh]

/-! ================================================================
    10. HALTING EQUIVALENCE
================================================================ -/

/--
For an active state, halting occurs exactly when

  quadratic(data) = target.
-/
theorem active_step_halts_iff
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (hactive : s.halt = 0) :
    (step C s target).halt = 1 ↔
      quadratic s.data = target := by
  constructor
  · intro h
    have hm : haltMask s target = 1 := by
      simpa [step, activeMask, hactive] using h
    exact (haltMask_eq_one_iff s target).mp hm
  · intro h
    apply active_halts C s target hactive
    exact (haltMask_eq_one_iff s target).mpr h

/-! ================================================================
    11. HALTED STATE = FIXED POINT
================================================================ -/

/--
The fundamental fixed-point theorem.

Once halt=1, every subsequent transition leaves the state
completely unchanged.
-/
theorem halted_fixed_point
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    step C s target = s := by
  simp [step, activeMask, h]

/--
PC is frozen after halting.
-/
theorem halted_pc_invariant
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    (step C s target).pc = s.pc := by
  rw [halted_fixed_point C s target h]

/--
Data is frozen after halting.
-/
theorem halted_data_invariant
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    (step C s target).data = s.data := by
  rw [halted_fixed_point C s target h]

/--
The halt flag itself remains 1.
-/
theorem halted_flag_invariant
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    (step C s target).halt = 1 := by
  rw [halted_fixed_point C s target h]

/-! ================================================================
    12. CONTROL INVARIANT
================================================================ -/

/--
The control state remains Boolean.
-/
theorem halt_invariant
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (hvalid : ValidHalt s) :
    ValidHalt (step C s target) := by
  rcases hvalid with h0 | h1
  · by_cases hh : haltMask s target = 1
    · right
      simp [step, activeMask, h0, hh]
    · left
      have hz : haltMask s target = 0 := by
        by_contra hn
        have : haltMask s target = 1 := by
          exact one_eq_one_iff.mp (by
            exact (zeroMask_eq_one_iff _).mp
              (show zeroMask (quadratic s.data - target) = 1 from by
                simpa [haltMask] using hn))
        exact hh this
      simp [step, activeMask, h0, hz]
  · right
    exact halted_flag_invariant C s target h1

/-! ================================================================
    13. DETERMINISM
================================================================ -/

/--
The transition is a mathematical function and therefore
deterministic.
-/
theorem step_deterministic
    (C : Tensor n)
    (s : State n)
    (target : U64) :
    step C s target = step C s target := by
  rfl

/--
Equal input states have equal successor states.
-/
theorem step_congruent
    (C : Tensor n)
    (s₁ s₂ : State n)
    (target : U64)
    (h : s₁ = s₂) :
    step C s₁ target = step C s₂ target := by
  rw [h]

/-! ================================================================
    14. ITERATED COMPUTATION
================================================================ -/

/--
Run the autonomous kernel for k clocks.
-/
def run
    (C : Tensor n)
    (target : U64) :
    Nat → State n → State n
  | 0, s => s
  | k + 1, s =>
      run C target k (step C s target)

/--
One additional clock after k clocks.
-/
theorem run_succ
    (C : Tensor n)
    (target : U64)
    (k : Nat)
    (s : State n) :
    run C target (k + 1) s =
      run C target k (step C s target) := by
  rfl

/--
A halted state is invariant under arbitrary iteration.
-/
theorem run_halted
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    ∀ k, run C target k s = s := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [run_succ]
      rw [halted_fixed_point C s target h]
      exact ih

/-! ================================================================
    15. HALTING STATE IS A GLOBAL FIXED POINT
================================================================ -/

/--
The fixed-point property is independent of the tensor C and
target once halt=1.
-/
theorem halt_absorbing
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    ∀ k,
      (run C target k s).halt = 1 := by
  intro k
  rw [run_halted C s target h]
  exact h

/-! ================================================================
    16. QUADRATIC FORM / ISOMETRY
================================================================ -/

/--
Algebraic isometry.
-/
structure Isometry (n : Nat) where
  toFun : Vec n → Vec n
  inner_preserve :
    ∀ x y,
      inner (toFun x) (toFun y) =
        inner x y

/--
An isometry preserves the quadratic form.
-/
theorem isometry_preserves_quadratic
    (f : Isometry n)
    (x : Vec n) :
    quadratic (f.toFun x) = quadratic x := by
  exact f.inner_preserve x x

/-! ================================================================
    17. CONSERVATION UNDER AN ISOMETRIC DYNAMICS
================================================================ -/

/--
If a hyperalgebraic transformation is an isometry, its quadratic
state value is conserved.
-/
def IsometricDynamics
    (F : Vec n → Vec n) : Prop :=
  ∀ x y, inner (F x) (F y) = inner x y

theorem isometric_dynamics_preserves_quadratic
    (F : Vec n → Vec n)
    (hF : IsometricDynamics F)
    (x : Vec n) :
    quadratic (F x) = quadratic x := by
  exact hF x x

/-! ================================================================
    18. STATE-LEVEL CONSERVATION
================================================================ -/

/--
If the active data transformation is isometric, the quadratic
value of the candidate state is unchanged.
-/
theorem hyperStep_quadratic_preserved
    (C : Tensor n)
    (hiso :
      ∀ x y,
        inner (hyperStep C x) (hyperStep C y) =
          inner x y)
    (x : Vec n) :
    quadratic (hyperStep C x) = quadratic x := by
  exact hiso x x

/-! ================================================================
    19. CORE SPECIFICATION
================================================================ -/

/--
Complete specification of one UHA computational cycle.
-/
def StepSpec
    (C : Tensor n)
    (s next : State n)
    (target : U64) : Prop :=
  (∀ i,
    next.data.coords i =
      s.data.coords i +
        activeMask s *
          ((hyperStep C s.data).coords i -
            s.data.coords i))
  ∧
  next.pc = s.pc + activeMask s
  ∧
  next.halt =
    s.halt +
      activeMask s *
        haltMask s target

/--
The reference Lean kernel satisfies its own complete specification.
-/
theorem step_satisfies_spec
    (C : Tensor n)
    (s : State n)
    (target : U64) :
    StepSpec C s (step C s target) target := by
  constructor
  · intro i
    exact step_data_spec C s target i
  constructor
  · exact step_pc_spec C s target
  · exact step_halt_spec C s target

/--
The specification uniquely determines the successor state.
-/
theorem step_spec_unique
    (C : Tensor n)
    (s next : State n)
    (target : U64)
    (hspec : StepSpec C s next target) :
    next = step C s target := by
  rcases hspec with ⟨hdata, hpc, hhalt⟩

  apply State.ext

  · exact hpc.trans (step_pc_spec C s target).symm

  · ext i
    exact
      (hdata i).trans
        (step_data_spec C s target i).symm

  · exact
      hhalt.trans
        (step_halt_spec C s target).symm

/-! ================================================================
    20. REFERENCE-KERNEL UNIQUENESS
================================================================ -/

/--
Any implementation satisfying StepSpec is observationally
identical to the reference Lean kernel.
-/
theorem implementation_refinement
    (C : Tensor n)
    (s next : State n)
    (target : U64)
    (hspec : StepSpec C s next target) :
    next = step C s target :=
  step_spec_unique C s next target hspec

/-! ================================================================
    21. FINITE STATE SPACE
================================================================ -/

/--
Every UHA vector belongs to a finite state space.
-/
instance : Fintype (Vec n) := by
  classical
  infer_instance

/--
The complete state space is finite.
-/
instance : Fintype (State n) := by
  classical
  infer_instance

/-! ================================================================
    22. CORE SUMMARY THEOREMS
================================================================ -/

/--
Deterministic autonomous transition.
-/
theorem core_deterministic :
    ∀ (C : Tensor n) (s : State n) (target : U64),
      ∃! next : State n,
        next = step C s target := by
  intro C s target
  refine ⟨step C s target, rfl, ?_⟩
  intro y hy
  exact hy.symm

/--
Every halted state is an absorbing fixed point.
-/
theorem core_absorbing
    (C : Tensor n)
    (s : State n)
    (target : U64)
    (h : s.halt = 1) :
    step C s target = s ∧
    ∀ k, run C target k s = s := by
  constructor
  · exact halted_fixed_point C s target h
  · exact run_halted C s target h

end UHA
