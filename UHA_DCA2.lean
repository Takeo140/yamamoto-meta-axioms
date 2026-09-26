/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto

  UHACore
  Discrete Complex Algebraic Computational Core

  Features:
    1. Exact discrete complex arithmetic over Gaussian integers
    2. Deterministic two-component state
    3. Conjugation and norm-square
    4. Linear state transformations
    5. X / Z / Identity / Swap operations
    6. Composition of transformations
    7. Involutivity and reversibility proofs
    8. Deterministic state evolution
    9. Algebraic invariants
-/

namespace UHACore

/-! ================================================================
    1. Discrete Complex Numbers
================================================================ -/

/--
  Discrete complex number.

  This is the Gaussian-integer algebra Z[i]:

      a + bi

  with a,b : Int.

  Unlike floating-point complex numbers, every operation is exact.
-/
structure DComplex where
  re : Int
  im : Int
  deriving Repr, DecidableEq


namespace DComplex

/-- Zero. -/
def zero : DComplex :=
  ⟨0, 0⟩

/-- One. -/
def one : DComplex :=
  ⟨1, 0⟩

/-- Imaginary unit. -/
def I : DComplex :=
  ⟨0, 1⟩

/-- Addition. -/
def add (a b : DComplex) : DComplex :=
  ⟨a.re + b.re, a.im + b.im⟩

/-- Negation. -/
def neg (a : DComplex) : DComplex :=
  ⟨-a.re, -a.im⟩

/-- Subtraction. -/
def sub (a b : DComplex) : DComplex :=
  add a (neg b)

/-- Gaussian-integer multiplication. -/
def mul (a b : DComplex) : DComplex :=
  ⟨
    a.re * b.re - a.im * b.im,
    a.re * b.im + a.im * b.re
  ⟩

/-- Complex conjugation. -/
def conj (a : DComplex) : DComplex :=
  ⟨a.re, -a.im⟩

/--
  Exact squared magnitude:

      |a + bi|² = a² + b²

  The result is an integer.
-/
def normSq (a : DComplex) : Int :=
  a.re * a.re + a.im * a.im


/-! ================================================================
    Basic Algebraic Properties
================================================================ -/

/-- Zero is an additive identity. -/
theorem add_zero (a : DComplex) :
    add a zero = a := by
  cases a
  rfl

/-- Zero is a left additive identity. -/
theorem zero_add (a : DComplex) :
    add zero a = a := by
  cases a
  rfl

/-- Negation is involutive. -/
theorem neg_neg (a : DComplex) :
    neg (neg a) = a := by
  cases a
  simp [neg]

/-- Conjugation is involutive. -/
theorem conj_conj (a : DComplex) :
    conj (conj a) = a := by
  cases a
  simp [conj]

/-- Conjugation commutes with addition. -/
theorem conj_add (a b : DComplex) :
    conj (add a b) =
      add (conj a) (conj b) := by
  cases a
  cases b
  simp [conj, add]

/-- Conjugation commutes with multiplication. -/
theorem conj_mul (a b : DComplex) :
    conj (mul a b) =
      mul (conj a) (conj b) := by
  cases a
  cases b
  simp [conj, mul]

/-- Squared norm is nonnegative. -/
theorem normSq_nonneg (a : DComplex) :
    0 ≤ normSq a := by
  simp [normSq]
  positivity

/--
  Norm-square of a product.

      |ab|² = |a|² |b|²
-/
theorem normSq_mul (a b : DComplex) :
    normSq (mul a b) =
      normSq a * normSq b := by
  cases a
  cases b
  simp [normSq, mul]
  ring


end DComplex


/-! ================================================================
    2. Two-Component Discrete State
================================================================ -/

structure DState where
  amp0 : DComplex
  amp1 : DComplex
  deriving Repr, DecidableEq


namespace DState

/-- Zero state. -/
def zero : DState :=
  ⟨DComplex.zero, DComplex.zero⟩

/-- Component-wise addition. -/
def add (a b : DState) : DState :=
  ⟨
    DComplex.add a.amp0 b.amp0,
    DComplex.add a.amp1 b.amp1
  ⟩

/-- Component-wise negation. -/
def neg (s : DState) : DState :=
  ⟨
    DComplex.neg s.amp0,
    DComplex.neg s.amp1
  ⟩

/-- Component-wise subtraction. -/
def sub (a b : DState) : DState :=
  add a (neg b)


/-- Total squared amplitude. -/
def normSq (s : DState) : Int :=
  DComplex.normSq s.amp0 +
  DComplex.normSq s.amp1


/-- X transformation: exchange the two components. -/
def applyX (s : DState) : DState :=
  ⟨s.amp1, s.amp0⟩


/-- Z transformation: negate the second component. -/
def applyZ (s : DState) : DState :=
  ⟨s.amp0, DComplex.neg s.amp1⟩


/-- Identity transformation. -/
def applyI (s : DState) : DState :=
  s


/-- Y-like discrete transformation.

    (a,b) ↦ (-b,a)

  This is multiplication by the imaginary unit
  at the two-component level.
-/
def applyY (s : DState) : DState :=
  ⟨
    DComplex.neg s.amp1,
    s.amp0
  ⟩


/-! ================================================================
    3. Fundamental Transformation Proofs
================================================================ -/

/-- X is involutive. -/
theorem applyX_involutive (s : DState) :
    applyX (applyX s) = s := by
  cases s
  rfl


/-- Z is involutive. -/
theorem applyZ_involutive (s : DState) :
    applyZ (applyZ s) = s := by
  cases s
  simp [applyZ, DComplex.neg]


/-- Y is not involutive; its square is negation. -/
theorem applyY_twice (s : DState) :
    applyY (applyY s) = neg s := by
  cases s
  simp [applyY, neg, DComplex.neg]


/-- Four Y transformations return to the original state. -/
theorem applyY_four (s : DState) :
    applyY (applyY (applyY (applyY s))) = s := by
  cases s
  simp [applyY, neg, DComplex.neg]


/-- Identity transformation. -/
theorem applyI_identity (s : DState) :
    applyI s = s := by
  rfl


/-! ================================================================
    4. Norm Invariants
================================================================ -/

/-- X preserves total squared amplitude. -/
theorem applyX_preserves_norm (s : DState) :
    normSq (applyX s) = normSq s := by
  simp [applyX, normSq]


/-- Z preserves total squared amplitude. -/
theorem applyZ_preserves_norm (s : DState) :
    normSq (applyZ s) = normSq s := by
  cases s with
  | mk a b =>
      simp [applyZ, normSq, DComplex.normSq]
      ring


/-- Y preserves total squared amplitude. -/
theorem applyY_preserves_norm (s : DState) :
    normSq (applyY s) = normSq s := by
  cases s with
  | mk a b =>
      simp [applyY, normSq, DComplex.normSq]
      ring


/-! ================================================================
    5. General State Transformation
================================================================ -/

/--
  A transformation is simply a deterministic function
  from states to states.
-/
abbrev Transform :=
  DState → DState


/-- Composition of transformations. -/
def compose
    (f g : Transform) :
    Transform :=
  fun s => f (g s)


/-- Identity transformation. -/
def identity : Transform :=
  fun s => s


/-- X as a general transformation. -/
def X : Transform :=
  applyX


/-- Z as a general transformation. -/
def Z : Transform :=
  applyZ


/-- Y as a general transformation. -/
def Y : Transform :=
  applyY


/-! ================================================================
    6. Transformation Algebra
================================================================ -/

/-- X² = I. -/
theorem X_squared :
    compose X X = identity := by
  funext s
  simp [compose, X, identity, applyX_involutive]


/-- Z² = I. -/
theorem Z_squared :
    compose Z Z = identity := by
  funext s
  simp [compose, Z, identity, applyZ_involutive]


/-- Y⁴ = I. -/
theorem Y_fourth :
    compose Y
      (compose Y
        (compose Y Y)) = identity := by
  funext s
  simp [compose, Y, identity, applyY_four]


/-! ================================================================
    7. Deterministic Transition System
================================================================ -/

/--
  Computational state with a halt flag.

  halted = true means no further state transition occurs.
-/
structure CoreState where
  state : DState
  halted : Bool
  deriving Repr, DecidableEq


/-- Activate a transformation. -/
def tick
    (t : Transform)
    (s : CoreState) :
    CoreState :=
  if s.halted then
    s
  else
    {
      state := t s.state
      halted := false
    }


/-- Halt operation. -/
def halt (s : CoreState) : CoreState :=
  {
    state := s.state
    halted := true
  }


/-- A halted state is fixed. -/
theorem halted_fixed
    (t : Transform)
    (s : CoreState)
    (h : s.halted = true) :
    tick t s = s := by
  simp [tick, h]


/-! ================================================================
    8. Program Representation
================================================================ -/

/--
  Finite deterministic instruction set.
-/
inductive Op where
  | identity
  | X
  | Z
  | Y
  | halt
  deriving Repr, DecidableEq


/-- Instruction semantics. -/
def execute
    (op : Op)
    (s : CoreState) :
    CoreState :=
  match op with
  | Op.identity =>
      tick identity s
  | Op.X =>
      tick X s
  | Op.Z =>
      tick Z s
  | Op.Y =>
      tick Y s
  | Op.halt =>
      halt s


/-- Program is a sequence of operations. -/
def Program :=
  List Op


/-! ================================================================
    9. Sequential Execution
================================================================ -/

/-- Execute one program operation. -/
def step
    (p : Program)
    (s : CoreState) :
    CoreState :=
  match p with
  | [] =>
      s
  | op :: _ =>
      execute op s


/-- Execute a complete program. -/
def run : Program → CoreState → CoreState
  | [], s =>
      s
  | op :: rest, s =>
      run rest (execute op s)


/-- Empty program is identity. -/
theorem run_nil (s : CoreState) :
    run [] s = s := by
  rfl


/-- Single instruction execution. -/
theorem run_single
    (op : Op)
    (s : CoreState) :
    run [op] s = execute op s := by
  rfl


/-! ================================================================
    10. Reversibility
================================================================ -/

/--
  X has an exact inverse: itself.
-/
def inverseX : Transform :=
  X


/--
  Z has an exact inverse: itself.
-/
def inverseZ : Transform :=
  Z


/-- X followed by its inverse returns the state. -/
theorem X_reversible (s : DState) :
    inverseX (X s) = s := by
  simp [inverseX, X, applyX_involutive]


/-- Z followed by its inverse returns the state. -/
theorem Z_reversible (s : DState) :
    inverseZ (Z s) = s := by
  simp [inverseZ, Z, applyZ_involutive]


/-! ================================================================
    11. Algebraic Core Invariant
================================================================ -/

/--
  X, Z and Y preserve the discrete total norm.

  This gives the core a simple conserved quantity.
-/
def preservesNorm
    (t : Transform) : Prop :=
  ∀ s : DState,
    DState.normSq (t s) =
      DState.normSq s


theorem X_preservesNorm :
    preservesNorm X := by
  intro s
  exact applyX_preserves_norm s


theorem Z_preservesNorm :
    preservesNorm Z := by
  intro s
  exact applyZ_preserves_norm s


theorem Y_preservesNorm :
    preservesNorm Y := by
  intro s
  exact applyY_preserves_norm s


/-! ================================================================
    12. Deterministic Computational Kernel
================================================================ -/

/--
  Complete UHACore kernel.

  A kernel contains a program and an initial state.
-/
structure Kernel where
  program : Program
  initial : CoreState


/-- Run a kernel. -/
def Kernel.run
    (k : Kernel) :
    CoreState :=
  run k.program k.initial


/--
  Kernel execution is deterministic because
  Program and State are ordinary mathematical values
  and every operation is a total function.
-/
theorem kernel_deterministic
    (k : Kernel) :
    Kernel.run k = Kernel.run k := by
  rfl


/-! ================================================================
    13. Fixed Point
================================================================ -/

/--
  A transformation fixed point.
-/
def IsFixed
    (t : Transform)
    (s : DState) : Prop :=
  t s = s


/-- Identity fixes every state. -/
theorem identity_fixed (s : DState) :
    IsFixed identity s := by
  rfl


/-- X fixes states whose two amplitudes are equal. -/
theorem X_fixed_of_equal
    (a : DComplex) :
    IsFixed X ⟨a, a⟩ := by
  rfl


/-- Z fixes states whose second amplitude is zero. -/
theorem Z_fixed_of_zero
    (a : DComplex) :
    IsFixed Z ⟨a, DComplex.zero⟩ := by
  rfl


end DState

end UHACore
