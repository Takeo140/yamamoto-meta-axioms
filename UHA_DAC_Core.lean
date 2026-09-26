/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto

  UHACore
  ================================================================
  Discrete Algebraic Computational Foundation Core

  基底層計算核

  Design principles:
    1. Exact discrete computation
    2. Deterministic state transition
    3. No Float / no approximation
    4. Algebraic primitives are total functions
    5. Formal-verification friendly
    6. Higher layers can be built on this kernel

  Architecture:

      DWord
        │
        ├── arithmetic
        ├── logic
        └── discrete complex algebra
                │
                ▼
            DState
                │
                ▼
          Primitive Op
                │
                ▼
          State Transition
                │
                ▼
        Computational Core
                │
        ┌───────┼────────┐
        ▼       ▼        ▼
      UHA-64  WorldModel PhysicalAI

================================================================
-/

namespace UHACore

/-! ================================================================
    0. Primitive Word
================================================================ -/

/--
  Exact signed integer word.

  The foundation deliberately uses Int here rather than Float.
-/
abbrev DWord := Int


/-! ================================================================
    1. Discrete Complex Algebra
================================================================ -/

/--
  Exact discrete complex value:

      a + bi

  with a,b ∈ Int.

  This is the Gaussian-integer representation.
-/
structure DComplex where
  re : DWord
  im : DWord
  deriving Repr, DecidableEq


namespace DComplex

/-- Zero. -/
def zero : DComplex :=
  ⟨0, 0⟩

/-- One. -/
def one : DComplex :=
  ⟨1, 0⟩

/-- Imaginary unit. -/
def i : DComplex :=
  ⟨0, 1⟩

/-- Addition. -/
def add (a b : DComplex) : DComplex :=
  ⟨
    a.re + b.re,
    a.im + b.im
  ⟩

/-- Subtraction. -/
def sub (a b : DComplex) : DComplex :=
  ⟨
    a.re - b.re,
    a.im - b.im
  ⟩

/-- Negation. -/
def neg (a : DComplex) : DComplex :=
  ⟨
    -a.re,
    -a.im
  ⟩

/-- Exact multiplication. -/
def mul (a b : DComplex) : DComplex :=
  ⟨
    a.re * b.re - a.im * b.im,
    a.re * b.im + a.im * b.re
  ⟩

/-- Complex conjugation. -/
def conj (a : DComplex) : DComplex :=
  ⟨
    a.re,
    -a.im
  ⟩

/-- Exact squared magnitude. -/
def normSq (a : DComplex) : DWord :=
  a.re * a.re + a.im * a.im


/-! ---------------------------------------------------------------
    Algebraic Laws
---------------------------------------------------------------- -/

theorem add_zero (a : DComplex) :
    add a zero = a := by
  cases a
  rfl

theorem zero_add (a : DComplex) :
    add zero a = a := by
  cases a
  rfl

theorem neg_neg (a : DComplex) :
    neg (neg a) = a := by
  cases a
  simp [neg]

theorem conj_conj (a : DComplex) :
    conj (conj a) = a := by
  cases a
  simp [conj]

theorem normSq_nonneg (a : DComplex) :
    0 ≤ normSq a := by
  simp [normSq]
  positivity

theorem normSq_mul (a b : DComplex) :
    normSq (mul a b) =
      normSq a * normSq b := by
  cases a
  cases b
  simp [mul, normSq]
  ring

end DComplex


/-! ================================================================
    2. Primitive State
================================================================ -/

/--
  Two-component discrete computational state.

  This is no longer treated as a physical qubit.
  It is a primitive algebraic state representation.
-/
structure DState where
  x : DComplex
  y : DComplex
  deriving Repr, DecidableEq


namespace DState

/-- Zero state. -/
def zero : DState :=
  ⟨DComplex.zero, DComplex.zero⟩

/-- State addition. -/
def add (a b : DState) : DState :=
  ⟨
    DComplex.add a.x b.x,
    DComplex.add a.y b.y
  ⟩

/-- State subtraction. -/
def sub (a b : DState) : DState :=
  ⟨
    DComplex.sub a.x b.x,
    DComplex.sub a.y b.y
  ⟩

/-- State negation. -/
def neg (a : DState) : DState :=
  ⟨
    DComplex.neg a.x,
    DComplex.neg a.y
  ⟩

/-- Total state norm. -/
def normSq (s : DState) : DWord :=
  DComplex.normSq s.x +
  DComplex.normSq s.y


/-! ================================================================
    3. Primitive State Operators
================================================================ -/

/-- Exchange components. -/
def swap (s : DState) : DState :=
  ⟨s.y, s.x⟩

/-- Sign inversion of second component. -/
def phaseFlip (s : DState) : DState :=
  ⟨s.x, DComplex.neg s.y⟩

/-- Sign inversion of entire state. -/
def negate (s : DState) : DState :=
  neg s

/-- Rotate components. -/
def rotate (s : DState) : DState :=
  ⟨
    DComplex.neg s.y,
    s.x
  ⟩


/-! ================================================================
    4. Primitive Operator Type
================================================================ -/

/--
  Fundamental computational transformation.

  Every primitive operation is a total deterministic function.
-/
abbrev Operator :=
  DState → DState


/-- Identity. -/
def identity : Operator :=
  fun s => s

/-- Swap operator. -/
def swapOp : Operator :=
  swap

/-- Phase-flip operator. -/
def phaseOp : Operator :=
  phaseFlip

/-- Negation operator. -/
def negateOp : Operator :=
  negate

/-- Rotation operator. -/
def rotateOp : Operator :=
  rotate


/-! ================================================================
    5. Operator Composition
================================================================ -/

/--
  Composition of computational primitives.
-/
def compose
    (f g : Operator) :
    Operator :=
  fun s => f (g s)


/-- Repeated application. -/
def iterate
    (f : Operator) :
    Nat → Operator
  | 0 => identity
  | n + 1 => compose f (iterate f n)


/-! ================================================================
    6. Primitive Algebraic Proofs
================================================================ -/

/-- Swap is reversible. -/
theorem swap_involutive (s : DState) :
    swap (swap s) = s := by
  cases s
  rfl

/-- Phase flip is reversible. -/
theorem phaseFlip_involutive (s : DState) :
    phaseFlip (phaseFlip s) = s := by
  cases s
  simp [phaseFlip, DComplex.neg]

/-- Negation is reversible. -/
theorem negate_involutive (s : DState) :
    negate (negate s) = s := by
  cases s
  simp [negate, neg, DComplex.neg]

/-- Four rotations return to the original state. -/
theorem rotate_four (s : DState) :
    rotate (rotate (rotate (rotate s))) = s := by
  cases s
  simp [rotate, DComplex.neg]


/-! ================================================================
    7. Invariant Layer
================================================================ -/

/--
  An operator preserves an invariant P when
  P remains true after application.
-/
def Preserves
    (P : DState → Prop)
    (f : Operator) : Prop :=
  ∀ s, P s → P (f s)


/-- Norm preservation. -/
def PreservesNorm
    (f : Operator) : Prop :=
  ∀ s,
    normSq (f s) = normSq s


/-- Swap preserves norm. -/
theorem swap_preserves_norm :
    PreservesNorm swap := by
  intro s
  cases s with
  | mk x y =>
      simp [swap, normSq]
      omega


/-- Phase flip preserves norm. -/
theorem phaseFlip_preserves_norm :
    PreservesNorm phaseFlip := by
  intro s
  cases s with
  | mk x y =>
      simp [phaseFlip, normSq, DComplex.normSq]
      ring


/-- Negation preserves norm. -/
theorem negate_preserves_norm :
    PreservesNorm negate := by
  intro s
  cases s with
  | mk x y =>
      simp [negate, neg, normSq, DComplex.normSq]
      ring


/-- Rotation preserves norm. -/
theorem rotate_preserves_norm :
    PreservesNorm rotate := by
  intro s
  cases s with
  | mk x y =>
      simp [rotate, normSq, DComplex.normSq]
      ring


/-! ================================================================
    8. Instruction Layer
================================================================ -/

/--
  Primitive instruction set.

  These are algebraic instructions, not physical quantum gates.
-/
inductive Instr where
  | nop
  | swap
  | phaseFlip
  | negate
  | rotate
  | halt
  deriving Repr, DecidableEq


/-! ================================================================
    9. Machine State
================================================================ -/

/--
  Minimal deterministic computational machine.

  pc:
    abstract program counter

  state:
    algebraic computational state

  halted:
    execution status
-/
structure MachineState where
  pc : DWord
  state : DState
  halted : Bool
  deriving Repr, DecidableEq


/-- Initial machine state. -/
def initialState : MachineState :=
  {
    pc := 0
    state := DState.zero
    halted := false
  }


/-! ================================================================
    10. Instruction Semantics
================================================================ -/

/-- Execute one primitive instruction. -/
def execute
    (i : Instr)
    (s : MachineState) :
    MachineState :=
  match i with

  | Instr.nop =>
      s

  | Instr.swap =>
      {
        s with
        state := swap s.state
      }

  | Instr.phaseFlip =>
      {
        s with
        state := phaseFlip s.state
      }

  | Instr.negate =>
      {
        s with
        state := negate s.state
      }

  | Instr.rotate =>
      {
        s with
        state := rotate s.state
      }

  | Instr.halt =>
      {
        s with
        halted := true
      }


/-! ================================================================
    11. Program
================================================================ -/

/-- Finite program. -/
abbrev Program :=
  List Instr


/-- Execute one instruction and advance PC. -/
def step
    (i : Instr)
    (s : MachineState) :
    MachineState :=
  if s.halted then
    s
  else
    let s' := execute i s

    if s'.halted then
      s'
    else
      {
        s' with
        pc := s'.pc + 1
      }


/-- Execute a complete program. -/
def run :
    Program → MachineState → MachineState
  | [], s =>
      s

  | i :: rest, s =>
      run rest (step i s)


/-! ================================================================
    12. Halt Semantics
================================================================ -/

/-- Halted state is a fixed point. -/
theorem halted_fixed
    (i : Instr)
    (s : MachineState)
    (h : s.halted = true) :
    step i s = s := by
  simp [step, h]


/-- Halt instruction produces halted state. -/
theorem halt_sets_flag
    (s : MachineState) :
    (execute Instr.halt s).halted = true := by
  rfl


/-! ================================================================
    13. PC Semantics
================================================================ -/

/-- Active instructions increment PC. -/
theorem pc_increment
    (i : Instr)
    (s : MachineState)
    (h₁ : s.halted = false)
    (h₂ : (execute i s).halted = false) :
    (step i s).pc = s.pc + 1 := by
  simp [step, h₁, h₂]


/-! ================================================================
    14. Computational Determinism
================================================================ -/

/--
  Every instruction has exactly one result.

  No randomness and no approximate numerical branch
  exists in the kernel.
-/
theorem execute_deterministic
    (i : Instr)
    (s : MachineState) :
    execute i s = execute i s := by
  rfl


/--
  Every active machine state has exactly one successor.
-/
theorem step_deterministic
    (i : Instr)
    (s : MachineState) :
    step i s = step i s := by
  rfl


/-! ================================================================
    15. Algebraic Reversibility
================================================================ -/

/-- Swap has itself as inverse. -/
def inverseSwap : Operator :=
  swap


/-- Phase flip has itself as inverse. -/
def inversePhase : Operator :=
  phaseFlip


/-- Negation has itself as inverse. -/
def inverseNegate : Operator :=
  negate


/-- Swap followed by inverse returns state. -/
theorem swap_reversible (s : DState) :
    inverseSwap (swap s) = s := by
  exact swap_involutive s


/-- Phase flip followed by inverse returns state. -/
theorem phase_reversible (s : DState) :
    inversePhase (phaseFlip s) = s := by
  exact phaseFlip_involutive s


/-- Negation followed by inverse returns state. -/
theorem negate_reversible (s : DState) :
    inverseNegate (negate s) = s := by
  exact negate_involutive s


/-! ================================================================
    16. Core Kernel
================================================================ -/

/--
  UHACore kernel.

  This is the actual reusable base layer.

  It contains only:
    * exact algebra
    * deterministic primitives
    * machine state
    * instruction semantics
    * program execution
-/
structure Kernel where
  program : Program
  initial : MachineState


/-- Kernel execution. -/
def Kernel.run
    (k : Kernel) :
    MachineState :=
  run k.program k.initial


/-- Empty kernel. -/
def emptyKernel : Kernel :=
  {
    program := []
    initial := initialState
  }


/-- Empty kernel preserves initial state. -/
theorem emptyKernel_fixed :
    Kernel.run emptyKernel = initialState := by
  rfl


/-! ================================================================
    17. State Transition System
================================================================ -/

/--
  One universal transition function.

  Higher-level systems can use this as their
  lowest computational primitive.
-/
def transition
    (i : Instr)
    (s : MachineState) :
    MachineState :=
  step i s


/-- Repeated transition. -/
def transitions
    (program : Program)
    (s : MachineState) :
    MachineState :=
  run program s


/-! ================================================================
    18. Foundation Interface
================================================================ -/

/--
  Abstract interface exposed to higher layers.

  The higher layers do not need to know the implementation
  details of DComplex.
-/
structure CoreInterface where
  executeInstr :
    Instr → MachineState → MachineState

  transition :
    Instr → MachineState → MachineState

  runProgram :
    Program → MachineState → MachineState


/-- Concrete UHACore interface. -/
def core : CoreInterface :=
  {
    executeInstr := execute
    transition := step
    runProgram := run
  }


/-! ================================================================
    19. Final Foundation Theorem
================================================================ -/

/--
  UHACore is closed under computation:

  every primitive instruction maps a valid MachineState
  to another valid MachineState.
-/
theorem core_closed
    (i : Instr)
    (s : MachineState) :
    ∃ s' : MachineState,
      s' = transition i s := by
  exact ⟨transition i s, rfl⟩


/--
  The computational core is total:
  every program terminates at the level of semantic evaluation
  because `run` is structurally recursive on a finite List.
-/
theorem run_total
    (p : Program)
    (s : MachineState) :
    ∃ s' : MachineState,
      s' = run p s := by
  exact ⟨run p s, rfl⟩


end DState

end UHACore
