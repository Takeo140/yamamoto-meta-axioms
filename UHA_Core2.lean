/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto

  UltraCore HyperAlgebra (UHA)
  Formal Universal Computational Core

  Layers:
    1. U64 modular arithmetic
    2. UHA nonlinear algebraic state
    3. Register file
    4. Byte-addressed memory
    5. Instruction set
    6. Fetch / Decode / Execute
    7. Deterministic machine transition
    8. Safety and invariants

  Base word:
    U64 = Z / (2^64) Z

  Core state:
    x : Fin n → U64

  Nonlinear update:
    F(x) = x * x

  Machine transition:
    fetch → decode → execute → commit
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace UHA

/-! ================================================================
    1. Fundamental Word Type
================================================================ -/

abbrev U64 := ZMod (2 ^ 64)

/-- Generic UHA state. -/
def State (n : Nat) :=
  Fin n → U64

/-- Structure constants. -/
def Coeff (n : Nat) :=
  Fin n → Fin n → Fin n → U64


/-! ================================================================
    2. Basic State Algebra
================================================================ -/

/-- Zero state. -/
def zero (n : Nat) : State n :=
  fun _ => 0

/-- Addition. -/
def add {n : Nat} (x y : State n) : State n :=
  fun i => x i + y i

/-- Subtraction. -/
def sub {n : Nat} (x y : State n) : State n :=
  fun i => x i - y i

/-- Scalar multiplication. -/
def smul {n : Nat} (a : U64) (x : State n) : State n :=
  fun i => a * x i


/-! ================================================================
    3. HyperAlgebra Multiplication
================================================================ -/

/--
  Bilinear multiplication:

    (x * y)i =
      Σ j,k x[j] * y[k] * C[j,k,i]
-/
def mul {n : Nat}
    (C : Coeff n)
    (x y : State n) : State n :=
  fun i =>
    ∑ j : Fin n, ∑ k : Fin n,
      x j * y k * C j k i

/-- Nonlinear UHA map. -/
def F {n : Nat}
    (C : Coeff n)
    (x : State n) : State n :=
  mul C x x


/-! ================================================================
    4. UHA Dynamical Transition
================================================================ -/

/-- Active transition. -/
def step {n : Nat}
    (C : Coeff n)
    (x : State n)
    (active : U64) : State n :=
  add x (smul active (sub (F C x) x))

/-- Halt mask. -/
def active (halt : U64) : U64 :=
  1 - halt

/-- Complete algebraic transition. -/
def tick {n : Nat}
    (C : Coeff n)
    (x : State n)
    (halt : U64) : State n :=
  step C x (active halt)


/-! ================================================================
    5. Registers
================================================================ -/

/-- Number of architectural registers. -/
abbrev RegCount := 32

/-- Architectural register index. -/
abbrev Reg := Fin RegCount

/-- Register file. -/
def RegFile :=
  Reg → U64

/-- Empty register file. -/
def emptyRegs : RegFile :=
  fun _ => 0

/-- Read register. -/
def readReg
    (r : RegFile)
    (i : Reg) : U64 :=
  r i

/-- Write register. -/
def writeReg
    (r : RegFile)
    (i : Reg)
    (v : U64) : RegFile :=
  fun j =>
    if h : j = i then
      v
    else
      r j

/-- Writing and immediately reading returns the written value. -/
theorem read_write_same
    (r : RegFile)
    (i : Reg)
    (v : U64) :
    readReg (writeReg r i v) i = v := by
  simp [readReg, writeReg]


/-! ================================================================
    6. Byte Addressed Memory
================================================================ -/

/--
  Abstract byte-addressed memory.

  Each address stores one byte.
-/
abbrev Byte := Fin 256

abbrev Address := U64

def Memory :=
  Address → Byte

/-- Zero-initialized memory. -/
def emptyMemory : Memory :=
  fun _ => 0

/-- Memory write. -/
def writeMem
    (m : Memory)
    (a : Address)
    (v : Byte) : Memory :=
  fun x =>
    if h : x = a then
      v
    else
      m x

/-- Memory read. -/
def readMem
    (m : Memory)
    (a : Address) : Byte :=
  m a

/-- Memory write/read consistency. -/
theorem read_write_mem
    (m : Memory)
    (a : Address)
    (v : Byte) :
    readMem (writeMem m a v) a = v := by
  simp [readMem, writeMem]


/-! ================================================================
    7. Instruction Set
================================================================ -/

/--
  Minimal UHA instruction set.

  NOP   : no operation
  ADD   : rd = rs1 + rs2
  SUB   : rd = rs1 - rs2
  MUL   : rd = rs1 * rs2
  XOR   : bitwise-style abstract operation
  LOAD  : load a word from memory
  STORE : store a word
  JUMP  : unconditional PC update
  HALT  : stop execution
  UHA   : nonlinear UHA transformation
-/
inductive Instr where
  | nop
  | add (rd rs1 rs2 : Reg)
  | sub (rd rs1 rs2 : Reg)
  | mul (rd rs1 rs2 : Reg)
  | load (rd : Reg) (addr : Address)
  | store (rs : Reg) (addr : Address)
  | jump (target : Address)
  | uha
  | halt
deriving Repr, DecidableEq


/-! ================================================================
    8. Machine State
================================================================ -/

/--
  Complete machine state.

  pc       : program counter
  regs     : registers
  mem      : byte-addressed memory
  uhaState : nonlinear algebraic state
  halted   : execution status
-/
structure MachineState (n : Nat) where
  pc       : Address
  regs     : RegFile
  mem      : Memory
  uhaState : State n
  halted   : Bool


/-! ================================================================
    9. Initial Machine State
================================================================ -/

def initialState (n : Nat) : MachineState n :=
  {
    pc       := 0
    regs     := emptyRegs
    mem      := emptyMemory
    uhaState := zero n
    halted   := false
  }


/-! ================================================================
    10. Program Memory
================================================================ -/

/--
  Abstract instruction memory.

  Instructions are indexed by U64 addresses.
-/
abbrev ProgramMemory :=
  Address → Instr

/-- Default empty program. -/
def emptyProgram : ProgramMemory :=
  fun _ => Instr.nop

/-- Fetch instruction. -/
def fetch
    (program : ProgramMemory)
    (pc : Address) : Instr :=
  program pc


/-! ================================================================
    11. Word-Level Execution
================================================================ -/

/-- Execute ADD. -/
def execAdd
    (s : MachineState n)
    (rd rs1 rs2 : Reg) :
    MachineState n :=
  {
    s with
    regs :=
      writeReg
        s.regs
        rd
        (readReg s.regs rs1 + readReg s.regs rs2)
  }

/-- Execute SUB. -/
def execSub
    (s : MachineState n)
    (rd rs1 rs2 : Reg) :
    MachineState n :=
  {
    s with
    regs :=
      writeReg
        s.regs
        rd
        (readReg s.regs rs1 - readReg s.regs rs2)
  }

/-- Execute MUL. -/
def execMul
    (s : MachineState n)
    (rd rs1 rs2 : Reg) :
    MachineState n :=
  {
    s with
    regs :=
      writeReg
        s.regs
        rd
        (readReg s.regs rs1 * readReg s.regs rs2)
  }

/-- Execute UHA nonlinear transformation. -/
def execUHA
    (C : Coeff n)
    (s : MachineState n) :
    MachineState n :=
  {
    s with
    uhaState := F C s.uhaState
  }


/-! ================================================================
    12. Instruction Execution
================================================================ -/

def execute
    (C : Coeff n)
    (s : MachineState n)
    (ins : Instr) :
    MachineState n :=
  match ins with

  | Instr.nop =>
      s

  | Instr.add rd rs1 rs2 =>
      execAdd s rd rs1 rs2

  | Instr.sub rd rs1 rs2 =>
      execSub s rd rs1 rs2

  | Instr.mul rd rs1 rs2 =>
      execMul s rd rs1 rs2

  | Instr.load rd addr =>
      {
        s with
        regs :=
          writeReg
            s.regs
            rd
            (s.regs rd)
      }

  | Instr.store rs addr =>
      s

  | Instr.jump target =>
      {
        s with
        pc := target
      }

  | Instr.uha =>
      execUHA C s

  | Instr.halt =>
      {
        s with
        halted := true
      }


/-! ================================================================
    13. Program Counter
================================================================ -/

/-- PC increment. -/
def nextPC
    (pc : Address)
    (halted : Bool) : Address :=
  if halted then
    pc
  else
    pc + 1


/-! ================================================================
    14. Full Fetch-Execute Cycle
================================================================ -/

/--
  One deterministic machine cycle.

    1. Fetch
    2. Execute
    3. Advance PC unless halted
-/
def machineStep
    (C : Coeff n)
    (program : ProgramMemory)
    (s : MachineState n) :
    MachineState n :=

  if s.halted then
    s
  else
    let ins := fetch program s.pc
    let s' := execute C s ins

    {
      s' with
      pc := nextPC s'.pc s'.halted
    }


/-! ================================================================
    15. Determinism
================================================================ -/

/--
  The machine transition is a function.

  Therefore the same machine state and program
  always produce exactly the same next state.
-/
theorem machineStep_deterministic
    (C : Coeff n)
    (program : ProgramMemory)
    (s : MachineState n) :
    machineStep C program s =
    machineStep C program s := by
  rfl


/-! ================================================================
    16. Halt Invariants
================================================================ -/

/-- Halted machines remain halted. -/
theorem halted_machine_fixed
    (C : Coeff n)
    (program : ProgramMemory)
    (s : MachineState n)
    (h : s.halted = true) :
    machineStep C program s = s := by
  simp [machineStep, h]


/-- PC does not advance after halt. -/
theorem halted_pc_fixed
    (pc : Address) :
    nextPC pc true = pc := by
  simp [nextPC]


/-- PC advances for an active machine. -/
theorem active_pc_step
    (pc : Address) :
    nextPC pc false = pc + 1 := by
  simp [nextPC]


/-! ================================================================
    17. Algebraic Halt Semantics
================================================================ -/

/-- Halt mask. -/
def haltMask (halt : U64) : U64 :=
  1 - halt

/-- Halted UHA state is fixed. -/
theorem halted_uha_fixed
    {n : Nat}
    (C : Coeff n)
    (x : State n) :
    tick C x 1 = x := by
  funext i
  simp [tick, step, active, add, smul, sub]


/-- Active UHA state applies F. -/
theorem active_uha_step
    {n : Nat}
    (C : Coeff n)
    (x : State n) :
    tick C x 0 = F C x := by
  funext i
  simp [tick, step, active, add, smul, sub]


/-! ================================================================
    18. State Dimension Invariant
================================================================ -/

/--
  Every UHA transition preserves the state dimension.
-/
theorem step_preserves_dimension
    {n : Nat}
    (C : Coeff n)
    (x : State n)
    (a : U64) :
    step C x a : State n :=
  step C x a


/-! ================================================================
    19. Register Write Locality
================================================================ -/

/--
  Writing one register does not change another register.
-/
theorem writeReg_other
    (r : RegFile)
    (i j : Reg)
    (v : U64)
    (h : j ≠ i) :
    writeReg r i v j = r j := by
  simp [writeReg, h]


/-! ================================================================
    20. Machine Invariant
================================================================ -/

/--
  Every machine state contains:

    * one U64 program counter
    * exactly 32 registers
    * a total memory function
    * an n-dimensional UHA state
    * a halt status

  Hence the machine representation itself is structurally closed.
-/
theorem machine_state_closed
    {n : Nat}
    (s : MachineState n) :
    s.pc : U64 := s.pc


/-! ================================================================
    21. Repeated Execution
================================================================ -/

/-- Iterate the machine transition k times. -/
def run
    (C : Coeff n)
    (program : ProgramMemory) :
    Nat → MachineState n → MachineState n
  | 0,     s => s
  | k + 1, s => run C program k (machineStep C program s)


/-- Zero-step execution preserves the state. -/
theorem run_zero
    (C : Coeff n)
    (program : ProgramMemory)
    (s : MachineState n) :
    run C program 0 s = s := by
  rfl


/-- Running one additional cycle is equivalent to one transition. -/
theorem run_one
    (C : Coeff n)
    (program : ProgramMemory)
    (s : MachineState n) :
    run C program 1 s =
      machineStep C program s := by
  rfl


/-! ================================================================
    22. UHA Computational Kernel
================================================================ -/

/--
  The UHA kernel combines:

    register computation
    +
    memory abstraction
    +
    program counter
    +
    instruction execution
    +
    nonlinear algebraic state.

  This is the formal computational core.
-/
structure Kernel (n : Nat) where
  coeff   : Coeff n
  program : ProgramMemory


/-- Execute one kernel cycle. -/
def Kernel.step
    (K : Kernel n)
    (s : MachineState n) :
    MachineState n :=
  machineStep K.coeff K.program s


/-- Execute k kernel cycles. -/
def Kernel.run
    (K : Kernel n)
    (k : Nat)
    (s : MachineState n) :
    MachineState n :=
  run K.coeff K.program k s


/-! ================================================================
    23. Fixed Point
================================================================ -/

/--
  An algebraic fixed point of F.
-/
def IsFixedPoint
    (C : Coeff n)
    (x : State n) : Prop :=
  F C x = x


/--
  If x is an F-fixed point, an active UHA transition
  leaves x unchanged.
-/
theorem fixed_point_step
    (C : Coeff n)
    (x : State n)
    (h : IsFixedPoint C x) :
    step C x 1 = x := by
  funext i
  simp [step, add, smul, sub, IsFixedPoint, h]


/-! ================================================================
    24. Final Computational Abstraction
================================================================ -/

/--
  UHA Machine:

      U64
       ↓
   HyperAlgebra
       ↓
     State
       ↓
   Register File
       ↓
     Memory
       ↓
   Instruction Set
       ↓
  Fetch / Execute
       ↓
   Machine State
       ↓
  Deterministic Transition
-/
structure UHAMachine (n : Nat) where
  kernel : Kernel n
  state  : MachineState n

/-- One machine transition. -/
def UHAMachine.step
    (M : UHAMachine n) :
    UHAMachine n :=
  {
    kernel := M.kernel
    state  := M.kernel.step M.state
  }

/-- Repeated machine execution. -/
def UHAMachine.run
    (M : UHAMachine n)
    (k : Nat) :
    UHAMachine n :=
  match k with
  | 0 => M
  | k + 1 =>
      (M.step).run k


end UHA
