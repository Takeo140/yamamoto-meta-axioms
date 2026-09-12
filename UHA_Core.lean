License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic

namespace UHA

/-
  UHA Computational Core

  Base ring:
    U64 = Z / (2^64) Z

  State:
    x : Fin n → U64

  Structure constants:
    C : Fin n → Fin n → Fin n → U64

  Bilinear multiplication:
    (x * y) i = Σ j,k, x j * y k * C j k i

  Nonlinear map:
    F(x) = x * x

  State transition:
    x' = x + active • (F(x) - x)

  halt = 1  => active = 0
  halt = 0  => active = 1
-/

abbrev U64 := ZMod (2 ^ 64)

/-- n-dimensional UHA state. -/
def State (n : Nat) :=
  Fin n → U64

/-- Structure constants C[j,k,i]. -/
def Coeff (n : Nat) :=
  Fin n → Fin n → Fin n → U64


/-- Zero state. -/
def zero (n : Nat) : State n :=
  fun _ => 0


/-- State addition. -/
def add {n : Nat} (x y : State n) : State n :=
  fun i => x i + y i


/-- State subtraction. -/
def sub {n : Nat} (x y : State n) : State n :=
  fun i => x i - y i


/-- Scalar multiplication. -/
def smul {n : Nat} (a : U64) (x : State n) : State n :=
  fun i => a * x i


/--
  Bilinear UHA multiplication.

  (x * y) i =
    Σ j, Σ k, x j * y k * C j k i
-/
def mul {n : Nat}
    (C : Coeff n)
    (x y : State n) : State n :=
  fun i =>
    ∑ j : Fin n, ∑ k : Fin n,
      x j * y k * C j k i


/--
  Nonlinear UHA map.

  F(x) = x * x
-/
def F {n : Nat}
    (C : Coeff n)
    (x : State n) : State n :=
  mul C x x


/--
  Active state transition.

  x' = x + active • (F(x) - x)
-/
def step {n : Nat}
    (C : Coeff n)
    (x : State n)
    (active : U64) : State n :=
  add x (smul active (sub (F C x) x))


/--
  Halt mask.

  active = 1 - halt
-/
def active (halt : U64) : U64 :=
  1 - halt


/--
  Complete UHA transition using halt mask.
-/
def tick {n : Nat}
    (C : Coeff n)
    (x : State n)
    (halt : U64) : State n :=
  step C x (active halt)


/--
  Program counter transition.
-/
def pcStep (pc halt : U64) : U64 :=
  pc + active halt


/--
  Halted state is a fixed point.
-/
theorem halted_fixed
    {n : Nat}
    (C : Coeff n)
    (x : State n) :
    tick C x 1 = x := by
  funext i
  simp [tick, step, active, add, smul, sub]


/--
  Active state applies F(x).

  When halt = 0:
    x' = F(x)
-/
theorem active_step
    {n : Nat}
    (C : Coeff n)
    (x : State n) :
    tick C x 0 = F C x := by
  funext i
  simp [tick, step, active, add, smul, sub]


/--
  The state dimension is preserved by every transition.
-/
theorem step_preserves_dimension
    {n : Nat}
    (C : Coeff n)
    (x : State n)
    (a : U64) :
    step C x a : State n :=
  step C x a


/--
  Halted program counter is unchanged.
-/
theorem halted_pc_fixed
    (pc : U64) :
    pcStep pc 1 = pc := by
  simp [pcStep, active]


/--
  Active program counter advances by one.
-/
theorem active_pc_step
    (pc : U64) :
    pcStep pc 0 = pc + 1 := by
  simp [pcStep, active]


end UHA
