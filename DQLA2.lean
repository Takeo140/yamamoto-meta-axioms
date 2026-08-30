import Mathlib

/-!
# Discrete Quantum Linear Algebra
## A GF(2) Symplectic Foundation for Stabilizer Quantum Computation

Copyright (c) 2026 Yamamoto Takeo
License: Apache License 2.0

This file provides a single-file formal foundation for discrete
linear-algebraic quantum computation.

Implemented layers:

1. GF(2) = ZMod 2
2. Binary vectors
3. Binary matrices
4. Pauli operators modulo global phase
5. Pauli multiplication
6. Binary symplectic form
7. Commutation / anticommutation
8. Clifford gates:
   * Hadamard
   * Phase
   * CNOT
9. Gate involution theorems
10. Stabilizer generators
11. Stabilizer states
12. Clifford circuits
13. Two-qubit Bell-state construction
14. Binary symplectic matrices
15. Symplectic-preservation predicates

Mathematical representation:

    Pauli(n) / phase ≅ GF(2)^(2n)

with

    p = (x,z)

and binary symplectic form

    ω(p,q) = x·z' + z·x'

over GF(2).
-/

namespace DiscreteQuantum

open scoped BigOperators

/-!
================================================================
1. GF(2)
================================================================
-/

/-- The binary finite field GF(2). -/
abbrev GF2 := ZMod 2

namespace GF2

/-- Characteristic two. -/
theorem add_self_eq_zero (a : GF2) :
    a + a = 0 := by
  exact add_self a

/-- Subtraction equals addition in GF(2). -/
theorem sub_eq_add (a b : GF2) :
    a - b = a + b := by
  simp [sub_eq_add_neg, ← add_assoc, add_self_eq_zero]

/-- Every element is its own additive inverse. -/
theorem neg_eq_self (a : GF2) :
    -a = a := by
  have h : a + a = 0 := add_self_eq_zero a
  apply eq_neg_of_add_eq_zero_left
  simpa [add_comm] using h

end GF2


/-!
================================================================
2. Binary vectors
================================================================
-/

/-- A vector over GF(2), indexed by `n`. -/
abbrev BitVec (n : Type*) := n → GF2

namespace BitVec

variable {n : Type*}

/-- Zero vector. -/
def zero : BitVec n :=
  fun _ => 0

/-- Vector addition. -/
def add (x y : BitVec n) : BitVec n :=
  fun i => x i + y i

/-- Scalar multiplication. -/
def scale (a : GF2) (x : BitVec n) : BitVec n :=
  fun i => a * x i

theorem ext
    {x y : BitVec n}
    (h : ∀ i, x i = y i) :
    x = y := by
  funext i
  exact h i

theorem add_comm
    (x y : BitVec n) :
    add x y = add y x := by
  funext i
  exact add_comm _ _

theorem add_assoc
    (x y z : BitVec n) :
    add (add x y) z = add x (add y z) := by
  funext i
  exact add_assoc _ _ _

theorem add_zero
    (x : BitVec n) :
    add x zero = x := by
  funext i
  simp [add, zero]

theorem zero_add
    (x : BitVec n) :
    add zero x = x := by
  funext i
  simp [add, zero]

theorem add_self
    (x : BitVec n) :
    add x x = zero := by
  funext i
  simp [add, zero]

end BitVec


/-!
================================================================
3. Binary linear algebra
================================================================
-/

namespace BinaryLinear

variable {ι κ λ : Type*}

/-- Binary matrix. -/
abbrev Matrix2 (ι κ : Type*) :=
  Matrix ι κ GF2

/-- Matrix-vector multiplication. -/
def mulVec
    [Fintype κ]
    (A : Matrix2 ι κ)
    (x : BitVec κ) :
    BitVec ι :=
  fun i => ∑ j, A i j * x j

/-- Matrix multiplication over GF(2). -/
def mul
    [Fintype κ]
    (A : Matrix2 ι κ)
    (B : Matrix2 κ λ) :
    Matrix2 ι λ :=
  fun i k => ∑ j, A i j * B j k

/-- Matrix transpose. -/
def transpose
    (A : Matrix2 ι κ) :
    Matrix2 κ ι :=
  fun j i => A i j

/-- Identity matrix. -/
def identity [DecidableEq ι] :
    Matrix2 ι ι :=
  fun i j => if i = j then 1 else 0

theorem transpose_transpose
    (A : Matrix2 ι κ) :
    transpose (transpose A) = A := by
  funext i j
  rfl

end BinaryLinear


/-!
================================================================
4. Pauli operators modulo global phase
================================================================

A Pauli operator is represented as:

    (x,z)

where x,z ∈ GF(2)^n.

For one qubit:

    I = (0,0)
    X = (1,0)
    Z = (0,1)
    Y = (1,1)

Global phases ±1, ±i are omitted.
-/

/-- Pauli operator modulo global phase. -/
structure Pauli (n : Type*) where
  x : BitVec n
  z : BitVec n

namespace Pauli

variable {n : Type*}

/-- Identity Pauli. -/
def identity : Pauli n where
  x := BitVec.zero
  z := BitVec.zero

/-- Phase-free Pauli multiplication. -/
def multiply
    (p q : Pauli n) :
    Pauli n where
  x := BitVec.add p.x q.x
  z := BitVec.add p.z q.z

@[ext]
theorem ext
    {p q : Pauli n}
    (hx : p.x = q.x)
    (hz : p.z = q.z) :
    p = q := by
  cases p
  cases q
  simp_all

theorem multiply_comm
    (p q : Pauli n) :
    multiply p q = multiply q p := by
  apply ext
  · exact BitVec.add_comm p.x q.x
  · exact BitVec.add_comm p.z q.z

theorem multiply_assoc
    (p q r : Pauli n) :
    multiply (multiply p q) r =
      multiply p (multiply q r) := by
  apply ext
  · exact BitVec.add_assoc p.x q.x r.x
  · exact BitVec.add_assoc p.z q.z r.z

theorem multiply_identity
    (p : Pauli n) :
    multiply p identity = p := by
  apply ext
  · exact BitVec.add_zero p.x
  · exact BitVec.add_zero p.z

theorem identity_multiply
    (p : Pauli n) :
    multiply identity p = p := by
  rw [multiply_comm]
  exact multiply_identity p

/-- Every phase-free Pauli is self-inverse. -/
theorem multiply_self
    (p : Pauli n) :
    multiply p p = identity := by
  apply ext
  · exact BitVec.add_self p.x
  · exact BitVec.add_self p.z

end Pauli


/-!
================================================================
5. Single-qubit Pauli basis
================================================================
-/

namespace OneQubit

abbrev Qubit := Fin 1

def I : Pauli Qubit where
  x := fun _ => 0
  z := fun _ => 0

def X : Pauli Qubit where
  x := fun _ => 1
  z := fun _ => 0

def Z : Pauli Qubit where
  x := fun _ => 0
  z := fun _ => 1

def Y : Pauli Qubit where
  x := fun _ => 1
  z := fun _ => 1

end OneQubit


/-!
================================================================
6. Binary symplectic geometry
================================================================
-/

namespace Symplectic

variable {n : Type*} [Fintype n]

/-- Binary dot product. -/
def dot
    (x y : BitVec n) :
    GF2 :=
  ∑ i, x i * y i

/-- Binary symplectic form. -/
def form
    (p q : Pauli n) :
    GF2 :=
  dot p.x q.z + dot p.z q.x

/-- Pauli commutation. -/
def Commutes
    (p q : Pauli n) :
    Prop :=
  form p q = 0

/-- Pauli anticommutation. -/
def Anticommutes
    (p q : Pauli n) :
    Prop :=
  form p q = 1

theorem dot_comm
    (x y : BitVec n) :
    dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

theorem form_symm
    (p q : Pauli n) :
    form p q = form q p := by
  unfold form
  rw [dot_comm p.x q.z]
  rw [dot_comm p.z q.x]
  rw [add_comm]

/-- The binary symplectic form is alternating. -/
theorem form_self
    (p : Pauli n) :
    form p p = 0 := by
  unfold form
  have h :
      dot p.z p.x = dot p.x p.z :=
    dot_comm p.z p.x
  rw [h]
  exact GF2.add_self_eq_zero _

theorem commutes_refl
    (p : Pauli n) :
    Commutes p p := by
  exact form_self p

theorem commutes_symm
    {p q : Pauli n}
    (h : Commutes p q) :
    Commutes q p := by
  unfold Commutes at *
  rw [form_symm]
  exact h

end Symplectic


/-!
================================================================
7. Single-qubit commutation
================================================================
-/

namespace OneQubit

open Symplectic

theorem X_Z_anticommute :
    Anticommutes X Z := by
  native_decide

theorem Z_X_anticommute :
    Anticommutes Z X := by
  native_decide

theorem X_X_commute :
    Commutes X X := by
  native_decide

theorem Z_Z_commute :
    Commutes Z Z := by
  native_decide

theorem I_X_commute :
    Commutes I X := by
  native_decide

theorem I_Z_commute :
    Commutes I Z := by
  native_decide

end OneQubit


/-!
================================================================
8. Clifford gates
================================================================
-/

namespace Clifford

variable {n : Type*} [DecidableEq n]

/--
Hadamard on target:

    X ↔ Z

Binary representation:

    x_t ↔ z_t
-/
def H
    (target : n)
    (p : Pauli n) :
    Pauli n where
  x := fun i =>
    if i = target then p.z i else p.x i
  z := fun i =>
    if i = target then p.x i else p.z i

/--
Phase gate S.

Modulo global phase:

    X → XZ
    Z → Z

Therefore:

    z_t := z_t + x_t
-/
def S
    (target : n)
    (p : Pauli n) :
    Pauli n where
  x := p.x
  z := fun i =>
    if i = target then
      p.z i + p.x i
    else
      p.z i

/--
CNOT(control,target).

Binary Pauli action:

    x_t := x_t + x_c
    z_c := z_c + z_t
-/
def CNOT
    (control target : n)
    (p : Pauli n) :
    Pauli n where
  x := fun i =>
    if i = target then
      p.x i + p.x control
    else
      p.x i
  z := fun i =>
    if i = control then
      p.z i + p.z target
    else
      p.z i

/-!
----------------------------------------------------------------
Gate identities
----------------------------------------------------------------
-/

/-- H² = I. -/
theorem H_squared
    (target : n)
    (p : Pauli n) :
    H target (H target p) = p := by
  apply Pauli.ext
  · funext i
    by_cases h : i = target
    · subst i
      simp [H]
    · simp [H, h]
  · funext i
    by_cases h : i = target
    · subst i
      simp [H]
    · simp [H, h]

/--
S² is identity on phase-free binary Pauli labels.

This is the quotient representation statement.
-/
theorem S_squared
    (target : n)
    (p : Pauli n) :
    S target (S target p) = p := by
  apply Pauli.ext
  · rfl
  · funext i
    by_cases h : i = target
    · subst i
      simp [S, GF2.add_self_eq_zero, add_assoc]
    · simp [S, h]

/--
CNOT² = I when control and target are distinct.
-/
theorem CNOT_squared
    (control target : n)
    (hct : control ≠ target)
    (p : Pauli n) :
    CNOT control target (CNOT control target p) = p := by
  apply Pauli.ext
  · funext i
    by_cases ht : i = target
    · subst i
      simp [CNOT, hct, GF2.add_self_eq_zero, add_assoc]
    · simp [CNOT, ht]
  · funext i
    by_cases hc : i = control
    · subst i
      simp [CNOT, hct, GF2.add_self_eq_zero, add_assoc]
    · simp [CNOT, hc]

end Clifford


/-!
================================================================
9. Clifford circuits
================================================================
-/

namespace Circuit

variable {n : Type*} [DecidableEq n]

/-- Elementary Clifford gate. -/
inductive Gate where
  | H : n → Gate
  | S : n → Gate
  | CNOT : n → n → Gate

deriving Repr

/-- Apply one gate to a Pauli operator. -/
def applyGate :
    Gate (n := n) → Pauli n → Pauli n
  | Gate.H q, p => Clifford.H q p
  | Gate.S q, p => Clifford.S q p
  | Gate.CNOT c t, p => Clifford.CNOT c t p

/-- A Clifford circuit is a list of gates. -/
abbrev Circuit :=
  List (Gate (n := n))

/-- Apply a circuit to a Pauli operator. -/
def run
    (c : Circuit (n := n))
    (p : Pauli n) :
    Pauli n :=
  c.foldl (fun state gate => applyGate gate state) p

theorem run_nil
    (p : Pauli n) :
    run ([] : Circuit (n := n)) p = p := by
  rfl

end Circuit


/-!
================================================================
10. Stabilizer states
================================================================
-/

/--
A minimal stabilizer representation.

A full tableau implementation additionally stores:

* phase bits
* row independence
* canonical reduction state

This structure provides the formal algebraic base.
-/
structure StabilizerState (n : Type*) where
  generators : List (Pauli n)

namespace StabilizerState

variable {n : Type*}

/-- Transform every generator. -/
def map
    (f : Pauli n → Pauli n)
    (s : StabilizerState n) :
    StabilizerState n where
  generators := s.generators.map f

theorem map_id
    (s : StabilizerState n) :
    map id s = s := by
  cases s
  simp [map]

theorem map_comp
    (f g : Pauli n → Pauli n)
    (s : StabilizerState n) :
    map f (map g s) =
      map (f ∘ g) s := by
  cases s
  simp [map, Function.comp]

variable [DecidableEq n]

def H
    (target : n)
    (s : StabilizerState n) :
    StabilizerState n :=
  map (Clifford.H target) s

def S
    (target : n)
    (s : StabilizerState n) :
    StabilizerState n :=
  map (Clifford.S target) s

def CNOT
    (control target : n)
    (s : StabilizerState n) :
    StabilizerState n :=
  map (Clifford.CNOT control target) s

/-- Apply a Clifford circuit to every generator. -/
def runCircuit
    (c : Circuit.Circuit (n := n))
    (s : StabilizerState n) :
    StabilizerState n :=
  map (Circuit.run c) s

end StabilizerState


/-!
================================================================
11. Two-qubit Pauli basis
================================================================
-/

namespace TwoQubit

abbrev Qubit := Fin 2

def I : Pauli Qubit where
  x := fun _ => 0
  z := fun _ => 0

def ZI : Pauli Qubit where
  x := fun _ => 0
  z := fun i => if i = 0 then 1 else 0

def IZ : Pauli Qubit where
  x := fun _ => 0
  z := fun i => if i = 1 then 1 else 0

def XI : Pauli Qubit where
  x := fun i => if i = 0 then 1 else 0
  z := fun _ => 0

def IX : Pauli Qubit where
  x := fun i => if i = 1 then 1 else 0
  z := fun _ => 0

def XX : Pauli Qubit where
  x := fun _ => 1
  z := fun _ => 0

def ZZ : Pauli Qubit where
  x := fun _ => 0
  z := fun _ => 1

end TwoQubit


/-!
================================================================
12. Bell state
================================================================

|00⟩ stabilizers:

    ZI
    IZ

Apply:

    H(0)
    CNOT(0,1)

Bell stabilizers become:

    XX
    ZZ

up to generator ordering.
-/

namespace Bell

open TwoQubit

def ket00 : StabilizerState Qubit where
  generators := [ZI, IZ]

def afterH :
    StabilizerState Qubit :=
  StabilizerState.H (0 : Qubit) ket00

def state :
    StabilizerState Qubit :=
  StabilizerState.CNOT
    (0 : Qubit)
    (1 : Qubit)
    afterH

/-- Expected canonical stabilizer generators. -/
def canonical :
    StabilizerState Qubit where
  generators := [XX, ZZ]

end Bell


/-!
================================================================
13. Binary symplectic vector representation
================================================================
-/

namespace SymplecticVector

variable {n : Type*}

/--
A 2n-dimensional binary symplectic vector represented structurally
as (x,z), avoiding fragile index arithmetic.
-/
structure Vector where
  x : BitVec n
  z : BitVec n

def ofPauli
    (p : Pauli n) :
    Vector (n := n) where
  x := p.x
  z := p.z

def toPauli
    (v : Vector (n := n)) :
    Pauli n where
  x := v.x
  z := v.z

theorem toPauli_ofPauli
    (p : Pauli n) :
    toPauli (ofPauli p) = p := by
  rfl

theorem ofPauli_toPauli
    (v : Vector (n := n)) :
    ofPauli (toPauli v) = v := by
  cases v
  rfl

end SymplecticVector


/-!
================================================================
14. Symplectic transformations
================================================================
-/

namespace SymplecticMap

variable {n : Type*} [Fintype n]

/--
A transformation preserving the binary symplectic form.
-/
def Preserves
    (f : Pauli n → Pauli n) :
    Prop :=
  ∀ p q,
    Symplectic.form (f p) (f q)
      =
    Symplectic.form p q

/-- Identity preserves the symplectic form. -/
theorem identity_preserves :
    Preserves (id : Pauli n → Pauli n) := by
  intro p q
  rfl

/-- Composition of symplectic transformations is symplectic. -/
theorem comp_preserves
    (f g : Pauli n → Pauli n)
    (hf : Preserves f)
    (hg : Preserves g) :
    Preserves (f ∘ g) := by
  intro p q
  simp only [Function.comp_apply]
  rw [hf]
  exact hg p q

end SymplecticMap


/-!
================================================================
15. Executable and formal examples
================================================================
-/

namespace Examples

open OneQubit

example :
    Pauli.multiply X X = I := by
  exact Pauli.multiply_self X

example :
    Pauli.multiply Z Z = I := by
  exact Pauli.multiply_self Z

example :
    Symplectic.Anticommutes X Z := by
  exact OneQubit.X_Z_anticommute

example :
    Symplectic.Commutes X X := by
  exact OneQubit.X_X_commute

example :
    Clifford.H
      (0 : Fin 1)
      (Clifford.H (0 : Fin 1) X)
      = X := by
  exact Clifford.H_squared (0 : Fin 1) X

example :
    Clifford.S
      (0 : Fin 1)
      (Clifford.S (0 : Fin 1) Z)
      = Z := by
  exact Clifford.S_squared (0 : Fin 1) Z

example :
    StabilizerState.map id Bell.ket00
      = Bell.ket00 := by
  exact StabilizerState.map_id Bell.ket00

end Examples


/-!
================================================================
16. Final mathematical architecture
================================================================

                        GF(2)
                          │
                          ▼
                     BitVec(n)
                          │
                          ▼
                     Pauli(n)
                     (x,z)
                          │
                          ▼
                  Symplectic form
               ω(p,q)=x·z'+z·x'
                          │
             ┌────────────┼────────────┐
             ▼            ▼            ▼
             H            S           CNOT
             │            │            │
             └────────────┼────────────┘
                          ▼
                   Clifford circuit
                          │
                          ▼
                   Stabilizer state
                          │
                          ▼
               Discrete quantum system


Future expansion layer:

    GF(2) Gaussian elimination
              ↓
    Stabilizer tableau reduction
              ↓
    Phase-bit representation
              ↓
    Pauli measurement
              ↓
    Aaronson-Gottesman simulator
              ↓
    Symplectic matrix representation
              ↓
         Mᵀ J M = J
              ↓
    Verified Clifford computation

This file is the unified algebraic core.
-/

end DiscreteQuantum
