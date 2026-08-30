import Mathlib

/-!
# Discrete Quantum Linear Algebra
# 離散型線形代数による量子計算

GF(2) = ZMod 2 を基礎とし、

* GF(2)^n 上のベクトル
* Pauli 演算子の (x,z) 表現
* 離散シンプレクティック形式
* 可換性・反可換性
* Hadamard
* Phase
* CNOT
* Stabilizer generators
* Bell state construction

を単一ファイルで定義する。

Copyright (c) 2026 Yamamoto Takeo
License: Apache License 2.0
-/


namespace DiscreteQuantum


/-!
============================================================
1. GF(2)
============================================================
-/


abbrev GF2 := ZMod 2


namespace GF2


/-- GF(2) addition. -/
def add (a b : GF2) : GF2 :=
  a + b


/-- GF(2) multiplication. -/
def mul (a b : GF2) : GF2 :=
  a * b


/-- Characteristic two: a + a = 0. -/
theorem self_add_zero (a : GF2) :
    a + a = 0 := by
  exact add_self a


/-- Every element is its own additive inverse. -/
theorem neg_eq_self (a : GF2) :
    -a = a := by
  have h : a + a = 0 := self_add_zero a
  omega


end GF2


/-!
============================================================
2. GF(2) Vectors
============================================================
-/


abbrev GF2Vector (n : Type*) :=
  n → GF2


namespace GF2Vector


variable {n : Type*}


/-- Zero vector. -/
def zero : GF2Vector n :=
  fun _ => 0


/-- Vector addition. -/
def add
    (x y : GF2Vector n) :
    GF2Vector n :=
  fun i => x i + y i


/-- Scalar multiplication. -/
def smul
    (a : GF2)
    (x : GF2Vector n) :
    GF2Vector n :=
  fun i => a * x i


theorem add_apply
    (x y : GF2Vector n)
    (i : n) :
    add x y i = x i + y i :=
  rfl


theorem add_comm
    (x y : GF2Vector n) :
    add x y = add y x := by
  funext i
  exact add_comm (x i) (y i)


theorem add_assoc
    (x y z : GF2Vector n) :
    add (add x y) z =
      add x (add y z) := by
  funext i
  simp [add, add_assoc]


theorem add_zero
    (x : GF2Vector n) :
    add x zero = x := by
  funext i
  simp [add, zero]


theorem zero_add
    (x : GF2Vector n) :
    add zero x = x := by
  funext i
  simp [add, zero]


theorem self_add_zero
    (x : GF2Vector n) :
    add x x = zero := by
  funext i
  simp [add, zero, GF2.self_add_zero]


end GF2Vector


/-!
============================================================
3. GF(2) Matrices
============================================================
-/


abbrev GF2Matrix
    (m n : Type*) :=
  Matrix m n GF2


namespace GF2Matrix


variable
  {m n k : Type*}
  [Fintype n]


/-- Matrix-vector multiplication over GF(2). -/
def mulVec
    (A : GF2Matrix m n)
    (x : GF2Vector n) :
    GF2Vector m :=
  fun i => ∑ j, A i j * x j


/-- Matrix multiplication. -/
def multiply
    (A : GF2Matrix m n)
    (B : GF2Matrix n k) :
    GF2Matrix m k :=
  fun i j => ∑ l, A i l * B l j


/-- Matrix transpose. -/
def transpose
    (A : GF2Matrix m n) :
    GF2Matrix n m :=
  fun i j => A j i


theorem transpose_apply
    (A : GF2Matrix m n)
    (i : n)
    (j : m) :
    transpose A i j = A j i :=
  rfl


end GF2Matrix


/-!
============================================================
4. Pauli Operators
============================================================

A Pauli operator modulo global phase is represented as

    (x,z)

where

    x,z : GF(2)^n

For each qubit:

    I = (0,0)
    X = (1,0)
    Z = (0,1)
    Y = (1,1)
-/


structure Pauli (n : Type*) where
  x : GF2Vector n
  z : GF2Vector n


namespace Pauli


variable {n : Type*}


/-- Identity Pauli operator. -/
def identity : Pauli n where
  x := GF2Vector.zero
  z := GF2Vector.zero


/-- Phase-free multiplication of Pauli operators. -/
def multiply
    (p q : Pauli n) :
    Pauli n where

  x := GF2Vector.add p.x q.x
  z := GF2Vector.add p.z q.z


/-- Coordinate extensionality. -/
@[ext]
theorem ext
    {p q : Pauli n}
    (hx : p.x = q.x)
    (hz : p.z = q.z) :
    p = q := by
  cases p
  cases q
  simp_all


/-- Pauli multiplication is commutative after quotienting phase. -/
theorem multiply_comm
    (p q : Pauli n) :
    multiply p q = multiply q p := by

  apply ext
  · exact GF2Vector.add_comm p.x q.x
  · exact GF2Vector.add_comm p.z q.z


theorem multiply_assoc
    (p q r : Pauli n) :
    multiply (multiply p q) r =
      multiply p (multiply q r) := by

  apply ext
  · exact GF2Vector.add_assoc p.x q.x r.x
  · exact GF2Vector.add_assoc p.z q.z r.z


theorem multiply_identity
    (p : Pauli n) :
    multiply p identity = p := by

  apply ext
  · exact GF2Vector.add_zero p.x
  · exact GF2Vector.add_zero p.z


theorem identity_multiply
    (p : Pauli n) :
    multiply identity p = p := by

  rw [multiply_comm]
  exact multiply_identity p


/-- Every phase-free Pauli squares to identity. -/
theorem multiply_self
    (p : Pauli n) :
    multiply p p = identity := by

  apply ext
  · exact GF2Vector.self_add_zero p.x
  · exact GF2Vector.self_add_zero p.z


end Pauli


/-!
============================================================
5. Single Qubit Pauli Basis
============================================================
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
============================================================
6. Binary Symplectic Geometry
============================================================

For

    p = (x,z)
    q = (x',z')

define

    ω(p,q)
      = x·z' + z·x'

over GF(2).

ω = 0  → commute
ω = 1  → anticommute
-/


namespace Symplectic


open scoped BigOperators


variable
  {n : Type*}
  [Fintype n]


/-- Dot product over GF(2). -/
def dot
    (x y : GF2Vector n) :
    GF2 :=
  ∑ i, x i * y i


/-- Binary symplectic form. -/
def form
    (p q : Pauli n) :
    GF2 :=
  dot p.x q.z +
  dot p.z q.x


/-- Commutation predicate. -/
def Commutes
    (p q : Pauli n) :
    Prop :=
  form p q = 0


/-- Anticommutation predicate. -/
def Anticommutes
    (p q : Pauli n) :
    Prop :=
  form p q = 1


theorem dot_comm
    (x y : GF2Vector n) :
    dot x y = dot y x := by

  simp only [dot]

  apply Finset.sum_congr rfl

  intro i hi

  exact mul_comm _ _


theorem form_symm
    (p q : Pauli n) :
    form p q = form q p := by

  simp [form, dot_comm, add_comm]


/-- The binary symplectic form is alternating. -/
theorem form_self
    (p : Pauli n) :
    form p p = 0 := by

  unfold form

  have h :
      dot p.x p.z =
      dot p.z p.x :=
    dot_comm p.x p.z

  rw [h]

  exact GF2.self_add_zero _


theorem commutes_refl
    (p : Pauli n) :
    Commutes p p := by

  exact form_self p


theorem commutes_symm
    {p q : Pauli n}
    (h : Commutes p q) :
    Commutes q p := by

  unfold Commutes at *

  rw [← form_symm p q]

  exact h


end Symplectic


/-!
============================================================
7. Explicit Single-Qubit Commutation Theorems
============================================================
-/


namespace OneQubit


open Symplectic


theorem X_Z_anticommute :
    Anticommutes X Z := by
  decide


theorem Z_X_anticommute :
    Anticommutes Z X := by
  decide


theorem X_X_commute :
    Commutes X X := by
  decide


theorem Z_Z_commute :
    Commutes Z Z := by
  decide


theorem I_X_commute :
    Commutes I X := by
  decide


theorem I_Z_commute :
    Commutes I Z := by
  decide


end OneQubit


/-!
============================================================
8. Clifford Gates
============================================================

Binary actions on Pauli coordinates.
-/


namespace Clifford


variable
  {n : Type*}
  [DecidableEq n]


/-!
------------------------------------------------------------
Hadamard

H:

    X ↔ Z

Therefore

    (x,z) ↦ (z,x)

on the target qubit.
------------------------------------------------------------
-/


def hadamard
    (target : n)
    (p : Pauli n) :
    Pauli n where

  x := fun i =>
    if i = target then
      p.z i
    else
      p.x i

  z := fun i =>
    if i = target then
      p.x i
    else
      p.z i


/-!
------------------------------------------------------------
Phase gate S

    X → XZ
    Z → Z

Therefore:

    z := z + x

on the target.
------------------------------------------------------------
-/


def phase
    (target : n)
    (p : Pauli n) :
    Pauli n where

  x := p.x

  z := fun i =>
    if i = target then
      p.z i + p.x i
    else
      p.z i


/-!
------------------------------------------------------------
CNOT

Control c
Target  t

    x_t := x_t + x_c
    z_c := z_c + z_t
------------------------------------------------------------
-/


def cnot
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
============================================================
9. Clifford Gate Theorems
============================================================
-/


/-- H² = I. -/
theorem hadamard_squared
    (target : n)
    (p : Pauli n) :
    hadamard target
      (hadamard target p) = p := by

  apply Pauli.ext

  · funext i

    by_cases h : i = target

    · subst i
      simp [hadamard]

    · simp [hadamard, h]

  · funext i

    by_cases h : i = target

    · subst i
      simp [hadamard]

    · simp [hadamard, h]


/-!
In the phase-free binary Pauli representation,

    S² = I

because Z₂ phases are being quotiented out.
-/


theorem phase_squared
    (target : n)
    (p : Pauli n) :
    phase target
      (phase target p) = p := by

  apply Pauli.ext

  · rfl

  · funext i

    by_cases h : i = target

    · subst i

      simp only [phase, dif_pos]

      rw [← add_assoc]

      have hx :
          p.x target + p.x target = 0 :=
        GF2.self_add_zero _

      rw [hx, add_zero]

    · simp [phase, h]


/-- CNOT preserves every non-target X coordinate. -/
theorem cnot_x_other
    (control target i : n)
    (h : i ≠ target)
    (p : Pauli n) :
    (cnot control target p).x i = p.x i := by

  simp [cnot, h]


/-- CNOT preserves every non-control Z coordinate. -/
theorem cnot_z_other
    (control target i : n)
    (h : i ≠ control)
    (p : Pauli n) :
    (cnot control target p).z i = p.z i := by

  simp [cnot, h]


end Clifford


/-!
============================================================
10. Stabilizer States
============================================================

A stabilizer state is represented here by a list
of Pauli generators.

This is the algebraic core.

A complete measurement engine would additionally
require:

* generator independence
* commutation invariants
* phase bits
* tableau row operations
-/


structure StabilizerState (n : Type*) where
  generators : List (Pauli n)


namespace StabilizerState


variable {n : Type*}


/-- Map a transformation over all stabilizer generators. -/
def map
    (f : Pauli n → Pauli n)
    (s : StabilizerState n) :
    StabilizerState n where

  generators :=
    s.generators.map f


theorem map_identity
    (s : StabilizerState n) :
    map id s = s := by

  cases s with
  | mk generators =>
      simp [map]


theorem map_comp
    (f g : Pauli n → Pauli n)
    (s : StabilizerState n) :
    map f (map g s)
      =
    map (f ∘ g) s := by

  cases s with
  | mk generators =>
      simp [map, Function.comp]


namespace Gates


variable [DecidableEq n]


def hadamard
    (target : n)
    (s : StabilizerState n) :
    StabilizerState n :=

  map
    (Clifford.hadamard target)
    s


def phase
    (target : n)
    (s : StabilizerState n) :
    StabilizerState n :=

  map
    (Clifford.phase target)
    s


def cnot
    (control target : n)
    (s : StabilizerState n) :
    StabilizerState n :=

  map
    (Clifford.cnot control target)
    s


end Gates


end StabilizerState


/-!
============================================================
11. Two-Qubit System
============================================================
-/


namespace TwoQubit


abbrev Qubit := Fin 2


def zeroVector :
    GF2Vector Qubit :=
  fun _ => 0


/-- Z ⊗ I. -/
def ZI : Pauli Qubit where

  x := fun _ => 0

  z := fun i =>
    if i = 0 then
      1
    else
      0


/-- I ⊗ Z. -/
def IZ : Pauli Qubit where

  x := fun _ => 0

  z := fun i =>
    if i = 1 then
      1
    else
      0


/-- X ⊗ I. -/
def XI : Pauli Qubit where

  x := fun i =>
    if i = 0 then
      1
    else
      0

  z := fun _ => 0


/-- I ⊗ X. -/
def IX : Pauli Qubit where

  x := fun i =>
    if i = 1 then
      1
    else
      0

  z := fun _ => 0


/-- X ⊗ X. -/
def XX : Pauli Qubit where

  x := fun _ => 1

  z := fun _ => 0


/-- Z ⊗ Z. -/
def ZZ : Pauli Qubit where

  x := fun _ => 0

  z := fun _ => 1


end TwoQubit


/-!
============================================================
12. Bell State Construction
============================================================

Start:

    |00>

Stabilizers:

    ZI
    IZ

Apply:

    H(0)
    CNOT(0,1)

Resulting Bell state stabilizer generators:

    XX
    ZZ

up to generator ordering.
-/


namespace BellState


open TwoQubit


/-- Stabilizer generators for |00⟩. -/
def ket00 :
    StabilizerState Qubit where

  generators :=
    [ZI, IZ]


/-- Apply H to qubit 0. -/
def afterH :
    StabilizerState Qubit :=

  StabilizerState.Gates.hadamard
    (0 : Qubit)
    ket00


/-- Apply CNOT(0,1). -/
def bell :
    StabilizerState Qubit :=

  StabilizerState.Gates.cnot
    (0 : Qubit)
    (1 : Qubit)
    afterH


end BellState


/-!
============================================================
13. Executable Examples
============================================================
-/


namespace Examples


open OneQubit


example :
    Pauli.multiply X X = I := by

  apply Pauli.ext

  · funext i
    fin_cases i
    simp [Pauli.multiply, X, I]

  · funext i
    fin_cases i
    simp [Pauli.multiply, X, I]


example :
    Pauli.multiply Z Z = I := by

  apply Pauli.ext

  · funext i
    fin_cases i
    simp [Pauli.multiply, Z, I]

  · funext i
    fin_cases i
    simp [Pauli.multiply, Z, I]


example :
    Symplectic.Anticommutes X Z := by
  exact OneQubit.X_Z_anticommute


example :
    Symplectic.Commutes X X := by
  exact OneQubit.X_X_commute


example :
    Symplectic.Commutes Z Z := by
  exact OneQubit.Z_Z_commute


example :
    Clifford.hadamard
      (0 : Fin 1)
      (
        Clifford.hadamard
          (0 : Fin 1)
          X
      )
      =
    X := by

  exact
    Clifford.hadamard_squared
      (0 : Fin 1)
      X


example :
    Clifford.phase
      (0 : Fin 1)
      (
        Clifford.phase
          (0 : Fin 1)
          Z
      )
      =
    Z := by

  exact
    Clifford.phase_squared
      (0 : Fin 1)
      Z


example :
    StabilizerState.map id
      BellState.ket00
      =
    BellState.ket00 := by

  exact
    StabilizerState.map_identity
      BellState.ket00


end Examples


/-!
============================================================
14. Mathematical Summary
============================================================

The construction implemented above is:

                    GF(2)
                       │
                       ▼
                  GF(2)^n
                       │
                       ▼
            Pauli = GF(2)^n × GF(2)^n
                       │
                       ▼
              Binary symplectic form

        ω((x,z),(x',z'))
          = x·z' + z·x'

                       │
          ┌────────────┼────────────┐
          ▼            ▼            ▼

        H gate       S gate       CNOT

          │            │            │
          └────────────┼────────────┘
                       ▼

               Clifford operations
                       │
                       ▼

             Stabilizer generators
                       │
                       ▼

              Discrete quantum system


============================================================
15. Future Extension Interface
============================================================

The next mathematically complete layer is:

1. Full Matrix representation of Clifford maps:

       M : GF(2)^(2n) → GF(2)^(2n)

2. Standard symplectic matrix:

           J = [0 I]
               [I 0]

3. Proof:

           Mᵀ J M = J

4. Stabilizer tableau including phase bits.

5. Measurement algorithm.

6. Gaussian elimination over GF(2).

7. Aaronson-Gottesman style tableau simulation.

This file establishes the algebraic core required
for those extensions.
-/


end DiscreteQuantum
