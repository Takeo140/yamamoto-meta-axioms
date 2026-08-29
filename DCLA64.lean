License Apache 2.0 Takeo Yamamoto

import Mathlib/Data/Complex.Basic
import Mathlib/LinearAlgebra/Matrix
import Mathlib/Data/Fin.VecNotation

/-!
  Discrete complex linear algebra over `Fin n` with explicit 64-dimensional example.
-/

namespace DiscreteComplexLA

/-- Classical bit as `Fin 2`. -/
abbrev Bit : Type := Fin 2

/-- Embed a classical bit into ℂ as 0 or 1. -/
def bitToC (b : Bit) : ℂ :=
  (b.val : ℂ)

/-- "Imaginary bit": multiply the classical bit value by `I`. -/
def Ibit (b : Bit) : ℂ :=
  Complex.I * bitToC b

/-- Discrete complex vector space of length `n`: functions `Fin n → ℂ`. -/
abbrev DCVec (n : ℕ) : Type := Fin n → ℂ

/-- Linear operators on `DCVec n` as `n × n` complex matrices. -/
abbrev LinOp (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℂ

/-- Dirac delta basis vector at index `i`. -/
def basisVec {n : ℕ} (i : Fin n) : DCVec n :=
  fun j => if h : j = i then 1 else 0

/-- Inner product on `DCVec n` as discrete sum over `Fin n`. -/
def inner {n : ℕ} (v w : DCVec n) : ℂ :=
  ∑ i : Fin n, Complex.conj (v i) * w i

/-- Norm squared of a discrete complex vector. -/
def normSq {n : ℕ} (v : DCVec n) : ℂ :=
  inner v v

/-- 64-dimensional discrete complex vector space. -/
abbrev DCVec64 : Type := DCVec 64

/-- 64×64 complex linear operators. -/
abbrev LinOp64 : Type := LinOp 64

/-- 標準基底の一つを 64 次元で取る例。 -/
def basis64 (i : Fin 64) : DCVec64 :=
  basisVec i

/-- 64 次元の恒等作用素。 -/
def id64 : LinOp64 :=
  Matrix.identity _

/-- 線形作用素の作用。 -/
def apply64 (A : LinOp64) (v : DCVec64) : DCVec64 :=
  fun i => Matrix.mulVec A v i

end DiscreteComplexLA
