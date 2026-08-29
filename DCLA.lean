License Apache 2.0 Takeo Yamamoto
import Mathlib/Data/Complex.Basic
import Mathlib/LinearAlgebra/Matrix
import Mathlib/LinearAlgebra/FiniteDimensional
import Mathlib/Data/Fin.Basic

/-!
  Discrete complex linear algebra over classical bits and finite index sets.

  - Classical bit: `Bit := Fin 2`
  - Discrete complex vector space: `DCVec n := Fin n → ℂ`
  - Linear operators: `LinOp n := Matrix (Fin n) (Fin n) ℂ`
-/

namespace DiscreteComplexLA

/-- Classical bit as `Fin 2` (0 or 1). -/
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

/-- Standard module structure: pointwise addition and scalar multiplication. -/
instance instAddDCVec (n : ℕ) : Add (DCVec n) := by
  infer_instance

instance instSubDCVec (n : ℕ) : Sub (DCVec n) := by
  infer_instance

instance instSMulDCVec (n : ℕ) : SMul ℂ (DCVec n) := by
  infer_instance

instance instInstModuleDCVec (n : ℕ) : Module ℂ (DCVec n) := by
  infer_instance

/-- Finite-dimensionality: `Fin n` is finite, so `DCVec n` is finite-dimensional over ℂ. -/
instance instFiniteDimensionalDCVec (n : ℕ) :
    FiniteDimensional ℂ (DCVec n) := by
  infer_instance

/-- Dirac delta basis vector at index `i`. -/
def basisVec {n : ℕ} (i : Fin n) : DCVec n :=
  fun j => if h : j = i then 1 else 0

/-- Classical bit states as discrete complex vectors in dimension 2. -/
def ket0 : DCVec 2 :=
  basisVec 0

def ket1 : DCVec 2 :=
  basisVec 1

/-- "Imaginary-weighted" classical bit states. -/
def Iket0 : DCVec 2 :=
  fun j => Complex.I * ket0 j

def Iket1 : DCVec 2 :=
  fun j => Complex.I * ket1 j

/-- Action of a linear operator (matrix) on a discrete complex vector. -/
def applyLinOp {n : ℕ} (A : LinOp n) (v : DCVec n) : DCVec n :=
  fun i => Matrix.mulVec A v i

/-- Identity operator on `DCVec n`. -/
def idOp (n : ℕ) : LinOp n :=
  Matrix.identity _

/-- Composition of linear operators via matrix multiplication. -/
def compOp {n : ℕ} (A B : LinOp n) : LinOp n :=
  A ⬝ B

/-- Example: Pauli-X (bit flip) on 2-dimensional discrete complex space. -/
def pauliX : LinOp 2 :=
  ![![0, 1],
    ![1, 0]]

/-- Example: Pauli-Z (phase flip) on 2-dimensional discrete complex space. -/
def pauliZ : LinOp 2 :=
  ![![1, 0],
    ![0, -1]]

/-- Pauli-X flips `ket0` to `ket1`. -/
lemma pauliX_ket0 :
    applyLinOp pauliX ket0 = ket1 := by
  funext i
  fin_cases i <;> simp [applyLinOp, pauliX, ket0, ket1, basisVec]

/-- Pauli-X flips `ket1` to `ket0`. -/
lemma pauliX_ket1 :
    applyLinOp pauliX ket1 = ket0 := by
  funext i
  fin_cases i <;> simp [applyLinOp, pauliX, ket0, ket1, basisVec]

/-- Pauli-Z adds a minus sign to `ket1` but leaves `ket0` unchanged. -/
lemma pauliZ_ket0 :
    applyLinOp pauliZ ket0 = ket0 := by
  funext i
  fin_cases i <;> simp [applyLinOp, pauliZ, ket0, basisVec]

lemma pauliZ_ket1 :
    applyLinOp pauliZ ket1 = fun j => if j = 0 then 0 else -1 := by
  funext i
  fin_cases i <;> simp [applyLinOp, pauliZ, ket1, basisVec]

/-- Inner product on `DCVec n` as discrete sum over `Fin n`. -/
def inner {n : ℕ} (v w : DCVec n) : ℂ :=
  ∑ i : Fin n, Complex.conj (v i) * w i

/-- Norm squared of a discrete complex vector. -/
def normSq {n : ℕ} (v : DCVec n) : ℂ :=
  inner v v

/-- Orthonormality of basis vectors (discrete Kronecker delta). -/
lemma inner_basisVec {n : ℕ} (i j : Fin n) :
    inner (basisVec i) (basisVec j) =
      (if i = j then 1 else 0) := by
  classical
  unfold inner basisVec
  by_cases h : i = j
  · subst h
    simp
  · have : (∑ k : Fin n, (if k = j then (1 : ℂ) else 0) * (if k = j then (1 : ℂ) else 0))
        = 1 := by
        classical
        simp
    -- for i ≠ j, the product is zero everywhere
    simp [h]

end DiscreteComplexLA
