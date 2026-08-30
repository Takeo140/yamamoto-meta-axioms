import Mathlib

/-!
# Digital 64-Bit Discrete Quantum Linear Algebra
## Direct Bitwise UInt64 Implementation for 64-Qubit Stabilizers

Copyright (c) 2026 Yamamoto Takeo
License: Apache License 2.0
-/

namespace DigitalQuantum64

/-!
================================================================
1. Bitwise Utility (GF(2) Inner Product via UInt64)
================================================================
-/

/-- Calculate bitwise parity (sum modulo 2) of a 64-bit integer. -/
def parity64 (w : UInt64) : ZMod 2 :=
  -- Popcount (number of set bits) mod 2
  if w.popcount.toNat % 2 == 1 then 1 else 0

/-!
================================================================
2. Digital Pauli64 Representation (x, z as 64-bit words)
================================================================

A 64-qubit Pauli operator (modulo global phase) is packed into 
two 64-bit CPU registers:
- `x : UInt64` where i-th bit represents X on qubit i.
- `z : UInt64` where i-th bit represents Z on qubit i.
-/

structure Pauli64 where
  x : UInt64
  z : UInt64
  deriving DecidableEq, Repr

namespace Pauli64

/-- Identity Pauli operator (0x0, 0x0). -/
def identity : Pauli64 := ⟨0, 0⟩

/-- Single-qubit X on qubit i (0 ≤ i < 64). -/
def X (i : Fin 64) : Pauli64 :=
  ⟨(1 : UInt64) <<< i.val, 0⟩

/-- Single-qubit Z on qubit i (0 ≤ i < 64). -/
def Z (i : Fin 64) : Pauli64 :=
  ⟨0, (1 : UInt64) <<< i.val⟩

/-- Single-qubit Y on qubit i (0 ≤ i < 64). -/
def Y (i : Fin 64) : Pauli64 :=
  ⟨(1 : UInt64) <<< i.val, (1 : UInt64) <<< i.val⟩

/--
Pauli multiplication modulo phase.
Bitwise XOR on CPU: (x1 ^ x2, z1 ^ z2)
-/
def multiply (p q : Pauli64) : Pauli64 :=
  ⟨p.x ^ q.x, p.z ^ q.z⟩

theorem multiply_self (p : Pauli64) : multiply p p = identity := by
  unfold multiply identity
  have hx : p.x ^ p.x = 0 := UInt64.xor_self p.x
  have hz : p.z ^ p.z = 0 := UInt64.xor_self p.z
  rw [hx, hz]

end Pauli64

/-!
================================================================
3. O(1) Symplectic Geometry via Bitwise Operations
================================================================
-/

namespace Symplectic64

/--
Binary Symplectic Form ω(p,q) = (p.x · q.z + p.z · q.x) mod 2
Computed via Bitwise AND, Bitwise XOR, and Popcount in O(1).
-/
def form (p q : Pauli64) : ZMod 2 :=
  let x1_z2 := parity64 (p.x &&& q.z)
  let z1_x2 := parity64 (p.z &&& q.x)
  x1_z2 + z1_x2

def Commutes (p q : Pauli64) : Prop :=
  form p q = 0

def Anticommutes (p q : Pauli64) : Prop :=
  form p q = 1

end Symplectic64

/-!
================================================================
4. Fast Bitwise Clifford Transformations
================================================================
-/

namespace Clifford64

/--
Hadamard gate on qubit `target`:
Swaps x bit and z bit at index `target`.
-/
def H (target : Fin 64) (p : Pauli64) : Pauli64 :=
  let mask := (1 : UInt64) <<< target.val
  let x_bit := (p.x &&& mask) >>> target.val
  let z_bit := (p.z &&& mask) >>> target.val
  let new_x := (p.x &&& ~~~mask) ||| (z_bit <<< target.val)
  let new_z := (p.z &&& ~~~mask) ||| (x_bit <<< target.val)
  ⟨new_x, new_z⟩

/--
Phase gate S on qubit `target`:
z_target := z_target XOR x_target
-/
def S (target : Fin 64) (p : Pauli64) : Pauli64 :=
  let mask := (1 : UInt64) <<< target.val
  let x_bit := p.x &&& mask
  ⟨p.x, p.z ^ x_bit⟩

/--
CNOT(control, target):
x_target := x_target XOR x_control
z_control := z_control XOR z_target
-/
def CNOT (control target : Fin 64) (p : Pauli64) : Pauli64 :=
  let c_mask := (1 : UInt64) <<< control.val
  let t_mask := (1 : UInt64) <<< target.val
  
  let x_c := (p.x &&& c_mask) >>> control.val
  let z_t := (p.z &&& t_mask) >>> target.val
  
  let new_x := p.x ^ (x_c <<< target.val)
  let new_z := p.z ^ (z_t <<< control.val)
  ⟨new_x, new_z⟩

end Clifford64

end DigitalQuantum64
