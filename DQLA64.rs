//! # Digital 64-Bit Discrete Quantum Linear Algebra
//! A GF(2) Symplectic Foundation for 64-Qubit Stabilizer Computation.
//!
//! Copyright (c) 2026 Yamamoto Takeo
//! License: Apache License 2.0

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pauli64 {
    /// Bitmask for X terms across 64 qubits.
    pub x: u64,
    /// Bitmask for Z terms across 64 qubits.
    pub z: u64,
}

impl Pauli64 {
    /// Identity operator (I^{\otimes 64}).
    #[inline]
    pub const fn identity() -> Self {
        Self { x: 0, z: 0 }
    }

    /// Single-qubit X on `qubit` (0 <= qubit < 64).
    #[inline]
    pub fn x_gate(qubit: u8) -> Self {
        debug_assert!(qubit < 64);
        Self {
            x: 1u64 << qubit,
            z: 0,
        }
    }

    /// Single-qubit Z on `qubit` (0 <= qubit < 64).
    #[inline]
    pub fn z_gate(qubit: u8) -> Self {
        debug_assert!(qubit < 64);
        Self {
            x: 0,
            z: 1u64 << qubit,
        }
    }

    /// Single-qubit Y on `qubit` (0 <= qubit < 64).
    #[inline]
    pub fn y_gate(qubit: u8) -> Self {
        debug_assert!(qubit < 64);
        let mask = 1u64 << qubit;
        Self { x: mask, z: mask }
    }

    /// Pauli multiplication modulo phase: O(1) Bitwise XOR.
    #[inline]
    pub fn multiply(self, rhs: Self) -> Self {
        Self {
            x: self.x ^ rhs.x,
            z: self.z ^ rhs.z,
        }
    }
}

/// Binary Symplectic Geometry over GF(2)^64.
impl Pauli64 {
    /// Compute the binary symplectic inner product:
    /// $\omega(p, q) = (p.x \cdot q.z + p.z \cdot q.x) \pmod 2$
    ///
    /// Evaluated in O(1) via Bitwise AND and POPCOUNT.
    #[inline]
    pub fn symplectic_form(self, other: Self) -> u8 {
        let x1_z2 = (self.x & other.z).count_ones() % 2;
        let z1_x2 = (self.z & other.x).count_ones() % 2;
        ((x1_z2 + z1_x2) % 2) as u8
    }

    /// Returns true if two Pauli operators commute.
    #[inline]
    pub fn commutes_with(self, other: Self) -> bool {
        self.symplectic_form(other) == 0
    }

    /// Returns true if two Pauli operators anticommute.
    #[inline]
    pub fn anticommutes_with(self, other: Self) -> bool {
        self.symplectic_form(other) == 1
    }
}

/// Fast Bitwise Clifford Transformations in O(1).
pub struct Clifford64;

impl Clifford64 {
    /// Hadamard gate on `target`: Swaps X bit and Z bit at target index.
    #[inline]
    pub fn h(target: u8, p: Pauli64) -> Pauli64 {
        debug_assert!(target < 64);
        let mask = 1u64 << target;
        let x_bit = (p.x & mask) >> target;
        let z_bit = (p.z & mask) >> target;

        let new_x = (p.x & !mask) | (z_bit << target);
        let new_z = (p.z & !mask) | (x_bit << target);
        Pauli64 { x: new_x, z: new_z }
    }

    /// Phase gate S on `target`: $Z_{\text{target}} \gets Z_{\text{target}} \oplus X_{\text{target}}$.
    #[inline]
    pub fn s(target: u8, p: Pauli64) -> Pauli64 {
        debug_assert!(target < 64);
        let mask = 1u64 << target;
        let x_bit = p.x & mask;
        Pauli64 {
            x: p.x,
            z: p.z ^ x_bit,
        }
    }

    /// CNOT(control, target):
    /// $X_{\text{target}} \gets X_{\text{target}} \oplus X_{\text{control}}$
    /// $Z_{\text{control}} \gets Z_{\text{control}} \oplus Z_{\text{target}}$
    #[inline]
    pub fn cnot(control: u8, target: u8, p: Pauli64) -> Pauli64 {
        debug_assert!(control < 64 && target < 64);
        let c_mask = 1u64 << control;
        let t_mask = 1u64 << target;

        let x_c = (p.x & c_mask) >> control;
        let z_t = (p.z & t_mask) >> target;

        Pauli64 {
            x: p.x ^ (x_c << target),
            z: p.z ^ (z_t << control),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_commutation() {
        let x0 = Pauli64::x_gate(0);
        let z0 = Pauli64::z_gate(0);
        let x1 = Pauli64::x_gate(1);

        assert!(x0.anticommutes_with(z0));
        assert!(x0.commutes_with(x1));
    }

    #[test]
    fn test_hadamard_involution() {
        let x0 = Pauli64::x_gate(0);
        let h_x0 = Clifford64::h(0, x0);
        assert_eq!(h_x0, Pauli64::z_gate(0));

        let hh_x0 = Clifford64::h(0, h_x0);
        assert_eq!(hh_x0, x0);
    }
}
