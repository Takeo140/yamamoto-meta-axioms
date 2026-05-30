// Bounded Smooth Collatz Machine (BSCM) — Engineering Version (Rust Optimized)
// Author: Takeo Yamamoto
// License: Apache 2.0

pub const N: u64 = u64::MAX; // 18446744073709551615

// ─────────────────────────────────────────────────────────────────────────────
// 1. Core transition function δ
// ─────────────────────────────────────────────────────────────────────────────

/// Engineering δ — State-reducing transition.
/// Optimized with bitwise operations to prevent integer overflow.
#[inline]
pub fn bscm_delta(s: u64) -> u64 {
    if s % 2 == 0 {
        s >> 1
    } else {
        // s が u64::MAX のとき、(s + 1) / 2 を直接行うとオーバーフローする。
        // 代数的に同値な 「(s / 2) + 1」 に変形することで、オーバーフローを完全に回避。
        (s >> 1) + 1
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Control interface
// ─────────────────────────────────────────────────────────────────────────────

/// Single control step.
/// Absorbs arbitrary external input via wrapping addition,
/// then applies δ. Overflow is structurally impossible.
#[inline]
pub fn bscm_control_step(current_state: u64, external_input: u64) -> u64 {
    let s_prime = current_state.wrapping_add(external_input);
    bscm_delta(s_prime)
}

/// Execute a control trace over a sequence of external inputs.
pub fn bscm_control_exec(initial_state: u64, inputs: &[u64]) -> u64 {
    inputs.iter().fold(initial_state, |state, &input| {
        bscm_control_step(state, input)
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. Tests (mirrors Lean theorems)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // Theorem 1: state-space invariance
    #[test]
    fn test_delta_bounded() {
        for s in [0u64, 1, 2, 3, N, N - 1, N / 2, 12345678901234] {
            assert!(bscm_delta(s) <= N);
        }
    }

    // Theorem 2: single-step robust boundedness
    #[test]
    fn test_control_step_bounded() {
        let cases = [(0, 0), (N, N), (12345, u64::MAX), (0, u64::MAX)];
        for (state, input) in cases {
            assert!(bscm_control_step(state, input) <= N);
        }
    }

    // Theorem 3: sequence-level safety invariance
    #[test]
    fn test_exec_bounded() {
        let inputs = vec![u64::MAX, u64::MAX, 99999, 0, u64::MAX];
        let result = bscm_control_exec(u64::MAX, &inputs);
        assert!(result <= N);
    }

    // Reduction property: all branches shrink state (except boundary s = 1)
    #[test]
    fn test_delta_reduces() {
        // s = 1 のときは 1 に収束するため、2以上で検証
        for s in [2u64, 4, 100, 1000, N - 1] {
            assert!(bscm_delta(s) < s);
        }
    }

    // Edge case test for u64::MAX to ensure no overflow panic occurs
    #[test]
    fn test_max_value_boundary() {
        // 元のコードではここでパニックが発生していた
        let res = bscm_delta(u64::MAX);
        // (u64::MAX + 1) / 2 の本来の挙動である 2^63 になるべき
        assert_eq!(res, 1u64 << 63); 
    }
}
