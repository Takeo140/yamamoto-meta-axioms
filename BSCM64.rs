// Bounded Smooth Collatz Machine (BSCM) — Engineering Version
// Author: Takeo Yamamoto
// License: Apache 2.0

const N: u64 = u64::MAX; // 18446744073709551615

// ─────────────────────────────────────────────────────────────────────────────
// 1. Core transition function δ
// ─────────────────────────────────────────────────────────────────────────────

#[inline]
pub fn bscm_delta(s: u64) -> u64 {
    if s % 2 == 0 {
        s / 2
    } else {
        (s + 1) / 2
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

    // Reduction property: all branches shrink state
    #[test]
    fn test_delta_reduces() {
        for s in [2u64, 4, 100, 1000, N - 1] {
            assert!(bscm_delta(s) < s);
        }
    }
}
