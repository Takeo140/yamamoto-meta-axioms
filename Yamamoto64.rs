/// Yamamoto-64: Occam-Meta Kernel
/// Author: Takeo Yamamoto
/// License: Apache-2.0
///
/// 64ビット環境向け計算理論基盤。
/// 記述長(K)を最小化する不動点(Fixed Point)計算理論。
/// Lean4形式証明済みカーネルのRust移植。

const THRESHOLD_VAL: u64 = 0x7FFFFFFFFFFFFFFF;
const THRESHOLD_POT: u64 = 0x3FFFFFFFFFFFFFFF;

/// Lean4: structure State64
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct State64 {
    pub val: u64,
    pub pot: u64,
    pub is_stable: bool, // 拡張予約フィールド
}

/// Lean4: def complexity (s : State64) : UInt64 := s.val ^^^ s.pot
#[inline]
pub fn complexity(s: &State64) -> u64 {
    s.val ^ s.pot
}

/// Lean4: def resolve_64 (s : State64) : State64
/// 証明済み性質:
///   - is_fixed_point: resolve(resolve(s)) == resolve(s)
///   - is_minimal:     complexity(resolve(s)) <= complexity(s)
#[inline]
pub fn resolve_64(s: State64) -> State64 {
    if s.val > THRESHOLD_VAL || s.pot > THRESHOLD_POT {
        State64 { val: 0, pot: 0, is_stable: true }
    } else {
        State64 { is_stable: true, ..s }
    }
}

/// Lean4: structure OccamMetaSystem
pub struct OccamMetaSystem {
    pub resolve: fn(State64) -> State64,
}

/// Lean4: def GlobalOccam64
pub const GLOBAL_OCCAM_64: OccamMetaSystem = OccamMetaSystem {
    resolve: resolve_64,
};

// --- ランタイムアサート（Lean4証明のミラー） ---

/// is_fixed_point: resolve(resolve(s)) == resolve(s)
#[cfg(debug_assertions)]
pub fn assert_fixed_point(s: State64) {
    let r = resolve_64(s);
    let rr = resolve_64(r);
    debug_assert_eq!(r, rr, "fixed point violation: {s:?}");
}

/// is_minimal: complexity(resolve(s)) <= complexity(s)
#[cfg(debug_assertions)]
pub fn assert_minimal(s: State64) {
    debug_assert!(
        complexity(&resolve_64(s)) <= complexity(&s),
        "minimality violation: {s:?}"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fixed_point_over_threshold() {
        let s = State64 { val: u64::MAX, pot: u64::MAX, is_stable: false };
        let r = resolve_64(s);
        assert_eq!(resolve_64(r), r);
        assert_eq!(r.val, 0);
        assert_eq!(r.pot, 0);
        assert!(r.is_stable);
    }

    #[test]
    fn test_fixed_point_under_threshold() {
        let s = State64 { val: 100, pot: 200, is_stable: false };
        let r = resolve_64(s);
        assert_eq!(resolve_64(r), r);
        assert_eq!(r.val, 100);
        assert_eq!(r.pot, 200);
        assert!(r.is_stable);
    }

    #[test]
    fn test_minimality_over_threshold() {
        let s = State64 { val: u64::MAX, pot: u64::MAX, is_stable: false };
        assert!(complexity(&resolve_64(s)) <= complexity(&s));
    }

    #[test]
    fn test_minimality_under_threshold() {
        let s = State64 { val: 0xABCD, pot: 0x1234, is_stable: false };
        assert_eq!(complexity(&resolve_64(s)), complexity(&s));
    }

    #[test]
    fn test_complexity_xor() {
        let s = State64 { val: 0xFF00, pot: 0x00FF, is_stable: false };
        assert_eq!(complexity(&s), 0xFFFF);
        // val == pot のとき complexity = 0（最小）
        let s2 = State64 { val: 42, pot: 42, is_stable: false };
        assert_eq!(complexity(&s2), 0);
    }
}
