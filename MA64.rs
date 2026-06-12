License Apache 2.0 Takeo Yamamoto

// meta_axioms64.rs
// MetaAxioms64v3.lean の Rust 実装
// Lean 型との対応は各コメントに記載

use std::fmt;

// ─────────────────────────────────────────────────
// 基本型
// Lean: abbrev Word := BitVec 64
// Lean: abbrev Cost := ℝ
// ─────────────────────────────────────────────────

pub type Word = u64;
pub type Cost = f64;

/// Lean: abbrev Instruction := Word → Word × Cost
pub type Instruction = fn(Word) -> (Word, Cost);

// ─────────────────────────────────────────────────
// MachineState
// Lean: structure MachineState where word : Word; cost : Cost
// ─────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MachineState {
    pub word: Word,
    pub cost: Cost,
}

impl MachineState {
    pub fn new(word: Word) -> Self {
        Self { word, cost: 0.0 }
    }
}

impl fmt::Display for MachineState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MachineState {{ word: 0x{:016x}, cost: {:.4} }}", self.word, self.cost)
    }
}

// ─────────────────────────────────────────────────
// A2: Hamming距離
// Lean: def hammingDist (x y : Word) : ℕ := (x ^^^ y).popcount
// ─────────────────────────────────────────────────

/// Lean: hammingDist
#[inline]
pub fn hamming_dist(x: Word, y: Word) -> u32 {
    (x ^ y).count_ones()
}

// ─────────────────────────────────────────────────
// A1: コスト最小点チェック（有限集合上で近似検証）
// Lean: def IsMinimalWord (cost : Word → Cost) (x₀ : Word) : Prop
// 注意：全 u64 を列挙不可。入力集合 S 上で検証する。
// ─────────────────────────────────────────────────

/// Lean: IsMinimalWord（有限集合 S 上の近似版）
pub fn is_minimal_on(cost: impl Fn(Word) -> Cost, x0: Word, candidates: &[Word]) -> bool {
    let c0 = cost(x0);
    candidates.iter().all(|&x| c0 <= cost(x))
}

// ─────────────────────────────────────────────────
// A2: Hamming連続性チェック（サンプリングベース）
// Lean: def HammingContinuous (cost : Word → Cost) (ε : Cost) : Prop
// ─────────────────────────────────────────────────

/// Lean: HammingContinuous（サンプル集合上で検証）
/// x の全1ビットフリップ近傍（64点）に対してチェック
pub fn check_hamming_continuous(
    cost: impl Fn(Word) -> Cost,
    samples: &[Word],
    eps: Cost,
) -> bool {
    for &x in samples {
        let cx = cost(x);
        for bit in 0u32..64 {
            let y = x ^ (1u64 << bit);
            let cy = cost(y);
            if (cx - cy).abs() > eps {
                return false;
            }
        }
    }
    true
}

// ─────────────────────────────────────────────────
// A4: 命令列実行エンジン
// Lean: def runInstructions (insns : List Instruction) (w₀ : Word) : MachineState
// ─────────────────────────────────────────────────

/// Lean: runInstructions
/// Lemma 3（結合性）・Lemma 4（コスト非負性）の仕様に従う
pub fn run_instructions(insns: &[Instruction], w0: Word) -> MachineState {
    let mut state = MachineState::new(w0);
    for &insn in insns {
        let (w_new, c_new) = insn(state.word);
        state.word = w_new;
        state.cost += c_new;
    }
    state
}

// ─────────────────────────────────────────────────
// Program 構造体
// Lean: structure Program (ι : Type) [Fintype ι] where
// ─────────────────────────────────────────────────

pub struct Program {
    pub insns: Vec<Instruction>,
}

impl Program {
    /// Lean: hNonempty の対応：空プログラムは作れない
    pub fn new(insns: Vec<Instruction>) -> Result<Self, &'static str> {
        if insns.is_empty() {
            Err("Program must have at least one instruction (hNonempty)")
        } else {
            Ok(Self { insns })
        }
    }

    /// Lean: runProgram
    pub fn run(&self, w0: Word) -> MachineState {
        run_instructions(&self.insns, w0)
    }
}

// ─────────────────────────────────────────────────
// A3: 決定性テスト
// Lean: IsDeterministic F G S
// ─────────────────────────────────────────────────

/// Lean: IsDeterministic（有限入力集合上で2実装を比較）
pub fn assert_deterministic<F, G>(f: F, g: G, inputs: &[Word]) -> bool
where
    F: Fn(Word) -> (Word, Cost),
    G: Fn(Word) -> (Word, Cost),
{
    inputs.iter().all(|&x| f(x) == g(x))
}

// ─────────────────────────────────────────────────
// Lemma 2 の対応：Hamming近傍コスト上界の実行時チェック
// Lean: neighbor_cost_bound
// ─────────────────────────────────────────────────

/// x0 の全Hamming-1近傍に対して cost(y) <= cost(x0) + eps を検証
pub fn verify_neighbor_cost_bound(
    cost: impl Fn(Word) -> Cost,
    x0: Word,
    eps: Cost,
) -> bool {
    let c0 = cost(x0);
    for bit in 0u32..64 {
        let y = x0 ^ (1u64 << bit);
        if cost(y) > c0 + eps {
            return false;
        }
    }
    true
}

// ─────────────────────────────────────────────────
// Lemma 3 の対応：命令列結合性の実行時テスト
// Lean: runInstructions_append
// ─────────────────────────────────────────────────

/// insns1 ++ insns2 の実行 == insns2(insns1(w0)) を検証
pub fn verify_append_associativity(
    insns1: &[Instruction],
    insns2: &[Instruction],
    w0: Word,
) -> bool {
    let combined: Vec<Instruction> = insns1.iter().chain(insns2.iter()).copied().collect();
    let r_combined = run_instructions(&combined, w0);

    let r1 = run_instructions(insns1, w0);
    let r2 = run_instructions(insns2, r1.word);

    r_combined.word == r2.word
        && (r_combined.cost - (r1.cost + r2.cost)).abs() < 1e-9
}

// ─────────────────────────────────────────────────
// 具体例命令
// Lean: def identityInsn : Instruction := fun w => (w, 0)
// ─────────────────────────────────────────────────

pub fn identity_insn(w: Word) -> (Word, Cost) {
    (w, 0.0)
}

pub fn popcount_insn(w: Word) -> (Word, Cost) {
    (w.count_ones() as u64, 1.0)
}

pub fn shift_left_insn(w: Word) -> (Word, Cost) {
    (w << 1, 0.5)
}

// ─────────────────────────────────────────────────
// 単体テスト
// Lean の各 Lemma に対応
// ─────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // Lean: identity_preserves_word
    #[test]
    fn test_identity_preserves_word() {
        let state = run_instructions(&[identity_insn], 0xDEADBEEFu64);
        assert_eq!(state.word, 0xDEADBEEFu64);
    }

    // Lean: identity_zero_cost
    #[test]
    fn test_identity_zero_cost() {
        let state = run_instructions(&[identity_insn], 0xDEADBEEFu64);
        assert_eq!(state.cost, 0.0);
    }

    // Lean: Lemma 3 runInstructions_append
    #[test]
    fn test_append_associativity() {
        let insns1: &[Instruction] = &[identity_insn, shift_left_insn];
        let insns2: &[Instruction] = &[popcount_insn];
        assert!(verify_append_associativity(insns1, insns2, 0xFF00u64));
    }

    // Lean: Lemma 4 runInstructions_cost_nonneg
    #[test]
    fn test_cost_nonneg() {
        let insns: &[Instruction] = &[identity_insn, popcount_insn, shift_left_insn];
        let state = run_instructions(insns, 12345u64);
        assert!(state.cost >= 0.0);
    }

    // Lean: Lemma 2 neighbor_cost_bound
    #[test]
    fn test_neighbor_cost_bound() {
        let cost = |w: Word| (w.count_ones() as f64);
        // popcount は Hamming距離1で最大1変化 → eps=1.0で成立
        assert!(verify_neighbor_cost_bound(cost, 0xFFFFu64, 1.0));
    }

    // Lean: hamming_dist
    #[test]
    fn test_hamming_dist() {
        assert_eq!(hamming_dist(0b1010u64, 0b1111u64), 2);
        assert_eq!(hamming_dist(0u64, 0u64), 0);
        assert_eq!(hamming_dist(1u64, 0u64), 1);
    }

    // Lean: IsConsistent64 / IsDeterministic
    #[test]
    fn test_deterministic() {
        let f = |w: Word| (w ^ 0xFF, 1.0f64);
        let g = |w: Word| (w ^ 0xFF, 1.0f64);
        let inputs: Vec<Word> = (0u64..256).collect();
        assert!(assert_deterministic(f, g, &inputs));
    }

    // Lean: Program hNonempty
    #[test]
    fn test_program_nonempty() {
        assert!(Program::new(vec![]).is_err());
        assert!(Program::new(vec![identity_insn]).is_ok());
    }

    // Lean: A1 IsMinimalWord
    #[test]
    fn test_minimal() {
        let cost = |w: Word| (w.count_ones() as f64);
        let candidates: Vec<Word> = (0u64..1024).collect();
        // popcount最小は0（全ビット0）
        assert!(is_minimal_on(cost, 0u64, &candidates));
    }
}
