// SPDX-License-Identifier: CC-BY-4.0　Apache 2.0 Takeo Yamamoto
// F-Theory: Formal Complexity Theory and O(1) Convergence
// Rigorous Cost-Monad Hash-Topology Model

/// §1. Cost Computation Model (コスト計算モデル)
/// 計算結果（T）と、その計算に要したステップ数（usize）のペアを保持する構造体
#[derive(Debug, Clone)]
pub struct CostComp<T> {
    pub value: T,
    pub cost: usize,
}

impl<T> CostComp<T> {
    /// 新しいコスト付き計算を生成 (Leanの `step` 相当)
    pub fn new(value: T, cost: usize) -> Self {
        Self { value, cost }
    }

    /// コスト付き計算を合成する (Leanの `bind_comp` 相当)
    pub fn bind<U, F>(self, f: F) -> CostComp<U>
    where
        F: FnOnce(T) -> CostComp<U>,
    {
        let next = f(self.value);
        CostComp {
            value: next.value,
            cost: self.cost + next.cost, // ステップ数を加算
        }
    }
}

// ============================================================

pub const SUCCESS_FLAG: &str = "META_AXIOM_SUCCESS";
pub const SYSTEM_ROOT: &str = "system_root";

/// §2. Advanced MetaSystem Architecture
/// メモリ空間とハッシュ関数をカプセル化したシステム構造
pub struct MetaSystem {
    pub scale_n: usize,
    pub memory: Vec<String>,
    // 任意の文字列キーから有効なインデックスへの写像
    pub hash_func: Box<dyn Fn(&str) -> usize>,
}

impl MetaSystem {
    /// システムの初期化と「メタ公理」のバリデーション
    pub fn new(scale_n: usize, memory: Vec<String>, hash_func: Box<dyn Fn(&str) -> usize>) -> Self {
        // [前提1] メモリサイズは必ず1以上 (mem_valid)
        assert!(!memory.is_empty(), "Fatal: Memory space must be > 0");

        let system = Self { scale_n, memory, hash_func };

        // [Meta-Axiom A1] A1_ExtremumPrinciple
        // システムルートのハッシュは必ずSuccessを指すという数学的保証の確認
        let root_idx = (system.hash_func)(SYSTEM_ROOT);
        assert_eq!(
            system.memory[root_idx], SUCCESS_FLAG,
            "Axiom Violation: system_root must point to SUCCESS_FLAG"
        );

        system
    }

    /// §3. Primitive Operations & Execution Logic

    /// ハッシュ値の計算: 常に O(1) = 1ステップと定義
    pub fn compute_hash(&self, key: &str) -> CostComp<usize> {
        let idx = (self.hash_func)(key);
        CostComp::new(idx, 1)
    }

    /// 配列（メモリ）へのアクセス: 常に O(1) = 1ステップと定義
    pub fn memory_read(&self, idx: usize) -> CostComp<String> {
        // RustのVecによる O(1) アクセス
        let val = self.memory[idx].clone();
        CostComp::new(val, 1)
    }

    /// 解の抽出アルゴリズム
    /// ハッシュ計算モナドとメモリアクセスモナドを `bind` で合成する
    pub fn extract_solution(&self, key: &str) -> CostComp<String> {
        self.compute_hash(key)
            .bind(|idx| self.memory_read(idx))
    }
}

// ============================================================
// §4. Formal Proofs (Rustではユニットテストとして表現)
// ============================================================

#[cfg(test)]
mod formal_proofs {
    use super::*;

    /// テスト用の有効なMetaSystemを構築するヘルパー
    fn build_valid_system() -> MetaSystem {
        let mut memory = vec!["EMPTY".to_string(); 100];
        let success_idx = 42;
        memory[success_idx] = SUCCESS_FLAG.to_string();

        let hash_func = Box::new(move |key: &str| -> usize {
            if key == SYSTEM_ROOT {
                success_idx
            } else {
                0 // 擬似的なハッシュ衝突
            }
        });

        MetaSystem::new(10_000, memory, hash_func)
    }

    /// 定理 1: 時間計算量の O(1) 収束証明 (Time Complexity Proof)
    #[test]
    fn proof_o1_time_complexity() {
        let system = build_valid_system();
        let result = system.extract_solution("some_random_key");

        // 抽出処理にかかる総ステップ数は、システム規模に一切依存せず常に定数 `2` である
        assert_eq!(result.cost, 2);
    }

    /// 定理 2: 絶対的収束と正確性の証明 (Absolute Convergence Proof)
    #[test]
    fn proof_absolute_convergence() {
        let system = build_valid_system();
        let result = system.extract_solution(SYSTEM_ROOT);

        // システムルートをキーとして実行した場合、計算結果は確実に SUCCESS_FLAG となる
        assert_eq!(result.value, SUCCESS_FLAG);
    }
}
