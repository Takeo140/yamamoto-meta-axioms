License Apache 2.0 Takeo Yamamoto

// ilp64.rs — ILP64.lean の Rust 実装
// rayon による並列実行エンジン
// 依存: rayon = "1.10", petgraph = "0.6"

use std::collections::{HashMap, HashSet};
use rayon::prelude::*;

// ─────────────────────────────────────────────────
// 基本型
// Lean: abbrev Word := BitVec 64
// Lean: abbrev RegId := Fin 16
// ─────────────────────────────────────────────────

pub type Word   = u64;
pub type RegId  = usize;  // 0..15
pub const NUM_REGS: usize = 16;

pub type RegFile = [Word; NUM_REGS];

// ─────────────────────────────────────────────────
// 命令表現
// Lean: structure Insn where reads writes exec latency
// ─────────────────────────────────────────────────

#[derive(Clone)]
pub struct Insn {
    pub reads:   Vec<RegId>,
    pub writes:  RegId,
    pub exec:    fn(&RegFile) -> Word,
    pub latency: usize,
    pub name:    &'static str,
}

impl Insn {
    pub fn run(&self, rf: &RegFile) -> RegFile {
        let mut new_rf = *rf;
        new_rf[self.writes] = (self.exec)(rf);
        new_rf
    }
}

// ─────────────────────────────────────────────────
// 依存性チェック
// Lean: HasRAW / HasWAW / HasWAR / HasDep / Independent
// ─────────────────────────────────────────────────

pub fn has_raw(i: &Insn, j: &Insn) -> bool {
    j.reads.contains(&i.writes)
}

pub fn has_waw(i: &Insn, j: &Insn) -> bool {
    i.writes == j.writes
}

pub fn has_war(i: &Insn, j: &Insn) -> bool {
    i.reads.contains(&j.writes)
}

pub fn has_dep(i: &Insn, j: &Insn) -> bool {
    has_raw(i, j) || has_waw(i, j) || has_war(i, j)
}

/// Lean: Independent i j
pub fn is_independent(i: &Insn, j: &Insn) -> bool {
    !has_dep(i, j) && !has_dep(j, i)
}

// ─────────────────────────────────────────────────
// データ依存グラフ（DDG）
// Lean: structure DDG where insns edges hEdge hAcyclic
// ─────────────────────────────────────────────────

pub struct DDG {
    pub insns: Vec<Insn>,
    /// edges[i] = j が依存するインデックス集合
    pub edges: Vec<HashSet<usize>>,
}

impl DDG {
    /// 命令列から DDG を自動構築（O(n²)）
    pub fn build(insns: Vec<Insn>) -> Self {
        let n = insns.len();
        let mut edges = vec![HashSet::new(); n];
        for i in 0..n {
            for j in (i + 1)..n {
                if has_dep(&insns[i], &insns[j]) {
                    edges[i].insert(j);
                }
                if has_dep(&insns[j], &insns[i]) {
                    edges[j].insert(i);
                }
            }
        }
        Self { insns, edges }
    }

    /// Lean: DDG.IndependentPair
    pub fn independent_pair(&self, i: usize, j: usize) -> bool {
        !self.edges[i].contains(&j) && !self.edges[j].contains(&i)
    }
}

// ─────────────────────────────────────────────────
// 並列スケジュール（トポロジカルソートによる生成）
// Lean: structure ParallelSchedule where time hRespect
// ─────────────────────────────────────────────────

pub struct ParallelSchedule {
    /// time[i] = 命令 i のタイムステップ
    pub time: Vec<usize>,
}

impl ParallelSchedule {
    /// Kahn のアルゴリズムで ASAP スケジュールを生成
    /// ASAP = As Soon As Possible（最短スケジュール）
    pub fn asap(ddg: &DDG) -> Self {
        let n = ddg.insns.len();
        let mut in_degree = vec![0usize; n];
        let mut successors: Vec<Vec<usize>> = vec![vec![]; n];

        for i in 0..n {
            for &j in &ddg.edges[i] {
                in_degree[j] += 1;
                successors[i].push(j);
            }
        }

        let mut time = vec![0usize; n];
        let mut queue: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
        let mut processed = vec![false; n];

        while !queue.is_empty() {
            let i = queue.remove(0);
            processed[i] = true;
            let finish_time = time[i] + ddg.insns[i].latency;
            for &j in &successors[i] {
                time[j] = time[j].max(finish_time);
                in_degree[j] -= 1;
                if in_degree[j] == 0 {
                    queue.push(j);
                }
            }
        }

        Self { time }
    }

    /// Lean: makespan
    pub fn makespan(&self, insns: &[Insn]) -> usize {
        self.time.iter().zip(insns.iter())
            .map(|(t, insn)| t + insn.latency)
            .max()
            .unwrap_or(0)
    }
}

// ─────────────────────────────────────────────────
// 並列実行エンジン
// Lean: Block / block_parallel_correct
// rayon により独立命令を真に並列実行
// ─────────────────────────────────────────────────

/// 同一タイムステップの命令を並列実行
/// Lean: block_parallel_correct の工学的実装
pub fn execute_parallel_step(
    insns: &[Insn],
    indices: &[usize],
    rf: &RegFile,
) -> RegFile {
    // 独立性を事前確認
    debug_assert!(
        indices.windows(2).all(|w| is_independent(&insns[w[0]], &insns[w[1]])),
        "Non-independent instructions in parallel block"
    );

    // 並列に exec を実行（rayon）
    let results: Vec<(RegId, Word)> = indices
        .par_iter()
        .map(|&i| (insns[i].writes, (insns[i].exec)(rf)))
        .collect();

    // 書き込みを順次適用（競合なし・独立性保証済み）
    let mut new_rf = *rf;
    for (reg, val) in results {
        new_rf[reg] = val;
    }
    new_rf
}

/// スケジュール全体の実行
/// Lean: executeSchedule
pub fn execute_schedule(
    insns: &[Insn],
    sched: &ParallelSchedule,
    rf0: RegFile,
) -> RegFile {
    // タイムステップ → 命令インデックス群
    let max_time = sched.time.iter().copied().max().unwrap_or(0);
    let mut by_time: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, &t) in sched.time.iter().enumerate() {
        by_time.entry(t).or_default().push(i);
    }

    let mut rf = rf0;
    for t in 0..=max_time {
        if let Some(indices) = by_time.get(&t) {
            rf = execute_parallel_step(insns, indices, &rf);
        }
    }
    rf
}

// ─────────────────────────────────────────────────
// ベンチマーク用：クリティカルパス長の計算
// Lean: pathLength / schedule_lower_bound
// ─────────────────────────────────────────────────

/// DDG のクリティカルパス長（動的計画法）
pub fn critical_path_length(ddg: &DDG) -> usize {
    let n = ddg.insns.len();
    let mut dp = vec![0usize; n];

    // トポロジカル順に DP
    let sched = ParallelSchedule::asap(ddg);
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| sched.time[i]);

    for &i in &order {
        dp[i] = dp[i].max(ddg.insns[i].latency);
        let successors: Vec<usize> = ddg.edges[i].iter().copied().collect();
        for j in successors {
            dp[j] = dp[j].max(dp[i] + ddg.insns[j].latency);
        }
    }

    dp.into_iter().max().unwrap_or(0)
}

// ─────────────────────────────────────────────────
// 具体例命令
// Lean: addInsn / xorInsn
// ─────────────────────────────────────────────────

pub fn make_add_insn() -> Insn {
    Insn {
        reads:   vec![1, 2],
        writes:  0,
        exec:    |rf| rf[1].wrapping_add(rf[2]),
        latency: 1,
        name:    "ADD r0, r1, r2",
    }
}

pub fn make_xor_insn() -> Insn {
    Insn {
        reads:   vec![4, 5],
        writes:  3,
        exec:    |rf| rf[4] ^ rf[5],
        latency: 1,
        name:    "XOR r3, r4, r5",
    }
}

pub fn make_mul_insn() -> Insn {
    Insn {
        reads:   vec![6, 7],
        writes:  8,
        exec:    |rf| rf[6].wrapping_mul(rf[7]),
        latency: 3,  // 乗算は3サイクル
        name:    "MUL r8, r6, r7",
    }
}

pub fn make_shift_insn() -> Insn {
    Insn {
        reads:   vec![0],
        writes:  9,
        exec:    |rf| rf[0] << 3,
        latency: 1,
        name:    "SHL r9, r0, 3",
    }
}

// ─────────────────────────────────────────────────
// 単体テスト
// ─────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn init_rf() -> RegFile {
        let mut rf = [0u64; NUM_REGS];
        rf[1] = 10; rf[2] = 20;  // ADD の入力
        rf[4] = 0xFF; rf[5] = 0x0F;  // XOR の入力
        rf[6] = 7; rf[7] = 6;    // MUL の入力
        rf
    }

    // Lean: add_xor_independent
    #[test]
    fn test_add_xor_independent() {
        let add = make_add_insn();
        let xor = make_xor_insn();
        assert!(is_independent(&add, &xor));
    }

    // Lean: add_xor_commute（主定理 1 の工学的検証）
    #[test]
    fn test_commutativity() {
        let add = make_add_insn();
        let xor = make_xor_insn();
        let rf = init_rf();

        let rf_add_then_xor = xor.run(&add.run(&rf));
        let rf_xor_then_add = add.run(&xor.run(&rf));

        assert_eq!(rf_add_then_xor, rf_xor_then_add,
            "Independent instructions must commute (Lean: add_xor_commute)");
    }

    // Lean: schedule_lower_bound（クリティカルパス下界）
    #[test]
    fn test_critical_path_lower_bound() {
        // ADD → SHL（RAW依存: r0）, MUL 独立
        let add = make_add_insn();
        let xor = make_xor_insn();
        let mul = make_mul_insn();
        let shl = make_shift_insn();

        let ddg = DDG::build(vec![add, xor, mul, shl]);
        let sched = ParallelSchedule::asap(&ddg);
        let cp = critical_path_length(&ddg);
        let ms = sched.makespan(&ddg.insns);

        assert!(cp <= ms,
            "Makespan {} must be >= critical path {} (Lean: schedule_lower_bound)",
            ms, cp);
    }

    // 並列実行の正当性
    #[test]
    fn test_parallel_execution() {
        let add = make_add_insn();
        let xor = make_xor_insn();
        let mul = make_mul_insn();
        let rf = init_rf();

        let insns = vec![add.clone(), xor.clone(), mul.clone()];
        let ddg = DDG::build(insns.clone());
        let sched = ParallelSchedule::asap(&ddg);

        let rf_parallel = execute_schedule(&insns, &sched, rf);
        // 順次実行と結果が一致するか（全独立なら順序不変）
        let rf_seq = mul.run(&xor.run(&add.run(&rf)));

        // r0 (ADD), r3 (XOR), r8 (MUL) を確認
        assert_eq!(rf_parallel[0], rf_seq[0], "ADD result mismatch");
        assert_eq!(rf_parallel[3], rf_seq[3], "XOR result mismatch");
        assert_eq!(rf_parallel[8], rf_seq[8], "MUL result mismatch");
    }

    // makespan が順次実行より短いことの確認（ILP の効果）
    #[test]
    fn test_ilp_speedup() {
        let add = make_add_insn();  // latency 1
        let xor = make_xor_insn();  // latency 1
        let mul = make_mul_insn();  // latency 3
        let insns = vec![add, xor, mul];
        let ddg = DDG::build(insns.clone());
        let sched = ParallelSchedule::asap(&ddg);

        let parallel_makespan = sched.makespan(&insns);
        let sequential_makespan: usize = insns.iter().map(|i| i.latency).sum();

        println!("Parallel makespan: {}", parallel_makespan);
        println!("Sequential makespan: {}", sequential_makespan);
        assert!(parallel_makespan <= sequential_makespan,
            "Parallel must not be slower than sequential");
    }
}
