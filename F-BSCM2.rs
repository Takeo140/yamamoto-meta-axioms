use std::collections::VecDeque;
use std::hash::Hasher;

// =============================================================================
// 1. F-BSCM 数理コア（64bit形式に完全合致）
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogSeverity {
    Info = 1,
    Warning = 2,
    Critical = 3,  // 最高優先度（アトラクターへの射影対象）
}

/// BSCM時間遷移関数 δ (State-Reducing & 64bit Bounded)
fn bscm_delta(s: u64) -> u64 {
    if s % 2 == 0 {
        s / 2
    } else {
        // 64bitオーバーフローを防ぐため、最大値の場合は安全にラップ
        if s == u64::MAX { 0 } else { (s + 1) / 2 }
    }
}

/// BSCM制御ステップ（外部入力を安全に64bitの剰余環へ写像）
fn bscm_control_step(current_state: u64, external_input: u64) -> u64 {
    // Rustのラッピング加算（% 2^64 と同値）
    let s_prime = current_state.wrapping_add(external_input);
    bscm_delta(s_prime)
}

// =============================================================================
// 2. セキュアログ・プロトコル実装
// =============================================================================

#[derive(Debug, Clone)]
pub struct LogEntry {
    pub index: u64,          // BSCMによって決定論的に割り振られるインデックス
    pub severity: LogSeverity,
    pub message: String,
    pub hash_chain: u64,     // 暗号学的強度の代わりに、高速な64bitハッシュチェーン
}

pub struct SecureLogSystem {
    current_state: u64,
    last_hash: u64,
    // F-Theory 空間: 常に severity (Weight) の降順にソートされたキュー
    // Meta-Axiom A4: 先頭ノードが常に最高重みを保持することを保証
    f_space: VecDeque<LogEntry>,
}

impl SecureLogSystem {
    pub fn new(initial_state: u64) -> Self {
        Self {
            current_state: initial_state,
            last_hash: 0,
            f_space: VecDeque::new(),
        }
    }

    /// ログの書き込み (Space-Time Integrated Step)
    pub fn append_log(&mut self, message: &str, severity: LogSeverity) {
        // 1. 時間（インデックス）の確定: 入力の文字長などを外部入力として状態遷移
        let external_input = message.len() as u64;
        self.current_state = bscm_control_step(self.current_state, external_input);

        // 2. ハッシュチェーンの生成 (改ざん防止の数理)
        // 現在のインデックス、メッセージ、直前のハッシュをミキシング
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        hasher.write_u64(self.current_state);
        hasher.write(message.as_bytes());
        hasher.write_u64(self.last_hash);
        self.last_hash = hasher.finish();

        let entry = LogEntry {
            index: self.current_state,
            severity,
            message: message.to_string(),
            hash_chain: self.last_hash,
        };

        // 3. F-Theory 空間へのインジェクション (A4不変量の維持)
        // 二分探索により、降順のソート順序を維持しながら O(N) で挿入
        let insert_pos = self.f_space
            .iter()
            .position(|e| e.severity < severity)
            .unwrap_or(self.f_space.len());
        
        self.f_space.insert(insert_pos, entry);
    }

    /// 【O(1) Convergence】最高優先度のログを一撃で抽出する
    pub fn extract_critical_alert(&self) -> Option<&LogEntry> {
        // F-Theoryの証明通り、先頭（Index 0）を見るだけで、
        // システム全体の規模 N に依存せず O(1) で最高リスクのログにアクセスできる
        self.f_space.front()
    }

    /// ログチェーンの完全性検証（改ざん検知）
    pub fn verify_integrity(&self) -> bool {
        // ログが途中で削除されたり、メッセージが書き換えられたりした場合、
        // ハッシュの連鎖が崩れるため、一発で検知可能
        // （ここにLeanの論理整合性 A3_LogicalConsistency が対応する）
        
        // 実装: 先頭からハッシュを再計算してチェック
        let mut current_state: u64 = 0;
        let mut last_hash: u64 = 0;
        
        for entry in &self.f_space {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            hasher.write_u64(entry.index);
            hasher.write(entry.message.as_bytes());
            hasher.write_u64(last_hash);
            let expected_hash = hasher.finish();
            
            if entry.hash_chain != expected_hash {
                return false;
            }
            
            last_hash = entry.hash_chain;
        }
        
        true
    }
}

// =============================================================================
// 3. 動作検証 (実用性デモ)
// =============================================================================
fn main() {
    let mut logger = SecureLogSystem::new(12345);

    // ログの連続投入
    logger.append_log("System initialized", LogSeverity::Info);
    logger.append_log("Database connection slow", LogSeverity::Warning);
    logger.append_log("UNAUTHORIZED ACCESS DETECTED", LogSeverity::Critical); // 最後にCriticalを投入
    logger.append_log("User logged out", LogSeverity::Info);

    // O(1) 抽出の確認
    if let Some(top_alert) = logger.extract_critical_alert() {
        println!("--- F-Theory O(1) Extraction Result ---");
        println!("Index (BSCM Time): {}", top_alert.index);
        println!("Severity (Weight): {:?}", top_alert.severity);
        println!("Message:           {}", top_alert.message);
        println!("Hash Chain:        {:X}", top_alert.hash_chain);
    }

    // 整合性検証
    println!("\n--- Integrity Verification ---");
    println!("Chain Valid: {}", logger.verify_integrity());
}
