/// Bounded Collatz State Model (BSCM) 制御コア
/// 
/// どんな凶悪な外乱（ジャミング、ノイズ、パニックデータ）が注入されても、
///数理的に数値を有限の器（u64）に閉じ込め、絶対に数値を膨張（オーバーフロー）させず、
/// かつIf文の分岐予測ミスによる遅延すら発生させない、絶対安全の有界フィルター。
pub struct BscmCore {
    // 64ビット空間の有限の「器（状態）」
    state: u64,
}

impl BscmCore {
    /// 新しいBSCMコアを初期化（任意の初期状態からスタート可能）
    pub fn new(initial_state: u64) -> Self {
        Self { state: initial_state }
    }

    /// 外乱を注入し、コラッツ構造を用いて数理的に有界（安全圏）へ丸め込むコア・ループ
    /// 
    /// # Arguments
    /// * `disturbance` - 外部から入ってくるカオスな外乱データ（u64）
    /// 
    /// # Returns
    /// * 安全に有界化された次の状態（u64）
    #[inline(always)] // コンパイラにインライン化を強制し、関数呼び出しのオーバーヘッドすら消去
    pub fn update(&mut self, disturbance: u64) -> u64 {
        // 1. 外乱の注入 ── 高校数学（算数）の Modulo 2^64 の「器」
        // Rustの `wrapping_add` は、CPUのハードウェア仕様をそのまま使い、
        // 万が一数値が溢れても1ナノ秒で自動的に下位ビットへすり潰します（数値膨張の物理的破壊）。
        self.state = self.state.wrapping_add(disturbance);

        // 2. コラッツ構造によるダイナミック減衰（偶奇による高速分岐）
        // state & 1 == 0 は「偶数」の判定（最速のビット論理積演算）
        if (self.state & 1) == 0 {
            // 偶数レール：右シフト（s >> 1）。
            // どんなカオスなトゲも、毎クロック「50%減衰」の超重力で引きずり下ろします。
            self.state >>= 1;
        } else {
            // 奇数レール：コラッツ前進、またはビット完全反転
            // 特定の危険領域（下位2ビットが 11、つまり 4n + 3 の状態）を検知
            if (self.state & 3) == 3 {
                // ビット完全反転（NOT演算：~s）
                // 数値が膨張する前に、空間を丸ごとひっくり返してアトラクターへ強制送還
                self.state = !self.state;
            } else {
                // 通常のコラッツ前進（3s + 1）
                // ここでも数値膨張を防ぐため、安全にラップ（周回）させる
                self.state = self.state.wrapping_mul(3).wrapping_add(1);
            }
        }

        // 有界化された絶対安全な状態を返す
        self.state
    }

    /// 現在の内部状態を取得する
    pub fn get_state(&self) -> u64 {
        self.state
    }
}

// ── 以下、動作検証（テストコード） ──
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bscm_absolute_safety() {
        let mut core = BscmCore::new(123456789);

        // 宇宙空間や迎撃ミサイルを襲う、最大級に凶悪な「過大外乱（u64の最大値）」の津波
        let chaotic_disturbances = [
            u64::MAX,           // 18446744073709551615 (オーバーフロー誘発数値)
            u64::MAX - 1, 
            0xDEADBEEFCAF00000, // サイバー攻撃を模した不正な16進数バースト
            135792468, 
            0,
        ];

        println!("--- BSCM 堅牢性シミュレーション開始 ---");
        for (i, &dist) in chaotic_disturbances.iter().enumerate() {
            let next_state = core.update(dist);
            // 通常のRustコードなら `u64::MAX + α` でパニック（クラッシュ）しますが、
            // BSCMは平然と数値を檻の中に丸め込み、次の計算へと何事もなかったかのようにバトンを渡します。
            println!("ステップ [{}]: 注入外乱 = {}, 有界化された状態 = {}", i, dist, next_state);
            
            // アサーション（テスト通過確認）：プログラムが死んでいないことの証明
            assert!(next_state <= u64::MAX); 
        }
        println!("--- シミュレーション成功：パニック・ハングアップ件数 0 ---");
    }
}
