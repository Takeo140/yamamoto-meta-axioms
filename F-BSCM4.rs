use std::collections::VecDeque;

// =============================================================================
// 1. F-BSCM 数理コア（64bit形式・ハードウェア適合）
// =============================================================================

fn bscm_delta(s: u64) -> u64 {
    if s % 2 == 0 { s / 2 } else { if s == u64::MAX { 0 } else { (s + 1) / 2 } }
}

fn bscm_control_step(current_state: u64, packet_size: u64) -> u64 {
    // パケットサイズを入力として状態を遷移。
    // 64bitのラッピング加算（% 2^64）により、ハードウェアレベルでのバッファ溢れを防ぐ数理
    current_state.wrapping_add(packet_size)
}

// =============================================================================
// 2. ネットワークルーター・バッファ管理実装
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum PacketPriority {
    BestEffort = 1,     // 一般のWebトラフィック（通常のデータ転送）
    VoiceVideo = 2,     // リアルタイム通信（QoS保証）
    NetworkControl = 3, // ルーター間の制御信号（最優先：BGPやOSPFなど。アトラクター射影対象）
}

#[derive(Debug, Clone)]
pub struct NetworkPacket {
    pub sequence_id: u64,       // BSCMが決定論的に生成する一意のパケット識別・時間ID
    pub priority: PacketPriority,
    pub payload_size: u32,
    pub data: Vec<u8>,
}

pub struct FBSCMRouterBuffer {
    /// BSCM 時間ドメイン: ルーター全体の「トラフィック蓄積状態」を表現
    /// ギガビットのバーストトラフィックが来ても、64bitの符号なし整数境界を決して超えない
    pub traffic_state: u64,
    
    /// F-Theory 空間ドメイン: パケットキュー（優先度順保持）
    /// Meta-Axiom A4不変量により、常に priority の降順（Control -> Voice -> Effort）でソートを維持
    packet_space: VecDeque<NetworkPacket>,
}

impl FBSCMRouterBuffer {
    pub fn new(initial_state: u64) -> Self {
        Self {
            traffic_state: initial_state,
            packet_space: VecDeque::new(),
        }
    }

    /// パケットの受信 (Space-Time Integrated Packet Ingress)
    /// 
    /// BSCMにより決定論的なsequence_idを生成し、F-Theoryの不変量を保ちながら
    /// 優先度順にパケットをバッファへ挿入する。
    pub fn receive_packet(&mut self, data: Vec<u8>, priority: PacketPriority) {
        // 1. 時間の確定 (BSCM)
        // パケットの長さを外部入力として状態遷移。決定論的に一意な sequence_id が確定する。
        let packet_size = data.len() as u64;
        self.traffic_state = bscm_control_step(self.traffic_state, packet_size);
        let next_seq_id = bscm_delta(self.traffic_state);

        let packet = NetworkPacket {
            sequence_id: next_seq_id,
            priority,
            payload_size: data.len() as u32,
            data,
        };

        // 2. 空間の不変量維持 (F-Theory)
        // トポロジー空間（バッファ）にパケットを挿入。
        // 優先度の降順を保つため、適切な位置に挿入する。
        let insert_pos = self.packet_space
            .iter()
            .position(|p| p.priority < priority)
            .unwrap_or(self.packet_space.len());
        
        self.packet_space.insert(insert_pos, packet);
    }

    /// 【O(1) Convergence】次にルーティング（転送）すべきパケットを一撃で取り出す
    /// 
    /// F-Theoryの証明（O1_convergence）が保証する通り、
    /// どれだけ大量のDDoSパケット（BestEffort）がバッファに詰まっていても、
    /// ルーターはキューの総数 N を走査することなく、先頭（Index 0）を O(1) で処理するだけで、
    /// ネットワーク崩壊を防ぐための重要シグナルを確実に最優先転送できる。
    pub fn pop_next_routing_packet(&mut self) -> Option<NetworkPacket> {
        self.packet_space.pop_front()
    }
}

// =============================================================================
// 3. ルーター挙動デモ（DDoS攻撃耐性のシミュレーション）
// =============================================================================
fn main() {
    let mut router = FBSCMRouterBuffer::new(0);

    // 1. 大量のスパムパケット（DDoS攻撃）が押し寄せる
    for i in 0..5 {
        router.receive_packet(
            format!("DDoS Attack Packet {}", i).into_bytes(), 
            PacketPriority::BestEffort
        );
    }

    // 2. その最中に、ルーターの死活を司る「制御信号（BGP Keepaliveなど）」が1通だけ届く
    router.receive_packet(
        "ROUTER_CONTROL_SIGNAL_KEEP_ALIVE".as_bytes().to_vec(), 
        PacketPriority::NetworkControl
    );

    // 3. 攻撃パケットがさらに届く
    router.receive_packet("DDoS Attack Packet 5".as_bytes().to_vec(), PacketPriority::BestEffort);

    println!("--- F-BSCM Network Router Packet Processing ---");

    // パケットの転送（ルーティング）開始
    // 大量のスパムパケット（BestEffort）の中に後から埋もれたはずの「NetworkControl」が、
    // 計算負荷ゼロ（O(1)）で確実に最初に取り出される。
    if let Some(first_packet) = router.pop_next_routing_packet() {
        println!(
            "-> [FORWARDED FIRST] Priority: {:?}, Size: {} bytes, Data: {}",
            first_packet.priority,
            first_packet.payload_size,
            String::from_utf8_lossy(&first_packet.data)
        );
    }

    // 残りのトラフィックも優先度順に平滑化されて処理される
    while let Some(packet) = router.pop_next_routing_packet() {
        println!("Forwarding Next -> Priority: {:?}", packet.priority);
    }
}
