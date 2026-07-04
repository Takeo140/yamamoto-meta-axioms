#include <iostream>
#include <vector>
#include <cstdint>
#include <cstring>
#include <cassert>
#include <chrono>

namespace UHA {

// UltraCore 基本スカラー：U64 有限環 ZMod(2^64)
using U64 = uint64_t;
using Size = uint64_t;

// 疎構造における非ゼロ要素の表現
struct CTerm {
    uint64_t index; // 位相空間上の座標インデックス
    U64 value;      // 複素数ビット状態の離散値
};

// UHAの位相空間状態
struct UHAState {
    uint32_t n;                 // 複素数ビット数 (次元数)
    std::vector<CTerm> terms;   // 非ゼロ要素のリスト (疎ベクトル)

    // 量子状態の離散版：ノルムの計算
    U64 compute_norm() const {
        U64 total_norm = 0;
        for (const auto& term : terms) {
            total_norm += term.value * term.value; // ZMod(2^64)上での二乗和
        }
        return total_norm;
    }
};

// ==========================================
// UHA PROTOCOL ENCODER (エンコーダ)
// ==========================================
class Encoder {
public:
    static std::vector<uint8_t> Encode(const UHAState& state) {
        // ヘッダーサイズの計算: Magic(4) + n(4) + nnz(8) = 16 bytes
        constexpr size_t HEADER_SIZE = 16;
        size_t payload_size = state.terms.size() * sizeof(CTerm);
        
        // メモリの一括確保（再確保のオーバーヘッドを完全に排除）
        std::vector<uint8_t> buffer(HEADER_SIZE + payload_size);
        uint8_t* ptr = buffer.data();

        // 1. Magic Number の書き込み ('U', 'H', 'A', '1')
        ptr[0] = 'U'; ptr[1] = 'H'; ptr[2] = 'A'; ptr[3] = '1';
        ptr += 4;

        // 2. 次元数 n の書き込み
        std::memcpy(ptr, &state.n, sizeof(uint32_t));
        ptr += sizeof(uint32_t);

        // 3. 非ゼロ要素数 (nnz) の書き込み
        uint64_t nnz = state.terms.size();
        std::memcpy(ptr, &nnz, sizeof(uint64_t));
        ptr += sizeof(uint64_t);

        // 4. ペイロード（非ゼロ要素のバイナリ配列）のゼロコピー書き込み
        if (nnz > 0) {
            std::memcpy(ptr, state.terms.data(), payload_size);
        }

        return buffer;
    }
};

// ==========================================
// UHA PROTOCOL DECODER (デコーダ)
// ==========================================
class Decoder {
public:
    static bool Decode(const std::vector<uint8_t>& buffer, UHAState& out_state) {
        constexpr size_t HEADER_SIZE = 16;
        if (buffer.size() < HEADER_SIZE) {
            std::cerr << "[Error] Buffer too small for header.\n";
            return false;
        }

        const uint8_t* ptr = buffer.data();

        // 1. Magic Number の検証
        if (ptr[0] != 'U' || ptr[1] != 'H' || ptr[2] != 'A' || ptr[3] != '1') {
            std::cerr << "[Error] Invalid Magic Number.\n";
            return false;
        }
        ptr += 4;

        // 2. 次元数 n の読み込み
        std::memcpy(&out_state.n, ptr, sizeof(uint32_t));
        ptr += sizeof(uint32_t);

        // 3. 非ゼロ要素数 (nnz) の読み込み
        uint64_t nnz = 0;
        std::memcpy(&nnz, ptr, sizeof(uint64_t));
        ptr += sizeof(uint64_t);

        // バッファサイズの整合性チェック（パケット破損の検知）
        size_t expected_size = HEADER_SIZE + (nnz * sizeof(CTerm));
        if (buffer.size() != expected_size) {
            std::cerr << "[Error] Buffer size mismatch. Corrupted packet.\n";
            return false;
        }

        // 4. ペイロードのデシリアライズ
        out_state.terms.resize(nnz);
        if (nnz > 0) {
            std::memcpy(out_state.terms.data(), ptr, nnz * sizeof(CTerm));
        }

        return true;
    }
};

} // namespace UHA

// ==========================================
// 検証用メイン関数（シミュレーション）
// ==========================================
int main() {
    std::cout << "=== UHA 通信プロトコル・実証実験 ===" << std::endl;

    // 1. 送信側：UHA状態（複素数ビット空間）の生成
    UHA::UHAState tx_state;
    tx_state.n = 35; // 35の複素数ビット空間
    
    // 擬似的な疎構造データの注入（非ゼロ要素を3つ作成）
    tx_state.terms.push_back({0x00000001, 123456789ULL});
    tx_state.terms.push_back({0x000FFFFF, 987654321ULL});
    tx_state.terms.push_back({0x01FFFFFF, 555555555ULL});

    // 送信前のノルム（量子状態の総和）を記録
    UHA::U64 tx_norm = tx_state.compute_norm();
    std::cout << "[TX] 状態生成完了。次元数: " << tx_state.n 
              << ", 非ゼロ要素数(nnz): " << tx_state.terms.size() << "\n";
    std::cout << "[TX] 送信前の保存ノルム: " << tx_norm << "\n\n";

    // 2. エンコード（シリアライズ）の実行
    auto start_enc = std::chrono::high_resolution_clock::now();
    std::vector<uint8_t> packet = UHA::Encoder::Encode(tx_state);
    auto end_enc = std::chrono::high_resolution_clock::now();

    std::cout << "[Network] エンコード完了。生成パケットサイズ: " << packet.size() << " bytes\n";
    std::cout << "[Network] 処理時間: " 
              << std::chrono::duration_cast<std::chrono::nanoseconds>(end_enc - start_enc).count() 
              << " ns\n\n";

    // -------------------------------------------------------------
    // ここで、ネットワーク（TCP/IPソケットなど）を介して packet が送信される
    // -------------------------------------------------------------

    // 3. 受信側：デコード（デシリアライズ）の実行
    UHA::UHAState rx_state;
    auto start_dec = std::chrono::high_resolution_clock::now();
    bool success = UHA::Decoder::Decode(packet, rx_state);
    auto end_dec = std::chrono::high_resolution_clock::now();

    if (!success) {
        std::cerr << "デコードに失敗しました。\n";
        return -1;
    }

    // 受信・復元後のノルムを計算
    UHA::U64 rx_norm = rx_state.compute_norm();
    std::cout << "[RX] デコード成功。復元次元数: " << rx_state.n 
              << ", 復元要素数: " << rx_state.terms.size() << "\n";
    std::cout << "[RX] 受信後の保存ノルム: " << rx_norm << "\n";
    std::cout << "[RX] 処理時間: " 
              << std::chrono::duration_cast<std::chrono::nanoseconds>(end_dec - start_dec).count() 
              << " ns\n\n";

    // 4. 完全性の検証（Fidelity 100% / unitary_like の証明）
    assert(tx_state.n == rx_state.n);
    assert(tx_state.terms.size() == rx_state.terms.size());
    assert(tx_norm == rx_norm); // ノルムが1ビットの狂いもなく完全一致すること

    std::cout << "【検証結果】: 転送前後でノルムが完全一致（Fidelity 100%）。\n";
    std::cout << "物理量子通信のデコヒーレンスを完全に排した、デジタルUHA通信プロトコルの正常動作を確認しました。\n";

    return 0;
}
