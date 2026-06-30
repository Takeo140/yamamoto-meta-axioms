#include "protocol.hpp"
#include <cstring>   // std::memcpy
#include <vector>
#include <span>      // std::span (C++20)
#include <cassert>

using namespace complexbit;

// encode_frame: Header + array of ComplexBit → contiguous frame
// std::span を用いることで、バッファサイズとデータサイズの不整合を安全に防ぐ
inline void encode_frame(const Header& h,
                         std::span<const ComplexBit> data,
                         std::span<std::uint8_t> out_buffer)
{
    // Payloadのサイズ計算
    std::size_t payload_bytes = sizeof(ComplexBit) * data.size();
    
    // 出力先バッファがヘッダ＋ペイロードを格納するのに十分なサイズか検証
    assert(out_buffer.size() >= sizeof(Header) + payload_bytes && "Buffer overflow detected");

    // 1. Header (8 bytes) のコピー
    std::memcpy(out_buffer.data(), &h, sizeof(Header));

    // 2. Payload のコピー
    // data が空 (count == 0) の場合、nullptr を std::memcpy に渡す未定義動作を回避
    if (payload_bytes > 0) {
        std::memcpy(out_buffer.data() + sizeof(Header), data.data(), payload_bytes);
    }
}

// 実行例 (ネットワーク等のバッファビルドシミュレーション)
int main() {
    // 送信データの準備
    ComplexBit arr[] = {
        {0x12345678ABCDEF00ULL, 0xCAFEBABEDEADBEEFULL},
        {0x0011223344556677ULL, 0x8899AABBCCDDEEFFULL}
    };

    Header h{};
    h.version  = PROTOCOL_VERSION;
    h.flags    = 0; // 圧縮・暗号化なし
    h.count    = static_cast<std::uint16_t>(std::size(arr)); // マジックナンバーを排除
    h.reserved = 0;

    // 必要な総フレームサイズを計算してバッファを確保
    std::size_t total_size = frame_size(h.count);
    std::vector<std::uint8_t> frame(total_size);

    // C++20 std::span によって暗黙的に安全な変換が行われる
    encode_frame(h, arr, frame);

    // ここで frame.data() と frame.size() を用いて
    // ソケット送信 (send) や ファイル書き込み (write) を実行可能
    
    return 0;
}

