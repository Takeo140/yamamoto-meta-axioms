// ComplexBit Protocol Decoder
// Copyright (c) 2026 Yamamoto Takeo
// License: CC BY 4.0  Apache 2.0

#include "protocol.hpp"
#include <cstring>   // std::memcpy
#include <vector>
#include <span>      // std::span (C++20)
#include <cassert>

using namespace complexbit;

// branchless decode: contiguous frame → Header
// std::span により、読み込み元のバッファサイズを安全に管理
inline Header decode_header(std::span<const std::uint8_t> frame) {
    // ヘッダサイズ未満の不正なフレームをブロック
    assert(frame.size() >= sizeof(Header) && "Frame is too small to contain a header");
    
    Header h{};
    std::memcpy(&h, frame.data(), sizeof(Header));
    return h;
}

// decode_payload: 連らなったフレームからペイロードを抽出
inline void decode_payload(std::span<const std::uint8_t> frame,
                           const Header& h,
                           std::span<ComplexBit> out_data)
{
    std::size_t payload_bytes = sizeof(ComplexBit) * static_cast<std::size_t>(h.count);
    
    // 1. 受信フレーム内に指定されたサイズのペイロードが本当に存在するか（オーバーリード防止）
    assert(frame.size() >= sizeof(Header) + payload_bytes && "Incomplete frame payload");
    
    // 2. 受け手側のバッファが十分なサイズを持っているか（オーバーフロー防止）
    assert(out_data.size() >= h.count && "Output buffer is too small");

    if (payload_bytes > 0) {
        const std::uint8_t* payload_start = frame.data() + sizeof(Header);
        std::memcpy(out_data.data(), payload_start, payload_bytes);
    }
}

// example usage (no networking, just buffer parse)
int main() {
    // 仮の受信フレーム生成（エンコード処理のシミュレーション）
    ComplexBit arr[2] = {
        {0x12345678ABCDEF00ULL, 0xCAFEBABEDEADBEEFULL},
        {0x0011223344556677ULL, 0x8899AABBCCDDEEFFULL}
    };

    Header h_send{};
    h_send.version  = PROTOCOL_VERSION;
    h_send.flags    = 0;
    h_send.count    = 2;
    h_send.reserved = 0;

    // フレーム構築
    std::vector<std::uint8_t> frame(frame_size(h_send.count));
    std::memcpy(frame.data(), &h_send, sizeof(Header));
    std::memcpy(frame.data() + sizeof(Header), arr, sizeof(ComplexBit) * 2);

    // ==========================================
    // ここから Decode 処理
    // ==========================================
    
    // std::vector をそのまま渡すと std::span へ安全に暗黙変換される
    Header h_recv = decode_header(frame);

    // ヘッダの情報を元に受信用のバッファを確保
    std::vector<ComplexBit> recv_arr(h_recv.count);
    
    // ペイロードの復元
    decode_payload(frame, h_recv, recv_arr);

    // recv_arr に複素数ビットが安全に復元されている
    return 0;
}
