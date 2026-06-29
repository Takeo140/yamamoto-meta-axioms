#include "protocol.hpp"
#include <cstring>   // std::memcpy
#include <vector>

using namespace complexbit;

// branchless decode: contiguous frame → Header + array of ComplexBit
inline Header decode_header(const std::uint8_t* frame) {
    Header h{};
    std::memcpy(&h, frame, sizeof(Header));
    return h;
}

inline void decode_payload(const std::uint8_t* frame,
                           const Header& h,
                           ComplexBit* out_data)
{
    const std::uint8_t* payload = frame + sizeof(Header);
    std::size_t payload_bytes = sizeof(ComplexBit) * static_cast<std::size_t>(h.count);
    std::memcpy(out_data, payload, payload_bytes);
}

// example usage (no networking, just buffer parse)
int main() {
    // 仮の受信フレーム（encode側と同じものを想定）
    ComplexBit arr[2] = {
        {0x12345678ABCDEF00ULL, 0xCAFEBABEDEADBEEFULL},
        {0x0011223344556677ULL, 0x8899AABBCCDDEEFFULL}
    };

    Header h_send{};
    h_send.version  = PROTOCOL_VERSION;
    h_send.flags    = 0;
    h_send.count    = 2;
    h_send.reserved = 0;

    std::vector<std::uint8_t> frame(frame_size(h_send.count));
    // 再利用：encode と同じロジックでフレームを作る
    std::memcpy(frame.data(), &h_send, sizeof(Header));
    std::memcpy(frame.data() + sizeof(Header), arr,
                sizeof(ComplexBit) * static_cast<std::size_t>(h_send.count));

    // ここから decode
    Header h_recv = decode_header(frame.data());

    std::vector<ComplexBit> recv_arr(h_recv.count);
    decode_payload(frame.data(), h_recv, recv_arr.data());

    // recv_arr に複素数ビットが復元されている
    return 0;
}
