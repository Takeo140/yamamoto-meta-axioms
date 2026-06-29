#include "protocol.hpp"
#include <cstring>   // std::memcpy
#include <vector>

using namespace complexbit;

// branchless encode: Header + array of ComplexBit → contiguous frame
inline void encode_frame(const Header& h,
                         const ComplexBit* data,
                         std::uint8_t* out_buffer)
{
    // Header (8 bytes)
    std::memcpy(out_buffer, &h, sizeof(Header));

    // Payload: count × ComplexBit (16 bytes each)
    std::size_t payload_bytes = sizeof(ComplexBit) * static_cast<std::size_t>(h.count);
    std::memcpy(out_buffer + sizeof(Header), data, payload_bytes);
}

// example usage (no networking, just buffer build)
int main() {
    // prepare some ComplexBit data
    ComplexBit arr[2] = {
        {0x12345678ABCDEF00ULL, 0xCAFEBABEDEADBEEFULL},
        {0x0011223344556677ULL, 0x8899AABBCCDDEEFFULL}
    };

    Header h{};
    h.version  = PROTOCOL_VERSION;
    h.flags    = 0;          // no compression/encryption/stream for now
    h.count    = 2;
    h.reserved = 0;

    std::vector<std::uint8_t> frame(frame_size(h.count));
    encode_frame(h, arr, frame.data());

    // ここで frame.data() をそのままソケット送信などに使える
    return 0;
}
