#ifndef COMPLEXBIT_PROTOCOL_HPP
#define COMPLEXBIT_PROTOCOL_HPP

#include <cstdint>
#include <cstddef>

namespace complexbit {

constexpr std::uint8_t PROTOCOL_VERSION = 0x01;

// Flags (bitmask)
constexpr std::uint8_t FLAG_COMPRESSED = 0x01;
constexpr std::uint8_t FLAG_ENCRYPTED  = 0x02;
constexpr std::uint8_t FLAG_STREAM     = 0x04;

struct Header {
    std::uint8_t  version;
    std::uint8_t  flags;
    std::uint16_t count;
    std::uint32_t reserved; // 0 for now
};

struct ComplexBit {
    std::uint64_t real;
    std::uint64_t imag;
};

inline std::size_t frame_size(std::uint16_t count) {
    return sizeof(Header) + sizeof(ComplexBit) * static_cast<std::size_t>(count);
}

} // namespace complexbit

#endif // COMPLEXBIT_PROTOCOL_HPP
