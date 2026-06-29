// ComplexBit Protocol Header
// Copyright (c) 2026 Yamamoto Takeo
// License: Apache License 2.0 / CC BY 4.0

#ifndef COMPLEXBIT_PROTOCOL_HPP
#define COMPLEXBIT_PROTOCOL_HPP

#include <cstdint>
#include <cstddef>
#include <type_traits> // std::is_standard_layout 用

// CUDA環境との互換性を確保するためのデコレータマクロ
#ifndef HD_INLINE
#if defined(__CUDACC__)
#define HD_INLINE __host__ __device__ constexpr inline
#else
#define HD_INLINE constexpr inline
#endif
#endif

namespace complexbit {

constexpr std::uint8_t PROTOCOL_VERSION = 0x01;

// Flags (bitmask) を論理的にグループ化
namespace ProtocolFlags {
    constexpr std::uint8_t COMPRESSED = 0x01;
    constexpr std::uint8_t ENCRYPTED  = 0x02;
    constexpr std::uint8_t STREAM     = 0x04;
}

// メモリレイアウトを厳密に保証するためパッキングを指定 (1バイト境界)
#pragma pack(push, 1)

struct Header {
    std::uint8_t  version;
    std::uint8_t  flags;
    std::uint16_t count;
    std::uint32_t reserved; // 拡張・アライメント用 (現在は0)
};

struct ComplexBit {
    std::uint64_t real;
    std::uint64_t imag;
};

#pragma pack(pop)

// 【重要】プロトコル定義のサイズと性質が想定通りかコンパイル時に検証
static_assert(sizeof(Header) == 8, "Header size must be exactly 8 bytes");
static_assert(sizeof(ComplexBit) == 16, "ComplexBit size must be exactly 16 bytes");
static_assert(std::is_standard_layout_v<Header>, "Header must have standard layout for safe memcopy");
static_assert(std::is_standard_layout_v<ComplexBit>, "ComplexBit must have standard layout for safe memcopy");

// フレーム全体のサイズを計算（constexpr, nodiscard, noexceptで完全最適化）
[[nodiscard]] HD_INLINE std::size_t frame_size(std::uint16_t count) noexcept {
    return sizeof(Header) + sizeof(ComplexBit) * static_cast<std::size_t>(count);
}

} // namespace complexbit

#endif // COMPLEXBIT_PROTOCOL_HPP
