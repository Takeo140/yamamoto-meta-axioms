// License Apache 2.0  Takeo Yamamoto
#pragma once
#include <cuda_runtime.h>
#include <cstdint>

using U64 = std::uint64_t;

// ---------------------------------------------------------------------------
// Section 1: Device-Optimized Branchless Core (Safe Version)
// ---------------------------------------------------------------------------

// 完全に unsigned のみで -x を定義（mod 2^64 で安全に動作）
__forceinline__ __host__ __device__ U64 nonzeroMask(U64 x) {
    U64 neg = 0 - x;              // unsigned の 2^64 wrap-around
    return (neg | x) >> 63;       // MSB が 1 → 非ゼロ
}

__forceinline__ __host__ __device__ U64 branchlessSelect(U64 control, U64 a, U64 b) {
    U64 m = nonzeroMask(control);
    return a * m + b * (1 - m);
}

// ---------------------------------------------------------------------------
// Section 2: Algebraic Structures (ComplexBit)
// ---------------------------------------------------------------------------

struct ComplexBit {
    U64 real, imag;

    __host__ __device__ __forceinline__
    ComplexBit operator*(const ComplexBit& o) const {
        return {
            real * o.real - imag * o.imag,
            real * o.imag + imag * o.real
        };
    }
};

// ---------------------------------------------------------------------------
// Section 3: Parallel BSCM Kernel
// ---------------------------------------------------------------------------

__device__ __forceinline__ U64 bscmDelta(U64 s) {
    // s % 2 は s & 1 に置き換え可能だが、最適化で同等になる
    return (s & 1ULL) == 0 ? (s >> 1) : ((s + 1) >> 1);
}

__global__ void bscmParallelKernel(U64* d_states, U64 input, int numStates) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < numStates) {
        d_states[idx] = bscmDelta(d_states[idx] + input);
    }
}
