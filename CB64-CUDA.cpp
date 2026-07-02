Lisense Apache 2.0  Takeo Yamamoto
#pragma once
#include <cuda_runtime.h>
#include <cstdint>

// Core types (using unsigned long long for 64-bit parity with U64/BitVec 64)
using U64 = std::uint64_t;

// ---------------------------------------------------------------------------
// Section 1: Device-Optimized Branchless Core
// ---------------------------------------------------------------------------

// __forceinline__ を付与し、関数呼び出しのオーバーヘッドを完全排除
__forceinline__ __host__ __device__ U64 nonzeroMask(U64 x) {
    return ((-static_cast<std::int64_t>(x)) | x) >> 63;
}

__forceinline__ __host__ __device__ U64 branchlessSelect(U64 control, U64 a, U64 b) {
    U64 m = nonzeroMask(control);
    return a * m + b * (1 - m);
}

// ---------------------------------------------------------------------------
// Section 2: Algebraic Structures (Complex/Quat)
// ---------------------------------------------------------------------------

struct ComplexBit {
    U64 real, imag;

    __host__ __device__ ComplexBit operator*(const ComplexBit& o) const {
        return { real * o.real - imag * o.imag, 
                 real * o.imag + imag * o.real };
    }
};

// ---------------------------------------------------------------------------
// Section 3: Parallel BSCM Kernel
// ---------------------------------------------------------------------------

__device__ __forceinline__ U64 bscmDelta(U64 s) {
    // 剰余演算はコストが高いため、ビット演算で代替可能だが、
    // コンパイラによる最適化が効くためこのままでも十分高速
    return (s % 2 == 0) ? (s >> 1) : ((s + 1) >> 1);
}

/**
 * BSCM並列実行カーネル
 * @param d_states: 各スレッドの現在の状態（入出力兼用）
 * @param input: 現在のステップの共通入力値
 */
__global__ void bscmParallelKernel(U64* d_states, U64 input, int numStates) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < numStates) {
        // 状態更新: (currentState + externalInput) を δ に適用
        // 整数加算は 2^64 でラップするため、自然に BitVec 64 と同値
        d_states[idx] = bscmDelta(d_states[idx] + input);
    }
}
