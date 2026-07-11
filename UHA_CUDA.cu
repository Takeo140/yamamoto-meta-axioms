// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cuda_runtime.h>
#include <stdint.h>
#include <cstdio>

using U64 = uint64_t;

// ===============================
// Lean: norm64 = popcount
// ===============================
__device__ __forceinline__
int norm64(U64 x) {
    return __popcll(x);
}

// ===============================
// Lean: UOp.apply (XOR)
// ===============================
template<int N>
__device__ __forceinline__
void uop_apply(const U64* __restrict__ x,
               const U64* __restrict__ mask,
               U64* __restrict__ y)
{
    #pragma unroll
    for (int i = 0; i < N; ++i)
        y[i] = x[i] ^ mask[i];
}

// ===============================
// Lean: norm_vec = Σ popcount(x[i])
// ===============================
template<int N>
__device__ __forceinline__
int norm_vec(const U64* __restrict__ v)
{
    int s = 0;
    #pragma unroll
    for (int i = 0; i < N; ++i)
        s += norm64(v[i]);
    return s;
}

// ===============================
// warp 内 min reduce
// ===============================
__device__ __forceinline__
int warpReduceMin(int v) {
    for (int offset = 16; offset > 0; offset >>= 1) {
        int other = __shfl_down_sync(0xffffffff, v, offset);
        v = v < other ? v : other;
    }
    return v;
}

// ===============================
// UHA step kernel (修正版)
// ===============================
template<int N>
__global__
void uha_step_kernel(const U64* __restrict__ start,
                     const U64* __restrict__ mask,
                     int steps,
                     int* __restrict__ out_norm)
{
    int tid_global = blockIdx.x * blockDim.x + threadIdx.x;
    int lane       = threadIdx.x & 31;

    U64 cur[N];
    U64 tmp[N];

    // 改善版：i 依存のハッシュで探索空間を広げる
    #pragma unroll
    for (int i = 0; i < N; ++i)
        cur[i] = start[i] ^
                 (U64)(tid_global * 0x9E3779B97F4A7C15ull +
                       i         * 0xD1B54A32D192ED03ull);

    int best = norm_vec<N>(cur);

    // UHA step iteration
    for (int k = 0; k < steps; ++k) {

        uop_apply<N>(cur, mask, tmp);

        #pragma unroll
        for (int i = 0; i < N; ++i)
            cur[i] = tmp[i];

        int n = norm_vec<N>(cur);
        if (n < best) best = n;
    }

    // warp 内 reduce
    int warp_min = warpReduceMin(best);

    // block 内 reduce（可変 warp 数）
    extern __shared__ int s_block_min[];
    if (lane == 0) {
        int warp_id = threadIdx.x >> 5;
        s_block_min[warp_id] = warp_min;
    }
    __syncthreads();

    if (threadIdx.x == 0) {
        int warp_count = blockDim.x >> 5;
        int block_min = s_block_min[0];
        for (int w = 1; w < warp_count; ++w)
            block_min = block_min < s_block_min[w] ? block_min : s_block_min[w];

        atomicMin(out_norm, block_min);
    }
}

// ===============================
// main
// ===============================
int main() {

    constexpr int N = 4;
    constexpr int STEPS = 2000000;   // 改善：現実的なステップ数

    U64 h_start[N] = {0xFFFFull, 0x0Full, 0xF0ull, 0xAAAAull};
    U64 h_mask[N]  = {0x00FFull, 0x00FFull, 0x00FFull, 0x00FFull};

    U64 *d_start = nullptr;
    U64 *d_mask  = nullptr;
    int *d_out   = nullptr;

    int h_out = 999999;

    cudaMalloc(&d_start, sizeof(U64) * N);
    cudaMalloc(&d_mask,  sizeof(U64) * N);
    cudaMalloc(&d_out,   sizeof(int));

    cudaMemcpy(d_start, h_start, sizeof(U64) * N, cudaMemcpyHostToDevice);
    cudaMemcpy(d_mask,  h_mask,  sizeof(U64) * N, cudaMemcpyHostToDevice);
    cudaMemcpy(d_out,   &h_out,  sizeof(int),    cudaMemcpyHostToDevice);

    constexpr int THREADS = 256;     // warp 8 個
    constexpr int BLOCKS  = 512;     // 探索器 131072 個

    int shared_bytes = (THREADS / 32) * sizeof(int);

    uha_step_kernel<N><<<BLOCKS, THREADS, shared_bytes>>>(d_start, d_mask, STEPS, d_out);
    cudaDeviceSynchronize();

    cudaMemcpy(&h_out, d_out, sizeof(int), cudaMemcpyDeviceToHost);

    printf("best_norm = %d\n", h_out);

    cudaFree(d_start);
    cudaFree(d_mask);
    cudaFree(d_out);

    return 0;
}
