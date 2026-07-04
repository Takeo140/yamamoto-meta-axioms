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
// Lean: step = apply → norm
// CUDA: warp 並列探索器 + block 集約
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

    // Lean: x₀ = start ⊕ tid
    #pragma unroll
    for (int i = 0; i < N; ++i)
        cur[i] = start[i] ^ (U64)(tid_global * 0x9E3779B97F4A7C15ull);

    int best = norm_vec<N>(cur);

    // Lean: step iteration
    for (int k = 0; k < steps; ++k) {

        // x := UOp.apply(x)
        uop_apply<N>(cur, mask, tmp);

        #pragma unroll
        for (int i = 0; i < N; ++i)
            cur[i] = tmp[i];

        // norm(x)
        int n = norm_vec<N>(cur);
        if (n < best) best = n;
    }

    // warp 内で最小値
    int warp_min = warpReduceMin(best);

    // block 内で warp の最小値を shared に集約
    __shared__ int s_block_min[32]; // 最大 32 warp/block を想定
    if (lane == 0) {
        int warp_id = threadIdx.x >> 5;
        s_block_min[warp_id] = warp_min;
    }
    __syncthreads();

    // block 内の最小値を 1 スレッドが計算
    if (threadIdx.x == 0) {
        int block_min = s_block_min[0];
        int warp_count = blockDim.x >> 5;
        for (int w = 1; w < warp_count; ++w)
            block_min = block_min < s_block_min[w] ? block_min : s_block_min[w];

        // グローバル最小値を atomicMin（block ごとに 1 回）
        atomicMin(out_norm, block_min);
    }
}

// ===============================
// main
// ===============================
int main() {

    constexpr int N = 4;
    constexpr int STEPS = 10000000;

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

    // Lean: 多状態並列 → CUDA: 多スレッド並列
    constexpr int THREADS = 32;     // 1 warp
    constexpr int BLOCKS  = 1024;   // 1024 warp = 32768 探索器

    uha_step_kernel<N><<<BLOCKS, THREADS>>>(d_start, d_mask, STEPS, d_out);
    cudaDeviceSynchronize();

    cudaMemcpy(&h_out, d_out, sizeof(int), cudaMemcpyDeviceToHost);

    printf("best_norm = %d\n", h_out);

    cudaFree(d_start);
    cudaFree(d_mask);
    cudaFree(d_out);

    return 0;
}
