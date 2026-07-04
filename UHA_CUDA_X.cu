// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cuda_runtime.h>
#include <stdint.h>

using U64 = uint64_t;

// ===============================
// UHA256 / UOp256 型
// ===============================
struct __align__(16) UHA256 {
    U64 coords[256];
};

struct __align__(16) UOp256 {
    U64 mask[256];
};

// 定数メモリ：全スレッド共通 UOp
__constant__ UOp256 d_uop;

// ===============================
// warp reduce (U64)
// ===============================
__device__ __forceinline__
U64 warpReduceSum(U64 v) {
    for (int offset = 16; offset > 0; offset >>= 1)
        v += __shfl_down_sync(0xffffffff, v, offset);
    return v;
}

// ===============================
// 基本ノルム：Σ x_i^2
// ===============================
__device__ __forceinline__
U64 uha_norm(const UHA256& x) {
    U64 acc = 0;
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        acc += x.coords[i] * x.coords[i];
    return acc;
}

// ===============================
// UOp: XOR（離散ユニタリ）
// 128-bit LD/ST で高速化
// ===============================
__device__ __forceinline__
UHA256 uha_apply_uop(const UHA256& x) {
    UHA256 r;

    const uint4* px = reinterpret_cast<const uint4*>(&x.coords[0]);
    const uint4* pm = reinterpret_cast<const uint4*>(&d_uop.mask[0]);
    uint4* pr      = reinterpret_cast<uint4*>(&r.coords[0]);

    #pragma unroll 64
    for (int i = 0; i < 256/4; ++i) {
        uint4 vx = px[i];
        uint4 vm = pm[i];
        pr[i] = make_uint4(vx.x ^ vm.x,
                           vx.y ^ vm.y,
                           vx.z ^ vm.z,
                           vx.w ^ vm.w);
    }
    return r;
}

// ===============================
// CTerm（疎構造）
// ===============================
struct CTerm {
    int j, k, i;
    U64 val;
};

// ===============================
// mulWith（warp-level）
// ===============================
__device__ __forceinline__
void mulWith_sparse_warp(const UHA256& x,
                         const UHA256& y,
                         const CTerm* __restrict__ s_terms,
                         int nnz,
                         U64* __restrict__ out256)
{
    int lane = threadIdx.x & 31;

    // 局所 256 要素（レジスタに載らないのでローカル）
    U64 partial[256];
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        partial[i] = 0;

    // warp 分割
    for (int t = lane; t < nnz; t += 32) {
        CTerm ct = s_terms[t];
        U64 xj = x.coords[ct.j];
        U64 yk = y.coords[ct.k];
        partial[ct.i] += xj * yk * ct.val;
    }

    // warp reduce
    #pragma unroll 32
    for (int i = 0; i < 256; ++i) {
        U64 v = partial[i];
        v = warpReduceSum(v);
        if (lane == 0)
            out256[i] = v;
    }
}

// ===============================
// kernel
// ===============================
__global__
void kernel_uha256_step(const UHA256* __restrict__ xs,
                        const CTerm* __restrict__ c_terms,
                        int nnz,
                        U64* __restrict__ norms,
                        int N)
{
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. 状態ロード
    UHA256 x = xs[idx];

    // 2. UOp 適用
    UHA256 y = uha_apply_uop(x);

    // 3. CTerm を shared に展開
    extern __shared__ CTerm s_terms[];
    for (int t = threadIdx.x; t < nnz; t += blockDim.x)
        s_terms[t] = c_terms[t];
    __syncthreads();

    // 4. mulWith（warp-level）
    __shared__ U64 z256[256];
    mulWith_sparse_warp(x, y, s_terms, nnz, z256);

    __syncthreads();

    // 5. ノルム
    if ((threadIdx.x & 31) == 0) {
        UHA256 z;
        #pragma unroll 32
        for (int i = 0; i < 256; ++i)
            z.coords[i] = z256[i];
        norms[idx] = uha_norm(z);
    }
}

// ===============================
// host 側（スケルトン）
// ===============================
int main() {
    constexpr int N = 1 << 20;   // 1M 状態
    constexpr int THREADS = 256;
    constexpr int BLOCKS  = (N + THREADS - 1) / THREADS;

    // UOp256 をホストで定義
    UOp256 h_uop{};
    for (int i = 0; i < 256; ++i)
        h_uop.mask[i] = 0x00FF00FF00FF00FFull;

    cudaMemcpyToSymbol(d_uop, &h_uop, sizeof(UOp256));

    // UHA256 群と CTerm 群を確保（省略）
    UHA256* d_xs   = nullptr;
    CTerm*  d_ct   = nullptr;
    U64*    d_norm = nullptr;

    // cudaMalloc / cudaMemcpy など…

    size_t shmem = sizeof(CTerm) * 1024;

    kernel_uha256_step<<<BLOCKS, THREADS, shmem>>>(d_xs, d_ct, 1024, d_norm, N);
    cudaDeviceSynchronize();

    return 0;
}
