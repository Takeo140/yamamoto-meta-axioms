// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cuda_runtime.h>
#include <stdint.h>

using U64 = uint64_t;

// ===============================
//  UHA256 / UOp256 / Sparse CTerm
// ===============================
struct __align__(16) UHA256 {
    U64 coords[256];
};

struct __align__(16) UOp256 {
    U64 mask[256];
};

// 疎構造 mulWith の 1 項
struct CTerm {
    int j;    // x[j]
    int k;    // y[k]
    int i;    // z[i]
    U64 val;  // c[j][k][i]
};

// UOp を定数メモリに置く
__constant__ UOp256 d_uop;


// ===============================
//  UOp: XOR（離散ユニタリ）
// ===============================
__device__ __forceinline__
void uha_apply_uop(const UHA256& x, UHA256& y) {
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        y.coords[i] = x.coords[i] ^ d_uop.mask[i];
}


// ===============================
//  norm: warp reduce で高速化
// ===============================
__device__ __forceinline__
U64 warp_reduce_sum(U64 v) {
    for (int offset = 16; offset > 0; offset >>= 1)
        v += __shfl_down_sync(0xffffffff, v, offset);
    return v;
}

__device__ __forceinline__
U64 uha_norm(const UHA256& x) {
    U64 local = 0;

    // 各スレッドが 8 要素ずつ担当（256 / 32 = 8）
    int tid = threadIdx.x & 31;
    int base = tid * 8;

    #pragma unroll
    for (int t = 0; t < 8; ++t) {
        U64 v = x.coords[base + t];
        local += v * v;
    }

    // warp 内で reduce
    return warp_reduce_sum(local);
}


// ===============================
//  UHA256 Sparse mulWith + step
// ===============================
extern "C"
__global__
void kernel_uha256_sparse_step(const UHA256* __restrict__ xs,
                               const CTerm*  __restrict__ c_terms,
                               int nnz,
                               U64* __restrict__ norms,
                               int N)
{
    // 共有メモリに CTerm をタイル化
    extern __shared__ CTerm tile[];

    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. 状態ロード（レジスタ保持）
    UHA256 x = xs[idx];
    UHA256 y, z;

    // 2. UOp 適用
    uha_apply_uop(x, y);

    // 3. z をゼロ初期化
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        z.coords[i] = 0;

    // 4. 疎構造 mulWith（タイル化）
    for (int base = 0; base < nnz; base += blockDim.x) {

        int t = base + threadIdx.x;
        if (t < nnz)
            tile[threadIdx.x] = c_terms[t];

        __syncthreads();

        int limit = min(blockDim.x, nnz - base);

        #pragma unroll 4
        for (int u = 0; u < limit; ++u) {
            CTerm ct = tile[u];
            z.coords[ct.i] += x.coords[ct.j] * y.coords[ct.k] * ct.val;
        }

        __syncthreads();
    }

    // 5. norm（warp reduce）
    U64 n = uha_norm(z);

    // warp の lane0 が書き込む
    if ((threadIdx.x & 31) == 0)
        norms[idx] = n;
}
