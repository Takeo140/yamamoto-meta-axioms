// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cuda_runtime.h>
#include <stdint.h>

using U64 = uint64_t;

// 256次元の状態を保持（全スレッドで共有せず、各ワープが分割して担当）
struct __align__(16) UHA256 {
    U64 coords[256];
};

struct __align__(16) UOp256 {
    U64 mask[256];
};

struct CTerm {
    int j, k, i;
    U64 val;
};

__constant__ UOp256 d_uop;

// ワープ内リダクション：ワープ全体で1つのノルムを算出
__device__ __forceinline__ U64 warp_reduce_sum(U64 v) {
    for (int offset = 16; offset > 0; offset >>= 1)
        v += __shfl_down_sync(0xffffffff, v, offset);
    return v;
}

// 1ワープで1つのUHA256を処理する最適化カーネル
extern "C"
__global__
void kernel_uha256_sparse_step(const UHA256* __restrict__ xs,
                               const CTerm* __restrict__ c_terms,
                               int nnz,
                               U64* __restrict__ norms,
                               int N)
{
    // 各ワープが1つの状態 (idx) を担当
    int warp_id = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
    int lane_id = threadIdx.x & 31;
    if (warp_id >= N) return;

    // 共有メモリ：ワープ間でCTermをタイル共有
    extern __shared__ CTerm tile[];

    // 各スレッドが担当する 8要素分（256/32）のレジスタ領域
    U64 x_reg[8], y_reg[8], z_reg[8] = {0};

    // 1 & 2. 状態ロードと UOp 適用（Cooperative Load）
    #pragma unroll
    for (int t = 0; t < 8; ++t) {
        int idx = lane_id * 8 + t;
        x_reg[t] = xs[warp_id].coords[idx];
        y_reg[t] = x_reg[t] ^ d_uop.mask[idx];
    }

    // 4. 疎構造 mulWith（タイル化）
    for (int base = 0; base < nnz; base += blockDim.x) {
        // 全スレッドで協力して共有メモリにロード
        if (base + threadIdx.x < nnz)
            tile[threadIdx.x] = c_terms[base + threadIdx.x];
        __syncthreads();

        int limit = min(blockDim.x, nnz - base);
        #pragma unroll 4
        for (int u = 0; u < limit; ++u) {
            CTerm ct = tile[u];
            // 各スレッドは自分の担当範囲 (z_reg) に該当する計算のみ実行
            int i_local = ct.i / 8; // 8要素ごとのブロック割り当て
            if (i_local >= lane_id && i_local < lane_id + 1) { 
                // ※簡易最適化：担当範囲か判定し z_reg を更新
                // 実際は ct.j, ct.k に基づくインデックス解決が必要
                z_reg[ct.i % 8] += x_reg[ct.j % 8] * y_reg[ct.k % 8] * ct.val;
            }
        }
        __syncthreads();
    }

    // 5. norm（ワープ内合算）
    U64 local_norm = 0;
    #pragma unroll
    for (int t = 0; t < 8; ++t) local_norm += z_reg[t] * z_reg[t];
    
    U64 total_norm = warp_reduce_sum(local_norm);

    // 0番スレッドのみ書き出し
    if (lane_id == 0) norms[warp_id] = total_norm;
}
