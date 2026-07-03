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
// 基本ノルム：Σ x_i^2
// ===============================
__device__ __forceinline__
U64 uha_norm(const UHA256& x) {
    U64 acc = 0;
    #pragma unroll 32
    for (int i = 0; i < 256; ++i) {
        U64 v = x.coords[i];
        acc += v * v;
    }
    return acc;
}

// ===============================
// UOp: XOR（離散ユニタリ）
// ===============================
__device__ __forceinline__
UHA256 uha_apply_uop(const UHA256& x) {
    UHA256 r;
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        r.coords[i] = x.coords[i] ^ d_uop.mask[i];
    return r;
}

// ===============================
// mulWith: 多元代数乗法（疎構造前提）
// c_idx: 非ゼロ項の (j,k,i) インデックス
// c_val: 対応する係数
// nnz  : 非ゼロ項数
// ===============================
struct CTerm {
    int j, k, i;
    U64 val;
};

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

    // 3. mulWith（疎構造版）
    UHA256 z;
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        z.coords[i] = 0;

    // Blackwell/H100 系 INT64 積和を素直に叩く
    for (int t = 0; t < nnz; ++t) {
        CTerm ct = c_terms[t];
        U64 xj = x.coords[ct.j];
        U64 yk = y.coords[ct.k];
        z.coords[ct.i] += xj * yk * ct.val;
    }

    // 4. ノルム評価
    norms[idx] = uha_norm(z);
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
        h_uop.mask[i] = 0x00FF00FF00FF00FFull; // 例

    // 定数メモリへコピー
    cudaMemcpyToSymbol(d_uop, &h_uop, sizeof(UOp256));

    // UHA256 群と CTerm 群を確保・初期化（省略）
    UHA256* d_xs   = nullptr;
    CTerm*  d_ct   = nullptr;
    U64*    d_norm = nullptr;

    // cudaMalloc / cudaMemcpy などを行う…

    kernel_uha256_step<<<BLOCKS, THREADS>>>(d_xs, d_ct, /*nnz*/ 1024, d_norm, N);
    cudaDeviceSynchronize();

    // 結果取得・後処理…

    return 0;
}
