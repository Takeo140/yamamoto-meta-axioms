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

// 疎構造 mulWith の 1 項: x[j] * y[k] * val → z[i]
struct CTerm {
    int j;    // 入力 x のインデックス
    int k;    // 入力 y のインデックス
    int i;    // 出力 z のインデックス
    U64 val;  // 構造定数 c[j][k][i]
};

// UOp を定数メモリに置く（全スレッド共通）
__constant__ UOp256 d_uop;


// ===============================
//  UOp: XOR（離散ユニタリ）
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
//  norm: Σ x_i^2（離散エネルギー）
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
//  UHA256 Sparse mulWith + step
//  x → UOp → mulWith_sparse → norm
// ===============================
__global__
void kernel_uha256_sparse_step(const UHA256* __restrict__ xs,
                               const CTerm*  __restrict__ c_terms,
                               int nnz,
                               U64* __restrict__ norms,
                               int N)
{
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= N) return;

    // 1. 状態ロード
    UHA256 x = xs[idx];

    // 2. UOp 適用（離散ユニタリ）
    UHA256 y = uha_apply_uop(x);

    // 3. 疎構造 mulWith: z[i] = Σ_t x[j_t] * y[k_t] * val_t
    UHA256 z;
    #pragma unroll 32
    for (int i = 0; i < 256; ++i)
        z.coords[i] = 0;

    for (int t = 0; t < nnz; ++t) {
        CTerm ct = c_terms[t];
        U64 xj   = x.coords[ct.j];
        U64 yk   = y.coords[ct.k];
        z.coords[ct.i] += xj * yk * ct.val;
    }

    // 4. ノルム評価（離散エネルギー）
    norms[idx] = uha_norm(z);
}


// ===============================
//  Host 側（スケルトン）
// ===============================
int main() {
    constexpr int N       = 1 << 20;   // 1M 状態
    constexpr int THREADS = 256;
    constexpr int BLOCKS  = (N + THREADS - 1) / THREADS;

    // 1. UOp をホストで定義
    UOp256 h_uop{};
    for (int i = 0; i < 256; ++i)
        h_uop.mask[i] = 0x00FF00FF00FF00FFull; // 例

    // 定数メモリへコピー
    cudaMemcpyToSymbol(d_uop, &h_uop, sizeof(UOp256));

    // 2. UHA256 群と CTerm 群を確保・初期化（nnz は疎構造に応じて）
    UHA256* d_xs   = nullptr;
    CTerm*  d_ct   = nullptr;
    U64*    d_norm = nullptr;

    // cudaMalloc / cudaMemcpy で d_xs, d_ct, d_norm をセットアップ…

    int nnz = 1024; // 例：非ゼロ項数

    // 3. カーネル起動
    kernel_uha256_sparse_step<<<BLOCKS, THREADS>>>(d_xs, d_ct, nnz, d_norm, N);
    cudaDeviceSynchronize();

    // 4. 結果取得・後処理…

    return 0;
}
