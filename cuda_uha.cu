// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cstdio>
#include <cstdint>

using U64 = unsigned long long;

// ===============================
//  GPU popcount
// ===============================
__device__ __forceinline__ int norm64(U64 x) {
    return __popcll(x);
}

// ===============================
//  UOp: ノルム保存作用素 (XOR)
// ===============================
template<int N>
__device__ __forceinline__
void apply(const U64* x, const U64* mask, U64* y) {
    #pragma unroll
    for (int i = 0; i < N; ++i)
        y[i] = x[i] ^ mask[i];
}

// ===============================
//  ノルム計算
// ===============================
template<int N>
__device__ __forceinline__
int norm_vec(const U64* v) {
    int s = 0;
    #pragma unroll
    for (int i = 0; i < N; ++i)
        s += norm64(v[i]);
    return s;
}

// ===============================
//  UHA GPU kernel
// ===============================
template<int N>
__global__
void uha_kernel(const U64* start, const U64* mask, int steps, int* out_norm) {
    U64 cur[N];
    U64 tmp[N];

    // 初期化
    #pragma unroll
    for (int i = 0; i < N; ++i)
        cur[i] = start[i];

    int best = norm_vec<N>(cur);

    // 探索ループ
    for (int k = 0; k < steps; ++k) {
        apply<N>(cur, mask, tmp);

        #pragma unroll
        for (int i = 0; i < N; ++i)
            cur[i] = tmp[i];

        int n = norm_vec<N>(cur);
        if (n < best) best = n;
    }

    // 結果を返す
    *out_norm = best;
}

// ===============================
//  main
// ===============================
int main() {
    constexpr int N = 4;
    constexpr int STEPS = 100000000;

    U64 h_start[N] = {0xFFFFull, 0x0Full, 0xF0ull, 0xAAAAull};
    U64 h_mask[N]  = {0x00FFull, 0x00FFull, 0x00FFull, 0x00FFull};

    U64 *d_start, *d_mask;
    int *d_out, h_out;

    cudaMalloc(&d_start, sizeof(U64) * N);
    cudaMalloc(&d_mask,  sizeof(U64) * N);
    cudaMalloc(&d_out,   sizeof(int));

    cudaMemcpy(d_start, h_start, sizeof(U64) * N, cudaMemcpyHostToDevice);
    cudaMemcpy(d_mask,  h_mask,  sizeof(U64) * N, cudaMemcpyHostToDevice);

    // 1ブロック1スレッド（Minimal Spec）
    uha_kernel<N><<<1,1>>>(d_start, d_mask, STEPS, d_out);

    cudaMemcpy(&h_out, d_out, sizeof(int), cudaMemcpyDeviceToHost);

    printf("best_norm = %d\n", h_out);

    cudaFree(d_start);
    cudaFree(d_mask);
    cudaFree(d_out);

    return 0;
}
