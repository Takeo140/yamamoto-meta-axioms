License Apache 2.0 Takeo Yamamoto
// TakeoUnifiedPhysicsAI_CUDA.cu
// 統合物理AIエンジン CUDA版（古典物理 + AI制御 + 量子計算 + 宇宙物理）

#include <cstdio>
#include <cmath>
#include <vector>
#include <cuda_runtime.h>

/*******************************************************
 * 共通構造体
 *******************************************************/

struct NeuralNet {
    float w1, b1;
    float w2, b2;
};

__device__ __host__ inline float relu(float x) {
    return x > 0.0f ? x : 0.0f;
}

__device__ __host__ inline float forwardNN(const NeuralNet& nn, float x) {
    float h = relu(x * nn.w1 + nn.b1);
    return h * nn.w2 + nn.b2;
}

struct State {
    float x, v, m;
};

struct PhysParams {
    float dt, friction, damping;
    NeuralNet nn;
};

struct Complex {
    float re, im;
};

__device__ __host__ inline Complex cadd(const Complex& a, const Complex& b) {
    return Complex{ a.re + b.re, a.im + b.im };
}

__device__ __host__ inline Complex cmul(const Complex& a, const Complex& b) {
    return Complex{
        a.re * b.re - a.im * b.im,
        a.re * b.im + a.im * b.re
    };
}

__device__ __host__ inline float cnorm2(const Complex& a) {
    return a.re * a.re + a.im * a.im;
}

struct QState {
    Complex a, b;
};

struct U2 {
    Complex u00, u01, u10, u11;
};

struct Vec2 {
    float x, y;
};

__device__ __host__ inline Vec2 vadd(const Vec2& a, const Vec2& b) {
    return Vec2{ a.x + b.x, a.y + b.y };
}

__device__ __host__ inline Vec2 vscale(float s, const Vec2& v) {
    return Vec2{ s * v.x, s * v.y };
}

__device__ __host__ inline float vnorm(const Vec2& v) {
    return sqrtf(v.x * v.x + v.y * v.y);
}

struct AstroState {
    Vec2 r;
    Vec2 v;
    float m;
};

struct AstroParams {
    float dt, G, M;
    NeuralNet nn;
};

/*******************************************************
 * 古典物理 + AI制御 (GPUカーネル)
 *******************************************************/

__global__
void physicsStepAI_kernel(State* states, PhysParams p, int N) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= N) return;

    State s = states[i];
    float Fext_ai = forwardNN(p.nn, s.x);
    float a = (Fext_ai - p.friction * s.v - p.damping * s.v) / s.m;
    float newV = s.v + a * p.dt;
    float newX = s.x + newV * p.dt;
    states[i] = State{ newX, newV, s.m };
}

/*******************************************************
 * 量子計算 (GPUカーネル)
 *******************************************************/

__global__
void applyGate_kernel(QState* qs, U2 U, int N) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= N) return;

    QState q = qs[i];
    Complex a_new = cadd(cmul(U.u00, q.a), cmul(U.u01, q.b));
    Complex b_new = cadd(cmul(U.u10, q.a), cmul(U.u11, q.b));
    qs[i] = QState{ a_new, b_new };
}

__global__
void measure_kernel(QState* qs, int* results, int N) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= N) return;

    QState q = qs[i];
    results[i] = cnorm2(q.a) >= cnorm2(q.b) ? 0 : 1;
}

/*******************************************************
 * 宇宙物理 (GPUカーネル)
 *******************************************************/

__global__
void astroStepAI_kernel(AstroState* states, AstroParams p, int N) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= N) return;

    AstroState s = states[i];

    float r_norm = vnorm(s.r);
    float dist3 = r_norm * r_norm * r_norm;
    float ag_mag = -(p.G * p.M) / dist3;

    Vec2 ag = vscale(ag_mag, s.r);
    Vec2 a_ai = Vec2{ forwardNN(p.nn, s.r.x), forwardNN(p.nn, s.r.y) };
    Vec2 a_total = vadd(ag, vscale(1.0f / s.m, a_ai));

    Vec2 newV = vadd(s.v, vscale(p.dt, a_total));
    Vec2 newR = vadd(s.r, vscale(p.dt, newV));

    states[i] = AstroState{ newR, newV, s.m };
}

/*******************************************************
 * ホスト側ユーティリティ
 *******************************************************/

void checkCuda(cudaError_t err, const char* msg) {
    if (err != cudaSuccess) {
        std::fprintf(stderr, "CUDA Error (%s): %s\n", msg, cudaGetErrorString(err));
        std::exit(1);
    }
}

/*******************************************************
 * 統合 example
 *******************************************************/

int main() {
    std::printf("=== Takeo Unified Physics & AI Engine (CUDA版) 起動 ===\n");

    // [1] 古典物理 + AI制御 (GPUで並列ステップ)
    int N_classical = 100000;
    State* d_statesC;
    PhysParams pC;
    pC.dt = 0.01f;
    pC.friction = 0.05f;
    pC.damping = 0.02f;
    pC.nn = NeuralNet{ 0.1f, 0.0f, -0.1f, 0.0f };

    checkCuda(cudaMalloc(&d_statesC, N_classical * sizeof(State)), "malloc statesC");
    // 初期化：全部同じ初期状態にしておく
    std::vector<State> h_initC(N_classical, State{0.0f, 0.0f, 1.0f});
    checkCuda(cudaMemcpy(d_statesC, h_initC.data(),
                         N_classical * sizeof(State),
                         cudaMemcpyHostToDevice),
              "memcpy statesC init");

    dim3 block(256);
    dim3 grid((N_classical + block.x - 1) / block.x);
    physicsStepAI_kernel<<<grid, block>>>(d_statesC, pC, N_classical);
    checkCuda(cudaDeviceSynchronize(), "physicsStepAI_kernel");

    std::vector<State> h_statesC(N_classical);
    checkCuda(cudaMemcpy(h_statesC.data(), d_statesC,
                         N_classical * sizeof(State),
                         cudaMemcpyDeviceToHost),
              "memcpy statesC back");

    std::printf("[古典AI] サンプル: 最終状態 x=%f, v=%f\n",
                h_statesC.back().x, h_statesC.back().v);

    // [2] 量子計算 (GPUで並列ゲート適用)
    int N_quantum = 1024;
    QState* d_qs;
    checkCuda(cudaMalloc(&d_qs, N_quantum * sizeof(QState)), "malloc qs");

    std::vector<QState> h_qs(N_quantum, QState{{1.0f, 0.0f}, {0.0f, 0.0f}});
    checkCuda(cudaMemcpy(d_qs, h_qs.data(),
                         N_quantum * sizeof(QState),
                         cudaMemcpyHostToDevice),
              "memcpy qs init");

    U2 H;
    H.u00 = {0.707f, 0.0f};
    H.u01 = {0.707f, 0.0f};
    H.u10 = {0.707f, 0.0f};
    H.u11 = {-0.707f, 0.0f};

    dim3 gridQ((N_quantum + block.x - 1) / block.x);
    applyGate_kernel<<<gridQ, block>>>(d_qs, H, N_quantum);
    checkCuda(cudaDeviceSynchronize(), "applyGate_kernel");

    int* d_results;
    checkCuda(cudaMalloc(&d_results, N_quantum * sizeof(int)), "malloc results");
    measure_kernel<<<gridQ, block>>>(d_qs, d_results, N_quantum);
    checkCuda(cudaDeviceSynchronize(), "measure_kernel");

    std::vector<int> h_results(N_quantum);
    checkCuda(cudaMemcpy(h_results.data(), d_results,
                         N_quantum * sizeof(int),
                         cudaMemcpyDeviceToHost),
              "memcpy results back");

    std::printf("[量子計算] サンプル測定結果: %d\n", h_results[0]);

    // [3] 宇宙物理 (GPUで軌道ステップ)
    int N_astro = 100000;
    AstroState* d_statesA;
    AstroParams pA;
    pA.dt = 0.01f;
    pA.G  = 1.0f;
    pA.M  = 100.0f;
    pA.nn = pC.nn;

    checkCuda(cudaMalloc(&d_statesA, N_astro * sizeof(AstroState)), "malloc statesA");
    std::vector<AstroState> h_initA(N_astro, AstroState{{10.0f, 0.0f}, {0.0f, 1.0f}, 1.0f});
    checkCuda(cudaMemcpy(d_statesA, h_initA.data(),
                         N_astro * sizeof(AstroState),
                         cudaMemcpyHostToDevice),
              "memcpy statesA init");

    dim3 gridA((N_astro + block.x - 1) / block.x);
    astroStepAI_kernel<<<gridA, block>>>(d_statesA, pA, N_astro);
    checkCuda(cudaDeviceSynchronize(), "astroStepAI_kernel");

    std::vector<AstroState> h_statesA(N_astro);
    checkCuda(cudaMemcpy(h_statesA.data(), d_statesA,
                         N_astro * sizeof(AstroState),
                         cudaMemcpyDeviceToHost),
              "memcpy statesA back");

    std::printf("[宇宙軌道] サンプル: X=%f, Y=%f\n",
                h_statesA.back().r.x, h_statesA.back().r.y);

    // 後片付け
    cudaFree(d_statesC);
    cudaFree(d_qs);
    cudaFree(d_results);
    cudaFree(d_statesA);

    std::printf("=== CUDA版統合実行完了 ===\n");
    return 0;
}
