// ComplexBit Ultra Core: Unified Algebraic-Geometric Branchless Engine
// C++ Practical Backend (CUDA-friendly, CPU互換)
//
// Copyright (c) 2026 Yamamoto Takeo
// License: CC BY 4.0 Apache 2.0

#include <cstdint>

// CUDA環境との互換性を確保するためのデコレータマクロ
#ifndef HD_INLINE
#if defined(__CUDACC__)
#define HD_INLINE __host__ __device__ constexpr inline
#else
#define HD_INLINE constexpr inline
#endif
#endif

// U64: C/Rust の u64 に対応する 64bit ビットベクトル
using U64 = std::uint64_t;

/* §1. U64 ビット演算補題と branchless コア
 *
 * Lean 側の補題:
 * - x ≠ 0 → ((-x) ||| x) >>> 63 = 1
 * - x = 0 → ((-x) ||| x) >>> 63 = 0
 * - 常に 0 または 1
 */

// 非ゼロ判定を 0/1 マスクに変換する branchless ビットトリック
[[nodiscard]] HD_INLINE U64 nonzeroMask(U64 x) {
    // ~x + 1ULL は -x と等価（C++標準の2の補数モジュロ演算）
    return ((-x) | x) >> 63;
}

// ゼロマスク：nonzeroMask の補集合
[[nodiscard]] HD_INLINE U64 zeroMask(U64 x) {
    return 1ULL - nonzeroMask(x);
}

// 分岐排除選択器：control ≠ 0 なら a、そうでなければ b
[[nodiscard]] HD_INLINE U64 branchlessSelect(U64 control, U64 a, U64 b) {
    U64 m = nonzeroMask(control);
    // Lean定義: a * m + b * (1ULL - m)
    // 実装最適化: 乗算を避け、全ビット0または1のマスクを生成して論理演算を行う
    U64 mask = 0ULL - m; // m=1 なら 0xFFF...FFF, m=0 なら 0x0
    return (a & mask) | (b & ~mask);
}

/* §2. ComplexBit：代数構造付き複素数ビット型 */

struct ComplexBit {
    U64 real;
    U64 imag;

    HD_INLINE ComplexBit() : real(0), imag(0) {}
    HD_INLINE ComplexBit(U64 r, U64 i) : real(r), imag(i) {}
};

// 加算
[[nodiscard]] HD_INLINE ComplexBit operator+(const ComplexBit& c1, const ComplexBit& c2) {
    return ComplexBit{c1.real + c2.real, c1.imag + c2.imag};
}

// 乗算（オーバーフロー込みの擬似複素数環）
[[nodiscard]] HD_INLINE ComplexBit operator*(const ComplexBit& c1, const ComplexBit& c2) {
    return ComplexBit{
        c1.real * c2.real - c1.imag * c2.imag,
        c1.real * c2.imag + c1.imag * c2.real
    };
}

// 零元
[[nodiscard]] HD_INLINE ComplexBit complexZero() { return ComplexBit{0, 0}; }

// 単位元（1）
[[nodiscard]] HD_INLINE ComplexBit complexOne() { return ComplexBit{1, 0}; }

// 虚数単位 I
[[nodiscard]] HD_INLINE ComplexBit complexI() { return ComplexBit{0, 1}; }

// 符号反転
// U64の単項マイナスは2の補数演算として安全かつ標準に準拠
[[nodiscard]] HD_INLINE ComplexBit operator-(const ComplexBit& c) {
    return ComplexBit{-c.real, -c.imag};
}

// 実部だけから ComplexBit を作る
[[nodiscard]] HD_INLINE ComplexBit complexOfReal(U64 x) { return ComplexBit{x, 0}; }

// 虚部だけから ComplexBit を作る
[[nodiscard]] HD_INLINE ComplexBit complexOfImag(U64 y) { return ComplexBit{0, y}; }

// 共役複素数
[[nodiscard]] HD_INLINE ComplexBit complexConj(const ComplexBit& c) {
    return ComplexBit{c.real, -c.imag};
}

// 90度回転（i を掛けるのに対応）
[[nodiscard]] HD_INLINE ComplexBit complexRotate90(const ComplexBit& c) {
    return ComplexBit{-c.imag, c.real};
}

/* §3. QuatBit：四元数ビット構造 */

struct QuatBit {
    U64 w, x, y, z;

    HD_INLINE QuatBit() : w(0), x(0), y(0), z(0) {}
    HD_INLINE QuatBit(U64 w_, U64 x_, U64 y_, U64 z_) : w(w_), x(x_), y(y_), z(z_) {}
};

[[nodiscard]] HD_INLINE QuatBit quatZero() { return QuatBit{0, 0, 0, 0}; }
[[nodiscard]] HD_INLINE QuatBit quatOne()  { return QuatBit{1, 0, 0, 0}; }

// Hamilton 積（オーバーフロー込み四元数積）
[[nodiscard]] HD_INLINE QuatBit operator*(const QuatBit& q1, const QuatBit& q2) {
    return QuatBit{
        q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z,
        q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y,
        q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x,
        q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w
    };
}

[[nodiscard]] HD_INLINE QuatBit quatUnitI() { return QuatBit{0, 1, 0, 0}; }
[[nodiscard]] HD_INLINE QuatBit quatUnitJ() { return QuatBit{0, 0, 1, 0}; }
[[nodiscard]] HD_INLINE QuatBit quatUnitK() { return QuatBit{0, 0, 0, 1}; }

/* §4. BitLayer 型クラス：ビットレイヤー抽象 */

template <typename T>
struct BitLayer;

// U64 の BitLayer
template <>
struct BitLayer<U64> {
    static HD_INLINE U64 inject(U64 x) { return x; }
    static HD_INLINE U64 extract(U64 x) { return x; }
    static HD_INLINE U64 liftOp(U64 (*f)(U64), U64 x) { return f(x); }
    static HD_INLINE U64 add(U64 a, U64 b) { return a + b; }
};

// ComplexBit の BitLayer（real を主ビットとみなす）
template <>
struct BitLayer<ComplexBit> {
    static HD_INLINE ComplexBit inject(U64 x) { return ComplexBit{x, 0}; }
    static HD_INLINE U64 extract(const ComplexBit& c) { return c.real; }
    static HD_INLINE ComplexBit liftOp(U64 (*f)(U64), const ComplexBit& c) {
        return ComplexBit{f(c.real), c.imag};
    }
    static HD_INLINE ComplexBit add(const ComplexBit& a, const ComplexBit& b) {
        return a + b;
    }
};

/* §5. BSCM：Bounded Smooth Collatz Machine（複素数ビット版） */

struct BSCMStateCB {
    ComplexBit state;
    U64        bound;
    U64        step;
};

// std::optionalの代わりとなる、GPU対応のResult構造体
struct BSCMResult {
    BSCMStateCB data;
    bool        valid;
};

// 1 ステップ分の Collatz 風更新（完全分岐排除＋バウンドチェック付き）
[[nodiscard]] HD_INLINE BSCMResult bscmStepCB(const BSCMStateCB& s) {
    U64 n = s.state.real;
    U64 odd_mask    = n & 1ULL;
    U64 even_result = n >> 1;
    U64 odd_result  = 3ULL * n + 1ULL;
    
    U64 next_n = branchlessSelect(odd_mask, odd_result, even_result);
    
    BSCMStateCB next{
        ComplexBit{next_n, s.state.imag + 1},
        s.bound,
        s.step + 1
    };
    
    // バウンドチェックも分岐を使わずにフラグ化する
    bool is_valid = (s.step < s.bound);
    return BSCMResult{next, is_valid};
}

/* §6. 簡単な動作確認用 example 相当 */

[[nodiscard]] HD_INLINE bool example_branchlessSelect() {
    U64 r = branchlessSelect(1ULL, 10ULL, 20ULL);
    return (r == 10ULL);
}

[[nodiscard]] HD_INLINE bool example_conj_conj(const ComplexBit& c) {
    ComplexBit cc = complexConj(complexConj(c));
    return (cc.real == c.real && cc.imag == c.imag);
}

#include <iostream>
#include <vector>
#include <chrono>
#include <iomanip>

// 性能評価用の構造体
struct BenchmarkResult {
    U64 start_val;
    U64 steps;
    U64 overflow_count;
    double duration_ns;
};

// 性能評価用メイン関数
int main() {
    // 性能測定用入力セット（小規模～極大値まで）
    std::vector<U64> test_inputs = {6, 27, 100, 0x123456789ABCDEF0ULL, 0xFFFFFFFFFFFFFFFFULL};
    
    std::cout << "--- Bounded Smooth Collatz Machine: Performance Benchmark ---" << std::endl;
    std::cout << "Input,Steps,Overflows,Time_ns" << std::endl;

    for (U64 start_val : test_inputs) {
        BSCMStateCB state{ complexOfReal(start_val), 1000000, 0 }; // ステップ制限を拡大
        U64 overflow_count = 0;
        U64 prev_n = start_val;

        // 計測開始
        auto start_time = std::chrono::high_resolution_clock::now();
        
        for (U64 i = 0; i < state.bound; ++i) {
            BSCMResult res = bscmStepCB(state);
            U64 current_n = res.data.state.real;

            // オーバーフロー検知
            bool is_odd = (prev_n & 1ULL);
            if ((is_odd && (current_n <= prev_n)) || (!is_odd && (current_n > prev_n))) {
                overflow_count++;
            }

            if (current_n == 1ULL || !res.valid) {
                state = res.data;
                break;
            }
            state = res.data;
            prev_n = current_n;
        }

        // 計測終了
        auto end_time = std::chrono::high_resolution_clock::now();
        double duration = std::chrono::duration<double, std::nano>(end_time - start_time).count();

        // 結果出力（CSV形式）
        std::cout << start_val << "," 
                  << state.step << "," 
                  << overflow_count << "," 
                  << duration << std::endl;
    }

    return 0;
}
