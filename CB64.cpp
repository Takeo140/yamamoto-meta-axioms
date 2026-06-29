// ComplexBit Ultra Core: Unified Algebraic-Geometric Branchless Engine
// C++ Practical Backend (CUDA-friendly, but CPUでも動作可能)
//
// Copyright (c) 2026 Yamamoto Takeo
// License: Apache License 2.0 / CC BY 4.0

#include <cstdint>
#include <optional>

// U64: C/Rust の u64 に対応する 64bit ビットベクトル
using U64 = std::uint64_t;

/* §1. U64 ビット演算補題と branchless コア
 *
 * Lean 側の補題:
 *  - x ≠ 0 → ((-x) ||| x) >>> 63 = 1
 *  - x = 0 → ((-x) ||| x) >>> 63 = 0
 *  - 常に 0 または 1
 */

// 非ゼロ判定を 0/1 マスクに変換する branchless ビットトリック
inline U64 nonzeroMask(U64 x) {
    U64 negx = ~x + 1ULL;      // -x (2の補数)
    return (negx | x) >> 63;   // MSB を取り出す
}

// ゼロマスク：nonzeroMask の補集合
inline U64 zeroMask(U64 x) {
    return 1ULL - nonzeroMask(x);
}

// 分岐排除選択器：control ≠ 0 なら a、そうでなければ b
inline U64 branchlessSelect(U64 control, U64 a, U64 b) {
    U64 m = nonzeroMask(control);      // 0 or 1
    return a * m + b * (1ULL - m);    // Lean の定義そのまま
}

/* §2. ComplexBit：代数構造付き複素数ビット型 */

struct ComplexBit {
    U64 real;
    U64 imag;

    ComplexBit() : real(0), imag(0) {}
    ComplexBit(U64 r, U64 i) : real(r), imag(i) {}
};

// 加算
inline ComplexBit operator+(const ComplexBit& c1, const ComplexBit& c2) {
    return ComplexBit{
        c1.real + c2.real,
        c1.imag + c2.imag
    };
}

// 乗算（オーバーフロー込みの擬似複素数環）
inline ComplexBit operator*(const ComplexBit& c1, const ComplexBit& c2) {
    return ComplexBit{
        c1.real * c2.real - c1.imag * c2.imag,
        c1.real * c2.imag + c1.imag * c2.real
    };
}

// 零元
inline ComplexBit complexZero() {
    return ComplexBit{0, 0};
}

// 単位元（1）
inline ComplexBit complexOne() {
    return ComplexBit{1, 0};
}

// 虚数単位 I
inline ComplexBit complexI() {
    return ComplexBit{0, 1};
}

// 符号反転
inline ComplexBit operator-(const ComplexBit& c) {
    return ComplexBit{
        static_cast<U64>(-static_cast<std::int64_t>(c.real)),
        static_cast<U64>(-static_cast<std::int64_t>(c.imag))
    };
}

// 実部だけから ComplexBit を作る
inline ComplexBit complexOfReal(U64 x) {
    return ComplexBit{x, 0};
}

// 虚部だけから ComplexBit を作る
inline ComplexBit complexOfImag(U64 y) {
    return ComplexBit{0, y};
}

// 共役複素数
inline ComplexBit complexConj(const ComplexBit& c) {
    return ComplexBit{
        c.real,
        static_cast<U64>(-static_cast<std::int64_t>(c.imag))
    };
}

// 90度回転（i を掛けるのに対応）
inline ComplexBit complexRotate90(const ComplexBit& c) {
    return ComplexBit{
        static_cast<U64>(-static_cast<std::int64_t>(c.imag)),
        c.real
    };
}

/* §3. QuatBit：四元数ビット構造 */

struct QuatBit {
    U64 w;
    U64 x;
    U64 y;
    U64 z;

    QuatBit() : w(0), x(0), y(0), z(0) {}
    QuatBit(U64 w_, U64 x_, U64 y_, U64 z_)
        : w(w_), x(x_), y(y_), z(z_) {}
};

inline QuatBit quatZero() {
    return QuatBit{0, 0, 0, 0};
}

inline QuatBit quatOne() {
    return QuatBit{1, 0, 0, 0};
}

// Hamilton 積（オーバーフロー込み四元数積）
inline QuatBit operator*(const QuatBit& q1, const QuatBit& q2) {
    return QuatBit{
        q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z,
        q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y,
        q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x,
        q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w
    };
}

inline QuatBit quatUnitI() { return QuatBit{0, 1, 0, 0}; }
inline QuatBit quatUnitJ() { return QuatBit{0, 0, 1, 0}; }
inline QuatBit quatUnitK() { return QuatBit{0, 0, 0, 1}; }

/* §4. BitLayer 型クラス：ビットレイヤー抽象
 *
 * C++ ではテンプレートでざっくり表現
 */

template <typename T>
struct BitLayer;

// U64 の BitLayer
template <>
struct BitLayer<U64> {
    static U64 inject(U64 x) { return x; }
    static U64 extract(U64 x) { return x; }
    static U64 liftOp(U64 (*f)(U64), U64 x) { return f(x); }
    static U64 add(U64 a, U64 b) { return a + b; }
};

// ComplexBit の BitLayer（real を主ビットとみなす）
template <>
struct BitLayer<ComplexBit> {
    static ComplexBit inject(U64 x) { return ComplexBit{x, 0}; }
    static U64 extract(const ComplexBit& c) { return c.real; }
    static ComplexBit liftOp(U64 (*f)(U64), const ComplexBit& c) {
        return ComplexBit{f(c.real), c.imag};
    }
    static ComplexBit add(const ComplexBit& a, const ComplexBit& b) {
        return a + b;
    }
};

/* §5. BSCM：Bounded Smooth Collatz Machine（複素数ビット版） */

struct BSCMStateCB {
    ComplexBit state;
    U64        bound;
    U64        step;
};

// 1 ステップ分の Collatz 風更新（分岐排除＋バウンドチェック付き）
inline std::optional<BSCMStateCB> bscmStepCB(const BSCMStateCB& s) {
    if (s.step >= s.bound) {
        return std::nullopt;
    } else {
        U64 n = s.state.real;
        U64 odd_mask    = n & 1ULL;
        U64 even_result = n >> 1;
        U64 odd_result  = 3ULL * n + 1ULL;
        U64 next_n      = branchlessSelect(odd_mask, odd_result, even_result);
        BSCMStateCB next{
            ComplexBit{next_n, s.state.imag + 1},
            s.bound,
            s.step + 1
        };
        return next;
    }
}

/* §6. 簡単な動作確認用 example 相当 */

inline bool example_branchlessSelect() {
    U64 r = branchlessSelect(1ULL, 10ULL, 20ULL);
    return (r == 10ULL);
}

inline bool example_conj_conj(const ComplexBit& c) {
    ComplexBit cc = complexConj(complexConj(c));
    return (cc.real == c.real && cc.imag == c.imag);
}
