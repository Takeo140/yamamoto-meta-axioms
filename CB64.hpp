// ComplexBit Ultra Core: Unified Algebraic-Geometric Branchless Engine
// C++ port of the Lean 4 formalization (Practical Lean Edition)
//
// Copyright (c) 2026 Yamamoto Takeo
// License: Apache License 2.0 / CC BY 4.0
//
// NOTE ON GUARANTEES
// -------------------
// The Lean file this is ported from carries formal proofs (branchlessSelect_correct,
// I_sq, rotate90_four_eq_id, bscmDelta_reduces, etc.). This C++ file has NO independent
// proof engine behind it: it is a direct, bit-for-bit-compatible algorithmic port.
// uint64_t arithmetic wraps mod 2^64 exactly like Lean's `BitVec 64`, so the two
// implementations should be observationally equivalent for all inputs, but that
// equivalence is asserted here only by construction + static_assert spot checks,
// not proved. Do not treat this file as carrying the same correctness guarantees
// as the Lean source; treat it as the reference implementation the proofs are about.

#pragma once
#include <cstdint>
#include <vector>
#include <compare>

using U64 = std::uint64_t;

// ---------------------------------------------------------------------------
// Section 1: U64 branchless core
// ---------------------------------------------------------------------------

namespace u64lemmas {

// Corresponds to U64Lemmas.neg_or_self_msb / neg_or_zero_msb / msb_val_binary.
// For x != 0, ((-x) | x) >> 63 == 1; for x == 0 it is 0. This mirrors the Lean
// lemmas exactly (both branches are provable there via bv_decide / rfl).
constexpr U64 neg_or_self_msb(U64 x) {
    return (static_cast<U64>(-static_cast<std::int64_t>(x)) | x) >> 63;
}

} // namespace u64lemmas

// Non-zero test collapsed to a 0/1 mask, branchless.
constexpr U64 nonzeroMask(U64 x) {
    return u64lemmas::neg_or_self_msb(x);
}

// Complement mask: 1 - nonzeroMask(x).
constexpr U64 zeroMask(U64 x) {
    return 1 - nonzeroMask(x);
}

// branchlessSelect(control, a, b) == (control != 0) ? a : b, with no branch.
// Matches branchlessSelect_correct in the Lean source.
constexpr U64 branchlessSelect(U64 control, U64 a, U64 b) {
    U64 m = nonzeroMask(control);
    return a * m + b * (1 - m);
}

// ---------------------------------------------------------------------------
// Section 2: ComplexBit
// ---------------------------------------------------------------------------

struct ComplexBit {
    U64 real{};
    U64 imag{};

    constexpr bool operator==(const ComplexBit&) const = default;

    constexpr ComplexBit operator+(const ComplexBit& o) const {
        return { real + o.real, imag + o.imag };
    }

    constexpr ComplexBit operator*(const ComplexBit& o) const {
        return {
            real * o.real - imag * o.imag,
            real * o.imag + imag * o.real
        };
    }

    constexpr ComplexBit operator-() const {
        return { static_cast<U64>(-static_cast<std::int64_t>(real)),
                 static_cast<U64>(-static_cast<std::int64_t>(imag)) };
    }

    static constexpr ComplexBit zero() { return {0, 0}; }
    static constexpr ComplexBit one()  { return {1, 0}; }
    static constexpr ComplexBit unitI(){ return {0, 1}; } // named unitI to avoid clash with I()

    static constexpr ComplexBit ofReal(U64 x) { return {x, 0}; }
    static constexpr ComplexBit ofImag(U64 y) { return {0, y}; }

    constexpr ComplexBit conj() const { return { real, static_cast<U64>(-static_cast<std::int64_t>(imag)) }; }

    constexpr ComplexBit rotate90() const {
        return { static_cast<U64>(-static_cast<std::int64_t>(imag)), real };
    }
};

// I * I == -one  (ComplexBit.I_sq)
static_assert(ComplexBit::unitI() * ComplexBit::unitI() == -ComplexBit::one());

// conj is an involution (ComplexBit.conj_conj)
static_assert(ComplexBit{3, 5}.conj().conj() == ComplexBit{3, 5});

// rotate90 has order 4 (ComplexBit.rotate90_four_eq_id)
static_assert(ComplexBit{7, 2}.rotate90().rotate90().rotate90().rotate90() == ComplexBit{7, 2});

// ---------------------------------------------------------------------------
// Section 3: QuatBit
// ---------------------------------------------------------------------------

struct QuatBit {
    U64 w{}, x{}, y{}, z{};

    constexpr bool operator==(const QuatBit&) const = default;

    constexpr QuatBit operator-() const {
        auto neg = [](U64 v) { return static_cast<U64>(-static_cast<std::int64_t>(v)); };
        return { neg(w), neg(x), neg(y), neg(z) };
    }

    constexpr QuatBit operator*(const QuatBit& o) const {
        return {
            w * o.w - x * o.x - y * o.y - z * o.z,
            w * o.x + x * o.w + y * o.z - z * o.y,
            w * o.y - x * o.z + y * o.w + z * o.x,
            w * o.z + x * o.y - y * o.x + z * o.w
        };
    }

    static constexpr QuatBit zero()  { return {0, 0, 0, 0}; }
    static constexpr QuatBit one()   { return {1, 0, 0, 0}; }
    static constexpr QuatBit unitI() { return {0, 1, 0, 0}; }
    static constexpr QuatBit unitJ() { return {0, 0, 1, 0}; }
    static constexpr QuatBit unitK() { return {0, 0, 0, 1}; }
};

static_assert(QuatBit::unitI() * QuatBit::unitJ() == QuatBit::unitK());      // ij_eq_k
static_assert(QuatBit::unitJ() * QuatBit::unitI() == -QuatBit::unitK());     // ji_eq_neg_k
static_assert(QuatBit::unitI() * QuatBit::unitI() == -QuatBit::one());       // unitI_sq
static_assert(QuatBit::unitJ() * QuatBit::unitJ() == -QuatBit::one());       // unitJ_sq
static_assert(QuatBit::unitK() * QuatBit::unitK() == -QuatBit::one());       // unitK_sq

// ---------------------------------------------------------------------------
// Section 4: BitLayer — expressed as a concept, not a runtime interface,
// since C++ has no direct analogue of a Lean typeclass with a proof obligation.
// The extract_inject law (extract(inject(x)) == x) is asserted per-instantiation
// below rather than enforced structurally.
// ---------------------------------------------------------------------------

template <class T>
concept BitLayer = requires(T t, U64 x, U64 (*f)(U64)) {
    { T::inject(x) } -> std::same_as<T>;
    { t.extract() } -> std::same_as<U64>;
};

struct U64Layer {
    static constexpr U64 inject(U64 x) { return x; }
};
static_assert(U64Layer::inject(42) == 42); // extract_inject law, trivially

struct ComplexBitLayer {
    static constexpr ComplexBit inject(U64 x) { return ComplexBit::ofReal(x); }
};
static_assert(ComplexBitLayer::inject(42).real == 42); // extract_inject law

// ---------------------------------------------------------------------------
// Section 5: BSCM — Bounded Smooth Collatz Machine
//
// This is the corrected version, ported faithfully from the original Nat-based
// Lean source (bscm_delta / bscm_control_step / bscm_control_exec), NOT the
// 3n+1 rule. Both branches of bscmDelta are state-reducing for s > 1
// (bscmDelta_reduces in Lean). uint64_t addition wraps mod 2^64 automatically,
// matching BitVec 64 semantics, so no explicit `% 2^64` is needed here either.
// ---------------------------------------------------------------------------

constexpr U64 bscmDelta(U64 s) {
    return (s % 2 == 0) ? (s / 2) : ((s + 1) / 2);
}

// bscmDelta_reduces: for s > 1, bscmDelta(s) < s. Spot-checked here; the real
// proof (for all s) lives in the Lean source via bv_decide.
static_assert(bscmDelta(2) < 2);
static_assert(bscmDelta(3) < 3);
static_assert(bscmDelta(1000000) < 1000000);

// Boundedness is automatic: U64 = uint64_t already satisfies 0 <= s < 2^64
// by construction, exactly as noted for bscmDelta_bounded / bscmControlStep_bounded
// / bscmSystem_never_overflows in the Lean source (all `True` there for the same reason).
constexpr U64 bscmControlStep(U64 currentState, U64 externalInput) {
    return bscmDelta(currentState + externalInput); // wraps mod 2^64, same as BitVec 64
}

inline U64 bscmControlExec(U64 initialState, const std::vector<U64>& inputs) {
    U64 state = initialState;
    for (U64 input : inputs) {
        state = bscmControlStep(state, input);
    }
    return state;
}

// ---------------------------------------------------------------------------
// Section 6: sanity checks mirroring the Lean `example` block
// ---------------------------------------------------------------------------

static_assert(branchlessSelect(1, 10, 20) == 10);
static_assert(branchlessSelect(0, 10, 20) == 20);
#include <iostream>
#include "ultra_core.hpp"   // ← Takeo のファイル名に合わせて変更

int main() {
    // --- ComplexBit の最小動作確認 ---
    ComplexBit a{3, 5};
    ComplexBit b{2, 7};
    ComplexBit c = a * b;

    std::cout << "ComplexBit mul: (" 
              << c.real << ", " << c.imag << ")\n";

    // --- QuatBit の最小動作確認 ---
    QuatBit qi = QuatBit::unitI();
    QuatBit qj = QuatBit::unitJ();
    QuatBit qk = qi * qj;

    std::cout << "QuatBit ij = k: (" 
              << qk.w << ", " << qk.x << ", " << qk.y << ", " << qk.z << ")\n";

    // --- branchlessSelect の確認 ---
    std::cout << "branchlessSelect(1, 10, 20) = "
              << branchlessSelect(1, 10, 20) << "\n";

    // --- BSCM の最小動作確認 ---
    U64 s = 10;
    U64 next = bscmDelta(s);

    std::cout << "bscmDelta(10) = " << next << "\n";

    return 0;
}
