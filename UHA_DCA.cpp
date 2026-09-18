License Apache 2.0  Takeo Yamamoto
// UHACore — Discrete Complex Algebraic Core (C++ port of the Lean 4 original)
//
// Ported from:
//   namespace UHACore { structure DComplex ... structure DState ... }
//
// Design intent preserved from the Lean source:
//   - No floating point anywhere. DComplex is a pair of exact integers
//     (a Gaussian integer), so every operation is exact by construction.
//   - applyX / applyZ are the discrete analogues of the Pauli X / Z gates.
//   - Both are involutions: applying either twice returns the original state.
//
// IMPORTANT — what this file does and does not give you:
//   Lean's `theorem ... := by cases s; rfl` / `simp [...]` are machine-checked
//   proofs holding for ALL DState values, verified by the Lean kernel.
//   C++ has no such kernel. The static_assert checks below verify the
//   involution property only for the specific constexpr sample values given —
//   they are compile-time *tests*, not a *proof*. If you need the same
//   universal guarantee C++ offers, this is the honest boundary: treat the
//   Lean file as the source of truth for correctness, and this file as a
//   faithful, exact-arithmetic implementation of the same definitions.

#pragma once
#include <cstdint>
#include <ostream>

namespace uhacore {

// 1. Discrete complex number (Gaussian integer pair).
// Using int64_t rather than machine `int` to match Lean's arbitrary-precision
// Int as closely as a fixed-width type can; swap in a bignum type if your
// use case can overflow 64 bits.
struct DComplex {
    int64_t re = 0;
    int64_t im = 0;

    constexpr DComplex() = default;
    constexpr DComplex(int64_t re_, int64_t im_) : re(re_), im(im_) {}

    friend constexpr bool operator==(const DComplex& a, const DComplex& b) {
        return a.re == b.re && a.im == b.im;
    }
    friend constexpr bool operator!=(const DComplex& a, const DComplex& b) {
        return !(a == b);
    }

    friend std::ostream& operator<<(std::ostream& os, const DComplex& c) {
        return os << "(" << c.re << " + " << c.im << "i)";
    }
};

namespace dcomplex {

    // Addition
    constexpr DComplex add(const DComplex& a, const DComplex& b) {
        return DComplex{a.re + b.re, a.im + b.im};
    }

    // Multiplication (standard complex product rule)
    constexpr DComplex mul(const DComplex& a, const DComplex& b) {
        return DComplex{a.re * b.re - a.im * b.im,
                         a.re * b.im + a.im * b.re};
    }

    // Negation (phase flip)
    constexpr DComplex neg(const DComplex& a) {
        return DComplex{-a.re, -a.im};
    }

} // namespace dcomplex

// 2. Discrete two-level state (discrete algebraic analogue of a qubit).
struct DState {
    DComplex amp0;
    DComplex amp1;

    friend constexpr bool operator==(const DState& a, const DState& b) {
        return a.amp0 == b.amp0 && a.amp1 == b.amp1;
    }
    friend constexpr bool operator!=(const DState& a, const DState& b) {
        return !(a == b);
    }
};

namespace dstate {

    // Transition A: discrete analogue of the Pauli X gate (state flip).
    constexpr DState applyX(const DState& s) {
        return DState{s.amp1, s.amp0};
    }

    // Transition B: discrete analogue of the Pauli Z gate (phase flip on amp1).
    constexpr DState applyZ(const DState& s) {
        return DState{s.amp0, dcomplex::neg(s.amp1)};
    }

} // namespace dstate

// 3. Compile-time sample-value checks (NOT a universal proof — see header note).
namespace uhacore_checks {

    constexpr DState kSample{DComplex{3, -5}, DComplex{-2, 7}};
    constexpr DState kZero{DComplex{0, 0}, DComplex{0, 0}};

    static_assert(dstate::applyX(dstate::applyX(kSample)) == kSample,
                  "applyX must be involutive on kSample");
    static_assert(dstate::applyX(dstate::applyX(kZero)) == kZero,
                  "applyX must be involutive on kZero");

    static_assert(dstate::applyZ(dstate::applyZ(kSample)) == kSample,
                  "applyZ must be involutive on kSample");
    static_assert(dstate::applyZ(dstate::applyZ(kZero)) == kZero,
                  "applyZ must be involutive on kZero");

} // namespace uhacore_checks

} // namespace uhacore
