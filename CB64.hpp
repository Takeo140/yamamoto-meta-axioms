// ComplexBit Ultra Core: Unified Algebraic-Geometric Branchless Engine
// C++ port of the Lean 4 formalization (Practical Lean Edition)
//
// Copyright (c) 2026 Yamamoto Takeo
// License: Apache License 2.0 / CC BY 4.0

#pragma once
#include <cstdint>
#include <vector>
#include <concepts>   // for std::same_as

using U64 = std::uint64_t;

// ---------------------------------------------------------------------------
// Section 1: U64 branchless core
// ---------------------------------------------------------------------------

namespace u64lemmas {

constexpr U64 neg_or_self_msb(U64 x) {
    return (static_cast<U64>(-static_cast<std::int64_t>(x)) | x) >> 63;
}

} // namespace u64lemmas

constexpr U64 nonzeroMask(U64 x) {
    return u64lemmas::neg_or_self_msb(x);
}

constexpr U64 zeroMask(U64 x) {
    return 1 - nonzeroMask(x);
}

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
    static constexpr ComplexBit unitI(){ return {0, 1}; }

    static constexpr ComplexBit ofReal(U64 x) { return {x, 0}; }
    static constexpr ComplexBit ofImag(U64 y) { return {0, y}; }

    constexpr ComplexBit conj() const {
        return { real, static_cast<U64>(-static_cast<std::int64_t>(imag)) };
    }

    constexpr ComplexBit rotate90() const {
        return { static_cast<U64>(-static_cast<std::int64_t>(imag)), real };
    }
};

static_assert(ComplexBit::unitI() * ComplexBit::unitI() == -ComplexBit::one());
static_assert(ComplexBit{3, 5}.conj().conj() == ComplexBit{3, 5});
static_assert(ComplexBit{7, 2}.rotate90().rotate90().rotate90().rotate90()
              == ComplexBit{7, 2});

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

static_assert(QuatBit::unitI() * QuatBit::unitJ() == QuatBit::unitK());
static_assert(QuatBit::unitJ() * QuatBit::unitI() == -QuatBit::unitK());
static_assert(QuatBit::unitI() * QuatBit::unitI() == -QuatBit::one());
static_assert(QuatBit::unitJ() * QuatBit::unitJ() == -QuatBit::one());
static_assert(QuatBit::unitK() * QuatBit::unitK() == -QuatBit::one());

// ---------------------------------------------------------------------------
// Section 4: BitLayer
// ---------------------------------------------------------------------------

template <class T>
concept BitLayer = requires(T t, U64 x) {
    { T::inject(x) } -> std::same_as<T>;
    { t.extract() }  -> std::same_as<U64>;
};

struct U64Layer {
    U64 value{};
    static constexpr U64Layer inject(U64 x) { return U64Layer{x}; }
    constexpr U64 extract() const { return value; }
};
static_assert(U64Layer::inject(42).extract() == 42);

struct ComplexBitLayer {
    ComplexBit value{};
    static constexpr ComplexBitLayer inject(U64 x) {
        return ComplexBitLayer{ComplexBit::ofReal(x)};
    }
    constexpr U64 extract() const { return value.real; }
};
static_assert(ComplexBitLayer::inject(42).extract() == 42);

// ---------------------------------------------------------------------------
// Section 5: BSCM
// ---------------------------------------------------------------------------

constexpr U64 bscmDelta(U64 s) {
    return (s % 2 == 0) ? (s / 2) : ((s + 1) / 2);
}

static_assert(bscmDelta(2) < 2);
static_assert(bscmDelta(3) < 3);
static_assert(bscmDelta(1000000) < 1000000);

constexpr U64 bscmControlStep(U64 currentState, U64 externalInput) {
    return bscmDelta(currentState + externalInput);
}

inline U64 bscmControlExec(U64 initialState, const std::vector<U64>& inputs) {
    U64 state = initialState;
    for (U64 input : inputs) {
        state = bscmControlStep(state, input);
    }
    return state;
}

// ---------------------------------------------------------------------------
// Section 6: sanity checks
// ---------------------------------------------------------------------------

static_assert(branchlessSelect(1, 10, 20) == 10);
static_assert(branchlessSelect(0, 10, 20) == 20);

#include <iostream>
#include "ultra_core.hpp"

int main() {
    ComplexBit a{3, 5};
    ComplexBit b{2, 7};
    ComplexBit c = a * b;

    std::cout << "ComplexBit mul: (" 
              << c.real << ", " << c.imag << ")\n";

    QuatBit qi = QuatBit::unitI();
    QuatBit qj = QuatBit::unitJ();
    QuatBit qk = qi * qj;

    std::cout << "QuatBit ij = k: (" 
              << qk.w << ", " << qk.x << ", " << qk.y << ", " << qk.z << ")\n";

    std::cout << "branchlessSelect(1, 10, 20) = "
              << branchlessSelect(1, 10, 20) << "\n";

    U64 s = 10;
    U64 next = bscmDelta(s);
    std::cout << "bscmDelta(10) = " << next << "\n";

    return 0;
}
