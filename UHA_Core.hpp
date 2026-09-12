// License Apache 2.0
// Copyright (c) Takeo Yamamoto

#include <cstdint>
#include <cstddef>
#include <vector>
#include <stdexcept>

namespace uha {

using U64 = std::uint64_t;

/*
 * ============================================================
 * UHA Computational Core
 *
 * Carrier:
 *     U64 = Z / (2^64) Z
 *
 * State:
 *     x in U64^n
 *
 * Bilinear product:
 *     (x * y)_i
 *       = sum_j sum_k x_j y_k C[j,k,i]
 *
 * Nonlinear map:
 *     F(x) = x * x
 *
 * State transition:
 *     x' = x + active * (F(x) - x)
 *
 * Halt:
 *     active = 1 - halt
 *
 * All arithmetic naturally wraps modulo 2^64.
 * ============================================================
 */


/*
 * ------------------------------------------------------------
 * UHA n-dimensional carrier
 * ------------------------------------------------------------
 */
struct State {
    std::vector<U64> x;

    explicit State(std::size_t n)
        : x(n, 0) {}

    explicit State(std::vector<U64> values)
        : x(std::move(values)) {}

    std::size_t size() const noexcept {
        return x.size();
    }

    U64& operator[](std::size_t i) {
        return x[i];
    }

    const U64& operator[](std::size_t i) const {
        return x[i];
    }
};


/*
 * ------------------------------------------------------------
 * Structure constants
 *
 * C[j,k,i]
 * ------------------------------------------------------------
 */
struct Algebra {
    std::size_t n;
    std::vector<U64> C;

    explicit Algebra(std::size_t dimension)
        : n(dimension),
          C(dimension * dimension * dimension, 0) {}

    std::size_t index(
        std::size_t j,
        std::size_t k,
        std::size_t i
    ) const noexcept {
        return (j * n + k) * n + i;
    }

    U64& coeff(
        std::size_t j,
        std::size_t k,
        std::size_t i
    ) {
        return C[index(j, k, i)];
    }

    const U64& coeff(
        std::size_t j,
        std::size_t k,
        std::size_t i
    ) const {
        return C[index(j, k, i)];
    }
};


/*
 * ------------------------------------------------------------
 * x + y
 * ------------------------------------------------------------
 */
inline State add(
    const State& x,
    const State& y
) {
    if (x.size() != y.size())
        throw std::invalid_argument("dimension mismatch");

    State out(x.size());

    for (std::size_t i = 0; i < x.size(); ++i)
        out[i] = x[i] + y[i];

    return out;
}


/*
 * ------------------------------------------------------------
 * x - y
 * ------------------------------------------------------------
 */
inline State sub(
    const State& x,
    const State& y
) {
    if (x.size() != y.size())
        throw std::invalid_argument("dimension mismatch");

    State out(x.size());

    for (std::size_t i = 0; i < x.size(); ++i)
        out[i] = x[i] - y[i];

    return out;
}


/*
 * ------------------------------------------------------------
 * a * x
 * ------------------------------------------------------------
 */
inline State smul(
    U64 a,
    const State& x
) {
    State out(x.size());

    for (std::size_t i = 0; i < x.size(); ++i)
        out[i] = a * x[i];

    return out;
}


/*
 * ------------------------------------------------------------
 * Bilinear multiplication
 *
 * (x * y)_i =
 *     sum_j sum_k x_j y_k C[j,k,i]
 * ------------------------------------------------------------
 */
inline State multiply(
    const Algebra& A,
    const State& x,
    const State& y
) {
    if (x.size() != A.n || y.size() != A.n)
        throw std::invalid_argument("dimension mismatch");

    State out(A.n);

    for (std::size_t j = 0; j < A.n; ++j) {
        for (std::size_t k = 0; k < A.n; ++k) {

            const U64 product = x[j] * y[k];

            for (std::size_t i = 0; i < A.n; ++i) {
                out[i] +=
                    product * A.coeff(j, k, i);
            }
        }
    }

    return out;
}


/*
 * ------------------------------------------------------------
 * Nonlinear UHA map
 *
 * F(x) = x * x
 * ------------------------------------------------------------
 */
inline State map(
    const Algebra& A,
    const State& x
) {
    return multiply(A, x, x);
}


/*
 * ------------------------------------------------------------
 * One UHA transition
 *
 * active = 0:
 *     x' = x
 *
 * active = 1:
 *     x' = x + (F(x) - x)
 *        = F(x)
 *
 * Since active is represented by U64,
 * this also supports the algebraic form:
 *
 *     x' = x + active * (F(x) - x)
 * ------------------------------------------------------------
 */
inline void step(
    const Algebra& A,
    State& x,
    U64 active
) {
    if (active == 0)
        return;

    State F = map(A, x);

    for (std::size_t i = 0; i < A.n; ++i)
        x[i] += active * (F[i] - x[i]);
}


/*
 * ------------------------------------------------------------
 * Halt mask
 *
 * halt = 0 -> active = 1
 * halt = 1 -> active = 0
 * ------------------------------------------------------------
 */
struct Machine {
    const Algebra& algebra;

    State state;

    U64 pc = 0;
    U64 halt = 0;

    Machine(const Algebra& A, State initial)
        : algebra(A),
          state(std::move(initial)) {

        if (state.size() != algebra.n)
            throw std::invalid_argument("dimension mismatch");
    }

    U64 active() const noexcept {
        return U64(1) - halt;
    }

    void tick() {
        const U64 a = active();

        step(
            algebra,
            state,
            a
        );

        pc += a;
    }

    void stop() noexcept {
        halt = 1;
    }

    bool halted() const noexcept {
        return halt != 0;
    }
};

} // namespace uha
