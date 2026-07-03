// License: Apache 2.0
// Author: Takeo Yamamoto

#include <cstdint>
#include <array>

using U64  = std::uint64_t;
using Size = std::size_t;

// ===============================
// UHA n : Fin n → U64
// ===============================
template<Size N>
struct UHA {
    std::array<U64, N> coords;

    UHA() { coords.fill(0); }
    explicit UHA(const std::array<U64, N>& a) : coords(a) {}
};

// ===============================
// UOp n : Fin n → U64  (XOR マスク)
// ===============================
template<Size N>
struct UOp {
    std::array<U64, N> mask;

    UOp() { mask.fill(0); }
    explicit UOp(const std::array<U64, N>& m) : mask(m) {}
};

// ===============================
// norm : Σ popcount(x[i])
// ===============================
inline std::uint32_t popcount64(U64 x) {
    return static_cast<std::uint32_t>(__builtin_popcountll(x));
}

template<Size N>
std::uint32_t norm(const UHA<N>& x) {
    std::uint32_t s = 0;
    for (Size i = 0; i < N; ++i)
        s += popcount64(x.coords[i]);
    return s;
}

// ===============================
// UOp.apply : x[i] XOR mask[i]
// ===============================
template<Size N>
UHA<N> apply(const UOp<N>& op, const UHA<N>& x) {
    UHA<N> y;
    for (Size i = 0; i < N; ++i)
        y.coords[i] = x.coords[i] ^ op.mask[i];
    return y;
}

// ===============================
// mulWith : Σ_{j,k} x[j] * y[k] * c[j][k][i]
// c : 構造定数テンソル c[j][k][i]
// ===============================
template<Size N>
UHA<N> mulWith(const UHA<N>& x,
               const UHA<N>& y,
               const std::array<std::array<std::array<U64, N>, N>, N>& c)
{
    UHA<N> r;
    for (Size i = 0; i < N; ++i) {
        U64 acc = 0;
        for (Size j = 0; j < N; ++j)
            for (Size k = 0; k < N; ++k)
                acc += x.coords[j] * y.coords[k] * c[j][k][i];
        r.coords[i] = acc;
    }
    return r;
}

// ===============================
// step : x → UOp → mulWith → norm
// ===============================
template<Size N>
std::uint64_t step(const UHA<N>& x,
                   const UOp<N>& op,
                   const std::array<std::array<std::array<U64, N>, N>, N>& c)
{
    UHA<N> y = apply<N>(op, x);
    UHA<N> z = mulWith<N>(x, y, c);
    return static_cast<std::uint64_t>(norm<N>(z));
}
