// License Apache 2.0  Takeo Yamamoto
#include <cstdint>
#include <vector>
#include <functional>
#include <numeric>
#include <stdexcept>

using U64 = uint64_t;

/**************************************
 * UHA n 次元キャリア
 **************************************/
struct UHA {
    std::vector<U64> coords;

    UHA(size_t n) : coords(n, 0) {}
    size_t size() const { return coords.size(); }
};

/**************************************
 * 基本演算
 **************************************/
UHA add(const UHA& x, const UHA& y) {
    size_t n = x.size();
    UHA out(n);
    for (size_t i = 0; i < n; ++i)
        out.coords[i] = x.coords[i] + y.coords[i];
    return out;
}

UHA smul(U64 a, const UHA& x) {
    size_t n = x.size();
    UHA out(n);
    for (size_t i = 0; i < n; ++i)
        out.coords[i] = a * x.coords[i];
    return out;
}

U64 inner(const UHA& x, const UHA& y) {
    U64 acc = 0;
    for (size_t i = 0; i < x.size(); ++i)
        acc += x.coords[i] * y.coords[i];
    return acc;
}

U64 norm(const UHA& x) {
    return inner(x, x);
}

bool orthogonal(const UHA& x, const UHA& y) {
    return inner(x, y) == 0;
}

/**************************************
 * 多元代数の乗法（構造定数 c[j][k]）
 **************************************/
UHA mulWith(const std::vector<std::vector<UHA>>& c,
            const UHA& x, const UHA& y) {

    size_t n = x.size();
    UHA out(n);

    for (size_t i = 0; i < n; ++i) {
        U64 acc = 0;
        for (size_t j = 0; j < n; ++j)
            for (size_t k = 0; k < n; ++k)
                acc += x.coords[j] * y.coords[k] * c[j][k].coords[i];
        out.coords[i] = acc;
    }
    return out;
}

/**************************************
 * 離散ユニタリ作用素 UOp
 **************************************/
struct UOp {
    std::function<UHA(const UHA&)> f;

    bool unitary_like(const UHA& v) const {
        return norm(f(v)) == norm(v);
    }
};

/**************************************
 * 標準量子ゲート（離散版）
 **************************************/
UOp XGate() {
    return UOp{
        .f = [](const UHA& v) {
            UHA out(2);
            out.coords[0] = v.coords[1];
            out.coords[1] = v.coords[0];
            return out;
        }
    };
}

UOp HGate() {
    return UOp{
        .f = [](const UHA& v) {
            UHA out(2);
            out.coords[0] = v.coords[0] + v.coords[1];
            out.coords[1] = v.coords[0] - v.coords[1];
            return out;
        }
    };
}

UOp CNOT() {
    return UOp{
        .f = [](const UHA& v) {
            UHA out(4);
            out.coords[0] = v.coords[0];
            out.coords[1] = v.coords[1];
            out.coords[2] = v.coords[3];
            out.coords[3] = v.coords[2];
            return out;
        }
    };
}

/**************************************
 * 離散量子回路 UCircuit
 **************************************/
struct UCircuit {
    std::vector<UOp> gates;

    UHA apply(const UHA& v) const {
        UHA cur = v;
        for (auto& g : gates)
            cur = g.f(cur);
        return cur;
    }
};

/**************************************
 * テンソル積
 **************************************/
UHA tensor(const UHA& x, const UHA& y) {
    size_t n = x.size();
    size_t m = y.size();
    UHA out(n * m);

    for (size_t i = 0; i < n; ++i)
        for (size_t j = 0; j < m; ++j)
            out.coords[i*m + j] = x.coords[i] * y.coords[j];

    return out;
}

/**************************************
 * エンタングルメント判定（簡易版）
 **************************************/
bool entangled(const UHA& psi, size_t n, size_t m) {
    return true; // 本格判定は rank 分解が必要
}

/**************************************
 * 離散 QFT（簡易版）
 **************************************/
UOp QFT(size_t n) {
    return UOp{
        .f = [n](const UHA& v) {
            UHA out(n);
            for (size_t k = 0; k < n; ++k) {
                U64 acc = 0;
                for (size_t j = 0; j < n; ++j)
                    acc += v.coords[j] * (U64)(j * k);
                out.coords[k] = acc;
            }
            return out;
        }
    };
}

/**************************************
 * Grover 演算子（離散版）
 **************************************/
UOp Grover(size_t n, const UOp& oracle) {
    return UOp{
        .f = [n, oracle](const UHA& v) {
            UHA w = oracle.f(v);

            U64 sum = 0;
            for (auto x : w.coords) sum += x;
            U64 avg = sum / n;

            UHA out(n);
            for (size_t i = 0; i < n; ++i)
                out.coords[i] = 2 * avg - w.coords[i];

            return out;
        }
    };
}
