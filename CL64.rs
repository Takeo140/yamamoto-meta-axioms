License Apache 2.0  Takeo Yamamoto

// complex_linalg64.rs
// -----------------------------------------------------------------------
// 64bit 離散型(固定小数点)複素数 線形代数ライブラリ — 量子計算タイプ
//
// 浮動小数点(f64)を一切使わず、i64 の Q32.32 固定小数点数のみで
// 複素数演算・行列演算・量子状態ベクトル演算を行う。
// 目的: 浮動小数点丸め誤差を排し、決定的(bit-exact)な複素線形代数を
//       64bit整数演算の範囲内で実現する。乗算は i128 中間精度を用いる。
// -----------------------------------------------------------------------

const FRAC_BITS: u32 = 32;
const SCALE: i64 = 1 << FRAC_BITS;

// ============================ Fx64: Q32.32 固定小数点 ============================

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fx64(pub i64);

impl Fx64 {
    pub fn from_f64(x: f64) -> Self {
        Fx64((x * SCALE as f64).round() as i64)
    }
    pub fn to_f64(self) -> f64 {
        self.0 as f64 / SCALE as f64
    }
    pub fn zero() -> Self { Fx64(0) }
    pub fn one() -> Self { Fx64(SCALE) }

    pub fn add(self, o: Fx64) -> Fx64 { Fx64(self.0.wrapping_add(o.0)) }
    pub fn sub(self, o: Fx64) -> Fx64 { Fx64(self.0.wrapping_sub(o.0)) }
    pub fn neg(self) -> Fx64 { Fx64(self.0.wrapping_neg()) }

    // 乗算: i128 中間精度で桁あふれを防ぎ、下位32bitを切り捨てて再スケール
    pub fn mul(self, o: Fx64) -> Fx64 {
        let prod: i128 = (self.0 as i128) * (o.0 as i128);
        Fx64((prod >> FRAC_BITS) as i64)
    }

    pub fn abs(self) -> Fx64 { Fx64(self.0.abs()) }

    // 整数ニュートン法による平方根 (固定小数点、決定的)
    pub fn sqrt(self) -> Fx64 {
        if self.0 <= 0 { return Fx64::zero(); }
        // x を SCALE^2 スケールの整数とみなして sqrt を取り、SCALE で正規化
        let target: i128 = (self.0 as i128) << FRAC_BITS;
        let mut lo: i128 = 0;
        let mut hi: i128 = 1i128 << 40; // 十分大きい上限
        while lo < hi {
            let mid = lo + (hi - lo + 1) / 2;
            if mid.checked_mul(mid).map_or(false, |v| v <= target) {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        Fx64(lo as i64)
    }
}

// ============================ Cx64: 離散複素数 ============================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cx64 {
    pub re: Fx64,
    pub im: Fx64,
}

impl Cx64 {
    pub fn new(re: f64, im: f64) -> Self {
        Cx64 { re: Fx64::from_f64(re), im: Fx64::from_f64(im) }
    }
    pub fn zero() -> Self { Cx64 { re: Fx64::zero(), im: Fx64::zero() } }
    pub fn one() -> Self { Cx64 { re: Fx64::one(), im: Fx64::zero() } }
    pub fn i() -> Self { Cx64 { re: Fx64::zero(), im: Fx64::one() } }

    pub fn add(self, o: Cx64) -> Cx64 {
        Cx64 { re: self.re.add(o.re), im: self.im.add(o.im) }
    }
    pub fn sub(self, o: Cx64) -> Cx64 {
        Cx64 { re: self.re.sub(o.re), im: self.im.sub(o.im) }
    }
    pub fn mul(self, o: Cx64) -> Cx64 {
        // (a+bi)(c+di) = (ac-bd) + (ad+bc)i
        let re = self.re.mul(o.re).sub(self.im.mul(o.im));
        let im = self.re.mul(o.im).add(self.im.mul(o.re));
        Cx64 { re, im }
    }
    pub fn conj(self) -> Cx64 {
        Cx64 { re: self.re, im: self.im.neg() }
    }
    pub fn norm_sqr(self) -> Fx64 {
        self.re.mul(self.re).add(self.im.mul(self.im))
    }
    pub fn norm(self) -> Fx64 {
        self.norm_sqr().sqrt()
    }
    pub fn scale(self, s: Fx64) -> Cx64 {
        Cx64 { re: self.re.mul(s), im: self.im.mul(s) }
    }
    pub fn to_f64_pair(self) -> (f64, f64) {
        (self.re.to_f64(), self.im.to_f64())
    }
}

// ============================ CMatrix: 複素行列 ============================

#[derive(Clone, Debug)]
pub struct CMatrix {
    pub rows: usize,
    pub cols: usize,
    pub data: Vec<Cx64>, // row-major
}

impl CMatrix {
    pub fn zeros(rows: usize, cols: usize) -> Self {
        CMatrix { rows, cols, data: vec![Cx64::zero(); rows * cols] }
    }

    pub fn from_rows(rows_data: Vec<Vec<Cx64>>) -> Self {
        let rows = rows_data.len();
        let cols = if rows > 0 { rows_data[0].len() } else { 0 };
        let mut data = Vec::with_capacity(rows * cols);
        for r in rows_data {
            assert_eq!(r.len(), cols, "行の長さが揃っていません");
            data.extend(r);
        }
        CMatrix { rows, cols, data }
    }

    pub fn identity(n: usize) -> Self {
        let mut m = CMatrix::zeros(n, n);
        for i in 0..n { m.set(i, i, Cx64::one()); }
        m
    }

    #[inline]
    pub fn get(&self, r: usize, c: usize) -> Cx64 { self.data[r * self.cols + c] }
    #[inline]
    pub fn set(&mut self, r: usize, c: usize, v: Cx64) { self.data[r * self.cols + c] = v; }

    // 行列積
    pub fn matmul(&self, o: &CMatrix) -> CMatrix {
        assert_eq!(self.cols, o.rows, "次元不一致: matmul");
        let mut out = CMatrix::zeros(self.rows, o.cols);
        for i in 0..self.rows {
            for k in 0..self.cols {
                let a = self.get(i, k);
                if a == Cx64::zero() { continue; }
                for j in 0..o.cols {
                    let v = out.get(i, j).add(a.mul(o.get(k, j)));
                    out.set(i, j, v);
                }
            }
        }
        out
    }

    // エルミート共役 (共役転置) — ユニタリ行列の逆行列として使う
    pub fn dagger(&self) -> CMatrix {
        let mut out = CMatrix::zeros(self.cols, self.rows);
        for i in 0..self.rows {
            for j in 0..self.cols {
                out.set(j, i, self.get(i, j).conj());
            }
        }
        out
    }

    // テンソル積 (クロネッカー積) — 複数量子ビットのゲート合成に使用
    pub fn kron(&self, o: &CMatrix) -> CMatrix {
        let rows = self.rows * o.rows;
        let cols = self.cols * o.cols;
        let mut out = CMatrix::zeros(rows, cols);
        for i1 in 0..self.rows {
            for j1 in 0..self.cols {
                let a = self.get(i1, j1);
                if a == Cx64::zero() { continue; }
                for i2 in 0..o.rows {
                    for j2 in 0..o.cols {
                        let v = a.mul(o.get(i2, j2));
                        out.set(i1 * o.rows + i2, j1 * o.cols + j2, v);
                    }
                }
            }
        }
        out
    }

    // 状態ベクトルへの作用 (行列 × 列ベクトル)
    pub fn apply(&self, v: &CVector) -> CVector {
        assert_eq!(self.cols, v.dim(), "次元不一致: apply");
        let mut out = vec![Cx64::zero(); self.rows];
        for i in 0..self.rows {
            let mut acc = Cx64::zero();
            for j in 0..self.cols {
                acc = acc.add(self.get(i, j).mul(v.get(j)));
            }
            out[i] = acc;
        }
        CVector { data: out }
    }

    // ユニタリ性の近似検証: U† U ≈ I を許容誤差 eps (Fx64) 以内で確認
    pub fn is_approx_unitary(&self, eps: Fx64) -> bool {
        if self.rows != self.cols { return false; }
        let n = self.rows;
        let prod = self.dagger().matmul(self);
        for i in 0..n {
            for j in 0..n {
                let expect = if i == j { Cx64::one() } else { Cx64::zero() };
                let diff = prod.get(i, j).sub(expect);
                if diff.norm().0 > eps.0 { return false; }
            }
        }
        true
    }
}

// ============================ CVector: 量子状態ベクトル ============================

#[derive(Clone, Debug)]
pub struct CVector {
    pub data: Vec<Cx64>,
}

impl CVector {
    pub fn dim(&self) -> usize { self.data.len() }
    pub fn get(&self, i: usize) -> Cx64 { self.data[i] }

    pub fn basis(dim: usize, idx: usize) -> Self {
        let mut d = vec![Cx64::zero(); dim];
        d[idx] = Cx64::one();
        CVector { data: d }
    }

    // 内積 <self|other> = Σ conj(self_i) * other_i
    pub fn inner(&self, o: &CVector) -> Cx64 {
        assert_eq!(self.dim(), o.dim());
        let mut acc = Cx64::zero();
        for i in 0..self.dim() {
            acc = acc.add(self.data[i].conj().mul(o.data[i]));
        }
        acc
    }

    pub fn norm(&self) -> Fx64 {
        self.inner(self).re.sqrt()
    }

    // 測定確率分布 |amp|^2 (f64 で出力。内部計算は固定小数点で厳密)
    pub fn probabilities(&self) -> Vec<f64> {
        self.data.iter().map(|c| c.norm_sqr().to_f64()).collect()
    }

    pub fn tensor(&self, o: &CVector) -> CVector {
        let mut out = Vec::with_capacity(self.dim() * o.dim());
        for a in &self.data {
            for b in &o.data {
                out.push(a.mul(*b));
            }
        }
        CVector { data: out }
    }
}

// ============================ 標準量子ゲート (離散/固定小数点) ============================

pub mod gates {
    use super::*;

    pub fn i_gate() -> CMatrix { CMatrix::identity(2) }

    pub fn x() -> CMatrix {
        CMatrix::from_rows(vec![
            vec![Cx64::zero(), Cx64::one()],
            vec![Cx64::one(), Cx64::zero()],
        ])
    }

    pub fn y() -> CMatrix {
        let mi = Cx64::i().scale(Fx64::from_f64(-1.0));
        CMatrix::from_rows(vec![
            vec![Cx64::zero(), mi],
            vec![Cx64::i(), Cx64::zero()],
        ])
    }

    pub fn z() -> CMatrix {
        CMatrix::from_rows(vec![
            vec![Cx64::one(), Cx64::zero()],
            vec![Cx64::zero(), Cx64::one().scale(Fx64::from_f64(-1.0))],
        ])
    }

    // アダマールゲート: 1/sqrt(2) を固定小数点定数として埋め込み
    pub fn h() -> CMatrix {
        let s = Fx64::from_f64(std::f64::consts::FRAC_1_SQRT_2);
        let p = Cx64 { re: s, im: Fx64::zero() };
        let m = Cx64 { re: s.neg(), im: Fx64::zero() };
        CMatrix::from_rows(vec![
            vec![p, p],
            vec![p, m],
        ])
    }

    pub fn s_gate() -> CMatrix {
        CMatrix::from_rows(vec![
            vec![Cx64::one(), Cx64::zero()],
            vec![Cx64::zero(), Cx64::i()],
        ])
    }

    pub fn t_gate() -> CMatrix {
        let s = Fx64::from_f64(std::f64::consts::FRAC_1_SQRT_2);
        let e = Cx64 { re: s, im: s }; // e^{i*pi/4}
        CMatrix::from_rows(vec![
            vec![Cx64::one(), Cx64::zero()],
            vec![Cx64::zero(), e],
        ])
    }

    // 2量子ビットCNOT (制御=先頭, 標的=後方)
    pub fn cnot() -> CMatrix {
        let mut m = CMatrix::identity(4);
        // |10> <-> |11> の入れ替え (行 2,3)
        for c in 0..4 {
            let a = m.get(2, c);
            let b = m.get(3, c);
            m.set(2, c, b);
            m.set(3, c, a);
        }
        m
    }
}

// ============================ デモ: Bell状態生成 ============================

fn main() {
    use gates::*;

    println!("=== 64bit 離散型複素数 線形代数 (量子計算タイプ) デモ ===\n");

    // |00> 初期状態 (2量子ビット, dim=4)
    let psi0 = CVector::basis(2, 0).tensor(&CVector::basis(2, 0));

    // H ⊗ I を適用
    let h_i = h().kron(&i_gate());
    let psi1 = h_i.apply(&psi0);

    // CNOT を適用 → Bell状態 (|00> + |11>)/sqrt(2)
    let psi2 = cnot().apply(&psi1);

    println!("Bell状態の振幅 (Fx64固定小数点 -> f64表示):");
    for (idx, amp) in psi2.data.iter().enumerate() {
        let (re, im) = amp.to_f64_pair();
        println!("  |{:02b}>: {:+.6} {:+.6}i", idx, re, im);
    }

    println!("\n測定確率:");
    for (idx, p) in psi2.probabilities().iter().enumerate() {
        println!("  |{:02b}>: {:.6}", idx, p);
    }

    println!("\n状態ベクトルのノルム: {:.9}", psi2.norm().to_f64());

    // ゲートのユニタリ性を検証 (許容誤差 1e-6 相当)
    let eps = Fx64::from_f64(1e-6);
    println!("\nユニタリ性検証 (許容誤差 1e-6):");
    println!("  H     : {}", h().is_approx_unitary(eps));
    println!("  X     : {}", x().is_approx_unitary(eps));
    println!("  Y     : {}", y().is_approx_unitary(eps));
    println!("  Z     : {}", z().is_approx_unitary(eps));
    println!("  S     : {}", s_gate().is_approx_unitary(eps));
    println!("  T     : {}", t_gate().is_approx_unitary(eps));
    println!("  CNOT  : {}", cnot().is_approx_unitary(eps));
    println!("  H⊗I   : {}", h_i.is_approx_unitary(eps));
}
