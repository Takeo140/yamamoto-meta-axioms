License Apache 2.0 Takeo Yamamoto

/*!
# ComplexQuantum Phase Space Simulator
# 連続位相空間における量子ビット演算ライブラリ
# Rust 実装

## 理論的位置づけ
本モジュールは、情報（Real）と価値（Imag）を連続的な複素確率振幅として捉え、
ブロッホ球（位相空間）上の回転運動として量子ゲートを再定義する。
測定は、ボルン則（|振幅|² = 確率）に基づき、確率的に状態を崩壊させる。
*/

use std::fmt;

// ============================================================
// §0. 簡易擬似乱数生成器（標準ライブラリのみで動作）
// ============================================================
struct SimpleRng {
    state: u64,
}

impl SimpleRng {
    fn new(seed: u64) -> Self {
        SimpleRng { state: seed }
    }

    fn next(&mut self) -> u64 {
        // xorshift-based LCG
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }

    fn next_f64(&mut self) -> f64 {
        self.next() as f64 / u64::MAX as f64
    }
}

// ============================================================
// §1. 連続複素数と量子状態の定義
// ============================================================

/// 複素数振幅
#[derive(Clone, Copy, Debug)]
struct ComplexAmp {
    re: f64,
    im: f64,
}

impl ComplexAmp {
    fn new(re: f64, im: f64) -> Self {
        ComplexAmp { re, im }
    }

    /// ノルムの二乗 |c|² = re² + im²
    fn norm_sq(&self) -> f64 {
        self.re * self.re + self.im * self.im
    }

    /// 複素共役
    fn conj(&self) -> Self {
        ComplexAmp::new(self.re, -self.im)
    }

    /// e^{iθ} = cos(θ) + i sin(θ)
    fn exp_i(theta: f64) -> Self {
        ComplexAmp::new(theta.cos(), theta.sin())
    }
}

impl fmt::Display for ComplexAmp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sign = if self.im >= 0.0 { "+" } else { "" };
        write!(f, "({:.6}{}{:.6}i)", self.re, sign, self.im)
    }
}

impl std::ops::Add for ComplexAmp {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        ComplexAmp::new(self.re + rhs.re, self.im + rhs.im)
    }
}

impl std::ops::Mul for ComplexAmp {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        ComplexAmp::new(
            self.re * rhs.re - self.im * rhs.im,
            self.re * rhs.im + self.im * rhs.re,
        )
    }
}

impl std::ops::Mul<f64> for ComplexAmp {
    type Output = Self;
    fn mul(self, rhs: f64) -> Self::Output {
        ComplexAmp::new(self.re * rhs, self.im * rhs)
    }
}

// ============================================================
// §1. 量子ビット
// ============================================================

/// 連続位相空間上の1量子ビット状態
/// |ψ⟩ = α|0⟩ + β|1⟩
#[derive(Clone, Copy, Debug)]
struct QuantumBit {
    alpha: ComplexAmp, // |0⟩ (情報基底) の確率振幅
    beta: ComplexAmp,  // |1⟩ (価値基底) の確率振幅
}

impl QuantumBit {
    fn new(alpha: ComplexAmp, beta: ComplexAmp) -> Self {
        let mut q = QuantumBit { alpha, beta };
        q.normalize();
        q
    }

    /// 正規化: |α|² + |β|² = 1
    fn normalize(&mut self) {
        let total = self.alpha.norm_sq() + self.beta.norm_sq();
        if total > 1e-15 {
            let norm = total.sqrt();
            self.alpha = self.alpha * (1.0 / norm);
            self.beta = self.beta * (1.0 / norm);
        }
    }

    fn is_normalized(&self, epsilon: f64) -> bool {
        let total = self.alpha.norm_sq() + self.beta.norm_sq();
        (total - 1.0).abs < epsilon
    }

    fn prob_0(&self) -> f64 {
        self.alpha.norm_sq()
    }

    fn prob_1(&self) -> f64 {
        self.beta.norm_sq()
    }

    /// ブロッホ球座標 (x, y, z)
    fn bloch_coordinates(&self) -> (f64, f64, f64) {
        let ab_conj = self.alpha * self.beta.conj();
        let x = 2.0 * ab_conj.re;
        let y = 2.0 * ab_conj.im;
        let z = self.alpha.norm_sq() - self.beta.norm_sq();
        (x, y, z)
    }
}

impl fmt::Display for QuantumBit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "|0⟩: {}, |1⟩: {}", self.alpha, self.beta)
    }
}

// ============================================================
// §2. 連続位相幾何ゲート群
// ============================================================

struct QuantumGates;

impl QuantumGates {
    /// 位相シフトゲート R_z(θ)
    /// |0⟩ → e^{-iθ/2}|0⟩
    /// |1⟩ → e^{iθ/2}|1⟩
    fn phase_shift(theta: f64, q: QuantumBit) -> QuantumBit {
        let half = theta / 2.0;
        let e_minus = ComplexAmp::exp_i(-half);
        let e_plus = ComplexAmp::exp_i(half);
        QuantumBit::new(q.alpha * e_minus, q.beta * e_plus)
    }

    /// アダマールゲート H = (1/√2) [[1, 1], [1, -1]]
    fn gate_h(q: QuantumBit) -> QuantumBit {
        let inv_sqrt2 = 1.0 / 2.0_f64.sqrt();
        let a_re = (q.alpha.re + q.beta.re) * inv_sqrt2;
        let a_im = (q.alpha.im + q.beta.im) * inv_sqrt2;
        let b_re = (q.alpha.re - q.beta.re) * inv_sqrt2;
        let b_im = (q.alpha.im - q.beta.im) * inv_sqrt2;
        QuantumBit::new(ComplexAmp::new(a_re, a_im), ComplexAmp::new(b_re, b_im))
    }

    /// パウリ X ゲート（ビット反転）
    fn gate_x(q: QuantumBit) -> QuantumBit {
        QuantumBit::new(q.beta, q.alpha)
    }

    /// パウリ Y ゲート
    fn gate_y(q: QuantumBit) -> QuantumBit {
        let i = ComplexAmp::new(0.0, 1.0);
        let minus_i = ComplexAmp::new(0.0, -1.0);
        QuantumBit::new(q.beta * minus_i, q.alpha * i)
    }

    /// パウリ Z ゲート（位相反転）
    fn gate_z(q: QuantumBit) -> QuantumBit {
        QuantumBit::new(q.alpha, q.beta * -1.0)
    }

    /// X軸回転 Rx(θ)
    fn rotation_x(theta: f64, q: QuantumBit) -> QuantumBit {
        let c = (theta / 2.0).cos();
        let s = (theta / 2.0).sin();
        let a_re = c * q.alpha.re - s * q.beta.im;
        let a_im = c * q.alpha.im + s * q.beta.re;
        let b_re = -s * q.alpha.im + c * q.beta.re;
        let b_im = s * q.alpha.re + c * q.beta.im;
        QuantumBit::new(ComplexAmp::new(a_re, a_im), ComplexAmp::new(b_re, b_im))
    }

    /// Y軸回転 Ry(θ)
    fn rotation_y(theta: f64, q: QuantumBit) -> QuantumBit {
        let c = (theta / 2.0).cos();
        let s = (theta / 2.0).sin();
        let a_re = c * q.alpha.re - s * q.beta.re;
        let a_im = c * q.alpha.im - s * q.beta.im;
        let b_re = s * q.alpha.re + c * q.beta.re;
        let b_im = s * q.alpha.im + c * q.beta.im;
        QuantumBit::new(ComplexAmp::new(a_re, a_im), ComplexAmp::new(b_re, b_im))
    }

    /// Z軸回転 Rz(θ)
    fn rotation_z(theta: f64, q: QuantumBit) -> QuantumBit {
        Self::phase_shift(theta, q)
    }
}

// ============================================================
// §3. ボルン則に基づく量子測定
// ============================================================

#[derive(Debug)]
struct MeasurementResult {
    collapsed_state: QuantumBit,
    observed_bit: u8,
    probability: f64,
}

struct QuantumMeasurement;

impl QuantumMeasurement {
    /// ボルン則に基づく確率的測定
    fn measure(q: &QuantumBit, rng: &mut SimpleRng) -> MeasurementResult {
        let p0 = q.prob_0();
        let p1 = q.prob_1();
        if rng.next_f64() < p0 {
            MeasurementResult {
                collapsed_state: QuantumBit::new(ComplexAmp::new(1.0, 0.0), ComplexAmp::new(0.0, 0.0)),
                observed_bit: 0,
                probability: p0,
            }
        } else {
            MeasurementResult {
                collapsed_state: QuantumBit::new(ComplexAmp::new(0.0, 0.0), ComplexAmp::new(1.0, 0.0)),
                observed_bit: 1,
                probability: p1,
            }
        }
    }

    /// 多数回測定統計
    fn measure_many(q: &QuantumBit, shots: usize, rng: &mut SimpleRng) -> (f64, f64) {
        let mut count0 = 0usize;
        for _ in 0..shots {
            let r = Self::measure(q, rng);
            if r.observed_bit == 0 {
                count0 += 1;
            }
        }
        (count0 as f64 / shots as f64, (shots - count0) as f64 / shots as f64)
    }
}

// ============================================================
// §4. 多量子ビットレジスタ（エンタングルメント対応）
// ============================================================

#[derive(Clone, Copy, Debug)]
struct QuantumRegister2 {
    amp00: ComplexAmp,
    amp01: ComplexAmp,
    amp10: ComplexAmp,
    amp11: ComplexAmp,
}

impl QuantumRegister2 {
    fn new(amp00: ComplexAmp, amp01: ComplexAmp, amp10: ComplexAmp, amp11: ComplexAmp) -> Self {
        let mut reg = QuantumRegister2 { amp00, amp01, amp10, amp11 };
        reg.normalize();
        reg
    }

    fn normalize(&mut self) {
        let total = self.amp00.norm_sq() + self.amp01.norm_sq() + self.amp10.norm_sq() + self.amp11.norm_sq();
        if total > 1e-15 {
            let n = 1.0 / total.sqrt();
            self.amp00 = self.amp00 * n;
            self.amp01 = self.amp01 * n;
            self.amp10 = self.amp10 * n;
            self.amp11 = self.amp11 * n;
        }
    }

    /// 初期状態 |00⟩
    fn init() -> Self {
        QuantumRegister2::new(
            ComplexAmp::new(1.0, 0.0),
            ComplexAmp::new(0.0, 0.0),
            ComplexAmp::new(0.0, 0.0),
            ComplexAmp::new(0.0, 0.0),
        )
    }

    /// 最初の量子ビットにHゲートを適用
    fn apply_h0(&self) -> Self {
        let inv_sqrt2 = 1.0 / 2.0_f64.sqrt();
        QuantumRegister2::new(
            ComplexAmp::new((self.amp00.re + self.amp10.re) * inv_sqrt2, (self.amp00.im + self.amp10.im) * inv_sqrt2),
            ComplexAmp::new((self.amp01.re + self.amp11.re) * inv_sqrt2, (self.amp01.im + self.amp11.im) * inv_sqrt2),
            ComplexAmp::new((self.amp00.re - self.amp10.re) * inv_sqrt2, (self.amp00.im - self.amp10.im) * inv_sqrt2),
            ComplexAmp::new((self.amp01.re - self.amp11.re) * inv_sqrt2, (self.amp01.im - self.amp11.im) * inv_sqrt2),
        )
    }

    /// CNOTゲート（制御=ビット0, ターゲット=ビット1）
    fn apply_cnot(&self) -> Self {
        // |10⟩ ↔ |11⟩
        QuantumRegister2::new(self.amp00, self.amp01, self.amp11, self.amp10)
    }

    /// ベル状態 |Φ⁺⟩ = (|00⟩ + |11⟩)/√2 を生成
    fn bell_state() -> Self {
        Self::init().apply_h0().apply_cnot()
    }
}

impl fmt::Display for QuantumRegister2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "|00⟩: {}", self.amp00)?;
        writeln!(f, "|01⟩: {}", self.amp01)?;
        writeln!(f, "|10⟩: {}", self.amp10)?;
        write!(f, "|11⟩: {}", self.amp11)
    }
}

// ============================================================
// §5. 連続演算のシミュレーション評価
// ============================================================

fn main() {
    let mut rng = SimpleRng::new(42);

    println!("{}", "=".repeat(70));
    println!("  量子コンピュータ的な複素数ビット計算理論");
    println!("  ComplexQuantum Phase Space Simulator (Rust)");
    println!("{}", "=".repeat(70));

    // 1. 初期状態 |0⟩
    println!("\n【1. 初期状態 |0⟩】");
    let psi0 = QuantumBit::new(ComplexAmp::new(1.0, 0.0), ComplexAmp::new(0.0, 0.0));
    println!("  {}", psi0);
    println!("  正規化: {}", psi0.is_normalized(1e-5));
    let (x, y, z) = psi0.bloch_coordinates();
    println!("  ブロッホ球: (x={:.4}, y={:.4}, z={:.4})", x, y, z);

    // 2. アダマールゲート
    println!("\n【2. アダマールゲート後】");
    let psi1 = QuantumGates::gate_h(psi0);
    println!("  {}", psi1);
    println!("  P(|0⟩) = {:.6}, P(|1⟩) = {:.6}", psi1.prob_0(), psi1.prob_1());
    let (x, y, z) = psi1.bloch_coordinates();
    println!("  ブロッホ球: (x={:.4}, y={:.4}, z={:.4})", x, y, z);

    // 3. 位相シフト R_z(π/4)
    println!("\n【3. 位相シフト R_z(π/4)】");
    let psi2 = QuantumGates::phase_shift(std::f64::consts::PI / 4.0, psi1);
    println!("  {}", psi2);
    println!("  P(|0⟩) = {:.6}, P(|1⟩) = {:.6}", psi2.prob_0(), psi2.prob_1());
    let (x, y, z) = psi2.bloch_coordinates();
    println!("  ブロッホ球: (x={:.4}, y={:.4}, z={:.4})", x, y, z);

    // 4. Xゲート
    println!("\n【4. Xゲート後】");
    let psi3 = QuantumGates::gate_x(psi2);
    println!("  {}", psi3);
    println!("  P(|0⟩) = {:.6}, P(|1⟩) = {:.6}", psi3.prob_0(), psi3.prob_1());
    let (x, y, z) = psi3.bloch_coordinates();
    println!("  ブロッホ球: (x={:.4}, y={:.4}, z={:.4})", x, y, z);

    // 5. 量子測定
    println!("\n【5. 量子測定（ボルン則）】");
    let result = QuantumMeasurement::measure(&psi3, &mut rng);
    println!("  観測ビット: {}, 確率: {:.6}", result.observed_bit, result.probability);
    println!("  崩壊後状態: {}", result.collapsed_state);

    // 6. 多数回測定統計
    println!("\n【6. 多数回測定統計 (1000 shots)】");
    let (p0_obs, p1_obs) = QuantumMeasurement::measure_many(&psi3, 1000, &mut rng);
    println!("  観測値 |0⟩: {:.4} (理論値: {:.4})", p0_obs, psi3.prob_0());
    println!("  観測値 |1⟩: {:.4} (理論値: {:.4})", p1_obs, psi3.prob_1());

    // 7. ベル状態
    println!("\n【7. ベル状態 |Φ⁺⟩ = (|00⟩ + |11⟩)/√2】");
    let bell = QuantumRegister2::bell_state();
    println!("{}", bell);

    // 8. ブロッホ球上の連続回転
    println!("\n【8. ブロッホ球上の連続回転 Ry】");
    let angles = [0.0, std::f64::consts::PI / 4.0, std::f64::consts::PI / 2.0, std::f64::consts::PI];
    for theta in angles {
        let q = QuantumGates::rotation_y(theta, psi0);
        let (x, y, z) = q.bloch_coordinates();
        println!("  Ry({:.4}): (x={:.4}, y={:.4}, z={:.4})", theta, x, y, z);
    }

    // 9. 位相干渉効果
    println!("\n【9. 位相干渉効果】");
    let inv_sqrt2 = 1.0 / 2.0_f64.sqrt();
    let q_plus = QuantumBit::new(ComplexAmp::new(inv_sqrt2, 0.0), ComplexAmp::new(inv_sqrt2, 0.0));
    let q_minus = QuantumBit::new(ComplexAmp::new(inv_sqrt2, 0.0), ComplexAmp::new(-inv_sqrt2, 0.0));
    println!("  |+⟩: {}", q_plus);
    println!("  |-⟩: {}", q_minus);
    println!("  H|+⟩ = {}", QuantumGates::gate_h(q_plus));
    println!("  H|-⟩ = {}", QuantumGates::gate_h(q_minus));
    println!("  (|+⟩ → |0⟩, |-⟩ → |1⟩ : 位相の違いが干渉で結果を変える)");

    println!("\n{}", "=".repeat(70));
    println!("  量子計算の核心: 複素数振幅の重ね合わせ・干渉・エンタングルメント");
    println!("{}", "=".repeat(70));
        }
