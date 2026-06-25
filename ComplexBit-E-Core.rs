// ComplexBit Quantum Gate Engine
// Copyright (c) 2026 Yamamoto Takeo
// License: Apache 2.0 / CC BY 4.0

use std::ops::{Add, Mul, Neg};

// ============================================================
// §1. ComplexBit 基本代数
// ============================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[repr(C, align(16))]
pub struct ComplexBit {
    pub real: u64,  // 情報の担体 / Gaussian 整数実部
    pub imag: u64,  // 情報価値 / 位相累積 / Gaussian 整数虚部
}

impl ComplexBit {
    #[inline(always)]
    pub const fn new(real: u64, imag: u64) -> Self { Self { real, imag } }

    pub const ZERO:   Self = Self::new(0, 0);
    pub const ONE:    Self = Self::new(1, 0);
    pub const I_UNIT: Self = Self::new(0, 1);

    #[inline(always)]
    pub fn norm_sq(self) -> u64 {
        self.real.wrapping_mul(self.real)
            .wrapping_add(self.imag.wrapping_mul(self.imag))
    }

    #[inline(always)]
    pub fn nonzero_mask(x: u64) -> u64 { (x.wrapping_neg() | x) >> 63 }

    #[inline(always)]
    pub fn branchless_select(ctrl: u64, a: u64, b: u64) -> u64 {
        let m = Self::nonzero_mask(ctrl);
        a.wrapping_mul(m).wrapping_add(b.wrapping_mul(1u64.wrapping_sub(m)))
    }

    #[inline(always)]
    pub fn select(ctrl: u64, a: Self, b: Self) -> Self {
        Self {
            real: Self::branchless_select(ctrl, a.real, b.real),
            imag: Self::branchless_select(ctrl, a.imag, b.imag),
        }
    }
}

impl Add for ComplexBit {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self {
            real: self.real.wrapping_add(rhs.real),
            imag: self.imag.wrapping_add(rhs.imag),
        }
    }
}

impl Mul for ComplexBit {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        Self {
            real: self.real.wrapping_mul(rhs.real)
                      .wrapping_sub(self.imag.wrapping_mul(rhs.imag)),
            imag: self.real.wrapping_mul(rhs.imag)
                      .wrapping_add(self.imag.wrapping_mul(rhs.real)),
        }
    }
}

impl Neg for ComplexBit {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        Self { real: self.real.wrapping_neg(), imag: self.imag.wrapping_neg() }
    }
}

// ============================================================
// §2. 量子ゲートトレイト + 実装
// ============================================================

pub trait QuantumGate: Send + Sync {
    fn apply(&self, c: ComplexBit) -> ComplexBit;

    fn then<G: QuantumGate>(self, next: G) -> Composed<Self, G>
    where Self: Sized,
    { Composed { first: self, second: next } }
}

pub struct Composed<A, B> { first: A, second: B }
impl<A: QuantumGate, B: QuantumGate> QuantumGate for Composed<A, B> {
    #[inline(always)]
    fn apply(&self, c: ComplexBit) -> ComplexBit {
        self.second.apply(self.first.apply(c))
    }
}

// Z gate: 虚部（情報価値）の極性反転  Z²=I, normSq 保存
pub struct GateZ;
impl QuantumGate for GateZ {
    #[inline(always)]
    fn apply(&self, c: ComplexBit) -> ComplexBit {
        ComplexBit { real: c.real, imag: c.imag.wrapping_neg() }
    }
}

// X gate: 情報↔価値の双対交換  X²=I, normSq 保存
pub struct GateX;
impl QuantumGate for GateX {
    #[inline(always)]
    fn apply(&self, c: ComplexBit) -> ComplexBit {
        ComplexBit { real: c.imag, imag: c.real }
    }
}

// S gate (rotI): ×i 回転  S²=Z, S⁴=I
pub struct GateS;
impl QuantumGate for GateS {
    #[inline(always)]
    fn apply(&self, c: ComplexBit) -> ComplexBit {
        ComplexBit { real: c.imag.wrapping_neg(), imag: c.real }
    }
}

// S† gate (rotNegI): ×(-i) 回転  S†S=I
pub struct GateSdag;
impl QuantumGate for GateSdag {
    #[inline(always)]
    fn apply(&self, c: ComplexBit) -> ComplexBit {
        ComplexBit { real: c.imag, imag: c.real.wrapping_neg() }
    }
}

// H gate: √2≈181/128 整数近似
pub struct GateH;
const H_SCALE: u64 = 181;
const H_SHIFT: u32 = 7;
impl QuantumGate for GateH {
    #[inline(always)]
    fn apply(&self, c: ComplexBit) -> ComplexBit {
        ComplexBit {
            real: c.real.wrapping_add(c.imag).wrapping_mul(H_SCALE) >> H_SHIFT,
            imag: c.real.wrapping_sub(c.imag).wrapping_mul(H_SCALE) >> H_SHIFT,
        }
    }
}

// ── CNOT gate ────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CNOTState { pub control: ComplexBit, pub target: ComplexBit }

pub struct GateCNOT;
impl GateCNOT {
    #[inline(always)]
    pub fn apply(&self, s: CNOTState) -> CNOTState {
        let ctrl_active = ComplexBit::nonzero_mask(s.control.norm_sq());
        let no_active   = 1u64.wrapping_sub(ctrl_active);
        CNOTState {
            control: s.control,
            target: ComplexBit {
                real: s.target.imag.wrapping_mul(ctrl_active)
                          .wrapping_add(s.target.real.wrapping_mul(no_active)),
                imag: s.target.real.wrapping_mul(ctrl_active)
                          .wrapping_add(s.target.imag.wrapping_mul(no_active)),
            },
        }
    }
}

// ============================================================
// §3. 情報価値演算（BitEconomics 統合）
// ============================================================

#[inline(always)]
pub fn value_transfer(src: ComplexBit, dst: ComplexBit) -> ComplexBit {
    ComplexBit { real: dst.real, imag: dst.imag.wrapping_add(src.imag) }
}

#[inline(always)]
pub fn entropy_approx(c: ComplexBit) -> u64 {
    let ns = c.norm_sq();
    if ns == 0 { return 0; }
    let log2_approx = 63 - ns.leading_zeros() as u64;
    ns.wrapping_mul(log2_approx)
}

// ============================================================
// §4. BSCM 並列エンジン（rayon）
// ============================================================

use rayon::prelude::*;

#[derive(Debug, Clone, Copy)]
pub struct BSCMState {
    pub state: ComplexBit,
    pub bound: u64,
    pub step:  u64,
}

impl BSCMState {
    #[inline(always)]
    pub fn step_complex(self) -> Option<Self> {
        if self.step >= self.bound { return None; }
        let z = self.state;
        let n = z.real;
        let even_path = ComplexBit { real: n >> 1,                          imag: n };
        let odd_path  = ComplexBit { real: 3u64.wrapping_mul(n).wrapping_add(1),
                                     imag: 3u64.wrapping_mul(z.imag) };
        Some(Self {
            state: ComplexBit::select(n & 1, odd_path, even_path),
            bound: self.bound,
            step:  self.step + 1,
        })
    }

    pub fn trajectory(self) -> Vec<ComplexBit> {
        let mut traj = Vec::with_capacity(256);
        let mut cur  = self;
        traj.push(cur.state);
        while let Some(next) = cur.step_complex() {
            traj.push(next.state);
            if next.state.real == 1 { break; }
            cur = next;
        }
        traj
    }

    pub fn norm_trajectory(self) -> Vec<u64> {
        self.trajectory().iter().map(|c| c.norm_sq()).collect()
    }
}

pub fn parallel_bscm_batch(initial_values: &[u64], bound: u64) -> Vec<Vec<ComplexBit>> {
    initial_values.par_iter()
        .map(|&n| BSCMState { state: ComplexBit::new(n, 0), bound, step: 0 }.trajectory())
        .collect()
}

pub fn parallel_max_norm(initial_values: &[u64], bound: u64) -> (u64, u64) {
    initial_values.par_iter()
        .map(|&n| {
            let max_ns = BSCMState { state: ComplexBit::new(n, 0), bound, step: 0 }
                .norm_trajectory().into_iter().max().unwrap_or(0);
            (n, max_ns)
        })
        .max_by_key(|&(_, ns)| ns)
        .unwrap_or((0, 0))
}

pub fn parallel_gate_apply<G: QuantumGate>(gate: &G, states: &[ComplexBit]) -> Vec<ComplexBit> {
    states.par_iter().map(|&c| gate.apply(c)).collect()
}

// ============================================================
// §5. 単体テスト
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn test_norm_sq()    { assert_eq!(ComplexBit::new(3,4).norm_sq(), 25); }
    #[test] fn test_add()        { assert_eq!(ComplexBit::new(2,3)+ComplexBit::new(4,5), ComplexBit::new(6,8)); }
    #[test] fn test_gate_z_inv() { let c=ComplexBit::new(3,5); assert_eq!(GateZ.apply(GateZ.apply(c)),c); }
    #[test] fn test_gate_z_norm(){ let c=ComplexBit::new(3,4); assert_eq!(GateZ.apply(c).norm_sq(),c.norm_sq()); }
    #[test] fn test_gate_x_inv() { let c=ComplexBit::new(3,5); assert_eq!(GateX.apply(GateX.apply(c)),c); }
    #[test] fn test_gate_x_norm(){ let c=ComplexBit::new(3,4); assert_eq!(GateX.apply(c).norm_sq(),c.norm_sq()); }
    #[test] fn test_gate_s_sq_z(){ let c=ComplexBit::new(3,5); assert_eq!(GateS.apply(GateS.apply(c)), -c); }
    #[test] fn test_gate_s_p4()  { let c=ComplexBit::new(7,11); assert_eq!(GateS.apply(GateS.apply(GateS.apply(GateS.apply(c)))),c); }
    #[test] fn test_sdag_inv()   { let c=ComplexBit::new(3,5); assert_eq!(GateSdag.apply(GateS.apply(c)),c); }
    #[test] fn test_s_norm()     { let c=ComplexBit::new(3,4); assert_eq!(GateS.apply(c).norm_sq(),c.norm_sq()); }

    #[test]
    fn test_cnot_control_unchanged() {
        let s = CNOTState { control: ComplexBit::new(1,0), target: ComplexBit::new(3,5) };
        assert_eq!(GateCNOT.apply(s).control, s.control);
    }
    #[test]
    fn test_cnot_zero_identity() {
        let s = CNOTState { control: ComplexBit::ZERO, target: ComplexBit::new(3,5) };
        assert_eq!(GateCNOT.apply(s).target, s.target);
    }
    #[test]
    fn test_cnot_involutive() {
        let s = CNOTState { control: ComplexBit::new(1,0), target: ComplexBit::new(3,5) };
        assert_eq!(GateCNOT.apply(GateCNOT.apply(s)), s);
    }
    #[test]
    fn test_cnot_applies_x() {
        let s = CNOTState { control: ComplexBit::new(1,0), target: ComplexBit::new(3,5) };
        assert_eq!(GateCNOT.apply(s).target, GateX.apply(s.target));
    }
    #[test]
    fn test_zxz_eq_x() {
        let c = ComplexBit::new(7,11);
        assert_eq!(GateZ.apply(GateX.apply(GateZ.apply(c))), (-ComplexBit { real: c.imag, imag: c.real }));
    }
    #[test]
    fn test_value_transfer() {
        let r = value_transfer(ComplexBit::new(0,10), ComplexBit::new(5,3));
        assert_eq!(r, ComplexBit::new(5,13));
    }
    #[test]
    fn test_bscm_even() {
        let s = BSCMState { state: ComplexBit::new(6,0), bound:100, step:0 };
        let n = s.step_complex().unwrap();
        assert_eq!(n.state, ComplexBit::new(3,6));
    }
    #[test]
    fn test_bscm_odd() {
        let s = BSCMState { state: ComplexBit::new(7,0), bound:100, step:0 };
        let n = s.step_complex().unwrap();
        assert_eq!(n.state.real, 22);
    }
    #[test]
    fn test_bscm_convergence() {
        let s = BSCMState { state: ComplexBit::new(27,0), bound:500, step:0 };
        assert_eq!(s.trajectory().last().unwrap().real, 1);
    }
    #[test]
    fn test_parallel_batch() {
        let inputs: Vec<u64> = (2..=100).collect();
        let results = parallel_bscm_batch(&inputs, 1000);
        for traj in &results {
            assert_eq!(traj.last().unwrap().real, 1);
        }
    }
    #[test]
    fn test_parallel_gate() {
        let states: Vec<ComplexBit> = (0..100).map(|i| ComplexBit::new(i,i*2)).collect();
        let results = parallel_gate_apply(&GateS, &states);
        for (i, &c) in states.iter().enumerate() { assert_eq!(results[i], GateS.apply(c)); }
    }
}
