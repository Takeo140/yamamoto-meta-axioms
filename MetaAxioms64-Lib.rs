// License Apache 2.0 Takeo Yamamoto
use bytemuck::{Pod, Zeroable};
use std::thread;

#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct ComplexAmp { pub re: f32, pub im: f32 }

impl ComplexAmp {
    pub const ZERO: Self = Self { re: 0.0, im: 0.0 };
    pub const ONE:  Self = Self { re: 1.0, im: 0.0 };
    pub const I:    Self = Self { re: 0.0, im: 1.0 };

    #[inline] pub fn norm_sq(self) -> f32 { self.re*self.re + self.im*self.im }
    #[inline] pub fn magnitude(self) -> f32 { self.norm_sq().sqrt() }
    #[inline] pub fn phase(self) -> f32 { self.im.atan2(self.re) }
    #[inline] pub fn mul(self, b: Self) -> Self {
        Self { re: self.re*b.re - self.im*b.im, im: self.re*b.im + self.im*b.re }
    }
    #[inline] pub fn add(self, b: Self) -> Self {
        Self { re: self.re+b.re, im: self.im+b.im }
    }
    pub fn entropy_contrib(self) -> f32 {
        let p = self.norm_sq();
        if p < 1e-15 { 0.0 } else { -p * p.log2() }
    }
    pub fn exp_i(theta: f32) -> Self { Self { re: theta.cos(), im: theta.sin() } }
}

#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Gate2x2 {
    pub u00re: f32, pub u00im: f32,
    pub u01re: f32, pub u01im: f32,
    pub u10re: f32, pub u10im: f32,
    pub u11re: f32, pub u11im: f32,
}

impl Gate2x2 {
    pub fn apply(&self, a: ComplexAmp, b: ComplexAmp) -> (ComplexAmp, ComplexAmp) {
        let u00 = ComplexAmp { re: self.u00re, im: self.u00im };
        let u01 = ComplexAmp { re: self.u01re, im: self.u01im };
        let u10 = ComplexAmp { re: self.u10re, im: self.u10im };
        let u11 = ComplexAmp { re: self.u11re, im: self.u11im };
        (u00.mul(a).add(u01.mul(b)), u10.mul(a).add(u11.mul(b)))
    }
    pub fn dagger(&self) -> Self {
        Self { u00re: self.u00re, u00im: -self.u00im,
               u01re: self.u10re, u01im: -self.u10im,
               u10re: self.u01re, u10im: -self.u01im,
               u11re: self.u11re, u11im: -self.u11im }
    }
    pub fn h() -> Self {
        let v = 1.0_f32 / 2.0_f32.sqrt();
        Self { u00re:v, u00im:0.0, u01re:v,  u01im:0.0,
               u10re:v, u10im:0.0, u11re:-v, u11im:0.0 }
    }
    pub fn x() -> Self { Self { u00re:0.0,u00im:0.0,u01re:1.0,u01im:0.0,
                                u10re:1.0,u10im:0.0,u11re:0.0,u11im:0.0 } }
    pub fn y() -> Self { Self { u00re:0.0,u00im:0.0, u01re:0.0,u01im:-1.0,
                                u10re:0.0,u10im:1.0, u11re:0.0,u11im:0.0 } }
    pub fn z() -> Self { Self { u00re:1.0,u00im:0.0,u01re:0.0, u01im:0.0,
                                u10re:0.0,u10im:0.0,u11re:-1.0,u11im:0.0 } }
    pub fn ry(theta: f32) -> Self {
        let (c,s) = ((theta/2.0).cos(), (theta/2.0).sin());
        Self { u00re:c, u00im:0.0, u01re:-s, u01im:0.0,
               u10re:s, u10im:0.0, u11re:c,  u11im:0.0 }
    }
    pub fn rz(theta: f32) -> Self {
        let (cm,sm) = ((-theta/2.0).cos(), (-theta/2.0).sin());
        let (cp,sp) = (( theta/2.0).cos(), ( theta/2.0).sin());
        Self { u00re:cm,u00im:sm, u01re:0.0,u01im:0.0,
               u10re:0.0,u10im:0.0, u11re:cp,u11im:sp }
    }
    pub fn p(phi: f32) -> Self {
        Self { u00re:1.0,u00im:0.0, u01re:0.0,u01im:0.0,
               u10re:0.0,u10im:0.0, u11re:phi.cos(),u11im:phi.sin() }
    }
}

#[derive(Debug, Clone)]
pub struct MetaAxioms64State { pub bits: [ComplexAmp; 64] }

impl MetaAxioms64State {
    pub fn init() -> Self { Self { bits: [ComplexAmp::ONE; 64] } }
    pub fn from_u64(n: u64) -> Self {
        let mut bits = [ComplexAmp::ZERO; 64];
        for k in 0..64 {
            bits[k] = if (n >> k) & 1 == 1 { ComplexAmp::I } else { ComplexAmp::ONE };
        }
        Self { bits }
    }
    #[inline]
    pub fn apply_gate1(&mut self, k: usize, g: &Gate2x2) {
        let c = self.bits[k];
        let (a2, b2) = g.apply(ComplexAmp{re:c.re,im:0.0}, ComplexAmp{re:c.im,im:0.0});
        self.bits[k] = ComplexAmp { re: a2.re, im: b2.re };
    }
    #[inline]
    pub fn interfere(&mut self, k: usize, j: usize, g: &Gate2x2) {
        let (a2, b2) = g.apply(self.bits[k], self.bits[j]);
        self.bits[k] = a2; self.bits[j] = b2;
    }
    #[inline]
    pub fn phase_rotate(&mut self, k: usize, theta: f32) {
        self.bits[k] = self.bits[k].mul(ComplexAmp::exp_i(theta));
    }
    pub fn total_entropy(&self) -> f32 { self.bits.iter().map(|c| c.entropy_contrib()).sum() }
    pub fn total_value(&self)   -> f32 { self.bits.iter().map(|c| c.im.abs()).sum() }
    pub fn total_info(&self)    -> f32 { self.bits.iter().map(|c| c.re.abs()).sum() }
    pub fn project_to_u64(&self) -> u64 {
        let mut r = 0u64;
        for k in 0..64 { if self.bits[k].im.abs() > self.bits[k].re.abs() { r |= 1u64<<k; } }
        r
    }
}

/// BSCMフル回路を1件実行
#[inline]
pub fn run_bscm_circuit(n: u64) -> u64 {
    let h  = Gate2x2::h();
    let rz = Gate2x2::rz(std::f32::consts::FRAC_PI_4);
    let mut s = MetaAxioms64State::from_u64(n);
    for k in (0..64).step_by(2) { s.apply_gate1(k, &h);  }
    for k in (1..64).step_by(2) { s.apply_gate1(k, &rz); }
    for k in 0..32 { s.interfere(k, k+32, &h); }
    s.project_to_u64()
}

/// メトリクス計算を1件実行
#[inline]
pub fn run_metrics(n: u64) -> (f32, f32, f32) {
    let h  = Gate2x2::h();
    let rz = Gate2x2::rz(std::f32::consts::FRAC_PI_4);
    let mut s = MetaAxioms64State::from_u64(n);
    for k in (0..64).step_by(2) { s.apply_gate1(k, &h);  }
    for k in (1..64).step_by(2) { s.apply_gate1(k, &rz); }
    for k in 0..32 { s.interfere(k, k+32, &h); }
    (s.total_entropy(), s.total_info(), s.total_value())
}

/// 標準スレッドによるバッチ並列処理
pub fn bscm_batch_parallel(inputs: &[u64], num_threads: usize) -> Vec<u64> {
    let chunk = (inputs.len() + num_threads - 1) / num_threads;
    let inputs: Vec<u64> = inputs.to_vec();
    let handles: Vec<_> = (0..num_threads).map(|t| {
        let start = t * chunk;
        let end   = ((t+1)*chunk).min(inputs.len());
        let slice = inputs[start..end].to_vec();
        thread::spawn(move || slice.iter().map(|&n| run_bscm_circuit(n)).collect::<Vec<_>>())
    }).collect();
    handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
}

pub fn metrics_batch_parallel(inputs: &[u64], num_threads: usize) -> Vec<(f32,f32,f32)> {
    let chunk = (inputs.len() + num_threads - 1) / num_threads;
    let inputs: Vec<u64> = inputs.to_vec();
    let handles: Vec<_> = (0..num_threads).map(|t| {
        let start = t * chunk;
        let end   = ((t+1)*chunk).min(inputs.len());
        let slice = inputs[start..end].to_vec();
        thread::spawn(move || slice.iter().map(|&n| run_metrics(n)).collect::<Vec<_>>())
    }).collect();
    handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
}
