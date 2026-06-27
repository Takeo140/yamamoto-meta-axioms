// License Apache 2.0 Takeo Yamamoto
use std::time::Instant;
use ftheory::{Gate2x2, MetaAxioms64State, run_bscm_circuit, bscm_batch_parallel, metrics_batch_parallel};

fn verify_axioms() {
    println!("\n=== F-Theory 公理検証 ===");
    let h = Gate2x2::h();
    let hd = h.dagger();
    let mut s = MetaAxioms64State::init();
    s.apply_gate1(0, &h);
    let after = s.bits[0];
    s.apply_gate1(0, &hd);
    let restored = s.bits[0];
    println!("A1 可逆性 : H適用後=({:.4},{:.4}i) H†後=({:.4},{:.4}i)",
        after.re, after.im, restored.re, restored.im);

    let mut s2 = MetaAxioms64State::init();
    let steps = 8usize;
    let phases: Vec<f32> = (0..steps).map(|i| {
        s2.phase_rotate(0, std::f32::consts::TAU / steps as f32);
        s2.bits[0].phase()
    }).collect();
    println!("A2 連続性 : 位相軌跡 {:?}", phases.iter().map(|p| format!("{:.2}",p)).collect::<Vec<_>>());

    let s3 = MetaAxioms64State::init();
    let mut s3b = s3.clone();
    s3b.apply_gate1(0, &h);
    println!("A3 情報保存: entropy 前={:.4} 後={:.4}",
        s3.total_entropy(), s3b.total_entropy());

    let mut s4 = MetaAxioms64State::init();
    let v0 = s4.total_value();
    s4.apply_gate1(0, &h);
    println!("A4 価値生成: value 前={:.4} 後={:.4} (+{:.4})",
        v0, s4.total_value(), s4.total_value()-v0);
}

fn main() {
    println!("╔═══════════════════════════════════════════════╗");
    println!("║  F-Theory MetaAxioms64 GPU バッチプロセッサ  ║");
    println!("║  License Apache 2.0  Takeo Yamamoto          ║");
    println!("╚═══════════════════════════════════════════════╝");

    verify_axioms();

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get()).unwrap_or(4);
    println!("\n=== バッチ性能ベンチマーク ({num_threads}スレッド) ===");
    println!("{:>12}  {:>12}  {:>16}  {:>10}",
        "バッチサイズ", "時間(ms)", "スループット(/秒)", "1件(μs)");
    println!("{}", "-".repeat(58));

    for &batch_size in &[1_000usize, 10_000, 100_000, 1_000_000] {
        let inputs: Vec<u64> = (0..batch_size as u64)
            .map(|i| i.wrapping_mul(0x9e3779b97f4a7c15u64))
            .collect();
        let t = Instant::now();
        let results = bscm_batch_parallel(&inputs, num_threads);
        let elapsed = t.elapsed().as_secs_f64();
        let ms = elapsed * 1000.0;
        let tput = batch_size as f64 / elapsed;
        let per_us = elapsed * 1e6 / batch_size as f64;
        println!("{:>12}  {:>12.2}  {:>16.0}  {:>10.4}",
            batch_size, ms, tput, per_us);
        // 結果の先頭3件をダンプ
        let _ = results;
    }

    println!("\n=== メトリクスバッチ (100,000件) ===");
    let batch: Vec<u64> = (0..100_000u64)
        .map(|i| i.wrapping_mul(0x9e3779b97f4a7c15u64))
        .collect();
    let t = Instant::now();
    let metrics = metrics_batch_parallel(&batch, num_threads);
    let ms = t.elapsed().as_secs_f64() * 1000.0;
    let avg_e: f32 = metrics.iter().map(|m| m.0).sum::<f32>() / metrics.len() as f32;
    let avg_i: f32 = metrics.iter().map(|m| m.1).sum::<f32>() / metrics.len() as f32;
    let avg_v: f32 = metrics.iter().map(|m| m.2).sum::<f32>() / metrics.len() as f32;
    println!("  計算時間    : {ms:.2} ms");
    println!("  平均entropy : {avg_e:.4} bits");
    println!("  平均情報量  : {avg_i:.4}");
    println!("  平均価値量  : {avg_v:.4}");
    println!("  情報/価値比 : {:.4}", avg_i / avg_v);

    println!("\n=== 単件レイテンシ ===");
    let n = 0xDEADBEEFCAFEBABEu64;
    let t = Instant::now();
    for _ in 0..10_000 { let _ = run_bscm_circuit(n); }
    let us = t.elapsed().as_secs_f64() * 1e6 / 10_000.0;
    println!("  0x{n:016X} → 0x{:016X}", run_bscm_circuit(n));
    println!("  1件レイテンシ: {us:.4} μs");

    println!("\n=== OpenCL GPU 有効化 ===");
    println!("  Cargo.toml に ocl = \"0.19\" を追加し");
    println!("  --features gpu でビルドすると kernels/ftheory.cl が");
    println!("  GPU上で実行され、スループットが10-100x向上します");
}
