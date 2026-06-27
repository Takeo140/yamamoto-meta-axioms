/*
 * F-Theory MetaAxioms64 — OpenCL カーネル
 * License Apache 2.0 Takeo Yamamoto
 *
 * 設計:
 *   各スレッド(gid)が1つの64ビット状態を担当。
 *   バッチサイズ = グローバルワークサイズ = 任意（推奨: 2^20 以上）
 *
 * メモリレイアウト:
 *   states[gid * 128 + k*2 + 0] = bits[k].re
 *   states[gid * 128 + k*2 + 1] = bits[k].im
 *   (64ビット × 2 float = 128 float / 状態)
 *
 * F-Theory 公理対応:
 *   A1 可逆性   — apply_gate2x2 はユニタリ変換
 *   A2 連続性   — float演算で連続位相空間を表現
 *   A3 情報保存 — norm_sq は変換前後で不変
 *   A4 価値生成 — H/Ry で Im成分（価値）を生成
 */

// ─── 複素数演算 ─────────────────────────────────────────────
inline float2 cmul(float2 a, float2 b) {
    return (float2)(a.x*b.x - a.y*b.y,
                    a.x*b.y + a.y*b.x);
}
inline float2 cadd(float2 a, float2 b) {
    return (float2)(a.x+b.x, a.y+b.y);
}
inline float  cnorm2(float2 a) { return a.x*a.x + a.y*a.y; }
inline float2 exp_i(float theta) {
    return (float2)(cos(theta), sin(theta));
}

// ─── 2×2 ゲート適用（A1: ユニタリ変換）───────────────────
inline void apply_gate2x2(
    float2 *a, float2 *b,
    float u00re, float u00im,
    float u01re, float u01im,
    float u10re, float u10im,
    float u11re, float u11im)
{
    float2 u00 = (float2)(u00re, u00im);
    float2 u01 = (float2)(u01re, u01im);
    float2 u10 = (float2)(u10re, u10im);
    float2 u11 = (float2)(u11re, u11im);
    float2 na = cadd(cmul(u00, *a), cmul(u01, *b));
    float2 nb = cadd(cmul(u10, *a), cmul(u11, *b));
    *a = na; *b = nb;
}

// ─── ビット k の振幅を取得/設定 ─────────────────────────
inline float2 get_bit(__global float *s, int gid, int k) {
    int base = gid * 128 + k * 2;
    return (float2)(s[base], s[base+1]);
}
inline void set_bit(__global float *s, int gid, int k, float2 v) {
    int base = gid * 128 + k * 2;
    s[base]   = v.x;
    s[base+1] = v.y;
}

// ============================================================
// カーネル 1: applyGate1Q
//   全バッチの各状態のビット k に 2x2 ゲートを適用（A1, A2）
// ============================================================
__kernel void applyGate1Q(
    __global float *states,
    int k,
    float u00re, float u00im,
    float u01re, float u01im,
    float u10re, float u10im,
    float u11re, float u11im)
{
    int gid = get_global_id(0);
    float2 a, b;
    // 単一ビットの re→|0⟩成分, im→|1⟩成分 として扱う
    float2 c = get_bit(states, gid, k);
    a = (float2)(c.x, 0.0f);
    b = (float2)(c.y, 0.0f);
    apply_gate2x2(&a, &b,
        u00re, u00im, u01re, u01im,
        u10re, u10im, u11re, u11im);
    set_bit(states, gid, k, (float2)(a.x, b.x));
}

// ============================================================
// カーネル 2: interfere
//   ビット k と j の間の2ビット干渉（A4: 価値生成の主役）
// ============================================================
__kernel void interfere(
    __global float *states,
    int k, int j,
    float u00re, float u00im,
    float u01re, float u01im,
    float u10re, float u10im,
    float u11re, float u11im)
{
    int gid = get_global_id(0);
    float2 a = get_bit(states, gid, k);
    float2 b = get_bit(states, gid, j);
    apply_gate2x2(&a, &b,
        u00re, u00im, u01re, u01im,
        u10re, u10im, u11re, u11im);
    set_bit(states, gid, k, a);
    set_bit(states, gid, j, b);
}

// ============================================================
// カーネル 3: phaseRotate
//   ビット k に位相回転 e^{i*theta} を掛ける（A2: 連続性）
// ============================================================
__kernel void phaseRotate(
    __global float *states,
    int k,
    float theta)
{
    int gid = get_global_id(0);
    float2 c   = get_bit(states, gid, k);
    float2 rot = exp_i(theta);
    set_bit(states, gid, k, cmul(c, rot));
}

// ============================================================
// カーネル 4: bscmCircuit
//   BSCMフル回路を1カーネルで実行（ローンチオーバーヘッド削減）
//   H×32(偶数ビット) + Rz(π/4)×32(奇数ビット) + interfere×32
// ============================================================
__kernel void bscmCircuit(__global float *states, float rz_phi)
{
    int gid = get_global_id(0);

    float inv_sqrt2 = 0.70710678118f;
    float cp = cos(rz_phi * 0.5f);
    float sp = sin(rz_phi * 0.5f);

    // H を偶数ビットに適用（A4: 情報→価値生成）
    for (int k = 0; k < 64; k += 2) {
        float2 c = get_bit(states, gid, k);
        float2 a = (float2)(c.x, 0.0f);
        float2 b = (float2)(c.y, 0.0f);
        float2 na = (float2)((a.x + b.x) * inv_sqrt2, (a.y + b.y) * inv_sqrt2);
        float2 nb = (float2)((a.x - b.x) * inv_sqrt2, (a.y - b.y) * inv_sqrt2);
        set_bit(states, gid, k, (float2)(na.x, nb.x));
    }

    // Rz(phi) を奇数ビットに適用（A2: 連続位相変化）
    for (int k = 1; k < 64; k += 2) {
        float2 c = get_bit(states, gid, k);
        float2 a = (float2)(c.x, 0.0f);
        float2 b = (float2)(c.y, 0.0f);
        // Rz: diag(e^{-i*phi/2}, e^{i*phi/2})
        float2 rot_minus = (float2)(cp, -sp);
        float2 rot_plus  = (float2)(cp,  sp);
        float2 na = cmul(rot_minus, a);
        float2 nb = cmul(rot_plus,  b);
        set_bit(states, gid, k, (float2)(na.x, nb.x));
    }

    // ビット k と k+32 の干渉（情報↔価値の相互作用）
    for (int k = 0; k < 32; k++) {
        float2 a = get_bit(states, gid, k);
        float2 b = get_bit(states, gid, k + 32);
        float2 na = (float2)((a.x + b.x) * inv_sqrt2, (a.y + b.y) * inv_sqrt2);
        float2 nb = (float2)((a.x - b.x) * inv_sqrt2, (a.y - b.y) * inv_sqrt2);
        set_bit(states, gid, k,      na);
        set_bit(states, gid, k + 32, nb);
    }
}

// ============================================================
// カーネル 5: computeMetrics
//   各状態のエントロピー・情報量・価値量を一括計算（A3確認）
//   outputs[gid*3+0] = entropy
//   outputs[gid*3+1] = total_info (sum |re|)
//   outputs[gid*3+2] = total_value (sum |im|)
// ============================================================
__kernel void computeMetrics(
    __global const float *states,
    __global float *outputs)
{
    int gid = get_global_id(0);
    float entropy = 0.0f;
    float info    = 0.0f;
    float value   = 0.0f;

    for (int k = 0; k < 64; k++) {
        float2 c = get_bit((__global float*)states, gid, k);
        float p = cnorm2(c);
        if (p > 1e-15f) entropy -= p * log2(p);
        info  += fabs(c.x);
        value += fabs(c.y);
    }

    outputs[gid * 3 + 0] = entropy;
    outputs[gid * 3 + 1] = info;
    outputs[gid * 3 + 2] = value;
}

// ============================================================
// カーネル 6: initFromUInt64
//   64ビット整数バッチから状態を初期化
//   inputs[gid] = UInt64 入力値
// ============================================================
__kernel void initFromUInt64(
    __global ulong *inputs,
    __global float *states)
{
    int gid = get_global_id(0);
    ulong n = inputs[gid];

    for (int k = 0; k < 64; k++) {
        float re, im;
        if ((n >> k) & 1UL) {
            re = 0.0f; im = 1.0f;  // |1⟩ = 価値状態
        } else {
            re = 1.0f; im = 0.0f;  // |0⟩ = 情報状態
        }
        int base = gid * 128 + k * 2;
        states[base]   = re;
        states[base+1] = im;
    }
}

// ============================================================
// カーネル 7: projectToUInt64
//   位相状態を64ビット整数に射影（|im|>|re| なら 1）
//   outputs[gid] = 射影結果
// ============================================================
__kernel void projectToUInt64(
    __global const float *states,
    __global ulong *outputs)
{
    int gid = get_global_id(0);
    ulong result = 0UL;

    for (int k = 0; k < 64; k++) {
        float2 c = get_bit((__global float*)states, gid, k);
        if (fabs(c.y) > fabs(c.x)) {
            result |= (1UL << k);
        }
    }
    outputs[gid] = result;
}

