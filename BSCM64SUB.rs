#![no_std]

const U64_MAX: u64 = u64::MAX;

#[inline(always)]
pub fn bscm_delta(s: u64) -> u64 {
    if (s & 1) == 0       { return s >> 1; }
    if (s & 3) == 1       { return (s - 1) >> 1; }
    U64_MAX ^ s
}

/// 循環検出付き実行
/// 循環を検出したら +1 ビット加算で軌道脱出
pub fn bscm_exec_corrected(initial_state: u64) -> u64 {
    let mut s = initial_state;
    let mut steps: u64 = 0;
    let mut last_seen: u64 = 0;
    let mut cycle_count: u64 = 0;

    while s != 1 && steps < u64::MAX {
        let next = bscm_delta(s);
        // 循環検出：前回値と一致
        if next == last_seen {
            cycle_count += 1;
            s = s.wrapping_add(cycle_count); // ビット加算で脱出
        } else {
            last_seen = s;
            s = next;
        }
        steps += 1;
    }
    steps
}

pub fn evaluate_bscm_complexity(input: u64) -> u64 {
    if input == 0 { return 0; }
    let initial_state = (input & 0x7FFFFFFFFFFFFFFF) << 1 | 1;
    bscm_exec_corrected(initial_state)
}
