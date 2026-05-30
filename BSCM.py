#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Bounded Smooth Collatz Machine (BSCM) - 64-bit Engineering Version (Optimized)
Monotone Reduction δ: all branches state-reducing

Author: Takeo Yamamoto
License: Apache-2.0
"""

MASK_64 = 0xFFFFFFFFFFFFFFFF  # 2**64 - 1

def evaluate_bscm_complexity_64(input_val: int) -> int:
    """
    Projects arbitrary input into 64-bit odd state space,
    then counts steps to reach state 1.
    Optimized: Removed redundant cycle detection and inlined delta function.
    """
    if input_val == 0:
        return 0

    # 64ビットの奇数空間へのマッピング
    current_state = ((input_val % (1 << 63)) * 2 + 1) & MASK_64
    total_clock = 0

    # 単調減少するためサイクルは発生しない（visited_statesのセットは不要）
    while current_state != 1:
        if current_state % 2 == 0:
            current_state >>= 1
        else:
            current_state = ((current_state + 1) >> 1) & MASK_64
        total_clock += 1

    return total_clock


if __name__ == "__main__":
    print("=== Bounded Smooth Collatz Machine (BSCM) ===")
    print("=== 64-bit Engineering Version (Optimized) ===")
    print("License: Apache-2.0\n")

    test_inputs = [
        1024,
        123456789,
        987654321012345,
        1844674407370955161,
    ]

    print(f"{'Input Value':<22} | {'Mapped 64-bit Init State':<25} | {'Total Steps (Clock)':<20}")
    print("-" * 75)

    for val in test_inputs:
        init_state = ((val % (1 << 63)) * 2 + 1) & MASK_64
        steps = evaluate_bscm_complexity_64(val)
        print(f"{val:<22} | {init_state:<25} | {steps:<20}")
