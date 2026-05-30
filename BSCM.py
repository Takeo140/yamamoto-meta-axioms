#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Bounded Smooth Collatz Machine (BSCM) - 64-bit Engineering Version
Monotone Reduction δ: all branches state-reducing

Author: Takeo Yamamoto
License: Apache-2.0
"""

MASK_64 = 0xFFFFFFFFFFFFFFFF  # 2**64 - 1

def bscm_delta_64(s: int) -> int:
    """
    Engineering δ — 64-bit monotone reduction.
    Even: s >> 1
    Odd:  (s + 1) >> 1
    Both branches strictly reduce state. No perturbation term.
    """
    s = s & MASK_64
    if s % 2 == 0:
        return s >> 1
    else:
        return ((s + 1) >> 1) & MASK_64


def evaluate_bscm_complexity_64(input_val: int) -> int:
    """
    Projects arbitrary input into 64-bit odd state space,
    then counts steps to reach state 1.
    Returns step count, or step count + 100_000_000 if a cycle is detected.
    """
    if input_val == 0:
        return 0

    initial_state = ((input_val % (1 << 63)) * 2 + 1) & MASK_64
    current_state = initial_state
    total_clock = 0
    visited_states = set()

    while current_state != 1:
        if current_state in visited_states:
            return total_clock + 100_000_000
        visited_states.add(current_state)
        current_state = bscm_delta_64(current_state)
        total_clock += 1

    return total_clock


if __name__ == "__main__":
    print("=== Bounded Smooth Collatz Machine (BSCM) ===")
    print("=== 64-bit Engineering Version ===")
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
