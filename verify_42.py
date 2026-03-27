"""
verify_42.py - Integration test for Yamamoto Meta-Axioms
Author: Takeo Yamamoto
License: CC BY 4.0

Tests A1–A4 explicitly. Prior version tested only A1.
Exit 0 = all assertions pass (GitHub Actions green).
Exit 1 = any assertion fails.
"""

import sys
import os

sys.path.append(os.path.dirname(os.path.abspath(__file__)))

try:
    from axioms import MetaAxioms
except ImportError:
    print("CRITICAL ERROR: axioms.py not found.")
    sys.exit(1)


def run_tests():
    failures = []

    # ── A1: Extremum Principle ────────────────────────────────────────────
    search_space = list(range(0, 101))
    found_x = MetaAxioms.axiom1_extremum(search_space, lambda x: abs(x - 42))
    if found_x != 42:
        failures.append(f"A1 FAILED: expected 42, got {found_x}")

    # ── A2: Topological Space (boundary check) ────────────────────────────
    domain = set(range(0, 101))
    if not MetaAxioms.axiom2_boundary_check(42, domain):
        failures.append("A2 FAILED: 42 not found in domain [0, 100]")
    if MetaAxioms.axiom2_boundary_check(101, domain):
        failures.append("A2 FAILED: 101 incorrectly accepted as inside domain")

    # ── A3: Logical Consistency ───────────────────────────────────────────
    if not MetaAxioms.axiom3_consistency(found_x, 42):
        failures.append(f"A3 FAILED: found_x={found_x} inconsistent with 42")
    if MetaAxioms.axiom3_consistency(found_x, 99):
        failures.append("A3 FAILED: 42 == 99 should be False")

    # ── A4: Hierarchical Structure (convex combination) ───────────────────
    micro = [10.0, 20.0, 30.0]
    weights = [0.2, 0.3, 0.5]   # sum = 1.0
    macro = MetaAxioms.axiom4_hierarchical_sum(micro, weights)
    expected = 0.2*10 + 0.3*20 + 0.5*30  # = 23.0
    if abs(macro - expected) > 1e-9:
        failures.append(f"A4 FAILED: expected {expected}, got {macro}")

    # A4 uniform weights (None → 1/n each)
    macro_uniform = MetaAxioms.axiom4_hierarchical_sum([42.0, 42.0, 42.0])
    if abs(macro_uniform - 42.0) > 1e-9:
        failures.append(f"A4 uniform FAILED: expected 42.0, got {macro_uniform}")

    # A4 should reject non-convex weights
    try:
        MetaAxioms.axiom4_hierarchical_sum([1.0, 2.0], weights=[1.0, 1.0])
        failures.append("A4 FAILED: did not raise on non-convex weights (sum=2)")
    except ValueError:
        pass  # expected

    # ── Report ────────────────────────────────────────────────────────────
    if failures:
        print("FAILED:")
        for f in failures:
            print(f"  {f}")
        sys.exit(1)

    print("------------------------------------")
    print(" YAMAMOTO META-AXIOMS: INTEGRATED ")
    print(" CI STATUS: GREEN                 ")
    print(" A1 A2 A3 A4: ALL PASS            ")
    print(" RESULT: 42                        ")
    print("------------------------------------")
    sys.exit(0)


if __name__ == "__main__":
    run_tests()
