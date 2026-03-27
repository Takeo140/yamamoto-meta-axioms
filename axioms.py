"""
axioms.py - Reference implementation of Yamamoto Meta-Axioms
Author: Takeo Yamamoto
License: CC BY 4.0

Fixes from prior version:
- axiom4: weights=None defaulted to all-1.0 (not a convex combination).
  Now raises ValueError if weights do not sum to 1.
- axiom3: return value changed from int (0/1) to bool for clarity.
- Added normalize_weights() helper for caller convenience.
"""

import numpy as np


class MetaAxioms:
    """
    Reference implementation of the four Meta-Axioms.
    Each method corresponds to one axiom (A1–A4).
    """

    @staticmethod
    def axiom1_extremum(search_space, loss_function):
        """
        A1: Extremum Principle
        Returns x* = argmin_{x in X} L(x).
        """
        costs = [loss_function(x) for x in search_space]
        return search_space[int(np.argmin(costs))]

    @staticmethod
    def axiom2_boundary_check(x, boundary_condition):
        """
        A2: Topological Space
        Returns True iff x lies within the defined domain X.
        """
        return x in boundary_condition

    @staticmethod
    def axiom3_consistency(found_value, expected_value):
        """
        A3: Logical Consistency
        Returns True (consistent) iff found_value == expected_value.
        Replaces prior int 0/1 return — bool is unambiguous.
        """
        return found_value == expected_value

    @staticmethod
    def normalize_weights(weights):
        """
        Helper: normalize a weight vector to a convex combination (sum=1).
        Raises ValueError if all weights are zero.
        """
        total = sum(weights)
        if total == 0:
            raise ValueError("weights must not all be zero")
        return [w / total for w in weights]

    @staticmethod
    def axiom4_hierarchical_sum(micro_results, weights=None):
        """
        A4: Hierarchical Structure
        F_macro = sum_i w_i * F_micro(i)

        weights must form a convex combination: all >= 0, sum == 1.
        If weights is None, uniform weights are used (1/n each).
        Raises ValueError if weights do not sum to 1 (tolerance 1e-9).
        """
        n = len(micro_results)
        if n == 0:
            return 0.0

        if weights is None:
            weights = [1.0 / n] * n  # uniform convex combination

        total = sum(weights)
        if abs(total - 1.0) > 1e-9:
            raise ValueError(
                f"A4 requires weights to sum to 1 (convex combination); "
                f"got sum={total:.6f}. Use MetaAxioms.normalize_weights() "
                f"to fix."
            )
        if any(w < 0 for w in weights):
            raise ValueError("A4 requires all weights to be non-negative.")

        return sum(w * res for w, res in zip(weights, micro_results))
