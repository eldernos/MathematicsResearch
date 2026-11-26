#!/usr/bin/env python3
"""Regression tests for Phase 21 Track G1 corrections.

Verifies:
1. Strict inclusion K_b ⊊ K_{b^k} for k ≥ 2 via the exact witness x = 1/(b^k - 1):
   in base b^k it is a fixed point (D_N = 1 for all N ≥ 1), while in base b its
   orbit cycles through k distinct points {b^j/(b^k - 1) : 0 ≤ j < k}, giving
   exact periodic discrepancy < 1.
2. Registry statements GF-15 and GF-18 preserve the corrected scopes (strict
   inclusion K_b ⊊ K_{b^k}, non-Liouville status open for Theorem U, and
   explicit external-input framing for Mira Cult's Erdős-Borwein deduction).
"""

from __future__ import annotations

from fractions import Fraction
import pathlib
import tomllib
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent


def exact_periodic_discrepancy(points: list[Fraction]) -> Fraction:
    """Exact interval discrepancy of the uniform empirical measure on `points` in [0, 1)."""
    pts = sorted(points)
    d = len(pts)
    assert d >= 1
    assert all(0 <= p < 1 for p in pts)
    best = Fraction(0)
    # Candidate suprema over half-open intervals [a, c) in [0, 1):
    # - Empty open gaps between consecutive points (and [0, pts[0]), (pts[-1], 1)):
    best = max(best, pts[0], Fraction(1) - pts[-1])
    for i in range(d - 1):
        best = max(best, pts[i + 1] - pts[i])
    # - Intervals [pts[i], pts[j] + eps) containing m = j - i + 1 points of length pts[j] - pts[i]:
    for i in range(d):
        for j in range(i, d):
            m = j - i + 1
            best = max(best, Fraction(m, d) - (pts[j] - pts[i]))
    # - Intervals (pts[i], pts[j]) containing j - i - 1 points of length pts[j] - pts[i]:
    for i in range(d):
        for j in range(i + 1, d):
            m = j - i - 1
            best = max(best, (pts[j] - pts[i]) - Fraction(m, d))
    # - Intervals [0, pts[j]) and (pts[i], 1):
    for j in range(d):
        best = max(best, pts[j] - Fraction(j, d))
    for i in range(d):
        best = max(best, (Fraction(1) - pts[i]) - Fraction(d - 1 - i, d))
    return best


class TestPhase21Corrections(unittest.TestCase):
    def test_strict_radix_power_inclusion_witness(self):
        """x = 1/(b^k - 1) lies in K_{b^k} \\ K_b for all b >= 2, k >= 2."""
        for b in range(2, 8):
            for k in range(2, 6):
                denom = b**k - 1
                x = Fraction(1, denom)
                # Fixed by multiplication by b^k modulo 1:
                self.assertEqual((b**k * x) % 1, x)
                # Base-b orbit has exact period k with k distinct points:
                orbit = [Fraction(b**j, denom) for j in range(k)]
                self.assertEqual(len(set(orbit)), k)
                self.assertTrue(all(0 < p < 1 for p in orbit))
                self.assertEqual((b * orbit[-1]) % 1, orbit[0])
                disc = exact_periodic_discrepancy(orbit)
                self.assertLess(disc, Fraction(1), f"b={b}, k={k} must have D_inf < 1")
                self.assertGreater(disc, Fraction(0))
                # Specifically for b=2, k=2 (x = 1/3): orbit {1/3, 2/3}, exact discrepancy 2/3.
                if b == 2 and k == 2:
                    self.assertEqual(disc, Fraction(2, 3))

    def test_registry_gf15_and_gf18_corrected(self):
        gf_path = ROOT / "docs" / "registry" / "GF.toml"
        data = tomllib.loads(gf_path.read_text(encoding="utf-8"))
        by_id = {entry["id"]: entry for entry in data["result"]}

        gf15 = by_id["GF-15"]
        self.assertNotIn("normal and non-Liouville", gf15["statement"])
        self.assertIn("non-Liouville status", gf15["scope"])

        gf18 = by_id["GF-18"]
        self.assertNotIn("K_b = K_{b^k}", gf18["statement"])
        self.assertIn("K_b ⊊ K_{b^k}", gf18["statement"])
        self.assertIn("1498319", gf18["statement"])


if __name__ == "__main__":
    unittest.main()
