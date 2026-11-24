"""Regression checks for intersected modular cells and rational kernel design."""
import unittest
from fractions import Fraction as Q
from math import gcd

from discrepancy_experiments import log_bits, quadratic_residue_witnesses
from kernel_coverage import block_discrepancy, coefficients, constrained_integer_model, enclosure, endpoint_bound, scan
from localized_certificate import certificate
from overlap_certificate import failed_intervals, joint_box_bound, joint_upper_density


class OverlapTests(unittest.TestCase):
    def test_joint_geometry(self):
        support = [2, 5, 13]
        a, b = [failed_intervals(p, certificate(2, support, p, 1)) for p in (5, 13)]
        self.assertEqual((a, b), ([(2, 4)], [(10, 13)]))
        low, high = joint_upper_density(5, a, 13, b, Q(1, 10**10))
        self.assertTrue(Q("0.2332417549") < low <= high < Q("0.2332417552"))
        self.assertEqual(high-low, Q(1, 10**10))
        self.assertEqual((low, high), joint_upper_density(13, b, 5, a, Q(1, 10**10)))
        # An independent count at all cutoffs through 5000 includes unfinished scales.
        width = {5: 1, 13: 1}
        bad = 0
        for n in range(5000):
            for p in width:
                if n >= p*width[p]:
                    width[p] *= p
            bad += 2*width[5] <= n < 4*width[5] and 10*width[13] <= n
            self.assertLessEqual(Q(bad, n+1), high)
        for p in (5, 13):
            self.assertEqual(failed_intervals(p, certificate(2, support, p, 2)), [])

    def test_phase_boxes(self):
        first = [(Q(2), Q(4))]
        second = [(Q(10), Q(13))]
        tests = [(5, first), (13, second)]
        coarse = joint_box_bound(tests, Q(1, 1000), 4)
        fine = joint_box_bound(tests, Q(1, 1000), 8)
        self.assertLessEqual(fine, coarse)
        self.assertGreaterEqual(fine, joint_upper_density(5, first, 13, second, Q(1, 1000))[0])
        self.assertEqual(joint_box_bound(tests + [(7, [])], Q(1, 1000), 4), 0)
        # All phases fail in these synthetic patterns.
        self.assertEqual(joint_upper_density(3, [(Q(1), Q(3))], 5, [(Q(1), Q(5))], Q(1, 1000)),
                         (Q(999, 1000), 1))

    def test_kernel_and_crt(self):
        coeff = coefficients(4)
        prefixes = [Q(0)]
        for k in range(1, 80):
            prefixes.append(2*prefixes[-1]+Q(1, k))
        digits = int(log_bits(100), 2)
        for n in (0, 1, 12, 64):
            low, high = enclosure(n, coeff, 17**4, prefixes)
            self.assertLessEqual(low, Q(digits, 2**(100-n)))
            self.assertLessEqual(Q(digits+1, 2**(100-n)), high)
        low, high = enclosure(12, coeff, 17**4, prefixes)
        y = (low+high)/2
        step = sum(Q(c, 13+i) for i, c in enumerate(coeff))/17**4
        h, model, error = constrained_integer_model(y, step, 35, low, high)
        self.assertEqual((h, model.denominator), (-9, 138879052884))
        self.assertEqual(gcd(35, model.denominator), 1)
        self.assertLess(2**13*error, Q(1, 32))
        self.assertIsNone(constrained_integer_model(Q(1, 6), Q(1, 3), 2, Q(0), Q(1)))
        for other in (h-35, h+35):
            self.assertLessEqual(error, max(abs(y+other*step-low), abs(y+other*step-high)))

    def test_block_discrepancy_and_coverage(self):
        self.assertEqual(block_discrepancy(1, 3, 2), Q(2, 3))
        self.assertEqual(block_discrepancy(0, 3, 10), 1)
        rows = scan(1024, 12, 4, [(3,), (5,), (13,), (3, 5, 13)])
        self.assertEqual([row[:4] for row in rows], [(7, 18, 18, 12), (0, 0, 0, 12), (2, 13, 13, 24), (11, 55, 24, 48)])
        self.assertLessEqual(rows[-1][4], 1-Q(48, 1024)*Q(2, 3))
        self.assertEqual(endpoint_bound(10, [(0, 8, 0), (2, 8, 0), (2, 10, 0)]), 0)

    def test_golden_residue_witnesses(self):
        states = quadratic_residue_witnesses(2668, 101, 4)
        pairs = [pair for residues in states.values() for pair in residues.values()]
        self.assertEqual(len(pairs), 1189)
        self.assertTrue(all(None not in pair for pair in pairs))
        self.assertEqual(max(max(pair) for pair in pairs), 2667)
        for modulus, residues in states.items():
            for residue, pair in residues.items():
                self.assertTrue(all(pow(2, n, modulus) == residue for n in pair))


if __name__ == "__main__":
    unittest.main()
