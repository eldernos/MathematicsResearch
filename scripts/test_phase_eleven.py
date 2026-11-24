import unittest
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations

from corrected_strides import cost_certificate, validate, word_test
from localized_certificate import certificate


class PhaseElevenArithmeticTests(unittest.TestCase):
    def test_corrected_numerators(self):
        validate()

    def test_linear_coverage_costs(self):
        for h, r, s, limit in (
            (Q(1, 2), '0.08857', '0.07169', '0.746090'),
            (Q(1), '0.22365', '0.16931', '1.095663'),
            (Q(2), '0.58202', '0.40077', '1.962602'),
            (Q(1, 2), '0.09', '0.073', '0.751'),
            (Q(1), '0.225', '0.17', '1.099'),
            (Q(2), '0.585', '0.402', '1.969'),
        ):
            self.assertLess(cost_certificate(h, Q(r), Q(s)), Q(limit))

    def test_corrected_window_sieve(self):
        for n, t, k, cut, expected in (
            (128, 40, 2, 4, (7, 7, 11, 0)),
            (256, 48, 2, 5, (8, 7, 21, 0)),
            (512, 64, 3, 5, (9, 8, 23, 0)),
            (1024, 80, 3, 7, (10, 9, 33, 0)),
        ):
            self.assertEqual(word_test(n, t, k, cut), expected)

    def test_fixed_support_depth_search(self):
        counts = Counter()
        for p in (3, 5, 7):
            pool = [q for q in (2, 3, 5, 7, 11, 13, 17, 19) if q != p]
            for size in range(1, 4):
                for rest in combinations(pool, size):
                    for unit in range(1, p):
                        for level in range(1, 9):
                            cells = certificate(p+unit, (p, *rest), p, level)
                            if all(residue for _, residue in cells):
                                counts[level] += 1
                                break
                        else:
                            self.fail((p, unit, rest))
        self.assertEqual([counts[i] for i in range(1, 9)], [589, 85, 50, 22, 5, 2, 2, 1])
