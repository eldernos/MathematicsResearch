import unittest
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations

from corrected_strides import adjacent_grid_example, cost_certificate, validate, word_test
from localized_certificate import certificate, prime
from stoneham_power_cells import first_passing, power_cells


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

    def test_adjacent_lifts(self):
        self.assertEqual(adjacent_grid_example(), (3888000, 3048192, 31104))

    def test_corrected_window_sieve(self):
        for n, t, k, cut, expected in (
            (128, 40, 2, 4, (7, 7, 11, 0)),
            (256, 48, 2, 5, (8, 7, 21, 0)),
            (512, 64, 3, 5, (9, 8, 23, 0)),
            (1024, 80, 3, 7, (10, 9, 33, 0)),
        ):
            self.assertEqual(word_test(n, t, k, cut), expected)

    def test_stoneham_power_precision(self):
        expected = [1, 4, 5, 9, 11, 14, 14, 18, 20]
        self.assertEqual([first_passing(3, d, 20)[0] for d in range(1, 10)], expected)
        for level in (2, 5, 8):
            cells = power_cells(2, 2, level)
            self.assertEqual([value for t, value in cells if t <= Q(3, 2)][-1], 0)

    def test_gaussian_shadows(self):
        # Check the combined p-residue against independently reduced finite fractions.
        weights = (1, 1, 1, 0, -1, -1, -1, 0)
        def partial(t, length):
            return sum((Q(weights[(j-1) % 8], j << (((2*t-1)*j+1)//2))
                        for j in range(1, length+1)), Q(0))
        def residue(x, p):
            return x.numerator*pow(x.denominator, -1, p) % p
        for n in range(4, 60):
            m, l = 2*n//3, 2*n//5
            for a, c in ((1, 1), (8, 4)):
                shifted = (1 << n)*(a*partial(2, m)+c*partial(3, l))
                for p in range(3, m+1, 2):
                    if prime(p) and p*p > m:
                        short = a*partial(2, m//p)+c*partial(3, l//p)
                        sign = (-1)**((p-1)//2)
                        self.assertEqual(residue(p*shifted, p),
                                         (sign*pow(2, n, p)*residue(short, p)) % p)

    def test_one_fixed_mask_at_thirty_levels(self):
        selected = [1, 2]
        start = Q(5, 2)
        partial = Q(3, 2)
        for i in range(1, 30):
            last = start*3**(i-1)
            candidates = []
            for first in (1, 5):
                while first <= last:
                    first *= 2
                candidates.append(first)
            possible = (subset for count in range(3)
                        for subset in combinations(candidates, count))
            for subset in possible:
                trial = partial+sum((Q(3**i, m) for m in subset), Q(0))
                if trial.numerator % 3**(i+1) == 0:
                    selected.extend(subset)
                    partial = trial
                    break
            else:
                self.fail((i, candidates))
            level = i+1
            # Direct row sum, independent of the grouped-tail congruence.
            rows = sum((Q(3**j, m) for j in range(level)
                        for m in selected if m <= start*3**j), Q(0))
            self.assertEqual(rows.numerator % 3**level, 0)

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
