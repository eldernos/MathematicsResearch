"""Compare certificate cells with exact rational prefixes, including cell boundaries."""

import unittest
from bisect import bisect_right
from fractions import Fraction
from math import comb

from discrepancy_experiments import binomial_survivors, corrected_model, log_bits, model_shell, periodic_phases, quadratic_statistics, shell_statistics
from localized_certificate import prime, certificate, discrepancy_bound


def supported(m, primes):
    for p in primes:
        while m % p == 0:
            m //= p
    return m == 1


class CertificateTests(unittest.TestCase):
    def test_mod_nine_table(self):
        cells = certificate(10, {2, 3, 5}, 3, 2)
        self.assertEqual(cells, [(1, 1), (Fraction(4, 3), 4), (Fraction(5, 3), 1),
                                 (2, 6), (Fraction(8, 3), 3)])

    def test_worst_prefix_and_refinement(self):
        results = [(Fraction(5, 12), 3), (Fraction(1, 4), 3), (0, 1)]
        previous = None
        for precision, expected in enumerate(results, 1):
            cells = certificate(7, {2, 3, 5}, 5, precision)
            self.assertEqual(discrepancy_bound(5, cells), expected)
            if previous is not None:
                starts = [left for left, _ in previous]
                for left, residue in cells:
                    parent = bisect_right(starts, left) - 1
                    self.assertEqual(residue % 5**(precision - 1), previous[parent][1])
            previous = cells
        # The sole failing cell is [2,3). Charging only complete scales would give 1/4.
        self.assertEqual([left for left, z in certificate(7, {2, 3, 5}, 5, 1) if not z], [2])

    def test_discrepancy_extremes(self):
        self.assertEqual(discrepancy_bound(3, [(Fraction(1), 0)]), (1, 1))
        self.assertEqual(discrepancy_bound(3, [(Fraction(1), 1)]), (0, 1))
        for order in (1, 2, 4):
            self.assertEqual(discrepancy_bound(2, certificate(15, {2, 3, 5, 7}, 2, 1, order)), (0, 1))

    def test_against_unshifted_rational_prefix(self):
        # Scales start once all contributing inverse-base powers have stabilized.
        for base, p, support in [(10, 3, {2, 3, 5}), (3, 2, {2, 3, 5}), (2, 5, {2, 5, 7})]:
            for precision in (1, 2):
                for order in (1, 2, 3):
                    with self.subTest(base=base, p=p, precision=precision, order=order):
                        cells = certificate(base, support, p, precision, order)
                        starts = [left for left, _ in cells]
                        modulus = p**precision
                        for k in {precision - 1, 2 * (precision - 1) + 1}:
                            scale = p**k
                            partial = Fraction(0)
                            for n in range(1, p * scale):
                                if supported(n, support):
                                    partial += Fraction(1, n**order * base**n)
                                if n >= scale:
                                    normalized = scale**order * partial
                                    actual = normalized.numerator * pow(normalized.denominator, -1, modulus)
                                    cell = bisect_right(starts, Fraction(n, scale)) - 1
                                    self.assertEqual(actual % modulus, cells[cell][1], n)

    def test_reported_certificate_bounds(self):
        for base, support, p, bounds in [
            (2, {2, 5}, 5, ['5/8', '0', '0', '0']),
            (10, {2, 5, 7}, 7, ['7/12', '7/30', '0', '0']),
            (2, {2, 5, 7}, 5, ['5/8', '1/4', '0', '0']),
            (210, {2, 3, 5, 7, 11}, 11, ['13/40', '17/420', '11/1890', '0']),
        ]:
            with self.subTest(base=base, support=support):
                actual = [discrepancy_bound(p, certificate(base, support, p, level))[0]
                          for level in range(1, 5)]
                self.assertEqual(actual, list(map(Fraction, bounds)))

    def test_corrected_denominators(self):
        for n in range(1, 52):
            for r in (0, n//3, n//2, n-1):
                den = corrected_model(n, r).denominator
                for p in range((n+r)//2+1, n+1):
                    if p != 2 and prime(p):
                        self.assertEqual(den % p, 0, (n, r, p))
            den = corrected_model(n, n).denominator
            for p, residue in binomial_survivors(n).items():
                self.assertEqual(den % p == 0, residue != 0, (n, p))
        self.assertEqual(binomial_survivors(100)[101], 0)

    def test_diagonal_step_and_actual_model_orbit(self):
        for n in range(25):
            step = corrected_model(n+1, n+1) - 2*corrected_model(n, n)
            self.assertEqual(step, Fraction(3*(-1)**n, 2*(2*n+1)*comb(2*n, n)))
        self.assertEqual(model_shell(256), (716, 141))

    def test_periodic_phases(self):
        weights = list(map(Fraction, ['-1/2', '1', '3/2', '-3']))
        self.assertEqual(periodic_phases(2, 3, weights), ([1, 3], [-8, 0]))
        # Period six has a transient because the radix of the power schedule divides six.
        self.assertEqual(periodic_phases(2, 3, [1]*6), ([3], [2]))
        self.assertEqual(periodic_phases(10, 3, [0]), ([0], [0]))

    def test_quadratic_statistics(self):
        # First four binary fractional digits are 1001, 0110 and 0111, respectively.
        self.assertEqual(quadratic_statistics(3, 3), ({'phi': 2, 'sqrt(2)': 2, '1/sqrt(5)': 1}, 3))

    def test_certified_logarithm_bits(self):
        self.assertEqual(int(log_bits(64), 2), 0xb17217f7d1cf79ab)
        self.assertEqual(shell_statistics(256), (Fraction(141, 256), Fraction(1413, 256)))


if __name__ == '__main__':
    unittest.main()
