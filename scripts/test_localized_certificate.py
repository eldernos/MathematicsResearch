"""Compare certificate cells with exact rational prefixes, including cell boundaries."""

import unittest
from bisect import bisect_right
from fractions import Fraction

from localized_certificate import certificate


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

    def test_against_unshifted_rational_prefix(self):
        # Scales start once all contributing inverse-base powers have stabilized.
        for base, p, support in [(10, 3, {2, 3, 5}), (3, 2, {2, 3, 5}), (2, 5, {2, 5, 7})]:
            for precision in (1, 2):
                for order in (1, 2, 3):
                    with self.subTest(base=base, p=p, precision=precision, order=order):
                        cells = certificate(base, support, p, precision, order)
                        starts = [left for left, _ in cells]
                        modulus = p**precision
                        k = 2 * (precision - 1) + 1
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


if __name__ == '__main__':
    unittest.main()
