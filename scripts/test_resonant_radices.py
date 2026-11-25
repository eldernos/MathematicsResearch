"""Exact finite checks of the varying-radix X² − 2X theorem. Run with unittest."""

from fractions import Fraction
from functools import cache
from itertools import product
from math import factorial
import unittest


def v2(n):
    """Exponent of 2 in a nonzero integer of either sign."""
    if n == 0:
        raise ValueError("Use a precision cap at zero")
    return (n & -n).bit_length() - 1


def integral_mod(q, precision):
    modulus = 1 << precision
    return q.numerator * pow(q.denominator, -1, modulus) % modulus


@cache
def coefficient(m):
    return Fraction(1 << m, ((1 << m) - 1) * factorial(m + 1))


def normalized(b):
    return b if b % 4 == 1 else -b


def log_inverse(b, precision):
    """-log(1+z) mod 2^precision. Terms m >= precision have valuation >= m."""
    z = normalized(b) - 1
    return integral_mod(sum((Fraction((-z)**m, m) for m in range(1, precision)),
                            Fraction()), precision)


def dyadic_slope(b, precision):
    """Delta at j=precision. Division by 2^j uses j extra bits."""
    exponent = 1 << precision
    modulus = 1 << (2 * precision)
    return (pow(b, -exponent, modulus) - 1) // exponent


def shifted_phase(x, precision):
    """F(x) mod 2^precision. Integrality and 4 | x bound the omitted degrees."""
    modulus = 1 << precision
    return sum(integral_mod(coefficient(m), precision) * pow(x, m, modulus)
               for m in range(1, (precision + 1) // 2)) % modulus


def upper_den_exponent(b, k):
    """Evaluate the polynomial numerator over 2^(2k) modulo that denominator."""
    modulus = 1 << (2 * k)
    corner = pow(b, -1, modulus)
    axis = 0
    for _ in range(k):
        corner = corner**2 % modulus
        axis = (2 * axis + corner) % modulus
    numerator = (axis**2 - corner**2 - (2 << k) * axis) % modulus
    return 2 * k - v2(numerator) if numerator else 0


def direct_prefix(b, n, k):
    """Unsimplified truncated square and linear terms, including every shift."""
    indices = range(1, k + 1)
    square = sum(Fraction(b**(n - (1 << i) - (1 << j)), 1 << (i + j))
                 for i, j in product(indices, repeat=2) if (1 << i) + (1 << j) <= n)
    linear = sum(Fraction(b**(n - (1 << i)), 1 << i) for i in indices)
    return square - 2 * linear


class ResonantRadices(unittest.TestCase):
    def test_legendre(self):
        self.assertEqual(coefficient(1), 1)
        for m in range(1, 513):
            a = coefficient(m)
            self.assertEqual(v2(a.numerator) - v2(a.denominator), (m + 1).bit_count() - 1)

    def test_log_and_finite_isometries(self):
        for p in range(2, 13):
            modulus = 1 << p
            images = {}
            for b in range(1, modulus, 4):
                x = log_inverse(b, p)
                self.assertEqual(dyadic_slope(b, p), x)
                f = shifted_phase(x, p)
                images[b] = f
                self.assertEqual(log_inverse(-b, p), x)
            self.assertEqual(sorted(images.values()), list(range(0, modulus, 4)))
            # A finite isometry is exactly a permutation at every quotient level
            # compatible with reduction. Check every lift to the next level.
            if p > 2:
                for b, f in images.items():
                    self.assertEqual(f % (modulus // 2), previous[b % (modulus // 2)])
            previous = images

    def test_direct_upper_prefix(self):
        for b in range(3, 32, 2):
            for k in range(1, 7):
                expected = 1 << upper_den_exponent(b, k)
                for n in range(3 << (k - 1), 1 << (k + 1)):
                    self.assertEqual(direct_prefix(b, n, k).denominator, expected)

    def test_worked_example_and_boundary(self):
        good = [b for b in range(3, 256, 2)
                if v2(b*b - 1) - 1 == 2 and upper_den_exponent(b, 11) == 0]
        self.assertEqual(good, [93, 163])
        for b in range(3, 512, 2):
            s = v2(b*b - 1) - 1
            for k in range(1, 19):
                for h in range(k + 1):
                    t = k - 1 - s - h
                    if t <= s:
                        self.assertEqual(upper_den_exponent(b, k) <= h, v2(k + 1) >= t)

    def test_resonant_classes(self):
        # Test every representable stratum in the quotient, including both signs.
        for t in range(3, 11):
            modulus = 1 << t
            for s in range(2, t):
                radices = [b for b in range(3, modulus + 2, 2)
                           if v2(b*b - 1) - 1 == s]
                phases = {b: shifted_phase(log_inverse(b, t), t) for b in radices}
                # At least two full admissibility periods at small s, plus an
                # admissible large k for every s. All H here are nonnegative.
                first = t + s + 1
                ks = set(range(first, first + (modulus if t <= 7 else 33)))
                eligible = (1 << s) - 1
                while eligible < first:
                    eligible += 1 << (s + 1)
                ks.add(eligible)
                for k in sorted(ks):
                    h = k - first
                    analytic = {b % modulus for b in radices if (phases[b] - k - 1) % modulus == 0}
                    direct = {b % modulus for b in radices if upper_den_exponent(b, k) <= h}
                    self.assertEqual(direct, analytic, (t, s, k))
                    if v2(k + 1) == s:
                        self.assertEqual(len(analytic), 2, (t, s, k))
                        u, v = sorted(analytic)
                        self.assertEqual(u + v, modulus)
                    else:
                        self.assertFalse(analytic, (t, s, k))


if __name__ == "__main__":
    unittest.main()
