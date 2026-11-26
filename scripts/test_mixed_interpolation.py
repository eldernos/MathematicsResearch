"""Exact finite checks for the nonrectangular mixed-prefix formula and its lifts."""

import unittest
from bisect import bisect_right
from collections import defaultdict
from fractions import Fraction


def powers(base, limit):
    values = []
    value = base
    while value <= limit:
        values.append(value)
        value *= base
    return values


def partial_sums(p, q, depth, last):
    """S_m modulo p^depth; all inverses here are inverses of units."""
    modulus = p**depth
    phi = (p - 1) * p ** (depth - 1)
    sums = [0]
    for j in range(1, last + 1):
        exponent = pow(q, j, phi)
        term = pow(q, -j, modulus) * pow(2, -exponent, modulus)
        sums.append((sums[-1] + term) % modulus)
    return sums


def shape_value(sums, p, m, a, b, modulus):
    """The positive endpoint numerator on a rectangle or two truncated arms."""
    if a == 0:
        assert b == 0
        return sums[m]
    assert 1 <= a <= m and b >= 1
    middle = sums[m - 1] - sums[m - a]
    last = sums[m] - sums[m - 1]
    return (sums[m - a] + p * middle + pow(p, b, modulus) * last) % modulus


def check_shape(n, ps, qs, p, q, actual):
    k, m = bisect_right(ps, n), bisect_right(qs, n)
    if not k or not m:
        return
    modulus = p**k
    a = m - bisect_right(qs, n - p**k)
    b = k - bisect_right(ps, n - q**m)
    sums = partial_sums(p, q, k, m)
    compressed = shape_value(sums, p, m, a, b, modulus)
    binary = pow(2, n, modulus)
    assert ((p - 1) * pow(2, p**k, modulus) * actual
            + binary * pow(q, m, modulus) * compressed) % modulus == 0


class MixedInterpolation(unittest.TestCase):
    def test_fractional_prefix(self):
        # This oracle advances the original rational, including simultaneous jumps.
        limit = 2400
        threes, fives = powers(3, limit), powers(5, limit)
        jumps = defaultdict(Fraction)
        for row in threes:
            for col in fives:
                jumps[row + col] += Fraction(1, row * col)
        frac = Fraction(0)
        for n in range(limit + 1):
            frac = (2 * frac + jumps.get(n, 0)) % 1
            k, l = bisect_right(threes, n), bisect_right(fives, n)
            integer = frac * 3**k * 5**l
            self.assertEqual(integer.denominator, 1)
            check_shape(n, threes, fives, 3, 5, integer.numerator)
            check_shape(n, fives, threes, 5, 3, integer.numerator)

    def test_large_boundary_prefixes(self):
        limit = 3**24
        threes, fives = powers(3, limit), powers(5, limit)
        events = {r + c for r in threes for c in fives}
        events.update(threes + fives)
        for n in sorted({e + d for e in events for d in (-1, 0, 1) if 0 <= e + d <= limit}):
            k, l = bisect_right(threes, n), bisect_right(fives, n)
            modulus = 3**k * 5**l
            actual = sum(
                pow(2, n - r - c, modulus) * (modulus // (r * c))
                for r in threes for c in fives if r + c <= n
            ) % modulus
            check_shape(n, threes, fives, 3, 5, actual)
            check_shape(n, fives, threes, 5, 3, actual)

    def test_digit_lifting(self):
        # Check all candidates in two complete periods, for each pair of deficits.
        for p, q, u in ((3, 5, 2), (5, 3, 4)):
            base_value = 6 if p == 3 else 15
            for h in range(1, 6):
                period = u * p ** (h - 1)
                start = 8 * u
                modulus = p**h
                sums = partial_sums(p, q, h + 1, start + 3 * period)
                for a, b in [(0, 0)] + [(a, b) for a in range(1, 7) for b in range(1, 7)]:
                    def value(m):
                        return shape_value(sums, p, m, a, b, p * modulus)
                    roots = []
                    for m in range(start, start + 2 * period):
                        if value(m) % modulus == 0:
                            roots.append(m)
                        self.assertEqual((value(m + period) - value(m)) % modulus, 0)
                        if (m - a) % u == 0:
                            self.assertEqual(
                                (value(m + period) - value(m)) % (p * modulus),
                                base_value * p ** (h - 1) % (p * modulus),
                            )
                    self.assertEqual(len(roots), 2)
                    self.assertEqual(roots[1] - roots[0], period)

    def test_deeper_one_corner(self):
        k, l = 49, 33
        p, q = 3**k, 5**l
        lower = max(p + q // 5, p // 3 + q)
        upper = p + q
        modulus = p * q
        for n in (lower, upper - 1):
            threes, fives = powers(3, n), powers(5, n)
            self.assertEqual((len(threes), len(fives)), (k, l))
            self.assertEqual((l - bisect_right(fives, n - p),
                              k - bisect_right(threes, n - q)), (1, 1))
            actual = sum(pow(2, n - r - c, modulus) * (modulus // (r * c))
                         for r in threes for c in fives if r + c <= n) % modulus
            self.assertEqual(Fraction(actual, modulus).denominator, 3**47 * 5**30)

    def test_one_corner_witness(self):
        # 3^5=243 and 5^3=125: first precision only, but the whole gap is exact.
        k, l = 5, 3
        p, q = 3**k, 5**l
        lower = max(p + q // 5, p // 3 + q)
        self.assertEqual((lower, p + q), (268, 368))
        for n in (lower - 1, lower, p + q - 1, p + q):
            threes, fives = powers(3, n), powers(5, n)
            a = l - bisect_right(fives, n - p)
            b = k - bisect_right(threes, n - q)
            self.assertEqual((a, b) == (1, 1), lower <= n < p + q)
        for prime, axis, m in ((3, 5, l), (5, 3, k)):
            sums = partial_sums(prime, axis, 1, m)
            self.assertEqual(shape_value(sums, prime, m, 1, 1, prime), 0)


if __name__ == "__main__":
    unittest.main()
