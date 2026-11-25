"""Exact controls for the finite translation geometry and Taylor-period obstruction."""
import unittest
from fractions import Fraction
from itertools import combinations, product
from math import gcd, lcm

from test_phase18_summation import is_prime, point_discrepancy, power_order


def orbit(b, x, n):
    return [b**j*x % 1 for j in range(n)]


def star_discrepancy(points):
    ordered = sorted(points)
    n = len(points)
    return max(max(Fraction(i+1, n)-u, u-Fraction(i, n)) for i, u in enumerate(ordered))


def deficit(b, x, n):
    return 1 - point_discrepancy(orbit(b, x, n))


class GeometryTests(unittest.TestCase):
    def test_quotient_and_triangle(self):
        for b, n in product((2, 3, 4), (2, 4, 7)):
            for x, y in product([Fraction(i, 12) for i in range(12)], repeat=2):
                dist = deficit(b, x-y, n)
                self.assertEqual(dist == 0, ((b-1)*(x-y)).denominator == 1)
                self.assertEqual(dist, deficit(b, y-x, n))
                self.assertLessEqual(dist, deficit(b, x, n)+deficit(b, y, n))
            u = Fraction(1, n*b**(n+1))
            self.assertEqual(deficit(b, u, n), (b**(n-1)-1)*u)

    def test_multipliers(self):
        for m in range(1, 10):
            b = m+1
            x = Fraction(1, m*m)
            self.assertEqual(point_discrepancy(orbit(b, x, 2*m)), Fraction(1, m))
            self.assertEqual(point_discrepancy(orbit(b, m*x, 2*m)), 1)
        for b, m, n in product((2, 3, 5), range(1, 6), (2, 9)):
            for i in range(17):
                x = Fraction(i, 17)
                d = point_discrepancy(orbit(b, x, n))
                md = point_discrepancy(orbit(b, m*x, n))
                self.assertLessEqual(md, m*d)
                self.assertGreaterEqual(md, 1-m*(1-d))

    def test_star_and_product(self):
        x, z = Fraction(1, 4), Fraction(-1, 256)
        self.assertEqual(star_discrepancy(orbit(2, x, 3)), Fraction(1, 2))
        self.assertEqual(star_discrepancy(orbit(2, z, 3)), 1-Fraction(1, 64))
        self.assertEqual(star_discrepancy(orbit(2, x+z, 3)), Fraction(1, 3)-Fraction(1, 64))
        # All rectangular atom-inclusion patterns from both sides of each atom.
        atoms = [Fraction(1, 3), Fraction(2, 3)]
        ends = [Fraction(0), *atoms, Fraction(1)]
        intervals = [(v-u, {x for x in atoms if (x > u or (left and x == u))
                             and (x < v or (right and x == v))})
                     for u, v in combinations(ends, 2) for left, right in product((False, True), repeat=2)]
        intervals += [(Fraction(0), {x}) for x in atoms]
        box = max(abs(Fraction(len(a & b), 2)-u*v) for u, a in intervals for v, b in intervals)
        self.assertEqual(box, Fraction(8, 9))

    def test_sparse_additive_complements(self):
        A = {0}
        for j in range(5):
            A |= {x+4**j for x in A}
        B = {2*x for x in A}
        self.assertEqual(sorted(a+c for a in A for c in B), list(range(4**5)))
        for b, r in product((2, 3, 5), (2, 3, 4)):
            self.assertEqual(power_order(b, b**r-1), r)

    def test_taylor_common_orders(self):
        # The elementary divisor count behind the asymptotic proof, with
        # the prime support checked in the actual reduced rational prefix.
        for base in (2, 3, 5):
            prefix = Fraction()
            for n in range(1, 201):
                prefix = base*prefix + Fraction(1, n)
                if n not in (20, 40, 80, 160, 200):
                    continue
                band = [p for p in range(n//2+1, n+1) if is_prime(p) and gcd(base, p)==1]
                self.assertTrue(all(prefix.denominator % p == 0 for p in band))
                for omit in [None, *band]:
                    included = [p for p in band if p != omit]
                    local_orders = {p: power_order(base, p) for p in included}
                    R = lcm(*local_orders.values())
                    for d in set(local_orders.values()):
                        same = [p for p in included if local_orders[p] == d]
                        self.assertEqual(R % d, 0)
                        self.assertLessEqual(len(same), n//d)
                        product_of_primes = 1
                        for p in same:
                            product_of_primes *= p
                        self.assertEqual((base**d - 1) % product_of_primes, 0)


if __name__ == "__main__":
    unittest.main()
