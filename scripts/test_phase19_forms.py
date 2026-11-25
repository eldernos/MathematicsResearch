"""Finite controls for projected digit flows and algebraic p-adic directions."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd
import unittest

from phase19_horizontal import spectrum
from test_phase18_summation import point_discrepancy, power_order


def radix_integer(digits, b):
    value = 0
    for digit in digits:
        value = value*b + digit
    return value


def projected_discrepancies(samples, rows):
    return [point_discrepancy([sum(h*x for h, x in zip(row, v)) % 1 for v in samples])
            for row in rows]


class FormTests(unittest.TestCase):
    def test_exact_periodic_paths_and_flow_approximation(self):
        alphabet = list(product((0, 1), repeat=2))
        rows = [(1, 0), (0, 1), (1, 1), (1, -1), (2, -3)]
        for word in product(alphabet, repeat=3):
            exact_points = []
            for offset in range(3):
                cycle = word[offset:] + word[:offset]
                exact_points.append(tuple(Fraction(radix_integer(axis, 2), 7) % 1
                                          for axis in zip(*cycle)))
            exact = projected_discrepancies(exact_points, rows)
            for depth in (2, 4, 6):
                blocks = [tuple(word[(i+j) % 3] for j in range(depth)) for i in range(3)]
                self.assertEqual(Counter(block[:-1] for block in blocks),
                                 Counter(block[1:] for block in blocks))
                points = [tuple(Fraction(radix_integer(axis, 2), 2**depth)
                                for axis in zip(*block)) for block in blocks]
                coarse = projected_discrepancies(points, rows)
                for row, d, e in zip(rows, exact, coarse):
                    self.assertLessEqual(abs(d-e), Fraction(2*sum(map(abs, row)), 2**depth))

    def test_hensel_direction_and_grid_cancellation(self):
        for b, p, dimension in ((2, 3, 2), (3, 5, 3)):
            t = power_order(b, p)
            v, unit = 0, b**t - 1
            while unit % p == 0:
                v, unit = v+1, unit//p
            q, root = p, 0  # The chosen simple root modulo p.
            for _ in range(4):
                lifts = [root+j*q for j in range(p)
                         if ((root+j*q)**dimension + 2*(root+j*q) + 2*p) % (p*q) == 0]
                self.assertEqual(len(lifts), 1)
                root, q = lifts[0], q*p
                for row in product(range(-2, 3), repeat=dimension):
                    if not any(row):
                        continue
                    numerator = sum(h*root**j for j, h in enumerate(row))
                    reduced_q = q//gcd(q, numerator)
                    if reduced_q <= p**v:
                        continue
                    period = power_order(b, reduced_q)
                    a = numerator//gcd(q, numerator)
                    points = {a*pow(b, n, reduced_q) % reduced_q for n in range(period)}
                    self.assertEqual(points, {(x+reduced_q//p) % reduced_q for x in points})

    def test_horizontal_row_endpoints(self):
        self.assertEqual(spectrum(3), (Fraction(2,3), Fraction(2,3)))
        self.assertEqual(spectrum(5), (Fraction(1,5), Fraction(8,15)))


if __name__ == "__main__":
    unittest.main()
