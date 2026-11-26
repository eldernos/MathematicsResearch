"""Exact finite checks for the ray partition, growing-prime grids and translations."""
from fractions import Fraction
from itertools import count, product
from math import gcd, isqrt, lcm, prod
import unittest


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def finite_rays(limit, modulus, residues):
    unused = {n for n in range(1, limit + 1) if n % modulus in residues}
    last_prime = 1
    while unused:
        start = min(unused)
        prime = next(n for n in count(max(last_prime, start, 2) + 1)
                     if is_prime(n) and (n - 1) % modulus == 0)
        last_prime = prime
        terms = []
        m = start
        while m <= limit:
            unused.remove(m)  # Also checks disjointness.
            terms.append(m)
            m *= prime
        yield start, prime, terms


def point_discrepancy(points):
    """Oscillation of the empirical CDF minus the identity, with both sides at ties."""
    points = sorted(x % 1 for x in points)
    size = len(points)
    return (max(Fraction(i + 1, size) - x for i, x in enumerate(points))
            - min(Fraction(i, size) - x for i, x in enumerate(points)))


def power_order(base, q):
    if q == 1:
        return 1
    assert gcd(base, q) == 1
    residue = base % q
    order = 1
    while residue != 1:
        residue = (residue * base) % q
        order += 1
    return order


class Phase18SummationTests(unittest.TestCase):
    def test_log_and_signed_bbp_prefixes(self):
        for modulus, weights, base in [(1, {0: 1}, 2), (8, {1: 4, 4: -2, 5: -1, 6: -1}, 16)]:
            cutoff = 200
            def term(m):
                residue = m % modulus
                return Fraction(weights[residue], m * base ** ((m - residue) // modulus))
            original = sum(term(m) for m in range(1, cutoff + 1) if m % modulus in weights)
            regrouped = sum(term(m) for _, _, terms in finite_rays(cutoff, modulus, weights)
                            for m in terms)
            self.assertEqual(regrouped, original)

    def test_full_orbit_fibres(self):
        for e, other in product(range(1, 5), (1, 5, 11, 25, 55, 85)):
            q = 3**e * other
            size = 3**(e - 1)
            step = power_order(2, other)
            step *= 2 // gcd(2, step)
            for a in (1, q - 1):
                fibre = {a * pow(2, step*j, q) % q for j in range(size)}
                self.assertEqual(fibre, set(range(a % (3*other), q, 3*other)))
                orbit = [Fraction(a * pow(2, j, q) % q, q) for j in range(power_order(2, q))]
                self.assertLessEqual(point_discrepancy(orbit), Fraction(1, size))

    def test_growing_support_denominator(self):
        # At n=2^(m^2), use modular powers instead of forming b^n.
        rows = []
        for m in range(1, 70):
            for p in range(3, m + 1, 2):
                if not is_prime(p) or (p != 3 and p % 3 != 2):
                    continue
                power = p
                while power < m:
                    power *= p
                if power == m:
                    rows.append((p, m))
            end = 1 << (m*m)
            prefix = sum(Fraction(pow(2, end - (1 << (u*u)), u), u) for _, u in rows)
            largest = {p: u for p, u in rows}
            self.assertEqual(Fraction(prefix).denominator, prod(largest.values()))

    def test_translation_with_boundary_crossings(self):
        for b, n, x, z in product((2, 3), (1, 3, 8, 16),
                                  (Fraction(0), Fraction(2, 9), Fraction(-3, 8)),
                                  (Fraction(1, 3), Fraction(-1, 32), Fraction(1, 81))):
            old = [x * b**i % 1 for i in range(n)]
            new = [(x+z) * b**i % 1 for i in range(n)]
            diff = abs(point_discrepancy(old) - point_discrepancy(new))
            displacement = [z * b**i % 1 for i in range(n)]
            self.assertLessEqual(diff, 1 - point_discrepancy(displacement))
            if x == 0:
                self.assertEqual(diff, 1 - point_discrepancy(displacement))
            distances = [min((u-v) % 1, (v-u) % 1) for u, v in zip(old, new)]
            for eps in {Fraction(0), *distances}:
                self.assertLessEqual(diff, Fraction(sum(d > eps for d in distances), n) + 2*eps)

    def test_positive_subset_delay(self):
        for p in (3, 5, 17, 61, 193, 449):
            for k in range(1, 7):
                if k >= p:
                    continue
                scale = 2**k * lcm(*range(1, k + 1))
                for mask in range(1, 2**k):
                    indices = [j for j in range(1, k + 1) if mask & (1 << (j-1))]
                    reduced = sum(Fraction(1, j * 2**j) for j in indices) * scale
                    actual = sum(Fraction(1, j * 2**(p*j)) for j in indices) * scale
                    self.assertEqual(reduced.denominator, 1)
                    self.assertTrue(0 < reduced < scale)
                    self.assertEqual(actual.numerator * pow(actual.denominator, -1, p) % p,
                                     reduced.numerator % p)
                    if p >= scale:
                        self.assertNotEqual(reduced.numerator % p, 0)

    def test_periodic_liouville_targets(self):
        for b, k in product((2, 3), (2, 3, 4)):
            words = list(product(range(b), repeat=k))
            for retired in range(k+1):
                blocks = ([(0,)*k] * (retired * len(words))) + words * (k-retired)
                for length in range(1, k+1):
                    counts = {cell: 0 for cell in product(range(b), repeat=length)}
                    for block in blocks:
                        for offset in range(k+1-length):
                            counts[block[offset:offset+length]] += 1
                    total = sum(counts.values())
                    for cell, observed in counts.items():
                        uniform = Fraction(k-retired, k*b**length)
                        atom = Fraction(retired, k) if not any(cell) else 0
                        self.assertEqual(Fraction(observed, total), uniform+atom)


if __name__ == "__main__":
    unittest.main()
