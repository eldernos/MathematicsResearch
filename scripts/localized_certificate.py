#!/usr/bin/env python3
"""Exact denominator-survival certificates for prime-restricted polylogarithms."""

import argparse
from fractions import Fraction
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def cofactors(primes, limit):
    """Enumerate smooth integers strictly below limit, including 1."""
    values = [1]
    for q in sorted(primes):
        extended = []
        for r in values:
            while r < limit:
                extended.append(r)
                r *= q
        values = extended
    return values


def certificate(base, support, p, precision, order=1):
    """Return (left endpoint, normalized residue) on each cell of [1,p)."""
    support = set(support)
    if base < 2 or precision < 1 or p not in support or not all(map(prime, support)):
        raise ValueError('require base ≥ 2, positive precision and a selected prime in a prime support')
    if order < 1:
        raise ValueError('polylogarithm order must be positive')
    if gcd(base, p) != 1:
        raise ValueError('the selected prime must be coprime to the base')
    modulus = p**precision
    lift = pow(pow(base, -1, modulus), p**(precision - 1), modulus)
    jumps = {Fraction(1): 0}
    layer = 1
    for _ in range((precision - 1) // order + 1):
        for r in cofactors(support - {p}, p * layer):
            start = max(Fraction(1), Fraction(r, layer))
            delta = pow(layer * pow(r, -1, modulus), order, modulus) * pow(lift, r, modulus)
            jumps[start] = (jumps.get(start, 0) + delta) % modulus
        layer *= p
    total = 0
    cells = []
    for start, change in sorted(jumps.items()):
        total = (total + change) % modulus
        cells.append((start, total))
    return cells


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('base', type=int)
    parser.add_argument('p', type=int)
    parser.add_argument('precision', type=int)
    parser.add_argument('support', type=int, nargs='+')
    parser.add_argument('--order', type=int, default=1, help='positive integer polylogarithm order (default 1)')
    args = parser.parse_args()
    try:
        cells = certificate(args.base, args.support, args.p, args.precision, args.order)
    except ValueError as error:
        parser.error(str(error))
    for start, residue in cells:
        print(f'{str(start):>12}  {residue}')
    print('denominator survival certified' if all(r for _, r in cells) else 'inconclusive')
