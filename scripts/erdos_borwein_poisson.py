#!/usr/bin/env python3
"""Enclose the limiting one-frequency under the marked Poisson hypothesis.

All stored probability masses are rounded down. Omitted outcomes and roundoff
are accounted for by the missing total mass. No sampling or floating point.
"""

from fractions import Fraction
from math import ceil, factorial, floor, isqrt


SCALE = 1 << 80
PRIME_LIMIT = 65536
MAX_MARK = 255
MAX_COLUMN = 383
DEPTH = 24


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def odd_mark_masses():
    """Lower bounds for the probabilities of the odd part of tau."""
    weights = {1: SCALE}
    for p in primes_through(PRIME_LIMIT):
        # Exponents zero and one both give odd part one.
        local = {1: SCALE * (p * p - 1) // (p * p)}
        exponent, denominator = 2, p**3
        while weight := SCALE * (p - 1) // denominator:
            factor = exponent + 1
            odd = factor // (factor & -factor)
            local[odd] = local.get(odd, 0) + weight
            exponent += 1
            denominator *= p
        products = {}
        for u, mass in weights.items():
            for odd, prob in local.items():
                value = u * odd
                if value <= MAX_MARK:
                    products[value] = products.get(value, 0) + mass * prob
        weights = {u: w // SCALE for u, w in products.items() if w >= SCALE}
    # All omitted primes have exponent at most one with probability >= 1-1/P.
    return {u: w * (PRIME_LIMIT - 1) // PRIME_LIMIT for u, w in weights.items()}


def poisson_column(marks):
    """The derivative of exp(sum_u nu(u) z**u - 1) gives a positive recurrence."""
    exp_lower = sum(Fraction((-1) ** k, factorial(k)) for k in range(32))
    column = [int(SCALE * exp_lower)]
    for n in range(1, MAX_COLUMN + 1):
        numerator = sum(u * w * column[n - u] for u, w in marks.items() if u <= n)
        column.append(numerator // (n * SCALE))
    return column


def head_parity(column):
    """Bound the parity of the first digit after carrying from DEPTH to one."""
    carry = [SCALE]
    for _ in range(DEPTH - 1):
        updated = [0] * ((len(carry) - 1 + MAX_COLUMN) // 2 + 1)
        for c, mass in enumerate(carry):
            for j, weight in enumerate(column):
                updated[(c + j) // 2] += mass * weight
        carry = [mass // SCALE for mass in updated]
    parity = [sum(column[::2]), sum(column[1::2])]
    even = sum(mass * parity[c % 2] for c, mass in enumerate(carry))
    odd = sum(mass * parity[1 - c % 2] for c, mass in enumerate(carry))
    return Fraction(even, SCALE**2), Fraction(odd, SCALE**2)


if __name__ == "__main__":
    even, odd = head_parity(poisson_column(odd_mark_masses()))
    # The independent remaining tail meets at most 2*ceil(tail) grid cells
    # next to cylinder endpoints in units of 2**(-DEPTH). See the paper proof.
    error = 7 * Fraction(3, 5) ** DEPTH
    denominator = 10**6
    lower = (odd - error) * denominator
    upper = (1 - even + error) * denominator
    print("conditional one-frequency in millionths (outward rounded)")
    print(floor(lower), ceil(upper))
