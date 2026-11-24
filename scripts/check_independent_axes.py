#!/usr/bin/env python3
"""Exact finite checks for the independent-axis residue and counting formulas."""

from bisect import bisect_right
from collections import defaultdict
from fractions import Fraction


def positive_powers(base, limit):
    value = base
    powers = []
    while value <= limit:
        powers.append(value)
        value *= base
    return powers


def check_prefixes(limit):
    threes = positive_powers(3, limit)
    fives = positive_powers(5, limit + 1)
    jumps = defaultdict(Fraction)
    for row in threes:
        for column in fives:
            if row + column <= limit:
                jumps[row + column] += Fraction(1, row * column)

    boundaries = {position + offset for position in jumps for offset in (-1, 0, 1)}
    prefix = Fraction(0)
    cost = 0
    both_lost = 0
    for n in range(limit + 1):
        prefix = (2 * prefix + jumps.get(n, 0)) % 1
        k = bisect_right(threes, n)
        l = bisect_right(fives, n)
        row, column = 3**k, 5**l
        scaled = prefix * (row * column)
        assert scaled.denominator == 1

        row_length = bisect_right(fives, n - row)
        column_length = bisect_right(threes, n - column)
        if k:
            ternary = pow(2, n - row, 3) * pow(5, l, 3) * (row_length % 2)
            assert scaled.numerator % 3 == ternary % 3
            assert (prefix.denominator % row == 0) == (row_length % 2 != 0)
        if l:
            quinary = pow(2, n - column, 5) * pow(3, k, 5)
            quinary *= (0, 4, 1, 2)[column_length % 4]
            assert scaled.numerator % 5 == quinary % 5
            assert (prefix.denominator % column == 0) == (column_length % 4 != 0)

        if n in boundaries:
            for prime, exponent in ((3, k), (5, l)):
                for depth in range(1, min(4, exponent) + 1):
                    modulus = prime**depth
                    residue = 0
                    for i, power3 in enumerate(threes[:k], 1):
                        for j, power5 in enumerate(fives[:l], 1):
                            layer = k - i if prime == 3 else l - j
                            location = power3 + power5
                            if layer < depth and location <= n:
                                residue += pow(2, n - location, modulus) * (row // power3) * (column // power5)
                    assert residue % modulus == scaled.numerator % modulus

        # The count through position n is the prefix of length n+1.
        cost += column_length % 4 == 0
        log_next = bisect_right(fives, n + 1)
        assert 40 * cost <= 27 * (n + 1) + 39 * log_next + 52
        both_lost += bool(k and l and not row_length % 2 and not column_length % 4)
    return both_lost


def valuation(value, prime):
    exponent = 0
    while value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def check_cross_sums(prime, axis, period, limit, precision):
    modulus = prime**precision
    totient = (prime - 1) * prime ** (precision - 1)
    total = 0
    for j in range(1, limit + 1):
        exponent = pow(axis, j, totient)
        total += pow(axis, -j, modulus) * pow(2, -exponent, modulus)
        total %= modulus
        expected = 0 if j % period else 1 + valuation(j // period, prime)
        observed = valuation(total, prime) if total else precision
        assert observed == min(expected, precision), (prime, j, total, expected)


if __name__ == "__main__":
    cutoff = 100_000
    failed_both = check_prefixes(cutoff)
    for prime, axis, period in ((3, 5, 2), (5, 3, 4)):
        check_cross_sums(prime, axis, period, limit=10_000, precision=9)
    print(f"Checked positions 0 through {cutoff:,}. Both top powers were lost at {failed_both:,}.")
    print("Checked 10,000 cross-sum lengths for each prime to precision 9.")
