"""Certify changes in every overlapping word via two CRT factors of a diagonal ln(2) numerator."""
from fractions import Fraction
from itertools import accumulate
from math import comb, isqrt, lcm, prod

from discrepancy_experiments import corrected_model, log_bits
from localized_certificate import prime
from strided_logarithm import residue_of_rational


def diagonal_residue(n, modulus):
    """Least numerator of the diagonal model at the common denominator L_(2n)."""
    value = 0
    for j in range(1, n + 1):
        value = (2 * value + modulus // j) % modulus
    correction = modulus // (n + 1)
    for j in range(n):
        value += correction
        if j + 1 < n:
            correction, remainder = divmod(-correction * (j + 1), n + j + 2)
            assert remainder == 0
    return value % modulus


def certified_positions(n):
    """Offset j is marked when the two four-bit cell indices force a transition."""
    modulus = lcm(*range(1, 2 * n + 1))
    upper = prod(p for p in range(n + 1, 2 * n + 1) if prime(p))
    lower = modulus // upper
    value = diagonal_residue(n, modulus)
    a = value * pow(lower, -1, upper) % upper
    b = value * pow(upper, -1, lower) % lower
    assert (a * lower + b * upper) % modulus == value
    if n <= 256:
        assert corrected_model(n, n) * modulus % modulus == value

    # At the last possible internal gap the unwrapped error is still < 1/16.
    assert 16 * 2**(2 * n - 3) < (2 * n + 1) * comb(2 * n, n)
    marks = []
    for _ in range(2 * n - 2):
        i, k = 16 * a // upper, 16 * b // lower
        marks.append(5 <= (i + k) % 16 <= 9)
        a = 2 * a % upper
        b = 2 * b % lower
    return marks


def window_counts(indicators, n, width):
    """All n starts, with the last bit of each word used only as a right neighbor."""
    prefix = list(accumulate(indicators, initial=0))
    return [prefix[i + width - 1] - prefix[i] for i in range(n)]


def shell(n):
    marks = certified_positions(n)
    # Independent rational enclosure of the true bits, including the last right neighbor.
    digits = log_bits(3 * n - 1)[n:]
    hits = [a != b for a, b in zip(digits, digits[1:])]
    assert len(marks) == len(hits) and all(not m or h for m, h in zip(marks, hits))
    for width in (isqrt(n), n):
        forced = window_counts(marks, n, width)
        actual = window_counts(hits, n, width)
        yield (n, width, sum(marks[:n]), min(forced), sum(4 * v >= width for v in forced),
               min(actual), sum(4 * v >= width for v in actual))


def zero_completion(n, width):
    """Preserve all first upper-band digits and displacements while zeroing the shell words."""
    grid = lcm(*range(1, n + 1))
    while grid % 2 == 0:
        grid //= 2
    assert 1 << (n + width - 1) <= grid
    precision = grid.bit_length() + 16
    while True:
        bits = int(log_bits(n + precision)[n:], 2)
        multiple = grid * bits >> precision
        if (grid * (bits + 1) - 1) >> precision == multiple:
            break
        precision += 16
    # The translated phase lies in [0,1/grid); the first n bits are preserved.
    translation = Fraction(-multiple, grid)
    assert 0 <= grid * bits - (multiple << precision)
    assert grid * (bits + 1) - (multiple << precision) <= 1 << precision
    comparisons = 0
    for u in range(n, 2 * n):
        value = corrected_model(u, u)
        translated = value + 2**(u - n) * translation
        assert lcm(*range(1, 2 * u + 1)) % translated.denominator == 0
        if u > n:
            assert translated - 2 * previous_translated == value - 2 * previous
        previous_translated, previous = translated, value
        for p in range(u + 1, 2 * u + 1):
            if prime(p):
                assert residue_of_rational(p * translated, p) == residue_of_rational(p * value, p)
                comparisons += 1
    return grid.bit_length() - 1, comparisons


if __name__ == "__main__":
    zero_bits, comparisons = zero_completion(64, 8)
    print(f"Countermodel at 64: {zero_bits} zero bits, {comparisons} matching upper-band values.")
    print("N T marked_shell least_certified certified_rich least_actual actual_rich")
    for k in range(8, 15):
        for row in shell(2**k):
            print(*row)
