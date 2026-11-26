"""Exact prime-residue checks and three adjacent partial-CRT certificates for ln(2)."""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
from math import ceil, floor, gcd, lcm

from corrected_strides import beta, model, orders, sieve_selected
from discrepancy_experiments import corrected_model, log_bits
from localized_certificate import prime
from strided_logarithm import residue_of_rational, shifted


def diagonal_checks():
    values = [corrected_model(n, n) for n in range(110)]
    for n in range(4, 90):
        step = values[n + 1] - 2 * values[n]
        increments = [(values[n + h] - 2**h * values[n]) / step for h in range(9)]
        for h, k in combinations(range(1, 9), 2):
            determinant = (2**k - 1) * increments[h] - (2**h - 1) * increments[k]
            assert determinant > 0
            for p in range(n + k + 1, 2*n + 1):
                if not prime(p):
                    continue
                x, y, z = [residue_of_rational(p * values[n + j], p) for j in (0, h, k)]
                observed = (2**k - 1) * (y - 2**h*x) - (2**h - 1) * (z - 2**k*x)
                assert (observed % p == 0) == (determinant.numerator % p == 0)
                if (h, k) == (1, 2):
                    assert (observed % p == 0) == ((5*n + 7) % p == 0)


def beta_model(m, r, s):
    value = shifted(6*m)
    for a, index, order, multiplier in ((4, 3*m, r, 2), (-8, 2*m, s, -1)):
        value += multiplier * sum(Q((-1)**j, (a-1)**(j+1)) * beta(index, j)
                                  for j in range(order))
    return value


def beta_step(m, r, s):
    positive = 16*beta(3*m, r) + 4*beta(3*m+1, r) + beta(3*m+2, r)
    alternating = 8*beta(2*m, s) - beta(2*m+1, s)
    return 2 * Q((-1)**r, 3**r) * positive + alternating / 9**s


def beta_checks():
    for r, s in ((0, 0), (2, 3), (4, 1), (3, 2), (6, 6)):
        values = [beta_model(m, r, s) for m in range(77)]
        for m, value in enumerate(values[:-1]):
            assert values[m+1] - 64*value == beta_step(m, r, s)
        for m in range(10, 70):
            for h, k in combinations(range(1, 6), 2):
                later = [values[m+i] - 64**i * values[m] for i in (h, k)]
                determinant = (64**k-1)*later[0] - (64**h-1)*later[1]
                if r % 2 == 0:
                    assert determinant > 0
                for p in range(2*(m+k)+s+1, 3*m+1):
                    if not prime(p) or 3*(m+k)+r >= 2*p:
                        continue
                    digits = []
                    for i in (0, h, k):
                        pole = 2*4**(3*(m+i)-p)
                        digit = residue_of_rational(values[m+i] - Q(pole, p), p)
                        assert residue_of_rational(p*values[m+i], p*p) == (pole+p*digit) % (p*p)
                        digits.append(digit)
                    x, y, z = digits
                    observed = (64**k-1)*(y-64**h*x) - (64**h-1)*(z-64**k*x)
                    assert observed % p == residue_of_rational(determinant, p)


def higher_digit_checks():
    """Exercise the third digit when the common denominator contains p squared."""
    for p in (29, 43):
        scale, modulus = p**2, p**3
        start = (scale+2)//3
        diagonal_start = (scale+1)//2
        r, s = 2, 1
        z = beta_model(start, r, s)
        y = corrected_model(diagonal_start, diagonal_start)
        delta = Q(3*(-1)**diagonal_start, 2) * beta(diagonal_start, diagonal_start)
        diagonal, signed = [], []
        for i in range(p):
            m, n = start+i, diagonal_start+i
            assert z.denominator % scale == 0
            signed.append(residue_of_rational(scale*z, modulus))
            diagonal.append(residue_of_rational(scale*y, modulus))
            z = 64*z + beta_step(m, r, s)
            y = 2*y + delta
            delta *= Q(-(n+1), 4*n+6)
        assert any(value % p for value in diagonal)
        assert y == corrected_model(diagonal_start+p, diagonal_start+p)
        assert z == beta_model(start+p, r, s)
        for h in range(1, 4):
            gaps = Counter((signed[i+h]-64**h*signed[i]) % modulus for i in range(p-h))
            assert max(gaps.values()) <= 2*(5*h+r+s)
        for h, k in combinations(range(1, 6), 2):
            triples = Counter((diagonal[i], diagonal[i+h], diagonal[i+k]) for i in range(p-k))
            assert max(triples.values()) <= 2*(k-1)


@dataclass(frozen=True)
class GridInterval:
    """All translates of a closed interval by integer multiples of 1 / size."""
    size: int
    low: Q
    high: Q


def intersect(first, second):
    h, k = first.size, second.size
    common = gcd(h, k)
    period = lcm(h, k)
    # The signed difference i/h - j/k is an integer multiple of 1/period.
    lower = ceil(period * (second.low - first.high))
    upper = floor(period * (second.high - first.low))
    assert period * ((first.high-first.low) + (second.high-second.low)) < 1
    assert lower == upper
    i = lower * pow(k//common, -1, h//common) % (h//common)
    j, remainder = divmod((k//common)*i - lower, h//common)
    assert remainder == 0
    low = max(first.low+Q(i, h), second.low+Q(j, k))
    high = min(first.high+Q(i, h), second.high+Q(j, k))
    assert low <= high
    return GridInterval(common, low, high)


def observation(start, advance, bits, omitted):
    data = model(start, *orders(start, bits + advance))
    selected = (p for p in range(2, len(data.weights)) if p not in omitted and prime(p))
    modulus, residue = sieve_selected(data, selected)
    size = data.common // modulus
    factor = 2**advance
    center = (factor * Q(residue, data.common)) % 1
    radius = factor * data.error
    return GridInterval(size//gcd(size, factor), center-radius, center+radius)


def changes(word, bits):
    return ((word ^ (word >> 1)) & ((1 << (bits-1))-1)).bit_count()


def overlap_certificate(n, bits):
    omissions = ({2, 3, 5, 7}, {2, 3, 5, 11}, {2, 3, 7, 11})
    grids = [observation(n-shift, shift, bits, omit)
             for shift, omit in zip((2, 1, 0), omissions)]
    result = intersect(intersect(grids[0], grids[1]), grids[2])
    reverse = intersect(grids[0], intersect(grids[1], grids[2]))
    g = result.size
    assert reverse.size == g and result.high-result.low == reverse.high-reverse.low
    assert (g*(result.low-reverse.low)).denominator == 1

    base = 1 << bits
    # No closed word cylinder can meet two different translated intervals.
    assert Q(1, g) - (result.high-result.low) > Q(1, base)
    low = ceil(g*base*result.low)-1
    high = floor(g*base*result.high)
    actual = int(log_bits(n+bits)[n:], 2)
    actual_admitted = False
    count, minimum = 0, bits
    for j in range(g):
        for u in range((low+j*base)//g, (high+j*base)//g + 1):
            word = u % base
            count += 1
            minimum = min(minimum, changes(word, bits))
            actual_admitted |= word == actual
    assert actual_admitted
    return g, count, minimum, changes(actual, bits)


if __name__ == "__main__":
    diagonal_checks()
    beta_checks()
    higher_digit_checks()
    print("All modular comparisons passed.")
    print("start bits joint_intervals admitted_words minimum_changes actual_changes")
    for n, bits in ((256, 64), (1024, 128), (4096, 256)):
        print(n, bits, *overlap_certificate(n, bits))
    print("shell bits blocks worst_block_minimum certified_changes actual_changes")
    for start, bits in ((256, 64), (512, 64), (1024, 128), (2048, 128)):
        rows = [overlap_certificate(n, bits) for n in range(start, 2*start, bits)]
        print(start, bits, len(rows), min(row[2] for row in rows),
              sum(row[2] for row in rows), sum(row[3] for row in rows))
