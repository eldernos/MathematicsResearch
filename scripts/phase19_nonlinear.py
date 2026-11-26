"""Exact checks of the grid-jump, derivative and freezing identities in Track D/F."""

from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction
from itertools import accumulate, product
from math import comb, gcd


def shell_jumps(p, s, d, depth, right_order=None):
    """Return integer weights on the u-grid scaled by p**(d*depth)."""
    if right_order is None:
        right_order = s
    scale = p**depth
    rows = []
    for loss in range(depth + 1):
        denominator = p**loss
        rows.append([
            (a * (scale // denominator), a == denominator)
            for a in range(1, p * denominator) if gcd(a, p) == 1
        ])
    all_jumps = Counter()
    competitors = set()
    for h in range(depth + 1):
        for k in range(depth - h + 1):
            weight = p**(s * h + right_order * k)
            for (z, z_is_one), (y, y_is_one) in product(rows[h], rows[k]):
                location = z**d + y**d
                if location < (p * scale)**d:
                    all_jumps[location] += weight
                    if not (z_is_one or y_is_one):
                        competitors.add(location)
    return all_jumps, sorted(competitors)


def prefix_evaluator(jumps):
    locations = sorted(jumps)
    sums = [0, *accumulate(jumps[location] for location in locations)]
    return lambda bound: sums[bisect_right(locations, bound)]


def isolated_centers(p, d, depth, competitors):
    scale = p**depth
    width_denominator = 8 * depth
    for c in range((scale + 1) // 2, 3 * scale // 2 + 1):
        if c % p == 0:
            continue
        # x = (c +/- 1/(8H))/p**H, with u mapped to the scaled integer grid.
        left, right = (
            scale**d + Fraction((width_denominator * c + sign)**d, width_denominator**d)
            for sign in (-1, 1)
        )
        if bisect_right(competitors, right) != bisect_left(competitors, left):
            continue
        yield left, scale**d + c**d, right


def check_isolated_centers(p, s, d, depth):
    jumps, competitors = shell_jumps(p, s, d, depth)
    mass = prefix_evaluator(jumps)
    good = 0
    for left, center, right in isolated_centers(p, d, depth, competitors):
        jump = 2 * p**(s * depth)
        assert jumps[center] == jump
        assert mass(right) - mass(left) == jump
        assert mass(center) == mass(right)
        assert jump % p**(s * depth + 1) != 0
        good += 1
    assert good > 0


def check_tied_weights():
    # All three terms of 3*X_1*X_3 - X_2**2 + X_4 have nominal weight four.
    p, d, depth = 3, 3, 4
    scale = p**depth
    cross, competitors = shell_jumps(p, 1, d, depth, right_order=3)
    square, _ = shell_jumps(p, 2, d, depth)
    combined = Counter({x: p * weight for x, weight in cross.items()})
    combined.subtract(square)
    excluded = set(competitors)
    for loss in range((depth + 1) // 4 + 1):
        for a in range(1, p**(loss + 1)):
            if a % p:
                location = (a * (scale // p**loss))**d
                combined[location] += p**(4 * loss)
                excluded.add(location)
    mass = prefix_evaluator(combined)
    good = 0
    for left, _, right in isolated_centers(p, d, depth, sorted(excluded)):
        jump = mass(right) - mass(left)
        assert jump == p * (p**depth + p**(3 * depth)) - 2 * p**(2 * depth)
        assert valuation(jump, p) == depth + 1
        good += 1
    assert good > 0


def valuation(n, p):
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent


def check_radix_freezing():
    b, p, s, d, t = 2, 3, 1, 3, 2
    depth, shell = 2, 3
    modulus = p**(s * depth + 1)
    jumps, _ = shell_jumps(p, s, d, depth)
    mass = prefix_evaluator(jumps)
    indices = range(1, p**(shell + 1))
    weights = [
        p**(s * (shell - valuation(i, p))) * pow(b, -t * i**d, modulus) % modulus
        for i in indices
    ]
    small_scale = p**(d * depth)
    large_scale = p**(d * shell)
    for cut in sorted(jumps):
        if cut < small_scale:
            continue
        # Check both sides of every retained jump against the original ordered tuples.
        for cutoff in (cut * (large_scale // small_scale) - 1,
                       cut * (large_scale // small_scale)):
            if cutoff < large_scale:
                continue
            direct = sum(
                weights[i - 1] * weights[j - 1] for i in indices for j in indices
                if i**d + j**d <= cutoff
            )
            assert (direct - mass(Fraction(cutoff * small_scale, large_scale))) % modulus == 0


def check_derivative(d, z, x):
    """Find three Taylor coefficients independently from f(z+h)**d = (z+h)**d+B."""
    b_shift = x**d - z**d
    first = Fraction(z**(d - 1), x**(d - 1))
    second = comb(d, 2) * (z**(d - 2) - x**(d - 2) * first**2) / (d * x**(d - 1))
    third = (
        comb(d, 3) * (z**(d - 3) - x**(d - 3) * first**3)
        - d * (d - 1) * x**(d - 2) * first * second
    ) / (d * x**(d - 1))
    formula = ((d - 1) * b_shift * z**(d - 3)
               * ((d - 2) * b_shift - (d + 1) * z**d) / x**(3 * d - 1))
    assert 6 * third == formula


if __name__ == "__main__":
    for args in [(3, 1, 3, h) for h in range(1, 6)] + [(5, 1, 3, 3), (3, 2, 4, 3)]:
        check_isolated_centers(*args)
    check_tied_weights()
    check_radix_freezing()
    for degree in (3, 4, 7):
        for z, x in product(map(Fraction, [1, 2, 3]), map(Fraction, [1, 2, 3])):
            check_derivative(degree, z, x)
    print("Verified isolated jumps, tied quadratic weights, shifted-prefix freezing and the derivative identity.")
