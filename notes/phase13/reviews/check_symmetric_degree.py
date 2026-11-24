"""Independent finite checks for the dyadic Stoneham degree review."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb


def check_cyclic_cuts():
    # Any upper set generated in this grid is determined by clamping at 2.
    grid = list(product(range(3), repeat=3))
    orbits = {min(v, v[1:] + v[:1], v[2:] + v[:2]) for v in grid}
    orbit_bit = {v: 1 << i for i, v in enumerate(sorted(orbits))}
    bit = {v: orbit_bit[min(v, v[1:] + v[:1], v[2:] + v[:2])] for v in grid}
    edges = [(v, v[:i] + (v[i] + 1,) + v[i + 1:])
             for v in grid for i in range(3) if v[i] < 2]
    count = 0
    for mask in range(1, 1 << len(orbits)):
        if any(mask & bit[v] and not mask & bit[w] for v, w in edges):
            continue
        # The cell over v has a free geometric tail in each clamped coordinate.
        numerator = Counter()
        for v in grid:
            if mask & bit[v]:
                exponent = 3 - v.count(2)
                for j in range(exponent + 1):
                    numerator[sum(v) + j] += (-1)**j * comb(exponent, j)
        first = next(j for j in range(3) if mask & bit[(j, j, j)])
        assert {j: c % 3 for j, c in numerator.items() if c % 3} == {3 * first: 1}
        count += 1
    return count


def reflected_cube():
    modulus = 128
    jumps = Counter({Fraction(1): 0})
    for v in product(range(7), repeat=3):
        if sum(v) >= 7:
            continue
        cut = sum(Fraction(1, 1 << i) for i in v)
        if cut < 2:
            jumps[max(1, cut)] += 1 << sum(v)
    residue = 0
    rows = []
    for cut, increment in sorted(jumps.items()):
        residue = (residue + increment) % modulus
        assert residue
        rows.append((str(cut), residue))
    return rows


def check_positive_indices():
    positions = 0
    for k in (7, 8, 9):
        shell = 1 << k
        insertions = Counter()
        for js in product(range(1, k + 1), repeat=3):
            insertions[sum(1 << j for j in js)] += 1 << (3 * k - sum(js))
        for b in (3, 5, 7):
            numerator = 0
            for n in range(2 * shell):
                numerator = b * numerator + insertions[n]
                if n >= shell:
                    loss = next(loss for end, loss in ((9, 5), (10, 6), (12, 4), (16, 3))
                                if 8 * n < end * shell)
                    assert numerator % (2 << loss) == 1 << loss
                    positions += 1
    return positions


if __name__ == "__main__":
    print("Cyclic upper sets:", check_cyclic_cuts())
    print("Cube cut and residue:", reflected_cube())
    print("Positive-index prefix checks:", check_positive_indices())
