#!/usr/bin/env python3
"""Enclose the ordinary upper density of simultaneous top-power failures.

All interval endpoints and comparisons in the certificate are integers or
Fractions. Run with python3 scripts/phase14_mixed_flow.py.
"""

from bisect import bisect_right
from fractions import Fraction
from math import lcm


def merge(intervals):
    merged = []
    for left, right in sorted(intervals):
        if left >= right:
            continue
        if merged and left <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(right, merged[-1][1]))
        else:
            merged.append((left, right))
    return merged


def intersect(first, second):
    i = j = 0
    while i < len(first) and j < len(second):
        a, b = first[i]
        c, d = second[j]
        if max(a, c) < min(b, d):
            yield max(a, c), min(b, d)
        if b <= d:
            i += 1
        if d <= b:
            j += 1


def peak(intervals, unit):
    """Maximize covered length / cutoff for unit <= cutoff <= 81*unit."""
    mass = 0
    best = Fraction(0)
    witness = Fraction(1)
    at_one = 0
    for left, right in intervals:
        if left >= 81 * unit:
            break
        right = min(right, 81 * unit)
        mass += right - left
        # The ratio increases within covered intervals and decreases in gaps.
        if right >= unit and mass * best.denominator > best.numerator * right:
            best, witness = Fraction(mass, right), Fraction(right, unit)
        if left < unit:
            at_one += min(right, unit) - left
    if at_one * best.denominator > best.numerator * unit:
        return Fraction(at_one, unit), Fraction(1)
    return best, witness


def flow_intervals(left, right, depth, *, outer, nonrectangular=False):
    """Return disjoint inner intervals at a point or outer intervals for a phase bracket."""
    assert 1 <= left <= right <= 25 and (outer or left == right)
    # The subdivision uses dyadic phases. Scale to integer endpoints, including
    # all negative powers retained from the two geometric grids.
    denominator = lcm(left.denominator, right.denominator)
    unit = denominator * 81**depth * 25**depth
    row = [unit // 3**(-i) if i < 0 else unit * 3**i
           for i in range(-4 * depth, 5)]
    col_unit = [unit // 5**(-j) if j < 0 else unit * 5**j
                for j in range(-2 * depth, 4)]
    col_lo = [value * left.numerator // left.denominator for value in col_unit]
    col_hi = [value * right.numerator // right.denominator for value in col_unit]
    row_bad = []
    col_bad = []
    if outer:
        row_bad.append((0, row[0]))
        col_bad.append((0, col_hi[0]))
    for p in row:
        if outer:
            row_bad.append((p, min(3 * p, p + col_hi[0])))
        for qlo, qhi in zip(col_lo[::2], col_hi[::2]):
            row_bad.append((p + qlo, min(3 * p, p + 5 * qhi)))
    for qlo, qhi in zip(col_lo, col_hi):
        if outer:
            col_bad.append((qlo, min(5 * qhi, qhi + row[0])))
        for p in row[::4]:
            col_bad.append((qlo + p, min(5 * qhi, qhi + 3 * p)))
    failures = intersect(merge(row_bad), merge(col_bad))
    if not nonrectangular:
        return failures, unit

    # On [max(P,Q), min(3P,5Q)) the missing corner is equivalent to x<P+Q.
    # Enlarge each moving Q-box for an outer union and include unresolved starts.
    corners = [(0, max(row[0], col_hi[0]))] if outer else []
    for p in row:
        for qlo, qhi in zip(col_lo, col_hi):
            corners.append((max(p, qlo), min(3*p, 5*qhi, p+qhi)))
    return intersect(list(failures), merge(corners)), unit


def flow_bound(left, right, depth, *, outer, nonrectangular=False):
    return peak(*flow_intervals(left, right, depth, outer=outer, nonrectangular=nonrectangular))


def certify(depth, tolerance, *, nonrectangular=False):
    """Bisect until every phase interval is bounded by the witness + tolerance."""
    phase = Fraction(25, 2) if nonrectangular else Fraction(1250, 81)
    lower, cutoff = flow_bound(phase, phase, depth, outer=False, nonrectangular=nonrectangular)
    upper = Fraction(0)
    pending = [(Fraction(1), Fraction(25))]
    boxes = 0
    while pending:
        left, right = pending.pop()
        mid = (left + right) / 2
        value, arg = flow_bound(mid, mid, depth, outer=False, nonrectangular=nonrectangular)
        if value > lower:
            lower, phase, cutoff = value, mid, arg
        cap, _ = flow_bound(left, right, depth, outer=True, nonrectangular=nonrectangular)
        assert value <= cap
        if cap <= lower + tolerance:
            upper = max(upper, cap)
            boxes += 1
        else:
            pending.extend([(mid, right), (left, mid)])
    return lower, upper, phase, cutoff, boxes


def powers(base, stop):
    values = [1]
    while values[-1] * base < stop:
        values.append(values[-1] * base)
    return values


def cell_lengths(intervals, width, count):
    """Covered length of consecutive physical unit cells in scaled coordinates."""
    span = next(intervals, None)
    completed = previous = 0
    for n in range(1, count + 1):
        edge = n * width
        while span and span[1] <= edge:
            completed += span[1] - span[0]
            span = next(intervals, None)
        total = completed + (max(0, edge - span[0]) if span else 0)
        yield total - previous
        previous = total


def check_integer_cells():
    # Normalize by three successive powers of 81. At physical shell starts
    # the true flow may oscillate inside one integer cell. Everywhere else
    # both inner and outer integrals must reproduce the direct integer tests.
    for k in range(3):
        scale = 81**k
        end = 81 * scale
        col_scale = 1
        while col_scale < scale:
            col_scale *= 25
        phase = Fraction(col_scale, scale)
        threes, fives = powers(3, end), powers(5, end)
        borders = {0, *threes, *fives}
        lengths = []
        for outer in (False, True):
            intervals, unit = flow_intervals(phase, phase, 5, outer=outer)
            assert unit % scale == 0
            width = unit // scale
            lengths.append(cell_lengths(intervals, width, end))
        for n, (inner, outer) in enumerate(zip(*lengths, strict=True)):
            p = threes[max(0, bisect_right(threes, n) - 1)]
            q = fives[max(0, bisect_right(fives, n) - 1)]
            j = max(0, bisect_right(fives, n - p) - 1)
            i = max(0, bisect_right(threes, n - q) - 1)
            expected = width if j % 2 == i % 4 == 0 else 0
            assert 0 <= inner <= outer <= width
            if n in borders:
                assert outer <= expected
            else:
                assert inner == outer == expected, (k, n)


if __name__ == "__main__":
    check_integer_cells()
    low, high, phase, cutoff, boxes = certify(16, Fraction(1, 10**15))
    # The displayed decimals round outwards; the tests here are exact.
    assert Fraction("0.575523806608492") < low <= high < Fraction("0.575523806608494")
    assert high < Fraction(143881, 250000) < Fraction(27, 40)
    print("Integer cells and shell edges checked through 531440.")
    print(f"lower = {low}\nupper = {high}\nwitness r = {phase}, T = {cutoff}")
    print(f"{boxes} certified phase intervals")
    print("0.575523806608492 < ordinary upper density < 0.575523806608494")
