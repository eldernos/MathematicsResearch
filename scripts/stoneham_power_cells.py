"""Exact leading p-adic cell tests for powers of the standard prime-axis Stoneham series."""
from collections import Counter
from fractions import Fraction
from math import factorial


def multisets(size, budget, minimum=0, prefix=()):
    """Nondecreasing deficit tuples with sum at most budget."""
    if size == 0:
        yield prefix
        return
    for i in range(minimum, budget//size+1):
        yield from multisets(size-1, budget-i, i, prefix+(i,))


def power_cells(p, degree, precision):
    if p < 2 or degree < 1 or precision < 1:
        raise ValueError("require a base >= 2 and positive degree and precision")
    changes = Counter()
    for indices in multisets(degree, precision-1):
        threshold = sum(Fraction(1, p**i) for i in indices)
        if threshold >= p:
            continue
        multiplicity = factorial(degree)
        for count in Counter(indices).values():
            multiplicity //= factorial(count)
        changes[max(Fraction(1), threshold)] += multiplicity*p**sum(indices)
    offsets = sorted(set(changes) | {Fraction(1)})
    value = 0
    cells = []
    for t in offsets:
        value = (value + changes[t]) % (p**precision)
        cells.append((t, value))
    return cells


def first_passing(p, degree, limit):
    for level in range(1, limit+1):
        cells = power_cells(p, degree, level)
        if all(value for _, value in cells):
            return level, len(cells)
    return None


if __name__ == '__main__':
    for d in range(1, 10):
        print('degree, first passing precision and cells:', d, first_passing(3, d, 30))
