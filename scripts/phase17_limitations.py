"""Exact finite checks for notes/phase17/limitations-and-undecidability.md.

All digit oracles use one-based positions after the binary point.
Run with python -B scripts/phase17_limitations.py.
"""

from collections.abc import Callable
from fractions import Fraction
from math import factorial, floor, lcm


Digit = Callable[[int], int]


def champernowne(n: int) -> int:
    """Skip blocks of equal-length integers, then select one bit."""
    if n < 1:
        raise ValueError("digit positions start at one")
    offset = n - 1
    width = 1
    while offset >= width * (1 << (width - 1)):
        offset -= width * (1 << (width - 1))
        width += 1
    word, index = divmod(offset, width)
    integer = (1 << (width - 1)) + word
    return (integer >> (width - 1 - index)) & 1


def liouville(n: int) -> int:
    """Membership in 1!, 2!, 3!, ... ."""
    if n < 1:
        raise ValueError("digit positions start at one")
    k = value = 1
    while value < n:
        k += 1
        value *= k
    return int(value == n)


def stoneham(n: int) -> int:
    """Parity of floor(2**n * alpha(2,3)), with a certified carry bound."""
    if n < 1:
        raise ValueError("digit positions start at one")
    p = 1
    residue = 0
    while 3 * p <= n:
        p *= 3
        residue = (3 * residue + pow(2, n - p, 2 * p)) % (2 * p)
    # The scaled prefix has mesh 1/p. Its remaining positive tail is
    # at most sum(2**(-j), j>=1)/(3*p), less than one mesh step.
    return residue // p


def bits(oracle: Digit, start: int, length: int) -> int:
    word = 0
    for n in range(start, start + length):
        word = (word << 1) | oracle(n)
    return word


def switch(before: Digit, after: Digit, halted_by: Callable[[int], bool]) -> Digit:
    return lambda n: after(n) if halted_by(n) else before(n)


def countdown(initial: int) -> Callable[[int], bool]:
    """Zero halts, a positive counter decrements, and -1 loops forever."""
    def halted_by(steps: int) -> bool:
        state = initial
        for _ in range(steps):
            if state == 0:
                break
            if state > 0:
                state -= 1
        return state == 0

    return halted_by


def completion(row: Fraction, target: Digit, n: int) -> Fraction:
    """Keep the row's odd-primary components and enter the target shift's cell."""
    mesh = 1 << n
    cell = bits(target, n + 1, n)
    return row + Fraction(cell - floor(mesh * row), mesh)


def masked_champernowne(n: int) -> int:
    """Replace positions [M_j, j*M_j) by zero, M_j = 2**(2**j), j>=2."""
    j, start = 2, 16
    while start <= n:
        if n < j * start:
            return 0
        start *= start
        j += 1
    return champernowne(n)


def check_oracles() -> None:
    expected = "".join(format(k, "b") for k in range(1, 512))
    assert all(champernowne(n) == int(bit) for n, bit in enumerate(expected, 1))
    assert {n for n in range(1, 5042) if liouville(n)} == {factorial(k) for k in range(1, 8)}

    # Independent enclosure, using ordinary rational sums and both endpoints.
    powers = (3, 9, 27, 81, 243, 729)
    lower = sum(Fraction(1, p << p) for p in powers)
    upper = lower + Fraction(1, 1 << (3 * powers[-1] - 1))
    for n in range(1, 1001):
        lo, hi = int(lower * (1 << n)), int(upper * (1 << n))
        assert lo == hi
        assert stoneham(n) == lo % 2


def check_switches() -> None:
    for before, after in ((champernowne, liouville), (liouville, champernowne)):
        for t in (-1, 0, 1, 2, 9, 63, 128, 201):
            stream = switch(before, after, countdown(t))
            assert all(stream(n) == (before(n) if t < 0 or n < t else after(n))
                       for n in range(1, 202))
            if t < 0:
                continue
            m = max(0, t - 1)
            delta = Fraction(bits(before, 1, m) - bits(after, 1, m), 1 << m)
            for length in (m, m + 1, m + 85):
                diff = bits(stream, 1, length) - bits(after, 1, length)
                assert Fraction(diff, 1 << length) == delta
            # Check the interval-count bound on genuine infinite-stream
            # cylinders. No padding or assumption about later bits is needed.
            width, sample = 5, 151
            left = [bits(stream, n, width) for n in range(1, sample + 1)]
            right = [bits(after, n, width) for n in range(1, sample + 1)]
            assert left[m:] == right[m:]
            for a in range(1 << width):
                for b in range(a + 1, (1 << width) + 1):
                    diff = sum(a <= w < b for w in left) - sum(a <= w < b for w in right)
                    assert abs(diff) <= min(m, sample)


def check_pairs() -> None:
    row = Fraction(0)
    for n in range(1, 151):
        row = 2 * row + Fraction(1, n)
        models = [completion(row, target, n) for target in (champernowne, liouville)]
        for model, target in zip(models, (champernowne, liouville)):
            denominator = (model - row).denominator
            assert denominator & (denominator - 1) == 0
            assert int((1 << n) * model) == bits(target, n + 1, n)
        denominator = (models[0] - models[1]).denominator
        assert denominator & (denominator - 1) == 0

    # Use a common denominator to count logarithmically weighted words exactly.
    intervals = [(16, 32), (256, 768)]
    sample = 2049
    scale = lcm(*range(1, sample + 1))
    for width in range(1, 6):
        changes = [0] * (1 << width)
        affected_mass = 0
        for n in range(1, sample + 1):
            original = bits(champernowne, n, width)
            masked = bits(masked_champernowne, n, width)
            affected = any(n < hi and n + width > lo for lo, hi in intervals)
            weight = scale // n
            changes[original] -= weight
            changes[masked] += weight
            if affected:
                affected_mass += weight
            else:
                assert original == masked
        assert sum(changes) == 0
        assert max(abs(change) for change in changes) <= affected_mass
    for j in range(2, 10):
        start = 1 << (1 << j)
        stop = j * start
        for n in (start - 1, start, stop - 8, stop - 1, stop):
            expected = 0 if start <= n < stop else champernowne(n)
            assert masked_champernowne(n) == expected
        assert bits(masked_champernowne, stop - 8, 8) == 0
        if j <= 3:
            zero_starts = sum(bits(masked_champernowne, n, 8) == 0 for n in range(1, stop + 1))
            assert zero_starts >= stop - start - 7


if __name__ == "__main__":
    check_oracles()
    check_switches()
    check_pairs()
    print("Passed: three digit oracles, both switch directions, dyadic edits, and both pairs.")
