"""Check the ordinary bounds by removing guaranteed surviving intervals."""

from fractions import Fraction
from math import lcm


LOWER = Fraction("0.575523806608492")
UPPER = Fraction("0.575523806608494")
FINITE = Fraction(143881, 250000)
H = 81**5


def grid(base, first, limit, unit):
    """All scaled powers from the given exponent through the physical cap."""
    value = unit // base**(-first)
    assert value * base**(-first) == unit
    while value <= limit:
        yield value
        value *= base


def peak(a, b, *, finite=False, witness=False):
    """Measure simultaneous failures from below, or unprotected time from above."""
    assert 1 <= a <= b <= 25 and (not witness or (a == b and not finite))
    ternary, quinary = (0, 0) if finite else (-48, -30)
    unit = lcm(a.denominator, b.denominator) * 3**(-ternary) * 5**(-quinary)
    first = (H if finite else 1) * unit
    last = 81 * first
    events = {0: 0, first: 0, last: 0}

    def interval(left, right):
        if finite:
            # In units of B the protected endpoints must be integers.
            left = -(-left // unit) * unit
            right = right // unit * unit
        right = min(right, last)
        if left < right:
            events[left] = events.get(left, 0) + 1
            events[right] = events.get(right, 0) - 1

    rows = list(grid(3, ternary, last, unit))
    columns = list(grid(5, quinary, last, unit))
    # Every column endpoint is divisible by both phase denominators.
    for p in rows:
        for q in columns[::2]:
            low = q * a.numerator // a.denominator
            high = q * b.numerator // b.denominator
            if witness:
                interval(p + high, min(3*p, p + 5*low))
            else:
                interval(p + 5*high, min(3*p, p + 25*low))
    for q in columns:
        low = q * a.numerator // a.denominator
        high = q * b.numerator // b.denominator
        for p in rows[::4]:
            if witness:
                interval(high + p, min(5*low, low + 3*p))
            else:
                interval(high + 3*p, min(5*low, low + 81*p))

    # At a single phase the failure bands of each axis are disjoint.
    # Two active bands then imply joint failure. For an entire bracket
    # a single active survival band suffices to exclude a joint failure.
    previous = active = mass = 0
    best_mass, best_cutoff = 0, first
    for cutoff, delta in sorted(events.items()):
        if active == (2 if witness else 0):
            mass += cutoff - previous
        if cutoff >= first and mass * best_cutoff > best_mass * cutoff:
            best_mass, best_cutoff = mass, cutoff
        active += delta
        previous = cutoff
    return Fraction(best_mass, best_cutoff), Fraction(best_cutoff, unit)


def verify_cover(*, finite):
    limit = FINITE if finite else UPPER
    stack = [(Fraction(1), Fraction(25))]
    length = greatest = leaves = 0
    while stack:
        a, b = stack.pop()
        bound, _ = peak(a, b, finite=finite)
        if bound < limit:
            length += b - a
            leaves += 1
            greatest = max(greatest, bound)
        else:
            width = (b-a)/3
            assert width > Fraction(1, 10**25), "subdivision did not certify"
            stack.extend([(a, a+width), (a+width, b-width), (b-width, b)])
    assert length == 24 and greatest < limit
    return leaves, greatest


if __name__ == "__main__":
    r = Fraction(1250, 81)
    lower, cutoff = peak(r, r, witness=True)
    assert lower > LOWER and cutoff == Fraction(493, 81)
    print(f"Witness at ({r}, {cutoff}) gives at least {lower}.", flush=True)
    for finite in (True, False):
        leaves, upper = verify_cover(finite=finite)
        print(f"{'Integer prefixes' if finite else 'Continuous flow'}: "
              f"{leaves} brackets, maximum upper bound {upper}.", flush=True)
