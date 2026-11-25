"""Exact finite checks for notes/phase18/programming.md. Standard library only.

Run: python -B scripts/phase18_programming.py
"""

from fractions import Fraction as Q
from math import floor, gcd, isqrt, lcm


def coefficient(b, gap, previous, current):
    residue = (current - b**gap * previous) % 1
    return residue or Q(1)


def coefficient_denominator(b, gap, previous, current):
    power = b**gap
    common = gcd(power, previous.denominator)
    d = previous.denominator // common
    a = power * previous.numerator // common
    multiple = lcm(d, current.denominator)
    numerator = current.numerator * (multiple // current.denominator) - a * (multiple // d)
    return multiple // gcd(multiple, numerator)


def residue_discrepancy(points, denominator):
    """Exact extreme discrepancy, with repeats, for integer residues / denominator."""
    count = len(points)
    # The largest positive arc excess is the oscillation of the cumulative
    # count minus length. Both sides of each jump enter the supremum.
    before = [i * denominator - x * count for i, x in enumerate(sorted(points))]
    return Q(max(before) + denominator - min(before), count * denominator)


def direct_arc_discrepancy(points, denominator):
    """Check the shortest enclosing arc for every inclusive circular run."""
    support = sorted(set(points))
    largest = Q(0)
    for start in support:
        for stop in support:
            span = (stop - start) % denominator
            enclosed = sum((x - start) % denominator <= span for x in points)
            largest = max(largest, Q(enclosed, len(points)) - Q(span, denominator))
    return largest


def check_coefficients():
    targets = sorted({Q(a, d) for d in range(1, 11) for a in range(d)})
    comparisons = 0
    for b in (2, 3, 6, 10):
        for gap in (1, 2, 4):
            for previous in targets:
                for current in targets:
                    c = coefficient(b, gap, previous, current)
                    assert 0 < c <= 1
                    assert (b**gap * (5 + previous) + c) % 1 == current
                    assert c.denominator == coefficient_denominator(b, gap, previous, current)
                    comparisons += 1
            first = 3
            for current in targets:
                c = coefficient(b, gap, Q(1, 3), current)
                group = sum(Q(b-1, b**gap-1) * c / b**m
                            for m in range(first + 1, first + gap + 1))
                assert group == c / b**(first + gap)
    assert coefficient(2, 1, Q(1, 3), Q(2, 3)) == 1
    assert coefficient(2, 1, Q(1, 9), Q(5, 9)).denominator == 3
    assert coefficient(2, 1, Q(1, 9), Q(1, 9)).denominator == 9
    print(f"B1: {comparisons} reduced denominators and prefix transitions; dense group sums exact")


def cycle_from(b, q, start):
    orbit = [start]
    residue = start * b % q
    while residue != start:
        orbit.append(residue)
        residue = residue * b % q
    return orbit


def prime_period_data(b, p):
    t = len(cycle_from(b, p, 1))
    factor = b**t - 1
    v = 0
    while factor % p == 0:
        factor //= p
        v += 1
    return t, v


def next_prime_power(p, k):
    """p^(1+floor(log_p k)) without numerical logarithms, k>=1."""
    q = p
    while q <= k:
        q *= p
    return q


def check_periods():
    for points in ([3], [2, 2, 2], [0, 1, 7], [1, 1, 3, 6, 6], [7, 1]):
        assert residue_discrepancy(points, 8) == direct_arc_discrepancy(points, 8)
    cycles = 0
    for b, p in ((2, 3), (2, 7), (8, 3), (10, 3), (19, 3), (3, 5)):
        t, v = prime_period_data(b, p)
        for e in range(1, 5):
            q = p**e
            remaining = {a for a in range(q) if a % p}
            while remaining:
                orbit = cycle_from(b, q, min(remaining))
                assert set(orbit) <= remaining
                remaining.difference_update(orbit)
                assert len(orbit) == t * p**max(e-v, 0)
                assert residue_discrepancy(orbit, q) <= min(1, Q(p**v, q))
                cycles += 1
    print(f"B2: {cycles} complete unit orbits, including nonprimitive cosets and v>1")


def check_windows():
    # A full uniform grid and a retired three-cycle in alternating positions.
    # Signed displacements cross zero, and sparse outliers exceed epsilon.
    scale = 420
    models = [((n//2) * 60 if n % 2 == 0 else (n//2 % 3)*140) % scale for n in range(80)]
    shifts = [(-1)**(n//2) * (103 if n % 13 == 0 else 2) for n in range(80)]
    observations = [(m+s) % scale for m, s in zip(models, shifts)]
    tested = 0
    for left in (0, 3, 7, 19):
        for right in range(left+1, len(models)+1):
            active = [models[n] for n in range(left, right) if n % 2 == 0]
            retired = [models[n] for n in range(left, right) if n % 2]
            length = right-left
            error = len(active)*residue_discrepancy(active, scale) if active else 0
            excess = len(retired)*residue_discrepancy(retired, scale) if retired else 0
            bad = sum(abs(shifts[n]) > 2 for n in range(left, right))
            actual = residue_discrepancy(observations[left:right], scale)
            assert abs(length*actual-excess) <= error+bad+Q(4*length, scale)
            tested += 1
    print(f"G1: {tested} translated windows with signed errors, outliers and finite cycles")


def cubic_prefix(b, p, delta, blocks):
    t, _ = prime_period_data(b, p)
    positions = [t * k**3 for k in range(blocks + 1)]
    targets = [Q(0)]
    prefix = Q(0)
    for k in range(1, blocks + 1):
        q = next_prime_power(p, k)
        assert k < q <= p*k
        retired = floor(k * delta) - floor((k-1) * delta)
        target = Q(0) if retired else Q(1, q)
        c = coefficient(b, positions[k] - positions[k-1], targets[-1], target)
        prefix += c / b**positions[k]
        assert (prefix * b**positions[k]) % 1 == target
        targets.append(target)
    return positions, targets, prefix


def check_all_prefixes(b, p, delta, blocks=7):
    positions, targets, prefix = cubic_prefix(b, p, delta, blocks)
    t, v = prime_period_data(b, p)
    total = positions[-2] + 1  # includes the next observation after a boundary
    next_position = t * (blocks+1)**3
    scale = lcm(*(u.denominator for u in targets))
    exact = []
    model = []
    active = []
    distances = []
    counts = [0] * len(targets)
    k = 0
    residue = prefix.numerator % prefix.denominator
    tail_factor = Q(b, b-1)
    for n in range(total):
        if n == positions[k+1]:
            k += 1
        u = targets[k]
        q = u.denominator
        local = n - positions[k]
        shadow = (u.numerator * pow(b, local, q) % q) * (scale // q)
        exact.append(residue)
        model.append(shadow)
        if u:
            active.append(shadow)
        counts[k] += 1
        distance_to_insertion = positions[k+1] - n
        distances.append(distance_to_insertion)
        # Check the real shifted tail bound modulo one against the finite sum.
        finite_tail_mod_one = (Q(residue, prefix.denominator) - Q(shadow, scale)) % 1
        assert finite_tail_mod_one <= tail_factor / b**distance_to_insertion
        residue = residue * b % prefix.denominator

        N = n+1
        error = Q(0)
        for index in range(k+1):
            denom = targets[index].denominator
            if denom == 1:
                continue
            period = t * max(1, denom // p**v)
            remainder = counts[index] % period
            error += (counts[index]-remainder) * min(1, Q(p**v, denom)) + remainder
        assert error <= Q((7*t*p**v + p)*k*(k+1), 2)
        if active:
            assert len(active) * residue_discrepancy(active, scale) <= error
        retired_fraction = Q(N-len(active), N)
        assert abs(residue_discrepancy(model, scale) - retired_fraction) <= error/N

        # Use the true infinite-tail bound to count exceptional positions. The
        # computed finite-series discrepancy itself encloses the infinite one
        # to within twice the maximum unobserved circular displacement.
        W = 1
        while (b-1) * b**W < b * (k+1):
            W += 1
        epsilon = Q(1, k+1)
        bad = sum(d < W for d in distances)
        assert bad <= (k+1) * W
        d_finite = residue_discrepancy(exact, prefix.denominator)
        radius = 2 * tail_factor / b**(next_position-n)
        assert abs(d_finite - retired_fraction) + radius <= (error+bad)/N + 2*epsilon
        if b == 2 and delta == Q(2, 5) and N == 400:
            unit = 10**6
            lower = floor((d_finite-radius)*unit)
            upper = -floor(-(d_finite+radius)*unit)
            print(f"B3: b=2, p=3, delta=2/5, N=400: D_N in [{lower}, {upper}] / {unit}")
    return total


def check_masks():
    b, p, t = 2, 3, 2
    count = 0
    for delta in (Q(0), Q(1, 7), Q(1, 2), Q(2, 3), Q(1)):
        for approximate in (False, True):
            target_sum = Q(0)
            retired_steps = 0
            retired_time = t
            C = 2 if approximate else 1
            for k in range(1, 151):
                term = delta
                if approximate:
                    term = min(Q(1), max(Q(0), delta + Q((-1)**k, 2**k)))
                target_sum += term
                bit = floor(target_sum) - retired_steps
                retired_steps += bit
                assert bit in (0, 1)
                assert abs(retired_steps-k*delta) <= C
                start = t * k**3
                gap = t * (3*k*k + 3*k + 1)
                for observed in (0, 1, gap//2, gap-1, gap):
                    length = start + observed
                    assert abs(retired_time + observed*bit - length*delta) <= t + (2*C+1)*gap
                    count += 1
                retired_time += bit * gap
                q = next_prime_power(p, k)
                assert q//p <= k < q
                assert 2 * Q(b, (b-1)*b**gap) < Q(1, q)
    print(f"B3: {count} cubic weighted cutoffs; exact rational ties and rounded Cauchy inputs")


def check_components():
    weights = [Q(1, 9), Q(1, 3), Q(5, 9)]
    types = [Q(0), Q(1, 7), Q(3, 7)]
    assert set(cycle_from(2, 7, 1)).isdisjoint(cycle_from(2, 7, 3))
    counts = [0] * len(types)
    times = [0] * len(types)
    for k in range(1, 121):
        selected = max(range(len(types)), key=lambda i: k*weights[i]-counts[i])
        counts[selected] += 1
        gap = (k+1)**3 - k**3
        times[selected] += gap
        for i, weight in enumerate(weights):
            assert -(len(types)-1) <= counts[i]-k*weight <= 1
            assert abs(times[i] - ((k+1)**3-1)*weight) <= 2*len(types)*gap
    # An irregular mask with alternating rates and one cumulative rounding.
    lower_rate, upper_rate = Q(1, 5), Q(4, 7)
    target_sum = Q(0)
    target_time = lower_rate
    retired_time = 1
    stage_end = 2
    rate = lower_rate
    for k in range(1, 1025):
        if k == stage_end:
            rate = upper_rate if rate == lower_rate else lower_rate
            stage_end *= stage_end
        new_sum = target_sum + rate
        retired = floor(new_sum) - floor(target_sum)
        target_sum = new_sum
        gap = (k+1)**3-k**3
        target_time += gap*rate
        retired_time += gap*retired
        assert lower_rate <= target_time/(k+1)**3 <= upper_rate
        assert abs(retired_time-target_time) <= 1 + 3*gap
    # Test the sparse algebraic diagonal choice against sqrt(2) with a certified
    # rational enclosure for its shifted orbit, including its two candidate bits.
    for k in (2, 4, 8):
        q = next_prime_power(3, k)
        start = 2*k**3
        gap = 2*((k+1)**3-k**3)
        scale = 16*q
        lower = isqrt(2 * (scale * 2**start)**2)
        approximation = Q(lower, scale) % 1
        def distance(point):
            forward = (point - approximation) % 1
            return min(forward, 1-forward)
        separation = max(distance(Q(0)), distance(Q(1, q)))
        assert separation - Q(1, scale) > Q(2, 2**gap)
    print("B4: three orbit types, irregular mask weights, sparse algebraic avoidance")


def main():
    check_coefficients()
    check_periods()
    check_windows()
    cutoffs = sum(check_all_prefixes(2, 3, delta) for delta in (Q(0), Q(2, 5), Q(1)))
    cutoffs += check_all_prefixes(10, 3, Q(1, 2))
    print(f"B2/B3/G1: {cutoffs} all-prefix finite discrepancies with rigorous infinite-tail radii")
    check_masks()
    check_components()


if __name__ == "__main__":
    main()
