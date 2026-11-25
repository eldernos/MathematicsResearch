"""Exact finite checks for notes/phase17/mixed-product-orbits.md."""

from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm


def order(value, modulus):
    if modulus == 1:
        return 1
    power, period = value % modulus, 1
    while power != 1:
        power = power * value % modulus
        period += 1
    return period


def valuation(value, prime):
    assert value
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def term(base, p, q, j, modulus):
    # Signed j is allowed on the chosen periodic torsion sheets when q is a unit.
    phi = modulus - modulus // p
    return pow(q, -j, modulus) * pow(base, -pow(q, j, phi), modulus) % modulus


def partial_sum(base, p, q, m, modulus):
    return sum(term(base, p, q, j, modulus) for j in range(1, m + 1)) % modulus


def side_parameters(base, p, q):
    torsion = order(base, p)
    prime_free = torsion // gcd(torsion, q)
    assert gcd(prime_free, q) == 1
    period = lcm(order(q, p), order(q, prime_free))
    first_sum = partial_sum(base, p, q, period, p * p)
    if first_sum % p:
        period *= p
    modulus = p * p
    block = partial_sum(base, p, q, period, modulus)
    zeros = tuple(j for j in range(1, period + 1)
                  if partial_sum(base, p, q, j, modulus) % p == 0)
    return period, block, zeros


class Axis:
    def __init__(self, base, p, q, precision):
        self.base, self.p, self.q = base, p, q
        self.u, block, zeros = side_parameters(base, p, q)
        assert zeros == (self.u,) and block % p == 0 and block != 0
        self.slope = block // p
        self.modulus = p ** precision
        values = [partial_sum(base, p, q, self.u * z, self.modulus)
                  for z in range(precision)]
        self.coefficients = []
        for k in range(1, precision):
            values = [(right - left) % self.modulus for left, right in zip(values, values[1:])]
            assert values[0] % p ** k == 0
            self.coefficients.append(values[0])

    def blocks(self, z, modulus):
        total, choose = 0, 1
        for k, coefficient in enumerate(self.coefficients, start=1):
            choose = choose * (z - k + 1) // k
            total += coefficient * choose
        return total % modulus

    def g(self, a, d, z, modulus):
        p = self.p
        m = a + self.u * z
        endpoint = 0 if d is None else p ** d * term(self.base, p, self.q, m, modulus)
        return (self.blocks(z, modulus) + p * sum(
            term(self.base, p, self.q, m - j, modulus) for j in range(1, a)
        ) + endpoint) % modulus

    def alpha(self, a, d, digits):
        p = self.p
        step, z = 1, 0
        inverse = pow(self.slope, -1, p)
        for _ in range(digits):
            place = p * step
            value = self.g(a, d, z, p * place)
            assert value % place == 0
            z += (-value // place * inverse % p) * step
            step *= p
        assert self.g(a, d, z, p * step) == 0
        return a + self.u * z


def arc_discrepancy(weighted_cycles):
    atoms = {}
    mass = F(0)
    for weight, orbit in weighted_cycles:
        mass += weight
        for point in orbit:
            atoms[point] = atoms.get(point, F(0)) + weight / len(orbit)
    assert 0 <= mass <= 1
    cumulative, extrema = F(0), [F(0)]
    for point, weight in sorted(atoms.items()):
        extrema.append(cumulative - mass * point)
        cumulative += weight
        extrema.append(cumulative - mass * point)
    return max(extrema) - min(extrema)


def cycle(base, numerator, denominator):
    assert gcd(base, denominator) == gcd(numerator, denominator) == 1
    start = residue = numerator % denominator
    orbit = [F(residue, denominator)]
    while True:
        residue = base * residue % denominator
        if residue == start:
            return orbit
        orbit.append(F(residue, denominator))


def verify_cycles():
    base_values = {3: F(2, 3), 5: F(2, 5), 15: F(11, 20)}
    for numerator in (1, 7):
        assert arc_discrepancy([(F(1), cycle(2, numerator, 15))]) == base_values[15]
    for r in range(5):
        for s in range(4):
            denominator = 3 ** r * 5 ** s
            kernel = (3 if r else 1) * (5 if s else 1)
            for numerator in (1, 7):
                orbit = cycle(2, numerator, denominator)
                assert len(orbit) == (1 if not r and not s else lcm(
                    2 * 3 ** (r - 1) if r else 1, 4 * 5 ** (s - 1) if s else 1
                ))
                expected = base_values.get(kernel, F(1)) * kernel / denominator
                assert arc_discrepancy([(F(1), orbit)]) == expected
                if denominator > 1:
                    for i, point in enumerate(sorted(orbit)):
                        assert F(i + 1, len(orbit)) <= F(15, 4) * point
                        assert F(len(orbit) - i, len(orbit)) <= F(15, 4) * (1 - point)
    first, second = cycle(2, 1, 15), cycle(2, 7, 15)
    mixture = arc_discrepancy([(F(1, 4), first), (F(1, 4), second)])
    assert mixture == F(7, 60) < base_values[15] / 2
    assert arc_discrepancy([(F(1, 3), first[:3]), (F(1, 3), cycle(2, 0, 1))]) >= F(1, 3)
    assert arc_discrepancy([(F(3, 8), cycle(2, 0, 1)), (F(1, 8), second)]) == F(3, 8)
    print(f"Binary cycles: {base_values}; equal-weight coset mixture: {mixture}")


def interval_lines(p, q, a, d):
    lower = [(F(1), F(1, q ** a)), (F(1, p ** d), F(1))]
    upper = [(F(1), F(1, q ** (a - 1))), (F(1, p ** (d - 1)), F(1)),
             (F(p), F(0)), (F(0), F(q))]
    return lower, upper


def exact_maximum(p, q, a, d):
    lower, upper = interval_lines(p, q, a, d)
    candidates = {F(1, q), F(p)}
    for (a0, a1), (b0, b1) in combinations(lower + upper, 2):
        if a1 != b1:
            ratio = (b0 - a0) / (a1 - b1)
            if F(1, q) <= ratio <= p:
                candidates.add(ratio)
    return max((max(F(0), 1 - max(c + m * r for c, m in lower) /
                    min(c + m * r for c, m in upper)), r) for r in candidates)


def verify_axis(axis, binary):
    base, p, q, u = axis.base, axis.p, axis.q, axis.u
    modulus = p ** 12
    for z in range(20):
        assert axis.blocks(z, modulus) == partial_sum(base, p, q, u * z, modulus)
    for m in range(1, 16):
        assert partial_sum(base ** q, p, q, m, modulus) == (
            q * partial_sum(base, p, q, m + 1, modulus) - pow(base, -q, modulus)
        ) % modulus
    depth = 12
    for a in (1, 2, 3, 4):
        limit = axis.alpha(a, None, depth)
        roots = [axis.alpha(a, d, depth) for d in range(1, 8)]
        for d, root in enumerate(roots, 1):
            assert valuation(root - limit, p) == valuation(u, p) + d - 1
            for next_root in roots[d:]:
                assert valuation(root - next_root, p) == valuation(u, p) + d - 1
    for k in (1, 2, p, p * p):
        first = axis.alpha(1, 1, depth)
        later = axis.alpha(1 + u * k, 1, depth)
        assert valuation(later - first, p) == valuation(u * k, p)
    if binary and p in (3, 5):
        expected = {3: (54, 27), 5: (500, 349)}[p]
        assert axis.alpha(1, 1, depth) % expected[0] == expected[1]


def depth_certificate(p_axis, q_axis):
    p, q = p_axis.p, q_axis.p
    eta, delta = F(1, 10 ** 6), F(1, 10 ** 7)

    def first_power_above(prime, bound):
        exponent = 0
        while prime ** exponent <= bound:
            exponent += 1
        return exponent

    a_max = first_power_above(q, 1 / eta)
    d_max = first_power_above(p, 1 / eta)
    r_k = first_power_above(p, 1 / delta) + 1
    r_l = first_power_above(q, 1 / delta) + 1
    max_depth = 14
    roots = [(p_axis.alpha(a, d, max_depth - 1), q_axis.alpha(d, a, max_depth - 1))
             for a in range(1, a_max + 1) for d in range(1, d_max + 1)]
    pairs = [(x - u, y - v) for (x, y), (u, v) in combinations(roots, 2)]

    def near(value, modulus, radius):
        residue = value % modulus
        return min(residue, modulus - residue) <= radius

    for h, k in sorted(((h, k) for h in range(2, max_depth + 1)
                        for k in range(2, max_depth + 1)), key=sum):
        mod_p, mod_q = p_axis.u * p ** (h - 1), q_axis.u * q ** (k - 1)
        if mod_p > r_l and mod_q > r_k and not any(
            near(d_l, mod_p, r_l) and near(d_k, mod_q, r_k) for d_l, d_k in pairs
        ):
            bound = F((p - 1) * (q - 1), 2 * p * q - p - q)
            bound += (F(p, p - 1) + F(q, q - 1)) * eta + delta
            print(f"  grid {a_max}×{d_max}, radii ({r_k}, {r_l}), depths ({h}, {k}), "
                  f"moduli ({mod_p}, {mod_q}): D^+ <= {bound} ({float(bound):.12f})")
            return bound
    raise AssertionError("No certificate at these depths")


def verify_prefixes(base, p, q):
    # All insertions and shell boundaries below this cutoff, plus their predecessors.
    cutoff = p ** 12
    pp = [p ** j for j in range(1, 13)]
    qq = [q ** j for j in range(1, 13) if q ** j <= cutoff]
    events = set(pp + qq + [P + Q for P in pp for Q in qq if P + Q <= cutoff])
    minimum = cutoff ** 2
    for n in sorted(events | {n - 1 for n in events}):
        if n < p + q:
            continue
        K = sum(P <= n for P in pp)
        L = sum(Q <= n for Q in qq)
        P, Q = pp[K - 1], qq[L - 1]
        a = L - sum(P + y <= n for y in qq)
        d = K - sum(x + Q <= n for x in pp)
        modulus = P * Q
        numerator = sum((P // x) * (Q // y) * pow(base, n - x - y, modulus)
                        for x in pp[:K] for y in qq[:L] if x + y <= n) % modulus
        minimum = min(minimum, modulus // gcd(numerator, modulus))
        if 0 < a < L and 0 < d < K:
            lower, upper = interval_lines(p, q, a, d)
            ratio = F(Q, P)
            assert max(c + m * ratio for c, m in lower) * P <= n
            assert n < min(c + m * ratio for c, m in upper) * P
        for own, other, H, m, gap, cross_gap in ((p, q, K, L, a, d), (q, p, L, K, d, a)):
            precision = own ** H
            g = partial_sum(base, own, other, m - gap, precision)
            if gap:
                g += own * sum(term(base, own, other, j, precision) for j in range(m - gap + 1, m))
                g += own ** cross_gap * term(base, own, other, m, precision)
            assert gcd(numerator, precision) == gcd(g, precision)
    print(f"  Checked switch boundaries through {cutoff:,}: minimum nonempty-prefix denominator {minimum}")
    assert minimum > 1


def main():
    verify_cycles()
    good = ((2, 3, 5), (2, 3, 7), (2, 3, 13), (36, 5, 7))
    for base, p, q in good:
        axes = Axis(base, p, q, 16), Axis(base, q, p, 16)
        print(f"({base}, {p}, {q}): {side_parameters(base, p, q)}, {side_parameters(base, q, p)}")
        maximum = F((p - 1) * (q - 1), 2 * p * q - p - q)
        assert exact_maximum(p, q, 1, 1) == (maximum, F(q * (p - 1), p * (q - 1)))
        for a in range(1, 11):
            for d in range(1, 11):
                if (a, d) != (1, 1):
                    assert exact_maximum(p, q, a, d)[0] <= F(p - 1, p * p) < maximum
        for axis in axes:
            verify_axis(axis, (base, p, q) == (2, 3, 5))
        verify_prefixes(base, p, q)
        if (base, p, q) != (2, 3, 5):
            bound = depth_certificate(*axes)
            assert maximum < bound < maximum + F(3, 10 ** 6)
            if (base, p, q) == (2, 3, 7):
                assert maximum == F(3, 8) and bound == F(11250083, 30000000)

    for base, p, q in ((2, 5, 7), (2, 3, 11), (3, 5, 7)):
        checks = side_parameters(base, p, q), side_parameters(base, q, p)
        assert any(block == 0 or zeros != (u,) for u, block, zeros in checks)
        print(f"({base}, {p}, {q}) fails the one-sheet hypotheses: {checks}")

    # A CRT choice of base exists for every odd prime pair. Check representatives here.
    for p, q in combinations((3, 5, 7, 11, 13, 17, 19), 2):
        for own, other in ((p, q), (q, p)):
            assert any(block and zeros == (u,) for u, block, zeros in (
                side_parameters(1 + own * c, own, other) for c in range(own)
            ))
    print("All Phase 17 Track D checks passed.")


if __name__ == "__main__":
    main()
