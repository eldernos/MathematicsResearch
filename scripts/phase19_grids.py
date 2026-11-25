"""Exact controls for the CRT grid, prefix denominators and missing-prime lemma."""

from fractions import Fraction
from math import gcd, isqrt, lcm


def factor(n):
    """Trial factorization for the small inputs in the controls."""
    result = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            result[d] = result.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        result[n] = 1
    return result


def valuation(n, p):
    assert n > 0
    depth = 0
    while n % p == 0:
        depth += 1
        n //= p
    return depth


def prime_power_order(b, p, e):
    """Remove factors of the Euler exponent by direct modular powering."""
    modulus = p**e
    assert e > 0 and gcd(b, modulus) == 1
    order = modulus // p * (p - 1)
    for r in factor(p - 1) | {p: e}:
        while order % r == 0 and pow(b, order // r, modulus) == 1:
            order //= r
    return order


def order_by_iteration(b, q):
    if q == 1:
        return 1
    assert gcd(b, q) == 1
    residue, period = b % q, 1
    while residue != 1:
        residue = residue * b % q
        period += 1
    return period


def check_cosets():
    cases = 0
    for b, p in [(2, 3), (2, 5), (3, 5), (10, 3), (26, 3)]:
        for Q in range(1, 32):
            if gcd(Q, b * p) != 1:
                continue
            t = lcm(order_by_iteration(b, Q), order_by_iteration(b, p))
            w = valuation(b**t - 1, p)
            for e in range(1, 5):
                q = p**e * Q
                size = p**max(0, e - w)
                stride = q // size
                period = order_by_iteration(b, q)
                assert period == t * size
                for a in {1, q - 1}:
                    # Inspect all consecutive iterates. Each of the t classes must
                    # give exactly its prescribed additive progression.
                    points = []
                    residue = a
                    for _ in range(period):
                        points.append(residue)
                        residue = b * residue % q
                    for i in range(t):
                        assert sorted(points[i::t]) == list(range(points[i] % stride, q, stride))
                    # Oscillation of the empirical CDF minus the identity (two sides).
                    errors = [q * i - period * x for i, x in enumerate(sorted(points))]
                    assert (max(errors) + q - min(errors)) * size <= period * q
                cases += 1
    return cases


def check_prefixes(b, p, limit, position):
    events = {}
    for r in range(2, limit + 1):
        if gcd(r, b) != 1 or any(r % d == 0 for d in range(2, isqrt(r) + 1)):
            continue
        j, u = 1, r
        while u <= limit:
            events[u] = (r, j)
            j += 1
            u *= r
    a, q, prev = 0, 1, 0
    local_orders = {}
    max_loss = 0
    samples = []
    for u, (r, j) in sorted(events.items()):
        n = position(u)
        denom = r ** ((2 if r == p else 1) * j)
        new_q = lcm(q, denom)
        # Shift the previous reduced fraction, then add the new term.
        a = (a * (new_q // q) * pow(b, n - prev, new_q) + new_q // denom) % new_q
        assert gcd(a, new_q) == 1
        q, prev = new_q, n
        local_orders[r] = prime_power_order(b, r, (2 if r == p else 1) * j)
        if r != p:
            max_loss = max(max_loss, valuation(prime_power_order(b, r, 1), p))
        if p not in local_orders:
            continue
        Q_order = lcm(*(order for ell, order in local_orders.items() if ell != p))
        assert valuation(Q_order, p) == max_loss
        d = prime_power_order(b, p, 1)
        v = valuation(b**d - 1, p)
        G = p ** max(0, valuation(q, p) - v - max_loss)
        assert lcm(*local_orders.values()) == lcm(d, Q_order) * G
        if b == 2 and p == 3:
            assert 9 * G > u
        samples.append((u, G))
    return len(events), samples


def check_combined_grid():
    b, q = 2, 3**3 * 5**2
    period = order_by_iteration(b, q)
    orbit = {pow(b, k, q) for k in range(period)}
    sizes = []
    for h in range(1, q + 1):
        if q % h:
            continue
        stable = all((x + q // h) % q in orbit for x in orbit)
        assert stable == (period == h * order_by_iteration(b, q // h))
        if stable:
            sizes.append(h)
    assert sizes == [1, 3, 5, 9, 15, 45]
    return sizes[-1]


def missing_prime_certificate(p, C):
    """A finite congruence certificate for infinitely many exponents k."""
    h = 1
    while p**h <= C:
        h += 1
    divisors = [min(r for r in factor(p**h + m) if r != p) for m in range(1, C + 1)]
    step = lcm(*(prime_power_order(p, r, 1) for r in divisors))
    # k + h is a multiple of step, and each certified divisor is proper.
    k = (1 + (h + max(divisors)) // step) * step - h
    for m, r in enumerate(divisors, 1):
        assert k >= 1 and k >= r
        assert (m * pow(p, k, r) + 1) % r == 0
    return k, step


def finite_prefix_bound(N):
    """Certificate on the genuine binary series for N near 16^11.

    Use only integer event positions and rational error terms. Future positions
    farther away than H contribute at most 2^-H at every retained shift.
    """
    start, H = isqrt(N), N.bit_length()
    assert 16**5 <= start < 16**7 and 16**9 <= N < 16**13 - H
    events = [(3, 3, 2), (5, 5, 1), (7, 7, 1), (9, 3, 4), (11, 11, 1)]
    depths = {}
    mesh = Fraction(0)
    remainder = 0
    for i, (label, p, e) in enumerate(events):
        depths[p] = e
        left = max(start, 16**label)
        right = min(N, 16**events[i + 1][0] if i + 1 < len(events) else N)
        if right <= left:
            continue
        orders = {r: order_by_iteration(2, r**f) for r, f in depths.items()}
        t = lcm(2, *(o for r, o in orders.items() if r != 3))
        size = 3**max(0, depths[3] - valuation(2**t - 1, 3))
        period = lcm(*orders.values())
        length = right - left
        mesh += Fraction(length, size)
        remainder += length % period
    guards = sum(max(0, min(N, 16**u) - max(start, 16**u - H)) for u, _, _ in events)
    return (start + guards + remainder + mesh) / N + Fraction(2, 2**H)


if __name__ == "__main__":
    print(f"CRT cosets, whole periods and exact discrepancy: {check_cosets()} parameter cases")
    print(f"Combined grid on modulus 675: {check_combined_grid()} points")
    for b, p in [(2, 3), (3, 5), (10, 3)]:
        count, samples = check_prefixes(b, p, 512, lambda u: 16**u)
        print(f"b={b}, p={p}: {count} exact insertion denominators; final (label, G)={samples[-1]}")
    assert prime_power_order(2, 31, 1) == 5 and 3 in factor(31 - 1)
    for C in (3, 9, 27):
        k, step = missing_prime_certificate(3, C)
        print(f"No prime m*3^k+1 for 1<=m<={C} when k={k}+{step}j, j>=0")
    for delta in (-1, 0, 1, 37):
        N = 16**11 + delta
        bound = finite_prefix_bound(N)
        assert bound < Fraction(1, 8)
        print(f"N=16^11{delta:+d}: certified D_N <= {bound} < 1/8")
