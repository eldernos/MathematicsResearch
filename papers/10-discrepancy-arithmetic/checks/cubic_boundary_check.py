#!/usr/bin/env python3
"""Exact finite check of Theorem 6.2(b) on its actual cubic schedule n_k = t k^3.

For each case (b, m, theta) the script builds x = sum_{k>=1} c_k b^(-t k^3) as in the proof:
types are the states 0 and one representative of each cycle of u -> b u on G = {j/m0}, scheduled by the
greedy deficit rule of Lemma 5.2 with exact rational weights, and the positive coefficients c_k come from
the state recurrence of Lemma 2.5.  It asserts 0 < c_k <= 1, den(c_k) | m0 and frac(R_k) = u_k, and then
computes D_N(x) and D_N(mx) exactly (integer arithmetic on a truncation of x whose error is below
b^-80 at the sampled points) and prints (|D_N(x)-delta| + |1-D_N(mx)|) N^(1/3).

This is a finite check, not a proof of the asymptotic statement.  Standard library only.
Usage: python -B papers/10-discrepancy-arithmetic/checks/cubic_boundary_check.py
"""
from fractions import Fraction as F
from math import gcd

BOUND = 10.0  # empirical ceiling for the printed ratio at the sampled N; the theorem asserts only that some C exists


def coprime_part(m, b):
    """The part m_0 of |m| prime to b: strip common factors with b until none remain."""
    m = abs(m)
    while gcd(m, b) > 1:
        m //= gcd(m, b)
    return m


def odd_prime_not_dividing(b):
    p = 3
    while b % p == 0 or any(p % q == 0 for q in range(2, int(p**0.5) + 1)):
        p += 2
    return p


def order_mod(b, p):
    k, v = 1, b % p
    while v != 1:
        v, k = (v * b) % p, k + 1
    return k


def cycles(b, m0):
    seen, out = set(), []
    for j in range(m0):
        if j in seen:
            continue
        cyc, v = [], j
        while v not in seen:
            seen.add(v)
            cyc.append(v)
            v = (v * b) % m0
        out.append(cyc)
    return out


def build(b, m0, theta, t, kmax):
    """Return (states, coeffs, n) for blocks 1..kmax; n[k] = t k^3, n[0] = 0."""
    cyc = cycles(b, m0)
    reps = [F(0)] + [F(c[0], m0) for c in cyc]
    weights = [theta] + [(1 - theta) * F(len(c), m0) for c in cyc]
    assert sum(weights) == 1
    counts = [0] * len(weights)
    n = [t * k**3 for k in range(kmax + 2)]
    u = [F(0)]
    for k in range(1, kmax + 1):
        i = max(range(len(weights)), key=lambda j: (k * weights[j] - counts[j], -j))
        counts[i] += 1
        u.append(reps[i])
    coeffs, R = [None], F(0)
    for k in range(1, kmax + 1):
        target = (u[k] - b ** (n[k] - n[k - 1]) * R) % 1
        c = target if target > 0 else F(1)
        assert 0 < c <= 1, (k, c)
        assert m0 % c.denominator == 0, (k, c, m0)
        R = b ** (n[k] - n[k - 1]) * R + c
        assert R % 1 == u[k], (k, R, u[k])
        coeffs.append(c)
    return u, coeffs, n


def discrepancy(points, S):
    """Extreme discrepancy of integer points p/S in [0,1): maximal excess over half-open circular arcs."""
    N = len(points)
    q = sorted(points)
    q = q + [v + S for v in q]
    best, run = 0, None
    for j, v in enumerate(q):
        cand = N * v - j * S
        run = cand if run is None or cand > run else run
        val = (j + 1) * S - N * v + run
        if val > best:
            best = val
    return F(best, N * S)


def brute_discrepancy(points, S):
    """Direct definition: sup over half-open arcs [a,c) of |count/N - (c-a)|.  Endpoints are the points
    and the points plus an infinitesimal, so that the supremum is read off exactly."""
    N = len(points)
    cuts = sorted(set([0, S] + list(points)))
    ends = [(v, f) for v in cuts for f in (0, 1)]
    best = F(0)
    for a in ends:
        for c in ends:
            if a < c and c[0] <= S and a[0] < S:
                cnt = sum(1 for p in points
                          if (p > a[0] if a[1] else p >= a[0]) and (p <= c[0] if c[1] else p < c[0]))
                best = max(best, abs(F(cnt, N) - F(c[0] - a[0], S)))
    return best


def self_test():
    import random
    random.seed(1)
    for _ in range(200):
        S, N = random.choice((7, 12, 30)), random.randint(1, 7)
        pts = [random.randrange(S) for _ in range(N)]
        assert discrepancy(pts, S) == brute_discrepancy(pts, S), pts


def run_case(b, m, theta, t, kmax, grid):
    m0 = coprime_part(m, b)
    delta = theta + (1 - theta) / m0
    u, coeffs, n = build(b, m0, theta, t, kmax)
    top = n[kmax]
    S = m0 * b**top
    A = sum(c.numerator * (m0 // c.denominator) * b ** (top - n[k]) for k, c in enumerate(coeffs) if k)
    # x_trunc = A / S exactly (denominators of c_k divide m0); the neglected tail changes b^n x by less
    # than b^(n - n[kmax+1]) * b/(b-1)
    worst = 0.0
    rows = []
    for N in grid:
        assert N + 80 <= n[kmax + 1], "increase kmax"
        p, pts = A % S, []
        for _ in range(N):
            pts.append(p)
            p = (b * p) % S
        dx = discrepancy(pts, S)
        dmx = discrepancy([(m * v) % S for v in pts], S)
        err = abs(dx - delta) + abs(1 - dmx)
        ratio = float(err) * N ** (1 / 3)
        worst = max(worst, ratio)
        rows.append((N, float(dx), float(dmx), ratio))
    return m0, delta, rows, worst


def main():
    self_test()
    print("discrepancy() agrees with the direct definition on 200 random small samples")
    cases = [(2, 3, F(0)), (2, 3, F(1, 2)), (2, 6, F(1, 2)), (3, 4, F(0)), (3, 4, F(1, 2)),
             (2, 4, F(0)), (6, 10, F(1, 3)), (10, 21, F(0)), (2, 5, F(1)), (3, 8, F(0))]
    overall = 0.0
    for b, m, theta in cases:
        p = odd_prime_not_dividing(b)
        for t in sorted({1, order_mod(b, p)}):
            kmax = 22 if t == 1 else 12
            top = t * (kmax + 1) ** 3
            grid = sorted({max(1, N) for N in (50, 200, 800, top // 4, top // 2, top - 100) if N + 80 <= top})
            m0, delta, rows, worst = run_case(b, m, theta, t, kmax, grid)
            overall = max(overall, worst)
            print(f"b={b} m={m} m0={m0} theta={theta} delta={delta} t={t}: max ratio {worst:.2f}")
            for N, dx, dmx, ratio in rows:
                print(f"    N={N:6d}  D_N(x)={dx:.4f}  D_N(mx)={dmx:.4f}  err*N^(1/3)={ratio:.2f}")
            assert worst <= BOUND, (b, m, theta, t, worst)
    print(f"all invariants hold (0<c_k<=1, den(c_k)|m0, frac(R_k)=u_k); largest ratio {overall:.2f} <= {BOUND}")


if __name__ == "__main__":
    main()
