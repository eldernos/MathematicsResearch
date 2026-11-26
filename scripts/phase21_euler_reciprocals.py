#!/usr/bin/env python3
"""Exact and certified checks for Phase 21 Track D, sub-tracks D1 and D2.

D1a  (a/d)E_b: the residue automaton over (k mod L, I mod d), its period, the exact
     rational limit law mu on (1/d)Z/Z and the rational limit D_inf = D*(mu); the
     finite inequality |D_N - D*(mu)| <= TV_N + beta_N + 2 eta_N at every checkpoint.
D1b  (a/d)E_b^3: the same automaton for Jacobi's cube, non-membership in K_b.
D1c  (a/d)E_b^2: E(q)^2 = E(q^2) mod 2, the exact limit 2/3 of D_N(E_b^2/2; b) for odd b
     (residue law exact, tails measured), and finite observations for odd d.
D2   x = prod (1 - b^-m_k) with ord_{D_k}(b) | m_{k+1}: the band identity, exact vanishing
     of the cycle Fourier coefficients, the window Weyl-sum bound, certified D_N(1/x)
     and 1 - D_N(x); the contrast x' = prod (1 + b^-m_k).

Standard library only.  Orbit points are computed from exact integer residues plus an
integer window of W digits; the neglected tail is bounded explicitly and every
discrepancy is within that bound (below 1e-12) of the exact finite value.

Run from the repository root:  python -B scripts/phase21_euler_reciprocals.py
"""

from __future__ import annotations

import cmath
import math
from fractions import Fraction
from math import gcd
from time import perf_counter

CHECKS = [0]


def check(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)
    CHECKS[0] += 1


def header(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------- arithmetic helpers

def factorize(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def order_mod(b, d, multiple=None):
    """Multiplicative order of b modulo d (gcd(b, d) = 1).  `multiple` is a known
    exponent with b^multiple = 1 mod d; otherwise d is small and we search."""
    if d == 1:
        return 1
    if multiple is None:
        x, k = b % d, 1
        while x != 1:
            x = x * b % d
            k += 1
        return k
    check(pow(b, multiple, d) == 1, "claimed multiple of the order")
    order = multiple
    for p in factorize(multiple):
        while order % p == 0 and pow(b, order // p, d) == 1:
            order //= p
    return order


def lcm(a, b):
    return a // gcd(a, b) * b


# ---------------------------------------------------------------- discrepancies

def discrepancy(values):
    """Extreme (interval) discrepancy of a finite point set in [0, 1)."""
    ordered = sorted(values)
    count = len(ordered)
    high = 0.0
    low = 0.0
    for i, y in enumerate(ordered):
        upper = (i + 1) / count - y
        if upper > high:
            high = upper
        lower = i / count - y
        if lower < low:
            low = lower
    return high - low


def atomic_discrepancy(weights):
    """D*(mu) for mu = sum w_j delta_{j/d}: the sup over closed atom arcs of
    (mass - length) and over open atom arcs of (length - mass).  Exact if the
    weights are Fractions."""
    d = len(weights)
    zero = weights[0] * 0
    best = zero
    for i in range(d):
        s = zero
        for l in range(d):
            s += weights[(i + l) % d]
            val = s - Fraction(l, d) if isinstance(s, Fraction) else s - l / d
            if val > best:
                best = val
        s = zero
        for l in range(1, d + 1):
            if l >= 2:
                s += weights[(i + l - 1) % d]
            val = Fraction(l, d) - s if isinstance(s, Fraction) else l / d - s
            if val > best:
                best = val
    return best


def orbit_measure(c, b, d, a=1):
    """Uniform probability on {a c b^i mod d}, as a list of Fractions indexed by Z/d."""
    pts = []
    x = c % d
    while True:
        pts.append(x)
        x = x * b % d
        if x == c % d:
            break
    w = [Fraction(0)] * d
    for x in pts:
        w[a * x % d] += Fraction(1, len(pts))
    return w


# ---------------------------------------------------------------- the series

def pentagonal_insertions(limit, scale=1):
    """[(position, sign)] for E(q^scale) = 1 + sum_k (-1)^k (q^{P_k^-} + q^{P_k^+}),
    positions <= limit, in increasing order (position 0 has sign +1)."""
    out = [(0, 1)]
    k = 1
    while True:
        lo = scale * (k * (3 * k - 1) // 2)
        if lo > limit:
            break
        s = -1 if k % 2 else 1
        out.append((lo, s))
        hi = scale * (k * (3 * k + 1) // 2)
        if hi <= limit:
            out.append((hi, s))
        k += 1
    return out


def cube_insertions(limit):
    """[(T_k, (-1)^k (2k+1))] for E(q)^3 (Jacobi)."""
    out = []
    k = 0
    while k * (k + 1) // 2 <= limit:
        out.append((k * (k + 1) // 2, (-1) ** k * (2 * k + 1)))
        k += 1
    return out


def dense(insertions, limit):
    c = [0] * (limit + 1)
    for p, s in insertions:
        if p <= limit:
            c[p] += s
    return c


def square_coefficients(limit):
    """a_2(n), n <= limit, by the pentagonal pair convolution (O(limit) pairs)."""
    ins = pentagonal_insertions(limit)
    c = [0] * (limit + 1)
    for p, s in ins:
        for q, t in ins:
            if p + q > limit:
                break
            c[p + q] += s * t
    return c


# ---------------------------------------------------------------- D1 automata

def euler_automaton(b, d, a=1, scale=1):
    """Limit law of {b^n (a/d) E(b^-scale)} for gcd(d, b) = 1, d >= 2, gcd(a, d) = 1.

    State u_k^+ = I(scale P_k^+) mod d (u_0^+ = 1).  Transition k-1 -> k:
        u_k^- = b^{scale(2k-1)} u_{k-1}^+ + (-1)^k,   u_k^+ = b^{scale k} u_k^- + (-1)^k.
    The run after scale P_k^- has length scale*k and after scale P_k^+ length
    scale*(2k+1): asymptotic weights 1/3 and 2/3, equal over classes of k mod P.
    Returns (P, L, weights, D*)."""
    t = order_mod(b, d)
    L = lcm(2, t)
    sgn = lambda k: -1 if k % 2 else 1
    u = 1
    minus, plus = [], []
    k = 0
    while True:
        k += 1
        um = (pow(b, scale * (2 * k - 1), d) * u + sgn(k)) % d
        u = (pow(b, scale * k, d) * um + sgn(k)) % d
        minus.append(um)
        plus.append(u)
        if k % L == 0 and u == 1:
            break
    P = k
    w = [Fraction(0)] * d
    for um, up in zip(minus, plus):
        om = orbit_measure(um, b, d, a)
        op = orbit_measure(up, b, d, a)
        for j in range(d):
            w[j] += Fraction(1, 3 * P) * om[j] + Fraction(2, 3 * P) * op[j]
    return P, L, w, atomic_discrepancy(w)


def cube_automaton(b, d, a=1):
    """Limit law of {b^n (a/d) E_b^3}: v_0 = 1, v_k = b^k v_{k-1} + (-1)^k (2k+1) mod d,
    run after T_k of length k+1, equal weights over classes of k mod P."""
    t = order_mod(b, d)
    L = lcm(t, 2 * d)
    v = 1
    states = []
    k = 0
    while True:
        k += 1
        v = (pow(b, k, d) * v + (-1) ** k * (2 * k + 1)) % d
        states.append(v)
        if k % L == 0 and v == 1:
            break
    P = k
    w = [Fraction(0)] * d
    for v in states:
        o = orbit_measure(v, b, d, a)
        for j in range(d):
            w[j] += Fraction(1, P) * o[j]
    return P, L, w, atomic_discrepancy(w)


# ---------------------------------------------------------------- certified orbits

def orbit_with_atoms(coef, positions, b, a, d, N, W, R):
    """Samples x_n = {b^n a F / d}, F = sum coef[m] b^-m, n < N, from the exact residue
    I_n mod d and the integer window T_n = sum_{n<m<=n+W} coef[m] b^{n+W-m}.
    Also returns, for each n, the atom (a I_n mod d) and whether n is good (no
    insertion in (n, n+R)).  coef must have length >= N + W + 2."""
    bW = b ** W
    mod = d * bW
    top = b ** (W - 1)
    I = coef[0] % d
    T = 0
    for m in range(1, W + 1):
        T = T * b + coef[m]
    xs = [0.0] * N
    atoms = [0] * N
    good = [False] * N
    nxt = 0
    pos = positions
    npos = len(pos)
    for n in range(N):
        while nxt < npos and pos[nxt] <= n:
            nxt += 1
        r = pos[nxt] - n if nxt < npos else 10 ** 9
        xs[n] = ((a * (I * bW + T)) % mod) / mod
        atoms[n] = a * I % d
        good[n] = r >= R
        I = (I * b + coef[n + 1]) % d
        T = (T - coef[n + 1] * top) * b + coef[n + W + 1]
    return xs, atoms, good


def tail_bound(c_const, b, W, sqrt_growth=False, n_max=0):
    """Analytic upper bound on sum_{j > W} |c(n + j)| b^{-j} for 0 <= n < n_max.
    If sqrt_growth is False, uses global |c(m)| <= c_const; if True, uses global
    |c(m)| <= c_const * sqrt(m + 1) via sqrt(n + W + 1 + t) <= sqrt(n_max + W + 2) * (1 + t)."""
    if not sqrt_growth:
        return c_const * b ** (-W) * b / (b - 1)
    # sum_{t >= 0} (1 + t) b^{-(W + 1 + t)} = b^{-W} * b / (b - 1)^2
    return c_const * math.sqrt(n_max + W + 2) * b ** (-W) * b / ((b - 1) ** 2)


def certified_limit_check(label, coef, positions, b, a, d, weights, Dstar, Ns, W,
                          c_const=1.0, sqrt_growth=False):
    """Check |D_N - D*| <= TV_N + beta_N + 2 eta_N + slack at the given checkpoints."""
    Nmax = max(Ns)
    c_eff = c_const * math.sqrt(Nmax + W + 2) if sqrt_growth else c_const
    R = math.ceil(math.log(max(2, abs(a)) * c_eff * Nmax * 4, b)) + 1
    xs, atoms, good = orbit_with_atoms(coef, positions, b, a, d, Nmax, W, R)
    eta = abs(a) * tail_bound(c_const, b, R - 1, sqrt_growth=sqrt_growth, n_max=Nmax) / d
    slack = 4 * abs(a) * tail_bound(c_const, b, W, sqrt_growth=sqrt_growth, n_max=Nmax) / d + 1e-12
    wf = [float(x) for x in weights]
    rows = []
    for N in Ns:
        D = discrepancy(xs[:N])
        cnt = [0] * d
        bad = 0
        for n in range(N):
            if good[n]:
                cnt[atoms[n]] += 1
            else:
                bad += 1
        tv = sum(abs(cnt[j] / N - wf[j]) for j in range(d))
        beta = bad / N
        err = abs(D - float(Dstar))
        bound = tv + beta + 2 * eta + slack
        check(err <= bound, f"{label}: |D_N - D*| <= TV + beta + 2 eta at N={N}")
        rows.append((N, D, err, tv, beta, err * math.sqrt(N) / math.log(N, b)))
    return rows


def fmt_measure(w):
    return ", ".join(f"{j}:{w[j]}" for j in range(len(w)) if w[j])


# ================================================================ D1a  (a/d) E_b

D1_CASES = [(2, 3), (2, 5), (2, 7), (2, 9), (2, 15), (3, 2), (3, 4), (3, 5), (3, 7),
            (10, 3), (10, 7), (5, 2), (7, 2), (2, 11), (3, 8)]


def section_d1a():
    header("D1a  rational multiples of Euler's product: residue automaton and limits")
    results = {}
    print(f"{'b':>3} {'d':>3} {'a':>3} {'P':>5} {'D_inf':>12}  law (atom j/d : weight)")
    for b, d in D1_CASES:
        for a in range(1, d):
            if gcd(a, d) != 1:
                continue
            P, L, w, Ds = euler_automaton(b, d, a)
            check(sum(w) == 1, "law has total mass one")
            check(Ds < 1, f"E_{b}*{a}/{d} not in K_b (D* < 1)")
            check(Ds >= Fraction(1, d), "D* >= 1/d for a law on (1/d)Z/Z")
            # invariance of the law under x -> b x
            check(all(w[j] == w[j * b % d] for j in range(d)), "law is xb-invariant")
            results[(b, d, a)] = (P, w, Ds)
            if a <= 2 or d <= 5:
                print(f"{b:>3} {d:>3} {a:>3} {P:>5} {str(Ds):>12}  {fmt_measure(w)}")
    # Phase 20 baselines
    check(results[(2, 3, 1)][2] == Fraction(1, 2), "D_inf(E_2/3) = 1/2")
    check(results[(2, 3, 1)][1] == [Fraction(1, 6), Fraction(5, 12), Fraction(5, 12)],
          "law of E_2/3 is 1/6, 5/12, 5/12")
    check(results[(3, 2, 1)][2] == Fraction(2, 3), "D_inf(E_3/2) = 2/3")
    for b in (3, 5, 7):
        check(results[(b, 2, 1)][1] == [Fraction(1, 3), Fraction(2, 3)], "odd b, d = 2")
    # Corollary D1.2: d = p prime, b a primitive root mod p: law w delta_0 + u (units),
    # D* = max(w, u, 2/p - w, (p-1)/p - (p-2) u)
    print("  primitive-root primes: D* = max(w0, u, 2/p - w0, (p-1)/p - (p-2)u)")
    for b, p in ((2, 3), (2, 5), (2, 11), (2, 13), (2, 19), (3, 2), (3, 5), (3, 7),
                 (10, 7), (10, 17), (5, 3), (7, 2)):
        check(order_mod(b, p) == p - 1, "primitive root")
        for law_fn in (euler_automaton, cube_automaton):
            P, L, w, Ds = law_fn(b, p)
            w0 = w[0]
            u = (1 - w0) / (p - 1)
            check(all(w[j] == u for j in range(1, p)), "uniform on units")
            formula = max(w0, u, Fraction(2, p) - w0, Fraction(p - 1, p) - (p - 2) * u)
            check(formula == Ds, f"closed form D* for ({b},{p}) {law_fn.__name__}")
        print(f"    b={b:>2} p={p:>2}: w0(E) = {euler_automaton(b, p)[2][0]},"
              f" w0(E^3) = {cube_automaton(b, p)[2][0]}")
    # dependence on the numerator a
    da = {a: results[(2, 7, a)][2] for a in range(1, 7)}
    print("  D_inf(a E_2/7) for a = 1..6:", ", ".join(str(da[a]) for a in range(1, 7)))
    check(results[(2, 7, 3)][2] == results[(2, 7, 4)][2], "a and -a give the same D_inf")
    # radix-primary factor: (a / (d0 d1)) E_b has the limit of (a b^e / d0 mod d1)/d1
    # (shift by e changes D_N by at most 2e/N); spot check b=2, a/d = 1/12 -> 1/3.
    coefs = dense(pentagonal_insertions((1 << 13) + 80), (1 << 13) + 80)
    pos = [p for p, _ in pentagonal_insertions((1 << 13) + 80)]
    xs12 = orbit_with_atoms(coefs, pos, 2, 1, 12, 1 << 13, 60, 30)[0]
    xs3 = orbit_with_atoms(coefs, pos, 2, 1, 3, (1 << 13) + 2, 60, 30)[0]
    check(all(abs(xs12[n + 2] - xs3[n]) < 1e-12 for n in range((1 << 13) - 2)),
          "{2^(n+2) E_2/12} = {2^n E_2/3}")
    # certified finite convergence
    print()
    print("  certified |D_N - D_inf| <= TV_N + beta_N + 2 eta_N  (beta = near-insertion share)")
    print(f"  {'case':>12} {'N':>7} {'D_N':>9} {'|D_N-D*|':>9} {'TV_N':>8} {'beta_N':>8}"
          f" {'err*sqrtN/logN':>15}")
    Ns = [1 << 12, 1 << 14, 1 << 16]
    lim = max(Ns) + 120
    for b, d, a in [(2, 3, 1), (2, 5, 1), (2, 7, 1), (2, 7, 3), (3, 2, 1), (3, 4, 1),
                    (3, 7, 1), (10, 3, 1), (10, 7, 1)]:
        ins = pentagonal_insertions(lim)
        coef = dense(ins, lim)
        W = math.ceil(60 / math.log2(b))
        P, w, Ds = results[(b, d, a)]
        rows = certified_limit_check(f"E_{b}*{a}/{d}", coef, [p for p, _ in ins], b, a, d,
                                     w, Ds, Ns, W)
        for N, D, err, tv, beta, ratio in rows:
            print(f"  {f'{a}E_{b}/{d}':>12} {N:>7} {D:9.6f} {err:9.6f} {tv:8.5f} {beta:8.5f}"
                  f" {ratio:15.3f}")
        check(rows[-1][2] < rows[0][2] or rows[-1][2] < 0.01, "error decreases")
    return results


# ================================================================ D1b  (a/d) E_b^3

def section_d1b(res1):
    header("D1b  rational multiples of Jacobi's cube E_b^3")
    print(f"{'b':>3} {'d':>3} {'a':>3} {'P':>6} {'D_inf(E^3)':>14} {'D_inf(E)':>12}  law of a E^3/d")
    out = {}
    for b, d in D1_CASES:
        for a in range(1, d):
            if gcd(a, d) != 1:
                continue
            P, L, w, Ds = cube_automaton(b, d, a)
            check(sum(w) == 1, "cube law mass one")
            check(Ds < 1, f"E_{b}^3*{a}/{d} not in K_b")
            check(all(w[j] == w[j * b % d] for j in range(d)), "cube law xb-invariant")
            out[(b, d, a)] = (P, w, Ds)
            if a <= 2 or d <= 5:
                print(f"{b:>3} {d:>3} {a:>3} {P:>6} {str(Ds):>14} {str(res1[(b, d, a)][2]):>12}"
                      f"  {fmt_measure(w) if d <= 9 else ''}")
    # the non-membership mechanism: a stable residue survives T_k only if d | 2k+1,
    # which fixes k in one class mod d (d odd) or never happens (d even)
    for d in (2, 3, 4, 5, 7, 9, 15):
        cls = [k for k in range(d) if (2 * k + 1) % d == 0]
        check(len(cls) == (1 if d % 2 else 0), "d | 2k+1 for at most one class of k mod d")
    # dependence on the numerator a (cases where (Z/d)^x has several <b>-cosets)
    for b, d, n_expected in ((2, 17, 2), (2, 31, 3), (10, 11, 5), (5, 13, 3)):
        vals = {euler_automaton(b, d, a)[3] for a in range(1, d)}
        check(len(vals) == n_expected, f"number of distinct D_inf(a E_{b}/{d})")
        print(f"  b={b}, d={d}: D_inf(a E_b/d) takes {len(vals)} values: "
              + ", ".join(str(v) for v in sorted(vals)))
    # verify the uniform cube cases cited in §3
    for b, d in ((2, 7), (2, 31), (2, 73), (3, 13), (2, 23)):
        _, _, w_u, Ds_u = cube_automaton(b, d, 1)
        check(all(wj == Fraction(1, d) for wj in w_u) and Ds_u == Fraction(1, d),
              f"uniform cube law for ({b},{d})")
    print()
    print("  certified finite convergence for the cube")
    Ns = [1 << 12, 1 << 14, 1 << 16]
    lim = max(Ns) + 120
    for b, d, a in [(2, 3, 1), (2, 5, 1), (3, 2, 1), (3, 4, 1), (10, 3, 1)]:
        ins = cube_insertions(lim)
        coef = dense(ins, lim)
        W = math.ceil(80 / math.log2(b))
        P, w, Ds = out[(b, d, a)]
        # Analytic bound for Jacobi's cube: |c(m)| <= 2*sqrt(2*m) + 1 <= 4*sqrt(m + 1)
        rows = certified_limit_check(f"E_{b}^3*{a}/{d}", coef, [p for p, _ in ins], b, a, d,
                                     w, Ds, Ns, W, c_const=4.0, sqrt_growth=True)
        for N, D, err, tv, beta, ratio in rows:
            print(f"  {f'{a}E_{b}^3/{d}':>12} {N:>7} {D:9.6f} {err:9.6f} {tv:8.5f} {beta:8.5f}"
                  f" {ratio:15.3f}")
    return out


# ================================================================ D1c  (a/d) E_b^2

def spf_sieve(limit):
    spf = list(range(limit + 1))
    p = 2
    while p * p <= limit:
        if spf[p] == p:
            for q in range(p * p, limit + 1, p):
                if spf[q] == q:
                    spf[q] = p
        p += 1
    return spf


def tail_good_check(label, coef, b, a, d, weights, Dstar, Ns, W, eta):
    """Version of the finite inequality where n is good when its exact window tail
    satisfies |a t_n / d| <= eta - (analytic truncation bound for E_b^2: |a_2(m)| <= 4*sqrt(m+1))."""
    Nmax = max(Ns)
    trunc = abs(a) * tail_bound(4.0, b, W, sqrt_growth=True, n_max=Nmax) / d
    bW = b ** W
    mod = d * bW
    top = b ** (W - 1)
    I = coef[0] % d
    T = 0
    for m in range(1, W + 1):
        T = T * b + coef[m]
    xs = [0.0] * Nmax
    atoms = [0] * Nmax
    good = [False] * Nmax
    lim = (eta - trunc) * d * bW / max(1, abs(a))
    for n in range(Nmax):
        xs[n] = ((a * (I * bW + T)) % mod) / mod
        atoms[n] = a * I % d
        good[n] = abs(T) <= lim
        I = (I * b + coef[n + 1]) % d
        T = (T - coef[n + 1] * top) * b + coef[n + W + 1]
    wf = [float(x) for x in weights]
    rows = []
    for N in Ns:
        D = discrepancy(xs[:N])
        cnt = [0] * d
        for n in range(N):
            if good[n]:
                cnt[atoms[n]] += 1
        beta = 1 - sum(cnt) / N
        tv = sum(abs(cnt[j] / N - wf[j]) for j in range(d))
        err = abs(D - float(Dstar))
        check(err <= tv + beta + 2 * eta + 2 * trunc + 1e-12,
              f"{label}: finite inequality at N={N}")
        law = [cnt[j] / max(1, sum(cnt)) for j in range(d)]
        rows.append((N, D, err, tv, beta, law))
    return rows


def section_d1c():
    header("D1c  rational multiples of Euler's square E_b^2")
    LIM = 20000
    a2 = square_coefficients(LIM)
    ins2 = pentagonal_insertions(LIM, scale=2)
    e_q2 = dense(ins2, LIM)
    check(all((a2[n] - e_q2[n]) % 2 == 0 for n in range(LIM + 1)),
          "E(q)^2 = E(q^2) mod 2 through q^20000")
    print("  E(q)^2 = E(q^2) (mod 2) checked through q^20000")
    for b in (3, 5, 7, 9, 11):
        P, L, w, Ds = euler_automaton(b, 2, 1, scale=2)
        check(w == [Fraction(1, 3), Fraction(2, 3)] and Ds == Fraction(2, 3),
              f"E(b^-2)/2 has law (1/3, 2/3) and D* = 2/3, b = {b}")
    print("  law of {b^n E(b^-2)/2}: 1/3 at 0, 2/3 at 1/2, D* = 2/3 for b = 3,5,7,9,11")

    # the residue sequences of E_b^2 and E(b^-2) agree mod 2 exactly
    Nmax = 1 << 17
    W = 50
    a2 = square_coefficients(Nmax + W + 2)
    e2 = dense(pentagonal_insertions(Nmax + W + 2, scale=2), Nmax + W + 2)
    I1 = I2 = 1
    same = True
    for n in range(1, Nmax):
        I1 = (I1 * 3 + a2[n]) % 2
        I2 = (I2 * 3 + e2[n]) % 2
        same &= I1 == I2
    check(same, "I_n(E_3^2) = I_n(E(3^-2)) mod 2 for n < 2^17")

    print()
    print("  d = 2, b = 3: D_N(E_3^2/2; 3) -> 2/3 (theorem); finite values")
    print(f"  {'N':>7} {'D_N':>9} {'|D_N-2/3|':>10} {'tail share':>11} {'atom law (good n)':>20}")
    Ns = [1 << 12, 1 << 14, 1 << 16, 1 << 17]
    rows = tail_good_check("E_3^2/2", a2, 3, 1, 2, [Fraction(1, 3), Fraction(2, 3)],
                           Fraction(2, 3), Ns, 34, 0.02)
    for N, D, err, tv, beta, law in rows:
        print(f"  {N:>7} {D:9.6f} {err:10.6f} {beta:11.5f}   ({law[0]:.4f}, {law[1]:.4f})")
    check(abs(rows[-1][5][0] - 1 / 3) < 0.02, "good-n atom law near (1/3, 2/3)")

    print()
    print("  odd d (status open for the exact limit; non-membership is Theorem D1.5)")
    print(f"  {'case':>10} {'N':>7} {'D_N':>9} {'1/d':>7} {'tail share':>11}  atom law of good n")
    for b, d in [(2, 3), (2, 5), (3, 5), (2, 7)]:
        W = math.ceil(60 / math.log2(b))
        coef = square_coefficients((1 << 16) + W + 2)
        unif = [Fraction(1, d)] * d
        rows = tail_good_check(f"E_{b}^2/{d}", coef, b, 1, d, unif, Fraction(1, d),
                               [1 << 14, 1 << 16], W, 0.02)
        for N, D, err, tv, beta, law in rows:
            print(f"  {f'E_{b}^2/{d}':>10} {N:>7} {D:9.5f} {1 / d:7.4f} {beta:11.5f}  "
                  + " ".join(f"{x:.3f}" for x in law))

    # alternation functional for the effective support S_l = {n: a_2(n) != 0 mod l}
    print()
    print("  effective-support alternation sum_i min(G_i, G_{i+1}) / N  (Theorem D1.5 needs")
    print("  a positive lower bound; here l = 3, 5, 7)")
    X = 1 << 17
    coef = square_coefficients(X)
    for ell in (3, 5, 7):
        S = [n for n in range(1, X + 1) if coef[n] % ell]
        gaps = [S[i + 1] - S[i] for i in range(len(S) - 1)]
        alt = sum(min(gaps[i], gaps[i + 1]) for i in range(len(gaps) - 1)) / X
        print(f"    l = {ell}:  |S_l cap [1,2^17]| = {len(S)}, alternation = {alt:.4f}")
        check(alt > 0.2, "alternation functional bounded away from 0 at 2^17")
    # S' (split part squarefree, non-split part a square) lies in S_l for odd l
    Y = 1 << 15
    spf = spf_sieve(12 * Y + 1)
    count_sp = 0
    for n in range(1, Y + 1):
        m = 12 * n + 1
        ok = True
        while m > 1:
            p = spf[m]
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p % 12 == 1:
                ok &= e == 1
            else:
                ok &= e % 2 == 0
        if ok:
            count_sp += 1
            check(coef[n] % 3 and coef[n] % 5 and coef[n] % 7,
                  "a_2(n) = +-2^w on S', nonzero mod odd l")
    print(f"    |S' cap [1,2^15]| = {count_sp},  ratio * (log X)^(3/4) / X = "
          f"{count_sp * math.log(Y) ** 0.75 / Y:.4f}")


# ================================================================ D2  normal reciprocals

def build_construction(b, ms, sign=-1):
    """R_k = prod_{j<=k} 1/(1 + sign b^-m_j); returns [(m_k, R_k, D_k, T_k)].
    For sign = -1 the band identity gives T_k | m_k D_{k-1}; for sign = +1, T_k | 2 m_k D_{k-1}."""
    R = Fraction(1)
    out = []
    for m in ms:
        if out:
            check(m % out[-1][3] == 0, "admissibility T_{k-1} | m_k")
        R = R * Fraction(b ** m, b ** m + sign)
        D = R.denominator
        check(gcd(D, b) == 1, "D_k coprime to b")
        prev = out[-1][2] if out else 1
        mult = m * prev * (2 if sign == 1 else 1)
        T = order_mod(b, D, mult)
        out.append((m, R, D, T))
    return out


def band_identity_holds(b, n, RK, Rprev, m, sign=-1):
    i, r = divmod(n, m)
    if sign == -1:
        main = (i + 1) * Fraction(b) ** r * Rprev
        tail = Fraction(b) ** r * Rprev / (b ** m - 1)
    else:
        main = (1 if i % 2 == 0 else 0) * Fraction(b) ** r * Rprev
        tail = (-1) ** (i + 1) * Fraction(b) ** r * Rprev / (b ** m + 1)
    diff = Fraction(b) ** n * RK - main - tail
    return diff.denominator == 1


def cycle_fourier(b, R, T, k):
    A, D = R.numerator, R.denominator
    s = 0j
    x = A % D
    for _ in range(T):
        s += cmath.exp(2j * math.pi * k * x / D)
        x = x * b % D
    return s / T


def fractional_bits(R, total):
    """Binary digits 1..total of the fractional part of R (exact)."""
    V = (R.numerator << total) // R.denominator
    return bin(V & ((1 << total) - 1))[2:].zfill(total)


def orbit_from_bits(bits, N, W):
    xs = [0.0] * N
    mask = (1 << W) - 1
    w = int(bits[:W], 2)
    scale = float(1 << W)
    for n in range(N):
        xs[n] = w / scale
        w = ((w << 1) & mask) | (bits[n + W] == "1")
    return xs


def section_d2():
    header("D2  an irrational x in K_b whose reciprocal is base-b normal")
    b = 2
    T3 = build_construction(b, [2, 4, 48])[-1][3]
    m4 = 20 * T3
    con = build_construction(b, [2, 4, 48, m4])
    print("  b = 2, admissible prefix (T_{k-1} | m_k):")
    for k, (m, R, D, T) in enumerate(con, 1):
        dstr = str(D) if D < 10 ** 18 else f"~2^{D.bit_length()}"
        print(f"    k={k}: m_k = {m:>6}   D_k = {dstr:>20}   T_k = ord_(D_k)(2) = {T}")
    check([c[3] for c in con[:3]] == [2, 12, 2160], "orders 2, 12, 2160")
    for k in range(1, len(con)):
        check(con[k][2] * 4 * con[k - 1][2] >= b ** con[k][0] - 1, "D_k growth inequality")
    # band identity, exactly (rational arithmetic)
    for K in (1, 2):
        m, RK = con[K][0], con[K][1]
        Rprev = con[K - 1][1]
        ns = list(range(0, 3 * m + 7)) + [7 * m + 1, 50 * m - 1]
        check(all(band_identity_holds(b, n, RK, Rprev, m) for n in ns),
              f"band identity for R_{K + 1}")
    m4_, R4 = con[3][0], con[3][1]
    for n in (m4_ - 1, m4_, 3 * m4_ + 17, 11 * m4_ + 1234):
        check(band_identity_holds(b, n, R4, con[2][1], m4_), "band identity for R_4")
    print("  band identity  b^n R_K = (i+1) b^r R_{K-1} + b^r R_{K-1}/(b^m_K - 1)  (mod 1): ok")
    # exact vanishing of cycle Fourier coefficients
    for K, Dprev in ((2, con[1][2]), (1, con[0][2])):
        _, R, D, T = con[K]
        for k in range(1, 3 * Dprev + 1):
            if k % Dprev:
                check(abs(cycle_fourier(b, R, T, k)) < 1e-9,
                      f"C_{K + 1}({k}) = 0 when D_{K} does not divide k")
    print("  cycle Fourier coefficients: C_3(k) = 0 unless 45 | k (k <= 135); "
          "C_2(k) = 0 unless 3 | k: ok")

    # orbit of y = 1/x: equals the orbit of R_4 to within 2^-W on n < 2^19
    Nmax = 1 << 19
    W = 52
    t0 = perf_counter()
    ys = orbit_from_bits(fractional_bits(R4, Nmax + W + 1), Nmax, W)
    H = [1, 2, 3, 5, 9, 45]
    cums = {}
    for h in H:
        acc = 0j
        arr = [0j] * Nmax
        tw = 2j * math.pi * h
        for n in range(Nmax):
            acc += cmath.exp(tw * ys[n])
            arr[n] = acc
        cums[h] = arr

    def window_bound(N, h):
        K = 4 if N >= con[3][0] else 3
        mK = con[K - 1][0]
        Dpp = con[K - 3][2]
        Tprev = con[K - 2][3]
        Rp = float(con[K - 2][1])
        I, r0 = divmod(N, mK)
        cnt = sum(1 for a in range(1, I + 1) if (h * a) % Dpp == 0)
        ind = 1 if (h * (I + 1)) % Dpp == 0 else 0
        e_eta = sum(min(2.0, 2 * math.pi * h * Rp * b ** (r - mK) / (1 - b ** (-mK)))
                    for r in range(mK))
        e_y = (sum(min(2.0, 2 * math.pi * h * 8.0 * b ** (n - m4)) for n in range(N))
               if K == 3 else 0.0)
        e_w = N * 2 * math.pi * h * 2.0 ** (1 - W)
        return mK * cnt + r0 * ind + (I + 1) * e_eta + Tprev + e_y + e_w

    print()
    print("  |W_h(N)| for {2^n/x}; every value is checked against the proved window bound")
    print(f"  {'N':>8} {'win':>4} " + " ".join(f"{'h=' + str(h):>8}" for h in H)
          + f" {'D_N(1/x)':>9}")
    for N in [300, 1000, 5000, 20000, 43199, 43200, 60000, 100000, 200000, 400000, Nmax]:
        vals = []
        for h in H:
            S = abs(cums[h][N - 1])
            check(S <= window_bound(N, h) + 1e-6, f"window bound h={h} N={N}")
            vals.append(S / N)
        DN = discrepancy(ys[:N])
        print(f"  {N:>8} {4 if N >= m4 else 3:>4} " + " ".join(f"{v:8.5f}" for v in vals)
              + f" {DN:9.5f}")
    for N in (100000, 400000, Nmax):
        for h in (1, 2):
            check(window_bound(N, h) / N < 0.12, "window-4 bound below 0.12")
    check(discrepancy(ys) < 0.06, "D_N(1/x) < 0.06 at N = 2^19 (window 4)")

    # x itself: 1 - D_N(x) <= 2/N + (w+1) #support/N
    X4 = Fraction(1)
    for m, _, _, _ in con:
        X4 *= 1 - Fraction(1, b ** m)
    xs = orbit_from_bits(fractional_bits(X4, Nmax + W + 1), Nmax, W)
    sums = {0}
    for m, _, _, _ in con:
        sums |= {s + m for s in sums}
    print()
    print(f"  x = prod (1 - 2^-m_k): subset-sum support {sorted(sums)[:6]} ... ({len(sums)} points)")
    for N in (1 << 12, 1 << 16, Nmax):
        w = math.ceil(2 * math.log2(N + 2)) + 1
        supp = sum(1 for s in sums if 0 < s <= N + w)
        bound = 2 / N + (w + 1) * supp / N
        deficit = 1 - discrepancy(xs[:N])
        check(deficit <= bound + 1e-12, "1 - D_N(x) <= 2/N + (w+1) S(N+w)/N")
        print(f"    N = {N:>7}:  1 - D_N(x) = {deficit:.3e}   bound {bound:.3e}")
    print(f"  (orbits and Weyl sums: {perf_counter() - t0:.1f} s)")

    # base 3: identities only
    con3 = build_construction(3, [2, 4, 64])
    check([c[3] for c in con3] == [2, 32, 40960], "base-3 orders")
    for n in list(range(0, 300, 11)) + [63, 64, 1000]:
        check(band_identity_holds(3, n, con3[2][1], con3[1][1], 64), "base-3 band identity")
    for k in range(1, 3 * 8 + 1):
        if k % 8:
            check(abs(cycle_fourier(3, con3[2][1], con3[2][3], k)) < 1e-9,
                  "base-3 cycle coefficient vanishes")
    print("  base 3, m = (2, 4, 64): orders (2, 32, 40960); band identity; "
          "C_3(k) = 0 for k <= 24 not divisible by D_1 = 8: ok")

    # contrast: x' = prod (1 + 2^-m_k)
    conp = build_construction(2, [2, 8, 160], sign=1)
    check([c[3] for c in conp] == [4, 16, 320], "orders for the + construction")
    for n in range(0, 2000, 13):
        check(band_identity_holds(2, n, conp[2][1], conp[1][1], 160, sign=1),
              "band identity for 1/(1 + b^-m)")
    Np = 1 << 16
    yp = orbit_from_bits(fractional_bits(conp[2][1], Np + W + 1), Np, W)
    print()
    print("  contrast x' = prod (1 + 2^-m_k), m = (2, 8, 160, ...): band multipliers alternate")
    print("  1, 0, so half of every prefix 2 J m_3 lies just above 0")
    for J in (5, 50, 200):
        N = 2 * J * 160
        DN = discrepancy(yp[:N])
        near0 = sum(1 for v in yp[:N] if v < 2.0 ** -20) / N
        check(DN >= 0.5 - 30 / 160 - 1e-6, "D_N(1/x') >= 1/2 - L/m")
        print(f"    N = {N:>6}:  D_N(1/x') = {DN:.5f},  share in [0, 2^-20) = {near0:.4f}")


# ================================================================ main

def main():
    t0 = perf_counter()
    res1 = section_d1a()
    section_d1b(res1)
    section_d1c()
    section_d2()
    print()
    print(f"all {CHECKS[0]} checks passed in {perf_counter() - t0:.1f} s")


if __name__ == "__main__":
    main()
