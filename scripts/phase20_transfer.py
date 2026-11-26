#!/usr/bin/env python3
"""Exact checks for Phase 20 Track B.

B1  coefficient transfer: shadow count, exact mean-tail identity, Markov bound,
    window form, width form and the linear-mass rate, on signed and unsigned
    sequences in several radices; sharpness of the constant 2.
B2  displaced-source reindexing in composite radices and the three
    counterexamples (rational sum, normal sum, polynomial widths).
B3  isolated-source constants: power-law, logarithmic (primes) and
    growing-width sources, with a certified lower-bound lemma check.
B4  the chi_4 Lambert series and Theta_3(1/2)^2 to N = 2^18.

All assertions use integers or Fractions.  Large-N discrepancies use digit
windows certified by integer carries; each reported value is within b^-P of
the true discrepancy.  Ratios to asymptotic formulas are finite measurements.

Run from the repository root:  python -B scripts/phase20_transfer.py
"""

from __future__ import annotations

import math
import random
from bisect import bisect_left, bisect_right
from fractions import Fraction
from math import isqrt
from time import perf_counter

LANDAU_RAMANUJAN = 0.7642236535892206629906987312500923281167905413934


# ---------------------------------------------------------------- digits

def carry_digits(coef, b):
    """Integer part and digits d[1..K] of sum_{i=0}^{K} coef[i] b^{-i}."""
    K = len(coef) - 1
    d = [0] * (K + 1)
    carry = 0
    for i in range(K, 0, -1):
        carry, d[i] = divmod(coef[i] + carry, b)
    return coef[0] + carry, d


def ndigits(x, b):
    """Number of base-b digits of the positive integer x."""
    n = 0
    while x:
        x //= b
        n += 1
    return n


def valuation(x, b):
    v = 0
    while x % b == 0:
        x //= b
        v += 1
    return v, x


# ------------------------------------------------- exact finite-support orbit

def exact_orbit(a, b, N):
    """Numerators Y_n of {b^n F} over B = b^K for F = sum_{m<=K} a[m] b^-m."""
    K = len(a) - 1
    _, d = carry_digits(a, b)
    B = b ** K
    R = 0
    for i in range(1, K + 1):
        R = R * b + d[i]
    Y = []
    for _ in range(N):
        Y.append(R)
        R = (R * b) % B
    return Y, B


def disc_exact(Y, B, N):
    """Exact extreme discrepancy of the first N points Y_n / B."""
    hi = lo = 0
    for i, y in enumerate(sorted(Y[:N]), 1):
        hi = max(hi, i * B - N * y)
        lo = max(lo, N * y - (i - 1) * B)
    return Fraction(hi + lo, N * B)


def far_exact(Y, B, N, eps):
    p, q = eps.numerator, eps.denominator
    return sum(1 for y in Y[:N] if q * min(y, B - y) > p * B)


# ------------------------------------------------------ B1 functionals

class Seq:
    def __init__(self, name, b, a):
        self.name, self.b, self.a = name, b, a
        self.K = len(a) - 1
        self.S = [0] * (self.K + 1)
        self.A = [0] * (self.K + 1)
        for m in range(1, self.K + 1):
            self.S[m] = self.S[m - 1] + (a[m] != 0)
            self.A[m] = self.A[m - 1] + abs(a[m])

    def Sx(self, X):
        return self.S[min(max(X, 0), self.K)]

    def Ax(self, X):
        return self.A[min(max(X, 0), self.K)]

    def Ahat(self, X):
        """sum_m |a(m)| min(1, b^{X-m})."""
        b, K = self.b, self.K
        head = self.Ax(X)
        if X >= K:
            return Fraction(head)
        num = sum(abs(self.a[m]) * b ** (K - m) for m in range(X + 1, K + 1))
        return head + Fraction(num, b ** (K - X))

    def mean_tail_sum(self, N, L):
        """sum_{n<N} tau_L(n) exactly, tau_L(n) = sum_{j>L} |a(n+j)| b^-j."""
        b, K = self.b, self.K
        num = 0
        for m in range(1, K + 1):
            if self.a[m] == 0:
                continue
            nmax = min(N - 1, m - L - 1)
            if nmax < 0:
                continue
            # sum_{n=0}^{nmax} b^{K-m+n}
            num += abs(self.a[m]) * b ** (K - m) * ((b ** (nmax + 1) - 1) // (b - 1))
        return Fraction(num, b ** K)

    def mean_tail_identity(self, N, L):
        """sum_{j>L} b^-j (A(N-1+j) - A(j-1))."""
        b, K = self.b, self.K
        num = 0
        for j in range(L + 1, K + 1):
            num += (self.Ax(N - 1 + j) - self.Ax(j - 1)) * b ** (K - j)
        return Fraction(num, b ** K)

    def shadow(self, N, L):
        return sum(1 for n in range(N)
                   if any(n + j <= self.K and self.a[n + j] != 0 for j in range(1, L + 1)))

    def sources(self):
        out = []
        for m in range(1, self.K + 1):
            if self.a[m]:
                V, U = valuation(abs(self.a[m]), self.b)
                u = ndigits(U, self.b)
                out.append((m, V, U, m - V, m - V - u))
        return out

    def width_shadow(self, N, L):
        mark = bytearray(N)
        for (_m, _V, _U, t, tt) in self.sources():
            lo, hi = max(tt - L, 0), min(t - 1, N - 1)
            for n in range(lo, hi + 1):
                mark[n] = 1
        return sum(mark)

    def Phat(self, X):
        """sum over sources of (|U| b^-u) min(1, b^{X - tt})."""
        b = self.b
        total = Fraction(0)
        for (_m, _V, U, t, tt) in self.sources():
            u = t - tt
            total += Fraction(U, b ** u) if tt <= X else Fraction(U, b ** (t - X))
        return total


def linear_rate_bound(b, C, N, S_before):
    rho = (1 + S_before) / N
    if rho >= 1:
        return 2.0
    return rho * (2 * math.log(1 / rho, b) + max(0.0, math.log(4 * C / (b - 1), b)) + 3)


def b1_sequences(rng):
    seqs = []
    K = 1500
    a = [0] * (K + 1)
    k = 1
    while int(k ** 1.5) <= 1350:
        a[int(k ** 1.5)] = 1
        k += 1
    seqs.append(Seq("unsigned k^1.5, b=2", 2, a))

    a = [0] * (K + 1)
    for j, m in enumerate(range(37, 1350, 37)):
        a[m] = (-1) ** j * (185 + j % 7)
    seqs.append(Seq("signed period-37 mass, b=3", 3, a))

    a = [0] * (K + 1)
    for m in range(1, 1351):
        if rng.random() < 0.03:
            a[m] = rng.choice((-1, 1)) * rng.randint(1, 300)
    seqs.append(Seq("random signed big coefficients, b=10", 10, a))

    a = [0] * (K + 1)
    for m in range(1, 1351):
        if rng.random() < 0.05:
            u = rng.randint(1, 50)
            while u % 6 == 0:
                u = rng.randint(1, 50)
            a[m] = rng.choice((-1, 1)) * 6 ** rng.randint(0, 4) * u
    seqs.append(Seq("composite b=6 with radix-power factors", 6, a))

    a = [0] * (K + 1)
    for m in range(5, 1351, 41):
        for off in range(4):
            a[m + off] = rng.choice((-1, 1)) * rng.randint(1, 20)
    seqs.append(Seq("clustered signed, b=12", 12, a))
    return seqs


def check_b1(rng):
    print("B1  coefficient transfer (exact)")
    N = 1200
    eps_grid = [Fraction(1, 2), Fraction(1, 8), Fraction(1, 64), Fraction(1, 1024)]
    L_grid = [0, 1, 2, 4, 8, 16]
    checks = 0
    for s in b1_sequences(rng):
        b = s.b
        Y, B = exact_orbit(s.a, b, N)
        D = disc_exact(Y, B, N)
        far = {eps: far_exact(Y, B, N, eps) for eps in eps_grid}
        best_M = best_W = Fraction(1)
        for L in L_grid:
            sh = s.shadow(N, L)
            assert sh <= L * (1 + s.Sx(N - 1))
            mt = s.mean_tail_sum(N, L)
            assert mt == s.mean_tail_identity(N, L)
            Ah = s.Ahat(N + L)
            assert mt <= Ah / ((b - 1) * b ** L)
            # Abel identity  Ahat(X) = (1 - 1/b) sum_{i>=0} b^-i A(X+i)
            X = N + L
            if X <= s.K:
                tail = sum(Fraction(s.Ax(X + i), b ** i) for i in range(s.K - X + 1)) \
                    + Fraction(s.Ax(s.K), b ** (s.K - X + 1)) * Fraction(b, b - 1)
            else:
                tail = Fraction(s.Ax(X)) * Fraction(b, b - 1)
            assert Ah == (1 - Fraction(1, b)) * tail
            ws = s.width_shadow(N, L)
            Ph = s.Phat(N + L)
            for eps in eps_grid:
                rhs_M = L * (1 + s.Sx(N - 1)) + Ah / ((b - 1) * b ** L * eps)
                rhs_W = ws + Ph / ((b - 1) * b ** L * eps)
                assert far[eps] <= rhs_M and far[eps] <= rhs_W
                assert 1 - D <= 2 * eps + rhs_M / N and 1 - D <= 2 * eps + rhs_W / N
                best_M = min(best_M, 2 * eps + rhs_M / N)
                best_W = min(best_W, 2 * eps + rhs_W / N)
                checks += 4
        # window (nonuniform) form on two windows
        for (N0, H) in ((300, 400), (700, 450)):
            for L in (2, 6):
                for eps in (Fraction(1, 16), Fraction(1, 256)):
                    p, q = eps.numerator, eps.denominator
                    cnt = sum(1 for y in Y[N0:N0 + H] if q * min(y, B - y) > p * B)
                    loc = Fraction(0)
                    for m in range(N0 + L + 1, s.K + 1):
                        if s.a[m]:
                            e = N0 + H + L - m
                            loc += abs(s.a[m]) * (Fraction(1) if e >= 0 else Fraction(1, b ** (-e)))
                    rhs = L * (1 + s.Sx(N0 + H - 1) - s.Sx(N0)) + loc / ((b - 1) * b ** L * eps)
                    assert cnt <= rhs
                    checks += 1
        print(f"    {s.name:40s} 1-D_N={float(1 - D):.4f}  best mass bound={float(best_M):.4f}"
              f"  best width bound={float(best_W):.4f}")
    print(f"    {checks} exact inequalities (shadow, mean-tail identity, Abel identity, Markov,"
          " width, window) passed")


def check_linear_rate(rng):
    print("B1  linear-mass rate  1-D_N <= rho(2 log_b(1/rho) + log_b^+(4C/(b-1)) + 3), all N")
    checks = 0
    for s in b1_sequences(rng)[:4]:
        C = max(Fraction(s.Ax(X), X) for X in range(1, s.K + 1))
        Y, B = exact_orbit(s.a, s.b, 1200)
        worst = 0.0
        for N in list(range(1, 401)) + [600, 900, 1200]:
            gap = float(1 - disc_exact(Y, B, N))
            bound = linear_rate_bound(s.b, float(C), N, s.Sx(N - 1))
            assert gap <= bound * (1 - 1e-12) + 1e-15
            worst = max(worst, gap / bound)
            checks += 1
        print(f"    {s.name:40s} C={float(C):8.3f}  max (1-D_N)/bound = {worst:.3f}")
    print(f"    {checks} prefixes checked")


def check_sharpness():
    print("B1  sharpness of the constant 2: z = K/(b^q-1), alternating digits, N = q")
    for b in (2, 3):
        for q in (16, 64, 256, 1024, 4096):
            K = 1
            while K * b * b + 1 <= q:
                K = K * b * b + 1  # digits 1,0,1,...,0,1 (not divisible by b)
            Bq = b ** q - 1
            Y = []
            y = K % Bq
            for _ in range(q):
                Y.append(y)
                y = (y * b) % Bq
            D = disc_exact(Y, Bq, q)
            rho = 1 / q
            C = K / q
            ratio = float(1 - D) / (rho * math.log(1 / rho, b))
            bound = linear_rate_bound(b, C, q, 0)
            assert float(1 - D) <= bound
            print(f"    b={b:2d} q={q:5d}  1-D={float(1 - D):.6f}  "
                  f"(1-D)/(rho log_b(1/rho))={ratio:.3f}  theorem bound={bound:.6f}")


# ------------------------------------------------------------- B2

def check_b2(rng):
    print("B2  displaced-source reindexing (exact, composite radices)")
    total = 0
    for b in (6, 10, 12, 2, 3):
        for trial in range(3):
            K = 120
            a = [0] * (K + 1)
            for m in range(1, K + 1):
                if rng.random() < 0.25:
                    v = rng.randint(0, 6)
                    u = rng.randint(1, 3 * b)
                    a[m] = rng.choice((-1, 1)) * b ** v * u
            a[1] = b ** 4 * 7 if b != 7 else b ** 4 * 5  # an arrival t <= 0
            F = sum(Fraction(a[m], b ** m) for m in range(1, K + 1))
            Cmap = {}
            for m in range(1, K + 1):
                if a[m]:
                    V, U = valuation(abs(a[m]), b)
                    t = m - V
                    Cmap[t] = Cmap.get(t, 0) + (U if a[m] > 0 else -U)
            G = sum((Fraction(c) * b ** (-t) if t <= 0 else Fraction(c, b ** t))
                    for t, c in Cmap.items())
            assert F == G
            assert min(Cmap) <= 0
            for n in range(K + 5):
                tail = sum(Fraction(c, b ** (t - n)) for t, c in Cmap.items() if t > n)
                diff = F * b ** n - tail
                assert diff.denominator == 1
                total += 1
    print(f"    F = sum_t C(t) b^-t and b^n F - sum_(t>n) C(t) b^(n-t) in Z: {total} shifts")

    # displaced width inequality versus raw mass inequality in radix 10
    N = 1000
    K = 1300
    a = [0] * (K + 1)
    k = 1
    while int(k ** 1.6) <= 1250:
        m = int(k ** 1.6)
        a[m] = (-1) ** k * 10 ** min(30, m // 40) * (1 + k % 9)
        k += 1
    s = Seq("radix-power coefficients", 10, a)
    Y, B = exact_orbit(a, 10, N)
    D = disc_exact(Y, B, N)
    best_W = min(Fraction(2) * e + (s.width_shadow(N, L) + s.Phat(N + L) / (9 * 10 ** L * e)) / N
                 for L in (1, 2, 3, 4, 6) for e in (Fraction(1, 100), Fraction(1, 1000)))
    best_M = min(Fraction(2) * e + (L * (1 + s.Sx(N - 1)) + s.Ahat(N + L) / (9 * 10 ** L * e)) / N
                 for L in (1, 2, 4, 8, 16, 32, 40) for e in (Fraction(1, 100), Fraction(1, 1000)))
    assert 1 - D <= best_W and 1 - D <= best_M
    print(f"    radix-power coefficients b=10, N={N}: 1-D_N={float(1 - D):.4f},"
          f" displaced-width bound {float(best_W):.4f}, raw-mass bound {float(best_M):.4f}")

    print("B2  counterexamples")
    # (a) logarithmic support, sum 1/(b^2-1) and 1/(b+1)
    for b in (2, 3, 6, 10):
        prev = 0
        partial = Fraction(0)
        for kk in range(1, 12):
            mk = 2 ** kk
            ak = (b ** (mk - prev) - 1) // (b * b - 1)
            assert ak * (b * b - 1) == b ** (mk - prev) - 1
            partial += Fraction(ak, b ** mk)
            assert partial == (1 - Fraction(1, b ** mk)) / (b * b - 1)
            prev = mk
        z = Fraction(1, b * b - 1)
        Bq = b * b - 1
        Y = [1, b] * 50
        for N in (2, 10, 100):
            assert disc_exact(Y, Bq, N) == Fraction(b, b + 1)
        assert 1 - disc_exact(Y, Bq, 100) == Fraction(1, b + 1)
        # random even support with the same sum
        mset = sorted(rng.sample(range(2, 400, 2), 9))
        prev, partial = 0, Fraction(0)
        for mk in mset:
            partial += Fraction((b ** (mk - prev) - 1) // (b * b - 1), b ** mk)
            prev = mk
        assert partial == (1 - Fraction(1, b ** mset[-1])) * z
    print("    (a) S(X)=floor(log2 X) and arbitrary even supports sum to 1/(b^2-1); "
          "1-D_N = 1/(b+1) at even N  [b=2,3,6,10]")

    # (b) and (c): Champernowne digit blocks
    for b, N in ((2, 4096), (10, 2048)):
        digs = []
        j = 1
        while len(digs) < 3 * N:
            x, ds = j, []
            while x:
                ds.append(x % b)
                x //= b
            digs.extend(reversed(ds))
            j += 1
        K = 2 * N
        for mode in ("log", "poly"):
            a = [0] * (K + 1)
            prev, supp = 0, 0
            if mode == "log":
                cuts = [2 ** i for i in range(1, 40) if 2 ** i <= K]
            else:
                cuts, m = [], 0
                while True:
                    ell = max(1, (len(str(m + 1)) if b == 10 else (m + 1).bit_length()) // 2)
                    if m + ell > K:
                        break
                    m += ell
                    cuts.append(m)
            for mk in cuts:
                block = 0
                for i in range(prev, mk):
                    block = block * b + digs[i]
                a[mk] = block
                if mode == "poly":
                    assert block * block <= b * mk  # |a(m)| <= sqrt(b m)
                prev = mk
                supp += 1
            _, d = carry_digits(a, b)
            assert d[1:prev + 1] == digs[:prev]
            Y, B = exact_orbit(a, b, N)
            D = disc_exact(Y, B, N)
            print(f"    ({'b' if mode == 'log' else 'c'}) b={b:2d} support {supp:5d} of {prev}"
                  f" indices, digits = Champernowne prefix, D_N({N}) = {float(D):.4f}")


# --------------------------------------------- certified large-N windows

def certified_digits(coef_fn, b, N, P, margin=64, tail=None, signed=False):
    """Digits d[1..N+P] of sum_m coef(m) b^-m, certified by two integer carries.

    With tail=None the cutoff K is moved to a nonzero coefficient past N+P+margin
    and the omitted tail is bounded from the next 800 coefficients, assuming
    |coef(m)| <= m^3 beyond them; a borrow or carry then stops near K."""
    K = N + P + margin
    if tail is None:
        while coef_fn(K) == 0:
            K += 1
            assert K < N + P + margin + 10 ** 5, "no nonzero coefficient for the cutoff"
        est = sum(abs(coef_fn(m)) * float(b) ** (K - m) for m in range(K + 1, K + 801))
        tail = 1 + int(est + 1e-6)
    coef = [0] + [coef_fn(m) for m in range(1, K + 1)]
    lo = coef.copy()
    hi = coef.copy()
    hi[K] += tail
    if signed:
        lo[K] -= tail
    _, dl = carry_digits(lo, b)
    _, dh = carry_digits(hi, b)
    assert dl[1:N + P + 1] == dh[1:N + P + 1], "digit certification failed"
    return dl


def windows(d, b, N, P):
    bp = b ** P
    y = 0
    for i in range(1, P + 1):
        y = y * b + d[i]
    out = [0] * N
    for n in range(N):
        out[n] = y
        y = (y * b) % bp + d[n + P + 1]
    return out


def disc_windows(y, b, P, N):
    bp = b ** P
    hi = lo = 0
    for i, v in enumerate(sorted(y[:N]), 1):
        hi = max(hi, i * bp - N * v)
        lo = max(lo, N * v - (i - 1) * bp)
    return (hi + lo) / (N * bp)


def centered_arc_bound(y, b, P, N):
    """min_r 2r + #{dist > r}/N, an upper bound for 1 - D_N (certified dist_hi)."""
    bp = b ** P
    dh = sorted(min(v + 1, bp - v) for v in y[:N])
    best = 1.0
    for k, v in enumerate(dh):
        best = min(best, 2 * v / bp + (N - 1 - k) / N)
    return best


def lemma_lower_bound(y, b, P, N):
    """max over (zeta, eta) of min(beta(zeta), mu(eta), eta - zeta): certified <= 1 - D_N."""
    bp = b ** P
    dh = sorted(min(v + 1, bp - v) for v in y[:N])   # dist <= dist_hi
    dl = sorted(min(v, bp - v - 1) for v in y[:N])   # dist >= dist_lo
    best = 0.0
    grid = [bp * 2.0 ** (-k / 8) for k in range(0, 8 * (P - 1))]
    for zeta in grid:
        beta = bisect_right(dh, zeta) / N
        if beta <= best:
            continue
        for eta in grid:
            if eta <= zeta:
                break
            mu = (N - bisect_left(dl, eta)) / N
            best = max(best, min(beta, mu, (eta - zeta) / bp))
    return best


def measure(name, coef_fn, b, Ns, P, model, tail=None, signed=False):
    Nmax = max(Ns)
    d = certified_digits(coef_fn, b, Nmax, P, tail=tail, signed=signed)
    y = windows(d, b, Nmax, P)
    rows = []
    for N in Ns:
        D = disc_windows(y, b, P, N)
        gap = 1 - D
        arc = centered_arc_bound(y, b, P, N)
        lb = lemma_lower_bound(y, b, P, N)
        h = b ** (-P)
        assert lb <= gap + h + 1e-12
        assert gap <= arc + h + 1e-12
        rows.append((N, gap, lb, arc, model(N)))
    print(f"    {name}")
    for (N, gap, lb, arc, mod) in rows:
        print(f"      N={N:7d}  1-D_N={gap:.5f}  lemma LB={lb:.5f}  centred-arc UB={arc:.5f}"
              f"  model={mod:.5f}  ratio={gap / mod:.3f}")
    return rows


def icbrt(n):
    r = round(n ** (1 / 3))
    while r ** 3 > n:
        r -= 1
    while (r + 1) ** 3 <= n:
        r += 1
    return r


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(range(p * p, n + 1, p)))
    return sieve


def check_b3():
    print("B3  isolated-source constants (certified digits; ratios are finite measurements)")
    Ns = (2 ** 12, 2 ** 14, 2 ** 16, 2 ** 18)
    P = 40

    def theta(m):
        r = isqrt(m)
        return 1 if r * r == m else 0

    def law(count, b):
        def model(N):
            rho = count(N) / N
            return rho * math.log(1 / rho, b)
        return model

    measure("Case 1, sigma=1/2: sum_j 2^-(j^2), model rho log2(1/rho), rho=floor(sqrt N)/N",
            theta, 2, Ns, P, law(lambda N: isqrt(N), 2), tail=4)
    measure("Case 1, sigma=1/2, b=10: sum_j 10^-(j^2)", theta, 10, Ns[:3], 14,
            law(lambda N: isqrt(N), 10), tail=4)

    def cube(m):
        return 1 if icbrt(m) ** 3 == m else 0

    measure("Case 1, sigma=1/3: sum_k 2^-(k^3)", cube, 2, Ns, P, law(icbrt, 2), tail=4)

    pr = primes_upto(2 ** 18 + 200)
    pcount = [0] * len(pr)
    for i in range(1, len(pr)):
        pcount[i] = pcount[i - 1] + pr[i]
    rows = measure("Case 2, kappa=1: prime constant sum_p 2^-p, model (pi(N)/N) log2(N/pi(N))",
                   lambda m: pr[m], 2, Ns, P, law(lambda N: pcount[N], 2), tail=4)
    for (N, gap, *_r) in rows[-1:]:
        asym = math.log(math.log(N)) / (math.log(2) * math.log(N))
        print(f"      asymptotic (log log N)/(log 2 log N) at N=2^18: {asym:.5f};"
              f" ratio {gap / asym:.3f}")
    # isolation statistics for primes
    N = 2 ** 18
    plist = [p for p in range(2, N + 1) if pr[p]]
    for H in (2, 4, 6, 8):
        bad = sum(1 for i, p in enumerate(plist)
                  if (i > 0 and p - plist[i - 1] <= H) or (i + 1 < len(plist) and plist[i + 1] - p <= H))
        print(f"      primes <= 2^18 with another prime within {H}: {bad / len(plist):.3f}")

    # Case 3: growing widths
    def width_model(src, b):
        def model(N):
            S = sum(1 for (t, u) in src if t <= N)
            W = sum(u for (t, u) in src if t <= N)
            lam = math.log(N / S, b)
            return (W + S * lam) / N
        return model

    def make(pos_fn, val_fn, b, Kmax):
        coef = {}
        src = []
        k = 1
        while True:
            m = pos_fn(k)
            if m > Kmax:
                break
            v = val_fn(k, m)
            coef[m] = coef.get(m, 0) + v
            V, U = valuation(abs(v), b)
            src.append((m - V, ndigits(U, b)))
            k += 1
        return (lambda m: coef.get(m, 0)), src

    Kmax = 2 ** 18 + 20000
    f, src = make(lambda j: j * j, lambda j, m: 2 * j + 1, 2, Kmax)
    measure("Case 3, sigma=gamma=1/2: sum_j (2j+1) 2^-(j^2), model (W + S lambda)/N",
            f, 2, Ns, P, width_model(src, 2))
    f, src = make(lambda j: j * j, lambda j, m: 2 * j + 1, 10, Kmax)
    measure("Case 3, b=10: sum_j (2j+1) 10^-(j^2)", f, 10, Ns[:3], 14, width_model(src, 10))
    pos = lambda k: int(k ** 1.5)
    f, src = make(pos, lambda k, m: (-1) ** k * (2 * k + 1), 2, Kmax)
    measure("Case 3, sigma=2/3, gamma=2/3: (-1)^k (2k+1) at floor(k^1.5)", f, 2, Ns, P,
            width_model(src, 2), signed=True)
    f2, src2 = make(pos, lambda k, m: 1 << ((2 * k + 1).bit_length() - 1), 2, Kmax)
    measure("      contrast: pure powers 2^w at floor(k^1.5) (same width), generic model",
            f2, 2, Ns, P, width_model(src, 2))
    f3, src3 = make(pos, lambda k, m: (1 << (2 * k + 1).bit_length()) - 1, 2, Kmax)
    measure("      contrast: all-ones 2^w - 1 at floor(k^1.5) (same width), generic model",
            f3, 2, Ns, P, width_model(src, 2))


# ------------------------------------------------------------- B4

def spf_sieve(n):
    spf = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if spf[p] == p:
            for q in range(p * p, n + 1, p):
                if spf[q] == q:
                    spf[q] = p
    return spf


def lambert_coefficients(spf, chi):
    """c(n) = sum_{d|n} chi(d) for a real character given on primes."""
    n_max = len(spf) - 1
    c = [0] * (n_max + 1)
    c[1] = 1
    for n in range(2, n_max + 1):
        p = spf[n]
        rest, e = n // p, 1
        while rest % p == 0:
            rest //= p
            e += 1
        s = chi(p)
        local = e + 1 if s == 1 else (1 - e % 2 if s == -1 else 1)
        c[n] = local * c[rest]
    return c


def chi4(p):
    return 0 if p == 2 else (1 if p % 4 == 1 else -1)


def chi3(p):
    return 0 if p == 3 else (1 if p % 3 == 1 else -1)


def check_b4():
    print("B4  chi_4 Lambert series L = sum_n (r_2(n)/4) 2^-n")
    P = 40
    Nmax = 2 ** 18
    K = Nmax + P + 64
    spf = spf_sieve(K + 10)
    c = lambert_coefficients(spf, chi4)
    lim = 4096
    r2 = [0] * (lim + 1)
    for x in range(-isqrt(lim), isqrt(lim) + 1):
        for yv in range(-isqrt(lim), isqrt(lim) + 1):
            s = x * x + yv * yv
            if 1 <= s <= lim:
                r2[s] += 1
    assert all(r2[n] == 4 * c[n] for n in range(1, lim + 1))
    assert all(c[n] == sum((0 if d % 2 == 0 else (1 if d % 4 == 1 else -1))
                           for d in range(1, n + 1) if n % d == 0) for n in range(1, 600))
    # Landau-Ramanujan constant from its Euler product
    pr = primes_upto(10 ** 6)
    prod = 1.0
    for p in range(3, 10 ** 6, 4):
        if pr[p]:
            prod *= 1 / (1 - p ** -2)
    Kc = math.sqrt(prod / 2)
    assert abs(Kc - LANDAU_RAMANUJAN) < 1e-6
    print(f"    r_2 formula to {lim}; Landau-Ramanujan K (Euler product to 1e6) = {Kc:.9f}")

    d = certified_digits(lambda m: c[m], 2, Nmax, P, tail=K + 2)
    y = windows(d, 2, Nmax, P)
    # Theta_3(1/2)^2 = 1 + sum r_2(n) 2^-n has the digits of 4L
    dt = certified_digits(lambda m: 4 * c[m], 2, Nmax, P, tail=4 * (K + 2))
    yt = windows(dt, 2, Nmax, P)
    assert dt[1:Nmax] == d[3:Nmax + 2]

    # displaced sources
    V = [0] * (K + 1)
    U = [0] * (K + 1)
    fiber = {}
    for n in range(1, K + 1):
        if c[n]:
            v, u = valuation(c[n], 2)
            V[n], U[n] = v, u
            fiber.setdefault(n - v, []).append(n)
    Cn = [0] * (K + 2)
    for t, ns in fiber.items():
        if 1 <= t <= K:
            Cn[t] = sum(U[n] for n in ns)
    A = [0.0] * (K + 2)
    for s in range(K - 1, -1, -1):
        A[s] = (Cn[s + 1] + A[s + 1]) / 2
    for N in (2 ** 12, 2 ** 14, 2 ** 16, 2 ** 18):
        D = disc_windows(y, 2, P, N)
        Dt = disc_windows(yt, 2, P, N)
        assert abs(Dt - D) <= 2 / N + 2 * 2 ** -P
        gap = 1 - D
        S = sum(1 for n in range(1, N + 1) if c[n])
        Seff = sum(1 for t in range(1, N + 1) if Cn[t])
        coll = sum(1 for t in range(1, N + 1) if t in fiber and len(fiber[t]) > 1)
        rho = Seff / N
        lnN = math.log(N)
        asym = Kc / (2 * math.log(2)) * math.log(lnN) / math.sqrt(lnN)
        law = rho * math.log2(1 / rho)
        arc = centered_arc_bound(y, 2, P, N)
        lb = lemma_lower_bound(y, 2, P, N)
        assert lb <= gap + 2 ** -P + 1e-12 and gap <= arc + 2 ** -P + 1e-12
        print(f"    N=2^{N.bit_length() - 1:2d}  1-D_N={gap:.5f}  |D_N(Theta^2)-D_N(L)|={abs(Dt - D):.2e}"
              f"  lemma LB={lb:.5f}  centred-arc UB={arc:.5f}")
        sups = [n for n in range(1, N + 1) if c[n]]
        meanV = sum(V[n] for n in sups) / S
        Hv = math.log2(lnN)
        bigV = sum(1 for n in sups if V[n] > Hv) / S
        meanU = sum(U[n] for n in sups) / S
        print(f"             S(N)={S}  S(N)/(K N/sqrt(log N))={S / (Kc * N / math.sqrt(lnN)):.4f}"
              f"  S_eff={Seff}  collisions={coll} ({coll / S:.4f})")
        print(f"             mean V={meanV:.3f}  P(V>log2 log N)={bigV:.4f}  mean U={meanU:.4f}"
              f"  P(U>1)={sum(1 for n in sups if U[n] > 1) / S:.4f}"
              f"  mean A(s)*sqrt(log N)={sum(A[:N]) / N * math.sqrt(lnN):.4f}")
        arrivals = [t for t in range(1, N + 1) if Cn[t]]
        iso = []
        for H in (1, 2, 3, 4, 6):
            pos = set(arrivals)
            bad = sum(1 for t in arrivals if any((t + h) in pos for h in range(-H, H + 1) if h))
            iso.append(f"H={H}:{1 - bad / len(arrivals):.3f}")
        print("             isolated arrival fraction  " + "  ".join(iso))
        print(f"             rho log2(1/rho)={law:.5f} (ratio {gap / law:.3f})   "
              f"K/(2 log 2) loglogN/sqrt(logN)={asym:.5f} (ratio {gap / asym:.3f})")

    # a second real character: chi_{-3}
    c3 = lambert_coefficients(spf, chi3)
    prod = 1.0
    for p in range(2, 10 ** 6):
        if pr[p] and p % 3 == 2:
            prod *= 1 / (1 - p ** -2)
    L1 = math.pi / (3 * math.sqrt(3))
    C3 = math.sqrt(L1 * prod * 1.5 / math.pi)
    N = 2 ** 16
    d3 = certified_digits(lambda m: c3[m], 2, N, P, tail=K + 2)
    y3 = windows(d3, 2, N, P)
    gap = 1 - disc_windows(y3, 2, P, N)
    S3 = sum(1 for n in range(1, N + 1) if c3[n])
    lnN = math.log(N)
    print(f"    chi_(-3): C_chi={C3:.6f}  S(N)/(C N/sqrt log N)={S3 / (C3 * N / math.sqrt(lnN)):.4f}"
          f"  1-D_N(2^16)={gap:.5f}  ratio to C/(2 log 2) loglogN/sqrt(logN):"
          f" {gap / (C3 / (2 * math.log(2)) * math.log(lnN) / math.sqrt(lnN)):.3f}")


def main():
    t0 = perf_counter()
    rng = random.Random(20260)
    check_b1(rng)
    check_linear_rate(random.Random(20260))
    check_sharpness()
    check_b2(random.Random(7))
    check_b3()
    check_b4()
    print(f"all Phase 20 Track B checks passed in {perf_counter() - t0:.1f} s")


if __name__ == "__main__":
    main()
