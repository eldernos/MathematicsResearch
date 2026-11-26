#!/usr/bin/env python3
"""Exact checks for notes/phase22/simple-normality-and-signed-transfer.md.

Pure standard library.  Every inequality of the note that concerns a finite prefix is
checked with exact integer or rational arithmetic on the truncated numbers

    z_M = c + sum_{1 <= m <= M} a(m) b^{-m},      c = m0/(b-1),

which are genuine real numbers, so the finite theorems apply to them verbatim.  Table
entries that are attributed to the infinite series are certified: for every reported
shift the truncation error is shown to be smaller than the distance to every relevant
cylinder boundary and to zero.

Sections (numbering follows the note):
  1  interior fixed-point cylinders and the boundary splitting (Lemma 1.1, 1.2)
  2  localization of the deficit at a fixed point (Lemma 2.2) and the word dichotomy
     (Theorem 3.2), on structured and random-burst inputs
  3  far-count and mean-distance bounds (Proposition 3.1)
  5  oriented-tail transfer (Theorem 5.2) and the bad-tail count (Theorem 5.3)
  6  gap-exact tails, bad counts per gap, dominance (Proposition 6.1, Lemma 6.2,
     Theorem 6.3, Corollary 6.4, Proposition 6.5)
  7  limiting frequencies of the explicit families (Table 7.1), lacunary oscillation
  8  prescribed limits and prescribed limit intervals (Theorems 8.1, 8.2)

Exits with status 0 when every check passes.
"""

from __future__ import annotations

import math
import random
import sys
import time
from fractions import Fraction
from math import isqrt

START = time.time()
CHECKS = 0


def check(cond: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


# ---------------------------------------------------------------------------
# Coefficient families (dict m -> a(m), 1 <= m <= M)
# ---------------------------------------------------------------------------

def fam_squares(M, coeff=1):
    return {k * k: coeff for k in range(1, isqrt(M) + 1)}


def fam_pentagonal(M):
    """E_b - 1 = sum_k (-1)^k (b^{-k(3k-1)/2} + b^{-k(3k+1)/2})."""
    a = {}
    k = 1
    while k * (3 * k - 1) // 2 <= M:
        s = (-1) ** k
        for p in (k * (3 * k - 1) // 2, k * (3 * k + 1) // 2):
            if p <= M:
                a[p] = a.get(p, 0) + s
        k += 1
    return a


def fam_jacobi(M):
    """E_b^3 - 1 = sum_{k>=1} (-1)^k (2k+1) b^{-k(k+1)/2}."""
    a = {}
    k = 1
    while k * (k + 1) // 2 <= M:
        a[k * (k + 1) // 2] = (-1) ** k * (2 * k + 1)
        k += 1
    return a


def fam_two_progression(M, s, t, sign_v=1):
    """+sign_v at v_k=(s k^2+t k)/2, -sign_v at u_k=(s k^2-t k)/2."""
    assert 0 < t < s and (s - t) % 2 == 0
    a = {}
    k = 1
    while (s * k * k - t * k) // 2 <= M:
        u, v = (s * k * k - t * k) // 2, (s * k * k + t * k) // 2
        a[u] = -sign_v
        if v <= M:
            a[v] = sign_v
        k += 1
    return a


def fam_periodic_squares(M, pattern):
    p = len(pattern)
    return {k * k: pattern[(k - 1) % p] for k in range(1, isqrt(M) + 1)}


def beatty_floor(k, alpha):
    """floor(k*alpha) for alpha a Fraction or the string 'golden' ((sqrt5-1)/2)."""
    if alpha == "golden":
        return (isqrt(5 * k * k) - k) // 2
    return (k * alpha.numerator) // alpha.denominator


def golden_times(x):
    """Lower bracket for x*(sqrt5-1)/2, x a positive integer: value in (lo, lo + 2^-21)."""
    return Fraction(isqrt(5 * x * x * 4 ** 20) - x * 2 ** 20, 2 ** 21)


def beatty_bit(k, alpha):
    return beatty_floor(k, alpha) - beatty_floor(k - 1, alpha)


def fam_beatty_squares(M, alpha):
    return {k * k: 2 * beatty_bit(k, alpha) - 1 for k in range(1, isqrt(M) + 1)}


INTERVAL_LO, INTERVAL_HI = Fraction(1, 5), Fraction(7, 10)


def interval_phase(k):
    """Phase i with K_i < k <= K_{i+1}, K_0 = 0, K_i = 2^{i^2} (i >= 1)."""
    i = 0
    while (1 << ((i + 1) ** 2)) < k:
        i += 1
    return i


def interval_target(k):
    return INTERVAL_HI if interval_phase(k) % 2 == 0 else INTERVAL_LO


def fam_interval_squares(M):
    return {k * k: 2 * beatty_bit(k, interval_target(k)) - 1 for k in range(1, isqrt(M) + 1)}


def fam_lacunary(M, lam=2):
    a = {}
    k = 1
    while lam ** k <= M:
        a[lam ** k] = (-1) ** k
        k += 1
    return a


def fam_cubes(M, signs=None):
    a = {}
    k = 1
    while k ** 3 <= M:
        a[k ** 3] = 1 if signs is None else signs[(k - 1) % len(signs)]
        k += 1
    return a


# ---------------------------------------------------------------------------
# Orbit of z_M = m0/(b-1) + sum a(m) b^{-m}
# ---------------------------------------------------------------------------

class Orbit:
    """Exact orbit data for n < N.

    W_n = b^M T_n with T_n = sum_{n < m <= M} a(m) b^{n-m};  W_{n+1} = b W_n - a(n+1) b^M.
    x_n = {m0/(b-1) + T_n} = X_n / Q with Q = (b-1) b^M.

    eps_sign in {-1, 0, +1}: when nonzero, every statistic is computed for z_M + eps_sign*eta
    with eta > 0 infinitesimal (exact ties are broken by the sign of the discarded tail).
    With certify=True, every non-tie comparison is shown to have margin larger than the
    truncation error b^{n-M} * Hcert, so the statistics are those of the infinite series.
    """

    def __init__(self, b, a, M, N, m0=0, Ls=(1, 2, 3, 4), keep_x=0, certify=False, eps_sign=0):
        assert N + max(Ls) <= M
        assert not (certify and eps_sign == 0)
        assert not certify or max(Ls) <= 4, "the digit certificate uses the grid b^-4"
        self.b, self.a, self.M, self.N, self.m0, self.Ls = b, a, M, N, m0, Ls
        self.eps_sign = eps_sign
        bM = b ** M
        Q = (b - 1) * bM
        self.Q = Q
        W = sum(c * b ** (M - m) for m, c in a.items() if 1 <= m <= M)
        thr = {L: b ** (M - L) for L in Ls}
        nsteps = N + max(Ls) - 1
        digits = []
        self.nonneg = []          # T_n >= 0
        self.badp = {L: [] for L in Ls}   # |T_n| >= b^-L
        self.bad = {L: [] for L in Ls}    # T_n not in [-b^-L, b^-L)
        self.circ = []            # numerator of ||T_n|| over b^M (only first keep_x)
        self.X = []
        self.W_at = {}            # W_{m-1} for support points m (to get V_k)
        support = sorted(m for m in a if a[m] != 0 and 1 <= m <= M)
        self.support = support
        need_prev = set(m - 1 for m in support)
        uncert = 0
        Hcert = 3 * isqrt(4 * M) + 8
        e = eps_sign
        if certify:
            # the error bound b^{n-M} Hcert grows with n; check it at n = N-1 once
            check((b - 1) * b ** 4 * b ** (N - 1) * Hcert < Q, "certificate error below the grid spacing")
        bn = 1
        for n in range(nsteps):
            if n in need_prev:
                self.W_at[n + 1] = W
            r = (m0 * bM + (b - 1) * W) % Q
            dg = (b * r) // Q
            if e < 0 and (b * r) % Q == 0:
                dg = (dg - 1) % b          # x_n - eta crosses down through a digit boundary
            digits.append(dg)
            if n < N:
                self.nonneg.append(W > 0 or (W == 0 and e >= 0))   # T_n = 0 counts as T_n >= 0
                aw = abs(W)
                sw = (W > 0) - (W < 0)
                for L in Ls:
                    t = thr[L]
                    # |T| >= b^-L; a tie |T| = b^-L survives unless the perturbation pushes inward
                    self.badp[L].append(aw > t or (aw == t and sw * e >= 0))
                    # T outside [-b^-L, b^-L): ties broken by e
                    out = W > t or W < -t or (W == t and e >= 0) or (W == -t and e < 0)
                    self.bad[L].append(out)
                if n < keep_x:
                    self.X.append(r)
                    r0 = W % bM
                    self.circ.append(min(r0, bM - r0))
                if certify:
                    err = bn * Hcert  # in units of b^{-M}
                    ok = aw == 0 or aw > err
                    for L in Ls:
                        ok = ok and (aw == thr[L] or abs(aw - thr[L]) > err)
                    g = (b ** 4 * r) % Q
                    ok = ok and (g == 0 or min(g, Q - g) > (b - 1) * b ** 4 * err)
                    if not ok:
                        uncert += 1
            an = a.get(n + 1, 0)
            W = b * W - an * bM if an else b * W
            bn *= b
        self.digits = digits
        self.uncertified = uncert

    # word value at shift n of length L (digits d_{n+1}..d_{n+L})
    def word(self, n, L):
        v = 0
        for i in range(L):
            v = v * self.b + self.digits[n + i]
        return v

    def word_counts(self, N, L):
        cnt = {}
        for n in range(N):
            v = self.word(n, L)
            cnt[v] = cnt.get(v, 0) + 1
        return cnt


def truncate_before_support(fam, N, b):
    """Return (a, M, s): M = (first support point m* > N + 70) - 1, a truncated to m <= M,
    and s = sign of the discarded tail z - z_M = sum_{m >= m*} a(m) b^{-m}.

    s = sign a(m*) is certified by the dominance inequality R* < |a(m*)| (Lemma 6.2),
    R* = sum_{m > m*} |a(m)| b^{m*-m}, evaluated on the generated support plus a crude
    bound for the remainder.  |z - z_M| <= (|a(m*)| + R*) b^{-m*} <= b^{-M} * Hcert.
    """
    top = 8 * N + 2000
    big = fam(top)
    nxt = min(m for m, c in big.items() if c != 0 and m > N + 70)
    check(nxt + 400 <= top, "generated support covers the dominance window")
    M = nxt - 1
    Rstar = Fraction(0)
    for m, c in big.items():
        if nxt < m <= nxt + 400 and c:
            Rstar += Fraction(abs(c), b ** (m - nxt))
    Rstar += Fraction(2 * (top + 500), b ** 399)   # remainder: |a(m)| <= m for all families
    check(Rstar < abs(big[nxt]), "dominance at the cut")
    check(abs(big[nxt]) + Rstar <= 3 * isqrt(4 * M) + 8, "tail size below Hcert")
    sgn = 1 if big[nxt] > 0 else -1
    return {m: c for m, c in big.items() if m <= M and c != 0}, M, sgn


def repunit(b, L):
    return (b ** L - 1) // (b - 1)


# ---------------------------------------------------------------------------
# Section 1: cylinder geometry of the fixed points
# ---------------------------------------------------------------------------

def section1():
    cases = 0
    for b in range(3, 13):
        for m in range(1, b - 1):
            c = Fraction(m, b - 1)
            for L in range(1, 5):
                v = m * repunit(b, L)
                lo, hi = Fraction(v, b ** L), Fraction(v + 1, b ** L)
                check(lo < c < hi, f"interior {b},{m},{L}")
                check(c - lo == Fraction(m, (b - 1) * b ** L), "left margin")
                check(hi - c == Fraction(b - 1 - m, (b - 1) * b ** L), "right margin")
                marg = Fraction(min(m, b - 1 - m), (b - 1) * b ** L)
                check(marg >= Fraction(1, (b - 1) * b ** L), "margin >= 1/((b-1)b^L)")
                check((marg == Fraction(1, (b - 1) * b ** L)) == (m in (1, b - 2)), "equality case")
                # closed ball of radius < margin lies in the cylinder; the endpoint behaviour
                eps = marg - Fraction(1, 10 ** 30)
                for t in (c - eps, c + eps, c):
                    check(math.floor(t * b ** L) == v, "ball inside cylinder")
                check(math.floor((c + marg) * b ** L) == (v + 1 if 2 * m >= b - 1 else v), "right endpoint")
                # digit-string of c: constant m
                check(all(math.floor(c * b ** j) % b == m for j in range(1, L + 1)), "c = 0.mmm...")
                cases += 1
    # boundary point 0: [0,b^-L) is 0^L and [1-b^-L,1) is (b-1)^L
    for b in range(2, 13):
        for L in range(1, 5):
            check((b - 1) * repunit(b, L) == b ** L - 1, "top word value")
            t = Fraction(1, b ** L) - Fraction(1, 10 ** 30)
            check(math.floor(t * b ** L) == 0, "0^L side")
            check(math.floor((1 - t) * b ** L) == b ** L - 1, "(b-1)^L side")
    print(f"[1] interior cylinder inclusions: {cases} cases (b=3..12, 1<=m<=b-2, L=1..4) pass;"
          " minimal margin 1/((b-1)b^L) attained exactly at m in {1, b-2}")


# ---------------------------------------------------------------------------
# Section 2: localization lemma and dichotomy theorem
# ---------------------------------------------------------------------------

def deficit(Xs, Q):
    """Exact 1 - D_N for x_n = X_n/Q as an unreduced pair (num, den), den = N*Q
    (Niederreiter's formula D_N = 1/N + max(i/N - x_(i)) - min(i/N - x_(i)))."""
    N = len(Xs)
    s = sorted(Xs)
    vals = [i * Q - N * x for i, x in enumerate(s, start=1)]
    DNQ = Q + max(vals) - min(vals)          # = N*Q*D_N
    return N * Q - DNQ, N * Q


STATS = {"lemma_cases": 0, "lemma_hyp": 0, "max_ratio": Fraction(0), "thm_cases": 0,
         "thm_i": 0, "thm_ii": 0}


def check_lemma_and_theorem(b, Xs, Q, label):
    N = len(Xs)
    dn, dd = deficit(Xs, Q)                  # delta = dn/dd
    check(0 <= dn <= dd, "deficit in [0,1]")
    STATS["lemma_cases"] += 1
    # hypothesis delta < 1/2 - 1/N  <=>  2N dn < (N-2) dd
    if N >= 3 and 2 * N * dn < (N - 2) * dd:
        STATS["lemma_hyp"] += 1
        D2 = (b - 1) * Q
        found = False
        best = None
        for j in range(b - 1):
            dnum = []
            for X in Xs:
                d = ((b - 1) * X - j * Q) % D2
                dnum.append(min(d, D2 - d))          # ||x_n - j/(b-1)|| = dnum/D2
            # dist > b delta/(b-1)  <=>  dnum (b-1) dd > b dn D2
            far = sum(1 for d in dnum if d * (b - 1) * dd > b * dn * D2)
            if far * dd <= dn * N:
                found = True
            if dn > 0:
                ds = sorted(dnum, reverse=True)
                kk = (dn * N) // dd
                rstar = ds[kk] if kk < N else 0
                ratio = Fraction(rstar * (b - 1) * dd, D2 * b * dn)
                best = ratio if best is None else min(best, ratio)
        check(found, f"Lemma 2.2 fails for {label} N={N}")
        if best is not None and best > STATS["max_ratio"]:
            STATS["max_ratio"] = best
        if b == 2 and 4 * dn < dd:
            # Theorem 4.1(a) needs 2 delta < eps <= 1/2, hence delta < 1/4.
            # Interior scale eps = delta + 1/4, so 2 delta < eps < 1/2.
            en, ed = 4 * dn + dd, 4 * dd
            check(2 * dn * ed < en * dd and 2 * en < ed, "interior scale")
            f0 = sum(1 for X in Xs if 2 * X < Q)
            Peps = sum(1 for X in Xs if X * ed < en * Q)
            check(0 <= f0 - Peps and (f0 - Peps) * dd <= dn * N, "Theorem 4.1 positive side")
            STATS["binary"] = STATS.get("binary", 0) + 1
    if N >= 4:
        for L in (1, 2, 3):
            # delta < b^{-L-1}
            if dn * b ** (L + 1) < dd:
                STATS["thm_cases"] += 1
                cnt = {}
                for X in Xs:
                    v = (b ** L * X) // Q
                    cnt[v] = cnt.get(v, 0) + 1
                other = N - cnt.get(0, 0) - cnt.get(b ** L - 1, 0)
                alt_i = other * dd <= dn * N
                alt_ii = [m for m in range(1, b - 1)
                          if (N - cnt.get(m * repunit(b, L), 0)) * dd <= dn * N]
                check(alt_i or bool(alt_ii), f"Theorem 3.2 fails for {label} N={N} L={L}")
                check(int(alt_i) + len(alt_ii) == 1, "alternatives exclusive")
                STATS["thm_i" if alt_i else "thm_ii"] += 1


def section2():
    # structured inputs: sparse series in M_b and m/(b-1) + M_b
    structured = []
    for b in (2, 3, 5, 10):
        for m0 in range(0, b - 1):
            structured.append((b, m0, fam_lacunary(700)))
            structured.append((b, m0, fam_cubes(700, signs=[1, -1, -1])))
        structured.append((b, 0, fam_pentagonal(700)))
        structured.append((b, 0, fam_squares(700)))
    for b, m0, a in structured:
        orb = Orbit(b, a, 700, 600, m0=m0, Ls=(1, 2, 3, 4), keep_x=600)
        for N in (4, 5, 8, 16, 32, 64, 150, 300, 600):
            check_lemma_and_theorem(b, orb.X[:N], orb.Q, f"b={b} m0={m0}")
    # random-burst inputs: long runs of a constant digit with noise; mixtures of 0 and b-1 runs
    rng = random.Random(22)
    for trial in range(700):
        b = rng.choice([2, 3, 4, 5, 7, 10])
        M = 70
        mode = rng.randrange(3)
        digs = []
        while len(digs) < M:
            run = rng.randint(3, 25)
            if mode == 0:
                d = rng.choice([0, b - 1])
            elif mode == 1 and b >= 3:
                d = rng.randrange(1, b - 1)
            else:
                d = rng.randrange(b)
            for _ in range(run):
                digs.append(d if rng.random() > 0.08 else rng.randrange(b))
        digs = digs[:M]
        Z = 0
        for d in digs:
            Z = Z * b + d
        Q = b ** M
        N = rng.randint(4, 50)
        Xs = [(Z * b ** n) % Q for n in range(N)]
        check_lemma_and_theorem(b, Xs, Q, f"random trial {trial}")
    print(f"[2] Lemma 2.2: {STATS['lemma_cases']} prefixes, hypothesis delta<1/2-1/N met in "
          f"{STATS['lemma_hyp']}; largest needed radius / (b delta/(b-1)) = "
          f"{float(STATS['max_ratio']):.4f} (<= 1)")
    print(f"    Theorem 3.2: {STATS['thm_cases']} (prefix, L) cases with delta<b^(-L-1): "
          f"{STATS['thm_i']} boundary, {STATS['thm_ii']} interior, all exclusive")
    print(f"    Theorem 4.1 finite positive-side bound: {STATS.get('binary', 0)} binary prefixes")


# ---------------------------------------------------------------------------
# Section 3: far counts and mean distances (Proposition 3.1)
# ---------------------------------------------------------------------------

def section3():
    cases = 0
    for b in (3, 4, 7, 10):
        for m0 in range(0, b - 1):
            for a in (fam_squares(700), fam_pentagonal(700), fam_beatty_squares(700, Fraction(1, 3))):
                orb = Orbit(b, a, 700, 600, m0=m0, keep_x=600)
                bM = b ** 700
                for N in (50, 200, 600):
                    for L in (1, 2, 3):
                        cnt = orb.word_counts(N, L)
                        MN = Fraction(sum(orb.circ[:N]), N * bM)
                        if m0 == 0:
                            far = sum(1 for n in range(N) if orb.circ[n] * b ** L >= bM)
                            other = N - cnt.get(0, 0) - cnt.get(b ** L - 1, 0)
                            check(other <= far, "boundary far count")
                            check(Fraction(far, N) <= b ** L * MN, "Markov boundary")
                        else:
                            mm = min(m0, b - 1 - m0)
                            # ||x_n - c|| = ||T_n||
                            far = sum(1 for n in range(N) if orb.circ[n] * (b - 1) * b ** L >= mm * bM)
                            miss = N - cnt.get(m0 * repunit(b, L), 0)
                            check(miss <= far, "interior far count")
                            check(Fraction(far, N) <= MN * Fraction((b - 1) * b ** L, mm), "Markov interior")
                        cases += 1
    # base 2: f_{0^L} vs f_0 and positive-side counts
    orb = Orbit(2, fam_pentagonal(3000), 3000, 2900, keep_x=2900)
    for N in (100, 1000, 2900):
        f0 = sum(1 for n in range(N) if orb.digits[n] == 0)
        for L in (1, 2, 3, 4):
            cnt = orb.word_counts(N, L)
            other = N - cnt.get(0, 0) - cnt.get(2 ** L - 1, 0)
            check(0 <= f0 - cnt.get(0, 0) <= other, "0 <= f_0 - f_{0^L} <= other")
        cases += 1
    print(f"[3] Proposition 3.1 far-count and Markov bounds: {cases} cases pass")


# ---------------------------------------------------------------------------
# Sections 5-7: oriented tails, gap-exact bad counts, dominance, tables
# ---------------------------------------------------------------------------

def hat_A_parts(a, b, X, M):
    """hat_A(X) = head + num / b^D exactly, for support in [1, M] and D = max(0, M - X)."""
    D = max(0, M - X)
    head = sum(abs(c) for m, c in a.items() if m <= X)
    num = sum(abs(c) * b ** (M - m) for m, c in a.items() if m > X)
    return head, num, D


def lam_gap(Wprev, b, M, L, e=0):
    """lambda_k = max(0, floor(L + log_b |V_k|)), V_k = b W_{m_k-1} / b^M; 0 if V_k = 0.
    Ties |V_k| = b^{l-L} are broken by the infinitesimal perturbation of sign e."""
    V = abs(b * Wprev)          # |V_k| * b^M
    if V == 0:
        return 0
    sv = 1 if Wprev > 0 else -1

    def holds(l):               # |V_k| >= b^{l-L}
        lhs, rhs = V * b ** L, b ** (M + l)
        return lhs > rhs or (lhs == rhs and sv * e >= 0)

    if not holds(0):
        return 0
    lam = 0
    while holds(lam + 1):
        lam += 1
    return lam


def analyse(name, b, fam, alpha, N, Ls=(1, 2, 3, 4), H=None, certify=True,
            linear_C=None, exact_prop=False, table=None):
    a, M, sg = truncate_before_support(fam, N, b)
    orb = Orbit(b, a, M, N, Ls=Ls, certify=certify, eps_sign=sg)
    if certify:
        check(orb.uncertified == 0, f"{name}: truncation certificate")
    sup = orb.support
    # support count S(X) for X < N
    S = [0] * (N + 1)
    sset = set(sup)
    for X in range(1, N + 1):
        S[X] = S[X - 1] + (1 if X in sset else 0)
    checkpoints = {c for c in (100, 1000, 2500, 5000) if c < N} | {N}
    # cumulative arrays
    for L in Ls:
        P = Qn = B = Bp = G = 0
        c0 = cT = coth = 0
        for n in range(N):
            v = orb.word(n, L)
            w0 = v == 0
            wT = v == b ** L - 1
            c0 += w0
            cT += wT
            coth += (not w0 and not wT)
            nn = orb.nonneg[n]
            G += nn
            B += orb.bad[L][n]
            Bp += orb.badp[L][n]
            if not orb.bad[L][n]:
                P += nn
                Qn += (not nn)
            Ncur = n + 1
            # Theorem 5.2
            check(P <= c0 <= P + B and Qn <= cT <= Qn + B and coth <= B, f"{name}: Thm 5.2")
            check((c0 - P) + (cT - Qn) + coth == B, f"{name}: Thm 5.2 identity")
            check(abs(c0 - G) <= Bp and abs(cT - (Ncur - G)) <= Bp, f"{name}: sign form")
            if H is not None:
                kap = H_kappa(b, H)
                check(Bp <= (L + kap) * (1 + S[Ncur - 1]), f"{name}: Cor 6.4 at N={Ncur}")
            if exact_prop:
                check(coth == B and c0 == P and cT == Qn, f"{name}: Prop 6.5 exactness")
            if Ncur in checkpoints:
                # Theorem 5.3 for several k (exact) at this prefix
                for k in (0, 1, 2, 4, 8, 12):
                    # exact: Bp <= (L+k)(1+S) + hat_A(X)/((b-1) b^k), X = Ncur+L+k, with
                    # hat_A(X) = head + num / b^D (head = sum_{m<=X}|a|, num over b^D, D = M - X)
                    X = Ncur + L + k
                    head, num, D = hat_A_parts(a, b, X, M)
                    lhs = (Bp - (L + k) * (1 + S[Ncur - 1])) * (b - 1) * b ** k - head
                    check(lhs <= 0 or lhs * b ** D <= num, f"{name}: Thm 5.3 L={L} k={k} N={Ncur}")
        if L == 1 and table is not None:
            table["f0"], table["fT"], table["gamma"] = Fraction(c0, N), Fraction(cT, N), Fraction(G, N)
            table["B1"] = Fraction(Bp, N)
        if L == 3 and table is not None:
            table["f03"], table["fT3"], table["B3"] = Fraction(c0, N), Fraction(cT, N), Fraction(Bp, N)
        if linear_C is not None:
            rho = Fraction(1 + S[N - 1], N)
            k = 0
            while b ** k < 1 / rho:
                k += 1
            lb = math.log(1 / rho, b)
            rhs = rho * (L + 1 + lb + (linear_C / (b - 1)) * (1 + (L + 3 + math.log(N, b)) / N))
            check(Bp / N <= float(rhs) * (1 + 1e-12), f"{name}: linear-mass rate")
        # Proposition 6.1 / Theorem 6.3: bad count of each complete gap is min(g_k, lambda_k)
        prev = 0
        for m in sup:
            if m > N:
                break
            g = m - prev
            lam = lam_gap(orb.W_at[m], b, M, L, sg)
            bad_in_gap = sum(orb.badp[L][n] for n in range(prev, m))
            check(bad_in_gap == min(g, lam), f"{name}: gap bad count")
            # bad shifts are the last ones in the gap
            check(all(orb.badp[L][n] == (m - n <= lam) for n in range(prev, m)), f"{name}: tail position")
            # sign constant on the gap and equal to sign(V_k)
            V = orb.W_at[m]
            check(all(orb.nonneg[n] == (V > 0 or (V == 0 and sg >= 0)) for n in range(prev, m)),
                  f"{name}: sign on gap")
            prev = m
    # Lemma 6.2: dominance sign(V_k) = sign(a(m_k)) for all complete gaps
    dom_fail = 0
    for m in sup:
        if m > N:
            break
        if (orb.W_at[m] > 0) != (a[m] > 0):
            dom_fail += 1
    if table is not None:
        table["dom_fail"] = dom_fail
        table["alpha"] = alpha
    return orb


def H_kappa(b, H):
    """kappa_{b,H} = ceil(log_b(bH/(b-1))) - 1 (co-infinite support)."""
    x = Fraction(b * H, b - 1)
    k = 0
    while b ** k < x:
        k += 1
    return max(0, k - 1)


def section5to7():
    N = 10000
    rows = []
    specs = [
        ("sum b^-k^2", 2, fam_squares, Fraction(1), {"H": 1}),
        ("sum b^-k^2", 10, fam_squares, Fraction(1), {"H": 1}),
        ("Theta_3(1/b)-1", 2, lambda M: fam_squares(M, 2), Fraction(1), {"H": 2}),
        ("Theta_3(1/b)-1", 3, lambda M: fam_squares(M, 2), Fraction(1), {"H": 2, "exact_prop": False}),
        ("E_b (pentagonal)", 2, fam_pentagonal, Fraction(1, 2), {"H": 1, "linear_C": 1}),
        ("E_b (pentagonal)", 3, fam_pentagonal, Fraction(1, 2), {"H": 1, "exact_prop": True, "linear_C": 1}),
        ("E_b (pentagonal)", 10, fam_pentagonal, Fraction(1, 2), {"H": 1, "exact_prop": True}),
        ("E_b^3 (Jacobi)", 2, fam_jacobi, Fraction(1, 2), {"linear_C": 4}),
        ("E_b^3 (Jacobi)", 10, fam_jacobi, Fraction(1, 2), {"linear_C": 4}),
        ("two-progression s=3,t=1", 2, lambda M: fam_two_progression(M, 3, 1), Fraction(1, 3), {"H": 1}),
        ("two-progression s=3,t=1", 3, lambda M: fam_two_progression(M, 3, 1), Fraction(1, 3), {"H": 1, "exact_prop": True}),
        ("two-progression s=10,t=4", 2, lambda M: fam_two_progression(M, 10, 4), Fraction(2, 5), {"H": 1}),
        ("two-progression s=10,t=4, signs swapped", 2, lambda M: fam_two_progression(M, 10, 4, -1), Fraction(3, 5), {"H": 1}),
        ("squares, signs (+,-,-)", 2, lambda M: fam_periodic_squares(M, [1, -1, -1]), Fraction(1, 3), {"H": 1}),
        ("squares, signs (+,+,-,-,-)", 2, lambda M: fam_periodic_squares(M, [1, 1, -1, -1, -1]), Fraction(2, 5), {"H": 1}),
    ]
    for name, b, fam, alpha, kw in specs:
        tab = {}
        analyse(name, b, fam, alpha, N, table=tab, **kw)
        check(tab["dom_fail"] == 0, f"{name}: dominance")
        rows.append((name, b, tab))
    print(f"[5-7] Theorem 5.2, Prop 6.1, Lemma 6.2, Thm 6.3, Cor 6.4 checked at every N <= {N};"
          " Theorem 5.3 at N in {100, 1000, 2500, 5000, 10000}; all truncations certified")
    print("      Table 7.1 (N = 10000; f for one digit and for words of length 3):")
    print("      | series | b | alpha | f_0 | f_{b-1} | f_{0^3} | f_{(b-1)^3} | gamma+ | B'_1/N |")
    for name, b, t in rows:
        print(f"      | {name} | {b} | {t['alpha']} | {float(t['f0']):.4f} | {float(t['fT']):.4f} | "
              f"{float(t['f03']):.4f} | {float(t['fT3']):.4f} | {float(t['gamma']):.4f} | {float(t['B1']):.4f} |")
    TABLE71.extend(rows)

    # Proposition 6.5: exactness and the two-sided bound for +-1 coefficients, b >= 3
    for b in (3, 5, 10):
        for a in (fam_pentagonal(3070), fam_two_progression(3070, 3, 1), fam_periodic_squares(3070, [1, -1])):
            orb = Orbit(b, a, 3070, 3000)
            for L in (2, 3, 4):
                prev = 0
                lo = hi = 0
                for m in orb.support:
                    if m > 3000:
                        break
                    g = m - prev
                    lam = lam_gap(orb.W_at[m], b, 3070, L)
                    check(L - 1 <= lam <= L, "Prop 6.5: L-1 <= lambda_k <= L")
                    lo += min(g, L - 1)
                    hi += min(g, L)
                    prev = m
                Nk = prev
                cnt = orb.word_counts(Nk, L)
                other = Nk - cnt.get(0, 0) - cnt.get(b ** L - 1, 0)
                check(lo <= other <= hi, "Prop 6.5 two-sided")
    # exact zero tails with an exactly truncated finite series (eps_sign = 0)
    for b in (2, 3, 10):
        a = {1: 1, 4: -1, 9: 1}
        orb = Orbit(b, a, 40, 30, eps_sign=0)
        for n in range(30):
            Tn = sum(Fraction(c, b ** (m - n)) for m, c in a.items() if m > n)
            check(orb.nonneg[n] == (Tn >= 0), "exact sign incl. T_n = 0")
            if n >= 9:
                check(Tn == 0 and orb.word(n, 3) == 0, "T_n = 0 reads 0^L")
        for L in (1, 2, 3):
            P = sum(1 for n in range(30) if orb.nonneg[n] and not orb.bad[L][n])
            c0 = orb.word_counts(30, L).get(0, 0)
            B = sum(orb.bad[L][:30])
            check(P <= c0 <= P + B, "Thm 5.2 with exact zero tails")
    print("      exact zero tails (eps_sign = 0): sign and Theorem 5.2 checks pass")
    print("      Prop 6.5: L-1 <= lambda_k <= L and the two-sided other-word count hold (b=3,5,10; L=2,3,4)")

    # lacunary alternating series: oscillation [1/3, 2/3]
    print("      Lacunary sum (-1)^k b^(-2^k): gamma+(2^K) and f_0(2^K)")
    for b in (2, 3):
        Nmax = 2 ** 14
        orb = analyse("lacunary", b, fam_lacunary, None, Nmax, H=1, Ls=(1, 2))
        line = []
        G = 0
        c0 = 0
        marks = {2 ** K: K for K in range(4, 15)}
        for n in range(Nmax):
            G += orb.nonneg[n]
            c0 += orb.digits[n] == 0
            if n + 1 in marks:
                K = marks[n + 1]
                pred = Fraction(2 ** (K + 1) - 2, 3) if K % 2 == 0 else Fraction(2 ** K - 2, 3)
                check(G == pred, f"lacunary gamma formula K={K}")
                line.append((K, Fraction(G, 2 ** K), Fraction(c0, 2 ** K)))
                LACUNARY.append((b, K, Fraction(G, 2 ** K), Fraction(c0, 2 ** K)))
        print("       b=%d: " % b + ", ".join(f"K={K}: {float(g):.5f}/{float(f):.5f}" for K, g, f in line if K >= 10))


TABLE71 = []
LACUNARY = []


# ---------------------------------------------------------------------------
# Section 7: displayed identities
# ---------------------------------------------------------------------------

def section7_identities():
    # pentagonal gaps
    for k in range(1, 20001):
        Pm, Pp = k * (3 * k - 1) // 2, k * (3 * k + 1) // 2
        check(Pp - Pm == k, "pentagonal inner gap")
        check(Pm - (k - 1) * (3 * k - 2) // 2 == 2 * k - 1, "pentagonal outer gap")
    # two-progression gaps
    for s, t in ((3, 1), (4, 2), (10, 4), (7, 3), (12, 2)):
        for k in range(1, 3001):
            u, v = (s * k * k - t * k) // 2, (s * k * k + t * k) // 2
            u1 = (s * (k + 1) ** 2 - t * (k + 1)) // 2
            check(2 * u == s * k * k - t * k and 2 * v == s * k * k + t * k, "integrality")
            check(v - u == t * k, "v-u")
            check(2 * (u1 - v) == (s - t) * (2 * k + 1), "u_{k+1}-v_k")
        check((s - t) // 2 >= 1, "u_1 >= 1")
    # Jacobi gaps
    for k in range(1, 5001):
        check(k * (k + 1) // 2 - (k - 1) * k // 2 == k, "triangular gap")
    # geometric-gap limits: alternating signs, ratio lam -> [1/(lam+1), lam/(lam+1)]
    for lam in (2, 3, 5):
        K = 40
        num_even = sum(lam ** k for k in range(0, K + 1) if k % 2 == K % 2)
        den = sum(lam ** k for k in range(0, K + 1))
        check(abs(Fraction(num_even, den) - Fraction(lam, lam + 1)) < Fraction(1, lam ** (K - 1)), "geometric limit")
    # Lemma 6.2(d): H > (b-1) b^(g-1) can reverse the sign with a finite support
    for b in (2, 3, 10):
        for g in (1, 2, 3):
            H = (b - 1) * b ** (g - 1) + 1
            J = 0
            V = Fraction(1)
            while V >= 0:
                V -= Fraction(H, b ** (g + J))
                J += 1
                check(J < 200, "sharpness search")
            # boundary H = (b-1) b^(g-1) with full tail gives V = 0 exactly
            Hb = (b - 1) * b ** (g - 1)
            check(1 - Fraction(Hb, b ** g) / (1 - Fraction(1, b)) == 0, "boundary equality")
            SHARP.append((b, g, H, J))
    print("[7] Lemma 6.2(d) sign reversal for H=(b-1)b^(g-1)+1: " +
          ", ".join(f"(b={b},g={g}): J={J}" for b, g, H, J in SHARP))
    print("[7] displayed gap identities (pentagonal, triangular, two-progression, geometric limits) pass")


# ---------------------------------------------------------------------------
# Section 8: prescribed limits and limit intervals
# ---------------------------------------------------------------------------

def section8():
    # Beatty identity: sum_{k<=K} beta(k)(2k-1) = alpha K^2 + E, |E| < 2K-1
    for alpha in (Fraction(0), Fraction(1), Fraction(1, 3), Fraction(2, 5), Fraction(5, 7), Fraction(1, 2)):
        Ssum = 0
        for K in range(1, 3001):
            Ssum += beatty_bit(K, alpha) * (2 * K - 1)
            E = Ssum - alpha * K * K
            frac_sum = sum(Fraction(k * alpha.numerator % alpha.denominator, alpha.denominator) for k in range(1, K)) if K <= 60 else None
            if frac_sum is not None:
                fK = Fraction(K * alpha.numerator % alpha.denominator, alpha.denominator)
                check(E == 2 * frac_sum - (2 * K - 1) * fK, "Abel formula for E")
            check(abs(E) < 2 * K - 1 or (K == 1 and E == 0), f"Beatty bound alpha={alpha} K={K}")
    Ssum = 0
    for K in range(1, 3001):
        Ssum += beatty_bit(K, "golden") * (2 * K - 1)
        lo = golden_times(K * K)                          # alpha K^2 in (lo, lo + 2^-21)
        hi = lo + Fraction(1, 2 ** 21)
        check(Ssum - (2 * K - 1) < lo and hi < Ssum + (2 * K - 1), f"golden Beatty K={K}")

    # Theorem 8.1: |f_{0^L}(N) - alpha| <= ((L+4) sqrt N + L)/N at every N, several bases
    res81 = []
    for alpha in (Fraction(1, 3), Fraction(2, 5), "golden"):
        for b in (2, 3, 10):
            Nmax = 6000
            a, M, sg = truncate_before_support(lambda MM: fam_beatty_squares(MM, alpha), Nmax, b)
            orb = Orbit(b, a, M, Nmax, certify=True, eps_sign=sg)
            check(orb.uncertified == 0, "certificate z_alpha")
            for L in (1, 2, 3, 4):
                c0 = 0
                G = 0
                worst = 0.0
                for n in range(Nmax):
                    c0 += orb.word(n, L) == 0
                    G += orb.nonneg[n]
                    Nc = n + 1
                    if alpha == "golden":
                        # |G - alpha Nc| <= 4 sqrt(Nc): alpha Nc in (lo, lo+1/2)
                        lo = golden_times(Nc)
                        dev = max(abs(G - lo), abs(G - lo - Fraction(1, 2 ** 21)))
                        check(dev * dev <= 16 * Nc, "Gamma+ golden")
                        dev0 = max(abs(c0 - lo), abs(c0 - lo - Fraction(1, 2 ** 21)))
                        check(dev0 <= L or (dev0 - L) ** 2 <= (L + 4) ** 2 * Nc, "Thm 8.1 golden")
                        val = float(dev0) / ((L + 4) * math.sqrt(Nc) + L)
                    else:
                        dev = abs(G - alpha * Nc)
                        check(dev * dev <= 16 * Nc, "Gamma+ bound 4 sqrt N")
                        dev0 = abs(c0 - alpha * Nc)
                        check(dev0 <= L or (dev0 - L) ** 2 <= (L + 4) ** 2 * Nc, "Thm 8.1")
                        val = float(dev0) / ((L + 4) * math.sqrt(Nc) + L)
                    worst = max(worst, val)
                if L == 1:
                    res81.append((alpha, b, float(Fraction(c0, Nmax)), worst))
    print("[8] Theorem 8.1 at every N <= 6000 (b = 2, 3, 10; L = 1..4):")
    for alpha, b, f, w in res81:
        al = "golden" if alpha == "golden" else str(alpha)
        print(f"      alpha={al} b={b}: f_0(6000)={f:.4f}, max ratio |f_0-alpha|/bound = {w:.3f}")
    RES81.extend(res81)

    # Theorem 8.2: interval [1/5, 7/10]
    Nmax = 2 ** 15
    a, M, sg = truncate_before_support(fam_interval_squares, Nmax, 2)
    orb = Orbit(2, a, M, Nmax, certify=True, eps_sign=sg)
    check(orb.uncertified == 0, "certificate interval example")
    G = 0
    c0 = 0
    for n in range(Nmax):
        G += orb.nonneg[n]
        c0 += orb.digits[n] == 0
        Nc = n + 1
        up = G - INTERVAL_HI * Nc
        dn = INTERVAL_LO * Nc - G
        check((up <= 0 or up * up <= 196 * Nc) and (dn <= 0 or dn * dn <= 196 * Nc), "Thm 8.2 envelope")
        check(abs(c0 - G) <= 1 + isqrt(Nc - 1), "Thm 8.2 digit vs sign count")
    # combinatorial Gamma+ at phase ends K_{i+1}^2 via the dominance identity
    ends = []
    Ssum = 0
    phase_ends = {1 << ((i + 1) ** 2): i for i in range(0, 4)}
    for k in range(1, (1 << 16) + 1):
        Ssum += beatty_bit(k, interval_target(k)) * (2 * k - 1)
        if k in phase_ends:
            i = phase_ends[k]
            Kn = k
            Kp = 0 if i == 0 else 1 << (i * i)
            g = Fraction(Ssum, Kn * Kn)
            if i % 2 == 0:
                check(g >= INTERVAL_HI - Fraction(Kp * Kp, Kn * Kn) - Fraction(4, Kn), "phase end (even)")
            else:
                check(g <= INTERVAL_LO + Fraction(Kp * Kp, Kn * Kn) + Fraction(4, Kn), "phase end (odd)")
            ends.append((i, Kn * Kn, g))
            if Kn * Kn <= Nmax:
                Gorb = sum(orb.nonneg[:Kn * Kn])
                check(Gorb == Ssum, "orbit sign count = combinatorial count")
    print("      Theorem 8.2, [1/5, 7/10]: envelope at every N <= 2^15; phase ends:")
    for i, Nn, g in ends:
        print(f"      i={i}: N=K_{i+1}^2={Nn}: gamma+ = {float(g):.6f}")
    ENDS.extend(ends)


RES81 = []
SHARP = []
ENDS = []


def main():
    for f in (section1, section2, section3, section5to7, section7_identities, section8):
        t0 = time.time()
        f()
        print(f"    ({f.__name__}: {time.time() - t0:.1f}s)")
    el = time.time() - START
    print(f"ALL {CHECKS} CHECKS PASSED in {el:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
