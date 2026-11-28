#!/usr/bin/env python3
"""
Phase 25 Addendum Track J: Dirichlet GRH, Paper VI planting, GF-22 moving
windows and the short-window exponent in Mira Cult's local-limit argument.

Companion script for notes/phase25/grh-lambert-windows.md.

Check categories (kept strictly separate):
  [exact]  exact integer / Fraction statements (parameter algebra, identities,
           lemmas checked exhaustively or on seeded random instances).
  [cert]   finite certificates: exact digit enclosures and factorizations that
           prove a finite statement (e.g. "w occurs in this window").
  [num]    floating-point measurements.  They are consistent with, but can
           never test, the Generalized Riemann Hypothesis or any limit law.

Nothing here verifies GRH.  GRH is an external, unproved hypothesis; every
result of the note that uses it is labelled Conditional.

Standard library only.  Exit code 0 iff every check passes.
Usage:  python -B scripts/phase25_grh_windows.py
"""

from __future__ import annotations

import math
import random
import sys
import time
from fractions import Fraction
from math import gcd, isqrt

COUNTS = {"exact": 0, "cert": 0, "num": 0}


def check(kind: str, cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(f"[{kind}] FAILED: {msg}")
    COUNTS[kind] += 1


def section(title: str) -> None:
    print(f"\n=== {title} ===")


# ---------------------------------------------------------------------------
# Rational enclosures of logarithms (outward rounded, 12 decimals)
# ---------------------------------------------------------------------------
LN2_LO, LN2_HI = Fraction(693147180559, 10**12), Fraction(693147180560, 10**12)
LN3_LO, LN3_HI = Fraction(1098612288668, 10**12), Fraction(1098612288669, 10**12)
LN10_LO, LN10_HI = Fraction(2302585092994, 10**12), Fraction(2302585092995, 10**12)
LN13_LO, LN13_HI = Fraction(2564949357461, 10**12), Fraction(2564949357462, 10**12)


def ln_upper_int(n: int) -> Fraction:
    """Rational upper bound for ln n (n >= 1) via bit length."""
    return n.bit_length() * LN2_HI


def ln_lower_int(n: int) -> Fraction:
    """Rational lower bound for ln n (n >= 1)."""
    return (n.bit_length() - 1) * LN2_LO


# ---------------------------------------------------------------------------
# Integer utilities
# ---------------------------------------------------------------------------
def iroot(n: int, k: int) -> int:
    """floor(n^(1/k)) for n >= 0, k >= 1."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x


def iroot_ceil(n: int, k: int) -> int:
    r = iroot(n, k)
    return r if r ** k == n else r + 1


def sieve_primes(limit: int) -> bytearray:
    s = bytearray([1]) * (limit + 1)
    s[0] = s[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if s[p]:
            s[p * p:: p] = bytearray(len(range(p * p, limit + 1, p)))
    return s


def spf_sieve(limit: int) -> list:
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for m in range(p * p, limit + 1, p):
                if spf[m] == m:
                    spf[m] = p
    return spf


def factor_spf(n: int, spf: list) -> dict:
    f = {}
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        f[p] = e
    return f


SMALL_PRIMES = [p for p in range(2, 1000) if all(p % d for d in range(2, isqrt(p) + 1))]
MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 3.3e24 (bases = first 13 primes)."""
    if n < 2:
        return False
    for p in SMALL_PRIMES[:40]:
        if n % p == 0:
            return n == p
    assert n < 3317044064679887385961981, "outside deterministic MR range"
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_brent(n: int, seed: int) -> int:
    rng = random.Random(seed)
    if n % 2 == 0:
        return 2
    while True:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g = r = q = 1
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
        if g != n:
            return g


def factorize(n: int) -> dict:
    """Full factorization; trial division by primes < 1000, then MR + Brent."""
    f: dict = {}
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    seed = 1
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime(m):
            f[m] = f.get(m, 0) + 1
            continue
        r = iroot(m, 2)
        if r * r == m:
            stack += [r, r]
            continue
        d = pollard_brent(m, seed)
        seed += 1
        stack += [d, m // d]
    return f


def tau_from_fac(fac: dict) -> int:
    t = 1
    for e in fac.values():
        t *= e + 1
    return t


def crt(residues: list) -> tuple:
    """residues: list of (r, m) with pairwise coprime m; returns (r, M)."""
    r, M = 0, 1
    for ri, mi in residues:
        t = ((ri - r) * pow(M, -1, mi)) % mi
        r, M = r + M * t, M * mi
    return r % M, M


# ---------------------------------------------------------------------------
# Z[omega] arithmetic, omega = e^{2 pi i/3}, omega^2 = -1 - omega
# ---------------------------------------------------------------------------
def zw_mul(a: tuple, b: tuple) -> tuple:
    (x1, y1), (x2, y2) = a, b
    return (x1 * x2 - y1 * y2, x1 * y2 + y1 * x2 - y1 * y2)


ZW_POW = {0: (1, 0), 1: (0, 1), 2: (-1, -1)}
CHI7_EXP = {1: 0, 3: 1, 2: 2, 6: 0, 4: 1, 5: 2}  # chi(3) = omega, chi = 0 on 7Z


def phi_plus(z: tuple) -> int:  # 2 Re
    return 2 * z[0] - z[1]


def phi_minus(z: tuple) -> int:  # (2/sqrt 3) Im
    return z[1]


def c_cubic7_from_fac(fac: dict) -> tuple:
    """c = 1 * chi for the cubic character mod 7 with chi(3) = omega (GF-22 Lemma 1.2)."""
    z = (1, 0)
    for p, e in fac.items():
        if p == 7:
            continue
        r = p % 7
        if r in (1, 6):
            z = (z[0] * (e + 1), z[1] * (e + 1))
        elif r in (3, 4):
            loc = {0: (1, 0), 1: (1, 1), 2: (0, 0)}[e % 3]
            z = zw_mul(z, loc)
        else:  # r in (2, 5): 1 + omega^2 = -omega
            loc = {0: (1, 0), 1: (0, -1), 2: (0, 0)}[e % 3]
            z = zw_mul(z, loc)
        if z == (0, 0):
            return z
    return z


def c_plus_big(n: int) -> int:
    return phi_plus(c_cubic7_from_fac(factorize(n)))


def c_chi4_from_fac(fac: dict) -> int:
    """(1 * chi_{-4})(n) = r_2(n)/4."""
    v = 1
    for p, e in fac.items():
        if p % 4 == 1:
            v *= e + 1
        elif p % 4 == 3:
            v *= 1 if e % 2 == 0 else 0
    return v


# ---------------------------------------------------------------------------
# S1. Paper VI planting parameters (paper.tex, \label{prop:planting}, 'Planted occurrences')
# ---------------------------------------------------------------------------
def paper6_params(nu_star: Fraction, a: Fraction) -> tuple:
    theta = min(Fraction(1, 4), (a - nu_star) / 2)
    nu = (nu_star + a - theta) / 2
    beta = Fraction(1, 2) + 1 / (4 * (a - theta))
    return theta, nu, beta


def s1_paper6_parameters() -> None:
    section("S1 [exact] Paper VI planting parameters for nu_* = 1/2 (GRH), 53/100 (Kumchev), 7/12 (PPS)")
    half = Fraction(1, 2)
    for nu_star in (half, Fraction(53, 100), Fraction(7, 12)):
        n_ok = 0
        grid = [nu_star + Fraction(k, 2000) for k in range(1, 2001) if nu_star + Fraction(k, 2000) < 1]
        grid += [nu_star + Fraction(1, 10**9), Fraction(1)]
        for a in grid:
            theta, nu, beta = paper6_params(nu_star, a)
            check("exact", 0 < theta <= Fraction(1, 4), f"theta in (0,1/4] at a={a}")
            check("exact", theta < half, "Lemma 'small factors' needs 0<theta<1/2")
            check("exact", nu_star < nu < a - theta, f"nu_* < nu < a-theta at a={a}")
            check("exact", nu < 1, "nu < 1")
            check("exact", a - theta > half, f"a - theta > 1/2 at a={a}")
            check("exact", 1 / (2 * (a - theta)) < beta < 1, f"1/(2(a-theta)) < beta < 1 at a={a}")
            check("exact", (a - theta) * beta > half, "far tail: (a-theta)beta > 1/2 so 2sqrt(N) <= Y^beta")
            check("exact", 1 - theta > half, "p > X >> N^{1-theta} exceeds 2 sqrt(3N)")
            n_ok += 1
        print(f"  nu_* = {nu_star}: all parameter constraints hold on {n_ok} exponents a in (nu_*, 1]")
    # Boundary a = nu_* = 1/2: the construction degenerates.
    theta = min(Fraction(1, 4), (half - half) / 2)
    check("exact", theta == 0, "at a = 1/2 the small-factor exponent theta collapses to 0")
    check("exact", half - theta == half, "at a = 1/2, a - theta = 1/2: the far-tail exponent beta would be 1")
    check("exact", half < Fraction(53, 100) < Fraction(7, 12), "GRH range strictly contains both unconditional ranges")
    print("  boundary a = 1/2: theta = 0 and a - theta = 1/2 (beta = 1) -> the method stops exactly at 1/2")


# ---------------------------------------------------------------------------
# S2. GRH error-term algebra and the (P_nu) threshold (Theorem A, Cor. A.3)
# ---------------------------------------------------------------------------
def s2_grh_algebra() -> None:
    section("S2 [exact]/[num] explicit-formula bookkeeping and short-interval thresholds")
    # T = sqrt(x): log(q x T) <= (3/2) log(q x)  <=>  q x^{3/2} <= (q x)^{3/2}, true for q >= 1.
    for q in (1, 2, 3, 4, 5, 7, 30, 1000, 10**6):
        for x in (2, 10, 10**3, 10**9, 10**30):
            # (q x)^{3/2} >= q x^{3/2}  <=>  q^3 x^3 >= q^2 x^3  (squared)
            check("exact", (q * x) ** 3 >= q * q * x ** 3, "log(qxT) <= 1.5 log(qx) at T = sqrt x")
    # Zero-sum bookkeeping: sum_{k<=K} log(q(k+2))/k <= log(q(K+2)) (1 + log K)
    for q in (1, 3, 4, 7, 100, 10**5):
        for K in (1, 2, 5, 10, 100, 1000, 10**4):
            lhs = math.fsum(math.log(q * (k + 2)) / k for k in range(1, K + 1))
            rhs = math.log(q * (K + 2)) * (1 + math.log(K))
            check("num", lhs <= rhs + 1e-9, f"zero-sum harmonic bookkeeping q={q} K={K}")
    # Where does the GRH error sqrt(X) log^2 X fall below X^nu?  (constant 1; illustration only)
    print("  least X (constant C=1) with X^nu >= sqrt(X) * (log X)^2   [num, illustration]:")
    for nu in (0.51, 0.55, 0.6, 7 / 12, 0.75):
        lo, hi = 1.0, 1e6  # in units of log X
        f = lambda L: (nu - 0.5) * L - 2 * math.log(L)
        # find the last crossing: f increasing for L > 2/(nu-1/2)
        L0 = 2 / (nu - 0.5)
        lo = L0
        while f(hi) < 0:
            hi *= 2
        for _ in range(200):
            mid = (lo + hi) / 2
            if f(mid) >= 0:
                hi = mid
            else:
                lo = mid
        check("num", f(hi) >= 0 and hi > L0, "bisection bracket")
        print(f"    nu = {nu:.4f}: log10 X >= {hi / math.log(10):10.1f}")
    print("  (so the GRH short-interval estimate is vacuous at every computationally accessible X)")


# ---------------------------------------------------------------------------
# S3. Prime powers (Lemma A.1): #{(p,k): k>=2, p^k <= x} <= isqrt(x) + iroot(x,3)*floor(log2 x)
# ---------------------------------------------------------------------------
def s3_prime_powers(prime_flags: bytearray) -> None:
    section("S3 [exact] prime-power count bound used to pass from psi to theta and pi")
    LIM = 10**6
    pp = []
    for p in range(2, isqrt(LIM) + 1):
        if prime_flags[p]:
            v = p * p
            while v <= LIM:
                pp.append(v)
                v *= p
    pp.sort()
    for idx, v in enumerate(pp):
        cnt = idx + 1  # number of higher prime powers <= v (left-continuous jump point)
        rhs = isqrt(v) + iroot(v, 3) * (v.bit_length() - 1)
        check("exact", cnt <= rhs, f"prime-power count bound at x={v}")
    print(f"  bound verified at all {len(pp)} jump points x <= 10^6 (exhaustive; the bound is nondecreasing)")


# ---------------------------------------------------------------------------
# S4. Finite consistency of psi(x;q,u) with the GRH-size error  [num]
# ---------------------------------------------------------------------------
def s4_psi_measurements(prime_flags: bytearray) -> None:
    section("S4 [num] psi(x;q,u) vs x/phi(q): finite consistency with an error sqrt(x) log^2 x (not a test of GRH)")
    LIM = 2 * 10**6
    lam = {}
    for p in range(2, LIM + 1):
        if prime_flags[p]:
            lp = math.log(p)
            v = p
            while v <= LIM:
                lam[v] = lp
                v *= p
    keys = sorted(lam)
    moduli = (3, 4, 5, 7, 8, 11, 12, 13)
    worst = 0.0
    for q in moduli:
        units = [u for u in range(1, q) if gcd(u, q) == 1]
        phq = len(units)
        psi = {u: 0.0 for u in units}
        ki = 0
        for x in range(10**4, LIM + 1, 10**4):
            while ki < len(keys) and keys[ki] <= x:
                n = keys[ki]
                r = n % q
                if r in psi:
                    psi[r] += lam[n]
                ki += 1
            for u in units:
                err = abs(psi[u] - x / phq)
                ratio = err / (math.sqrt(x) * math.log(x) ** 2)
                worst = max(worst, ratio)
                check("num", ratio < 1.0, f"|psi(x;{q},{u}) - x/phi| < sqrt(x) log^2 x at x={x}")
    print(f"  max over q in {moduli}, x <= 2e6 of |E|/(sqrt x log^2 x) = {worst:.5f}")
    # (P_nu) finite measurement for q0 = 4, a0 = 1 at nu = 0.55, constant c_P = 1/(2 phi(q0)) = 1/4
    worst_ratio = 10.0
    for X in range(10**5, 19 * 10**5 + 1, 10**4):
        Y = math.ceil(X ** 0.55)
        cnt = sum(1 for p in range(X + 1, X + Y + 1) if prime_flags[p] and p % 4 == 1)
        bound = Y / (4 * math.log(X))
        worst_ratio = min(worst_ratio, cnt / bound)
        check("num", cnt >= bound, f"(P_nu) measurement at X={X}")
    print(f"  #{{X<p<=X+X^0.55, p=1 mod 4}} / (Y/(4 log X)) >= {worst_ratio:.3f} for 1e5 <= X <= 1.9e6 (finite measurement)")


# ---------------------------------------------------------------------------
# S5. Lemma E.2: short-interval divisor sums in a progression (exact, seeded random + edge cases)
# ---------------------------------------------------------------------------
def s5_short_divisor_lemma() -> None:
    section("S5 [exact] Lemma E.2: sum_{X0<m<=X0+Z, m=c (D)} tau(m) <= 2 sqrt(X1) + (2Z/D) tau(g) (1 + log(X1)/2)")
    LIM = 300000
    tau = [0] * (LIM + 1)
    for d in range(1, LIM + 1):
        for m in range(d, LIM + 1, d):
            tau[m] += 1
    pref_cache = {}
    rng = random.Random(25010)
    cases = []
    for _ in range(2500):
        D = rng.choice([1, 2, 3, 4, 6, 12, 30, 210, 2310]) if rng.random() < 0.3 else rng.randint(1, 3000)
        c = rng.randrange(D) if rng.random() < 0.8 else 0
        Z = rng.randint(1, 60000)
        X0 = rng.randint(0, LIM - Z)
        cases.append((D, c, X0, Z))
    for D in (1, 2, 4, 8, 16, 64, 720):  # edge cases: c = 0 (g = D), short and long windows
        for Z in (1, 10, 1000, 100000):
            cases.append((D, 0, LIM - Z - 7, Z))
            cases.append((D, 0, 0, Z))
    worst = 0.0
    for D, c, X0, Z in cases:
        X1 = X0 + Z
        first = X0 + 1 + ((c - (X0 + 1)) % D)
        lhs = sum(tau[m] for m in range(first, X1 + 1, D))
        g = gcd(c, D)
        tg = tau[g] if g <= LIM else len([d for d in range(1, g + 1) if g % d == 0])
        rhs_lower = 2 * isqrt(X1) + Fraction(2 * Z, D) * tg * (1 + ln_lower_int(X1) / 2)
        check("exact", lhs <= rhs_lower, f"Lemma E.2 at D={D}, c={c}, X0={X0}, Z={Z}")
        worst = max(worst, lhs / float(rhs_lower))
    print(f"  verified on {len(cases)} instances (rigorous: rational lower bound for the right side); max lhs/rhs = {worst:.4f}")
    # gcd structure used in Step 6': gcd(A a0 + h, A q') | gcd(h, A) * gcd(A a0 + h, q') when gcd(A, q') = 1
    for _ in range(4000):
        A = rng.randint(1, 5000)
        qp = rng.randint(1, 5000)
        if gcd(A, qp) != 1:
            continue
        a0 = rng.randrange(qp)
        h = rng.randint(1, 10**6)
        lhs = gcd(A * a0 + h, A * qp)
        rhs = gcd(h, A) * gcd(A * a0 + h, qp)
        check("exact", rhs % lhs == 0, "gcd structure in the window tail estimate")


# ---------------------------------------------------------------------------
# S6. GF-22 CRT modulus regimes q'(N) = N^{o(1)} for L_+(b), cubic chi mod 7
# ---------------------------------------------------------------------------
def gf22_modulus(E: int, W: int, M: int, b: int, prime_flags: bytearray, K0: int = 512) -> dict:
    """Window version of GF-22 Step 2' for Phi_+ on the cubic character mod 7.

    kappa = Phi_+(1 + omega) = 1, so f = e = 0, W' = W; tau = bM + 1, A = 13^{bM}.
    L = least integer with b^L >= K0 * C_Phi * tau(A) * tau(q) * (1 + ln(6 A N))^2,
    evaluated with a rational UPPER bound for the logarithm (so L is admissible).
    """
    C_Phi, tau_q, d, ell, A0, q = 2, 2, 3, 13, 1, 7
    tau_val = b * M + 1
    A = ell ** (tau_val - 1)
    tauA = tau_val  # tau(13^{bM}) = bM + 1
    ln6AN_hi = LN2_HI + LN3_HI + (tau_val - 1) * LN13_HI + E * LN10_HI
    target = K0 * C_Phi * tauA * tau_q * (1 + ln6AN_hi) ** 2
    L = 0
    while b ** L < target:
        L += 1
    s = W + L
    P0 = L + W + math.ceil(2 * s * math.log2(d + 1)) + A0 + ell + q
    fam = []
    p = P0 + 1
    while len(fam) < s:
        if prime_flags[p] and p % 7 == 3:
            fam.append(p)
        p += 1
    qprime = q
    for pj in fam:
        qprime *= pj ** d
    return {"L": L, "s": s, "P0": P0, "pmax": fam[-1], "qprime": qprime, "A": A}


def s6_gf22_regimes(prime_flags: bytearray) -> None:
    section("S6 [exact]/[num] GF-22 window modulus q'(N) = q*prod p_j^3 for L_+(2): N^{o(1)} only asymptotically")
    Es = [10, 30, 100, 300, 1000, 3000, 10**4, 3 * 10**4, 10**5, 10**6]
    alphas = (Fraction(55, 100), Fraction(6, 10), Fraction(3, 4), Fraction(9, 10))
    rows = []
    prev_ratio = None
    for E in Es:
        R = gf22_modulus(E, W=2, M=3, b=2, prime_flags=prime_flags)
        dq = len(str(R["qprime"]))  # 10^{dq-1} <= q' < 10^{dq}
        dA = len(str(R["A"]))
        ratio = dq / E
        check("exact", R["s"] == 2 + R["L"], "s = W' + f + L")
        check("exact", all(R["qprime"] % (p ** 3) == 0 for p in (R["pmax"],)), "largest kill prime cubed divides q'")
        # Window inequality (illustration, GRH constant taken as 1):
        #   H/(A q') >= sqrt(N) * (ln(q' N))^2  with H = N^a, N = 10^E.
        # Sufficient (rigorous given the constant): a*E - dA - dq >= E/2 + 2*log10(ln(q'N)) + 1.
        lnqN_hi = (dq + E) * LN10_HI
        logterm = 2 * math.log10(float(lnqN_hi)) + 1
        holds = {}
        for a in alphas:
            holds[a] = (float(a) * E - dA - dq) >= E / 2 + logterm
        rows.append((E, R["L"], R["s"], R["pmax"], dq, ratio, holds))
        if prev_ratio is not None and E >= 100:
            check("num", ratio < prev_ratio, "log q'/log N decreasing in N")
        prev_ratio = ratio
    print("  log10 N | L  | s  | largest kill prime | digits(q') | digits(q')/log10 N | window ineq. holds for a = 0.55/0.6/0.75/0.9")
    for E, L, s, pmax, dq, ratio, holds in rows:
        flags = "/".join("Y" if holds[a] else "n" for a in alphas)
        print(f"  {E:>7} | {L:>2} | {s:>2} | {pmax:>18} | {dq:>10} | {ratio:>18.6f} | {flags}")
    by_E = {r[0]: r[6] for r in rows}
    for a in alphas:
        check("num", not by_E[100][a], f"illustrative constant-1 window inequality fails at N = 10^100 for a = {a}")
        check("num", by_E[10**6][a], f"illustrative constant-1 window inequality holds at N = 10^(10^6) for a = {a}")
    # For a fixed modulus (Paper VI) nothing grows: q0 is fixed and the threshold is the S2 one.
    print("  (Paper VI uses only the fixed modulus q0; GF-22 needs q' -> infinity with log q' << loglog N logloglog N)")


# ---------------------------------------------------------------------------
# S7. Phi additivity, the Q-basis argument, and non-additive counterexamples
# ---------------------------------------------------------------------------
def poly_mod(a: list, m: list) -> list:
    a = a[:]
    while len(a) >= len(m):
        coef = a[-1]
        if coef:
            shift = len(a) - len(m)
            for i, mc in enumerate(m):
                a[shift + i] -= coef * mc
        a.pop()
    return a


def poly_div_exact(a: list, m: list) -> list:
    a = a[:]
    out = [0] * (len(a) - len(m) + 1)
    for k in range(len(out) - 1, -1, -1):
        coef = a[k + len(m) - 1] // m[-1]
        out[k] = coef
        for i, mc in enumerate(m):
            a[k + i] -= coef * mc
    assert all(v == 0 for v in a), "inexact division"
    return out


def cyclotomic(h: int, cache: dict) -> list:
    if h in cache:
        return cache[h]
    num = [-1] + [0] * (h - 1) + [1]
    for d in range(1, h):
        if h % d == 0:
            num = poly_div_exact(num, cyclotomic(d, cache))
    cache[h] = num
    return num


def det_fraction(M: list) -> Fraction:
    M = [[Fraction(v) for v in row] for row in M]
    n, det = len(M), Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                for k in range(c, n):
                    M[r][k] -= f * M[c][k]
    return det


def s7_phi_additivity(spf: list) -> None:
    section("S7 [exact] additivity of Phi in GF-22 and non-additive counterexamples")
    rng = random.Random(25011)
    # (a) Phi_+ and Phi_- are additive; Phi(tau z) = tau Phi(z); kappa = Phi_pm(1 + omega) = 1.
    for _ in range(2000):
        z1 = (rng.randint(-10**6, 10**6), rng.randint(-10**6, 10**6))
        z2 = (rng.randint(-10**6, 10**6), rng.randint(-10**6, 10**6))
        s = (z1[0] + z2[0], z1[1] + z2[1])
        for Phi in (phi_plus, phi_minus):
            check("exact", Phi(s) == Phi(z1) + Phi(z2), "Phi additive")
            t = rng.randint(1, 50)
            check("exact", Phi((t * z1[0], t * z1[1])) == t * Phi(z1), "Phi(tau z) = tau Phi(z)")
    check("exact", phi_plus((1, 1)) == 1 and phi_minus((1, 1)) == 1, "kappa = Phi_pm(1+omega) = 1")
    # (b) closed form (GF-22 Lemma 1.2) against the divisor sum, n <= 3000
    for n in range(1, 3001):
        z = (0, 0)
        for d in range(1, n + 1):
            if n % d == 0 and d % 7:
                w = ZW_POW[CHI7_EXP[d % 7]]
                z = (z[0] + w[0], z[1] + w[1])
        check("exact", z == c_cubic7_from_fac(factor_spf(n, spf)) if n > 1 else z == (1, 0), f"closed form c(n), n={n}")
    # (c) value family: c_+(13^{V-1} u) = c_-(13^{V-1} u) = V for primes u = 3, 4 mod 7
    for u in (3, 11, 17, 31, 53, 59):
        for V in range(1, 8):
            z = c_cubic7_from_fac(factorize(13 ** (V - 1) * u))
            check("exact", phi_plus(z) == V and phi_minus(z) == V, f"value family u={u}, V={V}")
    # (d) Q-basis {(1+zeta_h)^j : j < phi(h)} of Q(zeta_h) for 3 <= h <= 30 (used to get kappa != 0)
    cache: dict = {}
    for h in range(3, 31):
        Ph = cyclotomic(h, cache)
        deg = len(Ph) - 1
        rows = []
        powj = [1]
        for j in range(deg):
            r = poly_mod(powj, Ph)
            rows.append(r + [0] * (deg - len(r)))
            nxt = [0] * (len(powj) + 1)
            for i, cf in enumerate(powj):
                nxt[i] += cf
                nxt[i + 1] += cf
            powj = nxt
        check("exact", det_fraction(rows) != 0, f"(1+zeta_{h})^j, j<phi({h}), is a Q-basis")
    print("  Phi_pm additive, kappa = 1, closed form to n = 3000, (1+zeta_h)^j basis for 3 <= h <= 30")
    # (e) A non-additive Phi with Phi(0) = 0 is not enough: Phi = indicator of nonzero.
    def phi_ind(z: tuple) -> int:
        return 0 if z == (0, 0) else 1

    check("exact", phi_ind((0, 0)) == 0 and phi_ind((1, 0)) == 1, "Phi_ind(0) = 0 and Phi_ind is nonzero")
    check("exact", phi_ind((1, 0)) + phi_ind((-1, 0)) != phi_ind((0, 0)),
          "Phi_ind(1) + Phi_ind(-1) = 2 != Phi_ind(0) = 0: Phi_ind is not additive")
    NMAX = 10**5
    spf_big = spf
    # chi_{-4}: digit n of F_2(1_{c != 0}) is 1_{n is a sum of two squares}; n = 3 mod 4 gives 0.
    a4 = [0] * (NMAX + 1)
    for n in range(1, NMAX + 1):
        a4[n] = 1 if (n == 1 or c_chi4_from_fac(factor_spf(n, spf_big)) != 0) else 0
    for n in range(3, NMAX + 1, 4):
        check("exact", a4[n] == 0, f"r_2(n) = 0 for n = 3 mod 4 (n={n})")
    digits4 = "".join(str(a4[n]) for n in range(1, NMAX + 1))
    check("exact", "1111" not in digits4, "word 1111 absent from F_2(1_{r_2>0}) (first 1e5 digits)")
    check("exact", "111" in digits4, "word 111 does occur (non-trivial sequence)")
    # cubic chi mod 7: n = 4 mod 8 has v_2(n) = 2 with 2 = 2 mod 7 in P', so c(n) = 0.
    a7 = [0] * (NMAX + 1)
    for n in range(1, NMAX + 1):
        a7[n] = 1 if (n == 1 or c_cubic7_from_fac(factor_spf(n, spf_big)) != (0, 0)) else 0
    for n in range(4, NMAX + 1, 8):
        check("exact", a7[n] == 0, f"c(n) = 0 for n = 4 mod 8 (n={n})")
    digits7 = "".join(str(a7[n]) for n in range(1, NMAX + 1))
    check("exact", "1" * 8 not in digits7, "word 1^8 absent from F_2(1_{c != 0}), cubic chi mod 7")
    check("exact", "1" * 7 in digits7, "word 1^7 does occur")
    # General mechanism: if chi(p) has exact order d >= 2 then c(p^{d-1}) = sum_{i<d} chi(p)^i = 0.
    for d in range(2, 13):
        # sum of the d-th roots of unity of a primitive d-th root zeta: test via polynomial identity
        # 1 + x + ... + x^{d-1} = (x^d - 1)/(x - 1) vanishes at every primitive d-th root (d >= 2)
        Pd = cyclotomic(d, cache)
        geom = [1] * d
        check("exact", all(v == 0 for v in poly_mod(geom, Pd)), f"Phi_d divides 1+x+...+x^(d-1), d={d}")
    print("  non-additive Phi = 1_{z != 0}: F_2 misses 1111 (chi_{-4}) and 1^8 (cubic chi mod 7); in base b >= 3 it misses the digit 2")


# ---------------------------------------------------------------------------
# S8. Finite moving-window instances of the GF-22 construction for L_+(2)
# ---------------------------------------------------------------------------
def certified_word_at(n: int, W: int, K: int = 64) -> tuple:
    """Return (word value, list of c_+(n+k), k=1..K) for x = L_+(2) = F_2(c_+) at start n.

    {2^n x} = {T_n}, T_n = sum_{k>=1} c_+(n+k) 2^{-k}.  The tail k > K is bounded by
    sum_{k>K} 2 tau(n+k) 2^{-k} with tau(m) <= 2 sqrt(m); for n >= 2K + 10 this is
    <= (4 (isqrt(2n) + 1) + 1) 2^{-K}.  Returns None if the enclosure straddles a cylinder edge.
    """
    assert n >= 2 * K + 10
    vals = [c_plus_big(n + k) for k in range(1, K + 1)]
    S = Fraction(sum(v * 2 ** (K - k) for k, v in enumerate(vals, start=1)), 2 ** K)
    B = Fraction(4 * (isqrt(2 * n) + 1) + 1, 2 ** K)
    lo, hi = S - B, S + B
    flo, fhi = lo - math.floor(lo), hi - math.floor(lo)
    if fhi >= 1:
        return None, vals
    wlo, whi = math.floor(flo * 2 ** W), math.floor(fhi * 2 ** W)
    if wlo != whi:
        return None, vals
    return wlo, vals


def s8_window_instances() -> None:
    section("S8 [cert] GF-22 moving-window construction: certified occurrences of 00 and 01 in L_+(2) inside prescribed windows [N, N+N^a)")
    kills = {-2: 3, -1: 2, 1: 5, 2: 11}  # offsets j -> kill primes in P' (chi(p) of order 3), v_p = 2
    qprime = 7 * 3 ** 3 * 2 ** 3 * 5 ** 3 * 11 ** 3
    check("exact", qprime == 251559000, "q' = 7 * prod p^3 = 251559000 (as in the GF-22 table)")
    for p in kills.values():
        check("exact", p % 7 in (2, 3, 4, 5), "kill primes lie in P' (chi(p) has order 3)")
        check("exact", c_cubic7_from_fac({p: 2}) == (0, 0), "local factor c(p^2) = 0")
    instances = [
        # (word, value M, A = 13^{2M}, V1 = 2M+1, N, a = num/den)
        ("00", 0, 1, 1, 10**17, (3, 5)),
        ("01", 1, 169, 3, 10**18, (7, 10)),
    ]
    W = 2
    for word, M, A, V1, N, (an, ad) in instances:
        H = iroot_ceil(N ** an, ad)  # H = ceil(N^{an/ad})
        check("exact", H ** ad >= N ** an and (H - 1) ** ad < N ** an, "H = ceil(N^a)")
        res = [(3 % 7, 7)]
        for j, p in kills.items():
            res.append((((p * p - j) * pow(A, -1, p ** 3)) % p ** 3, p ** 3))
        a0, mod = crt(res)
        check("exact", mod == qprime and gcd(a0, qprime) == 1, "residue class a0 mod q' is reduced")
        # u range: N <= A u - (W' + f + 1) < N + H with W' + f + 1 = 3
        ulo = -(-(N + 3) // A)
        uhi = (N + H + 2) // A
        first = ulo + ((a0 - ulo) % qprime)
        members = list(range(first, uhi + 1, qprime))
        primes = [u for u in members if is_prime(u)]
        found = None
        tried = 0
        for u in primes:
            tried += 1
            m0 = A * u
            n = m0 - 3
            check("cert", N <= n < N + H, "start lies in the prescribed window")
            for j in kills:
                check("cert", c_plus_big(m0 + j) == 0, f"kill position m0{j:+d} has c_+ = 0")
            check("cert", c_plus_big(m0) == V1, "value position c_+(A u) = V1")
            wval, vals = certified_word_at(n, W)
            if wval is None:
                continue
            check("cert", vals[0] == 0 and vals[1] == 0 and vals[2] == V1, "local pattern 0,0,V1 after start")
            if wval == M:
                found = (u, n, sum(1 for v in vals if v))
                break
        check("cert", found is not None, f"certified occurrence of {word} in [N, N+H)")
        u, n, nz = found
        print(f"  word {word}: N = 10^{len(str(N)) - 1}, H = ceil(N^({an}/{ad})) = {H}, class members = {len(members)}, "
              f"primes = {len(primes)}, primes tried = {tried}")
        print(f"      certified start n = {n} (u = {u}), nonzero coefficients among the next 64: {nz}")


# ---------------------------------------------------------------------------
# S9. Window discrepancy inequalities on L_{chi_4} (finite instances of the Lean lemmas on y = 2^N x)
# ---------------------------------------------------------------------------
def s9_window_discrepancy(spf: list) -> None:
    section("S9 [cert] window discrepancy D_{N,H}(L) = D_H({2^N L}): upper gap transfer on finite windows of L_{chi_4}")
    K = 12400
    num = 0
    for n in range(1, K + 1):
        num = 2 * num + (c_chi4_from_fac(factor_spf(n, spf)) if n > 1 else 1)
    # x * 2^K in [num, num + K + 2]  (0 <= c(n) <= n)
    B = K + 2
    digits_ok = None
    for npos in range(K, 0, -1):
        if (num >> (K - npos)) == ((num + B) >> (K - npos)):
            digits_ok = npos
            break
    check("cert", digits_ok is not None and digits_ok >= 12000, "at least 12000 certified binary digits of L_{chi_4}")
    PREC = 32

    def point(nn: int) -> int:  # floor(2^PREC x_nn) with x_nn = {2^nn x}; needs nn + PREC <= digits_ok
        assert nn + PREC <= digits_ok
        return (num >> (K - nn - PREC)) & ((1 << PREC) - 1)

    def disc(points: list) -> Fraction:
        ys = sorted(points)
        Hn = len(ys)
        g = [Fraction(i + 1, Hn) - Fraction(y, 1 << PREC) for i, y in enumerate(ys)]
        return Fraction(1, Hn) + max(g) - min(g)

    slack = Fraction(2, 1 << PREC)
    for N0, H in ((2048, 1024), (4096, 512), (6000, 3000), (9000, 2900), (11000, 900)):
        pts = [point(nn) for nn in range(N0, N0 + H)]
        D = disc(pts)
        ones = sum(1 for y in pts if y >= 1 << (PREC - 1))
        F_half = Fraction(ones, H)
        for ell in range(1, 12):
            rhs = Fraction(1, 2 ** ell) + Fraction(ell - 1, H) + ell * F_half
            check("cert", 1 - D <= rhs + slack, f"window upper gap transfer N={N0}, H={H}, ell={ell}")
        print(f"  window [{N0},{N0 + H}): 1 - D in [{float(1 - D - slack):.6f}, {float(1 - D + slack):.6f}], "
              f"ones fraction {float(F_half):.4f} (finite measurement only)")


# ---------------------------------------------------------------------------
# S10. Mira Cult audit: parameter algebra with the GRH level of distribution
# ---------------------------------------------------------------------------
def s10_mira_audit() -> None:
    section("S10 [exact] Mira Cult short-window audit: level-of-distribution bookkeeping under GRH")
    half = Fraction(1, 2)
    # Huxley-Iwaniec level used with PPS (2): nu <= 3*vartheta - 7/4 (- eps), 7/12 < vartheta <= 29/48.
    for k in range(1, 400):
        th = Fraction(7, 12) + Fraction(1, 12 * k)
        if th > Fraction(29, 48):
            continue
        hi_level = 3 * th - Fraction(7, 4)
        check("exact", hi_level == Fraction(1, 4 * k), "3 vartheta - 7/4 = 3(vartheta - 7/12) -> 0 as vartheta -> 7/12")
        check("exact", hi_level < th - half, "below 5/8 (so on (7/12, 29/48]) the HI level is the binding constraint")
    check("exact", 3 * Fraction(7, 12) - Fraction(7, 4) == 0, "HI level vanishes exactly at 7/12")
    print("  unconditional argument already runs with arbitrarily small level rho (rho < 3 vartheta - 7/4 -> 0)")
    # GRH level: sum_{q<=Q} max |...| <= C Q sqrt(x) log^2(Qx); with y = x^vartheta, Q = x^rho the
    # relative error is x^{rho + 1/2 - vartheta} log^2 x: a power saving iff rho < vartheta - 1/2.
    for a_num in range(501, 1001, 7):
        a = Fraction(a_num, 1000)
        a1 = (a + half) / 2                     # 1/2 < a' < a  (pays the end trim)
        theta = min(Fraction(1, 8), (2 * a1 - 1) / 3)
        ratio = (a1 - theta) / (1 - theta)      # log Y / log X for the largest cofactor b = N^theta
        vth = (half + ratio) / 2                # 1/2 < vartheta < ratio
        rho = (vth - half) / 2                  # 0 < rho < vartheta - 1/2
        check("exact", half < a1 < a, "1/2 < a' < a")
        check("exact", 0 < theta < a1 / 4, "theta < a'/4 (Mira's constraint)")
        check("exact", ratio > half, "(a' - theta)/(1 - theta) > 1/2")
        check("exact", a1 - theta > half, "a' - theta > 1/2 (divisor-pairing tail sqrt(N)/H -> 0)")
        check("exact", half < vth < ratio, "prime interval length exceeds X^vartheta, vartheta > 1/2")
        check("exact", 0 < rho < vth - half, "GRH level rho in (0, vartheta - 1/2): power saving")
    print("  for every a in (1/2, 1] (grid step 0.007): a', theta, vartheta, rho > 0 satisfy all audited constraints")
    # Bank budget: c = rho/(100 D (R+1)); sum_h 2^{-h}(R+h) = 2R + 2; D c (2R+2) = rho/50 < rho/4.
    for W in (1, 2, 3, 5, 10, 25, 50):
        Q = 100 * W + (100 * W) % 2
        D = Q + 1
        R = W ** 4
        for rho in (Fraction(1, 10), Fraction(1, 1000), Fraction(1, 10**6), Fraction(1, 10**12)):
            c = rho / (100 * D * (R + 1))
            check("exact", D * c * (2 * R + 2) == rho / 50, "later-bank modulus budget = rho/50")
            partial = sum(Fraction(R + h, 2 ** h) for h in range(0, 60))
            check("exact", D * c * partial < rho / 4, "finite partial budget < rho/4")
            eta = rho / 16
            check("exact", eta / c == Fraction(100 * D * (R + 1), 16), "eta/c depends on W only (not on rho)")
            check("exact", 4 / (eta * Fraction(3, 4)) == Fraction(256, 3) / rho,
                  "large-factor multiplicity <= 4/(eta*(1-theta)) < 256/(3*rho) for theta < 1/4")
    print("  bank budget rho/50 < rho/4 for every rho; eta/c independent of rho; only constants depend on rho")


# ---------------------------------------------------------------------------
def main() -> int:
    t0 = time.time()
    print("Phase 25 Addendum Track J: GRH, Paper VI planting, GF-22 moving windows, Mira Cult audit")
    prime_flags = sieve_primes(2 * 10**6 + 10**5)
    spf = spf_sieve(10**5 + 10)
    s1_paper6_parameters()
    s2_grh_algebra()
    s3_prime_powers(prime_flags)
    s4_psi_measurements(prime_flags)
    s5_short_divisor_lemma()
    s6_gf22_regimes(prime_flags)
    s7_phi_additivity(spf)
    s8_window_instances()
    s9_window_discrepancy(spf_sieve(12500))
    s10_mira_audit()
    total = sum(COUNTS.values())
    print(f"\nChecks: exact {COUNTS['exact']}, cert {COUNTS['cert']}, num {COUNTS['num']}  "
          f"(time {time.time() - t0:.1f} s)")
    print(f"ALL {total} CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
