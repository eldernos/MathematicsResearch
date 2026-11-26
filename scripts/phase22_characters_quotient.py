#!/usr/bin/env python3
"""Phase 22, Tracks B3-B4: exact and finite checks.

Companion to notes/phase22/odd-characters-and-kernel-quotient.md.

Standard library only.  Exits 0 when every assertion holds.

B3 (cubic character modulo 7).  chi(3) = omega = exp(2 pi i / 3), so chi = 1 on
{1, 6}, omega on {3, 4}, omega^2 on {2, 5}.  c = 1 * chi = x + y omega in Z[omega],
c_+ = 1 * (chi + chibar) = 2x - y and c_- = 1 * ((chi - chibar)/(i sqrt 3)) = y.

What is exact here:
  * c_+(n), c_-(n) for n <= 50,000 by divisor sieves of the weights w_+, w_-,
    compared with the closed form tau_1(n) * eps(t(n)) of Lemma 1.2 (and the
    closed form is then used up to 10^6);
  * the least n with c_+(n) = M and with c_-(n) = M for |M| <= 20, by a
    structured search (Lemma 2.2) cross-checked by exhaustion up to 10^6 and by
    direct divisor sums;
  * the hyperbola inequality for the means, the digit-window Lemma 5.1 at every
    admissible position of the certified expansions, and the arithmetic of the
    disjunctivity construction (Theorem 5.3) on explicit instances, where the
    digits at positions near 10^10 - 10^13 are read off from the local tail;
  * B4: the two radix-power inequalities for M_N on exact rationals, the
    quotient order, base-b periods, the exact discrepancy formula of a periodic
    orbit (two independent derivations, exact Fractions), the digit-frequency
    transfer, and the simple-normality classification.

What is only finite data: support densities against the Euler product, the
six sign classes, moment ratios, word counts, finite discrepancies.  They
illustrate the theorems; they prove nothing asymptotic.
"""

from __future__ import annotations

import math
import random
import sys
import time
from fractions import Fraction
from math import gcd

CHECKS = 0
T0 = time.time()


def check(cond: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def header(title: str) -> None:
    print()
    print(f"[{time.time() - T0:.1f} s]")
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Elementary arithmetic
# ---------------------------------------------------------------------------


def primes_upto(N: int) -> list[int]:
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(range(i * i, N + 1, i)))
    return [i for i in range(N + 1) if s[i]]


def spf_sieve(N: int, primes: list[int]) -> list[int]:
    """Smallest prime factor; larger primes first, smaller ones overwrite."""
    spf = list(range(N + 1))
    for p in reversed(primes):
        if p * p > N:
            continue
        spf[p * p :: p] = [p] * len(range(p * p, N + 1, p))
    return spf


SMALL_PRIMES = primes_upto(1000)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in SMALL_PRIMES[:25]:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True  # deterministic for n < 3.3e24


RNG = random.Random(20261126)


def pollard_brent(n: int) -> int:
    if n % 2 == 0:
        return 2
    while True:
        y, c, m = RNG.randrange(1, n), RNG.randrange(1, n), 64
        g = r = q = 1
        x = ys = y
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


def factorize(n: int) -> dict[int, int]:
    f: dict[int, int] = {}
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime(m):
            f[m] = f.get(m, 0) + 1
            continue
        d = pollard_brent(m)
        stack += [d, m // d]
    return f


def divisors_from(f: dict[int, int]) -> list[int]:
    ds = [1]
    for p, e in f.items():
        ds = [d * p ** i for d in ds for i in range(e + 1)]
    return ds


def crt(r1: int, m1: int, r2: int, m2: int) -> tuple[int, int]:
    g = gcd(m1, m2)
    assert g == 1
    t = (r2 - r1) * pow(m1, -1, m2) % m2
    return r1 + m1 * t, m1 * m2


# ---------------------------------------------------------------------------
# The cubic character modulo 7
# ---------------------------------------------------------------------------

# chi values as (x, y) in Z[omega]: 1 = (1,0), omega = (0,1), omega^2 = (-1,-1).
CHI = {0: (0, 0), 1: (1, 0), 6: (1, 0), 3: (0, 1), 4: (0, 1), 2: (-1, -1), 5: (-1, -1)}
WPLUS = {0: 0, 1: 2, 6: 2, 2: -1, 3: -1, 4: -1, 5: -1}
WMINUS = {0: 0, 1: 0, 6: 0, 3: 1, 4: 1, 2: -1, 5: -1}
EPS_PLUS = [2, 1, -1, -2, -1, 1]   # 2 cos(pi t / 3)
EPS_MINUS = [0, 1, 1, 0, -1, -1]   # (2/sqrt3) sin(pi t / 3)
KER = (1, 6)
CLS_P = (3, 4)   # chi = omega: t += 1 at exponents = 1 mod 3
CLS_M = (2, 5)   # chi = omega^2: t -= 1 at exponents = 1 mod 3


def zw_mul(a, b):
    """(a0 + a1 w)(b0 + b1 w) with w^2 = -1 - w."""
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0] - a[1] * b[1])


def local(p: int, e: int) -> tuple[int, int, int]:
    """(alive, tau_1 factor, t increment) of c(p^e)."""
    r = p % 7
    if r == 0:
        return 1, 1, 0
    if r in KER:
        return 1, e + 1, 0
    if e % 3 == 2:
        return 0, 1, 0
    if e % 3 == 1:
        return 1, 1, (1 if r in CLS_P else -1)
    return 1, 1, 0


def c_from_fact(f: dict[int, int]) -> tuple[int, int, int]:
    al, t1, t = 1, 1, 0
    for p, e in f.items():
        a, m, dt = local(p, e)
        al &= a
        t1 *= m
        t += dt
    return al, t1, t % 6


def cpm(state) -> tuple[int, int]:
    al, t1, t = state
    return al * t1 * EPS_PLUS[t], al * t1 * EPS_MINUS[t]


def c_direct(n: int) -> tuple[int, int]:
    """(c_+(n), c_-(n)) from the divisor sum of chi in Z[omega]."""
    X = Y = 0
    for d in divisors_from(factorize(n)):
        v = CHI[d % 7]
        X += v[0]
        Y += v[1]
    return 2 * X - Y, Y


# ---------------------------------------------------------------------------
# Certified base-b expansions (as in scripts/phase21_characters_classical.py)
# ---------------------------------------------------------------------------


class Num:
    """Real x known through an integer S and bound T with |b^K x - S| <= T."""

    def __init__(self, b: int, K: int, S: int, T: int):
        self.b, self.K, self.S, self.T = b, K, S, T

    def __add__(self, o: "Num") -> "Num":
        assert self.b == o.b and self.K == o.K
        return Num(self.b, self.K, self.S + o.S, self.T + o.T)

    def points(self, N: int) -> list[float]:
        """Fractional parts of b^n x, n < N, each within 1e-10 of the truth."""
        B = self.b ** self.K
        err = (self.T + 1) * Fraction(self.b ** N, B)
        assert err < Fraction(1, 10 ** 10), "precision too low"
        Bw = 2 ** 60
        pts = []
        cur = self.S % B
        for _ in range(N):
            pts.append((cur * Bw // B) / Bw)
            cur = cur * self.b % B
        return pts


def from_coeffs(b: int, K: int, coeff, tailC: int) -> Num:
    """x = sum_{n>=1} coeff(n) b^-n with |coeff(n)| <= tailC * n for n > K."""
    # divide and conquer evaluation of sum coeff(n) b^(K-n)
    def build(lo: int, hi: int) -> int:  # sum_{n=lo}^{hi} coeff(n) b^(hi-n)
        if hi - lo < 64:
            s = 0
            for n in range(lo, hi + 1):
                s = s * b + coeff(n)
            return s
        mid = (lo + hi) // 2
        return build(lo, mid) * b ** (hi - mid) + build(mid + 1, hi)

    S = build(1, K)
    T = tailC * (K + 2)
    return Num(b, K, S, T)


def to_digits(n: int, b: int, length: int) -> list[int]:
    """Base-b digits of 0 <= n < b^length, most significant first."""
    if length <= 40:
        out = [0] * length
        for i in range(length - 1, -1, -1):
            n, out[i] = divmod(n, b)
        return out
    half = length // 2
    hi, lo = divmod(n, b ** (length - half))
    return to_digits(hi, b, half) + to_digits(lo, b, length - half)


def certified_digits(x: Num) -> list[int]:
    """Digits d_1 d_2 ... of frac(x) that are certified by the enclosure."""
    b, K, S, T = x.b, x.K, x.S, x.T
    G = 1
    while b ** G <= 4 * T:
        G += 1
    while True:
        lo, hi = (S - T) // b ** G, (S + T) // b ** G
        if lo == hi:
            break
        G += 1
    F = lo % b ** (K - G)
    return to_digits(F, b, K - G)


def disc(points: list[float]) -> float:
    ys = sorted(points)
    M = len(ys)
    hi = lo = 0.0
    for i, y in enumerate(ys, 1):
        hi = max(hi, i / M - y)
        lo = min(lo, (i - 1) / M - y)
    return hi - lo


def points_from_digits(dig: list[int], b: int, N: int, W: int = 30) -> list[float]:
    BW = b ** W
    out = []
    for n in range(N):
        v = 0
        for d in dig[n : n + W]:
            v = v * b + d
        out.append(v / BW)
    return out


# ===========================================================================
# B3
# ===========================================================================


def section_B3_values(NB: int, N1: int):
    header("B3.1  Values of c_+ and c_- (cubic character mod 7)")
    primes = primes_upto(NB)
    spf = spf_sieve(NB, primes)

    # closed form via smallest prime factors
    alive = bytearray(NB + 1)
    tau1 = [0] * (NB + 1)
    tt = bytearray(NB + 1)
    E = bytearray(NB + 1)
    REST = [0] * (NB + 1)
    alive[1], tau1[1], tt[1] = 1, 1, 0
    for n in range(2, NB + 1):
        p = spf[n]
        m = n // p
        if m % p == 0:
            e = E[m] + 1
            rest = REST[m]
        else:
            e = 1
            rest = m
        E[n] = e
        REST[n] = rest
        r = p % 7
        if r == 0:
            alive[n], tau1[n], tt[n] = alive[rest], tau1[rest], tt[rest]
        elif r == 1 or r == 6:
            alive[n], tau1[n], tt[n] = alive[rest], tau1[rest] * (e + 1), tt[rest]
        else:
            em = e % 3
            if em == 2:
                alive[n], tau1[n], tt[n] = 0, tau1[rest], tt[rest]
            elif em == 1:
                d = 1 if (r == 3 or r == 4) else 5
                alive[n], tau1[n], tt[n] = alive[rest], tau1[rest], (tt[rest] + d) % 6
            else:
                alive[n], tau1[n], tt[n] = alive[rest], tau1[rest], tt[rest]

    def cp(n):
        return alive[n] * tau1[n] * EPS_PLUS[tt[n]]

    def cm(n):
        return alive[n] * tau1[n] * EPS_MINUS[tt[n]]

    # divisor sieves straight from the definitions
    Xs = [0] * (N1 + 1)
    Ys = [0] * (N1 + 1)
    Wp = [0] * (N1 + 1)
    Wm = [0] * (N1 + 1)
    for d in range(1, N1 + 1):
        r = d % 7
        if r == 0:
            continue
        cx, cy = CHI[r]
        wp, wm = WPLUS[r], WMINUS[r]
        for m in range(d, N1 + 1, d):
            Xs[m] += cx
            Ys[m] += cy
            Wp[m] += wp
            if wm:
                Wm[m] += wm
    bad = 0
    for n in range(1, N1 + 1):
        if not (Wp[n] == 2 * Xs[n] - Ys[n] == cp(n) and Wm[n] == Ys[n] == cm(n)):
            bad += 1
    check(bad == 0, "closed form of c_+, c_- disagrees with divisor sums")
    CHK = 0
    for n in range(1, N1 + 1):
        CHK = (CHK * 1000003 + Wp[n] * 7 + Wm[n]) % (2 ** 61 - 1)
    print(f"c_+ = 1*w_+ = 2x-y and c_- = 1*w_- = y agree with tau_1(n)*eps(t(n)) "
          f"for all n <= {N1}  (checksum {CHK})")
    print(f"  first values c_+(1..14) = {[cp(n) for n in range(1, 15)]}")
    print(f"  first values c_-(1..14) = {[cm(n) for n in range(1, 15)]}")

    # Lemma 1.1: local factors in Z[omega] vs (alive, tau1, t)
    unit = {0: (1, 0)}
    u = (1, 0)
    e6 = (1, 1)  # 1 + omega = -omega^2 = exp(i pi/3)
    for t in range(1, 6):
        u = zw_mul(u, e6)
        unit[t] = u
    nloc = 0
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43]:
        for e in range(0, 13):
            # geometric sum of chi(p)^i
            s = (0, 0)
            pw = (1, 0)
            for i in range(e + 1):
                s = (s[0] + pw[0], s[1] + pw[1])
                pw = zw_mul(pw, CHI[p % 7]) if p % 7 else ((1, 0) if i < 0 else (0, 0))
            if p == 7:
                s = (1, 0)
            al, m, dt = local(p, e)
            want = (0, 0) if not al else (m * unit[dt % 6][0], m * unit[dt % 6][1])
            check(s == want, f"local factor p={p} e={e}")
            nloc += 1
    print(f"Lemma 1.1: {nloc} local factors c(p^e) equal tau-factor * exp(i pi t/3) exactly")

    # every value is attained: least witnesses
    return dict(alive=alive, tau1=tau1, tt=tt, cp=cp, cm=cm, primes=primes, spf=spf, NB=NB)


def least_witnesses(data, Mmax: int = 20):
    header("B3.2  Surjectivity onto Z: least n with c_+(n) = M and c_-(n) = M")
    NB = data["NB"]
    alive, tau1, tt = data["alive"], data["tau1"], data["tt"]
    primes = data["primes"]
    KP = [p for p in primes if p % 7 in KER][:12]
    P3 = [p for p in primes if p % 7 in CLS_P][:10]
    P2 = [p for p in primes if p % 7 in CLS_M][:10]

    def mult_parts(T, mn=2):
        if T == 1:
            yield []
            return
        for f in range(mn, T + 1):
            if T % f == 0:
                for rest in mult_parts(T // f, f):
                    yield [f] + rest

    def kmin(T):
        best = None
        for part in mult_parts(T):
            ex = sorted((f - 1 for f in part), reverse=True)
            v = 1
            for p, e in zip(KP, ex):
                v *= p ** e
            best = v if best is None else min(best, v)
        return best

    smin = {}
    for a in range(9):
        for bb in range(9):
            v = math.prod(P3[:a]) * math.prod(P2[:bb])
            j = (a - bb) % 6
            smin[j] = v if j not in smin else min(smin[j], v)

    def structured(M, eps):
        if M == 0:
            return None
        best = None
        for j in range(6):
            if eps[j] == 0 or M % eps[j]:
                continue
            T = M // eps[j]
            if T < 1:
                continue
            v = kmin(T) * smin[j]
            best = v if best is None else min(best, v)
        return best

    # exhaustive minima up to NB
    first_p, first_m = {}, {}
    for n in range(1, NB + 1):
        v = alive[n] * tau1[n] * EPS_PLUS[tt[n]]
        if -Mmax <= v <= Mmax and v not in first_p:
            first_p[v] = n
        v = alive[n] * tau1[n] * EPS_MINUS[tt[n]]
        if -Mmax <= v <= Mmax and v not in first_m:
            first_m[v] = n
    res = {}
    for name, eps, first, zero in (("c_+", EPS_PLUS, first_p, 4), ("c_-", EPS_MINUS, first_m, 1)):
        row = {}
        for M in range(-Mmax, Mmax + 1):
            A = zero if M == 0 else structured(M, eps)
            check(A is not None, f"{name} value {M} unreachable")
            if A <= NB:
                check(first.get(M) == A, f"{name}: structured minimum {A} vs exhaustive {first.get(M)} for M={M}")
            else:
                check(M not in first, f"{name}: value {M} attained below {NB} but structured min {A}")
            dp, dm = c_direct(A)
            check((dp if name == "c_+" else dm) == M, f"{name}({A}) != {M} by direct divisor sum")
            row[M] = A
        res[name] = row
        print(f"{name}: every M in [-{Mmax},{Mmax}] attained; least witnesses (direct divisor sums agree):")
        line = []
        for M in range(-Mmax, Mmax + 1):
            line.append(f"{M}:{row[M]}")
        for i in range(0, len(line), 7):
            print("   " + "  ".join(line[i : i + 7]))
    # the explicit families of Proposition 2.1
    for V in range(1, 9):
        for u in (3, 17, 31, 59, 73, 101):
            A = 13 ** (V - 1) * u
            check(c_direct(A) == (V, V), f"c_pm(13^(V-1) u) = V fails V={V} u={u}")
            if u != 3:
                A2 = 3 * 13 ** (V - 1) * u
                check(c_direct(A2) == (-V, V), "c(3*13^(V-1)*u) = V omega")
    print("Prop. 2.1 families: c_+(13^(V-1)u) = c_-(13^(V-1)u) = V for primes u = 3 (mod 7), V <= 8")
    return res


def section_B3_densities(data):
    header("B3.3  Support density, sign classes, means and moments (finite data)")
    alive, tau1, tt, NB, primes = data["alive"], data["tau1"], data["tt"], data["NB"], data["primes"]
    # Euler product
    delta_P = 1.0
    for p in primes:
        if p % 7 in (2, 3, 4, 5):
            delta_P *= 1 - 1 / (p * p + p + 1)
    P = primes[-1]
    lo_d, hi_d = delta_P * (1 - 1 / P), delta_P
    print(f"delta = prod_(p = 2,3,4,5 mod 7) (1 - 1/(p^2+p+1)) in [{lo_d:.8f}, {hi_d:.8f}]")
    print(f"  2 delta/3 = {2 * delta_P / 3:.6f},  delta/6 = {delta_P / 6:.6f}")
    marks = [10 ** 4, 10 ** 5, NB]
    sp = sm = 0
    cls = [0] * 6
    sum_p = sum_m = 0
    abs_p = abs_m = 0
    sq_p = sq_m = 0
    rows = []
    mi = 0
    for n in range(1, NB + 1):
        if alive[n]:
            t1 = tau1[n]
            t = tt[n]
            vp = t1 * EPS_PLUS[t]
            vm = t1 * EPS_MINUS[t]
            sp += 1
            cls[t] += 1
            if vm:
                sm += 1
            sum_p += vp
            sum_m += vm
            abs_p += abs(vp)
            abs_m += abs(vm)
            sq_p += vp * vp
            sq_m += vm * vm
        if n == marks[mi]:
            rows.append((n, sp, sm, cls[:], sum_p, sum_m, abs_p, abs_m, sq_p, sq_m))
            mi += 1
            if mi == len(marks):
                break
    # means from the log-sine formula
    def mean_formula(w):
        M = 7
        tot = 0.0
        for k in range(1, M):
            Wk = sum(w[r % 7] * math.cos(2 * math.pi * k * r / M) for r in range(M)) / M
            tot -= Wk * math.log(2 * math.sin(math.pi * k / M))
        return tot

    mu_p, mu_m = mean_formula(WPLUS), mean_formula(WMINUS)
    # direct partial sums of w(m)/m as a sanity check
    ps = sum(WPLUS[m % 7] / m for m in range(1, 10 ** 6 + 1))
    ms = sum(WMINUS[m % 7] / m for m in range(1, 10 ** 6 + 1))
    check(abs(ps - mu_p) < 3e-6 and abs(ms - mu_m) < 2e-6, "log-sine formula vs partial sums")
    print(f"mean of c_+ = sum w_+(m)/m = 2 Re L(1,chi) = {mu_p:.12f}")
    print(f"mean of c_- = sum w_-(m)/m = (2/sqrt3) Im L(1,chi) = {mu_m:.12f}")
    print()
    print("     X   S_+/X   S_-/X  (S_-/S_+)  class t=0..5 as fraction of S_+         "
          "mean c_+  bound   mean c_-  bound")
    for (n, s1, s2, cl, a, bm, ap, am, qp, qm) in rows:
        fr = " ".join(f"{c / s1:.4f}" for c in cl)
        bp, bmn = 10 / math.sqrt(n), 5 / math.sqrt(n)
        check(abs(a / n - mu_p) <= bp + 1e-12, f"hyperbola bound c_+ at X={n}")
        check(abs(bm / n - mu_m) <= bmn + 1e-12, f"hyperbola bound c_- at X={n}")
        print(f"{n:>7} {s1 / n:.5f} {s2 / n:.5f}  {s2 / s1:.4f}   {fr}   "
              f"{a / n:+.5f} {bp:.4f}  {bm / n:+.5f} {bmn:.4f}")
    n, s1 = rows[-1][0], rows[-1][1]
    check(abs(s1 / n - delta_P) < 2e-3, "support density of c_+ near the Euler product")
    # Remark 3.2: h_2(n) = 1_S(n) omega^t(n) equals (chi * g_2)(n), g_2 supported on 7^a * squarefull
    def g2_local(p, e):
        r = p % 7
        if r == 0:
            return (1, 0)
        if r in KER:
            return (1, 0) if e == 0 else (0, 0)
        if e % 3 == 1:
            return (0, 0)
        if e % 3 == 0:
            return (1, 0)
        return (1, 1) if r in CLS_P else (0, -1)  # -omega^2 = 1 + omega ; -omega = (0, -1)
    OMP = [(1, 0), (0, 1), (-1, -1)]
    spf = data["spf"]
    Ng = 20000
    g2 = [(0, 0)] * (Ng + 1)
    g2[1] = (1, 0)
    for m in range(2, Ng + 1):
        f = {}
        mm = m
        while mm > 1:
            p = spf[mm]
            f[p] = f.get(p, 0) + 1
            mm //= p
        v = (1, 0)
        for p, e in f.items():
            v = zw_mul(v, g2_local(p, e))
        g2[m] = v
    conv = [[0, 0] for _ in range(Ng + 1)]
    for d in range(1, Ng + 1):
        if g2[d] == (0, 0):
            continue
        for m in range(1, Ng // d + 1):
            cv = CHI[m % 7]
            if cv == (0, 0):
                continue
            pr = zw_mul(g2[d], cv)
            conv[d * m][0] += pr[0]
            conv[d * m][1] += pr[1]
    for m in range(1, Ng + 1):
        # h_2(n) = omega^t(n) on S, and omega^t depends only on t mod 3
        want = OMP[tt[m] % 3] if alive[m] else (0, 0)
        check(tuple(conv[m]) == want, "h_2 = chi * g_2")
    pchi = [(0, 0)]
    acc = (0, 0)
    for m in range(1, 8):
        acc = (acc[0] + CHI[m % 7][0], acc[1] + CHI[m % 7][1])
        pchi.append(acc)
    check(max(abs(complex(x - y / 2, y * math.sqrt(3) / 2)) for x, y in pchi) <= 1 + 1e-12,
          "partial sums of chi have modulus <= 1")
    # sum_{n<=X} h_2(n) and the bound sum_{d<=X} |g_2(d)| <= #{7^a m <= X : m squarefull}
    sq = bytearray(NB + 1)  # squarefull indicator
    sq[1] = 1
    for m in range(2, NB + 1):
        mm, ok = m, True
        while mm > 1:
            p = spf[mm]
            e = 0
            while mm % p == 0:
                mm //= p
                e += 1
            if e == 1:
                ok = False
                break
        sq[m] = ok
    print()
    print("     X   |sum h_2(n)|   #{7^a m <= X, m squarefull}   ratios to sqrt X     |S_-/S_+ - 2/3|")
    H = [0.0, 0.0]
    mi = 0
    cnt7 = 0
    for m in range(1, NB + 1):
        if alive[m]:
            om = OMP[tt[m] % 3]
            H[0] += om[0]
            H[1] += om[1]
        mm = m
        while mm % 7 == 0:
            mm //= 7
        if sq[mm]:
            cnt7 += 1
        if m == marks[mi]:
            Hm = abs(complex(H[0] - H[1] / 2, H[1] * math.sqrt(3) / 2))
            check(Hm <= cnt7, "|sum h_2| <= #{7^a m <= X, m squarefull}")
            s1, s2 = rows[mi][1], rows[mi][2]
            print(f"{m:>7}   {Hm:10.3f}      {cnt7:8d}                    {Hm / math.sqrt(m):.3f}  "
                  f"{cnt7 / math.sqrt(m):.3f}        {abs(s2 / s1 - 2 / 3):.6f}")
            mi += 1
            if mi == len(marks):
                break
    print()
    print("     X   sum|c_+|/(X L^(1/3))  sum|c_-|/(X L^(1/3))  sum c_+^2/(X L)  "
          "sum c_-^2/(X L)  ratio of squares   (L = log X)")
    for (n, s1, s2, cl, a, bm, ap, am, qp, qm) in rows:
        L = math.log(n)
        print(f"{n:>7}      {ap / (n * L ** (1 / 3)):.4f}              {am / (n * L ** (1 / 3)):.4f}"
              f"            {qp / (n * L):.4f}           {qm / (n * L):.4f}          {qp / qm:.4f}")
    # pointwise inequalities used in Prop. 3.4
    for n in range(1, 50001):
        if alive[n]:
            t1, t = tau1[n], tt[n]
            vp = abs(t1 * EPS_PLUS[t])
            check(t1 <= vp <= 2 * t1, "|c| <= |c_+| <= 2|c|")
    return delta_P


def section_B3_expansions(data):
    header("B3.4  Certified expansions: word counts, digit-window lemma, discrepancies")
    cp, cm = data["cp"], data["cm"]
    out = {}
    specs = [("L_+(2)", 2, cp, 50000), ("L_-(2)", 2, cm, 50000), ("L_+(3)", 3, cp, 12000),
             ("L_-(3)", 3, cm, 12000)]
    for name, b, f, K in specs:
        x = from_coeffs(b, K, f, 2)
        dig = certified_digits(x)
        out[name] = (b, f, K, dig, x)
        print(f"{name}: {len(dig)} certified base-{b} digits from {K} coefficients; "
              f"first 40: {''.join(map(str, dig[:40]))}")
    # word counts
    print()
    for name in ("L_+(2)", "L_-(2)"):
        b, f, K, dig, x = out[name]
        s = "".join(map(str, dig))
        tot_words = 0
        minc = None
        for ell in range(1, 7):
            cnt = [0] * (1 << ell)
            v = int(s[:ell], 2)
            cnt[v] += 1
            mask = (1 << ell) - 1
            for ch in s[ell:]:
                v = ((v << 1) | (ch == "1")) & mask
                cnt[v] += 1
            for w in range(1 << ell):
                check(cnt[w] > 0, f"{name}: binary word {w:0{ell}b} missing")
                tot_words += 1
                minc = cnt[w] if minc is None else min(minc, cnt[w])
            if ell == 6:
                first0 = s.find("000000") + 1
                first1 = s.find("111111") + 1
                lo, hi = min(cnt), max(cnt)
        print(f"{name}: all {tot_words} binary words of length 1..6 occur among the first {len(s)} digits; "
              f"least count {minc}; length-6 counts in [{lo},{hi}]; first 000000 at {first0}, "
              f"first 111111 at {first1}")
    for name in ("L_+(3)", "L_-(3)"):
        b, f, K, dig, x = out[name]
        tot = 0
        minc = None
        for ell in range(1, 5):
            cnt = {}
            for i in range(len(dig) - ell + 1):
                key = tuple(dig[i : i + ell])
                cnt[key] = cnt.get(key, 0) + 1
            check(len(cnt) == 3 ** ell, f"{name}: some ternary word of length {ell} missing")
            tot += len(cnt)
            minc = min(cnt.values()) if minc is None else min(minc, min(cnt.values()))
        print(f"{name}: all {tot} ternary words of length 1..4 occur among the first {len(dig)} digits; "
              f"least count {minc}")
    # digit-window Lemma 5.1 at every admissible position
    print()
    for name in ("L_+(2)", "L_-(2)", "L_+(3)", "L_-(3)"):
        b, f, K, dig, x = out[name]
        coef = [0] + [f(n) for n in range(1, K + 1)]
        inst = 0
        lim = len(dig) - 80
        for W in (1, 2, 3):
            for N in range(0, lim):
                if any(coef[N + i] for i in range(1, W + 1)):
                    continue
                P = N + W + 1
                V = coef[P]
                if V % b == 0 or not (-b ** (W + 1) <= V < b ** (W + 1)):
                    continue
                # T_P = sum_{k>=1} coef[P+k] b^-k, truncated at 60 terms
                T = 0.0
                for k in range(1, 61):
                    T += coef[P + k] / b ** k
                # sum_{k>=61} 2 (P+k) b^-k = 2 b^-61 ((P+61)/(1-1/b) + (1/b)/(1-1/b)^2)
                rr = 1 / b
                err = 2 * rr ** 61 * ((P + 61) / (1 - rr) + rr / (1 - rr) ** 2)
                if abs(T) + err >= 0.5:
                    continue
                M1 = (V // b) % b ** W
                want = to_digits(M1, b, W)
                check(dig[N : N + W] == want, f"{name}: digit window fails at N={N}, W={W}")
                inst += 1
        print(f"{name}: Lemma 5.1 (f = 0) verified at all {inst} admissible positions with W in {{1,2,3}}")
    # finite discrepancies
    print()
    for name in ("L_+(2)", "L_-(2)", "L_+(3)"):
        b, f, K, dig, x = out[name]
        vals = []
        for N in (1000, 2000, 4000, 8000):
            pts = points_from_digits(dig, b, N, 40 if b == 2 else 26)
            vals.append(f"D_{N}={disc(pts):.4f}")
        print(f"{name}: " + ", ".join(vals) + "   (finite data)")
    return out


def construction_instances(data):
    header("B3.5  The disjunctivity construction on explicit instances")
    # P' primes (chi(p) != 1, p != 7); kill by v_p = 2
    Pp = [p for p in SMALL_PRIMES if p % 7 in (2, 3, 4, 5)]

    def c_state(n):
        return c_from_fact(factorize(n))

    def tail_T(start, b, terms, series):
        """sum_{k=1}^{terms} a(start+k) b^-k as a Fraction, and the truncation bound."""
        T = Fraction(0)
        for k in range(1, terms + 1):
            v = cpm(c_state(start + k))[series]
            T += Fraction(v, b ** k)
        # |a(n)| <= 2 tau(n) <= 4 sqrt(n); terms beyond terms+300 are below 2^-200
        err = Fraction(1, 2 ** 200)
        for k in range(terms + 1, terms + 300):
            err += Fraction(4 * (math.isqrt(start + k) + 1), b ** k)
        return T, err

    def least_A(series, V1):
        """least A <= 10^5, 7 not dividing A, with c_series(A u) = V1 for primes u = 3 mod 7."""
        for A in range(1, 10 ** 5):
            if A % 7 == 0:
                continue
            al, t1, t = data["alive"][A], data["tau1"][A], data["tt"][A]
            eps = EPS_PLUS if series == 0 else EPS_MINUS
            if al and t1 * eps[(t + 1) % 6] == V1:
                return A
        return None

    total = 0
    for b, W, L in ((2, 2, 2), (3, 1, 2)):
        for series, sname in ((0, "L_+"), (1, "L_-")):
            for M in range(b ** W):
                cands = [V for V in range(-b ** (W + 1), b ** (W + 1))
                         if V % b and (V // b) % b ** W == M]
                best = None
                for V1 in cands:
                    A = least_A(series, V1)
                    if A is None:
                        continue
                    offs = list(range(-W, 0)) + list(range(1, L + 1))
                    used, kills = set(), []
                    for j in offs:
                        for p in Pp:
                            if p in used or A % p == 0 or j % p == 0:
                                continue
                            used.add(p)
                            kills.append((p, j))
                            break
                    Q = math.prod(p ** 3 for p, _ in kills)
                    score = A * 7 * Q
                    if best is None or score < best[0]:
                        best = (score, V1, A, kills, Q)
                _, V1, A, kills, Q = best
                # CRT: u = 3 mod 7, A u = p^2 - j mod p^3
                r, m = 3, 7
                for p, j in kills:
                    rr = (p * p - j) * pow(A, -1, p ** 3) % p ** 3
                    r, m = crt(r, m, rr, p ** 3)
                found = False
                tries = 0
                u = r
                while not found:
                    u += m
                    tries += 1
                    check(tries < 20000, "no instance found")
                    if u <= A or not is_prime(u):
                        continue
                    m0 = A * u
                    # zero positions
                    for p, j in kills:
                        n = m0 + j
                        check(n % p ** 2 == 0 and n % p ** 3 != 0, "v_p = 2 at a kill position")
                        check(c_state(n)[0] == 0, "c vanishes at a kill position")
                    check(cpm(c_state(m0))[series] == V1, "value at the value position")
                    T, err = tail_T(m0 + L, b, 45, series)
                    if not (abs(T) + err < Fraction(b ** L, 2)):
                        continue
                    found = True
                    N = m0 - W - 1
                    # T_N = b^-(W+1) (V1 + b^-L T_{m0+L})
                    TN = Fraction(1, b ** (W + 1)) * (V1 + T / b ** L)
                    eN = err / b ** (W + 1 + L)
                    for z in (TN - eN, TN + eN):
                        fr = z - math.floor(z)
                        dg = to_digits(math.floor(fr * b ** W), b, W)
                        check(dg == to_digits(M, b, W), "digits at the constructed position")
                    total += 1
                    print(f"b={b} {sname} word {''.join(map(str, to_digits(M, b, W)))}: V1={V1:+d}, A={A}, "
                          f"kill primes {[p for p, _ in kills]}, modulus 7Q={m}, u={u}, "
                          f"digits N+1..N+{W} with N={N}  (|T|={float(abs(T)):.3f})")
    print(f"{total} explicit occurrences produced by the recipe; digits read off from the local tail")


def section_B3_constants():
    header("B3.6  Constants in the proof of Theorem 5.3")
    r = 2 ** -0.5
    s1 = sum(k * k * 2.0 ** -k for k in range(1, 400))
    s2 = r * (1 + r) / (1 - r) ** 3
    s2n = sum(k * k * r ** k for k in range(1, 2000))
    s3 = sum(2 * math.sqrt(3) * k * 2.0 ** -k for k in range(1, 400))
    check(abs(s1 - 6) < 1e-12 and abs(s2 - s2n) < 1e-9 and s2 < 48.05, "series constants")
    check(s3 < 7, "sum 2 sqrt3 k 2^-k < 7")
    check(6 * (s1 + s2) <= 330, "6 (6 + 48.05) <= 330")
    print(f"sum k^2 2^-k = {s1:.6f};  sum k^2 2^-k/2 = {s2:.6f};  sum 2 sqrt3 k 2^-k = {s3:.6f}")
    # 1 + log X <= (1 + log 3AY)(1 + log k) <= (1 + log 3AY) k  and  (2+k) <= 3k
    for k in range(1, 200):
        check(1 + math.log(k) <= k and 2 + k <= 3 * k and math.sqrt(3 * k) <= k * math.sqrt(3) + 1e-12,
              "elementary inequalities")
    # Lemma 5.2 (divisor sums in progressions) on random data
    tau = [0] * 200001
    for d in range(1, 200001):
        for m in range(d, 200001, d):
            tau[m] += 1
    for _ in range(300):
        D = RNG.randrange(1, 3000)
        c = RNG.randrange(0, D)
        X = RNG.randrange(1000, 200000)
        lhs = sum(tau[m] for m in range(c if c else D, X + 1, D))
        g = gcd(c, D)
        tg = sum(1 for e in range(1, g + 1) if g % e == 0)
        rhs = 2 * math.sqrt(X) + 2 * X / D * tg * (1 + math.log(X))
        check(lhs <= rhs, "Lemma 5.2")
    print("Lemma 5.2: sum_{m<=X, m=c (D)} tau(m) <= 2 sqrt X + (2X/D) tau(gcd(c,D)) (1 + log X) "
          "on 300 random (D, c, X)")


# ===========================================================================
# B4
# ===========================================================================


def nint_frac(fr: Fraction) -> Fraction:
    f = fr - math.floor(fr)
    return min(f, 1 - f)


def section_B4_M():
    header("B4.1  M_N(w; b) versus M_N(w; b^k) on exact rationals")
    n = 0
    worst = Fraction(0)
    for b in range(2, 7):
        for k in range(2, 6):
            C = Fraction(b ** k - 1, k * (b - 1))
            for _ in range(8):
                q = RNG.randrange(2, 10 ** 6)
                x = Fraction(RNG.randrange(0, q), q)
                Nmax = 24
                dist = [nint_frac(b ** m * x) for m in range(k * Nmax + k)]
                for N in range(1, Nmax + 1):
                    Mbk = sum(dist[k * j] for j in range(N)) / N
                    Mb = sum(dist[:k * N]) / (k * N)
                    check(Mbk <= k * Mb, "M_N(x;b^k) <= k M_kN(x;b)")
                    check(Mb <= C * Mbk, "M_kN(x;b) <= (b^k-1)/(k(b-1)) M_N(x;b^k)")
                    if Mbk:
                        worst = max(worst, Mb / (C * Mbk))
                    # arbitrary lengths N' = kN + rr
                    for rr in range(k):
                        Np = k * N + rr
                        Mp = sum(dist[:Np]) / Np
                        Mb1 = sum(dist[k * j] for j in range(N + 1)) / (N + 1)
                        check(Mp <= Fraction(b ** k - 1, b - 1) * Fraction(N + 1, Np) * Mb1,
                              "M_N' bound for N' = kN + r")
                    n += 1
                for j in range(k):
                    for m in range(40):
                        y = b ** m * x
                        check(nint_frac(b ** j * y) <= b ** j * nint_frac(y), "||b^j y|| <= b^j ||y||")
    for b in range(3, 7):
        for k in range(2, 6):
            w = Fraction(1, b ** k - 1)
            for N in range(1, 11):
                lhs = sum(nint_frac(b ** m * w) for m in range(k * N))
                rhs = Fraction(b ** k - 1, b - 1) * sum(nint_frac(b ** (k * j) * w) for j in range(N))
                check(lhs == rhs, "equality in (ii) at w = 1/(b^k-1), b >= 3")
    for b in range(2, 7):
        for k in range(2, 6):
            w = Fraction(1, b ** k)
            for N in range(1, 11):
                lhs = sum(nint_frac(b ** m * w) for m in range(k * N))
                rhs = Fraction(b ** k - 1, b - 1) * sum(nint_frac(b ** (k * j) * w) for j in range(N))
                check(lhs == rhs, "equality in (ii) at w = b^-k, b >= 2")
    print(f"Theorem 7.1 inequalities hold exactly on {n} (b, k, x, N) cases, b in [2,6], k in [2,5]; "
          f"largest ratio of the two sides of (ii): {float(worst):.4f}; equality at w = 1/(b^k-1) "
          f"for 3 <= b <= 6 and at w = b^-k for 2 <= b <= 6 (k <= 5, N <= 10)")


def period_b(b: int, k: int, r: int) -> int:
    Mk = b ** k - 1
    v = r % Mk
    d = 1
    while (v * b ** d - v) % Mk:
        d += 1
    return d


def orbit_points(b: int, k: int, r: int) -> list[Fraction]:
    Mk = b ** k - 1
    d = period_b(b, k, r)
    return sorted(Fraction(r * b ** j % Mk, Mk) for j in range(d))


def disc_formula(ys: list[Fraction]) -> Fraction:
    d = len(ys)
    z = [y - Fraction(i + 1, d) for i, y in enumerate(sorted(ys))]
    return Fraction(1, d) + max(z) - min(z)


def disc_extremal(ys: list[Fraction]) -> Fraction:
    """sup over [a,c) of |mu[a,c) - (c-a)| through the extremal configurations."""
    pts = sorted(ys)
    d = len(pts)
    best = Fraction(0)
    for i in range(d):
        for j in range(i, d):
            best = max(best, Fraction(j - i + 1, d) - (pts[j] - pts[i]))
    ext = [Fraction(0)] + pts + [Fraction(1)]
    for i in range(len(ext)):
        for j in range(i + 1, len(ext)):
            best = max(best, (ext[j] - ext[i]) - Fraction(j - i - 1, d))
    return best


def section_B4_quotient():
    header("B4.2  Quotient K_{b^k}/K_b, periods, exact base-b discrepancies")
    total = 0
    for b in range(2, 7):
        for k in range(2, 6):
            Mk = b ** k - 1
            R = Mk // (b - 1)
            classes = set()
            for m in range(Mk):
                d = period_b(b, k, m)
                check(k % d == 0, "period divides k")
                # m/(b^k-1) in K_b  iff  reduced denominator divides b - 1  iff  d = 1
                den = Fraction(m, Mk).denominator
                inK = (b - 1) % den == 0
                check(inK == (d == 1) == (m % R == 0), "kernel membership of m/(b^k-1)")
                classes.add(m % R)
                if m:
                    ys = orbit_points(b, k, m)
                    D1, D2 = disc_formula(ys), disc_extremal(ys)
                    check(D1 == D2, f"discrepancy formula b={b} k={k} r={m}")
                    check((D1 == 1) == (d == 1), "D(mu) = 1 iff d = 1")
                    if d >= 2:
                        G = max([ys[0], 1 - ys[-1]] + [ys[i + 1] - ys[i] for i in range(d - 1)])
                        check(D1 <= max(1 - (ys[-1] - ys[0]), 1 - Fraction(1, d), G) < 1, "D(mu) < 1 bound")
                    total += 1
            check(len(classes) == R, "number of cosets")
            check(min(j for j in range(1, k + 1) if (b ** j - 1) % R == 0) == k, "order of b modulo R is k")
            # coset relation: m ~ m' iff (m-m')/(b^k-1) in F_b
            for _ in range(50):
                m1, m2 = RNG.randrange(Mk), RNG.randrange(Mk)
                same = ((b - 1) * (m1 - m2)) % Mk == 0
                check(same == ((m1 - m2) % R == 0), "coset relation")
    print(f"for b in [2,6], k in [2,5]: m/(b^k-1) in K_b iff R | m iff period 1; "
          f"exactly R = (b^k-1)/(b-1) cosets; b has order exactly k modulo R")
    print(f"exact discrepancy D(mu_c) = 1/d + max z - min z agrees with the extremal enumeration "
          f"for all {total} triples (b, k, r) with 1 <= r <= b^k-2")
    tab = []
    for (b, k, r) in ((2, 2, 1), (2, 2, 2), (3, 3, 5), (2, 3, 1), (2, 4, 3), (3, 2, 1), (5, 2, 7), (2, 6, 21)):
        ys = orbit_points(b, k, r)
        tab.append(f"({b},{k},{r}): d={len(ys)}, D={disc_formula(ys)}")
    print("examples (b,k,r): " + "; ".join(tab))
    check(disc_formula(orbit_points(2, 2, 1)) == Fraction(2, 3), "D(1/3;2) = 2/3")
    check(disc_formula(orbit_points(3, 3, 5)) == Fraction(20, 39), "D(5/26;3) = 20/39")


def pent_coeffs(K: int) -> list[int]:
    a = [0] * (K + 1)
    j = 1
    while True:
        p1 = j * (3 * j - 1) // 2
        p2 = j * (3 * j + 1) // 2
        if p1 > K:
            break
        a[p1] += (-1) ** j
        if p2 <= K:
            a[p2] += (-1) ** j
        j += 1
    return a


def section_B4_examples():
    header("B4.3  r/(b^k-1) + E_b: finite discrepancies, digit transfer, simple normality")
    N = 3000
    print("   b  k   r   d   D_inf(exact)    D_N(x;b)   1-D_N(E_b;b)  |gap| <= bound    D_N(x;b^k)")
    for (b, k, r) in ((2, 2, 1), (2, 2, 2), (3, 3, 5), (2, 3, 3), (2, 4, 5), (3, 2, 4), (5, 2, 6), (6, 2, 7)):
        K = k * N + 120
        pe = pent_coeffs(K)
        Eb = from_coeffs(b, K, lambda n: pe[n], 1)
        Mk = b ** k - 1
        c = Num(b, K, (b ** K * r) // Mk, 1)
        x = c + Eb
        ptsx = x.points(k * N)
        ptsE = Eb.points(N)
        ys = orbit_points(b, k, r)
        d = len(ys)
        Dinf = disc_formula(ys)
        DN = disc(ptsx[:N])
        DE = disc(ptsE)
        bound = (1 - DE) + d / N + 2e-9
        check(abs(DN - float(Dinf)) <= bound, "|D_N(x) - D(mu_c)| <= 1 - D_N(E_b) + d/N")
        DNk = disc(ptsx[::k][:N])
        print(f"  {b:>2} {k:>2} {r:>3} {d:>3}   {float(Dinf):.6f}      {DN:.6f}    {1 - DE:.6f}     "
              f"{abs(DN - float(Dinf)):.6f} <= {bound:.4f}   {DNk:.6f}")
    # M_N(E_b) bound
    for b in (2, 3, 5):
        K = N + 120
        pe = pent_coeffs(K)
        Eb = from_coeffs(b, K, lambda n: pe[n], 1)
        pts = Eb.points(N)
        MN = sum(min(p, 1 - p) for p in pts) / N
        bound = (2 * math.sqrt(2 * N / 3) + 2) / N
        check(MN <= bound, "M_N(E_b) <= (2 sqrt(2N/3) + 2)/N")
        print(f"M_{N}(E_{b}; {b}) = {MN:.6f} <= {bound:.6f}")
    # digit transfer: 1/3 + E_2 (base 2) and 5/26 + E_3 (base 3)
    print()
    for (b, k, r) in ((2, 2, 1), (3, 3, 5)):
        Nd = 20000
        Kd = Nd + 120
        pe = pent_coeffs(Kd)
        Eb = from_coeffs(b, Kd, lambda n: pe[n], 1)
        Mk = b ** k - 1
        x = Num(b, Kd, (b ** Kd * r) // Mk, 1) + Eb
        px = x.points(Nd)
        pE = Eb.points(Nd)
        ys = orbit_points(b, k, r)
        eta = min(min(abs(y - Fraction(j, b)) for j in range(b + 1)) for y in ys)
        block = to_digits(r, b, k)
        exc = 0
        dis = 0
        cnt = [0] * b
        for n in range(Nd):
            dx = int(px[n] * b)
            check(abs(px[n] * b - round(px[n] * b)) > 1e-8, "digit not certified")
            cnt[dx] += 1
            if dx != block[n % k]:
                dis += 1
            if min(pE[n], 1 - pE[n]) < float(eta) - 1e-9:
                check(dx == block[n % k], "digit of x equals digit of c when ||b^n w|| < eta")
            else:
                exc += 1
        freqs = ", ".join(f"{j}:{cnt[j] / Nd:.5f}" for j in range(b))
        print(f"{r}/{Mk} + E_{b} in base {b}: block {''.join(map(str, block))}, eta = {eta}; "
              f"{exc} of {Nd} positions have ||b^n E_b|| >= eta (Markov-exceptional); single digits of x "
              f"and c differ at {dis} positions, all of them Markov-exceptional; frequencies {freqs}")
        check(dis <= exc <= (2 * math.sqrt(2 * Nd / 3) + 2) / float(eta), "Markov bound for exceptional positions")
        # in K_{b^k}: D_N(x; b^k) near 1
        pk = px[::k][: Nd // k]
        print(f"   D_{Nd // k}(x; {b ** k}) = {disc(pk):.6f}   D_{Nd}(x; {b}) = {disc(px):.6f}")
    # simple normality classification
    print()
    for b in range(2, 7):
        row = []
        for k in range(1, 7):
            exists = False
            for r in range(1, b ** k - 1):
                dg = to_digits(r, b, k)
                if all(dg.count(j) * b == k for j in range(b)):
                    exists = True
                    check(period_b(b, k, r) >= 2, "simply normal witness lies outside K_b")
                    break
            check(exists == (k % b == 0), f"simple-normal witness exists iff b | k (b={b}, k={k})")
            row.append("y" if exists else ".")
        print(f"b={b}: K_(b^k) \\ K_b contains a base-b simply normal number for k=1..6: {' '.join(row)}")
    # b = 2: a simply normal element of K_2 (runs of length 1, 2, 3, ...)
    Nr = 20000
    bits = []
    j = 1
    sym = 0
    while len(bits) < Nr + 60:
        bits += [sym] * j
        sym ^= 1
        j += 1
    ones = sum(bits[:Nr]) / Nr
    MN = 0.0
    for n in range(Nr):
        v = int("".join(map(str, bits[n : n + 50])), 2) / 2 ** 50
        MN += min(v, 1 - v)
    MN /= Nr
    print(f"run-length example in K_2: frequency of 1 = {ones:.5f}, M_{Nr} = {MN:.5f}")
    check(abs(ones - 0.5) < 0.01 and MN < 0.03, "run-length example")


def main() -> None:
    data = section_B3_values(10 ** 6, 50000)
    least_witnesses(data)
    section_B3_densities(data)
    section_B3_expansions(data)
    construction_instances(data)
    section_B3_constants()
    section_B4_M()
    section_B4_quotient()
    section_B4_examples()
    print()
    print(f"All {CHECKS} assertions passed in {time.time() - T0:.1f} s.")


if __name__ == "__main__":
    main()
