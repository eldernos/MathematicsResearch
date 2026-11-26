#!/usr/bin/env python3
"""Exact and certified checks for Phase 21 Track A (exact discrepancy across radices).

A1  multiplicative Lambert series L_chi(b) = sum (1*chi)(n) b^-n in radices 2,3,4,5,6,10:
    the exact first-moment decomposition, conditional concentration of log c(n) on the
    support, odd-prime valuation means against their local laws, radix widths, and
    certified discrepancies with the width model (W + S lambda)/N.
A2  the Phase 17 class with split density delta: the threshold delta* = 1/(1+log 2),
    width and moment diagnostics, extremal base-b runs in M*2^m, certified discrepancies.
A3  Euler's square E_b^2: pentagonal convolution to 10^6, the prime-factorization
    criterion for every n <= 10^6, the Euler product for C_eta with its Selberg-Delange
    second-order term against exact support counts, certified discrepancies (b = 2,3,4).
A4  binary quadratic forms: class number one (D = -3,-4,-7,-8), idoneal (D = -20,-24)
    and D = -23 (class group Z/3): representation numbers against ideal-class group-ring
    products, genus ratios, the Jacobsthal structure, pi_J, certified discrepancies.

Standard library only.  Every discrepancy is computed from digit windows certified by
two integer carries and is within b^-P of the true value.  Ratios to asymptotic formulas
are finite measurements, not evidence for the constants.

Run from the repository root:  python -B scripts/phase21_radix.py
"""

from __future__ import annotations

import math
from bisect import bisect_left, bisect_right
from math import isqrt, log
from time import perf_counter

LOG2 = math.log(2.0)
EULER_GAMMA = 0.57721566490153286060651209
SHANKS = 0.58194865931729079777          # second-order Landau-Ramanujan constant
LANDAU_RAMANUJAN = 0.76422365358922066299
DELTA_STAR = 1 / (1 + LOG2)

CHECKS = [0]


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)
    CHECKS[0] += 1


def header(title):
    print()
    print(title)


# ------------------------------------------------------------------ arithmetic

def prime_flags(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for p in range(2, isqrt(n) + 1):
        if s[p]:
            s[p * p::p] = bytearray(len(range(p * p, n + 1, p)))
    return s


class Factor:
    """n = p^e * rest with p the least prime factor of n (tables P, E, R)."""

    def __init__(self, n):
        spf = list(range(n + 1))
        small = [p for p in range(2, isqrt(n) + 1) if all(p % q for q in range(2, isqrt(p) + 1))]
        for p in reversed(small):           # smaller primes overwrite larger ones
            spf[p * p::p] = [p] * len(range(p * p, n + 1, p))
        E = [0] * (n + 1)
        R = [1] * (n + 1)
        for m in range(2, n + 1):
            p = spf[m]
            q = m // p
            if q > 1 and spf[q] == p:
                E[m] = E[q] + 1
                R[m] = R[q]
            else:
                E[m] = 1
                R[m] = q
        self.n, self.P, self.E, self.R = n, spf, E, R

    def multiplicative(self, local, n=None):
        n = self.n if n is None else n
        P, E, R = self.P, self.E, self.R
        f = [0] * (n + 1)
        f[1] = 1
        cache = {}
        for m in range(2, n + 1):
            key = (P[m], E[m])
            v = cache.get(key)
            if v is None:
                v = cache[key] = local(*key)
            f[m] = v * f[R[m]]
        return f

    def additive(self, local, n=None):
        n = self.n if n is None else n
        P, E, R = self.P, self.E, self.R
        f = [0] * (n + 1)
        for m in range(2, n + 1):
            f[m] = local(P[m], E[m]) + f[R[m]]
        return f


def kron(D, p):
    """Kronecker symbol (D/p) for a prime p."""
    if p == 2:
        if D % 2 == 0:
            return 0
        return 1 if D % 8 in (1, 7) else -1
    r = D % p
    if r == 0:
        return 0
    return 1 if pow(r, (p - 1) // 2, p) == 1 else -1


def lambert_local(s, e):
    """(1*chi)(p^e) when chi(p) = s."""
    if s == 1:
        return e + 1
    if s == -1:
        return 1 - e % 2
    return 1


def support_constant(chi, q, L1, flags):
    """C_chi = (L(1,chi)/pi prod_{chi(p)=-1}(1-p^-2)^-1 prod_{p|q}(1-1/p)^-1)^(1/2)."""
    prod = 1.0
    for p in range(2, len(flags)):
        if flags[p]:
            s = chi(p)
            if s == -1:
                prod /= 1 - p ** -2.0
            elif s == 0:
                prod /= 1 - 1 / p
    return math.sqrt(L1 / math.pi * prod)


def valuation(x, b):
    v = 0
    while x % b == 0:
        x //= b
        v += 1
    return v, x


def ndig(x, b):
    n = 0
    while x:
        x //= b
        n += 1
    return n


# ------------------------------------------------------- certified digit windows

def precision(b):
    return max(12, math.ceil(40 * LOG2 / math.log(b)))


def certified_digits(coef, b, K, need, tail):
    """Digits d[1..need] of sum_{m=1}^K coef[m] b^-m + theta*tail*b^-K (|theta| <= 1).

    Both endpoints are carried exactly; equal digits certify the true expansion."""
    out = []
    for sgn in (-1, 1):
        carry = sgn * tail
        d = [0] * (K + 1)
        for i in range(K, 0, -1):
            carry, d[i] = divmod(coef[i] + carry, b)
        out.append(d)
    lo, hi = out
    check(lo[1:need + 1] == hi[1:need + 1], f"digit certification failed (b={b})")
    return lo


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


def disc_windows(y, bp, N):
    hi = lo = 0
    for i, v in enumerate(sorted(y[:N]), 1):
        hi = max(hi, i * bp - N * v)
        lo = max(lo, N * v - (i - 1) * bp)
    return (hi + lo) / (N * bp)


def centered_arc_bound(y, bp, N):
    """min_r 2r + #{dist > r}/N >= 1 - D_N (with certified upper distances)."""
    dh = sorted(min(v + 1, bp - v) for v in y[:N])
    best = 1.0
    for k, v in enumerate(dh):
        best = min(best, 2 * v / bp + (N - 1 - k) / N)
    return best


def lemma_lower_bound(y, bp, N):
    """Coefficient-transfer Lemma 3.3: max min(bulk(zeta), marked(eta), eta - zeta)."""
    dh = sorted(min(v + 1, bp - v) for v in y[:N])
    dl = sorted(min(v, bp - v - 1) for v in y[:N])
    best = 0.0
    G = int(8 * math.log2(bp))
    grid = [bp * 2.0 ** (-k / 8) for k in range(G)]
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


def width_stats(a, b, N):
    """Sources n <= N: S, W = sum u_b(n), lambda = log_b(N/S), mean V_b."""
    S = W = Vs = 0
    for n in range(1, N + 1):
        x = a[n]
        if x:
            v, u = valuation(abs(x), b)
            S += 1
            Vs += v
            W += ndig(u, b)
    lam = math.log(N / S, b)
    return S, W, lam, Vs / S


def measure(name, a, b, Ns, tail, asym=None, quiet=False):
    """Certified 1 - D_N with Lemma 3.3 lower bound, centred-arc upper bound and the
    width model (W + S lambda)/N; asym(N) is the asymptotic formula, if given."""
    P = precision(b)
    Nmax = max(Ns)
    K = Nmax + P + 64
    d = certified_digits(a, b, K, Nmax + P, tail)
    y = windows(d, b, Nmax, P)
    bp = b ** P
    h = float(b) ** (-P)
    rows = []
    for N in Ns:
        gap = 1 - disc_windows(y, bp, N)
        lb = lemma_lower_bound(y, bp, N)
        ub = centered_arc_bound(y, bp, N)
        check(lb <= gap + h + 1e-12, f"{name}: Lemma 3.3 bound exceeds 1-D_N")
        check(gap <= ub + h + 1e-12, f"{name}: centred-arc bound below 1-D_N")
        S, W, lam, mV = width_stats(a, b, N)
        model = (W + S * lam) / N
        rows.append((N, gap, lb, ub, S, W, lam, model, mV))
    if not quiet:
        print(f"  {name}  (b={b}, P={P}, certified to b^-P)")
        for (N, gap, lb, ub, S, W, lam, model, mV) in rows:
            extra = f"  asym={asym(N):.4f} gap/asym={gap / asym(N):.3f}" if asym else ""
            print(f"    N=2^{N.bit_length() - 1:2d} 1-D_N={gap:.5f} LB={lb:.5f} UB={ub:.5f}"
                  f" S={S} W/S={W / S:.3f} lam={lam:.3f} model={model:.4f}"
                  f" gap/model={gap / model:.3f}{extra}")
    return rows


def asym_formula(C, kappa, width_coeff, b):
    """C (kappa + width_coeff) / log b * loglogN / (log N)^kappa."""
    def f(N):
        L = math.log(N)
        return C * (kappa + width_coeff) / math.log(b) * math.log(L) / L ** kappa
    return f


def is_power_of_two(b):
    return b & (b - 1) == 0


# ----------------------------------------------------------------------- A1

def chi4(p):
    return 0 if p == 2 else (1 if p % 4 == 1 else -1)


def section_a1(F, flags):
    header("A1  multiplicative Lambert series L_chi4(b) = sum (r_2(n)/4) b^-n")
    n_max = F.n
    c = F.multiplicative(lambda p, e: lambert_local(chi4(p), e))
    lim = 4096
    r2 = [0] * (lim + 1)
    for x in range(-isqrt(lim), isqrt(lim) + 1):
        for y in range(-isqrt(lim), isqrt(lim) + 1):
            s = x * x + y * y
            if 1 <= s <= lim:
                r2[s] += 1
    check(all(r2[n] == 4 * c[n] for n in range(1, lim + 1)), "r_2 = 4(1*chi_4)")
    K = support_constant(chi4, 4, math.pi / 4, flags)
    check(abs(K - LANDAU_RAMANUJAN) < 1e-6, "Landau-Ramanujan constant")
    print(f"  r_2 = 4(1*chi_4) to {lim}; C_chi4 = K = {K:.9f} (Euler product to {len(flags) - 1})")

    # support prefix counts and the split-prime count omega_s
    Scount = [0] * (n_max + 1)
    for n in range(1, n_max + 1):
        Scount[n] = Scount[n - 1] + (1 if c[n] else 0)
    om = F.additive(lambda p, e: 1 if p % 4 == 1 else 0)

    # exact first-moment decomposition: sum_{supp} omega_s = sum_{p split} S(N/p)
    split = [p for p in range(5, n_max + 1, 4) if flags[p]]
    print("  exact first moment and conditional concentration on the support:")
    for N in (2 ** 14, 2 ** 17, n_max):
        lhs = sum(om[n] for n in range(1, N + 1) if c[n])
        rhs = sum(Scount[N // p] for p in split if p <= N)
        check(lhs == rhs, "sum_supp omega_s = sum_p S(N/p)")
        lhs_log = sum(log(c[n]) for n in range(1, N + 1) if c[n])
        rhs_log = 0.0
        for p in split:
            if p > N:
                break
            e, pe = 1, p
            while pe <= N:
                rhs_log += log(e + 1) * (Scount[N // pe] - Scount[N // (pe * p)])
                e += 1
                pe *= p
        check(abs(lhs_log - rhs_log) <= 1e-9 * max(1.0, lhs_log), "first-moment identity for log c")
        S = Scount[N]
        LL = log(log(N))
        mom = {}
        for t in (-1.0, -0.5, 0.5, 1.0):
            mom[t] = sum(c[n] ** t for n in range(1, N + 1) if c[n]) / S
        mlog = lhs_log / S
        print(f"    N={N:8d} S={S} E[omega_s]={lhs / S:.4f} (LL/2={LL / 2:.4f})"
              f" E[log c]/LL={mlog / LL:.4f} (limit log2/2={LOG2 / 2:.4f})"
              f"  E[c^t] t=-1,-1/2,1/2,1: " + " ".join(f"{mom[t]:.4f}" for t in mom))

    # odd-prime valuations: bounded mean, local law, and the e >= q-1 mechanism
    N = n_max
    sup = [n for n in range(1, N + 1) if c[n]]
    S = len(sup)
    print("  odd-prime valuations v_q(c(n)) on the support (bounded conditional mean):")
    for q in (3, 5, 7):
        tot = 0
        for n in sup:
            v, _ = valuation(c[n], q)
            if v:
                tot += v
                m, ok = n, False      # some split p^e || n with e >= q-1
                while m > 1:
                    p, e = F.P[m], F.E[m]
                    if p % 4 == 1 and e >= q - 1:
                        ok = True
                    m = F.R[m]
                check(ok, "q | c(n) forces a split p^e || n with e >= q-1")
        local = 0.0
        for p in split[:20000]:
            s = sum(valuation(e + 1, q)[0] * p ** -float(e) for e in range(q - 1, 80))
            local += (1 - 1 / p) * s
        mean = tot / S
        check(mean < 2 * local + 0.01, "valuation mean against its local law")
        print(f"    q={q}: mean v_q(c) = {mean:.5f}; local law sum_p (1-1/p) sum_e v_q(e+1) p^-e"
              f" = {local:.5f}; sum v_q(c) / (N/sqrt(log N)) = {tot / (N / math.sqrt(log(N))):.4f}")
    for b in (3, 5, 6, 10):
        mV = sum(valuation(c[n], b)[0] for n in sup) / S
        print(f"    b={b:2d}: mean V_b = v_b(c(n)) over the support = {mV:.4f}")

    # certified discrepancies in six radices
    print("  certified discrepancies (tail bound c(m) <= tau(m) <= 2 sqrt m):")
    Ns = (2 ** 12, 2 ** 14, 2 ** 16, 2 ** 17)
    out = {}
    for b in (2, 3, 4, 5, 6, 10):
        Kc = max(Ns) + precision(b) + 64
        tail = 4 * isqrt(Kc + 1) + 4
        w = 0.0 if is_power_of_two(b) else LOG2 / 2
        rows = measure(f"L_chi4({b})", c, b, Ns, tail, asym_formula(K, 0.5, w, b))
        out[b] = rows
    # radix contrast at the largest N: the width term separates 2^k from other radices
    for b in (2, 3, 4, 5, 6, 10):
        (_, gap, _, _, S, W, lam, model, mV) = out[b][-1]
        print(f"    b={b:2d}: mean u_b/lambda = {W / S / lam:.3f}"
              f" (limit {'0' if is_power_of_two(b) else 'log 2 = 0.693'}),"
              f" gap*log b = {gap * math.log(b):.4f}")
    w2 = out[2][-1][5] / out[2][-1][4]
    w3 = out[3][-1][5] / out[3][-1][4]
    check(w3 > w2, "base-3 widths exceed base-2 widths")
    return c, K


# ----------------------------------------------------------------------- A2

def class_local(split_test):
    """Phase 17 class modulo 5: c(p^e) = e+1 on S, [e even] off S, 1 at p = 5."""
    def local(p, e):
        if p == 5:
            return 1
        return e + 1 if split_test(p) else 1 - e % 2
    return local


def extremal_runs(x, b):
    """Digits of x (least significant first) and the longest run of 0 or b-1."""
    d = []
    while x:
        x, r = divmod(x, b)
        d.append(r)
    best = cur = 0
    prev = None
    for r in d:
        if r in (0, b - 1) and r == prev:
            cur += 1
        elif r in (0, b - 1):
            cur = 1
        else:
            cur = 0
        prev = r
        best = max(best, cur)
    return d, best


def internal_near_zero(d, b, lam):
    """#{j in (lam, len]: digits j-lam..j-1 all 0 or all b-1} (positions from 0)."""
    L = len(d)
    count = 0
    for j in range(lam + 1, L + 1):
        block = d[j - lam:j]
        if all(v == 0 for v in block) or all(v == b - 1 for v in block):
            count += 1
    return count


def section_a2(F, flags):
    header("A2  the Phase 17 class with split density delta; threshold delta* = 1/(1+log 2)")
    check(abs(DELTA_STAR * LOG2 - (1 - DELTA_STAR)) < 1e-15, "delta* log 2 = 1 - delta*")
    print(f"  delta* = {DELTA_STAR:.6f}; omega = delta log 2 / kappa is the limiting u_b/lambda"
          " in radices that are not powers of 2")
    for delta in (0.25, 0.5, DELTA_STAR, 0.75):
        kappa = 1 - delta
        om = delta * LOG2 / kappa
        lo, hi = 2 * kappa if om >= 1 else kappa + delta * LOG2, kappa + delta * LOG2
        regime = "sub-threshold: exact" if om < 1 - 1e-12 else (
            "threshold: exact" if abs(om - 1) < 1e-9 else "beyond: unconditional bounds")
        print(f"    delta={delta:.4f} kappa={kappa:.4f} omega={om:.4f}  constant/C_f*log b in"
              f" [{lo:.4f}, {hi:.4f}]  ({regime}); radix 2^k: {kappa:.4f}")
        check((om < 1) == (delta < DELTA_STAR - 1e-12) or abs(delta - DELTA_STAR) < 1e-12,
              "threshold equivalence")
    n_max = F.n
    classes = {0.25: lambda p: p % 5 == 1, 0.75: lambda p: p % 5 != 1}
    coeffs = {}
    for delta, test in classes.items():
        c = F.multiplicative(class_local(test))
        # c = 1 * g with g completely multiplicative: g(p) = 1 on S, -1 off S, 0 at 5
        g = F.multiplicative(lambda p, e: 0 if p == 5 else (1 if test(p) else (-1) ** e), 2000)
        check(all(c[n] == sum(g[d] for d in range(1, n + 1) if n % d == 0) for n in range(1, 1501)),
              "c = 1 * g for the class")
        coeffs[delta] = c
        Scount = [0] * (n_max + 1)
        for n in range(1, n_max + 1):
            Scount[n] = Scount[n - 1] + (1 if c[n] else 0)
        omS = F.additive(lambda p, e: 1 if p != 5 and test(p) else 0)
        Sp = [p for p in range(2, n_max + 1) if flags[p] and p != 5 and test(p)]
        kappa = 1 - delta
        for N in (2 ** 14, 2 ** 17, n_max):
            lhs = sum(omS[n] for n in range(1, N + 1) if c[n])
            rhs = sum(Scount[N // p] for p in Sp if p <= N)
            check(lhs == rhs, "first-moment identity for omega_S")
            S = Scount[N]
            LL = log(log(N))
            mlog = sum(log(c[n]) for n in range(1, N + 1) if c[n]) / S
            # Rankin moments E[z^omega_S] on the support for z = 1/2, 2
            mz = [sum(z ** omS[n] for n in range(1, N + 1) if c[n]) / S for z in (0.5, 2.0)]
            print(f"    delta={delta}: N={N:8d} S(log N)^kappa/N={S * log(N) ** kappa / N:.4f}"
                  f" E[omega_S]/LL={lhs / S / LL:.4f} (delta={delta}) E[log c]/(LL log 2)="
                  f"{mlog / LL / LOG2:.4f} E[2^-omega]={mz[0]:.4f} E[2^omega]={mz[1]:.4f}")

    # extremal base-b runs in M 2^m: the arithmetic statistic behind the beyond-threshold gap
    print("  extremal runs (0 or b-1) in base-b expansions of M*2^m (M = 1,3,5), 100 <= m <= 2000:")
    for b in (3, 5, 6, 10):
        worst_frac = 0.0
        worst_log = 0.0
        last_long = 0
        zsum = 0
        for M in (1, 3, 5):
            x = M << 99
            for m in range(100, 2001):
                x <<= 1
                d, R = extremal_runs(x, b)
                L = len(d)
                worst_frac = max(worst_frac, R / L)
                worst_log = max(worst_log, R / math.log(m, b))
                if R >= 0.1 * L:
                    last_long = max(last_long, m)
                check(R < 0.2 * L, "no extremal run of length >= len/5")
                if m % 50 == 0:
                    zsum += internal_near_zero(d, b, max(1, L // 4))
        check(zsum == 0, "no internal near-zero window of length len/4")
        print(f"    b={b:2d}: max R/len = {worst_frac:.4f}, max R/log_b m = {worst_log:.3f};"
              f" last m with R >= len/10: {last_long}; near-zero windows of length len/4: {zsum}")

    print("  certified discrepancies (tail: c(m) <= tau(m) <= 2 sqrt m):")
    Ns = (2 ** 12, 2 ** 14, 2 ** 16)
    for delta, c in coeffs.items():
        for b in (2, 3):
            Kc = max(Ns) + precision(b) + 64
            measure(f"class delta={delta}", c, b, Ns, 4 * isqrt(Kc + 1) + 4)
    return coeffs


# ----------------------------------------------------------------------- A3

def pentagonal_square(limit):
    """a_2(n) for E(q)^2 = sum a_2(n) q^n by convolution of the pentagonal series."""
    pents = [(0, 1)]
    k = 1
    while k * (3 * k - 1) // 2 <= limit:
        s = -1 if k % 2 else 1
        pents.append((k * (3 * k - 1) // 2, s))
        if k * (3 * k + 1) // 2 <= limit:
            pents.append((k * (3 * k + 1) // 2, s))
        k += 1
    pents.sort()
    a = [0] * (limit + 1)
    for i, (p, s) in enumerate(pents):
        if 2 * p > limit:
            break
        a[2 * p] += 1
        for q, t in pents[i + 1:]:
            if p + q > limit:
                break
            a[p + q] += 2 * s * t
    return a


def numeric_Lprime1(chi, q, K):
    """-sum_{n} chi(n) log n / n, summed over K full periods (chi even: O(1/K^2) error)."""
    tot = 0.0
    res = [(a, chi(a)) for a in range(1, q + 1) if chi(a)]
    for k in range(K):
        base = k * q
        for a, s in res:
            m = base + a
            tot -= s * log(m) / m
    return tot


def section_a3(flags):
    header("A3  Euler's square E_b^2 = sum a_2(n) b^-n and eta(12 tau)^2")
    NE = 10 ** 6
    t = perf_counter()
    a2 = pentagonal_square(NE)
    # prime-factorization criterion for every n <= NE (12n+1 < 3466^2)
    rem = [12 * n + 1 for n in range(NE + 1)]
    prod = [1] * (NE + 1)
    bad = bytearray(NE + 1)
    for p in range(5, isqrt(12 * NE + 1) + 1):
        if not flags[p]:
            continue
        n0 = (-pow(12, -1, p)) % p
        split = p % 12 == 1
        for n in range(n0, NE + 1, p):
            x = rem[n]
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            rem[n] = x
            if split:
                prod[n] *= e + 1
            elif e & 1:
                bad[n] = 1
    mismatch = 0
    neg = 0
    for n in range(1, NE + 1):
        r = rem[n]
        if r > 1:
            if r % 12 == 1:
                prod[n] *= 2
            else:
                bad[n] = 1
        want = 0 if bad[n] else prod[n]
        if abs(a2[n]) != want:
            mismatch += 1
        if a2[n] < 0:
            neg += 1
    check(mismatch == 0, "E^2 factorization criterion for every n <= 10^6")
    S_E = [0] * (NE + 1)
    for n in range(1, NE + 1):
        S_E[n] = S_E[n - 1] + (1 if a2[n] else 0)
    print(f"  criterion |a_2(n)| = prod_(p=1 mod 12)(v_p(12n+1)+1) (else 0) verified for all"
          f" n <= {NE} [{perf_counter() - t:.1f} s]; S_eta({NE}) = {S_E[NE]}, negative: {neg}")

    # Euler product and the Selberg-Delange constants
    lp1 = 0.0      # sum over p >= 5, p != 1 mod 12, of log p / (p^2 - 1)
    lp3 = 0.0      # sum over p = 3 mod 4 of log p / (p^2 - 1)
    prod2 = 1.0
    for p in range(3, len(flags)):
        if flags[p]:
            if p % 4 == 3:
                lp3 += log(p) / (p * p - 1)
            if p >= 5 and p % 12 != 1:
                prod2 /= (1 - p ** -2.0) ** 2
                lp1 += log(p) / (p * p - 1)
    G4 = math.pi ** 2 * log(2 + math.sqrt(3)) / 54 * prod2
    lam0 = G4 ** 0.25 / math.gamma(0.25)
    C_eta = 12 * lam0
    LL4 = EULER_GAMMA + 2 * LOG2 + 3 * log(math.pi) - 4 * math.lgamma(0.25)
    LL3 = EULER_GAMMA + log(2 * math.pi) - 3 * (math.lgamma(1 / 3) - math.lgamma(2 / 3))
    chi12 = lambda a: {1: 1, 5: -1, 7: -1, 11: 1}.get(a % 12, 0)  # noqa: E731
    L12 = log(2 + math.sqrt(3)) / math.sqrt(3)
    LL12 = numeric_Lprime1(chi12, 12, 20000) / L12
    # cross-check the closed forms for odd characters by direct summation
    for chi, q, L1, closed in ((lambda a: (0, 1, 0, -1)[a % 4], 4, math.pi / 4, LL4),
                               (lambda a: (0, 1, -1)[a % 3], 3, math.pi / (3 * math.sqrt(3)), LL3)):
        Kp = 200000
        num = numeric_Lprime1(chi, q, Kp)
        corr = sum(a * chi(a) for a in range(1, q + 1)) / q * log(Kp * q) / (Kp * q)
        check(abs((num + corr) / L1 - closed) < 2e-4, "closed form for L'/L(1, chi) (odd chi)")
    D_LR = 0.5 * (EULER_GAMMA + LL4 - LOG2 - 2 * lp3) - 1
    C_LR = -0.5 * D_LR
    check(abs(C_LR - SHANKS) < 2e-4, "Selberg-Delange second-order term reproduces Shanks")
    D_S = 0.25 * (EULER_GAMMA + LOG2 + log(3) / 4 - LOG2 / 3 + LL4 + LL3 + LL12 - 4 * lp1) - 1
    C2 = -0.75 * D_S
    print(f"  L'/L(1,chi): chi_-4 {LL4:.6f}, chi_-3 {LL3:.6f}, chi_12 {LL12:.6f};"
          f" Landau-Ramanujan second-order term {C_LR:.6f} (Shanks {SHANKS:.6f})")
    print(f"  C_eta = 12 (pi^2 log(2+sqrt3)/54 prod_(p>=5, p!=1 mod 12)(1-p^-2)^-2)^(1/4) / Gamma(1/4)"
          f" = {C_eta:.6f};  second-order coefficient {C2:.5f}")
    print("  exact S_eta(N) against S(x) ~ (C_eta/12) x (log x)^(-3/4) (1 + c2/log x), x = 12N+1:")
    c3s = []
    for N in (10 ** 3, 10 ** 4, 10 ** 5, 2 * 10 ** 5, 5 * 10 ** 5, 10 ** 6):
        x = 12 * N + 1
        one = lam0 * x / log(x) ** 0.75
        two = one * (1 + C2 / log(x))
        exact = S_E[N] + 1
        err = exact / two - 1
        c3s.append(err * log(x) ** 2)
        check(N < 10 ** 4 or 1.0 < c3s[-1] < 2.5, "third-order residual is O(1/log^2 x)")
        check(N < 10 ** 4 or abs(err) < 0.015, "two-term Selberg-Delange prediction for S_eta")
        print(f"    N={N:8d} S_eta={S_E[N]:7d}  S(log N)^(3/4)/N={S_E[N] * log(N) ** 0.75 / N:.4f}"
              f"  exact/one-term={exact / one:.4f}  exact/two-term={1 + err:.5f}"
              f"  (residual x log^2 x = {c3s[-1]:.3f})")

    print("  certified discrepancies of E_b^2 (signed; tail |a_2(m)| <= r_2(24m+2) <= 8 sqrt(24m+2)):")
    Ns = (2 ** 12, 2 ** 14, 2 ** 16, 2 ** 17)
    for b in (2, 3, 4):
        Kc = max(Ns) + precision(b) + 64
        w = 0.0 if is_power_of_two(b) else LOG2 / 4
        measure("E_b^2", a2, b, Ns, 16 * isqrt(24 * Kc + 26) + 16, asym_formula(C_eta, 0.75, w, b))
    return a2, C_eta


# ----------------------------------------------------------------------- A4

def form_counts(a, b0, c, X):
    """r_Q(n) for n <= X by direct enumeration of Q(x,y) = a x^2 + b0 xy + c y^2."""
    D = b0 * b0 - 4 * a * c
    r = [0] * (X + 1)
    ymax = isqrt(4 * a * X // (-D)) + 1
    for y in range(-ymax, ymax + 1):
        disc = 4 * a * X + D * y * y
        if disc < 0:
            continue
        sq = isqrt(disc)
        lo = (-b0 * y - sq) // (2 * a) - 1
        hi = (-b0 * y + sq) // (2 * a) + 1
        cy = c * y * y
        for x in range(lo, hi + 1):
            v = a * x * x + b0 * x * y + cy
            if v <= X:
                r[v] += 1
    return r


def conv(u, v, h):
    out = [0] * h
    for i, x in enumerate(u):
        if x:
            for j, y in enumerate(v):
                if y:
                    out[(i + j) % h] += x * y
    return out


# (D, w, h, reduced forms); form i corresponds to the ideal class i (form 1 also to -1)
DISCRIMINANTS = [
    (-3, 6, 1, [(1, 1, 1)]),
    (-4, 4, 1, [(1, 0, 1)]),
    (-7, 2, 1, [(1, 1, 2)]),
    (-8, 2, 1, [(1, 0, 2)]),
    (-20, 2, 2, [(1, 0, 5), (2, 2, 3)]),
    (-24, 2, 2, [(1, 0, 6), (2, 0, 3)]),
    (-23, 2, 3, [(1, 1, 6), (2, 1, 3)]),
]
GENERA = {-3: 1, -4: 1, -7: 1, -8: 1, -20: 2, -24: 2, -23: 1}


def class_vectors(F, D, h, cls, X):
    """a_C(n) = #{ideals of norm n in class C} as vectors over Z/h (group-ring products)."""
    def local(p, e):
        s_ = kron(D, p)
        v = [0] * h
        if s_ == -1:
            if e % 2 == 0:
                v[0] = 1
            return tuple(v)
        g = cls[p]
        if s_ == 0:
            v[(e * g) % h] = 1
            return tuple(v)
        for i in range(e + 1):
            v[(g * (2 * i - e)) % h] += 1
        return tuple(v)

    vec = [None] * (X + 1)
    vec[1] = tuple([1] + [0] * (h - 1))
    cache = {}
    for m in range(2, X + 1):
        key = (F.P[m], F.E[m])
        f = cache.get(key)
        if f is None:
            f = cache[key] = local(*key)
        vec[m] = tuple(conv(f, vec[F.R[m]], h))
    return vec


def section_a4(F, flags):
    header("A4  binary quadratic forms Theta_Q(1/b) - 1 = sum r_Q(n) b^-n")
    Ns = (2 ** 14, 2 ** 16)
    X = max(Ns) + precision(2) + 64
    print(f"  representation numbers r_Q(n), n <= {X}, against ideal-class group-ring products:")
    results = {}
    for (D, w, h, forms) in DISCRIMINANTS:
        chi = lambda p, D=D: kron(D, p)  # noqa: E731
        reps = [form_counts(a, b0, c, X) for (a, b0, c) in forms]
        cls = {}
        for p in range(2, X + 1):
            if flags[p] and chi(p) != -1:
                hits = [i for i in range(len(forms)) if reps[i][p] > 0]
                check(len(hits) == 1, "each split/ramified prime is represented by one class pair")
                cls[p] = hits[0]
        vec = class_vectors(F, D, h, cls, X)
        a = [0] + [sum(vec[n]) for n in range(1, X + 1)]
        aa = F.multiplicative(lambda p, e, D=D: lambert_local(kron(D, p), e), X)
        check(a[1:] == aa[1:X + 1], "sum over classes = (1*chi_D)")
        for i in range(len(forms)):
            check(all(reps[i][n] == w * vec[n][i] for n in range(1, X + 1)),
                  f"r_Q = w a_C for D={D}, form {forms[i]}")
        mult = [1] + [2 if h == 3 else 1] * (len(forms) - 1)
        check(all(sum(mult[i] * reps[i][n] for i in range(len(forms))) == w * a[n]
                  for n in range(1, X + 1)), "sum over classes of r_Q = w (1*chi_D)")
        Ba = sum(1 for n in range(1, X + 1) if a[n])
        Bs = [sum(1 for n in range(1, X + 1) if reps[i][n]) for i in range(len(forms))]
        if h == 2:   # idoneal: genera are disjoint and r_Q = w a 1_genus
            check(sum(Bs) == Ba, "idoneal: each represented n lies in exactly one genus")
            for i in range(2):
                check(all(reps[i][n] in (0, w * a[n]) for n in range(1, X + 1)),
                      "idoneal: r_Q(n) = w (1*chi)(n) 1_genus(n)")
        L1 = 2 * math.pi * h / (w * math.sqrt(-D))
        C_D = support_constant(chi, -D, L1, flags)
        lnX = log(X)
        print(f"    D={D:4d} h={h} w={w}: C_chi = {C_D:.6f}; B_D(X)/(C X/sqrt log X) ="
              f" {Ba / (C_D * X / math.sqrt(lnX)):.4f}; B_Q/B_D = "
              + ", ".join(f"{forms[i]}: {Bs[i] / Ba:.4f}" for i in range(len(forms))))
        results[D] = (forms, reps, a, vec, C_D / GENERA[D], cls, w)

    # D = -23: concentration, the Jacobsthal structure and pi_J
    forms, reps, a, vec, C23, cls, w = results[-23]
    one_minus_piJ = 1.0
    for p, g in cls.items():
        if g == 1 and kron(-23, p) == 1:
            one_minus_piJ *= 1 - (1 - 1 / p) * p ** -2.0 / (1 - p ** -3.0)
    piJ = 1 - one_minus_piJ
    jt = nj = jt_principal = n_principal = ratio_ok = big = 0
    for n in range(1, X + 1):
        if not a[n]:
            continue
        m, J, s_, prodnp = n, False, 1, 1
        while m > 1:
            p, e = F.P[m], F.E[m]
            if kron(-23, p) == 1:
                if cls[p] == 1:
                    prodnp *= e + 1
                    if e % 3 == 2:
                        J = True
                else:
                    s_ *= e + 1
            m = F.R[m]
        if J:
            jt += 1
            check(all(3 * vec[n][C] == a[n] for C in range(3)), "J-type: a_C(n) = a(n)/3")
        else:
            nj += 1
            for C in range(3):
                beta, rmd = divmod(3 * vec[n][C] - a[n], s_)
                check(rmd == 0 and beta in (-2, -1, 1, 2),
                      "non-J: 3 a_C = a + s beta with beta in {+-1, +-2}")
                if prodnp % 4 == 0:
                    check(valuation(3 * vec[n][C] // s_, 2)[0] <= 1,
                          "non-J: v_2(3 a_C / s) <= 1 (Jacobsthal structure)")
        if reps[0][n]:
            n_principal += 1
            jt_principal += 1 if J else 0
        if a[n] >= 8:
            big += 1
            if abs(3 * vec[n][0] / a[n] - 1) <= 0.5:
                ratio_ok += 1
    print(f"  D=-23 (Cl = Z/3): 1 - pi_J = prod_(p nonprincipal split)(1 - (1-1/p)p^-2/(1-p^-3))"
          f" = {one_minus_piJ:.6f}; pi_J = {piJ:.6f}")
    print(f"    J-type fraction: on supp(1*chi) {jt / (jt + nj):.4f}, on supp(r_principal)"
          f" {jt_principal / n_principal:.4f}; |3 a_C0/a - 1| <= 1/2 for {ratio_ok / big:.4f}"
          f" of n with a(n) >= 8")
    fac23 = 1 + 2 / 3 * one_minus_piJ * LOG2
    print(f"    base-2^k constant factor 1 + (2/3)(1-pi_J) log 2 = {fac23:.6f}"
          f" (h_0 = 1: 1; radices other than 2^k: 1 + log 2 = {1 + LOG2:.6f})")

    print("  certified discrepancies (tail r_Q(m) <= w tau(m) <= 2w sqrt m):")
    for D in (-3, -4, -7, -8, -20, -24, -23):
        forms, reps, a, vec, CQ, cls, w = results[D]
        for i, f in enumerate(forms):
            for b in (2, 3):
                if is_power_of_two(b):
                    factor = fac23 if D == -23 else 1.0
                else:
                    factor = 1 + LOG2
                asym = asym_formula(CQ * factor, 0.5, 0.0, b)
                Kc = max(Ns) + precision(b) + 64
                measure(f"D={D} Q={f}", reps[i], b, Ns, 4 * w * isqrt(Kc + 1) + 4 * w, asym)
    return results


def main():
    t0 = perf_counter()
    F = Factor(2 ** 20)
    flags = prime_flags(2 ** 21)
    print(f"factor tables to 2^20 and primes to 2^21 in {perf_counter() - t0:.1f} s")
    t = perf_counter()
    section_a1(F, flags)
    print(f"  [A1 {perf_counter() - t:.1f} s]")
    t = perf_counter()
    section_a2(F, flags)
    print(f"  [A2 {perf_counter() - t:.1f} s]")
    t = perf_counter()
    section_a3(flags)
    print(f"  [A3 {perf_counter() - t:.1f} s]")
    t = perf_counter()
    section_a4(F, flags)
    print(f"  [A4 {perf_counter() - t:.1f} s]")
    print(f"\nall Phase 21 Track A checks passed ({CHECKS[0]} assertions) in {perf_counter() - t0:.1f} s")


if __name__ == "__main__":
    main()
