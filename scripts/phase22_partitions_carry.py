#!/usr/bin/env python3
"""Phase 22, Track D (D3, D4) and Track G1 Correction C (Lemma S).

Finite verification for notes/phase22/partitions-carry-and-lemma-s.md.
Standard library only.  Every discrepancy, frequency, density and ratio printed
here is a finite measurement; none of them is evidence for an asymptotic claim.

Sections
  S  Lemma S: support characterisation of a_2, exact shifted pair counts,
     g^2 | h, the CRT parametrisation and its determinant 144 h / g^2, local
     densities, the Selberg inequality on explicit instances (|lambda_d| <= 1,
     main term + remainder), the Rankin lower bound for G(xi), the Mertens
     constant for primes = 5, 7, 11 (mod 12), the v, v' series constants and the
     singular-series average.
  D3 Binary (Mahler) partitions, the exact finite Mahler identity, the window,
     chain-period formula T_K = m_K D_{K-1}, the coprime-period formula, the
     tracking/period table, the subsequence Fourier-vanishing example, Euler's
     odd/distinct identities, finite discrepancies.
  D4 NAF / minimal signed-digit weights, the counting and exponent lemmas, the
     carry normalisation, multiplicities, signed-digit and raw widths for
     E_2^2, E_2^4, E_2^6, E_2^8, D(Theta_3^2), D(E_2^2), F, the quadratic-width
     example, and the canonical nearest-integer (net) representation.
"""

import cmath
import math
import random
import sys
import time
from array import array
from fractions import Fraction
from functools import lru_cache
from math import comb, gcd, isqrt, log

CHECKS = 0


def check(cond, msg="check failed"):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise AssertionError(msg)


# ---------------------------------------------------------------------------
# Generic utilities
# ---------------------------------------------------------------------------

def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for p in range(2, isqrt(n) + 1):
        if s[p]:
            s[p * p::p] = bytearray(len(range(p * p, n + 1, p)))
    return [i for i, f in enumerate(s) if f]


def spf_table(n):
    spf = array('i', [0]) * (n + 1)
    for p in reversed(primes_upto(isqrt(n))):
        cnt = len(range(p * p, n + 1, p))
        spf[p * p::p] = array('i', [p]) * cnt
    return spf


def factor_spf(n, spf):
    f = {}
    while n > 1:
        p = spf[n] or n
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        f[p] = e
    return f


_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)


def is_prime(n):
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
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


def pollard_brent(n):
    if n % 2 == 0:
        return 2
    rng = random.Random(n)
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


@lru_cache(maxsize=None)
def factorize_t(n):
    f = {}
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
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
    return tuple(sorted(f.items()))


def factorize(n):
    return dict(factorize_t(n))


def merge(f, g, k=1):
    h = dict(f)
    for p, e in g.items():
        h[p] = h.get(p, 0) + k * e
    return h


def mobius_small(n):
    f = factorize(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def divisors(n):
    ds = [1]
    for p, e in factorize(n).items():
        ds = [d * p ** i for d in ds for i in range(e + 1)]
    return sorted(ds)


@lru_cache(maxsize=None)
def cyclotomic_value(d, b):
    num, den = 1, 1
    for e in divisors(d):
        mu = mobius_small(d // e)
        if mu == 1:
            num *= b ** e - 1
        elif mu == -1:
            den *= b ** e - 1
    assert num % den == 0
    return num // den


def factor_bm1(b, m):
    """Factorisation of b^m - 1 through its cyclotomic factors."""
    f = {}
    for d in divisors(m):
        v = cyclotomic_value(d, b)
        if v > 1:
            f = merge(f, factorize(v))
    return f


def order_mod(b, fac):
    """Exact multiplicative order of b modulo prod q^e (fac = {q: e})."""
    total = 1
    for q, e in fac.items():
        mod = q ** e
        phi_fac = merge(factorize(q - 1) if q > 2 else {}, {q: e - 1} if e > 1 else {})
        t = 1
        for r, k in phi_fac.items():
            t *= r ** k
        for r in phi_fac:
            while t % r == 0 and pow(b, t // r, mod) == 1:
                t //= r
        total = total * t // gcd(total, t)
    return total


def exact_order_test(b, D, T, T_primes):
    if pow(b, T, D) != 1:
        return False
    return all(pow(b, T // q, D) != 1 for q in T_primes)


def ext_disc(xs):
    """Extreme (interval) discrepancy of points in [0,1)."""
    ys = sorted(xs)
    N = len(ys)
    mx, mn = -2.0, 2.0
    for i, x in enumerate(ys, 1):
        v = i / N - x
        if v > mx:
            mx = v
        if v < mn:
            mn = v
    return 1.0 / N + mx - mn


def kmul(A, B, n, w=64):
    """First n coefficients of A*B by Kronecker substitution (signed, |c| < 2^(w-1))."""
    W = w // 8
    H = 1 << (w - 1)
    pat = b'\x00' * (W - 1) + b'\x80'
    A = A[:n]
    B = B[:n]

    def pack(C):
        raw = b''.join((c + H).to_bytes(W, 'little') for c in C)
        return int.from_bytes(raw, 'little') - int.from_bytes(pat * len(C), 'little')

    Lp = len(A) + len(B) - 1
    Q = pack(A) * pack(B) + int.from_bytes(pat * Lp, 'little')
    raw = Q.to_bytes(Lp * W, 'little')
    return [int.from_bytes(raw[i * W:(i + 1) * W], 'little') - H for i in range(min(n, Lp))]


_POW_CACHE = {}


def bpow(b, e):
    key = (b, e)
    v = _POW_CACHE.get(key)
    if v is None:
        v = b ** e
        _POW_CACHE[key] = v
    return v


def eval_series(a, M, b):
    """sum_{m=0}^{M} a[m] b^(M-m), by divide and conquer."""
    def rec(lo, hi):
        if hi - lo <= 32:
            v = 0
            for m in range(lo, hi):
                v = v * b + a[m]
            return v
        mid = (lo + hi) // 2
        left = rec(lo, mid)
        if b == 2:
            left <<= (hi - mid)
        else:
            left *= bpow(b, hi - mid)
        return left + rec(mid, hi)
    return rec(0, M + 1)


def base_digits(x, b, length):
    """Base-b digits of 0 <= x < b^length, most significant first."""
    if length <= 48:
        out = [0] * length
        for i in range(length - 1, -1, -1):
            x, out[i] = divmod(x, b)
        return out
    half = length // 2
    hi, lo = divmod(x, bpow(b, half))
    return base_digits(hi, b, length - half) + base_digits(lo, b, half)


def binary_fraction_digits(a, M):
    """Binary digits d_1..d_M of frac(sum_{m<=M} a[m] 2^-m) as a str."""
    X = eval_series(a, M, 2)
    frac = X % (1 << M)
    return format(frac, '0%db' % M)


def orbit_points_from_bits(s, N, prec=53):
    pts = []
    scale = float(1 << prec)
    for n in range(N):
        pts.append(int(s[n:n + prec], 2) / scale)
    return pts


def pent_list(M):
    out = [(0, 1)]
    k = 1
    while True:
        p1 = k * (3 * k - 1) // 2
        if p1 > M:
            break
        s = -1 if k % 2 else 1
        out.append((p1, s))
        p2 = k * (3 * k + 1) // 2
        if p2 <= M:
            out.append((p2, s))
        k += 1
    return out


def cube_list(M):
    out = []
    k = 0
    while k * (k + 1) // 2 <= M:
        out.append((k * (k + 1) // 2, (-1) ** k * (2 * k + 1)))
        k += 1
    return out


def sparse_mul(P, Q, M):
    c = [0] * (M + 1)
    for p, s in P:
        if p > M:
            continue
        for q, t in Q:
            if p + q > M:
                continue
            c[p + q] += s * t
    return c


def phi_table(n):
    ph = list(range(n + 1))
    for p in range(2, n + 1):
        if ph[p] == p:
            for k in range(p, n + 1, p):
                ph[k] -= ph[k] // p
    return ph


T0 = time.time()

# ---------------------------------------------------------------------------
# Section S: Lemma S
# ---------------------------------------------------------------------------
print("== Section S: Lemma S for (a/d) E_b^2, odd prime denominators ==")
N_S, H_S = 50000, 50
NN = N_S + H_S + 200
spf = spf_table(12 * NN + 1)

a2 = sparse_mul(pent_list(NN), pent_list(NN), NN)

# (S1) support characterisation, Phase 20 Theorem 6(a), and the u v^2 split.
vpart = [0] * (NN + 1)
upart = [0] * (NN + 1)
for n in range(NN + 1):
    f = factor_spf(12 * n + 1, spf)
    ok = all(e % 2 == 0 for p, e in f.items() if p % 12 != 1)
    check(all(p >= 5 for p in f), "12n+1 has a prime factor 2 or 3")
    if ok:
        v = 1
        u = 1
        mag = 1
        for p, e in f.items():
            if p % 12 == 1:
                u *= p ** e
                mag *= e + 1
            else:
                v *= p ** (e // 2)
        check(abs(a2[n]) == mag, "|a_2(n)| != prod (e+1) at n=%d" % n)
        check(u * v * v == 12 * n + 1)
        vpart[n], upart[n] = v, u
    else:
        check(a2[n] == 0, "a_2(n) nonzero off the predicted support at n=%d" % n)
supp = [n for n in range(NN + 1) if a2[n] != 0]
print("  support characterisation and |a_2(n)| = prod(e+1) verified for 0 <= n <= %d (%d supported)" % (NN, len(supp)))

# (S2) exact pair counts, g^2 | h, CRT parametrisation and determinant.
mask = 0
for n in supp:
    if n >= 1:
        mask |= 1 << n
window_mask = ((1 << (N_S + 1)) - 1) ^ 1  # bits 1..N_S
pair_counts = []
for h in range(1, H_S + 1):
    pair_counts.append(bin(mask & (mask >> h) & window_mask).count('1'))
total_pairs = sum(pair_counts)
logN = log(N_S)
ratio = total_pairs * logN ** 1.5 / (H_S * N_S)
print("  sum_{h<=50} #{n<=50000: a2(n)a2(n+h)!=0} = %d;  normalised by HN/(log N)^1.5: %.4f" % (total_pairs, ratio))
phS = phi_table(H_S)
per_h = [pair_counts[h - 1] * logN ** 1.5 / (N_S * h / phS[h]) for h in range(1, H_S + 1)]
print("  per-shift ratio #{pairs}(log N)^1.5 / ((h/phi(h)) N): min %.3f, max %.3f (h=%d), mean %.3f"
      % (min(per_h), max(per_h), 1 + per_h.index(max(per_h)), sum(per_h) / H_S))

suppset = bytearray(NN + 1)
for n in supp:
    suppset[n] = 1


def crt(a1, m1, a2_, m2):
    g = gcd(m1, m2)
    if (a2_ - a1) % g:
        return None
    l = m1 // g * m2
    t = ((a2_ - a1) // g) * pow(m1 // g, -1, m2 // g) % (m2 // g)
    return (a1 + m1 * t) % l, l


triples = {}
g_gt1 = 0
pairs_list = []
supp_in = [n for n in supp if 1 <= n <= N_S]
for h in range(1, H_S + 1):
    for n in supp_in:
        if suppset[n + h]:
            pairs_list.append((n, h))
            v, w = vpart[n], vpart[n + h]
            g = gcd(v, w)
            check(h % (g * g) == 0, "g^2 does not divide h")
            if g > 1:
                g_gt1 += 1
            triples.setdefault((v, w, h), []).append(n)
det_checks = 0
for (v, w, h), ns in triples.items():
    g = gcd(v, w)
    i12v = pow(12, -1, v * v) if v > 1 else 0
    i12w = pow(12, -1, w * w) if w > 1 else 0
    alpha = (-i12v) % (v * v) if v > 1 else 0
    beta = (-(1 + 12 * h) * i12w) % (w * w) if w > 1 else 0
    sol = crt(alpha, v * v, beta, w * w)
    check(sol is not None, "CRT inconsistent although g^2 | h")
    n0, L = sol
    check(L == v * v * w * w // (g * g))
    check((12 * n0 + 1) % (v * v) == 0 and (12 * n0 + 12 * h + 1) % (w * w) == 0)
    B1 = (12 * n0 + 1) // (v * v)
    B2 = (12 * n0 + 12 * h + 1) // (w * w)
    A1 = 12 * w * w // (g * g)
    A2 = 12 * v * v // (g * g)
    check(A1 * B2 - A2 * B1 == 144 * h // (g * g), "determinant identity")
    det_checks += 1
    for n in ns:
        check((n - n0) % L == 0)
        m = (n - n0) // L
        check(upart[n] == A1 * m + B1 and upart[n + h] == A2 * m + B2)
print("  g^2 | h on all %d pairs (%d with g > 1); determinant 144h/g^2 and u = A1 m + B1, u' = A2 m + B2 on %d (v,v',h) classes"
      % (total_pairs, g_gt1, det_checks))

# (S3) local densities omega(p) for the sifted pairs of linear forms.
dens_checks = 0
P0_small = [p for p in primes_upto(220) if p >= 5 and p % 12 != 1]
for (v, w, h) in list(triples)[:60]:
    g = gcd(v, w)
    n0, L = crt((-pow(12, -1, v * v)) % (v * v) if v > 1 else 0, v * v,
                (-(1 + 12 * h) * pow(12, -1, w * w)) % (w * w) if w > 1 else 0, w * w)
    A1, A2 = 12 * w * w // (g * g), 12 * v * v // (g * g)
    B1, B2 = (12 * n0 + 1) // (v * v), (12 * n0 + 12 * h + 1) // (w * w)
    for p in P0_small:
        if (v * w) % p == 0:
            continue
        roots = sum(1 for m in range(p) if (A1 * m + B1) * (A2 * m + B2) % p == 0)
        check(roots == (1 if h % p == 0 else 2), "omega(p) mismatch")
        dens_checks += 1
print("  omega(p) = 2 (p not dividing h), 1 (p | h) verified in %d (class, prime) cases" % dens_checks)


# (S4) Selberg inequality on explicit instances.
def selberg_instance(A1, B1, A2, B2, X, primes, xi):
    P = 1
    for p in primes:
        P *= p
    omega = {}
    roots = {}
    for p in primes:
        rs = sorted({m for m in range(p) if (A1 * m + B1) * (A2 * m + B2) % p == 0})
        roots[p] = rs
        omega[p] = len(rs)
    sqf = [1]
    for p in primes:
        sqf += [d * p for d in sqf if d * p < xi]
    sqf = sorted(d for d in sqf if d < xi)

    def pf(d):
        return [p for p in primes if d % p == 0]

    def g_of(d):
        r = Fraction(1)
        for p in pf(d):
            r *= Fraction(omega[p], p - omega[p])
        return r

    def f_of(d):
        r = Fraction(1)
        for p in pf(d):
            r *= Fraction(omega[p], p)
        return r

    G = sum(g_of(d) for d in sqf)
    lam = {}
    for d in sqf:
        Gd = sum(g_of(k) for k in sqf if k < Fraction(xi, d) and gcd(k, d) == 1)
        mu = -1 if len(pf(d)) % 2 else 1
        lam[d] = mu * g_of(d) / f_of(d) * Gd / G
    check(lam[1] == 1, "lambda_1 = 1")
    for d in sqf:
        check(abs(lam[d]) <= 1, "|lambda_d| <= 1")

    def count_A(d):
        # number of m in [1, X] with d | F(m), via CRT residues
        res = [0]
        mod = 1
        for p in pf(d):
            new = []
            for r0 in res:
                for r1 in roots[p]:
                    s = crt(r0, mod, r1, p)
                    new.append(s[0])
            res = new
            mod *= p
        return sum((X - r) // mod + (1 if r >= 1 else 0) for r in res) if mod > 1 else X

    S = 0
    upper = Fraction(0)
    for m in range(1, X + 1):
        Fm = (A1 * m + B1) * (A2 * m + B2)
        gm = gcd(Fm, P)
        if gm == 1:
            S += 1
        t = sum(lam[d] for d in sqf if gm % d == 0)
        upper += t * t
    rem = Fraction(0)    # lambda-weighted remainder  sum |lambda lambda r|
    rem_u = Fraction(0)  # unweighted remainder of Lemma S.1  sum |r|
    for d1 in sqf:
        for d2 in sqf:
            e = d1 * d2 // gcd(d1, d2)
            rd = count_A(e) - Fraction(X) * f_of(e)
            rho_e = 1
            for p in pf(e):
                rho_e *= omega[p]
            check(abs(rd) <= rho_e, "|r_d| <= rho(d)")
            rem += abs(lam[d1] * lam[d2] * rd)
            rem_u += abs(rd)
    bound = Fraction(X) / G + rem
    check(S <= upper <= bound + Fraction(1, 10 ** 9), "Selberg inequality (weighted remainder)")
    check(bound <= Fraction(X) / G + rem_u, "weighted remainder <= unweighted remainder")
    return S, float(upper), float(Fraction(X) / G), float(rem), float(G), float(rem_u)


sel_rows = []
sieve_primes = [p for p in primes_upto(40) if p >= 5 and p % 12 != 1]
for (h, X) in ((6, 3000), (25, 3000), (35, 3000)):
    S, up, main, rem, G, rem_u = selberg_instance(12, 1, 12, 12 * h + 1, X, sieve_primes, 60)
    sel_rows.append((h, X, S, up, main, rem, rem_u))
    print("  Selberg instance h=%d, X=%d, primes %s, xi=60: S=%d <= sum(sum lambda)^2=%.1f <= X/G + R_w = %.1f + %.1f;"
          " unweighted remainder R = %.1f" % (h, X, sieve_primes, S, up, main, rem, rem_u))

# (S5) Rankin lower bound for G(xi):  G >= sum_{n<xi} kappa(n)/n >= Pi - xi^-delta Pi_delta.
z_r = 60
Pz = [p for p in primes_upto(z_r) if p >= 5 and p % 12 != 1]
h_r = 7 * 11
omega_r = {p: (1 if h_r % p == 0 else 2) for p in Pz}
delta = 1 / log(z_r)
Pi = 1.0
Pid = 1.0
for p in Pz:
    Pi *= (1 - 1 / p) ** (-omega_r[p])
    Pid *= (1 - p ** (delta - 1)) ** (-omega_r[p])
for xi in (10 ** 3, 10 ** 4, 10 ** 5):
    # G(xi)
    sq = [1]
    for p in Pz:
        sq += [d * p for d in sq if d * p < xi]
    Gxi = 0.0
    for d in sq:
        gv = 1.0
        for p in Pz:
            if d % p == 0:
                gv *= omega_r[p] / (p - omega_r[p])
        Gxi += gv
    # sum_{n < xi, rad n | P} kappa(n)/n
    sm = [(1, 1.0)]
    for p in Pz:
        new = []
        for n, kap in sm:
            k = 0
            pk = 1
            while n * pk < xi:
                ck = 1 if omega_r[p] == 1 else k + 1
                new.append((n * pk, kap * ck))
                k += 1
                pk *= p
        sm = new
    Ksum = sum(kap / n for n, kap in sm)
    lower = Pi - xi ** (-delta) * Pid
    check(Gxi >= Ksum - 1e-12 and Ksum >= lower - 1e-12, "Rankin chain")
    print("  z=60, xi=%d: G(xi)=%.4f >= sum kappa(n)/n=%.4f >= Pi - xi^-delta Pi_delta=%.4f (Pi=%.4f)"
          % (xi, Gxi, Ksum, lower, Pi))

# (S6) Mertens in progressions: B(z) = (3/4) log log z - sum_{p<=z, p=5,7,11 (12)} 1/p.
plist = primes_upto(12 * NN + 1)
checkpoints = [10 ** k for k in range(2, 6)] + [600000]
Bvals = []
for z in checkpoints:
    s = sum(1 / p for p in plist if p <= z and p >= 5 and p % 12 != 1)
    Bvals.append((z, 0.75 * log(log(z)) - s))
print("  B(z) = (3/4)loglog z - sum 1/p over p = 5,7,11 mod 12:", ", ".join("z=%d: %.4f" % t for t in Bvals))
mert = max(sum(log(p) / p for p in plist if p <= z) - log(z) for z in (10, 100, 1000, 10 ** 4, 10 ** 5, 600000))
check(mert < 2, "Mertens sum log p / p <= log x + 2 at checkpoints")

# (S7) constants C_5 and the singular-series average.
pr = primes_upto(200000)
zeta2 = math.pi ** 2 / 6
prod4 = 1.0
prod2 = 1.0
for p in pr:
    prod4 *= 1 + ((p / (p - 1)) ** 4 - 1) / p ** 2
    prod2 *= 1 + (2 * p - 1) / ((p - 1) ** 2 * p ** 2)
Sg = zeta2 * prod4
Sw = zeta2 * prod2
C5 = Sg * Sw ** 2
print("  sum_g (g/phi g)^4/g^2 ~ %.4f, sum_w (w/phi w)^2/w^2 ~ %.4f, C_5 ~ %.3f (Euler products truncated at 2e5)"
      % (Sg, Sw, C5))
HH = 10000
ph = phi_table(HH)
const_ss = 1.0
for p in primes_upto(10 ** 6):
    const_ss *= 1 + 1 / (p * (p - 1))
run = 0.0
for H in range(1, HH + 1):
    run += H / ph[H]
    check(run <= const_ss * H + 1e-9, "sum h/phi(h) <= 1.9436 H")
SS50 = sum(h / ph[h] for h in range(1, 51)) / 50
avg_prod_1p2p = 0.0
for h in range(1, 51):
    t = 1.0
    for p in factorize(h):
        t *= 1 + 2 / p
    avg_prod_1p2p += t
avg_prod_1p2p /= 50
print("  sum_{h<=H} h/phi(h) <= %.5f H for all H <= 10^4; at H=50 the average is %.4f; average of prod(1+2/p) is %.4f"
      % (const_ss, SS50, avg_prod_1p2p))

# (S8) the large-v tail: count n <= N with v(n) > V or v(n+h) > V.
for V in (5, 10, 20):
    tail = sum(1 for (n, h) in pairs_list if vpart[n] > V or vpart[n + h] > V)
    bound = H_S * (2 * N_S / V + math.sqrt(12 * N_S + 1) + math.sqrt(24 * N_S + 1))
    check(tail <= bound)
    print("  pairs with v > %d or v' > %d: %d (bound H(2N/V + sqrt(12N+1) + sqrt(24N+1)) = %.0f)" % (V, V, tail, bound))
print("  [Section S: %.1fs]" % (time.time() - T0))

# ---------------------------------------------------------------------------
# Section D3
# ---------------------------------------------------------------------------
T1 = time.time()
print("== Section D3: intermediate products P_b(M) ==")
NB = 4800
beta = [0] * (NB + 1)
beta[0] = 1
for n in range(1, NB + 1):
    beta[n] = beta[n - 1] if n % 2 else beta[n - 1] + beta[n // 2]
dp = [1] + [0] * 3000
s = 1
while s <= 3000:
    for i in range(s, 3001):
        dp[i] += dp[i - s]
    s *= 2
check(dp == beta[:3001], "binary partitions: recurrence vs product")
for n in range(1, 2001):
    check(beta[2 * n] == sum(beta[:n + 1]), "beta(2n) = sum_{j<=n} beta(j)")
for n in range(2, 4097):
    K = (n - 1).bit_length()
    check(beta[n] * 10000 <= 47685 * 2 ** (K * (K - 1) // 2), "elementary upper bound for beta")
for n in range(2, NB + 1):
    check(beta[n] % 2 == 0)
lb = [(n, log(beta[n]) / (log(n) ** 2 / (2 * log(2)))) for n in (2 ** 8, 2 ** 10, 2 ** 12)]
print("  binary partitions beta(n) verified (recurrence = product, beta(2n)=sum, bound 4.7685*2^(K(K-1)/2), even for n>=2)")
print("  log beta(n) / ((log n)^2 / (2 log 2)) :", ", ".join("n=%d: %.3f" % t for t in lb))

# exact finite Mahler identity: (1-1/b) sum_{n<=M} beta(n) b^-n = sum_{2k<=M} beta(k) b^-2k - beta(M) b^-(M+1)
for b in (2, 3, 10):
    for M in (50, 301, 1000):
        lhs = (b - 1) * sum(beta[n] * b ** (M - n) for n in range(M + 1))
        rhs = b * sum(beta[k] * b ** (M - 2 * k) for k in range(M // 2 + 1)) - beta[M]
        check(lhs == rhs, "finite Mahler identity")
print("  finite Mahler identity (b-1) sum beta(n) b^(M-n) = b sum beta(k) b^(M-2k) - beta(M): exact for b in {2,3,10}, M in {50,301,1000}")


def window_exact(coef, N, b, A=2):
    # least L with sum_{L<j<=J} coef(N-1+j) b^-j < N^-A  (J = available length; finite data)
    J = min(len(coef) - N, 800)
    suffix = [0] * (J + 1)
    acc_ = 0
    for j in range(J, 0, -1):
        acc_ += coef[N - 1 + j] * b ** (J - j)
        suffix[j - 1] = acc_
    lim = b ** J
    for L in range(J):
        if suffix[L] * N ** A < lim:
            return L
    return None


for N in (500, 1000, 4000):
    Lx = window_exact(beta, N, 2)
    est = log(beta[N], 2) + 2 * log(N, 2)
    print("  Mahler window b=2, N=%d: exact L=%d; log2 beta(N) + 2 log2 N = %.1f; (log2 N)^2/2 = %.1f"
          % (N, Lx, est, log(N, 2) ** 2 / 2))
    check(Lx is not None and abs(Lx - est) <= 6)

# Euler odd/distinct identities.
NE = 800
pdist = [1] + [0] * NE
for k in range(1, NE + 1):
    for i in range(NE, k - 1, -1):
        pdist[i] += pdist[i - k]
pp = [1] + [0] * NE
for k in range(1, NE + 1):
    for i in range(k, NE + 1):
        pp[i] += pp[i - k]
pp2 = [pp[i // 2] if i % 2 == 0 else 0 for i in range(NE + 1)]
prod_qp = [sum(pdist[j] * pp2[i - j] for j in range(i + 1)) for i in range(NE + 1)]
check(prod_qp == pp, "P(q) = Q(q) P(q^2)")
oddprod = [1] + [0] * NE
for k in range(1, NE + 1, 2):
    for i in range(NE, k - 1, -1):
        oddprod[i] -= oddprod[i - k]
sc = [0] * (NE + 1)  # self-conjugate partitions = partitions into distinct odd parts
sc[0] = 1
tmp = [1] + [0] * NE
for k in range(1, NE + 1, 2):
    for i in range(NE, k - 1, -1):
        tmp[i] += tmp[i - k]
sc = tmp
check(all(oddprod[n] == (-1) ** n * sc[n] for n in range(NE + 1)), "prod (1-q^odd) = sum (-1)^n sc(n) q^n")
conv = [sum(oddprod[j] * pdist[i - j] for j in range(i + 1)) for i in range(0, 300)]
check(conv[0] == 1 and all(c == 0 for c in conv[1:]), "prod(1+q^m)^{-1} = prod(1-q^odd)")
print("  Euler: P = Q(q) P(q^2) and prod(1+q^m)^{-1} = prod(1-q^(2k-1)) = sum (-1)^n sc(n) q^n verified to q^%d" % NE)
print("    sc(n) (no cancellation): sc(200)=%d, sc(800) has %d digits" % (sc[200], len(str(sc[800]))))

# Periods of R_K and the tracking table.
b = 2


def DK_fac(ms):
    f = {}
    for m in ms:
        f = merge(f, factor_bm1(b, m))
    return f


def DK_val(ms):
    v = 1
    for m in ms:
        v *= b ** m - 1
    return v


def is_chain(ms):
    return all(ms[i + 1] % ms[i] == 0 for i in range(len(ms) - 1))


schedules = [
    ("M = N (partition constant)", [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 10),
    ("squares k^2", [1, 4, 9, 16, 25, 36], 5),
    ("chain 2^k (Mahler, k>=1)", [2, 4, 8, 16, 32, 64, 128, 256, 512], 8),
    ("chain 3^k", [3, 9, 27, 81, 243, 729], 5),
    ("chain k!", [1, 2, 6, 24, 120, 720, 5040], 6),
    ("chain 2^(k^2)", [2, 16, 512, 65536], 3),
    ("pairwise coprime primes", [2, 3, 5, 7, 11, 13, 17], 6),
    ("admissible (A1)-(A2)", [2, 4, 48, 43200, None], 4),
]
table_rows = []
for name, ms, Kmax in schedules:
    for K in range(1, Kmax + 1):
        mK = ms[:K]
        nxt = ms[K] if K < len(ms) else None
        if is_chain(mK) and K >= 2:
            T = mK[-1] * DK_val(mK[:-1])
            Tprimes = set(factorize(mK[-1])) | set(DK_fac(mK[:-1]))
            check(exact_order_test(b, DK_val(mK), T, Tprimes), "chain period T_K = m_K D_{K-1} (%s, K=%d)" % (name, K))
            how = "m_K D_(K-1)"
        elif name.startswith("pairwise"):
            T = 1
            for m in mK:
                T *= m
            check(exact_order_test(b, DK_val(mK), T, set(mK)), "coprime period T_K = prod m_j")
            how = "prod m_j"
        else:
            T = order_mod(b, DK_fac(mK))
            how = "exact"
        lcmv = 1
        for m in mK:
            lcmv = lcmv * m // gcd(lcmv, m)
        check(T % lcmv == 0, "lcm(m_j) | T_K")
        check(T >= sum(mK) - 2, "T_K >= sum m_j - 2")
        if K >= 2:
            Tprev = order_mod(b, DK_fac(mK[:-1])) if not (is_chain(mK[:-1]) and K >= 3) else mK[-2] * DK_val(mK[:-2])
            if mK[-1] % Tprev == 0:
                check(T == mK[-1] * DK_val(mK[:-1]), "T_K = m_K D_{K-1} under T_{K-1} | m_K")
        if K in (Kmax, max(2, Kmax - 1)) or name.startswith("admissible"):
            ratio = (nxt / T) if nxt else float('nan')
            table_rows.append((name, K, mK[-1], nxt, T, how, ratio))
print("  period table (b=2): schedule | K | m_K | m_(K+1) | log2 T_K | formula | m_(K+1)/T_K")
for name, K, m, nxt, T, how, ratio in table_rows:
    print("    %-28s %2d %7d %9s %9.1f  %-12s %.3g" % (name, K, m, str(nxt), log(T, 2), how, ratio))

# Lemma D3.10: the digit-agreement clause needs b^(m_(K+1)) >= 64.  Without it the
# integer parts may differ: b=2, M={1,2,4,5,6,8,9}, K=1 gives 11 agreeing fractional digits.
Mx = [1, 2, 4, 5, 6, 8, 9]
Px = Fraction(1)
for m in Mx:
    Px *= Fraction(2 ** m, 2 ** m - 1)
R1 = Fraction(2, 1)
check(Px - R1 > 1, "integer parts differ in the K=1 example")
fx, fr = Px - math.floor(Px), R1 - math.floor(R1)
agree = 0
while agree < 60 and math.floor(fx * 2) == math.floor(fr * 2):
    fx, fr = fx * 2 - math.floor(fx * 2), fr * 2 - math.floor(fr * 2)
    agree += 1
check(agree == 11, "11 agreeing fractional digits in the K=1 example")
# with b^(m_(K+1)) >= 64 the bound A < m_(K+1) holds: check on prefixes of several schedules
for Ms in ([1, 2, 4, 5, 6, 8, 9, 13], [2, 3, 7, 12, 20], [3, 9, 27], [1, 2, 3, 6, 252]):
    Pfull = Fraction(1)
    for m in Ms:
        Pfull *= Fraction(2 ** m, 2 ** m - 1)
    for K in range(1, len(Ms)):
        if 2 ** Ms[K] < 64:
            continue
        RK = Fraction(1)
        for m in Ms[:K]:
            RK *= Fraction(2 ** m, 2 ** m - 1)
        if math.floor(Pfull) != math.floor(RK):
            # proof of Lemma D3.10: then not even the first fractional digit agrees
            check(math.floor((Pfull % 1) * 2) != math.floor((RK % 1) * 2), "first digit differs")
            continue
        fx, fr = Pfull - math.floor(Pfull), RK - math.floor(RK)
        agree = 0
        while agree <= Ms[K] + 5 and math.floor(fx * 2) == math.floor(fr * 2):
            fx, fr = fx * 2 - math.floor(fx * 2), fr * 2 - math.floor(fr * 2)
            agree += 1
        check(agree < Ms[K], "Lemma D3.10 digit bound under b^(m_(K+1)) >= 64")
print("  Lemma D3.10: K=1 counterexample without b^m_(K+1) >= 64 (11 agreeing digits) and the bound A < m_(K+1) under it")

# Proposition D3.9(c'): odd chains in bases b = 3 (mod 4): T_K = m_K D_(K-1) / 2^min(K-2, v_2(b+1)-1).
odd_rows = []
for bb in (3, 7, 11):
    v2 = ((bb + 1) & -(bb + 1)).bit_length() - 1
    for ms_ in ([3, 9, 27, 81], [1, 3, 15, 45]):
        for K in range(2, len(ms_) + 1):
            mK = ms_[:K]
            Dprev = 1
            fprev = {}
            for m in mK[:-1]:
                Dprev *= bb ** m - 1
                fprev = merge(fprev, factor_bm1(bb, m))
            DKv = Dprev * (bb ** mK[-1] - 1)
            drop = 2 ** min(K - 2, v2 - 1)
            T = mK[-1] * Dprev // drop
            Tpr = set(factorize(mK[-1])) | set(fprev) | {2}
            check(exact_order_test(bb, DKv, T, Tpr), "odd-chain period formula")
            odd_rows.append((bb, tuple(mK), drop))
print("  Prop. D3.9(c'): odd chains {3^k}, {1,3,15,45} in bases 3, 7, 11: T_K = m_K D_(K-1)/2^min(K-2, v_2(b+1)-1) verified (%d cases);"
      " e.g. b=3, M={3,9,27}: factor %d" % (len(odd_rows), [r for r in odd_rows if r[0] == 3 and r[1] == (3, 9, 27)][0][2]))

# Coprime law: R_K orbit = convolution of the orbit laws of c_j / Q_j  (b=2, M={2,3,5}).
msC = [2, 3, 5]
Qs = [2 ** m - 1 for m in msC]
DC = 1
for q in Qs:
    DC *= q
RC = Fraction(2 ** sum(msC), DC)
cs = []
for j, q in enumerate(Qs):
    other = DC // q
    cs.append((2 ** sum(msC) * pow(other, -1, q)) % q)
check((RC - sum(Fraction(c, q) for c, q in zip(cs, Qs))).denominator == 1, "partial fractions")
orbit = sorted(Fraction((2 ** (sum(msC) + n)) % DC, DC) for n in range(30))
conv_pts = []
for r0 in range(2):
    for r1 in range(3):
        for r2 in range(5):
            x = sum(Fraction(c * 2 ** r % q, q) for c, q, r in zip(cs, Qs, (r0, r1, r2)))
            conv_pts.append(x - math.floor(x))
check(orbit == sorted(conv_pts), "coprime CRT law = convolution of component orbit laws")
print("  coprime schedule {2,3,5}: full-period law of R_3 equals the convolution of the three component orbit laws (exact)")

# Subsequence Fourier vanishing: M = {1,2,3,6,252}, T_3=6 | m_4=6, T_4=126 | m_5 = 252.
msS = [1, 2, 3, 6, 252]
check(order_mod(2, DK_fac(msS[:3])) == 6)
D3v = DK_val(msS[:3])
D4v = DK_val(msS[:4])
check(order_mod(2, DK_fac(msS[:4])) == 6 * D3v == 126)
T5 = 252 * D4v
D5v = DK_val(msS)
check(exact_order_test(2, D5v, T5, set(factorize(252)) | set(DK_fac(msS[:4]))), "T_5 = m_5 D_4")
res = pow(2, sum(msS), D5v)
pts = []
sh = 53
for n in range(T5):
    pts.append((res << sh) // D5v / float(1 << sh))
    res <<= 1
    if res >= D5v:
        res -= D5v
check(res == pow(2, sum(msS), D5v), "period closes")
dS = ext_disc(pts)
check(dS <= 6 / D4v, "full-period discrepancy <= 6/D_4")
fc = {}
for hh in (1, 2, 3, D4v):
    acc = 0j
    w = 2j * math.pi * hh
    for x in pts:
        acc += cmath.exp(w * x)
    fc[hh] = abs(acc) / T5
check(all(fc[hh] < 1e-6 for hh in (1, 2, 3)), "Fourier vanishing off D_4 Z")
print("  M={1,2,3,6,252}: T_5 = 252*D_4 = %d; full-period D = %.5f <= 6/D_4 = %.5f; |C(1)|,|C(2)|,|C(3)| < 1e-6, |C(D_4)| = %.4f"
      % (T5, dS, 6 / D4v, fc[D4v]))

# Finite discrepancies and digit frequencies (base 2, N = 4000).
NF = 4000
MF = NF + 700
pfull = [0] * (MF + 1)
pfull[0] = 1
pl = pent_list(MF)[1:]
for n in range(1, MF + 1):
    sacc = 0
    for (pv, sg) in pl:
        if pv > n:
            break
        sacc -= sg * pfull[n - pv]
    pfull[n] = sacc
psq = [1] + [0] * MF
k = 1
while k * k <= MF:
    s2 = k * k
    for i in range(s2, MF + 1):
        psq[i] += psq[i - s2]
    k += 1
fin_rows = []
for nm, coef in (("P_2 (M=N)", pfull), ("P_2({k^2})", psq), ("P_2({2^k: k>=0})", beta[:MF + 1])):
    bits = binary_fraction_digits(coef, MF)
    pts = orbit_points_from_bits(bits, NF)
    D_vals = [ext_disc(pts[:n]) for n in (1000, 2000, 4000)]
    ones = bits[:NF].count('1') / NF
    pairs = [0] * 4
    for i in range(NF - 1):
        pairs[int(bits[i:i + 2], 2)] += 1
    dev2 = max(abs(c / (NF - 1) - 0.25) for c in pairs)
    chg = sum(1 for i in range(NF) if bits[i] != bits[i + 1]) / NF
    fin_rows.append((nm, D_vals, ones, dev2, chg))
    print("  %-18s D_1000=%.4f D_2000=%.4f D_4000=%.4f  freq(1)=%.4f  max dev 2-words=%.4f  change density=%.4f"
          % (nm, D_vals[0], D_vals[1], D_vals[2], ones, dev2, chg))
print("  [Section D3: %.1fs]" % (time.time() - T1))

# ---------------------------------------------------------------------------
# Section D4
# ---------------------------------------------------------------------------
T2 = time.time()
print("== Section D4: signed digits and the entropy-multiplicity wall ==")


def naf_weight(x):
    x = abs(x)
    return ((3 * x) ^ x).bit_count()


def naf_explicit(x):
    x = abs(x)
    c = 0
    while x:
        if x & 1:
            d = 2 - (x & 3)
            x -= d
            c += 1
        x >>= 1
    return c


for x in range(1, 1 << 16):
    check(naf_weight(x) == naf_explicit(x), "NAF weight formula")


@lru_cache(maxsize=None)
def min_signed_weight(x, b):
    x = abs(x)
    if x == 0:
        return 0
    if x == 1:
        return 1
    r = x % b
    if r == 0:
        return min_signed_weight(x // b, b)
    return 1 + min(min_signed_weight((x - r) // b, b), min_signed_weight((x - r + b) // b, b))


# NAF is a minimal signed binary representation: compare with the DP for b = 2.
for x in range(1, 1 << 12):
    check(min_signed_weight(x, 2) == naf_weight(x))

# counting lemma: #{0<|x|<=X : w(x) <= k} <= sum_{r<=k} C(E,r) (2b-2)^r, E = floor(log_b X) + k
for (bb, X) in ((2, 1 << 14), (3, 3 ** 9)):
    wts = [min_signed_weight(x, bb) for x in range(1, X + 1)]
    for kk in range(1, 6):
        cnt = 2 * sum(1 for w_ in wts if w_ <= kk)
        E = int(math.floor(log(X, bb) + 1e-12)) + kk
        bound = sum(comb(E, r) * (2 * bb - 2) ** r for r in range(kk + 1)) - 1
        check(cnt <= bound, "counting lemma")
print("  NAF weight = popcount(3x xor x) and NAF minimality checked; counting lemma exact for b=2 (X=2^14), b=3 (X=3^9), k<=5")

# exponent lemma: |x| >= b^(e1 - r + 1) for distinct exponents, digits in [-(b-1), b-1]
from itertools import combinations, product
for bb in (2, 3):
    digs = [d for d in range(-(bb - 1), bb) if d]
    for r in (1, 2, 3):
        for pos in combinations(range(11), r):
            e1 = max(pos)
            for ds in product(digs, repeat=r):
                x = sum(d * bb ** e for d, e in zip(ds, pos))
                check(abs(x) >= bb ** (e1 - r + 1), "exponent lemma")
print("  exponent lemma |x| >= b^(e1-r+1) checked exhaustively (b=2,3; r<=3; exponents<=10)")

# carry normalisation: weight after normalising <= sum |c_e|
rng = random.Random(22)
for bb in (2, 3, 10):
    for _ in range(3000):
        terms = {}
        for _ in range(rng.randint(1, 6)):
            e = rng.randint(0, 12)
            terms[e] = terms.get(e, 0) + rng.randint(-25, 25)
        x = sum(c * bb ** e for e, c in terms.items())
        check(min_signed_weight(x, bb) <= sum(abs(c) for c in terms.values()), "w^pm <= w_1")
print("  carry normalisation w^pm(x) <= sum |c_e| checked on 9000 random multisets (b=2,3,10)")

# Benchmark series, base 2.
N4 = 50000
M4 = N4 + 128
E1 = pent_list(M4)
E3s = cube_list(M4)
c2 = sparse_mul(E1, E1, M4)
c4 = sparse_mul(E3s, E1, M4)
c6 = sparse_mul(E3s, E3s, M4)
c8 = kmul(c4, c4, M4 + 1)
# cross-check E^8 = E^6 * E^2 on a prefix
c8b = sparse_mul([(i, c6[i]) for i in range(2001) if c6[i]], [(i, c2[i]) for i in range(2001) if c2[i]], 2000)
check(c8[:2001] == c8b, "E^8 two ways")
check(c2[:M4 + 1] == a2[:M4 + 1], "E^2 consistency")
r2 = [0] * (M4 + 1)
for x in range(0, isqrt(M4) + 1):
    for y in range(0, isqrt(M4 - x * x) + 1):
        r2[x * x + y * y] += (2 if x else 1) * (2 if y else 1)
dtheta = [n * r2[n] for n in range(M4 + 1)]
dE2 = [n * c2[n] for n in range(M4 + 1)]
Fseq = [0] + [(1 << m.bit_length()) - 1 for m in range(1, M4 + 1)]
series = [
    ("E_2^2", c2), ("E_2^4", c4), ("E_2^6", c6), ("E_2^8", c8),
    ("D(Theta_3^2)", dtheta), ("D(E_2^2)", dE2), ("F (Prop. D4.6)", Fseq),
]
print("  series      S(N)*sqrt(logN)/N  W_raw/N  W_NAF/N  mean NAF/bits  max mult  #{w<=3} vs mu*bound  change dens.")
ln = log(N4)
d4_rows = []
for nm, a in series:
    S = 0
    Wraw = 0
    Wnaf = 0
    ratio_acc = 0.0
    nbig = 0
    vals = {}
    small = 0
    maxabs = 1
    for n in range(1, N4 + 1):
        x = a[n]
        if x:
            S += 1
            bl = abs(x).bit_length()
            wn = naf_weight(x)
            Wraw += bl
            Wnaf += wn
            if bl >= 8:
                ratio_acc += wn / bl
                nbig += 1
            vals[x] = vals.get(x, 0) + 1
            if wn <= 3:
                small += 1
            if abs(x) > maxabs:
                maxabs = abs(x)
    mu = max(vals.values())
    E = int(math.floor(log(maxabs, 2))) + 3
    cnt_bound = sum(comb(E, r) * 2 ** r for r in range(4)) - 1
    check(small <= mu * cnt_bound, "entropy-multiplicity count")
    bits = binary_fraction_digits(a, M4)
    chg = sum(1 for i in range(N4) if bits[i] != bits[i + 1]) / N4
    d4_rows.append((nm, S, Wraw, Wnaf, mu, small, chg))
    print("  %-15s %8.3f %9.2f %8.2f %10.3f %9d %8d <= %-9d %.4f"
          % (nm, S * math.sqrt(ln) / N4, Wraw / N4, Wnaf / N4, ratio_acc / max(nbig, 1), mu, small, mu * cnt_bound, chg))

# multiplicity of n r_2(n) <= max_{n<=N} r_2(n)/4 ; of n a_2(n) <= 2 max |a_2| ... (<= 2 max tau)
vals = {}
for n in range(1, N4 + 1):
    if dtheta[n]:
        vals[dtheta[n]] = vals.get(dtheta[n], 0) + 1
check(max(vals.values()) <= max(r2[1:N4 + 1]) // 4, "multiplicity of n r_2(n)")
vals = {}
for n in range(1, N4 + 1):
    if dE2[n]:
        vals[dE2[n]] = vals.get(dE2[n], 0) + 1
check(max(vals.values()) <= 2 * max(abs(c2[n]) for n in range(1, N4 + 1)), "multiplicity of n a_2(n)")

# F: net displaced sequence telescopes to 1 + lacunary.
MFt = 4096
num = sum(Fseq[m] << (MFt - m) for m in range(1, MFt + 1))
Anet = [0] * (MFt + 1)
for m in range(1, MFt + 1):
    w_ = m.bit_length()
    Anet[m - w_] += 1
    Anet[m] -= 1
num2 = sum(Anet[t] << (MFt - t) for t in range(0, MFt + 1))
check(num == num2, "F: net displaced identity")
lac = {2 ** s - s - 1 for s in range(1, 14)}
check(all(Anet[t] == (1 if t == 0 else 0) + (1 if t in lac else 0) for t in range(0, MFt - 13)), "F: A_net = [t=0] + [t lacunary]")
print("  F: net displaced coefficients A_net(t) = [t=0] + [t = 2^s - s - 1] for t <= %d (cross-index cancellation)" % (MFt - 13))

# quadratic-width example: a(m) = 2^floor(m/2) - 1 + [m power of 2]
MQ = 3000
aq = [0] + [(1 << (m // 2)) - 1 + (1 if (m & (m - 1)) == 0 else 0) for m in range(1, MQ + 1)]
numq = sum(aq[m] << (2 * MQ - m) for m in range(1, MQ + 1))
Aq = [0] * (MQ + 1)
for m in range(1, MQ + 1):
    Aq[m - m // 2] += 1
    Aq[m] -= 1
    if (m & (m - 1)) == 0:
        Aq[m] += 1
numq2 = sum(Aq[t] << (2 * MQ - t) for t in range(0, MQ + 1))
check(numq == numq2, "quadratic example: net identity")
check(all(Aq[t] == 1 + (1 if (t & (t - 1)) == 0 else 0) for t in range(1, MQ // 2)), "A_net = 1 + [t power of 2]")
WU = sum(aq[m].bit_length() for m in range(1, MQ + 1) if (m & (m - 1)) != 0)
WU += sum(1 for m in range(1, MQ + 1) if (m & (m - 1)) == 0)  # u(2^s) = 1 (unit part of 2^floor(m/2))
print("  quadratic-width example: W_U(%d)/N^2 = %.4f, A_net(t) = 1 + [t = 2^s] (so F = 1/(b-1) + lacunary)" % (MQ, WU / MQ ** 2))
check(abs(WU / MQ ** 2 - 0.25) < 0.01)

# canonical nearest-integer representation (Theorem D4.9): b = 2 and b = 3.
bits = binary_fraction_digits(Fseq, M4)
Acan = [int(bits[n]) - int(bits[n - 1]) for n in range(1, N4)]  # A(n) = d_{n+1} - d_n
check(all(abs(x) <= 1 for x in Acan))
N3 = 20000
M3 = N3 + 80
X3 = eval_series(c4, M3, 3)
frac3 = X3 % bpow(3, M3)
d3 = base_digits(frac3, 3, M3)
P34 = 3 ** 34
val = 0
for j in range(34):
    val = val * 3 + d3[j]
rnd = []
for n in range(0, N3 + 1):
    rnd.append(1 if 2 * val >= P34 else 0)
    val = (val * 3 + d3[n + 34]) % P34 if n + 34 < M3 else (val * 3) % P34
Ab3 = [d3[n - 1] + rnd[n] - 3 * rnd[n - 1] for n in range(1, N3 + 1)]
check(all(abs(x) <= 1 for x in Ab3), "|A(n)| <= floor(b/2)")
nz3 = sum(1 for x in Ab3 if x) / N3
# reconstruct: I_0 + sum A(n) 3^-n = round(x) + ... check the telescoping on integers
fl = 0
for n in range(1, 200):
    fl = 3 * fl + d3[n - 1]
Ival = fl + rnd[199]
recon = 3 ** 199 * rnd[0] + sum(Ab3[n - 1] * 3 ** (199 - n) for n in range(1, 200))
check(recon == Ival, "nearest-integer telescoping")
print("  canonical representation: b=2 -> A(n) = d_(n+1) - d_n in {-1,0,1}; b=3, E_3^4: |A|<=1 = floor(b/2), nonzero density %.4f (N=%d)" % (nz3, N3))
print("  [Section D4: %.1fs]" % (time.time() - T2))

print("ALL CHECKS PASSED: %d checks in %.1fs" % (CHECKS, time.time() - T0))
sys.exit(0)
