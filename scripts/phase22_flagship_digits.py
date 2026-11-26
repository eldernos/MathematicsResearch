#!/usr/bin/env python3
"""Exact and certified checks for Phase 22, Track A, sub-tracks A3 and A4.

Notes: notes/phase22/flagship-digit-laws.md

A3.1  Nonnegative sparse series.  (1*chi)(n) >= 0 for every real nonprincipal character
      chi mod q <= 30; local values (1*chi)(p^e); certified digits of Theta_3(1/b) and
      D^j Theta_3(1/b) satisfy the explicit bound f_{0^L}(N) >= 1 - R(sqrt(N+R)+1)/N;
      measured f_{0^L} for binary theta values and real-character Lambert series.
A3.2  Signed quadratic-support series D^j E_b, D^j E_b^3, (1/3) D(E_b^3).  On certified
      digits, every position outside the explicit exceptional windows reads 0^L or
      (b-1)^L according to the sign of the next coefficient (L = 1, 2, 3); the exceptional
      count and the gap imbalance bound |f - 1/2|; planted coefficient windows reproduce
      the base-b expansion of the next coefficient; word counts (disjunctivity).
A3.3  Signed periodic Lambert series a_{r,M} = tau_{r,M} - tau_{M-r,M}.  Reduction to
      gcd(r,M) = 1; nonnegativity for r = 1 iff lambda(M) = 2 (explicit negative values
      constructed for every M <= 60 with lambda(M) > 2); the character identity; mass
      law sum a(n) = (pi/M) cot(pi r/M) X + O(sqrt X); sign proportions, oriented-tail
      proportions and certified binary digit frequencies; Wirsing constants for (8,3).
A3.4  Euler's square.  a_2(n) by exact convolution for n <= 2^20; the sign rule
      c(p) = +2 iff p = x^2 + 36 y^2 for every prime p = 1 (12) below 12*2^20 + 1; the
      full sign formula for n <= 2^16; no congruence description modulo the tested
      moduli; oriented-tail proportions in bases 2 and 3; certified binary digits.
A4    Rational scalings (a/d)E_b, (a/d)E_b^3.  Signed automaton limit word laws (exact
      rationals); strict interiority of nonzero atoms; certified digits agree with the
      automaton prediction off the exceptional windows; the odd-order antisymmetry
      u_{k+t} = -u_k and complement symmetry; the base-2 simple-normality catalogue.

Standard library only.  Run from the repository root:
    python -B scripts/phase22_flagship_digits.py
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction as Fr
from math import gcd, isqrt
from time import perf_counter

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

CHECKS = [0]
T0 = perf_counter()


def check(cond, msg):
    if not cond:
        raise SystemExit("FAIL: " + msg)
    CHECKS[0] += 1


def header(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def lcm(x, y):
    return x // gcd(x, y) * y


def order_mod(b, d):
    if d == 1:
        return 1
    x, t = b % d, 1
    while x != 1:
        x = x * b % d
        t += 1
    return t


def carmichael(M):
    lam = 1
    for x in range(1, M):
        if gcd(x, M) == 1:
            lam = lcm(lam, order_mod(x, M))
    return lam


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i:: i] = bytearray(len(range(i * i, n + 1, i)))
    return s


# ---------------------------------------------------------------- base-b digits

_POW = {}


def bpow(b, e):
    key = (b, e)
    v = _POW.get(key)
    if v is None:
        v = b ** e
        _POW[key] = v
    return v


def to_base(v, b, n):
    """The n base-b digits of 0 <= v < b^n, most significant first."""
    if b == 2:
        return [int(c) for c in format(v, "0%db" % n)]
    if b == 10:
        return [int(c) for c in str(v).zfill(n)]
    if n <= 256:
        out = [0] * n
        for i in range(n - 1, -1, -1):
            v, out[i] = divmod(v, b)
        return out
    h = n // 2
    q, r = divmod(v, bpow(b, h))
    return to_base(q, b, n - h) + to_base(r, b, h)


def certified_digits(terms, b, N, M, B):
    """Digits d_1..d_N of frac(z), z = sum c_m b^{-m}.

    terms: sorted (m, c) with m <= M (all terms up to M); B: integer bound for
    |sum_{m > M} c_m b^{M-m}|.  Raises if the window does not certify N digits."""
    Z = 0
    prev = 0
    for m, c in terms:
        if m > M:
            break
        if b == 2:
            Z = (Z << (m - prev)) + c
        else:
            Z = Z * bpow(b, m - prev) + c
        prev = m
    Z = (Z << (M - prev)) if b == 2 else Z * bpow(b, M - prev)
    sh = bpow(b, M - N)
    lo = (Z - B - 1) // sh
    hi = (Z + B) // sh
    check(lo == hi, "digit window certifies %d digits (b=%d)" % (N, b))
    return to_base(lo % bpow(b, N), b, N)


def tail_bound(terms, M, b):
    s = 0.0
    for m, c in terms:
        if m > M:
            if m - M > 2000:
                break
            s += abs(c) * float(b) ** (M - m)
    return int(s) + 2


def word_counts(dig, L, N):
    cnt = {}
    for n in range(N):
        w = tuple(dig[n:n + L])
        cnt[w] = cnt.get(w, 0) + 1
    return cnt


# ---------------------------------------------------------------- series coefficients

def pentagonal_terms(Mmax):
    """[(m, s)] for E(q) = sum s q^m, m <= Mmax, sorted."""
    out = [(0, 1)]
    k = 1
    while k * (3 * k - 1) // 2 <= Mmax:
        s = -1 if k % 2 else 1
        out.append((k * (3 * k - 1) // 2, s))
        if k * (3 * k + 1) // 2 <= Mmax:
            out.append((k * (3 * k + 1) // 2, s))
        k += 1
    out.sort()
    return out


def cube_terms(Mmax):
    out = []
    k = 0
    while k * (k + 1) // 2 <= Mmax:
        out.append((k * (k + 1) // 2, (-1) ** k * (2 * k + 1)))
        k += 1
    return out


def deriv(terms, j):
    return [(m, c * m ** j) for (m, c) in terms if c * m ** j != 0]


# ================================================================ A3.1

def real_characters(q):
    """All real characters mod q as dicts on residues (0 off units)."""
    units = [x for x in range(1, q) if gcd(x, q) == 1] if q > 1 else [0]
    sq = {x * x % q for x in units}
    basis = []
    span = set(sq)
    for g in units:
        if g not in span:
            basis.append(g)
            span = span | {h * g % q for h in span}
    chars = []
    for mask in range(1 << len(basis)):
        chi = {x: 1 for x in sq}
        for i, g in enumerate(basis):
            s = -1 if (mask >> i) & 1 else 1
            chi.update({h * g % q: chi[h] * s for h in list(chi)})
        check(len(chi) == len(units), "real character mod %d well defined" % q)
        for x in units:
            for y in units:
                check(chi[x * y % q] == chi[x] * chi[y], "multiplicativity mod %d" % q)
        chars.append(chi)
    return chars


def section_a31():
    header("A3.1  Nonnegative sparse series")
    X = 3000
    nchar = 0
    for q in range(3, 31):
        for chi in real_characters(q):
            if all(v == 1 for v in chi.values()):
                continue
            nchar += 1
            c = [0] * (X + 1)
            for d in range(1, X + 1):
                v = chi.get(d % q, 0)
                if v:
                    for m in range(d, X + 1, d):
                        c[m] += v
            check(min(c[1:]) >= 0, "(1*chi)(n) >= 0, q=%d" % q)
            for p in (2, 3, 5, 7, 11, 13):
                for e in range(1, 7):
                    if p ** e <= X:
                        v = chi.get(p % q, 0)
                        pred = 1 if v == 0 else (e + 1 if v == 1 else (1 + (-1) ** e) // 2)
                        check(c[p ** e] == pred, "(1*chi)(p^e) local value")
    print("real nonprincipal characters mod q <= 30: %d; (1*chi)(n) >= 0 for n <= %d" % (nchar, X))

    # Theta_3 and its derivatives: explicit all-N bound on certified digits
    print("\nTheta_3(1/b) = 1 + 2 sum b^{-t^2} and D^j Theta_3: explicit bound "
          "f_{0^L}(N) >= 1 - R(sqrt(N+R)+1)/N")
    for b, N in ((2, 1 << 15), (3, 1 << 13), (10, 1 << 12)):
        for j in (0, 1, 2):
            M = N + 4 * isqrt(N) + 300
            terms = [(0, 1 if j == 0 else 0)] + [(t * t, 2 * t ** (2 * j)) for t in range(1, isqrt(M + 3000) + 2)]
            terms = [x for x in terms if x[1] != 0] or [(0, 0)]
            dig = certified_digits(terms, b, N, M, tail_bound(terms, M, b))
            Cbj = sum((1 + k) ** j * float(b) ** (-k) for k in range(1, 400))
            row = []
            for L in (1, 2, 3):
                for Nc in (N // 4, N // 2, N - 8):
                    R = L + math.ceil(math.log(2 * Cbj * (Nc + 64) ** j, b)) + 1
                    check(R <= 64, "R <= 64, so (Nc + 64)^j dominates (N + R)^j")
                    z = sum(1 for n in range(Nc) if all(x == 0 for x in dig[n:n + L]))
                    check(z / Nc >= 1 - R * (math.sqrt(Nc + R) + 1) / Nc, "Theta bound")
                row.append("%.5f" % (z / Nc))
            print("  b=%2d j=%d N=%6d  f_{0^L}, L=1,2,3: %s" % (b, j, N - 8, " ".join(row)))

    # binary theta values and real-character Lambert series: measured f_{0^L}
    print("\nlog-sparse nonnegative series (rate (log log N)/sqrt(log N)): measured f_{0^L}")
    X = 1 << 15
    forms = {"m^2+n^2": (1, 0, 1), "m^2+mn+n^2": (1, 1, 1), "m^2+5n^2": (1, 0, 5)}
    for name, (A, B0, C) in forms.items():
        r = [0] * (X + 600)
        lim = isqrt(4 * (X + 600)) + 2
        for m in range(-lim, lim + 1):
            for n in range(-lim, lim + 1):
                v = A * m * m + B0 * m * n + C * n * n
                if v < len(r):
                    r[v] += 1
        terms = [(m, r[m]) for m in range(len(r)) if r[m]]
        for b in (2, 3):
            N = X - 64
            dig = certified_digits(terms, b, N, X, tail_bound(terms, X, b) + 10 ** 6)
            fs = []
            for L in (1, 2, 3):
                fs.append(sum(1 for n in range(N - 4) if all(x == 0 for x in dig[n:n + L])) / (N - 4))
            print("  Theta_{%s}(1/%d): f_{0^L} = %s" % (name, b, " ".join("%.4f" % f for f in fs)))
    for q, name in ((4, "chi_-4"), (3, "chi_-3"), (5, "chi_5"), (8, "chi_8")):
        chis = [c for c in real_characters(q) if not all(v == 1 for v in c.values())]
        chi = chis[0] if q != 8 else [c for c in chis if c[3] == -1 and c[7] == 1][0]
        a = [0] * (X + 1)
        for d in range(1, X + 1):
            v = chi.get(d % q, 0)
            if v:
                for m in range(d, X + 1, d):
                    a[m] += v
        terms = [(m, a[m]) for m in range(1, X + 1) if a[m]]
        N = X - 128
        dig = certified_digits(terms, 2, N, X, 10 ** 6)
        f1 = sum(1 for n in range(N) if dig[n] == 0) / N
        print("  L_{%s}(2): f_0 = %.4f (support density %.4f)" % (name, f1, len(terms) / X))
        check(f1 > 0.6, "nonnegative Lambert series: zero-digit majority")


# ================================================================ A3.2

def mechanism(terms, b, N, dig, Ls=(1, 2, 3), label=""):
    """Check: off exceptional windows the word is 0^L / (b-1)^L by the next sign."""
    supp = [(m, c) for (m, c) in terms if m >= 1 and c != 0]
    # remainder bound after each support point
    rem = [0.0] * len(supp)
    acc = 0.0
    for i in range(len(supp) - 1, -1, -1):
        rem[i] = acc
        if i > 0:
            g = supp[i][0] - supp[i - 1][0]
            acc = (abs(supp[i][1]) + acc) * float(b) ** (-g) if g < 1500 else 0.0
    out = {}
    for L in Ls:
        nxt = 0
        exc = 0
        cnt0 = cntb = 0
        posw = negw = 0
        for n in range(N):
            while supp[nxt][0] <= n:
                nxt += 1
            m, c = supp[nxt]
            r = m - n
            ell = L + math.ceil(math.log(abs(c) + 0.5, b)) + 1
            w = dig[n:n + L]
            if c > 0:
                posw += 1
            else:
                negw += 1
            if r >= ell and rem[nxt] <= 0.5:
                pred = 0 if c > 0 else b - 1
                check(all(x == pred for x in w), "%s: oriented word at n=%d" % (label, n))
            else:
                exc += 1
            if all(x == 0 for x in w):
                cnt0 += 1
            elif all(x == b - 1 for x in w):
                cntb += 1
        imb = abs(posw - negw)
        check(abs(cnt0 - N / 2) <= exc + imb / 2, "%s: |Z_0 - N/2| bound" % label)
        check(abs(cntb - N / 2) <= exc + imb / 2, "%s: |Z_b - N/2| bound" % label)
        out[L] = (cnt0 / N, cntb / N, exc / N, imb / N)
    return out


def planted(terms, b, N, dig, label):
    """Digits ending at a support point m read (c_m + eps) mod b^ell, eps = floor(tau_m)."""
    supp = [(m, c) for (m, c) in terms if m >= 1 and c != 0]
    ok = 0
    for i in range(3, len(supp) - 2):
        m, c = supp[i]
        if m > N:
            break
        ell = len(to_base_any(abs(c), b))
        gap = m - supp[i - 1][0]
        g2 = supp[i + 1][0] - m
        if ell > gap or g2 < ell + 3 + math.ceil(math.log(abs(supp[i + 1][1]) + 1, b)):
            continue
        eps = 0 if supp[i + 1][1] > 0 else -1
        val = (c + eps) % bpow(b, ell)
        check(dig[m - ell:m] == to_base(val, b, ell), "%s: planted window at m=%d" % (label, m))
        ok += 1
    return ok


def to_base_any(v, b):
    out = []
    while v:
        v, r = divmod(v, b)
        out.append(r)
    return out[::-1] or [0]


def section_a32():
    header("A3.2  D^j E_b, D^j E_b^3, (1/3) D(E_b^3): oriented signs and planted windows")
    fams = []
    for b, N in ((2, 1 << 16), (3, 1 << 14), (10, 1 << 13)):
        M = N + 4 * isqrt(N) + 300
        pent = pentagonal_terms(M + 5000)
        cube = cube_terms(M + 5000)
        for j in (0, 1, 2):
            fams.append(("D^%dE" % j, b, N, M, deriv(pent, j) if j else pent))
        for j in (0, 1, 2):
            fams.append(("D^%dE^3" % j, b, N, M, deriv(cube, j) if j else cube))
        third = [(m, c * m // 3) for (m, c) in cube if m > 0]
        fams.append(("E^2*DE", b, N, M, third))
    words_seen = {}
    for name, b, N, M, terms in fams:
        dig = certified_digits(terms, b, N, M, tail_bound(terms, M, b))
        res = mechanism(terms, b, N - 4, dig, label="%s b=%d" % (name, b))
        pl = planted(terms, b, N - 4, dig, "%s b=%d" % (name, b)) if name != "D^0E" else 0
        print("  %-8s b=%2d N=%6d  L=1: f_0=%.4f f_(b-1)=%.4f  L=3: %.4f %.4f  exc(L=3)=%.4f  planted=%d"
              % (name, b, N - 4, res[1][0], res[1][1], res[3][0], res[3][1], res[3][2], pl))
        if b == 2:
            for L in (8, 10):
                words_seen[(name, L)] = len(word_counts(dig, L, N - 12))
    print("\n  distinct binary words in the first 2^16 digits (of 256 / 1024):")
    for name in ("D^0E", "D^1E", "D^2E", "D^0E^3", "D^1E^3", "E^2*DE"):
        print("    %-8s L=8: %4d   L=10: %4d" % (name, words_seen[(name, 8)], words_seen[(name, 10)]))
    check(words_seen[("D^0E", 8)] < 120, "E_2 misses many 8-words")
    check(words_seen[("D^1E", 8)] > words_seen[("D^0E", 8)], "DE_2 richer than E_2")

    # planting lemma: leading digits of (P_K^-)^j, K even, contain any prescribed word
    hits = 0
    for j in (1, 2):
        for L in range(1, 7):
            for w in range(1 << L):
                target = (1 << L) | w            # binary digits "1w"
                K = 2
                while True:
                    v = (K * (3 * K - 1) // 2) ** j
                    s = v.bit_length() - (L + 1)
                    if s >= 0 and (v >> s) == target:
                        break
                    K += 2
                    check(K < 10 ** 7, "planting search terminates")
                hits += 1
    print("\n  planting: for j=1,2 and every binary word w of length <= 6, some even K has "
          "(P_K^-)^j beginning with 1w (%d searches)" % hits)


# ================================================================ A3.3

def lambert_anti(M, r, X):
    a = [0] * (X + 1)
    for d in range(1, X + 1):
        rr = d % M
        if rr == r:
            v = 1
        elif rr == M - r:
            v = -1
        else:
            continue
        for m in range(d, X + 1, d):
            a[m] += v
    return a


def divisor_anti(n, M, r):
    s = 0
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            for e in {d, n // d}:
                if e % M == r:
                    s += 1
                elif e % M == M - r:
                    s -= 1
    return s


def anti_from_primes(ps, M, r):
    """a_{r,M}(p_1...p_s) for distinct primes, via the divisor-residue distribution."""
    dist = [0] * M
    dist[1 % M] = 1
    for p in ps:
        new = dist[:]
        for x in range(M):
            if dist[x]:
                new[x * p % M] += dist[x]
        dist = new
    return dist[r % M] - dist[(M - r) % M]


def oriented_rho(a, X, b, Ncut):
    supp = [n for n in range(1, X + 1) if a[n]]
    V = {}
    tau = 0.0
    for i in range(len(supp) - 1, -1, -1):
        m = supp[i]
        V[m] = a[m] + tau
        if i:
            g = m - supp[i - 1]
            tau = V[m] * float(b) ** (-g) if g < 1500 else 0.0
    pos = 0
    prev = 0
    for m in supp:
        g = min(m, Ncut) - prev
        if V[m] > 0:
            pos += g
        if m >= Ncut:
            break
        prev = m
    return pos / Ncut, supp


def section_a33():
    header("A3.3  Signed periodic Lambert series a_{r,M} = tau_{r,M} - tau_{M-r,M}")
    X = 1 << 16
    # nonnegativity criterion for r = 1 and explicit negative values
    P = primes_upto(200000)
    def prime_in(cls, M, avoid):
        p = M + cls
        while True:
            if p < len(P) and P[p] and p not in avoid and p % M == cls:
                return p
            p += M
    crit = []
    for M in range(3, 61):
        lam = carmichael(M)
        if lam == 2:
            a = lambert_anti(M, 1, 4000)
            check(min(a[1:]) >= 0, "a_{1,%d} >= 0 (lambda=2)" % M)
            crit.append((M, "nonneg"))
            continue
        units = [x for x in range(2, M - 1) if gcd(x, M) == 1]
        # Case A: u of order 2t (t >= 2) with u^t = -1
        n = None
        for u in units:
            h = order_mod(u, M)
            if h >= 4 and h % 2 == 0 and pow(u, h // 2, M) == M - 1:
                t = h // 2
                ps = []
                for _ in range(t + 1):
                    ps.append(prime_in(u, M, set(ps)))
                n = math.prod(ps)
                pred = 1 - (t + 1)
                case = "A"
                break
        if n is None:
            u = next(x for x in units if order_mod(x, M) >= 3)
            h = order_mod(u, M)
            v = (M - 1) * pow(u, -2, M) % M
            ps = [prime_in(u, M, set())]
            ps.append(prime_in(u, M, set(ps)))
            ps.append(prime_in(u, M, set(ps)))
            q = prime_in(v, M, set(ps))
            n = q * math.prod(ps)
            pred = 1 + (1 if h == 3 else 0) - 3
            case = "B"
        val = anti_from_primes(ps if case == "A" else ps + [q], M, 1)
        check(val == pred and val < 0, "explicit negative a_{1,%d}" % M)
        if n < 10 ** 8:
            check(divisor_anti(n, M, 1) == val, "divisor sum cross-check")
        crit.append((M, case))
    print("r = 1: a_{1,M}(n) >= 0 for all n exactly when lambda(M) = 2 (M | 24);")
    print("  checked M = 3..60: nonneg for", [M for M, c in crit if c == "nonneg"])
    print("  explicit negative values: case A for %d moduli, case B for %s"
          % (sum(1 for M, c in crit if c == "A"), [M for M, c in crit if c == "B"]))

    # character identities for real-type moduli
    a83 = lambert_anti(8, 3, 4000)
    def onestar(chi, q, n):
        return sum(chi.get(d % q, 0) for d in range(1, n + 1) if n % d == 0)
    chim4 = {1: 1, 3: -1}
    chim8 = {1: 1, 3: 1, 5: -1, 7: -1}
    chim4_8 = {1: 1, 3: -1, 5: 1, 7: -1}
    for n in range(1, 1500):
        check(2 * a83[n] == onestar(chim8, 8, n) - onestar(chim4_8, 8, n), "a_{3,8} identity")
    a125 = lambert_anti(12, 5, 2000)
    c4 = {1: 1, 5: 1, 7: -1, 11: -1}
    c3 = {1: 1, 5: -1, 7: 1, 11: -1}
    for n in range(1, 1500):
        check(2 * a125[n] == onestar(c4, 12, n) - onestar(c3, 12, n), "a_{5,12} identity")
    # complex case M = 5: a_{r,5} = Re / Im of (1*chi)(n), chi(2) = i
    chi5 = {1: 1, 2: 1j, 4: -1, 3: -1j}
    for n in range(1, 1500):
        z = sum(chi5.get(d % 5, 0) for d in range(1, n + 1) if n % d == 0)
        check(abs(divisor_anti(n, 5, 1) - z.real) < 1e-9 and abs(divisor_anti(n, 5, 2) - z.imag) < 1e-9,
              "M=5 character identity")
    print("identities: 2a_{3,8} = 1*chi_-8 - 1*chi_-4, 2a_{5,12} = 1*chi_-4' - 1*chi_-3',"
          " a_{1,5} = Re(1*chi), a_{2,5} = Im(1*chi), n < 1500")

    npairs = sum(1 for M in range(3, 13) for r in range(1, (M + 1) // 2) if 2 * r != M)
    check(npairs == 30, "30 pairs (M, r)")
    print("\n%d pairs (M, r), 3 <= M <= 12, 1 <= r < M/2:" % npairs)
    print(" M  r  g  type        supp/X  min  1st neg  neg/supp  unw+   rho+_2  f_0(cert)  mass/X  (pi/M)cot")
    for M in range(3, 13):
        for r in range(1, (M + 1) // 2):
            if 2 * r == M:
                continue
            a = lambert_anti(M, r, X)
            g = gcd(M, r)
            Mp, rp = M // g, r // g
            # reduction a_{r,M}(n) = a_{r',M'}(n/g)
            ared = lambert_anti(Mp, rp, X // g)
            for n in range(1, X + 1):
                check(a[n] == (ared[n // g] if n % g == 0 else 0), "gcd reduction")
            lamp = carmichael(Mp)
            typ = "nonneg" if (rp == 1 and lamp == 2) else ("r'=1 signed" if rp == 1 else
                                                          ("real signed" if lamp == 2 else "r'!=+-1"))
            supp = [n for n in range(1, X + 1) if a[n]]
            neg = [n for n in supp if a[n] < 0]
            if typ == "nonneg":
                check(not neg, "nonneg type")
            else:
                check(bool(neg) and any(a[n] > 0 for n in supp), "both signs")
            unw = sum(1 for n in supp if a[n] > 0) / len(supp)
            Nc = X - 400
            rho, _ = oriented_rho(a, X, 2, Nc)
            terms = [(n, a[n]) for n in supp]
            dig = certified_digits(terms, 2, Nc, X - 1, 4 * isqrt(X) + 8)
            f0 = sum(1 for x in dig if x == 0) / Nc
            mass = sum(a[1:])
            pred = math.pi / M / math.tan(math.pi * r / M)
            check(abs(mass - pred * X) <= 3 * math.sqrt(X) + 3, "mass law")
            print("%2d %2d %2d  %-11s %.4f %4d  %7s  %.4f   %.4f  %.4f  %.4f     %.4f  %.4f"
                  % (M, r, g, typ, len(supp) / X, min(a[1:]), neg[0] if neg else "-",
                     len(neg) / len(supp), unw, rho, f0, mass / X, pred))

    # Wirsing constants for the real-type cases (8,3) and (12,5)
    PP = primes_upto(2 * 10 ** 5)
    def wirsing_K(chi, q, Lval):
        prod = 1.0
        for p in range(2, 2 * 10 ** 5):
            if PP[p]:
                v = chi.get(p % q, 0) if gcd(p, q) == 1 else 0
                if v == -1:
                    prod *= 1 / (1 - 1 / p ** 2)
                elif v == 0:
                    prod *= 1 / (1 - 1 / p)
        return math.sqrt(Lval * prod / math.pi)
    K4 = wirsing_K({1: 1, 3: -1}, 4, math.pi / 4)
    K8 = wirsing_K({1: 1, 3: 1, 5: -1, 7: -1}, 8, math.pi / (2 * math.sqrt(2)))
    check(abs(K4 - 0.7642236535892206) < 1e-5, "Landau-Ramanujan constant")
    K4p = wirsing_K(c4, 12, math.pi / 3)
    K3p = wirsing_K(c3, 12, math.pi / (2 * math.sqrt(3)))
    print("\nWirsing constants: K_-4 = %.7f (Landau-Ramanujan), K_-8 = %.7f; "
          "unweighted sign limit for (8,3): K_-8/(K_-4+K_-8) = %.5f" % (K4, K8, K8 / (K4 + K8)))
    print("  for (12,5): K_-4'/(K_-4'+K_-3') = %.5f  (K_-4' = %.5f, K_-3' = %.5f)"
          % (K4p / (K4p + K3p), K4p, K3p))
    return K4, K8


# ================================================================ A3.4

def section_a34():
    header("A3.4  Euler's square E_b^2 = sum a_2(n) b^{-n}")
    N = 1 << 20
    pent = pentagonal_terms(N)
    a = [0] * (N + 1)
    for (p, s) in pent:
        for (q, t) in pent:
            if p + q > N:
                break
            a[p + q] += s * t
    check(a[:8] == [1, -2, -1, 2, 1, 2, -2, 0], "first coefficients of E^2")
    Mx = 12 * N + 1
    PR = primes_upto(Mx)
    nprime = 0
    plus = 0
    plist = []
    for p in range(13, Mx + 1, 12):
        if not PR[p]:
            continue
        c = 2
        while True:
            r = pow(c, (p - 1) // 4, p)
            if r * r % p == p - 1:
                break
            c += 1
        x, y = p, r
        lim = isqrt(p)
        while y > lim:
            x, y = y, x % y
        u = y
        v = isqrt(p - u * u)
        check(u * u + v * v == p, "Cornacchia")
        even = u if u % 2 == 0 else v
        pred = 2 if even % 3 == 0 else -2
        check(a[(p - 1) // 12] == pred, "sign rule c(p) at p=%d" % p)
        nprime += 1
        plus += pred > 0
        plist.append((p, pred > 0))
    print("sign rule c(p) = +2 iff p = x^2+36y^2 (even part divisible by 3), else -2:")
    print("  all %d primes p = 1 (12), p <= %d; proportion of +2: %.5f" % (nprime, Mx, plus / nprime))

    # full sign formula for n <= 2^16 via smallest prime factors
    X = 1 << 16
    lim = 12 * X + 2
    spf = list(range(lim))
    for i in range(2, isqrt(lim) + 1):
        if spf[i] == i:
            for k in range(i * i, lim, i):
                if spf[k] == k:
                    spf[k] = i
    def eps_p(p):
        return 1 if a[(p - 1) // 12] > 0 else -1
    for n in range(1, X + 1):
        m = 12 * n + 1
        fac = {}
        while m > 1:
            p = spf[m]
            fac[p] = fac.get(p, 0) + 1
            m //= p
        val = 1
        for p, e in fac.items():
            if p % 12 == 1:
                val *= (e + 1) * eps_p(p) ** e
            elif e % 2:
                val = 0
                break
            else:
                val *= (-(1 if p % 4 == 1 else -1)) ** (e // 2)
        check(val == a[n], "multiplicative formula for a_2(%d)" % n)
    print("  a_2(n) = c(12n+1), c(p^e) = (e+1)eps_p^e (p = 1 (12)), c(p^2e) = (-chi_-4(p))^e: n <= %d" % X)

    # no congruence description modulo tested moduli
    for Q in (24, 48, 72, 144, 288, 432, 720, 1440, 5040, 10080):
        seen = {}
        mixed = 0
        for p, sg in plist:
            seen.setdefault(p % Q, set()).add(sg)
        mixed = sum(1 for v in seen.values() if len(v) == 2)
        check(mixed == len(seen), "every class mod %d carries both signs" % Q)
    print("  every residue class p = 1 (12) mod Q carries primes of both signs, "
          "Q in {24,...,10080}")

    # oriented tails, sign proportions
    supp = [m for m in range(1, N + 1) if a[m]]
    print("\n  N        base  rho+ (oriented)  gap-weighted sgn a  unweighted +  carry flips")
    rows = {}
    for b in (2, 3):
        V = {}
        tau = 0.0
        for i in range(len(supp) - 1, -1, -1):
            m = supp[i]
            V[m] = a[m] + tau
            if i:
                g = m - supp[i - 1]
                tau = V[m] * float(b) ** (-g) if g < 1500 else 0.0
        for Nc in (1 << 14, 1 << 16, 1 << 18, N - 4000):
            pos = posa = 0
            prev = 0
            cnt = flips = npos = 0
            for m in supp:
                g = min(m, Nc) - prev
                if V[m] > 0:
                    pos += g
                if a[m] > 0:
                    posa += g
                if m >= Nc:
                    break
                cnt += 1
                npos += a[m] > 0
                flips += (V[m] > 0) != (a[m] > 0)
                prev = m
            rows[(b, Nc)] = pos / Nc
            print("  %7d   %d    %.5f          %.5f             %.5f       %.4f"
                  % (Nc, b, pos / Nc, posa / Nc, npos / cnt, flips / cnt))
            check(0.45 < pos / Nc < 0.55, "rho+ near 1/2 at accessible scale")
    # certified binary digits vs rho+
    Ncert = 1 << 18
    terms = [(m, a[m]) for m in range(0, Ncert + 2000) if a[m]]
    dig = certified_digits(terms, 2, Ncert, Ncert + 1500, 8 * isqrt(24 * (Ncert + 1600)) + 8)
    f0 = sum(1 for x in dig if x == 0) / Ncert
    print("\n  certified binary digits of E_2^2: f_0(2^18) = %.5f   (rho+ = %.5f)" % (f0, rows[(2, 1 << 18)]))
    isolated = sum(1 for i in range(1, len(supp) - 1)
                   if supp[i] - supp[i - 1] >= 8 and supp[i + 1] - supp[i] >= 8 and supp[i] < N - 10)
    print("  support density at 2^20: %.4f; support points isolated by 8 on both sides: %.4f"
          % (len(supp) / N, isolated / len(supp)))


# ================================================================ A4

def word_of(c, d, b, L):
    out = []
    x = c
    for _ in range(L):
        x *= b
        out.append(x // d)
        x %= d
    return tuple(out)


def euler_runs(b, d):
    """One period of runs: (weight, start residue u, sign of next insertion)."""
    t = order_mod(b, d)
    Lp = lcm(2, t)
    u = 1 % d
    start = (0, u)
    runs = []
    k = 0
    while True:
        k += 1
        um = (pow(b, 2 * k - 1, d) * u + (-1) ** k) % d
        up = (pow(b, k, d) * um + (-1) ** k) % d
        runs.append((k, um, up))
        u = up
        if (k % Lp, u) == start:
            break
    P = len(runs)
    out = []
    for (k, um, up) in runs:
        out.append((Fr(1, 3 * P), um, (-1) ** k))
        out.append((Fr(2, 3 * P), up, (-1) ** (k + 1)))
    return out, P, runs


def cube_runs(b, d):
    t = order_mod(b, d)
    L3 = lcm(lcm(t, 2), d)
    v = 1 % d
    start = (0, v)
    runs = []
    k = 0
    bk = 1
    while True:
        k += 1
        bk = bk * b % d
        v = (bk * v + (-1) ** k * (2 * k + 1)) % d
        runs.append((k, v))
        if (k % L3, v) == start:
            break
    P = len(runs)
    return [(Fr(1, P), v, (-1) ** (k + 1)) for (k, v) in runs], P, runs


def limit_words(runs, a, b, d, L):
    """Exact limit frequencies of all length-L words (integer arithmetic, then Fractions)."""
    sa = 1 if a > 0 else -1
    den = 1
    for (wt, u, ns) in runs:
        den = lcm(den, wt.denominator)
    agg = {}
    for (wt, u, ns) in runs:
        key = (u, ns if u == 0 else 0)
        agg[key] = agg.get(key, 0) + wt.numerator * (den // wt.denominator)
    t = order_mod(b, d)
    f = {}
    wcache = {}
    for (u, ns), wt in agg.items():
        orb = [u]
        x = u * b % d
        while x != u:
            orb.append(x)
            x = x * b % d
        share = wt * (t // len(orb))
        for x in orb:
            c = a * x % d
            if c == 0:
                w = (0,) * L if ns * sa > 0 else (b - 1,) * L
            else:
                w = wcache.get(c)
                if w is None:
                    w = wcache[c] = word_of(c, d, b, L)
            f[w] = f.get(w, 0) + share
    return {w: Fr(v, den * t) for w, v in f.items()}


def section_a4():
    header("A4  Rational scalings (a/d)E_b and (a/d)E_b^3: signed automaton word laws")
    # strict interiority of nonzero atoms
    for b in range(2, 11):
        for d in range(2, 60):
            if gcd(b, d) != 1:
                continue
            for c in range(1, d):
                for L in range(1, 7):
                    num = c * b ** L
                    check(num % d != 0, "atom c/d not on a b-adic boundary")
                    k = num // d
                    check(k * d < num < (k + 1) * d, "strict interior")
                    check(min(num - k * d, (k + 1) * d - num) >= 1, "distance >= 1/(d b^L)")
    print("strict interiority: every c/d (0<c<d, gcd(d,b)=1) lies at distance >= 1/(d b^L) "
          "from the b-adic grid, b<=10, d<60, L<=6")

    print("\nexact limit digit laws f_c (L = 1):")
    print("  series  b  d   a   P     law (digit: frequency)                         simply normal")
    table = [(2, 3), (2, 5), (2, 7), (2, 9), (2, 23), (3, 2), (3, 4), (3, 5), (3, 7), (3, 8),
             (5, 2), (10, 3), (10, 7)]
    nlaws = 0
    for kind in ("E", "E^3"):
        for (b, d) in table:
            runs, P, _ = euler_runs(b, d) if kind == "E" else cube_runs(b, d)
            for a in (1, -1):
                f = limit_words(runs, a, b, d, 1)
                nlaws += 1
                check(sum(f.values()) == 1, "mass 1")
                law = " ".join("%d:%s" % (w[0], f[w]) for w in sorted(f))
                sn = all(f.get((c,), 0) == Fr(1, b) for c in range(b))
                print("  %-4s   %2d %2d %3d %4d   %-46s %s" % (kind, b, d, a, P, law, "yes" if sn else "no"))
    f = limit_words(euler_runs(2, 3)[0], 1, 2, 3, 1)
    check(f[(0,)] == Fr(7, 12), "(1/3)E_2: f_0 = 7/12")
    f = limit_words(euler_runs(3, 2)[0], 1, 3, 2, 1)
    check((f[(0,)], f[(1,)], f[(2,)]) == (Fr(1, 6), Fr(2, 3), Fr(1, 6)), "(1/2)E_3 law")
    f = limit_words(cube_runs(3, 2)[0], 1, 3, 2, 1)
    check((f.get((0,), 0), f.get((1,), 0), f.get((2,), 0)) == (Fr(1, 2), Fr(1, 2), 0), "(1/2)E_3^3 law")
    print("  %d pairs (b,d), a = +-1, both series: %d exact laws" % (len(table), nlaws))
    check(len(table) == 13 and nlaws == 52, "law count")

    # zero-atom splits (w_0^+, w_0^-) of the worked cases
    def zero_split(runs, a):
        wp = sum(wt for (wt, u, ns) in runs if u == 0 and ns * a > 0)
        wm = sum(wt for (wt, u, ns) in runs if u == 0 and ns * a < 0)
        return wp, wm
    split_cases = [("E", 2, 3, (Fr(1, 6), 0)), ("E", 2, 7, (Fr(1, 18), Fr(1, 18))),
                   ("E^3", 2, 7, (Fr(1, 14), Fr(1, 14))), ("E", 2, 23, (Fr(1, 22), Fr(1, 22))),
                   ("E", 3, 2, (Fr(1, 6), Fr(1, 6))), ("E^3", 3, 2, (Fr(1, 2), 0)),
                   ("E", 3, 4, (Fr(1, 6), 0)), ("E", 10, 3, (Fr(1, 6), Fr(1, 6))),
                   ("E", 2, 13, (Fr(1, 36), Fr(1, 18))), ("E^3", 2, 35, (Fr(1, 140), Fr(1, 70)))]
    print("\nzero-atom splits (w_0^+, w_0^-), a = 1 (a = -1 swaps them):")
    for kind, b, d, want in split_cases:
        runs = euler_runs(b, d)[0] if kind == "E" else cube_runs(b, d)[0]
        got = zero_split(runs, 1)
        check(got == want, "zero split %s b=%d d=%d" % (kind, b, d))
        check(zero_split(runs, -1) == (got[1], got[0]), "a -> -a swaps the zero split")
        print("  (1/%d)%s_%d: w_0^+ = %s, w_0^- = %s" % (d, "E" if kind == "E" else "E^3", b, got[0], got[1]))
    f2 = limit_words(euler_runs(2, 7)[0], 1, 2, 7, 2)
    check((f2[(0, 0)], f2[(0, 1)]) == (Fr(11, 54), Fr(8, 27)), "(1/7)E_2 length-2 law")
    f2 = limit_words(cube_runs(2, 7)[0], 1, 2, 7, 2)
    check((f2[(0, 0)], f2[(0, 1)]) == (Fr(3, 14), Fr(2, 7)), "(1/7)E_2^3 length-2 law")
    f2 = limit_words(euler_runs(2, 23)[0], 1, 2, 23, 2)
    check((f2[(0, 0)], f2[(0, 1)]) == (Fr(61, 242), Fr(30, 121)), "(1/23)E_2 length-2 law")

    # certified digits vs automaton prediction
    print("\ncertified digits vs signed-automaton prediction (N = 2^16 for b=2, 2^14 otherwise):")
    print("  series  b  d   a   L  max|f_emp - f_lim|  exceptional/N  mismatches off windows")
    cases = [("E", 2, 3, 1), ("E", 2, 7, 1), ("E", 2, 7, 3), ("E", 2, 5, -2), ("E", 3, 2, 1),
             ("E", 3, 4, 1), ("E", 10, 3, 1), ("E^3", 2, 3, 1), ("E^3", 2, 7, 1), ("E^3", 3, 2, 1),
             ("E^3", 3, 2, -1), ("E^3", 3, 4, 5)]
    for kind, b, d, a in cases:
        N = 1 << 16 if b == 2 else 1 << 14
        M = N + 4 * isqrt(N) + 300
        base = pentagonal_terms(M + 5000) if kind == "E" else cube_terms(M + 5000)
        terms = [(m, a * c) for (m, c) in base]
        # digits of (a/d) z: certify floor(b^M a z / d)
        Z = 0
        prev = 0
        for m, c in terms:
            if m > M:
                break
            Z = (Z << (m - prev)) + c if b == 2 else Z * bpow(b, m - prev) + c
            prev = m
        Z = (Z << (M - prev)) if b == 2 else Z * bpow(b, M - prev)
        B = tail_bound(terms, M, b)
        sh = bpow(b, M - N) * d
        lo, hi = (Z - B - 1) // sh, (Z + B) // sh
        check(lo == hi, "certified digits of (a/d)z")
        dig = to_base(lo % bpow(b, N), b, N)
        supp = [(m, c) for (m, c) in base if c != 0]
        runs = euler_runs(b, d)[0] if kind == "E" else cube_runs(b, d)[0]
        # head residues I_n mod d and index of the next insertion, computed once
        coef = {m: c for (m, c) in supp}
        H = [0] * N
        NX = [0] * N
        h = 0
        j = 0
        for n in range(N):
            h = (h * b + coef.get(n, 0)) % d
            H[n] = h
            while supp[j][0] <= n:
                j += 1
            NX[n] = j
        for L in (1, 2, 3):
            lim = limit_words(runs, a, b, d, L)
            Ne = N - L
            exc = 0
            emp = {}
            zero = (0,) * L
            top = (b - 1,) * L
            wcache = {}
            for n in range(Ne):
                j = NX[n]
                m, c = supp[j]
                w = tuple(dig[n:n + L])
                emp[w] = emp.get(w, 0) + 1
                ell = L + math.ceil(math.log(abs(a) * (abs(c) + 0.5), b)) + 2
                if m - n >= ell and j >= 4:
                    at = a * H[n] % d
                    if at:
                        pred = wcache.get(at)
                        if pred is None:
                            pred = wcache[at] = word_of(at, d, b, L)
                    else:
                        pred = zero if a * c > 0 else top
                    if w != pred:
                        check(False, "automaton word prediction %s b=%d d=%d a=%d n=%d" % (kind, b, d, a, n))
                    CHECKS[0] += 1
                else:
                    exc += 1
            dev = max(abs(emp.get(w, 0) / Ne - float(lim.get(w, 0))) for w in set(emp) | set(lim))
            bound = (exc + 6 * (order_mod(b, d) + 2) * len([1 for (m, c) in supp if m < N]) + 40 * d * d) / Ne
            check(dev <= bound, "empirical law within explicit bound")
            if L in (1, 3):
                print("  %-4s   %2d %2d %3d   %d  %.5f            %.4f         0"
                      % (kind, b, d, a, L, dev, exc / Ne))

    # odd-order antisymmetry and complement symmetry
    nodd = 0
    for b in (2, 3, 4, 5, 7, 10):
        for d in range(2, 80):
            if gcd(b, d) != 1:
                continue
            t = order_mod(b, d)
            if t % 2 == 0:
                continue
            _, P, rr = euler_runs(b, d)
            seq = {k: (um, up) for (k, um, up) in rr}
            for k in range(1, P + 1):
                kk = (k + t - 1) % P + 1
                check(seq[kk][0] == (-seq[k][0]) % d and seq[kk][1] == (-seq[k][1]) % d,
                      "u_{k+t} = -u_k (b=%d d=%d)" % (b, d))
            for L in (1, 2, 3):
                for a in (1, 2, -1):
                    if gcd(a, d) != 1:
                        continue
                    f = limit_words(euler_runs(b, d)[0], a, b, d, L)
                    for w, v in f.items():
                        cw = tuple(b - 1 - x for x in w)
                        check(f.get(cw, 0) == v, "complement symmetry")
            if d % 2 == 1:
                T = lcm(t, d)
                _, P3, r3 = cube_runs(b, d)
                vs = {k: v for (k, v) in r3}
                for k in range(1, P3 + 1):
                    kk = (k + T - 1) % P3 + 1
                    check(vs[kk] == (-vs[k]) % d, "v_{k+T} = -v_k")
            nodd += 1
    print("\nodd order t = ord_d(b): u_{k+t} = -u_k, v_{k+lcm(t,d)} = -v_k (d odd), and complement "
          "symmetry of the limit word laws verified for %d pairs (b,d)" % nodd)

    # base-2 catalogue
    agree = 0
    sn_list = []
    uneven = 0
    for kind, dmax in (("E", 64), ("E^3", 46)):
        for d in range(3, dmax, 2):
            runs = euler_runs(2, d)[0] if kind == "E" else cube_runs(2, d)[0]
            t = order_mod(2, d)
            if t % 2 == 0:
                wp = sum(wt for (wt, u, ns) in runs if u == 0 and ns > 0)
                wm = sum(wt for (wt, u, ns) in runs if u == 0 and ns < 0)
                check(wp != wm, "even order: unbalanced zero split (%s d=%d)" % (kind, d))
                uneven += 1
            for a0 in range(1, d):
                if gcd(a0, d) != 1:
                    continue
                for a in (a0, -a0):
                    f = limit_words(runs, a, 2, d, 1)
                    sn = f.get((0,), 0) == Fr(1, 2)
                    check(sn == (t % 2 == 1), "base 2: simply normal iff ord_d(2) odd (%s d=%d a=%d)" % (kind, d, a))
                    agree += 1
                    if sn:
                        f2 = limit_words(runs, a, 2, d, 2)
                        check(any(v != Fr(1, 4) for v in f2.values()) or len(f2) < 4, "never 2-normal")
                        sn_list.append((kind, d))
    print("base 2 catalogue: (a/d)E_2 (d<64) and (a/d)E_2^3 (d<46), all a: simply normal iff "
          "ord_d(2) odd (%d laws); none is 2-normal" % agree)
    snE = sorted({d for k, d in sn_list if k == "E"})
    snE3 = sorted({d for k, d in sn_list if k == "E^3"})
    check(snE == [7, 23, 31, 47, 49] and snE3 == [7, 23, 31], "simply normal denominator lists")
    print("  simply normal denominators: E_2 %s, E_2^3 %s" % (snE, snE3))
    print("  even-order denominators with w_0^+ != w_0^- (a = 1): %d of %d" % (uneven, uneven))
    # b >= 3: search
    found = 0
    tested = 0
    for b in (3, 4, 5, 6, 7, 10):
        for d in range(2, 41):
            if gcd(b, d) != 1:
                continue
            runs = euler_runs(b, d)[0]
            for a0 in range(1, d):
                if gcd(a0, d) != 1:
                    continue
                for a in (a0, -a0):
                    f = limit_words(runs, a, b, d, 1)
                    tested += 1
                    if all(f.get((c,), 0) == Fr(1, b) for c in range(b)):
                        found += 1
    print("b in {3,4,5,6,7,10}, d <= 40: %d laws of (a/d)E_b tested, %d simply normal" % (tested, found))
    # L-normality bound
    for b in (2, 3):
        for d in range(2, 40):
            if gcd(b, d) != 1:
                continue
            f = limit_words(euler_runs(b, d)[0], 1, b, d, 3)
            check(len([v for v in f.values() if v > 0]) <= d + 1, "positive words <= d + 1")
    print("number of length-3 words with positive limit frequency <= d + 1 (b = 2, 3; d < 40)")


def main():
    section_a31()
    section_a32()
    section_a33()
    section_a34()
    section_a4()
    print()
    print("All %d checks passed in %.1f s." % (CHECKS[0], perf_counter() - T0))


if __name__ == "__main__":
    main()
