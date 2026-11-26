#!/usr/bin/env python3
"""Phase 21, Tracks B1-B4 and E1-E3: exact and finite checks.

Companion to notes/phase21/character-q-digamma.md (B1-B4) and
notes/phase21/classical-barriers.md (E1-E3).

Standard library only.  Exits 0 when every assertion holds.

What is exact here:
  * cyclotomic identities (character orthogonality, local vanishing, the
    mod 2^k coefficient identities) are checked in Z[zeta_L] by reduction
    modulo the cyclotomic polynomial;
  * divisor-sum supports, the support containments and the complementary
    support cover of E1 are exact integer computations up to the stated N;
  * the q-digamma and logarithm identities are checked to at least 50
    decimal digits with decimal arithmetic at 150 digits (the rational
    Lambert sums are exact Fractions with a rigorous tail bound);
  * discrepancies come from certified base-b expansions (an integer
    enclosure of b^K x); every reported D_N is within 1e-9 of the true value.

What is only finite data: support ratios against (log N)^(-1/h), mass ratios,
finite discrepancies.  These illustrate the theorems; they prove nothing
asymptotic, and the notes say so.
"""

from __future__ import annotations

import math
import random
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import product
from math import gcd

CHECKS = 0


def check(cond: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", msg)
        sys.exit(1)


def header(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Elementary arithmetic
# ---------------------------------------------------------------------------


def factor(n: int) -> dict[int, int]:
    f: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def divisors_of(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def euler_phi(n: int) -> int:
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r


def carmichael(q: int) -> int:
    L = 1
    for p, a in factor(q).items():
        if p == 2:
            lam = 1 if a == 1 else (2 if a == 2 else 2 ** (a - 2))
        else:
            lam = p ** (a - 1) * (p - 1)
        L = lcm(L, lam)
    return L


def spf_sieve(N: int) -> list[int]:
    spf = list(range(N + 1))
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def primes_upto(N: int) -> list[int]:
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i:: i] = bytearray(len(range(i * i, N + 1, i)))
    return [i for i in range(N + 1) if s[i]]


def is_squarefree_spf(n: int, spf: list[int]) -> bool:
    while n > 1:
        p = spf[n]
        n //= p
        if n % p == 0:
            return False
    return True


def one_star_periodic(wt: list[int], M: int, N: int) -> list[int]:
    """(1*w)(n) for n <= N, w periodic mod M with values wt[m % M]."""
    a = [0] * (N + 1)
    for r in range(M):
        v = wt[r]
        if v == 0:
            continue
        start = r if r > 0 else M
        for d in range(start, N + 1, M):
            for n in range(d, N + 1, d):
                a[n] += v
    return a


def tau_list(N: int) -> list[int]:
    t = [0] * (N + 1)
    for d in range(1, N + 1):
        for n in range(d, N + 1, d):
            t[n] += 1
    return t


# ---------------------------------------------------------------------------
# Cyclotomic arithmetic: elements of Z[mu_L] as length-L histograms
# ---------------------------------------------------------------------------

_PHI: dict[int, list[int]] = {}


def poly_divexact(num: list[int], den: list[int]) -> list[int]:
    num = num[:]
    dn = len(den) - 1
    assert den[-1] == 1
    out = [0] * (len(num) - dn)
    for i in range(len(num) - 1, dn - 1, -1):
        c = num[i]
        out[i - dn] = c
        if c:
            for j in range(dn + 1):
                num[i - dn + j] -= c * den[j]
    assert all(v == 0 for v in num[:dn])
    return out


def cyclotomic(L: int) -> list[int]:
    if L not in _PHI:
        num = [-1] + [0] * (L - 1) + [1]
        for d in divisors_of(L):
            if d < L:
                num = poly_divexact(num, cyclotomic(d))
        _PHI[L] = num
    return _PHI[L]


def cyc_reduce(v: list[int], L: int) -> list[int]:
    """Reduce sum v[j] x^j (deg < L) modulo Phi_L; result has deg < phi(L)."""
    phi = cyclotomic(L)
    dg = len(phi) - 1
    r = list(v)
    for i in range(len(r) - 1, dg - 1, -1):
        c = r[i]
        if c:
            for j in range(dg + 1):
                r[i - dg + j] -= c * phi[j]
    return r[:dg]


def cyc_is_zero(v: list[int], L: int) -> bool:
    return all(c == 0 for c in cyc_reduce(v, L))


def cyc_is_rational(v: list[int], L: int, value: int) -> bool:
    w = list(v)
    w[0] -= value
    return cyc_is_zero(w, L)


# ---------------------------------------------------------------------------
# Dirichlet characters modulo q (values as exponents of zeta_L, L = lambda(q))
# ---------------------------------------------------------------------------


def primitive_root(p: int, a: int) -> int:
    pa = p ** a
    ph = pa - pa // p
    fs = factor(ph)
    for g in range(2, pa):
        if gcd(g, p) == 1 and all(pow(g, ph // r, pa) != 1 for r in fs):
            return g
    raise ValueError("no primitive root")


class CharGroup:
    def __init__(self, q: int):
        self.q = q
        gens = []
        for p, a in sorted(factor(q).items()):
            pa = p ** a
            if p == 2:
                if a == 1:
                    continue
                gens.append((pa, pa - 1, 2))
                if a >= 3:
                    gens.append((pa, 5, 2 ** (a - 2)))
            else:
                gens.append((pa, primitive_root(p, a), pa - pa // p))
        self.gens = gens
        self.orders = [o for (_, _, o) in gens]
        L = 1
        for o in self.orders:
            L = lcm(L, o)
        self.L = L
        self.phi = euler_phi(q)
        dlog: dict[int, tuple[int, ...]] = {}
        for vec in product(*[range(o) for o in self.orders]):
            res: dict[int, int] = {}
            for (pa, g, _), e in zip(gens, vec):
                res[pa] = res.get(pa, 1) * pow(g, e, pa) % pa
            x, Mod = 0, 1
            for pa, r in res.items():
                t = (r - x) * pow(Mod, -1, pa) % pa
                x += Mod * t
                Mod *= pa
            if q // Mod == 2 and x % 2 == 0:
                x += Mod
            dlog[x % q] = vec
        assert len(dlog) == self.phi
        self.dlog = dlog
        self.chars = list(product(*[range(o) for o in self.orders]))

    def value(self, t, m: int):
        v = self.dlog.get(m % self.q)
        if v is None:
            return None
        s = 0
        for ti, ei, oi in zip(t, v, self.orders):
            s += ti * ei * (self.L // oi)
        return s % self.L

    def order(self, t) -> int:
        o = 1
        for ti, oi in zip(t, self.orders):
            o = lcm(o, oi // gcd(ti, oi))
        return o

    def is_principal(self, t) -> bool:
        return all(ti == 0 for ti in t)

    def is_odd(self, t) -> bool:
        if self.q <= 2:
            return False
        return self.value(t, self.q - 1) == self.L // 2 and self.L % 2 == 0

    def power(self, t, j: int):
        return tuple((ti * j) % oi for ti, oi in zip(t, self.orders))

    def conductor(self, t) -> int:
        for c in divisors_of(self.q):
            if all(self.value(t, m) == 0 for m in range(1, self.q)
                   if gcd(m, self.q) == 1 and (m - 1) % c == 0):
                return c
        return self.q


def char_value_order(G: CharGroup, t, m: int) -> int:
    """Order of chi(m) as a root of unity (0 if chi(m) = 0)."""
    v = G.value(t, m)
    if v is None:
        return 0
    return G.L // gcd(v, G.L)


def support_by_criterion(G: CharGroup, t, N: int, primes: list[int]) -> bytearray:
    """Indicator of c_chi(n) != 0 for n <= N via Lemma 1 (local vanishing)."""
    sup = bytearray([1]) * (N + 1)
    sup[0] = 0
    for p in primes:
        if G.q % p == 0:
            continue
        d = char_value_order(G, t, p)
        if d < 2:
            continue
        e = d - 1
        while True:
            pe = p ** e
            if pe > N:
                break
            for n in range(pe, N + 1, pe):
                if (n // pe) % p:
                    sup[n] = 0
            e += d
    return sup


def c_chi_exact(G: CharGroup, t, n: int, divs: list[int]) -> list[int]:
    v = [0] * G.L
    for d in divs:
        x = G.value(t, d)
        if x is not None:
            v[x] += 1
    return v


# ---------------------------------------------------------------------------
# Certified base-b expansions and extreme discrepancy
# ---------------------------------------------------------------------------


class Num:
    """Real x known through an integer S and bound T with |b^K x - S| <= T."""

    def __init__(self, b: int, K: int, S: int, T: int):
        self.b, self.K, self.S, self.T = b, K, S, T

    def __add__(self, o: "Num") -> "Num":
        assert self.b == o.b and self.K == o.K
        return Num(self.b, self.K, self.S + o.S, self.T + o.T)

    def __sub__(self, o: "Num") -> "Num":
        assert self.b == o.b and self.K == o.K
        return Num(self.b, self.K, self.S - o.S, self.T + o.T)

    def scale(self, c: int) -> "Num":
        return Num(self.b, self.K, self.S * c, self.T * abs(c))

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
    S = 0
    for n in range(1, K + 1):
        S = S * b + coeff(n)
    T = tailC * (K + 2)
    return Num(b, K, S, T)


def disc(points: list[float]) -> float:
    ys = sorted(points)
    M = len(ys)
    hi = lo = 0.0
    for i, y in enumerate(ys, 1):
        hi = max(hi, i / M - y)
        lo = min(lo, (i - 1) / M - y)
    return hi - lo


def disc_N(x: Num, N: int) -> float:
    return disc(x.points(N))


def lambert_num(b: int, K: int, a: list[int], tailC: int) -> Num:
    return from_coeffs(b, K, lambda n: a[n], tailC)


# ---------------------------------------------------------------------------
# Decimal helpers (50-digit checks at 150-digit working precision)
# ---------------------------------------------------------------------------

getcontext().prec = 150
D = Decimal


def dec(fr: Fraction) -> Decimal:
    return D(fr.numerator) / D(fr.denominator)


def A_exact(b: int, M: int, r: int, K: int) -> Fraction:
    """sum_{1 <= m <= K, m = r mod M} 1/(b^m - 1), exact."""
    s = Fraction(0)
    m = r % M
    if m == 0:
        m = M
    while m <= K:
        s += Fraction(1, b ** m - 1)
        m += M
    return s


def psi_q_def(q: Decimal, lnq: Decimal, x: Decimal, terms: int) -> Decimal:
    qx = (x * lnq).exp()
    s, t = D(0), qx
    for _ in range(terms):
        s += t / (1 - t)
        t *= q
    return -(1 - q).ln() + lnq * s


def psi_q_lambert(q: Decimal, lnq: Decimal, x: Decimal, terms: int) -> Decimal:
    s = D(0)
    qj = q
    for j in range(1, terms + 1):
        s += (j * x * lnq).exp() / (1 - qj)
        qj *= q
    return -(1 - q).ln() + lnq * s


def log_gamma_q_var(q: Decimal, lnq: Decimal, x: Decimal, terms: int) -> Decimal:
    """x-dependent part of log Gamma_q(x) = (1-x)log(1-q) - sum log(1-q^{n+x})."""
    t = (x * lnq).exp()
    s = D(0)
    for _ in range(terms):
        s += (1 - t).ln()
        t *= q
    return (1 - x) * (1 - q).ln() - s


def num_derivative(f, x: Decimal) -> Decimal:
    h = D(10) ** -20
    return (f(x - 2 * h) - 8 * f(x - h) + 8 * f(x + h) - f(x + 2 * h)) / (12 * h)


def terms_for(q: Decimal) -> int:
    return int(170 / float(-q.log10())) + 5


TOL50 = D(10) ** -50


# ---------------------------------------------------------------------------
# B1. Even-order characters
# ---------------------------------------------------------------------------


def section_B1(spf, primes, divs):
    header("B1. Complex characters of even order: local vanishing, supports, mass")
    EX = len(divs) - 1
    moduli = [5, 7, 8, 9, 12, 13, 16]
    groups = {q: CharGroup(q) for q in moduli}
    nloc = 0
    nsup = 0
    for q, G in groups.items():
        check(G.L == carmichael(q), "exponent of character group mod %d" % q)
        for t in G.chars:
            # Lemma 1: local values at prime powers
            for p in primes:
                if p > EX:
                    break
                pe, e = p, 1
                while pe <= EX:
                    v = c_chi_exact(G, t, pe, divs[pe])
                    z = cyc_is_zero(v, G.L)
                    if q % p == 0:
                        check(cyc_is_rational(v, G.L, 1), "c(p^e)=1 for p|q")
                    else:
                        d = char_value_order(G, t, p)
                        check(z == (d >= 2 and (e + 1) % d == 0),
                              "local vanishing q=%d t=%s p=%d e=%d" % (q, t, p, e))
                    nloc += 1
                    pe *= p
                    e += 1
            # support criterion versus exact cyclotomic value for every n <= EX
            sup = support_by_criterion(G, t, EX, primes)
            ok = True
            for n in range(1, EX + 1):
                v = c_chi_exact(G, t, n, divs[n])
                ok &= (not cyc_is_zero(v, G.L)) == bool(sup[n])
                nsup += 1
            check(ok, "support criterion q=%d t=%s" % (q, t))
    print("Lemma 1 (local values) checked exactly at %d prime powers; support" % nloc)
    print("criterion equals exact nonvanishing of c_chi(n) in Z[zeta_L] for %d pairs (n <= %d)." % (nsup, EX))

    # Every character of even order takes the value -1; density of such primes
    NS = 200000
    big_primes = [p for p in primes if p <= NS]
    print("\nPrime density of {p : chi(p) = -1} up to %d versus 1/h, and support ratios:" % NS)
    print("%-26s %3s %4s %8s  %s" % ("character", "h", "par", "dens-1", "S(N)/N and S(N)(log N)^(1/h)/N at N=1e3,1e4,1e5,2e5"))
    examples = [(5, (1,)), (13, (1,)), (13, (2,)), (13, (3,)), (16, (0, 1)), (16, (1, 1)),
                (7, (1,)), (8, (1, 1)), (12, (1, 1))]
    sup_cache = {}
    for q, t in examples:
        G = groups[q]
        h = G.order(t)
        check(h % 2 == 0, "even order")
        check(any(G.value(t, m) == G.L // 2 for m in G.dlog), "even order => value -1 attained")
        cnt = sum(1 for p in big_primes if q % p and G.value(t, p) == G.L // 2)
        tot = sum(1 for p in big_primes if q % p)
        dens = cnt / tot
        check(abs(dens - 1 / h) < 0.02, "prime density 1/h (finite)")
        sup = support_by_criterion(G, t, NS, big_primes)
        sup_cache[(q, t)] = sup
        pref = [0] * (NS + 1)
        c = 0
        for n in range(1, NS + 1):
            c += sup[n]
            pref[n] = c
        row = []
        for X in (10 ** 3, 10 ** 4, 10 ** 5, 2 * 10 ** 5):
            row.append("%.3f/%.3f" % (pref[X] / X, pref[X] * math.log(X) ** (1 / h) / X))
        par = "odd" if G.is_odd(t) else "even"
        print("%-26s %3d %4s %8.4f  %s" % ("mod %d t=%s" % (q, t), h, par, dens, " ".join(row)))
        # Galois conjugates share the support
        for j in range(2, h):
            if gcd(j, h) == 1:
                tj = G.power(t, j)
                supj = support_by_criterion(G, tj, 20000, big_primes)
                check(supj[:20001] == sup[:20001], "Galois-conjugate supports agree")
    print("Galois-conjugate characters have identical supports (checked to 20000).")

    # Mass: kappa_h closed forms and growth of sum |c_chi(n)|
    print("\nMean of |1 + zeta| over mu_h (kappa_h) and closed forms:")
    for h in range(2, 13):
        kap = sum(abs(complex(1 + math.cos(2 * math.pi * j / h), math.sin(2 * math.pi * j / h)))
                  for j in range(h)) / h
        closed = (2 / h) / math.tan(math.pi / (2 * h)) if h % 2 == 0 else (2 / h) / math.sin(math.pi / (2 * h))
        check(abs(kap - closed) < 1e-12, "kappa_h closed form h=%d" % h)
        if h in (2, 3, 4, 6, 8, 12):
            print("  h=%2d  kappa_h=%.6f  exponent kappa_h-1=%.6f" % (h, kap, kap - 1))
    check(abs(4 / math.pi - (2 / 4096) / math.tan(math.pi / 8192)) < 1e-6, "kappa_h -> 4/pi")

    def abs_mass(G, t, X):
        tot = 0.0
        for n in range(1, X + 1):
            m = n
            val = 1.0
            while m > 1:
                p = spf[m]
                e = 0
                while m % p == 0:
                    m //= p
                    e += 1
                v = G.value(t, p)
                if v is None:
                    continue
                if v == 0:
                    val *= e + 1
                else:
                    th = 2 * math.pi * v / G.L
                    val *= abs(math.sin((e + 1) * th / 2) / math.sin(th / 2))
            tot += val
        return tot

    print("\nAbsolute mass A(X)/X of c_chi (finite data; theory: X (log X)^(kappa_h - 1)):")
    taus = tau_list(10 ** 5)
    for q, t in [(5, (1,)), (5, (2,)), (13, (2,)), (16, (0, 1))]:
        G = groups[q]
        h = G.order(t)
        kap = (2 / h) / math.tan(math.pi / (2 * h))
        row = []
        prev = 0.0
        ratios = []
        for X in (10 ** 3, 10 ** 4, 10 ** 5):
            A = abs_mass(G, t, X)
            check(A <= sum(taus[1:X + 1]) + 1e-6, "mass <= sum tau")
            ratios.append(A / X)
            row.append("A/X=%.4f A/(X log^%.3f X)=%.4f" % (A / X, kap - 1, A / (X * math.log(X) ** (kap - 1))))
        if h >= 4:
            check(ratios[0] < ratios[1] < ratios[2], "superlinear mass visible for h>=4 (finite)")
        print("  mod %d t=%s h=%d: %s" % (q, t, h, "; ".join(row)))

    # Odd order: c_chi(n) != 0 on squarefree n coprime to q
    print("\nOdd-order characters: nonvanishing on squarefree n coprime to q:")
    for q, t in [(7, (2,)), (9, (2,)), (13, (4,))]:
        G = groups[q]
        h = G.order(t)
        check(h % 2 == 1 and h >= 3, "odd order")
        check(all(char_value_order(G, t, m) % 2 == 1 for m in G.dlog), "odd order never takes -1")
        bad = 0
        for n in range(1, EX + 1):
            if gcd(n, q) == 1 and is_squarefree_spf(n, spf):
                if cyc_is_zero(c_chi_exact(G, t, n, divs[n]), G.L):
                    bad += 1
        check(bad == 0, "odd-order nonvanishing on squarefree coprime n")
        sup = support_by_criterion(G, t, NS, big_primes)
        dens = sum(sup) / NS
        lower = 6 / math.pi ** 2
        for p in factor(q):
            lower *= p / (p + 1)
        check(dens >= lower - 0.01, "odd-order support density >= squarefree-coprime density")
        print("  mod %d t=%s (order %d): no zero among squarefree coprime n <= %d; S(N)/N = %.4f >= %.4f" %
              (q, t, h, EX, dens, lower))
    # integer combination chi + chibar mod 7 (cubic): 2*1_{1,6} - 1_{2,5} - 1_{3,4}
    wt7 = [0, 2, -1, -1, -1, -1, 2]
    a7 = one_star_periodic(wt7, 7, NS)
    zeros_sf = sum(1 for n in range(1, NS + 1) if n % 7 and a7[n] == 0 and is_squarefree_spf(n, spf))
    check(zeros_sf == 0, "1*(chi+chibar) mod 7 nonzero on squarefree coprime n")
    print("  1*(2*1_{1,6} - 1_{2,5} - 1_{3,4}) mod 7 is nonzero on every squarefree n <= %d prime to 7;"
          " support density %.4f" % (NS, sum(1 for n in range(1, NS + 1) if a7[n]) / NS))
    return groups, sup_cache


# ---------------------------------------------------------------------------
# B1.5 / B3.4: integer weights, even sector, complementary sector
# ---------------------------------------------------------------------------


def sylow2(q: int) -> list[int]:
    units = [m for m in range(1, q) if gcd(m, q) == 1] if q > 1 else [0]
    if q <= 2:
        return [1 % q] if q > 1 else [0]
    ph = len(units)
    two = 1
    while ph % (2 * two) == 0:
        two *= 2
    return [m for m in units if pow(m, two, q) == 1]


def strata(wt: list[int], M: int):
    """Yield (g, M/g, w_g) with w_g(x) = w(g x) on units mod M/g."""
    for g in divisors_of(M):
        Mg = M // g
        units = [x for x in range(Mg) if gcd(x, Mg) == 1] if Mg > 1 else [0]
        yield g, Mg, {x: wt[(g * x) % M] for x in units}


def sector_split(wt: list[int], M: int):
    """Return (in_even_sector, complementary projection per stratum, P2 sizes)."""
    even = True
    proj = {}
    sizes = {}
    for g, Mg, wg in strata(wt, M):
        P2 = sylow2(Mg) if Mg > 2 else ([1] if Mg == 2 else [0])
        sizes[g] = len(P2)
        cos = {}
        for x in wg:
            key = min((x * y) % Mg for y in P2) if Mg > 1 else 0
            cos.setdefault(key, []).append(x)
        pg = {}
        for key, xs in cos.items():
            s = sum(wg[x] for x in xs)
            for x in xs:
                pg[x] = Fraction(s, len(P2))
            if s != 0:
                even = False
        proj[g] = pg
    return even, proj, sizes


def char_coeffs(G: CharGroup, wt_units: dict[int, int]):
    """phi(q) * hat w(chi) as cyclotomic histograms, for w on units mod q."""
    out = {}
    for t in G.chars:
        v = [0] * G.L
        for x, wx in wt_units.items():
            if wx:
                val = G.value(t, x)
                v[(-val) % G.L] += wx
        out[t] = v
    return out


def section_B3_sectors(spf, primes, groups):
    header("B1.5 / B3.4. Integer periodic weights: even-order sector versus complement")
    NW = 100000
    rng = random.Random(21)
    print("Table: modulus M, phi, lambda, |P2|, dim of even sector on units, "
          "max order of an odd character")
    print("%4s %4s %4s %4s %6s %6s" % ("M", "phi", "lam", "|P2|", "dimE", "Hodd"))
    for M in [3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 17, 20, 21, 24]:
        G = CharGroup(M)
        P2 = sylow2(M)
        n_odd_order = sum(1 for t in G.chars if G.order(t) % 2 == 1)
        check(n_odd_order * len(P2) == G.phi, "odd-order characters = characters of G/P2")
        odd_orders = [G.order(t) for t in G.chars if G.is_odd(t)]
        check(all(o % 2 == 0 for o in odd_orders), "odd characters have even order")
        check(max(odd_orders) == carmichael(M), "max odd order = lambda(M)")
        print("%4d %4d %4d %4d %6d %6d" % (M, G.phi, G.L, len(P2), G.phi - n_odd_order, max(odd_orders)))
    for M in range(3, 301):
        G = CharGroup(M)
        odd_orders = [G.order(t) for t in G.chars if G.is_odd(t)]
        check(all(o % 2 == 0 for o in odd_orders) and max(odd_orders) == carmichael(M),
              "odd characters: even order, max order lambda(M), M=%d" % M)
    print("For every 3 <= M <= 300: odd characters have even order and the largest is lambda(M).")
    # equivalence: P2-coset sums vanish <=> no odd-order character component (exact)
    for M in [5, 7, 9, 13, 15, 16, 21]:
        G = CharGroup(M)
        units = [x for x in range(1, M) if gcd(x, M) == 1]
        for _ in range(30):
            wu = {x: rng.randint(-3, 3) for x in units}
            if rng.random() < 0.5:
                # project to the even sector exactly (scaled by |P2|)
                P2 = sylow2(M)
                wu = {x: len(P2) * wu[x] - sum(wu[(x * y) % M] for y in P2) for x in units}
            wt = [0] * M
            for x in units:
                wt[x] = wu[x]
            ev, _, _ = sector_split(wt, M)
            cc = char_coeffs(G, wu)
            no_odd = all(cyc_is_zero(cc[t], G.L) for t in G.chars if G.order(t) % 2 == 1)
            check(ev == no_odd, "coset criterion <=> no odd-order component (M=%d)" % M)
    print("Coset criterion equals vanishing of all odd-order Fourier coefficients (exact, 210 weights).")

    # support containment in the union of character supports, and density behaviour
    print("\nSupport densities S(X)/X at X = 1e3, 1e4, 1e5 (even sector decreases; complement stays):")
    # mod 13: trace of an even character of order 6, w(x) = 2 cos(pi dlog_2(x) / 3)
    G13 = CharGroup(13)
    t6 = next(t for t in G13.chars if G13.order(t) == 6)
    check(not G13.is_odd(t6), "order-6 characters mod 13 are even")
    tr6 = {x: round(2 * math.cos(2 * math.pi * G13.value(t6, x) / G13.L)) for x in range(1, 13)}
    tests = [
        ("mod 5  1_1 - 1_2 (Phase 20 OQ2)", 5, {1: 1, 2: -1}),
        ("mod 5  1_1 + 1_4 - 1_2 - 1_3 (chi_5)", 5, {1: 1, 4: 1, 2: -1, 3: -1}),
        ("mod 13 1_1 - 1_5 (P2-coset zero sum)", 13, {1: 1, 5: -1}),
        ("mod 13 chi6 + conj chi6 (even, order 6)", 13, tr6),
        ("mod 16 1_{1,15} - 1_{7,9} (even, order 4)", 16, {1: 1, 15: 1, 7: -1, 9: -1}),
        ("mod 16 1_1 - 1_9 (order-4 characters)", 16, {1: 1, 9: -1}),
        ("mod 7  1_1 - 1_6 (odd)", 7, {1: 1, 6: -1}),
        ("mod 7  1_1 - 1_2 (mixed)", 7, {1: 1, 2: -1}),
        ("mod 7  1_{1,6} - 1_{2,5} (complement)", 7, {1: 1, 6: 1, 2: -1, 5: -1}),
        ("mod 9  1_{1,8} - 1_{2,7} (complement)", 9, {1: 1, 8: 1, 2: -1, 7: -1}),
        ("mod 13 1_{P2} - 1_{2P2} (complement)", 13, {1: 1, 5: 1, 8: 1, 12: 1, 2: -1, 3: -1, 10: -1, 11: -1}),
    ]
    taus = tau_list(NW)
    big_primes = [p for p in primes if p <= NW]
    for name, M, dct in tests:
        wt = [0] * M
        for k, v in dct.items():
            wt[k % M] = v
        ev, proj, _ = sector_split(wt, M)
        a = one_star_periodic(wt, M, NW)
        dens = []
        for X in (10 ** 3, 10 ** 4, 10 ** 5):
            dens.append(sum(1 for n in range(1, X + 1) if a[n]) / X)
        mass = sum(abs(a[n]) for n in range(1, NW + 1))
        check(mass <= max(abs(v) for v in wt) * sum(taus[1:NW + 1]), "mass bound")
        if ev:
            G = groups.get(M) or CharGroup(M)
            units = {x: wt[x] for x in range(1, M) if gcd(x, M) == 1}
            cc = char_coeffs(G, units)
            used = [t for t in G.chars if not cyc_is_zero(cc[t], G.L)]
            check(all(G.order(t) % 2 == 0 for t in used), "even sector uses even-order characters")
            union = bytearray(NW + 1)
            for t in used:
                s = support_by_criterion(G, t, NW, big_primes)
                for n in range(1, NW + 1):
                    if s[n]:
                        union[n] = 1
            check(all(union[n] for n in range(1, NW + 1) if a[n]), "support inside union of character supports")
            check(dens[2] < dens[0], "even sector: finite density decreases")
            H = max(G.order(t) for t in used)
            par = "".join(sorted(set("o" if G.is_odd(t) else "e" for t in used)))
            tag = "even sector H=%d %s" % (H, par)
        else:
            check(min(dens) > 0.4, "complementary/mixed: finite density stays large")
            tag = "NOT even sector"
        print("  %-40s %-18s %s" % (name, tag, " ".join("%.4f" % d for d in dens)))

    # trace lemma: (1 + zeta_H)^i, i < phi(H), form a Q-basis of Q(zeta_H)
    for H in (4, 6, 8, 10, 12, 16):
        ph = euler_phi(H)
        rows = []
        cur = [1] + [0] * (H - 1)
        for i in range(ph):
            rows.append([Fraction(c) for c in cyc_reduce(cur, H)])
            nxt = [0] * H
            for j, c in enumerate(cur):
                nxt[j] += c
                nxt[(j + 1) % H] += c
            cur = nxt
        # determinant by Gaussian elimination
        Mx = [r[:] for r in rows]
        det = Fraction(1)
        for c in range(ph):
            piv = next((r for r in range(c, ph) if Mx[r][c] != 0), None)
            check(piv is not None, "basis (1+zeta)^i")
            if piv != c:
                Mx[c], Mx[piv] = Mx[piv], Mx[c]
                det = -det
            det *= Mx[c][c]
            for r in range(c + 1, ph):
                f = Mx[r][c] / Mx[c][c]
                for cc_ in range(c, ph):
                    Mx[r][cc_] -= f * Mx[c][cc_]
        check(det != 0, "nonzero determinant")
    print("\n(1+zeta_H)^i, 0 <= i < phi(H), is a Q-basis of Q(zeta_H) for H = 4,6,8,10,12,16 (exact).")


# ---------------------------------------------------------------------------
# B2. Powers of two
# ---------------------------------------------------------------------------


def section_B2(spf, primes, divs):
    header("B2. Moduli 2^k: exact identities, k-independent supports, binary transfer")
    EX = 1500
    for k in range(2, 8):
        q = 2 ** k
        G = CharGroup(q)
        orders = {}
        for t in G.chars:
            if G.is_principal(t):
                continue
            h = G.order(t)
            orders[h] = orders.get(h, 0) + 1
            check(h & (h - 1) == 0 and h <= max(2, 2 ** (k - 2)), "order divides 2^(k-2)")
            c = G.conductor(t)
            if h == 2:
                check(c in (4, 8), "conductor of real characters")
            else:
                check(c == 4 * h, "conductor 2^(j+2) for order 2^j >= 4")
        expect = {}
        if k >= 3:
            expect[2] = 3
            for j in range(2, k - 1):
                expect[2 ** j] = 2 ** j
        else:
            expect[2] = 1
        check(orders == expect, "number of characters of each order mod 2^%d" % k)
    print("Mod 2^k (k=2..7): orders divide 2^(k-2); #order-2 chars = 3, #order-2^j chars = 2^j;")
    print("order-2^j characters (j >= 2) have conductor 2^(j+2); real ones conductor 4 or 8.")

    # exact orthogonality and coefficient identity mod 16 and 32
    for k in (4, 5):
        q = 2 ** k
        G = CharGroup(q)
        L = G.L
        odd = [m for m in range(1, q, 2)]
        for r in odd:
            for m in odd:
                v = [0] * L
                for t in G.chars:
                    v[(G.value(t, m) - G.value(t, r)) % L] += 1
                check(cyc_is_rational(v, L, 2 ** (k - 1) if m == r else 0), "orthogonality mod %d" % q)
        nonprin = [t for t in G.chars if not G.is_principal(t)]
        cvals = {t: [None] + [c_chi_exact(G, t, n, divs[n]) for n in range(1, EX + 1)] for t in nonprin}
        for r in odd:
            for n in range(1, EX + 1):
                lhs = 2 ** (k - 1) * sum(1 for d in divs[n] if d % q == r) - sum(1 for d in divs[n] if d % 2)
                v = [0] * L
                for t in nonprin:
                    sh = (-G.value(t, r)) % L
                    cv = cvals[t][n]
                    for j, c in enumerate(cv):
                        if c:
                            v[(j + sh) % L] += c
                check(cyc_is_rational(v, L, lhs), "coefficient identity mod %d r=%d n=%d" % (q, r, n))
        print("Exact in Z[zeta_%d]: orthogonality mod %d and 2^(k-1) tau_r - tau_odd = sum_{chi != chi0}"
              " conj(chi(r)) c_chi(n), all odd r, n <= %d." % (L, q, EX))

    # supports: k-independence, distinct supports, union bound, S_k(N)
    NS = 100000
    big_primes = [p for p in primes if p <= NS]
    todd = [0] * (NS + 1)
    for d in range(1, NS + 1, 2):
        for n in range(d, NS + 1, d):
            todd[n] += 1
    prim_sup = {}
    for k in range(2, 9):
        q = 2 ** k
        G = CharGroup(q)
        sups = {}
        for t in G.chars:
            if G.is_principal(t):
                continue
            s = bytes(support_by_criterion(G, t, NS, big_primes))
            c = G.conductor(t)
            # compare with the primitive character mod c
            Gc = CharGroup(c)
            tc = next(u for u in Gc.chars
                      if all(Gc.value(u, m) * (G.L // Gc.L) % G.L == G.value(t, m) for m in range(1, c, 2)))
            key = (c, tc)
            if key not in prim_sup:
                prim_sup[key] = bytes(support_by_criterion(Gc, tc, NS, big_primes))
            check(prim_sup[key] == s, "support equals that of the primitive character")
            sups[t] = s
        distinct = len(set(sups.values()))
        check(distinct == (1 if k == 2 else 2 * k - 3), "number of distinct supports mod 2^%d" % k)
        union = bytearray(NS + 1)
        for s in set(sups.values()):
            for n in range(1, NS + 1):
                if s[n]:
                    union[n] = 1
        row = []
        for r in sorted(set(r for r in (1, 3, q - 1) if r < q)):
            tr = [0] * (NS + 1)
            for d in range(r, NS + 1, q):
                for n in range(d, NS + 1, d):
                    tr[n] += 1
            a = [2 ** (k - 1) * tr[n] - todd[n] for n in range(NS + 1)]
            check(all(union[n] for n in range(1, NS + 1) if a[n]), "supp(a_k) inside union")
            row.append("r=%d:%.4f" % (r, sum(1 for n in range(1, NS + 1) if a[n]) / NS))
        print("  k=%d: %2d distinct supports; union/N=%.4f; S_k(N)/N: %s" %
              (k, distinct, sum(union) / NS, " ".join(row)))
    print("Supports of order-2^j characters mod 2^k equal those of the primitive characters mod 2^(j+2):")
    print("the union bound for S_k(N) uses 2k-3 k-independent sets (checked to N = %d)." % NS)


def section_B2_disc():
    header("B2. Certified binary discrepancies: A_{r,2^k}, E_odd and Z_{k,r} = 2^(k-1) A_r - E_odd")
    N = 2000
    K = N + 80
    tau_odd = [0] * (K + 1)
    for d in range(1, K + 1, 2):
        for n in range(d, K + 1, d):
            tau_odd[n] += 1
    Eodd = lambert_num(2, K, tau_odd, 1)
    dE = disc_N(Eodd, N)
    print("D_%d(E_odd; 2) = %.4f" % (N, dE))
    rows = []
    for k in (2, 3, 4, 5, 6):
        q = 2 ** k
        for r in sorted(set(r for r in (1, 3, q - 1) if r < q)):
            tr = [0] * (K + 1)
            for d in range(r, K + 1, q):
                for n in range(d, K + 1, d):
                    tr[n] += 1
            A = lambert_num(2, K, tr, 1)
            Z = A.scale(2 ** (k - 1)) - Eodd
            dA = disc_N(A, N)
            dZ = disc_N(Z, N)
            dAs = disc_N(A.scale(2 ** (k - 1)), N)
            check(abs(dAs - dA) <= (k - 1) / N + 1e-9, "radix shift lemma")
            check(abs(dA - dE) <= (k - 1) / N + (1 - dZ) + 1e-9, "transfer inequality")
            rows.append((k, r, dA, dZ))
    print("%3s %5s %10s %12s %12s" % ("k", "r", "D_N(A_r)", "1-D_N(Z)", "|D(A)-D(E)|"))
    for k, r, dA, dZ in rows:
        print("%3d %5d %10.4f %12.4f %12.4f" % (k, r, dA, 1 - dZ, abs(dA - dE)))
    print("Every row satisfies |D_N(A_r)-D_N(E_odd)| <= (k-1)/N + (1-D_N(Z)) (sharp translation + radix shift).")

    # odd base: class differences in base 3
    N3 = 1200
    K3 = N3 + 50
    for k in (4, 5):
        q = 2 ** k
        w = [0] * q
        w[1], w[3] = 1, -1
        a = one_star_periodic(w, q, K3)
        X = lambert_num(3, K3, a, 1)
        print("base 3: 1 - D_%d(A_{1,%d}(3) - A_{3,%d}(3); 3) = %.4f (finite data)" % (N3, q, q, 1 - disc_N(X, N3)))
    # base 4, k = 4: 2^(k-1) = 8 is not a power of 4
    N4 = 1200
    K4 = N4 + 40
    tau_odd4 = [0] * (K4 + 1)
    for d in range(1, K4 + 1, 2):
        for n in range(d, K4 + 1, d):
            tau_odd4[n] += 1
    E4 = lambert_num(4, K4, tau_odd4, 1)
    tr = [0] * (K4 + 1)
    for d in range(1, K4 + 1, 16):
        for n in range(d, K4 + 1, d):
            tr[n] += 1
    A4 = lambert_num(4, K4, tr, 1)
    Z4 = A4.scale(8) - E4
    dA4, dE4, d2E4, dZ4 = disc_N(A4, N4), disc_N(E4, N4), disc_N(E4.scale(2), N4), disc_N(Z4, N4)
    # A_r(4) = (2 E_odd(4) + 2 Z)/16 : compare with 2 E_odd
    check(abs(disc_N(A4.scale(16), N4) - d2E4) <= (1 - disc_N(Z4.scale(2), N4)) + 1e-9, "base-4 transfer to 2E_odd")
    print("base 4, k=4, r=1: D(A_r)=%.4f, D(E_odd)=%.4f, D(2E_odd)=%.4f, 1-D(Z)=%.4f (finite data)" %
          (dA4, dE4, d2E4, 1 - dZ4))


# ---------------------------------------------------------------------------
# B3. Antisymmetric and odd periodic weights
# ---------------------------------------------------------------------------


def section_B3(spf, primes, groups):
    header("B3. Antisymmetric and general odd periodic Lambert weights")
    NW = 100000
    for M in (3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 16):
        G = CharGroup(M)
        units = [x for x in range(1, M) if gcd(x, M) == 1]
        for r in units:
            wu = {x: (1 if x == r else 0) - (1 if x == (M - r) % M else 0) for x in units}
            cc = char_coeffs(G, wu)
            for t in G.chars:
                target = [0] * G.L
                if G.is_odd(t):
                    target[(-G.value(t, r)) % G.L] = 2
                check(cyc_is_zero([a - b for a, b in zip(cc[t], target)], G.L),
                      "phi*hat w = (1-chi(-1)) conj chi(r)")
    print("phi(M) hat w(chi) = (1 - chi(-1)) conj(chi(r)) for w = 1_r - 1_{-r}: only odd characters,")
    print("each of even order, max order lambda(M) (exact for M = 3..10, 12, 13, 16).")

    # elementary vanishing at p = -1 mod M, and density table
    print("\nw = 1_r - 1_{-r}: zeros forced by primes p = -1 (mod M); S(X)/X and S(X)(log X)^(1/lambda)/X:")
    big_primes = [p for p in primes if p <= NW]
    for M, r in [(3, 1), (4, 1), (5, 1), (5, 2), (7, 1), (8, 1), (8, 3), (12, 1), (12, 5), (13, 1), (16, 3)]:
        wt = [0] * M
        wt[r % M] += 1
        wt[(-r) % M] -= 1
        a = one_star_periodic(wt, M, NW)
        neg = [p for p in big_primes if p % M == M - 1]
        killed = bytearray(NW + 1)
        for p in neg:
            pe = p
            while pe <= NW:
                for n in range(pe, NW + 1, pe):
                    if (n // pe) % p:
                        killed[n] = 1
                pe *= p * p
        check(all(a[n] == 0 for n in range(1, NW + 1) if killed[n]), "vanishing at p = -1 mod M")
        lam = carmichael(M)
        row = []
        for X in (10 ** 3, 10 ** 4, 10 ** 5):
            S = sum(1 for n in range(1, X + 1) if a[n])
            row.append("%.3f/%.3f" % (S / X, S * math.log(X) ** (1 / lam) / X))
        print("  M=%2d r=%2d lambda=%2d: %s" % (M, r, lam, " ".join(row)))

    # general odd periodic weights, gcd strata
    rng = random.Random(1729)
    NG = 4000
    for M in (6, 8, 9, 10, 12, 15, 18):
        for _ in range(6):
            wt = [0] * M
            for x in range(1, M):
                if 2 * x < M:
                    v = rng.randint(-3, 3)
                    wt[x], wt[M - x] = v, -v
            check(wt[0] == 0 and (M % 2 or wt[M // 2] == 0), "odd weight vanishes at 0 and M/2")
            a = one_star_periodic(wt, M, NG)
            # strata identity (1*w)(n) = sum_{g | gcd(n, M)} (1*w~_g)(n/g)
            st = list(strata(wt, M))
            parts = {}
            for g, Mg, wg in st:
                wtg = [0] * Mg if Mg > 1 else [0]
                for x, v in wg.items():
                    wtg[x % Mg if Mg > 1 else 0] = v
                if Mg <= 2:
                    check(all(v == 0 for v in wg.values()), "strata M/g in {1,2} vanish for odd w")
                else:
                    check(all(wg[x] == -wg[(Mg - x) % Mg] for x in wg), "strata are odd")
                parts[g] = one_star_periodic(wtg, Mg, NG) if Mg > 1 else [0] * (NG + 1)
            for n in range(1, NG + 1):
                s = sum(parts[g][n // g] for g, _, _ in st if n % g == 0)
                check(s == a[n], "gcd decomposition of 1*w")
            # vanishing at p = -1 mod M (any gcd)
            for p in primes:
                if p > NG:
                    break
                if p % M == M - 1:
                    for n in range(p, NG + 1, p):
                        if (n // p) % p:
                            check(a[n] == 0, "odd weight killed by p = -1 mod M")
    print("\nGeneral odd periodic integer weights (M = 6, 8, 9, 10, 12, 15, 18; 42 random weights):")
    print("gcd-strata identity, oddness of strata, and vanishing at p = -1 (mod M) hold for n <= %d." % NG)

    # certified discrepancies of A_{r,M}(b) - A_{-r,M}(b)
    print("\n1 - D_N(A_{r,M}(b) - A_{-r,M}(b); b) (finite data), with the Lambert-sum cross-check:")
    print("%6s %4s %4s %9s" % ("(M,r)", "b", "N", "1-D_N"))
    for (M, r) in [(3, 1), (4, 1), (5, 1), (5, 2), (7, 1), (7, 3), (8, 3), (12, 5)]:
        for b in (2, 3, 5, 10):
            N = {2: 1500, 3: 1000, 5: 800, 10: 600}[b]
            K = N + int(60 / math.log2(b)) + 10
            wt = [0] * M
            wt[r % M] += 1
            wt[(-r) % M] -= 1
            a = one_star_periodic(wt, M, K)
            X = lambert_num(b, K, a, 1)
            # cross-check against the exact Lambert sum truncated at K
            Lsum = A_exact(b, M, r, K) - A_exact(b, M, M - r, K)
            approx = Fraction(X.S, b ** K)
            check(abs(Lsum - approx) <= Fraction(X.T + 4 * (K + 2), b ** K), "Lambert sum = coefficient series")
            print("%6s %4d %4d %9.4f" % ("(%d,%d)" % (M, r), b, N, 1 - disc_N(X, N)))


# ---------------------------------------------------------------------------
# B4. q-digamma and other q-special functions
# ---------------------------------------------------------------------------


def section_B4(spf, primes):
    header("B4. q-digamma reflection, multiplication formula, q-polygamma, two-character sums")
    cases = [(2, 3, 1), (2, 4, 1), (2, 5, 1), (2, 5, 2), (3, 7, 3), (5, 6, 1), (10, 12, 5), (2, 8, 3),
             (2, 6, 2), (3, 9, 3), (10, 10, 4), (2, 6, 3), (2, 2, 1), (7, 13, 6)]
    worst_def = D(0)
    worst_ref = D(0)
    for (b, M, r) in cases:
        q = D(b) ** (-M)
        lnq = -M * D(b).ln()
        tm = terms_for(q)
        x = D(r) / D(M)
        y = 1 - x
        pn = num_derivative(lambda z: log_gamma_q_var(q, lnq, z, tm), x)
        pd = psi_q_def(q, lnq, x, tm)
        pl = psi_q_lambert(q, lnq, x, int(170 / float(-x * q.log10())) + 5)
        worst_def = max(worst_def, abs(pn - pd), abs(pl - pd))
        check(abs(pn - pd) < TOL50 and abs(pl - pd) < TOL50, "psi_q definition / Lambert / derivative")
        lhs = (pd - psi_q_def(q, lnq, y, tm)) / lnq
        Kc = int(70 / math.log10(b)) + M + 5
        rhs = dec(A_exact(b, M, r, Kc) - A_exact(b, M, M - r, Kc))
        worst_ref = max(worst_ref, abs(lhs - rhs))
        check(abs(lhs - rhs) < TOL50, "q-digamma reflection identity (b,M,r)=(%d,%d,%d)" % (b, M, r))
        check(lnq < 0, "log q < 0")
        if 2 * r < M:
            check(rhs > 0 and pd - psi_q_def(q, lnq, y, tm) < 0, "sign: A_r > A_{-r}, psi_q increasing")
        if 2 * r == M:
            check(abs(lhs) < TOL50, "2r = M gives 0")
        g = gcd(r, M)
        if g > 1 and 2 * r != M:
            # same q, base b^g, modulus M/g
            Kg = int(70 / math.log10(b ** g)) + M + 5
            alt = dec(A_exact(b ** g, M // g, r // g, Kg) - A_exact(b ** g, M // g, (M - r) // g, Kg))
            check(abs(alt - rhs) < TOL50, "gcd reduction to base b^g")
    print("psi_q via (i) derivative of log Gamma_q, (ii) the definition, (iii) the Lambert series:")
    print("  max discrepancy %.1e over %d cases." % (worst_def, len(cases)))
    print("[psi_q(r/M) - psi_q(1-r/M)] / log q = + (A_{r,M}(b) - A_{M-r,M}(b)): max error %.1e" % worst_ref)
    print("  (sign +; log q < 0 and psi_q(r/M) < psi_q(1-r/M) for 2r < M; 2r = M gives 0; gcd reduction ok)")

    # Reflection product and Jacobi triple product
    b, M = 2, 5
    q = D(b) ** (-M)
    lnq = -M * D(b).ln()
    tm = terms_for(q)

    def qpoch(a: Decimal, n: int) -> Decimal:
        p = D(1)
        t = a
        for _ in range(n):
            p *= 1 - t
            t *= q
        return p

    for r in (1, 2):
        x = D(r) / D(M)
        qx = (x * lnq).exp()
        q1x = ((1 - x) * lnq).exp()
        logG = lambda z: log_gamma_q_var(q, lnq, z, tm) + sum((1 - q ** (n + 1)).ln() for n in range(tm))
        lhs = logG(x) + logG(1 - x)
        rhs = (1 - q).ln() + 2 * qpoch(q, tm).ln() - qpoch(qx, tm).ln() - qpoch(q1x, tm).ln()
        check(abs(lhs - rhs) < TOL50, "Gamma_q reflection product")
        theta = sum((1 if n % 2 == 0 else -1) * (D(n * (n - 1)) / 2 * lnq + n * x * lnq).exp()
                    for n in range(-40, 41))
        check(abs(qpoch(qx, tm) * qpoch(q1x, tm) * qpoch(q, tm) - theta) < TOL50, "Jacobi triple product")
        dlog = num_derivative(lambda z: sum((1 if n % 2 == 0 else -1) * (D(n * (n - 1)) / 2 * lnq + n * z * lnq).exp()
                                            for n in range(-40, 41)).ln(), x)
        refl = psi_q_def(q, lnq, x, tm) - psi_q_def(q, lnq, 1 - x, tm)
        check(abs(refl + dlog) < TOL50, "psi_q(x) - psi_q(1-x) = -d/dx log theta")
    print("Gamma_q(x)Gamma_q(1-x) = (1-q)(q;q)^2/((q^x;q)(q^(1-x);q)), Jacobi triple product, and")
    print("psi_q(x) - psi_q(1-x) = -(d/dx) log sum (-1)^n q^(n(n-1)/2 + n x): 50 digits at q = 2^-5.")

    # Gauss multiplication formula
    for (b, M, n) in [(2, 3, 2), (3, 4, 3), (2, 5, 2)]:
        q = D(b) ** (-M)
        lnq = -M * D(b).ln()
        for xr in (Fraction(1, 7), Fraction(2, 5)):
            x = dec(xr)
            qn = q ** n
            lhs = n * psi_q_def(q, lnq, n * x, terms_for(q))
            rhs = n * ((1 - qn) / (1 - q)).ln() + sum(psi_q_def(qn, n * lnq, x + D(j) / D(n), terms_for(qn))
                                                    for j in range(n))
            check(abs(lhs - rhs) < TOL50, "q-Gauss multiplication")
    # its rational-point content is the partition relation A_{r,M} = sum_j A_{r+jM, nM}
    for (b, M, r, n) in [(2, 5, 2, 3), (3, 4, 1, 2)]:
        Kc = 200
        lhs = A_exact(b, M, r, Kc)
        rhs = sum(A_exact(b, n * M, r + j * M, Kc) for j in range(n))
        check(lhs == rhs, "partition relation")
    print("n psi_q(nx) = n log[n]_q + sum_j psi_{q^n}(x + j/n): 50 digits; at rational points it only")
    print("returns the partition relations A_{r,M} = sum_j A_{r+jM,nM} (exact).")

    # q-digamma linear forms: M = 5 zero-sum combination
    b, M = 3, 5
    q = D(b) ** (-M)
    lnq = -M * D(b).ln()
    tm = terms_for(q)
    cvec = {1: 2, 2: -1, 3: 0, 4: -1}
    lhs = sum(c * psi_q_def(q, lnq, D(r) / D(M), tm) for r, c in cvec.items()) / lnq
    rhs = dec(sum(c * A_exact(b, M, r, 200) for r, c in cvec.items()))
    check(abs(lhs - rhs) < TOL50, "q-digamma linear form mod 5")
    print("[2 psi_q(1/5) - psi_q(2/5) - psi_q(4/5)] / log q = 2A_1 - A_2 - A_4 at q = 3^-5 (50 digits);")
    print("its weight is in the even sector mod 5, so the value lies in K_3 (Corollary B4.3).")

    # q-polygamma j = 1
    b, M, r = 2, 5, 1
    q = D(b) ** (-M)
    lnq = -M * D(b).ln()
    tm = terms_for(q)
    x = D(r) / D(M)
    d1 = num_derivative(lambda z: psi_q_def(q, lnq, z, tm), x)
    d2 = num_derivative(lambda z: psi_q_def(q, lnq, z, tm), 1 - x)
    lhs = (d1 - d2) / lnq ** 2
    NP = 400
    coef = [0] * (NP + 1)
    for m in range(1, NP + 1):
        wm = (1 if m % M == r else 0) - (1 if m % M == M - r else 0)
        if wm:
            for kk in range(1, NP // m + 1):
                coef[kk * m] += wm * kk
    rhs = sum(D(coef[n]) / D(b) ** n for n in range(1, NP + 1))
    check(abs(lhs - rhs) < D(10) ** -40, "q-polygamma series (40 digits; numerical derivative)")
    NW = 100000
    coefW = [0] * (NW + 1)
    for m in range(1, NW + 1):
        wm = (1 if m % M == r else 0) - (1 if m % M == M - r else 0)
        if wm:
            for kk in range(1, NW // m + 1):
                coefW[kk * m] += wm * kk
    row = []
    for X in (10 ** 3, 10 ** 4, 10 ** 5):
        S = sum(1 for n in range(1, X + 1) if coefW[n])
        W = sum(1 + int(math.log2(abs(coefW[n]))) for n in range(1, X + 1) if coefW[n])
        row.append((X, S / X, W / X))
    check(row[0][2] < row[1][2] < row[2][2] and row[2][2] > 1, "q-polygamma width density exceeds 1 and grows")
    check(all(s == 1.0 for _, s, _ in row), "q-polygamma (M,r)=(5,1): every coefficient nonzero")
    # local nonvanishing of id^j * chi at prime powers: |sum_i chi(p)^i p^{(e-i)j}| > 0
    for p in (3, 7, 11, 13):
        for e in range(1, 6):
            for j in (1, 2):
                low = p ** (e * j) - sum(p ** ((e - i) * j) for i in range(1, e + 1))
                check(low > 0, "id^j * chi never vanishes at p^e")
    dens2 = []
    for (M2, r2) in ((5, 2), (7, 3), (12, 5)):
        cf = [0] * (NW + 1)
        for m in range(1, NW + 1):
            wm = (1 if m % M2 == r2 else 0) - (1 if m % M2 == M2 - r2 else 0)
            if wm:
                for kk in range(1, NW // m + 1):
                    cf[kk * m] += wm * kk
        d = [sum(1 for n in range(1, X + 1) if cf[n]) / X for X in (10 ** 3, 10 ** 4, 10 ** 5)]
        check(d[0] < d[1] < d[2] and d[2] > 0.7, "q-polygamma support density large and increasing (finite)")
        dens2.append(((M2, r2), d))
    print("q-polygamma (j=1): normalized reflection coefficients sum_{m|n} (n/m)(1_r - 1_{-r})(m) (40 digits);")
    print("  (M,r)=(5,1): all coefficients nonzero to 1e5; binary width density W(X)/X: " +
          ", ".join("X=%d: %.2f" % (X, w) for X, _, w in row))
    print("  support densities at 1e3,1e4,1e5: " +
          "; ".join("(%d,%d): %s" % (mr[0], mr[1], " ".join("%.3f" % v for v in d)) for mr, d in dens2) +
          "  -> dense support and polynomial size: the method fails.")

    # two-character sums psi = chi_4, phi = chi_{-3}
    def chi4(m):
        return 0 if m % 2 == 0 else (1 if m % 4 == 1 else -1)

    def chim3(m):
        return 0 if m % 3 == 0 else (1 if m % 3 == 1 else -1)

    def chi12(m):
        return chi4(m) * chim3(m)

    check(chi4(11) * chim3(11) == 1 and chi4(5) * chim3(5) == -1, "chi_12 = chi_4 chi_-3")
    check(chi4(11) * chim3(11) == chi4(1) * chim3(1), "psi*phi is even: (psi phi)(-1) = +1")
    NS = 100000
    sig = [0] * (NS + 1)
    for d in range(1, NS + 1):
        fd = chim3(d)
        if fd:
            for kk in range(1, NS // d + 1):
                g = chi4(kk)
                if g:
                    sig[d * kk] += fd * g
    for p in primes:
        if p > NS:
            break
        if chi12(p) == -1:
            pe = p
            while pe <= NS:
                for n in range(pe, NS + 1, pe):
                    if (n // pe) % p:
                        check(sig[n] == 0, "two-character sum killed at chi_12(p) = -1, odd exponent")
                pe *= p * p
    dens = [sum(1 for n in range(1, X + 1) if sig[n]) / X for X in (10 ** 3, 10 ** 4, 10 ** 5)]
    check(dens[2] < dens[0], "two-character support density decreases (finite)")
    for b in (2, 3, 10):
        Kc = int(80 / math.log10(b)) + 5
        lhs = D(0)
        for m in range(1, Kc + 1):
            c = chim3(m)
            if c:
                lhs += c * D(b) ** m / (D(b) ** (2 * m) + 1)
        rhs = sum(D(sig[n]) / D(b) ** n for n in range(1, Kc + 1))
        check(abs(lhs - rhs) < TOL50, "sum chi_-3(m) b^m/(b^2m+1) = sum sigma(n) b^-n")
    N = 1500
    K = N + 70
    X2 = lambert_num(2, K, sig, 1)
    print("Two-character sum sigma = chi_4 * chi_-3 (psi*phi even, omega = chi_12 real): killed at p = 5, 7")
    print("  (mod 12) to odd powers; support densities " + " ".join("%.4f" % d for d in dens) +
          "; generating identity 50 digits;")
    print("  1 - D_%d(sum chi_-3(m) 2^m/(4^m+1); 2) = %.4f (finite data)." % (N, 1 - disc_N(X2, N)))


# ---------------------------------------------------------------------------
# E1. Uniform residue-class approximation for Erdos-Borwein
# ---------------------------------------------------------------------------


def section_E1(spf):
    header("E1. The 2^k decomposition of E_odd: complementary supports and the trade-off")
    NS = 200000
    todd = [0] * (NS + 1)
    for d in range(1, NS + 1, 2):
        for n in range(d, NS + 1, d):
            todd[n] += 1
    print("%3s %6s %10s %14s %8s" % ("k", "r", "S_k(N)/N", "supp(tau_r)/N", "sum"))
    for k in range(2, 13):
        q = 2 ** k
        half = 2 ** (k - 1)
        for r in (1, q - 1):
            tr = [0] * (NS + 1)
            for d in range(r, NS + 1, q):
                for n in range(d, NS + 1, d):
                    tr[n] += 1
            Sk = 0
            St = 0
            cover = True
            zeros_ok = True
            for n in range(1, NS + 1):
                ak = half * tr[n] - todd[n]
                nz_a = ak != 0
                nz_t = tr[n] != 0
                cover &= nz_a or nz_t
                if not nz_a:
                    zeros_ok &= todd[n] >= half
                Sk += nz_a
                St += nz_t
            check(cover, "complementary cover: n in supp(tau_r) or supp(a_k)")
            check(zeros_ok, "zeros of a_k need tau_odd(n) >= 2^(k-1)")
            print("%3d %6d %10.4f %14.4f %8.4f" % (k, r, Sk / NS, St / NS, (Sk + St) / NS))
    print("Every n <= %d lies in supp(tau_r) or supp(a_k) (exact), for all listed k, r." % NS)

    # concentration of A_{2^k - 1, 2^k}(2) for N <= 2^k
    print("\nConcentration of A_{2^k-1,2^k}(2): 1 - D_N <= 2^(N - 2^k)(1 + 2^(3-2^k)) for N <= 2^k:")
    for k in (5, 6, 7):
        q = 2 ** k
        Nmax = 16 * q
        K = Nmax + 80
        tr = [0] * (K + 1)
        for d in range(q - 1, K + 1, q):
            for n in range(d, K + 1, d):
                tr[n] += 1
        A = lambert_num(2, K, tr, 1)
        pts = A.points(Nmax)
        for N in range(1, q + 1):
            dN = disc(pts[:N])
            check(1 - dN <= 2.0 ** (N - q) * (1 + 2.0 ** (3 - q)) + 1e-12, "trivial concentration bound")
        vals = ["N=%d:%.4f" % (N, 1 - disc(pts[:N])) for N in (q // 2, q, 4 * q, 16 * q)]
        print("  k=%d: 1-D_N = %s" % (k, "  ".join(vals)))

    # fixed N, growing k: D_N(A_{2^k-1,2^k}) -> 1
    N = 50
    row = []
    for k in range(3, 9):
        q = 2 ** k
        K = max(N, 16 * q) + 80
        tr = [0] * (K + 1)
        for d in range(q - 1, K + 1, q):
            for n in range(d, K + 1, d):
                tr[n] += 1
        A = lambert_num(2, K, tr, 1)
        row.append((k, disc_N(A, N)))
    check(row[-1][1] > 0.999, "fixed N, k large: D_N -> 1")
    print("\nFixed N = 50, growing k: D_N(A_{2^k-1,2^k}) = " + ", ".join("k=%d:%.4f" % kv for kv in row))
    print("(for each fixed k the A_r track E_odd as N -> infinity; the two limits are never interchanged)")

    # model trade-off: k*(N) for the explicit bound with unit constants
    print("\nModel threshold k*(N): largest k with k (log N)^(-2^(2-k)) (k + log2 log N) < 1 (unit constants):")
    print("%10s %6s %22s" % ("lnlnN", "k*", "log2 lnlnN - log2 lnlnlnN"))
    for L2 in (5, 10, 20, 50, 100, 1000, 10 ** 4):
        kstar = 1
        for k in range(2, 80):
            val = k * math.exp(-L2 * 2.0 ** (2 - k)) * (k + L2 / math.log(2))
            if val < 1:
                kstar = k
        pred = math.log2(L2) - math.log2(math.log(L2))
        print("%10d %6d %22.2f" % (L2, kstar, pred))

    # sharp translation consistency at N = 2000 (from B2) is checked there.


# ---------------------------------------------------------------------------
# E2. E(b), E_odd(b), E(b^2)
# ---------------------------------------------------------------------------


def section_E2():
    header("E2. E(b) = E_odd(b) + E(b^2): identities, triangle constraints, base change")
    NM = 100000
    tau = tau_list(NM)
    todd = [0] * (NM + 1)
    for d in range(1, NM + 1, 2):
        for n in range(d, NM + 1, d):
            todd[n] += 1
    ok1 = ok2 = True
    for m in range(1, NM + 1):
        ok1 &= tau[m] == todd[m] + (tau[m // 2] if m % 2 == 0 else 0)
        s, i = 0, 0
        while m % (2 ** i) == 0:
            s += todd[m // 2 ** i]
            i += 1
        ok2 &= s == tau[m]
    check(ok1, "tau = tau_odd + tau(m/2)")
    check(ok2, "iterated identity")
    print("tau(m) = tau_odd(m) + [2|m] tau(m/2) and tau(m) = sum_i tau_odd(m/2^i), m <= %d (exact)." % NM)
    for b in (2, 3, 10):
        Kc = int(80 / math.log10(b)) + 5
        E = sum(D(1) / (D(b) ** m - 1) for m in range(1, Kc + 1))
        Eodd = sum(D(1) / (D(b) ** m - 1) for m in range(1, Kc + 1, 2))
        Eb2 = sum(D(1) / (D(b) ** (2 * m) - 1) for m in range(1, Kc + 1))
        dual = sum(D(b) ** j / (D(b) ** (2 * j) - 1) for j in range(1, Kc + 1))
        check(abs(E - Eodd - Eb2) < TOL50, "E = E_odd + E(b^2)")
        check(abs(Eodd - dual) < TOL50, "E_odd = sum b^j/(b^2j - 1)")
    print("E(b) = E_odd(b) + E(b^2) and E_odd(b) = sum_j b^j/(b^(2j)-1): 50 digits, b = 2, 3, 10.")

    # triangle constraints in base 2
    Nmax = 4000
    K = 2 * Nmax + 80
    tauK = tau_list(K)
    toddK = [0] * (K + 1)
    for d in range(1, K + 1, 2):
        for n in range(d, K + 1, d):
            toddK[n] += 1
    E = lambert_num(2, K, tauK, 1)
    Eo = lambert_num(2, K, toddK, 1)
    E4 = E - Eo
    pE, pO, p4 = E.points(Nmax), Eo.points(Nmax), E4.points(Nmax)
    print("%6s %10s %10s %10s" % ("N", "D(E)", "D(E_odd)", "D(E(4))"))
    for N in (500, 1000, 2000, 4000):
        u, v, w = 1 - disc(pE[:N]), 1 - disc(pO[:N]), 1 - disc(p4[:N])
        for x_, y_, z_ in ((u, v, w), (v, w, u), (w, u, v)):
            check(x_ <= y_ + z_ + 1e-9, "pseudometric triangle inequality")
        print("%6d %10.4f %10.4f %10.4f" % (N, 1 - u, 1 - v, 1 - w))
    print("Deficits 1-D_N of E, E_odd, E(4) satisfy every triangle inequality (exact consequence of")
    print("the sharp translation bound); no further constraint follows from the addition law (OP-01).")

    # base change: 1 - D_N(x; 4) <= 2 (1 - D_{2N}(x; 2))
    def base4_points(x2: Num, N: int) -> list[float]:
        return x2.points(2 * N)[::2]

    # c_{chi_4} by sieve
    c4 = [0] * (K + 1)
    for d in range(1, K + 1, 2):
        v = 1 if d % 4 == 1 else -1
        for n in range(d, K + 1, d):
            c4[n] += v
    L4 = lambert_num(2, K, c4, 1)
    for name, x in (("E", E), ("E_odd", Eo), ("L_chi4", L4)):
        for N in (250, 500, 1000, 2000):
            d4 = disc(base4_points(x, N))
            d2 = disc(x.points(2 * N))
            check(1 - d4 <= 2 * (1 - d2) + 1e-9, "base change inequality")
    # K_b strictly inside K_{b^k} for all k >= 2 via x = 1/(b^k - 1), and 1/(b+1) for k = 2
    for b_test in (2, 3, 5):
        for k_test in (2, 3):
            denom = b_test ** k_test - 1
            orb = [(b_test ** j) / denom for j in range(k_test)] * 30
            check(disc(orb) < 1 - 1e-6, "1/(b^k - 1) not in K_b")
            check(abs(disc([1 / denom] * 60) - 1) < 1e-9, "1/(b^k - 1) in K_{b^k}")
        orb2 = [1 / (b_test + 1), b_test / (b_test + 1)] * 50
        expected_d = 2 / 3 if b_test == 2 else (b_test - 1) / (b_test + 1)
        check(abs(disc(orb2) - expected_d) < 1e-9, "D_{2m}(1/(b+1); b) = max(2/(b+1), (b-1)/(b+1))")
    print("1 - D_N(x; 4) <= 2(1 - D_2N(x; 2)) for x = E, E_odd, L_chi4 at N = 250..2000; and")
    print("1/(b^k - 1) in K_{b^k} \\ K_b for b=2,3,5, k=2,3; D(1/(b+1); b) = 2/3 (b=2), (b-1)/(b+1) (b>=3).")

    # dyadic truncation: E^{(I)} = E(2) - E(2^(2^I))
    N = 2000
    print("\nDyadic truncation E^(I) = E(2) - E(2^(2^I)) (base 2, N = %d):" % N)
    dE = disc(pE[:N])
    for I in range(1, 7):
        step = 2 ** I
        tail = [0] * (K + 1)
        for n in range(step, K + 1, step):
            tail[n] = tauK[n // step]
        T = lambert_num(2, K, tail, 1)
        trunc = E - T
        dT = disc_N(T, N)
        dtr = disc_N(trunc, N)
        check(abs(dE - dtr) <= 1 - dT + 1e-9, "dyadic truncation transfer")
        print("  I=%d: 1 - D_N(E(2^(2^I))) = %.4f, |D_N(E) - D_N(E^(I))| = %.4f" % (I, 1 - dT, abs(dE - dtr)))


# ---------------------------------------------------------------------------
# E3. Classical logarithm synthesis
# ---------------------------------------------------------------------------


def section_E3():
    header("E3. ln 2: Stoneham splitting, residue splitting, formal collapse, prime denominators")
    ln2 = D(2).ln()
    for c in (3, 5, 7):
        alpha = sum(D(1) / (D(c) ** k * D(2) ** (c ** k)) for k in range(1, 8))
        Zc = sum(D(1) / (D(K) * D(2) ** K) for K in range(1, 400) if not is_power_of(K, c))
        check(abs(ln2 - alpha - Zc) < TOL50, "ln 2 = alpha_{2,c} + Z_c")
    print("ln 2 = alpha_{2,c} + Z_c with alpha_{2,c} = sum_k c^-k 2^-(c^k) (Stoneham), c = 3, 5, 7: 50 digits.")

    # prime denominators of chronological prefixes
    for N in (60, 120, 240):
        for c in (3, 5):
            P = sum((Fraction(1, K * 2 ** K) for K in range(1, N + 1) if not is_power_of(K, c)), Fraction(0))
            den = (P * 2 ** N).denominator
            while den % 2 == 0:
                den //= 2
            band = [p for p in primes_upto(N) if 2 * p > N and p != c]
            check(all(den % p == 0 for p in band), "every top-band prime divides the Z_c prefix denominator")
        for (M, r) in ((4, 1), (4, 3), (6, 1), (6, 5), (5, 2)):
            P = sum((Fraction(1, K * 2 ** K) for K in range(1, N + 1) if K % M == r), Fraction(0))
            den = (P * 2 ** N).denominator
            band = [p for p in primes_upto(N) if 2 * p > N and p % M == r]
            check(all(den % p == 0 for p in band), "residue piece retains its top-band primes")
    print("Odd parts of the prefix denominators 2^N P_N contain every prime p in (N/2, N] (p != c) for Z_c,")
    print("and every such p = r (mod M) for the residue pieces B_{r,M} (N = 60, 120, 240; exact).")

    # residue splitting closed forms
    half = D(1) / 2
    B = {}
    for (M, r) in ((2, 1), (2, 0), (4, 1), (4, 3)):
        B[(M, r)] = sum(half ** K / K for K in range(1, 400) if K % M == r)
    check(abs(B[(2, 1)] - D(3).ln() / 2) < TOL50, "B_{1,2} = (1/2) ln 3")
    check(abs(B[(2, 0)] - (D(4) / 3).ln() / 2) < TOL50, "B_{0,2} = (1/2) ln(4/3)")

    def atan_inv(n: int) -> Decimal:
        x = D(1) / n
        s, t, k = D(0), x, 0
        while abs(t) > D(10) ** -140:
            s += t / (2 * k + 1) * (1 if k % 2 == 0 else -1)
            t *= x * x
            k += 1
        return s

    pi = 16 * atan_inv(5) - 4 * atan_inv(239)
    atan_half = pi / 4 - atan_inv(3)
    check(abs(B[(4, 1)] - B[(4, 3)] - atan_half) < TOL50, "B_{1,4} - B_{3,4} = arctan(1/2)")
    check(abs(B[(4, 1)] + B[(4, 3)] - D(3).ln() / 2) < TOL50, "B_{1,4} + B_{3,4} = (1/2) ln 3")
    print("Residue pieces: B_{1,2} = (ln 3)/2, B_{0,2} = (ln 4/3)/2, B_{1,4} - B_{3,4} = arctan(1/2) (pi by Machin).")

    # ln 2 = -sum mu(m) ln E_{2^m}
    def mob(n):
        f = factor(n)
        if any(e > 1 for e in f.values()):
            return 0
        return -1 if len(f) % 2 else 1

    s = D(0)
    for m in range(1, 200):
        mu = mob(m)
        if mu:
            prod_ = D(1)
            for kk in range(1, 200 // m + 2):
                prod_ *= 1 - D(2) ** (-m * kk)
            s -= mu * prod_.ln()
    check(abs(s - ln2) < D(10) ** -55, "ln 2 = -sum mu(m) ln E_{2^m}")
    print("ln 2 = -sum_m mu(m) ln E_{2^m} with every E_{2^m} in K_2 (truncated at m < 200; 55 digits).")

    # transfer inequality D_N(ln 2) <= D_N(alpha_{2,3}) + 1 - D_N(Z_3)
    N = 2000
    K = N + 80
    # 2^K ln 2 = sum_j 2^(K-j)/j: with G guard bits each floor loses < 1, the tail
    # beyond J = K + G is < 2^(K+G-J) = 1, so |2^(K+G) ln 2 - S| < J + 2 < 2^G.
    G = 20
    J = K + G
    S = sum((2 ** (K + G)) // (j * 2 ** j) for j in range(1, J + 1))
    check(J + 2 < 2 ** G, "guard bits")
    lnx = Num(2, K, S >> G, 2)
    S_al = 0
    for k in range(1, 9):
        if 3 ** k <= K:
            S_al += Fraction(2 ** (K - 3 ** k), 3 ** k)
    S_al = Fraction(S_al)
    al = Num(2, K, S_al.numerator // S_al.denominator, 2)
    Z3 = lnx - al
    dl, da, dz = disc_N(lnx, N), disc_N(al, N), disc_N(Z3, N)
    check(dl <= da + (1 - dz) + 1e-9, "translation inequality for ln 2 = alpha + Z_3")
    print("Base 2, N = %d: D_N(ln 2) = %.4f, D_N(alpha_{2,3}) = %.4f, D_N(Z_3) = %.4f (finite data);" % (N, dl, da, dz))
    print("the inequality D_N(ln 2) <= D_N(alpha_{2,3}) + 1 - D_N(Z_3) holds and is uninformative here.")


def is_power_of(K: int, c: int) -> bool:
    if K < c:
        return False
    while K % c == 0:
        K //= c
    return K == 1


# ---------------------------------------------------------------------------


def main() -> int:
    t0 = time.time()
    EX = 2000
    spf = spf_sieve(200000)
    primes = primes_upto(200000)
    divs = [[] for _ in range(EX + 1)]
    for d in range(1, EX + 1):
        for n in range(d, EX + 1, d):
            divs[n].append(d)
    groups, _ = section_B1(spf, primes, divs)
    section_B3_sectors(spf, primes, groups)
    section_B2(spf, primes, divs)
    section_B2_disc()
    section_B3(spf, primes, groups)
    section_B4(spf, primes)
    section_E1(spf)
    section_E2()
    section_E3()
    print()
    print("All %d checks passed in %.1f s." % (CHECKS, time.time() - t0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
