#!/usr/bin/env python3
"""Phase 26 Track E: constructive normality, reciprocal spectra and the bounded-CF cap.

Exact finite certificates for notes/phase26/constructive-normality-and-reciprocal-spectra.md.

Every assertion that supports a stated theorem uses Python ints and fractions.Fraction only.
Floating point appears in exactly two places, both marked [finite]:
  * generating a *candidate* test function h for the transfer-operator certificates
    (the candidate is then rounded to exact rationals and every inequality is checked exactly);
  * descriptive numerical measurements (Hausdorff dimensions, eigenvalues) printed for context.

Run:  python -B scripts/phase26_constructive_spectra.py   (exit code 0 = all certificates pass)
"""
from fractions import Fraction as Fr
from math import gcd
import itertools
import sys
import time

COUNTS = {}


def tick(key, n=1):
    COUNTS[key] = COUNTS.get(key, 0) + n


def frac_part(x):
    return x - (x.numerator // x.denominator)


def circ(x):
    """distance to nearest integer, exact"""
    f = frac_part(x)
    return min(f, 1 - f)


def dec(q, k=4):
    """exact decimal rendering of a nonnegative Fraction, rounded to k places (no floats)"""
    n = round(Fr(q) * 10 ** k)
    return "%d.%0*d" % (n // 10 ** k, k, n % 10 ** k)


# ---------------------------------------------------------------------------
# polynomial helpers (integer coefficient lists, index = degree)
# ---------------------------------------------------------------------------
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def pdiv_exact(a, b):
    """exact division a / b in Z[u] (b monic up to sign), returns quotient; asserts remainder 0"""
    a = a[:]
    lb = len(b)
    q = [0] * (len(a) - lb + 1)
    for k in range(len(a) - lb, -1, -1):
        c, r = divmod(a[k + lb - 1], b[-1])
        assert r == 0
        q[k] = c
        for i, y in enumerate(b):
            a[i + k] -= c * y
    assert not any(a)
    return q


_CYC = {}


def Phi(d):
    if d not in _CYC:
        num = [-1] + [0] * (d - 1) + [1]
        for e in range(1, d):
            if d % e == 0:
                num = pdiv_exact(num, Phi(e))
        while num[-1] == 0:
            num.pop()
        _CYC[d] = num
    return _CYC[d]


def series_div(num, den, n):
    """power series num/den to n terms, den[0] = +-1"""
    out = [0] * n
    for j in range(n):
        v = num[j] if j < len(num) else 0
        for i in range(1, min(j, len(den) - 1) + 1):
            v -= den[i] * out[j - i]
        assert v % den[0] == 0
        out[j] = v // den[0]
    return out


def cyclotomic_G(plus, minus):
    """G = prod_{d in plus} Phi_d / prod_{d in minus} Phi_d as (num, den)"""
    num, den = [1], [1]
    for d in plus:
        num = pmul(num, Phi(d))
    for d in minus:
        den = pmul(den, Phi(d))
    return num, den


def peval(c, u):
    return sum(x * u ** i for i, x in enumerate(c))


# ---------------------------------------------------------------------------
# polynomial helpers over F_p (cyclotomic congruence theorem E1.3A)
# ---------------------------------------------------------------------------
def ptrim(a):
    a = a[:]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def pmod(a, p):
    return ptrim([c % p for c in a])


def ppow_mod(a, e, p):
    out, base = [1], pmod(a, p)
    while e:
        if e & 1:
            out = pmod(pmul(out, base), p)
        base = pmod(pmul(base, base), p)
        e >>= 1
    return out


def prem_mod(a, b, p):
    """remainder of a modulo b in F_p[u] (b nonzero)"""
    a, b = pmod(a, p), pmod(b, p)
    inv = pow(b[-1], -1, p)
    while len(a) >= len(b) and any(a):
        c, k = a[-1] * inv % p, len(a) - len(b)
        for i, y in enumerate(b):
            a[i + k] = (a[i + k] - c * y) % p
        a = ptrim(a)
        if len(b) == 1:
            return [0]
    return a


def pgcd_mod(a, b, p):
    """monic gcd in F_p[u]"""
    a, b = pmod(a, p), pmod(b, p)
    while any(b):
        a, b = b, prem_mod(a, b, p)
    inv = pow(a[-1], -1, p)
    return [c * inv % p for c in a]


def pderiv_mod(a, p):
    return pmod([i * a[i] for i in range(1, len(a))] or [0], p)


def phi_sub(m, w, neg):
    """coefficient list of Phi_m(u^w) (neg=False) or Phi_m(-u^w) (neg=True)"""
    c = Phi(m)
    out = [0] * ((len(c) - 1) * w + 1)
    for i, x in enumerate(c):
        out[i * w] = -x if (neg and i % 2) else x
    return out


def classified_g2(Dmax):
    """Exponent vectors {(d, eps_d)} allowed by Theorem E1.3A(2) with every index d <= Dmax:
    finite products over distinct odd m >= 3 of (Phi_m(v)/Phi_m(-v))^{+-1}, v = u^{2^{r-1}}, i.e.
    eps = +-(1, ..., 1, -1) on (m, 2m, ..., 2^r m)."""
    comps = []
    for m in range(3, Dmax + 1, 2):
        opts = [()]
        r = 1
        while 2 ** r * m <= Dmax:
            pat = tuple((2 ** k * m, 1) for k in range(r)) + ((2 ** r * m, -1),)
            opts += [pat, tuple((d, -e) for d, e in pat)]
            r += 1
        comps.append(opts)
    return {frozenset(x for pat in choice for x in pat) for choice in itertools.product(*comps)}


# ---------------------------------------------------------------------------
# E1.  Band-multiplier calculus, mod-g rigidity, fold multipliers
# ---------------------------------------------------------------------------
def e1_band_calculus():
    print("[E1] cyclotomic band-multiplier calculus")
    nterms = 72
    one_minus_u = [1, -1]
    combos = []
    ds = list(range(2, 13))
    for k in range(0, 4):
        for sub in itertools.combinations(ds, k):
            for signs in itertools.product((1, -1), repeat=k):
                plus = [d for d, e in zip(sub, signs) if e == 1]
                minus = [d for d, e in zip(sub, signs) if e == -1]
                combos.append((plus, minus))
    allowed2 = classified_g2(12)
    moduli = (2, 3, 4, 5, 6, 7, 8, 9, 12)
    trivial = {g: 0 for g in moduli}
    nontrivial = {g: 0 for g in moduli}
    for plus, minus in combos:
        num, den = cyclotomic_G(plus, minus)
        S = series_div(num, pmul(den, one_minus_u), nterms)      # S = G/(1-u)
        T = series_div(den, pmul(num, one_minus_u), nterms)      # T = 1/((1-u)G)
        # convolution identity S*T = (j+1)
        for j in range(nterms):
            assert sum(S[i] * T[j - i] for i in range(j + 1)) == j + 1
        tick("E1 S*T=(j+1) identities", nterms)
        # Part 1, mod-g rigidity: S_j = 1 mod g for all j  =>  T_j = 1 mod g for all j (no zero band)
        for g in moduli:
            if all((x - 1) % g == 0 for x in S):
                assert all((x - 1) % g == 0 for x in T)
                assert all(x != 0 for x in T)
                if not plus and not minus:
                    trivial[g] += 1
                else:
                    # Theorem E1.3A: nontrivial solutions occur only at g = 2, inside the classified family
                    assert g == 2
                    assert frozenset([(d, 1) for d in plus] + [(d, -1) for d in minus]) in allowed2
                    nontrivial[g] += 1
        tick("E1 cyclotomic factors G tested")
    print("   factors tested:", COUNTS["E1 cyclotomic factors G tested"],
          " rigidity instances: trivial G = 1", trivial, "; nontrivial", nontrivial)
    assert all(v == 1 for v in trivial.values()) and nontrivial[2] == 6 and sum(nontrivial.values()) == 6
    tick("E1 mod-g rigidity instances, trivial G = 1", sum(trivial.values()))
    tick("E1 mod-g rigidity instances, nontrivial (all at g = 2)", sum(nontrivial.values()))

    # Op(c,l) transient: T = 1/(1-u^c)  =>  S_j = min(j+1, c)
    for c in range(2, 9):
        num, den = [1] * c, [1]                        # G = Pi_c
        S = series_div(num, pmul(den, one_minus_u), 40)
        T = series_div(den, pmul(num, one_minus_u), 40)
        assert S == [min(j + 1, c) for j in range(40)]
        assert T == [1 if j % c == 0 else 0 for j in range(40)]
        tick("E1 Op(c,l) transient identities")

    # base-2 skip factor G = Phi_2 Phi_3 / Pi_4: S pattern (1,2,2,1), T pattern (1,0,1)
    num, den = pmul(Phi(2), Phi(3)), [1, 1, 1, 1]
    S = series_div(num, pmul(den, one_minus_u), 48)
    T = series_div(den, pmul(num, one_minus_u), 48)
    assert S == [(1, 2, 2, 1)[j % 4] for j in range(48)]
    assert T == [(1, 0, 1)[j % 3] for j in range(48)]
    tick("E1 base-2 skip factor (1,2,2,1)/(1,0,1)")

    # exact band tracking on actual rationals, BOTH coordinates (E1.2(a)), as a statement modulo 1:
    #   || b^n y G(u) - S_j {b^n y} || <= 2 C_G y b^{m-l},  || b^n x / G(u) - T_j {b^n x} || <= 2 C_{1/G} x b^{m-l}
    # for n = j l + m, 0 <= m < l (preperiod a = 0 here: all denominators are prime to b, P_y, P_x | l).
    cases = [(3, Fr(1, 13), 6, ([2, 3], [4])), (10, Fr(1, 7), 12, ([3], [])),
             (5, Fr(2, 31), 6, ([2], [])), (2, Fr(1, 3), 4, ([2, 3], [4])),
             (7, Fr(3, 19), 6, ([5], [2])), (3, Fr(2, 5), 8, ([6], [3])),
             (10, Fr(3, 7), 12, ([3, 4], [6])), (2, Fr(3, 5), 4, ([3], [4])),
             (5, Fr(3, 7), 6, ([2], [3]))]
    for b, y, l, (plus, minus) in cases:
        x = 1 / y
        for z in (y, x):
            assert gcd(z.denominator, b) == 1 and (pow(b, l, z.denominator) - 1) % z.denominator == 0  # period | l
        num, den = cyclotomic_G(plus, minus)
        nb = 10
        CG = max(abs(c) for c in series_div(num, den, 240))      # sup |g_i|  (coefficients of G)
        CH = max(abs(c) for c in series_div(den, num, 240))      # sup |h_i|  (coefficients of 1/G)
        S = series_div(num, pmul(den, one_minus_u), nb)
        T = series_div(den, pmul(num, one_minus_u), nb)
        u = Fr(1, b ** l)
        Gval = Fr(peval(num, u), peval(den, u))
        y1, x1 = y * Gval, x / Gval
        assert x1 * y1 == 1
        for j in range(nb):
            for m in range(l):
                n = j * l + m
                w = 2 * Fr(b ** m, b ** l)
                assert circ(b ** n * y1 - S[j] * frac_part(b ** n * y)) <= CG * y * w
                assert circ(b ** n * x1 - T[j] * frac_part(b ** n * x)) <= CH * x * w
                tick("E1 exact band-tracking positions (y and x sides)", 2)
    # the statement is modulo 1 only: Audit m1 wrap-around example b=3, x=2, G=1+u, l=4, n=1
    b, x, l, n = 3, Fr(2), 4, 1
    new = frac_part(b ** n * x / (1 + Fr(1, b ** l)))
    pred = frac_part(1 * frac_part(b ** n * x))                     # T_0 = 1
    assert new - pred == Fr(38, 41) and circ(new - pred) == Fr(3, 41) <= 2 * x * Fr(b ** 1, b ** l)
    tick("E1 wrap-around example (real difference 38/41, circle distance 3/41)")
    print("   band-tracking positions checked:", COUNTS["E1 exact band-tracking positions (y and x sides)"],
          "(y and x sides); wrap-around example: real difference 38/41, circle distance 3/41")

    # fold-band multipliers: {i m mod P} = g Z/P with g = gcd(m, P); always contains t = 0
    for P in range(1, 40):
        for m in range(1, 60):
            g = gcd(m, P)
            assert {(i * m) % P for i in range(P)} == set(range(0, P, g))
            assert 0 in {(i * m) % P for i in range(P)}
            tick("E1 fold-offset subgroup checks")
    # fold multiplier identity b^{im+s}F + b^s F = (1 + b^{im}) b^s F, mod-D effect for D | b-1
    for b in (3, 4, 7, 10):
        for D in [d for d in range(2, b) if (b - 1) % d == 0]:
            for t in range(0, 6):
                assert (1 + b ** t) % D == 2 % D
                tick("E1 fold multiplier = 2 mod D (D | b-1)")


def e1_cyclotomic_congruence():
    """Theorem E1.3A.  (1) g >= 3 and G = 1 (mod g)  =>  G = 1.  (2) classification of G = 1 (mod 2).
    The proof is the paper proof in the note; here: its three ingredients and an exhaustive search."""
    print("[E1] Theorem E1.3A: cyclotomic congruence (G = 1 is the only solution for g >= 3)")
    # (i) Phi_{p^k m} = Phi_m^{(p-1) p^{k-1}} in F_p[u] for p not dividing m, k >= 1
    for p in (2, 3, 5, 7):
        for k in (1, 2, 3):
            for m in range(1, 61):
                if m % p == 0 or p ** k * m > 120:
                    continue
                assert pmod(Phi(p ** k * m), p) == ppow_mod(Phi(m), (p - 1) * p ** (k - 1), p)
                tick("E1.3A Frobenius congruences Phi_{p^k m} = Phi_m^{(p-1)p^{k-1}} mod p")
    # negative controls for the F_p gcd routine: p | m breaks coprimality and squarefreeness
    assert pgcd_mod(Phi(6), Phi(3), 2) == pmod(Phi(3), 2)              # Phi_6 = Phi_3 (mod 2)
    assert pgcd_mod(Phi(15), Phi(5), 3) == pmod(Phi(5), 3)             # Phi_15 = Phi_5^2 (mod 3)
    assert pgcd_mod(Phi(15), pderiv_mod(Phi(15), 3), 3) != [1]          # not squarefree mod 3
    tick("E1.3A negative controls for the F_p gcd routine", 3)
    # (ii) the Phi_m with p not dividing m are squarefree and pairwise coprime in F_p[u]
    for p in (2, 3, 5, 7):
        ms = [m for m in range(1, 41) if m % p]
        for i, m in enumerate(ms):
            f = pmod(Phi(m), p)
            assert pgcd_mod(f, pderiv_mod(f, p), p) == [1]
            for m2 in ms[i + 1:]:
                assert pgcd_mod(f, Phi(m2), p) == [1]
                tick("E1.3A pairwise coprimality checks of Phi_m, Phi_m' mod p")
            tick("E1.3A squarefreeness checks of Phi_m mod p")
    # (iii) odd m >= 3: Phi_m = P_m(u^2) + u Q_m(u^2) with Q_m != 0 mod 2 and deg(u Q_m(u^2)) < phi(m),
    #       so R_m = (u Q_m(u^2)/Phi_m(u))^{2^{r-1}} mod 2 is a nonzero proper fraction (it has a pole)
    for m in range(3, 100, 2):
        c = Phi(m)
        assert (len(c) - 1) % 2 == 0 and any(c[i] % 2 for i in range(1, len(c), 2))
        assert pgcd_mod(c, pderiv_mod(c, 2), 2) == [1]
        tick("E1.3A odd parts Q_m nonzero mod 2 (m odd)")
    # (iv) exhaustive: all 3^9 exponent vectors on d = 2..10; G = A/B, and G = 1 (mod q) iff A = B (mod q)
    ds = list(range(2, 11))
    moduli = (2, 3, 4, 5, 6, 7, 8, 9, 12)
    hits = {q: set() for q in moduli}

    def rec(i, A, B, eps):
        if i == len(ds):
            L = max(len(A), len(B))
            diff = [(A[k] if k < len(A) else 0) - (B[k] if k < len(B) else 0) for k in range(L)]
            for q in moduli:
                if all(c % q == 0 for c in diff):
                    hits[q].add(frozenset((d, e) for d, e in zip(ds, eps) if e))
            tick("E1.3A exhaustive exponent vectors on d = 2..10")
            return
        d = ds[i]
        rec(i + 1, A, B, eps + (0,))
        rec(i + 1, pmul(A, Phi(d)), B, eps + (1,))
        rec(i + 1, A, pmul(B, Phi(d)), eps + (-1,))
    rec(0, [1], [1], ())
    for q in moduli:
        if q >= 3:
            assert hits[q] == {frozenset()}, q
    assert hits[2] == classified_g2(10) and len(hits[2]) == 9
    for vec in hits[2]:                       # cross-check through the multipliers themselves
        num, den = cyclotomic_G([d for d, e in vec if e == 1], [d for d, e in vec if e == -1])
        S = series_div(num, pmul(den, [1, -1]), 120)
        T = series_div(den, pmul(num, [1, -1]), 120)
        assert all(x % 2 == 1 for x in S) and all(x % 2 == 1 for x in T)
    print("   %d exponent vectors: G = 1 (mod q) only for G = 1 when q in %s; %d classified solutions mod 2"
          % (COUNTS["E1.3A exhaustive exponent vectors on d = 2..10"], [q for q in moduli if q >= 3], len(hits[2])))


def cycle_mean_exact(z, b, maxP=10 ** 6):
    """exact cycle mean of ||b^n z|| for rational z with denominator prime to b; returns (mean, period)"""
    N, D = z.numerator, z.denominator
    assert gcd(D, b) == 1
    r0 = N % D
    r, tot, P = r0, 0, 0
    while True:
        tot += min(r, D - r)
        r, P = r * b % D, P + 1
        if r == r0:
            return Fr(tot, P * D), P
        assert P < maxP


def cycle_dist_mean(z, b, c, maxP=10 ** 6):
    """exact cycle mean of ||b^n z - c||"""
    N, D = z.numerator, z.denominator
    assert gcd(D, b) == 1
    r0 = N % D
    r, tot, P = r0, Fr(0), 0
    while True:
        tot += circ(Fr(r, D) - c)
        r, P = r * b % D, P + 1
        if r == r0:
            return tot / P
        assert P < maxP


def e1_g2_example():
    """Example E1.3B (Audit M1): b = 3, D = 2, G = Phi_6/Phi_3 preserves delta_{1/2} on every band, yet the
    exact cycle mean of x contracts at three consecutive scales."""
    print("[E1] Example E1.3B: b=3, G = Phi_6/Phi_3, y0 = 5/2 (law delta_1/2), x0 = 2/5")
    num, den = cyclotomic_G([6], [3])
    assert num == [1, -1, 1] and den == [1, 1, 1]
    S = series_div(num, pmul(den, [1, -1]), 120)
    T = series_div(den, pmul(num, [1, -1]), 120)
    assert S == [(1, -1, 1, 1, -1, 1)[j % 6] for j in range(120)]
    assert T == [(1, 3, 5, 5, 3, 1)[j % 6] for j in range(120)]
    assert all(frac_part(s * Fr(1, 2)) == Fr(1, 2) for s in S)     # (x S_j) fixes delta_{1/2} on every band
    assert all(t % 2 == 1 for t in T)                              # Part 1: T_j odd, no zero band
    tick("E1.3B multiplier patterns S = (1,-1,1,1,-1,1), T = (1,3,5,5,3,1)")
    y0, x0 = Fr(5, 2), Fr(2, 5)
    assert all(frac_part(3 ** n * y0) == Fr(1, 2) for n in range(12))    # cycle law of y0 is delta_{1/2}
    M0, P0 = cycle_mean_exact(x0, 3)
    assert (M0, P0) == (Fr(3, 10), 4)
    # error-free band calculus: x3 preserves the cycle law of x0, x5 sends it to 0
    orb = {frac_part(3 ** n * x0) for n in range(4)}
    assert {frac_part(3 * t) for t in orb} == orb and {frac_part(5 * t) for t in orb} == {0}
    tick("E1.3B error-free band laws (x3 fixes sigma_x0, x5 kills it)")
    for sched, targets in (((8, 48, 288), ("0.1975", "0.1590", "0.1401")), ((12, 72), ("0.1983", "0.1505"))):
        y, x, M = y0, x0, M0
        line = ["0.3000"]
        for l, tgt in zip(sched, targets):
            # band-calculus hypotheses: x, y purely periodic with P_x, P_y | l
            assert pow(3, l, x.denominator) == 1 and pow(3, l, y.denominator) == 1
            u = Fr(1, 3 ** l)
            y = y * Fr(peval(num, u), peval(den, u))
            x = 1 / y
            Mn, P = cycle_mean_exact(x, 3)
            assert Mn < M and abs(Mn - Fr(tgt)) < Fr(1, 20000)
            dy = cycle_dist_mean(y, 3, Fr(1, 2))
            line.append("%s (l=%d, P_x=%d, factor %s, mean |3^n y - 1/2| = %s)" % (dec(Mn), l, P, dec(Mn / M), dec(dy)))
            M = Mn
            tick("E1.3B exact contraction steps (cycle mean of x strictly decreases)")
        print("   M(x): " + " -> ".join(line))


def e1_b3_power_search():
    """Finite certificate: within the classified g = 2 family (Theorem E1.3A(2)), with at most two components,
    odd m <= 15 and r <= 3, no factor has every S_j a power of 3."""
    print("[E1] b = 3: classified g = 2 factors with every S_j a power of 3 (finite search)")

    def is_pow3(v):
        if v <= 0:
            return False
        while v % 3 == 0:
            v //= 3
        return v == 1
    comps = [(m, r, s) for m in (3, 5, 7, 9, 11, 13, 15) for r in (1, 2, 3) for s in (1, -1)]
    for k in (1, 2):
        for combo in itertools.combinations(comps, k):
            if len({c[0] for c in combo}) < k:
                continue
            num, den = [1], [1]
            for m, r, s in combo:
                a, c = phi_sub(m, 2 ** (r - 1), False), phi_sub(m, 2 ** (r - 1), True)
                num, den = (pmul(num, a), pmul(den, c)) if s == 1 else (pmul(num, c), pmul(den, a))
            S = series_div(num, pmul(den, [1, -1]), 400)
            assert all(v % 2 == 1 for v in S)
            assert any(not is_pow3(v) for v in S)          # explicit witness band
            tick("E1.3 b=3 classified g=2 factors with a non-power-of-3 multiplier")
    print("   factors searched:", COUNTS["E1.3 b=3 classified g=2 factors with a non-power-of-3 multiplier"],
          "; none has every S_j in 3^N")


def e1_fold_mass_bound():
    """Lemma E1.3C(a): with B the closed eta-ball about r/D, eta < 1/(3D), p = sigma(B) and 0 < rho < 1/3,
    a fold moves near-r/D mass:  ((1-rho) sigma + rho nu_F)(B) <= p - rho (3p - 2).
    (i) coprime folds, nu_F = sigma * sigma, on discrete measures concentrated near r/D;
    (ii) every offset t (nu_F = law of z + T_b^t z) on cycle laws of actual rationals."""
    print("[E1] Lemma E1.3C: fold union bound p' <= p - rho(3p - 2)")
    rhos = (Fr(1, 10), Fr(1, 4), Fr(1, 3))
    for b, D in ((3, 2), (4, 3), (7, 3), (7, 6), (10, 3), (10, 9)):
        eta = Fr(1, 4 * D)
        for r in sorted({1, D - 1}):
            c = Fr(r, D)

            def inB(t):
                return circ(t - c) <= eta
            near = [c + k * eta / 5 for k in range(-5, 6)]
            far = [Fr(0), c + Fr(1, 2 * D), c - Fr(2, 5 * D), Fr(1, 2)]
            for pat in range(12):
                pts = near[pat % 11:] + near[:pat % 11][:3] + far[: pat % 5]
                wts = [Fr(1 + (7 * i + pat) % 5, 1) for i in range(len(pts))]
                tot = sum(wts)
                wts = [w / tot for w in wts]
                p = sum(w for t, w in zip(pts, wts) if inB(t))
                conv = sum(w1 * w2 for t1, w1 in zip(pts, wts) for t2, w2 in zip(pts, wts) if inB(t1 + t2))
                for rho in rhos:
                    assert (1 - rho) * p + rho * conv <= p - rho * (3 * p - 2)
                    tick("E1.3C fold union-bound instances")
            for Q in (D * 5 + 1, D * 7 - 1, D * 11 + 1, 4 * D + 3):
                if gcd(Q, b) != 1:
                    continue
                for A in range(1, Q):
                    orbit = [frac_part(Fr(A * b ** n, Q)) for n in range(Q)]
                    P = next(n for n in range(1, Q + 1) if orbit[n % Q] == orbit[0]) if Q > 1 else 1
                    cyc = orbit[:P]
                    p = Fr(sum(1 for t in cyc if inB(t)), P)
                    for t in range(P):
                        mass = Fr(sum(1 for i in range(P) if inB(cyc[i] + cyc[(i + t) % P])), P)
                        for rho in rhos:
                            assert (1 - rho) * p + rho * mass <= p - rho * (3 * p - 2)
                    tick("E1.3C fold union-bound cycle laws (all offsets t)")
    print("   instances:", COUNTS["E1.3C fold union-bound instances"], "discrete-measure coprime folds;",
          COUNTS["E1.3C fold union-bound cycle laws (all offsets t)"], "actual cycle laws with every offset t")


def e1_kpower_bookkeeping():
    print("[E1] simultaneous radix b^k bookkeeping (k | L keeps every period coprime to k)")
    for k in (2, 3, 4, 5, 6, 12):
        PC, PF = 1, 1                    # seeds x0 = y0 = 1, both period one
        for step in range(4):
            L0 = 1
            while gcd(PC, k * L0) != 1 or k * L0 < 2:
                L0 += 1
            L = k * L0                    # L >= 2, coprime to P_C, divisible by k
            e, a, j = 2, 3, 0
            d = (L * PF) ** e
            while True:
                m = PC * (1 + j * L * PF)
                if m > d + a:
                    break
                j += 1
            q = m + d
            assert gcd(m, d) == 1 and gcd(q, m * PF) == 1
            assert gcd(q, k) == 1 and gcd(m * PF, k) == 1
            tick("E1 b^k period-coprimality steps")
            # the cut coordinate (period | q) is folded next; the folded one (period | m P_F) is cut next
            PC, PF = m * PF, q
            assert gcd(PC, PF) == 1 and gcd(PC, k) == 1 and gcd(PF, k) == 1
    # E1.5(2): on each progression n = i m + s = r' (mod k) the fold pair ((im+s) mod P_F, s mod P_F)
    # is still uniform on (Z/P_F)^2, using only gcd(m, P_F) = gcd(k, P_F) = 1
    for k in (2, 3, 4, 5, 6):
        for PF in range(1, 13):
            if gcd(PF, k) != 1:
                continue
            for m in range(1, 13):
                if gcd(m, PF) != 1:
                    continue
                for rr in range(k):
                    cnt = {}
                    for i in range(PF):
                        for s in range(k * PF):
                            if (i * m + s) % k == rr:
                                key = ((i * m + s) % PF, s % PF)
                                cnt[key] = cnt.get(key, 0) + 1
                    assert len(cnt) == PF * PF and set(cnt.values()) == {1}
                    tick("E1.5 progression fold-pair uniformity checks")


# ---------------------------------------------------------------------------
# E2.  Transfer-operator identities and certificates
# ---------------------------------------------------------------------------
def convergents(word):
    p1, p0, q1, q0 = 1, 0, 0, 1          # p_{-1}, p_0, q_{-1}, q_0
    for a in word:
        p1, p0 = p0, a * p0 + p1
        q1, q0 = q0, a * q0 + q1
    return p0, q0, p1, q1                # p_L, q_L, p_{L-1}, q_{L-1}


def e2_identities():
    print("[E2] transfer identity, reversal identity, supermultiplicativity")
    for M in (2, 3, 4):
        for L in range(1, 7):
            words = list(itertools.product(range(1, M + 1), repeat=L))
            # (L_s^L 1)(1) with L_s f(x) = sum_a (a+x)^-2s f(1/(a+x)), exact for 2s in {1, 2, 3}
            for e in (1, 2, 3):
                lhs = sum(Fr(1, (q + p) ** e) for p, q, _, _ in map(convergents, words))

                def LL(x, depth):
                    if depth == 0:
                        return Fr(1)
                    return sum(Fr(1) / (a + x) ** e * LL(1 / (a + x), depth - 1) for a in range(1, M + 1))
                if M ** L <= 1100:
                    assert lhs == LL(Fr(1), L)
                    tick("E2 exact transfer identities Sigma(M,L,s) = (L_s^L 1)(1), 2s in {1,2,3}")
            A = sorted(q + p for p, q, _, _ in map(convergents, words))
            B = sorted(q + q1 for _, q, _, q1 in map(convergents, words))
            assert A == B
            tick("E2 reversal multiset identities {q+p} = {q+q'}")
    for v in itertools.product(range(1, 6), repeat=3):
        for w in itertools.product(range(1, 6), repeat=2):
            pv, qv, _, _ = convergents(v)
            pw, qw, _, _ = convergents(w)
            pvw, qvw, _, _ = convergents(v + w)
            assert qvw + pvw <= (qv + pv) * (qw + pw)
            tick("E2 supermultiplicativity (q+p)(vw) <= (q+p)(v)(q+p)(w)")


def iroot(n, k):
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // pow(x, k - 1)) // k
        if y >= x:
            break
        x = y
    while pow(x, k) > n:
        x -= 1
    while pow(x + 1, k) <= n:
        x += 1
    return x


def pow_bounds(K, n, P, Q, Dbits=56):
    """rationals lo <= (K/n)^(P/Q) <= hi"""
    D = 1 << Dbits
    num = (D ** Q) * (K ** P)
    den = n ** P
    lo = iroot(num // den, Q)
    hi = iroot(-(-num // den), Q) + 1
    assert pow(lo, Q) * den <= num <= pow(hi, Q) * den
    return Fr(lo, D), Fr(hi, D)


def candidate_h(M, s_float, K, iters=300):
    """[finite] float power iteration on a piecewise-linear grid: candidate only."""
    xs = [i / K for i in range(K + 1)]
    h = [1.0] * (K + 1)

    def ev(hh, y):
        t = y * K
        j = min(int(t), K - 1)
        f = t - j
        return hh[j] * (1 - f) + hh[j + 1] * f
    lam = 1.0
    for _ in range(iters):
        nh = [sum((a + x) ** (-2 * s_float) * ev(h, 1 / (a + x)) for a in range(1, M + 1)) for x in xs]
        lam = nh[0] / h[0]
        h = [v / nh[0] for v in nh]
    return h, lam


def transfer_certificate(M, s, K, lam, lower):
    """Exact check of L_s h >= lam h (lower) or L_s h <= lam h (upper) on [0,1] for a
    decreasing piecewise-linear h with rational node values, L_s f(x)=sum_a (a+x)^{-2s} f(1/(a+x))."""
    P, Q = (2 * s).numerator, (2 * s).denominator
    hf, lam_float = candidate_h(M, float(s), K)
    H = [Fr(round(v * 10 ** 12), 10 ** 12) for v in hf]   # exact rationals from here on
    for i in range(K):
        assert H[i] > H[i + 1] > 0

    def hev(y):
        t = y * K
        j = min(t.numerator // t.denominator, K - 1)
        f = t - j
        return H[j] * (1 - f) + H[j + 1] * f
    cache = {}

    def pb(n):
        if n not in cache:
            cache[n] = pow_bounds(K, n, P, Q)
        return cache[n]
    for i in range(K):
        if lower:
            # x in [x_i, x_{i+1}]: (a+x)^{-2s} >= (a+x_{i+1})^{-2s}, h(1/(a+x)) >= h(1/(a+x_i)), h(x) <= h(x_i)
            lhs = sum(pb(a * K + i + 1)[0] * hev(Fr(K, a * K + i)) for a in range(1, M + 1))
            assert lhs >= lam * H[i], (M, s, i)
        else:
            lhs = sum(pb(a * K + i)[1] * hev(Fr(K, a * K + i + 1)) for a in range(1, M + 1))
            assert lhs <= lam * H[i + 1], (M, s, i)
        tick("E2 exact transfer-operator interval inequalities")
    return H, lam_float


def e2_caps():
    print("[E2] lowered caps: lower certificates Sigma(M,L,s) > 1")
    results = {}
    for (M, s, K, lam, regime) in [(14, Fr(18, 19), 1500, Fr(501, 500), "A (elementary, s>17/18)"),
                                   (8, Fr(46, 51), 1500, Fr(1003, 1000), "B (Weil-Estermann, s>9/10)")]:
        t0 = time.time()
        H, lf = transfer_certificate(M, s, K, lam, lower=True)
        ratio = H[K] / H[0]                       # h(1)/max h
        L = 2
        while lam ** L * ratio <= 1:
            L += 2
        # Sigma(M,L,s) = (L_s^L 1)(1) >= lam^L h(1)/h(0) > 1
        assert lam ** L * ratio > 1 and L % 2 == 0
        results[M] = (s, L)
        print("   M=%d s=%s regime %s: certified lam=%s, even L=%d, lam^L h(1)/h(0) > 1  [%.1fs]"
              % (M, s, regime, lam, L, time.time() - t0))
        tick("E2 lowered-cap certificates")
    print("[E2] barrier: upper certificates Sigma(M,L,s) <= lam^L < 1 for every L")
    for (M, s, K, lam, label) in [(7, Fr(9, 10), 400, Fr(99, 100), "Regime B cannot use M<=7"),
                                  (12, Fr(17, 18), 400, Fr(199, 200), "Regime A cannot use M<=12"),
                                  (4, Fr(5, 6), 200, Fr(19, 20), "no Kloosterman exponent rho>=0 reaches M<=4")]:
        H, lf = transfer_certificate(M, s, K, lam, lower=False)
        assert lam < 1
        print("   M=%d s=%s: L_s h <= %s h  => Sigma <= %s^L < 1 for all L (%s)" % (M, s, lam, lam, label))
        tick("E2 barrier certificates")
    return results


def e2_lp_and_parameters(results):
    print("[E2] LP threshold s*(rho) = (5-rho)/(2(3-rho)) and midpoint parameters")
    def sstar(rho):
        return (5 - rho) / (2 * (3 - rho))
    assert sstar(Fr(3, 4)) == Fr(17, 18) and sstar(Fr(1, 2)) == Fr(9, 10) and sstar(Fr(0)) == Fr(5, 6)
    for k in range(0, 100):
        r1, r2 = Fr(k, 100), Fr(k + 1, 100)
        assert sstar(r1) < sstar(r2)
        # feasibility boundary of (2.5): 2(1-s)/(1-rho) < s - 1/2  <=>  s > s*(rho)
        s = sstar(r1)
        assert 2 * (1 - s) / (1 - r1) == s - Fr(1, 2)
        tick("E2 LP threshold checks")
    for (s, rho) in [(results[8][0], Fr(1, 2)), (results[14][0], Fr(3, 4))]:
        alpha = (2 * (1 - s) / (1 - rho) + s - Fr(1, 2)) / 2
        beta = (1 + 2 * s - 6 * alpha) / 8
        for r in (1, 2, 3, 7):
            theta = Fr(0) if r == 1 else min(Fr(2, 3) * (s - 2 * alpha - 2 * beta), (1 - rho) * alpha - 2 * (1 - s)) / 2
            ineq = [2 * alpha + 4 * beta > 1, 2 * alpha + 2 * beta + Fr(3, 2) * theta < s,
                    1 - s - (1 - rho) / 2 * alpha + theta / 2 < 0, 4 * alpha + 2 * beta > 1, 2 * alpha > theta,
                    alpha > 0, beta > 0, (theta > 0) == (r >= 2)]
            assert all(ineq), (s, rho, r)
            mlin = 2 * alpha + 4 * beta - 1
            mA = s - 2 * alpha - 2 * beta - Fr(3, 2) * theta
            mB = (1 - rho) / 2 * alpha - (1 - s) - theta / 2
            eta = min(mlin, mA / 2, mB / 4) if r == 1 else min(mlin, 2 * alpha * s, s * theta / (r - 1), mA / 2, mB / 4)
            assert eta > 0
            tick("E2 (2.5) parameter certificates")
        print("   s=%s rho=%s: alpha=%s beta=%s, all five (2.5) inequalities exact for r=1,2,3,7" % (s, rho, alpha, beta))


def e2_G1_regression():
    print("[E2/E3] Audit IV G1: zero-weight regression and the D^Q >= B^P fix (M=30, L=2, s=10/11)")
    M, s = 30, Fr(10, 11)
    P, Q = (2 * s).numerator, (2 * s).denominator
    Ns = [a1 * a2 + 1 + a2 for a1 in range(1, M + 1) for a2 in range(1, M + 1)]
    B = max(Ns)
    assert B == 931

    def weights(D):
        cache = {}
        out = []
        for N in Ns:
            if N not in cache:
                cache[N] = iroot(D ** Q // N ** P, Q)
            out.append(cache[N])
        return out
    a = weights(14200)
    zeros = sum(1 for x in a if x == 0)
    assert sum(a) > 14200 and zeros == 461
    tick("E3 G1 regression (naive rule halts with zero weights)")
    Dstar = iroot(B ** P, Q)
    if Dstar ** Q < B ** P:
        Dstar += 1
    assert Dstar ** Q >= B ** P and (Dstar - 1) ** Q < B ** P
    a2 = weights(Dstar)
    assert min(a2) >= 1 and sum(a2) > Dstar
    for N, x in zip(Ns, a2):
        # p_u = a/T < a/D <= N^{-2s}
        assert x ** Q * N ** P <= Dstar ** Q
    tick("E3 G1 fix: all weights positive and Frostman-admissible")
    print("   naive D=14200: sum a_N=%d > D with %d/900 zero weights; fixed D*=%d: all 900 weights >= 1"
          % (sum(a), zeros, Dstar))


def e3_complexity(results):
    print("[E3] alphabet and constant sizes")
    rows = [(100, 52), (42, 4), (14, 4), (30, 2), (14, results[14][1]), (8, results[8][1])]
    for M, L in rows:
        children = M ** L
        pL, qL, _, _ = convergents([M] * L)
        BML = qL + pL
        assert BML <= 2 * (M + 1) ** L
        print("   M=%3d L=%4d: children per selection step = M^L has %d digits; B_{M,L} has %d digits"
              % (M, L, len(str(children)), len(str(BML))))
        tick("E3 size computations")


# ---------------------------------------------------------------------------
# E5.  Toeplitz determinants
# ---------------------------------------------------------------------------
def det(Mx):
    n = len(Mx)
    A = [row[:] for row in Mx]
    d = Fr(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for k in range(c, n):
                A[r][k] -= f * A[c][k]
    return d


def toeplitz(coef, r):
    return [[coef(i - j) for j in range(r)] for i in range(r)]


def exp_upper(x, N=30):
    """rational upper bound for exp(x), 0 <= x <= 1"""
    s = sum(Fr(x) ** k / Fr(prod(k)) for k in range(N + 1))
    return s + 3 * Fr(x) ** (N + 1) / prod(N + 1)


def exp_lower(x, N=30):
    return sum(Fr(x) ** k / Fr(prod(k)) for k in range(N + 1))


def prod(k):
    out = 1
    for i in range(2, k + 1):
        out *= i
    return out


def e5_toeplitz():
    print("[E5] Toeplitz Gram identities")
    for alpha in (Fr(0), Fr(1, 7), Fr(1, 2), Fr(5, 7), Fr(99, 100)):
        for r in range(1, 11):
            G = toeplitz(lambda k: Fr(1) if k == 0 else alpha, r)
            assert det(G) == (1 - alpha) ** (r - 1) * (1 + (r - 1) * alpha)
            tick("E5 det G_r = (1-a)^{r-1}(1+(r-1)a)")
    # orbit of 1/3 under T_2 = {1/3, 2/3}: coefficients cos(2 pi k/3) in {1, -1/2}
    pi3 = lambda k: Fr(1) if k % 3 == 0 else Fr(-1, 2)
    U3 = lambda k: Fr(1) if k % 3 == 0 else Fr(0)
    for r in range(1, 10):
        assert (det(toeplitz(pi3, r)) == 0) == (r >= 3)
        assert (det(toeplitz(U3, r)) == 0) == (r >= 4)
        for c0 in (Fr(1, 5), Fr(1, 2)):
            for c1 in (Fr(0), (1 - c0) / 2, 1 - c0):
                c2 = 1 - c0 - c1
                mix = lambda k: c1 * pi3(k) + c2 * U3(k) + (c0 if k == 0 else 0)
                assert det(toeplitz(mix, r)) >= c0 ** r
                tick("E5 mixture determinant >= c0^r")
    # determinant <-> weighted L^2 Fourier mass: exp(-2F) <= det T_r <= exp(-F/2) when F <= 1/8
    for base in (pi3, U3, lambda k: Fr(1)):
        for t in (Fr(1, 40), Fr(1, 80), Fr(1, 200)):
            for r in (2, 3, 4, 5):
                nu = lambda k: Fr(1) if k == 0 else t * base(k)
                F = sum((r - k) * nu(k) ** 2 for k in range(1, r))
                if F > Fr(1, 8):
                    continue
                d = det(toeplitz(nu, r))
                assert d * exp_upper(F / 2) <= 1          # det <= exp(-F/2)
                assert d * exp_lower(2 * F) >= 1          # det >= exp(-2F)
                for k in range(1, r):                     # Fischer: det T_r <= 1 - |nu^(k)|^2
                    assert d <= 1 - nu(k) ** 2
                tick("E5 determinant-L2 sandwich instances")
    # complex, non-symmetric measures: nu = (1-t) lambda + t pi with pi on (1/4)Z/Z, w_1 != w_3, so the
    # coefficients pi^(k) = sum_a w_a (-i)^{ak} lie in Q(i) and T_r(nu) is Hermitian, not real symmetric
    unit = [(Fr(1), Fr(0)), (Fr(0), Fr(-1)), (Fr(-1), Fr(0)), (Fr(0), Fr(1))]     # (-i)^j, j mod 4
    for w in ((Fr(1, 2), Fr(1, 4), Fr(1, 8), Fr(1, 8)), (Fr(0), Fr(1), Fr(0), Fr(0)),
              (Fr(1, 3), Fr(1, 2), Fr(0), Fr(1, 6)), (Fr(1, 10), Fr(3, 5), Fr(1, 5), Fr(1, 10))):
        assert sum(w) == 1 and w[1] != w[3]
        for t in (Fr(1, 10), Fr(1, 20), Fr(1, 40), Fr(1, 80), Fr(1, 200)):
            def nuq(k):
                if k == 0:
                    return (Fr(1), Fr(0))
                re = t * sum(wa * unit[(a * k) % 4][0] for a, wa in enumerate(w))
                im = t * sum(wa * unit[(a * k) % 4][1] for a, wa in enumerate(w))
                return (re, im)
            for r in (2, 3, 4, 5, 6):
                F = sum((r - k) * (nuq(k)[0] ** 2 + nuq(k)[1] ** 2) for k in range(1, r))
                if F > Fr(1, 8):
                    continue
                Mx = [[nuq(i - j) for j in range(r)] for i in range(r)]
                assert any(Mx[i][j][1] != 0 for i in range(r) for j in range(r))       # genuinely complex
                assert all(Mx[i][j] == (Mx[j][i][0], -Mx[j][i][1]) for i in range(r) for j in range(r))
                dre, dim = qdet(Mx)
                assert dim == 0                                   # Hermitian => real determinant
                assert dre * exp_upper(F / 2) <= 1 and dre * exp_lower(2 * F) >= 1
                for k in range(1, r):
                    assert dre <= 1 - (nuq(k)[0] ** 2 + nuq(k)[1] ** 2)
                tick("E5 complex non-symmetric sandwich + Fischer instances")


def qmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def qdiv(a, b):
    n = b[0] ** 2 + b[1] ** 2
    return ((a[0] * b[0] + a[1] * b[1]) / n, (a[1] * b[0] - a[0] * b[1]) / n)


def qdet(Mx):
    """exact determinant over Q(i), entries (re, im)"""
    n = len(Mx)
    A = [row[:] for row in Mx]
    d = (Fr(1), Fr(0))
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != (0, 0)), None)
        if piv is None:
            return (Fr(0), Fr(0))
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = (-d[0], -d[1])
        d = qmul(d, A[c][c])
        for r in range(c + 1, n):
            f = qdiv(A[r][c], A[c][c])
            for k in range(c, n):
                fk = qmul(f, A[c][k])
                A[r][k] = (A[r][k][0] - fk[0], A[r][k][1] - fk[1])
    return d


def finite_measurements():
    print("[finite] descriptive float measurements (not proof certificates)")
    try:
        import numpy as np
    except ImportError:
        print("   numpy unavailable; skipped")
        return

    def eig(M, s, n=40):
        k = np.arange(n)
        x = (1 - np.cos((2 * k + 1) * np.pi / (2 * n))) / 2
        w = np.array([(-1) ** j * np.sin((2 * j + 1) * np.pi / (2 * n)) for j in range(n)])
        A = np.zeros((n, n))
        for a in range(1, M + 1):
            y = 1 / (a + x)
            Mx = np.zeros((n, n))
            for i, yy in enumerate(y):
                t = w / (yy - x)
                Mx[i] = t / t.sum()
            A += ((a + x) ** (-2 * s))[:, None] * Mx
        return max(np.linalg.eigvals(A).real)
    for M in (4, 5, 7, 8, 12, 13, 14):
        print("   M=%2d  lambda(5/6)=%.6f lambda(9/10)=%.6f lambda(17/18)=%.6f"
              % (M, eig(M, 5 / 6), eig(M, 0.9), eig(M, 17 / 18)))


def main():
    t0 = time.time()
    e1_band_calculus()
    e1_cyclotomic_congruence()
    e1_g2_example()
    e1_b3_power_search()
    e1_fold_mass_bound()
    e1_kpower_bookkeeping()
    e2_identities()
    res = e2_caps()
    e2_lp_and_parameters(res)
    e2_G1_regression()
    e3_complexity(res)
    e5_toeplitz()
    finite_measurements()
    print("\nCertificate counts:")
    for k in sorted(COUNTS):
        print("   %-70s %d" % (k, COUNTS[k]))
    print("All Phase 26 Track E exact finite certificates passed (%.1fs)." % (time.time() - t0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
