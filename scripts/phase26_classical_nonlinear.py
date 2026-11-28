#!/usr/bin/env python3
"""Phase 26 Track F (F1-F4): exact certificates for
notes/phase26/classical-constants-and-nonlinear-boundaries.md.

Standard library only.  Every theorem-supporting assertion uses int / Fraction
arithmetic (labels [exact] or outward-rounded rational enclosures [encl]).
Floating point appears only in the isolated [finite] measurement section at the
end and never inside an assertion.

Run:  python -B scripts/phase26_classical_nonlinear.py   (exit code 0 on success)
"""
from fractions import Fraction as Fr
from math import gcd, isqrt
import sys
import time

COUNTS = {}


def check(cond, section, msg=""):
    """Record one assertion of the given section; abort on failure."""
    COUNTS[section] = COUNTS.get(section, 0) + 1
    if not cond:
        raise AssertionError(f"[{section}] failed: {msg}")


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i:: i] = bytearray(len(sieve[i * i:: i]))
    return [i for i in range(n + 1) if sieve[i]]


def frac_floor(x):
    return x.numerator // x.denominator


def dist_int(x):
    """||x|| = distance from the rational x to the nearest integer (exact)."""
    f = x - frac_floor(x)
    return min(f, 1 - f)


# ---------------------------------------------------------------------------
# F2.  q-Pade linear forms for E_b = prod_{j>=1} (1 - b^{-j}),  P_b = 1/E_b.
# ---------------------------------------------------------------------------

def Dk(b, k):
    r = 1
    for j in range(1, k + 1):
        r *= b ** j - 1
    return r


def gauss(b, n, r):
    """Gaussian binomial [n choose r]_b (an integer)."""
    num, den = Dk(b, n), Dk(b, r) * Dk(b, n - r)
    assert num % den == 0
    return num // den


def E_enclosure(b, K):
    """E_b = sum_k (-1)^k / D_k (Euler); alternating with decreasing terms."""
    s = Fr(0)
    for k in range(K + 1):
        s += Fr((-1) ** k, Dk(b, k))
    t = Fr(1, Dk(b, K + 1))
    return (s - t, s) if K % 2 == 0 else (s, s + t)


def Qn(b, n):
    return sum((-1) ** r * b ** (r * (n + 1) + r * r) * gauss(b, n, r) * (Dk(b, n) // Dk(b, r))
               for r in range(n + 1))


def Pn(b, n):
    return (-1) ** n * sum((-1) ** k * gauss(b, n, k) * Dk(b, 2 * n - k) for k in range(n + 1))


def Tk(b, n, k):
    """Definition: T_k = (-1)^k b^{-nk} C(b^k) / D_k with C(x) = prod_{j=n+1}^{2n} (x - b^j)."""
    C = 1
    for j in range(n + 1, 2 * n + 1):
        C *= b ** k - b ** j
    return Fr((-1) ** k * C, b ** (n * k) * Dk(b, k))


def poly_from_roots(roots):
    coeffs = [1]  # coeffs[i] = coefficient of x^i
    for a in roots:
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i + 1] += c
            new[i] -= a * c
        coeffs = new
    return coeffs


def section_F2():
    S = "F2"
    t0 = time.time()
    bases = (2, 3, 5, 10)
    # (a) coefficient identity c_i = (-1)^{n-i} b^{r(n+1)+r(r-1)/2} [n r]_b, r = n - i
    for b in bases:
        for n in range(1, 11):
            c = poly_from_roots([b ** j for j in range(n + 1, 2 * n + 1)])
            for i in range(n + 1):
                r = n - i
                check(c[i] == (-1) ** r * b ** (r * (n + 1) + r * (r - 1) // 2) * gauss(b, n, r), S,
                      f"coeff b={b} n={n} i={i}")
            # C(b^k) = 0 on k in [n+1, 2n]
            for k in range(n + 1, 2 * n + 1):
                check(sum(ci * b ** (k * i) for i, ci in enumerate(c)) == 0, S, "vanishing")
    # (b) closed forms of T_k: integrality for k <= n, tail formula for k >= 2n+1
    for b in bases:
        for n in range(1, 9):
            for k in range(0, n + 1):
                closed = Fr((-1) ** (k + n) * Dk(b, 2 * n - k), Dk(b, n - k) * Dk(b, k))
                check(Tk(b, n, k) == closed and closed.denominator == 1, S, f"Tk int b={b} n={n} k={k}")
                check(closed == (-1) ** (k + n) * gauss(b, n, k) * Fr(Dk(b, 2 * n - k), Dk(b, n)), S, "gauss form")
            for k in range(2 * n + 1, 2 * n + 7):
                closed = Fr((-1) ** k * b ** (n * (3 * n + 1) // 2) * Dk(b, k - n - 1),
                            b ** (n * k) * Dk(b, k - 2 * n - 1) * Dk(b, k))
                check(Tk(b, n, k) == closed, S, f"Tk tail b={b} n={n} k={k}")
                # ratio bound |T_{k+1}/T_k| <= 2/(b^{k+1}-1)
                ratio = abs(Tk(b, n, k + 1) / Tk(b, n, k))
                check(ratio <= Fr(2, b ** (k + 1) - 1), S, "ratio")
                check(Tk(b, n, k) * (-1) ** k > 0, S, "sign")
            # P_n = D_n * sum_{k<=n} T_k and alpha = Q_n / D_n
            check(Pn(b, n) == Dk(b, n) * sum(Tk(b, n, k) for k in range(n + 1)), S, "P_n")
            alpha = sum(Fr(poly_from_roots([b ** j for j in range(n + 1, 2 * n + 1)])[i] * b ** ((n - i) * (n - i + 1) // 2),
                           Dk(b, n - i)) for i in range(n + 1))
            check(alpha * Dk(b, n) == Qn(b, n), S, "Q_n = D_n alpha")
    # (c) the linear form lambda_n = Q_n E_b - P_n = D_n rho_n: rigorous enclosures and size bounds
    for b in bases:
        Elo, Ehi = E_enclosure(b, 60)
        check(Elo > 0 and Ehi - Elo < Fr(1, b ** 1000), S, "E enclosure")
        for n in range(1, 10):
            Q, P = Qn(b, n), Pn(b, n)
            lam_lo, lam_hi = sorted((Q * Elo - P, Q * Ehi - P))
            rho_part = sum(Tk(b, n, k) for k in range(2 * n + 1, 2 * n + 12))
            tail = abs(Tk(b, n, 2 * n + 12))
            r_lo, r_hi = Dk(b, n) * (rho_part - tail), Dk(b, n) * (rho_part + tail)
            check(r_lo <= lam_hi and lam_lo <= r_hi, S, f"identity enclosure b={b} n={n}")
            # |lambda_n| in [(13/15) E_b b^{-e_n}, 2 b^{-e_n}]  (b^{-e_n} handled via squares)
            lo_abs = min(abs(lam_lo), abs(lam_hi)) if lam_lo * lam_hi > 0 else Fr(0)
            hi_abs = max(abs(lam_lo), abs(lam_hi))
            # compare squares to avoid half-integer exponents: x >= c b^{-e}  <=>  x^2 b^{2e} >= c^2
            two_e = (3 * n + 2) * (n + 1)
            check(lo_abs ** 2 * b ** two_e >= (Fr(13, 15) * Elo) ** 2, S, f"lam lower b={b} n={n}")
            check(hi_abs ** 2 * b ** two_e <= 4, S, f"lam upper b={b} n={n}")
            f = 2 * n * n + n
            check(abs(Q) <= 3 * b ** f, S, "Q upper")
            # Thm 2.1(3) (repaired, review m1): ||Q_n| - b^f| <= b^f P_b / (b^{n+1} - 1), P_b <= 1/Elo
            check(abs(abs(Q) - b ** f) * (b ** (n + 1) - 1) * Elo <= b ** f, S, "Q deviation bound")
            if n >= 2:
                check(2 * abs(Q) >= b ** f, S, "Q lower (n >= 2)")
            # the sign of lambda_n is (-1)^{2n+1} = negative (first tail term dominates)
            check(lam_hi < 0, S, "lambda sign")
        # (d) non-proportionality of consecutive pairs (determinant != 0) for n = 1..9
        for n in range(1, 10):
            det = Qn(b, n) * Pn(b, n + 1) - Pn(b, n) * Qn(b, n + 1)
            check(det != 0, S, f"det b={b} n={n}")
    # (d') review m1: the analytic constants that close Thm 2.1(3)-(4) for EVERY b >= 2 and n >= 1
    E2lo, E2hi = E_enclosure(2, 60)
    check(E2lo * 3463 > 1000, S, "P_2 < 3.463")                       # P_b <= P_2 < 3.463
    check(Fr(3463, 1000) / 7 < Fr(1, 2), S, "P_2/(2^3-1) < 1/2")       # n >= 2: ratio <= P_2/7
    check(Fr(3463, 1000) / 3 < 2, S, "P_2/(2^2-1) < 2")                # n >= 1: |Q_n| <= 3 b^f
    check(E2lo > Fr(2887, 10000), S, "E_2 > 0.2887")
    check(13 * Fr(2887, 10000) * 2 ** 14 > 341 * 180, S, "n = 1 ratio > 341")
    for n in range(1, 40):
        fn = lambda m, r: r * (2 * m + 1) + (m * m + m) // 2 - (r * r + r) // 2
        en = lambda m: (3 * m + 2) * (m + 1) // 2
        check(fn(n + 1, n + 1) - fn(n, n) + en(n + 1) - en(n) == 7 * (n + 1), S, "exponent 7(n+1)")
        for r in range(n):
            check(2 * (fn(n, n) - fn(n, r)) == (n - r) * (3 * n + 1 - r), S, "f(n)-f(r)")
            check(fn(n, n) - fn(n, r) >= (n - r) * (n + 1), S, "f(n)-f(r) >= (n-r)(n+1)")
    for b in range(2, 18):                                              # det != 0 at n = 1, 2 for 16 bases
        for n in (1, 2):
            check(Qn(b, n) * Pn(b, n + 1) - Pn(b, n) * Qn(b, n + 1) != 0, S, f"det b={b} n={n}")
            check(2 * abs(Qn(b, n + 1)) >= b ** (2 * (n + 1) ** 2 + n + 1), S, "Q_{n+1} lower")
    # (d'') review M2: Lemma 2.0(1) needs b^N Z >= 1.  Counterexample b = 2, y = 100 sqrt2, N = 1, L = 6:
    #   Z = sqrt2/200 < 2^{-7} (so d_2 = ... = d_7 = 0 and A = 0), and no A >= 1 has |A y - 2| <= y 2^{-6}
    check(2 * 128 ** 2 < 200 ** 2, S, "Z = sqrt2/200 < 2^-7")          # 128 sqrt2 < 200
    check(2 * 100 ** 2 * 63 ** 2 > 128 ** 2, S, "y - 2 > y/64")         # 63 y > 128  <=>  (63*100 sqrt2)^2 > 128^2
    for b in (2, 3, 5, 10):
        Elo, Ehi = E_enclosure(b, 40)
        check(Ehi < 1, S, "P_b > 1, so b^N P_b >= 1 for all N >= 0")
    # (e) irrationality-measure chain on explicit integers A (b = 2): |A E - B| >= 1/(2|Q_m|)
    b = 2
    Elo, Ehi = E_enclosure(b, 60)
    for A in list(range(1, 400)) + [10 ** 6 + 7, 2 ** 40 + 1, 3 ** 30]:
        B = frac_floor(A * Ehi + Fr(1, 2))
        # minimal n >= 2 with b^{e_n} >= 4A  (tested via squares: b^{2 e_n} >= 16 A^2)
        n = 2
        while 16 * A * A > b ** ((3 * n + 2) * (n + 1)):
            n += 1
        dist = min(abs(A * Elo - B), abs(A * Ehi - B))
        bound = min(Fr(1, 2 * abs(Qn(b, n))), Fr(1, 2 * abs(Qn(b, n + 1))))
        check(dist >= bound, S, f"measure chain A={A}")
    # (f) b-adic scale of E_b (isolation barrier): ||b^g E_b|| >= (1/2) b^{-(g_{k+1}-g)}
    for b in (2, 3, 10):
        pent = sorted({k * (3 * k - 1) // 2 for k in range(-40, 41)})
        Elo, Ehi = E_enclosure(b, 70)
        for g in range(1, 400):
            k1 = min(x for x in pent if x > g)
            lo = min(dist_int(b ** g * Elo), dist_int(b ** g * Ehi))
            check(2 * lo * b ** (k1 - g) >= 1, S, f"isolation b={b} g={g}")
            # and the gap g_{k+1} - g_k <= 2 i + 1 <= sqrt(8 g / 3) + 2
            k0 = max(x for x in pent if x <= g)
            gap = k1 - k0
            check(3 * (gap - 2) ** 2 <= 8 * g or gap <= 2, S, "pentagonal gap")
            # review m5: g >= 1 forces g_{k+1} >= 2 and g_{k+2} - g_{k+1} >= 2 (no small-case exception)
            k2 = min(x for x in pent if x > k1)
            check(k1 >= 2 and k2 - k1 >= 2, S, "next pentagonal gap >= 2")
    # (f') review m5, Prop. 2.6: if t in [0,1) and |(b-1)t - d| < b^{-L} with d in {0..b-1}, then the
    #      first L base-b digits of t all equal d (d = 0 forces eta >= 0, d = b-1 forces eta < 0: no wrap)
    for b in (2, 3, 10):
        for d in range(b):
            for L in range(1, 13):
                for k in (1, 2, 999):
                    for sgn in (1, -1):
                        t = Fr(d, b - 1) + sgn * Fr(k, 1000) * Fr(1, (b - 1) * b ** L)
                        if not (0 <= t < 1):
                            continue
                        digs = [frac_floor(b ** j * t) % b for j in range(1, L + 1)]
                        check(digs == [d] * L, S, "Prop 2.6 run of length L")
    # (g) run-transfer certificates for P_b = 1/E_b on certified digits (base 2 and 3)
    for b in (2, 3):
        Elo, Ehi = E_enclosure(b, 80)
        Plo, Phi = 1 / Ehi, 1 / Elo
        Ndig = 1500
        dlo = [(frac_floor(b ** j * Plo) % b) for j in range(1, Ndig + 1)]
        dhi = [(frac_floor(b ** j * Phi) % b) for j in range(1, Ndig + 1)]
        check(dlo == dhi, S, "P digits certified")
        # longest constant run starting after position N (digits N+1..)
        runs_ok = True
        j = 0
        maxrun = {}
        while j < Ndig:
            k = j
            while k + 1 < Ndig and dlo[k + 1] == dlo[j]:
                k += 1
            L = k - j + 1
            N = j  # run occupies digits N+1..N+L
            if N >= 20 and L > Fr(4, 3) * N + 5 * isqrt(N + 1) + 40:
                runs_ok = False
            maxrun[N] = L
            j = k + 1
        check(runs_ok, S, "P_b runs within (4/3)N + O(sqrt N)")
        FINITE[f"P_{b} longest run after N>=20 (N, L)"] = max(((N, L) for N, L in maxrun.items() if N >= 20),
                                                               key=lambda t: Fr(t[1], t[0]))
        FINITE[f"P_{b} transitions in first {Ndig} digits"] = sum(1 for i in range(Ndig - 1) if dlo[i] != dlo[i + 1])
    print(f"  F2 done in {time.time() - t0:.1f}s")


FINITE = {}


# ---------------------------------------------------------------------------
# F1.  ln 2: band-indexed exclusion law, CRT decoupling, a ratio-2 reset block,
#      translate-robust prime-centered Pade forms.
# ---------------------------------------------------------------------------

def bbp_states(nmax):
    """s_n = sum_{k<=n} 2^{n-k}/k as Fractions, n = 0..nmax."""
    s = [Fr(0)]
    for n in range(1, nmax + 1):
        s.append(2 * s[-1] + Fr(1, n))
    return s


def vp_int(x, p):
    if x == 0:
        return 10 ** 9
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def vp_frac(x, p):
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def residue_mod_p(x, p):
    """x in Z_(p) -> x mod p."""
    assert x.denominator % p != 0
    return x.numerator * pow(x.denominator, -1, p) % p


def lcm_upto(n):
    out = 1
    for q in primes_upto(n):
        qe = q
        while qe * q <= n:
            qe *= q
        out *= qe
    return out


def ln2_enclosure(K):
    S_ = sum(Fr(1, k * 2 ** k) for k in range(1, K + 1))
    return S_, S_ + Fr(1, (K + 1) * 2 ** K)


def section_F1(s):
    S = "F1"
    t0 = time.time()
    A = [x.numerator for x in s]

    def frac_den(x):
        return (x - frac_floor(x)).denominator

    # (a) band-indexed exclusion law for single-level ODD primes p <= n with p^2 > n_end - 1
    #     (Lemma 1.1 hypothesis; p = 2 is excluded, see the counterexample in (a'')); brute force over a mod p
    cases = 0
    for n in (60, 90, 131):
        for rho in (Fr(3, 2), Fr(2), Fr(3)):
            n_end = frac_floor(rho * n)
            for p in primes_upto(n):
                if p * p <= n_end - 1 or p == 2:
                    continue
                cases += 1
                bands = sorted({k // p for k in range(n, n_end)})
                drop = any(A[m] % p == 0 for m in bands)
                excl = {(-pow(2, n - m, p) * residue_mod_p(s[m], p)) % p for m in bands if A[m] % p != 0}
                for k in range(n, n_end):
                    m = k // p
                    check(residue_mod_p(p * s[k], p) == pow(2, k - m, p) * residue_mod_p(s[m], p) % p, S, "band law")
                adm_pred = {0} if drop else set(range(p)) - excl
                adm_true = {a for a in range(p)
                            if all(frac_den(s[k] + Fr(2 ** (k - n) * a, p)) == frac_den(s[k]) for k in range(n, n_end))}
                check(adm_true == adm_pred, S, f"exclusion law n={n} p={p}")
                check(len(excl) <= len(bands), S, "exclusions <= bands")
                # repaired band count (review M1): |B_p(W)| <= ceil((n_end-n-1)/p) + 1 < (n_end-n)/p + 2
                check(len(bands) <= -((n - n_end + 1) // p) + 1, S, "band count <= ceil((L-1)/p)+1")
                check(len(bands) < Fr(n_end - n, p) + 2, S, "band count < L/p + 2")
    # (a') the band count formula and its sharp bound on a full grid (pure arithmetic, odd p <= n, p^2 > n_end-1)
    for n in range(3, 80):
        for n_end in range(n + 1, min(n * n, 2 * n + 2)):
            for p in primes_upto(n):
                if p == 2 or p * p <= n_end - 1:
                    continue
                nb = len({k // p for k in range(n, n_end)})
                Lw = n_end - n
                check(nb == (n_end - 1) // p - n // p + 1, S, "band count formula")
                check(nb <= -((1 - Lw) // p) + 1, S, "band count sharp bound")
                if n % p == p - 1:   # equality case n = -1 mod p
                    check(nb == -((1 - Lw) // p) + 1, S, "band count bound attained")
    # (a'') review M1 counterexamples to the ORIGINAL Lemma 1.1 statement
    #   - n = 9, n_end = 11, p = 5: |B_5(W)| = 2 > (11-9)/5 + 1 (band 2 is a drop band: A_2 = 5)
    bands = {k // 5 for k in range(9, 11)}
    check(len(bands) == 2 and Fr(2) > Fr(11 - 9, 5) + 1 and A[2] % 5 == 0, S, "old band bound false (p=5)")
    #   - n = 13, n_end = 15, p = 7, no drop band: |Excl_7(W)| = |B_7(W)| = 2 > (15-13)/7 + 1
    bands = sorted({k // 7 for k in range(13, 15)})
    excl7 = {(-pow(2, 13 - m, 7) * residue_mod_p(s[m], 7)) % 7 for m in bands}
    check(bands == [1, 2] and all(A[m] % 7 for m in bands) and excl7 == {4, 6}, S, "Excl_7 = {4, 6}")
    check(Fr(len(excl7)) > Fr(15 - 13, 7) + 1, S, "old exclusion bound false (p=7)")
    #   - p = 2 (n = 2, n_end = 3, M = 2): the band law fails and the predicted-admissible a = 1 kills Q_2
    check(residue_mod_p(2 * s[2], 2) != pow(2, 2 - 1, 2) * residue_mod_p(s[1], 2) % 2, S, "band law fails at p=2")
    excl2 = {(-pow(2, 2 - 1, 2) * residue_mod_p(s[1], 2)) % 2}
    check(A[1] % 2 == 1 and 1 not in excl2, S, "a = 1 predicted admissible at p=2")
    check(frac_den(s[2] + Fr(1, 2)) != frac_den(s[2]), S, "but x_2 + 1/2 has denominator 1 != Q_2 = 2")
    # (b) CRT product decoupling for pairs of primes (same band and cross band)
    n, n_end = 60, 120
    plist = [p for p in primes_upto(n) if p * p > n_end]
    pairs = [(plist[i], plist[j]) for i in range(len(plist)) for j in range(i + 1, len(plist))][:12]

    def adm(a, mod):
        return all(frac_den(s[k] + Fr(2 ** (k - n) * a, mod)) == frac_den(s[k]) for k in range(n, n_end))
    for p1, p2 in pairs:
        cnt12 = sum(1 for a in range(p1 * p2) if adm(a, p1 * p2))
        cnt1 = sum(1 for a in range(p1) if adm(a, p1))
        cnt2 = sum(1 for a in range(p2) if adm(a, p2))
        check(cnt12 == cnt1 * cnt2, S, f"CRT product {p1},{p2}")
    # (c) explicit full-denominator reset block of ratio 2 at n = 1000
    n, n_end, X = 1000, 2000, 150
    P = []
    for p in primes_upto(n):
        if p <= X:
            continue
        bands = sorted({k // p for k in range(n, n_end)})
        if any(A[m] % p == 0 for m in bands):
            continue
        P.append(p)
    M = 1
    for p in P:
        M *= p
    check(M.bit_length() - 1 >= (n_end - n) + 60, S, "modulus bits")
    excl = {}
    for p in P:
        bands = sorted({k // p for k in range(n, n_end)})
        excl[p] = {(-pow(2, n - m, p) * residue_mod_p(s[m], p)) % p for m in bands}
    W, Kt = 1400, 1600
    num = sum((1 << W) // ((n + k) << k) for k in range(1, Kt + 1))
    T_lo = Fr(num, 1 << W)
    T_hi = Fr(num + Kt + 1, 1 << W) + Fr(1, (n + Kt + 1) << Kt)
    fs = s[n] - frac_floor(s[n])
    tau_lo, tau_hi = -(fs + T_hi), -(fs + T_lo)
    check((tau_hi - tau_lo) * M < Fr(1, 4), S, "tau precision")
    a0 = frac_floor(M * tau_lo + Fr(1, 2))
    inv = {p: pow(M // p, -1, p) for p in P}
    found = None
    for d in range(0, 400000):
        for a in ((a0 + d, a0 - d) if d else (a0,)):
            if all((a * inv[p]) % p not in excl[p] for p in P):
                found = a
                break
        if found is not None:
            break
    check(found is not None, S, "admissible residue found")
    a = found
    max_scaled = Fr(0)
    for k in range(n, n_end):
        xt = s[k] + Fr((1 << (k - n)) * a, M)
        check(frac_den(xt) == frac_den(s[k]), S, "exact denominator")
        if k + 1 < n_end:
            nxt = s[k + 1] + Fr((1 << (k + 1 - n)) * a, M)
            check((nxt - 2 * xt - Fr(1, k + 1)).denominator == 1, S, "recurrence in block")
        dd = dist_int(xt)
        check(dd <= Fr(1, k) + Fr(1, 2 ** 30), S, "uniform smallness")
        max_scaled = max(max_scaled, k * dd)
    FINITE["F1 ratio-2 block [1000,2000): #primes, log2 M, |a-a0|, max n'||x~_n'||"] = (
        len(P), M.bit_length() - 1, abs(a - a0), float(max_scaled))
    # (d) translate-robust prime-centered Pade forms (Track B Thm 4.3 with rational shifts)
    from math import comb
    l2lo, l2hi = ln2_enclosure(1500)
    tested = 0
    for p in primes_upto(160):
        if p < 11:
            continue
        Lp = lcm_upto(p)
        for r in range(2, p, max(1, p // 7)):
            Mw = p - r + 1
            c = [(-1) ** (r - 1 - j) * comb(r - 1, j) * comb(Mw + r - 1 + j, r - 1) for j in range(r)]
            P3 = sum(cj * 2 ** j for j, cj in enumerate(c))
            LM = lcm_upto(Mw)
            base = sum(cj * s[Mw + j] for j, cj in enumerate(c))
            I_lo = 2 ** Mw * P3 * l2lo - base
            I_hi = 2 ** Mw * P3 * l2hi - base
            check(I_lo > 0, S, "I > 0")
            dens = {1, LM, s[Mw].denominator, LM // gcd(LM, 6)}
            for dden in dens:
                for shift in (-1, 0, 1, 3):
                    x = Fr(frac_floor(dden * 2 ** Mw * l2lo) + shift, dden)
                    Lam = x * P3 - base  # = I - (2^M ln 2 - x) P(3)
                    check((Lp * Lam).denominator == 1, S, "L_p Lambda integral")
                    check(vp_frac(Lam, p) == -1, S, "v_p(Lambda) = -1")
                    if Lp * I_hi < 1:
                        lower = (Fr(1, Lp) - I_hi) / P3
                        dist = min(abs(2 ** Mw * l2lo - x), abs(2 ** Mw * l2hi - x))
                        check(dist >= lower, S, "translate-robust lower bound")
                    tested += 1
    FINITE["F1 translate-robust Pade forms tested"] = tested
    print(f"  F1 done in {time.time() - t0:.1f}s")


# ---------------------------------------------------------------------------
# F3.  Flagship cube C_1(3)^3  (b = 2, p = 3, s = 1, d = 3, B = 4).
# ---------------------------------------------------------------------------

def cube_coeffs(mmax, p=3, s=1, d=3):
    """c_m = sum_{x^d+y^d+z^d=m, x,y,z>=1} p^{-s(v(x)+v(y)+v(z))}, m <= mmax (Fractions)."""
    w = {}
    i = 1
    while i ** d <= mmax:
        w[i ** d] = Fr(1, p ** (s * vp_int(i, p)))
        i += 1
    keys = sorted(w)
    two = {}
    for a in keys:
        for b_ in keys:
            if a + b_ > mmax:
                break
            two[a + b_] = two.get(a + b_, Fr(0)) + w[a] * w[b_]
    c = [Fr(0)] * (mmax + 1)
    for m2, val in two.items():
        for a in keys:
            if m2 + a > mmax:
                break
            c[m2 + a] += val * w[a]
    return c, w


def section_F3():
    S = "F3"
    t0 = time.time()
    B, p = 4, 3
    Mmax, J = 4000, 160
    c, w = cube_coeffs(Mmax + J + 1)
    # (a) depth recursion  C(z) - p^{-s} C(z^{p^d}) = sum_{p not | i} z^{i^d}, coefficientwise
    deg = Mmax + J + 1
    unit_cubes = set()
    ii = 1
    while ii ** 3 <= deg:
        if ii % 3 != 0:
            unit_cubes.add(ii ** 3)
        ii += 1
    for m in range(1, deg + 1):
        lhs = w.get(m, Fr(0)) - (Fr(1, 3) * w[m // 27] if m % 27 == 0 and (m // 27) in w else Fr(0))
        rhs = Fr(1) if m in unit_cubes else Fr(0)
        check(lhs == rhs, S, f"depth recursion m={m}")
    # (b) prefixes R_M, depths e_M, tail enclosures, rational-exclusion certificates
    R = Fr(0)
    best = (Fr(0), None)
    zero_depth = []
    cert_count = 0
    packets = {}
    for M in range(1, Mmax + 1):
        R = B * R + c[M]
        e = max(0, -vp_frac(R, p))
        check((R - frac_floor(R)).denominator == p ** e, S, "den(R_M) is a power of 3")
        check(p ** e <= M, S, "Prop 3.1: e_M <= s log_p M (s = 1)")
        if e == 0:
            zero_depth.append(M)
        Tpart = sum(c[M + j] * Fr(1, B ** j) for j in range(1, J + 1))
        tail = Fr(2 * (M + J + 2), B ** J)  # c_m <= m and sum_{j>J} (M+j) 4^{-j} <= 2(M+J+2) 4^{-J}
        T_hi = Tpart + tail
        check(Tpart > 0, S, "T_M > 0")
        if M in (91, 126):
            packets[M] = (R, e, Tpart, T_hi)
        V = 1 / (p ** e * T_hi)
        if V > best[0]:
            best = (V, M)
        cert_count += 1
    Vstar, Mstar = best
    check(Vstar > 1, S, "nontrivial exclusion")
    FINITE["F3 best exclusion: X != u/v for all v < V* (V*, at M)"] = (frac_floor(Vstar), Mstar)
    FINITE["F3 shifts M <= 4000 with e_M = 0 (count, first 8)"] = (len(zero_depth), zero_depth[:8])
    # (c) multi-packet collapse: propagated tail identity T_{M'} = B^{M'-M} T_M - sum c_i B^{M'-i} (exact, truncated)
    top = Mmax + J
    for M in range(10, 400, 37):
        for Mp in (M + 1, M + 5, M + 23):
            TM = sum(c[k] * Fr(1, B ** (k - M)) for k in range(M + 1, top + 1))
            TMp = sum(c[k] * Fr(1, B ** (k - Mp)) for k in range(Mp + 1, top + 1))
            mid = sum(c[i] * B ** (Mp - i) for i in range(M + 1, Mp + 1))
            check(TMp == B ** (Mp - M) * TM - mid, S, "propagated tail identity")
    # (c') review C1: the three exclusion tests of Thm 3.3 and the two counterexamples on C_1(3)^3.
    #   Exact-prefix test: (a, a+t] meets v^{-1}Z  iff  v t >= 1 - {v a}   (brute force on a grid)
    for v in range(1, 13):
        for i in range(0, 97, 7):
            a = Fr(i, 97)
            for j in range(1, 300, 13):
                t = Fr(j, 1013)
                lo_k, hi_k = frac_floor(v * a) - 1, frac_floor(v * (a + t)) + 2
                meets = any(a < Fr(k, v) <= a + t for k in range(lo_k, hi_k))
                fa = v * a - frac_floor(v * a)
                check(meets == (v * t >= 1 - fa), S, "exact-prefix interval criterion")
    #   Denominator-only (h = 0) test: min over units A of the least T > 0 with v'(A/p^e + T) in Z
    #   equals g_0/(v' p^e) = 1/lcm(v', p^e)   (GF-46 Thm 1.3(1) at h = 0)
    for pp in (3, 5):
        for e in range(1, 5):
            for vq in range(1, 61):
                units = [Ai for Ai in range(pp ** e) if Ai % pp]
                tmin = min((1 - (Fr(vq * Ai, pp ** e) - frac_floor(Fr(vq * Ai, pp ** e)))) / vq for Ai in units)
                g0 = gcd(vq, pp ** e)
                check(tmin == Fr(g0, vq * pp ** e) == Fr(1, vq * pp ** e // g0), S, "h = 0 threshold")
                # low residue h >= 1: r_min <= g_0 p^h <= v' p^h, so the threshold r_min/(v' p^e) <= p^{h-e}
                for h in range(1, e + 1):
                    g0h = gcd(vq, pp ** (e - h))
                    for A0 in (1, pp ** h - 1):
                        rmin = (-vq * A0) % (g0h * pp ** h) or g0h * pp ** h
                        check(Fr(rmin, vq * pp ** e) <= Fr(pp ** h, pp ** e), S, "low-residue threshold <= p^{h-e}")
    #   Counterexample 1 (exact prefix), M* = 91, v = 10, v' = 10/gcd(10, 4^91) = 5:
    R91, e91, T91lo, T91hi = packets[91]
    v, vq = 10, 10 // gcd(10, B ** 91)
    check(vq == 5 and e91 == 3 and c[92] == 2, S, "M=91 data")
    check(T91lo >= Fr(c[92], B) == Fr(1, 2), S, "T_91 >= 1/2")
    check(T91lo >= Fr(1, vq * 27 // gcd(vq, 27)), S, "h = 0 test FAILS at M=91, v=10 (T_91 >= 1/135)")
    A91 = (R91 - frac_floor(R91)) * 27
    check(A91 == 22, S, "{R_91} = 22/27")
    rmin91 = (-vq * A91.numerator) % 27 or 27
    check(rmin91 == 25 and T91lo * vq * 27 >= rmin91, S, "GF-46 h = e test also FAILS at M=91, v=10")
    a91, t91 = R91 / B ** 91, T91hi / B ** 91
    check(v * t91 < 1 - (v * a91 - frac_floor(v * a91)), S, "exact-prefix packet EXCLUDES 10 X in Z at M=91")
    #   Counterexample 2 (GF-46 at h = e, floor(R) discarded), M* = 126, v = 4, v' = 1:
    R126, e126, T126lo, T126hi = packets[126]
    v, vq = 4, 4 // gcd(4, B ** 126)
    check(vq == 1 and e126 == 3 and R126 - frac_floor(R126) == Fr(1, 27), S, "M=126 data")
    check(T126lo >= Fr(c[127], B) == Fr(3, 4), S, "T_126 >= 3/4")
    check(T126lo >= Fr(1, 27), S, "h = 0 test FAILS at M=126, v=4 (T_126 >= 1/27)")
    rmin126 = (-vq * 1) % 27 or 27
    check(rmin126 == 26 and vq * 27 * T126hi < rmin126, S, "GF-46 h = e test EXCLUDES 4 X in Z at M=126")
    check(T126hi < Fr(797, 1000) and T126lo > Fr(3, 4), S, "T_126 in [0.75, 0.797]")
    # (d) GF-46 depth drop at M = 1268 (q_1268 = 1)
    R = Fr(0)
    for M in range(1, 1269):
        R = B * R + c[M]
    check((R - frac_floor(R)).denominator == 1, S, "q_1268 = 1")
    print(f"  F3 done in {time.time() - t0:.1f}s ({cert_count} certificates)")


# ---------------------------------------------------------------------------
# F4.  Algebraic irrationals and the run-transfer ceiling.
# ---------------------------------------------------------------------------

def section_F4():
    S = "F4"
    t0 = time.time()
    # (a) sqrt(D): exact remainder recursion E_{N+1} = 4 E_N - d_{N+1}(4 x_N + d_{N+1}) and digit rule
    for D in (2, 3, 5):
        x = isqrt(D)
        E = D - x * x
        for N in range(0, 3000):
            x1 = isqrt(D * 4 ** (N + 1))
            d = x1 - 2 * x
            check(d in (0, 1), S, "binary digit")
            E1 = D * 4 ** (N + 1) - x1 * x1
            check(E1 == 4 * E - d * (4 * x + d), S, "remainder recursion")
            check((d == 1) == (4 * E >= 4 * x + 1), S, "digit rule")
            check(1 <= E1 < (2 * isqrt(D) + 3) * 2 ** (N + 2), S, "bounded remainder")
            x, E = x1, E1
    # golden ratio phi = (1 + sqrt5)/2: F_N = x_N^2 - 2^N x_N - 4^N in (-(2^N phi + x_N), 0)
    for N in range(1, 2000):
        x = (2 ** N + isqrt(5 * 4 ** N)) // 2
        # adjust to floor(2^N phi)
        while (2 * x - 2 ** N) ** 2 > 5 * 4 ** N:
            x -= 1
        while (2 * (x + 1) - 2 ** N) ** 2 <= 5 * 4 ** N:
            x += 1
        F = x * x - 2 ** N * x - 4 ** N
        check(F < 0 and -F < 2 ** (N + 2), S, "phi remainder")
    # (b) ceiling witness: switches at t_k = ceil(lam^k); runs <= (lam-1) n + 1, transitions = #switches
    for lam in (Fr(7, 3), Fr(3, 2), Fr(5)):
        Nmax = 6000
        t = []
        val = Fr(1)
        while True:
            tk = frac_floor(val) + (0 if val.denominator == 1 else 1)
            if tk >= Nmax:
                break
            if not t or tk > t[-1]:
                t.append(tk)
            val *= lam
        digits = []
        bit, idx = 0, 0
        for pos in range(1, Nmax + 1):
            if idx < len(t) and pos == t[idx]:
                bit ^= 1
                idx += 1
            digits.append(bit)
        trans = sum(1 for i in range(Nmax - 1) if digits[i] != digits[i + 1])
        check(trans <= len(t), S, "transitions = switches")
        # every run after position n (digits n+1..n+L) has L <= (lam-1)(n+1) + 1 for n >= t_1 - 1
        j = 0
        while j < Nmax:
            k = j
            while k + 1 < Nmax and digits[k + 1] == digits[j]:
                k += 1
            for nstart in range(max(j, t[0]), k + 1, 97):
                L = k - nstart + 1
                check(L <= (lam - 1) * (nstart + 1) + 1 or k == Nmax - 1, S, "ceiling run bound")
            j = k + 1
    print(f"  F4 done in {time.time() - t0:.1f}s")


def main():
    t0 = time.time()
    print("Phase 26 Track F certificates")
    states = bbp_states(2100)
    section_F2()
    section_F1(states)
    section_F3()
    section_F4()
    total = sum(COUNTS.values())
    print("assertion counts:", dict(sorted(COUNTS.items())), "total", total)
    print("[finite] measurements (no theorem depends on these):")
    for k, v in FINITE.items():
        print("   ", k, "=", v)
    print(f"all checks passed in {time.time() - t0:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
