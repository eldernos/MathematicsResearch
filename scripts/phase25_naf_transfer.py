"""Phase 25 Addendum Track I: Non-Adjacent Signed-Digit Geometric Transfer,
E_+(8) Order-4 Nonnormality, Sharp Order-3 Barrier & Cubic-Character L_-(4) Classification.

Standalone verification and certificate suite (Python 3.10+, standard library only).

EVIDENCE DISCIPLINE:
- Every certificate ([exact] and [encl]) uses ONLY exact Python `int` and
  `fractions.Fraction` arithmetic (including integer `isqrt`, `comb`, `gcd`,
  and scaled-integer outward rounding at scale 2^-192). ZERO floating-point
  arithmetic enters any certificate or assertion in Sections 1-5.
- Section 6 ([finite]) reports finite-prefix measurements ONLY; finite
  measurements are strictly isolated and never used as asymptotic evidence.

Run:
    python -B scripts/phase25_naf_transfer.py
"""

from collections import Counter
from fractions import Fraction
from math import comb, gcd, isqrt
import time

T0 = time.time()
COUNTS = {"exact": 0, "encl": 0, "finite": 0}


def check(cond, msg, kind="exact"):
    if not cond:
        raise AssertionError(f"FAILED [{kind}]: {msg}")
    COUNTS[kind] += 1


def head(title):
    print(f"\n=== {title} ===")


# ===========================================================================
# Exact integer & directed-rounding helpers (ZERO floats)
# ===========================================================================

SB = 192
ONE = 1 << SB


def cdiv(a, b):
    """Exact ceiling division ceil(a / b) for integers a, b with b > 0."""
    return -((-a) // b)


def frac_dn(fr):
    return (fr.numerator * ONE) // fr.denominator


def frac_up(fr):
    return cdiv(fr.numerator * ONE, fr.denominator)


def fx_to_frac(v):
    return Fraction(v, ONE)


def fmt_dn(fr, d=6):
    """Exact decimal string rounded DOWN (safe for certified lower bounds)."""
    fr = Fraction(fr)
    v = (fr.numerator * (10 ** d)) // fr.denominator
    sgn = "-" if v < 0 else ""
    v = abs(v)
    return f"{sgn}{v // (10 ** d)}.{v % (10 ** d):0{d}d}"


def fmt_up(fr, d=6):
    """Exact decimal string rounded UP (safe for certified upper bounds)."""
    fr = Fraction(fr)
    v = cdiv(fr.numerator * (10 ** d), fr.denominator)
    sgn = "-" if v < 0 else ""
    v = abs(v)
    return f"{sgn}{v // (10 ** d)}.{v % (10 ** d):0{d}d}"


def fmt_iv(iv, d=6):
    return f"[{fmt_dn(iv[0], d)}, {fmt_up(iv[1], d)}]"


def odd_part(n):
    n = abs(n)
    return 0 if n == 0 else n // (n & -n)


def v2(n):
    return (n & -n).bit_length() - 1


def primes_upto(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i : limit + 1 : i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i, v in enumerate(sieve) if v]


# ===========================================================================
# Canonical NAF & minimal signed-digit weight (matching DigitMassTransfer.lean)
# ===========================================================================

def naf_digits(A):
    """Canonical Non-Adjacent Form of any integer A in Z.

    Returns a list e where A = sum_{r>=0} e[r] * 2^r, e[r] in {-1, 0, 1},
    e[r] * e[r+1] = 0 for all r, and no trailing zero (empty list for A = 0).
    """
    if A == 0:
        return []
    out = []
    x = A
    while x != 0:
        if x & 1:
            eps = 1 if (x & 3) == 1 else -1
            out.append(eps)
            x = (x - eps) // 2
        else:
            out.append(0)
            x //= 2
    return out


def wpm(A):
    """NAF weight w_pm(A) for any integer A in Z."""
    x = abs(A)
    c = 0
    while x:
        if x & 1:
            if (x & 3) == 3:
                x += 1
            else:
                x -= 1
            c += 1
        x >>= 1
    return c


_WPM_REC_CACHE = {0: 0, 1: 1}


def wpm_rec(n):
    """Exact defining recursion of `signedWeight` in DigitMassTransfer.lean."""
    n = abs(n)
    if n in _WPM_REC_CACHE:
        return _WPM_REC_CACHE[n]
    if n & 1:
        m = n >> 1
        val = 1 + min(wpm_rec(m), wpm_rec(m + 1))
    else:
        val = wpm_rec(n >> 1)
    _WPM_REC_CACHE[n] = val
    return val


# ===========================================================================
# Outward-rounded exact Euler product & independent-exponent DP engine
# ===========================================================================

_PRIMES_CACHE = {}
_INV_SQ_CACHE = {}


def get_primes(limit):
    if limit not in _PRIMES_CACHE:
        _PRIMES_CACHE[limit] = primes_upto(limit)
    return _PRIMES_CACHE[limit]


def inv_sq_above(y, Y2=2000000):
    """Certified Fraction upper bound for sum_{p > y} p^{-2}.

    Exact outward sum over primes y < p <= Y2, plus elementary telescoping bound
    sum_{n > Y2, n = +-1 (mod 6)} n^{-2} <= 1 / (3 * (Y2 - 6)).
    """
    key = (y, Y2)
    if key not in _INV_SQ_CACHE:
        ps = get_primes(Y2)
        s = sum(cdiv(ONE, p * p) for p in ps if p > y)
        _INV_SQ_CACHE[key] = Fraction(s, ONE) + Fraction(1, 3 * (Y2 - 6))
    return _INV_SQ_CACHE[key]


def tail_bound(p, E, cd):
    """Upper bound for (1 - 1/p) sum_{e > E} g(e) p^{-e} when 0 <= g(e) <= c (e+1)^d."""
    c, d = cd
    assert E >= 3 * d
    x = Fraction(1, p)
    return c * ((E + 2) ** d) * (1 - x) * (x ** (E + 1)) / (1 - Fraction(3, 2) * x)


def local_bounds(g, p, E, cd):
    """Certified Fraction bounds for l(p) = (1 - 1/p) sum_{e >= 0} g(e) p^{-e}."""
    num = 0
    for e in range(E + 1):
        num = num * p + g(e)
    den = p ** (E + 1)
    lo = Fraction((p - 1) * num, den)
    return lo, lo + tail_bound(p, E, cd)


def exp_for(p):
    bits = p.bit_length()
    return max(7, 80 // max(1, bits - 1) + 2)


def tail_A(g, Y, cd, sign):
    """A such that sign * (l(p) - 1) <= A / p^2 for all p > Y (requires g(0) = g(1) = 1)."""
    c, d = cd
    E = 12
    A = Fraction(0)
    for e in range(2, E + 1):
        dd = g(e) - g(e - 1)
        if sign * dd > 0:
            A += Fraction(abs(dd), Y ** (e - 2))
    A += Fraction(c * ((E + 2) ** d), Y ** (E - 1)) / (1 - Fraction(3, 2 * Y))
    return A


class CertifiedEulerProduct:
    """Outward-rounded scale-2^-192 integer bounds for prod_{p in domain} l(p)."""

    def __init__(self, g, primes, Y, cd, domain=lambda p: True, keep=0):
        self.g = g
        self.cd = cd
        self.Y = Y
        lo = ONE
        hi = ONE
        self.prefix_lo = {}
        self.prefix_hi = {}
        for p in primes:
            if p > Y:
                break
            if not domain(p):
                continue
            l_lo, l_hi = local_bounds(g, p, exp_for(p), cd)
            lo = (lo * l_lo.numerator) // l_lo.denominator
            hi = cdiv(hi * l_hi.numerator, l_hi.denominator)
            if p <= keep:
                self.prefix_lo[p] = lo
                self.prefix_hi[p] = hi
        Ap = tail_A(g, Y, cd, +1)
        Am = tail_A(g, Y, cd, -1)
        S2 = inv_sq_above(Y)
        check(Ap * S2 < 1 and Am * S2 < 1, "EulerProduct tail convergence A*S2 < 1", "encl")
        tail_hi = Fraction(1, 1) / (1 - Ap * S2)
        tail_lo = 1 - Am * S2
        self.lo = (lo * tail_lo.numerator) // tail_lo.denominator
        self.hi = cdiv(hi * tail_hi.numerator, tail_hi.denominator)

    def bounds(self):
        return fx_to_frac(self.lo), fx_to_frac(self.hi)

    def R_after(self, p):
        return cdiv(self.hi * ONE, self.prefix_lo[p])


def certified_model_dp(stat, u_fn, ep, init, domain, primes, y, thr_bits=56):
    """Outward-rounded exact-int DP bounds for E[stat(prod_p u_fn(e_p))]."""
    thr = ONE >> thr_bits
    states = {}
    frozen = 0
    if init is None:
        states[1] = [ONE, ONE]
    else:
        for v, pr_lo, pr_hi in init["states"]:
            if v == 0:
                continue
            st = states.setdefault(v, [0, 0])
            st[0] += pr_lo
            st[1] += pr_hi
        frozen += init["frozen_hi"]
    last = None
    cd = ep.cd
    for p in primes:
        if p > y:
            break
        if not domain(p):
            continue
        Rp = ep.R_after(p)
        new_states = {}
        for v, (plo, phi) in states.items():
            sv = stat(v)
            e = 0
            while True:
                den = p ** (e + 1)
                qhi = cdiv(phi * (p - 1), den)
                if qhi < thr and e >= 3 * cd[1] + 1:
                    tfr = tail_bound(p, e - 1, cd)
                    frozen += cdiv(cdiv(phi * sv * tfr.numerator, tfr.denominator) * Rp, ONE)
                    break
                qlo = (plo * (p - 1)) // den
                vv = v * u_fn(e)
                if qhi < thr:
                    frozen += cdiv(qhi * stat(vv) * Rp, ONE)
                else:
                    st = new_states.setdefault(vv, [0, 0])
                    st[0] += qlo
                    st[1] += qhi
                e += 1
        states = new_states
        last = p
    R_end = ep.R_after(last) if last is not None else ep.hi
    hi = frozen
    lo = 0
    qfac = 1 - inv_sq_above(y)
    for v, (plo, phi) in states.items():
        sv = stat(v)
        hi += cdiv(phi * sv * R_end, ONE)
        lo += plo * sv
    lo = (lo * qfac.numerator) // qfac.denominator
    return fx_to_frac(lo), fx_to_frac(hi)


def best_naf_discrepancy(rho, s=1, max_r=16):
    """Exact Fraction supremum over r >= 1 of max(0, 1 - (4/3)*2^{-s*r} - s*r*rho)."""
    best = Fraction(0)
    best_r = 0
    for r in range(1, max_r + 1):
        ell = s * r
        val = 1 - Fraction(4, 3 << ell) - ell * rho
        if val > best:
            best = val
            best_r = r
    return best, best_r


def lowest_excluded_order(rho, s=1, max_L=12, max_r=6):
    """Lowest order L >= 1 in base 2^s excluded by NAF geometric transfer at rho."""
    b = 1 << s
    for L in range(1, max_L + 1):
        B = b ** L
        for r in range(1, max_r + 1):
            ell = s * r
            # Strict interior dyadic interval [m/B, 1 - m/B) subset ((2/3)*2^-ell, 1 - (2/3)*2^-ell)
            # Need m/B > 2 / (3 * 2^ell)  <=>  3 * 2^ell * m > 2 * B
            m = (2 * B) // (3 << ell) + 1
            if 2 * m < B:
                length = Fraction(B - 2 * m, B)
                if ell * rho < length:
                    return L, r, m, B, length
    return None


# ===========================================================================
# Section 1: Theorem A -- NAF Equivalence, Tail Bound & Finite Dyadic Transfer
# ===========================================================================

def section1_naf_geometric_transfer():
    head("Section 1 [exact]: NAF Equivalence, Tail Bound & Finite Dyadic Geometric Transfer")

    # 1a. Canonical NAF correctness, non-adjacency, symmetry, parity monotonicity, and
    #     exact equality w_NAF(A) = w_rec(|A|) across A in [-8192, 8192].
    for A in range(-8192, 8193):
        e = naf_digits(A)
        val = sum(d << r for r, d in enumerate(e))
        check(val == A, f"NAF value identity at A={A}")
        check(all(d in (-1, 0, 1) for d in e), f"NAF digits in {{-1,0,1}} at A={A}")
        for r in range(len(e) - 1):
            check(e[r] * e[r + 1] == 0, f"NAF non-adjacency at A={A}, r={r}")
        wt = sum(1 for d in e if d != 0)
        check(wt == wpm(A) == wpm_rec(abs(A)), f"w_NAF = wpm = signedWeight at A={A}")
        if A > 0:
            eneg = naf_digits(-A)
            check(eneg == [-d for d in e], f"NAF negation symmetry at A={A}")

    # Parity monotonicity lemma: w_rec(2q) <= w_rec(2q+1) and w_rec(2q+2) <= w_rec(2q+1).
    for q in range(0, 8193):
        w0 = wpm_rec(2 * q)
        w1 = wpm_rec(2 * q + 1)
        w2 = wpm_rec(2 * q + 2)
        check(w0 <= w1 and w2 <= w1, f"Parity monotonicity at q={q}")
        if q % 2 == 0:
            check(wpm_rec(2 * q + 1) == 1 + wpm_rec(q), f"NAF odd-step 1 mod 4 at q={q}")
        else:
            check(wpm_rec(2 * q + 1) == 1 + wpm_rec(q + 1), f"NAF odd-step 3 mod 4 at q={q}")

    # 1b. Brute-force minimality over ALL signed-digit representations of length <= 8
    #     (all 3^8 = 6561 signed strings on positions 0..7, which contains the full NAF
    #     of every A in [-170, 170], and in particular all A in [-127, 127]).
    min_wt_all = {}
    for code in range(3 ** 8):
        tmp = code
        val = 0
        wt = 0
        for r in range(8):
            d = (tmp % 3) - 1
            tmp //= 3
            if d:
                val += d << r
                wt += 1
        if val not in min_wt_all or wt < min_wt_all[val]:
            min_wt_all[val] = wt
    for A in range(-127, 128):
        check(min_wt_all[A] == wpm(A), f"Brute-force w_min(A) = w_NAF(A) at A={A}")

    # 1c. Exact finite dyadic tail bound and geometric interval count bound (base 2 and bases 4, 8),
    #     explicitly testing positive A, negative A, integer parts |A| >= 2^M, carry wraparound
    #     A = +-(2^M - 1), and alternating near-extremals A = +-((4^m - 1)/3).
    test_As = list(range(-512, 513))
    for M in (6, 8, 10, 12):
        test_As.extend([
            (1 << M) - 1, -((1 << M) - 1),
            (1 << M) + 1, -((1 << M) + 1),
            ((1 << M) - 1) // 3, -(((1 << M) - 1) // 3),
            ((1 << (M + 2)) - 1) // 3, -(((1 << (M + 2)) - 1) // 3),
        ])
    test_As = sorted(set(test_As))

    # Exhaustive check across M = 8 (all A in [-512, 512] + special values) and M = 10 (special values).
    dyadic_cases = 0
    extremal_attained = {1: False, 2: False, 3: False}
    for M, A_list in [(8, test_As), (10, [a for a in test_As if abs(a) <= 100 or abs(a) >= 250])]:
        den = 1 << M
        for A in A_list:
            e = naf_digits(A)
            wtA = sum(1 for d in e if d != 0)
            # Pad e to index M with zeros for lookup
            e_get = lambda r: e[r] if 0 <= r < len(e) else 0
            for ell in (1, 2, 3):
                # Interval [(2/3)*2^{-ell}, 1 - (2/3)*2^{-ell}]
                lo = Fraction(2, 3 << ell)
                hi = 1 - lo
                hits = 0
                for j in range(M):
                    # Exact fractional part {2^j * A / 2^M} = ((A << j) % 2^M) / 2^M
                    rem = (A << j) % den
                    pt = Fraction(rem, den)
                    # Check tail bound whenever next ell NAF digits vanish
                    if all(e_get(M - j - t) == 0 for t in range(1, ell + 1)):
                        Sj = sum(Fraction(e_get(M - j - t), 1 << t) for t in range(ell + 1, M - j + 1))
                        check(abs(Sj) < lo, f"Strict NAF tail bound at M={M}, A={A}, j={j}, ell={ell}")
                        check(not (lo <= pt <= hi), f"Zero-block avoids central interval at M={M}, A={A}, j={j}")
                    if lo <= pt <= hi:
                        hits += 1
                check(hits <= ell * wtA, f"Dyadic count <= ell*w_pm(A) at M={M}, A={A}, ell={ell}")
                if wtA > 0 and hits == ell * wtA:
                    extremal_attained[ell] = True
                dyadic_cases += 1

            # Multi-radix 2^s check: s = 2 (base 4, r = 1, 2) and s = 3 (base 8, r = 1)
            for s, r_vals in ((2, (1, 2)), (3, (1,))):
                Ns = M // s
                for r in r_vals:
                    ell = s * r
                    lo = Fraction(2, 3 << ell)
                    hi = 1 - lo
                    hits_s = 0
                    for m in range(Ns):
                        rem = (A << (s * m)) % den
                        pt = Fraction(rem, den)
                        if lo <= pt <= hi:
                            hits_s += 1
                    check(hits_s <= r * wtA, f"Multi-radix 2^{s} count <= r*w_pm at M={M}, A={A}, r={r}")
                    dyadic_cases += 1

    check(all(extremal_attained.values()), "Upper bound hits == ell*w_pm(A) is attained for ell = 1, 2, 3")

    # 1d. Algebraic comparison: for every m >= 2, NAF bound at ell = 2(m-1) strictly dominates
    #     GF-36 Theorem 7.1 at window m (same slope -2(m-1)rho, strictly larger intercept).
    for m in range(2, 20):
        ell = 2 * (m - 1)
        ic_gf36 = 1 - Fraction(1, 1 << (m - 1))
        ic_naf = 1 - Fraction(4, 3 << ell)
        check(ic_naf > ic_gf36, f"NAF intercept strictly beats GF-36 at m={m}")
    # Check exact unimodality crossovers: g_{ell+1}(rho) - g_ell(rho) = (2/3)*2^{-ell} - rho.
    for ell in range(1, 12):
        cross = Fraction(2, 3 << ell)
        g_ell = 1 - Fraction(4, 3 << ell) - ell * cross
        g_next = 1 - Fraction(4, 3 << (ell + 1)) - (ell + 1) * cross
        check(g_ell == g_next, f"Exact crossover at rho = (2/3)*2^(-{ell})")

    print(f"[exact] NAF equivalence w_NAF = signedWeight verified for all A in [-8192, 8192];")
    print(f"        brute-force w_min = w_NAF verified on [-127, 127] (all 3^8 distinct-exponent signed strings on 8 positions);")
    print(f"        finite dyadic & multi-radix (base 2, 4, 8) geometric bounds verified on {dyadic_cases} cases")
    print(f"        (A in [-512, 512] + special values; tightness hits == ell*w_pm(A) attained for ell = 1, 2, 3; GF-36 dominance verified).")


# ===========================================================================
# Section 2: Theorem B -- E_+(2^k) Re-Certifications, Order-4 & DP-Free Majorants
# ===========================================================================

def section2_eplus_certificates():
    head("Section 2 [encl]: E_+(2^k) Pure int/Fraction Re-Certifications & DP-Free Lean Majorants")

    # 2a. Independent re-certification of GF-40 Thm 3.1(a) (Phase 24 Track E) pure-Fraction enclosure
    #     (P=600, U_cap=512, K2=24)
    P_LIM = 600
    ODD_P = [p for p in get_primes(P_LIM) if p > 2]
    U_CAP = 512
    dist = {1: Fraction(1)}
    rem_p = Fraction(0)
    rem_u_hi = Fraction(0)
    for p in ODD_P:
        K = 10 if p <= 29 else (6 if p <= 100 else 4)
        x = Fraction(1, p)
        loc = {}
        u_sum = Fraction(0)
        for e in range(K):
            pr = (1 - x) * (x ** e)
            o = odd_part(e + 1)
            loc[o] = loc.get(o, Fraction(0)) + pr
            u_sum += pr * o
        p_tail = x ** K
        u_tail = (x ** K) * (K + Fraction(p, p - 1))
        L_hi = u_sum + u_tail
        new_dist = {}
        new_rem_u = rem_u_hi * L_hi
        new_rem_p = rem_p + (1 - rem_p) * p_tail
        for u, pr in dist.items():
            new_rem_u += pr * u * u_tail
            for o, lpr in loc.items():
                uo = u * o
                if uo <= U_CAP:
                    new_dist[uo] = new_dist.get(uo, Fraction(0)) + pr * lpr
                else:
                    new_rem_p += pr * lpr
                    new_rem_u += pr * lpr * uo
        dist = new_dist
        rem_p = new_rem_p
        rem_u_hi = new_rem_u

    # Explicit verification of the three tail constants for V = prod_{p > P_LIM} odd(e_p + 1) (P_LIM = 600):
    # (1) Every odd integer n = 2m + 1 >= 601 obeys 1/n^2 < (1/2)*(1/(n-1) - 1/(n+1)), so telescoping gives
    #     Pr(V != 1) <= sum_{p > 600} p^{-2} < 1/(2 * 600) = 1/1200.
    for n in range(P_LIM + 1, P_LIM + 20, 2):
        check(Fraction(1, n * n) < Fraction(1, 2) * (Fraction(1, n - 1) - Fraction(1, n + 1)),
              f"Odd telescoping 1/{n}^2 < (1/2)(1/{n-1} - 1/{n+1})")
    S2_600_tel = Fraction(1, 2 * P_LIM)
    check(inv_sq_above(P_LIM) < S2_600_tel, "Certified sum_{p>600} p^-2 < 1/1200", "encl")
    # (2) For p >= 601, odd(e+1) - 1 <= e for all e >= 2, so l_odd(p) - 1 <= (1 - 1/p) sum_{e>=2} e p^{-e}
    #     = (2 + 1/(p-1)) p^{-2} <= (2 + 1/600) p^{-2} = (1201/600) p^{-2}.
    #     Hence S_V := sum_{p>600} (l_odd(p) - 1) < (1201/600) * (1/1200) = 1201/720000, and
    #     E[V] <= 1 / (1 - S_V) = 720000/718799 < 1 + 2/600.
    S_V_hi = Fraction(2 * P_LIM + 1, P_LIM) * S2_600_tel
    E_V_hi = Fraction(1, 1) / (1 - S_V_hi)
    check(E_V_hi < 1 + Fraction(2, P_LIM), "GF-40 tail bound E[V] <= 1/(1 - S_V) < 1 + 2/600", "encl")
    # (3) E[V * 1_{V != 1}] = (E[V] - 1) + Pr(V != 1) < (E_V_hi - 1) + 1/1200 < 5/1200 = 5/(2*P_LIM).
    check((E_V_hi - 1) + S2_600_tel < Fraction(5, 2 * P_LIM),
          "GF-40 tail bound E[V * 1_{V != 1}] < 5/1200", "encl")
    E_U_lo = sum(u * pr for u, pr in dist.items())
    E_U_hi = E_U_lo + rem_u_hi
    tail_p_hi = Fraction(1, 2 * P_LIM)
    tail_U_hi = E_U_hi * Fraction(5, 2 * P_LIM)
    E_U_full_hi = E_U_hi * (1 + Fraction(2, P_LIM))

    K2 = 24
    WE_lo = Fraction(0)
    WE_hi = Fraction(0)
    # e = 0: |1-e| = 1, pr = 1/2; e = 1: a_+ = 0; e >= 2: |1-e| = e-1, pr = 2^{-(e+1)}
    for e in [0] + list(range(2, K2)):
        pr2 = Fraction(1, 1 << (e + 1))
        o2 = odd_part(abs(1 - e))
        lo_e = sum(wpm(u * o2) * pr for u, pr in dist.items()) * (1 - tail_p_hi)
        hi_e = sum(wpm(u * o2) * pr for u, pr in dist.items()) + wpm(o2) * (rem_u_hi + tail_U_hi)
        WE_lo += pr2 * lo_e
        WE_hi += pr2 * hi_e
    WE_hi += Fraction(K2, 1 << K2) * E_U_full_hi

    check(Fraction(907252, 10 ** 6) <= WE_lo and WE_hi <= Fraction(912845, 10 ** 6),
          "Independent GF-40 Thm 3.1(a) re-certification: W_+ in [0.907252, 0.912845]", "encl")
    D_E_exact = Fraction(2, 3) - Fraction(2, 3) * Fraction(912845, 10 ** 6)
    check(D_E_exact == Fraction(17431, 300000), "Exact GF-40-input D^- = 17431/300000", "encl")
    D_E_actual = Fraction(2, 3) - Fraction(2, 3) * WE_hi
    check(D_E_actual >= D_E_exact, "Actual GF-40-input D^- >= 17431/300000", "encl")

    # 2b. Independent re-certification of GF-36 Thm 7.2 (Phase 24 Track A) tight enclosure
    #     (scaled int, Y=200000, y=20000)
    Y_A = 200000
    y_A = 20000
    ps_A = get_primes(Y_A)
    wpe = lambda e: wpm(e + 1)
    odd_p = lambda p: p != 2
    epW = CertifiedEulerProduct(wpe, ps_A, Y_A, (1, 1), odd_p, keep=y_A)
    Wodd_lo, Wodd_hi = epW.bounds()

    # Exact 2-adic factor: sum_{e>=0} w_pm(|1-e|) 2^{-(e+1)}
    E2_A = 120
    two_lo = sum(Fraction(wpm(abs(1 - e)), 1 << (e + 1)) for e in range(E2_A + 1))
    # Tail e > E2_A: w_pm(e-1) <= e-1; sum_{e >= E2_A+1} (e-1) 2^{-(e+1)} = (E2_A + 1) 2^{-(E2_A + 1)}
    two_tail = Fraction(E2_A + 1, 1 << (E2_A + 1))
    two_hi = two_lo + two_tail
    Wmaj_lo = two_lo * Wodd_lo
    Wmaj_hi = two_hi * Wodd_hi
    check(Fraction(936414, 10 ** 6) <= Wmaj_lo and Wmaj_hi <= Fraction(936415, 10 ** 6),
          "Pure multiplicative W_+^maj (GF-36 Thm 7.2) in [0.936414, 0.936415]", "encl")
    check(Wmaj_hi < Fraction(15, 16), "Pure multiplicative W_+^maj < 15/16 (already proves Order 4!)", "encl")

    init_states = []
    for e in range(E2_A + 1):
        if e == 1:
            continue
        pr = ONE >> (e + 1)
        init_states.append((odd_part(abs(1 - e)), pr, pr))
    frozen_hi = cdiv(frac_up(two_tail) * epW.hi, ONE)
    WA_lo, WA_hi = certified_model_dp(
        wpm, lambda e: odd_part(e + 1), epW,
        {"states": init_states, "frozen_hi": frozen_hi}, odd_p, ps_A, y_A, thr_bits=60
    )
    check(Fraction(908174, 10 ** 6) <= WA_lo and WA_hi <= Fraction(908184, 10 ** 6),
          "Independent GF-36 Thm 7.2 re-certification: W_+ in [0.908174, 0.908184]", "encl")
    # Also check consistency between GF-40 and GF-36 enclosures (nonempty intersection!)
    check(max(WE_lo, WA_lo) <= min(WE_hi, WA_hi), "GF-40 and GF-36 enclosures overlap cleanly", "encl")

    D_A_from_pub = Fraction(2, 3) - Fraction(2, 3) * Fraction(908184, 10 ** 6)
    check(D_A_from_pub == Fraction(11477, 187500), "Exact GF-36-input D^- = 11477/187500", "encl")
    D_A_actual, ell_A = best_naf_discrepancy(WA_hi / 3, s=1)
    check(ell_A == 2 and D_A_actual >= D_A_from_pub, "Optimal ell=2 and D^- >= 11477/187500", "encl")

    # Compare against GF-40's exact A_16 bound: A_16 = 324039 / 1048576
    A16 = Fraction(1, 3) - (Fraction(7) - Fraction(-1, 2) ** 15) / (18 * 16)
    check(A16 == Fraction(324039, 1048576), "Exact GF-40 A_16 = 324039/1048576")
    D_GF40 = (A16 - Fraction(912845, 3 * 10 ** 6)) / ((1 << 16) * A16)
    check(D_E_exact > 247000 * D_GF40, "GF-40-input NAF transfer > 247,000x GF-40", "encl")
    check(D_A_from_pub > 261000 * D_GF40, "GF-36-input NAF transfer > 261,000x GF-40", "encl")
    check(D_A_from_pub > Fraction(261000) * Fraction(234, 10 ** 9), "GF-36-input NAF transfer > 261,000x 2.34e-7", "encl")

    # Binary order-4 nonnormality & base-4 order-2 nonnormality of E_+(8)
    check(Fraction(3, 16) > Fraction(1, 6) and Fraction(13, 16) < Fraction(5, 6),
          "[3/16, 13/16) strictly inside (1/6, 5/6)")
    check(Fraction(3, 16) - Fraction(1, 6) == Fraction(1, 48) > Fraction(1, 64),
          "Left/right margin 1/48 > 2^-6 (fixed R=6 suffices)")
    check(2 * WA_hi / 3 < Fraction(5, 8), "E_+(8) binary order-4 & base-4 order-2 nonnormality", "encl")
    check(2 * WE_hi / 3 < Fraction(5, 8), "E_+(8) order-4 nonnormality even from GF-40 input", "encl")

    # Base-4 and base-8 simple nonnormality of E_+(2^k) for ALL k >= 4!
    check(2 * WA_hi / 4 < Fraction(1, 2), "E_+(16) simply nonnormal in base 4 (and all k >= 4)", "encl")
    check(3 * WA_hi / 4 < Fraction(3, 4), "E_+(16) simply nonnormal in base 8 (and all k >= 4)", "encl")
    check(WA_hi < Fraction(15, 16), "E_+(32) simply nonnormal in base 32 (5*W/5 = W < 1 - 1/16)", "encl")

    # 2c. Elementary DP-free squarefull majorants < 93/100 for Lean 4 formalization!
    # Reuses DigitMassTransfer.lean's exact localBound B(p) = (1 - p^-2)^-1 - p^-3 - 2 p^-7 for odd primes!
    def B_lean(p):
        x = Fraction(1, p)
        return Fraction(1, 1 - x * x) - x ** 3 - 2 * (x ** 7)

    # Verify B_lean(p) >= (1 - 1/p) sum_{e>=0} s_2(e+1) p^{-e} >= local w_pm factor (already in Lean)
    # and check elementary +-1 mod 6 prime tail bound:
    # For M >= 1, every prime p >= 6M - 1 satisfies p = 6m - 1 or 6m + 1 (m >= M).
    # Since 1/(6m-1)^2 < (1/6)(1/(6m-7) - 1/(6m-1)) and 1/(6m+1)^2 < (1/6)(1/(6m-5) - 1/(6m+1)),
    # sum_{p >= 6M-1} 1/p^2 < (1/6)(1/(6M-7) + 1/(6M-5)) < 1 / (3*(6M - 7)).
    # Verify algebraic inequalities for small m >= 2:
    for m in range(2, 50):
        check(Fraction(1, (6 * m - 1) ** 2) < Fraction(1, 6) * (Fraction(1, 6 * m - 7) - Fraction(1, 6 * m - 1)),
              f"6m-1 telescoping at m={m}")
        check(Fraction(1, (6 * m + 1) ** 2) < Fraction(1, 6) * (Fraction(1, 6 * m - 5) - Fraction(1, 6 * m + 1)),
              f"6m+1 telescoping at m={m}")

    # Tier A (DP-free {2, 3}-coupled squarefull majorant):
    # G_{2,3}(2^{e2} 3^{e3} m) = w_pm(|1 - e2|*(e3 + 1)) * prod_{p>=5} s_2(v_p(m) + 1)
    # Verify pointwise majorization w_pm(a_+(n)) <= G_{2,3}(n) for all 1 <= n <= 20000!
    N_MAJ = 20000
    spf = list(range(N_MAJ + 1))
    for i in range(2, isqrt(N_MAJ) + 1):
        if spf[i] == i:
            for j in range(i * i, N_MAJ + 1, i):
                if spf[j] == j:
                    spf[j] = i
    for n in range(1, N_MAJ + 1):
        tmp = n
        e2 = 0
        while tmp % 2 == 0:
            tmp //= 2
            e2 += 1
        e3 = 0
        while tmp % 3 == 0:
            tmp //= 3
            e3 += 1
        tau_ge5 = 1
        s2_ge5 = 1
        while tmp > 1:
            p = spf[tmp]
            e = 0
            while tmp % p == 0:
                tmp //= p
                e += 1
            tau_ge5 *= (e + 1)
            s2_ge5 *= (e + 1).bit_count()
        a_n = (1 - e2) * (e3 + 1) * tau_ge5
        g23_n = wpm(abs(1 - e2) * (e3 + 1)) * s2_ge5
        check(wpm(a_n) <= g23_n, f"Pointwise w_pm(a_+(n)) <= G_{{2,3}}(n) at n={n}")

    # Exact rational upper bound on L_{2,3} with E2 = 18, E3 = 14:
    E2_m, E3_m = 18, 14
    L23_lo = Fraction(0)
    for e2 in range(E2_m):
        p2 = Fraction(1, 1 << (e2 + 1))
        for e3 in range(E3_m):
            p3 = Fraction(2, 3 ** (e3 + 1))
            L23_lo += p2 * p3 * wpm(abs(1 - e2) * (e3 + 1))
    # Verify exact geometric tail formulas by subtracting finite prefixes from closed-form full moments:
    check(Fraction(1, 1) - sum(Fraction(abs(1 - e), 1 << (e + 1)) for e in range(E2_m)) == Fraction(E2_m, 1 << E2_m),
          "Exact 2-adic tail identity for L_{2,3}")
    check(Fraction(3, 2) - sum(Fraction(2 * (e + 1), 3 ** (e + 1)) for e in range(E3_m)) == Fraction(1, 3 ** E3_m) * (E3_m + Fraction(3, 2)),
          "Exact 3-adic tail identity for L_{2,3}")
    check(Fraction(5, 4) - sum(Fraction(4 * (e + 1), 5 ** (e + 1)) for e in range(10)) == Fraction(1, 5 ** 10) * (10 + Fraction(5, 4)),
          "Exact 5-adic tail identity for L_{2,3,5}")
    tail_L23 = Fraction(E2_m, 1 << E2_m) * Fraction(3, 2) + Fraction(1, 3 ** E3_m) * (E3_m + Fraction(3, 2))
    L23_hi = L23_lo + tail_L23

    # Using P_cut = 211 (= 6*35 + 1; all primes >= 211 lie in {6m+-1 : m >= 35} with 6*35 - 7 = 203):
    # More cleanly take M_tail = 36 so 6*36 - 1 = 215 > 211 (45 primes 5 <= p <= 211!):
    ps_211 = [p for p in get_primes(211) if p >= 5]
    check(len(ps_211) == 45, "Exactly 45 primes in [5, 211]")
    prod_B_211 = Fraction(1)
    for p in ps_211:
        prod_B_211 *= B_lean(p)
    # Every prime p > 211 has p >= 223 >= 6*36 - 1 = 215, so sum_{p > 211} p^-2 <= 1/(3*(215 - 6)) = 1/627
    S2_211 = Fraction(1, 3 * (215 - 6))
    tail_211 = Fraction(1, 1) / (1 - S2_211)
    M23_hi_mod6 = L23_hi * prod_B_211 * tail_211
    check(M23_hi_mod6 < Fraction(93, 100), "DP-free G_{2,3} (45 primes p<=211, mod-6 tail) < 93/100", "encl")

    # Also with the trivial DigitMassTransfer.lean tail 1/(P-1) (no mod-6 lemma needed!) at P_cut = 601 (107 primes):
    ps_600 = [p for p in get_primes(600) if p >= 5]
    check(len(ps_600) == 107, "Exactly 107 primes in [5, 600]")
    prod_B_600 = Fraction(1)
    for p in ps_600:
        prod_B_600 *= B_lean(p)
    M23_hi_triv = L23_hi * prod_B_600 * Fraction(600, 599)
    check(M23_hi_triv < Fraction(93, 100), "DP-free G_{2,3} (107 primes p<601, trivial tail) < 93/100", "encl")

    # Tier B (Ultra-compact DP-free {2, 3, 5}-coupled majorant: ONLY 12 primes 7 <= p <= 47 with mod-6 tail,
    #         OR 26 primes 7 <= p <= 109 with trivial 1/(P-1) tail!):
    E2_5, E3_5, E5_5 = 16, 12, 10
    L235_lo = Fraction(0)
    for e2 in range(E2_5):
        p2 = Fraction(1, 1 << (e2 + 1))
        for e3 in range(E3_5):
            p3 = Fraction(2, 3 ** (e3 + 1))
            for e5 in range(E5_5):
                p5 = Fraction(4, 5 ** (e5 + 1))
                L235_lo += p2 * p3 * p5 * wpm(abs(1 - e2) * (e3 + 1) * (e5 + 1))
    # Moments of |1-e2|, e3+1, e5+1: 1, 3/2, 5/4
    # Tail for e5 >= E5_5: sum_{e>=E} (e+1)(4/5) 5^{-e} = 5^{-E} * (E + 5/4)
    tail_L235 = (
        Fraction(E2_5, 1 << E2_5) * Fraction(3, 2) * Fraction(5, 4)
        + Fraction(1, 3 ** E3_5) * (E3_5 + Fraction(3, 2)) * Fraction(5, 4)
        + Fraction(1, 5 ** E5_5) * (E5_5 + Fraction(5, 4)) * Fraction(3, 2)
    )
    L235_hi = L235_lo + tail_L235
    ps_47 = [p for p in get_primes(47) if p >= 7]  # 12 primes!
    check(len(ps_47) == 12, "Exactly 12 primes in [7, 47]")
    prod_B_47 = Fraction(1)
    for p in ps_47:
        prod_B_47 *= B_lean(p)
    # Next prime after 47 is 53 = 6*9 - 1, so sum_{p >= 53} p^-2 <= 1/(3*(53 - 6)) = 1/141
    M235_hi_mod6 = L235_hi * prod_B_47 / (1 - Fraction(1, 3 * (53 - 6)))
    check(M235_hi_mod6 < Fraction(93, 100), "DP-free G_{2,3,5} (12 primes p<=47, mod-6 tail) < 93/100", "encl")

    ps_109 = [p for p in get_primes(109) if p >= 7]  # 26 primes!
    check(len(ps_109) == 26, "Exactly 26 primes in [7, 109]")
    prod_B_109 = Fraction(1)
    for p in ps_109:
        prod_B_109 *= B_lean(p)
    M235_hi_triv = L235_hi * prod_B_109 * Fraction(112, 111)  # next prime >= 113
    check(M235_hi_triv < Fraction(93, 100), "DP-free G_{2,3,5} (26 primes p<=109, trivial tail) < 93/100", "encl")

    # Verify exact Lean target inequalities from C <= 93/100:
    C_lean = Fraction(93, 100)
    check(Fraction(2, 3) - Fraction(2, 3) * C_lean == Fraction(7, 150), "Lean D^-(E_+(8); 2) >= 7/150")
    check(Fraction(2, 3) * C_lean == Fraction(31, 50) < Fraction(5, 8), "Lean Order-4: 62/100 < 5/8")

    print(f"[encl] GF-40 Thm 3.1(a) re-certified (pure Fraction, P=600): W_+ in {fmt_iv((WE_lo, WE_hi))}")
    print(f"       -> D^-(E_+(8); 2) >= {D_E_exact} = {fmt_dn(D_E_exact, 7)} (actual >= {fmt_dn(D_E_actual, 7)})")
    print(f"[encl] GF-36 Thm 7.2 re-certified (scaled int, Y={Y_A}, y={y_A}): W_+ in {fmt_iv((WA_lo, WA_hi))}")
    print(f"       -> D^-(E_+(8); 2), D^-(E_+(8); 4) >= {D_A_from_pub} = {fmt_dn(D_A_from_pub, 7)} (actual >= {fmt_dn(D_A_actual, 7)})")
    print(f"       -> GF-40 ratio: GF-40 input = {int(D_E_exact / D_GF40)}x, GF-36 input = {int(D_A_from_pub / D_GF40)}x")
    print(f"[encl] DP-free majorants for Lean 4:")
    print(f"       Pure multiplicative W_+^maj in {fmt_iv((Wmaj_lo, Wmaj_hi))} (< 15/16 = 0.9375 -> D^- >= 1/24, Order 4!)")
    print(f"       G_{{2,3}}   (45 primes p<=211, mod-6 tail): <= {fmt_up(M23_hi_mod6, 6)} < 93/100 (-> D^- >= 7/150, Order 4!)")
    print(f"       G_{{2,3}}   (107 primes p<601, triv tail) : <= {fmt_up(M23_hi_triv, 6)} < 93/100")
    print(f"       G_{{2,3,5}} (12 primes p<=47,  mod-6 tail): <= {fmt_up(M235_hi_mod6, 6)} < 93/100")
    print(f"       G_{{2,3,5}} (26 primes p<=109, triv tail) : <= {fmt_up(M235_hi_triv, 6)} < 93/100")

    # Full table for E_+(2^k) across k = 3, 4, 5, 6, 8, 10, 16, 32, 64
    print("[encl] E_+(2^k) discrepancy & order table (using certified W_+ <= " + fmt_up(WA_hi, 6) + "):")
    print("       k   rho=W_+/k   D-(.;2) [ell*]   D-(.;4) [r*]   D-(.;8) [best]   D-(.;2^k) [best]  excl.ord(b=2)")
    for k in (3, 4, 5, 6, 8, 10, 16, 32, 64):
        rho = WA_hi / k
        d2, l2 = best_naf_discrepancy(rho, s=1)
        d4, r4 = best_naf_discrepancy(rho, s=2)
        d8_dir, r8 = best_naf_discrepancy(rho, s=3)
        d8_desc = Fraction(3, 7) * d2
        d8 = max(d8_dir, d8_desc)
        dk_dir, rk = best_naf_discrepancy(rho, s=k)
        dk_desc = Fraction(k, (1 << k) - 1) * d2
        dk = max(dk_dir, dk_desc)
        ord2 = lowest_excluded_order(rho, s=1)
        check(d2 > 0 and d4 > 0 and d8 > 0 and dk > 0, f"Positive D^- for E_+(2^{k})", "encl")
        # Verify NAF geometric transfer strictly beats GF-36 Thm 7.2 for every k >= 4
        if k >= 4:
            gf36_best = max(1 - Fraction(2, 1 << m) - (m - 1) * 2 * rho for m in range(2, 16))
            check(d2 > gf36_best, f"NAF transfer strictly dominates GF-36 at k={k}", "encl")
        print(f"      {k:2d}   {fmt_up(rho, 6)}    {fmt_dn(d2, 6)}  [{l2:2d}]    {fmt_dn(d4, 6)} [{r4:2d}]   "
              f"{fmt_dn(d8, 6)}         {fmt_dn(dk, 6)}          L={ord2[0]}")
    return (WE_lo, WE_hi), (WA_lo, WA_hi)


# ===========================================================================
# Section 3: Exact LP Minimum & Sharp Order-3 Barrier Witnesses (x_*, x_4)
# ===========================================================================

def solve_lp_min_exact(c, A_eq, b_eq):
    """Two-phase exact Fraction simplex minimizing c.x s.t. A_eq x = b_eq, x >= 0."""
    m = len(A_eq)
    n = len(c)
    A = [row[:] for row in A_eq]
    b = b_eq[:]
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]
    tab = [[Fraction(v) for v in A[i]] + [Fraction(1 if j == i else 0) for j in range(m)] + [Fraction(b[i])]
           for i in range(m)]
    basis = [n + i for i in range(m)]
    obj = [Fraction(0)] * n + [Fraction(1)] * m + [Fraction(0)]
    for i in range(m):
        for j in range(n + m + 1):
            obj[j] -= tab[i][j]

    def simplex(T, ob, bas, ncols):
        while True:
            enter = next((j for j in range(ncols) if ob[j] < 0), None)
            if enter is None:
                return ob
            leave = None
            best_r = None
            for i in range(len(T)):
                if T[i][enter] > 0:
                    r = T[i][-1] / T[i][enter]
                    if best_r is None or r < best_r or (r == best_r and bas[i] < bas[leave]):
                        best_r = r
                        leave = i
            assert leave is not None
            piv = T[leave][enter]
            T[leave] = [v / piv for v in T[leave]]
            for i in range(len(T)):
                if i != leave and T[i][enter] != 0:
                    fac = T[i][enter]
                    T[i] = [T[i][j] - fac * T[leave][j] for j in range(len(T[i]))]
            if ob[enter] != 0:
                fac = ob[enter]
                ob = [ob[j] - fac * T[leave][j] for j in range(len(ob))]
            bas[leave] = enter

    obj = simplex(tab, obj, basis, n + m)
    check(obj[-1] == 0, "LP Phase I feasible")
    for i in range(m):
        if basis[i] >= n:
            piv_col = next((j for j in range(n) if tab[i][j] != 0), None)
            if piv_col is not None:
                piv = tab[i][piv_col]
                tab[i] = [v / piv for v in tab[i]]
                for ii in range(m):
                    if ii != i and tab[ii][piv_col] != 0:
                        fac = tab[ii][piv_col]
                        tab[ii] = [tab[ii][j] - fac * tab[i][j] for j in range(len(tab[ii]))]
                basis[i] = piv_col
    keep = [i for i in range(m) if basis[i] < n]
    tab2 = [tab[i][:n] + [tab[i][-1]] for i in keep]
    basis2 = [basis[i] for i in keep]
    obj2 = [Fraction(v) for v in c] + [Fraction(0)]
    for i, bi in enumerate(basis2):
        if obj2[bi] != 0:
            fac = obj2[bi]
            obj2 = [obj2[j] - fac * tab2[i][j] for j in range(n + 1)]
    obj2 = simplex(tab2, obj2, basis2, n)
    x = [Fraction(0)] * n
    for i, bi in enumerate(basis2):
        x[bi] = tab2[i][-1]
    return sum(c[j] * x[j] for j in range(n)), x


def section3_order3_barrier():
    head("Section 3 [exact]: Exact Order-L NAF Minimum & Sharp Order-3 Barrier Witnesses")

    # 3a. Exact LP minimum signed-digit density for L-normal shift-invariant measures (L = 1..4)
    expected_min = {1: Fraction(0), 2: Fraction(1, 4), 3: Fraction(1, 4), 4: Fraction(5, 16)}
    for L in (1, 2, 3, 4):
        states = [(d, h) for d in (-1, 0, 1) for h in range(1 << (L - 1))]
        st_idx = {s: i for i, s in enumerate(states)}
        edges = []
        for d, h in states:
            for b in (0, 1):
                w = (h << 1) | b
                nh = w & ((1 << (L - 1)) - 1) if L > 1 else 0
                for dp in (-1, 0, 1):
                    a = b + 2 * d - dp
                    if -1 <= a <= 1:
                        edges.append((st_idx[(d, h)], st_idx[(dp, nh)], w, 1 if a != 0 else 0))
        A_eq, b_eq = [], []
        for s in range(len(states)):
            row = [0] * len(edges)
            for ei, (u, v, w, cost) in enumerate(edges):
                if u == s:
                    row[ei] += 1
                if v == s:
                    row[ei] -= 1
            if any(row):
                A_eq.append(row)
                b_eq.append(Fraction(0))
        for w in range(1 << L):
            A_eq.append([1 if e[2] == w else 0 for e in edges])
            b_eq.append(Fraction(1, 1 << L))
        val, _ = solve_lp_min_exact([Fraction(e[3]) for e in edges], A_eq, b_eq)
        check(val == expected_min[L], f"Exact LP min NAF density for {L}-normal == {expected_min[L]}")

    # 3b. Explicit irrational 3-normal witness x_* = 0. prod_{m>=1} (0001)^m (1110)^m
    #     Verify exact block NAF formula, zero-overhead cumulative w_pm(floor(2^{S_M} x_*)) = S_M / 4,
    #     and exact 3-word frequencies = 1/8 + O(1/sqrt(N)).
    bits = []
    prefix_int = 0
    for m in range(1, 41):
        block_bits = [0, 0, 0, 1] * m + [1, 1, 1, 0] * m
        Bm = 0
        for b in block_bits:
            Bm = (Bm << 1) | b
        # Exact closed-form NAF of Bm: sum_{j=1}^{m-1} 2^{4m+4j} + 2^{4m+1} - sum_{j=1}^{m-1} 2^{4j} - 2
        closed_Bm = sum(1 << (4 * m + 4 * j) for j in range(1, m)) + (1 << (4 * m + 1)) - sum(1 << (4 * j) for j in range(1, m)) - 2
        check(Bm == closed_Bm, f"Exact closed-form NAF identity for block B_{m}")
        check(wpm(Bm) == 2 * m, f"Exact block NAF weight w_pm(B_{m}) == 2*{m}")
        prefix_int = (prefix_int << (8 * m)) | Bm
        bits.extend(block_bits)
        SM = 4 * m * (m + 1)
        check(len(bits) == SM, f"Cumulative length S_{m} = 4*{m}*({m}+1)")
        check(wpm(prefix_int) == SM // 4, f"EXACT zero-overhead w_pm(floor(2^S_{m} x_*)) == S_{m}/4")

    # Verify all eight 3-word counts on x_* up to S_40 = 6560
    N_star = len(bits)
    cnt3 = [0] * 8
    for i in range(N_star - 2):
        cnt3[(bits[i] << 2) | (bits[i + 1] << 1) | bits[i + 2]] += 1
    for w in range(8):
        # Every 3-word count is within M = 40 of S_40 / 8 = 820
        check(abs(cnt3[w] - N_star // 8) <= 40, f"3-word count for {w:03b} within M of N/8")

    # 3c. Explicit 4-normal order-4 de Bruijn witness x_4 = 2479 / 65535 = 0.overline(0000100110101111)_2
    w4_int = 2479
    check(w4_int == (1 << 11) + (1 << 9) - (1 << 6) - (1 << 4) - 1, "Exact 5-term NAF of 2479")
    check(wpm(w4_int) == 5, "w_pm(2479) == 5")
    bits4 = [(w4_int >> (15 - i)) & 1 for i in range(16)]
    seen4 = set()
    for i in range(16):
        val4 = (bits4[i] << 3) | (bits4[(i + 1) % 16] << 2) | (bits4[(i + 2) % 16] << 1) | bits4[(i + 3) % 16]
        seen4.add(val4)
    check(len(seen4) == 16, "2479/65535 visits every length-4 binary word exactly once per period 16")
    rep = 0
    for m in range(1, 21):
        rep = (rep << 16) | w4_int
        check(wpm(rep) == 5 * m, f"Exact periodic NAF weight w_pm(floor(2^(16*{m}) x_4)) == 5*{m}")

    print("[exact] Exact LP min signed-digit density for L-normal measures: L=1 -> 0, L=2 -> 1/4, L=3 -> 1/4, L=4 -> 5/16.")
    print(f"[exact] Irrational 3-normal witness x_* verified through M=40 (S_40={N_star}):")
    print(f"        w_pm(floor(2^S_M x_*)) == S_M / 4 EXACTLY for all 1 <= M <= 40; 3-word counts = {cnt3}.")
    print("[exact] 4-normal de Bruijn witness x_4 = 2479/65535 verified: exact NAF weight 5m on 16m bits (m <= 20).")


# ===========================================================================
# Section 4: Theorem C -- Cubic Characters L_+(8), L_-(8), L_-(4) (mod 7, 9, 13, 19, 37)
# ===========================================================================

def cubic_char_table(M, g):
    """Return dict mapping a in (Z/MZ)* -> exponent t in {0, 1, 2} with chi(a) = omega^t."""
    tbl = {}
    a = 1
    while a not in tbl:
        tbl[a] = len(tbl) % 3
        a = (a * g) % M
    phi_M = sum(1 for x in range(1, M) if gcd(x, M) == 1)
    check(len(tbl) == phi_M, f"Generator {g} generates (Z/{M}Z)*")
    return tbl


def mul_eisenstein(u, v):
    """Multiply (a, b) representing a + b*omega in Z[omega], omega^2 + omega + 1 = 0."""
    a1, b1 = u
    a2, b2 = v
    # (a1 + b1 w)(a2 + b2 w) = (a1 a2 - b1 b2) + (a1 b2 + b1 a2 - b1 b2) w
    return (a1 * a2 - b1 * b2, a1 * b2 + b1 * a2 - b1 * b2)


def section4_cubic_characters():
    head("Section 4 [exact + encl]: Cubic-Character Classifications L_+(8), L_-(8), L_-(4)")

    # 4a. Exact cyclotomic verification of projections, phase table, signed weights,
    #     indicator expansion, and bounded partial sums of chi (zero external inputs!)
    # Six phases e^{i*pi*s/3} in Z[omega] basis (x, y) where z = x + y*omega:
    # s=0: 1=(1,0), s=1: 1+w=(1,1), s=2: w=(0,1), s=3: -1=(-1,0), s=4: -1-w=(-1,-1), s=5: -w=(0,-1)
    phase_xy = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]
    for s in range(6):
        z = (1, 0)
        for _ in range(s):
            z = mul_eisenstein(z, (1, 1))  # 1 + omega = e^{i*pi/3}
        check(z == phase_xy[s], f"Phase (1+w)^{s} == {phase_xy[s]}")
    plus_ph = [2 * x - y for x, y in phase_xy]
    minus_ph = [y for _, y in phase_xy]
    check(plus_ph == [2, 1, -1, -2, -1, 1], "Exact c_+/A phase table")
    check(minus_ph == [0, 1, 1, 0, -1, -1], "Exact c_-/A phase table")
    check(Fraction(sum(wpm(v) for v in plus_ph), 6) == Fraction(1, 1), "Phase average w_pm(c_+/A) = 1")
    check(Fraction(sum(wpm(v) for v in minus_ph), 6) == Fraction(2, 3), "Phase average w_pm(c_-/A) = 2/3")
    check(Fraction(sum(odd_part(v) for v in plus_ph), 6) == Fraction(1, 1), "Phase average odd(c_+/A) = 1")
    check(Fraction(sum(odd_part(v) for v in minus_ph), 6) == Fraction(2, 3), "Phase average odd(c_-/A) = 2/3")

    # Verify indicator expansion 1_{chi != 1} = 2/3 - (1/3) chi - (1/3) chi_bar on {1, omega, omega^2}
    # In Z[omega]: 1=(1,0), w=(0,1), w^2=(-1,-1). Notice w + w^2 = (-1, 0) = -1!
    for t, z in [(0, (1, 0)), (1, (0, 1)), (2, (-1, -1))]:
        zb = (z[0] - z[1], -z[1])  # conjugate of a + b*w is (a - b) - b*w
        # 3 * (2/3 - (1/3)z - (1/3)zb) = (2 - z_a - zb_a, -z_b - zb_b)
        val_re = 2 - z[0] - zb[0]
        val_im = -z[1] - zb[1]
        check(val_im == 0 and val_re == (0 if t == 0 else 3), f"Cubic indicator identity at t={t}")

    # Direct Dirichlet convolution check for M = 7 (g=3), M = 9 (g=2), M = 13 (g=2) through N = 4096
    N_CUB = 4096
    spf = list(range(N_CUB + 1))
    for i in range(2, isqrt(N_CUB) + 1):
        if spf[i] == i:
            for j in range(i * i, N_CUB + 1, i):
                if spf[j] == j:
                    spf[j] = i

    cubic_specs = [(7, 3), (9, 2), (13, 2)]
    omega_vec = [(1, 0), (0, 1), (-1, -1)]
    cubic_seqs = {}
    for M, g in cubic_specs:
        tbl = cubic_char_table(M, g)
        # Check exact zero-sum over one period and bounded partial sums |sum_{m'=1}^Z chi(m')| <= M
        # (using norm |a + b*w|^2 = a^2 - a*b + b^2 <= M^2)
        sa, sb = 0, 0
        for m in range(1, 3 * M + 1):
            t = tbl.get(m % M)
            if t is not None:
                sa += omega_vec[t][0]
                sb += omega_vec[t][1]
            norm_sq = sa * sa - sa * sb + sb * sb
            check(norm_sq <= M * M, f"Bounded partial sum |sum chi| <= {M} at m={m}")
            if m % M == 0:
                check(sa == 0 and sb == 0, f"Exact period zero-sum mod {M} at m={m}")

        # Compute (1 * chi)(n) by direct divisor sum and verify local factorization + w_pm formulas
        conv_a = [0] * (N_CUB + 1)
        conv_b = [0] * (N_CUB + 1)
        for d in range(1, N_CUB + 1):
            t = tbl.get(d % M)
            if t is not None:
                va, vb = omega_vec[t]
                for m in range(d, N_CUB + 1, d):
                    conv_a[m] += va
                    conv_b[m] += vb
        c_plus = [0] * (N_CUB + 1)
        c_minus = [0] * (N_CUB + 1)
        for n in range(1, N_CUB + 1):
            cp = 2 * conv_a[n] - conv_b[n]
            cm = conv_b[n]
            c_plus[n] = cp
            c_minus[n] = cm
            # Factor n to compute A(n), support indicator, stripped chi(n^circ), and majorant G_chi(n)
            tmp = n
            A_n = 1
            G_n = 1
            supp = True
            stripped = n
            while tmp > 1:
                p = spf[tmp]
                e = 0
                while tmp % p == 0:
                    tmp //= p
                    e += 1
                if M % p == 0:
                    stripped //= p ** e
                else:
                    t = tbl[p % M]
                    if t == 0:
                        A_n *= (e + 1)
                        G_n *= wpm(e + 1)
                    else:
                        if e % 3 == 2:
                            supp = False
                            G_n = 0
            chi_strip = tbl[stripped % M]
            # Exact signed-weight identities!
            check(wpm(cp) == (wpm(A_n) if supp else 0), f"Exact w_pm(c_+) identity mod {M} at n={n}")
            check(wpm(cm) == (wpm(A_n) if (supp and chi_strip != 0) else 0),
                  f"Exact w_pm(c_-) identity mod {M} at n={n}")
            check(wpm(cp) <= G_n, f"w_pm(c_+) <= G_chi mod {M} at n={n}")
            check(wpm(cm) <= (G_n if chi_strip != 0 else 0), f"w_pm(c_-) <= 1_{{chi!=1}} G_chi mod {M} at n={n}")
            check(abs(cp) <= 2 * A_n and abs(cm) <= A_n, f"|c_pm| <= 2 A_n mod {M} at n={n}")
        cubic_seqs[M] = (c_plus, c_minus)

    # 4b. Outward-rounded pure int/Fraction certification of delta, C_odd, W_chi (majorant),
    #     and W_{chi, true} (true NAF mean DP!) for M = 7, 9, 13 (plus bonus M = 19, 37, 31, 43).
    Y_C = 200000
    y_C = 10000
    ps_C = get_primes(Y_C)
    wpe = lambda e: wpm(e + 1)
    odde = lambda e: odd_part(e + 1)

    print("[encl] Certified cubic-character constants (pure int/Fraction outward rounding, ZERO external inputs):")
    cubic_certs = {}
    for M, g, gf31_bound in [(7, 3, Fraction(4, 5)), (9, 2, Fraction(21, 25)), (13, 2, Fraction(21, 25))]:
        tbl = cubic_char_table(M, g)
        cubes = {a for a, t in tbl.items() if t == 0}
        split_dom = lambda p, M=M, cubes=cubes: (M % p != 0) and (p % M in cubes)
        inert_dom = lambda p, M=M, cubes=cubes: (M % p != 0) and (p % M not in cubes)

        # Certify delta = prod_{chi(p) != 0, 1} (1 - 1/(p^2+p+1))
        d_lo = ONE
        d_hi = ONE
        for p in ps_C:
            if p > Y_C:
                break
            if inert_dom(p):
                den = p * p + p + 1
                num = den - 1
                d_lo = (d_lo * num) // den
                d_hi = cdiv(d_hi * num, den)
        # Tail for p > Y_C: each inert prime factor is in (1 - 1/p^2, 1), so prod_{p>Y_C} >= 1 - S2
        S2_C = inv_sq_above(Y_C)
        t_lo = 1 - S2_C
        delta_lo = fx_to_frac((d_lo * t_lo.numerator) // t_lo.denominator)
        delta_hi = fx_to_frac(d_hi)

        # Certify split-prime products for odd_part (C_odd) and w_pm (W_chi)
        ep_odd = CertifiedEulerProduct(odde, ps_C, Y_C, (1, 1), split_dom, keep=0)
        ep_w = CertifiedEulerProduct(wpe, ps_C, Y_C, (1, 1), split_dom, keep=y_C)
        Codd_lo = delta_lo * ep_odd.bounds()[0]
        Codd_hi = delta_hi * ep_odd.bounds()[1]
        Wchi_lo = delta_lo * ep_w.bounds()[0]
        Wchi_hi = delta_hi * ep_w.bounds()[1]

        # Certify true NAF mean W_{chi, true} = delta * E[w_pm(prod_{chi(p)=1} odd(e_p+1))]
        Ew_lo, Ew_hi = certified_model_dp(wpm, lambda e: odd_part(e + 1), ep_w, None, split_dom, ps_C, y_C, thr_bits=52)
        Wtrue_lo = delta_lo * Ew_lo
        Wtrue_hi = delta_hi * Ew_hi

        # Verify GF-31 bounds C_odd < 4/5 (mod 7), < 21/25 (mod 9, 13) AND implied L_-(4) exact fractions!
        check(Codd_hi < gf31_bound, f"Mod {M}: C_odd < {gf31_bound}", "encl")
        D_Lminus4_gf31 = Fraction(2, 3) - Fraction(2, 3) * gf31_bound  # 2/3 - 2 * ((2/3)*C_odd / 2) = 2/3 - (2/3) C_odd
        if M == 7:
            check(D_Lminus4_gf31 == Fraction(2, 15), "Mod 7 L_-(4) exact D^- >= 2/15 from C_odd < 4/5")
        else:
            check(D_Lminus4_gf31 == Fraction(8, 75), f"Mod {M} L_-(4) exact D^- >= 8/75 from C_odd < 21/25")

        # Verify tighter W_chi <= GF-36 Proposition 8.1 upper endpoints
        expected_wchi_hi = {7: Fraction(756905, 10 ** 6), 9: Fraction(804516, 10 ** 6), 13: Fraction(789314, 10 ** 6)}[M]
        check(Wchi_hi <= expected_wchi_hi, f"Mod {M}: W_chi <= {expected_wchi_hi}", "encl")
        check(Wtrue_hi <= Wchi_hi and Wchi_hi <= Codd_hi, f"Mod {M}: W_true <= W_chi <= C_odd", "encl")

        # Compute exact optimal discrepancy bounds & excluded orders for L_+(8), L_-(8), L_-(4)!
        # Note: L_+(8) has rho = W/3; L_-(4) has rho = (2/3 W)/2 = W/3 (IDENTICAL!); L_-(8) has rho = (2/3 W)/3 = 2W/9.
        rho_p8_maj = Wchi_hi / 3
        rho_p8_true = Wtrue_hi / 3
        rho_m8_maj = Fraction(2, 9) * Wchi_hi
        rho_m8_true = Fraction(2, 9) * Wtrue_hi

        D_p8_maj, l_p8 = best_naf_discrepancy(rho_p8_maj, s=1)
        D_p8_true, _ = best_naf_discrepancy(rho_p8_true, s=1)
        D_p8_b8_dir, _ = best_naf_discrepancy(rho_p8_maj, s=3)
        D_p8_b8 = max(D_p8_b8_dir, Fraction(3, 7) * D_p8_maj)
        D_p8_b8_true_dir, _ = best_naf_discrepancy(rho_p8_true, s=3)
        D_p8_b8_true = max(D_p8_b8_true_dir, Fraction(3, 7) * D_p8_true)

        D_m8_maj, l_m8 = best_naf_discrepancy(rho_m8_maj, s=1)
        D_m8_true, _ = best_naf_discrepancy(rho_m8_true, s=1)
        D_m8_b8_dir, _ = best_naf_discrepancy(rho_m8_maj, s=3)
        D_m8_b8 = max(D_m8_b8_dir, Fraction(3, 7) * D_m8_maj)
        D_m8_b8_true_dir, _ = best_naf_discrepancy(rho_m8_true, s=3)
        D_m8_b8_true = max(D_m8_b8_true_dir, Fraction(3, 7) * D_m8_true)

        ord_p8 = lowest_excluded_order(rho_p8_maj, s=1)
        ord_p8_b4 = lowest_excluded_order(rho_p8_maj, s=2)
        ord_m8 = lowest_excluded_order(rho_m8_maj, s=1)
        ord_m8_b4 = lowest_excluded_order(rho_m8_maj, s=2)
        ord_m8_b8 = lowest_excluded_order(rho_m8_maj, s=3)

        check(l_p8 == 2 and l_m8 == 2, f"Mod {M}: optimal ell = 2 for L_+(8), L_-(4), L_-(8)", "encl")
        check(D_p8_maj > D_Lminus4_gf31, f"Mod {M}: W_chi bound beats GF-31 C_odd bound on L_-(4)", "encl")
        check(D_p8_b8 > 0 and D_p8_b8_true >= D_p8_b8 and D_m8_b8 > 0 and D_m8_b8_true >= D_m8_b8,
              f"Mod {M}: uniform max(direct, descent) base-8 bounds positive and monotone", "encl")
        check(ord_p8[0] == 4 and ord_p8_b4[0] == 2, f"Mod {M}: L_+(8) & L_-(4) not 4-normal (b=2), not 2-normal (b=4)", "encl")
        check(ord_m8[0] == 2 and ord_m8_b4[0] == 1 and ord_m8_b8[0] == 1,
              f"Mod {M}: L_-(8) not 2-normal (b=2), simply nonnormal (b=4, b=8)", "encl")
        # Also verify L_+(4) remains above 1/3 (open)
        check(Wtrue_lo / 2 > Fraction(1, 3), f"Mod {M}: L_+(4) stays > 1/3 (honestly Open)", "encl")

        cubic_certs[M] = {
            "delta": (delta_lo, delta_hi), "C_odd": (Codd_lo, Codd_hi),
            "W_chi": (Wchi_lo, Wchi_hi), "W_true": (Wtrue_lo, Wtrue_hi),
            "D_p8_maj": D_p8_maj, "D_p8_true": D_p8_true,
            "D_p8_b8": D_p8_b8, "D_p8_b8_true": D_p8_b8_true,
            "D_m8_maj": D_m8_maj, "D_m8_true": D_m8_true,
            "D_m8_b8": D_m8_b8, "D_m8_b8_true": D_m8_b8_true,
        }
        print(f"       Mod {M:2d}: delta in {fmt_iv((delta_lo, delta_hi))}, C_odd in {fmt_iv((Codd_lo, Codd_hi))}")
        print(f"               W_chi in {fmt_iv((Wchi_lo, Wchi_hi))}, W_true in {fmt_iv((Wtrue_lo, Wtrue_hi))}")
        print(f"               L_+(8) & L_-(4): D-(.;2), D-(.;4) >= {fmt_dn(D_p8_maj, 6)} [W_chi] / {fmt_dn(D_p8_true, 6)} [W_true] (GF-31: {D_Lminus4_gf31})")
        print(f"               L_+(8) & L_-(4) base 8: D-(.;8) >= {fmt_dn(D_p8_b8, 6)} [W_chi] / {fmt_dn(D_p8_b8_true, 6)} [W_true]; excl. ord: L=4 (b=2), L=2 (b=4)")
        print(f"               L_-(8):          D-(.;2), D-(.;4) >= {fmt_dn(D_m8_maj, 6)} [W_chi] / {fmt_dn(D_m8_true, 6)} [W_true], D-(.;8) >= {fmt_dn(D_m8_b8, 6)} [W_chi] / {fmt_dn(D_m8_b8_true, 6)} [W_true]")
        print(f"                                excl. ord: L=2 (b=2), simply nonnormal in base 4 and base 8!")

    # 4c. Bonus higher cubic moduli M = 19, 37 (PASS k=2 for L_-(4) and k=3 for L_+(8)!) vs M = 31, 43 (FAIL > 1/3)
    print("[encl] Higher prime cubic moduli M = 19, 37 (newly classified at L_-(4), L_+(8)) vs M = 31, 43:")
    Y_B = 50000
    ps_B = get_primes(Y_B)
    S2_B = inv_sq_above(Y_B)
    for M in (19, 37, 31, 43):
        cubes = {pow(a, 3, M) for a in range(1, M)}
        split_dom = lambda p, M=M, cubes=cubes: (M % p != 0) and (p % M in cubes)
        inert_dom = lambda p, M=M, cubes=cubes: (M % p != 0) and (p % M not in cubes)
        d_lo = ONE
        d_hi = ONE
        for p in ps_B:
            if p > Y_B:
                break
            if inert_dom(p):
                den = p * p + p + 1
                d_lo = (d_lo * (den - 1)) // den
                d_hi = cdiv(d_hi * (den - 1), den)
        t_lo = 1 - S2_B
        delta_lo = fx_to_frac((d_lo * t_lo.numerator) // t_lo.denominator)
        delta_hi = fx_to_frac(d_hi)
        ep_w = CertifiedEulerProduct(wpe, ps_B, Y_B, (1, 1), split_dom, keep=0)
        W_lo = delta_lo * ep_w.bounds()[0]
        W_hi = delta_hi * ep_w.bounds()[1]
        if M in (19, 37):
            check(W_hi / 3 < Fraction(1, 3), f"Mod {M}: L_-(4) & L_+(8) fall below 1/3", "encl")
            d2, _ = best_naf_discrepancy(W_hi / 3, s=1)
            d8_dir, _ = best_naf_discrepancy(W_hi / 3, s=3)
            d8 = max(d8_dir, Fraction(3, 7) * d2)
            check(d8 > 0, f"Mod {M}: L_-(4) & L_+(8) base-8 bound D^-(.;8) > 0", "encl")
            ord2 = lowest_excluded_order(W_hi / 3, s=1)
            ord4 = lowest_excluded_order(W_hi / 3, s=2)
            check(ord2[0] == 4, f"Mod {M}: L_-(4) & L_+(8) not 4-normal in base 2", "encl")
            check(ord4[0] == 2, f"Mod {M}: L_-(4) & L_+(8) not 2-normal in base 4", "encl")
            print(f"       Mod {M:2d}: W_chi in {fmt_iv((W_lo, W_hi))} -> L_-(4), L_+(8): D-(.;2), D-(.;4) >= {fmt_dn(d2, 6)}, D-(.;8) >= {fmt_dn(d8, 6)}, NOT 4-normal (b=2), NOT 2-normal (b=4)")
        else:
            check(W_lo / 3 > Fraction(1, 3), f"Mod {M}: W_chi/3 > 1/3 (above threshold)", "encl")
            print(f"       Mod {M:2d}: W_chi in {fmt_iv((W_lo, W_hi))} -> W_chi/3 >= {fmt_dn(W_lo / 3, 6)} > 1/3 (L_-(4) Open)")

    return cubic_seqs, cubic_certs


# ===========================================================================
# Section 5: Other Dense Arithmetic Families Newly Below C/k < 1/3
# ===========================================================================

def section5_other_dense_families(WA_iv):
    head("Section 5 [exact + encl]: Other Dense Signed Families Newly Below C/k < 1/3")

    # 5a. Signed unitary Lambert series:
    #     E^*_+(2^k)     = sum_{m>=1} mu^2(m)/(2^{km}+1)         = sum a^*_+(n) 2^{-kn}
    #     E^*_{alt,+}(2^k)= sum_{m>=1} (-1)^{m-1} mu^2(m)/(2^{km}+1) = sum a^*_{alt,+}(n) 2^{-kn}
    # Exact formulas verified for all 1 <= n <= 4096:
    N_F = 4096
    mu2 = [1] * (N_F + 1)
    for d in range(2, isqrt(N_F) + 1):
        sq = d * d
        for m in range(sq, N_F + 1, sq):
            mu2[m] = 0
    spf = list(range(N_F + 1))
    for i in range(2, isqrt(N_F) + 1):
        if spf[i] == i:
            for j in range(i * i, N_F + 1, i):
                if spf[j] == j:
                    spf[j] = i

    def omega_odd(n):
        tmp = odd_part(n)
        c = 0
        while tmp > 1:
            p = spf[tmp]
            c += 1
            while tmp % p == 0:
                tmp //= p
        return c

    # Compute divisor convolutions directly for n <= 4096
    a_star_p = [0] * (N_F + 1)
    a_star_altp = [0] * (N_F + 1)
    a_odd_p = [0] * (N_F + 1)
    for d in range(1, N_F + 1):
        m2 = mu2[d]
        s_d = 1 if (d & 1) else -1
        for q in range(1, N_F // d + 1):
            n = d * q
            s_q = 1 if (q & 1) else -1
            if m2:
                a_star_p[n] += s_q
                a_star_altp[n] += s_d * s_q
            if d & 1:
                a_odd_p[n] += s_q

    for n in range(1, N_F + 1):
        e = v2(n)
        om = omega_odd(n)
        exp_sp = (1 << om) if e == 0 else (0 if e == 1 else -(1 << (om + 1)))
        exp_sap = (1 << om) if e == 0 else (-(1 << (om + 1)) if e == 1 else 0)
        check(a_star_p[n] == exp_sp, f"Exact a^*_+(n) formula at n={n}")
        check(a_star_altp[n] == exp_sap, f"Exact a^*_{{alt,+}}(n) formula at n={n}")
        check(wpm(a_star_p[n]) == (0 if e == 1 else 1), f"Exact w_pm(a^*_+(n)) at n={n}")
        check(wpm(a_star_altp[n]) == (1 if e <= 1 else 0), f"Exact w_pm(a^*_{{alt,+}}(n)) at n={n}")
        # Verify E_{+,odd}(2^k): a_{+,odd}(n) = (-1)^{n-1} tau_odd(n)
        tmp = odd_part(n)
        t_odd = 1
        while tmp > 1:
            p = spf[tmp]
            cnt = 0
            while tmp % p == 0:
                tmp //= p
                cnt += 1
            t_odd *= (cnt + 1)
        check(a_odd_p[n] == (t_odd if (n & 1) else -t_odd), f"Exact a_{{+,odd}}(n) = (-1)^(n-1) tau_odd(n) at n={n}")

    # Exact rational bounds for E^*_+(8) and E^*_{alt,+}(8): exact mean = 3/4 -> rho = 1/4 at k = 3!
    rho_sp8 = Fraction(3, 4) / 3
    check(rho_sp8 == Fraction(1, 4), "E^*_+(8) exact rho = 1/4")
    d2_sp8, _ = best_naf_discrepancy(rho_sp8, s=1)
    d4_sp8, _ = best_naf_discrepancy(rho_sp8, s=2)
    d8_sp8, _ = best_naf_discrepancy(rho_sp8, s=3)
    check(d2_sp8 == Fraction(1, 6) and d4_sp8 == Fraction(1, 6) and d8_sp8 == Fraction(1, 12),
          "E^*_+(8): D^-(.;2)=D^-(.;4) >= 1/6, D^-(.;8) >= 1/12")
    check(lowest_excluded_order(rho_sp8, s=1)[0] == 4 and lowest_excluded_order(rho_sp8, s=2)[0] == 2,
          "E^*_+(8) not 4-normal (b=2), not 2-normal (b=4)")
    # At k = 4: E^*_+(16) has rho = 3/16 < 1/4 -> not 2-normal in base 2, simply nonnormal in base 4 and 8!
    rho_sp16 = Fraction(3, 16)
    check(best_naf_discrepancy(rho_sp16, s=1)[0] == Fraction(7, 24), "E^*_+(16) D^-(.;2) >= 7/24")
    check(lowest_excluded_order(rho_sp16, s=1)[0] == 2 and lowest_excluded_order(rho_sp16, s=2)[0] == 1
          and lowest_excluded_order(rho_sp16, s=3)[0] == 1,
          "E^*_+(16) not 2-normal (b=2), simply nonnormal (b=4, b=8)")

    # 5b. Signed odd-divisor Lambert series E_{+,odd}(2^k) = sum_{m odd} 1/(2^{km}+1) at NEW k = 4!
    Y_F = 100000
    y_F = 5000
    ps_F = get_primes(Y_F)
    odd_p = lambda p: p != 2
    ep_odd_w = CertifiedEulerProduct(lambda e: wpm(e + 1), ps_F, Y_F, (1, 1), odd_p, keep=y_F)
    Wodd_maj = ep_odd_w.bounds()
    Wodd_true = certified_model_dp(wpm, lambda e: odd_part(e + 1), ep_odd_w, None, odd_p, ps_F, y_F, thr_bits=52)
    check(Wodd_maj[1] / 4 < Fraction(1, 3), "E_{+,odd}(16) passes < 1/3 even with DP-free majorant!", "encl")
    check(Wodd_true[0] / 3 > Fraction(1, 3), "E_{+,odd}(8) stays > 1/3 (k=3 Open)", "encl")
    d2_oddp16_maj, _ = best_naf_discrepancy(Wodd_maj[1] / 4, s=1)
    d2_oddp16_true, _ = best_naf_discrepancy(Wodd_true[1] / 4, s=1)
    check(lowest_excluded_order(Wodd_maj[1] / 4, s=1)[0] == 4, "E_{+,odd}(16) not 4-normal in base 2", "encl")

    # 5c. Signed higher-divisor series F_{2^k,+}(tau_r) = sum_{m>=1} tau_{r-1}(m)/(2^{km}+1), r = 4, 8, 16!
    # Verify exact multiplicative prime-power formula through n <= 1024 for r = 4:
    # At odd p: a(p^e) = tau_r(p^e) = comb(e+r-1, r-1);
    # At p = 2: a(2^e) = comb(e+r-2, r-2) - (comb(e+r-2, r-1) if e >= 1 else 0).
    N_T4 = 1024
    tau3 = [0] * (N_T4 + 1)
    for n in range(1, N_T4 + 1):
        tmp = n
        v = 1
        while tmp > 1:
            p = spf[tmp]
            e = 0
            while tmp % p == 0:
                tmp //= p
                e += 1
            v *= comb(e + 2, 2)
        tau3[n] = v
    a_t4p = [0] * (N_T4 + 1)
    for d in range(1, N_T4 + 1):
        td = tau3[d]
        for q in range(1, N_T4 // d + 1):
            a_t4p[d * q] += td if (q & 1) else -td
    for n in range(1, N_T4 + 1):
        e2 = v2(n)
        c2 = comb(e2 + 2, 2) - (comb(e2 + 2, 3) if e2 >= 1 else 0)
        tmp = odd_part(n)
        codd = 1
        while tmp > 1:
            p = spf[tmp]
            e = 0
            while tmp % p == 0:
                tmp //= p
                e += 1
            codd *= comb(e + 3, 3)
        check(a_t4p[n] == c2 * codd, f"Exact F_{{2^k,+}}(tau_4) coefficient formula at n={n}")

    # Certify outward-rounded majorants W_{tau_r, +}^{maj} for r = 4, 8, 16:
    Y_TR = 40000
    ps_TR = get_primes(Y_TR)
    tr_results = {}
    for r, k_new, k_old in [(4, 4, 5), (8, 6, 8), (16, 8, 10)]:
        # 2-adic factor: sum_{e>=0} w_pm(comb(e+r-2,r-2) - comb(e+r-2,r-1)) * 2^{-(e+1)}
        # Note |comb(e+r-2, r-2) - comb(e+r-2, r-1)| <= comb(e+r-1, r-1) <= (e+1)^{r-1},
        # and even simpler w_pm(m) <= log_2(m+1) <= (r-1)*(e+1) for all e >= 0!
        # Let's check exact bound w_pm(c2(e)) <= r * (e + 1) (since |c2(e)| <= (e+r)^r => bitlen <= r*log2(e+r) <= r*(e+1) for e >= r)!
        E2_r = 40
        l2_lo = Fraction(0)
        for e in range(E2_r + 1):
            c2 = comb(e + r - 2, r - 2) - (comb(e + r - 2, r - 1) if e >= 1 else 0)
            l2_lo += Fraction(wpm(c2), 1 << (e + 1))
        # Tail e > E2_r: for e >= 41 and r <= 16, |c2(e)| <= comb(e+r-1, r-1) <= 2^{e+r-1}, so w_pm(|c2(e)|) <= e + r!
        # Verify comb(e+r-1, r-1) <= 2^{e+r-1}: trivially true since comb(N, k) <= 2^N for ALL N, k!
        # So w_pm(|c2(e)|) <= s_2(|c2(e)|) <= e + r - 1 + 1 = e + r FOR ALL e >= 0!!
        # Tail sum_{e >= E2_r + 1} (e + r) 2^{-(e+1)} = (E2_r + r + 2) * 2^{-(E2_r + 1)}!
        l2_hi = l2_lo + Fraction(E2_r + r + 2, 1 << (E2_r + 1))
        # Odd primes: g(e) = w_pm(comb(e+r-1, r-1)) <= e + r <= r * (e + 1) (using comb(e+r-1, r-1) <= 2^{e+r-1} => s_2 <= e + r)!
        # Check g(0) = w_pm(1) = 1, g(1) = w_pm(r) = w_pm(2^m) = 1!
        g_r = lambda e, rr=r: wpm(comb(e + rr - 1, rr - 1))
        check(g_r(0) == 1 and g_r(1) == 1, f"g_{r}(0)=g_{r}(1)=1")
        ep_r = CertifiedEulerProduct(g_r, ps_TR, Y_TR, (r, 1), odd_p, keep=0)
        W_lo = l2_lo * ep_r.bounds()[0]
        W_hi = l2_hi * ep_r.bounds()[1]
        check(W_hi / k_new < Fraction(1, 3), f"F_{{2^k,+}}(tau_{r}) newly passes at k={k_new}", "encl")
        check(W_lo / (k_old - 1) > Fraction(1, 4), f"F_{{2^k,+}}(tau_{r}) misses GF-36 Thm 7.1 threshold 1/4 at k={k_old - 1}", "encl")
        d2_r, _ = best_naf_discrepancy(W_hi / k_new, s=1)
        ord_r = lowest_excluded_order(W_hi / k_new, s=1)
        tr_results[r] = (W_lo, W_hi, k_new, k_old, d2_r, ord_r[0])

    # 5d. Confirm boundary constants E_+(4), E^*_+(4) stay strictly > 1/3 (honestly Open)
    check(WA_iv[0] / 2 > Fraction(1, 3), "E_+(4) stays > 1/3 (Open)", "encl")
    check(Fraction(3, 8) > Fraction(1, 3), "E^*_+(4) stays 3/8 > 1/3 (Open)", "encl")

    print("[exact] E^*_+(2^k) and E^*_{alt,+}(2^k): exact coefficient formulas & w_pm mean = 3/4 verified (n <= 4096).")
    print("        -> NEW k=3 (E^*_+(8), E^*_{alt,+}(8)): D-(.;2)=D-(.;4) >= 1/6, D-(.;8) >= 1/12, NOT 4-normal (b=2), NOT 2-normal (b=4).")
    print(f"[encl]  E_{{+,odd}}(2^k): W_odd^maj in {fmt_iv(Wodd_maj)}, mu_NAF(tau_odd) in {fmt_iv(Wodd_true)}")
    print(f"        -> NEW k=4 (E_{{+,odd}}(16)): D-(.;2), D-(.;4) >= {fmt_dn(d2_oddp16_maj, 6)} [maj] / {fmt_dn(d2_oddp16_true, 6)} [true], NOT 4-normal (b=2)!")
    for r, (W_lo, W_hi, k_new, k_old, d2_r, o_r) in tr_results.items():
        print(f"[encl]  F_{{2^k,+}}(tau_{r:2d}): W^maj in {fmt_iv((W_lo, W_hi))} -> threshold k >= {k_new} vs GF-36 Thm 7.1 criterion k >= {k_old} (at k={k_new}: D-(.;2) >= {fmt_dn(d2_r, 6)}, NOT {o_r}-normal)")

    return a_star_p, a_odd_p


# ===========================================================================
# Section 6: Exact Prefix Shadowing Checks [exact] & Isolated Finite Measurements [finite]
# ===========================================================================

def certified_prefix_int(coeffs, k, N, guard=64):
    """Exact floor(2^N x) for signed x = sum_{n>=1} coeffs[n] 2^{-kn} with |coeffs[n]| <= 2*n.

    Certified by exact guard-bit interval containment (ZERO floats).
    """
    Mp = (N + guard) // k
    assert len(coeffs) > Mp + 1
    B = 1 << k
    S = 0
    for n in range(1, Mp + 1):
        S = S * B + coeffs[n]
    S <<= (N + guard - k * Mp)
    # Rigorous tail bound in units of 2^{-(N+guard)}: sum_{j>=1} 2*(Mp+j) 2^{-kj} <= 2*(Mp+2)
    tb = 2 * (Mp + 2) + 1
    lo = (S - tb) >> guard
    hi = (S + tb) >> guard
    check(lo == hi, f"Certified exact prefix floor(2^{N} x) via {guard} guard bits")
    return lo


def section6_prefix_checks_and_finite_measurements(cubic_seqs, a_star_p, a_odd_p):
    head("Section 6 [exact + finite]: Certified Prefix Shadowing & Isolated Finite Measurements")

    # Build a_+(n) up to 4096
    N_COEFF = 4096
    tau = [0] * (N_COEFF + 1)
    for d in range(1, N_COEFF + 1):
        for m in range(d, N_COEFF + 1, d):
            tau[m] += 1
    a_plus = [0] + [(1 - v2(n)) * (tau[n] // (v2(n) + 1)) for n in range(1, N_COEFF + 1)]
    neg_a_plus = [-v for v in a_plus]

    # 6a. [exact] Direct finite-N shadowing check of Theorem A (including negative x = -E_+(8)!)
    #     On N = 1200, R = 10, M = 1210, check exact integer count in [3/16, 13/16) <= 2 * w_pm(floor(2^M x))
    #     and <= 2 * (sum_{n<=M/k} w_pm(a(n)) + w_pm(floor(tau_M)))!
    N_SHAD = 1200
    R_SHAD = 10
    M_SHAD = N_SHAD + R_SHAD
    cases = [
        ("E_+(8)", a_plus, 3),
        ("-E_+(8) [neg]", neg_a_plus, 3),
        ("E_+(16)", a_plus, 4),
        ("E^*_+(8)", a_star_p, 3),
        ("E_{+,odd}(16)", a_odd_p, 4),
        ("L_+(8) mod 7", cubic_seqs[7][0], 3),
        ("L_-(8) mod 7", cubic_seqs[7][1], 3),
        ("L_-(4) mod 7", cubic_seqs[7][1], 2),
        ("L_-(4) mod 9", cubic_seqs[9][1], 2),
        ("L_-(4) mod 13", cubic_seqs[13][1], 2),
    ]
    for name, seq, k in cases:
        # Certify exact floor(2^{M_SHAD} x) and exact floor(2^{N_SHAD + 8} x)
        P_M = certified_prefix_int(seq, k, M_SHAD, guard=64)
        # Since M_SHAD = N_SHAD + 10, the top 4 fractional bits of {2^j x} for 0 <= j < N_SHAD
        # are determined identically by bits (M_SHAD - j - 1 .. M_SHAD - j - 4) of P_M!
        # Wait: because floor(2^{M_SHAD} x) = 2^{M_SHAD} x - {2^{M_SHAD} x}, bits down to N_SHAD + 4
        # match the canonical binary expansion of {x} exactly!
        frac_bits = P_M & ((1 << M_SHAD) - 1)
        # Count j < N_SHAD with {2^j x} in [3/16, 13/16) (top 4 bits in 3..12)
        hits_ord4 = 0
        hits_b4_ord2 = 0
        for j in range(N_SHAD):
            w4 = (frac_bits >> (M_SHAD - j - 4)) & 15
            if 3 <= w4 <= 12:
                hits_ord4 += 1
                if j % 2 == 0:
                    hits_b4_ord2 += 1
        w_PM = wpm(P_M)
        Q = M_SHAD // k
        A_M = 0
        mass = 0
        for n in range(1, Q + 1):
            A_M = (A_M << k) + seq[n]
            mass += wpm(seq[n])
        A_M <<= (M_SHAD - k * Q)
        t_M = P_M - A_M
        check(hits_ord4 <= 2 * w_PM, f"Theorem A exact finite-N check on {name}")
        check(hits_b4_ord2 <= w_PM, f"Multi-radix base-4 exact finite-N check on {name}")
        check(w_PM <= mass + wpm(t_M), f"Prefix signed-weight decomposition on {name}")

    print(f"[exact] Direct finite-N shadowing & prefix decomposition verified on all {len(cases)} series (N={N_SHAD}, R={R_SHAD}, incl. negative -E_+(8)).")

    # 6b. [finite] ISOLATED FINITE MEASUREMENTS ONLY (N = 4000 bits; NEVER asymptotic evidence!)
    N_FIN = 4000
    print(f"\n[finite] ISOLATED FINITE MEASUREMENTS ONLY (N = {N_FIN} certified bits; bears on NO limit):")
    print("         Series             k    f_1      F([1/4,3/4))  F([3/16,13/16))  F_4([3/16,13/16))  w_pm/N")
    for name, seq, k in cases:
        if name.startswith("-"):
            continue
        P = certified_prefix_int(seq, k, N_FIN + 16, guard=64)
        fb = P & ((1 << (N_FIN + 16)) - 1)
        top_N = fb >> 16
        ones = top_N.bit_count()
        c_mid2 = 0
        c_ord4 = 0
        c_b4_ord2 = 0
        for j in range(N_FIN):
            w4 = (fb >> (N_FIN + 16 - j - 4)) & 15
            if 4 <= w4 <= 11:
                c_mid2 += 1
            if 3 <= w4 <= 12:
                c_ord4 += 1
                if j % 2 == 0:
                    c_b4_ord2 += 1
        wN = wpm(top_N)
        check(0 <= ones <= N_FIN and 0 <= c_ord4 <= N_FIN, f"Sanity check finite stats {name}", "finite")
        print(f"         {name:16s}  {k:2d}  {ones/N_FIN:.5f}     {c_mid2/N_FIN:.5f}         "
              f"{c_ord4/N_FIN:.5f}            {c_b4_ord2/(N_FIN//2):.5f}          {wN/N_FIN:.5f}")


def main():
    section1_naf_geometric_transfer()
    _, WA_iv = section2_eplus_certificates()
    section3_order3_barrier()
    cubic_seqs, _ = section4_cubic_characters()
    a_star_p, a_odd_p = section5_other_dense_families(WA_iv)
    section6_prefix_checks_and_finite_measurements(cubic_seqs, a_star_p, a_odd_p)
    tot = sum(COUNTS.values())
    print(f"\nALL CHECKS PASSED ({tot} assertions: {COUNTS['exact']} [exact], {COUNTS['encl']} [encl], "
          f"{COUNTS['finite']} [finite]) in {time.time() - T0:.2f} s")


if __name__ == "__main__":
    main()
