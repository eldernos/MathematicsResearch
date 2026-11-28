#!/usr/bin/env python3
"""
Phase 24 Track C — Exact Verification Suite and Separate Finite Measurements.

Covers all four sub-tracks of notes/phase24/partitions-and-reciprocal-spectra.md:
  C1. Convergent reciprocal discrepancy spectrum A_conv(b):
      - All-dyadic-power (b = 2^e) dense spectrum and odd-e dense L-normal spectrum
      - Exact triangular multiplicity law N_k(v) for P_k(q) and conditional mod-p bound >= 1/(4p)
      - Prime-simplex exact discrepancy, Lucas mod-p lower bound, and exhaustive L <= 60
        zero-band density search for S_i in {0, +-2^a} (including L = 60 witness Phi_3 Phi_4 Phi_10)
      - Exact non-dyadic +1-inversion divisibility D | gcd(b^P - 1, 2^P - 1)
  C2. Slower reciprocal schedules & universal doubly-exponential period-growth barrier:
      - Exact Shared-Divisor Order Absorption Lemma: G_{k+1} = gcd(D_k, b^{m_{k+1}} - 1) | T_{k+1}
      - Elementary primitive-part bound Pi_b(p^r) > b^{p^r / 2} / p^r (zero external inputs)
      - Single-step LTE-order recycling vs. universal Lyapunov bound
  C3. Mahler partition constants X_2 and X_{b, m}:
      - Full m-ary Cartier identities and exact leading coefficient u_{s, r, 0} = m^{s - 1}
      - Exact elementary CRA-type divisibility identity b_m(m^2 n + m^2 - m) = m * sum_{j<=n} b_m(m j)
      - Canonical carry floor identity, L-digit master congruence, carry-increment functional
        equations, and exact binary carry-parity law d_k(X_2) = delta_{k+1} mod 2 (k >= 2)
      - Carry-Valuation Barrier finite-prefix identity for 120-bit truncated target differences
        (1/3, Champernowne C_2, Lambda_2)
  C4. Short-orbit bridge for P_b = 1/E_b:
      - Exact partition-difference identity and two-sided shadowing bounds for P_b - R_k^(E)
      - Exact p-adic valuations v_p(D_k^(E)), v_p(T_k^(E)), and primitive-order factorization R(d)
      - Exact pentagonal orbit coupling inequality on certified digits of P_b
      - Exact base-3 counterexamples for single-harmonic Weyl criteria

Strict separation of evidence:
  - Part I performs ONLY exact integer (`int`) and exact rational (`Fraction`) checks
    (Finite certificates of the stated finite instances).
  - Part II performs floating-point finite measurements (explicitly NOT asymptotic evidence).
"""

import cmath
import math
import time
from collections import Counter
from fractions import Fraction


class CertCounter:
    def __init__(self):
        self.exact = 0
        self.float_meas = 0
        self.by_section = {}

    def check_exact(self, section, cond, msg=""):
        if not cond:
            raise AssertionError(f"[EXACT FAIL in {section}] {msg}")
        self.exact += 1
        s = self.by_section.setdefault(section, [0, 0])
        s[0] += 1

    def check_float(self, section, cond, msg=""):
        if not cond:
            raise AssertionError(f"[FLOAT FAIL in {section}] {msg}")
        self.float_meas += 1
        s = self.by_section.setdefault(section, [0, 0])
        s[1] += 1


C = CertCounter()


# ---------------------------------------------------------------------------
# Pure exact integer/polynomial/number-theory helpers (internal assertions only)
# ---------------------------------------------------------------------------

def factor_int(n):
    assert n >= 1
    pf = {}
    d = 2
    t = n
    while d * d <= t:
        while t % d == 0:
            pf[d] = pf.get(d, 0) + 1
            t //= d
        d += 1
    if t > 1:
        pf[t] = pf.get(t, 0) + 1
    return pf


def ord_mod(b, n):
    """Exact multiplicative order of b mod n (gcd(b, n) = 1)."""
    if n == 1:
        return 1
    assert math.gcd(b, n) == 1
    pf = factor_int(n)
    ans = 1
    for p, e in pf.items():
        phi = p - 1
        op = phi
        for q in factor_int(phi):
            while op % q == 0 and pow(b, op // q, p) == 1:
                op //= q
        pe = p ** e
        o = op
        while pow(b, o, pe) != 1:
            o *= p
        ans = math.lcm(ans, o)
    assert pow(b, ans, n) == 1
    return ans


def ord_mod_dividing(b, n, mult):
    """Exact multiplicative order of b mod n given a known multiple mult with b^mult = 1 (mod n)."""
    if n == 1:
        return 1
    assert math.gcd(b, n) == 1 and pow(b, mult, n) == 1
    o = mult
    for q in factor_int(mult):
        while o % q == 0 and pow(b, o // q, n) == 1:
            o //= q
    assert pow(b, o, n) == 1
    return o


def v_p(n, p):
    assert n != 0 and p >= 2
    n = abs(n)
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def v_p_fact(n, p):
    s = 0
    while n > 0:
        n //= p
        s += n
    return s


def exact_orbit_disc(b, A, D):
    """Exact Fraction extreme interval discrepancy D(mu(A/D; b)) for gcd(b, D) = 1."""
    assert math.gcd(b, D) == 1
    cur = A % D
    seen = set()
    pts = []
    while cur not in seen:
        seen.add(cur)
        pts.append(Fraction(cur, D))
        cur = (cur * b) % D
    pts.sort()
    n = len(pts)
    mx = max(Fraction(i + 1, n) - pts[i] for i in range(n))
    mn = min(Fraction(i, n) - pts[i] for i in range(n))
    return mx - mn, n


def poly_mul(a, b):
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                res[i + j] += x * y
    return res


def poly_div_exact(a, b):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    assert len(a) >= len(b) and b[-1] != 0
    q = [0] * (len(a) - len(b) + 1)
    for i in range(len(a) - len(b), -1, -1):
        assert a[i + len(b) - 1] % b[-1] == 0
        c = a[i + len(b) - 1] // b[-1]
        q[i] = c
        if c:
            for j, y in enumerate(b):
                a[i + j] -= c * y
    assert all(x == 0 for x in a)
    return q


def poly_eval(p, x):
    acc = 0
    for c in reversed(p):
        acc = acc * x + c
    return acc


def cyclotomic_table(n_max):
    phi = {1: [-1, 1]}
    for n in range(2, n_max + 1):
        p = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0:
                p = poly_div_exact(p, phi[d])
        phi[n] = p
    return phi


def de_bruijn_binary(m):
    """Exact cyclic binary de Bruijn word of order m (length 2^m), rotated to end in 1."""
    a = [0] * (2 * m)
    seq = []

    def db(t, p):
        if t > m:
            if m % p == 0:
                seq.extend(a[1:p + 1])
        else:
            a[t] = a[t - p]
            db(t + 1, p)
            for j in range(a[t - p] + 1, 2):
                a[t] = j
                db(t + 1, t)

    db(1, 1)
    assert len(seq) == (1 << m)
    # Rotate so last bit is 1
    idx = len(seq) - 1 - seq[::-1].index(1)
    rot = seq[idx + 1:] + seq[:idx + 1]
    assert rot[-1] == 1
    return rot


def bits_to_int(bits):
    v = 0
    for bit in bits:
        v = (v << 1) | bit
    return v


def mary_partitions(m, n_max):
    """Exact table of m-ary partition numbers b_m(0..n_max)."""
    b = [0] * (n_max + 1)
    b[0] = 1
    for n in range(1, n_max + 1):
        b[n] = b[n - 1] + (b[n // m] if n % m == 0 else 0)
    return b


def ordinary_partitions(n_max):
    """Exact table of ordinary partition numbers p(0..n_max) via pentagonal recursion."""
    p = [0] * (n_max + 1)
    p[0] = 1
    for n in range(1, n_max + 1):
        s = 0
        k = 1
        while True:
            g1 = k * (3 * k - 1) // 2
            if g1 > n:
                break
            sign = 1 if (k % 2 == 1) else -1
            s += sign * p[n - g1]
            g2 = k * (3 * k + 1) // 2
            if g2 <= n:
                s += sign * p[n - g2]
            k += 1
        p[n] = s
    return p


def restricted_partitions(k, n_max):
    """Exact table of partitions p_{<=k}(0..n_max) into parts at most k."""
    dp = [0] * (n_max + 1)
    dp[0] = 1
    for part in range(1, k + 1):
        for n in range(part, n_max + 1):
            dp[n] += dp[n - part]
    return dp


def certified_digits_from_series(coeffs, b, N_digits, tail_majorant_fn):
    """
    Certify floor(x) and the first N_digits base-b digits d_1..d_{N_digits}
    of x = sum_{n>=0} coeffs[n] * b^{-n}, using exact integer interval arithmetic.
    Requires len(coeffs) > M where tail_majorant_fn(M) < 1 / b^{guard}.
    Returns (int_part, digits[1..N_digits], M_used).
    """
    # Choose guard so partial sum b^N * S_M is not within tail bound of an integer
    M = len(coeffs) - 1
    assert M > N_digits + 10
    # Compute S_M = num / b^M exactly
    num = 0
    for c in coeffs[:M + 1]:
        num = num * b + c
    # Tail bound: 0 <= x - S_M <= T_num / T_den (or symmetric |x - S_M| <= T)
    T = tail_majorant_fn(M)
    assert isinstance(T, Fraction) and T >= 0
    # Lower and upper bounds for b^{N_digits} * x:
    # S_M * b^{N_digits} = num / b^{M - N_digits}
    shift = b ** (M - N_digits)
    low = Fraction(num, shift) - T * (b ** N_digits)
    high = Fraction(num, shift) + T * (b ** N_digits)
    # For nonnegative series we can use low = Fraction(num, shift)
    lo_fl = math.floor(low)
    hi_fl = math.floor(high)
    assert lo_fl == hi_fl, f"Interval straddles integer: {float(low)} .. {float(high)}"
    int_part, frac_int = divmod(lo_fl, b ** N_digits)
    digits = []
    tmp = frac_int
    for _ in range(N_digits):
        tmp, d = divmod(tmp, b)
        digits.append(d)
    digits.reverse()
    return int_part, digits, M


# ===========================================================================
# PART I: EXACT FINITE CERTIFICATES (int / Fraction ONLY)
# ===========================================================================

def verify_C1():
    sec = "C1. Convergent reciprocal spectrum & obstructions"
    print(f"Running {sec}...")

    # 1a. Exact criterion: for b = 2^e and odd D >= 1,
    #     2 in <2^e> (mod D) <=> gcd(e, ord_D(2)) = 1, and then mu(r; 2^e) = mu(r; 2).
    for e in range(1, 7):
        b = 1 << e
        for D in range(3, 150, 2):
            o2 = ord_mod(2, D)
            # Check membership of 2 in <b> mod D directly
            cur = 1 % D
            seen = set()
            in_gen = False
            while cur not in seen:
                if cur == 2 % D:
                    in_gen = True
                seen.add(cur)
                cur = (cur * b) % D
            C.check_exact(sec, in_gen == (math.gcd(e, o2) == 1),
                          f"e={e}, D={D}: in_gen={in_gen}, gcd={math.gcd(e, o2)}")
            if in_gen:
                ob = ord_mod(b, D)
                C.check_exact(sec, ob == o2, f"e={e}, D={D}: ob={ob} != o2={o2}")
                # Check exact orbit equality for A = 1
                d2, n2 = exact_orbit_disc(2, 1, D)
                db, nb = exact_orbit_disc(b, 1, D)
                C.check_exact(sec, d2 == db and n2 == nb,
                              f"Orbit mismatch e={e}, D={D}")

    # 1b. Dense dyadic spectrum in bases b = 4, 8, 16 via w = 0^z w_{dB, m} with gcd(e, z + 2^m) = 1
    w_db4 = de_bruijn_binary(4)  # length 16, ends in 1
    dyadic_examples = {}
    for e in [2, 3, 4]:
        b = 1 << e
        vals = []
        for z_base in [0, 4, 8, 16, 32, 64, 96]:
            # Adjust z by at most e-1 so gcd(e, z + 16) = 1
            z = z_base
            while math.gcd(e, z + 16) != 1:
                z += 1
            P = z + 16
            bits = [0] * z + w_db4
            A = bits_to_int(bits)
            D_full = (1 << P) - 1
            g = math.gcd(A, D_full)
            Ar, Dr = A // g, D_full // g
            C.check_exact(sec, Ar % 2 == 1 and Dr % 2 == 1, f"Parity fail b={b}, P={P}")
            C.check_exact(sec, math.gcd(e, ord_mod_dividing(2, Dr, P)) == 1, f"gcd fail b={b}, Dr={Dr}")
            d_b, n_b = exact_orbit_disc(b, Ar, Dr)
            d_2, n_2 = exact_orbit_disc(2, Ar, Dr)
            C.check_exact(sec, d_b == d_2 and n_b == n_2, f"Disc mismatch b={b}, P={P}")
            vals.append((P, d_b))
        dyadic_examples[b] = vals
        # Check range spans well across (0.1, 0.85)
        C.check_exact(sec, vals[0][1] < Fraction(1, 5) and vals[-1][1] > Fraction(4, 5),
                      f"Range too narrow for b={b}")

    # 1c. Exact 1-normal convergent reciprocals in base 8 (e = 3, odd) via exact 3-normal binary words
    #     with gcd(3, P) = 1. Take R copies of W_1 (length 8) where 3 nmid R (e.g. R = 1, 2, 4, 5, 7, 8).
    #     Use loop-deleted binary de Bruijn graph G_{2, 3}^* (6 edges) + R loops at 00 and 11.
    #     G_{2,3}^* Eulerian circuit of length 6: 00->01->10->01? Let's construct explicitly:
    #     Edges of G_{2,3}^*: 001, 010, 011, 100, 101, 110 (all 6 non-constant 3-bit words).
    #     Circuit starting at 00: 00 ->1 01 ->0 10 ->1 01 ->1 11 ->0 10 ->0 00.
    #     Bit string (6 bits): 1, 0, 1, 1, 0, 0 -> cyclic 3-words: 101, 011, 110, 100, 001, 010!
    c_star = [1, 0, 1, 1, 0, 0]
    # Insert R copies of 0 after the final 00 (end of c_star) and R copies of 1 at 11 (after index 3)
    base8_1norm = []
    for R in [1, 2, 4, 5, 7, 8]:
        # Build word: prefix [1, 0, 1, 1] + [1]*R + [0, 0] + (R-1 copies of c_star) + [0]*R
        word = [1, 0, 1, 1] + [1] * R + [0, 0] + c_star * (R - 1) + [0] * R
        P = len(word)
        C.check_exact(sec, P == 8 * R and math.gcd(3, P) == 1, f"P={P} for R={R}")
        # Rotate so last bit is 1
        idx = len(word) - 1 - word[::-1].index(1)
        word = word[idx + 1:] + word[:idx + 1]
        # Verify exact 3-normality in base 2 (every 3-bit word occurs exactly R times cyclically)
        cnt3 = Counter(tuple(word[(i + j) % P] for j in range(3)) for i in range(P))
        C.check_exact(sec, len(cnt3) == 8 and all(v == R for v in cnt3.values()),
                      f"Not exact 3-normal for R={R}: {cnt3}")
        # Verify exact 1-normality in base 8 along step-3 shifts (0, 3, 6, ... mod P)
        # Since gcd(3, P) = 1, the base-8 digits at positions 0..P-1 are the 3-bit blocks at (3*t) mod P
        cnt8 = Counter(
            (word[(3 * t) % P] * 4 + word[(3 * t + 1) % P] * 2 + word[(3 * t + 2) % P])
            for t in range(P)
        )
        C.check_exact(sec, len(cnt8) == 8 and all(v == R for v in cnt8.values()),
                      f"Not exact base-8 1-normal for R={R}")
        A = bits_to_int(word)
        D_full = (1 << P) - 1
        g = math.gcd(A, D_full)
        Ar, Dr = A // g, D_full // g
        C.check_exact(sec, math.gcd(3, ord_mod_dividing(2, Dr, P)) == 1, f"2 not in <8> mod {Dr}")
        d8, n8 = exact_orbit_disc(8, Ar, Dr)
        C.check_exact(sec, Fraction(0) < d8 <= Fraction(1, 4), f"d8={d8} out of (0, 1/4]")
        base8_1norm.append((R, P, d8))

    # 1d. Exact triangular multiplicity law N_k(v) for P_k(q) (k = 1..20)
    #     and exact rational lower bound P(p | S_i^(k) | S_i^(k) != 0) >= 1/(4p) for all primes p <= k.
    def alt_poly(m):
        return [1 if i % 2 == 0 else -1 for i in range(m)]

    primes_20 = [2, 3, 5, 7, 11, 13, 17, 19]
    for k in range(1, 21):
        p1, p2 = 2 * k + 1, 2 * k + 3
        L = 2 * p1 * p2
        P_k = poly_mul(alt_poly(p1), alt_poly(p2))
        A_k = poly_div_exact([1] * L, P_k)
        A_k = A_k + [0] * (L - len(A_k))
        cnt = Counter(A_k)
        # Check exact multiplicity formula for every v in [-2k, 2k+2]
        expected_vals = set(range(-2 * k, 2 * k + 3))
        C.check_exact(sec, set(cnt.keys()) == expected_vals, f"Value set mismatch at k={k}")
        for v in range(-2 * k, 2 * k + 3):
            if v <= 0:
                exp_mult = 2 * (2 * k + 1 + v)
            elif v == 1:
                exp_mult = 4 * k + 2
            else:
                exp_mult = 2 * (2 * k + 3 - v)
            C.check_exact(sec, cnt[v] == exp_mult, f"N_{k}({v})={cnt[v]} != {exp_mult}")
        # Check exact rational lower bound >= 1/(4p) for every prime p <= k
        nz = L - (4 * k + 2)
        C.check_exact(sec, nz == 4 * (2 * k + 1) * (k + 1), f"nz formula at k={k}")
        for p in primes_20:
            if p <= k:
                div_nz = sum(m_cnt for val, m_cnt in cnt.items() if val != 0 and val % p == 0)
                C.check_exact(sec, Fraction(div_nz, nz) >= Fraction(1, 4 * p),
                              f"Lower bound fail at k={k}, p={p}: {div_nz}/{nz}")

    # 1e. Exact prime-simplex discrepancy identity D((1 - gamma) U_p(0) + gamma delta_0)
    #     = 1/p + gamma * (1 - 1/p), verified directly from step-function sup - inf!
    for p in [3, 5, 7, 11]:
        for num in [0, 1, 2, 3, 5, 7]:
            gamma = Fraction(num, 8)
            # Measure weights at j/p (0 <= j < p): w_0 = gamma + (1-gamma)/p, w_j = (1-gamma)/p
            w0 = gamma + (1 - gamma) * Fraction(1, p)
            wj = (1 - gamma) * Fraction(1, p)
            # Evaluate F(t) - t at left and right limits of every atom j/p (and at 0, 1)
            g_vals = [Fraction(0)]  # at t = 0
            cum = Fraction(0)
            for j in range(p):
                t = Fraction(j, p)
                g_vals.append(cum - t)       # left limit at j/p
                cum += (w0 if j == 0 else wj)
                g_vals.append(cum - t)       # right limit at j/p
            g_vals.append(cum - Fraction(1))  # left limit at 1
            D_exact = max(g_vals) - min(g_vals)
            D_formula = Fraction(1, p) + gamma * (1 - Fraction(1, p))
            C.check_exact(sec, D_exact == D_formula,
                          f"Prime simplex fail p={p}, gamma={gamma}: {D_exact} != {D_formula}")

    # 1f. Lucas mod-p zero-density lower bound rho^(p)(Q) >= 1/p for L = p^r (all nontrivial Q | (1-q^L)/(1-q))
    for p, r in [(3, 1), (3, 2), (5, 1), (5, 2)]:
        L = p ** r
        # Any divisor Q of (1-q^L)/(1-q) mod p is (1-q)^d mod p (1 <= d <= L-1),
        # so A(q) = (1-q)^{L-1-d} mod p; coeff of q^i is (-1)^i * binom(L-1-d, i) mod p.
        for d in range(1, L):
            N = L - 1 - d
            zeros_mod_p = sum(1 for i in range(L) if math.comb(N, i) % p == 0)
            C.check_exact(sec, Fraction(zeros_mod_p, L) >= Fraction(1, p),
                          f"Lucas fail p={p}, r={r}, d={d}: {zeros_mod_p}/{L}")

    # 1g. Exhaustive exact certificate over ALL 2 <= L <= 60 (no divisor-count exclusions)
    #     for nontrivial cyclotomic divisors Q | (1-q^L)/(1-q) with deg(Q) < L/3 and S_i in {0, +-2^a}:
    #     - For 2 <= L <= 59, every such divisor satisfies zero-band density rho_0(Q) >= 1/3
    #       (attained at L = 6 by Phi_6(q) = 1 - q + q^2 with S = (1, 2, 2, 1, 0, 0), rho_0 = 1/3, rho^(2) = 2/3).
    #     - At L = 60, there is a unique witness with rho_0(Q) < 1/3: Q = Phi_3 * Phi_4 * Phi_10
    #       (deg 8, S_i in {-2, -1, 0, 1, 2}, 18 zero bands, rho_0 = 18/60 = 3/10 < 1/3).
    phi_tab = cyclotomic_table(60)

    def is_pow2_or_zero(x):
        if x == 0:
            return True
        x = abs(x)
        return (x & (x - 1)) == 0

    # Explicit Phi_6 check at L = 6
    A_phi6 = poly_div_exact([1] * 6, phi_tab[6])
    A_phi6_pad = A_phi6 + [0] * (6 - len(A_phi6))
    C.check_exact(sec, A_phi6_pad == [1, 2, 2, 1, 0, 0], f"Phi_6 bands mismatch: {A_phi6_pad}")
    C.check_exact(sec, Fraction(sum(1 for c in A_phi6_pad if c == 0), 6) == Fraction(1, 3)
                  and Fraction(sum(1 for c in A_phi6_pad if c % 2 == 0), 6) == Fraction(2, 3),
                  "Phi_6 density mismatch")

    checked_cyc_59 = 0
    checked_cyc_60 = 0
    pow2_59 = 0
    pow2_60 = 0
    witnesses_60 = []
    for L in range(2, 61):
        divs = [d for d in range(2, L + 1) if L % d == 0]
        num = [1] * L
        for mask in range(1, 1 << len(divs)):
            deg = sum(len(phi_tab[divs[i]]) - 1 for i in range(len(divs)) if (mask >> i) & 1)
            if deg * 3 >= L:
                continue  # already >= deg trailing zeros, so rho_0 >= deg/L >= 1/3
            Q = [1]
            chosen = []
            for i, d in enumerate(divs):
                if (mask >> i) & 1:
                    Q = poly_mul(Q, phi_tab[d])
                    chosen.append(d)
            if Q[0] == -1:
                Q = [-c for c in Q]
            A = poly_div_exact(num, Q)
            if L <= 59:
                checked_cyc_59 += 1
            else:
                checked_cyc_60 += 1
            if all(is_pow2_or_zero(c) for c in A):
                nz = sum(1 for c in A if c != 0)
                zeros = L - nz
                if L <= 59:
                    pow2_59 += 1
                    C.check_exact(sec, 3 * zeros >= L, f"Found rho_0 < 1/3 at L={L}, chosen={chosen}")
                else:
                    pow2_60 += 1
                    if 3 * zeros < L:
                        witnesses_60.append((chosen, deg, zeros, sorted(set(A))))
    C.check_exact(sec, checked_cyc_59 == 514 and checked_cyc_60 == 423,
                  f"Unexpected divisor counts: L<=59={checked_cyc_59}, L=60={checked_cyc_60}")
    C.check_exact(sec, pow2_59 == 487 and pow2_60 == 297,
                  f"Unexpected pow2 counts: L<=59={pow2_59}, L=60={pow2_60}")
    C.check_exact(sec, witnesses_60 == [([3, 4, 10], 8, 18, [-2, -1, 0, 1, 2])],
                  f"Unexpected L=60 witnesses: {witnesses_60}")
    # Also certify exact zero-band density 18/60 = 3/10 < 1/3 for Q = Phi_3 * Phi_4 * Phi_10
    C.check_exact(sec, Fraction(18, 60) == Fraction(3, 10) and Fraction(3, 10) < Fraction(1, 3),
                  "L=60 density check")

    # 1h. Exact non-dyadic +1-inversion divisibility: 2 in <b> (mod D) => D | gcd(b^P - 1, 2^P - 1)
    for b in [3, 5, 6, 7, 10]:
        for D in range(3, 300, 2):
            if math.gcd(b, D) != 1:
                continue
            cur = 1 % D
            seen = set()
            in_gen = False
            while cur not in seen:
                if cur == 2 % D:
                    in_gen = True
                seen.add(cur)
                cur = (cur * b) % D
            if in_gen:
                P = ord_mod(b, D)
                g_bd = math.gcd(b ** P - 1, (1 << P) - 1)
                C.check_exact(sec, g_bd % D == 0, f"Divisibility fail b={b}, D={D}, P={P}")

    cyc_summary = (checked_cyc_59, checked_cyc_60, pow2_59, pow2_60, witnesses_60[0])
    return dyadic_examples, base8_1norm, cyc_summary


def verify_C2():
    sec = "C2. Universal doubly-exponential period-growth barrier"
    print(f"Running {sec}...")

    # 2a. Exact Shared-Divisor Order Absorption Lemma: G_{k+1} = gcd(D_k, b^{m_{k+1}} - 1) | T_{k+1}
    #     with ZERO constant loss across all bases b in {2, 3, 4, 5, 7, 10} and 2-/3-step schedules.
    for b in [2, 3, 4, 5, 7, 10]:
        for m1 in range(1, 8):
            D1 = b ** m1 - 1
            for m2 in range(1, 8):
                D2 = D1 * (b ** m2 - 1)
                G2 = math.gcd(D1, b ** m2 - 1)
                T2 = ord_mod(b, D2)
                C.check_exact(sec, T2 % G2 == 0, f"2-step fail b={b}, m=({m1},{m2})")
                # Also verify h_1 = gcd(m1, m2) => (b^{h_1} - 1) | G2 | T2 and lcm(m1, m2) | T2
                h1 = math.gcd(m1, m2)
                C.check_exact(sec, G2 % (b ** h1 - 1) == 0 and T2 % math.lcm(m1, m2) == 0,
                              f"h1/lcm fail b={b}, m=({m1},{m2})")
                for m3 in range(1, 7):
                    if b ** m3 > 10 ** 6:
                        continue
                    D3 = D2 * (b ** m3 - 1)
                    if D3 > 10 ** 11:
                        continue
                    G3 = math.gcd(D2, b ** m3 - 1)
                    T3 = ord_mod(b, D3)
                    C.check_exact(sec, T3 % G3 == 0, f"3-step fail b={b}, m=({m1},{m2},{m3})")
                    L3 = math.lcm(m1, m2, m3)
                    C.check_exact(sec, T3 % L3 == 0, f"L3 fail b={b}, m=({m1},{m2},{m3})")

    # 2b. Elementary primitive-part bound (zero external inputs):
    #     For every prime power p^r >= 7 and b >= 2,
    #     Phi_{p^r}(b) > b^{p^r / 2}, v_p(Phi_{p^r}(b)) <= 1, and Pi_b(p^r) >= Phi_{p^r}(b)/p > b^{p^r / 2}/p^r.
    prime_powers = [7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29]
    for b in [2, 3, 4, 5, 10]:
        for pr in prime_powers:
            pf = factor_int(pr)
            assert len(pf) == 1
            p, r = next(iter(pf.items()))
            num = b ** pr - 1
            den = b ** (pr // p) - 1
            assert num % den == 0
            phi_val = num // den
            # Exact check Phi_{p^r}(b)^2 > b^{p^r}
            C.check_exact(sec, phi_val * phi_val > b ** pr,
                          f"Phi bound fail b={b}, p^r={pr}")
            # Exact check v_p(Phi_{p^r}(b)) <= 1
            vp_phi = v_p(phi_val, p)
            C.check_exact(sec, vp_phi <= 1, f"v_p(Phi)={vp_phi} > 1 at b={b}, p^r={pr}")
            # Primitive part Pi_b(p^r) = phi_val / p^{vp_phi} (all other prime divisors have ord = p^r)
            Pi_val = phi_val // (p ** vp_phi)
            C.check_exact(sec, Pi_val * p >= phi_val and (Pi_val * pr) ** 2 > b ** pr,
                          f"Pi_b bound fail b={b}, p^r={pr}")
            # Exact integer check for Pi_val^15 > (272/100)^{pr} > e^{pr}
            C.check_exact(sec, (Pi_val ** 15) * (100 ** pr) > (272 ** pr),
                          f"exp(pr/15) bound fail b={b}, p^r={pr}")

    # 2c. Explicit single-step LTE-order recycling vs. pairwise-coprime growth:
    #     In base 2, m = (2, 4, 15) satisfies m_3 = 15 >= T_2 = 12, gcd(D_2, 2^15 - 1) = 1
    #     (D_2 = 45, 2^15 - 1 = 32767 = 7 * 31 * 151), yet gcd(T_2, m_3) = 3, giving T_3 = 60 = (1/3) T_2 m_3.
    for b, ms, expected_Ts in [(2, [2, 4, 15], [2, 12, 60]), (2, [2, 4, 21], [2, 12, 84]), (5, [1, 2, 12], None)]:
        D = 1
        Ts = []
        for m in ms:
            D *= (b ** m - 1)
            Ts.append(ord_mod(b, D))
        if expected_Ts is not None:
            C.check_exact(sec, Ts == expected_Ts, f"Recycling mismatch b={b}, ms={ms}: {Ts}")
            # Confirm strict single-step beating of T_{k-1} * m_k
            C.check_exact(sec, Ts[2] < Ts[1] * ms[2] and ms[2] >= Ts[1],
                          f"Recycling did not beat T2*m3: b={b}, ms={ms}")
        # Verify Lyapunov identity L_k * g_k = L_{k-1} * m_k and L_k | T_k at every step
        L_prev = 1
        for idx, m in enumerate(ms):
            g_k = math.gcd(L_prev, m)
            L_cur = math.lcm(L_prev, m)
            C.check_exact(sec, L_cur * g_k == L_prev * m and Ts[idx] % L_cur == 0,
                          f"Lyapunov identity fail b={b}, idx={idx}")
            L_prev = L_cur


def verify_C3():
    sec = "C3. Mahler partition constants X_2 and X_{b, m}"
    print(f"Running {sec}...")

    # 3a. Full m-ary Cartier operator identities for m = 2, 3, 4, 5 and k = 0..4 (through z^500)
    #     F_k(z) = (1 - z)^{-k} F(z), Q_m(z)^s = sum_{r=0}^{m-1} z^r U_{s, r}(z^m),
    #     U_{s, r}(1 - w) = sum_j u_{s, r, j} w^j, exact u_{s, r, 0} = m^{s - 1},
    #     and Phi_r F_k = sum_j u_{k+1, r, j} F_{k + 1 - j}.
    N_ser = 500
    for m in [2, 3, 4, 5]:
        bm = mary_partitions(m, m * N_ser + m)
        # Build F_k coefficients up to N_ser (for k = 0..5) via F_k[n] = sum_{j<=n} F_{k-1}[j]
        # Need F_k up to m*N_ser + m for Phi_r F_k, and up to N_ser for RHS
        F_tab = [bm]
        for k in range(1, 6):
            prev = F_tab[-1]
            cur = [0] * len(prev)
            acc = 0
            for i, x in enumerate(prev):
                acc += x
                cur[i] = acc
            F_tab.append(cur)
        Q_m = [1] * m
        Q_pow = [1]  # Q_m^0
        for s in range(1, 6):  # s = k + 1, k = 0..4
            Q_pow = poly_mul(Q_pow, Q_m)
            k = s - 1
            for r in range(m):
                # Extract U_{s, r}(y): coeff of y^t is coeff of z^{m*t + r} in Q_m^s
                U = [Q_pow[i] for i in range(r, len(Q_pow), m)]
                # Exact leading coefficient U(1) = m^{s - 1}
                C.check_exact(sec, sum(U) == m ** (s - 1),
                              f"u_{{s,r,0}} fail m={m}, s={s}, r={r}: {sum(U)} != {m**(s-1)}")
                # Expand U(1 - w) = sum_j u_j w^j via binomial transform:
                # U(1 - w) = sum_t U[t] (1 - w)^t = sum_j w^j * (-1)^j * sum_{t>=j} U[t] * binom(t, j)
                u_coeffs = []
                for j in range(len(U)):
                    val = sum(U[t] * math.comb(t, j) for t in range(j, len(U)))
                    if j % 2 == 1:
                        val = -val
                    u_coeffs.append(val)
                C.check_exact(sec, u_coeffs[0] == m ** (s - 1), f"u_0 mismatch m={m},s={s},r={r}")
                # Check Phi_r F_k [n] == sum_j u_j F_{k + 1 - j}[n] for n = 0..200
                for n in range(201):
                    lhs = F_tab[k][m * n + r]
                    rhs = sum(u_coeffs[j] * F_tab[k + 1 - j][n] for j in range(len(u_coeffs)))
                    C.check_exact(sec, lhs == rhs, f"Cartier fail m={m},k={k},r={r},n={n}")
                # Check exact k = 1 formula Phi_r F_1 = m F_2 - (m - 1 - r) F_1
                if k == 1:
                    C.check_exact(sec, u_coeffs == [m, -(m - 1 - r)] or (r == m - 1 and u_coeffs == [m]),
                                  f"k=1 formula mismatch m={m}, r={r}: {u_coeffs}")

    # 3b. Exact elementary CRA-type divisibility identity:
    #     b_m(m^2 n + m^2 - m) = m * sum_{j=0}^n b_m(m j) for all m = 2..6, n = 0..60.
    for m in [2, 3, 4, 5, 6]:
        bm = mary_partitions(m, m * m * 61 + m * m)
        acc = 0
        for n in range(61):
            acc += bm[m * n]
            val = bm[m * m * n + m * m - m]
            C.check_exact(sec, val == m * acc and val % m == 0,
                          f"CRA fail m={m}, n={n}: {val} != {m * acc}")

    # 3c. Exact canonical carry floor identity, Master Congruence, carry-increment functional
    #     equations, and exact binary carry-parity law d_k(X_2) = delta_{k+1} mod 2 (k >= 2).
    #     Certify digits of X_{b, m} for (b, m) in [(2,2), (3,2), (2,3), (3,3)].
    carry_samples = {}
    for b, m in [(2, 2), (3, 2), (2, 3), (3, 3)]:
        N_dig = 180
        M_trunc = 420
        bm = mary_partitions(m, M_trunc)
        # Elementary upper bound on tail: for n >= M_trunc, b_m(n) <= C_m * m^{(log_m n)^2/2 + log_m n / 2}
        # Even simpler exact geometric bound on [M_trunc + 1, inf):
        # By b_m(n + m) = b_m(n) + b_m(floor(n/m) + 1) <= 2 b_m(n), for ALL j >= 1:
        # b_m(M + j) <= 2^{ceil(j/m)} b_m(M) <= 2 * (2^{1/m})^j * b_m(M), and 2^{1/m} / b <= 2^{1/2}/2 < 0.71!
        # Even cleaner rational bound: (2/b) for m >= 2? Wait: 2^{1/2} < 3/2, so for b >= 2, (3/2)/b <= 3/4!
        # Let's prove & use exact induction: for ALL n >= m, b_m(n + 1) <= b_m(n) + b_m(n // m + 1) <= 2 b_m(n)
        # Better: for n >= 1, b_m(n + m) <= 2 b_m(n) => b_m(M + r*m + t) <= 2^{r+1} b_m(M) (0 <= t < m),
        # so sum_{j>=1} b_m(M + j) b^{-(M+j)} <= b^{-M} b_m(M) * sum_{r>=0} 2^{r+1} * m * b^{-r*m - 1}
        # = b_m(M) * 2 * m / (b^{M+1} * (1 - 2 / b^m))!
        # Since b >= 2, m >= 2 => b^m >= 4 => 1 - 2/b^m >= 1/2 => tail <= 4 * m * b_m(M) / b^{M+1}!
        # Verify exact 1-step monotonicity bound b_m(n+m) <= 2 b_m(n) is trivial since b_m(floor(n/m)+1) <= b_m(n) for n >= m.
        def tail_fn(M, bm_ref=bm, b_ref=b, m_ref=m):
            return Fraction(4 * m_ref * bm_ref[M], b_ref ** (M + 1))

        int_part, digits, _ = certified_digits_from_series(bm, b, N_dig, tail_fn)
        # Reconstruct canonical carry delta_n via exact backward/forward recurrence!
        # delta_1 = X_{b, m} - {X_{b, m}} - b_m(0)? Careful:
        # X_{b, m} = b_m(0) + sum_{n>=1} b_m(n) b^{-n} = int_part + sum_{n>=1} d_n b^{-n}.
        # By Theorem 5.2 of GF-32, for a(n) = b_m(n) (n >= 1), F_b(a) = X_{b, m} - 1,
        # so delta_1 = F_b(a) - {X_{b, m}} = int_part - 1!
        # And delta_{n+1} = b * delta_n + d_n - b_m(n) for all n >= 1!
        deltas = [None] * (N_dig + 2)
        deltas[1] = int_part - 1
        for k in range(1, N_dig + 1):
            deltas[k + 1] = b * deltas[k] + digits[k - 1] - bm[k]
        # Verify exact positivity & asymptotic floor relation:
        # b_m(k)/(b - 1) - 1 < delta_k for all k = 1..N_dig
        for k in range(1, N_dig + 1):
            C.check_exact(sec, deltas[k] * (b - 1) > bm[k] - (b - 1),
                          f"Lower carry bound fail ({b},{m}) k={k}")
            # Verify gauge identity b_m(k) == d_k + b * delta_k - delta_{k+1}
            C.check_exact(sec, bm[k] == digits[k - 1] + b * deltas[k] - deltas[k + 1],
                          f"Gauge identity fail ({b},{m}) k={k}")
        # Verify exact Master Congruence for L = 1..6 and k = 1..150
        for L in range(1, 7):
            mod = b ** L
            for k in range(1, 151):
                W_L = 0
                A_L = 0
                for j in range(L):
                    W_L = W_L * b + digits[k - 1 + j]
                    A_L = A_L * b + bm[k + j]
                C.check_exact(sec, W_L % mod == (A_L + deltas[k + L]) % mod,
                              f"Master congruence fail ({b},{m}) L={L}, k={k}")
        # Verify exact carry-increment functional equations Delta_k = delta_{k+1} - delta_k
        for k in range(2, N_dig):
            Dk = deltas[k + 1] - deltas[k]
            Dkm1 = deltas[k] - deltas[k - 1]
            if k % m != 0:
                C.check_exact(sec, digits[k - 1] - digits[k - 2] == Dk - b * Dkm1,
                              f"Carry-inc non-div fail ({b},{m}) k={k}")
            else:
                C.check_exact(sec, bm[k // m] == (digits[k - 1] - digits[k - 2]) + b * Dkm1 - Dk,
                              f"Carry-inc div fail ({b},{m}) k={k}")
        # Verify exact binary carry-parity law for X_2: d_k(X_2) == delta_{k+1} mod 2 for ALL k >= 2
        if (b, m) == (2, 2):
            for k in range(2, N_dig + 1):
                C.check_exact(sec, digits[k - 1] == (deltas[k + 1] % 2),
                              f"Binary carry parity fail k={k}")
            carry_samples["X2"] = (int_part, digits[:24], deltas[1:12])

    # 3d. Carry-Valuation Barrier finite-prefix verification:
    #     Certify the exact shifted-perturbation identity sum h(k) * 2^{-k} = Delta'_120
    #     for 120-bit truncated differences Delta'_120 = (t_120 - x_120) mod 2^{120} (ignoring
    #     any lower-order borrow from bits beyond position 120), using quadratic shift
    #     L(n) = max(1, floor((log_2(n+1))^2 / 4)), on truncated 1/3, Champernowne C_2, and Lambda_2 prefixes.
    bm2 = mary_partitions(2, 450)
    int_X2, dig_X2, _ = certified_digits_from_series(
        bm2, 2, 160, lambda M: Fraction(8 * bm2[M], 2 ** (M + 1))
    )
    # Finite exact certificate for 120-bit truncated differences (exact Fraction sum)
    K_bits = 120
    # Build three distinct target bitstreams of length K_bits:
    # (1) 1/3 = 0.010101..._2, (2) Champernowne C_2 = 0.1 10 11 100 101 ..., (3) Lambda_2 = sum 2^{-2^s}
    champer = []
    n_c = 1
    while len(champer) < K_bits:
        champer.extend(int(ch) for ch in bin(n_c)[2:])
        n_c += 1
    champer = champer[:K_bits]
    lam2 = [1 if (i & (i - 1)) == 0 else 0 for i in range(1, K_bits + 1)]
    third2 = [0 if i % 2 == 1 else 1 for i in range(1, K_bits + 1)]

    for name, target_bits in [("third", third2), ("champernowne", champer), ("lambda2", lam2)]:
        # Exact nonnegative difference Delta' = (target_int - X2_int) mod 2^{K_bits} in [0, 1),
        # so every binary digit c_n lies in {0, 1} and h(k) >= 0, guaranteeing a(k) >= b_2(k) >= 1!
        t_int = bits_to_int(target_bits)
        x_int = bits_to_int(dig_X2[:K_bits])
        diff_int = (t_int - x_int) % (1 << K_bits)
        c_seq = [(diff_int >> (K_bits - 1 - i)) & 1 for i in range(K_bits)]
        # Push each term c_n * 2^{-n} forward by L(n) = max(1, floor((log_2(n+1))^2 / 4))
        h = {}
        last_k = 0
        for n in range(1, K_bits + 1):
            ln2 = (n + 1).bit_length() - 1  # floor(log_2(n + 1))
            Ln = max(1, (ln2 * ln2) // 4)
            k = n + Ln
            assert k > last_k  # strictly increasing since Ln is nondecreasing!
            last_k = k
            h[k] = c_seq[n - 1] * (1 << Ln)
        max_k = last_k
        # Verify exact Fraction sum: sum_{k=1}^{max_k} h[k] * 2^{-k} == diff_int / 2^{K_bits}
        lhs_frac = sum(Fraction(val, 1 << k) for k, val in h.items())
        rhs_frac = Fraction(diff_int, 1 << K_bits)
        C.check_exact(sec, lhs_frac == rhs_frac, f"Barrier sum mismatch for {name}")
        # Verify exact parity 2 | a(k) for all k >= 2, h(k) >= 0, and strict positivity a(k) >= b_2(k) >= 1
        for k in range(2, max_k + 1):
            hk = h.get(k, 0)
            ak = bm2[k] + hk
            C.check_exact(sec, hk >= 0 and ak >= bm2[k] >= 1 and ak % 2 == 0,
                          f"Positivity/parity fail {name} k={k}")
        # Verify that for L = 1..6, h(k) == 0 mod 2^L for all k above the threshold
        for L in range(1, 7):
            # Threshold: once floor(log_2(n+1))^2 // 4 >= L, i.e., floor(log_2(n+1)) >= ceil(sqrt(4L))
            s_req = math.isqrt(4 * L - 1) + 1
            n_req = (1 << s_req) - 1
            k_req = n_req + (s_req * s_req) // 4
            for k in range(k_req, max_k + 1):
                C.check_exact(sec, h.get(k, 0) % (1 << L) == 0,
                              f"Mod 2^{L} fail {name} at k={k}")

    return carry_samples


def verify_C4():
    sec = "C4. Short-orbit bridge for P_b = 1/E_b"
    print(f"Running {sec}...")

    # 4a. Exact partition-difference identity: p(k + 1 + m) - p_{<=k}(k + 1 + m) = sum_{j=0}^m p(j)
    #     for all 1 <= k <= 30 and 0 <= m <= k.
    p_tab = ordinary_partitions(65)
    p_cum = []
    acc = 0
    for x in p_tab:
        acc += x
        p_cum.append(acc)
    for k in range(1, 31):
        pk_tab = restricted_partitions(k, 2 * k + 1)
        for m in range(k + 1):
            diff = p_tab[k + 1 + m] - pk_tab[k + 1 + m]
            C.check_exact(sec, diff == p_cum[m], f"Part-diff fail k={k}, m={m}")

    # 4b. Exact two-sided real shadowing bounds for P_b - R_k^(E) using exact Fraction arithmetic
    #     Certify P_b to high precision via exact pentagonal series E_b and inversion 1 / E_b!
    shadow_table = []
    for b in [2, 3, 5, 10]:
        # Compute E_b bracket [E_lo, E_hi] using K = 15 pentagonal pairs (tail < 2 * b^{-w_{16}^-} = 2 * b^{-376})
        K_pent = 15
        E_part = Fraction(1)
        for j in range(1, K_pent + 1):
            g1 = j * (3 * j - 1) // 2
            g2 = j * (3 * j + 1) // 2
            sgn = -1 if (j % 2 == 1) else 1
            E_part += Fraction(sgn, b ** g1) + Fraction(sgn, b ** g2)
        g_next = (K_pent + 1) * (3 * (K_pent + 1) - 1) // 2  # 376
        err_E = Fraction(2, b ** g_next)
        # Since E_part > 0, P_lo = 1 / (E_part + err_E) < P_b < 1 / (E_part - err_E) = P_hi
        P_lo = Fraction(1) / (E_part + err_E)
        P_hi = Fraction(1) / (E_part - err_E)
        R_k = Fraction(1)
        for k in range(1, 21):
            R_k *= Fraction(b ** k, b ** k - 1)
            # Exact certified unconditional bounds on P_b - R_k (all b >= 2, k >= 1):
            # R_k / ((b - 1) * b^k) < P_lo - R_k < P_b - R_k < P_hi - R_k < P_lo / ((b - 1) * b^k) < P_b / ((b - 1) * b^k)
            lb = R_k / ((b - 1) * (b ** k))
            ub = P_lo / ((b - 1) * (b ** k))
            C.check_exact(sec, lb < P_lo - R_k and P_hi - R_k < ub,
                          f"Shadowing bound fail b={b}, k={k}")
            if k in [6, 12, 20]:
                shadow_table.append((b, k, float(P_lo - R_k), float(lb), float(ub)))

    # 4c. Exact p-adic valuations v_p(D_k^(E)) and v_p(T_k^(E)), plus elementary primitive-order
    #     factorization Phi_d(b) / d <= R(d) <= Phi_d(b).
    phi_tab = cyclotomic_table(26)
    for b in [2, 3, 5]:
        for d in range(2, 25):
            phi_val = poly_eval(phi_tab[d], b)
            pf_phi = factor_int(phi_val)
            # R(d) = product of p^{v_p(Phi_d(b))} over primes p with ord_p(b) = d
            R_d = 1
            for p, e in pf_phi.items():
                if ord_mod(b, p) == d:
                    R_d *= p ** e
            # Note: at d = 2, b = 3 mod 4: ord_2(b) = 1 != 2, and Phi_2(b) = b + 1 can have 2^a || b+1 (exception noted in proof!).
            if not (d == 2 and b % 4 == 3):
                C.check_exact(sec, phi_val % R_d == 0 and (phi_val // R_d) <= d and d % (phi_val // R_d) == 0,
                              f"Primitive factorization fail b={b}, d={d}: Phi={phi_val}, R={R_d}")

    # Check exact v_p(D_k^(E)) formula for b in {2, 3, 5, 7} and k = 1..16
    for b in [2, 3, 5, 7]:
        D_k = 1
        for k in range(1, 17):
            D_k *= (b ** k - 1)
            # Test odd primes p <= 13 not dividing b, and p = 2 if b odd
            test_primes = [p for p in [2, 3, 5, 7, 11, 13] if b % p != 0]
            for p in test_primes:
                vp_actual = v_p(D_k, p)
                if p == 2:
                    if b % 4 == 1:
                        e0 = v_p(b - 1, 2)
                        vp_form = e0 * k + v_p_fact(k, 2)
                    else:
                        e0 = v_p(b * b - 1, 2)
                        vp_form = ((k + 1) // 2) + e0 * (k // 2) + v_p_fact(k // 2, 2)
                else:
                    sp = ord_mod(b, p)
                    e0 = v_p(b ** sp - 1, p)
                    vp_form = e0 * (k // sp) + v_p_fact(k // sp, p)
                C.check_exact(sec, vp_actual == vp_form,
                              f"v_p(D_k) fail b={b}, k={k}, p={p}: {vp_actual} != {vp_form}")

    # 4d. Exact pentagonal orbit coupling inequality on P_b = 1/E_b (b in {2, 3, 5}, K = 1..8):
    #     || b^n P_b + sum_{j=1}^K (-1)^j (b^{n-w_j^-} P_b + b^{n-w_j^+} P_b) ||_T <= 2 P_b b^{n - w_{K+1}^-}
    #     for all n in [w_K^+, w_{K+1}^- - 1].
    for b in [2, 3, 5]:
        # Bracket P_b to precision b^{-220}
        K_hi = 12  # w_13^- = 247
        E_hi_part = Fraction(1)
        for j in range(1, K_hi + 1):
            g1 = j * (3 * j - 1) // 2
            g2 = j * (3 * j + 1) // 2
            sgn = -1 if (j % 2 == 1) else 1
            E_hi_part += Fraction(sgn, b ** g1) + Fraction(sgn, b ** g2)
        err_E = Fraction(2, b ** (13 * 38 // 2))  # g1(13) = 247
        P_lo = Fraction(1) / (E_hi_part + err_E)
        P_hi = Fraction(1) / (E_hi_part - err_E)
        P_mid = (P_lo + P_hi) / 2
        P_rad = (P_hi - P_lo) / 2
        for K in range(1, 9):
            wK_plus = K * (3 * K + 1) // 2
            wKp1_minus = (K + 1) * (3 * (K + 1) - 1) // 2
            # E_b^(K)
            EK = Fraction(1)
            for j in range(1, K + 1):
                g1 = j * (3 * j - 1) // 2
                g2 = j * (3 * j + 1) // 2
                sgn = -1 if (j % 2 == 1) else 1
                EK += Fraction(sgn, b ** g1) + Fraction(sgn, b ** g2)
            for n in range(wK_plus, wKp1_minus):
                val = (b ** n) * EK * P_mid
                # Circular distance ||val||_T = min(val - floor(val), ceil(val) - val)
                fl = math.floor(val)
                dist_mid = min(val - fl, (fl + 1) - val)
                # Account for interval radius (b^n * |EK| * P_rad)
                rad = (b ** n) * abs(EK) * P_rad
                rhs = 2 * P_lo * Fraction(1, b ** (wKp1_minus - n))
                C.check_exact(sec, dist_mid + rad <= rhs,
                              f"Pentagonal coupling fail b={b}, K={K}, n={n}")

    # 4e. Exact counterexamples for single-harmonic Weyl criteria in base b = 3:
    #     (i) x = 1/4: orbit {1/4, 3/4}, e(2 * 1/4) = e(1/2) = -1 => W_2 = -1, |W_2| = 1,
    #         yet Re W_2 = -1 != 1 and D(mu(1/4; 3)) = 1/2 < 1.
    d_14, n_14 = exact_orbit_disc(3, 1, 4)
    C.check_exact(sec, n_14 == 2 and d_14 == Fraction(1, 2), f"1/4 base-3 disc={d_14}")
    # Check 2 * (1/4) = 1/2 (mod 1) and 2 * (3/4) = 1/2 (mod 1) exactly
    C.check_exact(sec, Fraction(2 * 1, 4) - math.floor(Fraction(2 * 1, 4)) == Fraction(1, 2), "2*(1/4)")
    C.check_exact(sec, Fraction(2 * 3, 4) - math.floor(Fraction(2 * 3, 4)) == Fraction(1, 2), "2*(3/4)")
    #     (ii) 2-point fixed-point mixture sigma = (1/2) delta_0 + (1/2) delta_{1/2} in base 3:
    #          (b-1)*0 = 0 (mod 1) and (b-1)*(1/2) = 1 = 0 (mod 1) => Re W_2 = 1,
    #          yet W_1 = (e(0) + e(1/2))/2 = 0 => |W_1| = 0 < 1, and D(sigma) = 1/2 < 1!
    #          Compute exact D(sigma):
    g_sig = [Fraction(0), Fraction(1, 2), Fraction(0), Fraction(1, 2), Fraction(0)]
    C.check_exact(sec, max(g_sig) - min(g_sig) == Fraction(1, 2), "Fixed-point mixture disc")

    return shadow_table


# ===========================================================================
# PART II: FLOATING-POINT FINITE MEASUREMENTS (NOT ASYMPTOTIC EVIDENCE)
# ===========================================================================

def run_float_measurements():
    sec = "Float measurements (NOT asymptotic evidence)"
    print(f"Running {sec}...")

    # F1. Ramanujan-sum bound |ln Phi_d(b) - phi(d) ln b| <= 1/(b - 1)
    phi_tab = cyclotomic_table(30)
    for b in [2, 3, 5, 10]:
        for d in range(2, 31):
            val = poly_eval(phi_tab[d], b)
            phi_d = len(phi_tab[d]) - 1
            err = abs(math.log(val) - phi_d * math.log(b))
            C.check_float(sec, err <= 1.0 / (b - 1) + 1e-12,
                          f"Ramanujan bound fail b={b}, d={d}: err={err}")

    # F2. Exact quadratic period ratio ln(T_k^(E)) / (k^2 ln b) vs 1/2 - 3/pi^2
    target_c = 0.5 - 3.0 / (math.pi ** 2)
    period_ratios = []
    for b in [2, 3, 5]:
        kmax = 26 if b == 2 else (16 if b == 3 else 12)
        pf_D = {}
        for k in range(1, kmax + 1):
            for p, e in factor_int(b ** k - 1).items():
                pf_D[p] = pf_D.get(p, 0) + e
            # Compute T_k = lcm of ord(b, p^e)
            T = 1
            for p, e in pf_D.items():
                if p == 2:
                    if e == 1:
                        o = 1
                    elif b % 4 == 1:
                        o = 1 << max(0, e - v_p(b - 1, 2))
                    else:
                        o = 2 * (1 << max(0, e - v_p(b * b - 1, 2)))
                else:
                    op = ord_mod(b, p)
                    ap = v_p(b ** op - 1, p)
                    o = op * (p ** max(0, e - ap))
                T = math.lcm(T, o)
            if k in [8, 12, 16, 20, 26]:
                ratio = math.log(T) / (k * k * math.log(b))
                C.check_float(sec, 0.15 < ratio < 0.35, f"Ratio out of expected band b={b}, k={k}")
                period_ratios.append((b, k, ratio, ratio - target_c))

    # F3. Short-orbit Weyl sums W_1 and Re W_{b-1} on R_k^(E) vs P_b and Theorem C4.4 two-sided bounds
    short_orbit_data = []
    for b in [2, 3, 5]:
        N = 120
        Delta = 20
        # Compute P_b to precision b^{-220}
        E_val = Fraction(1)
        for j in range(1, 13):
            g1 = j * (3 * j - 1) // 2
            g2 = j * (3 * j + 1) // 2
            sgn = -1 if (j % 2 == 1) else 1
            E_val += Fraction(sgn, b ** g1) + Fraction(sgn, b ** g2)
        P_approx = Fraction(1) / E_val
        # Conservative k = N + Delta + 4 >= k_b(N, Delta) = N + Delta + ceil(log_b(2 * P_b / (b - 1)))
        k_req = N + Delta + math.ceil(math.log(2.0 * float(P_approx) / (b - 1), b))
        k = N + Delta + 4
        assert k >= k_req, f"k={k} < k_b({N},{Delta})={k_req} at b={b}"
        # Compute R_k^(E) mod 1 orbit points for 0 <= n < N via Fraction
        R_k = Fraction(1)
        for j in range(1, k + 1):
            R_k *= Fraction(b ** j, b ** j - 1)
        pts_P = []
        pts_R = []
        cur_P = P_approx
        cur_R = R_k
        for _ in range(N):
            fP = cur_P - math.floor(cur_P)
            fR = cur_R - math.floor(cur_R)
            pts_P.append(float(fP))
            pts_R.append(float(fR))
            cur_P = fP * b
            cur_R = fR * b
        # Extreme discrepancy D_N(P_b; b)
        sp = sorted(pts_P)
        D_N = max((i + 1) / N - sp[i] for i in range(N)) - min(i / N - sp[i] for i in range(N))
        W1_P = sum(cmath.exp(2j * math.pi * x) for x in pts_P) / N
        W1_R = sum(cmath.exp(2j * math.pi * x) for x in pts_R) / N
        Wbm1_P = sum(cmath.exp(2j * math.pi * (b - 1) * x) for x in pts_P) / N
        Wbm1_R = sum(cmath.exp(2j * math.pi * (b - 1) * x) for x in pts_R) / N
        # Verify shadowing Weyl error <= 2*pi*(b-1)*b^{-Delta}
        C.check_float(sec, abs(W1_P - W1_R) <= 2 * math.pi * (b ** (-Delta)) + 1e-12,
                      f"W1 shadow fail b={b}")
        C.check_float(sec, abs(Wbm1_P - Wbm1_R) <= 2 * math.pi * (b - 1) * (b ** (-Delta)) + 1e-12,
                      f"Wbm1 shadow fail b={b}")
        # Verify Theorem C4.4 quantitative lower bound on 1 - D_N
        lb_1mD = 2.0 * (1.0 - Wbm1_P.real) / (5.0 * (math.pi ** 2) * ((b - 1) ** 2)) - 1.0 / N
        C.check_float(sec, 1.0 - D_N >= lb_1mD - 1e-12,
                      f"C4.4 lower bound fail b={b}: 1-D={1-D_N}, lb={lb_1mD}")
        if b == 2:
            ub_1mD = (2.0 ** 0.75) * ((1.0 - W1_P.real) ** 0.25)
            C.check_float(sec, 1.0 - D_N <= ub_1mD + 1e-12,
                          f"C4.4 base-2 upper bound fail: 1-D={1-D_N}, ub={ub_1mD}")
        short_orbit_data.append((b, N, k, D_N, abs(W1_R), Wbm1_R.real, lb_1mD))

    return period_ratios, short_orbit_data


def main():
    t0 = time.perf_counter()
    dyadic_examples, base8_1norm, cyc_summary = verify_C1()
    verify_C2()
    carry_samples = verify_C3()
    shadow_table = verify_C4()
    period_ratios, short_orbit_data = run_float_measurements()
    elapsed = time.perf_counter() - t0

    print("\n=== Phase 24 Track C Verification Summary ===")
    for sec, (ex, fl) in C.by_section.items():
        print(f"  {sec}: {ex} exact, {fl} float")
    print(f"TOTAL: {C.exact} substantive exact checks + {C.float_meas} float measurements "
          f"= {C.exact + C.float_meas} total ({elapsed:.2f} s)")

    print("\n--- Selected Exact Certificate Highlights ---")
    for b, vals in dyadic_examples.items():
        s = ", ".join(f"P={P}:{float(d):.4f}" for P, d in vals)
        print(f"  C1 dyadic b={b} exact D(mu): {s}")
    print("  C1 base-8 exact 1-normal D(mu):",
          ", ".join(f"R={R}(P={P}):{d}={float(d):.5f}" for R, P, d in base8_1norm))
    chk59, chk60, p2_59, p2_60, wit60 = cyc_summary
    chosen60, deg60, z60, vals60 = wit60
    print(f"  C1 exhaustive cyclotomic search (2 <= L <= 60, deg < L/3, no exclusions): "
          f"{chk59 + chk60} divisors ({chk59} for L<=59 with {p2_59} in {{0,+-2^a}}, all rho_0 >= 1/3; "
          f"{chk60} for L=60 with {p2_60} in {{0,+-2^a}}, unique witness Q=Phi_{chosen60} "
          f"deg={deg60}, S_i in {vals60}, rho_0={z60}/60=3/10 < 1/3)")
    if "X2" in carry_samples:
        ip, d24, del11 = carry_samples["X2"]
        print(f"  C3 X_2 int_part={ip}, first 24 bits={''.join(map(str, d24))}, delta_1..11={del11}")

    print("\n--- Selected Finite Measurements (NOT asymptotic evidence) ---")
    print("  C4 ln(T_k^(E))/(k^2 ln b) vs 1/2 - 3/pi^2 = 0.196036:")
    for b, k, r, diff in period_ratios:
        print(f"    b={b}, k={k:2d}: ratio={r:.6f} (diff={diff:+.6f})")
    print("  C4 short-orbit Weyl sums on R_k^(E) vs D_N(P_b) (N=120, Delta=20, conservative k=144 >= k_b(120,20)):")
    for b, N, k, dn, w1, wbm1, lb in short_orbit_data:
        print(f"    b={b}, N={N}, k={k}: D_N(P_b)={dn:.5f}, |W_1(R_k)|={w1:.5f}, Re(W_{{b-1}}(R_k))={wbm1:.5f}, "
              f"1-D_N(P_b)={1-dn:.5f} >= lb(P_b)={lb:.5f}")


if __name__ == "__main__":
    main()
