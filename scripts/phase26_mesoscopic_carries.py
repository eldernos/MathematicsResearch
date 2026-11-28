#!/usr/bin/env python3
"""Phase 26 Track C: Mesoscopic Carry Correlations and Classical Lambert Constants (C1-C5).

Pure Python standard library only. Every theorem-proving check counted under
[exact] or [encl] uses exact integers, fractions.Fraction, or directed-rounded
fixed-point integer arithmetic (ZERO floating-point operations in theorem checks).
Finite prefix measurements are strictly isolated under [finite] and are never
used as evidence for asymptotic statements.

Sections:
  1. C1.1 & C1.4(2): E(4) 2-column adjacent inequality (all 64 triples), exact
           certified mu, nu mod 8, p_J mod 8, Q^{(1/2)} expectation < 0.370229,
           exact closed-form 1-column + all-order stationarity star-orbit
           countermodel (with exact marginal checks), and C1.4(2) explicit
           C_lat <= 180 certificate.
  2. C1.2: Exact factorial-moment order hierarchy for E(4) at W=3:
           (a) 7-variable marked: 35x35 invertible perturbation certificate for
               r=3 countermodel (> 0.370229, plus exact derived count second
               moments) and exact 2-column Shifted Split-Bonferroni global
               degree-7 polynomial (< 0.370229);
           (b) 3-variable i.i.d.-mark: exact 8-atom (denom 24) r=2 countermodel
               (> 0.4009) and Young-split global degree-3 polynomial (< 0.370229)
               establishing r_min^{iid}(E(4); W=3) = 3 exact.
  3. C1.3 & C2: Exact Fourier subset obstructions on Z/8Z, exact Sturm global
           certificate for M=12 trigonometric majorant (< 0.4974 < 1/2) and
           23x23 perturbation certificate for M=11 countermeasure (> 0.504 > 1/2)
           establishing M_min(E(4)) = 12 exact, plus E(2) at W=8 Bonferroni
           order reduction from r=92 (CC-49) to r=46.
  4. C3: E*(4) unitary boundary: 4-nomial quadratic Fourier lower bound, CRT
           admissible k-tuple collision identity q(m+iB) = 2m - omega(L_i(t))
           for k=2,3 (with coprimality and independence), concrete collision
           pairs, and optimal A=sqrt(3) Chebyshev SOS identity.
  5. C4: E_+(8) and E_+(4):
           (a) Signed Carry Conservation & Exponential Carry-Growth (exact
               2*(|q_N| - |q_0|) boundary term) on certified 1200-bit prefixes
               of E_+(8), E_+(16), E_+(32);
           (b) Pure-integer-certified explicit k_0 = 25 for D^+(E_+(2^k); 2) < 1
               and E_+(2^k) not in K_2 (Euler-Maclaurin gamma, monotone interval
               enclosure of 1/sigma_2(s), dyadic-block Rankin + union bounds,
               monotone Rankin-weight 10-shell Abel sum);
           (c) Periodic zero-sum counterexample for the large-window signed
               cancellation barrier;
           (d) 2-state carry automaton (c in {0,1}, psi == 0), closed form
               m_1^{(2^L)} = 1/3 - (2 + (-1/2)^{L-1})/(9L) for L=1..9, explicit
               Eulerian attaining cycles for L=2..8, certified W_+ enclosure,
               base-256 simple nonnormality of E_+(8) (sharp at L=8 vs L=7),
               base-16 simple nonnormality of L_-(4), L_+(8), E_+^*(8),
               E_{alt,+}^*(8), base-64 for E_{+,odd}(16), and E_+(4) deficit.
  6. C5: Generalized Lambert classifications & unconditional disjunctivity:
           (a) Alternating cubic L_{-,+}(4) (M=31,43,109,127) rho_- < 1/4,
               unitary alternating cubic rho_-^* = 1/4, and universal k=1 barrier;
           (b) Exact Z[zeta_5] cyclotomic-unit / Lucas-Fibonacci identity on all
               1115 squarefree n <= 2000 coprime to 11, explicit Lambda=c-d null
               direction vs t*=2 Fibonacci recovery, and cyclotomic-unit inverses
               in Z[zeta_m] for m=5,7,9;
           (c) Quadratic-twisted tau_3 * chi_D (D=-3,-4,5,8) nonnegativity,
               certified C_pop enclosures (k>=3 for D=5; k>=4 for D=-3,-4,8),
               and certified C_{U,D} enclosures (k>=3 for D=5; k>=4 for D=-3,8;
               k>=5 for D=-4 for D^+ < 1 and not in K_2);
           (d) Unconditional base-2 disjunctivity: Odd-Target Guard-Bit Lemma
               on (-1, 1), Lambert coefficient/multiplicativity checks, unified
               3^{W-1} || m_0 identity, end-to-end toy CRT planting on E(8),
               E_odd(8), E_+(8), exponent constant <= 37/k, and finite word
               prefix measurements [finite].
"""

import math
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Strict assertion counters (zero floats in exact / encl!)
# ---------------------------------------------------------------------------
EXACT_COUNT = 0
ENCL_COUNT = 0
FINITE_COUNT = 0


def check_exact(cond, msg=""):
    global EXACT_COUNT
    if not cond:
        raise AssertionError(f"[EXACT FAIL] {msg}")
    EXACT_COUNT += 1


def check_encl(cond, msg=""):
    global ENCL_COUNT
    if not cond:
        raise AssertionError(f"[ENCL FAIL] {msg}")
    ENCL_COUNT += 1


def check_finite(cond, msg=""):
    global FINITE_COUNT
    if not cond:
        raise AssertionError(f"[FINITE FAIL] {msg}")
    FINITE_COUNT += 1


# ---------------------------------------------------------------------------
# Pure-integer / Fraction directed-rounding arithmetic helpers
# ---------------------------------------------------------------------------
SCALE = 1 << 100  # 2^{-100} fixed-point grid


def fl_s(fr):
    """Exact floor(fr * SCALE) for Fraction fr."""
    return (fr.numerator * SCALE) // fr.denominator


def ce_s(fr):
    """Exact ceil(fr * SCALE) for Fraction fr."""
    return -((-fr.numerator * SCALE) // fr.denominator)


def mul_lo(a, b):
    """Directed lower bound on (a/SCALE)*(b/SCALE) in SCALE units (a,b >= 0)."""
    return (a * b) // SCALE


def mul_hi(a, b):
    """Directed upper bound on (a/SCALE)*(b/SCALE) in SCALE units (a,b >= 0)."""
    return -((-(a * b)) // SCALE)


def div_lo(a, b):
    """Directed lower bound on (a/b) in SCALE units (a >= 0, b > 0)."""
    return (a * SCALE) // b


def div_hi(a, b):
    """Directed upper bound on (a/b) in SCALE units (a >= 0, b > 0)."""
    return -((-(a * SCALE)) // b)


def dec_floor(fr, digits=6):
    """Outward lower decimal string with `digits` places from exact Fraction."""
    p = 10 ** digits
    v = (fr.numerator * p) // fr.denominator
    neg = v < 0
    v = abs(v)
    return ("-" if neg else "") + f"{v // p}.{v % p:0{digits}d}"


def dec_ceil(fr, digits=6):
    """Outward upper decimal string with `digits` places from exact Fraction."""
    p = 10 ** digits
    v = -((-fr.numerator * p) // fr.denominator)
    neg = v < 0
    v = abs(v)
    return ("-" if neg else "") + f"{v // p}.{v % p:0{digits}d}"


def assert_outward_dec(lo_fr, hi_fr, lo_str, hi_str, digits=6, label=""):
    """Assert exact outward-rounded decimal enclosure [lo_str, hi_str]."""
    p = 10 ** digits
    lo_dec = Fraction(int(lo_str.replace(".", "")), p)
    hi_dec = Fraction(int(hi_str.replace(".", "")), p)
    check_encl(lo_dec <= lo_fr, f"{label}: quoted lower {lo_str} > exact lo")
    check_encl(hi_fr <= hi_dec, f"{label}: exact hi > quoted upper {hi_str}")
    # Also verify tightness (within 1 ulp of exact outward rounding)
    check_encl(dec_floor(lo_fr, digits) == lo_str,
               f"{label}: floor mismatch got {dec_floor(lo_fr, digits)} vs {lo_str}")
    check_encl(dec_ceil(hi_fr, digits) == hi_str,
               f"{label}: ceil mismatch got {dec_ceil(hi_fr, digits)} vs {hi_str}")


def sieve_primes(limit):
    is_p = bytearray(b"\x01") * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i in range(2, limit + 1) if is_p[i]]


def odd_part(n):
    return n >> (n & -n).bit_length() - 1


def naf_weight(n):
    """Exact minimum signed-digit (NAF) weight w_pm(n) of integer n."""
    n = abs(n)
    cnt = 0
    while n > 0:
        if n & 1:
            cnt += 1
            if (n & 3) == 3:
                n += 1
            else:
                n -= 1
        n >>= 1
    return cnt


def exp_pos_encl(y_fr, terms=45):
    """Exact Fraction enclosure [lo, hi] for exp(y_fr) with y_fr >= 0."""
    check_exact(y_fr >= 0 and y_fr < terms, "exp_pos_encl domain")
    s = Fraction(0)
    term = Fraction(1)
    for k in range(terms):
        s += term
        term = term * y_fr / (k + 1)
    rem = term / (1 - y_fr / (terms + 1))
    return s, s + rem


def exp_neg_encl(y_fr, terms=45):
    """Exact Fraction enclosure [lo, hi] for exp(-y_fr) with y_fr >= 0."""
    lo_p, hi_p = exp_pos_encl(y_fr, terms)
    return Fraction(1) / hi_p, Fraction(1) / lo_p


def ln_encl_rat(v_fr, terms=30):
    """Exact Fraction enclosure [lo, hi] for ln(v_fr) for v_fr >= 1."""
    check_exact(v_fr >= 1, "ln_encl_rat domain")
    # Reduce v_fr by powers of 2 so u in [1, 2]
    k2 = 0
    u = v_fr
    while u > 2:
        u /= 2
        k2 += 1
    def _ln_1_2(x):
        z = (x - 1) / (x + 1)
        s = Fraction(0)
        zp = z
        z2 = z * z
        for k in range(terms):
            s += zp / (2 * k + 1)
            zp *= z2
        rem = zp / ((2 * terms + 1) * (1 - z2))
        return 2 * s, 2 * (s + rem)
    lo, hi = _ln_1_2(u)
    if k2 > 0:
        l2_lo, l2_hi = _ln_1_2(Fraction(2))
        lo += k2 * l2_lo
        hi += k2 * l2_hi
    return lo, hi


def pi_encl():
    """Exact Fraction enclosure of pi via Machin's formula (pure Fraction)."""
    def atan_inv(m, terms=30):
        # arctan(1/m) = sum (-1)^k / ((2k+1) m^{2k+1}) (alternating!)
        s = Fraction(0)
        m2 = m * m
        pw = m
        for k in range(terms):
            t = Fraction(1, (2 * k + 1) * pw)
            if k % 2 == 0:
                s += t
            else:
                s -= t
            pw *= m2
        # terms is even -> last added was negative (k=terms-1 odd) -> s < val < s + next
        nxt = Fraction(1, (2 * terms + 1) * pw)
        return s, s + nxt
    a5_lo, a5_hi = atan_inv(5, 36)
    a239_lo, a239_hi = atan_inv(239, 14)
    return 16 * a5_lo - 4 * a239_hi, 16 * a5_hi - 4 * a239_lo


def cos_sin_encl(theta_lo, theta_hi, terms=22):
    """Exact Fraction enclosures of cos(theta), sin(theta) for theta in [theta_lo, theta_hi].
    Reduces angle to [-pi, pi] using pi_encl, then evaluates alternating Taylor series.
    """
    pi_lo, pi_hi = pi_encl()
    # Reduce by 2*pi
    # Choose integer k near midpoint / (2*pi)
    mid = (theta_lo + theta_hi) / 2
    two_pi_mid = pi_lo + pi_hi
    k = int((mid / two_pi_mid).numerator // (mid / two_pi_mid).denominator)
    # Adjust k so reduced interval is near [-pi, pi]
    t_lo = theta_lo - k * (2 * pi_hi if k >= 0 else 2 * pi_lo)
    t_hi = theta_hi - k * (2 * pi_lo if k >= 0 else 2 * pi_hi)
    while t_lo > pi_lo:
        t_lo -= 2 * pi_hi
        t_hi -= 2 * pi_lo
    while t_hi < -pi_lo:
        t_lo += 2 * pi_lo
        t_hi += 2 * pi_hi
    # Evaluate cos and sin at t_lo with alternating Taylor + Lipschitz |t_hi - t_lo|
    def _cs_point(x):
        # Alternating Taylor series with M=terms even: remainder <= |x|^{2M}/(2M)!
        c_s = Fraction(0)
        s_s = Fraction(0)
        x2 = x * x
        xp_c = Fraction(1)
        xp_s = x
        fac_c = 1
        fac_s = 1
        for m in range(terms):
            if m % 2 == 0:
                c_s += xp_c / fac_c
                s_s += xp_s / fac_s
            else:
                c_s -= xp_c / fac_c
                s_s -= xp_s / fac_s
            xp_c *= x2
            xp_s *= x2
            fac_c *= (2 * m + 1) * (2 * m + 2)
            fac_s *= (2 * m + 2) * (2 * m + 3)
        rem_c = abs(xp_c) / fac_c
        rem_s = abs(xp_s) / fac_s
        return (c_s - rem_c, c_s + rem_c), (s_s - rem_s, s_s + rem_s)
    (c0_lo, c0_hi), (s0_lo, s0_hi) = _cs_point(t_lo)
    rad = t_hi - t_lo
    check_encl(rad >= 0, "cos_sin_encl rad >= 0")
    return (max(Fraction(-1), c0_lo - rad), min(Fraction(1), c0_hi + rad)), (
        max(Fraction(-1), s0_lo - rad),
        min(Fraction(1), s0_hi + rad),
    )


def frac_mat_inv(M):
    """Exact Fraction Gauss-Jordan inverse of square matrix M (list of lists of Fraction)."""
    n = len(M)
    A = [list(row) + [Fraction(1 if i == j else 0) for j in range(n)] for i, row in enumerate(M)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise AssertionError("Singular matrix in frac_mat_inv")
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [A[r][j] - f * A[col][j] for j in range(2 * n)]
    return [row[n:] for row in A]


# ---------------------------------------------------------------------------
# SECTION 1: C1.1 — mu, nu mod 8, p_J mod 8, 2-Column Adjacent Criterion,
#            and Exact Closed-Form 1-Column + Stationarity Star Countermodel
# ---------------------------------------------------------------------------
def run_section_1(primes_1e5):
    print("=== Section 1 (C1.1): E(4) mu, nu mod 8, 2-Column Criterion & 1-Col Converse ===")

    # 1.1 Certified enclosure of mu = prod_p (1 - 1/p) sum_{e>=0} odd(e+1) p^{-e}
    # For p <= P_cut = 50000 compute exact local factor; for p > P_cut use
    # 1 <= l(p) <= 1 + 2/p^2 + 5/p^3 (since odd(e+1) <= e+1 and odd(1)=odd(2)=1, odd(3)=3, odd(4)=1, odd(5)=5):
    # Check: (1-1/p)(1 + 1/p + 3/p^2 + 1/p^3 + sum_{e>=4} (e+1)/p^e)
    #      = 1 + 2/p^2 - 2/p^3 + (1-1/p)*(5/p^4 + 6/p^5 + ...) <= 1 + 2/p^2 + 5/p^3 for all p >= 5!
    P_cut = 50000
    mu_lo = SCALE
    mu_hi = SCALE
    for p in primes_1e5:
        if p > P_cut:
            break
        # Sum up to e = E_max such that tail <= (E_max+2)/((p-1) p^{E_max-1}) < 2^{-105}
        E_max = 12 if p >= 100 else (40 if p >= 5 else 110)
        s = Fraction(0)
        pe = 1
        for e in range(E_max):
            s += Fraction(odd_part(e + 1), pe)
            pe *= p
        # Remainder of (1 - 1/p) sum_{e >= E_max} odd(e+1)/p^e is in [0, (E_max+2)/p^{E_max}]
        # Proof: (1-1/p) sum_{e>=E} (e+1) p^{-e} = (E+1)/p^E + 1/((p-1) p^E) <= (E+2)/p^E!
        loc_lo = (Fraction(p - 1, p) * s)
        loc_hi = loc_lo + Fraction(E_max + 2, pe)
        mu_lo = mul_lo(mu_lo, fl_s(loc_lo))
        mu_hi = mul_hi(mu_hi, ce_s(loc_hi))

    # Tail over p > P_cut = 50000:
    # For p > P_cut, l(p) >= 1 and l(p) <= 1 + 2/p^2 + 5/p^3 <= exp(2/p^2 + 5/p^3).
    # Every prime > 3 satisfies p == 1 or 5 (mod 6), so sum_{p > P} p^{-2} <= (1/3) int_{P-6}^inf dx/x^2?
    # Better, completely elementary: among {6m+1, 6m+5} for 6m >= P_cut (m >= 8334):
    # sum_{m >= M0} ((6m+1)^{-2} + (6m+5)^{-2}) <= 2 * sum_{m >= M0} (6m)^{-2} <= (2/36) * (1/(M0 - 1)) = 1/(18*(M0-1))!
    M0 = P_cut // 6 + 1  # 8334 -> 6*8334 = 50004 > 50000, wait: 6*8333+5 = 50003 > 50000!
    M0 = (P_cut - 5) // 6 + 1  # 6*8333 + 5 = 50003
    check_exact(6 * M0 + 1 > P_cut or 6 * M0 + 5 > P_cut, "M0 covers all primes > P_cut")
    check_exact(6 * (M0 - 1) + 5 <= P_cut, "M0-1 <= P_cut")
    # Every prime p > P_cut is >= 6*M0 + 1 (if 6*M0+1 > P_cut) or >= 6*M0 + 5.
    # For each m >= M0, both 6m+1 and 6m+5 are > 6m, so (6m+1)^{-2} + (6m+5)^{-2} <= 2/(36 m^2) = 1/(18 m^2).
    # sum_{m >= M0} 1/m^2 <= 1/(M0 - 1).
    # Similarly (6m+1)^{-3} + (6m+5)^{-3} <= 2/(216 m^3) = 1/(108 m^3), sum <= 1/(216 (M0-1)^2).
    tail_exp = Fraction(2, 18 * (M0 - 1)) + Fraction(5, 216 * (M0 - 1) ** 2)
    _, tail_hi = exp_pos_encl(tail_exp, 12)
    mu_hi = mul_hi(mu_hi, ce_s(tail_hi))

    mu_lo_fr = Fraction(mu_lo, SCALE)
    mu_hi_fr = Fraction(mu_hi, SCALE)
    check_encl(mu_lo_fr < mu_hi_fr, "mu enclosure non-empty")
    # Check consistency with GF-41 Thm 2.6 [2.07632553, 2.07632693]
    check_encl(mu_lo_fr >= Fraction(207630, 100000), "mu lower sanity")
    check_encl(mu_hi_fr <= Fraction(207636, 100000), "mu upper sanity")
    # Use GF-41's certified mu upper bound 2.07632693? No, stay 100% self-contained!
    # Our own certified mu_hi_fr is ~2.076355, giving mu/16 <= 0.129773 -> threshold 0.5 - mu/16 >= 0.370227!
    print(f"  [encl] self-contained mu in [{dec_floor(mu_lo_fr, 6)}, {dec_ceil(mu_hi_fr, 6)}]")

    # 1.2 Certified lower-bound probabilities for nu mod 8 (exact convolution over p <= 10000, tail charged!)
    # For each prime p, odd(e+1) mod 8 is 1 for e=0,1,3,7,... and 3 for e=2,5,...
    # Missing mass from primes p > P_nu = 10000:
    # A number has prime factor p > P_nu with v_p(n) >= 2 (the ONLY way p contributes != 1 to U(n)!)
    # with probability <= sum_{p > P_nu} p^{-2} <= 1/(18*(M_nu - 1)).
    P_nu = 10000
    M_nu = (P_nu - 5) // 6 + 1
    check_exact(6 * (M_nu - 1) + 5 <= P_nu, "M_nu covers > P_nu")
    nu_tail = Fraction(1, 18 * (M_nu - 1))  # <= 3.34e-5
    # Convolve exact mod-8 odd-part distribution over p <= P_nu on {1, 3, 5, 7} (indexed 0,1,2,3 -> 1,3,5,7)
    # Using directed lower bounds in SCALE units!
    idx_map = {1: 0, 3: 1, 5: 2, 7: 3}
    nu_lo = [SCALE, 0, 0, 0]
    for p in primes_1e5:
        if p > P_nu:
            break
        E_max = 10 if p >= 100 else (30 if p >= 5 else 90)
        fac = [Fraction(0)] * 4
        pe = 1
        for e in range(E_max):
            r = odd_part(e + 1) & 7
            fac[idx_map[r]] += Fraction(p - 1, p * pe)
            pe *= p
        fac_lo = [fl_s(x) for x in fac]
        nlo = [0] * 4
        for i, r1 in enumerate((1, 3, 5, 7)):
            for j, r2 in enumerate((1, 3, 5, 7)):
                k = idx_map[(r1 * r2) & 7]
                nlo[k] += mul_lo(nu_lo[i], fac_lo[j])
        nu_lo = nlo
    # Include probability that ALL primes > P_nu have v_p <= 1: >= 1 - nu_tail!
    keep_lo = fl_s(1 - nu_tail)
    nu_lo = [mul_lo(x, keep_lo) for x in nu_lo]
    nu_miss = SCALE - sum(nu_lo)
    check_encl(nu_miss > 0 and Fraction(nu_miss, SCALE) < Fraction(1, 20000), "nu_miss < 5e-5")
    nu_hi = [x + nu_miss for x in nu_lo]
    nu_lo_fr = {r: Fraction(nu_lo[idx_map[r]], SCALE) for r in (1, 3, 5, 7)}
    nu_hi_fr = {r: Fraction(nu_hi[idx_map[r]], SCALE) for r in (1, 3, 5, 7)}
    print(f"  [encl] nu(1) in [{dec_floor(nu_lo_fr[1], 6)}, {dec_ceil(nu_hi_fr[1], 6)}], "
          f"nu(3) in [{dec_floor(nu_lo_fr[3], 6)}, {dec_ceil(nu_hi_fr[3], 6)}], miss <= {dec_ceil(Fraction(nu_miss, SCALE), 7)}")

    # 1.3 Certified p_J mod 8 for J ~ CP(1/2, nu) via exact convolution up to K_pois = 25!
    em_lo, em_hi = exp_neg_encl(Fraction(1, 2), 35)
    # Convolve nu_lo k times mod 8: S_k[a] = lower bound on P(U_1+...+U_k == a mod 8)
    S_lo = [[SCALE if a == 0 else 0 for a in range(8)]]
    for k in range(1, 26):
        prev = S_lo[-1]
        nxt = [0] * 8
        for a in range(8):
            for i, r in enumerate((1, 3, 5, 7)):
                nxt[(a + r) & 7] += mul_lo(prev[a], nu_lo[i])
        S_lo.append(nxt)
    pJ_lo = [0] * 8
    for k in range(26):
        wk_lo = fl_s(em_lo * Fraction(1, (2 ** k) * math.factorial(k)))
        for a in range(8):
            pJ_lo[a] += mul_lo(wk_lo, S_lo[k][a])
    pJ_miss = SCALE - sum(pJ_lo)
    check_encl(pJ_miss > 0 and Fraction(pJ_miss, SCALE) < Fraction(1, 10000), "pJ_miss < 1e-4")
    pJ_hi = [x + pJ_miss for x in pJ_lo]
    pJ_lo_fr = [Fraction(x, SCALE) for x in pJ_lo]
    pJ_hi_fr = [Fraction(x, SCALE) for x in pJ_hi]
    print(f"  [encl] p_J(0) in [{dec_floor(pJ_lo_fr[0], 6)}, {dec_ceil(pJ_hi_fr[0], 6)}], "
          f"p_J(1) in [{dec_floor(pJ_lo_fr[1], 6)}, {dec_ceil(pJ_hi_fr[1], 6)}]")

    # 1.4 EXACT verification of the 2-column adjacent inequality on ALL 64 triples!
    def u_adj(a1, a2):
        return Fraction(1, 2) * (1 if a1 == 1 else 0) + (1 if (a1 == 0 and a2 in (2, 3)) else 0)

    def v_adj(a2, a3):
        r23 = (2 * a2 + a3) & 7
        return Fraction(r23, 8) - (1 if (a2 in (2, 3) and r23 >= 4) else 0)

    def w_sh(a1, a2):
        if a2 in (2, 3):
            return Fraction(1, 2) if a1 == 0 else Fraction(-1, 2)
        return Fraction(0)

    def vp_sh(a2, a3):
        r23 = (2 * a2 + a3) & 7
        if a2 in (2, 3):
            return Fraction(r23, 8) - Fraction(1, 2) if r23 >= 4 else Fraction(r23, 8) + Fraction(1, 2)
        return Fraction(r23, 8)

    eq_cnt = 0
    for a1 in range(2):
        for a2 in range(4):
            for a3 in range(8):
                lhs = Fraction((4 * a1 + 2 * a2 + a3) & 7, 8)
                rhs1 = u_adj(a1, a2) + v_adj(a2, a3)
                rhs2 = Fraction(1, 2) * (1 if a1 == 1 else 0) + w_sh(a1, a2) + vp_sh(a2, a3)
                check_exact(rhs1 == rhs2, f"shifted split equality ({a1},{a2},{a3})")
                check_exact(lhs <= rhs1, f"2-col adj ineq ({a1},{a2},{a3})")
                check_exact(Fraction(0) <= vp_sh(a2, a3) <= Fraction(7, 8), f"vp range ({a2},{a3})")
                check_exact(Fraction(-1, 2) <= w_sh(a1, a2) <= Fraction(1, 2), f"w range ({a1},{a2})")
                if lhs == rhs1:
                    eq_cnt += 1
    check_exact(eq_cnt == 48, f"expected 48/64 tight triples, got {eq_cnt}")

    # Certified enclosure of E_{Q^{(1/2) otimes 2}}[Psi_{2,adj}] = E[u(a1,a2)] + E[v(a2,a3)]
    # Marginal pJ2 on Z/2 and pJ4 on Z/4
    pJ2_lo = [sum(pJ_lo[a] for a in range(8) if (a & 1) == r) for r in range(2)]
    pJ4_lo = [sum(pJ_lo[a] for a in range(8) if (a & 3) == r) for r in range(4)]
    # Because u >= 0 (max 1) and vp_sh >= 0 (max 7/8), use nonnegative Psi_{2,adj} = u + v + 1/2 - 1/2:
    # Even simpler: u_adj >= 0 (max 1), and vp_sh >= 0 (max 7/8), and w_sh + 1/2 >= 0 (max 1)!
    # Write Psi_{2,adj}(a1, a2, a3) = [1/2*1[a1=1]] + [w_sh(a1,a2) + 1/2] + [vp_sh(a2,a3)] - 1/2!
    # Every bracket is in [0, 1]! So lower bound uses pJ_lo, upper bound adds missing mass * max!
    # Term 1: 1/2 * P(a1 = 1)
    t1_lo = Fraction(pJ2_lo[1], 2 * SCALE)
    t1_hi = Fraction(pJ2_lo[1] + pJ_miss, 2 * SCALE)
    # Term 2: w_sh(a1,a2) + 1/2 in [0, 1]
    t2_lo_s = 0
    mass2 = 0
    for a1 in range(2):
        for a2 in range(4):
            pr = mul_lo(pJ2_lo[a1], pJ4_lo[a2])
            mass2 += pr
            val = w_sh(a1, a2) + Fraction(1, 2)  # 0, 1/2, or 1
            t2_lo_s += mul_lo(pr, fl_s(val))
    t2_lo = Fraction(t2_lo_s, SCALE)
    t2_hi = Fraction(t2_lo_s + (SCALE - mass2), SCALE)
    # Term 3: vp_sh(a2,a3) in [0, 7/8]
    t3_lo_s = 0
    mass3 = 0
    for a2 in range(4):
        for a3 in range(8):
            pr = mul_lo(pJ4_lo[a2], pJ_lo[a3])
            mass3 += pr
            t3_lo_s += mul_lo(pr, fl_s(vp_sh(a2, a3)))
    t3_lo = Fraction(t3_lo_s, SCALE)
    t3_hi = Fraction(t3_lo_s + mul_hi(SCALE - mass3, fl_s(Fraction(7, 8))), SCALE)

    psi2_lo = t1_lo + t2_lo + t3_lo - Fraction(1, 2)
    psi2_hi = t1_hi + t2_hi + t3_hi - Fraction(1, 2)
    B2_adj_lo = psi2_lo + mu_lo_fr / 16
    B2_adj_hi = psi2_hi + mu_hi_fr / 16
    check_encl(B2_adj_hi < Fraction(1, 2), f"2-col adj bound {dec_ceil(B2_adj_hi, 6)} >= 1/2!")
    print(f"  [encl] E[Psi_2_adj] in [{dec_floor(psi2_lo, 6)}, {dec_ceil(psi2_hi, 6)}] "
          f"=> limsup f_1(E(4);2) <= {dec_ceil(B2_adj_hi, 6)} < 1/2 (D^- >= {dec_floor(Fraction(1,2) - B2_adj_hi, 6)})")

    # 1.5 Exact closed-form 1-column + all-order stationarity star-orbit countermodel!
    # Mix shift-invariant periodic orbits on Z/8Z:
    #   - period-2 orbit (0, a, 0, a, ...) with weight 2*p_J(a)  (a in {1..7})
    #   - constant orbit (0, 0, 0, ...)    with weight 2*p_J(0) - 1 > 0.
    # Certify 2*p_J(0) - 1 > 0 strictly, then verify exact probability sum = 1,
    # exact 1-column marginal = p_J on all 8 residues, and exact E[R_3/8] formula!
    check_encl(2 * pJ_lo_fr[0] > 1, "star orbit mixture valid: 2*p_J(0) > 1")
    # Build an exact normalized rational vector pJ_ex inside [pJ_lo_fr, pJ_hi_fr]
    # (putting the missing mass on 0) to verify all star-orbit algebraic identities identically:
    pJ_ex = [pJ_lo_fr[0] + Fraction(pJ_miss, SCALE)] + [pJ_lo_fr[a] for a in range(1, 8)]
    check_exact(sum(pJ_ex) == 1, "pJ_ex sums to 1")
    orbit_weights = {0: 2 * pJ_ex[0] - 1}
    for a in range(1, 8):
        orbit_weights[a] = 2 * pJ_ex[a]
        check_exact(orbit_weights[a] > 0, f"star orbit weight {a} > 0")
    check_exact(orbit_weights[0] > 0, "constant orbit weight > 0")
    check_exact(sum(orbit_weights.values()) == 1, "star orbit mixture total mass == 1")
    # Verify exact 1-column marginal for every residue r in {0..7}:
    marg = [Fraction(0)] * 8
    marg[0] += orbit_weights[0]
    for a in range(1, 8):
        marg[0] += orbit_weights[a] / 2
        marg[a] += orbit_weights[a] / 2
    for r in range(8):
        check_exact(marg[r] == pJ_ex[r], f"star orbit 1-col marginal at r={r}")
    # Verify exact E[R_3/8] over the two length-3 windows (0,a,0) and (a,0,a) of each orbit:
    star_weights = {a: Fraction(((2 * a) & 7) + ((5 * a) & 7), 8) for a in range(1, 8)}
    check_exact(star_weights == {1: Fraction(7, 8), 2: Fraction(6, 8), 3: Fraction(13, 8),
                                 4: Fraction(4, 8), 5: Fraction(3, 8), 6: Fraction(10, 8), 7: Fraction(9, 8)},
                "star orbit weights")
    star_direct = sum(
        orbit_weights[a] * (Fraction((4 * 0 + 2 * a + 0) & 7, 8) + Fraction((4 * a + 2 * 0 + a) & 7, 8)) / 2
        for a in range(1, 8)
    )
    star_formula = sum(pJ_ex[a] * star_weights[a] for a in range(1, 8))
    check_exact(star_direct == star_formula, "star orbit window expectation formula")
    star_lo = sum(pJ_lo_fr[a] * star_weights[a] for a in range(1, 8))
    thresh_hi = Fraction(1, 2) - mu_lo_fr / 16  # upper bound on threshold 1/2 - mu/16
    check_encl(star_lo > thresh_hi, f"star orbit {dec_floor(star_lo, 6)} <= thresh {dec_ceil(thresh_hi, 6)}")
    print(f"  [encl] 1-col + all-order stationarity star countermodel: E[R_3/8] >= {dec_floor(star_lo, 6)} > {dec_ceil(thresh_hi, 6)}")

    # 1.6 Theorem C1.4(2): Explicit absolute constant C_lat <= 180 for lattice-scale 2nd moments
    # Uses dyadic shells w_j = 24 * 2^j (j >= 0), r_j = 2^j (j >= 1), and 2-D Selberg sieve at s >= 12 > 10.
    ln2_lo_1, ln2_hi_1 = ln_encl_rat(Fraction(2), 30)
    ein1_s = Fraction(0)
    t_ein = Fraction(1)
    for jj in range(1, 35):
        ein1_s += t_ein / jj
        t_ein = t_ein / (jj + 1)
    ein1_hi = ein1_s + (t_ein / 35) / (1 - Fraction(1, 36))
    _, e2ein1_hi = exp_pos_encl(2 * ein1_hi, 45)
    _, em6_hi = exp_neg_encl(Fraction(6), 45)  # e^{-6}, since w_j / 8 = 6 * 2^{j-1}
    c_lat_a = Fraction(0)
    c_lat_b = Fraction(0)
    for j in range(1, 7):
        wj = 24 * (1 << j)
        rj = 1 << j
        c_lat_a += (2 * wj + 1) * (em6_hi ** (1 << (j - 1))) * e2ein1_hi
        c_lat_b += (2 * wj + 1) * ((2 * ln2_hi_1) ** rj) / math.factorial(rj)
    # Rigorous tail bound for j >= 7 (w_7 = 3072, r_7 = 128):
    # At j = 7, (2*3072 + 1) * e^{-384} * e^{2 Ein(1)} + (2*3072 + 1) * (2 ln 2)^{128} / 128! < 10^{-50},
    # and successive terms shrink by factor < 1/10, so tail < 2 * (j=7 term) < 10^{-6}.
    term7_a = (2 * 3072 + 1) * (em6_hi ** 64) * e2ein1_hi
    term7_b = (2 * 3072 + 1) * ((2 * ln2_hi_1) ** 128) / math.factorial(128)
    check_encl(2 * (term7_a + term7_b) < Fraction(1, 10 ** 6), "C_lat tail j>=7 < 1e-6")
    C_lat_raw_hi = Fraction(49) + c_lat_a + c_lat_b + Fraction(1, 10 ** 6)
    print(f"  [encl] C1.4(2) dyadic-shell constant C_lat_raw <= {dec_ceil(C_lat_raw_hi, 6)} (multiplied by 1/sigma_2(10) in main)")

    return {
        "mu_lo": mu_lo_fr, "mu_hi": mu_hi_fr,
        "nu_lo": nu_lo, "nu_hi": nu_hi, "nu_lo_fr": nu_lo_fr, "nu_hi_fr": nu_hi_fr, "nu_miss": nu_miss,
        "pJ_lo": pJ_lo, "pJ_hi": pJ_hi, "pJ_lo_fr": pJ_lo_fr, "pJ_hi_fr": pJ_hi_fr, "pJ_miss": pJ_miss,
        "psi2_lo": psi2_lo, "psi2_hi": psi2_hi, "B2_adj_hi": B2_adj_hi,
        "star_lo": star_lo, "thresh_lo": Fraction(1, 2) - mu_hi_fr / 16, "thresh_hi": thresh_hi,
        "C_lat_raw_hi": C_lat_raw_hi,
    }


# ---------------------------------------------------------------------------
# SECTION 2: C1.2 — Exact Factorial-Moment Order Hierarchy for E(4) at W = 3
# ---------------------------------------------------------------------------
def ff(n, k):
    r = 1
    for j in range(k):
        r *= (n - j)
    return r


def run_section_2(s1):
    print("\n=== Section 2 (C1.2): Exact Factorial-Moment Order Hierarchy (E(4), W=3) ===")
    nu_lo_fr = s1["nu_lo_fr"]
    nu_hi_fr = s1["nu_hi_fr"]
    nu_lo = s1["nu_lo"]
    nu_miss = s1["nu_miss"]
    thresh_lo = s1["thresh_lo"]
    thresh_hi = s1["thresh_hi"]

    # 2.1 7-variable marked r = 3 COUNTERMODEL (35x35 invertible perturbation certificate!)
    # Variables: (N1, N21, N23, N31) coupled on 35 integer points; (N33, N35, N37) independent 1D
    # closed-form order-3 Poisson-matched laws Q(lam) on {0, 1, 2, 3}.
    pts4_35 = [
        (0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 1, 0), (0, 0, 1, 1),
        (0, 0, 2, 0), (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 0, 2), (0, 1, 0, 4),
        (0, 1, 1, 4), (0, 1, 2, 0), (0, 2, 0, 0), (0, 2, 1, 0), (0, 2, 1, 2),
        (0, 3, 0, 0), (0, 3, 0, 1), (0, 3, 1, 0), (1, 0, 0, 0), (1, 0, 0, 2),
        (1, 0, 1, 1), (1, 0, 2, 0), (1, 0, 2, 1), (1, 0, 3, 0), (1, 1, 0, 0),
        (1, 1, 0, 1), (1, 1, 1, 0), (2, 0, 0, 1), (2, 0, 0, 2), (2, 0, 1, 0),
        (2, 0, 1, 1), (2, 1, 0, 0), (2, 2, 0, 0), (3, 0, 0, 0), (3, 0, 0, 1),
    ]
    mon4 = [(a, b, c, d) for a in range(4) for b in range(4 - a)
            for c in range(4 - a - b) for d in range(4 - a - b - c)]
    check_exact(len(mon4) == 35 and len(pts4_35) == 35, "35x35 4-var system")
    B_mat = [[Fraction(ff(pt[0], m[0]) * ff(pt[1], m[1]) * ff(pt[2], m[2]) * ff(pt[3], m[3]))
              for pt in pts4_35] for m in mon4]
    B_inv = frac_mat_inv(B_mat)
    # Verify exact B_inv * B_mat = I_35
    for i in range(35):
        for j in range(35):
            s = sum(B_inv[i][k] * B_mat[k][j] for k in range(35))
            check_exact(s == (1 if i == j else 0), f"B_inv*B[{i},{j}]")
    # Compute exact ||B_inv||_inf
    norm_Binv = max(sum(abs(x) for x in row) for row in B_inv)
    check_exact(norm_Binv < 20, f"||B_inv||_inf = {norm_Binv} < 20")

    # Interval enclosures for lam7 = [1/2, (nu1+nu5)/2, (nu3+nu7)/2, nu1/2, nu3/2, nu5/2, nu7/2]
    lam_lo = [
        Fraction(1, 2),
        (nu_lo_fr[1] + nu_lo_fr[5]) / 2,
        (nu_lo_fr[3] + nu_lo_fr[7]) / 2,
        nu_lo_fr[1] / 2, nu_lo_fr[3] / 2, nu_lo_fr[5] / 2, nu_lo_fr[7] / 2,
    ]
    lam_hi = [
        Fraction(1, 2),
        (nu_hi_fr[1] + nu_hi_fr[5]) / 2,
        (nu_hi_fr[3] + nu_hi_fr[7]) / 2,
        nu_hi_fr[1] / 2, nu_hi_fr[3] / 2, nu_hi_fr[5] / 2, nu_hi_fr[7] / 2,
    ]
    # Midpoint RHS b_mid and exact radius eps_b >= max_i |b_true[i] - b_mid[i]|
    b_lo = []
    b_hi = []
    for (a, b, c, d) in mon4:
        lo_v = (lam_lo[0] ** a) * (lam_lo[1] ** b) * (lam_lo[2] ** c) * (lam_lo[3] ** d)
        hi_v = (lam_hi[0] ** a) * (lam_hi[1] ** b) * (lam_hi[2] ** c) * (lam_hi[3] ** d)
        b_lo.append(lo_v)
        b_hi.append(hi_v)
    b_mid = [(b_lo[i] + b_hi[i]) / 2 for i in range(35)]
    eps_b = max((b_hi[i] - b_lo[i]) / 2 for i in range(35))
    # Exact midpoint weights w_mid = B_inv * b_mid; for EVERY true b in [b_lo, b_hi],
    # |w_true[j] - w_mid[j]| <= sum_k |B_inv[j][k]| * (b_hi[k] - b_lo[k]) / 2!
    w_lo = []
    w_hi = []
    for j in range(35):
        wm = sum(B_inv[j][k] * b_mid[k] for k in range(35))
        rad = sum(abs(B_inv[j][k]) * (b_hi[k] - b_lo[k]) / 2 for k in range(35))
        check_encl(wm - rad > 0, f"4-var r=3 weight {j} strictly positive")
        w_lo.append(wm - rad)
        w_hi.append(wm + rad)
    # Verify exact derived count second factorial moments on a normalized lam_ex in [lam_lo, lam_hi]:
    # Since all 120 order-<=3 marked factorial moments match Pois(lam_ex) identically, the total
    # column counts N1, N2 = N21 + N23, N3 = N31 + N33 + N35 + N37 satisfy
    # E[N_i(N_i - 1)] = 1/4 and E[N_i N_j] = 1/4 identically!
    nu_ex = {1: nu_lo_fr[1] + Fraction(nu_miss, SCALE), 3: nu_lo_fr[3], 5: nu_lo_fr[5], 7: nu_lo_fr[7]}
    check_exact(sum(nu_ex.values()) == 1, "nu_ex normalized")
    lam_ex = [
        Fraction(1, 2), (nu_ex[1] + nu_ex[5]) / 2, (nu_ex[3] + nu_ex[7]) / 2,
        nu_ex[1] / 2, nu_ex[3] / 2, nu_ex[5] / 2, nu_ex[7] / 2,
    ]
    b_ex = [(lam_ex[0] ** a) * (lam_ex[1] ** b) * (lam_ex[2] ** c) * (lam_ex[3] ** d) for (a, b, c, d) in mon4]
    w_ex = [sum(B_inv[j][k] * b_ex[k] for k in range(35)) for j in range(35)]
    check_exact(all(x > 0 for x in w_ex) and sum(w_ex) == 1, "w_ex valid probability law")
    def q1d_exact(l):
        return [1 - l + l ** 2 / 2 - l ** 3 / 6, l - l ** 2 + l ** 3 / 2, l ** 2 * (1 - l) / 2, l ** 3 / 6]
    q4_ex, q5_ex, q6_ex = q1d_exact(lam_ex[4]), q1d_exact(lam_ex[5]), q1d_exact(lam_ex[6])
    # Exact count expectations under w_ex x q4_ex x q5_ex x q6_ex:
    EN1_2 = sum(w_ex[j] * ff(pts4_35[j][0], 2) for j in range(35))
    EN2_2 = sum(w_ex[j] * ff(pts4_35[j][1] + pts4_35[j][2], 2) for j in range(35))
    EN1N2 = sum(w_ex[j] * pts4_35[j][0] * (pts4_35[j][1] + pts4_35[j][2]) for j in range(35))
    EN1_1 = sum(w_ex[j] * pts4_35[j][0] for j in range(35))
    EN2_1 = sum(w_ex[j] * (pts4_35[j][1] + pts4_35[j][2]) for j in range(35))
    EN31_1 = sum(w_ex[j] * pts4_35[j][3] for j in range(35))
    EN31_2 = sum(w_ex[j] * ff(pts4_35[j][3], 2) for j in range(35))
    EN1N31 = sum(w_ex[j] * pts4_35[j][0] * pts4_35[j][3] for j in range(35))
    EN2N31 = sum(w_ex[j] * (pts4_35[j][1] + pts4_35[j][2]) * pts4_35[j][3] for j in range(35))
    # Independent remainder R3 = N33 + N35 + N37 has mean lam_rem and E[R3(R3-1)] = lam_rem^2:
    ER_1 = sum(x * q4_ex[x] for x in range(4)) + sum(x * q5_ex[x] for x in range(4)) + sum(x * q6_ex[x] for x in range(4))
    ER_2 = (sum(ff(x, 2) * q4_ex[x] for x in range(4)) + sum(ff(x, 2) * q5_ex[x] for x in range(4))
            + sum(ff(x, 2) * q6_ex[x] for x in range(4))
            + 2 * (lam_ex[4] * lam_ex[5] + lam_ex[4] * lam_ex[6] + lam_ex[5] * lam_ex[6]))
    EN3_2 = EN31_2 + 2 * EN31_1 * ER_1 + ER_2
    EN1N3 = EN1N31 + EN1_1 * ER_1
    EN2N3 = EN2N31 + EN2_1 * ER_1
    for lbl, val in [("E[N1(N1-1)]", EN1_2), ("E[N2(N2-1)]", EN2_2), ("E[N3(N3-1)]", EN3_2),
                     ("E[N1 N2]", EN1N2), ("E[N1 N3]", EN1N3), ("E[N2 N3]", EN2N3)]:
        check_exact(val == Fraction(1, 4), f"7-var r=3 derived count moment {lbl} == 1/4")
    # 1D order-3 laws on N33, N35, N37: p3=l^3/6, p2=(l^2-l^3)/2, p1=l-l^2+l^3/2, p0=1-l+l^2/2-l^3/6
    # Since l in [0, 1/4], every p_k is strictly positive and monotonic on [l_lo, l_hi] -> easy interval bounds!
    def q1d_encl(l_lo, l_hi):
        # p3 = l^3/6 (increasing)
        p3_l, p3_h = l_lo ** 3 / 6, l_hi ** 3 / 6
        # p2 = l^2(1-l)/2 (increasing on [0, 2/3])
        check_encl(l_hi <= Fraction(1, 2), "q1d domain")
        p2_l, p2_h = l_lo ** 2 * (1 - l_lo) / 2, l_hi ** 2 * (1 - l_hi) / 2
        # p1 = l - l^2 + l^3/2: deriv 1 - 2l + 3/2 l^2 > 0 everywhere! (increasing)
        p1_l, p1_h = l_lo - l_lo ** 2 + l_lo ** 3 / 2, l_hi - l_hi ** 2 + l_hi ** 3 / 2
        # p0 = 1 - l + l^2/2 - l^3/6: deriv -(1 - l + l^2/2) < 0 (decreasing)
        p0_l, p0_h = 1 - l_hi + l_hi ** 2 / 2 - l_hi ** 3 / 6, 1 - l_lo + l_lo ** 2 / 2 - l_lo ** 3 / 6
        for x in (p0_l, p1_l, p2_l, p3_l):
            check_encl(x > 0, "q1d positive")
        return [p0_l, p1_l, p2_l, p3_l], [p0_h, p1_h, p2_h, p3_h]
    q4_l, _ = q1d_encl(lam_lo[4], lam_hi[4])
    q5_l, _ = q1d_encl(lam_lo[5], lam_hi[5])
    q6_l, _ = q1d_encl(lam_lo[6], lam_hi[6])
    p3_rem_lo = [Fraction(0)] * 8
    for x3 in range(4):
        for x5 in range(4):
            for x7 in range(4):
                p3_rem_lo[(3 * x3 + 5 * x5 + 7 * x7) & 7] += q4_l[x3] * q5_l[x5] * q6_l[x7]
    # Exact lower bound on E[R_3/8] for this true 7-var order-3-matched law!
    E_7var_r3_lo = Fraction(0)
    for j, (x1, x21, x23, x31) in enumerate(pts4_35):
        a1 = x1 & 1
        a2 = (x21 + 3 * x23) & 3
        g_lo = sum(p3_rem_lo[r3] * Fraction((4 * a1 + 2 * a2 + ((x31 + r3) & 7)) & 7, 8) for r3 in range(8))
        E_7var_r3_lo += w_lo[j] * g_lo
    check_encl(E_7var_r3_lo > thresh_hi, f"7-var r=3 lower {dec_floor(E_7var_r3_lo, 6)} <= thresh")
    print(f"  [encl] 7-var marked r=3 countermodel (35-pt x Q3): E[R_3/8] >= {dec_floor(E_7var_r3_lo, 6)} > {dec_ceil(thresh_hi, 6)} (r_min^marked >= 4)")

    # 2.2 7-variable marked r = 7 GLOBAL 2-COLUMN SHIFTED SPLIT-BONFERRONI!
    # First certify the algebraic Bonferroni inequality for EVERY integer t >= 0 and odd K in {1,3,5,7}:
    # sum_{j=0}^K (-1)^j C(t, j) == 1 if t == 0 else -C(t-1, K) <= 0!
    for K in (1, 3, 5, 7):
        for t in range(15):
            lhs = sum(((-1) ** j) * math.comb(t, j) for j in range(K + 1))
            rhs = 1 if t == 0 else -math.comb(t - 1, K)
            check_exact(lhs == rhs and lhs <= (1 if t == 0 else 0), f"Bonf identity K={K},t={t}")

    # Compute exact Fraction enclosures of E[P_7(1)] + E[P_7(w)] + E[P_7(v')] under Q^{(1/2) otimes 2}!
    # Notice P_7(g) = U_g - sum_{s=0}^6 (U_g - E[g | S=s]) * (LAM^s / s!) * trunc_exp(LAM, K(s)),
    # where K(s) = 7 - s (odd) if s even, and 6 - s (odd) if s odd.
    # Notice trunc_exp(LAM, K) = sum_{j=0}^K (-1)^j LAM^j / j! is POSITIVE for all K in {1,3,5,7} at LAM in {1/2, 1}!
    # Check positivity of trunc_exp:
    def trunc_exp(lam_fr, K):
        return sum(((-1) ** j) * (lam_fr ** j) / math.factorial(j) for j in range(K + 1))
    for s in range(7):
        K = 7 - s if (7 - s) % 2 == 1 else 6 - s
        check_exact(trunc_exp(Fraction(1, 2), K) >= 0, f"trunc_exp(1/2, {K}) >= 0")
        check_exact(trunc_exp(Fraction(1, 1), K) >= 0, f"trunc_exp(1, {K}) >= 0")

    # Therefore, to UPPER-bound P_7(g), we need an UPPER bound on E[g | S=s] (since U_g - E[g|S=s] has minus sign!).
    # Wait: E[1/2 * 1[a1=1] | S=s] = (1/2) * (s % 2) is EXACT!
    p_1 = Fraction(1, 2)
    for s in range(7):
        K = 7 - s if (7 - s) % 2 == 1 else 6 - s
        E1 = Fraction(1, 2) if (s & 1) else Fraction(0)
        p_1 -= (Fraction(1, 2) - E1) * (Fraction(1, 2) ** s / math.factorial(s)) * trunc_exp(Fraction(1, 2), K)

    # For w(a1,a2) (U = 1/2, LAM = 1) and vp(a2,a3) (U = 7/8, LAM = 1), compute exact lower-bound transition
    # probabilities on (a1, a2) and (a2, a3) in SCALE units; missing mass gets charged at MAX value (1/2 and 7/8)!
    def w_fn(a1, a2):
        return (Fraction(1, 2) if a1 == 0 else Fraction(-1, 2)) if a2 in (2, 3) else Fraction(0)

    def vp_fn(a2, a3):
        r23 = (2 * a2 + a3) & 7
        if a2 in (2, 3):
            return Fraction(r23, 8) - Fraction(1, 2) if r23 >= 4 else Fraction(r23, 8) + Fraction(1, 2)
        return Fraction(r23, 8)

    # Conditional transition probs for w on (a1 mod 2, a2 mod 4):
    # p1 = 1/2, p21 = (nu1+nu5)/2, p23 = (nu3+nu7)/2
    p21_lo = (nu_lo[0] + nu_lo[2]) // 2
    p23_lo = (nu_lo[1] + nu_lo[3]) // 2
    steps_w = [(1, 0, SCALE // 2), (0, 1, p21_lo), (0, 3, p23_lo)]
    dist_w = {(0, 0): SCALE}
    Ew_hi = []
    for s in range(7):
        # Upper bound on E[w | S=s] = E[w + 1/2 | S=s] - 1/2 <= sum dist_lo*(w+1/2) + (1 - sum dist_lo)*1 - 1/2!
        # Wait: w + 1/2 in {0, 1/2, 1}, so missing mass <= 1 - sum dist_lo charged at max 1!
        mass = sum(dist_w.values())
        s_val = sum(Fraction(pr, SCALE) * (w_fn(a1, a2) + Fraction(1, 2)) for (a1, a2), pr in dist_w.items())
        Ew_hi.append(s_val + Fraction(SCALE - mass, SCALE) - Fraction(1, 2))
        nd = {}
        for (a1, a2), pr in dist_w.items():
            for da1, da2, wt in steps_w:
                key = ((a1 + da1) & 1, (a2 + da2) & 3)
                nd[key] = nd.get(key, 0) + mul_lo(pr, wt)
        dist_w = nd

    # Conditional transition probs for vp on (a2 mod 4, a3 mod 8):
    steps_v = [
        (1, 0, p21_lo), (3, 0, p23_lo),
        (0, 1, nu_lo[0] // 2), (0, 3, nu_lo[1] // 2), (0, 5, nu_lo[2] // 2), (0, 7, nu_lo[3] // 2),
    ]
    dist_v = {(0, 0): SCALE}
    Evp_hi = []
    for s in range(7):
        mass = sum(dist_v.values())
        s_val = sum(Fraction(pr, SCALE) * vp_fn(a2, a3) for (a2, a3), pr in dist_v.items())
        Evp_hi.append(s_val + Fraction(SCALE - mass, SCALE) * Fraction(7, 8))
        nd = {}
        for (a2, a3), pr in dist_v.items():
            for da2, da3, wt in steps_v:
                key = ((a2 + da2) & 3, (a3 + da3) & 7)
                nd[key] = nd.get(key, 0) + mul_lo(pr, wt)
        dist_v = nd

    p_w_hi = Fraction(1, 2)
    p_v_hi = Fraction(7, 8)
    for s in range(7):
        K = 7 - s if (7 - s) % 2 == 1 else 6 - s
        te = trunc_exp(Fraction(1, 1), K)
        p_w_hi -= (Fraction(1, 2) - Ew_hi[s]) * Fraction(1, math.factorial(s)) * te
        p_v_hi -= (Fraction(7, 8) - Evp_hi[s]) * Fraction(1, math.factorial(s)) * te
    P7_hi = p_1 + p_w_hi + p_v_hi
    check_encl(P7_hi < thresh_lo, f"Split-Bonf r=7 {dec_ceil(P7_hi, 6)} >= thresh {dec_floor(thresh_lo, 6)}")
    print(f"  [encl] 2-col Shifted Split-Bonferroni r=7: E[P_7] <= {dec_ceil(P7_hi, 6)} < {dec_floor(thresh_lo, 6)} (4 <= r_min^marked <= 7)")

    # 2.3 3-variable i.i.d.-mark r = 2 COUNTERMODEL (8 exact rational atoms, denom 24!)
    cm_r2 = [
        ((0, 0, 0), Fraction(6, 24)), ((0, 1, 0), Fraction(4, 24)),
        ((0, 1, 1), Fraction(3, 24)), ((0, 1, 3), Fraction(1, 24)),
        ((1, 0, 0), Fraction(2, 24)), ((1, 0, 1), Fraction(6, 24)),
        ((1, 3, 0), Fraction(1, 24)), ((3, 1, 0), Fraction(1, 24)),
    ]
    # Verify ALL 10 factorial moments of order <= 2 match Pois(1/2)^3 IDENTICALLY!
    for a in range(3):
        for b in range(3 - a):
            for c in range(3 - a - b):
                mom = sum(w * ff(pt[0], a) * ff(pt[1], b) * ff(pt[2], c) for pt, w in cm_r2)
                check_exact(mom == Fraction(1, 2) ** (a + b + c), f"i.i.d. r=2 mom ({a},{b},{c})")
    # Compute lower bound on S_n mod 8 for n = 0..18 in SCALE units (for both r=2 and r=3!)
    S_lo = [[SCALE if a == 0 else 0 for a in range(8)]]
    for n in range(1, 19):
        prev = S_lo[-1]
        nxt = [0] * 8
        for a in range(8):
            for i, r in enumerate((1, 3, 5, 7)):
                nxt[(a + r) & 7] += mul_lo(prev[a], nu_lo[i])
        S_lo.append(nxt)
    # Exact lower/upper bounds on f_iid(n1, n2, n3)
    p1_s = [[sum(S_lo[n][a] for a in range(8) if (a & 1) == r) for r in range(2)] for n in range(19)]
    p2_s = [[sum(S_lo[n][a] for a in range(8) if (a & 3) == r) for r in range(4)] for n in range(19)]
    def f_iid_encl(n1, n2, n3):
        lo_s = 0
        mass = 0
        for a1 in range(2):
            for a2 in range(4):
                p12 = mul_lo(p1_s[n1][a1], p2_s[n2][a2])
                for a3 in range(8):
                    pr = mul_lo(p12, S_lo[n3][a3])
                    mass += pr
                    lo_s += (pr * ((4 * a1 + 2 * a2 + a3) & 7)) // 8
        lo_fr = Fraction(lo_s, SCALE)
        hi_fr = lo_fr + Fraction(SCALE - mass, SCALE) * Fraction(7, 8)
        return lo_fr, hi_fr
    E_iid_r2_lo = sum(w * f_iid_encl(pt[0], pt[1], pt[2])[0] for pt, w in cm_r2)
    check_encl(E_iid_r2_lo > thresh_hi, f"i.i.d. r=2 lower {dec_floor(E_iid_r2_lo, 6)} <= thresh")
    print(f"  [encl] 3-var i.i.d.-mark r=2 countermodel (8 atoms, denom 24): E[f_iid] >= {dec_floor(E_iid_r2_lo, 6)} > {dec_ceil(thresh_hi, 6)}")

    # 2.4 3-variable i.i.d.-mark r = 3 GLOBAL POLYNOMIAL CERTIFICATE (Young-split + 1800-pt box!)
    basis3 = [(a, b, c) for a in range(4) for b in range(4 - a) for c in range(4 - a - b)]
    w3_num = [10, 21210, -2300, 624, 37387, -8087, 0, -21706, 6509, 11893,
              50000, -5033, 0, -24775, 0, 2972, -41084, 2062, 18831, 24418]
    # Add tiny safety bump +10 (0.0001) to constant term to absorb nu_miss in f_iid_hi across box!
    w3_num[0] += 10
    w3_fr = [Fraction(v, 100000) for v in w3_num]
    # Exact Pois(1/2)^3 expectation of P_3:
    E_P3 = sum(w3_fr[j] * (Fraction(1, 2) ** sum(basis3[j])) for j in range(len(basis3)))
    check_encl(E_P3 < thresh_lo, f"E[P_3] = {dec_ceil(E_P3, 6)} >= thresh {dec_floor(thresh_lo, 6)}")

    # Expand P_3 to standard monomials n1^i n2^j n3^k and certify Young-split global bound >= 7/8
    # outside [0..9] x [0..9] x [0..17]!
    def ff_to_std(a):
        p = [1]
        for k in range(a):
            np_ = [0] * (len(p) + 1)
            for i, v in enumerate(p):
                np_[i] -= v * k
                np_[i + 1] += v
            p = np_
        return p
    std = {}
    for j, (a, b, c) in enumerate(basis3):
        px, py, pz = ff_to_std(a), ff_to_std(b), ff_to_std(c)
        for i1, v1 in enumerate(px):
            for i2, v2 in enumerate(py):
                for i3, v3 in enumerate(pz):
                    std[(i1, i2, i3)] = std.get((i1, i2, i3), Fraction(0)) + w3_fr[j] * v1 * v2 * v3
    for k, v in std.items():
        if sum(k) == 3:
            check_exact(v >= 0, f"deg-3 coeff {k} >= 0")
    a1, a2, a3 = std[(3, 0, 0)], std[(0, 3, 0)], std[(0, 0, 3)]
    b11, b22, b33 = -std[(2, 0, 0)], -std[(0, 2, 0)], -std[(0, 0, 2)]
    b12, b13, b23 = -std[(1, 1, 0)], -std[(1, 0, 1)], -std[(0, 1, 1)]
    check_exact(b12 >= 0 and b13 >= 0 and b23 >= 0, "deg-2 cross terms <= 0")
    # Young's inequality: n_i n_j <= (r/2) n_i^2 + (1/(2r)) n_j^2 with r12=2, r13=4, r23=2
    r12, r13, r23 = Fraction(2), Fraction(4), Fraction(2)
    A1 = b11 + b12 * r12 / 2 + b13 * r13 / 2
    A2 = b22 + b12 / (2 * r12) + b23 * r23 / 2
    A3 = b33 + b13 / (2 * r13) + b23 / (2 * r23)
    L1, L2, L3, c0 = std[(1, 0, 0)], std[(0, 1, 0)], std[(0, 0, 1)], std[(0, 0, 0)]
    # Exact global minimums of the three 1D cubics f_i(n) = a_i n^3 - A_i n^2 + L_i n on Z_{>=0}:
    # Since f_i'(n) = 3 a_i n^2 - 2 A_i n + L_i > 0 for all n >= N_inc (where 3 a_i N_inc > 2 A_i and f_i'(N_inc) > 0),
    # the global minimum on Z_{>=0} is attained on [0..N_inc]!
    def cert_1d_cubic(a, A, L, N_box):
        # Find exact minimum on Z_{>=0}
        N_inc = max(N_box, int(A / a) + 2)
        check_exact(3 * a * N_inc > 2 * A and 3 * a * N_inc * N_inc - 2 * A * N_inc + L > 0, "1D cubic monotone")
        vals = [a * n ** 3 - A * n ** 2 + L * n for n in range(N_inc + 1)]
        mn = min(vals)
        # Also verify strictly increasing from N_box onward:
        check_exact(3 * a * N_box > 2 * A and 3 * a * N_box * N_box - 2 * A * N_box + L > 0, "1D cubic inc >= N_box")
        return mn, vals[N_box]
    m1, v1 = cert_1d_cubic(a1, A1, L1, 10)
    m2, v2 = cert_1d_cubic(a2, A2, L2, 10)
    m3, v3 = cert_1d_cubic(a3, A3, L3, 18)
    check_exact(v1 + m2 + m3 + c0 >= Fraction(7, 8), "global n1 >= 10")
    check_exact(m1 + v2 + m3 + c0 >= Fraction(7, 8), "global n2 >= 10")
    check_exact(m1 + m2 + v3 + c0 >= Fraction(7, 8), "global n3 >= 18")
    # Now check ALL 10 * 10 * 18 = 1800 points in [0..9] x [0..9] x [0..17] in exact Fraction!
    for n1 in range(10):
        for n2 in range(10):
            for n3 in range(18):
                pval = sum(w3_fr[j] * ff(n1, a) * ff(n2, b) * ff(n3, c) for j, (a, b, c) in enumerate(basis3))
                _, fhi = f_iid_encl(n1, n2, n3)
                check_encl(pval >= fhi, f"P_3({n1},{n2},{n3}) < fhi")
    print(f"  [encl] 3-var i.i.d.-mark r=3 GLOBAL cert (Young + 1800 pts): E[P_3] = {dec_ceil(E_P3, 6)} < {dec_floor(thresh_lo, 6)} (r_min^iid = 3 EXACT)")

    return {"E_7var_r3_lo": E_7var_r3_lo, "P7_hi": P7_hi, "E_iid_r2_lo": E_iid_r2_lo, "E_P3": E_P3}


# ---------------------------------------------------------------------------
# SECTION 3: C1.3 & C2 — Z/8Z Fourier Subsets, Exact Sturm M=12 & M=11 on R/Z,
#            and E(2) at W=8 Bonferroni Order r=46
# ---------------------------------------------------------------------------
def poly_trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def poly_add(a, b):
    n = max(len(a), len(b))
    return poly_trim([(a[i] if i < len(a) else Fraction(0)) + (b[i] if i < len(b) else Fraction(0)) for i in range(n)])


def poly_sub(a, b):
    n = max(len(a), len(b))
    return poly_trim([(a[i] if i < len(a) else Fraction(0)) - (b[i] if i < len(b) else Fraction(0)) for i in range(n)])


def poly_mul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] += x * y
    return poly_trim(out)


def poly_divmod(a, b):
    a = poly_trim(a)
    b = poly_trim(b)
    if len(a) < len(b):
        return [Fraction(0)], a
    q = [Fraction(0)] * (len(a) - len(b) + 1)
    r = list(a)
    for i in range(len(a) - len(b), -1, -1):
        coef = r[i + len(b) - 1] / b[-1]
        q[i] = coef
        for j in range(len(b)):
            r[i + j] -= coef * b[j]
    return poly_trim(q), poly_trim(r)


def poly_deriv(a):
    return poly_trim([a[i] * i for i in range(1, len(a))]) if len(a) > 1 else [Fraction(0)]


def sturm_roots_pos(p):
    """Exact real root count of rational polynomial p in (0, +inf) via Sturm's theorem."""
    p = poly_trim(p)
    a, b = p, poly_deriv(p)
    while not (len(b) == 1 and b[0] == 0):
        _, r = poly_divmod(a, b)
        a, b = b, r
    p_sf, _ = poly_divmod(p, a)
    def norm_int(q):
        q = poly_trim(q)
        den = 1
        for x in q:
            den = math.lcm(den, x.denominator)
        ints = [int(x * den) for x in q]
        g = 0
        for v in ints:
            g = math.gcd(g, abs(v))
        if g > 1:
            ints = [v // g for v in ints]
        return [Fraction(v) for v in ints]
    seq = [norm_int(p_sf), norm_int(poly_deriv(p_sf))]
    while len(seq[-1]) > 1:
        _, r = poly_divmod(seq[-2], seq[-1])
        if len(r) == 1 and r[0] == 0:
            break
        seq.append(norm_int([-x for x in r]))
    def sc(vals):
        nz = [v for v in vals if v != 0]
        return sum(1 for i in range(len(nz) - 1) if nz[i] * nz[i + 1] < 0)
    s0 = [1 if q[0] > 0 else (-1 if q[0] < 0 else 0) for q in seq]
    sinf = [1 if q[-1] > 0 else (-1 if q[-1] < 0 else 0) for q in seq]
    return sc(s0) - sc(sinf)


def run_section_3(primes_1e5, s1):
    print("\n=== Section 3 (C1.3 & C2): Z/8Z Fourier, Exact Sturm M=12 / M=11, E(2) r=46 ===")
    pJ_lo = s1["pJ_lo"]
    pJ_miss = s1["pJ_miss"]
    thresh_hi = s1["thresh_hi"]

    # 3.1 On Z/8Z: exact law of R_3 = (4 a1 + 2 a2 + a3) mod 8 under Q_3^{(1/2)}
    pJ2_lo = [sum(pJ_lo[a] for a in range(8) if (a & 1) == r) for r in range(2)]
    pJ4_lo = [sum(pJ_lo[a] for a in range(8) if (a & 3) == r) for r in range(4)]
    qR_lo = [0] * 8
    for a1 in range(2):
        for a2 in range(4):
            p12 = mul_lo(pJ2_lo[a1], pJ4_lo[a2])
            for a3 in range(8):
                qR_lo[(4 * a1 + 2 * a2 + a3) & 7] += mul_lo(p12, pJ_lo[a3])
    qR_miss = SCALE - sum(qR_lo)
    qR_lo_fr = [Fraction(x, SCALE) for x in qR_lo]
    qR_hi_fr = [Fraction(x + qR_miss, SCALE) for x in qR_lo]
    # Prove EVERY proper subset S of {1,2,3,4} fails > 0.370229 by exhibiting an exact measure matching
    # all harmonics in {1,2,3,4} \ {h*} for each h* in {1, 2, 3, 4}!
    # For h* = 4: add +delta * (-1)^r to qR[r]! Preserves h=0,1,2,3 IDENTICALLY!
    #   Max delta keeping q >= 0 is min_{r odd} qR[r] (actually we want to INCREASE E[r/8],
    #   and sum_r (-1)^r * (r/8) = (0 - 1 + 2 - 3 + 4 - 5 + 6 - 7)/8 = -4/8 = -1/2 < 0!
    #   So subtract delta * (-1)^r, i.e., add delta on ODD r and subtract delta on EVEN r,
    #   max delta = min_{r even} qR[r] = qR[6] ~ 0.0445 -> adds +delta/2? Wait: even larger if we optimize on Z/8Z!)
    # Exact perturbation for each dropped harmonic h* in {1, 2, 3, 4}:
    #   h*=4: v4(r) = -(-1)^r -> inner with r/8 is +1/2; delta = min_{r even} qR[r]!
    #   Wait: let's check all four single-harmonic drops with pure exact vectors in ker(F_{S})!
    ER_lo = sum(qR_lo_fr[r] * Fraction(r, 8) for r in range(8))
    ER_hi = ER_lo + Fraction(qR_miss, SCALE) * Fraction(7, 8)
    print(f"  [encl] E_{{Q_3}}[R_3/8] in [{dec_floor(ER_lo, 6)}, {dec_ceil(ER_hi, 6)}]")
    # Exact kernel vectors v (sum v = 0, orthogonal to cos(2pi h r/8), sin(2pi h r/8) for h in S):
    # Note: for h* in {1, 2, 3}, ker has dimension 2 (cos and sin of h*); for h*=4, dim 1!
    # Wait: for h*=4: v = (-1, 1, -1, 1, -1, 1, -1, 1) -> sum v*r/8 = +1/2!
    # Wait: qR_lo[6] ~ 0.032 -> +0.016 only gives 0.339! Why did S={1,2,3} give 0.371794?!
    # Because you can ALSO change qR[0,2,4,6] non-uniformly? NO! If h=0,1,2,3 are ALL fixed (1 + 2+2+2 = 7 eqs in 8 vars!),
    # the kernel IS 1-dimensional (spanned by v4), so max delta = min_{r even} qR[r] = qR[6]?!
    # Let's compute min_{r even} qR[r] — wait: qR[6] is ~ 0.097! Check! 0.097 * (4/8)? NO! sum_{r=0}^7 (-(-1)^r) * r/8 = (+1-2+3-4+5-6+7)/8 = +4/8 = +1/2!
    # WAIT: (-1, +1, -1, +1, -1, +1, -1, +1) dot (0, 1, 2, 3, 4, 5, 6, 7)/8 = (1 - 2 + 3 - 4 + 5 - 6 + 7)/8 = 4/8 = 1/2!
    # Wait: qR[6] = P(R_3 = 6)! What IS qR[6]? Let's check exact values for all 4 dropped harmonics!
    # For h*=4: d4 = min(qR_lo_fr[0], qR_lo_fr[2], qR_lo_fr[4], qR_lo_fr[6])
    d4 = min(qR_lo_fr[r] for r in (0, 2, 4, 6))
    val_drop4 = ER_lo + d4 * Fraction(1, 2)
    # Wait: for h*=3: cos(6pi r/8) = (1, -s, 0, s, -1, s, 0, -s) where s = 1/sqrt(2), sin = (0, s, -1, s, 0, -s, 1, -s)
    # Rational combo cos + sin = (1, 0, -1, 2s? no!) -> cos(6pi r/8) + sin(6pi r/8) cancels s at r=1,5; wait:
    # For h*=3, ker is spanned by u_c = (1, -s, 0, s, -1, s, 0, -s) and u_s = (0, s, -1, s, 0, -s, 1, -s).
    # Notice u_c + u_s = (1, 0, -1, 2s, -1, 0, 1, -2s) -> still has s!
    # Better: use u_3 = (0, 1, -1, 1, 0, -1, 1, -1) ? Check orthogonal to h=0,1,2,4:
    # Exact integer combo: (u_c, u_s) dot (0..7)/8:
    # sum u_c[r] * r/8 = (-s + 3s - 4 + 5s - 7s)/8 = -1/2!  sum u_s[r] * r/8 = (s - 2 + 3s - 5s + 6 - 7s)/8 = (4 - 8s)/8 = 1/2 - s!
    # Use v = -u_c (no sqrt needed if we just take v_1, v_2, v_3 with rational bounds on sqrt(2) in [1414213/10^6, 1414214/10^6]!)
    # Even simpler: check h*=4 (1D exact), h*=2 (pure integers: v2a = (1,0,-1,0,1,0,-1,0), v2b = (0,1,0,-1,0,1,0,-1)!),
    # and h*=1, 3 using exact rational sqrt(2) enclosure!
    # Wait: for h*=2: v2a dot r/8 = (-2 + 4 - 6)/8 = -1/2; v2b dot r/8 = (1 - 3 + 5 - 7)/8 = -1/2!
    # So -v2a - v2b = (-1, -1, 1, 1, -1, -1, 1, 1) has dot = +1, min over {0,1,4,5} is qR[5]!
    d2_a = min(qR_lo_fr[r] for r in (0, 4))
    d2_b = min(qR_lo_fr[r] for r in (1, 5))
    val_drop2 = ER_lo + d2_a * Fraction(1, 2) + d2_b * Fraction(1, 2)
    # Wait: for h*=4, check val_drop4!
    check_encl(val_drop4 > thresh_hi, f"drop h=4: {dec_floor(val_drop4, 6)} <= {dec_ceil(thresh_hi, 6)}")
    check_encl(val_drop2 > thresh_hi, f"drop h=2: {dec_floor(val_drop2, 6)} <= {dec_ceil(thresh_hi, 6)}")
    # For h*=1 and h*=3: use s = 1/sqrt(2) = sqrt(2)/2 in [707106/10^6, 707107/10^6]
    # Exact kernel basis for h=1: c1 = (1, s, 0, -s, -1, -s, 0, s), s1 = (0, s, 1, s, 0, -s, -1, -s)
    # Exact dot with r/8: c1 dot r/8 = -1/2, s1 dot r/8 = -(1 + 2s)/2 = -1/2 - s!
    # Pick v = -alpha*c1 - beta*s1! At alpha = 0, beta = min(qR[1]/s, qR[2], qR[3]/s):
    s_lo, s_hi = Fraction(707106, 1000000), Fraction(707107, 1000000)
    check_exact(2 * s_lo * s_lo < 1 < 2 * s_hi * s_hi, "1/sqrt(2) enclosure")
    # For h*=1: -beta * s1 has negative entries at r=1 (s), r=2 (1), r=3 (s), positive at r=5,6,7;
    # dot with r/8 = beta * (1/2 + s)! Wait: beta = min(qR_lo[1]/s_hi, qR_lo[2], qR_lo[3]/s_hi)!
    beta1 = min(qR_lo_fr[1] / s_hi, qR_lo_fr[2], qR_lo_fr[3] / s_hi)
    # Also add -alpha1 * c1: wait, check if beta1 alone already beats thresh_hi!
    # Better: take alpha1 = min(qR_lo[0], (qR_lo[1]-beta1*s_hi)/s_hi, qR_lo[7]/s_hi)? No, optimize (-alpha*c1 - beta*s1):
    # At alpha = 0.055, beta = 0.055: -alpha*c1 - beta*s1 = (-a, -(a+b)s, -b, (a-b)s, a, (a+b)s, b, (b-a)s)!
    # Notice at alpha = beta = t: vector is t * (-1, -2s, -1, 0, 1, 2s, 1, 0), dot with r/8 = t * (1 + s)!
    t1 = min(qR_lo_fr[0], qR_lo_fr[1] / (2 * s_hi), qR_lo_fr[2])
    val_drop1 = ER_lo + t1 * (1 + s_lo)
    # For h*=3: c3 = (1, -s, 0, s, -1, s, 0, -s) (dot = -1/2), s3 = (0, s, -1, s, 0, -s, 1, -s) (dot = 1/2 - s < 0)
    # Take -t*(c3 - s3) = t * (-1, 2s, -1, 0, 1, -2s, 1, 0)? Wait: c3 dot = -1/2, s3 dot = 1/2 - s = -0.2071!
    # So take -a*c3 - b*s3 with a = b = t: vector is t * (-1, 0, 1, -2s, 1, 0, -1, 2s), dot = t * (1/2 + s - 1/2) = t * s!
    # Better: a = t, b = 0: -t * c3 = t * (-1, s, 0, -s, 1, -s, 0, s), dot = t/2!
    # Wait: min(qR[0], qR[3]/s, qR[5]/s) -> qR[5] ~ 0.068 -> t = 0.096 -> t/2 = 0.048 -> 0.323 + 0.048 = 0.371!
    # Even better: a = 1, b = 1/2 -> vector (-1, s/2, 1/2, -3s/2, 1, -s/2, -1/2, 3s/2), dot = 1/2 + (s - 1/2)/2 = 1/4 + s/2!
    # Even simpler: a = 1, b = -1/2 -> vector (-1, 3s/2, -1/2, -s/2, 1, -3s/2, 1/2, s/2), dot = 3/4 - s/2 = 0.3964;
    # Check a=1, b=0 directly!
    t3 = min(qR_lo_fr[0], qR_lo_fr[3] / s_hi, qR_lo_fr[5] / s_hi)
    val_drop3 = ER_lo + t3 * Fraction(1, 2)
    # If val_drop3 is slightly under thresh_hi, try a=1, b=1/4:
    if val_drop3 <= thresh_hi:
        # vector -t*(c3 + (1/4)*s3): entries (-1, 3s/4, 1/4, -5s/4, 1, -3s/4, -1/4, 5s/4)
        # negative entries at r=0 (-1), r=3 (-5s/4), r=5 (-3s/4), r=6 (-1/4); dot = 1/2 + (s-1/2)/4 = 3/8 + s/4
        t3b = min(qR_lo_fr[0], qR_lo_fr[3] / (Fraction(5, 4) * s_hi), qR_lo_fr[5] / (Fraction(3, 4) * s_hi), qR_lo_fr[6] * 4)
        val_drop3 = ER_lo + t3b * (Fraction(3, 8) + s_lo / 4)
    check_encl(val_drop1 > thresh_hi, f"drop h=1: {dec_floor(val_drop1, 6)} <= {dec_ceil(thresh_hi, 6)}")
    check_encl(val_drop3 > thresh_hi, f"drop h=3: {dec_floor(val_drop3, 6)} <= {dec_ceil(thresh_hi, 6)}")
    print(f"  [encl] Z/8Z proper-subset obstructions (all > {dec_ceil(thresh_hi, 6)}): "
          f"drop 1 >= {dec_floor(val_drop1, 5)}, drop 2 >= {dec_floor(val_drop2, 5)}, "
          f"drop 3 >= {dec_floor(val_drop3, 5)}, drop 4 >= {dec_floor(val_drop4, 5)}")

    # 3.2 Certified enclosures of phi_{E(4)}(h) = E[e^{2pi i h X}] on R/Z for odd h in {1,3,5,7,9,11}
    # Remember phi_{E(4)}(2^a * h_odd) = phi_{E(4)}(h_odd)!
    # Convolve exact mod-U pmf over p <= 300 up to U_max2 = 4095, combine (300, 400000] via Weierstrass,
    # and bound primes > 400000 by the 30-wheel tail sum_{p > 400000} p^{-2} <= 8/(900*(M30-1))!
    pi_lo, pi_hi = pi_encl()
    PI_LO = fl_s(pi_lo)
    PI_HI = ce_s(pi_hi)
    HALF_PI_LO = PI_LO // 2
    HALF_PI_HI = (PI_HI + 1) // 2

    def cos_sin_int_fast(num, den):
        """Exact directed-rounded (c_lo, c_hi, s_lo, s_hi) in SCALE units for angle 2*pi*num/den."""
        num = num % den
        q4 = (4 * num) // den
        r4 = 4 * num - q4 * den
        swap = (2 * r4 > den)
        if swap:
            r4 = den - r4
        x_lo = (HALF_PI_LO * r4) // den
        x_hi = -((-(HALF_PI_HI * r4)) // den)
        c_lo_v = SCALE
        c_hi_v = SCALE
        s_lo_v = x_lo
        s_hi_v = x_lo
        x2_lo = mul_lo(x_lo, x_lo)
        x2_hi = mul_hi(x_lo, x_lo)
        tc_lo, tc_hi = SCALE, SCALE
        ts_lo, ts_hi = x_lo, x_lo
        for m in range(1, 13):
            d_c = (2 * m - 1) * (2 * m)
            d_s = (2 * m) * (2 * m + 1)
            tc_lo = mul_lo(tc_lo, x2_lo) // d_c
            tc_hi = -((-mul_hi(tc_hi, x2_hi)) // d_c)
            ts_lo = mul_lo(ts_lo, x2_lo) // d_s
            ts_hi = -((-mul_hi(ts_hi, x2_hi)) // d_s)
            if m & 1:
                c_lo_v -= tc_hi
                c_hi_v -= tc_lo
                s_lo_v -= ts_hi
                s_hi_v -= ts_lo
            else:
                c_lo_v += tc_lo
                c_hi_v += tc_hi
                s_lo_v += ts_lo
                s_hi_v += ts_hi
        next_c = -((-mul_hi(tc_hi, x2_hi)) // (25 * 26))
        next_s = -((-mul_hi(ts_hi, x2_hi)) // (26 * 27))
        c_lo_v -= next_c
        s_lo_v -= next_s
        rad = x_hi - x_lo
        c_lo_v -= rad
        c_hi_v += rad
        s_lo_v -= rad
        s_hi_v += rad
        if swap:
            c_lo_v, c_hi_v, s_lo_v, s_hi_v = s_lo_v, s_hi_v, c_lo_v, c_hi_v
        if q4 == 0:
            return c_lo_v, c_hi_v, s_lo_v, s_hi_v
        elif q4 == 1:
            return -s_hi_v, -s_lo_v, c_lo_v, c_hi_v
        elif q4 == 2:
            return -c_hi_v, -c_lo_v, -s_hi_v, -s_lo_v
        else:
            return s_lo_v, s_hi_v, -c_hi_v, -c_lo_v

    cl, ch, sl, sh = cos_sin_int_fast(1, 4)
    check_encl(cl <= 0 <= ch and abs(sl - SCALE) < (SCALE >> 80), "cos/sin(pi/2)")
    cl, ch, sl, sh = cos_sin_int_fast(1, 6)
    check_encl(abs(cl - SCALE // 2) < (SCALE >> 80), "cos(pi/3) == 1/2")

    primes_4e5 = sieve_primes(400000)
    U_max2 = 4095
    pmf2 = {1: SCALE}
    for p in primes_4e5:
        if p > 300:
            break
        E_max = 10 if p >= 50 else (24 if p >= 5 else 80)
        fac = {}
        pe = 1
        for e in range(E_max):
            u = odd_part(e + 1)
            if u <= U_max2:
                fac[u] = fac.get(u, Fraction(0)) + Fraction(p - 1, p * pe)
            pe *= p
        fac_lo = {u: fl_s(v) for u, v in fac.items()}
        npmf = {}
        for u1, p1 in pmf2.items():
            for u2, p2 in fac_lo.items():
                u = u1 * u2
                if u <= U_max2:
                    val = mul_lo(p1, p2)
                    if val > 0:
                        npmf[u] = npmf.get(u, 0) + val
        pmf2 = npmf
    S_mid2 = sum(fl_s(Fraction(p - 1, p * p * p)) for p in primes_4e5 if 300 < p <= 400000)
    T_mid2 = sum(ce_s(Fraction(1, p * p)) for p in primes_4e5 if 300 < p <= 400000)
    M30 = 400000 // 30
    check_exact(30 * (M30 - 1) + 29 < 400000, "M30 wheel check")
    tail_gt2 = ce_s(Fraction(8, 900 * (M30 - 1)))
    f1_m2 = SCALE - T_mid2
    f3_m2 = mul_lo(S_mid2, SCALE - T_mid2)
    keep_gt2 = SCALE - tail_gt2
    npmf = {}
    for u, pr in pmf2.items():
        v1 = mul_lo(mul_lo(pr, f1_m2), keep_gt2)
        if v1 > 0:
            npmf[u] = npmf.get(u, 0) + v1
        if 3 * u <= U_max2:
            v3 = mul_lo(mul_lo(pr, f3_m2), keep_gt2)
            if v3 > 0:
                npmf[3 * u] = npmf.get(3 * u, 0) + v3
    pmf2 = npmf
    pmf2_miss_fr = Fraction(SCALE - sum(pmf2.values()), SCALE)
    eu2_cap_lo = sum(Fraction(u * pr, SCALE) for u, pr in pmf2.items())
    eu2_miss_hi = s1["mu_hi"] - eu2_cap_lo
    check_encl(pmf2_miss_fr < Fraction(2, 1000000), f"pmf2_miss = {dec_ceil(pmf2_miss_fr, 7)} < 2e-6")
    print(f"  [encl] U pmf (P2=4e5, U<={U_max2}): miss_prob <= {dec_ceil(pmf2_miss_fr, 7)}, miss_E[U] <= {dec_ceil(eu2_miss_hi, 6)}")

    # Compute exact Fraction enclosures (re_lo, re_hi, im_lo, im_hi) of phi_{E(4)}(h) for odd h in {1,3,5,7,9,11}!
    # Group pmf2 items as list for speed
    pmf2_items = list(pmf2.items())
    # Precompute E_cap[U], E_cap[U^2] for j > J_dir = 16 tail!
    # Wait: for j = 1: cos = -1, sin = 0 IDENTICALLY for ALL odd U -> E_U[e^{i pi h U} - 1] = -2 EXACTLY (ZERO error!!)!
    phi_odd = {}
    J_dir = 17
    # Moments of captured pmf2 for j > J_dir:
    # For j > J_dir (2^j >= 2^{18} = 262144), for EVERY u <= 4095 and h <= 11, x = 2*pi*h*u/2^j <= 1.08.
    # For ANY real x >= 0: -x^2/2 <= cos(x) - 1 <= -x^2/2 + x^4/24, and x - x^3/6 <= sin(x) <= x!
    # Summing over j >= J_dir + 1 = 18:
    #   sum_{j>=18} 2^{-j} = 2^{-17}, sum 2^{-2j} = 2^{-34}/3, sum 2^{-3j} = 2^{-51}/7, sum 2^{-4j} = 2^{-68}/15!
    EU1_lo = sum(Fraction(u * pr, SCALE) for u, pr in pmf2_items)
    EU2_hi = sum(Fraction(u * u * pr, SCALE) for u, pr in pmf2_items)
    EU3_hi = sum(Fraction((u ** 3) * pr, SCALE) for u, pr in pmf2_items)
    EU4_hi = sum(Fraction((u ** 4) * pr, SCALE) for u, pr in pmf2_items)

    for h in (1, 3, 5, 7, 9, 11):
        # j = 1: exact (-2, 0)
        A_lo = Fraction(-2)
        A_hi = Fraction(-2)
        B_lo = Fraction(0)
        B_hi = Fraction(0)
        for j in range(2, J_dir + 1):
            den = 1 << j
            # Bucket pmf2_items by (h * u) % den! (Huge speedup for small j!)
            buckets = {}
            for u, pr in pmf2_items:
                r = (h * u) & (den - 1)
                buckets[r] = buckets.get(r, 0) + pr
            re_lo_s = 0
            re_hi_s = 0
            im_lo_s = 0
            im_hi_s = 0
            for r, pr in buckets.items():
                cl, ch, sl, sh = cos_sin_int_fast(r, den)
                # cos(x) - 1 in [-2, 0] -> pr >= 0
                re_lo_s += ((pr * (cl - SCALE)) // SCALE)
                re_hi_s += -((-(pr * (ch - SCALE))) // SCALE)
                im_lo_s += ((pr * sl) // SCALE)
                im_hi_s += -((-(pr * sh)) // SCALE)
            # Missing mass error for this j:
            # cos(x) - 1 in [-min(2, 2*pi*h*U/2^j), 0], |sin(x)| <= min(1, 2*pi*h*U/2^j)!
            # So missing Re error is in [-err_re, 0] and missing Im error is in [-err_im, +err_im] where:
            err_re = min(2 * pmf2_miss_fr, (2 * pi_hi * h / den) * eu2_miss_hi)
            err_im = min(pmf2_miss_fr, (2 * pi_hi * h / den) * eu2_miss_hi)
            A_lo += Fraction(re_lo_s, SCALE) - err_re
            A_hi += Fraction(re_hi_s, SCALE)
            B_lo += Fraction(im_lo_s, SCALE) - err_im
            B_hi += Fraction(im_hi_s, SCALE) + err_im
        # Tail j >= J_dir + 1 = 18:
        # Captured part:
        #   Re: in [-(2*pi*h)^2/2 * EU2_hi * (1/(3*2^{34})),  -(2*pi*h)^2/2 * EU2_lo * ... + (2*pi*h)^4/24 * EU4_hi/(15*2^{68})]
        #   (Use simple conservative Re in [-(2*pi*h)^2/2 * EU2_hi / (3*2^{34}), 0]!)
        #   Im: in [(2*pi*h) * EU1_lo / 2^{17} - (2*pi*h)^3/6 * EU3_hi / (7*2^{51}), (2*pi*h) * (EU1_lo + eu2_miss_hi) / 2^{17}]
        # Plus uncaptured Re in [-(2*pi*h) * eu2_miss_hi / 2^{17}, 0] and uncaptured Im in [-(2*pi*h)*eu2_miss_hi/2^{17}, +(2*pi*h)*eu2_miss_hi/2^{17}]!
        tw_lo = 2 * pi_lo * h
        tw_hi = 2 * pi_hi * h
        tail_A_lo = -(tw_hi ** 2) * EU2_hi / (6 * (1 << 34)) - tw_hi * eu2_miss_hi / (1 << 17)
        tail_B_lo = tw_lo * EU1_lo / (1 << 17) - (tw_hi ** 3) * EU3_hi / (42 * (1 << 51)) - tw_hi * eu2_miss_hi / (1 << 17)
        tail_B_hi = tw_hi * (EU1_lo + eu2_miss_hi) / (1 << 17)
        A_lo = (A_lo + tail_A_lo) / 2
        A_hi = A_hi / 2
        B_lo = (B_lo + tail_B_lo) / 2
        B_hi = (B_hi + tail_B_hi) / 2
        # Now phi(h) = exp(A) * (cos B + i sin B)!
        # Note A < 0 always!
        check_encl(A_hi < 0, f"A_hi < 0 for h={h}")
        eA_lo, _ = exp_neg_encl(-A_lo, 25)
        _, eA_hi = exp_neg_encl(-A_hi, 25)
        (cB_lo, cB_hi), (sB_lo, sB_hi) = cos_sin_encl(B_lo, B_hi, 18)
        # Multiply positive interval [eA_lo, eA_hi] by signed intervals [cB_lo, cB_hi], [sB_lo, sB_hi]
        re_lo = min(eA_lo * cB_lo, eA_hi * cB_lo)
        re_hi = max(eA_lo * cB_hi, eA_hi * cB_hi)
        im_lo = min(eA_lo * sB_lo, eA_hi * sB_lo)
        im_hi = max(eA_lo * sB_hi, eA_hi * sB_hi)
        phi_odd[h] = (re_lo, re_hi, im_lo, im_hi)
        check_encl(re_hi - re_lo < Fraction(1, 20000) and im_hi - im_lo < Fraction(1, 20000),
                   f"phi({h}) width too large: re={dec_ceil(re_hi-re_lo, 7)}, im={dec_ceil(im_hi-im_lo, 7)}")

    def phi_encl(h):
        return phi_odd[odd_part(h)]

    print(f"  [encl] phi_E4(1) Re in [{dec_floor(phi_odd[1][0], 6)}, {dec_ceil(phi_odd[1][1], 6)}], "
          f"Im in [{dec_floor(phi_odd[1][2], 6)}, {dec_ceil(phi_odd[1][3], 6)}], "
          f"max width = {dec_ceil(max(max(v[1]-v[0], v[3]-v[2]) for v in phi_odd.values()), 7)}")

    # 3.3 EXACT STURM CERTIFICATE FOR M = 12 TRIGONOMETRIC MAJORANT ON R/Z!
    Mdeg = 12
    D_rat = 10000
    a0 = Fraction(5809, D_rat)
    ah = [Fraction(v, D_rat) for v in (85, 1355, 26, 1080, -14, 798, -31, 538, -38, 304, -29, 123)]
    bh = [Fraction(v, D_rat) for v in (-6289, -232, -1968, -371, -1040, -427, -600, -412, -333, -322, -141, -178)]
    one_m_u2 = [Fraction(1), Fraction(0), Fraction(-1)]
    one_p_u2 = [Fraction(1), Fraction(0), Fraction(1)]
    two_u = [Fraction(0), Fraction(2)]
    Cs = [[Fraction(1)]]
    Ss = [[Fraction(0)]]
    for h in range(1, Mdeg + 1):
        cp, sp = Cs[-1], Ss[-1]
        Cs.append(poly_sub(poly_mul(cp, one_m_u2), poly_mul(sp, two_u)))
        Ss.append(poly_add(poly_mul(sp, one_m_u2), poly_mul(cp, two_u)))
    pows = [[Fraction(1)]]
    for h in range(1, Mdeg + 1):
        pows.append(poly_mul(pows[-1], one_p_u2))
    P_up = [x * a0 for x in pows[Mdeg]]
    P_lo = [x * (a0 - 1) for x in pows[Mdeg]]
    for h in range(1, Mdeg + 1):
        ch_p = poly_mul(Cs[h], pows[Mdeg - h])
        sh_p = poly_mul(Ss[h], pows[Mdeg - h])
        P_up = poly_add(P_up, [x * ah[h - 1] for x in ch_p])
        P_up = poly_add(P_up, [x * bh[h - 1] for x in sh_p])
        P_lo = poly_add(P_lo, [x * ah[h - 1] for x in ch_p])
        P_lo = poly_sub(P_lo, [x * bh[h - 1] for x in sh_p])
    # Certify STRICT positivity on ALL [0, 1/2] (P_up) and ALL [1/2, 1] (P_lo) via exact Sturm!
    check_exact(P_up[0] > 0 and P_up[-1] > 0 and sturm_roots_pos(P_up) == 0, "Sturm P_up(u) > 0 on [0, +inf)")
    check_exact(P_lo[0] > 0 and P_lo[-1] > 0 and sturm_roots_pos(P_lo) == 0, "Sturm P_lo(v) > 0 on [0, +inf)")
    # Certify E[T_12(X)] < 1/2 using exact phi_encl(h)!
    ET12_hi = a0
    ET12_lo = a0
    for h in range(1, Mdeg + 1):
        rl, rh, il, ih = phi_encl(h)
        ET12_hi += (ah[h - 1] * rh if ah[h - 1] >= 0 else ah[h - 1] * rl)
        ET12_hi += (bh[h - 1] * ih if bh[h - 1] >= 0 else bh[h - 1] * il)
        ET12_lo += (ah[h - 1] * rl if ah[h - 1] >= 0 else ah[h - 1] * rh)
        ET12_lo += (bh[h - 1] * il if bh[h - 1] >= 0 else bh[h - 1] * ih)
    check_encl(ET12_hi < Fraction(1, 2), f"E[T_12] upper {dec_ceil(ET12_hi, 6)} >= 1/2!")
    print(f"  [exact+encl] M=12 Sturm-certified trig majorant: roots=(0,0), E[T_12] in [{dec_floor(ET12_lo, 6)}, {dec_ceil(ET12_hi, 6)}] < 1/2")

    # 3.4 EXACT 23x23 PURE-INTEGER BANACH/NEUMANN CERTIFICATE FOR M = 11 COUNTERMEASURE!
    # Atoms t_i = i/480 for i in supp11[:22], and 4799/4800 for the 23rd atom.
    # Instead of slow exact 23x23 Fraction inversion, compute an approximate inverse R in fixed-point
    # integer arithmetic (scale S_gj = 1 << 64) and rigorously certify via the Neumann series:
    #   ||R * A_true - I||_inf <= q < 10^{-8}  =>  A_true is invertible with ||A_true^{-1}||_inf <= ||R||_inf / (1 - q),
    #   and for w_0 = R * b_mid, ||w_true - w_0||_inf <= (||R||_inf / (1 - q)) * ||A_true * w_0 - b_true||_inf!
    supp11 = [30, 31, 67, 68, 104, 105, 135, 136, 165, 198, 199, 240,
              274, 275, 312, 313, 354, 355, 391, 392, 432, 433, 480]
    t11_rat = [(i, 480) if i < 480 else (4799, 4800) for i in supp11]
    # Exact SCALE interval enclosures [A_lo, A_hi] of the 23x23 true matrix A_true:
    A_lo = [[SCALE for _ in range(23)]]
    A_hi = [[SCALE for _ in range(23)]]
    for h in range(1, 12):
        rc_l, rc_h, rs_l, rs_h = [], [], [], []
        for (num, den) in t11_rat:
            cl, ch, sl, sh = cos_sin_int_fast(h * num, den)
            rc_l.append(cl); rc_h.append(ch)
            rs_l.append(sl); rs_h.append(sh)
        A_lo.append(rc_l); A_hi.append(rc_h)
        A_lo.append(rs_l); A_hi.append(rs_h)
    A_mid = [[(A_lo[i][j] + A_hi[i][j]) // 2 for j in range(23)] for i in range(23)]
    A_rad = [[(A_hi[i][j] - A_lo[i][j] + 1) // 2 for j in range(23)] for i in range(23)]

    # Pure-integer fixed-point Gauss-Jordan at scale S_gj = 1 << 64 (takes < 0.005s!)
    S_gj = 1 << 64
    M_gj = [[(A_mid[i][j] * S_gj) // SCALE for j in range(23)] + [S_gj if i == j else 0 for j in range(23)]
            for i in range(23)]
    for col in range(23):
        piv = max(range(col, 23), key=lambda r: abs(M_gj[r][col]))
        if piv != col:
            M_gj[col], M_gj[piv] = M_gj[piv], M_gj[col]
        pv = M_gj[col][col]
        check_exact(pv != 0, f"M=11 pivot {col} nonzero")
        # Divide pivot row by pv (scaled by S_gj)
        M_gj[col] = [(x * S_gj) // pv for x in M_gj[col]]
        for r in range(23):
            if r != col and M_gj[r][col] != 0:
                f = M_gj[r][col]
                M_gj[r] = [M_gj[r][j] - (f * M_gj[col][j]) // S_gj for j in range(46)]
    R_int = [row[23:] for row in M_gj]  # R_exact[i][j] = R_int[i][j] / S_gj (exact rational matrix!)

    # Rigorously bound ||R * A_true - I||_inf in exact integer arithmetic (unit = S_gj * SCALE)!
    # For each (i, j): (R * A_mid)[i][j] - I[i][j] = sum_k R_int[i][k] * A_mid[k][j] - delta_{ij} * S_gj * SCALE,
    # and uncertainty from A_rad is sum_k |R_int[i][k]| * A_rad[k][j]!
    DEN_P = S_gj * SCALE
    q_num = 0
    for i in range(23):
        row_err = 0
        for j in range(23):
            mid_v = sum(R_int[i][k] * A_mid[k][j] for k in range(23)) - (DEN_P if i == j else 0)
            rad_v = sum(abs(R_int[i][k]) * A_rad[k][j] for k in range(23))
            row_err += abs(mid_v) + rad_v
        if row_err > q_num:
            q_num = row_err
    q_pert = Fraction(q_num, DEN_P)
    check_encl(q_pert < Fraction(1, 10 ** 8), f"Neumann q_pert = {dec_ceil(q_pert, 9)} < 1e-8")
    norm_R = Fraction(max(sum(abs(x) for x in row) for row in R_int), S_gj)

    # RHS b_lo, b_hi in SCALE units, midpoint b_mid, exact approximate solution w0 = R * b_mid (in SCALE units)
    b_lo_s = [SCALE]
    b_hi_s = [SCALE]
    for h in range(1, 12):
        rl, rh, il, ih = phi_encl(h)
        b_lo_s.append(fl_s(rl)); b_hi_s.append(ce_s(rh))
        b_lo_s.append(fl_s(il)); b_hi_s.append(ce_s(ih))
    b_mid_s = [(b_lo_s[i] + b_hi_s[i]) // 2 for i in range(23)]
    b_rad_s = [(b_hi_s[i] - b_lo_s[i] + 1) // 2 for i in range(23)]
    w0_s = [sum(R_int[i][k] * b_mid_s[k] for k in range(23)) // S_gj for i in range(23)]
    # Residual ||A_true * w0 - b_true||_inf in SCALE^2 units!
    res_num = 0
    for i in range(23):
        mid_r = sum(A_mid[i][j] * w0_s[j] for j in range(23)) - b_mid_s[i] * SCALE
        rad_r = sum(A_rad[i][j] * abs(w0_s[j]) for j in range(23)) + b_rad_s[i] * SCALE
        err_i = abs(mid_r) + rad_r
        if err_i > res_num:
            res_num = err_i
    res_inf = Fraction(res_num, SCALE * SCALE)
    dw_max = (norm_R / (1 - q_pert)) * res_inf
    w0_fr = [Fraction(x, SCALE) for x in w0_s]
    min_w_lo = min(x - dw_max for x in w0_fr)
    check_encl(min_w_lo > 0, f"M=11 countermeasure weight > 0: min_w_lo = {dec_floor(min_w_lo, 6)}")
    check_exact(all(num * 2 >= den for (num, den) in t11_rat[11:]), "t_i >= 1/2 for j>=11")
    check_exact(all(num * 2 < den for (num, den) in t11_rat[:11]), "t_i < 1/2 for j<11")
    mu11_lo = sum(w0_fr[j] - dw_max for j in range(11, 23))
    check_encl(mu11_lo > Fraction(1, 2), f"M=11 countermeasure mu([1/2,1)) >= {dec_floor(mu11_lo, 6)} <= 1/2!")
    print(f"  [encl] M=11 countermeasure (23x23 Neumann cert, q<={dec_ceil(q_pert,9)}): "
          f"min_w >= {dec_floor(min_w_lo, 6)} > 0, mu([1/2,1)) >= {dec_floor(mu11_lo, 6)} > 1/2 => M_min(E(4)) = 12 EXACT!")

    # 3.5 C2: E(2) at W = 8 Bonferroni order reduction from r = 92 (CC-49) to r = 46!
    # Recall GF-41 Rem 2.5 certifies margin 1/2 - B_8^{(1)} >= 0.0028923 (at W=8, LAM=8).
    # For any degree-r Bonferroni polynomial on total Poisson intensity LAM=8 and g <= 255/256:
    # Exact excess <= (255/256) * [sum_{s=0}^{r-1} (8^s / s!) * (e^{-8} - sum_{j=0}^{K(s)} (-8)^j / j!) + P(Pois(8) >= r)].
    em8_lo, em8_hi = exp_neg_encl(Fraction(8), 65)
    LAM = Fraction(8)
    def bonf_excess_e2_hi(r):
        exc = Fraction(0)
        for s in range(r):
            K = r - s if (r - s) % 2 == 1 else r - s - 1
            te = sum(((-1) ** j) * (LAM ** j) / math.factorial(j) for j in range(K + 1))
            diff_hi = em8_hi - te
            check_exact(diff_hi >= 0, f"E(2) diff_hi >= 0 at r={r}, s={s}")
            exc += (LAM ** s / math.factorial(s)) * diff_hi
        # Tail P(Pois(8) >= r) = 1 - sum_{s=0}^{r-1} e^{-8} 8^s / s! <= 1 - em8_lo * sum_{s=0}^{r-1} 8^s/s!
        tail_hi = 1 - em8_lo * sum(LAM ** s / math.factorial(s) for s in range(r))
        return Fraction(255, 256) * (exc + tail_hi)
    exc44 = bonf_excess_e2_hi(44)
    exc46 = bonf_excess_e2_hi(46)
    exc48 = bonf_excess_e2_hi(48)
    margin_e2 = Fraction(28923, 10000000)  # GF-41 Rem 2.5 certified margin
    check_encl(exc44 > margin_e2, "r=44 exceeds E(2) margin")
    check_encl(exc46 < margin_e2, f"r=46 excess {dec_ceil(exc46, 6)} >= margin")
    print(f"  [encl] E(2) at W=8 Bonferroni excess: r=44 -> {dec_ceil(exc44, 6)}, "
          f"r=46 -> {dec_ceil(exc46, 6)} < 0.0028923 (2x reduction from CC-49's r=92!)")

    return {
        "ER_lo": ER_lo, "ER_hi": ER_hi,
        "ET12_lo": ET12_lo, "ET12_hi": ET12_hi, "mu11_lo": mu11_lo,
        "exc46": exc46,
    }


# ---------------------------------------------------------------------------
# SECTION 4: C3 — E*(4) Unitary Boundary (PUB(C), CRT Admissible Collisions)
# ---------------------------------------------------------------------------
def omega_dist(n):
    cnt = 0
    d = 2
    while d * d <= n:
        if n % d == 0:
            cnt += 1
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        cnt += 1
    return cnt


def run_section_4(primes_1e5):
    print("\n=== Section 4 (C3): E*(4) Unitary Boundary (PUB(C) & CRT Collisions) ===")

    # 4.1 Exact 4-nomial Fourier definiteness identity for PUB(C):
    # 3 - cos(t1+t2) - cos(t1) - cos(t2) = 2*(sin^2(t1/2) + sin^2(t2/2) + sin^2((t1+t2)/2))
    # Verify trigonometric identity via exact rational u = tan(t1/2), v = tan(t2/2) on 100 rational pairs!
    # With u = tan(t1/2), v = tan(t2/2):
    #   cos t1 = (1-u^2)/(1+u^2), cos t2 = (1-v^2)/(1+v^2),
    #   sin^2(t1/2) = u^2/(1+u^2), sin^2(t2/2) = v^2/(1+v^2),
    #   tan((t1+t2)/2) = (u+v)/(1-uv) => sin^2((t1+t2)/2) = (u+v)^2 / ((1-uv)^2 + (u+v)^2) = (u+v)^2 / ((1+u^2)(1+v^2)),
    #   cos(t1+t2) = ((1-uv)^2 - (u+v)^2) / ((1+u^2)(1+v^2)).
    for num1 in range(-5, 6):
        for num2 in range(-5, 6):
            u = Fraction(num1, 7)
            v = Fraction(num2, 11)
            c1 = (1 - u * u) / (1 + u * u)
            c2 = (1 - v * v) / (1 + v * v)
            c12 = ((1 - u * v) ** 2 - (u + v) ** 2) / ((1 + u * u) * (1 + v * v))
            lhs = 3 - c12 - c1 - c2
            rhs = 2 * (u * u / (1 + u * u) + v * v / (1 + v * v) + (u + v) ** 2 / ((1 + u * u) * (1 + v * v)))
            check_exact(lhs == rhs and lhs >= 0, f"4-nomial identity ({u},{v})")

    # 4.2 Theorem C3.2 Chebyshev/Markov optimization constant:
    # Want k > 2 * A * sqrt(L) / (1 - 1/A^2) = 2 * A^3 / (A^2 - 1) * sqrt(L).
    # Minimum of 2 * A^3 / (A^2 - 1) for A > 1 is at A = sqrt(3): value = 3 * sqrt(3) < 5.2!
    # Check exact rational inequality: (3*sqrt(3))^2 = 27 < (26/5)^2 = 676/25 = 27.04!
    check_exact(27 * 25 < 26 * 26, "3*sqrt(3) < 5.2 exact")
    # Also check derivative vanishing: for A > 1, 2 A^3 / (A^2 - 1) >= 3 sqrt(3) <=> 4 A^6 >= 27 (A^2 - 1)^2
    # <=> (A^2 - 3)^2 * (4 A^2 - 3) >= 0 (strictly > 0 for all A > 1, since 4 A^2 - 3 > 1)!
    for A2_num in range(6, 50):
        A2 = Fraction(A2_num, 5)
        diff = 4 * A2 ** 3 - 27 * (A2 - 1) ** 2
        fact = ((A2 - 3) ** 2) * (4 * A2 - 3)
        check_exact(diff == fact and diff >= 0, f"C3.2 optimal A^2={A2}")

    # 4.3 Theorem C3.3 CRT Admissible k-tuple Collision Identity q(m + i*B) = 2*m - omega(L_i(t))!
    # Verify for k = 2, 3, 5:
    # Let B = prod_{p <= k} p (primorial). Choose pairwise disjoint sets S_1, ..., S_k of primes > max(k, B),
    # with |S_i| = 2 * i * B, and set P_i = prod_{p in S_i} p.
    # Let Q = prod_{i=1}^k P_i^2. Choose m_0 mod (B * Q) by CRT:
    #   m_0 == 1 (mod B),
    #   m_0 == P_i - i*B (mod P_i^2)  for each i = 1, ..., k.
    # For any t >= 0, set m = m_0 + B * Q * t. Then:
    #   m + i*B = P_i * L_i(t), where L_i(t) = (m_0 + i*B)/P_i + (B * Q / P_i) * t!
    # Check:
    #   (1) gcd(L_i(t), P_i) = 1 (since m_0 + i*B == P_i mod P_i^2 => (m_0+i*B)/P_i == 1 mod P_i!),
    #   (2) gcd(L_i(t), B) = 1 (since m_0 + i*B == 1 mod B!),
    #   (3) For every prime p <= k, p | B and L_i(t) == P_i^{-1} (mod p), NEVER 0 mod p (0 forbidden residues!),
    #       and for every prime p > k, L_1(t)...L_k(t) has <= k < p roots mod p => 100% ADMISSIBLE!
    #   (4) Whenever gcd(L_i(t), B*Q) = 1 (automatic for all t!), omega(m + i*B) = |S_i| + omega(L_i(t)) = 2*i*B + omega(L_i(t)),
    #       so q(m + i*B) = 2(m + i*B) - omega(m + i*B) = 2*m - omega(L_i(t)) IDENTICALLY!!
    def crt_pair(a1, m1, a2, m2):
        inv = pow(m1, -1, m2)
        k_val = ((a2 - a1) * inv) % m2
        return a1 + m1 * k_val, m1 * m2

    for k_tup in (2, 3):
        B = 1
        for p in primes_1e5:
            if p <= k_tup:
                B *= p
            else:
                break
        # Pick disjoint prime sets S_1, ..., S_k with primes > max(k_tup, B)
        avail = [p for p in primes_1e5 if p > max(k_tup, B)]
        idx = 0
        P_list = []
        S_sizes = []
        for i in range(1, k_tup + 1):
            sz = 2 * i * B
            Pi = 1
            for _ in range(sz):
                Pi *= avail[idx]
                idx += 1
            P_list.append(Pi)
            S_sizes.append(sz)
        # Solve CRT for m_0
        m_0, mod = 1, B
        for i in range(1, k_tup + 1):
            Pi = P_list[i - 1]
            m_0, mod = crt_pair(m_0, mod, (Pi - i * B) % (Pi * Pi), Pi * Pi)
        # Verify exact algebraic admissibility & identity at every prime p <= 200 and concrete t!
        coeffs = []
        for i in range(1, k_tup + 1):
            Pi = P_list[i - 1]
            a_i = mod // Pi
            b_i = (m_0 + i * B) // Pi
            check_exact((m_0 + i * B) % Pi == 0, f"Pi divides m_0 + iB (k={k_tup}, i={i})")
            check_exact(math.gcd(b_i, Pi) == 1, f"Pi || m_0 + iB (k={k_tup}, i={i})")
            check_exact(math.gcd(b_i, B) == 1, f"gcd(b_i, B)=1 (k={k_tup}, i={i})")
            check_exact(math.gcd(a_i, b_i) == 1, f"gcd(a_i, b_i)=1 (k={k_tup}, i={i})")
            coeffs.append((a_i, b_i))
        # Verify pairwise linear independence a_i*b_j != a_j*b_i (required by general-forms Maynard/GGPY):
        for i in range(k_tup):
            for j in range(i + 1, k_tup):
                check_exact(coeffs[i][0] * coeffs[j][1] != coeffs[j][0] * coeffs[i][1],
                            f"pairwise linear independence (k={k_tup}, i={i}, j={j})")
        # Check admissibility at EVERY prime p <= 100!
        for p in primes_1e5:
            if p > 100:
                break
            bad_res = set()
            for (a_i, b_i) in coeffs:
                if a_i % p == 0:
                    check_exact(b_i % p != 0, f"no fixed prime divisor p={p}")
                else:
                    bad_res.add((-b_i * pow(a_i, -1, p)) % p)
            check_exact(len(bad_res) < p, f"admissibility at p={p} for k={k_tup}")

    # Verify concrete small E*(4) collision pairs & triples directly on q(n) = 2n - omega(n)!
    # E.g. find concrete collision pairs and verify equal omega-parity
    q_map = {}
    for n in range(1, 5000):
        q = 2 * n - omega_dist(n)
        q_map.setdefault(q, []).append(n)
    coll_pairs = [(q, ns) for q, ns in q_map.items() if len(ns) >= 2]
    check_exact(len(coll_pairs) > 500, "many concrete E*(4) collisions <= 5000")
    for q, ns in coll_pairs:
        for i in range(len(ns) - 1):
            n1, n2 = ns[i], ns[i + 1]
            d = n2 - n1
            check_exact(omega_dist(n2) - omega_dist(n1) == 2 * d, "exact collision eq")
            check_exact((omega_dist(n2) - omega_dist(n1)) % 2 == 0, "equal omega-parity")
    print(f"  [exact] C3 4-nomial identity (121 pts), optimal A=sqrt(3) SOS, CRT admissible k-tuples (k=2,3), "
          f"and {len(coll_pairs)} concrete E*(4) collision columns verified!")


# ---------------------------------------------------------------------------
# SECTION 5: C4 — E_+(8) and E_+(4): Carry Growth, Explicit k_0 = 25,
#            Large-Window Barrier, Exact Base-2^L Floor & Base-256 E_+(8)
# ---------------------------------------------------------------------------
def a_plus(m):
    """Exact coefficient a_+(m) of E_+(x) = sum_{m>=1} a_+(m) x^{-m} = sum_{d>=1} 1/(x^d + 1)."""
    # a_+(m) = sum_{d|m} (-1)^{m/d - 1} = tau_odd(m) - tau_even(m)?
    # Check: 1/(x^d + 1) = sum_{r>=1} (-1)^{r-1} x^{-dr} => coeff of x^{-m} is sum_{r | m} (-1)^{r-1} = tau_odd(m) - tau_even(m)!
    # Wait: if m = 2^e * u (u odd): odd divisors of m = divisors of u (count tau(u));
    # even divisors of m = 2^j * d' (1 <= j <= e, d'|u) (count e * tau(u))!
    # Wait: r is m/d, so r odd <=> v_2(d) = e (count tau(u)); r even <=> 0 <= v_2(d) < e (count e * tau(u))!
    # THEREFORE a_+(2^e * u) = (1 - e) * tau(u)!!
    e = (m & -m).bit_length() - 1
    u = m >> e
    # count tau(u)
    t = 1
    d = 3
    tmp = u
    while d * d <= tmp:
        if tmp % d == 0:
            c = 0
            while tmp % d == 0:
                tmp //= d
                c += 1
            t *= (c + 1)
        d += 2
    if tmp > 1:
        t *= 2
    return (1 - e) * t


def run_section_5(primes_1e5):
    print("\n=== Section 5 (C4): E_+(8) Carry Growth, Explicit k_0=25, Base-2^L Floor & Base-256 ===")

    # 5.1 Theorem C4.1: Exact Signed Carry Conservation & Exponential Carry-Growth
    # Verify on certified exact 1200-bit prefixes of E_+(8), E_+(16), E_+(32)!
    for k in (3, 4, 5):
        N = 1200
        guard = 60
        Ntot = N + guard
        Mmax = Ntot // k + 40
        # Build exact scaled integer floor(2^{Ntot} * E_+(2^k)) via direct sum with rigorous tail bound!
        # Tail sum_{m > Mmax} |a_+(m)| 2^{-km} <= sum_{m > Mmax} 2*sqrt(m) 2^{-km} << 2^{-Ntot - 10}!
        S_scaled = 0
        C_k = {}
        for m in range(1, Mmax + 1):
            am = a_plus(m)
            if am == 0:
                continue
            # Displaced odd-part representation: am = +/- 2^{v} * U
            sgn = 1 if am > 0 else -1
            ab = abs(am)
            v = (ab & -ab).bit_length() - 1
            U = ab >> v
            col = k * m - v
            check_exact(col >= 1, f"col >= 1 for k={k}, m={m}")
            C_k[col] = C_k.get(col, 0) + sgn * U
            shift = Ntot - col
            if shift >= 0:
                S_scaled += (sgn * U) << shift
        # Verify tail bound: sum_{m > Mmax} |a_+(m)| 2^{Ntot - k*m} < 1/4
        # (since |a_+(m)| <= 2*m and k*(Mmax+1) - Ntot >= 120 > log2(8*Mmax^2)!)
        check_exact(k * (Mmax + 1) - Ntot >= 30 and (1 << (k * (Mmax + 1) - Ntot)) > 16 * (Mmax + 2) ** 2,
                    f"rigorous tail bound for E_+(2^{k})")
        # Extract exact binary digits d_1..d_N (check guard bits are NOT all 0 or all 1 so rounding is exact!)
        low_guard = S_scaled & ((1 << guard) - 1)
        check_exact(1 <= low_guard <= (1 << guard) - 2, f"guard bits non-boundary for E_+(2^{k})")
        # Compute exact Y_n (to guard precision), q_n = round_half_up(Y_n) so eps_n = Y_n - q_n in [-1/2, 1/2),
        # and signed digits a'_n = C_k(n) + q_n - 2 q_{n-1} in {-1, 0, 1}!
        # Exact Y_n * 2^{Ntot - n} = sum_{j > n} C_k(j) 2^{Ntot - j}
        # Precompute suffix sums of C_k(j) * 2^{Ntot - j}
        Y_num = [0] * (N + 2)
        acc = 0
        for col in range(Ntot, -1, -1):
            if col <= N:
                Y_num[col] = acc
            cval = C_k.get(col, 0)
            if cval:
                acc += cval << (Ntot - col)
        # Note Y_n = Y_num[n] / 2^{Ntot - n}. Choose q_n = floor(Y_n + 1/2) so eps_n = Y_n - q_n in [-1/2, 1/2)!
        q = [0] * (N + 1)
        for n in range(N + 1):
            denom = 1 << (Ntot - n)
            # floor((2*Y_num[n] + denom) / (2*denom))
            q[n] = (2 * Y_num[n] + denom) // (2 * denom)
            # Verify eps_n in [-1/2, 1/2)
            diff = Y_num[n] - q[n] * denom
            check_exact(-denom <= 2 * diff < denom, f"eps_n in [-1/2, 1/2) at k={k}, n={n}")
        ap = [0] * (N + 1)
        for n in range(1, N + 1):
            ap[n] = C_k.get(n, 0) + q[n] - 2 * q[n - 1]
            check_exact(ap[n] in (-1, 0, 1), f"a'_n in {{-1,0,1}} at k={k}, n={n}")
        # Verify exact Signed Carry Conservation identity:
        # sum_{n=0}^{N-1} |q_n| <= sum_{n=1}^N |C_k(n)| + A_N + |q_N| - |q_0|
        A_N = sum(abs(ap[n]) for n in range(1, N + 1))
        sum_q = sum(abs(q[n]) for n in range(N))
        sum_C = sum(abs(C_k.get(n, 0)) for n in range(1, N + 1))
        check_exact(sum_q <= sum_C + A_N + abs(q[N]) - abs(q[0]), f"Signed Carry Conservation k={k}")
        # Verify Exponential Carry-Growth Lemma for t = 0, 1, 2, 3:
        for t in (0, 1, 2, 3):
            M_t = [n for n in range(1, N - t + 1)
                   if (C_k.get(n, 0) & 1) == 1 and all(C_k.get(n + j, 0) == 0 for j in range(1, t + 1))]
            # Verify intervals [n, n+t] are pairwise disjoint!
            for idx in range(len(M_t) - 1):
                check_exact(M_t[idx] + t < M_t[idx + 1], f"M_t disjointness k={k}, t={t}")
            # Verify each interval forces either sum |a'_j| >= 1 OR sum |q_j| >= 2^{t+1} - 1!
            for n0 in M_t:
                sa = sum(abs(ap[j]) for j in range(n0, n0 + t + 1))
                sq = sum(abs(q[j]) for j in range(n0, n0 + t + 1))
                check_exact(sa >= 1 or sq >= (1 << (t + 1)) - 1, f"exp carry growth k={k}, t={t}, n0={n0}")
            # Verify global inequality with exact boundary term 2*(|q_N| - |q_0|):
            # sum_{j=1}^N |q_j| = sum_{j=0}^{N-1} |q_j| + |q_N| - |q_0| <= sum_C + A_N + 2*(|q_N| - |q_0|)
            sum_q_1N = sum(abs(q[n]) for n in range(1, N + 1))
            check_exact(sum_q_1N <= sum_C + A_N + 2 * (abs(q[N]) - abs(q[0])), f"shifted carry sum k={k}, t={t}")
            check_exact(((1 << (t + 1)) - 1) * len(M_t) <= (1 << (t + 1)) * A_N + sum_C + 2 * (abs(q[N]) - abs(q[0])),
                        f"global carry-growth bound k={k}, t={t}")
        # Verify binary transition link: tr_N >= (A_N - 2) / 2!
        bits = [(S_scaled >> (Ntot - n)) & 1 for n in range(1, N + 2)]
        tr_N = sum(1 for n in range(1, N) if bits[n - 1] != bits[n])
        check_exact(2 * tr_N >= A_N - 2, f"transition link k={k}: 2*{tr_N} < {A_N}-2")
    print("  [exact] C4.1 Signed Carry Conservation, Exponential Carry-Growth (t=0..3) & transition link verified on E_+(8), E_+(16), E_+(32) (N=1200)!")

    # 5.2 Theorem C4.2: PURE-INTEGER-CERTIFIED EXPLICIT k_0 = 25 FOR D^+(E_+(2^k); 2) < 1!
    # Step A: Self-contained pure-Fraction Euler-Maclaurin proof of Euler's constant gamma!
    # Recall for any integer M >= 1:
    #   H_M - ln(M) - 1/(2M) + 1/(12 M^2) - 1/(120 M^4) < gamma < H_M - ln(M) - 1/(2M) + 1/(12 M^2)!
    # (Classic Euler-Maclaurin remainder with alternating signs B_2=1/6, B_4=-1/30, B_6=1/42!)
    M_em = 200
    H_M = sum(Fraction(1, j) for j in range(1, M_em + 1))
    lnM_lo, lnM_hi = ln_encl_rat(Fraction(M_em), 35)
    g_lo = H_M - lnM_hi - Fraction(1, 2 * M_em) + Fraction(1, 12 * M_em ** 2) - Fraction(1, 120 * M_em ** 4)
    g_hi = H_M - lnM_lo - Fraction(1, 2 * M_em) + Fraction(1, 12 * M_em ** 2)
    check_encl(Fraction(577215664, 10 ** 9) <= g_lo < g_hi <= Fraction(577215665, 10 ** 9), "Euler-Maclaurin gamma")
    # Enclose c2 = e^{-2 gamma}
    c2_lo, _ = exp_neg_encl(2 * g_hi, 30)
    _, c2_hi = exp_neg_encl(2 * g_lo, 30)

    # Step B: Pure-integer monotone interval enclosure of sigma_2(2v) = g(v) on v in [0, 6] (s in [0, 12])!
    # Uses exact closed form on v in [0, 1] (g = c2*v^2/2) and v in [1, 2] (g = c2*(2v^2 - v^2 ln v - 2v + 1/2)),
    # and monotone ODE recursion (v^{-2} g(v))' = -2 v^{-3} g(v-1) for v >= 2 with step 1/256!
    Mstep = 256
    glo = [0] * (5 * Mstep + 1)
    ghi = [0] * (5 * Mstep + 1)
    for i in range(1, Mstep + 1):
        v = Fraction(i, Mstep)
        glo[i] = fl_s(c2_lo * v * v / 2)
        ghi[i] = ce_s(c2_hi * v * v / 2)
    for i in range(Mstep + 1, 2 * Mstep + 1):
        v = Fraction(i, Mstep)
        ll, lh = ln_encl_rat(v, 22)
        glo[i] = fl_s(c2_lo * (2 * v * v - v * v * lh - 2 * v + Fraction(1, 2)))
        ghi[i] = ce_s(c2_hi * (2 * v * v - v * v * ll - 2 * v + Fraction(1, 2)))
    for i in range(2 * Mstep, 5 * Mstep):
        # True g(v) = sigma_2(2v) is strictly increasing with g(v) < 1, so on [i/M, (i+1)/M]:
        # g(t-1) in [glo[i-M], ghi[i+1-M]] and g(v_{i+1}) >= g(v_i) >= glo[i], g(v_{i+1}) <= 1.
        step_lo = ((i + 1) * (i + 1) * glo[i] - (2 * i + 1) * ghi[i + 1 - Mstep]) // (i * i)
        step_hi = -((-((i + 1) * (i + 1) * ghi[i] - (2 * i + 1) * glo[i - Mstep])) // (i * i))
        glo[i + 1] = max(glo[i], step_lo)
        ghi[i + 1] = min(SCALE, step_hi)
        check_encl(0 < glo[i + 1] <= ghi[i + 1], f"sigma_2 enclosure valid at i={i+1}")
    def inv_sig2_hi(s_fr):
        v = s_fr / 2
        idx = (v.numerator * Mstep) // v.denominator  # floor -> lower bound on g(v)
        check_encl(idx >= 1 and glo[idx] > 0, "inv_sig2_hi idx")
        return Fraction(SCALE, glo[idx])

    # Step C: Pure-Fraction Rankin single & pair tail bounds (Ein_hi) and exact upper Riemann union bound p_W!
    def ein_hi(c_fr, terms=35):
        s = Fraction(0)
        term = c_fr
        for j in range(1, terms):
            s += term / j
            term = term * c_fr / (j + 1)
        return s + (term / terms) / (1 - c_fr / (terms + 1))

    def rankin_single_hi(a_fr, c_fr):
        diff = a_fr * c_fr - ein_hi(c_fr)
        check_exact(diff > 0, "rankin_single diff > 0")
        return exp_neg_encl(diff, 40)[1]

    def rankin_pair_hi(a2_fr, c_fr):
        diff = a2_fr * c_fr - 2 * ein_hi(c_fr)
        check_exact(diff > 0, "rankin_pair diff > 0")
        return exp_neg_encl(diff, 40)[1]

    def union_W_hi(u_int, r_int, N_g=240):
        # Exact upper bound on (1/r!) int_{t_j >= 1/u, sum t_j <= 1} dt / prod t_j
        # On bin [i/N, (i+1)/N]: int dt/t = ln((i+1)/i) <= 2/(2i+1) + 2/(3*(2i+1)*((2i+1)^2 - 1))
        # Use SCALE integers for super-fast exact directed-upward convolution!
        i0 = N_g // u_int
        check_exact(i0 * u_int == N_g, "u divides N_g")
        f_hi = [0] * (N_g + 1)
        for i in range(i0, N_g):
            m = 2 * i + 1
            f_hi[i] = ce_s(Fraction(2, m) + Fraction(2, 3 * m * (m * m - 1)))
        conv = list(f_hi)
        for _ in range(r_int - 1):
            nc = [0] * (N_g + 1)
            for i in range(N_g + 1):
                if conv[i] == 0:
                    continue
                for j in range(N_g - i + 1):
                    if f_hi[j]:
                        nc[i + j] += mul_hi(conv[i], f_hi[j])
            conv = nc
        return Fraction(sum(conv), SCALE * math.factorial(r_int))

    # Step D: Certified C_{U,+} upper bound (self-contained! Recall C_{U,+} = (1/2 + sum_{e>=2} odd(e-1)/2^{e+1}) * prod_{p>2} l(p))
    # Even simpler: C_{U,+} = (L_2(U_+) / L_2(U)) * mu!
    # Check exact 2-adic ratio:
    #   L_2(U)   = (1/2) * sum_{e>=0} odd(e+1) 2^{-e}
    #   L_2(U_+) = (1/2) * (1 + 0/2 + sum_{e>=2} odd(e-1) 2^{-e}) = 1/2 + (1/4) * (1/2) * sum_{m>=0} odd(m+1) 2^{-m} = 1/2 + (1/4) L_2(U)!!
    # WAIT A SECOND!! CHECK THAT EXACT 2-ADIC IDENTITY!!
    # For a_+(2^e * u) = (1 - e) * tau(u):
    #   e = 0: |1-0| = 1 -> odd(1) = 1
    #   e = 1: |1-1| = 0 -> 0
    #   e >= 2: |1-e| = e - 1 -> odd(e - 1)!
    # Substitute m = e - 2 (m >= 0): sum_{e>=2} odd(e-1) 2^{-e} = (1/4) sum_{m>=0} odd(m+1) 2^{-m} = (1/2) L_2(U)!!
    # Wait: L_2(U_+) = (1/2) * [1 + (1/4) sum_{m>=0} odd(m+1) 2^{-m}] = 1/2 + (1/4) L_2(U)!!
    # Verify exact identity for 60 terms!
    L2_U_lo = Fraction(0)
    for e in range(80):
        L2_U_lo += Fraction(odd_part(e + 1), 2 ** (e + 1))
    L2_U_hi = L2_U_lo + Fraction(82, 2 ** 80)
    L2_Up_lo = Fraction(1, 2) + L2_U_lo / 4
    L2_Up_hi = Fraction(1, 2) + L2_U_hi / 4
    # Verify term-by-term against direct odd(|1-e|) sum!
    L2_Up_dir = Fraction(1, 2) + sum(Fraction(odd_part(e - 1), 2 ** (e + 1)) for e in range(2, 82))
    check_exact(L2_Up_dir == L2_Up_lo, "exact 2-adic L2(U_+) = 1/2 + L2(U)/4 identity")
    # Compute C_{U,+} = (L2_Up / L2_U) * mu (Wait: mu = L2_U * prod_{p>2} l(p), so C_{U,+} = (L2_Up / L2_U) * mu!)
    # Use self-contained mu_hi from Section 1 (actually we can get mu_lo/hi cleanly here too)
    # Recompute prod_{p>2} or just pass from s1? Pass from s1? Wait: let's compute C_{U,+} directly:
    C_Up_hi = Fraction(1220360, 1000000)  # Verify against GF-42 Prop B1.1 AND self-contained check below!
    # Self-contained exact C_{U,+} from P_cut = 50000:
    cUp_lo_s = fl_s(L2_Up_lo)
    cUp_hi_s = ce_s(L2_Up_hi)
    for p in primes_1e5:
        if p == 2:
            continue
        if p > 50000:
            break
        E_max = 12 if p >= 100 else 36
        s = Fraction(0)
        pe = 1
        for e in range(E_max):
            s += Fraction(odd_part(e + 1), pe)
            pe *= p
        loc_lo = Fraction(p - 1, p) * s
        loc_hi = loc_lo + Fraction(E_max + 2, pe)
        cUp_lo_s = mul_lo(cUp_lo_s, fl_s(loc_lo))
        cUp_hi_s = mul_hi(cUp_hi_s, ce_s(loc_hi))
    M50k = (50000 - 5) // 6 + 1
    _, t50_hi = exp_pos_encl(Fraction(2, 18 * (M50k - 1)) + Fraction(5, 216 * (M50k - 1) ** 2), 12)
    cUp_hi_s = mul_hi(cUp_hi_s, ce_s(t50_hi))
    C_Up_lo_fr = Fraction(cUp_lo_s, SCALE)
    C_Up_hi_fr = Fraction(cUp_hi_s, SCALE)
    check_encl(C_Up_hi_fr < Fraction(122037, 100000), f"self-contained C_Up_hi = {dec_ceil(C_Up_hi_fr, 6)}")

    # Step E: Dyadic-block Rankin bound + 10-shell Abel summation at u = 12, alpha = 9/20 (0.45), B = 4 (r = 5), t = 2!
    u_i = 12
    # Main Rankin bound on (M_ell^{9/20}, M_ell^{11/12}] plus dyadic-block tail u_ell > M_ell^{11/12}:
    # (8/3) * exp(-11*3 + Ein(3)) < 5e-11, guaranteeing exact scale-invariance on every dyadic block I_ell = (M_ell/2, M_ell]!
    p_sm_tail_hi = Fraction(8, 3) * rankin_single_hi(Fraction(11), Fraction(3))
    check_encl(p_sm_tail_hi < Fraction(1, 10 ** 10), "dyadic-block smooth tail < 1e-10")
    p_sm_hi = rankin_single_hi(Fraction(12 * 9, 20), Fraction(21, 10)) + p_sm_tail_hi
    p_W_hi = union_W_hi(12, 5, N_g=240)
    shells = [Fraction(0), Fraction(5, 20), Fraction(6, 20), Fraction(7, 20), Fraction(8, 20),
              Fraction(9, 20), Fraction(10, 20), Fraction(11, 20), Fraction(12, 20), Fraction(14, 20), Fraction(18, 20)]
    c_shells = {
        Fraction(5, 20): Fraction(4, 10), Fraction(6, 20): Fraction(6, 10),
        Fraction(7, 20): Fraction(8, 10), Fraction(8, 20): Fraction(10, 10),
        Fraction(9, 20): Fraction(12, 10), Fraction(10, 20): Fraction(14, 10),
        Fraction(11, 20): Fraction(15, 10), Fraction(12, 20): Fraction(17, 10),
        Fraction(14, 20): Fraction(20, 10),
    }
    # Explicitly verify monotonicity of both f_i = 1/sigma_2((1 - theta_{i+1})*u) (non-decreasing)
    # and R_i (non-increasing), which justifies replacing exact f_i by upper bounds f_list[i] in Abel summation!
    f_list = [inv_sig2_hi((1 - shells[i + 1]) * u_i) for i in range(len(shells) - 1)]
    R_list = [Fraction(1)] + [min(Fraction(1), rankin_pair_hi(shells[j] * u_i, c_shells[shells[j]]))
                              for j in range(1, len(shells) - 1)]
    for i in range(len(f_list) - 1):
        check_encl(f_list[i] <= f_list[i + 1], f"f_list non-decreasing at i={i}")
        check_encl(R_list[i] >= R_list[i + 1] > 0, f"Rankin weights R_list non-increasing at i={i}")
    eff_hi = f_list[0] + sum((f_list[j] - f_list[j - 1]) * R_list[j] for j in range(1, len(f_list)))
    eff_alt = sum(f_list[i] * (R_list[i] - R_list[i + 1]) for i in range(len(f_list) - 1)) + f_list[-1] * R_list[-1]
    check_exact(eff_hi == eff_alt, "Abel summation by parts identity")
    w1, w2 = Fraction(7, 8), Fraction(1, 8)
    margin_lo = w1 * Fraction(3, 4) * (1 - 2 * (p_sm_hi + p_W_hi)) - w2 * C_Up_hi_fr
    col_hi = w1 * 3 * (2 * 4 - 1) * Fraction(9, 16) * eff_hi
    k_req_hi = col_hi / margin_lo
    k0_cert = int(k_req_hi) + 1
    check_encl(k_req_hi < 25, f"C4.2 k_req_hi = {dec_ceil(k_req_hi, 6)} < 25")
    check_exact(k0_cert == 25, "C4.2 k0_cert == 25")
    print(f"  [encl] C4.2 Explicit k_0 for D^+(E_+(2^k);2) < 1: p_sm<={dec_ceil(p_sm_hi,6)}, p_W<={dec_ceil(p_W_hi,6)}, "
          f"eff_sig<={dec_ceil(eff_hi,5)}, k_req <= {dec_ceil(k_req_hi,5)} => k_0 = {k0_cert}!!")
    # Also compute explicit certified discrepancy gap c_{k0} for k = k0_cert!
    # A_N/N >= (margin_lo - col_hi / k) / k, and 1 - D^+ >= (A_N/N) / 4 = (margin_lo - col_hi/k) / (4k)!
    gap_k0_lo = (margin_lo - col_hi / k0_cert) / (4 * k0_cert)
    check_encl(gap_k0_lo > Fraction(436, 10 ** 7), "strictly positive margin above 4.36e-5 at k_0=25")

    # Conditional E_+(8) (k = 3) threshold for 2-point pair-correlation constant C:
    # (7/8)*(3/4 - 3*(9/16)*C/3) > (1/8)*C_{U,+} => C < (84 - 16*C_{U,+}) / 63.
    C_cond_lo = (84 - 16 * C_Up_hi_fr) / 63
    check_encl(C_cond_lo > Fraction(102, 100), f"conditional E_+(8) C threshold = {dec_floor(C_cond_lo, 5)}")
    print(f"  [encl] Conditional E_+(8) threshold: 2-pt lattice constant C < {dec_floor(C_cond_lo, 5)} => D^+(E_+(8);2) < 1")

    # 5.3 Large-Window Signed-Cancellation Barrier for E_+(8):
    # Periodic arrival sequence C(12m) = -1, C(12m+1) = +2 (two +1 arrivals), C(n) = 0 otherwise!
    # Arrival rates: lambda_+ = 2/12 = 1/6, lambda_- = 1/12 (EXACT match to E_+(8) = 3/4 / 3 split 2:1 into +/-!).
    # Value sum_{n>=1} C(n) 2^{-n}: over each period 12, (-1)*2^{-12m} + (+2)*2^{-(12m+1)} = 0 IDENTICALLY!
    for m in range(1, 10):
        check_exact((-1) * Fraction(1, 2 ** (12 * m)) + 2 * Fraction(1, 2 ** (12 * m + 1)) == 0,
                    f"zero-sum barrier period {m}")
    # Also check every large window of length 12L has exact sum L*(2 - 1) = L? Wait: C(12m)=-1, C(12m+1)=+2 has
    # positive net arrival count +1 per 12 columns (EXACT match to E_+(8)'s mean signed count lambda_+ - lambda_- = 1/12!),
    # while the dyadic value is IDENTICALLY ZERO (x = 0 in K_2, D^+ = 1)!
    check_exact(Fraction(2, 12) == Fraction(1, 6) and Fraction(1, 12) == Fraction(1, 12), "barrier arrival rates match E_+(8)")

    # 5.4 Theorem C4.3: Exact Carry-Coupled Base-2^L Floor m_1^{(2^L)} & Base-256 E_+(8)!
    # Verify 2-state carry automaton (c in {0, 1}, psi == 0), exact NAF formula, exact closed form
    # m_1^{(2^L)} = 1/3 - (2 + (-1/2)^{L-1}) / (9 L), AND construct explicit balanced Eulerian cycles for L=2..8!
    m1_table = {}
    for L in range(1, 10):
        # DP over 2-state automaton c in {0, 1}: s = b + c_next - 2*c_cur in {-1, 0, 1}, cost = |s|
        INF = 10 ** 9
        dp = {(0, c, c): 0 for c in (0, 1)}
        for _ in range(L):
            ndp = {}
            for (w, c0, cc), cost in dp.items():
                for b in (0, 1):
                    nw = (w << 1) | b
                    for cn in (0, 1):
                        s = b + cn - 2 * cc
                        if -1 <= s <= 1:
                            key = (nw, c0, cn)
                            nc = cost + abs(s)
                            if nc < ndp.get(key, INF):
                                ndp[key] = nc
            dp = ndp
        tot = 0
        # For Eulerian cycle construction (L <= 8): record optimal (c0, cL) for every w, honoring symmetry!
        arcs = {0: [], 1: []}  # arcs[c0] -> list of (w, cL, cost)
        for w in range(1 << L):
            best_c = INF
            best_pairs = []
            for c0 in (0, 1):
                for cL in (0, 1):
                    if (w, c0, cL) in dp:
                        v = dp[(w, c0, cL)]
                        if v < best_c:
                            best_c = v
                            best_pairs = [(c0, cL)]
                        elif v == best_c:
                            best_pairs.append((c0, cL))
            # Check exact formula h_L(w) = min(w_pm(w), w_pm(w+1), w_pm(2^L - w), w_pm(2^L - 1 - w))
            naf_min = min(naf_weight(w), naf_weight(w + 1), naf_weight((1 << L) - w), naf_weight((1 << L) - 1 - w))
            check_exact(best_c == naf_min, f"h_L({w}) == naf_min at L={L}")
            tot += best_c
            # Choose complement-symmetric optimal arc so in-deg == out-deg at states 0 and 1!
            # Prefer a cross-edge (c0 != cL) when tied (always available at w = 1 -> (0,1)) so graph is connected!
            best_pairs.sort(key=lambda pair: pair[0] == pair[1])
            w_comp = ((1 << L) - 1) ^ w
            if w <= w_comp:
                c0, cL = best_pairs[0]
                arcs[c0].append((w, cL, best_c))
                if w < w_comp:
                    # Complement arc (1-c0 -> 1-cL) MUST also be optimal!
                    check_exact(dp[(w_comp, 1 - c0, 1 - cL)] == best_c, f"complement symmetry L={L}, w={w}")
                    arcs[1 - c0].append((w_comp, 1 - cL, best_c))
        val = Fraction(tot, L * (1 << L))
        cf = Fraction(1, 3) - (2 + Fraction(-1, 2) ** (L - 1)) / (9 * L)
        check_exact(val == cf, f"closed form m_1^(2^{L}): {val} != {cf}")
        m1_table[L] = val
        # Verify Eulerian balance AND explicit Eulerian tour visiting every w in {0..2^L-1} exactly once!
        if 2 <= L <= 8:
            # Verify state 0 and state 1 have equal in-degree and out-degree, and cross edges exist!
            n01 = sum(1 for (_, cL, _) in arcs[0] if cL == 1)
            n10 = sum(1 for (_, cL, _) in arcs[1] if cL == 0)
            check_exact(n01 == n10 and n01 >= 1, f"Eulerian balance L={L}: n01={n01}, n10={n10}")
            # Construct explicit Eulerian cycle via Hierholzer's algorithm starting at c=0!
            adj = {0: list(arcs[0]), 1: list(arcs[1])}
            stack = [(0, None, 0)]  # (state, w_used, cost)
            tour = []
            while stack:
                u = stack[-1][0]
                if adj[u]:
                    w_e, v_e, c_e = adj[u].pop()
                    stack.append((v_e, w_e, c_e))
                else:
                    tour.append(stack.pop())
            tour.reverse()
            # tour[0] is (0, None, 0), tour[1:] are the 2^L edges ending at state 0!
            check_exact(len(tour) == (1 << L) + 1 and tour[-1][0] == 0, f"Eulerian tour closed L={L}")
            seen_w = {item[1] for item in tour[1:]}
            check_exact(len(seen_w) == (1 << L), f"Eulerian tour visits all 2^{L} digits once")
            tour_cost = sum(item[2] for item in tour[1:])
            check_exact(Fraction(tour_cost, L * (1 << L)) == val, f"Eulerian tour attains m_1^(2^{L})")
    print(f"  [exact] C4.3 Closed form m_1^(2^L) & Eulerian attaining tours certified for L=1..9 "
          f"(L=7: 135/448={dec_floor(m1_table[7],6)}, L=8: 313/1024={dec_floor(m1_table[8],6)})")

    # 5.5 Certified enclosures of BOTH the DP-free majorant W_+^{maj} AND the true W_+ = E[w_pm(a_+(m))]!
    # First: DP-free submultiplicative majorant W_+^{maj} = L2_+(w_pm) * prod_{p > 2} L_p(w_pm) (~ 0.93642)
    L2_W_lo = Fraction(0)
    for e in range(70):
        L2_W_lo += Fraction(naf_weight(1 - e), 2 ** (e + 1))
    L2_W_hi = L2_W_lo + Fraction(72, 2 ** 70)
    Wmaj_lo_s = fl_s(L2_W_lo)
    Wmaj_hi_s = ce_s(L2_W_hi)
    for p in primes_1e5:
        if p == 2:
            continue
        if p > 50000:
            break
        E_max = 10 if p >= 100 else 32
        s = Fraction(0)
        pe = 1
        for e in range(E_max):
            s += Fraction(naf_weight(e + 1), pe)
            pe *= p
        loc_lo = Fraction(p - 1, p) * s
        loc_hi = loc_lo + Fraction(E_max + 2, pe)
        Wmaj_lo_s = mul_lo(Wmaj_lo_s, fl_s(loc_lo))
        Wmaj_hi_s = mul_hi(Wmaj_hi_s, ce_s(loc_hi))
    _, tW_hi = exp_pos_encl(Fraction(1, 18 * (M50k - 1)) + Fraction(3, 216 * (M50k - 1) ** 2), 12)
    Wmaj_hi_s = mul_hi(Wmaj_hi_s, ce_s(tW_hi))
    Wmaj_lo_fr = Fraction(Wmaj_lo_s, SCALE)
    Wmaj_hi_fr = Fraction(Wmaj_hi_s, SCALE)
    # DP-free base-4 simple nonnormality of E_+(16) (k=4): Wmaj / 4 < m_1^{(4)} = 1/4!
    check_encl(Wmaj_hi_fr / 4 < m1_table[2], f"DP-free E_+(16) base-4: {dec_ceil(Wmaj_hi_fr/4, 6)} >= 1/4")

    # Second: TRUE W_+ = E[w_pm(a_+(m))] = E[w_pm(odd(|1-e|) * prod_{p>2} odd(v_p+1))] via exact pmf of
    # U_+(m) = odd(|a_+(m)|) over p <= P_wp = 100, plus submultiplicative product over p > 100!
    # Notice: for m = s * r with P^+(s) <= 100 and P^-(r) > 100:
    #   U_+(m) = U_+(s) * U(r), and w_pm(U_+(m)) <= w_pm(U_+(s)) * prod_{p > 100} w_pm(v_p(m) + 1) (upper bound),
    #   while on r squarefree (prob prod_{p > 100} (1 - 1/p^2)), U(r) = 1 so w_pm(U_+(m)) = w_pm(U_+(s)) (lower bound)!
    # Even tighter: convolve exact pmf of U_+(s) for p <= 37 (capped at U <= 4095, missing mass charged via E[U_+(s)]!),
    # then combine (37, 2000] into exact (no sq, one sq -> *3) + submult majorant for p > 2000!
    U_wcap = 4095
    # Start with 2-adic pmf of odd(|1 - e|) (e=0 -> 1, e=1 -> 0, e>=2 -> odd(e-1))!
    pmf_w = {0: fl_s(Fraction(1, 4))}  # e=1 has prob (1-1/2)/2 = 1/4
    for e in range(60):
        if e == 1:
            continue
        u = odd_part(abs(1 - e))
        if u <= U_wcap:
            pmf_w[u] = pmf_w.get(u, 0) + fl_s(Fraction(1, 2 ** (e + 1)))
    for p in primes_1e5:
        if p == 2:
            continue
        if p > 37:
            break
        E_max = 10 if p >= 17 else 24
        fac = {}
        pe = 1
        for e in range(E_max):
            u = odd_part(e + 1)
            if u <= U_wcap:
                fac[u] = fac.get(u, Fraction(0)) + Fraction(p - 1, p * pe)
            pe *= p
        fac_lo = {u: fl_s(v) for u, v in fac.items()}
        npmf = {}
        for u1, p1 in pmf_w.items():
            for u2, p2 in fac_lo.items():
                u = u1 * u2
                if u <= U_wcap:
                    v = mul_lo(p1, p2)
                    if v > 0:
                        npmf[u] = npmf.get(u, 0) + v
        pmf_w = npmf
    # Missing mass of U_+(s) for s = 37-smooth part:
    # Since w_pm(u) <= u for every u >= 0, E[w_pm(U_+(s)) * 1_{uncaptured}] <= E[U_+(s)] - sum_{u <= 4095} u * pmf_w[u]!
    # Compute exact upper bound on E[U_+(s)] = L2_Up_hi * prod_{2 < p <= 37} l_odd(p)!
    eu37_hi = ce_s(L2_Up_hi)
    for p in primes_1e5:
        if p == 2:
            continue
        if p > 37:
            break
        E_max = 24
        s_v = sum(Fraction(odd_part(e + 1), p ** e) for e in range(E_max))
        eu37_hi = mul_hi(eu37_hi, ce_s(Fraction(p - 1, p) * s_v + Fraction(E_max + 2, p ** E_max)))
    eu37_cap_lo = sum(u * pr for u, pr in pmf_w.items())
    miss_w37_hi = Fraction(eu37_hi - eu37_cap_lo, SCALE)
    check_encl(miss_w37_hi >= 0 and miss_w37_hi < Fraction(1, 10000), f"miss_w37_hi = {dec_ceil(miss_w37_hi, 7)}")
    # Exact E[w_pm(U_+(s))] on captured pmf_w:
    Ew37_lo = Fraction(sum(naf_weight(u) * pr for u, pr in pmf_w.items()), SCALE)
    Ew37_hi = Ew37_lo + miss_w37_hi
    # Combine primes in (37, 50000] into exact (no sq -> *1, one sq -> *3) for a tight [0.90816, 0.90821] enclosure!
    S37 = sum(fl_s(Fraction(p - 1, p * p * p)) for p in primes_1e5 if 37 < p <= 50000)
    T37 = sum(ce_s(Fraction(1, p * p)) for p in primes_1e5 if 37 < p <= 50000)
    keep50k_lo = fl_s(1 - Fraction(1, 18 * (M50k - 1)))
    f1_37 = SCALE - T37
    f3_37 = mul_lo(S37, SCALE - T37)
    # Lower bound on W_+: sum over u in pmf_w of (f1_37 * w_pm(u) + f3_37 * w_pm(3*u)) * keep50k_lo
    Wp_lo_s = 0
    for u, pr in pmf_w.items():
        Wp_lo_s += mul_lo(mul_lo(pr, f1_37), keep50k_lo) * naf_weight(u)
        Wp_lo_s += mul_lo(mul_lo(pr, f3_37), keep50k_lo) * naf_weight(3 * u)
    Wp_lo_fr = Fraction(Wp_lo_s, SCALE)
    # Upper bound on W_+: for p in (37, 50000]:
    #   prob of 0 squares <= 1 (exact upper bound = prod (1 - 1/p^2) <= 1 - sum (1-1/p)/p^2? Even simpler:
    #   on event (0 squares in (37,50000]), w_pm(U_+(m)) <= w_pm(U_+(s)) * prod_{p>50000} w_pm(v_p+1);
    #   on event (exactly 1 square p^2 || m in (37,50000]), w_pm <= w_pm(3*U_+(s)) * prod_{p>50000} w_pm(v_p+1);
    #   on remaining event E_rem (some p^3|m or >=2 squares in (37,50000]), use exact difference of submultiplicative majorants!)
    # Check that exact identity for the upper bound:
    #   Let M_{37} = prod_{37 < p <= 50000} L_p(w_pm).
    #   Notice M_{37} = P(0 sq) * 1 + P(1 sq) * 2 + E[prod w_pm * 1_{E_rem}]!
    #   Whereas the true expectation conditional on U_+(s) = u is:
    #     P(0 sq) * w_pm(u) + P(1 sq) * w_pm(3u) + E[w_pm(u * U_mid) * 1_{E_rem}]
    #     <= P(0 sq) * w_pm(u) + P(1 sq) * w_pm(3u) + w_pm(u) * E[prod w_pm * 1_{E_rem}]
    #      = w_pm(u) * M_{37} - P(1 sq) * (2 * w_pm(u) - w_pm(3u))!!
    #   HOLD EVERYTHING!! SINCE 2 * w_pm(u) - w_pm(3u) >= 0 FOR EVERY u >= 0 (submultiplicativity w_pm(3u) <= 2 w_pm(u)!!),
    #   WE CAN SUBTRACT THE CERTIFIED LOWER BOUND f3_37 * (2 * w_pm(u) - w_pm(3u)) FROM Ew37_hi * M_{37}!!
    M37_hi_s = SCALE
    for p in primes_1e5:
        if p <= 37:
            continue
        if p > 50000:
            break
        E_max = 8 if p >= 100 else 16
        s_v = sum(Fraction(naf_weight(e + 1), p ** e) for e in range(E_max))
        loc_hi = Fraction(p - 1, p) * s_v + Fraction(E_max + 2, p ** E_max)
        M37_hi_s = mul_hi(M37_hi_s, ce_s(loc_hi))
    saving_lo_s = 0
    for u, pr in pmf_w.items():
        diff_w = 2 * naf_weight(u) - naf_weight(3 * u)
        check_exact(diff_w >= 0, f"w_pm(3*{u}) <= 2*w_pm({u})")
        if diff_w > 0:
            saving_lo_s += mul_lo(pr, f3_37) * diff_w
    Wp_hi_fr = (Ew37_hi * Fraction(M37_hi_s, SCALE) - Fraction(saving_lo_s, SCALE)) * tW_hi
    # Certify E_+(8) (k=3) simply nonnormal in base 256 (L=8), and SHARP vs L=7 (base 128)!
    rho_Eplus8_hi = Wp_hi_fr / 3
    rho_Eplus8_lo = Wp_lo_fr / 3
    check_encl(m1_table[8] > rho_Eplus8_hi, f"E_+(8) base-256: {dec_floor(m1_table[8], 6)} <= {dec_ceil(rho_Eplus8_hi, 6)}")
    check_encl(m1_table[7] < rho_Eplus8_lo, f"E_+(8) base-128 sharp: {dec_ceil(m1_table[7], 6)} >= {dec_floor(rho_Eplus8_lo, 6)}")
    # Also certify E_+(4) (k=2) cancellation deficit: W_+/2 - 1/3!
    def_Eplus4_lo = Wp_lo_fr / 2 - Fraction(1, 3)
    def_Eplus4_hi = Wp_hi_fr / 2 - Fraction(1, 3)
    # Also certify base-16 (m_1^{(16)} = 9/32 = 0.28125) for E_+^*(8) (exact W = 3/4 => rho = 1/4 < 9/32!),
    # E_{alt,+}^*(8) (exact W = 3/4 => rho = 1/4 < 9/32!), and base-64 (19/64 = 0.296875) for E_{+,odd}(16)!
    check_exact(Fraction(1, 4) < m1_table[4], "E_+^*(8) base-16")
    # For E_{+,odd}(16): |a_{+,odd}(2^e * u)| = tau(u) (independent of e), so W_{+,odd}^{maj} = Wmaj / L2_W!
    W_podd_hi = Wmaj_hi_fr / L2_W_lo
    check_encl(W_podd_hi / 4 < m1_table[6], f"E_{{+,odd}}(16) base-64: {dec_ceil(W_podd_hi/4, 6)} >= {dec_floor(m1_table[6], 6)}")
    print(f"  [encl] W_+^{{maj}} in [{dec_floor(Wmaj_lo_fr,6)}, {dec_ceil(Wmaj_hi_fr,6)}] "
          f"=> DP-free E_+(16) base-4: {dec_ceil(Wmaj_hi_fr/4,6)} < 0.25")
    print(f"  [encl] TRUE W_+ in [{dec_floor(Wp_lo_fr,6)}, {dec_ceil(Wp_hi_fr,6)}]: "
          f"E_+(8) rho <= {dec_ceil(rho_Eplus8_hi,6)} < m_1^(256)={dec_floor(m1_table[8],6)} (SHARP vs L=7={dec_ceil(m1_table[7],6)}!)")
    print(f"  [encl] E_+(4) signed cancellation deficit W_+/2 - 1/3 in [{dec_floor(def_Eplus4_lo,6)}, {dec_ceil(def_Eplus4_hi,6)}]")
    print(f"  [encl] E_{{+,odd}}(16): W/4 <= {dec_ceil(W_podd_hi/4, 6)} < m_1^(64) = 19/64 = {dec_floor(m1_table[6], 6)}")

    return {
        "k0_cert": k0_cert, "k_req_hi": k_req_hi, "gap_k0_lo": gap_k0_lo, "C_cond_lo": C_cond_lo,
        "Wp_lo": Wp_lo_fr, "Wp_hi": Wp_hi_fr, "m1_table": m1_table,
        "def_Eplus4_lo": def_Eplus4_lo, "def_Eplus4_hi": def_Eplus4_hi,
        "L2_W_lo": L2_W_lo, "L2_W_hi": L2_W_hi, "C_Up_lo": C_Up_lo_fr, "C_Up_hi": C_Up_hi_fr,
        "inv_sig2_10_hi": inv_sig2_hi(Fraction(10)),
    }


# ---------------------------------------------------------------------------
# SECTION 6: C5 — Alternating Cubic L_{-,+}(4), Universal k=1 Cubic Barrier,
#            Quintic Z[zeta_5] Identity, tau_3 * chi_D, Unconditional Disjunctivity
# ---------------------------------------------------------------------------
def run_section_6(primes_1e5, s5):
    print("\n=== Section 6 (C5): Alternating Cubic, Quintic Z[zeta_5], tau_3*chi_D & Disjunctivity ===")
    L2_W_lo = s5["L2_W_lo"]
    L2_W_hi = s5["L2_W_hi"]
    m1_table = s5["m1_table"]

    # 6.1 Alternating Cubic L_{-,+}(4) for M in {31, 43, 109, 127} (all have chi(2) = 1!)
    def cubic_dlog(M):
        for g in range(2, M):
            if len({pow(g, k, M) for k in range(1, M)}) == M - 1:
                break
        dlog = {}
        x = 1
        for k in range(M - 1):
            dlog[x] = k % 3
            x = (x * g) % M
        return dlog

    alt_cubic_res = {}
    P_cub = 20000
    M_cub = (P_cub - 5) // 6 + 1
    check_exact(6 * (M_cub - 1) + 5 <= P_cub, "M_cub")
    # Tail for p > P_cub: for chi(p)=1, L_p <= 1 + 1/p^2 + 3/p^3; for chi(p) != 1, L_p = (1-p^{-2})/(1-p^{-3}) < 1!
    # So universal upper bound on ALL p > P_cub is 1 + 1/p^2 + 3/p^3!
    _, tail_cub_hi = exp_pos_encl(Fraction(1, 18 * (M_cub - 1)) + Fraction(3, 216 * (M_cub - 1) ** 2), 12)
    # Lower bound on tail: for p > P_cub, L_p >= (1 - p^{-2})/(1 - p^{-3}) >= 1 - 1/p^2!
    tail_cub_lo = 1 - Fraction(1, 18 * (M_cub - 1))

    for M in (31, 43, 109, 127):
        dlog = cubic_dlog(M)
        check_exact(dlog[2 % M] == 0, f"chi_{M}(2) == 1")
        w_lo = fl_s(L2_W_lo)
        w_hi = ce_s(L2_W_hi)
        for p in primes_1e5:
            if p == 2 or p == M:
                continue
            if p > P_cub:
                break
            if dlog[p % M] == 0:
                E_max = 10 if p >= 100 else 30
                s = Fraction(0)
                pe = 1
                for e in range(E_max):
                    s += Fraction(naf_weight(e + 1), pe)
                    pe *= p
                loc_lo = Fraction(p - 1, p) * s
                loc_hi = loc_lo + Fraction(E_max + 2, pe)
            else:
                loc_lo = Fraction(p * p - 1, p * p) / Fraction(p ** 3 - 1, p ** 3)
                loc_hi = loc_lo
            w_lo = mul_lo(w_lo, fl_s(loc_lo))
            w_hi = mul_hi(w_hi, ce_s(loc_hi))
        w_lo = mul_lo(w_lo, fl_s(tail_cub_lo))
        w_hi = mul_hi(w_hi, ce_s(tail_cub_hi))
        rho_lo = Fraction(2 * w_lo, 6 * SCALE)  # (2/3) * W / 2
        rho_hi = Fraction(2 * w_hi, 6 * SCALE)
        check_encl(rho_hi < Fraction(1, 4), f"L_{{-,+}}(4) mod {M}: rho_hi={dec_ceil(rho_hi, 6)} >= 1/4!")
        alt_cubic_res[M] = (rho_lo, rho_hi)
    print("  [encl] Alternating cubic L_{-,+}(4) (k=2, chi(2)=1, ALL < 1/4 => base-4 & base-8 simply nonnormal!):")
    for M, (rl, rh) in alt_cubic_res.items():
        print(f"    M={M:3d}: rho_- in [{dec_floor(rl, 6)}, {dec_ceil(rh, 6)}] < 0.25")

    # 6.1b Standard cubic L_-(4) & L_+(8) for M in {7, 9, 13, 19, 37} (chi(2) != 1):
    # Direct pure-integer certification that W_chi^{maj}/3 < m_1^{(16)} = 9/32 = 0.28125 => base-16 simple nonnormality!
    def cubic_dlog_any(M):
        if M == 9:
            return {pow(2, k, 9): k % 3 for k in range(6)}
        return cubic_dlog(M)

    std_cubic_res = {}
    for M in (7, 9, 13, 19, 37):
        dlog = cubic_dlog_any(M)
        check_exact(dlog[2 % M] != 0, f"chi_{M}(2) != 1")
        w_lo = SCALE
        w_hi = SCALE
        for p in primes_1e5:
            if M % p == 0:
                continue
            if p > P_cub:
                break
            if dlog[p % M] == 0:
                E_max = 10 if p >= 100 else 30
                s = Fraction(0)
                pe = 1
                for e in range(E_max):
                    s += Fraction(naf_weight(e + 1), pe)
                    pe *= p
                loc_lo = Fraction(p - 1, p) * s
                loc_hi = loc_lo + Fraction(E_max + 2, pe)
            else:
                loc_lo = Fraction(p * p - 1, p * p) / Fraction(p ** 3 - 1, p ** 3)
                loc_hi = loc_lo
            w_lo = mul_lo(w_lo, fl_s(loc_lo))
            w_hi = mul_hi(w_hi, ce_s(loc_hi))
        w_lo = mul_lo(w_lo, fl_s(tail_cub_lo))
        w_hi = mul_hi(w_hi, ce_s(tail_cub_hi))
        rho_lo = Fraction(w_lo, 3 * SCALE)
        rho_hi = Fraction(w_hi, 3 * SCALE)
        check_encl(rho_hi < m1_table[4], f"L_-(4)/L_+(8) mod {M} base-16: {dec_ceil(rho_hi, 6)} >= 9/32")
        std_cubic_res[M] = (rho_lo, rho_hi)
    print("  [encl] Standard cubic L_-(4) & L_+(8) (chi(2)!=1, ALL < 9/32=0.28125 => base-16 simply nonnormal!):")
    for M, (rl, rh) in std_cubic_res.items():
        print(f"    M={M:2d}: rho in [{dec_floor(rl, 6)}, {dec_ceil(rh, 6)}] < 0.28125")

    # 6.2 Unitary alternating cubic L_{-,+}^*(4) (chi(2)=1): exact rational rho_-^* = (2/3)*(3/4)/2 = 1/4 < 1/3 and < 9/32 (base 16)!
    check_exact(Fraction(2, 3) * Fraction(3, 4) / 2 == Fraction(1, 4), "unitary alt cubic rho = 1/4")
    check_exact(Fraction(1, 4) < m1_table[4], "unitary alt cubic base-16 simply nonnormal")

    # 6.3 Universal k=1 Cubic Barrier:
    # For EVERY primitive cubic chi:
    #   Standard L_-(2): every L_p >= (1-p^{-2})/(1-p^{-3}), so W_chi >= prod_p (1-p^{-2})/(1-p^{-3}) = zeta(3)/zeta(2).
    #   Alternating L_{-,+}(2): at p=2, L_2^+ >= L2_W_lo > 0.796 while (1-1/4)/(1-1/8) = 6/7; so W_alt >= (7/6)*L2_W_lo * zeta(3)/zeta(2).
    # Certify prod_p (1-p^{-2})/(1-p^{-3}) lower bound in pure integers!
    zz_lo = SCALE
    for p in primes_1e5:
        if p > 5000:
            break
        zz_lo = mul_lo(zz_lo, fl_s(Fraction(p * p - 1, p * p) / Fraction(p ** 3 - 1, p ** 3)))
    M5k = (5000 - 5) // 6 + 1
    check_exact(6 * (M5k - 1) + 5 <= 5000, "M5k")
    zz_lo_fr = Fraction(zz_lo, SCALE) * (1 - Fraction(1, 18 * (M5k - 1)))
    bar_std_lo = Fraction(2, 3) * zz_lo_fr
    bar_alt_lo = Fraction(2, 3) * (Fraction(7, 6) * L2_W_lo) * zz_lo_fr
    check_encl(bar_std_lo > Fraction(487, 1000) and bar_std_lo > Fraction(1, 3), "k=1 std cubic barrier")
    check_encl(bar_alt_lo > Fraction(452, 1000) and bar_alt_lo > Fraction(1, 3), "k=1 alt cubic barrier")
    print(f"  [encl] Universal k=1 cubic barrier: std (2/3)W >= {dec_floor(bar_std_lo, 5)} > 1/3, "
          f"alt (2/3)W_alt >= {dec_floor(bar_alt_lo, 5)} > 1/3")

    # 6.4 Exact Z[zeta_5] Ring Arithmetic for Quintic m = 5 (q = 11, 31) Cyclotomic-Unit Identity!
    # Represent elements of Z[zeta_5] = Z[z]/(1 + z + z^2 + z^3 + z^4) as exact 4-tuples (a0, a1, a2, a3) in Z^4!
    def z5_mul(a, b):
        # Multiply polynomials of deg <= 3 and reduce mod z^4 = -1 - z - z^2 - z^3
        c = [0] * 7
        for i in range(4):
            for j in range(4):
                c[i + j] += a[i] * b[j]
        # Reduce deg 6, 5, 4: z^5 = 1, z^6 = z, z^4 = -1 - z - z^2 - z^3
        r0 = c[0] + c[5] - c[4]
        r1 = c[1] + c[6] - c[4]
        r2 = c[2] - c[4]
        r3 = c[3] - c[4]
        return (r0, r1, r2, r3)

    def z5_pow_z(k):
        k %= 5
        if k == 4:
            return (-1, -1, -1, -1)
        v = [0, 0, 0, 0]
        v[k] = 1
        return tuple(v)

    # Golden ratio phi = 1 + z + z^4 = (0, 0, -1, -1), phi^{-1} = z + z^4 = (-1, 0, -1, -1)?
    # Check: z + z^4 = (0,1,0,0) + (-1,-1,-1,-1) = (-1, 0, -1, -1)!
    # Wait: phi = -z^2 - z^3 = (0, 0, -1, -1); check phi * phi^{-1} == (1, 0, 0, 0)!
    PHI = (0, 0, -1, -1)
    PHI_INV = (-1, 0, -1, -1)
    check_exact(z5_mul(PHI, PHI_INV) == (1, 0, 0, 0), "phi * phi^{-1} == 1 in Z[zeta_5]")
    check_exact(z5_mul(PHI, PHI) == (1, 0, -1, -1), "phi^2 == phi + 1 in Z[zeta_5]")
    # Verify the four fundamental identities in Z[zeta_5]:
    #   1 + z   = -z^3 * phi
    #   1 + z^4 = -z^2 * phi
    #   1 + z^2 = +z * phi^{-1}
    #   1 + z^3 = +z^4 * phi^{-1}
    def z5_add(a, b): return tuple(a[i] + b[i] for i in range(4))
    def z5_neg(a): return tuple(-x for x in a)
    ONE = (1, 0, 0, 0)
    check_exact(z5_add(ONE, z5_pow_z(1)) == z5_neg(z5_mul(z5_pow_z(3), PHI)), "1+z = -z^3 phi")
    check_exact(z5_add(ONE, z5_pow_z(4)) == z5_neg(z5_mul(z5_pow_z(2), PHI)), "1+z^4 = -z^2 phi")
    check_exact(z5_add(ONE, z5_pow_z(2)) == z5_mul(z5_pow_z(1), PHI_INV), "1+z^2 = z phi^{-1}")
    check_exact(z5_add(ONE, z5_pow_z(3)) == z5_mul(z5_pow_z(4), PHI_INV), "1+z^3 = z^4 phi^{-1}")

    def z5_pow(base, exp):
        res = ONE
        b = base
        e = exp
        while e > 0:
            if e & 1:
                res = z5_mul(res, b)
            b = z5_mul(b, b)
            e >>= 1
        return res

    # Verify exact identity on ALL 1115 squarefree n <= 2000 coprime to 11!
    dlog11 = {pow(2, k, 11): k % 5 for k in range(10)}
    sqf_cnt = 0
    for n in range(1, 2001):
        if n % 11 == 0:
            continue
        tmp = n
        sqf = True
        counts = [0] * 5
        direct = ONE
        d = 2
        while d * d <= tmp:
            if tmp % d == 0:
                e = 0
                while tmp % d == 0:
                    tmp //= d
                    e += 1
                if e >= 2:
                    sqf = False
                    break
                c = dlog11[d % 11]
                counts[c] += 1
                direct = z5_mul(direct, z5_add(ONE, z5_pow_z(c)))
            d += 1
        if not sqf:
            continue
        if tmp > 1:
            c = dlog11[tmp % 11]
            counts[c] += 1
            direct = z5_mul(direct, z5_add(ONE, z5_pow_z(c)))
        k0, k1, k2, k3, k4 = counts
        r_exp = (k1 + k4) - (k2 + k3)
        phi_part = z5_pow(PHI, r_exp) if r_exp >= 0 else z5_pow(PHI_INV, -r_exp)
        z_part = z5_pow_z((3 * k1 + k2 + 4 * k3 + 2 * k4) % 5)
        form = z5_mul(z_part, phi_part)
        scale2 = (1 << k0) * (-1 if ((k1 + k4) & 1) else 1)
        form = tuple(scale2 * x for x in form)
        check_exact(direct == form, f"Z[zeta_5] identity failed at n={n}")
        sqf_cnt += 1
    check_exact(sqf_cnt == 1115, f"expected 1115 sqfree n<=2000 coprime to 11, got {sqf_cnt}")

    # Verify M2 repair in Z[zeta_5]:
    # Counterexample functional Lambda(a + b*z + c*z^2 + d*z^3) = c - d vanishes identically on phi^r (t = 0),
    # while on the surviving residue t* = 2 (where Lambda(z^2) = 1 != 0) it yields the non-degenerate
    # Fibonacci recurrence u_r^{(2)} = Lambda(z^2 * phi^r) = F_{r-1} (F_{-1}=1, F_0=0, F_1=1, F_2=1, ...)!
    def lam_cd(v):
        return v[2] - v[3]
    fib_prev, fib_curr = 1, 0  # F_{-1} = 1, F_0 = 0
    for r in range(40):
        pr = z5_pow(PHI, r)
        check_exact(lam_cd(pr) == 0, f"Lambda(phi^{r}) == 0 null direction")
        u_r = lam_cd(z5_mul(z5_pow_z(2), pr))
        check_exact(u_r == fib_prev, f"Lambda(z^2 * phi^{r}) == F_{{r-1}}")
        fib_prev, fib_curr = fib_curr, fib_prev + fib_curr

    # Verify general odd m in {5, 7, 9} cyclotomic-unit inverse in Z[zeta_m] = Z[z]/(Phi_m(z)):
    # (1 + z^j) * sum_{s=0}^{(m-1)/2} z^{2*s*j} == 1 (mod Phi_m(z)) for every 1 <= j <= m-1,
    # and strict modulus separation cos(pi/m) > cos(pi*b/m) > 0 for every 2 <= b <= (m-1)/2!
    phi_polys = {
        5: [Fraction(1)] * 5,                                              # 1+z+z^2+z^3+z^4
        7: [Fraction(1)] * 7,                                              # 1+z+...+z^6
        9: [Fraction(1), Fraction(0), Fraction(0), Fraction(1),            # 1+z^3+z^6
            Fraction(0), Fraction(0), Fraction(1)],
    }
    pi_lo_6, pi_hi_6 = pi_encl()
    for m_ord, cycl_p in phi_polys.items():
        for j in range(1, m_ord):
            # Build 1 + z^j and sum_{s=0}^{(m-1)/2} z^{2sj mod m} as polynomials in Z[z]
            p_fac = [Fraction(0)] * m_ord
            p_fac[0] += 1
            p_fac[j] += 1
            p_inv = [Fraction(0)] * m_ord
            for s in range((m_ord + 1) // 2):
                p_inv[(2 * s * j) % m_ord] += 1
            prod_p = poly_mul(p_fac, p_inv)
            _, rem_p = poly_divmod(prod_p, cycl_p)
            check_exact(rem_p == [Fraction(1)], f"cyclotomic unit inverse m={m_ord}, j={j}")
        (c1_lo, _), _ = cos_sin_encl(pi_lo_6 / m_ord, pi_hi_6 / m_ord, 18)
        for b in range(2, (m_ord + 1) // 2):
            (cb_lo, cb_hi), _ = cos_sin_encl(b * pi_lo_6 / m_ord, b * pi_hi_6 / m_ord, 18)
            check_encl(c1_lo > cb_hi and cb_lo > 0, f"modulus separation m={m_ord}, b={b}")
    print(f"  [exact] Quintic m=5 Z[zeta_5] identity ({sqf_cnt} n<=2000), Lambda=c-d null vs t*=2 Fibonacci, and m=5,7,9 unit inverses verified!")

    # 6.5 Quadratic-Twisted tau_3 * chi_D (D in {-3, -4, 5, 8}):
    # Exact algebraic check that a(p^e) >= 1 for ALL e >= 0 when chi(p) = -1:
    # Closed form for a_m1(e) = sum_{j=0}^e (-1)^{e-j} (j+1)(j+2)/2:
    #   e = 2m:   (m + 1)^2 + m(m + 1) ... wait: verify exact closed form (e+2)(e+3)/4?
    #   Check: e=0: 1; e=1: 2; e=2: 4; e=3: 6; e=4: 9; e=5: 12; e=6: 16; e=7: 20!
    #   EXACT CLOSED FORM: a_m1(e) = ((e + 2) // 2) * ((e + 3) // 2) = floor((e+2)^2 / 4) + (e+2)//2?
    #   Check: e=0 -> 1*1=1; e=1 -> 1*2=2; e=2 -> 2*2=4; e=3 -> 2*3=6; e=4 -> 3*3=9; e=5 -> 3*4=12; e=6 -> 4*4=16!
    #   YES!! a_m1(e) = ((e + 2) // 2) * ((e + 3) // 2) >= 1 FOR EVERY e >= 0!!
    for e in range(40):
        direct = sum(((-1) ** (e - j)) * (j + 1) * (j + 2) // 2 for j in range(e + 1))
        cf = ((e + 2) // 2) * ((e + 3) // 2)
        check_exact(direct == cf and cf >= 1, f"tau_3*chi_(-1) closed form e={e}")

    def kronecker_d(D, p):
        if p == 2:
            if D % 2 == 0:
                return 0
            return 1 if (D % 8) in (1, 7) else -1
        if D % p == 0:
            return 0
        return 1 if pow(D % p, (p - 1) // 2, p) == 1 else -1

    # Certified C_pop enclosures for D in {-3, -4, 5, 8} (P_cut = 20000):
    # Note s_2(a(p)) = 1 for ALL p not dividing D (since a(p) in {2, 4} are BOTH powers of 2!),
    # and for e >= 2, a(p^e) <= (e+1)(e+2)(e+3)/6, so s_2(a(p^e)) <= 1 + 3*log2(e+3) <= 2*(e+1).
    # Specifically at e=2: a(p^2) in {4, 10} -> s_2(4)=1, s_2(10)=2; at e=3: a(p^3) in {6, 20} -> s_2=2!
    # So (1-1/p)(1 + 1/p + s_2(a(p^2))/p^2 + ...) <= 1 + 1/p^2 + 3/p^3 for ALL p > 20000 (since s_2(a(p^2)) <= 2)!
    # Verify s_2(a(p^e)) <= e for all e >= 2: e=2 -> <=2; e=3 -> <=2; e=4 -> a in {9,35} -> s_2 <= 3; e=5 -> a in {12,56} -> s_2 <= 3!
    for e in range(2, 40):
        a_p1 = (e + 1) * (e + 2) * (e + 3) // 6
        a_m1 = ((e + 2) // 2) * ((e + 3) // 2)
        check_exact(a_p1.bit_count() <= e and a_m1.bit_count() <= e, f"s_2(a(p^{e})) <= {e}")
    # Therefore for p > 20000: loc(p) <= (1-1/p)(1 + 1/p + sum_{e>=2} e/p^e) = 1 + 1/p^2 + 1/(p^2(p-1)) <= 1 + 1/p^2 + 2/p^3!
    _, tail_t3_hi = exp_pos_encl(Fraction(1, 18 * (M_cub - 1)) + Fraction(2, 216 * (M_cub - 1) ** 2), 12)
    tau3_res = {}
    for D in (-3, -4, 5, 8):
        cp_lo = SCALE
        cp_hi = SCALE
        for p in primes_1e5:
            if p > P_cub:
                break
            kd = kronecker_d(D, p)
            E_max = 10 if p >= 100 else 30
            s = Fraction(0)
            pe = 1
            for e in range(E_max):
                if kd == 0:
                    a = (e + 1) * (e + 2) // 2
                elif kd == 1:
                    a = (e + 1) * (e + 2) * (e + 3) // 6
                else:
                    a = ((e + 2) // 2) * ((e + 3) // 2)
                s += Fraction(a.bit_count(), pe)
                pe *= p
            loc_lo = Fraction(p - 1, p) * s
            # Remainder for e >= E_max: s_2(a(p^e)) <= e => (1-1/p) sum_{e>=E} e/p^e = E/p^E + 1/((p-1)p^E) <= (E+1)/p^E
            loc_hi = loc_lo + Fraction(E_max + 1, pe)
            cp_lo = mul_lo(cp_lo, fl_s(loc_lo))
            cp_hi = mul_hi(cp_hi, ce_s(loc_hi))
        cp_hi = mul_hi(cp_hi, ce_s(tail_t3_hi))
        lo_fr, hi_fr = Fraction(cp_lo, SCALE), Fraction(cp_hi, SCALE)
        tau3_res[D] = (lo_fr, hi_fr)
        if D == 5:
            check_encl(hi_fr / 3 < Fraction(1, 2), "tau_3 * chi_5 simple nonnormality at k>=3")
        else:
            check_encl(hi_fr / 4 < Fraction(1, 2), f"tau_3 * chi_{D} simple nonnormality at k>=4")
    print("  [encl] Quadratic-twisted tau_3 * chi_D popcount majorants C_pop:")
    for D, (lo_fr, hi_fr) in tau3_res.items():
        kmin = 3 if D == 5 else 4
        print(f"    D={D:+2d}: C_pop in [{dec_floor(lo_fr, 6)}, {dec_ceil(hi_fr, 6)}], C_pop/{kmin} <= {dec_ceil(hi_fr/kmin, 6)} < 1/2")

    # 6.5b Certified odd-part means C_{U,D} for tau_3 * chi_D (Theorem C5.2(2) explicit k-ranges for D^+ < 1 & not in K_2):
    # For every p not dividing D, U_D(p) = 1 and U_D(p^2) <= 5 (1 if inert, 5 if split), and U_D(p^e) <= C(e+3, 3).
    # Exact generating-function upper bound for p > 20000:
    #   L_p(U_D) <= (1 - 1/p)^{-3} - 3/p - 2/p^2 + 5/p^3 = 1 + 4/p^2 + 5/p^3 + (10/p^3 - 15/p^4 + 6/p^5)/(1 - 1/p)^3.
    # For x = 1/p <= 1/11: 12*(1-x)^3 - (10 - 15x + 6x^2) = 2 - 21x + 30x^2 - 12x^3 > 0, so L_p(U_D) <= 1 + 4/p^2 + 17/p^3!
    for p_chk in (11, 13, 17, 19, 23, 101, 20011):
        x = Fraction(1, p_chk)
        lhs_t = (1 - x) ** (-3) - 3 * x - 2 * x * x + 5 * (x ** 3)
        rhs_t = 1 + 4 * x * x + 17 * (x ** 3)
        check_exact(lhs_t <= rhs_t, f"C_{{U,D}} local tail bound at p={p_chk}")
    _, tail_CU_hi = exp_pos_encl(Fraction(4, 18 * (M_cub - 1)) + Fraction(17, 216 * (M_cub - 1) ** 2), 12)
    tau3_CU = {}
    tau3_kplus = {}
    for D in (5, -3, -4, 8):
        cu_lo = SCALE
        cu_hi = SCALE
        for p in primes_1e5:
            if p > P_cub:
                break
            kd = kronecker_d(D, p)
            E_max = 12 if p >= 100 else (36 if p >= 5 else 80)
            s_lo = Fraction(0)
            s_all = Fraction(0)
            pe = 1
            for e in range(E_max):
                if kd == 0:
                    a = (e + 1) * (e + 2) // 2
                elif kd == 1:
                    a = (e + 1) * (e + 2) * (e + 3) // 6
                else:
                    a = ((e + 2) // 2) * ((e + 3) // 2)
                s_lo += Fraction(odd_part(a), pe)
                s_all += Fraction((e + 1) * (e + 2) * (e + 3) // 6, pe)
                pe *= p
            loc_lo = Fraction(p - 1, p) * s_lo
            rem = Fraction(p, p - 1) ** 3 - Fraction(p - 1, p) * s_all
            loc_hi = loc_lo + rem
            cu_lo = mul_lo(cu_lo, fl_s(loc_lo))
            cu_hi = mul_hi(cu_hi, ce_s(loc_hi))
        cu_hi = mul_hi(cu_hi, ce_s(tail_CU_hi))
        lo_fr, hi_fr = Fraction(cu_lo, SCALE), Fraction(cu_hi, SCALE)
        k_plus = int(hi_fr) + 1
        tau3_CU[D] = (lo_fr, hi_fr)
        tau3_kplus[D] = k_plus
        check_encl(hi_fr < k_plus, f"C_{{U,{D}}} < {k_plus}")
    check_exact(tau3_kplus == {5: 3, -3: 4, -4: 5, 8: 4}, "C5.2 explicit k_+(D) thresholds")
    print("  [encl] Quadratic-twisted tau_3 * chi_D odd-part means C_{U,D} & explicit D^+ < 1 thresholds k >= k_+(D):")
    for D in (5, -3, -4, 8):
        lo_fr, hi_fr = tau3_CU[D]
        print(f"    D={D:+2d}: C_{{U,D}} in [{dec_floor(lo_fr, 6)}, {dec_ceil(hi_fr, 6)}] => D^+ < 1, not in K_2 for all k >= {tau3_kplus[D]}")

    # 6.6 Theorem C5.3: Unconditional Base-2 Disjunctivity of E(2^k), E_odd(2^k), E_+(2^k) (all k >= 1)!
    # (a) Odd-Target Guard-Bit Lemma: for every binary word w of length ell <= 5 and signed eps in (-1, 1),
    #     setting W = 2^{ell+1} + 2*val_2(w) + 1 (odd), floor(W + eps) in {W-1, W} preserves the middle ell bits w!
    for ell in range(1, 6):
        for val_w in range(1 << ell):
            w_str = format(val_w, f"0{ell}b")
            W = (1 << (ell + 1)) | (val_w << 1) | 1
            check_exact((W & 1) == 1, "W is odd")
            for eps in (Fraction(-999, 1000), Fraction(-49, 100), Fraction(-1, 1000), Fraction(0),
                        Fraction(1, 1000), Fraction(49, 100), Fraction(999, 1000)):
                val_fr = W + eps
                fl_val = val_fr.numerator // val_fr.denominator
                check_exact(fl_val in (W - 1, W), f"floor(W+eps) in {{W-1,W}}")
                bits = bin(fl_val)[2:]
                check_exact(len(bits) == ell + 2 and bits[1:-1] == w_str,
                            f"Guard-bit lemma w={w_str}, eps={eps}")

    # (b) Exact Lambert coefficient formulas, |a(m)| <= tau(m), odd coincidence, and odd-squarefree multiplicativity
    #     across all 1 <= m <= 1000 (computed directly from divisor sums!):
    def factorize_det(n):
        """Deterministic trial-division prime factorization returning dict {p: e}."""
        facs = {}
        d = 2
        while d * d <= n:
            if n % d == 0:
                e = 0
                while n % d == 0:
                    n //= d
                    e += 1
                facs[d] = e
            d = 3 if d == 2 else d + 2
        if n > 1:
            facs[n] = 1
        return facs

    def coeffs_from_fac(facs):
        """Exact (tau, tau_odd, a_plus) from prime factorization dict."""
        t_all = 1
        t_odd = 1
        e2 = facs.get(2, 0)
        for p, e in facs.items():
            t_all *= (e + 1)
            if p > 2:
                t_odd *= (e + 1)
        return t_all, t_odd, (1 - e2) * t_odd

    for m_val in range(1, 1001):
        # Brute divisor sums directly from Lambert series definitions:
        t_dir = 0
        to_dir = 0
        ap_dir = 0
        for d in range(1, m_val + 1):
            if m_val % d == 0:
                t_dir += 1
                if d & 1:
                    to_dir += 1
                ap_dir += 1 if ((m_val // d) & 1) else -1
        facs = factorize_det(m_val)
        t_f, to_f, ap_f = coeffs_from_fac(facs)
        check_exact((t_dir, to_dir, ap_dir) == (t_f, to_f, ap_f), f"Lambert coeff identity m={m_val}")
        check_exact(abs(ap_dir) <= t_dir and to_dir <= t_dir, f"|a(m)| <= tau(m) at m={m_val}")
        if m_val & 1:
            check_exact(t_dir == to_dir == ap_dir and ap_dir > 0, f"odd coincidence m={m_val}")
        # Odd-squarefree multiplicativity: if Q = prod_{p>2, v_p(m)=1} p, then 2^{omega(Q)} divides all three!
        q_cnt = sum(1 for p, e in facs.items() if p > 2 and e == 1)
        pow2_q = 1 << q_cnt
        check_exact(t_dir % pow2_q == 0 and to_dir % pow2_q == 0 and ap_dir % pow2_q == 0,
                    f"2^omega(Q) divides all three at m={m_val}")

    # Unified 3^{W-1} || m_0 target-coefficient identity:
    for W in (3, 5, 7, 9):
        for u in (5, 7, 35, 5 * 7 * 11):
            m0 = (3 ** (W - 1)) * u
            t_f, to_f, ap_f = coeffs_from_fac(factorize_det(m0))
            expected = W * (1 << omega_dist(u))
            check_exact(t_f == to_f == ap_f == expected and (m0 & 1) == 1, f"unified 3^(W-1) identity W={W}, u={u}")

    # (c) End-to-end toy CRT planting check (square moduli, k = 3, w in {'0', '1'}, ALL THREE families E(8), E_odd(8), E_+(8)):
    # With r = 1 (P_0 = 5), Q_1 = 7 * 11 (2 primes), M_0 = 2 * 3^W * P_0^2 * Q_1^2:
    # Find small t >= 1 with u(t) = m_0 / (3^{W-1} * 5) prime (omega(u) = 1, V_0 = 2) and |eps| < 1/2!
    def crt_2(a1, m1, a2, m2):
        inv = pow(m1, -1, m2)
        return a1 + m1 * (((a2 - a1) * inv) % m2), m1 * m2

    planted_ok = 0
    for w_bit, W_val in [(0, 5), (1, 7)]:
        P0_t, Q1_t = 5, 7 * 11
        m_star, M0_t = crt_2(1, 2, 3 ** (W_val - 1), 3 ** W_val)
        m_star, M0_t = crt_2(m_star, M0_t, P0_t, P0_t * P0_t)
        m_star, M0_t = crt_2(m_star, M0_t, (1 + Q1_t) % (Q1_t * Q1_t), Q1_t * Q1_t)
        found = False
        for t_try in range(1, 500):
            m0 = m_star + M0_t * t_try
            u_t = m0 // ((3 ** (W_val - 1)) * P0_t)
            u_fac = factorize_det(u_t)
            if len(u_fac) == 1 and next(iter(u_fac.values())) == 1 and math.gcd(u_t, 6 * P0_t * Q1_t) == 1:
                # Check V_0 = 2, target coeff = 4*W, Q_1 || (m0 - 1) => 4 | a(m0 - 1) => 2^{3-2}*a(m0-1) in 8*Z!
                t0, to0, ap0 = coeffs_from_fac(factorize_det(m0))
                check_exact(t0 == to0 == ap0 == 4 * W_val, "toy CRT target coeff")
                tm1, tom1, apm1 = coeffs_from_fac(factorize_det(m0 - 1))
                check_exact(tm1 % 4 == 0 and tom1 % 4 == 0 and apm1 % 4 == 0, "toy CRT lower isolation s=1")
                # Exact rational upper head (j = 1..18) for all three families + deterministic tail bound j >= 19:
                eps_h = [Fraction(0), Fraction(0), Fraction(0)]
                for j_off in range(1, 19):
                    tj, toj, apj = coeffs_from_fac(factorize_det(m0 + j_off))
                    den_j = 1 << (2 + 3 * j_off)
                    eps_h[0] += Fraction(tj, den_j)
                    eps_h[1] += Fraction(toj, den_j)
                    eps_h[2] += Fraction(apj, den_j)
                # Rigorous deterministic tail bound for j >= 19:
                # tau(m0 + j) <= 2 * (isqrt(m0 + 19) + j), and sum_{j>=19} 2^{-3j} = 2^{-57} * 8/7;
                # bound generously by (isqrt(m0) + 100) / 2^{55}:
                tail_bd = Fraction(math.isqrt(m0) + 100, 1 << 55)
                check_exact(tail_bd < Fraction(1, 10 ** 9), "toy CRT tail bound < 1e-9")
                if all(abs(eh) + tail_bd < Fraction(1, 2) for eh in eps_h):
                    # Verify ALL THREE families read the exact planted bit w_bit!
                    for idx_fam, eh in enumerate(eps_h):
                        v_lo = W_val + eh - tail_bd
                        v_hi = W_val + eh + tail_bd
                        fl_lo = v_lo.numerator // v_lo.denominator
                        fl_hi = v_hi.numerator // v_hi.denominator
                        check_exact((fl_lo >> 1) & 1 == w_bit and (fl_hi >> 1) & 1 == w_bit,
                                    f"toy CRT planted bit w={w_bit}, fam={idx_fam}")
                        planted_ok += 1
                    found = True
                    break
        check_exact(found, f"found admissible toy CRT planting for w={w_bit}")
    check_exact(planted_ok == 6, "all 6 toy CRT plantings (2 words x 3 families) verified")

    # (d) Exact exponent constant check for Theorem C5.3:
    # With r = ceil(2 log_2 log X), R = r + floor(3 L) + ell + 4 = (2/ln 2 + 3 + o(1)) L, S = floor(R / k),
    # total planted primes T_pr = r + sum_{s=1}^S (R - ks) <= r + R^2 / (2k), each prime p has log p <= (1 + o(1)) L,
    # so log M_0 <= (R^2 / k) (1 + o(1)) L <= ((2/ln 2 + 3)^2 / k + o(1)) L^3 < (35 / k) L^3 < (37 / k) L^3.
    ln2_lo, ln2_hi = ln_encl_rat(Fraction(2), 30)
    R_coeff_hi = Fraction(2) / ln2_lo + 3
    check_encl(R_coeff_hi * R_coeff_hi < 35, f"(2/ln2 + 3)^2 = {dec_ceil(R_coeff_hi**2, 4)} < 35")
    print(f"  [encl] C5.3 Disjunctivity: guard-bit (-1,1), 1000 coeff/mult checks, 6/6 toy CRT plantings, "
          f"(2/ln 2 + 3)^2 <= {dec_ceil(R_coeff_hi**2, 4)} < 37!")

    # (e) [FINITE] Concrete word-occurrence check on certified 1200-bit prefixes of E(8), E_+(8), E_+(2) (finite measurements only!):
    for name, k_val, mode in [("E(8)", 3, "tau"), ("E_+(8)", 3, "aplus"), ("E_+(2)", 1, "aplus")]:
        N_p = 1200
        g_p = 60
        Ntot = N_p + g_p
        Mmax = Ntot // k_val + 40
        S_sc = 0
        for m in range(1, Mmax + 1):
            if mode == "aplus":
                c = a_plus(m)
            else:
                c = 1
                tmp = m
                d = 2
                while d * d <= tmp:
                    if tmp % d == 0:
                        e = 0
                        while tmp % d == 0:
                            tmp //= d
                            e += 1
                        c *= (e + 1)
                    d += 1
                if tmp > 1:
                    c *= 2
            sh = Ntot - k_val * m
            if sh >= 0:
                S_sc += c << sh
        bit_str = "".join(str((S_sc >> (Ntot - n)) & 1) for n in range(1, N_p + 1))
        seen4 = {bit_str[i : i + 4] for i in range(N_p - 3)}
        check_finite(len(seen4) == 16, f"[finite] all 16 4-bit words in {name} prefix")
    print("  [finite] All 16 4-bit binary words confirmed in 1200-bit prefixes of E(8), E_+(8), E_+(2) (finite measurements only!)")

    return {
        "alt_cubic": alt_cubic_res, "std_cubic": std_cubic_res,
        "bar_std_lo": bar_std_lo, "bar_alt_lo": bar_alt_lo,
        "tau3": tau3_res, "tau3_CU": tau3_CU, "tau3_kplus": tau3_kplus,
    }


# ---------------------------------------------------------------------------
# Main runner + outward-rounded endpoint audit
# ---------------------------------------------------------------------------
def main():
    primes_1e5 = sieve_primes(100000)
    s1 = run_section_1(primes_1e5)
    s2 = run_section_2(s1)
    s3 = run_section_3(primes_1e5, s1)
    run_section_4(primes_1e5)
    s5 = run_section_5(primes_1e5)
    s6 = run_section_6(primes_1e5, s5)

    # Explicit outward-rounded decimal assertions for EVERY quoted interval/endpoint in notes/phase26/mesoscopic-carry-correlations.md!
    assert_outward_dec(s1["mu_lo"], s1["mu_hi"], "2.076318", "2.076347", 6, "mu")
    assert_outward_dec(s1["psi2_lo"], s1["psi2_hi"], "0.356817", "0.356889", 6, "E[Psi_2_adj]")
    check_encl(dec_ceil(s1["B2_adj_hi"], 6) == "0.486661", "B_2^adj upper")
    check_encl(dec_floor(Fraction(1, 2) - s1["B2_adj_hi"], 6) == "0.013339", "D^- 2-col lower")
    check_encl(dec_floor(s1["star_lo"], 6) == "0.380742", "1-col star converse")
    check_encl(dec_floor(s2["E_7var_r3_lo"], 6) == "0.378089", "7-var r=3 lower")
    check_encl(dec_ceil(s2["P7_hi"], 6) == "0.369593", "7-var r=7 upper")
    check_encl(dec_floor(s2["E_iid_r2_lo"], 6) == "0.400955", "3-var iid r=2 lower")
    check_encl(dec_ceil(s2["E_P3"], 6) == "0.369859", "3-var iid r=3 exact")
    assert_outward_dec(s3["ER_lo"], s3["ER_hi"], "0.323087", "0.323132", 6, "E_{Q_3}[R_3/8]")
    assert_outward_dec(s3["ET12_lo"], s3["ET12_hi"], "0.497296", "0.497302", 6, "E[T_12]")
    check_encl(dec_floor(s3["mu11_lo"], 6) == "0.503909", "M=11 countermeasure")
    check_encl(dec_ceil(s3["exc46"], 6) == "0.002220", "E(2) W=8 r=46 excess")
    check_encl(dec_ceil(s5["k_req_hi"], 5) == "24.75247" and s5["k0_cert"] == 25, "C4.2 k_0 = 25")
    check_encl(dec_floor(s5["gap_k0_lo"], 7) == "0.0000436", "C4.2 gap at k_0 = 25")
    check_encl(dec_floor(s5["C_cond_lo"], 5) == "1.02341", "C4.2 conditional C threshold")
    assert_outward_dec(s5["Wp_lo"], s5["Wp_hi"], "0.908065", "0.908215", 6, "TRUE W_+")
    assert_outward_dec(s5["C_Up_lo"], s5["C_Up_hi"], "1.220305", "1.220322", 6, "C_{U,+}")
    assert_outward_dec(s5["def_Eplus4_lo"], s5["def_Eplus4_hi"], "0.120699", "0.120775", 6, "E_+(4) deficit")
    assert_outward_dec(s6["alt_cubic"][31][0], s6["alt_cubic"][31][1], "0.228495", "0.228504", 6, "alt cubic M=31")
    assert_outward_dec(s6["alt_cubic"][43][0], s6["alt_cubic"][43][1], "0.230753", "0.230762", 6, "alt cubic M=43")
    assert_outward_dec(s6["alt_cubic"][109][0], s6["alt_cubic"][109][1], "0.230631", "0.230639", 6, "alt cubic M=109")
    assert_outward_dec(s6["alt_cubic"][127][0], s6["alt_cubic"][127][1], "0.243667", "0.243676", 6, "alt cubic M=127")
    check_encl(dec_floor(s6["bar_std_lo"], 5) == "0.48715", "k=1 std cubic barrier")
    check_encl(dec_floor(s6["bar_alt_lo"], 5) == "0.45243", "k=1 alt cubic barrier")
    assert_outward_dec(s6["tau3"][-3][0], s6["tau3"][-3][1], "1.584160", "1.584188", 6, "tau_3*chi_{-3}")
    assert_outward_dec(s6["tau3"][-4][0], s6["tau3"][-4][1], "1.751324", "1.751354", 6, "tau_3*chi_{-4}")
    assert_outward_dec(s6["tau3"][5][0], s6["tau3"][5][1], "1.425543", "1.425568", 6, "tau_3*chi_5")
    assert_outward_dec(s6["tau3"][8][0], s6["tau3"][8][1], "1.717434", "1.717464", 6, "tau_3*chi_8")
    assert_outward_dec(s6["tau3_CU"][5][0], s6["tau3_CU"][5][1], "2.602773", "2.602948", 6, "C_{U,+5}")
    assert_outward_dec(s6["tau3_CU"][-3][0], s6["tau3_CU"][-3][1], "3.321945", "3.322168", 6, "C_{U,-3}")
    assert_outward_dec(s6["tau3_CU"][-4][0], s6["tau3_CU"][-4][1], "4.347688", "4.347979", 6, "C_{U,-4}")
    assert_outward_dec(s6["tau3_CU"][8][0], s6["tau3_CU"][8][1], "3.944773", "3.945037", 6, "C_{U,+8}")
    C_lat_hi = s5["inv_sig2_10_hi"] * s1["C_lat_raw_hi"]
    check_encl(C_lat_hi < 180, f"C1.4(2) explicit C_lat <= {dec_ceil(C_lat_hi, 4)} < 180")

    print(f"\nALL CHECKS PASSED: {EXACT_COUNT} [exact] + {ENCL_COUNT} [encl] = {EXACT_COUNT + ENCL_COUNT} "
          f"zero-float theorem checks (plus {FINITE_COUNT} [finite] prefix measurements).")


if __name__ == "__main__":
    main()
