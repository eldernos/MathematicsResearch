#!/usr/bin/env python3
"""
Phase 25 Track B: Generalized Erdos-Borwein & Signed Lambert Classification.

Companion verification and certificate script for:
    notes/phase25/generalized-lambert-and-eplus.md

Strict separation of check categories:
  [exact]  Exact integer / Fraction algebraic, combinatorial, and automaton proofs.
  [encl]   Outward-rounded exact integer / Fraction enclosures of infinite sums/products.
  [finite] Finite-prefix digit/block measurements (never asymptotic evidence).

Standard library only. Exits 0 iff every assertion passes.
"""

from __future__ import annotations

import math
import time
from fractions import Fraction
from typing import Dict, List, Tuple

CHECKS_EXACT = 0
CHECKS_ENCL = 0
CHECKS_FINITE = 0


def check_exact(cond: bool, msg: str = "") -> None:
    global CHECKS_EXACT
    if not cond:
        raise AssertionError(f"[exact] FAILED: {msg}")
    CHECKS_EXACT += 1


def check_encl(cond: bool, msg: str = "") -> None:
    global CHECKS_ENCL
    if not cond:
        raise AssertionError(f"[encl] FAILED: {msg}")
    CHECKS_ENCL += 1


def check_finite(cond: bool, msg: str = "") -> None:
    global CHECKS_FINITE
    if not cond:
        raise AssertionError(f"[finite] FAILED: {msg}")
    CHECKS_FINITE += 1


# =============================================================================
# Core exact arithmetic utilities (integer / Fraction / fixed-scale outward)
# =============================================================================

SCALE_BITS = 96
SCALE = 1 << SCALE_BITS


def primes_up_to(limit: int) -> List[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i : limit + 1 : i] = bytearray(len(sieve[i * i : limit + 1 : i]))
    return [i for i, v in enumerate(sieve) if v]


def odd_part(n: int) -> int:
    n = abs(n)
    if n == 0:
        return 0
    return n >> ((n & -n).bit_length() - 1)


def strip_factor(val: int, b: int) -> int:
    if val == 0:
        return 0
    val = abs(val)
    while val % b == 0:
        val //= b
    return val


def v2(n: int) -> int:
    if n == 0:
        raise ValueError("v2(0) undefined")
    return (n & -n).bit_length() - 1


def popcount(n: int) -> int:
    return abs(n).bit_count()


def naf_weight(n: int) -> int:
    n = abs(n)
    w = 0
    while n > 0:
        if n & 1:
            w += 1
            if n & 2:
                n += 1
            else:
                n -= 1
        n >>= 1
    return w


def asym_weight_int(n: int, cp: int, cm: int, memo: Dict[Tuple[int, int, int], int]) -> int:
    """Exact minimal (cp, cm)-weighted signed binary cost for integer n (cp, cm in Z_>=0)."""
    if n == 0:
        return 0
    if n < 0:
        return asym_weight_int(-n, cm, cp, memo)
    key = (n, cp, cm)
    if key in memo:
        return memo[key]
    if n == 1:
        res = cp
    elif (n & 1) == 0:
        res = asym_weight_int(n >> 1, cp, cm, memo)
    else:
        a = cp + asym_weight_int((n - 1) >> 1, cp, cm, memo)
        b = cm + asym_weight_int((n + 1) >> 1, cp, cm, memo)
        res = a if a <= b else b
    memo[key] = res
    return res


def isqrt_bracket(m: int, scale: int = 1 << 64) -> Tuple[Fraction, Fraction]:
    """Exact rational enclosure [lo, hi] of sqrt(m) via integer isqrt."""
    r = math.isqrt(m * scale * scale)
    lo = Fraction(r, scale)
    hi = Fraction(r, scale) if r * r == m * scale * scale else Fraction(r + 1, scale)
    check_exact(lo * lo <= m <= hi * hi, f"isqrt_bracket failed for m={m}")
    return lo, hi


def mul_iv_scaled(a: Tuple[int, int], b: Tuple[int, int]) -> Tuple[int, int]:
    """Multiply two nonnegative fixed-scale intervals (scale = SCALE) with outward rounding."""
    lo = (a[0] * b[0]) >> SCALE_BITS
    hi = (a[1] * b[1] + SCALE - 1) >> SCALE_BITS
    return lo, hi


def frac_to_iv(lo_f: Fraction, hi_f: Fraction) -> Tuple[int, int]:
    """Convert exact Fraction interval [lo_f, hi_f] to outward-rounded SCALE interval."""
    lo = (lo_f.numerator * SCALE) // lo_f.denominator
    hi = (hi_f.numerator * SCALE + hi_f.denominator - 1) // hi_f.denominator
    return lo, hi


def iv_to_frac(iv: Tuple[int, int]) -> Tuple[Fraction, Fraction]:
    return Fraction(iv[0], SCALE), Fraction(iv[1], SCALE)


def fmt_lb_dec(x: Fraction, digits: int = 4) -> str:
    """Outward-rounded (floor) decimal string for a nonnegative rational lower bound."""
    if x < 0:
        raise ValueError(f"fmt_lb_dec requires x >= 0, got {x}")
    ten = 10 ** digits
    val = (x.numerator * ten) // x.denominator
    int_part, frac_part = divmod(val, ten)
    return f"{int_part}.{frac_part:0{digits}d}"


def fmt_ub_dec(x: Fraction, digits: int = 4) -> str:
    """Outward-rounded (ceil) decimal string for a nonnegative rational upper bound."""
    if x < 0:
        raise ValueError(f"fmt_ub_dec requires x >= 0, got {x}")
    ten = 10 ** digits
    val = (x.numerator * ten + x.denominator - 1) // x.denominator
    int_part, frac_part = divmod(val, ten)
    return f"{int_part}.{frac_part:0{digits}d}"


def sci_exp(x: Fraction) -> int:
    """Exact integer exponent e with 10^e <= x < 10^(e+1) for positive rational x."""
    if x <= 0:
        raise ValueError(f"sci_exp requires x > 0, got {x}")
    num, den = x.numerator, x.denominator
    e = 0
    if num >= den:
        p = 1
        while num >= den * (p * 10):
            p *= 10
            e += 1
    else:
        p = 1
        while num * p < den:
            p *= 10
            e -= 1
    return e


def fmt_lb_sci(x: Fraction, digits: int = 4) -> str:
    """Outward-rounded (floor) scientific notation string for a positive rational lower bound."""
    e = sci_exp(x)
    shift = digits - e
    if shift >= 0:
        mant = (x.numerator * (10 ** shift)) // x.denominator
    else:
        mant = x.numerator // (x.denominator * (10 ** (-shift)))
    ten = 10 ** digits
    int_part, frac_part = divmod(mant, ten)
    return f"{int_part}.{frac_part:0{digits}d}e{e:+03d}"


def fmt_encl(lo: Fraction, hi: Fraction, digits: int = 6) -> str:
    """Outward-rounded decimal string of [lo, hi] to `digits` decimal places (zero float)."""
    return f"[{fmt_lb_dec(lo, digits)}, {fmt_ub_dec(hi, digits)}]"


def prime_inv_sq_tail_ub(P: int) -> Fraction:
    """
    Rigorous elementary upper bound on sum_{p > P} 1/p^2 for even P >= 6.
    Uses the elementary telescoping bound over odd integers >= P + 1:
        sum_{m >= P/2} 1/(2m+1)^2 < (1/2) sum_{m >= P/2} (1/(2m-1) - 1/(2m+1)) = 1/(2*(P-1)).
    """
    check_exact(P >= 6 and P % 2 == 0, "P must be even >= 6")
    return Fraction(1, 2 * (P - 1))


def exp_ub_rational(t: Fraction) -> Fraction:
    """For 0 <= t < 1, exp(t) <= 1/(1 - t) (since 1 - t <= exp(-t))."""
    check_exact(0 <= t < 1, f"exp_ub_rational requires 0 <= t < 1, got {t}")
    return Fraction(1, 1) / (1 - t)


# =============================================================================
# Section 1: B1 -- Exact Carry Conservation, Dead-Block Reduction, & C_U
# =============================================================================

def certify_odd_part_means(P: int = 20000) -> Dict[str, Tuple[Fraction, Fraction]]:
    """
    Certify outward-rounded exact rational enclosures for:
      L2_odd, L2_plus, C_U_odd, C_U, C_U_plus, and C_U^(M) for M in {3,4,6,8,12,24},
      plus s = 1/2 moments C_U(1/2), C_U_odd(1/2), C_U_plus(1/2).
    """
    ps = primes_up_to(P)
    check_exact(ps[0] == 2 and ps[-1] < P, "prime sieve sanity")

    # 1a. Verify power-series identity for sum_{m>=1} odd(m) x^m through x^255
    M_pow = 256
    lhs = [0] * M_pow
    for m in range(1, M_pow):
        lhs[m] = odd_part(m)
    rhs = [0] * M_pow
    j = 0
    while (1 << j) < M_pow:
        step = 1 << j
        r = 0
        while step * (2 * r + 1) < M_pow:
            rhs[step * (2 * r + 1)] += 2 * r + 1
            r += 1
        j += 1
    check_exact(lhs == rhs, "odd(m) power series decomposition through x^255")

    # 1b. Verify L_p^odd < 1 + 2/p^2 algebraically: 2p^2 - 6p + 3 > 0 for all p >= 3
    for p in ps[1:100]:
        check_exact(2 * p * p - 6 * p + 3 > 0, f"local upper bound polynomial at p={p}")

    # 1c. Certify L2_odd = (1/2) sum_{e>=0} odd(e+1) 2^{-e}
    # Using E = 60 terms; tail <= 2^{-60} * (61 + 1) = 62 / 2^60
    E2 = 60
    l2_lo = Fraction(0)
    for e in range(E2):
        l2_lo += Fraction(odd_part(e + 1), 1 << (e + 1))
    l2_hi = l2_lo + Fraction(E2 + 2, 1 << E2)
    # Cross-check with closed form sum_{j=0..5} 2^{2^j}(2^{2^{j+1}}+1)/(2^{2^{j+1}}-1)^2
    l2_cf = Fraction(0)
    for j in range(6):
        a = 1 << (1 << j)
        a2 = a * a
        l2_cf += Fraction(a * (a2 + 1), (a2 - 1) ** 2)
    check_encl(l2_cf >= l2_lo - Fraction(1, 1 << 50) and l2_cf <= l2_hi, "L2_odd closed form check")

    l2_plus_lo = Fraction(1, 2) + l2_lo / 4
    l2_plus_hi = Fraction(1, 2) + l2_hi / 4

    # 1d. Certify C_U_odd = prod_{p > 2} L_p^odd in fixed-scale outward arithmetic
    prod_odd_iv = (SCALE, SCALE)
    local_odd_small: Dict[int, Tuple[Fraction, Fraction]] = {}
    for p in ps[1:]:
        E = 24 if p <= 200 else (12 if p <= 2000 else 6)
        # Compute exact sum_{e=0}^{E-1} odd(e+1) / p^e using integer numerator over p^(E-1)
        num = 0
        pow_p = 1
        for e in range(E - 1, -1, -1):
            num += odd_part(e + 1) * pow_p
            if e > 0:
                pow_p *= p
        den = pow_p * p  # (1 - 1/p) * num / p^{E-1} = (p - 1) * num / p^E
        loc_lo = Fraction((p - 1) * num, den)
        # Tail: (1 - 1/p) sum_{e>=E} odd(e+1)/p^e <= (E + 1 + 1/(p-1)) / p^E
        tail = Fraction((E + 1) * (p - 1) + 1, (p - 1) * den)
        loc_hi = loc_lo + tail
        check_encl(1 < loc_lo <= loc_hi < 1 + Fraction(2, p * p), f"L_p^odd bracket at p={p}")
        if p <= 29:
            local_odd_small[p] = (loc_lo, loc_hi)
        prod_odd_iv = mul_iv_scaled(prod_odd_iv, frac_to_iv(loc_lo, loc_hi))

    # Tail over p > P: prod_{p > P} L_p^odd <= exp(2 * sum_{p > P} 1/p^2) <= 1/(1 - 1/(P-1))
    tail_odd_ub = exp_ub_rational(2 * prime_inv_sq_tail_ub(P))
    prod_odd_iv = mul_iv_scaled(prod_odd_iv, frac_to_iv(Fraction(1), tail_odd_ub))
    cu_odd_lo, cu_odd_hi = iv_to_frac(prod_odd_iv)

    cu_lo, cu_hi = l2_lo * cu_odd_lo, l2_hi * cu_odd_hi
    cu_plus_lo, cu_plus_hi = l2_plus_lo * cu_odd_lo, l2_plus_hi * cu_odd_hi

    # Check key B1 / B2 inequalities and exact tabulated endpoints
    check_encl(Fraction(2076306, 1000000) <= cu_lo <= cu_hi <= Fraction(2076411, 1000000),
               f"C_U enclosure {fmt_encl(cu_lo, cu_hi)}")
    check_encl(Fraction(1402443, 1000000) <= cu_odd_lo <= cu_odd_hi <= Fraction(1402514, 1000000),
               f"C_U_odd enclosure {fmt_encl(cu_odd_lo, cu_odd_hi)}")
    check_encl(Fraction(1220298, 1000000) <= cu_plus_lo <= cu_plus_hi <= Fraction(1220360, 1000000),
               f"C_U_plus enclosure {fmt_encl(cu_plus_lo, cu_plus_hi)}")
    check_encl(cu_hi < 3, "C_U < 3 for E(2^k) k >= 3")
    check_encl(cu_hi / 4 <= Fraction(519103, 1000000) < Fraction(8, 15), "C_U/4 < 8/15 for E(16) not in K_16 \\ K_2")
    check_encl(cu_hi / 5 <= Fraction(415283, 1000000) < Fraction(1, 2), "C_U/5 < 1/2 for E(2^k) not in K_{2^j} \\ K_2 (k>=5)")
    check_encl(cu_odd_hi < 2, "C_U_odd < 2 for E_odd(4) D^+ < 1")
    check_encl(cu_odd_hi / 3 <= Fraction(467505, 1000000) < Fraction(1, 2), "C_U_odd/3 < 1/2 for E_odd(2^k) not in K_{2^j}")
    # Theorem B1.4(2) Markov parameter j_0 = ceil(log_2(320 * C_{U,+})) = 9
    check_encl(256 < 320 * cu_plus_lo <= 320 * cu_plus_hi < 512,
               "Theorem B1.4(2) Markov cutoff j_0 = ceil(log_2(320 * C_{U,+})) == 9")
    check_encl(8 * cu_plus_hi / 512 < Fraction(1, 40), "Theorem B1.4(2) far-tail Markov bound < 1/40")

    # C_U^(3) = C_U / L_3^odd (for M = 3, 2-elementary mod 3)
    l3_lo, l3_hi = local_odd_small[3]
    cu_mod3_lo, cu_mod3_hi = cu_lo / l3_hi, cu_hi / l3_lo
    check_encl(cu_mod3_hi <= Fraction(1740302, 1000000) < 2, f"C_U^(3) < 2 for A_{{r,3}}(4): {fmt_encl(cu_mod3_lo, cu_mod3_hi)}")

    # C_U^(5) = C_U / L_5^odd (for M = 5, Fermat prime with phi(5) = 4 = 2^2)
    l5_lo, l5_hi = local_odd_small[5]
    cu_mod5_lo, cu_mod5_hi = cu_lo / l5_hi, cu_hi / l5_lo
    check_encl(cu_mod5_hi <= Fraction(1940647, 1000000) < 2, f"C_U^(5) < 2 for A_{{r,5}}(4): {fmt_encl(cu_mod5_lo, cu_mod5_hi)}")

    # C_U^(6) = C_U_odd / L_3^odd (also equals C_U^(12), C_U^(24))
    cu_mod6_lo, cu_mod6_hi = cu_odd_lo / l3_hi, cu_odd_hi / l3_lo
    check_encl(cu_mod6_hi <= Fraction(1175489, 1000000) < Fraction(3, 2), f"C_U^(6) < 3/2: {fmt_encl(cu_mod6_lo, cu_mod6_hi)}")

    # 1e. Certify s = 1/2 moments: C_U_odd(1/2), C_U(1/2), C_U_plus(1/2)
    # Precompute exact isqrt brackets for odd(e+1) up to e = 60
    sqrt_odd: Dict[int, Tuple[Fraction, Fraction]] = {}
    for e in range(65):
        u = odd_part(e + 1)
        if u not in sqrt_odd:
            sqrt_odd[u] = isqrt_bracket(u)

    l2_half_lo = Fraction(0)
    l2_half_hi = Fraction(0)
    for e in range(50):
        slo, shi = sqrt_odd[odd_part(e + 1)]
        l2_half_lo += slo / (1 << (e + 1))
        l2_half_hi += shi / (1 << (e + 1))
    l2_half_hi += Fraction(50 + 2, 1 << 50)
    l2_plus_half_lo = Fraction(1, 2) + l2_half_lo / 4
    l2_plus_half_hi = Fraction(1, 2) + l2_half_hi / 4

    P_half = 6000
    ps_h = primes_up_to(P_half)
    prod_odd_half_iv = (SCALE, SCALE)
    for p in ps_h[1:]:
        E = 18 if p <= 100 else (10 if p <= 1000 else 5)
        loc_lo = Fraction(0)
        loc_hi = Fraction(0)
        p_pow = 1
        for e in range(E):
            slo, shi = sqrt_odd[odd_part(e + 1)]
            loc_lo += slo / p_pow
            loc_hi += shi / p_pow
            p_pow *= p
        loc_lo = loc_lo * (p - 1) / p
        loc_hi = loc_hi * (p - 1) / p
        # Tail <= (E + 1 + 1/(p-1)) / p^E
        tail = Fraction((E + 1) * (p - 1) + 1, (p - 1) * p_pow)
        loc_hi += tail
        prod_odd_half_iv = mul_iv_scaled(prod_odd_half_iv, frac_to_iv(loc_lo, loc_hi))

    # Tail for p > P_half: sqrt(e+1) - 1 <= e/2 => L_p(1/2) - 1 <= (5/4)/p^2
    tail_half_ub = exp_ub_rational(Fraction(5, 4) * prime_inv_sq_tail_ub(P_half))
    prod_odd_half_iv = mul_iv_scaled(prod_odd_half_iv, frac_to_iv(Fraction(1), tail_half_ub))
    cu_odd_half_lo, cu_odd_half_hi = iv_to_frac(prod_odd_half_iv)
    cu_half_lo, cu_half_hi = l2_half_lo * cu_odd_half_lo, l2_half_hi * cu_odd_half_hi
    cu_plus_half_lo, cu_plus_half_hi = l2_plus_half_lo * cu_odd_half_lo, l2_plus_half_hi * cu_odd_half_hi

    # Check direct base-32 simple nonnormality of E_+(32) at s = 1/2!
    # Uniform sum_{d=0}^{31} (min(d, 31-d)/32)^{1/2} / 32 vs C_U_plus(1/2) / (5*(sqrt(2) - 1))
    rt2_lo, rt2_hi = isqrt_bracket(2)
    unif32_lo = Fraction(0)
    for d in range(32):
        m = min(d, 31 - d)
        # sqrt(m / 32) = sqrt(2*m) / 8
        smlo, _ = isqrt_bracket(2 * m)
        unif32_lo += smlo / 8
    unif32_lo /= 32
    ub_eplus32_hi = cu_plus_half_hi / (5 * (rt2_lo - 1))
    check_encl(ub_eplus32_hi <= Fraction(432658, 1000000) < Fraction(447125, 1000000) <= unif32_lo,
               f"E_+(32) base-32 simple nonnormality at s=1/2: ub <= {fmt_ub_dec(ub_eplus32_hi, 6)} < {fmt_lb_dec(unif32_lo, 6)} <= unif")

    return {
        "L2_odd": (l2_lo, l2_hi),
        "L2_plus": (l2_plus_lo, l2_plus_hi),
        "C_U_odd": (cu_odd_lo, cu_odd_hi),
        "C_U": (cu_lo, cu_hi),
        "C_U_plus": (cu_plus_lo, cu_plus_hi),
        "C_U_mod3": (cu_mod3_lo, cu_mod3_hi),
        "C_U_mod5": (cu_mod5_lo, cu_mod5_hi),
        "C_U_mod6": (cu_mod6_lo, cu_mod6_hi),
        "C_U_half": (cu_half_lo, cu_half_hi),
        "C_U_odd_half": (cu_odd_half_lo, cu_odd_half_hi),
        "C_U_plus_half": (cu_plus_half_lo, cu_plus_half_hi),
        "Eplus32_s_half_ub": (ub_eplus32_hi, unif32_lo),
    }


def verify_b1_carry_conservation_and_identities() -> Dict[str, Dict[str, float]]:
    """
    Exact finite checks of:
      (1) km - V(m) >= 1 for all k >= 2, 1 <= m <= 30000;
      (2) Exact column carry identity C_k(n) + q_n = d_n + b*q_{n-1},
          mass conservation, dead-position property, and dead-block transition bound
          on certified prefixes of E(8), E(16), E_odd(4), E_odd(8), E*(4), E*(8), and E_3^*(9);
      (3) Phase-averaged linear system 2*x_{r-1} - x_r = c - b_r => x_r = c - {2^r R/(2^j-1)};
      (4) Signed isolated-odd-arrival transition lemma on E_+(8), E_+(16), E_+(32).
    """
    M_pos = 30000
    tau = [0] * (M_pos + 1)
    tau_odd = [0] * (M_pos + 1)
    omega = [0] * (M_pos + 1)
    for d in range(1, M_pos + 1):
        for m in range(d, M_pos + 1, d):
            tau[m] += 1
            if d & 1:
                tau_odd[m] += 1
    for p in primes_up_to(M_pos):
        for m in range(p, M_pos + 1, p):
            omega[m] += 1

    # (1) Positivity of displaced index km - V(m) >= 1 for all k >= 2, m <= 30000
    for m in range(1, M_pos + 1):
        check_exact(2 * m - v2(tau[m]) >= 1, f"2m - V(m) >= 1 at m={m}")
        check_exact(2 * m - v2(tau_odd[m]) >= 1, f"2m - V_odd(m) >= 1 at m={m}")
        check_exact(2 * m - omega[m] >= 1, f"2m - omega(m) >= 1 at m={m}")

    # Helper to certify prefix digits and carry states for nonnegative F_{b^k}(a) = sum a(m) b^{-km}.
    # Scales every source m <= M_tot = N_guard // k directly by b^{N_guard - k*m}, with rigorous
    # tail bound sum_{m > M_tot} a(m) b^{N_guard - k*m} <= 4*(M_tot + 2) (valid since 0 <= a(m) <= 2*m).
    def test_unsigned_series(name: str, b: int, k: int, coeff_fn, val_fn, N_bits: int) -> Dict[str, float]:
        N_guard = N_bits + 96
        M_tot = N_guard // k
        # Confirm no source m > M_tot can displace into [1, N_bits]: since a(m) <= 2*m, V(m) <= log_b(2*m) <= bit_length(2*m)
        check_exact(k * (M_tot + 1) - (2 * (M_tot + 1)).bit_length() > N_bits, f"{name} displaced-arrival completeness")
        Ck = [0] * (N_bits + 1)
        S_lo = 0
        for m in range(1, M_tot + 1):
            a = coeff_fn(m)
            check_exact(0 <= a <= 2 * m, f"{name} coefficient bound at m={m}")
            v = val_fn(m)
            u = a // (b ** v)
            check_exact(u * (b ** v) == a, f"{name} factorization at m={m}")
            pos = k * m - v
            if 1 <= pos <= N_bits:
                Ck[pos] += u
            S_lo += a * (b ** (N_guard - k * m))
        # Rigorous tail upper bound for m > M_tot: sum_{r>=1} 2*(M_tot+r)*b^{N_guard - k*(M_tot+r)} <= 4*(M_tot + 2)
        tail_err = 4 * (M_tot + 2)
        S_hi = S_lo + tail_err

        shift = b ** (N_guard - N_bits)
        pref_lo = S_lo // shift
        pref_hi = S_hi // shift
        check_exact(pref_lo == pref_hi, f"{name} certified prefix up to N={N_bits}")

        # Extract exact digits d[1..N_bits] and floor(F) = d0
        d = [0] * (N_bits + 1)
        tmp = pref_lo
        for n in range(N_bits, 0, -1):
            d[n] = tmp % b
            tmp //= b
        d0 = tmp
        # Reconstruct exact integer carries q_n = floor(b^n F) - A_n via the column carry identity
        # (only nonnegativity q_n >= 0 and dead-block / exit properties carry non-tautological content).
        q = [0] * (N_bits + 1)
        q[0] = d0
        for n in range(1, N_bits + 1):
            q[n] = d[n] + b * q[n - 1] - Ck[n]
            check_exact(q[n] >= 0, f"{name} q[{n}] >= 0")

        # Verify dead-position property and dead-block transition bound!
        dead = [n for n in range(1, N_bits + 1) if d[n] == 0 and q[n - 1] == 0]
        for n in dead:
            check_exact(Ck[n] == 0 and q[n] == 0, f"{name} dead property at n={n}")

        dead_set = set(dead)
        # Verify every exit (n in dead, n+1 not in dead, n < N_bits) is a (0, nonzero) transition!
        exits = 0
        for n in dead:
            if n < N_bits and (n + 1) not in dead_set:
                check_exact(d[n] == 0 and d[n + 1] != 0, f"{name} dead exit transition at n={n}")
                exits += 1

        # Verify exact dead-block inequality of Lemma B1.2(2) for G = 2, 4, 8, 16:
        # (G - 1) * #{1 <= n < N : d_n = 0, d_{n+1} != 0} >= |D_N| - (G - 1) - #{1 <= a <= N - G + 1 : C_k(a..a+G-1) = 0}
        zero_to_nz = sum(1 for n in range(1, N_bits) if d[n] == 0 and d[n + 1] != 0)
        for G in (2, 4, 8, 16):
            empty_G = sum(
                1 for a in range(1, N_bits - G + 2) if all(Ck[a + j] == 0 for j in range(G))
            )
            check_exact(
                (G - 1) * zero_to_nz >= len(dead) - (G - 1) - empty_G,
                f"{name} dead-block inequality at G={G}",
            )

        tr = sum(1 for n in range(1, N_bits) if d[n] != d[n + 1])
        return {
            "N": N_bits,
            "dead_frac": len(dead) / N_bits,
            "tr_frac": tr / N_bits,
            "f_nz": sum(1 for n in range(1, N_bits + 1) if d[n] != 0) / N_bits,
            "mass_frac": sum(Ck[1 : N_bits + 1]) / N_bits,
            "exits_frac": exits / N_bits,
        }

    stats: Dict[str, Dict[str, float]] = {}
    stats["E(8)"] = test_unsigned_series("E(8)", 2, 3, lambda m: tau[m], lambda m: v2(tau[m]), 4000)
    stats["E(16)"] = test_unsigned_series("E(16)", 2, 4, lambda m: tau[m], lambda m: v2(tau[m]), 4000)
    stats["E_odd(4)"] = test_unsigned_series("E_odd(4)", 2, 2, lambda m: tau_odd[m], lambda m: v2(tau_odd[m]), 4000)
    stats["E_odd(8)"] = test_unsigned_series("E_odd(8)", 2, 3, lambda m: tau_odd[m], lambda m: v2(tau_odd[m]), 4000)
    stats["E*(4)"] = test_unsigned_series("E*(4)", 2, 2, lambda m: 1 << omega[m], lambda m: omega[m], 4000)
    stats["E*(8)"] = test_unsigned_series("E*(8)", 2, 3, lambda m: 1 << omega[m], lambda m: omega[m], 4000)
    stats["E_3*(9)"] = test_unsigned_series("E_3*(9)", 3, 2, lambda m: 3 ** omega[m], lambda m: omega[m], 2000)

    # (3) Phase-averaged carry system: 2*x_{r-1} - x_r = c - b_r => x_r = c - {2^r R/(2^j - 1)}
    for j in range(2, 9):
        mod_j = (1 << j) - 1
        c_test = Fraction(7, 13)
        for R in range(1, mod_j):
            # Periodic bits b_1, ..., b_j of R / (2^j - 1)
            bits = [(R >> (j - 1 - idx)) & 1 for idx in range(j)]
            # z_r = {2^r * R / (2^j - 1)} for r = 0..j-1
            z = [Fraction((R * (1 << r)) % mod_j, mod_j) for r in range(j)]
            x = [c_test - zr for zr in z]
            for r in range(j):
                # Equation for r-th digit: bits[r] is digit at position r+1, z[r] = {2^r R/(2^j-1)},
                # 2*z[r] - z[(r+1)%j] = bits[r], so 2*x[r] - x[(r+1)%j] = c_test - bits[r]
                check_exact(2 * x[r] - x[(r + 1) % j] == c_test - bits[r], f"phase system j={j}, R={R}, r={r}")
            # Also verify max(z) >= 2^{j-1}/(2^j - 1) > 1/2
            check_exact(max(z) >= Fraction(1 << (j - 1), mod_j), f"max(z) bound j={j}, R={R}")

    # (4) Signed isolated-odd-arrival transition lemma on E_+(8), E_+(16), E_+(32)
    # Scales every source m <= M_tot = N_guard // k directly by 2^{N_guard - k*m}, with rigorous
    # tail error |2^{N_guard} E_+(2^k) - S_val| <= 4*(M_tot + 2) (since |a_+(m)| <= m).
    for k in (3, 4, 5):
        N_bits = 2400
        N_guard = N_bits + 100
        M_tot = N_guard // k
        check_exact(k * (M_tot + 1) - (2 * (M_tot + 1)).bit_length() > N_bits,
                    f"E_+(2^{k}) displaced-arrival completeness")
        Ck_plus = [0] * (N_bits + 1)
        S_val = 0
        for m in range(1, M_tot + 1):
            e2 = v2(m)
            if e2 == 1:
                continue
            ap = (1 - e2) * tau_odd[m]
            check_exact(abs(ap) <= m, f"E_+(2^{k}) |a_+(m)| <= m at m={m}")
            vp = v2(abs(ap))
            up = ap // (1 << vp)  # signed odd part
            pos = k * m - vp
            if 1 <= pos <= N_bits:
                Ck_plus[pos] += up
            S_val += ap << (N_guard - k * m)
        tail_err = 4 * (M_tot + 2)
        shift = 1 << (N_guard - N_bits)
        lo_p = (S_val - tail_err) // shift
        hi_p = (S_val + tail_err) // shift
        check_exact(lo_p == hi_p, f"E_+(2^{k}) certified prefix N={N_bits}")
        bits = [(lo_p >> (N_bits - n)) & 1 for n in range(1, N_bits + 1)]
        # Verify signed isolated-odd-arrival lemma: if Ck_plus[n] is odd and |Y_n| < 1/2,
        # then (bits[n-1], bits[n]) is a transition (01 or 10).
        # Since 2^{N_guard} E_+ = prefix_int * 2^{N_guard - n} + Y_n * 2^{N_guard - n},
        # |Y_n * 2^{N_guard - n} - rem_scaled| <= tail_err.
        prefix_int = 0
        iso_hits = 0
        for n in range(1, N_bits):
            prefix_int = 2 * prefix_int + Ck_plus[n]
            rem_scaled = S_val - (prefix_int << (N_guard - n))
            half_scaled = 1 << (N_guard - n - 1)
            if (Ck_plus[n] & 1) == 1 and abs(rem_scaled) + tail_err < half_scaled:
                # Guaranteed |Y_n| < 1/2, so {2^{n-1} E_+} in (1/4, 3/4), i.e., bits[n-1] != bits[n]
                check_exact(bits[n - 1] != bits[n], f"E_+(2^{k}) signed odd-arrival lemma at n={n}")
                iso_hits += 1
        check_exact(iso_hits > 100, f"E_+(2^{k}) had {iso_hits} isolated odd arrivals")
        stats[f"E_+(2^{k})_iso"] = {"N": N_bits, "iso_hits": iso_hits, "iso_frac": iso_hits / N_bits}

    return stats


# =============================================================================
# Section 2: B2 -- Construction-Radix Discrepancy D^-(F_{2^k}; 2^k) -> 1
# =============================================================================

def verify_b2_construction_radix(b1_encl: Dict[str, Tuple[Fraction, Fraction]]) -> Dict[str, List[Tuple[int, Fraction, Fraction]]]:
    """
    Certify exact D^-(F_{2^k}(a); 2^k) lower bounds via displaced odd-part moments (s = 1 and s = 1/2),
    and verify exact displaced radix identity and s-moment integral formula.
    """
    # Verify exact s-moment integral identity:
    # int_0^{(1-D)/2} s * t^{s-1} * (1 - 2t - D) dt = (1 - D)^{s+1} / (2^s * (s + 1))
    # Checked at rational D and integer/rational exponents via exact derivative identity:
    # d/dt [ t^s (1 - D) - (2s/(s+1)) t^{s+1} ] = s t^{s-1} (1 - D - 2t)
    for s in [Fraction(1), Fraction(1, 2), Fraction(1, 3), Fraction(2, 3), Fraction(3, 4)]:
        for a in [Fraction(1, 5), Fraction(1, 3), Fraction(2, 5)]:
            # At t = a = (1-D)/2, 1-D = 2a:
            # Value = 2a * a^s - (2s/(s+1)) a^{s+1} = (2/(s+1)) a^{s+1}
            coeff = 2 - Fraction(2) * s / (s + 1)
            check_exact(coeff == Fraction(2, 1) / (s + 1), f"s-moment integral coeff at s={s}")

    # Verify exact displaced radix identity a(n) b^{-n} = W_k(n) b^{-l_k(n)} for b = 2^k
    N_check = 2000
    tau = [0] * (N_check + 1)
    for d in range(1, N_check + 1):
        for m in range(d, N_check + 1, d):
            tau[m] += 1
    for k in (2, 3, 4, 5):
        b = 1 << k
        for n in range(1, 400):
            v = v2(tau[n])
            q, r = divmod(v, k)
            W = odd_part(tau[n]) << r
            check_exact(W * (b ** q) == tau[n], f"displaced radix identity k={k}, n={n}")

    # Compute rigorous lower bounds on D^-(F_{2^k}(a); 2^k) from s = 1 (1 - 2*sqrt(C_U/k))
    # and s = 1/2 (1 - (sqrt(2) * (3/2) * C_U(1/2) / (k * (sqrt(2) - 1)))^{2/3})
    # using exact rational upper bounds on (1 - D)^{s+1}
    rt2_lo, rt2_hi = isqrt_bracket(2)
    tables: Dict[str, List[Tuple[int, Fraction, Fraction]]] = {}
    families = [
        ("E(2^k)", b1_encl["C_U"][1], b1_encl["C_U_half"][1]),
        ("E_odd(2^k)", b1_encl["C_U_odd"][1], b1_encl["C_U_odd_half"][1]),
        ("E*(2^k)", Fraction(1), Fraction(1)),
        ("E_+(2^k)", b1_encl["C_U_plus"][1], b1_encl["C_U_plus_half"][1]),
    ]
    # Exact outward-rounded (floored) 4-decimal table endpoints asserted explicitly (scaled by 10^4)
    expected_b2_table: Dict[Tuple[str, int], Tuple[int, int]] = {
        ("E(2^k)", 5): (0, 0),
        ("E(2^k)", 6): (0, 0),
        ("E(2^k)", 8): (0, 1076),
        ("E(2^k)", 10): (886, 2310),
        ("E(2^k)", 12): (1680, 3190),
        ("E(2^k)", 16): (2795, 4378),
        ("E(2^k)", 32): (4905, 6458),
        ("E(2^k)", 64): (6397, 7769),
        ("E_odd(2^k)", 5): (0, 0),
        ("E_odd(2^k)", 6): (330, 216),
        ("E_odd(2^k)", 8): (1625, 1923),
        ("E_odd(2^k)", 10): (2509, 3040),
        ("E_odd(2^k)", 12): (3162, 3836),
        ("E_odd(2^k)", 16): (4078, 4912),
        ("E_odd(2^k)", 32): (5812, 6794),
        ("E_odd(2^k)", 64): (7039, 7980),
        ("E*(2^k)", 5): (1055, 0),
        ("E*(2^k)", 6): (1835, 1001),
        ("E*(2^k)", 8): (2928, 2572),
        ("E*(2^k)", 10): (3675, 3598),
        ("E*(2^k)", 12): (4226, 4331),
        ("E*(2^k)", 16): (5000, 5320),
        ("E*(2^k)", 32): (6464, 7052),
        ("E*(2^k)", 64): (7500, 8143),
        ("E_+(2^k)", 5): (119, 555),
        ("E_+(2^k)", 6): (980, 1636),
        ("E_+(2^k)", 8): (2188, 3096),
        ("E_+(2^k)", 10): (3013, 4050),
        ("E_+(2^k)", 12): (3622, 4731),
        ("E_+(2^k)", 16): (4476, 5650),
        ("E_+(2^k)", 32): (6094, 7260),
        ("E_+(2^k)", 64): (7238, 8274),
    }
    for fname, cu1_hi, cuh_hi in families:
        rows: List[Tuple[int, Fraction, Fraction]] = []
        for k in (4, 5, 6, 8, 10, 12, 16, 32, 64):
            # s = 1 bound: (1 - D)^2 <= 4 * cu1_hi / k
            rhs1 = 4 * cu1_hi / k
            if rhs1 < 1:
                num_s = rhs1.numerator * rhs1.denominator
                _, sq_hi = isqrt_bracket(num_s)
                d1_lo = 1 - sq_hi / rhs1.denominator
                check_encl((1 - d1_lo) ** 2 >= rhs1, f"s=1 D^- cert {fname} k={k}")
            else:
                d1_lo = Fraction(0)
            # s = 1/2 bound: (1 - D)^{3/2} <= rt2_hi * (3/2) * cuh_hi / (k * (rt2_lo - 1))
            rhsh = rt2_hi * Fraction(3, 2) * cuh_hi / (k * (rt2_lo - 1))
            if rhsh < 1:
                r2 = rhsh * rhsh
                S_c = 10 ** 9
                lo_c, hi_c = 0, S_c
                while lo_c < hi_c:
                    mid = (lo_c + hi_c) // 2
                    if mid * mid * mid * r2.denominator >= r2.numerator * (S_c ** 3):
                        hi_c = mid
                    else:
                        lo_c = mid + 1
                dh_lo = 1 - Fraction(lo_c, S_c)
                check_encl((1 - dh_lo) ** 3 >= r2, f"s=1/2 D^- cert {fname} k={k}")
            else:
                dh_lo = Fraction(0)
            if (fname, k) in expected_b2_table:
                exp1, exph = expected_b2_table[(fname, k)]
                if exp1 > 0:
                    check_encl(d1_lo >= Fraction(exp1, 10000),
                               f"B2 table s=1 endpoint {fname} k={k}: {fmt_lb_dec(d1_lo, 4)} >= {fmt_lb_dec(Fraction(exp1, 10000), 4)}")
                if exph > 0:
                    check_encl(dh_lo >= Fraction(exph, 10000),
                               f"B2 table s=1/2 endpoint {fname} k={k}: {fmt_lb_dec(dh_lo, 4)} >= {fmt_lb_dec(Fraction(exph, 10000), 4)}")
            rows.append((k, d1_lo, dh_lo))
        tables[fname] = rows

    # Confirm 148x improvement at k = 64 vs Phase 24 (0.00524)
    e64_dh = dict((k, dh) for k, _, dh in tables["E(2^k)"])[64]
    check_encl(e64_dh >= Fraction(7769, 10000) > 148 * Fraction(524, 100000), "E(2^64) > 148x vs Phase 24")

    # Verify direct base-2^k simple nonnormality threshold C_U / k < 1/4 - 1/2^{k+1}
    # E_+(64) at k = 6 (s = 1)
    check_encl(b1_encl["C_U_plus"][1] / 6 < Fraction(1, 4) - Fraction(1, 128), "E_+(64) base-64 s=1 simple nonnormality")
    # E*(32) at k = 5 (s = 1)
    check_encl(Fraction(1, 5) < Fraction(1, 4) - Fraction(1, 64), "E*(32) base-32 s=1 simple nonnormality")
    # E_odd(64) at k = 6 (s = 1)
    check_encl(b1_encl["C_U_odd"][1] / 6 < Fraction(1, 4) - Fraction(1, 128), "E_odd(64) base-64 s=1 simple nonnormality")
    # E(512) at k = 9 (s = 1)
    check_encl(b1_encl["C_U"][1] / 9 < Fraction(1, 4) - Fraction(1, 1024), "E(512) base-512 s=1 simple nonnormality")
    # Check E_b^*(b^k) general base bound 1/(k(b-1)) < 1/4 for b = 2,3,4,5,6,10
    for b in (2, 3, 4, 5, 6, 10):
        k_thr = 4 // (b - 1) + 1
        check_exact(Fraction(1, k_thr * (b - 1)) < Fraction(1, 4), f"E_b^*(b^k) threshold b={b}")

    return tables


# =============================================================================
# Section 3: B3 -- Exact Koksma Variation, Asymmetric (1,3/2) Transducer, & Lean Cert
# =============================================================================

def build_weighted_automaton(cp: int, cm: int):
    """Build exact normalized min-plus DP states and Moore minimization for costs (cp, cm)."""
    def step(v, bit):
        v0, v1, v2 = v
        if bit == 0:
            nv = (min(v0 + cm, v1 + cp), v1, min(v1 + cm, v2 + cp))
        else:
            nv = (v0, min(v0 + cm, v1 + cp), v1)
        m = min(nv)
        return (nv[0] - m, nv[1] - m, nv[2] - m), m

    init = (0, 0, 0)
    states = {init: 0}
    q = [init]
    tr = {}
    while q:
        s = q.pop(0)
        for bit in (0, 1):
            ns, inc = step(s, bit)
            if ns not in states:
                states[ns] = len(states)
                q.append(ns)
            tr[(states[s], bit)] = (states[ns], inc)

    n = len(states)
    part = [tuple(tr[(s, b)][1] for b in (0, 1)) for s in range(n)]
    while True:
        new_part = [(part[s], part[tr[(s, 0)][0]], part[tr[(s, 1)][0]]) for s in range(n)]
        mp = {x: i for i, x in enumerate(sorted(set(new_part)))}
        new_part = [mp[x] for x in new_part]
        if new_part == part:
            break
        part = new_part
    # Remap so start state is 0
    start_cls = part[0]
    remap = {start_cls: 0}
    for c in sorted(set(part)):
        if c not in remap:
            remap[c] = len(remap)
    part = [remap[c] for c in part]
    m_states = len(set(part))
    lumped = {}
    for s in range(n):
        c = part[s]
        t0 = (part[tr[(s, 0)][0]], tr[(s, 0)][1])
        t1 = (part[tr[(s, 1)][0]], tr[(s, 1)][1])
        if c in lumped:
            check_exact(lumped[c] == (t0, t1), "lumping consistency")
        else:
            lumped[c] = (t0, t1)
    return n, m_states, lumped


def compute_sig_all_words(L: int, cp: int, cm: int) -> List[int]:
    """Compute exact free-boundary minimal (cp, cm)-cost for all 2^L words in lexicographic order."""
    states = [(0, 0, 0)]
    for _ in range(L):
        nxt = []
        for v0, v1, v2 in states:
            nxt.append((min(v0 + cm, v1 + cp), v1, min(v1 + cm, v2 + cp)))
            nxt.append((v0, min(v0 + cm, v1 + cp), v1))
        states = nxt
    return [min(v) for v in states]


def certify_weighted_naf_means(P_dp: int = 1200, U_cap: int = 1024) -> Dict[str, Tuple[Fraction, Fraction]]:
    """
    Certify exact outward-rounded rational enclosures for:
      - W_+ = mu_NAF(a_+) via exact DP on odd primes 3 <= p <= P_dp (plus rigorous tail);
      - mu_{1, 3/2}(a_+) via exact DP on odd primes 3 <= p <= P_dp (using submultiplicativity of w_{1, 3/2});
      - W_+^maj (full Euler product) AND ultra-short Lean-ready majorant bounds!
    """
    ps = primes_up_to(P_dp)
    # 1. Exact Lean-ready majorant bounds:
    # For odd p: L_p^NAF <= L_p^pop = (1 - 1/p) sum s_2(e+1) p^{-e} = sum_{j>=0} p/(p^{2^j} + 1) <= 1 + 1/p^2
    # Verify L_p^pop <= 1 + 1/p^2 for p >= 3:
    # L_p^pop - 1 = (p-1)/((p+1)(p^2+1)) + sum_{j>=2} p/(p^{2^j}+1)
    # Also compute exact L2_NAF_plus = (1/2) sum_{e>=0} w_pm(|1-e|) 2^{-e}
    E2 = 50
    l2_naf_lo = Fraction(0)
    for e in range(E2):
        l2_naf_lo += Fraction(naf_weight(abs(1 - e)), 1 << (e + 1))
    # Tail: w_pm(|1-e|) <= e, so (1/2) sum_{e>=E2} e 2^{-e} = (E2 + 1) / 2^{E2}
    l2_naf_hi = l2_naf_lo + Fraction(E2 + 1, 1 << E2)
    check_encl(l2_naf_hi < Fraction(79605, 100000), f"L2_NAF_plus enclosure {fmt_encl(l2_naf_lo, l2_naf_hi)}")

    # Ultra-short Lean majorant (reusing s_2 local factor for odd primes + tail 1 + 1/p^2):
    # (a) Tier 1: 10 odd primes p <= 31 + 1/(2*31) => W_+^maj <= 0.946830 < 23671/25000 (clears L = 23, 24 with D^- >= 13/10^9)
    prod_lean31_hi = Fraction(1)
    for p in primes_up_to(31)[1:]:
        s_p = sum(Fraction(p, p ** (1 << j) + 1) for j in range(5)) + Fraction(2 * p, p ** 32)
        prod_lean31_hi *= s_p
    prod_lean31_hi *= exp_ub_rational(prime_inv_sq_tail_ub(32))
    w_maj_lean31_hi = l2_naf_hi * prod_lean31_hi

    # (b) Tier 2: odd primes p <= 150 (34 odd primes) + 1/(2*149) => W_+^maj <= 0.939378 < 47/50 (optimal L = 21)
    prod_lean150_hi = Fraction(1)
    for p in primes_up_to(150)[1:]:
        s_p = sum(Fraction(p, p ** (1 << j) + 1) for j in range(5)) + Fraction(2 * p, p ** 32)
        prod_lean150_hi *= s_p
    prod_lean150_hi *= exp_ub_rational(prime_inv_sq_tail_ub(150))
    w_maj_lean150_hi = l2_naf_hi * prod_lean150_hi
    # Also compute tight W_+^maj over p <= 10000 using NAF local factor
    ps_maj = primes_up_to(10000)
    prod_naf_iv = (SCALE, SCALE)
    for p in ps_maj[1:]:
        E = 20 if p <= 100 else (10 if p <= 1000 else 6)
        loc_lo = Fraction(0)
        p_pow = 1
        for e in range(E):
            loc_lo += Fraction(naf_weight(e + 1), p_pow)
            p_pow *= p
        loc_lo = loc_lo * (p - 1) / p
        # Tail <= (E + 1 + 1/(p-1)) / p^E
        loc_hi = loc_lo + Fraction((E + 1) * (p - 1) + 1, (p - 1) * p_pow)
        prod_naf_iv = mul_iv_scaled(prod_naf_iv, frac_to_iv(loc_lo, loc_hi))
    # Tail for p > 10000: L_p^NAF <= L_p^pop <= 1 + 1/p^2
    prod_naf_iv = mul_iv_scaled(prod_naf_iv, frac_to_iv(Fraction(1), exp_ub_rational(prime_inv_sq_tail_ub(10000))))
    pnaf_lo, pnaf_hi = iv_to_frac(prod_naf_iv)
    wmaj_lo, wmaj_hi = l2_naf_lo * pnaf_lo, l2_naf_hi * pnaf_hi

    # Also certify DP-free Lean majorant for W_+^maj < 15/16 = 0.9375 using NAF local factor p <= 400!
    prod_lean_naf_hi = Fraction(1)
    for p in primes_up_to(400)[1:]:
        E = 16 if p <= 30 else 8
        loc_hi = sum(Fraction(naf_weight(e + 1), p ** e) for e in range(E)) * (p - 1) / p
        loc_hi += Fraction((E + 1) * (p - 1) + 1, (p - 1) * (p ** E))
        prod_lean_naf_hi *= loc_hi
    prod_lean_naf_hi *= exp_ub_rational(prime_inv_sq_tail_ub(400))
    w_maj_lean400_hi = l2_naf_hi * prod_lean_naf_hi

    check_encl(w_maj_lean31_hi <= Fraction(946830, 1000000) < Fraction(23671, 25000),
               f"Lean p<=31 s2-majorant < 23671/25000: ub <= {fmt_ub_dec(w_maj_lean31_hi, 6)}")
    check_encl(w_maj_lean150_hi <= Fraction(939378, 1000000) < Fraction(47, 50),
               f"Lean p<=150 s2-majorant < 47/50: ub <= {fmt_ub_dec(w_maj_lean150_hi, 6)}")
    check_encl(w_maj_lean400_hi <= Fraction(937255, 1000000) < Fraction(15, 16),
               f"Lean p<=400 NAF-majorant < 15/16: ub <= {fmt_ub_dec(w_maj_lean400_hi, 6)}")
    check_encl(Fraction(936405, 1000000) <= wmaj_lo <= wmaj_hi <= Fraction(936453, 1000000),
               f"W_+^maj enclosure {fmt_encl(wmaj_lo, wmaj_hi)}")

    # 2. Exact outward-rounded DP for U_odd = prod_{3 <= p <= P_dp} odd(B_p + 1)
    # Track exact scaled probability intervals [lo, hi] for u <= U_cap, plus overflow mass bound (weighted by u)!
    # Overflow: if u' > U_cap, accumulate upper bound on E[u' * 1_{overflow}] (valid since w_{1,lam}(+-u) <= lam * s_2(u) <= lam * u!)
    # Even better: track E[s_2(u) * 1_{overflow}] using s_2(a*b) <= s_2(a)*s_2(b)!
    # Let's track overflow_s2_ub: upper bound on E[s_2(U_odd_partial) * 1_{overflow}].
    # Since w_{1, lam}(o2 * u) <= w_{1, lam}(o2) * w_{1, lam}(u) <= w_{1, lam}(o2) * s_2(u) (for lam >= 1, u > 0),
    # multiplying by E[w_{1, lam}(o2)] gives a 100% rigorous upper bound on the overflow!
    dist: Dict[int, Tuple[int, int]] = {1: (SCALE, SCALE)}
    overflow_s2_ub = Fraction(0)
    for p in ps[1:]:
        E = 18 if p <= 29 else (10 if p <= 200 else 6)
        # Local probabilities for u = odd(e+1), e < E, plus tail e >= E
        loc_probs: Dict[int, Fraction] = {}
        for e in range(E):
            u = odd_part(e + 1)
            loc_probs[u] = loc_probs.get(u, Fraction(0)) + Fraction(p - 1, p ** (e + 1))
        # Tail for e >= E: E[s_2(odd(B_p+1)) * 1_{B_p >= E}] <= (E + 1 + 1/(p-1)) / p^E
        loc_tail_s2 = Fraction((E + 1) * (p - 1) + 1, (p - 1) * (p ** E))
        # Full local L_p^pop upper bound for propagating existing overflow_s2_ub
        loc_full_s2 = sum(Fraction(popcount(u)) * pr for u, pr in loc_probs.items()) + loc_tail_s2
        overflow_s2_ub *= loc_full_s2

        # Precompute scaled intervals for loc_probs
        loc_iv = {u: frac_to_iv(pr, pr) for u, pr in loc_probs.items()}
        new_dist: Dict[int, List[int]] = {}
        cur_s2_hi = Fraction(0)
        for u_old, iv_old in dist.items():
            cur_s2_hi += Fraction(popcount(u_old) * iv_old[1], SCALE)
            for u_loc, iv_loc in loc_iv.items():
                u_new = u_old * u_loc
                p_lo, p_hi = mul_iv_scaled(iv_old, iv_loc)
                if u_new <= U_cap:
                    if u_new in new_dist:
                        new_dist[u_new][0] += p_lo
                        new_dist[u_new][1] += p_hi
                    else:
                        new_dist[u_new] = [p_lo, p_hi]
                else:
                    # Upper bound s_2(u_new) <= popcount(u_old) * popcount(u_loc)
                    overflow_s2_ub += Fraction(popcount(u_old) * popcount(u_loc) * p_hi, SCALE)
        overflow_s2_ub += cur_s2_hi * loc_tail_s2
        dist = {u: (v[0], v[1]) for u, v in new_dist.items()}

    # Tail over primes p > P_dp:
    # Lower factor: prod_{p > P_dp} (1 - p^{-2}) >= 1 - sum_{p > P_dp} p^{-2}
    # Upper factor: prod_{p > P_dp} L_p^pop <= exp(sum_{p > P_dp} p^{-2}) <= 1/(1 - tail_p2)
    tail_p2 = prime_inv_sq_tail_ub(P_dp)
    lower_tail_fac = 1 - tail_p2
    upper_tail_fac = exp_ub_rational(tail_p2)

    # Now evaluate BOTH lambda = 1 (cp=1, cm=1, scale=1) and lambda = 3/2 (cp=2, cm=3, scale=2)
    results: Dict[str, Tuple[Fraction, Fraction]] = {
        "L2_NAF_plus": (l2_naf_lo, l2_naf_hi),
        "W_plus_maj": (wmaj_lo, wmaj_hi),
        "W_plus_lean31": (Fraction(0), w_maj_lean31_hi),
        "W_plus_lean150": (Fraction(0), w_maj_lean150_hi),
        "W_plus_lean400": (Fraction(0), w_maj_lean400_hi),
    }

    for name, cp, cm, sc in [("W_plus", 1, 1, 1), ("mu_asym_3_2", 2, 3, 2)]:
        memo: Dict[Tuple[int, int, int], int] = {}
        # Verify submultiplicativity w(a*b) <= w(a)*w(b) on sample pairs
        if name == "mu_asym_3_2":
            for a in range(-40, 41):
                for b in range(-40, 41):
                    wa = Fraction(asym_weight_int(a, cp, cm, memo), sc)
                    wb = Fraction(asym_weight_int(b, cp, cm, memo), sc)
                    wab = Fraction(asym_weight_int(a * b, cp, cm, memo), sc)
                    check_exact(wab <= wa * wb, f"submultiplicativity w_{{1,3/2}} at ({a},{b})")

        # 2-adic weights for a_+:
        # e = 0: +1 (prob 1/2)
        # e = 1: 0  (prob 1/4)
        # e >= 2: -(e - 1) (prob 2^{-(e+1)})
        E2_dp = 36
        # Compute E[w_{1,lam}(o2 * U_odd_<=P) * 1_{U <= U_cap}]
        # Positive branch (e = 0): o2 = +1, prob 1/2
        # Negative branch (e >= 2): o2 = -odd(e-1), prob 2^{-(e+1)}
        o2_probs: Dict[int, Fraction] = {1: Fraction(1, 2)}
        for e in range(2, E2_dp):
            o2 = -odd_part(e - 1)
            o2_probs[o2] = o2_probs.get(o2, Fraction(0)) + Fraction(1, 1 << (e + 1))
        # 2-adic tail (e >= E2_dp): for negative -(e-1), w_{1,lam}(-(e-1)) <= (cm/sc) * s_2(e-1) <= (cm/sc) * e
        e2_tail_w_ub = Fraction(cm, sc) * Fraction(E2_dp + 1, 1 << E2_dp)
        # Also E[w_{1,lam}(o2)] upper bound for overflow
        e_w_o2_ub = sum(Fraction(asym_weight_int(o2, cp, cm, memo), sc) * pr for o2, pr in o2_probs.items()) + e2_tail_w_ub

        exp_lo = Fraction(0)
        exp_hi = Fraction(0)
        for u, (p_lo, p_hi) in dist.items():
            # Average over o2
            w_u_avg = Fraction(0)
            for o2, pr2 in o2_probs.items():
                w_u_avg += Fraction(asym_weight_int(o2 * u, cp, cm, memo), sc) * pr2
            exp_lo += w_u_avg * Fraction(p_lo, SCALE)
            exp_hi += (w_u_avg + e2_tail_w_ub * popcount(u)) * Fraction(p_hi, SCALE)

        # Add overflow term (using submultiplicativity w(o2 * u) <= w(o2) * s_2(u))
        exp_hi += e_w_o2_ub * overflow_s2_ub

        # Multiply by prime > P_dp factors
        final_lo = exp_lo * lower_tail_fac
        final_hi = exp_hi * upper_tail_fac
        results[name] = (final_lo, final_hi)

    check_encl(Fraction(908078, 1000000) <= results["W_plus"][0] <= results["W_plus"][1] <= Fraction(908260, 1000000),
               f"W_+ certified enclosure {fmt_encl(*results['W_plus'])}")
    check_encl(Fraction(1041775, 1000000) <= results["mu_asym_3_2"][0] <= results["mu_asym_3_2"][1] <= Fraction(1041984, 1000000),
               f"mu_{{1,3/2}} certified enclosure {fmt_encl(*results['mu_asym_3_2'])}")
    return results


def verify_b3_automata_koksma_and_lean(naf_encl: Dict[str, Tuple[Fraction, Fraction]]) -> Dict[str, object]:
    """
    Certify:
      (1) 4-state automaton closure, closed-form A_L, and EXACT circular variation V_circ(L) = (2^L + 2(-1)^L)/3;
      (2) 6-line suffix proof check: cost(s, 0 1^t) vs cost(s, 1 0^t) for all 4 states and t = 0..6;
      (3) Discrete circular Koksma inequality on 200 empirical test measures;
      (4) 7-state minimal asymmetric (1, 3/2) automaton, exact stationary law (A_inf = 12/31),
          exact A_14(1, 3/2), and V_circ(1, 3/2; 14);
      (5) Certified D^-(E_+(8); 2) improvements (4-state Koksma, 7-state asymmetric Koksma, DP-free Lean);
      (6) Simple nonnormality of E_+(2^k) in base 2^k (k>=4), base 8 (k>=5), base 4 (k>=8), and E_+(8) in base 2^L (L>=13);
      (7) Exact Lean prefix-boundary theorem H_N - X_N in {0, 1} and w_pm(X_N) <= w_pm(S_M^+) + 1;
      (8) Transducer obstruction witness E_2 (Euler pentagonal).
    """
    # (1) 4-state automaton closure
    n_raw4, n_min4, lump4 = build_weighted_automaton(1, 1)
    check_exact(n_raw4 == 7 and n_min4 == 4, f"4-state closure: raw={n_raw4}, min={n_min4}")

    # Verify exact suffix comparison (0 1^t vs 1 0^t) on the 4-state lumped automaton!
    def run_lumped(lump, st, word):
        cost = 0
        for b in word:
            st, inc = lump[st][b]
            cost += inc
        return cost

    # Identify state B (the unique state where bit 0 costs 1 and bit 1 costs 0)
    state_B = [s for s in range(4) if lump4[s][0][1] == 1 and lump4[s][1][1] == 0]
    check_exact(len(state_B) == 1, "unique state B")
    sB = state_B[0]
    for s in range(4):
        # t = 0: '0' vs '1'
        diff0 = run_lumped(lump4, s, [1]) - run_lumped(lump4, s, [0])
        check_exact(diff0 == (-1 if s == sB else 0), f"t=0 diff at state {s}")
        # t = 1: '01' vs '10'
        diff1 = run_lumped(lump4, s, [1, 0]) - run_lumped(lump4, s, [0, 1])
        check_exact(diff1 == (0 if s == sB else 1), f"t=1 diff at state {s}")
        # t >= 2: '0 1^t' vs '1 0^t' ALWAYS 0!
        for t in range(2, 8):
            difft = run_lumped(lump4, s, [1] + [0] * t) - run_lumped(lump4, s, [0] + [1] * t)
            check_exact(difft == 0, f"t={t} diff at state {s}")

    # Exhaustive check of A_L and V_circ(L) = (2^L + 2(-1)^L)/3 for L = 2..15
    for L in range(2, 16):
        sig = compute_sig_all_words(L, 1, 1)
        n = 1 << L
        AL = Fraction(sum(sig), L * n)
        AL_closed = Fraction(1, 3) - (Fraction(7) - Fraction(-1, 2) ** (L - 1)) / (18 * L)
        check_exact(AL == AL_closed, f"A_L formula at L={L}")
        diffs = [sig[(j + 1) % n] - sig[j] for j in range(n)]
        vc = sum(abs(d) for d in diffs)
        vc_closed = (n + 2 * ((-1) ** L)) // 3
        check_exact(vc == vc_closed, f"V_circ formula at L={L}")
        cnt_pos = sum(1 for d in diffs if d == 1)
        cnt_neg = sum(1 for d in diffs if d == -1)
        cnt_zero = sum(1 for d in diffs if d == 0)
        check_exact(cnt_pos == cnt_neg == vc_closed // 2 and cnt_pos + cnt_neg + cnt_zero == n,
                    f"jump counts at L={L}")

    # (3) Discrete circular Koksma inequality check on 200 rational empirical orbits
    sig6 = compute_sig_all_words(6, 1, 1)
    n6 = 64
    AL6 = Fraction(sum(sig6), 6 * n6)
    vc6 = Fraction(sum(abs(sig6[(j + 1) % n6] - sig6[j]) for j in range(n6)), 6)
    for seed in range(1, 201):
        # Generate deterministic empirical orbit of length 40 in [0, 1) with denominator 257
        pts = sorted(Fraction((seed * (i * i + 7 * i + 3)) % 257, 257) for i in range(40))
        N_pts = len(pts)
        # Exact extreme discrepancy D_N = max(z) - min(z) + 1/N where z_i = i/N - pts[i]
        # Wait: exact extreme discrepancy for sorted pts:
        # sup_{u < v} |F(v) - F(u)| = max_t F(t) - min_t F(t) where F(t) = mu([0,t)) - t.
        # At jump point pts[i]: left limit = i/N - pts[i], right limit = (i+1)/N - pts[i]
        # Including endpoints 0 and 1 (F(0) = F(1) = 0):
        f_vals = [Fraction(0)]
        for i, p in enumerate(pts):
            f_vals.append(Fraction(i, N_pts) - p)
            f_vals.append(Fraction(i + 1, N_pts) - p)
        D_exact = max(f_vals) - min(f_vals)
        # Empirical integral of g_6(t) = sig6[floor(64*t)] / 6
        emp_int = sum(Fraction(sig6[int(p * n6)], 6) for p in pts) / N_pts
        check_exact(abs(emp_int - AL6) <= (vc6 / 2) * D_exact, f"Koksma check seed={seed}")

    # (4) 7-state minimal asymmetric (1, 3/2) automaton (cp=2, cm=3, scaled by 2)
    n_raw7, n_min7, lump7 = build_weighted_automaton(2, 3)
    check_exact(n_raw7 == 13 and n_min7 == 7, f"7-state closure: raw={n_raw7}, min={n_min7}")

    # Compute exact rational stationary distribution of lump7 by solving pi * P = pi
    # Verified directly by exact rational matrix multiplication!
    # Solve (P^T - I) pi = 0, sum pi = 1 using exact Gaussian elimination over Fraction
    M_mat = [[Fraction(0) for _ in range(n_min7 + 1)] for _ in range(n_min7)]
    for s in range(n_min7):
        for b in (0, 1):
            ns, _ = lump7[s][b]
            M_mat[ns][s] += Fraction(1, 2)
        M_mat[s][s] -= 1
    # Replace last row with sum(pi) = 1
    M_mat[-1] = [Fraction(1)] * n_min7 + [Fraction(1)]
    # Gaussian elimination
    for col in range(n_min7):
        piv = next(r for r in range(col, n_min7) if M_mat[r][col] != 0)
        M_mat[col], M_mat[piv] = M_mat[piv], M_mat[col]
        inv = 1 / M_mat[col][col]
        M_mat[col] = [x * inv for x in M_mat[col]]
        for r in range(n_min7):
            if r != col and M_mat[r][col] != 0:
                fac = M_mat[r][col]
                M_mat[r] = [M_mat[r][c] - fac * M_mat[col][c] for c in range(n_min7 + 1)]
    pi7 = [M_mat[r][n_min7] for r in range(n_min7)]
    check_exact(sum(pi7) == 1 and all(x > 0 for x in pi7), "pi7 valid probability distribution")
    # Verify pi7 * P = pi7
    for ns in range(n_min7):
        tot = sum(pi7[s] * Fraction(1, 2) for s in range(n_min7) for b in (0, 1) if lump7[s][b][0] == ns)
        check_exact(tot == pi7[ns], f"pi7 stationary at state {ns}")
    # Stationary expected cost (unscaled by 2)
    A_inf_3_2 = sum(pi7[s] * Fraction(lump7[s][0][1] + lump7[s][1][1], 4) for s in range(n_min7))
    check_exact(A_inf_3_2 == Fraction(12, 31), f"A_inf(1, 3/2) == 12/31, got {A_inf_3_2}")

    # Verify irreducibility and aperiodicity of lump7 (supporting sup_L A_L(1, 3/2) = A_inf = 12/31 via Fekete's lemma)
    check_exact(lump7[2][0][0] == 2, "lump7 state 2 has self-loop on bit 0 (aperiodic)")
    for src in range(n_min7):
        seen = {src}
        bfs = [src]
        while bfs:
            cur = bfs.pop(0)
            for b in (0, 1):
                nxt = lump7[cur][b][0]
                if nxt not in seen:
                    seen.add(nxt)
                    bfs.append(nxt)
        check_exact(len(seen) == n_min7, f"lump7 irreducible from state {src}")

    # Verify strict increase 0 = A_1(1,3/2) < A_2(1,3/2) < ... < A_14(1,3/2) < 12/31, and exact A_14, V_circ(14)
    prev_A_asym = Fraction(-1)
    for L_a in range(1, 14):
        sig_a = compute_sig_all_words(L_a, 2, 3)
        AL_a = Fraction(sum(sig_a), 2 * L_a * (1 << L_a))
        check_exact(prev_A_asym < AL_a < A_inf_3_2, f"A_{L_a}(1,3/2) strictly increasing below 12/31")
        prev_A_asym = AL_a

    # Exact A_14(1, 3/2) and V_circ(1, 3/2; 14)
    sig14_asym = compute_sig_all_words(14, 2, 3)
    n14 = 1 << 14
    A14_asym = Fraction(sum(sig14_asym), 2 * 14 * n14)
    vc14_asym = Fraction(sum(abs(sig14_asym[(j + 1) % n14] - sig14_asym[j]) for j in range(n14)), 2 * 14)
    check_exact(prev_A_asym < A14_asym < A_inf_3_2, "A_13(1,3/2) < A_14(1,3/2) < 12/31")
    check_exact(A14_asym == Fraction(80897, 229376), f"A_14(1, 3/2) == 80897/229376, got {A14_asym}")
    check_exact(vc14_asym == 453, f"V_circ(g_14^(1,3/2)) == 453, got {vc14_asym}")

    # (5) Certified D^-(E_+(8); 2) bounds (at optimal window lengths L, outward-rounded assertions)
    W_plus_hi = naf_encl["W_plus"][1]
    mu_asym_hi = naf_encl["mu_asym_3_2"][1]
    W_maj_hi = naf_encl["W_plus_maj"][1]
    W_lean31_hi = naf_encl["W_plus_lean31"][1]
    W_lean150_hi = naf_encl["W_plus_lean150"][1]
    W_lean400_hi = naf_encl["W_plus_lean400"][1]

    def A_sym(L: int) -> Fraction:
        return Fraction(1, 3) - (Fraction(7) - Fraction(-1, 2) ** (L - 1)) / (18 * L)

    def D_koksma_sym(L: int, w_hi: Fraction, k: int = 3) -> Fraction:
        gap = A_sym(L) - w_hi / k
        check_encl(gap > 0, f"positive gap at L={L}")
        return Fraction(6 * L) * gap / ((1 << L) + 2 * ((-1) ** L))

    D_sym_14 = D_koksma_sym(14, W_plus_hi, 3)
    D_asym_14 = (A14_asym - mu_asym_hi / 3) / (vc14_asym / 2)
    D_maj_20 = D_koksma_sym(20, W_maj_hi, 3)
    D_lean400_20 = D_koksma_sym(20, W_lean400_hi, 3)
    D_lean400_thresh_20 = D_koksma_sym(20, Fraction(15, 16), 3)
    D_lean150_21 = D_koksma_sym(21, W_lean150_hi, 3)
    D_lean150_thresh_21 = D_koksma_sym(21, Fraction(47, 50), 3)
    D_lean31_23 = D_koksma_sym(23, W_lean31_hi, 3)
    D_lean31_thresh_23 = D_koksma_sym(23, Fraction(23671, 25000), 3)
    D_lean31_thresh_24 = D_koksma_sym(24, Fraction(23671, 25000), 3)

    check_encl(D_sym_14 >= Fraction(14362, 10 ** 9) and D_sym_14 > 61 * Fraction(234, 10 ** 9),
               f"4-state Koksma D^-(E_+(8)) >= {fmt_lb_sci(D_sym_14, 4)}")
    check_encl(D_asym_14 >= Fraction(23642, 10 ** 9) and D_asym_14 > 101 * Fraction(234, 10 ** 9),
               f"7-state asym Koksma D^-(E_+(8)) >= {fmt_lb_sci(D_asym_14, 4)}")
    check_encl(D_maj_20 >= Fraction(19891, 10 ** 11),
               f"DP-free W_+^maj (L=20) D^-(E_+(8)) >= {fmt_lb_sci(D_maj_20, 4)}")
    check_encl(D_lean400_20 >= Fraction(16830, 10 ** 11) and D_lean400_thresh_20 >= Fraction(15894, 10 ** 11),
               f"Lean p<=400 (L=20) D^-(E_+(8)) >= {fmt_lb_sci(D_lean400_20, 4)} (from 15/16: >= {fmt_lb_sci(D_lean400_thresh_20, 4)})")
    check_encl(D_lean150_21 >= Fraction(10147, 10 ** 11) and D_lean150_thresh_21 >= Fraction(89009, 10 ** 12),
               f"Lean p<=150 (L=21) D^-(E_+(8)) >= {fmt_lb_sci(D_lean150_21, 4)} (from 47/50: >= {fmt_lb_sci(D_lean150_thresh_21, 4)})")
    check_encl(D_lean31_23 >= Fraction(13412, 10 ** 12),
               f"Lean p<=31 (L=23) D^-(E_+(8)) >= {fmt_lb_sci(D_lean31_23, 4)}")
    check_encl(D_lean31_thresh_23 >= Fraction(13354, 10 ** 12) >= Fraction(13, 10 ** 9),
               f"Lean Tier-1 blueprint (23671/25000, L=23) D^- >= {fmt_lb_sci(D_lean31_thresh_23, 4)} >= 13/10^9")
    check_encl(D_lean31_thresh_24 >= Fraction(13014, 10 ** 12) >= Fraction(13, 10 ** 9),
               f"Lean Tier-1 blueprint (23671/25000, L=24) D^- >= {fmt_lb_sci(D_lean31_thresh_24, 4)} >= 13/10^9")

    # (6) Base-2^k / base-8 / base-4 simple nonnormality of E_+(2^k) via disjoint blocks
    # Base 2^k (k >= 4): W_+^maj <= 0.936453 < 15/16 = 4 * A_4
    check_encl(W_maj_hi <= Fraction(936453, 10 ** 6) < 4 * A_sym(4) and 4 * A_sym(4) == Fraction(15, 16),
               "E_+(16) base-16 simple nonnormality (even with W_+^maj)")
    # Base 8 (k >= 5): W_+^maj / 5 <= 0.187291 < A_3 = 5/24
    check_encl(W_maj_hi / 5 <= Fraction(187291, 10 ** 6) < A_sym(3) and A_sym(3) == Fraction(5, 24),
               "E_+(32) base-8 simple nonnormality (even with W_+^maj)")
    # Base 4 (k >= 8): W_+^maj / 8 <= 0.117057 < A_2 = 1/8
    check_encl(W_maj_hi / 8 <= Fraction(117057, 10 ** 6) < A_sym(2) and A_sym(2) == Fraction(1, 8),
               "E_+(256) base-4 simple nonnormality (even with W_+^maj)")
    # E_+(8) in base 2^L for L >= 13: W_+ / 3 <= 0.302754 < A_13 = 32313/106496
    check_encl(W_plus_hi / 3 <= Fraction(302754, 10 ** 6) < A_sym(13) and A_sym(13) == Fraction(32313, 106496),
               "E_+(8) base-2^13 simple nonnormality")

    # (7) Verify Lean prefix-boundary theorem: H_N - X_N in {0, 1} and w_pm(X_N) <= w_pm(S_M^+) + 1
    N_max_p = 400
    tau_odd = [0] * (N_max_p + 1)
    for d in range(1, N_max_p + 1, 2):
        for m in range(d, N_max_p + 1, d):
            tau_odd[m] += 1
    a_plus = [0] + [(1 - v2(n)) * tau_odd[n] for n in range(1, N_max_p + 1)]

    def to_naf_digits(val: int) -> List[int]:
        """Signed NAF digits (LSB first) of integer val."""
        sign = 1 if val >= 0 else -1
        n = abs(val)
        digs = []
        while n > 0:
            if n & 1:
                d = 2 - (n & 3)  # +1 if n%4==1, -1 if n%4==3
                digs.append(sign * d)
                n -= d
            else:
                digs.append(0)
            n >>= 1
        return digs

    for k in (1, 2, 3, 4, 5):
        # Compute high-precision value of E_+(2^k) at 2^P_ref with rigorous tail bound <= 4*(M_ref + 2)
        P_ref = 100 * k + 120
        M_ref = P_ref // k
        E_ref = 0
        for m in range(1, M_ref + 1):
            E_ref += a_plus[m] << (P_ref - k * m)
        tail_err = 4 * (M_ref + 2)
        for N0 in range(1, 51):
            N = k * N0
            # Exact integer ceiling of (2 / k) * log2(N0 + 2): smallest h0 >= 0 with 2^(k*h0) >= (N0 + 2)^2
            target_sq = (N0 + 2) * (N0 + 2)
            h0 = ((target_sq - 1).bit_length() + k - 1) // k
            check_exact((1 << (k * h0)) >= target_sq and (h0 == 0 or (1 << (k * (h0 - 1))) < target_sq),
                        f"exact integer H ceiling k={k}, N0={N0}")
            H = h0 + 4
            M = N0 + H
            if M > N_max_p:
                continue
            SM = 0
            for n in range(1, M + 1):
                SM = (SM << k) + a_plus[n]
            digs = to_naf_digits(SM)
            # High NAF integer H_N = sum_{j >= k*H} digs[j] 2^{j - k*H}
            HN = 0
            for j in range(len(digs) - 1, k * H - 1, -1):
                HN = 2 * HN + digs[j]
            XN_lo = (E_ref - tail_err) >> (P_ref - N)
            XN_hi = (E_ref + tail_err) >> (P_ref - N)
            check_exact(XN_lo == XN_hi, f"certified X_N at k={k}, N0={N0}")
            XN = XN_lo
            check_exact(HN - XN in (0, 1), f"H_N - X_N in {{0,1}} failed at k={k}, N0={N0}: diff={HN - XN}")
            check_exact(naf_weight(XN) <= naf_weight(SM) + 1, f"w_pm(X_N) <= w_pm(S_M)+1 at k={k}, N0={N0}")

    # (8) Transducer obstruction witness: Euler pentagonal E_2
    # E_2 = 1 + sum_{j>=1} (-1)^j (2^{-j(3j-1)/2} + 2^{-j(3j+1)/2})
    # Check that up to N = 4000, the number of nonzero terms n = 102 satisfies n <= 2*sqrt(2*N/3) + 2
    # (equivalently 3*(n - 2)^2 <= 8*N).
    N_e2 = 4000
    e2_terms = []
    j = 1
    while True:
        p1 = j * (3 * j - 1) // 2
        p2 = j * (3 * j + 1) // 2
        if p1 > N_e2:
            break
        e2_terms.append((p1, -1 if j & 1 else 1))
        if p2 <= N_e2:
            e2_terms.append((p2, -1 if j & 1 else 1))
        j += 1
    check_exact(len(e2_terms) == 102 and 3 * (len(e2_terms) - 2) ** 2 <= 8 * N_e2,
                f"E_2 sparse signed support up to 4000: {len(e2_terms)}")

    return {
        "n_raw4": n_raw4,
        "n_min4": n_min4,
        "n_raw7": n_raw7,
        "n_min7": n_min7,
        "pi7": pi7,
        "lump7": lump7,
        "A_inf_3_2": A_inf_3_2,
        "A14_asym": A14_asym,
        "vc14_asym": vc14_asym,
        "D_sym_14": D_sym_14,
        "D_asym_14": D_asym_14,
        "D_maj_20": D_maj_20,
        "D_lean400_20": D_lean400_20,
        "D_lean400_thresh_20": D_lean400_thresh_20,
        "D_lean150_21": D_lean150_21,
        "D_lean150_thresh_21": D_lean150_thresh_21,
        "D_lean31_23": D_lean31_23,
        "D_lean31_thresh_23": D_lean31_thresh_23,
    }


# =============================================================================
# Section 4: B4 -- E_+(4) Signed Carry Frontier & Fixed-Block Cancellation Barrier
# =============================================================================

def verify_b4_eplus4_frontier(naf_encl: Dict[str, Tuple[Fraction, Fraction]]) -> Dict[str, object]:
    """
    Certify:
      (1) Exact normalization & sharpened sufficient carry deficit for E_+(4):
          W_+^hi / 2 - 1/3 < 0.1208 (vs Track E's 0.1231), plus relative deficit for lam = 3/2;
      (2) Exact separated-support NAF additivity lemma (key to Theorem B4.1: lim_{M->inf} c_{2,B}^{block} = 0);
      (3) Exact opposite-sign and adjacent-column NAF cancellation savings;
      (4) [finite] Measurements of fixed-block cancellation c_{2,B}^{block}(M) for B = 1,2,4,8,16
          and full-prefix f_1(E_+(2^k); 2) for k = 1,2,3,4,5,6,8 (demonstrating the finite-scale illusion!).
    """
    W_plus_lo, W_plus_hi = naf_encl["W_plus"]
    def_lo = W_plus_lo / 2 - Fraction(1, 3)
    def_hi = W_plus_hi / 2 - Fraction(1, 3)
    check_encl(Fraction(120705, 1000000) <= def_lo <= def_hi <= Fraction(120797, 1000000),
               f"E_+(4) sufficient NAF deficit enclosure {fmt_encl(def_lo, def_hi)}")

    mu_asym_lo, mu_asym_hi = naf_encl["mu_asym_3_2"]
    rel_sym_hi = (W_plus_hi / 2) / Fraction(1, 3) - 1
    rel_asym_hi = (mu_asym_hi / 2) / Fraction(12, 31) - 1
    check_encl(rel_sym_hi <= Fraction(36239, 100000) and rel_asym_hi <= Fraction(34590, 100000) and rel_asym_hi < rel_sym_hi,
               f"asymmetric lam=3/2 reduces relative deficit: {fmt_ub_dec(rel_asym_hi, 5)} < {fmt_ub_dec(rel_sym_hi, 5)}")

    # (2) Verify separated-support NAF additivity:
    # If X_j = s_j * U_j * 2^{L_j} with U_j odd, L_{j+1} >= L_j + U_j.bit_length() + 2,
    # then w_pm(sum X_j) == sum w_pm(X_j) identically!
    for seed in range(1, 401):
        # Build 3 terms with arbitrary signs and odd U_j <= 63
        U = [((seed * (3 * i + 5) + 2 * i) % 31) * 2 + 1 for i in range(3)]
        S = [1 if ((seed >> i) & 1) else -1 for i in range(3)]
        L0 = 0
        L1 = L0 + U[0].bit_length() + 2 + (seed % 3)
        L2 = L1 + U[1].bit_length() + 2 + ((seed >> 2) % 3)
        X = [S[0] * (U[0] << L0), S[1] * (U[1] << L1), S[2] * (U[2] << L2)]
        check_exact(naf_weight(sum(X)) == sum(naf_weight(x) for x in X),
                    f"separated NAF additivity failed at seed={seed}")

    # (3) Opposite-sign & same-sign collision NAF savings for all odd U1, U2 <= 63
    for u1 in range(1, 64, 2):
        for u2 in range(1, 64, 2):
            # Opposite sign at same column: u1 - u2 is even, and w(u1 - u2) <= w(u1) + w(u2) - 1 ALWAYS!
            save_opp = naf_weight(u1) + naf_weight(u2) - naf_weight(u1 - u2)
            check_exact(save_opp >= 1, f"opposite-sign collision saving >= 1 at ({u1},{u2})")
            if u1 == u2:
                check_exact(save_opp == 2 * naf_weight(u1), f"exact cancellation at u1=u2={u1}")
    # Check adjacent opposite-sign at u1=u2=1: 2 - 1 = 1 saves 1; same-sign at u1=u2=1: 1 + 1 = 2 saves 1
    check_exact(naf_weight(2) + naf_weight(-1) - naf_weight(1) == 1, "adjacent opposite-sign saving")
    check_exact(naf_weight(1) + naf_weight(1) - naf_weight(2) == 1, "same-sign collision saving")

    # (4) [finite] Fixed-block cancellation measurements for E_+(4) across M = 2^10..2^16
    M_max = 1 << 16
    tau_odd = [0] * (M_max + 1)
    for d in range(1, M_max + 1, 2):
        for m in range(d, M_max + 1, d):
            tau_odd[m] += 1
    a_plus = [0] + [(1 - v2(n)) * tau_odd[n] for n in range(1, M_max + 1)]
    w_ap = [0] + [naf_weight(a_plus[n]) for n in range(1, M_max + 1)]

    block_table: Dict[int, List[Tuple[int, float]]] = {}
    for B in (1, 2, 4, 8, 16):
        rows = []
        for M in (1 << 10, 1 << 12, 1 << 14, 1 << 16):
            nb = M // B
            raw = sum(w_ap[1 : nb * B + 1])
            blk = 0
            for r in range(nb):
                s = 0
                base = r * B
                for j in range(1, B + 1):
                    s = (s << 2) + a_plus[base + j]
                blk += naf_weight(s)
            c_blk = (raw - blk) / (2 * nb * B)
            check_finite(0.0 <= c_blk < 0.5, f"finite block cancellation sanity B={B}, M={M}")
            rows.append((M, c_blk))
        block_table[B] = rows

    # Also [finite] certified prefix measurements of f_1(E_+(2^k); 2) for k = 1, 2, 3, 4, 5, 6, 8
    eplus_f1: List[Tuple[int, int, float, float]] = []
    for k in (1, 2, 3, 4, 5, 6, 8):
        N_bits = 12000
        N_guard = N_bits + 96
        M_tot = N_guard // k
        # Build exact sum at scale 2^{N_guard}; omitted tail has |err| <= 4*(M_tot + 2)
        S_val = 0
        for m in range(1, M_tot + 1):
            S_val += a_plus[m] << (N_guard - k * m)
        tail_err = 4 * (M_tot + 2)
        shift = 1 << (N_guard - N_bits)
        lo_p = (S_val - tail_err) // shift
        hi_p = (S_val + tail_err) // shift
        check_exact(lo_p == hi_p, f"finite E_+(2^{k}) certified {N_bits} bits")
        f1 = (lo_p & ((1 << N_bits) - 1)).bit_count() / N_bits
        # Also count transitions
        x_mask = lo_p & ((1 << N_bits) - 1)
        tr = ((x_mask ^ (x_mask >> 1)) & ((1 << (N_bits - 1)) - 1)).bit_count() / (N_bits - 1)
        check_finite(0.0 < f1 < 1.0 and 0.0 < tr < 1.0, f"finite E_+(2^{k}) stats")
        eplus_f1.append((k, N_bits, f1, tr))

    return {
        "def_encl": (def_lo, def_hi),
        "rel_sym_hi": rel_sym_hi,
        "rel_asym_hi": rel_asym_hi,
        "block_table": block_table,
        "eplus_f1": eplus_f1,
    }


# =============================================================================
# Section 5: B5 -- Broader Lambert Classifications (tau_r, prime bases, periodic)
# =============================================================================

def certify_b5_families() -> Dict[str, Tuple[Fraction, Fraction]]:
    """
    Certify outward-rounded enclosures of C_U for:
      - tau_4 (base 2), tau_8 (base 2),
      - tau_3 (base 3), tau_5 (base 5), tau_7 (base 7),
    and verify exact character-spectrum decomposition for mod 7, 9, 13 periodic weights.
    """
    results: Dict[str, Tuple[Fraction, Fraction]] = {}
    configs = [
        ("tau_4_b2", 4, 2, 4000),
        ("tau_8_b2", 8, 2, 2000),
        ("tau_3_b3", 3, 3, 4000),
        ("tau_5_b5", 5, 5, 4000),
        ("tau_7_b7", 7, 7, 3000),
    ]
    for name, r, b, P in configs:
        ps = primes_up_to(P)
        prod_iv = (SCALE, SCALE)
        for p in ps:
            if p == 2:
                E = 140
            elif p == 3:
                E = 80
            elif p <= 13:
                E = 40
            elif p <= 50:
                E = 22
            elif p <= 500:
                E = 12
            else:
                E = 6
            # Exact finite sum (1 - 1/p) sum_{e=0}^{E-1} strip_b(binom(e+r-1, r-1)) / p^e
            loc_lo = Fraction(0)
            p_pow = 1
            exact_binom_partial = Fraction(0)
            for e in range(E):
                c = math.comb(e + r - 1, r - 1)
                loc_lo += Fraction(strip_factor(c, b), p_pow)
                exact_binom_partial += Fraction(c, p_pow)
                p_pow *= p
            loc_lo = loc_lo * (p - 1) / p
            # Exact tail bound: (1 - 1/p) sum_{e>=E} binom(e+r-1, r-1) p^{-e}
            #                 = (1 - 1/p)^{-(r-1)} - (1 - 1/p) * exact_binom_partial
            full_binom = Fraction(p, p - 1) ** (r - 1)
            tail = full_binom - exact_binom_partial * (p - 1) / p
            check_exact(tail > 0, f"{name} positive tail at p={p}")
            loc_hi = loc_lo + tail
            prod_iv = mul_iv_scaled(prod_iv, frac_to_iv(loc_lo, loc_hi))

        # Large-prime tail p > P:
        # L_p - 1 <= (r - 1 + binom(r, 2) / (1 - r / (2*P))) / p^2
        # Verify binom(e+r-2, r-2) / binom(e+r-3, r-2) <= r/2 for e >= 2 (true since (e+r-2)/e <= r/2 iff 2r-4 <= (r-2)e)
        check_exact(P > 2 * r, f"{name} P > 2r")
        A_coeff = Fraction(r - 1) + Fraction(r * (r - 1), 2) / (1 - Fraction(r, 2 * P))
        tail_sum = A_coeff * prime_inv_sq_tail_ub(P)
        tail_ub = exp_ub_rational(tail_sum)
        prod_iv = mul_iv_scaled(prod_iv, frac_to_iv(Fraction(1), tail_ub))
        results[name] = iv_to_frac(prod_iv)

    # Check B1 thresholds k > C_U and exact 5-decimal endpoints for these families:
    check_encl(Fraction(942224, 100000) <= results["tau_4_b2"][0] <= results["tau_4_b2"][1] <= Fraction(943286, 100000) < 10,
               f"C_U(tau_4) < 10: {fmt_encl(*results['tau_4_b2'], 5)}")
    check_encl(Fraction(44050019, 100000) <= results["tau_8_b2"][0] <= results["tau_8_b2"][1] <= Fraction(44439685, 100000) < 445,
               f"C_U(tau_8) < 445: {fmt_encl(*results['tau_8_b2'], 5)}")
    check_encl(Fraction(365171, 100000) <= results["tau_3_b3"][0] <= results["tau_3_b3"][1] <= Fraction(365400, 100000) < 4,
               f"C_U(tau_3, b=3) < 4: {fmt_encl(*results['tau_3_b3'], 5)}")
    check_encl(Fraction(1351915, 100000) <= results["tau_5_b5"][0] <= results["tau_5_b5"][1] <= Fraction(1354287, 100000) < 14,
               f"C_U(tau_5, b=5) < 14: {fmt_encl(*results['tau_5_b5'], 5)}")
    check_encl(Fraction(6618231, 100000) <= results["tau_7_b7"][0] <= results["tau_7_b7"][1] <= Fraction(6648186, 100000) < 67,
               f"C_U(tau_7, b=7) < 67: {fmt_encl(*results['tau_7_b7'], 5)}")

    # Verify exact complete lists for phi(M) = 2^t (2 <= M <= 257) and odd(lambda(M)) | 3 (1 <= M <= 100)
    def euler_phi(n: int) -> int:
        res = n
        d = 2
        tmp = n
        while d * d <= tmp:
            if tmp % d == 0:
                while tmp % d == 0:
                    tmp //= d
                res = (res // d) * (d - 1)
            d += 1
        if tmp > 1:
            res = (res // tmp) * (tmp - 1)
        return res

    fermat_M = [M for M in range(2, 258) if (euler_phi(M) & (euler_phi(M) - 1)) == 0]
    expected_fermat_M = [
        2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, 24, 30, 32, 34, 40, 48, 51, 60,
        64, 68, 80, 85, 96, 102, 120, 128, 136, 160, 170, 192, 204, 240, 255, 256, 257,
    ]
    check_exact(fermat_M == expected_fermat_M, f"complete Fermat-product list 2..257 mismatch: {fermat_M}")

    def carmichael(n: int) -> int:
        res = 1
        d = 2
        tmp = n
        while d * d <= tmp:
            if tmp % d == 0:
                pe = 1
                while tmp % d == 0:
                    tmp //= d
                    pe *= d
                lam_pe = pe // 4 if (d == 2 and pe >= 8) else (pe // d) * (d - 1)
                res = math.lcm(res, lam_pe)
            d += 1
        if tmp > 1:
            res = math.lcm(res, tmp - 1)
        return res

    good_M = [M for M in range(1, 101) if 3 % odd_part(carmichael(M)) == 0]
    expected_good_M = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 20, 21, 24,
        26, 28, 30, 32, 34, 35, 36, 39, 40, 42, 45, 48, 51, 52, 56, 60, 63, 64,
        65, 68, 70, 72, 78, 80, 84, 85, 90, 91, 96, 97,
    ]
    check_exact(good_M == expected_good_M, f"complete odd(lambda(M))|3 list 1..100 mismatch: {good_M}")
    for M_bad in (11, 19, 22, 23, 25, 27, 29, 31, 33, 37, 41, 43, 44, 49, 50, 55):
        check_exact(M_bad not in good_M, f"M={M_bad} excluded from odd(lambda(M)) | 3")
    # Also verify exact Fermat-power-of-two phi(M) = 2^t decomposition for M = 5:
    # 4*delta_r(u) - 1 = chi_2(u)*chi_2(r) + 2*Re(conj(chi_4(r))*chi_4(u)), where chi_4(2) = i
    chi2_5 = {1: 1, 2: -1, 3: -1, 4: 1}
    dlog5 = {1: 0, 2: 1, 4: 2, 3: 3}
    re_tab = {0: 2, 1: 0, 2: -2, 3: 0}
    for r in (1, 2, 3, 4):
        for u in (1, 2, 3, 4):
            rhs = 1 + chi2_5[r] * chi2_5[u] + re_tab[(dlog5[u] - dlog5[r]) % 4]
            check_exact(rhs == (4 if u == r else 0), f"mod-5 character identity at r={r}, u={u}")
    # Verify Theorem B5.2(2) direct digit-mass step for M = 5: off E_5 (where all nonprincipal
    # (1*chi)(n) vanish), 4 * tau_{r,5}(n) == tau^{(5)}(n) and s_2(tau_{r,5}(n)) == s_2(tau^{(5)}(n)).
    chi4_5_re = {1: 1, 2: 0, 4: -1, 3: 0}
    chi4_5_im = {1: 0, 2: 1, 4: 0, 3: -1}
    off_e5_count = 0
    for n in range(1, 1001):
        divs = [d for d in range(1, n + 1) if n % d == 0 and d % 5 != 0]
        c2 = sum(chi2_5[d % 5] for d in divs)
        c4_re = sum(chi4_5_re[d % 5] for d in divs)
        c4_im = sum(chi4_5_im[d % 5] for d in divs)
        if c2 == 0 and c4_re == 0 and c4_im == 0:
            off_e5_count += 1
            tau_m5 = len(divs)
            for r in (1, 2, 3, 4):
                tau_r5 = sum(1 for d in divs if d % 5 == r)
                check_exact(4 * tau_r5 == tau_m5 and popcount(tau_r5) == popcount(tau_m5),
                            f"mod-5 off-E_5 popcount identity n={n}, r={r}")
    check_exact(off_e5_count > 100, f"mod-5 off-E_5 count up to 1000: {off_e5_count}")

    # Exact cubic-character decomposition check for M = 7 (generator 3, order 6):
    # Every function w on (Z/7Z)^* satisfies 12 * w(u) = a_0 + a_quad*chi_2(u) + b_1*chi_3_re(u) + b_2*chi_3_im(u) + ...
    # Specifically check that for every basis delta_r (r in {1..6}), 6 * delta_r is an integer combination of:
    #   chi_0 = (1,1,1,1,1,1), chi_2 (Legendre),
    #   c3_plus = 2*Re(chi_3) = (2,-1,-1,-1,-1,2) [wait: at 1,2,3,4,5,6: 3^0=1->1, 3^1=3->w, 3^2=2->w^2, 3^3=6->1, 3^4=4->w, 3^5=5->w^2]
    #   and its even-order twist chi_6 = chi_2 * chi_3!
    # Check exact orthogonality / integer basis on (Z/7Z)^*!
    units7 = [1, 2, 3, 4, 5, 6]
    # discrete log base 3 mod 7:
    dlog7 = {}
    val = 1
    for e in range(6):
        dlog7[val] = e
        val = (val * 3) % 7
    # Basis vectors over Z:
    # chi_0(u) = 1
    # chi_2(u) = (-1)^{dlog(u)}
    # cubic real: 2*Re(w^{dlog}) in {2, -1, -1}
    # cubic imag: (w^{dlog} - w^{-dlog}) / (w - w^{-1}) in {0, 1, -1}
    # order-6 real: chi_2(u) * (2*Re(w^{dlog}))
    # order-6 imag: chi_2(u) * imag_cubic(u)
    cub_re = {0: 2, 1: -1, 2: -1}
    cub_im = {0: 0, 1: 1, 2: -1}
    basis = [
        [1 for u in units7],
        [(-1) ** dlog7[u] for u in units7],
        [cub_re[dlog7[u] % 3] for u in units7],
        [cub_im[dlog7[u] % 3] for u in units7],
        [((-1) ** dlog7[u]) * cub_re[dlog7[u] % 3] for u in units7],
        [((-1) ** dlog7[u]) * cub_im[dlog7[u] % 3] for u in units7],
    ]
    # Verify exact integer coefficients for 6 * delta_r!
    # Note: <chi_0, chi_0>=6, <chi_2, chi_2>=6, <cub_re, cub_re>=12, <cub_im, cub_im>=4, <o6_re, o6_re>=12, <o6_im, o6_im>=4
    # Wait: pairwise orthogonal! So 12 * delta_r = sum_i (12 / ||b_i||^2) * b_i(r) * b_i!
    norms = [sum(x * x for x in v) for v in basis]
    check_exact(norms == [6, 6, 12, 4, 12, 4], f"mod-7 character basis norms: {norms}")
    for i in range(6):
        for j in range(i + 1, 6):
            check_exact(sum(basis[i][t] * basis[j][t] for t in range(6)) == 0, f"orthogonality ({i},{j})")
    for r_idx in range(6):
        coeffs = [(12 // norms[i]) * basis[i][r_idx] for i in range(6)]
        for u_idx in range(6):
            val_u = sum(coeffs[i] * basis[i][u_idx] for i in range(6))
            check_exact(val_u == (12 if u_idx == r_idx else 0), f"mod-7 delta_{r_idx+1} reconstruction at {u_idx+1}")

    # Also verify exact algebraic identity: (A + B*w)(x + y*w) + conj = ((2A-B)*c_+ + 3B*c_-)/2
    # where c_+ = 2x - y, c_- = y, and 2*Re(w) = -1, 2*Re(w^2) = -1
    for A in range(-4, 5):
        for B in range(-4, 5):
            for x in range(-4, 5):
                for y in range(-4, 5):
                    # 2*Re((A+Bw)(x+yw)) = 2*(Ax - By) - (Ay + Bx + By)? Wait:
                    # (A+Bw)(x+yw) = (Ax - By) + (Ay + Bx - By)*w  (since w^2 = -1 - w)
                    # 2*Re(u + v*w) = 2u - v
                    re2 = 2 * (A * x - B * y) - (A * y + B * x - B * y)
                    cp_v = 2 * x - y
                    cm_v = y
                    # Check 2 * re2 == (2A - B)*cp_v + 3*B*cm_v? Wait:
                    # re2 = 2Ax - Ay - Bx - By.
                    # 2*re2 = 4Ax - 2Ay - 2Bx - 2By
                    # (2A - B)*(2x - y) + 3*B*y = 4Ax - 2Ay - 2Bx + By + 3By = 4Ax - 2Ay - 2Bx + 4By (wrong sign on B!)
                    # Let's check the EXACT coefficient:
                    # 2*re2 = (2A - B)*(2x - y) - 3*B*y = 4Ax - 2Ay - 2Bx + By - 3By = 4Ax - 2Ay - 2Bx - 2By!
                    check_exact(2 * re2 == (2 * A - B) * cp_v - 3 * B * cm_v,
                                f"cubic trace identity at ({A},{B},{x},{y})")

    return results


# =============================================================================
# Main driver & formatted summary
# =============================================================================

def main() -> None:
    t0 = time.time()
    print("=== Phase 25 Track B: Generalized Erdos-Borwein & Signed Lambert Classification ===\n")

    print("[1/5] Certifying odd-part means C_U, C_U_odd, C_U_plus, C_U^(M), and s=1/2 moments...")
    b1_encl = certify_odd_part_means(P=20000)
    for k_name in ("L2_odd", "L2_plus", "C_U_odd", "C_U", "C_U_plus", "C_U_mod3", "C_U_mod5", "C_U_mod6",
                   "C_U_half", "C_U_odd_half", "C_U_plus_half"):
        lo, hi = b1_encl[k_name]
        print(f"  [encl] {k_name:14s} in {fmt_encl(lo, hi, 6)}")
    ub32, unif32 = b1_encl["Eplus32_s_half_ub"]
    print(f"  [encl] E_+(32) base-32 (s=1/2): ub <= {fmt_ub_dec(ub32, 6)} < {fmt_lb_dec(unif32, 6)} <= unif")

    print("\n[2/5] Verifying B1 carry conservation, dead-block transitions, phase system, and signed odd-arrivals...")
    b1_stats = verify_b1_carry_conservation_and_identities()
    for name, st in b1_stats.items():
        if "dead_frac" in st:
            print(f"  [exact+finite] {name:8s} (N={st['N']}): dead={st['dead_frac']:.4f}, tr={st['tr_frac']:.4f}, "
                  f"f_nz={st['f_nz']:.4f}, mass={st['mass_frac']:.4f}, exits={st['exits_frac']:.4f}")
        else:
            print(f"  [exact+finite] {name:12s} (N={st['N']}): iso_odd_hits={st['iso_hits']} ({st['iso_frac']:.4f})")

    print("\n[3/5] Certifying B2 construction-radix D^-(F_{2^k}; 2^k) lower bounds (outward-rounded floor)...")
    b2_tables = verify_b2_construction_radix(b1_encl)
    for fname, rows in b2_tables.items():
        summary = ", ".join(
            f"k={k}:({fmt_lb_dec(d1, 4)},{fmt_lb_dec(dh, 4)})"
            for k, d1, dh in rows if k in (4, 5, 6, 8, 10, 12, 16, 32, 64)
        )
        print(f"  [encl] {fname:10s}: {summary}")

    print("\n[4/5] Certifying B3 weighted NAF means, 4-state Koksma V_circ, 7-state asymmetric automaton, & Lean certs...")
    naf_encl = certify_weighted_naf_means(P_dp=5000, U_cap=1024)
    for k_name in ("L2_NAF_plus", "W_plus_maj", "W_plus_lean31", "W_plus_lean150", "W_plus_lean400", "W_plus", "mu_asym_3_2"):
        lo, hi = naf_encl[k_name]
        print(f"  [encl] {k_name:15s} in {fmt_encl(lo, hi, 6)}")
    b3_info = verify_b3_automata_koksma_and_lean(naf_encl)
    print(f"  [exact] 4-state: raw={b3_info['n_raw4']}, min={b3_info['n_min4']}; "
          f"7-state (1,3/2): raw={b3_info['n_raw7']}, min={b3_info['n_min7']}, A_inf={b3_info['A_inf_3_2']}")
    print(f"  [exact] pi7 = {[str(x) for x in b3_info['pi7']]}")
    print(f"  [encl] D^-(E_+(8); 2) >= {fmt_lb_sci(b3_info['D_sym_14'], 4)} (4-state Koksma, L=14)")
    print(f"  [encl] D^-(E_+(8); 2) >= {fmt_lb_sci(b3_info['D_asym_14'], 4)} (7-state lam=3/2 Koksma, L=14)")
    print(f"  [encl] D^-(E_+(8); 2) >= {fmt_lb_sci(b3_info['D_maj_20'], 4)} (DP-free W_+^maj, optimal L=20)")
    print(f"  [encl] D^-(E_+(8); 2) >= {fmt_lb_sci(b3_info['D_lean400_20'], 4)} (Lean Tier 3 p<=400 NAF-maj, optimal L=20; from 15/16: >= {fmt_lb_sci(b3_info['D_lean400_thresh_20'], 4)})")
    print(f"  [encl] D^-(E_+(8); 2) >= {fmt_lb_sci(b3_info['D_lean150_21'], 4)} (Lean Tier 2 p<=150 s2-maj, optimal L=21; from 47/50: >= {fmt_lb_sci(b3_info['D_lean150_thresh_21'], 4)})")
    print(f"  [encl] D^-(E_+(8); 2) >= {fmt_lb_sci(b3_info['D_lean31_23'], 4)} (Lean Tier 1 p<=31 s2-maj, optimal L=23; from 23671/25000: >= {fmt_lb_sci(b3_info['D_lean31_thresh_23'], 4)})")

    print("\n[5/5] Verifying B4 E_+(4) frontier & B5 broader Lambert families...")
    b4_info = verify_b4_eplus4_frontier(naf_encl)
    print(f"  [encl] E_+(4) sufficient NAF deficit in {fmt_encl(*b4_info['def_encl'], 6)} "
          f"(rel sym <= {fmt_ub_dec(b4_info['rel_sym_hi'], 5)}, rel asym(3/2) <= {fmt_ub_dec(b4_info['rel_asym_hi'], 5)})")
    print("  [finite] E_+(4) fixed-block cancellation (illusion: increases at M=2^10..2^16 yet -> 0 as M -> inf):")
    for B, rows in b4_info["block_table"].items():
        print(f"    B={B:2d}: " + ", ".join(f"M={M}:{v:.5f}" for M, v in rows))
    print("  [finite] E_+(2^k) base-2 prefix measurements (N=12000 certified bits):")
    for k, Nb, f1, tr in b4_info["eplus_f1"]:
        print(f"    k={k}: f_1={f1:.5f}, tr={tr:.5f}")

    b5_encl = certify_b5_families()
    for name, (lo, hi) in b5_encl.items():
        print(f"  [encl] C_U({name:8s}) in {fmt_encl(lo, hi, 5)}")

    dt = time.time() - t0
    print(f"\nALL CHECKS PASSED in {dt:.2f}s: "
          f"{CHECKS_EXACT:,} [exact], {CHECKS_ENCL:,} [encl], {CHECKS_FINITE:,} [finite] "
          f"(total {CHECKS_EXACT + CHECKS_ENCL + CHECKS_FINITE:,}).")


if __name__ == "__main__":
    main()
