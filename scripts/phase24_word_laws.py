#!/usr/bin/env python3
"""Exact-arithmetic verifier for Phase 24 Track B:
  - Sub-track B2: Higher-m partition reciprocals Y_{b,m} (exact digits, gap law,
    exact C_1(m^k), self-similar limit set [1 - 1/m, 1 - 1/(m(m-1))], words,
    non-disjunctivity).
  - Sub-track B1: Euler's square E_2^2 (exact theta-difference identity,
    prime-by-prime Selberg inequality, local factor algebraic identity,
    zero-float rational certificates for pi, Gamma(1/4), E_0 -> K_* < 3.178808
    -> 8*K_* < 25.431 < 26 -> liminf f_d >= 1/26).
  - Sub-track B3: Rational-scaling Conjecture 5.5, base-2 complement symmetry
    vs base-b >= 3 interior obstructions, universal family (1/(b^2+b+1)) E_b,
    primitive-root impossibility edge cases p in {3, 5, 11}, new balanced
    b-exceptional primes (b=4 p=29; b=6 p=59, 1613; b=10 p=113), and exact
    base-2 search through p <= 40,000.
  - Sub-track B4: Multi-radix finite-order normality (cross-radix order
    implication & sharpness, phase-stratified & coupling discrepancy ceilings,
    explicit witnesses with D_infty(x; b) > 2/b^(k*L2), phased de Bruijn Euler
    circuits, parity obstruction at (b,k,L1,L2)=(2,2,3,1) in K_{2^8},
    kernel intersection gcd law, and disjunctive/non-disjunctive tower checks).

Uses Python standard library only. Every algebraic identity, digit prefix,
order test, and rational inequality is checked with exact int/Fraction
arithmetic. Runs in a few seconds and exits 0 iff all checks pass.
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction


CHECKS = 0


def check(cond: bool, msg: str = "") -> None:
    global CHECKS
    if not cond:
        raise AssertionError(f"Check failed: {msg}")
    CHECKS += 1


# ============================================================================
# Shared number-theory helpers
# ============================================================================

def primes_up_to(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, math.isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i, v in enumerate(sieve) if v]


def mult_order(b: int, p: int) -> int:
    """Exact multiplicative order of b mod prime p (p nmid b)."""
    t = p - 1
    n = t
    d = 2
    while d * d <= n:
        if n % d == 0:
            while t % d == 0 and pow(b, t // d, p) == 1:
                t //= d
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        while t % n == 0 and pow(b, t // n, p) == 1:
            t //= n
    return t


def v2(n: int) -> int:
    """2-adic valuation of positive integer n."""
    return (n & -n).bit_length() - 1


def s2(n: int) -> int:
    """Binary digit sum of nonnegative integer n."""
    return n.bit_count()


def u_m(i: int, m: int) -> int:
    """Map binary digits of i >= 0 into base m."""
    res = 0
    p = 1
    while i > 0:
        if i & 1:
            res += p
        p *= m
        i >>= 1
    return res


def disc_multiset(vals: list[Fraction]) -> Fraction:
    """Exact extreme discrepancy of an equal-weight multiset in [0, 1)."""
    n = len(vals)
    s = sorted(vals)
    mx = max(s[i] - Fraction(i, n) for i in range(n))
    mn = min(s[i] - Fraction(i, n) for i in range(n))
    return Fraction(1, n) + mx - mn


def ceil_decimal_str(q: Fraction, digits: int) -> str:
    """Return an exact outward-rounded (ceiling) decimal string for q >= 0."""
    scale = 10 ** digits
    scaled = q * scale
    c = (scaled.numerator + scaled.denominator - 1) // scaled.denominator
    whole, frac = divmod(c, scale)
    return f"{whole}.{frac:0{digits}d}"


# ============================================================================
# Sub-track B2: Higher-m Partition Reciprocals Y_{b,m}
# ============================================================================

def exact_digits_Ybm(b: int, m: int, N: int) -> list[int]:
    """Certify the exact first N fractional base-b digits of Y_{b,m} using
    exact integer arithmetic and the proved tail bound |R_i| < 1."""
    pad = N + 25
    num = 0
    i = 0
    while True:
        u = u_m(i, m)
        if u > pad:
            tail_sgn = -1 if (s2(i) & 1) else 1
            break
        sgn = -1 if (s2(i) & 1) else 1
        num += sgn * (b ** (pad - u))
        i += 1
    # Since 0 < |tail| < 1 at scale b^pad with sign tail_sgn:
    fl = num if tail_sgn > 0 else num - 1
    check(0 < fl < b ** pad, f"Y_{{{b},{m}}} integer part check")
    top = fl // (b ** (pad - N))
    digs = []
    for _ in range(N):
        digs.append(top % b)
        top //= b
    digs.reverse()
    return digs


def F_m_exact_rational(m: int, x: Fraction) -> Fraction:
    """Evaluate the exact self-similar cumulative function F_m(x) at any
    rational x in [0, 1] using the functional equation, solving the exact
    affine equation on any detected cycle."""
    if not (0 <= x <= 1):
        raise ValueError(f"x must lie in [0, 1], got {x}")
    inv_m = Fraction(1, m)
    inv_m1 = Fraction(1, m - 1)
    c_top = Fraction(1, m * (m - 1))
    fm_1m = Fraction(m * m - m - 1, m * m * (m - 1))
    # Maintain F_m(x) = A * F_m(cur) + B
    A = Fraction(1)
    B = Fraction(0)
    cur = x
    seen: dict[Fraction, tuple[Fraction, Fraction]] = {}
    while True:
        if cur == 0:
            return B
        if cur >= inv_m1:
            return A * (cur - c_top) + B
        if cur in seen:
            Aj, Bj = seen[cur]
            # Every cycle visits branch (1) (multiplying A by 1/m), so |A| <= |Aj|/m < |Aj|.
            f_cur = (B - Bj) / (Aj - A)
            return Aj * f_cur + Bj
        seen[cur] = (A, B)
        if cur <= inv_m:
            A = A * inv_m
            cur = m * cur
        else:
            s = cur - inv_m
            B = B + A * (fm_1m + s)
            A = -A
            cur = s


def verify_B2() -> None:
    print("=== Sub-track B2: Higher-m partition reciprocals Y_{b,m} ===")

    # 1. Support-gap formula u_i - u_{i-1} = ((m-2)*m^{v_2(i)} + 1)/(m-1)
    #    and exact Thue-Morse signed even-gap sum Delta(k) = g_{2^k} + g_{2^{k-1}}.
    for m in [3, 4, 5, 6, 10]:
        prev = u_m(0, m)
        check(prev == 0, "u_0 = 0")
        for i in range(1, 513):
            cur = u_m(i, m)
            r = v2(i)
            gap = ((m - 2) * (m ** r) + 1) // (m - 1)
            check((m - 2) * (m ** r) + 1 == (m - 1) * (cur - prev),
                  f"gap formula m={m}, i={i}")
            check(cur - prev == gap, f"gap integer m={m}, i={i}")
            prev = cur

        # Exact signed even-gap sum Delta(k) for k = 2..8
        for k in range(2, 9):
            w1 = 0
            w0 = 0
            for j in range(1, 2 ** (k - 1) + 1):
                i = 2 * j
                g = u_m(i, m) - u_m(i - 1, m)
                if s2(i) & 1:
                    w1 += g
                else:
                    w0 += g
            delta = w1 - w0
            expected_delta = ((m - 2) * (m ** k + m ** (k - 1)) + 2) // (m - 1)
            check(delta == expected_delta, f"Delta(k) m={m}, k={k}")
            check(w1 + w0 == m ** k - 2 ** (k - 1), f"W1+W0 m={m}, k={k}")
            w0_exact = (m ** (k - 1) - 1) // (m - 1) - 2 ** (k - 2)
            w1_exact = (m ** (k - 1) * (m * m - m - 1) + 1) // (m - 1) - 2 ** (k - 2)
            check(w0 == w0_exact and w1 == w1_exact, f"W0/W1 exact m={m}, k={k}")

    # 2. Exact tail-bound rational check: (b^{-1} + b^{-m})/(1 - b^{-m}) <= 5/7 < 1
    for b in [2, 3, 4, 5, 10]:
        for m in [3, 4, 5, 6, 10]:
            even_bd = Fraction(b ** (m - 1) + 1, b ** m - 1)
            odd_bd = Fraction(b + 1, b ** m - 1)
            check(even_bd <= Fraction(5, 7) < 1, f"even tail bound b={b}, m={m}")
            check(odd_bd <= Fraction(3, 7) < Fraction(1, 2), f"odd tail bound b={b}, m={m}")
            # Verify equality between majorants: b^{-1}(1 + odd_bd) == even_bd when i is even
            check(Fraction(1, b) * (1 + odd_bd) == even_bd, "tail majorant identity")

    # 3. Exact digit law, exact C_1(m^k) for b=2, forbidden words, and exact
    #    nonconstant word counts for (b, m) in {2,3,4} x {3,4,5,6,10}
    cases = [
        (2, 3, 5), (2, 4, 4), (2, 5, 4), (2, 6, 3), (2, 10, 3),
        (3, 3, 5), (3, 4, 4), (3, 5, 3), (3, 6, 3), (3, 10, 2),
        (4, 3, 4), (4, 4, 4), (4, 5, 3), (4, 6, 3), (4, 10, 2),
    ]
    for b, m, k in cases:
        N = m ** k
        digs = exact_digits_Ybm(b, m, N)
        pred = [None] * N
        for i in range(1, 2 ** k + 1):
            ui_prev = u_m(i - 1, m)
            ui = u_m(i, m)
            ti = s2(i) & 1
            ti1 = s2(i + 1) & 1
            if i % 2 == 0:
                d = (b - 1) if ti == 1 else 0
                for n in range(ui_prev + 1, ui + 1):
                    pred[n - 1] = d
            else:
                check(ui == ui_prev + 1, "odd gap is 1")
                if (ti, ti1) == (0, 0):
                    d = 1
                elif (ti, ti1) == (0, 1):
                    d = 0
                elif (ti, ti1) == (1, 0):
                    d = b - 1
                else:
                    d = b - 2
                pred[ui - 1] = d
        check(digs == pred, f"exact digit law b={b}, m={m}, N={N}")

        # Finite-prefix upper bound C_{b-1}(N) <= (1 - 1/(m*(m-1))) * N for every 1 <= N <= m^k
        top_cnt = 0
        for n in range(1, N + 1):
            if digs[n - 1] == b - 1:
                top_cnt += 1
            check(top_cnt * m * (m - 1) <= (m * m - m - 1) * n,
                  f"finite upper bound b={b}, m={m}, n={n}")

        # Exact binary count C_1(m^k) with ZERO 2^k error term, plus exact finite-prefix
        # crossing C_1(u_{2^k - 1}) = m^{k-1} - 1 < (1 - 1/m) * u_{2^k - 1}!
        if b == 2:
            c1 = sum(1 for d in digs if d == 1)
            c0 = N - c1
            c1_exact = (m ** (k - 1) * (m * m - m - 1) - (m - 2)) // (m - 1)
            c0_exact = (m ** (k - 1) + m - 2) // (m - 1)
            check(c1 == c1_exact and c0 == c0_exact,
                  f"exact C_1(m^k) m={m}, k={k}: {c1} vs {c1_exact}")
            u_last = (m ** k - 1) // (m - 1)
            c1_ulast = sum(1 for d in digs[:u_last] if d == 1)
            check(c1_ulast == m ** (k - 1) - 1,
                  f"exact C_1(u_{{2^k-1}}) m={m}, k={k}: {c1_ulast}")
            check(Fraction(c1_ulast, u_last) == Fraction(m - 1, m) - Fraction(m - 1, m * u_last) < Fraction(m - 1, m),
                  f"finite lower crossing m={m}, k={k}")
            # Non-disjunctivity: neither 0101 nor 1010 occurs
            for pos in range(N - 3):
                w4 = tuple(digs[pos : pos + 4])
                check(w4 != (0, 1, 0, 1) and w4 != (1, 0, 1, 0),
                      f"forbidden 4-word at pos={pos}, m={m}")
        else:
            # For b >= 3, no two consecutive interior digits in {1..b-2} occur
            for pos in range(N - 1):
                d1, d2 = digs[pos], digs[pos + 1]
                check(not (1 <= d1 <= b - 2 and 1 <= d2 <= b - 2),
                      f"forbidden interior 2-word b={b}, m={m}, pos={pos}")

        # Word length L=2,3: check nonconstant word count <= L * 2^k
        for L in [2, 3]:
            nonconst = 0
            for pos in range(N - L + 1):
                w = digs[pos : pos + L]
                if not (all(x == 0 for x in w) or all(x == b - 1 for x in w)):
                    nonconst += 1
            check(nonconst <= L * (2 ** k), f"nonconst bound b={b}, m={m}, L={L}")

    # 4. Exact self-similar function F_m(t)/t check at key rational points
    for m in [3, 4, 5, 6, 10]:
        f_max = Fraction(m * m - m - 1, m * (m - 1))  # 1 - 1/(m(m-1))
        f_min = Fraction(m - 1, m)                    # 1 - 1/m
        # At t = 1 and t = 1/m: exact limsup
        check(F_m_exact_rational(m, Fraction(1)) == f_max, f"F_m(1) m={m}")
        check(F_m_exact_rational(m, Fraction(1, m)) / Fraction(1, m) == f_max, f"F_m(1/m)/(1/m)")
        # At t = 1/(m-1) and t = 1/m + 1/m^2: exact liminf!
        t_u = Fraction(1, m - 1)
        t_2 = Fraction(1, m) + Fraction(1, m * m)
        check(F_m_exact_rational(m, t_u) / t_u == f_min, f"F_m(1/(m-1)) m={m}")
        check(F_m_exact_rational(m, t_2) / t_2 == f_min, f"F_m(1/m+1/m^2) m={m}")
        # Also at Cantor minimizers t_r = 1/m + 1/m^2 + 1/(m^{r+1}(m-1))!
        for r in range(1, 5):
            t_r = Fraction(1, m) + Fraction(1, m * m) + Fraction(1, (m ** (r + 1)) * (m - 1))
            check(F_m_exact_rational(m, t_r) / t_r == f_min, f"Cantor minimizer m={m}, r={r}")
        # Check dense grid of depth-4 m-adic points in [1/m, 1] all lie in [f_min, f_max]
        denom = m ** 4
        for num in range(m ** 3, denom + 1):
            t = Fraction(num, denom)
            val = F_m_exact_rational(m, t) / t
            check(f_min <= val <= f_max, f"envelope bound m={m}, t={t}")

    # Verify cycle-solving branch of F_m_exact_rational on periodic orbits (e.g. m=3, x=1/8: 1/8->3/8->1/24->1/8)
    f3_1_8 = F_m_exact_rational(3, Fraction(1, 8))
    check(f3_1_8 == Fraction(23, 240), f"F_3(1/8) cycle exact: {f3_1_8}")
    check(Fraction(2, 3) <= f3_1_8 / Fraction(1, 8) <= Fraction(5, 6), "F_3(1/8)/(1/8) in envelope")
    check(f3_1_8 == F_m_exact_rational(3, Fraction(3, 8)) / 3, "F_3(1/8) functional eq check")
    check(
        F_m_exact_rational(3, Fraction(3, 8))
        == Fraction(5, 18) + Fraction(1, 24) - F_m_exact_rational(3, Fraction(1, 24)),
        "F_3(3/8) functional eq check",
    )

    # Finite measurement printout for table (b=2, m=3,4,5 at k=6,5,4)
    print("  [Finite measurements] Y_{2,m} prefix extrema on [m^{k-1}, m^k]:")
    for m, k in [(3, 6), (4, 5), (5, 4)]:
        N = m ** k
        digs = exact_digits_Ybm(2, m, N)
        cnt = 0
        mn_f, mx_f = Fraction(1), Fraction(0)
        for n in range(1, N + 1):
            if digs[n - 1] == 1:
                cnt += 1
            if n >= m ** (k - 1):
                fr = Fraction(cnt, n)
                if fr < mn_f:
                    mn_f = fr
                if fr > mx_f:
                    mx_f = fr
        print(
            f"    m={m}, k={k} (N={N}): min f_1={float(mn_f):.6f} (liminf={1-1/m:.6f}), "
            f"max f_1={float(mx_f):.6f} (limsup={1-1/(m*(m-1)):.6f})"
        )
    print("  Sub-track B2: ALL checks passed.")


# ============================================================================
# Sub-track B1: Euler's Square E_2^2
# ============================================================================

def verify_B1() -> None:
    print("=== Sub-track B1: Euler's square E_2^2 ===")

    # 1. Exact theta-difference identity:
    #    a_2(n) = (1/2) * (r_{x^2+36y^2}(12n+1) - r_{4x^2+9y^2}(12n+1))
    #    r_2(24n+2)/4 = r_2(12n+1)/4 = R_+(12n+1) + R_-(12n+1)
    #    For n in U (a_2(n) != 0): |a_2(n)| == r_2(12n+1)/4 iff 12n+1 has no prime factor == 5 mod 12
    #    a_2(n) == r_2(12n+1)/4 (mod 2)
    Nmax = 3000
    pent: dict[int, int] = {}
    j = 0
    while True:
        p1 = j * (3 * j - 1) // 2
        p2 = j * (3 * j + 1) // 2
        if p1 > Nmax and p2 > Nmax:
            break
        sgn = 1 if j % 2 == 0 else -1
        if p1 <= Nmax:
            pent[p1] = pent.get(p1, 0) + sgn
        if j > 0 and p2 <= Nmax:
            pent[p2] = pent.get(p2, 0) + sgn
        j += 1

    a2 = [0] * (Nmax + 1)
    for p1, c1 in pent.items():
        for p2, c2 in pent.items():
            if p1 + p2 <= Nmax:
                a2[p1 + p2] += c1 * c2

    Mmax = 12 * Nmax + 1
    rA = [0] * (Mmax + 1)  # r_{x^2 + 36 y^2}
    rB = [0] * (Mmax + 1)  # r_{4 x^2 + 9 y^2}
    r2_arr = [0] * (Mmax + 1)  # r_2(m)
    lim = math.isqrt(Mmax)
    for x in range(-lim, lim + 1):
        x2 = x * x
        ylim = math.isqrt(Mmax - x2)
        for y in range(-ylim, ylim + 1):
            v = x2 + y * y
            r2_arr[v] += 1
        ylim6 = math.isqrt((Mmax - x2) // 36)
        for y in range(-ylim6, ylim6 + 1):
            rA[x2 + 36 * y * y] += 1
    lim2 = math.isqrt(Mmax // 4)
    for x in range(-lim2, lim2 + 1):
        x2 = 4 * x * x
        ylim3 = math.isqrt((Mmax - x2) // 9)
        for y in range(-ylim3, ylim3 + 1):
            rB[x2 + 9 * y * y] += 1

    def has_prime_5mod12(m: int) -> bool:
        d = 5
        tmp = m
        while d * d <= tmp:
            if tmp % d == 0:
                if d % 12 == 5:
                    return True
                while tmp % d == 0:
                    tmp //= d
            d += 2
        return tmp > 1 and tmp % 12 == 5

    for n in range(Nmax + 1):
        m = 12 * n + 1
        check(rA[m] % 2 == 0 and rB[m] % 2 == 0, f"even counts at n={n}")
        check(r2_arr[m] % 4 == 0, f"r2 div 4 at n={n}")
        rp = rA[m] // 2
        rm = rB[m] // 2
        check(a2[n] == rp - rm, f"theta diff at n={n}")
        check(r2_arr[m] // 4 == rp + rm, f"r2 sum at n={n}")
        check((a2[n] - r2_arr[m] // 4) % 2 == 0, f"mod 2 congruence at n={n}")
        check(abs(a2[n]) <= r2_arr[m] // 4, f"|a2| <= r2/4 at n={n}")
        if a2[n] != 0:
            eq_holds = (abs(a2[n]) == r2_arr[m] // 4)
            check(eq_holds == (not has_prime_5mod12(m)), f"equality criterion n={n}")

    # 2. Exact algebraic local-factor identity for E_0:
    #    (1 - 1/(p-1)^2) * (1 - 1/p^2)^2 * (p^4/(p^4-1)) * (1 + 1/(p(p-2)) + 2(p-1)/((p^2-1)(p-2)))
    #    == 1 + 2/((p-1)(p^2+1))
    ps_P0 = [p for p in primes_up_to(500) if p >= 5 and p % 12 != 1]
    for p in ps_P0:
        lhs = (
            (1 - Fraction(1, (p - 1) ** 2))
            * ((1 - Fraction(1, p * p)) ** 2)
            * Fraction(p ** 4, p ** 4 - 1)
            * (1 + Fraction(1, p * (p - 2)) + Fraction(2 * (p - 1), (p * p - 1) * (p - 2)))
        )
        rhs = 1 + Fraction(2, (p - 1) * (p * p + 1))
        check(lhs == rhs, f"local factor identity at p={p}")

    # 3. Exact prime-by-prime Selberg sieve lower bound Lemma 2.2 on full G_0(xi):
    #    G(xi) >= G_0(xi) * prod_{p in S} (p - 2)/(p - 1)
    #    using ALL primes p in P_0 with p < xi for each tested cutoff xi.
    for xi in [40, 100, 250]:
        primes_P0_xi = [p for p in primes_up_to(xi - 1) if p >= 5 and p % 12 != 1]
        # Generate all squarefree d < xi composed of all primes in P_0 below xi
        sqfree = [1]
        for p in primes_P0_xi:
            sqfree += [d * p for d in sqfree if d * p < xi]

        def eval_G(switched: set[int]) -> Fraction:
            tot = Fraction(0)
            for d in sqfree:
                term = Fraction(1)
                tmp = d
                for p in primes_P0_xi:
                    if p > tmp:
                        break
                    if tmp % p == 0:
                        term *= Fraction(1, p - 1) if p in switched else Fraction(2, p - 2)
                        tmp //= p
                tot += term
            return tot

        G0 = eval_G(set())
        for switched in [{5}, {7}, {5, 7}, {5, 11}, {5, 7, 11}, {7, 17, 19}]:
            Gs = eval_G(switched)
            fac = Fraction(1)
            for p in switched:
                fac *= Fraction(p - 2, p - 1)
            check(Gs >= G0 * fac, f"Selberg prime-switch xi={xi}, S={switched}")

    # 4. Exact weighted-sum inequality sum_{1 <= m < M} (H - D*m) <= H^2 / (2D)
    for H in range(1, 40):
        for D in range(1, 25):
            s = sum(H - D * m for m in range(1, H) if D * m < H)
            check(2 * D * s <= H * H, f"weighted sum H={H}, D={D}")

    # 5. Zero-float exact rational certificates proving E_0 < 1.028980,
    #    K_* < 3.178808, and 8 * K_* < 25.431 < 26 -> kappa > 1/26!
    #    (a) Exact Euler product head through p <= 100 + odd-prime tail bound:
    #        For odd p = 2j + 1 >= 101 (j >= 50), 2/((p-1)(p^2+1)) < 1/(4 j^3),
    #        so tail < sum_{j >= 50} 1/(4 j^3) < int_{49}^infty dt/(4 t^3) = 1/(8*49^2) = 1/19208.
    #        Using exp(u) < 1/(1 - u): E_0 < E0_head * (19208 / 19207).
    P0_100 = [p for p in primes_up_to(100) if p >= 5 and p % 12 != 1]
    E0_head = Fraction(1)
    for p in P0_100:
        E0_head *= 1 + Fraction(2, (p - 1) * (p * p + 1))
    E0_upper = E0_head * Fraction(19208, 19207)
    check(E0_upper < Fraction(1028980, 1000000), f"E_0 < 1.028980: {ceil_decimal_str(E0_upper, 6)}")

    #    (b) Exact Machin rational certificate for pi and sqrt(2*pi):
    #        pi = 16 arctan(1/5) - 4 arctan(1/239)
    #           < 16 * sum_{j=0}^4 (-1)^j / ((2j+1) * 5^(2j+1)) - 4 * (1/239 - 1/(3 * 239^3))
    pi_cert = (
        16 * sum(Fraction((-1) ** j, (2 * j + 1) * (5 ** (2 * j + 1))) for j in range(5))
        - 4 * (Fraction(1, 239) - Fraction(1, 3 * (239 ** 3)))
    )
    check(pi_cert < Fraction(31416, 10000), f"pi < 3.1416: {ceil_decimal_str(pi_cert, 6)}")
    sqrt2pi_upper = Fraction(25067, 10000)
    check(2 * pi_cert < sqrt2pi_upper ** 2, "2*pi < (25067/10000)^2")

    #    (c) Exact Taylor-integral rational certificate for Gamma(1/4):
    #        On [0, 16], e^{-x} <= sum_{j=0}^{80} (-x)^j / j! (even degree 80),
    #        and int_0^{16} x^{j - 3/4} dx = 8 * 16^j / (4j + 1);
    #        on [16, infty), x^{-3/4} < 1 so tail < e^{-16} < 2^{-16}.
    gamma14_cert = (
        8 * sum(Fraction((-16) ** j, math.factorial(j) * (4 * j + 1)) for j in range(81))
        + Fraction(1, 1 << 16)
    )
    check(gamma14_cert < Fraction(3625626, 1000000),
          f"Gamma(1/4) < 3.625626: {ceil_decimal_str(gamma14_cert, 6)}")
    gamma14_upper = Fraction(36257, 10000)
    check(gamma14_cert < gamma14_upper, "Gamma(1/4) < 3.6257")

    #    (d) Exact rational bound on K_* = (3 sqrt(2*pi) / 32) * Gamma(1/4)^2 * E_0
    K_star_upper = Fraction(3, 32) * sqrt2pi_upper * (gamma14_upper ** 2) * E0_upper
    check(K_star_upper < Fraction(3178808, 1000000),
          f"K_* < 3.178808: {ceil_decimal_str(K_star_upper, 6)}")
    check(8 * K_star_upper < Fraction(25431, 1000),
          f"8*K_* < 25.431: {ceil_decimal_str(8 * K_star_upper, 4)}")
    check(8 * K_star_upper < Fraction(254305, 10000),
          f"8*K_* < 25.4305: {ceil_decimal_str(8 * K_star_upper, 4)}")
    check(8 * K_star_upper < 26, f"8*K_* < 26: {ceil_decimal_str(8 * K_star_upper, 4)}")
    check(Fraction(1, 8) / K_star_upper > Fraction(1, 26), "kappa > 1/26")
    print(
        f"  Certified outward-rounded rational upper bounds: "
        f"pi < {ceil_decimal_str(pi_cert, 6)}, Gamma(1/4) < {ceil_decimal_str(gamma14_cert, 6)}, "
        f"E_0 < {ceil_decimal_str(E0_upper, 6)}, K_* < {ceil_decimal_str(K_star_upper, 6)}, "
        f"8*K_* < {ceil_decimal_str(8 * K_star_upper, 4)} < 26 -> kappa > 1/26"
    )
    print("  Sub-track B1: ALL checks passed.")


# ============================================================================
# Sub-track B3: Rational-Scaling Conjecture 5.5 & Exceptional Primes
# ============================================================================

def euler_digit_law(b: int, d: int, a: int = 1) -> tuple[int, Fraction, Fraction, list[Fraction]]:
    """Exact limit digit frequencies of (a/d) E_b in base b.
    Requires b >= 2, odd d >= 1 with gcd(d, b) = 1, and nonzero a with gcd(a, d) = 1.
    At d = 1 uses the trivial-modulus convention ord_1(b) = 1."""
    if b < 2 or d < 1 or d % 2 == 0 or math.gcd(d, b) != 1 or a == 0 or math.gcd(abs(a), d) != 1:
        raise ValueError(f"Invalid parameters: b={b}, d={d}, a={a}")
    if d == 1:
        f = [Fraction(0)] * b
        f[0] = Fraction(1, 2)
        f[b - 1] = Fraction(1, 2)
        return 1, Fraction(1, 2), Fraction(1, 2), f
    t = 1
    cur = b % d
    while cur != 1:
        cur = (cur * b) % d
        t += 1
    q = pow(b, t - 1, d)

    def tm(i: int) -> int:
        p = i * (3 * i - 1) // 2
        val = pow(q, p % t, d)
        return val if i % 2 == 0 else (-val) % d

    P = 2 * t
    atom_mass = [Fraction(0)] * d
    w0_plus = Fraction(0)
    w0_minus = Fraction(0)

    def add_orbit(start: int, weight: Fraction, sgn: int) -> None:
        nonlocal w0_plus, w0_minus
        c = (a * start) % d
        if c == 0:
            if sgn * (1 if a > 0 else -1) > 0:
                w0_plus += weight
            else:
                w0_minus += weight
        else:
            orb = []
            x = c
            while x not in orb:
                orb.append(x)
                x = (x * b) % d
            share = weight / len(orb)
            for x in orb:
                atom_mass[x] += share

    for k in range(P):
        Ak_minus = sum(tm(i) for i in range(1 - k, k + 1)) % d
        uk_minus = (pow(b, (k * (3 * k - 1) // 2) % t, d) * Ak_minus) % d
        add_orbit(uk_minus, Fraction(1, 3 * P), 1 if k % 2 == 0 else -1)
        Ak_plus = sum(tm(i) for i in range(-k, k + 1)) % d
        uk_plus = (pow(b, (k * (3 * k + 1) // 2) % t, d) * Ak_plus) % d
        add_orbit(uk_plus, Fraction(2, 3 * P), 1 if (k + 1) % 2 == 0 else -1)

    f = [Fraction(0)] * b
    f[0] += w0_plus
    f[b - 1] += w0_minus
    for c in range(1, d):
        if atom_mass[c]:
            f[(b * c) // d] += atom_mass[c]
    return t, w0_plus, w0_minus, f


def check_b_exceptional_prime(b: int, p: int) -> tuple[int, int, list[int], int] | None:
    """Return (t, h, zeros_in_1..h, Xi) if prime p (p nmid 2b) is b-exceptional, else None."""
    b_mod = b % p
    if b_mod == 0:
        return None
    t = mult_order(b_mod, p)
    if t & 1:
        return None
    h = t >> 1
    q = pow(b_mod, p - 2, p)
    q3 = (q * q % p) * q % p
    cur = (1 - q) % p
    zeros = [1] if cur == 0 else []
    q_pos = q
    step_pos = q * q3 % p
    q_neg = 1
    step_neg = q * q % p
    sgn_neg = p - 1
    sgn_pos = 1
    for k in range(1, h):
        q_neg = q_neg * step_neg % p
        step_neg = step_neg * q3 % p
        q_pos = q_pos * step_pos % p
        step_pos = step_pos * q3 % p
        cur = (cur + sgn_neg * q_neg + sgn_pos * q_pos) % p
        if cur == 0:
            zeros.append(k + 1)
        sgn_neg = p - sgn_neg
        sgn_pos = p - sgn_pos
    if not zeros or zeros[-1] != h:
        return None
    xi = 1 + (1 if h % 2 == 0 else -1) + 2 * sum((1 if k % 2 == 0 else -1) for k in zeros if k < h)
    return t, h, zeros, xi


def verify_B3() -> None:
    print("=== Sub-track B3: Rational-scaling Conjecture 5.5 & exceptional primes ===")

    # 1. Base-2 complement sum f_0(a/d; 2) + f_0((d-a)/d; 2) == 1 identically,
    #    vs failure of f_e + f_{b-1-e} == 2/b in bases b >= 3.
    for d in range(3, 50, 2):
        for a in range(1, d):
            if math.gcd(a, d) != 1:
                continue
            # Purely periodic orbit of a/d in base 2
            orb = []
            x = a
            while x not in orb:
                orb.append(x)
                x = (2 * x) % d
            f0_a = Fraction(sum(1 for c in orb if 2 * c < d), len(orb))
            f0_comp = Fraction(sum(1 for c in orb if 2 * (d - c) < d), len(orb))
            check(f0_a + f0_comp == 1, f"base-2 complement identity a={a}, d={d}")

    # 2. Universal infinite family (1/(b^2+b+1)) E_b across b = 2..12
    for b in range(2, 13):
        d = b * b + b + 1
        check(d % 2 == 1 and math.gcd(d, b) == 1, f"d=b^2+b+1 coprime b={b}")
        t, wp, wm, f = euler_digit_law(b, d, 1)
        check(t == 3, f"ord_{d}({b}) == 3")
        check(wp == Fraction(1, 18) and wm == Fraction(1, 18), f"balanced zero split b={b}")
        if b == 2:
            check(f == [Fraction(1, 2), Fraction(1, 2)], "b=2 simply normal")
        elif b == 3:
            check(f == [Fraction(19, 54), Fraction(8, 27), Fraction(19, 54)], "b=3 exact")
        else:
            expected = [Fraction(19, 54), Fraction(4, 27)] + [Fraction(0)] * (b - 4) + [Fraction(4, 27), Fraction(19, 54)]
            check(f == expected, f"universal formula b={b}")

    # 3. Primitive-root impossibility finite edge cases: p in {3, 5, 11}, plus d = 1 trivial modulus check
    #    (Only primitive-root pairs with p == -1 mod b and b >= 3 are (b=3, p=5) and (b=6, p=11))
    check(euler_digit_law(2, 1, 1) == (1, Fraction(1, 2), Fraction(1, 2), [Fraction(1, 2), Fraction(1, 2)]),
          "d=1 trivial modulus E_2")
    t35, wp35, wm35, f35 = euler_digit_law(3, 5, 1)
    check(t35 == 4 and wp35 == Fraction(1, 4) and wm35 == Fraction(1, 6) and wp35 != wm35, "E_3/5 unbalanced (a>0)")
    t35n, wp35n, wm35n, _ = euler_digit_law(3, 5, -1)
    check(t35n == 4 and wp35n == wm35 and wm35n == wp35, "E_3/5 negative numerator swaps boundary")
    t611, wp611, wm611, f611 = euler_digit_law(6, 11, 1)
    check(t611 == 10 and wp611 == Fraction(1, 10) and wm611 == Fraction(1, 15), "E_6/11 exact (a>0)")
    check(wp611 + wm611 == Fraction(1, 6), "E_6/11 total zero mass equals 2/(p+1)")
    check(f611 == [Fraction(11, 60), Fraction(1, 6), Fraction(1, 6), Fraction(1, 6), Fraction(1, 6), Fraction(3, 20)],
          "E_6/11 interior digits equal 1/6, boundary unbalanced (a>0)")
    _, wp611n, wm611n, f611n = euler_digit_law(6, 11, -1)
    check(wp611n == wm611 and wm611n == wp611 and f611n == list(reversed(f611)),
          "E_6/11 negative numerator reverses digits")

    # 4. Balanced b-exceptional primes (refuting radix-free converse in both t == 2 mod 4 and t == 0 mod 4):
    #    (b=4, p=29), (b=6, p=59), (b=6, p=1613), (b=10, p=113)
    res_4_29 = check_b_exceptional_prime(4, 29)
    check(res_4_29 == (14, 7, [7], 0), f"b=4, p=29: {res_4_29}")
    t, wp, wm, f = euler_digit_law(4, 29, 1)
    check(t == 14 and wp == wm == Fraction(1, 14), "E_4/29 balanced (a=1)")
    check(f == [Fraction(29, 98), Fraction(10, 49), Fraction(10, 49), Fraction(29, 98)], "E_4/29 exact digits (a=1)")
    t2, wp2, wm2, f2 = euler_digit_law(4, 29, 2)
    check(t2 == 14 and wp2 == wm2 == Fraction(1, 14), "2*E_4/29 balanced (other coset a=2)")
    check(f2 == [Fraction(27, 98), Fraction(11, 49), Fraction(11, 49), Fraction(27, 98)], "2*E_4/29 exact digits (a=2)")

    res_6_59 = check_b_exceptional_prime(6, 59)
    check(res_6_59 == (58, 29, [29], 0), f"b=6, p=59: {res_6_59}")
    t, wp, wm, f = euler_digit_law(6, 59, 1)
    check(t == 58 and wp == wm == Fraction(5, 174), "E_6/59 balanced")
    check(f == [Fraction(883, 5046)] + [Fraction(410, 2523)] * 4 + [Fraction(883, 5046)], "E_6/59 exact digits")

    res_6_1613 = check_b_exceptional_prime(6, 1613)
    check(res_6_1613 == (806, 403, [403], 0), f"b=6, p=1613: {res_6_1613}")

    res_10_113 = check_b_exceptional_prime(10, 113)
    check(res_10_113 == (112, 56, [29, 56], 0), f"b=10, p=113: {res_10_113}")
    t, wp, wm, f = euler_digit_law(10, 113, 1)
    check(t == 112 and wp == wm == Fraction(1, 56), "E_10/113 balanced")
    expected_113 = [
        Fraction(353, 3136), Fraction(297, 3136), Fraction(297, 3136),
        Fraction(81, 784), Fraction(297, 3136), Fraction(297, 3136),
        Fraction(81, 784), Fraction(297, 3136), Fraction(297, 3136),
        Fraction(353, 3136),
    ]
    check(f == expected_113, "E_10/113 exact digits")

    # Verify infinite arithmetic progressions of bases b == b0 mod p preserve balanced exceptionality
    for b0, p in [(4, 29), (6, 59), (10, 113)]:
        ref = check_b_exceptional_prime(b0, p)
        for m_step in range(1, 6):
            check(check_b_exceptional_prime(b0 + m_step * p, p) == ref,
                  f"progression b={b0 + m_step*p}, p={p}")

    # 5. Extended base-2 Conjecture 5.5 search: ZERO 2-exceptional primes p <= 40,000
    ps40k = primes_up_to(40000)
    even_ord_cnt = 0
    for p in ps40k:
        if p == 2:
            continue
        res = check_b_exceptional_prime(2, p)
        check(res is None, f"Unexpected 2-exceptional prime p={p}")
        if mult_order(2, p) % 2 == 0:
            even_ord_cnt += 1
    print(f"  Verified 0 base-2 exceptional primes among {even_ord_cnt} even-order primes <= 40,000.")
    print("  Sub-track B3: ALL checks passed.")


# ============================================================================
# Sub-track B4: Multi-Radix Finite-Order Normality & Joint Constraints
# ============================================================================

def phased_debruijn_circuit(b: int, k: int, L: int) -> list[int]:
    """Construct an Euler circuit of length k * b^L in the phased de Bruijn
    graph G_phased(b, k, L) via Hierholzer's algorithm."""
    if L == 1:
        # Vertices are phases r in Z/kZ, edges (r, d) -> (r+1) mod k
        # Simply repeat 0, 1, ..., b-1 across k shifts? Need every (r, d) once!
        # Wait: edge (r, d) goes r -> (r+1) mod k.
        adj = {r: [d for d in range(b)] for r in range(k)}
        stack = [(0, None)]
        digits: list[int] = []
        while stack:
            v, incoming = stack[-1]
            if adj[v]:
                d = adj[v].pop()
                stack.append(((v + 1) % k, d))
            else:
                stack.pop()
                if incoming is not None:
                    digits.append(incoming)
        digits.reverse()
        return digits
    M = b ** (L - 1)
    # Vertex is (v, r) with 0 <= v < b^(L-1), 0 <= r < k
    adj2: dict[tuple[int, int], list[int]] = {
        (v, r): list(range(b)) for v in range(M) for r in range(k)
    }
    stack2: list[tuple[tuple[int, int], int | None]] = [((0, 0), None)]
    digits = []
    while stack2:
        (v, r), incoming = stack2[-1]
        if adj2[(v, r)]:
            d = adj2[(v, r)].pop()
            nv = (v * b + d) % M
            nr = (r + 1) % k
            stack2.append(((nv, nr), d))
        else:
            stack2.pop()
            if incoming is not None:
                digits.append(incoming)
    digits.reverse()
    return digits


def word_counts_cyclic(digits: list[int], b: int, L: int, step: int = 1, offset: int = 0) -> dict[tuple[int, ...], int]:
    """Count length-L base-b words at cyclic positions offset, offset+step, ..."""
    n = len(digits)
    counts: dict[tuple[int, ...], int] = {}
    for idx in range(offset, n, step):
        w = tuple(digits[(idx + j) % n] for j in range(L))
        counts[w] = counts.get(w, 0) + 1
    return counts


def verify_B4() -> None:
    print("=== Sub-track B4: Multi-radix finite-order normality & joint constraints ===")

    # 1. Exact sharpness of cross-radix order implication (Theorem 4.1):
    #    For (b, k, L2), check the Gray-code / Markov-transition sharpness
    #    At (b=2, k=2, L2=1): '00 01 11 10' is 1-normal in base 4, 1-normal in base 2, NOT 2-normal in base 2!
    gray22 = [0, 0, 0, 1, 1, 1, 1, 0]
    c_b4 = word_counts_cyclic(gray22, 2, 2, step=2)
    check(len(c_b4) == 4 and set(c_b4.values()) == {1}, "Gray 2,2 is 1-normal in base 4")
    c_b2_1 = word_counts_cyclic(gray22, 2, 1, step=1)
    check(c_b2_1 == {(0,): 4, (1,): 4}, "Gray 2,2 is 1-normal in base 2")
    c_b2_2 = word_counts_cyclic(gray22, 2, 2, step=1)
    check(c_b2_2[(0, 0)] == 3 and c_b2_2[(0, 1)] == 1, "Gray 2,2 fails 2-normality in base 2")

    # Verify the exact Markov sharpness formula f_{0^{l_*}} = b^{-l_*}(1 + (b-1)/(2k))
    # for multiple (b, k, L2) by explicit rational stationary distribution check!
    for b, k, L2 in [(2, 2, 1), (2, 3, 1), (3, 2, 1), (2, 2, 2)]:
        B = b ** k
        l_star = k * (L2 - 1) + 2
        # Under P_mix = (1/2) P_unif + (1/2) P_Pi on length-L2 base-B words,
        # where at v_0 = 0^{L2-1}, Pi maps {D_0 : b | D_0} bijectively onto {D_{L2} < b^{k-1}}:
        # Phase r in {0..k-2}: probability of 0^{l_*} is b^{-l_*}.
        # Phase r = k-1: needs D_0 == 0 mod b (size b^{k-1}), D_1..D_{L2-1} = 0, and D_{L2} < b^{k-1}.
        # Under P_unif: prob = b^{k-1} / B^{L2} * (b^{k-1} / B) = b^{2k-2} / b^{k(L2+1)} = b^{-l_*}.
        # Under P_Pi: every D_0 == 0 mod b maps with prob 1 into D_{L2} < b^{k-1}, so prob = b^{k-1} / B^{L2} = b * b^{-l_*}.
        p_unif = Fraction(b ** (k - 1), B ** L2) * Fraction(b ** (k - 1), B)
        p_pi = Fraction(b ** (k - 1), B ** L2)
        check(p_unif == Fraction(1, b ** l_star), f"p_unif == b^(-l_*) ({b},{k},{L2})")
        check(p_pi == Fraction(b, b ** l_star), f"p_pi == b * b^(-l_*) ({b},{k},{L2})")
        p_phase_last = Fraction(1, 2) * (p_unif + p_pi)
        f_overall = ((k - 1) * Fraction(1, b ** l_star) + p_phase_last) / k
        expected = Fraction(1, b ** l_star) * (1 + Fraction(b - 1, 2 * k))
        check(f_overall == expected and f_overall > Fraction(1, b ** l_star),
              f"Markov sharpness formula ({b},{k},{L2})")

    # 2. Reverse sharpness: L1-normal in base b, NOT 1-normal in base b^k
    #    via T_{b^k}-invariant symbolic measure
    #    rho = nu_{mk} + b^{-mk} * ( (1/m) sum_{j=0}^{m-1} delta_{T_b^{kj} u^infty}
    #                              - (1/m) sum_{j=0}^{m-1} delta_{T_b^{kj} v^infty} ),
    #    where u = 0^k 1^{(m-1)k} and v = T_b u.
    for b, k, L1 in [(2, 2, 2), (2, 3, 3), (3, 2, 3), (2, 2, 4)]:
        m = max(2, (L1 + k - 1) // k)
        mk = m * k
        u = [0] * k + [1] * ((m - 1) * k)
        tu = u[1:] + u[:1]
        # Base-b word counts of u^infty and (T_b u)^infty are identical for all lengths
        for ell in range(1, L1 + 1):
            check(word_counts_cyclic(u, b, ell, 1) == word_counts_cyclic(tu, b, ell, 1),
                  f"shift invariance u vs Tu ({b},{k},{L1},ell={ell})")
        # Base-b^k orbit average of u^infty visits 0^k with mass 1/m, v^infty with mass 0
        c_u = word_counts_cyclic(u, b, k, step=k).get((0,) * k, 0)
        c_tu = word_counts_cyclic(tu, b, k, step=k).get((0,) * k, 0)
        check(Fraction(c_u, m) - Fraction(c_tu, m) == Fraction(1, m),
              f"base-b^k orbit imbalance ({b},{k},{L1})")

    # 3. Explicit multi-radix discrepancy witnesses exceeding 2/b^{k L2}
    #    Compute exact full-multiset discrepancy via disc_multiset over all k phases!
    #    (a) (b=3, k=2, L2=1): 2/9 = 8/36, exact periodic mixture (18 equal-weight phase points)
    #        achieves exact discrepancy D_infty(x; 3) = 11/36 > 2/9 (and <= phase ceiling 4/9).
    #    Orbits of T_9: 0^infty (1/9), {1/8} (1/9), {3/8} (1/9), {1/2} (1/9), {5/8} (1/9),
    #                   {7/8} (1/9), {30/91, 88/91, 64/91} (1/3).
    orbits_32 = [
        (Fraction(1, 9), [Fraction(0)]),
        (Fraction(1, 9), [Fraction(1, 8)]),
        (Fraction(1, 9), [Fraction(3, 8)]),
        (Fraction(1, 9), [Fraction(1, 2)]),
        (Fraction(1, 9), [Fraction(5, 8)]),
        (Fraction(1, 9), [Fraction(7, 8)]),
        (Fraction(1, 3), [Fraction(30, 91), Fraction(88, 91), Fraction(64, 91)]),
    ]
    # Verify T_9 invariance, exact 1/9 mass in each base-9 cell, and equal per-phase atom weights
    cell_mass = [Fraction(0)] * 9
    pts_32: list[Fraction] = []
    for w, orb in orbits_32:
        check(w / (len(orb) * 2) == Fraction(1, 18), "(3,2,1) equal per-phase weight 1/18")
        for y in orb:
            check((9 * y) % 1 in orb, "T_9 invariant orbit")
            cell_mass[int(9 * y)] += w / len(orb)
            pts_32.extend([y, (3 * y) % 1])
    check(len(pts_32) == 18, "(3,2,1) phase multiset has 18 points")
    check(all(m == Fraction(1, 9) for m in cell_mass), "(3,2,1) witness is 1-normal in base 9")
    disc_32 = disc_multiset(pts_32)
    check(disc_32 == Fraction(11, 36), f"(3,2,1) exact discrepancy={disc_32}")
    check(disc_32 > Fraction(2, 9), "(3,2,1) strictly exceeds 2/9")
    # Also verify it obeys our phase-stratified upper bound 2*(3^2 - 1)/(2*(3-1)*9) = 4/9
    check(disc_32 <= Fraction(4, 9), "(3,2,1) obeys phase-stratified ceiling 4/9")

    #    (b) (b=2, k=3, L2=1): 2/8 = 1/4, exact periodic mixture (24 equal-weight phase points)
    #        achieves exact discrepancy D_infty(x; 2) = 1865/6132 > 1/4 (and <= phase ceiling 7/12).
    #    Orbits of T_8: {1/3, 2/3} (1/4), {51/511, 408/511, 198/511} (3/8),
    #                   {103/511, 313/511, 460/511} (3/8).
    orbits_23 = [
        (Fraction(1, 4), [Fraction(1, 3), Fraction(2, 3)]),
        (Fraction(3, 8), [Fraction(51, 511), Fraction(408, 511), Fraction(198, 511)]),
        (Fraction(3, 8), [Fraction(103, 511), Fraction(313, 511), Fraction(460, 511)]),
    ]
    cell_mass_23 = [Fraction(0)] * 8
    pts_23: list[Fraction] = []
    for w, orb in orbits_23:
        check(w / (len(orb) * 3) == Fraction(1, 24), "(2,3,1) equal per-phase weight 1/24")
        for y in orb:
            check((8 * y) % 1 in orb, "T_8 invariant orbit")
            cell_mass_23[int(8 * y)] += w / len(orb)
            pts_23.extend([y, (2 * y) % 1, (4 * y) % 1])
    check(len(pts_23) == 24, "(2,3,1) phase multiset has 24 points")
    check(all(m == Fraction(1, 8) for m in cell_mass_23), "(2,3,1) witness is 1-normal in base 8")
    disc_23 = disc_multiset(pts_23)
    check(disc_23 == Fraction(1865, 6132), f"(2,3,1) exact discrepancy={disc_23}")
    check(disc_23 > Fraction(1, 4), "(2,3,1) strictly exceeds 1/4")
    # Phase-stratified bound for (2,3,1): 2*(8-1)/(3*1*8) = 7/12
    check(disc_23 <= Fraction(7, 12), "(2,3,1) obeys phase-stratified ceiling 7/12")

    # 4. Phased de Bruijn Euler circuits (Theorem 4.3 sufficiency) AND exact
    #    parity obstruction at (b=2, k=2, L1=3, L2=1) in K_{2^8}
    #    First check obstruction at m = 8: test ALL 6 cyclic permutations of {00, 01, 10, 11}
    for perm in itertools.permutations([1, 2, 3]):
        seq = [0] + list(perm)
        bits = []
        for d in seq:
            bits.extend([d // 2, d % 2])
        c3 = word_counts_cyclic(bits, 2, 3, step=1)
        check(len(c3) < 8, f"No length-8 block is both 3-normal in base 2 and 1-normal in base 4: {seq}")

    #    Next verify phased de Bruijn Euler circuits achieve BOTH L1-normality in base b
    #    and L2-normality in base b^k at m = k * b^{max(L1, k*L2)}!
    for b, k, L1, L2 in [(2, 2, 3, 1), (2, 2, 2, 1), (2, 3, 3, 1), (3, 2, 2, 1)]:
        L_star = max(L1, k * L2)
        digs = phased_debruijn_circuit(b, k, L_star)
        m = k * (b ** L_star)
        check(len(digs) == m, f"phased circuit length {len(digs)} == {m}")
        # Check L1-normal in base b
        c_L1 = word_counts_cyclic(digs, b, L1, step=1)
        check(len(c_L1) == b ** L1 and set(c_L1.values()) == {m // (b ** L1)},
              f"phased circuit L1-normal ({b},{k},{L1},{L2})")
        # Check L2-normal in base b^k (length k*L2 words at step k)
        c_L2 = word_counts_cyclic(digs, b, k * L2, step=k)
        check(len(c_L2) == b ** (k * L2) and set(c_L2.values()) == {(m // k) // (b ** (k * L2))},
              f"phased circuit L2-normal in base b^k ({b},{k},{L1},{L2})")
        # Check NOT in K_b and NOT in K_{b^k}
        Q = b ** m - 1
        r = 0
        for d in digs:
            r = r * b + d
        check(0 < r < Q, "nonzero r < Q")
        check((b - 1) * r % Q != 0, "not in K_b")
        check((b ** k - 1) * r % Q != 0, "not in K_{b^k}")

    # 5. Kernel intersection gcd law: gcd(b^{k1}-1, b^{k2}-1) == b^{gcd(k1,k2)} - 1
    for b in [2, 3, 5, 10]:
        for k1 in range(1, 13):
            for k2 in range(1, 13):
                g = math.gcd(k1, k2)
                check(math.gcd(b ** k1 - 1, b ** k2 - 1) == b ** g - 1,
                      f"gcd law b={b}, k1={k1}, k2={k2}")

    # 6. Disjunctive perturbation planting identity (Theorem 4.5):
    #    For periodic c = r / (b^k - 1) with 0 < r < b^k - 1, verify exact word
    #    planting at sparse positions without carry corruption!
    for b, k, r in [(2, 4, 3), (3, 3, 5)]:
        Q = b ** k - 1
        # Plant all base-b words of length 2 at positions N_j = 10 + 12*j
        words = list(itertools.product(range(b), repeat=2))
        u_num = 0
        max_pos = 10 + 12 * len(words) + 10
        # Build u = sum v_j * b^{-(N_j + 2)}
        for idx, w in enumerate(words):
            Nj = 10 + 12 * idx
            # Digits of c at positions [Nj+1, Nj+2] (1-indexed): floor(b^2 * {b^Nj c})
            r_shift = (r * pow(b, Nj, Q)) % Q
            Cj = (b * b * r_shift) // Q
            Wj = w[0] * b + w[1]
            vj = (Wj - Cj) % (b * b)
            u_num += vj * (b ** (max_pos - (Nj + 2)))
        # Exact rational x = r/Q + u_num / b^max_pos
        x_frac = Fraction(r, Q) + Fraction(u_num, b ** max_pos)
        for idx, w in enumerate(words):
            Nj = 10 + 12 * idx
            # Extract length-2 word at shift Nj
            shifted = (x_frac * (b ** Nj)) % 1
            got = int(shifted * (b * b))
            Wj = w[0] * b + w[1]
            check(got == Wj, f"planted word b={b}, w={w}, got={got}")

    print("  Sub-track B4: ALL checks passed.")


def main() -> None:
    verify_B2()
    verify_B1()
    verify_B3()
    verify_B4()
    print(f"\nALL PHASE 24 TRACK B CHECKS PASSED ({CHECKS:,} exact checks, exit 0).")


if __name__ == "__main__":
    main()
