#!/usr/bin/env python3
"""Phase 24, Track E: Classical constants, joint BBP numerators, net carry complexity,
and the dyadic Lambert / E / E_+ obstruction map.

Companion to notes/phase24/classical-constants-and-joint-numerators.md.
Standard library only; exits 0 when every assertion holds.
Run:  python -B scripts/phase24_classical.py

Sections
  E1  Joint multi-prime BBP numerator correlations for ln 2:
      - Exact same-band CRT collapse and global smooth-defect identity (Theorem 1.1)
      - Exact consecutive-shift band evolution and Wieferich prime-square exits (Theorem 1.1(d))
      - Elementary O(n^{2/3}) dropped-prime mass bound (Theorem 1.2)
      - Exact top-band real realization ln 2 = alpha_top + beta_low (Theorem 1.3)
      - Joint multi-prime period character factorization & sharp r >= 2 / fixed-band barriers (Theorem 1.4)
  E2  Algebraic irrationals (sqrt(2), sqrt(3), phi) via net carry complexity:
      - Exact carry-gauge quadratic residual identity and binary borrow dichotomy (Theorem 2.1)
      - Elementary convolution-borrow lower bounds on s_b and squaring carry identity (Theorem 2.2)
      - Carry-gauge gap recurrence, signed-digit neutralization barrier (Theorem 2.3)
      - Exponential-carry deficit barrier for binomial/Catalan/Pell series (Theorem 2.4)
  E3  Classical Lambert & E / E_+ obstruction map:
      - Certified exact rational enclosures for mu_pop and mu_NAF (Theorem 3.1)
      - Exact binary and NAF carry-balance laws across E(2^k), E_odd(2^k), E_+(2^k) (Theorem 3.1)
      - Exact 4-state minimized NAF automaton, closed formula A_L, and E_+(2^k) nonnormality for k >= 3 (Theorem 3.2)
      - Exact 3-term / 4-term reduction of C_+(h; X) eliminating Hypothesis (H2) (Theorem 3.3)
      - Quantitative obstruction-map diagnostics across k = 1, 2, 3, 4 (Section 3.4)

Labels in printout:
  [exact]   exact integer / rational identity or inequality (a finite certificate);
  [encl]    rigorous rational enclosure of an infinite sum or Euler product;
  [float]   floating-point evaluation of an exact formula (not certified);
  [finite]  finite measurement (bears on no asymptotic limit).
"""

import cmath
import math
import sys
import time
from collections import Counter
from fractions import Fraction as Fr

T0 = time.time()
CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        print("FAILED:", msg)
        sys.exit(1)


def head(title):
    print("\n" + "=" * 78 + "\n" + title + "\n" + "=" * 78)


def sieve_primes(limit):
    s = bytearray([1]) * (limit + 1)
    s[0] = s[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(limit + 1) if s[i]], s


def v2(n):
    return (n & -n).bit_length() - 1


def odd_part(n):
    return n >> v2(n)


def naf_weight(n):
    """Exact minimum signed-digit (NAF) weight w_2^pm(n) for integer n."""
    n = abs(n)
    w = 0
    while n:
        if n & 1:
            d = 2 - (n & 3)
            n -= d
            w += 1
        n >>= 1
    return w


def naf_digits_le(n):
    """Return list of (position, sign in {-1, +1}) for NAF of n >= 0, ascending positions."""
    out = []
    pos = 0
    while n:
        if n & 1:
            d = 2 - (n & 3)
            out.append((pos, d))
            n -= d
        n >>= 1
        pos += 1
    return out


def base_b_digits(n, b):
    """Least-significant-first base-b digits of n >= 0."""
    if n == 0:
        return [0]
    out = []
    while n:
        out.append(n % b)
        n //= b
    return out


def icbrt(n):
    """Exact integer cube root floor(n^(1/3)) for n >= 0."""
    if n <= 0:
        return 0
    x = int(round(n ** (1.0 / 3.0)))
    while (x + 1) ** 3 <= n:
        x += 1
    while x ** 3 > n:
        x -= 1
    return x


def fmt_floor(fr, digits=6):
    """Exact outward-lower (floor) decimal string for Fraction fr >= 0."""
    check(fr >= 0, "fmt_floor expects non-negative Fraction")
    scale = 10 ** digits
    n = (fr.numerator * scale) // fr.denominator
    return f"{n // scale}.{n % scale:0{digits}d}"


def fmt_ceil(fr, digits=6):
    """Exact outward-upper (ceiling) decimal string for Fraction fr >= 0."""
    check(fr >= 0, "fmt_ceil expects non-negative Fraction")
    scale = 10 ** digits
    n = -((-fr.numerator * scale) // fr.denominator)
    return f"{n // scale}.{n % scale:0{digits}d}"


def mult_order(a, m):
    """Exact multiplicative order of a modulo m (gcd(a, m) == 1)."""
    if m == 1:
        return 1
    # Factor m by trial division (sufficient for all moduli tested here)
    phi = m
    x = m
    d = 2
    while d * d <= x:
        if x % d == 0:
            while x % d == 0:
                x //= d
            phi = phi // d * (d - 1)
        d += 1 if d == 2 else 2
    if x > 1:
        phi = phi // x * (x - 1)
    # Factor phi
    facs = []
    y = phi
    d = 2
    while d * d <= y:
        if y % d == 0:
            facs.append(d)
            while y % d == 0:
                y //= d
        d += 1 if d == 2 else 2
    if y > 1:
        facs.append(y)
    ord_val = phi
    for p in facs:
        while ord_val % p == 0 and pow(a, ord_val // p, m) == 1:
            ord_val //= p
    return ord_val


# ========================================================================= E1
def section_E1():
    head("E1. Joint Multi-Prime BBP Numerators for ln 2")
    NMAX = 1200
    PRIMES, IS_PRIME = sieve_primes(max(NMAX + 100, 5000))
    ODD_PRIMES = [p for p in PRIMES if p > 2]

    # Exact s_N = sum_{k=1}^N 2^(N-k)/k = A_N / Q_N
    s_list = [Fr(0)]
    A = [0]
    Q = [1]
    s = Fr(0)
    for n in range(1, NMAX + 1):
        s = 2 * s + Fr(1, n)
        s_list.append(s)
        A.append(s.numerator)
        Q.append(s.denominator)

    # --- Theorem 1.1(a)-(b): Same-band CRT collapse and explicit Q_m correction ---
    crt_checks = 0
    for N in range(6, 501):
        rN = math.isqrt(N)
        for m in range(1, rN + 1):
            lo = max(rN, N // (m + 1))
            hi = N // m
            band_all = [p for p in ODD_PRIMES if lo < p <= hi]
            surv = [p for p in band_all if A[m] % p != 0]
            if len(surv) < 2:
                continue
            M_S = 1
            for p in surv:
                M_S *= p
            H_S = sum(M_S // p for p in surv)
            # Compute actual sum_{p in surv} u_{N,p}/p mod 1 from exact s_N
            x_S_direct = Fr(0)
            for p in surv:
                # p s_N mod p = A_N * (Q_N / p)^(-1) mod p
                check(Q[N] % p == 0 and Q[N] % (p * p) != 0, "p || Q_N")
                u_p = (A[N] % p) * pow((Q[N] // p) % p, -1, p) % p
                x_S_direct += Fr(u_p, p)
            x_S_direct = x_S_direct - math.floor(x_S_direct)
            # Theorem 1.1(a): U_{N,S} = 2^(N-m) A_m Q_m^{-1} H_S mod M_S
            check(math.gcd(Q[m], M_S) == 1, "gcd(Q_m, M_S) = 1")
            U_pred = (pow(2, N - m, M_S) * (A[m] % M_S) * pow(Q[m] % M_S, -1, M_S) * (H_S % M_S)) % M_S
            check(x_S_direct == Fr(U_pred, M_S), "Theorem 1.1(a) same-band CRT collapse")
            # Theorem 1.1(b): explicit lift with Q_m correction
            B_Nm = (1 << (N - m)) * s_list[m] * sum(Fr(1, p) for p in surv)
            if Q[m] == 1:
                corr = Fr(0)
            else:
                inv_M = pow(M_S % Q[m], -1, Q[m])
                corr = Fr((pow(2, N - m, Q[m]) * (A[m] % Q[m]) * inv_M * (H_S % Q[m])) % Q[m], Q[m])
            diff = B_Nm - corr - x_S_direct
            check(diff.denominator == 1, "Theorem 1.1(b) exact Q_m-correction lift")
            crt_checks += 1
    print(f"[exact] Theorem 1.1(a)-(b): same-band CRT collapse & Q_m lift verified for {crt_checks} multi-prime bands (N <= 500)")

    # --- Theorem 1.1(c): Global band decomposition & explicit smooth defect ---
    def max_prime_factor(k):
        mp = 1
        d = 2
        x = k
        while d * d <= x:
            while x % d == 0:
                mp = d
                x //= d
            d += 1 if d == 2 else 2
        if x > 1:
            mp = x
        return mp

    def X_big_exact(n):
        rn = math.isqrt(n)
        tot = Fr(0)
        for m in range(1, rn + 1):
            lo = max(rn, n // (m + 1))
            hi = n // m
            harm = sum(Fr(1, p) for p in ODD_PRIMES if lo < p <= hi)
            if harm:
                tot += (1 << (n - m)) * s_list[m] * harm
        return tot

    smooth_checks = 0
    for N in range(4, 221):
        rN = math.isqrt(N)
        Xbig = X_big_exact(N)
        R_tilde = s_list[N] - Xbig
        # Check explicit generalized Fermat-quotient formula for R_tilde (N >= 4 => 2 <= sqrt(N))
        smooth_sum = sum(Fr(1 << (N - k), k) for k in range(1, N + 1) if max_prime_factor(k) <= rN)
        fermat_corr = Fr(0)
        for m in range(1, rN + 1):
            lo = max(rN, N // (m + 1))
            hi = N // m
            for p in ODD_PRIMES:
                if p > hi:
                    break
                if p <= lo:
                    continue
                for i in range(1, m + 1):
                    # (2^(i(p-1)) - 1) / p is an exact integer
                    num = (1 << (i * (p - 1))) - 1
                    check(num % p == 0, "generalized Fermat quotient integral")
                    fermat_corr += Fr((1 << (N - i * p)) * (num // p), i)
        check(R_tilde == smooth_sum - fermat_corr, "Theorem 1.1(c) explicit smooth defect")
        # Check denominator of R_tilde is sqrt(N)-smooth
        den = R_tilde.denominator
        check(den == 1 or max_prime_factor(den) <= rN, "R_tilde denominator is sqrt(N)-smooth")
        smooth_checks += 1
    print(f"[exact] Theorem 1.1(c): global band decomposition & explicit smooth defect verified for all 4 <= N <= {smooth_checks + 3}")

    # --- Theorem 1.1(d): Consecutive-shift evolution & Wieferich prime-square exits ---
    Xbig_cache = [Fr(0), Fr(0)] + [X_big_exact(n) for n in range(2, 305)]
    step_checks = 0
    sq_exits = []
    for n in range(4, 304):
        diff = Xbig_cache[n + 1] - 2 * Xbig_cache[n]
        r_next = math.isqrt(n + 1)
        if r_next * r_next == n + 1 and r_next > 2 and IS_PRIME[r_next]:
            p = r_next
            expected = -Fr(1 << (p * p - p + 1), p) * s_list[p - 1]
            check(diff == expected, f"Theorem 1.1(d) prime-square exit at n+1={p}^2")
            # Check mod 1 p-part is -2 q_p(2)/p mod 1 (up to Q_{p-1}-smooth part)
            qp = (pow(2, p - 1, p * p) - 1) // p % p
            p_res = (diff.numerator % p) * pow((diff.denominator // p) % p, -1, p) % p if diff.denominator % p == 0 else 0
            check(p_res == (-2 * qp) % p, "prime-square exit p-residue = -2 q_p(2) mod p")
            sq_exits.append((p, qp, p_res))
        else:
            P_plus = max_prime_factor(n + 1)
            if P_plus <= r_next:
                check(diff == 0, "Theorem 1.1(d) smooth step gives zero jump")
            else:
                m = (n + 1) // P_plus
                check(diff == Fr(1 << (n + 1 - m), n + 1), "Theorem 1.1(d) large-prime step jump")
        step_checks += 1
    # Multi-step check across windows [N, N+Delta]
    for N, Delta in ((40, 20), (115, 25), (165, 20), (280, 20)):
        for t in range(1, Delta + 1):
            lhs = Xbig_cache[N + t] - (1 << t) * Xbig_cache[N]
            rhs = Fr(0)
            for j in range(N + 1, N + t + 1):
                rj = math.isqrt(j)
                if rj * rj == j and rj > 2 and IS_PRIME[rj]:
                    p = rj
                    rhs -= Fr(1 << (N + t - p + 1), p) * s_list[p - 1]
                else:
                    Pp = max_prime_factor(j)
                    if Pp > rj:
                        rhs += Fr(1 << (N + t - j // Pp), j)
            check(lhs == rhs, f"Theorem 1.1(d) multi-step evolution at N={N}, t={t}")
    # Check Wieferich primes 1093, 3511 have vanishing exit residue
    for wp in (1093, 3511):
        check((pow(2, wp - 1, wp * wp) - 1) // wp % wp == 0, f"Wieferich prime {wp} exit vanishes")
    print(f"[exact] Theorem 1.1(d): consecutive & multi-step band evolution verified ({step_checks} steps, prime-square exits p = {[x[0] for x in sq_exits]})")

    # --- Theorem 1.2: Unconditional O(n^{2/3}) dropped-prime mass bound ---
    # Exact integer checks: A_m < 8^m and prod_{p in D_n} p satisfies exact integer exponent bound
    max_logA_ratio = 0.0
    for m in range(1, NMAX + 1):
        check(A[m] < (1 << (3 * m)), f"A_m < 8^m at m={m}")
        max_logA_ratio = max(max_logA_ratio, math.log2(A[m]) / m)
    worst_drop_ratio = 0.0
    max_drop_count = 0
    for n in range(2, NMAX + 1):
        rn = math.isqrt(n)
        drop_prod = 1
        drop_log = 0.0
        drop_cnt = 0
        for p in ODD_PRIMES:
            if p > n:
                break
            if p <= rn:
                continue
            m = n // p
            if A[m] % p == 0:
                drop_prod *= p
                drop_log += math.log(p)
                drop_cnt += 1
        # Exact integer cutoff M1 = max(1, floor((2n/3)^(1/3)))
        M1 = max(1, icbrt((2 * n) // 3))
        # Exact integer inequality: prod_{p in D_n} p <= 2^{(3/2)M1(M1+1) + 2n/(M1+1)}
        check(drop_prod ** (2 * (M1 + 1)) <= (1 << (3 * M1 * (M1 + 1) ** 2 + 4 * n)),
              f"Theorem 1.2 exact integer dropped-prime product bound at n={n}")
        # Floating-point check of the 4 n^(2/3) bound
        elem_bound = (1.5 * M1 * (M1 + 1) + 2.0 * n / (M1 + 1)) * math.log(2)
        check(drop_log <= elem_bound + 1e-12, "Theorem 1.2 [float] elementary M1 bound")
        check(drop_log <= 4.0 * (n ** (2.0 / 3.0)), "Theorem 1.2 [float] <= 4 n^(2/3)")
        if n >= 10:
            worst_drop_ratio = max(worst_drop_ratio, drop_log / (n ** (2.0 / 3.0)))
        max_drop_count = max(max_drop_count, drop_cnt)
    # Floating-point check of analytic constant <= 4 n^(2/3) for 2 <= n < 20000
    for n in range(2, 20000):
        M1 = max(1, icbrt((2 * n) // 3))
        val = (1.5 * M1 * (M1 + 1) + 2.0 * n / (M1 + 1)) * math.log(2)
        check(val <= 4.0 * (n ** (2.0 / 3.0)), f"Theorem 1.2 [float] analytic constant <= 4 n^(2/3) at n={n}")
    print(f"[exact] Theorem 1.2: A_m < 8^m (1 <= m <= {NMAX}) and exact integer product bound")
    print(f"        (prod_{{p in D_n}} p)^(2(M1+1)) <= 2^(3 M1(M1+1)^2 + 4n) verified (2 <= n <= {NMAX}, max #D_n = {max_drop_count})")
    print(f"[float] Theorem 1.2: max log_2(A_m)/m = {max_logA_ratio:.4f}; sum_(p in D_n) log p <= 4 n^(2/3)")
    print(f"        checked numerically (observed max / n^(2/3) = {worst_drop_ratio:.4f}; analytic constant n < 20000)")

    # --- Theorem 1.3: Exact top-band real realization alpha_top ---
    # Exact recurrence for Phi_{n,1} = 2^(n-1) sum_{n/2 < p <= n} 1/p mod 1, with Phi_{2,1} = 0
    def phi_top(n):
        if n <= 2:
            return Fr(0)
        s_ = Fr(0)
        for p in ODD_PRIMES:
            if p > n:
                break
            if 2 * p > n:
                s_ += Fr(pow(2, n - 1, p), p)
        return s_ - math.floor(s_)

    check(phi_top(2) == Fr(0), "Theorem 1.3 Phi_{2,1} = 0")
    phi_prev = phi_top(3)
    for n in range(3, 800):
        phi_curr = phi_top(n + 1)
        kick = Fr(1, n + 1) if IS_PRIME[n + 1] else Fr(0)
        if (n + 1) % 2 == 0 and ((n + 1) // 2) > 2 and IS_PRIME[(n + 1) // 2]:
            kick -= Fr(2, (n + 1) // 2)
        rhs = (2 * phi_prev + kick)
        rhs = rhs - math.floor(rhs)
        check(phi_curr == rhs, f"Theorem 1.3 top-band recurrence at n={n}")
        phi_prev = phi_curr
    print("[exact] Theorem 1.3: exact recurrence for Phi_{n,1} verified (3 <= n <= 800; Phi_{2,1} = 0)")

    # Certified fixed-point enclosure of alpha_top = sum_{p>=3} (1 - 2^(1-p))/(p 2^p) at scale 2^W
    ND = 1 << 12
    W = ND + 128
    alpha_top_scaled = 0
    used_primes = 0
    for p in ODD_PRIMES:
        if p > W:
            break
        # Each term (2^(W-p) - 2^(W+1-2p))/p rounded by floor on both parts has error in (-1, +1)
        t1 = (1 << (W - p)) // p
        t2 = (1 << (W + 1 - 2 * p)) // p if W + 1 - 2 * p >= 0 else 0
        alpha_top_scaled += t1 - t2
        used_primes += 1
    # Rigorous error bound on alpha_top_scaled / 2^W:
    # rounding <= used_primes, omitted tail sum_{p > W} (1 - 2^(1-p))/(p 2^p) < 2^(-W)/W < 2^(-W),
    # hence |alpha_top - alpha_top_scaled / 2^W| < (used_primes + 1) / 2^W.
    alpha_err_W = used_primes + 1
    # Also compute ln 2 to W bits via (2/3) sum 9^-k/(2k+1)
    t = (2 << W) // 3
    ln2_scaled = 0
    k = 0
    while t:
        ln2_scaled += t // (2 * k + 1)
        t //= 9
        k += 1
    beta_low_scaled = (ln2_scaled - alpha_top_scaled) % (1 << W)
    # Certified shadowing {2^n alpha_top} = {Phi_{n,1} + r_n^top} and |r_n^top| < 8/(3n)
    # with explicit propagated rounding + tail bounds:
    for n in [2, 3] + list(range(4, 201, 3)):
        ph = phi_top(n)
        # r_n^top truncated to p <= n + 80; omitted positive tail < sum_{k > 80} 2^(-k)/(n+80) = 2^(-80)/(n+80) < 2^(-80)
        r_top_trunc = Fr(0)
        for p in ODD_PRIMES:
            if p > n + 80:
                break
            if p > n:
                r_top_trunc += Fr((1 << (p - 1)) - 1, p * (1 << (2 * p - 1 - n)))
            elif 2 * p > n:
                r_top_trunc -= Fr(1, p * (1 << (2 * p - n - 1)))
        r_tail_hi = Fr(1, (n + 80) * (1 << 80))
        check(abs(r_top_trunc) + r_tail_hi < Fr(8, 3 * n), f"Theorem 1.3 certified |r_n^top| < 8/(3n) at n={n}")
        # Propagated error on 2^n alpha_top mod 1:
        # shift error < alpha_err_W * 2^(n - W), 44-bit truncation error < 2^(-44), r_top tail < r_tail_hi
        shifted = (alpha_top_scaled << n) % (1 << W)
        approx_frac = Fr(shifted >> (W - 44), 1 << 44)
        pred = (ph + r_top_trunc)
        pred = pred - math.floor(pred)
        d = abs(pred - approx_frac)
        d = min(d, 1 - d)
        total_err_bound = Fr(alpha_err_W, 1 << (W - n)) + Fr(1, 1 << 44) + r_tail_hi
        check(d <= total_err_bound, f"Theorem 1.3 certified fixed-point shadowing at n={n}")
        check(total_err_bound < Fr(1, 1 << 43), f"Theorem 1.3 shadowing precision < 2^(-43) at n={n}")
    print("[encl]  Theorem 1.3: certified |r_n^top| < 8/(3n) and fixed-point shadowing")
    print("        {2^n alpha_top} = {Phi_{n,1} + r_n^top} to < 2^(-43) with propagated tail/rounding bounds (n <= 200)")

    # --- Theorem 1.4: Joint r=2 period factorization & Barriers 1-2 ---
    small_odd = [p for p in ODD_PRIMES if p <= 67]
    pair_cnt = 0
    prim_g2_cnt = 0
    max_gauss_ratio = 0.0
    for i, p1 in enumerate(small_odd):
        t1 = mult_order(2, p1)
        for p2 in small_odd[i + 1:]:
            t2 = mult_order(2, p2)
            g = math.gcd(t1, t2)
            T = t1 * t2 // g
            c1, c2 = 1, 1
            # Direct period sum
            direct = sum(cmath.exp(2j * math.pi * (pow(2, k, p1) * c1 / p1 + pow(2, k, p2) * c2 / p2))
                         for k in range(T))
            # Exact g-character factorization formula
            factored = 0j
            for j in range(g):
                s1 = sum(cmath.exp(2j * math.pi * (j * a / g + pow(2, a, p1) * c1 / p1)) for a in range(t1))
                s2 = sum(cmath.exp(2j * math.pi * (-j * b / g + pow(2, b, p2) * c2 / p2)) for b in range(t2))
                factored += s1 * s2
            factored /= g
            check(abs(direct - factored) < 1e-8, f"Theorem 1.4 [float] pair factorization ({p1},{p2})")
            # Check Korobov / Gauss bound <= sqrt(p1 p2)
            ratio = abs(direct) / math.sqrt(p1 * p2)
            check(ratio <= 1.0 + 1e-9, f"Theorem 1.4 [float] <= sqrt(p1 p2) at ({p1},{p2})")
            max_gauss_ratio = max(max_gauss_ratio, ratio)
            # Check exact primitive-root g=2 closed form: (1 + eps1 eps2 sqrt(p1 p2)) / 2 (for c1=c2=1)
            if t1 == p1 - 1 and t2 == p2 - 1 and g == 2:
                eps1 = 1.0 if p1 % 4 == 1 else 1j
                eps2 = 1.0 if p2 % 4 == 1 else 1j
                closed = 0.5 * (1.0 + eps1 * eps2 * math.sqrt(p1 * p2))
                check(abs(direct - closed) < 1e-8, f"Theorem 1.4 [float] g=2 primitive-root closed form ({p1},{p2})")
                prim_g2_cnt += 1
            pair_cnt += 1
    print(f"[float] Theorem 1.4: r=2 period character factorization evaluated numerically on {pair_cnt} pairs (p <= 67, c1=c2=1),")
    print(f"        {prim_g2_cnt} primitive-root g=2 pairs match (1 + eps1 eps2 sqrt(p1 p2))/2; max |S|/sqrt(p1 p2) = {max_gauss_ratio:.4f}")

    # Barrier 1 check: for all same-band pairs p1 < p2 in band m, L_W = (m+1)p1 - m p2 < p1 < sqrt(p1 p2)
    b1_cnt = 0
    for N in range(20, 401, 5):
        rN = math.isqrt(N)
        for m in range(1, rN + 1):
            lo = max(rN, N // (m + 1))
            hi = N // m
            ps = [p for p in ODD_PRIMES if lo < p <= hi]
            for i in range(len(ps)):
                for j in range(i + 1, len(ps)):
                    p1, p2 = ps[i], ps[j]
                    LW = (m + 1) * p1 - m * p2
                    check(0 < LW < p1 and LW * LW < p1 * p2, "Barrier 1: L_W < p1 < sqrt(p1 p2)")
                    b1_cnt += 1

    # Barrier 2 check: fixed-band complement alignment with exact denominator Q_n
    b2_cnt = 0
    for M0 in (1, 2, 3):
        for theta in (Fr(0, 1), Fr(1, 3)):
            for n in range(100, 351, 5):
                rn = math.isqrt(n)
                P_n = [p for p in ODD_PRIMES if rn < p <= n and A[n // p] % p != 0]
                lower = [p for p in P_n if n // p > M0]
                check(len(lower) >= 1, f"Barrier 2: surviving lower-band prime at n={n}, M0={M0}")
                p_star = max(lower)
                check(p_star > n / (2 * (M0 + 1)), f"Barrier 2: p_star > n/(2(M0+1)) at n={n}, M0={M0}")
                x_n = s_list[n] - math.floor(s_list[n])
                base = x_n
                for p in lower:
                    u_p = (A[n] % p) * pow((Q[n] // p) % p, -1, p) % p
                    base -= Fr(u_p, p)
                    if p != p_star:
                        base += Fr(1, p)
                base = base - math.floor(base)
                # Choose u_star in {1, ..., p_star - 1} minimizing circle distance of base + u_star/p_star to theta
                target_shift = (theta - base) - math.floor(theta - base)
                u0 = int(target_shift * p_star) % p_star
                best_u = 1
                best_d = Fr(1)
                for cand in ((u0 - 1) % p_star, u0, (u0 + 1) % p_star, (u0 + 2) % p_star):
                    if cand == 0:
                        continue
                    val = (base + Fr(cand, p_star)) - math.floor(base + Fr(cand, p_star))
                    d = abs(val - theta)
                    d = min(d, 1 - d)
                    if d < best_d:
                        best_d = d
                        best_u = cand
                x_tilde = (base + Fr(best_u, p_star)) - math.floor(base + Fr(best_u, p_star))
                check(x_tilde.denominator == Q[n], "Barrier 2: modified state preserves exact reduced denominator Q_n")
                check(best_d <= Fr(1, p_star), "Barrier 2: circle distance <= 1/p^*")
                b2_cnt += 1
    print(f"[exact] Theorem 1.4 Barriers: Barrier 1 checked on {b1_cnt} same-band pairs; Barrier 2 exact-Q_n")
    print(f"        alignment checked on {b2_cnt} instances (M0 in {{1,2,3}}, theta in {{0, 1/3}})")

    # [finite] Illustrative Weyl sums |S_N(1)| for ln 2, alpha_top, beta_low
    print("[finite] Illustrative first-frequency Weyl sums |S_N(1)| (53-bit points; finite data only):")
    for N in (1 << 10, 1 << 11, 1 << 12):
        vals = []
        for scaled in (ln2_scaled, alpha_top_scaled, beta_low_scaled):
            z = 0j
            for n in range(N):
                sh = (scaled << n) % (1 << W)
                x = (sh >> (W - 53)) / (2.0 ** 53)
                z += cmath.exp(2j * math.pi * x)
            vals.append(abs(z) / N)
        print(f"         N = {N:4d}:  ln 2: {vals[0]:.4f}   alpha_top: {vals[1]:.4f}   beta_low: {vals[2]:.4f}")


# ========================================================================= E2
def section_E2():
    head("E2. Algebraic Irrationals (sqrt(2), sqrt(3), phi) via Net Carry Complexity")

    # Helper: exact N-bit integer prefix x_N = floor(2^N alpha)
    def prefix_sqrtD(D, N):
        return math.isqrt(D << (2 * N))

    def prefix_phi(N):
        # floor(2^N * (1 + sqrt(5))/2) = floor((2^N + sqrt(5 * 4^N))/2)
        return ((1 << N) + math.isqrt(5 << (2 * N))) // 2

    # --- Theorem 2.1: Exact carry-gauge quadratic residual & binary borrow dichotomy ---
    t21_cnt = 0
    t21_Ns = [2, 3, 4, 5] + list(range(10, 301, 5))
    for name, A_c, B_c, C_c, D_disc, pref_fn in [
        ("sqrt(2)", 1, 0, -2, 8, lambda N: prefix_sqrtD(2, N)),
        ("sqrt(3)", 1, 0, -3, 12, lambda N: prefix_sqrtD(3, N)),
        ("phi", 1, -1, -1, 5, prefix_phi),
    ]:
        for N in t21_Ns:
            xN = pref_fn(N)
            # Check for gauge shifts delta_{N+1} in {-1, 0, 1}
            for delta in (-1, 0, 1):
                xp = xN - delta
                Ep = -(A_c * xp * xp + B_c * (1 << N) * xp + C_c * (1 << (2 * N)))
                zp = 2 * A_c * xp + B_c * (1 << N)
                check(D_disc * (1 << (2 * N)) - zp * zp == 4 * A_c * Ep, "Theorem 2.1 completed-square identity")
                check(Ep != 0, "Theorem 2.1 residual nonzero")
                if delta >= 0:
                    check(Ep > 0, "delta >= 0 => E'_N > 0 (borrow)")
                else:
                    check(Ep < 0, "delta = -1 => E'_N < 0 (no borrow)")
                t21_cnt += 1
            # Binary borrow dichotomy on sqrt(2) for delta_{N+1} in {0, -1} (all N >= 2)
            if name == "sqrt(2)":
                sq0 = xN * xN
                sq1 = (xN + 1) * (xN + 1)
                # bits [N+2, 2N] of sq0 are ALL 1; of sq1 are ALL 0!
                mask = ((1 << (N - 1)) - 1) << (N + 2)
                check((sq0 & mask) == mask, "Theorem 2.1 dichotomy: delta=0 => all 1s in [N+2, 2N]")
                check((sq1 & mask) == 0, "Theorem 2.1 dichotomy: delta=-1 => all 0s in [N+2, 2N]")
    print(f"[exact] Theorem 2.1: quadratic residual, completed-square identity, and binary borrow dichotomy")
    print(f"        verified on sqrt(2), sqrt(3), phi ({t21_cnt} exact instances, N = 2..300)")

    # --- Theorem 2.2: Elementary convolution-borrow bounds & squaring carry identity ---
    # Start each sequence at its exact stated endpoint (N >= 2 for sqrt(2), N >= 3 for sqrt(3), N >= 5 for phi)
    for N in range(2, 1001):
        x2 = prefix_sqrtD(2, N)
        s2_x2 = x2.bit_count()
        check((x2 * x2).bit_count() >= N - 1, "sqrt(2): s_2(x_N^2) >= N - 1")
        check(s2_x2 * (s2_x2 + 1) // 2 >= (x2 * x2).bit_count(), "s_2(x^2) <= s_2(x)(s_2(x)+1)/2")
        check(s2_x2 * (s2_x2 + 1) >= 2 * (N - 1), "sqrt(2) exact integer explicit lower bound")

    for N in range(3, 1001):
        x3 = prefix_sqrtD(3, N)
        s2_x3 = x3.bit_count()
        check((x3 * x3).bit_count() >= N - 2, "sqrt(3): s_2(x_N^2) >= N - 2")
        check((x3 * x3).bit_count() >= N - 1, "sqrt(3): surviving high bit 2N+1 gives s_2(x_N^2) >= N - 1")
        check(s2_x3 * (s2_x3 + 1) >= 2 * (N - 2), "sqrt(3) exact integer explicit lower bound")

    for N in range(5, 1001):
        xp = prefix_phi(N)
        zp = 2 * xp - (1 << N)
        check(zp.bit_count() == xp.bit_count() - 1, "phi: s_2(2 x_N - 2^N) = s_2(x_N) - 1")
        check((zp * zp).bit_count() >= N - 4, "phi: s_2(z_N^2) >= N - 4")
        check((zp * zp).bit_count() >= N - 3, "phi: surviving high bit 2N+2 gives s_2(z_N^2) >= N - 3")
        check((xp.bit_count() - 1) * xp.bit_count() >= 2 * (N - 4), "phi exact integer explicit lower bound")

    # Ordinary-digit check at N = 0 when d_0 >= b (e.g. b = 2, alpha = sqrt(5) => x_0 = 2, w_2^+(x_0) = 1)
    check(sum(base_b_digits(prefix_sqrtD(5, 0), 2)) == 1, "ordinary digits of entire integer x_0 = 2 give w_2^+(x_0) = 1")

    # General base b >= 2 squaring carry identity (b-1) Gamma_N = w_b^+(x_N)^2 - w_b^+(x_N^2)
    carry_id_cnt = 0
    for b in (2, 3, 5, 10):
        for D in (2, 3, 5):
            v_bD = 0
            tmp = D
            while tmp % b == 0:
                v_bD += 1
                tmp //= b
            c_shift = int(math.floor(math.log(2 * math.sqrt(D), b))) + 1
            for N in (20, 50, 100):
                xN = math.isqrt(D * (b ** (2 * N)))
                digs = base_b_digits(xN, b)
                wb_x = sum(digs)
                wb_x2 = sum(base_b_digits(xN * xN, b))
                # Compute exact squaring carries Gamma_N directly column-by-column
                conv = [0] * (2 * len(digs) + 2)
                for i, di in enumerate(digs):
                    for j, dj in enumerate(digs):
                        conv[i + j] += di * dj
                gamma = 0
                c_in = 0
                for col in conv:
                    tot = col + c_in
                    c_out = tot // b
                    gamma += c_out
                    c_in = c_out
                while c_in:
                    c_out = c_in // b
                    gamma += c_out
                    c_in = c_out
                check((b - 1) * gamma == wb_x * wb_x - wb_x2, "Theorem 2.2 exact squaring carry identity")
                check(wb_x2 >= (b - 1) * (N + v_bD - c_shift), "Theorem 2.2 base-b borrow lower bound")
                check(wb_x * wb_x >= (b - 1) * (N + v_bD - c_shift), "Theorem 2.2 base-b digit-sum bound")
                carry_id_cnt += 1
    print(f"[exact] Theorem 2.2: explicit s_2 bounds verified from exact endpoints (sqrt(2): N>=2, sqrt(3): N>=3, phi: N>=5, to 1000);")
    print(f"        exact base-b squaring carry identity (b-1)Gamma_N = w_b(x_N)^2 - w_b(x_N^2) checked ({carry_id_cnt} cases)")

    # --- Theorem 2.3: Carry-gauge gap recurrence & signed-digit neutralization witnesses ---
    N_GAP = 2000
    for name, pref_fn, bound_c, m1_max in [
        ("sqrt(2)", lambda N: prefix_sqrtD(2, N), 2, 2),
        ("sqrt(3)", lambda N: prefix_sqrtD(3, N), 3, 2),
        ("phi", prefix_phi, 2, 2),
    ]:
        xN = pref_fn(N_GAP)
        naf = naf_digits_le(xN)
        # Keep ONLY fractional positions m_j = N_GAP - pos >= 1 (integer part m <= 0 excluded)
        ms = [N_GAP - pos for pos, _ in reversed(naf) if N_GAP - pos >= 1]
        check(ms[0] <= m1_max, f"Theorem 2.3 first fractional position m_1 <= M_1 for {name}")
        for j in range(len(ms) - 1):
            check(ms[j + 1] <= 2 * ms[j] + bound_c, f"Theorem 2.3 gap recurrence for {name} at j={j}")
        # Check repaired all-N lower bound K >= log_2((N + 1 + c)/(M_1 + c)) including N = 1
        idx = 0
        for N in (1, 2, 3, 5, 10, 100, 1000, N_GAP):
            while idx < len(ms) and ms[idx] <= N:
                idx += 1
            check((1 << idx) * (m1_max + bound_c) >= N + 1 + bound_c,
                  f"Theorem 2.3 repaired all-N support bound for {name} at N={N}")
    # Signed-digit neutralization witnesses u_N = 2^N - 1
    for N in range(4, 201):
        uN = (1 << N) - 1
        check(uN.bit_count() == N and naf_weight(uN) == 2, "witness u_N = 2^N - 1")
        check((uN * uN).bit_count() == N and naf_weight(uN * uN) == 3, "witness u_N^2: s_2 = N, w_2^pm = 3")
    print("[exact] Theorem 2.3: carry-gauge gap recurrence m_{j+1} <= 2 m_j + c (all fractional m_j >= 1) and")
    print("        repaired all-N support bound verified on NAF prefixes (N <= 2000); neutralization witnesses u_N = 2^N - 1 (4 <= N <= 200)")

    # --- Theorem 2.4: Exponential-carry deficit barrier for binomial/Catalan/Pell series ---
    # Verify Kummer's theorem v_2(C(2k, k)) = s_2(k) for 0 <= k <= 400
    for k in range(401):
        c = math.comb(2 * k, k)
        check(v2(c) == k.bit_count(), "Kummer: v_2(binom(2k, k)) = s_2(k)")

    # Verify all 4 dyadic integer-coefficient series + genuine base-200 gauge/width check for Series 5
    # Series 1: sqrt(2) = sum_{k>=0} binom(2k, k) 2^(-3k)
    # Series 2: sqrt(2) = sum_{k>=0} (-1)^k * 3 * binom(2k, k) 2^(-(5k+1))
    # Series 3: sqrt(3) = 2 - sum_{k>=1} C_{k-1} 2^(-(4k-2))
    # Series 4: phi     = 3/2 + sum_{k>=1} (-1)^(k-1) C_{k-1} 2^(-(4k-1))
    # Series 5: 5*sqrt(2) = 7 * sum_{k>=0} binom(2k, k) 200^(-k)
    PREC = 240
    # Exact scaled sum S / 2^PREC
    def check_dyadic_series(name, target_int, coeff_fn, step_s, offset_r, rho_num, rho_den, n_terms, extra_terms=None):
        M = step_s * n_terms + max(offset_r, 0) + 10
        num_sum = 0
        a_map = dict(extra_terms) if extra_terms else {}
        for k in range(n_terms + 1):
            m, val = coeff_fn(k)
            if m < 0:
                continue
            a_map[m] = a_map.get(m, 0) + val
        for m, val in a_map.items():
            if m <= M:
                num_sum += val * (1 << (M - m))
        approx = num_sum >> (M - PREC)
        check(abs(approx - target_int) <= 2, f"Theorem 2.4 series identity for {name}")
        digits = [(target_int >> (PREC - j)) & 1 for j in range(1, 121)]
        deltas = {}
        xp = 0
        for n in range(0, 120):
            xp = 2 * xp + a_map.get(n, 0)
            xn = target_int >> (PREC - n)
            deltas[n + 1] = xn - xp
        for m in range(1, 119):
            check(a_map.get(m, 0) == digits[m - 1] + 2 * deltas[m] - deltas[m + 1],
                  f"Theorem 2.4 exact gauge identity for {name} at m={m}")
        N_w = 300
        wu = 0
        for m, val in a_map.items():
            if 1 <= m <= N_w and val != 0:
                u = odd_part(abs(val))
                wu += u.bit_length()
        pred_coef = rho_num / (2.0 * rho_den * step_s)
        obs_coef = wu / (N_w * N_w)
        max_d = max(abs(deltas[m]) for m in range(100, 120))
        check(max_d > (1 << int(100 * rho_num / rho_den - 15)), f"Theorem 2.4 exponential carry growth for {name}")
        return obs_coef, pred_coef, math.log2(abs(deltas[110])) / 110.0 if deltas[110] != 0 else 0.0

    r1 = check_dyadic_series("sqrt(2) [8^-k]", prefix_sqrtD(2, PREC),
                             lambda k: (3 * k, math.comb(2 * k, k)), 3, 0, 2, 3, 250)
    r2 = check_dyadic_series("sqrt(2) [32^-k]", prefix_sqrtD(2, PREC),
                             lambda k: (5 * k + 1, ((-1) ** k) * 3 * math.comb(2 * k, k)), 5, 1, 2, 5, 160)
    r3 = check_dyadic_series("sqrt(3) [16^-k]", prefix_sqrtD(3, PREC),
                             lambda k: (-1, 0) if k == 0 else (4 * k - 2, -(math.comb(2 * (k - 1), k - 1) // k)),
                             4, -2, 1, 2, 160, extra_terms={0: 2})
    r4 = check_dyadic_series("phi [16^-k]", prefix_phi(PREC),
                             lambda k: (-1, 0) if k == 0 else (4 * k - 1, ((-1) ** (k - 1)) * (math.comb(2 * (k - 1), k - 1) // k)),
                             4, -1, 1, 2, 160, extra_terms={0: 1, 1: 1})
    # Double-check Series 4 cleanly: phi = 3/2 + sum_{k>=1} (-1)^(k-1) C_{k-1} 2^{-(4k-1)}
    s4_exact = Fr(3, 2) + sum(Fr(((-1) ** (k - 1)) * (math.comb(2 * (k - 1), k - 1) // k), 1 << (4 * k - 1)) for k in range(1, 120))
    phi_exact_err = abs(s4_exact * s4_exact - s4_exact - 1)
    check(phi_exact_err < Fr(1, 1 << 230), "Series 4 exact convergence to phi")

    # Series 5: 5 sqrt(2) = 7 sum_{k>=0} binom(2k, k) 200^(-k) -- genuine base-200 gauge & width check
    s5_exact = Fr(7, 5) * sum(Fr(math.comb(2 * k, k), 200 ** k) for k in range(45))
    check(abs(s5_exact * s5_exact - 2) < Fr(1, 10 ** 75), "Series 5 (7/5)(1-1/50)^(-1/2) = sqrt(2)")
    B200 = 200
    PREC200 = 80
    # Exact prefix floor(200^PREC200 * 5 * sqrt(2)) = isqrt(50 * 200^(2*PREC200))
    target_200 = math.isqrt(50 * (B200 ** (2 * PREC200)))
    # Base-200 digits d_0, d_1, ..., d_60 of 5*sqrt(2)
    digits_200 = []
    for n in range(1, 61):
        xn = target_200 // (B200 ** (PREC200 - n))
        xn_prev = target_200 // (B200 ** (PREC200 - (n - 1)))
        digits_200.append(xn - B200 * xn_prev)
    deltas_200 = {}
    xp200 = 0
    for n in range(0, 61):
        a_n = 7 * math.comb(2 * n, n)
        xp200 = B200 * xp200 + a_n
        xn = target_200 // (B200 ** (PREC200 - n))
        deltas_200[n + 1] = xn - xp200
    for m in range(1, 60):
        a_m = 7 * math.comb(2 * m, m)
        check(a_m == digits_200[m - 1] + B200 * deltas_200[m] - deltas_200[m + 1],
              f"Theorem 2.4 exact base-200 gauge identity at m={m}")
    # Exponential base-200 carry growth: |delta_60| ~ 4^60 / sqrt(pi*60) * 7/200
    check(abs(deltas_200[60]) > (1 << 110), "Theorem 2.4 base-200 exponential carry growth")
    # Displaced radix-200 width W_{U,200}(300) (stripping complete powers of 200) vs binary width W_{U,2}(300)
    N_w200 = 300
    wu_200 = 0
    wu_200_bin = 0
    for k in range(1, N_w200 + 1):
        ak = 7 * math.comb(2 * k, k)
        # Strip complete powers of 200
        v200_ak = 0
        u200 = ak
        while u200 % B200 == 0:
            u200 //= B200
            v200_ak += 1
        check(v200_ak <= v2(ak) // 3, f"v_200(a_k) <= v_2(a_k)/3 at k={k}")
        wu_200 += len(base_b_digits(u200, B200))
        wu_200_bin += odd_part(ak).bit_length()
    obs_w200 = wu_200 / (N_w200 * N_w200)
    pred_w200 = math.log(4, B200) / 2.0
    obs_w200_bin = wu_200_bin / (N_w200 * N_w200)
    check(abs(obs_w200 - pred_w200) < 0.01, "Theorem 2.4 radix-200 width approaches log_200(4)/2")
    check(abs(obs_w200_bin - 1.0) < 0.03, "Theorem 2.4 binary odd-part width of 5*sqrt(2) approaches 1")

    print("[exact] Theorem 2.4: Kummer v_2(binom(2k,k)) = s_2(k) (k <= 400); exact series & gauge identities")
    print("        verified for all 5 binomial/Catalan/Pell series (including base-200 gauge & width):")
    print(f"        sqrt(2)  [8^-k]:   W_{{U,2}}(300)/300^2   = {r1[0]:.4f} (asymp 1/9    = {r1[1]:.4f}), log_2|delta_110|/110 = {r1[2]:.3f} (rho=0.667)")
    print(f"        sqrt(2)  [32^-k]:  W_{{U,2}}(300)/300^2   = {r2[0]:.4f} (asymp 1/25   = {r2[1]:.4f}), log_2|delta_110|/110 = {r2[2]:.3f} (rho=0.400)")
    print(f"        sqrt(3)  [16^-k]:  W_{{U,2}}(300)/300^2   = {r3[0]:.4f} (asymp 1/16   = {r3[1]:.4f}), log_2|delta_110|/110 = {r3[2]:.3f} (rho=0.500)")
    print(f"        phi      [16^-k]:  W_{{U,2}}(300)/300^2   = {r4[0]:.4f} (asymp 1/16   = {r4[1]:.4f}), log_2|delta_110|/110 = {r4[2]:.3f} (rho=0.500)")
    print(f"        5sqrt(2) [200^-k]: W_{{U,200}}(300)/300^2 = {obs_w200:.4f} (asymp {pred_w200:.4f}); W_{{U,2}}(300)/300^2 = {obs_w200_bin:.4f} (asymp 1.0000)")

    # Pell convergents p_r/q_r of sqrt(2): sign (-eps)^k check and tracking length vs ord_{q_r^odd}(2)
    p_p, q_p = 1, 1
    pell_rows = []
    for r in range(1, 19):
        eps = (-1) ** r
        check(p_p * p_p - 2 * q_p * q_p == eps, f"Pell identity p^2 - 2 q^2 = eps at r={r}")
        if r <= 6:
            # Verify q_r sqrt(2) = p_r sum_{k>=0} (-eps)^k binom(2k,k) (8 q_r^2)^{-k}
            approx_pell = Fr(p_p, q_p) * sum(Fr(((-eps) ** k) * math.comb(2 * k, k), (8 * q_p * q_p) ** k) for k in range(12))
            check(abs(approx_pell * approx_pell - 2) < Fr(1, (q_p * q_p) ** 6), f"Pell series sign (-eps)^k at r={r}")
        q_odd = odd_part(q_p)
        if q_odd > 1 and r <= 16:
            ord2 = mult_order(2, q_odd)
            track_bits = 2 * math.log2(q_p) + 1.5
            pell_rows.append((r, q_p, q_odd, ord2, track_bits))
        p_p, q_p = p_p + 2 * q_p, p_p + q_p
    print("[exact] Pell convergents p_r/q_r of sqrt(2): (-eps)^k series sign verified (r <= 6);")
    print("        real-distance precision ~ 2 log_2(q_r) bits vs ord_{q_odd}(2):")
    for (r, q_p, q_odd, ord2, tb) in pell_rows[-5:]:
        print(f"        r={r:2d}: q_r={q_p:9d}, q_odd={q_odd:9d}, real-dist~{tb:5.1f} bits, ord_2(q_odd)={ord2}")


# ========================================================================= E3
def section_E3():
    head("E3. Classical Lambert & E / E_+ Obstruction Map")

    # --- Theorem 3.1: Certified exact rational enclosures for mu_pop and mu_NAF ---
    P_LIM = 600
    PRIMES, _ = sieve_primes(P_LIM)
    ODD_P = [p for p in PRIMES if p > 2]

    # Exact distribution of U_odd = prod_{2 < p <= P_LIM} odd(B_p + 1) truncated at u <= U_CAP
    # Tracking exact missing probability rem_p and exact missing U-expectation rem_u_hi
    U_CAP = 512
    dist = {1: Fr(1)}
    rem_p = Fr(0)
    rem_u_hi = Fr(0)
    for p in ODD_P:
        K = 10 if p <= 29 else (6 if p <= 100 else 4)
        x = Fr(1, p)
        loc = {}
        u_sum = Fr(0)
        for e in range(K):
            pr = (1 - x) * (x ** e)
            o = odd_part(e + 1)
            loc[o] = loc.get(o, Fr(0)) + pr
            u_sum += pr * o
        p_tail = x ** K
        u_tail = (x ** K) * (K + Fr(p, p - 1))
        L_hi = u_sum + u_tail
        new_dist = {}
        new_rem_u = rem_u_hi * L_hi
        new_rem_p = rem_p + (1 - rem_p) * p_tail
        for u, pr in dist.items():
            new_rem_u += pr * u * u_tail
            for o, lpr in loc.items():
                uo = u * o
                if uo <= U_CAP:
                    new_dist[uo] = new_dist.get(uo, Fr(0)) + pr * lpr
                else:
                    new_rem_p += pr * lpr
                    new_rem_u += pr * lpr * uo
        dist = new_dist
        rem_p = new_rem_p
        rem_u_hi = new_rem_u

    # Rigorous tail bounds for primes p > P_LIM = 600:
    # 1. Convexity of x^-2 on length-2 intervals centered at odd integers gives sum_{p > 600} 1/p^2 < 1/(2*600).
    # 2. Telescoping sum 2/((m-2)m) = 1/(m-2) - 1/m over odd m >= 601 omitting composite 603 gives
    #    sum_{p > 600} 2/(p(p-1)) <= 1/599 - 2/(601*603) < 1/600.
    check(Fr(1, 599) - Fr(2, 601 * 603) < Fr(1, P_LIM), "Theorem 3.1(a) explicit prime-tail telescoping bound at P=600")
    # 3. Hence prod_{p > P_LIM} L_p <= exp(1/P_LIM) <= 1 + 2/P_LIM (since e^t <= 1 + 2t on [0, 1])
    #    and prod_{p > P_LIM} (1 - 1/p^2) >= 1 - 1/(2 P_LIM),
    #    so E[U_odd 1_{A_P^c}] <= E[U_odd^{(<=P)}] * (prod L_p - prod(1 - 1/p^2)) <= E_U_hi * 5/(2 P_LIM).
    E_U_lo = sum(u * pr for u, pr in dist.items())
    E_U_hi = E_U_lo + rem_u_hi
    tail_p_hi = Fr(1, 2 * P_LIM)
    tail_U_hi = E_U_hi * Fr(5, 2 * P_LIM)

    # Verify submultiplicativity s_2(uv) <= s_2(u) s_2(v) and w_2^pm(uv) <= w_2^pm(u) w_2^pm(v)
    for u in range(1, 60, 2):
        for v in range(1, 60, 2):
            check((u * v).bit_count() <= u.bit_count() * v.bit_count(), "s_2 submultiplicative")
            check(naf_weight(u * v) <= naf_weight(u) * naf_weight(v), "w_2^pm submultiplicative")

    def enclose_odd_scaled(fn, o2):
        """Rigorous [lo, hi] for E[fn(o2 * U_odd)], using fn(o2 * u) <= fn(o2) * u on the tail."""
        lo = sum(fn(u * o2) * pr for u, pr in dist.items()) * (1 - tail_p_hi)
        hi = sum(fn(u * o2) * pr for u, pr in dist.items()) + fn(o2) * (rem_u_hi + tail_U_hi)
        return lo, hi

    def enclose_2adic(fn, mode):
        K2 = 24
        lo_tot = Fr(0)
        hi_tot = Fr(0)
        E_U_full_hi = E_U_hi * (1 + Fr(2, P_LIM))
        if mode == "tau":
            for e in range(K2):
                pr2 = Fr(1, 1 << (e + 1))
                o2 = odd_part(e + 1)
                lo_e, hi_e = enclose_odd_scaled(fn, o2)
                lo_tot += pr2 * lo_e
                hi_tot += pr2 * hi_e
            # Tail e >= K2: fn(o2 * u) <= (e + 1) * u; sum_{e>=K2} (e+1) 2^{-(e+1)} = (K2 + 2) 2^{-K2}
            hi_tot += Fr(K2 + 2, 1 << K2) * E_U_full_hi
        elif mode == "ap":
            lo0, hi0 = enclose_odd_scaled(fn, 1)
            lo_tot += Fr(1, 2) * lo0
            hi_tot += Fr(1, 2) * hi0
            for e in range(2, K2):
                pr2 = Fr(1, 1 << (e + 1))
                o2 = odd_part(e - 1)
                lo_e, hi_e = enclose_odd_scaled(fn, o2)
                lo_tot += pr2 * lo_e
                hi_tot += pr2 * hi_e
            # Tail e >= K2: fn(o2 * u) <= (e - 1) * u; sum_{e>=K2} (e-1) 2^{-(e+1)} = K2 * 2^{-K2}
            hi_tot += Fr(K2, 1 << K2) * E_U_full_hi
        return lo_tot, hi_tot

    encl_pop_odd = enclose_odd_scaled(lambda u: u.bit_count(), 1)
    encl_pop_tau = enclose_2adic(lambda u: u.bit_count(), "tau")
    encl_pop_ap = enclose_2adic(lambda u: u.bit_count(), "ap")
    encl_naf_tau = enclose_2adic(naf_weight, "tau")
    encl_naf_ap = enclose_2adic(naf_weight, "ap")

    # Assert EVERY published outward-rounded interval against exact Fractions
    published_encl = [
        ("mu_pop(tau_odd)", encl_pop_odd, Fr(1159430, 10**6), Fr(1166471, 10**6), Fr(386476, 10**6), Fr(388824, 10**6)),
        ("mu_pop(tau)",     encl_pop_tau, Fr(1337765, 10**6), Fr(1346123, 10**6), Fr(445921, 10**6), Fr(448708, 10**6)),
        ("mu_pop(|a_+|)",   encl_pop_ap,  Fr(914156,  10**6), Fr(919767,  10**6), Fr(304718, 10**6), Fr(306589, 10**6)),
        ("mu_NAF(tau)",     encl_naf_tau, Fr(1315644, 10**6), Fr(1323936, 10**6), Fr(438548, 10**6), Fr(441312, 10**6)),
        ("mu_NAF(a_+)",     encl_naf_ap,  Fr(907252,  10**6), Fr(912845,  10**6), Fr(302417, 10**6), Fr(304282, 10**6)),
    ]
    print("[encl] Certified exact rational enclosures (P = 600, U_cap = 512, K2 = 24; outward-rounded):")
    for label, (lo, hi), pub_lo, pub_hi, pub_lo3, pub_hi3 in published_encl:
        check(pub_lo <= lo and hi <= pub_hi, f"Outward-rounded published interval for {label}")
        check(pub_lo3 <= lo / 3 and hi / 3 <= pub_hi3, f"Outward-rounded published /3 interval for {label}")
        print(f"       {label:16s} in [{fmt_floor(lo)}, {fmt_ceil(hi)}]   (/3 in [{fmt_floor(lo / 3)}, {fmt_ceil(hi / 3)}])")

    # Certify k >= 3 thresholds and published sufficient carry thresholds
    check(encl_pop_tau[1] / 3 < Fr(1, 2), "CERTIFIED: mu_pop(tau)/3 < 1/2 => E(2^k) simply nonnormal for k >= 3")
    check(encl_pop_odd[1] / 3 < Fr(1, 2), "CERTIFIED: mu_pop(tau_odd)/3 < 1/2 => E_odd(2^k) simply nonnormal for k >= 3")
    check(Fr(1, 2) - encl_pop_tau[1] / 3 >= Fr(5129, 10**5), "CERTIFIED: D^-(E(2^k); 2) >= 0.05129 for k >= 3")
    check(encl_pop_tau[1] / 2 <= Fr(673062, 10**6), "Published upper bound 0.673062 for E(4)")
    check(encl_pop_tau[1] / 2 - Fr(1, 2) <= Fr(173062, 10**6), "Published sufficient threshold 0.1731 for E(4)")
    check(encl_naf_ap[1] / 2 <= Fr(456423, 10**6), "Published upper bound 0.456423 for E_+(4)")
    check(encl_naf_ap[1] / 2 - Fr(1, 3) <= Fr(123090, 10**6), "Published sufficient threshold 0.1231 for E_+(4)")
    check(encl_pop_tau[1] - Fr(1, 2) <= Fr(846123, 10**6), "Published sufficient threshold 0.8462 for E(2)")
    check(encl_naf_ap[1] - Fr(1, 3) <= Fr(579512, 10**6), "Published sufficient threshold 0.579512 for E_+(2)")

    # All-prefix signed carry-buffer check for Theorem 3.1(c): H = ceil((2/k) log_2(N0 + 2)) + 4
    for k in range(1, 7):
        for N0 in range(1, 101):
            # Exact H = smallest integer >= (2/k) log_2(N0 + 2) + 4, i.e. 2^(k*(H-4)) >= (N0 + 2)^2
            t_min = 0
            while (1 << (k * t_min)) < (N0 + 2) ** 2:
                t_min += 1
            H = t_min + 4
            M = N0 + H
            check(H <= 2 * N0 + 7, f"Theorem 3.1(c) H <= 2*N0 + 7 at k={k}, N0={N0}")
            check((1 << (k * H)) >= 16 * (N0 + 2) ** 2, f"Theorem 3.1(c) 2^(kH) >= 16(N0+2)^2 at k={k}, N0={N0}")
            check(2 * (M + 2) * Fr(1, 1 << (k * H)) < Fr(1, 4), f"Theorem 3.1(c) omitted tail < 1/4 at k={k}, N0={N0}")

    # --- Theorem 3.2: Exact 4-state minimized NAF automaton & closed formula A_L ---
    # 3-state transducer from GF-32 Theorem 5.5
    states3 = (-1, 0, 1)
    trans3 = {b: {} for b in (0, 1)}
    for b in (0, 1):
        for d in states3:
            trans3[b][d] = []
            for dp in states3:
                a = b + 2 * d - dp
                if -1 <= a <= 1:
                    trans3[b][d].append((dp, 0 if a == 0 else 1))

    def step_dp_vec(vec, bit):
        nv = [10 ** 9, 10 ** 9, 10 ** 9]
        for i, d in enumerate(states3):
            for dp, cost in trans3[bit][d]:
                j = dp + 1
                if vec[i] + cost < nv[j]:
                    nv[j] = vec[i] + cost
        m = min(nv)
        return (nv[0] - m, nv[1] - m, nv[2] - m), m

    # Explicit BFS closure certifying the exact 7 reachable DP vectors and the 4-state lumping {A, B, C, D}
    reachable = {(0, 0, 0)}
    queue = [(0, 0, 0)]
    while queue:
        v = queue.pop()
        for b in (0, 1):
            nv, _ = step_dp_vec(v, b)
            if nv not in reachable:
                reachable.add(nv)
                queue.append(nv)
    lump_map = {
        (0, 0, 0): "A", (0, 0, 1): "A",
        (0, 1, 0): "B", (0, 1, 1): "B",
        (1, 0, 0): "C", (1, 0, 1): "C",
        (1, 1, 0): "D",
    }
    expected_table = {
        "A": {0: ("C", 0), 1: ("B", 0)},
        "B": {0: ("A", 1), 1: ("B", 0)},
        "C": {0: ("C", 0), 1: ("D", 0)},
        "D": {0: ("C", 1), 1: ("B", 1)},
    }
    check(reachable == set(lump_map.keys()) and len(reachable) == 7,
          "Theorem 3.2(a) exact 7 reachable normalized DP vectors")
    for vec, cls in lump_map.items():
        for b in (0, 1):
            nv, inc = step_dp_vec(vec, b)
            check((lump_map[nv], inc) == expected_table[cls][b],
                  f"Theorem 3.2(a) 4-state lumping transition at {vec} ({cls}) on bit {b}")
    # Certify minimality of {A, B, C, D}: immediate cost vectors (bit 0, bit 1) and suffix "11" costs
    imm = {cls: (expected_table[cls][0][1], expected_table[cls][1][1]) for cls in ("A", "B", "C", "D")}
    check(imm["B"] == (1, 0) and imm["D"] == (1, 1) and imm["A"] == (0, 0) and imm["C"] == (0, 0),
          "Theorem 3.2(a) immediate costs distinguish B and D")
    def word_cost(start_cls, bits):
        cls, tot = start_cls, 0
        for b in bits:
            cls, c = expected_table[cls][b]
            tot += c
        return tot
    check(word_cost("A", (1, 1)) == 0 and word_cost("C", (1, 1)) == 1,
          "Theorem 3.2(a) suffix '11' distinguishes A (cost 0) from C (cost 1)")

    # Finite cross-check: exact DP over normalized vectors from (0,0,0) for L = 1..20
    dist_v = {(0, 0, 0): 1}
    total_cost = Fr(0)
    AL_vals = {}
    for L in range(1, 21):
        new_dist = Counter()
        step_inc = 0
        for vec, cnt in dist_v.items():
            for b in (0, 1):
                nvec, m = step_dp_vec(vec, b)
                step_inc += m * cnt
                new_dist[nvec] += cnt
        dist_v = new_dist
        total_cost += Fr(step_inc, 1 << L)
        AL = total_cost / L
        AL_closed = Fr(1, 3) - (Fr(7) - Fr(-1, 2) ** (L - 1)) / (18 * L)
        check(AL == AL_closed, f"Theorem 3.2 closed formula A_L finite cross-check at L={L}")
        AL_vals[L] = AL

    # Finite cross-check by brute force over all 2^L words for L <= 10
    for L in range(1, 11):
        brute_sum = 0
        for mask in range(1 << L):
            v = [0, 0, 0]
            for pos in range(L - 1, -1, -1):
                b = (mask >> pos) & 1
                nv = [10 ** 9, 10 ** 9, 10 ** 9]
                for i, d in enumerate(states3):
                    for dp, cost in trans3[b][d]:
                        j = dp + 1
                        if v[i] + cost < nv[j]:
                            nv[j] = v[i] + cost
                v = nv
            brute_sum += min(v)
        check(Fr(brute_sum, L * (1 << L)) == AL_vals[L], f"Theorem 3.2 brute-force cross-check L={L}")

    # Certify E_+(8) nonnormality and explicit D^-(E_+(8); 2) >= 2.34e-7 > 0 via L = 16!
    L_cert = 16
    A16 = AL_vals[L_cert]
    mu_naf_ap_hi = encl_naf_ap[1]
    check(mu_naf_ap_hi / 3 < A16, "CERTIFIED: mu_NAF(a_+)/3 < A_16 => E_+(2^k) nonnormal for k >= 3")
    D_minus_Eplus8 = (A16 - mu_naf_ap_hi / 3) / ((1 << L_cert) * A16)
    check(D_minus_Eplus8 >= Fr(234, 10**9), "CERTIFIED: D^-(E_+(8); 2) >= 2.34e-7 > 0")
    print(f"[exact] Theorem 3.2: full 7-vector BFS closure, 4-state lumping table & minimality certified")
    print(f"        (proving A_L = 1/3 - (7 - (-1/2)^(L-1))/(18L) for all L >= 1; finite cross-checks: DP L<=20, brute-force L<=10)")
    print(f"[encl]  CERTIFIED: mu_NAF(a_+)/3 <= {fmt_ceil(mu_naf_ap_hi / 3)} < A_16 = {A16} (> {fmt_floor(A16)}),")
    print(f"        giving explicit D^-(E_+(8); 2) >= {fmt_floor(D_minus_Eplus8, 9)} (>= 2.34e-7 > 0; nonnormal for all k >= 3)")

    # --- Theorem 3.3: Exact 3-term / 4-term reduction of C_+(h; X) eliminating (H2) ---
    X_DIV = 65536
    tau = [0] * (X_DIV + 100)
    for d in range(1, X_DIV + 100):
        for m in range(d, X_DIV + 100, d):
            tau[m] += 1
    ap = [0] * (X_DIV + 100)
    for n in range(1, X_DIV + 100):
        e = v2(n)
        ap[n] = (1 - e) * (tau[n] // (e + 1))

    # Check exact identities for ALL 1 <= h <= 32 at both odd and even X (999, 1000, 10001, 65536)
    red_cnt = 0
    for Xc in (999, 1000, 10001, X_DIV):
        for h in range(1, 33):
            lhs = sum(ap[n] * ap[n + h] for n in range(1, Xc + 1))
            if h % 2 == 1:
                t1 = sum(tau[n] * tau[n + h] for n in range(1, Xc + 1))
                t2 = sum(tau[m] * tau[2 * m + h] for m in range(1, Xc // 2 + 1))
                t3 = sum(tau[2 * m - h] * tau[m] for m in range((h + 1) // 2, (Xc + h) // 2 + 1))
                rhs = t1 - 2 * t2 - 2 * t3
                check(lhs == rhs, f"Theorem 3.3 exact odd-h reduction at X={Xc}, h={h}")
            else:
                hp = h // 2
                t1 = sum(tau[n] * tau[n + h] for n in range(1, Xc + 1))
                t2 = sum(tau[m] * tau[2 * m + h] for m in range(1, Xc // 2 + 1))
                t3 = sum(tau[2 * m] * tau[m + hp] for m in range(1, Xc // 2 + 1))
                t4 = sum(tau[m] * tau[m + hp] for m in range(1, Xc // 2 + 1))
                rhs = t1 - 2 * t2 - 2 * t3 + 4 * t4
                check(lhs == rhs, f"Theorem 3.3 exact even-h reduction at X={Xc}, h={h}")
            red_cnt += 1

    # Check exact 2-adic algebraic cancellation reproducing (1/4)(2 - 3 * 2^-k) for k = 0..20
    for k in range(0, 21):
        target = Fr(1, 4) * (2 - Fr(3, 1 << k))
        if k == 0:
            val = Fr(3, 4) - 2 * Fr(1, 4) - 2 * Fr(1, 4)
        else:
            t1 = Fr(1, 4) * (6 - Fr(3, 1 << k))
            t23 = -4 * (Fr(1, 8) * (8 - Fr(6, 1 << k)))
            t4 = 4 * Fr(1, 2) * Fr(1, 4) * (6 - Fr(3, 1 << (k - 1)))
            val = t1 + t23 + t4
        check(val == target, f"Theorem 3.3 2-adic algebraic collapse at k={k}")
    print(f"[exact] Theorem 3.3: exact 3-term (odd h) and 4-term (even h, all X) reductions of sum a_+(n)a_+(n+h)")
    print(f"        verified with zero error on {red_cnt} pairs (1 <= h <= 32, odd/even X up to {X_DIV}) and 2-adic collapse (k <= 20)")

    # --- Exact independent column carry-balance checks & obstruction-map diagnostics ---
    M_DIAG = 6000
    GUARD_DIGS = 40
    print(f"[exact] Theorem 3.1(b) independent column carry-balance verification (M = {M_DIAG});")
    print(f"[finite] Obstruction-map digit/NAF measurements (M = {M_DIAG}, {GUARD_DIGS}-base-digit guard; finite data only):")
    print("        series      k  f1_bin   c_bar_bin  sum_s2/(kM)  naf/N    c_bar_NAF  sum_naf/(kM)  status")
    tau_odd_arr = [0] + [tau[n] // (v2(n) + 1) for n in range(1, M_DIAG + 1)]
    base4_stats = {}
    for name, seq, signed in [("E(2^k)", tau, False), ("E_odd(2^k)", tau_odd_arr, False), ("E_+(2^k)", ap, True)]:
        for k in (1, 2, 3, 4):
            b = 1 << k
            S = 0
            sum_s2 = 0
            sum_naf = 0
            for n in range(1, M_DIAG + 1):
                S = S * b + seq[n]
                sum_s2 += abs(seq[n]).bit_count()
                sum_naf += naf_weight(seq[n])
            if not signed:
                # Independent column-by-column binary carry count verifying Kummer's balance identity
                cols = [0] * (k * M_DIAG + 64)
                for n in range(1, M_DIAG + 1):
                    val_n = seq[n]
                    base_pos = k * (M_DIAG - n)
                    bit = 0
                    while val_n:
                        if val_n & 1:
                            cols[base_pos + bit] += 1
                        val_n >>= 1
                        bit += 1
                C_bin = 0
                c_in = 0
                s2_rec = 0
                for col in cols:
                    tot = col + c_in
                    s2_rec += tot & 1
                    c_out = tot >> 1
                    C_bin += c_out
                    c_in = c_out
                while c_in:
                    s2_rec += c_in & 1
                    c_out = c_in >> 1
                    C_bin += c_out
                    c_in = c_out
                check(s2_rec == S.bit_count(), "Independent column normalization matches s_2(S)")
                check(C_bin >= 0, "Theorem 3.1 C_bin >= 0 for nonnegative series")
                check(S.bit_count() + C_bin == sum_s2, "Theorem 3.1 independent column verification of carry balance")
            else:
                C_bin = 0
            C_naf = sum_naf - naf_weight(S)
            check(C_naf >= 0, "Theorem 3.1 C_NAF >= 0 (subadditivity of w_2^pm)")
            # Fractional digits (strip integer part and bottom GUARD_DIGS*k guard bits)
            F = S % (b ** M_DIAG)
            guard_bits = GUARD_DIGS * k
            guard_rem = F & ((1 << guard_bits) - 1)
            # Rigorous omitted tail bound in units of 2^(-k*M_DIAG): sum_{j>=1} 2(M+j) b^{-j} <= 2*(M+2)
            tail_max = 2 * (M_DIAG + 2)
            check(tail_max < guard_rem < (1 << guard_bits) - tail_max,
                  f"Guard remainder isolates retained digits from omitted tail ({name}, k={k})")
            val = F >> guard_bits
            nbits = (M_DIAG - GUARD_DIGS) * k
            f1 = val.bit_count() / nbits
            naf_d = naf_weight(val) / nbits
            status = "PROVED" if k >= 3 else "OPEN"
            cbin_str = f"{C_bin/(k*M_DIAG):8.4f}" if not signed else "   (n/a)"
            print(f"        {name:10s}  {k}  {f1:.4f}  {cbin_str}    {sum_s2/(k*M_DIAG):.4f}     {naf_d:.4f}    {C_naf/(k*M_DIAG):.4f}     {sum_naf/(k*M_DIAG):.4f}      {status}")
            if k == 2 and name in ("E(2^k)", "E_+(2^k)"):
                ndigs4 = M_DIAG - GUARD_DIGS
                cnt4 = [0, 0, 0, 0]
                tmp = val
                for _ in range(ndigs4):
                    cnt4[tmp & 3] += 1
                    tmp >>= 2
                base4_stats[name] = tuple(c / ndigs4 for c in cnt4)
    e4_f = base4_stats["E(2^k)"]
    ep4_f = base4_stats["E_+(2^k)"]
    print(f"[finite] Base-4 digit frequencies (M = {M_DIAG}, {M_DIAG - GUARD_DIGS} certified retained base-4 digits):")
    print(f"         E(4):   ({e4_f[0]:.5f}, {e4_f[1]:.5f}, {e4_f[2]:.5f}, {e4_f[3]:.5f})")
    print(f"         E_+(4): ({ep4_f[0]:.5f}, {ep4_f[1]:.5f}, {ep4_f[2]:.5f}, {ep4_f[3]:.5f})  [digit 0 = {ep4_f[0]:.5f}]")


def main():
    for fn in (section_E1, section_E2, section_E3):
        t0 = time.time()
        fn()
        print(f"  ({fn.__name__}: {time.time() - t0:.1f} s)")
    print(f"\nALL CHECKS PASSED ({CHECKS[0]} assertions) in {time.time() - T0:.1f} s")


if __name__ == "__main__":
    main()
