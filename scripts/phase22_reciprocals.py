#!/usr/bin/env python3
"""Exact algebraic checks and finite-scale measurements for Phase 22 Track D.

Sections:
  1. Exact period identity T_k = m_k * D_{k-1} across bases b = 2..10 (including
     b = 2, m_1 = 1 and b == 3 mod 4 with odd m_1, m_2), full Hull-Dobell order
     lifting and S_i(b^m) mod D bijectivity, and 2-adic sharpness counterexamples.
  2. Exact partial-band inequality (constant 3 -> 1), divisor-sum bound for
     sum_{h<=H} gcd(h, D)/h, Phase 21 vs Phase 22 Erdos-Turan comparison (both
     Phase 21's D_3 and the balanced D_3), exact shifted-grid discrepancy and
     circular W_1 bounds, partial-band Weyl-sum and Koksma lower-bound checks
     on b = 2, m = (2, 4, 48, 43200), and balanced log-tower heights.
  3. Exact signed period identity T_k(eps) = 2*m_k (eps_k = +1) vs m_k*D_{k-1}(eps)
     (eps_k = -1) across bases b = 2..10 and all sign triples, plus general
     plus-sign lifting ord_{D(b^m + 1)}(b) = 2*m.
  4. Finite-scale orbit measurements for y(eps): pure +1 with m_k = 2^k * k!
     (non-tetration), r-runs of +1 after a -1 reset (D -> 1 - 2^{-r}, oriented
     digit frequencies), continuous sweep across [m_K, 2*m_K], and finite-scale
     illustration of the -1 melting transition.
  5. Closed-form band theorem for P_k(q) = ((1+q^{2k+1})/(1+q))*((1+q^{2k+3})/(1+q))
     for k = 1..25 (including exact tail identity tau_{L-d}(q) = q^d / P_k(q)),
     generalized band identity and T_j | L_j*m_j across bases 2, 3, 5, 10,
     concrete 0+/1- sign mixing in base 2, and consecutive-k prescribed-alpha
     approximation.

Standard library only. Orbit values use 40-bit (48-bit in Section 2) truncations
of exact rational expansions; they are finite-scale measurements, not interval
certificates.

Run from the repository root:  python -B scripts/phase22_reciprocals.py
"""

from __future__ import annotations

import cmath
import math
from fractions import Fraction
from math import gcd
from time import perf_counter

SECTION_CHECKS: dict[str, int] = {}
CURRENT_SECTION = ["init"]


def set_section(name: str) -> None:
    CURRENT_SECTION[0] = name
    SECTION_CHECKS.setdefault(name, 0)


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit("FAIL: " + msg)
    sec = CURRENT_SECTION[0]
    SECTION_CHECKS[sec] = SECTION_CHECKS.get(sec, 0) + 1


def header(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------- arithmetic helpers


def factorize(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def rad_star(n: int) -> int:
    """Hull-Dobell radical: product of distinct prime factors of n, times 2 if 4 | n."""
    r = 1
    for p in factorize(n):
        r *= p
    if n % 4 == 0:
        r *= 2
    return r


def order_mod(b: int, d: int, multiple: int | None = None) -> int:
    """Exact multiplicative order of b modulo d (gcd(b, d) = 1)."""
    if d == 1:
        return 1
    check(gcd(b, d) == 1, f"gcd({b}, {d}) != 1")
    if multiple is None:
        x, k = b % d, 1
        while x != 1:
            x = (x * b) % d
            k += 1
        return k
    check(pow(b, multiple, d) == 1, f"b^{multiple} != 1 mod {d}")
    order = multiple
    for p in factorize(multiple):
        while order % p == 0 and pow(b, order // p, d) == 1:
            order //= p
    return order


def tau(n: int) -> int:
    t = 1
    for e in factorize(n).values():
        t *= e + 1
    return t


def divisors(n: int) -> list[int]:
    divs = [1]
    for p, e in factorize(n).items():
        divs = [d * (p ** k) for d in divs for k in range(e + 1)]
    return sorted(divs)


def discrepancy(values: list[float]) -> float:
    """Exact extreme interval discrepancy of a finite point set in [0, 1)."""
    ordered = sorted(values)
    n = len(ordered)
    high = 0.0
    low = 0.0
    for i, y in enumerate(ordered):
        u = (i + 1) / n - y
        if u > high:
            high = u
        l = i / n - y
        if l < low:
            low = l
    return high - low


def orbit_from_fraction_fast(
    R: Fraction, b: int, N: int, W: int = 40
) -> tuple[list[float], list[int]]:
    """Compute first N orbit points {b^n R} truncated to b^{-W} and exact first digits."""
    if b == 2:
        total = N + W + 1
        V = ((R.numerator % R.denominator) << total) // R.denominator
        bits = bin(V)[2:].zfill(total)
        mask = (1 << W) - 1
        w = int(bits[:W], 2)
        scale = float(1 << W)
        xs = [0.0] * N
        digs = [0] * N
        for n in range(N):
            xs[n] = w / scale
            digs[n] = 1 if bits[n] == "1" else 0
            w = ((w << 1) & mask) | (1 if bits[n + W] == "1" else 0)
        return xs, digs

    den = R.denominator
    num = R.numerator % den
    xs = [0.0] * N
    digs = [0] * N
    if den.bit_length() <= 3000:
        inv = 1.0 / den if den < (1 << 1000) else None
        shift = den.bit_length() - 53 if inv is None else 0
        den_hi = (den >> shift) if inv is None else 1
        for n in range(N):
            xs[n] = (num * inv) if inv is not None else ((num >> shift) / den_hi)
            d, num = divmod(num * b, den)
            digs[n] = d
        return xs, digs

    scale_pow = b ** (N + W)
    rem = (num * scale_pow) // den
    raw = [0] * (N + W)
    for idx in range(N + W - 1, -1, -1):
        rem, raw[idx] = divmod(rem, b)
    pow_w = b ** W
    top_place = pow_w // b
    inv_pow = 1.0 / pow_w
    acc = 0
    for j in range(W):
        acc = acc * b + raw[j]
    for n in range(N):
        xs[n] = acc * inv_pow
        digs[n] = raw[n]
        acc = (acc - raw[n] * top_place) * b + raw[n + W]
    return xs, digs


def wasserstein1_empirical_to_lambda(xs: list[float]) -> float:
    """Exact circular W_1 distance on R/Z between the empirical measure of xs and
    Lebesgue measure: inf_{c in R} int_0^1 |F_n(t) - t - c| dt."""
    ordered = sorted(xs)
    n = len(ordered)
    segs: list[tuple[float, float, float]] = []
    prev = 0.0
    for i, x in enumerate(ordered):
        if x > prev:
            segs.append((x - prev, i / n - prev, i / n - x))
        prev = x
    if prev < 1.0:
        segs.append((1.0 - prev, 1.0 - prev, 0.0))

    def eval_cost(c: float) -> float:
        total = 0.0
        for length, u0, u1 in segs:
            a, b_val = u0 - c, u1 - c
            if a >= 0.0 and b_val >= 0.0:
                total += 0.5 * (a + b_val) * length
            elif a <= 0.0 and b_val <= 0.0:
                total += -0.5 * (a + b_val) * length
            else:
                total += 0.5 * (a * a + b_val * b_val)
        return total

    lo = min(u1 for _, _, u1 in segs)
    hi = max(u0 for _, u0, _ in segs)
    for _ in range(50):
        mid = 0.5 * (lo + hi)
        meas_gt = 0.0
        for length, u0, u1 in segs:
            if u1 >= mid:
                meas_gt += length
            elif u0 > mid:
                meas_gt += u0 - mid
        if meas_gt > 0.5:
            lo = mid
        else:
            hi = mid
    return eval_cost(0.5 * (lo + hi))


# ---------------------------------------------------------------- Section 1: Exact periods (minus)


def section_exact_period_minus() -> None:
    set_section("1. Exact periods (minus) & Hull-Dobell")
    header("1. Exact period identity T_k = m_k * D_{k-1} & Hull-Dobell lifting")

    cases = [
        (2, [1, 2, 6]),
        (2, [2, 4, 48]),
        (2, [3, 6, 42]),
        (3, [1, 3, 18]),     # b == 3 mod 4, odd m_1 and m_2
        (3, [1, 1, 2]),      # repeated m in the algebraic lemma
        (3, [2, 4, 32]),
        (4, [1, 2, 6]),
        (5, [1, 2, 8]),
        (6, [1, 2, 10]),
        (7, [1, 3, 18]),     # b == 3 mod 4, odd m_1 and m_2
        (7, [2, 4, 192]),
        (8, [1, 2, 14]),
        (9, [1, 2, 16]),
        (10, [1, 2, 18]),
        (10, [2, 4, 396]),
    ]
    print("  Testing T_k = m_k * D_{k-1} across bases b = 2..10 (including b=2,m1=1 & b=3 mod 4 odd m):")
    for b, ms in cases:
        D_prev = 1
        T_prev = 1
        row_T = []
        for k, m in enumerate(ms, 1):
            check(m % T_prev == 0, f"admissibility failed b={b} k={k}")
            D_k = D_prev * (b ** m - 1)
            expected = m * D_prev
            T_k = order_mod(b, D_k, expected)
            check(T_k == expected, f"T_k mismatch for b={b}, ms={ms}, k={k}: got {T_k}, expected {expected}")
            row_T.append(T_k)
            D_prev = D_k
            T_prev = T_k
        print(f"    b={b:2d}, m={str(ms):14s} -> T={row_T}  (exact m_k*D_{{k-1}}: ok)")

    # Exhaustive check of Hull-Dobell lifting for 2 <= b <= 10, 1 <= m <= 6, 1 <= D <= 100:
    hd_count = 0
    strict_hd_count = 0
    v2_fail_examples = []
    for b in range(2, 11):
        for m in range(1, 7):
            q = b ** m
            qm1 = q - 1
            for D in range(1, 101):
                if gcd(b, D) != 1:
                    continue
                if qm1 % rad_star(D) == 0:
                    hd_count += 1
                    if qm1 % D != 0:
                        strict_hd_count += 1
                    T = order_mod(b, D * qm1, m * D)
                    check(T == m * D, f"Hull-Dobell lifting failed: b={b}, m={m}, D={D}")
                    seen = set()
                    s = 0
                    p_q = 1
                    for _ in range(D):
                        s = (s + p_q) % D
                        seen.add(s)
                        p_q = (p_q * q) % D
                    check(len(seen) == D, f"S_i not bijective for b={b}, m={m}, D={D}")
                elif D % 4 == 0 and qm1 % 2 == 0 and qm1 % 4 != 0 and qm1 % (rad_star(D) // 2) == 0:
                    T = order_mod(b, D * qm1, m * D)
                    check(T < m * D, f"expected T < m*D when 4|D and q=3 mod 4: b={b}, m={m}, D={D}")
                    if len(v2_fail_examples) < 3:
                        v2_fail_examples.append((b, m, D, T, m * D))
    print(f"  Hull-Dobell lifting verified for {hd_count} triples (b, m, D) "
          f"({strict_hd_count} with D not dividing b^m - 1): all T = m*D and S_i bijective!")
    check(len(v2_fail_examples) >= 1, "expected counterexample when 4 | D and v_2(b^m-1) = 1")
    print(f"  2-adic sharpness counterexamples (4|D, b^m = 3 mod 4): {v2_fail_examples[:2]}")


# ---------------------------------------------------------------- Section 2: Sharpened bounds


def section_improved_rates() -> None:
    set_section("2. Weyl, divisor-sum, grid & Koksma")
    header("2. Sharpened Weyl/divisor-sum bounds, exact grid bound & Koksma lower bound")

    # 2a. Exact partial-band inequality (Lemma 2.1):
    pb_checks = 0
    for dp in range(1, 25):
        for I in range(1, 40):
            for m in (1, 2, 7, 20):
                for r0 in (0, 1, m // 2, m - 1):
                    if r0 >= m:
                        continue
                    lhs = m * (I // dp) + (r0 if (I + 1) % dp == 0 else 0)
                    N = I * m + r0
                    check(lhs * dp <= N, f"partial-band inequality failed dp={dp}, I={I}, m={m}, r0={r0}")
                    pb_checks += 1
    print(f"  Sharpened partial-band inequality (constant 3 -> 1) verified on {pb_checks} tuples: ok")

    # 2b. Exact divisor-sum bound (Lemma 2.2):
    harm = [0.0] * 5005
    for n in range(1, len(harm)):
        harm[n] = harm[n - 1] + 1.0 / n
    test_Ds = [1, 3, 12, 45, 60, 120, 360, 720, 2520, 4095, 5040]
    for D in test_Ds:
        divs = divisors(D)
        tD = len(divs)
        for H in (10, 50, 200, min(D, 2000), 2000):
            exact = sum(gcd(h, D) / h for h in range(1, H + 1))
            sharp_div = sum(harm[H // d] for d in divs if d <= H)
            tau_le_H = sum(1 for d in divs if d <= H)
            bound_log = tau_le_H * (1.0 + math.log(H))
            bound_tau = tD * (1.0 + math.log(H))
            check(exact <= sharp_div + 1e-12, f"exact <= sharp_div failed D={D}, H={H}")
            check(sharp_div <= bound_log + 1e-12, f"sharp_div <= bound_log failed D={D}, H={H}")
            check(bound_log <= bound_tau + 1e-12, f"bound_log <= bound_tau failed D={D}, H={H}")
    print(f"  Divisor-sum bound sum_{{h<=H}} gcd(h,D)/h <= sum_{{d|D, d<=H}} H_{{floor(H/d)}} "
          f"<= tau(D)(1 + log H) verified on {len(test_Ds)} moduli: ok")

    # 2c. Quantitative comparison of main (D_{K-2} and omega_{K-1}) Erdos-Turan terms
    #     at omega_{K-1} = D_{K-2} (omitting the smaller c_b(H)/m_K term):
    D3_bal = 45 * (2**36 - 1)   # balanced sequence from (2, 4): m_3 = 36
    D3_p21 = 45 * (2**48 - 1)   # Phase 21 sequence (2, 4, 48, 43200)
    print()
    print("  Comparison of main D_{K-2} + omega_{K-1} Erdos-Turan terms at omega_{K-1} = D_{K-2}")
    print("  (omitting the c_b(H)/m_K term):")
    print(f"    {'label':>14} {'D_{K-2}':>18} {'tau(D)':>7} {'Phase21 (sqrt D)':>18} {'Phase22 (H=D)':>18} {'ratio':>9}")
    for label, D in [
        ("D_2 (2,4)", 45),
        ("2^12 - 1", 4095),
        ("10^6", 10**6),
        ("D_3 bal m3=36", D3_bal),
        ("D_3 P21 m3=48", D3_p21),
    ]:
        tD = tau(D)
        H21 = int(math.isqrt(D))
        b21 = 6.0 / (H21 + 1) + 12.0 / (math.pi * math.sqrt(D)) + (4.0 / math.pi) * (1.0 + math.log(H21)) / D
        H22 = D
        b22 = 6.0 / (H22 + 1) + (4.0 / math.pi) * (tD + 1.0) * (1.0 + math.log(H22)) / D
        check(b22 < b21, f"Phase 22 bound should beat Phase 21 at D={D}")
        print(f"    {label:>14} {D:18d} {tD:7d} {b21:18.4e} {b22:18.4e} {b21/b22:8.1f}x")

    # 2d. Exact complete-period discrepancy D(mu_K) <= 1 / D_{K-1} and circular W_1 <= 1 / (4*D_{K-1}):
    print()
    print("  Exact complete-period discrepancy D(mu_K) <= 1/D_{K-1} and W_1(mu_K, lambda) <= 1/(4*D_{K-1}):")
    for b, ms in [(2, [2, 4, 48]), (3, [2, 4]), (5, [1, 2])]:
        R = Fraction(1)
        D_prev = 1
        for k, m in enumerate(ms, 1):
            R *= Fraction(b ** m, b ** m - 1)
            D = R.denominator
            T = m * D_prev
            if T <= 5000:
                A = R.numerator % D
                x = A
                pts = []
                for _ in range(T):
                    pts.append(x / D)
                    x = (x * b) % D
                dm = discrepancy(pts)
                w1 = wasserstein1_empirical_to_lambda(pts)
                check(dm <= 1.0 / D_prev + 1e-12, f"D(mu_K) > 1/D_{{K-1}} for b={b}, k={k}")
                check(w1 <= 1.0 / (4 * D_prev) + 1e-9, f"W_1(mu_K, lambda) > 1/(4*D_{{K-1}}) for b={b}, k={k}")
                print(f"    b={b}, k={k}, m_k={m:2d}, D_{{k-1}}={D_prev:3d}, T_k={T:4d}: "
                      f"D(mu_k)={dm:.6f} <= {1/D_prev:.6f},  W1={w1:.6f} <= {1/(4*D_prev):.6f}")
            D_prev = D

    # 2e. Sharpened Weyl bound (Theorem 2(1)) on BOTH complete-band and partial-band prefixes
    #     plus Koksma lower bound on b = 2, m = (2, 4, 48, 43200):
    R3 = Fraction(4, 3) * Fraction(16, 15) * Fraction(2**48, 2**48 - 1)
    R4 = R3 * Fraction(2**43200, 2**43200 - 1)
    D2 = 45
    T3 = 2160
    m4 = 43200
    prefixes = [m4, m4 + 7 * T3, 2 * m4 - 1, 3 * m4 - 1, 3 * m4, (7 * m4) // 2, 4 * m4 - 1]
    Nmax = max(prefixes)
    xs4, _ = orbit_from_fraction_fast(R4, 2, Nmax, W=48)
    hs = (1, 2, 3, 5, 9, 15, 45)

    # Precompute cumulative exponential sums up to Nmax:
    cums: dict[int, list[complex]] = {}
    for h in hs:
        acc = 0j
        arr = [0j] * Nmax
        tw = 2j * math.pi * h
        for n in range(Nmax):
            acc += cmath.exp(tw * xs4[n])
            arr[n] = acc
        cums[h] = arr

    worst_ratio = 0.0
    worst_info = (0, 0, 0.0, 0.0, 0.0)
    print()
    print("  Partial-band Weyl check (Theorem 2(1)) on b=2, m=(2,4,48,43200), D_2=45, T_3=2160:")
    for N in prefixes:
        DN = discrepancy(xs4[:N])
        for h in hs:
            Wh = abs(cums[h][N - 1]) / N
            c2h = 2.0 * math.log2(64.0 * math.pi * h) + 8.0
            b_p22 = gcd(h, D2) / D2 + (T3 + 3.0 * c2h) / m4
            b_p21 = 3.0 * gcd(h, D2) / D2 + (T3 + 3.0 * c2h) / m4
            check(Wh <= b_p22 + 1e-9, f"sharpened Weyl bound failed at N={N}, h={h}")
            check(Wh <= math.pi * h * DN + 1e-9, f"Koksma failed at N={N}, h={h}")
            if h < D2:
                ratio = Wh / b_p22
                if ratio > worst_ratio:
                    worst_ratio = ratio
                    worst_info = (N, h, Wh, b_p22, b_p21)
    N_w, h_w, Wh_w, b22_w, b21_w = worst_info
    W45_m4 = abs(cums[45][m4 - 1]) / m4
    DN_m4 = discrepancy(xs4[:m4])
    koksma_lb = W45_m4 / (math.pi * D2)
    check(W45_m4 > 0.85, f"expected |W_45(m_4)| > 0.85, got {W45_m4}")
    check(DN_m4 >= koksma_lb - 1e-12, "Koksma inequality failed at m_4")
    # Highlight h=15, N=3*m_4-1 where constant 1 is tight and Phase 21 constant 3 is trivial (>1):
    W15_3m = abs(cums[15][3 * m4 - 2]) / (3 * m4 - 1)
    c2_15 = 2.0 * math.log2(64.0 * math.pi * 15) + 8.0
    b22_15 = gcd(15, D2) / D2 + (T3 + 3.0 * c2_15) / m4
    b21_15 = 3.0 * gcd(15, D2) / D2 + (T3 + 3.0 * c2_15) / m4
    check(W15_3m <= b22_15 < 0.40 and b21_15 > 1.0, "expected nontrivial constant-1 bound at h=15, N=3*m4-1")
    print(f"    7 prefixes x 7 frequencies: max ratio |W_h|/bound (h<45) = {worst_ratio:.4f} "
          f"at N={N_w}, h={h_w} (|W|={Wh_w:.4f}, new={b22_w:.4f}, P21={b21_w:.4f})")
    print(f"    At N=3*m_4-1={3*m4-1}, h=15: |W_15|={W15_3m:.4f} <= new bound {b22_15:.4f} (P21={b21_15:.4f})")
    print(f"    At N=m_4={m4}: |W_45(m_4)|={W45_m4:.5f}, Koksma LB={koksma_lb:.5f} <= D_{{m_4}}={DN_m4:.5f}: ok")

    # 2f. Balanced log-tower audit for omega_k = D_{k-1} (m_{k+1} = m_k * D_{k-1}^2) in base 2:
    lm = [0.0, math.log2(2), math.log2(4)]
    lD = [0.0, math.log2(3), math.log2(45)]
    for k in range(3, 8):
        lm_k = lm[k - 1] + 2.0 * lD[k - 2]
        lm.append(lm_k)
        lD_k = lD[k - 1] + (2.0 ** lm_k if lm_k < 500 else float("inf"))
        lD.append(lD_k)
    ratio_K6 = lD[4] / math.log2(lm[7])
    check(ratio_K6 > 700.0, f"expected log2(D_4)/log2(log2(m_7)) > 700, got {ratio_K6}")
    print(f"  Balanced omega_k = D_{{k-1}} (b=2): at K=6, log2(D_4)={lD[4]:.1f}, "
          f"log2(log2(m_7))={math.log2(lm[7]):.2f} (ratio {ratio_K6:.1f}): ok")


# ---------------------------------------------------------------- Section 3: Exact signed periods


def section_signed_periods() -> None:
    set_section("3. Signed periods")
    header("3. Exact signed period identity T_k(eps) = 2*m_k (+1) vs m_k*D_{k-1} (-1)")

    total_triples = 0
    for b in range(2, 11):
        for mask in range(8):
            eps = [1 if (mask >> j) & 1 else -1 for j in range(3)]
            D = 1
            T = 1
            m = 1 if (b >= 3 or eps[0] == 1) else 2
            for k in range(3):
                if k == 0:
                    mk = m
                else:
                    mk = T if (k == 1 and T > m) else 2 * T
                    if b >= 5 and mk > 24:
                        mk = T
                check(mk % T == 0, "sign-admissibility T_{k-1} | m_k")
                fac = b ** mk + eps[k]
                check(gcd(b, fac) == 1, "gcd(b, b^m + eps) = 1")
                D_new = D * fac
                expected = (2 * mk) if eps[k] == 1 else (mk * D)
                T_new = order_mod(b, D_new, expected)
                check(T_new == expected,
                      f"signed period mismatch b={b} eps={eps} k={k+1}: got {T_new}, expected {expected}")
                D, T, m = D_new, T_new, mk
            total_triples += 1

    # Edge case b = 2, m_1 = 1 with both signs:
    for eps in ([-1, 1, -1], [-1, 1, 1], [1, -1, 1], [1, 1, 1]):
        D, T = 1, 1
        for k in range(3):
            mk = 1 if k == 0 else (2 * T if T <= 12 else T)
            D_new = D * (2 ** mk + eps[k])
            expected = (2 * mk) if eps[k] == 1 else (mk * D)
            T_new = order_mod(2, D_new, expected)
            check(T_new == expected, f"b=2, m1=1 edge case failed eps={eps} k={k+1}")
            D, T = D_new, T_new

    plus_lift = 0
    for b in range(2, 11):
        for m in range(1, 7):
            qm1 = b ** m - 1
            qp1 = b ** m + 1
            for D in divisors(qm1):
                if D > 200:
                    continue
                T = order_mod(b, D * qp1, 2 * m)
                check(T == 2 * m, f"plus-sign lifting failed b={b}, m={m}, D={D}")
                plus_lift += 1
    print(f"  Verified T_k(eps) across 9 bases (b=2..10) x 8 sign triples ({total_triples} runs) "
          f"+ 4 edge runs (b=2,m1=1): ok")
    print(f"  General plus-sign lifting ord_{{D(b^m+1)}}(b) = 2*m verified on {plus_lift} triples (b,m,D): ok")


# ---------------------------------------------------------------- Section 4: Sign regimes & digits


def section_classification_and_digits() -> None:
    set_section("4. Sign trajectories & digits")
    header("4. Measure recursion, discrepancy trajectories, melting & oriented digits")

    # 4a. Pure +1 product with non-tetration sequence m_k = 2^k * k! (2*m_k | m_{k+1}, ratio k+1):
    #     b=2: m = (2, 8, 48, 384, 3840); b=3: m = (2, 8, 48, 384).
    print("  [4a] Pure +1 product y(+1,+1,...) with m_k = 2^k * k! (2*m_k | m_{k+1}, b=2 and b=3):")
    ms_fact_2 = [2**k * math.factorial(k) for k in range(1, 6)]   # [2, 8, 48, 384, 3840]
    ms_fact_3 = [2**k * math.factorial(k) for k in range(1, 5)]   # [2, 8, 48, 384]
    for b, ms in [(2, ms_fact_2), (3, ms_fact_3)]:
        R = Fraction(1)
        dm = 0.0
        f0 = 0.0
        near1_neg = 0.0
        for k, m in enumerate(ms, 1):
            if k > 1:
                check(m % (2 * ms[k - 2]) == 0, "2*m_{k-1} | m_k")
            R *= Fraction(b ** m, b ** m + 1)
            T = 2 * m
            check(pow(b, T, R.denominator) == 1, "b^{2m} = 1 mod D_k")
            if k <= 3:
                check(order_mod(b, R.denominator, T) == T, "exact order 2m")
            xs, digs = orbit_from_fraction_fast(R, b, T, W=40)
            dm = discrepancy(xs)
            f0 = sum(1 for d in digs if d == 0) / T
            near0_pos = sum(1 for x in xs if 0.0 <= x < b ** (-6)) / T
            near1_neg = sum(1 for x in xs if x > 1.0 - b ** (-6)) / T
            if k >= 2:
                check(dm >= 1.0 - 2.0 ** (-(k - 1)) - 0.20, f"D(mu_k) too small for all-+1 b={b} k={k}")
            print(f"    b={b}, k={k}, m_k={m:4d}, T_k={T:4d}: D(mu_k)={dm:.5f}, "
                  f"f_0={f0:.5f}, 0+={near0_pos:.4f}, 1-={near1_neg:.4f}")
        min_d = 0.90 if b == 2 else 0.80
        check(dm > min_d and f0 > min_d and near1_neg < 0.01,
              f"all-+1 did not concentrate at 0+ for b={b}")

    # 4b. Finite runs of r = 1, 2, 3 consecutive +1s after a -1 reset:
    print()
    print("  [4b] r-runs of +1 after a -1 reset: D -> 1 - 2^{-r} and f_0 -> 1 - ((b-1)/b)*2^{-r}:")
    for b, m1, m2 in [(2, 6, 12), (3, 4, 8)]:
        R = Fraction(b ** m1, b ** m1 - 1) * Fraction(b ** m2, b ** m2 - 1)
        D1 = b ** m1 - 1
        T = m2 * D1
        check(pow(b, T, R.denominator) == 1, "T_2 period check")
        xs_reset, digs_reset = orbit_from_fraction_fast(R, b, T, W=40)
        d_reset = discrepancy(xs_reset)
        check(d_reset <= 1.0 / D1 + 1e-12, "reset discrepancy bound")
        print(f"    b={b}, reset (-1,-1) m=({m1},{m2}), D_1={D1}, T_2={T}: "
              f"D={d_reset:.5f} (<=1/D_1={1/D1:.5f}), f_0={sum(d==0 for d in digs_reset)/T:.5f}")
        for r_run in range(1, 4):
            mk = T if r_run == 1 else 2 * T
            R *= Fraction(b ** mk, b ** mk + 1)
            T = 2 * mk
            check(pow(b, T, R.denominator) == 1, f"T period check r={r_run}")
            xs, digs = orbit_from_fraction_fast(R, b, T, W=40)
            dm = discrepancy(xs)
            f0 = sum(1 for d in digs if d == 0) / T
            f_last = sum(1 for d in digs if d == b - 1) / T
            pred_D = 1.0 - 2.0 ** (-r_run)
            pred_f0 = 1.0 - ((b - 1) / b) * 2.0 ** (-r_run)
            pred_flast = (1.0 / b) * 2.0 ** (-r_run)
            check(abs(dm - pred_D) < 0.02, f"D mismatch b={b} r={r_run}: {dm} vs {pred_D}")
            check(abs(f0 - pred_f0) < 0.02, f"f0 mismatch b={b} r={r_run}: {f0} vs {pred_f0}")
            check(abs(f_last - pred_flast) < 0.02, f"f_{b-1} mismatch b={b} r={r_run}: {f_last} vs {pred_flast}")
            print(f"    b={b}, r={r_run}, m={mk:5d}, T={T:5d}: "
                  f"D={dm:.5f} (pred {pred_D:.5f}), f_0={f0:.5f} (pred {pred_f0:.5f}), "
                  f"f_{b-1}={f_last:.5f} (pred {pred_flast:.5f})")

    # 4c. Continuous sweep on a +1 shell [m_4, 2*m_4] (b=2, r=2):
    R_r1 = Fraction(2**6, 2**6 - 1) * Fraction(2**12, 2**12 - 1) * Fraction(2**756, 2**756 + 1)
    m_sw = 3024
    R_r2 = R_r1 * Fraction(2**m_sw, 2**m_sw + 1)
    xs_sw, digs_sw = orbit_from_fraction_fast(R_r2, 2, 2 * m_sw, W=40)
    print()
    print(f"  [4c] Continuous sweep on r=2 (+1) shell [m_4, 2*m_4] = [{m_sw}, {2*m_sw}] (b=2):")
    for frac in (1.0, 1.2, 1.4, 1.6, 1.8, 2.0):
        N = int(round(frac * m_sw))
        theta = m_sw / N
        pred_D = 1.0 - theta * 0.5
        obs_D = discrepancy(xs_sw[:N])
        obs_f0 = sum(1 for d in digs_sw[:N] if d == 0) / N
        pred_f0 = 0.5 + 0.5 * pred_D
        check(abs(obs_D - pred_D) < 0.015, f"sweep D mismatch at N={N}: {obs_D} vs {pred_D}")
        check(abs(obs_f0 - pred_f0) < 0.015, f"sweep f0 mismatch at N={N}: {obs_f0} vs {pred_f0}")
        print(f"    N={N:5d} (theta={theta:.3f}): D_N={obs_D:.4f} (pred {pred_D:.4f}), "
              f"f_0={obs_f0:.4f} (pred {pred_f0:.4f})")

    # 4d. Finite-scale illustration of the -1 melting transition after a +1 shell (b=2, m=(2,4,24)):
    R_m1 = Fraction(2**2, 3) * Fraction(2**4, 15) * Fraction(2**24, 2**24 + 1)
    D3 = R_m1.denominator
    T3 = 48
    A3 = R_m1.numerator % D3
    orb3 = [(A3 * pow(2, t, D3)) % D3 for t in range(T3)]
    print()
    print(f"  [4d] Finite-scale illustration of -1 melting after +1 shell (b=2, m=(2,4,24), T_3=48):")
    prev_d = 1.0
    for exp_I in (0, 3, 6, 9):
        I = 1 << exp_I
        pts = [((a * x) % D3) / D3 for a in range(1, I + 1) for x in orb3]
        d_obs = discrepancy(pts)
        f0_obs = sum(1 for v in pts if v < 0.5) / len(pts)
        beta = min(1.0, exp_I / 24.0)
        pred_alpha = 0.5 * (1.0 - beta)
        check(d_obs < prev_d, f"expected monotone decrease during melting at I={I}")
        check(abs(d_obs - pred_alpha) < 0.08, f"melting discrepancy too far from asymptotic alpha at I={I}")
        prev_d = d_obs
        print(f"    I=2^{exp_I:2d}={I:4d} (beta={beta:.3f}): D={d_obs:.4f} (asymptotic alpha={pred_alpha:.4f}), f_0={f0_obs:.4f}")
    R_small = Fraction(4, 3) * Fraction(2**12, 2**12 + 1)
    Ds = R_small.denominator
    Ts = 24
    As = R_small.numerator % Ds
    orbs = [(As * pow(2, t, Ds)) % Ds for t in range(Ts)]
    check(all(gcd(x, Ds) == 1 for x in orbs), "orbit points must be units mod D_2")
    print(f"    Exact complete-cycle reset: all {Ts} orbit points of R_2 (D_2={Ds}) are units mod D_2: ok")


# ---------------------------------------------------------------- Section 5: Cyclotomic family


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i + j] += x * y
    while len(res) > 1 and res[-1] == 0:
        res.pop()
    return res


def poly_div_exact(a: list[int], b: list[int]) -> list[int]:
    """Exact polynomial division in Z[q], verified once via exact multiplication."""
    orig_a = list(a)
    while len(orig_a) > 1 and orig_a[-1] == 0:
        orig_a.pop()
    rem = list(orig_a)
    db = len(b) - 1
    check(len(rem) >= len(b), "poly_div_exact degree error")
    q = [0] * (len(rem) - db)
    for i in range(len(q) - 1, -1, -1):
        c, r = divmod(rem[i + db], b[db])
        if r != 0:
            raise SystemExit("FAIL: poly_div_exact non-integer quotient")
        q[i] = c
        for j in range(db + 1):
            rem[i + j] -= c * b[j]
    check(all(x == 0 for x in rem) and poly_mul(q, b) == orig_a, "poly_div_exact identity failed")
    return q


def poly_eval_int(P: list[int], X: int) -> int:
    val = 0
    for c in reversed(P):
        val = val * X + c
    return val


def build_Pk_Ak(k: int) -> tuple[int, int, int, list[int], list[int], list[int]]:
    p, r = 2 * k + 1, 2 * k + 3
    L = 2 * p * r
    Pp = [(-1) ** i for i in range(p)]
    Pr = [(-1) ** i for i in range(r)]
    P = poly_mul(Pp, Pr)
    A = poly_div_exact([1] * L, P)
    S = A + [0] * (L - len(A))
    c = [S[0]] + [S[i] - S[i - 1] for i in range(1, L)]
    return p, r, L, P, S, c


def section_cyclotomic_simple_normality() -> None:
    set_section("5. Cyclotomic family P_k")
    header("5. Cyclotomic family P_k(q), base-2 simple normality & prescribed alpha")

    # 5a. Closed-form theorem (Proposition 5.1) for all k = 1..25:
    for k in range(1, 26):
        p, r, L, P, S, c = build_Pk_Ak(k)
        check(P == P[::-1], f"P_{k} not palindromic")
        check(len(P) - 1 == 2 * p, f"deg P_{k} != 2p")
        A = S[: L - 2 * p]
        check(A == A[::-1], f"A_{k} not palindromic")
        check(all(x != 0 for x in A), f"internal zero found in A_{k}")
        check(all(x == 0 for x in S[L - 2 * p :]), f"trailing entry nonzero in S_{k}")
        pos = sum(1 for x in A if x > 0)
        neg = sum(1 for x in A if x < 0)
        check(pos == 2 * (k + 2) * (2 * k + 1), f"pos count mismatch k={k}")
        check(neg == 2 * k * (2 * k + 1), f"neg count mismatch k={k}")
        check(min(S) == -2 * k and max(S) == 2 * k + 2, f"range of S_{k} mismatch")
        check(max(abs(x) for x in c) <= 2, f"max |c_s| > 2 at k={k}")
        check(Fraction(2 * p, L) == Fraction(1, 2 * k + 3), f"rho_k != 1/(2k+3) at k={k}")
        # Exact tail identity on trailing zero bands: tau_{L-d}(q) = q^d / P_k(q) identically,
        # verified by checking c_{L-d+u mod L} = 0 for 1 <= u < d and = c_{u-d} for d <= u <= L:
        if k <= 12:
            for d in range(1, 2 * p + 1):
                i_z = L - d
                check(all(c[(i_z + u) % L] == 0 for u in range(1, d)), f"zero-band tail prefix k={k}, d={d}")
                check(c[(i_z + d) % L] == 1, f"zero-band leading term != 1 k={k}, d={d}")
            num_G = poly_mul([1, 1], [1] + [0] * (p * r - 1) + [1])
            den_G = poly_mul([1] + [0] * (p - 1) + [1], [1] + [0] * (r - 1) + [1])
            G = poly_div_exact(num_G, den_G)
            check(len(G) == p * p, f"len(G_{k}) != p^2")
            G_pred = [0] * (p * p)
            for m in range(k):
                sgn = (-1) ** m
                for n in range(m * p, m * r + 2):
                    G_pred[n] = sgn
                    G_pred[p * p - 1 - n] = sgn
            sgn_c = (-1) ** k
            for n in range(k * p, k * r + 1):
                G_pred[n] = sgn_c
            check(G == G_pred, f"closed form of G_{k} failed")
    print("  Closed-form theorem for P_k(q) verified for ALL k = 1..25:")
    print("    zero internal zeros, 4k+2 trailing 0+ bands (rho_k = 1/(2k+3)),")
    print("    pos = 2(k+2)(2k+1), neg = 2k(2k+1), range [-2k, 2k+2], max |c_s| <= 2,")
    print("    exact tau_{L-d}(q) = q^d / P_k(q) (k <= 12): ok!")

    # 5b. Generalized band identity & period divisibility T_j | L_j*m_j across bases 2, 3, 5, 10:
    print()
    print("  [5b] Generalized band identity & period divisibility T_j | L_j*m_j across bases:")
    for b in (2, 3, 5, 10):
        p, r, L, P, S, c = build_Pk_Ak(1)
        m0 = 2 if b == 2 else 1
        R0 = Fraction(b ** m0, b ** m0 - 1)
        m1 = 2 * m0
        D_fac = poly_eval_int(P, b ** m1)
        check(gcd(b, D_fac) == 1, f"gcd(b, P_1(b^m1)) != 1 for b={b}")
        check(D_fac % R0.denominator == 1 % R0.denominator, f"P_1(b^m1) != 1 mod D_0 for b={b}")
        R1 = R0 * Fraction(b ** (2 * p * m1), D_fac)
        D1 = R1.denominator
        check(D1 == R0.denominator * D_fac, f"reduced denominator mismatch b={b}")
        check(pow(b, L * m1, D1) == 1, f"T_1 does not divide L_1*m_1 for b={b}")
        T1 = order_mod(b, D1, L * m1)
        # Verify exact cyclotomicTail formula on all 30 bands and r = 0, 1:
        q_rat = Fraction(1, b ** m1)
        for i in range(L):
            tau_exact = (
                sum(Fraction(c[(i + u) % L]) * (q_rat ** u) for u in range(1, L + 1))
                / (1 - q_rat ** L)
            )
            if S[i] == 0:
                d_trail = L - i
                check(tau_exact == (q_rat ** d_trail) / Fraction(D_fac, b ** (2 * p * m1)),
                      f"exact tau_{{L-d}} = q^d/P_1(q) mismatch b={b} i={i}")
            for rem in (0, 1):
                diff = (
                    Fraction(b) ** (i * m1 + rem) * R1
                    - S[i] * Fraction(b) ** rem * R0
                    - Fraction(b) ** rem * R0 * tau_exact
                )
                check(diff.denominator == 1, f"exact cyclotomic band identity failed b={b} i={i} rem={rem}")
                if S[i] == 0:
                    d_trail = L - i
                    lo_b = Fraction(1, 2) * R0 * Fraction(b) ** (rem - d_trail * m1)
                    hi_b = Fraction(2, 1) * R0 * Fraction(b) ** (rem - d_trail * m1)
                    tail_val = Fraction(b) ** rem * R0 * tau_exact
                    check(lo_b <= tail_val <= hi_b, f"zero-band 0+ bound failed b={b} i={i} rem={rem}")
        print(f"    b={b:2d}: m0={m0}, m1={m1}, L_1*m1={L*m1}, exact T_1={T1} | {L*m1}; "
              f"exact cyclotomic band identity & 6 trailing 0+ tails verified!")

    # 5c. Concrete 0+/1- sign mixing in base 2 with P_4 (k=4, L=198, rho=1/11):
    #     R_init = (1 + 2^{-32})^{-1} * (1 + 2^{-128})^{-1} (T_init = 256):
    #     Delta_old = 0.5, f_0 = 0.75, D ~ 0.89.
    #     Applying P_4 at m = 256 (T_mix = 198*256 = 50688) predicts
    #     Delta_new = (2*0.5 + 1)/11 = 2/11, f_0 = 13/22 = 0.5909.
    print()
    print("  [5c] Concrete 0+/1- sign mixing in base 2 (high D while f_0 drops to exact 13/22):")
    R_init = Fraction(2**32, 2**32 + 1) * Fraction(2**128, 2**128 + 1)
    T_init = 256
    xs_init, digs_init = orbit_from_fraction_fast(R_init, 2, T_init, W=40)
    f0_init = sum(d == 0 for d in digs_init) / T_init
    D_init = discrepancy(xs_init)
    p4, r4, L4, P4, S4, _ = build_Pk_Ak(4)
    m_p4 = 256
    D_P4 = poly_eval_int(P4, 2 ** m_p4)
    R_mix = R_init * Fraction(2 ** (2 * p4 * m_p4), D_P4)
    T_mix = L4 * m_p4
    check(pow(2, T_mix, R_mix.denominator) == 1, "T_mix period check")
    xs_mix, digs_mix = orbit_from_fraction_fast(R_mix, 2, T_mix, W=40)
    D_mix = discrepancy(xs_mix)
    f0_mix = sum(d == 0 for d in digs_mix) / T_mix
    f00_mix = sum(1 for i in range(T_mix - 1) if digs_mix[i] == 0 and digs_mix[i + 1] == 0) / (T_mix - 1)
    f11_mix = sum(1 for i in range(T_mix - 1) if digs_mix[i] == 1 and digs_mix[i + 1] == 1) / (T_mix - 1)
    near0_p = sum(1 for x in xs_mix if x < 2.0 ** (-10)) / T_mix
    near1_m = sum(1 for x in xs_mix if x > 1.0 - 2.0 ** (-10)) / T_mix
    pred_f0_mix = 13.0 / 22.0
    check(near1_m > 0.30, f"expected substantial 1- mass after P_4, got {near1_m}")
    check(abs(f0_mix - pred_f0_mix) < 0.01, f"f0_mix={f0_mix:.4f} vs pred {pred_f0_mix:.4f}")
    check(D_mix > 0.85, f"expected high discrepancy D_mix > 0.85, got {D_mix}")
    print(f"    Before P_4 (R_init, T={T_init:5d}): D={D_init:.4f}, f_0={f0_init:.4f} (pred 0.7500)")
    print(f"    After  P_4 (m={m_p4}, T={T_mix:5d}): D={D_mix:.4f}, f_0={f0_mix:.4f} (pred {pred_f0_mix:.4f}), "
          f"0+={near0_p:.4f}, 1-={near1_m:.4f}, f_00={f00_mix:.4f}, f_11={f11_mix:.4f}")

    delta = 0.0
    w_rem = 1.0
    for j in range(1, 501):
        w_rem *= 1.0 - 1.0 / (2 * j + 3)
        delta = (2.0 * delta + 1.0) / (2 * j + 3)
        check(abs(delta) <= 3.0 / (2 * j + 3) + 1e-15, "bias contraction bound failed")
    check(w_rem < 0.08 and delta < 0.002, "asymptotic convergence of (w_rem, delta)")
    print(f"    Exact recursion at J=500: remaining old weight={w_rem:.5f} -> 0, "
          f"bias B_500={delta:.6f} <= 3/1003")

    # 5d. Consecutive-k prescribed discrepancy approximation for arbitrary alpha in (0, 1):
    print()
    print("  [5d] Consecutive-k prescribed discrepancy prod_{k=s}^{s+t_s-1} (1 - 1/(2k+3)) -> 1 - alpha:")
    targets = [
        ("1/pi", 1.0 / math.pi),
        ("sqrt(2)/2", math.sqrt(2.0) / 2.0),
        ("1/e", 1.0 / math.e),
        ("0.123456", 0.123456),
        ("0.9", 0.9),
    ]
    for name, alpha in targets:
        s = max(50, int(math.ceil(1.0 / alpha)) + 1)
        prod = 1.0
        k = s
        while prod * (1.0 - 1.0 / (2 * k + 3)) >= 1.0 - alpha:
            prod *= 1.0 - 1.0 / (2 * k + 3)
            k += 1
        t_s = k - s
        err = (1.0 - prod) - alpha
        check(-1.0 / (2 * s + 3) <= err <= 1e-15, f"prescribed alpha bound failed for {name}")
        print(f"    alpha={name:9s} ({alpha:.6f}), s={s:2d}, t_s={t_s:4d}: "
              f"1 - prod = {1.0 - prod:.6f}, |err| = {abs(err):.6f} <= 1/{2*s+3} = {1/(2*s+3):.6f}")


# ---------------------------------------------------------------- main


def main() -> None:
    t0 = perf_counter()
    section_exact_period_minus()
    section_improved_rates()
    section_signed_periods()
    section_classification_and_digits()
    section_cyclotomic_simple_normality()
    total = sum(SECTION_CHECKS.values())
    print()
    print("Per-section check counts:")
    for name, count in SECTION_CHECKS.items():
        print(f"  {name:42s}: {count:6d}")
    print(f"Total: {total} checks passed in {perf_counter() - t0:.2f} s")


if __name__ == "__main__":
    main()
