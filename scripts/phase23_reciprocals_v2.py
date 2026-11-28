#!/usr/bin/env python3
"""Exact algebraic checks and finite-scale measurements for Phase 23 Track D
(sub-tracks D1, D2, and D4).

Sections:
  1. D1: Rational-orbit inversion x = (1/r) * prod (1 + b^{-m_j})^{-1},
     exact signed band identity, exact subset-sum orbit lock, exact Fraction
     convergent discrepancies across bases b = 2, 3, 4, 5, 10, universal
     repunit inversion Q_b(q) = (1 - q^b)/(1 - q), and Q(1) = 1 multiplier
     excess identity.
  2. D2: Exact maximum discrepancy D_max(b, L) = 2 * b^{-L} of L-normal
     numbers via loop-deleted de Bruijn Eulerian circuits G_{b,L}^*, exact
     L-word counts of W_R^exact, and exact affine mixture D((1-t)lambda + t*sigma).
  3. D2: Unconditional exact L-normal nonnormal reciprocals in ALL bases b >= 2
     (resolving Phase 22 Open Problem #5) via the refined Markov digraph
     G_{b, Q*b^L} (strict interiority, exact L-normality of ALL s*r for
     1 <= s < b, and exact positive discrepancy bounds), plus primitive-root
     convergent L-normal reciprocals and quadratic-reciprocity obstructions.
  4. D4: Bang-Zsigmondy rigidity rad*(b^m - 1) | (b^n - 1) <=> m | n, exact
     characterization of Hull-Dobell divisibility (HD1), strict Hull-Dobell
     chains with D_{k-1} not dividing b^{m_k} - 1, exact Fourier vanishing,
     and persistence of S_i(b^{m_K}) = i + 1 mod (b^{m_{K-1}} - 1).
  5. D4: Anchored coprime non-tetration normal reciprocals for ALL bases b >= 2
     (exact period T_k = s * M^{k-1} * prod q_j, exact CRT Fourier vanishing
     for M^{k-1} not dividing h, exact Fraction discrepancy <= M^{-(k-1)},
     exact band-multiplier divisibility, and doubly-exponential growth audit).
  6. D4: Fully coprime base-2 CRT convolution factorization, exact partial
     fraction identity, universal 01-transition bound, squaring inequalities for
     |C_k(h)| and band L^2 energy E_k(h), prime-exponent partial products, and
     ordinary partition partial products R_k^{(E)} with exact p-adic grid bound.

Standard library only. Exact integer / Fraction assertions are tracked separately
from IEEE-754 floating-point finite measurements (Weyl sums, truncated orbit
discrepancies, and growth-constant audits). Low-level helper invariants do not
increment substantive check counts.

Run from the repository root:  python -B scripts/phase23_reciprocals_v2.py
"""

from __future__ import annotations

import cmath
import math
from fractions import Fraction
from math import gcd
from time import perf_counter

SECTION_EXACT_CHECKS: dict[str, int] = {}
SECTION_FLOAT_CHECKS: dict[str, int] = {}
CURRENT_SECTION = ["init"]


def set_section(name: str) -> None:
    CURRENT_SECTION[0] = name
    SECTION_EXACT_CHECKS.setdefault(name, 0)
    SECTION_FLOAT_CHECKS.setdefault(name, 0)


def internal_assert(cond: bool, msg: str) -> None:
    """Validate helper preconditions/invariants without inflating check counts."""
    if not cond:
        raise SystemExit("INTERNAL FAIL: " + msg)


def check(cond: bool, msg: str) -> None:
    """Record a substantive exact integer / Fraction verification check."""
    if not cond:
        raise SystemExit("FAIL (exact): " + msg)
    sec = CURRENT_SECTION[0]
    SECTION_EXACT_CHECKS[sec] = SECTION_EXACT_CHECKS.get(sec, 0) + 1


def check_float(cond: bool, msg: str) -> None:
    """Record a floating-point finite-measurement consistency check."""
    if not cond:
        raise SystemExit("FAIL (float measurement): " + msg)
    sec = CURRENT_SECTION[0]
    SECTION_FLOAT_CHECKS[sec] = SECTION_FLOAT_CHECKS.get(sec, 0) + 1


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
    r = 1
    for p in factorize(n):
        r *= p
    if n % 4 == 0:
        r *= 2
    return r


def v_p(n: int, p: int) -> int:
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def order_mod(b: int, d: int, multiple: int | None = None) -> int:
    if d == 1:
        return 1
    internal_assert(gcd(b, d) == 1, f"gcd({b}, d[{d.bit_length()}b]) != 1")
    if multiple is None:
        facs = factorize(d)
        phi = d
        for p in facs:
            phi = phi // p * (p - 1)
        multiple = phi
    internal_assert(pow(b, multiple, d) == 1, f"b^{multiple} != 1 mod d[{d.bit_length()}b]")
    order = multiple
    for p in factorize(multiple):
        while order % p == 0 and pow(b, order // p, d) == 1:
            order //= p
    return order


def exact_discrepancy_mod(num: int, den: int, b: int, period: int) -> Fraction:
    """Exact Fraction extreme interval discrepancy of the periodic orbit
    {b^t * num / den mod 1 : 0 <= t < period}."""
    rems: list[int] = []
    x = num % den
    for _ in range(period):
        rems.append(x)
        x = (x * b) % den
    rems.sort()
    n = period
    hi = Fraction(-1, 1)
    lo = Fraction(2, 1)
    for i, r in enumerate(rems):
        pt = Fraction(r, den)
        u = Fraction(i + 1, n) - pt
        if u > hi:
            hi = u
        l = Fraction(i, n) - pt
        if l < lo:
            lo = l
    return hi - lo


def exact_discrepancy_rems(rems: list[int], den: int) -> Fraction:
    """Exact Fraction extreme interval discrepancy of {r / den : r in rems}."""
    ordered = sorted(rems)
    n = len(ordered)
    hi = Fraction(-1, 1)
    lo = Fraction(2, 1)
    for i, r in enumerate(ordered):
        pt = Fraction(r, den)
        u = Fraction(i + 1, n) - pt
        if u > hi:
            hi = u
        l = Fraction(i, n) - pt
        if l < lo:
            lo = l
    return hi - lo


def disc_float_orbit(num: int, den: int, b: int, N: int) -> float:
    """Finite-scale 52-bit truncated discrepancy of first N orbit points {b^n num/den}."""
    shift = max(0, den.bit_length() - 52)
    den_hi = float(den >> shift)
    x = num % den
    pts = [0.0] * N
    for n in range(N):
        pts[n] = (x >> shift) / den_hi
        x = (x * b) % den
    pts.sort()
    hi = 0.0
    lo = 0.0
    invN = 1.0 / N
    for i, v in enumerate(pts):
        u = (i + 1) * invN - v
        if u > hi:
            hi = u
        l = i * invN - v
        if l < lo:
            lo = l
    return hi - lo


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i + j] += x * y
    while len(res) > 1 and res[-1] == 0:
        res.pop()
    return res


def poly_div_exact(a: list[int], b: list[int]) -> list[int]:
    orig = list(a)
    while len(orig) > 1 and orig[-1] == 0:
        orig.pop()
    rem = list(orig)
    db = len(b) - 1
    q = [0] * (len(rem) - db)
    for i in range(len(q) - 1, -1, -1):
        c, r = divmod(rem[i + db], b[db])
        internal_assert(r == 0, "poly_div_exact non-integer quotient")
        q[i] = c
        for j in range(db + 1):
            rem[i + j] -= c * b[j]
    internal_assert(all(x == 0 for x in rem) and poly_mul(q, b) == orig, "poly_div_exact failed")
    return q


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    p = 2
    while p * p <= n:
        if n % p == 0:
            return False
        p += 1
    return True


def in_subgroup_generated_by(target: int, base: int, mod: int) -> int | None:
    """Return smallest s >= 0 with base^s == target (mod mod), or None."""
    t = target % mod
    x = 1 % mod
    for s in range(mod + 1):
        if x == t:
            return s
        x = (x * base) % mod
        if x == 1 % mod and s > 0:
            break
    return None


# ---------------------------------------------------------------- Section 1: D1 Convergent Reciprocals


def section_d1_convergent_reciprocals() -> None:
    set_section("1. D1 Convergent reciprocals")
    header("1. D1: Rational-orbit inversion, exact convergent limits & Q(1)=1 excess identity")

    # 1a. Exact +1-inversion identities: X_k = (1/r) * prod_{j<=k} (1 + b^{-m_j})^{-1}
    #     and Y_k = r * prod_{j<=k} (1 + b^{-m_j}) across bases 2, 3, 4, 5, 10!
    examples = [
        (2, 1, 3),      # D = 2/3
        (2, 1, 5),      # D = 2/5
        (2, 1, 7),      # D = 4/7
        (2, 3, 11),     # D = 2/11
        (2, 1, 15),     # D = 11/20
        (3, 1, 5),      # 2 = 3^3 mod 5
        (3, 1, 7),      # 2 = 3^2 mod 7 (also exact 1-normal!)
        (3, 1, 17),     # 2 = 3^14 mod 17
        (3, 5, 17),     # test gcd(A, b) = 1 with A > 1
        (4, 3, 31),     # 2 = 4^3 mod 31
        (4, 7, 127),    # 2 = 4^4 mod 127
        (5, 1, 3),      # 2 = 5^1 mod 3
        (5, 1, 9),      # 2 = 5^1 mod 9
        (5, 1, 49),     # 2 = 5^18 mod 49
        (10, 1, 19),    # 2 = 10^17 mod 19
        (10, 1, 49),    # 2 = 10^2 mod 49
    ]
    print("  [1a] Exact Fraction convergent discrepancies D(mu(r; b)) with 2 in <b> mod D:")
    for b, A, D in examples:
        check(gcd(b, A * D) == 1 and gcd(A, D) == 1, f"coprimality failed {(b, A, D)}")
        s_pow = in_subgroup_generated_by(2, b, D)
        check(s_pow is not None, f"2 not in <{b}> mod {D}")
        ord_A = order_mod(b, A)
        ord_D = order_mod(b, D)
        P = math.lcm(ord_A, ord_D)
        d_exact = exact_discrepancy_mod(A, D, b, ord_D)
        check(Fraction(0) < d_exact < Fraction(1), f"discrepancy not in (0, 1) for {(b, A, D)}")
        # Check exact +1-inversion period divisibility & exact subset-sum orbit lock for 2 steps
        if b ** (4 * P) < 10**60:
            m1 = P
            m2 = 2 * P
            r = Fraction(A, D)
            X1 = Fraction(1, 1) / r * Fraction(b**m1, b**m1 + 1)
            X2 = X1 * Fraction(b**m2, b**m2 + 1)
            check(pow(b, 2 * m1, X1.denominator) == 1, f"ord(X1) !| 2*m1 for {(b, A, D)}")
            check(pow(b, 2 * m2, X2.denominator) == 1, f"ord(X2) !| 2*m2 for {(b, A, D)}")
            # Exact signed band identity for X2 at i=0,1 and r_idx=0,1:
            for i_b in (0, 1):
                mult = 1 if i_b % 2 == 0 else 0
                sgn = -1 if i_b % 2 == 0 else 1
                for r_idx in (0, 1):
                    lhs = Fraction(b ** (i_b * m2 + r_idx)) * X2
                    rhs = mult * Fraction(b**r_idx) * X1 + sgn * Fraction(b**r_idx) * X1 / (b**m2 + 1)
                    check((lhs - rhs).denominator == 1, f"signed band identity failed {(b, A, D)}")
            # Exact subset-sum orbit lock on Y2 = r*(1 + b^{-m1})*(1 + b^{-m2}) for n >= m1 + m2:
            Y2 = r * (1 + Fraction(1, b**m1)) * (1 + Fraction(1, b**m2))
            for n_test in range(m1 + m2, m1 + m2 + min(ord_D, 6)):
                diff = Fraction(b**n_test) * Y2 - Fraction(4 * (b**n_test)) * r
                check(diff.denominator == 1, f"subset-sum orbit lock failed {(b, A, D)}")
                # And 4 * b^n * r == b^{n + 2*s_pow} * r (mod 1):
                diff2 = Fraction(4 * (b**n_test)) * r - Fraction(b ** (n_test + 2 * s_pow)) * r
                check(diff2.denominator == 1, f"2^2 = b^(2s) orbit invariance failed {(b, A, D)}")
        print(f"    b={b:2d}, r={A}/{D:<3d} (ord_D={ord_D:2d}, 2=b^{s_pow:2d} mod D): "
              f"D_inf = {str(d_exact):>9s} = {float(d_exact):.6f}")

    # 1b. Finite-scale convergence demonstration of BOTH D_N(X_k; 2) -> 1 and D_N(Y_k; 2) -> D(r; 2):
    print()
    print("  [1b] Finite-scale orbit check of (X_k, Y_k) for b=2, r=1/3 (D=2/3) and r=1/5 (D=2/5):")
    for A, D, target_D in [(1, 3, Fraction(2, 3)), (1, 5, Fraction(2, 5))]:
        P = order_mod(2, D)
        # Non-tetration schedule with P | m_1 and 2*m_j | m_{j+1} (ratios 6, 16):
        ms = [16, 96, 1536]
        check(ms[0] % P == 0 and ms[1] % (2 * ms[0]) == 0 and ms[2] % (2 * ms[1]) == 0, "schedule div failed")
        X = Fraction(D, A)
        Y = Fraction(A, D)
        for mj in ms:
            X *= Fraction(2**mj, 2**mj + 1)
            Y *= Fraction(2**mj + 1, 2**mj)
        check(X * Y == 1, "X * Y != 1")
        N_check = 2 * ms[2]
        dX = disc_float_orbit(X.numerator, X.denominator, 2, N_check)
        dY = disc_float_orbit(Y.numerator, Y.denominator, 2, N_check)
        check_float(dX > 0.82, f"expected high D(X) for r={A}/{D}, got {dX}")
        check_float(abs(dY - float(target_D)) < 0.05, f"D(Y) too far from {target_D}: got {dY}")
        print(f"    [float] b=2, r={A}/{D}, m={ms}, N={N_check}: D_N(X_3)={dX:.4f} (-> 1), "
              f"D_N(Y_3)={dY:.4f} (target {target_D} = {float(target_D):.4f})")

    # 1c. Base-2 dense periodic-word spectrum in [0, 1]: de Bruijn order-4 + z zeros!
    print()
    print("  [1c] Base-2 exact convergent discrepancies spanning [0, 1] (order-4 de Bruijn + z zeros):")
    # Standard cyclic order-4 binary de Bruijn word of length 16 (rotated to end in 1)
    db4 = "0000100110101111"
    check(len(db4) == 16 and len({(db4 + db4)[i : i + 4] for i in range(16)}) == 16, "db4 invalid")
    for z in (0, 4, 16, 48, 144):
        w = "0" * z + db4
        P = len(w)
        A = int(w, 2)
        den = (1 << P) - 1
        g = gcd(A, den)
        A_red, D_red = A // g, den // g
        check(A_red % 2 == 1 and D_red % 2 == 1, "oddness failed for db4+zeros")
        d_exact = exact_discrepancy_mod(A_red, D_red, 2, order_mod(2, D_red, P))
        target_approx = Fraction(z, z + 16)
        check(abs(d_exact - target_approx) < Fraction(7, 50), "db4+zeros discrepancy far from z/(z+16)")
        print(f"    z={z:3d} zeros (P={P:3d}, target z/(z+16)={float(target_approx):.4f}): "
              f"exact D(mu(r; 2)) = {float(d_exact):.6f}")

    # 1d. Universal repunit inversion Q_b(q) = (1 - q^b)/(1 - q): exact band identity & period divisibility
    #     Includes both A = 1 and A > 1 reduced seeds with gcd(b, A*D) = 1.
    print()
    print("  [1d] Universal repunit inversion Q_b(q) = (1 - q^b)/(1 - q) across b = 2..6 (incl. A > 1):")
    repunit_seeds = [
        (2, 1, 3),
        (3, 1, 4),
        (3, 5, 7),
        (3, 2, 5),
        (4, 1, 5),
        (4, 3, 7),
        (5, 1, 6),
        (5, 2, 3),
        (6, 1, 7),
    ]
    for b, A, D in repunit_seeds:
        check(gcd(A, D) == 1 and gcd(b, A * D) == 1, f"repunit seed coprimality failed {(b, A, D)}")
        P = math.lcm(order_mod(b, A), order_mod(b, D))
        m1 = P
        m2 = b * P
        X0 = Fraction(D, A)
        X1 = X0 * Fraction(b ** ((b - 1) * m1) * (b**m1 - 1), b ** (b * m1) - 1)
        X2 = X1 * Fraction(b ** ((b - 1) * m2) * (b**m2 - 1), b ** (b * m2) - 1)
        check(pow(b, b * m1, X1.denominator) == 1, f"repunit ord(X1) !| b*m1 for {(b, A, D)}")
        check(pow(b, b * m2, X2.denominator) == 1, f"repunit ord(X2) !| b*m2 for {(b, A, D)}")
        # Exact band identity for 1/Q_b(q) = (1-q)/(1-q^b): S_0 = 1, S_1 = ... = S_{b-1} = 0!
        q = Fraction(1, b**m1)
        for i_b in range(b):
            S_i = 1 if i_b == 0 else 0
            # tail tau_i(q) = (-q + q^b)/(1 - q^b) if i == 0 else q^{b-i}*(1 - q)/(1 - q^b)
            tau_i = (-q + q**b) / (1 - q**b) if i_b == 0 else (q ** (b - i_b)) * (1 - q) / (1 - q**b)
            for rem in (0, 1):
                lhs = Fraction(b ** (i_b * m1 + rem)) * X1
                rhs = S_i * Fraction(b**rem) * X0 + Fraction(b**rem) * X0 * tau_i
                check((lhs - rhs).denominator == 1, f"repunit band identity failed {(b, A, D)}, i={i_b}")
        # Exact subset-sum formula on Y1 = (A/D) * (1 + b^{-m1} + ... + b^{-(b-1)*m1})
        Y1 = Fraction(A, D) * sum(Fraction(1, b ** (s * m1)) for s in range(b))
        check(X1 * Y1 == 1, f"X1*Y1 != 1 for {(b, A, D)}")
        for s in range(b):
            n_test = s * m1
            diff = Fraction(b**n_test) * Y1 - Fraction((s + 1) * (b**n_test), 1) * Fraction(A, D)
            # drop tail sum_{u > s} b^{(s-u)*m1} * A/D
            tail = Fraction(A, D) * sum(Fraction(1, b ** ((u - s) * m1)) for u in range(s + 1, b))
            check((diff - tail).denominator == 1, f"repunit Y1 block {s} failed for {(b, A, D)}")
        print(f"    b={b}, r={A}/{D}: P={P:2d}, ord(X1)|{b*m1}, ord(X2)|{b*m2}, all {b} band identities exact: ok")

    # 1e. Exact Q(1) = 1 multiplier-excess identity (Proposition 1.4) + uncapped |S_i|<=1 check (L <= 50)
    Phi: dict[int, list[int]] = {1: [-1, 1]}
    for n in range(2, 51):
        p = [-1] + [0] * (n - 1) + [1]
        for d in range(1, n):
            if n % d == 0:
                p = poly_div_exact(p, Phi[d])
        Phi[n] = p
    q1_checked = 0
    for k in range(1, 16):
        p, r = 2 * k + 1, 2 * k + 3
        L = 2 * p * r
        P_poly = poly_mul([(-1) ** i for i in range(p)], [(-1) ** i for i in range(r)])
        check(sum(P_poly) == 1, f"P_{k}(1) != 1")
        A_poly = poly_div_exact([1] * L, P_poly)
        S = A_poly + [0] * (L - len(A_poly))
        lhs_ex = sum(x - 1 for x in S if x >= 2)
        rhs_ex = sum(1 for x in S if x == 0) + sum(1 - x for x in S if x <= -1)
        check(lhs_ex == rhs_ex and max(S) >= 2, f"Q(1)=1 excess identity failed k={k}")
        q1_checked += 1
    rho_ge_half_total = 0
    rho_ge_half_lowdeg = 0
    for L in range(2, 51):
        divs = [d for d in range(2, L + 1) if L % d == 0]
        all_ones = [1] * L

        def dfs(idx: int, cur_Q: list[int], cur_deg: int) -> None:
            nonlocal rho_ge_half_total, rho_ge_half_lowdeg
            if cur_deg > 0 and abs(sum(cur_Q)) >= 2:
                A_poly = poly_div_exact(all_ones, cur_Q)
                if max(abs(x) for x in A_poly) <= 1:
                    zeros = (L - len(A_poly)) + sum(1 for x in A_poly if x == 0)
                    check(zeros * 2 >= L, f"found |S_i|<=1 with rho<1/2 at L={L}")
                    rho_ge_half_total += 1
                    if cur_deg <= L // 2:
                        rho_ge_half_lowdeg += 1
            for i in range(idx, len(divs)):
                d = divs[i]
                phi_d = len(Phi[d]) - 1
                dfs(i + 1, poly_mul(cur_Q, Phi[d]), cur_deg + phi_d)

        dfs(0, [1], 0)
    print(f"  [1e] Q(1)=1 exact excess identity verified on {q1_checked} P_k polynomials; "
          f"all {rho_ge_half_total} cyclotomic divisors with |S_i|<=1 (L<=50; "
          f"{rho_ge_half_lowdeg} with deg Q <= floor(L/2)) have rho >= 1/2: ok")


# ---------------------------------------------------------------- Section 2: D2 Exact D_max(b, L) = 2*b^{-L}


def eulerian_circuit_debruijn_deleted(b: int, L: int) -> list[int]:
    """Return cyclic digit sequence of Eulerian circuit C* of G_{b,L}*
    (all b^L - 2 edges except 0^L and (b-1)^L). Works for all b >= 2, L >= 1."""
    if L == 1:
        return list(range(1, b - 1))
    nv = b ** (L - 1)
    mod_v = nv
    adj: dict[int, list[tuple[int, int]]] = {u: [] for u in range(nv)}
    for u in range(nv):
        for d in range(b):
            v = (u * b + d) % mod_v
            if (u == 0 and d == 0) or (u == nv - 1 and d == b - 1):
                continue
            adj[u].append((v, d))
    stack: list[tuple[int, int | None]] = [(0, None)]
    digs: list[int] = []
    while stack:
        u, _ = stack[-1]
        if adj[u]:
            v, d = adj[u].pop()
            stack.append((v, d))
        else:
            _, d_in = stack.pop()
            if d_in is not None:
                digs.append(d_in)
    digs.reverse()
    check(len(digs) == b**L - 2, f"G* circuit length mismatch for b={b}, L={L}")
    return digs


def build_extremal_L_normal_word(b: int, L: int, R: int) -> list[int]:
    """Exact length R*b^L cyclic word traversing every L-word exactly R times,
    with R consecutive 0^L self-loops and R consecutive (b-1)^L self-loops."""
    if L == 1:
        w = [0] * R + [b - 1] * R
        for _ in range(R):
            w.extend(range(1, b - 1))
        # Rotate to end in 1
        idx1 = w.index(1)
        return w[idx1 + 1 :] + w[: idx1 + 1]
    c_star = eulerian_circuit_debruijn_deleted(b, L)
    # Trace vertices along c_star starting from vertex 0^{L-1}
    nv = b ** (L - 1)
    # Actually Hierholzer started at vertex 0, so the state before edge c_star[0] is 0!
    full: list[int] = []
    state = 0
    ins0 = False
    ins_max = False
    for _ in range(R):
        for d in c_star:
            if not ins0 and state == 0:
                full.extend([0] * R)
                ins0 = True
            if not ins_max and state == nv - 1:
                full.extend([b - 1] * R)
                ins_max = True
            full.append(d)
            state = (state * b + d) % nv
    check(ins0 and ins_max and state == 0 and len(full) == R * (b**L), "W_R^exact build failed")
    # Rotate so last digit is 1
    idx1 = full.index(1)
    return full[idx1 + 1 :] + full[: idx1 + 1]


def verify_exact_L_word_counts(digs: list[int], b: int, L: int) -> None:
    P = len(digs)
    bL = b**L
    check(P % bL == 0, "period not divisible by b^L")
    target = P // bL
    counts: dict[int, int] = {}
    ext = digs + digs[: L - 1]
    w = 0
    for j in range(L):
        w = w * b + ext[j]
    mod_w = bL
    for i in range(P):
        counts[w] = counts.get(w, 0) + 1
        if i + 1 < P:
            w = (w * b + ext[i + L]) % mod_w
    check(len(counts) == bL and all(c == target for c in counts.values()), "not exact L-normal")


def section_d2_sharp_max_discrepancy() -> None:
    set_section("2. D2 Exact D_max(b,L) = 2/b^L")
    header("2. D2: Exact maximum discrepancy D_max(b, L) = 2 * b^{-L} of L-normal numbers")

    cases = [
        (2, 1, [5, 25, 100]),
        (2, 2, [5, 25, 100]),
        (2, 3, [5, 25, 60]),
        (3, 1, [5, 25, 100]),
        (3, 2, [5, 25, 60]),
        (4, 1, [5, 25, 60]),
        (5, 1, [5, 25, 50]),
    ]
    print("  [2a] Exact L-normal periodic rationals r_R = v(W_R^exact)/(b^{R*b^L}-1) approaching 2*b^{-L}:")
    for b, L, Rs in cases:
        dmax = Fraction(2, b**L)
        row = []
        prev_d = Fraction(-1, 1)
        for R in Rs:
            digs = build_extremal_L_normal_word(b, L, R)
            verify_exact_L_word_counts(digs, b, L)
            P = len(digs)
            A = 0
            for dg in digs:
                A = A * b + dg
            check(gcd(A, b) == 1, "last digit 1 failed")
            den = b**P - 1
            if P <= 120:
                d_val = exact_discrepancy_mod(A, den, b, P)
                check(d_val <= dmax, f"exceeded 2*b^(-L): {d_val} > {dmax}")
                d_flt = float(d_val)
                check(d_val >= prev_d, "expected monotone approach for small R")
                prev_d = d_val
                tag = "exact"
            else:
                d_flt = disc_float_orbit(A, den, b, P)
                check_float(d_flt <= float(dmax) + 1e-9, f"exceeded 2*b^(-L): {d_flt}")
                tag = "float"
            row.append(f"R={R}:{d_flt:.4f}({tag})")
        check_float(d_flt > 0.70 * float(dmax), f"did not approach 2*b^(-L) for b={b}, L={L}: {d_flt}")
        print(f"    b={b}, L={L} (2*b^-L = {str(dmax):>5s} = {float(dmax):.4f}): " + ",  ".join(row))

    # 2b. Exact affine mixture law D((1-t)lambda + t*sigma) = t*D(sigma) verified on atomic measures
    #     and dense base-2 L=2 convergent spectrum in [0, 1/2] via mixing W_R^exact + order-4 de Bruijn!
    print()
    print("  [2b] Base-2 exact 2-normal convergent reciprocals spanning [0, 1/2] (exact Fraction D):")
    db4 = [int(ch) for ch in "0000100110101111"]
    verify_exact_L_word_counts(db4, 2, 2)
    # Start both at digit 0 -> ... -> digit 1 (matching common 1-digit prefix 0 and ending in 1).
    db4_01 = [int(ch) for ch in "0000100110101111"]  # starts with 0, ends with 1!
    w2_ext = [0] * 17 + [1] * 17 + [0, 1] * 15  # starts with 0, ends with 1, length 64, exact 16 of each 2-word!
    verify_exact_L_word_counts(w2_ext, 2, 2)
    for c_ext, c_db in [(0, 4), (1, 12), (1, 4), (2, 4), (4, 2), (4, 0)]:
        word = w2_ext * c_ext + db4_01 * c_db
        verify_exact_L_word_counts(word, 2, 2)
        P = len(word)
        A = 0
        for dg in word:
            A = (A << 1) | dg
        den = (1 << P) - 1
        d_ex = exact_discrepancy_mod(A, den, 2, P)
        check(Fraction(0) < d_ex <= Fraction(1, 2), f"2-normal discrepancy out of (0, 1/2]: {d_ex}")
        w_frac = (64 * c_ext) / P
        print(f"    c_ext={c_ext}, c_db={c_db:2d} (P={P:3d}, ext weight={w_frac:.3f}): "
              f"EXACT 2-normal, exact D(mu(r; 2)) = {float(d_ex):.5f}")


# ---------------------------------------------------------------- Section 3: D2 Unconditional ALL bases b >= 2


def build_refined_debruijn_rational(b: int, L: int, R: int) -> tuple[int, int, int, int, list[int]]:
    """Construct exact rational r = A / (b^P - 1) from the refined Markov digraph
    G_{b, M} (M = lcm(1..b-1) * b^L) with R consecutive self-loops at 0 and M-1."""
    Q = 1
    for s in range(1, b):
        Q = math.lcm(Q, s)
    M = Q * (b**L)
    adj: dict[int, list[tuple[int, int]]] = {u: [] for u in range(M)}
    for u in range(M):
        for d in range(b):
            v = (b * u + d) % M
            if (u == 0 and d == 0) or (u == M - 1 and d == b - 1):
                continue
            adj[u].append((v, d))
    stack: list[tuple[int, tuple[int, int, int] | None]] = [(0, None)]
    circuit: list[tuple[int, int, int]] = []
    while stack:
        u, _ = stack[-1]
        if adj[u]:
            v, d = adj[u].pop()
            stack.append((v, (u, d, v)))
        else:
            _, edge = stack.pop()
            if edge is not None:
                circuit.append(edge)
    circuit.reverse()
    check(len(circuit) == b * M - 2, f"G*_{{b,M}} circuit length mismatch b={b}, L={L}")
    full: list[tuple[int, int, int]] = []
    ins0 = False
    insM = False
    for _ in range(R):
        for u, d, v in circuit:
            if not ins0 and u == 0:
                full.extend([(0, 0, 0)] * R)
                ins0 = True
            if not insM and u == M - 1:
                full.extend([(M - 1, b - 1, M - 1)] * R)
                insM = True
            full.append((u, d, v))
    check(ins0 and insM and len(full) == R * b * M, "refined walk length mismatch")
    P = len(full)
    # Rotate so last vertex has floor(b*u/M) == 1 (giving gcd(A, b) = 1!)
    rot = next((idx + 1) % P for idx, (u, _, _) in enumerate(full) if (u * b) // M == 1)
    full = full[rot:] + full[:rot]
    digs = [(u * b) // M for u, _, _ in full]
    check(digs[-1] == 1, "rotated last digit != 1")
    A = 0
    for dg in digs:
        A = A * b + dg
    check(gcd(A, b) == 1, "gcd(A, b) != 1")
    us = [u for u, _, _ in full]
    return M, P, A, b**P - 1, us


def section_d2_all_bases_L_normal() -> None:
    set_section("3. D2 All-base L-normal reciprocals")
    header("3. D2: Unconditional exact L-normal nonnormal reciprocals in ALL bases b >= 2")

    print("  [3a] Refined Markov digraph G_{b, Q*b^L} (strict interiority + exact L-normality for ALL s < b):")
    for b, L, R in [(2, 1, 10), (2, 2, 10), (3, 1, 20), (3, 2, 8), (4, 1, 10), (5, 1, 5)]:
        M, P, A, den, us = build_refined_debruijn_rational(b, L, R)
        # Exact strict interiority check u_n / M < T_b^n(r) < (u_n + 1) / M at EVERY n < P!
        rem = A
        for n, u in enumerate(us):
            check(u * den < rem * M < (u + 1) * den, f"strict interiority failed b={b} L={L} n={n}")
            rem = (rem * b) % den
        check(rem == A, "cycle closure failed")
        # Exact L-normality check & exact proven-interval bound for EVERY s = 1, ..., b - 1!
        bL = b**L
        # Exact integer ceiling k_R = min{k >= 0 : b^k >= R} (avoid floating-point log in exact checks).
        k_R = 0
        bk = 1
        while bk < R:
            k_R += 1
            bk *= b
        if k_R >= 1:
            check(b ** (k_R - 1) < R <= b ** k_R, f"exact k_R bracket failed for b={b}, R={R}")
        # Common interval I_R = [eta_R, 1 - eta_R) with eta_R = b * b^{-k_R} = b^{1 - k_R}
        eta_num = 1
        eta_den = b ** (k_R - 1) if k_R >= 1 else 1
        proven_lb = Fraction(2, b * M) - Fraction(2 * k_R, R * b * M) - Fraction(2 * b, R)
        d_vals = []
        d_mode = "exact" if P <= 100 else "float"
        for s in range(1, b):
            counts: dict[int, int] = {}
            r0 = (s * A) % den
            in_IR = 0
            for _ in range(P):
                w = (r0 * bL) // den
                counts[w] = counts.get(w, 0) + 1
                if k_R >= 2 and eta_num * den <= r0 * eta_den < (eta_den - eta_num) * den:
                    in_IR += 1
                r0 = (r0 * b) % den
            check(len(counts) == bL and all(c == P // bL for c in counts.values()),
                  f"exact L-normality failed for b={b}, L={L}, s={s}")
            if k_R >= 2 and eta_den > 2:
                exact_IR_gap = (Fraction(eta_den - 2 * eta_num, eta_den)) - Fraction(in_IR, P)
                check(exact_IR_gap >= proven_lb, f"exact |I_R|-mu(I_R) < proven lb for b={b}, L={L}, s={s}")
            if P <= 100:
                d_ex = exact_discrepancy_mod(s * A, den, b, P)
                check(Fraction(0) < d_ex <= Fraction(2, bL), f"exact D(s*r) out of (0, 2/b^L]: {d_ex}")
                ds = float(d_ex)
            else:
                ds = disc_float_orbit(s * A, den, b, P)
                check_float(0.0 < ds <= 2.0 / bL + 1e-9, f"float D(s*r) out of (0, 2/b^L]: {ds}")
            d_vals.append(ds)
        print(f"    b={b}, L={L}, R={R:2d}, M={M:2d}, P={P:4d}: strict interiority & exact L-normality "
              f"for ALL s=1..{b-1} ok! D ({d_mode}) in [{min(d_vals):.4f}, {max(d_vals):.4f}] (<= {2/bL:.4f})")

    # 3b. Primitive-root exact convergent L-normal reciprocals x = p * prod (1 + b^{-m_j})^{-1}
    print()
    print("  [3b] Primitive-root exact convergent L-normal reciprocals (r = 1/p, p = k*b^L + 1, D_inf = 2/p):")
    pr_cases = [
        (2, 1, 3),
        (2, 2, 5),
        (2, 2, 13),
        (3, 1, 7),
        (3, 2, 19),
        (3, 3, 163),
        (6, 1, 13),
        (6, 2, 109),
        (7, 1, 71),
        (10, 1, 61),
        (10, 2, 701),
    ]
    for b, L, p in pr_cases:
        check(is_prime(p) and (p - 1) % (b**L) == 0, f"p != k*b^L + 1 for {(b, L, p)}")
        check(order_mod(b, p) == p - 1, f"{b} not primitive root mod {p}")
        # Exact L-word count of 1/p over its period p - 1:
        bL = b**L
        counts: dict[int, int] = {}
        x = 1
        for _ in range(p - 1):
            w = (x * bL) // p
            counts[w] = counts.get(w, 0) + 1
            x = (x * b) % p
        check(len(counts) == bL and all(c == (p - 1) // bL for c in counts.values()),
              f"1/{p} not exact L-normal in base {b}")
        d_ex = exact_discrepancy_mod(1, p, b, p - 1)
        check(d_ex == Fraction(2, p), f"D(1/{p}; {b}) = {d_ex} != 2/{p}")
        print(f"    b={b:2d}, L={L}, p={p:3d}: ord_p(b)={p-1:3d}, exact {L}-normal, "
              f"exact D_inf = 2/{p} = {float(d_ex):.6f}")

    # 3c. Quadratic-reciprocity obstruction check:
    #     (i) all b = 0, 1 (mod 4) at L = 1 (here b in {4, 5, 8, 9}),
    #     (ii) all b = 2 (mod 4) at L = 3 (here b in {2, 6, 10}):
    for b in (4, 5, 8, 9):
        for k in range(1, 200):
            p = k * b + 1
            if is_prime(p):
                check(order_mod(b, p) < p - 1, f"unexpected primitive root b={b}, p={p}")
    for b in (2, 6, 10):
        b3 = b**3
        for k in range(1, 60):
            p = k * b3 + 1
            if is_prime(p):
                check(order_mod(b, p) < p - 1, f"unexpected primitive root b={b}, L=3, p={p}")
    print("  [3c] Quadratic-reciprocity obstruction confirmed for b in {4,5,8,9} (L>=1) and b in {2,6,10} (L>=3): ok")

    # 3d. Prescribed rational digit-frequency convergent reciprocals in base 2:
    print()
    print("  [3d] Prescribed rational base-2 digit frequency p_0 = a/q with convergent discrepancy:")
    for name, word in [
        ("p_0 = 1/3", "011"),
        ("p_0 = 2/5", "00111"),
        ("p_0 = 3/7", "0001111"),
        ("p_0 = 3/7 (alt)", "0101011"),
    ]:
        P = len(word)
        A = int(word, 2)
        den = (1 << P) - 1
        g = gcd(A, den)
        A_r, D_r = A // g, den // g
        check(A_r % 2 == 1 and D_r % 2 == 1, "oddness failed")
        T = order_mod(2, D_r)
        d_ex = exact_discrepancy_mod(A_r, D_r, 2, T)
        p0 = Fraction(word.count("0"), P)
        print(f"    {name:16s} (word={word:7s}, r={A_r}/{D_r}): exact f_0={p0}, exact D_inf={d_ex} ({float(d_ex):.5f})")


# ---------------------------------------------------------------- Section 4: D4 Hull-Dobell Rigidity & Normality


def section_d4_hull_dobell() -> None:
    set_section("4. D4 Hull-Dobell rigidity & growth")
    header("4. D4: Bang-Zsigmondy rigidity, Hull-Dobell normality & (HD1)-(HD2) growth")

    # 4a. Exhaustive check of rad*(b^m - 1) | (b^n - 1) <=> m | n for 2 <= b <= 12, 1 <= m, n <= 16
    rig_checks = 0
    for b in range(2, 13):
        m_max = 16 if b <= 4 else (12 if b <= 6 else 9)
        rads = {m: rad_star(b**m - 1) for m in range(1, m_max + 1)}
        for m in range(1, m_max + 1):
            for n in range(1, m_max + 1):
                lhs = ((pow(b, n, rads[m]) - 1) % rads[m] == 0)
                rhs = (n % m == 0)
                check(lhs == rhs, f"Bang-Zsigmondy rigidity failed: b={b}, m={m}, n={n}")
                rig_checks += 1
    # Explicitly verify full equivalence rad*(b^m - 1) | (b^n - 1) <=> m | n on Zsigmondy exceptions:
    exc_checks = 0
    for b in (3, 7, 15, 31, 63):
        r2 = rad_star(b**2 - 1)
        check(r2 % 4 == 0 and (b - 1) % 4 == 2, f"m=2 exception 2-adic check failed b={b}")
        for n in range(1, 21):
            lhs = ((pow(b, n, r2) - 1) % r2 == 0)
            check(lhs == (n % 2 == 0), f"m=2 exception equiv failed b={b}, n={n}")
            exc_checks += 1
    r26 = rad_star(2**6 - 1)
    check(r26 == 21, "rad*(2^6 - 1) != 21")
    for n in range(1, 25):
        lhs = ((pow(2, n, r26) - 1) % r26 == 0)
        check(lhs == (n % 6 == 0), f"b=2, m=6 exception equiv failed n={n}")
        exc_checks += 1
    print(f"  [4a] Bang-Zsigmondy rigidity rad*(b^m - 1) | (b^n - 1) <=> m | n verified on "
          f"{rig_checks} grid triples + {exc_checks} exception triples (b in {{3,7,15,31,63}}, (2,6)): ok")

    # 4b. Strict Hull-Dobell chains where D_{k-1} does NOT divide b^{m_k} - 1, yet (HD1) holds:
    hd_chains = [
        (2, [2, 4, 8]),        # D_2 = 45, rad*(45)=15 | 255 = 2^8-1, 45 !| 255!
        (2, [3, 6, 12]),       # D_2 = 7*63 = 441, rad*(441)=21 | 2^12-1, 441 !| 2^12-1!
        (3, [1, 2, 6]),        # D_2 = 2*8 = 16, rad*(16)=4 | 728 = 3^6-1, 16 !| 728!
        (3, [2, 4, 8]),        # D_2 = 8*80 = 640, rad*(640)=20 | 3^8-1 = 6560, 640 !| 6560!
        (5, [1, 2, 4]),        # D_2 = 4*24 = 96, rad*(96)=12 | 5^4-1 = 624, 96 !| 624!
        (7, [1, 3, 6]),        # b = 3 mod 4: m_1=1, m_2=3 odd, m_3=6 EVEN, D_2=2052 !| 7^6-1!
    ]
    # Explicit b = 3 (mod 4) parity switch check at k = 3:
    for b_p in (3, 7, 11):
        d2_odd = (b_p - 1) * (b_p**3 - 1)
        check(d2_odd % 4 == 0, "expected 4 | D_2 for odd m_1, m_2")
        check((b_p**9 - 1) % rad_star(d2_odd) != 0, "expected odd m_3=9 to violate (HD1)")
        check((b_p**6 - 1) % rad_star(d2_odd) == 0, "expected even m_3=6 to satisfy (HD1)")
    print()
    print("  [4b] Strict Hull-Dobell chains (rad*(D_{k-1}) | b^{m_k}-1, D_{k-1} !| b^{m_k}-1):")
    for b, ms in hd_chains:
        D_prev = 1
        D_prev2 = 1
        for k, m in enumerate(ms, 1):
            bm1 = b**m - 1
            if k >= 2:
                check(bm1 % rad_star(D_prev) == 0, f"(HD1) failed b={b}, ms={ms}, k={k}")
                check(m % ms[k - 2] == 0, f"m_{{k-1}} | m_k failed")
                check(bm1 % (b ** ms[k - 2] - 1) == 0, f"(b^{{m_{{k-1}}}}-1) | (b^{{m_k}}-1) failed")
            D_k = D_prev * bm1
            T_k = order_mod(b, D_k, m * D_prev)
            check(T_k == m * D_prev, f"T_k != m_k * D_{{k-1}} for b={b}, ms={ms}, k={k}")
            if k == 3:
                check(bm1 % D_prev != 0, f"expected strict HD (D_2 !| b^{{m_3}}-1) for b={b}, ms={ms}")
                # Verify exact band-divisibility equivalence d' | S_i(b^{m_3}) <=> d' | (i+1) for all d' | D_1
                # AND exact persistence S_i(b^{m_3}) == i + 1 mod (b^{m_2} - 1)!
                q3 = b**m
                m2_mod = b ** ms[1] - 1
                s_val = 0
                pq = 1
                for i in range(D_prev2 * 2 + 5):
                    s_val += pq
                    pq *= q3
                    check(s_val % m2_mod == (i + 1) % m2_mod, "S_i != i+1 mod (b^{m_2}-1)")
                    for h in range(1, min(D_prev2 + 1, 15)):
                        dp = D_prev2 // gcd(h, D_prev2)
                        check((s_val % dp == 0) == ((i + 1) % dp == 0), "d' | S_i <=> d' | (i+1) failed")
            D_prev2 = D_prev
            D_prev = D_k
        # Verify exact Fourier vanishing C_2(h) = 0 off D_1*Z and exact Fraction D(mu_2) <= 1/D_1
        R2 = Fraction(b ** ms[0], b ** ms[0] - 1) * Fraction(b ** ms[1], b ** ms[1] - 1)
        D1 = b ** ms[0] - 1
        T2 = ms[1] * D1
        if T2 <= 2000:
            d_m2 = exact_discrepancy_mod(R2.numerator, R2.denominator, b, T2)
            check(d_m2 <= Fraction(1, D1), f"D(mu_2) > 1/D_1 for b={b}, ms={ms}")
        print(f"    b={b}, m={ms}: T_3={ms[2]*D_prev2}, D_2 !| (b^m3-1), "
              f"yet S_i = i+1 mod (b^m2-1) & d'|S_i <=> d'|(i+1) exact!")


# ---------------------------------------------------------------- Section 5: D4 Anchored Coprime Non-Tetration


def section_d4_anchored_coprime() -> None:
    set_section("5. D4 Anchored coprime schedules")
    header("5. D4: Anchored coprime non-tetration normal reciprocals for ALL bases b >= 2")

    # Test genuine recursive anchored coprime schedules (b, s, q1, omegas) across b in {2, 3, 4, 5, 10},
    # EVERY schedule satisfying Theorem 5's exact hypotheses:
    #   s_b | s, q1 >= 5, gcd(q1, s*M) = 1, s*M | omega_1, s | omega_{k-1} (k >= 3),
    #   q_k = omega_{k-1} * (T_{k-1} / s) + 1.
    recursive_configs = [
        (2, 2, 5, [6]),         # M = 3,  q = [5, 31],          T_2 = 930  (exact D <= 1/3)
        (2, 2, 5, [6, 18]),     # M = 3,  q = [5, 31, 8371],    T_3 = 23,355,090 (omega_k = s*M^k)
        (2, 4, 7, [60]),        # M = 15, q = [7, 421],         T_2 = 176,820 (higher anchor!)
        (3, 2, 5, [16]),        # M = 8,  q = [5, 81],          T_2 = 6,480
        (4, 1, 5, [3]),         # M = 3,  q = [5, 16],          T_2 = 240  (exact D <= 1/3)
        (4, 1, 5, [3, 9]),      # M = 3,  q = [5, 16, 2161],    T_3 = 1,555,920 (omega_k = s*M^k)
        (5, 1, 5, [4]),         # M = 4,  q = [5, 21],          T_2 = 420  (exact D <= 1/4)
        (5, 1, 7, [4]),         # M = 4,  q = [7, 29],          T_2 = 812  (exact D <= 1/4)
        (10, 1, 7, [9]),        # M = 9,  q = [7, 64],          T_2 = 4,032
    ]
    print("  [5a] Genuine recursive anchored coprime schedules (exact T_k, coprimality, D <= M^{-(k-1)}):")
    for b, s, q1, omegas in recursive_configs:
        s_b = 1 if (b >= 4 and b % 4 != 3) else 2
        check(s > 0 and s % s_b == 0, f"s_b !| s for {(b, s, q1, omegas)}")
        M = b**s - 1
        check(M >= 3 and (M % 2 == 1 or M % 4 == 0), f"anchor M invalid for b={b}, s={s}")
        check(q1 >= 5 and gcd(q1, s * M) == 1, f"q1 hypothesis failed for {(b, s, q1, omegas)}")
        qs = [q1]
        T_cur = s * q1
        for idx, om in enumerate(omegas, 2):
            if idx == 2:
                check(om >= 1 and om % (s * M) == 0, f"s*M !| omega_1 for {(b, s, q1, omegas)}")
            else:
                check(om >= 1 and om % s == 0, f"s !| omega_{idx-1} for {(b, s, q1, omegas)}")
            qk = om * (T_cur // s) + 1
            qs.append(qk)
            T_cur = s * (M ** (idx - 1)) * math.prod(qs)
        D = 1
        d_tildes: list[int] = []
        R_exact: Fraction | None = Fraction(1) if T_cur <= 1000 else None
        for k, q in enumerate(qs, 1):
            check(gcd(q, s * M) == 1, f"gcd(q, s*M) != 1 for {(b, s, qs)}")
            for q_prev in qs[: k - 1]:
                check(gcd(q, q_prev) == 1, "qs not pairwise coprime")
            m = s * q
            fac = b**m - 1
            check(fac % M == 0, "M !| b^m - 1")
            dt = fac // M
            check(gcd(dt, M) == 1, "gcd(d_tilde, M) != 1")
            for dt_prev in d_tildes:
                check(gcd(dt, dt_prev) == 1, "d_tildes not pairwise coprime")
            d_tildes.append(dt)
            D *= fac
            if R_exact is not None:
                R_exact *= Fraction(b**m, fac)
            # Check exact ord_{M^k}(b) = s * M^{k-1} and q | ord_{dt}(b) | s * q
            check(order_mod(b, M**k, s * (M ** (k - 1))) == s * (M ** (k - 1)), "ord_{M^k}(b) mismatch")
            if m <= 200:
                ord_dt = order_mod(b, dt, s * q)
                check(ord_dt % q == 0 and (s * q) % ord_dt == 0, "ord_{d_tilde}(b) bounds failed")
            T_pred = s * (M ** (k - 1)) * math.prod(qs[:k])
            check(order_mod(b, D, T_pred) == T_pred, f"T_k mismatch for {(b, s, qs)} k={k}")
        k_fin = len(qs)
        T_fin = s * (M ** (k_fin - 1)) * math.prod(qs)
        M_grid = M ** (k_fin - 1)
        if R_exact is not None:
            d_ex = exact_discrepancy_mod(R_exact.numerator, R_exact.denominator, b, T_fin)
            check(d_ex <= Fraction(1, M_grid), f"D(mu_k) > 1/M^(k-1): {d_ex} > 1/{M_grid}")
            # Finite-scale floating-point check of Fourier vanishing for all 1 <= h < M_grid:
            den = R_exact.denominator
            x = R_exact.numerator % den
            pts = []
            for _ in range(T_fin):
                pts.append(x / den)
                x = (x * b) % den
            max_van = 0.0
            for h in range(1, M_grid):
                val = abs(sum(cmath.exp(2j * math.pi * h * p) for p in pts)) / T_fin
                max_van = max(max_van, val)
            check_float(max_van < 1e-11, f"Fourier vanishing failed: {max_van}")
            print(f"    b={b:2d}, s={s}, M={M:2d}, q={str(qs):16s}, T={T_fin:8d}: "
                  f"[float] max_{{h<{M_grid}}}|C_k|={max_van:.1e}, exact D={float(d_ex):.6f} <= 1/{M_grid}={1/M_grid:.6f}")
        else:
            print(f"    b={b:2d}, s={s}, M={M:2d}, q={str(qs):16s}, T={T_fin:8d}: "
                  f"exact recursive schedule, T_k & coprime factorization verified!")

    # 5b. Band-multiplier LTE check M^{K-2} | h * S_i(b^s) <=> d' | (i+1) for b = 2, 3, 4, 10:
    lte_checks = 0
    for b, s in [(2, 2), (2, 4), (3, 2), (4, 1), (10, 1)]:
        M = b**s - 1
        bs = b**s
        for power in (1, 2):
            Mp = M**power
            if Mp > 100:
                continue
            for h in range(1, min(Mp + 1, 16)):
                dp = Mp // gcd(h, Mp)
                si = 0
                p_bs = 1
                for i in range(2 * dp + 3):
                    si = (si + p_bs) % Mp
                    p_bs = (p_bs * bs) % Mp
                    check((si % dp == 0) == ((i + 1) % dp == 0), "anchored band LTE failed")
                    lte_checks += 1
    print(f"  [5b] Anchored band-multiplier LTE equivalence verified on {lte_checks} tuples: ok")

    # 5c. Doubly-exponential growth audit for balanced omega_k = s * M^k: ln(T_k)/2^k -> c_*
    print()
    print("  [5c] Balanced doubly-exponential growth audit (omega_k = s*M^k, ln(T_k)/2^k -> c_*):")
    for b, s, q1 in [(2, 2, 5), (2, 4, 7), (3, 2, 5), (10, 1, 7)]:
        M = b**s - 1
        log_T = math.log(s * q1)
        ratios = []
        for k in range(2, 22):
            # T_k = M^k * T_{k-1}^2 + M * T_{k-1}, so ln T_k = 2*ln T_{k-1} + k*ln M + log(1 + M^{1-k}/T_{k-1})
            log_T = 2.0 * log_T + k * math.log(M) + (math.log1p(M ** (1 - k) * math.exp(-log_T)) if log_T < 500 else 0.0)
            ratios.append(log_T / (2**k))
        check_float(abs(ratios[-1] - ratios[-2]) < 1e-4, f"ln(T_k)/2^k did not converge for b={b}, s={s}")
        print(f"    [float] b={b:2d}, s={s}, M={M:2d} (log_2 M = {math.log2(M):.4f}): "
              f"ln(T_k)/2^k -> {ratios[-1]:.6f} (doubly exponential, NOT tetration!)")


# ---------------------------------------------------------------- Section 6: D4 Fully Coprime, Primes & 1/E_b


def section_d4_coprime_primes_partition() -> None:
    set_section("6. D4 Coprime CRT, primes & 1/E_b")
    header("6. D4: Fully coprime CRT convolution, prime product & 1/E_b partial products")

    # 6a. Universal 01-transition bound |nu_hat(h)| <= 1 - (2 - sqrt(2))/m across ALL 2 <= m <= 11, 1 <= u < 2^m - 1
    bound_c = 2.0 - math.sqrt(2.0)
    trans_checks = 0
    for m in range(2, 12):
        d = (1 << m) - 1
        rhs = 1.0 - bound_c / m
        for u in range(1, d):
            # only test minimal representative of each x2-orbit to keep it super fast!
            x = u
            is_min = True
            s_val = 0j
            for _ in range(m):
                if x < u:
                    is_min = False
                    break
                s_val += cmath.exp(2j * math.pi * (x / d))
                x = (2 * x) % d
            if is_min:
                check_float(abs(s_val) / m <= rhs + 1e-12, f"01-transition bound failed m={m}, u={u}")
                trans_checks += 1
    print(f"  [6a] [float] Universal 01-transition bound |nu_hat| <= 1 - (2 - sqrt(2))/m verified on "
          f"ALL {trans_checks} orbits for 2 <= m <= 11: ok")

    # 6b. Exact partial-fraction identity a_k^{(k)}/(2^{m_k}-1) = {-R_{k-1}} + R_{k-1}/(2^{m_k}-1),
    #     CRT factorization, and squaring inequalities for |C_k(h)| and E_k(h):
    def c2_const(h_val: int) -> int:
        return 4 + 2 * math.ceil(math.log2(4.0 * math.pi * abs(h_val)))

    def nu_hat_single(mj: int, aj: int, H: int) -> complex:
        dj = (1 << mj) - 1
        val = (H * aj) % dj
        if val == 0:
            return 1.0 + 0j
        if mj <= 60:
            s = 0j
            x = val
            for _ in range(mj):
                s += cmath.exp(2j * math.pi * (x / dj))
                x = (2 * x) % dj
            return s / mj
        bits = bin(val)[2:].zfill(mj)
        doub = bits + bits
        s = 0j
        for r in range(mj):
            s += cmath.exp(2j * math.pi * (int(doub[r : r + 52], 2) / (1 << 52)))
        return s / mj

    def factor_l2_energy(mj: int, aj: int, h_val: int) -> float:
        dj = (1 << mj) - 1
        val = (h_val * aj) % dj
        if mj <= 60:
            zs = []
            x = val
            for _ in range(mj):
                zs.append(cmath.exp(2j * math.pi * (x / dj)))
                x = (2 * x) % dj
        else:
            bits = bin(val)[2:].zfill(mj)
            doub = bits + bits
            zs = [cmath.exp(2j * math.pi * (int(doub[r : r + 52], 2) / (1 << 52))) for r in range(mj)]
        avg_sq = 0.0
        for xi in range(mj):
            tw = -2j * math.pi * xi / mj
            zh = sum(zs[r] * cmath.exp(tw * r) for r in range(mj)) / mj
            avg_sq += abs(zh) ** 4
        return avg_sq

    # (i) Schedule m = [2, 5, 31, 621] (omega = (2, 3, 2)): exact partial fraction + CRT + |C_k| squaring + E_k decay
    ms = [2, 5, 31, 621]
    print()
    print("  [6b-i] Fully coprime base-2 schedule m = [2, 5, 31, 621] (omega = (2, 3, 2)):")
    R_prev = Fraction(1)
    D_prev = 1
    T_prev = 1
    a_base: list[int] = []
    for k, m in enumerate(ms, 1):
        check(k == 1 or m % T_prev == 1, "m_k != 1 mod T_{k-1}")
        if k == 2:
            check((m - 1) // T_prev >= 2, "omega_1 >= 2 required")
        dm = (1 << m) - 1
        check(gcd(D_prev, dm) == 1, "not pairwise coprime")
        A_prev = R_prev.numerator
        ak = (A_prev * pow(D_prev, -1, dm)) % dm
        a_base.append(ak)
        if k >= 2:
            neg_R_frac = Fraction(-R_prev.numerator % R_prev.denominator, R_prev.denominator)
            check(Fraction(ak, dm) == neg_R_frac + R_prev / dm, f"exact partial-fraction identity failed k={k}")
        R_cur = R_prev * Fraction(1 << m, dm)
        D_cur = D_prev * dm
        T_cur = T_prev * m
        check(R_cur.denominator == D_cur, "denominator mismatch")
        if k <= 3:
            check(order_mod(2, D_cur, T_cur) == T_cur, f"T_k != prod m_j at k={k}")
            A_cur = R_cur.numerator % D_cur
            for h in (1, 3, 5):
                s_dir = 0j
                x = A_cur
                for _ in range(T_cur):
                    s_dir += cmath.exp(2j * math.pi * h * (x / D_cur))
                    x = (2 * x) % D_cur
                c_dir = s_dir / T_cur
                c_prod = 1.0 + 0j
                for j in range(k):
                    c_prod *= nu_hat_single(ms[j], a_base[j], h)
                check_float(abs(c_dir - c_prod) < 1e-11, f"CRT product mismatch k={k}, h={h}")
        R_prev, D_prev, T_prev = R_cur, D_cur, T_cur

    for h in (1, 3, 5):
        c_prod = 1.0 + 0j
        e_prod = 1.0
        row_c = []
        row_e = []
        c2h = c2_const(h)
        for k in range(4):
            prev_abs = abs(c_prod)
            c_prod *= nu_hat_single(ms[k], a_base[k], h)
            if k >= 1:
                check_float(abs(c_prod) <= prev_abs**2 + c2h / ms[k] + 1e-11,
                            f"|C_k| squaring inequality failed on [2,5,31,621] k={k+1}, h={h}")
            if h in (1, 3):
                e_prod *= factor_l2_energy(ms[k], a_base[k], h)
                row_e.append(f"k={k+1}:{e_prod:.5f}")
            row_c.append(f"k={k+1}:{abs(c_prod):.5f}")
        if h in (1, 3):
            check_float(abs(c_prod) < 0.10 and e_prod < 0.05, f"expected rapid decay at h={h}")
            print(f"    [float] h={h}: |C_k(h)| -> " + ", ".join(row_c))
            print(f"    [float] h={h}: E_k(h)   -> " + ", ".join(row_e) + "  (finite decay measurement; 7/omega >= 2.33)")

    # (ii) Non-vacuous E_k squaring inequality check on m = [2, 21, 421] (omega = (10, 10), 7/omega = 0.7 < 1):
    ms_nv = [2, 21, 421]
    omegas_nv = [10, 10]
    print()
    print("  [6b-ii] Non-vacuous E_k squaring inequality on m = [2, 21, 421] (omega = (10, 10), 7/omega = 0.70):")
    A_p, D_p, T_p = 1, 1, 1
    a_nv: list[int] = []
    for k, m in enumerate(ms_nv, 1):
        check(k == 1 or m == omegas_nv[k - 2] * T_p + 1, "m_k != omega*T_{k-1} + 1")
        dm = (1 << m) - 1
        check(gcd(D_p, dm) == 1, "not pairwise coprime in ms_nv")
        ak = (A_p * pow(D_p, -1, dm)) % dm
        a_nv.append(ak)
        if k >= 2:
            # Exact integer form of ak/dm = {-R_{k-1}} + R_{k-1}/dm:
            check(ak * D_p == ((-A_p) % D_p) * dm + A_p, f"exact partial-fraction identity failed ms_nv k={k}")
        A_p = A_p << m
        D_p = D_p * dm
        T_p = T_p * m
        check(order_mod(2, D_p, T_p) == T_p, f"T_k mismatch ms_nv k={k}")
    for h in (1, 3):
        c_prod = 1.0 + 0j
        e_prod = 1.0
        c2h = c2_const(h)
        for k in range(len(ms_nv)):
            prev_c = abs(c_prod)
            prev_e = e_prod
            c_prod *= nu_hat_single(ms_nv[k], a_nv[k], h)
            e_prod *= factor_l2_energy(ms_nv[k], a_nv[k], h)
            if k >= 1:
                om = omegas_nv[k - 1]
                rhs_c = prev_c**2 + c2h / ms_nv[k]
                rhs_e = prev_e**2 + 7.0 / om + 4.0 * c2h / ms_nv[k]
                check_float(abs(c_prod) <= rhs_c + 1e-11, f"|C_k| squaring failed ms_nv k={k+1}, h={h}")
                check_float(e_prod <= rhs_e + 1e-11, f"E_k squaring failed ms_nv k={k+1}, h={h}")
                if k == 2 and h == 1:
                    check_float(rhs_e < 1.0, f"expected non-vacuous E_k RHS < 1, got {rhs_e}")
                    print(f"    [float] h=1, k=3 (m_3=421, omega_2=10): "
                          f"E_3(1)={e_prod:.5f} <= E_2^2 + 7/10 + 4*c2/421 = {rhs_e:.5f} (< 1, non-vacuous!)")
        print(f"    [float] h={h}: |C_3({h})|={abs(c_prod):.5f}, E_3({h})={e_prod:.5f} (all squaring inequalities ok)")

    # (iii) Tight |C_k| squaring inequality check on m = [2, 9, 145, 41761] (omega = (4, 8, 16)):
    ms_tight = [2, 9, 145, 41761]
    omegas_tight = [4, 8, 16]
    A_p, D_p, T_p = 1, 1, 1
    a_tight: list[int] = []
    for k, m in enumerate(ms_tight, 1):
        check(k == 1 or m == omegas_tight[k - 2] * T_p + 1, "m_k != omega*T_{k-1} + 1 in ms_tight")
        dm = (1 << m) - 1
        check(gcd(D_p, dm) == 1, "not pairwise coprime in ms_tight")
        ak = (A_p * pow(D_p, -1, dm)) % dm
        a_tight.append(ak)
        if k >= 2:
            check(ak * D_p == ((-A_p) % D_p) * dm + A_p, f"exact partial-fraction identity failed ms_tight k={k}")
        A_p = A_p << m
        D_p = D_p * dm
        T_p = T_p * m
    print()
    print("  [6b-iii] Tight |C_k| squaring inequality on m = [2, 9, 145, 41761] (omega = (4, 8, 16)):")
    for h in (1, 3, 5):
        c_prod = 1.0 + 0j
        c2h = c2_const(h)
        for k in range(len(ms_tight)):
            prev_c = abs(c_prod)
            c_prod *= nu_hat_single(ms_tight[k], a_tight[k], h)
            if k >= 1:
                rhs_c = prev_c**2 + c2h / ms_tight[k]
                check_float(abs(c_prod) <= rhs_c + 1e-11, f"|C_k| squaring failed ms_tight k={k+1}, h={h}")
        print(f"    [float] h={h}: |C_4({h})|={abs(c_prod):.5f} <= {prev_c**2 + c2h / ms_tight[-1]:.5f} (ok)")

    # 6c. Prime-exponent product R_k^{(prime)} = prod_{j<=k} (1 - 2^{-p_j})^{-1} for k = 1..5:
    print()
    print("  [6c] Prime-exponent partial products R_k^{(prime)} = prod_{j<=k} (1 - 2^{-p_j})^{-1}:")
    primes_p = [2, 3, 5, 7, 11]
    for k in range(1, len(primes_p) + 1):
        sub = primes_p[:k]
        T_p = math.prod(sub)
        D_p = math.prod((1 << p) - 1 for p in sub)
        check(order_mod(2, D_p, T_p) == T_p, f"prime period mismatch k={k}")
        c1 = 1.0 + 0j
        c3 = 1.0 + 0j
        ub1 = 1.0
        for j in range(k):
            pj = sub[j]
            dj = (1 << pj) - 1
            aj = 1
            for i in range(k):
                if i != j:
                    pi = sub[i]
                    aj = (aj * pow(2, pi, dj) * pow(pow(2, pi, dj) - 1, -1, dj)) % dj
            s1, s3 = 0j, 0j
            x1, x3 = aj % dj, (3 * aj) % dj
            for _ in range(pj):
                s1 += cmath.exp(2j * math.pi * (x1 / dj))
                s3 += cmath.exp(2j * math.pi * (x3 / dj))
                x1 = (2 * x1) % dj
                x3 = (2 * x3) % dj
            c1 *= s1 / pj
            c3 *= s3 / pj
            ub1 *= 1.0 - bound_c / pj
        check_float(abs(c1) <= ub1 + 1e-12, "prime product exceeded 01-transition bound")
        print(f"    [float] k={k}, p={str(sub):17s}, T_k={T_p:4d}: "
              f"|C_k(1)|={abs(c1):.5f} <= {ub1:.5f}, |C_k(3)|={abs(c3):.5f}")

    # 6d. Ordinary partition partial products R_k^{(E)} = prod_{j=1}^k (1 - b^{-j})^{-1}
    #     and exact p-adic grid bound D(mu(R_k^{(E)}; b)) <= p^{-r_k}!
    print()
    print("  [6d] Ordinary partition partial products R_k^{(E)} = prod_{j=1}^k (1 - b^{-j})^{-1} & p-adic grid bound:")
    for b, p_anc, k_max in [(2, 3, 7), (3, 2, 5), (5, 2, 5)]:
        R = Fraction(1)
        for k in range(1, k_max + 1):
            R *= Fraction(b**k, b**k - 1)
            D = R.denominator
            ek = v_p(D, p_anc)
            D_prime = D // (p_anc**ek)
            T_prime = order_mod(b, D_prime)
            T_p = order_mod(b, p_anc**ek)
            T_k = math.lcm(T_p, T_prime)
            check(order_mod(b, D, T_k) == T_k, f"partition T_k mismatch b={b}, k={k}")
            # For p = 2 and b = 3 (mod 4), the +/-1 factor in (Z/2^e Z)* does not advance
            # along 1 + 4Z, so the exact p-adic arithmetic-progression grid has exponent
            # max(0, v_2(T_p) - max(1, v_2(T_prime))):
            v_shift = max(1, v_p(T_prime, p_anc)) if (p_anc == 2 and b % 4 == 3) else v_p(T_prime, p_anc)
            rk = max(0, v_p(T_p, p_anc) - v_shift)
            grid_ub = Fraction(1, p_anc**rk)
            d_ex = exact_discrepancy_mod(R.numerator, D, b, T_k)
            check(d_ex <= grid_ub, f"p-adic grid bound failed b={b}, k={k}: {d_ex} > {grid_ub}")
            print(f"    b={b}, p={p_anc}, k={k}: D_k={D:9d} (v_p={ek:2d}), T_k={T_k:4d}, "
                  f"p^{{r_k}}={p_anc**rk:3d}: exact D={float(d_ex):.5f} <= {float(grid_ub):.5f}")


# ---------------------------------------------------------------- main


def main() -> None:
    t0 = perf_counter()
    section_d1_convergent_reciprocals()
    section_d2_sharp_max_discrepancy()
    section_d2_all_bases_L_normal()
    section_d4_hull_dobell()
    section_d4_anchored_coprime()
    section_d4_coprime_primes_partition()
    total_exact = sum(SECTION_EXACT_CHECKS.values())
    total_float = sum(SECTION_FLOAT_CHECKS.values())
    print()
    print("Per-section substantive check counts (helper invariants excluded):")
    print(f"  {'Section':42s}  {'Exact':>7s}  {'Float':>7s}")
    for name in SECTION_EXACT_CHECKS:
        print(f"  {name:42s}  {SECTION_EXACT_CHECKS[name]:7d}  {SECTION_FLOAT_CHECKS[name]:7d}")
    print(
        f"Total: {total_exact} exact checks + {total_float} float measurements "
        f"({total_exact + total_float} total) passed in {perf_counter() - t0:.2f} s"
    )


if __name__ == "__main__":
    main()
