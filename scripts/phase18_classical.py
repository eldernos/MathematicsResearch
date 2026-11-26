#!/usr/bin/env python3
"""Exact arithmetic verification for Phase 18 Track F (F1-F5):
classical constant synthesis, positive dyadic groupings, delayed retirement,
complement denominator persistence, and named targets (pi, e, Li_s, zeta(3), algebraic)."""

from __future__ import annotations

import math
from decimal import Decimal, getcontext
from fractions import Fraction


def v_p(n: int, p: int) -> int:
    if n == 0:
        raise ValueError("v_p(0)")
    n = abs(n)
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def odd_part(n: int) -> int:
    n = abs(n)
    while n > 0 and (n & 1) == 0:
        n >>= 1
    return n


def mult_order(a: int, m: int) -> int:
    if m == 1:
        return 1
    assert math.gcd(a, m) == 1
    cur = a % m
    k = 1
    while cur != 1:
        cur = (cur * a) % m
        k += 1
    return k


def primes_up_to(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, math.isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i : n + 1 : i] = b"\x00" * ((n - i * i) // i + 1)
    return [i for i, v in enumerate(sieve) if v]


def factor_odd_primes(n: int) -> set[int]:
    n = odd_part(n)
    ps: set[int] = set()
    d = 3
    while d * d <= n:
        if n % d == 0:
            ps.add(d)
            while n % d == 0:
                n //= d
        d += 2
    if n > 1:
        ps.add(n)
    return ps


def verify_f1() -> None:
    print("=== F1: Exact periodicity & positive dyadic groupings on odd d-rays ===")
    # 1. Verify exact preperiod a = v_2(ord_d(2)) and minimal eventual period P_d = lcm(t, ord_{u_0}(2))
    for d in range(3, 200, 2):
        t = mult_order(2, d)
        a = v_p(t, 2)
        u = odd_part(t)
        u0 = u // math.gcd(u, d)
        p_d = math.lcm(t, mult_order(2, u0))

        def r(j: int) -> int:
            e = d * (1 << j) + j
            return pow(2, -e, d)

        # Periodicity from a onward
        for j in range(a, a + 2 * p_d + 5):
            assert r(j + p_d) == r(j), f"period failed d={d}, j={j}"
        # Exact preperiod: if a > 0, r(a-1 + p_d) != r(a-1)
        if a > 0:
            assert r(a - 1 + p_d) != r(a - 1), f"preperiod not sharp d={d}"
        # Exact minimal period: no proper divisor of p_d works on [a, a + p_d)
        for div in range(1, p_d):
            if p_d % div == 0:
                if all(r(j + div) == r(j) for j in range(a, a + p_d)):
                    raise AssertionError(f"non-minimal period d={d}, div={div}, p_d={p_d}")
    print("Verified exact preperiod a=v_2(ord_d(2)) and minimal period P_d for all odd d in [3, 199].")

    # 2. Check minimal single-ray dyadic group containing j=0 for small odd d
    print("\nSmall odd d minimal-span single-ray dyadic groups containing j=0:")
    print(f"{'d':>4} {'t':>4} {'a':>2} {'P_d':>4} {'K_min':>5} {'|G|':>4} {'G':>20} {'R=e(d,K)':>10} {'exact_den_ok':>12}")
    for d in [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 41]:
        t = mult_order(2, d)
        a = v_p(t, 2)
        u = odd_part(t)
        u0 = u // math.gcd(u, d)
        p_d = math.lcm(t, mult_order(2, u0))

        # BFS/DP over j = 0, 1, ..., K to find smallest K with a subset containing 0 and K summing to 0 mod d
        # Track reachable residues mod d with minimal subset size
        r0 = pow(2, -d, d)
        dp: dict[int, tuple[int, ...]] = {r0: (0,)}
        found = None
        for k in range(1, 35):
            rk = pow(2, -(d * (1 << k) + k), d)
            # Check if -rk mod d is already in dp
            need = (-rk) % d
            if need in dp:
                found = dp[need] + (k,)
                break
            new_dp = dict(dp)
            for res, grp in dp.items():
                nres = (res + rk) % d
                ngrp = grp + (k,)
                if nres not in new_dp or len(ngrp) < len(new_dp[nres]):
                    new_dp[nres] = ngrp
            dp = new_dp
        assert found is not None, f"no group found for d={d}"
        k_min = found[-1]
        r_exp = d * (1 << k_min) + k_min
        # Exact Fraction verification when exponent <= 2000
        ok_str = "mod-checked"
        if r_exp <= 2000:
            s = sum(Fraction(1, d * (1 << (d * (1 << j) + j))) for j in found)
            assert odd_part(s.denominator) == 1
            assert v_p(s.denominator, 2) == r_exp
            ok_str = f"2^{r_exp}"
        else:
            # Verify modularly: sum 2^{e(d,K) - e(d,j)} == 0 mod d and is odd
            tot_mod = sum(pow(2, r_exp - (d * (1 << j) + j), d) for j in found) % d
            assert tot_mod == 0
            ok_str = "exact-mod"
        print(f"{d:>4} {t:>4} {a:>2} {p_d:>4} {k_min:>5} {len(found):>4} {str(list(found)):>20} {r_exp:>10} {ok_str:>12}")

    # 3. Verify explicit 2-term partition for d=3: {0,2}, {1,4}, {3,6}, {5,8}, ...
    groups_3 = [(0, 2)] + [(2 * k - 1, 2 * k + 2) for k in range(1, 8)]
    used = sorted(x for g in groups_3 for x in g)
    assert used[:12] == list(range(12))
    for g in groups_3[:5]:
        s = sum(Fraction(1, 3 * (1 << (3 * (1 << j) + j))) for j in g)
        assert odd_part(s.denominator) == 1
        assert v_p(s.denominator, 2) == 3 * (1 << g[-1]) + g[-1]
    print("\nVerified explicit 2-term dyadic partition on d=3 ray.")


def verify_f2() -> None:
    print("\n=== F2: Delayed-retirement obstruction & cross-ray 2-adic drop ===")
    # 1. Exact classification of primes with K_min = 1, 2, 3 via B(G) = sum_{j in G} 2^{2^K - 2^j + K - j}
    for K in [1, 2, 3, 4]:
        primes_at_K: set[int] = set()
        details: list[tuple[list[int], int, list[int]]] = []
        for mask in range(1 << (K - 1)):
            G = [0] + [j for j in range(1, K) if (mask >> (j - 1)) & 1] + [K]
            B = sum(1 << ((1 << K) - (1 << j) + (K - j)) for j in G)
            assert B < (2 * (1 << ((1 << K) + K))) // 3 + 1
            ps = sorted(factor_odd_primes(B)) if K <= 3 else []
            if K <= 3:
                primes_at_K.update(ps)
                details.append((G, B, ps))
        if K <= 3:
            print(f"K={K}: subsets & odd prime divisors of B(G):")
            for G, B, ps in details:
                print(f"  G={G}, B(G)={B}, odd primes={ps}")
            print(f"  All primes admitting K={K}: {sorted(primes_at_K)}")

    # 2. Verify worst-case and typical-prime unfinished fraction at N = 500, 2000, 10000
    # Precompute for K=1..7 all primes dividing B(G) (for small K <= 5 exact; for larger K, use exact B(G) mod p)
    print("\nFraction of odd primes p <= N whose minimal single-ray dyadic group finishes by Taylor index N (p*2^K <= N):")
    for N in [200, 1000, 5000]:
        ps = [p for p in primes_up_to(N) if p >= 3]
        finished = 0
        for p in ps:
            # Largest K with p * 2^K <= N
            Kmax = (N // p).bit_length() - 1
            if Kmax < 1:
                continue
            # Check if any subset G <= {0..Kmax} containing 0 and some k >= 1 has sum 2^{-(p*2^j + j)} = 0 mod p
            # Note modulo p, r_p(j) = 2^{-(2^j + j)} mod p since 2^p = 2 mod p!
            r0 = pow(2, -1, p)
            reach = {r0}
            ok = False
            for k in range(1, Kmax + 1):
                rk = pow(2, -((1 << k) + k), p)
                if ((-rk) % p) in reach:
                    ok = True
                    break
                reach = reach | {(x + rk) % p for x in reach}
            if ok:
                finished += 1
        frac_open = 1.0 - finished / len(ps)
        print(f"  N={N:>5}: odd primes={len(ps):>4}, finished={finished:>3}, open={len(ps)-finished:>4} ({100*frac_open:.2f}% open)")

    # 3. Cross-ray 2-adic drop counterexamples!
    g1 = [5, 8, 10]
    s1 = sum(Fraction(1, m * (1 << m)) for m in g1)
    emax1 = max(m + v_p(m, 2) for m in g1)
    ered1 = v_p(s1.denominator, 2)
    assert odd_part(s1.denominator) == 1 and s1 == Fraction(7, 1024)
    assert emax1 == 11 and ered1 == 10
    print(f"\nCross-ray 2-adic drop example 1: G={g1}, S(G)={s1}, E_max={emax1}, e_red={ered1}, drop={emax1 - ered1}")

    # Search for a cross-ray positive dyadic group with drop >= 2!
    # Idea: combine a single-ray dyadic group G_d ending at E = d*2^K + K with a second dyadic group ending at E (e.g. d=1 term 2^b with 2^b + b = E, or another single-ray group)!
    # Check E = 2^b + b for b in 3..14: find odd d >= 3, K >= 1 with d*2^K + K = E and a dyadic group G_d on ray d with max G_d = K!
    best_drop = (1, g1, s1, emax1, ered1)
    for b in range(3, 12):
        E = (1 << b) + b
        for K in range(1, b):
            num = E - K
            if num > 0 and num % (1 << K) == 0:
                d = num // (1 << K)
                if d >= 3 and d % 2 == 1:
                    # Find all dyadic groups on ray d with max = K (small K <= 10)
                    # Check subsets of {0..K-1} + {K}
                    if K <= 10:
                        for mask in range(1, 1 << K):
                            G_idx = [j for j in range(K) if (mask >> j) & 1] + [K]
                            M_mod = sum(pow(2, E - (d * (1 << j) + j), d) for j in G_idx) % d
                            if M_mod == 0:
                                # Exact numerator A = M(G_idx) // d
                                M_val = sum(1 << (E - (d * (1 << j) + j)) for j in G_idx)
                                assert M_val % d == 0
                                A = M_val // d
                                # Add term m = 2^b (contributes 1/2^E): numerator becomes A + 1!
                                drop = v_p(A + 1, 2)
                                if drop > best_drop[0]:
                                    ms = sorted([d * (1 << j) for j in G_idx] + [1 << b])
                                    best_drop = (drop, ms, Fraction(A + 1, 1 << E), E, E - drop)
    drop, ms, sval, emax, ered = best_drop
    assert odd_part(sval.denominator) == 1 and v_p(sval.denominator, 2) == ered
    # Direct recomputation from ms
    s_direct = sum(Fraction(1, m * (1 << m)) for m in ms)
    assert s_direct == sval
    print(f"Cross-ray 2-adic drop example 2: G={ms}, E_max={emax}, e_red={ered}, drop={drop} (S(G)={sval.numerator}/2^{ered})")

    # 4. Strategy A vs Strategy B at N = 32, 64, 128
    print("\nStrategy A (completed groups only) vs Strategy B (Taylor prefix) at cutoff N:")
    for N in [32, 64, 128]:
        R_N = sum(Fraction(1 << (N - m), m) for m in range(1, N + 1))
        q_odd = odd_part(R_N.denominator)
        # Every prime p in (N/2, N] is omitted from ANY completed-group sum C_N
        p_omit = [p for p in primes_up_to(N) if p > N // 2]
        err_lb = sum(Fraction(1 << (N - p), p) for p in p_omit)
        print(f"  N={N:>3}: log(q_odd(R_N))/N = {math.log(q_odd)/N:.4f}, log2(2^N(ln2 - C_N)) >= {math.log2(float(err_lb)):.2f} (from {len(p_omit)} open primes in (N/2,N])")


def verify_f3_f4() -> None:
    print("\n=== F3 & F4: Complement denominator persistence & horizontal dyadic rays ===")
    # Theorem F4.2: B_P = ln 2 - A_P has exact odd-denominator rate 1 for P = {2,3} and P = {2,3,5}
    for P_name, P in [("{2,3}", (2, 3)), ("{2,3,5}", (2, 3, 5))]:
        def is_smooth(m: int) -> bool:
            x = m
            for p in P:
                while x % p == 0:
                    x //= p
            return x == 1

        print(f"Complement B_P for P={P_name}:")
        for N in [64, 128, 256]:
            BP_N = sum(Fraction(1 << (N - m), m) for m in range(1, N + 1) if not is_smooth(m))
            q_odd = odd_part(BP_N.denominator)
            # Check Frobenius congruence for every prime p > max(P) with p^2 > N
            mismatches = 0
            for p in primes_up_to(N):
                if p > max(P) and p * p > N:
                    v = N // p
                    # P_v = sum_{l=1}^v 1/(l * 2^l)
                    Pv = sum(Fraction(1, l * (1 << l)) for l in range(1, v + 1))
                    # Residue of p * BP_N mod p should equal 2^N * Pv mod p
                    pred_nz = (Pv.numerator % p) != 0
                    actual_div = (q_odd % p) == 0
                    if pred_nz != actual_div:
                        mismatches += 1
            assert mismatches == 0
            print(f"  N={N:>3}: log(q_odd(2^N B_P(N)))/N = {math.log(q_odd)/N:.5f}, Frobenius mismatches = {mismatches}")

    # Include the same dyadic-exponent cutoff as the construction. Missing
    # terms through m=140 are exact; the remaining Taylor tail is geometric.
    total = Fraction()
    for d in range(1, 141, 2):
        j = 0
        while (exponent := d * (1 << j) + j) <= 140:
            total += Fraction(1, d * (1 << exponent))
            j += 1
    taylor = sum(Fraction(1, m * 2**m) for m in range(1, 141))
    error_upper = taylor - total + Fraction(1, 141 * 2**140)
    assert 0 <= taylor-total and error_upper < Fraction(1, 10**38)
    print("Horizontal dyadic-ray truncation has certified error below 10^-38.")


def atan_inverse_bounds(a, terms):
    """Bracket arctan(1/a) between consecutive alternating rational sums."""
    value = sum(Fraction((-1)**j, (2*j+1) * a**(2*j+1)) for j in range(terms))
    adjacent = value + Fraction((-1)**terms, (2*terms+1) * a**(2*terms+1))
    return min(value, adjacent), max(value, adjacent)


def ceil_log2_rational(x):
    exponent = x.numerator.bit_length() - x.denominator.bit_length()
    return exponent + (Fraction(2)**exponent < x)


def chebyshev_even_poly(two_d: int) -> list[int]:
    """Return coefficients c_k of T_{2D}(x) = sum_{k=0}^{D} c_k x^{2k}."""
    assert two_d % 2 == 0
    # Standard Chebyshev T_n(x): T_0 = 1, T_1 = x, T_{n+1} = 2x T_n - T_{n-1}
    t_prev = [1]
    t_curr = [0, 1]
    if two_d == 0:
        return [1]
    for _ in range(2, two_d + 1):
        t_next = [0] * (len(t_curr) + 1)
        for i, c in enumerate(t_curr):
            t_next[i + 1] += 2 * c
        for i, c in enumerate(t_prev):
            t_next[i] -= c
        t_prev, t_curr = t_curr, t_next
    # Verify odd coefficients are 0
    for i in range(1, len(t_curr), 2):
        assert t_curr[i] == 0
    return [t_curr[2 * k] for k in range(two_d // 2 + 1)]


def poly_div_even_quad(even_coeffs: list[int], a: int) -> tuple[list[int], int]:
    """Divide a polynomial in y = x² by y + a², returning quotient and remainder."""
    # Synthetic division by y - (-a^2)
    a2 = a * a
    n = len(even_coeffs) - 1
    q = [0] * n
    rem = even_coeffs[n]
    for k in range(n - 1, -1, -1):
        q[k] = rem
        rem = even_coeffs[k] - a2 * rem
    return q, rem


def legendre_grid(degree, poles):
    """First-crossing threshold and exact moment for the even Legendre kernel."""
    n = 2 * degree
    # The coefficient of x^(n-2j) in 2^n P_n(x), in increasing powers of y=x².
    coefficients = [(-1)**j * math.comb(n, j) * math.comb(2*n-2*j, n)
                    for j in range(degree, -1, -1)]
    moment = Fraction()
    values = []
    for weight, a in poles:
        quotient, remainder = poly_div_even_quad(coefficients, a)
        values.append(abs(remainder))
        integral = sum(Fraction(c, 2*j+1) for j, c in enumerate(quotient))
        moment += Fraction(weight*a, remainder) * integral
    threshold = min(values).bit_length() - 1 - n
    grid = math.lcm(*range(1, n, 2))
    return threshold, moment, grid


def verify_legendre_windows():
    """Check every shift through 256 and three larger shifts against rational bounds."""
    five_low, five_high = atan_inverse_bounds(5, 425)
    large_low, large_high = atan_inverse_bounds(239, 145)
    pi_low = 16*five_low - 4*large_high
    pi_high = 16*five_high - 4*large_low
    shifts = [*range(1, 257), 512, 600, 800]
    for poles in (((16, 5), (-4, 239)), ((24, 8), (8, 57), (4, 239))):
        degree = 0
        threshold = -1
        for n in shifts:
            while threshold < n:
                degree += 1
                threshold, moment, grid = legendre_grid(degree, poles)
            shift = 1 << n
            model = Fraction(-round(grid*shift*moment), grid)
            assert model.denominator % 2 == 1 and grid % model.denominator == 0
            error_upper = max(abs(shift*pi_low-model), abs(shift*pi_high-model))
            # The absolute Poisson-tail prefactor 8r/((1-r²)(1-r)) is < 1
            # for a >= 2. Also r < (2a)^-2.
            bound = Fraction(1, 2*grid) + sum(
                Fraction(abs(c)*a, (2*a)**(2*degree)) for c, a in poles)
            assert error_upper <= bound, (poles, degree, n)
            # Certify agreement with nearest-grid rounding by bracketing π
            # on both sides. This is an observed property of these cutoffs.
            assert round(grid*shift*pi_low) == grid*model == round(grid*shift*pi_high)
            if n == 600:
                q = model.denominator
                primes = primes_up_to(2*degree)
                # q divides the odd lcm. Every prime factor of phi(q) is <= 2D.
                order = q
                for p in primes:
                    if q % p == 0:
                        order = order // p * (p - 1)
                for p in primes:
                    while order % p == 0 and pow(2, order//p, q) == 1:
                        order //= p
                assert pow(2, order, q) == 1
                assert all(pow(2, order//p, q) != 1 for p in primes if order % p == 0)
                print(f"Legendre shift 600 with smallest pole {min(a for _, a in poles)}: "
                      f"exact period {order}")
            if n in (256, 600, 800):
                print(f"Legendre a_min={min(a for _, a in poles)}, shift={n}, "
                      f"D={degree}, denominator bits={model.denominator.bit_length()}, "
                      f"certified accuracy bits={-ceil_log2_rational(error_upper)}")
    print(f"Verified rational pi enclosures at {2*len(shifts)} Legendre-grid shifts.")


def verify_f5() -> None:
    print("\n=== F5: Named other classical constants (pi, e, Li_s, zeta(3), algebraic) ===")

    # 1. pi: Standard BBP rate (3/2 per binary bit), Bellard rate, and single-prime non-cancellation
    print("1a. Standard BBP formula for pi (shifted by 16^M = 2^{4M}, N=4M binary bits):")
    for M in [16, 32, 64, 128]:
        N = 4 * M
        Y = Fraction(0)
        for k in range(M + 1):
            pow16 = 1 << (4 * (M - k))
            Y += pow16 * (Fraction(4, 8 * k + 1) - Fraction(2, 8 * k + 4) - Fraction(1, 8 * k + 5) - Fraction(1, 8 * k + 6))
        q_full = Y.denominator
        q_odd = odd_part(q_full)
        print(f"  M={M:>3} (N={N:>3}): log(q_N)/N = {math.log(q_full)/N:.5f}, log(q_odd)/N = {math.log(q_odd)/N:.5f} (theory: 1.50000)")

    # Enumerate the four literal BBP terms before reducing any denominator.
    # The second occurrence has k=(p-1)/2, the largest possible k.
    for p in primes_up_to(500):
        if p == 2:
            continue
        terms = [Fraction(weight, (8*k + a) * 16**k)
                 for k in range((p-1)//2 + 1)
                 for a, weight in ((1, 4), (4, -2), (5, -1), (6, -1))
                 if odd_part(8*k + a) == p]
        assert len(terms) == 2 and sum(terms).denominator % p == 0, (p, terms)
        if p == 3:
            assert sum(terms) == Fraction(-17, 96)
    print("Both original BBP slots retain each odd prime through 500.")

    print("1b. Bellard formula for pi (shifted by 2^{10M}, N=10M binary bits):")
    for M in [12, 24, 48]:
        N = 10 * M
        Y = Fraction(0)
        for k in range(M + 1):
            sgn = -1 if (k & 1) else 1
            pow2 = 1 << (10 * (M - k))
            term = (
                Fraction(-32, 4 * k + 1)
                - Fraction(1, 4 * k + 3)
                + Fraction(256, 10 * k + 1)
                - Fraction(64, 10 * k + 3)
                - Fraction(4, 10 * k + 5)
                - Fraction(4, 10 * k + 7)
                + Fraction(1, 10 * k + 9)
            )
            Y += sgn * pow2 * term
        Y /= 64
        q_full = Y.denominator
        q_odd = odd_part(q_full)
        print(f"  M={M:>2} (N={N:>3}): log(q_N)/N = {math.log(q_full)/N:.5f}, log(q_odd)/N = {math.log(q_odd)/N:.5f}")

    # Exact reference enclosure from Machin's identity. The separate
    # rational approximants below are constructed without this reference.
    five_low, five_high = atan_inverse_bounds(5, 260)
    large_low, large_high = atan_inverse_bounds(239, 100)
    pi_low = 16*five_low - 4*large_high
    pi_high = 16*five_high - 4*large_low
    getcontext().prec = 500  # Only for the later illustrative decimal comparisons.
    print("1c. pi-free rounded Chebyshev-pole integrals (even T_{2D}(x), odd denominators only):")
    pi_families = [
        ("Single pole 4*atan(1)", [(4, 1)], math.log(2) / math.log(1 + math.sqrt(2))),
        ("Machin 16*atan(1/5)-4*atan(1/239)", [(16, 5), (-4, 239)], math.log(2) / math.log(5 + math.sqrt(26))),
        ("Stormer 24*atan(1/8)+8*atan(1/57)+4*atan(1/239)", [(24, 8), (8, 57), (4, 239)], math.log(2) / math.log(8 + math.sqrt(65))),
    ]
    for name, poles, lim_rate in pi_families:
        print(f"  Family: {name} (asymptotic rate <= {lim_rate:.6f})")
        for D in [40, 80, 120]:
            ev = chebyshev_even_poly(2 * D)
            # Accumulate R_tot(y) = sum (c_i a_i / rem_i) * q_i(y)
            r_tot = [Fraction(0)] * D
            min_abs_rem = None
            for c_i, a_i in poles:
                q_i, rem_i = poly_div_even_quad(ev, a_i)
                assert rem_i != 0
                if min_abs_rem is None or abs(rem_i) < min_abs_rem:
                    min_abs_rem = abs(rem_i)
                scale = Fraction(c_i * a_i, rem_i)
                for k in range(D):
                    r_tot[k] += scale * q_i[k]
            assert min_abs_rem is not None
            e = min_abs_rem.bit_length() - 1
            # Round 2^e * r_tot[k] to nearest integer (purely polynomial, NO knowledge of pi!)
            Q_int = []
            for k in range(D):
                val = r_tot[k] * (1 << e)
                # nearest integer
                num, den = val.numerator, val.denominator
                q_k = (2 * num + den) // (2 * den) if num >= 0 else -((-2 * num + den) // (2 * den))
                Q_int.append(q_k)
            # w = ceil(log2(D * (ln(D) + 1))) + 2
            # Integral comparison gives H_D - 1 <= log D <= H_(D-1).
            harmonic = sum(Fraction(1, j) for j in range(1, D+1))
            w = ceil_log2_rational(D*harmonic) + 2
            assert w == ceil_log2_rational(D*(harmonic + 1) - 1) + 2
            N = e - w
            # Y_N = -2^{-w} * sum_{k=0}^{D-1} Q_int[k] / (2k + 1)
            Y_N = -Fraction(1, 1 << w) * sum(Fraction(Q_int[k], 2 * k + 1) for k in range(D))
            # Verify denominator divides 2^w * lcm(1, 3, ..., 2D-1)
            lcm_odd = math.lcm(*range(1, 2 * D, 2))
            assert (Y_N * (1 << w) * lcm_odd).denominator == 1
            q_N = Y_N.denominator
            q_odd = odd_part(q_N)
            error_upper = max(abs((1 << N)*pi_low-Y_N), abs((1 << N)*pi_high-Y_N))
            assert error_upper < Fraction(1, N)
            log2_err = math.log2(float(error_upper))  # Display only.
            print(f"    D={D:>3}, N={N:>4}, w={w:>2}: log(q_N)/N={math.log(q_N)/N:.5f}, odd={math.log(q_odd)/N:.5f}, log2|err|={log2_err:.2f}")

    # 2. e: Theorem F5.3 (impossibility of finite positive dyadic factorial groups) + rates
    print("\n2. e: Factorial grouping impossibility (Theorem F5.3) & shifted rates:")
    # Exhaustive check for M <= 16 (all 2^16 nonempty subsets with max >= 3)
    for M in range(3, 17):
        # Verify our 2-case proof explicitly: either M has odd prime p|M, or M=2^r and odd prime p|(M-1)
        if odd_part(M) > 1:
            p = min(factor_odd_primes(M))
            assert v_p(math.factorial(M), p) > v_p(math.factorial(M - 1), p)
        else:
            p = min(factor_odd_primes(M - 1))
            assert p >= 3 and (M - 1) % p == 0 and M % p != 0
    # Brute force all subsets of {0..15} with max >= 3 (65528 subsets)
    f_vals = [Fraction(1, math.factorial(k)) for k in range(16)]
    for mask in range(8, 1 << 16):
        s = Fraction(0)
        for k in range(16):
            if (mask >> k) & 1:
                s += f_vals[k]
        assert odd_part(s.denominator) > 1, f"found dyadic factorial group! mask={mask}"
    print("  Exhaustively verified: ZERO of 65,528 subsets of {0..15} with max >= 3 sum to a dyadic rational.")
    # Verify Taylor shifted rate -> ln 2 and diagonal Pade shifted rate -> (ln 2)/2
    e_dec = Decimal(1).exp()
    print("  e Taylor shifted prefixes (2^N * sum_{k=0}^n 1/k! with n! >= 2^N):")
    for N in [100, 250, 500]:
        n = 1
        fact = 1
        while fact < (1 << N):
            n += 1
            fact *= n
        A_n = sum(fact // math.factorial(k) for k in range(n + 1))
        Y = Fraction(A_n << N, fact)
        q_N = Y.denominator
        print(f"    N={N:>3} (n={n:>3}): log(q_N)/N = {math.log(q_N)/N:.5f} (ln 2 = {math.log(2):.5f})")

    print("  e diagonal Pade approximants C_m/B_m:")
    for m in [15, 30, 50]:
        B_m = sum(math.comb(m, j) * math.factorial(2 * m - j) // math.factorial(m) for j in range(m + 1))
        C_m = sum((-1) ** j * math.comb(m, j) * math.factorial(2 * m - j) // math.factorial(m) for j in range(m + 1))
        # Wait: C_m = sum_{l=0}^{2m} P^{(l)}(1) / m! where P(t) = t^m (1-t)^m -> P(1-t) = P(t), so P^{(l)}(1) = (-1)^l P^{(l)}(0)
        # Check sign: int_0^1 e^{1-t} P(t) dt = e * sum P^{(l)}(0) - sum P^{(l)}(1)
        # P(t) = sum_{j=0}^m (-1)^j comb(m,j) t^{m+j}, so P^{(m+j)}(0) = (-1)^j comb(m,j) (m+j)!
        # Wait: let's compute exact coefficients of e*B_m - C_m via integration by parts!
        B_m = sum((-1) ** j * math.comb(m, j) * math.factorial(m + j) // math.factorial(m) for j in range(m + 1))
        C_m = sum((-1) ** (m + j) * (-1) ** j * math.comb(m, j) * math.factorial(m + j) // math.factorial(m) for j in range(m + 1))
        # Make both positive
        if B_m < 0:
            B_m, C_m = -B_m, -C_m
        # Check: C_m / B_m approximates e!
        err = abs(e_dec - Decimal(C_m) / Decimal(B_m))
        N_eff = -math.log2(float(err))
        q_odd = odd_part(Fraction(C_m, B_m).denominator)
        print(f"    m={m:>2}, N_eff={N_eff:>6.1f}: log(q_odd)/N_eff = {math.log(q_odd)/N_eff:.5f} ((ln 2)/2 = {math.log(2)/2:.5f})")

    # 3. Li_s(1/2) for s = 2, 3
    print("\n3. Polylogarithms Li_s(1/2) shifted denominator rates (theory: s):")
    for s in [2, 3]:
        for N in [64, 128, 256]:
            Y = sum(Fraction(1 << (N - m), m ** s) for m in range(1, N + 1))
            q_N = Y.denominator
            print(f"  Li_{s}(1/2), N={N:>3}: log(q_N)/N = {math.log(q_N)/N:.5f} (theory: {s}.00000)")

    # 4. zeta(3): Apery binomial series & Apery recurrence convergents
    print("\n4a. zeta(3) Apery binomial series (5/2) * sum_{k=1}^M (-1)^{k-1}/(k^3 comb(2k,k)), M=N//2:")
    for N in [64, 128, 256]:
        M = N // 2
        Y = Fraction(5, 2) * (1 << N) * sum(Fraction((-1) ** (k - 1), (k ** 3) * math.comb(2 * k, k)) for k in range(1, M + 1))
        q_N = Y.denominator
        q_odd = odd_part(q_N)
        print(f"  N={N:>3} (M={M:>3}): log(q_N)/N = {math.log(q_N)/N:.5f}, log(q_odd)/N = {math.log(q_odd)/N:.5f}")

    print("4b. zeta(3) Apery recurrence convergents a_n/b_n:")
    b0, b1 = Fraction(1), Fraction(5)
    a0, a1 = Fraction(0), Fraction(6)
    z3_dec = Decimal("1.2020569031595942853997381615114499907649862923404988817922715553418382057863130901864558736093352581")
    apery_lim = (3 + 4 * math.log(1 + math.sqrt(2))) * math.log(2) / (8 * math.log(1 + math.sqrt(2)))
    for n in range(2, 31):
        p_coeff = 34 * n ** 3 - 51 * n ** 2 + 27 * n - 5
        b2 = (p_coeff * b1 - ((n - 1) ** 3) * b0) / (n ** 3)
        a2 = (p_coeff * a1 - ((n - 1) ** 3) * a0) / (n ** 3)
        b0, b1 = b1, b2
        a0, a1 = a1, a2
        if n in (10, 20, 30):
            approx = a1 / b1
            err = abs(z3_dec - Decimal(approx.numerator) / Decimal(approx.denominator))
            N_eff = -math.log2(float(err))
            q_odd = odd_part(approx.denominator)
            print(f"  n={n:>2}, N_eff={N_eff:>6.1f}: log(q_odd)/N_eff = {math.log(q_odd)/N_eff:.5f} (theory: {apery_lim:.5f})")

    # 5. Algebraic irrationals: Catalan dyadic series vs Pell convergents
    print("\n5. Algebraic irrationals (Catalan dyadic series vs Pell convergents):")
    s2 = Decimal(2).sqrt()
    s3 = Decimal(3).sqrt()
    phi = (Decimal(1) + Decimal(5).sqrt()) / Decimal(2)
    # Check Catalan series identities
    for label, target, stride, alt, shift0 in [
        ("(3/4)*sqrt(2)", Decimal(3) / Decimal(4) * s2, 5, True, Decimal(1)),
        ("sqrt(3)/2", s3 / Decimal(2), 4, False, Decimal(1)),
        ("phi=(1+sqrt(5))/2", phi, 4, True, Decimal(3) / Decimal(2)),
    ]:
        N = 120
        K = N // (stride - 2)
        tot = Fraction(3, 2) if shift0 == Decimal("1.5") else Fraction(1)
        for k in range(1, K + 1):
            cat = math.comb(2 * k - 2, k - 1) // k
            sgn = ((-1) ** (k - 1)) if alt else -1
            tot += Fraction(sgn * cat, 1 << (stride * k - 1))
        shifted = tot * (1 << N)
        assert odd_part(shifted.denominator) == 1
        v2_ex = v_p(shifted.denominator, 2)
        err = abs(target - Decimal(tot.numerator) / Decimal(tot.denominator))
        print(f"  {label:<18}: odd_den=1, K={K:>2}, v2(den(2^N S_K))/N={v2_ex/N:.4f} (pred {2/(stride-2):.4f}), log2|err|={math.log2(float(err)):.1f}")

    # Pell convergents to sqrt(2)
    p0, q0 = 1, 1
    p1, q1 = 3, 2
    # Actually p_n/q_n with p^2 - 2q^2 = (-1)^n: (1,1), (3,2), (7,5), (17,12)...
    # Notice q_n is odd for even n, even for odd n; even better, odd_part(q_n) has v2(q_n) <= log2(q_n)
    p_a, q_a = 1, 1
    p_b, q_b = 3, 2
    for step in range(2, 42):
        p_c, q_c = 2 * p_b + p_a, 2 * q_b + q_a
        p_a, q_a = p_b, q_b
        p_b, q_b = p_c, q_c
        if step in (20, 30, 40):
            err = abs(s2 - Decimal(p_b) / Decimal(q_b))
            N_eff = -math.log2(float(err))
            print(f"  Pell sqrt(2) step={step:>2}, N_eff={N_eff:>5.1f}: log(q_odd)/N_eff = {math.log(odd_part(q_b))/N_eff:.5f} ((ln 2)/2 = {math.log(2)/2:.5f})")


if __name__ == "__main__":
    verify_f1()
    verify_f2()
    verify_f3_f4()
    verify_f5()
    verify_legendre_windows()
    print("\nAll Phase 18 classical synthesis checks passed.")
