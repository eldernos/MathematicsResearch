"""Exact finite certificates and clearly separated numerical checks for Phase 25 Track F.

Covers:
  F1. Equality boundaries d = r in {2, 3}: low-residue-locked & aggregate-denominator-locked
      single-packet obstruction (full-window invariants + exact local discrepancy bounds),
      lag-delta scaled-phase equidistribution, flagship cube consecutive-arrival cancellation
      (with exact 3-adic congruences), exact iff one-gap + low-residue characterization using
      Q' = Q / gcd(Q, B^M) (including the real-data b=2, M=10, Q=2 regression test), and
      flagship cube prefix-denominator drops through M = 2200.
  F2. Computable badly approximable polynomial-normal numbers: elementary fourth-moment
      Kloosterman identities, prime-power congruence counts, non-vacuous trapezoid majorant
      and Fourier-tail split-sum bounds, exact integer zeta-constant bounds, pure-analytic
      hand-checkable M=100 L=52 steps and exact integer block-measure certificates (M=42 L=4
      elementary, M=14 L=4 and M=30 L=2 Weil-Estermann), exact rational Fourier-decay
      exponents and computable rational majorants (xi_0_bar, C_bar, K_bar, J_e) for r=1,2,3,
      matrix continuant bounds, and L^2 potential martingale selection on certified weights.
  F3. Stronger deterministic approximation bounds: exact continued-fraction folding lemma
      (zero loss at c=1, factor-2-free c^2 bound for c>=2), slow-pole locally varying
      full-density all-prime series V(w) with exact theorem schedules (kappa, m_j, P_k),
      exact regrouping, order valuations, monic-polynomial p-adic valuation pole retention
      including p | C(r, j) (e.g. (r, j, p) = (3, 1, 3), (3, 2, 3), (4, 2, 3)), and injectivity.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import cos, gcd, isqrt, pi, prod, sin, comb


def vp(n, p):
    assert n != 0
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def vp_frac(x, p):
    assert x != 0
    return vp(x.numerator, p) - vp(x.denominator, p)


def floor_frac(x):
    return x.numerator // x.denominator


def ceil_frac(x):
    return -((-x.numerator) // x.denominator)


def iroot_floor(n, k):
    """Exact floor of the k-th root of nonnegative integer n (exact integer certification)."""
    if n == 0:
        return 0
    if k == 1:
        return n
    bl = n.bit_length()
    shift = max(0, ((bl - 50) // k) * k)
    x = (int((n >> shift) ** (1.0 / k)) + 2) << (shift // k)
    while x ** k < n:
        x *= 2
    while True:
        x_next = ((k - 1) * x + n // (x ** (k - 1))) // k
        if x_next >= x:
            break
        x = x_next
    while (x + 1) ** k <= n:
        x += 1
    while x ** k > n:
        x -= 1
    assert x ** k <= n < (x + 1) ** k
    return x


def cf_canonical(x):
    """Canonical regular continued fraction [a0; a1, ..., an] of rational x >= 0 (an >= 2 if n >= 1)."""
    assert x >= 0
    res = []
    while True:
        a = x.numerator // x.denominator
        res.append(a)
        x -= a
        if x == 0:
            break
        x = Fraction(1, 1) / x
    return res


def primes_away(m):
    n = 2
    while True:
        if m % n and all(n % k for k in range(2, isqrt(n) + 1)):
            yield n
        n += 1


def mult_order(b, mod):
    assert gcd(b, mod) == 1 and mod >= 1
    if mod == 1:
        return 1
    x = b % mod
    k = 1
    while x != 1:
        x = (x * b) % mod
        k += 1
    return k


def convolution_coeffs(d, p, s, limit):
    """Ordered d-fold positive power convolution for C_s(d)^d up to shift limit."""
    atoms = []
    i = 1
    while i ** d <= limit:
        atoms.append((i ** d, Fraction(1, p ** (s * vp(i, p)))))
        i += 1
    row = {0: Fraction(1)}
    for _ in range(d):
        nxt = Counter()
        for m, val in row.items():
            for pw, w in atoms:
                if m + pw > limit:
                    break
                nxt[m + pw] += val * w
        row = nxt
    return row


# ---------------------------------------------------------------------------
# F1: Equality boundaries d = r in {2, 3}
# ---------------------------------------------------------------------------

def check_f1_low_residue_packet_barrier():
    """Exact certificates for Theorem 1.1 (low-residue & aggregate-den-locked single-packet
    obstruction + exact local discrepancy bounds) and Theorem 1.2 (lag-delta scaled-phase
    equidistribution + flagship cube 3-adic cancellation)."""
    checked_lifts = 0
    site_checks = 0
    agg_checks = 0
    zero_disc_bounds = []
    for d, p, s, b, t, a, h in [
        (2, 3, 2, 2, 2, 2, 2),  # B=4, M=162, E=8, h=2, E-h=6, p^(E-h)=729, L=9, K=12
        (3, 3, 2, 2, 2, 1, 2),  # B=4, M=81, E=6, h=2, E-h=4, p^(E-h)=81, L=6, K=12
    ]:
        B = b ** t
        U = p ** a
        M = d * (U ** d)
        E = s * d * a
        v = (h + s - 1) // s
        G = p ** (d * (a - v + 1))
        L = 0
        while b ** (L + 1) <= p ** (E - h):
            L += 1
        K = min(G - 1, max(12, (L + t - 1) // t + 2))
        assert K < G and L >= 6

        limit = M + K + 15
        row = convolution_coeffs(d, p, s, limit)
        R_map = {}
        phase = Fraction(0)
        for m in range(1, M + K + 1):
            phase = (B * phase + row[m]) % 1
            if m >= M:
                R_map[m] = phase
                assert phase.denominator == p ** E
        assert R_map[M].numerator % p == 1

        # Exact positive rational tail satisfying T_{m+1} = B * T_m - c_{m+1}
        T_end = Fraction(1, 7 * (B ** 4))
        T_map = {M + K: T_end}
        for m in range(M + K - 1, M - 1, -1):
            T_map[m] = (T_map[m + 1] + row[m + 1]) / B
            assert T_map[m] > 0

        pE = p ** E
        pEh = p ** (E - h)
        ph = p ** h
        w_B = vp(B - 1, p)

        # Precompute exact integer numerators A_y mod p^E and powers B^(y-M) mod p^(E-h)
        A_int = {y: R_map[y].numerator for y in range(M, M + K + 1)}
        B_pow = {y: pow(B, y - M, pEh) for y in range(M, M + K + 1)}

        # Precompute all qualifying aggregate pairs M <= u1 < v1 <= M+K with w_B + v_p(v1-u1) < h
        qual_pairs = []
        for u1 in range(M, M + K + 1):
            for v1 in range(u1 + 1, M + K + 1):
                m_val = w_B + vp(v1 - u1, p)
                if m_val < h:
                    diff_num = (A_int[v1] - A_int[u1]) % pE
                    g = gcd(diff_num, pE)
                    exp_den = pE // g
                    assert exp_den == p ** (E - m_val)
                    exp_low = (diff_num // g) % ph
                    qual_pairs.append((u1, v1, exp_den, exp_low))

        # Vary ALL u in {0, ..., p^(E-h) - 1}: check EVERY site y in [M, M+K] and EVERY qualifying pair
        words_seen = set()
        zero_word_witness = None
        for u in range(pEh):
            A_tilde = {}
            for y in range(M, M + K + 1):
                a_t = (A_int[y] + u * B_pow[y] * ph) % pE
                assert a_t % p != 0              # exact denominator p^E
                assert a_t % ph == A_int[y] % ph # exact low residue mod p^h
                # Scaled phase {p^(E-h) * (a_t / p^E)} = (a_t % ph) / ph identically preserved
                assert (a_t * pEh) % pE == (A_int[y] * pEh) % pE
                A_tilde[y] = a_t
                site_checks += 1
            for u1, v1, exp_den, exp_low in qual_pairs:
                d_num = (A_tilde[v1] - A_tilde[u1]) % pE
                g = gcd(d_num, pE)
                assert pE // g == exp_den
                assert (d_num // g) % ph == exp_low
                agg_checks += 1
            x_tilde = (R_map[M] + T_map[M] + Fraction(u, pEh)) % 1
            word_int = floor_frac((b ** L) * x_tilde)
            words_seen.add(word_int)
            if word_int == 0 and zero_word_witness is None:
                zero_word_witness = (u, x_tilde)
            checked_lifts += 1
        assert len(words_seen) == b ** L and zero_word_witness is not None

        # Certify exact all-zero local discrepancy lower bound max_{1<=m<=L} ((L-m+1)/L - b^(-m))
        _, x0 = zero_word_witness
        best_m, best_lb = max(
            ((m_idx, Fraction(L - m_idx + 1, L) - Fraction(1, b ** m_idx)) for m_idx in range(1, L + 1)),
            key=lambda pair: pair[1],
        )
        # Directly count the L shifts {b^n * x0} in [0, b^(-best_m)) using exact Fractions
        pts = [((b ** n) * x0) % 1 for n in range(L)]
        in_iv = sum(1 for pt in pts if pt < Fraction(1, b ** best_m))
        emp_disc_iv = Fraction(in_iv, L) - Fraction(1, b ** best_m)
        assert emp_disc_iv >= best_lb
        zero_disc_bounds.append((L, best_lb))
    assert zero_disc_bounds == [(9, Fraction(47, 72)), (6, Fraction(7, 12))]

    # Theorem 1.2(1): exact lag-delta scaled-phase uniform grids
    lag_grids = 0
    for p, B in ((3, 4), (3, 10), (5, 16)):
        w = vp(B - 1, p)
        for k in (2, 3, 4):
            h = w + k
            mod = p ** h
            for delta in (1, 2, p, 2 * p):
                ell = vp(delta, p)
                if k < w + ell:
                    continue
                for unit in (1, 2):
                    counts = Counter(
                        unit * pow(B, r, mod) * ((pow(B, delta, mod) - 1) % mod) % mod
                        for r in range(p ** k)
                    )
                    base_res = (unit * (pow(B, delta, mod) - 1)) % (p ** (2 * w + ell))
                    grid = set(range(base_res, mod, p ** (2 * w + ell)))
                    assert set(counts) == grid
                    assert set(counts.values()) == {p ** (w + ell)}
                    lag_grids += 1

    # Theorem 1.2(2): flagship cube consecutive selected-arrival extra cancellation (d=3, p=3, B=4)
    # Also verify the exact 3-adic congruences explaining k=3 (1 residue) and k=4 (2 residues).
    for r in range(27):
        j = 1 + 3 * r
        delta = (j + 1) ** 3 - j ** 3
        assert delta == 7 + 27 * r * (r + 1)
        val81 = pow(4, j ** 3, 81) * ((pow(4, delta, 81) - 1) % 81) % 81
        assert val81 == (4 * (4 ** 7 - 1)) % 81
        val243 = pow(4, j ** 3, 243) * ((pow(4, delta, 243) - 1) % 243) % 243
        assert val243 == (4 * (4 ** 7 - 1) + 81 * (r * r + 2 * r)) % 243

    collapse_counts = []
    for k in range(3, 8):
        mod = 3 ** (1 + k)
        vals = Counter()
        for r in range(3 ** (k - 1)):
            j = 1 + 3 * r
            delta = (j + 1) ** 3 - j ** 3
            assert delta % 3 == 1
            v_val = pow(4, j ** 3, mod) * ((pow(4, delta, mod) - 1) % mod) % mod
            assert v_val % 3 == 0 and v_val % 9 != 0
            vals[v_val // 3] += 1
        collapse_counts.append(len(vals))
    assert collapse_counts == [1, 2, 4, 11, 31]
    print(f"F1 barrier & lag grids: {checked_lifts} lifts ({site_checks} site checks, "
          f"{agg_checks} aggregate-pair checks, all words realized, zero-word bounds={zero_disc_bounds}), "
          f"{lag_grids} exact lag-delta grids, flagship cube collapse={collapse_counts}")


def check_f1_gap_certificate_iff_and_cube_drops():
    """Exact certificates for Theorem 1.3(1) (iff characterization using Q' = Q / gcd(Q, B^M),
    including the real-data C_1(2)^2 regression test at b=2, M=10, Q=2) and exact flagship cube
    prefix-denominator drops through M = 2200."""
    # 1. Real-data regression test (C1): C_1(2)^2 with b=2, B=4, p=3, s=1, M=10, h=0, Q=2
    row_sq = convolution_coeffs(2, 3, 1, 25)
    R10 = Fraction(0)
    for m in range(1, 11):
        R10 = 4 * R10 + row_sq[m]
    assert R10 == Fraction(202802, 3) and R10.denominator == 3
    # Rigorous rational upper bound on T_10 = sum_{m>=11} c_m * 4^(10-m):
    # exact sum for 11<=m<=25 plus trivial upper bound c_m <= m for m>=26:
    # sum_{m>=26} m * 4^(10-m) = (26/4^16) * (4/3) + (1/4^16) * (4/9) = (108/9) / 4^16 < 1/4^14
    T10_head = sum(row_sq[m] * Fraction(1, 4 ** (m - 10)) for m in range(11, 26))
    T10_tail_ub = Fraction(12, 4 ** 16)
    T10_ub = T10_head + T10_tail_ub
    assert T10_ub < Fraction(1, 6)  # T_max = 1/6 is a valid strict upper bound on T_10
    B_reg = 4
    M_reg = 10
    Q_reg = 2
    p_reg = 3
    e_reg = 1
    Qp_reg = Q_reg // gcd(Q_reg, B_reg ** M_reg)
    assert Qp_reg == 1
    r_min_reg = gcd(Qp_reg, p_reg ** e_reg)
    assert r_min_reg == 1
    # At T_max = 1/6: Q' * p^e * T_max = 1/2 < 1 = r_min, so 2*X in Z IS excluded!
    assert Qp_reg * (p_reg ** e_reg) * Fraction(1, 6) < r_min_reg
    # Verify no unit A_tilde in {1, 2} admits Q'*(A_tilde/3 + T) in Z with 0 < T <= 1/6
    for A_tilde in (1, 2):
        min_T = Fraction((-Qp_reg * A_tilde - 1) % 3 + 1, Qp_reg * 3)
        assert min_T > Fraction(1, 6)
    # At T_max = 1/3: Q' * p^e * T_max = 1 >= r_min, and an explicit rational X' with 2*X' in Z exists!
    N_wit = (B_reg ** M_reg) // 2 - 1  # = 2^19 - 1
    X_wit = (N_wit + Fraction(2, 3) + Fraction(1, 3)) / (B_reg ** M_reg)
    assert Q_reg * X_wit == 1
    assert (B_reg ** M_reg * X_wit - Fraction(1, 3) - N_wit) == Fraction(2, 3)

    # 2. Systematic iff verification across (b, p, e, h, Q, M) with actual X' witnesses
    iff_cases = 0
    reduced_cases = 0
    for b in (2, 3, 5, 6, 10):
        for p in (3, 5):
            if b % p == 0:
                continue
            t = mult_order(b, p)
            B = b ** t
            for M in (1, 10):
                BM = B ** M
                for e in (2, 3):
                    pe = p ** e
                    for h in range(0, e + 1):
                        ph = p ** h
                        for Q in (1, 2, 3, 4, 5, 6, 9, 10, 15):
                            G_B = gcd(Q, BM)
                            Qp = Q // G_B
                            B0 = BM // G_B
                            assert gcd(Qp, B0) == 1
                            g0 = gcd(Qp, p ** (e - h))
                            step = g0 * ph
                            units = [1] if h == 0 else [a for a in range(1, min(ph, 7)) if a % p]
                            for A0 in units:
                                if G_B > 1:
                                    reduced_cases += 1
                                valid_residues = []
                                for u in range(p ** (e - h)):
                                    A_tilde = (A0 + u * ph) % pe
                                    if A_tilde % p == 0:
                                        continue
                                    r = (-Qp * A_tilde - 1) % pe + 1
                                    valid_residues.append((r, A_tilde))
                                r_min_emp, witness_A = min(valid_residues)
                                if h == 0:
                                    r_min_formula = g0
                                else:
                                    r_min_formula = (-Qp * A0 - 1) % step + 1
                                assert r_min_emp == r_min_formula
                                T_wit = Fraction(r_min_formula, Qp * pe)
                                # Verify Q'*(witness_A/p^e + T_wit) is an integer k and solve Q'*N = -k (mod B0)
                                phi_wit = Fraction(witness_A, pe) + T_wit
                                k_frac = Qp * phi_wit
                                assert k_frac.denominator == 1
                                k_int = k_frac.numerator
                                N_sol = (-k_int * pow(Qp, -1, B0)) % B0
                                X_prime = (Fraction(N_sol) + phi_wit) / BM
                                assert (Q * X_prime).denominator == 1
                                # Verify exact consistency of X_prime with the data
                                R_prime = BM * X_prime - T_wit
                                assert (R_prime % 1) == Fraction(witness_A, pe)
                                assert R_prime.denominator == pe
                                if h >= 1:
                                    assert witness_A % ph == A0 % ph
                                # Verify strict exclusion for every valid lift below T_wit
                                for r, _ in valid_residues:
                                    assert Fraction(r, Qp * pe) >= T_wit
                                iff_cases += 1

    # 3. Flagship cube (d=3, p=3, s=1, B=4) prefix denominators through M = 2200
    limit = 2200
    row = convolution_coeffs(3, 3, 1, limit)
    R = Fraction(0)
    prev_e = 0
    drops = []
    e_at = {}
    first_e6 = None
    for M in range(1, limit + 1):
        R = 4 * R + row[M]
        e = vp(R.denominator, 3)
        e_at[M] = e
        if e == 6 and first_e6 is None:
            first_e6 = M
        if e < prev_e:
            drops.append((M, prev_e, e))
        prev_e = e
    assert drops == [(783, 3, 2), (820, 2, 1), (953, 2, 1), (1161, 3, 2), (1268, 2, 0)]
    assert e_at[1268] == 0 and e_at[2186] == 4 and e_at[2187] == 6 and first_e6 == 2187 and e_at[2200] == 6

    # Exact rational threshold sanity checks using analytic bounds 2/3 < log(2) < 7/10
    assert Fraction(1, 2) / Fraction(2, 3) == Fraction(3, 4)
    assert Fraction(2, 3) / Fraction(7, 10) == Fraction(20, 21)
    assert Fraction(1, 2) / Fraction(7, 10) < Fraction(2, 3) / Fraction(7, 10)
    print(f"F1 gap iff & cube drops: C_1(2)^2 regression test passed (R_10=202802/3, Q'=1); "
          f"{iff_cases} exact (b,p,e,h,Q,M) iff configs ({reduced_cases} with gcd(Q,B^M)>1); "
          f"5 flagship cube drops through M=2200 (e(1268)=0, e(2186)=4, first e=6 at M=2187)")


# ---------------------------------------------------------------------------
# F2: Computable badly approximable polynomial-normal numbers
# ---------------------------------------------------------------------------

def check_f2_kloosterman_and_hyperbola():
    """Exact integer/Fraction certificates for Lemma 2.1 (fourth-moment identity, prime-power
    congruence counts, non-vacuous trapezoid majorant & Fourier-tail split-sum bounds, exact
    integer zeta-constant bounds) + clearly separated floating-point sanity measurements."""
    # 1. Exact integer fourth-moment solution count for primes p
    for p in (2, 3, 5, 7, 11, 13):
        inv = {x: pow(x, -1, p) for x in range(1, p)}
        pairs = Counter(((x1 + x2) % p, (inv[x1] + inv[x2]) % p)
                        for x1 in range(1, p) for x2 in range(1, p))
        sols = sum(c * c for c in pairs.values())
        expected = 1 if p == 2 else 3 * (p - 1) * (p - 2)
        assert sols == expected
        assert sols < 3 * p * p
        if p >= 3:
            assert 3 * p * p * (p - 2) < 16 * (p ** 3)

    # 2. Exact prime-power quadratic-congruence count (stationary phase mod p^k)
    prime_powers = ((2, 2), (2, 3), (2, 4), (2, 5), (3, 2), (3, 3), (3, 4), (5, 2), (5, 3))
    for p, k in prime_powers:
        m = k // 2
        pm = p ** m
        pkm = p ** (k - m)
        max_sols = (4 if p == 2 else 2) * (p ** (k - 2 * m))
        for u in range(1, pm):
            if u % p == 0:
                continue
            for v in range(1, pm):
                if v % p == 0:
                    continue
                cnt = sum(1 for x0 in range(1, pkm) if x0 % p and (u * x0 * x0 - v) % pm == 0)
                assert cnt <= max_sols

    # 3. Non-vacuous exact trapezoid majorant & Fourier-tail split-sum certificates (Lemma 2.1 Step 3)
    split_sum_checks = 0
    max_split_ratio = Fraction(0)
    majorant_checks = 0
    for q in (13, 16, 21, 25, 30, 37, 45, 60):
        divisors = [d for d in range(1, q + 1) if q % d == 0]
        inv_map = {x: (-pow(x, -1, q)) % q for x in range(1, q) if gcd(x, q) == 1}
        L_vals = [L for L in range(1, (q + 3) // 4)]  # all 1 <= L < q/4
        for L in L_vals:
            assert 3 * L - 1 < q  # zero wraparound
            # Verify exact trapezoid majorant B_I for a=0
            B_I = [Fraction(0)] * q
            for x in range(q):
                # B_I(x) = (1/L) * sum_{y=-L+1}^0 1_{[0, 2L-1]}((x - y) mod q)
                B_I[x] = Fraction(sum(1 for y in range(-L + 1, 1) if (x - y) % q < 2 * L), L)
                assert 0 <= B_I[x] <= 1
                if x < L:
                    assert B_I[x] == 1
            assert sum(B_I) == 2 * L
            # Check exact Fourier-tail split-sum bound < 5*q/d for EVERY divisor d | q
            for d in divisors:
                # 2 * sum_{1 <= u' <= q/(2d)} min(2L, q^2 / (4 L (d u')^2)) < 5 q / d
                limit_u = q // (2 * d)
                tail_sum = Fraction(0)
                for u_prime in range(1, limit_u + 1):
                    term = min(Fraction(2 * L), Fraction(q * q, 4 * L * d * d * u_prime * u_prime))
                    # Note: if 2*d*u' == q (even q/d), that frequency occurs once, not twice; doubling is a valid upper bound
                    tail_sum += 2 * term
                bound = Fraction(5 * q, d)
                assert tail_sum < bound
                ratio = tail_sum / bound
                if ratio > max_split_ratio:
                    max_split_ratio = ratio
                split_sum_checks += 1
        # Verify exact non-wraparound majorization sum_{x in (Z/qZ)^x} B_I(x) B_J(-x^{-1}) >= count
        sample_Ls = sorted({1, L_vals[len(L_vals) // 2], L_vals[-1]})
        for L1 in sample_Ls:
            B1 = [Fraction(sum(1 for y in range(-L1 + 1, 1) if (x - y) % q < 2 * L1), L1) for x in range(q)]
            for L2 in sample_Ls:
                B2 = [Fraction(sum(1 for y in range(-L2 + 1, 1) if (x - y) % q < 2 * L2), L2) for x in range(q)]
                exact_cnt = sum(1 for x, y in inv_map.items() if x < L1 and y < L2)
                maj_sum = sum(B1[x] * B2[y] for x, y in inv_map.items())
                assert maj_sum >= exact_cnt
                majorant_checks += 1

    # 4. Exact integer zeta-constant certificates for the constants 120 and 90 in (2.2)-(2.3)
    # Certify zeta(7/4) <= sum_{n=1}^5 n^(-7/4) + (4/3)*5^(-3/4) < 2  =>  50*zeta(7/4) + 20 < 120
    S_scale = 10 ** 6
    z74_ub = Fraction(0)
    for n in range(1, 6):
        # upper bound n^(-7/4) <= (floor(S_scale / n^(7/4)) + 1) / S_scale
        val = iroot_floor((S_scale ** 4) // (n ** 7), 4) + 1
        assert (val ** 4) * (n ** 7) > S_scale ** 4
        z74_ub += Fraction(val, S_scale)
    tail74 = iroot_floor((S_scale ** 4) // (5 ** 3), 4) + 1
    assert (tail74 ** 4) * (5 ** 3) > S_scale ** 4
    z74_ub += Fraction(4, 3) * Fraction(tail74, S_scale)
    assert z74_ub < 2 and 50 * z74_ub + 20 < 120

    # Certify zeta(3/2) <= sum_{n=1}^25 n^(-3/2) + 2*25^(-1/2) < 14/5  =>  25*zeta(3/2) + 20 < 90
    z32_ub = Fraction(0)
    for n in range(1, 26):
        val = isqrt((S_scale ** 2) // (n ** 3)) + 1
        assert (val ** 2) * (n ** 3) > S_scale ** 2
        z32_ub += Fraction(val, S_scale)
    z32_ub += Fraction(2, 5)  # 2 * 25^(-1/2) = 2/5 exact
    assert z32_ub < Fraction(14, 5) and 25 * z32_ub + 20 < 90

    # 5. Clearly separated floating-point sanity measurements (NOT proof certificates)
    max_elem_ratio = 0.0
    max_weil_ratio = 0.0
    for q in (2, 3, 4, 5, 7, 8, 9, 12, 16, 25, 27):
        tau_q = sum(1 for d in range(1, q + 1) if q % d == 0)
        invs = [(x, pow(x, -1, q)) for x in range(1, q) if gcd(x, q) == 1]
        for u in range(q):
            for v in range(q):
                re_s = sum(cos(2 * pi * ((u * x + v * xi) % q) / q) for x, xi in invs)
                im_s = sum(sin(2 * pi * ((u * x + v * xi) % q) / q) for x, xi in invs)
                mag = (re_s * re_s + im_s * im_s) ** 0.5
                g = gcd(gcd(u, v), q)
                max_elem_ratio = max(max_elem_ratio, mag / (2 * tau_q * (g ** 0.25) * (q ** 0.75)))
                max_weil_ratio = max(max_weil_ratio, mag / (tau_q * (g ** 0.5) * (q ** 0.5)))
    assert max_elem_ratio <= 1.0 + 1e-12 and max_weil_ratio <= 1.0 + 1e-12

    # Empirical hyperbola rectangle excess measurement vs sqrt(q) on primes q in {101, 503, 2003}
    max_emp_rect_ratio = 0.0
    emp_rects = 0
    for q in (101, 503, 2003):
        pts = [(x, (-pow(x, -1, q)) % q) for x in range(1, q)]
        for L1 in (q // 5, q // 3):
            for L2 in (q // 5, q // 3):
                for a in (0, q // 4):
                    for b in (0, q // 3):
                        cnt = sum(1 for x, y in pts if (x - a) % q < L1 and (y - b) % q < L2)
                        expected_cnt = L1 * L2 * (q - 1) / (q * q)
                        max_emp_rect_ratio = max(max_emp_rect_ratio, abs(cnt - expected_cnt) / (q ** 0.5))
                        emp_rects += 1
    assert max_emp_rect_ratio < 5.0
    print(f"F2 Kloosterman & hyperbola: exact fourth-moment, {len(prime_powers)} prime-power, "
          f"{split_sum_checks} split-sum (max ratio={float(max_split_ratio):.4f}<1), "
          f"{majorant_checks} trapezoid-majorant, and exact zeta(7/4), zeta(3/2) certificates; "
          f"float sanity max_elem={max_elem_ratio:.4f}, max_weil={max_weil_ratio:.4f}, "
          f"emp_rect_excess/sqrt(q)={max_emp_rect_ratio:.4f} ({emp_rects} rects)")


def certify_block_sum_exact(M, L, P, Q, D):
    """Exact integer certificate that sum_{u in {1..M}^L} (q_L(u) + p_L(u))^(-P/Q) > 1.
    Returns (distinct_N, total_int, D, counts_dict) where total_int > D proves existence of
    explicit rational weights p_u = a_{N(u)} / total_int <= N(u)^(-P/Q) summing to 1."""
    if L == 2:
        counts = Counter(a * b + 1 + b for a in range(1, M + 1) for b in range(1, M + 1))
    elif L == 4:
        left = Counter((a + 1, a * b + b + 1) for a in range(1, M + 1) for b in range(1, M + 1))
        right = Counter((b2, a2 * b2 + 1) for a2 in range(1, M + 1) for b2 in range(1, M + 1))
        counts = Counter()
        for (u1, u2), c1 in left.items():
            for (r2, s2), c2 in right.items():
                counts[u1 * r2 + u2 * s2] += c1 * c2
    else:
        raise ValueError("Unsupported L")
    DQ = D ** Q
    total = 0
    for N, mult in counts.items():
        target = DQ // (N ** P)
        a = iroot_floor(target, Q)
        assert a > 0 and (a ** Q) * (N ** P) <= DQ
        total += mult * a
    assert total > D
    return len(counts), total, D, counts


def compute_f2_rational_majorants(M, L, B0, s, rho_klo, C_klo, alpha, beta, theta_base, coeffs):
    """Exact computable rational algorithm of Theorems 2.3 and 2.4.
    coeffs = [c_0, c_1, ..., c_r] (Fraction list with c_r != 0).
    Returns (eta, xi0_bar, C_bar, K_bar) as exact Fraction/int objects."""
    r = len(coeffs) - 1
    assert r >= 1 and coeffs[r] != 0
    theta = Fraction(0) if r == 1 else theta_base
    c_star = abs(coeffs[r])
    M_P = sum(j * abs(coeffs[j]) for j in range(1, r + 1))
    L_P = sum(j * (j - 1) * abs(coeffs[j]) for j in range(2, r + 1))
    M_P_bar = max(Fraction(1), M_P)
    C_F = 2 * B0 * B0 + 2
    S1 = 2 * (M + 1) * B0 * L_P

    m_lin = 2 * alpha + 4 * beta - 1
    m_A = s - 2 * alpha - 2 * beta - Fraction(3, 2) * theta
    m_B = (1 - rho_klo) * alpha / 2 - (1 - s) - theta / 2
    assert m_lin > 0 and m_A > 0 and m_B > 0
    if r == 1:
        eta = min(m_lin, m_A / 2, m_B / 4)
    else:
        eta = min(m_lin, 2 * alpha * s, s * theta / (r - 1), m_A / 2, m_B / 4)
    assert 0 < eta < 1

    # Explicit computable integer thresholds X_1..X_5
    gamma1 = 1 - 2 * alpha - 2 * beta - theta
    assert gamma1 > 0
    if r == 1:
        X1 = max(1, ceil_frac(Fraction(8 * B0 * B0) / c_star)) ** ceil_frac(Fraction(1) / gamma1)
        X2 = 1
        X3 = 1
        X4 = 1
    else:
        X1 = (8 * B0 * B0) ** ceil_frac(Fraction(1) / gamma1)
        gamma2 = 4 * alpha + 2 * beta - 1
        gamma3 = 2 * alpha - theta
        gamma4 = (1 + rho_klo) * alpha - theta
        assert gamma2 > 0 and gamma3 > 0 and gamma4 > 0
        X2 = max(1, ceil_frac(2 * L_P)) ** ceil_frac(Fraction(1) / gamma2)
        X3 = max(1, ceil_frac(16 * B0 * B0 * L_P)) ** ceil_frac(Fraction(1) / gamma3)
        X4 = max(1, ceil_frac(S1 + 1)) ** ceil_frac(Fraction(1) / gamma4)
    gamma5 = 1 - 2 * alpha - 2 * beta
    assert gamma5 > 0
    X5 = max(1, ceil_frac(Fraction(1) / M_P)) ** ceil_frac(Fraction(1) / gamma5)
    xi0_bar = max(16, X1, X2, X3, X4, X5)

    # Explicit computable rational constant C_bar(P)
    if r == 1:
        A1 = Fraction(0)
        D_delta1 = max(Fraction(1), Fraction(1) / (c_star * c_star))
    else:
        A1 = (r - 1) * (2 * C_F * max(Fraction(1), Fraction(1) / (r * c_star)) + 4)
        D_delta1 = Fraction(1)
    A2 = 4 * (L_P + 2 * M_P)
    KA0 = 4096 * (r + 1) * (M + 1) * (B0 ** 4) * M_P_bar * D_delta1
    KB0 = Fraction(24 * (r + 1) * (C_klo + 64) * (B0 ** 3)) * (S1 + 1) / m_B
    A3 = 12 * C_F * B0 * M_P_bar * (KA0 + KB0)
    C_bar = max(Fraction(1 + xi0_bar), 2 * (A1 + A2 + A3))

    # Explicit rational majorant K_bar > 1 + 2*C_bar/(1 - 2^(-eta))^2 via log 2 > 2/3
    inv_factor = 1 + Fraction(3, 2) / eta
    K_bar = 1 + 2 * C_bar * inv_factor * inv_factor
    return eta, xi0_bar, C_bar, K_bar


def check_f2_block_measures_and_exponents():
    """100% exact integer/Fraction certificates for F2 Lemmas 2.2-2.4."""
    # 1. Pure-analytic hand-checkable proof steps for M=100, L=52, s=19/20 (zero block enumeration)
    assert 5 * (5 ** 2) > 11 ** 2                                 # phi > 8/5
    assert Fraction(261, 96) < Fraction(11, 4)                    # e < 11/4
    assert Fraction(11, 4) ** 2 < Fraction(3, 2) ** 5             # e^(2/5) < 3/2
    assert Fraction(11, 4) ** 2 < 8                               # e^2 < 2^3 => log 2 > 2/3
    assert (1 + Fraction(35, 121)) > Fraction(5, 4)               # (128/121)^5 > 5/4 (Bernoulli)
    assert (1 + Fraction(51, 125)) > Fraction(6, 5)               # (128/125)^17 > 6/5 (Bernoulli)
    assert 2 ** 155 > 3 * (11 ** 10) * (5 ** 51)                  # final integer inequality
    # Also verify the sharper 809/500 form
    assert 5 * (500 ** 2) > 1118 ** 2
    assert (809 ** 51) * (100 ** 520) > (2 ** 19) * (500 ** 51) * (102 ** 520)

    # 2. Exact integer block-measure certificates
    D = 10 ** 18
    n30, t30, _, _ = certify_block_sum_exact(30, 2, 20, 11, D)
    n14, t14, _, _ = certify_block_sum_exact(14, 4, 20, 11, D)
    n42, t42, _, _ = certify_block_sum_exact(42, 4, 36, 19, D)

    # 3. Exact Fraction exponent-margin certificates for Theorem 2.3 across ALL THREE s values
    param_triples = [
        ("Regime A (M=100, s=19/20)", Fraction(19, 20), Fraction(3, 4), 120,
         Fraction(21, 50), Fraction(9, 200), Fraction(1, 1000)),
        ("Regime A (M=42, s=18/19)", Fraction(18, 19), Fraction(3, 4), 120,
         Fraction(43, 100), Fraction(37, 1000), Fraction(1, 2000)),
        ("Regime B (M=14/30, s=10/11)", Fraction(10, 11), Fraction(1, 2), 90,
         Fraction(19, 50), Fraction(13, 200), Fraction(1, 500)),
    ]
    expected_margins = [
        (Fraction(1, 50), Fraction(37, 2000), Fraction(1, 500)),
        (Fraction(1, 125), Fraction(959, 76000), Fraction(33, 38000)),
        (Fraction(1, 50), Fraction(177, 11000), Fraction(17, 5500)),
    ]
    for (label, s_v, rho_v, C_klo, a_v, b_v, th_v), exp_m in zip(param_triples, expected_margins):
        # All 5 inequalities in (2.5)
        m_lin = 2 * a_v + 4 * b_v - 1
        m_A = s_v - 2 * a_v - 2 * b_v - Fraction(3, 2) * th_v
        m_B = (1 - rho_v) * a_v / 2 - (1 - s_v) - th_v / 2
        assert m_lin > 0 and m_A > 0 and m_B > 0
        assert 4 * a_v + 2 * b_v > 1
        assert 2 * a_v > th_v
        # Derived inequalities: Delta << u_min and K <= q
        assert 2 * a_v + 2 * b_v + th_v < 1
        assert th_v < (1 + rho_v) * a_v
        assert (m_lin, m_A, m_B) == exp_m

    # 4. Certify the computable rational majorants (xi0_bar, C_bar, K_bar, J_e) for r = 1, 2, 3
    #    and verify all exact integer power inequalities at |xi| = xi0_bar
    sample_polys = [
        [Fraction(0), Fraction(1)],                              # P(X) = X (r = 1)
        [Fraction(0), Fraction(-1, 3), Fraction(1)],             # P(X) = X^2 - X/3 (r = 2)
        [Fraction(1), Fraction(-1), Fraction(0), Fraction(1, 2)] # P(X) = X^3/2 - X + 1 (r = 3)
    ]
    B0_30 = 30 * 30 + 1 + 30
    s_we, rho_we, C_we = Fraction(10, 11), Fraction(1, 2), 90
    a_we, b_we, th_we = Fraction(19, 50), Fraction(13, 200), Fraction(1, 500)
    for e_idx, coeffs in enumerate(sample_polys, start=1):
        r_deg = len(coeffs) - 1
        eta, xi0_bar, C_bar, K_bar = compute_f2_rational_majorants(
            30, 2, B0_30, s_we, rho_we, C_we, a_we, b_we, th_we, coeffs
        )
        assert isinstance(xi0_bar, int) and xi0_bar >= 16
        assert isinstance(C_bar, Fraction) and C_bar > 0
        assert isinstance(K_bar, Fraction) and K_bar > 1
        # Verify exact integer power inequalities enforcing Step 4-5 thresholds at |xi| = xi0_bar
        th_cur = Fraction(0) if r_deg == 1 else th_we
        c_st = abs(coeffs[r_deg])
        M_P = sum(j * abs(coeffs[j]) for j in range(1, r_deg + 1))
        L_P = sum(j * (j - 1) * abs(coeffs[j]) for j in range(2, r_deg + 1))
        g1 = 1 - 2 * a_we - 2 * b_we - th_cur
        g5 = 1 - 2 * a_we - 2 * b_we
        if r_deg == 1:
            assert Fraction(xi0_bar) ** g1.numerator >= (Fraction(8 * B0_30 * B0_30) / c_st) ** g1.denominator
        else:
            assert xi0_bar ** g1.numerator >= (8 * B0_30 * B0_30) ** g1.denominator
            g2 = 4 * a_we + 2 * b_we - 1
            g3 = 2 * a_we - th_cur
            g4 = (1 + rho_we) * a_we - th_cur
            S1 = 2 * 31 * B0_30 * L_P
            assert Fraction(xi0_bar) ** g2.numerator >= (2 * L_P) ** g2.denominator
            assert Fraction(xi0_bar) ** g3.numerator >= (16 * B0_30 * B0_30 * L_P) ** g3.denominator
            assert Fraction(xi0_bar) ** g4.numerator >= (S1 + 1) ** g4.denominator
        assert (Fraction(xi0_bar) ** g5.numerator) * (M_P ** g5.denominator) >= 1
        J_e = floor_frac((2 ** (e_idx + 3)) * K_bar) + 1
        assert isinstance(J_e, int) and J_e > (2 ** (e_idx + 3)) * K_bar
        assert Fraction(2, J_e) * K_bar < Fraction(1, 2 ** (e_idx + 2))

    # 5. Exact matrix submultiplicativity, det=+1, uniqueness of (p, q), and w(a) <= q(a)^(-2s)
    #    on the 10,000 depth-4 block concatenations from {1..10}^2 x {1..10}^2 of M=30, L=2
    DQ = D ** 11
    weights_30 = {}
    mats_30 = {}
    for a in range(1, 31):
        for b in range(1, 31):
            N = a * b + 1 + b
            wt_int = iroot_floor(DQ // (N ** 20), 11)
            weights_30[(a, b)] = Fraction(wt_int, t30)
            mats_30[(a, b)] = (1, b, a, a * b + 1)
    assert sum(weights_30.values()) == 1
    seen_pq = set()
    concat_checked = 0
    for u1 in product(range(1, 11), repeat=2):
        p1_, p1, q1_, q1 = mats_30[u1]
        for u2 in product(range(1, 11), repeat=2):
            r1_, r1, s1_, s1 = mats_30[u2]
            P_ = p1_ * r1_ + p1 * s1_
            P = p1_ * r1 + p1 * s1
            Q_ = q1_ * r1_ + q1 * s1_
            Q_new = q1_ * r1 + q1 * s1
            assert P_ * Q_new - P * Q_ == 1
            assert (P * Q_ + 1) % Q_new == 0
            assert Q_new <= (q1 + p1) * (s1 + r1)
            assert (P, Q_new) not in seen_pq
            seen_pq.add((P, Q_new))
            w_prod = weights_30[u1] * weights_30[u2]
            assert (w_prod ** 11) * (Q_new ** 20) <= 1
            concat_checked += 1

    # 6. Exact Weyl square-subsequence interpolation bound (<= 4/j) & L^2 martingale selection
    #    algebra on the actual 900-child certified M=30, L=2 probability distribution
    for j in range(1, 30):
        for N in range(j * j, (j + 1) ** 2):
            assert Fraction(2 * (N - j * j), N) <= Fraction(4, j)
    w_list = [weights_30[(a, b)] for a in range(1, 31) for b in range(1, 31)]
    assert len(w_list) == 900 and sum(w_list) == 1
    for m in range(0, 6):
        Bm = 1 - Fraction(1, 2 ** (m + 1))
        Bm1 = 1 - Fraction(1, 2 ** (m + 2))
        delta_m = (Bm1 - Bm) / 4
        # Construct nontrivial nonnegative child expectations whose exact weighted average is < Bm
        parent_target = Bm - Fraction(1, 1000)
        # Assign E_u = parent_target * (1 + offset_u) centered so sum w_u * offset_u == 0
        raw_offsets = [Fraction(((idx % 7) - 3), 10) for idx in range(900)]
        mean_off = sum(w * o for w, o in zip(w_list, raw_offsets))
        child_vals = [parent_target * (1 + (o - mean_off)) for o in raw_offsets]
        assert all(v >= 0 for v in child_vals)
        assert sum(w * v for w, v in zip(w_list, child_vals)) == parent_target
        assert min(child_vals) + delta_m < Bm1 - delta_m

    print(f"F2 block measures & exponents: hand-checkable M=100 L=52 steps certified; "
          f"exact integer certs M=42 L=4 (s=18/19, {n42} distinct N, ratio={t42/D:.6f}), "
          f"M=14 L=4 (s=10/11, {n14} distinct N, ratio={t14/D:.6f}), "
          f"M=30 L=2 (s=10/11, {n30} distinct N, ratio={t30/D:.6f}); "
          f"3 exponent triples + computable rational majorants (r=1,2,3), "
          f"{concat_checked} concatenations, and 900-child martingale step verified")


# ---------------------------------------------------------------------------
# F3: Exact CF folding & slow-pole locally varying all-prime series
# ---------------------------------------------------------------------------

def monic_fj_valuation(r, j, p):
    """Exact nu_{r, j, p} = (r - j) + v_p(f_{r, j}(p / (1 - p))) where
    f_{r, j}(T) = sum_{i=0}^j C(r, i) T^(j - i) is monic in Z[T]."""
    tp = Fraction(p, 1 - p)
    val = sum(comb(r, i) * (tp ** (j - i)) for i in range(j + 1))
    assert val != 0  # guaranteed for odd prime p by rational root theorem
    return (r - j) + vp_frac(val, p)


def check_f3_cf_folding_and_local_series():
    """Exact certificates for Theorem 3.1 (CF folding lemma) and Theorem 3.2
    (slow-pole locally varying full-density all-prime series V(w), including exact
    theorem schedules and C3 monic-polynomial p-adic valuation tests with p | C(r, j))."""
    c1_checks = 0
    c_gen_checks = 0
    for q in range(3, 25):
        for p in range(1, q // 2 + 1):
            if gcd(p, q) != 1:
                continue
            u = Fraction(p, q)
            a = cf_canonical(u)[1:]
            if a[0] < 2 or a[-1] < 2:
                continue
            Au = max(a)
            for sign in (1, -1):
                for dz in range(2, 12):
                    v = u + Fraction(sign, dz * q * q)
                    av = cf_canonical(v)[1:]
                    expected_last = (a[0] - 1) if (len(a) == 1 and sign == -1) else a[0]
                    assert max(av) == max(Au, dz - 1) and av[-1] == expected_last >= 2
                    c1_checks += 1
                for c in range(2, 6):
                    for dz in range(2 * c + 1, 2 * c + 10):
                        if gcd(c, dz) != 1:
                            continue
                        v = u + Fraction(sign * c, dz * q * q)
                        av = cf_canonical(v)[1:]
                        assert max(av) <= max(dz // c, c * c * (Au + 2) - 1)
                        c_gen_checks += 1

    # Theorem 3.2: exact theorem schedules (kappa, m_j, P_k), regrouping, and C3 monic-polynomial depths
    kappa = (2, 4, 7, 11, 16, 22)  # strictly increasing gaps 2, 3, 4, 5, 6
    kappa_to_m = {k: m + 1 for m, k in enumerate(kappa)}

    def e_of_k(k):
        return sum(1 for km in kappa if km <= k)

    def P_of_k(k):
        ek = e_of_k(k)
        # 2^(floor(log2(1 + ek)))
        cand = 1 << ((1 + ek).bit_length() - 1)
        return cand if 2 * cand <= (1 << k) else 1

    # Verify exact nu_{r, j, p} values including p | C(r, j) cases
    assert monic_fj_valuation(3, 1, 3) == 3
    assert monic_fj_valuation(3, 2, 3) == 2
    assert monic_fj_valuation(3, 3, 3) == 0
    assert monic_fj_valuation(4, 2, 3) == 4  # 6*t^2 + 4*t^3 = 0 at t = -3/2, f_{4,2}(-3/2) = 9/4
    assert monic_fj_valuation(2, 1, 3) == 1
    assert monic_fj_valuation(2, 2, 3) == 0

    padic_depth_checks = 0
    exact_frac_depth_checks = 0

    for b, p in ((2, 3), (3, 5), (6, 5)):
        # 1. Exact auxiliary prime schedule m_j = 1 + max(m_{j-1}, 4 * ceil(log2(prod ell_i)))
        aux_gen = primes_away(b * p)
        ells = [next(aux_gen) for _ in range(12)]
        m_sched = []
        prod_ell = 1
        prev_m = 0
        for ell in ells:
            prod_ell *= ell
            ceil_log2 = (prod_ell - 1).bit_length()  # exact ceil(log2(prod_ell)) for prod_ell >= 2
            assert 2 ** (ceil_log2 - 1) < prod_ell <= 2 ** ceil_log2
            mj = 1 + max(prev_m, 4 * ceil_log2)
            assert prod_ell ** 4 <= 2 ** mj
            m_sched.append(mj)
            prev_m = mj
        if (b, p) == (3, 5):
            assert ells[0] == 2 and m_sched[0] == 5  # matches note's exact ceil(log2) formula!
        m_to_ell = {mj: ell for mj, ell in zip(m_sched, ells)}

        rad_b = prod(r for r in range(2, b + 1)
                     if b % r == 0 and all(r % j for j in range(2, isqrt(r) + 1)))
        t_ord = mult_order(b, p)
        a0 = vp(b ** t_ord - 1, p)
        assert a0 == 1

        # Verify auxiliary-prime CRT construction at m = m_sched[0]
        m1 = m_sched[0]
        mu1 = m_to_ell[m1]
        pole1 = p ** m1
        mod1 = rad_b * mu1
        # Use a representative shift exponent 2^k with k = 20
        u_aux = 1 + mod1 * (((mu1 * pow(b, 1 << 20, pole1) - 1) * pow(mod1, -1, pole1)) % pole1)
        assert u_aux % pole1 == (mu1 * pow(b, 1 << 20, pole1)) % pole1
        assert u_aux % mod1 == 1 and 0 < Fraction(u_aux, pole1 * mu1) <= rad_b

        # 2. Build exact c_k for k = 1..22 using the exact theorem formulas
        c_map = {}
        D_map = {}
        cur_D = 1
        for k in range(1, 23):
            if k in kappa_to_m:
                m_idx = kappa_to_m[k]
                mu = m_to_ell.get(m_idx, 1)
                pole = p ** m_idx
                mod = rad_b * mu
                # Compute b^(2^k) mod pole efficiently by modular exponentiation
                b_pow_mod = pow(b, 1 << k, pole)
                res = ((mu * b_pow_mod - 1) * pow(mod, -1, pole)) % pole
                u_val = 1 + mod * res
                c_map[k] = Fraction(u_val, pole * mu)
                assert 0 < c_map[k] <= rad_b
                cur_D = (p ** m_idx) * (cur_D // (p ** vp(cur_D, p))) * mu
            else:
                c_map[k] = Fraction(2, 1)
            D_map[k] = cur_D

        # Verify exact P_k power-of-two order valuations through k = 22
        for k in range(1, 23):
            Pk = P_of_k(k)
            assert (Pk & (Pk - 1)) == 0 and (1 << k) % Pk == 0
            val = b ** Pk - 1
            assert vp(val, p) <= a0
            Q0 = val
            while Q0 % p == 0:
                Q0 //= p
            for r_prime in range(2, b + 1):
                if b % r_prime == 0 and all(r_prime % j for j in range(2, isqrt(r_prime) + 1)):
                    while Q0 % r_prime == 0:
                        Q0 //= r_prime
            for r_deg in (1, 2, 3):
                if Q0 > 1:
                    assert mult_order(b, Q0 ** r_deg) % p != 0

        # 3. Exact raw-vs-regrouped identity, positivity, all-site denominators, and injectivity on k=1..7
        # Exact P_k on k=1..7 for kappa=(2,4,7,...): P = {1:1, 2:2, 3:2, 4:2, 5:2, 6:2, 7:4}
        assert [P_of_k(k) for k in range(1, 8)] == [1, 2, 2, 2, 2, 2, 4]
        pattern_generators = [
            lambda k, Pk: tuple(1 for _ in range(Pk)),                               # all-ones baseline
            lambda k, Pk: tuple(1 + ((k + i) % 2) for i in range(Pk)),               # alternating local pattern
            lambda k, Pk: tuple(1 + ((k * i + 1) % 2) for i in range(Pk)),           # second varying pattern
        ]
        vals_seen = []
        for gen in pattern_generators:
            raw = Fraction(0)
            regroup = Fraction(0)
            prev_lam = Fraction(0)
            for k in range(1, 8):
                nk = 1 << k
                Pk = P_of_k(k)
                w_word = gen(k, Pk)
                assert len(w_word) == Pk
                W_int = sum(w_word[i] * (b ** (Pk - 1 - i)) for i in range(Pk))
                lam = Fraction(W_int, b ** Pk - 1)
                dk = c_map[k] + lam - prev_lam
                if k in kappa_to_m and kappa_to_m[k] > a0:
                    assert vp(dk.denominator, p) == kappa_to_m[k]
                elif k not in kappa_to_m:
                    assert dk >= 1  # strictly positive even at k=1 and b=2
                raw += c_map[k] / (b ** nk)
                assert (raw * (b ** nk)).denominator == D_map[k]
                regroup += dk / (b ** nk)
                for offset in range(1, nk + 1):
                    site_coeff = w_word[(offset - 1) % Pk]
                    raw += Fraction(site_coeff, b ** (nk + offset))
                    assert (raw * (b ** (nk + offset))).denominator == D_map[k]
                assert raw == regroup - lam / (b ** (2 * nk))
                prev_lam = lam
            vals_seen.append(raw)
        assert len(set(vals_seen)) == len(pattern_generators)

        # 4. C3 exact monic-polynomial valuation verification (literal Fraction at M=4 for (b,p)=(2,3))
        if (b, p) == (2, 3):
            M_lit = 4  # kappa_4 = 11, kappa_3 = 7
            # Build exact Fraction d_k for k=1..11 using all-ones baseline (where delta_m in Z_3)
            d_lit = {}
            prev_l = Fraction(0)
            for k in range(1, 12):
                Pk = P_of_k(k)
                lam = Fraction(sum(b ** (Pk - 1 - i) for i in range(Pk)), b ** Pk - 1)
                d_lit[k] = c_map[k] + lam - prev_l
                prev_l = lam
            # Exact unshifted terms a_k = d_k / b^(2^k); v_p(b^n * S_n) == v_p(S_n)
            a_lit = {k: d_lit[k] / (b ** (1 << k)) for k in range(1, 12)}
            # Precompute pairwise sums for fast degree 2, 3, 4 exact Fraction convolutions
            c2 = Counter()
            for k1, v1 in a_lit.items():
                for k2, v2 in a_lit.items():
                    c2[(1 << k1) + (1 << k2)] += v1 * v2
            c3 = Counter()
            for s2, v2 in c2.items():
                for k3, v3 in a_lit.items():
                    c3[s2 + (1 << k3)] += v2 * v3
            c4 = Counter()
            for s2a, v2a in c2.items():
                for s2b, v2b in c2.items():
                    c4[s2a + s2b] += v2a * v2b
            lit_convs = {2: c2, 3: c3, 4: c4}
            # Check exact 3-depths at interior shifts of j-th intervals (matches referee's C3 table!)
            for r_deg, j_idx, exp_depth in (
                (2, 1, 7), (2, 2, 8),
                (3, 1, 9), (3, 2, 10), (3, 3, 12),
                (4, 2, 12),
            ):
                assert exp_depth == r_deg * M_lit - monic_fj_valuation(r_deg, j_idx, 3)
                n_shift = j_idx * (1 << 11) + (r_deg - j_idx) * (1 << 7) + 7
                pref = sum(v for pos, v in lit_convs[r_deg].items() if pos <= n_shift)
                assert -vp_frac(pref, 3) == exp_depth
                exact_frac_depth_checks += 1

        # 5. C3 exact p-adic modular arithmetic verification at M = 6 (kappa_6 = 22, M - a0 = 5 > max nu = 4)
        #    across multiple locally varying patterns w and non-monomial P(X) = p*X^3 + 2*X^2 + X!
        M_mod = 6  # kappa_6 = 22, kappa_5 = 16
        K_prec = 4 * M_mod + 8
        P_MOD = p ** K_prec
        for gen in pattern_generators:
            d_mod_terms = {}
            prev_l = Fraction(0)
            for k in range(1, 23):
                Pk = P_of_k(k)
                w_word = gen(k, Pk)
                W_int = sum(w_word[i] * (b ** (Pk - 1 - i)) for i in range(Pk))
                lam = Fraction(W_int, b ** Pk - 1)
                dk = c_map[k] + lam - prev_l
                prev_l = lam
                # Exact image of p^M_mod * d_k * b^(-2^k) in Z / p^K_prec Z
                scaled = dk * (p ** M_mod)
                assert scaled.denominator % p != 0
                b_inv = pow(b, -(1 << k), P_MOD)
                val_mod = (scaled.numerator * pow(scaled.denominator, -1, P_MOD) * b_inv) % P_MOD
                d_mod_terms[k] = val_mod

            # Build exact degree 1, 2, 3, 4 convolutions modulo P_MOD (each term carries factor p^(r * M_mod))
            m1_c = {1 << k: v for k, v in d_mod_terms.items()}
            m2_c = Counter()
            for p1, v1 in m1_c.items():
                for p2, v2 in m1_c.items():
                    m2_c[p1 + p2] = (m2_c[p1 + p2] + v1 * v2) % P_MOD
            m3_c = Counter()
            for p2, v2 in m2_c.items():
                for p1, v1 in m1_c.items():
                    m3_c[p2 + p1] = (m3_c[p2 + p1] + v2 * v1) % P_MOD
            m4_c = Counter()
            for p2a, v2a in m2_c.items():
                for p2b, v2b in m2_c.items():
                    m4_c[p2a + p2b] = (m4_c[p2a + p2b] + v2a * v2b) % P_MOD
            mod_convs = {1: m1_c, 2: m2_c, 3: m3_c, 4: m4_c}

            for r_deg in (1, 2, 3, 4):
                for j_idx in range(1, r_deg + 1):
                    nu = monic_fj_valuation(r_deg, j_idx, p)
                    assert M_mod - a0 > nu  # theorem's strict threshold holds uniformly in w!
                    n_shift = j_idx * (1 << 22) + (r_deg - j_idx) * (1 << 16) + 17
                    tot = sum(v for pos, v in mod_convs[r_deg].items() if pos <= n_shift) % P_MOD
                    assert tot != 0 and vp(tot, p) == nu
                    padic_depth_checks += 1

            # Also test non-monomial P(X) = p*X^3 + 2*X^2 + X (leading coeff has v_p(gamma_3) = 1)
            for j_idx in (1, 2, 3):
                nu = monic_fj_valuation(3, j_idx, p)
                n_shift = j_idx * (1 << 22) + (3 - j_idx) * (1 << 16) + 17
                s3 = sum(v for pos, v in m3_c.items() if pos <= n_shift) % P_MOD
                s2 = sum(v for pos, v in m2_c.items() if pos <= n_shift) % P_MOD
                s1 = sum(v for pos, v in m1_c.items() if pos <= n_shift) % P_MOD
                # Multiply P(V) by p^(3*M_mod): p * s3 + 2 * p^M_mod * s2 + p^(2*M_mod) * s1
                tot_P = (p * s3 + 2 * (p ** M_mod) * s2 + (p ** (2 * M_mod)) * s1) % P_MOD
                assert tot_P != 0 and vp(tot_P, p) == 1 + nu  # exact depth = 3*M_mod - 1 - nu
                padic_depth_checks += 1

    print(f"F3 CF folding & local series: {c1_checks} zero-loss c=1 folds, "
          f"{c_gen_checks} general c>=2 folds; exact theorem schedules, regrouping, "
          f"order valuations, and C3 monic-polynomial pole depths verified "
          f"({exact_frac_depth_checks} literal Fraction + {padic_depth_checks} exact p-adic checks, "
          f"including p | C(r, j) cases (3,1,3), (3,2,3), (4,2,3))")


def main():
    check_f1_low_residue_packet_barrier()
    check_f1_gap_certificate_iff_and_cube_drops()
    check_f2_kloosterman_and_hyperbola()
    check_f2_block_measures_and_exponents()
    check_f3_cf_folding_and_local_series()
    print("All Phase 25 Track F exact finite certificates passed.")


if __name__ == "__main__":
    main()
