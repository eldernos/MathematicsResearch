#!/usr/bin/env python3
"""Exact arithmetic checks and targeted controls for Phase 15 tracks B/G:
higher-rank Fredholm identities, finite-width projections, solenoid costs,
induced return equivalences (including unfinished runs), and sparse-digit
counterexamples.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb, cos, gcd, isqrt, lcm, log, pi, prod
import sys


from discrepancy_experiments import log_bits as certified_log2_bits
from localized_certificate import prime as is_prime


def primes_up_to(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if is_prime(p)]


def v_p(n: int, p: int) -> int:
    """Exact p-adic valuation of a nonzero integer n."""
    assert n != 0
    n = abs(n)
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def v_p_frac(q: Fraction, p: int) -> int:
    assert q != 0
    return v_p(q.numerator, p) - v_p(q.denominator, p)


# ---------------------------------------------------------------------------
# 1. Higher-rank Fredholm identities, box telescoping, and Bernoulli operators
# ---------------------------------------------------------------------------

def smooth_numbers_box(primes: tuple[int, ...], limits: tuple[int, ...]) -> list[int]:
    """All m = prod p_i^{a_i} with 0 <= a_i < limits[i]."""
    res = [1]
    for p, lim in zip(primes, limits):
        nxt = []
        for x in res:
            pw = 1
            for _ in range(lim):
                nxt.append(x * pw)
                pw *= p
        res = nxt
    return sorted(res)


def subsets_with_mobius(primes: tuple[int, ...]) -> list[tuple[int, int]]:
    """Return pairs (prod_{p in D} p, (-1)^|D|) for all subsets D of primes."""
    out = []
    for k in range(len(primes) + 1):
        sign = -1 if (k % 2 == 1) else 1
        for sub in combinations(primes, k):
            out.append((prod(sub, start=1), sign))
    return out


def verify_fredholm_identities() -> dict[str, object]:
    """Verify exact higher-rank box telescoping, closed-form mixed differences at z=1/2,
    and simultaneous Bernoulli eigenfunctions for commuting transfer operators L_p.
    """
    # (a) Exact polynomial verification of box telescoping on z^1..z^M for P={2,3} and {2,3,5}
    # For arbitrary weights w(p) = 1/p^s (s=0 and s=1) and arbitrary coefficients c_n.
    for P, A, s in [
        ((2,), (4,), 0),
        ((2, 3), (4, 3), 0),
        ((2, 3), (4, 3), 1),
        ((2, 3, 5), (3, 2, 2), 1),
    ]:
        # Test on F(z) = sum_{n=1}^N c_n z^n with nontrivial rational coefficients c_n = 1/(n+1)
        # and also c_n = 1/n (logarithm) and c_n = 1_{n in <P>} (Fredholm series).
        z = Fraction(1, 2)
        N_deg = 40

        def eval_F(val: Fraction, mode: str) -> Fraction:
            total = Fraction(0)
            zp = val
            for n in range(1, N_deg + 1):
                if mode == "log":
                    coeff = Fraction(1, n)
                elif mode == "nonmult":
                    coeff = Fraction(1, n + 2)
                else:
                    # Fredholm indicator for <P>
                    m = n
                    for p in P:
                        while m % p == 0:
                            m //= p
                    coeff = Fraction(1, n**s) if m == 1 else Fraction(0)
                total += coeff * zp
                zp *= val
            return total

        subs = subsets_with_mobius(P)

        def eval_delta_F(val: Fraction, mode: str) -> Fraction:
            return sum(
                Fraction(mu, D**s) * eval_F(val**D, mode) for D, mu in subs
            )

        for mode in ("log", "nonmult", "fredholm"):
            lhs_box = sum(
                Fraction(1, m**s) * eval_delta_F(z**m, mode)
                for m in smooth_numbers_box(P, A)
            )
            lhs = eval_F(z, mode) - lhs_box
            rhs = Fraction(0)
            for k in range(1, len(P) + 1):
                sign = 1 if (k % 2 == 1) else -1
                for idxs in combinations(range(len(P)), k):
                    M_prod = prod(P[j] ** A[j] for j in idxs)
                    rhs += Fraction(sign, M_prod**s) * eval_F(z**M_prod, mode)
            assert lhs == rhs, f"Box telescoping mismatch for P={P}, s={s}, mode={mode}"

    # (b) Exact closed-form values of mixed differences g_{P,1}(1/2) = sum_{gcd(d,prod P)=1} 2^{-d}/d
    # Formula: g_{P,1}(1/2) = (1/L) * ln(Q_P), where L = prod P and
    # Q_P = prod_{D subseteq P} (1 - 2^{-D})^{-mu(D) * L / D}.
    closed_forms = {}
    for P in ((2,), (3,), (2, 3), (2, 3, 5)):
        L = prod(P)
        Q_num = Fraction(1)
        for D, mu in subsets_with_mobius(P):
            exp = -mu * (L // D)
            factor = Fraction(2**D - 1, 2**D)
            Q_num *= factor**exp if exp >= 0 else (Fraction(1) / factor) ** (-exp)
        # Direct partial sum of sum_{gcd(d,L)=1} 2^{-d}/d up to d=80
        direct = sum(
            Fraction(1, d * (1 << d)) for d in range(1, 81) if gcd(d, L) == 1
        )
        approx_closed = log(float(Q_num)) / L
        assert abs(float(direct) - approx_closed) < 1e-15
        closed_forms[P] = (L, Q_num, approx_closed)

    assert closed_forms[(2,)][1] == Fraction(3, 1)
    assert closed_forms[(3,)][1] == Fraction(7, 1)
    assert closed_forms[(2, 3)][1] == Fraction(21, 1)

    # (c) Exact Bernoulli polynomials B_m(x) and Raabe identity L_p(B_m) = p^{-m} B_m
    # Compute Bernoulli numbers B_k via exact recursion sum_{j=0}^k C(k+1, j) B_j = 0.
    max_m = 6
    B_num: list[Fraction] = [Fraction(1)]
    for k in range(1, max_m + 1):
        s_val = sum(comb(k + 1, j) * B_num[j] for j in range(k))
        B_num.append(-s_val / (k + 1))

    def eval_bernoulli_poly(m: int, x: Fraction) -> Fraction:
        return sum(comb(m, k) * B_num[k] * (x ** (m - k)) for k in range(m + 1))

    for p in (2, 3, 5):
        for m in range(max_m + 1):
            for x in (Fraction(0), Fraction(1, 3), Fraction(2, 5), Fraction(7, 11)):
                lp_bm = sum(eval_bernoulli_poly(m, (x + j) / p) for j in range(p)) / p
                expected = Fraction(1, p**m) * eval_bernoulli_poly(m, x)
                assert lp_bm == expected, f"Raabe mismatch at p={p}, m={m}, x={x}"

    return {"closed_forms": closed_forms, "bernoulli_verified_up_to": max_m}


# ---------------------------------------------------------------------------
# 2. Finite-width projections Pi_{P,W}(1/2) and mixed-difference prime bands
# ---------------------------------------------------------------------------

def multiplicative_order(a: int, m: int) -> int:
    """Exact multiplicative order of a mod m (requires gcd(a,m)=1)."""
    if m == 1:
        return 1
    assert gcd(a, m) == 1
    # Factor m by trial division (sufficient for our exact test range)
    def factorize(n: int) -> dict[int, int]:
        fac: dict[int, int] = {}
        d = 2
        while d * d <= n:
            while n % d == 0:
                fac[d] = fac.get(d, 0) + 1
                n //= d
            d += 1
        if n > 1:
            fac[n] = fac.get(n, 0) + 1
        return fac

    def prime_power_order(base: int, p: int, e: int) -> int:
        mod = p**e
        phi = (p - 1) * (p ** (e - 1))
        ord_val = phi
        for q in factorize(phi):
            while ord_val % q == 0 and pow(base, ord_val // q, mod) == 1:
                ord_val //= q
        return ord_val

    res = 1
    for p, e in factorize(m).items():
        res = lcm(res, prime_power_order(a, p, e))
    return res


def verify_finite_width_projections() -> dict[str, object]:
    """Verify:
    1) Exact 3-valuation v_3(den(2^N Pi_{3,W}^{(N)}(1/2))) = floor(log_3 N) on ALL N in [3^k, 3^{k+1}).
    2) Quantitative width-vs-horizon costs: log(D_W)/W and ord_{D_W_odd}(2).
    3) Pure mixed difference g_{P,1}^{(N)}(1/2) (and -1/2) still has full top prime band (N/2, N].
    """
    # 1) Exact v_3 survival for Pi_{{3}, W}(1/2) across all N in [3, 242]
    max_N = 242  # covers shells k=1,2,3,4 ([3,9), [9,27), [27,81), [81,243))
    widths_checked = (1, 2, 5, 10, 20)
    for W in widths_checked:
        # Support elements n = d * 3^j <= max_N with 3 \nmid d and 1 <= d <= W
        support = set()
        for d in range(1, W + 1):
            if d % 3 != 0:
                val = d
                while val <= max_N:
                    support.add(val)
                    val *= 3
        D_W = lcm(*(d for d in range(1, W + 1) if d % 3 != 0))
        prefix = Fraction(0)
        shell_k = 0
        next_pow3 = 3
        for N in range(1, max_N + 1):
            prefix *= 2
            if N in support:
                prefix += Fraction(1, N)
            if N == next_pow3:
                shell_k += 1
                next_pow3 *= 3
            if N >= 3:
                q = prefix.denominator
                assert v_p(q, 3) == shell_k, f"Unexpected cancellation at W={W}, N={N}"
                assert (D_W * (3**shell_k)) % q == 0

    # Check exact approximation error bound 0 < ln(2) - Pi_{{3},W}(1/2) <= 2^{-W}/(W+1)
    # via exact partial sums up to 160 bits.
    ln2_tail_ub = Fraction(1, 161 * (1 << 160))
    width_errors = []
    for W in (2, 5, 10, 20, 40):
        # Sum of omitted terms d > W, 3 \nmid d, d*3^j <= 160
        omitted = Fraction(0)
        for d in range(W + 1, 161):
            if d % 3 != 0:
                val = d
                while val <= 160:
                    omitted += Fraction(1, val * (1 << val))
                    val *= 3
        ub = Fraction(1, (W + 1) * (1 << W))
        assert omitted > 0 and omitted + ln2_tail_ub <= ub
        width_errors.append((W, float(omitted), float(ub)))

    # Extended width-cost table up to W=120
    width_costs = []
    for W in (10, 20, 40, 80, 120):
        D_W = lcm(*(d for d in range(1, W + 1) if d % 3 != 0))
        D_W_odd = D_W >> v_p(D_W, 2)
        ord2 = multiplicative_order(2, D_W_odd)
        ub_val = 1.0 / ((W + 1) * float(1 << W))
        width_costs.append((W, ub_val, log(D_W) / W, D_W.bit_length(), ord2, log(ord2) / W))

    # Also check rank-2 finite-width projection Pi_{{2,3}, W}(1/2) for W=1,5,7:
    # count exact v_3(q_N) drops below floor(log_3 N) on [3, 242].
    rank2_drops = {}
    for W in (1, 5, 7):
        support23 = set()
        for d in range(1, W + 1):
            if gcd(d, 6) == 1:
                a = d
                while a <= max_N:
                    b = a
                    while b <= max_N:
                        support23.add(b)
                        b *= 3
                    a *= 2
        pref = Fraction(0)
        drops = 0
        sk = 0
        np3 = 3
        for N in range(1, max_N + 1):
            pref *= 2
            if N in support23:
                pref += Fraction(1, N)
            if N == np3:
                sk += 1
                np3 *= 3
            if N >= 3 and v_p(pref.denominator, 3) < sk:
                drops += 1
        rank2_drops[W] = drops

    # 3) Verify pure mixed difference g_{{2,3},1}^{(N)}(1/2) (and - 1/2) retains ALL primes p in (N/2, N]
    band_checks = []
    for N in (64, 128, 256):
        val_full = Fraction(0)
        for d in range(1, N + 1):
            val_full *= 2
            if gcd(d, 6) == 1:
                val_full += Fraction(1, d)
        val_minus_half = val_full - Fraction(1 << (N - 1), 1)
        top_primes = [p for p in range(N // 2 + 1, N + 1) if is_prime(p)]
        for p in top_primes:
            assert val_full.denominator % p == 0
            assert val_minus_half.denominator % p == 0
        band_checks.append((N, len(top_primes), log(val_full.denominator) / N))

    return {
        "widths_checked": widths_checked,
        "max_N_v3": max_N,
        "width_errors": width_errors,
        "width_costs": width_costs,
        "rank2_drops": rank2_drops,
        "band_checks": band_checks,
    }


# ---------------------------------------------------------------------------
# 3. Solenoid representation and quantitative costs
# ---------------------------------------------------------------------------

def p_adic_principal_part(q: Fraction, p: int) -> Fraction:
    """Return the unique {q}_p in Z[1/p] cap [0, 1) such that q - {q}_p in Z_p."""
    if not q:
        return Fraction(0)
    e = v_p_frac(q, p)
    if e >= 0:
        return Fraction(0)
    pe = p ** (-e)
    # q = num / (pe * den_prime), where gcd(den_prime, p) = 1
    num = q.numerator
    den_prime = q.denominator // pe
    inv = pow(den_prime, -1, pe)
    u = (num * inv) % pe
    return Fraction(u, pe)


def two_stride_prefix(N: int) -> Fraction:
    """Two-stride ln(2) prefix Y_N = 2^N (2 A_2(N) - A_{3,-}(N))."""
    total = Fraction(0)
    for j in range(1, N // 2 + 1):
        total += Fraction(2 * (1 << (N - 2 * j)), j)
    for j in range(1, N // 3 + 1):
        sign = 1 if (j % 2 == 1) else -1
        total += Fraction(sign * (1 << (N - 3 * j)), j)
    return total


def gaussian_5_12_prefix(N: int) -> Fraction:
    """Phase 13/14E optimal 5/12-rate Gaussian prefix S_5(N) * 2^N."""
    # Y_N(5) = 2^N * [2 sum_{2j<=N} 4^{-j}/j - 6 sum_{3j<=N} (-8)^{-j}/j
    #                 + 10 sum_{4j<=N} 16^{-j}/j - 10 sum_{5j<=2N} Re(((1+i)/8)^j)/j]
    # Note: 2^{ceil(5j/2)} Re(((1+i)/8)^j) repeats (1, 0, -1, -1, -1, 0, 1, 1) for j >= 1.
    w_pat = (1, 0, -1, -1, -1, 0, 1, 1)
    total = Fraction(0)
    for j in range(1, N // 2 + 1):
        total += Fraction(2 * (1 << (N - 2 * j)), j)
    for j in range(1, N // 3 + 1):
        sign = -1 if (j % 2 == 1) else 1
        total += Fraction(-6 * sign * (1 << (N - 3 * j)), j)
    for j in range(1, N // 4 + 1):
        total += Fraction(10 * (1 << (N - 4 * j)), j)
    for j in range(1, (2 * N) // 5 + 1):
        w = w_pat[(j - 1) % 8]
        if w != 0:
            e_j = (5 * j + 1) // 2
            total -= Fraction(10 * w * (1 << (N - e_j)), j)
    return total


def verify_solenoid_identities_and_costs() -> dict[str, object]:
    """Verify:
    1) Exact partial-fraction / Delta(Z[1/P])-invariance of solenoid characters chi_r.
    2) Exact local-global split [(Y_n, 0)] = [(R_S(n), -P_S(n))] in Sigma_S.
    3) Quantitative solenoid lifting costs (rank |P| and log(q_N)/N) across
       standard (rate 1), two-stride (rate 1/2), and Gaussian (rate 5/12) models.
    """
    # 1) Character invariance on Delta(Z[1/P]) for P = {2, 3, 5}
    P = (2, 3, 5)
    test_rs = [Fraction(a, (2**e2) * (3**e3) * (5**e5))
               for a in (-7, -1, 1, 5, 11)
               for e2 in (0, 2) for e3 in (0, 1) for e5 in (0, 1)]
    for r in test_rs:
        for s in (Fraction(1, 6), Fraction(7, 30), Fraction(-13, 60)):
            rs = r * s
            diff = rs - sum(p_adic_principal_part(rs, p) for p in P)
            assert diff.denominator == 1, f"Character invariance failed at r={r}, s={s}"

    # 2) Local-global split Y_n = P_S(n) + R_S(n) in Sigma_S for S = (5, 7)
    S = (5, 7)
    for n in range(30, 61):
        Y_n = two_stride_prefix(n)
        P_S = sum(p_adic_principal_part(Y_n, p) for p in S)
        R_S = Y_n - P_S
        # Verify R_S is S-integral (denominator coprime to 5 and 7)
        assert gcd(R_S.denominator, 35) == 1
        # Compare characters in several inverse-limit coordinates on the two representatives.
        for frequency in (Fraction(1), Fraction(1, 5), Fraction(-2, 49), Fraction(11, 35)):
            real_phase = frequency * R_S
            local_phase = sum(p_adic_principal_part(-frequency * P_S, p) for p in S)
            assert (frequency * Y_n - (real_phase - local_phase)).denominator == 1

    # 3) Quantitative solenoid lifting costs (exact prime rank and log denominator / N)
    cost_rows = []
    for N in (128, 256, 512):
        # Standard prefix R_N
        R_N = Fraction(0)
        for j in range(1, N + 1):
            R_N = 2 * R_N + Fraction(1, j)
        Y2_N = two_stride_prefix(N)
        YG_N = gaussian_5_12_prefix(N)

        def prime_rank(q: int, limit: int) -> int:
            return sum(1 for p in primes_up_to(limit) if q % p == 0)

        r_std = prime_rank(R_N.denominator, N)
        r_two = prime_rank(Y2_N.denominator, N // 2)
        r_gau = prime_rank(YG_N.denominator, N // 2)
        cost_rows.append(
            (
                N,
                r_std,
                log(R_N.denominator) / N,
                r_two,
                log(Y2_N.denominator) / N,
                r_gau,
                log(YG_N.denominator) / N,
            )
        )

    return {"solenoid_cost_rows": cost_rows}


# ---------------------------------------------------------------------------
# 4. Induced returns, unfinished-run equivalences, and targeted controls
# ---------------------------------------------------------------------------

def run_statistics_from_bits(bits: str, N: int, L_values: tuple[int, ...]) -> dict[str, object]:
    """Given a binary string of length >= N+1 (so bits[0..N] determine transitions at 0..N-1),
    compute exact induced-return statistics on [0, N), separating completed runs and the
    unfinished run u_tilde_N = N - t_{K(N)}.
    """
    assert len(bits) >= N + 1
    trans = [i for i in range(N) if bits[i] != bits[i + 1]]
    K = len(trans)
    assert K >= 1
    r0 = trans[0]
    completed = [trans[i + 1] - trans[i] for i in range(K - 1)]
    u_tilde = N - trans[-1]  # 1 <= u_tilde <= r_K
    # Exact telescoping check:
    assert r0 + sum(completed) + u_tilde == N

    # Verify aggregate age W_N = sum_{i=0}^N A_i (using AggregateGaps.lean convention)
    # Note: A_0 = 0, A_{n+1} = 0 if trans at n else A_n + 1.
    age = 0
    W_N = 0
    for i in range(N):
        if bits[i] != bits[i + 1]:
            age = 0
        else:
            age += 1
        W_N += age
    # Exact identity from gap_moments in AggregateGaps.lean:
    # (r0 + 1)^2 + sum_{r in completed} r^2 + u_tilde^2 == (N + 1) + 2 * W_N
    S2_all = (r0 + 1) ** 2 + sum(r * r for r in completed) + (u_tilde) ** 2
    # Wait: check exact alignment with gapAge!
    # At i = trans[0] = r0: gapAge(r0) = r0, so (gapAge(r0)+1) = r0 + 1.
    # At i = trans[m] (m>=1): gapAge(trans[m]) = trans[m] - trans[m-1] - 1 = r_m - 1, so gapAge+1 = r_m.
    # At i = N: gapAge(N) = N - trans[-1] - 1 = u_tilde - 1, so gapAge(N)+1 = u_tilde.
    assert S2_all == (N + 1) + 2 * W_N

    S2 = sum(r * r for r in completed) + u_tilde * u_tilde
    S3 = sum(r**3 for r in completed) + u_tilde**3

    excess_full = {}
    excess_comp = {}
    mass_full = {}
    for L in L_values:
        ec = sum(max(0, r - L) for r in completed)
        ef = ec + max(0, u_tilde - L)
        mf = sum(r for r in completed if r > L) + (u_tilde if u_tilde > L else 0)
        # Exact unfinished-run inequality: N - r0 <= L * K + E_L(N)
        assert N - r0 <= L * K + ef
        excess_full[L] = ef
        excess_comp[L] = ec
        mass_full[L] = mf

    return {
        "N": N,
        "K": K,
        "tau": K / N,
        "r0": r0,
        "u_tilde": u_tilde,
        "mean_completed": sum(completed) / len(completed) if completed else 0.0,
        "W_N": W_N,
        "S2": S2,
        "S3": S3,
        "excess_full": excess_full,
        "excess_comp": excess_comp,
        "mass_full": mass_full,
    }


def verify_induced_returns_and_controls() -> dict[str, object]:
    L_vals = (1, 2, 4, 8)

    # Control 1: Certified actual binary digits of ln(2) up to N = 16384
    max_N = 16384
    ln2_bits = certified_log2_bits(max_N + 64)
    ln2_rows = []
    for exp in (8, 10, 12, 14):
        N = 1 << exp
        st = run_statistics_from_bits(ln2_bits, N, L_vals)
        ln2_rows.append(st)

    # Numerical check of the two-sided spike bound on certified cylinders.
    trans_all = [i for i in range(1000) if ln2_bits[i] != ln2_bits[i + 1]]
    for idx in range(min(200, len(trans_all) - 1)):
        t = trans_all[idx]
        r_E = trans_all[idx + 1] - t
        # Approximate y = {2^t ln 2} from the next 52 certified bits
        y = int(ln2_bits[t : t + 52], 2) / (1 << 52)
        v_y = -log(abs(cos(pi * y)))
        lo = (r_E + 1) * log(2) - log(pi)
        hi = (r_E + 1) * log(2)
        assert lo - 1e-12 < v_y < hi + 1e-12, f"Spike bound failed at t={t}"

    # Control 2: Fredholm-Kempner constant K = sum_{j>=0} 2^{-2^j}
    # Fractional bit at index i >= 0 (representing 2^{-(i+1)}) is 1 iff i+1 is a power of 2.
    fk_bits_list = ["0"] * (max_N + 64)
    pw = 1
    while pw <= max_N + 64:
        fk_bits_list[pw - 1] = "1"
        pw <<= 1
    fk_bits = "".join(fk_bits_list)
    fk_rows = []
    for exp in (8, 10, 12, 14):
        N = 1 << exp
        st = run_statistics_from_bits(fk_bits, N, L_vals)
        fk_rows.append(st)

    # Verify K approaches extremal constants S_2(2^m)/2^{2m} -> 1/3, S_3(2^m)/2^{3m} -> 1/7, W/N^2 -> 1/6
    # Wait: in K, each isolated '1' at position 2^j (index 2^j - 1) creates TWO adjacent transitions
    # (0->1 at 2^j - 2 and 1->0 at 2^j - 1) followed by a run of length 2^j - 1!
    # Check exact asymptotics at N = 16384:
    st_fk_14 = fk_rows[-1]
    assert abs(st_fk_14["S2"] / (16384**2) - 1 / 3) < 1e-3
    assert abs(st_fk_14["S3"] / (16384**3) - 1 / 7) < 1e-3
    assert abs(st_fk_14["W_N"] / (16384**2) - 1 / 6) < 1e-3

    # The rigorous construction uses exponents 4*j + max(j-4,0)^2.
    # The finite sample reaches precisely its first four exceptional blocks.
    dyad_len = (1 << 17) + 16
    dyad_arr = [str(i % 2) for i in range(dyad_len)]
    zero_blocks = []
    for j, k_j in enumerate((4, 8, 12, 16), start=1):
        start = max(2, (1 << k_j) // (j + 1))
        end = (1 << k_j) + 2  # zero bits through index 2^{k_j}+1 => no transition on [start, 2^{k_j}]
        for idx in range(start, end):
            dyad_arr[idx] = "0"
        zero_blocks.append((j, k_j, start, end))
    dyad_bits = "".join(dyad_arr)
    dyad_rows = []
    for m in range(4, 18):
        N = 1 << m
        st = run_statistics_from_bits(dyad_bits, N, (2,))
        dyad_rows.append(
            (
                m,
                N,
                st["tau"],
                st["excess_comp"][2] / N,
                st["excess_full"][2] / N,
                st["u_tilde"] / N,
            )
        )
    # Verify key separation: max completed excess across ALL dyadic cutoffs <= 0.51,
    # while full excess reaches > 0.79 at m=16 (approaching 1 as j -> infinity) and tau drops <= 1/(j+1)
    assert max(row[3] for row in dyad_rows) < 0.52
    assert dyad_rows[-2][4] > 0.79  # m = 16
    assert dyad_rows[-2][2] <= 0.21  # m = 16: tau <= 1/5 + O(2^{-4})

    # Finite equal-run controls for the subquadratic moment inequality.
    upgrade_rows = []
    for exp in (10, 12, 14, 16, 18, 20):
        N = 1 << exp
        R = isqrt(N)
        blocks = (N // R) + 2
        bits_s = "".join(("0" if (b % 2 == 0) else "1") * R for b in range(blocks))
        trans = [i for i in range(N) if bits_s[i] != bits_s[i + 1]]
        K = len(trans)
        comp_runs = [trans[i + 1] - trans[i] for i in range(K - 1)]
        u_tilde = N - trans[-1]
        M = sum(comp_runs)
        S_comp = sum(r * r for r in comp_runs)
        S2 = S_comp + u_tilde * u_tilde
        C_eff = S2 / (N ** 1.5)
        naive_tau = K / N
        t_opt = 0.5 * (S_comp / M)
        best_r = 0.0
        best_L = 1
        for L in range(1, 60):
            if L <= t_opt:
                lhs_sum = sum(min(r, L) for r in comp_runs)
                rhs_bound = L * (M * M) / S_comp
                assert lhs_sum + 1e-9 >= rhs_bound
                r_cand = min(2.0 ** (-(L + 3)), rhs_bound / N)
                if r_cand > best_r:
                    best_r = r_cand
                    best_L = L
        upgrade_rows.append((N, R, K, C_eff, naive_tau, best_L, best_r, best_r / naive_tau))

    return {
        "ln2_rows": ln2_rows,
        "fk_rows": fk_rows,
        "dyad_rows": dyad_rows,
        "upgrade_rows": upgrade_rows,
    }


def main() -> int:
    fred = verify_fredholm_identities()
    fw = verify_finite_width_projections()
    sol = verify_solenoid_identities_and_costs()
    ret = verify_induced_returns_and_controls()

    print("=== 1. Higher-rank Fredholm identities & Bernoulli transfer operators ===")
    for P, (L, Q_num, val) in fred["closed_forms"].items():
        print(f"  P={P}: g_{{P,1}}(1/2) = (1/{L}) * ln({Q_num}) = {val:.12f}")
    print(f"  Box telescoping (s=0,1; log/nonmult/fredholm) and Raabe L_p(B_m)=p^-m B_m (m<=6): PASS")

    print("\n=== 2. Finite-width projections Pi_{3,W}(1/2) & pure mixed-difference bands ===")
    print(f"  Exact v_3(den(2^N Pi_{{3,W}}^{{(N)}}(1/2))) = floor(log_3 N) on all 3<=N<={fw['max_N_v3']} for W in {fw['widths_checked']}: PASS")
    print(f"  Rank-2 Pi_{{2,3}},W(1/2) v_3 drops below floor(log_3 N) on [3,{fw['max_N_v3']}]: {fw['rank2_drops']}")
    print("  Omitted terms through 160 vs full tail bound 2^{-W}/(W+1):")
    for W, om, ub in fw["width_errors"]:
        print(f"    W={W:2d}: partial difference = {om:.6e}  <=  {ub:.6e}")
    print("  W   | 2^{-W}/(W+1) | log(D_W)/W | bits(D_W) | ord_{D_W,odd}(2) | log(ord)/W")
    for W, ub_val, logD_W, bitsD, ord2, log_ord in fw["width_costs"]:
        print(f"  {W:3d} | {ub_val:12.3e} | {logD_W:10.6f} | {bitsD:9d} | {ord2:16d} | {log_ord:10.6f}")
    print("  Pure mixed difference g_{{2,3},1}(1/2) top-band prime survival:")
    for N, cnt, rate in fw["band_checks"]:
        print(f"    N={N:3d}: all {cnt} primes in (N/2, N] survive (also after -1/2); log(q_N)/N = {rate:.6f}")

    print("\n=== 3. Solenoid lifting costs (rank |P| and log(q_N)/N) ===")
    print("  N   | rank_std rate_std | rank_2str rate_2str | rank_G512 rate_G512")
    for row in sol["solenoid_cost_rows"]:
        N, rs, ls, r2, l2, rg, lg = row
        print(f"  {N:3d} | {rs:8d} {ls:8.5f} | {r2:9d} {l2:9.5f} | {rg:9d} {lg:9.5f}")

    print("\n=== 4a. Induced returns: actual certified ln(2) vs Fredholm-Kempner K ===")
    print("  ln(2): N     | K(N)  | tau_N   | u_tilde | W_N/N   | S2/N    | E2/N    | E4/N    | E8/N")
    for st in ret["ln2_rows"]:
        N = st["N"]
        print(
            f"         {N:5d} | {st['K']:5d} | {st['tau']:7.5f} | {st['u_tilde']:7d} |"
            f" {st['W_N']/N:7.4f} | {st['S2']/N:7.4f} | {st['excess_full'][2]/N:7.5f} |"
            f" {st['excess_full'][4]/N:7.5f} | {st['excess_full'][8]/N:7.5f}"
        )
    print("  K:     N     | K(N)  | tau_N   | W_N/N^2 | S2/N^2  | S3/N^3  | E2/N    | E8/N")
    for st in ret["fk_rows"]:
        N = st["N"]
        print(
            f"         {N:5d} | {st['K']:5d} | {st['tau']:7.5f} | {st['W_N']/N**2:7.5f} |"
            f" {st['S2']/N**2:7.5f} | {st['S3']/N**3:7.5f} | {st['excess_full'][2]/N:7.5f} |"
            f" {st['excess_full'][8]/N:7.5f}"
        )

    print("\n=== 4b. Unfinished-run dyadic separation counterexample x_dyad (L=2) ===")
    print("  m  | N      | tau_N   | E2_comp/N | E2_full/N | u_tilde/N")
    for m, N, tau, ec, ef, ut in ret["dyad_rows"]:
        if m in (4, 5, 8, 9, 12, 13, 16, 17):
            print(f"  {m:2d} | {N:6d} | {tau:7.5f} | {ec:9.5f} | {ef:9.5f} | {ut:9.5f}")

    print("\n=== 4c. Finite equal-run control: S_2(N) ~ C N^{3/2} logarithmic gap upgrade ===")
    print("  N     | R   | K(N) | C_eff   | naive K/N | L* | upgrade r | ratio (r / (K/N))")
    for N, R, K, Ce, nt, Ls, br, rat in ret["upgrade_rows"]:
        print(f"  {N:5d} | {R:3d} | {K:4d} | {Ce:7.4f} | {nt:9.6f} | {Ls:2d} | {br:9.6f} | {rat:7.3f}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
