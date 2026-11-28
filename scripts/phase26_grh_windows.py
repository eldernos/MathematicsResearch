#!/usr/bin/env python3
"""
Phase 26 Track G — Exact Certificates, Consistency Checks & Finite Diagnostics
for External GRH Verification Accounting, Lambert Window Extensions (G2.1-G2.5),
the Galois-Conjugate Second-Moment Bound, and the CRT Zero-Block Barriers.

Design policy:
  - All [exact] checks are substantive mathematical certificates using ONLY
    Python `int` and `fractions.Fraction` (zero floating-point operations).
  - All [consistency] checks are pure int/Fraction/string bookkeeping or
    sanity checks (file/declaration partitions, hex SHA format checks,
    illustrative-parameter checks, ring-bookkeeping checks) separated honestly
    from substantive [exact] certificates.
  - All floating-point or finite-range illustrations are strictly isolated
    under [finite] and are explicitly NOT asymptotic evidence.

Run:
    python -B scripts/phase26_grh_windows.py
"""

from __future__ import annotations

import math
from fractions import Fraction


EXACT_COUNT = 0
CONSISTENCY_COUNT = 0
FINITE_COUNT = 0


def check_exact(cond: bool, msg: str) -> None:
    global EXACT_COUNT
    if not cond:
        raise AssertionError(f"[EXACT FAIL] {msg}")
    EXACT_COUNT += 1


def check_consistency(cond: bool, msg: str) -> None:
    global CONSISTENCY_COUNT
    if not cond:
        raise AssertionError(f"[CONSISTENCY FAIL] {msg}")
    CONSISTENCY_COUNT += 1


def check_finite(cond: bool, msg: str) -> None:
    global FINITE_COUNT
    if not cond:
        raise AssertionError(f"[FINITE FAIL] {msg}")
    FINITE_COUNT += 1


def sieve_primes(limit: int) -> list[int]:
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0] = is_prime[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if is_prime[p]:
            start = p * p
            step = p
            is_prime[start : limit + 1 : step] = b"\x00" * (
                (limit - start) // step + 1
            )
    return [i for i in range(2, limit + 1) if is_prime[i]]


def padic_val(n: int, p: int) -> int:
    v = 0
    while n > 0 and n % p == 0:
        n //= p
        v += 1
    return v


def ceil_frac(f: Fraction) -> int:
    if f.numerator % f.denominator == 0:
        return f.numerator // f.denominator
    if f.numerator > 0:
        return f.numerator // f.denominator + 1
    return f.numerator // f.denominator


def is_hex_sha(s: str, expected_len: int) -> bool:
    return len(s) == expected_len and all(c in "0123456789abcdef" for c in s)


def solve_linear_exact(mat: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    """Exact Gaussian elimination over Q using Fraction (zero floats)."""
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(mat)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("singular rational matrix")
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        for c in range(col, n + 1):
            aug[col][c] /= pv
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                for c in range(col, n + 1):
                    aug[r][c] -= fac * aug[col][c]
    return [aug[i][n] for i in range(n)]


def det_exact(mat: list[list[Fraction]]) -> Fraction:
    """Exact determinant over Q using Fraction (zero floats)."""
    n = len(mat)
    a = [row[:] for row in mat]
    sign = Fraction(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if a[r][col] != 0:
                piv = r
                break
        if piv is None:
            return Fraction(0)
        if piv != col:
            a[col], a[piv] = a[piv], a[col]
            sign = -sign
        pv = a[col][col]
        for r in range(col + 1, n):
            if a[r][col] != 0:
                fac = a[r][col] / pv
                for c in range(col, n):
                    a[r][c] -= fac * a[col][c]
    prod = sign
    for i in range(n):
        prod *= a[i][i]
    return prod


# ---------------------------------------------------------------------------
# Certified outward rational enclosures of ln(b) for b in {2, 3, 5, 6, 10, 12}
# Derived strictly from Taylor series of ln((1+z)/(1-z)) = 2 * sum z^(2k+1)/(2k+1)
# using exact Fraction arithmetic (zero floats).
# ---------------------------------------------------------------------------
def ln_rat_enclosure(r: Fraction, terms: int = 25) -> tuple[Fraction, Fraction]:
    """Return exact (lo, hi) with lo < ln(r) < hi for r > 1."""
    check_exact(r > 1, f"ln_rat_enclosure requires r > 1, got {r}")
    if r > 2:
        lo_total = Fraction(0)
        hi_total = Fraction(0)
        cur = r
        while cur > 2:
            cur = cur / 2
            l2, h2 = ln_rat_enclosure(Fraction(2), terms)
            lo_total += l2
            hi_total += h2
        if cur > 1:
            lr, hr = ln_rat_enclosure(cur, terms)
            lo_total += lr
            hi_total += hr
        return lo_total, hi_total

    z = (r - 1) / (r + 1)
    z2 = z * z
    s = Fraction(0)
    zpow = z
    for k in range(terms):
        s += Fraction(2, 2 * k + 1) * zpow
        zpow *= z2
    # After the loop zpow = z^(2*terms + 1), so the positive tail is
    # strictly < (2 / (2*terms + 1)) * z^(2*terms + 1) / (1 - z^2).
    tail_hi = Fraction(2, 2 * terms + 1) * zpow / (1 - z2)
    lo = s
    hi = s + tail_hi
    check_exact(lo < hi, f"non-degenerate ln enclosure for {r}")
    return lo, hi


# ---------------------------------------------------------------------------
# C1 [consistency + exact ratios]: G1 External GRH Primary-Source Accounting
# ---------------------------------------------------------------------------
def c1_g1_verification_accounting() -> dict[str, object]:
    # File/line/declaration counts read directly from primary sources
    # (lsernau/grh-lean@72fead10, math.mit.edu/~drew/grh/ & shortgrh/, mrubinst.github.io)
    orig_lines = 17_374_215
    orig_code = 15_531_759

    read_files = 803
    read_lib_files = 495
    read_new_files = 306
    read_top_files = 2  # Statements.lean, Main.lean
    read_lines = 477_124
    read_code = 299_902
    read_decls_con = 216_571
    read_decls_l4l = 216_568
    read_shared_decls = 165_163
    read_unique_decls = 51_408

    comp_files = 794
    comp_lib_files = 573
    comp_new_files = 219
    comp_top_files = 2  # Statements.lean, Main.lean
    comp_lines = 112_827
    comp_code = 76_149
    comp_decls_con = 204_583
    comp_decls_l4l = 204_580
    comp_unique_decls = 39_420

    # Accounting partitions (consistency checks)
    check_consistency(
        read_lib_files + read_new_files + read_top_files == read_files,
        "grh/ file partition",
    )
    check_consistency(
        comp_lib_files + comp_new_files + comp_top_files == comp_files,
        "grh-compact/ file partition",
    )
    check_consistency(
        read_decls_con - read_decls_l4l == 3,
        "Quot 4-to-1 declaration delta in readable edition",
    )
    check_consistency(
        comp_decls_con - comp_decls_l4l == 3,
        "Quot 4-to-1 declaration delta in compact edition",
    )
    check_consistency(
        read_shared_decls + read_unique_decls == read_decls_con,
        "readable declaration partition",
    )
    check_consistency(
        read_shared_decls + comp_unique_decls == comp_decls_con,
        "compact declaration partition",
    )
    check_consistency(
        39_482 + 10_750 == 50_232,
        "shared Mathlib closure comparison partition",
    )

    # Exact rational compression ratios from the transcribed counts
    comp_total_reduction = Fraction(orig_lines - comp_lines, orig_lines)
    comp_code_reduction = Fraction(orig_code - comp_code, orig_code)
    read_total_reduction = Fraction(orig_lines - read_lines, orig_lines)
    read_code_reduction = Fraction(orig_code - read_code, orig_code)

    check_consistency(comp_total_reduction > Fraction(9935, 10000), "compact total >99.35%")
    check_consistency(comp_code_reduction > Fraction(9950, 10000), "compact code >99.50%")
    check_consistency(read_total_reduction > Fraction(9725, 10000), "readable total >97.25%")
    check_consistency(read_code_reduction > Fraction(9806, 10000), "readable code >98.06%")

    # Hex format consistency checks for pinned SHAs (values verified against GitHub API)
    pinned_shas = {
        "grh_lean_commit": ("72fead102f663d5c7a407964a13dc0cf9d977207", 40),
        "grh_lean_tree": ("5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f", 40),
        "mathlib_v435": ("56a005855ea17e0b0958f73ec801ae140b0a1679", 40),
        "grh_lean_archive_sha256": (
            "9138cf2f5862e64f823ed676e8d37333c0717e1a13cd8f74f6b735ab2d1ba57c",
            64,
        ),
        "orig_tarball_sha256": (
            "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc",
            64,
        ),
    }
    for name, (val, expected_len) in pinned_shas.items():
        check_consistency(is_hex_sha(val, expected_len), f"hex SHA format for {name}")

    return {
        "comp_code_reduction": comp_code_reduction,
        "read_code_reduction": read_code_reduction,
    }


# ---------------------------------------------------------------------------
# C2 [exact + consistency]: G2.1A Paper VI at H = sqrt(N) (log N)^C under GRH(q_0)
# ---------------------------------------------------------------------------
def c2_paper6_sqrt_log_windows(ln2_lo: Fraction, ln2_hi: Fraction) -> None:
    # 1. Exact geometric tail sum identity: sum_{j=J+1}^{J+M} j 2^{-j}
    for J in range(1, 35):
        partial = Fraction(0)
        for M in range(1, 25):
            j = J + M
            partial += Fraction(j, 1 << j)
            closed = Fraction(J + 2, 1 << J) - Fraction(J + M + 2, 1 << (J + M))
            check_exact(partial == closed, f"tail sum identity J={J}, M={M}")
            check_exact(partial < Fraction(J + 2, 1 << J), f"tail upper bound J={J}")

    # 2. Exact exponent budget for every C in (2, 20] on a 1/20 grid
    for k in range(1, 361):
        C = Fraction(2) + Fraction(k, 20)
        eps = min(Fraction(1, 10), C - 2)
        B = 2 * (C - 2) - eps
        check_exact(B > 0, f"B > 0 for C={C}")

        # Prime-supply exponent (the binding constraint): C - 2 - B/2 = eps/2 > 0
        prime_margin = C - 2 - B / 2
        check_exact(prime_margin == eps / 2 and prime_margin > 0, f"prime margin C={C}")

        # Far-tail cutoff constant C_J = max(4, ceil((B + 2) / ln2_lo))
        C_J = max(4, ceil_frac((B + 2) / ln2_lo))
        # Y-term exponent saving relative to Y / log N: 2 - C_J * ln 2 < 0
        y_term_exp_hi = 2 - C_J * ln2_lo
        check_exact(y_term_exp_hi < 0, f"Y-term saving at C={C}")

        # sqrt(N)-term saving relative to Y / log N requires ONLY B + 1 - C - C_J * ln 2 < 0
        # (equivalently B - C - C_J * ln 2 < -1), which holds for EVERY C > -1 since C_J * ln 2 >= B + 2.
        sqrt_term_exp_hi = B + 1 - C - C_J * ln2_lo
        check_exact(sqrt_term_exp_hi < 0, f"sqrt(N)-term necessary saving (< 0) at C={C}")
        check_exact(sqrt_term_exp_hi < -1, f"sqrt(N)-term margin (< -1) at C={C}")

    # Also check directly that B + 1 - C - C_J * ln 2 < 0 holds even below C = 2 (every C > -1, B = 0)
    for k in range(1, 60):
        C_low = Fraction(-1) + Fraction(k, 20)
        C_J_low = max(4, ceil_frac(Fraction(2) / ln2_lo))
        check_exact(1 - C_low - C_J_low * ln2_lo < 0, f"far-tail non-bottleneck at C={C_low}")

    # 3. Critical C = 2 constant-multiple threshold (m = 1, b = p_0^{2u}, illustrative C_2 = 10):
    # Consistency check on squared form K^2 > 32 * C_2^2 * phi(q_0)^2 * p_0^{2u}
    for phi_q0 in (2, 4, 6):
        for p0 in (5, 11):
            for u in (1, 2, 3):
                C2 = Fraction(10)
                rhs_sq = 32 * (C2 ** 2) * (phi_q0 ** 2) * (p0 ** (2 * u))
                K_min = math.isqrt(int(rhs_sq)) + 1
                check_consistency(K_min * K_min > rhs_sq, f"C=2 threshold K_min={K_min}")

    # 4. Small-factor Rankin check in lem:small for M = (log N)^B:
    check_exact(2 * ln2_lo > 1, "2 ln 2 > 1 for lem:small Rankin trick")
    for num in range(1, 20):
        delta = Fraction(num, 20)
        check_exact(2 * delta - 2 * ln2_lo < delta, f"Rankin exponent at delta={delta}")


# ---------------------------------------------------------------------------
# C3 [exact + consistency]: G2.1B & G2.2B GF-22 Sub-Polynomial Thresholds
# ---------------------------------------------------------------------------
def c3_gf22_thresholds(
    ln_bounds: dict[int, tuple[Fraction, Fraction]],
) -> dict[tuple[int, int], tuple[Fraction, Fraction]]:
    check_consistency(2 - (-1) == 3, "Step 5' dominates Step 6' by (log N)^3")

    enclosures: dict[tuple[int, int], tuple[Fraction, Fraction]] = {}
    for d in (2, 3, 4, 5):
        for b in (2, 3, 5, 10):
            lo_ln, hi_ln = ln_bounds[b]
            c_lo = Fraction(d) / hi_ln
            c_hi = Fraction(d) / lo_ln
            check_exact(c_lo < c_hi, f"enclosure d={d}, b={b}")
            check_consistency(2 * c_lo < 2 * c_hi, f"halving factor consistency d={d}, b={b}")
            check_consistency(
                2 * (Fraction(d) / lo_ln) == Fraction(2 * d) / lo_ln,
                "C_1 = 2 C_0 algebraic scaling",
            )
            enclosures[(d, b)] = (c_lo, c_hi)

    # Specific check for cubic L_+(2) (d = 3, b = 2):
    c32_lo, c32_hi = enclosures[(3, 2)]
    check_exact(Fraction(4328, 1000) < c32_lo and c32_hi < Fraction(4329, 1000), "3/ln 2 enclosure")
    check_exact(
        Fraction(8656, 1000) < 2 * c32_lo and 2 * c32_hi < Fraction(8657, 1000),
        "6/ln 2 enclosure",
    )
    return enclosures


# ---------------------------------------------------------------------------
# C4 [exact + consistency]: G2.2 Zero-Density, Two-Regime sigma-Split & Almost-All
# ---------------------------------------------------------------------------
def c4_zero_density_and_almost_all() -> None:
    zd_table = [
        ("Ingham (1940)", Fraction(8, 3), Fraction(5, 8), Fraction(1, 4)),
        ("Montgomery (1971)", Fraction(5, 2), Fraction(3, 5), Fraction(1, 5)),
        ("Huxley (1972/1975) + Jutila (1977)", Fraction(12, 5), Fraction(7, 12), Fraction(1, 6)),
        ("Chen-Gupta-Li (2025/2026, arXiv)", Fraction(7, 3), Fraction(4, 7), Fraction(1, 7)),
        ("Guth-Maynard (2024/2026, q=1)", Fraction(30, 13), Fraction(17, 30), Fraction(2, 15)),
        ("Density Hypothesis", Fraction(2, 1), Fraction(1, 2), Fraction(0, 1)),
    ]
    for name, A, exp_all, exp_aa in zd_table:
        check_exact(1 - Fraction(1) / A == exp_all, f"all-window exponent for {name}")
        check_exact(1 - Fraction(2) / A == exp_aa, f"almost-all exponent for {name}")

    # Strict ordering chains
    chain_all = [
        Fraction(1, 2),
        Fraction(525, 1000),
        Fraction(53, 100),
        Fraction(17, 30),
        Fraction(4, 7),
        Fraction(7, 12),
    ]
    for i in range(len(chain_all) - 1):
        check_exact(chain_all[i] < chain_all[i + 1], f"all-window chain index {i}")

    chain_aa = [
        Fraction(0),
        Fraction(1, 20),
        Fraction(2, 15),
        Fraction(1, 7),
        Fraction(1, 6),
        Fraction(1, 5),
        Fraction(1, 2),
    ]
    for i in range(len(chain_aa) - 1):
        check_exact(chain_aa[i] < chain_aa[i + 1], f"almost-all chain index {i}")

    # Theorem G2.2A: Paper VI unconditional almost-all parameter grid for A in {12/5, 7/3}
    for A in (Fraction(12, 5), Fraction(7, 3)):
        theta_star = 1 - Fraction(2) / A
        for k in range(1, 501):
            a = theta_star + (1 - theta_star) * Fraction(k, 500)
            theta = min(Fraction(1, 4), (a - theta_star) / 2)
            check_exact(Fraction(0) < theta <= Fraction(1, 4), f"G2.2A theta bounds a={a}")
            a_minus_theta = a - theta
            vartheta_min = a_minus_theta / (1 - theta)
            check_exact(vartheta_min >= a_minus_theta, f"vartheta_min >= a - theta at a={a}")
            if a < 1:
                check_exact(a > vartheta_min > a_minus_theta, f"strict chain at a={a}")
            check_exact(a_minus_theta >= (a + theta_star) / 2, f"midpoint lower bound at a={a}")
            check_exact(a_minus_theta > theta_star, f"exceeds theta_star at a={a}")
            gamma = 2 - A * (1 - a_minus_theta)
            check_exact(gamma >= A * (a - theta_star) / 2 and gamma > 0, f"variance saving at a={a}")

    # Theorem G2.2A': Paper VI GRH(q_0) almost-all parameter grid for theta in (0, 1]
    for k in range(1, 501):
        a = Fraction(k, 500)
        mu = min(Fraction(1, 4), a / 2)
        check_exact(a - mu >= a / 2 and a - mu > 0, f"G2.2A' Y_m power at a={a}")
        saving = a - (a + mu) / 2
        check_exact(saving == (a - mu) / 2 and saving > 0, f"G2.2A' power saving at a={a}")
        pp_saving = (1 - mu) / 2
        check_exact(pp_saving >= Fraction(3, 8), f"G2.2A' prime-power saving at a={a}")

    # M3 repair: Two-regime sigma-split at sigma_0 = 4/5 (c_0 = 1/5) using:
    #   - Bulk [1/2, 4/5]: eps-form N_q(sigma, T) <<_{eps'} (qT)^{A(1-sigma) + eps'}
    #     (A = 12/5 Huxley 1975; A = 7/3 Chen-Gupta-Li 2507.08296v2)
    #   - Near-1 [4/5, 1 - eta]: Jutila (1977, Math. Scand. 41, Thm. 1, eq. (1.7))
    #     log-free N_q(sigma, T) <<_{eps''} (qT)^{(2 + eps'')(1 - sigma)}
    # Also checks Thorner-Zaman (2024, Math. Z. 306, Thm. 2.1, eq. (2.1))
    # full-strip log-free N_q(sigma, T) <<_{eps1} (qT)^{(12/5 + eps1)(1 - sigma)}.
    c0 = Fraction(1, 5)  # 1 - sigma_0 = 1 - 4/5 = 1/5
    for A in (Fraction(12, 5), Fraction(7, 3)):
        a_all_thresh = 1 - Fraction(1) / A  # 7/12 for 12/5; 4/7 for 7/3
        a_aa_thresh = 1 - Fraction(2) / A   # 1/6 for 12/5; 1/7 for 7/3

        # 1. All-window regime (G2.2C & 4/7 addendum)
        for k in range(1, 201):
            a = a_all_thresh + (1 - a_all_thresh) * Fraction(k, 200)
            eps0 = (a - a_all_thresh) / 2
            t_exp = 1 - a + eps0  # T = U^{t_exp}
            gamma0 = 1 - A * t_exp
            check_exact(gamma0 == A * (a - a_all_thresh) / 2 and gamma0 > 0, f"all gamma0 A={A}, a={a}")
            # Bulk [1/2, 4/5]: eps' = gamma0 / 20 is absorbed by U^{-(3/4)*gamma0*(1-sigma)} at 1-sigma >= c0 = 1/5
            eps_bulk = gamma0 / 20
            bulk_saving_at_c0 = Fraction(3, 4) * gamma0 * c0 - eps_bulk
            check_exact(bulk_saving_at_c0 == gamma0 / 10 and bulk_saving_at_c0 > 0, f"all bulk saving A={A}, a={a}")
            # Near-1 [4/5, 1 - eta]: Jutila log-free exponent 2 + eps_lf with eps_lf = 1/10
            gamma_lf_exact = 1 - 2 * t_exp
            check_exact(gamma_lf_exact == a - Fraction(1) / A, f"all Jutila margin identity A={A}, a={a}")
            check_exact(gamma_lf_exact > a_aa_thresh and gamma_lf_exact > Fraction(1, 7), f"all Jutila positive A={A}, a={a}")
            eps_lf = Fraction(1, 10)
            near1_saving = 1 - (2 + eps_lf) * t_exp
            check_exact(near1_saving > gamma_lf_exact / 2 and near1_saving > 0, f"all near-1 saving A={A}, a={a}")
            # Full-strip log-free check for A = 12/5 (Thorner-Zaman Thm. 2.1): eps1 = gamma0 / 2
            if A == Fraction(12, 5):
                eps1 = gamma0 / 2
                tz_saving = 1 - (A + eps1) * t_exp
                check_exact(tz_saving > gamma0 / 2 and tz_saving > 0, f"TZ full-strip all saving a={a}")
            # Low-beta (beta <= 1/2) exponent: 1/2 - a + eps0 < 0
            low_beta_exp = Fraction(1, 2) - a + eps0
            check_exact(low_beta_exp < Fraction(-1, 14), f"all low-beta saving A={A}, a={a}")

        # 2. Almost-all / mean-square regime (Lemma 3.2 -> G2.2A, G2.2D & 1/7 addendum)
        for k in range(1, 201):
            a = a_aa_thresh + (1 - a_aa_thresh) * Fraction(k, 200)
            eps0 = (a - a_aa_thresh) / 2
            u_exp = 1 - a + eps0  # U = 6 * T^{u_exp}
            gamma1 = 2 - A * u_exp
            check_exact(gamma1 == A * (a - a_aa_thresh) / 2 and gamma1 > 0, f"aa gamma1 A={A}, a={a}")
            # Bulk [1/2, 4/5]: eps' = gamma1 / 20 absorbed at 1-sigma >= 1/5
            eps_bulk = gamma1 / 20
            bulk_saving_at_c0 = Fraction(3, 4) * gamma1 * c0 - eps_bulk
            check_exact(bulk_saving_at_c0 == gamma1 / 10 and bulk_saving_at_c0 > 0, f"aa bulk saving A={A}, a={a}")
            # Near-1 [4/5, 1 - eta]: Jutila log-free exponent 2 + eps_lf with eps_lf = 1/10
            gamma_lf_exact = 2 - 2 * u_exp
            check_exact(gamma_lf_exact == a + a_aa_thresh, f"aa Jutila margin identity A={A}, a={a}")
            check_exact(gamma_lf_exact > 2 * a_aa_thresh and gamma_lf_exact > Fraction(2, 7), f"aa Jutila positive A={A}, a={a}")
            eps_lf = Fraction(1, 10)
            near1_saving = 2 - (2 + eps_lf) * u_exp
            check_exact(near1_saving > gamma_lf_exact / 2 and near1_saving > 0, f"aa near-1 saving A={A}, a={a}")
            # Full-strip log-free check for A = 12/5 (Thorner-Zaman Thm. 2.1): eps1 = gamma1 / 2
            if A == Fraction(12, 5):
                eps1 = gamma1 / 2
                tz_saving = 2 - (A + eps1) * u_exp
                check_exact(tz_saving > gamma1 / 2 and tz_saving > 0, f"TZ full-strip aa saving a={a}")

    # Khale (2024) Theorem 1.1 constant budget bookkeeping: 61.5 + 0.5 = 62
    check_consistency(Fraction(123, 2) + Fraction(1, 2) == 62, "Khale 61.5 + 0.5 = 62")


# ---------------------------------------------------------------------------
# C5 [exact]: G2.3 Exact Window Discrepancy Constants & Shiu Valuation Bound
# ---------------------------------------------------------------------------
def c5_window_leading_constants(
    ln_bounds: dict[int, tuple[Fraction, Fraction]],
) -> dict[int, tuple[Fraction, Fraction]]:
    ln2_lo, ln2_hi = ln_bounds[2]

    # Critical threshold delta* = 1 / (1 + ln 2)
    dstar_lo = Fraction(1) / (1 + ln2_hi)
    dstar_hi = Fraction(1) / (1 + ln2_lo)
    check_exact(Fraction(5906, 10000) < dstar_lo and dstar_hi < Fraction(5907, 10000), "delta* enclosure")
    check_exact(Fraction(1, 2) < dstar_lo, "delta = 1/2 < delta*")
    check_exact(Fraction(1, 4) < dstar_lo, "delta = 1/4 < delta*")

    for delta in (Fraction(1, 4), Fraction(1, 2)):
        kappa = 1 - delta
        omega_hi = delta * ln2_hi / kappa
        check_exact(omega_hi < 1, f"sub-threshold omega < 1 at delta={delta}")
        B = max(Fraction(0), 2 * delta - 1)
        check_exact((2 + omega_hi) * kappa + (B + 2) - B > kappa + 2, f"tail radius margin delta={delta}")

    # GF-21 even-composite threshold jumps: beta_b = ln(b)/ln(b'), delta*_b = beta_b/(beta_b + ln 2)
    jump_enclosures: dict[int, tuple[Fraction, Fraction]] = {}
    for b in (3, 5, 6, 10, 12):
        lnb_lo, lnb_hi = ln_bounds[b]
        v2 = padic_val(b, 2)
        b_odd = b >> v2
        if v2 == 0:
            beta_lo, beta_hi = Fraction(1), Fraction(1)
        else:
            lnb_odd_lo, lnb_odd_hi = ln_bounds[b_odd]
            beta_lo = lnb_lo / lnb_odd_hi
            beta_hi = lnb_hi / lnb_odd_lo
        db_lo = Fraction(1) / (1 + ln2_hi / beta_lo)
        db_hi = Fraction(1) / (1 + ln2_lo / beta_hi)
        check_exact(db_lo < db_hi, f"delta*_b enclosure b={b}")
        if v2 > 0:
            check_exact(db_lo > dstar_hi, f"even-composite jump delta*_{b} > delta*_odd")
        jump_enclosures[b] = (db_lo, db_hi)

    check_exact(
        Fraction(7017, 10000) < jump_enclosures[6][0] and jump_enclosures[6][1] < Fraction(7018, 10000),
        "delta*_6",
    )
    check_exact(
        Fraction(6736, 10000) < jump_enclosures[10][0] and jump_enclosures[10][1] < Fraction(6737, 10000),
        "delta*_10",
    )
    check_exact(
        Fraction(7654, 10000) < jump_enclosures[12][0] and jump_enclosures[12][1] < Fraction(7655, 10000),
        "delta*_12",
    )

    # Shiu class verification for h_q(p^e) = 2^{v_q(c(p^e))} <= e + 1 <= 2^e
    # (applies specifically to h_q; g_t and z^{omega_{S,1}} are immediate analytic bounds)
    for q in (3, 5, 7, 11, 13):
        for e in range(1, 501):
            max_vq = 0
            pw = q
            while pw <= e + 1:
                max_vq += 1
                pw *= q
            check_exact((1 << max_vq) <= e + 1 <= (1 << e), f"Shiu h_q bound q={q}, e={e}")

    return jump_enclosures


# ---------------------------------------------------------------------------
# C6 [exact + consistency]: G2.4 Galois-Conjugate Bound (h=5), Second-Moment
# Shiu Reduction, kappa'_2(h) != 1, and CRT/Union Zero-Block Barriers
# ---------------------------------------------------------------------------
def _mul_z5(a: list[int], b: list[int]) -> list[int]:
    """Exact multiplication in Z[zeta_5] = Z[x]/(1 + x + x^2 + x^3 + x^4)."""
    res = [0] * 7
    for i in range(4):
        for j in range(4):
            res[i + j] += a[i] * b[j]
    # x^4 = -1 - x - x^2 - x^3; x^5 = 1; x^6 = x
    out = [res[0] - res[4] + res[5], res[1] - res[4] + res[6], res[2] - res[4], res[3] - res[4]]
    return out


def _conj_z5(a: list[int]) -> list[int]:
    """Complex conjugation zeta_5^j -> zeta_5^{-j} in Z[zeta_5]."""
    # a0 + a1*z^4 + a2*z^3 + a3*z^2 = (a0-a1) + (-a1)z + (a3-a1)z^2 + (a2-a1)z^3
    return [a[0] - a[1], -a[1], a[3] - a[1], a[2] - a[1]]


def _tr_z5(a: list[int]) -> int:
    """Exact trace Tr_{Q(zeta_5)/Q}(a) in Z."""
    return 4 * a[0] - a[1] - a[2] - a[3]


def _mul_q5(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    """Exact multiplication in Q(zeta_5) = Q[x]/(1 + x + x^2 + x^3 + x^4)."""
    res = [Fraction(0)] * 7
    for i in range(4):
        for j in range(4):
            res[i + j] += a[i] * b[j]
    return [res[0] - res[4] + res[5], res[1] - res[4] + res[6], res[2] - res[4], res[3] - res[4]]


def _conj_q5(a: list[Fraction]) -> list[Fraction]:
    return [a[0] - a[1], -a[1], a[3] - a[1], a[2] - a[1]]


def _tr_q5(a: list[Fraction]) -> Fraction:
    return 4 * a[0] - a[1] - a[2] - a[3]


def c6_shiu_second_moment_and_crt_barrier() -> dict[str, object]:
    # 1. Quotient-ring bookkeeping check of sum_{j=0}^{h-1} (2 + x^j + x^{h-j}) in Q[x]/(x^h - 1)
    for h in range(2, 61):
        coeffs = [0] * h
        coeffs[0] += 2 * h
        for j in range(h):
            coeffs[j] += 1
            coeffs[(h - j) % h] += 1
        reduced = [coeffs[r] - 2 for r in range(h)]
        check_consistency(
            reduced[0] == 2 * h and all(c == 0 for c in reduced[1:]),
            f"kappa_2(chi)=2 ring bookkeeping h={h}",
        )

    # 2. M1 [exact]: Galois-conjugate trace-duality bound & counterexample at h = 5 (phi(5) = 4)
    # Build exact 4x4 integer trace matrix M_{i,j} = Tr(zeta_5^{i+j}) for 0 <= i, j < 4
    M_z5 = [
        [Fraction(4 if (i + j) % 5 == 0 else -1) for j in range(4)]
        for i in range(4)
    ]
    disc_z5 = det_exact(M_z5)
    check_exact(disc_z5 == Fraction(125), "disc(Q(zeta_5)/Q) = det(Tr(zeta_5^{i+j})) = 5^3 = 125")

    # Solve M_z5 * beta_r = e_r for all 4 coordinate functionals Phi_r(a0 + a1*z + a2*z^2 + a3*z^3) = a_r
    betas: list[list[Fraction]] = []
    K_phis: list[Fraction] = []
    for r in range(4):
        rhs = [Fraction(1 if i == r else 0) for i in range(4)]
        beta = solve_linear_exact(M_z5, rhs)
        # Verify M_z5 * beta == rhs exactly
        for i in range(4):
            check_exact(sum(M_z5[i][j] * beta[j] for j in range(4)) == rhs[i], f"trace dual r={r}, i={i}")
        # Exact rational Cauchy-Schwarz constant K_Phi = Tr(beta * conj(beta)) = sum_sigma |sigma(beta)|^2
        K_val = _tr_q5(_mul_q5(beta, _conj_q5(beta)))
        check_exact(K_val > 0, f"K_Phi_{r} > 0")
        betas.append(beta)
        K_phis.append(K_val)

    # Specifically for Phi_0(z) = a_0: beta_0 = (1 - zeta_5)/5 and K_{Phi_0} = 2/5
    check_exact(
        betas[0] == [Fraction(1, 5), Fraction(-1, 5), Fraction(0), Fraction(0)],
        "beta_{Phi_0} = (1 - zeta_5)/5",
    )
    check_exact(K_phis[0] == Fraction(2, 5), "K_{Phi_0} = Tr(beta_0 * conj(beta_0)) = 2/5")

    # Verify exact trace identity and Galois-conjugate Cauchy-Schwarz bound on z_k = (1 + zeta_5^2)^k
    # for ALL 1 <= k <= 40 and ALL 4 coordinate functionals Phi_0..Phi_3!
    base_z5 = [1, 0, 1, 0]  # 1 + zeta_5^2
    cur_z5 = [1, 0, 0, 0]
    counterexample_vals: dict[int, tuple[int, int]] = {}
    # Exact rational bound |1 + zeta_5^2|^2 = (3 - sqrt(5))/2 < 39/100:
    # (3 - 78/100)^2 = (222/100)^2 = 49284/10000 < 5 = 50000/10000 => sqrt(5) > 222/100 => (3-sqrt(5))/2 < 39/100.
    check_exact(Fraction(222, 100) ** 2 < Fraction(5), "exact proof sqrt(5) > 2.22 => |1+zeta_5^2|^2 < 39/100")
    mod_sq_hi = Fraction(39, 100)

    for k in range(1, 41):
        cur_z5 = _mul_z5(cur_z5, base_z5)
        cur_q5 = [Fraction(c) for c in cur_z5]
        # Exact sum of squared Galois conjugates: sum_sigma |sigma(z_k)|^2 = Tr(z_k * conj(z_k)) in Z_{>0}
        tr_sq = _tr_z5(_mul_z5(cur_z5, _conj_z5(cur_z5)))
        check_exact(tr_sq > 0, f"Tr(|z_{k}|^2) > 0")
        for r in range(4):
            phi_val = cur_z5[r]
            # Exact trace identity Phi_r(z_k) == Tr(beta_r * z_k)
            tr_val = _tr_q5(_mul_q5(betas[r], cur_q5))
            check_exact(tr_val == Fraction(phi_val), f"trace identity h=5, r={r}, k={k}")
            # Exact Galois-conjugate Cauchy-Schwarz bound: |Phi_r(z_k)|^2 <= K_{Phi_r} * sum_sigma |sigma(z_k)|^2
            check_exact(
                Fraction(phi_val * phi_val) <= K_phis[r] * Fraction(tr_sq),
                f"Galois-conjugate CS bound h=5, r={r}, k={k}",
            )
        if k in (5, 10, 20, 40):
            counterexample_vals[k] = (abs(cur_z5[0]), tr_sq)
            # Certify in pure rationals that naive |Phi_0(z_k)| <= |z_k| fails dramatically!
            check_exact(
                Fraction(cur_z5[0] * cur_z5[0]) > (mod_sq_hi ** k),
                f"naive |Phi_0(z_{k})| <= |z_{k}| fails at h=5, k={k}",
            )

    # Confirm exact Fibonacci magnitudes from referee's counterexample
    check_exact(counterexample_vals[5][0] == 8, "h=5 counterexample |Phi_0(z_5)| = 8")
    check_exact(counterexample_vals[10][0] == 89, "h=5 counterexample |Phi_0(z_10)| = 89")
    check_exact(counterexample_vals[20][0] == 10946, "h=5 counterexample |Phi_0(z_20)| = 10946")
    check_exact(counterexample_vals[40][0] == 165580141, "h=5 counterexample |Phi_0(z_40)| = 165580141")
    # At k = 40: |z_40|^2 < (39/100)^40 < 10^{-16} while |Phi_0(z_40)|^2 > 10^{16} (gap > 10^{32}!)
    check_exact((mod_sq_hi ** 40) < Fraction(1, 10**16), "|z_40|^2 < 10^{-16} at h=5")
    check_exact(counterexample_vals[40][0] ** 2 > 10**16, "|Phi_0(z_40)|^2 > 10^{16} at h=5")

    # 3. Exact rational verification for cubic h = 3 and quadratic h = 2, plus Fourier proof kappa'_2(h) != 1
    check_exact(Fraction(2**1 + 2, 3 * 1) == Fraction(4, 3), "g_3(1) = 4/3")
    check_exact(Fraction(2**2 + 2, 3 * 2) == Fraction(1, 1), "g_3(2) = 1")
    check_exact((2**21) * (10**10) < (43**10), "exact integer proof that g_3(21/10) < 1")
    check_exact((2**21) * (10000**10) > (42748**10), "exact integer proof that g_3(21/10) > 0.996")
    check_exact(8 * 10000 < 9 * 9025, "exact integer proof that g_2(3/2) < 0.95")

    # Exact Fourier-series sign check for kappa'_2(h) - 1 = sum_{k>=1} 2*(-1)^{kh} / (kh*(k^2 h^2 - 1)):
    # For even h >= 2 every term is > 0; for odd h >= 3 terms strictly alternate and decrease, so -a_1 + a_2 < 0.
    for h in range(2, 61):
        a1 = Fraction(2, h * (h * h - 1))
        a2 = Fraction(2, (2 * h) * (4 * h * h - 1))
        check_exact(a1 > a2 > 0, f"Fourier term monotonicity h={h}")
        if h % 2 == 0:
            check_exact(a1 > 0, f"kappa'_2({h}) - 1 > a_1 > 0")
        else:
            check_exact(-a1 + a2 < 0, f"kappa'_2({h}) - 1 < -a_1 + a_2 < 0")

    # 4. Exact rational certificate for P(2) = sum_{p prime} 1/p^2 < 453/1000 < 1/2
    primes_10k = sieve_primes(10000)
    p2_partial = sum(Fraction(1, p * p) for p in primes_10k)
    p2_tail_hi = Fraction(1, 10000)
    p2_lo = p2_partial
    p2_hi = p2_partial + p2_tail_hi
    check_exact(Fraction(452, 1000) < p2_lo and p2_hi < Fraction(453, 1000), "P(2) in (0.452, 0.453)")
    check_exact(p2_hi < Fraction(1, 2), "P(2) < 1/2 (universal CRT & union-bound covering barrier)")

    # 5. Exact rational certificate for cubic mod 7 inert primes P' = {p = 2, 3, 4, 5 mod 7}
    inert_mod7 = [p for p in primes_10k if p % 7 in (2, 3, 4, 5)]
    p2_mod7_lo = sum(Fraction(1, p * p) for p in inert_mod7)
    p2_mod7_hi = p2_mod7_lo + p2_tail_hi
    check_exact(
        Fraction(4225, 10000) < p2_mod7_lo and p2_mod7_hi < Fraction(4228, 10000),
        "P_{P'}(2) in (0.4225, 0.4228)",
    )
    uncovered_floor = 1 - p2_mod7_hi
    check_exact(uncovered_floor > Fraction(577, 1000), "uncovered fraction > 0.577 for cubic mod 7")

    # M2 exact exponent certificates:
    # Single CRT class exponent: d_min * (1 - P_{P'}(2)) >= 3 * 0.577 = 1.731 (universal >= 3 * 0.547 = 1.641)
    # Union-bound exponent over ALL zero blocks: (1 - P_{P'}(2)) / 2 > 0.288 (universal (1 - P(2))/2 > 0.273)
    union_exp_univ_lo = (1 - p2_hi) / 2
    union_exp_mod7_lo = uncovered_floor / 2
    single_exp_mod7_lo = 3 * uncovered_floor
    check_exact(union_exp_univ_lo > Fraction(273, 1000), "universal union-bound exponent (1-P(2))/2 > 0.273")
    check_exact(union_exp_mod7_lo > Fraction(288, 1000), "cubic mod 7 union-bound exponent > 0.288")
    check_exact(single_exp_mod7_lo > Fraction(1731, 1000), "cubic mod 7 single-CRT exponent > 1.731")
    check_exact(single_exp_mod7_lo == 6 * union_exp_mod7_lo, "single-class/union exponent ratio = 2*d_min = 6")

    vanish_sum_lo = sum(Fraction(1, p * p + p + 1) for p in inert_mod7)
    vanish_sum_hi = vanish_sum_lo + p2_tail_hi
    check_exact(
        Fraction(27, 100) < vanish_sum_lo and vanish_sum_hi < Fraction(29, 100),
        "sum 1/(p^2+p+1) in (0.27, 0.29)",
    )

    # 6. Concrete covering-congruence lower bound on finite block lengths L
    covering_table = []
    for L in (10, 20, 50, 100, 200, 500, 1000):
        small_p = [p for p in inert_mod7 if p * p <= L]
        max_covered_small = sum((L // (p * p)) + 1 for p in small_p)
        min_distinct_large = max(0, L - max_covered_small)
        if L == 10:
            # Explicit note (m5): at L = 10 the bound gives exactly 5 = L/2
            check_exact(min_distinct_large * 2 == L, "at L=10 min_distinct_large = 5 = L/2")
        else:
            check_exact(min_distinct_large * 2 > L, f"more than L/2 uncovered offsets at L={L}")
        large_p = [p for p in inert_mod7 if p * p > L][:min_distinct_large]
        check_exact(len(large_p) == min_distinct_large, f"enough primes for L={L}")
        q_min = 1
        for p in large_p:
            q_min *= p ** 3
        bits_q_min = q_min.bit_length() - 1
        check_exact((1 << bits_q_min) <= q_min < (1 << (bits_q_min + 1)), f"bit_length check L={L}")
        covering_table.append((L, len(small_p), max_covered_small, min_distinct_large, bits_q_min))

    return {
        "p2_lo": p2_lo,
        "p2_hi": p2_hi,
        "p2_mod7_lo": p2_mod7_lo,
        "p2_mod7_hi": p2_mod7_hi,
        "union_exp_univ_lo": union_exp_univ_lo,
        "union_exp_mod7_lo": union_exp_mod7_lo,
        "single_exp_mod7_lo": single_exp_mod7_lo,
        "counterexample_vals": counterexample_vals,
        "covering_table": covering_table,
    }


# ---------------------------------------------------------------------------
# C7 [finite]: Isolated Numerical & Finite Measurements (NOT Asymptotic Evidence)
# ---------------------------------------------------------------------------
def c7_finite_illustrations() -> dict[str, object]:
    # 1. Optimal Shiu moment exponent alpha_*(h) = inf_{t >= 1} kappa_t(h) / t
    opt_shiu = {}
    for h in (2, 3, 4, 5, 6, 7, 12):
        best_t = 1.0
        best_val = 10.0
        for step in range(0, 3001):
            t = 1.0 + step * 0.001
            kappa_t = sum((2.0 * abs(math.cos(math.pi * j / h))) ** t for j in range(h)) / h
            val = kappa_t / t
            if val < best_val:
                best_val = val
                best_t = t
        k1 = sum(2.0 * abs(math.cos(math.pi * j / h)) for j in range(h)) / h
        check_finite(best_val < 1.0, f"alpha_*(h) < 1 strictly for h={h}")
        check_finite(best_val < k1, f"alpha_*(h) < kappa_1(h) for h={h}")
        opt_shiu[h] = (k1, best_t, best_val)

    # 2. Illustrative comparison of GF-22 CRT modulus digits for L_+(2) (W=2, M=3, A=13^6)
    primes_20000 = sieve_primes(20000)
    kill_pool = [p for p in primes_20000 if p % 7 == 3]
    A_val = 13 ** 6
    tau_A = 7
    tau_q = 2
    C_phi = 2
    modulus_comparison = []
    for log10_N in (10, 100, 1000, 10_000, 1_000_000):
        ln_6AN = math.log(6 * A_val) + log10_N * math.log(10.0)
        L_old = math.ceil(math.log2(512 * C_phi * tau_A * tau_q * (1.0 + ln_6AN) ** 2))
        s_old = 2 + L_old
        P0_old = L_old + 2 + math.ceil(2 * s_old * math.log2(4)) + 1 + 13 + 7
        ps_old = [p for p in kill_pool if p > P0_old][:s_old]
        digits_old = math.log10(7) + 3.0 * sum(math.log10(p) for p in ps_old)

        L_new = math.ceil(math.log2(512 * C_phi * tau_A * tau_q * (1.0 + ln_6AN)))
        s_new = 2 + L_new
        P0_new = L_new + 2 + math.ceil(8 * s_new + 8 * math.log2(max(2.0, ln_6AN))) + 1 + 13 + 7
        ps_new = [p for p in kill_pool if p > P0_new][:s_new]
        digits_new = math.log10(7) + 3.0 * sum(math.log10(p) for p in ps_new)

        check_finite(digits_new < digits_old, f"G2.4A reduces log10(q') at log10 N = {log10_N}")
        modulus_comparison.append((log10_N, L_old, digits_old, L_new, digits_new, digits_new / digits_old))

    return {
        "opt_shiu": opt_shiu,
        "modulus_comparison": modulus_comparison,
    }


def main() -> int:
    ln_bounds = {b: ln_rat_enclosure(Fraction(b), terms=25) for b in (2, 3, 5, 6, 10, 12)}
    ln2_lo, ln2_hi = ln_bounds[2]
    check_exact(
        Fraction(69314718, 10**8) < ln2_lo and ln2_hi < Fraction(69314719, 10**8),
        "ln(2) 8-digit exact enclosure",
    )

    c1 = c1_g1_verification_accounting()
    c2_paper6_sqrt_log_windows(ln2_lo, ln2_hi)
    c3 = c3_gf22_thresholds(ln_bounds)
    c4_zero_density_and_almost_all()
    c5 = c5_window_leading_constants(ln_bounds)
    c6 = c6_shiu_second_moment_and_crt_barrier()
    c7 = c7_finite_illustrations()

    print("=== Phase 26 Track G Verification Summary ===")
    print(
        f"C1 [consistency] grh-compact code reduction: "
        f"{float(c1['comp_code_reduction'])*100:.4f}% (> 99.50%)"
    )
    print(
        f"C1 [consistency] grh readable code reduction: "
        f"{float(c1['read_code_reduction'])*100:.4f}% (> 98.06%)"
    )
    print("C3 [exact] GF-22 t=2 CRT constant d/ln(b) enclosures:")
    for (d, b) in ((2, 2), (3, 2), (3, 3), (3, 10)):
        lo, hi = c3[(d, b)]
        print(
            f"   (d={d}, b={b}): d/ln(b) in [{float(lo):.6f}, {float(hi):.6f}] "
            f"(2d/ln(b) in [{float(2*lo):.6f}, {float(2*hi):.6f}])"
        )
    print("C5 [exact] GF-21 even-composite threshold enclosures delta*_b:")
    for b, (lo, hi) in c5.items():
        print(f"   b={b:2d}: delta*_b in [{float(lo):.6f}, {float(hi):.6f}]")
    print("C6 [exact] h=5 Galois-conjugate trace-duality bound (K_{Phi_0} = 2/5, z_k = (1 + zeta_5^2)^k):")
    for k, (phi_v, tr_sq) in c6["counterexample_vals"].items():
        print(f"   k={k:2d}: |Phi_0(z_k)|={phi_v:9d}, Tr(|z_k|^2)={tr_sq} (bound holds; naive |Phi_0|<=|z_k| fails)")
    print(
        f"C6 [exact] P(2) in [{float(c6['p2_lo']):.6f}, {float(c6['p2_hi']):.6f}] < 1/2; "
        f"universal union exponent (1-P(2))/2 > {float(c6['union_exp_univ_lo']):.6f}"
    )
    print(
        f"C6 [exact] P_{{P'}}(2) (cubic mod 7) in "
        f"[{float(c6['p2_mod7_lo']):.6f}, {float(c6['p2_mod7_hi']):.6f}]; "
        f"single-CRT > {float(c6['single_exp_mod7_lo']):.6f}, "
        f"union-bound > {float(c6['union_exp_mod7_lo']):.6f}"
    )
    print("C6 [exact] Cubic mod 7 CRT covering-congruence lower bounds:")
    for L, n_sm, max_cov, min_lg, bits_q in c6["covering_table"]:
        print(
            f"   L={L:4d}: small_p={n_sm:2d}, max_cov={max_cov:3d}, "
            f"min_distinct_large={min_lg:3d}, log2(Q_min)>={bits_q}"
        )
    print("C7 [finite] Optimal Shiu moment exponent alpha_*(h) (isolated finite numeric):")
    for h, (k1, bt, bv) in c7["opt_shiu"].items():
        print(f"   h={h:2d}: kappa_1={k1:.6f}, t*={bt:.3f}, alpha_*={bv:.6f}")
    print("C7 [finite] Illustrative L_+(2) CRT log10(q') reduction (isolated finite numeric):")
    for log10_N, Lo, do, Ln, dn, rat in c7["modulus_comparison"]:
        print(
            f"   log10(N)={log10_N:7d}: L_old={Lo:2d} (log10 q'~{do:6.1f}) "
            f"-> L_new={Ln:2d} (log10 q'~{dn:6.1f}), ratio={rat:.3f}"
        )

    total = EXACT_COUNT + CONSISTENCY_COUNT + FINITE_COUNT
    print(
        f"\nALL {total} CHECKS PASSED "
        f"({EXACT_COUNT} exact, {CONSISTENCY_COUNT} consistency, {FINITE_COUNT} finite)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
