#!/usr/bin/env python3
"""Phase 21, Tracks D3-D4: the partition constant and higher modular objects.

Standard library only.  Run:  python -B scripts/phase21_partitions_modular.py

Exact checks (assertions):
  D3  p(n) < exp(pi*sqrt(2n/3))  and the eta-transformation refinement
      p(n) <= c (24n)^(-1/4) exp(pi*sqrt(2n/3));
      certified windows  L_nec <= L_exact <= L_mod <= L_elem;
      certified digits of P_b from the window and from 1/E_b agree;
      shift-register carry recurrence and pentagonal window identity for R_{n,L};
      the theta*p(n) solutions of the homogeneous circle recurrence;
      rational approximants r_K = b^{m_K}/Q_K: Q_K = +-1 mod b, agreement
      length <= m_{K+1}, and ord_{Q_K}(b) > 20 m_{K+1} for the K tested.
  D4  the polynomial-mass rate (Theorem D4.1) against exact finite discrepancies
      of derivative series (q d/dq)^j E_b, E_b^3, Theta_3;
      Lean hypotheses of poly_mass_sparse_tendsto_one for those sequences;
      CM-field support conditions, Hecke multiplicativity, the twisted Hecke
      relation for eta^10, eta^14 and its failure for eta^26;
      the b-coprime-part lemma and the valuation-surviving width lower bound;
      the counterexample showing that W(N)=o(N) is not necessary for K_b;
      classical identities for Theta^3, Theta^4, E_2, E_4, E_6, Delta.

All discrepancies, word frequencies and width densities printed below are
FINITE MEASUREMENTS.  They are not evidence of normality or non-normality.
"""

from __future__ import annotations

import math
import sys
import time
from math import gcd, isqrt, log, pi, sqrt, exp

T0 = time.time()
CHECKS = 0
KPAR = pi * sqrt(2.0 / 3.0)  # Hardy-Ramanujan exponent constant


def check(cond: bool, msg: str) -> None:
    global CHECKS
    if not cond:
        raise AssertionError(msg)
    CHECKS += 1


def header(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Certified enclosures, digits, discrepancy  (same conventions as Phase 20)
# ---------------------------------------------------------------------------


class Enc:
    """Real number x with lo <= b^K x <= hi (integers)."""

    def __init__(self, b: int, K: int, lo: int, hi: int):
        assert lo <= hi
        self.b, self.K, self.lo, self.hi = b, K, lo, hi

    def recip(self) -> "Enc":
        assert self.lo > 0
        B2 = self.b ** (2 * self.K)
        return Enc(self.b, self.K, B2 // self.hi, -((-B2) // self.lo))

    def digits(self, D: int) -> tuple[int, list[int]]:
        assert D <= self.K
        s = self.b ** (self.K - D)
        a, c = self.lo // s, self.hi // s
        if a != c:
            raise ValueError("enclosure too wide for %d digits" % D)
        ip, fr = divmod(a, self.b ** D)
        return ip, to_digits(fr, self.b, D)


def to_digits(v: int, b: int, nd: int) -> list[int]:
    if nd <= 48:
        out = [0] * nd
        for i in range(nd - 1, -1, -1):
            v, out[i] = divmod(v, b)
        return out
    lo_n = nd // 2
    hi, lo = divmod(v, b ** lo_n)
    return to_digits(hi, b, nd - lo_n) + to_digits(lo, b, lo_n)


def precision(b: int) -> int:
    P = 1
    while b ** P < 2 ** 40:
        P += 1
    return P


def orbit_points(digs: list[int], b: int, N: int) -> list[float]:
    P = precision(b)
    assert len(digs) >= N + P
    BP = b ** P
    w = 0
    for i in range(P):
        w = w * b + digs[i]
    pts = []
    for n in range(N):
        pts.append(w / BP)
        w = (w * b + digs[n + P]) % BP
    return pts


def disc(points: list[float]) -> float:
    ys = sorted(points)
    M = len(ys)
    hi = lo = 0.0
    for i, y in enumerate(ys, 1):
        hi = max(hi, i / M - y)
        lo = min(lo, (i - 1) / M - y)
    return hi - lo


def enc_from_array(b: int, a: list[int], K: int, tail_scaled: float) -> Enc:
    """x = sum_{m>=0} a[m] b^-m where |b^K * sum_{m>len(a)-1} a[m] b^-m| <= tail_scaled."""
    X = len(a) - 1
    assert X >= K
    S = 0
    for m in range(X + 1):
        S = S * b + a[m]
    q = S // b ** (X - K)
    t = int(math.ceil(tail_scaled)) + 1
    return Enc(b, K, q - t, q + 1 + t)


def disc_of(x: Enc, Ns: list[int]) -> dict[int, float]:
    P = precision(x.b)
    _, digs = x.digits(max(Ns) + P)
    pts = orbit_points(digs, x.b, max(Ns))
    return {N: disc(pts[:N]) for N in Ns}


def disc_series(b: int, a: list[int], Ns: list[int], tail_log) -> dict[int, float]:
    """Finite discrepancies of x = sum a[m] b^-m.  tail_log(m) bounds log|a(m)| for m
    beyond the array.  The precision is raised until the digits are certified (constant
    digit blocks, as in E_b, can make a short guard ambiguous)."""
    X = len(a) - 1
    for extra in (30, 90, 160, 250, 340):
        Kd = max(Ns) + precision(b) + extra
        if Kd > X - 10:
            break
        tl = 2 * sum(exp(tail_log(X + i) - (X + i - Kd) * log(b)) for i in range(1, 60))
        try:
            return disc_of(enc_from_array(b, a, Kd, tl), Ns)
        except ValueError:
            continue
    raise ValueError("could not certify digits")


# ---------------------------------------------------------------------------
# Arithmetic helpers
# ---------------------------------------------------------------------------


def partitions(M: int) -> list[int]:
    p = [0] * (M + 1)
    p[0] = 1
    for n in range(1, M + 1):
        s, k = 0, 1
        while True:
            g1 = k * (3 * k - 1) // 2
            if g1 > n:
                break
            sgn = 1 if k % 2 else -1
            s += sgn * p[n - g1]
            g2 = k * (3 * k + 1) // 2
            if g2 <= n:
                s += sgn * p[n - g2]
            k += 1
        p[n] = s
    return p


def pent_list(M: int) -> list[tuple[int, int]]:
    """Generalized pentagonal g_k <= M (k != 0), sorted, with sign eps_k=(-1)^(k+1)."""
    out = []
    k = 1
    while k * (3 * k - 1) // 2 <= M:
        s = 1 if k % 2 else -1
        out.append((k * (3 * k - 1) // 2, s))
        g2 = k * (3 * k + 1) // 2
        if g2 <= M:
            out.append((g2, s))
        k += 1
    out.sort()
    return out


def euler_coeffs(M: int) -> list[int]:
    c = [0] * (M + 1)
    c[0] = 1
    for g, s in pent_list(M):
        c[g] -= s  # E = 1 - sum eps_k q^{g_k}
    return c


def jacobi_coeffs(M: int) -> list[int]:
    c = [0] * (M + 1)
    k = 0
    while k * (k + 1) // 2 <= M:
        c[k * (k + 1) // 2] += (-1) ** k * (2 * k + 1)
        k += 1
    return c


def theta_coeffs(M: int) -> list[int]:
    c = [0] * (M + 1)
    c[0] = 1
    n = 1
    while n * n <= M:
        c[n * n] += 2
        n += 1
    return c


def smul(f: list[int], s: list[int], M: int) -> list[int]:
    """Product of f (any) with sparse s, truncated at M."""
    sp = [(i, v) for i, v in enumerate(s[: M + 1]) if v]
    out = [0] * (M + 1)
    for i, v in sp:
        lim = M + 1 - i
        for n in range(lim):
            fn = f[n]
            if fn:
                out[n + i] += v * fn
    return out


def dmul(f: list[int], g: list[int], M: int) -> list[int]:
    out = [0] * (M + 1)
    for i in range(M + 1):
        fi = f[i]
        if fi:
            for j in range(M + 1 - i):
                out[i + j] += fi * g[j]
    return out


def divisor_sums(M: int, k: int) -> list[int]:
    s = [0] * (M + 1)
    for d in range(1, M + 1):
        dk = d ** k
        for m in range(d, M + 1, d):
            s[m] += dk
    return s


def spf_table(M: int) -> list[int]:
    spf = list(range(M + 1))
    for i in range(2, isqrt(M) + 1):
        if spf[i] == i:
            for j in range(i * i, M + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factor(n: int, spf: list[int]) -> dict[int, int]:
    f: dict[int, int] = {}
    while n > 1:
        p = spf[n]
        f[p] = f.get(p, 0) + 1
        n //= p
    return f


def vb(x: int, b: int) -> int:
    x = abs(x)
    v = 0
    while x % b == 0:
        x //= b
        v += 1
    return v


def ndig(x: int, b: int) -> int:
    """Number of base-b digits of |x| > 0."""
    x = abs(x)
    d = 0
    while x:
        x //= b
        d += 1
    return d


def coprime_part(x: int, b: int) -> int:
    x = abs(x)
    for q in range(2, b + 1):
        if b % q == 0 and all(q % r for r in range(2, q)):
            while x % q == 0:
                x //= q
    return x


# ===========================================================================
# D3.  The partition constant P_b
# ===========================================================================


def tail_exact_lt(p: list[int], b: int, n: int, L: int, tau_den: int) -> bool:
    """Certify T(n,L) = sum_{j>L} p(n+j) b^-j < 1/tau_den: exact integer finite part
    (L < j <= L+G) plus the eta-refined analytic bound for j > L+G."""
    G = 160
    assert n + L + G + 1 < len(p)
    S = 0
    for j in range(L + 1, L + G + 1):
        S = S * b + p[n + j]
    # T(n,L) = (S + far) / b^(L+G) with 0 <= far <= mod_tail_bound(n+L+G+1, b)
    far = mod_tail_bound(n + L + G + 1, b)
    far_int = int(far * (1 + 1e-6)) + 1
    return (S + far_int) * tau_den < b ** (L + G)


def elem_tail_bound(m0: int, b: int) -> float:
    """Elementary bound for sum_{i>=0} p(m0+i) b^-(i+1):
    exp(K sqrt(m0)) b^-1 / (1 - exp(-(log b - K/(2 sqrt m0))))."""
    lam = log(b) - KPAR / (2 * sqrt(m0))
    if lam <= 0:
        return float("inf")
    lg = KPAR * sqrt(m0) - log(b) - log(1 - exp(-lam))
    return exp(lg) if lg < 700 else float("inf")


CMOD = 1.0000001


def mod_tail_bound(m0: int, b: int) -> float:
    """Eta-refined: p(m) <= CMOD (24 m)^(-1/4) exp(K sqrt m), decreasing prefactor."""
    return CMOD * (24 * m0) ** (-0.25) * elem_tail_bound(m0, b)


def window_elem(N: int, b: int, tau: float, refined: bool) -> int:
    """Least L with  max_{n<N} T(n,L) = T(N-1,L) <= bound < tau."""
    L = 0
    while True:
        # T(N-1,L) = sum_{j>L} p(N-1+j) b^-j = b^-L * sum_{i>=0} p(N+L+i) b^-(i+1)
        bd = (mod_tail_bound if refined else elem_tail_bound)(N + L, b)
        if bd < float("inf") and log(bd) - L * log(b) < log(tau):
            return L
        L += 1


def window_exact(p: list[int], N: int, b: int, tau_den: int) -> int:
    L = 0
    while not tail_exact_lt(p, b, N - 1, L, tau_den):
        L += 1
    return L


def window_nec(p: list[int], N: int, b: int, tau_den: int) -> int:
    """Least L with p(N+L) b^-(L+1) < 1/tau_den (necessary for T(N-1,L) < tau)."""
    L = 0
    while p[N + L] * tau_den >= b ** (L + 1):
        L += 1
    return L


def section_partition_bounds(p: list[int]) -> None:
    header("D3.1  Elementary and eta-refined bounds for p(n)")
    M = len(p) - 1
    worst_el = worst_mod = 1e9
    for n in range(1, M + 1):
        lp = math.log(p[n])
        el = KPAR * sqrt(n) - lp
        md = log(CMOD) - 0.25 * log(24 * n) + KPAR * sqrt(n) - lp
        check(el > 0, "elementary bound p(n) < exp(K sqrt n) at n=%d" % n)
        check(md >= 0, "eta-refined bound at n=%d" % n)
        worst_el = min(worst_el, el)
        worst_mod = min(worst_mod, md)
    print("p(n) < exp(pi sqrt(2n/3)) for 1<=n<=%d; least log-margin %.4f" % (M, worst_el))
    print("p(n) <= 1.0000001 (24n)^(-1/4) exp(pi sqrt(2n/3)) for 1<=n<=%d; least log-margin %.4f"
          % (M, worst_mod))
    for n in (100, 1000, M):
        hr = KPAR * sqrt(n) - log(4 * sqrt(3) * n)
        print("  n=%5d  log p(n) - log(HR main term) = %+.5f" % (n, math.log(p[n]) - hr))


def section_windows(p: list[int]) -> dict[tuple[int, int], int]:
    header("D3.2  Certified all-N carry windows for P_b  (tau = N^-2)")
    print("  b      N   L_nec  L_exact  L_mod  L_elem  L_asym   (L_asym = K sqrtN/ln b + K^2/(2 ln^2 b) + log_b(N^2/(b-1)))")
    out = {}
    for b in (2, 3, 5, 10):
        for N in (100, 1000, 4000):
            td = N * N
            Ln = window_nec(p, N, b, td)
            Lx = window_exact(p, N, b, td)
            Lm = window_elem(N, b, 1.0 / td, True)
            Le = window_elem(N, b, 1.0 / td, False)
            La = KPAR * sqrt(N) / log(b) + KPAR ** 2 / (2 * log(b) ** 2) + (2 * log(N) - log(b - 1)) / log(b)
            check(Ln <= Lx <= Lm <= Le, "window ordering b=%d N=%d" % (b, N))
            # gap between the elementary window and the necessary one is O(log_b N)
            check(Le - Ln <= log(4 * sqrt(3) * (N + Le)) / log(b) + 4, "elementary window gap b=%d N=%d" % (b, N))
            if N >= 1000:
                check(abs(Le - La) <= 3, "asymptotic window formula b=%d N=%d" % (b, N))
            out[(b, N)] = Lx
            print("  %-3d %6d  %5d  %7d  %5d  %6d  %6.1f" % (b, N, Ln, Lx, Lm, Le, La))
    return out


def pb_enc(p: list[int], b: int, D: int, tau_den: int) -> Enc:
    """Enclosure of P_b b^D... returned as Enc with K = D + L."""
    L = window_exact(p, D + 1, b, tau_den)  # covers T(D, L)
    S = 0
    for n in range(D + L + 1):
        S = S * b + p[n]
    # P_b b^(D+L) = S + b^L T(D,L),  0 <= b^L T(D,L) < b^L / tau_den
    return Enc(b, D + L, S, S + -(-(b ** L) // tau_den))


def euler_enc(b: int, K: int) -> Enc:
    c = euler_coeffs(K + 5)
    S = 0
    for m in range(K + 1):
        S = S * b + c[m]
    return Enc(b, K, S - 1, S + 1)


def section_pb_digits(p: list[int]) -> dict[int, list[int]]:
    header("D3.3  Certified digits of P_b (window method vs 1/E_b), carry recurrences")
    N = 4000
    digits = {}
    for b in (2, 3, 5, 10):
        P = precision(b)
        D = N + P + 4
        x = pb_enc(p, b, D, 10 ** 12)
        ip, dg = x.digits(D)
        y = euler_enc(b, D + 40).recip()
        ip2, dg2 = y.digits(D)
        check(ip == ip2 and dg == dg2, "P_b digits agree b=%d" % b)
        digits[b] = dg
        print("  b=%-2d  %d certified digits agree (window enclosure vs reciprocal of E_b)" % (b, D))

    # Shift register and pentagonal window identity (exact integers)
    pl = pent_list(4000)
    for b in (2, 3, 10):
        L = 30
        BL = b ** L
        R = [sum(p[n + j] * b ** (L - j) for j in range(1, L + 1)) for n in range(400)]
        for n in range(399):
            check((b * R[n] + p[n + L + 1]) % BL == R[n + 1] % BL, "shift register b=%d n=%d" % (b, n))
        for n in range(1, 400):
            rhs = 0
            for g, s in pl:
                if g <= n:
                    rhs += s * R[n - g]
                elif g < n + L + 1:
                    rhs += s * sum(p[n + j - g] * b ** (L - j) for j in range(g - n, L + 1))
                else:
                    break
            check(rhs == R[n], "pentagonal window identity b=%d n=%d" % (b, n))
    print("  R_{n+1,L} = b R_{n,L} + p(n+L+1) (mod b^L): checked n<399, L=30, b=2,3,10")
    print("  R_{n,L} = sum_{g<=n} eps R_{n-g,L} + boundary (exact integers): checked 1<=n<400")

    # Lemma D1.1 transfer: 0 <= x_n - R_{n,L}/b^L < T(n,L) < 1e-12 (mod 1), so the first
    # d digits of x_n equal those of R_{n,L} up to one final carry, d = 30 binary digits
    b = 2
    dg = digits[b]
    L = window_exact(p, N, b, 10 ** 12)
    d = 30
    carries = 0
    for n in range(0, N, 7):
        R = sum(p[n + j] * b ** (L - j) for j in range(1, L + 1)) % b ** L
        top = 0
        for i in range(d):
            top = top * b + dg[n + i]
        diff = (top - R // b ** (L - d)) % b ** d
        check(diff in (0, 1), "window transfer n=%d" % n)
        carries += diff
    print("  b=2, L=%d: first %d digits of x_n equal those of R_{n,L} up to one final carry"
          " (%d carries in %d samples)" % (L, d, carries, len(range(0, N, 7))))
    return digits


def section_pb_measure(digits: dict[int, list[int]], p: list[int]) -> None:
    header("D3.4  Finite measurements for P_b (NOT evidence of normality)")
    for b in (2, 3, 5, 10):
        dg = digits[b]
        pts = orbit_points(dg, b, 4000)
        line = "  b=%-2d " % b + "  ".join("D_%d=%.4f" % (N, disc(pts[:N])) for N in (1000, 2000, 4000))
        print(line)
        for ell in ((1, 2, 3, 4) if b == 2 else (1, 2)):
            cnt: dict[tuple, int] = {}
            tot = 4000 - ell + 1
            for i in range(tot):
                w = tuple(dg[i: i + ell])
                cnt[w] = cnt.get(w, 0) + 1
            exp_ = tot / b ** ell
            chi2 = sum((cnt.get(w, 0) - exp_) ** 2 / exp_ for w in all_words(b, ell))
            dev = max(abs(cnt.get(w, 0) / tot - b ** -ell) for w in all_words(b, ell))
            print("        words of length %d: max|freq-b^-%d| = %.4f, chi^2 = %.1f on %d d.f."
                  % (ell, ell, dev, chi2, b ** ell - 1))


def all_words(b: int, ell: int):
    if ell == 0:
        yield ()
        return
    for w in all_words(b, ell - 1):
        for d in range(b):
            yield w + (d,)


def section_solved_tail(p: list[int], digits: dict[int, list[int]]) -> None:
    """T_n = sum_{m<=n} p(n-m) beta_m,  beta_m = P_b sum_{g>m} eps_g b^(m-g)  (b = 2)."""
    dg = digits[2]
    D = len(dg)
    frac = 0
    for d in dg:
        frac = frac * 2 + d
    # integer part of P_2: P_2 = 1/E_2 with E_2 = 0.2887880950...
    Pint = 3 * 2 ** D + frac  # floor(P_2 2^D)
    check(abs(Pint / 2 ** D - 3.4627466194550636) < 1e-12, "P_2 numerical value")
    pl = pent_list(D + 200)
    for n in range(0, 41):
        Tn = Pint * 2 ** n - 2 ** D * sum(p[k] * 2 ** (n - k) for k in range(n + 1))
        tot = 0
        for m in range(n + 1):
            beta = sum(e * ((Pint * 2 ** m) >> g) for g, e in pl if g > m)
            tot += p[n - m] * beta
        tol = 2 ** n + 300 * sum(p[: n + 1])
        check(abs(Tn - tot) <= tol, "solved tail identity n=%d" % n)
    print("  T_n = sum_{m<=n} p(n-m) beta_m with beta_m = P_b sum_{g>m} eps b^(m-g): checked n<=40, b=2")


def section_recurrence_empty(p: list[int]) -> None:
    header("D3.5  The circle recurrence admits equidistributed and zero solutions")
    # theta = (sqrt5 - 1)/2 * 2^-10, to 600 bits
    B = 600
    th = (isqrt(5 * 4 ** B) - 2 ** B) // 2 // 2 ** 10  # theta * 2^B
    M = 4000
    pl = pent_list(M)
    vals = [th * p[n] for n in range(M)]
    for n in range(1, M, 13):
        s = 0
        for g, e in pl:
            if g > n:
                break
            s += e * vals[n - g]
        check(s == vals[n], "theta p(n) solves the homogeneous recurrence at n=%d" % n)
    mask = (1 << B) - 1
    pts = [((v & mask) >> (B - 52)) / 2.0 ** 52 for v in vals]
    print("  xi_n = {theta p(n)}, theta = (sqrt5-1)/2^11: exact homogeneous recurrence checked;")
    print("  finite D_4000(xi) = %.4f (finite measurement); the zero solution has D_N = 1." % disc(pts))
    print("  Both satisfy x_n = sum eps_k x_{n-g_k} + rho_n with |rho_n| inside the Phase 20 bound.")


def section_approximants(p: list[int], digits: dict[int, list[int]]) -> None:
    header("D3.6  Rational approximants r_K = b^{m_K}/Q_K = 1/E_b^{(K)}")
    pl = pent_list(2000)
    small = []
    for b in (2, 3, 5, 10):
        dg = digits[b]
        rows = []
        Kmax = 34 if b == 2 else 28
        for K in range(3, Kmax + 1):
            mK = pl[K - 1][0]
            mK1 = pl[K][0]
            Q = b ** mK
            for g, s in pl[:K]:
                Q -= s * b ** (mK - g)
            check(Q > 0 and gcd(Q, b) == 1 and Q % b in (1, b - 1), "Q_K unit mod b, b=%d K=%d" % (b, K))
            check(Q.bit_length() >= (mK - 1) * math.log2(b), "Q_K size b=%d K=%d" % (b, K))
            # agreement of fractional digits of r_K with P_b
            D = mK1 + 8
            if D + 2 > len(dg):
                break
            num = b ** (mK + D)
            fr = (num // Q) % b ** D
            rd = to_digits(fr, b, D)
            A = 0
            while A < D and rd[A] == dg[A]:
                A += 1
            check(A <= mK1, "agreement bounded by m_{K+1} b=%d K=%d" % (b, K))
            # multiplicative order exceeds 20 m_{K+1}
            v, ordK = 1, None
            for m in range(1, 20 * mK1 + 1):
                v = v * b % Q
                if v == 1:
                    ordK = m
                    break
            if ordK is not None:
                small.append((b, K, ordK, mK1))
            if K >= 6:
                check(ordK is None, "ord_{Q_K}(b) > 20 m_{K+1}, b=%d K=%d" % (b, K))
            rows.append((K, mK, mK1, A))
        Ks = [r for r in rows if r[0] in (5, 10, 15, 20, 25, 30)]
        print("  b=%-2d  K: m_K, m_{K+1}, agreeing digits A_K, excess A_K - m_K:" % b)
        print("        " + "; ".join("K=%d: %d,%d,%d,%+d" % (K, a, c, A, A - a) for K, a, c, A in Ks))
    print("  Small orders ord_{Q_K}(b) <= 20 m_{K+1} (b, K, ord, m_{K+1}): %s" % small)
    print("  For all K tested: Q_K = +-1 mod b and A_K <= m_{K+1}; for 6 <= K, ord_{Q_K}(b) > 20 m_{K+1}.")
    print("  The prefix tracked by r_K covers < 1/20 of one period of r_K.")


# ===========================================================================
# D4.  Polynomial-mass transfer, derivatives, the width-density wall
# ===========================================================================


def Mkappa(b: int, kappa: float) -> float:
    return (1 - 1 / b) * sum((1 + i) ** kappa * b ** -i for i in range(4000))


def thm_d41_bound(b: int, N: int, S_Nm1: int, C: float, kappa: float) -> float:
    rho = (1 + S_Nm1) / N
    c = 2 ** (kappa + 1) * C * Mkappa(b, kappa) / (b - 1)
    return rho * max(2.0, 2 * log(1 / rho) / log(b) + (kappa - 1) * log(N) / log(b) + max(0.0, log(c) / log(b)) + 3)


def section_derivatives() -> None:
    header("D4.1  Derivatives (q d/dq)^j of unary series: Theorem D4.1 vs exact finite D_N")
    N = 4000
    Ns = [1000, 4000]
    families = []
    XL = N + 400
    E = euler_coeffs(XL)
    J3 = jacobi_coeffs(XL)
    T3 = theta_coeffs(XL)
    # (name, base sequence, C, kappa0 with A(X) <= C X^(kappa0) for j=0)
    families.append(("E_b", E, 3.0, 0.5))
    families.append(("E_b^3", J3, 4.0, 1.0))
    families.append(("Theta_3", T3, 3.0, 0.5))
    print("  1-D_N (finite), bound of Theorem D4.1, ratio (1-D_N)/(rho_N log_b N); kappa = j + kappa0")
    for name, base, C, k0 in families:
        for j in (0, 1, 2, 3):
            a = [m ** j * base[m] for m in range(XL + 1)]
            kappa = j + k0
            # Mass hypothesis A(X) <= C X^kappa (all X <= XL) and Lean form A(X) <= C (X+1)^k
            A = 0
            kl = math.ceil(kappa)
            okm = True
            for X in range(1, XL + 1):
                A += abs(a[X])
                if A > C * X ** kappa or A > C * (X + 1) ** kl:
                    okm = False
                    break
            check(okm, "mass hypothesis %s j=%d" % (name, j))
            for b in (2, 3, 10):
                # tail beyond XL: |a(m)| <= A(m) <= C m^kappa
                prof = disc_series(b, a, Ns, lambda m: log(C) + kappa * log(m))
                outs = []
                for Nn in Ns:
                    S = sum(1 for m in range(1, Nn) if a[m])
                    bd = thm_d41_bound(b, Nn, S, C, kappa)
                    dfc = 1 - prof[Nn]
                    check(dfc <= bd + 1e-9, "Theorem D4.1 bound %s j=%d b=%d N=%d" % (name, j, b, Nn))
                    rho = (1 + S) / Nn
                    outs.append("N=%d: %.4f<=%.3f r=%.2f" % (Nn, dfc, bd, dfc / (rho * log(Nn) / log(b))))
                if b == 2 or j in (0, 3):
                    print("  %-8s j=%d b=%-2d  %s" % (name, j, b, "   ".join(outs)))
    # Lean sparsity hypothesis S(N) log N / N
    for name, base in (("pentagonal", E), ("triangular", J3), ("squares", T3)):
        vals = []
        for Nn in (100, 1000, 4000):
            S = sum(1 for m in range(1, Nn + 1) if base[m])
            vals.append(S * log(Nn) / Nn)
        check(vals[0] > vals[1] > vals[2], "S log N / N decreasing for %s" % name)
        print("  S(N) log N / N for %s support: %s" % (name, ", ".join("%.3f" % v for v in vals)))


def section_counterexample() -> None:
    header("D4.2  W(N) = o(N) is sufficient, not necessary, for K_b")
    b = 2
    X = 4300
    a = [0] * (X + 1)
    for m in range(1, X + 1):
        a[m] = 2 ** m.bit_length() - 1
    # F = sum (2^{w(m)}-1) 2^-m = sum 2^{-(m-w(m))} - 1 ; check on the truncation exactly
    lhs = sum(a[m] * 2 ** (X - m) for m in range(1, X + 1))
    rhs = sum(2 ** (X - (m - m.bit_length())) for m in range(1, X + 1)) - (2 ** X - 1)
    check(lhs == rhs, "telescoped identity for the width counterexample")
    t = [m - m.bit_length() for m in range(1, X + 1)]
    check(all(0 <= t[i + 1] - t[i] <= 1 for i in range(len(t) - 1)), "t(m) steps are 0 or 1")
    prof = disc_series(2, a, [1000, 4000], lambda m: m.bit_length() * log(2))
    W = {N: sum(m.bit_length() for m in range(1, N + 1)) for N in (1000, 4000)}
    for N in (1000, 4000):
        print("  N=%d: W(N)/N = %.2f (grows like log_2 N), D_N = %.4f" % (N, W[N] / N, prof[N]))
    check(prof[4000] > 0.95, "counterexample orbit concentrates (finite check)")
    print("  F = sum_{t in J} 2^-t + (element of F_2), J = {t : t(m)=t(m+1)} of size O(log X): F in K_2.")


def eta_powers(X: int) -> dict[int, list[int]]:
    E = euler_coeffs(X)
    J = jacobi_coeffs(X)
    P: dict[int, list[int]] = {1: E, 3: J}
    P[2] = smul(E, E, X)
    P[4] = smul(J, E, X)
    P[6] = smul(J, J, X)
    P[7] = smul(P[6], E, X)
    P[8] = smul(P[7], E, X)
    P[9] = smul(P[6], J, X)
    P[10] = smul(P[9], E, X)
    P[11] = smul(P[10], E, X)
    P[14] = smul(P[11], J, X)
    P[17] = smul(P[14], J, X)
    P[20] = smul(P[17], J, X)
    P[23] = smul(P[20], J, X)
    P[24] = smul(P[23], E, X)
    P[26] = smul(P[23], J, X)
    return P


def section_eta(P: dict[int, list[int]], X: int) -> None:
    header("D4.3  Serre's lacunary eta powers: CM structure, support and width densities")
    spf = spf_table(24 * X + 30)
    # index map n -> N' = (24 n + r)/g, g = gcd(24, r)
    weight = {2: 1, 4: 2, 6: 3, 8: 4, 10: 5, 14: 7, 26: 13}
    print("  r  wt  S(X)/X  S logX/X  S sqrt(logX)/X  W_2/X  W_10/X  WU_2/X  WU_10/X  cover_2  field")
    for r in (2, 4, 6, 8, 10, 14, 26):
        g = gcd(24, r)
        c = P[r]
        viol_i = viol_3 = both = 0
        S = W2 = W10 = U2 = U10 = 0
        cover = bytearray(X + 1)
        for n in range(1, X + 1):
            v = c[n]
            if v == 0:
                continue
            S += 1
            Np = (24 * n + r) // g
            f = factor(Np, spf)
            bi = any(q % 4 == 3 and e % 2 for q, e in f.items())
            b3 = any(q % 3 == 2 and e % 2 for q, e in f.items())
            viol_i += bi
            viol_3 += b3
            both += bi and b3
            d2, d10 = ndig(v, 2), ndig(v, 10)
            W2 += d2
            W10 += d10
            v2, v10 = vb(v, 2), vb(v, 10)
            U2 += d2 - v2
            U10 += d10 - v10
            for t in range(max(0, n - d2), n - v2):  # binary digit footprint [n-d, n-v-1]
                cover[t] = 1
        if r == 2:
            check(viol_i == 0 and viol_3 == 0, "eta^2 support obeys both CM conditions")
            fld = "Q(i)&Q(s-3)"
        elif r in (4, 8, 14):
            check(viol_3 == 0 and viol_i > 0, "eta^%d: CM by Q(sqrt-3)" % r)
            fld = "Q(sqrt-3)"
        elif r in (6, 10):
            check(viol_i == 0 and viol_3 > 0, "eta^%d: CM by Q(i)" % r)
            fld = "Q(i)"
        else:
            check(both == 0 and viol_i > 0 and viol_3 > 0, "eta^26: mixed Q(i)/Q(sqrt-3) support")
            fld = "mixed"
        lx = log(X)
        print("  %-2d %-3d %.4f  %.3f     %.3f          %6.2f  %6.2f  %6.2f  %6.2f   %.3f    %s"
              % (r, weight[r], S / X, S * lx / X, S * sqrt(lx) / X, W2 / X, W10 / X, U2 / X, U10 / X,
                 sum(cover[:X]) / X, fld))
    # weight-one eta^2: a(p) = 0 unless p = 1 mod 12, and then a(p) = +-2
    c = P[2]
    A2 = {(12 * n + 1): c[n] for n in range(X + 1)}
    cnt = 0
    for q in range(13, 12 * X + 1, 12):
        if spf[q] == q:
            check(A2[q] in (2, -2), "eta^2: a(p)=+-2 for p=1 mod 12")
            cnt += 1
    print("  eta^2 (weight 1): indices are 1 mod 12; a(p) = +-2 on all %d primes p = 1 mod 12 <= %d," % (cnt, 12 * X))
    print("  so primes with a(p) = 0 have density 3/4 and S(X) ~ c X/(log X)^(3/4).")


def section_hecke(P: dict[int, list[int]], X: int) -> None:
    header("D4.4  Hecke structure, b-coprime parts and the valuation-surviving width bound")
    spf = spf_table(24 * X + 30)
    # Newforms: eta(6t)^4 (36.2.a.a), eta(4t)^6 (16.3.c.a, char chi_-4), eta(3t)^8 (9.4.a.a)
    for r, k, chi in ((4, 2, lambda q: 1), (6, 3, lambda q: 1 if q % 4 == 1 else -1), (8, 4, lambda q: 1)):
        g = gcd(24, r)
        A = {(24 * n + r) // g: P[r][n] for n in range(X + 1)}
        Mx = max(A)
        mods = 24 // g
        cnt = 0
        for m in range(1, 400):
            if m not in A:
                continue
            for n in range(1, Mx // m + 1):
                if n in A and m * n in A and gcd(m, n) == 1:
                    check(A[m * n] == A[m] * A[n], "multiplicativity r=%d" % r)
                    cnt += 1
        hp = 0
        for q in range(5, isqrt(Mx) + 1):
            if spf[q] == q and q in A and q * q in A:
                check(A[q * q] == A[q] ** 2 - chi(q) * q ** (k - 1), "Hecke p^2 relation r=%d p=%d" % (r, q))
                check(abs(A[q]) <= 2 * q ** ((k - 1) / 2) + 1e-9, "Hecke/Deligne bound r=%d" % r)
                hp += 1
        print("  eta^%-2d (weight %d): a(mn)=a(m)a(n) on %d coprime pairs; a(p^2)=a(p)^2-chi(p)p^(k-1) on %d primes"
              % (r, k, cnt, hp))
    # Twisted Hecke relation for 10, 14; failure for 26
    for r in (10, 14, 26):
        g = gcd(24, r)
        m0 = r // g
        A = {(24 * n + r) // g: P[r][n] for n in range(X + 1)}
        ok = bad = 0
        for q in range(13, 600, 12):
            if spf[q] != q:
                continue
            for m in range(m0, 12 * X, 12):
                if q * m not in A:
                    break
                if gcd(m, q) == 1:
                    if A[q * m] == A[q * m0] * A[m]:
                        ok += 1
                    else:
                        bad += 1
        if r in (10, 14):
            check(bad == 0 and ok > 500, "twisted Hecke relation eta^%d" % r)
        else:
            check(bad > ok, "twisted Hecke relation fails for eta^26")
        print("  eta^%-2d: a(pm) = a(p m0) a(m) for p = 1 mod 12, (m,p)=1: %d hold, %d fail" % (r, ok, bad))

    # b-coprime lemma: |U(xy)| >= coprime_b(x)
    for b in (2, 6, 10, 12):
        for x in range(1, 120):
            for y in range(1, 120):
                z = x * y
                U = z // b ** vb(z, b)
                check(U >= coprime_part(x, b), "b-coprime lemma b=%d x=%d y=%d" % (b, x, y))
    print("  Lemma W.1 (|U(xy)| >= b-coprime part of x): checked 1<=x,y<120, b in {2,6,10,12}")

    # Valuation-surviving construction  n' = p m  (p > sqrt(Y) good prime)
    for r, k in ((4, 2), (6, 3), (8, 4), (10, 5), (14, 7)):
        g = gcd(24, r)
        mods = 24 // g
        m0 = r // g
        A = {(24 * n + r) // g: P[r][n] for n in range(X + 1)}
        Y = max(A)
        lam = {}
        good_frac = {}
        for b in (2, 10):
            qs = [q for q in (2, 3, 5) if b % q == 0]
            e0 = 3
            tot = good = 0
            for q in range(5, Y // m0 + 1):
                if spf[q] != q or q % mods != 1 % mods:
                    continue
                lp = A.get(q * m0)
                if lp is None:
                    continue
                tot += 1
                if lp != 0 and abs(lp) >= q ** ((k - 1) / 2) and all(vb(lp, qq) <= e0 for qq in qs):
                    good += 1
                    lam[(b, q)] = lp
            good_frac[b] = good / max(tot, 1)
        # count n' = q m <= Y with q good (b=10), q > sqrt(Y), m in support, and check widths
        cntn = 0
        minexcess = 1e9
        for (b, q), lp in lam.items():
            if b != 10 or q * q <= Y:
                continue
            for m in range(m0, Y // q + 1, mods):
                v = A.get(q * m)
                if v is None or A.get(m, 0) == 0:
                    continue
                check(v * A[m0] == lp * A[m], "factorization a(qm) = lambda(q) a(m), r=%d" % r)
                U = abs(v) // 10 ** vb(v, 10)
                check(U >= coprime_part(lp, 10), "valuation survival r=%d" % r)
                u = ndig(U, 10)
                minexcess = min(minexcess, u - ((k - 1) / 2 * log(q, 10) - 3))
                cntn += 1
        check(minexcess > 0, "displaced width u(n) > ((k-1)/2) log_10 p - e0, r=%d" % r)
        Xn = Y * mods / 24.0  # radix index scale
        print("  eta^%-2d: good primes (|a|>=p^((k-1)/2), v_q<=3): %.2f (b=2), %.2f (b=10);"
              " constructed n' = p m: %d  (X/sqrt(log X) = %.0f)"
              % (r, good_frac[2], good_frac[10], cntn, X / sqrt(log(X))))


def section_products(P: dict[int, list[int]], X: int) -> None:
    header("D4.5  Where derivatives hit the wall: unary vs binary/weight-one objects")
    T3 = theta_coeffs(X)
    T2 = smul(T3, T3, X)
    E2 = P[2]
    lx = log(X)
    for name, base in (("D^j Theta_3", T3), ("D^j E_b", P[1]), ("D^j Theta_3^2", T2), ("D^j E_b^2", E2)):
        S = sum(1 for m in range(1, X + 1) if base[m])
        for j in (0, 1, 2):
            W2 = sum(ndig(m ** j * base[m], 2) for m in range(1, X + 1) if base[m])
            print("  %-14s j=%d: S logX/X = %.3f, W_2(X)/X = %.3f" % (name, j, S * lx / X, W2 / X))
    # E_b * D E_b = (1/2) D(E_b^2): exact identity
    E = P[1]
    DE = [m * E[m] for m in range(X + 1)]
    prod = smul(DE, E, X)
    check(all(2 * prod[m] == m * E2[m] for m in range(X + 1)), "E_b * D E_b = D(E_b^2)/2")
    print("  identity E_b (q d/dq)E_b = (1/2)(q d/dq)E_b^2 checked through q^%d" % X)
    # E_b^2 (q d/dq)E_b = (1/3)(q d/dq)E_b^3 = sum (-1)^k k(k+1)(2k+1)/6 q^{k(k+1)/2}
    prod3 = smul(prod, E, X)
    J = P[3]
    tri = [0] * (X + 1)
    k = 0
    while k * (k + 1) // 2 <= X:
        tri[k * (k + 1) // 2] = (-1) ** k * (k * (k + 1) * (2 * k + 1) // 6)
        k += 1
    check(all(3 * prod3[m] == m * J[m] for m in range(X + 1)), "E^2 DE = D(E^3)/3")
    check(all(prod3[m] == tri[m] for m in range(X + 1)), "E^2 DE has triangular support")
    print("  identity E_b^2 (q d/dq)E_b = sum_k (-1)^k k(k+1)(2k+1)/6 q^{k(k+1)/2} checked through q^%d" % X)


def section_dense(P: dict[int, list[int]]) -> None:
    header("D4.6  Dense classical constants: identities, width densities, finite D_N")
    X = 6000
    T3 = theta_coeffs(X)
    T2 = smul(T3, T3, X)
    Th3 = smul(T2, T3, X)
    Th4 = smul(Th3, T3, X)
    s1, s3, s5 = divisor_sums(X, 1), divisor_sums(X, 3), divisor_sums(X, 5)
    E2 = [1] + [-24 * s1[n] for n in range(1, X + 1)]
    E4 = [1] + [240 * s3[n] for n in range(1, X + 1)]
    E6 = [1] + [-504 * s5[n] for n in range(1, X + 1)]
    # Jacobi four squares and Theta^4 = (4 E2(q^4) - E2(q))/3
    s1_4 = [s1[n] - (4 * s1[n // 4] if n % 4 == 0 else 0) for n in range(X + 1)]
    check(all(Th4[n] == 8 * s1_4[n] for n in range(1, X + 1)), "Jacobi r_4(n) = 8 sum_{d|n,4!|d} d")
    check(all(3 * Th4[n] == (4 * (E2[n // 4] if n % 4 == 0 else 0) - E2[n]) for n in range(X + 1)),
          "Theta^4 = (4E2(q^4) - E2(q))/3")
    # Legendre / Gauss: r_3(n) = 0 iff n = 4^a(8k+7)
    for n in range(1, X + 1):
        m = n
        while m % 4 == 0:
            m //= 4
        check((Th3[n] == 0) == (m % 8 == 7), "Legendre three squares n=%d" % n)
    # Delta = (E4^3 - E6^2)/1728 = q E^24
    Xs = 400
    E4c = dmul(dmul(E4[: Xs + 1], E4[: Xs + 1], Xs), E4[: Xs + 1], Xs)
    E6c = dmul(E6[: Xs + 1], E6[: Xs + 1], Xs)
    E24 = P[24]
    check(all((E4c[n] - E6c[n]) == 1728 * (E24[n - 1] if n >= 1 else 0) for n in range(Xs + 1)),
          "Delta = (E4^3-E6^2)/1728 = q prod(1-q^n)^24")
    print("  Jacobi r_4, Theta^4 = (4E_2(q^4)-E_2(q))/3, Legendre r_3 criterion: checked n<=%d" % X)
    print("  Delta = (E_4^3-E_6^2)/1728 = q prod(1-q^n)^24: checked through q^%d" % Xs)

    tau = [0] + E24[:X]  # Delta coefficients tau(n), tau(0)=0
    series = (("Theta^3", Th3, lambda n: 2 * log(2 * sqrt(n) + 2) + 1),
              ("Theta^4", Th4, lambda n: log(8 * n * (1 + log(n)))),
              ("E_2(1/b)", E2, lambda n: log(24 * n * (1 + log(n)))),
              ("E_4(1/b)", E4, lambda n: log(240 * 1.21 * n ** 3)),
              ("E_6(1/b)", E6, lambda n: log(504 * 1.04 * n ** 5)),
              ("Delta(1/b)", tau, lambda n: log(n ** 6.0 * 2 * sqrt(n) + 1)))
    N = 4000
    print("  name          W_2(N)/N  W_10(N)/N   D_N b=2       D_N b=10   (finite measurements)")
    for name, a, lb in series:
        W2 = sum(ndig(a[n], 2) for n in range(1, N + 1) if a[n]) / N
        W10 = sum(ndig(a[n], 10) for n in range(1, N + 1) if a[n]) / N
        res = []
        for b in (2, 10):
            res.append(disc_series(b, a, [N], lb)[N])
        print("  %-12s  %7.2f  %8.2f   %.4f        %.4f" % (name, W2, W10, res[0], res[1]))
    print("  Mod K_b (Phase 20, L = L_chi4(b)):  Theta^4 = 16 L^2,  Theta^3 = 4 Theta L,")
    print("  and therefore E_2(1/b) = 4 E_2(b^-4) - 48 L^2  (mod K_b).  These decide nothing.")
    # check the coefficient identity behind E_2(q) = 4E_2(q^4) - 3 Theta^4
    check(all(E2[n] == 4 * (E2[n // 4] if n % 4 == 0 else 0) - 3 * Th4[n] for n in range(X + 1)),
          "E_2(q) = 4E_2(q^4) - 3Theta(q)^4")


def section_eta_disc(P: dict[int, list[int]], X: int) -> None:
    header("D4.7  Finite D_N for eta powers in base 2 (finite measurements only)")
    N = 4000
    out = []
    for r in (1, 2, 3, 4, 6, 8, 10, 14, 26):
        a = P[r]
        # crude: |coef of prod(1-q^n)^r| <= coef of prod(1-q^n)^-r <= exp(pi sqrt(2 r n/3))
        a = a[: N + 1500]
        out.append("r=%d: %.4f" % (r, disc_series(2, a, [N], lambda m: pi * sqrt(2 * r * m / 3.0))[N]))
    print("  D_4000(E_2^r):  " + ", ".join(out))


def main() -> int:
    M = 4700
    p = partitions(M)
    section_partition_bounds(p)
    section_windows(p)
    digits = section_pb_digits(p)
    section_pb_measure(digits, p)
    section_recurrence_empty(p)
    section_solved_tail(p, digits)
    section_approximants(p, digits)
    section_derivatives()
    section_counterexample()
    X = 16384
    P = eta_powers(X)
    section_eta(P, X)
    section_hecke(P, 6000)
    section_products(P, 6000)
    section_dense(P)
    section_eta_disc(P, X)
    print()
    print("All %d checks passed in %.1f s." % (CHECKS, time.time() - T0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
