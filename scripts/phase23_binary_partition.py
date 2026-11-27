#!/usr/bin/env python3
"""Phase 23, Tracks D3 and B3: Mahler's binary partition constant and net
carry-cancellation complexity.

Finite verification for notes/phase23/binary-partition-and-carry-complexity.md.
Standard library only.  Every identity, divisibility, order, window and
inequality certificate uses exact int / Fraction arithmetic, with two stated
exceptions: the Corollary 2.2 comparisons and the power form 2 N^{log_m 2} of
the support bound in Theorem 3.4 involve the irrational quantities log_m n,
and are compared in floating point with tolerance 1e-9 (the integer form
S_m(N) <= 2^K - 1 behind the latter is checked exactly).  Floating point is
otherwise used only to print finite measurements.  Every discrepancy,
frequency, density and ratio printed in the "finite measurement" tables is a
finite measurement and is not evidence for any asymptotic claim.

Numbering follows the note: Lemma 5.3 (quantitative Phase 19), Theorem 5.4
(support against kernel deficit), Theorem 5.5 (three-state transducer).

Sections
  A  m-ary partition functions: recurrences, product form, parity, the
     elementary two-sided bounds (Theorem 2.1, Corollary 2.2), exact windows
     and both bounds of Proposition 2.3.
  B  Reciprocals: the Thue-Morse identity 1/X_b = Y_b, its truncated form, the
     m-ary sparse reciprocal Y_{b,m}, the digit code of Y_b, Thue-Morse block
     counts, the zero-orbit rate of Y_{b,m} (Theorems 3.1-3.4).
  C  Rational approximants: exact orders ord_{D_J}(b) by factorisation and
     order tests, the chain formula, m-ary chains, tracking lengths and the
     tracking ratio of Consequence 4.4, the Cartier closure behind
     Proposition 4.5 (beta mod 2^L is 2-automatic) (Section 4).
  D  The radix-power tower: Z[1/b]-module tests, coset transport r -> 2r,
     X_{b^2} = (1 - 1/b) X_b at the level of certified digits (Section 1).
  E  Carry complexity: radix-equivalence telescoping, the gauge identity, the
     kernel of b - S and the growth bound of Theorem 5.2, the zero-transition
     table, the three-window lemma, the minimal-support DP against brute
     force, Lemma 5.3 and Theorems 5.4-5.5 on exact rationals,
     w^+-(R_k) = k, the signed-width families inside K_b (Section 5).
  F  Finite measurements (base 2, N = 4000) for X_2, Y_2, X_{2,3}, Y_{2,3},
     Lambda_2, E_2^2, E_2^4, E_2^6, E_2^8, D(Theta_3^2), D(E_2^2) (Section 6).
"""

import itertools
import math
import random
import sys
import time
from fractions import Fraction
from math import gcd, isqrt

CHECKS = 0
T0 = time.time()


def check(cond, msg="check failed"):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise AssertionError(msg)


def section(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Generic utilities
# ---------------------------------------------------------------------------

def popcount(n):
    return bin(n).count("1")


def tm(n):
    """Thue-Morse t_n = s_2(n) mod 2."""
    return popcount(n) & 1


def mary_partitions(m, nmax):
    """b_m(n) for 0 <= n <= nmax via (1 - z) F(z) = F(z^m)."""
    a = [0] * (nmax + 1)
    a[0] = 1
    for n in range(1, nmax + 1):
        a[n] = a[n - 1] + (a[n // m] if n % m == 0 else 0)
    return a


def digits_base(v, b, length):
    """Base-b digits of 0 <= v < b**length, most significant first."""
    if b == 2:
        s = format(v, "b")
        check(len(s) <= length, "digit overflow")
        return [int(ch) for ch in s.zfill(length)]
    if length <= 48:
        out = [0] * length
        for i in range(length - 1, -1, -1):
            v, out[i] = divmod(v, b)
        check(v == 0, "digit overflow")
        return out
    h = length // 2
    hi, lo = divmod(v, b ** (length - h))
    return digits_base(hi, b, h) + digits_base(lo, b, length - h)


def certified_floor(coeff, b, M, H, J0=2000, nonneg=False):
    """floor(b^M x) for x = sum_n coeff[n] b^{-n}.

    With M2 = M + H and S = sum_{n <= M2} coeff[n] b^{M2-n}, b^{M2} x = S + tail
    and |tail| <= TB = floor(max_{1<=j<=J0} |coeff[M2+j]| / (b - 1)) + 2.  One
    unit of the "+2" absorbs the floor; the other covers the terms j > J0:
    every coefficient sequence used here satisfies |a(n)| <= 2^{n/8} for
    n >= 2000, and J0 >= M2/7 + 20 makes sum_{j>J0} 2^{(M2+j)/8} b^{-j} < 1.
    The majorant is checked exactly on finite grids (n <= 17000 for beta,
    n <= 20000 for b_3, b_4, b_5, 2000 <= n <= 9000 for the series of
    Section F); beyond those grids it rests on analytic growth bounds
    (Theorem 2.1 for b_m, polynomial growth for the eta/theta series,
    boundedness for Y_b, Y_{2,3}, Lambda_2).  If nonneg, the tail is >= 0.
    H is doubled until the tail cannot move the quotient.
    """
    while True:
        M2 = M + H
        check(len(coeff) > M2 + J0, "not enough coefficients")
        check(J0 >= M2 / 7 + 20, "J0 too small for the 2^{n/8} majorant")
        S = 0
        for n in range(M2 + 1):
            S = S * b + coeff[n]
        TB = max(abs(coeff[M2 + j]) for j in range(1, J0 + 1)) // (b - 1) + 2
        q, r = divmod(S, b ** H)
        if (nonneg or r - TB >= 0) and r + TB < b ** H:
            return q
        H *= 2


def frac_digits_of(P, b, M):
    """Integer part and the M fractional digits of P / b^M."""
    ip, fr = divmod(P, b ** M)
    return ip, digits_base(fr, b, M)


# ---------------------------------------------------------------------------
# Primality and factorisation (deterministic Miller-Rabin below 3.3e24)
# ---------------------------------------------------------------------------

MR_LIMIT = 3317044064679887385961981
SMALL_PRIMES = [p for p in range(2, 10000) if all(p % q for q in range(2, isqrt(p) + 1))]


def is_prime(n):
    if n < 2:
        return False
    for p in SMALL_PRIMES[:13]:
        if n % p == 0:
            return n == p
    check(n < MR_LIMIT, "Miller-Rabin outside deterministic range")
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in SMALL_PRIMES[:13]:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_brent(n):
    if n % 2 == 0:
        return 2
    rng = random.Random(n)
    while True:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g, r, q = 1, 1, 1
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
        if g != n:
            return g


def prime_factors(n, acc=None):
    if acc is None:
        acc = set()
    if n == 1:
        return acc
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            acc.add(p)
            while n % p == 0:
                n //= p
    if n == 1:
        return acc
    if is_prime(n):
        acc.add(n)
        return acc
    f = pollard_brent(n)
    prime_factors(f, acc)
    prime_factors(n // f, acc)
    return acc


def exact_order_check(b, D, T, primes_of_T):
    """True iff ord_D(b) == T, given the full prime set of T."""
    if pow(b, T, D) != 1 % D:
        return False
    for q in primes_of_T:
        if T % q == 0 and pow(b, T // q, D) == 1 % D:
            return False
    return True


def v2(n):
    return (n & -n).bit_length() - 1


# ===========================================================================
# A. m-ary partition functions
# ===========================================================================

section("A. m-ary partition functions: recurrences, bounds, windows")

NBETA = 17000
beta = mary_partitions(2, NBETA)

# A1. recurrence beta(2n) = beta(2n+1) = sum_{k<=n} beta(k)
s = 0
for n in range(0, 8000):
    s += beta[n]
    check(beta[2 * n] == s and beta[2 * n + 1] == s, "binary partition recurrence")
# A2. product form up to 3000: divide 1 by (1 - z^{2^j}) successively
NP = 3000
prod = [1] + [0] * NP
k = 1
while k <= NP:
    for n in range(k, NP + 1):
        prod[n] += prod[n - k]
    k *= 2
check(prod == beta[:NP + 1], "binary partition product form")
# m-ary product form and recurrence
mary = {}
for m in (3, 4, 5):
    mary[m] = mary_partitions(m, 20000)
    prod = [1] + [0] * NP
    k = 1
    while k <= NP:
        for n in range(k, NP + 1):
            prod[n] += prod[n - k]
        k *= m
    check(prod == mary[m][:NP + 1], "m-ary product form")
    s = 0
    for n in range(0, 3000):
        s += mary[m][n]
        for i in range(m):
            check(mary[m][m * n + i] == s, "m-ary recurrence")
# A3. parity: beta(n) even for n >= 2 (Churchhouse's first congruence)
for n in range(2, NBETA + 1):
    check(beta[n] % 2 == 0, "parity of beta")
# finite Mahler identity (Phase 22 D3.13(a); Lean blueprint mahler_finite)
for b in (2, 3, 10):
    for M in (0, 1, 2, 7, 50, 301, 1000):
        lhs = (b - 1) * sum(beta[n] * b ** (M - n) for n in range(M + 1))
        rhs = b * sum(beta[k] * b ** (M - 2 * k) for k in range(M // 2 + 1)) - beta[M]
        check(lhs == rhs, "finite Mahler identity")
print("beta recurrence (n < 8000), product form (n <= 3000), parity (2 <= n <= %d): ok" % NBETA)
print("m-ary recurrences and product forms, m = 3, 4, 5: ok")

# A4. elementary two-sided bounds (Theorem 2.1)
print()
print("Theorem 2.1: L_k <= b_m(m^k) <= U_k with U_k = prod_{i<k}(m^i+1),")
print("L_k = prod_{i=1}^{k-1}(floor(m^{k-i}/k)+1)")


def U_bound(m, k):
    out = 1
    for i in range(k):
        out *= m ** i + 1
    return out


def L_bound(m, k):
    out = 1
    for i in range(1, k):
        out *= m ** (k - i) // k + 1
    return out


bound_rows = []
for m, kmax, arr in ((2, 14, beta), (3, 9, mary[3]), (4, 7, mary[4]), (5, 6, mary[5])):
    for kk in range(1, kmax + 1):
        val = arr[m ** kk]
        check(L_bound(m, kk) <= val <= U_bound(m, kk), "Theorem 2.1 bounds")
        if kk >= 2:
            check(m ** (kk * (kk - 1) // 2) <= val * kk ** (kk - 1), "lower bound, power form")
    # every n in [m, len): L_{floor log} <= b_m(n) <= U_{floor log + 1}
    n = m
    kk = 1
    while n < len(arr) and m ** (kk + 1) <= len(arr) * m:
        lo, hi = m ** kk, min(m ** (kk + 1), len(arr))
        Lk, Uk1 = L_bound(m, kk), U_bound(m, kk + 1)
        for t in range(lo, hi):
            check(Lk <= arr[t] <= Uk1, "Theorem 2.1, all n")
        kk += 1
        n = m ** kk
    for kk in (kmax - 1, kmax):
        val = arr[m ** kk]
        bound_rows.append((m, kk, math.log(L_bound(m, kk), m), math.log(val, m),
                           kk * (kk - 1) / 2, math.log(U_bound(m, kk), m)))
prodC = {}
for m in (2, 3, 4, 5):
    p = Fraction(1)
    for i in range(0, 60):
        p *= 1 + Fraction(1, m ** i)
    prodC[m] = float(p)
check(abs(prodC[2] - 4.768462) < 1e-6, "prod (1+2^-i) constant")
# Corollary 2.2: with l = log_m n (n >= m),
#   l^2/2 - 3l/2 + 1 - l log_m l <= log_m b_m(n) <= l^2/2 + l/2 + log_m C_m
# (floating point, tolerance 1e-9: l = log_m n is irrational)
worst = {}
for m, arr in ((2, beta), (3, mary[3]), (4, mary[4]), (5, mary[5])):
    lo_gap = hi_gap = float("inf")
    for n in range(m, len(arr)):
        l = math.log(n, m)
        val = math.log(arr[n], m)
        lo = l * l / 2 - 1.5 * l + 1 - l * math.log(l, m)
        hi = l * l / 2 + l / 2 + math.log(prodC[m], m)
        check(lo - 1e-9 <= val <= hi + 1e-9, "Corollary 2.2")
        lo_gap = min(lo_gap, val - lo)
        hi_gap = min(hi_gap, hi - val)
    worst[m] = (lo_gap, hi_gap)
print("Corollary 2.2 holds for all m <= n < len (m = 2..5); min slacks: " +
      ", ".join("m=%d: %.3f/%.3f" % (m, worst[m][0], worst[m][1]) for m in worst))
# M2 (referee): the former constant log_m(C_m/2) fails the intermediate step
# log_m b_m(m^{k+1}) <= k(k+1)/2 + const at k = 1 for every m >= 3, since
# b_m(m^2) = m + 2 > m C_m / 2; the corrected constant log_m C_m holds.
# Exact: C_m lies in [P, P (1 + 4 m^{-60})] with P = prod_{i<60}(1 + m^{-i}).
for m in range(3, 11):
    arr_m = mary_partitions(m, m * m)
    check(arr_m[m * m] == m + 2, "b_m(m^2) = m + 2")
    P = Fraction(1)
    for i in range(60):
        P *= 1 + Fraction(1, m ** i)
    Cup = P * (1 + Fraction(4, m ** 60))
    check(2 * (m + 2) > m * Cup, "old constant log_m(C_m/2) fails at k = 1")
    check(m + 2 <= m * P, "corrected constant log_m C_m holds at k = 1")
print("Corollary 2.2 at k = 1: b_m(m^2) = m + 2 exceeds m C_m/2 for 3 <= m <= 10 "
      "(old constant invalid), and is <= m C_m (corrected constant): ok")
print("  m  k  log_m L_k  log_m b_m(m^k)  k(k-1)/2  log_m U_k")
for row in bound_rows:
    print("  %d %2d  %8.3f  %12.3f  %9.1f  %9.3f" % row)
print("  constants C_m = prod_{i>=0}(1+m^-i): " +
      ", ".join("m=%d: %.6f" % (m, prodC[m]) for m in (2, 3, 4, 5)))
norm = [(kk, math.log2(beta[2 ** kk]) / (kk * kk / 2)) for kk in (8, 10, 12, 14)]
print("  normalised log2 beta(2^k)/(k^2/2): " + ", ".join("k=%d: %.4f" % t for t in norm))

# majorant used in certified_floor: beta(n) <= 2^{n/8} for n >= 2000.
# Exact: with K = bit length of n - 1, beta(n) <= beta(2^K) <= U_K(2) by
# monotonicity and Theorem 2.1, and U_K(2) <= 2^{floor(n/8)} is an integer test.
for n in range(2000, NBETA + 1, 50):
    K = (n - 1).bit_length()
    check(U_bound(2, K) <= 2 ** (n // 8), "majorant 2^{n/8} (beta)")
for m in (3, 4, 5):
    for n in range(2000, len(mary[m]), 37):
        check(mary[m][n] <= 2 ** (n // 8), "majorant 2^{n/8} (b_m)")

# A5. exact windows L_tau(N) for X_b, tau = N^{-2} (Proposition 2.3)
print()
print("Proposition 2.3: exact certified windows, tau = N^-2")


def tail_scaled(arr, b, n0, L, H, J0=2000):
    """Bracket for b^{L+H} T(n0, L), T(n0,L) = sum_{j>L} arr[n0+j] b^{-j}."""
    S = 0
    for j in range(L + 1, L + H + 1):
        S = S * b + arr[n0 + j]
    TB = arr[n0 + L + H + J0] // (b - 1) + 2
    return S, S + TB


def exact_window(arr, b, N, H=260):
    L = 0
    while True:
        lo, hi = tail_scaled(arr, b, N - 1, L, H)
        bigP = b ** (L + H)
        if N * N * hi < bigP:
            return L
        check(N * N * lo >= bigP, "window ambiguity")
        L += 1


def necessary_window(arr, b, N):
    L = 0
    while not (N * N * arr[N + L] < b ** (L + 1)):
        L += 1
    return L


window_rows = []
window_star = {}
for b in (2, 3, 10):
    for N in (500, 1000, 2000, 4000):
        Lx = exact_window(beta, b, N)
        Ln = necessary_window(beta, b, N)
        check(Ln <= Lx, "window lower bound")
        lb = math.log(beta[N], b)
        lead = math.log2(N) ** 2 / (2 * math.log2(b))
        # lower bound, exact: L >= log_b beta(N) + log_b(1/tau) - 1 iff b^{L+1} >= beta(N) N^2
        check(b ** (Lx + 1) >= beta[N] * N * N, "window >= log_b beta + log_b(1/tau) - 1")
        # upper bound (corrected constant, M3): L* = least L with
        # (N+1) beta(N) / ((b-1) b^L) < tau/2, i.e. 2 N^2 (N+1) beta(N) < (b-1) b^L.
        # Then L* <= log_b beta(N) + log_b(1/tau) + log_b(N+1) + log_b(2/(b-1)) + 1,
        # L* < N (hypothesis of Phase 22 D3.13(c)), 2 b^{-N/2} <= tau/2, and
        # L_exact <= L*.
        Ls = 0
        while not (2 * N * N * (N + 1) * beta[N] < (b - 1) * b ** Ls):
            Ls += 1
        check((b - 1) * b ** (Ls - 1) <= 2 * N * N * (N + 1) * beta[N], "L* <= Omega + 1")
        check(Ls < N, "L* < N")
        check(16 * N ** 4 <= b ** N, "2 b^{-N/2} <= tau/2")
        check(Lx <= Ls, "L_exact <= L*")
        check((b - 1) * b ** (Lx - 1) <= 2 * N * N * (N + 1) * beta[N],
              "window <= log_b beta + log_b(1/tau) + log_b(N+1) + log_b(2/(b-1)) + 1")
        window_star[(b, N)] = Ls
        window_rows.append((b, N, Lx, Ln, lb, lb + 2 * math.log(N, b), lead))
# agreement with Phase 22 (b = 2): L = 44, 52, 70 at N = 500, 1000, 4000
w2 = {r[1]: r[2] for r in window_rows if r[0] == 2}
check(w2[500] == 44 and w2[1000] == 52 and w2[4000] == 70, "Phase 22 windows reproduced")
print("   b     N  L_exact  L_nec  log_b beta(N)  +log_b(1/tau)  (log2 N)^2/(2 log2 b)   L*")
for row in window_rows:
    print("  %2d  %4d  %7d  %5d  %13.2f  %13.2f  %10.2f            %3d"
          % (row + (window_star[(row[0], row[1])],)))

# ===========================================================================
# B. Reciprocals: Thue-Morse identity and the m-ary sparse reciprocal
# ===========================================================================

section("B. Reciprocals 1/X_b = Y_b and 1/X_{b,m} = Y_{b,m}")


def poly_mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, c in enumerate(q):
                if c:
                    out[i + j] += a * c
    return out


def mary_sign(m, n):
    """eps_m(n) = (-1)^{s_m(n)} if all base-m digits of n are 0/1, else 0."""
    sgn = 1
    while n:
        n, d = divmod(n, m)
        if d > 1:
            return 0
        if d == 1:
            sgn = -sgn
    return sgn


# B1. truncated identity prod_{j<=J}(1 - z^{m^j}) = sum_{n < m^{J+1}} eps_m(n) z^n
for m, Jmax in ((2, 11), (3, 6), (4, 5), (5, 4), (7, 3)):
    for J in range(0, Jmax + 1):
        p = [1]
        for j in range(J + 1):
            f = [0] * (m ** j + 1)
            f[0], f[-1] = 1, -1
            p = poly_mul(p, f)
        rhs = [mary_sign(m, n) for n in range(m ** (J + 1))]
        p = p + [0] * (len(rhs) - len(p))
        check(p == rhs, "truncated Thue-Morse identity")
        if m == 2:
            check(all(rhs[n] == (-1) ** tm(n) for n in range(len(rhs))), "eps_2 = (-1)^t")
print("prod_{j<=J}(1 - z^{m^j}) = sum_{n<m^{J+1}} eps_m(n) z^n: m=2 (J<=11), 3 (J<=6), 4, 5, 7: ok")

# B2. convolution beta * eps_2 = delta_0 and b_3 * eps_3 = delta_0 up to n = 1200
NC = 1200
eps2 = [(-1) ** tm(n) for n in range(NC + 1)]
eps3 = [mary_sign(3, n) for n in range(NC + 1)]
for arr, eps in ((beta, eps2), (mary[3], eps3)):
    nz = [i for i in range(NC + 1) if eps[i]]
    for n in range(NC + 1):
        sacc = 0
        for i in nz:
            if i > n:
                break
            sacc += eps[i] * arr[n - i]
        check(sacc == (1 if n == 0 else 0), "reciprocal convolution")
print("coefficientwise X(z) Y(z) = 1 through z^%d for m = 2, 3: ok" % NC)

# B3. exact rational check X_b^{(J)} * Y_b^{[2^{J+1}]} = 1
for b in (2, 3, 10):
    for J in range(0, 7):
        XJ = Fraction(1)
        for j in range(J + 1):
            XJ *= Fraction(b ** (2 ** j), b ** (2 ** j) - 1)
        YJ = sum(Fraction((-1) ** tm(n), b ** n) for n in range(2 ** (J + 1)))
        check(XJ * YJ == 1, "X^(J) Y^[2^{J+1}] = 1")
print("X_b^(J) * (2^(J+1)-truncation of Y_b) = 1 exactly, b = 2, 3, 10, J <= 6: ok")

# B4. Thue-Morse block counts (Lemma 3.2): C(N) = #{n<N: t_n != t_{n+1}}
NT = 70000
tseq = [tm(n) for n in range(NT + 2)]
C = 0
maxE = Fraction(0)
cnt = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
for n in range(NT):
    C += tseq[n] != tseq[n + 1]
    cnt[(tseq[n], tseq[n + 1])] += 1
    E = Fraction(C) - Fraction(2 * (n + 1), 3)
    check(abs(E) <= Fraction((n + 1).bit_length(), 3), "|C(N) - 2N/3| <= (floor log2 N + 1)/3")
    maxE = max(maxE, abs(E))
check(abs(cnt[(0, 1)] - cnt[(1, 0)]) <= 1, "01/10 alternate")
for key, target in (((0, 0), Fraction(1, 6)), ((1, 1), Fraction(1, 6)),
                    ((0, 1), Fraction(1, 3)), ((1, 0), Fraction(1, 3))):
    check(abs(Fraction(cnt[key], NT) - target) < Fraction(1, 1000), "TM 2-block frequency")
# recursion p_{2k} = 1, p_{2k+1} = 1 - p_k
for k in range(30000):
    check(tseq[2 * k] ^ tseq[2 * k + 1] == 1, "p_2k = 1")
    check(tseq[2 * k + 1] ^ tseq[2 * k + 2] == 1 - (tseq[k] ^ tseq[k + 1]), "p_2k+1 = 1 - p_k")
# cube-freeness of TM on a prefix: no factor www with |w| <= 6 among first 20000
tstr = "".join(map(str, tseq[:20000]))
for L in range(1, 7):
    for w in itertools.product("01", repeat=L):
        ww = "".join(w) * 3
        check(ww not in tstr, "TM cube-free (finite check)")
print("TM 2-block counts in [0,%d): 00:%d 01:%d 10:%d 11:%d; max|C(N)-2N/3| = %.3f"
      % (NT, cnt[(0, 0)], cnt[(0, 1)], cnt[(1, 0)], cnt[(1, 1)], float(maxE)))

# B5. base-b digits of Y_b: code (t_n, t_{n+1}) -> 1, 0, b-1, b-2 for b >= 3 and
# 1 - t_{n+1} for b = 2.  Certified digits from the series.
NDIG = 4000
Gd = 64
H_cert = 220
NCOEF = 9000
eps2_long = [(-1) ** tseq[n] if n < len(tseq) else (-1) ** tm(n) for n in range(NCOEF + 1)]


def certified_digits(coeff, b, N, G=Gd, H=None, nonneg=False):
    if H is None:
        H = max(40, int(math.ceil(160 / math.log2(b))) + 20)
    M = N + G
    P = certified_floor(coeff, b, M, H, nonneg=nonneg)
    ip, ds = frac_digits_of(P, b, M)
    # P is the exact floor of b^M x, so all M digits are exact
    check(len(ds) == M, "digit count")
    return ip, ds, P, M


Yb_digits = {}
for b in (2, 3, 4, 5, 10):
    ip, ds, _, _ = certified_digits(eps2_long, b, NDIG)
    check(ip == 0, "Y_b in (0,1)")
    for n in range(1, NDIG + 1):
        d = ds[n - 1]
        if b == 2:
            check(d == 1 - tseq[n + 1], "Y_2 digit code")
        else:
            code = {(0, 0): 1, (0, 1): 0, (1, 0): b - 1, (1, 1): b - 2}[(tseq[n], tseq[n + 1])]
            check(d == code, "Y_b digit code")
    Yb_digits[b] = ds[:NDIG]
    if b >= 3:
        # allowed pairs (0,0), (b-1,b-1) never occur
        for n in range(NDIG - 1):
            check((ds[n], ds[n + 1]) not in ((0, 0), (b - 1, b - 1)), "Y_b allowed pairs absent")
freq3 = [Yb_digits[3].count(d) / NDIG for d in range(3)]
check(all(abs(f - 1 / 3) < 0.01 for f in freq3), "Y_3 digit frequencies near 1/3 (finite)")
y2 = "".join(map(str, Yb_digits[2]))
check("000" not in y2 and "111" not in y2, "Y_2 avoids 000 and 111")
print("digit code of Y_b verified on %d certified digits, b = 2, 3, 4, 5, 10" % NDIG)
print("Y_3 digit frequencies (finite, N=%d): %.4f %.4f %.4f" % ((NDIG,) + tuple(freq3)))

# B6. X_2 = 1/(2 - 4 tau_TM), tau_TM = sum t_n 2^{-n-1}
tauTM = sum(Fraction(tseq[n], 2 ** (n + 1)) for n in range(200))
X2approx = sum(Fraction(beta[n], 2 ** n) for n in range(260))
check(abs(X2approx * (2 - 4 * tauTM) - 1) < Fraction(1, 2 ** 150), "X_2 (2 - 4 tau) = 1")
print("tau_TM = %.15f, X_2 = 1/(2-4 tau) = %.15f" % (float(tauTM), float(X2approx)))

# B7. sparse reciprocal Y_{b,m}, m >= 3: support count S_m(N) <= 2 N^{log_m 2} - 1
for m in (3, 4, 5, 7):
    cntS = 0
    for n in range(1, 60001):
        if mary_sign(m, n):
            cntS += 1
        if n in (10, 100, 1000, 10000, 60000) or n % 997 == 0:
            K = 1
            while m ** K <= n:
                K += 1
            check(cntS <= 2 ** K - 1, "support bound S_m(N) <= 2^K - 1 (exact)")
            check(cntS <= 2 * n ** (math.log(2) / math.log(m)) - 1 + 1e-9, "support bound S_m(N) (float)")


def zero_orbit_mean_exactish(coeff, b, N, G=64):
    """M_N(x; b) from certified digits: uses ||b^n x|| from G-digit windows."""
    ip, ds, P, M = certified_digits(coeff, b, N, G=G)
    total = Fraction(0)
    scale = b ** G
    win = 0
    full = ds + [0]
    for i in range(G):
        win = win * b + full[i]
    for n in range(N):
        y = Fraction(win, scale)
        total += min(y, 1 - y)
        win = (win * b) % scale + full[n + G]
    return total / N


ratel = []
for b in (2, 3):
    for m in (3, 4):
        coeff = [mary_sign(m, n) for n in range(14001)]
        for N in (1000, 4000):
            MN = zero_orbit_mean_exactish(coeff, b, N)
            Sm = sum(1 for n in range(1, N + 1) if mary_sign(m, n))
            bound = Fraction(Sm + 1, N)
            check(MN <= bound + Fraction(2, b ** 60), "M_N(Y_{b,m}) <= (S_m(N)+1)/N")
            ratel.append((b, m, N, float(MN), float(bound), 2 * N ** (math.log(2) / math.log(m) - 1)))
print("Theorem 3.4: M_N(Y_{b,m}; b) <= (S_m(N)+1)/N <= 2 N^{log_m 2 - 1}")
print("   b  m     N   M_N (finite)   (S+1)/N    2N^{log_m 2 - 1}")
for row in ratel:
    print("  %2d  %d  %4d   %.6f      %.6f   %.6f" % row)

# ===========================================================================
# C. Rational approximants: exact orders
# ===========================================================================

section("C. Exact multiplicative orders of b modulo D_J")


def chain_D(b, m, J):
    out = 1
    for j in range(J + 1):
        out *= b ** (m ** j) - 1
    return out


def primes_of_chain_D(b, m, J):
    acc = set()
    for j in range(J + 1):
        if m == 2:
            prime_factors(b - 1, acc)
            for i in range(j):
                prime_factors(b ** (2 ** i) + 1, acc)
        else:
            prime_factors(b ** (m ** j) - 1, acc)
    return acc


order_rows = []
for b in (2, 3, 5, 7, 10):
    for J in range(0, 7):
        D = chain_D(b, 2, J)
        if J == 0:
            T = 1
            check(D == b - 1 and pow(b, 1, D) == 1 % D, "J = 0")
        else:
            T = 2 ** J * chain_D(b, 2, J - 1)
            primesT = {2} | primes_of_chain_D(b, 2, J - 1)
            check(exact_order_check(b, D, T, primesT), "T_J = 2^J D_{J-1}")
        trackJ = 2 ** (J + 1)
        order_rows.append((b, J, T, trackJ))
print("ord_{D_J}(b) = 2^J D_{J-1} (J >= 1) verified by exact order tests, b in {2,3,5,7,10}, J <= 6")
print("   b  J  log10 T_J   T_J (if small)      2^{J+1}/T_J")
for b, J, T, tr in order_rows:
    if b in (2, 10) or J <= 3:
        small = str(T) if T < 10 ** 14 else "-"
        print("  %2d  %d  %9.3f   %-16s  %.3e" % (b, J, math.log10(T), small, tr / T))
# power-of-two classification: for J >= 1, T_J = 2^J D_{J-1} is a power of 2
# iff (J = 1 and b - 1 is a power of 2) or (J = 2 and b = 3)
for b in range(2, 41):
    for J in range(1, 6):
        T = 2 ** J * chain_D(b, 2, J - 1)
        pw = T & (T - 1) == 0
        pred = (J == 1 and (b - 1) & (b - 2) == 0) or (J == 2 and b == 3)
        check(pw == pred, "power-of-two classification of T_J")
# explicit small values for b = 2
T2 = {J: T for (b, J, T, tr) in order_rows if b == 2}
check(T2[0] == 1 and T2[1] == 2 and T2[2] == 12 and T2[3] == 4 * 3 * 15 * 2, "small T_J, b = 2")

# m-ary chains
mrows = []
for b in (2, 3, 5, 7, 10):
    for m in (3, 4, 5):
        for J in range(1, 4):
            if m == 5 and J == 3 and b >= 7:
                continue
            D = chain_D(b, m, J)
            base_T = m ** J * chain_D(b, m, J - 1)
            if b % 2 == 0 or b % 4 == 1 or m % 2 == 0:
                T = base_T
                kind = "m^J D"
            else:
                e = min(J - 1, v2(b + 1) - 1)
                check(base_T % (2 ** e) == 0, "divisibility in (c')")
                T = base_T // 2 ** e
                kind = "m^J D/2^%d" % e
            primesT = prime_factors(m) | primes_of_chain_D(b, m, J - 1) | {2}
            check(exact_order_check(b, D, T, primesT), "m-ary chain order")
            mrows.append((b, m, J, kind, math.log10(T), m ** (J + 1) / T))
print("m-ary chains {1, m, ..., m^J}: orders verified in %d cases" % len(mrows))
for row in mrows:
    if row[2] == 2 and row[1] in (3, 4):
        print("  b=%2d m=%d J=%d  %-11s log10 T = %8.3f   m^{J+1}/T = %.3e" % row)

# tracking lengths A_J for X_b vs X_b^{(J)}
print()
print("Tracking: A_J = number of leading fractional digits shared by X_b and X_b^(J)")
track_rows = []
for b in (2, 3, 10):
    ipX, dsX, _, _ = certified_digits(beta, b, 300, G=40, nonneg=True)
    for J in range(0, 7):
        D = chain_D(b, 2, J)
        num = b ** (2 ** (J + 1) - 1)
        ipJ, r = divmod(num, D)
        A = 0
        if ipJ == ipX:
            for n in range(300):
                r *= b
                d, r = divmod(r, D)
                if d != dsX[n]:
                    break
                A += 1
        mJ1 = 2 ** (J + 1)
        if b ** mJ1 >= 64:
            check(ipJ == ipX and A < mJ1, "A_J < 2^{J+1} (Lemma D3.10)")
        T = 1 if J == 0 else 2 ** J * chain_D(b, 2, J - 1)
        track_rows.append((b, J, A, mJ1, T))
print("   b  J   A_J  2^{J+1}   A_J/T_J")
for b, J, A, mJ1, T in track_rows:
    print("  %2d  %d  %4d  %6d   %.3e" % (b, J, A, mJ1, A / T))
# Lemma 4.2 for J >= 1: A_J / T_J < 2 / D_{J-1}
for b, J, A, mJ1, T in track_rows:
    if J >= 1 and b ** mJ1 >= 64:
        check(Fraction(A, T) < Fraction(2, chain_D(b, 2, J - 1)), "Lemma 4.2: A_J/T_J < 2/D_{J-1}")


# Consequence 4.4 (M4): A_{J,m}/T_{J,m} < 2^e m / D_{J-1,m}, where e = 0 in the
# first case of Theorem 4.3 and e = min(J-1, v_2(b+1)-1) otherwise; in all cases
# e <= max(0, min(J-1, v_2(b+1)-1)).  The former exponent min(J-1, v_2(b+1)-1)
# equals -1 for even b and fails at b = 2, m = 2, J = 2 (A = 6, T = 12, D_1 = 3).
def theorem43_exponent(b, m, J):
    if b % 2 == 0 or b % 4 == 1 or m % 2 == 0:
        return 0
    return min(J - 1, v2(b + 1) - 1)


def tracking_length(coeff_digits, ip, num, D, nd, b):
    ipJ, r = divmod(num, D)
    A = 0
    if ipJ == ip:
        for n in range(nd):
            r *= b
            d, r = divmod(r, D)
            if d != coeff_digits[n]:
                break
            A += 1
    return ipJ, A


rowJ2 = [t for t in track_rows if t[0] == 2 and t[1] == 2][0]
check(rowJ2[2] == 6 and rowJ2[4] == 12 and chain_D(2, 2, 1) == 3, "b=2, J=2: A=6, T=12, D_1=3")
check(Fraction(6, 12) > Fraction(1, 2) * Fraction(2, 3), "former exponent -1 fails at b=2, m=2, J=2")
check(Fraction(6, 12) < Fraction(2 ** max(0, min(1, v2(3) - 1)) * 2, 3), "corrected bound at b=2, m=2, J=2")
mtrack = []
for m in (3, 4):
    for b in (2, 3, 5, 7):
        ipX, dsX, _, _ = certified_digits(mary[m], b, 300, G=40, nonneg=True)
        for J in (1, 2, 3):
            mJ1 = m ** (J + 1)
            if b ** mJ1 < 64 or mJ1 > 280:
                continue
            D = chain_D(b, m, J)
            num = b ** sum(m ** j for j in range(J + 1))
            ipJ, A = tracking_length(dsX, ipX, num, D, 300, b)
            check(ipJ == ipX and A < mJ1, "A_{J,m} < m^{J+1} (Lemma D3.10)")
            e = theorem43_exponent(b, m, J)
            T = m ** J * chain_D(b, m, J - 1) // 2 ** e
            check(exact_order_check(b, D, T, prime_factors(m) | primes_of_chain_D(b, m, J - 1) | {2}),
                  "T_{J,m} from Theorem 4.3")
            emax = max(0, min(J - 1, v2(b + 1) - 1))
            check(e <= emax, "e <= max(0, min(J-1, v_2(b+1)-1))")
            bound = Fraction(2 ** e * m, chain_D(b, m, J - 1))
            check(Fraction(A, T) < bound, "Consequence 4.4 tracking ratio")
            check(Fraction(A, T) < Fraction(2 ** emax * m, chain_D(b, m, J - 1)), "Consequence 4.4 (max form)")
            mtrack.append((b, m, J, A, mJ1, e, float(Fraction(A, T)), float(bound)))
print("Consequence 4.4: m-ary tracking A_{J,m}/T_{J,m} < 2^e m/D_{J-1,m} in %d cases;"
      " b=2, m=2, J=2: A/T = 1/2 > 1/3 (former exponent -1) and < 2/3 (corrected)" % len(mtrack))
print("   b  m  J  A_{J,m}  m^{J+1}  e   A/T         2^e m/D_{J-1,m}")
for row in mtrack:
    print("  %2d  %d  %d  %6d  %7d  %d   %.3e   %.3e" % row)


# Proposition 4.5: beta mod 2^L is 2-automatic.  With F_k = (1-z)^{-k} F and
# (1+z)^s = U_s(z^2) + z V_s(z^2), U_s(1-w) = sum_j u_{s,j} w^j,
# V_s(1-w) = sum_j v_{s,j} w^j, the exact identities
#   Phi_0 F_k = sum_j u_{k+1,j} F_{k+1-j},  Phi_1 F_k = sum_j v_{k+1,j} F_{k+1-j}
# hold in Z[[y]], and u_{s,0} = v_{s,0} = 2^{s-1}.  So span(F_0..F_L) mod 2^L is
# closed under the Cartier operators Phi_0, Phi_1 (Phi_i A has coefficients
# A_{2n+i}).  Checked exactly through y^NCART.
def poly_in_w(coeffs_y):
    """Coefficients in w of P(1 - w), given coefficients of P(y)."""
    out = [0] * len(coeffs_y)
    for e, c in enumerate(coeffs_y):
        for j in range(e + 1):
            out[j] += c * math.comb(e, j) * (-1) ** j
    return out


NCART = 3000
KCART = 7
Fk = [beta[:2 * NCART + 2]]
for k in range(1, KCART + 2):
    prev, acc, row = Fk[-1], 0, []
    for c in prev:
        acc += c
        row.append(acc)
    Fk.append(row)
for k in range(0, KCART + 1):
    s_ = k + 1
    U = [math.comb(s_, 2 * e) for e in range(s_ // 2 + 1)]
    V = [math.comb(s_, 2 * e + 1) for e in range((s_ - 1) // 2 + 1)]
    uw, vw = poly_in_w(U), poly_in_w(V)
    check(uw[0] == 2 ** k and vw[0] == 2 ** k, "u_{s,0} = v_{s,0} = 2^{s-1}")
    for i, cw in ((0, uw), (1, vw)):
        for n in range(NCART):
            rhs = sum(c * Fk[s_ - j][n] for j, c in enumerate(cw))
            check(Fk[k][2 * n + i] == rhs, "Cartier identity Phi_i F_k")
print("Proposition 4.5: Phi_i F_k = sum_j c_j F_{k+1-j} exactly through y^%d for k <= %d, "
      "leading coefficient 2^k: ok" % (NCART, KCART))


def kernel_count(q, depth, plen):
    seen = set()
    for e in range(depth + 1):
        for r in range(2 ** e):
            seen.add(tuple(beta[2 ** e * n + r] % q for n in range(plen)))
    return len(seen)


kc = {q: kernel_count(q, 6, 200) for q in (2, 4, 8, 16, 3)}
for L in (1, 2, 3, 4):
    check(kc[2 ** L] <= 2 ** (L * (L + 1)), "prefix 2-kernel count <= 2^{L(L+1)}")
print("finite measurement: distinct 2-kernel prefixes (depth <= 6, length 200) of beta mod q: " +
      ", ".join("q=%d: %d" % (q, kc[q]) for q in (2, 4, 8, 16, 3)))

# ===========================================================================
# D. The radix-power tower
# ===========================================================================

section("D. Radix-power tower: Z[1/b]-modules and coset transport")


def in_K_rational(q, B):
    """Phase 19 test: q in K_B iff the B-coprime part of its denominator divides B-1."""
    d = Fraction(q).denominator
    g = gcd(d, B)
    while g > 1:
        while d % g == 0:
            d //= g
        g = gcd(d, B)
    return (B - 1) % d == 0


rng = random.Random(20261127)
for b in range(2, 11):
    for k in (1, 2, 3):
        Bk = b ** k
        for _ in range(60):
            a = rng.randrange(-500, 500)
            q = Fraction(a, Bk - 1) / b ** rng.randrange(0, 4)
            check(in_K_rational(q, Bk), "rationals of F_{b^k} Z[1/b] lie in K_{b^k}")
            u = Fraction(rng.randrange(-50, 50), b ** rng.randrange(0, 5))
            check(in_K_rational(u * q, Bk), "Z[1/b] acts on rational part of K_{b^k}")
    if b >= 3:
        check(not in_K_rational(Fraction(1, (b - 1) ** 2), b), "division by b-1 leaves K_b")
# coset transport: class of r/(b(b+1)) in K_{b^2}/K_b equals 2r mod (b+1)
for b in range(2, 25):
    R = b + 1
    for r in range(0, b * b - 1):
        sval = (r * (1 - b)) % (b * b - 1)
        diff = Fraction(r, b * (b + 1)) - Fraction(sval, b * b - 1)
        # diff must lie in Z[1/b]
        dd = diff.denominator
        g = gcd(dd, b)
        while g > 1:
            while dd % g == 0:
                dd //= g
            g = gcd(dd, b)
        check(dd == 1, "r/(b(b+1)) - s/(b^2-1) in Z[1/b]")
        check(sval % R == (2 * r) % R, "class map r -> 2r")
        # direct: X_{b^2}-type multiplier (b-1)/b preserves membership
        q = Fraction(r, b * b - 1)
        check(in_K_rational(q * Fraction(b - 1, b), b * b), "(b-1)/b maps K_{b^2} rationals to K_{b^2}")
        check(in_K_rational(Fraction(sval, b * b - 1), b) == (sval % R == 0), "Theorem 8.1 class test")
print("Z[1/b]-module tests (b <= 10, k <= 3) and coset transport r -> 2r (b <= 24): ok")

# X_{b^2} = (1 - 1/b) X_b at the level of certified digits
for b in (2, 3, 10):
    Mtest = 600
    coeff_b2 = [0] * (2 * (Mtest + 2300) + 2)
    for n in range(len(coeff_b2) // 2):
        coeff_b2[2 * n] = beta[n]
    # x' = X_{b^2} written in base b: sum beta(n) b^{-2n}
    Pb2 = certified_floor(coeff_b2, b, Mtest, 80, nonneg=True)
    PX = certified_floor(beta, b, Mtest + 1, 80, nonneg=True)  # floor(b^{M+1} X_b)
    # (b-1) b^{M-1} X_b = (b-1) b^{M+1} X_b / b^2: floor of (b-1)*PX / b^2 up to one unit
    lo = ((b - 1) * PX) // (b * b)
    hi = ((b - 1) * (PX + 1)) // (b * b)
    check(lo <= Pb2 <= hi, "X_{b^2} = (b-1)/b X_b on certified digits")
    if b == 2:
        check(Pb2 == PX // 4, "X_4 = X_2/2: binary digits shift by one place")
print("X_{b^2} = (1 - 1/b) X_b confirmed on 600 certified digits, b = 2, 3, 10")

# ===========================================================================
# E. Carry complexity
# ===========================================================================

section("E. Radix equivalence, gauge identity and minimal net support")

# E1. finite telescoping: sum_{m=1}^M (b D_m - D_{m+1}) b^{M-m} = D_1 b^M - D_{M+1}
for _ in range(400):
    b = rng.randrange(2, 13)
    M = rng.randrange(1, 40)
    Dl = [0] + [rng.randrange(-10 ** 6, 10 ** 6) for _ in range(M + 1)]
    lhs = sum((b * Dl[m] - Dl[m + 1]) * b ** (M - m) for m in range(1, M + 1))
    check(lhs == Dl[1] * b ** M - Dl[M + 1], "radix telescoping")


def rational_digits(x, b, n):
    """Integer part and first n base-b digits of rational x (finite convention)."""
    x = Fraction(x)
    ip = x.numerator // x.denominator
    fr = x - ip
    out = []
    for _ in range(n):
        fr *= b
        d = fr.numerator // fr.denominator
        out.append(d)
        fr -= d
    return ip, out


# E2. gauge identity: a~(m) = d_m + b delta_m - delta_{m+1}
nker = 0
for _ in range(300):
    b = rng.randrange(2, 11)
    Lsup = rng.randrange(1, 25)
    Bc = rng.choice([b // 2, b - 1, 60])
    at = [0] + [rng.randrange(-Bc, Bc + 1) for _ in range(Lsup)]
    x = sum(Fraction(at[m], b ** m) for m in range(1, Lsup + 1))
    ip, ds = rational_digits(x, b, Lsup + 40)
    ds = [None] + ds
    atl = at + [0] * 60
    deltas = {}
    for m in range(1, Lsup + 30):
        dm = sum(Fraction(atl[m + j] - ds[m + j], b ** (j + 1)) for j in range(0, Lsup + 38 - m))
        check(dm.denominator == 1, "delta_m integral")
        deltas[m] = int(dm)
    for m in range(1, Lsup + 29):
        check(atl[m] == ds[m] + b * deltas[m] - deltas[m + 1], "gauge identity")
    if 1 <= Bc <= b - 1:
        check(all(d in (-1, 0, 1) for d in deltas.values()), "delta in {-1,0,1} when |a| <= b-1")
    check(deltas[1] == x - Fraction(sum(Fraction(ds[m], b ** m) for m in range(1, Lsup + 40))),
          "delta_1 = F(a~) - F(d)")
    # Theorem 5.2 (C1): growth bound of the canonical carry,
    # |delta_m| b^{-m} <= b^{-1} sum_{k>=m} |a~(k) - d_k| b^{-k}  (x is b-adic, so
    # d_k = 0 and a~(k) = 0 for k > Lsup and the sums are finite and exact)
    for m in range(1, Lsup + 29):
        tail = sum(Fraction(abs(atl[k] - ds[k]), b ** k) for k in range(m, Lsup + 40))
        check(Fraction(abs(deltas[m]), b ** m) <= tail / b, "canonical carry growth bound")
    check(all(deltas[m] == 0 for m in range(Lsup + 1, Lsup + 29)), "canonical carry vanishes past support")
    # Theorem 5.2 (C1): ker(b - S) = {(c b^{m-1})_m}; delta + c b^{m-1} solves the
    # same equation but violates delta_m = o(b^m) (delta~_m b^{-m} -> c/b != 0)
    cker = rng.choice([-3, -2, -1, 1, 2, 3])
    dt = {m: deltas[m] + cker * b ** (m - 1) for m in deltas}
    for m in range(1, Lsup + 29):
        check(atl[m] == ds[m] + b * dt[m] - dt[m + 1], "kernel shift solves the gauge equation")
    check(all(dt[m] != deltas[m] for m in dt), "kernel shift is a different integer sequence")
    mfar = Lsup + 28
    check(Fraction(dt[mfar], b ** mfar) == Fraction(cker, b), "kernel shift: delta~_m b^{-m} = c/b, not o(1)")
    nker += 1

# E3. zero-transition table
for b in range(2, 17):
    zs = set()
    for dl in (-1, 0, 1):
        for dl2 in (-1, 0, 1):
            for d in range(b):
                if d + b * dl - dl2 == 0:
                    zs.add((dl, dl2, d))
    check(zs == {(0, 0, 0), (0, 1, 1), (-1, -1, b - 1)}, "zero transitions")
# E4. three-window lemma
for b in range(2, 8):
    allowed = {(0, 0), (b - 1, b - 1)}
    for path in itertools.product((-1, 0, 1), repeat=4):
        for dd in itertools.product(range(b), repeat=3):
            if (dd[0], dd[1]) in allowed:
                continue
            zero = all(dd[i] + b * path[i] - path[i + 1] == 0 for i in range(3))
            check(not zero, "three-window lemma")
print("telescoping, gauge identity (300 random), zero transitions (b <= 16), three-window lemma: ok")
print("Theorem 5.2: canonical carry satisfies |delta_m| b^-m <= b^-1 sum_{k>=m} |a~(k)-d_k| b^-k; "
      "kernel shifts delta + c b^(m-1) (c != 0) solve the same equation with delta~_m b^-m = c/b "
      "(%d instances): ok" % nker)


def sigma_dp(ds, theta_end, b, B):
    """Minimal number of nonzero a~(m), m <= N, over representations with
    |a~| <= B; ds = d_1..d_N, theta_end = {b^N x} (Fraction)."""
    INF = 10 ** 9
    cost = {-1: 0, 0: 0, 1: 0}
    for d in ds:
        new = {-1: INF, 0: INF, 1: INF}
        for sdel, cst in cost.items():
            if cst >= INF:
                continue
            for t in (-1, 0, 1):
                a = d + b * sdel - t
                if -B <= a <= B:
                    v = cst + (a != 0)
                    if v < new[t]:
                        new[t] = v
        cost = new
    lim = Fraction(B, b - 1)
    best = INF
    for t in (-1, 0, 1):
        if abs(t + theta_end) <= lim:
            best = min(best, cost[t])
    return best


def sigma_brute(x, b, B, N):
    x = Fraction(x)
    p, q = x.numerator, x.denominator
    best = None
    bN = b ** N
    for pref in itertools.product(range(-B, B + 1), repeat=N):
        S = 0
        for a in pref:
            S = S * b + a
        r = (p * bN - q * S) % (q * bN)
        if min(r, q * bN - r) * (b - 1) <= B * q:
            w = sum(1 for a in pref if a)
            if best is None or w < best:
                best = w
    return best


def sigma_of_rational(x, b, B, N):
    ip, ds = rational_digits(x, b, N)
    fr = Fraction(x) - ip
    theta = (fr * b ** N) - int(fr * b ** N)
    return sigma_dp(ds, theta, b, B)


nbrute = 0
for b, B, N in ((2, 1, 7), (3, 1, 6), (3, 2, 5), (4, 2, 5), (5, 2, 5), (5, 4, 3), (6, 3, 4)):
    for _ in range(10):
        q = rng.randrange(2, 400)
        x = Fraction(rng.randrange(0, 5 * q), q)
        check(sigma_of_rational(x, b, B, N) == sigma_brute(x, b, B, N), "DP = brute force")
        nbrute += 1
print("minimal-support DP agrees with brute force on %d rational instances" % nbrute)


def orbit_points(x, b, N):
    x = Fraction(x)
    p, q = x.numerator, x.denominator
    r = p % q
    out = []
    for _ in range(N):
        out.append(r)
        r = r * b % q
    return out, q


def disc_from_sorted_ints(ys, scale):
    """Extreme discrepancy of points ys/scale: 1/N + max z - min z."""
    ys = sorted(ys)
    N = len(ys)
    zmax = zmin = None
    for i, y in enumerate(ys, 1):
        z = N * y - i * scale
        zmax = z if zmax is None or z > zmax else zmax
        zmin = z if zmin is None or z < zmin else zmin
    return Fraction(1, N) + Fraction(zmax - zmin, N * scale)


def disc_brute(points):
    """Brute-force sup over [alpha, beta) of |count/N - length| (rational points)."""
    N = len(points)
    grid = sorted(set(points) | {Fraction(0), Fraction(1)})
    best = Fraction(0)
    for i, u in enumerate(grid):
        for v in grid[i:]:
            ln = v - u
            c_cl = sum(1 for y in points if u <= y <= v)
            c_op = sum(1 for y in points if u < y < v)
            c_ho = sum(1 for y in points if u <= y < v)
            c_oh = sum(1 for y in points if u < y <= v)
            for c in (c_cl, c_op, c_ho, c_oh):
                best = max(best, abs(Fraction(c, N) - ln))
    return best


for _ in range(150):
    b = rng.randrange(2, 7)
    q = rng.randrange(2, 60)
    x = Fraction(rng.randrange(0, q), q)
    N = rng.randrange(1, 18)
    pts, qq = orbit_points(x, b, N)
    check(disc_from_sorted_ints(pts, qq) == disc_brute([Fraction(r, qq) for r in pts]),
          "discrepancy formula with ties")


def mu_N(pts, q, b):
    """min_{c in F_b} M_N(x - c) for exact orbit numerators pts over q."""
    best = None
    N = len(pts)
    for j in range(b - 1):
        tot = 0
        den = q * (b - 1)
        for r in pts:
            v = (r * (b - 1) - j * q) % den
            tot += min(v, den - v)
        val = Fraction(tot, N * den)
        best = val if best is None or val < best else best
    return best


def chi_N(ds, b, N):
    allowed = {(0, 0), (b - 1, b - 1)}
    return sum(1 for m in range(N) if (ds[m], ds[m + 1]) not in allowed)


# E5. Lemma 5.3, Theorem 5.4 and Theorem 5.5(c) on exact rationals
nQ = 0
for _ in range(500):
    b = rng.choice([2, 3, 4, 5, 10])
    q = rng.randrange(3, 3000)
    x = Fraction(rng.randrange(1, q), q)
    N = rng.randrange(3, 160)
    pts, qq = orbit_points(x, b, N)
    D = disc_from_sorted_ints(pts, qq)
    mu = mu_N(pts, qq, b)
    dlt = 1 - D
    check(Fraction(2, 5) * mu - Fraction(1, N) <= dlt, "Lemma 5.3 lower")
    check(dlt <= 0 or dlt * dlt <= 8 * mu, "Lemma 5.3 upper")
    B = b // 2
    sig = None
    chis = []
    for j in range(b - 1):
        w = x - Fraction(j, b - 1)
        sj = sigma_of_rational(w, b, B, N)
        sig = sj if sig is None else min(sig, sj)
        ipw, dsw = rational_digits(w, b, N + 1)
        chis.append((chi_N(dsw, b, N - 2), chi_N(dsw, b, N)))
        check(Fraction(chis[-1][0], 3) <= sj <= chis[-1][1] + 1, "Theorem 5.5(c) sandwich")
        # canonical count #{n<N: ||b^n w|| >= 1/(2b)}
        ptsw, qw = orbit_points(w, b, N)
        canon = sum(1 for r in ptsw if 2 * b * min(r, qw - r) >= qw)
        check(sj <= canon, "sigma <= canonical count")
        Mw = Fraction(sum(min(r, qw - r) for r in ptsw), N * qw)
        check(Fraction(b - 1, B) * N * Mw - Fraction(1, b - 1) <= sj, "Theorem 5.4 lower")
        check(canon <= 2 * b * N * Mw, "Theorem 5.4 Markov step")
    check(sig <= 2 * b * N * mu, "Theorem 5.4 upper (min over c)")
    nQ += 1
print("Lemma 5.3, Theorem 5.4 and Theorem 5.5(c) verified exactly on %d random rationals" % nQ)


# E6. minimal signed weight and w^+-(R_k) = k
def min_signed_weight(x, b, memo=None):
    if memo is None:
        memo = {}
    x = abs(x)
    if x == 0:
        return 0
    if x < b:
        return 1
    if x in memo:
        return memo[x]
    r = x % b
    if r == 0:
        res = min_signed_weight(x // b, b, memo)
    else:
        res = 1 + min(min_signed_weight((x - r) // b, b, memo),
                      min_signed_weight((x - r + b) // b, b, memo))
    memo[x] = res
    return res


for x in range(1, 1 << 14):
    check(min_signed_weight(x, 2) == popcount((3 * x) ^ x), "NAF weight formula")
for b in range(2, 8):
    for kk in range(0, 16):
        Rk = sum(b ** (2 * i) for i in range(kk))
        check(min_signed_weight(Rk, b) == kk, "w(R_k) = k")
print("NAF formula (x < 2^14) and w_b(R_k) = k (b <= 7, k <= 15): ok")


# E7. signed-width families inside K_b
def family_k(m, b, kind):
    if kind == "sqrt":
        s_ = 0
        while b ** ((s_ + 1) ** 2) <= m:
            s_ += 1
        return (b - 1) * s_
    return (b - 1) * (m // (4 * (b - 1)))


def family_delta(m, b, kind):
    kk = family_k(m, b, kind)
    Rk = sum(b ** (2 * i) for i in range(kk))
    check(Rk % (b - 1) == 0, "R_k divisible by b - 1")
    return Rk // (b - 1)


def is_pow2(m):
    return m >= 1 and m & (m - 1) == 0


def int_len(v, b):
    """Exact number of base-b digits of the integer v >= 1."""
    n = 0
    while v:
        v //= b
        n += 1
    return n


fam_rows = []
for b in (2, 3):
    for kind, Nf in (("sqrt", 3000), ("max", 360)):
        dl = [0] + [family_delta(m, b, kind) for m in range(1, Nf + 3)]
        at = [0] + [(1 if is_pow2(m) else 0) + dl[m + 1] - b * dl[m] for m in range(1, Nf + 2)]
        # finite identity
        for M in (10, 50, min(Nf, 300)):
            lhs = sum(at[m] * b ** (M - m) for m in range(1, M + 1))
            rhs = sum(b ** (M - m) for m in range(1, M + 1) if is_pow2(m)) + dl[M + 1] - dl[1] * b ** M
            check(lhs == rhs, "family telescoping")
        check(dl[1] == 0, "Delta(1) = 0")
        Wpm = 0
        Wraw = 0
        lowb = 0
        for m in range(1, Nf + 1):
            if at[m] != 0:
                w = min_signed_weight(abs(at[m]), b)
                Wpm += w
                Wraw += int_len(abs(at[m]), b)
                if dl[m + 1] == dl[m]:
                    kk = family_k(m, b, kind)
                    check(w >= kk - (1 if is_pow2(m) else 0), "non-jump weight >= k - c")
                    lowb += kk - (1 if is_pow2(m) else 0)
        check(lowb <= Wpm <= Wraw, "family width bounds")
        fam_rows.append((b, kind, Nf, Wpm / Nf, Wpm / Nf ** 2, Wraw / Nf,
                         sum(1 for m in range(1, Nf + 1) if at[m] != 0) / Nf))
print("signed-width families: F_b(a~) = Lambda_b exactly (finite telescoping checked)")
print("   b  kind     N   W+-/N    W+-/N^2   Wraw/N   support density")
for row in fam_rows:
    print("  %2d  %-4s  %4d  %7.3f  %8.5f  %7.3f   %.4f" % row)

# ===========================================================================
# F. Finite measurements
# ===========================================================================

section("F. Finite measurements, base 2, N = 4000 (not evidence)")


def gen_pent_series(nmax):
    e = [0] * (nmax + 1)
    e[0] = 1
    k = 1
    while True:
        g1 = k * (3 * k - 1) // 2
        g2 = k * (3 * k + 1) // 2
        if g1 > nmax:
            break
        e[g1] += (-1) ** k
        if g2 <= nmax:
            e[g2] += (-1) ** k
        k += 1
    return e


def sparse_mul(p, q, nmax):
    out = [0] * (nmax + 1)
    qnz = [(j, c) for j, c in enumerate(q[:nmax + 1]) if c]
    for i, a in enumerate(p[:nmax + 1]):
        if a:
            for j, c in qnz:
                if i + j > nmax:
                    break
                out[i + j] += a * c
    return out


NF = NCOEF
E1 = gen_pent_series(NF)
E3 = [0] * (NF + 1)
kk = 0
while kk * (kk + 1) // 2 <= NF:
    E3[kk * (kk + 1) // 2] += (-1) ** kk * (2 * kk + 1)
    kk += 1
check(sparse_mul(E1, sparse_mul(E1, E1, 400), 400) == E3[:401], "Jacobi E^3")
E2s = sparse_mul(E1, E1, NF)
E4s = sparse_mul(E1, E3, NF)
E6s = sparse_mul(E3, E3, NF)
E7s = sparse_mul(E6s, E1, NF)
E8s = sparse_mul(E7s, E1, NF)
th = [0] * (NF + 1)
th[0] = 1
kk = 1
while kk * kk <= NF:
    th[kk * kk] = 2
    kk += 1
r2 = sparse_mul(th, th, NF)
DTh = [n * r2[n] for n in range(NF + 1)]
DE2 = [n * E2s[n] for n in range(NF + 1)]
lam = [1 if (n >= 1 and is_pow2(n)) else 0 for n in range(NF + 1)]
tern = mary[3]
Y23 = [mary_sign(3, n) for n in range(14001)]
# majorant check for the j > J0 tail clause of certified_floor:
# |a(n)| <= 2^{n/8} for 2000 <= n <= NF (finite grid; beyond NF the majorant
# rests on the analytic growth bounds named in the certified_floor docstring)
for arr in (E2s, E4s, E6s, E8s, DTh, DE2, tern, beta):
    for n in range(2000, min(NF, len(arr) - 1) + 1, 37):
        check(abs(arr[n]) <= 2 ** (n // 8), "coefficient majorant 2^{n/8}")

consts = [
    ("X_2", beta, True), ("Y_2", eps2_long, False), ("X_{2,3}", tern, True), ("Y_{2,3}", Y23, False),
    ("Lambda_2", lam, True), ("E_2^2", E2s, False), ("E_2^4", E4s, False), ("E_2^6", E6s, False), ("E_2^8", E8s, False),
    ("D(Theta_3^2)", DTh, True), ("D(E_2^2)", DE2, False),
]
meas = []
Lw = 64
for name, coeff, nn in consts:
    ip, ds, P, M = certified_digits(coeff, 2, NDIG, nonneg=nn)
    full = ds
    win = 0
    for i in range(Lw):
        win = win * 2 + full[i]
    pts = []
    for n in range(NDIG):
        pts.append(win)
        win = (win * 2) % (1 << Lw) + full[n + Lw]
    row = [name]
    for Nm in (1000, 2000, 4000):
        row.append(float(disc_from_sorted_ints(pts[:Nm], 1 << Lw)))
    mu = Fraction(sum(min(y, (1 << Lw) - y) for y in pts), NDIG << Lw)
    chi = chi_N(full, 2, NDIG)
    theta = Fraction(int("".join(map(str, full[NDIG:NDIG + 60])), 2), 1 << 60)
    # the true {2^N x} lies in (theta, theta + 2^-60) (x irrational); the DP
    # must give the same value at both ends of that open bracket
    eta = Fraction(1, 2 ** 62)
    sig = sigma_dp(full[:NDIG], theta + eta, 2, 1)
    check(sig == sigma_dp(full[:NDIG], theta + Fraction(1, 2 ** 60) - eta, 2, 1), "theta bracket")
    ones = sum(full[:NDIG]) / NDIG
    D4 = row[3]
    check(Fraction(2, 5) * mu - Fraction(1, NDIG) <= 1 - Fraction(D4) + Fraction(1, 10 ** 9),
          "Lemma 5.3 on measured constants (lower)")
    check(Fraction(chi_N(full, 2, NDIG - 2), 3) <= sig <= chi + 1, "Theorem 5.5(c) on constants")
    row += [float(mu), chi / NDIG, sig / NDIG, ones]
    meas.append(row)
print("  constant        D_1000   D_2000   D_4000   mu_4000   chi/N    sigma/N  freq(1)")
for row in meas:
    print("  %-13s  %.4f   %.4f   %.4f   %.5f   %.4f   %.4f   %.4f" % tuple(row))
mX2 = meas[0]
check(abs(mX2[3] - 0.0220) < 5e-5 and abs(mX2[1] - 0.0301) < 5e-5, "Phase 22 X_2 discrepancies reproduced")

# digit change density of Y_2 equals TM change density on the shifted window
check(meas[1][1] >= 0.25 and meas[1][2] >= 0.25 and meas[1][3] >= 0.25, "D_N(Y_2) >= 1/4")
ch = sum(1 for n in range(NDIG - 1) if Yb_digits[2][n] != Yb_digits[2][n + 1])
check(ch == sum(1 for n in range(2, NDIG + 1) if tseq[n] != tseq[n + 1]), "Y_2 changes = TM changes")

# Y_b: lower bound mu >= 2/(3 b^2) - o(1), limsup D <= 1 - 4/(15 b^2) and
# D_N >= 2/b^2 (Theorem 3.3(c),(d)); finite checks for b = 3, 4, 5
for b in (3, 4, 5):
    ds = Yb_digits[b]
    Ls = 30
    scale = b ** Ls
    win = 0
    for i in range(Ls):
        win = win * b + ds[i]
    pts = []
    for n in range(NDIG - Ls):
        pts.append(win)
        win = (win * b) % scale + ds[n + Ls]
    best = None
    for j in range(b - 1):
        den = scale * (b - 1)
        tot = 0
        for y in pts:
            v = (y * (b - 1) - j * scale) % den
            tot += min(v, den - v)
        val = Fraction(tot, len(pts) * den)
        best = val if best is None or val < best else best
    Dm = disc_from_sorted_ints(pts, scale)
    check(best >= Fraction(2, 3 * b * b) - Fraction(1, 100), "mu_N(Y_b) lower bound (finite)")
    check(Dm <= 1 - Fraction(4, 15 * b * b), "D_N(Y_b) <= 1 - 4/(15 b^2) (finite)")
    check(Dm >= Fraction(2, b * b), "D_N(Y_b) >= 2/b^2 (no point in [0, b^-2) or [1 - b^-2, 1))")
    check(min(pts) >= scale // (b * b), "orbit avoids [0, b^-2)")
    check(max(pts) < scale - scale // (b * b), "orbit avoids [1 - b^-2, 1)")
    print("  Y_%d (base %d, N=%d): D_N = %.4f, mu_N = %.4f, 1 - 4/(15b^2) = %.4f"
          % (b, b, len(pts), float(Dm), float(best), 1 - 4 / (15 * b * b)))

elapsed = time.time() - T0
print()
print("All %d checks passed in %.1f s." % (CHECKS, elapsed))
sys.exit(0)
