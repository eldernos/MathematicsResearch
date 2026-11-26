"""Phase 16, track 5: dyadic Stoneham polynomials. Standard library only.

Run `python -B scripts/phase16_dyadic_stoneham.py` from the repository root
(about two minutes). Options:

  --max-degree D   certify the leading-mass cuts M_d for 3 <= d <= D (default 64;
                   D = 120 reproduces the full table in notes/phase16/dyadic-stoneham.md,
                   about eight minutes)
  --quick          shorter Part A searches and certificates through degree 40
  --descent-search search good pairs (e, p) for the cyclic descent, 3 <= e <= 7,
                   primes p < 10^5 with ord_p 2 <= 25 (a few minutes)

Part A treats the parameter-two quadratic X^2 - 2X and the 2-adic number
kappa(b) = -C(lambda)/lambda of notes/phase14/quadratic-denominators.md, with
lambda = (1/2) log_2(b^-2). It checks the functional equation, the 2-adic
isometry of lambda -> kappa, the integer recursion for the upper denominators,
the depth statistics of v_2(k - kappa) and lattice exclusions of small algebraic
relations.

Part B treats the leading mass M_d(t) of the symmetric dyadic cut of
notes/phase14/higher-degrees.md. It runs a branch-and-bound over the binary
digits of t through a finite linear representation, certifies nonvanishing
modulo 2^(L_d) with the minimal precision L_d for every listed degree, checks the
cyclic-descent congruence modulo odd primes and certifies the residue tables
behind the infinite families e * p^r.

Proofs, scope and open boundaries are in notes/phase16/dyadic-stoneham.md.
"""

import argparse
import random
import sys
import time
from fractions import Fraction
from functools import cache, lru_cache
from math import comb, expm1, factorial, log2

sys.setrecursionlimit(100000)


def order(x):
    """2-adic order of a nonzero integer."""
    if x == 0:
        raise ArithmeticError("zero has infinite order")
    return (x & -x).bit_length() - 1


def v2_factorial(n):
    return n - bin(n).count("1")


# =====================================================================================
# Part A. The 2-adic intercept C(lambda) and the ratio kappa = -C/lambda
# =====================================================================================

def s_of(b):
    """s = v_2(b^2 - 1) - 1 >= 2 for odd b >= 3."""
    return order(b*b - 1) - 1


def kappa_by_recurrence(b, K):
    """(lambda, C, kappa) modulo 2^K for X^2 - 2X, from the finite recurrence
    delta_{j+1} = delta_j + 2^(j-1) delta_j^2 with delta_1 = (b^-2 - 1)/2."""
    s = s_of(b)
    P = K + s + 16
    mod = 1 << P
    d = ((1 - b*b) // 2) * pow(b*b, -1, mod) % mod
    deltas = []
    for j in range(1, P + 2):
        deltas.append(d)
        d = (d + (1 << (j-1)) * d * d) % mod
    lam = d                       # v_2(delta_j - lambda) = j - 1 + 2s
    C = (lam + sum(u - lam for u in deltas)) % mod
    assert order(lam) == s and order(C) == s
    kap = (-(C >> s) * pow(lam >> s, -1, 1 << K)) % (1 << K)
    return lam % (1 << K), C % (1 << K), kap


def log2adic(u, P):
    """Iwasawa 2-adic logarithm of an odd integer u modulo 2^P, log(u) = log(u^2)/2."""
    x = u*u - 1
    mod = 1 << (P + 64)
    total, n, xn = 0, 1, x
    while 3*n - n.bit_length() < P + 70:
        e = order(n)
        term = (xn >> e) * pow(n >> e, -1, mod)
        total += term if n % 2 else -term
        n += 1
        xn *= x
    total %= mod
    assert total % 2 == 0
    return (total >> 1) % (1 << P)


def kappa_series_at(lam, K, s):
    """kappa_0(lambda) = -1 - sum_{r>=2} 2^(r-1)/((1-2^(r-1)) r!) lambda^(r-1) mod 2^K,
    for lambda with v_2(lambda) >= s >= 2 (lambda = 0 allowed)."""
    P = K + 8
    mod = 1 << P
    total, r = -1, 2
    while (r - 1) * s < P + 8:
        f = factorial(r)
        e = order(f)
        num = (1 << (r - 1 - e)) * pow(lam, r - 1, mod)
        den = (1 - (1 << (r-1))) * (f >> e)
        total -= num * pow(den, -1, mod)
        r += 1
    return total % (1 << K)


def kappa_by_series(b, K):
    s = s_of(b)
    lam = (-log2adic(b, K + 40)) % (1 << (K + 40))
    return lam % (1 << K), kappa_series_at(lam, K, s)


def kappa_coefficients(N):
    """Exact Taylor coefficients a_n of kappa_0(lambda) = sum a_n lambda^n, n <= N."""
    a = [Fraction(-1)]
    for n in range(1, N+1):
        r = n + 1
        a.append(-Fraction(2**(r-1), (1 - 2**(r-1)) * factorial(r)))
    return a


def frac_order(q):
    q = Fraction(q)
    return order(q.numerator) - order(q.denominator)


def check_kappa_values(Bs, K):
    rows = []
    for b in Bs:
        lam1, C1, k1 = kappa_by_recurrence(b, K)
        lam2, k2 = kappa_by_series(b, K)
        assert lam1 == lam2 and k1 == k2, b
        assert k1 % 4 == 3 and order((k1 + 1 - lam1) % (1 << K)) >= 2*s_of(b)
        rows.append((b, s_of(b), lam1, k1))
    # Phase 14 residues for b = 3.
    lam3, C3, k3 = kappa_by_recurrence(3, 16)
    assert (lam3, C3, k3) == (5900, 2044, 15595)
    return rows


def check_functional_equation():
    """Coefficient identity (2^r - 2) c_r = -2^r/r! and the 2-adic identity
    kappa(b^2) - kappa(b) = (b^-2 - 1 - 2 lambda)/(2 lambda) with independent runs."""
    for r in range(2, 401):
        c = Fraction(2**(r-1), (1 - 2**(r-1)) * factorial(r))
        assert (2**r - 2) * c == -Fraction(2**r, factorial(r))
    K = 100
    for b in (3, 5, 7, 9, 11, 15):
        _, _, kb = kappa_by_recurrence(b, K)
        _, _, kb2 = kappa_by_recurrence(b*b, K)
        mod = 1 << (K + 40)
        lam = kappa_by_recurrence(b, K + 40)[0]
        num = (pow(b*b, -1, mod) - 1 - 2*lam) % mod
        den = 2*lam
        e = order(den)
        assert order(num) >= e
        rhs = (num >> e) * pow(den >> e, -1, mod) % (1 << K)
        assert (kb2 - kb - rhs) % (1 << K) == 0
    # Base change: radix b^2 with (A, B) = (b^2, 2 - 4b^2) has kappa' = kappa(b) - 1.
    for b in (3, 5, 7, 11):
        B2 = b*b
        mod = 1 << 160
        lam2, C2, _ = kappa_by_recurrence(B2, 150)
        A, Bc = B2, 2 - 4*B2
        num = (-(2*A + Bc + 2*A*C2)) % mod
        den = 2*A*lam2
        e = order(den)
        kp = (num >> e) * pow(den >> e, -1, mod) % (1 << 100)
        assert (kp - kappa_by_recurrence(b, 100)[2] + 1) % (1 << 100) == 0
    # The same power series is entire over the complex numbers:
    # C(lam) = lam - sum_{m>=0} 2^m (e^(lam/2^m) - 1 - lam/2^m).
    for x in (0.37, 1.3, -2.1, 3.0):
        series = x + sum(2**(r-1) / ((1 - 2**(r-1)) * factorial(r)) * x**r for r in range(2, 60))
        def tail(y):          # e^y - 1 - y without cancellation
            if abs(y) > 1e-3:
                return expm1(y) - y
            return sum(y**r / factorial(r) for r in range(2, 9))
        dual = x - sum(2**m * tail(x / 2**m) for m in range(0, 80))
        assert abs(series - dual) < 1e-9 * max(1, abs(series))


def check_isometry():
    """kappa_0 has 2-integral coefficients, a_0 = -1, a_1 = 1, and on 4Z_2 the
    derivative is 1 + O(2^(s+2)). Hence lambda -> kappa is an isometry of 4Z_2 onto
    -1 + 4Z_2; on residues it is a bijection, checked here modulo 2^12."""
    a = kappa_coefficients(300)
    assert a[0] == -1 and a[1] == 1
    assert all(frac_order(x) >= 0 for x in a[1:])
    assert frac_order(2*a[2]) == 2
    for n in range(2, 301):
        # derivative term n a_n lambda^(n-1) with v(lambda) >= s >= 2 has order >= s + 2
        for s in (2, 3, 4, 5):
            assert frac_order(n * a[n]) + (n-1)*s >= s + 2
    m = 12
    images = set()
    for b in range(1, 1 << m, 4):           # all residues b = 1 mod 4 modulo 2^m
        lam = (-log2adic(b, m + 8)) % (1 << (m + 8)) if b != 1 else 0
        images.add(kappa_series_at(lam, m, 2))
    assert images == set(range(3, 1 << m, 4))
    rng = random.Random(16)
    for _ in range(200):
        b1, b2 = (rng.randrange(3, 1 << 40) | 1 for _ in range(2))
        if (b1 - b2) % 4:
            b2 = (b2 + 2) % (1 << 40)
        if b2 < 3 or b1 == b2:
            continue
        k1 = kappa_by_recurrence(b1, 64)[2]
        k2 = kappa_by_recurrence(b2, 64)[2]
        if order(b1 - b2) < 60:
            assert order(k1 - k2) == order(b1 - b2)
    return len(images)


def check_similarity_spheres():
    """For general (A, B) with beta = (2A+B)/(2A), kappa = kappa_0 - beta/lambda.
    On the sphere v(lambda) = s and v(beta) != 2s it scales distances by 2^max(0, 2s - v(beta))."""
    rng = random.Random(5)
    K = 80
    checked = 0
    for beta_order in (3, 5, 7):          # 2s = 4 is the critical sphere
        beta = (1 << beta_order) * 5
        s = 2
        for _ in range(60):
            u1, u2 = rng.randrange(1 << 50) | 1, rng.randrange(1 << 50) | 1
            if u1 == u2:
                continue
            l1, l2 = (u1 << s), (u2 << s)          # v(lambda) = s
            mod = 1 << (K + 20)
            def kap(l):
                k0 = kappa_series_at(l % mod, K + 10, s)
                return (k0 - (beta >> s) * pow(l >> s, -1, mod)) % (1 << K)
            d = order(l1 - l2)
            if d + max(0, 2*s - beta_order) >= K - 4:
                continue
            assert order(kap(l1) - kap(l2)) == d - max(0, 2*s - beta_order)
            checked += 1
    return checked


def check_integer_recursion(Bs, KZ):
    """Z_1 = 2 - 2b^2, Z_{k+1} = 2 + 2 b^(2^k) (Z_k - 1) are integers with
    q_k = 2^max(0, 2k - 1 - v_2(Z_k)) for X^2 - 2X, and v_2(Z_k) = k + s + v_2(k - kappa)
    whenever v_2(k - kappa) < k - 1 + s (otherwise both are >= 2k - 1 and q_k = 1)."""
    for b in Bs:
        s = s_of(b)
        kap = kappa_by_recurrence(b, 128)[2]
        mod = 1 << (2*KZ + 16)
        Z, bp = (2 - 2*b*b) % mod, b*b % mod
        for k in range(1, KZ + 1):
            vz, pred = order(Z), k + s + order(k - kap)
            assert vz == pred or (vz >= 2*k - 1 and pred >= 2*k - 1)
            Z = (2 + 2*bp*(Z - 1)) % mod
            bp = bp*bp % mod
    # Direct shifted prefixes for small shells (independent of the recursion).
    for b in (3, 5, 7):
        Zs = [None, 2 - 2*b*b]
        for k in range(1, 9):
            Zs.append(2 + 2*b**(2**k)*(Zs[-1] - 1))
        for k in range(1, 9):
            n = 3 * 2**(k-1)
            L = [Fraction(1, 2**j * b**(2**j)) for j in range(1, k+1)]
            Sk = sum(L)
            prefix = (Sk*Sk - L[-1]**2) - 2*Sk
            q = (prefix * b**n).denominator
            assert q == 2**max(0, 2*k - 1 - order(Zs[k])), (b, k)


def depth_statistics(b, N, brute=False):
    """max v_2(k - kappa) and max excess v_2(k-kappa) - log2 k over 1 <= k <= N.
    The candidates are the least positive residues r_m = kappa mod 2^m."""
    kap = kappa_by_recurrence(b, 128)[2]
    cands = {}
    for m in range(1, 120):
        r = kap % (1 << m) or (1 << m)
        if r <= N:
            cands[r] = order(r - kap)
    best_k = max(cands, key=lambda k: (cands[k], -k))
    excess_k = max(cands, key=lambda k: cands[k] - log2(k))
    if brute:
        vb = max(range(1, N+1), key=lambda k: (order(k - kap), -k))
        eb = max(range(1, N+1), key=lambda k: order(k - kap) - log2(k))
        assert (vb, order(vb - kap)) == (best_k, cands[best_k])
        assert abs((order(eb - kap) - log2(eb)) - (cands[excess_k] - log2(excess_k))) < 1e-12
    records = sorted(cands.items())
    return cands[best_k], best_k, cands[excess_k] - log2(excess_k), excess_k, records


# ---- exact LLL for small dimensions ------------------------------------------------

def lll(basis, delta=Fraction(3, 4)):
    b = [list(v) for v in basis]
    n = len(b)

    def dot(u, v):
        return sum(x*y for x, y in zip(u, v))

    def gso(b):
        bs, mu = [], [[Fraction(0)]*n for _ in range(n)]
        for i in range(n):
            v = [Fraction(x) for x in b[i]]
            for j in range(i):
                mu[i][j] = dot(b[i], bs[j]) / dot(bs[j], bs[j])
                v = [x - mu[i][j]*y for x, y in zip(v, bs[j])]
            bs.append(v)
        return bs, mu

    bs, mu = gso(b)
    k = 1
    while k < n:
        for j in range(k-1, -1, -1):
            q = round(mu[k][j])
            if q:
                b[k] = [x - q*y for x, y in zip(b[k], b[j])]
                bs, mu = gso(b)
        if dot(bs[k], bs[k]) >= (delta - mu[k][k-1]**2) * dot(bs[k-1], bs[k-1]):
            k += 1
        else:
            b[k], b[k-1] = b[k-1], b[k]
            bs, mu = gso(b)
            k = max(k-1, 1)
    bs, _ = gso(b)
    return b, bs


def algebraic_exclusion(b, D, K):
    """Rigorous lower bound for the Euclidean norm of any nonzero integer polynomial
    of degree <= D vanishing at kappa(b), from the Gram-Schmidt norms of a reduced basis
    of {a : sum a_i kappa^i = 0 mod 2^K}."""
    kap = kappa_by_recurrence(b, K)[2]
    mod = 1 << K
    basis = [[mod] + [0]*D]
    for i in range(1, D+1):
        row = [(-pow(kap, i, mod)) % mod] + [0]*D
        row[i] = 1
        basis.append(row)
    red, bs = lll(basis)
    for v in red:
        assert sum(x * pow(kap, i, mod) for i, x in enumerate(v)) % mod == 0
    sq = min(sum(x*x for x in v) for v in bs)
    return float(sq) ** 0.5 if sq < 2**1000 else 2.0**500


def part_a(quick):
    t0 = time.time()
    Bs = (3, 5, 7, 9, 11, 15)
    rows = check_kappa_values(Bs + (25, 49, 81, 121, 225), 128)
    print("A1. kappa(b) mod 2^128 agrees by recurrence and by the lambda-series:")
    for b, s, lam, kap in rows:
        if b in Bs:
            print(f"    b={b:3d} s={s} lambda=...{lam % (1 << 16):5d} (mod 2^16)  kappa = {kap:#034x}")
    check_functional_equation()
    print("A2. functional equation: 399 coefficient identities, six radix pairs (b, b^2), "
          "base change b -> b^2, archimedean dual series")
    n_img = check_isometry()
    n_sim = check_similarity_spheres()
    print(f"A3. lambda -> kappa: integral coefficients, kappa' = 1 + O(2^(s+2)), bijection on "
          f"{n_img} residues mod 2^12, isometry on random pairs; {n_sim} similarity checks for beta != 0")
    KZ = 2048 if quick else 8192
    check_integer_recursion(Bs, KZ)
    print(f"A4. integer recursion Z_k matches k + s + v_2(k - kappa) whenever v_2(k - kappa) < k - 1 + s "
          f"(else both >= 2k - 1) for k <= {KZ}; direct prefixes k <= 8")
    N = 10**6
    print(f"A5. depth of v_2(k - kappa(b)) for 1 <= k <= {N}:")
    for b in Bs:
        v, k, ex, kx, rec = depth_statistics(b, N, brute=False)
        depth_statistics(b, 10**4 if quick else 10**5, brute=True)
        print(f"    b={b:2d}: max v_2 = {v} at k = {k}; max v_2(k-kappa) - log2 k = {ex:.2f} at k = {kx}")
    K = 512
    D = 4 if quick else 6
    print(f"A6. no integer polynomial of degree <= {D} with Euclidean norm below the bound vanishes at kappa(b):")
    for b in (3, 5, 7):
        for deg in range(1, D+1):
            bound = algebraic_exclusion(b, deg, K)
            if deg in (1, 2, D):
                print(f"    b={b} degree {deg}: norm > 2^{log2(bound):.1f}")
    print(f"    Part A done in {time.time() - t0:.1f}s")


# =====================================================================================
# Part B. The leading mass M_d(t) on the shell [1, 2)
# =====================================================================================

@cache
def mass(d, t, strict=False):
    """Exact integer M_d(t) for a dyadic cut t (Phase 14 recurrence)."""
    if d == 0:
        return int(t > 0 if strict else t >= 0)
    if t <= 0:
        return 0
    if t > d or (t == d and not strict):
        return (-1) ** d
    return sum(comb(d, m) * 2 ** (d-m) * mass(d-m, 2*(t-m), strict)
               for m in range(min(d, int(t)) + 1))


class Automaton:
    """Finite linear representation of M_d on [1, 2).

    State (a, n), 1 <= a <= d, 0 <= n < a, stands for M_a(n + f) with f in [0, 1).
    Reading the next binary digit c of f gives
        M_a(n + f) = sum_{m <= n} C(a, m) 2^(a-m) M_{a-m}(2(n - m) + c + f'),
    and a target with 2(n - m) + c >= a - m is absorbed with value (-1)^(a-m).
    Every transition weight is divisible by 2^(a-n) >= 2.
    """

    def __init__(self, d):
        self.d = d
        self.states = [(a, n) for a in range(1, d+1) for n in range(a)]
        self.index = {s: i for i, s in enumerate(self.states)}
        self.gap = [a - n for a, n in self.states]
        self.T = ([], [])
        for (a, n) in self.states:
            for c in (0, 1):
                out = []
                for m in range(n+1):
                    w = comb(a, m) << (a-m)
                    a2, n2 = a-m, 2*(n-m)+c
                    if n2 >= a2:
                        out.append((-1, w if a2 % 2 == 0 else -w))
                    else:
                        out.append((self.index[(a2, n2)], w))
                self.T[c].append(out)
        self.V = [mass(a, Fraction(n)) for (a, n) in self.states]
        self.start = self.index[(d, 1)] if d >= 2 else None

    def evaluate(self, bits):
        """Exact M_d(1 + 0.bits)."""
        if self.d == 1:
            return -1
        row, absorbed = {self.start: 1}, 0
        for c in bits:
            new = {}
            for i, x in row.items():
                for j, w in self.T[c][i]:
                    if j < 0:
                        absorbed += x*w
                    else:
                        new[j] = new.get(j, 0) + x*w
            row = new
        return absorbed + sum(x * self.V[i] for i, x in row.items())


def branch_and_bound(d, L, weight_cap=True, auto=None):
    """Leaves (tau, depth, valuation) partitioning [1, 2) into dyadic intervals on each of
    which v_2(M_d) is constant; valuation L means 'residue zero modulo 2^L'."""
    A = auto or Automaton(d)
    mod = 1 << L
    V = [v % mod for v in A.V]
    leaves = []
    stack = [({A.start: 1}, 0, 0, 1, 1)]
    nodes = 0
    while stack:
        row, absorbed, depth, num, ones = stack.pop()
        nodes += 1
        val = (absorbed + sum(x * V[i] for i, x in row.items())) % mod
        vv = order(val) if val else L
        nu = min((order(x) + A.gap[i] for i, x in row.items()), default=L)
        tau = Fraction(num, 1 << depth)
        # Extensions differ from the value at tau by multiples of 2^nu. A point
        # with d one-bits is its own truncation, so its extensions share its value.
        if vv < nu or nu >= L or (weight_cap and ones == d):
            leaves.append((tau, depth, vv))
            continue
        for c in (0, 1):
            new, ab = {}, absorbed
            for i, x in row.items():
                for j, w in A.T[c][i]:
                    if j < 0:
                        ab += x*w
                    else:
                        new[j] = new.get(j, 0) + x*w
            new = {j: y % mod for j, y in new.items() if y % mod}
            stack.append((new, ab % mod, depth+1, 2*num + c, ones + c))
    leaves.sort()
    x = Fraction(1)
    for tau, depth, _ in leaves:
        assert tau == x
        x += Fraction(1, 1 << depth)
    assert x == 2
    return leaves, nodes


# Degree: (L_d = maximal loss + 1, first location of the maximal loss, minimal loss,
#          number of leaves at precision L_d). Locations are in [1, 2).
CERTIFICATES = {
    3: (7, (9, 8), 3, 5), 4: (9, (1, 1), 7, 6), 5: (16, (65, 64), 9, 11),
    6: (25, (149, 128), 12, 16), 7: (25, (169, 128), 14, 17), 8: (34, (1345, 1024), 20, 21),
    9: (36, (513, 512), 23, 19), 10: (37, (19, 16), 27, 23), 11: (46, (561, 512), 30, 29),
    12: (47, (79, 64), 35, 26), 13: (56, (257, 256), 38, 38), 14: (60, (375, 256), 42, 41),
    15: (65, (133, 128), 45, 37), 16: (68, (6785, 4096), 53, 41), 17: (78, (4097, 4096), 57, 57),
    18: (84, (521, 512), 62, 53), 19: (89, (257, 256), 66, 47), 20: (90, (1, 1), 72, 45),
    21: (101, (1025, 1024), 76, 61), 22: (112, (1149, 1024), 81, 73),
    23: (110, (129, 128), 85, 66), 24: (113, (1, 1), 92, 63), 25: (125, (2049, 2048), 96, 69),
    26: (130, (561, 512), 101, 75), 27: (135, (257, 256), 105, 71), 28: (141, (285, 256), 111, 68),
    29: (151, (5041, 4096), 115, 81), 30: (153, (529, 512), 120, 93),
    31: (165, (2097, 2048), 124, 74), 32: (164, (633, 512), 134, 75),
    33: (181, (262145, 262144), 139, 105), 34: (179, (67, 64), 145, 93),
    35: (191, (1025, 1024), 150, 111), 36: (191, (1, 1), 157, 83),
    37: (210, (262145, 262144), 162, 123), 38: (212, (4369, 4096), 168, 120),
    39: (215, (513, 512), 173, 106), 40: (218, (1, 1), 181, 102),
    41: (234, (32769, 32768), 186, 118), 42: (236, (537, 512), 192, 117),
    43: (244, (1025, 1024), 197, 127), 44: (248, (271, 256), 204, 109),
    45: (262, (16385, 16384), 209, 127), 46: (267, (619521, 524288), 215, 151),
    47: (269, (257, 256), 220, 125), 48: (275, (287, 256), 229, 135),
    49: (290, (65537, 65536), 234, 163), 50: (293, (537, 512), 240, 164),
    51: (301, (1025, 1024), 245, 164), 52: (302, (1, 1), 252, 130),
    53: (322, (65537, 65536), 257, 171), 54: (322, (2081, 2048), 263, 172),
    55: (330, (513, 512), 268, 164), 56: (332, (1121, 1024), 276, 159),
    57: (346, (32769, 32768), 281, 171), 58: (348, (537, 512), 287, 174),
    59: (357, (2115, 2048), 292, 168), 60: (361, (1081, 1024), 299, 175),
    61: (371, (8193, 8192), 304, 175), 62: (376, (2081, 2048), 310, 195),
    63: (383, (519, 512), 315, 143), 64: (396, (1095, 1024), 327, 174),
    65: (404, (131073, 131072), 333, 198), 66: (408, (4105, 4096), 340, 205),
    67: (418, (4097, 4096), 346, 202), 68: (423, (1037, 1024), 354, 165),
    69: (435, (8193, 8192), 360, 220), 70: (439, (1033, 1024), 367, 224),
    71: (448, (2049, 2048), 373, 215), 72: (453, (2141, 2048), 382, 201),
    73: (466, (16385, 16384), 388, 201), 74: (473, (8593, 8192), 395, 217),
    75: (485, (4097, 4096), 401, 222), 76: (486, (527, 512), 409, 183),
    77: (497, (8193, 8192), 415, 228), 78: (501, (517, 512), 422, 248),
    79: (517, (133633, 131072), 428, 215), 80: (515, (543, 512), 438, 220),
    81: (530, (32769, 32768), 444, 252), 82: (542, (33537, 32768), 451, 261),
    83: (545, (4097, 4096), 457, 240), 84: (547, (1, 1), 465, 212),
    85: (566, (8193, 8192), 471, 268), 86: (569, (4129, 4096), 478, 278),
    87: (581, (2049, 2048), 484, 267), 88: (578, (1, 1), 493, 244),
    89: (596, (16385, 16384), 499, 263), 90: (598, (1049, 1024), 506, 285),
    91: (609, (4097, 4096), 512, 258), 92: (615, (1053, 1024), 520, 228),
    93: (624, (8193, 8192), 526, 255), 94: (628, (517, 512), 533, 294),
    95: (638, (4177, 4096), 539, 235), 96: (651, (2127, 2048), 550, 259),
    97: (660, (65537, 65536), 556, 307), 98: (663, (1049, 1024), 563, 289),
    99: (673, (4097, 4096), 569, 298), 100: (675, (1, 1), 577, 249),
    101: (690, (8193, 8192), 583, 322), 102: (695, (1033, 1024), 590, 327),
    103: (703, (2049, 2048), 596, 304), 104: (706, (1, 1), 605, 285),
    105: (721, (16385, 16384), 611, 305), 106: (731, (1049, 1024), 618, 319),
    107: (738, (4097, 4096), 624, 325), 108: (740, (527, 512), 632, 266),
    109: (752, (8193, 8192), 638, 310), 110: (756, (517, 512), 645, 356),
    111: (766, (1025, 1024), 651, 307), 112: (770, (543, 512), 661, 309),
    113: (787, (32769, 32768), 667, 346), 114: (793, (8385, 8192), 674, 373),
    115: (800, (4097, 4096), 680, 354), 116: (802, (1, 1), 688, 291),
    117: (818, (8193, 8192), 694, 372), 118: (824, (8433, 8192), 701, 373),
    119: (832, (8483, 8192), 707, 354), 120: (836, (2157, 2048), 716, 336),
}


def certify(d, L, auto=None):
    leaves, nodes = branch_and_bound(d, L, auto=auto)
    vals = [v for _, _, v in leaves]
    assert max(vals) == L - 1, (d, max(vals), L)      # nonzero mod 2^L, sharp witness
    witness = min(t for t, _, v in leaves if v == L - 1)
    return leaves, nodes, witness, min(vals)


def heap_sum(d):
    return sum(k.bit_length() - 1 for k in range(1, d+1))


def check_automaton_and_truncation():
    rng = random.Random(1)
    for d in range(2, 11):
        A = Automaton(d)
        for _ in range(40):
            bits = [rng.randint(0, 1) for _ in range(rng.randint(0, 14))]
            t = 1 + sum(Fraction(c, 2**(i+1)) for i, c in enumerate(bits))
            assert A.evaluate(bits) == mass(d, t)
            # Truncation after the d-th one-bit leaves M_d unchanged.
            seen, cut = 1, []
            for c in bits:
                if seen == d:
                    break
                cut.append(c)
                seen += c
            tt = 1 + sum(Fraction(c, 2**(i+1)) for i, c in enumerate(cut))
            assert mass(d, t) == mass(d, tt)


def check_against_phase14(results):
    """Same minimal precision and witness as the Phase 14 multiset certificates."""
    try:
        import phase14_dyadic_power_cells as p14
    except ImportError:
        return 0
    n = 0
    for d, (bits, _, _, witness) in p14.CERTIFICATES.items():
        if d in results:
            assert results[d][0] == bits
            assert results[d][1] == Fraction(*witness)
            n += 1
    # Full valuation tables agree with the Phase 14 enumeration for d <= 9.
    for d in range(3, 10):
        bits = p14.CERTIFICATES[d][0]
        cells, _ = p14.cut_residues(d, bits)
        leaves, _ = branch_and_bound(d, bits)
        for t, residue in cells.items():
            v = [vv for tau, dep, vv in leaves if tau <= t < tau + Fraction(1, 1 << dep)][0]
            assert v == order(residue)
    return n


def check_witnesses(results, leaves_by_degree):
    """Exact integers at the witness of the maximal loss, at the start of the least-loss
    interval and at random dyadic cuts, against the certified leaf valuations."""
    rng = random.Random(11)
    count = 0
    for d, (L, witness, mn, _) in results.items():
        assert order(mass(d, witness)) == L - 1
        r = (d + 1).bit_length() - 1
        assert order(mass(d, 2 - Fraction(1, 2**(r-1)))) == mn
        leaves = leaves_by_degree[d]
        for _ in range(3):
            t = Fraction(rng.randrange(1 << 10, 1 << 11), 1 << 10)
            v = [vv for tau, dep, vv in leaves if tau <= t < tau + Fraction(1, 1 << dep)][0]
            assert order(mass(d, t)) == v
        count += 5
    return count


def check_exact_endpoints(dmax):
    """Exact integer recurrence at every leaf endpoint and on both sides of it."""
    count = 0
    for d in range(3, dmax+1):
        L = CERT_TABLE[d][0]
        leaves, _ = branch_and_bound(d, L)
        for tau, depth, vv in leaves:
            m = mass(d, tau)
            assert m != 0 and order(m) == vv
            right = tau + Fraction(1, 1 << depth) - Fraction(1, 1 << (depth + 6))
            assert order(mass(d, right)) == vv
            count += 1
        # Without the truncation shortcut the valuation function is the same.
        if d <= 12:
            plain, _ = branch_and_bound(d, L, weight_cap=False)
            for tau, depth, vv in plain:
                assert order(mass(d, tau)) == vv
    return count


@lru_cache(None)
def min_orbit_cost(d, n):
    """min over multisets of d levels with sum c_i 2^-i < n of sum(i c_i - v_2(c_i!))."""
    if d == 0:
        return 0
    if n > d:
        return -v2_factorial(d)
    return min((d-m) - v2_factorial(m) + min_orbit_cost(d-m, 2*(n-m))
               for m in range(0, min(d, n-1)+1))


def low_orbits(d, phimax):
    out = []

    def rec(level, left, loc, phi, chosen):
        if left == 0:
            out.append((loc, phi, tuple(chosen)))
            return
        if phi + (level-1)*left + 1 > phimax:
            return
        for c in range(left, -1, -1):
            nloc = loc + Fraction(c, 1 << level)
            if nloc >= 2:
                continue
            if c:
                chosen.append((level, c))
            rec(level+1, left-c, nloc, phi + level*c - v2_factorial(c), chosen)
            if c:
                chosen.pop()
    rec(0, d, Fraction(0), 0, [])
    return out


def check_minimum_structure(results, dmax_dp=299, dmax_orbits=64):
    for d, (L, w, mn, _) in results.items():
        assert mn == v2_factorial(d) + heap_sum(d), d
    for d in range(1, dmax_dp + 1):
        assert min_orbit_cost(d, 2) == heap_sum(d)
    for d in range(2, dmax_orbits + 1):
        r = (d + 1).bit_length() - 1          # 2^r - 1 <= d <= 2^(r+1) - 2
        j = d - (2**r - 1)
        mins = sorted((loc, ms) for loc, phi, ms in low_orbits(d, heap_sum(d)) if phi == heap_sum(d))
        if j == 0:
            assert mins == [(Fraction(2) - Fraction(1, 2**(r-1)), ((r-1, d),))]
        else:
            lo = ((r-1, 2**r - j - 1), (r, 2*j)) if 2**r - j - 1 else ((r, 2*j),)
            hi = ((r-1, 2**r - j), (r, 2*j - 1))
            assert mins == [(2 - Fraction(1, 2**(r-1)), lo), (2 - Fraction(1, 2**r), hi)], d
    return dmax_dp, dmax_orbits


def check_special_cutoffs(dmax):
    """v_2(M_d(1)) = r d + 2j exactly when C(d, 2j) is odd (d = 2^r + j); constancy
    of M_d on [2 - 2^(1-d), 2); M_2 = 4 - 2^(a+1) on [1 + 2^-a, 1 + 2^(1-a))."""
    exact = 0
    for d in range(2, dmax + 1):
        r = d.bit_length() - 1
        j = d - 2**r
        m1 = mass(d, Fraction(1))
        W = r*d + 2*j
        if comb(d, 2*j) % 2:
            assert order(m1) == W
            exact += 1
        else:
            assert order(m1) > W
        assert mass(d, Fraction(2), True) == mass(d, 2 - Fraction(1, 2**(d-1)))
    for a in range(1, 30):
        assert mass(2, 1 + Fraction(1, 2**a)) == 4 - 2**(a+1)
    return exact


# ---- cyclic descent modulo odd primes ------------------------------------------------

def values_mod_p(e, p, cap=2_000_000):
    """Set of values of M_e(y) mod p over all y in [1, 2), by exhausting the vectors
    of the linear representation over F_p. Returns None if more than cap vectors."""
    if e == 1:
        return {(-1) % p}
    A = Automaton(e)
    N = len(A.states)
    V = [v % p for v in A.V]
    start = [0]*(N+1)
    start[A.start] = 1
    start = tuple(start)
    seen, stack, vals = {start}, [start], set()
    while stack:
        vec = stack.pop()
        vals.add((vec[N] + sum(vec[i]*V[i] for i in range(N) if vec[i])) % p)
        for c in (0, 1):
            new = [0]*(N+1)
            new[N] = vec[N]
            for i in range(N):
                x = vec[i]
                if x:
                    for j, w in A.T[c][i]:
                        if j < 0:
                            new[N] += x*w
                        else:
                            new[j] += x*w
            new = tuple(v % p for v in new)
            if new not in seen:
                seen.add(new)
                if len(seen) > cap:
                    return None
                stack.append(new)
    return vals


GOOD_PAIRS = [(3, 31), (3, 127), (3, 257), (3, 337), (3, 1801), (3, 8191), (4, 8191)]


def check_cyclic_descent():
    rng = random.Random(7)
    checks = 0
    for (p, r, e) in ((3, 1, 2), (3, 1, 4), (5, 1, 2), (3, 2, 2), (7, 1, 2), (5, 1, 3), (3, 1, 5)):
        d = p**r * e
        for _ in range(12):
            t = Fraction(rng.randrange(1 << 12, 1 << 13), 1 << 12)
            x, j = t / p**r, 0
            while x < 1:
                x, j = 2*x, j+1
            assert (mass(d, t) - 2**(e*j) * mass(e, x)) % p == 0
            checks += 1
    for e, p in GOOD_PAIRS:
        vals = values_mod_p(e, p)
        assert vals is not None and 0 not in vals, (e, p)
    # Independent exact spot check on cut points of binary weight <= e.
    for e, p, top in ((3, 31, 24), (4, 8191, 14)):
        for a in range(1, top):
            for b in range(a+1, top+1):
                ys = [1 + Fraction(1, 2**a), 1 + Fraction(1, 2**a) + Fraction(1, 2**b)]
                if e == 4:
                    ys += [1 + Fraction(1, 2**a) + Fraction(1, 2**b) + Fraction(1, 2**(b+1))]
                for y in ys:
                    assert mass(e, y) % p
        assert mass(e, Fraction(1)) % p
    # Sparsity: the only good primes below 60 for e <= 5 are p | e.
    sparsity = {}
    for e in range(2, 6):
        good = []
        for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59):
            vals = values_mod_p(e, p)
            if vals is not None and 0 not in vals:
                good.append(p)
        sparsity[e] = good
    assert sparsity == {2: [], 3: [3, 31], 4: [], 5: [5]}
    return checks, sparsity


def descent_search(emax=7, pmax=10**5, omax=25, cap=400_000):
    """Good pairs (e, p) among primes p < pmax with ord_p(2) <= omax, 3 <= e <= emax."""
    sieve = bytearray([1]) * pmax
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(pmax**0.5) + 1):
        if sieve[i]:
            sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
    primes = []
    for p in range(3, pmax):
        if sieve[p]:
            x, k = 2 % p, 1
            while x != 1 and k < omax:
                x, k = 2*x % p, k + 1
            if x == 1:
                primes.append(p)
    good, capped = [], []
    for e in range(3, emax + 1):
        for p in primes:
            vals = values_mod_p(e, p, cap)
            if vals is None:
                capped.append((e, p))
            elif 0 not in vals:
                good.append((e, p))
    return primes, good, capped


def part_b(max_degree, quick):
    t0 = time.time()
    check_automaton_and_truncation()
    print("B1. linear representation equals the exact recurrence; truncation after the d-th one-bit")
    results, leaves_by_degree = {}, {}
    total_nodes = 0
    for d in range(3, max_degree + 1):
        L = CERT_TABLE[d][0]
        leaves, nodes, witness, mn = certify(d, L)
        results[d] = (L, witness, mn, len(leaves))
        leaves_by_degree[d] = leaves
        total_nodes += nodes
        assert results[d] == (L, Fraction(*CERT_TABLE[d][1]), CERT_TABLE[d][2], CERT_TABLE[d][3]), \
            (d, results[d])
    print(f"B2. certified M_d != 0 on all of [1, 2) for 3 <= d <= {max_degree}: minimal precision L_d "
          f"verified sharp, {total_nodes} branch nodes, {time.time() - t0:.1f}s")
    for d in sorted(results):
        if d in (3, 4, 15, 16, 24, 32, 40, 64, 100, 120):
            L, w, mn, n = results[d]
            print(f"    d={d:3d}: max loss {L-1:4d} first at t = {w}, min loss {mn:4d}, {n} leaves")
    nw = check_witnesses(results, leaves_by_degree)
    print(f"    exact integers confirm the maximal-loss witness, the least-loss point and random cuts ({nw} values)")
    n14 = check_against_phase14(results)
    print(f"    agrees with the Phase 14 multiset certificates in {n14} degrees")
    dm = 16 if quick else 24
    pts = check_exact_endpoints(dm)
    print(f"    exact integer recurrence confirms every leaf valuation for d <= {dm} ({pts} leaves)")
    dp, do = check_minimum_structure(results, 120 if quick else 299, 40 if quick else 64)
    print(f"B3. minimal loss = v_2(d!) + sum floor(log2 k) for all certified d; orbit DP to d = {dp}; "
          f"two minimal orbits at 2 - 2^(1-r), 2 - 2^-r for d <= {do}")
    ex = check_special_cutoffs(60 if quick else 120)
    print(f"B4. special cutoffs: v_2(M_d(1)) = rd + 2j exactly in the {ex} degrees with C(d,2j) odd; "
          f"M_d constant on [2 - 2^(1-d), 2)")
    checks, sparsity = check_cyclic_descent()
    print(f"B5. cyclic descent M_(p^r e)(t) = 2^(ej) M_e(y) mod p in {checks} exact cases; "
          f"good pairs (e, p) {GOOD_PAIRS} certified; good primes < 60: {sparsity}")
    print(f"    Part B done in {time.time() - t0:.1f}s")


CERT_TABLE = CERTIFICATES


def generate(dmax):
    """Recompute table rows from scratch, without the stored precisions."""
    for d in range(3, dmax + 1):
        L = int(d * log2(d) * 1.7) + 40
        leaves, _ = branch_and_bound(d, L)
        maxv = max(v for _, _, v in leaves)
        assert maxv < L
        leaves, nodes, witness, mn = certify(d, maxv + 1)
        print(f"    {d}: ({maxv + 1}, ({witness.numerator}, {witness.denominator}), {mn}, {len(leaves)}),",
              flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-degree", type=int, default=None)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--descent-search", action="store_true",
                        help="search good pairs (e, p), 3 <= e <= 7, p < 10^5 with ord_p 2 <= 25")
    parser.add_argument("--generate", type=int, default=None, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.generate:
        generate(args.generate)
        return
    if args.descent_search:
        primes, good, capped = descent_search()
        assert len(primes) == 23
        print(f"{len(primes)} primes: {primes}")
        print(f"good pairs: {good}")
        print(f"undecided (orbit cap): {capped}")
        assert set(good) == set(GOOD_PAIRS) | {(3, 3), (5, 5), (7, 7)}
        return
    max_degree = args.max_degree or (40 if args.quick else 64)
    max_degree = min(max_degree, max(CERT_TABLE))
    part_a(args.quick)
    part_b(max_degree, args.quick)


if __name__ == "__main__":
    main()
