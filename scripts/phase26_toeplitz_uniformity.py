#!/usr/bin/env python3
"""Phase 26 Track A -- Toeplitz determinants, positivity and quantitative uniformity.

Companion certificate script for notes/phase26/toeplitz-determinants-and-uniformity.md.

Standard library only.  Run:  python -B scripts/phase26_toeplitz_uniformity.py

Sections A1-A7 use exact arithmetic only: Python ints, fractions.Fraction, the
Gaussian rationals Q(i) (class QI below) and the cyclotomic rings Z[x]/Phi_Q
(cyclic integer vectors reduced modulo Phi_Q).  Every assertion in those sections is
counted as [exact].  No float appears in any [exact] assertion.

The final section [finite] contains floating-point experiments (orbit Gram
determinants of ln 2, a Stoneham number, Euler's product, Champernowne's binary
constant, a pseudo-random biased Bernoulli sequence and an explicit mu_alpha
construction).  These are finite measurements only; they are never used in any
proof and never support an asymptotic statement.
"""

import cmath
import math
import random
import sys
import time
from fractions import Fraction as F
from itertools import combinations, permutations, product

COUNTS = {"exact": 0, "finite": 0}
SECTION_COUNTS = {}
_current = ["setup"]


def section(name):
    _current[0] = name
    SECTION_COUNTS.setdefault(name, 0)
    print(f"--- {name}")


def check(cond, msg, kind="exact"):
    if not cond:
        raise AssertionError(f"[{kind}] FAILED: {msg}")
    COUNTS[kind] += 1
    SECTION_COUNTS[_current[0]] = SECTION_COUNTS.get(_current[0], 0) + 1


# ---------------------------------------------------------------------------
# Exact Gaussian rationals Q(i)
# ---------------------------------------------------------------------------
class QI:
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = re if isinstance(re, F) else F(re)
        self.im = im if isinstance(im, F) else F(im)

    @staticmethod
    def c(x):
        return x if isinstance(x, QI) else QI(x, 0)

    def __add__(self, o):
        o = QI.c(o)
        return QI(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = QI.c(o)
        return QI(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return QI.c(o) - self

    def __neg__(self):
        return QI(-self.re, -self.im)

    def __mul__(self, o):
        o = QI.c(o)
        return QI(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = QI.c(o)
        d = o.re * o.re + o.im * o.im
        return QI((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)

    def conj(self):
        return QI(self.re, -self.im)

    def n2(self):
        return self.re * self.re + self.im * self.im

    def __eq__(self, o):
        o = QI.c(o)
        return self.re == o.re and self.im == o.im

    def __hash__(self):
        return hash((self.re, self.im))

    def __repr__(self):
        return f"({self.re}+{self.im}i)"


def qpow(z, k):
    """z**k for k in Z; uses z^{-1} = conj(z) when |z| = 1."""
    if k < 0:
        z = z.conj() if z.n2() == 1 else QI(1) / z
        k = -k
    r, b = QI(1), z
    while k:
        if k & 1:
            r = r * b
        b = b * b
        k >>= 1
    return r


def det(M):
    """Determinant over a field (Fraction or QI entries) by exact elimination."""
    n = len(M)
    if n == 0:
        return F(1)
    A = [list(row) for row in M]
    res = A[0][0] * 0 + 1
    for c in range(n):
        p = next((i for i in range(c, n) if not A[i][c] == 0), None)
        if p is None:
            return A[0][0] * 0
        if p != c:
            A[c], A[p] = A[p], A[c]
            res = -res
        piv = A[c][c]
        res = res * piv
        for i in range(c + 1, n):
            if not A[i][c] == 0:
                f = A[i][c] / piv
                A[i] = [A[i][j] - f * A[c][j] for j in range(n)]
    return res


def realdet(M):
    d = QI.c(det(M))
    check(d.im == 0, "Hermitian determinant is real")
    return d.re


def is_pd_hermitian(M):
    """Sylvester criterion: all leading principal minors > 0 (exact)."""
    for k in range(1, len(M) + 1):
        if not realdet([row[:k] for row in M[:k]]) > 0:
            return False
    return True


def circle_point(t):
    """Rational point ((1-t^2) + 2ti)/(1+t^2) on the unit circle (t = None gives -1)."""
    if t is None:
        return QI(-1, 0)
    t = F(t)
    d = 1 + t * t
    return QI((1 - t * t) / d, 2 * t / d)


def inner(u, v):
    s = QI(0)
    for a, b in zip(u, v):
        s = s + a * b.conj()
    return s


def weyl(z, k):
    """Normalized Weyl sum S(k) = (1/N) sum z_n^k of unimodular points."""
    N = len(z)
    s = QI(0)
    for w in z:
        s = s + qpow(w, k)
    return s / N


def orbit_gram(z, r):
    """G_{jk} = S(k - j), 0 <= j, k < r."""
    S = {k: weyl(z, k) for k in range(-(r - 1), r)}
    return [[S[k - j] for k in range(r)] for j in range(r)]


def gs_residuals(vs):
    """Squared Gram-Schmidt residual norms (classical GS against orthogonal u_i)."""
    us, ds = [], []
    for v in vs:
        u = list(v)
        for w, ww in us:
            if ww == 0:
                continue
            coef = inner(v, w) / ww
            u = [a - coef * b for a, b in zip(u, w)]
        uu = inner(u, u)
        check(uu.im == 0 and uu.re >= 0, "residual norm is real and nonnegative")
        us.append((u, uu.re))
        ds.append(uu.re)
    return ds


def project_out(v, basis):
    """v minus its orthogonal projection onto span(basis)."""
    us = []
    for w in basis:
        u = list(w)
        for x, xx in us:
            if xx == 0:
                continue
            coef = inner(w, x) / xx
            u = [a - coef * b for a, b in zip(u, x)]
        us.append((u, inner(u, u).re))
    out = list(v)
    for x, xx in us:
        if xx == 0:
            continue
        coef = inner(v, x) / xx
        out = [a - coef * b for a, b in zip(out, x)]
    return out


def fpow(x, k):
    return F(1) if k == 0 else x ** k


def igcd(a, b):
    """Integer gcd by Euclid (exact; keeps the math module out of the [exact] sections)."""
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def _dec(scaled, digits):
    s = str(scaled).rjust(digits + 1, "0")
    return s[:-digits] + "." + s[-digits:]


def dec_floor(x, digits):
    """Decimal string of floor(x 10^d)/10^d for a Fraction x >= 0 (integer arithmetic, rounds down)."""
    x = F(x)
    return _dec((x.numerator * 10 ** digits) // x.denominator, digits)


def dec_ceil(x, digits):
    """Decimal string of ceil(x 10^d)/10^d for a Fraction x >= 0 (integer arithmetic, rounds up)."""
    x = F(x)
    return _dec(-((-x.numerator * 10 ** digits) // x.denominator), digits)


# ---------------------------------------------------------------------------
# A1. Gram determinant inequality, Verblunsky factorization, monotonicity,
#     Hadamard-Fischer, equality characterization, rank
# ---------------------------------------------------------------------------
def a1_checks():
    section("A1 Gram determinant inequalities")
    rng = random.Random(260101)
    params = [0, 1, -1, None, F(1, 2), F(-1, 2), 2, -2, F(1, 3), F(2, 3), 3, F(-3, 4), F(3, 4), F(1, 5), F(-2, 3)]
    configs = []
    # structured configurations: r = 1, singular (repeated points), 4th roots of unity
    configs.append(([circle_point(0)], 1))
    configs.append(([circle_point(F(1, 2))] * 3, 3))                          # rank 1, |S| = 1
    configs.append(([circle_point(0), circle_point(1), circle_point(None), circle_point(-1)], 4))   # G = I
    configs.append(([circle_point(0), circle_point(1), circle_point(None), circle_point(-1)], 5))   # rank 4 < 5
    configs.append(([circle_point(0), circle_point(None)], 3))                # two antipodal points
    for _ in range(70):
        N = rng.randint(1, 7)
        r = rng.randint(1, 6)
        pts = [circle_point(rng.choice(params)) for _ in range(N)]
        configs.append((pts, r))
    n_eq_nondeg = 0
    for pts, r in configs:
        N = len(pts)
        G = orbit_gram(pts, r)
        # Hermitian with unit diagonal
        for j in range(r):
            check(G[j][j] == 1, "unit diagonal")
            for k in range(r):
                check(G[j][k] == G[k][j].conj(), "Hermitian")
        S = weyl(pts, 1)
        s2 = S.n2()
        D = [realdet([row[:m] for row in G[:m]]) for m in range(r + 1)]   # D[m] = det G_m
        Dr = D[r]
        check(Dr >= 0, "PSD: det >= 0")
        check(Dr <= 1, "Hadamard: det <= 1")
        bound = fpow(1 - s2, r - 1)
        check(Dr <= bound, "A1.1: det G_r <= (1-|S|^2)^(r-1)")
        check(bound <= fpow(1 - s2, r // 2), "(1-|S|^2)^(r-1) <= (1-|S|^2)^floor(r/2)")
        # Gram-Schmidt factorization on the actual vectors v_j = (z_n^j)
        vs = [[qpow(z, j) for z in pts] for j in range(r)]
        ds = [d / N for d in gs_residuals(vs)]
        prod_d = F(1)
        for d in ds:
            prod_d *= d
        check(prod_d == Dr, "det G = product of normalized GS residuals")
        for j in range(1, r):
            check(ds[j] <= ds[j - 1], "residuals nonincreasing (shift invariance)")
            check(ds[j] <= 1 - s2, "residual <= 1 - |S|^2")
        for m in range(1, r + 1):
            check(D[m] * D[m - 1] == 0 or ds[m - 1] == D[m] / D[m - 1], "d_{m-1} = D_m / D_{m-1}")
        # Verblunsky / partial autocorrelation via projections (Toeplitz shift and antiunitary flip)
        alphas = []
        degenerate = False
        for j in range(1, r):
            if ds[j - 1] == 0:
                degenerate = True
                break
            basis = vs[1:j]
            fj = project_out(vs[j], basis)
            gj = project_out(vs[0], basis)
            check(inner(fj, fj).re / N == ds[j - 1], "||f_j||^2 = d_{j-1}")
            check(inner(gj, gj).re / N == ds[j - 1], "||g_j||^2 = d_{j-1} (antiunitary flip)")
            a = inner(fj, gj) / N / ds[j - 1]
            check(a.n2() <= 1, "|alpha_j| <= 1")
            check(ds[j] == ds[j - 1] * (1 - a.n2()), "d_j = d_{j-1}(1 - |alpha_j|^2)")
            alphas.append(a)
        if r >= 2 and not degenerate:
            check(alphas[0] == S, "alpha_1 = S_N(h)")
        if not degenerate:
            P = F(1)
            for k, a in enumerate(alphas, start=1):
                P *= fpow(1 - a.n2(), r - k)
            check(P == Dr, "det G_r = prod_k (1-|alpha_k|^2)^(r-k)")
            # Burg / maximum-entropy upper bounds from the first m coefficients
            for m in range(1, r):
                Pm = F(1)
                for k in range(1, m + 1):
                    Pm *= fpow(1 - alphas[k - 1].n2(), r - k)
                check(Dr <= Pm, "det G_r <= prod_{k<=m}(1-|alpha_k|^2)^(r-k)")
        # monotonicity of the normalized root and Hadamard-Fischer with remainder block
        for m in range(1, r + 1):
            check(Dr ** m <= D[m] ** r, "(det G_r)^(1/r) <= (det G_m)^(1/m)")
            q, s = divmod(r, m)
            check(D[s] <= 1, "remainder block has det <= 1 (Hadamard)")
            check(Dr <= fpow(D[m], q) * D[s], "Fischer: det G_r <= (det G_m)^q det G_s")
            check(Dr <= fpow(D[m], q), "det G_r <= (det G_m)^floor(r/m)")
        # equality characterization: equality iff S(k) = S^k for 0 <= k < r
        geometric = all(weyl(pts, k) == qpow(S, k) if k > 0 else True for k in range(r))
        equal = (Dr == bound)
        check(equal == geometric, "equality in A1.1 iff S(k) = S(1)^k for k < r")
        if equal and s2 < 1 and r >= 3:
            n_eq_nondeg += 1
        # rank: det > 0 iff number of distinct points >= r
        distinct = len(set(pts))
        check((Dr > 0) == (distinct >= r), "det > 0 iff #distinct points >= r")
    check(n_eq_nondeg >= 1, "a nondegenerate equality case (|S| < 1, r >= 3) occurs")
    # geometric (Poisson / AR(1)) Toeplitz matrices: det = (1-|c|^2)^(r-1) exactly
    for c in [QI(F(1, 2)), QI(F(1, 3), F(1, 4)), QI(F(-2, 5), F(1, 5)), QI(0), QI(F(3, 5), F(-1, 5))]:
        for r in range(1, 8):
            T = [[qpow(c, k - j) if k >= j else qpow(c.conj(), j - k) for k in range(r)] for j in range(r)]
            # qpow with negative exponent is avoided above; c^0 = 1
            check(realdet(T) == fpow(1 - c.n2(), r - 1), "geometric Toeplitz: det = (1-|c|^2)^(r-1)")
    print(f"    {len(configs)} configurations, nondegenerate equality cases: {n_eq_nondeg}")


# ---------------------------------------------------------------------------
# Cyclotomic arithmetic: elements of Z[zeta_Q] as cyclic integer vectors of
# length Q (exponents mod Q); equality is tested after reduction modulo Phi_Q.
# ---------------------------------------------------------------------------
_CYC = {}


def poly_divmod(a, m):
    """Division of integer polynomials (low -> high) by a monic m."""
    a = list(a)
    dm = len(m) - 1
    if len(a) - 1 < dm:
        return [0], a
    q = [0] * (len(a) - dm)
    for i in range(len(a) - 1, dm - 1, -1):
        c = a[i]
        if c:
            q[i - dm] = c
            for j in range(dm + 1):
                a[i - dm + j] -= c * m[j]
    rem = a[:dm] if dm > 0 else [0]
    return q, rem


def cyclotomic(Q):
    if Q in _CYC:
        return _CYC[Q]
    num = [-1] + [0] * (Q - 1) + [1]
    for d in range(1, Q):
        if Q % d == 0:
            num, rem = poly_divmod(num, cyclotomic(d))
            check(all(c == 0 for c in rem), "cyclotomic division exact")
    while len(num) > 1 and num[-1] == 0:
        num.pop()
    _CYC[Q] = num
    return num


def cyc_const(Q, c):
    v = [0] * Q
    v[0] = c
    return v


def cyc_add(u, v):
    return [a + b for a, b in zip(u, v)]


def cyc_sub(u, v):
    return [a - b for a, b in zip(u, v)]


def cyc_mul(u, v):
    Q = len(u)
    out = [0] * Q
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                if b:
                    out[(i + j) % Q] += a * b
    return out


def cyc_reduce(u):
    """Reduce a cyclic vector modulo Phi_Q (canonical representative)."""
    _, rem = poly_divmod(u, cyclotomic(len(u)))
    return rem


def cyc_is_zero(u):
    return all(c == 0 for c in cyc_reduce(u))


def cyc_equal_const(u, c):
    return cyc_is_zero(cyc_sub(u, cyc_const(len(u), c)))


def cyc_det(M):
    """Leibniz determinant of a small matrix over Z[zeta_Q]."""
    r = len(M)
    Q = len(M[0][0])
    total = cyc_const(Q, 0)
    for perm in permutations(range(r)):
        inv = sum(1 for i in range(r) for j in range(i + 1, r) if perm[i] > perm[j])
        term = cyc_const(Q, 1)
        for i in range(r):
            term = cyc_mul(term, M[i][perm[i]])
        total = cyc_add(total, term) if inv % 2 == 0 else cyc_sub(total, term)
    return total


def cyc_abs2_diff(Q, a, c):
    """|zeta^a - zeta^c|^2 = 2 - zeta^(a-c) - zeta^(c-a)."""
    v = cyc_const(Q, 2)
    v[(a - c) % Q] -= 1
    v[(c - a) % Q] -= 1
    return v


def poly_resultant(a, b):
    """Resultant of two polynomials with rational coefficients (low -> high)."""
    a = [F(x) for x in a]
    b = [F(x) for x in b]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    m, n = len(a) - 1, len(b) - 1
    if n == 0:
        return b[0] ** m
    if m < n:
        return (-1) ** (m * n) * poly_resultant(b, a)
    rem = list(a)
    for i in range(m, n - 1, -1):
        c = rem[i] / b[-1]
        if c:
            for j in range(n + 1):
                rem[i - n + j] -= c * b[j]
    rem = rem[:n]
    while len(rem) > 1 and rem[-1] == 0:
        rem.pop()
    if len(rem) == 1 and rem[0] == 0:
        return F(0)
    k = len(rem) - 1
    # Res(a, b) = (-1)^(mn) Res(b, a) and Res(b, a) = lc(b)^(m - k) Res(b, rem)
    return (-1) ** (m * n) * b[-1] ** (m - k) * poly_resultant(b, rem)


def cyc_norm(u):
    """Absolute norm of u in Q(zeta_Q), computed as Res(Phi_Q, u)."""
    red = cyc_reduce(u)
    if all(c == 0 for c in red):
        return F(0)
    return poly_resultant(cyclotomic(len(u)), red)


def orbit_exponents(Q, b, a, h, N):
    """u_n = h a b^n mod Q, so z_n = zeta_Q^(u_n) = e(h b^n a / Q)."""
    return [(h * a * pow(b, n, Q)) % Q for n in range(N)]


def cyc_orbit_NG(Q, us, r):
    """N * G_{N,r}: entries sum_n zeta^((k-j) u_n)."""
    M = []
    for j in range(r):
        row = []
        for k in range(r):
            v = [0] * Q
            for u in us:
                v[((k - j) * u) % Q] += 1
            row.append(v)
        M.append(row)
    return M


def cyc_cauchy_binet(Q, us, r):
    total = cyc_const(Q, 0)
    for I in combinations(range(len(us)), r):
        term = cyc_const(Q, 1)
        for a, c in combinations(I, 2):
            term = cyc_mul(term, cyc_abs2_diff(Q, us[a], us[c]))
        total = cyc_add(total, term)
    return total


# ---------------------------------------------------------------------------
# A4. Exact controls: compound-symmetric Gram matrices, GF-45 limit law,
#     primitive-root rational orbits, regularization
# ---------------------------------------------------------------------------
def compound(alpha, r):
    return [[(1 - alpha) * (1 if j == k else 0) + alpha for k in range(r)] for j in range(r)]


def a4_checks():
    section("A4 exact controls")
    alphas = [F(0), F(1), F(1, 2), F(1, 3), F(2, 7), F(9, 10), F(1, 100), F(-1, 6), F(-1, 12), F(5, 4)]
    for al in alphas:
        for r in range(1, 13):
            G = compound(al, r)
            d = det(G)
            formula = fpow(1 - al, r - 1) * (1 + (r - 1) * al)
            check(d == formula, "det((1-a)I + aJ) = (1-a)^(r-1)(1+(r-1)a)")
            ones = [F(1)] * r
            Gv = [sum(G[j][k] * ones[k] for k in range(r)) for j in range(r)]
            check(all(x == 1 + (r - 1) * al for x in Gv), "all-ones eigenvector, eigenvalue 1+(r-1)a")
            for kk in range(1, r):
                v = [F(0)] * r
                v[0], v[kk] = F(1), F(-1)
                Gv = [sum(G[j][k] * v[k] for k in range(r)) for j in range(r)]
                check(all(Gv[j] == (1 - al) * v[j] for j in range(r)), "e_0 - e_k eigenvectors, eigenvalue 1-a")
            if 0 <= al <= 1:
                check(fpow(1 - al, r) <= d, "(1-a)^r <= det (lambda_min bound)")
                check(d <= r * fpow(1 - al, r - 1), "det <= r (1-a)^(r-1)")
                for t in [F(1, 4), F(1, 2), F(9, 10)]:
                    Gt = [[(1 - t) * G[j][k] + (t if j == k else 0) for k in range(r)] for j in range(r)]
                    al2 = (1 - t) * al
                    check(det(Gt) == fpow(1 - al2, r - 1) * (1 + (r - 1) * al2),
                          "regularized mu_alpha Gram is compound symmetric with alpha' = (1-t) alpha")
                    check(1 - al2 == t + (1 - t) * (1 - al), "limit root 1-(1-t)alpha = t + (1-t) a(mu_alpha)")
    # Fourier coefficients of (M_h)_* mu_alpha: alpha + (1-alpha)[k = 0]
    for al in [F(1, 3), F(3, 4)]:
        for h in [1, 2, -3]:
            for k in range(-4, 5):
                coef = al + ((1 - al) if k * h == 0 else 0)
                check(coef == (1 if k == 0 else al), "mu_alpha Fourier coefficients")
    # primitive-root rational orbits: complete cancellation, G = (1+beta)I - beta J, beta = 1/(Q-1)
    for (Q, b) in [(5, 2), (7, 3), (11, 2), (13, 2)]:
        P = Q - 1
        check(len({pow(b, n, Q) for n in range(P)}) == P, "b is a primitive root mod Q")
        us = orbit_exponents(Q, b, 1, 1, P)
        for k in range(1, Q):
            s = [0] * Q
            for u in us:
                s[(k * u) % Q] += 1
            check(cyc_equal_const(s, -1), "full-period Weyl sum is -1, so S = -1/(Q-1)")
        beta = F(1, Q - 1)
        for r in range(1, Q + 1):
            G = compound(-beta, r)
            check(det(G) == fpow(1 + beta, r - 1) * (1 + beta - r * beta), "det((1+beta)I - beta J)")
            check((det(G) == 0) == (r == Q), "det vanishes exactly at r = Q (rank Q-1)")
        # cross-check one Toeplitz determinant directly in Z[zeta_Q]
        r = 3
        NG = cyc_orbit_NG(Q, us, r)
        lhs = cyc_det(NG)
        target = det(compound(-beta, r)) * P ** r
        check(target.denominator == 1 and cyc_equal_const(lhs, target.numerator),
              "N^r det G_{P,3} in Z[zeta_Q] equals P^3 det((1+beta)I - beta J)")
    # periodic orbit rank: x = 1/7 in base 2 has 3 orbit points; det G_{N,4} = 0, det G_{N,3} != 0
    us = orbit_exponents(7, 2, 1, 1, 6)
    check(not cyc_is_zero(cyc_det(cyc_orbit_NG(7, us, 3))), "periodic orbit 1/7: det G_3 != 0")
    check(cyc_is_zero(cyc_det(cyc_orbit_NG(7, us, 4))), "periodic orbit 1/7: det G_4 = 0 (rank 3)")
    # 1/3 in base 2: invariant measure on two points {1/3, 2/3}: det G_2 != 0, det G_3 = 0
    us = orbit_exponents(3, 2, 1, 1, 4)
    check(not cyc_is_zero(cyc_det(cyc_orbit_NG(3, us, 2))), "1/3 base 2: det G_2 != 0")
    check(cyc_is_zero(cyc_det(cyc_orbit_NG(3, us, 3))), "1/3 base 2: det G_3 = 0 (two-point support)")


# ---------------------------------------------------------------------------
# Atomic configurations on the grid (1/Q)Z with Q in {3, 4, 6}: exact discrepancy
# and exact |S(h)|^2 (all cosines rational).
# ---------------------------------------------------------------------------
_COS = {F(0): F(1), F(1, 6): F(1, 2), F(1, 4): F(0), F(1, 3): F(-1, 2), F(1, 2): F(-1),
        F(2, 3): F(-1, 2), F(3, 4): F(0), F(5, 6): F(1, 2)}


def cos_turn(x):
    """cos(2 pi x) for x in (1/12)Z with denominator dividing 4 or 6."""
    x = F(x) % 1
    return _COS[x]


def extreme_discrepancy(atoms):
    """atoms: list of (t in [0,1), mass); D = sup R - inf R, R(t) = mu([0,t)) - t."""
    atoms = sorted(atoms)
    acc = F(0)
    sup_r, inf_r = F(0), F(0)
    for t, m in atoms:
        left = acc - t
        acc += m
        right = acc - t
        sup_r = max(sup_r, right)
        inf_r = min(inf_r, left)
    return sup_r - inf_r, max(sup_r, -inf_r)   # (extreme D, star D*)


def grid_configs(Q, Nmax):
    for N in range(1, Nmax + 1):
        for cut in combinations(range(N + Q - 1), Q - 1):
            prev, mult = -1, []
            for c in cut + (N + Q - 1,):
                mult.append(c - prev - 1)
                prev = c
            yield N, mult


def grid_abs2_weyl(Q, mult, h):
    N = sum(mult)
    s = F(0)
    for j, mj in enumerate(mult):
        if mj:
            for k, mk in enumerate(mult):
                if mk:
                    s += mj * mk * cos_turn(F(h * (j - k), Q))
    return s / (N * N)


def gauss_grid_points(mult):
    """Q = 4 grid points as exact Gaussian integers i^j."""
    roots = [QI(1), QI(0, 1), QI(-1), QI(0, -1)]
    pts = []
    for j, m in enumerate(mult):
        pts += [roots[j]] * m
    return pts


# ---------------------------------------------------------------------------
# A5. Exact Koksma constant |S_N(h)| <= 2|h| D_N (sharp), Toeplitz operator-norm
#     bound ||G - I|| <= pi |h| (r-1) D_N, Frobenius identities
# ---------------------------------------------------------------------------
PI_LO = F(314159, 100000)      # 3.14159 < pi
PI_HI = F(22, 7)               # pi < 22/7 (Dalzell's integral)


def a5_checks():
    section("A5 Koksma constant and Toeplitz norm bounds")
    # (i) |S(h)| <= 2|h| D and |S(h)| <= 4|h| D* on every grid configuration
    ncfg = 0
    for Q, Nmax in [(3, 10), (4, 8), (6, 6)]:
        for N, mult in grid_configs(Q, Nmax):
            atoms = [(F(j, Q), F(m, N)) for j, m in enumerate(mult) if m]
            D, Dstar = extreme_discrepancy(atoms)
            check(D <= 2 * Dstar and Dstar <= D, "D* <= D <= 2 D*")
            ncfg += 1
            for h in range(1, 7):
                s2 = grid_abs2_weyl(Q, mult, h)
                check(s2 <= 4 * h * h * D * D, "Koksma (sharp form): |S(h)| <= 2|h| D_N")
                check(s2 <= 16 * h * h * Dstar * Dstar, "|S(h)| <= 4|h| D*_N")
    print(f"    Koksma checks on {ncfg} grid configurations, h = 1..6")
    # (ii) sharpness of the constant 2: explicit point set with |S(h)|/(|h| D) > 19/10
    M = 1000
    removed = [j for j in range(M) if abs(F(j, M) - F(1, 2)) <= F(1, 40)]
    E = len(removed)
    mult = [1] * M
    for j in removed:
        mult[j] = 0
    mult[0] += E
    N = sum(mult)
    check(N == M, "sharpness configuration has N = M points")
    # Re S(1) = (1/N)[sum_removed (-cos 2 pi j/M) + E] since sum_j cos(2 pi j/M) = 0;
    # -cos(2 pi j/M) = cos(2 pi s) >= 1 - 2 pi^2 s^2 >= 1 - 2 (22/7)^2 s^2, s = j/M - 1/2
    re_lower = (sum(1 - 2 * PI_HI ** 2 * (F(j, M) - F(1, 2)) ** 2 for j in removed) + E) / N
    # MN-2: the certified six-digit lower bound is 0.101781 (the exact value 0.1017817... rounds up
    # to 0.101782, which is NOT certified by these inequalities)
    check(re_lower >= F(101781, 10 ** 6), "MN-2: Re S_N(1) >= 0.101781 (outward-rounded certified bound)")
    check(re_lower < F(101782, 10 ** 6), "MN-2: re_lower < 0.101782, so 0.101782 is not a certified bound")
    for h in [1, 2, 3]:
        # unwound configuration: sites (j + l M)/(h M), multiplicity mult[j]; S_{hN}(h) = S_N(1)
        atoms = [(F(j + l * M, h * M), F(mult[j], h * N)) for j in range(M) for l in range(h) if mult[j]]
        D, _ = extreme_discrepancy(atoms)
        check(h * D == F(52, 1000), f"sharpness configuration: |h| D_N = 0.052 exactly (h={h})")
        check(re_lower > F(19, 10) * h * D, f"sharpness: |S(h)| >= Re S(h) > (19/10)|h| D_N (h={h})")
        check(re_lower > F(1957, 1000) * h * D, f"sharpness: |S(h)| / (|h| D_N) > 1.957 (h={h})")
        check(re_lower <= 2 * h * D, "consistency with the upper bound 2|h| D_N")
        # diagnostic print, outward-rounded by integer arithmetic (no floats)
        print(f"    sharpness certificate h={h}: Re S >= {dec_floor(re_lower, 6)}, |h|D = {h * D}, "
              f"ratio > {dec_floor(re_lower / (h * D), 4)}")
    # (iii) Toeplitz operator-norm bound beta I +- (G - I) > 0, beta = 3.14159 |h| (r-1) D (Q = 4)
    npd = 0
    for N, mult in grid_configs(4, 5):
        pts = gauss_grid_points(mult)
        atoms = [(F(j, 4), F(m, N)) for j, m in enumerate(mult) if m]
        D, _ = extreme_discrepancy(atoms)
        for h in [1, 2, 3]:
            zh = [qpow(z, h) for z in pts]
            for r in range(2, 5):
                G = orbit_gram(zh, r)
                beta = PI_LO * h * (r - 1) * D
                Ep = [[(beta if j == k else 0) + (G[j][k] - (1 if j == k else 0)) for k in range(r)] for j in range(r)]
                Em = [[(beta if j == k else 0) - (G[j][k] - (1 if j == k else 0)) for k in range(r)] for j in range(r)]
                check(is_pd_hermitian(Ep) and is_pd_hermitian(Em),
                      "||G_{N,r}(h) - I|| < 3.14159 |h| (r-1) D_N <= pi |h| (r-1) D_N")
                npd += 1
                # Frobenius identity ||G - I||_F^2 = 2 sum_{k<r} (r-k)|S(kh)|^2
                fro = sum((G[j][k] - (1 if j == k else 0)).n2() for j in range(r) for k in range(r))
                check(fro == 2 * sum((r - k) * weyl(zh, k).n2() for k in range(1, r)), "Frobenius identity")
    print(f"    operator-norm certificates: {npd}")
    for r in range(1, 60):
        check(sum((r - k) * k * k for k in range(1, r)) == F(r * r * (r * r - 1), 12),
              "sum_{k<r} (r-k) k^2 = r^2 (r^2-1)/12")
        # row-sum constant: max_j sum_k |k - j| = r(r-1)/2
        check(max(sum(abs(k - j) for k in range(r)) for j in range(r)) == r * (r - 1) // 2, "max row |k-j| sum")
    # (iv) log-det comparison constants: for |l| <= eta < 1 the polynomial parts of the bounds
    #      l - l^2/(2(1-eta)) <= log(1+l) <= l - l^2/(2(1+eta)) are consistent: 1/(1+eta) <= 1/(1-eta)
    for eta in [F(1, 10), F(1, 2), F(9, 10)]:
        check(1 / (1 + eta) <= 1 / (1 - eta), "two-sided log-det constants ordered")
    # (v) MJ-1: the unrestricted converse of Corollary 5.4 is false
    converse_counterexample_checks()


def converse_counterexample_checks():
    """MJ-1 counterexample (Corollary 5.4, item 3 of the restricted converse).

    Point set: K = m^3 copies of z = 1 together with the N - K roots of z^(N-K) = 1, where
    N = 2 m^4 and r = m^4.  For 1 <= k <= r - 1 < N - K the roots sum to 0, so
    S_N(k) = K/N = 1/(2m) =: a and G_{N,r}(1) = (1 - a) I_r + a J_r.  Then
    1 >= (det G)^(1/r) >= 1 - a -> 1, while the Fejer energy
    sum_{k<r} (1 - k/r)|S_N(k)|^2 = (r - 1) a^2 / 2 = (m^4 - 1)/(8 m^2) -> infinity, and
    ||E||_op = (r - 1) a >= 1, so Theorem 5.3 does not apply.  At the sub-dimension m one has
    ||G_{N,m}(1) - I|| = (m - 1) a < 1/2 and energy (m - 1) a^2 / 2 -> 0, as the restricted converse
    requires.  All arithmetic is exact (ints, Fractions, Z[zeta_Q]).
    """
    for m in range(2, 7):
        r, N, K = m ** 4, 2 * m ** 4, m ** 3
        Q = N - K
        al = F(K, N)
        check(al == F(1, 2 * m), "MJ-1: alpha = K/N = 1/(2m)")
        check(r - 1 < Q, "MJ-1: every frequency 1 <= k <= r-1 lies below the number N-K of roots")
        formula = fpow(1 - al, r - 1) * (1 + (r - 1) * al)
        if m <= 3:
            # exact verification of the Weyl sums in Z[zeta_Q]: N S_N(k) = K for 1 <= k <= r - 1
            for k in range(1, r):
                g = igcd(k, Q)
                v = [0] * Q
                for j in range(Q):
                    v[(j * k) % Q] += 1
                check(all(v[e] == (g if e % g == 0 else 0) for e in range(Q)),
                      "MJ-1: {jk mod Q : j < Q} is g copies of gZ/QZ, g = gcd(k, Q)")
                check(Q // g >= 2, "MJ-1: Q/g >= 2, so the (Q/g)-th roots of unity sum to 0")
                v[0] += K                      # the K points at z = 1
                check(cyc_equal_const(v, K), "MJ-1: N S_N(k) = K exactly in Z[zeta_Q]")
            G = [[F(1) if j == k else al for k in range(r)] for j in range(r)]   # entries S_N(k - j)
            check(G == compound(al, r), "MJ-1: G_{N,r}(1) = (1-a) I_r + a J_r")
            check(det(G) == formula, "MJ-1: det G_{N,r}(1) = (1-a)^(r-1) (1+(r-1)a) (Proposition 4.1)")
        check(formula <= 1, "MJ-1: det G_{N,r}(1) <= 1 (Hadamard), so the root is <= 1")
        check(formula >= fpow(1 - al, r), "MJ-1: (det G_{N,r}(1))^(1/r) >= 1 - a = 1 - 1/(2m)")
        energy = sum((1 - F(k, r)) * al * al for k in range(1, r))
        check(energy == (r - 1) * al * al / 2, "MJ-1: Fejer energy = (r-1) a^2 / 2")
        check(energy == F(m ** 4 - 1, 8 * m * m), "MJ-1: Fejer energy = (m^4-1)/(8 m^2)")
        check(energy >= F(m * m - 1, 8), "MJ-1: Fejer energy >= (m^2-1)/8 -> infinity")
        check((r - 1) * al >= 1, "MJ-1: ||E||_op = (r-1) a >= 1, so Theorem 5.3 does not apply")
        check((m - 1) * al < F(1, 2), "MJ-1: sub-dimension m: ||G_{N,m}(1) - I|| = (m-1) a < 1/2")
        check((m - 1) * al * al / 2 <= F(1, 8 * m), "MJ-1: sub-dimension m: energy (m-1) a^2/2 <= 1/(8m)")
        print(f"    MJ-1 counterexample m={m}: r={r}, root >= 1 - 1/{2 * m}, "
              f"Fejer energy = {energy} >= {F(m * m - 1, 8)}, ||E|| = {(r - 1) * al}")


# ---------------------------------------------------------------------------
# A6. Weak positivity certificates: D+ < 1 iff limsup |S_N(1)| < 1 (2x2 determinant),
#     explicit constants, biased Bernoulli, finite interval-mass certificate
# ---------------------------------------------------------------------------
def bernoulli_grid(p, K):
    """mu_p (P(digit 0) = p) masses of the 2^K dyadic cells, ordered by binary value."""
    masses = [F(1)]
    for _ in range(K):
        masses = [m * w for m in masses for w in (p, 1 - p)]
    return masses


def a6_checks():
    section("A6 weak positivity certificates")
    # (i) explicit thresholds for the ln 2 target D+(ln 2; 2) <= 0.9999
    delta = F(1, 10 ** 4)
    check(PI_HI ** 2 < 10, "pi^2 < (22/7)^2 < 10")
    sigma0 = 1 - 2 * delta - 5 * delta ** 2
    check(sigma0 == F(99979995, 10 ** 8), "sigma_0 = 0.99979995")
    phase23 = (1 - delta) * (1 - (PI_HI * delta) ** 2 / 2) - delta
    check(phase23 >= sigma0, "Phase 23 form (1-d)(1-(22d/7)^2/2)-d >= 1-2d-5d^2")
    check(phase23 > F(9997, 10000), "Phase 23 threshold 0.9997 is implied")
    eta0 = 16 * delta ** 3 / 27
    ell = 2 * delta / 3
    check(4 * ell ** 2 * (delta - ell) == eta0, "max_l 4 l^2 (d - l) = 16 d^3/27 at l = 2d/3")
    for l2 in [delta / 2, delta / 3, 3 * delta / 4, delta / 10]:
        check(4 * l2 ** 2 * (delta - l2) <= eta0, "l = 2d/3 maximizes 4 l^2 (d - l)")
    check(eta0 == F(16, 27 * 10 ** 12), "D+ <= 0.9999 forces limsup|S_N(1)| <= 1 - 16/(27 10^12)")
    # (ii) per-N two-sided inequalities on grid configurations
    nq = 0
    for Q, Nmax in [(3, 9), (4, 8), (6, 6)]:
        for N, mult in grid_configs(Q, Nmax):
            atoms = [(F(j, Q), F(m, N)) for j, m in enumerate(mult) if m]
            D, _ = extreme_discrepancy(atoms)
            s2 = grid_abs2_weyl(Q, mult, 1)
            for ell in [F(1, 16), F(1, 8), F(1, 4), F(3, 8), F(1, 2)]:
                X = 4 * ell ** 2 * (1 - ell - D)
                if 0 <= X <= 1:
                    check(s2 <= (1 - X) ** 2, "D_N >= 1 - l - (1-|S_N(1)|)/(4 l^2)")
                    nq += 1
            dl = 1 - D
            if dl <= F(1, 2):
                g = 1 - 2 * dl - 5 * dl ** 2
                if g > 0:
                    check(s2 >= g * g, "D_N = 1 - d implies |S_N(1)| >= 1 - 2d - 5d^2")
                    nq += 1
    print(f"    per-N D_N <-> |S_N(1)| inequalities: {nq}")
    # (iii) biased Bernoulli: positive cylinder masses, explicit D(mu_p) < 1, exact enclosure
    K = 12
    for p in [F(1, 3), F(1, 4), F(2, 5), F(1, 10)]:
        q = min(p, 1 - p)
        masses = bernoulli_grid(p, K)
        check(sum(masses) == 1 and all(m > 0 for m in masses), "mu_p: every cylinder has positive mass")
        acc, sup_r, inf_r = F(0), F(0), F(0)
        for idx, m in enumerate(masses):
            t = F(idx, 2 ** K)
            sup_r, inf_r = max(sup_r, acc - t), min(inf_r, acc - t)
            acc += m
        Dgrid = sup_r - inf_r
        maxcell = max(masses)
        Dup = Dgrid + maxcell + F(1, 2 ** K)
        k = 1
        while not 2 * (1 - q) ** k < 1:
            k += 1
        bound = max(2 * (1 - q) ** k, 1 - q ** k, F(2, 2 ** k))
        check(bound < 1, "explicit bound D(mu_p) <= max(2(1-q)^k, 1-q^k, 2^(1-k)) < 1")
        check(Dgrid <= bound, "grid discrepancy consistent with the explicit bound")
        if p == F(1, 3):
            check(Dup <= F(8, 9), "exact enclosure: D(mu_1/3) <= D_grid + maxcell + 2^-K <= 8/9")
            check(bound == F(8, 9), "explicit bound for p = 1/3 is 8/9")
            # MN-2: the published enclosure [0.239065, 0.247017] is outward-rounded
            check(Dgrid >= F(239065, 10 ** 6), "MN-2: D(mu_1/3) >= D_grid >= 0.239065")
            check(Dup <= F(247017, 10 ** 6), "MN-2: D(mu_1/3) <= D_up <= 0.247017")
            print(f"    D(mu_1/3) in [{dec_floor(Dgrid, 6)}, {dec_ceil(Dup, 6)}]  (outward-rounded)")
    # (iv) finite interval-mass certificate: lambda_min(G_{N,r}(1)) >= gamma implies
    #      D_N <= 1 - gamma + 2 sqrt(gamma / r)   (checked as (D-1+gamma)_+^2 <= 4 gamma / r)
    ncert = 0
    for N, mult in grid_configs(4, 6):
        pts = gauss_grid_points(mult)
        atoms = [(F(j, 4), F(m, N)) for j, m in enumerate(mult) if m]
        D, _ = extreme_discrepancy(atoms)
        for r in range(1, 5):
            G = orbit_gram(pts, r)
            lo, hi = 0, 33          # largest kk in [1, 32] with G - (kk/32) I positive definite (monotone)
            while hi - lo > 1:
                mid = (lo + hi) // 2
                g = F(mid, 32)
                if is_pd_hermitian([[G[j][k] - (g if j == k else 0) for k in range(r)] for j in range(r)]):
                    lo = mid
                else:
                    hi = mid
            gamma = F(lo, 32)
            if gamma > 0:
                lhs = max(F(0), D - 1 + gamma)
                check(lhs * lhs <= 4 * gamma / r, "interval-mass certificate D_N <= 1 - gamma + 2 sqrt(gamma/r)")
                ncert += 1
    print(f"    interval-mass certificates: {ncert}")


# ---------------------------------------------------------------------------
# A7. Cauchy-Binet, cyclotomic norms, Vandermonde divisibility, random-point law,
#     denominator-only and rank-only countermodels
# ---------------------------------------------------------------------------
def gi_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gi_det(M):
    r = len(M)
    tot = (0, 0)
    for perm in permutations(range(r)):
        inv = sum(1 for i in range(r) for j in range(i + 1, r) if perm[i] > perm[j])
        term = (1, 0)
        for i in range(r):
            term = gi_mul(term, M[i][perm[i]])
        tot = (tot[0] + term[0], tot[1] + term[1]) if inv % 2 == 0 else (tot[0] - term[0], tot[1] - term[1])
    return tot


def a7_checks():
    section("A7 Cauchy-Binet, arithmetic and countermodels")
    rng = random.Random(260707)
    params = [0, 1, -1, None, F(1, 2), F(-1, 2), 2, F(1, 3), F(2, 3), F(-3, 4), F(3, 2)]
    # (i) Cauchy-Binet over Q(i): N^r det G = sum_{|I|=r} prod_{a<c} |z_a - z_c|^2
    for _ in range(40):
        N = rng.randint(1, 6)
        r = rng.randint(1, 4)
        pts = [circle_point(rng.choice(params)) for _ in range(N)]
        lhs = realdet(orbit_gram(pts, r)) * N ** r
        rhs = F(0)
        for I in combinations(range(N), r):
            term = F(1)
            for a, c in combinations(I, 2):
                term *= (pts[a] - pts[c]).n2()
            rhs += term
        check(lhs == rhs, "Cauchy-Binet expansion of the orbit Gram determinant (Q(i))")
        if r == 2:
            S = weyl(pts, 1)
            check(1 - S.n2() == rhs / N ** 2, "det G_2 = 1 - |S|^2 = N^-2 sum_{i<j} |z_i - z_j|^2")
    # (ii) Cauchy-Binet in Z[zeta_Q] for rational orbits x = a/Q, and Vandermonde divisibility
    cases = [(7, 2, 1, 1, 6, 3), (7, 3, 1, 1, 6, 4), (7, 3, 2, 1, 5, 3), (9, 2, 1, 1, 6, 3), (9, 2, 1, 3, 6, 2),
             (5, 2, 1, 1, 4, 3), (5, 2, 1, 1, 5, 4), (11, 2, 1, 1, 6, 3), (11, 2, 3, 2, 7, 3), (13, 2, 1, 1, 6, 3),
             (13, 5, 1, 1, 4, 3), (8, 3, 1, 1, 4, 2), (12, 5, 1, 1, 4, 2), (7, 2, 1, 1, 6, 4), (11, 3, 1, 1, 5, 4)]
    for (Q, b, a, h, N, r) in cases:
        us = orbit_exponents(Q, b, a, h, N)
        X = cyc_det(cyc_orbit_NG(Q, us, r))
        CB = cyc_cauchy_binet(Q, us, r)
        check(cyc_is_zero(cyc_sub(X, CB)), f"cyclotomic Cauchy-Binet (Q={Q}, b={b}, N={N}, r={r})")
        distinct = len(set(us))
        check(cyc_is_zero(X) == (distinct < r), "N^r det G = 0 iff fewer than r distinct orbit points")
        nm = cyc_norm(X)
        check(nm >= 0 and nm.denominator == 1, "norm of N^r det G is a nonnegative integer (totally nonnegative)")
        if Q in (5, 7, 11, 13):           # prime: (1 - zeta)^(r(r-1)) divides N^r det G
            pw = Q ** (r * (r - 1))
            check(nm.numerator % pw == 0, "Vandermonde divisibility: p^(r(r-1)) | Norm(N^r det G)")
            if nm != 0:
                check(nm >= pw, "Galois-averaged lower bound: Norm >= p^(r(r-1))")
    # (iii) uniform Q-th roots: sum_{|I|=r} prod |zeta^a - zeta^c|^2 = Q^r for r <= Q (G = I)
    for Q in range(2, 10):
        for r in range(1, Q + 1):
            check(cyc_equal_const(cyc_cauchy_binet(Q, list(range(Q)), r), Q ** r),
                  f"uniform roots identity sum |V_I|^2 = Q^r (Q={Q}, r={r})")
    # (iv) random-point law: z_n i.i.d. uniform on mu_4 gives E det G_{N,r} = prod_{j<r} (1 - j/N), r <= 4
    for N in range(1, 7):
        for r in range(1, min(N, 4) + 1):
            total = 0
            for es in product(range(4), repeat=N):
                M = []
                for j in range(r):
                    row = []
                    for k in range(r):
                        cnt = [0, 0, 0, 0]
                        for e in es:
                            cnt[((k - j) * e) % 4] += 1
                        row.append((cnt[0] - cnt[2], cnt[1] - cnt[3]))
                    M.append(row)
                d = gi_det(M)
                check(d[1] == 0 and d[0] >= 0, "det(N G) is a nonnegative integer")
                total += d[0]
            falling = 1
            for j in range(r):
                falling *= (N - j)
            check(total == 4 ** N * falling, f"E det G_(N,r) = prod (1 - j/N) on mu_4 (N={N}, r={r})")
    # (v) denominator-only / rank-only countermodel: distinct clustered points z_n = z(1/(K+n)), K = N:
    #     every Cauchy-Binet term is positive but det G_2 = 1 - |S|^2 < 2/K^2 -> 0
    for N in [4, 8, 12, 16]:
        pts = [circle_point(F(1, N + n)) for n in range(N)]
        check(len(set(pts)) == N, "clustered countermodel: all points distinct")
        S = weyl(pts, 1)
        pair = F(0)
        for a, c in combinations(range(N), 2):
            dd = (pts[a] - pts[c]).n2()
            check(dd > 0, "every pair contributes a positive Vandermonde factor")
            pair += dd
        check(1 - S.n2() == pair / N ** 2, "1 - |S|^2 = N^-2 sum |z_i - z_j|^2")
        check(1 - S.n2() < F(2, N * N), "det G_2 < 2/K^2 although rank is full")
        for r in range(2, min(N, 3) + 1):
            check(realdet(orbit_gram(pts, r)) > 0, "full rank: det G_r > 0")


# ---------------------------------------------------------------------------
# [finite] Floating-point finite measurements (never used in any proof)
# ---------------------------------------------------------------------------
def int_bits_ln2(B, G=48):
    tot, k = 0, 1
    one = 1 << (B + G)
    while (k << k) <= one:
        tot += one // (k << k)
        k += 1
    return tot >> G


def int_bits_stoneham23(B, G=48):
    tot, k = 0, 1
    while 3 ** k <= B + G:
        tot += (1 << (B + G - 3 ** k)) // (3 ** k)
        k += 1
    return tot >> G


def int_bits_euler2(B, G=48):
    X = 1 << (B + G)
    for k in range(1, B + G + 1):
        X -= X >> k
    return X >> G


def bits_to_int(bits):
    v = 0
    for d in bits:
        v = (v << 1) | d
    return v


def champernowne_bits(B):
    out, n = [], 1
    while len(out) < B:
        out += [int(c) for c in bin(n)[2:]]
        n += 1
    return out[:B]


def mu_half_bits(B):
    """Champernowne blocks of length k followed by zero runs of length k (alpha = 1/2)."""
    C = champernowne_bits(B)
    out, pos, k = [], 0, 1
    while len(out) < B:
        out += C[pos:pos + k]
        pos += k
        out += [0] * k
        k += 1
    return out[:B]


def orbit_points(X, B, N):
    mask = (1 << 53) - 1
    return [((X >> (B - n - 53)) & mask) / float(1 << 53) for n in range(N)]


def float_det_hermitian(G):
    n = len(G)
    A = [row[:] for row in G]
    d = 1.0 + 0j
    for c in range(n):
        p = max(range(c, n), key=lambda i: abs(A[i][c]))
        if abs(A[p][c]) == 0:
            return 0.0
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            for j in range(c, n):
                A[i][j] -= f * A[c][j]
    return d.real


def finite_section():
    section("[finite] floating-point measurements")
    B = 4096 + 128
    rng = random.Random(2026)
    sources = {
        "ln 2": int_bits_ln2(B),
        "Stoneham a(2,3)": int_bits_stoneham23(B),
        "Euler E_2": int_bits_euler2(B),
        "Champernowne_2": bits_to_int(champernowne_bits(B)),
        "Bernoulli p=1/3": bits_to_int([0 if rng.random() < 1 / 3 else 1 for _ in range(B)]),
        "mu_1/2 construction": bits_to_int(mu_half_bits(B)),
    }
    rs = [1, 2, 4, 8, 16, 32]
    print(f"    {'number':22s} {'N':>5s} {'|S_N(1)|':>9s} " + " ".join(f"{'r=' + str(r):>8s}" for r in rs[1:]))
    for name, X in sources.items():
        for N in [256, 1024, 4096]:
            ts = orbit_points(X, B, N)
            S = [sum(cmath.exp(2j * math.pi * k * t) for t in ts) / N for k in range(max(rs))]
            roots = []
            for r in rs:
                G = [[S[k - j] if k >= j else S[j - k].conjugate() for k in range(r)] for j in range(r)]
                dval = float_det_hermitian(G)
                bound = (1 - abs(S[1]) ** 2) ** (r - 1) if r > 1 else 1.0
                check(dval >= -1e-9 and dval <= bound + 1e-9, "finite: 0 <= det <= (1-|S|^2)^(r-1)", "finite")
                roots.append(max(dval, 0.0) ** (1.0 / r))
            for a, b in zip(roots, roots[1:]):
                check(b <= a + 1e-7, "finite: normalized root nonincreasing in r", "finite")
            print(f"    {name:22s} {N:5d} {abs(S[1]):9.5f} " + " ".join(f"{v:8.5f}" for v in roots[1:]))


def main():
    t0 = time.time()
    a1_checks()
    a4_checks()
    a5_checks()
    a6_checks()
    a7_checks()
    finite_section()
    print("=" * 72)
    for name, cnt in SECTION_COUNTS.items():
        if cnt:
            print(f"  {name:50s} {cnt:8d}")
    print(f"  [exact] assertions: {COUNTS['exact']}")
    print(f"  [finite] assertions (floating point, isolated): {COUNTS['finite']}")
    print(f"  total: {COUNTS['exact'] + COUNTS['finite']}   time {time.time() - t0:.1f}s")
    print("All Phase 26 Track A certificates passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
