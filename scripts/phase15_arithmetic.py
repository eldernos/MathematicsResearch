"""Phase 15, tracks C and D: exact arithmetic lifts of dyadic logarithm prefixes.

Run `python3 -B scripts/phase15_arithmetic.py` (about a minute; `--quick` is shorter).
Prefix identities, denominator computations and the atlas shadowing windows use
integer or rational arithmetic. Root, quadrature and log-size diagnostics use
floating-point or Decimal arithmetic.
The accompanying proofs and scope statements are in notes/phase15/arithmetic-lifts.md.

Conventions. A *trace source* is a monic integer polynomial f with roots a_i, an
integer t with |a_i| < 2^t, and an integer n >= 1. Its prefix at the homogeneous
cutoff M (an integer, meaning the real cutoff x = M/2) is

    S(M) = sum_{j >= 1, n*j <= M} p_j / (j * 2^(t*j)),     p_j = sum_i a_i^j,

so that S(infinity) = d*t*log 2 - log|f(2^t)|. The real source A_k is f = X-1,
t = k, n = 2k. The Gaussian source G_t is f = X^2-2X+2, n = 2t-1, whose terms are
2 Re((1+i)^j)/(j 2^(tj)). The shifted prefix at the binary cutoff N is Y_N = 2^N S(2N).
"""

import sys
from decimal import Decimal, getcontext
from fractions import Fraction as Q
from itertools import product
from math import gcd, isqrt, log, log2, comb, factorial
import cmath
from discrepancy_experiments import log_bits

# ----------------------------------------------------------------------------------
# Elementary tools
# ----------------------------------------------------------------------------------


def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = b"\0\0"
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


def factor_small(n, bound=10**6):
    """Trial division; returns {p: e}. Fails loudly if a cofactor above bound^2 remains."""
    n = abs(n)
    out = {}
    d = 2
    while d <= bound and d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        if d * d <= n:
            raise ValueError("unfactored cofactor exceeds trial division limit")
        out[n] = out.get(n, 0) + 1
    return out


def newton(f, J):
    """Power sums p_1..p_J of the roots of the monic integer polynomial f (low to high)."""
    d = len(f) - 1
    assert f[-1] == 1
    e = [1] + [(-1) ** k * f[d - k] for k in range(1, d + 1)]
    p = [0] * (J + 1)
    for j in range(1, J + 1):
        s = 0
        for k in range(1, min(j - 1, d) + 1):
            s += (-1) ** (k - 1) * e[k] * p[j - k]
        if j <= d:
            s += (-1) ** (j - 1) * j * e[j]
        p[j] = s
    return p


def poly_eval(f, x):
    r = 0
    for c in reversed(f):
        r = r * x + c
    return r


def dec_log(x, prec):
    getcontext().prec = prec
    return Decimal(x).ln()


class Source:
    """A dyadic trace source (f, t, n); see the module docstring."""

    def __init__(self, name, f, t, n):
        self.name, self.f, self.t, self.n = name, list(f), t, n
        self.d = len(f) - 1
        self._ps = [0]

    def ps(self, J):
        if len(self._ps) <= J:
            self._ps = newton(self.f, max(J, 2 * len(self._ps)))
        return self._ps

    def prefix(self, jmax):
        """sum_{j<=jmax} p_j / (j 2^(tj)) as a Fraction."""
        p = self.ps(jmax)
        return sum((Q(p[j], j << (self.t * j)) for j in range(1, jmax + 1)), Q())

    def cell(self, v):
        """Prefix at the integer cutoff M=v (real cutoff x=v/2)."""
        return self.prefix(v // self.n)

    def infinite_valuation(self):
        """Exponent vector (e_2, e_3, e_5, ...) with value sum e_p log p (dict)."""
        B = 1 << self.t
        fac = factor_small(poly_eval(self.f, B))
        val = {p: -e for p, e in fac.items()}
        val[2] = val.get(2, 0) + self.d * self.t
        return {p: e for p, e in val.items() if e}


def A(k):
    return Source("A%d" % k, [-1, 1], k, 2 * k)


def G(t):
    return Source("G%d" % t, [2, -2, 1], t, 2 * t - 1)


def Am(k):
    """Signed real source: -log(1 + 2^-k)."""
    return Source("A%d-" % k, [1, 1], k, 2 * k)


def Gm(t):
    """Sign twin of G_t, roots -(1 +- i)."""
    return Source("G%d-" % t, [2, 2, 1], t, 2 * t - 1)


def combo_cell(coef, v):
    return sum((c * s.cell(v) for s, c in coef), Q())


# ----------------------------------------------------------------------------------
# Section 1. Bezout lemma: integer combinations of sources and the gcd
# ----------------------------------------------------------------------------------


def egcd(a, b):
    if b == 0:
        return (abs(a), (1 if a >= 0 else -1), 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def bezout_certificate(nums, c):
    """Integers x_i with sum x_i nums_i = c, or None. Solvable iff gcd(nums) divides c."""
    g, coeffs = 0, []
    for a in nums:
        g2, x, y = egcd(g, a)
        coeffs = [cc * x for cc in coeffs] + [y]
        g = g2
    if g == 0:
        return [0] * len(nums) if c == 0 else None
    if c % g:
        return None
    return [cc * (c // g) for cc in coeffs]


def int_kernel(E, k):
    """Basis of {x in Z^k : E x = 0} by unimodular column reduction."""
    r = len(E)
    cols = [[E[i][c] for i in range(r)] + [int(i == c) for i in range(k)] for c in range(k)]
    piv = 0
    for row in range(r):
        while True:
            nz = [c for c in range(piv, k) if cols[c][row]]
            if len(nz) <= 1:
                break
            m = min(nz, key=lambda c: abs(cols[c][row]))
            for c in nz:
                if c != m:
                    q = cols[c][row] // cols[m][row]
                    cols[c] = [a - q * b for a, b in zip(cols[c], cols[m])]
        nz = [c for c in range(piv, k) if cols[c][row]]
        if nz:
            cols[piv], cols[nz[0]] = cols[nz[0]], cols[piv]
            piv += 1
    kernel = [col[r:] for col in cols[piv:]]
    for x in kernel:
        assert all(sum(E[i][c] * x[c] for c in range(k)) == 0 for i in range(r))
    return kernel


def target_lattice(sources):
    """Valuation data, kernel and the gcd g with: integer relation sum x_i V_i = m log 2 exists iff g | m."""
    vals = [s.infinite_valuation() for s in sources]
    odd = sorted({p for v in vals for p in v if p != 2})
    E = [[v.get(p, 0) for v in vals] for p in odd]
    two = [v.get(2, 0) for v in vals]
    K = int_kernel(E, len(sources))
    contents = [sum(a * b for a, b in zip(two, x)) for x in K]
    g = 0
    for c in contents:
        g = gcd(g, c)
    return vals, odd, E, two, K, contents, g


def reach_certificate(sources, m):
    vals, odd, E, two, K, contents, g = target_lattice(sources)
    lam = bezout_certificate(contents, m)
    if lam is None:
        return None
    x = [sum(l * kv[i] for l, kv in zip(lam, K)) for i in range(len(sources))]
    assert sum(a * b for a, b in zip(two, x)) == m
    assert all(sum(E[r][i] * x[i] for i in range(len(x))) == 0 for r in range(len(E)))
    return x


def section_bezout(quick):
    print("== 1. Bezout lemma and the target lattice")
    for a, b in product(range(-12, 13), repeat=2):
        for c in range(-30, 31):
            cert = bezout_certificate([a, b], c)
            solvable = any(a * x + b * y == c for x in range(-40, 41) for y in range(-40, 41)) \
                if (a or b) and abs(c) <= 6 and not quick else None
            if cert is not None:
                assert a * cert[0] + b * cert[1] == c
                assert (a or b) and c % gcd(a, b) == 0 or (a == b == 0 and c == 0)
            else:
                assert (a == b == 0 and c) or c % gcd(a, b)
                if solvable is not None:
                    assert not solvable
    print("   a*x+b*y=c: certificate exists iff gcd(a,b) | c, checked on a grid (with brute-force search for small c)")
    full = [A(1), A(2), A(3), A(4), A(6), G(1), G(2), G(3)]
    vals, odd, E, two, K, contents, g = target_lattice(full)
    print("   Phase 14 alphabet: odd-prime kernel has rank", len(K), "(zero relations rank", len(K) - 1,
          "), gcd of dyadic content", g)
    assert len(K) == 5 and g == 1
    for m in (1, 2, 5, -3):
        x = reach_certificate(full, m)
        assert x is not None
    examples = []
    pool = [A(k) for k in range(1, 7)] + [Am(k) for k in range(1, 7)] + [G(t) for t in range(1, 4)] +         [Gm(t) for t in range(1, 4)]
    names = [s.name for s in pool]
    from itertools import combinations
    for r in range(2, 5):
        for sub in combinations(range(len(pool)), r):
            S = [pool[i] for i in sub]
            data = target_lattice(S)
            if data[4] and data[6] not in (0, 1):
                examples.append(([names[i] for i in sub], data[6], len(data[4])))
        if len(examples) >= 2:
            break
    examples.sort(key=lambda e: (len(e[0]), e[1]))
    for names_, g2, rk in examples[:4]:
        sub = [s for s in pool if s.name in names_]
        assert reach_certificate(sub, g2) is not None
        assert reach_certificate(sub, 1) is None
        assert reach_certificate(sub, g2 + 1) is None or g2 == 1
        print("   subalphabet", "+".join(names_), ": odd-prime kernel rank", rk, "reaches m*log2 iff", g2, "| m")
    assert examples, "expected at least one proper sub-alphabet with g > 1"
    # brute-force confirmation of necessity on the first example
    names_, g2, rk = examples[0]
    sub = [s for s in pool if s.name in names_]
    vals, odd, E, two, K, contents, g = target_lattice(sub)
    found = set()
    R = 6 if quick else 9
    for x in product(range(-R, R + 1), repeat=len(sub)):
        if all(sum(E[r][i] * x[i] for i in range(len(sub))) == 0 for r in range(len(E))):
            found.add(sum(a * b for a, b in zip(two, x)))
    assert all(m % g2 == 0 for m in found) and (g2 in found or -g2 in found)
    print("   brute force over the box |x_i| <=", R, "reaches exactly multiples of", g2, ":", sorted(found)[:7])

    # the cell lattice: smallest nonzero cell value of an integer combination
    v = 12
    cells = [s.cell(v) for s in full]
    den = 1
    for c in cells:
        den = den * c.denominator // gcd(den, c.denominator)
    nums = [int(c * den) for c in cells]
    gc = 0
    for a in nums:
        gc = gcd(gc, a)
    vals_box = {sum(x * a for x, a in zip(xs, nums)) for xs in product(range(-2, 3), repeat=len(full))}
    assert all(w % gc == 0 for w in vals_box)
    cert = bezout_certificate(nums, gc)
    assert cert is not None and sum(x * a for x, a in zip(cert, nums)) == gc
    assert bezout_certificate(nums, gc + 1) is None or gc == 1
    print("   cell v=12: nonzero integer combinations of the eight cell values are multiples of", Q(gc, den),
          "(Bezout); a certificate attains the minimum")


# ----------------------------------------------------------------------------------
# Section 2. Prefix-level relations are multiplicative relations of root multisets
# ----------------------------------------------------------------------------------


def mobius(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def nu(n, vec):
    """Distribution operator: each theta becomes the n-th roots (theta+m)/n mod 1 (xi^n = e(theta))."""
    out = {}
    for th, mult in vec.items():
        for m in range(n):
            xi = ((th + m) / n) % 1
            out[xi] = out.get(xi, 0) + mult
    return out


def add(u, v, c=1):
    out = dict(u)
    for k, m in v.items():
        out[k] = out.get(k, 0) + c * m
        if out[k] == 0:
            del out[k]
    return out


def Zvec(c):
    return {Q(m, c): 1 for m in range(c)}


def orbit(M, ap):
    """u-argument set of the Galois orbit of 2^(ap/2) * zeta_M, as a set (multiplicity one)."""
    units = [s for s in range(1, M + 1) if gcd(s, M) == 1]
    th = set()
    for s in units:
        if ap % 2 == 0:
            th.add(Q(s, M) % 1)
        elif M % 8 == 0:
            th.add((Q(s, M) + (Q(1, 2) if s % 8 in (3, 5) else 0)) % 1)
        else:
            th.add(Q(s, M) % 1)
            th.add((Q(s, M) + Q(1, 2)) % 1)
    return {x: 1 for x in th}


def dec_vec_A(k):
    return nu(2 * k, {Q(0): 1})


def dec_vec_G(t):
    return nu(2 * t - 1, {Q(1, 8): 1, Q(7, 8): 1})


def decompose(M, ap, n):
    """Integer coefficients {('A',k): c, ('G',t): c} with source(orbit, n) = combination. Verified by caller."""
    res = {}

    def addA(k, c):
        res[("A", k)] = res.get(("A", k), 0) + c

    def via_Z(coefs):  # coefs: {c: a} meaning sum a * nu_n Z_c = sum a * Z_{nc}
        acc = {}
        for c, a in coefs.items():
            acc[n * c] = acc.get(n * c, 0) + a
        for idx, a in acc.items():
            if a:
                assert idx % 2 == 0, "odd real index would not be an A-source"
                addA(idx // 2, a)

    def P(Mc):
        return {d: mobius(Mc // d) for d in divisors(Mc) if mobius(Mc // d)}

    if ap % 2 == 0 or M % 16 == 0:
        via_Z(P(M))
    elif M % 8 != 0:
        half = Q(1, 2)
        shifted = {(Q(s, M) + half) % 1 for s in range(1, M + 1) if gcd(s, M) == 1}
        plain = {Q(s, M) % 1 for s in range(1, M + 1) if gcd(s, M) == 1}
        coefs = dict(P(M))
        if shifted != plain:
            Mp = 2 * M if M % 2 else (M if M % 4 == 0 else M // 2)
            for d, a in P(Mp).items():
                coefs[d] = coefs.get(d, 0) + a
        via_Z(coefs)
    else:  # M = 8 M', M' odd: orbit = g_e * P_{M'}, e in {g, g'}; the caller tries both
        raise NotImplementedError
    return res


def decompose_8(M, n, eps):
    """M = 8 M' with M' odd: orbit is g_eps * P_{M'} (g = {1/8,7/8}, g' = {3/8,5/8})."""
    Mp = M // 8
    res = {}
    for d in divisors(Mp):
        mu = mobius(Mp // d)
        if not mu:
            continue
        # g_eps * Z_d = nu_d(g^[d]) with g^[d] = g_eps if d = +-1 mod 8, else the other one
        use_g = (eps == "g") == (d % 8 in (1, 7))
        nd = n * d  # odd
        if use_g:
            res[("G", (nd + 1) // 2)] = res.get(("G", (nd + 1) // 2), 0) + mu
        else:  # g' = P_8 - g
            res[("A", 4 * nd)] = res.get(("A", 4 * nd), 0) + mu
            res[("A", 2 * nd)] = res.get(("A", 2 * nd), 0) - mu
            res[("G", (nd + 1) // 2)] = res.get(("G", (nd + 1) // 2), 0) - mu
    return res


def vec_of_decomposition(dec):
    out = {}
    for (kind, idx), c in dec.items():
        if c:
            out = add(out, dec_vec_A(idx) if kind == "A" else dec_vec_G(idx), c)
    return out


def section_roots(quick):
    print("== 2. Prefix-level relations = multiplicative relations of u-root multisets (u = 2^(-1/2))")
    # (a) the polynomial model agrees with the root model for the new degree-4 source
    f24 = [4, -4, 2, -2, 1]
    p = newton(f24, 40)
    for j in range(1, 41):
        s = sum((2 ** 0.5 * cmath.exp(2j * cmath.pi * k / 24)) ** j for k in (1, 7, 17, 23)).real
        assert abs(s - p[j]) < 1e-6 * max(1, abs(p[j])), (j, s, p[j])
    print("   f24 = X^4-2X^3+2X^2-4X+4 has roots sqrt2*zeta_24^k, k in {1,7,17,23} (power sums match through j=40)")
    n1 = Source("N1", f24, 1, 1)
    full = {("A", 2): 1, ("A", 4): -1, ("G", 1): 1, ("G", 2): 1}
    comb = [(A(2), 1), (A(4), -1), (G(1), 1), (G(2), 1)]
    top = 120 if quick else 400
    for v in range(1, top + 1):
        assert n1.cell(v) == combo_cell(comb, v), v
    assert vec_of_decomposition(full) == nu(1, {Q(k, 24): 1 for k in (1, 7, 17, 23)})
    print("   prefix identity N1 = A2 - A4 + G1 + G2 holds at every half-integer cutoff through", top // 2,
          "and as multisets of roots")
    # (b) completeness: every balanced orbit source decomposes into A_k and G_t
    count = 0
    sign_twins = 0
    maxM = 120 if quick else 240
    for M in range(1, maxM + 1):
        if M > 48 and M % 8:
            continue
        for ap in (0, 1, 2, 3):
            for t in range(1, 5):
                n = 2 * t - ap
                if n < 1:
                    continue
                target = nu(n, {th: 1 for th in orbit(M, ap)})
                if ap % 2 == 1 and M % 8 == 0 and M % 16:
                    hits = [e for e in ("g", "gp") if vec_of_decomposition(decompose_8(M, n, e)) == target]
                    assert len(hits) == 1, (M, ap, n, hits)
                    twin = nu(n, {(th + Q(1, 2)) % 1: 1 for th in orbit(M, ap)})
                    other = "gp" if hits[0] == "g" else "g"
                    assert vec_of_decomposition(decompose_8(M, n, other)) == twin
                    sign_twins += 1
                else:
                    assert vec_of_decomposition(decompose(M, ap, n)) == target, (M, ap, n)
                count += 1
    print("   completeness: %d orbit sources (zeta_M, M<=%d, 2^(ap/2), t<=4) are integer combinations of A_k, G_t" % (count, maxM))
    print("   exceptional-conductor sign twins checked:", sign_twins)
    # (c) independence of the elementary sources A_k, G_t at the prefix level
    vecs = [dec_vec_A(k) for k in range(1, 13)] + [dec_vec_G(t) for t in range(1, 13)]
    keys = sorted({k for v in vecs for k in v})
    rows = [[v.get(k, 0) for k in keys] for v in vecs]
    assert rank_Q(rows) == len(vecs)
    print("   the 12 real sources A_1..A_12 and 12 Gaussian sources G_1..G_12 are linearly independent (rank %d)" % len(vecs))


def rank_Q(rows):
    rows = [[Q(x) for x in r] for r in rows]
    rank, ncols = 0, len(rows[0])
    for c in range(ncols):
        piv = next((i for i in range(rank, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pr = rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i][c]:
                m = rows[i][c] / pr[c]
                rows[i] = [a - m * b for a, b in zip(rows[i], pr)]
        rank += 1
    return rank


# ----------------------------------------------------------------------------------
# Section 3. Balance of an algebraic trace source and the 2-adic / precision conservation law
# ----------------------------------------------------------------------------------


def newton_polygon_min_valuation(f):
    """Smallest 2-adic valuation of a root of f (Newton polygon, exact)."""
    pts = [(k, v2(c)) for k, c in enumerate(f) if c]
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x2) >= (pt[1] - y2) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    slopes_ = [Q(y2 - y1, x2 - x1) for (x1, y1), (x2, y2) in zip(hull, hull[1:])]
    return -max(slopes_)


def complex_roots(f, iters=400):
    d = len(f) - 1
    roots = [(0.4 + 0.9j) ** k * (1 + max(abs(c) for c in f)) for k in range(d)]
    for _ in range(iters):
        new = []
        for i, r in enumerate(roots):
            den = 1
            for j, s in enumerate(roots):
                if i != j:
                    den *= r - s
            new.append(r - sum(c * r ** k for k, c in enumerate(f)) / den)
        roots = new
    return roots


def slopes(f):
    roots = complex_roots(f)
    A_ = max(log2(abs(r)) for r in roots)
    d = len(f) - 1
    mu = newton_polygon_min_valuation(f)
    return mu, Q(v2(f[0]), d), log2(abs(f[0])) / d, A_, roots


def section_balance(quick):
    print("== 3. Balance and the exponent gap")
    examples = [
        ("Gaussian 1+i", [2, -2, 1], 2),
        ("sqrt2*zeta_24 (degree 4)", [4, -4, 2, -2, 1], 2),
        ("2*zeta_6", [4, -2, 1], 2),
        ("sqrt2", [-2, 0, 1], 2),
        ("1+sqrt(-7)", [8, -2, 1], 3),
        ("1+sqrt2", [-1, -2, 1], 2),
        ("1+zeta_8", [2, -4, 6, -4, 1], 3),
    ]
    rows = []
    for name, f, t in examples:
        mu, aod, logc, A_, roots = slopes(f)
        assert float(mu) <= float(aod) + 1e-9 and float(aod) <= logc + 1e-9 and logc <= A_ + 1e-7, name
        balanced = float(mu) > A_ - 1e-9
        if balanced:
            # Kronecker: alpha^d / 2^a is a root of unity; all roots have modulus 2^(a/d)
            assert all(abs(abs(r) - 2 ** float(aod)) < 1e-6 for r in roots)
            assert abs(f[0]) == 2 ** v2(f[0])
        p = newton(f, 80)
        nz = [j for j in range(1, 81) if p[j]]
        odd_part = max(abs(p[j]) >> v2(p[j]) for j in nz)
        if balanced:
            assert all(v2(p[j]) >= mu * j for j in nz)
            assert odd_part <= 4
        kappa = (t - A_) / (t - float(mu))
        rows.append((name, mu, A_, balanced, odd_part, kappa))
        print("   %-26s t=%d  mu=%-5s A=%.4f  balanced=%-5s max odd part of p_j (j<=80) = %-12d kappa=%.4f"
              % (name, t, mu, A_, balanced, odd_part, kappa))
    # exact conservation law on the unbalanced source alpha = 1 + sqrt(-7), t = 3
    f, t = [8, -2, 1], 3
    mu, A_ = Q(1), 1.5
    p = newton(f, 400)
    assert all(p[j] % 2 ** j == 0 and (p[j] >> j) % 2 == 1 for j in range(1, 400) if p[j])
    print("   alpha=1+sqrt(-7): p_j = 2^j * (odd) for all j<=399, so e(j)=2j exactly, mu=1, A=3/2")
    print("   N    exact-exponent cutoff J=N/2: bits lost S (kappa predicts N/4)   analytic cutoff J=2N/3: 2-adic denominator bits E (predicts N/3)")
    for N in (40, 90, 150) if quick else (40, 90, 150, 300):
        prec = int(0.31 * N) + 80
        L2 = dec_log(2, prec)
        value = 3 * L2 - dec_log(7, prec)

        def measure(J):
            Y = 2 ** N * sum((Q(p[j], j * 8 ** j) for j in range(1, J + 1)), Q())
            getcontext().prec = prec
            err = abs(Decimal(2 ** N) * value - Decimal(Y.numerator) / Decimal(Y.denominator))
            return v2(Y.denominator), float(err.ln() / L2)

        _, S_exact = measure(N // 2)
        E_an, S_an = measure(-(-2 * N // 3))
        assert N / 4 - 2 * log2(N) - 2 <= S_exact <= N / 4 + 1, (N, S_exact)
        assert abs(E_an - N / 3) <= log2(N) + 3, (N, E_an)
        assert S_an < 0
        print("   %3d   S = %7.2f                                                      E = %d  (analytic cutoff has error 2^%.1f)"
              % (N, S_exact, E_an, S_an))
    return rows


# ----------------------------------------------------------------------------------
# Section 4. Frobenius trace congruence and correct truncation
# ----------------------------------------------------------------------------------


def shifted_prefix(coef, N, mult=1):
    """2^N * sum c_i S_i at the homogeneous cutoff n*j*mult <= 2N, using integer comparisons only."""
    total = Q()
    for s, c in coef:
        total += c * s.prefix((2 * N) // (s.n * mult))
    return total * 2 ** N


def frobenius_check(coef, N, wrong_floor=False):
    """Return (support primes, mismatches, floor-first mismatches) for the test p*Y = 2^N S(N/p) mod p."""
    Y = shifted_prefix(coef, N)
    jmax = max((2 * N) // s.n for s, _ in coef)
    support, bad, bad_floor = [], 0, 0
    for p in primes_upto(jmax):
        if p == 2 or p * p <= jmax:
            continue
        if any(c.denominator % p == 0 for _, c in coef):
            continue
        shadow = shifted_prefix(coef, N, mult=p)
        diff = p * Y - shadow
        assert diff.denominator % p and diff.numerator % p == 0, (N, p)
        pred = shadow.numerator % p != 0
        actual = Y.denominator % p == 0
        bad += pred != actual
        if actual:
            support.append(p)
        if wrong_floor:  # round the real cutoff N/p down before using it
            fl = Q()
            for s, c in coef:
                fl += c * s.prefix((2 * (N // p)) // s.n)
            fl *= 2 ** N
            bad_floor += (fl.numerator % p != 0) != actual
    return support, bad, bad_floor


def section_frobenius(quick):
    print("== 4. Frobenius congruence for traces and correct truncation")
    polys = [[2, -2, 1], [4, -4, 2, -2, 1], [8, -2, 1], [-1, -2, 1], [3, 1, 0, 5, 1], [7, -3, 0, 2, 1, 1]]
    checks = 0
    for f in polys:
        p_ = newton(f, 20 * 47)
        for p in primes_upto(47):
            for l in range(1, 21):
                assert (p_[p * l] - p_[l]) % p == 0
                checks += 1
    print("   Tr(alpha^(p l)) = Tr(alpha^l) mod p for %d (f, p, l) triples, six polynomials incl. degree 5" % checks)
    n1 = Source("N1", [4, -4, 2, -2, 1], 1, 1)
    n2 = Source("N2", [4, -4, 2, -2, 1], 2, 3)
    q7a = Source("Q7analytic", [8, -2, 1], 3, 3)
    q7e = Source("Q7exact", [8, -2, 1], 3, 4)
    cases = {
        "A1": [(A(1), Q(1))],
        "G3": [(G(3), Q(1))],
        "N1 (degree 4, t=1)": [(n1, Q(1))],
        "N2 - 3 G2 (mixed)": [(n2, Q(1)), (G(2), Q(-3))],
        "Q7 analytic cutoff n=3": [(q7a, Q(1))],
        "Q7 exact-exponent cutoff n=4": [(q7e, Q(1))],
    }
    Ns = (61, 100) if quick else (61, 100, 157, 233)
    for name, coef in cases.items():
        tot = tot_bad = tot_floor = 0
        for N in Ns:
            sup, bad, bf = frobenius_check(coef, N, wrong_floor=True)
            tot += len(sup)
            tot_bad += bad
            tot_floor += bf
        assert tot_bad == 0
        print("   %-30s support primes tested: %4d, congruence/support mismatches: %d, floor-first mismatches: %d"
              % (name, tot, tot_bad, tot_floor))
        if name.startswith("G3"):
            assert tot_floor > 0
    N, p = 13, 5
    s = G(3)
    assert (2 * N) // (s.n * p) == 1 and (2 * (N // p)) // s.n == 0
    print("   worked case G3, N=13, p=5: homogeneous cutoff keeps j=1 (5*1*5 <= 26); rounding 13/5 down loses it")
    s = G(3)
    for N in (60, 120):
        prec = N // 3 + 60
        value = 5 * dec_log(2, prec) - 2 * dec_log(5, prec)
        good = shifted_prefix([(s, Q(1))], N)
        crude = 2 ** N * s.prefix(N // 3)
        getcontext().prec = prec
        eg = abs(Decimal(2 ** N) * value - Decimal(good.numerator) / Decimal(good.denominator))
        ec = abs(Decimal(2 ** N) * value - Decimal(crude.numerator) / Decimal(crude.denominator))
        assert eg < 1 and ec > eg * Decimal(2 ** (N // 8))
        print("   G3 at N=%d: |2^N value - Y| = %.2e with n*j<=2N; %.2e with the crude rule t*j<=N" % (N, eg, ec))


# ----------------------------------------------------------------------------------
# Section 5. Weighted height against denominator rate
# ----------------------------------------------------------------------------------

BASIS = None
_CELLS = {}


def basis():
    global BASIS
    if BASIS is None:
        BASIS = [A(1), A(2), A(3), A(4), A(6), G(1), G(2), G(3)]
    return BASIS


def cell_of(s, v):
    key = (s.name, v)
    if key not in _CELLS:
        _CELLS[key] = s.cell(v)
    return _CELLS[key]


def normal_coefficients(a, u, b, c):
    """Coefficients (A1,A2,A3,A4,A6,G1,G2,G3) of every rational formula for log 2 in this alphabet
    (valuations at 2,3,5,7 solved exactly; checked by `check_limit`)."""
    a6 = a + u + b + c - 1
    a4 = -b - 2 * c
    return (a, -a4 - 2 * a6, -a6, a4, a6, u, b, c)


def check_limit(coefs):
    tot = {}
    for s, c in zip(basis(), coefs):
        for p, e in s.infinite_valuation().items():
            tot[p] = tot.get(p, 0) + c * e
    tot = {p: e for p, e in tot.items() if e}
    assert tot == {2: 1}, tot


def weighted_height(coefs):
    """C = sum |real coefficients| + 2 sum |Gaussian coefficients| (weight = number of conjugates)."""
    return sum(abs(c) * (1 if s.f == [-1, 1] else s.d) for s, c in zip(basis(), coefs))


def tail_cutoff(C):
    """Least integer X with 2^X > 4C / 0.69, so S(x) > 0 for x >= X (ln 2 > 0.69, tail <= 4C 2^-x)."""
    X = 1
    while 2 ** X * 69 <= 400 * C:
        X += 1
    return X


def rate_exact(coefs):
    """Exact rate sum over {x: S(x) != 0} of dx/x^2, with the certified tail beyond X."""
    C = weighted_height(coefs)
    X = tail_cutoff(C)
    rate = Q(1, X)
    zero_cells = []
    for v in range(1, 2 * X):
        val = sum((c * cell_of(s, v) for s, c in zip(basis(), coefs)), Q())
        if val:
            rate += Q(2, v * (v + 1))
        else:
            zero_cells.append(v)
    return rate, C, X, zero_cells


def section_height(quick):
    print("== 5. Weighted height against denominator rate")
    ln2 = log(2)
    # reproduce the Phase 14 values with an independent implementation
    known = {(0, 0, 0, -5): Q(5, 12), (0, 0, 0, -2): Q(13, 30), (0, 0, -2, -3): Q(29, 60)}
    for par, want in known.items():
        co = normal_coefficients(*par)
        check_limit(co)
        rate, C, X, zc = rate_exact(co)
        assert rate == want, (par, rate)
        print("   (a,u,b,c)=%-14s coefficients %-26s height C=%2d rate %s" % (par, co, C, rate))
    # the tail bound |S_i(x) - V_i| <= w_i * 4 * 2^-x for every basis source (w = 1 real, 2 Gaussian)
    getcontext().prec = 60
    for s in basis():
        V = sum(e * dec_log(pp, 60) for pp, e in s.infinite_valuation().items())
        w = 1 if s.f == [-1, 1] else 2
        for v in range(0, 61):
            diff = abs(Decimal(s.cell(v).numerator) / Decimal(s.cell(v).denominator) - V)
            assert diff <= Decimal(w * 4) * Decimal(2) ** (-Decimal(v) / 2), (s.name, v)
    print("   tail bound |S_i(x) - V_i| <= 4 w_i 2^-x verified at every half-integer cutoff through x = 30 for the eight basis sources")
    for par in known:
        co = normal_coefficients(*par)
        rate, C, X, zc = rate_exact(co)
        for v in range(2 * X, 90):
            assert sum((c * cell_of(s, v) for s, c in zip(basis(), co)), Q()) != 0
    R = 3 if quick else 5
    best = {}
    count = 0
    min_rate = Q(2)
    for u in (0, 1, -1):
        for a, b, c in product(range(-R, R + 1), repeat=3):
            co = normal_coefficients(a, u, b, c)
            rate, C, X, zc = rate_exact(co)
            count += 1
            # Theorem: rate >= 1/X, and every zero cell v satisfies 2^(v/2) <= 4C/ln 2
            assert rate >= Q(1, X)
            for v in zc:
                assert 2 ** (v / 2) <= 4 * C / ln2 + 1e-9, (a, u, b, c, v)
            if u != 0:
                assert rate >= 1
            if C not in best or rate < best[C][0]:
                best[C] = (rate, (a, u, b, c))
            min_rate = min(min_rate, rate)
    assert min_rate >= Q(5, 12) and (R < 5 or min_rate == Q(5, 12)), min_rate
    print("   enumerated %d integer formulas, |a|,|b|,|c| <= %d, |u| <= 1: least rate %s (Phase 14 global optimum 5/12)"
          % (count, R, min_rate))
    print("   height C | least rate found | parameters | height-obstruction lower bound 1/X(C)")
    frontier, cur = [], Q(3)
    for C in sorted(best):
        if best[C][0] < cur:
            cur = best[C][0]
            frontier.append((C, cur, best[C][1]))
    for C, r, par in frontier:
        print("   %9s | %-16s | %-14s | %s" % (C, r, par, Q(1, tail_cutoff(C))))
    # killing a band costs height exponentially: first nonzero cell index against C
    print("   zero cells force C >= (ln2/4) 2^(v/2): e.g. a vanishing cell at v=7 (x=3.5) needs C >= %.2f" % (ln2 / 4 * 2 ** 3.5))
    return frontier


# ----------------------------------------------------------------------------------
# Section 6. Candidate sources: actual tests of support, rate, precision and future window
# ----------------------------------------------------------------------------------


def atlas_error(Y, N, multiple):
    """Enclose the unwrapped error and certify the maximal shift within 2^-8."""
    bits = 4 * N + 80
    while True:
        left = int(log_bits(bits), 2)
        unit = Q(multiple, 1 << (bits - N))
        lo, hi = left * unit - Y, (left + 1) * unit - Y
        upper = max(abs(lo), abs(hi))
        lower = max(lo, -hi, 0)
        if lower > Q(1, 256):
            return upper, None
        if upper <= Q(1, 256):
            window = 0
            while upper * (1 << (window + 1)) <= Q(1, 256):
                window += 1
            if lower * (1 << (window + 1)) > Q(1, 256):
                return upper, window
        bits *= 2


def lg2(d):
    getcontext().prec = 60
    return float(d.ln() / Decimal(2).ln())


def support_primes(Y, bound):
    q = Y.denominator >> v2(Y.denominator)
    return [p for p in primes_upto(bound) if p > 2 and q % p == 0]


def future_window_mass(coef, N, support):
    """Compare the actual primary components, including prime powers, up to N shifts."""
    base = shifted_prefix(coef, N)
    windows = dict.fromkeys(support, N)
    for j in range(1, N + 1):
        difference = shifted_prefix(coef, N + j) - (1 << j) * base
        for p in support:
            if windows[p] == N and difference.denominator % p == 0:
                windows[p] = j - 1
    wins = windows.items()
    total = sum(log(p) for p, _ in wins)
    prof = {}
    for frac in (Q(1, 16), Q(1, 8), Q(1, 4)):
        prof[frac] = sum(log(p) for p, w in wins if w >= frac * N) / total
    return min(w for _, w in wins), prof


def beukers_pade(n):
    """Integers/rationals with I_n = int_0^1 x^n(1-x)^n/(1+x)^(n+1) dx = c_n log 2 - r_n (exact)."""
    # polynomial (y-1)^n (2-y)^n in y = 1 + x
    poly = [1]
    for factor in [[-1, 1]] * n + [[2, -1]] * n:
        new = [0] * (len(poly) + 1)
        for i, a in enumerate(poly):
            new[i] += a * factor[0]
            new[i + 1] += a * factor[1]
        poly = new
    cn = poly[n]
    # int y^(k-n-1) dy over [1,2] = (2^(k-n) - 1)/(k-n)
    r = Q()
    for k, ck in enumerate(poly):
        if k != n and ck:
            e = k - n
            r -= ck * (Q(2) ** e - 1) / e
    return cn, r


def simpson_beukers(n, steps=4000):
    h = Decimal(1) / steps
    f = lambda x: (x * (1 - x)) ** n / (1 + x) ** (n + 1)
    s = f(Decimal(0)) + f(Decimal(1))
    for i in range(1, steps):
        s += (4 if i % 2 else 2) * f(i * h)
    return s * h / 3


def solve_linear(M, rhs=None):
    """Gauss-Jordan over Fractions; returns solution of M x = rhs or None if singular (square)."""
    n = len(M)
    A_ = [list(map(Q, row)) + [Q(rhs[i])] for i, row in enumerate(M)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A_[i][c]), None)
        if piv is None:
            return None
        A_[c], A_[piv] = A_[piv], A_[c]
        pv = A_[c][c]
        A_[c] = [x / pv for x in A_[c]]
        for i in range(n):
            if i != c and A_[i][c]:
                m = A_[i][c]
                A_[i] = [a - m * b for a, b in zip(A_[i], A_[c])]
    return [A_[i][n] for i in range(n)]


def nullspace_vector(M, ncols):
    """One nonzero kernel vector of the (ncols-1) x ncols matrix M over Q (assumes the kernel is a line)."""
    rows = [[Q(x) for x in r] for r in M]
    pivcols, r_ = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r_, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r_], rows[piv] = rows[piv], rows[r_]
        pv = rows[r_][c]
        rows[r_] = [x / pv for x in rows[r_]]
        for i in range(len(rows)):
            if i != r_ and rows[i][c]:
                m = rows[i][c]
                rows[i] = [a - m * b for a, b in zip(rows[i], rows[r_])]
        pivcols.append(c)
        r_ += 1
    free = [c for c in range(ncols) if c not in pivcols]
    assert len(free) == 1, "kernel is not a line"
    f = free[0]
    x = [Q(0)] * ncols
    x[f] = Q(1)
    for i, c in enumerate(pivcols):
        x[c] = -rows[i][f]
    return x


def diag_pade_trace(f, n):
    """[n/n] Pade approximant of g(z) = -sum p_m z^m / m (= log of the reversed polynomial); (P, Q) coefficient lists."""
    p = newton(f, 2 * n + 1)
    g = [Q(0)] + [Q(-p[m], m) for m in range(1, 2 * n + 2)]
    M = [[g[m - i] if m - i >= 1 else Q(0) for i in range(1, n + 1)] for m in range(n + 1, 2 * n + 1)]
    rhs = [-g[m] for m in range(n + 1, 2 * n + 1)]
    q = solve_linear(M, rhs)
    if q is None:
        return None
    qpoly = [Q(1)] + q
    ppoly = [sum((qpoly[i] * g[m - i] for i in range(0, m + 1) if m - i >= 0), Q()) for m in range(0, n + 1)]
    # defining property: Q g - P = O(z^(2n+1))
    for m in range(0, 2 * n + 1):
        coeff = sum((qpoly[i] * g[m - i] for i in range(0, n + 1) if 0 <= m - i), Q())
        assert coeff == (ppoly[m] if m <= n else 0), (n, m)
    return ppoly, qpoly


def hermite_pade_logs(n):
    """Type I Hermite-Pade: polynomials Q0,Q1,Q2 of degree <= n with Q0 + Q1 log(1-z) + Q2 log(1-z/2) = O(z^(3n+2)).
    Returns the integer form (a0, aL, a3) with a0 + aL log2 + a3 log3 = D * (value at z = 1/2), and the order check."""
    f1 = lambda m: Q(-1, m)
    f2 = lambda m: Q(-1, m * 2 ** m)
    ncols = 3 * (n + 1)
    M = []
    for k in range(3 * n + 2):
        row = []
        for i in range(n + 1):
            row.append(Q(1) if i == k else Q(0))
        for i in range(n + 1):
            row.append(f1(k - i) if k - i >= 1 else Q(0))
        for i in range(n + 1):
            row.append(f2(k - i) if k - i >= 1 else Q(0))
        M.append(row)
    x = nullspace_vector(M, ncols)
    den = 1
    for c in x:
        den = den * c.denominator // gcd(den, c.denominator)
    x = [c * den for c in x]
    assert all(c.denominator == 1 for c in x)
    z0 = Q(1, 2)
    Qv = [sum((x[j * (n + 1) + i] * z0 ** i for i in range(n + 1)), Q()) for j in range(3)]
    D = 1
    for c in Qv:
        D = D * c.denominator // gcd(D, c.denominator)
    a0, aL, a3 = Qv[0] * D, (-Qv[1] - 2 * Qv[2]) * D, Qv[2] * D
    assert all(c.denominator == 1 for c in (a0, aL, a3))
    g = gcd(gcd(int(a0), int(aL)), int(a3))
    return int(a0) // g, int(aL) // g, int(a3) // g


def section_atlas(quick):
    print("== 6. Candidate sources: support, rate, precision, future window (shift N, error of 2^N x)")
    Ns = (96,) if quick else (96, 192)
    n1 = Source("N1", [4, -4, 2, -2, 1], 1, 1)
    minimizer = [(A(2), Q(2)), (A(3), Q(6)), (A(4), Q(10)), (A(6), Q(-6)), (G(3), Q(-5))]
    hdr = "   %-34s %5s %9s %8s %8s %9s %8s %8s %8s %8s"
    print(hdr % ("source", "N", "log q/N", "2-adic", "support", "log2 err", "window", "min W_p", "m(N/16)", "m(N/4)"))
    atlas = []

    def emit(name, N, Y, coef=None, multiple=1, support_bound=None):
        err, window = atlas_error(Y, N, multiple)
        q = Y.denominator
        two = v2(q)
        sup = support_primes(Y, support_bound or 4 * N)
        W = "none" if window is None else str(window)
        log_error = log2(err)
        mw, m16, m4 = "", "", ""
        if coef is not None:
            frob_sup, bad, _ = frobenius_check(coef, N)
            assert bad == 0 and set(frob_sup) <= set(sup)
            mw, prof = future_window_mass(coef, N, sup)
            m16, m4 = "%.2f" % prof[Q(1, 16)], "%.2f" % prof[Q(1, 4)]
        rate = log(q) / N
        print(hdr % (name, N, "%.4f" % rate, two, len(sup), "%.1f" % log_error, W, mw, m16, m4))
        atlas.append((name, N, rate, two, len(sup), log_error, W, mw))
        return err

    for N in Ns:
        emit("Taylor A1", N, shifted_prefix([(A(1), Q(1))], N), [(A(1), Q(1))])
        mn = shifted_prefix(minimizer, N)
        emit("Gaussian minimizer (rate 5/12)", N, mn, minimizer)
        comb = [(G(1), Q(1)), (G(2), Q(1)), (A(2), Q(1)), (A(4), Q(-1))]
        assert shifted_prefix([(n1, Q(1))], N) == shifted_prefix(comb, N)
        emit("degree-4 trace N1 (=G1+G2+A2-A4)", N, shifted_prefix([(n1, Q(1))], N),
             [(n1, Q(1))], multiple=2)
        # diagonal beta correction
        y = sum((Q(2 ** (N - r), r) for r in range(1, N + 1)), Q())
        y += sum((Q((-1) ** h * factorial(N) * factorial(h), factorial(N + h + 1)) for h in range(N)), Q())
        err = emit("beta diagonal (Paper V)", N, y)
        assert err <= Q(factorial(N) ** 2, factorial(2 * N + 1))
    # Beukers-Pade for log 2: exact identity I_n = c_n log 2 - r_n against an independent quadrature
    for n in range(1, 7):
        cn, r = beukers_pade(n)
        getcontext().prec = 80
        In = cn * dec_log(2, 80) - Decimal(r.numerator) / Decimal(r.denominator)
        assert In > 0 and abs(In - simpson_beukers(n)) < Decimal("1e-12"), n
    for n in (13,) if quick else (13, 26):
        cn, r = beukers_pade(n)
        getcontext().prec = 80
        L = dec_log(2, 80)
        In = cn * L - Decimal(r.numerator) / Decimal(r.denominator)
        eps = In / cn
        # largest N with 2^N eps <= 1/N
        N = 1
        while Decimal(2) ** (N + 1) * eps * (N + 1) <= 1:
            N += 1
        emit("Beukers-Pade n=%d" % n, N, Q(2) ** N * r / cn, support_bound=3 * N)
    # Pade of the Gaussian trace function at z = 1/2 (value -log 2)
    for n in (14,) if quick else (14, 28):
        res = None
        for nn in range(n, n + 4):
            res = diag_pade_trace([2, -2, 1], nn)
            if res is not None:
                n = nn
                break
        P_, Q_ = res
        z0 = Q(1, 2)
        R = sum((c * z0 ** i for i, c in enumerate(P_)), Q()) / sum((c * z0 ** i for i, c in enumerate(Q_)), Q())
        getcontext().prec = 80
        eps = abs(dec_log(2, 80) + Decimal(R.numerator) / Decimal(R.denominator))
        N = 1
        while Decimal(2) ** (N + 1) * eps * (N + 1) <= 1:
            N += 1
        emit("Pade of Gaussian trace n=%d" % n, N, -Q(2) ** N * R, support_bound=3 * N)
    # Hermite-Pade: a joint linear form in 1, log 2, log 3
    print("   Hermite-Pade type I for (log(1-z), log(1-z/2)) at z=1/2: form a0 + aL log2 + a3 log3")
    print("     n   log2 H    -log2|form|   P/log2 H      a3 != 0")
    for n in range(1, 7 if quick else 13):
        a0, aL, a3 = hermite_pade_logs(n)
        getcontext().prec = 400
        V = a0 + aL * dec_log(2, 400) + a3 * dec_log(3, 400)
        H = max(abs(a0), abs(aL), abs(a3))
        assert V != 0 and abs(V) < Decimal(1)
        P = -lg2(abs(V))
        print("   %3d   %7.1f    %9.1f    %8.4f       %s" % (n, log2(H), P, P / log2(H), a3 != 0))
        assert a3 != 0
    return atlas


def main(argv):
    quick = "--quick" in argv
    only = [a for a in argv if a.startswith("--only=")]
    sections = [("bezout", section_bezout), ("roots", section_roots), ("balance", section_balance),
                ("frobenius", section_frobenius), ("height", section_height), ("atlas", section_atlas)]
    for name, fn in sections:
        if only and name not in only[0][7:].split(","):
            continue
        fn(quick)
    print("All Phase 15 arithmetic checks passed.")


if __name__ == "__main__":
    main(sys.argv[1:])
