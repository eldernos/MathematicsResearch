"""Phase 15, track C: an exact affine-lift experiment for the shifted prefixes of ln 2.

Run `python3 -B scripts/phase15_affine.py` (about five seconds; `--quick` is shorter). Standard library only.
The statements, scope and tables are in notes/phase15/affine-experiment.md.

Setting. At a common shift N three genuinely different rational approximants of X = 2^N ln 2 are built:

  T  Taylor        sum_{j<=J} 2^(N-j)/j                      (ln 2 = -log(1-1/2))
  G  Gaussian      sum_{j<=J} 2^N Tr((1+i)^j)/(j 2^j)         (ln 2 = -log|1-(1+i)/2|^2)
  B  beta/diagonal 2^(N-n) y_n,  y_n = sum_{r<=n} 2^(n-r)/r + sum_{h<n} (-1)^h n! h!/(n+h+1)!

Each depth (J, J, n) is the least one whose *certified* error is at most 2^-L. The certificate is an exact
rational comparison against a proven dyadic enclosure lo/2^P <= ln 2 <= hi/2^P obtained from the
independent series ln 2 = 2 artanh(1/3) with directed integer rounding. An integer affine combination
sum c_i R_i, sum c_i = 1, has |sum c_i R_i - X| <= sum |c_i| eps_i (triangle weighting; Lean:
NormalityChecker.AffineDenominator.combined_error). An odd integer D divides the denominator of
sum c_i R_i away exactly when D | sum c_i A_i, where R_i = A_i/M, and by Lean's feasible_iff_gcd that is
solvable iff gcd(D, A_i - A_0) | A_0. The search below solves the congruence lattice exactly (unimodular
reduction, LLL, bounded enumeration around the rounded least-squares coordinates) and uses exact Fractions for every certificate.
"""

import sys
from fractions import Fraction as Q
from math import gcd, log2, isqrt, factorial
from itertools import product
from decimal import Decimal, getcontext
import random

# ----------------------------------------------------------------------------------
# Elementary helpers (copied in small form from scripts/phase15_arithmetic.py)
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


def odd_part(n):
    return n >> v2(n)


def smooth_factor(n, primes):
    """{p: e} of n over the given primes; asserts that nothing is left over."""
    out = {}
    for p in primes:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            out[p] = e
        if n == 1:
            break
    assert n == 1, "denominator not smooth over the prime table"
    return out


def egcd(a, b):
    """(g, s, t) with g = gcd(|a|,|b|) >= 0 and s a + t b = g."""
    s0, t0, s1, t1 = 1, 0, 0, 1
    x, y = a, b
    while y:
        q = x // y
        x, y = y, x - q * y
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    if x < 0:
        x, s0, t0 = -x, -s0, -t0
    return x, s0, t0


def flog2(x):
    """log2 of a positive Fraction (works far below float range)."""
    x = Q(x)
    return log2(x.numerator) - log2(x.denominator)


def window(eps, tol):
    """Largest j >= 0 with 2^j eps <= tol, or -1 if even j = 0 fails (eps, tol Fractions)."""
    if eps == 0:
        return 10 ** 9
    if eps > tol:
        return -1
    j = max(0, int(flog2(tol) - flog2(eps)) - 2)
    while eps * 2 ** (j + 1) <= tol:
        j += 1
    while j >= 0 and eps * 2 ** j > tol:
        j -= 1
    return j


# ----------------------------------------------------------------------------------
# 1. Proven binary enclosure of ln 2 and the three approximants
# ----------------------------------------------------------------------------------


def ln2_enclosure(P, guard=40):
    """Integers lo <= hi with lo/2^P <= ln 2 <= hi/2^P.

    ln 2 = 2 artanh(1/3) = sum_{k>=0} 2/((2k+1) 3^(2k+1)). With S = P + guard each term is rounded down for lo
    and up for hi; the tail from k = m is at most (9/4)/((2m+1) 3^(2m+1)) (geometric bound), rounded up."""
    S = P + guard
    lo = hi = 0
    k = 0
    while True:
        den = (2 * k + 1) * 3 ** (2 * k + 1)
        tail = -((-9 * (1 << S)) // (4 * den))  # ceil of 2^S * (9/4)/den, a bound on the tail from index k
        if tail <= 1 << guard // 2 and k > 5:
            hi += tail
            break
        t = 2 * (1 << S)
        lo += t // den
        hi += -((-t) // den)
        k += 1
    return lo >> guard, -((-hi) >> guard)


class Enclosure:
    def __init__(self, N, P):
        self.N, self.P = N, P
        lo, hi = ln2_enclosure(P)
        assert hi - lo <= 4
        self.lo, self.hi = Q(lo << N, 1 << P), Q(hi << N, 1 << P)  # 2^N lo/2^P and 2^N hi/2^P
        # independent sanity checks against Decimal and against the Taylor partial sums (both are lower bounds)
        getcontext().prec = int(P * 0.31) + 30
        d = Decimal(2).ln()
        assert Decimal(lo) / Decimal(2) ** P <= d <= Decimal(hi) / Decimal(2) ** P
        part = sum((Q(1, j << j) for j in range(1, 60)), Q())  # lower bound for ln 2 with tail below 2^-59
        assert part <= Q(hi, 1 << P) and Q(lo, 1 << P) <= part + Q(1, 1 << 59)

    def eps(self, R):
        """Certified bound for |R - 2^N ln 2| (exact rational)."""
        return max(abs(R - self.lo), abs(R - self.hi))


def taylor(N, J):
    return sum((Q(1 << N, j << j) if N >= 0 else Q(1, j << (j - N)) for j in range(1, J + 1)), Q())


def gaussian_traces(J):
    """p_j = Tr((1+i)^j) = 2 Re((1+i)^j) for j = 1..J."""
    a, b, out = 1, 1, [0]
    for _ in range(J):
        out.append(2 * a)
        a, b = a - b, a + b
    return out


def gaussian(N, J, ps=None):
    ps = ps or gaussian_traces(J)
    return sum((Q(ps[j] << N, j << j) for j in range(1, J + 1)), Q())


def beta_y(n):
    y = sum((Q(1 << (n - r), r) for r in range(1, n + 1)), Q())
    y += sum((Q((-1) ** h * factorial(n) * factorial(h), factorial(n + h + 1)) for h in range(n)), Q())
    return y


def beta(N, n):
    return beta_y(n) * (Q(1 << (N - n)) if N >= n else Q(1, 1 << (n - N)))


class Approximants:
    """The three approximants at shift N with precision target 2^-L."""

    def __init__(self, N, L):
        self.N, self.L = N, L
        self.enc = Enclosure(N, N + L + 90)
        target = Q(1, 1 << L)
        J = 1
        while self.enc.eps(taylor(N, J)) > target:
            J += 1
        self.J_T = J
        ps = gaussian_traces(4 * (N + L) + 40)
        J = 1
        while self.enc.eps(gaussian(N, J, ps)) > target:
            J += 1
        self.J_G = J
        n = 1
        while self.enc.eps(beta(N, n)) > target:
            n += 1
        self.n_B = n
        self.names = ["T", "G", "B"]
        self.R = [taylor(N, self.J_T), gaussian(N, self.J_G, ps), beta(N, self.n_B)]
        self.eps = [self.enc.eps(r) for r in self.R]
        assert all(e <= target for e in self.eps)
        # consistency of the beta tail with the published bound n!^2/(2n+1)!
        mid = (self.enc.lo + self.enc.hi) / 2  # 2^N ln 2 up to the enclosure width
        assert abs(beta_y(n) - mid * Q(2) ** (n - N)) <= Q(factorial(n) ** 2, factorial(2 * n + 1)) * 2
        # common denominator and numerators; the odd part is what a lattice can remove
        M = 1
        for r in self.R:
            M = M * r.denominator // gcd(M, r.denominator)
        self.M, self.M_odd = M, odd_part(M)
        self.A = [int(r * M) for r in self.R]
        self.primes = primes_upto(8 * (N + L) + 100)

    def depth(self):
        return {"T": self.J_T, "G": self.J_G, "B": self.n_B}


# ----------------------------------------------------------------------------------
# 2. The affine congruence lattice: exact solution, reduction and bounded enumeration
# ----------------------------------------------------------------------------------


def coset_lattice(D, A):
    """Structure of {c in Z^k : sum c = 1, D | sum c_i A_i}, reference index 0.

    Put d_i = A_i - A_0 and x = (c_1..c_{k-1}); the condition is A_0 + sum x_i d_i = 0 mod D. Unimodular column
    operations send d to (g1, 0, .., 0); then g1 y_1 = -A_0 mod D. Returns None if infeasible, else
    (particular c, basis of the sum-zero sublattice as vectors in Z^k, index D/gg, gg) where gg = gcd(D, d_1..d_{k-1})
    and the index of the sublattice in the full sum-zero lattice Z^{k-1} is D/gg."""
    k = len(A)
    n = k - 1
    if D == 1:
        part = [1] + [0] * n
        gg, idx = 1, 1
        basis_x = [[int(i == j) for i in range(n)] for j in range(n)]
    else:
        a = [(A[i] - A[0]) % D for i in range(1, k)]
        cols = [[int(i == j) for i in range(n)] for j in range(n)]
        for j in range(1, n):
            if a[j] == 0:
                continue
            g, s, t = egcd(a[0], a[j])
            c0, cj = cols[0], cols[j]
            cols[0] = [s * x + t * y for x, y in zip(c0, cj)]
            cols[j] = [(a[j] // g) * x - (a[0] // g) * y for x, y in zip(c0, cj)]
            a[0], a[j] = g, 0
        g1 = a[0] if n else 0
        gg = gcd(g1, D)
        if A[0] % gg:
            return None
        m = D // gg
        y1 = 0 if m == 1 else ((-(A[0] // gg)) * pow((g1 // gg) % m, -1, m)) % m
        xp = [y1 * u for u in cols[0]] if n else []
        part = [1 - sum(xp)] + xp
        basis_x = [[m * u for u in cols[0]]] + cols[1:] if n else []
        idx = m
    basis = [[-sum(x)] + x for x in basis_x]
    for v in basis:
        assert sum(v) == 0 and sum(c * ai for c, ai in zip(v, A)) % D == 0
    assert sum(part) == 1 and sum(c * ai for c, ai in zip(part, A)) % D == 0
    return part, basis, idx, gg


def lll(rows, s2, delta=Q(3, 4)):
    """Integer LLL on the rows with the diagonal metric <x,y> = sum s2_i x_i y_i (exact)."""
    b = [r[:] for r in rows]
    n = len(b)
    if n <= 1:
        return b

    def dot(x, y):
        return sum(w * p * q for w, p, q in zip(s2, x, y))

    def gs():
        bs, mu, Bn = [], [[Q(0)] * n for _ in range(n)], []
        for i in range(n):
            v = [Q(x) for x in b[i]]
            for j in range(i):
                mu[i][j] = dot(b[i], bs[j]) / Bn[j]
                v = [p - mu[i][j] * q for p, q in zip(v, bs[j])]
            bs.append(v)
            Bn.append(dot(v, v))
        return mu, Bn

    mu, Bn = gs()
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                b[k] = [p - q * r for p, r in zip(b[k], b[j])]
                mu, Bn = gs()
        if Bn[k] >= (delta - mu[k][k - 1] ** 2) * Bn[k - 1]:
            k += 1
        else:
            b[k], b[k - 1] = b[k - 1], b[k]
            mu, Bn = gs()
            k = max(k - 1, 1)
    return b


def solve_small(G, rhs):
    n = len(G)
    M = [[Q(x) for x in row] + [Q(rhs[i])] for i, row in enumerate(G)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]
                M[i] = [p - f * q for p, q in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]


def search_coset(D, A, weights, R=3, mixing=2, box=None):
    """Minimise sum weights_i |c_i| (integer weights) over the coset of D, about a rounded real least-squares centre.

    The centre is obtained by solving the weighted real least-squares problem (minimise the weighted l2 distance from
    the particular solution to the lattice span), expressing the minimiser in the LLL-reduced basis and rounding
    each coordinate; the enumeration then takes +-R around those rounded coordinates. This is a bounded search with
    integer weights, not a global minimisation over Z^k; the exact weighted error is recomputed in rationals afterwards.

    `mixing` is the least number of nonzero coefficients (2 = genuine mixing, len(A) = every approximant used,
    0 = unrestricted). `box` optionally bounds max |c_i|.
    Returns (c, cost) or None. The enumeration is (2R+1)^(k-1) points around the weighted-l2 centre."""
    res = coset_lattice(D, A)
    if res is None:
        return None
    part, basis, idx, gg = res
    k = len(A)
    s2 = [w * w for w in weights]
    red = lll(basis, s2)
    n = len(red)
    dot = lambda x, y: sum(w * p * q for w, p, q in zip(s2, x, y))
    if n:
        lam = solve_small([[dot(u, v) for v in red] for u in red], [-dot(u, part) for u in red])
        centre = [round(x) for x in lam]
    else:
        centre = []
    best = None
    cost = lambda c: sum(w * abs(x) for w, x in zip(weights, c))
    for off in product(range(-R, R + 1), repeat=n):
        c = part[:]
        for o, cc, v in zip(off, centre, red):
            c = [x + (o + cc) * y for x, y in zip(c, v)]
        if sum(1 for x in c if x) < mixing:
            continue
        if box is not None and max(abs(x) for x in c) > box:
            continue
        key = (cost(c), sum(abs(x) for x in c))
        if best is None or key < best[0]:
            best = (key, c)
    if best is None:
        return None
    return best[1], best[0][0]


def brute_min_l1(D, A, B, mixing=2):
    """Exhaustive minimum of sum |c_i| over |c_i| <= B (k = 3 only), for cross-checking search_coset."""
    best = None
    for c1 in range(-B, B + 1):
        for c2 in range(-B, B + 1):
            c0 = 1 - c1 - c2
            if abs(c0) > B:
                continue
            c = [c0, c1, c2]
            if sum(1 for x in c if x) < mixing:
                continue
            if sum(x * a for x, a in zip(c, A)) % D == 0:
                l1 = sum(map(abs, c))
                if best is None or l1 < best[0]:
                    best = (l1, c)
    return best


# ----------------------------------------------------------------------------------
# 3. Reports for the lift experiment
# ----------------------------------------------------------------------------------


def evaluate(ap, c):
    R = sum((ci * r for ci, r in zip(c, ap.R)), Q())
    eps = sum((abs(ci) * e for ci, e in zip(c, ap.eps)), Q())
    actual = ap.enc.eps(R)  # |R - X| <= this, uses the enclosure only
    assert actual <= eps, "triangle bound violated"
    return R, eps, actual


def odd_support(R, primes):
    return smooth_factor(odd_part(R.denominator), primes)


def bits(n):
    return log2(n) if n > 0 else 0.0


def lattice_index_report(ap):
    A, M = ap.A, ap.M_odd
    d = [A[i] - A[0] for i in range(1, len(A))]
    g = M
    for x in d:
        g = gcd(g, x)
    return {"M_odd": M, "g": g, "index": M // g, "feasible_full": A[0] % g == 0,
            "diff_gcd_bits": bits(g), "k": len(A)}


def removable_primes(ap):
    """Odd primes p^e || M with gcd(p^e, A_i - A_0) | A_0 (Lean: feasible_iff_gcd, applied at modulus p^e)."""
    A = ap.A
    sup = smooth_factor(ap.M_odd, ap.primes)
    out = []
    for p, e in sup.items():
        pe = p ** e
        g = pe
        for i in range(1, len(A)):
            g = gcd(g, A[i] - A[0])
        if A[0] % g == 0:
            out.append((p, e))
    return sup, sorted(out, reverse=True)


def valuation_vec(n, primes):
    return smooth_factor(n, primes) if n > 1 else {}


def relative_divisors(q_ref, q_new, primes):
    """(removed, added): the divisor of q_ref that is lost and the divisor of q_new that is gained."""
    a, b = valuation_vec(q_ref, primes), valuation_vec(q_new, primes)
    rem = add = 1
    for p in set(a) | set(b):
        d = a.get(p, 0) - b.get(p, 0)
        if d > 0:
            rem *= p ** d
        elif d < 0:
            add *= p ** (-d)
    return rem, add


class View:
    """A sub-family of the approximants (indices into ap.names) with its own common denominator."""

    def __init__(self, ap, idx):
        self.ap, self.idx = ap, idx
        self.names = [ap.names[i] for i in idx]
        self.R = [ap.R[i] for i in idx]
        self.eps = [ap.eps[i] for i in idx]
        M = 1
        for r in self.R:
            M = M * r.denominator // gcd(M, r.denominator)
        self.M = M
        self.M_odd = odd_part(M)
        self.A = [int(r * M) for r in self.R]
        self.primes, self.enc = ap.primes, ap.enc

    def label(self):
        return "".join(self.names)


def ladder_rows(view, order, tol, R, q_ref):
    """Rows for D_t = product of the first t primes of `order` (each to its full power in the common denominator).
    Each row: best sampled genuine mixture by l1 norm, by certified error, and with every c_i nonzero."""
    k = len(view.A)
    sup, rem = removable_primes(view)
    remd = dict(rem)
    order = [p for p in order if p in remd]
    shift = view.ap.L + 40
    w_eps = [-((-e.numerator * (1 << shift)) // e.denominator) for e in view.eps]
    rows, D = [], 1
    for t in range(len(order) + 1):
        if t:
            D *= order[t - 1] ** remd[order[t - 1]]
        s1 = search_coset(D, view.A, [1] * k, R)
        s2 = search_coset(D, view.A, w_eps, R)
        if s1 is None or s2 is None:
            continue
        s3 = search_coset(D, view.A, w_eps, R, mixing=k) if k > 2 else None
        c1, c2 = s1[0], s2[0]
        _, e1, _ = evaluate(view, c1)
        R2, e2, a2 = evaluate(view, c2)
        for cc in (c1, c2):
            assert sum(cc) == 1 and sum(x * a for x, a in zip(cc, view.A)) % D == 0
        q2 = odd_part(R2.denominator)
        e3 = evaluate(view, s3[0])[1] if s3 else None
        removed, added = relative_divisors(q_ref, q2, view.primes)
        ind = coset_lattice(D, view.A)[2]
        rows.append({"t": t, "D": D, "index": ind, "c_l1": c1, "W_l1": window(e1, tol), "c": c2, "eps": e2,
                     "W": window(e2, tol), "actual": a2, "q": q2, "full_q": R2.denominator,
                     "removed": removed, "added": added,
                     "c_all": s3[0] if s3 else None, "eps_all": e3, "W_all": window(e3, tol) if e3 else None,
                     "support": odd_support(R2, view.primes)})
    return rows


def run_shift(N, L, tol_bits, W_req, R=3, verbose=True, subsets=True):
    """One shift. Main ladder: reference approximant Taylor, D_t = product of the t largest primes of the Taylor
    denominator. Then every sub-family with at least two members gets a ladder over the largest primes of its own
    common denominator, to ask whether any genuine mixture beats the best single approximant."""
    tol = Q(1, 1 << tol_bits)
    ap = Approximants(N, L)
    full = View(ap, [0, 1, 2])
    sup, rem = removable_primes(full)
    idx = lattice_index_report(full)
    q_T = odd_part(ap.R[0].denominator)
    singles = [(nm, r, e, odd_support(r, ap.primes)) for nm, r, e in zip(ap.names, ap.R, ap.eps)]
    best_single = min(singles, key=lambda s: odd_part(s[1].denominator))
    q_best = odd_part(best_single[1].denominator)
    order = sorted(valuation_vec(q_T, ap.primes), reverse=True)
    if verbose:
        print("-- shift N=%d, precision target 2^-%d, tolerance 2^-%d (future shifts W: largest j with 2^j eps <= tol)" % (N, L, tol_bits))
        print("   depths: " + ", ".join("%s=%d" % kv for kv in ap.depth().items()))
        print("   %-3s %8s %10s %7s %8s %s" % ("src", "log2 eps", "odd q bits", "2-adic", "#primes", "max prime"))
        for nm, r, e, s in singles:
            print("   %-3s %8.1f %10.1f %7d %8d %d" % (nm, flog2(e), bits(odd_part(r.denominator)), v2(r.denominator),
                                                        len(s), max(s) if s else 0))
        print("   common odd denominator M: %.1f bits, %d primes; gcd(M, A_i - A_0) = %d, so the lattice for removing all of M "
              "has index %.1f bits in Z^%d; full removal feasible = %s" % (
                  bits(full.M_odd), len(sup), idx["g"], bits(idx["index"]), idx["k"] - 1, idx["feasible_full"]))
        print("   ladder over the Taylor primes, largest first; weights = certified eps_i; genuine mixing = at least two nonzero c_i,")
        print("   'all' = every c_i nonzero; unimodular lattice + LLL, +-%d about the rounded least-squares coordinates of the reduced basis" % R)
        print("   %3s %7s %6s | %9s %5s | %9s %5s | %8s %5s | %9s | %8s %8s %7s" % (
            "t", "D bits", "idx b", "box |c|_1", "W", "log2 eps", "W", "all: eps", "W", "odd q b", "removed", "added", "#primes"))
    rows = ladder_rows(full, order, tol, R, q_T)
    if verbose:
        for r in rows:
            e3 = r["eps_all"]
            print("   %3d %7.1f %6.1f | %9d %5d | %9.1f %5d | %8s %5s | %9.1f | %8.1f %8.1f %7d" % (
                r["t"], bits(r["D"]), bits(r["index"]), sum(map(abs, r["c_l1"])), r["W_l1"], flog2(r["eps"]), r["W"],
                "%.1f" % flog2(e3) if e3 else "-", r["W_all"] if r["W_all"] is not None else "-", bits(r["q"]),
                bits(r["removed"]), bits(r["added"]), len(r["support"])))
            print("       full denominator = %d, v2 = %d" % (r["full_q"], v2(r["full_q"])))
    ok = [r for r in rows if r["W"] >= W_req]
    sel = max(ok, key=lambda r: r["D"])
    sup2 = sel["support"]
    summary = dict(sel, N=N, L=L, depths=ap.depth(), q_T=q_T, support_T=singles[0][3], best_single=best_single[0],
                   q_best=q_best, support_best=best_single[3], singles=singles)
    if verbose:
        print("   selected (largest D with W >= %d): t=%d" % (W_req, sel["t"]))
        print("     removed divisor of the Taylor denominator: %d (%.1f bits); added divisor %d (%.1f bits)" % (
            sel["removed"], bits(sel["removed"]), sel["added"], bits(sel["added"])))
        print("     c = %s, ||c||_1 = %d, certified error 2^%.1f (measured <= 2^%.1f), future shifts W = %d at tolerance 2^-%d" % (
            sel["c"], sum(map(abs, sel["c"])), flog2(sel["eps"]), flog2(sel["actual"]), sel["W"], tol_bits))
        print("     lattice index of D: %.1f bits (D = %.1f bits, gcd(D, differences) = %d)" % (
            bits(sel["index"]), bits(sel["D"]), sel["D"] // sel["index"]))
        print("     reduced odd denominator %.1f bits (%d primes) vs Taylor %.1f bits (%d primes); best single %s %.1f bits (%d primes)" % (
            bits(sel["q"]), len(sup2), bits(q_T), len(singles[0][3]), best_single[0], bits(q_best), len(best_single[3])))
        print("     prime support: %s" % sorted(sup2))
    summary["subsets"] = []
    if subsets:
        if verbose:
            print("   Sub-families: ladder over the largest primes of each common denominator; best row with W >= %d" % W_req)
            print("   %-4s %8s %8s | %6s %9s %5s %9s | %9s %8s %s" % (
                "fam", "M bits", "t/rows", "D bits", "|c|_1", "W", "q bits", "best sgl", "beats?", "c (bounded search)"))
        for sub in ([0, 1], [0, 2], [1, 2], [0, 1, 2]):
            v = View(ap, sub)
            rws = ladder_rows(v, sorted(valuation_vec(v.M_odd, ap.primes), reverse=True), tol, R, q_T)
            okk = [r for r in rws if r["W"] >= W_req]
            bm = min(okk, key=lambda r: (r["q"], r["D"]))
            bs = min(odd_part(r.denominator) for r in v.R)
            summary["subsets"].append((v.label(), bm, bs))
            bm["family"] = v.label()
            if verbose:
                print("     full denominator = %d, v2 = %d" % (bm["full_q"], v2(bm["full_q"])))
                print("   %-4s %8.1f %4d/%-3d | %6.1f %9d %5d %9.1f | %9.1f %8s %s" % (
                    v.label(), bits(v.M_odd), bm["t"], len(rws) - 1, bits(bm["D"]), sum(map(abs, bm["c"])), bm["W"],
                    bits(bm["q"]), bits(bs), "yes" if bm["q"] < bs else "no", bm["c"]))
        best = min((r for _, r, _ in summary["subsets"]), key=lambda r: (r["q"], r["D"]))
        summary["best_mixture"] = best
        w_eps = [-((-e.numerator * (1 << (L + 40))) // e.denominator) for e in ap.eps]
        s3 = search_coset(best["D"], full.A, w_eps, R, mixing=3)
        e3 = evaluate(full, s3[0])[1] if s3 else None
        best["c_all3"], best["eps_all3"] = (s3[0], e3) if s3 else (None, None)
        if verbose:
            print("   Smallest odd denominator in the tested ladders (family %s, W >= %d):" % (best["family"], W_req))
            print("     c = %s (||c||_1 = %d), required D = %d (%.1f bits), lattice index %.1f bits" % (
                best["c"], sum(map(abs, best["c"])), best["D"], bits(best["D"]), bits(best["index"])))
            print("     removed divisor of the Taylor denominator %d (%.1f bits); added divisor %d (%.1f bits)" % (
                best["removed"], bits(best["removed"]), best["added"], bits(best["added"])))
            print("     certified error 2^%.1f, measured <= 2^%.1f, future shifts W = %d at tolerance 2^-%d" % (
                flog2(best["eps"]), flog2(best["actual"]), best["W"], tol_bits))
            print("     reduced odd denominator %.1f bits, prime support (%d): %s" % (bits(best["q"]), len(best["support"]), sorted(best["support"])))
            if e3 is not None:
                R3 = sum((x * r for x, r in zip(s3[0], ap.R)), Q())
                print("     same D with every c_i nonzero: c = %s, certified error 2^%.1f, W = %d, but reduced odd denominator %.1f bits "
                      "(Gaussian primes return)" % (s3[0], flog2(e3), window(e3, tol), bits(odd_part(R3.denominator))))
    # A prime carried by Taylor alone is killed by c_T = 0 mod p, a rank-one condition: in the T,B family the cheapest
    # vector then has |c|_1 = 2D - 1 (observed and printed, not asserted in general).
    for label, bm, _ in summary["subsets"]:
        if label == "TB" and bm["D"] > 1:
            summary["TB_single_pole"] = sum(map(abs, bm["c"])) == 2 * bm["D"] - 1
            if verbose:
                print("   T,B family: |c|_1 = %d, 2D-1 = %d, equal: %s (primes of T absent from B cost c_T = 0 mod p)" % (
                    sum(map(abs, bm["c"])), 2 * bm["D"] - 1, summary["TB_single_pole"]))
    return ap, rows, summary


# ----------------------------------------------------------------------------------
# 4. Validation of the lattice solver
# ----------------------------------------------------------------------------------


def validate_solver(quick):
    random.seed(15)
    trials = 0
    for _ in range(40 if quick else 120):
        D = random.choice([3, 5, 7, 15, 35, 105, 143, 221, 1001, 3 * 5 * 7 * 11 * 13])
        A = [random.randrange(-10 ** 6, 10 ** 6) for _ in range(3)]
        # Lean theorem feasible_iff_gcd, checked against exhaustive search
        g = D
        for i in (1, 2):
            g = gcd(g, A[i] - A[0])
        feasible = A[0] % g == 0
        res = coset_lattice(D, A)
        assert (res is not None) == feasible
        if feasible:
            B = 14
            bf = brute_min_l1(D, A, B)
            s = search_coset(D, A, [1, 1, 1], R=4)
            assert s is not None
            c, _ = s
            assert sum(c) == 1 and sum(x * a for x, a in zip(c, A)) % D == 0
            if bf is not None:
                assert sum(map(abs, c)) <= bf[0], (D, A, c, bf)
            trials += 1
    print("   solver validation: %d feasible random instances; sampled cost <= brute-force minimum over |c_i|<=14" % trials)
    # degenerate dimension: all differences zero mod D -> index 1, feasible only if D | A_0
    res = coset_lattice(15, [1, 16, 31])
    assert res is None
    res = coset_lattice(15, [0, 15, 30])
    assert res is not None and res[2] == 1
    res = coset_lattice(15, [1])  # k = 1: no mixing at all
    assert res is None
    res = coset_lattice(1001, [2, 9, 300])
    assert res is not None
    print("   degenerate cases: all differences = 0 (mod D) gives index 1 and feasibility iff D | A_0; k=1 gives only D | A_0")


# ----------------------------------------------------------------------------------
# 4b. Replayable bounded-optimal examples (exhaustive search in a stated box) and cross-checks
# ----------------------------------------------------------------------------------


def exhaustive_box(A, cost, D, B, mixing):
    """Global minimum of cost(c) over ALL integer vectors with sum c = 1, max |c_i| <= B, at least `mixing` nonzero
    coordinates and D | sum c_i A_i. Exhaustive for k = 2, 3. cost(c) may return an exact Fraction. Returns (cost, c)."""
    k = len(A)
    best = None
    for free in product(range(-B, B + 1), repeat=k - 1):
        c = [1 - sum(free)] + list(free)
        if abs(c[0]) > B or sum(1 for x in c if x) < mixing:
            continue
        if sum(x * a for x, a in zip(c, A)) % D:
            continue
        key = (cost(c), sum(map(abs, c)), c)
        if best is None or key < best:
            best = key
    return best


def exact_denominator(R):
    """Full reduced denominator of R as 'value = 2^a * odd', with the odd part factored."""
    q = R.denominator
    f = smooth_factor(odd_part(q), primes_upto(10 ** 5)) if odd_part(q) > 1 else {}
    return q, v2(q), f


def show_combo(view, c, tol, label):
    R, eps, actual = evaluate(view, c)
    q, a2, f = exact_denominator(R)
    print("   %s" % label)
    print("     c = %s (sum = %d, ||c||_1 = %d, nonzero = %d)" % (c, sum(c), sum(map(abs, c)), sum(1 for x in c if x)))
    print("     value = %d/%d" % (R.numerator, R.denominator))
    print("     denominator = %d = 2^%d * %s" % (q, a2, " * ".join("%d%s" % (p, "^%d" % e if e > 1 else "") for p, e in sorted(f.items())) or "1"))
    print("     certified error sum |c_i| eps_i = 2^%.2f, measured error <= 2^%.2f, future shifts W = %d at tolerance 2^-%d" % (
        flog2(eps), flog2(actual), window(eps, tol), int(-flog2(tol))))
    return R, eps


def replay_examples(N=32, L=24, tol_bits=8):
    """Two examples at one shift, small enough to replay by hand with a Fraction-capable calculator.

    (A) T and B only: the box minimum of the l1 norm over genuine mixtures (two nonzero coefficients) that remove the
        product D of the two largest primes of the Taylor denominator.
    (B) T, G and B with all three coefficients nonzero: the box minimum of the exact weighted error sum |c_i| eps_i
        for the same D. The lattice search of section 2 uses integer weights ceil(eps_i 2^(L+40)); here the exhaustive
        search uses the exact rational eps_i, and the two are compared.
    Both are exhaustive over the stated box, hence global minima inside the box and not over Z^k."""
    tol = Q(1, 1 << tol_bits)
    ap = Approximants(N, L)
    full = View(ap, [0, 1, 2])
    q_T = odd_part(ap.R[0].denominator)
    D_primes = sorted(valuation_vec(q_T, ap.primes), reverse=True)[:2]
    sup, rem = removable_primes(full)
    remd = dict(rem)
    D = 1
    for p in D_primes:
        D *= p ** remd[p]
    print("== Replayable bounded-optimal examples at N=%d, L=%d: D = %s = %d (the two largest primes of the Taylor denominator)" % (
        N, L, "*".join(map(str, D_primes)), D))
    print("   R_T = %d/%d" % (ap.R[0].numerator, ap.R[0].denominator))
    print("   R_G = %d/%d" % (ap.R[1].numerator, ap.R[1].denominator))
    print("   R_B = %d/%d" % (ap.R[2].numerator, ap.R[2].denominator))
    print("   certified errors: " + ", ".join("eps_%s = 2^%.2f" % (nm, flog2(e)) for nm, e in zip(ap.names, ap.eps)))
    for nm, r in zip(ap.names, ap.R):
        q, a2, f = exact_denominator(r)
        print("   denominator of R_%s = 2^%d * odd part with %d primes (%.1f bits)" % (nm, a2, len(f), bits(odd_part(q))))
    # (A) T and B, l1 norm, box 2D+100
    TB = View(ap, [0, 2])
    B_A = 2 * D + 100
    ba = exhaustive_box(TB.A, lambda c: sum(map(abs, c)), D, B_A, 2)
    print("   (A) T,B; exhaustive over |c_i| <= %d; minimise ||c||_1 among genuine mixtures with D | numerator: minimum %d" % (B_A, ba[0]))
    RA, _ = show_combo(TB, ba[2], tol, "optimal genuine mixture of T and B (box minimum)")
    ls = search_coset(D, TB.A, [1, 1], 3)
    print("     lattice search (section 2) returns the same vector: %s" % (ls is not None and ls[0] == ba[2]))
    assert sum(x * a for x, a in zip(ba[2], TB.A)) % D == 0
    # (B) T, G, B all nonzero, exact weighted error, box 60
    B_B = 60
    exact_cost = lambda c: sum((abs(x) * e for x, e in zip(c, ap.eps)), Q())
    bb = exhaustive_box(full.A, exact_cost, D, B_B, 3)
    print("   (B) T,G,B; exhaustive over |c_i| <= %d; every c_i nonzero; minimise the exact weighted error sum |c_i| eps_i" % B_B)
    RB, epsB = show_combo(full, bb[2], tol, "optimal three-way mixture (box minimum, exact weights)")
    w_eps = [-((-e.numerator * (1 << (L + 40))) // e.denominator) for e in ap.eps]
    s3 = search_coset(D, full.A, w_eps, 3, mixing=3)
    ex_r = exhaustive_box(full.A, lambda c: sum(w * abs(x) for w, x in zip(w_eps, c)), D, B_B, 3)
    print("     lattice search with rounded integer weights ceil(eps_i 2^%d) returns the same vector: %s; "
          "exhaustive search with rounded weights returns the same vector: %s" % (L + 40, s3 is not None and s3[0] == bb[2], ex_r[2] == bb[2]))
    # the unrestricted two-coefficient alternative inside the same box, for contrast
    b2 = exhaustive_box(full.A, exact_cost, D, B_B, 2)
    print("     for contrast, the box minimum of the exact weighted error with only two nonzero coefficients is %s, error 2^%.2f" % (
        b2[2], flog2(b2[0])))
    return ba, bb


def cross_checks():
    """Cross-checks against the Phase 14 base helpers when scripts/discrepancy_experiments.py is importable."""
    try:
        import os
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import discrepancy_experiments as de
    except Exception as exc:  # pragma: no cover - depends on the checkout
        print("   (cross-checks against scripts/discrepancy_experiments.py skipped: %s)" % exc)
        return
    for n in (1, 5, 18, 39):
        assert beta_y(n) == de.corrected_model(n, n), n
    lo, hi = ln2_enclosure(96)
    bits_ = de.log_bits(64)
    assert lo >> 32 == int(bits_, 2) or (hi >> 32) == int(bits_, 2)
    assert lo >> 32 == hi >> 32 == int(bits_, 2)
    print("   cross-checks: beta_y(n) = corrected_model(n, n) for n in 1,5,18,39; leading 64 bits of ln 2 agree with log_bits(64)")


# ----------------------------------------------------------------------------------
# 5. The Taylor obstruction: affine combinations of Taylor cutoffs preserve the common residue
# ----------------------------------------------------------------------------------


def taylor_bad_primes(v, primes):
    """Primes dividing the numerator u_v of sum_{m<=v} 1/(m 2^m) (the residue polar part is 2^N u_v / (w_v p))."""
    s = sum((Q(1, m << m) for m in range(1, v + 1)), Q())
    return {p for p in primes if s.numerator % p == 0}, s


def band(K, h, v, primes):
    return [p for p in primes if p * (v + 1) > K + h and p * v <= K]


def taylor_obstruction_exact(N, K, h, vs, ncomb=60):
    """Exact check at one (N, K, h): the cutoffs J in [K, K+h].

    (a) for p in the v-band, floor(J/p) = v for every J, so T_J - T_K is p-integral;
    (b) v_p(T_K) = 1 unless p | u_v; (c) therefore every integer affine combination of T_K..T_{K+h} has p ||
    denominator (checked on all coefficient vectors with |c_i| <= 1 and on random large ones); (d) the gcd lemma says
    D = product of the surviving band primes is not removable: gcd(D, T_J numerators - T_K numerator) = D."""
    primes = primes_upto(K + h + 10)
    T = []
    cur = taylor(N, K - 1)
    for J in range(K, K + h + 1):
        cur += Q(1 << N, J << J) if N >= 0 else Q(1, J << (J - N))
        T.append(cur)
    M = 1
    for r in T:
        M = M * r.denominator // gcd(M, r.denominator)
    A = [int(r * M) for r in T]
    surviving, poor = [], []
    for v in vs:
        bad, _ = taylor_bad_primes(v, primes)
        for p in band(K, h, v, primes):
            assert p * p > K + h, "band prime too small for the polar-part argument"
            assert all((J // p) == v for J in range(K, K + h + 1))
            for r in T:  # (a)
                assert (r - T[0]).denominator % p != 0
            polar = T[0].denominator % p == 0
            assert polar == (p not in bad), (p, v)  # (b) denominator exactly p iff p does not divide u_v
            if polar:
                assert T[0].denominator % (p * p) != 0
                surviving.append(p)
            else:
                poor.append(p)
    D = 1
    for p in surviving:
        D *= p
    # (c) every affine combination keeps every surviving prime in its denominator
    checks = 0
    vecs = list(product((-1, 0, 1), repeat=h)) if h <= 8 else []
    for tail in vecs:
        c = [1 - sum(tail)] + list(tail)
        R = sum((ci * r for ci, r in zip(c, T)), Q())
        assert all(R.denominator % p == 0 for p in surviving)
        checks += 1
    rng = random.Random(7)
    for _ in range(ncomb):
        tail = [rng.randrange(-10 ** 9, 10 ** 9) for _ in range(h)]
        c = [1 - sum(tail)] + tail
        R = sum((ci * r for ci, r in zip(c, T)), Q())
        assert all(R.denominator % p == 0 for p in surviving)
        checks += 1
    # (d) lattice index at modulus D: all differences vanish mod D (index 1, dimension 0 of mixing), D does not divide A_0
    diffs = [(a - A[0]) for a in A[1:]]
    gD = D
    for x in diffs:
        gD = gcd(gD, x)
    assert gD == D and A[0] % D != 0
    res = coset_lattice(D, A[:min(len(A), 4)])
    assert res is None
    return {"K": K, "h": h, "primes": len(surviving), "lost": len(poor), "log_odd_q": log2(odd_part(T[0].denominator)) * 0.6931471805599453, "checks": checks, "D_bits": bits(D)}


def taylor_obstruction_table(Ks, vs=(1, 2, 3, 4, 5, 6)):
    """Preserved logarithmic mass of the bands sum_v sum_{p in band_v, p not | u_v} log p, relative to K, h ~ sqrt K."""
    from math import log
    print("   %9s %6s %4s | %12s %14s %10s" % ("K", "h", "V", "log mass / K", "1-1/(V+1)", "primes"))
    out = []
    bad_cache = {}
    plist = primes_upto(max(Ks) + 1000)
    for K in Ks:
        h = isqrt(K)
        for V in (2, 4, 6):
            mass, cnt = 0.0, 0
            for v in range(1, V + 1):
                if v not in bad_cache:
                    bad_cache[v] = taylor_bad_primes(v, plist[: len(plist)])[0] if v <= 6 else set()
                bad = bad_cache[v]
                for p in band(K, h, v, [q for q in plist if q <= K]):
                    if p not in bad:
                        mass += log(p)
                        cnt += 1
            out.append((K, h, V, mass / K, 1 - 1 / (V + 1), cnt))
            print("   %9d %6d %4d | %12.4f %14.4f %10d" % (K, h, V, mass / K, 1 - 1 / (V + 1), cnt))
    return out


def section_obstruction(quick):
    print("== Taylor obstruction: integer affine combinations of Taylor cutoffs in [K, K+h] (h = o(K), v fixed)")
    for (N, K, h) in ((60, 150, 4), (200, 400, 6)) if quick else ((60, 150, 4), (200, 400, 6), (96, 720, 8)):
        r = taylor_obstruction_exact(N, K, h, vs=(1, 2, 3, 4), ncomb=40)
        print("   exact N=%d K=%d h=%d v<=4: %d band primes keep v_p=1 in every affine combination (%d coefficient vectors "
              "checked incl. all |c_i|<=1), %d band primes lost to u_v, log D = %.1f, log odd denominator of T_K = %.1f (natural logs)"
              % (N, K, h, r["primes"], r["checks"], r["lost"], r["D_bits"] * 0.6931471805599453, r["log_odd_q"]))
        print("      lattice: all %d differences T_J - T_K vanish mod D, so gcd(D, differences) = D, the congruence lattice is the "
              "whole sum-zero lattice Z^%d (index 1, mixing dimension 0) and D | A_0 fails: D is not removable" % (h, h))
    print("   preserved logarithmic mass (formula, h = isqrt K); bands v <= V, bad primes = divisors of u_v:")
    taylor_obstruction_table((1000, 10 ** 4) if quick else (1000, 10 ** 4, 10 ** 5, 10 ** 6))
    print("   u_v (numerators of sum_{m<=v} 1/(m 2^m)): " +
          ", ".join("%d: %d" % (v, taylor_bad_primes(v, [2])[1].numerator) for v in range(1, 7)))


# ----------------------------------------------------------------------------------
# 6. Main
# ----------------------------------------------------------------------------------


def check_nonconsecutive_divisors(ap):
    """Independent witnesses excluded by the descending-prime prefix search."""
    coefficient = {32: 893, 48: 204883990}[ap.N]
    c = [coefficient, 0, 1 - coefficient]
    value, budget, _ = evaluate(ap, c)
    denominator = value.denominator
    odds = odd_part(denominator)
    shifts = window(budget, Q(1, 256))
    if ap.N == 48:
        assert odds == 60452009000818733925 < ap.R[2].denominator == 190103424450275260925
        assert v2(denominator) == 35 and denominator > ap.R[2].denominator and shifts == 4
        seven = 53 * 59 * 61 * 67 * 71 * 73 * 79
        for coefficients, required, retained, expected_window in (
                ([-2, 1, 2], seven // 53, 53, 30), ([-104, 52, 53], seven, 1, 25)):
            row, charge, _ = evaluate(ap, coefficients)
            assert gcd(row.denominator, required) == 1 and row.denominator % retained == 0
            assert window(charge, Q(1, 256)) == expected_window
    else:
        assert shifts == 5 and odds < (1 << 44)
    print("   nonconsecutive divisor witness: c=%s norm=%d full denominator=%d v2=%d "
          "odd support=%s log2 budget=%.2f last shift=%d" %
          (c, sum(map(abs, c)), denominator, v2(denominator),
           sorted(odd_support(value, ap.primes)), flog2(budget), shifts))


def main(argv):
    quick = "--quick" in argv
    print("== Solver validation")
    validate_solver(quick)
    cross_checks()
    replay_examples()
    print("== Affine lifts at common shifts (T = Taylor, G = Gaussian, B = beta); k = 3 approximants")
    cases = [(32, 24)] if quick else [(32, 24), (48, 40), (64, 56)]
    results = []
    for N, L in cases:
        ap, _, result = run_shift(N, L, tol_bits=8, W_req=4)
        results.append(result)
        if N in (32, 48):
            check_nonconsecutive_divisors(ap)
    section_obstruction(quick)
    print("All Phase 15 affine checks passed.")
    return results


if __name__ == "__main__":
    main(sys.argv[1:])
