"""Phase 16, Track 3: adaptive dyadic logarithm identities and the 5/12 obstruction.

Standard library only. Every certificate uses exact integer or Fraction arithmetic;
the only floating-point values are printed summaries (logarithms of exact integers)
and the comparison of an exact shifted prefix with a certified dyadic enclosure of
2^N log 2.

Run:  python -B scripts/phase16_adaptive_log.py              (about 5 seconds)
      python -B scripts/phase16_adaptive_log.py --quick      (skips N = 480)
      python -B scripts/phase16_adaptive_log.py --frontier   (adds section 6, minutes)

Notation follows notes/phase14/gaussian-relations.md.  A cell is indexed by
v = floor(2x).  A formula for log 2 in the real+Gaussian alphabet collapses at every
real cutoff to

    S_theta = B + a(A1-B) + u(G1-B) + b(G2+A2-A4-B) + c(G3+2A2-2A4-B),
    B = 2A2 + A3 - A6,  theta = (a, u, b, c) in Q^4.

On the cell v the value S_theta(v/2) is an affine form row(v) . (1, a, u, b, c).
"""

import sys
import time
from fractions import Fraction as Q
from math import gcd, isqrt, log

QUICK = "--quick" in sys.argv
NAMES = ("a", "u", "b", "c")
THETA_MIN = (0, 0, 0, -5)      # rate 5/12
THETA_TWO = (0, 0, 0, -2)      # rate 13/30


def mass(v):
    """Asymptotic prime mass 2/(v(v+1)) of the band 2N/(v+1) < p <= 2N/v."""
    return Q(2, v * (v + 1))


# ---------------------------------------------------------------------------
# 1. Cell values of the eight surviving sources and the five basis prefixes
# ---------------------------------------------------------------------------

def source_cells(vmax):
    """Exact values at x = v/2, v = 0..vmax, of A1,A2,A3,A4,A6,G1,G2,G3.

    A_k gains its j-th term (2^-k)^j / j at v = 2kj.  G_t gains
    2 Re(((1+i)/2^t)^j) / j at v = (2t-1) j: the homogeneous cutoffs.
    """
    out = {}
    for k in (1, 2, 3, 4, 6):
        jumps = [Q(0)] * (vmax + 1)
        j = 1
        while 2 * k * j <= vmax:
            jumps[2 * k * j] += Q(1, j << (k * j))
            j += 1
        out["A%d" % k] = jumps
    for t in (1, 2, 3):
        n = 2 * t - 1
        jumps = [Q(0)] * (vmax + 1)
        a, b, j = 1, 0, 1
        while n * j <= vmax:
            a, b = a - b, a + b                     # (1+i)^j = a + b i
            jumps[n * j] += Q(2 * a, j << (t * j))
            j += 1
        out["G%d" % t] = jumps
    for name, jumps in out.items():
        total = Q(0)
        for v in range(vmax + 1):
            total += jumps[v]
            jumps[v] = total
    return out


def basis_rows(vmax):
    """row[v] = (B, A1-B, G1-B, G2+A2-A4-B, G3+2A2-2A4-B) at x = v/2."""
    s = source_cells(vmax)
    rows = []
    for v in range(vmax + 1):
        A1, A2, A3, A4, A6 = (s["A%d" % k][v] for k in (1, 2, 3, 4, 6))
        G1, G2, G3 = (s["G%d" % t][v] for t in (1, 2, 3))
        base = 2 * A2 + A3 - A6
        rows.append((base, A1 - base, G1 - base, G2 + A2 - A4 - base,
                     G3 + 2 * A2 - 2 * A4 - base))
    return rows, s


def normal_coefficients(theta):
    """Coefficients of (A1,A2,A3,A4,A6,G1,G2,G3) in S_theta (valuation system)."""
    a, u, b, c = theta
    a6 = a + u + b + c - 1
    a4 = -b - 2 * c
    return (a, -a4 - 2 * a6, -a6, a4, a6, u, b, c)


def value(row, theta):
    return row[0] + sum(t * r for t, r in zip(theta, row[1:]))


def reduce_row(row, equations):
    """Eliminate earlier pivot variables, in insertion order (forward elimination)."""
    for column, pivot in equations:
        if row[column]:
            row = tuple(x - row[column] * y for x, y in zip(row, pivot))
    return row


def exact_rate(theta, rows):
    """Fixed-formula rate rho(theta) with the certified positive tail (Phase 14)."""
    coeffs = normal_coefficients(theta)
    weight = sum(map(abs, coeffs[:5])) + 2 * sum(map(abs, coeffs[5:]))
    end = 1
    while 2 ** end <= 8 * weight:
        end += 1
    assert 2 * end <= len(rows) - 1, "extend the cell table"
    rate = Q(1, end)
    for v in range(1, 2 * end):
        if value(rows[v], theta):
            rate += mass(v)
    return rate, end


def check_rows(rows, s):
    print("== 1. Cell rows and the collapsed normal form")
    # Constant cells of the families used later (no congruence can cancel these bands).
    top = len(rows) - 1
    assert [v for v in range(1, top) if not any(rows[v][1:])] == []
    assert [v for v in range(1, top) if rows[v][1] == rows[v][3] == rows[v][4] == 0] == [1]
    assert [v for v in range(1, top) if rows[v][3] == rows[v][4] == 0] == [1, 2]
    assert [v for v in range(1, top) if rows[v][4] == 0] == [1, 2, 3, 4, 8, 9, 10, 11]
    print("   constant cells up to v=%d: none in Q^4; {1} on u=0; {1,2} on u=a=0;"
          " {1,2,3,4,8,9,10,11} on the c-line (values 0,0,0,1/2,11/16 x4)" % (top - 1))
    # The row form agrees with the 8-source normal form at random-ish rational points.
    tests = [(0, 0, 0, -5), (Q(1, 3), -2, Q(7, 5), 11), (5, Q(-1, 2), 0, Q(3, 4))]
    for theta in tests:
        co = normal_coefficients(theta)
        for v in range(0, 80):
            src = [s[n][v] for n in ("A1", "A2", "A3", "A4", "A6", "G1", "G2", "G3")]
            assert value(rows[v], theta) == sum(x * y for x, y in zip(co, src))
    # Infinite values: each zero-limit basis direction has zero log-2 and odd-prime
    # content.  Exponent vectors over (log 2, log 3, log 5, log 7).
    inf = {"A1": (1, 0, 0, 0), "A2": (2, -1, 0, 0), "A3": (3, 0, 0, -1),
           "A4": (4, -1, -1, 0), "A6": (6, -2, 0, -1), "G1": (1, 0, 0, 0),
           "G2": (3, 0, -1, 0), "G3": (5, 0, -2, 0)}
    order = ("A1", "A2", "A3", "A4", "A6", "G1", "G2", "G3")
    for theta, target in ((THETA_MIN, (1, 0, 0, 0)), ((Q(2, 7), 3, -1, 4), (1, 0, 0, 0))):
        co = normal_coefficients(theta)
        vec = tuple(sum(c * inf[n][i] for c, n in zip(co, order)) for i in range(4))
        assert vec == target
    print("   normal form = row form on 80 cells at 3 rational points; S(inf)=log 2 checked")
    print("   cells 1..7 (const; a,u,b,c):")
    for v in range(1, 8):
        print("    v=%d  %s" % (v, "  ".join(str(x) for x in rows[v])))


# ---------------------------------------------------------------------------
# 2. Uniform finite-cell mass bound: branch and bound over all of Q^4
# ---------------------------------------------------------------------------

class Tree:
    def __init__(self):
        self.nodes = self.branch = self.pruned = self.leaves = 0
        self.zero_rows = self.const_rows = 0
        self.max_bits = 0
        self.max_depth = 0


def band_certificate(rows, cells, bound):
    """All affine spaces of theta in Q^4 whose mass on `cells` stays below `bound`.

    The truthful path of any theta (zero branch iff its row vanishes) has spent
    exactly its mass on the cells processed; the nonzero branch forgets its
    inequation, which only enlarges the tested set.
    """
    tree = Tree()
    leaves = []

    def visit(index, equations, spent, depth):
        tree.nodes += 1
        tree.max_depth = max(tree.max_depth, depth)
        if spent >= bound:
            tree.pruned += 1
            return
        if index == len(cells):
            tree.leaves += 1
            leaves.append((equations, spent))
            return
        v = cells[index]
        reduced = reduce_row(rows[v], equations)
        column = next((k for k in (1, 2, 3, 4) if reduced[k]), None)
        if column is None:
            if reduced[0]:
                tree.const_rows += 1
                visit(index + 1, equations, spent + mass(v), depth)
            else:
                tree.zero_rows += 1
                visit(index + 1, equations, spent, depth)
            return
        tree.branch += 1
        pivot = tuple(x / reduced[column] for x in reduced)
        tree.max_bits = max(tree.max_bits, max(
            max(x.numerator.bit_length(), x.denominator.bit_length()) for x in pivot))
        visit(index + 1, equations + [(column, pivot)], spent, depth + 1)
        visit(index + 1, equations, spent + mass(v), depth + 1)

    visit(0, [], Q(0), 0)
    return leaves, tree


def leaf_points(leaves):
    points = {}
    for equations, spent in leaves:
        assert len(equations) == 4, "a leaf is not a single point"
        point = [None] * 4
        for column, row in equations:
            assert row[1:] == tuple(int(i == column) for i in (1, 2, 3, 4)), "not diagonal"
            point[column - 1] = -row[0]
        points[tuple(point)] = spent
    return points


def check_uniform_bound(rows):
    print("== 2. Uniform finite-cell mass bound over all (a,u,b,c) in Q^4")
    cells = list(range(1, 72))                       # 1 <= x < 36
    results = {}
    for bound in (Q(13, 30), Q(5, 12)):
        t0 = time.time()
        leaves, tree = band_certificate(rows, cells, bound)
        points = leaf_points(leaves)
        results[bound] = (points, tree)
        print("   bound %s on cells v=1..71: nodes %d, branchings %d, pruned %d, leaves %d,"
              " zero rows %d, constant rows %d, depth <= %d, pivot entries <= %d bits (%.1fs)"
              % (bound, tree.nodes, tree.branch, tree.pruned, tree.leaves, tree.zero_rows,
                 tree.const_rows, tree.max_depth, tree.max_bits, time.time() - t0))
        print("     surviving points:", ", ".join("(%s): %s" % (",".join(map(str, k)), v) for k, v in points.items()))
    points, tree = results[Q(13, 30)]
    assert points == {THETA_MIN: Q(7, 18), THETA_TWO: Q(73, 180)}
    assert results[Q(5, 12)][0] == points
    # Positivity of the two leaves from v = 8 on: exact cells, then the Phase 15 tail.
    for theta, finite, full in ((THETA_MIN, Q(7, 18), Q(5, 12)),
                                (THETA_TWO, Q(73, 180), Q(13, 30))):
        rate, end = exact_rate(theta, rows)
        assert rate == full
        assert all(value(rows[v], theta) > 0 for v in range(8, 2 * end))
        assert sum((mass(v) for v in range(1, 72) if value(rows[v], theta)), Q(0)) == finite
    # The uniform statement for every V >= 36 (checked exactly through V = 400):
    #   m_V(theta) = sum_{1<=v<2V, S(v/2)!=0} 2/(v(v+1)) >= 5/12 - 1/V,
    # with equality only at THETA_MIN; every other theta has m_V >= 13/30 - 1/V.
    for V in range(36, 401):
        tail = sum((mass(v) for v in range(72, 2 * V)), Q(0))
        m_min = Q(7, 18) + tail
        m_two = Q(73, 180) + tail
        assert m_min == Q(5, 12) - Q(1, V) and m_two == Q(13, 30) - Q(1, V)
        assert Q(13, 30) > m_min   # pruned branches already exceed the minimizer
    print("   for 36 <= V <= 400: min m_V = 5/12 - 1/V exactly (only at (0,0,0,-5));"
          " runner-up m_V >= 13/30 - 1/V")
    print("   u != 0 is pruned at the first cell (S(1/2) = u, mass 1)")
    bits = max(max(x.numerator.bit_length(), x.denominator.bit_length())
               for v in range(72) for x in rows[v])
    D = 1
    for v in range(72):
        for x in rows[v]:
            D = D * x.denominator // gcd(D, x.denominator)
    print("   Lean export size: 71 rows of 5 rationals, entries <= %d bits, common denominator"
          " %d bits" % (bits, D.bit_length()))
    return tree


# ---------------------------------------------------------------------------
# 3. Explicit linear-height threshold: a relaxed branch and bound
# ---------------------------------------------------------------------------

def relaxed_threshold(rows, eps, rational, target=Q(5, 12)):
    """Lower bound for liminf log q_N / N over theta_N != THETA_MIN with
    log H_N <= eps N.  Returns the minimum bound over all leaves (None if all pruned
    at 5/12) and tree statistics.

    In the nonzero branch a cell is charged (m_v - eps)^+ for pruning.  At a leaf the
    nonzero cells are regrouped by proportional affine forms on the leaf space F: one
    numerator of height <= H_N K carries every cancelled prime of the class, so the
    class costs (sum of masses - eps)^+.  Constant forms on F lose O(1) only.  When F
    becomes a point theta_F, the formula is fixed and its exact rate is used.
    Rational theta pay a further eps for primes of the denominator D_N.
    """
    vmax = max(v for v in range(1, 72) if mass(v) > eps)
    cells = list(range(1, vmax + 1))
    threshold = target + (eps if rational else 0)
    stats = {"nodes": 0, "points": 0, "spaces": 0, "pruned": 0}
    worst = [None]

    def leaf_value(bound):
        if worst[0] is None or bound < worst[0]:
            worst[0] = bound

    def visit(index, equations, const, under, nonzero):
        stats["nodes"] += 1
        if len(equations) == 4:
            stats["points"] += 1
            theta = [None] * 4
            # back-substitute the (forward-eliminated) pivots
            for column, row in reversed(equations):
                val = -row[0] - sum(row[k] * theta[k - 1] for k in range(1, 5)
                                    if k != column and theta[k - 1] is not None)
                theta[column - 1] = val
            theta = tuple(theta)
            if any(not value(rows[v], theta) for v in nonzero):
                return                           # infeasible branch
            if theta == THETA_MIN:
                return
            rate, _ = exact_rate(theta, rows)
            leaf_value(rate)
            return
        if const + under >= threshold:
            stats["pruned"] += 1
            return
        if index == len(cells):
            stats["spaces"] += 1
            classes = {}
            extra = Q(0)
            for v in nonzero:
                r = reduce_row(rows[v], equations)
                k = next((k for k in (1, 2, 3, 4) if r[k]), None)
                if k is None:
                    if not r[0]:
                        return                   # infeasible branch
                    extra += mass(v)
                    continue
                key = tuple(x / r[k] for x in r)
                classes[key] = classes.get(key, Q(0)) + mass(v)
            bound = const + extra + sum((max(Q(0), m - eps) for m in classes.values()), Q(0))
            leaf_value(bound - (eps if rational else 0))
            return
        v = cells[index]
        reduced = reduce_row(rows[v], equations)
        column = next((k for k in (1, 2, 3, 4) if reduced[k]), None)
        if column is None:
            visit(index + 1, equations, const + (mass(v) if reduced[0] else 0), under, nonzero)
            return
        pivot = tuple(x / reduced[column] for x in reduced)
        visit(index + 1, equations + [(column, pivot)], const, under, nonzero)
        visit(index + 1, equations, const, under + max(Q(0), mass(v) - eps), nonzero + [v])

    visit(0, [], Q(0), Q(0), [])
    return worst[0], stats, vmax


def threshold_search(rows, rational, target, lo, hi, show=()):
    """Largest eps = 1/k (k integer in (lo, hi]) that the relaxation certifies."""
    tag = "rational" if rational else "integer "

    def ok_at(k, verbose=False):
        low, stats, vmax = relaxed_threshold(rows, Q(1, k), rational, target)
        ok = low is None or low >= target
        if verbose:
            print("   %s target %s, eps=1/%d: cells<=%d, nodes %d, point leaves %d,"
                  " space leaves %d -> min bound %s %s"
                  % (tag, target, k, vmax, stats["nodes"], stats["points"], stats["spaces"],
                     "(all pruned)" if low is None else "%.5f" % float(low),
                     "OK" if ok else "fails"))
        return ok
    for k in show:
        ok_at(k, verbose=True)
    assert not ok_at(lo) and ok_at(hi)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok_at(mid):
            hi = mid
        else:
            lo = mid
    return hi


def check_threshold(rows):
    print("== 3. Linear heights: certified epsilon below which the constants survive")
    found = {}
    for rational in (False, True):
        found[(rational, "5/12")] = threshold_search(rows, rational, Q(5, 12), 500, 600,
                                                     show=(4000, 1000, 600, 500))
        found[(rational, "13/30")] = threshold_search(rows, rational, Q(13, 30), 100, 20000,
                                                      show=(2000,))
    for rational in (False, True):
        print("   %s theta_N: log H_N <= N/%d gives liminf >= 5/12;"
              " log H_N <= N/%d and theta_N != (0,0,0,-5) give liminf >= 13/30"
              % ("integer " if rational is False else "rational", found[(rational, "5/12")],
                 found[(rational, "13/30")]))
    return found


# ---------------------------------------------------------------------------
# 4. Adaptive constructions at linear height: CRT, LLL, exact verification
# ---------------------------------------------------------------------------

def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(sieve[p * p::p]))
    return [p for p in range(n + 1) if sieve[p]]


def ln2_fixed(bits):
    """Integer s with |s - 2^bits log 2| <= bits + 2 (series sum 1/(k 2^k))."""
    return sum((1 << (bits - k)) // k for k in range(1, bits)), bits + 2


def modp(x, p):
    return x.numerator % p * pow(x.denominator % p, -1, p) % p


def lll(basis, delta=Q(99, 100)):
    """Exact LLL reduction of a list of integer row vectors."""
    b = [list(r) for r in basis]
    n = len(b)

    def dot(x, y):
        return sum(i * j for i, j in zip(x, y))

    def gso():
        bs, mu, bb = [], [[Q(0)] * n for _ in range(n)], []
        for i in range(n):
            w = [Q(x) for x in b[i]]
            for j in range(i):
                mu[i][j] = Q(dot(b[i], bs[j])) / bb[j] if bb[j] else Q(0)
                w = [x - mu[i][j] * y for x, y in zip(w, bs[j])]
            bs.append(w)
            bb.append(dot(w, w))
        return mu, bb

    mu, bb = gso()
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            r = round(mu[k][j])
            if r:
                b[k] = [x - r * y for x, y in zip(b[k], b[j])]
                mu, bb = gso()
        if bb[k] >= (delta - mu[k][k - 1] ** 2) * bb[k - 1]:
            k += 1
        else:
            b[k], b[k - 1] = b[k - 1], b[k]
            mu, bb = gso()
            k = max(k - 1, 1)
    return b


class Shift:
    """Exact data at one cutoff N: cell rows up to 2N, the five shifted prefixes
    Y_i(N) = 2^N f_i(N), and a dyadic enclosure of 2^N log 2."""

    def __init__(self, N):
        self.N = N
        self.rows, _ = basis_rows(2 * N)
        self.Y = tuple(Q(2 ** N) * x for x in self.rows[2 * N])
        self.primes = [p for p in primes_upto(2 * N) if p > 2 and p * p > 2 * N]
        self.bits = 4 * N + 400
        s, err = ln2_fixed(self.bits)
        self.ln2N = Q(s << N, 1 << self.bits)       # 2^N log 2 up to radius below
        self.ln2N_radius = Q(err << N, 1 << self.bits)

    def prefix(self, theta):
        return self.Y[0] + sum(t * y for t, y in zip(theta, self.Y[1:]))

    def error(self, theta):
        e = self.ln2N - self.prefix(theta)
        assert abs(e) > 100 * self.ln2N_radius
        return e

    def band(self, p):
        return (2 * self.N) // p


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def height(theta):
    D = 1
    for t in theta:
        D = D * Q(t).denominator // gcd(D, Q(t).denominator)
    return max([D] + [abs(Q(t) * D).numerator for t in theta])


def evaluate(sh, theta):
    """Exact q_N, the band-by-band support predicted by the Frobenius congruence,
    the height and the shifted error."""
    theta = tuple(Q(t) for t in theta)
    Y = sh.prefix(theta)
    q = Y.denominator
    oq = odd_part(q)
    mismatches = 0
    lost = {}
    if all(t.denominator == 1 for t in theta):
        for p in sh.primes:
            v = sh.band(p)
            residue = modp(value(sh.rows[v], theta), p)
            if (q % p == 0) != (residue != 0):
                mismatches += 1
            if not residue:
                key = "cong" if value(sh.rows[v], theta) else "zero"
                lost[key] = lost.get(key, 0.0) + log(p)
    e = sh.error(theta)
    return {"logq": log(oq) / sh.N, "logH": log(height(theta)) / sh.N,
            "cong": lost.get("cong", 0.0) / sh.N, "zero": lost.get("zero", 0.0) / sh.N,
            "err": float(log(abs(e), 2)) if e else float("-inf"),
            "mism": mismatches, "lost": lost, "theta": theta}


def congruences(sh, theta0, dirs, cancel):
    """For each prime p of the cancelled bands, the affine congruence
    alpha_p + beta_p . z == 0 (mod p) on theta = theta0 + sum z_j dirs[j]."""
    out = []
    for p in sh.primes:
        v = sh.band(p)
        if v not in cancel:
            continue
        row = sh.rows[v]
        alpha = value(row, theta0)
        beta = [sum(d * r for d, r in zip(direction, row[1:])) for direction in dirs]
        bp = [modp(x, p) for x in beta]
        if not any(bp):
            continue                                 # row constant along the family
        out.append((p, modp(alpha, p), bp))
    return out


def crt(pairs):
    x, m = 0, 1
    for r, p in pairs:
        x += m * ((r - x) * pow(m, -1, p) % p)
        m *= p
    return x, m


def solve_family(sh, theta0, dirs, cancel, with_error=False):
    """Choose z in Z^k with all congruences satisfied and theta short; optionally
    also make the shifted error 2^N log 2 - Y_N small (Kannan embedding + LLL)."""
    k = len(dirs)
    cons = congruences(sh, theta0, dirs, cancel)
    # pivot coordinate that is a unit at every prime (drop the rare exceptions)
    j = max(range(k), key=lambda j: sum(log(p) for p, _, bp in cons if bp[j]))
    cons = [c for c in cons if c[2][j]]
    Qmod = 1
    for p, _, _ in cons:
        Qmod *= p
    # w . z == -alpha (mod Q) after scaling coordinate j to 1
    zstar_j, _ = crt([(-a * pow(bp[j], -1, p) % p, p) for p, a, bp in cons])
    others = [crt([(bp[i] * pow(bp[j], -1, p) % p, p) for p, a, bp in cons])[0]
              if i != j else None for i in range(k)]

    def theta_of(z):
        return tuple(t + sum(zi * d[c] for zi, d in zip(z, dirs)) for c, t in enumerate(theta0))

    if k == 1 and not with_error:
        z = zstar_j % Qmod
        if z > Qmod // 2:
            z -= Qmod
        return theta_of([z]), Qmod
    # lattice of z with w.z == 0 mod Q: e_i - r_i e_j (i != j) and Q e_j
    basis = []
    for i in range(k):
        if i == j:
            continue
        vec = [0] * k
        vec[i], vec[j] = 1, -others[i] % Qmod
        basis.append(vec)
    vec = [0] * k
    vec[j] = Qmod
    basis.append(vec)
    target = [0] * k
    target[j] = zstar_j
    if with_error:
        # one extra coordinate W * (shifted error); W ~ expected size of z, so that
        # the reduced vector has error of order one
        assert k >= 2
        W = 2 ** max(1, Qmod.bit_length() // (k - 1))

        def err_lin(z):                                   # -(dirs z) . Y(N)
            return -sum(zi * sum(d[c] * sh.Y[c + 1] for c in range(4))
                        for zi, d in zip(z, dirs))
        e0 = sh.ln2N - sh.prefix(theta0)
        rows = [vec + [round(W * err_lin(vec))] for vec in basis]
        target = target + [round(W * (e0 + err_lin(target)))]
    else:
        rows = basis
    red = lll(rows)
    # Babai nearest plane: subtract the lattice vector closest to the target
    n = len(red)
    bs, bb = [], []
    for i in range(n):
        w = [Q(x) for x in red[i]]
        for j2 in range(i):
            if bb[j2]:
                mu = sum(x * y for x, y in zip(red[i], bs[j2])) / bb[j2]
                w = [x - mu * y for x, y in zip(w, bs[j2])]
        bs.append(w)
        bb.append(sum(x * x for x in w))
    t = list(target)
    for i in range(n - 1, -1, -1):
        c = round(sum(x * y for x, y in zip(t, bs[i])) / bb[i])
        if c:
            t = [x - c * y for x, y in zip(t, red[i])]
    z = t[:k]
    return theta_of(z), Qmod


def check_constructions(Ns):
    print("== 4. Adaptive integer formulas at linear height (exact verification)")
    line = [(0, 0, 0, 1)]
    out = {}
    for N in Ns:
        t0 = time.time()
        sh = Shift(N)
        rows = sh.rows
        # c-line: cells 1..3 vanish identically, cell 4 = 1/2, cells 8..11 = 11/16.
        assert all(value(rows[v], (0, 0, 0, Q(c))) == 0 for v in (1, 2, 3) for c in (-7, 3, 10))
        configs = []
        configs.append(("fixed minimizer (0,0,0,-5)", THETA_MIN, 0, "5/12"))
        configs.append(("fixed runner-up (0,0,0,-2)", THETA_TWO, 0, "13/30"))
        # (L1) c-line: keep bands 6,7 (c == -5 mod p) and cancel band 5 (c == -2 mod p)
        th, M = solve_family(sh, (0, 0, 0, -5), line, {5, 6, 7})
        configs.append(("c-line, cancel v=5,6,7 (CRT)", th, M, "1/2-3/20 = 7/20"))
        # (L2) c-line: cancel every band v >= 5 (cells 4, 8..11 are constant on the line)
        allv = set(range(5, isqrt(2 * N) + 2))
        th, M = solve_family(sh, (0, 0, 0, -5), line, allv)
        configs.append(("c-line, cancel all v>=5 (CRT)", th, M, "11/60"))
        # (P) u = 0: cancel every band v >= 2 with three free integers, LLL + Babai
        u0 = [(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
        allv2 = set(range(2, isqrt(2 * N) + 2))
        th, M = solve_family(sh, (0, 0, 0, 0), u0, allv2)
        configs.append(("u=0, cancel all v>=2 (LLL)", th, M, "0"))
        # (E) error-constrained: plane {u = a = 0} (cell 2 = a/2), cancel 3,5,6,7
        r2 = rows[2]
        plane = [(0, 0, 1, 0), (0, 0, 0, 1)]
        assert r2[0] == 0 and r2[3] == 0 and r2[4] == 0 and r2[1] != 0
        th, M = solve_family(sh, (0, 0, 0, -5), plane, {3, 5, 6, 7}, with_error=True)
        configs.append(("plane u=a=0, cancel 3,5,6,7, |err|<~1", th, M, "7/20"))
        th, M = solve_family(sh, (0, 0, 0, -5), plane, {3, 4, 5, 6, 7}, with_error=True)
        configs.append(("plane u=a=0, cancel 3..7, |err|<~1", th, M, "1/4"))
        th, M = solve_family(sh, (0, 0, 0, 0), u0, allv2, with_error=True)
        configs.append(("u=0, cancel all v>=2, |err|<~1 (LLL)", th, M, "0"))
        print("   N = %d   (%d odd primes with p^2 > 2N; %.1fs setup)"
              % (N, len(sh.primes), time.time() - t0))
        print("     %-40s %7s %7s %7s %7s %7s %9s %4s  %s"
              % ("formula", "logq/N", "logH/N", "logM/N", "cong/N", "zero/N", "log2|err|",
                 "mism", "limit rate"))
        for name, th, M, rate in configs:
            r = evaluate(sh, th)
            assert r["mism"] == 0
            out[(N, name)] = r
            print("     %-40s %7.4f %7.4f %7.4f %7.4f %7.4f %9.1f %4d  %s"
                  % (name, r["logq"], r["logH"], log(M) / N if M else 0.0, r["cong"],
                     r["zero"], r["err"], r["mism"], rate))
        print("     (%.1fs)" % (time.time() - t0))
    return out


W_SIGNS = (1, 1, 0, -1, -1, -1, 0, 1)     # Re((1+i)^j) = W_SIGNS[j % 8] 2^(j//2)
DIRECTIONS = {   # zero-limit directions f_i as combinations of (A1,A2,A3,A4,A6,G1,G2,G3)
    "a": (1, -2, -1, 0, 1, 0, 0, 0),     # A1 - B
    "u": (0, -2, -1, 0, 1, 1, 0, 0),     # G1 - B
    "b": (0, -1, -1, -1, 1, 0, 1, 0),    # G2 + A2 - A4 - B
    "c": (0, 0, -1, -2, 1, 0, 0, 1),     # G3 + 2A2 - 2A4 - B
}


def tail_limits(N):
    """Exact lim N 2^N (s(inf) - s(N)) along N' = N mod 120, for the eight sources.

    A_k: k 2^(N mod k) / (2^k - 1).  G_t (n = 2t-1, J = floor(2N/n)):
    n sum_{j>J} W_j 2^(N - ceil(nj/2)), summed over one period of eight.
    """
    out = []
    for k in (1, 2, 3, 4, 6):
        out.append(Q(k * 2 ** (N % k), 2 ** k - 1))
    for t in (1, 2, 3):
        n = 2 * t - 1
        J = 2 * N // n
        block = sum((Q(W_SIGNS[j % 8] * 2 ** N, 2 ** (-(-n * j // 2))) for j in range(J + 1, J + 9)),
                    Q(0))
        out.append(n * block / (1 - Q(1, 2 ** (4 * n))))
    return out


def check_tails(Ns):
    print("== 5. Shifted tails: the error of an adaptive formula")
    # Y_N = Y_0(N) + theta . Y(N) with Y_i(N) = 2^N f_i(N) rational (f_i(inf) = 0), so
    # 2^N log 2 - Y_N = E_0(N) - theta . Y(N).  N Y_i(N) tends to a function g_i of N mod 60.
    def g(N):
        lim = tail_limits(N)
        return {d: -sum(c * x for c, x in zip(co, lim)) for d, co in DIRECTIONS.items()}
    period = [g(N) for N in range(600, 660)]
    assert all(g(N + 60) == period[N % 60] for N in range(600, 720)
               ) and all(g(N) == period[N % 60] for N in range(600, 720))
    gmin = {d: min(abs(x[d]) for x in period) for d in DIRECTIONS}
    print("   lim N*Y_i(N) is 60-periodic; min over residues of |g_i|: "
          + ", ".join("%s: %s (%.4f)" % (d, gmin[d], float(gmin[d])) for d in DIRECTIONS))
    assert all(x > 0 for x in gmin.values())
    for N in Ns:
        sh = Shift(N)
        Y = dict(zip(NAMES, sh.Y[1:]))
        gN = period[N % 60]
        dev = max(abs(N * Y[d] - gN[d]) for d in NAMES)
        assert dev * N < 60            # O(1/N) convergence, constant checked here
        print("   N=%d: N*Y(N) = (%s), max |N Y_i - g_i| = %.4f"
              % (N, ", ".join("%.4f" % float(N * Y[d]) for d in NAMES), float(dev)))
        # small combinations exist (Dirichlet): LLL on [I | W Y]
        W = 2 ** (N // 2)
        rows = [[int(i == j) for j in range(4)] + [round(W * Y[NAMES[i]])] for i in range(4)]
        red = lll(rows)
        best = min(red, key=lambda r: max(map(abs, r[:4])))
        comb = sum(t * Y[d] for t, d in zip(best[:4], NAMES))
        print("     a short theta with tiny theta.Y(N): height %d, |theta.Y(N)| = %.3g"
              % (max(map(abs, best[:4])), float(abs(comb))))
    print("   on the c-line, |error| >= |c| min|g_c|/(2N) - O(1): a subexponential error forces"
          " log|c| = o(N)")


def check_collapse():
    """1(b): a raw identity with huge coefficients on large strides and zero-sum
    padding collapses to its four touching coordinates."""
    print("== 1b. Raw identities: the collapsed height reads only 16 small sources")
    V = 160

    def src(key, v):
        if key[0] == "A":
            return real_sum_v(key[1], v, key[2])
        return gaussian_sum_v(key[1], v, key[2])     # key[3] = conjugate phase flag

    theta0 = (Q(3, 7), Q(-1, 2), Q(-2), Q(5))
    co = normal_coefficients(theta0)
    raw = {}

    def add(key, c):
        raw[key] = raw.get(key, 0) + c
    for c, k in zip(co[:5], (1, 2, 3, 4, 6)):
        add(("A", k, 1), c)
    for c, t in zip(co[5:], (1, 2, 3)):
        add(("G", t, 1, False), c - 7)
        add(("G", t, 1, True), 7)                   # the conjugate phase (1-i)/2^t
    K = 10 ** 30
    for k in (1, 25):                                # A_{k,+} + A_{k,-} - A_{2k} = 0
        add(("A", k, 1), K); add(("A", k, -1), K); add(("A", 2 * k, 1), -K)
    for t in (1, 9):                                 # G_{t,+} + G_{t,-} - A_{2n,-} = 0
        n = 2 * t - 1
        add(("G", t, 1, False), K); add(("G", t, -1, True), K); add(("A", 2 * n, -1), -K)
    for m in (17,):                                  # A_{m,-} - A_{2m} + A_m = 0
        add(("A", m, -1), Q(K, 3)); add(("A", 2 * m, 1), -Q(K, 3)); add(("A", m, 1), Q(K, 3))
    for v in range(V):
        assert sum(c * src(key, v) for key, c in raw.items()) == value(ROWS[v], theta0)

    def coord(t):
        return sum(c * (1 if key[2] == 1 else -1) for key, c in raw.items()
                   if key[0] == "G" and key[1] == t)
    a = raw.get(("A", 1, 1), 0) - raw.get(("A", 1, -1), 0)
    theta = (a, coord(1), coord(2), coord(3))
    assert theta == theta0
    touching = [c for key, c in raw.items() if key[1] == 1 or (key[0] == "G" and key[1] <= 3)]
    D = 1
    for c in raw.values():
        D = D * Q(c).denominator // gcd(D, Q(c).denominator)
    Hraw = max([D] + [abs(Q(c) * D).numerator for c in raw.values()])
    Dt = 1
    for c in touching:
        Dt = Dt * Q(c).denominator // gcd(Dt, Q(c).denominator)
    Ht = max([Dt] + [abs(Q(c) * Dt).numerator for c in touching])
    assert height(theta) <= 4 * Ht
    print("   %d raw sources, max stride %d, log10 H_raw = %.1f; collapsed theta = (%s),"
          " H_N = %d <= 4 H_touch; identity checked on %d cells"
          % (len(raw), max(key[1] for key in raw), log(Hraw, 10),
             ", ".join(map(str, theta)), height(theta), V))


def real_sum_v(k, v, sign=1):
    return sum((Q(sign ** j, j << (k * j)) for j in range(1, v // (2 * k) + 1)), Q())


def gaussian_sum_v(t, v, sign=1):
    a, b = 1, 0
    total = Q()
    for j in range(1, v // (2 * t - 1) + 1):
        a, b = sign * (a - b), sign * (a + b)
        total += Q(2 * a, j << (t * j))
    return total


def check_frontier():
    """Heuristic frontier (option --frontier, a few minutes): over every affine family F
    cut out by zero cells v <= 71 (all hyperplanes, planes and lines), the generic active
    mass M_F (cells v <= 120 not identically zero on F, plus the tail 2/121) and
    min (M_F - 5/12)/dim F.  Under the generic-lattice heuristic a k-dimensional family
    cancels about k log H, so this is the conjectural critical exponent."""
    print("== 6. Heuristic frontier over all zero-cell families (lines, planes, spaces)")
    rows, _ = basis_rows(130)
    VM = 120

    def rref(eqs):
        M = [list(e) for e in eqs]
        r = 0
        for col in (1, 2, 3, 4):
            p = next((i for i in range(r, len(M)) if M[i][col]), None)
            if p is None:
                continue
            M[r], M[p] = M[p], M[r]
            M[r] = [x / M[r][col] for x in M[r]]
            for i in range(len(M)):
                if i != r and M[i][col]:
                    M[i] = [x - M[i][col] * y for x, y in zip(M[i], M[r])]
            r += 1
        if any(M[i][0] for i in range(r, len(M))):
            return None
        return tuple(tuple(x) for x in M[:r])

    def active_mass(F):
        total = Q(2, VM + 1)
        for v in range(1, VM + 1):
            r = rows[v]
            for e in F:
                col = next(k for k in (1, 2, 3, 4) if e[k])
                if r[col]:
                    r = tuple(x - r[col] * y for x, y in zip(r, e))
            if any(r):
                total += mass(v)
        return total
    hyper = {rref([rows[v]]) for v in range(1, 72)} - {None}
    planes = {F for A in hyper for B in hyper
              for F in [rref(list(A) + list(B))] if F and len(F) == 2}
    lines = {F for P in planes for A in hyper
             for F in [rref(list(P) + list(A))] if F and len(F) == 3}
    best = {4: active_mass(())}
    for k, fams in ((3, hyper), (2, planes), (1, lines)):
        best[k] = min(active_mass(F) for F in fams)
    print("   families: %d hyperplanes, %d planes, %d lines"
          % (len(hyper), len(planes), len(lines)))
    for k in (1, 2, 3, 4):
        free = (best[k] - Q(5, 12)) / k
        err = (best[k] - Q(5, 12)) / (k - 1) if k > 1 else None
        print("   dim %d: min M_F = %s, (M-5/12)/k = %s, with error (M-5/12)/(k-1) = %s"
              % (k, best[k], free, err))
    assert best[1] == Q(1, 2) and best[2] == Q(2, 3) and best[3] == 1 and best[4] == 2


if __name__ == "__main__":
    T0 = time.time()
    rows, s = basis_rows(400)
    ROWS = rows
    check_rows(rows, s)
    check_collapse()
    check_uniform_bound(rows)
    check_threshold(rows)
    Ns = (120, 240) if QUICK else (120, 240, 480)
    check_constructions(Ns)
    check_tails(Ns)
    if "--frontier" in sys.argv:
        check_frontier()
    print("All Phase 16 adaptive-logarithm checks passed (%.1fs)." % (time.time() - T0))
