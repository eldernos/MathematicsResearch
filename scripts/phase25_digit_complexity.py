#!/usr/bin/env python3
"""Phase 25 Track D: digit complexity, middle-interval orbit formulas, exact LP discrepancy
certificates, carry-aware functionals and multi-radix finite-order compatibility.

Companion to notes/phase25/digit-complexity-and-lp-witnesses.md.

Pure Python 3 standard library.  Every certificate is checked in exact integer or
fractions.Fraction arithmetic.  Every printed bound is rounded OUTWARD (lo(): floor for lower
bounds, hi(): ceiling for upper bounds), and the rounding direction is itself checked exactly;
floating point appears only in the random-trial weights of D1.2 (instances are verified exactly).  Random
searches use fixed seeds and are verified exactly afterwards, so a found witness is a
certificate regardless of how it was found.

Run:  python -B scripts/phase25_digit_complexity.py     (exit code 0 iff every check passes)
"""

import random
import sys
from collections import Counter
from fractions import Fraction as Fr

FAILS = []
COUNT = [0]


def check(cond, msg):
    COUNT[0] += 1
    if not cond:
        FAILS.append(msg)
        print("  FAIL:", msg)


def head(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def _dec_floor(q, n):
    """Exact floor of the rational q to n decimals, as a Fraction."""
    q = Fr(q)
    s = 10 ** n
    return Fr((q.numerator * s) // q.denominator, s)


def _dec_ceil(q, n):
    q = Fr(q)
    s = 10 ** n
    return Fr(-((-q.numerator * s) // q.denominator), s)


def _fmt(d, n):
    sign = "-" if d < 0 else ""
    d = abs(d)
    s = 10 ** n
    ip, fp = divmod(d.numerator * s // d.denominator, s)
    return "%s%d.%0*d" % (sign, ip, n, fp)


def lo(q, n=6):
    """Outward rounding for a LOWER bound: the printed decimal d satisfies d <= q (checked exactly)."""
    d = _dec_floor(q, n)
    check(d <= Fr(q) < d + Fr(1, 10 ** n), "outward floor rounding to %s (%d decimals)" % (_fmt(d, n), n))
    return _fmt(d, n)


def hi(q, n=6):
    """Outward rounding for an UPPER bound: the printed decimal d satisfies d >= q (checked exactly)."""
    d = _dec_ceil(q, n)
    check(d - Fr(1, 10 ** n) < Fr(q) <= d, "outward ceiling rounding to %s (%d decimals)" % (_fmt(d, n), n))
    return _fmt(d, n)


def dec(s):
    """Exact Fraction of a decimal literal such as '0.058103'."""
    ip, _, fp = s.partition(".")
    return Fr(int(ip + fp), 10 ** len(fp)) if fp else Fr(int(ip))


INF = 10 ** 9

# ---------------------------------------------------------------------------
# Generic signed-digit carry DP (free boundary)  a_i = d_i + b*delta_{i-1} - delta_i, |a_i| <= B
# ---------------------------------------------------------------------------


def carries(b, B):
    """Carry range forced by |a'| <= B and digits not ending in (b-1)^infinity."""
    return (-1, 0, 1) if B == b - 1 else (-1, 0)


def dp_step(vec, d, b, B, C):
    out = []
    for dp in C:
        best = INF
        for i, dl in enumerate(C):
            if vec[i] >= INF:
                continue
            a = d + b * dl - dp
            if -B <= a <= B:
                c = vec[i] + (1 if a else 0)
                if c < best:
                    best = c
        out.append(best)
    return out


def dp_vector(digs, b=2, B=1):
    C = carries(b, B)
    v = [0] * len(C)
    for d in digs:
        v = dp_step(v, d, b, B, C)
    return v


def sigma_free(digs, b=2, B=1):
    return min(dp_vector(digs, b, B))


def sigma_exact(digs, N, b, B):
    """Exact sigma_B(x;N) for the finite b-adic rational x = 0.d_1...d_M (M = len(digs))."""
    C = carries(b, B)
    v = dp_vector(digs[:N], b, B)
    M = len(digs)
    tail = 0
    for d in digs[N:]:
        tail = tail * b + d
    scale = b ** (M - N)
    best = INF
    for i, dl in enumerate(C):
        # tail value t = tail/scale; need t + dl in [-B/(b-1), B/(b-1)]
        val = (tail + dl * scale) * (b - 1)
        if -B * scale <= val <= B * scale and v[i] < best:
            best = v[i]
    return best


def sigma_exact_rational(p, q, N, b, B):
    """Exact sigma_B(x;N) for an arbitrary rational x = p/q in [0,1) (periodic expansions allowed).
    By Lemma 1.1 an admissible a' is a carry path delta_0..delta_N in C(b,B) with digits in [-B,B]
    on positions 1..N and residual r_N = t_N + delta_N in [-B/(b-1), B/(b-1)] (every such value is a
    [-B,B]-digit tail because 2B+1 >= b)."""
    C = carries(b, B)
    digs = []
    r = p
    for _ in range(N):
        r *= b
        digs.append(r // q)
        r %= q
    v = dp_vector(digs, b, B)
    best = INF
    for i, dl in enumerate(C):
        val = (r + dl * q) * (b - 1)          # (t_N + delta_N) * q * (b-1), t_N = r/q
        if -B * q <= val <= B * q and v[i] < best:
            best = v[i]
    return best


def orbit_numerators_rational(p, q, N, b):
    """Numerators of t_n = {b^n p/q} over q, 0 <= n <= N."""
    out = []
    r = p % q
    for _ in range(N + 1):
        out.append(r)
        r = (r * b) % q
    return out


def orbit_points(digs, N, b):
    """Numerators of {b^n x}, 0 <= n < N, over the common denominator b^M (x = 0.d_1..d_M)."""
    M = len(digs)
    X = 0
    for d in digs:
        X = X * b + d
    mod = b ** M
    pts = []
    for n in range(N):
        pts.append((X * pow(b, n, mod)) % mod)
    return pts, mod


# ---------------------------------------------------------------------------
# Base-2 4-state transducer (Phase 24, GF-40), re-derived and checked here
# ---------------------------------------------------------------------------
A_, B_, C_, D_ = 0, 1, 2, 3
SNAME = "ABCD"
T4 = {A_: {0: (C_, 0), 1: (B_, 0)},
      B_: {0: (A_, 1), 1: (B_, 0)},
      C_: {0: (C_, 0), 1: (D_, 0)},
      D_: {0: (C_, 1), 1: (B_, 1)}}


def t4_cost(bits, s=A_):
    tot = 0
    for x in bits:
        s, c = T4[s][x]
        tot += c
    return tot


def int_bits(w, L):
    return [(w >> (L - 1 - i)) & 1 for i in range(L)]


def count10(bits):
    return sum(1 for i in range(len(bits) - 1) if bits[i] == 1 and bits[i + 1] == 0)


def count_type_changes(bits, prefix0=True):
    """Number of 11-pairs whose last preceding doubled pair is 00 (= occurrences of 00(10)^j11).
    With prefix0, a virtual leading 0 is prepended (the free-boundary start)."""
    s = ([0] if prefix0 else []) + list(bits)
    typ = None
    cnt = 0
    for i in range(len(s) - 1):
        if s[i] == s[i + 1]:
            if s[i] == 1 and typ == 0:
                cnt += 1
            typ = s[i]
    return cnt


def count_patterns_direct(bits, prefix0=True):
    s = ([0] if prefix0 else []) + list(bits)
    n = len(s)
    cnt = 0
    for i in range(n):
        j = 0
        while True:
            p = [0, 0] + [1, 0] * j + [1, 1]
            if i + len(p) > n:
                break
            if s[i:i + len(p)] == p:
                cnt += 1
            j += 1
    return cnt


def cyclic_cost(word):
    """Steady-state signed cost per lap of the periodic word (= P * lim sigma_1/N)."""
    s = A_
    seen = {}
    laps = []
    lap = 0
    while s not in seen:
        seen[s] = lap
        tot = 0
        for x in word:
            s, c = T4[s][x]
            tot += c
        laps.append(tot)
        lap += 1
    start = seen[s]
    cyc = laps[start:]
    return Fr(sum(cyc), len(cyc))


def section_D1_transducer():
    head("D1.1  4-state transducer, exact descent-pattern formula, DP spread")
    # 7 reachable normalized DP vectors (base 2, B=1)
    C = carries(2, 1)
    reach = {(0, 0, 0)}
    todo = [(0, 0, 0)]
    while todo:
        v = todo.pop()
        for x in (0, 1):
            nv = dp_step(list(v), x, 2, 1, C)
            m = min(nv)
            t = tuple(y - m for y in nv)
            if t not in reach:
                reach.add(t)
                todo.append(t)
    check(len(reach) == 7, "base-2 DP closes at 7 normalized vectors")
    check(all(max(v) - min(v) <= 1 for v in reach),
          "every reachable normalized DP vector has spread <= 1 (gives sigma_1 <= sigma_free + 1)")
    # transducer reproduces sigma_free; pattern formula; direct pattern count
    n_words = 0
    for L in range(1, 15):
        for w in range(1 << L):
            bits = int_bits(w, L)
            sf = sigma_free(bits)
            n_words += 1
            if t4_cost(bits) != sf:
                check(False, "4-state transducer = sigma_free at %s" % bits)
            if count10(bits) + count_type_changes(bits) != sf:
                check(False, "descent-pattern formula at %s" % bits)
            if L <= 11 and count_type_changes(bits) != count_patterns_direct(bits):
                check(False, "type-change count = #00(10)^j11 at %s" % bits)
    check(True, "transducer & pattern formula verified on all %d words of length <= 14" % n_words)
    print("  sigma_free(w) = #10(w) + #{00(10)^j 11 in 0w}: verified on all %d words, L <= 14" % n_words)


# ---------------------------------------------------------------------------
# D1.2 / D2.3  Middle-interval orbit formulas (all bases)
# ---------------------------------------------------------------------------


def section_orbit_formulas():
    head("D1.2  Orbit formulas: sigma_B(x;N) versus visits of {b^n x} to a middle interval")
    rng = random.Random(25001)
    worst = Counter()
    trials = 0
    for b in range(2, 8):
        for B in range(b // 2, b):
            for t in range(50):
                M = rng.randint(8, 46)
                mode = t % 3
                if mode == 0:
                    digs = [rng.randrange(b) for _ in range(M)]
                elif mode == 1:
                    wts = [rng.random() ** 3 for _ in range(b)]
                    digs = rng.choices(range(b), weights=wts, k=M)
                else:
                    digs = []
                    while len(digs) < M:
                        digs += [rng.randrange(b)] * rng.randint(1, 5)
                    digs = digs[:M]
                pts, mod = orbit_points(digs, M, b)
                for N in range(1, M + 1):
                    trials += 1
                    s = sigma_exact(digs, N, b, B)
                    if B <= b - 2:
                        # ||b^n x|| > B/(b(b-1))  <=>  B*mod < b(b-1)*p < (b(b-1)-B)*mod
                        q = b * (b - 1)
                        K = sum(1 for p in pts[:N] if B * mod < q * p < (q - B) * mod)
                        if s != K:
                            check(False, "exact formula sigma_B = #{||b^n x|| > theta} b=%d B=%d %s N=%d" % (b, B, digs, N))
                    else:
                        K = sum(1 for p in pts[:N] if mod <= (b + 1) * p < b * mod)
                        worst[(b, "K_I - sigma")] = max(worst[(b, "K_I - sigma")], K - s)
                        if not (K - 1 <= s <= K):
                            check(False, "K_I - 1 <= sigma_{b-1} <= K_I  b=%d %s N=%d" % (b, digs, N))
                        if b == 2:
                            K6 = sum(1 for p in pts[:N] if mod <= 6 * p < 5 * mod)
                            e = 2 * s - K6
                            worst["max 2s-K6"] = max(worst.get("max 2s-K6", -INF), e)
                            worst["min 2s-K6"] = min(worst.get("min 2s-K6", INF), e)
                            worst["|K6-2K3|"] = max(worst["|K6-2K3|"], abs(K6 - 2 * K))
                            if not (-2 <= e <= 1) or abs(K6 - 2 * K) > 1:
                                check(False, "-2 <= 2 sigma_1 - K_6 <= 1 and |K_6 - 2K_3| <= 1 at %s N=%d" % (digs, N))
    check(True, "orbit formulas verified on %d exact (x, N) instances, b = 2..7" % trials)
    print("  %d exact instances (b = 2..7, all B in [floor(b/2), b-1]); exact sigma_B via tail-constrained DP" % trials)
    print("  B <= b-2: sigma_B(x;N) = #{n<N: ||b^n x|| > B/(b(b-1))}  (equality in every instance)")
    print("  B = b-1 : K_I - 1 <= sigma_{b-1} <= K_I, I = [1/(b+1), b/(b+1));  max(K_I - sigma) =",
          max(v for k, v in worst.items() if isinstance(k, tuple)))
    print("  base 2  : 2 sigma_1 - K_6 ranges over [%d, %d] (proved in [-2, 1]), max |K_6 - 2K_3| = %d (proved <= 1)"
          % (worst["min 2s-K6"], worst["max 2s-K6"], worst["|K6-2K3|"]))

    # Deterministic suite on exact periodic and boundary rationals.  Finite b-adic rationals never
    # land on the critical endpoints theta, 1-theta, 1/(b+1), b/(b+1), 1/6, 5/6, so these are tested here.
    # Sanity: the rational DP agrees with the finite-expansion DP on finite b-adic rationals.
    agree = True
    for b in range(2, 6):
        for B in range(b // 2, b):
            for X in range(b ** 4):
                digs = [(X // b ** (3 - i)) % b for i in range(4)]
                for N in range(1, 5):
                    if sigma_exact(digs, N, b, B) != sigma_exact_rational(X, b ** 4, N, b, B):
                        agree = False
    check(agree, "rational tail-constrained DP agrees with the finite-expansion DP (b <= 5, 4 digits)")
    rat_trials = 0
    ext = {"min": INF, "max": -INF, "KI": 0}
    for b in range(2, 8):
        for B in range(b // 2, b):
            pts = set()
            for q in range(1, 25):
                for p in range(q):
                    pts.add(Fr(p, q))
            special = [Fr(1, 2), Fr(1, 3), Fr(2, 3), Fr(1, 6), Fr(5, 6), Fr(1, b + 1), Fr(b, b + 1),
                       Fr(1, 7), Fr(3, 7), Fr(1, 13), Fr(5, 12), Fr(1, b - 1) % 1 if b > 2 else Fr(0)]
            if B <= b - 2:
                th = Fr(B, b * (b - 1))
                special += [th, 1 - th, th / b, Fr(1, 2) - th, Fr(1, 2) + th]
                special += [Fr(k, b * (b - 1)) for k in range(b * (b - 1))]
            pts.update(special)
            for x in sorted(pts):
                p, q = x.numerator, x.denominator
                tn = orbit_numerators_rational(p, q, 12, b)
                for N in range(1, 13):
                    rat_trials += 1
                    s = sigma_exact_rational(p, q, N, b, B)
                    if B <= b - 2:
                        qq = b * (b - 1)
                        K = sum(1 for t in tn[:N] if B * q < qq * t < (qq - B) * q)
                        if s != K:
                            check(False, "rational suite: sigma_B = #{||b^n x|| > theta} b=%d B=%d x=%s N=%d" % (b, B, x, N))
                    else:
                        K = sum(1 for t in tn[:N] if q <= (b + 1) * t < b * q)
                        ext["KI"] = max(ext["KI"], K - s)
                        if not (K - 1 <= s <= K):
                            check(False, "rational suite: K_I - 1 <= sigma_{b-1} <= K_I b=%d x=%s N=%d" % (b, x, N))
                        if K - s == 1 and q <= (b + 1) * tn[N] < b * q:
                            check(False, "rational suite: sigma = K_I - 1 forces t_N not in I_b, b=%d x=%s N=%d" % (b, x, N))
                        if b == 2:
                            K6 = sum(1 for t in tn[:N] if q <= 6 * t < 5 * q)
                            e = 2 * s - K6
                            ext["min"] = min(ext["min"], e)
                            ext["max"] = max(ext["max"], e)
                            if not (-2 <= e <= 1) or abs(K6 - 2 * K) > 1:
                                check(False, "rational suite: -2 <= 2 sigma_1 - K_6 <= 1 at x=%s N=%d" % (x, N))
    check(True, "orbit formulas on %d exact rational (x, N) instances incl. periodic and boundary points" % rat_trials)
    check(ext["min"] == -2 and ext["max"] == 1, "base 2: the range [-2, 1] of 2 sigma_1 - K_J is attained")
    check(ext["KI"] == 1, "B = b-1: the defect K_I - sigma = 1 is attained")
    # the two explicit attainment examples of the note
    check(2 * sigma_exact_rational(1, 4, 2, 2, 1) - 2 == -2, "x = 1/4, N = 2: sigma_1 = 0, K_J = 2 (value -2)")
    check(2 * sigma_exact_rational(1, 2, 2, 2, 1) - 1 == 1, "x = 1/2, N = 2: sigma_1 = 1, K_J = 1 (value +1)")
    print("  rational suite: %d instances (b = 2..7, all B, x = p/q with q <= 24 plus theta, 1-theta, 1/(b+1)," % rat_trials)
    print("    b/(b+1), 1/6, 5/6, ...; N <= 12): all formulas hold; base 2: 2 sigma_1 - K_J in [%d, %d]"
          % (ext["min"], ext["max"]))
    print("    (attained: x = 1/4, N = 2 gives -2; x = 1/2, N = 2 gives +1); sigma = K_I - 1 => t_N not in I_b")


# ---------------------------------------------------------------------------
# D1.3  Exact averages A(b,B), finite windows A_L(b,B), Bernoulli / Markov laws
# ---------------------------------------------------------------------------


def automaton(b, B):
    C = carries(b, B)
    start = tuple(0 for _ in C)
    idx = {start: 0}
    order = [start]
    trans = {}
    i = 0
    while i < len(order):
        v = order[i]
        i += 1
        for d in range(b):
            nv = dp_step(list(v), d, b, B, C)
            m = min(nv)
            t = tuple(y - m for y in nv)
            if t not in idx:
                idx[t] = len(order)
                order.append(t)
            trans[(idx[v], d)] = (idx[t], m)
    return order, trans


def solve_linear(Mat, rhs):
    n = len(Mat)
    A = [row[:] + [rhs[i]] for i, row in enumerate(Mat)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [A[i][n] for i in range(n)]


def stationary_cost(nstates, trans_prob):
    """trans_prob: dict s -> list of (prob, next, cost).  Returns stationary expected cost
    on the (unique) closed class reachable from state 0."""
    reach = {0}
    todo = [0]
    while todo:
        s = todo.pop()
        for p, t, c in trans_prob[s]:
            if p and t not in reach:
                reach.add(t)
                todo.append(t)
    # closed class: states from which 0's reach-set is reachable back
    def reach_from(s):
        R = {s}
        st = [s]
        while st:
            u = st.pop()
            for p, t, c in trans_prob[u]:
                if p and t not in R:
                    R.add(t)
                    st.append(t)
        return R
    rec = sorted(s for s in reach if all(s in reach_from(t) for t in reach_from(s)))
    pos = {s: i for i, s in enumerate(rec)}
    k = len(rec)
    Mat = [[Fr(0)] * k for _ in range(k)]
    cost = [Fr(0)] * k
    for s in rec:
        for p, t, c in trans_prob[s]:
            Mat[pos[t]][pos[s]] += p
            cost[pos[s]] += p * c
    for i in range(k):
        Mat[i][i] -= 1
    Mat[-1] = [Fr(1)] * k
    rhs = [Fr(0)] * (k - 1) + [Fr(1)]
    pi = solve_linear(Mat, rhs)
    return sum(p * c for p, c in zip(pi, cost)), k


def A_closed(b, B):
    return Fr(b - 1, b + 1) if B == b - 1 else 1 - Fr(2 * B, b * (b - 1))


def AL_closed(b, B, L):
    if b == 2:
        return Fr(1, 3) - (7 - Fr(-1, 2) ** (L - 1)) / (18 * L)
    if B == b - 1:
        return Fr(b - 1, b + 1) - (b + 3) * (1 - Fr(-1, b) ** L) / ((b + 1) ** 2 * L)
    return A_closed(b, B) - 2 * (b - 1 - B) * (1 - Fr(1, b ** L)) / ((b - 1) ** 2 * L)


def section_averages():
    head("D1.3  Exact averages A(b,B), finite windows A_L(b,B), Bernoulli and Markov laws")
    rows = []
    for b in range(2, 13):
        for B in range(b // 2, b):
            order, trans = automaton(b, B)
            tp = {s: [(Fr(1, b), trans[(s, d)][0], trans[(s, d)][1]) for d in range(b)] for s in range(len(order))}
            A, k = stationary_cost(len(order), tp)
            check(A == A_closed(b, B), "A(%d,%d) closed form" % (b, B))
            check(all(max(v) - min(v) <= 1 for v in order), "DP spread <= 1 for b=%d B=%d" % (b, B))
            if b <= 6:
                rows.append("b=%d B=%d: %d states, A=%s" % (b, B, len(order), A))
    print("  " + "; ".join(rows[:6]))
    print("  " + "; ".join(rows[6:]))
    print("  A(b,B) = 1 - 2B/(b(b-1)) for floor(b/2) <= B <= b-2 and (b-1)/(b+1) for B = b-1: verified b <= 12")
    # finite windows by brute force (uniform average of free-boundary sigma over all b^L words)
    for b, Lmax in ((2, 12), (3, 7), (4, 5), (5, 4), (6, 4), (7, 3)):
        for B in range(b // 2, b):
            for L in range(1, Lmax + 1):
                tot = 0
                for w in range(b ** L):
                    digs = []
                    x = w
                    for _ in range(L):
                        digs.append(x % b)
                        x //= b
                    tot += sigma_free(digs, b, B)
                check(Fr(tot, L * b ** L) == AL_closed(b, B, L), "A_L(%d,%d) closed form at L=%d" % (b, B, L))
    print("  A_L(b,B) closed forms verified by enumeration (b=2: L<=12; b=3: L<=7; b=4: L<=5; b=5,6: L<=4; b=7: L<=3)")

    # Bernoulli(p) and 2-state Markov digit laws through the 4-state chain on (state,last bit)
    def markov_cost(a, c):
        # joint states (A,0),(C,0),(B,1),(D,1) -> indices 0..3 ; P(0->1)=a, P(1->0)=c
        tp = {0: [(1 - a, 1, 0), (a, 2, 0)],
              1: [(1 - a, 1, 0), (a, 3, 0)],
              2: [(c, 0, 1), (1 - c, 2, 0)],
              3: [(c, 1, 1), (1 - c, 2, 1)]}
        return stationary_cost(4, tp)[0]

    def interval_mass(a, c):
        # nu([1/3,2/3)) = sum_j nu(0(10)^j 11) + nu(1(01)^j 00) for the stationary Markov measure
        p0, p1 = c / (a + c), a / (a + c)
        g = a * c  # one (10) or (01) step pair
        s1 = p0 * a * (1 - c) / (1 - g)          # 0 (10)^j 1 1
        s2 = p1 * c * (1 - a) / (1 - g)          # 1 (01)^j 0 0
        return s1 + s2

    for (a, c) in ((Fr(1, 2), Fr(1, 2)), (Fr(1, 3), Fr(2, 3)), (Fr(1, 5), Fr(4, 5)), (Fr(2, 7), Fr(5, 7)),
                   (Fr(1, 3), Fr(1, 4)), (Fr(2, 5), Fr(1, 7)), (Fr(3, 4), Fr(5, 6))):
        mc = markov_cost(a, c)
        closed = a * c * (2 - a - c) / ((a + c) * (1 - a * c))
        check(mc == closed, "Markov cost closed form at (a,c)=(%s,%s)" % (a, c))
        check(mc == interval_mass(a, c), "Markov cost = nu([1/3,2/3)) at (a,c)=(%s,%s)" % (a, c))
        if a + c == 1:
            p, q = a, c
            check(mc == p * q / (1 - p * q), "Bernoulli cost pq/(1-pq) at p=%s" % p)
    print("  Markov (P(0->1)=a, P(1->0)=c): cost = ac(2-a-c)/((a+c)(1-ac)) = nu([1/3,2/3)); Bernoulli(p): pq/(1-pq)")


# ---------------------------------------------------------------------------
# D1.4  Synchronized windows, sharp signed-cost interval for L-normal numbers
# ---------------------------------------------------------------------------


def gbar_closed(L):
    m = L // 2
    return Fr(1, 3) - Fr(1, 3 * 4 ** m)


def g_tables(Lmax):
    nxt = [[0] * 2 for _ in range(16)]
    for mask in range(16):
        for x in (0, 1):
            nm = 0
            for s in range(4):
                if mask >> s & 1:
                    nm |= 1 << T4[s][x][0]
            nxt[mask][x] = nm
    reach = [[15]]
    for l in range(1, Lmax):
        prev = reach[-1]
        cur = [0] * (1 << l)
        for u in range(1 << l):
            cur[u] = nxt[prev[u >> 1]][u & 1]
        reach.append(cur)
    gs = {}
    for L in range(1, Lmax + 1):
        R = reach[L - 1]
        g = [0] * (1 << L)
        for w in range(1 << L):
            mask = R[w >> 1]
            x = w & 1
            g[w] = min(T4[s][x][1] for s in range(4) if mask >> s & 1)
        gs[L] = g
    return gs


def random_euler(Lw, rng, b=2, mult=1):
    V = b ** (Lw - 1)
    adj = {v: [] for v in range(V)}
    for v in range(V):
        for a in range(b):
            adj[v] += [(v * b + a) % V] * mult
        rng.shuffle(adj[v])
    stack = [0]
    circ = []
    while stack:
        v = stack[-1]
        if adj[v]:
            stack.append(adj[v].pop())
        else:
            circ.append(stack.pop())
    circ.reverse()
    return [u % b for u in circ[1:]]


def all_debruijn(L):
    V = 1 << (L - 1)
    mask = V - 1
    n = 1 << L
    used = {0}
    seq = [0] * L
    res = []

    def dfs(v):
        if len(used) == n:
            res.append(tuple(seq[:n]))
            return
        for a in (0, 1):
            w = (v << 1) | a
            if w not in used:
                used.add(w)
                seq.append(a)
                dfs(w & mask)
                seq.pop()
                used.discard(w)
    dfs(0)
    out = []
    for s in res:
        if len({tuple(s[(i + j) % n] for j in range(L)) for i in range(n)}) == n:
            out.append(s)
    return out


def section_sync_windows():
    head("D1.4  Synchronized windows g_L and the sharp signed cost of L-normal numbers")
    Lmax = 16
    gs = g_tables(Lmax)
    for L in range(1, Lmax + 1):
        check(Fr(sum(gs[L]), 1 << L) == gbar_closed(L), "gbar_L closed form at L=%d" % L)
    print("  gbar_L = 2^-L sum_w g_L(w) = 1/3 - 4^{-floor(L/2)}/3 verified for L <= %d" % Lmax)
    # explicit formula g_L(w) = [w ends 10] + sum_j [w ends 00(10)^j 11]
    for L in range(2, 13):
        for w in range(1 << L):
            bits = int_bits(w, L)
            e = 1 if bits[-2:] == [1, 0] else 0
            j = 0
            while 4 + 2 * j <= L:
                p = [0, 0] + [1, 0] * j + [1, 1]
                if bits[-len(p):] == p:
                    e += 1
                j += 1
            if e != gs[L][w]:
                check(False, "explicit g_L formula at %s" % bits)
    check(True, "g_L(w) = [w ends in 10] + #{j : w ends in 00(10)^j 11}  (L <= 12)")
    # pointwise identity cost(S_t, d_{t+1}) = g_L(window) + [window = w*_L][S_t = D]
    rng = random.Random(25002)
    for L in range(2, 11):
        alt = [1 if (L - 1 - i) % 2 == 0 else 0 for i in range(1, L)]
        wstar = alt + [1]
        ws = int("".join(map(str, wstar)), 2)
        for t in range(30):
            bits = [rng.randint(0, 1) for _ in range(120)] if t % 2 else \
                   sum(([rng.randint(0, 1)] * rng.randint(1, 3) if rng.random() < 0.4 else [0, 1] * rng.randint(1, 8)
                        for _ in range(40)), [])[:150]
            s = A_
            ok = True
            for i, x in enumerate(bits):
                if i >= L - 1:
                    w = int("".join(map(str, bits[i - L + 1:i + 1])), 2)
                    c = T4[s][x][1]
                    if c != gs[L][w] + (1 if (w == ws and s == D_) else 0):
                        ok = False
                s = T4[s][x][0]
            check(ok, "cost = g_L + [w*][D] identity at L=%d" % L)
    print("  pointwise identity cost(S_t,d_{t+1}) = g_L(window) + [window = w*_L][S_t = D] checked (L = 2..10)")
    # inner/outer dyadic approximations of [1/6,5/6)
    for L in range(1, 41):
        n = 1 << L
        # inner: cylinders [w,w+1)/n inside [1/6,5/6);  outer: cylinders meeting [1/6,5/6)
        inner = max(0, (5 * n) // 6 - (-(-n // 6)))
        outer = -(-(5 * n) // 6) - n // 6
        if L <= 14:
            check(inner == sum(1 for w in range(n) if 6 * w >= n and 6 * (w + 1) <= 5 * n) and
                  outer == sum(1 for w in range(n) if 6 * (w + 1) > n and 6 * w < 5 * n),
                  "inner/outer cylinder counts by enumeration at L=%d" % L)
        check(Fr(inner, 2 * n) == gbar_closed(L), "(1/2) inner_L[1/6,5/6) = gbar_L at L=%d" % L)
        check(Fr(outer, 2 * n) == gbar_closed(L) + Fr(1, n), "(1/2) outer_L[1/6,5/6) = gbar_L + 2^-L at L=%d" % L)
    print("  (1/2)|inner_L| = gbar_L and (1/2)|outer_L| = gbar_L + 2^-L for the dyadic approximations of [1/6,5/6), L <= 40")

    # de Bruijn dichotomy and attainment
    rng = random.Random(25003)
    found_min, found_max = {}, {}
    for L in range(2, 11):
        base = gbar_closed(L) * (1 << L)
        tries = 0
        while (L not in found_min or L not in found_max) and tries < 4000:
            tries += 1
            s = random_euler(L, rng)
            c = cyclic_cost(s)
            if c not in (base, base + 1):
                check(False, "de Bruijn dichotomy at L=%d: cost %s" % (L, c))
            if c == base and L not in found_min:
                found_min[L] = s
            if c == base + 1 and L not in found_max:
                found_max[L] = s
        if L >= 4:
            check(L in found_min, "periodic L-normal word with cost exactly 2^L gbar_L at L=%d" % L)
        check(L in found_max, "periodic L-normal word with cost 2^L gbar_L + 1 at L=%d" % L)
    for L in (2, 3):
        allc = {cyclic_cost(s) for s in all_debruijn(L)}
        check(allc == {gbar_closed(L) * (1 << L) + 1}, "all order-%d de Bruijn words have cost 2^L gbar_L + 1" % L)
    for n in range(1, 21):
        word = [0, 0, 0, 1] * n + [1, 1, 1, 0] * n
        check(cyclic_cost(word) == 2 * n, "(0001)^n(1110)^n cyclic cost exactly 2n (density 1/4) at n=%d" % n)
        cnt = Counter(tuple(word[(i + j) % (8 * n)] for j in range(3)) for i in range(8 * n))
        dev = max(abs(Fr(cnt[w], 8 * n) - Fr(1, 8)) for w in [(a, b_, c) for a in (0, 1) for b_ in (0, 1) for c in (0, 1)])
        check(dev <= Fr(1, 4 * n), "(0001)^n(1110)^n has 3-block deviation <= 1/(4n) at n=%d" % n)
    # exact uniformity of 2-blocks forces a 00->11 type change, so cost >= P/4 + 1 for exactly 2-normal cycles
    for P in (4, 8, 12, 16):
        for w in range(1 << P):
            word = int_bits(w, P)
            c2 = Counter((word[i], word[(i + 1) % P]) for i in range(P))
            if len(c2) == 4 and len(set(c2.values())) == 1:
                if cyclic_cost(word) < Fr(P, 4) + 1:
                    check(False, "exactly 2-normal cycle with cost < P/4 + 1: %s" % word)
    check(True, "every exactly 2-normal cyclic word of length P <= 16 has cost >= P/4 + 1")
    print("  de Bruijn words of order L (L=2..10, seeded sampled walks): cost in {2^L gbar_L, 2^L gbar_L + 1}; min attained L=4..10, max L=2..10")
    print("  L = 2,3: every de Bruijn word has cost 2^L gbar_L + 1; exactly 2-normal cycles (P <= 16) have cost >= P/4 + 1;")
    print("  (0001)^n(1110)^n has density exactly 1/4 and 3-block deviation <= 1/(4n): the infimum 1/4 is a limit, not a periodic minimum")
    return gs


# ---------------------------------------------------------------------------
# D2  Exact LP certificates
# ---------------------------------------------------------------------------


def type_update(t, b1, b2):
    return b2 if b1 == b2 else t


def aug_cost(t, w, L):
    b1 = (w >> (L - 1)) & 1
    b2 = (w >> (L - 2)) & 1
    return (1 if (b1, b2) == (1, 0) else 0) + (1 if (b1, b2) == (1, 1) and t == 0 else 0)


def bellman_ford(nv, edges):
    """edges: list of (tail, head, weight) with integer or Fraction weights.  Returns potentials psi
    with psi[head] <= psi[tail] + weight for every edge, or None if a negative cycle exists."""
    psi = [0] * nv
    for it in range(nv + 1):
        changed = False
        for (u, v, w) in edges:
            if psi[u] + w < psi[v]:
                psi[v] = psi[u] + w
                changed = True
        if not changed:
            return psi
    return None


def inner_interval(L):
    n = 1 << L
    return -(-n // 6), (5 * n) // 6   # [jb, jg) : inner dyadic approximation of [1/6, 5/6)


def section_lp():
    head("D2.1  Type-augmented LP: exact dual certificates (canonical interval, z = 2) for L = 4..12")
    out = {}
    for L in (4, 6, 8, 10, 12):
        n = 1 << L
        mask = (1 << (L - 1)) - 1
        jb, jg = inner_interval(L)
        check(Fr(jg - jb, n) == 2 * gbar_closed(L), "|I_L| = 2 gbar_L at L=%d" % L)
        bb = format(jb, "0%db" % L)
        gg = format(jg, "0%db" % L)
        check(bb == "00" + "10" * ((L - 4) // 2) + "11" and gg == "11" + "01" * ((L - 2) // 2),
              "dual support points are 00(10)^{m-2}11 and 11(01)^{m-1} at L=%d" % L)
        V = 2 * (1 << (L - 1))
        edges = []
        for t in (0, 1):
            for w in range(n):
                b1 = (w >> (L - 1)) & 1
                b2 = (w >> (L - 2)) & 1
                tail = t * (mask + 1) + (w >> 1)
                hd = type_update(t, b1, b2) * (mask + 1) + (w & mask)
                q = 2 * aug_cost(t, w, L) - (1 if jb <= w < jg else 0)
                edges.append((tail, hd, q))
        psi = bellman_ford(V, edges)
        check(psi is not None, "Bellman-Ford potentials exist (no negative cycle) at L=%d" % L)
        if psi is None:
            continue
        check(all(psi[v] <= psi[u] + q for (u, v, q) in edges), "exact edge inequalities at L=%d" % L)
        osc = max(psi) - min(psi)
        out[L] = osc
        print("  L=%2d: I_L=[%s,%s)/2^L, |I_L| = %s = 2*gbar_L; potentials verified on %d edges, osc(psi) = %d"
              % (L, bb, gg, Fr(jg - jb, n), len(edges), osc))
    print("  => for every real x, N:  D_N(x;2) >= 2 gbar_L - 2(sigma_1(x;N)+1)/N - osc(psi)/N")

    head("D2.2  Plain window LP at L = 4: explicit certificate D >= (4/3)(5/16 - alpha)")
    gs = g_tables(4)
    g4 = gs[4]
    check([w for w in range(16) if g4[w]] == [2, 3, 6, 10, 14], "g_4 support = {0010,0011,0110,1010,1110}")
    rho = {3: Fr(1), 4: Fr(-1, 3), 11: Fr(-1, 3), 14: Fr(-1, 3)}
    check(sum(rho.values()) == 0 and sum(abs(v) for v in rho.values()) == 2, "rho has mass 0 and variation 2")
    h = [sum(v for j, v in rho.items() if j > w) for w in range(16)]
    K = sum(v * j for j, v in rho.items()) / 16
    check(K == Fr(-5, 12), "K = -5/12")
    edges = [(w >> 1, w & 7, 3 * h[w] + 4 * g4[w]) for w in range(16)]
    check(all(Fr(q).denominator == 1 for (_, _, q) in edges), "plain certificate weights are integers")
    edges = [(u, v, int(q)) for (u, v, q) in edges]
    psi = bellman_ford(8, edges)
    check(psi is not None and all(psi[v] <= psi[u] + q for (u, v, q) in edges),
          "plain L=4 certificate: 3h + 4g >= coboundary")
    print("  3 D >= 3G_3 - G_4 - G_11 - G_14 >= 5/4 - 4 sum mu g   (potentials %s)" % psi)

    head("D2.3  Exact primal certificate at L = 4 (augmented LP optimum = 2(5/16 - alpha) on [9/32, 5/16])")
    base = {(0, 0): ("5/16", -1), (0, 1): ("3/8", -1), (0, 2): ("1/16", 0), (0, 3): ("1/16", 0),
            (0, 4): ("1/16", 0), (0, 5): ("-1/4", 1), (0, 6): ("5/16", -1), (0, 7): ("-1/4", 1),
            (0, 8): ("5/16", -1), (0, 9): ("-1/4", 1), (0, 10): ("-1/4", 1), (0, 13): ("5/16", -1),
            (0, 15): ("-1/4", 1), (1, 0): ("1/16", 0), (1, 6): ("-9/16", 2), (1, 7): ("5/8", -2),
            (1, 8): ("1/16", 0), (1, 11): ("1/16", 0), (1, 12): ("1/16", 0), (1, 13): ("-1/4", 1),
            (1, 14): ("3/8", -1)}
    L = 4
    for alpha in (Fr(9, 32), Fr(304282, 10 ** 6), Fr(908184, 3 * 10 ** 6), Fr(3, 10), Fr(5, 16)):
        nu = {(t, w): Fr(0) for t in (0, 1) for w in range(16)}
        for k, (b0, s0) in base.items():
            nu[k] = Fr(b0) + s0 * alpha
        ok = all(v >= 0 for v in nu.values()) and sum(nu.values()) == 1
        for tp in (0, 1):
            for u in range(8):
                u1 = (u >> 2) & 1
                lhs = sum(nu[(t, (x << 3) | u)] for t in (0, 1) for x in (0, 1) if type_update(t, x, u1) == tp)
                rhs = sum(nu[(tp, (u << 1) | a)] for a in (0, 1))
                ok = ok and lhs == rhs
        cost = sum(nu[(t, w)] * aug_cost(t, w, L) for t in (0, 1) for w in range(16))
        mu = [nu[(0, w)] + nu[(1, w)] for w in range(16)]
        G = [Fr(0)]
        for w in range(16):
            G.append(G[-1] + mu[w] - Fr(1, 16))
        Dg = max(G) - min(G)
        check(ok and cost == alpha and Dg == 2 * (Fr(5, 16) - alpha),
              "L=4 primal feasible with cost alpha and grid discrepancy 2(5/16-alpha) at alpha=%s" % alpha)
    # Table 2.2 (type-augmented row): exact values 2(gbar_L - alpha) at alpha = 0.304282
    a0 = Fr(304282, 10 ** 6)
    tab = {L: 2 * (gbar_closed(L) - a0) for L in (4, 6, 8, 10, 12)}
    check(tab[8] == dec("0.0554985"), "Table 2.2: 2(gbar_8 - 0.304282) = 0.0554985 exactly")
    check([lo(tab[L], 7) for L in (4, 6, 8, 10, 12)] == ["0.0164360", "0.0476860", "0.0554985", "0.0574516", "0.0579399"]
          and lo(2 * (Fr(1, 3) - a0), 7) == "0.0581026", "Table 2.2: exact 7-decimal truncations of 2(gbar_L - alpha)")
    print("  nu(alpha) = nu0 + alpha nu1 (21 entries) is feasible, cost = alpha, D_grid = 2(5/16 - alpha) exactly;")
    print("  with the L = 4 dual this pins LP*_4(alpha) = 2(5/16 - alpha) for 9/32 <= alpha <= 5/16")
    return out


def section_witness():
    head("D2.4  Limitation: explicit periodic witness with sigma-density <= 0.304282")
    P, cost = WITNESS_P, WITNESS_COST
    v = int(WITNESS_HEX, 16)
    bitstr = format(v, "0%db" % P)
    check(len(bitstr) == P, "witness decodes to %d bits" % P)
    bits = [int(ch) for ch in bitstr]
    c = cyclic_cost(bits)
    check(c == cost, "witness cyclic signed cost = %d" % cost)
    alpha = Fr(304282, 10 ** 6)
    check(Fr(cost, P) <= alpha, "witness density %d/%d <= 0.304282" % (cost, P))
    # exact discrepancy of the periodic orbit {2^n x}, x = W/(2^P - 1)
    Mden = (1 << P) - 1
    pts = []
    for n in range(P):
        pts.append(v)
        v = ((v << 1) & Mden) | (v >> (P - 1))
    pts.sort()
    vals = [Fr(i, P) - Fr(p, Mden) for i, p in enumerate(pts, 1)]
    D = Fr(1, P) + max(vals) - min(vals)
    check(D <= WITNESS_DMAX, "periodic-orbit discrepancy D(W) <= %s" % _fmt(WITNESS_DMAX, 6))
    check(D > WITNESS_DMAX - Fr(1, 10 ** 6), "WITNESS_DMAX = 0.059108 is the outward (ceiling) rounding of D(W)")
    check(_dec_floor(D, 12) == Fr(59107954113, 10 ** 12), "D(W) = 0.059107954113...")
    # Theorem 2.6 also holds at alpha = 0.912845/3 (the GF-40 input for E_+(8))
    check(Fr(cost, P) <= Fr(912845, 3 * 10 ** 6), "witness density 4887/16076 <= 0.912845/3")
    check(D >= 2 * (Fr(1, 3) - Fr(cost, P)), "D(W) >= 2(1/3 - density)  (consistency with the orbit theorem)")
    # middle-interval counts over one period
    K6 = sum(1 for p in pts if Mden <= 6 * p < 5 * Mden)
    K3 = sum(1 for p in pts if Mden <= 3 * p < 2 * Mden)
    check(K3 == cost and K6 == 2 * cost, "witness: K_3 = cost and K_6 = 2 cost over one period")
    lb = 2 * (Fr(1, 3) - alpha)
    check(lb == Fr(43577, 750000) and lo(lb) == "0.058102" and lb < dec("0.058103"),
          "literal alpha = 0.304282: 2(1/3 - alpha) = 43577/750000 = 0.0581026..., floor 0.058102")
    lb2 = 2 * (Fr(1, 3) - Fr(912845, 3 * 10 ** 6))
    check(lb2 == Fr(17431, 300000) and lo(lb2) == "0.058103",
          "alpha = 0.912845/3: 2(1/3 - alpha) = 17431/300000 = 0.0581033..., floor 0.058103")
    print("  P = %d, cost = %d (density <= %s <= 0.304282), K_3 = %d, K_6 = %d" % (P, cost, hi(Fr(cost, P)), K3, K6))
    print("  exact D(W) = %s... <= %s" % (lo(D, 12), hi(D)))
    print("  Theorem 2.6: %s <= Delta(0.304282) <= %s ;  %s <= Delta(0.912845/3) <= %s"
          % (lo(lb), hi(D), lo(lb2), hi(D)))
    print("  ratio D(W) / (2(1/3 - density)) = %s...  (truncated)" % lo(D / (2 * (Fr(1, 3) - Fr(cost, P))), 6))
    return D


def section_applications(Dw):
    head("D2.5  Applications: D^- lower bounds (inputs: GF-40 Thm 3.1, GF-36 Thm 7.2 / Prop 8.1)")
    one3 = Fr(1, 3)
    W_gf40 = Fr(912845, 10 ** 6)   # mu_NAF(a_+) <= 0.912845      (GF-40)
    W_gf36 = Fr(908184, 10 ** 6)   # W_+ <= 0.908184              (GF-36)
    cub = {7: Fr(756905, 10 ** 6), 9: Fr(804516, 10 ** 6), 13: Fr(789314, 10 ** 6)}

    def trans_bound(Wm, k):
        best = Fr(0)
        for m in range(2, 40):
            val = 1 - Fr(2, 2 ** m) - (m - 1) * 2 * Wm / k
            best = max(best, val)
        return best

    # Each row: (name, mean majorant W, k, alpha upper bound as stated in the note (ceiling),
    #            D^- lower bound as stated in the note (floor), transition bound as stated (floor) or None).
    # Every stated decimal is checked to be the exact OUTWARD rounding of the exact rational value.
    spec = [("E_+(8)  [GF-40 input]", W_gf40, 3, "0.304282", "0.058103", None),
            ("E_+(8)  [GF-36 input]", W_gf36, 3, "0.302728", "0.061210", None),
            ("E_+(16) [GF-40 input]", W_gf40, 4, "0.228212", "0.210244", "0.043577"),
            ("E_+(16) [GF-36 input]", W_gf36, 4, "0.227046", "0.212574", "0.045908"),
            ("E_+(32) [GF-36 input]", W_gf36, 5, "0.181637", "0.303393", "0.136726"),
            ("E_+(2^16)[GF-36 input]", W_gf36, 16, "0.056762", "0.553143", "0.534431"),
            ("L_+-(8) mod 7", cub[7], 3, "0.252302", "0.162063", None),
            ("L_+-(8) mod 9", cub[9], 3, "0.268172", "0.130322", None),
            ("L_+-(8) mod 13", cub[13], 3, "0.263105", "0.140457", None),
            ("L_+-(16) mod 7", cub[7], 4, "0.189227", "0.288214", "0.121547"),
            ("L_+-(16) mod 9", cub[9], 4, "0.201129", "0.264408", "0.097742"),
            ("L_+-(16) mod 13", cub[13], 4, "0.197329", "0.272009", "0.105343")]
    rows = []
    for name, Wm, k, a_st, d_st, t_st in spec:
        alpha = Wm / k
        new = 2 * (one3 - alpha)
        old = trans_bound(Wm, k)
        check(new > 0, "%s: 2(1/3 - alpha) > 0" % name)
        check(hi(alpha) == a_st and alpha <= dec(a_st), "%s: stated alpha <= %s is the outward (ceiling) rounding" % (name, a_st))
        check(lo(new) == d_st and new >= dec(d_st), "%s: stated D^- >= %s is the outward (floor) rounding" % (name, d_st))
        if t_st is None:
            check(old <= 0, "%s: transition method gives nothing" % name)
        else:
            check(lo(old) == t_st and old >= dec(t_st), "%s: transition bound %s is floor-rounded" % (name, t_st))
        not4 = alpha < gbar_closed(4)
        rows.append((name, alpha, new, old, not4, k))
        print("  %-24s alpha <= %s  D^-(x;2) >= %s   [transition method: %s]  not 4-normal: %s   base 2^k: >= %s"
              % (name, a_st, d_st, lo(old) if old > 0 else "none", not4,
                 lo(new * k / (2 ** k - 1))))
    e8 = rows[0][2]
    check(e8 == Fr(17431, 300000), "D^-(E_+(8);2) >= 17431/300000 = 0.0581033... (GF-40 input)")
    check(e8 / Fr(234, 10 ** 9) > 24 * 10 ** 4, "improvement over 2.34e-7 exceeds 2.4*10^5")
    check(rows[1][2] >= dec("0.061210") and rows[1][2] < dec("0.061211"), "D^-(E_+(8);2) >= 0.061210 (not 0.061211) with GF-36 input")
    check(rows[2][2] >= dec("0.2102"), "D^-(E_+(16);2) >= 0.2102 (GF-40 input)")
    check(rows[3][2] >= dec("0.2125") and rows[3][2] < dec("0.2126"), "D^-(E_+(16);2) >= 0.2125 (not 0.2126) with GF-36 input")
    check(rows[2][2] > Fr(9, 2) * Fr(459, 10000), "D^-(E_+(16);2) > 4.5 x 0.0459 (GF-36 transition bound)")
    check(all(r[2] > Fr(13, 100) for r in rows[6:9]), "cubic L_+-(8): D^- > 0.13 for M = 7, 9, 13")
    check([lo(r[2], 4) for r in rows[6:9]] == ["0.1620", "0.1303", "0.1404"], "cubic L_+-(8): 4-decimal floors")
    check(all(r[4] for r in rows[:4] + rows[6:9]), "alpha < gbar_4 = 5/16: E_+(8), E_+(16), L_+-(8) not 4-normal in base 2")
    # base-8 radix descent (P24-A Prop. 2.4(5)): (3/7) * 0.058103 > 0.0249
    check(Fr(3, 7) * dec("0.058103") > dec("0.0249"), "radix descent: (3/7) * 0.058103 > 0.0249")
    check(lo(rows[5][2], 4) == "0.5531" and lo(rows[5][3], 4) == "0.5344", "k = 16: 0.5531 (signed) vs 0.5344 (transition)")
    # E_+(4) barrier (lower enclosure of the same mean, GF-36: W_+ >= 0.908174)
    W_lo = Fr(908174, 10 ** 6)
    check(W_lo / 2 > one3, "E_+(4): zero-carry signed bound W_+/2 >= 0.454087 > 1/3 (method inapplicable)")
    deficit = W_lo / 2 - one3
    check(lo(deficit) == "0.120753" and lo(deficit, 4) == "0.1207" and deficit < dec("0.120754"),
          "E_+(4): necessary deficit W_lo/2 - 1/3 = 0.1207536..., stated outward as 0.120753 / 0.1207")
    print("  E_+(4): W_+/2 >= %s > 1/3; a certified carry deficit > %s is necessary for this route"
          % (lo(W_lo / 2), lo(deficit)))
    print("  Optimal-constant sandwich: 0.058102 <= Delta(0.304282) <= %s; 0.058103 <= Delta(0.912845/3) <= %s"
          % (hi(Dw), hi(Dw)))


# ---------------------------------------------------------------------------
# D3  Carry-aware functionals
# ---------------------------------------------------------------------------


def section_functionals():
    head("D3  Carry-aware functionals: comparison inequalities and separating families")
    worst = Counter()
    for L in range(1, 15):
        for w in range(1 << L):
            bits = int_bits(w, L)
            s = sigma_free(bits)
            tr = sum(1 for i in range(L - 1) if bits[i] != bits[i + 1])
            n1 = sum(bits)
            n0 = L - n1
            c10 = count10(bits)
            if not (c10 <= s <= min(tr, n0, n1) and 2 * c10 >= tr - 1):
                check(False, "functional inequalities at %s" % bits)
            worst["eq_tr"] += (s == tr and L >= 4)
            worst["eq_half"] += (2 * s <= tr + 1 and L >= 4)
    check(True, "(tr-1)/2 <= #10 <= sigma_free <= min(tr, #0, #1)  (all words L <= 14)")
    print("  all words of length <= 14: (tr-1)/2 <= #10 <= sigma_free <= min(tr, #0, #1)  (both ends attained)")
    print("  words (4 <= L <= 14) with sigma_free = tr: %d; with 2 sigma_free <= tr + 1: %d" % (worst["eq_tr"], worst["eq_half"]))
    fam = {"(0001)": [0, 0, 0, 1], "(0011)": [0, 0, 1, 1], "(01)": [0, 1], "(0^5 1^5)": [0] * 5 + [1] * 5,
           "(0^20 1^20)": [0] * 20 + [1] * 20}
    exp = {"(0001)": Fr(1, 4), "(0011)": Fr(1, 2), "(01)": Fr(1, 2), "(0^5 1^5)": Fr(1, 5), "(0^20 1^20)": Fr(1, 20)}
    for k, wd in fam.items():
        dens = cyclic_cost(wd) / len(wd)
        trd = Fr(sum(1 for i in range(len(wd)) if wd[i] != wd[(i + 1) % len(wd)]), len(wd))
        check(dens == exp[k], "cyclic signed density of %s" % k)
        print("  %-12s sigma-density %-5s transition density %-5s ones %s" % (k, dens, trd, Fr(sum(wd), len(wd))))
    # telescoping coefficients: a(n) = 2^k c(n) - c(n+1) with c(n) = n  (polynomial growth, so (H) holds)
    def naf_w(n):
        n = abs(n)
        w = 0
        while n:
            if n & 1:
                w += 1
                n -= 2 - (n & 3)
            n >>= 1
        return w
    for k in (3, 4, 8):
        M = 400
        a = [(1 << k) * n - (n + 1) for n in range(1, M + 1)]
        lhs = sum(Fr(a[n - 1], 1 << (k * n)) for n in range(1, M + 1))
        check(lhs == 1 - Fr(M + 1, 1 << (k * M)), "telescoping identity sum a(n)2^{-kn} = 1 - (M+1)2^{-kM} (k=%d)" % k)
        check(naf_w(2 ** 20 - 1) == 2 and naf_w(0b1011) == 3, "NAF weight helper")
        mean = Fr(sum(naf_w(x) for x in a), M)
        check(mean / k > Fr(1, 3), "mean coefficient weight / k exceeds 1/3 although x = 1 (k=%d)" % k)
        print("  k=%d: a(n) = (2^k-1)n - 1, x = sum a(n)2^{-kn} = 1 exactly; mean NAF weight (n<=400)/k = %s > 1/3 while sigma_1 = 0"
              % (k, lo(mean / k)))


# ---------------------------------------------------------------------------
# D4  Multi-radix finite-order compatibility inside K_{b^m}
# ---------------------------------------------------------------------------


def compat(W, b, k, L1, L2):
    m = len(W)
    if m % k:
        return False
    c1 = Counter(tuple(W[(i + j) % m] for j in range(L1)) for i in range(m))
    if len(c1) != b ** L1 or len(set(c1.values())) != 1:
        return False
    c2 = Counter(tuple(W[(i + j) % m] for j in range(k * L2)) for i in range(0, m, k))
    return len(c2) == b ** (k * L2) and len(set(c2.values())) == 1


def compat_any_phase(W, b, k, L1, L2):
    for r in range(k):
        if compat(W[r:] + W[:r], b, k, L1, L2):
            return W[r:] + W[:r]
    return None


def phased_euler(b, k, Ls):
    """Euler circuit of G_phased(b,k,Ls): every Ls-word once at every phase (length k b^Ls)."""
    V = b ** (Ls - 1)
    adj = {(v, r): [((v * b + a) % V, (r + 1) % k, a) for a in range(b)] for v in range(V) for r in range(k)}
    stack = [((0, 0), None)]
    circ = []
    while stack:
        node, lab = stack[-1]
        if adj[node]:
            nv, nr, a = adj[node].pop()
            stack.append(((nv, nr), a))
        else:
            circ.append(stack.pop())
    circ.reverse()
    word = [lab for (_, lab) in circ[1:]]
    # rotate so that the walk starts at phase 0 with the (Ls-1)-word 0...0 preceding it
    return word


def section_multiradix():
    head("D4  Multi-radix compatibility: exact obstructions, witnesses and the completed small-case table")
    # (2,2,3,1): run-parity proof + enumeration
    for s in all_debruijn(3):
        n = len(s)
        runs = []
        i = 0
        # rotate to start at a run boundary
        r0 = next(j for j in range(n) if s[j] != s[j - 1])
        t = list(s[r0:] + s[:r0])
        starts = [j for j in range(n) if t[j] != t[j - 1]]
        zero_starts = [j for j in starts if t[j] == 0]
        check(len({j % 2 for j in zero_starts}) == 1, "(2,2,3,1): both 0-runs start at the same parity (run lengths odd)")
        check(compat_any_phase(list(s), 2, 2, 3, 1) is None, "(2,2,3,1): de Bruijn word fails at m = 8")
    stats = {}
    for (L1, L2) in ((4, 1), (5, 1), (5, 2)):
        ds = all_debruijn(L1)
        ok = [s for s in ds if compat_any_phase(list(s), 2, 2, L1, L2)]
        stats[(L1, L2)] = (len(ds), len(ok))
    check(stats[(4, 1)] == (16, 0), "(2,2,4,1): none of the 16 de Bruijn words of order 4 works (m = 16 infeasible)")
    check(stats[(5, 1)][0] == 2048 and stats[(5, 1)][1] > 0, "(2,2,5,1): m = 32 feasible")
    check(stats[(5, 2)] == (2048, 0), "(2,2,5,2): none of the 2048 de Bruijn words of order 5 works (m = 32 infeasible)")
    print("  exhaustive: (2,2,3,1) m=8: 0/2 ; (2,2,4,1) m=16: 0/16 ; (2,2,5,1) m=32: %d/2048 ; (2,2,5,2) m=32: 0/2048"
          % stats[(5, 1)][1])
    # witnesses by seeded search (verified exactly)
    rng = random.Random(25004)
    wit = {}
    for (b, k, L1, L2, m) in ((2, 2, 3, 1, 24), (2, 2, 4, 1, 48), (2, 2, 5, 2, 96), (2, 4, 5, 1, 64),
                              (2, 2, 6, 1, 64), (2, 4, 6, 1, 64)):
        W = None
        for t in range(6000):
            cand = random_euler(L1, rng, b, m // b ** L1)
            W = compat_any_phase(cand, b, k, L1, L2)
            if W:
                break
        check(W is not None, "witness found for (b,k,L1,L2,m) = %s" % ((b, k, L1, L2, m),))
        if W:
            check(compat(W, b, k, L1, L2), "witness verified exactly for %s" % ((b, k, L1, L2, m),))
            wit[(b, k, L1, L2)] = W
    print("  witnesses (exactly verified): (2,2,3,1) m=24, (2,2,4,1) m=48, (2,2,5,2) m=96, (2,4,5,1) m=64, (2,2,6,1) m=64, (2,4,6,1) m=64")
    # closure: repetition and splicing with the phased Euler circuit W_0
    W = wit[(2, 2, 3, 1)]
    check(compat(W + W, 2, 2, 3, 1), "repetition closure: m=48 from m=24")
    W0 = phased_euler(2, 2, 3)
    check(len(W0) == 16 and compat_any_phase(W0, 2, 2, 3, 1) is not None, "phased Euler circuit W_0 (m = 16) is a witness")
    # splice W0 into W at a common vertex ((Ls-1)-word, phase mod k); W0 visits every vertex
    Ls, k = 3, 2
    m1, m0 = len(W), len(W0)
    W0r = compat_any_phase(W0, 2, 2, 3, 1)
    vert0 = {(tuple(W0r[(j + t) % m0] for t in range(Ls - 1)), j % k) for j in range(m0)}
    check(len(vert0) == k * 2 ** (Ls - 1), "W_0 visits every vertex of the phased graph")
    i = 0
    u = tuple(W[(i + t) % m1] for t in range(Ls - 1))
    j = next(j for j in range(m0) if j % k == i % k and tuple(W0r[(j + t) % m0] for t in range(Ls - 1)) == u)
    S = W[:i] + W0r[j:] + W0r[:j] + W[i:]
    check(len(S) == 40 and compat(S, 2, 2, 3, 1), "splice closure: m = 24 + 16 = 40 feasible for (2,2,3,1)")
    print("  closure checks: W^2 (m = 48) and W spliced with W_0 (m = 40) are exact witnesses for (2,2,3,1)")
    print("  completed table (with the closure lemmas): (2,2,3,1): F = 8N\\{8}; (2,2,4,1): F = 16N\\{16};")
    print("    (2,2,5,1): F = 32N; (2,2,5,2): F = 32N\\{32}; (2,4,5,1): F = 64N; (2,2,6,1): F = 64N; (2,4,6,1): F = 64N")


def main():
    print("Phase 25 Track D verification (exact arithmetic)")
    section_D1_transducer()
    section_orbit_formulas()
    section_averages()
    section_sync_windows()
    section_lp()
    Dw = section_witness()
    section_applications(Dw)
    section_functionals()
    section_multiradix()
    print()
    print("=" * 78)
    if FAILS:
        print("FAILED: %d of %d checks" % (len(FAILS), COUNT[0]))
        for f in FAILS[:20]:
            print("  -", f)
        sys.exit(1)
    print("ALL %d CHECKS PASSED" % COUNT[0])
    sys.exit(0)


# Periodic witness (found from the L = 12 type-augmented LP primal by an Euler circuit; verified exactly)
WITNESS_P = 16076
WITNESS_COST = 4887
WITNESS_DMAX = Fr(59108, 10 ** 6)   # outward (ceiling) rounding of D(W) = 0.059107954113...
WITNESS_HEX = (
    "cdb6c28ffe1527775b5ac5360851e1527ff854951e1527fac35c2a4fd8d5b20471551527b5ac5360851fff6356c811c5"
    "51527df75b576c456c8126c10a3c2a4f7e2f6c28f0a93aad90232a8a93abdb115b576c28b6d851e1527aad9023bbadab"
    "b622b6aed8bdb0a3c2a4ffe1527775b570a92a3c2a4ff586bc2a4eeeb6ae1527ff0a93eb0d70a93eb0d70a93dad629b0"
    "428b6c456c811c55154a3c2a4eeeb6bc2a4ffe1527fff8549ffc2a4fff0a93fffc35c2a4ffe1527bf17b6145b6d8516d"
    "851e1527775b5ac5360851e1527fac36bc2a4fbeeb6ae1527d61ae1527ec6adabb6145b6145b6d851e1525478549fb1a"
    "b6aed851e1527ff0a93ff8549ffd8d5b576c28b6c28b6c28b6c28b6d88ad90232a8a93fd61b5e1527ffd9b6c28b6c28b"
    "6c5ed851e1527775b576c28b6c456c811c551527ff8549ffc2a4a8f0a93fd61ae1527fac36bc2a4fbeeb6aed851e1527"
    "ff0a93ff8549feb0d70a93bbadabb6145b6145b6c28f0a93ffc2a4fff0a93abeeb6b58a6c10a3ffc2a4a8f0a93d586c1"
    "0a3c2a4f6b58a6c10a3c2a4ffff0a93dad629b0428b6c28f0a93abeeb6bc2a4fff8549ffc2a4a8f0a93d59b6c28ffe15"
    "27775b5e1527775b576c28fff854951e1527ff8549ffc2a4f6aed8800cdb62f6c28f0a93ff8549fb36db115b576c456c"
    "8126c10a3c2a4ff586ed6b14d8238aa2a4eeeb6ae1527ff6b58a6c10a2db0a3c2a4ff586b8549ed5c2a4f561ae1527b5"
    "ac5360851e1527b5ac5360851e1527ff8549efc5ed8800cdb6c47775b5e1527ff0a93dab8549feb0d70a93d59b6c28f0"
    "a93efbadabb622b6aed8800c49b0428f0a93ffe1527fac35c2a4a8f0a93fd61b5e356d5c2a4fbeeb6ae1527ff0a93efb"
    "adabb61478549f594428b6c28f0a92a3c2a4ff586b8549fff0a93ff8549ffc2a4eeeb6aed851ffd8d5b570a93efbadaf"
    "0a93ff8549ffff0a93fd6510a3c2a4fd9b6c28f0a93abeeb6bc2a4fffe1527fff0a93fd61bb5ac5360851e1527775b5a"
    "c5360851e152547ff0a93efbadaf0a93ff8549ffc2a4fd8c551527ffe1527df75b576c5ed851e1527ffc2a4eaf6c456d"
    "6b14d8bdb115b576c28f0a93ff8549fb1ab6ae1527d61b0428f0a93ffe1527fac35c2a4fff0a93ff8549feb0d70a93ab"
    "eeb6aed8bd9b6db6c456d78d5b20471551527fffb5ac53608516d851e152755b2046551527bf17b6145b6147854951e1"
    "527ffe1527fac360851e1527ab36db627bf17b61478549feb0d8238aa51e1527ff0a93bbadabb61478549efc5ecdb614"
    "78549ffc2a4eeeb6bc2a4fff0a93ffc35c2a4ff586d78d5b2049b0428ffe1527ab0d70a93ff8549ed5db0a3c2a4eeeb6"
    "bc2a4eaf0a93ff8549ffe1527ff0a93dad629b0428b6db0a3c2a4fff8549f586d78549ddd6d78549efc5ed88009feb0d"
    "70a93ff8549efc5ed8bdb0a3c2a4f6b58a6c10a2db61478549ddd6d5c2a4eeeb6ae1527ecdb62f66db10019b6d851e15"
    "2777527ff0a93ff8549ffe1527ff854951e152757dd6d6b14d82145b6c28b6c28f0a93ffc2a4eeeb6ae1527df75b570a"
    "93fd61bb5ac5360851e1527bf17b6238aa2a4f7e2f6c28f0a93d56d5db17b62f6c28f0a93abc2a4eab6bc2a4fff0a93d"
    "f8bdb0a3ff8549ddd6d5c2a4ffe1527ff0a93ffb5ac5360851e1527578d5b2049b0428b6d8bdb115b2047154549ffe15"
    "27df75b576c400624d82145b6147854951e1527ff0a93ff8549fff0a93fff0a92a3c2a4eaf6c28f0a92a3c2a4eaf6c28"
    "f0a93ffc2a4fd8d70a93ffe1527775b5e1527fac360851ffc2a4fffe1527fac360851e1527fac360851ffc2a4fd8d5b5"
    "76c456c8126c10a3c2a4ffe1ae1527ff0a93ff8549d5f75b576c456c8126c10a2db6c28b6db17b61478549d55db0a3c2"
    "a4fac360851e152757dd6d5db115b2049b0428b6d8516db0a2db0a2db115b5e1527ff0a92a3c2a4ffe1527fac35c2a4f"
    "7e2f6c28b6c28b6c28f0a93df8bdb0a3c2a4f566db61478549ffc2a4eeeb6bc2a4ffe1527ab36d8800cdb6147154a3c2"
    "a4f561ae1527ff8608516db0a3c2a4ffe1527ffc2a4a8f0a93ffc2a4fff8549d5e1527ff8549fff0a93ff8549ffc2a4f"
    "f586b8549eacdb6c456c811ddd6d5db0a2db0a3c2a4ffe1527ff8549d5e152757dd6d78549f7dd6d78549feb0d823bba"
    "dad629b0428e2a8aa2a4ffe1527ff0a93ff8549ddd6d5c2a4fbeeb6aed851ffc2a4eafbadab8549ffc2a4ffe15254785"
    "49ffc2a4eaf0a93ffc2a4fff0a93f66db0a3c2a4ffe1527775b5e1527775b5e1525478549feb0d821478549d56c811c5"
    "515275576c5ed851e1527ff0a92a3c2a4fff854951e1527df75b5e1527fac35c2a4ffe1527ff0d70a93fd61b04655154"
    "a3c2a4ffe1527ff8549ffc2a4fff0a93ffff0a93fd61ae1527ff0a93d59b6c28f0a92a3c2a4ffff0a93fff8549ffc2a4"
    "ffe1525478549feb0d70a93df8bdb11c551527aabb61478549ffc2a4a8f0a93df8bd9b6d8516d8bdb17b6145b6d8516d"
    "b6d88e2a8a93df8bdb115b20471551527ffb1ab6409360851c551527fff0a93bbadab8549d56d78d5b570a93efbadaf0"
    "a93d56c8126c10a2db6147854951ffc2a4ffe1527fff8549ffe15275576c5ed851e1527ff8549ffc2a4fff8549ddd6d7"
    "8d5b2049b0428f0a93efbadaf0a93f6356d78549feb0d82145b61478549ffed6b14d821478549fffc2a4ff586ed6b14d"
    "82145b6db62f6c28f0a93ffe1527ff854951e1527ff8549d5e152757b622b6408e2aa2a8a93ff8549f586b8549ffc2a4"
    "fff8549feb0daf0a93fd61ae1527775b5e1527ffc2a4a8f0a93d59b6c5ecdb6145b6c28b6d8516d8800"
)

if __name__ == "__main__":
    main()
