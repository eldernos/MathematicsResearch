#!/usr/bin/env python3
"""Phase 22, Track B: radix thresholds (B1) and class-group 2-adic valuations (B2).

Finite checks for notes/phase22/radix-thresholds-and-class-groups.md.
Standard library only.  Every assertion is an exact integer statement unless
it is explicitly labelled as a printed measurement.

    python -B scripts/phase22_radix_classgroups.py
"""

import math
import random
import sys
import time
from math import gcd, log

T0 = time.time()
CHECKS = 0


def check(cond, msg):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise AssertionError(msg)


# ---------------------------------------------------------------------------
# common helpers
# ---------------------------------------------------------------------------

def v_p(n, p):
    if n == 0:
        return 10 ** 9
    n = abs(n)
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def digits(U, b):
    """Base-b digits of U >= 1, least significant first."""
    out = []
    while U:
        U, d = divmod(U, b)
        out.append(d)
    return out


def extremal_runs(ds, b):
    """Maximal runs of 0s or of (b-1)s: list of (start, length) in digit positions."""
    runs = []
    i = 0
    n = len(ds)
    while i < n:
        d = ds[i]
        if d == 0 or d == b - 1:
            j = i
            while j < n and ds[j] == d:
                j += 1
            runs.append((i, j - i))
            i = j
        else:
            i += 1
    return runs


def split_radix(b):
    s = v_p(b, 2)
    return s, b >> s


def beta_of(b):
    s, bp = split_radix(b)
    if bp == 1:
        return math.inf
    return log(b) / log(bp)


def g_beta(y, beta):
    """Run-packing function g_beta(y) = sum_{i>=0} (y gamma^i / beta - 1)_+."""
    if beta == math.inf:
        return 0.0
    gam = 1.0 - 1.0 / beta
    tot = 0.0
    x = y
    while x / beta > 1.0:
        tot += x / beta - 1.0
        x *= gam
        if gam == 0.0:
            break
    return tot


def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factor(n, spf):
    out = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return out


# ---------------------------------------------------------------------------
# B1.1  composite-radix displacement for L_{chi_4}(b)
# ---------------------------------------------------------------------------

def section_b1_lambert():
    print("== B1.1 composite-radix displacement for L_chi4(b), n <= 2^16 ==")
    N = 1 << 16
    c = [0] * (N + 1)
    for d in range(1, N + 1):
        chi = 0 if d % 2 == 0 else (1 if d % 4 == 1 else -1)
        if chi:
            for m in range(d, N + 1, d):
                c[m] += chi
    supp = [n for n in range(1, N + 1) if c[n] > 0]
    S = len(supp)
    lam = log(N / S)
    print(f"  support S(N) = {S}, rho = {S / N:.5f}")
    rows = []
    for b in (2, 3, 5, 6, 10, 12):
        s, bp = split_radix(b)
        tot_u = 0
        tot_V = 0
        for n in supp:
            a = c[n]
            V = 0
            while a % b == 0:
                a //= b
                V += 1
            U = a
            u = len(digits(U, b))
            tot_u += u
            tot_V += V
            # bottom-band barrier: ||U/b^j|| >= b'^{-j} for j <= v_2(U)/s
            if s >= 1 and bp > 1:
                v2 = v_p(U, 2)
                for j in range(1, v2 // s + 1):
                    r = U % (b ** j)
                    check(min(r, b ** j - r) >= 2 ** (s * j),
                          f"bottom barrier fails b={b} n={n} j={j}")
            # generic bound (Phase 20 Lemma 3.2(1)): b does not divide U
            check(U % b != 0, "unit divisible by radix")
        rows.append((b, tot_u / S / (lam / log(b)), tot_V / S))
    for b, mu, mv in rows:
        print(f"  b={b:>2}: mean u_b/lambda_N = {mu:.4f}, mean V_b = {mv:.4f}")
    # the composite even radices have the same width scale as the odd ones:
    # u_6 >= u_3 * log 3/log 6 - 1 etc. are not asserted (finite height); only
    # the qualitative radix-2 absorption is asserted.
    check(rows[0][1] < rows[1][1], "base-2 widths should be below base-3 widths")


# ---------------------------------------------------------------------------
# B1.2  2-adic run barrier and run packing in even composite radices
# ---------------------------------------------------------------------------

def section_b1_runs():
    print("== B1.2 2-adic run barrier and run packing, U = M 2^r ==")
    worst_ratio = {}
    for b in (6, 10, 12, 14, 18, 20, 24):
        s, bp = split_radix(b)
        beta = beta_of(b)
        worst = 0.0
        for M in (1, 3, 5, 7, 9, 11, 15, 25, 27):
            for r in range(1, 401):
                U0 = M << r
                # remove radix powers (V_b) as in the width law
                U = U0
                while U % b == 0:
                    U //= b
                ds = digits(U, b)
                u = len(ds)
                v2 = v_p(U, 2)
                lim = v2 // s  # positions where the barrier applies
                for (st, ln) in extremal_runs(ds, b):
                    if st + ln <= lim:
                        # Lemma 1.2(2): 2^{s(st+ln)} < b^{st}
                        check(st >= 1 and 2 ** (s * (st + ln)) < b ** st,
                              f"run barrier fails b={b} M={M} r={r} run={(st, ln)}")
                        worst = max(worst, ln / st * (beta - 1.0))
                if u <= lim and r % 3 == 0 and M in (1, 3, 5, 27):
                    runs = extremal_runs(ds, b)
                    for k in (2, 4, 8):
                        # near positions at threshold b^{-k}
                        Z = 0
                        for j in range(1, u + 1):
                            m = b ** j
                            rr = U % m
                            if min(rr, m - rr) * b ** k < m:
                                Z += 1
                                check(j * log(bp) > k * log(b) - 1e-9,
                                      f"near position below k*beta b={b} j={j} k={k}")
                        E = sum(max(0, ln - k + 1) for (_, ln) in runs)
                        check(Z <= E, "near count exceeds run excess")
                        bound = (k - 1) * g_beta(u / (k - 1), beta)
                        check(E <= bound + 1e-9,
                              f"run packing bound fails b={b} M={M} r={r} k={k}: {E} > {bound}")
                        far = (u + k - 1) - Z
                        check(far >= u + k - 1 - bound - 1e-9, "far count bound")
        worst_ratio[b] = worst
        print(f"  b={b:>2}: beta={beta:.5f}, max (run length)/(start) * (beta-1) = {worst:.4f} (< 1 asserted)")
        check(worst < 1.0, "normalized run ratio must be < 1")
    # contrast: prime radices have no linear barrier from the coefficient side
    for b in (3, 5, 7):
        worst = 0.0
        for M in (1, 3, 5, 7):
            for r in range(1, 401):
                U = M << r
                while U % b == 0:
                    U //= b
                for (st, ln) in extremal_runs(digits(U, b), b):
                    if st >= 1:
                        worst = max(worst, ln / st)
        print(f"  odd prime b={b}: max (run length)/(start) over M<=7, r<=400 = {worst:.3f} (printed only)")


def section_b1_packing():
    print("== B1.3 run-packing function g_beta: recursion, Lipschitz bound, sharpness ==")
    rng = random.Random(22)
    for b in (6, 10, 12, 20, 24):
        beta = beta_of(b)
        gam = 1 - 1 / beta
        for y in [0.1 * i for i in range(1, 120)]:
            lhs = g_beta(y, beta)
            rhs = max(0.0, y / beta - 1.0) + g_beta(gam * y, beta)
            check(abs(lhs - rhs) < 1e-9, "g recursion")
            check(g_beta(y + 0.05, beta) - lhs <= 0.05 + 1e-12, "g is 1-Lipschitz")
            check(g_beta(y + 0.05, beta) >= lhs - 1e-12, "g nondecreasing")
        # random admissible configurations never beat g (kappa0 = 1)
        for _ in range(400):
            x = rng.uniform(0.5, 12.0)
            top = x
            tot = 0.0
            while top > 1e-3:
                ell = rng.uniform(0, top / beta) * 0.999
                tot += max(0.0, ell - 1.0)
                top = top - ell - rng.uniform(0, 0.3 * top)
            check(tot <= g_beta(x, beta) + 1e-9, "random packing exceeds g")
        # geometric configuration attains g up to epsilon
        for x in (3.0, 6.0, 10.0):
            top, tot = x, 0.0
            while top / beta > 1:
                ell = top / beta * (1 - 1e-9)
                tot += ell - 1
                top -= ell
            check(abs(tot - g_beta(x, beta)) < 1e-6, "geometric configuration attains g")


def section_b1_constants():
    print("== B1.4 thresholds delta*_b and unconditional constants (units of C_f LL/(log b (log N)^kappa)) ==")
    L2 = log(2)
    print("  b    beta      delta*_b")
    for b in (3, 5, 6, 10, 12, 14, 18, 20, 24, 15):
        beta = beta_of(b)
        if beta == math.inf:
            continue
        ds = beta / (beta + L2)
        print(f"  {b:>2}  {beta:.5f}  {ds:.6f}")
    check(abs(1 / (1 + L2) - beta_of(3) / (beta_of(3) + L2)) < 1e-12, "odd b gives delta*")
    print("  delta  kappa  omega   b=3 lower  b=6 lower  b=10 lower  b=12 lower  upper(all)")
    for delta in (0.6, 0.65, 0.7, 0.75, 0.8, 0.9):
        kap = 1 - delta
        om = delta * L2 / kap
        vals = []
        for b in (3, 6, 10, 12):
            beta = beta_of(b)
            vals.append(kap * (1 + om - g_beta(om, beta)))
        up = kap + delta * L2
        for v in vals:
            check(v <= up + 1e-12 and v >= 2 * kap - 1e-12, "constants ordered")
        print(f"  {delta:.2f}   {kap:.2f}  {om:.4f}  {vals[0]:.4f}     {vals[1]:.4f}     {vals[2]:.4f}      {vals[3]:.4f}      {up:.4f}")


def section_b1_pairs():
    print("== B1.5 isolation scale: a pair of unit sources at gap d ==")
    for b in (3, 5, 10):
        for k in range(2, 15):
            for d in range(1, 30):
                U = b ** d + 1
                far = 0
                for j in range(1, d + k + 1):
                    m = b ** j
                    rr = U % m
                    if min(rr, m - rr) * b ** k >= m:
                        far += 1
                check(far == min(d, k) + k, f"pair far count b={b} k={k} d={d}: {far}")
    print("  far count of a pair (b^d + 1) at threshold b^-k equals min(d,k)+k for all tested b,k,d")


# ---------------------------------------------------------------------------
# B2  group rings
# ---------------------------------------------------------------------------

class AbGroup:
    """Z/n1 x Z/n2 with elements as integer indices."""

    def __init__(self, n1, n2=1):
        self.n1, self.n2 = n1, n2
        self.h = n1 * n2
        self.els = [(i, j) for i in range(n1) for j in range(n2)]
        self.idx = {e: k for k, e in enumerate(self.els)}
        self.mul = [[self.idx[((a[0] + c[0]) % n1, (a[1] + c[1]) % n2)] for c in self.els] for a in self.els]
        self.inv = [self.idx[((-a[0]) % n1, (-a[1]) % n2)] for a in self.els]
        self.zero = self.idx[(0, 0)]

    def order(self, g):
        a, c = self.els[g]
        o1 = self.n1 // gcd(self.n1, a)
        o2 = self.n2 // gcd(self.n2, c)
        return o1 * o2 // gcd(o1, o2)

    def power(self, g, k):
        a, c = self.els[g]
        return self.idx[((a * k) % self.n1, (c * k) % self.n2)]

    def ring_mul(self, X, Y):
        Z = [0] * self.h
        for i, x in enumerate(X):
            if x:
                row = self.mul[i]
                for j, y in enumerate(Y):
                    if y:
                        Z[row[j]] += x * y
        return Z

    def basis_elem(self, g, coeff=1):
        X = [0] * self.h
        X[g] = coeff
        return X

    def xc(self, g):
        """[c] + [c^{-1}]"""
        X = [0] * self.h
        X[g] += 1
        X[self.inv[g]] += 1
        return X

    def local_split(self, g, e):
        """sum_{i=0}^e [p]^{2i-e}"""
        X = [0] * self.h
        for i in range(e + 1):
            X[self.power(g, 2 * i - e)] += 1
        return X

    def char(self, k, g):
        """character chi_k(g) = exp(2 pi i (k1 g1/n1 + k2 g2/n2))"""
        k1, k2 = self.els[k]
        a, c = self.els[g]
        return complex(math.cos(2 * math.pi * (k1 * a / self.n1 + k2 * c / self.n2)),
                       math.sin(2 * math.pi * (k1 * a / self.n1 + k2 * c / self.n2)))

    def char_order(self, k):
        return self.order(k)  # dual group is isomorphic via the same indices

    def val_order(self, k, g):
        """exact order of the root of unity chi_k(g)"""
        k1, k2 = self.els[k]
        a, c = self.els[g]
        M = self.n1 * self.n2
        num = (k1 * a * self.n2 + k2 * c * self.n1) % M
        return M // gcd(num, M)

    def two_part_size(self):
        return 1 << v_p(self.h, 2)

    def odd_part_size(self):
        return self.h >> v_p(self.h, 2)

    def G2_squares(self):
        h2 = self.two_part_size()
        m = self.odd_part_size()
        G2 = [g for g in range(self.h) if self.power(g, h2) == self.zero]
        return sorted({self.power(g, 2) for g in G2}), G2

    def odd_component(self, g):
        h2 = self.two_part_size()
        m = self.odd_part_size()
        # g_odd = g^{h2 * t} with h2 t = 1 mod m
        if m == 1:
            return self.zero
        t = pow(h2, -1, m)
        return self.power(g, h2 * t)


def v2_vec(X):
    return min((v_p(x, 2) for x in X if x), default=10 ** 9)


def section_b2_identities():
    print("== B2.1 exact group-ring identities, products of length <= 40 ==")
    # Z/3
    G = AbGroup(3)
    x = G.xc(G.idx[(1, 0)])
    P = G.basis_elem(G.zero)
    for r in range(1, 41):
        P = G.ring_mul(P, x)
        check(P[G.zero] == (2 ** r + 2 * (-1) ** r) // 3, "Z/3 principal coefficient")
        check(P[G.idx[(1, 0)]] == (2 ** r - (-1) ** r) // 3 == P[G.idx[(2, 0)]], "Z/3 other coefficients")
        check(P[G.zero] % 2 == 0 and P[G.idx[(1, 0)]] % 2 == 1, "Z/3 parities")
    # idempotent mod 2: ([1]+[2])^2 = [1]+[2] in F_2[Z/3]
    sq = G.ring_mul(x, x)
    check([t % 2 for t in sq] == [t % 2 for t in x], "Z/3 idempotent mod 2")
    print("  Z/3: coefficients (2^r+2(-1)^r)/3 and (2^r-(-1)^r)/3; [1]+[2] idempotent mod 2")

    # Z/4: pure powers of two
    G = AbGroup(4)
    x = G.xc(G.idx[(1, 0)])
    P = G.basis_elem(G.zero)
    for r in range(1, 41):
        P = G.ring_mul(P, x)
        for g in range(4):
            a = G.els[g][0]
            expect = 2 ** (r - 1) if (a - r) % 2 == 0 else 0
            check(P[g] == expect, "Z/4 pure power of two")
    print("  Z/4: ([1]+[3])^r = 2^(r-1) ([0]+[2]) or 2^(r-1) ([1]+[3]) exactly")

    # Z/2 x Z/2: every x_c = 2[c]
    G = AbGroup(2, 2)
    for g in range(4):
        check(G.xc(g) == G.basis_elem(g, 2), "Z/2xZ/2 ambiguous")
    print("  Z/2 x Z/2: every [c]+[c^-1] = 2[c] (h_0 = 1)")

    # Z/8: class +-1 alone gives non-power-of-two coefficients; adding a
    # class +-2 factor (order-4 annihilation) restores pure powers of two.
    G = AbGroup(8)
    x1 = G.xc(G.idx[(1, 0)])
    x2 = G.xc(G.idx[(2, 0)])
    P = G.basis_elem(G.zero)
    found_odd = False
    for r in range(1, 41):
        P = G.ring_mul(P, x1)
        if r % 2 == 0 and r >= 4:
            c0 = P[G.zero]
            check(c0 == 2 ** (r - 2) + 2 ** (r // 2 - 1), "Z/8 principal coefficient formula")
            if (c0 >> v_p(c0, 2)) > 1:
                found_odd = True
        Q = G.ring_mul(P, x2)
        rr = r + 1
        for g in range(8):
            a = G.els[g][0]
            expect = 2 ** (rr - 2) if (a - r) % 2 == 0 else 0
            check(Q[g] == expect, "Z/8 annihilated product = a/h_0 on the genus")
    check(found_odd, "Z/8 atypical odd parts exist")
    print("  Z/8: x_1^r has [0]-coefficient 2^(r-2)+2^(r/2-1) (odd part ~ 2^(r/2));")
    print("       x_1^r x_2 = 2^(r-1) * (sum over a coset of 2G) exactly (order-4 annihilation)")

    # Z/5: Lucas-number formula and bounded excess
    G = AbGroup(5)
    lucas = [2, 1]
    for _ in range(200):
        lucas.append(lucas[-1] + lucas[-2])

    def L(j):
        return lucas[j] if j >= 0 else (-1) ** (-j) * lucas[-j]

    rng = random.Random(5)
    for _ in range(3000):
        m0, m1, m2 = rng.randint(0, 12), rng.randint(0, 14), rng.randint(0, 14)
        X = G.basis_elem(G.zero, 2 ** m0)
        for _ in range(m1):
            X = G.ring_mul(X, G.xc(G.idx[(1, 0)]))
        for _ in range(m2):
            X = G.ring_mul(X, G.xc(G.idx[(2, 0)]))
        r = m0 + m1 + m2
        j = m1 - m2
        sgn = (-1) ** m1
        check(5 * X[G.zero] == 2 ** r + sgn * 2 ** (m0 + 1) * L(j), "Z/5 principal Lucas formula")
        check(5 * X[G.idx[(1, 0)]] == 2 ** r - sgn * 2 ** m0 * L(j + 1), "Z/5 class +-1 Lucas formula")
        check(5 * X[G.idx[(2, 0)]] == 2 ** r + sgn * 2 ** m0 * L(j - 1), "Z/5 class +-2 Lucas formula")
        if m1 + m2 >= 1 and r - m0 >= 4:
            for g in range(5):
                ex = v_p(X[g], 2) - m0
                check(0 <= ex <= 3, f"Z/5 excess out of range: {ex}")
    for n in range(0, 120):
        check(v_p(L(n), 2) == (0 if n % 3 else (2 if n % 6 == 3 else 1)), "v_2 of Lucas numbers")
    print("  Z/5: 5 a_0 = 2^r + (-1)^{m1} 2^{m0+1} L_j, 5 a_{+-1} = 2^r - (-1)^{m1} 2^{m0} L_{j+1},")
    print("       5 a_{+-2} = 2^r + (-1)^{m1} 2^{m0} L_{j-1}  (j = m1 - m2);")
    print("       v_2(L_n) in {0,1,2}, so v_2(a_C) - m_0 in {0,...,3}")

    # nilpotency of the augmentation ideal of F_2[G_2]
    for (n1, n2) in ((4, 1), (8, 1), (2, 4), (4, 4)):
        G = AbGroup(n1, n2)
        gens = [G.idx[(1, 0)], G.idx[(0, 1)]] if n2 > 1 else [G.idx[(1, 0)]]
        orders = [n1, n2] if n2 > 1 else [n1]
        t = 1 + sum(o - 1 for o in orders)
        one = G.basis_elem(G.zero)

        def aug(g):
            X = G.basis_elem(g)
            X[G.zero] -= 1
            return X

        def mono(exps):
            X = one
            for g, e in zip(gens, exps):
                for _ in range(e):
                    X = G.ring_mul(X, aug(g))
            return [c % 2 for c in X]

        top = mono([o - 1 for o in orders])
        check(any(top), "I^{t-1} nonzero mod 2")
        for i, o in enumerate(orders):
            ex = [oo - 1 for oo in orders]
            ex[i] += 1
            check(not any(mono(ex)), "I^t = 0 mod 2")
        print(f"  F_2[Z/{n1}" + (f" x Z/{n2}" if n2 > 1 else "") + f"]: augmentation ideal nilpotent of index {t}")


def section_b2_random_products():
    print("== B2.2 order-4 annihilation and 2-adic lower bound on random products ==")
    rng = random.Random(2022)
    for (n1, n2) in ((6, 1), (7, 1), (2, 4), (8, 1), (4, 1), (2, 6), (12, 1), (3, 3)):
        G = AbGroup(n1, n2)
        H2sq, G2 = G.G2_squares()
        hsq = len(H2sq)
        # quotient G -> Gbar = G / G_2^2
        coset = {}
        reps = []
        for g in range(G.h):
            if g in coset:
                continue
            cid = len(reps)
            reps.append(g)
            for hh in H2sq:
                coset[G.mul[g][hh]] = cid
        chars = list(range(G.h))
        bad_chars = [k for k in chars if G.char_order(k) % 4 == 0]
        odd_chars = [k for k in chars if all(G.val_order(k, g) == 1 for g in G2)]
        maxexc = 0
        n_ok = 0
        for _ in range(1500):
            r = rng.randint(1, 18)
            classes = [rng.randrange(G.h) for _ in range(r)]
            exps = [1 if rng.random() < 0.85 else rng.randint(2, 4) for _ in range(r)]
            X = G.basis_elem(G.zero)
            for g, e in zip(classes, exps):
                X = G.ring_mul(X, G.local_split(g, e))
            killed_bad = all(any(e == 1 and G.val_order(k, g) == 4 for g, e in zip(classes, exps))
                             for k in bad_chars)
            if not killed_bad:
                continue
            # reduction identity: |G_2^2| a_C = coefficient of Cbar in the image
            Xbar = [0] * len(reps)
            for g, cf in enumerate(X):
                Xbar[coset[g]] += cf
            for C in range(G.h):
                check(hsq * X[C] == Xbar[coset[C]], "order-4 annihilation identity")
            # surviving odd characters and the 2-adic lower bound
            surv = []
            for k in odd_chars:
                dead = any(G.val_order(k, g) > 1 and (e + 1) % G.val_order(k, g) == 0
                           for g, e in zip(classes, exps))
                if not dead:
                    surv.append(sum(1 for g, e in zip(classes, exps) if e == 1 and G.val_order(k, g) == 1))
            lb = min(surv) - v_p(hsq, 2)
            for C in range(G.h):
                if X[C]:
                    check(v_p(X[C], 2) >= lb, "2-adic lower bound min_psi m_ker(psi)")
                    maxexc = max(maxexc, v_p(X[C], 2) - lb)
            n_ok += 1
        name = f"Z/{n1}" + (f" x Z/{n2}" if n2 > 1 else "")
        print(f"  {name:<10}: |G_2^2|={hsq}, annihilated samples={n_ok}, max excess v_2(a_C) - lower bound = {maxexc}")


# ---------------------------------------------------------------------------
# B2.3  binary quadratic forms
# ---------------------------------------------------------------------------

def xgcd(a, b):
    x0, y0, x1, y1 = 1, 0, 0, 1
    while b:
        q, a, b = a // b, b, a % b
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def reduce_form(a, b, c):
    while True:
        if a > c:
            a, b, c = c, -b, a
            continue
        if abs(b) > a:
            # translate b into (-a, a]
            k = (a - b) // (2 * a)
            b2 = b + 2 * a * k
            c = (b2 * b2 - (b * b - 4 * a * c)) // (4 * a)
            b = b2
            continue
        break
    if b < 0 and (abs(b) == a or a == c):
        b = -b
    return (a, b, c)


def reduced_forms(D):
    out = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a) == 0:
                c = (b * b - D) // (4 * a)
                if c < a:
                    continue
                if b < 0 and c == a:
                    continue
                if gcd(gcd(a, abs(b)), c) != 1:
                    continue
                out.append((a, b, c))
        a += 1
    return out


def compose(f, g, D):
    a1, b1, c1 = f
    a2, b2, c2 = g
    beta = (b1 + b2) // 2
    g1, x1, y1 = xgcd(a1, a2)
    e, s, t = xgcd(g1, beta)
    u, v, w = s * x1, s * y1, t
    A = a1 * a2 // (e * e)
    B = (u * a1 * b2 + v * a2 * b1 + w * (b1 * b2 + D) // 2) // e
    B %= 2 * A
    C = (B * B - D) // (4 * A)
    return reduce_form(A, B, C)


def class_group(D):
    forms = reduced_forms(D)
    h = len(forms)
    fid = {f: i for i, f in enumerate(forms)}
    e = fid[reduce_form(1, D % 2, (D % 2 - D) // 4)]
    table = [[fid[compose(f, g, D)] for g in forms] for f in forms]
    # group axioms
    for i in range(h):
        check(table[i][e] == i, "identity")
        inv = fid[reduce_form(forms[i][0], -forms[i][1], forms[i][2])]
        check(table[i][inv] == e, "inverse")
        for j in range(h):
            check(table[i][j] == table[j][i], "commutative")
            for k in range(h):
                check(table[table[i][j]][k] == table[i][table[j][k]], "associative")

    def order(i):
        k, x = 1, i
        while x != e:
            x = table[x][i]
            k += 1
        return k

    def pw(i, n):
        x = e
        for _ in range(n % order(i)):
            x = table[x][i]
        return x

    # find iso to Z/n1 x Z/n2 with n1 | n2
    for n1 in range(1, h + 1):
        if h % n1 or (h // n1) % n1:
            continue
        n2 = h // n1
        for g2 in range(h):
            if order(g2) != n2:
                continue
            for g1 in range(h):
                if order(g1) != n1:
                    continue
                img = {}
                okk = True
                for i in range(n1):
                    for j in range(n2):
                        x = table[pw(g1, i)][pw(g2, j)]
                        if x in img.values():
                            okk = False
                            break
                        img[(i, j)] = x
                    if not okk:
                        break
                if okk and len(set(img.values())) == h:
                    G = AbGroup(n2, n1) if n1 > 1 else AbGroup(n2)
                    form_to_el = {}
                    for (i, j), x in img.items():
                        form_to_el[x] = G.idx[(j, i)] if n1 > 1 else G.idx[(j, 0)]
                    return forms, G, form_to_el, fid
    raise RuntimeError("no basis found")


def kron(D, p):
    if p == 2:
        if D % 2 == 0:
            return 0
        return 1 if D % 8 in (1, 7) else -1
    r = pow(D % p, (p - 1) // 2, p)
    if r == 0:
        return 0
    return 1 if r == 1 else -1


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    # Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        bb = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, bb * bb % p, t * bb * bb % p, r * bb % p
    return r


def prime_form(D, p):
    """Reduced form of a prime ideal above p (split or ramified)."""
    if p == 2:
        if D % 2:
            b = 1
        else:
            b = 2 if (D // 4) % 2 else 0
    else:
        if D % p == 0:
            b = p if D % 2 else 0
        else:
            r = sqrt_mod(D, p)
            b = r if (r - D) % 2 == 0 else p - r
    c = (b * b - D) // (4 * p)
    check((b * b - D) % (4 * p) == 0, "prime form discriminant")
    return reduce_form(p, b, c)


def primes_upto(n):
    sv = bytearray([1]) * (n + 1)
    sv[0] = sv[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sv[i]:
            sv[i * i::i] = bytearray(len(sv[i * i::i]))
    return [i for i in range(n + 1) if sv[i]]


def lattice_counts(f, N):
    a, b, c = f
    r = [0] * (N + 1)
    D = b * b - 4 * a * c
    ymax = int(math.isqrt(4 * a * N // (-D))) + 2
    for y in range(-ymax, ymax + 1):
        # a x^2 + b x y + c y^2 <= N
        disc = b * b * y * y - 4 * a * (c * y * y - N)
        if disc < 0:
            continue
        sq = math.isqrt(disc)
        lo = (-b * y - sq) // (2 * a) - 1
        hi = (-b * y + sq) // (2 * a) + 1
        for x in range(lo, hi + 1):
            v = a * x * x + b * x * y + c * y * y
            if 0 < v <= N:
                r[v] += 1
    return r


DISCS = [(-39, "Z/4"), (-47, "Z/5"), (-84, "Z/2 x Z/2"), (-87, "Z/6"), (-95, "Z/8"), (-71, "Z/7")]


def find_disc(target, h=8, mmax=2000):
    """smallest fundamental D = -m with class group Z/n1 x Z/n2, (n1, n2) = target"""
    for m in range(3, mmax):
        D = -m
        if D % 4 not in (0, 1):
            continue
        # fundamental test
        if D % 4 == 1:
            n = m
            ok = all(n % (p * p) for p in range(3, int(n ** 0.5) + 1, 2)) and n % 4 != 0
        else:
            d = D // 4
            ok = d % 4 in (2, 3) and all((-d) % (p * p) for p in range(3, int((-d) ** 0.5) + 2, 2))
            if (-d) % 4 == 0:
                ok = False
        if not ok:
            continue
        forms = reduced_forms(D)
        if len(forms) != h:
            continue
        _, G, _, _ = class_group(D)
        if (G.n1, G.n2) == target:
            return D
    return None


def section_b2_forms():
    print("== B2.3 representation counts r_Q(n) = w a_C(n) for seven discriminants, n <= 50000 ==")
    N = 50000
    spf = spf_sieve(N)
    D24 = find_disc((4, 2))
    check(D24 is not None, "found Z/2 x Z/4 discriminant")
    discs = DISCS + [(D24, "Z/2 x Z/4")]
    summary = []
    for D, name in discs:
        forms, G, f2e, fid = class_group(D)
        h = len(forms)
        expect = {"Z/4": (4, 1), "Z/5": (5, 1), "Z/2 x Z/2": (2, 2), "Z/6": (6, 1), "Z/8": (8, 1),
                  "Z/7": (7, 1), "Z/2 x Z/4": (4, 2)}[name]
        check((G.n1, G.n2) == expect, f"class group structure of {D}")
        two_group = G.odd_part_size() == 1
        bad_chars = [k for k in range(G.h) if G.char_order(k) % 4 == 0]
        n_cond = 0
        H2sq, G2 = G.G2_squares()
        hsq = len(H2sq)
        h0 = G.h // (1 << v_p(G.h, 2)) * hsq  # |G^2| = |G_odd| |G_2^2|
        # genus count
        sq = {G.power(g, 2) for g in range(G.h)}
        check(len(sq) == h0, "h_0 = |G^2|")
        w = 2
        cls_of = {}
        for p in primes_upto(N):
            k = kron(D, p)
            if k == 1 or k == 0:
                cls_of[p] = (k, f2e[fid[prime_form(D, p)]])
            else:
                cls_of[p] = (-1, None)
        reps = {f: lattice_counts(f, N) for f in forms}
        stats = {}
        for f in forms:
            stats[f] = [0, 0, 0.0, 0]  # support, sum v2, sum log2 odd, count a_C = a/h0
        n_supp = 0
        for n in range(1, N + 1):
            X = G.basis_elem(G.zero)
            a = 1
            zero = False
            sq1 = []
            for p, e in factor(n, spf):
                k, g = cls_of[p]
                if k == 1:
                    X = G.ring_mul(X, G.local_split(g, e))
                    a *= e + 1
                    if e == 1:
                        sq1.append(g)
                elif k == 0:
                    X = G.ring_mul(X, G.basis_elem(G.power(g, e)))
                else:
                    if e % 2:
                        zero = True
                        break
            if zero:
                for f in forms:
                    check(reps[f][n] == 0, "inert odd exponent not represented")
                continue
            n_supp += 1
            if two_group and all(any(G.val_order(kk, g) == 4 for g in sq1) for kk in bad_chars):
                # Theorem 2.3 (2-groups): a_C = a/h_0 on the genus, 0 off it
                n_cond += 1
                for f in forms:
                    check(h0 * X[f2e[fid[f]]] in (0, a), f"2-group annihilation D={D} n={n}")
            for f in forms:
                aC = X[f2e[fid[f]]]
                check(reps[f][n] == w * aC, f"r_Q = w a_C fails D={D} f={f} n={n}")
                if aC:
                    st = stats[f]
                    rq = w * aC
                    st[0] += 1
                    v2 = v_p(rq, 2)
                    st[1] += v2
                    st[2] += math.log2(rq >> v2)
                    if h0 * aC == a:
                        st[3] += 1
        lines = []
        for f in forms:
            st = stats[f]
            S = st[0]
            lines.append((f, S / N, st[1] / S, st[2] / S, st[3] / S))
        summary.append((D, name, G, h0, hsq, lines, n_supp))
        print(f"  D={D:>5} ({name}, h={h}, h_0={h0}, |G_2^2|={hsq}): identity checked for {N} n and {h} forms")
        if two_group:
            print(f"     2-group: annihilation condition holds for {n_cond}/{n_supp} supported n; a_C = a/h_0 asserted there")
        for f, dens, mv2, mlo, frac in lines:
            print(f"     Q={f}: S_Q/N={dens:.4f}, mean v_2(r_Q)={mv2:.3f}, mean log2 U_2={mlo:.3f}, "
                  f"frac a_C = a/h_0: {frac:.3f}")
    return summary, spf


def section_b2_excess(spf):
    print("== B2.4 excess v_2(a_C) - min_{psi surviving} m_ker(psi) + v_2|G_2^2| on annihilated supported n <= 30000 ==")
    N = 30000
    D12 = find_disc((12, 1), h=12)
    check(D12 is not None, "found cyclic Z/12 discriminant")
    D33 = -4027
    _, G33, _, _ = class_group(D33)
    check((G33.n1, G33.n2) == (3, 3), "Cl(-4027) = Z/3 x Z/3")
    for D, name in ((-47, "Z/5"), (-87, "Z/6"), (-71, "Z/7"), (D12, "Z/12"), (D33, "Z/3 x Z/3")):
        forms, G, f2e, fid = class_group(D)
        H2sq, G2 = G.G2_squares()
        hsq = len(H2sq)
        odd_chars = [k for k in range(G.h) if all(G.val_order(k, g) == 1 for g in G2)]
        bad_chars = [k for k in range(G.h) if G.char_order(k) % 4 == 0]
        cls = {}
        for p in primes_upto(N):
            k = kron(D, p)
            cls[p] = (k, f2e[fid[prime_form(D, p)]] if k >= 0 else None)
        hist = {}
        vq = {3: [0, 0, 0], 5: [0, 0, 0]}  # count, sum v_q, count v_q >= 3
        for n in range(2, N + 1):
            fac = factor(n, spf)
            X = G.basis_elem(G.zero)
            dead = False
            split = []
            for p, e in fac:
                k, g = cls[p]
                if k == 1:
                    X = G.ring_mul(X, G.local_split(g, e))
                    split.append((g, e))
                elif k == 0:
                    X = G.ring_mul(X, G.basis_elem(G.power(g, e)))
                elif e % 2:
                    dead = True
                    break
            if dead or not split:
                continue
            for f in forms:
                aC = X[f2e[fid[f]]]
                if aC:
                    for q in (3, 5):
                        vv = v_p(aC, q)
                        vq[q][0] += 1
                        vq[q][1] += vv
                        vq[q][2] += vv >= 3
            # Lemma 2.5 needs the order-4 annihilation hypothesis of Lemma 2.1(2)
            if not all(any(e == 1 and G.val_order(kk, g) == 4 for g, e in split) for kk in bad_chars):
                continue
            surv = []
            for kk in odd_chars:
                killed = any(G.val_order(kk, g) > 1 and (e + 1) % G.val_order(kk, g) == 0 for g, e in split)
                if not killed:
                    surv.append(sum(v_p(e + 1, 2) for g, e in split if G.val_order(kk, g) == 1))
            lb = min(surv) - v_p(hsq, 2)
            for f in forms:
                aC = X[f2e[fid[f]]]
                if aC:
                    ex = v_p(aC, 2) - lb
                    check(ex >= 0, "excess negative")
                    hist[ex] = hist.get(ex, 0) + 1
        tot = sum(hist.values())
        top = sorted(hist.items())[:4]
        print(f"  D={D} ({name}, |G_2^2|={hsq}): " + ", ".join(f"P(excess={k})={v / tot:.3f}" for k, v in top)
              + f", max={max(hist)}")
        print(f"     odd valuations (printed only): mean v_3(a_C)={vq[3][1] / vq[3][0]:.4f}, "
              f"P(v_3>=3)={vq[3][2] / vq[3][0]:.4f}; mean v_5(a_C)={vq[5][1] / vq[5][0]:.4f}, "
              f"P(v_5>=3)={vq[5][2] / vq[5][0]:.4f}")


def section_b2_constants():
    print("== B2.5 predicted radix-2^k constants 1 + log2 * E[1 - 1/d] (units of Psi_N) ==")
    P = 200000
    pr = primes_upto(P)
    out = {}
    for D, ell in ((-23, 3), (-87, 3), (-47, 5), (-71, 7)):
        forms, G, f2e, fid = class_group(D)
        _, G2 = G.G2_squares()
        G2set = set(G2)
        prod = 1.0
        for p in pr:
            if kron(D, p) != 1:
                continue
            g = f2e[fid[prime_form(D, p)]]
            if g in G2set:
                continue
            Pp = (1 - 1 / p) * p ** (1 - ell) / (1 - p ** (-ell))
            prod *= 1 - Pp
        const = 1 + (1 - 1 / ell) * prod * log(2)
        out[D] = (prod, const)
        print(f"  D={D}: G_odd=Z/{ell}, 1-pi_J={prod:.6f}, constant={const:.6f}")
    check(abs(out[-23][0] - 0.783637) < 2e-6, "Delta=-23 reproduces Phase 21 1-pi_J")
    check(abs(out[-23][1] - 1.362117) < 2e-6, "Delta=-23 reproduces Phase 21 constant")
    for D in (-39, -84, -95, -260):
        print(f"  D={D}: G_odd trivial, constant = 1 (same as h_0 = 1)")
    return out


def main():
    section_b1_lambert()
    section_b1_runs()
    section_b1_packing()
    section_b1_constants()
    section_b1_pairs()
    section_b2_identities()
    section_b2_random_products()
    summary, spf = section_b2_forms()
    section_b2_excess(spf)
    section_b2_constants()
    print(f"OK: {CHECKS} checks passed in {time.time() - T0:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
