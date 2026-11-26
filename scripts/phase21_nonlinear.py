"""Exact controls for Phase 21 Track C (the nonlinear normality boundary).

Run from the repository root:  python -B scripts/phase21_nonlinear.py

C1  Freezing of the actual binary prefix of C(2,3,1,4)^3 to the cubic mass M_3 at the
    threshold J_0(L) = ceil(L/s + L/d); an exact counterexample to uniform isolation on
    every interval of length p^(-sigma_r H/3) (a delta_H-net of competitor sums
    2 + (a/3^H)^4 just above u = 2, certified at H = 4000); the competitor inflation
    near u = 2 at small H; exact exponent margins for r = 2 (q = 3) and for q > d.
C2  The boundary d = r for C(2,3,1,2)^2 and C(2,3,1,3)^3: ordered and distinct insertion
    counts, run lengths, mean real tail, density of shifts with full 3-adic depth, the
    denominator-only barrier, and finite digit statistics (evidence only).
C3  Tied top-depth monomials in several orders: exact jumps of the weighted mass at
    level-H centres for X1^3 + c X1 X2 + c' X3 and X1^2 X3 + c X1 X2^2 (orders 1,2,3,
    d = 4), the cancellation X1 X2 X4 - X1 X3^2 at loss-0 centres, and competitor
    counts showing why higher orders must sit on bounded losses.
C4  The hybrid polynomial-schedule all-prime construction: exact reduced denominators,
    unchanged 3-adic residues when auxiliary indices are prime to p (and pollution when
    they are not), period bounds, and the threshold tables for dense introduction.

All assertions use exact integers or Fractions. Floating point appears only in printed
summaries (densities, logarithms, digit frequencies).
"""

from bisect import bisect_left, bisect_right
from fractions import Fraction
from itertools import product
from math import comb, exp, factorial, gcd, isqrt, lcm, log, sqrt
import random

# ---------------------------------------------------------------- arithmetic helpers


def val(n, p):
    """p-adic valuation of a nonzero integer or Fraction."""
    if isinstance(n, Fraction):
        return val(n.numerator, p) - val(n.denominator, p)
    assert n != 0
    n, e = abs(n), 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def factor(n):
    out, q = {}, 2
    while q * q <= n:
        while n % q == 0:
            out[q] = out.get(q, 0) + 1
            n //= q
        q += 1 if q == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n + 1) if sieve[i]]


def mult_order(b, m):
    """Multiplicative order of b modulo m (gcd(b, m) = 1)."""
    if m == 1:
        return 1
    fac = factor(m)
    phi = 1
    for q, e in fac.items():
        phi *= (q - 1) * q ** (e - 1)
    order = phi
    for q in factor(phi):
        while order % q == 0 and pow(b, order // q, m) == 1:
            order //= q
    return order


def iroot4(x):
    """floor(x^(1/4)) for an integer x >= 0."""
    return isqrt(isqrt(x))


def icbrt_ceil(x):
    lo, hi = 0, 1
    while hi**3 < x:
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if mid**3 >= x:
            hi = mid
        else:
            lo = mid + 1
    return lo


# ================================================================ C1


def check_c1_freezing():
    """p^(rsJ) b^(-n) R_n == M_3(u) mod p^L for the actual prefix of C(2,3,1,4)^3."""
    b, p, s, d, t, r, L = 2, 3, 1, 4, 2, 3, 3
    J = -(-(L * d + L * s) // (s * d))  # ceil(L/s + L/d)
    mod = p**L
    g = pow(b ** t, -1, mod)  # b^(-t) mod p^L
    imax = 3 ** (J + 1)
    w = [0] * (imax + 1)
    for i in range(1, imax + 1):
        w[i] = (p ** (s * (J - val(i, p))) * pow(g, i**d, mod)) % mod
    pref = [0] * (imax + 1)
    for i in range(1, imax + 1):
        pref[i] = (pref[i - 1] + w[i]) % mod
    # mass coordinates z = a/p^h, h <= (L-1)//s, scaled by p^hmax
    hmax = (L - 1) // s
    coords = [(a * p ** (hmax - h), h) for h in range(hmax + 1) for a in range(1, p ** (h + 1)) if a % p]
    rng = random.Random(21)
    checked = 0
    for _ in range(6):
        n = rng.randrange(t * p ** (d * J), t * p ** (d * (J + 1)))
        X = n // t  # need sum i^4 <= n/t
        total = 0
        for i in range(1, imax + 1):
            if i**d > X:
                break
            for j in range(1, imax + 1):
                rest = X - i**d - j**d
                if rest < 1:
                    break
                k = min(iroot4(rest), imax)
                total += w[i] * w[j] * pref[k]
        total %= mod
        # M_3(u) mod p^L with u = n/(t p^(dJ)); compare S(z) * p^(d hmax) * t * p^(dJ) <= n * p^(d hmax)
        bound = n * p ** (d * hmax)
        scale = t * p ** (d * J)
        mass = 0
        for (Z1, h1), (Z2, h2), (Z3, h3) in product(coords, repeat=3):
            if s * (h1 + h2 + h3) <= L - 1 and (Z1**d + Z2**d + Z3**d) * scale <= bound:
                mass += p ** (s * (h1 + h2 + h3))
        assert total == mass % mod, (n, total, mass % mod)
        checked += 1
    print(f"C1: actual prefix of C(2,3,1,4)^3 freezes to M_3(u) mod 3^{L} at J = J_0(L) = {J} "
          f"({checked} random shifts, all ordered triples)")


def check_c1_counterexample():
    """Competitor sums 2 + (a/3^H)^4 form a delta_H-net of (2+rho_H, 2+2 rho_H]."""
    p, d, r = 3, 4, 3
    eps = Fraction(1, 4)
    sigma3 = Fraction(1, 42)
    results = []
    for H in (6, 10, 100, 1000, 4000):
        R = icbrt_ceil(8 * (32 * H * H) ** 4) + 1  # rho_H = 1/R
        P4 = p ** (d * H)
        # smallest a with (a/3^H)^4 >= 2 rho, i.e. a^4 R >= 2 * 3^(4H); then two more steps
        a_hi = iroot4((2 * P4) // R) + 1
        while a_hi**4 * R < 2 * P4:
            a_hi += 1
        a_hi += 2
        # largest gap between consecutive admissible numerators (3 does not divide a) is at most
        # (a_hi^4 - (a_hi - 2)^4)/3^(4H); require it <= 2 delta_H = 2 eps/(H^2 3^H)
        gap_num = a_hi**4 - (a_hi - 2) ** 4
        assert gap_num * H**2 * p**H <= 2 * eps * P4, H
        # the net starts below 2 + rho: some admissible a has (a/3^H)^4 <= rho
        a_lo = iroot4(P4 // R)
        assert a_lo >= 3 and a_lo**4 * R <= P4
        long_interval = R ** 126 < p**H  # rho_H > 3^(-H/126) = 3^(-sigma_3 H / 3)
        results.append((H, long_interval))
    assert results[-1] == (4000, True) and not results[0][1]
    first = next(H for H, ok in results if ok)
    print("C1: competitor sums 2+(a/3^H)^4 are a delta_H-net of (2+rho_H, 2+2rho_H], rho_H ~ H^(-8/3);"
          f" certified exactly for H in {[h for h, _ in results]}")
    print(f"    rho_H > 3^(-sigma_3 H/3) holds at H = {first}: no isolated centre on an interval of that length")
    assert sigma3 / 3 == Fraction(1, 126)


def level_coords(p, d, Hmax):
    """Per-loss sorted lists of scaled d-th powers (Z = a p^(Hmax-h), weight key Z^d)."""
    out = []
    for h in range(Hmax + 1):
        out.append(sorted((a * p ** (Hmax - h)) ** d for a in range(1, p ** (h + 1)) if a % p))
    return out


def count_window(p, d, Hmax, lo, hi):
    """Ordered triples of level <= Hmax with lo < S(z) <= hi (scaled by p^(d Hmax))."""
    lists = level_coords(p, d, Hmax)
    total = 0
    for h1 in range(Hmax + 1):
        for x1 in lists[h1]:
            if x1 >= hi:
                break
            for h2 in range(Hmax + 1 - h1):
                for x2 in lists[h2]:
                    s12 = x1 + x2
                    if s12 >= hi:
                        break
                    for h3 in range(Hmax + 1 - h1 - h2):
                        lst = lists[h3]
                        total += bisect_right(lst, hi - s12) - bisect_right(lst, lo - s12)
    return total


def check_c1_inflation():
    """Near u = 2 the competitor count is not proportional to the window length."""
    p, d, H = 3, 4, 6
    sc = p ** (d * H)
    rows = []
    for k in (2, 4, 6, 8):
        wdt = sc // p**k
        near = count_window(p, d, H, 2 * sc, 2 * sc + wdt)
        far = count_window(p, d, H, 2 * sc + sc // 2, 2 * sc + sc // 2 + wdt)
        rows.append((k, near, far))
    # generic windows scale like the length; the window (2, 2+w] decays only like w^(1/4)
    assert rows[-1][1] > 20 * max(rows[-1][2], 1)
    assert rows[0][1] < 3 * rows[0][2]
    print("C1: level<=6 triple counts in (2,2+3^-k] vs (2.5,2.5+3^-k], k=2,4,6,8:",
          ", ".join(f"{n}/{f}" for _, n, f in rows))


def exponents(q, alpha, beta):
    K = 2 ** (q - 1)
    e1 = beta + (1 - q * alpha) / Fraction(2 * K - 2)
    e2 = beta + alpha * (Fraction(q, 2 * K - 2) - Fraction(2, K)) - Fraction(1, 2 * K - 2)
    return e1, e2


def check_c1_margins():
    # r = 2, q = 3: region beta/2 <= alpha <= beta <= 1 (vertices suffice: linear in each)
    worst = min(1 - max(exponents(3, a, b)) for a, b in
                [(Fraction(0), Fraction(0)), (Fraction(1, 2), Fraction(1)), (Fraction(1), Fraction(1))])
    assert worst == Fraction(1, 12)
    # q > d: the cap x >= eta = p^(-2 kappa H) adds 2 kappa (q-d)/(2K_q-2) to E_1, and gamma adds
    # (c + 2 kappa d (q-2))/(2K_q-2) to E_2; the anchor loss adds kappa to both.  Both exponents grow
    # with beta, so the worst competitor has beta = min(1, r alpha).
    kappa, c = Fraction(1, 2000), Fraction(1, 2000)
    for r, d in ((3, 3), (2, 2), (4, 3), (3, 2)):
        qs = range(3, 4) if r == 2 else range(4, r + 2)
        m = Fraction(1)
        for i in range(841):
            alpha = Fraction(i, 840)
            beta = min(Fraction(1), r * alpha)
            best = None
            for q in qs:
                K = 2 ** (q - 1)
                e1, e2 = exponents(q, alpha, beta)
                e1 += kappa + 2 * kappa * max(q - d, 0) / (2 * K - 2)
                e2 += kappa + (c + kappa + 2 * kappa * d * (q - 2)) / (2 * K - 2)
                val_q = max(e1, e2)
                best = val_q if best is None else min(best, val_q)
            m = min(m, 1 - best)
        assert m > 0, (r, d, m)
    print(f"C1: exponent margin for r=2 with q=3 is exactly 1/12; with the eta-cap the q>d cases"
          f" (r,d)=(3,3),(2,2),(4,3),(3,2) keep positive margins at kappa=c=1/2000")


# ================================================================ C2


def tuple_coeffs(r, d, s, p, X, Jtop):
    """dict m -> p^(r s Jtop) * sum over ordered r-tuples with sum i^d = m of p^(-s sum v_p(i))."""
    imax = 1
    while (imax + 1) ** d <= X:
        imax += 1
    w = [0] + [p ** (s * (Jtop - val(i, p))) for i in range(1, imax + 1)]
    cur = {0: 1}
    for _ in range(r):
        nxt = {}
        for m0, c0 in cur.items():
            for i in range(1, imax + 1):
                m1 = m0 + i**d
                if m1 > X:
                    break
                nxt[m1] = nxt.get(m1, 0) + c0 * w[i]
        cur = nxt
    return cur


def check_c2_counts():
    rows = []
    for r, d, X, vol in ((2, 2, 10**6, Fraction(785398, 10**6)), (3, 3, 10**6, Fraction(712072, 10**6))):
        ordered, distinct = 0, set()
        roots = [i**d for i in range(1, 2 + round(X ** (1 / d))) if i**d <= X]
        if r == 2:
            for a in roots:
                for b2 in roots:
                    if a + b2 > X:
                        break
                    ordered += 1
                    distinct.add(a + b2)
        else:
            for a in roots:
                for b2 in roots:
                    if a + b2 >= X:
                        break
                    for c3 in roots:
                        if a + b2 + c3 > X:
                            break
                        ordered += 1
                        distinct.add(a + b2 + c3)
        rows.append((X, ordered, len(distinct)))
        # ordered tuples ~ vol * X: the insertion count is linear, not O(X^(1-eta))
        assert abs(Fraction(ordered, X) - vol) < Fraction(1, 50)
    (X2, o2, n2), (X3, o3, n3) = rows
    landau = 0.7642236535892206 * X2 / sqrt(log(X2))
    assert n2 < X2 // 4 and n3 < X3 // 8
    print(f"C2: r=d=2: {o2} ordered pairs, {n2} distinct sums of two positive squares <= 10^6 "
          f"(Landau KX/sqrt(log X) = {landau:.0f}, ratio {n2 / landau:.3f})")
    print(f"    r=d=3: {o3} ordered triples, {n3} distinct sums of three positive cubes <= 10^6 "
          f"(density {n3 / X3:.4f}, mean gap {X3 / n3:.2f})")


def orbit_stats(r, d, s, N):
    """Shifts n <= N of x = C(2,3,s,d)^r (t = 2): exact 3-depth of R_n, real tail, runs."""
    p, t = 3, 2
    X = N // t + 40
    Jtop = 0
    while 3 ** (d * (Jtop + 1)) <= X:
        Jtop += 1
    Jtop += 1
    E = r * s * Jtop
    cur = tuple_coeffs(r, d, s, p, X, Jtop)
    coef = [0] * (X + 1)
    for m, c in cur.items():
        coef[m] = c  # 3^E times the true coefficient at position t*m
    M = 3**E
    depth = [0] * (N + 1)
    Nn = 0
    for n in range(1, N + 1):
        Nn = (2 * Nn + (coef[n // t] if n % t == 0 else 0)) % M
        depth[n] = 0 if Nn == 0 else E - val(Nn, p)
    tail = [0.0] * (N + 2)
    T = 0.0
    for n in range(t * X, -1, -1):
        if n <= N + 1:
            tail[n] = T
        c = coef[n // t] / M if n % t == 0 else 0.0
        T = (T + c) / 2
    mass = Fraction(sum(coef[m] for m in range(1, N // t + 1)), M)
    positions = [t * m for m in range(1, N // t + 1) if coef[m]]
    return depth, tail, mass, positions


def check_c2_orbits():
    out = []
    for r, d, N in ((2, 2, 400000), (3, 3, 400000)):
        depth, tail, mass, positions = orbit_stats(r, d, 1, N)
        # cumulative coefficient weight per shift is bounded below: the mean real tail is O(1)
        assert mass / N > Fraction(1, 10)
        lo = N // 2
        full = {}
        for L in (0, 1, 2, 3):
            good = 0
            for n in range(lo, N + 1):
                J = 0
                while 2 * 3 ** (d * (J + 1)) <= n:
                    J += 1
                if depth[n] >= r * J - L:
                    good += 1
            full[L] = good / (N - lo + 1)
        big_tail = sum(1 for n in range(lo, N + 1) if tail[n] >= 0.125) / (N - lo + 1)
        gaps = [b2 - a for a, b2 in zip(positions, positions[1:])]
        out.append((r, d, float(mass / N), full, big_tail, sum(gaps) / len(gaps)))
        assert full[3] > 0.9  # full 3-adic depth on most shifts
    for r, d, mt, full, bt, mg in out:
        print(f"C2: C(2,3,1,{d})^{r}, shifts 2e5..4e5: weight/shift {mt:.3f}; depth >= {r}J-L on "
              + ", ".join(f"{full[L]:.3f} (L={L})" for L in full)
              + f"; tail >= 1/8 on {bt:.3f}; mean run {mg:.1f}")


def check_c2_barrier():
    """Denominator-only methods cannot see digits: every T-bit pattern starts some a/3^e."""
    for e in range(1, 10):
        q = 3**e
        T = 0
        while 2 ** (T + 1) <= q // 2:
            T += 1
        seen = {(a << T) // q for a in range(1, q) if a % 3}
        assert len(seen) == 2**T
    print("C2: for q = 3^e (e <= 9) and 2^T <= q/2 all 2^T leading T-bit patterns occur among a/q, 3 !| a")


def digit_deviation(r, d, s, Nb):
    p, t, G = 3, 2, 64
    X = (Nb + G) // t + 1
    Jtop = 0
    while 3 ** (d * (Jtop + 1)) <= X:
        Jtop += 1
    cur = tuple_coeffs(r, d, s, p, X, Jtop)
    tot = 0
    for m, c in cur.items():
        if t * m <= Nb + G:
            tot += c << (Nb + G - t * m)
    digits = bin(tot // (p ** (r * s * Jtop) << G))[2:].zfill(Nb)[-Nb:]
    dev = 0.0
    for k in (1, 2, 3):
        counts = {}
        for i in range(Nb - k + 1):
            counts[digits[i : i + k]] = counts.get(digits[i : i + k], 0) + 1
        for pat in product("01", repeat=k):
            f = counts.get("".join(pat), 0) / (Nb - k + 1)
            dev = max(dev, abs(f - 2.0**-k))
    return dev


def check_c2_digits():
    Nb = 20000
    rows = [(lbl, digit_deviation(r, d, s, Nb)) for lbl, r, d, s in
            (("C(2,3,1,2)^2", 2, 2, 1), ("C(2,3,1,3)^3", 3, 3, 1), ("C(2,3,1,4)^3", 3, 4, 1),
             ("C(2,3,0,2)^2", 2, 2, 0))]
    assert rows[-1][1] > 0.3  # the unweighted square is visibly non-normal
    print("C2: max block-frequency deviation (k <= 3), first 20000 bits (evidence only): "
          + "; ".join(f"{lbl} {dv:.4f}" for lbl, dv in rows))


# ================================================================ C3


class Coords:
    """Coordinates a/p^h in (0, p) with h <= Hmax, scaled by p^Hmax; per-loss sorted d-th powers."""

    def __init__(self, p, d, Hmax):
        self.p, self.d, self.Hmax = p, d, Hmax
        self.pow = [sorted((a * p ** (Hmax - h)) ** d for a in range(1, p ** (h + 1)) if a % p)
                    for h in range(Hmax + 1)]
        self.scale = p ** (d * Hmax)

    def key(self, a, h):
        return (a * self.p ** (self.Hmax - h)) ** self.d


def near_tuples(C, monomials, xi, Delta, pi):
    """Slot tuples (any monomial) of weighted level < pi with |S - xi| <= Delta.

    monomials: list of (coefficient, orders).  Returns (S, weight, index) triples.
    The slots are enumerated with the highest orders first and the last slot solved by bisection.
    """
    found = []
    for idx, (_, orders) in enumerate(monomials):
        orders = sorted(orders, reverse=True)
        k = len(orders)

        def rec(slot, partial, budget):
            o = orders[slot]
            if slot == k - 1:
                for h in range(C.Hmax + 1):
                    if o * h >= budget:
                        break
                    lst = C.pow[h]
                    i0 = bisect_left(lst, xi - Delta - partial)
                    i1 = bisect_right(lst, xi + Delta - partial)
                    for x in lst[i0:i1]:
                        found.append((partial + x, pi - budget + o * h, idx))
                return
            for h in range(C.Hmax + 1):
                if o * h >= budget:
                    break
                for x in C.pow[h]:
                    if partial + x > xi + Delta:
                        break
                    rec(slot + 1, partial + x, budget - o * h)

        rec(0, 0, pi)
    return found


def jump_and_gap(C, monomials, xi, pi):
    p = C.p
    Delta = C.scale // 10
    tup = near_tuples(C, monomials, xi, Delta, pi)
    jump = sum(monomials[i][0] * p**w for S, w, i in tup if S == xi) % p**pi
    others = [abs(S - xi) for S, w, i in tup if S != xi]
    return jump, (min(others) if others else Delta)


def check_c3_tied():
    p, d = 3, 4
    # P1 = X1^3 + 7 X1 X2 + 11 X3, orders (1,2,3): all three monomials have top depth 3.
    P1 = [(1, [1, 1, 1]), (7, [1, 2]), (11, [3])]
    H, pi = 6, 6 + val(6, p) + 1
    C = Coords(p, d, pi)
    rng = random.Random(5)
    count = 0
    for _ in range(4):
        # dominant-loss anchor (h1, h2) = (1, 2), z of loss v = 3; anchors <= theta = 6^(-1/4)
        a1 = rng.choice([1])
        a2 = rng.choice([1, 2, 4, 5])
        m = rng.choice([m for m in range(22, 81) if m % 3])
        xi = C.key(a1, 1) + C.key(a2, 2) + C.key(m, 3)
        jump, gap = jump_and_gap(C, P1, xi, pi)
        assert jump == (6 * p**H) % p**pi and jump != 0
        assert gap > 0
        count += 1
    # P2 = X1^2 X3 + 5 X1 X2^2, both of top depth 5; target X1^2 X3 with X3 on the bounded loss h1.
    P2 = [(1, [1, 1, 3]), (5, [1, 2, 2])]
    h1, h2, v = 1, 2, 3
    H = h1 + h2 + v
    pi = H + 2 * h1 + val(2, p) + 1
    C = Coords(p, d, pi)
    for a2, m in ((1, 25), (4, 26), (5, 23)):
        xi = C.key(1, h1) + C.key(a2, h2) + C.key(m, v)
        jump, gap = jump_and_gap(C, P2, xi, pi)
        assert jump == (2 * p ** (H + 2 * h1)) % p**pi and jump != 0 and gap > 0
        # the X1 X2^2 contribution at the same point has valuation H + h1 + h2 > H + 2 h1
        count += 1
    # P3 = X1 X2 X4 - X1 X3^2, orders (1,2,3,4): equal top depth 7.  Loss-0 coordinates cancel.
    P3 = [(1, [1, 2, 4]), (-1, [1, 3, 3])]
    Hz = 4
    pi0 = Hz + 1
    C = Coords(p, d, 2 * Hz + 1)
    xi = 2 * C.key(1, 0) + C.key(25, Hz)
    tup = near_tuples(C, P3, xi, 0, 2 * Hz + 1)
    jump_full = sum(P3[i][0] * p**w for S, w, i in tup if S == xi)
    assert jump_full % p**pi0 == 0 and val(jump_full, p) == 2 * Hz  # leading jump cancels
    # bounded positive losses (h1, h2) = (1, 2) on the higher orders separate the two monomials
    h1, h2, v = 1, 2, 3
    pi = v + 2 * h2 + 4 * h1 + 1
    C = Coords(p, d, pi)
    xi = C.key(1, h1) + C.key(1, h2) + C.key(25, v)
    jump, gap = jump_and_gap(C, P3, xi, pi)
    assert jump == p ** (pi - 1) % p**pi and gap > 0
    count += 1
    print(f"C3: exact jumps at {count} tied centres: X1^3+7X1X2+11X3 gives 6*3^H; X1^2X3+5X1X2^2 gives "
          f"2*3^(H+2h1); X1X2X4-X1X3^2 cancels at loss-0 centres (valuation 2H) but not at bounded losses")


def relevant_count(p, orders, pi):
    """Exact number of slot tuples with sum_j o_j h_j < pi (coordinates of loss h: (p-1) p^h)."""
    total = 0

    def rec(j, budget, acc):
        nonlocal total
        if j == len(orders):
            total += acc
            return
        h = 0
        while orders[j] * h < budget:
            rec(j + 1, budget - orders[j] * h, acc * (p - 1) * p**h)
            h += 1

    rec(0, pi, 1)
    return total


def check_c3_excess():
    """Higher orders on growing losses inflate the relevant competitors by p^(excess)."""
    p, H = 3, 16
    orders = [[1, 1, 3], [1, 2, 2]]
    bounded = sum(relevant_count(p, o, H + 2 * 1 + 1) for o in orders)
    grown = sum(relevant_count(p, o, H + 2 * (H // 4) + 1) for o in orders)
    # bounded design: O(H p^H) competitors; grown design: p^(H/2) times more
    assert bounded < 1000 * H * p**H
    assert grown > p ** (H // 2 - 2) * bounded  # excess grows from 2 to H/2
    print(f"C3: relevant competitors at H={H}: {bounded} (order 3 on loss 1) vs {grown} (order 3 on loss H/4);"
          f" ratio {grown / bounded:.0f} > 3^(H/2-2) = {p ** (H // 2 - 2)}")


# ================================================================ C4

AUX = [q for q in primes_upto(400) if q not in (2, 3)]


def hybrid_mu(k, polluted=False):
    """Auxiliary prime l_j at index k = 2^(2^j), j >= 0 (prime to 3, so log Lambda_K = o(log K));
    optionally also a polluting index 27 = 3^3."""
    if polluted and k == 27:
        return 5
    if k >= 2 and k & (k - 1) == 0:
        e = k.bit_length() - 1
        if e & (e - 1) == 0:
            return AUX[e.bit_length() - 1]
    return 1


def check_c4_denominators():
    """Reduced denominators of the shifted prefixes of the hybrid W on the schedule 2 k^5."""
    p, s, d, t = 3, 1, 5, 2
    rng = random.Random(7)
    count = 0
    for _ in range(12):
        K = rng.randrange(2, 300)
        n = rng.randrange(t * K**d, t * (K + 1) ** d)
        JK = max(val(k, p) for k in range(1, K + 1))
        Lam = 1
        for k in range(1, K + 1):
            Lam *= hybrid_mu(k)
        D = p ** (s * JK) * Lam
        N = 0
        for k in range(1, K + 1):
            N += (D // (p ** (s * val(k, p)) * hybrid_mu(k))) * pow(2, n - t * k**d, D)
        q = D // gcd(N % D, D)
        assert q == D  # every introduced auxiliary prime and the full 3-depth survive
        count += 1
    print(f"C4: hybrid W = sum 3^(-v(k)) mu_k^(-1) 2^(-2k^5), l_j at k = 2^(2^j): reduced denominator "
          f"= 3^(floor log_3 K) * prod l_j exactly at {count} random shifts")


def square_residue(n, J, L, polluted, with_aux=True):
    p, s, d, t = 3, 1, 5, 2
    mod = p**L
    g = pow(2**t, -1, mod)
    imax = 1
    while t * (imax + 1) ** d <= n:
        imax += 1
    w = [0] * (imax + 1)
    for i in range(1, imax + 1):
        mu = hybrid_mu(i, polluted) if with_aux else 1
        w[i] = p ** (s * (J - val(i, p))) * pow(mu, -1, mod) * pow(g, i**d, mod) % mod
    tot = 0
    for i in range(1, imax + 1):
        for j in range(1, imax + 1):
            if t * (i**d + j**d) > n:
                break
            tot += w[i] * w[j]
    return tot % mod


def check_c4_residues():
    """Auxiliary indices prime to p leave the frozen 3-adic residue of W^2 unchanged."""
    p, d, t, L, s = 3, 5, 2, 2, 1
    J = -(-(L * d + L * s) // (s * d))
    rng = random.Random(11)
    same = 0
    for _ in range(8):
        n = rng.randrange(t * p ** (d * J), t * p ** (d * (J + 1)))
        assert square_residue(n, J, L, False) == square_residue(n, J, L, False, with_aux=False)
        same += 1
    # an auxiliary prime at an index of full valuation (27 = 3^J) changes the residue
    n = 4 * 27**5 + 12345
    assert t * p ** (d * J) <= n < t * p ** (d * (J + 1))
    assert square_residue(n, J, L, True) != square_residue(n, J, L, False)
    print(f"C4: 3^(2J) b^(-n) R_n mod 3^{L} of W^2 equals that of C(2,3,1,5)^2 at {same} shifts (J = {J});"
          " an auxiliary prime at index 27 = 3^J changes it")


def check_c4_periods():
    """Exact denominators and periods of the shifted prefixes of W^2 against the complete-period budget."""
    p, s, d, t = 3, 1, 5, 2
    rows = []
    for K in (40, 90, 200):
        n = t * K**d + 7
        JK = max(val(k, p) for k in range(1, K + 1))
        Lam = 1
        for k in range(1, K + 1):
            Lam *= hybrid_mu(k)
        D = p ** (2 * s * JK) * Lam**2
        N = 0
        for i in range(1, K + 1):
            for j in range(1, K + 1):
                e = n - t * (i**d + j**d)
                if e < 0:
                    break
                N += (D // (p ** (s * (val(i, p) + val(j, p))) * hybrid_mu(i) * hybrid_mu(j))) * pow(2, e, D)
        q = D // gcd(N % D, D)
        per = mult_order(2, q)
        assert D % q == 0 and per <= t * p ** (2 * s * JK) * Lam**2
        assert val(q, p) >= 2 * s * JK - 2  # near-full 3-adic depth (the mass may vanish mod 3)
        rows.append((K, n, q, per, 2 * s * JK - val(q, p)))
    print("C4: W^2 at shifts n = 2K^5+7: (K, log10 n, log10 q_n, log10 period, depth defect) = "
          + ", ".join(f"({K}, {log(n, 10):.1f}, {log(q, 10):.1f}, {log(per, 10):.1f}, {df})" for K, n, q, per, df in rows))


def check_c4_thresholds():
    """Primorial versus lcm(l-1) for the first k off-radix primes (b = 2, p = 3 removed)."""
    ells = [q for q in primes_upto(40000) if q not in (2, 3)]
    rows = []
    maxexp = {}
    logLam = 0.0
    for k, ell in enumerate(ells, start=1):
        logLam += log(ell)
        for q, e in factor(ell - 1).items():
            if e > maxexp.get(q, 0):
                maxexp[q] = e
        if k in (100, 1000, 3000):
            logA = sum(e * log(q) for q, e in maxexp.items())
            rows.append((k, ell, logLam, logA, k * log(k)))
    k, ell, logLam, logA, klogk = rows[-1]
    assert logA < 0.5 * logLam  # periods at r = 1 are far below the primorial
    print("C4: first k off-radix primes: (k, log primorial, log lcm(l-1), k log k) = "
          + ", ".join(f"({k}, {a:.0f}, {b2:.0f}, {c:.0f})" for k, _, a, b2, c in rows))
    # quasi-polynomial schedule n_K = 2K exp((log K)^2) with l_j at indices ~ e^j: budget ratio
    ratios = []
    for lgK in (10, 20, 40, 80, 160):
        J = int(lgK / log(3))
        Lam = sum(log(q) for q in ells[: int(lgK)])
        budget = 3 * lgK + 3 * J * log(3) + 3 * Lam  # r = 3: K^r runs times 3^(rJ) Lambda^r
        ratios.append(budget / (lgK**2 + lgK + log(2)))
    assert all(a > b2 for a, b2 in zip(ratios, ratios[1:])) and ratios[-1] < 0.25
    print("C4: quasi-polynomial schedule, r = 3: log(runs * period) / log n_K at log K = 10..160: "
          + ", ".join(f"{x:.2f}" for x in ratios))


def main():
    check_c1_freezing()
    check_c1_counterexample()
    check_c1_inflation()
    check_c1_margins()
    check_c2_counts()
    check_c2_orbits()
    check_c2_barrier()
    check_c2_digits()
    check_c3_tied()
    check_c3_excess()
    check_c4_denominators()
    check_c4_residues()
    check_c4_periods()
    check_c4_thresholds()
    print("phase21 nonlinear checks passed")


if __name__ == "__main__":
    main()
