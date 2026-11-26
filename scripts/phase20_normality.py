"""Exact controls for Phase 20 Track C (protected poles, all-prime polynomials, dense cubes).

Run from the repository root:  python -B scripts/phase20_normality.py

C1  W = sum_k 1/(p^{k^2} l_k b^{2^{k^3}}): window rule, exact p-adic pole of every
    retained shifted prefix of P(W) (degrees 1-3, rational coefficients), complementary
    support, surviving p-grid, newest-prime persistence, brute-force grid structure and
    Liouville exponents.
C2  Two generators on one prime (rationally independent depth weights) with auxiliary
    primes, and two protected primes with auxiliary primes and CRT-programmed numerators.
C3  The q-th derivative of (x^d+B)^(1/d) from exact Taylor coefficients, the cubic p-adic
    mass and its flank residues at isolated level-H centres, measures of the isolated
    neighbourhoods, a balanced quartic coincidence, and the exponent bookkeeping of the
    pair-correlation estimate.
All arithmetic is exact (integers and fractions); no floating point enters an assertion
except the reported measures and the final margin scans, which use exact Fractions.
"""

from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import comb, factorial, gcd, isqrt, lcm, log2, prod

# ---------------------------------------------------------------- arithmetic helpers


def factor(n):
    result, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            result[d] = result.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def is_prime(n):
    return n > 1 and factor(n) == {n: 1}


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


def prime_power_order(b, ell, f):
    m = ell**f
    assert gcd(b, m) == 1
    order = ell ** (f - 1) * (ell - 1)
    for r in set(factor(ell - 1)) | ({ell} if f > 1 else set()):
        while order % r == 0 and pow(b, order // r, m) == 1:
            order //= r
    return order


def order_mod(b, fac):
    """Multiplicative order of b modulo prod ell^f, from a known factorization."""
    return lcm(1, *(prime_power_order(b, ell, f) for ell, f in fac.items()))


def aux_primes(b, p, count):
    out, n = [], 2
    while len(out) < count:
        if is_prime(n) and b % n and n != p:
            out.append(n)
        n += 1
    return out


def grid_exponent(b, p, e, Qfac):
    """Exact surviving p-grid exponent max(0, e - w) of Phase 19 grids.md section 1."""
    d = prime_power_order(b, p, 1)
    t = lcm(d, order_mod(b, Qfac)) if Qfac else d
    big = p ** (e + 40)
    w = val(pow(b, t, big) - 1, p) if pow(b, t, big) != 1 else e + 40
    return max(0, e - w), w, t


def reduced_den(num_mod, D):
    """Reduced denominator of (num_mod / D) mod 1."""
    return D // gcd(num_mod % D, D)


# ---------------------------------------------------------------- C1


def c1_terms(b, p, K):
    ell = aux_primes(b, p, K)
    n = {k: 2 ** (k**3) for k in range(0, K + 2)}
    n[0] = 0
    den = {k: p ** (k * k) * ell[k - 1] for k in range(1, K + 1)}
    return ell, n, den


def c1_tuples(P, K, den, n):
    """Ordered-tuple expansion of P(W) restricted to indices <= K, grouped by multiset.

    Each item: (multiset, position, coefficient as Fraction)."""
    out = []
    for j, a in enumerate(P):
        if a == 0:
            continue
        if j == 0:
            out.append(((), 0, Fraction(a)))
            continue
        for ms in combinations_with_replacement(range(1, K + 1), j):
            mult = factorial(j)
            for idx in set(ms):
                mult //= factorial(ms.count(idx))
            out.append((ms, sum(n[i] for i in ms), Fraction(a) * mult / prod(den[i] for i in ms)))
    return out


def shifted_den(b, tuples, N):
    """Reduced denominator of the shifted prefix b^N * (sum over tuples with position <= N)."""
    present = [(ms, pos, c) for ms, pos, c in tuples if pos <= N]
    D = lcm(1, *(c.denominator for _, _, c in present))
    num = sum(c.numerator * (D // c.denominator) * pow(b, N - pos, D) for _, pos, c in present)
    return reduced_den(num, D), present


def check_c1():
    cases = [(2, 3), (3, 5), (10, 3), (2, 7), (5, 3)]
    polys = [
        [Fraction(0), Fraction(1)],                                   # W
        [Fraction(1), Fraction(-1, 2), Fraction(3)],                  # 3W^2 - W/2 + 1
        [Fraction(-1, 3), Fraction(7), Fraction(0), Fraction(2, 5)],  # (2/5)W^3 + 7W - 1/3
        [Fraction(0), Fraction(0), Fraction(-2), Fraction(9)],        # 9W^3 - 2W^2 (v_3(A)=2)
    ]
    checked = grids = poles = 0
    K = 4
    for b, p in cases:
        ell, n, den = c1_terms(b, p, K + 1)
        a_lift = val(pow(b, prime_power_order(b, p, 1), p**30) - 1, p)
        for P in polys:
            r = len(P) - 1
            M = lcm(1, *(c.denominator for c in P))
            A1 = int(P[-1] * M)
            k1 = 2
            while not (min((k1 - 1) ** 2, 2 * k1 - 1) > val(A1, p) + max(val(comb(r, l), p) for l in range(1, r + 1))):
                k1 += 1
            tuples = c1_tuples(P, K + 1, den, n)
            for k in range(2, K + 1):
                shifts = []
                for l in range(1, r + 1):
                    shifts.append((l, l * n[k] + r * n[k - 1] + 1))
                    shifts.append((l, (l + 1) * n[k] - 1 if l < r else n[k + 1] - 1))
                for l, N in shifts:
                    assert min(r, N // n[k]) == l
                    q, present = shifted_den(b, tuples, N)
                    # window rule: present tuples are exactly those on indices <= k with
                    # at most l copies of k
                    for ms, pos, c in tuples:
                        expect = (not ms) or (max(ms) <= k and ms.count(k) <= l)
                        assert (pos <= N) == expect, (b, p, P, k, N, ms)
                    e = val(q, p)
                    D_rl = (r - l) * (k - 1) ** 2 + l * k * k
                    if k >= k1:
                        assert e == D_rl - val(A1 * comb(r, l), p) + val(M, p), (b, p, P, k, l, e)
                        poles += 1
                    # complementary support
                    Q = q // p**e
                    allowed = M * prod(ell[j - 1] ** r for j in range(1, k + 1))
                    assert allowed % Q == 0
                    if l == r and (A1 * M) % ell[k - 1]:
                        assert val(q, ell[k - 1]) == r
                    # surviving grid
                    Qfac = factor(Q) if Q > 1 else {}
                    g, w, t = grid_exponent(b, p, e, Qfac)
                    bound = a_lift + max([val(x - 1, p) for x in Qfac if x != 2] + [0])
                    assert w <= bound, (b, p, k, w, bound)
                    assert g >= e - bound
                    if k >= k1:
                        assert g >= r * (k - 1) ** 2 + 2 * k - 1 - val(A1, p) - val(comb(r, l), p) - bound
                    grids += 1
                    checked += 1
        # W itself: exact denominator in shell k (no windows when r = 1)
        tuplesW = c1_tuples([0, 1], K + 1, den, n)
        for k in range(1, K + 1):
            for N in (n[k], n[k] + 1, n[k] + n[k - 1], 3 * n[k] + 5, n[k + 1] - 1):
                q, _ = shifted_den(b, tuplesW, N)
                assert q == p ** (k * k) * prod(ell[:k]), (b, p, k, N)
                for j in range(1, k + 1):
                    assert val(q, ell[j - 1]) == 1
    print(f"C1: {checked} retained prefixes of P(W) (4 polynomials, 5 radix/prime pairs, shells 2-4)")
    print(f"    window rule and support at all; exact pole formula at {poles} (k >= k1); {grids} surviving grids")


def check_c1_bruteforce():
    """Full-orbit grid structure for actual small prefixes of W."""
    count = 0
    for b, p, P, N in [(2, 3, [0, 1], 2**8 + 3), (2, 3, [0, 1], 2**8 + 100), (3, 5, [0, 1], 2**8 + 7),
                       (2, 5, [0, 1], 2**8 + 1)]:
        ell, n, den = c1_terms(b, p, 3)
        tuples = c1_tuples(P, 3, den, n)
        present = [(ms, pos, c) for ms, pos, c in tuples if pos <= N]
        D = lcm(1, *(c.denominator for _, _, c in present))
        num = sum(c.numerator * (D // c.denominator) * pow(b, N - pos, D) for _, pos, c in present) % D
        g0 = gcd(num, D)
        A, q = num // g0, D // g0
        e = val(q, p)
        Q = q // p**e
        G_exp, w, t = grid_exponent(b, p, e, factor(Q))
        G = p**G_exp
        P_ord = order_mod(b, factor(q))
        assert P_ord == t * G
        orbit = [A * pow(b, i, q) % q for i in range(P_ord)]
        for c in range(t):
            cls = sorted(orbit[c::t])
            base = A * pow(b, c, q) % (q // G)
            assert cls == sorted(base + (q // G) * j for j in range(G))
        count += 1
    print(f"C1: brute-force orbits of {count} actual prefixes split into t grids of exactly G points")


def check_c1_liouville():
    b, p = 2, 3
    ell, n, _ = c1_terms(b, p, 7)
    ratios = []
    for k in range(1, 6):
        logden = 3 * (n[k] * log2(b) + k * k * log2(p) + sum(log2(x) for x in ell[:k]))
        ratios.append(n[k + 1] / logden)
    assert all(x < y for x, y in zip(ratios, ratios[1:])) and ratios[-1] > 1e20
    print("C1: Liouville exponent ratio n_{k+1}/log2(den P(U_k)) for cubic P:",
          ", ".join(f"{x:.3g}" for x in ratios))


# ---------------------------------------------------------------- C2


def multi_tuples(P, coeffs, n, K):
    """Expansion of P(X_1,...,X_m) on indices <= K.  P: {exponent vector: integer}.

    coeffs[a][k] is the Fraction coefficient of X_a at step k.  Items: (counts of the
    newest index per variable as a dict of multisets, position, coefficient)."""
    out = []
    for nu, c0 in P.items():
        per_var = []
        for a, e in enumerate(nu):
            choices = []
            for ms in combinations_with_replacement(range(1, K + 1), e):
                mult = factorial(e)
                for i in set(ms):
                    mult //= factorial(ms.count(i))
                choices.append((ms, mult * prod((coeffs[a][i] for i in ms), start=Fraction(1))))
            per_var.append(choices)
        for pick in product(*per_var):
            mss = tuple(ms for ms, _ in pick)
            pos = sum(n[i] for ms in mss for i in ms)
            out.append((mss, pos, c0 * prod((c for _, c in pick), start=Fraction(1))))
    return out


def check_c2_shared_prime():
    """Variant 1: one prime p, depths floor(gamma_a k^2), gamma = (1, sqrt 2), auxiliary l_k."""
    b, p, K = 2, 3, 4
    ell = aux_primes(b, p, K + 1)
    n = {k: 2 ** (k**3) for k in range(1, K + 2)}
    n[0] = 0
    depth = [lambda k: k * k, lambda k: isqrt(2 * k**4)]
    coeffs = [{k: Fraction(1, p ** depth[a](k) * ell[k - 1]) for k in range(1, K + 2)} for a in range(2)]
    P = {(2, 1): 1, (0, 2): -3, (1, 1): 5, (1, 0): 1}
    winner = (2, 1)            # gamma.nu = 2 + sqrt 2 is the unique maximum
    r = 3
    tuples = multi_tuples(P, coeffs, n, K + 1)
    count = 0
    for k in range(2, K + 1):
        for l in range(1, r + 1):
            for N in (l * n[k] + r * n[k - 1] + 1, ((l + 1) * n[k] - 1) if l < r else n[k + 1] - 1):
                q, _ = shifted_den(b, tuples, N)
                # best new-count vector j <= winner with |j| <= l, by gamma.j (exact: compare
                # j1 + sqrt2 j2 via integer arithmetic)
                cands = [(j1, j2) for j1 in range(winner[0] + 1) for j2 in range(winner[1] + 1) if j1 + j2 <= l]
                key = lambda j: (j[0] + j[1] * Fraction(isqrt(2 * 10**40), 10**20))
                j = max(cands, key=key)
                pred = sum(winner[a] * depth[a](k - 1) + j[a] * (depth[a](k) - depth[a](k - 1)) for a in range(2))
                pred -= val(P[winner] * comb(winner[0], j[0]) * comb(winner[1], j[1]), p)
                assert val(q, p) == pred, (k, l, N, val(q, p), pred)
                Q = q // p ** val(q, p)
                assert (prod(ell[i] for i in range(k)) ** (2 * r)) % Q == 0
                count += 1
    print(f"C2: shared prime, two generators with auxiliary primes: exact winning pole at {count} prefixes")


def check_c2_two_primes():
    """Variant 2: protected primes 3 and 5, auxiliary primes coprime to 30, CRT numerators."""
    b, ps, K, C = 2, (3, 5), 4, 3
    ell = [x for x in range(7, 200) if is_prime(x)][: K + 1]
    n = {k: 2 ** (k**3) for k in range(1, K + 2)}
    n[0] = 0
    E = {k: C * k + k * k for k in range(0, K + 2)}
    theta = {(0, 1): 1, (1, 0): 2}   # theta[(i, j)]: limit of X_j in Z_{p_i}
    A = {0: {}, 1: {}}

    def U_mod(j, k, i, prec):
        m = ps[i] ** prec
        return sum(A[j][kk] * pow(ps[j] ** E[kk] * ell[kk - 1] * pow(b, n[kk], m), -1, m) for kk in range(1, k + 1)) % m

    for k in range(1, K + 2):
        for j in range(2):
            i = 1 - j
            mod_i = ps[i] ** k
            target = ps[j] ** E[k] * ell[k - 1] * pow(b, n[k], mod_i) * (theta[(i, j)] - U_mod(j, k - 1, i, k)) % mod_i
            mod_j = ps[j] * ell[k - 1]
            # CRT: A = 1 mod p_j l_k, A = target mod p_i^k; least positive representative
            M_all = mod_j * mod_i
            a = (1 * mod_i * pow(mod_i, -1, mod_j) + target * mod_j * pow(mod_j, -1, mod_i)) % M_all or M_all
            A[j][k] = a
            w = Fraction(a, ps[j] ** E[k] * ell[k - 1])
            assert 0 < w <= 1 and w.denominator == ps[j] ** E[k] * ell[k - 1]
            assert U_mod(j, k, i, k) == theta[(i, j)] % mod_i
    coeffs = [{k: Fraction(A[j][k], ps[j] ** E[k] * ell[k - 1]) for k in range(1, K + 2)} for j in range(2)]
    P = {(2, 1): 1, (0, 1): -7}       # X1^2 X2 - 7 X2
    tuples = multi_tuples(P, coeffs, n, K + 1)
    r, count = 3, 0
    for k in range(3, K + 1):
        for l in range(1, r + 1):
            for N in (l * n[k] + r * n[k - 1] + 1, ((l + 1) * n[k] - 1) if l < r else n[k + 1] - 1):
                q, _ = shifted_den(b, tuples, N)
                # prime 5 protects X2 (degree 1, f = X1^2 - 7 -> theta^2 - 7 = -6, a 5-unit)
                assert val(q, 5) == E[k], (k, l, val(q, 5))
                # prime 3 protects X1 (degree 2, f = X2 -> theta = 2, a 3-unit)
                t = min(2, l)
                assert val(q, 3) == 2 * E[k - 1] + t * (E[k] - E[k - 1]) - val(comb(2, t), 3)
                for pi, other in ((3, 5), (5, 3)):
                    e = val(q, pi)
                    e_other = val(q, other)
                    Qfac = factor(q // (pi**e * other ** e_other))
                    if e_other:
                        Qfac[other] = e_other
                    g, wloss, _ = grid_exponent(b, pi, e, Qfac)
                    a_i = val(pow(b, prime_power_order(b, pi, 1), pi**20) - 1, pi)
                    bound = a_i + max([val(prime_power_order(b, other, 1), pi)] +
                                      [val(x - 1, pi) for x in Qfac if x != other])
                    assert wloss <= bound and g >= e - bound
                count += 1
    print(f"C2: two protected primes with auxiliary primes: weights in (0,1], congruences, exact poles "
          f"at both primes and bounded grid loss at {count} prefixes")


# ---------------------------------------------------------------- C3


def taylor(x0, y0, d, order):
    """Exact Taylor coefficients c_0..c_order of y(x) with y^d = x^d + B at (x0, y0)."""
    B = y0**d - x0**d
    c = [Fraction(y0)]

    def power_coeff(series, e, m):
        acc = [Fraction(1)] + [Fraction(0)] * m
        for _ in range(e):
            acc = [sum(acc[i] * series[t - i] for i in range(t + 1) if t - i < len(series)) for t in range(m + 1)]
        return acc[m]

    for m in range(1, order + 1):
        trial = c + [Fraction(0)]
        rest = power_coeff(trial, d, m)
        rhs = comb(d, m) * Fraction(x0) ** (d - m) if m <= d else Fraction(0)
        c.append((rhs - rest) / (d * Fraction(y0) ** (d - 1)))
    return B, c


def phi(q, d):
    """Phi_q(X, B) as {(i, j): coeff} for X^i B^j, with f^(q) = (d-1) B x^(d-q) y^(1-qd) Phi_q."""
    P = {(0, 0): Fraction(1)}
    for qq in range(2, q):
        new = {}

        def add(key, v):
            new[key] = new.get(key, 0) + v
        for (i, j), v in P.items():
            add((i, j + 1), (d - qq) * v)            # (d-q) B
            add((i + 1, j), (d - qq + 1 - qq * d) * v)  # (d-q) X + (1-qd) X
            if i:
                add((i + 1, j), d * i * v)              # d X^2 dPhi/dX
                add((i, j + 1), d * i * v)              # d X B dPhi/dX
        P = {k: v for k, v in new.items() if v}
    return P


def check_c3_derivatives():
    pts = [(Fraction(1, 2), Fraction(3, 2)), (Fraction(5, 4), Fraction(1)), (Fraction(2), Fraction(7, 3)),
           (Fraction(3, 5), Fraction(2, 7))]
    count = 0
    for d in range(4, 8):
        for x0, y0 in pts:
            B, c = taylor(x0, y0, d, 6)
            for q in range(2, 7):
                ph = phi(q, d)
                X = x0**d
                value = (d - 1) * B * x0 ** (d - q) * y0 ** (1 - q * d) * sum(v * X**i * B**j for (i, j), v in ph.items())
                assert value == factorial(q) * c[q], (d, q)
                lead = ph.get((q - 2, 0), 0)
                assert lead == (-1) ** q * prod(range(d + 1, d + q - 1))
                count += 1
        ph4 = phi(4, d)
        assert ph4 == {k: v for k, v in {(2, 0): (d + 1) * (d + 2), (1, 1): -(d + 1) * (4 * d - 7),
                                         (0, 2): (d - 2) * (d - 3)}.items() if v}
    # d = 4: roots of Phi_4 in X are B (45 +- sqrt 1785)/60, both of the sign of B
    disc = 45**2 - 4 * 30 * 2
    assert disc == 1785 and 45 > isqrt(disc)
    print(f"C3: f^(q) = (d-1) B x^(d-q) (x^d+B)^(1/d-q) Phi_q(x^d,B) verified exactly at {count} "
          "(d,q,point) triples; leading coefficient (-1)^q (d+1)...(d+q-2); Phi_4 explicit")


def coords(p, H):
    return {h: [a for a in range(1, p ** (h + 1)) if a % p] for h in range(H + 1)}


def multisets(p, d, Hmax, Hscale, extra_diag=False):
    """All multisets {z1,z2,z3} with total loss <= Hmax: (S scaled by p^(d Hscale), level, perms, losses)."""
    C = coords(p, Hmax + 1)
    out = []
    for h1 in range(Hmax + 1):
        for h2 in range(h1, Hmax + 1 - h1):
            for h3 in range(h2, Hmax + 1 - h1 - h2):
                hs = (h1, h2, h3)
                for trip in _triples(C, hs):
                    S = sum(a**d * p ** (d * (Hscale - h)) for a, h in zip(trip, hs))
                    perms = 6 // prod(factorial(sum(1 for x in zip(trip, hs) if x == y)) for y in set(zip(trip, hs)))
                    out.append((S, h1 + h2 + h3, perms, hs, trip))
    if extra_diag and (Hmax + 1) % 3 == 0:
        h = (Hmax + 1) // 3
        for a in C[h]:
            out.append((3 * a**d * p ** (d * (Hscale - h)), Hmax + 1, 1, (h, h, h), (a, a, a)))
    return out


def _triples(C, hs):
    h1, h2, h3 = hs
    if h1 == h2 == h3:
        yield from combinations_with_replacement(C[h1], 3)
    elif h1 == h2:
        for x, y in combinations_with_replacement(C[h1], 2):
            for z in C[h3]:
                yield (x, y, z)
    elif h2 == h3:
        for x in C[h1]:
            for y, z in combinations_with_replacement(C[h2], 2):
                yield (x, y, z)
    else:
        for x in C[h1]:
            for y in C[h2]:
                for z in C[h3]:
                    yield (x, y, z)


def isolation_measure(p, d, H, eps, window, check_flanks=0):
    """Measure of the union of radius-delta/2 intervals about isolated level-H centres."""
    Hs = H + 1
    scale = p ** (d * Hs)
    rel = multisets(p, d, H, Hs, extra_diag=(p == 3))
    prec = H + 1 + val(6, p)
    vals = {}
    for S, lev, perms, hs, trip in rel:
        vals.setdefault(S, []).append((lev, perms, hs))
    keys = sorted(vals)
    delta = Fraction(eps, H * H * p**H)
    dint = delta * scale
    lo, hi = window[0] * scale, window[1] * scale
    isolated = []
    for idx, S in enumerate(keys):
        if not (lo <= S <= hi) or len(vals[S]) != 1:
            continue
        lev, perms, hs = vals[S][0]
        if lev != H or (perms * p**H) % p**prec == 0:
            continue
        left = S - keys[idx - 1] if idx else None
        right = keys[idx + 1] - S if idx + 1 < len(keys) else None
        if (left is None or left > dint) and (right is None or right > dint):
            isolated.append((S, perms, hs))
    if check_flanks:
        full = multisets(p, d, H + 1, Hs) if p == 3 else rel
        mod = p**prec
        pts = sorted((S, perms * p**lev % mod) for S, lev, perms, _, _ in full)
        import bisect
        xs = [s for s, _ in pts]
        pref = [0]
        for _, w in pts:
            pref.append((pref[-1] + w) % mod)

        def M(u):
            return pref[bisect.bisect_right(xs, u)]
        step = max(1, len(isolated) // check_flanks)
        for S, perms, _ in isolated[::step]:
            jump = (M(S + dint / 2) - M(S - dint / 2)) % mod
            assert jump == perms * p**H % mod != 0
            assert M(S - dint / 2) == M(S - dint + 1) or dint < 2
    prim = [x for x in isolated if x[2] == (0, 0, H)]
    dom = [x for x in isolated if x[2][0] < x[2][1] < x[2][2] and x[2][1] >= 2 * x[2][0] + 1]
    width = window[1] - window[0]
    return {name: (float(len(v) * delta / width), len(v)) for name, v in
            (("all", isolated), ("primitive", prim), ("dominant", dom))}


def check_c3_mass():
    rows = []
    for p, Hs in ((3, range(2, 7)), (5, range(1, 4))):
        for H in Hs:
            res = isolation_measure(p, 4, H, Fraction(1, 4), (Fraction(3, 2), Fraction(p**4 - 2)),
                                    check_flanks=60 if (p, H) in ((3, 4), (3, 5), (5, 3)) else 0)
            rows.append((p, H, res))
            (ma, na), (mp, np_), (mu, nu) = res["all"], res["primitive"], res["dominant"]
            print(f"    p={p} d=4 H={H}: isolated measure / window: all {ma:.4f} ({na}), "
                  f"normalized by H^2/((H+1)(H+2)) {ma * H * H / ((H + 1) * (H + 2)):.4f}; "
                  f"dominant {mu:.4f}; primitive (1,1,c/p^H) {mp:.5f}, times H^2 {mp * H * H:.3f}")
    p3 = [res for p, H, res in rows if p == 3]
    alls = [res["all"][0] * H * H / ((H + 1) * (H + 2)) for (p, H, res) in rows if p == 3]
    assert max(alls[2:]) < 1.15 * min(alls[2:])           # all-centre measure ~ constant
    assert p3[-1]["primitive"][0] < 0.5 * p3[1]["primitive"][0]   # single family decays like 1/H^2
    print("C3: flank residues at sampled isolated centres differ by exactly perms * p^H (mod p^(H+1+v_p(6)))")


def check_c3_coincidences():
    assert 59**4 + 158**4 == 133**4 + 134**4
    assert all(x % 5 for x in (59, 158, 133, 134)) and 158 < 5 * 125
    p, d, Hm = 3, 4, 4
    C = coords(p, Hm)
    sums = {}
    for h1 in range(Hm + 1):
        for h2 in range(h1, Hm + 1):
            for x in C[h1]:
                for y in C[h2]:
                    if h1 == h2 and y < x:
                        continue
                    S = x**d * p ** (d * (Hm - h1)) + y**d * p ** (d * (Hm - h2))
                    sums.setdefault(S, []).append(((h1, x), (h2, y)))
    nontriv = [v for v in sums.values() if len(v) > 1]
    dominant_hits = 0
    for v in nontriv:
        for (ha, a), (hb, bb) in v:
            k = ha + hb
            if hb >= 2 * ha + 1:
                for w in v:
                    if w != ((ha, a), (hb, bb)) and w[0][0] + w[1][0] <= k:
                        dominant_hits += 1
    assert dominant_hits == 0
    print(f"C3: quartic coincidence 59^4+158^4 = 133^4+134^4 gives balanced level-6 B=0 rows at p=5; "
          f"p=3 losses <= {Hm}: {len(nontriv)} nontrivial equal sums, none against a dominant anchor")


def check_c3_exponents():
    """Margins of E1, E2 (pair-correlation exponents) on an exact grid of (alpha, beta)."""
    def margins(r, q, alpha, beta, kappa, gamma):
        K = 2 ** (q - 1)
        e1 = kappa + beta + (1 - q * alpha) / (2 * K - 2)
        e2 = kappa + beta - Fraction(2, K) * alpha + (q * alpha - 1 + kappa) / (2 * K - 2) + gamma / (2 * K - 2)
        return 1 - e1, 1 - e2
    # r = 3, d = 4, q = 4 everywhere, kappa = 1/200, c = 1/8, gamma = c + 2 kappa (d(q-1) - q)
    kappa, c, d = Fraction(1, 200), Fraction(1, 8), 4
    gamma = c + 2 * kappa * (d * 3 - 4)
    worst = min(min(margins(3, 4, Fraction(a, 600), Fraction(bb, 200), kappa, gamma))
                for bb in range(1, 201) for a in range(1, 601)
                if Fraction(bb, 200) / 3 <= Fraction(a, 600) <= Fraction(bb, 200))
    assert worst > 0 and kappa < c / d
    print(f"C3: r=3, d=4, q=4, kappa=1/200, c=1/8: minimum exponent margin {float(worst):.4f} > 0")
    for r in range(3, 9):
        sig = None
        for a in range(1, 1681):
            alpha = Fraction(a, 1680)
            for bb in range(1, 169):
                beta = Fraction(bb, 168)
                if not (beta / r <= alpha <= beta):
                    continue
                best = max(min(margins(r, q, alpha, beta, 0, 0)) for q in range(4, r + 2))
                sig = best if sig is None else min(sig, best)
        exact_sig = Fraction(1, r * (2 ** (r + 1) - 2))
        assert sig == exact_sig, (r, sig, exact_sig)
        print(f"    r={r}: derivative orders 4..{r + 1} cover all competitor classes, exact margin {exact_sig} ({float(sig):.5f})")


def main():
    check_c1()
    check_c1_bruteforce()
    check_c1_liouville()
    check_c2_shared_prime()
    check_c2_two_primes()
    check_c3_derivatives()
    check_c3_mass()
    check_c3_coincidences()
    check_c3_exponents()
    print("phase20 checks passed")


if __name__ == "__main__":
    main()
