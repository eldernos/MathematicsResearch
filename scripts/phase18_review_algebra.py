"""Independent review checks for notes/phase18/principal.md and algebra.md.

These checks were written separately from scripts/phase18_principal.py and use
different enumeration strategies. Run with python -B scripts/phase18_review_algebra.py.
Optional argument: --layers N (default 14) for the flagship square certificate.
Requires numpy only for the Gauss-sum check.
"""

import argparse
import cmath
import math
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def vp(n, p):
    n = abs(n)
    if n == 0:
        return math.inf
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def flog(n, p):
    """Largest J with p**J <= n, for n >= 1."""
    J, power = 0, p
    while power <= n:
        power *= p
        J += 1
    return J


def ordmod(b, m):
    x, k = b % m, 1
    while x != 1:
        x = x * b % m
        k += 1
    return k


def iroot(n, d):
    """Exact floor of the d-th root of a nonnegative integer."""
    if n < 2:
        return n
    x = int(round(n ** (1.0 / d)))
    while x ** d > n:
        x -= 1
    while (x + 1) ** d <= n:
        x += 1
    return x


def nd_discrepancy(numerators, q):
    """Return q*N*D_N for the points k/q (extreme discrepancy, half-open intervals).

    Uses N*D_N = 1 + max_i (i - N x_i) - min_i (i - N x_i), i = 1..N, sorted x.
    """
    xs = sorted(numerators)
    N = len(xs)
    vals = [q * (i + 1) - N * x for i, x in enumerate(xs)]
    return q + max(vals) - min(vals)


# ---------------------------------------------------------------- principal

def check_principal_denominators():
    cases = 0
    for b, p, d, s, K in ((2, 3, 3, 1, 30), (2, 3, 3, 2, 30), (2, 3, 2, 0, 30),
                          (10, 3, 2, 1, 40), (26, 3, 2, 2, 40), (2, 5, 3, 1, 30),
                          (3, 7, 2, 1, 60)):
        t = ordmod(b, p)
        pos = [t * k ** d for k in range(1, K + 1)]
        w = [Fraction(1, p ** (s * vp(k, p))) for k in range(1, K + 1)]
        samples = set()
        for n in pos:
            samples.update((n - 1, n, n + 1))
        samples.update(n - 1 for n in pos[1:])
        for n in sorted(samples):
            if n > pos[-1]:
                continue
            Kn = sum(1 for m in pos if m <= n)
            R = sum((w[i] * b ** (n - pos[i]) for i in range(Kn)), Fraction(0))
            expected = p ** (s * flog(Kn, p)) if Kn else 1
            require(R.denominator == expected, (b, p, d, s, n, R.denominator))
            if Kn and n == pos[Kn - 1]:
                U = sum((w[i] / b ** pos[i] for i in range(Kn)), Fraction(0))
                require(U.denominator == b ** n * expected, (b, p, s, n))
            cases += 1
    return cases


def check_subgroups_and_periods():
    """Order formula, full inverse image, full-period error <= t and
    the L-step error <= p^a L/q + q, all exactly."""
    cases = 0
    worst_ratio = 0.0
    for b, p in ((2, 3), (10, 3), (26, 3), (2, 5), (7, 5), (3, 7), (2, 7), (18, 7)):
        t = ordmod(b, p)
        a = vp(b ** t - 1, p)
        for e in range(1, a + 4):
            q = p ** e
            if q > 20000:
                break
            T = ordmod(b, q)
            require(T == t * p ** max(0, e - a), (b, p, e, T))
            starts = [1, q - 1, (q // 2) | 1 if p != 2 else 1]
            starts = [z for z in starts if z % p]
            for z in starts:
                orbit = [z * pow(b, i, q) % q for i in range(T)]
                if e >= a:
                    classes = {x % p ** a for x in orbit}
                    require(len(classes) == t, (b, p, e))
                    require(set(orbit) == {x for x in range(q) if x % p ** a in classes},
                            (b, p, e))
                # Full period: unnormalized error <= t.
                require(nd_discrepancy(orbit, q) <= t * q, (b, p, e, 'period'))
                lengths = sorted({1, 2, 3, T // 3 + 1, T // 2, T - 1, T, T + 1,
                                  2 * T + T // 2 + 1, 3 * T - 1} - {0})
                for L in lengths:
                    pts = [orbit[i % T] for i in range(L)]
                    err = Fraction(nd_discrepancy(pts, q), q)
                    bound = Fraction(p ** a * L, q) + q
                    require(err <= bound, (b, p, e, L, err, bound))
                    cases += 1
                    # Fragment comparison with sqrt(q) log^2(2q): informational.
                    if L < T:
                        worst_ratio = max(worst_ratio,
                                          float(err) / (math.sqrt(q) * math.log(2 * q) ** 2))
    return cases, worst_ratio


def check_gauss_sums():
    """|tau(Psi, m)| <= sqrt(q * gcd(m, q)) for every character mod p^e."""
    import numpy as np
    cases = 0
    worst = 0.0
    for p, emax in ((3, 6), (5, 4), (7, 3), (11, 2)):
        g = next(x for x in range(2, p * p) if math.gcd(x, p) == 1
                 and ordmod(x, p * p) == p * (p - 1))
        for e in range(1, emax + 1):
            q = p ** e
            phi = q - q // p
            powers = [pow(g, k, q) for k in range(phi)]
            for m in range(q):
                vec = np.exp(2j * np.pi * np.array([m * x % q for x in powers]) / q)
                taus = np.fft.fft(vec)  # tau(Psi_j, m) for all j (up to conjugation)
                bound = math.sqrt(q * math.gcd(m, q))
                top = float(np.max(np.abs(taus)))
                require(top <= bound * (1 + 1e-9) + 1e-9, (p, e, m, top, bound))
                worst = max(worst, top / bound)
                cases += 1
    return cases, worst


def check_lte():
    cases = 0
    for b in range(2, 40):
        for ell in (3, 5, 7, 11, 13):
            if b % ell == 0:
                continue
            u = ordmod(b, ell)
            for h in range(u, 400, u):
                require(vp(b ** h - 1, ell) == vp(b ** u - 1, ell) + vp(h // u, ell),
                        (b, ell, h))
                cases += 1
        if b % 2:
            for h in range(1, 200):
                expected = vp(b - 1, 2) if h % 2 else vp(b * b - 1, 2) + vp(h, 2) - 1
                require(vp(b ** h - 1, 2) == expected, (b, h))
                cases += 1
    return cases


def flagship_discrepancies(exponents=(10, 12, 14, 16, 18)):
    """Numerical D_N of the real orbit of C(2,3,1,3) (floating-point windows)."""
    Nmax = 2 ** max(exponents)
    P = Nmax + 128
    X = 0
    k = 1
    while 2 * k ** 3 <= P:
        X += (1 << (P - 2 * k ** 3)) // 3 ** vp(k, 3)
        k += 1
    bits = bin(X)[2:].rjust(P, '0')
    out = []
    for ex in exponents:
        N = 2 ** ex
        xs = sorted(int(bits[n:n + 60], 2) / 2 ** 60 for n in range(N))
        dplus = max((i + 1) / N - x for i, x in enumerate(xs))
        dminus = max(x - i / N for i, x in enumerate(xs))
        D = dplus + dminus
        out.append((N, D, D * N ** (1 / 3)))
    return out


# ----------------------------------------------------------- E2 layer counts

def check_first_layer_counts():
    """Brute-force check of: first nonempty layer H <= r and 1 <= C_H(u) < p^r,
    for every cell of [1, p^d), when r < d."""
    report = {}
    for p, d, r in ((3, 3, 2), (3, 4, 2), (3, 4, 3), (5, 3, 2), (5, 4, 3),
                    (7, 3, 2), (3, 5, 4), (3, 5, 2), (11, 3, 2)):
        lam = p ** d
        G = p ** (d * r)
        top = lam * G
        coords = {h: [a ** d * p ** (d * (r - h)) for a in range(1, p ** (h + 1)) if a % p]
                  for h in range(r + 1)}
        events = defaultdict(Counter)

        def rec(i, H, total):
            if total >= top:
                return
            if i == r:
                events[max(total, G)][H] += 1
                return
            for h in range(r - H + 1):
                for c in coords[h]:
                    if total + c >= top:
                        break
                    rec(i + 1, H + h, total + c)

        rec(0, 0, 0)
        points = sorted(set(events) | {G, top})
        counts = Counter()
        worst = 0
        cells = 0
        for left, right in zip(points, points[1:]):
            counts.update(events.get(left, Counter()))
            H = min(h for h, c in counts.items() if c)
            CH = counts[H]
            require(H <= r and 1 <= CH < p ** r, (p, d, r, left, H, CH))
            worst = max(worst, CH)
            cells += 1
        report[(p, d, r)] = (cells, worst, p ** r)
    return report


# ------------------------------------------------- E2 direct p-adic depths

def poly_schedule_losses(b, p, s, d, coeffs, Kmax, extra=12):
    """Exact p-adic depth of the shifted prefix of P(X), X = C(b,p,s,d), at every
    insertion event n <= t*Kmax^d. Returns {J: max loss rsJ - depth} per shell J."""
    t = ordmod(b, p)
    r = len(coeffs) - 1
    V = flog(Kmax, p)
    L = r * s * V + extra
    mod = p ** L
    limit = t * Kmax ** d
    base = {}
    for k in range(1, Kmax + 1):
        n = t * k ** d
        base[n] = p ** (s * (V - vp(k, p))) * pow(b, -n, mod) % mod
    convs = [{0: 1}]
    for _ in range(r):
        prev = convs[-1]
        nxt = defaultdict(int)
        for n1, x1 in prev.items():
            for n2, x2 in base.items():
                n = n1 + n2
                if n > limit:
                    break
                nxt[n] = (nxt[n] + x1 * x2) % mod
        convs.append(dict(sorted(nxt.items())))
    events = defaultdict(int)
    for j, c in enumerate(coeffs):
        if c == 0:
            continue
        factor = c * p ** (s * V * (r - j))
        for n, x in convs[j].items():
            events[n] = (events[n] + factor * x) % mod
    A = coeffs[-1]
    S = 0
    losses = {}
    for n in sorted(events):
        S = (S + events[n]) % mod
        K = iroot(n // t, d)
        if K == 0:
            continue
        J = flog(K, p)
        v = vp(S, p) if S else math.inf
        require(v < L, ("precision", b, p, s, d, n))
        depth = r * s * V - v
        loss = r * s * J - depth
        losses[J] = max(losses.get(J, -math.inf), loss)
    return losses, vp(A, p)


def check_polynomial_schedule_normality():
    rows = []
    # (b, p, s, d, coefficients low->high, Kmax, theorem applies?)
    for b, p, s, d, coeffs, Kmax in (
            (2, 3, 2, 3, (0, 0, 1), 243),
            (2, 3, 2, 3, (1, 5, 3), 243),
            (2, 3, 3, 3, (0, 0, 1), 243),
            (2, 5, 2, 3, (0, 0, 1), 125),
            (8, 3, 2, 3, (2, -1, 7), 243),
            (2, 3, 3, 4, (0, 0, 0, 1), 81),
            (2, 3, 1, 3, (0, 0, 1), 243)):
        losses, va = poly_schedule_losses(b, p, s, d, coeffs, Kmax)
        r = len(coeffs) - 1
        allowed = s * r + (r - 1) + va
        rows.append(((b, p, s, d, coeffs), dict(sorted(losses.items())), allowed))
        if s >= r:
            Jtop = max(losses)
            require(losses[Jtop] <= allowed, (b, p, s, d, coeffs, losses))
    return rows


# --------------------------------------------- factorial schedule (direct)

def factorial_losses(b, p, s, coeffs, Kmax, L=40):
    """Direct tuple enumeration on each plateau (no use of F_l)."""
    t = ordmod(b, p)
    a = vp(b ** t - 1, p)
    r = len(coeffs) - 1
    mod = p ** L
    order_L = t * p ** max(0, L - a)
    V = flog(Kmax, p)
    fact = [1]
    for i in range(1, Kmax + 2):
        fact.append(fact[-1] * i)
    n_of = [None] + [t * fact[i] for i in range(1, Kmax + 2)]
    unit = [None] + [pow(b, -(n_of[i] % order_L), mod) for i in range(1, Kmax + 2)]
    wt = [None] + [p ** (s * (V - vp(i, p))) for i in range(1, Kmax + 2)]
    out = {}
    for k in range(3, Kmax + 1):
        if r * n_of[k - 1] >= n_of[k] or (r + 1) * n_of[k] >= n_of[k + 1]:
            continue
        J = flog(k, p)
        for l in range(1, r + 1):
            n = l * n_of[k] + r * n_of[k - 1] + 1
            S = 0
            for j, c in enumerate(coeffs):
                if c == 0:
                    continue
                total = 0
                for tup in product(range(1, k + 1), repeat=j):
                    if sum(n_of[i] for i in tup) <= n:
                        term = 1
                        for i in tup:
                            term = term * wt[i] * unit[i] % mod
                        total += term
                S = (S + c * p ** (s * V * (r - j)) * total) % mod
            v = vp(S, p) if S else math.inf
            require(v < L, ('precision', k, l))
            depth = r * s * V - v
            out[(k, l)] = r * s * J - depth
    return out


def B_value(m, p, s):
    return sum((Fraction(1, p ** (s * vp(x, p))) for x in range(1, m)), Fraction(0)) \
        - m * Fraction((p - 1) * p ** s, p ** (s + 1) - 1)


def check_B_identity():
    cases = 0
    for p in (3, 5, 7):
        for s in (1, 2, 3):
            lam = Fraction((p - 1) * p ** s, p ** (s + 1) - 1)
            for m in range(1, 400):
                if m % p == 0:
                    continue
                B = B_value(m, p, s)
                require(-1 < B < 0, (p, s, m, B))
                # Identity sum_{a<=m} w(a) - m lam = sum_h delta_h {m/p^h}.
                # For p^h > m the fractional part is m/p^h; that tail is geometric
                # with ratio p^{-(s+1)}.
                rhs = Fraction(0)
                h = 1
                while p ** h <= m:
                    delta = Fraction(1, p ** (s * (h - 1))) - Fraction(1, p ** (s * h))
                    rhs += delta * (Fraction(m, p ** h) - m // p ** h)
                    h += 1
                delta = Fraction(1, p ** (s * (h - 1))) - Fraction(1, p ** (s * h))
                rhs += delta * Fraction(m, p ** h) / (1 - Fraction(1, p ** (s + 1)))
                require(B + 1 == rhs, (p, s, m))
                for r in range(1, 7):
                    for l in range(r + 1):
                        g = sum(math.comb(r, j) * B ** (r - j) for j in range(l + 1))
                        require(g != 0, (p, s, m, r, l))
                        cases += 1
    return cases


def check_padic_limit(b, p, s, L=30):
    """p^{sv} U_{k-1} -> B(m) in Q_p for the factorial schedule, k = m p^v.
    Both sides are multiplied by p^{sE}, E = max v_p(a) for a < m."""
    t = ordmod(b, p)
    a = vp(b ** t - 1, p)
    mod = p ** L
    reduced = p ** max(0, L - a)  # i! modulo this determines b^{t i!} mod p^L
    rows = []
    for m in (1, 2, 4, 5, 7):
        if m % p == 0:
            continue
        E = flog(m - 1, p) if m > 1 else 0
        B = B_value(m, p, s) * p ** (s * E)
        require(B.denominator % p != 0, (m, B))
        Bmod = B.numerator * pow(B.denominator, -1, mod) % mod
        for v in range(1, 6):
            k = m * p ** v
            if k > 2500:
                break
            total = 0
            f = 1
            for i in range(1, k):
                f = f * i % reduced
                e = s * (v + E - vp(i, p))
                require(e >= 0, (m, v, i))
                total += p ** e * pow(b, -t * f, mod)
            diff = (total - Bmod) % mod
            rows.append((m, v, vp(diff, p) if diff else L))
    return rows


# ------------------------------------------------------------- E3 products

def check_affine_product(N=2_000_000):
    """X = C(2,5,1,3), Y' = (5/9)Y + (4/9)2^{-2}: exact 5-pole at every event."""
    b, p, q = 2, 5, 3
    tp, tq = ordmod(b, p), ordmod(b, q)
    xs = []
    i = 1
    while tp * i ** 3 <= N:
        xs.append((tp * i ** 3, Fraction(1, p ** vp(i, p))))
        i += 1
    ys = []
    j = 1
    while tq * j ** 3 <= N:
        w = Fraction(1, q ** vp(j, q))
        ys.append((tq * j ** 3, w if j == 1 else Fraction(5, 9) * w))
        j += 1
    # Affine identity on truncations.
    Y = sum((Fraction(1, q ** vp(jj, q)) / b ** (tq * jj ** 3) for jj in range(1, 9)), Fraction(0))
    Yp = sum((w / b ** m for m, w in ys[:8]), Fraction(0))
    require(Yp == Fraction(5, 9) * Y + Fraction(4, 9) / b ** 2, 'affine identity')
    V = flog(len(xs), p)
    L = V + 8
    mod = p ** L
    events = defaultdict(int)
    for nx, wx in xs:
        for ny, wy in ys:
            n = nx + ny
            if n > N:
                break
            val = wx * wy * p ** V
            events[n] = (events[n] + val.numerator * pow(val.denominator, -1, mod)
                         * pow(b, -n, mod)) % mod
    S = 0
    checked = 0
    m1 = ys[0][0]
    for n in sorted(events):
        S = (S + events[n]) % mod
        K = sum(1 for nx, _ in xs if nx <= n - m1)
        if K == 0:
            continue
        depth = V - vp(S, p)
        require(depth == flog(K, p), (n, K, depth))
        checked += 1
    return checked


def check_increasing_depth_product(N=4_000_000):
    """Primary weights 5^{-i} at 4*2^i; opposite positions chosen by the
    two-candidate unit test near j^3. Exact depth K at every event."""
    b, p, q = 2, 5, 3
    tp, tq = ordmod(b, p), ordmod(b, q)
    xs = []
    i = 1
    while tp * 2 ** i <= N:
        xs.append((tp * 2 ** i, Fraction(1, p ** i)))
        i += 1
    ys = []
    residue = 0  # unshifted opposite-axis prefix modulo p (it is p-integral)
    j = 1
    skips = 0
    while True:
        w = Fraction(1, q ** vp(j, q))
        wmod = pow(w.denominator, -1, p)
        lower = max(j ** 3, ys[-1][0] + 1 if ys else 1)
        m = -(-lower // tq) * tq
        cand = (residue + wmod * pow(b, -m, p)) % p
        if cand == 0:
            m += tq
            skips += 1
            cand = (residue + wmod * pow(b, -m, p)) % p
        if m > N:
            break
        require(cand != 0, ('unit', j))
        residue = cand
        ys.append((m, w))
        j += 1
    V = len(xs)
    L = V + 8
    mod = p ** L
    events = defaultdict(int)
    for nx, wx in xs:
        for ny, wy in ys:
            n = nx + ny
            if n > N:
                break
            val = wx * wy * p ** V
            events[n] = (events[n] + val.numerator * pow(val.denominator, -1, mod)
                         * pow(b, -n, mod)) % mod
    S = 0
    checked = 0
    m1 = ys[0][0]
    for n in sorted(events):
        S = (S + events[n]) % mod
        K = sum(1 for nx, _ in xs if nx <= n - m1)
        if K == 0:
            continue
        require(V - vp(S, p) == K, (n, K))
        checked += 1
    return checked, skips


# ------------------------------------------------ flagship square certificate

def failure_bound(failed, lam, scale):
    """1 - rho for failed cells given on an integer grid of mesh 1/scale on [1, lam)."""
    width = sum(r - l for l, r in failed)
    prev = Fraction(width, lam - 1)
    best = prev / scale
    acc = 0
    for l, r in sorted(failed):
        acc += r - l
        best = max(best, (prev + acc) / r)
    return best


def brute_square(p, d, s, layers):
    lam = p ** d
    h_star = layers - 1
    G = p ** (d * h_star)
    top = lam * G
    events = defaultdict(int)
    for h1 in range(h_star + 1):
        for h2 in range(h_star + 1 - h1):
            weight = p ** (s * (h1 + h2))
            c2 = p ** (d * (h_star - h2))
            for a in range(1, p ** (h1 + 1)):
                if a % p == 0:
                    continue
                A = a ** d * p ** (d * (h_star - h1))
                if A + c2 >= top:
                    break
                for c in range(1, p ** (h2 + 1)):
                    if c % p == 0:
                        continue
                    x = A + c ** d * c2
                    if x >= top:
                        break
                    events[max(x, G)] += weight
    mod = p ** (s * layers)
    points = sorted(set(events) | {G, top})
    M = 0
    failed = []
    for l, r in zip(points, points[1:]):
        M += events.get(l, 0)
        if M % mod == 0:
            if failed and failed[-1][1] == l:
                failed[-1] = (failed[-1][0], r)
            else:
                failed.append((l, r))
    return failed, failure_bound(failed, lam, G)


def adaptive_square(p, d, s, layers):
    """Own refinement: ordered loss pairs, integer roots, exact masses."""
    lam = p ** d
    cells = [(1, lam, 0)]
    history = []
    for j in range(layers):
        if j:
            cells = [(l * lam, r * lam, M) for l, r, M in cells]
        weight = p ** (s * j)
        mod = p ** (s * (j + 1))
        new = []
        for l, r, M in cells:
            jumps = Counter()
            base = M
            for h1 in range(j + 1):
                h2 = j - h1
                # Ordered pair (h1, h2): enumerate the coordinate of smaller loss
                # and solve for the other by exact integer roots. Both orders
                # are enumerated separately (no multiplicity shortcut).
                hi, ho = min(h1, h2), max(h1, h2)
                step = p ** (d * (j - ho))
                for a in range(1, p ** (hi + 1)):
                    if a % p == 0:
                        continue
                    A = a ** d * p ** (d * (j - hi))
                    if A + step >= r:
                        break
                    below = iroot(max(0, l - A) // step, d)
                    base += weight * (below - below // p)
                    upto = iroot((r - 1 - A) // step, d)
                    for c in range(below + 1, upto + 1):
                        if c % p:
                            jumps[A + c ** d * step] += weight
            cur, mass = l, base
            for x in sorted(jumps):
                if mass % mod == 0:
                    new.append((cur, x, mass))
                cur, mass = x, mass + jumps[x]
            if mass % mod == 0:
                new.append((cur, r, mass))
        cells = new
        history.append(len(cells))
        if not cells:
            break
    scale = lam ** (len(history) - 1)
    return history, failure_bound([(l, r) for l, r, _ in cells], lam, scale)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--layers', type=int, default=14)
    parser.add_argument('--skip-slow', action='store_true')
    args = parser.parse_args()

    print('principal denominators:', check_principal_denominators())
    cases, ratio = check_subgroups_and_periods()
    print(f'subgroup/period cases: {cases}; max fragment error / (sqrt q log^2 2q) = {ratio:.3f}')
    cases, worst = check_gauss_sums()
    print(f'Gauss sums checked: {cases}; max |tau|/sqrt(q gcd) = {worst:.6f}')
    print('lifting-the-exponent cases:', check_lte())
    for row in check_first_layer_counts().items():
        print('first-layer counts (p,d,r) -> (cells, max C_H, p^r):', row)
    print('B(m) identity and truncated-binomial nonvanishing:', check_B_identity())
    for b, p, s in ((2, 3, 1), (2, 3, 2), (2, 5, 1)):
        print(f'p-adic limit agreement digits (m, v, digits) for b={b}, p={p}, s={s}:',
              check_padic_limit(b, p, s))
    for spec, losses, allowed in check_polynomial_schedule_normality():
        print('poly schedule', spec, 'max loss per shell', losses, 'allowed', allowed)
    for b, p, s, coeffs, Kmax in ((2, 3, 1, (0, 0, 1), 90), (2, 3, 2, (3, 0, 1), 90),
                                  (2, 3, 1, (0, 1, 0, 3), 30), (2, 5, 1, (0, 0, 2), 60)):
        out = factorial_losses(b, p, s, coeffs, Kmax)
        print(f'factorial b={b} p={p} s={s} P={coeffs}: max loss {max(out.values())}, '
              f'min loss {min(out.values())}, '
              f'losses at k=p^2,2p^2,p^3: '
              f'{[out.get((k, l)) for k in (p * p, 2 * p * p, p ** 3) for l in range(1, len(coeffs))]}')
    print('affine product exact poles:', check_affine_product())
    print('increasing-depth product exact poles (events, skips):', check_increasing_depth_product())
    for layers in range(1, 10 if not args.skip_slow else 7):
        bf, bbound = brute_square(3, 3, 1, layers)
        hist, abound = adaptive_square(3, 3, 1, layers)
        require(bbound == abound, (layers, bbound, abound))
        print(f'square layers {layers}: brute = adaptive = {abound} ~ {float(abound):.3e}; '
              f'failed runs {len(bf)}; history {hist}')
    hist, bound = adaptive_square(3, 3, 1, args.layers)
    print(f'square layers {args.layers}: {bound} ~ {float(bound):.4e}; history {hist}')
    for N, D, scaled in flagship_discrepancies():
        print(f'flagship N={N}: D_N ~ {D:.6f}, N^(1/3) D_N ~ {scaled:.3f}')


if __name__ == '__main__':
    main()
