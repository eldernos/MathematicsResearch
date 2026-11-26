"""Exact controls for Phase 22 Track C3-C4 (short orbits and irrationality exponents).

Run from the repository root:  python -B scripts/phase22_short_orbits.py

C3  Short orbits on growing moduli.
    * Lemma A ingredients: lifting the exponent, exact vanishing of complete principal-unit
      orbit sums, the stride van der Corput inequality, the differenced-phase identity,
      and the sharpness example (no cancellation when v_p(G-1) is comparable to log M).
    * Corollary B on actual Theorem H prefixes of W^2 (b = 2, p = 3, s = 2, r = 2,
      d = 3, 4, 5, 6, the old gap r+1 <= d <= r(s+1)): reduced denominators q = 3^e Q,
      T_Q = ord_Q(2), the identities v_3(2^L - 1) = v_3(2^(t T_Q) - 1) = a_0 + v_3(T_Q)
      with L = lcm(t, T_Q), and the exact CRT factorization of the orbit sum.
    * The exponent budget theta, n_theta, delta for the gap range.
C4  Irrationality exponents and geometric schedules.
    * Base-(r+1) weights: distinct r-fold sums (true) against the size of the resulting
      denominators (fatal for the digit half).
    * Theorem G (linear weights e_k = k, n_k = t*lam^k, p > (r+1)!): lexicographic
      initial segments, the candidate formula for the top weight, the tied multiplicity
      bound (r+1)!, and the exact p-adic valuation of every polynomial prefix at every
      insertion position of [n_K, n_{K+1}) for r = 1, 2, 3; the cancellation at p = 3.
    * Exact denominators of U_k, the exponent ratio log|W - U_k| / log den(U_k), and the
      continued-fraction convergents of W for r = 1, lam = 3 (finite evidence for mu = 3).
    * Theorem S: on the Stoneham schedule b^(-3^k) with auxiliary units u = l mod 3^j, the
      3-adic depth defect d k - v_3(q_n) of W^d stays bounded (at most 12) for d = 2..5 at
      every insertion position, as for the Stoneham number alpha_(2,3); with dense auxiliary
      primes inside the active window, p^(dk) R_d agrees with alpha_(2,3) modulo 3^l exactly.
    * The measure functions of the Phase 21 schedules (ratio -> 1) and the cost of
      introducing a new prime at every index of a geometric schedule.

All assertions use exact integers or Fractions; floating point appears only in printed
summaries and in the numerical exponential-sum comparisons (tolerance 1e-8).
"""

from cmath import exp as cexp
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import ceil, exp, factorial, gcd, lcm, log, log2, pi
import random

random.seed(22)
TAU = 2 * pi

# ---------------------------------------------------------------- arithmetic helpers


def val(n, p):
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
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n + 1) if sieve[i]]


def order_prime_power(b, l, k):
    """Multiplicative order of b modulo l^k (gcd(b, l) = 1)."""
    m = l ** k
    o = l - 1 if l > 2 else 1
    for q in (factor(o) if o > 1 else {}):
        while o % q == 0 and pow(b, o // q, l) == 1:
            o //= q
    while pow(b, o, m) != 1:
        o *= l
    return o


def order(b, m):
    if m == 1:
        return 1
    return lcm(*[order_prime_power(b, l, k) for l, k in factor(m).items()])


def blog2(x):
    """log2 of a positive integer, accurate for very large integers."""
    bl = x.bit_length()
    if bl <= 60:
        return log2(x)
    return log2(x >> (bl - 60)) + (bl - 60)


def e_phase(x):
    """e(x) for a Fraction x."""
    return cexp(1j * TAU * float(x - (x.numerator // x.denominator)))


# ======================================================================== C3: Lemma A


def lemma_a_ingredients():
    print("C3. Lemma A ingredients")
    # 1. LTE: v_p(G^n - 1) = A + v_p(n) for G = 1 mod p, p odd.
    checks = 0
    for p in (3, 5, 7, 11):
        for _ in range(40):
            A = random.randint(1, 4)
            G = 1 + p ** A * random.choice([u for u in range(1, 50) if u % p])
            for n in range(1, 200):
                assert val(pow(G, n) - 1, p) == A + val(n, p)
                checks += 1
    print(f"  LTE v_p(G^n - 1) = A + v_p(n): {checks} cases")

    # 2. Complete principal-unit orbits are all of 1 + p^A Z / p^e and sum to zero.
    cases = 0
    for p in (3, 5, 7):
        for A in (1, 2, 3):
            for e in range(A + 1, A + 6):
                if p ** e > 200000:
                    continue
                G = 1 + p ** A * random.choice([u for u in range(1, 30) if u % p])
                mod = p ** e
                period = p ** (e - A)
                orbit, x = set(), 1
                for _ in range(period):
                    orbit.add(x)
                    x = x * G % mod
                assert x == 1 and orbit == {1 + p ** A * z for z in range(period)}
                for c in (1, 2, p + 1):
                    s = sum(cexp(1j * TAU * (c * y % mod) / mod) for y in orbit)
                    assert abs(s) < 1e-8 * period
                cases += 1
    print(f"  complete orbits = 1 + p^A Z/p^e and complete sums vanish: {cases} cases")

    # 3. Stride van der Corput inequality and the differenced-phase identity.
    p, e, A, G = 3, 14, 1, 4  # G = b^t for b = 2, t = 2, a_0 = 1
    mod = p ** e
    for (c, M, k, H) in [(1, 2000, 2, 12), (5, 3000, 3, 9), (7, 4000, 1, 20)]:
        a = [cexp(1j * TAU * (c * pow(G, m, mod) % mod) / mod) for m in range(M)]
        w = p ** k
        S = abs(sum(a))
        rhs_inner = M
        for h in range(1, H):
            Ch = sum(a[m + h * w] * a[m].conjugate() for m in range(M - h * w))
            rhs_inner += 2 * abs(Ch)
            # differenced phase: c(G^{m+hw} - G^m) = c_h G^m p^{A+k+j} with p | c_h false
            j = val(h, p)
            num = pow(G, h * w) - 1
            assert val(num, p) == A + k + j
            ch = c * num // p ** (A + k + j)
            assert ch % p
            for m in (0, 1, 17, M // 2):
                lhs = c * (pow(G, m + h * w, mod) - pow(G, m, mod)) % mod
                rhs = ch * pow(G, m, mod) * p ** (A + k + j) % mod
                assert lhs == rhs
        assert S * S <= (M + (H - 1) * w) / H * rhs_inner + 1e-6
    print("  stride van der Corput inequality and differenced phases: 3 instances")

    # 4. Sharpness: A = e/2 and M = p^A/10 gives no cancellation.
    for p, a in ((3, 6), (5, 4), (7, 3)):
        e, G, mod = 2 * a, 1 + p ** a, p ** (2 * a)
        M = p ** a // 10
        S = sum(cexp(1j * TAU * pow(G, m, mod) / mod) for m in range(M))
        assert abs(S) / M > 0.98
    print("  sharpness: v_p(G-1) = e/2, M = p^(e/2)/10 gives |S|/M > 0.98 (3 cases)")

    # 5. Evidence only: a long orbit of length p^(theta e).
    p, e, G = 3, 30, 4
    mod = p ** e
    M = 3 ** 10
    x, S = 1, 0j
    for _ in range(M):
        S += cexp(1j * TAU * x / mod)
        x = x * G % mod
    print(f"  evidence: |sum_(m<3^10) e(4^m/3^30)|/3^10 = {abs(S) / M:.4f}")


def lemma_a_budget():
    print("C3. Exponent budget in the gap r+1 <= d <= r(s+1)")
    print("   r  s  d  run exp 1-r/d  p-depth rs/d  theta     n_theta  delta")
    for r, s in ((2, 1), (2, 2), (3, 1), (3, 2)):
        for d in range(r + 1, r * (s + 1) + 1):
            eps1 = Fraction(1, 6 * d)
            theta = (d - r - 3 * d * eps1) / (r * s)
            assert theta > 0
            n_theta = ceil(2 / theta) + 1
            print(f"   {r}  {s}  {d}  {1 - r / d:.3f}        {r * s / d:.3f}       "
                  f"{float(theta):.4f}   {n_theta:3d}     2^-{n_theta + 2}")


# ====================================================================== C3: Theorem H


def theorem_h_prefixes():
    print("C3. Corollary B on Theorem H prefixes of W^2 (b=2, p=3, s=2)")
    b, p, s, t, a0 = 2, 3, 2, 2, 1
    assert order(b, p) == t and val(b ** t - 1, p) == a0
    aux = {2: 7, 4: 19, 5: 73, 7: 37, 8: 5}  # ord_l(2): 3, 18, 9, 36, 4 ; p does not divide k
    assert all(k % p for k in aux)
    def coef(k):
        return Fraction(1, p ** (s * val(k, p)) * aux.get(k, 1))
    total_pairs = 0
    for d in (3, 4, 5, 6):
        K = 16
        pos = {k: t * k ** d for k in range(1, K + 1)}
        tested = 0
        lte_cases = set()
        for n in sorted({pos[i] + pos[j] for i in range(1, K + 1) for j in range(1, K + 1)}):
            if n < pos[9] or n > pos[K]:
                continue
            if random.random() > 0.15:
                continue
            # exact shifted prefix of W^2 at n (all ordered pairs present)
            R = Fraction(0)
            for i in range(1, K + 1):
                for j in range(1, K + 1):
                    if pos[i] + pos[j] <= n:
                        c = coef(i) * coef(j)
                        R += Fraction(pow(b, n - pos[i] - pos[j], c.denominator) * c.numerator, c.denominator)
            R -= R.numerator // R.denominator
            q = R.denominator
            e = val(q, p)
            Q = q // p ** e
            # Q divides Lambda_K^2 (squares of the auxiliary primes present)
            Lam = 1
            for k, l in aux.items():
                if pos[k] <= n:
                    Lam *= l
            assert (Lam * Lam) % Q == 0
            TQ = order(b, Q)
            L = lcm(t, TQ)
            big = p ** 60
            assert val(pow(b, L, big) - 1, p) == a0 + val(TQ, p)
            assert val(pow(b, t * TQ, big) - 1, p) == a0 + val(TQ, p)
            lte_cases.add(val(TQ, p))
            # exact CRT splitting of sum_{j<T} e(b^j y) for y = h R
            for h in (1, 2, 3):
                y = h * R
                y -= y.numerator // y.denominator
                if y == 0:
                    continue
                qq = y.denominator
                ee = val(qq, p)
                QQ = qq // p ** ee
                a = y.numerator
                pe = p ** ee
                a1 = a * pow(QQ, -1, pe) % pe if ee else 0
                a2 = a * pow(pe, -1, QQ) % QQ if QQ > 1 else 0
                assert (Fraction(a1, pe) + Fraction(a2, QQ) - y).denominator == 1
                T = 1500
                direct = sum(e_phase(Fraction(pow(b, j, qq) * a % qq, qq)) for j in range(T))
                LL = lcm(t, order(b, QQ))
                G = pow(b, LL, pe) if ee else 1
                split = 0j
                for j0 in range(min(LL, T)):
                    Mj = (T - 1 - j0) // LL + 1
                    outer = e_phase(Fraction(pow(b, j0, QQ) * a2 % QQ, QQ)) if QQ > 1 else 1
                    inner, g = 0j, 1
                    cc = pow(b, j0, pe) * a1 % pe if ee else 0
                    for m in range(Mj):
                        inner += e_phase(Fraction(cc * g % pe, pe)) if ee else 1
                        g = g * G % pe if ee else 1
                    split += outer * inner
                assert abs(direct - split) < 1e-8 * T
            tested += 1
        total_pairs += tested
        print(f"  d={d}: {tested} shifts in shells K in [9,16]; v_3(T_Q) values seen {sorted(lte_cases)}; "
              f"run exponent 1-r/d = {1 - 2 / d:.3f} vs depth exponent rs/d = {2 * s / d:.3f}")
    assert total_pairs > 20
    # LTE identity on every divisor Q of prod l^2 over the auxiliary primes
    base = 1
    for l in aux.values():
        base *= l * l
    seen, ndiv = set(), 0
    for Q in range(1, base + 1) if base < 10 ** 5 else divisors(base):
        if base % Q:
            continue
        TQ = order(b, Q)
        v = val(TQ, p) if TQ > 1 else 0
        L = lcm(t, TQ)
        assert val(pow(b, L, p ** 60) - 1, p) == a0 + v == val(pow(b, t * TQ, p ** 60) - 1, p)
        seen.add(v)
        ndiv += 1
    print(f"  LTE v_3(2^L - 1) = v_3(2^(2 T_Q) - 1) = 1 + v_3(T_Q) on all {ndiv} divisors Q of "
          f"prod l^2; v_3(T_Q) takes the values {sorted(seen)}")


# ================================================================ C4: base-(r+1) weights


def base_r1_weights():
    print("C4. Base-(r+1) weights e_k = (r+1)^k")
    for r in (2, 3):
        K = 12
        for size in range(1, r + 1):
            sums = {}
            for M in combinations_with_replacement(range(1, K + 1), size):
                w = sum((r + 1) ** k for k in M)
                assert w not in sums
                sums[w] = M
        # linear weights tie
        lin = {}
        ties = 0
        for M in combinations_with_replacement(range(1, K + 1), r):
            lin.setdefault(sum(M), []).append(M)
        ties = sum(1 for v in lin.values() if len(v) > 1)
        lam = r + 2
        print(f"  r={r}: all multisets of size <= {r} from 1..{K} have distinct weights; "
              f"linear weights: {ties} tied sums")
        for Kk in (5, 10, 20):
            depth_bits = r * (r + 1) ** Kk * log(3, 2)
            run_bits = Kk * log(lam, 2)
            print(f"    K={Kk}: log2 of p^(r e_K) = {depth_bits:.3g}, log2 of run length lam^K = {run_bits:.3g}")


# ======================================================================= C4: Theorem G


def make_instance(r, p, b, lam, aux):
    t = order(b, p)
    def n(k):
        return t * lam ** k
    u, mu = {}, {}
    for k, l in aux.items():
        x = 1
        while not (x % p == l % p and gcd(x, b * l) == 1):
            x += 1
        u[k], mu[k] = x, l
    return t, n, u, mu


def theorem_g_valuations(r, p, b, lam, aux, Kmin, Kmax, poly):
    t, n, u, mu = make_instance(r, p, b, lam, aux)
    assert lam > r and p % b and b % p
    multi_cap = factorial(r + 1)
    def unit(k, mod):
        return u.get(k, 1) * pow(mu.get(k, 1), -1, mod) % mod
    checked = 0
    exact = 0
    for K in range(Kmin, Kmax + 1):
        lo, hi = n(K), n(K + 1)
        idx = [k for k in range(1, K + 1)]
        allsorted = {a: list(combinations_with_replacement(range(K, 0, -1), a)) for a in range(1, r + 1)}
        # all sorted tuples (descending) of every degree; positions
        positions = {lo}
        for a in range(1, r + 1):
            for M in allsorted[a]:
                x = sum(n(k) for k in M)
                if lo <= x < hi:
                    positions.add(x)
        # distinct degree-r multisets have distinct positions
        posr = [sum(n(k) for k in M) for M in allsorted[r]]
        assert len(set(posr)) == len(posr)
        for X in sorted(positions):
            present = [M for M in allsorted[r] if sum(n(k) for k in M) <= X]
            g = max(present)  # lexicographic max of descending tuples
            assert set(present) == {M for M in allsorted[r] if M <= g}
            wstar = max(sum(M) for M in present)
            cands = [g] + [tuple(list(g[:a]) + [g[a] - 1] * (r - a)) for a in range(r) if g[a] >= 2]
            assert wstar == max(sum(M) for M in cands)
            assert r * (K - 1) <= wstar <= r * K
            tops = [M for M in present if sum(M) == wstar]
            assert all(M in cands for M in tops)
            mult = sum(factorial(r) // prodfact(M) for M in tops)
            assert 1 <= mult <= multi_cap
            # exact valuation of the full prefix sum_a A_a S_a(X), scaled by p^Wmax
            prec = 6
            Wmax = wstar
            for a in range(1, r):
                for M in allsorted[a]:
                    if sum(n(k) for k in M) <= X:
                        Wmax = max(Wmax, sum(M))
            mod = p ** (Wmax + prec)
            total = poly[0] * pow(b, X, mod) * p ** Wmax % mod
            for a in range(1, r + 1):
                if poly[a] == 0:
                    continue
                for M in allsorted[a]:
                    x = sum(n(k) for k in M)
                    if x > X:
                        continue
                    term = factorial(a) // prodfact(M)
                    for k in M:
                        term = term * unit(k, mod) % mod
                    term = term * pow(b, X - x, mod) * p ** (Wmax - sum(M)) % mod
                    total = (total + poly[a] * term) % mod
            assert total != 0
            v = val(total, p) - Wmax
            if p > multi_cap:
                assert v == -wstar + val(poly[r], p), (K, X, v, wstar)
                exact += 1
            checked += 1
    return checked, exact


def divisors(n):
    out = [1]
    for l, k in factor(n).items():
        out = [d * l ** i for d in out for i in range(k + 1)]
    return sorted(out)


def prodfact(M):
    out = 1
    for k in set(M):
        out *= factorial(M.count(k))
    return out


def theorem_g_checks():
    print("C4. Theorem G: exact p-adic depth at every insertion position")
    runs = [
        (1, 3, 2, 3, {2: 5, 4: 7, 6: 11}, 2, 12, (1, 4)),
        (2, 7, 2, 3, {3: 3, 5: 5, 7: 11}, 3, 9, (3, 2, 5)),
        (3, 29, 2, 4, {3: 3, 5: 5}, 5, 7, (1, 0, 3, 29)),
    ]
    for r, p, b, lam, aux, Kmin, Kmax, poly in runs:
        assert p > factorial(r + 1) and lam > r
        checked, exact = theorem_g_valuations(r, p, b, lam, aux, Kmin, Kmax, poly)
        print(f"  r={r}, p={p}, b={b}, lam={lam}: {checked} positions in shells K={Kmin}..{Kmax}; "
              f"v_p(prefix) = -w* + v_p(A_r) at all {exact}")
    # cancellation when p <= (r+1)!: r = 2, p = 3, tie (K-1,K-1) & (K,K-2) with count 1 + 2 = 3
    r, p, b, lam = 2, 3, 2, 3
    t, n, u, mu = make_instance(r, p, b, lam, {})
    K = 8
    X = n(K) + n(K - 2)
    present = [M for M in combinations_with_replacement(range(K, 0, -1), 2) if n(M[0]) + n(M[1]) <= X]
    wstar = max(sum(M) for M in present)
    tops = sorted(M for M in present if sum(M) == wstar)
    assert tops == [(K - 1, K - 1), (K, K - 2)]
    mod = p ** (wstar + 8)
    total = 0
    for M in present:
        total += (factorial(2) // prodfact(M)) * pow(b, X - n(M[0]) - n(M[1]), mod) * p ** (wstar - sum(M))
    total %= mod
    v = val(total, p) - wstar
    assert v > -wstar
    print(f"  p=3 <= 3!: at X = n_8 + n_6 the tied tops (7,7),(8,6) have count 3 and "
          f"v_3(S_2) = {v} > -w* = {-wstar} (the pole cancels by {v + wstar})")


def theorem_g_irrationality():
    print("C4. Theorem G: exact denominators and the exponent of U_k")
    insts = [
        (1, 3, 2, 3, {2: 5, 4: 7, 6: 11}, 8),
        (2, 7, 2, 3, {3: 3, 5: 5, 7: 11}, 7),
        (3, 29, 2, 4, {3: 3, 5: 5}, 5),
    ]
    for r, p, b, lam, aux, kmax in insts:
        t, n, u, mu = make_instance(r, p, b, lam, aux)
        mu_all = lambda k: mu.get(k, 1)
        U = Fraction(0)
        line = []
        for k in range(1, kmax + 1):
            U += Fraction(u.get(k, 1), p ** k * mu_all(k) * b ** n(k))
            Lam = 1
            for kk, l in aux.items():
                if kk <= k:
                    Lam *= l
            assert U.denominator == p ** k * Lam * b ** n(k)
            if k >= 2:
                c_next = Fraction(u.get(k + 1, 1), p ** (k + 1) * mu_all(k + 1))
                logden = log(U.denominator)
                hi = (n(k + 1) * log(b) - log(c_next)) / logden
                lo = (n(k + 1) * log(b) - log(2 * c_next)) / logden
                line.append(f"{lo:.4f}..{hi:.4f}")
        bound = max(lam, (2 * lam - 1) / (lam - 1))
        print(f"  r={r}, lam={lam}: den(U_k) = p^k Lambda_k b^(n_k) exactly; "
              f"-log|W-U_k|/log den(U_k) for k=2..{kmax}: {', '.join(line)}  (mu = {bound})")


def convergent_check():
    print("C4. Continued fraction of W (r=1, b=2, p=3, lam=3): exponents of convergents")
    r, p, b, lam, aux = 1, 3, 2, 3, {2: 5, 4: 7, 6: 11}
    t, n, u, mu = make_instance(r, p, b, lam, aux)
    proxy = Fraction(0)
    Uk = {}
    for k in range(1, 9):
        proxy += Fraction(u.get(k, 1), p ** k * mu.get(k, 1) * b ** n(k))
        Uk[k] = proxy
    # proxy = U_8; |W - U_8| < 2^(1 - n_9)
    A, B = proxy.numerator, proxy.denominator
    qlimit = Uk[7].denominator * 2
    h0, h1, k0, k1 = 0, 1, 1, 0
    x, y = A, B
    worst = (0.0, None)
    hits = set()
    steps = 0
    counted = 0
    while y:
        a = x // y
        x, y = y, x - a * y
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        steps += 1
        if k1 > qlimit:
            break
        if k1 < 2 ** 30:
            continue
        counted += 1
        diff = abs(A * k1 - h1 * B)
        # log2 |U_8 - h/k| = log2 diff - log2 B - log2 k ; the proxy error is negligible here
        lg = blog2(diff) - blog2(B) - blog2(k1)
        expo = -lg / blog2(k1)
        for k, V in Uk.items():
            if V == Fraction(h1, k1):
                hits.add(k)
        if expo > worst[0]:
            worst = (expo, k1.bit_length())
    assert hits >= {4, 5, 6, 7}
    assert worst[0] < 3.05
    print(f"  {counted} convergents with 2^30 <= q <= 2 den(U_7) (from {steps} partial quotients computed); "
          f"U_4..U_7 are among them; largest exponent: {worst[0]:.4f} (q of {worst[1]} bits)")


def measure_functions():
    print("C4. Ratio-to-one schedules: rho_k = n_k/(n_k - n_(k-1)) governs the separation bound")
    t, d = 2, 5
    for k in (10, 100, 1000, 10000):
        nH_k, nH_km = t * k ** d, t * (k - 1) ** d
        rhoH = nH_k / (nH_k - nH_km)
        # quasi-polynomial in logarithmic form
        logn = lambda i: log(t * i) + log(i + 1) ** 2
        rhoU = 1 / (1 - exp(logn(k - 1) - logn(k)))
        logQ_H = (nH_k - nH_km) * log(2)
        logQ_U = log(2) * exp(logn(k)) / rhoU
        print(f"  k={k}: Theorem H (d=5) rho={rhoH:.1f} at log Q ~ {logQ_H:.3g};  "
              f"Theorem U rho={rhoU:.1f} at log Q ~ {logQ_U:.3g}")
    print("  rho_k -> infinity in both, so separation gives only |W - A/Q| >= Q^(-psi(Q)), psi -> infinity")


def every_index_cost():
    print("C4. A new prime at every index of a geometric schedule")
    ps = [l for l in primes_upto(40000) if l not in (2, 3)]
    ords = 1
    logA = 0.0
    first = None
    table = []
    for k, l in enumerate(ps[:3000], 1):
        o = order(2, l)
        g = gcd(ords, o)
        ords = ords // g * o
        if k in (100, 300, 1000, 2000, 3000):
            logA = log(ords)
            table.append((k, logA, k * log(3)))
        if log(ords) <= k * log(3):
            first = k
    for k, la, kl in table:
        print(f"  k={k}: log lcm_(j<=k) ord_(l_j)(2) = {la:.0f} vs k log 3 = {kl:.0f}")
    print(f"  the lcm of orders exceeds 3^k for every k with {first} < k <= 3000")
    assert first is not None and first < 100
    # sparse introduction k_j = j * ceil((log log (j+16))^2) keeps the ratio below 1
    ords = 1
    worst = 0.0
    for j, l in enumerate(ps[:3000], 1):
        o = order(2, l)
        ords = ords // gcd(ords, o) * o
        kj = j * ceil(log(log(j + 16)) ** 2)
        worst = max(worst, log(ords) / (kj * log(3))) if j > 20 else worst
    print(f"  with k_j = j ceil((log log(j+16))^2): max ratio log lcm / (k_j log 3) over 20<j<=3000 = {worst:.3f}")
    assert worst < 1


def stoneham_all_prime():
    """Theorem S mechanism: W = sum u_k/(p^k mu_k) b^(-p^k) with u_(k_j) = l_j mod p^j.
    Compare the p-adic depth defect d*k - v_p(q_n) of W^d with that of the Stoneham
    number alpha_(b,p) at every insertion position of shells k, for d = 2..5."""
    print("C4. Theorem S: all-degree depth on the Stoneham schedule with auxiliary primes")
    p, b = 3, 2
    aux = {2: 5, 4: 7, 6: 11}  # j-th auxiliary prime at index 2j
    u = {}
    for j, (k, l) in enumerate(sorted(aux.items()), 1):
        x = 1
        while not (x % p ** j == l % p ** j and gcd(x, b * l) == 1):
            x += 1
        u[k] = x
        assert Fraction(x, p ** k * l) <= b  # bounded coefficients
    def defects(d, kmin, kmax, modified):
        rows = []
        for k in range(kmin, kmax + 1):
            lo, hi = p ** k, p ** (k + 1)
            ms = list(combinations_with_replacement(range(k, 0, -1), d))
            positions = sorted({lo} | {sum(p ** j for j in M) for M in ms if lo <= sum(p ** j for j in M) < hi})
            worst = 0
            for X in positions:
                prec = d * k + 4
                mod = p ** prec
                total = 0
                for M in ms:
                    x = sum(p ** j for j in M)
                    if x > X:
                        continue
                    term = factorial(d) // prodfact(M) * pow(b, X - x, mod) * p ** (d * k - sum(M))
                    if modified:
                        for j in M:
                            if j in aux:
                                term = term * u[j] * pow(aux[j], -1, mod)
                    total = (total + term) % mod
                assert total != 0
                worst = max(worst, val(total, p))
            rows.append(worst)
        return rows
    for d in (2, 3, 4, 5):
        kmax = {2: 10, 3: 9, 4: 8, 5: 8}[d]
        w_mod = defects(d, 3, kmax, True)
        w_st = defects(d, 3, kmax, False)
        assert max(w_mod + w_st) <= 12 and w_mod[-1] == w_st[-1]
        print(f"  d={d}: max defect d k - v_3(q_n) per shell k=3..{kmax}: modified {w_mod}; "
              f"alpha_(2,3) {w_st}")

    # Direct test of the congruence transfer: dense auxiliary primes l_J at k_J = J + 1
    # (J = 1..8), u_J = l_J mod 3^J.  For k >= 2l every auxiliary index in the window
    # [k-l+1, k] has J >= l, so p^(dk) R_d(n) must agree with alpha_(2,3) modulo 3^l.
    dense = {J + 1: l for J, l in enumerate([5, 7, 11, 13, 17, 19, 23, 29], 1)}
    ud = {}
    for k, l in dense.items():
        J = k - 1
        x = 1
        while not (x % p ** J == l % p ** J and gcd(x, b * l) == 1):
            x += 1
        ud[k] = x
        assert Fraction(x, p ** k * l) <= b
    for d, l, ks in ((2, 4, (8, 9, 10, 11)), (3, 5, (10, 11))):
        npos = 0
        active = set()
        for k in ks:
            assert k >= 2 * l
            lo, hi = p ** k, p ** (k + 1)
            ms = list(combinations_with_replacement(range(k, 0, -1), d))
            positions = sorted({lo} | {sum(p ** j for j in M) for M in ms if lo <= sum(p ** j for j in M) < hi})
            mod = p ** l
            for X in positions:
                tot_mod = tot_st = 0
                for M in ms:
                    x = sum(p ** j for j in M)
                    if x > X or d * k - sum(M) >= l:
                        continue
                    term = factorial(d) // prodfact(M) * pow(b, X - x, mod) * p ** (d * k - sum(M))
                    tot_st = (tot_st + term) % mod
                    for j in M:
                        if j in dense:
                            assert j - 1 >= l  # every auxiliary index in the window has J >= l
                            active.add(j)
                            term = term * ud[j] * pow(dense[j], -1, mod)
                    tot_mod = (tot_mod + term) % mod
                assert tot_mod == tot_st != 0
                npos += 1
        print(f"  congruence transfer, d={d}, l={l}: p^(dk) R_d = alpha_(2,3) mod 3^{l} and nonzero at all "
              f"{npos} positions of shells k={ks[0]}..{ks[-1]}; auxiliary indices active in the window: {sorted(active)}")


def main():
    lemma_a_ingredients()
    lemma_a_budget()
    theorem_h_prefixes()
    base_r1_weights()
    theorem_g_checks()
    theorem_g_irrationality()
    convergent_check()
    stoneham_all_prime()
    measure_functions()
    every_index_cost()
    print("All Phase 22 C3-C4 checks passed.")


if __name__ == "__main__":
    main()
