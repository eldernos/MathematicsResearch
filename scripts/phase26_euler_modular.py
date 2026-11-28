"""Exact finite checks for Phase 26 Track D (D1-D4). Run with python -B.

Every theorem-supporting assertion uses int and Fraction only.  Every displayed
lower bound is asserted as an exact rational inequality and printed by
downward truncation, never by round-to-nearest.  Lines tagged [finite] print
finite measurements, which are not asymptotic evidence.  The single block
tagged [exploration] uses floats and proves nothing.
"""

from fractions import Fraction as F
from math import gcd, isqrt, prod
import itertools

CHECKS = [0]


def check(cond, msg="check failed"):
    if not cond:
        raise AssertionError(msg)
    CHECKS[0] += 1


# ---------------------------------------------------------------- helpers

def factors(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(sieve[p * p::p]))
    return [i for i in range(n + 1) if sieve[i]]


def v2(n):
    return (n & -n).bit_length() - 1


def naf_weight(x):
    x = abs(x)
    count = 0
    while x:
        if x & 1:
            count += 1
            x -= 2 - (x & 3)
        x >>= 1
    return count


def transitions(bits_int, length):
    """Adjacent unequal pairs in the length-bit string of 0 <= bits_int."""
    return ((bits_int ^ (bits_int >> 1)) & ((1 << (length - 1)) - 1)).bit_count()


def atan_partial(d, last):
    return sum(F((-1) ** j, (2 * j + 1) * d ** (2 * j + 1)) for j in range(last + 1))


def pi_bounds():
    lo = 16 * atan_partial(5, 5) - 4 * atan_partial(239, 2)
    hi = 16 * atan_partial(5, 4) - 4 * atan_partial(239, 1)
    check(3 < lo < hi < F(31416, 10000))
    return lo, hi


def log2_bounds():
    # log 2 = 2 atanh(1/3) = 2 sum 1/((2j+1) 3^(2j+1)); positive terms.
    lo = 2 * sum(F(1, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(12))
    tail = F(2, 25 * 3 ** 25) * F(9, 8)  # geometric majorant of the tail
    hi = lo + tail
    check(F(6931, 10000) < lo < hi < F(6932, 10000))
    return lo, hi


def pentagonal_terms(limit):
    terms = [(0, 1)]
    j = 1
    while j * (3 * j - 1) // 2 <= limit:
        for n in (j * (3 * j - 1) // 2, j * (3 * j + 1) // 2):
            if n <= limit:
                terms.append((n, (-1) ** j))
        j += 1
    return terms


def euler_power(r, limit):
    """Coefficients of E(q)^r = prod (1-q^j)^r through q^limit (sparse products)."""
    terms = pentagonal_terms(limit)
    coeff = [1] + [0] * limit
    for _ in range(r):
        nxt = [0] * (limit + 1)
        for n, a in terms:
            for m in range(limit + 1 - n):
                if coeff[m]:
                    nxt[n + m] += a * coeff[m]
        coeff = nxt
    return coeff


# ------------------------------------------------- D1: Euler square E_2^2

def good_sign(p):
    for y in range(0, isqrt(p) + 1, 2):
        x = isqrt(p - y * y)
        if x * x + y * y == p:
            return 1 if y % 3 == 0 else -1
    raise AssertionError(p)


def cm_coefficient(index):
    value = 1
    for p, e in factors(index).items():
        if p % 12 == 1:
            value *= (e + 1) * good_sign(p) ** e
        elif p in (2, 3) or e % 2:
            return 0
        elif p % 4 == 1:
            value *= (-1) ** (e // 2)
    return value


def d1_constants():
    pi_lo, pi_hi = pi_bounds()
    # Theorem 1 of GF-43 and its exact decomposition.
    check(F(106103, 10 ** 6) < 1 / (3 * pi_hi) < 1 / (3 * pi_lo) < F(106104, 10 ** 6))
    # K = Gamma(7/4) Gamma(1/4) 4^(3/4) / 4.  With Gamma(7/4) = (3/4)Gamma(3/4),
    # Gamma(1/4)Gamma(3/4) = pi sqrt 2 and 4^(3/4) = 2 sqrt 2, K/pi is
    # (3/4) * (sqrt2 * 2 sqrt2) / 4 = (3/4) * 4 / 4.
    check(F(3, 4) * 4 / 4 == F(3, 4))
    # Transfer formula: bound = e^{g d} theta^d / (A Gamma(1/4)); for Selberg
    # A = 2^d e^{g d} Gamma(1+d), and Gamma(1+d)Gamma(1-d) = (3/4) pi sqrt 2.
    # bound = theta^(3/4) 2^(-3/4) 2^(-1/2) (4/3) / pi = (2 theta)^(3/4)/(3 pi):
    check(F(-3, 4) - F(1, 2) == F(3, 4) - 2)
    check(F(4, 3) * F(1, 4) == F(1, 3))
    # theta = 1/2 recovers 1/(3 pi): (2 * 1/2)^(3/4) = 1.
    # Conditional level theta -> 1 with Selberg weights: 2^(3/4)/(3 pi).
    r_lo, r_hi = F(16817, 10000), F(16818, 10000)
    check(r_lo ** 4 < 8 < r_hi ** 4)
    eh_lo, eh_hi = r_lo / (3 * pi_hi), r_hi / (3 * pi_lo)
    check(F(1784, 10000) < eh_lo < eh_hi < F(1785, 10000))
    # Optimisation identity: 1/(4K) - (t/2 - K t^2/4) = K (t - 1/K)^2 / 4.
    for K in (F(9, 4), F(2355, 1000), F(3, 1), F(7, 3)):
        for t in (F(0), F(1, 7), 1 / K, F(1, 2), F(2)):
            check(1 / (4 * K) - (t / 2 - K * t * t / 4) == K * (t - 1 / K) ** 2 / 4)
    print("Finite certificate: 106103/10^6 < 1/(3 pi) < 106104/10^6; "
          "Selberg level-1 value 2^(3/4)/(3 pi) in (0.1784, 0.1785).")


def d1_class_b():
    # Pointwise first-order inequality and its equality cases, exhaustively.
    n = 0
    for H in range(2, 13):
        for mask in range(1 << (H - 1)):
            om = [(mask >> (h - 1)) & 1 for h in range(1, H)]
            g = next((h for h in range(1, H) if om[h - 1]), H)
            rhs = H - sum((H - h) * om[h - 1] for h in range(1, H))
            check(min(g, H) >= rhs)
            if sum(om) <= 1:
                check(min(g, H) == rhs)
            # Layer-cake identity behind D2.3: min(g, H) = sum_{v<H} 1[g > v].
            check(min(g, H) == sum(1 for v in range(H) if not any(om[:v])))
            n += 1
    # Truncation is optimal among phi with phi(g) <= g, phi <= Phi:
    # value(phi) = Phi - sum_h u_h (Phi - phi(h)) with predecessor rates u_h.
    G = 5
    for u in (F(1, 10), F(1, 7), F(3, 20)):
        for Phi in range(1, G + 1):
            best = Phi - sum(u * (Phi - min(h, Phi)) for h in range(1, G + 1))
            for phi in itertools.product(*[range(0, min(h, Phi) + 1) for h in range(1, G + 1)]):
                val = Phi - sum(u * (Phi - phi[h - 1]) for h in range(1, G + 1))
                check(val <= best)
    print(f"Finite certificate: first-order inequality on {n} predecessor patterns; "
          "truncation optimal on all small test functions.")


def conv(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return out


def d1_sharpness_model():
    """Alternating model: sign-sigma gaps uniform on 1..Hs, sign -sigma gaps = L."""
    Hs, L = 60, 252
    Eg = F(Hs + 1, 2)
    K = (Eg + L) / (2 * Hs)              # so that K * rho = 1/Hs exactly
    rho = 2 / (Eg + L)
    check(K * rho == F(1, Hs))
    check(F(9, 4) < K)
    W_sigma = Eg / (Eg + L)              # W_sigma / N in the stationary model
    check(W_sigma == (1 / (4 * K)) * F(Hs + 1, Hs))
    uni = [0] + [1] * Hs                 # counts; scale Hs per uniform summand
    Hmax = 8 * L

    def chain(first_uniform):
        """Distances to earlier points: alternating uniform and L backward gaps."""
        out, cur, scale, shift = [], [1], 1, 0
        kinds = itertools.cycle(("U", "L") if first_uniform else ("L", "U"))
        while shift + min(i for i, x in enumerate(cur) if x) <= Hmax:
            if next(kinds) == "U":
                cur, scale = conv(cur, uni), scale * Hs
            else:
                shift += L
            out.append(([0] * shift + cur, scale))
        return out

    def tri(dlist, H):
        total = F(0)
        for pmf, sc in dlist:
            total += F(sum((H - d) * c for d, c in enumerate(pmf[:H]) if c), sc)
        return total

    def count(dlist, H):                 # expected number of earlier points within H
        return sum(F(sum(pmf[:H + 1]), sc) for pmf, sc in dlist)
    plus, minus = chain(True), chain(False)
    check(len(plus) >= 15 and len(minus) >= 15)
    check(K == F(113, 48))
    grid = list(range(1, 3 * Hs)) + list(range(3 * Hs, Hmax, 7)) + [Hmax]
    check(grid[-2] == 2014 and grid[-1] == Hmax == 2016)
    for H in grid:
        bound = F(H * (H - 1), 2 * Hs)
        check(tri(plus, H) <= bound and tri(minus, H) <= bound)
        if H <= Hs + 1:
            check(tri(plus, H) == bound)
        if H < L:
            check(tri(minus, H) == 0)
        check(count(plus, H) <= F(H, Hs) and count(minus, H) <= F(H, Hs))
    print(f"Finite certificate: sharpness model K={K} meets every triangular and uniform "
          f"predecessor bound for every H<{3 * Hs}, H={3 * Hs},{3 * Hs + 7},...,{grid[-2]} "
          f"and H={Hmax}; W_sigma/N = (1+1/{Hs})/(4K).")


def d1_warning_and_gram_models():
    # Model A: iid gaps in {1,3}, s=+1 iff gap 3.  Model B: same gaps, iid signs.
    gaps = (1, 3)
    Phi_A = (F(1, 2) * 3 - F(1, 2) * 1) / (F(1, 2) * 3 + F(1, 2) * 1)
    check(Phi_A == F(1, 2))
    # Stationary law of position mod q is uniform; joint law with the sign too.
    for q in range(2, 13):
        pi_vec = [F(1, q)] * q
        nxt = [F(0)] * q
        for a in range(q):
            for g in gaps:
                nxt[(a + g) % q] += pi_vec[a] / 2
        check(nxt == pi_vec)
        for a in range(q):
            plus = pi_vec[(a - 3) % q] / 2
            minus = pi_vec[(a - 1) % q] / 2
            check(plus == minus == F(1, 2 * q))
    sign = {1: -1, 3: 1}
    # Enumerate gap tuples (g_i, g_{i+1}, ..., g_{i+d}) for exact correlations.
    back_nonzero = 0
    back = {}
    for d in range(1, 7):
        for h in range(1, 3 * d + 1):
            fwd_pure = fwd_mixed = back_mixed = F(0)
            for tup in itertools.product(gaps, repeat=d + 1):
                w = F(1, 2 ** (d + 1))
                if sum(tup[1:]) != h:
                    continue
                si, sj = sign[tup[0]], sign[tup[-1]]
                fwd_pure += w * si * sj      # a(m_i) a(m_j), leftmost factor signed
                fwd_mixed += w * si          # a(m_i) 1_U(m_j)
                back_mixed += w * sj         # 1_U(m_i) a(m_j): predecessor type
            check(fwd_pure == 0 and fwd_mixed == 0)
            back_nonzero += back_mixed != 0
            back[d, h] = back_mixed
    check(back_nonzero > 0)
    # Repeated shifts are NOT covered by D2.1.  Point density 1/E[g] = 1/2; the
    # 2-point diagonal E[a(m)^2] = E[u(m)] = C(empty, {0}) is pure support (1/2
    # in both models), but E[a(m)^2 a(m+h)] = E[u(m) a(m+h)] = C({h}, {0}) is
    # predecessor type: density times the Palm sum over the number d of steps.
    density = 1 / (F(1, 2) * 1 + F(1, 2) * 3)
    check(density == F(1, 2))
    rep_A = {h: density * sum(back[d, h] for d in range(1, h + 1) if (d, h) in back)
             for h in range(1, 7)}
    rep_B = {}
    for h in range(1, 7):                # model B: the right sign is a fair coin
        tot = F(0)
        for d in range(1, h + 1):
            for tup in itertools.product(gaps, repeat=d + 1):
                if sum(tup[1:]) == h:
                    tot += sum(F(sj, 2 ** (d + 2)) for sj in (1, -1))
        rep_B[h] = density * tot
    check(rep_A[1] == F(-1, 4) and rep_B[1] == 0)
    check(all(v == 0 for v in rep_B.values()))
    # Three-point pure signed correlations vanish as well.
    for d, e in ((1, 1), (1, 2), (2, 1), (2, 3)):
        tot = {}
        for tup in itertools.product(gaps, repeat=d + e + 1):
            key = (sum(tup[1:d + 1]), sum(tup[d + 1:]))
            val = sign[tup[0]] * sign[tup[d]] * sign[tup[-1]]
            tot[key] = tot.get(key, F(0)) + F(val, 2 ** (d + e + 1))
        check(all(v == 0 for v in tot.values()))
    print("Finite certificate: warning model Phi=1/2 with uniform signed residues mod q<=12; "
          f"signed-leftmost correlations vanish, {back_nonzero} predecessor-type ones do not; "
          f"repeated shift E[a(m)^2 a(m+1)] = {rep_A[1]} (model A) vs {rep_B[1]} (model B).")


def d1_measurements(limit=6000):
    coeff = euler_power(2, limit)
    check(coeff[:2001] == [cm_coefficient(12 * n + 1) for n in range(2001)])
    sign = [(v > 0) - (v < 0) for v in coeff]
    ends = [i for i, v in enumerate(coeff) if v]
    pairs = list(zip(ends, ends[1:]))
    sp = sum(1 for b in ends[1:] if sign[b] > 0)
    sm = sum(1 for b in ends[1:] if sign[b] < 0)
    out = []
    for H in (1, 2, 4, 8, 16, 32):
        signed = sum(sign[b] * min(H, b - a) for a, b in pairs)
        unsigned = sum(min(H, b - a) for a, b in pairs)
        out.append(f"H={H}: {signed}/{unsigned}")
    # Identity behind Corollary D1.2: sum_b s(b) min(g,H) = H(S+ - S-) - sum s (H-g)_+.
    for H in (3, 9, 27):
        lhs = sum(sign[b] * min(H, b - a) for a, b in pairs)
        rhs = H * (sp - sm) - sum(sign[b] * max(0, H - (b - a)) for a, b in pairs)
        check(lhs == rhs)
    print(f"[finite] E_2^2 through {limit}: S+={sp}, S-={sm}, signed gap sum "
          f"{sum(sign[b] * (b - a) for a, b in pairs)}; signed/unsigned truncated sums: "
          + ", ".join(out))
    return coeff, sign, ends


def beta_sieve_exploration():
    """[exploration] floats: Rosser-Iwaniec beta-sieve constant in dimension kappa.

    Integral form of the delay-differential system, normalised to A = 1:
    F(s) = s^(-kappa) on (0, beta+1], f = 0 on (0, beta], and
    s^kappa f(s) = int_beta^s kappa t^(kappa-1) F(t-1) dt,
    s^kappa F(s) = (beta+1)^kappa F(beta+1) + int_(beta+1)^s kappa t^(kappa-1) f(t-1) dt.
    The grid s_i = beta + i/n1 is aligned with the unit delay, so every delayed
    value is a grid value and every kink of F, f is a grid point; the trapezoid
    rule is then second order.  beta solves F(inf) = f(inf) by bisection,
    A = 1/F(inf), and one Richardson step in the grid size removes the h^2 term.
    """
    import math

    def limits(kappa, beta, n1, umax=10):
        h = 1.0 / n1
        n = umax * n1 + 1
        s = [beta + i * h for i in range(n)]
        Fv, fv = [0.0] * n, [0.0] * n
        for i in range(n1 + 1):
            Fv[i] = s[i] ** (-kappa)

        def weight(i):
            return kappa * s[i] ** (kappa - 1)

        def F_delayed(i):                      # F(s_i - 1)
            return (s[i] - 1) ** (-kappa) if i <= 2 * n1 else Fv[i - n1]
        int_f, int_F = 0.0, (beta + 1) ** kappa * Fv[n1]
        prev = weight(0) * F_delayed(0)
        for i in range(1, n):
            cur = weight(i) * F_delayed(i)
            int_f += h / 2 * (prev + cur)
            prev = cur
            fv[i] = int_f / s[i] ** kappa
            if i > n1:
                int_F += h / 2 * (weight(i - 1) * fv[i - 1 - n1] + weight(i) * fv[i - n1])
                Fv[i] = int_F / s[i] ** kappa
        return Fv[-1], fv[-1]

    def solve(kappa, n1, lo, hi):
        F_lo, f_lo = limits(kappa, lo, n1)
        side = F_lo > f_lo
        for _ in range(40):
            mid = (lo + hi) / 2
            Fm, fm = limits(kappa, mid, n1)
            if (Fm > fm) == side:
                lo = mid
            else:
                hi = mid
        beta = (lo + hi) / 2
        return beta, 1 / limits(kappa, beta, n1)[0]

    gamma_e = 0.5772156649015329
    out = []
    for kappa, lo, hi in ((1.0, 1.8, 2.2), (0.75, 1.3, 1.5)):
        (b1, A1), (b2, A2) = solve(kappa, 250, lo, hi), solve(kappa, 500, lo, hi)
        beta, A = (4 * b2 - b1) / 3, (4 * A2 - A1) / 3
        sel = 2 ** kappa * math.exp(gamma_e * kappa) * math.gamma(1 + kappa)
        out.append(f"kappa={kappa}: beta~{beta:.4f}, A_beta~{A:.4f}, "
                   f"A_Selberg={sel:.4f}, ratio~{A / sel:.4f}")
        if kappa == 1.0:
            out.append(f"|beta_1-2|={abs(beta - 2):.0e}, |A_1-2e^gamma|="
                       f"{abs(A - 2 * math.exp(gamma_e)):.0e}")
    bound = sel / (3 * math.pi * A)
    out.append(f"implied conditional bound ~ {bound:.4f}; with level 1 ~ {2 ** 0.75 * bound:.4f}")
    print("[exploration, floats, proves nothing] " + "; ".join(out))


# ------------------------------------------- D2: positivity and Gram data

def is_psd(M):
    """Exact positive-semidefiniteness test for a symmetric rational matrix."""
    n = len(M)
    A = [[F(x) for x in row] for row in M]
    for k in range(n):
        piv = A[k][k]
        if piv < 0:
            return False
        if piv == 0:
            if any(A[k][j] != 0 for j in range(k + 1, n)):
                return False
            continue
        for i in range(k + 1, n):
            f = A[i][k] / piv
            for j in range(k, n):
                A[i][j] -= f * A[k][j]
    return True


def d2_checks(coeff, sign, ends):
    N = len(coeff) - 1
    a = sign
    u = [1 if c else 0 for c in coeff]
    lags = 12
    G = [[sum(a[m - i] * a[m - j] for m in range(lags, N + 1)) for j in range(lags)]
         for i in range(lags)]
    check(all(G[i][j] == G[j][i] for i in range(lags) for j in range(lags)))
    check(is_psd(G))
    neg = [-x for x in a]
    check(G == [[sum(neg[m - i] * neg[m - j] for m in range(lags, N + 1))
                 for j in range(lags)] for i in range(lags)])
    # Mixed Gram of (a(m), 1_U(m-1), ..., 1_U(m-8)): its first row holds the
    # backward (predecessor-type) correlations, which do see the gaps.
    vec = [[a[m]] + [u[m - h] for h in range(1, 9)] for m in range(9, N + 1)]
    Gm = [[sum(v[i] * v[j] for v in vec) for j in range(9)] for i in range(9)]
    check(is_psd(Gm))
    # Gm is NOT sign-flip invariant: under s -> -s it becomes J Gm J with
    # J = diag(-1, 1, ..., 1), so its mixed entries Gm[0][h] change sign.
    vec_neg = [[neg[m]] + [u[m - h] for h in range(1, 9)] for m in range(9, N + 1)]
    Gm_neg = [[sum(v[i] * v[j] for v in vec_neg) for j in range(9)] for i in range(9)]
    Jd = [-1] + [1] * 8
    check(Gm_neg == [[Jd[i] * Gm[i][j] * Jd[j] for j in range(9)] for i in range(9)])
    check(Gm_neg != Gm and all(Gm_neg[0][h] == -Gm[0][h] != 0 for h in range(1, 9)))
    check(is_psd(Gm_neg))
    back = [Gm[0][h] for h in range(1, 9)]
    fwd = [sum(a[m] * u[m + h] for m in range(1, N + 1 - h)) for h in range(1, 9)]
    # Collapse: Gram of v_i = s_i e_{min(g_i, 10)} equals the unsigned one.
    gaps = [(b, b - p) for p, b in zip(ends, ends[1:])]
    signed, unsigned = {}, {}
    for b, g in gaps:
        key = min(g, 10)
        signed[key] = signed.get(key, 0) + sign[b] * sign[b]
        unsigned[key] = unsigned.get(key, 0) + 1
    check(signed == unsigned)
    # Bordered Gram [[S, sum s g], [sum s g, sum g^2]]: the PSD bound is vacuous.
    S = len(gaps)
    sg = sum(sign[b] * g for b, g in gaps)
    g1 = sum(g for _, g in gaps)
    g2 = sum(g * g for _, g in gaps)
    check(is_psd([[S, sg], [sg, g2]]))
    check(S * g2 >= g1 * g1)            # so sqrt(S sum g^2) >= sum g
    # Any 2x2 Gram of (x_i, y_i) with x_i y_i = s_i g_i: sum x^2 sum y^2 >= (sum g)^2.
    # Family x_i = s_i g_i^e, y_i = g_i^(1-e); e = 0 is the bordered matrix.
    for e in (-1, 0, 2, 3):
        X2 = sum(F(g) ** (2 * e) for _, g in gaps)
        Y2 = sum(F(g) ** (2 - 2 * e) for _, g in gaps)
        check(sum(sign[b] * F(g) ** e * F(g) ** (1 - e) for b, g in gaps) == sg)
        check(is_psd([[X2, sg], [sg, Y2]]))
        check(X2 * Y2 >= g1 * g1)
    # Equality case x_i = s_i sqrt(g_i), y_i = sqrt(g_i): x_i^2 = y_i^2 = g_i,
    # so the Gram matrix is [[sum g, sum s g], [sum s g, sum g]], bound exactly sum g.
    check(is_psd([[g1, sg], [sg, g1]]) and abs(sg) <= g1)
    # LP extremal law (at most one predecessor): genuine distribution, PSD moments.
    H = 7
    rates = [F(1, 8)] * (H - 1)
    p0 = 1 - sum(rates)
    check(p0 >= 0)
    M = [[F(0)] * H for _ in range(H)]
    M[0][0] = F(1)
    for h in range(1, H):
        M[0][h] = M[h][0] = M[h][h] = rates[h - 1]
    check(is_psd(M))
    Emin = p0 * H + sum(rates[h - 1] * h for h in range(1, H))
    check(Emin == H - sum((H - h) * rates[h - 1] for h in range(1, H)))
    # Horizons with sum u_h > 1: greedy singleton law attains
    # sum_{v<H} (1 - sum_{h<=v} u_h)_+, the union-bound minimum.
    for Hg, ratesg in ((12, [F(1, 8)] * 11),
                       (7, [F(1, 3), F(1, 4), F(1, 4), F(1, 3), F(1, 5), F(1, 5)])):
        check(sum(ratesg) > 1)
        law, cum = {}, F(0)
        for h in range(1, Hg):
            take = min(ratesg[h - 1], 1 - cum)
            if take <= 0:
                break
            law[h], cum = take, cum + take
        check(cum == 1 and all(0 < law[h] <= ratesg[h - 1] for h in law))
        Eg = sum(h * p for h, p in law.items())          # min(g, H) = h under e_h
        check(Eg == sum(max(F(0), 1 - sum(ratesg[:v])) for v in range(Hg)))
        Mg = [[F(0)] * Hg for _ in range(Hg)]
        Mg[0][0] = F(1)
        for h, p in law.items():
            Mg[0][h] = Mg[h][0] = Mg[h][h] = p
        check(is_psd(Mg))
    print("Finite certificate: 12x12 signed Toeplitz Gram PSD and sign-flip invariant; "
          "9x9 mixed Gram PSD with Gm(-s) = J Gm(s) J (mixed entries change sign); "
          "gap Gram collapses; every tested 2x2 Gram bound >= sum g, equality attained; "
          "greedy singleton law optimal for horizons with sum u_h > 1.\n"
          f"[finite] backward sum s(m)1_U(m-h), h=1..8: {back}; forward: {fwd}")


# ------------------------------------------- D3: theta cube and fourth power

def theta_coefficients(limit):
    squares = [j * j for j in range(1, isqrt(limit) + 1)]
    coeff = [1] + [0] * limit
    powers = []
    for _ in range(4):
        nxt = coeff.copy()
        for sq in squares:
            for n in range(sq, limit + 1):
                nxt[n] += 2 * coeff[n - sq]
        powers.append(nxt)
        coeff = nxt
    return powers


def hurwitz(D):
    if D == 0:
        return F(-1, 12)
    if D % 4 in (1, 2):
        return F(0)
    total = F(0)
    a = 1
    while 3 * a * a <= D:
        for b in range(-a + 1, a + 1):
            if (b * b + D) % (4 * a):
                continue
            c = (b * b + D) // (4 * a)
            if c < a or (b < 0 and a == c):
                continue
            if a == c and b == 0:
                total += F(1, 2)
            elif a == b == c:
                total += F(1, 3)
            else:
                total += 1
        a += 1
    return total


def d3_identities(limit=2200):
    _, _, cube, fourth = theta_coefficients(limit)
    check([hurwitz(d) for d in (3, 4, 7, 8, 11, 12, 15, 16)] ==
          [F(1, 3), F(1, 2), 1, 1, 1, F(4, 3), 2, F(3, 2)])
    for n in range(1, limit + 1):
        m = n
        while m % 4 == 0:
            m //= 4
        check((cube[n] == 0) == (m % 8 == 7))
        check(cube[n] == cube[m])
        if n % 8 == 3:
            check(cube[n] % 8 == 0)
        odd = prod((p ** (e + 1) - 1) // (p - 1) for p, e in factors(n).items() if p != 2)
        check(fourth[n] == (8 if n % 2 else 24) * odd)
        if 2 * n <= limit and n % 2 == 0:
            check(fourth[2 * n] == fourth[n])
    # Gauss-Kronecker-Hurwitz: r_3(n) = 12 (H(4n) - 2 H(n)), and its special cases
    # with Hurwitz (weighted) class numbers; n = 3 needs no exclusion.
    for n in range(1, 601):
        h1, h4 = hurwitz(n), hurwitz(4 * n)
        check(cube[n] == 12 * (h4 - 2 * h1))
        if n % 4 in (1, 2):
            check(h1 == 0 and cube[n] == 12 * h4)
        elif n % 8 == 3:
            check(h4 == 4 * h1 and cube[n] == 24 * h1)
        elif n % 8 == 7:
            check(h4 == 2 * h1 and cube[n] == 0)
    check(cube[3] == 8 == 24 * hurwitz(3) and hurwitz(3) == F(1, 3))
    # sum r_3(8n+3) q^(8n+3) = 8 q^3 psi(q^8)^3, psi(q) = sum q^(j(j+1)/2).
    top = (limit - 3) // 8
    tri = [0] * (top + 1)
    j = 0
    while j * (j + 1) // 2 <= top:
        tri[j * (j + 1) // 2] += 1
        j += 1
    psi3 = conv(conv(tri, tri), tri)[:top + 1]
    for n in range(top + 1):
        check(cube[8 * n + 3] == 8 * psi3[n])
    # 4-dissection: Theta^3(q) - Theta^3(q^4) lives on n mod 8 in {1,2,3,5,6}.
    for n in range(1, limit + 1):
        diff = cube[n] - (cube[n // 4] if n % 4 == 0 else 0)
        check((diff != 0) <= (n % 8 in (1, 2, 3, 5, 6)))
    # Turan-Kubilius ingredients for v_2(r_4(n)): exact partial sums.
    for J in range(1, 40):
        check(sum(F(j, 2 ** j) for j in range(1, J + 1)) == 2 - F(J + 2, 2 ** J))
        check(sum(F(j * j, 2 ** j) for j in range(1, J + 1)) == 6 - F(J * J + 4 * J + 6, 2 ** J))
    ps = primes_upto(200000)[1:]
    freq = {}
    for p in ps:
        freq[v2(p + 1)] = freq.get(v2(p + 1), 0) + 1
    meanv = F(sum(v2(p + 1) for p in ps), len(ps))
    shares = [round(freq[j] / len(ps), 4) for j in (1, 2, 3)]
    print("Finite certificate: Legendre zeros, r3(4n)=r3(n), r3=12(H(4n)-2H(n)) (n<=600), "
          "8q^3 psi(q^8)^3, Jacobi r4, 4-dissection.\n"
          f"[finite] odd primes <= 2e5: share of v2(p+1)=1,2,3: {shares}, "
          f"mean v2(p+1) = {float(meanv):.4f} (Dirichlet density value 2)")
    return cube, fourth


def inertness(coeffs, k, t, nmax, free, rep, label):
    """Steer sum a_n 2^(-kn) by data-preserving bounded perturbations."""
    J = 2 ** (3 * k + 2)
    unit = F(1, 2 ** k)
    w = {m: sum(unit ** n for n in range(m, nmax + 1) if rep(n) == m) for m in free}
    base = sum(coeffs[n] * unit ** n for n in range(1, nmax + 1))
    cap = sum(2 ** t * J * w[m] for m in free)
    for m, m2 in zip(free, free[1:]):
        check(m2 - m <= 3)
        check(w[m] <= J * w[m2])        # one step is covered by the next index
    results = []
    targets = [base + cap / 3]
    dy = (base + 2 * cap / 3) * 2 ** 12
    targets.append(F(-((-dy.numerator) // dy.denominator), 2 ** 12))  # dyadic
    for y in targets:
        check(base <= y <= base + cap)
        R = y - base
        jm = {}
        for m in free:
            step = 2 ** t * w[m]
            jm[m] = min(J, int(R / step))
            R -= jm[m] * step
        check(0 <= R < 2 ** t * w[free[-1]] * 2)
        a = [0] * (nmax + 1)
        for n in range(1, nmax + 1):
            a[n] = coeffs[n] + 2 ** t * jm.get(rep(n), 0)
            check((a[n] == 0) == (coeffs[n] == 0))
            check((a[n] - coeffs[n]) % 2 ** t == 0 and 0 <= a[n] - coeffs[n] <= 2 ** t * J)
        for n in range(1, nmax + 1):
            if rep(n) != n:
                check(a[n] == a[rep(n)])
        check(sum(a[n] * unit ** n for n in range(1, nmax + 1)) == y - R)
        results.append(float(y))
    print(f"Finite certificate: {label} inertness, k={k}, t={t}, n<={nmax}: targets "
          f"{results[0]:.6f} and dyadic {results[1]:.6f} reached up to one final step.")


def d3_inertness(cube, fourth):
    def rep3(n):
        while n % 4 == 0:
            n //= 4
        return n
    free3 = [m for m in range(1, 241) if m % 4 and m % 8 != 7]
    inertness(cube, 1, 2, 240, free3, rep3, "theta-cube")

    def rep4(n):
        while n % 4 == 0:
            n //= 2
        return n
    free4 = [m for m in range(1, 241) if m % 4]
    inertness(fourth, 1, 3, 240, free4, rep4, "theta-fourth")
    # Infinite version: w_m <= 2 * 2^(-km) and w_{m+3} >= 2^(-k(m+3)).
    for k in range(1, 12):
        check(2 ** (3 * k + 2) * F(1, 2 ** (3 * k)) >= 2)


def d3_euler_cube():
    c3 = euler_power(3, 3000)
    tri = {}
    n = 0
    while n * (n + 1) // 2 <= 3000:
        tri[n * (n + 1) // 2] = (-1) ** n * (2 * n + 1)
        n += 1
    check(c3 == [tri.get(i, 0) for i in range(3001)])
    print("Finite certificate: Jacobi's identity for E^3 through q^3000 (GF-04 prior input).")


# ------------------------------------------- D4: higher Euler powers

FORMS = ((4, 6, 2, "eis"), (6, 4, 3, "gauss"), (8, 3, 4, "eis"))


def two_squares(p, D):
    for y in range(0, isqrt(p // D) + 1):
        x2 = p - D * y * y
        x = isqrt(x2)
        if x * x == x2:
            return x, y
    return None


def cm_candidates(p, w, field):
    D = 3 if field == "eis" else 1
    x, y = two_squares(p, D)
    A, B = 1, 0
    for _ in range(w - 1):
        A, B = A * x - D * B * y, A * y + B * x
    if field == "eis":
        return {abs(2 * A), abs(A + 3 * B), abs(A - 3 * B)}
    return {abs(2 * A), abs(2 * B)}


def is_prime(n):
    return n > 1 and factors(n) == {n: 1}


def d4_forms():
    data = {}
    for r, c, w, field in FORMS:
        M = 3400 if r == 4 else 2500
        er = euler_power(r, M)
        af = {c * j + 1: er[j] for j in range(M + 1)}
        if field == "eis":
            inert, split = (lambda q: q % 3 == 2), (lambda q: q % 3 == 1)
        else:
            inert, split = (lambda q: q % 4 == 3), (lambda q: q % 4 == 1)
        for n, val in af.items():
            if n == 1:
                continue
            fac = factors(n)
            expect = all(e % 2 == 0 for q, e in fac.items() if inert(q))
            check((val != 0) == expect, f"support r={r} n={n}")
            if fac == {n: 1}:
                check(split(n) and val != 0)
                check(val * val <= 4 * n ** (w - 1))
                check(abs(val) in cm_candidates(n, w, field))
        data[r] = (c, w, M, af)
    print("Finite certificate: CM support law, split-prime nonvanishing, |a(p)|^2 <= 4p^(w-1) "
          "and Hecke-character magnitude forms for eta(6t)^4, eta(4t)^6, eta(3t)^8.")
    return data


def floor_sci3(x):
    """(m, e) with 100 <= m < 1000 and m 10^e <= x < (m+1) 10^e, exactly (x > 0)."""
    e = 0
    while x >= 1000 * F(10) ** e:
        e += 1
    while x < 100 * F(10) ** e:
        e -= 1
    return int(x / F(10) ** e), e


def sci3(m, e):
    """Display m 10^e (100 <= m < 1000) as d.dd e+XX, from integers only."""
    return f"{m // 100}.{m % 100:02d}e{e + 2:+03d}"


# Lower bounds on tau_{w,k} quoted in the note, as (m, e) meaning tau > m 10^e.
CERTIFIED_TAU = {(2, 47): (136, -7), (2, 94): (195, -6),
                 (3, 93): (222, -8), (3, 186): (781, -7),
                 (4, 139): (638, -9), (4, 278): (443, -7)}


def d4_constants():
    log_lo, log_hi = log2_bounds()
    # tau_{w,k} = c' (1/2 - 32 lam) lam / 2 <= c'/1024 < 1/2, by the quadratic identity
    # 1/1024 - (1/2 - 32 lam) lam / 2 = 16 (lam - 1/128)^2 (checked at 4 points).
    for lam in (F(0), F(1, 128), F(1, 64), F(1, 7)):
        check(F(1, 1024) - (F(1, 2) - 32 * lam) * lam / 2 == 16 * (lam - F(1, 128)) ** 2)
    out = []
    certified = set()
    for (r, c, w, _), cp in zip(FORMS, (F(1, 5), F(2, 25), F(1, 22))):
        p_, q_ = cp.numerator, cp.denominator
        base = F(q_, p_) ** p_ * F(q_, q_ - p_) ** (q_ - p_) * 2 ** p_
        check(base ** (w - 1) < 2 ** q_)          # (w-1)(H(c')+c') < 1
        check(cp <= F(2, 3))
        k0 = next(k for k in range(1, 10 ** 4) if 32 * (w - 1) < k * log_lo)
        check(32 * (w - 1) >= (k0 - 1) * log_hi)   # integer threshold is exact
        kE = next(k for k in range(1, 10 ** 5) if 32 * c * (w - 1) < k * log_lo)
        check(32 * c * (w - 1) >= (kE - 1) * log_hi)
        check(cp <= F(1, 5) and cp / 1024 < F(1, 2))
        shown = []
        for k in (k0, 2 * k0):
            # lam uses log_lo (lam >= true lambda) and the outer factor log_hi, so
            # this rational number is a lower bound for the true tau_{w,k}.
            lam = F(w - 1, 2 * k) / log_lo
            tau = (F(1, 2) - 32 * lam) * cp * (w - 1) / (4 * k * log_hi)
            check(0 < tau <= cp / 1024)
            m, e = CERTIFIED_TAU[(w, k)]
            bound, ulp = m * F(10) ** e, F(10) ** e
            check(tau > bound)                   # the displayed lower bound, exactly
            check(tau < bound + ulp)             # ... and it is the 3-digit truncation
            check(floor_sci3(tau) == (m, e))
            certified.add((w, k))
            shown.append(f"tau_{{{w},{k}}} > {sci3(m, e)}")
        out.append(f"w={w}: k0={k0} (Euler index {kE}), " + ", ".join(shown))
    check(certified == set(CERTIFIED_TAU))
    # Mean of the singular series: sum_{h<=H} S(h) <= H, via the local identity.
    for p in primes_upto(2000)[1:]:
        check(1 + F(1, p * (p - 2)) == 1 / (1 - F(1, (p - 1) ** 2)))
    odd = primes_upto(300)[1:]
    inv_c2_lo = prod(1 / (1 - F(1, (p - 1) ** 2)) for p in odd)
    for H in range(2, 301, 2):
        s = sum(prod(F(p - 1, p - 2) for p in factors(h) if p > 2) for h in range(2, H + 1, 2))
        check(s <= F(H, 2) * inv_c2_lo)
    print("Finite certificate: entropy exponents and thresholds; certified lower bounds "
          "(exact rational inequalities, truncated downward): " + "; ".join(out))


def d4_quantitative_k2(dmax=99):
    """Lemma D4.0: D^+ <= 1 - min(1/4, tau/2), on purely periodic binary orbits.

    For x = a/d with d odd the orbit is a cycle of n distinct points b/d, D_N tends
    to the discrepancy D of the uniform measure on the cycle, and the transition
    density is tau = #{b : 1/4 <= b/d < 3/4} / n.  D is computed exactly over
    half-open intervals: sup(count/n - length) uses [p_i, p_j + eps), and
    sup(length - count/n) uses (p_i, p_j) with the endpoints 0 and 1 allowed.
    """
    seen, cycles, beyond = set(), 0, 0
    for d in range(3, dmax + 1, 2):
        for a0 in range(1, d):
            if a0 in seen or gcd(a0, d) != 1:
                continue
            orbit, b = [], a0
            while True:
                orbit.append(b)
                b = 2 * b % d
                if b == a0:
                    break
            seen.update(orbit)
            pts = sorted(orbit)
            n = len(pts)
            trans = sum(1 for b in pts if d <= 4 * b < 3 * d)
            best = 0                       # n d D, as an integer
            for i in range(n):
                for j in range(i, n):
                    best = max(best, (j - i + 1) * d - n * (pts[j] - pts[i]))
            ends = [0] + pts + [d]
            for i in range(n + 2):
                for j in range(i + 1, n + 2):
                    best = max(best, n * (ends[j] - ends[i]) - (j - i - 1) * d)
            D, tau = F(best, n * d), F(trans, n)
            check(D <= 1 - min(F(1, 4), tau / 2))
            beyond += D > 1 - tau / 2
            cycles += 1
            if d == 3:                     # x = 1/3: tau = 1 but D = 2/3 > 1 - tau/2
                check(D == F(2, 3) and tau == 1 and D > 1 - tau / 2)
        seen.clear()
    check(beyond == 1)                     # only the cycle {1/3, 2/3}
    print(f"Finite certificate: D_inf <= 1 - min(1/4, tau/2) on all {cycles} binary cycles "
          f"a/d, d odd <= {dmax}; cycles above the uncapped 1 - tau/2: {beyond} "
          f"(x = 1/3: tau = 1, D = 2/3).")


def d4_isolation_measure(data, k=24, P=20000, G=200):
    c, w, M, af = data[4]
    ps = [p for p in primes_upto(P + G) if p > 3]
    split = [p for p in ps if af.get(p, 0)]
    Z = sum(af[p] << (k * (P + G - p)) for p in split)
    lo, hi = (Z - 1) >> (k * G), (Z + 1) >> (k * G)
    check(lo == hi)                     # the tail beyond P+G has absolute value < 1
    frac = lo % (1 << (k * P))
    T = transitions(frac, k * P)
    iso = 0
    for i, p in enumerate(split):
        if p > P:
            break
        Hp = -(-((w - 1) * (4 * p).bit_length() // 2 + 4) // k)
        left = split[i - 1] if i else -10 ** 9
        iso += (p - left >= Hp and split[i + 1] - p >= Hp)
    nsp = sum(1 for p in split if p <= P)
    print(f"[finite] eta(6t)^4 prime subseries, k={k}, first {k * P} bits: transitions "
          f"{T} (density {T / (k * P):.5f}; GF-43 ceiling 1/(4k log 2) = "
          f"{1 / (4 * k * 0.693147):.5f}); isolated split primes {iso}/{nsp}.")


def d4_composite(data):
    out = []
    for r in (4, 6, 8):
        c, w, M, af = data[r]
        sup = [n for n, v in af.items() if v and n > 1]
        prime_idx = {n for n in sup if is_prime(n)}
        comp = [n for n in sup if n not in prime_idx]
        mw = F(sum(naf_weight(af[n]) for n in comp), len(comp))
        out.append(f"E^{r}: Euler indices <= {M}: support {len(sup)}, prime {len(prime_idx)}, "
                   f"composite {len(comp)}, mean NAF weight per supported composite index "
                   f"{float(mw):.2f}")
    print("[finite] " + "; ".join(out))


def d4_telescoping(N=1 << 14):
    d = [0] + [(4 ** n.bit_length() - 1) // 3 for n in range(1, N + 2)]
    c = [0] + [2 * d[n] - d[n + 1] for n in range(1, N + 1)]
    check(all(c[n] != 0 for n in range(1, N + 1)))
    check(sum(F(c[n], 2 ** n) for n in range(1, N + 1)) == d[1] - F(d[N + 1], 2 ** N))
    tot = sum(naf_weight(c[n]) for n in range(1, N + 1))
    check(tot >= N * (N.bit_length() - 3))
    print(f"Finite certificate: telescoping sequence, all coefficients nonzero, mean NAF "
          f"weight {tot / N:.2f} at N={N}, value d_1 = 1 (an integer, in M_2).")


if __name__ == "__main__":
    d1_constants()
    d1_class_b()
    d1_sharpness_model()
    d1_warning_and_gram_models()
    coeff, sign, ends = d1_measurements()
    d2_checks(coeff, sign, ends)
    cube, fourth = d3_identities()
    d3_inertness(cube, fourth)
    d3_euler_cube()
    data = d4_forms()
    d4_constants()
    d4_quantitative_k2()
    d4_isolation_measure(data)
    d4_composite(data)
    d4_telescoping()
    beta_sieve_exploration()
    print(f"All exact checks passed: {CHECKS[0]} assertions.")
