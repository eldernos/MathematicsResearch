"""Exact controls for Phase 22 Track C (the equality boundary d = r).

Run from the repository root:  python -B scripts/phase22_nonlinear_boundary.py

Notation (notes/phase22/nonlinear-equality-boundary.md):  b = 2, p = 3, t = ord_3 2 = 2,
C = C(2,3,s,d) = sum_i 3^(-s v_3(i)) 2^(-t i^d).  For an ordered r-tuple of indices the
level is the sum of the 3-adic valuations.  For H >= 0,

    p^(sH) C^r = X_H + Z_H,
    X_H = sum over tuples of level <= H of p^(s(H - level)) b^(-t m)   (integer coefficients),
    Z_H = sum over tuples of level  > H of p^(-s(level - H)) b^(-t m).

R   The retirement identity for C(2,3,1,2)^2 and C(2,3,2,2)^2 (H = 0..3) and for
    C(2,3,1,3)^3 (H = 0..2), checked coefficientwise against an independent convolution;
    integrality, support on sums of r positive d-th powers, and the linear mass bound
    A_H(Y) <= p^(sH) * vol * Y; the prefix identity {b^n R_n(Z_H)} = {p^(sH) b^n R_n(C^r)}.
G   Gap statistics up to X = 500000: sums of two positive squares S, the positions P_H of
    Z_H and the positions P_H^frac where z_H(m) is not an integer, the pairs of level > H,
    the inclusions 3^(2k) S^+ in P_H and 3^(2k) (squarefree S^+, = 2 mod 3) in P_H^frac,
    the examples m = 16810 and m = 450, coverage by long runs at the H-dependent depth
    threshold; sums of three positive cubes up to 10^6.
D   Certified binary digits of C(2,3,1,2)^2, C(2,3,2,2)^2,
    C(2,3,1,3)^3, and of X_0, Z_0: digit and block frequencies, transition density,
    extreme discrepancy D_N, rational prefix versus actual shift, jump classes.
    FINITE MEASUREMENTS ONLY; nothing asymptotic is inferred from them.
W   Point-set lemmas: D(MZ) <= M D(Z) and 1 - D(MZ) <= M (1 - D(Z)) (exact Fractions),
    the sharp-translation inequality on actual orbits, the Weyl transfer at frequency 3,
    the geometric form of Lemma U below log_b(eps q), and exact checks on the rational
    orbits {2^n / 3^e}.

All assertions on identities use exact integers or Fractions.  Floating point appears
only in measured statistics, which are labelled as such.
"""

from fractions import Fraction
from math import gamma, isqrt, log, pi, sqrt, cos, sin
import random
import time

B, P, T = 2, 3, 2  # radix, prime, t = ord_3(2)


def v3(n):
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def icbrt(x):
    r = int(round(x ** (1 / 3)))
    while r ** 3 > x:
        r -= 1
    while (r + 1) ** 3 <= x:
        r += 1
    return r


# ================================================================ R: retirement identity


def tuple_levels(r, d, Mmax):
    """dict m -> list of levels of ordered r-tuples of positive integers with sum of d-th powers m."""
    out = {}
    top = 1
    while (top + 1) ** d <= Mmax:
        top += 1
    pw = [(i ** d, v3(i)) for i in range(1, top + 1)]

    def rec(k, acc_m, acc_l):
        if k == r:
            out.setdefault(acc_m, []).append(acc_l)
            return
        for (q, l) in pw:
            if acc_m + q > Mmax:
                break
            rec(k + 1, acc_m + q, acc_l + l)

    rec(0, 0, 0)
    return out


def convolution_coeffs(r, d, s, Mmax):
    """Independent route: r-fold convolution of c1(k) = 3^(-s v(i)) at k = i^d, as Fractions."""
    c1 = {}
    i = 1
    while i ** d <= Mmax:
        c1[i ** d] = Fraction(1, 3 ** (s * v3(i)))
        i += 1
    cur = dict(c1)
    for _ in range(r - 1):
        nxt = {}
        for a, x in cur.items():
            for k, y in c1.items():
                if a + k <= Mmax:
                    nxt[a + k] = nxt.get(a + k, 0) + x * y
        cur = nxt
    return cur


def check_retirement():
    print("R  Retirement identity p^(sH) C^r = X_H + Z_H")
    cases = [(2, 2, 1, 20000, 3), (2, 2, 2, 20000, 3), (3, 3, 1, 30000, 2)]
    for (r, d, s, Mmax, Hmax) in cases:
        lev = tuple_levels(r, d, Mmax)
        conv = convolution_coeffs(r, d, s, Mmax)
        assert set(conv) == set(lev)
        vol = gamma(1 + 1 / d) ** r / gamma(1 + r / d)  # volume of {x >= 0 : sum x_i^d <= 1}
        for H in range(Hmax + 1):
            for m in sorted(lev):
                ls = lev[m]
                a = sum(3 ** (s * (H - l)) for l in ls if l <= H)
                z = sum(Fraction(1, 3 ** (s * (l - H))) for l in ls if l > H)
                assert isinstance(a, int)
                assert 3 ** (s * H) * conv[m] == a + z  # coefficientwise identity
                if z:
                    assert z.denominator % 3 == 0 or z.denominator == 1
            # linear mass: A_H(Y) <= p^(sH) * #tuples <= p^(sH) * vol * Y, checked at many Y
            cum = 0
            checkpoints = set(range(1000, Mmax + 1, 1000))
            for m in range(1, Mmax + 1):
                if m in lev:
                    cum += sum(3 ** (s * (H - l)) for l in lev[m] if l <= H)
                if m in checkpoints:
                    assert cum <= 3 ** (s * H) * vol * m
            ntup = sum(len(x) for x in lev.values())
            assert ntup <= vol * Mmax
        print(f"   (r,d,s)=({r},{d},{s}): identity exact for m <= {Mmax}, H = 0..{Hmax}; "
              f"X_H integral, supported on sums of {r} positive {d}-th powers; "
              f"tuples {ntup} <= vol*Y = {vol * Mmax:.0f}")
    # prefix identity {b^n R_n(Z_H)} = {p^(sH) b^n R_n(C^2)} for C(2,3,1,2)^2
    r, d, s = 2, 2, 1
    Mmax = 6000
    lev = tuple_levels(r, d, Mmax)
    E = 2 * s * 12  # common denominator exponent: levels <= 2*log_3(sqrt(Mmax)) < 12
    Q = 3 ** E
    for H in (0, 1, 2):
        yC = 0  # numerator of {b^n R_n(C^2)} over 3^E
        yZ = 0
        for n in range(1, T * Mmax + 1):
            yC = (2 * yC) % Q
            yZ = (2 * yZ) % Q
            if n % T == 0 and (n // T) in lev:
                ls = lev[n // T]
                yC = (yC + sum(3 ** (E - s * l) for l in ls)) % Q
                yZ = (yZ + sum(3 ** (E - s * (l - H)) for l in ls if l > H)) % Q
            assert (3 ** (s * H) * yC - yZ) % Q == 0
        print(f"   prefix identity {{b^n R_n(Z_{H})}} = {{3^{H} b^n R_n(C^2)}} exact for n <= {T * Mmax}")
    # 3 = 3 (mod 4): v_3(i^2 + j^2) = 2 min(v_3 i, v_3 j)
    for i in range(1, 400):
        for j in range(1, 400):
            assert v3(i * i + j * j) == 2 * min(v3(i), v3(j))
    print("   v_3(i^2 + j^2) = 2 min(v_3 i, v_3 j) for all i, j < 400")


# ================================================================ G: gap statistics


def gap_profile(pos, X):
    """Gap lengths of sorted positions in [1, X]: the integers of [1, X] are split into
    [1, pos[0]), [pos[k], pos[k+1]) and [pos[-1], X]; the lengths sum to exactly X."""
    gaps = [pos[0] - 1] + [pos[k + 1] - pos[k] for k in range(len(pos) - 1)] + [X + 1 - pos[-1]]
    assert sum(gaps) == X
    return gaps


def squarefree(n):
    q = 2
    while q * q <= n:
        if n % (q * q) == 0:
            return False
        q += 1
    return True


def cover(gaps, G, X):
    return sum(g for g in gaps if g >= G) / X


def check_gaps():
    print("G  Gap statistics (sums of two squares vs positions of Z_H; three cubes)")
    X = 500000
    s = 1
    maxlev = [-1] * (X + 1)
    minlev = [99] * (X + 1)
    LE = 24  # 3^LE clears every denominator 3^(level - H), level <= 2 log_3(sqrt X) < 24
    MODZ = 3 ** LE
    zacc = [[0] * (X + 1) for _ in range(4)]  # 3^LE * z_H(m) mod 3^LE, H = 0..3
    pairs_by_level = {}
    pairs_max_ge = {}  # pairs with max(h1, h2) >= K (the split C_{<K}, C_{>=K})
    top = isqrt(X)
    for i in range(1, top + 1):
        vi = v3(i)
        ii = i * i
        for j in range(1, isqrt(X - ii) + 1 if X - ii >= 1 else 1):
            m = ii + j * j
            vj = v3(j)
            l = vi + vj
            if l > maxlev[m]:
                maxlev[m] = l
            if l < minlev[m]:
                minlev[m] = l
            for H in range(4):
                if l > H:
                    zacc[H][m] = (zacc[H][m] + 3 ** (LE - (l - H))) % MODZ
            pairs_by_level[l] = pairs_by_level.get(l, 0) + 1
            mx = max(vi, vj)
            pairs_max_ge[mx] = pairs_max_ge.get(mx, 0) + 1
    npairs = sum(pairs_by_level.values())
    assert npairs <= pi * X / 4
    S = [m for m in range(1, X + 1) if maxlev[m] >= 0]
    gS = gap_profile(S, X)
    print(f"   X = {X}: ordered pairs {npairs} (pi X/4 = {pi * X / 4:.0f}); "
          f"|S| = {len(S)}; mean gap {X / len(S):.2f}; sqrt(log X) = {sqrt(log(X)):.2f}")
    # H-dependent depth threshold: at shifts n <= T X the top shell is 3^(2J) <= X, and by the
    # prefix identity q_n(Z_H) = q_n(C^2) / 3^H, so lambda_H = log_2(3^(2J - H) / 2).
    J2 = 0
    while 3 ** (J2 + 2) <= X:
        J2 += 2
    print(f"   top shell 3^{J2} <= X; depth threshold lambda_H = log_2(3^({J2} - H)/2)")
    print("   H | pairs lvl>H / all | |P_H| | mean gap | ratio to S | shifts in support runs >= lambda_H "
          "| integral z_H in P_H | |P_H^frac| | shifts in fractional runs >= lambda_H")
    sfqnr = [n for n in S if n % 3 == 2 and squarefree(n)]
    for H in range(0, 6):
        PH = [m for m in S if maxlev[m] > H]
        npH = sum(c for l, c in pairs_by_level.items() if l > H)
        k = (H + 2) // 2  # ceil((H+1)/2)
        Q = 3 ** (2 * k)
        setPH = set(PH)
        for m in S:  # inclusion 3^(2k) S^+ in P_H
            if Q * m > X:
                break
            assert Q * m in setPH
        g = gap_profile(PH, X)
        lam = log(3 ** (J2 - H) / 2, 2)
        sup = sum(gg for gg in g if T * gg >= lam) / X
        line = (f"   {H} | {npH / npairs:.4f} | {len(PH)} | {X / len(PH):.2f} | "
                f"{(X / len(PH)) / (X / len(S)):.2f} | {sup:.3f}")
        if H <= 3:
            Pfrac = [m for m in PH if zacc[H][m] != 0]
            setF = set(Pfrac)
            nint = len(PH) - len(Pfrac)
            # inclusion 3^(2k) * (squarefree n in S^+, n = 2 mod 3) in P_H^frac; z_H = 2^w 3^-(2k-H)
            for n in sfqnr:
                if Q * n > X:
                    break
                assert Q * n in setF
            gF = gap_profile(Pfrac, X)
            fr = sum(gg for gg in gF if T * gg >= lam) / X
            line += f" | {nint} | {len(Pfrac)} | {fr:.3f}"
            if H == 1:
                nint9 = sum(1 for n in S if Q * n <= X and zacc[1][Q * n] == 0)
                assert zacc[1][450] == 0  # 450 = 3^2 + 21^2 = 15^2 + 15^2: z_1 = 3 * (1/3) = 1
                line += f" (of which in 9 S^+: {nint9})"
            if H == 0:
                assert zacc[0][16810] == 0  # six level-1 pairs: z_0 = 6 * (1/3) = 2
        print(line + f"   [lambda_{H} = {lam:.2f}]")
    reps16810 = [(i, isqrt(16810 - i * i)) for i in range(1, 130)
                 if isqrt(16810 - i * i) ** 2 == 16810 - i * i and 16810 - i * i > 0]
    assert reps16810 == [(13, 129), (41, 123), (67, 111), (111, 67), (123, 41), (129, 13)]
    assert all(v3(i) + v3(j) == 1 for i, j in reps16810)
    print(f"   m = 16810: ordered representations {reps16810}, all of level 1, so z_0 = 6/3 = 2")
    print(f"   squarefree n in S^+ with n = 2 mod 3 up to X: {len(sfqnr)} (|S^+| = {len(S)})")
    # the split by max(v(i), v(j)) >= K of C = C_{<K} + C_{>=K}: pair fraction 2/p^K - 1/p^2K
    for K in (1, 2, 3):
        npK = sum(c for mx, c in pairs_max_ge.items() if mx >= K)
        print(f"   pairs with max(v(i),v(j)) >= {K}: fraction {npK / npairs:.4f} "
              f"(2/3^K - 1/9^K = {2 / 3 ** K - 1 / 9 ** K:.4f})")
    # coverage of [1, X] by S-gaps of length >= g (Hooley: -> 0 for g = eps log X)
    cS = [cover(gS, G, X) for G in (5, 10, 15, 20)]
    print(f"   cover of [1,X] by S-gaps >= 5,10,15,20: " + ", ".join(f"{c:.4f}" for c in cS))
    lam = log(3 ** J2 / 2, 2)
    print(f"   C^2: shifts in runs >= lambda = {lam:.2f}: {sum(gg for gg in gS if T * gg >= lam) / X:.3f}")
    # sums of three positive cubes
    for X3 in (500000, 10 ** 6):
        rep = bytearray(X3 + 1)
        lev3max = [-1] * (X3 + 1)
        c = icbrt(X3)
        ntrip = 0
        for i in range(1, c + 1):
            for j in range(1, c + 1):
                a = i ** 3 + j ** 3
                if a >= X3:
                    break
                for k in range(1, c + 1):
                    m = a + k ** 3
                    if m > X3:
                        break
                    ntrip += 1
                    rep[m] = 1
                    l = v3(i) + v3(j) + v3(k)
                    if l > lev3max[m]:
                        lev3max[m] = l
        S3 = [m for m in range(1, X3 + 1) if rep[m]]
        assert all(m % 9 not in (4, 5) for m in S3)  # cubes are 0, +-1 mod 9
        # level 0 does not force 3 not dividing m (contrast with the rule for squares)
        assert v3(1 + 1 + 1) == 1 and v3(1 + 8 + 64) == 0
        vol3 = gamma(4 / 3) ** 3
        assert ntrip <= vol3 * X3
        g3 = gap_profile(S3, X3)
        line = (f"   three positive cubes, X = {X3}: ordered triples {ntrip} (<= {vol3:.4f} X); "
                f"distinct {len(S3)} = {len(S3) / X3:.4f} X; mean gap {X3 / len(S3):.2f}; "
                f"max gap {max(g3)}; cover(gap>=20) {cover(g3, 20, X3):.3f}")
        print(line)
        if X3 == 500000:
            for H in (0, 1, 2):
                P3 = [m for m in S3 if lev3max[m] > H]
                print(f"      positions of Z_{H} (level > {H}): {len(P3)}, mean gap {X3 / len(P3):.2f}")
        # local densities in dyadic windows (finite measurement; positive density is open)
        if X3 == 10 ** 6:
            dens = []
            for lo in (62500, 125000, 250000, 500000):
                hi = 2 * lo
                cnt = sum(1 for m in range(lo + 1, min(hi, X3) + 1) if rep[m])
                dens.append(cnt / (min(hi, X3) - lo))
            print("      density in (Y, 2Y] for Y = 62500..500000: " + ", ".join(f"{x:.4f}" for x in dens))


# ================================================================ D: certified digits


def series_interval(terms, Q):
    """terms: list of (shift k, Fraction coef) meaning coef * 2^(-k).  Returns (lo, hi) with
    lo <= 2^Q * sum <= hi, exact integer arithmetic; all k assumed >= 1 and finite list
    covering every k <= Q.  tail_bound: caller adds its own bound to hi."""
    lo = 0
    err = 0
    for k, c in terms:
        if k <= Q:
            lo += (c.numerator << (Q - k)) // c.denominator
            err += 1
    return lo, lo + err


def C_interval(d, s, Q):
    terms = []
    i = 1
    while T * i ** d <= Q:
        terms.append((T * i ** d, Fraction(1, 3 ** (s * v3(i)))))
        i += 1
    lo, hi = series_interval(terms, Q)
    return lo, hi + 1  # tail beyond Q is < 2^(Q - T i^d) summed < 1


def power_interval(lo, hi, r, Q):
    """(lo/2^Q, hi/2^Q) bounds a positive x; return bounds on x^r at scale 2^Q."""
    return (lo ** r) >> (Q * (r - 1)), ((hi ** r) >> (Q * (r - 1))) + 1


def frac_bits(lo, hi, Q, need):
    """certified fractional bits (string of length >= need) of x with lo <= 2^Q x <= hi."""
    if (lo >> Q) != (hi >> Q):
        raise AssertionError("integer part not certified")
    flo, fhi = lo & ((1 << Q) - 1), hi & ((1 << Q) - 1)
    diff = flo ^ fhi
    cert = Q - diff.bit_length()
    assert cert >= need, (cert, need)
    s = bin(flo)[2:].zfill(Q)
    return s[:cert]


def integer_series_interval(coef, Q, H):
    """coef: dict position k = 2m -> a_H(m), nonnegative integers with a_H(m) <= 3^H sqrt(m)
    (an ordered pair is fixed by its first coordinate i <= sqrt m).  Terms with k <= Q are
    exact.  Q is even, so the omitted tail (all k > Q) is at most
        3^H sum_{u >= 1} sqrt(Q/2 + u) 4^(-u) <= 3^H sqrt(Q/2 + 1) sum_u sqrt(u) 4^(-u)
                                              <  3^H (isqrt(Q/2 + 1) + 1),
    since sum_u sqrt(u) 4^(-u) < 0.41.  Returns (lo, hi) with lo <= 2^Q X_H <= hi."""
    assert Q % 2 == 0
    lo = 0
    for k, a in coef.items():
        assert a * a <= 9 ** H * (k // 2)
        if k <= Q:
            lo += a << (Q - k)
    tail = 3 ** H * (isqrt(Q // 2 + 1) + 1)
    return lo, lo + tail


def discrepancy(points):
    xs = sorted(points)
    N = len(xs)
    mx = max((i + 1) / N - x for i, x in enumerate(xs))
    mn = min((i + 1) / N - x for i, x in enumerate(xs))
    return 1 / N + mx - mn


def orbit(bits, N):
    return [int(bits[n:n + 53], 2) / (1 << 53) for n in range(N)]


def digit_stats(bits, N):
    seg = bits[:N]
    ones = seg.count("1") / N
    trans = sum(1 for k in range(N - 1) if seg[k] != seg[k + 1]) / (N - 1)
    dev = 0.0
    for k in range(1, 5):
        cnt = {}
        for i in range(N - k + 1):
            w = seg[i:i + k]
            cnt[w] = cnt.get(w, 0) + 1
        tot = N - k + 1
        for w in range(2 ** k):
            key = bin(w)[2:].zfill(k)
            dev = max(dev, abs(cnt.get(key, 0) / tot - 2 ** -k))
    return ones, trans, dev


def check_digits():
    print("D  Certified digits and finite statistics (finite measurements, not proofs)")
    NB = 1 << 16
    Q = NB + 192
    results = {}
    lev2 = tuple_levels(2, 2, Q // T + 2)
    for (r, d, s) in [(2, 2, 1), (2, 2, 2), (3, 3, 1)]:
        lo, hi = C_interval(d, s, Q)
        plo, phi = power_interval(lo, hi, r, Q)
        bits = frac_bits(plo, phi, Q, NB + 60)
        z = orbit(bits, NB)
        ones, trans, dev = digit_stats(bits, NB)
        Ds = {N: discrepancy(z[:N]) for N in (1 << 10, 1 << 12, 1 << 14, 1 << 16)}
        results[(r, d, s)] = (bits, z)
        print(f"   C(2,3,{s},{d})^{r}: {len(bits)} certified bits; ones {ones:.4f}; "
              f"transitions {trans:.4f}; max block dev (k<=4) {dev:.4f}; D_N at N=2^10,12,14,16: "
              + ", ".join(f"{Ds[N]:.4f}" for N in sorted(Ds)))
    # X_0 and Z_0 for C(2,3,1,2)^2, and the rational prefix vs the actual shift
    bitsC, zC = results[(2, 2, 1)]
    for H in (0, 1):
        aH = {T * m: sum(3 ** (H - l) for l in ls if l <= H) for m, ls in lev2.items()}
        aH = {k: a for k, a in aH.items() if a}
        xlo, xhi = integer_series_interval(aH, Q, H)
        lo, hi = C_interval(2, 1, Q)
        plo, phi = power_interval(lo, hi, 2, Q)
        zlo, zhi = 3 ** H * plo - xhi, 3 ** H * phi - xlo
        # shift to positive fractional window
        off = ((-zlo) >> Q) + 1 << Q if zlo < 0 else 0
        bitsZ = frac_bits(zlo + off, zhi + off, Q, NB + 60)
        bitsX = frac_bits(xlo, xhi, Q, NB + 60)
        zZ, zX = orbit(bitsZ, NB), orbit(bitsX, NB)
        # sharp translation on the actual orbits: |D(3^H C^2) - D(Z_H)| <= 1 - D(X_H)
        z3 = [(3 ** H * u) % 1.0 for u in zC]
        for N in (1 << 12, 1 << 14, 1 << 16):
            dC, dZ, dX = discrepancy(z3[:N]), discrepancy(zZ[:N]), discrepancy(zX[:N])
            assert abs(dC - dZ) <= 1 - dX + 1e-9
        dC, dZ, dX = discrepancy(z3), discrepancy(zZ), discrepancy(zX)
        mean_dist = sum(min(u, 1 - u) for u in zX) / NB
        print(f"   H={H}: D_N(3^H C^2)={dC:.4f}, D_N(Z_{H})={dZ:.4f}, D_N(X_{H})={dX:.4f} at N=2^16; "
              f"mean ||b^n X_{H}|| = {mean_dist:.3f} (K_b-ness of X_H is invisible at this N)")
        if H == 1:
            # Weyl transfer at frequency 3: |S_N(C^2;3) - S_N(Z_1;1)| <= 2 pi sum ||b^n X_1||
            def S(pts, h):
                re = sum(cos(2 * pi * h * u) for u in pts)
                im = sum(sin(2 * pi * h * u) for u in pts)
                return complex(re, im)
            lhs = abs(S(zC, 3) - S(zZ, 1)) / NB
            rhs = 2 * pi * mean_dist
            assert lhs <= rhs + 1e-6
            print(f"   Weyl transfer: |S_N(C^2;3) - S_N(Z_1;1)|/N = {lhs:.4f} <= 2 pi mean||b^n X_1|| "
                  f"= {rhs:.4f}; |S_N(C^2;1)|/N = {abs(S(zC, 1)) / NB:.4f}")
    # rational prefix y_n = {b^n R_n} versus actual shift, and jump classes
    E = 30
    Mod = 3 ** E
    y = 0
    tails = []
    yZ0 = 0
    for n in range(1, NB + 1):
        y = (2 * y) % Mod
        yZ0 = (2 * yZ0) % Mod
        if n % T == 0 and (n // T) in lev2:
            ls = lev2[n // T]
            y = (y + sum(3 ** (E - l) for l in ls)) % Mod
            yZ0 = (yZ0 + sum(3 ** (E - l) for l in ls if l >= 1)) % Mod
        assert y == yZ0  # integer (level-0) jumps never move the rational orbit
        if n < NB:
            tails.append((zC[n] - y / Mod) % 1.0)
    big = sum(1 for u in tails if 0.125 <= u <= 0.875) / len(tails)
    tiny = sum(1 for u in tails if min(u, 1 - u) < 2 ** -20) / len(tails)
    print(f"   rational orbit {{b^n R_n}} equals the orbit of Z_0's prefix for all n <= 2^16 (exact); "
          f"tail in [1/8,7/8] on {big:.3f} of shifts, tail < 2^-20 on {tiny:.3f}")
    jumps = {"integral": 0, "den 3": 0, "den 9": 0, "den >= 27": 0}
    npos = 0
    for m, ls in lev2.items():
        if T * m > NB:
            continue
        npos += 1
        c = sum(Fraction(1, 3 ** l) for l in ls)
        dden = (c - int(c)).denominator
        key = ("integral" if dden == 1 else "den 3" if dden == 3 else "den 9" if dden == 9 else "den >= 27")
        jumps[key] += 1
    print(f"   jump classes at the {npos} positions m <= 2^15: "
          + ", ".join(f"{k} {v / npos:.3f}" for k, v in jumps.items()))


# ================================================================ W: point-set lemmas


def disc_exact(points):
    xs = sorted(points)
    N = len(xs)
    vals = [Fraction(i + 1, N) - x for i, x in enumerate(xs)]
    return Fraction(1, N) + max(vals) - min(vals)


def check_lemmas():
    print("W  Point-set lemmas and the incomplete-orbit obstruction")
    rng = random.Random(22)
    cnt = 0
    for trial in range(300):
        N = rng.randint(1, 40)
        mode = trial % 3
        if mode == 0:
            pts = [Fraction(rng.randrange(1000), 1000) for _ in range(N)]
        elif mode == 1:  # concentrated near 0
            pts = [Fraction(rng.randrange(20), 1000) for _ in range(N)]
        else:  # concentrated near a fixed point of x -> 2x?  only 0; near 1/3-orbit
            pts = [Fraction(rng.choice([1, 2]), 3) + Fraction(rng.randrange(10), 10 ** 4) for _ in range(N)]
        D = disc_exact(pts)
        for M in (2, 3, 5, 9):
            MD = disc_exact([(M * x) % 1 for x in pts])
            assert MD <= M * D
            assert 1 - MD <= M * (1 - D)
            cnt += 1
    print(f"   D(MZ) <= M D(Z) and 1 - D(MZ) <= M (1 - D(Z)) hold on {cnt} exact point sets")
    # orbit of a/3^e: lemma on D^+ transfer for the rational orbit (exact)
    for e in (4, 6, 8):
        q = 3 ** e
        pts = [Fraction(pow(2, n, q), q) for n in range(200)]
        D = disc_exact(pts)
        for M in (3, 9):
            MD = disc_exact([(M * x) % 1 for x in pts])
            assert 1 - MD <= M * (1 - D)
    print("   the same inequalities hold on the orbits {2^n / 3^e}, e = 4, 6, 8")
    # no uniform short-orbit bound below log_b(eps q): numerator a = 1 (Lemma U, geometric form)
    for e in (20, 40, 80):
        q = 3 ** e
        eps = Fraction(1, 64)
        Tlen = 0
        while 2 ** (Tlen + 1) <= eps * q:  # largest integer T with b^T <= eps q
            Tlen += 1
        geo = sum(Fraction(2 ** j, q) for j in range(Tlen))
        assert geo == Fraction(2 ** Tlen - 1, q) and geo < eps / (B - 1)
        val = sum(complex(cos(2 * pi * 2 ** j / q), sin(2 * pi * 2 ** j / q)) for j in range(Tlen))
        assert abs(val - Tlen) <= 2 * pi * float(eps) / (B - 1) + 1e-12
        print(f"   q = 3^{e}: T = {Tlen} = floor(log_2(q/64)); |sum_(j<T) e(2^j/q) - T| = "
              f"{abs(val - Tlen):.2e} <= 2 pi eps/(b-1) = {2 * pi * float(eps):.3f}")


def main():
    t0 = time.time()
    check_retirement()
    check_gaps()
    check_digits()
    check_lemmas()
    print(f"All Phase 22 Track C checks passed in {time.time() - t0:.1f} s.")


if __name__ == "__main__":
    main()
