"""Phase 16, Track 4: Non-flat approximants to ln 2.

1. Full balanced classification (all radii 2^(a/e), all degrees):
   Verifies Kummer/Galois collapse f(X) = g(X^r), irreducibility over Q,
   power-sum vanishing for r !| j, and exact prefix-level collapse
   S_{f,t}(x) -> Z-combination of {A_k, G_t} across a comprehensive test
   suite for e in {3, 4, 5, 6, 8, 12} (plus reducible balanced products).

2. Unbalanced algebraic trace sources (mu < A < t):
   Systematic search over irreducible monic integer polynomials of degrees
   2, 3, 4 with {2,3,5,7}-smooth |f(2^t)|, Lagrange 2-adic non-cancellation
   check, exact 2-adic + odd-prime Frobenius full-rate minimization against
   the Phase 14 alphabet, and finite-N reduced-denominator verification.

3. Pade, asymmetric Legendre/beta integrals, simultaneous Type II Pade,
   and rounded Chebyshev-pole integrals:
   Exact rational evaluations, shifted binary denominator rates (log q_N)/N,
   precision windows, prime-band cancellation, and asymptotic saddle-point
   analysis.

Run: python -B scripts/phase16_nonflat.py
"""

import cmath
import math
from decimal import Decimal, getcontext
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, isqrt, lcm, log, log2


def v2(n):
    n = abs(n)
    if n == 0:
        return 10**9
    return (n & -n).bit_length() - 1


def factor_small(n, bound=10**5):
    n = abs(n)
    if n == 0:
        return None
    out = {}
    d = 2
    while d <= bound and d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        if d * d <= n:
            return None
        out[n] = out.get(n, 0) + 1
    return out


def is_smooth_2357(n):
    n = abs(n)
    if n == 0:
        return False
    for p in (2, 3, 5, 7):
        while n % p == 0:
            n //= p
    return n == 1


def newton(f, J):
    """Power sums p_1..p_J of monic integer poly f (low to high)."""
    d = len(f) - 1
    assert f[-1] == 1
    e = [1] + [(-1) ** k * f[d - k] for k in range(1, d + 1)]
    p = [0] * (J + 1)
    for j in range(1, J + 1):
        if j <= d:
            s = sum((-1) ** (k - 1) * e[k] * p[j - k] for k in range(1, j))
            s += (-1) ** (j - 1) * j * e[j]
        else:
            s = sum((-1) ** (k - 1) * e[k] * p[j - k] for k in range(1, d + 1))
        p[j] = s
    return p


def poly_eval(f, x):
    r = 0
    for c in reversed(f):
        r = r * x + c
    return r


def poly_mul(a, b):
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                res[i + j] += x * y
    return res


def poly_from_roots_complex(roots):
    p = [1 + 0j]
    for r in roots:
        np = [0j] * (len(p) + 1)
        for i, c in enumerate(p):
            np[i] -= c * r
            np[i + 1] += c
        p = np
    out = []
    for c in p:
        assert abs(c.imag) < 1e-6 * max(1.0, abs(c)), f"Non-real coeff {c}"
        rc = round(c.real)
        assert abs(c.real - rc) < 1e-6 * max(1, abs(rc)), f"Non-integer coeff {c}"
        out.append(int(rc))
    return out


def newton_polygon_min_valuation(f):
    pts = [(k, v2(c)) for k, c in enumerate(f) if c]
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x2) >= (pt[1] - y2) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    slopes_ = [Q(y2 - y1, x2 - x1) for (x1, y1), (x2, y2) in zip(hull, hull[1:])]
    return -max(slopes_)


def complex_roots(f, iters=300):
    d = len(f) - 1
    if d == 1:
        return [complex(-f[0])]
    if d == 2:
        b, c = f[1], f[0]
        sq = cmath.sqrt(b * b - 4 * c)
        return [(-b + sq) / 2, (-b - sq) / 2]
    rad = 1.0 + max(abs(c) for c in f[:-1])
    roots = [rad * cmath.exp(2j * math.pi * (k + 0.137) / d) for k in range(d)]
    for _ in range(iters):
        max_step = 0.0
        new = []
        for i, r in enumerate(roots):
            val = 0j
            for c in reversed(f):
                val = val * r + c
            den = 1 + 0j
            for j, s in enumerate(roots):
                if i != j:
                    den *= r - s
            step = 0j if abs(den) < 1e-30 else val / den
            if abs(step) > max_step:
                max_step = abs(step)
            new.append(r - step)
        roots = new
        if max_step < 1e-13:
            break
    return roots


def dec_ln2(prec):
    getcontext().prec = prec + 20
    return Decimal(2).ln()


def mobius(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r


def divisors(n):
    n = abs(n)
    small, large = [], []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
    return small + large[::-1]


def is_irreducible_deg234(f):
    d = len(f) - 1
    assert d in (2, 3, 4) and f[-1] == 1
    if f[0] == 0:
        return False
    for r in divisors(f[0]):
        if poly_eval(f, r) == 0 or poly_eval(f, -r) == 0:
            return False
    if d <= 3:
        return True
    a0, a1, a2, a3, _ = f
    for q_abs in divisors(a0):
        for q in (q_abs, -q_abs):
            s = a0 // q
            if q != s:
                num = a1 - q * a3
                den = s - q
                if num % den == 0:
                    p = num // den
                    r = a3 - p
                    if p * r + q + s == a2:
                        return False
            else:
                if a1 == q * a3:
                    disc = a3 * a3 - 4 * (a2 - 2 * q)
                    if disc >= 0:
                        sq = isqrt(disc)
                        if sq * sq == disc and (a3 + sq) % 2 == 0:
                            return False
    return True


def is_irreducible_via_root_subsets(roots):
    d = len(roots)
    for k in range(1, d // 2 + 1):
        for sub in combinations(roots, k):
            prod = 1 + 0j
            for r in sub:
                prod *= r
            if abs(prod.imag) > 1e-5 or abs(prod.real - round(prod.real)) > 1e-5:
                continue
            tr = sum(sub)
            if abs(tr.imag) > 1e-5 or abs(tr.real - round(tr.real)) > 1e-5:
                continue
            p = [1 + 0j]
            for r in sub:
                np = [0j] * (len(p) + 1)
                for i, c in enumerate(p):
                    np[i] -= c * r
                    np[i + 1] += c
                p = np
            if all(abs(c.imag) < 1e-5 and abs(c.real - round(c.real)) < 1e-5 for c in p):
                return False
    return True


def flat_orbit_phases(M, ap, sign_flip=False):
    units = [s for s in range(1, M + 1) if gcd(s, M) == 1]
    th = set()
    shift = Q(1, 2) if sign_flip else Q(0)
    for s in units:
        if ap % 2 == 0:
            th.add((Q(s, M) + shift) % 1)
        elif M % 8 == 0:
            th.add((Q(s, M) + (Q(1, 2) if s % 8 in (3, 5) else Q(0)) + shift) % 1)
        else:
            th.add((Q(s, M) + shift) % 1)
            th.add((Q(s, M) + Q(1, 2) + shift) % 1)
    return sorted(th)


def full_galois_orbit_phases(e, a, M, b_phase):
    r = e if (e % 2 == 1) else e // 2
    L = lcm(lcm(e, M), 8)
    units = [u for u in range(1, L + 1) if gcd(u, L) == 1]
    phases = set()
    for u in units:
        if e % 2 == 1:
            for k in range(e):
                phases.add((Q(a * k, e) + Q(b_phase * u, M)) % 1)
        else:
            delta = 0 if (u % 8 in (1, 7)) else 1
            for k in range(r):
                phases.add((Q(a * (2 * k + delta), e) + Q(b_phase * u, M)) % 1)
    return sorted(phases)


def nu(n, vec):
    out = {}
    for th, mult in vec.items():
        for m in range(n):
            xi = ((th + m) / n) % 1
            out[xi] = out.get(xi, 0) + mult
    return out


def add_vec(u, v, c=1):
    out = dict(u)
    for k, m in v.items():
        out[k] = out.get(k, 0) + c * m
        if out[k] == 0:
            del out[k]
    return out


def dec_vec_A(k):
    return nu(2 * k, {Q(0): 1})


def dec_vec_G(t):
    return nu(2 * t - 1, {Q(1, 8): 1, Q(7, 8): 1})


def vec_of_dec(dec):
    out = {}
    for (kind, idx), c in dec.items():
        if c:
            out = add_vec(out, dec_vec_A(idx) if kind == "A" else dec_vec_G(idx), c)
    return out


def decompose_flat_orbit(M, ap, n, phases_target):
    res = {}

    def addA(k, c):
        res[("A", k)] = res.get(("A", k), 0) + c

    def via_Z(coefs):
        acc = {}
        for c, a in coefs.items():
            acc[n * c] = acc.get(n * c, 0) + a
        for idx, a in acc.items():
            if a:
                assert idx % 2 == 0
                addA(idx // 2, a)

    def P(Mc):
        return {d: mobius(Mc // d) for d in divisors(Mc) if mobius(Mc // d)}

    target = nu(n, {th: 1 for th in phases_target})

    if ap % 2 == 0 or M % 16 == 0:
        via_Z(P(M))
        res = {k: v for k, v in res.items() if v}
        assert vec_of_dec(res) == target
        return res
    elif M % 8 != 0:
        half = Q(1, 2)
        plain = {Q(s, M) % 1 for s in range(1, M + 1) if gcd(s, M) == 1}
        shifted = {(x + half) % 1 for x in plain}
        coefs = dict(P(M))
        if shifted != plain:
            Mp = 2 * M if M % 2 else (M if M % 4 == 0 else M // 2)
            for d, a in P(Mp).items():
                coefs[d] = coefs.get(d, 0) + a
        via_Z(coefs)
        res = {k: v for k, v in res.items() if v}
        assert vec_of_dec(res) == target
        return res
    else:
        Mp = M // 8
        for eps in ("g", "gp"):
            cand = {}
            for d in divisors(Mp):
                mu_ = mobius(Mp // d)
                if not mu_:
                    continue
                use_g = (eps == "g") == (d % 8 in (1, 7))
                nd = n * d
                if use_g:
                    cand[("G", (nd + 1) // 2)] = cand.get(("G", (nd + 1) // 2), 0) + mu_
                else:
                    cand[("A", 4 * nd)] = cand.get(("A", 4 * nd), 0) + mu_
                    cand[("A", 2 * nd)] = cand.get(("A", 2 * nd), 0) - mu_
                    cand[("G", (nd + 1) // 2)] = cand.get(("G", (nd + 1) // 2), 0) - mu_
            if vec_of_dec(cand) == target:
                return {k: v for k, v in cand.items() if v}
        raise AssertionError(f"Decomposition failed for M={M}, ap={ap}, n={n}")


def prefix_A(k, x_num, x_den):
    jmax = x_num // (k * x_den)
    return sum((Q(1, j << (k * j)) for j in range(1, jmax + 1)), Q())


_G_PS = [0]


def prefix_G(t, x_num, x_den):
    global _G_PS
    jmax = (2 * x_num) // ((2 * t - 1) * x_den)
    if len(_G_PS) <= jmax:
        _G_PS = newton([2, -2, 1], max(jmax, 2 * len(_G_PS)))
    return sum((Q(_G_PS[j], j << (t * j)) for j in range(1, jmax + 1)), Q())


def section_1_balanced():
    print("== SECTION 1: Complete Balanced Classification (all radii 2^(a/e))")
    cases = [
        (4, 1, 1, 1), (4, 1, 4, 1), (4, 1, 8, 1), (4, 1, 16, 1), (4, 1, 16, 3),
        (4, 1, 24, 1), (4, 1, 32, 1), (4, 1, 48, 1), (4, 3, 8, 1), (4, 3, 16, 1),
        (3, 1, 1, 1), (3, 1, 3, 1), (3, 1, 4, 1), (3, 1, 6, 1), (3, 1, 8, 1),
        (3, 1, 9, 1), (3, 1, 12, 1), (3, 2, 1, 1), (3, 2, 9, 1),
        (5, 1, 1, 1), (5, 1, 5, 1), (5, 1, 10, 1), (5, 2, 5, 1), (5, 2, 15, 1),
        (6, 1, 1, 1), (6, 1, 3, 1), (6, 1, 8, 1), (6, 1, 12, 1), (6, 1, 24, 1),
        (6, 1, 24, 5), (6, 1, 48, 1), (6, 5, 24, 1),
        (8, 1, 1, 1), (8, 1, 8, 1), (8, 1, 16, 1), (8, 1, 32, 1), (8, 1, 32, 3),
        (8, 3, 16, 1), (8, 3, 32, 1),
        (12, 1, 1, 1), (12, 1, 12, 1), (12, 1, 24, 1), (12, 1, 48, 1), (12, 5, 48, 1),
    ]

    subset_irred_count = 0
    for e, a, M, b_phase in cases:
        assert gcd(a, e) == 1 and gcd(b_phase, M) == 1
        r = e if (e % 2 == 1) else e // 2
        ap = 2 * a if (e % 2 == 1) else a
        th_beta = Q(b_phase * r, M) % 1
        M_beta = th_beta.denominator
        phases_pos = flat_orbit_phases(M_beta, ap, sign_flip=False)
        if th_beta in phases_pos:
            phases = phases_pos
        else:
            phases = flat_orbit_phases(M_beta, ap, sign_flip=True)
            assert th_beta in phases
        beta_roots = [(2.0 ** (ap / 2.0)) * cmath.exp(2j * math.pi * float(th)) for th in phases]
        g = poly_from_roots_complex(beta_roots)
        f = [0] * (r * (len(g) - 1) + 1)
        for i, c in enumerate(g):
            f[i * r] = c
        gal_phases = full_galois_orbit_phases(e, a, M, b_phase)
        gal_roots = [(2.0 ** (a / e)) * cmath.exp(2j * math.pi * float(th)) for th in gal_phases]
        f_gal = poly_from_roots_complex(gal_roots)
        assert f == f_gal, f"f(X) != Galois orbit poly for {(e,a,M,b_phase)}"
        assert newton_polygon_min_valuation(f) == Q(a, e)
        if len(gal_roots) <= 12:
            assert is_irreducible_via_root_subsets(gal_roots), f"Reducible! {(e,a,M,b_phase)}"
            subset_irred_count += 1
        Jcheck = min(64, 4 * r + 16)
        pf = newton(f, Jcheck)
        pg = newton(g, Jcheck // r + 1)
        for j in range(1, Jcheck + 1):
            if j % r != 0:
                assert pf[j] == 0
            else:
                assert pf[j] == r * pg[j // r]
        t = (a // e) + 1
        T = r * t
        n_flat = 2 * T - ap
        dec = decompose_flat_orbit(M_beta, ap, n_flat, phases)
        et_a = e * t - a
        for num in range(1, 32):
            for x_den in (2, e):
                jmax_f = (e * num) // (et_a * x_den)
                if jmax_f > len(pf) - 1:
                    pf = newton(f, jmax_f)
                sf_val = sum((Q(pf[j], j << (t * j)) for j in range(1, jmax_f + 1)), Q())
                comb_val = Q()
                for (kind, idx), coef in dec.items():
                    comb_val += coef * (prefix_A(idx, num, x_den) if kind == "A" else prefix_G(idx, num, x_den))
                assert sf_val == comb_val
        if (e, a, M, b_phase) in [
            (4, 1, 16, 1), (4, 1, 16, 3), (4, 3, 8, 1), (4, 1, 32, 1), (4, 1, 48, 1),
            (3, 1, 9, 1), (5, 2, 5, 1), (6, 1, 24, 1), (8, 1, 32, 1), (12, 1, 48, 1),
        ]:
            terms = " + ".join(f"{c}*{k}{i}" for (k, i), c in sorted(dec.items())).replace("+ -", "- ")
            print(f"   (e={e:2d}, a={a}, M={M:2d}, b={b_phase}) r={r:2d} deg={len(f)-1:2d} t={t} -> {terms}")
    f_red = [4, 0, 0, 0, 0, 0, 0, 0, 1]
    pf_red = newton(f_red, 40)
    for num in range(1, 30):
        jmax = (4 * num) // (3 * 2)
        val_red = sum((Q(pf_red[j], j << j) for j in range(1, jmax + 1)), Q())
        assert val_red == prefix_A(12, num, 2) - prefix_A(6, num, 2)
    print(f"   Verified all {len(cases)} balanced irreducible sources (e in {{3,4,5,6,8,12}}; {subset_irred_count} subset-certified)")
    print("   plus reducible product X^8 + 4 = (X^4-2X^2+2)(X^4+2X^2+2) -> A_12 - A_6 at all cutoffs.")


def section_2_unbalanced():
    print("\n== SECTION 2: Unbalanced Algebraic Trace Sources (mu < A < t)")
    candidates = []

    def inspect_poly(f):
        d = len(f) - 1
        if f[0] == 0:
            return
        if all(f[k] % (1 << (d - k)) == 0 for k in range(d)):
            return
        smooth_ts = []
        for t in range(1, 7):
            val = poly_eval(f, 1 << t)
            if val != 0 and is_smooth_2357(val):
                smooth_ts.append((t, val))
        if not smooth_ts:
            return
        if not is_irreducible_deg234(f):
            return
        mu = newton_polygon_min_valuation(f)
        roots = complex_roots(f)
        A = max(log2(abs(r)) for r in roots)
        if A - float(mu) < 1e-6:
            return
        for t, val in smooth_ts:
            if A >= t - 1e-9:
                continue
            fac = factor_small(val)
            rho2 = (A - float(mu)) / (t - A) * log(2)
            candidates.append((rho2, d, f, t, float(mu), A, val, fac))

    for b in range(-20, 21):
        for c in range(-32, 33):
            if c:
                inspect_poly([c, b, 1])
    for a2 in range(-6, 7):
        for a1 in range(-10, 11):
            for a0 in range(-16, 17):
                if a0:
                    inspect_poly([a0, a1, a2, 1])
    for a3 in range(-3, 4):
        for a2 in range(-5, 6):
            for a1 in range(-5, 6):
                for a0 in range(-8, 9):
                    if a0:
                        inspect_poly([a0, a1, a2, a3, 1])

    candidates.sort(key=lambda x: x[0])
    print(f"   Found {len(candidates)} irreducible unbalanced (f, t) with {{2,3,5,7}}-smooth |f(2^t)| (deg 2..4).")
    print("   Lowest 10 by 2-adic cost rho_2 = ((A - mu)/(t - A)) * ln 2:")
    print("   %-24s  d  t    mu      A     t-A    rho_2     f(2^t)" % "f(X) [low..high]")
    for rho2, d, f, t, mu, A, val, fac in candidates[:10]:
        fstr = "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(fac.items()))
        if val < 0:
            fstr = "-" + fstr
        print("   %-24s  %d  %d  %5.3f  %6.4f  %5.3f  %7.5f   %s" % (str(f), d, t, mu, A, t - A, rho2, fstr))

    benchmarks = [
        ("1+sqrt(-7)", [8, -2, 1], 3),
        ("3+sqrt(-7)", [16, -6, 1], 3),
        ("1+2i", [5, -2, 1], 2),
        ("2+sqrt(-3)", [7, -4, 1], 2),
        ("1+sqrt(2)", [-1, -2, 1], 2),
        ("phi (X^2-X-1)", [-1, -1, 1], 1),
        ("plastic (X^3-X-1)", [-1, -1, 0, 1], 1),
    ]
    print("\n   Benchmark unbalanced sources & Lagrange 2-adic non-cancellation check:")
    for name, f, t in benchmarks:
        d = len(f) - 1
        mu = newton_polygon_min_valuation(f)
        A = max(log2(abs(r)) for r in complex_roots(f))
        val = poly_eval(f, 1 << t)
        fac = factor_small(val)
        rho2 = (A - float(mu)) / (t - A) * log(2)
        ps = newton(f, 120)
        max_ex = max(min(v2(ps[j]) for j in range(J - d + 1, J + 1)) - float(mu) * J for J in range(d, 121))
        fstr = "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(fac.items()))
        print(f"   {name:18s} t={t} mu={str(mu):4s} A={A:.4f} rho_2={rho2:.5f} f(2^t)={val} ({fstr}) max_v2_excess={max_ex:.2f}")

    print("\n   Full rate (rho_2 + rho_odd) combining lowest-rho_2 unbalanced sources with Phase 14 alphabet:")
    test_list = list(candidates[:8])
    for item in candidates:
        if item[2] == [8, -2, 1] and item[3] == 3 and item not in test_list:
            test_list.append(item)
            break

    best_full = (10.0, None)
    for rho2, d, f, t, mu, A, val, fac in test_list:
        e2 = d * t - fac.get(2, 0)
        e3 = -fac.get(3, 0)
        e5 = -fac.get(5, 0)
        e7 = -fac.get(7, 0)
        u_A1 = -(e2 + 2 * e3 + 3 * e5 + 3 * e7)
        u_A2 = e3
        u_A3 = e7
        u_G2 = e5
        s_stride = t - A
        ps_f = newton(f, 40)

        def odd_rate_fn(c0, p14_par):
            a_, u_, b_, c_ = p14_par
            a6 = a_ + u_ + b_ + c_ - 1
            a4 = -b_ - 2 * c_
            cA1 = a_ + c0 * u_A1
            cA2 = -a4 - 2 * a6 + c0 * u_A2
            cA3 = -a6 + c0 * u_A3
            cA4 = a4
            cA6 = a6
            cG1 = u_
            cG2 = b_ + c0 * u_G2
            cG3 = c_
            X = 12.0
            pts = {0.0, X}
            for v in range(1, 25):
                pts.add(v / 2.0)
            k = 1
            while k * s_stride < X:
                pts.add(k * s_stride)
                k += 1
            pts = sorted(pts)
            rate = 1.0 / X
            for lo, hi in zip(pts, pts[1:]):
                if hi - lo < 1e-12:
                    continue
                mid = 0.5 * (lo + hi)
                val_s = Q()
                if cA1:
                    val_s += cA1 * prefix_A(1, int(mid), 1)
                if cA2:
                    val_s += cA2 * prefix_A(2, int(mid), 1)
                if cA3:
                    val_s += cA3 * prefix_A(3, int(mid), 1)
                if cA4:
                    val_s += cA4 * prefix_A(4, int(mid), 1)
                if cA6:
                    val_s += cA6 * prefix_A(6, int(mid), 1)
                if cG1:
                    val_s += cG1 * prefix_G(1, int(mid * 2), 2)
                if cG2:
                    val_s += cG2 * prefix_G(2, int(mid * 2), 2)
                if cG3:
                    val_s += cG3 * prefix_G(3, int(mid * 2), 2)
                jf = int(math.floor(mid / s_stride))
                if jf >= 1:
                    val_s += c0 * sum((Q(ps_f[j], j << (t * j)) for j in range(1, jf + 1)), Q())
                if val_s != 0:
                    if lo == 0.0:
                        return 10.0
                    rate += 1.0 / lo - 1.0 / hi
            return rate

        best_c = (10.0, None)
        for c0 in (-2, -1, 1, 2):
            a_fix = -c0 * u_A1
            for b_ in range(-4, 5):
                for c_ in range(-6, 4):
                    rodd = odd_rate_fn(c0, (a_fix, 0, b_, c_))
                    rtot = rho2 + rodd
                    if rtot < best_c[0]:
                        best_c = (rtot, (c0, (a_fix, 0, b_, c_), rodd))
        rtot_b, (c0_b, par_b, rodd_b) = best_c
        print(
            f"   f={str(f):20s} t={t} t-A={s_stride:5.3f}: rho_2={rho2:.4f} + rho_odd={rodd_b:.4f} "
            f"= {rtot_b:.4f} (vs 5/12=0.4167)"
        )
        if rtot_b < best_full[0]:
            best_full = (rtot_b, (f, t, rho2, rodd_b, c0_b, par_b))
    print(f"   Lowest full unbalanced rate found: {best_full[0]:.5f} (5/12 = {5/12:.5f}).")


def legendre_integral_exact(a, b, c, n, d_mid=0, pole="1+x"):
    if pole == "2-x":
        a, b = b, a
    an, bn, cn, dn = a * n, b * n, c * n, d_mid * n
    A_poly = [math.comb(an, i) * ((-1) ** (an - i)) for i in range(an + 1)]
    B_poly = [math.comb(bn, j) * ((-1) ** j) * (1 << (bn - j)) for j in range(bn + 1)]
    poly = poly_mul(A_poly, B_poly)
    if dn > 0:
        C_poly = [math.comb(dn, l) * ((-2) ** l) * (3 ** (dn - l)) for l in range(dn + 1)]
        poly = poly_mul(poly, C_poly)
    c_val = poly[cn] if cn < len(poly) else 0
    r_val = Q()
    for k, ck in enumerate(poly):
        if k != cn and ck:
            e = k - cn
            if e > 0:
                r_val -= Q(ck * ((1 << e) - 1), e)
            else:
                m = -e
                r_val -= Q(ck * ((1 << m) - 1), m << m)
    return c_val, r_val


def legendre_asymptotic(a, b, c):
    assert 0 <= c <= a + b
    A2 = c - a - b
    A1 = 2 * a + b - 3 * c
    A0 = 2 * c
    if c == 0:
        y_pos = 1.0 + a / (a + b)
        g_pos = ((y_pos - 1) ** a) * ((2 - y_pos) ** b)
        g_neg_abs = 2.0 ** b
        v2_c = float(b)
    elif c == a + b:
        y_pos = 2.0 * (a + b) / (a + 2 * b)
        g_pos = ((y_pos - 1) ** a) * ((2 - y_pos) ** b) / (y_pos ** c)
        g_neg_abs = 1.0
        v2_c = 0.0
    else:
        sq = math.sqrt(A1 * A1 - 4 * A2 * A0)
        r1 = (-A1 + sq) / (2 * A2)
        r2 = (-A1 - sq) / (2 * A2)
        y_pos = r1 if 1.0 < r1 < 2.0 else r2
        y_neg = r2 if y_pos == r1 else r1
        g_pos = ((y_pos - 1) ** a) * ((2 - y_pos) ** b) / (y_pos ** c)
        g_neg_abs = (abs(y_neg - 1) ** a) * (abs(2 - y_neg) ** b) / (abs(y_neg) ** c)
        v2_c = float(max(0, b - c))
    err_bits = log2(g_neg_abs / g_pos)
    odd_c_log = log(g_neg_abs) - v2_c * log(2)
    M_lcm = max(c, a + b - c)
    v2_tot = v2_c + c
    excess_2 = max(0.0, v2_tot - err_bits) * log(2)
    naive_rate = (M_lcm + odd_c_log + excess_2) / err_bits
    return err_bits, odd_c_log, M_lcm, naive_rate, v2_c


def measure_rational_ln2(rat_val):
    L0 = dec_ln2(80)
    getcontext().prec = 100
    diff0 = abs(L0 - Decimal(rat_val.numerator) / Decimal(rat_val.denominator))
    assert diff0 > 0
    est_N = max(20, int(-float(diff0.ln() / Decimal(2).ln())) + 40)
    prec = max(100, int(est_N * 0.35) + 80)
    L = dec_ln2(prec)
    getcontext().prec = prec + 20
    eps = abs(L - Decimal(rat_val.numerator) / Decimal(rat_val.denominator))
    N = max(1, int(-float(eps.ln() / Decimal(2).ln())) - 20)
    while Decimal(1 << (N + 1)) * eps * (N + 1) <= 1:
        N += 1
    while N > 1 and Decimal(1 << N) * eps * N > 1:
        N -= 1
    Y = rat_val * (1 << N)
    q = Y.denominator
    v2q = v2(q)
    err_bits = float((Decimal(1 << N) * eps).ln() / Decimal(2).ln())
    return N, log(q) / N, v2q, log(q >> v2q) / N, err_bits


def solve_linear_Q(M, rhs):
    n = len(M)
    A = [list(row) + [rhs[i]] for i, row in enumerate(M)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c]), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                m = A[i][c]
                A[i] = [a - m * b for a, b in zip(A[i], A[c])]
    return [A[i][n] for i in range(n)]


def nullspace_1d_Q(M, ncols):
    rows = [list(r) for r in M]
    pivcols, r_ = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r_, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[r_], rows[piv] = rows[piv], rows[r_]
        pv = rows[r_][c]
        rows[r_] = [x / pv for x in rows[r_]]
        for i in range(len(rows)):
            if i != r_ and rows[i][c]:
                m = rows[i][c]
                rows[i] = [a - m * b for a, b in zip(rows[i], rows[r_])]
        pivcols.append(c)
        r_ += 1
    free = [c for c in range(ncols) if c not in pivcols]
    if not free:
        return None
    f = free[-1]
    x = [Q(0)] * ncols
    x[f] = Q(1)
    for i, c in enumerate(pivcols):
        x[c] = -rows[i][f]
    return x


def type2_simultaneous_pade(f1_c, f2_c, n1, n2):
    degQ = n1 + n2
    ncols = degQ + 1
    M = []
    for k in range(degQ + 1, degQ + n1 + 1):
        M.append([f1_c[k - i] if 0 <= k - i < len(f1_c) else Q(0) for i in range(ncols)])
    for k in range(degQ + 1, degQ + n2 + 1):
        M.append([f2_c[k - i] if 0 <= k - i < len(f2_c) else Q(0) for i in range(ncols)])
    Qp = nullspace_1d_Q(M, ncols)
    if Qp is None:
        return None
    den = 1
    for c in Qp:
        den = lcm(den, c.denominator)
    Qp = [c * den for c in Qp]
    P1 = [sum((Qp[i] * f1_c[k - i] for i in range(min(k + 1, ncols))), Q()) for k in range(degQ + 1)]
    P2 = [sum((Qp[i] * f2_c[k - i] for i in range(min(k + 1, ncols))), Q()) for k in range(degQ + 1)]
    for k in range(degQ + 1, degQ + n1 + 1):
        assert sum((Qp[i] * f1_c[k - i] for i in range(ncols) if k - i >= 0), Q()) == 0
    for k in range(degQ + 1, degQ + n2 + 1):
        assert sum((Qp[i] * f2_c[k - i] for i in range(ncols) if k - i >= 0), Q()) == 0
    return Qp, P1, P2


def eval_poly_Q(p, z):
    r = Q(0)
    for c in reversed(p):
        r = r * z + c
    return r


def cheb_T(D):
    if D == 0:
        return [1]
    if D == 1:
        return [0, 1]
    a, b = [1], [0, 1]
    for _ in range(2, D + 1):
        c = [0] * (len(b) + 1)
        for i, v in enumerate(b):
            c[i + 1] += 2 * v
        for i, v in enumerate(a):
            c[i] -= v
        a, b = b, c
    return b


def poly_compose_2x_m1(p):
    res = [0]
    pw = [1]
    for c in p:
        if len(res) < len(pw):
            res.extend([0] * (len(pw) - len(res)))
        for i, v in enumerate(pw):
            res[i] += c * v
        npw = [0] * (len(pw) + 1)
        for i, v in enumerate(pw):
            npw[i] -= v
            npw[i + 1] += 2 * v
        pw = npw
    return res


def poly_div_linear(p, a, sigma):
    r = a * sigma
    d = len(p) - 1
    q = [0] * d
    rem = list(p)
    for i in range(d, 0, -1):
        q[i - 1] = rem[i]
        rem[i - 1] += rem[i] * r
    assert rem[0] == 0
    return [-c for c in q] if sigma == 1 else q


def cheb_pole_rational(poles, D, w_extra=None):
    T = poly_compose_2x_m1(cheb_T(D))
    Tvals = [poly_eval(T, a * sigma) for _, a, sigma in poles]
    min_T = min(abs(tv) for tv in Tvals)
    e = min_T.bit_length() - 1
    R_tot = [Q(0)] * D
    for (coef, a, sigma), tv in zip(poles, Tvals):
        num = list(T)
        num[0] -= tv
        q_num = poly_div_linear(num, a, sigma)
        for k in range(D):
            R_tot[k] += Q(coef * (q_num[k] << e), tv)
    Q_poly = [round(c) for c in R_tot]
    intQ = sum((Q(c, k + 1) for k, c in enumerate(Q_poly)), Q())
    # Error of int Q_D is <= ln 2 + H_D / 2 < log(D) + 1.
    # Choosing w = ceil(log2(N_est * (log(D) + 1))) ensures |2^N ln 2 - Y_N| < 1/N (and < 2^-8 for D >= 40).
    w = (int(math.ceil(math.log2(max(8.0, D * (math.log(D) + 1.0))))) + 2) if w_extra is None else w_extra
    N = e - w
    Y = -intQ / (1 << w)
    prec = max(100, int(N * 0.35) + 80)
    L = dec_ln2(prec)
    getcontext().prec = prec + 20
    err = abs(Decimal(1 << N) * L - Decimal(Y.numerator) / Decimal(Y.denominator))
    err_bits = float(err.ln() / Decimal(2).ln())
    win = max(0, int(-err_bits) - 8) if err_bits <= -8.0 else None
    q = Y.denominator
    v2q = v2(q)
    return N, e, w, log(q) / N, log(q >> v2q) / N, v2q, err_bits, win


def section_3_pade_and_integrals():
    print("\n== SECTION 3: Pade, Asymmetric Legendre/Beta, Simultaneous Pade & Chebyshev-Pole")

    print("\n   (3A) Classical Beukers / Alladi-Robinson Pade (1, 1, 1):")
    eb, oc, ml, nr, v2c = legendre_asymptotic(1, 1, 1)
    print(f"   Asymptotic (no prime canc.): err_bits/n={eb:.5f}, odd_c/n={oc:.5f}, lcm/n={ml}, rate={nr:.5f}")
    for n in (13, 26, 40, 60):
        cn, rn = legendre_integral_exact(1, 1, 1, n)
        cn2, rn2 = legendre_integral_exact(1, 1, 1, n, pole="2-x")
        assert cn == cn2 and rn == rn2
        rat = rn / cn
        N, rate, v2q, rate_odd, err_bits = measure_rational_ln2(rat)
        print(f"   n={n:2d}: N={N:3d} log(q)/N={rate:.5f} (v2={v2q}) log2(err)={err_bits:5.1f}")

    print("\n   (3B) Asymmetric Legendre/Beta integrals I_n(a, b, c):")
    for (a, b, c) in [(1, 2, 0), (1, 3, 1), (2, 3, 1), (2, 5, 2)]:
        c1, r1 = legendre_integral_exact(a, b, c, 5)
        c2, r2 = legendre_integral_exact(b, a, a + b - c, 5)
        assert Q(c1, 1) == Q(c2, 1) * (Q(2) ** ((b - c) * 5))
        assert r1 == r2 * (Q(2) ** ((b - c) * 5))
    print("   Verified Mobius symmetry I_n(a,b,c) = 2^((b-c)n) I_n(b,a,a+b-c) identically.")

    to_test = [
        (1, 1, 1), (1, 2, 0), (1, 2, 1), (2, 3, 1), (2, 3, 2), (3, 4, 2),
        (3, 5, 2), (1, 3, 1), (2, 5, 2), (3, 7, 3), (4, 5, 2), (5, 5, 3),
    ]
    exact_leg = []
    for a, b, c in to_test:
        eb, oc, ml, nr, v2c = legendre_asymptotic(a, b, c)
        n = max(8, min(28, 120 // (a + b)))
        cn, rn = legendre_integral_exact(a, b, c, n)
        if cn == 0:
            continue
        N, rate, v2q, _, _ = measure_rational_ln2(rn / cn)
        exact_leg.append((rate, a, b, c, n, N, nr, eb, v2c, v2q))
    exact_leg.sort()
    for rate, a, b, c, n, N, nr, eb, v2c, v2q in exact_leg[:8]:
        print(f"   ({a},{b},{c}) n={n:2d} N={N:3d}: exact_rate={rate:.5f} (naive={nr:.5f}, v2(c)/n={v2c:.1f}, v2={v2q})")

    print("\n   (3C) Simultaneous Type II Pade approximants at z = 1/2:")
    maxK = 80
    c_log1mz = [Q(0)] + [Q(-1, k) for k in range(1, maxK)]
    c_log1pz = [Q(0)] + [Q((-1) ** (k - 1), k) for k in range(1, maxK)]
    c_log1mz2 = [Q(0)] * maxK
    for k in range(1, maxK // 2):
        c_log1mz2[2 * k] = Q(-1, k)
    c_log1pz3 = [Q(0)] * maxK
    for k in range(1, maxK // 3):
        c_log1pz3[3 * k] = Q((-1) ** (k - 1), k)

    for n1, n2 in [(6, 6), (8, 8), (10, 10), (10, 5)]:
        Q1, P1a, _ = type2_simultaneous_pade(c_log1mz, c_log1mz2, n1, n2)
        r1 = -eval_poly_Q(P1a, Q(1, 2)) / eval_poly_Q(Q1, Q(1, 2))
        N, rate, v2q, _, _ = measure_rational_ln2(r1)
        print(f"   Pair (log(1-z), log(1-z^2)) ({n1},{n2}): N={N:3d} log(q)/N={rate:.5f} v2={v2q}")

    for n1, n2 in [(8, 8), (10, 10), (12, 8)]:
        res = type2_simultaneous_pade(c_log1mz2, c_log1pz3, n1, n2)
        if res is not None:
            Qp, P1, P2 = res
            Qv = eval_poly_Q(Qp, Q(1, 2))
            if Qv != 0:
                rat = (-2 * eval_poly_Q(P1, Q(1, 2)) + eval_poly_Q(P2, Q(1, 2))) / Qv
                N, rate, v2q, _, _ = measure_rational_ln2(rat)
                print(f"   Pair (log(1-z^2), log(1+z^3)) ({n1},{n2}): N={N:3d} log(q)/N={rate:.5f} v2={v2q}")

    print("\n   (3D) Rounded Chebyshev-Pole Integrals (explicit, ln2-free, BEATING 5/12 = 0.41667!):")
    lim1 = log(2) / (2 * log(1 + math.sqrt(2)))
    print(f"   Family 3D-1: Single pole 1/(1+x), limit = {lim1:.6f} (< 5/12 = {5/12:.6f}):")
    for D in (80, 120, 240, 400):
        N, e, w, rate, rodd, v2q, err_bits, win = cheb_pole_rational([(1, 1, -1)], D)
        assert err_bits < -8.0
        if D >= 240:
            assert rate < 5 / 12
        print(f"     D={D:3d} N={N:4d} w={w:2d}: log(q)/N={rate:.5f} (odd={rodd:.5f}, v2={v2q:2d}) log2(err)={err_bits:6.2f} win={win}")

    lim2 = log(2) / (2 * log(2 + math.sqrt(3)))
    print(f"   Family 3D-2: Two-stride 2/(4-x) + 1/(8+x), limit = {lim2:.6f}:")
    for D in (50, 80, 120, 160):
        N, e, w, rate, rodd, v2q, err_bits, win = cheb_pole_rational([(2, 4, 1), (1, 8, -1)], D)
        assert err_bits < -8.0 and rate < 5 / 12
        print(f"     D={D:3d} N={N:3d} w={w:2d}: log(q)/N={rate:.5f} (odd={rodd:.5f}, v2={v2q:2d}) log2(err)={err_bits:6.2f} win={win}")

    lim3 = 1.0 / log2(17 + 12 * math.sqrt(2))
    print(f"   Family 3D-3: Telescoping M=8 (sum_{{a=9}}^{{16}} 1/(a-x)), limit = {lim3:.6f}:")
    poles_M8 = [(1, a, 1) for a in range(9, 17)]
    for D in (50, 80, 120):
        N, e, w, rate, rodd, v2q, err_bits, win = cheb_pole_rational(poles_M8, D)
        assert err_bits < -8.0 and rate < 5 / 12
        print(f"     D={D:3d} N={N:3d} w={w:2d}: log(q)/N={rate:.5f} (odd={rodd:.5f}, v2={v2q:2d}) log2(err)={err_bits:6.2f} win={win}")

    print("\n   Forward coverage alpha=1/2 (precision window >= N/2) for Family 3D-2 vs corrected-strides (0.74609):")
    for D in (60, 120, 180):
        T_est = int(D * log2(7 + 4 * math.sqrt(3)))
        w_lin = T_est // 3 + 12
        N, e, w, rate, rodd, v2q, err_bits, win = cheb_pole_rational([(2, 4, 1), (1, 8, -1)], D, w_extra=w_lin)
        print(f"     D={D:3d} N={N:3d} win={win} (win/N={win/N:.3f}): log(q)/N={rate:.5f} (odd={rodd:.5f}, 2-adic={v2q*log(2)/N:.5f})")


def main():
    section_1_balanced()
    section_2_unbalanced()
    section_3_pade_and_integrals()
    print("\nAll Phase 16 non-flat approximant checks passed.")


if __name__ == "__main__":
    main()
