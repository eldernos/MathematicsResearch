"""Exact checks for Phase 23, Track A, sub-tracks A3 and A4.

Companion to notes/phase23/rational-scalings-and-signed-special.md.  Standard library only;
all arithmetic is exact (int / Fraction).  Run:

    python -B scripts/phase23_rational_signed.py

Sections
--------
R1  Signed automaton laws of (a/d)E_2 and (a/d)E_2^3 for every odd d <= 200 and every
    numerator class (a mod d, sign a): negation symmetry of the nonzero atoms, the zero-split
    parity formula, f_0 = 1/2 + sgn(a) Xi/(6t) (Euler) and 1/2 + sgn(a) Xi3/(2L) (cube),
    base-2 simple normality iff ord_d(2) odd, the half-period test, exact D_infinity.
R2  Exceptional primes.  Prime reduction of the half-period test; no 2-exceptional prime
    for E (p <= 20000) or for E^3 (p <= 3000); the base-10 example (a/113)E_10 (even order
    112 = 0 mod 4, zeros {29, 56, 83, 112}, complement-symmetric law); the base-3 cube-exceptional prime 5 (unbalanced).
R3  Other radices b = 3..10: parity formula in bases 3, 5, 10; no simply normal law.
R4  Rational scalings of Theta_3(1/b): exact laws, the mod-3 theorem, odd-order obstruction,
    exact list of base-2 simply normal denominators d <= 200, D_infinity, uniformity of the
    base-b lists over all numerators and signs; Proposition 5.4 word count for E_2 (4L - 4).
R5  Derivative scalings (a/d)D^jE_2, (a/d)D^jE_2^3, j = 1, 2: symmetry and simple normality;
    content 3 of D^jE^3 (j <= 6); Corollary 6.2 (3 || d); even denominators with b odd: term
    period 2 lcm(t, d) of D^jE_b (lcm(2t, d) fails) and Theorem 1.1 symmetry.
R6  (a/2)E_b^2 in odd base b: E^2 = E(q^2) mod 2, atom-1/2 density 2/3, certified digits.
S1  Classification of everywhere-nonnegative pairs (r, M), M <= 60, with explicit negative
    witnesses for every signed pair.
S2  The universal sign-flip involution (-1 a square mod M'), transport identity.
S3  Dominant-part flips for cyclic moduli without a square root of -1.
S4  Im(1*chi) mod 5 = a_{2,5}; finite sign statistics.
"""

import sys
import time
from fractions import Fraction as Fr
from math import gcd, isqrt

CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        print("FAILED:", msg)
        sys.exit(1)


def header(s):
    print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78)


def lcm(a, b):
    return a // gcd(a, b) * b


def order_mod(b, d):
    if d == 1:
        return 1
    x, k = b % d, 1
    while x != 1:
        x = x * b % d
        k += 1
    return k


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


PRIMES = primes_upto(20000)


def order_prime(b, p):
    n = p - 1
    t, m, fac, f = n, n, [], 2
    while f * f <= m:
        if m % f == 0:
            fac.append(f)
            while m % f == 0:
                m //= f
        f += 1
    if m > 1:
        fac.append(m)
    for f in fac:
        while t % f == 0 and pow(b, t // f, p) == 1:
            t //= f
    return t


def pent(j):
    return j * (3 * j - 1) // 2


# ====================================================================== automaton laws
# A law is (t, g, W, cnt, zp, zm): cnt[rho] = total integer weight of run classes whose head
# residue is = rho (mod g); W = sum(cnt); zp, zm = weight of zero-head classes whose run sign is
# +1 / -1 (for a > 0).  Masses: a nonzero atom c in Z/d has mass sm[c mod g]/Den, where sm is the
# x b-orbit smear of cnt (times t), and the zero atom splits as (zp*t, zm*t)/Den, Den = W*t*(d/g).

def law_from_entries(b, d, t, entries, g):
    cnt = [0] * g
    zp = zm = 0
    for (w, s, r) in entries:
        rr = r % g
        cnt[rr] += w
        if rr == 0:
            if s > 0:
                zp += w
            else:
                zm += w
    return (t, g, sum(cnt), cnt, zp, zm)


def smear(b, law):
    t, g, W, cnt, zp, zm = law
    sm = [0] * g
    seen = [False] * g
    for r in range(g):
        if seen[r]:
            continue
        orb = []
        x = r
        while not seen[x]:
            seen[x] = True
            orb.append(x)
            x = x * b % g
        tot = sum(cnt[y] for y in orb) * (t // len(orb))
        for y in orb:
            sm[y] = tot
    return sm


def euler_period(b, d, j=0):
    """Term period of tm(i) = (-1)^i P(i)^j q^{P(i)} mod d: 2t for j = 0, 2 lcm(t, d) for j >= 1.

    For even Lam, P(i + Lam) - P(i) = (Lam/2)(6i + 3Lam - 1) has 2-adic valuation v_2(Lam) - 1,
    so P(i)^j is Lam-periodic mod d only when 2d | Lam.  lcm(2t, d) is therefore NOT a period
    when d is even with v_2(d) > v_2(t) (e.g. b = 3, d = 2); 2 lcm(t, d) is a period for all d."""
    t = order_mod(b, d)
    return 2 * t if j == 0 else 2 * lcm(t, d)


def euler_law(b, d, j=0, mult=1, period=None):
    """(a/d) D^j E_b, insertions at generalized pentagonal numbers P(i), coefficient (-1)^i P(i)^j.

    mult > 1 enumerates mult consecutive term periods (used to test period-independence);
    period overrides the class period (used only to exhibit the wrong period lcm(2t, d))."""
    t = order_mod(b, d)
    q = pow(b, -1, d)
    Lam = mult * (euler_period(b, d, j) if period is None else period)
    tm = {}
    for i in range(-Lam - 1, Lam + 2):
        P = pent(i)
        v = pow(P, j, d) * pow(q, P % t, d) % d
        tm[i] = (-v) % d if i & 1 else v
    A = tm[0]
    entries = []
    Ams, As = [], []
    for k in range(1, Lam + 1):
        Am = (A + tm[k]) % d
        A = (Am + tm[-k]) % d
        Ams.append(Am)
        As.append(A)
        entries.append((1, 1 if k % 2 == 0 else -1, Am))
        entries.append((2, -1 if k % 2 == 0 else 1, A))
    sigma = sum(tm[i] for i in range(Lam)) % d
    g = gcd(2 * sigma, d)
    return law_from_entries(b, d, t, entries, g), Ams, As, sigma, Lam


def cube_law(b, d, j=0):
    """(a/d) D^j E_b^3, insertions at T_i with coefficient (-1)^i (2i+1) T_i^j."""
    t = order_mod(b, d)
    q = pow(b, -1, d)
    Lam = 2 * lcm(t, d)
    s = 0
    bp = 1          # q^{T_i}
    inc = 1         # q^{i+1}
    seq = []
    for i in range(Lam):
        Ti = i * (i + 1) // 2
        term = (2 * i + 1) * bp % d
        if j:
            term = term * pow(Ti, j, d) % d
        if i & 1:
            term = -term
        s = (s + term) % d
        seq.append(s)
        inc = inc * q % d
        bp = bp * inc % d
    g = gcd(s, d)
    entries = [(1, 1 if (k + 1) % 2 == 0 else -1, seq[k]) for k in range(Lam)]
    return law_from_entries(b, d, t, entries, g), seq, s, Lam


def theta_law(b, d):
    """(a/d) Theta_3(1/b) = (a/d)(1 + 2 sum b^{-k^2}); every run sign is +1."""
    t = order_mod(b, d)
    q = pow(b, -1, d)
    B = 1
    seq = []
    for k in range(1, t + 1):
        B = (B + 2 * pow(q, (k * k) % t, d)) % d
        seq.append(B)
    G = sum(pow(q, (i * i) % t, d) for i in range(t)) % d
    g = gcd(2 * G, d)
    entries = [(1, 1, x) for x in seq]
    return law_from_entries(b, d, t, entries, g), seq, G


def masses(b, d, law):
    """integer numerators over Den: list m[c] for c = 1..d-1, zero split (zp*t, zm*t), Den."""
    t, g, W, cnt, zp, zm = law
    sm = smear(b, law)
    Den = W * t * (d // g)
    return sm, Den


def word_of(c, d, b, L):
    out = []
    x = c
    for _ in range(L):
        x *= b
        out.append(x // d)
        x %= d
    return tuple(out)


def word_law(b, d, law, a, L):
    t, g, W, cnt, zp, zm = law
    sm, Den = masses(b, d, law)
    f = {}
    for c in range(1, d):
        w = word_of(a * c % d, d, b, L)
        f[w] = f.get(w, 0) + sm[c % g]
    zw, tw = (0,) * L, (b - 1,) * L
    pz, mz = (zp * t, zm * t) if a > 0 else (zm * t, zp * t)
    f[zw] = f.get(zw, 0) + pz
    f[tw] = f.get(tw, 0) + mz
    return {w: Fr(v, Den) for w, v in f.items() if v}


def digit_law(b, d, law, a):
    f = word_law(b, d, law, a, 1)
    return [f.get((e,), Fr(0)) for e in range(b)]


def d_infinity(b, d, law, a):
    """exact lim D_N for half-open intervals: atoms c/d (c != 0), zero atom split 0+ / 1-."""
    t, g, W, cnt, zp, zm = law
    sm, Den = masses(b, d, law)
    m = [0] * (d + 1)
    for c in range(1, d):
        m[(a * c) % d] += sm[c % g]
    pz, mz = (zp * t, zm * t) if a > 0 else (zm * t, zp * t)
    m[0] += pz
    m[d] += mz
    # D^+ = max_{i<=j} sum_{c=i}^{j} m_c/Den - (j-i)/d  (Kadane, scaled by Den*d)
    best = cur = None
    for c in range(d + 1):
        v = d * m[c]
        cur = v if cur is None else max(v, cur - Den + v)
        best = cur if best is None else max(best, cur)
    Dp = Fr(best, Den * d)
    # D^- = 1/d + max(0, max subarray over c=1..d-1 of (1/d - m_c/Den))
    best2, cur2 = 0, 0
    for c in range(1, d):
        v = Den - d * m[c]
        cur2 = max(v, cur2 + v)
        best2 = max(best2, cur2)
    Dm = Fr(Den + best2, Den * d)
    return max(Dp, Dm), Dp, Dm


def unit_coset_reps(b, d):
    seen = set()
    reps = []
    for a in range(1, d):
        if gcd(a, d) != 1 or a in seen:
            continue
        reps.append(a)
        x = a
        while x not in seen:
            seen.add(x)
            x = x * b % d
    return reps


# ====================================================================== R1
def section_r1():
    header("R1  (a/d)E_2 and (a/d)E_2^3, all odd d <= 200: exact base-2 laws")
    nlaw = {"E": 0, "E3": 0}
    sn_den = {"E": [], "E3": []}
    xi_tab = {}
    maxxi = {"E": 0, "E3": 0}
    for kind in ("E", "E3"):
        for d in range(3, 201, 2):
            if kind == "E":
                law, Ams, As, sigma, Lam = euler_law(2, d)
            else:
                law, seq, sigma, Lam = cube_law(2, d)
            t, g, W, cnt, zp, zm = law
            check(sigma % d == 0 and g == d, "period sum vanishes mod d (%s, d=%d)" % (kind, d))
            sm, Den = masses(2, d, law)
            # negation symmetry of the nonzero atoms
            for c in range(1, d):
                check(sm[c % g] == sm[(-c) % g], "negation symmetry %s d=%d" % (kind, d))
            # parity formula for the zero split
            if kind == "E":
                h = t // 2
                if t % 2 == 1:
                    check(zp == zm, "odd order: balanced split")
                    S = 0
                else:
                    zk = [1 if Ams[k - 1] % d == 0 else 0 for k in range(1, t + 1)]  # k = 1..t
                    S = sum((1 if k % 2 == 0 else -1) * zk[k - 1] for k in range(1, t + 1))
                    check(zp - zm == 2 * S, "zp - zm = 2 Xi (E, d=%d)" % d)
                    # + runs cancel in pairs
                    plus = sum((1 if k % 2 == 1 else -1) * (1 if As[k - 1] % d == 0 else 0)
                               for k in range(1, 2 * t + 1))
                    check(plus == 0, "+ runs contribute 0")
                    iota = pow(2, h, d)
                    dm = gcd(d, iota + 1)
                    dp = d // dm
                    Ah = Ams[h - 1]
                    check(Ah % dp == 0, "A^-(h) = 0 mod d_+")
                    check((S % 2 == 1) == (Ah % dm != 0), "Xi odd iff A^-(h) != 0 mod d_-")
                    check(Ah % dm != 0, "half-period test holds (E, d=%d)" % d)
                    xi_tab[("E", d)] = (t, S)
                    maxxi["E"] = max(maxxi["E"], abs(S))
            else:
                Lc = Lam // 2
                if t % 2 == 1:
                    check(zp == zm, "odd order: balanced split (cube)")
                else:
                    S = sum((1 if (k + 1) % 2 == 0 else -1) * (1 if seq[k] % d == 0 else 0)
                            for k in range(Lc))
                    check(zp - zm == 2 * S, "zp - zm = 2 Xi3 (d=%d)" % d)
                    iota = pow(2, t // 2, d)
                    dm = gcd(d, iota + 1)
                    v = seq[Lc // 2 - 1]
                    check(v % (d // dm) == 0, "V(L/2-1) = 0 mod d_+")
                    check((S % 2 == 1) == (v % dm != 0), "Xi3 odd iff V(L/2-1) != 0 mod d_-")
                    check(v % dm != 0, "half-period test holds (cube, d=%d)" % d)
                    xi_tab[("E3", d)] = (Lc, S)
                    maxxi["E3"] = max(maxxi["E3"], abs(S))
            # f_0 for every (a mod d, sign a); x2 invariance -> coset representatives suffice
            nz = Den - (zp + zm) * t
            check(nz % 2 == 0, "nonzero mass splits evenly")
            good = 0
            for a in unit_coset_reps(2, d):
                f0nz = sum(sm[c % g] for c in range(1, d) if 2 * (a * c % d) < d)
                check(2 * f0nz == nz, "symmetric atoms give half of the nonzero mass to digit 0")
                for sa in (1, -1):
                    f0 = Fr(f0nz + (zp if sa > 0 else zm) * t, Den)
                    if t % 2 == 0:
                        X = xi_tab[(kind, d)]
                        pred = Fr(1, 2) + sa * (Fr(X[1], 6 * t) if kind == "E" else Fr(X[1], 2 * X[0]))
                        check(f0 == pred, "closed form for f_0 (%s d=%d)" % (kind, d))
                    if f0 == Fr(1, 2):
                        good += 1
            nreps = len(unit_coset_reps(2, d))
            nlaw[kind] += 2 * sum(1 for a in range(1, d) if gcd(a, d) == 1)
            if good:
                check(good == 2 * nreps and t % 2 == 1, "simply normal iff odd order (%s d=%d)" % (kind, d))
                sn_den[kind].append(d)
            else:
                check(t % 2 == 0, "odd order always simply normal")
    print("laws (a mod d, sign a) examined: E_2: %d, E_2^3: %d" % (nlaw["E"], nlaw["E3"]))
    for kind in ("E", "E3"):
        print("  %s: base-2 simply normal exactly for the %d odd-order d: %s"
              % (kind, len(sn_den[kind]), sn_den[kind]))
    check(sn_den["E"] == sn_den["E3"] == [7, 23, 31, 47, 49, 71, 73, 79, 89, 103, 127, 151, 161,
                                          167, 191, 199], "odd-order list d <= 200")
    check(nlaw["E"] == 2 * sum(sum(1 for a in range(1, d) if gcd(a, d) == 1) for d in range(3, 201, 2)),
          "law count")
    print("  every even-order d passes the half-period test; max |Xi| = %d (E), %d (E^3)"
          % (maxxi["E"], maxxi["E3"]))
    print("\n  sample closed forms f_0((a/d)z) = 1/2 + sgn(a) Xi/(6t) [E], 1/2 + sgn(a) Xi3/(2L) [E^3], a > 0:")
    sample = [("E", 3), ("E", 5), ("E", 13), ("E", 21), ("E", 37), ("E", 67), ("E3", 3), ("E3", 5),
              ("E3", 35)]
    want = {("E", 3): (1, Fr(7, 12)), ("E", 5): (1, Fr(13, 24)), ("E", 13): (-1, Fr(35, 72)),
            ("E", 21): (1, Fr(19, 36)), ("E", 37): (1, Fr(109, 216)), ("E", 67): (-1, Fr(197, 396)),
            ("E3", 35): (-3, Fr(139, 280))}
    for kind, d in sample:
        T, S = xi_tab[(kind, d)]
        f0 = Fr(1, 2) + (Fr(S, 6 * T) if kind == "E" else Fr(S, 2 * T))
        if (kind, d) in want:
            check((S, f0) == want[(kind, d)], "sample value %s %d" % (kind, d))
        print("    %-3s d=%3d  %s=%3d  Xi=%3d  f_0=%s" % (kind, d, "t" if kind == "E" else "L", T, S, f0))
    # exact D_infinity
    print("\n  exact D_infinity (a = 1):")
    for kind, d in (("E", 3), ("E", 5), ("E", 7), ("E", 13), ("E", 23), ("E3", 3), ("E3", 7)):
        law = euler_law(2, d)[0] if kind == "E" else cube_law(2, d)[0]
        D, Dp, Dm = d_infinity(2, d, law, 1)
        if (kind, d) == ("E", 3):
            check(D == Fr(1, 2), "D_inf((1/3)E_2) = 1/2")
        print("    (1/%d)%s_2: D_inf = %s  (D+ = %s, D- = %s)" % (d, "E" if kind == "E" else "E^3", D, Dp, Dm))
    return xi_tab


# ====================================================================== R2
def euler_half(b, p, t):
    """A^-(t/2) mod p, by incremental exponents."""
    h = t // 2
    q = pow(b, -1, p)
    j = 1 - h
    e = pent(j) % t
    cur = pow(q, e, p)
    step = pow(q, (3 * j + 1) % t, p)   # q^{P(j+1)-P(j)} = q^{3j+1}
    q3 = pow(q, 3, p)
    s = 0
    for jj in range(1 - h, h + 1):
        s += -cur if jj & 1 else cur
        cur = cur * step % p
        step = step * q3 % p
    return s % p


def cube_half(b, p, t, n):
    """V(n) mod p via arithmetic-progression sums over residues mod 2t."""
    q = pow(b, -1, p)
    T2 = 2 * t
    s = 0
    qt = 1
    inc = 1
    for r in range(min(T2, n + 1)):
        M = (n - r) // T2
        S = (M + 1) * (2 * r + 1) + T2 * M * (M + 1)
        v = qt * S
        s += -v if r & 1 else v
        inc = inc * q % p
        qt = qt * inc % p
    return s % p


def section_r2():
    header("R2  Exceptional primes and the prime reduction of the half-period test")
    # prime reduction check on composite d <= 200 (both series)
    nred = 0
    for d in range(3, 201, 2):
        t = order_mod(2, d)
        if t % 2:
            continue
        h = t // 2
        dm = gcd(d, pow(2, h, d) + 1)
        _, Ams, _, _, _ = euler_law(2, d)
        law3, seq, _, Lam = cube_law(2, d)
        L = Lam // 2
        for p in PRIMES:
            if p > dm:
                break
            if dm % p:
                continue
            tp = order_mod(2, p)
            check(tp % 2 == 0 and (2 * h // tp) % 2 == 1, "p | d_- has even order, same 2-part")
            mprime = 2 * h // tp
            check(Ams[h - 1] % p == ((-1) ** ((mprime - 1) // 2) * euler_half(2, p, tp)) % p,
                  "A^-(h) = +- A_p^-(t_p/2) mod p")
            Lp = tp * p
            mm = L // Lp
            check(L % Lp == 0 and mm % 2 == 1, "L = L_p * odd")
            check(seq[L // 2 - 1] % p == ((-1) ** ((mm - 1) // 2) * cube_half(2, p, tp, Lp // 2 - 1)) % p,
                  "V(L/2-1) = +- V_p(L_p/2-1) mod p")
            nred += 1
    print("prime reduction verified for %d pairs (d, p | d_-), odd d <= 200" % nred)
    # direct cube_half vs automaton for small primes
    for p in (3, 5, 11, 13, 19, 29):
        tp = order_mod(2, p)
        _, seq, _, Lam = cube_law(2, p)
        check(seq[Lam // 4 - 1] % p == cube_half(2, p, tp, Lam // 4 - 1), "cube_half formula")
    # exceptional prime searches
    t0 = time.time()
    nE = 0
    excE = []
    for p in PRIMES:
        if p < 3:
            continue
        t = order_prime(2, p)
        if t % 2:
            continue
        nE += 1
        if euler_half(2, p, t) == 0:
            excE.append(p)
    check(excE == [], "no 2-exceptional prime for E up to 20000")
    nC = 0
    excC = []
    for p in PRIMES:
        if p < 3 or p > 3000:
            continue
        t = order_prime(2, p)
        if t % 2:
            continue
        nC += 1
        if cube_half(2, p, t, p * t // 2 - 1) == 0:
            excC.append(p)
    check(excC == [], "no 2-exceptional prime for E^3 up to 3000")
    print("base 2: %d primes p <= 20000 with ord_p(2) even, none exceptional for E;" % nE)
    print("        %d primes p <= 3000 with ord_p(2) even, none exceptional for E^3  (%.1fs)" % (nC, time.time() - t0))
    check((nE, nC) == (1615, 303), "prime counts")
    # base 10 and base 3
    exc10 = [p for p in PRIMES if 3 <= p <= 1000 and p != 5 and order_prime(10, p) % 2 == 0
             and euler_half(10, p, order_prime(10, p)) == 0]
    exc3c = [p for p in PRIMES if 5 <= p <= 300 and order_prime(3, p) % 2 == 0
             and cube_half(3, p, order_prime(3, p), p * order_prime(3, p) // 2 - 1) == 0]
    check(exc10 == [113], "base-10 E-exceptional primes <= 1000")
    check(exc3c == [5], "base-3 cube-exceptional primes <= 300")
    print("base 10: E-exceptional primes p <= 1000: %s;  base 3: cube-exceptional p <= 300: %s" % (exc10, exc3c))
    law, Ams, As, sigma, Lam = euler_law(10, 113)
    t, g, W, cnt, zp, zm = law
    check(t == 112 and zp == zm, "(a/113)E_10: even order 112, balanced zero split")
    for L in (1, 2):
        for a in (1, 3, -1):
            f = word_law(10, 113, law, a, L)
            for w, v in f.items():
                check(f.get(tuple(9 - x for x in w), 0) == v, "complement symmetry (a/113)E_10")
    f1 = digit_law(10, 113, law, 1)
    check(f1[0] == Fr(353, 3136) and f1[1] == Fr(297, 3136) and f1[3] == Fr(81, 784), "(1/113)E_10 digits")
    sm, Den = masses(10, 113, law)
    # t = 112 = 0 mod 4: balance comes from odd-indexed zeros, not from 1 + (-1)^h z_h = 0
    z113 = [k for k in range(1, t + 1) if Ams[k - 1] % 113 == 0]
    check(t % 4 == 0 and z113 == [29, 56, 83, 112]
          and sum((-1) ** k for k in z113) == 0, "p = 113: t = 0 mod 4, A^- zeros {29, 56, 83, 112}, Xi = 0")
    print("(a/113)E_10: t = 112, w_0^+ = w_0^- = %s; law complement-symmetric (L = 1, 2);"
          % Fr(zp * t, Den))
    print("   t = 112 = 0 mod 4; zeros of A^-(k) mod 113, 1 <= k <= 112: %s, so Xi_10(113) = 0" % z113)
    print("   digits f_0..f_9 (a=1): %s" % " ".join(str(x) for x in f1))
    law3 = cube_law(3, 5)[0]
    t3, g3, W3, cnt3, zp3, zm3 = law3
    sm3, Den3 = masses(3, 5, law3)
    check((Fr(zp3 * t3, Den3), Fr(zm3 * t3, Den3)) == (Fr(3, 10), Fr(1, 10)), "(a/5)E_3^3 split")
    print("(a/5)E_3^3: cube-exceptional prime but w_0^+ = 3/10, w_0^- = 1/10 (unbalanced); law %s"
          % [str(x) for x in digit_law(3, 5, law3, 1)])


# ====================================================================== R3
def section_r3():
    header("R3  Radices b = 3..10: parity formula and the search for simple normality")
    nlaws = 0
    for b in (3, 5, 10):
        for d in range(3, 121, 2):
            if gcd(b, d) != 1:
                continue
            law, Ams, As, sigma, Lam = euler_law(b, d)
            t, g, W, cnt, zp, zm = law
            check(g == d, "sigma = 0 mod d (b=%d,d=%d)" % (b, d))
            if t % 2 == 0:
                S = sum((1 if k % 2 == 0 else -1) * (1 if Ams[k - 1] % d == 0 else 0) for k in range(1, t + 1))
                check(zp - zm == 2 * S, "parity formula b=%d d=%d" % (b, d))
                dm = gcd(d, pow(b, t // 2, d) + 1)
                check((S % 2 == 1) == (Ams[t // 2 - 1] % dm != 0), "Xi parity b=%d d=%d" % (b, d))
            else:
                check(zp == zm, "odd order balanced b=%d d=%d" % (b, d))
    found = []
    for b in range(3, 11):
        for d in range(2, 101):
            if gcd(b, d) != 1:
                continue
            for kind in ("E", "E3"):
                if kind == "E3" and d > 50:
                    continue
                law = euler_law(b, d)[0] if kind == "E" else cube_law(b, d)[0]
                t, g, W, cnt, zp, zm = law
                sm, Den = masses(b, d, law)
                for c in range(1, d):
                    check(sm[c % g] == sm[(-c) % g], "negation symmetry b=%d d=%d %s" % (b, d, kind))
                reps = [a for a in range(1, d) if gcd(a, d) == 1]
                nlaws += 2 * len(reps)
                if zp != zm:
                    continue        # f_0 - f_{b-1} = +-(w0+ - w0-) != 0
                for a in unit_coset_reps(b, d):
                    f = digit_law(b, d, law, a)
                    if all(x == Fr(1, b) for x in f):
                        found.append((kind, b, d, a))
    check(found == [], "no simply normal rational scaling in bases 3..10")
    print("parity formula verified in bases 3, 5, 10 for odd d < 121 (E)")
    print("bases 3..10: %d laws ((a mod d, sign), E: d <= 100, E^3: d <= 50); none simply normal in base b"
          % nlaws)


# ====================================================================== R4
def section_r4():
    header("R4  Rational scalings (a/d)Theta_3(1/b)")
    sn = []
    for d in range(3, 201, 2):
        law, seq, G = theta_law(2, d)
        t, g, W, cnt, zp, zm = law
        sm, Den = masses(2, d, law)
        for c in range(1, d):
            check(sm[c % g] == sm[(-c) % g], "theta negation symmetry d=%d" % d)
        w0 = Fr(zp * t, Den)
        check(zm == 0, "theta: all run signs positive")
        if t % 2 == 1:
            check(seq[(t - 1) // 2 - 1 if (t - 1) // 2 >= 1 else t - 1] % g == 0 or (t - 1) // 2 == 0,
                  "odd order: fixed point is a zero")
            check(w0 > 0, "odd order => zero atom (d=%d)" % d)
        if g == 1:
            check(w0 == Fr(1, d), "g = 1 => w0 = 1/d")
        if d % 3 == 0:
            check(G % 3 == 0 and all(x % 3 != 0 for x in seq), "mod-3 theorem d=%d" % d)
            check(w0 == 0, "3 | d => no zero atom")
        for a in (1, -1):
            f = digit_law(2, d, law, a)
            check(f[0] == Fr(1, 2) + a * w0 / 2, "theta f_0 = 1/2 + sgn(a) w0/2")
        if w0 == 0:
            sn.append(d)
    want = [3, 9, 11, 15, 19, 21, 27, 33, 39, 43, 45, 51, 55, 57, 59, 63, 69, 75, 77, 81, 87, 93, 95,
            99, 105, 107, 111, 117, 121, 123, 129, 133, 135, 139, 141, 143, 147, 153, 159, 163, 165,
            171, 177, 179, 183, 187, 189, 195]
    check(sn == want, "list of base-2 simply normal theta scalings")
    non3 = [d for d in sn if d % 3]
    print("(a/d)Theta_3(1/2) simply normal in base 2 (all a coprime to d) for %d odd d <= 200:" % len(sn))
    print("   all 33 odd multiples of 3, and %s" % non3)
    check(len([d for d in sn if d % 3 == 0]) == 33, "33 multiples of 3")
    # p = 3 mod 8 primes
    p38 = [p for p in PRIMES if 3 <= p <= 200 and p % 8 == 3]
    p38sn = [p for p in p38 if p in sn]
    print("   primes p = 3 mod 8 below 200: %s; simply normal: %s" % (p38, p38sn))
    for p in p38:
        t = order_mod(2, p)
        check(t % 4 == 2, "p = 3 mod 8 => ord_p(2) = 2 mod 4")
    # exact laws and D_inf
    print("   exact laws (a = 1):")
    for d in (3, 5, 7, 9, 11, 13, 15):
        law, seq, G = theta_law(2, d)
        f2 = word_law(2, d, law, 1, 2)
        D, Dp, Dm = d_infinity(2, d, law, 1)
        f1 = digit_law(2, d, law, 1)
        if d == 3:
            check(f2 == {(0, 1): Fr(1, 2), (1, 0): Fr(1, 2)} and D == Fr(2, 3), "(1/3)Theta_3: alternating, D=2/3")
        if d == 5:
            check(f1[0] == Fr(3, 5), "(1/5)Theta_3: f0 = 3/5")
        print("     (1/%d)Theta_3(1/2): f_0 = %s, f_00 = %s, f_01 = %s, D_inf = %s"
              % (d, f1[0], f2.get((0, 0), 0), f2.get((0, 1), 0), D))
    # bases b >= 3: simply normal theta scalings exist
    found = {}
    for b in (3, 4, 5, 6, 7, 10):
        lst = []
        for d in range(2, 81):
            if gcd(b, d) != 1:
                continue
            law = theta_law(b, d)[0]
            res = [all(x == Fr(1, b) for x in digit_law(b, d, law, sa * a))
                   for a in unit_coset_reps(b, d) for sa in (1, -1)]
            check(any(res) == all(res), "theta base-%d law uniform over numerators and signs (d=%d)" % (b, d))
            if all(res):
                lst.append(d)
        found[b] = lst
    check(found == {3: [7, 14, 19, 31, 35, 38, 43, 49, 62, 70, 74, 77, 79], 4: [], 5: [], 6: [79],
                    7: [71], 10: []}, "theta scalings simply normal in base b, d <= 80")
    print("   simply normal in base b (d <= 80): %s" % found)
    law = theta_law(3, 7)[0]
    f2 = word_law(3, 7, law, 1, 2)
    check(digit_law(3, 7, law, 1) == [Fr(1, 3)] * 3 and len(f2) == 6
          and all(v == Fr(1, 6) for v in f2.values()), "(1/7)Theta_3(1/3) law")
    D, Dp, Dm = d_infinity(3, 7, law, 1)
    print("   (1/7)Theta_3(1/3): digits 1/3 each; six words of length 2, each 1/6 (00,11,22 absent);"
          " D_inf = %s" % D)
    # prime criterion: t = p-1 = 2 mod 4 ... (i) t = 2 mod 4, (ii) zero-free, (iii) b primitive root,
    # (iv) b | p-1  =>  simply normal in base b; checked against the automaton for p <= 300
    ncrit = 0
    for b in (2, 3, 6, 7):
        for p in PRIMES:
            if p < 3 or p > 300 or b % p == 0:
                continue
            t = order_mod(b, p)
            law, seq, G = theta_law(b, p)
            zero_free = all(x % p for x in seq)
            if t % 4 == 2:
                check(G % p == 0, "t = 2 mod 4 => Gauss-type sum G = 0 mod p")
            crit = (t % 4 == 2 and zero_free and t == p - 1 and (p - 1) % b == 0)
            sn_b = all(all(x == Fr(1, b) for x in digit_law(b, p, law, sa * a))
                       for a in unit_coset_reps(b, p) for sa in (1, -1))
            if crit:
                check(sn_b, "prime criterion => simply normal (b=%d, p=%d)" % (b, p))
                ncrit += 1
            if b == 2:
                check(sn_b == (t % 4 == 2 and zero_free), "base-2 prime criterion (p=%d)" % p)
    print("   prime criterion (t = 2 mod 4, zero-free, b primitive root, b | p-1) confirmed: %d pairs"
          " (b, p), b in {2,3,6,7}, p <= 300" % ncrit)
    # Proposition 5.4: words of length L occurring infinitely often in E_2 (d = 1, a = 1, b = 2).
    # At distance r <= R before an insertion the word depends on (r, c_k, sgn R_k); predicted set
    # = digits of {c 2^-r (1 + s eps)}, c, s in {+1, -1}.  Bound 4dR + d + 1, R = L + ceil(log_2 4d|a|).
    N = 20000
    pnext = min(P for P in (pent(i) for i in range(-200, 201)) if P > N)
    M = pnext + 64
    X = 0
    for i in range(-200, 201):
        P = pent(i)
        if P <= M:
            X += (-1 if i & 1 else 1) << (M - P)
    gbits = M - N
    rem = X & ((1 << gbits) - 1)
    check(2 <= rem <= (1 << gbits) - 3, "E_2 bits certified (tail beyond M is < 1 unit)")
    s2 = format(X >> gbits, "0%db" % N)
    n0 = pent(-30)      # gaps >= 30 after this point
    counts = {}
    for L in range(3, 12):
        pred = set()
        for r in range(1, L + 5):
            for c in (1, -1):
                for e in (1, -1):
                    x = Fr(c, 2 ** r) * (1 + Fr(e, 2 ** (L + 8)))
                    x -= x.numerator // x.denominator
                    w = ""
                    for _ in range(L):
                        x *= 2
                        dg = 1 if x >= 1 else 0
                        w += str(dg)
                        x -= dg
                    pred.add(w)
        first = set(s2[n:n + L] for n in range(n0, N // 2))
        second = set(s2[n:n + L] for n in range(N // 2, N - L + 1))
        check(first == second == pred, "E_2 tail words = predicted (r, c_k, sgn R_k) set, L=%d" % L)
        check(len(pred) == 4 * L - 4, "E_2: exactly 4L - 4 recurrent words, L=%d" % L)
        R = L + 2
        check(len(pred) <= 4 * R + 2, "bound 4dR + d + 1 (L=%d)" % L)
        counts[L] = len(pred)
    check(counts[8] == 28 and counts[8] > 1 * (8 + 2 + 2), "L = 8: 28 words > d(R+2) = 12")
    print("   Prop. 5.4, E_2 (d = 1): recurrent words of length L number exactly 4L - 4 (L = 3..11);"
          " L = 8: %d words, bound 4dR+d+1 = %d (old claim d(R+2) = %d is false)" % (counts[8], 4 * 10 + 2, 12))


# ====================================================================== R5
def section_r5():
    header("R5  Derivative scalings (a/d)D^jE_2 and (a/d)D^jE_2^3, j = 1, 2")
    res = {}
    for kind in ("E", "E3"):
        for j in (1, 2):
            sn = []
            for d in range(3, 46, 2):
                law = euler_law(2, d, j)[0] if kind == "E" else cube_law(2, d, j)[0]
                t, g, W, cnt, zp, zm = law
                sm, Den = masses(2, d, law)
                for c in range(1, d):
                    check(sm[c % g] == sm[(-c) % g], "derivative negation symmetry")
                if t % 2 == 1:
                    check(zp == zm, "odd order => complement symmetric (D^j)")
                ok = all(digit_law(2, d, law, sa * a)[0] == Fr(1, 2)
                         for a in unit_coset_reps(2, d) for sa in (1, -1))
                anyok = any(digit_law(2, d, law, sa * a)[0] == Fr(1, 2)
                            for a in unit_coset_reps(2, d) for sa in (1, -1))
                check(ok == anyok, "all or nothing")
                if ok:
                    sn.append(d)
            res[(kind, j)] = sn
            print("  %s, j=%d: base-2 simply normal for odd d <= 45 exactly at %s" % (
                "D^jE_2" if kind == "E" else "D^jE_2^3", j, sn))
            # content: every coefficient of D^jE^3 (j >= 1) is divisible by 3, so the reduced
            # denominator is d / gcd(d, 3); for D^jE the content is 1
            want = [d for d in range(3, 46, 2)
                    if order_mod(2, d // (gcd(d, 3) if kind == "E3" else 1)) % 2 == 1]
            check(sn == want, "derivative SN iff reduced denominator has odd order (d <= 45)")
    for j in range(1, 7):
        cs = [(-1) ** k * (2 * k + 1) * (k * (k + 1) // 2) ** j for k in range(1, 40)]
        check(cs[0] == -3, "k = 1 coefficient of D^jE^3 is -3")
        g0 = 0
        for c in cs:
            g0 = gcd(g0, c)
        check(g0 == 3, "content of D^jE^3 is 3")
    print("  content of D^jE^3 is exactly 3 for j = 1..6 (k = 1 coefficient -3): (a/3)DE_2^3 = a E_2^2 DE_2"
          " (Theorem 2), (a/21)DE_2^3 = (a/7)E_2^2DE_2")
    # Corollary 6.2: 3 || d and ord_{d/3}(2) odd => (a/d)D^jE_2^3 simply normal in base 2
    cor = []
    for d in (3, 21, 69, 93):
        check(d % 3 == 0 and d % 9 != 0 and order_mod(2, d // 3) % 2 == 1, "Cor 6.2 hypothesis d=%d" % d)
        for j in (1, 2):
            law = cube_law(2, d, j)[0]
            check(all(digit_law(2, d, law, sa * a)[0] == Fr(1, 2)
                      for a in unit_coset_reps(2, d) for sa in (1, -1)), "Cor 6.2 d=%d j=%d" % (d, j))
        cor.append(d)
    print("  Corollary 6.2 (3 || d, ord_{d/3}(2) odd): (a/d)D^jE_2^3 simply normal, j = 1, 2, d in %s" % cor)
    # even denominators (b odd): the D^jE_b term period is 2 lcm(t, d), not lcm(2t, d)
    neven = 0
    for b, d in ((3, 2), (3, 4), (5, 4), (3, 8), (5, 8), (7, 16), (5, 12), (7, 6)):
        t = order_mod(b, d)
        vd = (d & -d).bit_length()
        vt = (t & -t).bit_length()
        check(d % 2 == 0 and vd > vt, "even d with v_2(d) > v_2(t)")
        for j in (1, 2):
            Lam = euler_period(b, d, j)
            old = lcm(2 * t, d)

            def tmz(i):
                P = pent(i)
                v = pow(P, j, d) * pow(b, -P, d) % d
                return (-v) % d if i & 1 else v
            check(Lam == 2 * lcm(t, d) and all(tmz(i + Lam) == tmz(i) for i in range(-2 * Lam, 2 * Lam)),
                  "2 lcm(t, d) is a term period (b=%d, d=%d, j=%d)" % (b, d, j))
            if j == 1:
                check(all(tmz(i + old) == (tmz(i) + d // 2) % d for i in range(-2 * old, 2 * old)),
                      "lcm(2t, d) shifts tm by d/2: not a period (b=%d, d=%d)" % (b, d))
            law = euler_law(b, d, j)[0]
            law2 = euler_law(b, d, j, mult=2)[0]
            tt, g, W, cnt, zp, zm = law
            sm, Den = masses(b, d, law)
            for c in range(1, d):
                check(sm[c % g] == sm[(-c) % g], "even-d negation symmetry (b=%d, d=%d, j=%d)" % (b, d, j))
            for a in unit_coset_reps(b, d):
                for sa in (1, -1):
                    for L in (1, 2, 3):
                        f = word_law(b, d, law, sa * a, L)
                        check(f == word_law(b, d, law2, sa * a, L), "period-independent law")
                        z, top = (0,) * L, (b - 1,) * L
                        for w, v in f.items():
                            if w not in (z, top):
                                check(f.get(tuple(b - 1 - x for x in w), 0) == v, "f_w = f_wbar (even d)")
                        check(f.get(z, 0) - f.get(top, 0) == sa * Fr((zp - zm) * tt, Den),
                              "f_0^L - f_(b-1)^L = sgn(a)(w0+ - w0-) (even d)")
                        neven += 1
        if (b, d) == (3, 2):
            bad = digit_law(b, d, euler_law(b, d, 1, period=lcm(2 * t, d))[0], 1)
            good = digit_law(b, d, euler_law(b, d, 1)[0], 1)
            check(good == [Fr(1, 3), Fr(1, 2), Fr(1, 6)] and bad == [Fr(1, 6), Fr(5, 6), Fr(0)],
                  "(1/2)DE_3: correct law vs law from the wrong period lcm(2t, d)")
    print("  even d, v_2(d) > v_2(t) (8 pairs (b, d), j = 1, 2): term period 2 lcm(t, d) verified, lcm(2t, d)"
          " fails; Theorem 1.1 symmetry verified on %d (a, sign, L) laws" % neven)
    print("  (1/2)DE_3 in base 3: digits %s (the wrong period lcm(2t, d) = 2 would give %s)" % (
        " ".join(str(x) for x in digit_law(3, 2, euler_law(3, 2, 1)[0], 1)),
        " ".join(str(x) for x in digit_law(3, 2, euler_law(3, 2, 1, period=2)[0], 1))))
    # an even-order example law
    law = euler_law(2, 3, 1)[0]
    f = digit_law(2, 3, law, 1)
    print("  (1/3)DE_2: f_0 = %s;  (1/3)D^2E_2: f_0 = %s;  (1/5)DE_2^3: f_0 = %s" % (
        f[0], digit_law(2, 3, euler_law(2, 3, 2)[0], 1)[0], digit_law(2, 5, cube_law(2, 5, 1)[0], 1)[0]))


# ====================================================================== R6
def euler_coeffs(M):
    e = [0] * (M + 1)
    for j in range(-isqrt(M) - 2, isqrt(M) + 3):
        P = pent(j)
        if 0 <= P <= M:
            e[P] += -1 if j & 1 else 1
    return e


def section_r6():
    header("R6  (a/2)E_b^2 in odd base b")
    M = 4400
    e = euler_coeffs(M)
    supp = [(m, c) for m, c in enumerate(e) if c]
    a2 = [0] * (M + 1)
    for m1, c1 in supp:
        for m2, c2 in supp:
            if m1 + m2 > M:
                break
            a2[m1 + m2] += c1 * c2
    gp = set(pent(j) for j in range(-100, 101))
    for n in range(M + 1):
        check((a2[n] % 2 == 1) == (n % 2 == 0 and n // 2 in gp), "E^2 = E(q^2) mod 2 at n=%d" % n)
    # atom 1/2 shifts: I_n odd
    par = 0
    odd = 0
    N = 4096
    for n in range(N):
        par ^= a2[n] & 1
        odd += par
    check(abs(3 * odd - 2 * N) <= 3 * (2 * isqrt(N) + 4), "atom-1/2 density 2/3 + O(sqrt N)")
    print("E(q)^2 = E(q^2) mod 2 verified for n <= %d; atom-1/2 shifts below %d: %d (2N/3 = %.1f)"
          % (M, N, odd, 2 * N / 3))
    # certified base-3 digits of (1/2)E_3^2
    b = 3
    Nd = 4000
    Mx = M
    Z = 0
    for m in range(Mx + 1):
        Z = Z * b + a2[m]
    # tail bound: |a2(m)| <= 12m+1
    B = 0                                   # integer bound for sum_{k>=1} (12(Mx+k)+1) 3^{-k}
    for k in range(1, 60):
        B += -(-(12 * (Mx + k) + 1) * 10 ** 6 // (3 ** k))
    B = B // 10 ** 6 + 2
    sh = 2 * b ** (Mx - Nd)
    lo, hi = (Z - B) // sh, (Z + B) // sh
    check(lo == hi, "certified digits of (1/2)E_3^2")
    v = lo % b ** Nd
    dig = []
    for _ in range(Nd):
        dig.append(v % b)
        v //= b
    dig.reverse()
    f = [Fr(dig.count(c), Nd) for c in range(3)]
    print("certified base-3 digits of (1/2)E_3^2, N = %d: f_0 = %.4f, f_1 = %.4f, f_2 = %.4f"
          % (Nd, float(f[0]), float(f[1]), float(f[2])))
    # digit d_{n+1} conditioned on the atom (I_n mod 2) at shift n
    par = 0
    c1 = [0, 0, 0]
    c0 = [0, 0, 0]
    for n in range(Nd):
        par ^= a2[n] & 1
        (c1 if par else c0)[dig[n]] += 1
    n1, n0 = sum(c1), sum(c0)
    print("   atom 1/2 shifts: %d, digit-1 share %.4f;  atom 0 shifts: %d, digit {0,2} share %.4f"
          % (n1, c1[1] / n1, n0, (c0[0] + c0[2]) / n0))
    check(n1 + n0 == Nd, "shift count")


# ====================================================================== A4 helpers
def divisors_from_fact(fac):
    ds = [1]
    for p, e in fac:
        ds = [x * p ** k for x in ds for k in range(e + 1)]
    return ds


SPF = None


def factor(n):
    out = []
    while n > 1:
        p = SPF[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return out


def hist_of(fac, M):
    h = {}
    for x in divisors_from_fact(fac):
        r = x % M
        h[r] = h.get(r, 0) + 1
    return h


def hist_mul(h1, h2, M):
    out = {}
    for x, a in h1.items():
        for y, c in h2.items():
            r = x * y % M
            out[r] = out.get(r, 0) + a * c
    return out


def a_from_hist(h, r, M):
    return h.get(r % M, 0) - h.get((-r) % M, 0)


def units(M):
    return [x for x in range(1, M) if gcd(x, M) == 1]


def carmichael(M):
    return max(order_mod(u, M) for u in units(M)) if M > 2 else 1


def neg1_square(M):
    for u in units(M):
        if u * u % M == M - 1:
            return u
    return None


def is_cyclic(M):
    return carmichael(M) == len(units(M))


def smallest_primes_in(cls, M, k, avoid=()):
    out = []
    for p in PRIMES:
        if p % M == cls % M and p not in avoid and M % p:
            out.append(p)
            if len(out) == k:
                return out
    raise RuntimeError("not enough primes")


# ====================================================================== S1
def section_s1():
    header("S1  Everywhere-nonnegative q-digamma reflections: classification for M <= 60")
    X = 20000
    # reduced nonnegative pairs: r'=1, M' | 24, M' >= 3
    for Mp in (3, 4, 6, 8, 12, 24):
        a = [0] * (X + 1)
        for dd in range(1, X + 1):
            w = 1 if dd % Mp == 1 else (-1 if dd % Mp == Mp - 1 else 0)
            if w:
                for n in range(dd, X + 1, dd):
                    a[n] += w
        check(min(a[1:]) >= 0, "a_{1,%d} >= 0 up to %d" % (Mp, X))
    nonneg, signed = [], []
    for M in range(3, 61):
        for r in range(1, (M + 1) // 2):
            if 2 * r >= M:
                continue
            g = gcd(r, M)
            Mp, rp = M // g, r // g
            pred = (rp == 1 and 24 % Mp == 0)
            (nonneg if pred else signed).append((r, M))
            if pred:
                continue
            # witness for (rp, Mp)
            G = units(Mp)
            if rp % Mp not in (1, Mp - 1):
                p = smallest_primes_in((-rp) % Mp, Mp, 1)[0]
                res = [p % Mp]
                n = p
            else:
                # rp = 1, lambda(Mp) > 2
                best = None
                for u in G:
                    h = order_mod(u, Mp)
                    if h >= 4 and h % 2 == 0 and pow(u, h // 2, Mp) == Mp - 1:
                        if best is None or h < best[1]:
                            best = (u, h)
                if best:
                    u, h = best
                    ps = smallest_primes_in(u, Mp, h // 2 + 1)
                else:
                    u = next(x for x in G if order_mod(x, Mp) >= 3)
                    v = (-pow(u, -2, Mp)) % Mp
                    ps = smallest_primes_in(u, Mp, 3) + smallest_primes_in(v, Mp, 1)
                res = [p % Mp for p in ps]
                n = 1
                for p in ps:
                    n *= p
            dist = {1 % Mp: 1}
            for x in res:
                nd = dict(dist)
                for y, c in dist.items():
                    z = y * x % Mp
                    nd[z] = nd.get(z, 0) + c
                dist = nd
            val = dist.get(rp % Mp, 0) - dist.get((-rp) % Mp, 0)
            check(val < 0, "negative witness for (r,M)=(%d,%d)" % (r, M))
            if n < 10 ** 7:
                direct = 0
                for dd in range(1, isqrt(n) + 1):
                    if n % dd == 0:
                        for e in {dd, n // dd}:
                            direct += 1 if e % Mp == rp % Mp else (-1 if e % Mp == (-rp) % Mp else 0)
                check(direct == val, "direct divisor sum")
    print("pairs 1 <= r < M/2, 3 <= M <= 60: %d nonnegative, %d signed (each signed pair has an explicit"
          " witness n with a_{r,M}(gn) < 0)" % (len(nonneg), len(signed)))
    check(len(nonneg) + len(signed) == sum((M - 1) // 2 for M in range(3, 61)), "pair count")
    print("nonnegative exactly when r | M and M/r in {3,4,6,8,12,24}: %d pairs" % len(nonneg))
    # gcd reduction identity, small check
    for (r, M) in [(2, 10), (3, 15), (4, 20), (6, 21), (5, 30)]:
        g = gcd(r, M)
        for n in range(1, 400):
            lhs = sum((1 if dd % M == r else -1 if dd % M == M - r else 0) for dd in range(1, n + 1) if n % dd == 0)
            rhs = 0
            if n % g == 0:
                m = n // g
                Mp, rp = M // g, r // g
                rhs = sum((1 if dd % Mp == rp else -1 if dd % Mp == Mp - rp else 0)
                          for dd in range(1, m + 1) if m % dd == 0)
            check(lhs == rhs, "gcd reduction")
    # eventual negativity: a(nq) = 2a(n) for q = 1 mod M prime
    for (r, M) in [(1, 5), (2, 5), (1, 7), (3, 8)]:
        q = smallest_primes_in(1, M, 1, avoid=(2, 3))[0]
        for n in range(1, 300):
            if n % q == 0:
                continue
            h1 = hist_of(factor(n), M)
            h2 = hist_mul(h1, hist_of([(q, 1)], M), M)
            check(a_from_hist(h2, r, M) == 2 * a_from_hist(h1, r, M), "a(nq) = 2a(n)")
    print("a(nq) = 2a(n) for primes q = 1 (mod M): negative values recur along nq, nq_1q_2, ...")
    return nonneg, signed


# ====================================================================== S2
def section_s2():
    header("S2  Universal sign flip: -1 a square mod M'")
    mods = [M for M in range(3, 61) if carmichael(M) > 2 and neg1_square(M)]
    check(mods == [5, 10, 13, 17, 25, 26, 29, 34, 37, 41, 50, 53, 58], "moduli with -1 a square")
    print("moduli M' <= 60 with lambda(M') > 2 and -1 a square: %s" % mods)
    # real odd character exists iff -1 not a square: check G/G^2 criterion
    for M in range(3, 61):
        sq = set(u * u % M for u in units(M))
        # a real odd character exists iff -1 not in G^2 (G/G^2 elementary abelian)
        check((neg1_square(M) is None) == ((M - 1) not in sq), "square criterion")
    nflip = 0
    for M in mods:
        u = neg1_square(M)
        q1, q2 = smallest_primes_in(u, M, 2)
        hm = hist_of([(q1, 2), (q2, 2)], M)
        hq = hist_of([(q1, 2)], M)
        uinv = pow(u, -1, M)
        for n in range(1, 400):
            if n % q1 == 0 or n % q2 == 0:
                continue
            hn = hist_of(factor(n), M)
            hnm = hist_mul(hn, hm, M)
            hnq = hist_mul(hn, hq, M)
            for r in units(M):
                if 2 * r > M:
                    continue
                check(a_from_hist(hnm, r, M) == -a_from_hist(hn, r, M), "flip a(n m) = -a(n), M=%d" % M)
                check(a_from_hist(hnq, r, M) == a_from_hist(hn, uinv * r, M), "transport a(n q^2) = a_{u^-1 r}(n)")
                nflip += 1
    print("a_{r,M'}(n q1^2 q2^2) = -a_{r,M'}(n) and a_{r,M'}(n q1^2) = a_{u^{-1}r,M'}(n) verified on %d"
          " triples (M', r, n), n < 400" % nflip)
    u = neg1_square(5)
    print("example M' = 5: u = %d, q1, q2 = %s, m = %d" % (u, smallest_primes_in(u, 5, 2),
                                                       (smallest_primes_in(u, 5, 2)[0] * smallest_primes_in(u, 5, 2)[1]) ** 2))


# ====================================================================== S3
def poly_mulmod(a, b, n):
    out = [0] * n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[(i + j) % n] += x * y
    return out


def cyclotomic(n):
    # Phi_n via division of x^n - 1 by Phi_d, d | n, d < n
    cache = {}

    def phi(m):
        if m in cache:
            return cache[m]
        num = [-1] + [0] * (m - 1) + [1]   # x^m - 1, low to high
        for d in range(1, m):
            if m % d == 0:
                num = poly_div(num, phi(d))
        cache[m] = num
        return num
    return phi(n)


def poly_div(a, b):
    a = a[:]
    q = [0] * (len(a) - len(b) + 1)
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1] // b[-1]
        q[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    check(all(x == 0 for x in a[:len(b) - 1]), "exact division")
    return q


def poly_mod(a, b):
    a = a[:]
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1] // b[-1]
        for j, y in enumerate(b):
            a[i + j] -= c * y
    return a[:len(b) - 1]


def section_s3():
    header("S3  Dominant-part flips for cyclic moduli without sqrt(-1)")
    mods = [M for M in range(3, 32) if is_cyclic(M) and len(units(M)) >= 4 and neg1_square(M) is None]
    check(mods == [7, 9, 11, 14, 18, 19, 22, 23, 27, 31], "cyclic moduli list")
    tot = 0
    for M in mods:
        G = units(M)
        phi = len(G)
        gam = next(x for x in G if order_mod(x, M) == phi)
        ind = {}
        x = 1
        for k in range(phi):
            ind[x] = k
            x = x * gam % M
        # choose prime powers (class index, exponent)
        if phi % 3 == 0:
            spec = [(phi // 3, 1)] * 3
        else:
            spec = [(1, phi - 2), (1, phi - 2), (phi - 2, phi // 2 - 2)]
        cls_used = {}
        fac = []
        for (ix, e) in spec:
            cls = pow(gam, ix, M)
            k = cls_used.get(cls, 0)
            p = smallest_primes_in(cls, M, k + 1)[k]
            cls_used[cls] = k + 1
            fac.append((p, e))
        # (1*chi0)(m) in Z[x]/Phi_phi
        val = [1] + [0] * (phi - 1)
        for (p, e) in fac:
            f = [0] * phi
            for i in range(e + 1):
                f[(ind[p % M] * i) % phi] += 1
            val = poly_mulmod(val, f, phi)
        red = poly_mod(val, cyclotomic(phi))
        check(red == [-1] + [0] * (len(red) - 1), "(1*chi0)(m) = -1 (M=%d)" % M)
        hm = hist_of(fac, M)
        bad_j = [j for j in range(1, phi, 2) if gcd(j, phi) > 1]
        ndom = nsupp = 0
        for n in range(1, 1500):
            if gcd(n, M) != 1 or any(n % p == 0 for p, _ in fac):
                continue
            fn = factor(n)
            hn = hist_of(fn, M)
            if all(a_from_hist(hn, r, M) == 0 for r in G):
                continue
            nsupp += 1
            dom = True
            for j in bad_j:
                kills = False
                for (p, e) in fn:
                    o = phi // gcd(phi, j * ind[p % M])
                    if o > 1 and (e + 1) % o == 0:
                        kills = True
                        break
                if not kills:
                    dom = False
                    break
            if not dom:
                continue
            ndom += 1
            hnm = hist_mul(hn, hm, M)
            for r in G:
                check(a_from_hist(hnm, r, M) == -a_from_hist(hn, r, M), "dominant flip M=%d n=%d" % (M, n))
                tot += 1
        print("  M'=%2d phi=%2d  m = %s  dominant share of support (n<1500, (n,mM')=1): %d/%d"
              % (M, phi, "*".join("%d^%d" % pe for pe in fac), ndom, nsupp))
    print("dominant flips verified on %d triples (M', r, n)" % tot)


# ====================================================================== S4
def section_s4():
    header("S4  Im(1*chi) mod 5 and finite sign statistics")
    X = 1 << 15
    re = [0] * (X + 1)
    im = [0] * (X + 1)
    chi = {0: (0, 0), 1: (1, 0), 2: (0, 1), 3: (0, -1), 4: (-1, 0)}
    for dd in range(1, X + 1):
        cr, ci = chi[dd % 5]
        if cr or ci:
            for n in range(dd, X + 1, dd):
                re[n] += cr
                im[n] += ci
    stats = {}
    for (r, M) in [(1, 5), (2, 5), (1, 13), (3, 7), (1, 7), (3, 8), (5, 12)]:
        a = [0] * (X + 1)
        for dd in range(1, X + 1):
            w = 1 if dd % M == r else (-1 if dd % M == M - r else 0)
            if w:
                for n in range(dd, X + 1, dd):
                    a[n] += w
        if (r, M) == (1, 5):
            check(a == re, "a_{1,5} = Re(1*chi)")
        if (r, M) == (2, 5):
            check(a == im, "a_{2,5} = Im(1*chi)")
        S = sum(1 for n in range(1, X + 1) if a[n])
        pos = sum(1 for n in range(1, X + 1) if a[n] > 0)
        stats[(r, M)] = (S, pos)
        print("  (M,r)=(%2d,%d): support/X = %.4f, positive/support = %.4f, negative/support = %.4f"
              % (M, r, S / X, pos / S, 1 - pos / S))
    print("a_{1,5} = Re(1*chi), a_{2,5} = Im(1*chi) (chi(2) = i) verified for n <= %d" % X)


# ====================================================================== main
def main():
    global SPF
    t0 = time.time()
    SPF = list(range(20001))
    for i in range(2, 142):
        if SPF[i] == i:
            for j in range(i * i, 20001, i):
                if SPF[j] == j:
                    SPF[j] = i
    section_r1()
    section_r2()
    section_r3()
    section_r4()
    section_r5()
    section_r6()
    section_s1()
    section_s2()
    section_s3()
    section_s4()
    print("\nALL CHECKS PASSED: %d checks in %.1f s" % (CHECKS[0], time.time() - t0))


if __name__ == "__main__":
    main()
