#!/usr/bin/env python3
"""Phase 25, Track G: the original classical constants E(2), E_+(2), ln 2, sqrt(2), sqrt(3), phi, e.

Companion to notes/phase25/classical-constants-frontier.md.
Standard library only; exits 0 when every assertion holds.
Run:  python -B scripts/phase25_classical.py

Sections
  G1  E(2) = sum tau(n) 2^-n:
      - column process, carry-orbit identity, depth-L local carries (Lemma 1.1)
      - carry targets: simple normality vs the Poisson comparison law (Prop. 1.2)
      - ingredients of the mesoscopic collision theorem (Lemmas 1.3-1.4, Thm 1.5)
      - bounded-perturbation barrier (Prop. 1.7)
      - finite measurements: f_1, kappa_1/N, collision-distance law (Sec. 1.6)
  G2  E_+(2) = sum a_+(n) 2^-n:
      - sign-distance rule (Lemma 2.1), 2-adic displacement shift (Thm 2.2),
        exact rational enclosure of E|R_2| (Thm 2.2(1))
      - signed column collisions; finite measurements (Sec. 2.4)
  G3  ln 2:
      - BBP recurrence solution space (Lemma 3.1)
      - generalized band law at every p-adic level (Lemma 3.3), drop sets D(p)
      - dynamic rigidity: the finite translate class T = prod_p T_p (Thm 3.2, Prop. 3.4)
      - fixed-depth reduction (Thm 3.5)
      - geometric-reset barrier, two explicit blocks (Thm 3.6)
  G4  sqrt(2), sqrt(3), sqrt(5)/phi, e:
      - block-doubling identity and signed-weight propagation (Prop. 4.2)
      - signed support versus transitions (Lemma 4.1)
      - band law for the exponential partial sums e_K (Thm 4.3)

Labels in printout:
  [exact]   exact integer / rational identity or inequality (a finite certificate);
  [encl]    rigorous rational enclosure;
  [float]   floating-point evaluation of an exact formula (not certified);
  [finite]  finite measurement (bears on no asymptotic limit).
"""

import math
import sys
import time
from collections import Counter
from fractions import Fraction as Fr

T0 = time.time()
CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        print("FAILED:", msg)
        sys.exit(1)


def head(title):
    print("\n" + "=" * 78 + "\n" + title + "\n" + "=" * 78)


def sieve_primes(limit):
    s = bytearray([1]) * (limit + 1)
    s[0] = s[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i in range(limit + 1) if s[i]]


def v2(x):
    return (x & -x).bit_length() - 1


def vp(x, p):
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def naf_weight(c):
    c = abs(c)
    w = 0
    while c:
        if c & 1:
            r = 2 - (c & 3)  # +1 if c = 1 mod 4, -1 if c = 3 mod 4
            c -= r
            w += 1
        c >>= 1
    return w


def popcount(x):
    return bin(x).count("1")


def frac_dist(q):
    """Distance from the rational q to the nearest integer (exact)."""
    f = q - (q.numerator // q.denominator)
    return min(f, 1 - f)


def dec_floor(q, k):
    """Largest k-decimal rational <= q (exact, outward rounding for a lower endpoint)."""
    return Fr(math.floor(Fr(q) * 10 ** k), 10 ** k)


def dec_ceil(q, k):
    """Smallest k-decimal rational >= q (exact, outward rounding for an upper endpoint)."""
    return Fr(math.ceil(Fr(q) * 10 ** k), 10 ** k)


def fmt_dec(q, k):
    """Format a nonnegative k-decimal rational exactly (no float conversion)."""
    n = Fr(q) * 10 ** k
    check(n.denominator == 1 and n >= 0, "fmt_dec expects a nonnegative k-decimal rational")
    n = n.numerator
    return f"{n // 10 ** k}.{n % 10 ** k:0{k}d}"


# ---------------------------------------------------------------------------
# Shared arithmetic for G1 / G2
# ---------------------------------------------------------------------------
NMAX = 1 << 17
GUARD = 64
M_COL = NMAX + GUARD
LIM = M_COL + 400

TAU = [0] * (LIM + 1)
for _d in range(1, LIM + 1):
    for _m in range(_d, LIM + 1, _d):
        TAU[_m] += 1
PRIMES = sieve_primes(LIM)
OMEGA = [0] * (LIM + 1)
for _p in PRIMES:
    for _m in range(_p, LIM + 1, _p):
        OMEGA[_m] += 1
VV = [0] * (LIM + 1)
UU = [0] * (LIM + 1)
for _n in range(1, LIM + 1):
    _t = TAU[_n]
    _v = v2(_t)
    VV[_n] = _v
    UU[_n] = _t >> _v


# ===========================================================================
# G1
# ===========================================================================
def section_g1():
    head("G1  Original Erdos-Borwein constant E(2) = sum tau(n) 2^-n")
    # tau(n) <= 2 sqrt(n): bit lengths are small, so every column j <= M_COL is complete
    for n in range(1, LIM + 1):
        check(TAU[n] * TAU[n] <= 4 * n, "tau(n) <= 2 sqrt(n)")
    check(max(TAU[n].bit_length() for n in range(1, LIM + 1)) <= 12, "bit length of tau")

    # --- column process: source n deposits the bits of U(n) at columns n - V(n) - i
    S = [0] * (M_COL + 2)
    srcs = [[] for _ in range(NMAX + 1)]
    for n in range(1, M_COL + 20):
        v = VV[n]
        u = UU[n]
        i = 0
        while u:
            if u & 1:
                j = n - v - i
                check(j >= 1, "every bit lands at a fractional column j >= 1")
                if j <= M_COL:
                    S[j] += 1
                    if j <= NMAX:
                        srcs[j].append(n)
            u >>= 1
            i += 1
    print(f"  [exact] column process built for columns 1..{M_COL} (sources n <= {M_COL + 19})")

    # --- rigorous bound on the unknown carry entering column M_COL+1 (exact rational arithmetic)
    #     Y_{M+1} <= sum_{t>=1} beta(M+t) 2^-t with beta(j) = (2 + log2(2j)/2)(3 + log2(2j)/2).
    #     Since log2(2j) < b_j := (2j).bit_length(), beta(j) < (4 + b_j)(6 + b_j)/4.
    #     Head t <= T0 exactly; for t > T0, b_{M+t} <= B0 + bitlen(t) <= B0 + t with B0 = bitlen(2M)
    #     (as 2(M+t) <= 2M(1+t) <= 2M 2^bitlen(t)), so the term is < (c+t)^2 2^-t / 4 with c = 6 + B0.
    #     If (c+t)^2 <= 2^(t/2) for all t > T0, the tail is < (1/4) sum_{t>T0} 2^(-t/2) < 2^(-(T0+1)/2).
    T0 = 200
    B0 = (2 * M_COL).bit_length()
    cc = 6 + B0
    check((cc + T0 + 1) ** 4 <= 2 ** (T0 + 1), "(c+t)^2 <= 2^(t/2) at t = T0+1 (exact)")
    check((cc + T0 + 2) ** 4 <= 2 * (cc + T0 + 1) ** 4,
          "ratio ((c+t+1)/(c+t))^2 <= sqrt(2) for t > T0, so (c+t)^2 <= 2^(t/2) persists (exact)")
    yhead = sum(Fr((4 + (2 * (M_COL + t)).bit_length()) * (6 + (2 * (M_COL + t)).bit_length()), 4 << t)
                for t in range(1, T0 + 1))
    ybound = yhead + Fr(1, 2 ** ((T0 + 1) // 2))
    CMAX = 1000
    check(ybound < CMAX, "rigorous carry-in bound below CMAX (exact)")
    print(f"  [exact] carry-in bound Y_(M+1) < {fmt_dec(dec_ceil(ybound, 2), 2)} < CMAX = {CMAX}"
          f" (exact rational majorant; floating-point value of the beta-sum about"
          f" {sum((2 + 0.5 * math.log2(2 * (M_COL + t))) * (3 + 0.5 * math.log2(2 * (M_COL + t))) * 2.0 ** (-t) for t in range(1, 200)):.3f})")

    def run_carries(cin):
        c = [0] * (M_COL + 2)
        d = [0] * (M_COL + 2)
        c[M_COL + 1] = cin
        for j in range(M_COL, 0, -1):
            tot = S[j] + c[j + 1]
            d[j] = tot & 1
            c[j] = tot >> 1
        return c, d

    c_lo, d_lo = run_carries(0)
    c_hi, d_hi = run_carries(CMAX)
    check(c_lo[NMAX + 1] == c_hi[NMAX + 1], "carries certified at column NMAX+1 (monotone coupling)")
    c, d = c_lo, d_lo
    for j in range(1, NMAX + 1):
        check(d_lo[j] == d_hi[j], "digit certified")
    check(c[1] == 1, "carry out of column 1 equals floor(E) = 1")
    print(f"  [exact] digits d_1..d_{NMAX} and carries c_1..c_{NMAX + 1} certified; c_1 = floor(E) = 1")

    # --- independent Horner check of the first 4096 digits
    Np, G = 4096, 64
    X = 0
    for n in range(1, Np + G + 1):
        X = (X << 1) + TAU[n]
    # tail = sum_{m>=1} tau(Mh+m) 2^-m with Mh = Np+G; tau(n) <= 2 sqrt(n) and sqrt(Mh+m) <= sqrt(Mh) + m
    # give tail <= sum_{m>=1} 2 (sqrt(Mh) + m) 2^-m = 2 sqrt(Mh) + 4, which is < 400 iff 4 Mh < 396^2.
    Mh = Np + G
    check(4 * Mh < (400 - 4) ** 2, "Horner tail 2 sqrt(Np+G) + 4 < 400 (exact integer check)")
    fl = X >> G
    check(fl == (X + 400) >> G, "Horner floor determined")
    check(fl >> Np == 1, "integer part of E is 1")
    for j in range(1, Np + 1):
        check(((fl >> (Np - j)) & 1) == d[j], "Horner digit agrees with column process")
    print(f"  [exact] independent Horner evaluation agrees on all {Np} digits")

    # --- Lemma 1.1: column equations, Kummer form, depth-L truncation
    for j in range(1, NMAX + 1):
        check(S[j] + c[j + 1] == d[j] + 2 * c[j], "column equation S_j + c_(j+1) = d_j + 2 c_j")
    for N in (1 << 10, 1 << 12, 1 << 14, 1 << 16, NMAX):
        lhs = sum(d[1:N + 1])
        rhs = sum(S[1:N + 1]) - sum(c[1:N + 1]) + c[N + 1] - c[1]
        check(lhs == rhs, "Kummer form sum d = sum S - kappa + c_(N+1) - c_1")
    Ls = (1, 2, 4, 8, 16)
    loc_sum = {L: 0 for L in Ls}
    loc_diff = {L: 0 for L in Ls}
    for L in Ls:
        for j in range(1, NMAX + 1):
            W = 0
            for t in range(L):
                W = 2 * W + S[j + t]
            cl = W >> L
            check(c[j] == (W + c[j + L]) >> L, "finite-window carry identity")
            check(cl <= c[j] <= cl + ((c[j + L] + (1 << L) - 1) >> L), "depth-L truncation bound")
            loc_sum[L] += cl
            loc_diff[L] += (cl != c[j])
    kappa = sum(c[1:NMAX + 1])
    print(f"  [exact] column equations, Kummer form (5 values of N), window identity and depth-L bounds"
          f" (L in {Ls}) for all j <= {NMAX}")
    print(f"  [finite] depth-L local carry densities at N = 2^17 (true kappa_1/N = {kappa / NMAX:.5f}):")
    for L in Ls:
        print(f"           L = {L:2d}: mean c^(L) = {loc_sum[L] / NMAX:.5f},"
              f"  columns with c^(L) != c: {loc_diff[L]} ({loc_diff[L] / NMAX:.5f})")

    # --- Proposition 1.2: carry targets (exact interval arithmetic)
    Ct = (Fr(1339103, 10 ** 6), Fr(1339116, 10 ** 6))
    ps = (Fr(492450290, 10 ** 9), Fr(492460864, 10 ** 9))
    target = (Ct[0] - Fr(1, 2), Ct[1] - Fr(1, 2))
    model = (Ct[0] - ps[1], Ct[1] - ps[0])
    gap = (Fr(1, 2) - ps[1], Fr(1, 2) - ps[0])
    check(target == (Fr(839103, 10 ** 6), Fr(839116, 10 ** 6)), "target interval")
    check(model[0] > target[1], "Poisson-model carry density lies strictly above the target")
    check(Fr(846642, 10 ** 6) <= model[0] and model[1] <= Fr(846666, 10 ** 6), "model interval rounding")
    check(dec_floor(model[0], 6) == Fr(846642, 10 ** 6) and dec_ceil(model[1], 6) == Fr(846666, 10 ** 6),
          "model interval: stated endpoints are the outward 6-decimal roundings")
    # M1: the gap is certified at 7 decimals with outward rounding (exact upper endpoint 0.007549710)
    check(gap == (Fr(7539136, 10 ** 9), Fr(7549710, 10 ** 9)), "gap endpoints exactly")
    check(Fr(75391, 10 ** 7) <= gap[0] and gap[1] <= Fr(75498, 10 ** 7), "gap interval [0.0075391, 0.0075498]")
    check(dec_floor(gap[0], 7) == Fr(75391, 10 ** 7) and dec_ceil(gap[1], 7) == Fr(75498, 10 ** 7),
          "gap interval: stated endpoints are the outward 7-decimal roundings")
    check(gap[1] > Fr(75497, 10 ** 7), "the inward-rounded endpoint 0.0075497 would be invalid")
    check(Ct[0] - 1 >= Fr(339103, 10 ** 6), "C_true - 1 >= 0.339103")
    print(f"  [encl] simple-normality carry target C_true - 1/2 in"
          f" [{fmt_dec(dec_floor(target[0], 6), 6)}, {fmt_dec(dec_ceil(target[1], 6), 6)}]")
    print(f"  [encl] Poisson comparison carry C_true - p_* in"
          f" [{fmt_dec(dec_floor(model[0], 6), 6)}, {fmt_dec(dec_ceil(model[1], 6), 6)}]"
          f"  (model value, not evidence)")
    print(f"  [encl] difference 1/2 - p_* in [{fmt_dec(dec_floor(gap[0], 7), 7)}, {fmt_dec(dec_ceil(gap[1], 7), 7)}]"
          f" (outward-rounded; exact endpoints [{fmt_dec(gap[0], 9)}, {fmt_dec(gap[1], 9)}])")

    # --- Lemma 1.3 / 1.4 ingredients (finite and float)
    meanR = sum(abs(VV[n] - OMEGA[n]) for n in range(1, NMAX + 1)) / NMAX
    pr_small = [p for p in PRIMES if p < 100000] if PRIMES[-1] >= 100000 else sieve_primes(100000)
    Rb = 0.0
    for p in pr_small:
        Rb += sum((1 + math.log2(e + 1)) / p ** e for e in range(2, 60))
    Rb += 2.0 / 100000  # tail: sum_{p > 1e5} (1 + log2 3) * 2 / p^2 < 2e-5
    check(meanR <= Rb, "empirical mean |V - omega| below the elementary bound")
    print(f"  [finite] mean |V(n) - omega(n)| over n <= 2^17 = {meanR:.4f}"
          f"  <= [float] bound sum_p sum_(e>=2) (1+log2(e+1))/p^e = {Rb:.4f}")

    def s2odd(e):
        x = e + 1
        while x % 2 == 0:
            x //= 2
        return popcount(x)

    prod = 1.0
    for p in pr_small:
        acc = 0.0
        prev = 1.0
        for e in range(2, 60):
            g = float(s2odd(e)) ** 4
            acc += abs(g - prev) / p ** e
            prev = g
        prod *= 1 + acc
    prod *= math.exp(4000.0 / 100000)  # crude tail: |h(p^e)| <= 2(e+1)^4, sum_{p>1e5} ... < 4e-2
    m4 = sum(popcount(UU[n]) ** 4 for n in range(1, NMAX + 1)) / NMAX
    check(m4 <= prod, "empirical fourth moment of s_2(U) below the multiplicative majorant")
    meanlogU = sum(math.log2(UU[n]) for n in range(1, NMAX + 1)) / NMAX
    print(f"  [finite] mean s_2(U(n))^4 = {m4:.4f} <= [float] majorant {prod:.4f};"
          f"  mean log2 U(n) = {meanlogU:.4f}")

    # D_1 = V(n+1) - V(n): finite law (local probabilities do not yet look small)
    D1 = Counter(VV[n + 1] - VV[n] for n in range(1, NMAX + 1))
    row = ", ".join(f"{dd:+d}: {D1[dd] / NMAX:.3f}" for dd in range(-3, 4))
    print(f"  [finite] law of V(n+1) - V(n) on n <= 2^17: {row}")

    # --- collisions: pairs of bits from distinct sources sharing a column
    Ns = [1 << 10, 1 << 12, 1 << 14, 1 << 16, NMAX]
    snaps = {}
    pairs = 0
    hist = Counter()
    mass = 0
    excess = 0
    dsum = 0
    shell = Counter()
    for j in range(1, NMAX + 1):
        Lj = srcs[j]
        check(len(Lj) == S[j], "column list matches S_j")
        mass += S[j]
        excess += max(S[j] - 1, 0)
        if len(Lj) >= 2:
            check(len(set(Lj)) == len(Lj), "no source deposits two bits in one column")
            for a in range(len(Lj)):
                for b in range(a + 1, len(Lj)):
                    n1, n2 = min(Lj[a], Lj[b]), max(Lj[a], Lj[b])
                    h = n2 - n1
                    check(1 <= h <= TAU[n2].bit_length() - 1, "collision distance h <= log2 tau(n')")
                    hist[h] += 1
                    pairs += 1
                    if h <= 3:
                        shell[(n1.bit_length(), h)] += 1
        dsum += d[j]
        if j in Ns:
            check(pairs == sum(S[t] * (S[t] - 1) // 2 for t in range(1, j + 1)), "pair count = sum C(S_j,2)")
            check(pairs >= mass - j, "pair count >= sum S_j - N")
            snaps[j] = dict(f1=dsum / j, kappa=sum(c[1:j + 1]) / j, mass=mass / j, excess=excess / j,
                            pairs=pairs / j, h1=hist[1] / pairs, h2=(hist[1] + hist[2]) / pairs,
                            h4=sum(hist[t] for t in range(1, 5)) / pairs,
                            mh=sum(t * hist[t] for t in hist) / pairs, hmax=max(hist))
    print("  [finite] f_1, carry density and collision statistics (columns j <= N):")
    print("        N   loglogN    f_1    kappa/N  mass/N  excess/N  pairs/N  P(h=1)  P(h<=2)  P(h<=4)  mean h  max h")
    for N in Ns:
        z = snaps[N]
        print(f"   {N:7d}   {math.log(math.log(N)):.3f}   {z['f1']:.5f}  {z['kappa']:.5f}  {z['mass']:.4f}"
              f"  {z['excess']:.4f}   {z['pairs']:.4f}   {z['h1']:.4f}  {z['h2']:.4f}   {z['h4']:.4f}"
              f"   {z['mh']:.3f}   {z['hmax']}")
    print("  [finite] pair density per source at fixed distance h, by dyadic shell of the smaller source:")
    print("     shell   loglog   h=1      h=2      h=3")
    for s in range(9, 18):
        size = 1 << (s - 1)
        if (1 << s) > NMAX - 20:
            break
        print(f"     2^{s:<3d}   {math.log(math.log(1 << s)):.3f}   {shell[(s, 1)] / size:.4f}   "
              f"{shell[(s, 2)] / size:.4f}   {shell[(s, 3)] / size:.4f}")
    return S, c, d


def section_g1_perturbation():
    head("G1  Proposition 1.7: bounded-perturbation barrier (exact identities)")
    # eps(2m-1) = u_m, eps(2m) = -u_m (m >= 2), u_m in {0,1,2,3}
    for m in range(2, 60):
        for u in range(4):
            lhs = Fr(u, 2 ** (2 * m - 1)) - Fr(u, 2 ** (2 * m))
            check(lhs == Fr(u, 4 ** m), "pair contribution equals u_m 4^-m")
    check(sum(Fr(3, 4 ** m) for m in range(2, 200)) < Fr(1, 4), "partial range below 1/4")
    check(Fr(1, 4) - sum(Fr(3, 4 ** m) for m in range(2, 200)) == Fr(1, 4 ** 199), "range is exactly [0, 1/4]")
    for m in range(2, LIM // 2 + 1):
        check(TAU[2 * m] >= 3, "tau(2m) >= 3 for m >= 2 (nonnegativity of tau - u_m)")
    # pseudo-random digits; correlation and mean stability at X = 2^14
    X = 1 << 14
    seed = 12345
    eps = [0] * (X + 80)
    for m in range(2, (X + 70) // 2):
        seed = (1103515245 * seed + 12345) % (1 << 31)
        u = seed % 4
        eps[2 * m - 1] = u
        eps[2 * m] = -u
    run = 0
    for Xp in range(1, X + 1):
        run += eps[Xp]
        check(0 <= run <= 3, "partial sums of eps lie in [0, 3] (every X' <= X)")
    for c_name, cf in (("tau", lambda n: TAU[n]),
                       ("a_+", lambda n: (1 - v2(n)) * (TAU[n] // (v2(n) + 1)))):
        for h in range(0, 9):
            base_sum = sum(abs(cf(n)) for n in range(1, X + h + 1))
            s0 = sum(cf(n) * cf(n + h) for n in range(1, X + 1))
            s1 = sum((cf(n) + eps[n]) * (cf(n + h) + eps[n + h]) for n in range(1, X + 1))
            check(abs(s1 - s0) <= 6 * base_sum + 9 * X, f"correlation change bounded ({c_name}, h={h})")
    print("  [exact] eps-pairs contribute u_m 4^-m; range [0,1/4]; tau(2m) >= 3; 0 <= sum_(n<=X') eps <= 3 for all X' <= X;")
    print("          |sum c#c#(n+h) - sum c c(n+h)| <= 6 sum_(n<=X+h)|c| + 9X for c in {tau, a_+}, h <= 8, X = 2^14")


# ===========================================================================
# G2
# ===========================================================================
def section_g2():
    head("G2  Original plus Erdos-Borwein constant E_+(2) = sum a_+(n) 2^-n")
    AP = [0] * (LIM + 1)
    for n in range(1, LIM + 1):
        e = v2(n)
        AP[n] = (1 - e) * (TAU[n] // (e + 1))
    # alternating divisor sum check
    for n in range(1, 3001):
        check(AP[n] == sum((-1) ** (dd - 1) for dd in range(1, n + 1) if n % dd == 0), "a_+ formula")
    # Lemma 2.1: sign-distance rule
    cnt = 0
    for n in range(1, (1 << 16) + 1):
        for h in range(1, 65):
            pr = AP[n] * AP[n + h]
            if pr != 0:
                check((pr > 0) == (h % 2 == 0), "sign(a_+(n) a_+(n+h)) = (-1)^h")
                cnt += 1
    print(f"  [exact] Lemma 2.1 sign-distance rule on {cnt} nonzero pairs (n <= 2^16, h <= 64)")
    # displacement shift V_+ - V = v2(e-1) - v2(e+1) (e >= 2), 0 (e = 0)
    for n in range(1, LIM + 1):
        if AP[n] == 0:
            check(n % 4 == 2, "a_+(n) = 0 iff n = 2 mod 4")
            continue
        e = v2(n)
        Vp = v2(abs(AP[n]))
        want = 0 if e == 0 else v2(e - 1) - v2(e + 1)
        check(Vp - VV[n] == want, "V_+(n) - V(n) = v2(e-1) - v2(e+1)")
    print(f"  [exact] V_+(n) - V(n) = v2(e-1) - v2(e+1) (e >= 2), = 0 (e = 0), for all n <= {LIM}")
    meanR2 = sum(abs(v2(abs(AP[n])) - VV[n]) for n in range(1, NMAX + 1) if AP[n]) / NMAX
    # M2: exact rational enclosure of E|R_2| = sum_(e>=2) |v2(e-1) - v2(e+1)| 2^-(e+1).
    # Tail e >= EH: |v2(e-1) - v2(e+1)| <= log2(e+1) <= e and sum_(e>=EH) e 2^-(e+1) = (EH+1) 2^-EH.
    EH = 100
    for e in range(2, 4 * EH):
        check(abs(v2(e - 1) - v2(e + 1)) <= e, "|v2(e-1) - v2(e+1)| <= e")
    check(sum(Fr(e, 2 ** (e + 1)) for e in range(EH, 4 * EH)) + Fr(4 * EH + 1, 2 ** (4 * EH))
          == Fr(EH + 1, 2 ** EH), "closed form of the tail sum_(e>=EH) e 2^-(e+1)")
    haar_lo = sum(Fr(abs(v2(e - 1) - v2(e + 1)), 2 ** (e + 1)) for e in range(2, EH))
    haar_hi = haar_lo + Fr(EH + 1, 2 ** EH)
    check(Fr(882543, 10 ** 7) <= haar_lo and haar_hi <= Fr(882544, 10 ** 7),
          "E|R_2| in [0.0882543, 0.0882544] (exact)")
    check(haar_hi < Fr(883, 10 ** 4), "E|R_2| < 0.0883, so '0.0883...' would be false")
    print(f"  [finite] mean |V_+ - V| on n <= 2^17: {meanR2:.4f}")
    print(f"  [encl] Haar value E|R_2| = sum_(e>=2) |v2(e-1)-v2(e+1)| 2^-(e+1) in"
          f" [{fmt_dec(dec_floor(haar_lo, 7), 7)}, {fmt_dec(dec_ceil(haar_hi, 7), 7)}]"
          f" (exact head e < {EH}, tail <= {EH + 1}/2^{EH})")

    srcsP = [[] for _ in range(NMAX + 1)]
    for n in range(1, M_COL + 20):
        a = AP[n]
        if a == 0:
            continue
        A = abs(a)
        v = v2(A)
        w = A >> v
        i = 0
        while w:
            if w & 1:
                j = n - v - i
                check(j >= 1, "E_+ bit at fractional column")
                if j <= NMAX:
                    srcsP[j].append(n)
            w >>= 1
            i += 1
    Ns = [1 << 10, 1 << 12, 1 << 14, 1 << 16, NMAX]
    print("  [finite] signed column collisions (columns j <= N):")
    print("        N    mass/N   pairs/N   P(h=1)  P(h<=2)  reinforcing  cancelling  reinf. share")
    mass = 0
    pairs = 0
    reinf = 0
    hist = Counter()
    byh = Counter()
    for j in range(1, NMAX + 1):
        Lj = srcsP[j]
        mass += len(Lj)
        if len(Lj) >= 2:
            check(len(set(Lj)) == len(Lj), "distinct sources in an E_+ column")
            for a in range(len(Lj)):
                for b in range(a + 1, len(Lj)):
                    n1, n2 = min(Lj[a], Lj[b]), max(Lj[a], Lj[b])
                    h = n2 - n1
                    s1 = 1 if n1 % 2 else -1
                    s2 = 1 if n2 % 2 else -1
                    check((s1 * s2 > 0) == (h % 2 == 0), "reinforcing iff h even")
                    pairs += 1
                    hist[h] += 1
                    if s1 * s2 > 0:
                        reinf += 1
                        byh[(h, 1)] += 1
                    else:
                        byh[(h, -1)] += 1
        if j in Ns:
            print(f"   {j:7d}   {mass / j:.4f}    {pairs / j:.4f}   {hist[1] / pairs:.4f}  "
                  f"{(hist[1] + hist[2]) / pairs:.4f}   {reinf / j:.4f}      {(pairs - reinf) / j:.4f}"
                  f"      {reinf / pairs:.4f}")
    row = ", ".join(f"h={h}: {byh[(h, 1)] + byh[(h, -1)]}" for h in range(1, 7))
    print(f"  [finite] collision pairs by distance at N = 2^17: {row}")
    check(mass / NMAX < 1, "E_+ bit mass per column below 1 at N = 2^17 (no pigeonhole collisions)")


# ===========================================================================
# G3
# ===========================================================================
NB = 2000


def section_g3():
    head("G3  ln 2: BBP recurrence, dynamic rigidity, fixed-depth reduction, reset barrier")
    A = [0] * (NB + 1)
    Q = [1] * (NB + 1)
    s = Fr(0)
    for n in range(1, NB + 1):
        s = 2 * s + Fr(1, n)
        A[n] = s.numerator
        Q[n] = s.denominator
    print(f"  [exact] s_n = A_n/Q_n computed for n <= {NB}; log Q_n / n at n = {NB}: "
          f"{(Q[NB].bit_length() * math.log(2)) / NB:.4f} (bit-length estimate)")

    # Lemma 3.1: translates solve the recurrence
    for delta in (Fr(1, 3), Fr(2, 7), Fr(5, 8), Fr(3, 11 * 13)):
        prev = None
        for n in range(10, 60):
            xt = Fr(A[n], Q[n]) + 2 ** (n - 10) * delta
            if prev is not None:
                diff = xt - 2 * prev - Fr(1, n)
                check(diff.denominator == 1, "translate satisfies the BBP recurrence mod 1")
            prev = xt
    print("  [exact] x_n + 2^(n-n0) delta satisfies x_(n+1) = 2 x_n + 1/(n+1) mod 1 (4 values of delta)")

    # Lemma 3.3: generalized band law at every level
    pr = sieve_primes(NB)
    pairs = 0
    drops = 0
    for n in range(3, NB + 1):
        Qn = Q[n]
        An = A[n]
        for p in pr:
            if p > n:
                break
            if p == 2:
                continue
            J = 0
            pk = 1
            while pk * p <= n:
                pk *= p
                J += 1
            m = n // pk
            r = Qn % (pk * p)
            check(r != 0, "v_p(Q_n) <= floor(log_p n)")
            v = 0
            rr = r
            while rr % p == 0:
                rr //= p
                v += 1
            if A[m] % p != 0:
                check(v == J, "v_p(Q_n) = J when p does not divide A_m")
                qq = (r // pk) % p
                lhs = (An % p) * pow(qq, -1, p) % p
                rhs = pow(2, n - m, p) * (A[m] % p) * pow(Q[m] % p, -1, p) % p
                check(lhs == rhs, "leading p-adic digit p^J s_n = 2^(n-m) s_m mod p")
            else:
                check(v < J, "drop: v_p(Q_n) < J when p | A_m")
                drops += 1
            pairs += 1
    print(f"  [exact] generalized band law (all levels J) for {pairs} pairs (n <= {NB}, odd p <= n);"
          f" {drops} drop events")

    # drop sets D(p) = {m < p : p | A_m}
    D = {}
    for p in pr:
        if p == 2:
            continue
        D[p] = [m for m in range(1, p) if A[m] % p == 0]
    nd = sum(1 for p in D if not D[p])
    small = [p for p in D if p < 100 and D[p]]
    print(f"  [exact] drop sets: {nd} of {len(D)} odd primes p < {NB} have D(p) empty;"
          f" primes < 100 with D(p) nonempty: {small} (D(5) = {D[5]}, D(17) = {D[17]})")

    # Theorem 3.2 / Proposition 3.4: the finite translate class T = prod T_p at n1 = 40
    n1 = 40
    Qn1 = Q[n1]
    ps = [p for p in pr if p <= n1 and Qn1 % p == 0]
    check(all(Qn1 % p == 0 for p in ps), "prime support of Q_40")
    rest = Qn1
    for p in ps:
        while rest % p == 0:
            rest //= p
    check(rest == 1, "Q_40 is 40-smooth")
    total_upper = 1
    exact_lower = 1
    all_exact = True
    lines = []
    for p in ps:
        J1 = vp(Qn1, p)
        P = p ** J1
        good = set(range(P))
        for n in range(n1, NB + 1):
            v = vp(Q[n], p)
            if v > J1:
                continue
            u_part = Q[n] // p ** v
            X = (A[n] % P) * pow(u_part % P, -1, P) % P * (p ** (J1 - v)) % P
            tw = pow(2, n - n1, P)
            ng = set()
            for u in good:
                y = (X + tw * u) % P
                if y == 0:
                    e_new = 0
                else:
                    e_new = J1 - vp(y, p)
                if e_new == v:
                    ng.add(u)
            good = ng
        check(0 in good, "delta_p = 0 always survives")
        if p == 2:
            # T_2 is determined by n in [n1, n1 + v_2(Q_n1)) (Prop. 3.4(2)); require that range inside [n1, NB]
            exact = n1 + J1 <= NB
        else:
            exact = ((not D[p]) and p ** (J1 + 1) <= NB) or len(good) == 1
        all_exact = all_exact and exact
        if p != 2 and not D[p]:
            for u in range(0, P, p):
                check(u in good, "D(p) empty: every delta_p of valuation >= -(J1-1) survives")
            exact_lower *= p ** (J1 - 1)
        total_upper *= len(good)
        lines.append(f"p={p}: J1={J1}, |T_p| {'=' if exact else '<='} {len(good)}"
                     + ("" if p == 2 else f" (D(p) {'empty' if not D[p] else D[p]})"))
    print(f"  [exact] translate class at n1 = {n1}, checked on [{n1}, {NB}]:")
    for i in range(0, len(lines), 3):
        print("          " + ";  ".join(lines[i:i + 3]))
    check(all_exact, "every local factor T_p is certified exactly")
    check(total_upper == 5054400, "|T| at n1 = 40")
    print(f"  [exact] every factor is exact (p = 2; D(p) empty with p^(J1+1) <= {NB}; or T_p = {{0}}),"
          f" so |T| = {total_upper} exactly")
    print(f"          (generic lower bound prod p^(J1-1) over D(p) empty = {exact_lower};"
          f" Q_40 = {Qn1}, about 2^{Qn1.bit_length()})")
    check(exact_lower <= total_upper < Qn1, "translate class is a proper finite subset")

    # Theorem 3.5: fixed-depth reduction
    for n in range(16, 1500):
        for t in range(1, 9):
            st = Fr(A[n + t], Q[n + t]) - 2 ** t * Fr(A[n], Q[n])
            exp = sum(Fr(2 ** (t - k), n + k) for k in range(1, t + 1))
            check(st == exp, "s_(n+t) - 2^t s_n = sum 2^(t-k)/(n+k)")
            check(0 < exp < Fr(2 ** t, n + 1), "0 < s_(n,t) < 2^t/(n+1)")
    print("  [exact] fixed-depth reduction: s_(n+t) - 2^t s_n in (0, 2^t/(n+1)) for 16 <= n < 1500, t <= 8")

    # Theorem 3.6: geometric-reset barrier, explicit blocks
    allp = sieve_primes(60000)
    thsum = [0.0] * 60001
    acc = 0.0
    ip = 0
    for x in range(60001):
        while ip < len(allp) and allp[ip] <= x:
            acc += math.log(allp[ip])
            ip += 1
        thsum[x] = acc
    worst = min((thsum[n] - thsum[n // 2]) / n for n in range(240, 60001))
    print(f"  [float] min over 240 <= n <= 60000 of (theta(n) - theta(n/2))/n = {worst:.4f}")
    # exact: M(n) = prod_{n/2 < p <= n} p has log2 M(n) >= 0.55 n on 240 <= n <= 60000
    isp = bytearray(60001)
    for p in allp:
        isp[p] = 1
    Mn = 1
    for p in allp:
        if 119 < p <= 239:
            Mn *= p
    worst_bits = 10.0
    for n in range(240, 60001):
        if isp[n]:
            Mn *= n
        if n % 2 == 0 and isp[n // 2]:
            check(Mn % (n // 2) == 0, "leaving prime divides the product")
            Mn //= n // 2
        check(20 * (Mn.bit_length() - 1) >= 11 * n, "log2 M(n) >= 0.55 n (exact, via bit length)")
        worst_bits = min(worst_bits, (Mn.bit_length() - 1) / n)
    print(f"  [exact] floor(log2 prod_(n/2<p<=n) p) >= 0.55 n for every 240 <= n <= 60000"
          f" (min ratio {worst_bits:.4f})")
    for n in (240, 360, 540, 1000, 60000):
        check((4 * n * n + 2 * n) / math.log(n / 2) < n * n, "sieve inequality (4n^2+2n)/ln(n/2) < n^2")

    def block(ni, nnext, prev_state):
        Pset = [p for p in pr if ni // 2 < p <= ni] if ni <= NB else None
        M = 1
        for p in Pset:
            M *= p
        # high-precision {2^ni ln 2} = x_ni + r_ni
        PREC = 900
        r_sc = sum((1 << (PREC - k)) // (ni + k) for k in range(1, PREC))
        x_sc = (A[ni] << PREC) // Q[ni]
        t_sc = (-(x_sc + r_sc)) % (1 << PREC)
        a0 = (t_sc * M + (1 << (PREC - 1))) >> PREC
        # residues: true component at p and excluded classes
        comps = {}
        for p in Pset:
            for n in range(ni, nnext):
                check(vp(Q[n], p) == 1, "top-band prime has v_p(Q_n) = 1 throughout the block")
                comps[(p, n)] = (A[n] % p) * pow((Q[n] // p) % p, -1, p) % p
        jj = 0
        tries = 0
        while True:
            a = a0 + jj
            ok = True
            for p in Pset:
                vpart = a * pow((M // p) % p, -1, p) % p
                for n in range(ni, nnext):
                    if (comps[(p, n)] + pow(2, n - ni, p) * vpart) % p == 0:
                        ok = False
                        break
                if not ok:
                    break
            tries += 1
            if ok:
                break
            jj = -jj if jj > 0 else -jj + 1
        check(abs(jj) <= ni * ni, "good residue found within n^2 of the target (sieve bound)")
        excl = 0
        for p in Pset:
            ex = set()
            for n in range(ni, nnext):
                ex.add((-comps[(p, n)] * pow(pow(2, n - ni, p), -1, p)) % p)
            check(len(ex) <= 2, "at most two excluded residues per top-band prime")
            excl += len(ex)
        delta = Fr(a, M)
        check(delta.denominator == M or M % delta.denominator == 0, "delta supported on top-band primes")
        eta_bound = Fr(abs(jj) + 1, M) + Fr(1000, 2 ** PREC)
        states = {}
        maxdist = Fr(0)
        for n in range(ni, nnext):
            xt = Fr(A[n], Q[n]) + 2 ** (n - ni) * delta
            xt -= xt.numerator // xt.denominator
            check(xt.denominator == Q[n], "exact reduced denominator Q_n preserved")
            dist = frac_dist(xt)
            check(dist <= 2 ** (n - ni) * eta_bound + Fr(1, n), "state within 2^(n-ni)|eta| + 1/n of 0")
            maxdist = max(maxdist, dist * n)
            if n > ni:
                prevx = states[n - 1]
                check((xt - 2 * prevx - Fr(1, n)).denominator == 1, "exact recurrence inside the block")
            states[n] = xt
        if prev_state is not None:
            check((states[ni] - 2 * prev_state - Fr(1, ni)).denominator != 1, "recurrence violated at the reset")
        # components at primes outside the block support are unchanged: at every n of the block the
        # difference from the true state has denominator dividing M (squarefree, top-band primes only)
        for n in range(ni, nnext):
            diff = states[n] - (Fr(A[n], Q[n]) - A[n] // Q[n])
            check(M % diff.denominator == 0, "changed components only at top-band primes of the reset")
        log2M = math.log2(M)
        check(M.bit_length() - 1 <= log2M < M.bit_length(), "log2 M consistent with the bit length")
        print(f"  [exact] block [{ni}, {nnext}): {len(Pset)} primes in ({ni // 2}, {ni}], log2 M = {log2M:.3f} [float],"
              f" offset |j| = {abs(jj)} ({tries} tries), excluded residues {excl};"
              f" max n*||x~_n|| = {float(maxdist):.4f}")
        return states[nnext - 1]

    last = block(240, 360, None)
    block(360, 540, last)


# ===========================================================================
# G4
# ===========================================================================
def section_g4():
    head("G4  sqrt(2), sqrt(3), sqrt(5)/phi, e")
    # Proposition 4.2: block-doubling identity
    for D in (2, 3, 5):
        for N in range(1, 301):
            xN = math.isqrt(D * 4 ** N)
            x2N = math.isqrt(D * 16 ** N)
            EN = D * 4 ** N - xN * xN
            E2N = D * 16 ** N - x2N * x2N
            tN = x2N - (xN << N)
            check(0 <= tN < (1 << N), "0 <= t_N < 2^N")
            check(EN >= 1 and E2N >= 1, "E_N >= 1")
            check((xN * tN << (N + 1)) + tN * tN + E2N == (EN << (2 * N)), "block-doubling identity")
            wE, wx, wt, wE2 = naf_weight(EN), naf_weight(xN), naf_weight(tN), naf_weight(E2N)
            check(wE <= wx * wt + wt * (wt + 1) // 2 + wE2, "signed-weight propagation")
            check(naf_weight(xN * xN) <= wx * (wx + 1) // 2, "w(x^2) <= w(x)(w(x)+1)/2")
            wD = naf_weight(D)
            check(wE <= wD + naf_weight(xN * xN) and naf_weight(xN * xN) <= wD + wE, "w(E) vs w(x^2) within w(D)")
    print("  [exact] 2^(N+1) x_N t_N + t_N^2 + E_2N = 4^N E_N and the signed-weight inequalities,"
          " D in {2,3,5}, N <= 300")
    # Lemma 4.1: signed support versus transitions on prefixes
    NN = 4096

    def digits_sqrt(D, N):
        x = math.isqrt(D * 4 ** N)
        ip = math.isqrt(D)
        frac = x - (ip << N)
        return [(frac >> (N - j)) & 1 for j in range(1, N + 1)]

    def digits_phi(N):
        y = math.isqrt(5 * 4 ** N)
        z = ((1 << N) + y) >> 1
        frac = z - (1 << N)
        return [(frac >> (N - j)) & 1 for j in range(1, N + 1)]

    def sigma_profile(bits):
        INF = 10 ** 9
        dp = {-1: 0, 0: 0, 1: 0}
        out = []
        for dg in bits:
            nd = {-1: INF, 0: INF, 1: INF}
            for dl, cst in dp.items():
                for dn in (-1, 0, 1):
                    a = dg + 2 * dl - dn
                    if -1 <= a <= 1:
                        c2 = cst + (a != 0)
                        if c2 < nd[dn]:
                            nd[dn] = c2
            dp = nd
            out.append(min(dp.values()))
        return out

    for name, bits in (("sqrt2", digits_sqrt(2, NN)), ("sqrt3", digits_sqrt(3, NN)), ("phi", digits_phi(NN))):
        sig = sigma_profile(bits)
        chi = 0
        ones = 0
        for N in range(1, NN + 1):
            if N >= 2 and bits[N - 1] != bits[N - 2]:
                chi += 1
            ones += bits[N - 1]
            sN = sig[N - 1]
            check(chi <= 3 * sN + 1, "chi <= 3 sigma + 1")
            check(sN <= chi, "sigma <= chi (witness delta_m = -d_m, delta_(N+1) = -d_N)")
        print(f"  [exact] {name}: chi <= 3 sigma_free + 1 and sigma_free <= chi for all prefixes N <= {NN};"
              f" [finite] at N = {NN}: sigma/N = {sig[-1] / NN:.4f}, chi/N = {chi / NN:.4f}, ones/N = {ones / NN:.4f}")

    # Theorem 4.3: band law for e_K
    KMAX = 400
    E = [1] * (KMAX + 1)
    fact = [1] * (KMAX + 1)
    for j in range(1, KMAX + 1):
        E[j] = j * E[j - 1] + 1
        fact[j] = fact[j - 1] * j
    pr = sieve_primes(KMAX)
    eK = Fr(0)
    cnt = 0
    drops = []
    for K in range(0, KMAX + 1):
        eK += Fr(1, fact[K])
        check(eK == Fr(E[K], fact[K]), "e_K = E_K / K!")
        if K % 2 == 0:
            check(E[K] % 2 == 1 and vp(eK.denominator, 2) == vp(fact[K], 2) if K >= 2 else True,
                  "K even: E_K odd, v_2(den e_K) = v_2(K!)")
        for p in pr:
            if p > K:
                break
            if p * p <= K:
                continue
            m = K // p
            i = K - m * p
            num, den = eK.numerator, eK.denominator
            v = vp(den, p)
            if E[i] % p != 0:
                check(v == m, "v_p(den e_K) = floor(K/p) when p does not divide E_(K - mp)")
                lhs = (num % p) * pow((den // p ** m) % p, -1, p) % p
                rhs = ((-1) ** m * E[i] * pow(fact[i] * fact[m] % p, -1, p)) % p
                check(lhs == rhs, "p^m e_K = (-1)^m e_(K-mp)/m! mod p")
            else:
                check(v < m, "drop for e: v_p < m when p | E_(K-mp)")
                drops.append((K, p))
            cnt += 1
    for j in range(1, 60):
        # E_j = floor(e j!) using a certified rational enclosure of e
        lo = sum(Fr(1, fact[k]) for k in range(0, 80))
        hi = lo + Fr(2, fact[80])
        check(math.floor(lo * fact[j]) == E[j] == math.floor(hi * fact[j]), "E_j = floor(e j!)")
    print(f"  [exact] band law for e_K on {cnt} pairs (K <= {KMAX}, sqrt(K) < p <= K);"
          f" {len(drops)} drop events, first: {drops[:4]}")
    print("  [exact] E_j = floor(e j!) for 1 <= j < 60; K even => E_K odd and v_2(den e_K) = v_2(K!)")


def main():
    section_g1()
    section_g1_perturbation()
    section_g2()
    section_g3()
    section_g4()
    head("Summary")
    print(f"  {CHECKS[0]} assertions passed in {time.time() - T0:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
