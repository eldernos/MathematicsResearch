#!/usr/bin/env python3
"""Phase 23, Track E: classical correlations, the 2-adic peeling of E_+, and ln 2.

Companion to notes/phase23/classical-correlations-and-log2.md.  Standard library
only; exits 0 when every assertion holds.  Run:  python -B scripts/phase23_classical.py

Sections
  P   2-adic structure of a_+(n) = (1 - v_2(n)) tau_odd(n): parity = squares,
      a_+(k^2) = lambda(k) mod 4, residue 2 mod 4 and 2 vs 6 mod 8, the
      counts N_j(X) of 2^j-indivisible coefficients; the peeling identity
      E_+ = sum 2^(-k^2) + 2 B_1 and finite checks of the K_2 transfer.
  C   Shifted correlations: exact p-adic local factors, the 2-adic ratio
      rho(h) (= -1/3 for every odd h), r-point ratios, the singular series
      S_r of the divisor lattice with rational enclosures, finite ratios.
  T   Raw-tail second moments of E and E_+ (diagonal / off-diagonal split).
  M   Mod-4 mark correlations of U = odd(tau) at consecutive shifts.
  L   ln 2: Glaisher-Wieferich numerator law, top-band numerator residues,
      the Weyl-sum form of D^+ < 1, the degree-2 transition minorant,
      finite transition counts.
  B   Consistency of the missing-estimate map with the fixed 50-constant roster.

Labels in the printout:
  [exact]   integer / rational arithmetic (a proof of the displayed identity);
  [encl]    rigorous rational/integer enclosure of an infinite product;
  [float]   floating-point evaluation of an exact formula (not certified);
  [finite]  finite measurement (bears on no limit).
"""

import math
import operator
import sys
import time
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


# ---------------------------------------------------------------- sieve
X = 1 << 20                 # main range n <= X
NMAX = X + 4096             # margin for shifts and tails


def build_tables(n_max):
    s = bytearray([1]) * (n_max + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n_max ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    primes = [i for i in range(n_max + 1) if s[i]]
    spf = list(range(n_max + 1))
    for p in reversed([q for q in primes if q * q <= n_max]):
        spf[p * p::p] = [p] * len(range(p * p, n_max + 1, p))
    tau = [0] * (n_max + 1)
    tau[1] = 1
    ex = [0] * (n_max + 1)
    rest = [1] * (n_max + 1)
    om = [0] * (n_max + 1)          # Omega(n)
    for n in range(2, n_max + 1):
        p = spf[n]
        m = n // p
        if m % p == 0:
            ex[n] = ex[m] + 1
            rest[n] = rest[m]
        else:
            ex[n] = 1
            rest[n] = m
        tau[n] = tau[rest[n]] * (ex[n] + 1)
        om[n] = om[m] + 1
    ap = [0] * (n_max + 1)
    for n in range(1, n_max + 1):
        e = (n & -n).bit_length() - 1
        ap[n] = (1 - e) * (tau[n] // (e + 1))
    return primes, tau, om, ap, spf


PRIMES, TAU, OM, AP, SPF = build_tables(NMAX)
PRIME_SET = set(p for p in PRIMES if p < 5000)


def v2(k):
    return (k & -k).bit_length() - 1


def vp(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def odd_part(k):
    return k >> v2(k)


def _factor(n):
    out = []
    while n > 1:
        q = SPF[n]
        out.append(q)
        n //= q
    return out


def isqrt_exact(n):
    r = math.isqrt(n)
    return r if r * r == n else None


def dc_sum(a, lo, hi):
    """Integer sum_{lo<=n<hi} a[n] 2^(hi-1-n) by divide and conquer."""
    if hi - lo <= 64:
        s = 0
        for n in range(lo, hi):
            s = 2 * s + a[n]
        return s
    mid = (lo + hi) // 2
    return (dc_sum(a, lo, mid) << (hi - mid)) + dc_sum(a, mid, hi)


def frac_digits(coef, n_dig, guard=96, nonneg=False):
    """Binary digits 1..n_dig of frac(sum_{n>=1} coef[n] 2^-n), certified.

    Every coefficient array used here satisfies |coef[n]| <= tau(n) + 4 <= 2 sqrt(n) + 4 for
    ALL n >= 1 (a_+, 2 floor(a_+/2), 4 floor(a_+/4), floor(a_+/2), a_+ mod 4, 1_square).  The
    omitted tail n > M = n_dig + guard is therefore, in units of 2^-M, at most
    sum_{k>=1} (2 sqrt(M+k) + 4) 2^-k <= 2 sqrt(2M) + 4 + sum_{k>M} (2 sqrt(2k) + 4) 2^-k
    < 2 sqrt(2M) + 5 < 2^15 (asserted below); digits 1..n_dig are certain when guard bits
    n_dig+1 .. M-17 are not a single run."""
    M = n_dig + guard
    check(2 * math.isqrt(2 * M) + 7 < 1 << 15, "tail bound 2 sqrt(2M) + 5 < 2^15")
    S = dc_sum(coef, 1, M + 1)
    F = S % (1 << M)
    bits = bin(F)[2:].zfill(M)
    g = bits[n_dig:M - 17]
    if nonneg:      # tail >= 0: only a carry (guard bits all 1) could change digits 1..n_dig
        check("0" in g, "guard bits not all 1")
    else:
        check("0" in g and "1" in g, "guard bits not a single run")
    return bits


def ext_discrepancy(bits, N):
    """Extreme discrepancy of {2^n x}, 0<=n<N, from the digit string (53-bit points)."""
    pts = sorted(int(bits[n:n + 53], 2) / 2.0 ** 53 for n in range(N))
    a = max((i + 1) / N - x for i, x in enumerate(pts))
    b = max(x - i / N for i, x in enumerate(pts))
    return a + b


# =============================================================== P
def section_P():
    head("P. 2-adic structure of a_+ and the peeling of E_+")
    ap, tau, om = AP, TAU, OM

    # alternating divisor sum, n <= 3000
    for n in range(1, 3001):
        s = sum((1 if d % 2 else -1) for d in range(1, n + 1) if n % d == 0)
        check(s == ap[n], "a_+ = sum_{d|n} (-1)^(d-1)")

    # parity: a_+(n) mod 2 = [n square]; a_+(k^2) = lambda(k) = tau(k^2) mod 4
    sqflag = bytearray(X + 1)
    for k in range(1, math.isqrt(X) + 1):
        sqflag[k * k] = 1
    check(all((ap[n] & 1) == sqflag[n] for n in range(1, X + 1)), "a_+ odd iff square")
    CHECKS[0] += X - 1
    nsq = 0
    for k in range(1, math.isqrt(X) + 1):
        n = k * k
        nsq += 1
        lam = -1 if om[k] % 2 else 1
        check(om[n] == 2 * om[k], "Omega(k^2) = 2 Omega(k)")
        check((ap[n] - lam) % 4 == 0, "a_+(k^2) = lambda(k) mod 4")
        check((tau[n] - lam) % 4 == 0, "tau(k^2) = lambda(k) mod 4")
    check(nsq == 1024, "1024 squares up to 2^20")
    print(f"[exact] a_+(n) mod 2 = [n square] and a_+(k^2) = tau(k^2) = lambda(k) (mod 4) "
          f"for all n <= 2^20 ({nsq} squares)")

    # chi_4(a_+(n)) summed = Liouville summatory L(sqrt X)
    def chi4(a):
        r = a % 4
        return 1 if r == 1 else (-1 if r == 3 else 0)
    lam_k = [0] + [(-1 if (om[k] % 2) else 1) for k in range(1, 1025)]
    lhs = 0
    marks_x = {10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, X}
    for n in range(1, X + 1):
        if sqflag[n]:
            lhs += chi4(ap[n])
        else:
            check(ap[n] % 2 == 0, "non-square: chi_4 = 0")
        if n in marks_x:
            check(lhs == sum(lam_k[1:math.isqrt(n) + 1]), "sum chi_4(a_+(n)) = L(sqrt X)")
    print(f"[exact] sum_(n<=X) chi_4(a_+(n)) = L(floor sqrt X) at X = 10^3..10^6, 2^20; "
          f"L(1024) = {sum(lam_k[1:1025])}")

    # v_2(a_+(n)) = 1: exact characterization and the mod 8 sign rule
    cnt2 = 0
    c8 = {2: 0, 6: 0}
    alpha_tally = {}
    for n in range(1, X + 1):
        a = ap[n]
        if a == 0 or v2(abs(a)) != 1:
            continue
        cnt2 += 1
        c8[a % 8] += 1
        e = v2(n)
        m = n >> e
        sq = isqrt_exact(m) is not None
        if sq:
            check(e % 4 == 3, "square odd part with v_2(a_+)=1 forces e = 3 mod 4")
            continue
        check(e == 0 or (e % 2 == 0), "e in {0, 2, 4, ...}")
        # exactly one prime with odd exponent alpha, alpha = 1 mod 4
        fac = {}
        w = m
        while w > 1:
            q = SPF[w]
            fac[q] = fac.get(q, 0) + 1
            w //= q
        odd_exp = [al for al in fac.values() if al % 2]
        check(len(odd_exp) == 1 and odd_exp[0] % 4 == 1, "m = p^alpha s^2, alpha = 1 mod 4")
        alpha = odd_exp[0]
        alpha_tally[alpha] = alpha_tally.get(alpha, 0) + 1
        sign_e = 1 if e % 4 == 0 else -1                 # (1-e) mod 4 for e even
        lam_s = -1 if ((om[m] - alpha) // 2) % 2 else 1  # lambda(s), Omega(m) = alpha + 2 Omega(s)
        check(((a // 2) - sign_e * chi4_odd((alpha + 1) // 2) * lam_s) % 4 == 0,
              "a_+/2 = (1-e) ((alpha+1)/2) lambda(s) mod 4")
    print(f"[exact] for all n <= 2^20 with v_2(a_+(n)) = 1: n = 2^e p^alpha s^2 (e in {{0,2,4,..}}, "
          f"alpha = 1 mod 4) or e = 3 mod 4 with square odd part;")
    print(f"        a_+(n)/2 = (1-e) ((alpha+1)/2) lambda(s) mod 4; exponent tally alpha: {dict(sorted(alpha_tally.items()))}")
    LX = math.log(X)
    # PNT-scale main terms with the true scale log(X / (2^e s^2)), and with exact prime counts
    pc = [0] * (X + 1)
    is_p = bytearray(X + 1)
    for q in PRIMES:
        if q > X:
            break
        is_p[q] = 1
    run = 0
    for i in range(X + 1):
        run += is_p[i]
        pc[i] = run
    mt = mt_signed = 0.0
    ex_tot = ex_signed = 0
    for e in [0] + list(range(2, 21, 2)):
        se = 1 if e % 4 == 0 else -1
        for s_ in range(1, math.isqrt(X >> e) + 1, 2):
            Y = (X >> e) // (s_ * s_)
            lam = -1 if om[s_] % 2 else 1
            # odd primes p <= Y not dividing s_ (alpha = 1 terms)
            cnt_p = pc[Y] - (1 if Y >= 2 else 0) - sum(1 for q in set(_factor(s_)) if q <= Y)
            ex_tot += cnt_p
            ex_signed += se * lam * cnt_p
            if Y >= 3:
                mt += Y / math.log(Y)
                mt_signed += se * lam * Y / math.log(Y)
    n_alpha1 = alpha_tally.get(1, 0)
    print(f"[finite] #{{n<=2^20: a_+ = 2 mod 4}} = {cnt2}; ratio to X/log X = {cnt2 / (X / LX):.4f} "
          f"(limit pi^2/6 = {math.pi ** 2 / 6:.4f}); ratio to sum_(e,s) Y/log Y, "
          f"Y = X/(2^e s^2): {cnt2 / mt:.4f}")
    check(ex_tot == n_alpha1, "alpha = 1 count = sum_(e,s) #{odd p <= X/(2^e s^2), p not | s}")
    print(f"[exact] the alpha = 1 part ({n_alpha1}) equals sum_(e in 0,2,4..; s odd) #{{odd p <= X/(2^e s^2): p not | s}}")
    print(f"[finite] #(a_+ = 2 mod 8) = {c8[2]}, #(a_+ = 6 mod 8) = {c8[6]}, ratio "
          f"{c8[2] / c8[6]:.4f} (limit 7/3 = {7 / 3:.4f}); signed main term / total main term = "
          f"{mt_signed / mt:.4f} vs observed {(c8[2] - c8[6]) / cnt2:.4f} (limit 2/5)")
    check(abs(Fr(7, 60) + Fr(1, 20) - Fr(1, 6)) == 0, "7/60 + 1/20 = 1/6")
    check(Fr(5, 4) * Fr(4, 5) == 1 and Fr(1, 15) - Fr(4, 15) + 1 == Fr(4, 5), "2-adic weights 4/5")

    # residue distribution mod 8 and the counts N_j(X)
    res = [0] * 8
    vcount = [0] * 64
    for n in range(1, X + 1):
        t = ap[n]
        res[t % 8] += 1
        if t:
            vcount[v2(abs(t))] += 1
    print(f"[finite] residues of a_+(n) mod 8 for n <= 2^20: {res}")
    Nj = [sum(vcount[:j]) for j in range(1, 6)]
    check(Nj[2] == sum(1 for n in range(1, 1 << 16) if ap[n] % 8) + sum(
        1 for n in range(1 << 16, X + 1) if ap[n] % 8), "N_3 cross-check")
    check(Nj[0] == 1024, "N_1(X) = floor sqrt X")
    check(Nj[1] == 1024 + cnt2, "N_2 = squares + v_2 = 1")
    # lower bound for N_j via odd squarefree n with exactly j-1 prime factors: a_+ = 2^(j-1)
    print("[finite] N_j(2^20) = #{n <= 2^20 : 2^j does not divide a_+(n)}, j = 1..5: "
          + ", ".join(str(v) for v in Nj))
    print("         density N_j/X: " + ", ".join(f"{v / X:.4f}" for v in Nj))
    for p, q in ((3, 5), (3, 7), (5, 7)):
        check(ap[p * q] == 4, "a_+(pq) = 4")
    check(ap[3 * 5 * 7] == 8 and ap[3] == 2, "a_+(odd squarefree with k primes) = 2^k")

    # peeling identity at finite truncation: sum (a mod 2^j) 2^(M-n) etc.
    M = 4000
    lhs = sum((ap[n] - 2 * (ap[n] // 2)) << (M - n) for n in range(1, M + 1))
    rhs = sum(1 << (M - k * k) for k in range(1, math.isqrt(M) + 1))
    check(lhs == rhs, "E_+ - 2 B_1 = sum 2^(-k^2) (truncated, exact)")
    print("[exact] sum_(n<=4000) (a_+(n) - 2 floor(a_+(n)/2)) 2^-n = sum_(k^2<=4000) 2^(-k^2)")
    for n in range(1, 20001):
        check((TAU[n] - (TAU[n] & 1)) // 2 - ap[n] // 2 == (TAU[n // 2] if n % 2 == 0 else 0),
              "floor(tau/2) - floor(a_+/2) = tau(n/2) [2|n]")
    print("[exact] floor(tau(n)/2) - floor(a_+(n)/2) = tau(n/2)[2|n] (n <= 20000), so B_1(tau) - B_1(a_+) = E(4)")

    # finite discrepancy checks of the K_2 transfer (SY-04 inequality)
    ND = 1 << 14
    c_E = [0] + [ap[n] for n in range(1, NMAX + 1)]
    c_E[0] = 0
    c_S = [0] * (NMAX + 1)
    for k in range(1, math.isqrt(NMAX) + 1):
        c_S[k * k] = 1
    c_2B1 = [0] + [2 * (ap[n] // 2) for n in range(1, NMAX + 1)]
    c_y2 = [0] + [ap[n] % 4 for n in range(1, NMAX + 1)]
    c_4B2 = [0] + [4 * (ap[n] // 4) for n in range(1, NMAX + 1)]
    c_B1 = [0] + [ap[n] // 2 for n in range(1, NMAX + 1)]
    for arr in (c_E, c_2B1, c_4B2, c_B1):
        arr[0] = 0
    bE = frac_digits(c_E, ND + 64)
    bS = frac_digits(c_S, ND + 64, nonneg=True)
    b2B = frac_digits(c_2B1, ND + 64)
    by2 = frac_digits(c_y2, ND + 64, nonneg=True)
    b4B = frac_digits(c_4B2, ND + 64)
    bB1 = frac_digits(c_B1, ND + 64)
    print("[finite] extreme discrepancies D_N (53-bit points; finite data):")
    print("         N      E_+      S=sum2^-k^2  2B_1     B_1      y_2      4B_2")
    tol = 1e-9
    for N in (1 << 10, 1 << 12, 1 << 14):
        dE, dS, d2B, dy2, d4B, dB1 = (ext_discrepancy(b, N) for b in (bE, bS, b2B, by2, b4B, bB1))
        print(f"         {N:<6d} {dE:.5f}  {dS:.5f}      {d2B:.5f}  {dB1:.5f}  {dy2:.5f}  {d4B:.5f}")
        check(abs(dE - d2B) <= 1 - dS + tol, "SY-04: |D(E_+) - D(2B_1)| <= 1 - D(S)")
        check(abs(dE - d4B) <= 1 - dy2 + tol, "SY-04: |D(E_+) - D(4B_2)| <= 1 - D(y_2)")
        check(abs(d2B - dB1) <= 1 / N + tol, "|D(2x) - D(x)| <= 1/N")
    # the K_2 lemma bound for S at N = 2^14 with L = 7
    N, L = 1 << 14, 7
    bound = Fr(L * math.isqrt(N + L), N) + Fr(1, 2 ** L)
    check(1 - ext_discrepancy(bS, N) <= float(bound) + tol, "1 - D_N(S) <= L sqrt(N+L)/N + 2^-L")
    print(f"[exact] K_2 lemma bound at N=2^14, L=7: 1 - D_N(S) <= {float(bound):.5f}")


# =============================================================== C
def poly_geom_sum(vals, x):
    """sum_{k>=0} P(k) x^k for a polynomial P given by values P(0..d) (d >= deg P)."""
    diffs = list(vals)
    total = Fr(0)
    i = 0
    while diffs:
        total += diffs[0] * x ** i / (1 - x) ** (i + 1)
        diffs = [diffs[t + 1] - diffs[t] for t in range(len(diffs) - 1)]
        i += 1
    return total


def local_E(p, S, g, deg, s=0):
    """E over n in Z_p (Haar) of prod_{h in S} g(s + v_p(n + h))^{S[h]}; g a polynomial of degree deg."""
    if len(S) == 1:
        (_, m), = S.items()
        d = m * deg + 1
        vals = [Fr(g(s + k)) ** m for k in range(d + 1)]
        x = Fr(1, p)
        return (1 - x) * poly_geom_sum(vals, x)
    tot = Fr(0)
    for c in range(p):
        grp = {}
        out = Fr(1)
        for h, m in S.items():
            if (c + h) % p == 0:
                k = (c + h) // p
                grp[k] = grp.get(k, 0) + m
            else:
                out *= Fr(g(s)) ** m
        if grp:
            out *= local_E(p, grp, g, deg, s + 1)
        tot += out
    return tot / p


def G_TAU(v):
    return 1 + v


def G_PLUS(v):
    return 1 - v


def shifts(hs):
    S = {}
    for h in hs:
        S[h] = S.get(h, 0) + 1
    return S


def sigma_m1(h):
    return Fr(sum(Fr(1, d) for d in range(1, h + 1) if h % d == 0))


_TAIL_CACHE = {}


def euler_tail_enclosure(r, p_lo, P=200000, scale_bits=96):
    """Rigorous [lo, hi] for prod_{p >= p_lo} (1-1/p)^(r-1) (1 + (r-1)/p), p_lo >= r."""
    key = (r, p_lo, P, scale_bits)
    if key not in _TAIL_CACHE:
        _TAIL_CACHE[key] = _euler_tail(r, p_lo, P, scale_bits)
    return _TAIL_CACHE[key]


def _euler_tail(r, p_lo, P, scale_bits):
    one = 1 << scale_bits
    lo, hi = one, one
    for p in PRIMES:
        if p < p_lo:
            continue
        if p > P:
            break
        num = (p - 1) ** (r - 1) * (p + r - 1)
        den = p ** r
        lo = lo * num // den
        hi = -((-hi * num) // den)
    # tail p > P: factor in [1 - (r-1)^2/p^2, 1], product >= 1 - (r-1)^2/P
    t = Fr((r - 1) ** 2, P)
    return Fr(lo, one) * (1 - t), Fr(hi, one)


def section_C():
    head("C. Shifted correlations: local factors, 2-adic ratios, singular series")
    # validation: tau local factors (Ingham): (1-1/p)^2 E_p[(1+v)(1+v')] = (1-p^-2) sum_{j<=v_p(h)} p^-j
    for p in (2, 3, 5, 7):
        for h in range(1, 41):
            lhs = (1 - Fr(1, p)) ** 2 * local_E(p, shifts([0, h]), G_TAU, 1)
            rhs = (1 - Fr(1, p * p)) * sum(Fr(1, p ** j) for j in range(vp(h, p) + 1))
            check(lhs == rhs, "Ingham local factor")
    check(local_E(2, {0: 2}, G_TAU, 1) == 6 and local_E(2, {0: 2}, G_PLUS, 1) == 2,
          "E_2[(1+v)^2] = 6, E_2[(1-v)^2] = 2")
    check(local_E(2, {0: 1}, G_PLUS, 1) == 0 and local_E(2, {0: 1}, G_TAU, 1) == 2,
          "E_2[1-v] = 0 (no log in the mean)")
    print("[exact] local recursion reproduces Ingham's factors (1-p^-2) sum_{j<=v_p(h)} p^-j, "
          "p <= 7, h <= 40; E_2[1-v] = 0, E_2[(1-v)^2]/E_2[(1+v)^2] = 1/3")
    # rho(h)
    rho = {}
    for h in range(1, 17):
        rho[h] = local_E(2, shifts([0, h]), G_PLUS, 1) / local_E(2, shifts([0, h]), G_TAU, 1)
    for h in range(1, 17, 2):
        check(rho[h] == Fr(-1, 3), "rho(odd h) = -1/3")
    print("[exact] rho(h) = E_2[(1-v(n))(1-v(n+h))] / E_2[(1+v(n))(1+v(n+h))]:")
    print("         " + "  ".join(f"h={h}:{rho[h]}" for h in range(1, 9)))
    print("         " + "  ".join(f"h={h}:{rho[h]}" for h in (12, 16)))
    numer = {k: local_E(2, shifts([0, 2 ** k]), G_PLUS, 1) for k in range(0, 8)}
    denom = {k: local_E(2, shifts([0, 2 ** k]), G_TAU, 1) for k in range(0, 8)}
    for h in range(1, 65):
        k = vp(h, 2)
        check(local_E(2, shifts([0, h]), G_PLUS, 1) == numer[k], "2-adic factor depends on v_2(h) only")
    for k in range(0, 21):
        nk = local_E(2, shifts([0, 2 ** k]), G_PLUS, 1)
        dk = local_E(2, shifts([0, 2 ** k]), G_TAU, 1)
        check(nk == 2 - Fr(3, 2 ** k) and dk == 6 - Fr(3, 2 ** k), "closed forms 2-3/2^k, 6-3/2^k")
        check(nk / dk == Fr(2 ** (k + 1) - 3, 3 * (2 ** (k + 1) - 1)), "rho closed form")
    print("[exact] closed forms (k = v_2(h) <= 20): E_2[(1-v)(1-v')] = 2 - 3/2^k, E_2[(1+v)(1+v')] = 6 - 3/2^k,"
          " rho(h) = (2^(k+1) - 3) / (3 (2^(k+1) - 1))")
    print("[exact] numerator E_2[(1-v)(1-v')] by k = v_2(h): "
          + ", ".join(f"{k}:{numer[k]}" for k in range(8)))
    print("[exact] denominator E_2[(1+v)(1+v')] by k:      "
          + ", ".join(f"{k}:{denom[k]}" for k in range(8)))
    # leading constants c_+(h) = rho(h) (6/pi^2) sigma_{-1}(h)
    six_pi2 = 6 / math.pi ** 2
    print("[float] c_+(h) = rho(h) (6/pi^2) sigma_{-1}(h), the coefficient of log^2 X in C_+(h;X):")
    print("         " + "  ".join(f"h={h}:{float(rho[h] * sigma_m1(h)) * six_pi2:+.6f}" for h in range(1, 9)))
    # finite ratios
    ap, tau = AP, TAU
    print("[finite] sum_(n<=X) a_+(n)a_+(n+h) / sum_(n<=X) tau(n)tau(n+h) at X = 2^14, 2^17, 2^20:")
    cuts = (1 << 14, 1 << 17, 1 << 20)

    def prod_list(c, hs):
        out = c[1 + hs[0]:X + 1 + hs[0]]
        for h in hs[1:]:
            out = list(map(operator.mul, out, c[1 + h:X + 1 + h]))
        return out

    def ratio_rows(hs):
        pa, pt = prod_list(ap, hs), prod_list(tau, hs)
        return [sum(pa[:XX]) / sum(pt[:XX]) for XX in cuts], sum(pa)
    for h in range(1, 9):
        pa, pt = prod_list(ap, (0, h)), prod_list(tau, (0, h))
        out = [sum(pa[:XX]) / sum(pt[:XX]) for XX in cuts]
        if h % 2 == 1:
            check(sum(pa) < 0, "odd h: correlation negative")
        print(f"         h={h}: " + "  ".join(f"{v:+.4f}" for v in out) + f"   (rho = {float(rho[h]):+.4f})")
    # pointwise sign: odd h gives a_+(n)a_+(n+h) <= 0 for every n
    for h in (1, 3, 5, 7):
        check(all(ap[n] * ap[n + h] <= 0 for n in range(1, 1 << 16)), "pointwise sign, odd h")
    print("[exact] for odd h, a_+(n) a_+(n+h) <= 0 for every n (checked n < 2^16; proof: parity)")

    # r-point patterns: 2-adic ratio rho(h) and the singular series S(h) of the divisor lattice
    def singular_series(hs):
        r = len(hs)
        exact_part = Fr(1)
        for p in PRIMES:
            if p >= 60:
                break
            f = (1 - Fr(1, p)) ** r * local_E(p, shifts(hs), G_TAU, 1)
            if len({h % p for h in hs}) == r:
                check(f == (1 - Fr(1, p)) ** (r - 1) * (1 + Fr(r - 1, p)), "generic local factor")
            exact_part *= f
        check(max(hs) - min(hs) < 61, "differences below 61")
        lo, hi = euler_tail_enclosure(r, 61)
        return exact_part * lo, exact_part * hi

    def rho_of(hs):
        S = shifts(hs)
        return local_E(2, S, G_PLUS, 1) / local_E(2, S, G_TAU, 1)

    patterns = []
    for r in range(2, 8):
        patterns.append(("consecutive", tuple(range(r))))
    for r in range(2, 8):
        patterns.append(("step 4", tuple(4 * j for j in range(r))))
    for r in range(3, 8):
        patterns.append(("step 2", tuple(2 * j for j in range(r))))
    for r in range(4, 8):
        patterns.append(("{0,1} mod 4", (0, 1, 4, 5, 8, 9, 12)[:r]))
    print("[encl] singular series S(h) = prod_p (1-1/p)^r E_p[prod_j (1+v_p(n+h_j))] (tau; the independent-")
    print("       shift model gives 1) and the a_+ analogue rho(h) S(h); log^r X coefficients:")
    S_encl = {}
    for name, hs in patterns:
        lo, hi = singular_series(hs)
        rh = rho_of(hs)
        S_encl[hs] = (lo, hi)
        if all(any((h + c) % 4 == 2 for h in hs) for c in range(4)):
            check(rh == 0, "pattern covering 2 mod 4 for every n: rho = 0")
            check(all(math.prod(AP[n + h] for h in hs) == 0 for n in range(1, 4097)),
                  "product vanishes identically")
        a1, a2 = sorted((rh * lo, rh * hi))
        print(f"         {name:12s} r={len(hs)} h={str(hs):24s} S in [{float(lo):.6f}, {float(hi):.6f}]  "
              f"rho = {str(rh):12s} rho*S ~ {float(a1):+.6f}")
    check(S_encl[(0, 1)][0] <= 6 / math.pi ** 2 <= S_encl[(0, 1)][1], "S(0,1) = 6/pi^2 inside enclosure")
    print("[finite] 3-point ratios sum prod a_+(n+h_j) / sum prod tau(n+h_j) at X = 2^14, 2^17, 2^20:")
    for hs in ((0, 1, 2), (0, 2, 4), (0, 4, 8)):
        out, _ = ratio_rows(hs)
        print(f"         h={hs}: " + "  ".join(f"{v:+.4f}" for v in out) + f"   (rho = {float(rho_of(hs)):+.4f})")
    # generic p: 1 - (r-1)^2/p^2 <= f_p <= 1
    for r in range(2, 8):
        for p in (11, 13, 101):
            f = (1 - Fr(1, p)) ** (r - 1) * (1 + Fr(r - 1, p))
            check(1 - Fr((r - 1) ** 2, p * p) <= f <= 1, "generic factor bounds")
    # CRT density of divisor events vs independent model: a small exact table
    print("[exact] CRT lattice: dens{d_j | n+h_j} = [gcd(d_i,d_j) | h_j-h_i] / lcm(d) (checked by "
          "enumeration over a period for all d_j <= 12, shifts (0,1,2))")
    for d1 in range(1, 13):
        for d2 in range(1, 13):
            for d3 in (1, 2, 3, 4, 6):
                L = math.lcm(d1, d2, d3)
                cnt = sum(1 for n in range(L) if n % d1 == 0 and (n + 1) % d2 == 0 and (n + 2) % d3 == 0)
                ok = math.gcd(d1, d2) == 1 and math.gcd(d2, d3) == 1 and 2 % math.gcd(d1, d3) == 0
                check(Fr(cnt, L) == (Fr(1, L) if ok else 0), "CRT density")
    return rho, S_encl


# =============================================================== T
def section_T():
    head("T. Raw-tail second moments: T_n = sum_k c(n+k) 2^-k for c = tau and c = a_+")
    SC = 1 << 64
    out = {}
    for name, c in (("tau", TAU), ("a_+", AP)):
        T = [0] * (NMAX + 1)
        t = 0
        for n in range(NMAX, 0, -1):          # T_{n-1} = (T_n + c(n)) / 2
            T[n] = t                           # store T_n (scaled)
            t = (t + c[n] * SC) >> 1
        res = []
        for XX in (1 << 14, 1 << 17, 1 << 20):
            s1 = sum(T[n] for n in range(1, XX + 1))
            s2 = sum(T[n] * T[n] for n in range(1, XX + 1))
            c2 = sum(c[n] * c[n] for n in range(1, XX + 1))
            # diagonal sum_k 4^-k sum_n c(n+k)^2, truncated at k = 40 (remainder < 4^-40 of the total)
            dg = Fr(0)
            run = sum(c[n] ** 2 for n in range(2, XX + 2))
            for k in range(1, 41):
                dg += Fr(run, 4 ** k)
                run += c[XX + k + 1] ** 2 - c[k + 1] ** 2
            mean = Fr(s1, SC * XX)
            m2 = Fr(s2, SC * SC * XX)
            var = m2 - mean * mean
            offd = m2 - dg / XX
            res.append((XX, float(mean), float(m2), float(var), float(Fr(c2, XX)),
                        float(dg / XX), float(offd)))
        out[name] = res
    # identity a(n) = 2 T_{n-1} - T_n holds by construction; check unconditional sandwich
    print("[finite] X       mean T     E[T^2]      Var T      E[c^2]     diag      off-diag  "
          "off/diag  Var/E[c^2]")
    for name in ("tau", "a_+"):
        print(f"  c = {name}")
        for (XX, mean, m2, var, c2, dg, offd) in out[name]:
            check(m2 <= c2 * 1.01 + 1, "E[T^2] <= E[c^2] (Cauchy-Schwarz, up to boundary)")
            check(m2 >= c2 / 10 * 0.99, "E[T^2] >= E[c^2]/10 (from c(n) = 2T_{n-1} - T_n)")
            print(f"  2^{XX.bit_length() - 1:<4d} {mean:9.4f} {m2:10.3f} {var:10.3f} {c2:10.3f} "
                  f"{dg:9.3f} {offd:+9.3f} {offd / dg:+8.4f}  {var / c2:8.4f}")
    vt = [r[3] for r in out["tau"]]
    vp_ = [r[3] for r in out["a_+"]]
    print("[finite] Var(T^+)/Var(T) at X = 2^14, 2^17, 2^20: "
          + ", ".join(f"{a / b:.4f}" for a, b in zip(vp_, vt)) + "   (limit 1/3)")
    six = 6 / math.pi ** 2
    lx = math.log(X)
    pred_tau = sum(2 / 3 / 2 ** h * six * float(sigma_m1(h)) for h in range(1, 61))
    pred_plus = 0.0
    for h in range(1, 61):
        k = vp(h, 2)
        rh = Fr(2 ** (k + 1) - 3, 3 * (2 ** (k + 1) - 1))
        pred_plus += 2 / 3 / 2 ** h * six * float(rh * sigma_m1(h))
    print(f"[float] off-diagonal leading term (2/3) sum_h 2^-h c(h) log^2 X at X = 2^20 (c(h) from Ingham for tau,"
          f" from rho(h) for a_+, conditional on (H2)): tau {pred_tau * lx * lx:+.2f} (observed "
          f"{out['tau'][-1][6]:+.2f}), a_+ {pred_plus * lx * lx:+.2f} (observed {out['a_+'][-1][6]:+.2f})")
    print(f"[float] coefficients: (2/3) sum_h 2^-h c(h) = {pred_tau:.6f} (tau), {pred_plus:.6f} (a_+)")
    closed = 4 / math.pi ** 2 * sum(1 / (d * (2 ** d - 1)) for d in range(1, 80))
    check(abs(closed - pred_tau) < 1e-12, "kappa_tau = (4/pi^2) sum_d 1/(d(2^d-1))")
    # Lemma 3.2: sum_{n<=X} tau(n)tau(n+h) <= 4 sigma_{-1}(h) X (1 + log(2X)/2)^2 + 8X for 1 <= h <= X
    worst = 0.0
    nl = 0
    for XX, hs in ((1 << 10, range(1, (1 << 10) + 1)),
                   (1 << 18, list(range(1, 13)) + [1 << 17, 1 << 18])):
        for h in hs:
            lhs = sum(TAU[n] * TAU[n + h] for n in range(1, XX + 1))
            rhs = 4 * float(sigma_m1(h)) * XX * (1 + math.log(2 * XX) / 2) ** 2 + 8 * XX
            check(lhs <= rhs, "Lemma 3.2 uniform two-point bound")
            worst = max(worst, lhs / rhs)
            nl += 1
    print(f"[exact] Lemma 3.2 bound checked for {nl} (X, h): X = 2^10, all h <= X; X = 2^18, h <= 12 and"
          f" h = 2^17, 2^18 (max lhs/rhs = {worst:.4f})")
    print(f"[float] kappa_tau = (4/pi^2) sum_d 1/(d(2^d-1)) = {closed:.6f}")
    print(f"[float] predicted leading constants: Var(T)/log^3 X -> 1/(3 pi^2) = {1 / (3 * math.pi ** 2):.6f}, "
          f"Var(T^+)/log^3 X -> 1/(9 pi^2) = {1 / (9 * math.pi ** 2):.6f}")


# =============================================================== M
def chi4_odd(u):
    return 1 if u % 4 == 1 else -1


def psi(v):
    """chi_4 of odd(v+1): the local contribution of v_p(m) = v to chi_4(odd(tau(m)))."""
    return chi4_odd(odd_part(v + 1))


def section_M():
    head("M. Mod-4 mark correlations of U(m) = odd(tau(m)) at consecutive shifts")
    # q_p = P(psi(v_p) = -1), p odd, as truncated series with tail bound
    def q_bounds(p):
        K = max(8, int(40 / math.log10(p)) + 2)
        x = Fr(1, p)
        s = sum((1 - x) * x ** k for k in range(K) if psi(k) == -1)
        return s, s + x ** K
    # p = 2: exact local joint law of (psi(v_2(n+j)))_{j<r} by enumeration mod 2^K
    K2 = 16
    MOD = 1 << K2
    psi_tab = [0] + [psi(v2(w)) for w in range(1, MOD)]
    cnt7 = {}
    bad = 0
    for n in range(MOD):
        if any((n + j) % MOD == 0 for j in range(7)):
            bad += 1
            continue
        key = tuple(psi_tab[(n + j) % MOD] for j in range(7))
        cnt7[key] = cnt7.get(key, 0) + 1
    law2 = {}
    for r in range(1, 8):            # marginals of the 7-shift law (excluded mass <= 7/2^K2)
        cnt = {}
        for key, v in cnt7.items():
            cnt[key[:r]] = cnt.get(key[:r], 0) + v
        law2[r] = (cnt, bad)
    q2 = sum(Fr(1, 2 ** (k + 1)) for k in range(80) if psi(k) == -1)     # + O(2^-80)
    # TV bounds
    print("[encl] TV distance between the true joint law of (chi_4(U(n+j)))_{j<r} and i.i.d. marks,")
    print("       upper bound sum_p TV_p, with TV_p = r q_p (1 - (1-q_p)^(r-1)) for odd p:")
    tvb = {}
    for r in range(2, 8):
        # p = 2 by enumeration
        cnt, bad = law2[r]
        tv2 = Fr(0)
        import itertools
        for key in itertools.product((1, -1), repeat=r):
            pt = Fr(cnt.get(key, 0), MOD)
            pm = Fr(1)
            for z in key:
                pm *= q2 if z == -1 else 1 - q2
            tv2 += abs(pt - pm)
        tv2 = tv2 / 2 + Fr(bad, MOD) + r * Fr(1, MOD)
        tv_odd = Fr(0)
        for p in PRIMES:
            if p == 2:
                continue
            if p > 1000:
                break
            qlo, qhi = q_bounds(p)
            tv_odd += r * qhi * (1 - (1 - qhi) ** (r - 1))
        tail = Fr(r * (r - 1), 3 * 1000 ** 3)
        tvb[r] = (tv2, tv_odd + tail)
        print(f"         r={r}: TV_2 <= {float(tv2):.5f}   sum_(p odd) TV_p <= {float(tv_odd + tail):.5f}"
              f"   total <= {float(tv2 + tv_odd + tail):.5f}")
    # exact Fourier description and actual TV (float evaluation of the exact product formula)
    qs = []
    for p in PRIMES:
        if p == 2:
            continue
        if p > 20000:
            break
        qlo, qhi = q_bounds(p) if p < 1000 else (Fr(0), Fr(0))
        qs.append(float(qlo) if p < 1000 else (1 - 1 / p) / p ** 2)
    import itertools
    print("[float] actual TV of the limiting joint law vs i.i.d. marks (exact Fourier formula, "
          "odd primes <= 20000):")
    for r in (2, 3, 4, 5, 6, 7):
        cnt, bad = law2[r]
        # moments at p = 2 for each subset A
        m2 = {}
        for A in itertools.product((0, 1), repeat=r):
            s = 0
            for key, v in cnt.items():
                pr = 1
                for j in range(r):
                    if A[j]:
                        pr *= key[j]
                s += pr * v
            m2[A] = s / (MOD - bad)
        modd = {a: math.prod(1 - 2 * a * q for q in qs) for a in range(r + 1)}
        t1 = m2[tuple([1] + [0] * (r - 1))] * modd[1]
        tv = 0.0
        for eps in itertools.product((1, -1), repeat=r):
            pt = pm = 0.0
            for A in itertools.product((0, 1), repeat=r):
                sgn = math.prod(eps[j] for j in range(r) if A[j])
                a = sum(A)
                pt += m2[A] * modd[a] * sgn
                pm += t1 ** a * sgn
            tv += abs(pt - pm) / 2 ** r
        print(f"         r={r}: TV = {tv / 2:.5f}")
    t = (1 - 2 * float(q2)) * math.prod(1 - 2 * q for q in qs)
    print(f"[float] E chi_4(U) = 2 Pr(U = 1 mod 4) - 1 = {t:.6f}  (Pr(U = 1 mod 4) = {(1 + t) / 2:.6f})")
    # finite: empirical pair moment E chi4(U(n)) chi4(U(n+1)) vs formula
    emp1 = sum(chi4_odd(odd_part(TAU[n])) for n in range(1, X + 1)) / X
    emp2 = sum(chi4_odd(odd_part(TAU[n])) * chi4_odd(odd_part(TAU[n + 1])) for n in range(1, X + 1)) / X
    cnt, bad = law2[2]
    m2_11 = sum(k[0] * k[1] * v for k, v in cnt.items()) / (MOD - bad)
    pred2 = m2_11 * math.prod(1 - 4 * q for q in qs)
    print(f"[finite] n <= 2^20: mean chi_4(U(n)) = {emp1:.5f} (limit {t:.5f}); "
          f"mean chi_4(U(n))chi_4(U(n+1)) = {emp2:.5f} (limit {pred2:.5f}, i.i.d. model {t * t:.5f})")
    check(abs(emp1 - t) < 0.01 and abs(emp2 - pred2) < 0.01, "finite mark moments near limits")


# =============================================================== L
def section_L():
    head("L. ln 2: numerator laws, Weyl-sum form of D^+ < 1, transitions")
    # exact s_N = sum_{k<=N} 2^(N-k)/k via s_{N+1} = 2 s_N + 1/(N+1)
    NM = 3000
    s = Fr(0)
    A, Q = [0], [1]
    for N in range(1, NM + 1):
        s = 2 * s + Fr(1, N)
        A.append(s.numerator)
        Q.append(s.denominator)
    check(Fr(A[10], Q[10]) == sum(Fr(2 ** (10 - k), k) for k in range(1, 11)), "s_10")
    # (i') band law for all primes p with p^2 > N: m = floor(N/p) < p,
    #      v_p(Q_N) = 1 - [p | A_m] and p s_N = 2^(N-m) s_m (mod p)
    nb = 0
    dropped = []
    small_ok = 0
    for N in range(2, NM + 1):
        QN, AN = Q[N], A[N]
        big = 1                                   # product of the surviving primes p in P_N
        for p in PRIMES:
            if p > N:
                break
            if p * p <= N or p == 2:
                continue
            m = N // p
            qr = QN % (p * p)
            vq = 1 if qr % p == 0 else 0
            check(qr != 0, "v_p(Q_N) <= 1 for p^2 > N")
            survive = A[m] % p != 0
            check(vq == (1 if survive else 0), "band law: v_p(Q_N) = 1 - [p | A_m]")
            if survive:
                r = AN % p * pow(qr // p, -1, p) % p          # (Q_N / p) mod p = (Q_N mod p^2) / p
                check(r == pow(2, N - m, p) * A[m] * pow(Q[m] % p, -1, p) % p, "band residue")
                big *= p
            else:
                dropped.append((N, p, m))
            nb += 1
        # Section 5.3 decomposition: Q_N = (prod of p in P_N) * (a number supported on 2 and on
        # primes q with q^2 <= N), so x_N = R_N + sum_{p in P_N} (p-component) with no prime
        # counted twice (the boundary band m = floor(sqrt N) contributes only primes p > sqrt N).
        check(QN % big == 0, "P_N divides Q_N")
        rest = QN // big
        for q in PRIMES:
            if q * q > N and q > 2:
                break
            while rest % q == 0:
                rest //= q
        check(rest == 1, "R_N supported on 2 and primes q <= sqrt N")
        small_ok += 1
    print(f"[exact] band law for every odd p with p^2 > N (N <= {NM}, {nb} pairs): m = floor(N/p),"
          f" v_p(Q_N) = 1 - [p | A_m], and p x_N = 2^(N-m) A_m / Q_m (mod p)")
    print("        (m = 1, the top band (N/2, N]: A_1 = 1, so v_p(Q_N) = 1 and p x_N = 2^(N-1) = 2^(N-p) mod p)")
    print(f"[exact] for all {small_ok} N in [2, {NM}]: Q_N = prod(P_N) * (2- and sqrt(N)-smooth part), where P_N ="
          " {odd p : sqrt N < p <= N, p not | A_floor(N/p)}")
    first_A = ", ".join(f"A_{m}={A[m]}" for m in range(1, 7))
    dset = sorted({(p, m) for (_, p, m) in dropped})
    print(f"[exact] A_1..A_6: {first_A}; dropped (p, m) pairs with N <= {NM}: {dset[:12]}"
          f"{' ...' if len(dset) > 12 else ''} ({len(dset)} pairs, {len(dropped)} (N,p) events)")
    for N in (1000, 2000, 3000):
        lq = math.log(Q[N])
        lbig = sum(math.log(p) for p in PRIMES if p * p > N and 2 < p <= N)
        ldrop = sum(math.log(p) for (n_, p, m) in dropped if n_ == N)
        print(f"[finite] N = {N}: log Q_N / N = {lq / N:.4f}; large primes (p^2 > N): sum log p / N = "
              f"{lbig / N:.4f}, dropped share = {ldrop / lbig:.5f}")
    # single-prime behaviour along a band window [mp, (m+1)p), m = 1, 2: the p-component of x_N is
    # c 2^(N - mp) mod p with c != 0, so it runs through the coset c<2> of size t = ord_p(2), each
    # element (p-1)/t times plus one extra visit to c (the window has p = (p-1) + 1 terms)
    npair = nprim = 0
    nonprim_ex = []
    worst_prim = 0.0
    avg_ex = {}
    for p in PRIMES:
        if p < 3:
            continue
        if 3 * p > NM:
            break
        t = next(i for i in range(1, p) if pow(2, i, p) == 1)
        k_idx = (p - 1) // t
        for m in (1, 2):
            if A[m] % p == 0:
                continue
            seq = [A[N] % p * pow((Q[N] // p) % p, -1, p) % p for N in range(m * p, (m + 1) * p)]
            c = seq[0]
            coset = {c * pow(2, i, p) % p for i in range(t)}
            mult = {}
            for u in seq:
                mult[u] = mult.get(u, 0) + 1
            check(set(mult) == coset, "band window runs through the coset c<2>")
            check(all(mult[u] == k_idx + (1 if u == c else 0) for u in coset),
                  "band-window multiplicities (p-1)/t, plus one at the start")
            avg = abs(sum(complex(math.cos(2 * math.pi * u / p), math.sin(2 * math.pi * u / p))
                          for u in seq)) / p
            per = abs(sum(complex(math.cos(2 * math.pi * u / p), math.sin(2 * math.pi * u / p))
                          for u in coset))
            check(per <= ((k_idx - 1) * math.sqrt(p) + 1) / k_idx + 1e-9, "Gauss-period bound")
            npair += 1
            if t == p - 1:
                nprim += 1
                worst_prim = max(worst_prim, avg * p)
                check(avg <= 2 / p + 1e-12, "primitive root: window average <= 2/p")
            else:
                if len(nonprim_ex) < 4 and t <= 11 and (p, t) not in nonprim_ex:
                    nonprim_ex.append((p, t))
            if p in (7, 31) and m == 1:
                avg_ex[p] = (t, avg)
    print(f"[exact] band windows [mp, (m+1)p), m = 1, 2, odd p <= {NM // 3} with p not | A_m ({npair} pairs):"
          " the p-component of x_N runs")
    print("        through a coset c<2> mod p of size t = ord_p(2), each element (p-1)/t times plus one extra"
          " visit to c;")
    print(f"        {nprim} pairs have 2 a primitive root (t = p-1: every nonzero residue), {npair - nprim} have"
          f" t < p-1, e.g. (p, t) = {nonprim_ex}")
    print(f"[float] window phase average |(1/p) sum_N e(component_N)|: <= 2/p at every primitive-root pair"
          f" (max p*avg = {worst_prim:.4f}); "
          + ", ".join(f"p = {p_} (t = {t_}, m = 1): {a_:.4f}" for p_, (t_, a_) in sorted(avg_ex.items())))
    print("        and |sum_(u in c<2>) e(u/p)| <= ((k-1) sqrt p + 1)/k, k = (p-1)/t, at every pair (Gauss periods)")
    hits = {j: [] for j in range(6)}
    for p in PRIMES:
        if p < 11:
            continue
        if p > NM:
            break
        q = (pow(2, p - 1, p * p) - 1) // p % p
        for j in range(6):
            N = p - 1 - j
            Hj = sum(pow(2, i - 1, p) * pow(i, -1, p) for i in range(1, j + 1)) % p
            sN = A[N] % p * pow(Q[N] % p, -1, p) % p
            check(sN == pow(2, N, p) * (q + Hj) % p, "s_{p-1-j} = 2^N (q_p(2) + H_j) mod p")
            check((A[N] % p == 0) == ((q + Hj) % p == 0), "numerator survival law")
            if A[N] % p == 0:
                hits[j].append(p)
    wief = [p for p in PRIMES if p < 100000 and pow(2, p - 1, p * p) == 1]
    check(wief == [1093, 3511], "Wieferich primes below 10^5")
    print("[exact] s_(p-1-j) = 2^(p-1-j) (q_p(2) + sum_(i<=j) 2^(i-1)/i) mod p for 11 <= p <= 3000, j <= 5")
    print("[exact] primes p <= 3000 dividing the numerator of s_(p-1-j): "
          + "; ".join(f"j={j}: {hits[j]}" for j in range(6)))
    print(f"[exact] Wieferich primes below 10^5: {wief}  (p | num s_(p-1) iff p Wieferich)")

    # (iii) Weyl-sum threshold for D^+ <= 0.9999
    eps = Fr(1, 10 ** 4)
    pi_hi = Fr(22, 7)
    thr = (1 - eps) * (1 - (pi_hi * eps) ** 2 / 2) - eps
    check(thr > Fr(9997, 10000), "threshold > 0.9997")
    print(f"[exact] if |S_N(1)| < (1-e)(1-(22e/7)^2/2) - e = {float(thr):.10f} (e = 10^-4) then D_N < 0.9999;")
    print("        hence limsup |S_N(1)| <= 0.9997 implies D^+(ln 2; 2) <= 0.9999")
    # (iv) minorant identity 1/4 - c/2 + (2c^2-1)/4 = (c^2 - c)/2 in [0,1] on c<=0, <=0 on c>0
    for k in range(-100, 101):
        c = Fr(k, 100)
        m = Fr(1, 4) - c / 2 + (2 * c * c - 1) / 4
        check(m == (c * c - c) / 2, "minorant identity")
        check((m <= 1 and m >= 0) if c <= 0 else m <= 0, "minorant bounds")
    print("[exact] 1_[1/4,3/4](x) >= 1/4 - cos(2 pi x)/2 + cos(4 pi x)/4 = (c^2 - c)/2, c = cos 2 pi x")

    # (v) digits of ln 2: ln 2 = (2/3) sum 9^-k/(2k+1); floor(2^W ln 2) with error < 2^16
    ND = 1 << 16
    W = ND + 96
    t = (2 << W) // 3
    acc = 0
    k = 0
    while t:
        acc += t // (2 * k + 1)
        t //= 9
        k += 1
    F = acc % (1 << W)
    bits = bin(F)[2:].zfill(W)
    g = bits[ND:W - 18]
    check("0" in g and "1" in g, "ln 2 guard bits")
    check(bits[:20] == "10110001011100100001", "ln 2 = 0.10110001011100100001..._2")
    # BBP state agreement x_N + r_N = {2^N ln 2}: check top 30 bits for N <= 300
    for N in range(1, 301, 7):
        xN = Fr(A[N] % Q[N], Q[N])
        rN = sum(Fr(1, (N + j) * 2 ** j) for j in range(1, 80))
        val = (xN + rN) % 1
        check(abs(val - Fr(int(bits[N:N + 40], 2), 1 << 40)) < Fr(1, 1 << 38), "BBP state")
    print("[exact] {2^N ln 2} = x_N + r_N with x_N = A_N mod Q_N / Q_N (checked to 38 bits, N <= 300)")
    print("[finite] binary transitions of ln 2 (#{1 <= j < N : d_j != d_(j+1)}), |S_N(1)| (53-bit points), and the")
    print("         main term log N / log mu (mu = 3.5746) of the unconditional transition count:")
    trans = 0
    zre = zim = 0.0
    rows = []
    marks = {1 << e for e in range(10, 17)}
    for n in range(ND):
        if n >= 1 and bits[n - 1] != bits[n]:
            trans += 1
        x = int(bits[n:n + 53], 2) / 2.0 ** 53
        zre += math.cos(2 * math.pi * x)
        zim += math.sin(2 * math.pi * x)
        if n + 1 in marks:
            rows.append((n + 1, trans, math.hypot(zre, zim) / (n + 1)))
    mu = 3.5746
    for (N, tr, S1) in rows:
        print(f"         N = 2^{N.bit_length() - 1:<3d} transitions {tr:6d}  ({tr / N:.4f} N)   "
              f"|S_N(1)| = {S1:.4f}   log N/log mu = {math.log(N) / math.log(mu):.1f}")
    check(rows[-1][1] > 0.4 * ND, "finite transition density")


# =============================================================== B
CLUSTER_MAP = {
    "algebraic": ["BC-01", "BC-02", "BC-03", "BC-04", "BC-05", "BC-06", "BC-07"],
    "logarithmic_pi": ["BC-08", "BC-09", "BC-10", "BC-11", "BC-12", "BC-13", "BC-14", "BC-15"],
    "exponential_gamma_bessel": ["BC-16", "BC-17", "BC-18", "BC-19", "BC-20", "BC-21"],
    "zeta_L": ["BC-22", "BC-23", "BC-24", "BC-25", "BC-26"],
    "dense_modular_lambert": ["BC-31", "BC-32", "BC-35", "BC-36", "BC-38", "BC-39", "BC-42",
                              "BC-43", "BC-44"],
}


def section_B():
    head("B. Missing-estimate map vs the fixed 50-constant roster")
    try:
        import tomllib
    except ImportError:                      # pragma: no cover
        print("tomllib unavailable; skipped")
        return
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "docs", "benchmarks", "classical-constants.toml")
    with open(path, "rb") as fh:
        data = tomllib.load(fh)
    roster = {c["id"]: c for c in data["constant"]}
    check(len(roster) == 50, "roster size 50")
    mapped = [i for ids in CLUSTER_MAP.values() for i in ids]
    check(len(mapped) == 35 and len(set(mapped)) == 35, "35 mapped constants")
    for i in mapped:
        check(i in roster, f"{i} in roster")
    open_now = sorted(i for i, c in roster.items()
                      if c["full_normality"] == "open" and c["evidence"] == "open")
    check(set(open_now) <= set(mapped), "every currently open constant is mapped")
    print(f"[exact] 35 mapped IDs, all in the roster; currently open (full normality and evidence "
          f"'open'): {len(open_now)}; all of them mapped")
    for k, ids in CLUSTER_MAP.items():
        print(f"         {k:26s} {', '.join(ids)}")


def main():
    for f in (section_P, section_C, section_T, section_M, section_L, section_B):
        t = time.time()
        f()
        print(f"  ({f.__name__}: {time.time() - t:.1f} s)")
    print(f"\nALL CHECKS PASSED ({CHECKS[0]} checks) in {time.time() - T0:.1f} s")


if __name__ == "__main__":
    main()
