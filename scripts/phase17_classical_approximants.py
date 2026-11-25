"""Phase 17, Track E: classical constants and usable rational approximants.

Standard library only (plus the sibling Phase 16 script `phase16_adaptive_log.py`, imported
read-only for its exact cell rows, LLL and congruence helpers in section E3).
Every certificate in E1/E2 uses exact integer or Fraction arithmetic; the only floating
values are printed summaries (base-2 logarithms of exact integers/fractions).

    python -B scripts/phase17_classical_approximants.py          (about 3 seconds)

E1/E2  Correlated (Bezout) rounding of rounded pole-integral approximants to ln 2.
       Kernels: the Phase 16 Chebyshev kernel T_D(2x-1) and the Legendre kernel P_D(2x-1).
       Methods: independent rounding with the Phase 16 shift w (reference), correlated
       Bezout rounding with w = 0, and the ln 2-aware nearest grid on (1/L_D) Z.
E3     Dimension k = 1..4 lattice experiments on the Phase 16 adaptive-logarithm families:
       feasibility / height / error / window, and the Minkowski trade-off law
       (k-1) log H = log M + T log 2 + O(1).
E4     Exact finite comparisons for ln 2, pi, e, sqrt(2), phi: binary statistics,
       continued fractions, Zeckendorf indices of 2^n, factorial/BBP denominators.
"""

import importlib
import math
import os
import random
import sys
import time
from fractions import Fraction as Q
from math import comb, gcd, isqrt, lcm, log, log2

T_START = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
MU_LN2 = 3.57455391      # Marcovecchio (2009), Acta Arith. 139, Thm 1.1
MU_LN2_CONFIRMED = 3.89139977   # Rukhadze (1987)
LN2 = math.log(2)


def banner(text):
    print("\n== " + text)


def v2(n):
    n = abs(n)
    return (n & -n).bit_length() - 1 if n else 10 ** 9


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(sieve[p * p::p]))
    return [p for p in range(n + 1) if sieve[p]]


def lcm_range(D):
    L = 1
    for k in range(2, D + 1):
        L = lcm(L, k)
    return L


def log2q(x):
    """log2 of a positive Fraction or int (exact integers, float summary)."""
    x = Q(x)
    return math.log2(x.numerator) - math.log2(x.denominator)


def nearest(x):
    """Nearest integer of a Fraction (ties upward)."""
    return (2 * x.numerator + x.denominator) // (2 * x.denominator)


# ---------------------------------------------------------------------------
# certified enclosure of ln 2
# ---------------------------------------------------------------------------
LN2_BITS = 4400
LN2_S = sum((1 << (LN2_BITS - k)) // k for k in range(1, LN2_BITS + 1))
# 2^B ln 2 lies in [LN2_S, LN2_S + B + 1): each floor loses < 1 unit and the tail is < 1.
LN2_LO = Q(LN2_S, 1 << LN2_BITS)
LN2_HI = Q(LN2_S + LN2_BITS + 1, 1 << LN2_BITS)


def dist_to_int(c, N):
    """Bounds (lo, hi) for ||c 2^N ln 2||, c a positive integer, and the nearest integer."""
    x_lo, x_hi = c * (1 << N) * LN2_LO, c * (1 << N) * LN2_HI
    r = nearest(x_lo)
    assert r == nearest(x_hi), "enclosure straddles a half-integer: raise LN2_BITS"
    a, b = abs(x_lo - r), abs(x_hi - r)
    assert (x_lo - r) * (x_hi - r) > 0, "enclosure straddles an integer: raise LN2_BITS"
    return min(a, b), max(a, b), r


def err_bounds(Y, N):
    """Certified bounds for |2^N ln 2 - Y|."""
    d1, d2 = (1 << N) * LN2_LO - Y, (1 << N) * LN2_HI - Y
    assert d1 * d2 > 0, "enclosure straddles Y: raise LN2_BITS"
    return min(abs(d1), abs(d2)), max(abs(d1), abs(d2))


# ---------------------------------------------------------------------------
# kernels and pole data
# ---------------------------------------------------------------------------
def cheb_shifted(D, fact):
    """Integer coefficients (low to high) of T_D(2x-1)."""
    c = [0] * (D + 1)
    c[0] = (-1) ** D
    for k in range(1, D + 1):
        num = D * fact[D + k - 1] * 4 ** k
        den = fact[D - k] * fact[2 * k]
        assert num % den == 0
        c[k] = (-1) ** (D - k) * (num // den)
    return c


def legendre_shifted(n):
    """Integer coefficients of P_n(2x-1) = sum (-1)^(n+k) C(n,k) C(n+k,k) x^k."""
    return [(-1) ** (n + k) * comb(n, k) * comb(n + k, k) for k in range(n + 1)]


def poly_eval(p, x):
    r = 0
    for c in reversed(p):
        r = r * x + c
    return r


def pole_quotient(K, a, sigma):
    """P with K(x) - K(x_i) = (a - sigma x) P(x), x_i = sigma a, as integer coefficients."""
    xi = sigma * a
    d = len(K) - 1
    q = [0] * d
    carry = 0
    for i in range(d, 0, -1):
        carry = K[i] + carry * xi
        q[i - 1] = carry
    return [-sigma * c for c in q]


FAMILIES = [
    ("single 1/(1+x)", [(1, 1, -1)]),
    ("two-stride", [(2, 4, 1), (1, 8, -1)]),
    ("telescoping M=8", [(1, a, 1) for a in range(9, 17)]),
]


def check_pole_identity(poles):
    """sum c_i int_0^1 dx/(a_i - sigma_i x) = ln 2, checked exactly as a product identity."""
    prod = Q(1)
    for c, a, s in poles:
        prod *= (Q(a, a - 1) if s == 1 else Q(a + 1, a)) ** c
    assert prod == 2


def build_r(K, poles):
    """e and r_k = 2^e R_tot,k (Fractions), with exact S = sum r_k/(k+1)."""
    D = len(K) - 1
    tv = [poly_eval(K, a * s) for _, a, s in poles]
    e = min(abs(t) for t in tv).bit_length() - 1
    den = 1
    for t in tv:
        den = lcm(den, abs(t))
    num = [0] * D
    for (c, a, s), t in zip(poles, tv):
        P = pole_quotient(K, a, s)
        mult = c * (den // t)          # exact: t divides den, sign carried by t
        for k in range(D):
            num[k] += mult * P[k]
    r = [Q(n << e, den) for n in num]
    return e, r, tv


def bezout_delta(D, L, Delta, primes):
    """Integers delta_k with sum delta_k L/(k+1) = Delta (partial fractions / CRT).

    For each prime p <= D put P = p^a, the largest prime power <= D, use the index k = P-1
    with weight L/P (a unit mod p), and a centred residue s_p; the remainder is a multiple
    of L and goes into k = 0.  |delta_k| <= P/2 at k = P-1.
    """
    delta = [0] * D
    used = 0
    for p in primes:
        if p > D:
            break
        P = p
        while P * p <= D:
            P *= p
        wgt = L // P
        s = (Delta * pow(wgt, -1, P)) % P
        if s > P // 2:
            s -= P
        delta[P - 1] += s
        used += s * wgt
    rest = Delta - used
    assert rest % L == 0
    delta[0] += rest // L
    assert sum(delta[k] * (L // (k + 1)) for k in range(D)) == Delta
    return delta


class Ctx:
    def __init__(self, Dmax):
        self.Dmax = Dmax
        self.fact = [1]
        for i in range(1, 2 * Dmax + 2):
            self.fact.append(self.fact[-1] * i)
        self.primes = primes_upto(Dmax)
        self.L = {}

    def Lcm(self, D):
        if D not in self.L:
            self.L[D] = lcm_range(D)
        return self.L[D]


def analyze(ctx, fam, poles, D, kern, meth):
    """One certified row: build the approximant, measure every metric exactly."""
    K = cheb_shifted(D, ctx.fact) if kern == "cheb" else legendre_shifted(D)
    e, r, tv = build_r(K, poles)
    L = ctx.Lcm(D)
    S = sum((r[k] / (k + 1) for k in range(D)), Q(0))
    Q0 = [nearest(x) for x in r]
    if meth == "indep":
        w = int(math.ceil(math.log2(max(8.0, D * (math.log(D) + 1.0))))) + 2
        Qk = Q0
        dmax = 0
    else:
        w = 0
        n_star = nearest(L * S)
        n0 = sum(Q0[k] * (L // (k + 1)) for k in range(D))
        delta = bezout_delta(D, L, n_star - n0, ctx.primes)
        Qk = [a + b for a, b in zip(Q0, delta)]
        dmax = max(abs(x) for x in delta)
        # the exact grid property: integral of Q is the nearest point of (1/L)Z to S
        assert abs(Q(sum(Qk[k] * (L // (k + 1)) for k in range(D)), L) - S) <= Q(1, 2 * L)
    nnum = sum(Qk[k] * (L // (k + 1)) for k in range(D))
    N = e - w
    Y = -Q(nnum, L << w)
    q = Y.denominator
    assert (L << w) % q == 0                          # q_N divides 2^w L_D
    sup = [p for p in ctx.primes if q % p == 0]
    rem = q
    for p in sup:
        while rem % p == 0:
            rem //= p
    assert rem == 1                                   # support inside primes <= D
    elo, ehi = err_bounds(Y, N)
    eta_q_lo, _, _ = dist_to_int(q, N)
    assert elo >= eta_q_lo / q                        # grid ceiling, exact
    Lg = L << w
    eta_lo, eta_hi, rbench = dist_to_int(Lg, N)
    Traw = int(math.floor(-log2q(ehi)))
    row = dict(fam=fam, kern=kern, meth=meth, D=D, N=N, w=w, e=e, q=q,
               logq=math.log(q) / N, logodd=math.log(q >> v2(q)) / N, v2=v2(q),
               nsup=len(sup), npi=len([p for p in ctx.primes if p <= D]),
               hq=max(abs(x) for x in Qk).bit_length(), dmax=dmax,
               err=log2q(ehi), Traw=Traw, T=max(0, Traw - 8),
               log2q_=log2q(q), log2L=log2q(Lg), eta=log2q(eta_hi),
               Tgrid=max(0, int(math.floor(-log2q(eta_hi / Lg))) - 8), qodd=q >> v2(q),
               tv=tv, S=S, r=r, L=L, same=(rbench == -nnum))
    return row


def print_rows(rows):
    print("   fam  kern meth   D     N  w  logq/N odd/N v2 supp/piD  Q-bits dmax"
          "  log2err   T  Tgrid  log2q  log2L   log2eta  T-log2q =grid")
    for x in rows:
        print("   %-4s %-4s %-5s %3d %5d %2d  %.4f %.4f %2d %3d/%-3d %6d %4d %8.2f %4d %5d %7.1f %7.1f %9.1f %8.1f  %s" % (
            x["fam"][:4], x["kern"], x["meth"], x["D"], x["N"], x["w"], x["logq"], x["logodd"],
            x["v2"], x["nsup"], x["npi"], x["hq"], x["dmax"], x["err"], x["T"], x["Tgrid"],
            x["log2q_"], x["log2L"], x["eta"], x["Traw"] - x["log2q_"], "yes" if x["same"] else "no"))


def selftests(ctx):
    banner("0. Self-tests of the exact machinery")
    # Chebyshev / Legendre coefficients against their recurrences
    def cheb_rec(D):
        a, b = [1], [0, 1]
        if D == 0:
            return a
        for _ in range(2, D + 1):
            c = [0] * (len(b) + 1)
            for i, v in enumerate(b):
                c[i + 1] += 2 * v
            for i, v in enumerate(a):
                c[i] -= v
            a, b = b, c
        sq = [0] * (len(b))
        # compose with 2x-1
        res = [0] * len(b)
        pw = [1]
        for coef in b:
            for i, v in enumerate(pw):
                res[i] += coef * v
            npw = [0] * (len(pw) + 1)
            for i, v in enumerate(pw):
                npw[i] -= v
                npw[i + 1] += 2 * v
            pw = npw
        return res

    for D in range(1, 11):
        assert cheb_shifted(D, ctx.fact) == cheb_rec(D)[:D + 1], D
    for n in range(1, 9):
        p = legendre_shifted(n)
        # Legendre: (n+1) P_{n+1} = (2n+1) u P_n - n P_{n-1}, u = 2x-1, checked at points
        for xv in (Q(1, 3), Q(2), Q(-3, 2)):
            u = 2 * xv - 1
            pm, pc = Q(1), u
            for m in range(1, n):
                pm, pc = pc, ((2 * m + 1) * u * pc - m * pm) / (m + 1)
            assert poly_eval(p, xv) == (pc if n >= 1 else Q(1))
    for _, poles in FAMILIES:
        check_pole_identity(poles)
    # numeric check of  ln 2 + int R = int K/(K(x_1)(a-sigma x))  for single pole, D = 14
    for kern in ("cheb", "leg"):
        D = 14
        K = cheb_shifted(D, ctx.fact) if kern == "cheb" else legendre_shifted(D)
        e, r, tv = build_r(K, FAMILIES[0][1])
        intR = float(sum((r[k] / (k + 1) for k in range(D)), Q(0)) / (1 << e))
        n = 4000
        h = 1.0 / n
        quad = sum((poly_eval(K, (i + 0.5) * h) / (1 + (i + 0.5) * h)) for i in range(n)) * h / tv[0]
        assert abs(LN2 + intR - quad) < 1e-9, (kern, LN2 + intR, quad)
    print("   Chebyshev/Legendre coefficients, pole identities (exact) and the remainder identity ok")


def analytic_remainder(ctx):
    banner("1a. The analytic remainder: Chebyshev kernel ~ D^-2, Legendre kernel ~ rho^-D")
    print("   E_D = |2^e ln 2 + int 2^e R| (single pole 1/(1+x)); predicted Chebyshev value")
    print("   2^e/|T_D(3)| * (1/4 + (-1)^D/2)/D^2 from two integrations by parts")
    for D in (40, 41, 80, 81, 160, 161, 320):
        K = cheb_shifted(D, ctx.fact)
        e, r, tv = build_r(K, FAMILIES[0][1])
        S = sum((r[k] / (k + 1) for k in range(D)), Q(0))
        lo = (1 << e) * LN2_LO + S
        hi = (1 << e) * LN2_HI + S
        assert lo * hi > 0
        E = min(abs(lo), abs(hi))
        pred = Q(1 << e, abs(tv[0])) * abs(Q(1, 4) + Q((-1) ** D, 2)) / D ** 2
        ratio = float(E / pred)
        print("   D=%3d (%s)  log2 E = %7.2f   D^2 E = %.4f   E/pred = %.4f" % (
            D, "even" if D % 2 == 0 else "odd ", log2q(E), float(E * D * D), ratio))
        assert abs(ratio - 1) < 0.02, ratio
    print("   other families (Chebyshev kernel): E_D D^2 / (2^e |c/T(x*)| |g(1) + (-1)^D g(-1)|) for the dominant pole x*")
    for fam, poles in FAMILIES[1:]:
        for D in (160, 161):
            K = cheb_shifted(D, ctx.fact)
            e, r, tv = build_r(K, poles)
            S = sum((r[k] / (k + 1) for k in range(D)), Q(0))
            lo, hi = (1 << e) * LN2_LO + S, (1 << e) * LN2_HI + S
            assert lo * hi > 0
            E = min(abs(lo), abs(hi))
            i = min(range(len(poles)), key=lambda t: abs(tv[t]))
            c, a, sg = poles[i]
            z = 2 * a - sg
            pred = Q(abs(c) * (1 << e), abs(tv[i])) * abs(Q(1, z - sg) + (-1) ** D * Q(1, z + sg)) / D ** 2
            print("   %-16s D=%d: log2 E = %7.2f, E/pred = %.5f" % (fam, D, log2q(E), float(E / pred)))
            assert abs(float(E / pred) - 1) < 0.01
    print("   Legendre kernel (same pole): log2 E_D against -D log2(rho), rho = 3 + 2 sqrt 2")
    for D in (40, 80, 160, 320):
        K = legendre_shifted(D)
        e, r, tv = build_r(K, FAMILIES[0][1])
        S = sum((r[k] / (k + 1) for k in range(D)), Q(0))
        lo = (1 << e) * LN2_LO + S
        hi = (1 << e) * LN2_HI + S
        assert lo * hi > 0
        E = min(abs(lo), abs(hi))
        print("   D=%3d  log2 E = %8.2f   -D log2 rho = %8.2f   log2 L_D = %7.2f" % (
            D, log2q(E), -D * math.log2(3 + 2 * math.sqrt(2)), log2q(ctx.Lcm(D))))
        assert log2q(E) < -0.9 * D * math.log2(3 + 2 * math.sqrt(2))
        assert E < Q(1, 2 * ctx.Lcm(D))      # below the grid spacing: the grid dominates


def run_e12():
    ctx = Ctx(330)
    selftests(ctx)
    analytic_remainder(ctx)
    banner("1b. Certified table: independent (Phase 16) vs correlated (Bezout, w=0) rounding")
    print("   meth: indep = round each coefficient, shift w (Phase 16); corr = Bezout, w = 0, q | L_D.")
    print("   T = floor(-log2 err) - 8 (consecutive shifts kept within 2^-8); Tgrid = same for the")
    print("   ln2-aware nearest point of (1/(2^w L_D))Z at the same N; log2eta = log2||2^w L_D 2^N ln2||.")
    plan = [(FAMILIES[0], (24, 60, 120, 240)), (FAMILIES[1], (24, 60, 120)),
            (FAMILIES[2], (24, 60, 120))]
    rows = []
    for (fam, poles), Ds in plan:
        for D in Ds:
            for kern, meth in (("cheb", "indep"), ("cheb", "corr"), ("leg", "indep"), ("leg", "corr")):
                rows.append(analyze(ctx, fam, poles, D, kern, meth))
        print_rows(rows[-4 * len(Ds):])
        print()
    # ---- assertions: the theorems of the note, checked on every row -----------------------
    for x in rows:
        D = x["D"]
        if x["meth"] == "corr":
            assert x["w"] == 0 and x["q"] <= x["L"]
            assert x["dmax"] <= D // 2 + 1 + int(math.log(D)) + 1       # Bezout height
            if x["kern"] == "leg":
                # identification: the ln2-free numerator IS the ln2-aware nearest-grid numerator
                assert x["same"], x
                # window = log2 L_D up to the lucky bits log2(1/eta) + O(1)
                assert x["Traw"] >= x["log2L"] - 2, x
                assert x["Traw"] <= x["log2L"] + 2 + max(0.0, -x["eta"]) , x
            else:
                # Chebyshev kernel: window only ~ 2 log2 D (analytic floor)
                assert x["Traw"] <= 2 * math.log2(D) + 9, x
                assert x["Traw"] >= 2 * math.log2(D) - 9, x
        # grid ceiling: window never exceeds log2 q + log2(1/eta_q) (asserted exactly inside)
        # irrationality-measure confinement  T <= (mu-1) N + mu log2 q + O(1)
        assert x["Traw"] <= (MU_LN2 - 1) * x["N"] + MU_LN2 * x["log2q_"] + 2
    # headline comparisons (single pole, D = 240)
    pick = {(x["kern"], x["meth"]): x for x in rows if x["fam"].startswith("single") and x["D"] == 240}
    a, b, c = pick[("cheb", "indep")], pick[("cheb", "corr")], pick[("leg", "corr")]
    print("   single pole D=240:  Phase 16: N=%d, v2=%d, log q/N=%.4f, T=%d | Cheb+Bezout: N=%d,"
          " v2=%d, log q/N=%.4f, T=%d | Legendre+Bezout: N=%d, v2=%d, log q/N=%.4f, T=%d (log2 L=%.0f)"
          % (a["N"], a["v2"], a["logq"], a["T"], b["N"], b["v2"], b["logq"], b["T"],
             c["N"], c["v2"], c["logq"], c["T"], c["log2L"]))
    assert c["T"] > 20 * a["T"] and b["T"] < a["T"] + 8
    assert c["logq"] < 5 / 12 and b["logq"] < 5 / 12

    banner("1c. Support and prime survival in the correlated rows")
    for x in rows:
        if x["meth"] == "corr" and x["kern"] == "leg" and x["D"] in (60, 120, 240):
            ctxp = [p for p in ctx.primes if p <= x["D"]]
            sup = [p for p in ctxp if x["q"] % p == 0]
            big = [p for p in ctxp if p > x["D"] // 2]
            kept_big = len([p for p in sup if p > x["D"] // 2])
            print("   %-16s D=%3d: prime support %d of %d primes <= D; of the %d primes in (D/2, D] %d divide q_N;"
                  " v2(q_N)=%d (v2(L_D)=%d); odd part %.0f bits" % (
                      x["fam"], x["D"], len(sup), len(ctxp), len(big), kept_big, x["v2"],
                      v2(ctx.Lcm(x["D"])), math.log2(x["qodd"])))

    banner("1d. Why (1+c) log2 L_D needs luck: eta_{N,L} for N in a window of 3000 shifts, L = L_240")
    L = ctx.Lcm(240)
    M = L * LN2_S
    B = LN2_BITS
    base = 600
    # exact (float of a scaled integer, 2^-53 relative accuracy is enough here)
    etas = []
    for N in range(base, base + 3000):
        r_ = (M << N) & ((1 << B) - 1)
        m_ = min(r_, (1 << B) - r_)
        etas.append(math.ldexp(m_ >> (B - 60), -60))
    etas.sort()
    print("   log2 L_240 = %.1f; over 3000 consecutive N the smallest eta values are 2^%.1f, 2^%.1f, 2^%.1f"
          % (log2q(L), math.log2(etas[0]), math.log2(etas[1]), math.log2(etas[2])))
    for j in (1, 3, 5, 8, 10):
        frac = sum(1 for t in etas if t <= 2.0 ** (-j)) / len(etas)
        print("   fraction of N with eta <= 2^-%-2d : %.4f   (uniform model 2^(1-j) = %.4f)" % (j, frac, 2.0 ** (1 - j)))
    gain = -math.log2(etas[0])
    print("   best gain over the grid: %.1f bits from 3000 trials (log2 3000 = %.1f); a gain of c*log2 L_D = %.0f bits"
          " (c = 1/10) would need about 2^%.0f trials" % (gain, math.log2(3000), 0.1 * log2q(L), 0.1 * log2q(L)))
    assert gain < math.log2(3000) + 8

    banner("1e. Window-denominator confinement (Theorem 6): T <= (mu-1) N + mu log2 q + O(1)")
    print("   For each correlated Legendre row: allowed ceiling vs actual T, and delta_N = ln T / ln q")
    print("   (Vandehey-type hypothesis T >= q^delta requires delta > 1/(k+2): 1/3 for square, 1/4 for cube).")
    for x in rows:
        if x["meth"] == "corr" and x["kern"] == "leg":
            ceil_ = (MU_LN2 - 1) * x["N"] + MU_LN2 * x["log2q_"]
            dN = math.log(max(x["Traw"], 2)) / math.log(x["q"])
            print("   %-16s D=%3d N=%4d: T=%4d, ceiling %.0f (mu=%.3f), T/log2 q = %.3f, delta_N = %.4f %s" % (
                x["fam"], x["D"], x["N"], x["Traw"], ceil_, MU_LN2, x["Traw"] / x["log2q_"], dN,
                "(< 1/4)" if dN < 1 / 4 else ("(< 1/3)" if dN < 1 / 3 else "")))
    # constants of Theorem C for the three Phase-16 limits  rho_lim = ln 2 / ln(rho_min)
    for fam, limit in (("single", 0.393220), ("two-stride", 0.263162), ("M=8", 0.19661)):
        N_over_log2q = LN2 / limit            # N / log2 q  = ln2 / rate
        cst = (MU_LN2 - 1) * N_over_log2q + MU_LN2
        print("   %-10s rate %.5f: any approximant with this rate has T <= %.2f log2 q_N + O(1)" % (fam, limit, cst))
    return rows, ctx


# ---------------------------------------------------------------------------
# E3: lattices in dimension k
# ---------------------------------------------------------------------------
def solve_k(P16, sh, theta0, dirs, cancel, Wbits):
    """Cancel the bands in `cancel` by CRT congruences on theta = theta0 + sum z_j dirs[j],
    and (Wbits is not None) weight the shifted error by W = 2^Wbits in a Kannan embedding."""
    k = len(dirs)
    cons = P16.congruences(sh, theta0, dirs, cancel)
    j = max(range(k), key=lambda t: sum(log(p) for p, _, bp in cons if bp[t]))
    cons = [c for c in cons if c[2][j]]
    Qmod = 1
    for p, _, _ in cons:
        Qmod *= p
    zstar_j, _ = P16.crt([(-a * pow(bp[j], -1, p) % p, p) for p, a, bp in cons])
    others = [P16.crt([(bp[i] * pow(bp[j], -1, p) % p, p) for p, a, bp in cons])[0] if i != j else None
              for i in range(k)]

    def theta_of(z):
        return tuple(t + sum(zi * d[c] for zi, d in zip(z, dirs)) for c, t in enumerate(theta0))

    if k == 1:
        z = zstar_j % Qmod
        if z > Qmod // 2:
            z -= Qmod
        return theta_of([z]), Qmod, cons
    basis = []
    for i in range(k):
        if i == j:
            continue
        vec = [0] * k
        vec[i], vec[j] = 1, -others[i] % Qmod
        basis.append(vec)
    vec = [0] * k
    vec[j] = Qmod
    basis.append(vec)
    target = [0] * k
    target[j] = zstar_j
    if Wbits is not None:
        W = 1 << Wbits

        def err_lin(z):
            return -sum(zi * sum(d[c] * sh.Y[c + 1] for c in range(4)) for zi, d in zip(z, dirs))
        e0 = sh.ln2N - sh.prefix(theta0)
        rows = [vec_ + [round(W * err_lin(vec_))] for vec_ in basis]
        target = target + [round(W * (e0 + err_lin(target)))]
    else:
        rows = basis
    red = P16.lll(rows)
    n = len(red)
    bs, bb = [], []
    for i in range(n):
        w_ = [Q(x) for x in red[i]]
        for j2 in range(i):
            if bb[j2]:
                mu = sum(x * y for x, y in zip(red[i], bs[j2])) / bb[j2]
                w_ = [x - mu * y for x, y in zip(w_, bs[j2])]
        bs.append(w_)
        bb.append(sum(x * x for x in w_))
    t = list(target)
    for i in range(n - 1, -1, -1):
        c = round(sum(x * y for x, y in zip(t, bs[i])) / bb[i])
        if c:
            t = [x - c * y for x, y in zip(t, red[i])]
    return theta_of(t[:k]), Qmod, cons


def run_e3():
    banner("3. E3: feasibility / height / error / window in dimension k (exact, N = 120)")
    sys.path.insert(0, HERE)
    P16 = importlib.import_module("phase16_adaptive_log")
    N = 120
    t0 = time.time()
    sh = P16.Shift(N)
    print("   exact shifted data at N=%d built in %.1fs; y_i = Y_i(N): N*Y(N) = (%s)" % (
        N, time.time() - t0, ", ".join("%.4f" % float(N * y) for y in sh.Y[1:])))
    cancel = {3, 5, 6, 7}
    theta0 = (0, 0, 0, -5)
    cancel_k = {5, 6, 7, 2, 3}                     # five nonconstant bands for k = 3, 4 (band 2 is zero on the plane)
    fams = {
        1: ([(0, 0, 0, 1)], {5, 6, 7}),
        2: ([(0, 0, 1, 0), (0, 0, 0, 1)], cancel),
        3: ([(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)], cancel_k),
        4: ([(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)], cancel_k),
    }

    def measure(k, theta, Qmod, cons, cset):
        H = P16.height(theta)
        e = sh.error(theta)
        ev = P16.evaluate(sh, theta)
        assert ev["mism"] == 0
        # grid ceiling for the adaptive formula: Y = a/q  =>  |2^N ln 2 - Y| >= ||q 2^N ln 2|| / q  (exact)
        Yq = sh.prefix(theta)
        qd = Yq.denominator
        xq = qd * sh.ln2N
        assert abs(sh.ln2N - Yq) >= abs(xq - round(xq)) / qd
        for p, _, _ in cons:                      # every imposed congruence really holds
            v = sh.band(p)
            assert P16.modp(P16.value(sh.rows[v], theta), p) == 0
        # bands cancelled *exactly* (cell value 0) cost no height but use up one dimension each
        zero = sorted(v for v in cset if P16.value(sh.rows[v], theta) == 0)
        Meff = 1
        for p, _, _ in cons:
            if sh.band(p) not in zero:
                Meff *= p
        return dict(k=k, H=H, M=Qmod, lnH=math.log(H), lnM=math.log(Qmod), err=e, zero=zero,
                    keff=max(1, k - len(zero)), lnMeff=math.log(Meff),
                    log2err=float(log2q(abs(e))), logq=ev["logq"], theta=theta)

    def coset_ceiling(dirs, cons):
        """Every theta in the coset has Y_N(theta) in (1/q*)Z, q* = common denominator with the cancelled
        primes removed (p^2 > 2N, so each occurs to the first power).  Hence for ALL such theta
        |2^N ln 2 - Y_N| >= ||q* 2^N ln 2|| / q*: a ceiling independent of the height."""
        ys = [sum(d[c] * sh.Y[c + 1] for c in range(4)) for d in dirs]
        Dy = 1
        for x in [sh.prefix(theta0)] + ys:
            Dy = lcm(Dy, Q(x).denominator)
        qs = Dy
        for p_, _, _ in cons:
            if qs % p_ == 0:
                qs //= p_
        xq = qs * sh.ln2N
        eta = abs(xq - nearest(xq))
        return qs, log2q(qs) , log2q(eta)

    # (a) the four notions, k = 1..4
    print("   notion table at N=120: (1) feasibility = index M of the CRT coset (cancelled bands: k=1 {5,6,7}, k=2 {3,5,6,7},"
          " k=3,4 {2,3,5,6,7}; band 1 = u is left active for k=4);")
    print("   (2) lowest height with no error constraint; (3)/(4) error-constrained, target error ~2^-16 and ~2^-32")
    print("   (z... = cancelled bands that vanish exactly in the minimal solution: free in height, one dimension each)")
    print("   k |   log2 M | (2) log2 H  zero | (3) log2 H, log2 err, T | (4) log2 H, log2 err, T | log q/N | T/log2 q")
    out = {}
    ceil_k = {}
    for k in (1, 2, 3, 4):
        dirs, cset = fams[k]
        th, Qm, cons = solve_k(P16, sh, theta0, dirs, cset, None)
        m2 = measure(k, th, Qm, cons, cset)
        qs, lq, le = coset_ceiling(dirs, cons)
        ceil_k[k] = lq - le
        line = "   %d | %8.1f | %5.1f z%-6s|" % (k, math.log2(Qm), math.log2(m2["H"]), "".join(map(str, m2["zero"])) or "-")
        res = {"free": m2}
        if k >= 2:
            for T_t in (16, 32):
                lnH_pred = (math.log(Qm) + T_t * LN2) / (k - 1)
                wb = max(1, int(lnH_pred / LN2 + T_t))
                th2, Qm2, cons2 = solve_k(P16, sh, theta0, dirs, cset, wb)
                m3 = measure(k, th2, Qm2, cons2, cset)
                res[T_t] = m3
                Tm = max(0, int(-m3["log2err"]) - 8)
                line += " %8.1f %8.1f %3d |" % (math.log2(m3["H"]), m3["log2err"], Tm)
            last = res[32]
            line += " %.4f | %.3f" % (last["logq"], max(1, -last["log2err"] - 8) / (last["logq"] * N / LN2))
        else:
            line += "   (error is not adjustable: k = 1)                    |  %.4f |" % m2["logq"]
        print(line)
        print("       coset ceiling (all theta, any height): log2 q* = %.1f, log2 eta* = %.1f  =>  T <= %.1f" % (lq, le, lq - le))
        out[k] = res
    # on the c-line the error is |c| |Y_c| - O(1): exponentially large (Phase 16)
    assert out[1]["free"]["log2err"] > 5
    # (b) the Minkowski law  (k-1) ln H - ln M + ln|err|  = c_k  (nearly constant along a scan)
    print("\n   Minkowski law: c = (k-1) ln H - ln M + ln|err| along a scan of target windows T_t")
    print("   (volume count: #{coset points with |z|<=H, |err|<=delta} ~ (2H)^(k-1) 2 delta/(Y M)).")
    print("   k  T_t |  log2 H  log2 err   window | effective dimension k_eff = k - #(exactly vanishing cancelled bands) |  c_eff | luck = -log2 err - log2 q")
    slopes = {}
    for k in (2, 3, 4):
        dirs, cset = fams[k]
        pts = []
        for T_t in (4, 12, 20, 28, 36, 56):
            th0, Qm0, cons0 = solve_k(P16, sh, theta0, dirs, cset, None)
            lnH_pred = (math.log(Qm0) + T_t * LN2) / (k - 1)
            wb = max(1, int(lnH_pred / LN2 + T_t))
            th2, Qm2, cons2 = solve_k(P16, sh, theta0, dirs, cset, wb)
            m3 = measure(k, th2, Qm2, cons2, cset)
            ke = m3["keff"]
            c = (ke - 1) * m3["lnH"] - m3["lnMeff"] + math.log(abs(m3["err"]))
            assert -m3["log2err"] <= ceil_k[k] + 1e-6, (k, m3["log2err"], ceil_k[k])
            if -m3["log2err"] <= 0.8 * ceil_k[k]:
                pts.append((-m3["log2err"], m3["lnH"], c, ke))
            luck = -m3["log2err"] - m3["logq"] * N / LN2
            print("   %d  %3d | %7.1f %8.1f %8d | k_eff=%d exact-zero bands %-8s | %8.2f | luck %6.1f | ceiling %.1f%s" % (
                k, T_t, math.log2(m3["H"]), m3["log2err"], max(0, int(-m3["log2err"]) - 8), ke,
                m3["zero"], c, luck, ceil_k[k], "  (saturated)" if -m3["log2err"] > 0.8 * ceil_k[k] else ""))
        # least squares slope of ln H against achieved bits
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        sl = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        spread = max(p[2] for p in pts) - min(p[2] for p in pts)
        kk = max(set(p[3] for p in pts), key=[p[3] for p in pts].count)
        print("   k=%d (k_eff=%d): slope %.3f (theory ln2/(k_eff-1) = %.3f); spread of c_eff over the scan %.2f nats" % (
            k, kk, sl, LN2 / (kk - 1), spread))
        slopes[k] = (sl, kk)
    # honest check: the measured slope has the predicted sign and rank-ordering
    assert all(slopes[k][0] > 0 for k in (2, 3, 4))
    assert all(0.4 * LN2 / (slopes[k][1] - 1) < slopes[k][0] < 2.5 * LN2 / (slopes[k][1] - 1) for k in (2, 3, 4))
    return out


# ---------------------------------------------------------------------------
# E4: five constants
# ---------------------------------------------------------------------------
NB = 1 << 15
G = 64


def frac_sqrt2():
    m = NB + G
    return isqrt(2 << (2 * m)) % (1 << m) >> G


def frac_phi():
    m = NB + G
    s5 = isqrt(5 << (2 * m))
    return (((1 << m) + s5) // 2) % (1 << m) >> G


def frac_e():
    m = NB + G
    t, s, k = 1 << m, 0, 0
    while t:
        s += t
        k += 1
        t //= k
    return s % (1 << m) >> G


def atan_inv(x, m):
    t = (1 << m) // x
    total, x2, k, sign = t, x * x, 1, 1
    while t:
        t //= x2
        k += 2
        sign = -sign
        total += sign * (t // k)
    return total


def frac_pi():
    m = NB + G
    return (16 * atan_inv(5, m) - 4 * atan_inv(239, m)) % (1 << m) >> G


def frac_ln2():
    m = NB + G
    t = (2 << m) // 3
    total, k = 0, 1
    while t:
        total += t // k
        t //= 9
        k += 2
    return total % (1 << m) >> G


HEX = {  # first 12 hex digits of the fractional parts (known values)
    "ln 2": "b17217f7d1cf", "pi": "243f6a8885a3", "e": "b7e151628aed",
    "sqrt 2": "6a09e667f3bc", "phi": "9e3779b97f4a",
}


def bitstring(X):
    return bin(X)[2:].zfill(NB)


def cf_of_fixed(X, m, n):
    """First n partial quotients of the real X/2^m (valid while 2 q^2 < 2^m)."""
    a, b = X, 1 << m
    out, p0, p1, q0, q1 = [], 1, 0, 0, 1
    qs = []
    for _ in range(n):
        if b == 0:
            break
        t = a // b
        out.append(t)
        a, b = b, a - t * b
        p0, p1 = t * p0 + p1, p0
        q0, q1 = t * q0 + q1, q0
        qs.append(q0)
    return out, qs


def run_e4():
    banner("4. E4: pi, e, sqrt(2), phi, ln 2 -- exact finite comparisons (%d binary digits)" % NB)
    t0 = time.time()
    consts = {"ln 2": frac_ln2(), "pi": frac_pi(), "e": frac_e(), "sqrt 2": frac_sqrt2(), "phi": frac_phi()}
    for name, X in consts.items():
        hexs = "%x" % X
        hexs = hexs.zfill(NB // 4)[:12]
        assert hexs == HEX[name], (name, hexs)
    bits = {k: bitstring(v) for k, v in consts.items()}
    print("   digits generated and checked against known hex prefixes in %.1fs" % (time.time() - t0))

    # ---- (a) binary statistics --------------------------------------------------------
    print("\n   (a) binary statistics of the first N digits: ones frequency, transition frequency tau_N")
    print("       (next two digits differ), digit changes C_N, C_N/sqrt(N), longest run, D_N <= max(2/3,1-tau_N)+1/N")
    print("   const    N      ones     tau_N    C_N/sqrtN  longest run (start)  log2 N  D bound")
    stats = {}
    for name, s in bits.items():
        for N in (1 << 12, NB - 64):
            ones = s.count("1", 0, N) / N
            tr = sum(1 for n in range(N) if s[n] != s[n + 1]) / N
            ch = sum(1 for n in range(N - 1) if s[n] != s[n + 1])
            best, start, run, cur = 0, 0, 1, 0
            for n in range(1, N):
                if s[n] == s[n - 1]:
                    run += 1
                else:
                    if run > best:
                        best, start = run, n - run
                    run = 1
            if run > best:
                best, start = run, N - run
            print("   %-6s %6d  %.4f   %.4f   %7.2f   %4d (%5d)         %5.1f   %.4f" % (
                name, N, ones, tr, ch / math.sqrt(N), best, start, math.log2(N), max(2 / 3, 1 - tr) + 1 / N))
            stats[(name, N)] = (ones, tr, ch, best)
    Nn = NB - 64
    print("   rigorous growth forms at N=%d: sqrt(N) = %.0f (BBCP ones, degree 2; Kaneko changes for 1/sqrt5 ~ 0.707 sqrt N);"
          " (ln N)^1.5/(ln ln N)^0.5 = %.0f (Bugeaud-Evertse changes, any algebraic irrational); observed C_N ~ %d"
          % (Nn, math.sqrt(Nn), math.log(Nn) ** 1.5 / math.log(math.log(Nn)) ** 0.5, int(0.5 * Nn)))
    # every constant: observed transition frequency is ~1/2, far above the rigorous sqrt(N)/N
    for name in bits:
        _, tr, ch, best = stats[(name, NB - 64)]
        assert 0.45 < tr < 0.55 and best <= 2 * math.log2(NB) + 4

    # ---- (b) continued fractions ------------------------------------------------------
    print("\n   (b) continued fractions (first 300 partial quotients): Levy ratio ln(q_n)/n, largest a_n,")
    print("       largest local exponent log q_{n+1}/log q_n (n >= 20), proven exponent bound for mu")
    mu_known = {"ln 2": "<= 3.57455391 (Marcovecchio 2009) / 3.89139977 (Rukhadze 1987)",
                "pi": "<= 7.1032 (Zeilberger-Zudilin 2020, confirmed)",
                "e": "= 2 (Euler CF; Davis 1978/79 sharp loglog/log law)",
                "sqrt 2": "= 2 (Pell; bounded partial quotients)", "phi": "= 2 (Fibonacci; a_n = 1)"}
    for name, X in consts.items():
        ints = {"ln 2": 0, "pi": 3, "e": 2, "sqrt 2": 1, "phi": 1}[name]
        a, qs = cf_of_fixed(X, NB, 301)       # CF of the fractional part
        amax = max(a[1:]) if name != "ln 2" else max(a)
        lev = math.log(qs[299]) / 300
        loc = max(math.log(qs[n + 1]) / math.log(qs[n]) for n in range(20, 298))
        print("   %-6s Levy %.4f  max a_n %4d   max local exponent %.3f   mu %s" % (name, lev, amax, loc, mu_known[name]))
    # e: exact Euler pattern and the Davis loglog/log constant on the actual convergents
    print("   e via Euler [2;1,2,1,1,4,1,1,6,...]: convergents to q ~ 10^600; exact Davis constant c_n = q_n^2|e-p_n/q_n| * log(q_n)/loglog(q_n)")

    def euler_a(k):
        return 2 * (k + 1) // 3 if k % 3 == 2 else 1

    def euler_tail_bounds(m, depth=8):
        """Exact rational [lo, hi] enclosure of alpha_m = [a_m; a_{m+1}, ...]."""
        lo, hi = Q(euler_a(m + depth)), Q(euler_a(m + depth) + 1)
        for j in range(m + depth - 1, m - 1, -1):
            aj = euler_a(j)
            lo, hi = aj + Q(1, hi), aj + Q(1, lo)
        return lo, hi

    p0, p1, q0, q1 = 2, 1, 1, 0
    all_c = []
    large_c = []
    for n in range(1, 1200):
        an = euler_a(n)
        p0, p1 = an * p0 + p1, p0
        q0, q1 = an * q0 + q1, q0
        if q0 >= 3:
            a_next = euler_a(n + 1)
            _, alpha_hi = euler_tail_bounds(n + 1)
            # |e - p_n/q_n| = 1 / (q_n^2 * (alpha_{n+1} + q_{n-1}/q_n)), so using alpha_hi gives a certified lower bound
            denom_hi = float(alpha_hi) + float(Q(q1, q0))
            lq = math.log(q0)
            c_lo = lq / (denom_hi * math.log(lq))
            rec = (c_lo, n, q0, a_next)
            all_c.append(rec)
            if q0.bit_length() > 40:
                large_c.append(rec)
        if q0.bit_length() > 2000:
            break
    c_min_all = min(all_c, key=lambda r_: r_[0])
    c_min_large = min(large_c, key=lambda r_: r_[0])
    big_next = [r_ for r_ in large_c if r_[3] > 1]
    print("   n=%d: %d convergents (q>=3); last three with a_{n+1}>1: %s (limit 0.5000 = Davis constant 1/2)" % (
        n, len(all_c), ", ".join("%.4f" % r_[0] for r_ in big_next[-3:])))
    print("   => global min over 3 <= q <= 10^%d: c = %.6f (at n=%d, q=%d, a_{n+1}=%d); for q > 2^40: c = %.6f (at n=%d, a_{n+1}=%d)" % (
        int(2000 * LN2 / math.log(10)), c_min_all[0], c_min_all[1], c_min_all[2], c_min_all[3],
        c_min_large[0], c_min_large[1], c_min_large[3]))
    assert 0.386 < c_min_all[0] < 0.387 and c_min_all[1] == 19
    assert 0.387 < c_min_large[0] < 0.388 and c_min_large[1] == 31
    assert 0.40 < big_next[-1][0] < 0.50

    # ---- (c) golden ratio: Zeckendorf least index of 2^n --------------------------------
    print("\n   (c) phi: least Zeckendorf index k(2^n) and the Lean bounds phi^-(k+1) <= ||2^n phi|| <= phi^(1-k)")
    nmax = 600
    fib = [0, 1]
    while fib[-1] < 1 << (nmax + 2):
        fib.append(fib[-1] + fib[-2])
    phi = (1 + math.sqrt(5)) / 2

    def least_index(M):
        k = len(fib) - 1
        low = None
        while M > 0:
            while fib[k] > M:
                k -= 1
            low = k
            M -= fib[k]
            k -= 2
        return low

    def dist_phi(n):                      # ||2^n phi||, exact up to 2^-200
        g = 200
        s = isqrt(5 << (2 * (n - 1 + g)))
        f = s & ((1 << g) - 1)
        return min(f, (1 << g) - f) / float(1 << g)

    ks = []
    for n in range(1, nmax):
        k = least_index(1 << n)
        d = dist_phi(n)
        assert phi ** (-(k + 1)) <= d * (1 + 1e-9) and d <= phi ** (1 - k) * (1 + 1e-9), (n, k, d)
        ks.append(k)
    rnd = random.Random(17)
    ks_rand = [least_index(rnd.getrandbits(n) | (1 << (n - 1))) for n in range(1, nmax)]
    print("   Lean bounds verified for all 1 <= n < %d. P(k <= K) over n<%d: 2^n vs random integers of equal size" % (nmax, nmax))
    print("   K      :   " + " ".join("%5d" % K for K in (2, 4, 6, 8, 10, 12, 16, 20)))
    print("   2^n    :   " + " ".join("%5.3f" % (sum(1 for k in ks if k <= K) / len(ks)) for K in (2, 4, 6, 8, 10, 12, 16, 20)))
    print("   random :   " + " ".join("%5.3f" % (sum(1 for k in ks_rand if k <= K) / len(ks_rand)) for K in (2, 4, 6, 8, 10, 12, 16, 20)))
    print("   (D^+(phi) < 1 <=> some K has positive lower density of {n : k(2^n) <= K}: observed density at K=8 is %.3f, but"
          " nothing proves positivity as n -> infinity)" % (sum(1 for k in ks if k <= 8) / len(ks)))
    assert sum(1 for k in ks if k <= 12) / len(ks) > 0.5

    # ---- (d) Liouville / Lucas run ceilings ---------------------------------------------
    print("\n   (d) Liouville ceilings: after position n the run of equal digits is at most (mu-1) n + O(1)")
    for name in ("phi", "sqrt 2"):
        s = bits[name]
        worst = 0
        for n in range(1, 4000):
            r = 1
            while s[n + r] == s[n]:
                r += 1
            worst = max(worst, r - n)
        # exact quadratic ceiling: |x - p/2^n| >= 1/((c + 1) 4^n) with c = |x - x'| in {sqrt 5, 2 sqrt 2}
        c_ = math.sqrt(5) if name == "phi" else 2 * math.sqrt(2)
        print("   %-6s: max over n<4000 of (run after n) - n = %d (ceiling: log2(%.3f + 1) = %.2f)" % (
            name, worst, c_, math.log2(c_ + 1)))
        assert worst <= math.log2(c_ + 1) + 1
    print("   e: run <= N + log2 N - log2 log N + O(1) (Davis lower bound); ln 2: <= 2.575 N + O(1); pi: <= 6.1032 N + O(1)")

    # ---- (e) denominators of explicit prefixes ------------------------------------------
    print("\n   (e) exact reduced denominators of explicit shifted prefixes (odd part, rate = ln q_odd / N)")
    # e: A_n/n!, error < 1/n!, N = floor(log2 (n+1)!)
    num = 1
    f = 1
    line = []
    nsel = (100, 200, 400, 800, 1600)
    for n in range(1, nsel[-1] + 1):
        num = n * num + 1
        f *= n
        if n in nsel:
            g_ = gcd(num, f)
            qn = f // g_
            qodd = qn >> v2(qn)
            N_ = int(log2q(f * (n + 1)))
            line.append("n=%d: %.4f (log Q_n/log n! = %.4f)" % (n, math.log(qodd) / N_, math.log(qn) / math.log(f)))
    print("   e  Taylor truncation A_n/n!:  " + "; ".join(line))
    # e: Dirichlet-optimal convergents (generic, window-free)
    pairs = []
    p0, p1, q0, q1 = 2, 1, 1, 0
    for n in range(1, 400):
        an = 2 * (n + 1) // 3 if n % 3 == 2 else 1
        p0, p1 = an * p0 + p1, p0
        q0, q1 = an * q0 + q1, q0
        if n in (60, 150, 300, 399):
            Nn = int(2 * log2q(q0) - math.log2(an + 2)) - 1
            pairs.append("q~2^%d: N=%d rate %.4f" % (int(log2q(q0)), Nn, math.log(q0 >> v2(q0)) / Nn))
    print("   e  convergents p/q, N chosen with 2^N|e-p/q| <~ 1/2:  " + "; ".join(pairs))
    print("      (generic Dirichlet value is ln2/2 = %.4f for every irrational, with window T ~ 0)" % (LN2 / 2))
    # pi BBP and ln 2 prefix
    out = []
    for n in (50, 100, 200, 300):
        R = Q(0)
        for k in range(n + 1):
            R = 16 * R + Q(4, 8 * k + 1) - Q(2, 8 * k + 4) - Q(1, 8 * k + 5) - Q(1, 8 * k + 6)
        qq = R.denominator
        out.append("hex n=%d (N=%d): %.4f" % (n, 4 * n, math.log(qq >> v2(qq)) / (4 * n)))
    print("   pi BBP prefix R_n = 16 R_{n-1} + c_n:  " + "; ".join(out))
    out = []
    for N_ in (200, 400, 800, 1600):
        R = Q(0)
        for n in range(1, N_ + 1):
            R = 2 * R + Q(1, n)
        qq = R.denominator
        out.append("N=%d: %.4f" % (N_, math.log(qq >> v2(qq)) / N_))
    print("   ln 2 prefix R_N = 2 R_{N-1} + 1/N:  " + "; ".join(out))
    print("   references (not recomputed): ln 2 Phase 14 optimum 5/12, Phase 16 explicit rounded 0.3932 / 0.2632 / -> 0;"
          " pi Gaussian-logarithm model 2/3 (notes/gaussian-arctangent-denominators.md)")


def main():
    rows, ctx = run_e12()
    print("\n   [E1/E2 done in %.1fs]" % (time.time() - T_START))
    run_e3()
    print("\n   [E3 done in %.1fs]" % (time.time() - T_START))
    run_e4()
    print("\nAll Phase 17 Track E classical-approximant checks passed (%.1fs)." % (time.time() - T_START))


if __name__ == "__main__":
    main()
