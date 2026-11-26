#!/usr/bin/env python3
"""Phase 22, Track E: classical targets and reconnaissance (verification script).

Companion to notes/phase22/classical-targets-and-recon.md.  Pure standard library,
exits 0 when every assertion holds.  Sections:

  E1  Erdos-Borwein E(b) and E_+(b) = sum 1/(b^n+1): identities, coefficients,
      mean log 2, comparison-model constants, finite digits; moment-class
      countermodels (exact rational laws) for the minimal correlation order.
  E2  Kempner's number sum 2^(-2^k): continued fraction bounded by 6 (badly
      approximable) while its binary orbit concentrates (K_2); ln 2 contrast.
  E3  Cahen's constant, reciprocal Fibonacci constant, Catalan values C(1/b),
      Apery's zeta(3), and C_1 = [0;1,2,3,...] = I_1(2)/I_0(2).

Evidence labels used in the printout:
  [exact]   integer / rational arithmetic, or a 50-digit identity check;
  [model]   floating-point evaluation of the comparison model (not a proof);
  [finite]  finite digit data (bears on no limit).
"""

import math
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction as Fr
from math import comb, factorial

T0 = time.time()
CHECKS = [0]


def check(cond, msg):
    CHECKS[0] += 1
    if not cond:
        print("FAILED:", msg)
        sys.exit(1)


def head(title):
    print("\n" + "=" * 78 + "\n" + title + "\n" + "=" * 78)


getcontext().prec = 90
TOL50 = Decimal(10) ** -50


def dclose(a, b, tol=TOL50):
    return abs(a - b) < tol


# ---------------------------------------------------------------- utilities
def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def odd_part(k):
    while k % 2 == 0:
        k //= 2
    return k


def v2(k):
    e = 0
    while k % 2 == 0:
        k //= 2
        e += 1
    return e


def dc_sum(a, lo, hi):
    """Integer sum_{lo<=n<hi} a[n] 2^(hi-1-n) by divide and conquer."""
    if hi - lo <= 64:
        s = 0
        for n in range(lo, hi):
            s = 2 * s + a[n]
        return s
    mid = (lo + hi) // 2
    return (dc_sum(a, lo, mid) << (hi - mid)) + dc_sum(a, mid, hi)


def frac_bits(X, L):
    """Binary digits 1..L of X / 2^L (fractional part) as a '0'/'1' string."""
    ip = X >> L
    return ip, bin(X - (ip << L))[2:].zfill(L)


def ext_discrepancy(bits, N):
    """Extreme discrepancy of {2^n x}, 0<=n<N, from the digit string (53-bit points)."""
    pts = sorted(int(bits[n:n + 53], 2) / 2.0 ** 53 for n in range(N))
    a = max((i + 1) / N - x for i, x in enumerate(pts))
    b = max(x - i / N for i, x in enumerate(pts))
    return a + b


def cf_of_fraction(p, q):
    out = []
    while q:
        k = p // q
        out.append(k)
        p, q = q, p - k * q
    return out


def common_prefix(a, b):
    i = 0
    while i < min(len(a), len(b)) and a[i] == b[i]:
        i += 1
    return i


def d_pi():
    """pi by Machin's formula in the current Decimal context."""
    def atan_inv(n):
        x = Decimal(1) / n
        x2 = x * x
        s, t, k = Decimal(0), x, 0
        while abs(t) > Decimal(10) ** -(getcontext().prec + 2):
            s += t / (2 * k + 1)
            t = -t * x2
            k += 1
        return s
    return 16 * atan_inv(5) - 4 * atan_inv(239)


def d_ln2():
    # ln 2 = (2/3) sum 9^-k/(2k+1)
    s, t, k = Decimal(0), Decimal(1), 0
    while t > Decimal(10) ** -(getcontext().prec + 2):
        s += t / (2 * k + 1)
        t /= 9
        k += 1
    return Decimal(2) / 3 * s


PI = d_pi()
LN2 = d_ln2()


# =============================================================== E1
def section_E1():
    head("E1. Erdos-Borwein E(b) and E_+(b) = sum_{n>=1} 1/(b^n+1)")

    # --- 1. the identities E_+(b) = E(b) - 2E(b^2) = E_odd(b) - E(b^2)
    def E(b, step=1, start=1):
        s, m = Decimal(0), start
        while True:
            t = Decimal(1) / (Decimal(b) ** m - 1)
            if t < Decimal(10) ** -85:
                return s
            s += t
            m += step

    def Eplus(b):
        s, m = Decimal(0), 1
        while True:
            t = Decimal(1) / (Decimal(b) ** m + 1)
            if t < Decimal(10) ** -85:
                return s
            s += t
            m += 1

    for b in (2, 3, 10):
        ep, e1, e2, eo = Eplus(b), E(b), E(b * b), E(b, 2, 1)
        check(dclose(ep, e1 - 2 * e2), "E_+ = E - 2E(b^2), b=%d" % b)
        check(dclose(ep, eo - e2), "E_+ = E_odd - E(b^2), b=%d" % b)
        check(dclose(e1 + ep, 2 * eo), "E + E_+ = 2E_odd, b=%d" % b)
        check(dclose(e1 - ep, 2 * e2), "E - E_+ = 2E(b^2), b=%d" % b)
        print("[exact] b=%2d  E_+(b) = %s  (= E - 2E(b^2) = E_odd - E(b^2), 50 digits)"
              % (b, str(ep)[:32]))

    # --- 2. coefficients a_+(n) for n <= 100000
    X = 100000
    tau = [0] * (X + 1)
    tau_odd = [0] * (X + 1)
    alt = [0] * (X + 1)
    for d in range(1, X + 1):
        sgn = 1 if d % 2 else -1
        for m in range(d, X + 1, d):
            tau[m] += 1
            alt[m] += sgn
            if d % 2:
                tau_odd[m] += 1
    ap = [0] * (X + 1)
    for n in range(1, X + 1):
        ap[n] = tau[n] - (2 * tau[n // 2] if n % 2 == 0 else 0)
        e = v2(n)
        check(ap[n] == (1 - e) * tau_odd[n], "a_+(n) = (1-v_2(n)) tau_odd(n)")
        check(ap[n] == alt[n], "a_+(n) = sum_{d|n} (-1)^(d-1)")
        check((ap[n] % 2 == 1) == (math.isqrt(n) ** 2 == n), "a_+(n) odd iff n square")
    zeros = sum(1 for n in range(1, X + 1) if ap[n] == 0)
    check(all(ap[n] == 0 for n in range(2, X + 1, 4)), "a_+ = 0 on n = 2 mod 4")
    check(zeros == X // 4 + (1 if X % 4 >= 2 else 0), "zeros exactly n = 2 mod 4")
    print("[exact] a_+(n) = tau(n) - 2[2|n]tau(n/2) = (1-v_2(n)) tau_odd(n) = sum_{d|n}(-1)^(d-1),"
          " n <= %d; zeros exactly at n = 2 mod 4; odd iff n is a square" % X)

    # --- 3. mean log 2 and the hyperbola identity
    ln2 = math.log(2)
    S = 0
    marks = {1000, 10000, 100000}
    print("[exact]      X   sum a_+(n)   X log 2     dev/sqrt(X)   sum a_+^2 / sum tau^2")
    s2a = s2t = 0
    for n in range(1, X + 1):
        S += ap[n]
        s2a += ap[n] ** 2
        s2t += tau[n] ** 2
        if n in marks:
            hyper = sum((1 if d % 2 else -1) * (n // d) for d in range(1, n + 1))
            check(hyper == S, "sum a_+ = sum_d (-1)^(d-1) floor(X/d)")
            dev = (S - n * ln2) / math.sqrt(n)
            check(abs(dev) < 2.0, "partial sum within 2 sqrt(X) of X log 2 (finite)")
            print("        %7d %11d %12.2f %12.4f %14.4f" % (n, S, n * ln2, dev, s2a / s2t))
    check(abs(s2a / s2t - 1 / 3) < 0.05, "second moment ratio near 1/3 (finite)")

    # --- 4. comparison-model constants (CC-49 law Q_inf and its signed analogue)
    t = time.time()
    P = 3000
    plist = primes_upto(P)
    MMAX = 1023

    def mark_law(include2):
        law = {1: 1.0}
        for p in plist:
            if p == 2 and not include2:
                continue
            f = {}
            for a in range(60):
                pr = (1 - 1 / p) * p ** (-a)
                if pr < 1e-18:
                    break
                u = odd_part(a + 1)
                f[u] = f.get(u, 0.0) + pr
            new = {}
            for x, px in law.items():
                for u, pu in f.items():
                    y = min(x * u, MMAX + 1)
                    new[y] = new.get(y, 0.0) + px * pu
            law = new
        tail = sum(1.0 / (p * p) for p in primes_upto(200000) if p > P)
        new = {}
        for x, px in law.items():
            new[x] = new.get(x, 0.0) + px * (1 - tail)
            y = min(3 * x, MMAX + 1)
            new[y] = new.get(y, 0.0) + px * tail
        law = {u: p for u, p in new.items() if u <= MMAX}
        s = sum(law.values())
        return {u: p / s for u, p in law.items()}

    nu = mark_law(True)
    nuo = mark_law(False)
    mu = sum(u * p for u, p in nu.items())
    mu_o = sum(u * p for u, p in nuo.items())
    E2 = sum(odd_part(k) * 2.0 ** -k for k in range(1, 200))
    check(abs(mu - 2.07630) < 1e-4 and 2.0762592 - 2e-5 < mu < 2.0763285 + 2e-5,
          "mu matches the CC-49 enclosure")
    print("        mu/mu_odd = %.7f, E_2 = %.7f" % (mu / mu_o, E2))
    check(abs(mu / mu_o - E2) < 1e-4, "mu = E_2 mu_odd (2-factor of the Euler product)")
    mu_pos, mu_neg = mu_o / 2, mu_o * E2 / 4

    def panjer(law, lam, jmax):
        b = [0.0] * (jmax + 1)
        b[0] = math.exp(-lam)
        items = sorted(law.items())
        for j in range(1, jmax + 1):
            b[j] = lam / j * sum(u * p * b[j - u] for u, p in items if u <= j)
        return b

    def carry_law(J, iters=48):
        c = {0: 1.0}
        for _ in range(iters):
            new = {}
            for j, pj in J.items():
                for x, px in c.items():
                    w = pj * px
                    if w > 1e-17:
                        y = (j + x) // 2
                        new[y] = new.get(y, 0.0) + w
            c = new
        return c

    JE = {j: p for j, p in enumerate(panjer(nu, 1.0, 300)) if p > 1e-16}
    cE = carry_law(JE)
    parE = sum(p * (-1) ** x for x, p in cE.items())
    pstar = 0.5 - 0.5 * math.exp(-2) * parE
    check(0.111481733 - 2e-5 < parE < 0.111502881 + 2e-5, "E(-1)^c_1 matches CC-49")
    check(0.492450290 - 2e-5 < pstar < 0.492460864 + 2e-5, "p_* matches CC-49")

    neg = {}
    for e in range(2, 50):
        for u, p in nuo.items():
            v = odd_part(e - 1) * u
            if v <= MMAX:
                neg[v] = neg.get(v, 0.0) + 2.0 ** (-(e - 1)) * p
    s = sum(neg.values())
    neg = {u: p / s for u, p in neg.items()}
    Jp = panjer(nuo, 0.5, 300)
    Jn = panjer(neg, 0.25, 300)
    JP = {}
    for a, pa in enumerate(Jp):
        if pa < 1e-16:
            continue
        for bb, pb in enumerate(Jn):
            if pa * pb > 1e-17:
                JP[a - bb] = JP.get(a - bb, 0.0) + pa * pb
    cP = carry_law(JP)
    parP = sum(p * (-1) ** x for x, p in cP.items())
    pplus = 0.5 - 0.5 * math.exp(-1.5) * parP
    check(abs((mu_pos - mu_neg) - mu_o * (0.5 - E2 / 4)) < 1e-12, "signed tail mean")
    check(0.47 < pplus < 0.485, "E_+ model frequency in the expected range")
    print("[model] mu = %.6f, E(-1)^c = %.6f, p_* = %.6f  (CC-49 enclosures reproduced)"
          % (mu, parE, pstar))
    print("[model] E_+: source rate 3/4, mu_pos = %.6f, mu_neg = %.6f, net = %.6f"
          % (mu_pos, mu_neg, mu_pos - mu_neg))
    print("[model] E_+: E(-1)^c = %.6f, p_+ = %.6f, bias 1/2 - p_+ = %.6f (E: %.6f, ratio %.2f)"
          % (parP, pplus, 0.5 - pplus, 0.5 - pstar, (0.5 - pplus) / (0.5 - pstar)))
    print("        model time %.1fs" % (time.time() - t))

    # --- 5. finite binary digits of E and E_+
    t = time.time()
    N = 1 << 19
    G = 64
    L = N + G
    tauL = [0] * (L + 1)
    for d in range(1, L + 1):
        for m in range(d, L + 1, d):
            tauL[m] += 1
    apL = [0] * (L + 1)
    for n in range(1, L + 1):
        apL[n] = tauL[n] - (2 * tauL[n // 2] if n % 2 == 0 else 0)
    ipE, bE = frac_bits(dc_sum(tauL, 1, L + 1), L)
    ipP, bP = frac_bits(dc_sum(apL, 1, L + 1), L)
    # guard: the omitted tail is < 2^12 in units of 2^-L; keep N digits
    check(ipE == 1 and bE.startswith("1001101101010000010111111"), "binary digits of E")
    check(ipP == 0, "E_+ < 1")
    for bits in (bE, bP):
        g = bits[N - 1:N + G - 12]
        check("0" in g and "1" in g, "guard bits not a single run (digits 1..N certain)")
    print("[finite] E_+(2) = 0.%s..._2" % bP[:40])
    print("[finite] shell frequencies of 1 (shifts n in [2^s, 2^(s+1)), i.e. digits 2^s+1..2^(s+1));"
          " model p_* = %.4f, p_+ = %.4f"
          % (pstar, pplus))
    for sh in range(12, 19):
        a, b = 1 << sh, 1 << (sh + 1)
        print("         s=%2d   E %.6f   E_+ %.6f" % (sh, bE[a:b].count("1") / (b - a),
                                                    bP[a:b].count("1") / (b - a)))
    for n_ in (1000, 10000, 100000):
        dE, dP = ext_discrepancy(bE, n_), ext_discrepancy(bP, n_)
        print("[finite] D_N  N=%6d   E %.4f   E_+ %.4f" % (n_, dE, dP))
    print("        digits time %.1fs" % (time.time() - t))
    return nu, JE, JP, mu_pos, mu_neg


def section_thresholds(JE, JP, mu_pos, mu_neg):
    """Model column thresholds f_sup(D) (CC-49 knapsack; signed two-budget version for E_+)."""
    head("E1. Column thresholds (model; slow)")

    def cellmass(J, t, D):
        st = {0: 1.0}
        for i in range(D):
            bit = (t >> i) & 1
            new = {}
            for c, pc in st.items():
                for j, pj in J.items():
                    v = j + c
                    if (v - bit) % 2:
                        continue
                    w = pc * pj
                    if w > 1e-18:
                        nc = (v - bit) // 2
                        new[nc] = new.get(nc, 0.0) + w
            st = new
        return sum(st.values())

    def toppar(J, D):
        c = {0: 1.0}
        for _ in range(D - 1):
            new = {}
            for j, pj in J.items():
                for x, px in c.items():
                    w = pj * px
                    if w > 1e-18:
                        y = (j + x) // 2
                        new[y] = new.get(y, 0.0) + w
            c = new
        return sum(p * (-1) ** x for x, p in c.items())

    def fsup(J, lam, D, budgets):
        val = 0.5 - 0.5 * math.exp(-2 * lam) * toppar(J, D)
        for side, B in budgets:
            k = 0 if side == "neg" else 1
            rem = B
            while True:
                t = (1 << (D - 1)) - k if side == "pos" else k
                m = cellmass(J, t, D)
                if k == 0:
                    val += m       # the cell r = 0 wraps under any negative carry: free
                elif k * m <= rem:
                    val += m
                    rem -= k * m
                else:
                    val += rem / k
                    break
                k += 1
        return val

    for D, lo, hi in ((15, 0.502823, 0.502828), (16, 0.499732, 0.499736)):
        v = fsup(JE, 1.0, D, [("pos", 2.0763285)])
        check(lo - 2e-5 < v < hi + 2e-5, "reproduces the certified CC-49 value at D=%d" % D)
        print("[model] E    D=%d  f_sup = %.6f  (CC-49 certified [%.6f, %.6f])" % (D, v, lo, hi))
    for D in (12, 13, 14):
        v = fsup(JP, 0.75, D, [("pos", mu_pos), ("neg", mu_neg)])
        print("[model] E_+  D=%d  f_sup = %.6f" % (D, v))
        check((v > 0.5) == (D <= 13), "E_+ threshold is 14 columns (model)")


# =============================================================== E1(a)
def section_E1a(nu):
    head("E1(a). Moment classes: exact two-column countermodels")
    # parity Bonferroni values e_r (CC-49 Theorem parity)
    e_r = {r: sum(Fr((-2) ** k, factorial(k)) for k in range(r + 1)) for r in range(1, 14, 2)}
    check(e_r[5] == Fr(1, 15) and e_r[7] == Fr(41, 315) and e_r[9] == Fr(383, 2835),
          "parity Bonferroni values")
    # carry law mod 4 and mark law mod 4 in the CC-49 comparison model
    pi1 = sum(p for u, p in nu.items() if u % 4 == 1)
    b = [0.0] * 301
    b[0] = math.exp(-1)
    items = sorted(nu.items())
    for j in range(1, 301):
        b[j] = 1.0 / j * sum(u * p * b[j - u] for u, p in items if u <= j)
    J = {j: p for j, p in enumerate(b) if p > 1e-16}
    c = {0: 1.0}
    for _ in range(48):
        new = {}
        for j, pj in J.items():
            for x, px in c.items():
                w = pj * px
                if w > 1e-17:
                    y = (j + x) // 2
                    new[y] = new.get(y, 0.0) + w
        c = new
    cm = [0.0] * 4
    for x, p in c.items():
        cm[x % 4] += p
    g = [1, 1, -1, -1]

    def h(n):
        d = [1.0, 0.0, 0.0, 0.0]
        for _ in range(n):
            d = [d[(a - 1) % 4] * pi1 + d[(a - 3) % 4] * (1 - pi1) for a in range(4)]
        return sum(d[a] * cm[bb] * g[(a + bb) % 4] for a in range(4) for bb in range(4))

    Hn = [h(n) for n in range(64)]
    # closed form: S_n mod 4 has steps +-1, so E i^{S_n} = (i t)^n with t = 2 pi1 - 1, and
    # g(x) = Re i^x + Im i^x; hence h(n) = t^n * sum_b c_b g(n + b).
    tt = 2 * pi1 - 1
    for n in range(20):
        closed = tt ** n * sum(cm[bb] * g[(n + bb) % 4] for bb in range(4))
        check(abs(closed - Hn[n]) < 1e-12, "closed form of h(n)")
    EH = sum(math.exp(-1) / factorial(n) * Hn[n] for n in range(64))
    check(abs(EH - 0.1114931) < 3e-5, "E h(N_2) = E(-1)^{c_1} under Q_inf")
    print("[model] P(U=1 mod 4) = %.6f; carry mod 4 law = %s; E h(N_2) = %.6f"
          % (pi1, ", ".join("%.6f" % v for v in cm), EH))
    print("[model] h(n) = E[(-1)^{c_1} | N_2 = n] = (2 pi1 - 1)^n sum_b c_b g(n+b): %s"
          % ", ".join("%.4f" % v for v in Hn[:6]))
    cert = certify_mod4_inputs()
    (p_lo, p_hi), c_lo, c_hi = cert
    print("[certificate] P(U=1 mod 4) in [%.6f, %.6f]" % (p_lo, p_hi))
    print("[certificate] carry residues mod 4 in %s"
          % ", ".join("[%.6f, %.6f]" % (float(a), float(b)) for a, b in zip(c_lo, c_hi)))
    check(p_lo <= pi1 <= p_hi and all(a <= x <= b for a, x, b in zip(c_lo, cm, c_hi)),
          "floating-point model inputs lie inside the certified intervals")
    for r, atoms in COUNTERMODELS.items():
        w = [(a, bb, Fr(num, den)) for (a, bb, num, den) in atoms]
        check(all(x > 0 for _, _, x in w), "positive weights")
        for i in range(r + 1):
            for j in range(r + 1 - i):
                mom = sum(x * comb(a, i) * comb(bb, j) for a, bb, x in w)
                check(mom == Fr(1, factorial(i) * factorial(j)),
                      "mixed factorial moment (%d,%d) exact" % (i, j))
        obj = sum(float(x) * (-1) ** a * Hn[bb] for a, bb, x in w)
        f1 = 0.5 - 0.5 * obj
        # robustness: |delta h(n)| <= (4 + 2n) delta for perturbations delta of cm and pi1;
        # E N_2 = 1 exactly, so |delta obj| <= 6 delta.  Round the radius DOWN.
        radius = math.floor(-obj / 6 * 1e4) / 1e4
        check(f1 > 0.5, "countermodel has f(1) > 1/2 (order %d)" % r)
        f_lo = certified_f1_lower(w, cert)
        check(f_lo > Fr(1, 2), "certified f(1) > 1/2 (order %d)" % r)
        print("[exact moments] order r=%d: %d atoms on {0..%d}^2; model f(1) = %.6f "
              "(robust for input errors < %.4f)"
              % (r, len(w), max(max(a, bb) for a, bb, _ in w), f1, radius))
        print("[certificate]   order r=%d: f(1) >= %.6f > 1/2 for every value of the five inputs"
              " in the certified intervals" % (r, math.floor(float(f_lo) * 1e6) / 1e6))
    print("        => in the CC-49 information classes, r_min(D) >= %d for EVERY D >= 2"
          " (finite certificate)" % (max(COUNTERMODELS) + 1))


def certify_mod4_inputs(P=4000, MMAX=511, JMAX=255, T=18):
    """Outward-rounded enclosures of P(U = 1 mod 4) and of P(c = b mod 4), b = 0..3, under Q_inf.

    Integer lower measures at scale S = 2^64 (every product and quotient floored), so each
    computed mass is a lower bound for the true one; the missing mass bounds the excess.
      * marks: primes p <= P exactly (all exponents a with p^-a >= 2^-64), marks <= MMAX;
        primes p > P contribute the factor 1 on the event {all B_p <= 1}, of probability
        >= 1 - sum_{n > P odd} n^-2 >= 1 - 1/(2(P-1)).
      * column law: Panjer recursion b_j = (1/j) sum_u u nu(u) b_{j-u}, b_0 = e^-1 (lower
        bound from the alternating series), j <= JMAX; monotone in nu.
      * carry: c^(T) = floor(sum_{i<=T} J_i 2^-i) by T carry steps; P(c != c^(T)) <=
        E floor(Y_T) * max_r P(R_T = r) <= mu * p0^T (CC-49 Lemma "depth truncation"),
        with mu <= 2.0763285 (CC-49 certified enclosure) and p0 = (1 + e^-2)/2 < 0.5677.
    """
    S = 1 << 64
    law = {1: S}
    for p in primes_upto(P):
        f = {}
        a = 0
        while True:
            v = S * (p - 1) // p ** (a + 1)
            if v == 0:
                break
            u = odd_part(a + 1)
            f[u] = f.get(u, 0) + v
            a += 1
        new = {}
        for x, px in law.items():
            for u, pu in f.items():
                y = x * u
                if y <= MMAX:
                    new[y] = new.get(y, 0) + px * pu // S
        law = new
    big = S - (-(-S // (2 * (P - 1))))           # floor(S (1 - 1/(2(P-1))))
    law = {u: pu * big // S for u, pu in law.items()}
    miss_nu = Fr(S - sum(law.values()), S)
    p1 = Fr(sum(pu for u, pu in law.items() if u % 4 == 1), S)
    pi1_int = (p1, p1 + miss_nu)
    em1 = sum(Fr((-1) ** k, factorial(k)) for k in range(42))   # ends on a negative term
    check(Fr(3678794411714423, 10 ** 16) < em1 < Fr(3678794411714424, 10 ** 16), "e^-1 bound")
    b = [0] * (JMAX + 1)
    b[0] = em1.numerator * S // em1.denominator
    items = sorted(law.items())
    for j in range(1, JMAX + 1):
        b[j] = sum(u * pu * b[j - u] for u, pu in items if u <= j) // (j * S)
    J = {j: v for j, v in enumerate(b) if v}
    x = {0: S}
    for _ in range(T):
        new = {}
        for j, pj in J.items():
            for c, pc in x.items():
                y = (j + c) // 2
                new[y] = new.get(y, 0) + pj * pc // S
        x = new
    miss = Fr(S - sum(x.values()), S)
    delta = Fr(20763285, 10 ** 7) * Fr(5677, 10000) ** T
    check(Fr(5677, 10000) > (1 + Fr(13534, 100000)) / 2, "p0 upper bound (e^-2 < 0.13534)")
    low = [Fr(sum(v for c, v in x.items() if c % 4 == bb), S) for bb in range(4)]
    c_lo = [max(Fr(0), l - delta) for l in low]
    c_hi = [l + miss + delta for l in low]
    return pi1_int, c_lo, c_hi


def certified_f1_lower(w, cert):
    """Lower bound for f(1) = 1/2 - obj/2, obj = sum w (-1)^n1 h(n2), over the enclosures.

    h(n) = t^n A_{n mod 4}, t = 2 pi1 - 1 > 0, A_m = sum_b c_b g(m+b), A_2 = -A_0, A_3 = -A_1.
    So obj = A_0 P_0(t) + A_1 P_1(t) with explicit rational polynomials P_0, P_1.
    """
    (p_lo, p_hi), c_lo, c_hi = cert
    g = [1, 1, -1, -1]
    t_lo, t_hi = 2 * p_lo - 1, 2 * p_hi - 1
    check(t_lo > 0, "t > 0")
    A = []
    for m in (0, 1):
        lo = sum(c_lo[bb] if g[(m + bb) % 4] > 0 else -c_hi[bb] for bb in range(4))
        hi = sum(c_hi[bb] if g[(m + bb) % 4] > 0 else -c_lo[bb] for bb in range(4))
        A.append((lo, hi))
    polys = [{}, {}]
    for a, bb, x in w:
        sign = (-1) ** a * (1 if bb % 4 in (0, 1) else -1)
        polys[bb % 2][bb] = polys[bb % 2].get(bb, 0) + sign * x
    hi_obj = Fr(0)
    for m in (0, 1):
        pos = lambda t: sum(cf * t ** e for e, cf in polys[m].items() if cf > 0)
        neg = lambda t: sum(-cf * t ** e for e, cf in polys[m].items() if cf < 0)
        P_lo, P_hi = pos(t_lo) - neg(t_hi), pos(t_hi) - neg(t_lo)
        hi_obj += max(A[m][0] * P_lo, A[m][0] * P_hi, A[m][1] * P_lo, A[m][1] * P_hi)
    return Fr(1, 2) - hi_obj / 2


# Exact rational laws of (N_1, N_2) (atoms (n1, n2, numerator, denominator)) found by a
# floating-point simplex and re-solved exactly; inserted below.
COUNTERMODELS = {
    5: [(1, 2, 43, 288), (5, 1, 1, 720), (6, 0, 1, 864), (0, 0, 101, 864), (1, 0, 71, 360),
        (0, 1, 31, 180), (1, 1, 5, 432), (1, 3, 5, 504), (4, 2, 5, 288), (3, 3, 1, 216),
        (0, 4, 5, 288), (0, 2, 5, 96), (3, 0, 1, 18), (0, 3, 1, 108), (1, 10, 1, 30240),
        (2, 1, 1, 6), (2, 4, 5, 288)],
    6: [(0, 0, 10051, 83160), (3, 2, 1, 108), (2, 0, 1, 60), (1, 0, 79, 440), (3, 3, 7, 612),
        (0, 7, 1, 83160), (12, 0, 1, 1372140), (1, 5, 29, 22440), (0, 1, 511, 2970),
        (0, 4, 17, 2376), (4, 2, 7, 816), (12, 11, 1, 2221560), (1, 2, 35, 264),
        (0, 3, 19, 594), (1, 1, 9, 220), (5, 1, 3, 680), (5, 0, 1, 840), (3, 0, 4, 81),
        (2, 4, 3, 272), (2, 1, 3, 20), (6, 0, 11, 36720), (1, 3, 1, 66), (0, 2, 139, 3960),
        (1, 6, 1, 1320), (0, 6, 137, 403920)],
}


# =============================================================== E2
def section_E2():
    head("E2. Kempner's number: badly approximable and in K_2")
    K = 12
    # x lies in [x_K, x_K + 2^(1 - 2^(K+1))]: compare the continued fractions of both ends
    lo_num = sum(1 << ((1 << K) - (1 << k)) for k in range(K + 1))
    den = 1 << (1 << K)
    hi_num = lo_num * (1 << (1 << K)) + 2
    hi_den = 1 << (1 << (K + 1))
    a = cf_of_fraction(lo_num, den)
    b = cf_of_fraction(hi_num, hi_den)
    n = common_prefix(a, b)
    pq = a[:n - 1]
    check(n - 1 >= 1000, "at least 1000 certified partial quotients")
    check(max(pq[1:]) <= 6 and set(pq[1:]) <= {1, 2, 4, 6}, "partial quotients in {1,2,4,6}")
    check(pq[1] == 1 and 1 not in pq[2:], "1 occurs only as a_1")
    print("[exact] Kempner x = sum 2^(-2^k) = [%s, ...]" % ", ".join(map(str, pq[:20])))
    print("[exact] first %d partial quotients certified; all in {1,2,4,6} (a_1 = 1 only),"
          " so ||q x|| >= 1/(8q) on this range (Shallit 1979: for all q)" % (n - 1))
    # Dirichlet lower bound on the certified range: ||q_k x|| >= 1/((a_{k+1}+2) q_k)
    p0, q0, p1, q1 = 0, 1, 1, 0
    xv = Fr(lo_num, den)
    for k in range(60):
        p0, p1 = p1, pq[k] * p1 + p0
        q0, q1 = q1, pq[k] * q1 + q0
        if k >= 1:
            check(abs(q1 * xv - p1) * 8 * q1 >= 1, "||q x|| >= 1/(8q) at convergents")
    # binary orbit concentration: 1 - D_N <= ((log2 N)+1)(L)/N + 2^-L
    L = 1 << 15
    bl = ["0"] * L
    for k in range(15):
        bl[(1 << k) - 1] = "1"          # digit position 2^k (string index 2^k - 1)
    bits = "".join(bl)
    check(bits.startswith("1101000100000001"), "Kempner binary digits")
    print("[exact] Kempner binary orbit:   N   1 - D_N    N(1-D_N)/(log2 N)^2")
    for N in (1 << 8, 1 << 10, 1 << 12, 1 << 14):
        d = ext_discrepancy(bits, N)
        lg = math.log2(N)
        check(1 - d <= (lg + 2) ** 2 / N, "K_2 rate for Kempner's number")
        print("        %6d   %.6f   %.4f" % (N, 1 - d, N * (1 - d) / lg ** 2))

    # ln 2 contrast: continued fraction and runs from 8192 certified bits
    Lb = 8192
    G = 40
    s = 0
    for k in range(1, Lb + G + 1):
        s += (1 << (Lb + G - k)) // k
    lo = s >> G  # floor(2^Lb ln2) up to one unit
    ca = cf_of_fraction(lo, 1 << Lb)
    cb = cf_of_fraction(lo + 2, 1 << Lb)
    m = common_prefix(ca, cb) - 1
    check(ca[:6] == [0, 1, 2, 3, 1, 6], "ln 2 = [0;1,2,3,1,6,...]")
    big = max(ca[1:m])
    print("[finite] ln 2: %d certified partial quotients, max %d (Kempner: max 6)" % (m, big))
    lnbits = bin(lo)[2:].zfill(Lb)
    runs, cur, start = [], 1, 0
    for i in range(1, Lb - 50):
        if lnbits[i] == lnbits[i - 1]:
            cur += 1
        else:
            runs.append((cur, start))
            cur, start = 1, i
    worst = max(r / (st + 1) for r, st in runs if st >= 16)
    longest = max(r for r, _ in runs)
    check(worst < 2.57455391, "every run obeys L <= (mu-1) n with mu(ln2) <= 3.5746")
    print("[finite] ln 2 first %d bits: longest run %d, max run/position (n>=16) %.3f"
          " vs the irrationality-measure cap mu-1 = 2.5746" % (Lb - 50, longest, worst))


# =============================================================== E3
def section_E3():
    head("E3.1 Cahen's constant C = sum (-1)^k/(s_k - 1), Sylvester s_k")
    s = [2]
    for _ in range(18):
        s.append(s[-1] ** 2 - s[-1] + 1)
    prod = 1
    for k in range(1, 19):
        prod *= s[k - 1]
        check(s[k] - 1 == prod, "s_k - 1 = prod_{j<k} s_j")
    for j in range(12):
        for i in range(j):
            check(math.gcd(s[i], s[j]) == 1, "Sylvester numbers pairwise coprime")
    print("[exact] s_k - 1 = s_0 s_1 ... s_{k-1} (k <= 18); s_j pairwise coprime (j < 12)")
    print("[exact]  K  log2 D_K  log2(s_K-1)  log D_K/log s_K   error*D_K^3   tracking/log_2 D_K")
    Dk = {}
    for K in range(1, 13):
        CK = sum(Fr((-1) ** k, s[k] - 1) for k in range(K + 1))
        pred = 1
        for j in range(K):
            if (K - j) % 2 == 1:
                pred *= s[j]
        check(CK.denominator == pred, "reduced denominator = prod_{j<K, K-j odd} s_j")
        Dk[K] = pred
        if K >= 2:
            check(Dk[K] * Dk[K - 1] == s[K] - 1, "D_K D_{K-1} = s_K - 1")
            err = abs(sum(Fr((-1) ** k, s[k] - 1) for k in range(K + 1, K + 4)))
            # |C - C_K| = 1/(s_{K+1}-1) (1 + O(1/s_{K+1}))
            check(abs(err * (s[K + 1] - 1) - 1) < Fr(2, s[K + 1]), "error ~ 1/(s_{K+1}-1)")
            rK = Fr(Dk[K] ** 3, s[K + 1] - 1)
            if K >= 3:
                rK1 = Fr(Dk[K - 1] ** 3, s[K] - 1)
                check(rK * rK1 == 1 - Fr(1, s[K]), "r_K r_{K-1} = 1 - 1/s_K (parity oscillation)")
            if K >= 3:
                ed3 = float(err * Fr(pred) ** 3)
                track = math.log2(s[K + 1] - 1)
                print("        %2d %9d %11d %15.6f %14.6f %12.4f" % (
                    K, pred.bit_length(), (s[K] - 1).bit_length(),
                    math.log(pred) / math.log(s[K]), ed3, track / math.log2(pred)))
                if K >= 7:
                    check(abs(ed3 - (1.520221 if K % 2 else 0.657799)) < 1e-5,
                          "error*D_K^3 -> L (odd K), 1/L (even K)")
    # orders of 2 and 10 modulo the first Sylvester numbers (factorizations hard-coded,
    # verified by multiplication and primality tests)
    fac = {1: [3], 2: [7], 3: [43], 4: [13, 139], 5: [3263443],
           6: [547, 607, 1033, 31051], 7: [29881, 67003, 9119521, 6212157481]}

    def is_prime(n):
        if n < 2:
            return False
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
            if n % p == 0:
                return n == p
        d, r = n - 1, 0
        while d % 2 == 0:
            d //= 2
            r += 1
        for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
            x = pow(a, d, n)
            if x in (1, n - 1):
                continue
            for _ in range(r - 1):
                x = x * x % n
                if x == n - 1:
                    break
            else:
                return False
        return True

    def factor_small(n):
        out, p = {}, 2
        while p * p <= n:
            while n % p == 0:
                out[p] = out.get(p, 0) + 1
                n //= p
            p += 1
        if n > 1:
            out[n] = out.get(n, 0) + 1
        return out

    def order_mod_prime(bse, p):
        o = p - 1
        for q in factor_small(p - 1):
            while o % q == 0 and pow(bse, o // q, p) == 1:
                o //= q
        return o

    print("[exact]  j   s_j                         ord_{s_j}(2)            ord_{s_j}(10)   2 log_2 s_{j+1}")
    for j, ps in fac.items():
        pr = 1
        for p in ps:
            check(is_prime(p), "prime factor")
            pr *= p
        check(pr == s[j], "factorization of s_%d" % j)
        o2 = o10 = 1
        for p in ps:
            a2 = order_mod_prime(2, p)
            o2 = o2 * a2 // math.gcd(o2, a2)
            if p not in (2, 5):
                a10 = order_mod_prime(10, p)
                o10 = o10 * a10 // math.gcd(o10, a10)
        check(pow(2, o2, s[j]) == 1 and pow(10, o10, s[j]) == 1, "orders")
        # s_j first enters the reduced denominator D_{j+1}; C_{j+1} tracks 2 log_2 s_{j+1} bits
        print("        %d   %-27d %-23d %-15d %.1f" % (j, s[j], o2, o10, 2 * math.log2(s[j + 1])))
    # value and finite digits
    Lb = 16384
    X = sum(((-1) ** k) * ((1 << (Lb + 64)) // (s[k] - 1)) for k in range(18))
    Cd = Decimal(0)
    for k in range(10):
        Cd += Decimal((-1) ** k) / Decimal(s[k] - 1)
    check(str(Cd).startswith("0.64341054628833802618225430775756476"), "Cahen value")
    bits = bin(X >> 64)[2:].zfill(Lb)
    print("[exact] C = %s..." % str(Cd)[:42])
    print("[finite] C, first %d bits: frequency of 1 = %.5f, D_N(N=10^4) = %.4f"
          % (Lb, bits.count("1") / Lb, ext_discrepancy(bits, 10000)))

    head("E3.2 Reciprocal Fibonacci constant psi = sum 1/F_n")
    F = [0, 1]
    while F[-1] < 10 ** 95:
        F.append(F[-1] + F[-2])
    psi = sum(Decimal(1) / F[n] for n in range(1, len(F)))
    check(str(psi).startswith("3.35988566624317755317201130291892717968890513"), "psi value")
    r5 = Decimal(5).sqrt()
    phi = (1 + r5) / 2
    q = (3 - r5) / 2
    check(dclose(q, 1 / phi ** 2), "q = phi^-2")
    th = Decimal(0)
    n = 0
    while True:
        t = q ** (n * (n + 1))
        if t < Decimal(10) ** -88:
            break
        th += t
        n += 1
    theta2_sq = 4 * (1 / phi) * th * th        # theta_2(q)^2 = 4 q^(1/2) (sum q^(n(n+1)))^2
    lam = Decimal(0)
    m = 1
    while True:
        t = q ** m / (1 - q ** m)
        if t < Decimal(10) ** -88:
            break
        lam += t
        m += 2
    odd_sum = sum(Decimal(1) / F[n] for n in range(1, len(F), 2))
    even_sum = sum(Decimal(1) / F[n] for n in range(2, len(F), 2))
    check(dclose(odd_sum, r5 / 4 * theta2_sq), "sum 1/F_{2n-1} = (sqrt5/4) theta_2(q)^2")
    check(dclose(even_sum, r5 * lam), "sum 1/F_{2n} = sqrt5 (L(q) - L(q^2))")
    check(dclose(psi, r5 * (theta2_sq / 4 + lam)), "Landau decomposition of psi")
    # coefficient form in the radix phi: psi/sqrt5 = sum c(N) phi^-N
    Nmax = 420
    c = [0] * (Nmax + 1)
    for mm in range(1, Nmax + 1, 2):
        for nn in range(1, Nmax // mm + 1):
            c[mm * nn] += (-1) ** (nn * (mm - 1) // 2)
    for Nn in range(1, Nmax + 1):
        if Nn % 2:
            r2q = sum(1 if d % 4 == 1 else -1 for d in range(1, Nn + 1, 2) if Nn % d == 0)
            check(c[Nn] == r2q, "c(N) = r_2(N)/4 for odd N")
        else:
            check(c[Nn] == sum(1 for d in range(1, Nn + 1, 2) if Nn % d == 0),
                  "c(N) = tau_odd(N) for even N")
    xs = 1 / phi
    series = sum(c[Nn] * xs ** Nn for Nn in range(1, Nmax + 1))
    check(dclose(series * r5, psi, Decimal(10) ** -60), "psi = sqrt5 sum c(N) phi^-N")
    print("[exact] psi = %s... = sqrt5 [theta_2(q)^2/4 + sum_{m odd} q^m/(1-q^m)], q = phi^-2"
          % str(psi)[:30])
    print("[exact] psi/sqrt5 = sum_N c(N) phi^-N with c(N) = r_2(N)/4 (N odd), tau_odd(N) (N even)")
    # finite digits and the sparse cousin sum 2^(-F_n)
    Lb = 8192
    FF = [1, 2]
    while FF[-1] < 4 * Lb:
        FF.append(FF[-1] + FF[-2])
    sp = bin(sum(1 << (4 * Lb - f) for f in FF if f <= 4 * Lb) + (1 << (4 * Lb)))[3:]
    print("[exact] sparse cousin y = sum_{n>=2} 2^(-F_n):  N   1 - D_N   N(1-D_N)/(log2 N)^2")
    for N in (1 << 10, 1 << 12, 1 << 14):
        d = ext_discrepancy(sp, N)
        check(1 - d <= (math.log2(N) + 2) ** 2 / N, "sparse Fibonacci cousin in K_2")
        print("        %6d   %.6f   %.4f" % (N, 1 - d, N * (1 - d) / math.log2(N) ** 2))
    Fl = [0, 1]
    while Fl[-1].bit_length() < Lb + 80:
        Fl.append(Fl[-1] + Fl[-2])
    Xp = sum((1 << (Lb + 64)) // Fl[n] for n in range(1, len(Fl)))
    bits = bin((Xp >> 64) - (3 << Lb))[2:].zfill(Lb)
    print("[finite] psi, first %d bits: frequency of 1 = %.5f, D_N(N=4000) = %.4f"
          % (Lb, bits.count("1") / Lb, ext_discrepancy(bits, 4000)))

    head("E3.3 Catalan values C(1/b) = sum C_n b^-n and the exponential-mass wall")
    for b in (5, 6, 8, 10):
        sv, cn, n = Decimal(0), 1, 0
        while True:
            t = Decimal(cn) / Decimal(b) ** n
            if t < Decimal(10) ** -88 and n > 10:
                break
            sv += t
            cn = cn * 2 * (2 * n + 1) // (n + 2)
            n += 1
        closed = (b - Decimal(b * b - 4 * b).sqrt()) / 2
        check(dclose(sv, closed), "C(1/b) = (b - sqrt(b^2-4b))/2")
        cb, n, sb = 1, 0, Decimal(0)
        while True:
            t = Decimal(cb) / Decimal(b) ** n
            if t < Decimal(10) ** -88 and n > 10:
                break
            sb += t
            cb = cb * (2 * n + 1) * 2 // (n + 1)
            n += 1
        check(dclose(sb, (Decimal(b) / (b - 4)).sqrt()), "sum binom(2n,n) b^-n = sqrt(b/(b-4))")
        print("[exact] b=%2d  C(1/b) = %s = (b - sqrt(%d))/2;  sum binom(2n,n) b^-n = sqrt(%s)"
              % (b, str(sv)[:24], b * b - 4 * b, str(Fr(b, b - 4))))
    check(dclose(sum(Decimal(comb(2 * n, n)) / Decimal(8) ** n for n in range(400)),
                 Decimal(2).sqrt(), Decimal(10) ** -60), "sqrt 2 = sum binom(2n,n)/8^n")
    # carry window: the integer tail at shift n is ~ C_n * 4/(b-4), i.e. n log_b 4 digits
    print("[exact] base 8 tails T_n = sum_j C_{n+j} 8^-j:  n   log_8 T_n / n  (-> log_8 4 = 2/3)")
    cat = [1]
    for n in range(1, 1400):
        cat.append(cat[-1] * 2 * (2 * n - 1) // (n + 1))
    for n in (100, 400, 1000):
        Tn = sum(Fr(cat[n + j], 8 ** j) for j in range(1, 300))
        ratio = (math.log2(Tn.numerator) - math.log2(Tn.denominator)) / (3 * n)
        check(abs(ratio - 2 / 3) < 0.05, "exponential tails")
        print("        %5d   %.4f" % (n, ratio))

    head("E3.4 Apery's zeta(3)")
    ap, bc = Decimal(0), 1
    for n in range(1, 160):
        bc = bc * 2 * (2 * n - 1) // n
        ap += Decimal((-1) ** (n - 1)) / (Decimal(n) ** 3 * bc)
    z3 = Decimal(5) / 2 * ap
    li3 = sum(Decimal(1) / (Decimal(2) ** k * Decimal(k) ** 3) for k in range(1, 320))
    z3b = Decimal(8) / 7 * (li3 + PI ** 2 * LN2 / 12 - LN2 ** 3 / 6)
    check(dclose(z3, z3b), "Apery series = (8/7)(Li_3(1/2) + pi^2 ln2/12 - ln^3 2/6)")
    check(str(z3).startswith("1.2020569031595942853997381615114499907649862923404988817922"),
          "zeta(3) value")
    print("[exact] zeta(3) = %s... (Apery series = Li_3(1/2) ladder, 50 digits)" % str(z3)[:34])
    A, bc = Fr(0), 1
    print("[exact]   n   log2 den / n   (cap 4/ln2 = %.4f from lcm(1..n)^2 lcm(1..2n))"
          "   top band (n/2, n]: v_p(den) = 3" % (4 / math.log(2)))
    plist = primes_upto(800)
    l1 = l2 = 1
    for n in range(1, 401):
        bc = bc * 2 * (2 * n - 1) // n
        A += Fr((-1) ** (n - 1), n ** 3 * bc)
        l1 = l1 * n // math.gcd(l1, n)
        for m in (2 * n - 1, 2 * n):
            l2 = l2 * m // math.gcd(l2, m)
        den = A.denominator
        check((l1 * l1 * l2) % den == 0, "den A_n divides lcm(1..n)^2 lcm(1..2n)")
        if n >= 3:
            ok = True
            for p in plist:
                if p > n:
                    break
                if n / 2 < p and p >= 3:
                    vp = 0
                    dd = den
                    while dd % p == 0:
                        dd //= p
                        vp += 1
                    ok = ok and vp == 3
            check(ok, "every top-band prime divides the denominator exactly to the 3rd power")
        if n in (60, 120, 200, 400):
            print("        %4d   %.4f          %s" % (n, math.log2(den) / n, ok))
    check(5.2 < math.log2(A.denominator) / 400 < 6.4, "denominator rate")

    head("E3.5 C_1 = [0;1,2,3,...] = I_1(2)/I_0(2)")
    I0 = sum(Fr(1, factorial(k) ** 2) for k in range(120))
    I1 = sum(Fr(1, factorial(k) * factorial(k + 1)) for k in range(120))
    x = I1 / I0
    p0, q0, p1, q1 = 1, 0, 0, 1   # p_{-1}/q_{-1}, p_0/q_0 for a_0 = 0
    for n in range(1, 61):
        p0, p1 = p1, n * p1 + p0
        q0, q1 = q1, n * q1 + q0
        if n == 40:
            check(abs(Decimal(p1) / Decimal(q1) - Decimal(x.numerator) / Decimal(x.denominator))
                  < TOL50, "Bessel ratio = [0;1,2,3,...] to 50 digits")
        if n in (10, 20, 40, 60):
            err = abs(x - Fr(p1, q1))
            qn1 = (n + 1) * q1 + q0
            # |x - p_n/q_n| ~ 1/(q_n q_{n+1}),  q_{n+1} ~ (n+1) q_n
            check(abs(float(err * q1 * qn1) - 1) < 2.0 / n, "error ~ 1/(q_n q_{n+1})")
            print("[exact] n=%2d  q_{n+1}/((n+1)q_n) = %.6f   |x-p_n/q_n| q_n q_{n+1} = %.6f"
                  "   exponent excess log(q_{n+1}/q_n)/log q_n = %.4f"
                  % (n, qn1 / ((n + 1) * q1), float(err * q1 * qn1),
                     (math.log(qn1) - math.log(q1)) / math.log(q1)))
    xd = Decimal(x.numerator) / Decimal(x.denominator)
    check(str(xd).startswith("0.697774657964007982006790592551752599486658262998021232368630"),
          "C_1 value")
    Lb = 16384
    I0i = sum((1 << (Lb + 64)) // (factorial(k) ** 2) for k in range(1100))
    I1i = sum((1 << (Lb + 64)) // (factorial(k) * factorial(k + 1)) for k in range(1100))
    bits = bin((I1i << Lb) // I0i)[2:].zfill(Lb)
    dec = str((I1i * 10 ** 4000) // I0i).zfill(4000)[:4000]
    print("[exact] C_1 = %s..." % str(xd)[:42])
    print("[finite] C_1, first %d bits: frequency of 1 = %.5f, D_N(N=10^4) = %.4f;"
          " first 4000 decimals: digit counts %s"
          % (Lb, bits.count("1") / Lb, ext_discrepancy(bits, 10000),
             [dec.count(str(d)) for d in range(10)]))


def main():
    nu, JE, JP, mu_pos, mu_neg = section_E1()
    if "--thresholds" in sys.argv:
        section_thresholds(JE, JP, mu_pos, mu_neg)
    section_E1a(nu)
    section_E2()
    section_E3()
    print("\nAll %d checks passed in %.1fs." % (CHECKS[0], time.time() - T0))


if __name__ == "__main__":
    main()
