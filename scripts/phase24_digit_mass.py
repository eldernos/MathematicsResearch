#!/usr/bin/env python3
"""Phase 24 Track A: dense digit-mass transfer, generalized Erdos-Borwein constants,
arithmetic Lambert families and signed transition complexity.

Companion to notes/phase24/dense-digit-mass-and-lambert.md.

Sections
  1. Exhaustive checks of the elementary digit inequalities (Kummer, s_b, w_b,
     signed binary weight w_pm, transition increments).
  2. Exact local Euler-factor identities and the squarefull convolution.
  3. Exact prefix decompositions and carry tails on certified prefixes.
  4. Certified constants: outward-rounded integer arithmetic (scale 2^-SB) and
     fractions.Fraction.  These are THEOREM INPUTS (label: Finite certificate).
  5. Threshold certificates derived with Fraction arithmetic from Section 4.
  6. FINITE MEASUREMENTS ONLY.  Prefix statistics of the constants.  They are
     reported for orientation and are never used to prove asymptotic statements.

Exit code 0 iff every assertion holds.  Run:  python -B scripts/phase24_digit_mass.py
"""

import sys
import time
from fractions import Fraction
from math import comb, isqrt

sys.set_int_max_str_digits(0)

CHECKS = 0
T0 = time.time()


def check(cond, msg="check failed"):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise AssertionError(msg)


def section(title):
    print()
    print(f"[t = {time.time() - T0:.0f} s]")
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Basic digit functions
# ---------------------------------------------------------------------------

def sb(n, b):
    """Base-b digit sum of n >= 0."""
    if b == 2:
        return bin(n).count("1")
    t = 0
    while n:
        n, r = divmod(n, b)
        t += r
    return t


def wb(n, b):
    """Number of nonzero base-b digits of n >= 0."""
    if b == 2:
        return bin(n).count("1")
    t = 0
    while n:
        n, r = divmod(n, b)
        t += r != 0
    return t


def odd_part(n):
    return n // (n & -n) if n else 0


def b_free(n, b):
    while n % b == 0:
        n //= b
    return n


def wpm(c):
    """Minimal number of terms in c = sum eps_i 2^{m_i}, eps_i = +-1 (NAF weight)."""
    c = abs(c)
    w = 0
    while c:
        if c & 1:
            w += 1
            c = c + 1 if (c & 3) == 3 else c - 1
        c >>= 1
    return w


_WREC = {0: 0, 1: 1}


def wpm_rec(c):
    """Defining recursion: w(0)=0, w(2c)=w(c), w(c)=1+min(w((c-1)/2), w((c+1)/2)) for odd c."""
    c = abs(c)
    if c in _WREC:
        return _WREC[c]
    if c % 2 == 0:
        v = wpm_rec(c // 2)
    else:
        v = 1 + min(wpm_rec((c - 1) // 2), wpm_rec((c + 1) // 2))
    _WREC[c] = v
    return v


def trans(A):
    """T(A): number of i >= 0 with bit_i(A) != bit_{i+1}(A), two's complement."""
    if A < 0:
        A = ~A  # complementing every bit preserves transitions
    return bin(A ^ (A >> 1)).count("1")


def carries_two(a, c, b):
    """Number of carries when adding a and c in base b."""
    k = 0
    carry = 0
    while a or c or carry:
        a, x = divmod(a, b)
        c, y = divmod(c, b)
        carry = 1 if x + y + carry >= b else 0
        k += carry
    return k


def column_carry_total(ops, b):
    """Total column carry sum_j c_j of the column addition of the list ops (>= 0)."""
    ops = list(ops)
    total = 0
    carry = 0
    while any(ops) or carry:
        col = carry
        nxt = []
        for a in ops:
            a, r = divmod(a, b)
            col += r
            nxt.append(a)
        ops = nxt
        carry = col // b
        total += carry
    return total


# ---------------------------------------------------------------------------
# Arithmetic sieves
# ---------------------------------------------------------------------------

def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if s[i]]


def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, isqrt(n) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def exponents(n, spf):
    out = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out.append((p, e))
    return out


def arithmetic_tables(n):
    """tau, omega, tau_odd, tau_3 for 0..n (index 0 unused)."""
    spf = spf_sieve(n)
    tau = [0] * (n + 1)
    omg = [0] * (n + 1)
    tod = [0] * (n + 1)
    t3 = [0] * (n + 1)
    for m in range(1, n + 1):
        t = 1
        o = 1
        w = 0
        u = 1
        for p, e in exponents(m, spf):
            t *= e + 1
            w += 1
            u *= comb(e + 2, 2)
            if p != 2:
                o *= e + 1
        tau[m], omg[m], tod[m], t3[m] = t, w, o, u
    return tau, omg, tod, t3, spf


def a_plus(n, tod):
    """Plus Erdos-Borwein coefficient a_+(n) = (1 - v_2(n)) tau_odd(n)."""
    e = (n & -n).bit_length() - 1
    return (1 - e) * tod[n]


# ===========================================================================
# Section 1. Elementary digit inequalities
# ===========================================================================

def section1():
    section("1. Elementary digit inequalities (exhaustive finite checks)")
    # 1a. Kummer identity, subadditivity of s_b and w_b, submultiplicativity.
    lim = {2: 512, 3: 400, 4: 300, 5: 260, 6: 220, 7: 200, 8: 200, 9: 180, 10: 180}
    pairs = 0
    for b, L in lim.items():
        S = [sb(a, b) for a in range(2 * L + 1)]
        W = [wb(a, b) for a in range(2 * L + 1)]
        for a in range(L):
            for c in range(L):
                k = carries_two(a, c, b)
                check(S[a + c] == S[a] + S[c] - (b - 1) * k, f"Kummer b={b} {a}+{c}")
                check(W[a + c] <= W[a] + W[c], f"w_b subadditive b={b} {a}+{c}")
                pairs += 1
        for a in range(1, 120):
            for c in range(1, 120):
                m = a * c
                check(sb(m, b) <= S[a] * S[c], "s_b submultiplicative")
                wm = wb(m, b)
                check(wm <= S[a] * W[c] and wm <= 2 * W[a] * W[c], "w_b product bound")
    print(f"  Kummer identity, s_b and w_b subadditivity: {pairs} pairs, bases 2..10")
    # Failure of w_b(ac) <= w_b(a) w_b(c) for every b >= 3, and sharpness of 2.
    for b in range(3, 17):
        check(wb((b - 1) ** 2, b) == 2 and wb(b - 1, b) == 1, "w_b((b-1)^2)=2")
    check(wb(4, 3) == 2 and wb(2, 3) == 1, "w_3(tau(pq)) = w_3(4) = 2 > w_3(2)^2")
    check(wb(16, 10) == 2 and wb(2, 10) == 1, "w_10(tau(pqrs)) = 2 > 1")
    print("  w_b(ac) <= w_b(a)w_b(c) FAILS for b >= 3: w_b((b-1)^2) = 2 (b=3..16);"
          " w_3(tau(pq)) = w_3(4) = 2")
    # 1b. Multi-operand Kummer identity (deterministic pseudo-random lists).
    seed = 12345
    trials = 0
    for b in range(2, 11):
        for t in range(300):
            ops = []
            for i in range(1 + t % 7):
                seed = (seed * 6364136223846793005 + 1442695040888963407) % (1 << 64)
                ops.append(seed % (b ** (1 + (seed >> 40) % 9)))
            lhs = sum(sb(a, b) for a in ops) - sb(sum(ops), b)
            check(lhs == (b - 1) * column_carry_total(ops, b), "multi-operand Kummer")
            trials += 1
    print(f"  multi-operand Kummer identity: {trials} operand lists, bases 2..10")
    # 1c. Signed binary weight: NAF algorithm equals the defining recursion.
    for c in range(-4096, 4097):
        check(wpm(c) == wpm_rec(c), "NAF weight = minimal signed weight")
        check(wpm(c) <= sb(abs(c), 2), "w_pm <= s_2")
    for c in range(-300, 301):
        for d in range(-300, 301, 7):
            check(wpm(c + d) <= wpm(c) + wpm(d), "w_pm subadditive")
            check(wpm(c * d) <= wpm(c) * wpm(d), "w_pm submultiplicative")
    print("  w_pm: NAF = defining recursion for |c| <= 4096; sub-additive and -multiplicative")
    # 1d. Transition increments |T(A +- 2^m) - T(A)| <= 2 and T(A+c) <= T(A) + 2 w_pm(c).
    cnt = 0
    worst = 0
    for A in range(-(1 << 12), 1 << 12):
        tA = trans(A)
        for m in range(0, 14):
            for s in (1, -1):
                d = trans(A + s * (1 << m)) - tA
                check(-2 <= d <= 2, f"transition increment A={A} m={m}")
                worst = max(worst, d)
                cnt += 1
    check(worst == 2, "the constant 2 is attained")
    for A in range(-600, 601):
        tA = trans(A)
        for c in range(-600, 601, 3):
            check(trans(A + c) <= tA + 2 * wpm(c), "T(A+c) <= T(A) + 2 w_pm(c)")
            cnt += 1
    print(f"  transition increments: {cnt} cases; max increment from +-2^m is 2 (attained)")


# ===========================================================================
# Section 2. Local identities and the squarefull convolution
# ===========================================================================

def section2(tau, spf, nmax):
    section("2. Local Euler-factor identities and squarefull convolution")
    # 2a. Power series identity (1-x) sum_e s_2(e+1) x^e = sum_j x^{2^j-1}/(1+x^{2^j}).
    D = 2048
    lhs = [0] * D
    prev = 0
    for e in range(D):
        cur = sb(e + 1, 2)
        lhs[e] = cur - prev
        prev = cur
    rhs = [0] * D
    j = 0
    while (1 << j) - 1 < D:
        step = 1 << j
        i = 0
        while (1 << j) - 1 + i * step < D:
            rhs[(1 << j) - 1 + i * step] += (-1) ** i
            i += 1
        j += 1
    check(lhs == rhs, "power-series identity for s_2(e+1)")
    print(f"  (1-x) sum s_2(e+1)x^e = sum_j x^(2^j-1)/(1+x^(2^j)) through x^{D-1}: exact")
    # 2b. Numerical local identity at p = 2, 3, 5, 7 with rigorous truncation bounds.
    for p in (2, 3, 5, 7, 11):
        x = Fraction(1, p)
        E = 60
        part = (1 - x) * sum(sb(e + 1, 2) * x ** e for e in range(E + 1))
        tail = x ** (E + 1) * (E + 2 + x / (1 - x))   # uses s_2(e+1) <= e+1
        rhs_lo = sum(Fraction(p, p ** (2 ** jj) + 1) for jj in range(7))
        rhs_hi = rhs_lo + 2 * Fraction(p, p ** (2 ** 7))
        check(part <= rhs_hi and rhs_lo <= part + tail, f"local identity p={p}")
    print("  (1-1/p) sum_e s_2(e+1)/p^e = sum_j p/(p^(2^j)+1): checked p = 2,3,5,7,11")
    # 2c. Squarefull support of h = g * mu for g(n) = prod s_2(e+1); s_2(tau) <= g.
    lim = min(nmax, 200000)
    g = [0] * (lim + 1)
    for n in range(1, lim + 1):
        v = 1
        for p, e in exponents(n, spf):
            v *= sb(e + 1, 2)
        g[n] = v
    h = g[:]
    for d in range(1, lim + 1):
        hd = h[d]
        if hd:
            for m in range(2 * d, lim + 1, d):
                h[m] -= hd
    nz = 0
    for n in range(1, lim + 1):
        if h[n]:
            nz += 1
            ex = exponents(n, spf)
            check(all(e >= 2 for _, e in ex), "h supported on squarefull integers")
            check(h[n] == eval_h_product(ex), "h multiplicative with h(p^e)=s2(e+1)-s2(e)")
    for n in range(1, lim + 1):
        check(sb(tau[n], 2) <= g[n], "s_2(tau(n)) <= prod s_2(e+1)")
        check(sb(tau[n], 2) == sb(odd_part(tau[n]), 2), "s_2(tau) = s_2(odd(tau))")
    print(f"  h = g*mu: {nz} nonzero values up to {lim}, all on squarefull n, h(p) = 0;"
          f" s_2(tau(n)) <= g(n) for n <= {lim}")


def eval_h_product(ex):
    v = 1
    for _, e in ex:
        v *= sb(e + 1, 2) - sb(e, 2)
    return v


# ===========================================================================
# Section 3. Exact prefix decompositions
# ===========================================================================

def coeff_bound_tail(Mp, growth):
    """Upper bound, in units of b^{-(N+G)}, for |sum_{n>Mp} c(n) b^{N+G-kn}|."""
    if growth == "sqrt":      # |c(n)| <= tau(n) <= 2 sqrt(n)
        return 4 * (isqrt(Mp + 1) + 1) + 1
    if growth == "linear":    # |c(n)| <= tau(n)^2 <= 4n
        return 8 * (Mp + 1) + 1
    raise ValueError(growth)


def dc_sum(c, lo, hi, B, powcache):
    """sum_{n=lo}^{hi-1} c[n] B^{hi-1-n}."""
    if hi - lo <= 64:
        s = 0
        for n in range(lo, hi):
            s = s * B + c[n]
        return s
    mid = (lo + hi) // 2
    L = hi - mid
    if L not in powcache:
        powcache[L] = B ** L
    return dc_sum(c, lo, mid, B, powcache) * powcache[L] + dc_sum(c, mid, hi, B, powcache)


def prefix_int(c, b, k, N, growth="sqrt", G=64, signed=False):
    """Exact floor(b^N x) for x = sum_{n>=1} c[n] b^{-kn}; certified by guard digits."""
    Mp = (N + G) // k
    assert len(c) > Mp + 1
    B = b ** k
    S = dc_sum(c, 1, Mp + 1, B, {}) * b ** (N + G - k * Mp)
    tb = coeff_bound_tail(Mp, growth)
    bG = b ** G
    lo = (S - (tb if signed else 0)) // bG
    hi = (S + tb) // bG
    check(lo == hi, "prefix certification by guard digits")
    return lo


def to_digits(P, b, N):
    """Last N base-b digits of P >= 0 (most significant first): the digits d_1..d_N."""
    if b == 2:
        s = bin(P & ((1 << N) - 1))[2:].zfill(N)
        return [int(ch) for ch in s]
    if b == 10:
        s = str(P % 10 ** N).zfill(N)
        return [int(ch) for ch in s]
    out = []

    def rec(n, width):
        if width <= 400:
            loc = []
            for _ in range(width):
                n, r = divmod(n, b)
                loc.append(r)
            out.extend(reversed(loc))
            return
        half = width // 2
        q, r = divmod(n, b ** half)
        rec(q, width - half)
        rec(r, half)

    rec(P % b ** N, N)
    return out


def section3(tau, omg, tod):
    section("3. Exact prefix decompositions and carry tails")
    Nmax = 3000
    families = {
        "E(2)": (2, 1, tau, False), "E(4)": (2, 2, tau, False),
        "E(8)": (2, 3, tau, False), "E*(4)": (2, 2, [0] + [1 << omg[n] for n in range(1, len(omg))], False),
    }
    worst_tail = {}
    plus_one_failures = {}
    for name, (b, k, c, signed) in families.items():
        P = prefix_int(c, b, k, Nmax)
        A = 0
        mass = 0
        worst = 0
        fail = None
        for N in range(1, Nmax + 1):
            A *= 2
            if N % k == 0:
                A += c[N // k]
                mass += sb(c[N // k], 2)
            PN = P >> (Nmax - N)
            t = PN - A                      # floor(tau_N) >= 0
            check(t >= 0, "floor tau_N >= 0 for nonnegative series")
            stail = sb(t, 2)
            worst = max(worst, stail)
            intpart = PN >> N
            dsum = sb(PN & ((1 << N) - 1), 2)   # digit sum of the fractional prefix d_1..d_N
            check(dsum + sb(intpart, 2) == sb(PN, 2), "digit sum of prefix splits at the radix point")
            check(sb(PN, 2) <= mass + stail, "Theorem 2.2(i)")
            if fail is None and sb(PN, 2) >= mass + 2:
                fail = (N, sb(PN, 2) - mass, t)
            if N <= 400 and N % 37 == 0:
                ops = [c[n] << (N - k * n) for n in range(1, N // k + 1)] + [t]
                kap = column_carry_total(ops, 2)
                check(sb(PN, 2) == mass + stail - kap, "exact Kummer prefix identity")
        worst_tail[name] = worst
        plus_one_failures[name] = fail
        print(f"  {name}: N <= {Nmax}: s_2(P_N) <= sum_(n<=N/k) s_2(a(n)) + s_2(floor tau_N);"
              f" max s_2(floor tau_N) = {worst}; first N with excess >= 2: {fail}")
    # Signed: transitions of E_+(2^k) prefixes.
    for k in (1, 2, 3, 4):
        c = [0] + [a_plus(n, tod) for n in range(1, len(tod))]
        P = prefix_int(c, 2, k, Nmax, signed=True)
        A = 0
        wmass = 0
        for N in range(1, Nmax + 1):
            A *= 2
            if N % k == 0:
                A += c[N // k]
                wmass += wpm(c[N // k])
            PN = P >> (Nmax - N)
            t = PN - A
            check(trans(PN) <= trans(A) + 2 * wpm(t), "signed carry tail")
            check(trans(A) <= 2 * wmass, "T(A_N) <= 2 sum w_pm(a(n))")
        print(f"  E_+(2^{k}): N <= {Nmax}: T(P_N) <= 2 sum w_pm(a_+(n)) + 2 w_pm(floor tau_N)")
    return worst_tail, plus_one_failures


# ===========================================================================
# Section 4. Certified constants (outward-rounded)
# ===========================================================================

SB = 192
ONE = 1 << SB


def cdiv(a, b):
    return -((-a) // b)


def fx_to_frac(v):
    return Fraction(v, ONE)


def frac_up(fr):
    return cdiv(fr.numerator * ONE, fr.denominator)


def frac_dn(fr):
    return (fr.numerator * ONE) // fr.denominator


def tail_bound(p, E, cd):
    """Upper bound for (1-1/p) sum_{e>E} g(e) p^{-e} when 0 <= g(e) <= c (e+1)^d.

    For e >= E+1 and E >= 3d: ((e+1)/(E+2))^d <= exp(d(e-E-1)/(E+2)) <= (3/2)^(e-E-1),
    so the tail is at most c (E+2)^d (1-x) x^(E+1) / (1 - 3x/2), x = 1/p <= 1/2.
    """
    c, d = cd
    assert E >= 3 * d
    x = Fraction(1, p)
    return c * (E + 2) ** d * (1 - x) * x ** (E + 1) / (1 - Fraction(3, 2) * x)


def local_bounds(g, p, E, cd):
    """Rational bounds for l(p) = (1-1/p) sum_{e>=0} g(e) p^{-e}, 0 <= g(e) <= c (e+1)^d."""
    num = 0
    for e in range(E + 1):
        num = num * p + g(e)
    den = p ** (E + 1)
    lo = Fraction((p - 1) * num, den)
    return lo, lo + tail_bound(p, E, cd)


def exp_for(p):
    bits = p.bit_length()
    return max(7, 96 // max(1, bits - 1) + 2)


def tail_A(g, Y, cd, sign):
    """A with sign*(l(p)-1) <= A/p^2 for all p > Y (needs g(0)=g(1)=1).

    l(p) - 1 = sum_{e>=2} (g(e)-g(e-1)) p^{-e} and |g(e)-g(e-1)| <= c (e+1)^d.
    """
    c, d = cd
    E = 12
    A = Fraction(0)
    for e in range(2, E + 1):
        dd = g(e) - g(e - 1)
        if sign * dd > 0:
            A += Fraction(abs(dd), Y ** (e - 2))
    # sum_{e>E} c (e+1)^d Y^{2-e} <= c (E+2)^d Y^{1-E} / (1 - 3/(2Y)) as in tail_bound
    A += Fraction(c * (E + 2) ** d, Y ** (E - 1)) / (1 - Fraction(3, 2 * Y))
    return A


_BIG = {}


def inv_sq_above(y):
    """Fraction upper bound for sum_{p > y} p^{-2}.

    Exact (rounded up at scale 2^-SB) over primes y < p <= Y2 = 4*10^6, plus
    sum_{n > Y2, n = +-1 mod 6} n^{-2} <= 1/(3(Y2-6)) for the rest (telescoping
    1/(6m-1)^2 <= (1/6)(1/(6m-7) - 1/(6m-1)) and its analogue for 6m+1).
    """
    Y2 = 4000000
    if "primes" not in _BIG:
        _BIG["primes"] = primes_upto(Y2)
    if y not in _BIG:
        s = sum(cdiv(ONE, q * q) for q in _BIG["primes"] if q > y)
        _BIG[y] = Fraction(s, ONE) + Fraction(1, 3 * (Y2 - 6))
    return _BIG[y]


class EulerProduct:
    """Outward-rounded bounds for prod over primes in a domain of l(p)."""

    def __init__(self, name, g, primes, Y, cd, domain=lambda p: True, keep=0):
        self.name = name
        self.g = g
        lo = ONE
        hi = ONE
        self.prefix_lo = {}
        self.prefix_hi = {}
        for p in primes:
            if p > Y:
                break
            if not domain(p):
                continue
            l_lo, l_hi = local_bounds(g, p, exp_for(p), cd)
            lo = (lo * l_lo.numerator) // l_lo.denominator
            hi = cdiv(hi * l_hi.numerator, l_hi.denominator)
            if p <= keep:
                self.prefix_lo[p] = lo
                self.prefix_hi[p] = hi
        self.head_lo, self.head_hi = lo, hi
        Ap = tail_A(g, Y, cd, +1)
        Am = tail_A(g, Y, cd, -1)
        S2 = inv_sq_above(Y)
        check(Ap * S2 < 1 and Am * S2 < 1, "tail constants: A S2 < 1")
        tail_hi = 1 / (1 - Ap * S2)         # prod (1 + A/p^2) <= exp(A S2) <= 1/(1 - A S2)
        tail_lo = 1 - Am * S2               # prod (1 - A'/p^2) >= 1 - A' S2
        self.lo = (lo * tail_lo.numerator) // tail_lo.denominator
        self.hi = cdiv(hi * tail_hi.numerator, tail_hi.denominator)
        self.Y = Y

    def bounds(self):
        return fx_to_frac(self.lo), fx_to_frac(self.hi)

    def R_after(self, p):
        """Upper bound for prod over domain primes q > p of l(q) (p in prefix table)."""
        return cdiv(self.hi * ONE, self.prefix_lo[p])


def model_dp(name, stat, u, ep, init, domain, primes, y, thr_bits=64):
    """Certified bounds for E[stat(prod_p u(e_p))] in the independent-exponent model.

    ep: EulerProduct of the majorant l(p) = E[F(u(e_p))] over the same domain.
    init: list of (value, prob_numerator_fixed) for the special 2-adic factor or None.
    Returns (lo, hi) as Fractions.
    """
    thr = ONE >> thr_bits
    states = {}
    frozen = 0                                  # scale ONE
    if init is None:
        states[1] = [ONE, ONE]
    else:
        for v, pr_lo, pr_hi in init["states"]:
            if v == 0:
                continue
            st = states.setdefault(v, [0, 0])
            st[0] += pr_lo
            st[1] += pr_hi
        frozen += init["frozen_hi"]             # already multiplied by R_all
    last = None
    for p in primes:
        if p > y:
            break
        if not domain(p):
            continue
        Rp = ep.R_after(p)
        new = {}
        cd = ep_cd[ep.name]
        for v, (plo, phi) in states.items():
            sv = stat(v)
            e = 0
            while True:
                den = p ** (e + 1)
                qhi = cdiv(phi * (p - 1), den)
                if qhi < thr and e >= 3 * cd[1] + 1:
                    # all exponents e' >= e: E[F(u(e')) 1(e' >= e)] <= tail_bound(p, e-1)
                    tfr = tail_bound(p, e - 1, cd)
                    frozen += cdiv(cdiv(phi * sv * tfr.numerator, tfr.denominator) * Rp, ONE)
                    break
                qlo = (plo * (p - 1)) // den
                vv = v * u(e)
                if qhi < thr:
                    frozen += cdiv(qhi * stat(vv) * Rp, ONE)
                else:
                    st = new.setdefault(vv, [0, 0])
                    st[0] += qlo
                    st[1] += qhi
                e += 1
        states = new
        last = p
    R_end = ep.R_after(last)
    hi = frozen
    lo = 0
    # lower bound factor: P(u(e_p) = 1 for all domain p > y) >= 1 - sum_{p>y} p^{-2}
    qfac = 1 - inv_sq_above(y)
    for v, (plo, phi) in states.items():
        sv = stat(v)
        hi += cdiv(phi * sv * R_end, ONE)
        lo += plo * sv
    lo = (lo * qfac.numerator) // qfac.denominator
    print(f"  {name}: {len(states)} live states after primes <= {y}"
          f" (t = {time.time() - T0:.0f} s)")
    return fx_to_frac(lo), fx_to_frac(hi)


ep_cd = {}


def make_ep(name, g, primes, Y, cd, domain=lambda p: True, keep=0):
    ep_cd[name] = cd
    return EulerProduct(name, g, primes, Y, cd, domain, keep)


def fmt_dn(fr, d=6):
    """Decimal rounded DOWN (safe for lower bounds)."""
    fr = Fraction(fr)
    v = (fr.numerator * 10 ** d) // fr.denominator
    sgn = "-" if v < 0 else ""
    v = abs(v)
    return f"{sgn}{v // 10 ** d}.{v % 10 ** d:0{d}d}"


def fmt_up(fr, d=6):
    """Decimal rounded UP (safe for upper bounds)."""
    fr = Fraction(fr)
    v = -((-fr.numerator * 10 ** d) // fr.denominator)
    sgn = "-" if v < 0 else ""
    v = abs(v)
    return f"{sgn}{v // 10 ** d}.{v % 10 ** d:0{d}d}"


def fmt_iv(iv, d=6):
    return f"[{fmt_dn(iv[0], d)}, {fmt_up(iv[1], d)}]"


def section4(primes):
    section("4. Certified constants (outward-rounded integer arithmetic; theorem inputs)")
    Y = 300000
    y = 20000
    res = {}
    s2e = lambda e: sb(e + 1, 2)
    all_p = lambda p: True
    odd_p = lambda p: p != 2
    # --- E: majorant C and model constant C_true
    epC = make_ep("C", s2e, primes, Y, (1, 1), all_p, keep=y)
    C_lo, C_hi = epC.bounds()
    res["C"] = (C_lo, C_hi)
    print(f"  C      = prod_p sum_j p/(p^(2^j)+1)          in {fmt_iv(res['C'], 7)}")
    check(C_hi < Fraction(29, 20), "C < 29/20")
    check(C_hi < Fraction(14036, 10000), "C < 1.4036")
    # H = sum |h(n)|/n for the squarefull convolution of g = prod s_2(e+1)
    # l_H(p) = 1 + sum_{e>=2} |h(p^e)| p^-e ; write as (1-1/p) sum G(p^e) p^-e with G cumulative
    Gcum = lambda e: 1 + sum(abs(sb(i + 1, 2) - sb(i, 2)) for i in range(2, e + 1))
    epH = make_ep("H", Gcum, primes, 20000, (1, 2), all_p)
    H_lo, H_hi = epH.bounds()
    res["H"] = (H_lo, H_hi)
    print(f"  H      = sum_n |h(n)|/n (squarefull, h(p)=0) in {fmt_iv(res['H'])}")
    check(H_hi < 2, "H < 2: absolute convergence")
    Ct = model_dp("C_true", lambda v: sb(v, 2), lambda e: odd_part(e + 1), epC, None,
                  all_p, primes, y)
    res["C_true"] = Ct
    print(f"  C_true = lim mean s_2(tau(n))                in {fmt_iv(Ct)}")
    check(Ct[1] < C_lo, "C_true < C strictly")
    # --- E_odd
    epO = make_ep("C_odd", s2e, primes, Y, (1, 1), odd_p, keep=y)
    res["C_odd"] = epO.bounds()
    Co = model_dp("C_odd_true", lambda v: sb(v, 2), lambda e: odd_part(e + 1), epO, None,
                  odd_p, primes, y)
    res["C_odd_true"] = Co
    print(f"  C_odd  (majorant)                            in {fmt_iv(res['C_odd'])}")
    print(f"  C_odd_true = lim mean s_2(tau_odd(n))        in {fmt_iv(Co)}")
    # --- E_+ : signed weight
    wpe = lambda e: wpm(e + 1)
    epW = make_ep("W_odd", wpe, primes, Y, (1, 1), odd_p, keep=y)
    Wodd = epW.bounds()
    two_adic = Fraction(0)
    E2 = 120
    for e in range(E2 + 1):
        two_adic += Fraction(wpm(abs(1 - e)), 2 ** (e + 1))
    two_tail = Fraction(E2 + 2, 2 ** (E2 + 1))          # w_pm(|1-e|) <= e
    Wmaj = (two_adic * Wodd[0], (two_adic + two_tail) * Wodd[1])
    res["W_maj"] = Wmaj
    print(f"  W_+^maj = (1/2 sum w(|1-e|)2^-e) prod_odd   in {fmt_iv(Wmaj)}")
    print(f"     2-adic factor in {fmt_iv((two_adic, two_adic + two_tail))}; odd product in {fmt_iv(Wodd)}")
    check(Wmaj[1] < 1, "W_+^maj < 1")
    init_states = []
    for e in range(E2 + 1):
        if e == 1:
            continue
        pr = ONE >> (e + 1)
        init_states.append((odd_part(abs(1 - e)), pr, pr))
    frozen_hi = cdiv(frac_up(two_tail) * epW.hi, ONE)
    Wt = model_dp("W_+", wpm, lambda e: odd_part(e + 1), epW,
                  {"states": init_states, "frozen_hi": frozen_hi}, odd_p, primes, y)
    res["W_true"] = Wt
    print(f"  W_+ = lim mean w_pm(a_+(n))                 in {fmt_iv(Wt)}")
    check(Wt[0] > Fraction(3, 4), "W_+ > 3/4 (method floor at k = 3)")
    # --- tau_r, r = 4, 8, 16
    for r in (4, 8, 16):
        gr = (lambda rr: (lambda e: sb(comb(e + rr - 1, rr - 1), 2)))(r)
        epR = make_ep(f"tau{r}", gr, primes, Y, (r, 1), all_p, keep=1000)
        maj = epR.bounds()
        tr = model_dp(f"C_tau{r}_true", lambda v: sb(v, 2),
                      (lambda rr: (lambda e: odd_part(comb(e + rr - 1, rr - 1))))(r),
                      epR, None, all_p, primes, 1000, thr_bits=44)
        res[f"tau{r}"] = maj
        res[f"tau{r}_true"] = tr
        print(f"  C_tau{r} majorant in {fmt_iv(maj)}; true mean in {fmt_iv(tr)}")
    # --- base-b tau_b families, b = 3..10
    for b in range(3, 11):
        gbb = (lambda bb: (lambda e: sb(comb(e + bb - 1, bb - 1), bb)))(b)
        epB = make_ep(f"taub{b}", gbb, primes, 100000, (b * b, 1), all_p, keep=400)
        maj = epB.bounds()
        tr = model_dp(f"C_[{b}]_true", (lambda bb: (lambda v: sb(v, bb)))(b),
                      (lambda bb: (lambda e: b_free(comb(e + bb - 1, bb - 1), bb)))(b),
                      epB, None, all_p, primes, 400, thr_bits=36)
        res[f"taub{b}"] = maj
        res[f"taub{b}_true"] = tr
        print(f"  base {b:2d}: C_[{b}] majorant in {fmt_iv(maj, 4)}; true in {fmt_iv(tr, 4)}")
    # --- cubic characters (majorant for w_pm(c_pm(n)))
    cubic = {7: {1, 6}, 9: {1, 8}, 13: {1, 5, 8, 12}}
    for M, cubes in cubic.items():
        lo = ONE
        hi = ONE
        Yc = 200000
        for p in primes:
            if p > Yc:
                break
            if M % p == 0:
                continue
            if p % M in cubes:
                l_lo, l_hi = local_bounds(wpe, p, exp_for(p), (1, 1))
            else:
                l_lo = l_hi = Fraction(p * p - 1, p * p) / Fraction(p ** 3 - 1, p ** 3)
            lo = (lo * l_lo.numerator) // l_lo.denominator
            hi = cdiv(hi * l_hi.numerator, l_hi.denominator)
        A = tail_A(wpe, Yc, (1, 1), +1)
        Am = tail_A(wpe, Yc, (1, 1), -1)
        S2 = inv_sq_above(Yc)
        check(A * S2 < 1 and (1 + Am) * S2 < 1, "cubic tail constants: A S2 < 1")
        th = 1 / (1 - A * S2)
        tl = 1 - (1 + Am) * S2
        Wc = (Fraction((lo * tl.numerator) // tl.denominator, ONE),
              Fraction(cdiv(hi * th.numerator, th.denominator), ONE))
        res[f"cubic{M}"] = Wc
        print(f"  cubic chi mod {M:2d}: W_chi in {fmt_iv(Wc)}")
        check(Wc[1] < 1, "W_chi < 1")
    return res


# ===========================================================================
# Section 5. Thresholds
# ===========================================================================

def section5(res):
    section("5. Threshold certificates (Fraction arithmetic from Section 4)")
    half = Fraction(1, 2)
    C_lo, C_hi = res["C"]
    Ct_lo, Ct_hi = res["C_true"]
    # E(2^k): limsup f_1 <= C_true/k
    check(Ct_hi / 3 < half and C_hi / 3 < half, "E(8): C/3 < 1/2")
    check(Ct_lo / 2 > half, "E(4): pure digit-mass bound exceeds 1/2")
    print("  E(2^k), base 2: limsup f_1 <= C_true/k; k=3 bound < 1/2; k=2 bound > 1/2")
    print(f"  (C_true-1)/2 in {fmt_iv(((Ct_lo - 1) / 2, (Ct_hi - 1) / 2))};"
          f" C_true - 1/2 in {fmt_iv((Ct_lo - half, Ct_hi - half))}; C_true/2 <= {fmt_up(Ct_hi / 2, 5)}")
    print("   k  beta=C_true/k  D-(.;2) >=     D-(.;2^k) >= (descent)  D-(.;2^k) >= (popcount)")
    table = []
    for k in (3, 4, 5, 6, 8, 10, 16, 32, 64):
        beta = Ct_hi / k
        best = half - beta
        for m in range(1, 12):
            best = max(best, 1 - m * beta - Fraction(1, 2 ** m))
        desc = Fraction(k, 2 ** k - 1) * best
        pop = (1 - Ct_hi / 2 - Fraction(k + 1, 2 ** k)) / (k - 1) if k >= 4 else Fraction(0)
        pop = max(pop, Fraction(0))
        check(best > 0, "D- > 0")
        table.append((k, beta, best, desc, pop))
        print(f"  {k:3d}  {fmt_up(beta, 5)}       {fmt_dn(best, 5)}       {fmt_dn(desc, 5)} ({float(desc):.2e})"
              f"       {fmt_dn(pop, 5)}")
    # E_odd
    Co_lo, Co_hi = res["C_odd_true"]
    check(Co_hi / 3 < half and Co_lo / 2 > half, "E_odd thresholds")
    print(f"  E_odd(2^k): k >= 3 (C_odd_true/3 <= {fmt_up(Co_hi / 3, 5)}); k = 2 fails for the method;"
          f" C_odd_true/2 <= {fmt_up(Co_hi / 2, 5)}")
    # E_+
    W_lo, W_hi = res["W_true"]
    Wm_hi = res["W_maj"][1]
    check(2 * Wm_hi / 4 < half, "E_+(16): 2W/4 < 1/2")
    check(2 * W_lo / 3 > half, "method floor at k=3")
    print(f"  E_+(2^k): transition freq <= 2W_+/k; k=4: <= {fmt_up(2 * W_hi / 4, 5)} < 1/2;"
          f" D-(E_+(16);2) >= {fmt_dn(half - 2 * W_hi / 4, 5)}")
    for k in (4, 5, 6, 8, 16):
        b2 = half - 2 * W_hi / k
        best = b2
        for m in range(2, 12):
            best = max(best, 1 - Fraction(2, 2 ** m) - (m - 1) * 2 * W_hi / k)
        print(f"    k={k:2d}: f_01+f_10 <= {fmt_up(2 * W_hi / k, 5)};  D-(E_+(2^k); 2) >= {fmt_dn(best, 5)}")
    # unitary
    for k in (3, 4, 8):
        print(f"  E*(2^{k}): limsup f_1 <= 1/{k}; D-(.;2) >= "
              f"{fmt_dn(max(half - Fraction(1, k), max(1 - Fraction(m, k) - Fraction(1, 2 ** m) for m in range(1, 10))), 5)}")
    # tau_r
    for r, kk in ((4, 4), (8, 4), (16, 5)):
        lo, hi = res[f"tau{r}_true"]
        check(hi / kk < half, f"tau_{r} threshold k={kk}")
        check(lo / (kk - 1) > half, f"tau_{r} method fails at k={kk - 1}")
        print(f"  tau_{r}: Lambert sum simply nonnormal in base 2 for k >= {kk};"
              f" method fails at k = {kk - 1}")
    # base-b tau_b families: average digit <= C/k < (b-1)/2
    for b in range(3, 11):
        lo, hi = res[f"taub{b}_true"]
        k0 = next(k for k in range(1, 20) if hi / k < Fraction(b - 1, 2))
        check(k0 == 1 or lo / (k0 - 1) >= Fraction(b - 1, 2), "base-b threshold sharp for method")
        res[f"k0_{b}"] = k0
        dm = (Fraction(b - 1, 2) - hi / k0) / (b - 1)
        print(f"  base {b:2d}: sum tau_{b}(n) {b}^(-kn) simply nonnormal in base {b} for k >= {k0};"
              f" at k0: avg digit <= {fmt_up(hi / k0, 4)}, D- >= {fmt_dn(dm, 5)}")
    # cubic characters
    for M in (7, 9, 13):
        lo, hi = res[f"cubic{M}"]
        check(2 * hi / 4 < half, "cubic k = 4")
        print(f"  cubic mod {M}: L_pm(2^k) not 2-normal in base 2 for k >= 4;"
              f" k=4: D-(.;2) >= {fmt_dn(half - 2 * hi / 4, 5)};"
              f" majorant misses k=3: {bool(2 * lo / 3 >= half)}")
    return table


# ===========================================================================
# Section 6. FINITE MEASUREMENTS ONLY
# ===========================================================================

def stats_binary(d):
    N = len(d)
    ones = sum(d)
    tr = sum(1 for i in range(N - 1) if d[i] != d[i + 1])
    return ones / N, tr / (N - 1)


def section6(tau, omg, tod, t3):
    section("6. FINITE MEASUREMENTS ONLY (prefix statistics; not proofs)")
    N2 = 1 << 17
    c_tau = tau
    c_plus = [0] + [a_plus(n, tod) for n in range(1, len(tod))]
    c_star = [0] + [1 << omg[n] for n in range(1, len(omg))]
    c_odd = tod
    rows = []
    for name, c, k, signed in (("E(2)", c_tau, 1, False), ("E(4)", c_tau, 2, False),
                               ("E(8)", c_tau, 3, False), ("E(16)", c_tau, 4, False),
                               ("E_odd(4)", c_odd, 2, False), ("E_odd(8)", c_odd, 3, False),
                               ("E*(4)", c_star, 2, False), ("E*(8)", c_star, 3, False),
                               ("E_+(2)", c_plus, 1, True), ("E_+(4)", c_plus, 2, True),
                               ("E_+(8)", c_plus, 3, True), ("E_+(16)", c_plus, 4, True)):
        P = prefix_int(c, 2, k, N2, signed=signed)
        d = to_digits(P, 2, N2)
        f1, ftr = stats_binary(d)
        M = N2 // k
        if signed:
            mass = sum(wpm(c[n]) for n in range(1, M + 1)) / N2
            kap = None
        else:
            A = dc_sum(c, 1, M + 1, 1 << k, {}) << (N2 - k * M)
            t = P - A
            mass = sum(sb(c[n], 2) for n in range(1, M + 1)) / N2
            kap = (sum(sb(c[n], 2) for n in range(1, M + 1)) + sb(t, 2) - sb(P, 2)) / N2
        rows.append((name, f1, ftr, mass, kap))
        ks = f"{kap:.5f}" if kap is not None else "   -   "
        print(f"  {name:9s} N=2^17: f_1={f1:.5f}  f_01+f_10={ftr:.5f}  "
              f"coef.mass/N={mass:.5f}  carry kappa/N={ks}")
    # E(4) carry density versus the simple-normality value (C_true-1)/2.
    # E*(4): collision positions 2n - omega(n).
    X = len(omg) - 1
    pos = {}
    for n in range(1, X + 1):
        q = 2 * n - omg[n]
        pos[q] = pos.get(q, 0) + 1
    coll_pos = sum(1 for q, r in pos.items() if r >= 2 and q <= X)
    later = sum(r - 1 for q, r in pos.items() if r >= 2 and q <= X)
    print(f"  E*(4): positions q(n)=2n-omega(n), q <= {X}: collision positions/q-range ="
          f" {coll_pos / X:.5f}; n with a later partner / (X/2) = {later / (X / 2):.5f}")
    # Base 3 and base 10.
    N3 = 40000
    for name, c, b, k, growth in (("E(9)_3", c_tau, 3, 2, "sqrt"),
                                  ("E(3)_3", c_tau, 3, 1, "sqrt"),
                                  ("sum tau_3(n) 9^-n, base 3", t3, 3, 2, "linear"),
                                  ("E*_3(9)=sum 3^w(n) 9^-n", [0] + [3 ** omg[n] for n in range(1, len(omg))], 3, 2, "linear"),
                                  ("E(100)_10", c_tau, 10, 2, "sqrt"),
                                  ("E(16)_4", c_tau, 4, 2, "sqrt")):
        Nb = N3 if b != 10 else 20000
        P = prefix_int(c, b, k, Nb, growth=growth)
        d = to_digits(P, b, Nb)
        hist = [0] * b
        for x in d:
            hist[x] += 1
        avg = sum(i * h for i, h in enumerate(hist)) / Nb
        nz = 1 - hist[0] / Nb
        freqs = " ".join(f"{h / Nb:.4f}" for h in hist)
        print(f"  {name:28s} N={Nb}: avg digit={avg:.4f} (uniform {(b - 1) / 2})"
              f" nonzero={nz:.4f} (uniform {(b - 1) / b:.4f})")
        print(f"      digit frequencies: {freqs}")
        rows.append((name, avg, nz, None, None))
    # mean of s_2(tau(n)) up to X
    m = sum(sb(tau[n], 2) for n in range(1, X + 1)) / X
    mw = sum(wpm(a_plus(n, tod)) for n in range(1, X + 1)) / X
    print(f"  (1/X) sum s_2(tau(n)) at X={X}: {m:.6f};  (1/X) sum w_pm(a_+(n)): {mw:.6f}")
    return rows


def main():
    section1()
    nmax = 600000
    tau, omg, tod, t3, spf = arithmetic_tables(nmax)
    section2(tau, spf, nmax)
    section3(tau, omg, tod)
    primes = primes_upto(300000)
    res = section4(primes)
    section5(res)
    section6(tau, omg, tod, t3)
    print()
    print(f"All {CHECKS} checks passed in {time.time() - T0:.1f} s.")


if __name__ == "__main__":
    main()
