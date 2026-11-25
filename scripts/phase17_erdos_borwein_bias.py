#!/usr/bin/env python3
"""Phase 17, Track C: which finite statistics can certify the Erdos-Borwein bias?

    E = sum_{m>=1} 1/(2^m - 1) = sum_{m>=1} tau(m) 2^(-m),   tau(m) = 2^V(m) U(m).

Comparison law Q_infty (Phase 14): independent columns J_d = U_1 + ... + U_K with
K ~ Poisson(1) and U_i ~ nu, the law of the odd part of tau at a random integer.
A shift reads X = sum_d J_d 2^(-d) mod 1; its first digit is 1 iff X >= 1/2.
R_D = sum_{d<=D} 2^(D-d) J_d mod 2^D is the packed residue of D columns.

Sections (all assertions are exact unless the section is marked [float]):
  A  certified mark law nu, column law, mu (integer lower bounds at scale 2^64)
  B  carry dynamic programme (Kronecker-packed integer convolutions)
  C  minimal column truncation D: law of R_D + Phase 14 tail mean
  D  stationary model: p_* and E(-1)^(carry) enclosures
  E  column hierarchy: product perturbations preserving every k-column law
  F  moment hierarchy: rational countermodels, parity dual certificate,
     combined parity/knapsack attack, explicit Bonferroni dual witness
  G  [float] Fourier coefficients, Selberg majorant, exact-coefficient dual measure
  H  Crandall (Integers 12 (2012) A23) checks against certified digits

Probabilities of the comparison law are enclosed by integer lower bounds; every
truncation and rounding loss is charged to an explicit error term.  Section G
uses IEEE doubles with explicit error radii plus a 1e-9 safety margin.

Standard library only.  Run from the repository root:

    python -B scripts/phase17_erdos_borwein_bias.py
"""

import cmath
import math
import sys
import time
from array import array
from fractions import Fraction as Fr
from itertools import compress
from math import comb, factorial, isqrt, pi

T0 = time.time()
S = 64
ONE = 1 << S
P0 = 1 << 12            # primes handled individually in the mark law
P1 = 1 << 22            # primes in (P0, P1] handled as one combined factor
MAX_MARK = 511
JMAX = 511              # column values retained
CW = JMAX + 1           # carry values (a carry never exceeds JMAX)
WB = 18                 # bytes per Kronecker slot (entries < 2^137)
ROUND = [0]             # number of floor operations (each loses < 2^-64)


def say(*args):
    print(*args, flush=True)


def section(title):
    say()
    say("=" * 78)
    say(title, "  [%.1fs]" % (time.time() - T0))
    say("=" * 78)


def dec(x, digits=8):
    return f"{float(x):.{digits}f}"


def dec_lo(x, digits=8):
    """Exact floor-rounded decimal string (guaranteed <= x)."""
    x = Fr(x)
    scale = 10 ** digits
    n = (x.numerator * scale) // x.denominator
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // scale}.{n % scale:0{digits}d}"


def dec_hi(x, digits=8):
    """Exact ceil-rounded decimal string (guaranteed >= x)."""
    x = Fr(x)
    scale = 10 ** digits
    n = -((-x.numerator * scale) // x.denominator)
    sign = "-" if n < 0 else ""
    n = abs(n)
    return f"{sign}{n // scale}.{n % scale:0{digits}d}"


# ---------------------------------------------------------------------------
# A. Certified mark law and column law
# ---------------------------------------------------------------------------

def sieve(n):
    flags = bytearray([1]) * (n + 1)
    flags[0] = flags[1] = 0
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p * p::p] = bytes(len(range(p * p, n + 1, p)))
    return flags


def odd(n):
    return n // (n & -n)


def exp_neg_bounds(x, terms=60):
    """Rational lower and upper bounds for exp(-x), 0 < x <= 20."""
    total, term, sums = Fr(0), Fr(1), []
    for k in range(terms):
        total += term
        sums.append(total)
        term = term * (-x) / (k + 1)
    # Terms decrease in modulus once k > x; partial sums then alternate.
    lo = max(s for k, s in enumerate(sums) if k > 2 * x and k % 2 == 1)
    hi = min(s for k, s in enumerate(sums) if k > 2 * x and k % 2 == 0)
    assert 0 < lo < hi
    return lo, hi


def mark_law():
    """Lower bounds nu_LB(u) * 2^64 for the law of U_* = prod_p odd(B_p + 1)."""
    flags = sieve(P1)
    small = [p for p in range(2, P0 + 1) if flags[p]]
    dist = {1: ONE}
    for p in small:
        local, a, den = {}, 0, p
        while True:                       # Pr(B_p = a) = (p - 1) / p^(a + 1)
            w = ONE * (p - 1) // den
            if not w:
                break
            o = odd(a + 1)
            local[o] = local.get(o, 0) + w
            a += 1
            den *= p
        new = {}
        for u, x in dist.items():
            for o, y in local.items():
                if u * o <= MAX_MARK:
                    new[u * o] = new.get(u * o, 0) + x * y
        dist = {u: x >> S for u, x in new.items() if x >> S}
    # Primes in (P0, P1]: all exponents <= 1 (factor 1), or exactly one
    # exponent equal to 2 and the others <= 1 (factor 3).
    sig2 = beta = 0
    for p in compress(range(P0 + 1, P1 + 1), flags[P0 + 1:]):
        sig2 += -(-ONE // (p * p))        # upper bound for 2^64 sum p^-2
        beta += ONE * (p - 1) // p ** 3   # lower bound for 2^64 sum (p-1)/p^3
    tail = -(-ONE // (2 * (P1 - 1)))      # 2^64 sum_{n > P1 odd} n^-2
    a0 = ONE - sig2
    a1 = beta * (ONE - sig2) >> S
    new = {}
    for u, x in dist.items():
        new[u] = new.get(u, 0) + x * a0
        if 3 * u <= MAX_MARK:
            new[3 * u] = new.get(3 * u, 0) + x * a1
    dist = {u: ((x >> S) * (ONE - tail)) >> S for u, x in new.items()}
    return dist, small, Fr(sig2 + tail, ONE)


def mu_upper(small, sig_large):
    """Rational upper bound for mu = E U_* = prod_p E odd(B_p + 1)."""
    prod = ONE
    for p in small:
        tot, a, den = 0, 0, p
        while den < (1 << 110):
            tot += -(-ONE * (p - 1) * odd(a + 1) // den)
            a += 1
            den *= p
        # sum_{a' >= a} (a'+1) x^a' (1-x) <= 4 (a+1) x^a for x <= 1/2
        tot += -(-ONE * 4 * (a + 1) // den * p) + 1
        prod = -(-prod * tot // ONE)
    # E odd(B_p+1) - 1 <= 2.01/p^2 for p > 4096 and prod <= 1 + 2.04 * sum.
    assert sig_large < Fr(1, 1000)
    return Fr(prod, ONE) * (1 + Fr(204, 100) * sig_large)


def column_law(nu, e1_lo):
    """b_LB(j) <= Pr(J = j) * 2^64, from j b_j = sum_u u nu(u) b_{j-u}."""
    b = [int(e1_lo * ONE)]
    items = sorted(nu.items())
    for j in range(1, JMAX + 1):
        b.append(sum(u * x * b[j - u] for u, x in items if u <= j) // (j * ONE))
    return b


# ---------------------------------------------------------------------------
# B. Carry dynamic programme
# ---------------------------------------------------------------------------

def pack(v):
    return int.from_bytes(b"".join(x.to_bytes(WB, "little") for x in v), "little")


def unpack(z, n):
    buf = z.to_bytes(n * WB, "little")
    return [int.from_bytes(buf[i * WB:(i + 1) * WB], "little") for i in range(n)]


class Column:
    """A packed column law (integer masses at scale 2^64)."""

    def __init__(self, masses):
        self.m = list(masses)
        self.n = len(self.m)
        self.z = pack(self.m)
        self.even = sum(self.m[0::2])
        self.odd = sum(self.m[1::2])


def conv(a, col):
    return unpack(pack(a) * col.z, len(a) + col.n - 1)


def floor_all(v):
    ROUND[0] += len(v)
    out = [x >> S for x in v]
    while out and not out[-1]:
        out.pop()
    return out


def step(carry, col, bit=None):
    """Process one column: s = carry + C; keep s mod 2 == bit; new carry s >> 1."""
    c = conv(carry, col)
    if bit is None:
        if len(c) % 2:
            c.append(0)
        return floor_all([x + y for x, y in zip(c[0::2], c[1::2])])
    return floor_all(c[bit::2])


def top_weights(col, bit):
    """W(c) = Pr(the column with incoming carry c shows digit `bit`) * 2^64."""
    return [col.even if (bit - c) % 2 == 0 else col.odd for c in range(CW)]


def w_chain(w, bits, brev):
    """Extend weights over carries into column t to carries into deeper columns.

    bits lists the prescribed digits of columns t+1, t+2, ... (deeper first is
    last).  W_new(c) = sum_j b_j [ (c + j) mod 2 == beta ] W_old((c + j) >> 1).
    """
    for beta in bits:
        v = [0] * (2 * CW)
        for c, x in enumerate(w):
            v[2 * c + beta] = x
        r = conv(v, brev)
        w = [x >> S for x in r[JMAX:JMAX + CW]]
        ROUND[0] += CW
    return w


def dot(carry, w):
    ROUND[0] += 1
    return sum(x * y for x, y in zip(carry, w)) >> S


def trie_leaves(T, col):
    """Carry vectors after the T least significant columns, for every pattern.

    Returns a dict: low-bit value l (0 <= l < 2^T) -> carry vector into the next
    column.  One convolution per internal node gives both children.
    """
    level = [((), [ONE])]
    for _ in range(T):
        nxt = []
        for bits, carry in level:
            c = conv(carry, col)
            for bit in (0, 1):
                nxt.append((bits + (bit,), floor_all(c[bit::2])))
        level = nxt
    return {sum(b << i for i, b in enumerate(bits)): carry for bits, carry in level}


# ---------------------------------------------------------------------------
# Interval helper
# ---------------------------------------------------------------------------

class Iv:
    def __init__(self, lo, hi=None):
        self.lo = Fr(lo)
        self.hi = Fr(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Iv) else Iv(o)))

    def __mul__(self, o):
        o = o if isinstance(o, Iv) else Iv(o)
        p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return Iv(min(p), max(p))

    def __repr__(self):
        return "[%.9f, %.9f]" % (float(self.lo), float(self.hi))


# ---------------------------------------------------------------------------
# C. Minimal column truncation (law of R_D + tail mean <= mu)
# ---------------------------------------------------------------------------

class Truncation:
    """Cells of Q_D just below 2^(D-1), dyadic blocks beyond, and Q_D(top bit 1)."""

    def __init__(self, D, T, ctx, parity_split=False):
        self.D, self.T = D, T
        col, brev = ctx["col"], ctx["brev"]
        self.cells = {}           # k -> mass LB, cell r = 2^(D-1) - k
        self.cells_par = {}       # k -> (even, odd) LB: carry parity into column 1
        leaves = trie_leaves(T, col)
        m = D - T                 # prescribed columns D-T .. 1
        if m >= 1:
            w = w_chain(top_weights(col, 0), [1] * (m - 1), brev)
            if parity_split:
                wp = [w_chain([ONE if c % 2 == par else 0 for c in range(CW)],
                              [1] * (m - 1), brev) for par in (0, 1)]
        for low, carry in leaves.items():
            k = (1 << T) - low if low else 1 << T
            if m >= 1:
                self.cells[k] = dot(carry, w)
                if parity_split:
                    self.cells_par[k] = tuple(dot(carry, wp[par]) for par in (0, 1))
        # Free prefixes: carry into column D-j after j unrestricted columns.
        free = [[ONE]]
        for _ in range(D - 1):
            free.append(step(free[-1], col))
        into1 = free[D - 1]
        self.top1 = sum(x * (col.odd if c % 2 == 0 else col.even)
                        for c, x in enumerate(into1)) >> S
        self.par1 = (sum(into1[0::2]), sum(into1[1::2]))
        ROUND[0] += 3
        # Dyadic blocks: k in (2^j, 2^(j+1)], top D-j digits 0 1...1 0.
        self.blocks = {}
        self.blocks_par = {}
        for j in range(T, D - 1):
            carry = step(free[j], col, 0)
            for _ in range(D - j - 2):
                carry = step(carry, col, 1)
            # carry is now into column 1; the top digit must be 0
            self.blocks[j] = sum(x * (col.even if c % 2 == 0 else col.odd)
                                 for c, x in enumerate(carry)) >> S
            self.blocks_par[j] = (sum(carry[0::2]), sum(carry[1::2]))
            ROUND[0] += 1

    def items(self, masses=None, block_masses=None):
        cells = self.cells if masses is None else masses
        blocks = self.blocks if block_masses is None else block_masses
        out = [(k, k, x) for k, x in cells.items()]
        out += [((1 << j) + 1, 1 << (j + 1), x) for j, x in blocks.items()]
        return out


def greedy(items, budget, which):
    """Fractional knapsack: maximise moved mass, item cost per unit mass.

    which = 0 sorts and charges by the cost lower bound (certification);
    which = 1 by the cost upper bound (realisable countermodel).
    Masses are integers at scale 2^64; returns (moved mass, critical cost).
    """
    budget = Fr(budget) * ONE
    moved = Fr(0)
    for item in sorted(items, key=lambda t: t[which]):
        cost, mass = item[which], item[2]
        if cost * mass <= budget:
            budget -= cost * mass
            moved += mass
        else:
            moved += budget / cost
            return moved / ONE, cost
    return moved / ONE, None


def dual_value(items, budget, lam):
    """LP dual of the knapsack: lam * budget + sum (1 - lam * cost_lo)^+ mass."""
    v = lam * budget
    for lo, _, mass in items:
        if lam * lo < 1:
            v += (1 - lam * lo) * Fr(mass, ONE)
    return v


# ---------------------------------------------------------------------------
# F. Moment hierarchy helpers (exact)
# ---------------------------------------------------------------------------

def odd_order_law(r):
    """The law on {0..r} with E C(N,k) = 1/k! for k <= r."""
    return {n: Fr(1, factorial(n)) * sum(Fr((-1) ** j, factorial(j)) for j in range(r - n + 1))
            for n in range(r + 1)}


def solve(mat, rhs):
    n = len(rhs)
    a = [row[:] + [rhs[i]] for i, row in enumerate(mat)]
    for i in range(n):
        piv = next(r for r in range(i, n) if a[r][i] != 0)
        a[i], a[piv] = a[piv], a[i]
        for r in range(n):
            if r != i and a[r][i] != 0:
                f = a[r][i] / a[i][i]
                a[r] = [x - f * y for x, y in zip(a[r], a[i])]
    return [a[i][n] / a[i][i] for i in range(n)]


def law_with_far_point(r, far):
    """Support {0..r-1} U {far}, binomial moments 1/k! for k <= r."""
    support = list(range(r)) + [far]
    mat = [[Fr(comb(n, k)) for n in support] for k in range(r + 1)]
    w = solve(mat, [Fr(1, factorial(k)) for k in range(r + 1)])
    return dict(zip(support, w))


def binomial_moments_match(law, r):
    return all(sum(w * comb(n, k) for n, w in law.items()) == Fr(1, factorial(k))
               for k in range(r + 1))


def parity(law):
    return sum(w * (-1) ** n for n, w in law.items())


def mix(t, law_a, law_b):
    out = {}
    for n, w in law_a.items():
        out[n] = out.get(n, 0) + t * w
    for n, w in law_b.items():
        out[n] = out.get(n, 0) + (1 - t) * w
    return out


def q_dual(r, n):
    return sum((-2) ** k * comb(n, k) for k in range(r + 1))


# ---------------------------------------------------------------------------
# H. Digits of E and arithmetic checks
# ---------------------------------------------------------------------------

def tau_table(n):
    spf = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if spf[p] == p:
            for m in range(p * p, n + 1, p):
                if spf[m] == m:
                    spf[m] = p
    tau = array("H", [0, 1]) + array("H", [0]) * (n - 1)
    expo = array("B", [0]) * (n + 1)
    rest = array("I", [0, 1]) + array("I", [0]) * (n - 1)
    for m in range(2, n + 1):
        p = spf[m]
        q = m // p
        if q % p == 0:
            expo[m] = expo[q] + 1
            rest[m] = rest[q]
        else:
            expo[m] = 1
            rest[m] = q
        tau[m] = tau[rest[m]] * (expo[m] + 1)
    return tau


def certified_bits(last, guard=64):
    """String of the fractional binary digits 1..last of E, carries certified."""
    lim = last + guard
    tau = tau_table(lim)
    assert max(tau) < 256
    raw = array("B", tau[1:lim + 1]).tobytes()
    value = 0
    for j in range(8):
        table = bytes(48 + ((x >> j) & 1) for x in range(256))
        value += int(raw.translate(table), 2) << j
    # tau(m) <= 2 sqrt(m), so the unseen tail is < 2 isqrt(lim) + 3 units of 2^-lim.
    lower, upper = value >> guard, (value + 2 * isqrt(lim) + 3) >> guard
    assert lower == upper, "carry not certified"
    assert lower >> last == 1
    return format(lower, "b")[1:]


def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.317e24 (Sorenson-Webster bases)."""
    if n < 2:
        return False
    bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in bases:
        if n % p == 0:
            return n == p
    assert n < 3317044064679887385961981
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in bases:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def brent(n):
    if n % 2 == 0:
        return 2
    for c in range(1, 200):
        y, r, q, g, x, ys = 2, 1, 1, 1, 2, 2
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(128, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += 128
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g
    raise RuntimeError("factorisation failed")


def factor(n, out=None):
    out = {} if out is None else out
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    if n == 1:
        return out
    if is_prime(n):
        out[n] = out.get(n, 0) + 1
        return out
    d = brent(n)
    factor(d, out)
    factor(n // d, out)
    return out


def tau_of(n):
    t = 1
    for e in factor(n).values():
        t *= e + 1
    return t


def remote_bit(Q, G):
    """e_Q = (tau(Q) + floor(sum_{j>=1} tau(Q+j) 2^-j)) mod 2, carry certified."""
    head = sum(tau_of(Q + j) << (G - j) for j in range(1, G + 1))
    tail = 4 * isqrt(4 * Q) + 8          # bound on the unseen tail, units 2^-G
    lo, hi = head >> G, (head + tail) >> G
    assert lo == hi, "remote carry not certified"
    return (tau_of(Q) + lo) % 2


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    ctx = {}

    # ------------------------------------------------------------------ A
    section("A. Certified mark law, column law and mu")
    e1_lo, e1_hi = exp_neg_bounds(1)
    e2_lo, e2_hi = exp_neg_bounds(2)
    nu, small, sig_large = mark_law()
    nu_mass = Fr(sum(nu.values()), ONE)
    delta_nu = 1 - nu_mass
    mu_lo = Fr(sum(u * x for u, x in nu.items()), ONE)
    mu_hi = mu_upper(small, sig_large)
    b = column_law(nu, e1_lo)
    col = Column(b)
    brev = Column(b[::-1])
    delta_b = 1 - Fr(sum(b), ONE)
    ctx.update(col=col, brev=brev)
    say("marks retained:", len(nu), "odd values <=", MAX_MARK,
        "; nu missing mass <= %.3e" % float(delta_nu))
    say("mu in [%s, %s]   (Phase 14 used mu <= 5/2)" % (dec_lo(mu_lo, 7), dec_hi(mu_hi, 7)))
    say("column law: values <= %d, missing mass delta_b <= %.3e" % (JMAX, float(delta_b)))
    assert delta_nu < Fr(3, 10 ** 7) and delta_b < Fr(3, 10 ** 7)
    assert mu_hi - mu_lo < Fr(1, 10 ** 4) and mu_hi < Fr(20764, 10000)
    p_even_lo = Fr(col.even, ONE)
    assert p_even_lo <= (1 + e2_hi) / 2 and (1 + e2_lo) / 2 - p_even_lo < delta_b
    say("Pr(J even) = (1+e^-2)/2 checked against the column law")

    def dp_error(depth):
        return depth * delta_b + Fr(ROUND[0], ONE)

    # ------------------------------------------------------------------ C
    section("C. Minimal column truncation: law of R_D plus E[tail] <= mu")
    say("f(1) <= Q_D(R_D >= 2^(D-1)) + max moved mass, cost of cell 2^(D-1)-k is k,")
    say("budget mu (Phase 14 unconditional tail mean).  'cert' must be < 1/2 to")
    say("certify; 'cmod' >= 1/2 exhibits a joint law with R_D ~ Q_D, E[tail] <= mu.")
    trunc = {}
    table = []
    for D in (4, 6, 8, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23):
        T = 10 if D in (15, 16) else min(D - 1, 8 if D == 17 else 7)
        tr = Truncation(D, T, ctx, parity_split=D in (16, 17))
        trunc[D] = tr
        err = dp_error(D)
        items = tr.items()
        up_moved, crit = greedy(items, mu_hi, 0)
        lo_moved, _ = greedy(items, mu_lo, 1)
        cert = Fr(tr.top1, ONE) + up_moved + err
        cmod = Fr(tr.top1, ONE) + lo_moved
        table.append((D, tr.top1, cert, cmod, crit))
        say("D=%2d  T=%2d  Q_D(top 1) >= %s   cert <= %s   cmod >= %s   k* = %s"
            % (D, T, dec_lo(Fr(tr.top1, ONE)), dec_hi(cert), dec_lo(cmod), crit))
    cert16 = [c for D, _, c, _, _ in table if D == 16][0]
    cmod15 = [m for D, _, _, m, _ in table if D == 15][0]
    assert cert16 < Fr(1, 2), "D = 16 must certify"
    assert cmod15 >= Fr(1, 2), "D = 15 must admit a countermodel"
    for D, _, cert, cmod, _ in table:
        if D <= 15:
            assert cmod >= Fr(1, 2)
        else:
            assert cert < Fr(1, 2)
    # LP dual certificate at D = 16.
    tr16 = trunc[16]
    items16 = tr16.items()
    _, kstar = greedy(items16, mu_hi, 0)
    lam = Fr(1, kstar)
    dual16 = Fr(tr16.top1, ONE) + dual_value(items16, mu_hi, lam) + dp_error(16)
    assert dual16 < Fr(1, 2)
    say("D=16 LP dual certificate: lambda = 1/%d, value <= %s, margin %.3e"
        % (kstar, dec_hi(dual16), float(Fr(1, 2) - dual16)))
    # The certificate is one bounded statistic of R_16:
    # Psi_16 = 1{R_16 >= 2^15} + sum_{k < kstar} (1 - k/kstar) 1{R_16 = 2^15 - k}.
    psi_q = dual16 - lam * mu_hi
    say("single statistic Psi_16: E_Q16[Psi_16] <= %s; sufficient: limsup E_I[Psi_16] < %s"
        % (dec_hi(psi_q), dec_lo(Fr(1, 2) - lam * mu_hi)))
    assert all(lam * lo >= 1 for lo, _, _ in items16 if lo >= kstar)
    say("RESULT C: D = 16 is the least truncation certified by law(R_D) + E[tail]<=mu;")
    say("          the D = 15 countermodel is also one for every D < 15 (it keeps the")
    say("          columns independent, so E[tail at level D-1] = (mu + E[tail_D])/2 <= mu).")

    # ------------------------------------------------------------------ D
    section("D. Stationary model Q_infty: p_* and E(-1)^(carry into column 1)")
    L = 48
    deep_into = {}
    carry = [ONE]
    for d in range(L, 1, -1):            # process columns L..2
        carry = step(carry, col)
        if d - 1 <= 6:
            deep_into[d - 1] = carry      # carry into column d-1
    into1 = deep_into[1]
    one_lb = Fr(sum(x * (col.odd if c % 2 == 0 else col.even)
                    for c, x in enumerate(into1)), ONE * ONE)
    zero_lb = Fr(sum(x * (col.even if c % 2 == 0 else col.odd)
                     for c, x in enumerate(into1)), ONE * ONE)
    p0_hi = (1 + e2_hi) / 2
    flip = 2 * (mu_hi + 1) * p0_hi ** L    # Phase 14 cylinder error at depth L
    errL = dp_error(L) + flip
    pstar = Iv(one_lb - flip, 1 - zero_lb + flip)
    ce = Fr(sum(into1[0::2]), ONE)
    co = Fr(sum(into1[1::2]), ONE)
    # carry_sign: into1 uses L-1 columns (2..L); the (L-1)-column carry tail error is
    # 2*(mu_hi+1)*p0_hi^(L-1) < 3*flip since 3*p0_hi ~ 1.703 > 1, so errL + 2*flip = dp_error(L) + 3*flip suffices.
    carry_sign = Iv(ce - co - errL - 2 * flip, ce - co + errL + 2 * flip)
    say("p_* in", pstar, "  width %.2e  (Phase 14: [0.492230, 0.492685])"
        % float(pstar.hi - pstar.lo))
    say("E(-1)^(c_1) in", carry_sign)
    assert Fr(492230, 10 ** 6) <= pstar.lo and pstar.hi <= Fr(492685, 10 ** 6)
    assert carry_sign.lo > Fr(11, 100)
    # Phase 14 bound |f - p_*| <= Delta_D + (s+7)(3/5)^D + mu/s covers all D >= 24
    eps24 = (664 + 7) * Fr(3, 5) ** 24 + mu_hi / 664
    assert pstar.hi + eps24 < Fr(1, 2)
    say("Phase 14 carry bound at D=24, s=664: p_* + eps <= %s < 1/2 (hence all D >= 24;"
        % dec(pstar.hi + eps24))
    say("  with Section C, every D >= 16 certifies)")
    gap_lo = Fr(1, 2) - pstar.hi
    gap_hi = Fr(1, 2) - pstar.lo
    say("1/2 - p_* in [%s, %s]" % (dec_lo(gap_lo), dec_hi(gap_hi)))

    # ------------------------------------------------------------------ E
    section("E. Column hierarchy: exact k-column laws cannot certify (k <= 4)")
    sets = {
        2: [[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44],
            [1, 2, 3, 5, 6, 9, 10, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30, 33, 34, 37, 38, 41,
             42, 45, 46, 47]],
        3: [list(range(0, 48, 2)),
            [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 25, 28, 29, 32, 33, 36, 37, 40, 41, 44, 45],
            [1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 18, 19, 20, 21, 22, 26, 27, 28, 29, 30, 34,
             35, 36, 37, 38, 42, 43, 44, 45, 46]],
        4: [list(range(1, 48, 2)),
            [1, 2, 4, 5, 6, 9, 10, 12, 13, 14, 16, 17, 18, 21, 22, 24, 25, 26, 28, 29, 30, 33, 34,
             37, 38, 41, 42, 45, 46],
            [2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 16, 18, 19, 20, 21, 22, 26, 27, 28, 29, 30, 32,
             34, 35, 36, 37, 38, 42, 43, 44, 45, 46],
            [1, 2, 3, 4, 5, 6, 7, 18, 19, 20, 21, 22, 23, 33, 34, 35, 36, 37, 38, 39]],
        5: [list(range(1, 48, 2)),
            [1, 2, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 21, 22, 24, 25, 26, 28, 29, 30, 33, 34,
             37, 38, 41, 42, 45, 46],
            [1, 2, 4, 7, 9, 10, 12, 15, 17, 18, 20, 23, 25, 26, 28, 31, 33, 34, 36, 39, 41, 42, 44,
             47],
            [1, 2, 3, 4, 5, 8, 14, 15, 18, 19, 20, 21, 24, 30, 31, 34, 35, 36, 37, 40, 46, 47],
            [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 24, 25, 26, 27, 28,
             29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]],
    }
    say("density 1 + eps * prod_{i<=K} g_i(C_i),  g_i = (1_{S_i} - pi_i)/max(pi_i, 1-pi_i)")
    say("preserves the joint law of every set of columns missing one of 1..K.")
    for K, ss in sets.items():
        restricted = {i + 1: Column([x if j in set(s) else 0 for j, x in enumerate(b)])
                      for i, s in enumerate(ss)}
        pis = {i: Iv(Fr(sum(restricted[i].m), ONE), Fr(sum(restricted[i].m), ONE) + delta_b)
               for i in restricted}
        total = Iv(0)
        # deficit of each event: L columns of delta_b, all floors so far and the
        # K steps of every event below (< 2*CW floors each), Phase 14 flip bound
        errK = dp_error(L) + Fr((1 << K) * K * 2 * CW + 2 * CW, ONE) + flip
        for mask in range(1 << K):
            cr = deep_into[K]
            for i in range(K, 1, -1):
                cr = step(cr, restricted[i] if mask >> (i - 1) & 1 else col)
            c1 = restricted[1] if mask & 1 else col
            prob = Fr(sum(x * (c1.odd if c % 2 == 0 else c1.even)
                          for c, x in enumerate(cr)), ONE * ONE)
            term = Iv(prob - flip, prob + errK)
            for i in range(1, K + 1):
                if not mask >> (i - 1) & 1:
                    term = term * (-pis[i])
            total = total + term
        norm = Iv(1)
        for i in range(1, K + 1):
            m = Iv(max(pis[i].lo, 1 - pis[i].hi), max(pis[i].hi, 1 - pis[i].lo))
            norm = norm * m
        assert total.lo > 0
        shift_lo = total.lo / norm.hi
        ok = shift_lo > gap_hi
        say("K=%d columns perturbed (all %d-column laws exact): shift >= %s  %s"
            % (K, K - 1, dec_lo(shift_lo, 6), "f(1) >= p_* + shift > 1/2" if ok else ""))
        assert ok
    say("RESULT E: the joint laws of all k-column subsets, k <= 4 (in particular all")
    say("          first and second moments and pairwise independence) leave f(1) = 1/2")
    say("          and f(1) > 1/2 attainable.")

    # ------------------------------------------------------------------ F
    section("F. Moment hierarchy: factorial moments of order <= r")
    say("Odd r: min E(-1)^N over laws on Z>=0 with E C(N,k) = 1/k! (k <= r) equals")
    say("e_r = sum_{k<=r} (-2)^k/k!  (primal: law on {0..r}; dual: q_r(n) = same sum).")
    e_odd = {}
    for r in (1, 3, 5, 7, 9, 11):
        law = odd_order_law(r)
        assert all(w >= 0 for w in law.values()) and binomial_moments_match(law, r)
        er = parity(law)
        assert er == sum(Fr((-2) ** k, factorial(k)) for k in range(r + 1))
        # dual polynomial q_r(n) <= (-1)^n, with equality on 0..r (proof in the note)
        assert all(q_dual(r, n) <= (-1) ** n for n in range(400))
        assert all(q_dual(r, n) == (-1) ** n for n in range(r + 1))
        e_odd[r] = er
        say("  r=%2d  e_r = %-14s = %s" % (r, er, dec(er, 9)))
    assert e_odd[3] < 0 < e_odd[5]
    # exact parity-zero countermodels for r <= 4
    law3, law5 = odd_order_law(3), odd_order_law(5)
    zero3 = mix(Fr(1, 6), law3, law5)
    assert binomial_moments_match(zero3, 3) and parity(zero3) == 0
    assert all(w >= 0 for w in zero3.values())
    law4 = law_with_far_point(4, 12)
    assert all(w >= 0 for w in law4.values()) and binomial_moments_match(law4, 4)
    e4 = parity(law4)
    t4 = Fr(1, 15) / (Fr(1, 15) - e4)
    zero4 = mix(t4, law4, law5)
    assert binomial_moments_match(zero4, 4) and parity(zero4) == 0
    assert all(w >= 0 for w in zero4.values())
    say("r<=3: law (1/6)*L3 + (5/6)*L5 on {0..5}:", {n: str(w) for n, w in sorted(zero3.items())})
    say("r =4: law on {0,1,2,3,12} has E(-1)^N = %s; mixed with L5 (t=%s) gives 0" % (e4, t4))
    say("  => column-1 count law with these moments, marks iid nu, all else Poisson:")
    say("     f(1) = 1/2 - E(-1)^N E(-1)^c / 2 = 1/2 exactly; with L3: f(1) >= %s"
        % dec(Fr(1, 2) + Fr(1, 6) * carry_sign.lo))
    assert Fr(1, 2) + Fr(1, 6) * carry_sign.lo > Fr(1, 2)

    # Combined attack: column-1 parity law + knapsack tail on D columns.
    say("Combined attack (column 1 law with order-r moments, columns 2..D Poisson,")
    say("tail coupled by the knapsack with budget mu):")

    def combined(D, e, which):
        tr = trunc[D]
        cells = {k: ((1 + e) * ev + (1 - e) * od) / 2 for k, (ev, od) in tr.cells_par.items()}
        blocks = {j: ((1 + e) * ev + (1 - e) * od) / 2 for j, (ev, od) in tr.blocks_par.items()}
        ev, od = tr.par1
        topq = Fr((1 - e) * ev + (1 + e) * od, 2 * ONE)
        items = [(k, k, x) for k, x in cells.items()]
        items += [((1 << j) + 1, 1 << (j + 1), x) for j, x in blocks.items()]
        if which == 1:
            moved, _ = greedy(items, mu_lo, 1)
            return topq + moved
        moved, _ = greedy(items, mu_hi, 0)
        return topq + moved + dp_error(D)

    law8 = law_with_far_point(8, 400)
    law6 = law_with_far_point(6, 40)
    for nm, lw, r in (("L8far", law8, 8), ("L6far", law6, 6)):
        assert all(w >= 0 for w in lw.values()) and binomial_moments_match(lw, r)
    # Also verify exact nonnegativity and parity convergence for even r <= 10 at L = 50000
    for r_even in (2, 4, 6, 8, 10):
        lw_big = law_with_far_point(r_even, 50000)
        assert all(w >= 0 for w in lw_big.values()) and binomial_moments_match(lw_big, r_even)
        assert parity(lw_big) - e_odd[r_even - 1] < Fr(1, 100)
    attacks = [(16, 7, e_odd[7], 1), (16, 8, parity(law8), 1),
               (17, 5, e_odd[5], 1), (17, 6, parity(law6), 1),
               (16, 9, e_odd[9], 0), (17, 7, e_odd[7], 0)]
    for D, r, e, which in attacks:
        v = combined(D, e, which)
        if which == 1:
            say("  D=%d r=%d  E(-1)^N=%s  countermodel f(1) >= %s %s"
                % (D, r, dec(e, 7), dec_lo(v, 7), "(>= 1/2)" if v >= Fr(1, 2) else ""))
            assert v >= Fr(1, 2)
        else:
            say("  D=%d r=%d  this attack gives at most f(1) <= %s (< 1/2: attack exhausted)"
                % (D, r, dec_hi(v, 7)))
            assert v < Fr(1, 2)
    say("RESULT F1: order r <= 4 fails on every D; at D = 16 order r <= 8 fails, at")
    say("           D = 17 order r <= 6 fails (exact countermodels).")

    # Bonferroni dual witness of order R on 16 columns.
    lam16 = 16
    R = 92
    ex_lo, ex_hi = exp_neg_bounds(lam16, 120)
    tot, term = Fr(0), Fr(1)
    KMAX = 360
    for K in range(KMAX + 1):
        if K >= R:
            s = 0
            for j in range(R):
                t = R - j if (R - j) % 2 == 0 else R - j - 1
                if K - j - 1 >= t:
                    s += comb(K, j) * comb(K - j - 1, t)
            tot += term * s
        term = term * lam16 / (K + 1)
    # term = 16^(KMAX+1)/(KMAX+1)!; s(K) <= 4^K beyond KMAX
    tail = term * 4 ** (KMAX + 1) / (1 - Fr(4 * lam16, KMAX + 2))
    excess = ex_hi * (tot + tail) + Fr(lam16 ** R, factorial(R))
    witness = dual16 + excess
    say("Bonferroni witness, order %d on 16 columns: Poisson excess <= %.3e;" % (R, float(excess)))
    say("  E_Poisson[witness] + lambda*mu <= %s < 1/2" % dec(witness))
    assert witness < Fr(1, 2)
    say("RESULT F2: Poisson factorial moments of total order <= 92 on 16 columns,")
    say("           with Phase 14's tail mean, certify f(1) < 1/2 (explicit witness).")

    # ------------------------------------------------------------------ G
    section("G. [float] Fourier coefficients and trigonometric certificates")
    nuf = [0.0] * (MAX_MARK + 1)
    for u, x in nu.items():
        nuf[u] = x / ONE
    dnu = float(delta_nu)
    dmu = float(mu_hi - mu_lo)
    muh = float(mu_hi)
    DM = 64

    def kappa(m):
        tot, rad = 0j, 0.0
        for d in range(1, DM + 1):
            th = m / 2.0 ** d
            w = cmath.exp(2j * pi * th)
            z = w * w
            s, e = 0j, w
            for u in range(1, MAX_MARK + 1, 2):
                x = nuf[u]
                if x:
                    s += x * (e - 1)
                e *= z
            tot += s
            rad += min(2 * dnu, 2 * pi * th * dmu)
        rad += 2 * pi * m * muh / 2.0 ** DM + 1e-10
        return tot, rad

    NS = 116
    phi, prad = {0: 1 + 0j}, {0: 0.0}
    for m in range(1, NS + 1):
        if m % 2:
            k, r = kappa(m)
            phi[m] = cmath.exp(k)
            prad[m] = abs(phi[m]) * math.expm1(r) + 1e-12
        else:
            phi[m], prad[m] = phi[m // 2], prad[m // 2]
    say("phi(m) = E_Q e(mX) = exp(kappa(m)),  phi(2m) = phi(m):")
    for m in range(1, 17):
        say("  m=%2d  phi = %+.7f %+.7fi   |phi| = %.7f   (radius %.1e)"
            % (m, phi[m].real, phi[m].imag, abs(phi[m]), prad[m]))
    part = 0.5
    for m in range(1, NS + 1, 2):
        part -= 2 / pi * phi[m].imag / m
        if m in (1, 3, 7, 15, 115):
            say("  1/2 - (2/pi) sum_{odd m<=%3d} Im phi(m)/m = %.6f" % (m, part))
    if "--dump-phi" in sys.argv:
        with open(sys.argv[sys.argv.index("--dump-phi") + 1], "w") as fh:
            for m in range(NS + 1):
                fh.write("%d %.17g %.17g\n" % (m, phi[m].real, phi[m].imag))

    def jhat(u):
        return pi * u * (1 - u) / math.tan(pi * u) + u

    def selberg(N):
        val, rad = 0.5 + 1 / (N + 1), 1e-9
        for n in range(1, N + 1):
            s = 1j / (pi * n) * jhat(n / (N + 1)) if n % 2 else (1 - n / (N + 1)) / (N + 1)
            val += 2 * (s * phi[n]).real
            rad += 2 * abs(s) * prad[n]
        return val, rad

    for N in (1, 2, 3, 7, 15, 31, 63, 115, 116):
        v, r = selberg(N)
        say("  Selberg-Vaaler majorant degree %3d: E_Q <= %.6f" % (N, v + r))
    v, r = selberg(NS)
    assert v + r < 0.5
    say("RESULT G1: degree %d majorant gives E_Q[S+] <= %.7f < 1/2 (margin %.2e)"
        % (NS, v + r, 0.5 - v - r))

    # Exact-coefficient dual measure for degree <= 110.
    NL, G, tmix = DUAL_N, DUAL_GRID, 2e-4
    if not DUAL_MEASURE:
        say("dual measure not embedded; skipping G2")
        return
    nodes = [(i / G, Fr(w)) for i, w in DUAL_MEASURE]
    mass_A = sum(Fr(w) for i, w in DUAL_MEASURE if i == 0 or 2 * i >= G)
    mass = sum(Fr(w) for _, w in DUAL_MEASURE)
    assert all(Fr(w) >= 0 for _, w in DUAL_MEASURE)
    fl = [(x, float(w)) for x, w in nodes]
    wsum = sum(abs(w) for _, w in fl)
    psi0 = (1 - (1 - tmix) * float(mass)) / tmix
    abs_sum = 0.0
    for n in range(1, NL + 1):
        rh = sum(w * cmath.exp(2j * pi * n * x) for x, w in fl)
        err = 1e-12 * wsum * n
        psi = (phi[n] - (1 - tmix) * rh) / tmix
        abs_sum += abs(psi) + (prad[n] + err) / tmix
    K = 2 * NL + 1
    min_weight = (psi0 - 1e-9 - 2 * abs_sum) / K
    lower_A = (1 - tmix) * float(mass_A)
    say("dual measure: %d grid atoms, rho_0(closed [1/2,1]) = %.7f, quadrature weights"
        " >= %.2e" % (len(nodes), float(mass_A), min_weight))
    assert min_weight > 0 and lower_A >= 0.5 + 1e-9
    say("RESULT G2: a positive measure with Fourier coefficients phi(m), |m| <= %d," % NL)
    say("           gives mass >= %.6f to [1/2, 1]; no majorant of degree <= %d certifies."
        % (lower_A, NL))

    # ------------------------------------------------------------------ H
    section("H. Digits of E and Crandall's Section 6")
    LAST = 1 << 20
    bits = certified_bits(LAST)
    crandall_abstract = "1001101101010000010111111"
    assert bits.startswith(crandall_abstract)
    say("first 25 fractional bits:", bits[:25], "= Crandall's abstract")
    # Independent derivation from the defining series sum 1/(2^m - 1):
    # sum_m floor(2^K/(2^m-1)) <= floor(2^K E) <= that + K + 2.
    KS = 1024
    lower = sum((1 << KS) // ((1 << m) - 1) for m in range(1, KS + 1))
    upper = lower + KS + 2
    series_bits = format(lower >> (KS - 512), "b")
    assert lower >> (KS - 512) == upper >> (KS - 512) and series_bits[0] == "1"
    assert len(series_bits) == 513 and series_bits[1:] == bits[:512]
    say("first 512 bits agree with the defining series sum 1/(2^m - 1) (independent)")
    z = int("1" + bits[:128], 2)
    hexd = format(z, "x")
    say("hex: %s.%s..." % (hexd[0], hexd[1:33]))
    dec_digits = (z * 10 ** 30) >> 128
    say("decimal from the bits: %d.%s" % (dec_digits // 10 ** 30,
                                          str(dec_digits % 10 ** 30).zfill(30)[:20]))
    assert str(dec_digits).startswith("160669515241529176378")
    e10 = remote_bit(10 ** 10, 64)
    e20 = remote_bit(10 ** 20, 96)
    say("e_(10^10) = %d, e_(10^20) = %d   (Crandall Table 1: 0, 0)" % (e10, e20))
    assert (e10, e20) == (0, 0)
    ones = bits.count("1")
    say("bits 1..2^20: ones %d, frequency %.6f" % (ones, ones / LAST))
    for k in (2, 3, 4):
        n = (LAST // k) * k
        counts = [0] * (1 << k)
        for i in range(0, n, k):
            counts[int(bits[i:i + k], 2)] += 1
        tot = sum(counts)
        say("  base %2d (non-overlapping): %s" % (1 << k, " ".join("%.4f" % (c * (1 << k) / tot)
                                                                for c in counts)))
    cr2 = [4359105565638, 4436987456570]
    cr4 = [1080561684345, 1106903007230, 1091079189718, 1119502629811]
    cr8 = [359190664177, 361815499829, 361805068965, 371183479256, 361917190569,
           368575859354, 370698715770, 376844529482]
    cr16 = [134567994085, 132761862795, 131164175459, 135827739295, 135994852874,
            139494161026, 140042450578, 142316547830, 137111036682, 135761702456,
            134046630124, 138527844259, 138566029070, 141037268645, 140378720036,
            141424240338]
    NB = 1 << 43
    assert sum(cr2) == NB and sum(cr4) == NB // 2 and sum(cr8) == NB // 3
    assert sum(cr16) == NB // 4
    pop = [bin(d).count("1") for d in range(16)]
    ones4 = sum(pop[d] * c for d, c in enumerate(cr4))
    ones8 = sum(pop[d] * c for d, c in enumerate(cr8))
    ones16 = sum(pop[d] * c for d, c in enumerate(cr16))
    assert ones4 == cr2[1] and ones16 == cr2[1] and cr2[1] - ones8 in (0, 1, 2)
    say("Crandall's tables (as transcribed): sums 2^43/l; ones from bases 4, 16 equal the")
    say("binary count; base 8 gives %d fewer (2 leftover bits)." % (cr2[1] - ones8))
    f_lab = Fr(cr2[1], NB)
    rest_lab = Fr(cr2[1] - ones, NB - LAST)
    rest_cmp = Fr(cr2[0] - ones, NB - LAST)
    say("as labelled: f(1) on [1,2^43] = %.6f; implied on (2^20, 2^43]: %.6f"
        % (float(f_lab), float(rest_lab)))
    say("complemented: f(1) on [1,2^43] = %.6f; implied on (2^20, 2^43]: %.6f"
        % (float(1 - f_lab), float(rest_cmp)))

    say()
    say("all assertions passed  [%.1fs]" % (time.time() - T0))


# Dual measure for Section G: atoms at i/DUAL_GRID with weights (exact decimals).
DUAL_N = 110
DUAL_GRID = 8192
DUAL_TEXT = """
0:0.0075902860761898304 72:0.0048052565867530333 73:0.0038230237236970442
145:0.0042199480284248686 146:0.0046777595456511988
217:0.00073377546920818824 218:0.0080883063161208985
291:0.0033480313066118995 292:0.0058546288393934226
364:0.0087903930220060451 365:0.00031317957470249259
436:0.0001882178908988946 437:0.0088506013104685029
511:0.0073550197479524742 512:0.0014853318719524487
583:0.0041900233743620329 584:0.0052681080595631102
656:0.0033404813344637897 657:0.0060775697290646694
729:0.007804636232556025 730:0.0013188169974744405
802:0.00031665190261511897 803:0.0089739524876069256
875:0.0041787812658850417 876:0.0048891382425079255
948:0.0025720676058234482 949:0.0063106785439163921
1023:0.005934486118410273 1024:0.0027679604752023309
1095:0.0023162172281367627 1096:0.0071751754852590766
1168:0.0014729703709126334 1169:0.0080905522401035612
1241:0.0067851273527260673 1242:0.0025613102458160162
1315:0.0095716961470197048 1387:0.0050345759947045925
1388:0.0043345808607072158 1460:0.0048051079854405602
1461:0.0044019026472721457 1534:0.0031400932148989646
1535:0.0057732223788037303 1607:0.0079725513445382933
1608:0.0014490387277318196 1680:0.0062480673373474672
1681:0.0030646103223466782 1752:0.00076237469654220804
1753:0.0082158687983957517 1826:0.0018375911940230381
1827:0.0072313556856265018 1899:0.004339162965392775
1900:0.0044622299024318418 1972:0.0014896210652228076
1973:0.007100482716978984 2047:0.0024138333590003848
2048:0.0060433405149067808 2120:0.007824400951327113
2121:0.0015307802082376997 2193:0.0071155165492712341
2194:0.0023886732132536699 2265:0.0030796272798474899
2266:0.006254129969239069 2339:0.0058840603273762502
2340:0.0037462396440125223 2411:0.0017580132153171167
2412:0.0077061281966039974 2484:0.0021119460701119913
2485:0.0072275905507023664 2558:0.0008738690696516243
2559:0.0081980273420138271 2631:0.006386563393252288
2632:0.003229952483459799 2704:0.0052275659072668346
2705:0.004294321885843091 2776:0.00030036613809425472
2777:0.0088890448092617778 2850:0.0020344921150392118
2851:0.0072710349809274469 2923:0.005644484112134856
2924:0.0034015487597375675 2996:0.0039558329395146131
2997:0.0048783882955838326 3071:0.0078101821845384051
3072:0.00080070422366284135 3143:0.0040040102010174133
3144:0.0053167381224198213 3216:0.0029180959227931348
3217:0.0064294555679921565 3289:0.0077959732688489668
3290:0.0013096522423421365 3362:0.0010827771115755691
3363:0.0082094543360127174 3435:0.0057211565174503194
3436:0.0033527623187377823 3508:0.0053755278403475387
3509:0.003524621969847088 3582:0.0039847227189479337
3583:0.004607623041525408 3655:0.0083667290950268577
3656:0.00066977076455932729 3728:0.0064273880028356762
3729:0.0024784089774877462 3800:0.00085546777268061291
3801:0.0077137179565828383 3874:0.0016144318664350703
3875:0.0070227078413626987 3947:0.0035780873198160553
3948:0.0047932052636504583 4020:0.00038295806395883647
4021:0.0077794520688502251 4096:0.0080739958448663926
4168:0.005285040264222848 4169:0.0037462636331006957
4241:0.0048518237629811582 4242:0.0043807343630445127
4313:0.001365430304448732 4314:0.0077368479254499647
4387:0.0044298586182673046 4388:0.0050048257206277503
4459:0.00083698649920911682 4460:0.0084589715541109785
4532:0.0015864330019138683 4533:0.0076115567034270434
4606:0.00050728065059427033 4607:0.0084526546232892141
4679:0.0065168932495126373 4680:0.0030234723881581
4752:0.0059247768087487742 4753:0.0035459496399608305
4824:0.0015065736529262367 4825:0.0076514596174730547
4898:0.0035732935882325971 4899:0.005723036087197271
4971:0.0077400341239096775 4972:0.0013148211105809377
5044:0.0064720358877917283 5045:0.0023853655445313484
5118:0.002068314031658758 5119:0.0065745377343960822
5191:0.0075749045563933077 5192:0.0018059559579302871
5264:0.0070825073219977974 5265:0.0023380208974675808
5336:0.0032995546771400872 5337:0.0058918470842043054
5410:0.00611838198375559 5411:0.00326653906671793
5482:0.0021394041658829421 5483:0.0070363242626839979
5555:0.0022278511029700963 5556:0.0067793414603712163
5629:0.001494248804873783 5630:0.0072001474895368872
5702:0.0061134383567830975 5703:0.0030583503089407055
5775:0.0047589713933839156 5776:0.004287689487592266
5848:0.0085663388974642034 5849:0.00015168627608538735
5921:0.0010588608877169601 5922:0.0077248407892473231
5994:0.0039792054045547894 5995:0.004544554076117824
6067:0.0014435874459148693 6068:0.0068696230356128877
6142:0.003335506391332363 6143:0.0048103830420499821
6215:0.0083015489888516331 6216:0.0006795360857064426
6288:0.0077965452740729165 6289:0.0013008424876784521
6360:0.004120715915393966 6361:0.0048088761728436761
6434:0.0066718345720180048 6435:0.0025087760395045931
6506:0.0029827615698916577 6507:0.0060382901624624575
6579:0.0031446020722528303 6580:0.0057498863767357512
6653:0.0024175181451470641 6654:0.006197077115240931
6726:0.0073212701710529673 6727:0.001804669138577044
6799:0.0062655904817690488 6800:0.0027579163126963562
6871:0.001606083115722267 6872:0.0071067979835870163
6945:0.0029488198680162783 6946:0.0058533299220439559
7018:0.0064693554020520327 7019:0.0020910815381001576
7091:0.0046315137788017196 7092:0.0037266103790416193
7165:0.00057514365116708072 7166:0.0075431149956241457
7238:0.0045403798871578175 7239:0.0042339160364158138
7311:0.0032723747018024094 7312:0.0055100126734140093
7384:0.0076073154106559094 7385:0.00094714515263183744
7457:0.00073981814765021296 7458:0.0079683667085892595
7530:0.0048611410608673565 7531:0.0036442644731977877
7603:0.0039720026490294852 7604:0.0043662468905355956
7677:0.0025566243291404805 7678:0.0054775359662622642
7750:0.0057818585635404591 7751:0.0026672774347973045
7823:0.0034214949081116659 7824:0.0048980043772884237
7896:0.0057316238335716335 7897:0.0022763384669834169
7970:0.0056220024686042735 7971:0.0024398808084690731
8043:0.0065872087187032729 8044:0.0012278193743311759
8116:0.0024311225770972801 8117:0.0051926316555890627
"""
DUAL_MEASURE = [(int(a), b) for a, b in (t.split(":") for t in DUAL_TEXT.split())]

if __name__ == "__main__":
    main()
