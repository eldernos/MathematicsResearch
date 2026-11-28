#!/usr/bin/env python3
"""Phase 25 Track A: the E(4) and E*(4) carry-correlation frontier.

Companion to notes/phase25/e4-carry-correlations.md.

Sections (labels follow docs/research-objectives.md)
  1. Exhaustive/synthetic checks of the closed-form carry lemma, Kummer identity,
     monotonicity, the window lemma and superadditivity.        [Finite certificate]
  2. E(4) = sum tau(n) 4^-n: exact prefix, true (infinite-tail) carries, the
     exact digit identity for every N <= NB, the Phase-24 kappa, the head-only
     kappa and the tail-chain bound, window approximations.      [Finite certificate]
  3. Base 4: s_4(m)+s_4(2m)=3 s_2(m), the low-bit decomposition, even/odd carry
     identities, base-4 carries = even binary carries.          [Finite certificate]
  4. E*(4) = sum 2^omega(n) 4^-n: digit = occupancy off 2K*+[c*_N>=1] places,
     parity constraint on collisions, origin of every base-4 digit 3.
                                                                 [Finite certificate]
  5. Locality barrier: D-local block carries are lower bounds.  [Finite certificate]
  6. Exact countermodels (fractions.Fraction, finite Markov chains).
                                                                 [Finite certificate]
  7. Certified model constants: mu = mean odd part of tau, and the residue-window
     bounds B_W of the compound-Poisson comparison law (integer arithmetic at
     scale 2^-SB, directed rounding).           [Finite certificate; used Conditionally]
  8. FINITE MEASUREMENTS ONLY (prefix statistics) and FLOATING-POINT EXPLORATION
     (model predictions).  Never used as proofs.

Exact versus floating point.  Every assertion made with check() uses only
integers and fractions.Fraction; these are the "exact checks".  The three loose
sanity assertions on the floating-point heuristic model in Section 8 use
float_sanity() and are counted separately.  Floats otherwise appear only when
displaying finite measurements.  Every certified decimal interval quoted in the
note is produced by dec_lo (exact floor) / dec_hi (exact ceiling) and asserted
against the exact Fraction enclosure.

Exit code 0 iff every assertion holds (about 2.5 million checks, about 15 s).
Requires Python >= 3.10.7 (int.bit_count, sys.set_int_max_str_digits).
Run:  python -B scripts/phase25_e4_carries.py
"""

import math
import sys
import time
from fractions import Fraction

sys.set_int_max_str_digits(0)

CHECKS = 0           # exact checks: integers and fractions.Fraction only
FLOAT_CHECKS = 0     # floating-point sanity checks of the heuristic model (Section 8)
T0 = time.time()


def check(cond, msg="check failed"):
    """Exact assertion; cond must be computed without floating point."""
    global CHECKS
    CHECKS += 1
    if not cond:
        raise AssertionError(msg)


def float_sanity(cond, msg="float sanity check failed"):
    """Loose floating-point sanity assertion; NOT counted as an exact check."""
    global FLOAT_CHECKS
    FLOAT_CHECKS += 1
    if not cond:
        raise AssertionError(msg)


def _fmt_dec(q, k):
    sign = "-" if q < 0 else ""
    digs = str(abs(q)).rjust(k + 1, "0")
    return f"{sign}{digs[:-k]}.{digs[-k:]}"


def dec_lo(x, k):
    """Largest multiple of 10^-k that is <= x (exact floor): for LOWER endpoints."""
    x = Fraction(x)
    q = (x.numerator * 10 ** k) // x.denominator
    out = _fmt_dec(q, k)
    check(Fraction(out) <= x < Fraction(out) + Fraction(1, 10 ** k), "dec_lo is the exact floor")
    return out


def dec_hi(x, k):
    """Smallest multiple of 10^-k that is >= x (exact ceiling): for UPPER endpoints."""
    x = Fraction(x)
    q = -((-x.numerator * 10 ** k) // x.denominator)
    out = _fmt_dec(q, k)
    check(Fraction(out) - Fraction(1, 10 ** k) < x <= Fraction(out), "dec_hi is the exact ceiling")
    return out


def quoted_interval(name, lo, hi, k, note_lo, note_hi):
    """Assert that the interval [note_lo, note_hi] quoted in the note is exactly the
    outward rounding of the certified enclosure [lo, hi] to k decimals."""
    a, b = dec_lo(lo, k), dec_hi(hi, k)
    check(a == note_lo and b == note_hi, f"{name}: note quotes [{note_lo}, {note_hi}], outward [{a}, {b}]")
    check(Fraction(note_lo) <= lo <= hi <= Fraction(note_hi), f"{name}: quoted interval encloses certificate")
    return f"[{a}, {b}]"


def section(title):
    print()
    print(f"[t = {time.time() - T0:.0f} s]  {title}")
    print("-" * 78)


def s2(n):
    return bin(n).count("1")


def s4(n):
    t = 0
    while n:
        n, r = divmod(n, 4)
        t += r
    return t


def v2(n):
    return (n & -n).bit_length() - 1


def sieve_tau(n):
    t = [0] * (n + 1)
    for d in range(1, n + 1):
        for m in range(d, n + 1, d):
            t[m] += 1
    return t


def sieve_omega(n):
    w = [0] * (n + 1)
    for p in range(2, n + 1):
        if w[p] == 0:
            for m in range(p, n + 1, p):
                w[m] += 1
    return w


def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, math.isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def odd_part(n):
    return n >> v2(n)


# ---------------------------------------------------------------------------
# Column-carry machinery.  Columns j >= 1 carry weight 2^-j; arrivals r[j] >= 0.
# The TRUE carry into column j is c_j = floor(sum_{i>j} r_i 2^(j-i)).
# ---------------------------------------------------------------------------

def carries_backward(r, j0, c_start):
    """c[j] for 0 <= j <= j0 from c[j0] = c_start by c[j-1] = (r[j]+c[j])//2."""
    c = [0] * (j0 + 1)
    c[j0] = c_start
    for j in range(j0, 0, -1):
        c[j - 1] = (r[j] + c[j]) >> 1
    return c


def true_carries(r, j0, bound, upto):
    """Exact true carries for j <= upto, by monotone coalescence of the two
    chains started from the lower bound 0 and an upper bound for c[j0]."""
    lo = carries_backward(r, j0, 0)
    hi = carries_backward(r, j0, bound)
    for j in range(upto + 1):
        check(lo[j] == hi[j], f"carry chains did not coalesce at column {j}")
    return lo


def prefix_floor(terms_fn, nmax_n, nbits, guard, tail_bound_fn):
    """floor(2^nbits * x) for x = sum_n terms, terms_fn(n) = (value, exponent) with
    contribution value*2^-exponent; uses guard bits and an explicit tail bound."""
    acc = 0
    scale = nbits + guard
    for n in range(1, nmax_n + 1):
        val, e = terms_fn(n)
        sh = scale - e
        if sh >= 0:
            acc += val << sh
        else:
            acc += val >> (-sh)      # floor; at most 1 lost unit per term
    lost = nmax_n                    # floor losses
    tail = tail_bound_fn(nmax_n, scale)
    lo = acc >> guard
    hi = (acc + lost + tail) >> guard
    check(lo == hi, "prefix floor not determined; increase guard")
    return lo


# ===========================================================================
section("1. Closed-form carries, Kummer, monotonicity, window lemma (synthetic)")
# ===========================================================================


def closed_form_carries(r, L):
    """c_j = floor(sum_{j<i<=L} r_i 2^(j-i)) computed as an integer quotient."""
    out = []
    for j in range(L + 1):
        num = 0
        for i in range(j + 1, L + 1):
            num += r[i] << (L - i)
        out.append(num >> (L - j))
    return out


import itertools

n_vec = 0
for L in range(1, 7):
    for tup in itertools.product(range(4), repeat=L):
        r = [0] + list(tup)
        c = carries_backward(r, L, 0)
        cf = closed_form_carries(r, L)
        check(c == cf, "closed form != recursion")
        d = [(r[j] + c[j]) & 1 for j in range(L + 1)]
        # Kummer: sum d = sum r - sum_{j=1}^{L-1} c_j + c_L - 2 c_0 ... with c_L = 0
        for N in range(1, L + 1):
            S = sum(d[1:N + 1])
            R = sum(r[1:N + 1])
            check(S == R - sum(c[1:N]) + c[N] - 2 * c[0], "Kummer identity")
        # the value is preserved: sum r_i 2^-i = c_0 + sum d_i 2^-i
        check(sum(r[i] << (L - i) for i in range(1, L + 1))
              == (c[0] << L) + sum(d[i] << (L - i) for i in range(1, L + 1)), "value")
        n_vec += 1
print(f"closed-form carry = backward recursion and Kummer identity: {n_vec} vectors")

# monotonicity and window lemma on pseudo-random long arrival sequences
seed = 12345


def rnd():
    global seed
    seed = (seed * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
    return seed >> 33


for trial in range(300):
    L = 120
    r = [0] + [min(rnd() % 7, rnd() % 4) for _ in range(L)]
    rp = [ri + (1 if rnd() % 5 == 0 else 0) for ri in r]
    c = carries_backward(r, L, 0)
    cp = carries_backward(rp, L, 0)
    check(all(cp[j] >= c[j] for j in range(L + 1)), "monotonicity")
    d = [(r[j] + c[j]) & 1 for j in range(L + 1)]
    B = max(c)
    ell = (B + 1).bit_length()          # 2^ell >= B+1
    for W in (4, 6, 9):
        for j in range(0, L - W):
            # window carry: reset at column j+W
            cw = 0
            for i in range(j + W, j, -1):
                cw = (r[i] + cw) >> 1
            check(cw <= c[j], "window lower bound")
            if (B + 1) <= (1 << W):
                check(c[j] - cw <= 1, "window error <= 1")
            if c[j] > cw and W > ell:
                check(all(d[i] == 0 for i in range(j + 1, j + W - ell + 1)),
                      "window error forces a zero run")
    # superadditivity of carries along addition trees (Kummer associativity)
    vals = [rnd() % 50 for _ in range(12)]
    tot = sum(s2(v) for v in vals) - s2(sum(vals))
    a, b = sum(vals[:5]), sum(vals[5:])
    part = (sum(s2(v) for v in vals[:5]) - s2(a)) + (sum(s2(v) for v in vals[5:]) - s2(b))
    check(tot == part + (s2(a) + s2(b) - s2(a + b)) and tot >= part, "superadditivity")
print("monotonicity, window lemma (<=1 error, zero-run implication), superadditivity: 300 trials")

# {a+t} <= {a}+t for t >= 0 (exact rationals)
for k in range(2000):
    a = Fraction(rnd() % 10007, 97)
    t = Fraction(rnd() % 3001, 1013)
    fa = a - (a.numerator // a.denominator)
    s = a + t
    fs = s - (s.numerator // s.denominator)
    check(fs <= fa + t, "fractional-part subadditivity")
print("fractional inequality {a+t} <= {a}+t: 2000 exact cases")

# ===========================================================================
section("2. E(4): exact prefix, true carries, identities for every N")
# ===========================================================================

NB = 1 << 17                 # binary digits certified
G = 64                       # guard columns
J0 = NB + G
NMAXN = (J0 + 48) // 2 + 2
TAU = sieve_tau(NMAXN + 8)


def tau_tail_bound(nmax, scale):
    # sum_{n>nmax} tau(n) 2^(scale-2n) <= sum 2 sqrt(n) 2^(scale-2n)
    n0 = nmax + 1
    return (2 * (math.isqrt(n0 + 64) + 1) * 2 * (1 << max(scale - 2 * n0, 0))) + 2


X = prefix_floor(lambda n: (TAU[n], 2 * n), NMAXN, NB, 96, tau_tail_bound)
digits = bin(X)[2:].zfill(NB)
check(len(digits) == NB, "E(4) < 1, so floor(2^NB x) has at most NB bits")
d = [0] + [int(ch) for ch in digits]            # d[1..NB]
Spref = [0] * (NB + 1)
for j in range(1, NB + 1):
    Spref[j] = Spref[j - 1] + d[j]

# bit arrivals r_j and J-arrivals (odd part placed at the lowest-bit column)
r = [0] * (J0 + 1)
Jc = [0] * (J0 + 1)
for n in range(1, NMAXN + 1):
    t = TAU[n]
    i = 0
    while t:
        if t & 1:
            col = 2 * n - i
            if 1 <= col <= J0:
                r[col] += 1
        t >>= 1
        i += 1
    col = 2 * n - v2(TAU[n])
    if 1 <= col <= J0:
        Jc[col] += odd_part(TAU[n])
# n > NMAXN: tau(n) <= 2 sqrt n gives 4^v(n) <= tau(n)^2 <= 4n, so the lowest column
# 2n - v(n) >= 2n - 1 - log2(n)/2, which increases in n.  With n0 = NMAXN + 1 and
# a = 2 n0 - 1 - J0, the exact test 2^(2a) > n0 gives log2(n0)/2 < a, i.e. column > J0.
n0 = NMAXN + 1
check(2 * n0 - 1 - J0 > 0 and (1 << (2 * (2 * n0 - 1 - J0))) > n0,
      "all arrivals into columns <= J0 counted")
# bound r_i <= 3/2 + log2(i)/4 (proved in the note) on the computed range, exactly:
# 4 r_i - 6 <= log2(i)  <=>  4 r_i - 6 <= 0  or  2^(4 r_i - 6) <= i
check(all(4 * r[i] - 6 <= 0 or (1 << (4 * r[i] - 6)) <= i for i in range(1, J0 + 1)),
      "arrival bound")
# a priori bound for c_{J0}: c_N < 3/2 + log2(N)/4 + 1/(2 N ln 2), and 1/(2 N ln 2) < 1/N.
# Bc is valid if 3/2 + log2(J0)/4 + 1/J0 <= Bc + 1, which holds when J0 >= 64 and
# log2(J0) <= 4 Bc - 2 - 1/16, i.e. J0^16 <= 2^(16(4 Bc - 2) - 1).  Take the least such Bc.
check(J0 >= 64, "J0 >= 64")
Bc = 1
while J0 ** 16 > (1 << (16 * (4 * Bc - 2) - 1)):
    Bc += 1
check(Bc == 5, "a priori carry bound B = 5")
c = true_carries(r, J0, Bc, NB + 1)
check(c[0] == 0, "floor(E(4)) = 0")
# J-carries: c^J_{J0} <= sum_{n > J0/2} tau(n) 2^(J0-2n) <= 3 sqrt(J0)
cJ = true_carries(Jc, J0, 3 * math.isqrt(J0) + 3, NB + 1)

Rpref = [0] * (NB + 1)
JRpref = [0] * (NB + 1)
Kpref = [0] * (NB + 1)        # Kpref[N] = sum_{j=1}^{N-1} c_j
KJpref = [0] * (NB + 1)
for j in range(1, NB + 1):
    check((r[j] + c[j]) & 1 == d[j] and r[j] + c[j] == d[j] + 2 * c[j - 1], "column eq")
    check((Jc[j] + cJ[j]) & 1 == d[j] and Jc[j] + cJ[j] == d[j] + 2 * cJ[j - 1], "J column eq")
    Rpref[j] = Rpref[j - 1] + r[j]
    JRpref[j] = JRpref[j - 1] + Jc[j]
    Kpref[j] = Kpref[j - 1] + (c[j - 1] if j >= 2 else 0)
    KJpref[j] = KJpref[j - 1] + (cJ[j - 1] if j >= 2 else 0)
for N in range(1, NB + 1):
    check(Spref[N] == Rpref[N] - Kpref[N] + c[N], "exact digit identity (bits)")
    check(Spref[N] == JRpref[N] - KJpref[N] + cJ[N], "exact digit identity (J)")
print(f"E(4): {NB} digits; column equations and S(N) = R(N) - K(N) + c_N for every N <= {NB}")
print(f"  max true carry on [1,{NB}] = {max(c[1:NB + 1])} (a priori bound {Bc})")

# head-only kappa, Phase-24 kappa and the tail chain, for every N
s2tau_pref = [0] * (NB // 2 + 2)
for n in range(1, NB // 2 + 2):
    s2tau_pref[n] = s2tau_pref[n - 1] + s2(TAU[n])
zr = [0] * (NB + 1)                    # length of zero run ending at position p
for p in range(1, NB + 1):
    zr[p] = zr[p - 1] + 1 if d[p] == 0 else 0
A = 0
max_gap = (0, 0, 0, 0)
gap_hist = {}
for N in range(1, NB + 1):
    A = (A << 1) + (TAU[N // 2] if N % 2 == 0 else 0)
    M = N // 2
    FN = X >> (NB - N)
    T = FN - A
    check(T >= 0, "tail integer nonnegative")
    k_head = s2tau_pref[M] - A.bit_count()
    k_24 = s2tau_pref[M] + T.bit_count() - FN.bit_count()
    gap = k_24 - k_head
    ell = T.bit_length()
    Z = zr[N - ell] if N - ell >= 1 else 0
    check(0 <= gap <= ell + Z, "tail-chain bound gap <= ell(T_N) + Z(N)")
    # relation to the true carry total (exact): k_24 = K(N) - c_N + s2(T_N) - eps_N
    eps = Rpref[N] - s2tau_pref[M]          # tail bits landing in columns <= N
    check(k_24 == Kpref[N] - c[N] + T.bit_count() - eps, "Phase-24 kappa vs true K")
    gap_hist[gap] = gap_hist.get(gap, 0) + 1
    if gap > max_gap[0]:
        max_gap = (gap, N, ell, Z)
print(f"  head-only vs full carry gap: max {max_gap[0]} at N={max_gap[1]} "
      f"(ell(T_N)={max_gap[2]}, zero run Z(N)={max_gap[3]}); "
      f"gap >= 8 at {sum(v for g, v in gap_hist.items() if g >= 8)} values of N")
check(max_gap[0] == 9 and max_gap[1] == 490, "the longest tail chain in the certified range")
check(max_gap[2] == 2 and max_gap[3] == 8, "N = 490: ell(T_N) = 2 and Z(N) = 8")
check(sum(v for g, v in gap_hist.items() if g >= 8) == 22, "gap >= 8 at 22 values of N")
LONG_CHAIN = max_gap
T_NB = T                     # tail integer T_N at N = NB

# window approximations: c^W_j <= c_j <= c^W_j + 1, error => zero run
ellB = (Bc + 1).bit_length()
win_err = {}
for W in (4, 8, 16):
    errs = 0
    for j in range(0, NB - W):
        cw = 0
        for i in range(j + W, j, -1):
            cw = (r[i] + cw) >> 1
        diff = c[j] - cw
        check(0 <= diff <= 1, "window error in {0,1}")
        if diff:
            errs += 1
            if W > ellB:
                check(all(d[i] == 0 for i in range(j + 1, j + W - ellB + 1)),
                      "window error implies zero window")
    win_err[W] = errs
check(win_err == {4: 346, 8: 5, 16: 0}, "window error counts 346, 5, 0")
print("  window errors #{j: c_j != c_j^W}: " + ", ".join(f"W={w}: {e}" for w, e in win_err.items()))

# ===========================================================================
section("3. Base 4: digit-sum identity, low-bit decomposition, even/odd carries")
# ===========================================================================

for m in range(1 << 16):
    check(s4(m) + s4(2 * m) == 3 * s2(m), "s4(m)+s4(2m)=3 s2(m)")
print("s4(m) + s4(2m) = 3 s2(m) for all m < 2^16")

MB = NB // 2
sq = set(k * k for k in range(1, math.isqrt(NMAXN) + 2))
for m in range(1, MB + 1):
    low = (1 if m in sq else 0) + sum((TAU[m + t] >> (2 * t)) & 1 for t in range(1, 40))
    check(low == r[2 * m], "low-bit decomposition r_{2m}")
    check(((TAU[m] & 1) == 1) == (m in sq), "tau(m) odd iff m square")
print(f"r_(2m) = [m square] + sum_t bit_(2t)(tau(m+t)) for all m <= {MB}")

# base-4 arrivals a_m = 2 r_(2m-1) + r_(2m) and base-4 carries
a4 = [0] * (J0 // 2 + 1)
for m in range(1, J0 // 2 + 1):
    a4[m] = 2 * r[2 * m - 1] + r[2 * m]


def carries_backward4(arr, top, start):
    out = [0] * (top + 1)
    out[top] = start
    for m in range(top, 0, -1):
        out[m - 1] = (arr[m] + out[m]) >> 2
    return out


C4 = carries_backward4(a4, J0 // 2, 0)
C4h = carries_backward4(a4, J0 // 2, Bc)
for m in range(0, MB + 1):
    check(C4[m] == C4h[m] == c[2 * m], "base-4 carry = even binary carry")
Re = Ro = Se = So = Ee = Oo = 0
D4 = [0, 0, 0, 0]
for m in range(1, MB + 1):
    Re += r[2 * m]
    Ro += r[2 * m - 1]
    Se += d[2 * m]
    So += d[2 * m - 1]
    Ee += c[2 * m]
    Oo += c[2 * m - 1]
    D4[2 * d[2 * m - 1] + d[2 * m]] += 1
    if m % 4096 == 0 or m == MB:
        check(Se - So == (Re - Ro) + 3 * (Ee - Oo) - 2 * c[2 * m], "even-odd identity")
        check(2 * So + Se == 2 * Ro + Re - 3 * Ee + 4 * c[2 * m], "base-4 digit sum identity")
# exact per-n parity identity for even/odd bit counts
for n in range(1, MB + 1):
    t = TAU[n]
    ev = sum(1 for i in range(t.bit_length()) if (t >> i) & 1 and i % 2 == 0)
    od = s2(t) - ev
    o = odd_part(t)
    phi = sum(((-1) ** i) * ((o >> i) & 1) for i in range(o.bit_length()))
    check(ev - od == (-1) ** v2(t) * phi, "even-odd bit identity")
print("even-odd and base-4 digit-sum identities verified; base-4 carries = c_(2m)")

# ===========================================================================
section("4. E*(4): digits = occupancy off 2K*+[c*_N>=1] places; parity; base-4 digit 3")
# ===========================================================================

OM = sieve_omega(NMAXN + 8)
X2 = prefix_floor(lambda n: (1, 2 * n - OM[n]), NMAXN, NB, 96,
                  lambda nmax, scale: (1 << max(scale - 2 * nmax + 40, 0)) + 2)
dg2 = bin(X2)[2:].zfill(NB)
check(len(dg2) == NB, "E*(4) < 1")
ds = [0] + [int(ch) for ch in dg2]
rs = [0] * (J0 + 1)
for n in range(1, NMAXN + 1):
    q = 2 * n - OM[n]
    check(q % 2 == OM[n] % 2, "q(n) = omega(n) mod 2")
    if 1 <= q <= J0:
        rs[q] += 1
Bs = 2 + J0.bit_length() // 2
cs = true_carries(rs, J0, Bs, NB + 1)
check(cs[0] == 0, "floor(E*(4)) = 0")
Ks = 0
mism = 0
for j in range(1, NB + 1):
    check(rs[j] + cs[j] == ds[j] + 2 * cs[j - 1], "E*(4) column eq")
    if j >= 2:
        Ks += cs[j - 1]
    if ds[j] != (1 if rs[j] >= 1 else 0):
        mism += 1
# Thm 4.1(b): mismatches <= #{1<=j<=N: c*_j>=1} + #{0<=j<N: c*_j>=1} <= 2K* + [c*_N >= 1]
check(mism <= 2 * Ks + (1 if cs[NB] >= 1 else 0) <= 2 * Ks + cs[NB],
      "digits agree with occupancy off <= 2K* + [c*_N >= 1] <= 2K* + c*_N columns")
check(sum(ds[1:NB + 1]) == sum(rs[1:NB + 1]) - Ks + cs[NB], "E*(4) digit identity")
# collisions need equal omega-parity; every base-4 digit 3 comes from an
# adjacent pair q(n') = q(n)-1 or from a carry
byq = {}
for n in range(1, NMAXN + 1):
    byq.setdefault(2 * n - OM[n], []).append(n)
ncoll = 0                     # all collision columns q(n), n <= NMAXN (includes q > NB)
ncoll_NB = 0                  # collision columns with q <= NB
for q, lst in byq.items():
    if len(lst) >= 2:
        for a in lst:
            for b in lst:
                check(OM[a] % 2 == OM[b] % 2, "collision partners have equal omega parity")
        ncoll += 1
        ncoll_NB += q <= NB
dig3 = adj3 = car3 = 0
for m in range(1, MB + 1):
    if ds[2 * m - 1] == 1 and ds[2 * m] == 1:
        dig3 += 1
        adjacent = rs[2 * m - 1] >= 1 and rs[2 * m] >= 1
        carried = cs[2 * m] >= 1 or cs[2 * m - 1] >= 1
        check(adjacent or carried, "digit 3 needs adjacency or carry")
        adj3 += adjacent and not carried
        car3 += carried
check((mism, Ks, cs[NB]) == (15679, 7983, 0), "E*(4) mismatch and carry counts")
check((ncoll, ncoll_NB) == (7709, 7701), "E*(4) collision column counts")
check((dig3, adj3, car3) == (3886, 3834, 52), "E*(4) digit-3 counts")
print(f"E*(4): occupancy mismatches {mism} <= 2K*+c*_N = {2 * Ks + cs[NB]} (K* = {Ks}, c*_N = {cs[NB]}); "
      f"collision columns from n <= {NMAXN}: {ncoll} ({ncoll_NB} with q <= {NB}); "
      f"base-4 digit-3 positions {dig3} ({adj3} pure adjacency, {car3} with carry)")

# ===========================================================================
section("5. Locality barrier: D-local block carries are valid lower bounds")
# ===========================================================================

k_head_NB = s2tau_pref[NB // 2] - A.bit_count()      # A = head integer A_NB from Section 2
dloc = {}
for D in (0, 1, 2, 4, 8, 16, 32):
    tot = 0
    n = 1
    while n <= NB // 2:
        hi = min(n + D, NB // 2)
        val = 0
        for m in range(n, hi + 1):
            val += TAU[m] << (2 * (hi - m))
        tot += sum(s2(TAU[m]) for m in range(n, hi + 1)) - s2(val)
        n = hi + 1
    check(tot <= k_head_NB, "D-local carries <= head carries <= true carries")
    if D == 0:
        check(tot == 0, "a single coefficient never carries")
    dloc[D] = tot
# Thm 1.4: k_head <= k_24 = K(N) - c_N + s2(T_N) - eps_N <= K(N) - c_N + s2(T_N) = K(N) + O(log N)
check(k_head_NB <= Kpref[NB] - c[NB] + T_NB.bit_count(),
      "head carries <= true carries + s2(T_N) (= O(log N))")
# column-block reset lower bounds, averaged over all offsets
cblk = {}
for W in (2, 4, 8, 16, 32):
    acc = 0
    offs = list(range(0, W, max(1, W // 4)))
    for s in offs:
        a = s
        while a + W <= NB:
            cc = 0
            for j in range(a + W, a, -1):
                cc = (r[j] + cc) >> 1
                acc += cc
            a += W
    check(acc <= len(offs) * (Kpref[NB] + c[NB] + 1), "column-block reset lower bound")
    cblk[W] = Fraction(acc, len(offs))
# fixed-shift collision fractions tau(n) & (tau(n+d) >> 2d) on dyadic ranges
coll = {}
for e in (10, 13, 16):
    Xr = 1 << e
    row = []
    for dd in (1, 2, 3, 4, 6, 8):
        cnt = sum(1 for n in range(Xr // 2, Xr) if TAU[n] & (TAU[n + dd] >> (2 * dd)))
        row.append(Fraction(cnt, Xr // 2))      # finite measurement
    coll[e] = row
print("D-local carries / NB: " + ", ".join(f"D={D}: {v / NB:.5f}" for D, v in dloc.items()))
print("column-block reset carries / NB: " + ", ".join(f"W={W}: {float(v / NB):.5f}" for W, v in cblk.items()))

# ===========================================================================
section("6. Exact countermodels (iid column models, fractions.Fraction)")
# ===========================================================================


def stationary(law, cmax):
    """Exact stationary law of c' = (r + c)//2 on {0..cmax}; law = {r: prob}."""
    n = cmax + 1
    # equations: pi_k = sum_c pi_c P((r+c)//2 = k); replace last by sum = 1
    Mx = [[Fraction(0)] * (n + 1) for _ in range(n)]
    for k in range(n):
        Mx[k][k] -= 1
        for cc in range(n):
            for rv, p in law.items():
                if (rv + cc) // 2 == k:
                    Mx[k][cc] += p
    Mx[n - 1] = [Fraction(1)] * n + [Fraction(1)]
    for col in range(n):
        piv = next(i for i in range(col, n) if Mx[i][col] != 0)
        Mx[col], Mx[piv] = Mx[piv], Mx[col]
        pv = Mx[col][col]
        Mx[col] = [x / pv for x in Mx[col]]
        for i in range(n):
            if i != col and Mx[i][col] != 0:
                f = Mx[i][col]
                Mx[i] = [a - f * b for a, b in zip(Mx[i], Mx[col])]
    pi = [Mx[i][n] for i in range(n)]
    # closure: the chain never leaves {0..cmax}
    for cc in range(n):
        for rv in law:
            check((rv + cc) // 2 <= cmax, "carry state space closed")
    return pi


def f1_of(law, cmax):
    pi = stationary(law, cmax)
    f1 = sum(pi[cc] * p for cc in range(cmax + 1) for rv, p in law.items() if (rv + cc) % 2)
    Er = sum(rv * p for rv, p in law.items())
    Ec = sum(cc * pi[cc] for cc in range(cmax + 1))
    check(f1 == Er - Ec, "stationary identity f1 = E r - E c")
    return f1, pi


LAM_LO = Fraction(1339103, 2000000)     # C_true/2 lower end
LAM_HI = Fraction(1339116, 2000000)     # C_true/2 upper end
for lam in (LAM_LO, LAM_HI):
    tstar = (2 * lam - 1) / 4
    for t, expect in ((Fraction(0), lam), (tstar, Fraction(1, 2)), (lam / 2, lam / 2)):
        law = {0: 1 - lam + t, 1: lam - 2 * t, 2: t}
        f1, pi = f1_of(law, 1)
        check(f1 == lam - t / (1 - lam + 2 * t), "closed form f1 for {0,1,2} family")
        check(f1 == expect, "threshold / extreme values")
print("three-point bit-column family: f1 = lam - t/(1-lam+2t); threshold t* = (2 lam - 1)/4")

# two laws with equal first and second factorial moments, f1 = 1/2 vs f1 != 1/2
lam = LAM_LO
tstar = (2 * lam - 1) / 4
m2 = 2 * tstar
lawA = {0: 1 - lam + tstar, 1: lam - 2 * tstar, 2: tstar}
s = Fraction(1, 200)
lawB = {3: s, 2: (m2 - 6 * s) / 2}
lawB[1] = lam - 2 * lawB[2] - 3 * s
lawB[0] = 1 - lawB[1] - lawB[2] - s
check(all(p >= 0 for p in lawB.values()), "law B is a probability law")
for law in (lawA, lawB):
    check(sum(law.values()) == 1, "mass")
    check(sum(k * p for k, p in law.items()) == lam, "first moment")
    check(sum(k * (k - 1) * p for k, p in law.items()) == m2, "second factorial moment")
fA, _ = f1_of(lawA, 1)
fB, _ = f1_of(lawB, 2)
check(fA == Fraction(1, 2) and fB != Fraction(1, 2), "two moments do not fix f1")
check(fB == Fraction(92307439724609, 179643056000000), "law B: exact f1")
print(f"equal first two factorial moments: f1 = 1/2 versus f1 = {fB} in "
      f"[{dec_lo(fB, 6)}, {dec_hi(fB, 6)}]")

# E*(4) count models: E N = 1/2
f_bern, _ = f1_of({0: Fraction(1, 2), 1: Fraction(1, 2)}, 0)
check(f_bern == Fraction(1, 2), "no collisions: f1 = 1/2")
for law in ({0: Fraction(5, 8), 1: Fraction(1, 4), 2: Fraction(1, 8)},
            {0: Fraction(3, 4), 2: Fraction(1, 4)},
            {0: Fraction(21, 36), 1: Fraction(13, 36), 2: Fraction(1, 36), 3: Fraction(1, 36)}):
    check(sum(law.values()) == 1 and sum(k * p for k, p in law.items()) == Fraction(1, 2), "E N = 1/2")
    fx, _ = f1_of(law, max(law))
    check(fx < Fraction(1, 2), "any collision mass forces f1 < 1/2")
print("E*(4) count models with E N = 1/2: f1 = 1/2 iff P(N >= 2) = 0 (exact examples)")

# ===========================================================================
section("7. Certified constants: mu and residue-window bounds B_W (scale 2^-SB)")
# ===========================================================================

SB = 100
ONE = 1 << SB
PM = 1_000_000
PR = primes_upto(PM)


def odd_e1(e):
    return odd_part(e + 1)


# mu = prod_p l(p), l(p) = sum_e odd(e+1)(p-1)/p^(e+1)
mu_lo = ONE
mu_hi = ONE
for p in PR:
    lo_sum = 0
    hi_sum = 0
    e = 0
    pe1 = p                      # p^(e+1)
    while True:
        term_num = odd_e1(e) * (p - 1)
        lo_sum += (term_num << SB) // pe1
        hi_sum += -((-(term_num << SB)) // pe1)
        e += 1
        pe1 *= p
        if pe1 > (ONE << 20):
            break
    # tail: sum_{e'>=e} odd(e'+1)(p-1)/p^(e'+1) <= (e+2)/p^e = (e+2) p / p^(e+1)
    hi_sum += -((-(((e + 2) * p) << SB)) // pe1)
    mu_lo = (mu_lo * lo_sum) >> SB
    mu_hi = -((-(mu_hi * hi_sum)) >> SB)
# primes > PM: 1 <= l(p) <= 1 + 2/p^2 + 5/p^3; primes > 3 are = +-1 (mod 6), so
# sum_{p>PM} (2/p^2 + 5/p^3) <= 2/(3(PM-6)) + 1/(PM-6)^2 =: y, product <= exp(y)
y = Fraction(2, 3 * (PM - 6)) + Fraction(1, (PM - 6) ** 2)
expy = 1 + y + y * y
mu_hi = -((-(mu_hi * expy.numerator)) // expy.denominator)
MU_LO = Fraction(mu_lo, ONE)
MU_HI = Fraction(mu_hi, ONE)
check(MU_LO >= Fraction(20762592, 10 ** 7) and MU_HI <= Fraction(20763285, 10 ** 7),
      "mu inside the Phase 17 (CC-49) interval [2.0762592, 2.0763285]")
check(Fraction(20763285 - 20762592, 10 ** 7) >= 50 * (MU_HI - MU_LO),
      "mu interval at least 50 times narrower than Phase 17 (CC-49)")
mu_txt = quoted_interval("mu", MU_LO, MU_HI, 8, "2.07632553", "2.07632693")
print(f"mu in {mu_txt}  (outward-rounded; exact width <= {dec_hi(MU_HI - MU_LO, 10)})")


def mark_law_mod(Wm, P1=3000, P2=PM):
    """Lower-bound probabilities of U = prod_p odd(e_p+1) modulo 2^Wm (scale ONE)."""
    mod = 1 << Wm
    vec = [0] * mod
    vec[1] = ONE
    for p in PR:
        if p > P1:
            break
        loc = [0] * mod
        e = 0
        pe1 = p
        while pe1 <= (ONE << 8):
            loc[odd_e1(e) % mod] += ((p - 1) << SB) // pe1
            e += 1
            pe1 *= p
        locnz = [(u, x) for u, x in enumerate(loc) if x]
        new = [0] * mod
        for a in range(1, mod, 2):
            if vec[a]:
                va = vec[a]
                for u, x in locnz:
                    new[(a * u) % mod] += (va * x) >> SB
        vec = new
    # primes in (P1, P2]: none or exactly one factor 3
    S2 = 0
    S3 = 0
    for p in PR:
        if P1 < p <= P2:
            S2 += -((-ONE) // (p * p))
            S3 += ((p - 1) << SB) // (p ** 3)
    A0 = ONE - S2
    A1 = (S3 * A0) >> SB
    Ainf = ONE - (-((-ONE) // (P2 - 1)))
    new = [0] * mod
    for a in range(mod):
        if vec[a]:
            new[a] += (vec[a] * A0) >> SB
            new[(3 * a) % mod] += (vec[a] * A1) >> SB
    vec = [(x * Ainf) >> SB for x in new]
    return vec


def exp_neg_lo(lam):
    s = Fraction(0)
    term = Fraction(1)
    for i in range(0, 41):
        s += term
        term = term * (-lam) / (i + 1)
    # the partial sum ends after a positive term when 41 terms: add next (negative) term
    return s + term


def compound_mod(lam, nu, Wm, K0=30):
    mod = 1 << Wm
    e_lo = exp_neg_lo(lam)
    out = [0] * mod
    conv = [0] * mod
    conv[0] = ONE
    w = e_lo
    for k in range(K0 + 1):
        wk = (w.numerator << SB) // w.denominator
        for a in range(mod):
            if conv[a]:
                out[a] += (wk * conv[a]) >> SB
        nxt = [0] * mod
        for a in range(mod):
            if conv[a]:
                ca = conv[a]
                for u in range(mod):
                    if nu[u]:
                        nxt[(a + u) % mod] += (ca * nu[u]) >> SB
        conv = nxt
        w = w * lam / (k + 1)
    return out


def residue_window_bounds(lam, nu_full, Wm, mu_lo, mu_hi):
    """Lower/upper bounds for B_W = E_Q{R_W/2^W} + 2^-W mu_J under the model."""
    mod = 1 << Wm
    nu = [0] * mod
    for a, x in enumerate(nu_full):
        nu[a % mod] += x
    Jlaw = compound_mod(lam, nu, Wm)
    law = [0] * mod
    law[0] = ONE
    for i in range(1, Wm + 1):
        term = [0] * mod
        for a in range(mod):
            term[(a << (Wm - i)) % mod] += Jlaw[a]
        new = [0] * mod
        for a in range(mod):
            if law[a]:
                for b in range(mod):
                    if term[b]:
                        new[(a + b) % mod] += (law[a] * term[b]) >> SB
        law = new
    mass = Fraction(sum(law), ONE)
    first = Fraction(sum(a * law[a] for a in range(mod)), ONE * mod)
    missing = 1 - mass
    check(0 <= missing < Fraction(1, 10 ** 4), "missing mass small")
    eq_lo = first                                        # E_Q[R/2^W] >= eq_lo
    eq_hi = first + missing * Fraction(mod - 1, mod)     # missing mass charged at 1 - 2^-W
    lo = eq_lo + Fraction(1, mod) * mu_lo
    hi = eq_hi + Fraction(1, mod) * mu_hi
    return lo, hi, missing, eq_lo, eq_hi


NU8 = mark_law_mod(8)
BW = {}
EQ = {}
MISS = {}
for name, lam, k, Wlist in (("E(4)", Fraction(1, 2), 2, (1, 2, 3, 4)),
                            ("E(2)", Fraction(1), 1, (6, 7, 8))):
    for Wm in Wlist:
        lo, hi, miss, eq_lo, eq_hi = residue_window_bounds(lam, NU8, Wm, MU_LO / k, MU_HI / k)
        BW[(name, Wm)] = (lo, hi)
        EQ[(name, Wm)] = (eq_lo, eq_hi)
        MISS[(name, Wm)] = miss
        print(f"  {name}: B_{Wm} in [{dec_lo(lo, 6)}, {dec_hi(hi, 6)}]  "
              f"(missing mass <= {dec_hi(miss, 8)})")
check(all(MISS[("E(4)", Wm)] <= Fraction(21, 10 ** 7) for Wm in (1, 2, 3, 4)),
      "E(4): missing mass <= 2.1e-6")
check(all(MISS[("E(2)", Wm)] <= Fraction(81, 10 ** 7) for Wm in (6, 7, 8)),
      "E(2): missing mass <= 8.1e-6")
# every B_W interval quoted in the note is the outward rounding of the certificate
for key, (nlo, nhi) in {("E(4)", 1): ("0.677111", "0.677112"),
                        ("E(4)", 2): ("0.520615", "0.520617"),
                        ("E(4)", 3): ("0.452879", "0.452881"),
                        ("E(4)", 4): ("0.424560", "0.424563"),
                        ("E(2)", 7): ("0.502089", "0.502097"),
                        ("E(2)", 8): ("0.497099", "0.497108")}.items():
    quoted_interval(f"{key[0]} B_{key[1]}", BW[key][0], BW[key][1], 6, nlo, nhi)
check(BW[("E(4)", 3)][1] < Fraction(1, 2), "E(4): B_3 < 1/2 (certified)")
check(BW[("E(4)", 2)][0] > Fraction(1, 2), "E(4): B_2 > 1/2 (window 2 fails)")
check(BW[("E(2)", 8)][1] < Fraction(1, 2), "E(2): B_8 < 1/2 (certified)")
check(BW[("E(2)", 7)][0] > Fraction(1, 2), "E(2): B_7 > 1/2 (window 7 fails)")
# closed forms (U is odd, so (-1)^J = (-1)^K and P(J odd) = (1 - e^(-2 lam))/2):
#   E(4): B_1 = (1 - e^-1)/4 + mu/4;  E*(4) (marks 1, mu_J = 1/2): B_1 = (1 - e^-1)/4 + 1/4
e1_lo = exp_neg_lo(Fraction(1))
e1_hi = e1_lo + Fraction(1, math.factorial(42))      # next (positive) series term
lo1, hi1 = BW[("E(4)", 1)]
check(lo1 <= (1 - e1_lo) / 4 + MU_HI / 4 and hi1 >= (1 - e1_hi) / 4 + MU_LO / 4,
      "B_1 closed form consistent")
check((1 - e1_lo) / 4 + Fraction(1, 4) < Fraction(41, 100), "E*(4): B_1 < 0.41")
# consequences quoted in the note (Thm 2.4, Rem 2.5), all with exact outward rounding
B3hi, B4hi, B8hi = BW[("E(4)", 3)][1], BW[("E(4)", 4)][1], BW[("E(2)", 8)][1]
CT_LO = Fraction(1339103, 10 ** 6)            # C_true lower end (Phase 24 Thm 4.1)
check(dec_hi(B3hi, 6) == "0.452881" and dec_lo(Fraction(1, 2) - B3hi, 6) == "0.047119",
      "W=3: limsup f1 <= 0.452881, D^- >= 0.047119")
check(dec_hi(B4hi, 6) == "0.424563" and dec_lo(Fraction(1, 2) - B4hi, 6) == "0.075437",
      "W=4: limsup f1 <= 0.424563, D^- >= 0.075437")
check(dec_lo(CT_LO / 2 - B3hi, 6) == "0.216670", "liminf K/N >= C_true/2 - B_3 >= 0.216670")
check(dec_lo(MU_LO / 2 - B3hi, 6) == "0.585282", "liminf K^J/N >= mu/2 - B_3 >= 0.585282")
quoted_interval("mu/2 - 1/2", MU_LO / 2 - Fraction(1, 2), MU_HI / 2 - Fraction(1, 2), 6,
                "0.538162", "0.538164")
check(Fraction("0.585282") > Fraction("0.538164") and Fraction("0.216670") > Fraction("0.169558"),
      "carry densities exceed the thresholds")
check(Fraction(1, 2) - B8hi >= Fraction(289, 10 ** 5), "E(2): 1/2 - B_8 >= 2.89e-3")
# criterion table (note Section 2): sufficient thresholds t_W <= 1/2 - mu_hi 2^-W-1 and
# certified intervals for E_Q[R_W/2^W] under Q_W^(1/2)
NOTE_THR = {1: "-0.019082", 2: "0.240459", 3: "0.370229", 4: "0.435114"}
NOTE_EQ = {}
for Wm in (1, 2, 3, 4):
    need_lo = Fraction(1, 2) - MU_HI / (2 << Wm)       # 1/2 - mu 2^-W-1 >= need_lo
    thr = dec_lo(need_lo, 6)
    check(thr == NOTE_THR[Wm] and Fraction(thr) <= need_lo,
          f"W={Wm}: avg < {NOTE_THR[Wm]} suffices for RHS < 1/2")
    eq_lo, eq_hi = EQ[("E(4)", Wm)]
    NOTE_EQ[Wm] = (dec_lo(eq_lo, 6), dec_hi(eq_hi, 6))
    print(f"  E(4) criterion W={Wm}: sufficient: limsup avg{{R_W/2^W}} < {thr} "
          f"(1/2 - mu 2^-W-1 in [{dec_lo(need_lo, 8)}, {dec_hi(Fraction(1, 2) - MU_LO / (2 << Wm), 8)}]); "
          f"E_Q[R_W/2^W] in [{NOTE_EQ[Wm][0]}, {NOTE_EQ[Wm][1]}]")
check(NOTE_EQ == {1: ("0.158029", "0.158031"), 2: ("0.261075", "0.261076"),
                  3: ("0.323108", "0.323111"), 4: ("0.359675", "0.359678")},
      "criterion table: certified E_Q[R_W/2^W] intervals quoted in the note")

# ===========================================================================
section("8. FINITE MEASUREMENTS ONLY and FLOATING-POINT EXPLORATION")
# ===========================================================================

print("Finite measurements (not evidence for limits):")
f1E4 = Spref[NB] / NB
print(f"  E(4), N=2^17: R(N)/N = {Rpref[NB] / NB:.5f} (limit C_true/2 ~ 0.66956), "
      f"sum J/N = {JRpref[NB] / NB:.5f} (limit mu/2 ~ 1.03816)")
print(f"  E(4), N=2^17: f1 = {f1E4:.5f}; true carry density K/N = {Kpref[NB] / NB:.5f}; "
      f"J-carry density = {KJpref[NB] / NB:.5f}; threshold (C_true-1)/2 ~ 0.16955")
print(f"  E(4): f_even = {Se / MB:.5f}, f_odd = {So / MB:.5f}; even-column carries {Ee / MB:.5f}, "
      f"odd-column carries {Oo / MB:.5f}; arrivals even {Re / MB:.5f}, odd {Ro / MB:.5f}")
print(f"  E(4) base-4 digit frequencies 0,1,2,3: " + " ".join(f"{x / MB:.4f}" for x in D4)
      + f"; interior {(D4[1] + D4[2]) / MB:.4f}")
for W in (1, 2, 3, 4):
    acc = 0
    for j in range(0, NB - W):
        acc += sum(Jc[j + i] << (W - i) for i in range(1, W + 1)) % (1 << W)
    print(f"  E(4) empirical avg {{R_{W}/2^{W}}} = {acc / ((NB - W) * (1 << W)):.5f}")
print(f"  E*(4): f1 = {sum(ds[1:NB + 1]) / NB:.5f}, carry density {Ks / NB:.5f}, "
      f"base-4 digit-3 frequency {dig3 / MB:.4f}")
for e, row in coll.items():
    print(f"  E(4) fixed-shift collision fraction on [2^{e - 1}, 2^{e}), d=1,2,3,4,6,8: "
          + " ".join(f"{float(x):.4f}" for x in row))
print(f"  longest certified tail chain: head-only kappa undercounts by {LONG_CHAIN[0]} at N={LONG_CHAIN[1]}")

print("Floating-point exploration (heuristic compound-Poisson model; not evidence):")


def float_mark_law(UM=127, P1=1500):
    law = {1: 1.0}
    for p in PR:
        if p > P1:
            break
        loc = {}
        e = 0
        pr = 1.0 - 1.0 / p
        while pr > 1e-18:
            u = odd_e1(e)
            loc[u] = loc.get(u, 0.0) + pr
            e += 1
            pr /= p
        new = {}
        for a, x in law.items():
            for u, yv in loc.items():
                if a * u <= UM:
                    new[a * u] = new.get(a * u, 0.0) + x * yv
        law = new
    a3 = sum((1 - 1 / p) / p ** 2 for p in PR if p > P1)
    new = {}
    for x, px in law.items():
        new[x] = new.get(x, 0.0) + px * math.exp(-a3)
        if 3 * x <= UM:
            new[3 * x] = new.get(3 * x, 0.0) + px * a3 * math.exp(-a3)
    return new


def float_model(lam, nu, JM=320, W=48):
    base = [0.0] * (JM + 1)
    for u, p in nu.items():
        if u <= JM:
            base[u] += p
    Jl = [0.0] * (JM + 1)
    cur = [0.0] * (JM + 1)
    cur[0] = 1.0
    w = math.exp(-lam)
    sup = [(u, p) for u, p in enumerate(base) if p > 0]
    for k in range(30):
        for i in range(JM + 1):
            Jl[i] += w * cur[i]
        nxt = [0.0] * (JM + 1)
        for i, ci in enumerate(cur):
            if ci > 1e-18:
                for u, p in sup:
                    if i + u <= JM:
                        nxt[i + u] += ci * p
        cur = nxt
        w *= lam / (k + 1)
    supJ = [(j, p) for j, p in enumerate(Jl) if p > 1e-16]
    Po = sum(p for j, p in supJ if j & 1)
    EJ = sum(j * p for j, p in supJ)
    law = [0.0] * (JM + 2)
    law[0] = 1.0
    ecw = []
    for _ in range(W):
        new = [0.0] * (JM + 2)
        for cc, pc in enumerate(law):
            if pc > 1e-18:
                for j, p in supJ:
                    new[(j + cc) >> 1] += pc * p
        law = new
        ecw.append(sum(cc * p for cc, p in enumerate(law)))
    pce = sum(p for cc, p in enumerate(law) if cc % 2 == 0)
    f1 = pce * Po + (1 - pce) * (1 - Po)
    joint = [0.0] * 4
    for c2, p2 in enumerate(law):
        if p2 > 1e-18:
            for j2, q2 in supJ:
                t = j2 + c2
                b = t & 1
                c1 = t >> 1
                pa = Po if c1 % 2 == 0 else 1 - Po
                joint[2 + b] += p2 * q2 * pa
                joint[b] += p2 * q2 * (1 - pa)
    return f1, joint, EJ, ecw


NUF = float_mark_law()
preds = {}
for name, lam, nu in (("E(2)", 1.0, NUF), ("E(4)", 0.5, NUF), ("E(8)", 1 / 3, NUF),
                      ("E*(4)", 0.5, {1: 1.0}), ("E*(8)", 1 / 3, {1: 1.0})):
    f1m, joint, EJ, ecw = float_model(lam, nu)
    preds[name] = f1m
    print(f"  {name}: model f1 ~ {f1m:.5f}; model base-4 digit law 0,1,2,3 ~ "
          + " ".join(f"{x:.4f}" for x in joint)
          + f"; mark-window carries E c^(J,W) (W=1,2,3,8) ~ {ecw[0]:.4f} {ecw[1]:.4f} {ecw[2]:.4f} {ecw[7]:.4f}")
# loose sanity checks against Phase 17 (p* = 0.49245) and Phase 24 (0.36353, 0.27337)
# loose floating-point sanity checks; counted separately from the exact checks
float_sanity(abs(preds["E(2)"] - 0.49245) < 2e-3, "model sanity vs Phase 17")
float_sanity(abs(preds["E*(4)"] - 0.36353) < 1e-4 and abs(preds["E*(8)"] - 0.27337) < 1e-4,
             "model sanity vs Phase 24")
float_sanity(preds["E(4)"] < 0.41, "model E(4) prediction well below 1/2")

print()
print(f"ALL CHECKS PASSED: {CHECKS} exact checks (plus {FLOAT_CHECKS} floating-point "
      f"sanity checks of the heuristic model) in {time.time() - T0:.0f} s")
