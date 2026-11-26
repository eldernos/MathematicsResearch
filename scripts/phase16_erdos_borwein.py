#!/usr/bin/env python3
"""Two-source arrival correlations and binary word laws of the Erdos-Borwein constant.

E = sum_{m>=1} 1/(2^m - 1) = sum_m tau(m) 2^(-m).  Write tau(m) = 2^V(m) U(m)
with U(m) odd.  The term m places the odd mark U(m) at binary position
t(m) = m - V(m).  N(t) counts the sources at position t and C(t) is the sum of
their marks.  A shift n reads the fractional digits n+1, n+2, ...

All statistics of the actual constant are exact integer counts on the dyadic
shells of shifts [2^s, 2^(s+1)).  The binary digits are certified by integer
carry bounds, as in scripts/erdos_borwein_arrivals.py.  Floating point is used
only for the comparison laws (the marked Poisson model Q_D, the independent
displacement model, the local Euler factors) and for printed ratios.

Standard library only.  Run from the repository root:

    python -B scripts/phase16_erdos_borwein.py
"""

import argparse
import random
import sys
from array import array
from cmath import exp as cexp
from collections import Counter, defaultdict
from itertools import compress
from math import cos, exp, isqrt, lgamma, log, pi, sqrt

CUT = 1e-18                      # truncation of local geometric series
ADD = [bytes((x + d) & 255 for x in range(256)) for d in range(256)]
BITCHAR = [bytes(48 + ((x >> j) & 1) for x in range(256)) for j in range(8)]
ASCII01 = bytes(1 if x == 49 else 0 for x in range(256))
EQ01 = [bytes(1 if x == v else 0 for x in range(256)) for v in range(256)]
EQFF = [bytes(255 if x == v else 0 for x in range(256)) for v in range(256)]
EQCHAR = [bytes(49 if x == v else 48 for x in range(256)) for v in range(256)]
ODDCHAR = bytes(49 if x & 1 else 48 for x in range(256))


def v2(n):
    return (n & -n).bit_length() - 1


def odd(n):
    return n >> v2(n)


def le_bytes(arr):
    """Little-endian raw bytes of an array of unsigned integers."""
    if sys.byteorder == "little":
        return arr.tobytes()
    copy = array(arr.typecode, arr)
    copy.byteswap()
    return copy.tobytes()


def from_le(typecode, raw):
    out = array(typecode)
    out.frombytes(raw)
    if sys.byteorder != "little":
        out.byteswap()
    return out


def bitset(raw_ascii):
    """Integer whose bit i is set iff raw_ascii[i] == ord('1')."""
    return int(raw_ascii[::-1], 2) if raw_ascii else 0


# --------------------------------------------------------------------------
# Exact arithmetic tables
# --------------------------------------------------------------------------

def prime_flags(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[0] = flags[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p :: p] = bytes(len(range(p * p, limit + 1, p)))
    return flags


def valuation_tables(limit):
    """V(n) = v_2(tau(n)) and U(n) = odd part of tau(n) for 0 <= n <= limit.

    V(n) = sum_p v_2(v_p(n) + 1) is accumulated as a telescoping sum over the
    prime powers p^a dividing n; U is multiplied over prime squares only, since
    exponents 0 and 1 have odd part one.
    """
    flags = prime_flags(limit)
    primes = list(compress(range(limit + 1), flags))
    V = bytearray(limit + 1)
    U = array("H", [1]) * (limit + 1)
    for p in primes:
        V[p::p] = V[p::p].translate(ADD[1])
        if p > limit // p:
            continue
        power, a = p * p, 2
        while power <= limit:
            delta = v2(a + 1) - v2(a)
            if delta:
                V[power::power] = V[power::power].translate(ADD[delta & 255])
            before, after = odd(a), odd(a + 1)
            if before != after:
                U[power::power] = array("H", [x // before * after for x in U[power::power]])
            if power > limit // p:
                break
            power *= p
            a += 1
    return primes, V, U


def weighted_sum(values, start, stop):
    """sum_{start <= i < stop} values[i] * 2^(stop - 1 - i), values in array('H')."""
    raw = le_bytes(values[start:stop])
    low, high = raw[0::2], raw[1::2]
    total = 0
    for j in range(8):
        total += int(low.translate(BITCHAR[j]), 2) << j
    if high != bytes(len(high)):
        for j in range(8):
            total += int(high.translate(BITCHAR[j]), 2) << (j + 8)
    return total


def certified_floor(tau, last, limit):
    """floor(2^last * E), with the carry from m > last certified."""
    head = weighted_sum(tau, 1, last + 1)
    tail = weighted_sum(tau, last + 1, limit + 1)
    shift = limit - last
    # For m > limit, tau(m) <= 2 sqrt(m), so the unseen tail in units of
    # 2^(-limit) is at most 2 sqrt(limit) + 1 < 2 isqrt(limit) + 3.
    lower, upper = tail >> shift, (tail + 2 * isqrt(limit) + 3) >> shift
    if lower != upper:
        raise RuntimeError("carry not certified; enlarge the guard")
    return head + lower


def binary_digits(tau, last, limit):
    """bytes d with d[i] = i-th fractional binary digit of E, 1 <= i <= last."""
    z = certified_floor(tau, last, limit)
    if z >> last != 1:
        raise RuntimeError("unexpected integer part")
    text = format(z & ((1 << last) - 1), "b").zfill(last)
    return b"\x00" + text.encode().translate(ASCII01)


def columns(V, U, lo, hi, vmax):
    """N(t) and C(t) for lo <= t < hi (index t - lo), from sources m = t + v."""
    length = hi - lo
    raw_u = le_bytes(U)
    n_total = c_total = 0
    for v in range(vmax + 1):
        seg = V[lo + v : hi + v]
        n_total += int.from_bytes(seg.translate(EQ01[v]), "little")
        mask = seg.translate(EQFF[v])
        wide = bytearray(2 * length)
        wide[0::2] = mask
        wide[1::2] = mask
        c_total += (int.from_bytes(raw_u[2 * (lo + v) : 2 * (hi + v)], "little")
                    & int.from_bytes(wide, "little"))
    return n_total.to_bytes(length, "little"), from_le("H", c_total.to_bytes(2 * length, "little"))


def packed_residues(C, start, count, depth):
    """R_depth(n) = sum_{d=1}^{depth} 2^(depth-d) C(n+d) mod 2^depth, n = start..start+count-1.

    C is indexed by position.  Uses 32-bit lanes: C < 2^16, so no lane overflows.
    """
    lanes = array("I", C[start + 1 : start + count + depth + 1])
    x = int.from_bytes(le_bytes(lanes), "little")
    total = 0
    for d in range(1, depth + 1):
        total += (x >> (32 * (d - 1))) << (depth - d)
    lane_mask = int.from_bytes(((1 << depth) - 1).to_bytes(4, "little") * count, "little")
    return from_le("I", (total & lane_mask).to_bytes(4 * count + 8, "little")[: 4 * count])


# --------------------------------------------------------------------------
# Comparison laws
# --------------------------------------------------------------------------

def mark_law(primes, max_mark=255, prime_cut=1 << 14):
    """nu = law of U_* = prod_p odd(B_p + 1), Pr(B_p = a) = (1 - 1/p) p^(-a)."""
    dist = {1: 1.0}
    for p in primes:
        if p > prime_cut:
            break
        local, a, prob = defaultdict(float), 0, 1 - 1 / p
        while prob > CUT:
            local[odd(a + 1)] += prob
            a += 1
            prob /= p
        new = defaultdict(float)
        for u, w in dist.items():
            for o, q in local.items():
                if u * o <= max_mark:
                    new[u * o] += w * q
        dist = new
    big = [p for p in primes if p > prime_cut]
    eps = sum((1 - 1 / p) / (p * p) for p in big) + 1 / (big[-1] * log(big[-1]))
    final = defaultdict(float)
    for u, w in dist.items():
        final[u] += w * (1 - eps)
        if 3 * u <= max_mark:
            final[3 * u] += w * eps
    return dict(final)


def compound_poisson(nu, jmax):
    """b_j = Pr(J = j), J = sum of a Poisson(1) number of marks with law nu."""
    b = [exp(-1.0)] + [0.0] * jmax
    items = sorted(nu.items())
    for j in range(1, jmax + 1):
        b[j] = sum(u * w * b[j - u] for u, w in items if u <= j) / j
    return b


def fft(values, sign):
    """sum_j a_j exp(sign 2 pi i j k / n), radix two."""
    a = list(values)
    n = len(a)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit
            bit >>= 1
        j |= bit
        if i < j:
            a[i], a[j] = a[j], a[i]
    length = 2
    while length <= n:
        step = cexp(sign * 2j * pi / length)
        half = length // 2
        for start in range(0, n, length):
            w = 1.0
            for k in range(start, start + half):
                u, v = a[k], a[k + half] * w
                a[k], a[k + half] = u + v, u - v
                w *= step
        length <<= 1
    return a


def poisson_residue_law(b, depth):
    """Q_depth: law of sum_{d=1}^{depth} 2^(depth-d) J_d mod 2^depth, J_d i.i.d. ~ b."""
    size = 1 << depth
    folded = [0.0] * size
    for j, w in enumerate(b):
        folded[j % size] += w
    phi = fft(folded, +1)
    rhat = [1.0 + 0j] * size
    for h in range(size):
        prod = 1.0 + 0j
        for d in range(1, depth + 1):
            prod *= phi[(h << (depth - d)) % size]
        rhat[h] = prod
    q = fft(rhat, -1)
    return [max(z.real / size, 0.0) for z in q]


def model_one_frequency(b, depth=48, tol=1e-14):
    """One-frequency of the infinite independent model, and E(-1)^carry."""
    cap = max(j for j, w in enumerate(b) if w > tol)
    col = b[: cap + 1]
    carry = {0: 1.0}
    for _ in range(depth):
        new = defaultdict(float)
        for c, w in carry.items():
            for j, q in enumerate(col):
                new[(c + j) >> 1] += w * q
        carry = {c: w for c, w in new.items() if w > tol}
    even, oddm = sum(col[0::2]), sum(col[1::2])
    p_one = sum(w * (oddm if c % 2 == 0 else even) for c, w in carry.items())
    carry_sign = sum(w * (-1) ** c for c, w in carry.items())
    return p_one, carry_sign, even - oddm


def binomial_mad(n, q):
    """E|X - nq| for X ~ Bin(n, q) (de Moivre)."""
    if q <= 0.0 or q >= 1.0:
        return 0.0
    nu = int(n * q)
    if nu >= n:
        return 0.0
    logv = (log(2 * (nu + 1)) + lgamma(n + 1) - lgamma(nu + 2) - lgamma(n - nu)
            + (nu + 1) * log(q) + (n - nu) * log(1 - q))
    return exp(logv)


def tv_floor(n, law):
    """Expected total variation of an i.i.d. sample of size n from law."""
    return sum(binomial_mad(n, q) for q in law) / (2 * n)


# --------------------------------------------------------------------------
# Local (p-adic) joint laws of (v_p(m), v_p(m+k)), m Haar-distributed on Z_p
# --------------------------------------------------------------------------

def v2_p(k, p):
    e = 0
    while k % p == 0:
        k //= p
        e += 1
    return e


def local_single(p, w):
    total, a, prob = 0.0, 0, 1 - 1 / p
    while prob > CUT:
        total += prob * w(a)
        a += 1
        prob /= p
    return total


def local_joint(p, kappa, w1, w2):
    """E[w1(v_p(m)) w2(v_p(m+k))] for v_p(k) = kappa, m Haar on Z_p.

    a < kappa forces v_p(m+k) = a; a > kappa forces v_p(m+k) = kappa; for
    a = kappa the excess valuation j satisfies Pr(j = 0) = (p-2)/(p-1) and
    Pr(j = i) = (1-1/p) p^(1-i) / (p-1) for i >= 1.
    """
    q = 1 - 1 / p
    total, a, prob = 0.0, 0, q
    while prob > CUT or a <= kappa:
        if a < kappa:
            total += prob * w1(a) * w2(a)
        elif a > kappa:
            total += prob * w1(a) * w2(kappa)
        else:
            inner = (p - 2) / (p - 1) * w2(kappa)
            i, pj = 1, q / (p - 1)
            while pj > CUT:
                inner += pj * w2(kappa + i)
                i += 1
                pj /= p
            total += prob * w1(kappa) * inner
        a += 1
        prob /= p
    return total


def euler_tables(primes, thetas, pmax=2000, pratio=1024, kcap=4096):
    """Local factors R_p(theta; kappa) = E_p^joint / |phi_p(theta)|^2 for the
    difference V(m+k) - V(m), kappa = v_p(k).  For p not dividing k,
    E_p^joint = 2 Re phi_p(theta) - 1 exactly (the two divisibility events are
    disjoint).  Returns the product over 5 <= p <= pmax of the kappa = 0
    factors and a table of the remaining factors."""
    plus = [lambda a, th=th: cexp(2j * pi * th * v2(a + 1)) for th in thetas]
    minus = [lambda a, th=th: cexp(-2j * pi * th * v2(a + 1)) for th in thetas]
    r0, rk = {}, {}
    base = [1.0] * len(thetas)
    for p in primes:
        if p > pmax:
            break
        row, phis = [], []
        for i in range(len(thetas)):
            phi = local_single(p, plus[i])
            phis.append(phi)
            row.append((2 * phi.real - 1) / abs(phi) ** 2)
        r0[p] = row
        if p >= 5:
            base = [x * y for x, y in zip(base, row)]
        if p <= pratio:
            kappa = 0 if p <= 3 else 1
            while p ** kappa <= kcap:
                rk[p, kappa] = [local_joint(p, kappa, minus[i], plus[i]).real / abs(phis[i]) ** 2
                                for i in range(len(thetas))]
                kappa += 1
    return base, r0, rk


def small_factorization(k, pratio=1024):
    k, out, p = abs(k), [], 2
    while p <= pratio and k > 1:
        e = 0
        while k % p == 0:
            k //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1 if p == 2 else 2
    return out


def euler_factor(k, tables):
    """E_k(theta, -theta) = prod_{p <= 2000} R_p(theta; v_p(k)) on the theta grid
    (primes in (1024, 2000] dividing k keep their kappa = 0 factor)."""
    base, r0, rk = tables
    fac = dict(small_factorization(k))
    vals = [x * y * z for x, y, z in zip(base, rk[2, fac.get(2, 0)], rk[3, fac.get(3, 0)])]
    for p, e in fac.items():
        if p >= 5:
            vals = [x * y / z for x, y, z in zip(vals, rk[p, e], r0[p])]
    return vals


# --------------------------------------------------------------------------
# Shell statistics
# --------------------------------------------------------------------------

def source_law(V, lo, hi):
    """Law of V(m) over sources m with lo <= t(m) < hi."""
    vmax = max(V[lo : hi + 64])
    counts = [0] * (vmax + 1)
    for v in range(vmax + 1):
        counts[v] = V[lo + v : hi + v].count(v)
    total = sum(counts)
    return [c / total for c in counts], total


def pair_counts(key, lo, hi, keys_a, keys_b, bmax=3):
    """counts[b][k] = #{(m, m'): lo <= t(m) < hi, t(m') = t(m) + b, m' = m + k}
    restricted to key(m) in keys_a and key(m') in keys_b, where key encodes
    V (low six bits) and an optional mark class (bit six)."""
    length = hi - lo
    mask = (1 << length) - 1
    sets_a, sets_b = {}, {}
    for kv in set(keys_a) | set(keys_b):
        v = kv & 63
        raw = key[lo + v : hi + bmax + v].translate(EQCHAR[kv])
        if raw.count(b"1") == 0:
            continue
        s = bitset(raw)
        if kv in keys_a:
            sets_a[kv] = s & mask
        if kv in keys_b:
            sets_b[kv] = s
    counts = [defaultdict(int) for _ in range(bmax + 1)]
    for b in range(bmax + 1):
        for ka, sa in sets_a.items():
            for kb, sb in sets_b.items():
                k = b + (kb & 63) - (ka & 63)
                if k == 0:
                    continue
                c = (sa & (sb >> b)).bit_count()
                if c:
                    counts[b][k] += c
    return counts


def parity_correlations(V, lo, hi, kmax):
    length = hi - lo
    mask = (1 << length) - 1
    par = bitset(V[lo : hi + kmax].translate(ODDCHAR))
    single = (length - 2 * (par & mask).bit_count()) / length
    out = []
    for k in range(1, kmax + 1):
        out.append((length - 2 * ((par ^ (par >> k)) & mask).bit_count()) / length)
    return single, out


def joint_difference_law(V, lo, hi, kmax, vmax):
    """law[k][x] = Pr_m(V(m+k) - V(m) = x), m uniform on [lo, hi)."""
    length = hi - lo
    mask = (1 << length) - 1
    sets = {}
    for v in range(vmax + 1):
        raw = V[lo : hi + kmax].translate(EQCHAR[v])
        if raw.count(b"1"):
            sets[v] = bitset(raw)
    law = {}
    for k in range(1, kmax + 1):
        row = defaultdict(int)
        for a, sa in sets.items():
            sa_m = sa & mask
            for b_, sb in sets.items():
                c = (sa_m & (sb >> k)).bit_count()
                if c:
                    row[b_ - a] += c
        law[k] = {x: c / length for x, c in row.items()}
    return law


def histogram_stats(values):
    if isinstance(values, (bytes, bytearray)):
        hist = {j: values.count(j) for j in range(max(values) + 1)}
        hist = Counter({j: c for j, c in hist.items() if c})
    else:
        hist = Counter(values)
    n = sum(hist.values())
    mean = sum(j * c for j, c in hist.items()) / n
    var = sum((j - mean) ** 2 * c for j, c in hist.items()) / n
    fact2 = sum(j * (j - 1) * c for j, c in hist.items()) / n
    fact3 = sum(j * (j - 1) * (j - 2) * c for j, c in hist.items()) / n
    sign = sum((-1) ** j * c for j, c in hist.items())
    return hist, n, mean, var, fact2, fact3, sign


def fold(hist, bits):
    size = 1 << bits
    out = [0] * size
    for r, c in hist.items():
        out[r & (size - 1)] += c
    return out


def total_variation(counts, n, law):
    return 0.5 * sum(abs(c / n - q) for c, q in zip(counts, law))


def word_codes(digits):
    """Byte strings whose entry i encodes the 2- and 3-digit words starting at digit i."""
    x = int.from_bytes(digits, "little")
    size = len(digits) + 1
    return ((2 * x + (x >> 8)).to_bytes(size, "little"),
            (4 * x + 2 * (x >> 8) + (x >> 16)).to_bytes(size, "little"))


DIGCHAR = bytes(48 + (x & 1) for x in range(256))


def digit_parity_split(digits, N, lo, hi):
    """E(-1)^C(n+1), E(-1)^c(n+1) with c the carry from deeper columns, and
    E(-1)^digit(n+1), using digit = C + c mod 2 (N has the parity of C)."""
    length = hi - lo
    dig = bitset(digits[lo + 1 : hi + 1].translate(DIGCHAR))
    col = bitset(N[lo + 1 : hi + 1].translate(ODDCHAR))
    sgn = lambda s: (length - 2 * s.bit_count()) / length
    return sgn(col), sgn(dig ^ col), sgn(dig)


# --------------------------------------------------------------------------
# Independent displacement model (finite-T comparison)
# --------------------------------------------------------------------------

def displaced_model(V, U, lo, hi, rng, guard=64):
    """Resample (V(m), U(m)) i.i.d. from their empirical joint law on [lo, hi)."""
    law = Counter(zip(V[lo:hi], U[lo:hi]))
    keys = list(law)
    cum, run = [], 0
    for key_ in keys:
        run += law[key_]
        cum.append(run)
    sample = rng.choices(keys, cum_weights=cum, k=hi - lo + guard)
    return bytearray(v for v, _ in sample), array("H", [u for _, u in sample])


# --------------------------------------------------------------------------
# Self-tests (small exact checks of the vectorised routines)
# --------------------------------------------------------------------------

def self_tests(V, U, N, C, digits):
    limit = 5000
    brute = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for m in range(d, limit + 1, d):
            brute[m] += 1
    for m in range(1, limit + 1):
        assert brute[m] == U[m] << V[m], m
    direct_n, direct_c = Counter(), Counter()
    for m in range(1, 20100):
        t = m - V[m]
        direct_n[t] += 1
        direct_c[t] += U[m]
    for t in range(1, 20000):
        assert direct_n[t] == N[t] and direct_c[t] == C[t], t
    # E = 1.60669515241529176378330152319...
    lead = int("".join(map(str, digits[1:61])), 2) / 2 ** 60
    assert abs(1 + lead - 1.6066951524152917637833) < 1e-15
    res = packed_residues(C, 1000, 50, 12)
    for i in range(50):
        n = 1000 + i
        assert res[i] == sum(2 ** (12 - d) * C[n + d] for d in range(1, 13)) % 4096
    for n_, q in ((7, 0.3), (12, 0.05), (20, 0.5)):
        exact = sum(abs(x - n_ * q) * exp(lgamma(n_ + 1) - lgamma(x + 1) - lgamma(n_ - x + 1))
                    * q ** x * (1 - q) ** (n_ - x) for x in range(n_ + 1))
        assert abs(exact - binomial_mad(n_, q)) < 1e-12
    # local joint law against integers in a full period (bounded weights)
    w1 = lambda a: 1 / (a + 1)
    w2 = lambda a: 0.5 + 0.5 * (-1) ** a / (a + 2)
    for p, top in ((2, 15), (3, 10)):
        span = p ** top
        vp = lambda m: v2_p(m, p) if m else 99
        for k in (1, p, p * p, 5 * p):
            emp = sum(w1(vp(m)) * w2(vp(m + k)) for m in range(span)) / span
            assert abs(emp - local_joint(p, v2_p(k, p), w1, w2)) < 4 * p ** -top, (p, k)
    for p in (2, 3, 5, 7):
        w1 = lambda a: cexp(0.7j * v2(a + 1)) * (1 + (odd(a + 1) % 4 == 3))
        w2 = lambda a: cexp(-1.9j * v2(a + 1))
        avg = sum((1 - 1 / p) * p ** -kap * local_joint(p, kap, w1, w2) for kap in range(60))
        assert abs(avg - local_single(p, w1) * local_single(p, w2)) < 1e-12
        assert abs(local_joint(p, 0, w1, w2)
                   - (local_single(p, w1) + local_single(p, w2) - 1)) < 1e-12


# --------------------------------------------------------------------------
# Main computation
# --------------------------------------------------------------------------

def lnln(s):
    return log(s * log(2))


COS = []


def model_atoms(cstar, ek, x):
    """(1/Q) sum_i c_*(theta_i) E_k(theta_i) cos(2 pi theta_i x) on a grid of size Q."""
    size = len(cstar)
    return sum(c * e * COS[(i * x) % size] for i, (c, e) in enumerate(zip(cstar, ek))) / size


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--smin", type=int, default=12)
    parser.add_argument("--smax", type=int, default=21)
    parser.add_argument("--seed", type=int, default=20261124)
    parser.add_argument("--model-shells", type=int, nargs="*", default=[18, 21])
    args = parser.parse_args()
    smin, smax = args.smin, args.smax
    shells = list(range(smin, smax + 1))
    top = 1 << (smax + 1)
    last = top + 16                          # digits and columns used: < top + 13
    limit = top + 512
    primes, V, U = valuation_tables(limit)
    tau = array("H", [u << v for u, v in zip(U, V)])
    vmax = max(V)
    digits = binary_digits(tau, last, limit)
    N, C = columns(V, U, 1, last + 1, vmax)
    N = b"\x00" + N
    C = array("H", [0]) + C
    check = last - 200
    zc = weighted_sum(C, 1, check + 1) + (weighted_sum(C, check + 1, last + 1) >> (last - check))
    assert zc == certified_floor(tau, check, limit), "columns disagree with the digits"
    self_tests(V, U, N, C, digits)

    nu = mark_law(primes)
    mu = sum(u * w for u, w in nu.items())
    mu2 = sum(u * u * w for u, w in nu.items())
    nu3 = sum(w for u, w in nu.items() if u % 4 == 3)
    bcol = compound_poisson(nu, 1023)
    p_star, carry_sign, col_sign = model_one_frequency(bcol)
    qlaw = {d: poisson_residue_law(bcol, d) for d in (4, 8, 12)}

    grid = 64
    thetas = [j / grid for j in range(grid)]
    COS[:] = [cos(2 * pi * j / grid) for j in range(grid)]
    tables = euler_tables(primes, thetas)
    ek = {k: euler_factor(k, tables) for k in range(1, 61)}

    print("Erdos-Borwein constant E = sum tau(m) 2^-m: exact shells of shifts [2^s, 2^(s+1)),"
          f" s = {smin}..{smax}")
    print(f"sieve limit {limit}; max V = {vmax}.  Self-checks passed (tau table, columns, digits,")
    print("packed residues, de Moivre, local joint laws, Haar averages, column/digit identity).\n")

    print("== Marked Poisson model (Phase 14 comparison law Q_D) ==")
    print(f"mu = E U_* = {mu:.6f}, E U_*^2 = {mu2:.6f}, nu(1) = {nu[1]:.6f},"
          f" nu(U = 3 mod 4) = {nu3:.6f}")
    print(f"E(-1)^J = {col_sign:.6f} (e^-2 = {exp(-2):.6f}),  E(-1)^carry = {carry_sign:.6f}")
    print(f"p_* = (1 - E(-1)^J E(-1)^carry)/2 = {p_star:.6f}   (certified: [0.492230, 0.492685])")
    assert 0.492230 <= p_star <= 0.492685
    print()

    two_codes, three_codes = word_codes(digits)
    print("== A. Overlapping words at shifts n in [2^s, 2^(s+1)) (digits n+1, n+2, n+3) ==")
    print(" s  T=lnln2^s  f(1)      f(00)    f(01)    f(10)    f(11)    f(000)   f(111)"
          "   max|f(w3)-1/8|")
    rows = {s: {} for s in shells}
    for s in shells:
        lo, hi = 1 << s, 1 << (s + 1)
        length = hi - lo
        ones = digits[lo + 1 : hi + 1].count(1)
        two = [two_codes[lo + 1 : hi + 1].count(bytes([w])) for w in range(4)]
        three = [three_codes[lo + 1 : hi + 1].count(bytes([w])) for w in range(8)]
        if s == 18:
            assert two == [67135, 63695, 63696, 67618], two
        rows[s]["ones"] = ones / length
        dev3 = max(abs(c / length - 0.125) for c in three)
        print(f"{s:2d}  {lnln(s):.4f}   {ones / length:.6f}  "
              + "  ".join(f"{c / length:.5f}" for c in two)
              + f"  {three[0] / length:.5f}  {three[7] / length:.5f}  {dev3:.5f}")
    print(f"marked Poisson model (T = infinity): f(1) = {p_star:.6f}")
    prefix_ones = digits[1 : top + 1].count(1)
    print(f"prefix digits 1..2^{smax + 1}: {prefix_ones} ones, frequency {prefix_ones / top:.6f}")

    def blocks(width):
        # non-overlapping blocks (digits 1..width, width+1..2 width, ...) of the prefix
        count = top // width
        value = 0
        for i in range(width):
            value = 2 * value + int.from_bytes(digits[1 + i : 1 + i + width * count : width], "little")
        raw = value.to_bytes(count + 1, "little")[:count]
        return [raw.count(bytes([c])) / count for c in range(1 << width)]

    crandall = {1: [4359105565638, 4436987456570],
                2: [1080561684345, 1106903007230, 1091079189718, 1119502629811],
                3: [359190664177, 361815499829, 361805068965, 371183479256,
                    361917190569, 368575859354, 370698715770, 376844529482]}
    print("non-overlapping block frequencies, our prefix vs Crandall's 2^43 table"
          " (Integers 12 (2012) A23, Sec. 6):")
    for width in (1, 2, 3):
        ours = blocks(width)
        table = crandall[width]
        theirs = [c / sum(table) for c in table]
        print(f"  base {1 << width}: ours   " + " ".join(f"{x:.5f}" for x in ours))
        print(f"          table  " + " ".join(f"{x:.5f}" for x in theirs))
        print(f"          table with bits complemented " + " ".join(f"{x:.5f}" for x in theirs[::-1]))
    print()

    print("== B. Column at position n+1, n in the shell: N sources, C = sum of odd marks ==")
    print(" s   mean N   EN(N-1)  EN(N-1)(N-2) var N    E(-1)^N  prod(1-2p_v) "
          "Pr(N=0)  mean C   var C")
    print(f"Pois 1        1        1            1        {exp(-2):.5f}  ->e^-2"
          f"        {exp(-1):.5f}  {mu:.4f}   {mu2:.4f}")
    for s in shells:
        lo, hi = 1 << s, 1 << (s + 1)
        hist, n, mean, var, f2, f3, sign = histogram_stats(N[lo + 1 : hi + 1])
        _, _, cmean, cvar, _, _, csign = histogram_stats(C[lo + 1 : hi + 1])
        assert sign == csign
        if s == 18:
            assert sum(j * c for j, c in hist.items()) == 262145 and sign == 14434
        pv, _ = source_law(V, lo + 1, hi + 1)
        bern = 1.0
        for p_ in pv:
            bern *= 1 - 2 * p_
        rows[s].update(pv=pv, sign=sign / n, f2=f2)
        print(f"{s:2d}  {mean:.5f}  {f2:.5f}  {f3:.5f}      {var:.5f}  {sign / n:.5f}  "
              f"{bern:.5f}      {hist[0] / n:.5f}  {cmean:.4f}   {cvar:.4f}")
    print("prod(1-2p_v): value of E(-1)^N if the V(m) were independent with the shell law p_v.")
    print("Law of V over the sources of each shell (the displacement law): mean, variance, sum p_v^2")
    line = ""
    for s in shells:
        pv = rows[s]["pv"]
        mean = sum(v * p_ for v, p_ in enumerate(pv))
        var = sum((v - mean) ** 2 * p_ for v, p_ in enumerate(pv))
        line += f" s={s}: {mean:.3f}/{var:.3f}/{sum(p_ * p_ for p_ in pv):.4f}"
        if s % 4 == 3:
            print(line)
            line = ""
    if line:
        print(line)
    print()

    print("== C. Digit parity split (-1)^digit(n+1) = (-1)^C(n+1) (-1)^carry(n+1) ==")
    print(" s   E(-1)^C   E(-1)^c   E(-1)^dig  product   covariance  f(1)=(1-E(-1)^dig)/2")
    for s in shells:
        lo, hi = 1 << s, 1 << (s + 1)
        ec, ecar, edig = digit_parity_split(digits, N, lo, hi)
        print(f"{s:2d}  {ec:+.5f}  {ecar:+.5f}  {edig:+.5f}   {ec * ecar:+.5f}  "
              f"{edig - ec * ecar:+.5f}    {(1 - edig) / 2:.6f}")
    print(f"Pois {col_sign:+.5f}  {carry_sign:+.5f}  {col_sign * carry_sign:+.5f}   "
          f"{col_sign * carry_sign:+.5f}  +0.00000    {p_star:.6f}")
    print()

    cls = le_bytes(U)[0::2].translate(bytes(64 if x & 3 == 3 else 0 for x in range(256)))
    key = (int.from_bytes(V, "little") + int.from_bytes(cls, "little")).to_bytes(len(V), "little")
    print("== D. Two-source moments M_2(b) = (1/H) #{(m, m'): m != m', t(m) in I, t(m') = t(m) + b} ==")
    print("I = positions [2^s + 1, 2^(s+1)], H = |I|.  ind = 1 - sum_v p_v p_(v+b) (independent")
    print("displacements, the k = 0 hole); loc = local-Euler-factor model; marked: F = G =")
    print("1[U = 3 mod 4], divided by the squared shell share nu_s(3).  Poisson limit: 1.")
    print(" s  hole    b=0: act  ind     loc   | b=1: act  ind     loc   | b=2: act  ind     loc"
          "   | b=3: act  ind     loc   | marked b=0  b=1")
    store = {}
    for s in shells:
        lo, hi = (1 << s) + 1, (1 << (s + 1)) + 1
        H = hi - lo
        pv = rows[s]["pv"]
        vtop = len(pv) - 1
        counts = pair_counts(V, lo, hi, list(range(vtop + 1)), list(range(vtop + 1)))
        assert sum(j * (j - 1) * c for j, c in Counter(N[lo:hi]).items()) == sum(counts[0].values())
        keys3 = [64 + v for v in range(vtop + 1)]
        mcounts = pair_counts(key, lo, hi, keys3, keys3, bmax=1)
        share = (sum(key[lo + v : hi + v].count(64 + v) for v in range(vtop + 1))
                 / sum(V[lo + v : hi + v].count(v) for v in range(vtop + 1)))
        m2 = [sum(counts[b].values()) / H for b in range(4)]
        ind = [1 - sum(pv[v] * pv[v + b] for v in range(vtop + 1 - b)) for b in range(4)]
        cstar = [abs(sum(p_ * cexp(2j * pi * th * v) for v, p_ in enumerate(pv))) ** 2
                 for th in thetas]
        # one period of the theta grid: |k - b| <= 31 (|V(m+k) - V(m)| <= max V here)
        loc = [sum(model_atoms(cstar, ek[abs(k)], k - b) for k in range(b - 31, b + 32) if k)
               for b in range(4)]
        mm = [sum(mcounts[b].values()) / H / share ** 2 for b in range(2)]
        store[s] = (counts, pv, H, cstar)
        print(f"{s:2d}  {1 - ind[0]:.4f}  {m2[0]:.4f}  {ind[0]:.4f}  {loc[0]:.4f} |"
              f" {m2[1]:.4f}  {ind[1]:.4f}  {loc[1]:.4f} | {m2[2]:.4f}  {ind[2]:.4f}  {loc[2]:.4f} |"
              f" {m2[3]:.4f}  {ind[3]:.4f}  {loc[3]:.4f} | {mm[0]:.4f}  {mm[1]:.4f}"
              f"  (nu_s(3) = {share:.4f})")
        rows[s]["m2"] = m2
    print(f"hole = sum_v p_v^2 ~ (4 pi T)^(-1/2) = {1 / sqrt(4 * pi * lnln(smax)):.4f} at s = {smax};"
          f" limit nu(3) = {nu3:.4f}")
    print()

    s = smax
    counts, pv, H, cstar = store[s]
    vtop = len(pv) - 1
    print(f"== E. M_2(b) by source gap k = m' - m on shell s = {s} ==")
    print("P_k(b) = (1/H) #{m: t(m) in I, V(m+k) - V(m) = k - b};  ind_k = sum_v p_v p_(v+k-b);"
          "  loc_k = model")
    print("   k |  b=0: act   ind     loc    act/ind |  b=1: act   ind     loc    act/ind")

    def ind_atom(x):
        return sum(pv[v] * pv[v + x] for v in range(vtop + 1) if 0 <= v + x <= vtop)

    for k in list(range(-6, 0)) + list(range(1, 13)):
        line = f" {k:3d} |"
        for b in range(2):
            act = counts[b].get(k, 0) / H
            ia = ind_atom(k - b)
            la = model_atoms(cstar, ek[abs(k)], k - b)
            line += f"  {act:.5f}  {ia:.5f}  {la:.5f}  {act / ia if ia else 0:.4f} |"
        print(line)
    for b in range(2):
        tot = {par: sum(c for k, c in counts[b].items() if k % 2 == par) / H for par in (0, 1)}
        itot = {par: sum(ind_atom(k - b) for k in range(b - 31, b + 32) if k and k % 2 == par)
                for par in (0, 1)}
        print(f"b = {b}: even k {tot[0]:.5f} (ind {itot[0]:.5f}),  odd k {tot[1]:.5f}"
              f" (ind {itot[1]:.5f})")
    print("By shell: even-k and odd-k parts of M_2(0) and the alternating sum sum_k (-1)^k P_k(0)")
    print("(the theta = 1/2 component), each with its independent-displacement value;"
          " the alternating")
    print("independent value is (sum_v (-1)^v p_v)^2 - sum_v p_v^2.")
    print(" s   even act  ind     odd act   ind     alt act   ind")
    for s2 in shells:
        c2, pv2, H2, _ = store[s2]
        vt = len(pv2) - 1
        atom = lambda x: sum(pv2[v] * pv2[v + x] for v in range(vt + 1) if 0 <= v + x <= vt)
        ev = sum(c for k, c in c2[0].items() if k % 2 == 0) / H2
        od = sum(c for k, c in c2[0].items() if k % 2) / H2
        iev = sum(atom(k) for k in range(-31, 32) if k and k % 2 == 0)
        iod = sum(atom(k) for k in range(-31, 32) if k % 2)
        print(f"{s2:2d}   {ev:.5f}  {iev:.5f}  {od:.5f}  {iod:.5f}  {ev - od:+.5f}  {iev - iod:+.5f}")
    print()

    print("== F. Two-point parity E_m[(-1)^(V(m)+V(m+k))], m in [2^s, 2^(s+1)) ==")
    print(" s   E(-1)^V   square   k=1     k=2     k=3     k=4     k=5     k=6     k=8     k=12")
    half = grid // 2
    for s2 in shells:
        lo, hi = 1 << s2, 1 << (s2 + 1)
        single, corr = parity_correlations(V, lo, hi, 12)
        pick = [corr[i - 1] for i in (1, 2, 3, 4, 5, 6, 8, 12)]
        print(f"{s2:2d}  {single:+.4f}  {single * single:.4f}  "
              + "  ".join(f"{c:+.4f}" for c in pick))
    print("local factor E_k(1/2): " + " ".join(f"k={k}:{ek[k][half]:+.3f}"
                                               for k in (1, 2, 3, 4, 5, 6, 8, 12)))
    print("Kubilius model: E(-1)^(V(m)+V(m+k)) ~ (E(-1)^V)^2 E_k(1/2).")
    print()

    lo, hi = 1 << smax, 1 << (smax + 1)
    law = joint_difference_law(V, lo, hi, 12, vmax)
    pv_m = [V[lo:hi].count(v) / (hi - lo) for v in range(vmax + 1)]
    cm = [abs(sum(p_ * cexp(2j * pi * th * v) for v, p_ in enumerate(pv_m))) ** 2 for th in thetas]
    print(f"== G. Diagonal Pr(V(m+k) = V(m)), m in [2^{smax}, 2^{smax + 1}) ==")
    print(f"independent value sum_v p_v^2 = {sum(p_ * p_ for p_ in pv_m):.5f};"
          f" Gaussian 1/(2 sqrt(pi T)) = {1 / (2 * sqrt(pi * lnln(smax))):.5f}")
    print("   k   actual   local model   ratio")
    for k in range(1, 13):
        act = law[k].get(0, 0.0)
        loc = model_atoms(cm, ek[k], 0)
        print(f" {k:3d}  {act:.5f}  {loc:.5f}       {act / loc:.4f}")
    print()

    print("== H. Total variation between packed residues R_D(n) and Q_D, n in the shell ==")
    print(" s    D=4: TV   floor   | D=8: TV   floor   | D=12: TV  floor")
    residues = {}
    for s2 in shells:
        lo, hi = 1 << s2, 1 << (s2 + 1)
        length = hi - lo
        res = packed_residues(C, lo - 8, length + 8, 12)
        out = []
        base_hist = Counter(res[8 : 8 + length])
        residues[s2] = (res, base_hist)
        for d, offset in ((4, 0), (8, 4), (12, 8)):
            # R_d(n) = R_12(n - (12 - d)) mod 2^d; res[j] = R_12(lo - 8 + j); the window
            # res[offset : offset + length] differs from res[8 : 8 + length] at its ends only
            hist = Counter(base_hist)
            for x_ in res[offset:8]:
                hist[x_] += 1
            for x_ in res[offset + length : 8 + length]:
                hist[x_] -= 1
            counts_d = fold(hist, d)
            out.append((total_variation(counts_d, length, qlaw[d]), tv_floor(length, qlaw[d])))
        rows[s2]["tv"] = out
        print(f"{s2:2d}   " + " | ".join(f"{tv:.5f}  {fl:.5f}" for tv, fl in out))
    print("floor = expected TV of an i.i.d. sample of the same size drawn from Q_D itself")
    print()

    rng = random.Random(args.seed)
    print("== I. Independent displacement model: (V(m), U(m)) resampled i.i.d. from each"
          " shell's joint law ==")
    print(" s   path     f(1)      EN(N-1)  E(-1)^N  M2(1)    TV(R8,Q8) TV(R12,Q12)"
          "  TV(R12 actual, R12 model)")
    for s2 in args.model_shells:
        if s2 not in shells:
            continue
        lo, hi = 1 << s2, 1 << (s2 + 1)
        length = hi - lo
        Vm, Um = displaced_model(V, U, lo, hi, rng)
        span = len(Vm) - 40
        Nm, Cm = columns(Vm, Um, 0, span, max(Vm))
        x = weighted_sum(Cm, 1, span)
        text = format(x & ((1 << (span - 1)) - 1), "b").zfill(span - 1)
        mdig = b"\x00" + text.encode().translate(ASCII01)
        _, nm, _, _, f2m, _, signm = histogram_stats(Nm[1 : length + 1])
        vt = max(Vm)
        cm_pairs = pair_counts(Vm, 1, length + 1, list(range(vt + 1)), list(range(vt + 1)), bmax=1)
        resm = packed_residues(Cm, 0, length + 8, 12)
        tv8 = total_variation(fold(Counter(resm[4 : 4 + length]), 8), length, qlaw[8])
        m12 = fold(Counter(resm[8 : 8 + length]), 12)
        tv12 = total_variation(m12, length, qlaw[12])
        a12 = fold(residues[s2][1], 12)
        tvam = 0.5 * sum(abs(a - b) for a, b in zip(a12, m12)) / length
        r = rows[s2]
        print(f"{s2:2d}  actual   {r['ones']:.6f}  {r['f2']:.5f}  {r['sign']:+.5f}  "
              f"{r['m2'][1]:.5f}  {r['tv'][1][0]:.5f}   {r['tv'][2][0]:.5f}")
        print(f"{s2:2d}  model    {mdig[1 : length + 1].count(1) / length:.6f}  {f2m:.5f}  "
              f"{signm / nm:+.5f}  {sum(cm_pairs[1].values()) / length:.5f}  {tv8:.5f}   "
              f"{tv12:.5f}    {tvam:.5f}  (two-sample floor ~ "
              f"{sqrt(2) * tv_floor(length, qlaw[12]):.5f})")
    print()

    print("== J. Local Euler factor of the two-point law of V(m+k) - V(m) ==")
    print("R_p(theta; kappa) = E_p^joint / |phi_p(theta)|^2 with kappa = v_p(k)."
          "  The Haar average over k is 1 exactly.")
    for th in (0.5, 0.25, 1 / 32):
        f_minus = lambda a, th=th: cexp(-2j * pi * th * v2(a + 1))
        f_plus = lambda a, th=th: cexp(2j * pi * th * v2(a + 1))
        phi = local_single(2, f_plus)
        vals = [local_joint(2, kap, f_minus, f_plus).real / abs(phi) ** 2 for kap in range(5)]
        avg = sum(0.5 ** (kap + 1) * local_joint(2, kap, f_minus, f_plus).real
                  for kap in range(60)) / abs(phi) ** 2
        print(f"theta = {th:.5f}: p = 2, kappa = 0..4: " + " ".join(f"{x:+.5f}" for x in vals)
              + f"   Haar average {avg:.12f}")
    for j in (32, 16, 2):
        vals = [ek[k][j] for k in range(1, 13)]
        mean = sum(euler_factor(k, tables)[j] for k in range(1, 4097)) / 4096
        print(f"theta = {thetas[j]:.5f}: E_k for k = 1..12: " + " ".join(f"{x:+.3f}" for x in vals)
              + f";  mean over k <= 4096: {mean:.4f}")
    covs = [(ek[k][1] - 1) / (4 * pi * pi * thetas[1] ** 2) for k in range(1, 13)]
    print("model Cov(V(m), V(m+k)) read from E_k(1/64) = 1 + 4 pi^2 theta^2 Cov + O(theta^4),"
          " k = 1..12:")
    print("  " + " ".join(f"{c:+.3f}" for c in covs))
    print()

    # persistent mark factor: F = 1[U = 3 mod 4] = (1 - chi(U))/2, chi the character mod 4
    chi = lambda a: 1.0 if odd(a + 1) % 4 == 1 else -1.0
    xs = 1.0
    small = [p for p in primes if p <= 2000]
    for p in small:
        xs *= local_single(p, chi)
    joint0 = {p: local_joint(p, 0, chi, chi) for p in small}
    ybase = 1.0
    for p in small:
        ybase *= joint0[p]
    cache = {}

    def mark_model(k):
        y = ybase
        for p in small:
            if k % p == 0:
                kap = v2_p(k, p)
                if (p, kap) not in cache:
                    cache[p, kap] = local_joint(p, kap, chi, chi) / joint0[p]
                y *= cache[p, kap]
        return (1 - 2 * xs + y) / (1 - xs) ** 2
    lo, hi = 1 << smax, 1 << (smax + 1)
    fbits = bitset(le_bytes(U)[2 * lo : 2 * (hi + 12) : 2].translate(
        bytes(49 if x & 3 == 3 else 48 for x in range(256))))
    length = hi - lo
    fmask = (1 << length) - 1
    share = (fbits & fmask).bit_count() / length
    print(f"== K. Mark factor E[F(U(m)) F(U(m+k))] / nu(F)^2, F = 1[U = 3 mod 4], m in [2^{smax},"
          f" 2^{smax + 1}) ==")
    print("   k   actual (shell share)   local model   (theta = 0 factor; persists pointwise in k)")
    for k in range(1, 13):
        act = (fbits & (fbits >> k) & fmask).bit_count() / length / share ** 2
        print(f" {k:3d}   {act:.4f}                {mark_model(k):.4f}")
    print(f"mean of the local model over k <= 2048: "
          f"{sum(mark_model(k) for k in range(1, 2049)) / 2048:.4f}; Haar average 1")
    print()

    # Kubilius local-factor model at large T: Poisson(T) displacements, local factors E_k
    print("== L. Local-factor model with Poisson(T) displacements: M_2(b) = sum_k P_k(b) as T grows ==")
    print("c_T(theta) = exp(-2T(1 - cos 2 pi theta)) is the decoupled characteristic function;"
          " hole = Pr(D_* = 0) = e^(-2T) I_0(2T)")
    big = 256
    thetas_b = [j / big for j in range(big)]
    tables_b = euler_tables(primes, thetas_b, pmax=500, pratio=128, kcap=256)
    ek_b = {k: euler_factor(k, tables_b) for k in range(1, 131)}
    cos_b = [cos(2 * pi * j / big) for j in range(big)]
    print("   T      hole     M2(0)    M2(1)    M2(2)    even-k share of M2(0)")
    for T in (2.68, 3.37, 5.0, 10.0, 20.0, 40.0):
        ct = [exp(-2 * T * (1 - cos(2 * pi * th))) for th in thetas_b]
        def atom(k, x):
            e = ek_b[abs(k)] if k else [1.0] * big
            return sum(c * f * cos_b[(i * x) % big] for i, (c, f) in enumerate(zip(ct, e))) / big
        hole = atom(0, 0)
        vals = [sum(atom(k, k - b) for k in range(b - 127, b + 128) if k) for b in range(3)]
        even = sum(atom(k, k) for k in range(-127, 128) if k and k % 2 == 0)
        print(f" {T:5.2f}   {hole:.4f}   {vals[0]:.4f}   {vals[1]:.4f}   {vals[2]:.4f}   "
              f"{even / vals[0]:.4f}")
    print("T = 2.68 and 3.37 are s = 21 and s = 43; the model tends to the Poisson value 1 at rate"
          " T^(-1/2).")


if __name__ == "__main__":
    main()
