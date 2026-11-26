#!/usr/bin/env python3
"""Independent floating-point and exact cross-checks for the Erdos-Borwein note.

This script does NOT reuse scripts/phase17_erdos_borwein_bias.py.  It recomputes, by
different routes, headline numbers of the note.  It is a cross-check, not a certificate:
sections 1-3 use IEEE doubles (numpy), sections 4-5 use exact fractions.

  1  mu = E U_*, from the per-prime Euler product (primes up to 2e5, tail neglected)
  2  mark law nu (marks <= 511), column law J, law R_16 of 16 packed columns (FFT),
     E[Psi_16(R_16)] and the top-bit probability
  3  p_* and E(-1)^{c_1} by a direct carry recursion over 80 columns
  4  exact: primal laws L_r and parity e_r (r odd), rho_3, rho_4 of Theorem 7.4(a),
     and the Bonferroni excess of Theorem 7.5 for K <= 360
  5  majorant property of the Selberg-Vaaler polynomial of degree N on a 2^18 grid

Run (under a minute):  python -B crosscheck.py
Requires numpy.  Expected output is quoted in VERIFICATION.md.
"""
import math
from fractions import Fraction as Fr
from math import comb, factorial

import numpy as np


def primes_upto(n):
    s = np.ones(n + 1, bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def odd(n):
    while n % 2 == 0:
        n //= 2
    return n


# ---------------------------------------------------------------- 1, 2
MARK = 511
P = primes_upto(200000)
nu = np.zeros(MARK + 1)
nu[1] = 1.0
mu = 1.0
for p in P:
    p = int(p)
    dist, a = {}, 0
    while True:
        pr = (1 - 1 / p) * p ** (-a)
        if pr < 1e-18:
            break
        o = odd(a + 1)
        dist[o] = dist.get(o, 0) + pr
        a += 1
    mu *= sum(o * q for o, q in dist.items())
    if p <= 4096:
        new = np.zeros(MARK + 1)
        for o, q in dist.items():
            if o == 1:
                new += q * nu
            else:
                for u in range(1, MARK // o + 1, 2):
                    if nu[u]:
                        new[u * o] += q * nu[u]
        nu = new
# crude lump for primes in (4096, 2e5]: only exponent 2 matters (mark 3)
lump = sum((1 - 1 / int(p)) * int(p) ** -2 for p in P if p > 4096)
new = nu * (1 - lump)
for u in range(1, MARK // 3 + 1, 2):
    new[3 * u] += lump * nu[u]
nu = new
print("1. mu (Euler product, primes <= 2e5):", round(mu, 7), " (certified enclosure [2.0762592, 2.0763285];",
      "primes > 2e5 add about 1e-6)")
assert 2.07625 < mu < 2.07633

JM = 1500
b = np.zeros(JM + 1)
b[0] = math.exp(-1)
for j in range(1, JM + 1):
    b[j] = sum(u * nu[u] * b[j - u] for u in range(1, min(j, MARK) + 1, 2)) / j
print("2. column law mass", b.sum(), " P(J even)", b[0::2].sum(), " (1+e^-2)/2 =", (1 + math.exp(-2)) / 2)

D = 16
M = 1 << D
F = np.ones(M, complex)
for d in range(1, D + 1):
    v = np.zeros(M)
    mult = 1 << (D - d)
    for j in range(JM + 1):
        v[(j * mult) % M] += b[j]
    F *= np.fft.fft(v)
R = np.real(np.fft.ifft(F))
R[R < 0] = 0
half = M // 2
Psi = np.zeros(M)
Psi[half:] = 1
for k in range(1, 557):
    Psi[half - k] = 1 - k / 557
EPsi = float((R * Psi).sum())
print("   E_Q16[Psi_16] (float) =", round(EPsi, 7), " (certified upper bound 0.4960081);",
      "top-bit prob", round(float(R[half:].sum()), 7))
print("   with mu/557 (mu = 2.0763285):", round(EPsi + 2.0763285 / 557, 7), "< 1/2")
assert 0.49598 < EPsi < 0.49601

# ---------------------------------------------------------------- 3
S = JM + 10
st = np.zeros(S + 1)
st[0] = 1.0
for d in range(80, 1, -1):
    new = np.zeros(S + 1)
    for s in range(S + 1):
        if st[s] == 0:
            continue
        base = s // 2
        lim = min(JM, S - base)
        new[base:base + lim + 1] += st[s] * b[:lim + 1]
    st = new
c1 = np.zeros(S + 1)
for s in range(S + 1):
    c1[s // 2] += st[s]
eneg = float(sum(c1[c] * (-1) ** c for c in range(S + 1)))
pstar = 0.5 - 0.5 * math.exp(-2) * eneg
print("3. E(-1)^{c_1} =", round(eneg, 6), " (certified [0.111481733, 0.111502881]);",
      "p_* =", round(pstar, 6), " (certified [0.492450290, 0.492460864])")
assert 0.4924 < pstar < 0.4925


# ---------------------------------------------------------------- 4
def ff(n, k):
    r = 1
    for i in range(k):
        r *= n - i
    return r


def law_L(r):
    return {n: Fr(1, factorial(n)) * sum(Fr((-1) ** j, factorial(j)) for j in range(r - n + 1))
            for n in range(r + 1)}


def check(law, r):
    assert sum(law.values()) == 1 and all(v >= 0 for v in law.values())
    for k in range(1, r + 1):
        assert sum(v * ff(n, k) for n, v in law.items()) == 1, k


def par(law):
    return sum(v * (-1) ** n for n, v in law.items())


def e_r(r):
    return sum(Fr((-2) ** k, factorial(k)) for k in range(r + 1))


print("4. parity Bonferroni (Theorem 7.1): r, e_r, parity of primal law")
for r in (1, 3, 5, 7, 9, 11):
    L = law_L(r)
    check(L, r)
    assert par(L) == e_r(r)
    # dual inequality q_r(n) <= (-1)^n on a range, equality on 0..r
    for n in range(300):
        q = sum((-2) ** k * comb(n, k) for k in range(r + 1))
        assert q <= (-1) ** n and (q == (-1) ** n or n > r)
    print("  ", r, e_r(r))
rho3 = {0: Fr(13, 36), 1: Fr(19, 48), 2: Fr(5, 36), 3: Fr(7, 72), 5: Fr(1, 144)}
check(rho3, 3)
assert par(rho3) == 0
support = [0, 1, 2, 3, 12]
mat = [[Fr(ff(n, k)) if k else Fr(1) for n in support] for k in range(5)]
aug = [row[:] + [Fr(1)] for row in mat]
for c in range(5):
    piv = next(i for i in range(c, 5) if aug[i][c] != 0)
    aug[c], aug[piv] = aug[piv], aug[c]
    aug[c] = [x / aug[c][c] for x in aug[c]]
    for i in range(5):
        if i != c:
            aug[i] = [x - aug[i][c] * y for x, y in zip(aug[i], aug[c])]
L412 = {n: aug[i][5] for i, n in enumerate(support)}
assert L412 == {0: Fr(25, 72), 1: Fr(5, 11), 2: Fr(1, 20), 3: Fr(4, 27), 12: Fr(1, 11880)}
check(L412, 4)
assert par(L412) == Fr(-61, 297)
rho4 = {n: Fr(99, 404) * L412.get(n, 0) + Fr(305, 404) * law_L(5).get(n, 0)
        for n in set(L412) | set(law_L(5))}
check(rho4, 4)
assert par(rho4) == 0
print("   rho_3 (orders <= 3) and rho_4 (orders <= 4): exact parity 0; L^(12) parity -61/297")

tot = 0.0
for K in range(92, 361):
    pk = math.exp(-16 + K * math.log(16) - math.lgamma(K + 1))
    s = 0
    for j in range(92):
        t = 92 - j
        t -= t % 2
        if K - j - 1 >= t:
            s += comb(K, j) * comb(K - j - 1, t)
    tot += pk * s
excess = tot + 16.0 ** 92 / math.factorial(92)
print("   Bonferroni excess (K <= 360) =", round(excess, 9), " (note: <= 1.197e-4 including the tail beyond K = 360)")
assert 1.19e-4 < excess < 1.2e-4


# ---------------------------------------------------------------- 5
def coeffs(N):
    c = np.zeros(N + 1, complex)
    c[0] = 0.5 + 1 / (N + 1)
    for m in range(1, N + 1):
        if m % 2:
            u = m / (N + 1)
            c[m] = 1j / (np.pi * m) * (np.pi * u * (1 - u) / np.tan(np.pi * u) + u)
        else:
            c[m] = (1 - m / (N + 1)) / (N + 1)
    return c


def Sval(N, x):
    c = coeffs(N)
    out = np.full_like(x, c[0].real)
    for m in range(1, N + 1):
        out += 2 * np.real(c[m] * np.exp(2j * np.pi * m * x))
    return out


G = 1 << 18
x = (np.arange(G) + 0.5) / G
ind = ((x >= 0.5) & (x < 1)).astype(float)
for N in (31, 110, 116):
    mn = float((Sval(N, x) - ind).min())
    print("5. degree %3d: min over grid of (S - indicator) = %.3e" % (N, mn))
    assert mn > -1e-9
print("all cross-checks passed")
