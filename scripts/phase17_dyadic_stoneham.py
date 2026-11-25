"""Phase 17, Track A: dyadic Stoneham classification. Standard library only.

Run `python -B scripts/phase17_dyadic_stoneham.py` from the repository root
(about 40 seconds). Options:

  --degree-128      rerun the branch-and-bound certificate for M_128 on [1, 2)
                    at its sharp precision 907 (about 40 more seconds)
  --middle-max A    certify the middle automaton states (a, n), 1 <= n <= a - 2,
                    for a <= A (default 32; A = 64 takes about two minutes)
  --emit-lean       print the minimized F_31 certificate for the pair (3, 31)
                    as Lean 4 data (a format sketch, not compiled here)

Every exact claim of notes/phase17/dyadic-stoneham-classification.md is checked
here with assertions, using exact integer and rational arithmetic only; the few
observations the note labels exploratory are not rerun.

Part A1 treats the leading mass M_d(t) = sum 2^(v_1 + ... + v_d) over v in N^d
with sum 2^(-v_i) <= t (a 2-adically convergent sum that is an integer). It
checks the proof of the least-orbit-order theorem F(d) = sum_{k<=d} floor(log2 k)
(and its version for every Kraft budget 2^a), the exact list of minimizing orbits,
the location of the least loss, the zero-freeness of the middle automaton states,
the top-state formula, the parity lemma for odd twists, the second-order (mod p^2)
cyclic descent and explicit witnesses of its failure, nine new good descent pairs,
minimized F_p certificates and the degree-128 certificate.

Part A2 treats the resonant quadratics. It checks the closed form of the plateau
cycle point for X^2 - 2X, the exact cycle discrepancies for denominator 1, and the
finite classification of admissible plateau cycles that gives unconditional bounds
limsup D_N < 1/4 for explicit (b, C_0, D).

Part A3 checks the pivot-degree criterion for joint normality on examples.
"""

import argparse
import random
import sys
import time
from fractions import Fraction
from functools import lru_cache
from math import comb, gcd, log2

sys.setrecursionlimit(100000)


def order(x):
    """2-adic order of a nonzero integer."""
    if x == 0:
        raise ArithmeticError("zero has infinite order")
    return (x & -x).bit_length() - 1


def s2(n):
    return bin(n).count("1")


def v2_factorial(n):
    return n - s2(n)


def heap_sum(d):
    """G(d) = sum_{k=1}^d floor(log2 k)."""
    return sum(k.bit_length() - 1 for k in range(1, d + 1))


def is_prime(n):
    if n < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):   # deterministic below 3.3e24
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


def mult_order(x, n):
    if n == 1:
        return 1
    k, y = 1, x % n
    while y != 1:
        y, k = y * x % n, k + 1
    return k


# =====================================================================================
# Exact masses, twisted masses and the digit automaton
# =====================================================================================

@lru_cache(maxsize=None)
def mass(d, t):
    """Exact integer M_d(t) for a dyadic (Fraction) cut t, by the zero-count recurrence."""
    if d == 0:
        return int(t >= 0)
    if t <= 0:
        return 0
    if t >= d:
        return (-1) ** d
    return sum(comb(d, m) * 2 ** (d - m) * mass(d - m, 2 * (t - m)) for m in range(min(d, int(t)) + 1))


class TwistedMass:
    """M^(z)_d(t) = K_{U_t}(z)/(1-z)^d, either exactly (N=None, Fractions) or modulo N."""

    def __init__(self, z, N=None):
        self.z, self.N = z, N
        self.inv = Fraction(1, 1 - z) if N is None else pow((1 - z) % N, -1, N)
        self.cache = {}

    def __call__(self, d, t):
        key = (d, t)
        if key in self.cache:
            return self.cache[key]
        N, z = self.N, self.z
        if d == 0:
            r = int(t >= 0)
        elif t <= 0:
            r = 0
        elif t >= d:
            r = self.inv ** d if N is None else pow(self.inv, d, N)
        else:
            r = sum(comb(d, m) * (z ** (d - m) if N is None else pow(z, d - m, N)) * self(d - m, 2 * (t - m))
                    for m in range(min(d, int(t)) + 1))
            if N is not None:
                r %= N
        self.cache[key] = r
        return r


class Automaton:
    """Linear representation of M_d. State (a, n), 1 <= a <= d, 0 <= n < a, stands for
    M_a(n + f) with f in [0, 1). Reading the next binary digit c of f = (c + f')/2,
        M_a(n + f) = sum_{m <= n} C(a, m) z^(a-m) M_{a-m}(2(n - m) + c + f'),
    and a target with 2(n - m) + c >= a - m is absorbed with value (1-z)^-(a-m).
    For z = 2 and N = None this is the exact Phase 16 automaton; with a modulus N it
    computes the twisted mass modulo N."""

    def __init__(self, d, z=2, N=None):
        self.d, self.N = d, N
        self.states = [(a, n) for a in range(1, d + 1) for n in range(a)]
        self.index = {s: i for i, s in enumerate(self.states)}
        self.gap = [a - n for a, n in self.states]
        if N is None:
            assert z == 2
            absorbed = lambda a: (-1) ** a
        else:
            inv = pow((1 - z) % N, -1, N)
            absorbed = lambda a: pow(inv, a, N)
        self.T = ([], [])
        for (a, n) in self.states:
            for c in (0, 1):
                out = []
                for m in range(n + 1):
                    w = comb(a, m) * z ** (a - m)
                    if N:
                        w %= N
                    a2, n2 = a - m, 2 * (n - m) + c
                    if n2 >= a2:
                        ww = w * absorbed(a2)
                        out.append((-1, ww % N if N else ww))
                    else:
                        out.append((self.index[(a2, n2)], w))
                self.T[c].append(out)
        if N is None:
            self.V = [mass(a, Fraction(n)) for (a, n) in self.states]
        else:
            tm = TwistedMass(z, N)
            self.V = [tm(a, Fraction(n)) for (a, n) in self.states]

    def step(self, row, absorbed, c, mod=None):
        new, ab = {}, absorbed
        for i, x in row.items():
            for j, w in self.T[c][i]:
                if j < 0:
                    ab += x * w
                else:
                    new[j] = new.get(j, 0) + x * w
        if mod:
            new = {j: y % mod for j, y in new.items() if y % mod}
            ab %= mod
        return new, ab

    def evaluate(self, start, bits, mod=None):
        row, ab = {self.index[start]: 1}, 0
        for c in bits:
            row, ab = self.step(row, ab, c, mod)
        val = ab + sum(x * self.V[i] for i, x in row.items())
        return val % mod if mod else val


def branch_and_bound(A, a, n, L):
    """Partition [n, n+1) into dyadic intervals on which v_2(M_a) is constant, for the
    state (a, n) of the exact automaton A. A leaf (f, depth, v) with v = L means a
    residue 0 modulo 2^L. Completions of a prefix change the value by multiples of
    2^nu (all live transition weights are divisible by 2^(a'-n')); a prefix of f with
    a - s_2(n) one-bits is its own truncation (binary weight of a sum of a powers of 2)."""
    mod = 1 << L
    V = [v % mod for v in A.V]
    cap = a - s2(n)
    leaves, nodes = [], 0
    stack = [({A.index[(a, n)]: 1}, 0, 0, 0, 0)]
    while stack:
        row, absorbed, depth, num, ones = stack.pop()
        nodes += 1
        val = (absorbed + sum(x * V[i] for i, x in row.items())) % mod
        vv = order(val) if val else L
        nu = min((order(x) + A.gap[i] for i, x in row.items()), default=L)
        if vv < nu or nu >= L or ones == cap:
            leaves.append((Fraction(num, 1 << depth), depth, vv))
            continue
        for c in (0, 1):
            new, ab = A.step(row, absorbed, c, mod)
            stack.append((new, ab, depth + 1, 2 * num + c, ones + c))
    leaves.sort()
    x = Fraction(0)
    for f, depth, _ in leaves:
        assert f == x
        x += Fraction(1, 1 << depth)
    assert x == 1
    return leaves, nodes


def bits_of(f, L):
    """First L binary digits of f in [0, 1) (f dyadic with at most L digits)."""
    out = []
    for _ in range(L):
        f *= 2
        out.append(int(f >= 1))
        f -= out[-1]
    assert f == 0
    return out


# =====================================================================================
# A1.1 Least orbit order: F(d) = sum floor(log2 k), every Kraft budget 2^a, minimizers
# =====================================================================================

def phi(c):
    """Phi(c) = sum_i (i c_i - v_2(c_i!)) for a multiset given as {level: multiplicity}."""
    return sum(i * ci - v2_factorial(ci) for i, ci in c.items())


def kraft(c):
    return sum(Fraction(ci, 2 ** i) for i, ci in c.items())


def slack_terms(c, a=1):
    """The terms sigma_D and S_D of the proof, D = 0..I-1, for Kraft(c) < 2^a."""
    d = sum(c.values())
    top = max(c)
    sig, S = [], []
    for D in range(top):
        N = sum(ci for i, ci in c.items() if i <= D)
        A = sum(ci << (D - i) for i, ci in c.items() if i <= D)
        SD = sum(ci >> (i - D) for i, ci in c.items() if i > D)
        assert d - N >= SD                         # first half of sigma_D >= S_D
        assert (1 << (D + a)) - 1 - A >= SD         # second half, from Kraft < 2^a
        sig.append(min(d - N, (1 << (D + a)) - 1 - N))
        S.append(SD)
    return sig, S


def least_bound(d, a):
    """Closed form of min Phi over multisets of size d with Kraft sum < 2^a."""
    return (sum(max(0, k.bit_length() - a) for k in range(1, d + 1))
            - sum(min(d >> k, (1 << (a - k)) - 1) for k in range(1, a)))


@lru_cache(maxsize=None)
def min_phi(d, n):
    """DP: min Phi over multisets of size d (levels >= 0) with Kraft sum < n."""
    if d == 0:
        return 0
    if n > d:
        return -v2_factorial(d)
    return min((d - m) - v2_factorial(m) + min_phi(d - m, 2 * (n - m)) for m in range(min(d, n - 1) + 1))


def all_minimizers(d, n, level=0):
    """Every multiset (as a tuple of (level, count)) attaining min_phi(d, n)."""
    if d == 0:
        return [()]
    best, out = min_phi(d, n), []
    for m in range(min(d, n - 1) + 1):
        if m == d:
            if -v2_factorial(d) == best:
                out.append(((level, d),))
            continue
        if (d - m) - v2_factorial(m) + min_phi(d - m, 2 * (n - m)) == best:
            for rest in all_minimizers(d - m, 2 * (n - m), level + 1):
                out.append((((level, m),) if m else ()) + rest)
    return out


def predicted_minimizers(d):
    """Theorem 1(ii): for 2^r - 1 <= d <= 2^(r+1) - 2 and j = d - 2^r + 1, the
    minimizers of Phi under Kraft < 2 are {(r-1)^(2^r-1-j), r^(2j)} and
    {(r-1)^(2^r-j), r^(2j-1)} (j >= 1), or {(r-1)^d} (j = 0)."""
    r = (d + 1).bit_length() - 1
    j = d - (2 ** r - 1)
    if j == 0:
        return {((r - 1, d),)}
    lo = ((r - 1, 2 ** r - 1 - j), (r, 2 * j)) if 2 ** r - 1 - j else ((r, 2 * j),)
    hi = ((r - 1, 2 ** r - j), (r, 2 * j - 1))
    return {lo, hi}


def check_least_orbit_order(dmax_dp=300, dmax_a=150):
    rng = random.Random(17)
    # (1) The slack identity Phi(c) - G(d) = sum_D (sigma_D - S_D), every term >= 0.
    tested = 0
    for _ in range(3000):
        c, used = {}, Fraction(0)
        for i in range(rng.randint(1, 10)):
            room = (2 - used) * 2 ** i            # c_i 2^-i < 2 - used
            top = int(room) - (1 if room == int(room) else 0)
            ci = rng.randint(0, max(0, top)) if rng.random() < 0.8 else rng.randint(0, max(0, top) // 3)
            if ci:
                c[i] = ci
                used += Fraction(ci, 2 ** i)
        if not c:
            continue
        assert kraft(c) < 2
        d = sum(c.values())
        sig, S = slack_terms(c)
        assert all(x >= y for x, y in zip(sig, S))
        assert sum(S) == sum(v2_factorial(ci) for ci in c.values())   # Legendre, c_j < 2^(j+1)
        assert phi(c) - heap_sum(d) == sum(x - y for x, y in zip(sig, S))
        tested += 1
    # (2) The DP minimum equals G(d), and the minimizers are exactly the predicted orbits.
    for d in range(1, dmax_dp + 1):
        assert min_phi(d, 2) == heap_sum(d)
        assert set(all_minimizers(d, 2)) == predicted_minimizers(d), d
        for orb in predicted_minimizers(d):
            c = dict(orb)
            assert phi(c) == heap_sum(d) and kraft(c) < 2
    # (3) Every budget 2^a: lower bound (proof) and construction, against the DP.
    for a in range(0, 8):
        for d in range(0, dmax_a + 1):
            assert min_phi(d, 2 ** a) == least_bound(d, a), (a, d)
            if d >= 2 ** a:
                I = next(I for I in range(1, 40) if 2 ** (I + a - 1) <= d <= 2 ** (I + a) - 1)
                M = 2 ** (I + a - 1) - 1
                yp_eps = d - M                    # = floor(y/2) + (y mod 2)
                for y in (2 * yp_eps - 1, 2 * yp_eps):
                    x = M - y // 2
                    if y >= 1 and x >= 0 and x + y == d:
                        c = {I - 1: x, I: y} if x else {I: y}
                        assert kraft(c) < 2 ** a and phi(c) == least_bound(d, a), (a, d)
    return tested


def check_least_loss_location(dmax=40):
    """Corollary 2: v_2(M_d) = v_2(d!) + G(d) exactly on [2 - 2^(1-r), 2 - 2^(-r))
    (on [2 - 2^(1-r), 2) for d = 2^r - 1), and is larger elsewhere."""
    count = 0
    for d in range(3, dmax + 1):                  # d >= 3, so r >= 2 and every point lies in [1, 2)
        r = (d + 1).bit_length() - 1
        j = d - (2 ** r - 1)
        V = v2_factorial(d) + heap_sum(d)
        lo = 2 - Fraction(1, 2 ** (r - 1))
        hi = 2 - Fraction(1, 2 ** r)
        inside = [lo, lo + Fraction(1, 2 ** (r + 3)), hi - Fraction(1, 2 ** (r + 6))]
        for t in inside:
            assert order(mass(d, t)) == V
        assert order(mass(d, lo - Fraction(1, 2 ** (r + 4)))) > V
        if j >= 1:
            assert order(mass(d, hi)) > V
            assert order(mass(d, hi + Fraction(1, 2 ** (r + 3)))) > V
        else:
            assert order(mass(d, hi)) == V
        count += 1
    return count


# =====================================================================================
# A1.2 Automaton states: top-state formula, middle-state certificates
# =====================================================================================

def top_state_value(a, f):
    """M_a(a - 1 + f) = (-1)^a - 1 - a(2^(W+1) - 2) for f in [2^(-W-1), 2^(-W)), and
    (-1)^a - 1 + 2a at f = 0."""
    if f == 0:
        return (-1) ** a - 1 + 2 * a
    W = 0
    while f < Fraction(1, 2 ** (W + 1)):
        W += 1
    return (-1) ** a - 1 - a * (2 ** (W + 1) - 2)


def check_top_state():
    rng = random.Random(2)
    for a in range(1, 13):
        for _ in range(60):
            f = Fraction(rng.randrange(0, 1 << 12), 1 << 12)
            assert mass(a, a - 1 + f) == top_state_value(a, f)
        # zero exactly on [a - 1/2, a) for even a, never for odd a
        for k in range(1, 12):
            f = Fraction(1, 2 ** k)
            v = top_state_value(a, f)
            assert (v == 0) == (a % 2 == 0 and k == 1)
        assert top_state_value(a, Fraction(0)) != 0 or a == 1     # M_1(0) = 0 trivially


def certify_middle_states(amax):
    """Every middle state (a, n), 3 <= a <= amax, 1 <= n <= a - 2, has no zero residue
    on [n, n + 1) at precision L (hence no zero cell). Returns the largest loss seen."""
    worst = {}
    for a in range(3, amax + 1):
        A = Automaton(a)
        L = int(a * log2(a) * 1.6) + 30
        for n in range(1, a - 1):
            leaves, _ = branch_and_bound(A, a, n, L)
            mx = max(v for _, _, v in leaves)
            assert mx < L, (a, n)
            worst[(a, n)] = mx
    return worst


# =====================================================================================
# A1.3 Parity of odd twists and the mod-3 reformulation
# =====================================================================================

def cuts(d, depth):
    """All dyadic cuts in [1, 2) with at most d one-bits, positions <= depth."""
    out = []

    def rec(pos, val, ones):
        out.append(val)
        if ones == d:
            return
        for q in range(pos, depth + 1):
            rec(q + 1, val + Fraction(1, 2 ** q), ones + 1)
    rec(1, Fraction(1), 1)
    return out


def check_parity_and_mod3(dmax=7, depth=8):
    """K_U(z) = (1-z)^d M^(z)_d is an odd integer for every odd z (K_U(1) = 1), and
    M_d(t) = (-1)^d K_U(-1) mod 3. Returns the degrees with a mod-3 zero."""
    mod3_zero = {}
    for d in range(2, dmax + 1):
        tm_m1, tm_3 = TwistedMass(-1), TwistedMass(3)
        zero_here = None
        for t in cuts(d, depth):
            K = tm_m1(d, t) * 2 ** d
            assert K.denominator == 1 and K.numerator % 2 == 1
            K3 = tm_3(d, t) * (-2) ** d
            assert K3.denominator == 1 and K3.numerator % 2 == 1
            assert (mass(d, t) - (-1) ** d * K.numerator) % 3 == 0
            if K.numerator % 3 == 0 and zero_here is None:
                zero_here = t
        mod3_zero[d] = zero_here
    return mod3_zero


# =====================================================================================
# A1.4 Second-order cyclic descent modulo p^2
# =====================================================================================

def normalize(x):
    """(y, j) with y = 2^j x in [1, 2); j may be negative."""
    j = 0
    while x < 1:
        x, j = 2 * x, j + 1
    while x >= 2:
        x, j = x / 2, j - 1
    return x, j


def check_second_order_descent():
    """M_{e p^r}(t) = Z^(e p j) M^(Z)_{ep}(y) mod p^2 for r >= 2, Z = 2^p, y = 2^j t/p^(r-1)."""
    rng = random.Random(23)
    checks = 0
    for (e, p, r) in ((1, 3, 2), (2, 3, 2), (2, 3, 3), (3, 3, 2), (4, 3, 2), (1, 5, 2), (2, 5, 2), (1, 7, 2)):
        d = e * p ** r
        tm = TwistedMass(2 ** p, p * p)
        for _ in range(8):
            t = Fraction(rng.randrange(1 << 10, 1 << 11), 1 << 10)
            y, j = normalize(t / p ** (r - 1))
            assert (mass(d, t) - pow(2 ** p, e * p * j, p * p) * tm(e * p, y)) % (p * p) == 0
            checks += 1
    # 2^(p^(r-1)) = 2^p mod p^2 for r >= 2
    for p in (3, 5, 7, 11, 13):
        for r in range(2, 6):
            assert pow(2, p ** (r - 1), p * p) == pow(2, p, p * p)
    # Witnesses: the twisted mass vanishes mod p^2 on explicit cells, so second-order
    # descent cannot certify these pairs.
    witnesses = [(2, 3, Fraction(9, 8)), (2, 5, 1 + Fraction(1, 64)), (4, 3, Fraction(9, 8)),
                 (3, 5, Fraction(15, 8)), (3, 7, 1 + Fraction(1, 2) + Fraction(1, 2 ** 8) + Fraction(1, 2 ** 9)),
                 (3, 11, normalize(11 * Fraction(9135223889, 8589934592))[0])]
    for e, p, y in witnesses:
        tm = TwistedMass(2 ** p, p * p)
        assert tm(e * p, y) == 0, (e, p, y)
        assert tm(e, normalize(y / p)[0]) % p == 0 if e > 1 else True
    # Independent exact confirmation at r = 2: M_18(27/16) = 0 mod 9, M_75(75/64) = 0 mod 25.
    assert mass(18, Fraction(27, 16)) % 9 == 0 and mass(18, Fraction(27, 16)) != 0
    assert mass(75, Fraction(75, 64)) % 25 == 0 and mass(75, Fraction(75, 64)) != 0
    return checks, witnesses


# =====================================================================================
# A1.5 First-order cyclic descent: new good pairs, minimized certificates
# =====================================================================================

def descent_orbit(e, p, cap=2_000_000, want_path=False):
    """Exhaust the vectors of the degree-e automaton over F_p reachable from (e, 1).
    Returns (set of values, number of vectors, a digit word reaching value 0 or None)."""
    A = Automaton(e)
    S = len(A.states)
    V = [v % p for v in A.V]
    start = [0] * (S + 1)
    start[A.index[(e, 1)]] = 1
    start = tuple(start)
    parent = {start: None}
    stack, vals, zero_word = [start], set(), None
    while stack:
        vec = stack.pop()
        val = (vec[S] + sum(vec[i] * V[i] for i in range(S) if vec[i])) % p
        vals.add(val)
        if val == 0 and zero_word is None and want_path:
            word, cur = [], vec
            while parent[cur] is not None:
                cur, c = parent[cur]
                word.append(c)
            zero_word = word[::-1]
        for c in (0, 1):
            new = [0] * (S + 1)
            new[S] = vec[S]
            for i in range(S):
                x = vec[i]
                if x:
                    for j, w in A.T[c][i]:
                        new[j if j >= 0 else S] += x * w
            new = tuple(v % p for v in new)
            if new not in parent:
                parent[new] = (vec, c) if want_path else True
                if len(parent) > cap:
                    return None, len(parent), None
                stack.append(new)
    return vals, len(parent), zero_word


PHASE16_GOOD = [(3, 31), (3, 127), (3, 257), (3, 337), (3, 1801), (3, 8191), (4, 8191)]
NEW_GOOD = [(3, 65537), (4, 65537), (3, 131071), (4, 131071), (3, 524287), (4, 524287),
            (5, 524287), (3, 2 ** 31 - 1), (4, 2 ** 31 - 1)]
NEW_BAD = [(5, 8191), (5, 131071), (6, 8191)]


def check_new_descent_pairs():
    sizes = {}
    for e, p in NEW_GOOD:
        assert is_prime(p)
        vals, n, _ = descent_orbit(e, p)
        assert vals is not None and 0 not in vals, (e, p)
        sizes[(e, p)] = n
    bad_witness = {}
    for e, p in NEW_BAD:
        vals, n, word = descent_orbit(e, p, want_path=True)
        assert vals is not None and 0 in vals and word is not None
        # truncate the word after its (e-1)-th one-bit and confirm with the exact integer
        cut, ones = [], 0
        for c in word:
            if ones == e - 1:
                break
            cut.append(c)
            ones += c
        y = 1 + sum(Fraction(c, 2 ** (i + 1)) for i, c in enumerate(cut))
        assert mass(e, y) % p == 0 and mass(e, y) != 0
        bad_witness[(e, p)] = y
    # spot check of one new family through the descent congruence at r = 1:
    # M_{3p}(t) = 2^(3j) M_3(y) mod p for p = 65537 is never 0 (exact, two cuts)
    p = 65537
    for t in (Fraction(3, 2), Fraction(5, 4) + Fraction(1, 64)):
        y, j = normalize(t / p)
        assert (2 ** (3 * j) * mass(3, y)) % p != 0
    return sizes, bad_witness


def _dense(e, p):
    A = Automaton(e)
    S = len(A.states)
    n = S + 1
    T = []
    for c in (0, 1):
        M = [[0] * n for _ in range(n)]
        for i in range(S):
            for j, w in A.T[c][i]:
                k = j if j >= 0 else S
                M[i][k] = (M[i][k] + w) % p
        M[S][S] = 1
        T.append(M)
    V = [v % p for v in A.V] + [1]
    start = [0] * n
    start[A.index[(e, 1)]] = 1
    return T, V, start


def _solve(cols, w, p):
    """Coordinates x with sum_j x_j cols_j = w over F_p (cols independent), or None."""
    k, n = len(cols), len(w)
    M = [[cols[j][r] for j in range(k)] + [w[r]] for r in range(n)]
    row = 0
    for col in range(k):
        pr = next((r for r in range(row, n) if M[r][col]), None)
        if pr is None:
            return None
        M[row], M[pr] = M[pr], M[row]
        inv = pow(M[row][col], -1, p)
        M[row] = [x * inv % p for x in M[row]]
        for r in range(n):
            if r != row and M[r][col]:
                f = M[r][col]
                M[r] = [(x - f * y) % p for x, y in zip(M[r], M[row])]
        row += 1
    if any(M[r][k] for r in range(k, n)):
        return None
    return [M[r][k] for r in range(k)]


def minimized_certificate(e, p):
    """Observable quotient over F_p: columns o_1 = V, o_i = T_w V spanning the space of
    future functionals; reduced matrices X_c with T_c o_i = sum_j X_c[i][j] o_j; the
    reduced orbit of s_0 = (start . o_i)_i. The value of a word is the first reduced
    coordinate, so a closed orbit avoiding first coordinate 0 certifies (e, p)."""
    T, V, start = _dense(e, p)
    cols, frontier = [V], [V]
    while frontier:
        new = []
        for col in frontier:
            for c in (0, 1):
                w = [sum(a * b for a, b in zip(r, col)) % p for r in T[c]]
                if _solve(cols, w, p) is None:
                    cols.append(w)
                    new.append(w)
        frontier = new
    k = len(cols)
    X = []
    for c in (0, 1):
        Xc = []
        for o in cols:
            w = [sum(a * b for a, b in zip(r, o)) % p for r in T[c]]
            x = _solve(cols, w, p)
            assert x is not None                 # intertwining identity T_c o_i in span
            Xc.append(x)
        X.append(Xc)
    s0 = tuple(sum(a * b for a, b in zip(start, o)) % p for o in cols)
    seen, stack = {s0: 0}, [s0]
    order_list = [s0]
    while stack:
        s = stack.pop()
        for c in (0, 1):
            t = tuple(sum(X[c][i][j] * s[j] for j in range(k)) % p for i in range(k))
            if t not in seen:
                seen[t] = len(order_list)
                order_list.append(t)
                stack.append(t)
    zero = any(s[0] == 0 for s in order_list)
    return k, X, s0, order_list, zero


def observable_ranks(emax, P=(1 << 61) - 1):
    ranks = {}
    for e in range(2, emax + 1):
        T, V, start = _dense(e, P)
        cols, frontier = [V], [V]
        while frontier:
            new = []
            for col in frontier:
                for c in (0, 1):
                    w = [sum(a * b for a, b in zip(r, col)) % P for r in T[c]]
                    if _solve(cols, w, P) is None:
                        cols.append(w)
                        new.append(w)
            frontier = new
        ranks[e] = len(cols)
    return ranks


def emit_lean(e, p):
    """Print the minimized certificate as Lean 4 data plus a Bool checker (ASCII only).
    This is a format sketch: it was not compiled in Phase 17."""
    k, X, s0, orbit, zero = minimized_certificate(e, p)
    assert not zero
    idx = {s: i for i, s in enumerate(orbit)}
    succ = [[idx[tuple(sum(X[c][i][j] * s[j] for j in range(k)) % p for i in range(k))]
             for c in (0, 1)] for s in orbit]
    print(f"-- Minimized cyclic-descent certificate for (e, p) = ({e}, {p}).")
    print("-- Format sketch generated by scripts/phase17_dyadic_stoneham.py --emit-lean; not compiled.")
    print(f"-- Reduced dimension {k}; orbit of {len(orbit)} vectors; value = first coordinate.")
    print(f"def P : Nat := {p}")
    print(f"def X0 : List (List Nat) := {[row for row in X[0]]}")
    print(f"def X1 : List (List Nat) := {[row for row in X[1]]}")
    print(f"def orbit : List (List Nat) := {[list(s) for s in orbit]}")
    print(f"def succ : List (List Nat) := {succ}")
    print("def mulVec (M : List (List Nat)) (v : List Nat) : List Nat :=")
    print("  M.map fun row => ((List.zipWith (fun a b => a * b) row v).foldl (fun a b => a + b) 0) % P")
    print("def check : Bool :=")
    print("  (List.range orbit.length).all fun i =>")
    print("    (orbit.getD i []).headD 0 % P != 0 &&")
    print("    mulVec X0 (orbit.getD i []) == orbit.getD ((succ.getD i []).getD 0 0) [] &&")
    print("    mulVec X1 (orbit.getD i []) == orbit.getD ((succ.getD i []).getD 1 0) []")
    print("theorem check_true : check = true := by decide")
    print("-- Remaining obligations: the intertwining identity T_c o_i = sum_j Xc[i][j] o_j over ZMod P")
    print("-- (a finite matrix identity) and the recurrence that defines the automaton for M_e.")


def check_max_loss_mechanism(dmax=60):
    """At the first maximal-loss point t of every 3 <= d <= dmax (Phase 16 table), the
    one-zero term d 2^(d-1) M_(d-1)(2t-2) is strictly more divisible than the zero-free
    term 2^d M_d(2t): the maximal loss is d + v_2 of the middle state (d, 2) at 2t."""
    sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
    import phase16_dyadic_stoneham as p16
    n = 0
    for d, (L, w, _, _) in p16.CERTIFICATES.items():
        if d > dmax:
            continue
        t = Fraction(*w)
        A = 2 ** d * mass(d, 2 * t)
        B = d * 2 ** (d - 1) * mass(d - 1, 2 * t - 2)
        assert order(A + B) == L - 1 == order(A) and (B == 0 or order(B) > order(A))
        n += 1
    return n


def check_one_bit_family(dmax=7):
    """M_d(1 + 2^-a) = sum_{e=0}^{d-1} c_(d,e) 2^(e a) for a >= d - 1, with c_(d,0) = M_d(1)."""
    out = {}
    for d in range(2, dmax + 1):
        a0 = d - 1
        xs = [2 ** a for a in range(a0, a0 + d)]
        ys = [mass(d, 1 + Fraction(1, 2 ** a)) for a in range(a0, a0 + d)]
        n = d
        M = [[Fraction(x) ** k for k in range(n)] + [Fraction(y)] for x, y in zip(xs, ys)]
        for c in range(n):
            piv = next(r for r in range(c, n) if M[r][c])
            M[c], M[piv] = M[piv], M[c]
            for r in range(n):
                if r != c and M[r][c]:
                    f = M[r][c] / M[c][c]
                    M[r] = [u - f * v for u, v in zip(M[r], M[c])]
        coeff = [M[k][n] / M[k][k] for k in range(n)]
        assert all(x.denominator == 1 for x in coeff) and coeff[0] == mass(d, Fraction(1))
        for a in range(a0, a0 + d + 8):
            assert sum(ck * 2 ** (a * k) for k, ck in enumerate(coeff)) == mass(d, 1 + Fraction(1, 2 ** a))
        out[d] = [int(x) for x in coeff]
    return out


# =====================================================================================
# A1.6 Degree 128
# =====================================================================================

DEGREE_128 = (907, Fraction(138241, 131072), 776, 345)


def check_degree_128_points():
    """Exact integers at the stored witness of the maximal loss and at the least-loss
    interval [2 - 2^-6, 2 - 2^-7) for d = 128 (r = 7, j = 1)."""
    L, w, mn, _ = DEGREE_128
    assert order(mass(128, w)) == L - 1
    assert order(mass(128, 2 - Fraction(1, 64))) == mn == v2_factorial(128) + heap_sum(128)


def certify_degree_128():
    L, w, mn, nleaves = DEGREE_128
    A = Automaton(128)
    leaves, nodes = branch_and_bound(A, 128, 1, L)
    vals = [v for _, _, v in leaves]
    assert max(vals) == L - 1 and min(vals) == mn and len(leaves) == nleaves
    assert min(1 + f for f, _, v in leaves if v == L - 1) == w
    return nodes


# =====================================================================================
# Part A2. Resonant quadratics: plateau cycles
# =====================================================================================

def s_of(b):
    return order(b * b - 1) - 1


def kappa_data(b, K):
    """(lambda, C) modulo 2^K from delta_{j+1} = delta_j + 2^(j-1) delta_j^2."""
    P = K + s_of(b) + 16
    mod = 1 << P
    d = ((1 - b * b) // 2) * pow(b * b, -1, mod) % mod
    deltas = []
    for j in range(1, P + 2):
        deltas.append(d)
        d = (d + (1 << (j - 1)) * d * d) % mod
    lam = d
    C = (lam + sum(u - lam for u in deltas)) % mod
    return lam, C, mod


def kappa_general(b, A, B, K=64):
    """kappa = -(2A + B + 2AC)/(2A lambda) mod 2^K for resonant (A, B)."""
    lam, C, mod = kappa_data(b, K + 64)
    num = (-(2 * A + B + 2 * A * C)) % mod
    den = 2 * A * lam
    e = order(den)
    assert num == 0 or order(num) >= e, "not resonant"
    return (num >> e) * pow(den >> e, -1, mod) % (1 << K)


def quadZ(b, k):
    Z = 2 - 2 * b * b
    for i in range(1, k):
        Z = 2 + 2 * b ** (2 ** i) * (Z - 1)
    return Z


def prefix(b, n, A, B, C0):
    """Shifted rational prefix R_n of A alpha^2 + B alpha + C0 (direct insertion sum)."""
    total = Fraction(C0 * b ** n)
    i = 1
    while 2 ** i <= n:
        total += Fraction(B * b ** (n - 2 ** i), 2 ** i)
        j = 1
        while 2 ** i + 2 ** j <= n:
            total += Fraction(A * b ** (n - 2 ** i - 2 ** j), 2 ** (i + j))
            j += 1
        i += 1
    return total


def frac(x):
    return x - (x.numerator // x.denominator)


def cycle_discrepancy_brute(y, b):
    """Extreme discrepancy by direct enumeration of the extremal half-open intervals
    (quadratic time); used only to test cycle_discrepancy."""
    y = frac(y)
    pts, x = [], y
    while True:
        pts.append(x)
        x = frac(b * x)
        if x == y:
            break
    pts.sort()
    m = len(pts)
    best = Fraction(0)
    for i in range(m):
        xi = pts[i]
        best = max(best, abs(Fraction(i, m) - xi), abs(Fraction(i + 1, m) - xi),
                   abs(Fraction(m - i, m) - (1 - xi)), abs(Fraction(m - i - 1, m) - (1 - xi)))
        for j in range(i, m):
            best = max(best, abs(Fraction(j - i + 1, m) - (pts[j] - xi)))
            if j > i:
                best = max(best, abs(Fraction(j - i - 1, m) - (pts[j] - xi)))
    return best, m


def cycle_discrepancy(y, b):
    """Exact extreme discrepancy (half-open intervals in [0, 1)) of the uniform
    probability on the cycle of y under x -> b x mod 1, and the cycle length.
    With sorted points x_0 < ... < x_(m-1) and a_i = i/m - x_i, the extremal intervals
    give the candidates a_j - a_i + 1/m (closed, i <= j), a_i - a_j + 1/m (open, i < j),
    a_i + 1/m and -a_i (intervals touching 0 or 1); everything is scaled by m q."""
    y = frac(y)
    q, n0 = y.denominator, y.numerator
    pts, n = [], n0
    while True:
        pts.append(n)
        n = b * n % q
        if n == n0:
            break
    pts.sort()
    m = len(pts)
    A = [i * q - x * m for i, x in enumerate(pts)]
    best = 0
    lo = hi = A[0]
    for i, a in enumerate(A):
        if i:
            best = max(best, a - lo + q, hi - a + q)
        best = max(best, q, a + q, -a)          # q: the closed interval [x_i, x_i]
        lo, hi = min(lo, a), max(hi, a)
    return Fraction(best, m * q), m


def check_cycle_point_formula():
    """For X^2 - 2X and D = 1: frac(R_n) = frac(-Z_k b^(2^(k-1)) / 2^(2k-1)) at
    n = 3 * 2^(k-1), and its denominator is q_k = 2^[2k - 1 - v_2(Z_k)]_+."""
    count = 0
    for b in (3, 5, 7, 9):
        for k in range(1, 8):
            n = 3 * 2 ** (k - 1)
            R = prefix(b, n, 1, -2, 0)
            Z = quadZ(b, k)
            y = frac(Fraction(-Z * b ** (2 ** (k - 1)), 2 ** (2 * k - 1)))
            assert frac(R) == y
            assert y.denominator == 2 ** max(0, 2 * k - 1 - order(Z))
            assert Z % b == 2 % b                     # Z_k = 2 mod b
            count += 1
    return count


def theta_discrepancy(b, h, u):
    """Closed form of Delta_b(u/2^h) for b = 3 mod 4 (Proposition A2.2)."""
    s = s_of(b)
    if h <= 1:
        return Fraction(1)
    if h <= s:
        w = min(u % 2 ** h, 2 ** h - u % 2 ** h)
        return Fraction(max(w, 2 ** (h - 1) - w), 2 ** (h - 1))
    theta = Fraction((2 ** (s - 1) - u) % 2 ** s, 2 ** s)
    return max(theta, 1 - theta) / 2 ** max(0, h - s - 1)


def check_d1_cycles(hmax=10):
    rng = random.Random(4)
    for _ in range(300):
        b = rng.choice((3, 5, 7, 9, 11, 13, 17, 19, 23))
        q = rng.choice((2, 4, 8, 16, 32, 3, 6, 12, 24, 5, 10, 20, 7, 9, 18, 36, 15, 30, 60))
        if gcd(q, b) != 1:
            continue
        y = Fraction(rng.randrange(q), q)
        assert cycle_discrepancy(y, b) == cycle_discrepancy_brute(y, b), (y, b)
    """Delta_b(u/2^h) = 2^-[h - v_2(b-1)]_+ for b = 1 mod 4; explicit theta form for
    b = 3 mod 4; singletons exactly for h <= v_2(b-1)."""
    count = 0
    for b in (3, 5, 7, 9, 11, 13, 15, 17, 19, 23, 25, 27, 31, 33):
        t0 = order(b - 1)
        for h in range(hmax + 1):
            for u in (range(1, 2 ** h, 2) if h else [0]):
                D, m = cycle_discrepancy(Fraction(u, 2 ** h), b)
                assert (m == 1) == (h <= t0)
                if b % 4 == 1:
                    assert D == Fraction(1, 2 ** max(0, h - t0))
                else:
                    assert D == theta_discrepancy(b, h, u), (b, h, u)
                count += 1
    return count


def odd_component_sequence(b, A, B, C0, D1, kmax=None):
    """r_k = b^(n_k) Q_k mod D1 (n_k = 3 * 2^(k-1)) for k = 1, 2, ...; returns the list
    up to the first repeated state and (k0, period) of the eventual cycle, or with kmax
    the list r_1..r_kmax."""
    if D1 == 1:
        return ([0] * kmax if kmax else [0]), (1, 1)
    inv2 = pow(2, -1, D1)
    S, i2k, beta = 0, 1, b % D1          # beta = b^(2^(k-1)) mod D1
    seen, seq = {}, []
    for k in range(1, 10 ** 6):
        if kmax and k > kmax:
            return seq, None
        i2k = i2k * inv2 % D1
        L = i2k * pow(beta * beta % D1, -1, D1) % D1
        S = (S + L) % D1
        Q = (A * (S * S - L * L) + B * S + C0) % D1
        seq.append(pow(beta, 3, D1) * Q % D1)
        state = (S, i2k, beta)
        if state in seen and not kmax:
            return seq, (seen[state], k - seen[state])
        seen[state] = k
        beta = beta * beta % D1
    raise RuntimeError("no period")


def plateau_bound(b, A, B, C0, D):
    """sup of Delta_b over all plateau cycles admissible for (A alpha^2 + B alpha + C0)/D,
    gcd(D, b) = 1, (A, B) resonant. Returns (sup, h attaining it, singleton possible, info)."""
    assert gcd(D, b) == 1
    delta = order(D) if D % 2 == 0 else 0
    D1 = D >> delta
    seq, (k0, per) = odd_component_sequence(b, A, B, C0, D1)
    v = order(per) if per % 2 == 0 else 0
    assert v <= 64
    kap = kappa_general(b, A, B)
    ks = [k for k in range(k0, k0 + per) if (k - kap) % (1 << v) == 0]
    alpha2 = pow(1 << delta, -1, D1) if D1 > 1 else 0
    yodd = sorted({Fraction(seq[k - 1] * alpha2 % D1, D1) if D1 > 1 else Fraction(0) for k in ks})
    M = 2 * mult_order(b, D1) // gcd(2, mult_order(b, D1))
    t1 = order(b ** M - 1)
    best, best_h, singleton, h = Fraction(0), None, False, 0
    while True:
        m = h + delta
        if h >= 1 and m >= t1 and Fraction(1, 2 ** (m - t1)) <= best:
            break                                   # tail bound: Delta <= 2^(t1 - m)
        js = range(1, 1 << m, 2) if h >= 1 else range(0, 1 << m)
        for yo in yodd:
            for j in js:
                dlt, size = cycle_discrepancy(yo + Fraction(j, 1 << m), b)
                singleton |= size == 1
                if dlt > best:
                    best, best_h = dlt, h
        h += 1
    return best, best_h, singleton, (k0, per, len(yodd))


def check_odd_components():
    """The odd component of frac(R_n/D) agrees with the periodic residue r_k."""
    for b, D, C0 in ((5, 3, 0), (5, 9, 2), (7, 5, 3), (11, 7, 1), (13, 15, 4)):
        delta = order(D) if D % 2 == 0 else 0
        D1 = D >> delta
        seq, _ = odd_component_sequence(b, 1, -2, C0, D1, kmax=7)
        for k in range(1, 8):
            n = 3 * 2 ** (k - 1)
            R = prefix(b, n, 1, -2, C0)
            # R is dyadic; its residue modulo D1 is R.numerator * (R.denominator)^-1
            assert R.numerator * pow(R.denominator, -1, D1) % D1 == seq[k - 1]
    # Q_k = C0 + 2 mod 3 for X^2 - 2X and every k >= 1 (3 does not divide b)
    for b in (5, 7, 11, 13, 17):
        for C0 in range(3):
            seq, _ = odd_component_sequence(b, 1, -2, C0, 3, kmax=60)
            assert all(r % 3 == (pow(b, 3 * 2 ** k, 3) * (C0 + 2)) % 3 for k, r in enumerate(seq))


PLATEAU_EXPECTED = {
    (5, 3): ['5/6', '1', '5/6'], (11, 3): ['11/12', '1', '11/12'], (17, 3): ['5/6', '1', '5/6'],
    (7, 3): ['1', '1', '1'], (3, 5): ['27/40', '1', '27/40', '27/40', '27/40'],
    (5, 9): ['5/18', '1', '5/18', '5/18', '1', '5/18', '5/18', '1', '5/18'],
    (7, 9): ['1/3', '1', '1/3', '1/3', '1', '1/3', '1/3', '1', '1/3'],
    (11, 9): ['11/36', '1', '11/36', '11/36', '1', '11/36', '11/36', '1', '11/36'],
}


def check_plateau_bounds():
    table = {}
    for (b, D), expected in PLATEAU_EXPECTED.items():
        row = []
        for C0 in range(D):
            sup, h, sing, _ = plateau_bound(b, 1, -2, C0, D)
            assert sing == (sup == 1)
            row.append(str(sup))
        assert row == expected, (b, D, row)
        table[(b, D)] = row
    # D = 3, C0 = 0, every b = 2 mod 3 below 50: no singleton, sup < 1
    sup3 = {}
    for b in range(5, 100, 3):                    # b = 2 mod 3
        if b % 2 == 0:
            continue
        for C0 in (0, 2):
            sup, h, sing, _ = plateau_bound(b, 1, -2, C0, 3)
            assert not sing and sup == 1 - Fraction(1, 3 * 2 ** order(b + 1)), (b, C0, sup)
        sup3[b] = sup
    # another resonant pair: (A, B) = (1, 6) for b = 5 (v_2(2A + B) = 3 >= v_2(2A) + s = 3);
    # kappa is even, so Q_k = C0 - A mod 3 on the admissible (even) k: singleton iff C0 = 1 mod 3
    assert kappa_general(5, 1, 6) % 2 == 0 and kappa_general(5, 1, -2) % 4 == 3
    for C0 in range(3):
        sup, h, sing, _ = plateau_bound(5, 1, 6, C0, 3)
        assert sing == (C0 % 3 == 1)
    return table, sup3


# =====================================================================================
# Part A3. Joint normality: pivot degrees
# =====================================================================================

GOOD_PAIRS = PHASE16_GOOD + NEW_GOOD


def resolved_degree(d):
    """Degrees d != 2 with P(alpha) normal for every rational P of degree d."""
    if d == 1 or 3 <= d <= 120 or d == 128:
        return True
    for p in range(3, d + 1, 2):                       # odd prime powers (Phase 13)
        if is_prime(p):
            q = p
            while q < d:
                q *= p
            if q == d:
                return True
    for e, p in GOOD_PAIRS:
        q = e
        while q < d:
            q *= p
        if q == d:
            return True
    return False


def nonresonant(Acoef, Bcoef, b):
    """v_2(2A + B) < v_2(2A) + s for rational A != 0, B."""
    def v(q):
        q = Fraction(q)
        return float("inf") if q == 0 else order(q.numerator) - order(q.denominator)
    return v(2 * Acoef + Bcoef) < v(2 * Acoef) + s_of(b)


def joint_status(polys, b):
    """Echelon the Q-span of the polynomials (coefficient lists, index = degree) and
    decide whether Theorem A3 applies: no constant in the span, every pivot degree
    resolved or 2, and if 2 is a pivot then 1 is not and the degree-2 row is non-resonant."""
    rows = [[Fraction(x) for x in P] for P in polys]
    width = max(len(r) for r in rows)
    rows = [r + [Fraction(0)] * (width - len(r)) for r in rows]
    pivots = {}
    for r in rows:
        r = r[:]
        for deg in sorted(pivots, reverse=True):
            if r[deg]:
                f = r[deg] / pivots[deg][deg]
                r = [x - f * y for x, y in zip(r, pivots[deg])]
        nz = [i for i, x in enumerate(r) if x]
        if not nz:
            return False, "dependent family"
        pivots[max(nz)] = r
    if 0 in pivots:
        return False, "span contains a nonzero constant"
    for deg in pivots:
        if deg != 2 and not resolved_degree(deg):
            return False, f"unresolved pivot degree {deg}"
    if 2 in pivots:
        if 1 in pivots:
            return False, "pivots 1 and 2: the span contains a resonant quadratic"
        r = pivots[2]
        if not nonresonant(r[2], r[1], b):
            return False, "resonant degree-2 pivot"
    return True, sorted(pivots)


def check_joint_examples():
    b = 3
    X = lambda k: [0] * k + [1]
    add = lambda *ps: [sum(c) for c in zip(*[p + [0] * (200 - len(p)) for p in ps])]
    ex = {
        "alpha^3, alpha^5 + alpha^2, alpha^128": [X(3), add(X(5), X(2)), X(128)],
        "alpha, alpha^3 - alpha^2": [X(1), add(X(3), [0, 0, -1])],
        "alpha^2 + alpha (non-resonant), alpha^7": [add(X(2), X(1)), X(7)],
        "alpha^2 - 2 alpha (resonant)": [add(X(2), [0, -2])],
        "alpha^2, alpha": [X(2), X(1)],
        "alpha^122 + alpha^3, alpha^3": [add(X(122), X(3)), X(3)],
        "alpha^3 + 1, alpha^3": [add(X(3), [1]), X(3)],
        "alpha^(3*65537)": [X(3 * 65537)],
    }
    expected = {
        "alpha^3, alpha^5 + alpha^2, alpha^128": True, "alpha, alpha^3 - alpha^2": True,
        "alpha^2 + alpha (non-resonant), alpha^7": True, "alpha^2 - 2 alpha (resonant)": False,
        "alpha^2, alpha": False, "alpha^122 + alpha^3, alpha^3": False,
        "alpha^3 + 1, alpha^3": False, "alpha^(3*65537)": True,
    }
    out = {}
    for name, polys in ex.items():
        ok, why = joint_status(polys, b)
        assert ok == expected[name], (name, why)
        out[name] = (ok, why)
    return out


# =====================================================================================

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--degree-128", action="store_true")
    parser.add_argument("--middle-max", type=int, default=32)
    parser.add_argument("--emit-lean", action="store_true")
    args = parser.parse_args()
    if args.emit_lean:
        emit_lean(3, 31)
        return
    T0 = time.time()

    print("Part A1. The leading mass M_d on [1, 2)")
    n = check_least_orbit_order()
    print(f"A1.1 least orbit order: slack identity Phi - G = sum(sigma_D - S_D) >= 0 on {n} random multisets;")
    print("     min Phi = sum floor(log2 k) with exactly the predicted one or two minimizing orbits, d <= 300;")
    print("     closed form for every Kraft budget 2^a (a <= 7, d <= 150), lower bound and construction")
    n = check_least_loss_location()
    print(f"     least loss v_2(d!) + G(d) exactly on [2 - 2^(1-r), 2 - 2^-r), exact integers for {n} degrees")
    check_top_state()
    print("A1.2 top state M_a(a-1+f) closed form (a <= 12); zero exactly on [a - 1/2, a) for even a")
    t = time.time()
    worst = certify_middle_states(args.middle_max)
    print(f"     middle states (a, n), 1 <= n <= a-2, a <= {args.middle_max}: no zero cell "
          f"({len(worst)} states, max loss {max(worst.values())}, {time.time() - t:.1f}s)")
    z3 = check_parity_and_mod3()
    print(f"A1.3 K_U(z) odd for z = -1, 3 at every cut (d <= 7); M_d = (-1)^d K_U(-1) mod 3;")
    print(f"     degrees with a mod-3 zero: {[d for d, w in z3.items() if w is not None]} "
          f"(e.g. d=2 at {z3[2]}, d=4 at {z3[4]}); none for {[d for d, w in z3.items() if w is None]}")
    nchk, wit = check_second_order_descent()
    print(f"A1.4 second-order descent mod p^2: {nchk} exact congruences; zero witnesses mod p^2 for "
          f"{[(e, p) for e, p, _ in wit]}; M_18(27/16) = 0 mod 9, M_75(75/64) = 0 mod 25")
    t = time.time()
    sizes, badw = check_new_descent_pairs()
    print(f"A1.5 new good pairs (orbit sizes): {sizes}")
    print(f"     bad pairs with exact zero witnesses mod p: {badw} ({time.time() - t:.1f}s)")
    certs = {}
    for e, p in ((3, 31), (3, 127), (3, 8191), (4, 8191)):
        k, X, s0, orb, zero = minimized_certificate(e, p)
        assert not zero
        certs[(e, p)] = (e * (e + 1) // 2 + 1, k, len(orb))
    assert certs[(3, 31)] == (7, 5, 57) and certs[(4, 8191)] == (11, 7, 4850)
    # mirror of the Bool checker printed by --emit-lean for (3, 31)
    k, X, s0, orb, _ = minimized_certificate(3, 31)
    idx = {v: i for i, v in enumerate(orb)}
    mulvec = lambda M, v: tuple(sum(a * b for a, b in zip(row, v)) % 31 for row in M)
    assert orb[0] == s0 and all(v[0] % 31 and mulvec(X[0], v) in idx and mulvec(X[1], v) in idx for v in orb)
    ranks = observable_ranks(10)
    assert ranks == {2: 3, 3: 5, 4: 7, 5: 9, 6: 12, 7: 15, 8: 18, 9: 21, 10: 25}
    print(f"     minimized F_p certificates (states, rank, reduced orbit): {certs}")
    print(f"     observable rank of the degree-e representation mod 2^61-1: {ranks}")
    n = check_max_loss_mechanism()
    onebit = check_one_bit_family()
    print(f"     maximal loss = d + v_2(M_d(2t)) at the first maximal-loss point, one-zero term more divisible ({n} degrees)")
    print(f"     M_d(1 + 2^-a) = sum_e c_(d,e) 2^(ea) for a >= d-1 (d <= 7); e.g. d=4: {onebit[4]}")
    t = time.time()
    check_degree_128_points()
    print(f"A1.6 d = 128: exact v_2 = 906 at t = 138241/131072 and 776 = v_2(128!) + G(128) at 2 - 2^-6 "
          f"({time.time() - t:.1f}s)")
    if args.degree_128:
        t = time.time()
        nodes = certify_degree_128()
        print(f"     certificate M_128 != 0 on [1, 2): precision 907 sharp, 345 leaves, {nodes} nodes, "
              f"{time.time() - t:.1f}s")

    print("Part A2. Resonant quadratics")
    n = check_cycle_point_formula()
    print(f"A2.1 cycle point frac(R_n) = frac(-Z_k b^(2^(k-1))/2^(2k-1)), denominator q_k, Z_k = 2 mod b ({n} cases)")
    n = check_d1_cycles()
    print(f"A2.2 Delta_b(u/2^h) = 2^-[h - v_2(b-1)]_+ (b = 1 mod 4), theta form (b = 3 mod 4); {n} cycles")
    check_odd_components()
    table, sup3 = check_plateau_bounds()
    print("A2.3 admissible plateau cycles; sup Delta (limsup D_N <= sup/4), C0 = 0..D-1:")
    for (b, D), row in table.items():
        print(f"     b={b:2d} D={D}: {row}")
    print(f"     D = 3, C0 in {{0, 2}}, b = 2 mod 3, b < 100: no singleton cycle, sup Delta = 1 - 1/(3 * 2^v_2(b+1)) "
          f"(e.g. {dict((b, str(v)) for b, v in list(sup3.items())[:6])})")

    print("Part A3. Joint normality")
    for name, (ok, why) in check_joint_examples().items():
        print(f"     {name}: {'jointly normal' if ok else 'not covered'} ({why})")
    elapsed = time.time() - T0
    print(f"All assertions passed in {elapsed:.1f}s")


if __name__ == "__main__":
    main()
