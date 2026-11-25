#!/usr/bin/env python3
"""Exact checks for Phase 19 Track E (notes/phase19/classical.md).

Positive subset sums of the p-multiples of the binary Taylor series of log 2,
global dyadic completion, Glaisher block identities, Wieferich exceptions in
the reduced denominators, and the average denominator loss.

Standard library only.  Run

    python3 -B scripts/phase19_classical.py            # default limits
    python3 -B scripts/phase19_classical.py --limit 1000000 --group-limit 100000

The script ends with "All Phase 19 classical checks passed."
"""

from __future__ import annotations

import argparse
import math
import random
import time
from collections import Counter

# Rosser-Schoenfeld (1962, Theorem 12): psi(x) < 1.03883 x for every x > 0.
PSI_CONST = 1.03883
LOG_NUM_CONST = math.log(2) + PSI_CONST  # log N_S < LOG_NUM_CONST * k


# ---------------------------------------------------------------- utilities

def primes_up_to(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, math.isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i:: i] = b"\x00" * ((n - i * i) // i + 1)
    return [i for i, v in enumerate(sieve) if v]


def v_p(n: int, p: int) -> int:
    assert n != 0
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def odd_prime_factors(n: int) -> list[int]:
    while n % 2 == 0:
        n //= 2
    out = []
    d = 3
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 2
    if n > 1:
        out.append(n)
    return out


def lcm_upto(k: int) -> int:
    out = 1
    for i in range(2, k + 1):
        out = out * i // math.gcd(out, i)
    return out


def fermat_quotient(a: int, p: int) -> int:
    return ((pow(a, p - 1, p * p) - 1) // p) % p


def x_res(j: int, p: int) -> int:
    """x_j(p) = (j 2^j)^(-1) mod p, for p not dividing j."""
    return pow(j * pow(2, j, p) % p, -1, p)


def rot(bits: int, x: int, p: int, mask: int) -> int:
    """Cyclic shift of a residue bitset modulo p by x."""
    return ((bits << x) | (bits >> (p - x))) & mask


# ------------------------------------------------------- the local problem

def local_minima(p: int, jmax: int | None = None) -> tuple[int | None, int | None]:
    """Return (k(p), k*(p)).

    k(p): least K such that some S subset of [1, K] with 1 in S and p not
    dividing any j in S has sum of x_j(p) = 0 mod p.  k*(p): the same for
    arbitrary nonempty S.  Indices divisible by p are skipped (they only
    occur for p <= 3 here)."""
    mask = (1 << p) - 1
    x1 = x_res(1, p)
    target = (-x1) % p
    with_one = 1            # subset sums of x_2..x_K, empty sum included
    nonempty = 1 << x1      # nonempty subset sums of x_1..x_K
    k = None
    kstar = 1 if x1 == 0 else None
    j = 1
    while k is None or kstar is None:
        j += 1
        if jmax is not None and j > jmax:
            break
        if j % p == 0:
            continue
        x = x_res(j, p)
        if k is None:
            with_one |= rot(with_one, x, p, mask)
            if (with_one >> target) & 1:
                k = j
        if kstar is None:
            nonempty |= rot(nonempty, x, p, mask) | (1 << x)
            if nonempty & 1:
                kstar = j
    return k, kstar


def minimal_set_with_one(p: int) -> list[int]:
    """An explicit S realizing k(p) (requires k(p) <= p - 1)."""
    mask = (1 << p) - 1
    target = (-x_res(1, p)) % p
    history = [1]           # history[i] = sums of x_2..x_{i+1}
    j = 1
    while True:
        j += 1
        assert j < p
        x = x_res(j, p)
        nxt = history[-1] | rot(history[-1], x, p, mask)
        history.append(nxt)
        if (nxt >> target) & 1:
            break
    chosen = [1]
    t = target
    for idx in range(len(history) - 1, 0, -1):
        jj = idx + 1
        if (history[idx - 1] >> t) & 1:
            continue
        chosen.append(jj)
        t = (t - x_res(jj, p)) % p
    assert t == 0
    chosen.sort()
    assert chosen[-1] == j and sum(x_res(i, p) for i in chosen) % p == 0
    return chosen


def random_model_k(p: int, rng: random.Random) -> int:
    mask = (1 << p) - 1
    target = (-rng.randrange(1, p)) % p
    sums = 1
    j = 1
    while True:
        j += 1
        sums |= rot(sums, rng.randrange(1, p), p, mask)
        if (sums >> target) & 1:
            return j


# ---------------------------------------------------- global completion

def subset_sum_cover(q: int, cands: list[int]) -> dict[int, list[int]]:
    """For each reachable residue r mod q, one witness list of indices j in
    cands with sum x_j(q) = r (the empty list for r = 0).  The witnesses are
    the first ones found in the given order; they need not be shortest."""
    best: dict[int, list[int]] = {0: []}
    for j in cands:
        x = x_res(j, q)
        new = {}
        for r, lst in best.items():
            r2 = (r + x) % q
            if r2 not in best and (r2 not in new or len(new[r2]) > len(lst) + 1):
                new[r2] = lst + [j]
        best.update(new)
    return best


_COVER_CACHE: dict[int, dict[int, list[int]]] = {}


def cover_table(q: int) -> dict[int, list[int]]:
    if q not in _COVER_CACHE:
        _COVER_CACHE[q] = subset_sum_cover(q, list(range(1, q)))
    return _COVER_CACHE[q]


def q_state(group: set[int], q: int) -> tuple[int, int]:
    """(valuation, leading digit) of T_q = sum of a_m over m in group with q | m.
    A nonnegative valuation is reported as (0, 0)."""
    terms = [m for m in group if m % q == 0]
    if not terms:
        return 0, 0
    top = max(v_p(m, q) for m in terms)
    mod = q ** (top + 1)
    s = 0
    for m in terms:
        v = v_p(m, q)
        u = m // q ** v
        s = (s + q ** (top - v) * pow(u * pow(2, m, mod) % mod, -1, mod)) % mod
    if s == 0:
        return 0, 0
    w = v_p(s, q)
    if w >= top:
        return 0, 0
    return -(top - w), (s // q ** w) % q


def complete_group(p: int, S: list[int]) -> set[int]:
    """Theorem 2.2: extend p*S by corrections q^e j' (1 <= j' < q) processed
    in decreasing order of the primes q < p."""
    group = {p * j for j in S}
    pending: set[int] = set()
    for j in S:
        pending.update(odd_prime_factors(j))
    done: set[int] = set()
    while pending - done:
        q = max(pending - done)
        done.add(q)
        assert q < p
        while True:
            val, digit = q_state(group, q)
            if val >= 0:
                break
            e = -val
            sub = cover_table(q).get((-digit) % q)
            assert sub, (p, q, e, digit)
            for jj in sub:
                m = q ** e * jj
                assert m not in group and m % p != 0
                group.add(m)
                pending.update(odd_prime_factors(jj))
    return group


def is_dyadic_sum(group: set[int]) -> bool:
    top = max(m + v_p(m, 2) for m in group)
    odd_lcm = 1
    for m in group:
        o = m >> v_p(m, 2)
        odd_lcm = odd_lcm * o // math.gcd(odd_lcm, o)
    num = sum((1 << (top - m - v_p(m, 2))) * (odd_lcm // (m >> v_p(m, 2))) for m in group)
    return num % odd_lcm == 0


def ray_minimum(p: int) -> int:
    """Least K with a single-ray group {p 2^i : i in G}, 0, K in G (Phase 18 F2.2)."""
    mask = (1 << p) - 1
    target = (-x_res(1, p)) % p
    sums = 1
    i = 0
    while True:
        i += 1
        x = pow(pow(2, i, p) * pow(2, pow(2, i, p - 1), p) % p, -1, p)
        sums |= rot(sums, x, p, mask)
        if (sums >> target) & 1:
            return i


# --------------------------------------------------------------- sections

def section_local(limit: int, seed_count: int) -> dict[int, tuple[int, int]]:
    print(f"=== 1. Local minima k(p), k*(p) for odd primes p <= {limit} ===")
    t0 = time.time()
    data = {}
    for p in primes_up_to(limit):
        if p == 2:
            continue
        data[p] = local_minima(p)
    print(f"computed {len(data)} primes in {time.time() - t0:.1f}s")
    small = {p: data[p] for p in data if p <= 61}
    # The survey searches past p - 1 and skips multipliers divisible by p.
    # This differs from the note's convention (S inside [1, p-1]) only at
    # p = 3, where the survey reports 4 while k(3) is infinite in the note.
    print("small primes (p: k, k*), unrestricted search:", small)
    assert small[3] == (4, 4) and small[5] == (2, 2) and small[7] == (6, 4)
    assert small[13] == (3, 3) and small[37] == (9, 8) and small[41] == (4, 4)
    assert local_minima(3, jmax=2) == (None, None)
    for p, (k, ks) in data.items():
        assert ks <= k
        if p >= 5:
            assert k <= p - 1, p
    big_ps = [p for p in data if p > 100]
    equal = sum(1 for p in big_ps if data[p][0] == data[p][1])
    gap = max(data[p][0] - data[p][1] for p in big_ps)
    print(f"k(p) = k*(p) for {equal} of {len(big_ps)} primes 100 < p <= {limit}; "
          f"largest k(p) - k*(p) = {gap}")
    if limit == 200000:
        assert (equal, len(big_ps), gap) == (10575, 17959, 10)
    excess = sorted((k - math.log2(p), p, k) for p, (k, _) in data.items())
    print("largest k(p) - log2 p:", [(round(e, 3), p, k) for e, p, k in excess[-5:]])
    print("smallest k(p) - log2 p:", [(round(e, 3), p, k) for e, p, k in excess[:5]])
    # Theorem 3.3 numerically (trivially weaker than the data)
    for p, (k, _) in data.items():
        if p >= 41:
            assert k <= math.ceil(3 * math.sqrt(4 * p - 3))
    # random subset-sum model comparison on p > 100
    big = [p for p in data if p > 100]
    act = Counter(data[p][0] - math.ceil(math.log2(p)) for p in big)
    mean_act = sum(data[p][0] - math.log2(p) for p in big) / len(big)
    sims = []
    for seed in range(seed_count):
        rng = random.Random(1900 + seed)
        sims.append(Counter(random_model_k(p, rng) - math.ceil(math.log2(p)) for p in big))
    keys = sorted(set(act) | set().union(*sims))
    print("k(p) - ceil(log2 p): actual vs mean of random-model runs")
    pooled = Counter()
    for s in sims:
        pooled.update(s)
    for d in keys:
        print(f"  {d:>4}: {act[d]:>7}  {pooled[d] / seed_count:>10.1f}")
    # chi-square over cells with expected >= 20 (others pooled into tails)
    exp = {d: pooled[d] / seed_count for d in keys}
    cells, chi = 0, 0.0
    lo_a = lo_e = hi_a = hi_e = 0.0
    for d in keys:
        if exp[d] >= 20:
            chi += (act[d] - exp[d]) ** 2 / exp[d]
            cells += 1
        elif d < 0:
            lo_a += act[d]
            lo_e += exp[d]
        else:
            hi_a += act[d]
            hi_e += exp[d]
    for a, e in ((lo_a, lo_e), (hi_a, hi_e)):
        if e > 0:
            chi += (a - e) ** 2 / e
            cells += 1
    print(f"mean k(p) - log2 p = {mean_act:.4f}; chi-square {chi:.1f} on {cells} cells "
          f"(random model with {seed_count} runs)")
    return data


def section_exceptional(data: dict[int, tuple[int, int]], limit: int) -> None:
    print("\n=== 2. Theorem 4.1: primes with small k(p), k*(p) ===")
    kmax = 12
    with_one: dict[int, set[int]] = {}
    any_set: dict[int, set[int]] = {}
    for k in range(1, kmax + 1):
        lk = lcm_upto(k)
        ps1: set[int] = set()
        ps_any: set[int] = set()
        for mask in range(1, 1 << k):
            S = [j + 1 for j in range(k) if (mask >> j) & 1]
            num = sum((1 << (k - j)) * (lk // j) for j in S)
            assert 0 < num < (1 << k) * lk
            assert math.log(num) < LOG_NUM_CONST * k
            fac = {q for q in odd_prime_factors(num) if q > k}
            ps_any |= fac
            if S[0] == 1:
                ps1 |= fac
        with_one[k] = ps1
        any_set[k] = ps_any
    print(" k  #{p>k: k(p)<=k}  #{p>k: k*(p)<=k}  bound 2^(k-1)*1.732k/log3   primes with k(p)=k (first few)")
    prev: set[int] = set()
    for k in range(1, kmax + 1):
        bound = (2 ** (k - 1)) * LOG_NUM_CONST * k / math.log(3)
        assert len(with_one[k]) <= bound
        new = sorted(with_one[k] - prev)
        prev = prev | with_one[k]
        print(f"{k:>2}  {len(with_one[k]):>15}  {len(any_set[k]):>16}  {bound:>26.1f}   {new[:8]}")
        # cross-check with the bitset survey
        dp1 = {p for p, (kk, _) in data.items() if p > k and kk <= k}
        dpa = {p for p, (_, ks) in data.items() if p > k and ks <= k}
        assert dp1 == {p for p in with_one[k] if p <= limit}, k
        assert dpa == {p for p in any_set[k] if p <= limit}, k
    assert sorted(with_one[2]) == [5] and sorted(with_one[3]) == [5, 13]
    assert sorted(with_one[4] - with_one[3]) == [11, 41, 107, 131]
    # density statement at the survey limit
    X = limit
    k0 = math.floor(math.log2(X) - 2 * math.log2(math.log2(X)))
    band = [p for p in data if X // 2 < p <= X]
    bad = [p for p in band if data[p][0] <= k0]
    print(f"primes in ({X // 2}, {X}]: {len(band)}; with k(p) <= log2 X - 2 log2 log2 X "
          f"(= {k0}): {len(bad)}")


def section_global(group_limit: int) -> None:
    print(f"\n=== 3. Theorem 2.2: global dyadic groups, 5 <= p <= {group_limit} ===")
    # Lemma 3.1 for q <= 31 by computation, and q >= 37 also spot-checked
    for q in primes_up_to(400):
        if q == 2:
            continue
        table = cover_table(q)
        assert len(table) == q, q
    print("subset sums of x_1(q),...,x_{q-1}(q) cover Z/q for every odd prime q < 400")
    # collision lemma: at most one colliding pair per difference d
    for p in primes_up_to(3000)[1:]:
        seen: dict[int, list[int]] = {}
        for j in range(1, p):
            seen.setdefault(x_res(j, p), []).append(j)
        diffs = Counter()
        for js in seen.values():
            for a in range(len(js)):
                for b in range(a + 1, len(js)):
                    diffs[js[b] - js[a]] += 1
        assert all(c == 1 for c in diffs.values()), p
        assert len(seen) >= p / 3
    print("collision lemma and distinct-value bound checked for 3 <= p < 3000")
    # p = 3: no admissible S inside [1, 2]; M_glob(3) = 12 from {3, 12}
    assert local_minima(3, jmax=2)[0] is None
    assert is_dyadic_sum({3, 12})
    t0 = time.time()
    count = 0
    stats = []
    for p in primes_up_to(group_limit):
        if p < 5:
            continue
        S = minimal_set_with_one(p)
        G = complete_group(p, S)
        assert is_dyadic_sum(G), p
        assert max(G) == p * S[-1]
        assert {m for m in G if m % p == 0} == {p * j for j in S}
        assert max([m for m in G if m % p] + [0]) < S[-1] ** 2
        count += 1
        stats.append((p, S[-1], len(S), len(G)))
    print(f"verified {count} groups with max G = p k(p) in {time.time() - t0:.1f}s")
    for p, k, s, g in stats[:6]:
        print(f"  p={p}: k(p)={k}, |S|={s}, |G|={g}")
    G7 = complete_group(7, minimal_set_with_one(7))
    print("  example p=7:", sorted(G7))
    assert sorted(G7) == [3, 6, 7, 15, 21, 35, 42]
    largest = max(stats, key=lambda r: r[3])
    print(f"  largest group: p={largest[0]}, k={largest[1]}, |G|={largest[3]}")
    # single-ray comparison
    worse = 0
    rows = []
    for p, k, _, _ in stats:
        K = ray_minimum(p)
        if p * 2 ** K > p * k:
            worse += 1
        if p in (5, 7, 11, 13, 29, 101, 1009, 10007):
            rows.append((p, k, p * k, K, p * 2 ** K))
    print(f"single-ray minimum is strictly larger for {worse} of {len(stats)} primes")
    for r in rows:
        print(f"  p={r[0]}: general p*k(p)={r[2]} (k={r[1]}), single ray p*2^K={r[4]} (K={r[3]})")


def section_glaisher(limit: int) -> None:
    print(f"\n=== 4. Theorem 5.2: Glaisher block identities, 5 <= p <= {limit} ===")
    for p in primes_up_to(limit):
        if p < 5:
            continue
        xs = [x_res(j, p) for j in range(1, p)]
        q2 = fermat_quotient(2, p)
        q3 = fermat_quotient(3, p)
        assert sum(xs) % p == q2
        assert sum(xs[0::2]) % p == 3 * q3 * pow(4, -1, p) % p
        s2 = sum(pow(j * j * pow(2, j, p) % p, -1, p) for j in range(1, p)) % p
        assert s2 == (-q2 * q2 * pow(2, -1, p)) % p
        t2 = sum(pow(2, j, p) * pow(j * j, -1, p) for j in range(1, p)) % p
        assert t2 == (-q2 * q2) % p          # Granville's congruence
        for b in (3, 5, 10):
            if b % p == 0 or (b - 1) % p == 0:
                continue
            sb = sum(pow(j * pow(b, j, p) % p, -1, p) for j in range(1, p)) % p
            rhs = (b * fermat_quotient(b, p) - (b - 1) * fermat_quotient(b - 1, p)) * pow(b, -1, p) % p
            assert sb == rhs
            assert rhs == fermat_quotient(pow(b, b) * pow(pow(b - 1, b - 1), -1, p * p) % (p * p), p) * pow(b, -1, p) % p
    print("full block = q_p(2), odd block = (3/4) q_p(3), order two = -q_p(2)^2/2, "
          "base b in {3,5,10}: all congruences hold")
    for p in (1093, 3511):
        assert sum(x_res(j, p) for j in range(1, p)) % p == 0
        assert fermat_quotient(2, p) == 0
    for p in (11, 1006003):
        assert sum(x_res(j, p) for j in range(1, p, 2)) % p == 0
    print("Wieferich primes 1093, 3511 kill their full block; base-3 Wieferich 11, 1006003 kill the odd block")
    wief = [p for p in primes_up_to(limit) if p > 2 and fermat_quotient(2, p) == 0]
    assert wief == [1093, 3511]


def top_digit_valuation(n: int, p: int, a: int) -> int:
    """Exact v_p of the reduced denominator of R(n) = sum_{m<=n} 2^(n-m)/m,
    for p odd with p^a <= n < p^(a+1) (only multiples of p matter)."""
    mod = p ** (a + 1)
    s = 0
    for ell in range(1, n // p + 1):
        v = v_p(ell, p)
        u = ell // p ** v
        # p^a / (ell p) = p^(a-1-v) / u
        s = (s + pow(2, n - ell * p, mod) * p ** (a - 1 - v) * pow(u, -1, mod)) % mod
    if s == 0:
        return 0
    return max(0, a - v_p(s, p))


def section_wieferich_denominators() -> None:
    print("\n=== 5. Corollary 5.4: reduced denominators in the band floor(n/p^a) = p - 1 ===")
    for p in (1093, 3511):
        for n in (p * (p - 1), p * p - 1):
            val = top_digit_valuation(n, p, 1)
            print(f"  p={p}, n={n}: v_p(den R(n)) = {val} (full power would be 1)")
            assert val == 0
    for p in (1091, 1097, 3499):
        n = p * (p - 1)
        assert top_digit_valuation(n, p, 1) == 1
    # a = 2 for p = 1093: partial survival of p^2
    p = 1093
    for n in ((p - 1) * p * p, p ** 3 - 1):
        val = top_digit_valuation(n, p, 2)
        print(f"  p={p}, n={n}: v_p(den R(n)) = {val} (full power would be 2)")
        assert val < 2
    # Order two needs p >= 5: at p = 3, n = 6 the Li_2(1/2) prefix loses a factor 3
    # although 3 is not a Wieferich prime.
    from fractions import Fraction
    li2 = sum(Fraction(2 ** (6 - m), m * m) for m in range(1, 7))
    assert li2 == Fraction(5587, 150) and v_p(li2.denominator, 3) == 1
    assert fermat_quotient(2, 3) != 0
    print("  Li_2(1/2) prefix at p=3, n=6: 5587/150, v_3 = 1 < 2 (order-two statement needs p >= 5)")
    # Order two at the Wieferich prime 1093: the full p^2 is lost, one factor survives.
    p = 1093
    for n in (1092 * p, p * p - 1):
        mod = p ** 3
        s = 0
        for ell in range(1, n // p + 1):
            s = (s + pow(2, n - ell * p, mod) * pow(ell * ell, -1, mod)) % mod
        val = 0 if s == 0 else max(0, 2 - v_p(s, p))
        print(f"  Li_2(1/2) prefix, p={p}, n={n}: v_p(den) = {val} (full power would be 2)")
        assert val == 1


def exact_loss_table(nmax: int) -> list[int]:
    """g(n) = D(n)/Q(n) for n <= nmax, with D(n) = lcm(1..n) and Q(n) the reduced
    denominator of R(n) = sum_{m<=n} 2^(n-m)/m.  The loss is log g(n)."""
    gs = [1] * (nmax + 1)
    L = 1
    num = 0  # R(n) = num / L
    for n in range(1, nmax + 1):
        newL = L * n // math.gcd(L, n)
        num = num * 2 * (newL // L) + newL // n
        L = newL
        gs[n] = math.gcd(num, L)
    return gs


def large_prime_drops(xmax: int) -> list[tuple[int, int]]:
    """All pairs (k, p) with p prime, k < p, k p <= xmax and p | U(k), where U(k)
    is the reduced numerator of A(k) = sum_{j<=k} 1/(j 2^j)."""
    primes = primes_up_to(xmax)
    drops = []
    for k in range(1, math.isqrt(xmax) + 1):
        lk = lcm_upto(k)
        U = sum((1 << (k - j)) * (lk // j) for j in range(1, k + 1))
        U //= math.gcd(U, (1 << k) * lk)
        assert math.log(U) < LOG_NUM_CONST * k
        for p in primes:
            if p <= k:
                continue
            if p * k > xmax:
                break
            if U % p == 0:
                drops.append((k, p))
    return drops


def section_average_loss(nmax: int, xmax: int) -> None:
    print(f"\n=== 6. Theorem 6.1: average denominator loss (exact for n <= {nmax}) ===")
    t0 = time.time()
    gs = exact_loss_table(nmax)
    losses = [math.log(g) for g in gs]
    assert gs[3] == 2      # R(3) = 16/3: the radix prime loses its factor 2
    for X in (100, 500, 1000, nmax):
        avg = sum(losses[1:X + 1]) / X
        mx = max(range(1, X + 1), key=lambda n: losses[n])
        zero = sum(1 for n in range(1, X + 1) if gs[n] == 1) / X
        print(f"  X={X}: average loss {avg:.3f} (Theorem 6.1 bound {3.5 * math.sqrt(X):.1f}); "
              f"max {losses[mx]:.3f} at n={mx}; share of n with no loss {zero:.3f}")
        assert avg <= 3.5 * math.sqrt(X)
    t1 = time.time()
    drops = large_prime_drops(xmax)
    drop_set = set(drops)
    print(f"  all {len(drops)} large-prime drop pairs (k, p) with k p <= {xmax} "
          f"found in {time.time() - t1:.1f}s; first: {drops[:10]}")
    # Prime-by-prime comparison.  Convention: p = 2 (the radix) and odd p with
    # p^2 <= n are "small" and cost at most their full lcm exponent; an odd p
    # with p^2 > n loses log p exactly when (floor(n/p), p) is a drop pair.
    primes = primes_up_to(nmax)
    for n in range(1, nmax + 1):
        g = gs[n]
        small_cost = 0.0
        for p in primes:
            if p > n:
                break
            e = v_p(g, p)
            if p == 2 or p * p <= n:
                full = int(math.log(n) / math.log(p) + 1e-12)
                assert e <= full
                small_cost += full * math.log(p)
            else:
                assert e == (1 if (n // p, p) in drop_set else 0), (n, p)
        assert math.log(g) <= small_cost + sum(math.log(p) for p in primes
                                               if p * p > n and p <= n and (n // p, p) in drop_set) + 1e-6
    print(f"  prime-by-prime loss decomposition verified for n <= {nmax} "
          f"({time.time() - t0:.1f}s)")
    total = 0.0
    for k, p in drops:
        nlo, nhi = k * p, min((k + 1) * p - 1, xmax)
        total += (nhi - nlo + 1) * math.log(p)
    print(f"  exact average large-prime loss over n <= {xmax}: {total / xmax:.4f} "
          f"(unconditional bound {LOG_NUM_CONST * math.sqrt(xmax):.1f}; "
          f"(1/2) log X = {0.5 * math.log(xmax):.2f})")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=200000)
    ap.add_argument("--group-limit", type=int, default=20000)
    ap.add_argument("--seeds", type=int, default=3)
    args = ap.parse_args()
    data = section_local(args.limit, args.seeds)
    section_exceptional(data, args.limit)
    section_global(args.group_limit)
    section_glaisher(5000)
    section_wieferich_denominators()
    section_average_loss(2000, 300000)
    print("\nAll Phase 19 classical checks passed.")


if __name__ == "__main__":
    main()
