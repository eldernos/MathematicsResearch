"""Exact finite checks for Euler's square and the higher-order tower (Phase 23)."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt


def sign(x):
    return (x > 0) - (x < 0)


def euler_square(limit):
    pent = [(0, 1)]
    j = 1
    while j * (3 * j - 1) // 2 <= limit:
        for m in (j * (3 * j - 1) // 2, j * (3 * j + 1) // 2):
            if m <= limit:
                pent.append((m, 1 if j % 2 == 0 else -1))
        j += 1
    coeff = [0] * (limit + 1)
    for m, s in pent:
        for n, t in pent:
            if m + n > limit:
                break
            coeff[m + n] += s * t
    return coeff


def check_hecke(coeff):
    """Independent Gaussian ideal count, prime powers and multiplicative signs."""
    bound = 12 * (len(coeff) - 1) + 1
    gaussian = [0] * len(coeff)
    prime_sign = {}
    for x in range(1, isqrt(bound) + 1, 2):
        for y in range(0, isqrt(bound - x * x) + 1, 2):
            norm = x * x + y * y
            if norm % 12 == 1:
                char = 1 if y % 3 == 0 else -1
                assert (x % 3 == 0) == (char == -1)
                gaussian[(norm - 1) // 12] += (2 if y else 1) * char
                prime_sign[norm] = char  # only prime keys used below
    assert gaussian == coeff
    spf = list(range(bound + 1))
    for p in range(2, isqrt(bound) + 1):
        if spf[p] == p:
            for m in range(p * p, bound + 1, p):
                if spf[m] == m:
                    spf[m] = p
    for n, value in enumerate(coeff):
        m = 12 * n + 1
        predicted = 1
        while m > 1:
            p = spf[m]
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p % 12 == 1:
                predicted *= (e + 1) * prime_sign[p] ** e
            elif e % 2:
                predicted = 0
            elif p % 12 == 5:
                predicted *= (-1) ** (e // 2)
        assert value == predicted
    for p in (13, 37, 61, 73, 97):
        for n in range((len(coeff) - 1 - (p - 1) // 12) // p + 1):
            m = 12 * n + 1
            exponent = 0
            while m % p == 0:
                m //= p
                exponent += 1
            transformed = coeff[p * n + (p - 1) // 12]
            assert (exponent + 1) * transformed == prime_sign[p] * (exponent + 2) * coeff[n]


def certified_tails(coeff, last):
    """Outward-rounded dyadic intervals for the infinite signed tails T_n."""
    scale = 1 << 180
    limit = len(coeff) - 1
    low, high = -(limit + 3) * scale, (limit + 3) * scale
    signs = [0] * (last + 1)
    digits = [0] * (last + 1)
    for n in range(limit - 1, -1, -1):
        head = coeff[n + 1] * scale
        low = (head + low) // 2
        high = -(-(head + high) // 2)
        if n <= last:
            assert sign(low) == sign(high) != 0
            assert 2 * low // scale == 2 * high // scale
            signs[n] = sign(low)
            digits[n] = (2 * low // scale) % 2
    return signs, digits


def check_euler():
    sizes = (4096, 16384, 32768)
    coeff = euler_square(sizes[-1] + 512)
    check_hecke(coeff)
    support = [i for i, a in enumerate(coeff) if a]
    last = next(m for m in support if m >= sizes[-1])
    oriented, digits = certified_tails(coeff, last)
    # Independent single dyadic enclosure of the first N binary digits.
    numerator = 0
    for a in coeff:
        numerator = 2 * numerator + a
    limit = len(coeff) - 1
    print("Euler finite measurements: N, support through N, positive, zero digits,"
          " positive oriented weight, positive coefficient weight, flipped weight")
    for n in sizes:
        certified = (numerator - limit - 3) >> (limit - n)
        assert certified == (numerator + limit + 3) >> (limit - n)
        zeros = n - (certified % (1 << n)).bit_count()
        assert zeros == digits[:n].count(0)
        positive_oriented = positive_coeff = flipped = 0
        truncated = Counter()
        measured = {}
        previous = 0
        for m in support[1:]:
            width = min(n, m) - previous
            s = sign(coeff[m])
            v = oriented[m - 1]
            assert oriented[previous:min(n, m)] == [v] * width
            positive_oriented += width * (v > 0)
            positive_coeff += width * (s > 0)
            flipped += width * (v != s)
            if m <= n:
                for h in (1, 3, 12, 32):
                    truncated[h] += min(width, h) * s
            if m >= n:
                break
            previous = m
        assert positive_oriented == oriented[:n].count(1)
        assert abs(positive_oriented - positive_coeff) <= flipped
        for h in truncated:
            # Sum of signed void indicators, computed directly from the coefficients.
            measured[h] = sum(sign(coeff[m]) for m in support[1:] if m <= n
                              for j in range(min(h, m))
                              if not any(coeff[m - j:m]))
        assert dict(truncated) == measured
        ends = [m for m in support if 0 < m <= n]
        gaps = [(m, m - old) for m, old in zip(ends, [0] + ends)]
        for h in truncated:
            # For each surviving layer lost, count earlier positive supported partners.
            pair_cost = sum(h - j for j in range(1, h) for m in ends
                            if j < m and coeff[m - j])
            for sigma in (-1, 1):
                same = [g for m, g in gaps if sign(coeff[m]) == sigma]
                assert h * len(same) - sum(min(g, h) for g in same) <= h + pair_cost
        num = sum(0 < m <= n for m in support)
        positive = sum(a > 0 for a in coeff[1:n + 1])
        row = (num, positive, zeros, positive_oriented, positive_coeff, flipped)
        expected = {4096: (1762, 884, 2119, 2106, 2076, 90),
                    16384: (6376, 3190, 8304, 8275, 8216, 323),
                    32768: (12187, 6095, 16545, 16510, 16422, 686)}
        assert row == expected[n]
        print(n, *row)


def block_value(b, digits):
    result = 0
    for digit in digits:
        result = b * result + digit
    return result


def check_frequency_constants():
    # Elementary rational majorants used after the asymptotic sieve estimate.
    assert sum(F(1, n * n) for n in range(1, 7)) + F(1, 6) < F(5, 3)
    assert F(5, 4) ** 4 <= 1 + F(8, 5)
    assert F(2, 3) * F(5, 3) * F(4, 3) < F(3, 2)
    assert 2 * 6 ** 3 * F(3, 2) ** 3 * 2 * F(5, 4) ** 2 < 5000
    assert F(1, 8 * 5000) == F(1, 40000)
    assert F(1, 2) - F(1, 40000) == F(19999, 40000)


def cyclic_counts(b, word, length):
    return Counter(block_value(b, (word[(i + j) % len(word)] for j in range(length)))
                   for i in range(len(word)))


def rotations(b, word):
    q = b ** len(word) - 1
    r = block_value(b, word)
    assert 0 < r < q
    values = []
    for _ in word:
        values.append(r)
        r = b * r % q
    return sorted(values), q


def discrepancy(b, word):
    values, q = rotations(b, word)
    k = len(word)
    residuals = [k * value - i * q for i, value in enumerate(values)]
    return F(q + max(residuals) - min(residuals), k * q)


def direct_discrepancy(b, word):
    """Enumerate positive arc excess, including tiny arcs and wrapped arcs."""
    values, q = rotations(b, word)
    mass = Counter(values)
    return max(F(sum(multiplicity for z, multiplicity in mass.items()
                     if (z - x) % q <= (y - x) % q), len(word)) - F((y - x) % q, q)
               for x in mass for y in mass)


def balanced_circuits(b, order, copies):
    """Enumerate tours starting at 0^(order-1), identifying equal parallel edges."""
    cells = b ** order
    vertices = cells // b
    left = [copies] * cells
    path = []

    def visit(v):
        if len(path) == cells * copies:
            if v == 0:
                yield tuple(path)
            return
        for digit in range(b):
            edge = b * v + digit
            if left[edge]:
                left[edge] -= 1
                path.append(digit)
                yield from visit(edge % vertices)
                path.pop()
                left[edge] += 1

    yield from visit(0)


def sharp_spectrum(b, order, k, *, exact_order=False):
    m = b ** order
    if k % m:
        return set()
    result = set()
    for word in balanced_circuits(b, order, k // m):
        if exact_order:
            longer = cyclic_counts(b, word, order + 1)
            if len(longer) == b * m and all(v * b * m == k for v in longer.values()):
                continue
        result.add(discrepancy(b, word))
    return result


def check_tower():
    for b, last_k, last_order in ((2, 9, 3), (3, 6, 2)):
        for k in range(2, last_k + 1):
            brute = [set() for _ in range(last_order)]
            exact = [set() for _ in range(last_order)]
            for word in product(range(b), repeat=k):
                if len(set(word)) == 1:
                    continue
                val = discrepancy(b, word)
                assert val == direct_discrepancy(b, word)
                for order in range(1, last_order + 1):
                    m = b ** order
                    counts = cyclic_counts(b, word, order)
                    if len(counts) != m or len(set(counts.values())) != 1:
                        continue
                    brute[order - 1].add(val)
                    longer = cyclic_counts(b, word, order + 1)
                    if len(longer) != b * m or len(set(longer.values())) != 1:
                        exact[order - 1].add(val)
                    assert val <= F(2, m) - F(2, m * (b ** k - 1))
            for order in range(1, last_order + 1):
                assert brute[order - 1] == sharp_spectrum(b, order, k)
                assert exact[order - 1] == sharp_spectrum(b, order, k, exact_order=True)
                assert bool(brute[order - 1]) == (k % (b ** order) == 0)
    for b, order in ((2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (4, 1)):
        m = b ** order
        for word in balanced_circuits(b, order, 1):
            assert cyclic_counts(b, word, order) == Counter(range(m))
            assert sorted(cyclic_counts(b, word, order + 1).values()) == [1] * m
            v, q = rotations(b, word)
            d = discrepancy(b, word)
            assert d == F(q + v[-1] - v[0], m * q)
            assert F(2, m + 1) <= d <= F(2, m) * (1 - F(1, b * m - 1))
            assert discrepancy(b, word * 2) == d
    examples = {(2, 1, 2): (1, F(2, 3), F(2, 3)),
                (2, 1, 4): (2, F(2, 5), F(2, 3)),
                (2, 2, 4): (1, F(2, 5), F(2, 5)),
                (2, 3, 8): (1, F(229, 1020), F(229, 1020)),
                (3, 2, 9): (12, F(17789, 88569), F(6226, 29523))}
    for (b, order, k), expected in examples.items():
        spec = sorted(sharp_spectrum(b, order, k))
        assert (len(spec), spec[0], spec[-1]) == expected
        print("Fixed tower (b,L,k), cardinality, minimum, maximum:",
              (b, order, k), len(spec), spec[0], spec[-1])
    for b, order in ((2, 3), (3, 2)):
        word = next(balanced_circuits(b, order, 1))
        values, q = rotations(b, word)
        for length in range(1, 6):
            scale = b ** length
            for v in values:
                cell = scale * v // q
                assert gcd(b, q) == 1 and scale * v % q
                x = F(v, q)
                for delta in (F(-1, 2 * q * scale), F(1, 2 * q * scale)):
                    assert (x + delta) * scale // 1 == cell
        # An actual sparse-digit rational truncation, with both signs of perturbation.
        # Points away from the grid must have the periodic word at the same start.
        last = 128
        u = sum((F(1, b ** j) for j in (2, 4, 8, 16, 32, 64, last)), F(0))
        c = F(block_value(b, word), q)
        for delta in (u, -u):
            orbit, perturbed, offsets = c, (c + delta) % 1, delta % 1
            for _ in range(last):
                distance = min(offsets, 1 - offsets)
                for length in (1, order, order + 1):
                    scale = b ** length
                    if distance * q * scale < 1:
                        assert orbit * scale // 1 == perturbed * scale // 1
                orbit, perturbed, offsets = ((b * y) % 1 for y in (orbit, perturbed, offsets))


def spliced_cycle(b, order, depth, periods, laps):
    """Insert rotation-orbit walks into one higher-order de Bruijn circuit."""
    seed = next(balanced_circuits(b, depth, 1)) * periods
    insertions = {}
    seen = set()
    for w in product(range(b), repeat=order):
        if w in seen:
            continue
        cycle = []
        v = w
        while v not in seen:
            seen.add(v)
            cycle.append(v[-1])
            v = v[1:] + v[:1]
        vertex = w[:-1]
        insertions.setdefault(vertex, []).extend(cycle * laps)
    result = []
    for i, digit in enumerate(seed):
        vertex = tuple(seed[(i - j) % len(seed)] for j in range(order - 1, 0, -1))
        result.extend(insertions.pop(vertex, []))
        result.append(digit)
    assert not insertions
    return tuple(result)


def check_mixture():
    """Exact masses on fine grids in the periodic part of the real-spectrum proof."""
    for b, order in ((2, 1), (2, 3), (3, 2)):
        m = b ** order
        words = list(product(range(b), repeat=order))
        for length in (order, order + 1, order + 3):
            grid = b ** length
            mass = Counter(block_value(b, (w[j % order] for j in range(length))) for w in words)
            for t in (F(0), F(2, 5), F(1)):
                probs = [(1 - t) / grid + t * F(mass[j], m) for j in range(grid)]
                assert sum(probs) == 1
                if length == order:
                    assert set(probs) == {F(1, m)}
                else:
                    assert probs[0] == (1 - t) / grid + t / m
                residuals = [F(0)]
                for p in probs:
                    residuals.append(residuals[-1] + p - F(1, grid))
                grid_d = max(residuals) - min(residuals)
                assert 2 * t * (F(1, m) - F(1, grid)) <= grid_d <= 2 * t / m
    for b, order, depth, periods, laps in ((2, 1, 3, 3, 18), (2, 3, 4, 2, 24),
                                          (3, 2, 3, 2, 30)):
        word = spliced_cycle(b, order, depth, periods, laps)
        m = b ** order
        k = len(word)
        assert k == periods * b ** depth + laps * m
        assert cyclic_counts(b, word, order) == Counter({i: k // m for i in range(m)})
        counts = cyclic_counts(b, word, depth)
        grid = b ** depth
        expected = Counter({i: periods for i in range(grid)})
        for v in product(range(b), repeat=order):
            j = block_value(b, (v[a % order] for a in range(depth)))
            expected[j] += laps
        # At most two splice junctions per inserted orbit alter depth-1 starts each.
        changed = sum(max(expected[i] - counts[i], 0) for i in range(grid))
        assert changed <= 2 * m * (depth - 1)
        assert cyclic_counts(b, word, order + 1)[0] * b * m != k
        d = discrepancy(b, word)
        t = F(laps * m, k)
        assert 2 * t * (F(1, m) - F(1, grid)) - F(changed, k) <= d
        assert d <= 2 * t / m + F(2, grid) + F(changed, k)


if __name__ == "__main__":
    check_euler()
    check_frequency_constants()
    check_tower()
    check_mixture()
    print("All exact finite checks passed.")
