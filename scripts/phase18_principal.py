"""Exact finite checks for notes/phase18/principal.md and algebra.md.

Run with python -B scripts/phase18_principal.py. No third-party dependencies.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from math import ceil, comb, factorial, floor, gcd


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def valuation(n, p):
    if n <= 0:
        raise ValueError("valuation requires a positive integer")
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def floor_log(n, p):
    exponent = 0
    while p ** (exponent + 1) <= n:
        exponent += 1
    return exponent


def order(b, modulus):
    if modulus <= 1 or gcd(b, modulus) != 1:
        raise ValueError("order requires a unit and modulus greater than one")
    residue = b % modulus
    length = 1
    while residue != 1:
        residue = residue * b % modulus
        length += 1
    return length


def rational_mod(x, modulus):
    return x.numerator * pow(x.denominator, -1, modulus) % modulus


def discrepancy(points):
    """Extreme discrepancy via the two one-sided extrema of F(x)-x."""
    points = sorted(points)
    count = len(points)
    after = max(Fraction(j + 1, count) - x for j, x in enumerate(points))
    before = max(x - Fraction(j, count) for j, x in enumerate(points))
    return after + before


def check_groups_and_prefixes():
    groups = 0
    for b, m, h, c in product((2, 3, 8), (0, 4), range(1, 13),
                              (Fraction(-5, 6), Fraction(2, 25), Fraction(0))):
        repunit = (b**h - 1) // (b - 1)
        raw = sum(c / (repunit * b ** (m + j)) for j in range(1, h + 1))
        require(raw == c / b ** (m + h), (b, m, h, c))
        groups += 1

    shifts = 0
    for b, p, d in ((2, 3, 3), (8, 3, 2), (3, 5, 2)):
        t = order(b, p)
        positions = [t * k**d for k in range(1, 13)]
        for s in (0, 1, 3):
            truncated = Fraction(0)
            k = 0
            prefix = Fraction(0)
            for n in range(positions[-1] + 3):
                prefix = (b * prefix) % 1
                if k < len(positions) and positions[k] == n:
                    k += 1
                    weight = Fraction(1, p ** (s * valuation(k, p)))
                    prefix = (prefix + weight) % 1
                    truncated += weight / b**n
                    expected = b**n * p ** (s * floor_log(k, p))
                    require(truncated.denominator == expected, (b, p, s, k))
                    require((b**n * truncated) % 1 == prefix, (b, p, n))
                depth = s * floor_log(k, p) if k else 0
                require(prefix.denominator == p**depth, (b, p, s, n, prefix))
                shifts += 1
    return groups, shifts


def check_subgroups():
    cases = 0
    for b, p in ((2, 3), (8, 3), (7, 3), (4, 5), (3, 13)):
        t = order(b, p)
        a = valuation(b**t - 1, p)
        for e in range(1, 5):
            q = p**e
            period = order(b, q)
            require(period == t * p ** max(0, e - a), (b, p, e))
            for start in (1, q - 1):
                residues = [start]
                for _ in range(1, period):
                    residues.append(b * residues[-1] % q)
                if e >= a:
                    classes = {z % p**a for z in residues}
                    lifted = {z for z in range(q) if z % p**a in classes}
                    require(set(residues) == lifted and len(classes) == t, (b, p, e))
                points = [Fraction(z, q) for z in residues]
                require(discrepancy(points) <= Fraction(p**a, q), (q, b, start))
                for length in (1, period // 2 + 1, period + 1):
                    sample = (points + points)[:length]
                    error = length * discrepancy(sample)
                    require(error <= Fraction(length * p**a, q) + q, (q, length))
                cases += 1
    return cases


def check_schedules_and_combinations():
    cases = 0
    b, p, q = 2, 3, 5
    for schedule in (lambda k: 2 * factorial(k), lambda k: 2 * 3**k):
        positions = [schedule(k) for k in range(1, 8)]
        for s in (0, 1, 2):
            prefix = Fraction(0)
            terms = [Fraction(1, b**n * p ** (s * valuation(k, p)))
                     for k, n in enumerate(positions, start=1)]
            total = sum(terms)
            for k, (n, term) in enumerate(zip(positions[:-1], terms), start=1):
                prefix += term
                require(prefix.denominator == b**n * p ** (s * floor_log(k, p)),
                        (n, k, s))
                tail = total - prefix
                scale = b ** positions[k]
                require(Fraction(1, (k + 1)**s) <= scale * tail <= Fraction(b, b - 1),
                        (n, tail))
                cases += 1

    # Distinct schedules on different axes, two distinct orders on the 3-axis.
    rows = ((p, 3, -2, 2, 2), (p, 1, 4, 2, 2), (q, 2, 6, 4, 3))
    states = [Fraction(0) for _ in rows]
    counts = [0] * len(rows)
    for n in range(2100):
        for i, (prime, s, _, t, d) in enumerate(rows):
            states[i] = b * states[i] % 1
            if n == t * (counts[i] + 1)**d:
                counts[i] += 1
                states[i] = (states[i] + Fraction(1, prime ** (s * valuation(counts[i], prime)))) % 1
        combined = 7 + sum(row[2] * x for row, x in zip(rows, states))
        if counts[0] >= p:
            require(valuation(combined.denominator, p) == 3 * floor_log(counts[0], p),
                    (n, combined))
        if counts[2] >= q:
            require(valuation(combined.denominator, q) == 2 * floor_log(counts[2], q),
                    (n, combined))
        cases += 1
    return cases


def convolve(weights, r):
    polynomials = [{0: Fraction(1)}]
    for _ in range(r):
        coefficients = Counter()
        for n, coefficient in polynomials[-1].items():
            for m, w in weights.items():
                coefficients[n + m] += coefficient * w
        polynomials.append(coefficients)
    return polynomials


def check_convolutions():
    cases = 0
    for p, d, r in ((3, 3, 2), (3, 4, 3), (5, 3, 2)):
        b = 2
        t = order(b, p)
        shell = p**d
        thresholds = Counter(sum(a**d for a in row)
                             for row in product(range(1, p), repeat=r))
        passed = [sum(count for x, count in thresholds.items() if x <= u) % p != 0
                  for u in range(1, shell)]
        old = Fraction(sum(passed), shell - 1)
        rho = min((old + sum(passed[:y-1])) / y for y in range(1, shell + 1))
        if (p, d, r) == (3, 3, 2):
            require(rho == Fraction(9, 26), rho)
        if (p, d, r) == (3, 4, 3):
            require(rho == Fraction(13, 40), rho)

        # Directly convolve the rational weights, then query before/at/after
        # each scaled leading-residue boundary. Include both signs and lower degrees.
        for J, multiplier in ((1, -1), (2, p)):
            weights = {t * k**d: Fraction(1, p ** valuation(k, p))
                       for k in range(1, p ** (J + 1))}
            polynomials = convolve(weights, r)
            scale = t * p ** (d * J)
            cuts = {scale, scale * shell - 1}
            for x in thresholds:
                cuts.update(scale * x + delta for delta in (-1, 0, 1)
                            if scale <= scale * x + delta < scale * shell)
            common = p ** valuation(abs(multiplier), p)
            normalizer = p ** (r * J) // common
            for n in sorted(cuts):
                # Every weighted polynomial term is integral at the predicted scale.
                cleared = 0
                for degree, factor in ((r, multiplier), (r - 1, 1), (0, -2)):
                    for m, weight in polynomials[degree].items():
                        if m <= n:
                            integer = factor * normalizer * weight
                            require(integer.denominator == 1, (n, m, weight))
                            cleared += integer.numerator * pow(b, n - m, p)
                predicted = (multiplier // common * pow(b, n, p)
                             * sum(c for x, c in thresholds.items() if scale * x <= n))
                require((cleared - predicted) % p == 0, (p, d, r, n))
                cases += 1
    return cases


def check_factorial_plateaus():
    cases = 0
    b, p, k = 2, 3, 9
    modulus = p**10
    weights = {2 * factorial(i): Fraction(1, p ** valuation(i, p)) for i in range(1, k + 1)}
    nk = 2 * factorial(k)
    prev = 2 * factorial(k - 1)
    scale = p ** floor_log(k, p)
    old = sum(int(scale * weight) * pow(b, -n, modulus)
              for n, weight in weights.items() if n < nk)
    new = int(scale * weights[nk]) * pow(b, -nk, modulus)
    for r in range(1, 7):
        coefficients = convolve(weights, r)[-1]
        for l in range(1, r + 1):
            lower = l * nk + r * prev + 1
            upper = min((l + 1) * nk, 2 * factorial(k + 1)) - 1
            for n in (lower, upper):
                direct = sum(int(scale**r * weight) * pow(b, -m, modulus)
                             for m, weight in coefficients.items() if m <= n)
                model = sum(comb(r, j) * old ** (r - j) * new**j for j in range(l + 1))
                require((direct - model) % modulus == 0, (r, l, n))
                cases += 1
    return cases


def integer_root(n, degree):
    """Greatest integer a with a**degree <= n, using integer Newton steps."""
    if n <= 1:
        return n
    a = 1 << ((n.bit_length() + degree - 1) // degree)
    while True:
        smaller = ((degree - 1) * a + n // a ** (degree - 1)) // degree
        if smaller >= a:
            return a
        a = smaller


def square_certificate(p, d, s, layers):
    """Refine only failed cells; endpoints have denominator p**(d*layer).

    A failed cell stores the exact integer mass from already counted layers.
    All intervals are left closed. Counts include tuples at the left endpoint.
    """
    shell = p**d
    failed = [(1, shell, 0)]
    history = []
    for layer in range(layers):
        weight = p ** (s * layer)
        modulus = weight * p**s
        scale = 1 if layer == 0 else shell
        refined = []
        for left, right, previous in failed:
            left *= scale
            right *= scale
            mass = previous
            changes = Counter()
            for u in range(layer // 2 + 1):
                v = layer - u
                multiplicity = 1 if u == v else 2
                step = p ** (d * (layer - v))
                for a in range(1, p ** (u + 1)):
                    if a % p == 0:
                        continue
                    first = (a * p ** (layer - u)) ** d
                    if first >= right:
                        break
                    start = integer_root(max(0, left - first) // step, d)
                    stop = integer_root((right - 1 - first) // step, d)
                    mass += weight * multiplicity * (start - start // p)
                    for c in range(start + 1, stop + 1):
                        if c % p:
                            changes[first + step * c**d] += weight * multiplicity
            current = left
            for at in sorted(changes):
                if mass % modulus == 0:
                    refined.append((current, at, mass))
                mass += changes[at]
                current = at
            if mass % modulus == 0:
                refined.append((current, right, mass))
        failed = refined
        history.append(len(failed))
        if not failed:
            break
    denominator = shell ** (len(history) - 1)
    width = sum(right - left for left, right, _ in failed)
    previous = Fraction(width, shell - 1)
    worst = previous / denominator
    # In a failed interval the failure frequency is increasing, and on
    # the complement it is decreasing. Test ends and the shell boundaries.
    prefix = 0
    for left, right, _ in failed:
        prefix += right - left
        worst = max(worst, (previous + prefix) / right)
    return history, worst


def check_layer_counts():
    """Independent exhaustive tuple enumeration at small fixed precision."""
    cases = 0
    for p, d, r, maximum in ((3, 3, 2, 5), (3, 4, 3, 3), (5, 3, 2, 3)):
        shell = p**d
        unit = shell**maximum
        axis = [[(a * p ** (maximum - j)) ** d for a in range(1, p ** (j + 1)) if a % p]
                for j in range(maximum + 1)]
        events = {}
        for losses in product(range(maximum + 1), repeat=r):
            H = sum(losses)
            if H > maximum:
                continue
            for xs in product(*(axis[h] for h in losses)):
                at = max(unit, sum(xs))
                if at < unit * shell:
                    events.setdefault(at, Counter())[H] += 1
        mass = Counter()
        points = sorted({unit, unit * shell, *events})
        failed = 0
        prefix_worst = Fraction(0)
        ends = []
        for left, right in zip(points, points[1:]):
            mass.update(events.get(left, {}))
            H = min(mass)
            require(H <= r and 1 <= mass[H] < p**r, (p, d, r, H, mass[H]))
            if sum(count * p**j for j, count in mass.items()) % p ** (maximum + 1) == 0:
                failed += right - left
                ends.append((right, failed))
            cases += 1
        if r == 2:
            previous = Fraction(failed, shell - 1)
            prefix_worst = max([previous / unit] + [(previous + n) / y for y, n in ends])
            _, adaptive = square_certificate(p, d, 1, maximum + 1)
            require(adaptive == prefix_worst, (p, d, adaptive, prefix_worst))
    return cases


def check_late_shells():
    """Check the early counterexample and the first guaranteed square shell."""
    b, p, s, r, d = 2, 3, 2, 2, 3
    t = order(b, p)
    a = valuation(b**t - 1, p)
    threshold = r + max(0, (s - a + d - 1) // d)
    require(threshold == 3, threshold)
    rows = []
    for J in (threshold - 1, threshold):
        mod = p ** (r * s * J + 2)
        start = t * p ** (d * J)
        stop = start * p**d
        axis = [(t * k**d, p ** (s * (J - valuation(k, p))))
                for k in range(1, p ** (J + 1))]
        events = Counter()
        for n, first in axis:
            for m, second in axis:
                if n + m >= stop:
                    break
                events[max(start, n + m)] += first * second * pow(b, -(n + m), mod)
        mass = 0
        loss = 0
        for n in sorted(events):
            mass = (mass + events[n]) % mod
            require(mass != 0, (J, n, mod))
            loss = max(loss, valuation(mass, p))
        rows.append((J, loss))
    require(rows == [(2, 6), (3, 5)], rows)
    return rows


def check_factorial_limits():
    cases = 0
    for b, p, s, precision, v in ((2, 3, 1, 4, 5), (2, 3, 2, 5, 5),
                                   (8, 3, 1, 4, 5), (2, 5, 1, 3, 3)):
        modulus = p**precision
        period = order(b, modulus)
        t = order(b, p)
        lam = Fraction((p - 1) * p**s, p ** (s + 1) - 1)
        for m in (1, 2, p + 1, 2 * p + 1):
            k = m * p**v
            J = floor_log(k, p)
            common = p ** (s * (J - v))
            B = sum((Fraction(1, p ** (s * valuation(a, p))) for a in range(1, m)),
                    Fraction(0)) - m * lam
            require(-1 < B < 0, (p, s, m, B))
            old = 0
            fact = 1
            for i in range(1, k + 1):
                fact = fact * i % period
                value = (p ** (s * (J - valuation(i, p)))
                         * pow(b, -(t * fact), modulus)) % modulus
                if i < k:
                    old = (old + value) % modulus
            new = value
            require(old == rational_mod(common * B, modulus), (b, p, s, m, old, B))
            require(new == common % modulus, (b, p, s, m, new))
            for r in range(1, 9):
                for l in range(r + 1):
                    expected = sum(comb(r, j) * B ** (r - j) for j in range(l + 1))
                    require(expected != 0, (r, l, B))
                    actual = sum(comb(r, j) * old ** (r - j) * new**j
                                 for j in range(l + 1))
                    require(actual % modulus == rational_mod(common**r * expected, modulus),
                            (b, p, s, m, r, l))
                    cases += 1
    return cases


def check_product_rectangles():
    b, p, q = 2, 5, 3
    tp, tq = order(b, p), order(b, q)
    x_terms, y_terms = [], []
    cross = 0
    last = 1
    skips = 0
    cases = 0
    for j in range(1, 63):
        threshold = (j + 1) * last
        stride = tp if j % 2 else tq
        pos = (threshold + stride - 1) // stride * stride
        if j % 2:
            x_terms.append((pos, Fraction(1, p ** valuation(len(x_terms) + 1, p))))
        else:
            weight = Fraction(1, q ** valuation(len(y_terms) + 1, q))
            increment = rational_mod(weight, p) * pow(b, -pos, p)
            if (cross + increment) % p == 0:
                pos += tq
                skips += 1
                increment = rational_mod(weight, p) * pow(b, -pos, p)
            cross = (cross + increment) % p
            require(cross != 0, j)
            y_terms.append((pos, weight))
        if y_terms:
            depth = floor_log(len(x_terms), p)
            modulus = p ** (depth + 2)
            boundary = pos + last
            rectangle = 0
            before = 0
            for nx, wx in x_terms:
                for ny, wy in y_terms:
                    n = nx + ny
                    require(n <= boundary, (j, n, boundary))
                    term = rational_mod(p**depth * wx * wy, modulus) * pow(b, -n, modulus)
                    rectangle += term
                    if n < boundary:
                        before += term
            require(rectangle % p != 0, (j, rectangle))
            latest = (rational_mod(p**depth * x_terms[-1][1] * y_terms[-1][1], modulus)
                      * pow(b, -boundary, modulus))
            require((rectangle - before - latest) % modulus == 0, (j, boundary))
            cases += 1
        last = pos
    require(skips > 0, "the opposite-axis rejection branch should be exercised")
    return cases, skips


def check_every_product_cutoff():
    b, p, q, N = 2, 5, 3, 5000
    tp, tq = order(b, p), order(b, q)
    cases = 0
    for increasing in (False, True):
        x_axis = []
        for i in range(1, N):
            n = tp * (2**i if increasing else i**3)
            if n > N:
                break
            depth = i if increasing else valuation(i, p)
            x_axis.append((n, Fraction(1, p**depth)))
        y_axis = []
        cross = 0
        for j in range(1, N):
            weight = Fraction(1, q ** valuation(j, q))
            if increasing:
                lower = max(j**3, y_axis[-1][0] + 1 if y_axis else 1)
                m = (lower + tq - 1) // tq * tq
                if (cross + rational_mod(weight, p) * pow(b, -m, p)) % p == 0:
                    m += tq
            else:
                m = tq * j**3
                if j > 1:
                    weight *= Fraction(p, q**2)
            if m > N:
                break
            cross = (cross + rational_mod(weight, p) * pow(b, -m, p)) % p
            require(cross != 0, (increasing, j))
            y_axis.append((m, weight))
        insertions = Counter()
        for nx, x in x_axis:
            for ny, y in y_axis:
                if nx + ny <= N:
                    insertions[nx + ny] += x * y
        prefix = Fraction(0)
        for n in range(N + 1):
            prefix = (b * prefix + insertions[n]) % 1
            k = sum(nx <= n - y_axis[0][0] for nx, _ in x_axis)
            depth = k if increasing else floor_log(k, p)
            require(valuation(prefix.denominator, p) == depth, (increasing, n, k))
            cases += 1
    return cases


def flagship_enclosures():
    """Enclose the true discrepancy to six decimals by a rational truncation."""
    k = 9
    b = 2
    u = sum(Fraction(1, 3 ** valuation(i, 3) * b ** (2 * i**3))
            for i in range(1, k + 1))
    lines = []
    for N in (32, 128, 512, 1024):
        points = []
        y = u
        for _ in range(N):
            points.append(y)
            y = b * y % 1
        d = discrepancy(points)
        # All true orbits are within this circle radius of their model.
        radius = Fraction(b ** (N - 1) * b, (b - 1) * b ** (2 * (k + 1)**3))
        lower = (d - 2 * radius) * 10**6
        upper = (d + 2 * radius) * 10**6
        lines.append((N, floor(lower), ceil(upper)))
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--square-layers", type=int, default=14,
                        help="precision of the flagship square certificate (default 14)")
    args = parser.parse_args()
    if args.square_layers < 1:
        parser.error("--square-layers must be positive")
    groups, shifts = check_groups_and_prefixes()
    print(f"Geometric groups: {groups}; exact principal prefix shifts: {shifts}")
    print(f"Prime-power subgroup cases: {check_subgroups()}")
    print(f"Schedule approximants and mixed linear prefixes: {check_schedules_and_combinations()}")
    print(f"Polynomial convolution cutoffs and multipliers: {check_convolutions()}")
    print(f"Independently enumerated reflected tuple cells: {check_layer_counts()}")
    print(f"Square (s=2) shell and maximum pole loss: {check_late_shells()}")
    history, bound = square_certificate(3, 3, 1, args.square_layers)
    known = {1: Fraction(17, 26),
             14: Fraction(10893289026421, 20594407551577180074),
             21: Fraction(14035285166320179631, 47872170047321719707829651794)}
    if args.square_layers in known:
        require(bound == known[args.square_layers], (args.square_layers, bound))
    print(f"Flagship square failed cells: {history}; limsup bound: {bound}")
    print(f"Factorial partial convolution plateaus: {check_factorial_plateaus()}")
    print(f"Factorial normalized Taylor residue checks: {check_factorial_limits()}")
    rectangles, skips = check_product_rectangles()
    print(f"Independent-axis rectangles: {rectangles}; skipped multiples: {skips}")
    print(f"Products with an exact pole at every cutoff: {check_every_product_cutoff()}")
    for N, lower, upper in flagship_enclosures():
        print(f"Flagship N={N}: {lower}/1000000 <= D_N <= {upper}/1000000")


if __name__ == "__main__":
    main()
