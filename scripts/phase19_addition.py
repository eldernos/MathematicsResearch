"""Exact finite certificates for notes/phase19/addition.md. Run with python -B."""

from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import lcm

from phase18_programming import (
    coefficient,
    cycle_from,
    next_prime_power,
    prime_period_data,
    residue_discrepancy,
)


VERTICES = ((1, 1, 1), (0, 1, 0), (1, 0, 0), (0, 0, 1), (0, 0, 0))
DIRECTIONS = ((0, 0), (1, 0), (0, 1), (1, -1), (1, 1))


def weights(alpha, beta, gamma):
    s = max(Q(0), (alpha + beta + gamma - 1) / Q(2))
    return s, beta - s, alpha - s, gamma - s, 1 - alpha - beta - gamma + 2*s


def scheduled_types(masses, steps, approximate=False):
    counts = [0] * len(masses)
    for k in range(1, steps + 1):
        estimates = masses
        if approximate:
            # Rational approximants for these test inputs, with error < 1/(20k).
            scale = 20 * k
            estimates = [Q(w * scale // 1, scale) for w in masses]
        chosen = max(range(len(masses)), key=lambda i: k * estimates[i] - counts[i])
        assert k * masses[chosen] > counts[chosen]
        counts[chosen] += 1
        assert all(-4 <= count - k*w <= 1 for count, w in zip(counts, masses))
        yield chosen


def target_pair(kind, p, k):
    q = next_prime_power(p, k)
    return tuple(Q(a % q, q) for a in DIRECTIONS[kind])


def projection(pair, index):
    return sum(pair) if index == 2 else pair[index]


def check_polytope():
    admissible = 0
    grid = [Q(i, 12) for i in range(13)]
    for alpha, beta, gamma in product(grid, repeat=3):
        inside = max(0, alpha + beta - 1) <= gamma <= 1 - abs(alpha - beta)
        masses = weights(alpha, beta, gamma)
        assert (min(masses) >= 0) == inside
        assert sum(masses) == 1
        assert tuple(sum(w*v[j] for w, v in zip(masses, VERTICES))
                     for j in range(3)) == (alpha, beta, gamma)
        admissible += inside
    for kind, vertex in enumerate(VERTICES):
        assert weights(*vertex)[kind] == 1
        for q in (3, 5, 9):
            pair = tuple(Q(a, q) for a in DIRECTIONS[kind])
            for j in range(3):
                value = projection(pair, j) % 1
                assert (value == 0) == bool(vertex[j])
                assert value == 0 or value.denominator == q
    equal = (Q(1, 3),) * 3
    assert next(scheduled_types(weights(*equal), 1, approximate=True)) == 1
    for triple in (equal, (Q(29, 101), Q(42, 101), Q(46, 101)), *VERTICES):
        tuple(scheduled_types(weights(*triple), 220, approximate=True))
    print(f"Weights: {admissible} admissible points out of {len(grid)**3}; "
          "five vertices, exact ties and rounded comparisons passed.")


def orbit_residues(b, start, denominator, length):
    residue = start % denominator
    for _ in range(length):
        yield residue
        residue = b * residue % denominator


def check_cubic(b, p, triple, blocks):
    """Compare a truncated sum, its block model, and the infinite-series bounds."""
    masses = weights(*triple)
    t, v = prime_period_data(b, p)
    kinds = [0, *scheduled_types(masses, blocks, approximate=True)]
    states = [(Q(0), Q(0))]
    sums = [Q(0), Q(0)]
    for k, kind in enumerate(kinds[1:], 1):
        pair = target_pair(kind, p, k)
        n = t * k**3
        gap = n - t * (k-1)**3
        for j in range(2):
            c = coefficient(b, gap, states[-1][j], pair[j])
            assert 0 < c <= 1 and next_prime_power(p, k) % c.denominator == 0
            sums[j] += c / b**n
            assert sums[j] * b**n % 1 == pair[j]
        states.append(pair)

    max_n = t * blocks**3
    q = next_prime_power(p, blocks)
    denominator = lcm(*(value.denominator for value in sums))
    B = Q(b, b - 1)
    examples = []
    for j in range(3):
        projected = projection(sums, j)
        true_sample = list(orbit_residues(b, int(projected * denominator),
                                          denominator, max_n))
        scale = 2 if j == 2 else 1
        model = []
        retired = 0
        completed_error = Q(0)
        checks = 0
        for k in range(blocks):
            start = t*k**3
            stop = t*(k+1)**3
            projected_state = projection(states[k], j) % 1
            is_retired = VERTICES[kinds[k]][j]
            assert (projected_state == 0) == bool(is_retired)
            block_q = projected_state.denominator
            period = len(cycle_from(b, block_q, projected_state.numerator % block_q))
            full_error = min(Q(1), Q(p**v, block_q))
            bound = Q(0)
            for ell, residue in enumerate(orbit_residues(
                    b, int(projected_state * q), q, stop-start), 1):
                N = start + ell
                model.append(residue)
                retired += is_retired
                remainder = ell % period
                if not is_retired:
                    bound = (ell - remainder) * full_error + remainder
                H = completed_error + bound
                delta_model = residue_discrepancy(model, q)
                assert abs(delta_model * N - retired) <= H

                # Good-position bound for the actual infinite series, including
                # all omitted insertions after this rational truncation.
                displacement = Q(true_sample[N-1], denominator) - Q(residue, q)
                omitted = scale * B * Q(1, b**(t*(blocks+1)**3 - (N-1)))
                circle_distance = min(displacement % 1, (-displacement) % 1)
                assert circle_distance + omitted <= scale * B / b**(stop-(N-1))
                delta_trunc = residue_discrepancy(true_sample[:N], denominator)
                K = k + (N == stop)
                epsilon = Q(1, K+1)
                W = 0
                while 2*B > epsilon * b**W:
                    W += 1
                bad_budget = (K+1)*W
                # A coupled infinite orbit has discrepancy within 2*omitted
                # of this exact finite discrepancy (largest shift is N-1).
                assert abs(delta_trunc - Q(retired, N)) + 2*omitted <= (
                    (H + bad_budget) / N + 2*epsilon)
                if K:
                    h = t*(3*K*K + 3*K + 1)
                    assert abs(retired - N*triple[j]) <= t + 17*h
                if N == 100:
                    # Enclose the infinite-series value on a 10^-6 grid.
                    lower = (delta_trunc - 2*omitted) * 10**6
                    upper = (delta_trunc + 2*omitted) * 10**6
                    examples.append((lower // 1, -(-upper // 1)))
                checks += 1
            completed_error += bound
        assert checks == max_n
    return 3*max_n, examples


def polynomial_box(polynomial, rectangles):
    """Interval evaluation for positive coordinate boxes and integer coefficients."""
    lo = hi = Q(0)
    for (i, j), coefficient_ij in polynomial.items():
        lower = coefficient_ij * rectangles[0][0]**i * rectangles[1][0]**j
        upper = coefficient_ij * rectangles[0][1]**i * rectangles[1][1]**j
        lo += min(lower, upper)
        hi += max(lower, upper)
    return lo, hi


def check_sparse_avoidance():
    # Nominal vertex (1,1,1), where both coordinates would otherwise coincide.
    b, p, t = 2, 3, 2
    B = Q(2)
    states = (Q(0), Q(0))
    sums = states
    J = 0
    stages = []
    polynomials = [
        {(0, 0): 1},
        {(1, 0): 1},
        {(2, 0): 1, (1, 1): -2, (0, 2): 1},
        {(1, 0): 1, (0, 1): -1},
        {(0, 2): 37, (0, 1): -17, (0, 0): 2},
    ]
    for polynomial in polynomials:
        dx = max(i for i, _ in polynomial)
        dy = max(j for _, j in polynomial)
        k = 1
        while (k <= J or next_prime_power(p, k) <= max(dx, dy) or
               2*B*next_prime_power(p, k) >= b**(t*((k+1)**3-k**3))):
            k *= 2
        q = next_prime_power(p, k)
        candidates = []
        for a, c in product(range(dx+1), range(dy+1)):
            candidates.append(((Q(a, q), Q(c, q)), sums, states))
        L = J
        while True:
            L += 1
            n, following = t*L**3, t*(L+1)**3
            gap = n - t*(L-1)**3
            tail = B / b**following
            for index, (choice, previous_sum, previous_state) in enumerate(candidates):
                target = choice if L == k else (Q(0), Q(0))
                partial = tuple(value + coefficient(b, gap, old, new) / b**n
                                for value, old, new in zip(previous_sum, previous_state, target))
                candidates[index] = choice, partial, target
                if L >= k:
                    rectangle = [(value, value + tail) for value in partial]
                    lo, hi = polynomial_box(polynomial, rectangle)
                    if hi < 0 or lo > 0:
                        sums, states, J = partial, target, L
                        stages.append((k, L))
                        break
            else:
                continue
            break
    final_tail = B / b**(t*(J+1)**3)
    for polynomial in polynomials:
        lo, hi = polynomial_box(polynomial, [(value, value+final_tail) for value in sums])
        assert hi < 0 or lo > 0
    assert any(k < depth for k, depth in stages)
    print(f"Sparse avoidance: {len(stages)} permanent polynomial certificates; "
          f"(override, certification depth) {stages}.")


def balance_mixture(point):
    """Decompose a rational feasible deficit vector into binary supports."""
    total = sum(point)
    for i, value in enumerate(point):
        if 2*value == total:
            mixture = Counter({(0,) * len(point): 1-value})
            for j, weight in enumerate(point):
                if j != i and weight:
                    vertex = tuple(int(k in (i, j)) for k in range(len(point)))
                    mixture[vertex] += weight
            return mixture
    for i, value in enumerate(point):
        if value not in (0, 1):
            others = point[:i] + point[i+1:]
            lo = max(0, 2*max(others) - sum(others))
            hi = min(1, sum(others))
            assert lo < value < hi
            mixture = Counter()
            upper_weight = (value-lo) / (hi-lo)
            for endpoint, factor in ((lo, 1-upper_weight), (hi, upper_weight)):
                child = point[:i] + (endpoint,) + point[i+1:]
                for vertex, weight in balance_mixture(child).items():
                    mixture[vertex] += factor*weight
            return mixture
    return Counter({tuple(map(int, point)): Q(1)})


def check_many_summands():
    count = 0
    for m in range(2, 6):
        grid = [Q(i, 3) for i in range(4)]
        for point in product(grid, repeat=m):
            if 2*max(point) > sum(point):
                continue
            mixture = balance_mixture(point)
            assert all(w >= 0 for w in mixture.values()) and sum(mixture.values()) == 1
            for vertex in mixture:
                selected = [i for i, bit in enumerate(vertex) if bit]
                assert len(selected) != 1
                relation = [0] * m
                if selected:
                    for i in selected[:-1]:
                        relation[i] = 1
                    relation[selected[-1]] = 1-len(selected)
                projected = relation[:-1] + [sum(relation[:-1])]
                assert projected[-1] == -relation[-1]
                assert tuple(bool(x) for x in projected) == vertex
            recovered = tuple(sum(w*v[j] for v, w in mixture.items()) for j in range(m))
            assert recovered == point
            count += 1
    print(f"General sums: exact convex decompositions of {count} feasible "
          "prescriptions for one through four summands.")


def check_higher_forms():
    checked = 0
    for b, q in ((2, 9), (3, 8), (10, 7)):
        for N in (1, 2, 4, 7, 13):
            discs = []
            for a in range(q):
                points = list(orbit_residues(b, a, q, N))
                discs.append(residue_discrepancy(points, q))
            for x, y, z in product(range(q), repeat=3):
                pair_sum = sum(discs[a % q] for a in (x+y, x+z, y+z))
                assert pair_sum <= 2 + 2*min(discs[x], discs[y], discs[z])
                checked += 1
    assert residue_discrepancy([1, 2], 3) == Q(2, 3)
    print(f"Six-form obstruction: {checked} rational orbit prefixes passed.")


def check_padic_direction():
    # Surface H = {(s, t, s+t)}. The row (1,1,-1) annihilates H.
    b, p = 2, 3
    _, v = prime_period_data(b, p)
    rows = ((1, 1, -1), (1, 0, 0), (0, 1, 0), (-3, 1, 0), (0, 0, 3))
    valuations = (None, 0, 1, 2, 1)
    for e in range(1, 8):
        q = p**e
        theta = sum(p**exponent for exponent in (1, 2, 6) if exponent < e)
        for row, s in zip(rows, valuations):
            numerator = sum(a*c for a, c in zip(row, (1, theta, 1+theta))) % q
            reduced = Q(numerator, q)
            if s is None or e <= s:
                assert reduced == 0
            else:
                assert reduced.denominator == p**(e-s)
                cycle = cycle_from(b, reduced.denominator, reduced.numerator)
                assert residue_discrepancy(cycle, reduced.denominator) <= Q(p**(v+s), q)
    print("Subtorus projections: an annihilator and four active rows at seven depths passed.")


def weighted_discrepancy(masses):
    best = Q(0)
    for a, c in product(masses, repeat=2):
        span = (c-a) % 1
        mass = sum(w for r, w in masses.items() if (r-a) % 1 <= span)
        best = max(best, mass-span)
    # Independently check the inclusive-arc formula at atoms and across zero.
    grid = lcm(*(r.denominator for r in masses))
    count = lcm(*(w.denominator for w in masses.values()))
    points = [int(r*grid) for r, w in masses.items() for _ in range(int(w*count))]
    assert best == residue_discrepancy(points, grid)
    return best


def check_word_flows():
    b = 2
    components = [
        (Q(1, 3), ((0, 1), (1, 0), (1, 0))),
        (Q(1, 6), ((1, 1),)),
        (Q(1, 2), ((0, 0), (1, 0), (1, 1), (0, 1))),
    ]
    rows = ((1, 0), (0, 1), (1, 1), (2, -3), (0, 0))
    for L in (1, 2, 5, 8):
        flows = Counter()
        exact = [Counter() for _ in rows]
        grid = [Counter() for _ in rows]
        for weight, digits in components:
            period = len(digits)
            for offset in range(period):
                word = tuple(digits[(offset+i) % period] for i in range(L))
                mass = weight / period
                flows[word] += mass
                cycle = digits[offset:] + digits[:offset]
                point = [Q(sum(d[j]*b**i for i, d in enumerate(reversed(cycle))),
                           b**period-1) for j in range(2)]
                for row, law in zip(rows, exact):
                    law[sum(a*x for a, x in zip(row, point)) % 1] += mass
        incoming, outgoing = Counter(), Counter()
        for word, mass in flows.items():
            incoming[word[1:]] += mass
            outgoing[word[:-1]] += mass
            point = [Q(sum(d[j]*b**i for i, d in enumerate(reversed(word))),
                       b**L) for j in range(2)]
            for row, law in zip(rows, grid):
                law[sum(a*x for a, x in zip(row, point)) % 1] += mass
        assert sum(flows.values()) == 1 and incoming == outgoing
        for row, full_law, grid_law in zip(rows, exact, grid):
            full, truncated = weighted_discrepancy(full_law), weighted_discrepancy(grid_law)
            assert abs(full - truncated) <= Q(2*sum(map(abs, row)), b**L)
    print("Stationary word flows: five projected laws at four digit depths passed.")


def main():
    check_polytope()
    triple = (Q(1, 4), Q(1, 2), Q(3, 8))
    total, example = check_cubic(2, 3, triple, 6)
    for b, p, requested in ((10, 3, VERTICES[3]), (2, 7, VERTICES[4]),
                             (2, 3, (Q(1, 5), Q(1, 5), Q(1, 5)))):
        count, _ = check_cubic(b, p, requested, 4)
        total += count
    print(f"Cubic series: {total} projected prefixes checked; "
          f"binary N=100 intervals times 10^6: {example}.")
    check_sparse_avoidance()
    check_many_summands()
    check_higher_forms()
    check_padic_direction()
    check_word_flows()


if __name__ == "__main__":
    main()
