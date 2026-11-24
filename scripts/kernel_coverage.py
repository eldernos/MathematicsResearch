#!/usr/bin/env python3
"""Exact finite-block coverage for polynomial models of binary logarithm shifts."""
import argparse
from fractions import Fraction as Q
from heapq import heappop, heappush
from math import ceil, floor, gcd, lcm

from localized_certificate import cofactors, prime


def coefficients(power):
    """Integer coefficients of (8t²-8t+1)^power in increasing order."""
    terms = [1]
    for _ in range(power):
        new = [0] * (len(terms) + 2)
        for j, a in enumerate(terms):
            new[j] += a
            new[j + 1] -= 8 * a
            new[j + 2] += 8 * a
        terms = new
    return terms


def enclosure(n, coeff, scale, prefixes):
    center = sum((a * prefixes[n+j] for j, a in enumerate(coeff)), Q(0)) / scale
    radius = Q(1, scale*(n+1))
    return center - radius, center + radius


def constrained_integer_model(y, step, cancel, low, high):
    """Remove 'cancel' from the common denominator, minimizing worst unwrapped error."""
    if not step or low > high:
        raise ValueError("require a nonzero step and an ordered enclosure")
    common = lcm(y.denominator, step.denominator)
    if cancel < 1 or common % cancel:
        raise ValueError("the cancellation modulus must divide the common denominator")
    a, b = int(common*y), int(common*step)
    g = gcd(b, cancel)
    if a % g:
        return None
    period = cancel // g
    residue = (-a // g * pow(b // g, -1, period)) % period
    target = ((low + high)/2 - y)/step
    closest = round((target - residue)/period)
    h = residue + period*closest
    value = y + h*step
    return h, value, max(abs(low-value), abs(high-value))


def block_discrepancy(a, q, length):
    """Extreme interval discrepancy of the rational doubling orbit, including ties."""
    points = []
    for _ in range(length):
        points.append(a % q)
        a = 2*a % q
    points.sort()
    above = max((i+1)*q - length*z for i, z in enumerate(points))
    below = max(length*z - i*q for i, z in enumerate(points))
    return Q(above+below, length*q)


def endpoint_bound(end, edges):
    """Least undirected path cost with trivial unit edges between successive samples."""
    graph = [[] for _ in range(end+1)]
    for left, right, cost in edges:
        if not 0 <= left <= end or not 0 <= right <= end or cost < 0:
            raise ValueError("require valid endpoints and nonnegative certificate costs")
        graph[left].append((right, cost))
        graph[right].append((left, cost))
    best = list(range(end+1))
    # The unit-edge walk gives all these feasible initial distances.
    queue = [(d, d) for d in best]
    while queue:
        cost, vertex = heappop(queue)
        if cost != best[vertex]:
            continue
        if vertex == end:
            return cost
        neighbors = list(graph[vertex])
        if vertex:
            neighbors.append((vertex-1, 1))
        if vertex < end:
            neighbors.append((vertex+1, 1))
        for other, weight in neighbors:
            candidate = cost+weight
            if candidate < best[other]:
                best[other] = candidate
                heappush(queue, (candidate, other))


def scan(end, length, power, supports, tolerance=Q(1, 32), max_discrepancy=Q(1, 3)):
    if end < length or length < 2 or power < 1:
        raise ValueError("require end >= block length >= 2 and positive kernel power")
    if not 0 < tolerance < Q(1, 2) or not 0 < max_discrepancy <= 1:
        raise ValueError("invalid error or discrepancy budget")
    coeff = coefficients(power)
    scale = 17**power
    prefixes = [Q(0)]
    for k in range(1, end + len(coeff)):
        prefixes.append(2*prefixes[-1] + Q(1, k))
    grids = []
    for support in supports:
        if not support or any(p == 2 or not prime(p) for p in support):
            raise ValueError("each grid uses a nonempty set of odd primes")
        grids.append([q for q in cofactors(set(support), length**2+1) if q > 1])
    covered = set()
    all_starts = set()
    rows = []
    edge_costs = {}
    for grid in grids:
        starts, positions = [], set()
        for n in range(end-length+1):
            low, high = enclosure(n, coeff, scale, prefixes)
            midpoint = (low+high)/2
            cheapest = None
            for q in grid:
                # Radius tolerance/2^(length-1) is < 1/(2q) in the reported search.
                # Enumerating the full feasible interval also covers shorter user inputs.
                radius = tolerance/2**(length-1)
                a_min = ceil((high-radius)*q)
                a_max = floor((low+radius)*q)
                for a in range(a_min, a_max+1):
                    if gcd(a, q) != 1:
                        continue
                    error = 2**(length-1)*((high-low)/2 + abs(Q(a, q)-midpoint))
                    bound = block_discrepancy(a, q, length) + 2*error
                    if bound <= max_discrepancy and (cheapest is None or bound < cheapest):
                        cheapest = bound
            if cheapest is not None:
                starts.append(n)
                positions.update(range(n, n+length))
                edge_costs[n] = min(edge_costs.get(n, length), length*cheapest)
        all_starts.update(starts)
        # Earliest finish maximizes the number of disjoint equal-length intervals.
        stop = packed = 0
        for start in sorted(all_starts):
            if start >= stop:
                stop = start+length
                packed += length
        cost = endpoint_bound(end, [(n, n+length, c) for n, c in edge_costs.items()])
        rows.append((len(starts), len(positions), len(positions-covered), packed, Q(cost)/end))
        covered |= positions
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--end", type=int, default=1024)
    parser.add_argument("--length", type=int, default=12)
    parser.add_argument("--power", type=int, default=4)
    args = parser.parse_args()
    supports = [(3,), (5,), (13,), (3, 5, 13)]
    for support, row in zip(supports, scan(args.end, args.length, args.power, supports)):
        print(f"{support}: {row[0]} passing starts, {row[1]} positions, {row[2]} additional, {row[3]} cumulatively disjoint, "
              f"prefix discrepancy ≤ {ceil(10**6*row[4])/10**6:.6f}")
