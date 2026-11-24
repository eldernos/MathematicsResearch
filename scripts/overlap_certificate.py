#!/usr/bin/env python3
"""Exact enclosures of joint upper density for two geometric cell tests."""
import argparse
from fractions import Fraction as Q

from localized_certificate import certificate, discrepancy_bound


def failed_intervals(p, cells):
    intervals = []
    for (left, residue), right in zip(cells, [x for x, _ in cells[1:]] + [Q(p)]):
        if residue == 0:
            if intervals and intervals[-1][1] == left:
                intervals[-1] = (intervals[-1][0], right)
            else:
                intervals.append((left, right))
    return intervals


def copies(p, intervals, scale, cutoff):
    """All scaled intervals potentially visible in [cutoff,1], for scale <= 1."""
    result = []
    while p * scale >= cutoff:
        result.extend((a * scale, b * scale) for a, b in intervals)
        scale /= p
    return result


def intersection_length(fixed, moving, scale):
    i = j = 0
    length = Q(0)
    while i < len(fixed) and j < len(moving):
        a, b = fixed[i]
        c, d = moving[j]
        c, d = scale*c, scale*d
        length += max(0, min(b, d) - max(a, c))
        if b <= d:
            i += 1
        else:
            j += 1
    return length


def joint_upper_density(p, first, q, second, cutoff):
    """Enclose the upper density; distinct primes make the phase orbit dense."""
    if p == q or not 0 < cutoff < 1:
        raise ValueError("use distinct selected primes and a cutoff strictly between 0 and 1")
    if not first or not second:
        return Q(0), Q(0)
    best = Q(0)
    for a, pattern, b, other in ((p, first, q, second), (q, second, p, first)):
        moving = sorted(copies(b, other, Q(1), cutoff))
        for _, end in pattern:
            fixed = sorted((max(cutoff, x), min(Q(1), y))
                           for x, y in copies(a, pattern, 1/Q(end), cutoff)
                           if max(cutoff, x) < min(1, y))
            phases = {1/Q(b), Q(1)}
            for interval in fixed:
                for edge in interval:
                    for pair in moving:
                        for point in pair:
                            phase = edge / point
                            if 1/Q(b) < phase < 1:
                                phases.add(phase)
            best = max(best, *(intersection_length(fixed, moving, u) for u in phases))
    return best, min(Q(1), best + cutoff)


def merged(intervals):
    result = []
    for a, b in sorted(intervals):
        if a >= b:
            continue
        if result and a <= result[-1][1]:
            result[-1] = (result[-1][0], max(b, result[-1][1]))
        else:
            result.append((a, b))
    return result


def intersect(left, right):
    i = j = 0
    result = []
    while i < len(left) and j < len(right):
        a, b = left[i]
        c, d = right[j]
        if max(a, c) < min(b, d):
            result.append((max(a, c), min(b, d)))
        i += b <= d
        j += d <= b
    return result


def joint_box_bound(tests, cutoff, divisions):
    """Upper density for any finite collection; includes all possible phase vectors."""
    if not tests or not 0 < cutoff < 1 or divisions < 1:
        raise ValueError("require a nonempty family, cutoff in (0,1) and a positive mesh size")
    regions = [(cutoff, Q(1))]
    boxes = []
    for p, pattern in tests:
        bands = copies(p, pattern, Q(1), cutoff)
        row = []
        for j in range(divisions):
            u = Q(divisions+j*(p-1), p*divisions)
            v = u + Q(p-1, p*divisions)
            row.append(merged((max(cutoff, u*a), min(Q(1), v*b)) for a, b in bands))
        boxes.append(row)

    def search(k, remaining):
        if not remaining or k == len(boxes):
            return sum((b-a for a, b in remaining), Q(0))
        return max(search(k+1, intersect(remaining, envelope)) for envelope in boxes[k])

    return min(cutoff+search(0, regions),
               *(discrepancy_bound(p, indicator_cells(p, pattern))[0] for p, pattern in tests))


def indicator_cells(p, pattern):
    edges = {Q(1)}
    for a, b in pattern:
        edges.add(a)
        if b < p:
            edges.add(b)
    return [(u, int(not any(a <= u < b for a, b in pattern))) for u in sorted(edges)]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", type=int)
    parser.add_argument("p", type=int)
    parser.add_argument("q", type=int)
    parser.add_argument("support", type=int, nargs="+")
    parser.add_argument("--levels", type=int, nargs=2, default=(1, 1))
    parser.add_argument("--order", type=int, default=1)
    parser.add_argument("--cutoff", type=Q, default=Q(1, 10**10))
    parser.add_argument("--extra", type=int, nargs=2, action="append", default=[],
                        metavar=("PRIME", "LEVEL"), help="include another test using the phase box bound")
    parser.add_argument("--divisions", type=int, default=16)
    args = parser.parse_args()
    patterns = [failed_intervals(p, certificate(args.base, args.support, p, ell, args.order))
                for p, ell in zip((args.p, args.q), args.levels)]
    if args.extra:
        tests = list(zip((args.p, args.q), patterns))
        for p, level in args.extra:
            tests.append((p, failed_intervals(p, certificate(args.base, args.support, p, level, args.order))))
        print("Joint upper density ≤", joint_box_bound(tests, args.cutoff, args.divisions))
        raise SystemExit(0)
    low, high = joint_upper_density(args.p, patterns[0], args.q, patterns[1], args.cutoff)
    print(f"Joint upper density in [{low}, {high}]")
    print(f"Decimal approximations {float(low):.12f}, {float(high):.12f}")
