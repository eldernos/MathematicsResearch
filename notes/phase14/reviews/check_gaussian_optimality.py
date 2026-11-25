"""Independent rational-arithmetic checks for the Phase 14E review."""

from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import gcd, prod


def check_small_cyclotomic_norms():
    small = [n for n in range(7, 256, 2) if sum(gcd(i, n) == 1 for i in range(n)) < 16]
    norms = {}
    for n in range(1, max(small) + 1, 2):
        for sign in (1, -1):
            trace_sign = 1 if n % 8 in (1, 7) else -1
            norm = 1 + 2**n - sign*trace_sign*2**((n+1)//2)
            proper = prod(norms[d, sign] for d in range(1, n, 2) if n % d == 0)
            norms[n, sign], remainder = divmod(norm, proper)
            assert remainder == 0
    assert [(n, norms[n, 1], norms[n, -1]) for n in small] == [
        (7, 113, 29), (9, 37, 109), (11, 2113, 397),
        (13, 8321, 1613), (15, 61, 1321), (21, 1429, 14449),
    ]
    assert all(norms[n, sign] > n for n in small for sign in (1, -1))


def real_prefix(k, v):
    return sum((Q(1, j * 2**(k*j)) for j in range(1, v//(2*k) + 1)), Q())


def gaussian_prefix(t, v):
    # The roots 1+i and 1-i of X²-2X+2 give their power-sum recurrence.
    previous, trace = 2, 2
    total = Q()
    for j in range(1, v//(2*t-1) + 1):
        total += Q(trace, j * 2**(t*j))
        previous, trace = trace, 2*(trace-previous)
    return total


def row(v):
    """Affine coefficients in the order 1, a, u, b, c at x = v/2."""
    a1, a2, a3, a4, a6 = (real_prefix(k, v) for k in (1, 2, 3, 4, 6))
    g1, g2, g3 = (gaussian_prefix(t, v) for t in (1, 2, 3))
    base = 2*a2 + a3 - a6
    return base, a1-base, g1-base, g2+a2-a4-base, g3+2*a2-2*a4-base


def check_first_cutoffs(rows):
    matrix = [rows[2*n][1:] for n in (1, 2, 3, 4)]
    determinant = Q()
    for perm in permutations(range(4)):
        inversions = sum(i > j for i, j in combinations(perm, 2))
        determinant += (-1)**inversions * prod(r[k] for r, k in zip(matrix, perm))
    assert determinant == Q(67, 215040)
    assert rows[1] == (0, 0, 1, 0, 0)
    assert [rows[v][0:2] + rows[v][3:] for v in (2, 3, 4)] == [
        (0, Q(1, 2), 0, 0), (0, Q(1, 2), Q(1, 2), 0),
        (Q(1, 2), Q(1, 8), Q(1, 4), 0),
    ]
    # On a=4, u=0, b=-4, only c is free.
    assert [(f+4*a-4*b, c) for f, a, _, b, c in rows[5:10]] == [
        (0, Q(1, 4)), (Q(7, 24), Q(1, 8)), (Q(7, 24), Q(1, 8)),
        (Q(13, 24), 0), (Q(5, 8), 0),
    ]


def check_plane(rows):
    """Compute the finite mass on every type of point in the (b,c)-plane."""
    lines = defaultdict(Q)
    total = Q()
    for v in range(1, 60):
        constant, _, _, b, c = rows[v]
        weight = Q(2, v*(v+1))
        if constant or b or c:
            total += weight
        if b or c:
            scale = b or c
            lines[b/scale, c/scale, constant/scale] += weight

    vertices = set()
    for (b1, c1, d1), (b2, c2, d2) in combinations(lines, 2):
        det = b1*c2 - b2*c1
        if det:
            vertices.add(((c1*d2-c2*d1)/det, (d1*b2-d2*b1)/det))

    assert (len(lines), len(vertices)) == (33, 509)
    assert (total, total-max(lines.values())) == (Q(19, 30), Q(7, 15))
    masses = {}
    for b, c in vertices:
        removed = sum(weight for (x, y, z), weight in lines.items() if x*b+y*c+z == 0)
        masses[b, c] = total-removed
    assert {p: m for p, m in masses.items() if m <= Q(13, 30)} == {
        (0, -5): Q(23, 60), (0, -2): Q(2, 5), (0, Q(-265, 3)): Q(13, 30),
    }


def check_winners(rows):
    for c, early, positive_min, rate in [
        (-5, [Q(1, 2), Q(-3, 4), 0, 0], Q(125, 192), Q(5, 12)),
        (-2, [Q(1, 2), 0, Q(3, 8), Q(3, 8)], Q(259, 384), Q(13, 30)),
    ]:
        values = [f+c*coeff for f, _, _, _, coeff in rows]
        assert values[:4] == [0]*4 and values[4:8] == early
        assert min(values[8:18]) == positive_min
        # The review proves positivity for x >= 9. Its mass telescopes to 1/9.
        assert Q(1, 9) + sum(Q(2, v*(v+1)) for v in range(1, 18) if values[v]) == rate
        shifted = [(2**n * values[2*n]).denominator for n in (13, 18, 44)]
        assert shifted == ([15, 63, 101745] if c == -5 else [6, 90, 11115])


if __name__ == "__main__":
    rows = [row(v) for v in range(89)]
    check_small_cyclotomic_norms()
    check_first_cutoffs(rows)
    check_plane(rows)
    check_winners(rows)
    print("33 lines, 509 intersections. Unique rates at or below 13/30: 5/12 and 13/30.")
