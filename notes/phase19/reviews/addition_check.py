"""Independent review checks for notes/phase19/addition.md (commit ca020db).

Standard library only; deliberately does not import the author's scripts.
Run from the repository root with:  python -B notes/phase19/reviews/addition_check.py
"""

from fractions import Fraction as F
from itertools import combinations, product
import random


def circle_disc(points):
    """Extreme discrepancy over half-open circle arcs of a finite sample in [0,1).

    Positive excess suffices by complementation; the supremum over arcs that
    contain a given cyclic run of sorted atoms is count/N minus the run's span.
    """
    N = len(points)
    atoms = sorted(set(p % 1 for p in points))
    mult = {a: 0 for a in atoms}
    for p in points:
        mult[p % 1] += 1
    m = len(atoms)
    best = F(0)
    for i in range(m):
        count = 0
        for j in range(m):
            a = atoms[(i + j) % m]
            count += mult[a]
            span = (a - atoms[i]) % 1
            best = max(best, F(count, N) - span)
    return best


# ---------------------------------------------------------------- 1. polytope
def vertices_of_balance_polytope(n):
    """Brute-force vertices of {e in [0,1]^n : e_i <= sum_{j!=i} e_j}."""
    rows = []
    for i in range(n):
        r = [F(-1)] * n
        r[i] = F(1)
        rows.append((r, F(0)))                     # e_i - sum others <= 0
        u = [F(0)] * n
        u[i] = F(1)
        rows.append((u, F(1)))                     # e_i <= 1
        rows.append(([-x for x in u], F(0)))       # -e_i <= 0

    def solve(A, b):
        M = [list(a) + [c] for a, c in zip(A, b)]
        k = len(M)
        for col in range(k):
            piv = next((r for r in range(col, k) if M[r][col] != 0), None)
            if piv is None:
                return None
            M[col], M[piv] = M[piv], M[col]
            for r in range(k):
                if r != col and M[r][col]:
                    f = M[r][col] / M[col][col]
                    M[r] = [x - f * y for x, y in zip(M[r], M[col])]
        return tuple(M[i][k] / M[i][i] for i in range(k))

    verts = set()
    for combo in combinations(rows, n):
        x = solve([c[0] for c in combo], [c[1] for c in combo])
        if x is None:
            continue
        if all(sum(a * xi for a, xi in zip(r, x)) <= c for r, c in rows):
            verts.add(x)
    return verts


def check_polytopes():
    for n in range(2, 6):          # n = d+1 coordinates, d = 1..4 summands
        got = vertices_of_balance_polytope(n)
        want = {tuple(F(b) for b in v) for v in product((0, 1), repeat=n)
                if sum(v) != 1}
        assert got == want, (n, got ^ want)
    print("Polytope: brute-force vertices equal 0 and binary vectors with >=2 ones, d=1..4.")


# ------------------------------------------------ 2. inequalities on samples
def check_sample_inequalities(trials=400, seed=1):
    """The necessity inequalities hold for arbitrary paired circle samples."""
    rng = random.Random(seed)
    for _ in range(trials):
        N = rng.randint(1, 7)
        q = rng.choice((6, 8, 12, 30))
        # Bias toward atoms at zero so near-extremal cases occur.
        def sample():
            return [F(rng.choice((0, 0, rng.randrange(q))), q) for _ in range(N)]
        x, y, z = sample(), sample(), sample()
        D = circle_disc
        add = lambda u, v: [(a + c) % 1 for a, c in zip(u, v)]
        dx, dy, dxy = D(x), D(y), D(add(x, y))
        assert max(0, dx + dy - 1) <= dxy <= 1 - abs(dx - dy)
        # Doubling bound and the six-form inequality.
        assert D([2 * a % 1 for a in x]) <= 2 * dx
        u, v, w = add(x, y), add(x, z), add(y, z)
        assert D(u) + D(v) + D(w) <= 2 + 2 * min(dx, dy, D(z))
    print(f"Sample inequalities: {trials} random paired samples (not orbits) passed.")


def check_six_form_tightness():
    """The six-form bound is attained by finite samples, so it is not slack."""
    # x=y=z all equal and on a two-point sample {0,1/2}: compute both sides.
    x = [F(0), F(1, 2)]
    add = lambda u, v: [(a + c) % 1 for a, c in zip(u, v)]
    lhs = 3 * circle_disc(add(x, x))
    rhs = 2 + 2 * circle_disc(x)
    assert lhs == 3 and rhs == 3
    print("Six-form: equality at a finite sample (x=y=z on {0,1/2}).")


# --------------------------------------- 3. replicate the binary N=100 example
def next_pp(p, k):
    q = 1
    while q <= k:
        q *= p
    return q


def check_binary_example():
    b, p, t = 2, 3, 2
    alpha, beta, gamma = F(1, 4), F(1, 2), F(3, 8)
    s = max(F(0), (alpha + beta + gamma - 1) / 2)
    w = [s, beta - s, alpha - s, gamma - s, 1 - alpha - beta - gamma + 2 * s]
    dirs = ((0, 0), (1, 0), (0, 1), (1, -1), (1, 1))
    counts = [0] * 5
    kinds = [0]
    for k in range(1, 7):
        est = [F((wi * 20 * k).numerator // (wi * 20 * k).denominator, 20 * k) for wi in w]
        i = max(range(5), key=lambda j: k * est[j] - counts[j])
        assert k * w[i] > counts[i]
        counts[i] += 1
        kinds.append(i)
    sums, prev = [F(0), F(0)], [F(0), F(0)]
    for k in range(1, 7):
        q = next_pp(p, k)
        gap = t * k**3 - t * (k - 1)**3
        for j in range(2):
            target = F(dirs[kinds[k]][j] % q, q)
            c = (target - b**gap * prev[j]) % 1 or F(1)
            sums[j] += c / F(b)**(t * k**3)
            prev[j] = target
    tail = F(b, b - 1) * F(1, b**(t * 7**3 - 99))   # largest shift is 99
    out = []
    for j, z in enumerate((sums[0], sums[1], sums[0] + sums[1])):
        d = circle_disc([z * b**n % 1 for n in range(100)])
        eps = (2 if j == 2 else 1) * tail
        out.append((((d - 2 * eps) * 10**6).__floor__(), (-(-(d + 2 * eps) * 10**6).__floor__())))
    assert out == [(469999, 470000), (189722, 189723), (318888, 318889)], out
    print(f"Binary example: independent recomputation reproduces {out}.")
    return kinds


# ------------------------------------------- 4. (1),(3) outside Haar mixtures
def check_rows_one_three():
    orbit = [F(1, 3), F(2, 3)] * 6
    assert circle_disc(orbit) == F(2, 3)
    assert circle_disc([3 * a % 1 for a in orbit]) == 1
    print("Rows (1),(3): u=1/3 in base 2 gives (2/3, 1), off the flat-hull diagonal.")


def main():
    check_polytopes()
    check_sample_inequalities()
    check_six_form_tightness()
    kinds = check_binary_example()
    print(f"  scheduled types for blocks 0..6: {kinds}")
    check_rows_one_three()


if __name__ == "__main__":
    main()
