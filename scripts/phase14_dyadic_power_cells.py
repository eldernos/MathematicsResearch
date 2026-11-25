"""Exact dyadic power certificates. Standard library only.

Run with no options to verify degrees 3 through 15 and the positive-index
tests. --audit also checks every weight-bounded multiset without pruning.
--cells D prints the reduced denominator losses on every D-th power cell.
"""

import argparse
from bisect import bisect_right
from collections import defaultdict
from fractions import Fraction
from functools import cache
from itertools import product
from math import comb, factorial


# Bits, nonzero jump locations, sufficient positive-index shell, sharp witness.
CERTIFICATES = {
    3: (7, 9, 5, (9, 8)),
    4: (9, 4, 4, (1, 1)),
    5: (16, 37, 9, (65, 64)),
    6: (25, 208, 15, (149, 128)),
    7: (25, 131, 13, (169, 128)),
    8: (34, 340, 17, (1345, 1024)),
    9: (36, 296, 16, (513, 512)),
    10: (37, 133, 13, (19, 16)),
    11: (46, 632, 19, (561, 512)),
    12: (47, 242, 15, (79, 64)),
    13: (56, 977, 21, (257, 256)),
    14: (60, 906, 21, (375, 256)),
    15: (65, 1302, 23, (133, 128)),
}


def order(x):
    if x == 0:
        raise ArithmeticError("zero has infinite order")
    return (x & -x).bit_length() - 1


@cache
def mass(d, t, strict=False):
    """Exact integer sum of the infinite cut in Z_2, including one-sided cuts."""
    if d == 0:
        return int(t > 0 if strict else t >= 0)
    if t <= 0:
        return 0
    if t > d or (t == d and not strict):
        return (-1) ** d
    # Pick the coordinates at deficit zero. All others shift one step.
    return sum(
        comb(d, m) * 2 ** (d-m) * mass(d-m, 2*(t-m), strict)
        for m in range(min(d, int(t)) + 1)
    )


def cut_residues(d, bits):
    """Enumerate every nonzero jump of the ordered mass, including the shell start."""
    unit = 1 << bits
    jumps = defaultdict(int)
    first_shell = 0

    def visit(left, minimum, weight, location, ways):
        nonlocal first_shell
        if left == 0:
            largest = minimum-1
            first_shell = max(first_shell, largest+1, largest+bits-2-weight-order(ways))
            jumps[max(unit, location)] += ways << weight
            return
        budget = bits - 1 - weight
        mean, extra = divmod(budget, left)
        if mean < minimum:
            return
        # Among remaining tuples of weight at most budget, equalizing the
        # coordinates minimizes the insertion position. Both quantities are
        # measured on a grid with unit = 2^bits.
        least = (2*left-extra) * unit >> (mean+1)
        if location + least >= 2*unit:
            return
        for exponent in range(minimum, mean+1):
            step = unit >> exponent
            for count in range(1, left+1):
                new_location = location + count*step
                if new_location >= 2*unit:
                    break
                remaining = left - count
                new_weight = weight + count*exponent
                multiplicity = ways * comb(left, count)
                # Subsequent choices multiply multiplicity by integers.
                if new_weight + remaining*(exponent+1) + order(multiplicity) >= bits:
                    continue
                visit(remaining, exponent+1, new_weight, new_location, multiplicity)

    visit(d, 0, 0, 0, 1)
    cells = {}
    residue = 0
    for location, jump in sorted(jumps.items()):
        if jump % unit or location == unit:
            residue = (residue + jump) % unit
            cells[Fraction(location, unit)] = residue
    cells.setdefault(Fraction(1), 0)
    return cells, first_shell


def unpruned_residues(d, bits):
    """Audit all sorted tuples of weight < bits, without geometric or order pruning."""
    unit = 1 << bits
    jumps = defaultdict(int)
    permutations = factorial(d)
    leaves = 0

    def visit(left, previous, run, stabilizer, budget, position):
        nonlocal leaves
        if left == 0:
            leaves += 1
            if position < 2*unit:
                jumps[max(unit, position)] += (permutations//stabilizer) << (bits-1-budget)
            return
        for i in range(previous, budget//left+1):
            new_run = run+1 if i == previous else 1
            visit(left-1, i, new_run, stabilizer*new_run, budget-i, position+(unit >> i))

    visit(d, 0, 0, 1, bits-1, 0)
    residue = 0
    cells = {}
    for x, jump in sorted(jumps.items()):
        residue = (residue+jump) % unit
        if x == unit or jump % unit:
            cells[Fraction(x, unit)] = residue
    cells.setdefault(Fraction(1), 0)
    return cells, leaves


def certify(d):
    bits, count, first_shell, witness = CERTIFICATES[d]
    cells, threshold = cut_residues(d, bits)
    assert threshold == first_shell
    assert len(cells) == count and all(cells.values())
    witness = Fraction(*witness)
    assert cells[witness] == 1 << (bits-1)
    # The independent exact-integer recurrence agrees on both sides of every
    # retained jump. At the shell start the strict cut belongs to the old shell.
    previous = None
    for t, residue in sorted(cells.items()):
        assert mass(d, t) % (1 << bits) == residue
        if previous is not None:
            assert mass(d, t, True) % (1 << bits) == previous
        previous = residue
    assert mass(d, Fraction(2), True) % (1 << bits) == previous
    return cells


def shifted_prefix_mod(b, d, k, n, bits):
    """Compute 2^(d*k) b^(-n) R_(d,n) directly from positive-index terms."""
    mod = 1 << bits
    inverse = pow(b, -1, mod)
    units = [pow(inverse, 1 << j, mod) for j in range(k+1)]
    full = [0]
    for j in range(1, k+1):
        full.append((2*full[-1] + units[j]) % mod)

    @cache
    def prefix(arity, ceiling, cutoff):
        if arity == 0:
            return int(cutoff >= 0)
        if ceiling == 0 or cutoff < 2*arity:
            return 0
        step = 1 << ceiling
        if cutoff >= arity*step:
            return pow(full[ceiling], arity, mod)
        # Choose how often the *largest positive index* occurs.
        return sum(
            comb(arity, m) * (1 << (arity-m)) * pow(units[ceiling], m, mod)
            * prefix(arity-m, ceiling-1, cutoff-m*step)
            for m in range(min(arity, cutoff//step)+1)
        ) % mod

    return prefix(d, k, n)


def test_quartic():
    checked = 0
    for k in range(1, 10):
        shell = 1 << k
        insertions = defaultdict(int)
        # An independently expanded positive-index shifted prefix with radix factors.
        for js in product(range(1, k+1), repeat=4):
            insertions[sum(1 << j for j in js)] += 1 << (4*k-sum(js))
        for b in (3, 5, 7):
            numerator = 0
            for n in range(2*shell):
                numerator = b*numerator + insertions[n]
                if n < shell:
                    continue
                den_order = 0 if not numerator else max(0, 4*k-order(numerator))
                if k < 3:
                    expected = 0
                elif k == 3:
                    expected = 4 if n < 12 else 5 if n < 14 else 3
                else:
                    expected = 4*k - (7 if 6*shell <= 4*n < 7*shell else 8)
                assert den_order == expected
                checked += 1
    return checked


def test_positive_degree15(cells):
    bits = CERTIFICATES[15][0]
    endpoints = sorted(cells)
    checked = 0
    for b, k in ((3, 23), (5, 24), (7, 70)):
        shell = 1 << k
        # Both sides of representative jumps, the worst loss, and shell edges.
        points = {shell, 2*shell-1, shell*133//128}
        for t in endpoints[::97]:
            n = int(t*shell)
            points.update((max(shell, n-1), n))
        for n in sorted(points):
            t = Fraction(n, shell)
            predicted = cells[endpoints[bisect_right(endpoints, t)-1]]
            assert shifted_prefix_mod(b, 15, k, n, bits) == predicted
            checked += 1
    # Exhaust all positions on two pre-asymptotic shells. Here use differently
    # organized computations and keep all bits up to the clearing denominator.
    for k in (5, 6):
        shell = 1 << k
        insertions = {0: 1}
        for _ in range(15):
            nxt = defaultdict(int)
            for n, value in insertions.items():
                for j in range(1, k+1):
                    at = n + (1 << j)
                    if at < 2*shell:
                        nxt[at] += value << (k-j)
            insertions = nxt
        b = 3
        modulus = 1 << (15*k)
        shifted = 0
        for n in range(2*shell):
            shifted = b*shifted + insertions.get(n, 0)
            if n >= shell:
                raw = shifted_prefix_mod(b, 15, k, n, 15*k)
                assert shifted % modulus == raw*b**n % modulus
                checked += 1
    return checked


def verify_zero_cells():
    # On the upper square cell every point but the origin occurs. The early
    # cell has order two. The same corner geometry lives in every even box.
    assert cut_residues(2, 3)[0] == {Fraction(1): 4, Fraction(3, 2): 0}
    for d in (2, 4, 6, 8, 14):
        assert mass(d, Fraction(2*d-1, 2)) == mass(d, Fraction(d), True) == 0
        for b in (3, 5, 7):
            a = 0
            for k in range(1, 8):
                a = 2*b**(1 << (k-1))*a + 1
                if k >= 2:
                    assert order(a**d-1) == k+order(d)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells", type=int, choices=CERTIFICATES)
    parser.add_argument("--audit", action="store_true", help="also enumerate all weight-bounded multisets")
    args = parser.parse_args()
    if args.cells:
        previous = None
        cells = certify(args.cells)
        if args.audit:
            audit, _ = unpruned_residues(args.cells, CERTIFICATES[args.cells][0])
            assert audit == cells
        for t, residue in sorted(cells.items()):
            loss = order(residue)
            if loss != previous:
                print(t, loss)
            previous = loss
        return
    for d, (bits, count, first_shell, _) in CERTIFICATES.items():
        cells = certify(d)
        if args.audit:
            audit, leaves = unpruned_residues(d, bits)
            assert cells == audit
            print(f"audited {leaves} multisets", end="; ")
        print(f"degree {d:2d}: {count:4d} jump locations, maximum loss {bits-1}, from shell {first_shell}")
    verify_zero_cells()
    print("Positive-index quartic checks:", test_quartic())
    print("Positive-index degree-15 checks:", test_positive_degree15(cells))


if __name__ == "__main__":
    main()
