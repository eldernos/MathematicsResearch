"""Exact certificates for the Gaussian logarithm relation and denominator theorems.

Run with Python 3. All ranks, cutoffs, rates and residues use integer or rational
arithmetic. A cell is indexed by v = floor(2x), even when x = N/p is not integral.
"""

from fractions import Fraction as Q
from math import gcd, isqrt


def real_sum(k, v, sign=1):
    """Real Taylor prefix at x = v/2, with phase sign/2^k."""
    return sum((Q(sign**j, j << (k*j)) for j in range(1, v//(2*k) + 1)), Q())


def gaussian_sum(t, v, sign=1):
    """Twice the real prefix, from powers of sign*(1+i) in Z[i]."""
    a, b = 1, 0
    total = Q()
    for j in range(1, v//(2*t-1) + 1):
        a, b = sign*(a-b), sign*(a+b)
        total += Q(2*a, j << (t*j))
    return total


def affine_row(v):
    """Constant and coefficients of a_1, g_2, g_3 when g_1=0."""
    a1, a2, a3, a4, a6 = (real_sum(k, v) for k in (1, 2, 3, 4, 6))
    g2, g3 = (gaussian_sum(t, v) for t in (2, 3))
    base = 2*a2 + a3 - a6
    return (base, a1-base, g2+a2-a4-base, g3+2*a2-2*a4-base)


def reduce_row(row, equations):
    """Eliminate the earlier pivot variables, in their order of insertion."""
    for column, pivot in equations:
        row = tuple(x-row[column]*y for x, y in zip(row, pivot))
    return row


def band_certificate(end, bound):
    """Return all affine spaces that the mass lower bound fails to exclude."""
    cells = [(affine_row(v), Q(2, v*(v+1))) for v in range(2, end)]
    leaves = []

    def visit(index, equations, spent):
        if spent >= bound:
            return  # Every candidate has strictly positive mass beyond the cutoff.
        if index == len(cells):
            leaves.append((equations, spent))
            return
        row, mass = cells[index]
        reduced = reduce_row(row, equations)
        column = next((k for k in (1, 2, 3) if reduced[k]), None)
        if column is None:
            visit(index+1, equations, spent + (mass if reduced[0] else 0))
            return
        pivot = tuple(x/reduced[column] for x in reduced)
        visit(index+1, equations + [(column, pivot)], spent)
        # Discarding the inequation here only enlarges the space still to test.
        visit(index+1, equations, spent+mass)

    visit(0, [], Q(0))
    return leaves


def normal_coefficients(a, u, b, c):
    """The coefficients (A1,A2,A3,A4,A6,G1,G2,G3) of a log 2 formula."""
    a6 = a+u+b+c-1
    a4 = -b-2*c
    return (a, -a4-2*a6, -a6, a4, a6, u, b, c)


def exact_rate(a, u, b, c):
    """Evaluate the infinite band sum with a certified positive tail."""
    *real, g1, g2, g3 = normal_coefficients(a, u, b, c)
    weight = sum(map(abs, real)) + 2*sum(map(abs, (g1, g2, g3)))
    end = 1
    while 2**end <= 8*weight:
        end += 1
    rate = Q(1, end)
    for v in range(1, 2*end):
        total = sum(w*real_sum(k, v) for w, k in zip(real, (1, 2, 3, 4, 6)))
        total += sum(w*gaussian_sum(t, v) for t, w in enumerate((g1, g2, g3), 1))
        if total:
            rate += Q(2, v*(v+1))
    return rate


def prime(p):
    return p > 1 and all(p % d for d in range(2, isqrt(p)+1))


def check_primitive_factors():
    # phi(n) >= sqrt(n) for odd n. Beyond this finite test phi(n) >= 16.
    small = [n for n in range(7, 256, 2)
             if sum(gcd(k,n) == 1 for k in range(1,n+1)) < 16]
    witnesses = {7: (113,29), 9: (37,109), 11: (397,2113), 13: (1613,53),
                 15: (61,1321), 21: (14449,1429)}
    assert small == list(witnesses)
    for n, pair in witnesses.items():
        for sign, p in zip((-1, 1), pair):
            numerator = 2**n + sign*2**((n+1)//2) + 1
            assert prime(p) and numerator % p == 0 and pow(2, 4*n, p) == 1
            assert all(pow(2, k, p) != 1 for k in range(1, 4*n))
    print("Paired primitive factors verified at", *small)


def check_optimum():
    # The worked two-Gaussian example removes two separated bands.
    def example(v):
        base, _, b, c = affine_row(v)
        return base - 2*b - 3*c

    assert [example(v) for v in range(3, 8)] == [-1, 0, Q(-3,4), 0, 0]
    assert min(example(v) for v in range(8, 18)) == Q(5,8)
    assert exact_rate(0, 0, -2, -3) == Q(29,60)
    leaves = band_certificate(72, Q(13, 30))
    survivors = {}
    for equations, mass in leaves:
        assert len(equations) == 3
        # At these leaves the reduced equations are already diagonal.
        point = [None]*3
        for column, row in equations:
            assert row[1:] == tuple(int(i == column) for i in (1, 2, 3))
            point[column-1] = -row[0]
        assert tuple(point) not in survivors
        survivors[tuple(point)] = mass
    assert survivors == {(0, 0, -2): Q(73, 180), (0, 0, -5): Q(7, 18)}
    for (a, b, c), mass in survivors.items():
        rate = exact_rate(a, 0, b, c)
        assert rate == {-2: Q(13, 30), -5: Q(5, 12)}[c]
        print(f"(a,u,b,c) = (0,0,0,{c}): finite mass {mass}, full rate {rate}")


def check_cutoffs():
    for v in range(81):
        for k in range(1, 11):
            assert real_sum(k,v) + real_sum(k,v,-1) == real_sum(2*k,v)
            assert gaussian_sum(k,v) + gaussian_sum(k,v,-1) == real_sum(4*k-2,v,-1)
    # Independent insertion test: reduce the real part of the phase power itself
    # and read its dyadic denominator. This includes t=1 and the zero coefficients.
    for t in range(1, 11):
        a, b = 1, 0
        signs = (1, 1, 0, -1, -1, -1, 0, 1)
        for j in range(1, 101):
            a, b = a-b, a+b
            power = Q(a, 2**(t*j))
            exponent = t*j - j//2
            assert power * 2**exponent == signs[j % 8]
            if power:
                assert power.denominator == 2**exponent


def check_frobenius():
    # Mixed signs and rational coefficients. With t=1 the largest index is 2N.
    def raw(v):
        return (Q(1, 3)*gaussian_sum(1,v) - 3*gaussian_sum(2,v,-1)
                + 5*gaussian_sum(4,v) + real_sum(3,v,-1))

    counts = {1: 0, 3: 0}
    for n in (7, 13, 28, 57, 100, 180):
        prefix = 2**n * raw(2*n)
        for p in range(5, 2*n+1):
            if prime(p) and p*p > 2*n:
                shadow = 2**n * raw(2*n//p)
                difference = p*prefix - shadow
                assert difference.denominator % p and difference.numerator % p == 0
                assert (prefix.denominator % p == 0) == (shadow.numerator % p != 0)
                counts[p % 4] += 1
    print("Split and inert prime-prefix tests:", counts[1], counts[3])


if __name__ == "__main__":
    check_primitive_factors()
    check_cutoffs()
    check_frobenius()
    check_optimum()
