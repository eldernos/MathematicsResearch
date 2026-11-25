"""Exact checks of quadratic plateau predictions and joint prime projections."""
from fractions import Fraction
from itertools import combinations
from math import gcd, prod


def two_order(n):
    if not n:
        raise ValueError("the valuation of zero is infinite")
    return (abs(n) & -abs(n)).bit_length() - 1


def delta_mod(b, j, bits):
    modulus = 1 << (bits + j)
    power = pow(pow(b, -1, modulus), 1 << j, modulus)
    assert (power - 1) % (1 << j) == 0
    return (power - 1) // (1 << j) % (1 << bits)


def quadratic_checks():
    count = 0
    for b in range(3, 22, 2):
        s = two_order(b*b - 1) - 1
        bits = 40
        modulus = 1 << bits
        ds = [delta_mod(b, j, bits) for j in range(1, bits + 2)]
        # The recurrence fixes all these low bits from the stabilization index on.
        lam = ds[-1]
        constant = (lam + sum(d - lam for d in ds)) % modulus
        assert two_order(lam) == s
        for k in range(2, 10):
            error = (sum(ds[:k])+ds[k-1]-k*lam-constant) % modulus
            assert two_order(error) == k-1+2*s
            start = 3 << (k-1)
            x = [Fraction(1, (1 << j) * b**(1 << j)) for j in range(1, k+1)]
            linear = sum(x)
            square = sum(u*v for i,u in enumerate(x,1) for j,v in enumerate(x,1)
                         if (1<<i)+(1<<j) <= start)
            for a in (-3, 1, 2, 4):
                for z in (-8, -4, -2, 0, 1, 2, 6):
                    numerator = (2*a+z+2*a*(k*lam+constant)) % (1<<k)
                    expected = (1 << (k-two_order(numerator))) if numerator else 1
                    for n in (start, (2 << k)-1):
                        y = b**n*(a*square+z*linear+7)
                        assert y.denominator == expected
                        count += 1
    return count


def crt_checks():
    count = 0
    y = Fraction()
    for n in range(1, 2001):
        w = 4*(n%2==0) + 3*(n%3==0) - 6*(n%6==0)
        y = 2*y + Fraction(w,n)
        primes = [p for p in range(max(5,n//3+1), n//2+1)
                  if all(p%d for d in range(2, int(p**0.5)+1))]
        for pair in combinations(primes[:4],2):
            m = prod(pair)
            fractions = [Fraction(pow(2,n-1,p),p) for p in pair]
            assert gcd((y-sum(fractions)).denominator,m)==1
            for h in ((1,1), (1,-1), (2,3)):
                a = sum(z*(m//p) for z,p in zip(h,pair))
                assert gcd(a,m)==1
                lhs = sum(z*f for z,f in zip(h,fractions))
                assert (lhs - Fraction(a*pow(2,n-1,m),m)).denominator == 1
                count += 1
    return count


if __name__ == '__main__':
    print('Exact quadratic cutoffs checked:', quadratic_checks())
    print('Exact joint CRT character arguments checked:', crt_checks())
