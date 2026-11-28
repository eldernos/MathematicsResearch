"""Exact finite checks for Phase 25 Track C. Run with python -B."""

from fractions import Fraction as F
from math import factorial, gcd, isqrt, prod


def factors(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = 1
    return result


def good_sign(p):
    for y in range(0, isqrt(p) + 1, 2):
        x = isqrt(p - y * y)
        if x * x + y * y == p:
            return 1 if y % 3 == 0 else -1
    raise AssertionError(p)


def cm_coefficient(index):
    value = 1
    for p, e in factors(index).items():
        if p % 12 == 1:
            value *= (e + 1) * good_sign(p) ** e
        elif p in (2, 3) or e % 2:
            return 0
        elif p % 4 == 1:
            value *= (-1) ** (e // 2)
    return value


def euler_square(limit):
    terms = [(0, 1)]
    for j in range(1, isqrt(2 * limit) + 1):
        for n in (j * (3 * j - 1) // 2, j * (3 * j + 1) // 2):
            if n <= limit:
                terms.append((n, (-1) ** j))
    coeff = [0] * (limit + 1)
    for n, a in terms:
        for m, b in terms:
            if n + m <= limit:
                coeff[n + m] += a * b
    return coeff


def atan_partial(d, last):
    return sum(F((-1) ** j, (2*j+1) * d ** (2*j+1)) for j in range(last+1))


def constants():
    pi_lo = 16*atan_partial(5, 5) - 4*atan_partial(239, 2)
    pi_hi = 16*atan_partial(5, 4) - 4*atan_partial(239, 1)
    root_hi = F(25067, 10000)
    assert 0 < pi_lo < pi_hi and 2*pi_hi < root_hi**2
    gamma_hi = sum(F(8*(-16)**j, factorial(j)*(4*j+1)) for j in range(81)) + F(1, 2**16)
    bad = [p for p in range(5, 101) if p % 12 in (5, 7, 11) and factors(p) == {p: 1}]
    product_hi = F(19208, 19207) * prod(1 + F(2, (p-1)*(p*p+1)) for p in bad)
    old_hi = F(3, 32) * root_hi * gamma_hi**2 * product_hi
    assert 8*old_hi < F(25431, 1000) < 26
    assert F(106103, 10**6) < 1/(3*pi_hi) < 1/(3*pi_lo) < F(106104, 10**6)
    assert F(1, 10) < 1/(3*pi_hi)
    for p in bad:
        assert (1-F(1,p-1)) * (1+F(1,p*(p-2))) == 1-F(1,p)
        for j in (1, 2, 3):
            u = sum(F(p-1, p**(e+1)) for e in range(0, 2*j, 2)) + F(1,p**(2*j))
            assert u == F(p, p+1) + F(1, (p+1)*p**(2*j))
    print("Finite certificate: old bound > 1/26; new bound 106103/10^6 < 1/(3 pi) < 106104/10^6.")


def sieve_local_checks():
    # One small prime with precision two, one sifted prime, and both unit and
    # nonunit square parts. Count accepted pairs directly over a CRT period.
    q, ell = 25, 7
    residues = [u for u in range(q) if gcd(u, q) == 1]
    small_density = F(5, 6) + F(1, 6*q)
    for v in (1, 5):
        total = F()
        for h in range(q*ell):
            accepted = sum((v*v*u - 12*h) % 5 != 0 or (v*v*u - 12*h) % q == 0
                           for u in residues)
            large_density = F(sum((v*v*u - 12*h) % ell != 0 for u in range(1, ell)), ell-1)
            assert large_density == (1 if h % ell == 0 else 1-F(1, ell-1))
            total += F(accepted, len(residues)) * large_density
        assert total/(q*ell) == small_density*(1-F(1, ell))


def euler_checks(limit=6000):
    coeff = euler_square(limit)
    sign = [(v > 0) - (v < 0) for v in coeff]
    assert coeff == [cm_coefficient(12*n+1) for n in range(limit+1)]
    ends = [i for i, value in enumerate(coeff) if value]
    gaps = list(zip(ends, ends[1:]))
    for p in (13, 37):
        shift = (p-1)//12
        for n in range((limit-shift)//p + 1):
            assert sign[p*n+shift] == good_sign(p)*sign[n]
    for h in (1, 3, 11, 25):
        layered = sum(sign[b] for b in ends[1:] for j in range(min(b,h))
                      if not any(coeff[b-j:b]))
        assert layered == sum(sign[b]*min(h,b-a) for a,b in gaps)
        for s in (-1, 1):
            selected = [b for b in ends[1:] if sign[b] == s and b % 3]
            eligible = {b for b in ends if b % 5}
            pairs = sum(h-d for b in selected for d in range(1,min(h,b+1)) if b-d in eligible)
            lost = sum(1 for a,b in gaps if sign[b] == s and b % 3 and a not in eligible)
            assert sum(b-a for a,b in gaps if sign[b] == s) >= h*(len(selected)-lost)-pairs
    band = {13, 37, 61, 73}
    for n in range(1, 12*limit+2, 12):
        if not cm_coefficient(n):
            continue
        divisors = [p for p in band if n % p == 0]
        marked = sum((F(1, 1+sum((n//p) % q == 0 for q in band)) for p in divisors), F())
        assert 0 <= marked <= 1
        if divisors and all(n % (p*p) for p in divisors):
            assert marked == 1
    print(f"Finite measurement: N={limit}, signed complete-gap sum/N =",
          F(sum(sign[b]*(b-a) for a,b in gaps), limit))


def theta_coefficients(limit):
    squares = [j*j for j in range(1, isqrt(limit)+1)]
    coeff = [1] + [0]*limit
    powers = []
    for _ in range(4):
        nxt = coeff.copy()
        for square in squares:
            for n in range(square, limit+1):
                nxt[n] += 2*coeff[n-square]
        powers.append(nxt)
        coeff = nxt
    return powers


def signed_weight(x):
    x = abs(x)
    count = 0
    while x:
        if x % 2:
            count += 1
            x -= 2 - x % 4
        x //= 2
    return count


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def sigma_valuation(p, e):
    return v2(p+1) + v2(e+1) - 1 if e % 2 else 0


def reduced_class_number(disc):
    # Reduced positive primitive forms, with the standard boundary convention.
    count = 0
    for a in range(1, isqrt((-disc)//3)+1):
        for b in range(-a, a+1):
            c, rem = divmod(b*b-disc, 4*a)
            if rem or a > c or (b < 0 and (abs(b) == a or a == c)):
                continue
            count += gcd(gcd(a, b), c) == 1
    return count


def prime_subseries_checks():
    # Expand the actual eta products directly at a finite Fourier precision.
    limit = 400
    log2_lo = 2*(F(1, 3) + F(1, 81))  # first two terms of 2 atanh(1/3)
    for power, step, inert_modulus, stretch, euler_stretch in (
        (4, 6, 3, 1, 5), (6, 4, 4, 2, 6), (8, 3, 3, 3, 7)
    ):
        coeff = [0, 1] + [0]*(limit-1)
        for offset in range(step, limit, step):
            for _ in range(power):
                for n in range(limit, offset, -1):
                    coeff[n] -= coeff[n-offset]
        weight = power//2
        assert weight-1 < 2*stretch*log2_lo
        assert step*(weight-1) < 2*euler_stretch*log2_lo
        for p in range(5, limit+1):
            if factors(p) != {p: 1}:
                continue
            if p % inert_modulus == inert_modulus-1:
                assert coeff[p] == 0
            assert coeff[p]**2 <= 4*p**(weight-1)
            assert 2*signed_weight(coeff[p]) <= abs(coeff[p]).bit_length()+2
    assert 1 < 2*log2_lo
    assert 6 < 9*log2_lo


def theta_checks(limit=2200):
    _, _, cube, fourth = theta_coefficients(limit)
    optimal = [0, 1]
    for n in range(2, max(fourth)+1):
        if n % 2:
            optimal.append(1 + min(optimal[n//2], optimal[n//2+1]))
        else:
            optimal.append(optimal[n//2])
    for n in range(1, limit+1):
        m = n
        while m % 4 == 0:
            m //= 4
        assert (cube[n] == 0) == (m % 8 == 7) and cube[n] == cube[m]
        exps = factors(n)
        odd_sigma = prod((p**(e+1)-1)//(p-1) for p,e in exps.items() if p != 2)
        assert fourth[n] == (8 if n % 2 else 24)*odd_sigma
        assert v2(fourth[n]) == 3 + sum(sigma_valuation(p,e) for p,e in exps.items() if p != 2)
        ramified = sum(p != 2 and e % 2 for p,e in exps.items())
        assert cube[n] % (1 << max(0, ramified-1)) == 0
        if cube[n]:
            d = prod(p for p,e in exps.items() if e % 2)
            correction = sum(sigma_valuation(p, e//2) for p,e in exps.items() if p != 2 and e % 2)
            assert v2(cube[n]) == v2(cube[d]) + correction
        if n > 1 and n % 8 == 1 and all(e == 1 for e in exps.values()):
            assert cube[n] == 12 * reduced_class_number(-4*n)
        for c in (cube[n], fourth[n]):
            assert optimal[c] == signed_weight(c) <= c.bit_count()
    for j, coeff in ((3, cube), (4, fourth)):
        for k in (1, 2, 4, 30):
            blocks = 1024
            guard = 64
            base = 1 << k
            head = 0
            for c in coeff[:blocks+1]:
                head = base*head + c
            guard_int = 0
            for c in coeff[blocks+1:blocks+guard+1]:
                guard_int = base*guard_int + c
            # Sum over h>=1 of (1+h)^2 2^-h is 11.
            unit = base**guard
            tail_hi = 11 * 81 * (blocks+guard+1)**2
            carry = guard_int//unit
            assert (guard_int+tail_hi)//unit == carry
            prefix = head+carry
            bitmask = (1 << (k*blocks))-1
            digits = (prefix & bitmask).bit_count()
            net = sum(c.bit_count() for c in coeff[:blocks+1]) + carry.bit_count() - prefix.bit_count()
            columns = {}
            operands = [(k*(blocks-n), c) for n,c in enumerate(coeff[:blocks+1])]
            for shift, value in [*operands, (0, carry)]:
                while value:
                    bit = value & -value
                    pos = shift + bit.bit_length()-1
                    columns[pos] = columns.get(pos, 0)+1
                    value -= bit
            incoming = column_carries = 0
            for pos in range(prefix.bit_length()+1):
                incoming = (incoming+columns.get(pos, 0))//2
                column_carries += incoming
            assert incoming == 0
            assert net == column_carries
            if base > 11*81*(blocks+1)**2:
                assert carry == 0 and digits == sum(c.bit_count() for c in coeff[1:blocks+1])
            print(f"Finite measurement: theta^{j}, k={k}, {blocks} blocks, ones={digits}/{k*blocks}.")


if __name__ == "__main__":
    constants()
    sieve_local_checks()
    euler_checks()
    theta_checks()
    prime_subseries_checks()
    print("All exact checks passed.")
