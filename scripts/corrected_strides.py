"""Exact corrections and modular word tests for the two-stride binary logarithm."""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
from math import ceil, comb, floor, gcd, isqrt, lcm

from localized_certificate import prime
from strided_logarithm import shifted


def beta(m, j):
    return Q(1, (m+j+1)*comb(m+j, j))


def components(n):
    return ((4, n//2, 2 << (n % 2)), (-8, n//3, -(-1)**(n//3) * (1 << (n % 3))))


def orders(n, bits):
    """Guarantee error <= 2^-bits/(bits+1) through two independent beta bounds."""
    result = []
    for a, m, multiplier in components(n):
        j = 0
        while abs(multiplier)*beta(m, j)*(2 << bits)*(bits+1) > abs(a-1)**j:
            j += 1
        result.append(j)
    return tuple(result)


@dataclass(frozen=True)
class Model:
    common: int
    scale: int
    lcm_base: int
    weights: tuple
    correction_residue: int
    error: Q


def model(n, r, s):
    if min(n, r, s) < 0:
        raise ValueError("nonnegative position and correction orders required")
    end = max(n//2+r, n//3+s)
    base = lcm(*range(1, end+1))
    scale = 3**max(r, 2*s)
    weights = [0]*(end+1)
    for j in range(1, n//2+1):
        weights[j] += scale*(2 << (n-2*j))
    for j in range(1, n//3+1):
        weights[j] += scale*(-1)**(j+1)*(1 << (n-3*j))
    residue, error = 0, Q(0)
    for (a, m, multiplier), order in zip(components(n), (r, s)):
        for j in range(order):
            coefficient = multiplier*(-1)**j*(scale//(a-1)**(j+1))
            # base*beta(m,j) is integral by the binomial expansion in powers of t.
            cleared, remainder = divmod(base, beta(m, j).denominator)
            assert remainder == 0
            residue += coefficient*cleared
            for ell in range(j+1):
                weights[m+ell+1] += coefficient*(-1)**ell*comb(j, ell)
        error += abs(multiplier)*beta(m, order)/abs(a-1)**order
    return Model(scale*base, scale, base, tuple(weights), residue % scale, error)


def merge_residue(modulus, residue, new_mod, value):
    digit = (value-residue)*pow(modulus, -1, new_mod) % new_mod
    return modulus*new_mod, residue+modulus*digit


def sieve(data, cutoff):
    """Use full large prime powers and the extra power of three from the corrections."""
    if cutoff < 3:
        raise ValueError("cutoff must be at least three")
    return sieve_selected(data, (p for p in range(cutoff+1, len(data.weights)) if prime(p)))


def sieve_selected(data, primes):
    """The selector supplies distinct primes other than 3 from the common lcm."""
    modulus, residue = data.scale, data.correction_residue
    end = len(data.weights)-1
    for p in primes:
        power = p
        while power*p <= end:
            power *= p
        pole = 0
        for k in range(p, end+1, p):
            unit, divisor = k, 1
            while unit % p == 0:
                unit //= p
                divisor *= p
            pole += data.weights[k]*(power//divisor)*pow(unit, -1, power)
        value = (data.lcm_base//power)*pole % power
        modulus, residue = merge_residue(modulus, residue, power, value)
    return modulus, residue


def words(bits, changes):
    """All binary words of a given length with at most the indicated changes."""
    for k in range(changes+1):
        for positions in combinations(range(1, bits), k):
            word = 0
            for pos in positions:
                word ^= (1 << (bits-pos))-1
            yield word
            yield ((1 << bits)-1)^word


def word_test(n, bits, changes, cutoff):
    if not 0 <= changes < bits:
        raise ValueError("require 0 <= changes < bits")
    r, s = orders(n, bits)
    data = model(n, r, s)
    modulus, residue = sieve(data, cutoff)
    base = 1 << bits
    shift = data.common*base*data.error.numerator
    unit = data.error.denominator
    den = base*modulus*unit
    def survives(word):
        low = (word*data.common-base*residue)*unit-shift
        high = ((word+1)*data.common-base*residue)*unit+shift
        return -((-low)//den) <= high//den
    count = sum(survives(w) for w in words(bits, changes))
    return r, s, (data.common//modulus).bit_length(), count


def adjacent_grid_example():
    """Observe the same phase by advancing one model by a bit and restarting the next."""
    (n, t) = (512, 64)
    models = [model(start, *orders(start, t)) for start in (n, n+1)]
    omitted = ({2, 3, 5}, {2, 3, 7})
    grids = []
    for data, skip in zip(models, omitted):
        primes = (p for p in range(2, len(data.weights)) if p not in skip and prime(p))
        modulus, residue = sieve_selected(data, primes)
        grids.append((data.common//modulus, Q(residue, data.common)))
    size, first = grids[0]
    h = size//gcd(size, 2)
    k, second = grids[1]
    period = lcm(h, k)
    error = 2*models[0].error + models[1].error
    offset = 2*first-second
    lower, upper = ceil(period*(-error-offset)), floor(period*(error-offset))
    assert 2*period*error < 1 and lower == upper
    return h, k, gcd(h, k)


def exponent_exceeds(m_fraction, r_fraction, d, horizon):
    """Integer test for a strict beta entropy margin above horizon*log(2)."""
    den = lcm(m_fraction.denominator, r_fraction.denominator, horizon.denominator)
    m, r, h = (int(v*den) for v in (m_fraction, r_fraction, horizon))
    return (m+r)**(m+r)*d**r > m**m*r**r*2**h


def cost_certificate(h, r, s):
    assert exponent_exceeds(Q(1, 2), r, 3, h)
    assert exponent_exceeds(Q(1, 3), s, 9, h)
    # 2*atanh(1/2) = log(3); bound the remaining geometric tail explicitly.
    x = Q(1, 2)
    log3_upper = 2*(sum(x**(2*j+1)/(2*j+1) for j in range(13))
                    + x**27/(27*(1-x*x)))
    return max(Q(1, 2)+r, Q(1, 3)+s) + max(r, 2*s)*log3_upper


def validate():
    for n in range(3, 36):
        for r, s in ((0, 0), (1, 3), (4, 2)):
            data = model(n, r, s)
            y = shifted(n)
            for (a, m, factor), order in zip(components(n), (r, s)):
                y += factor*sum(Q((-1)**j, (a-1)**(j+1))*beta(m,j) for j in range(order))
            cleared = y*data.common
            assert cleared.denominator == 1
            assert cleared == sum(coef*(data.lcm_base//j)
                                  for j, coef in enumerate(data.weights) if j)
            for cutoff in (3, 5, max(3, isqrt(len(data.weights)-1))):
                modulus, residue = sieve(data, cutoff)
                assert cleared.numerator % modulus == residue


if __name__ == '__main__':
    validate()
    for h, r, s in ((Q(1, 2), Q(8857, 100000), Q(7169, 100000)),
                    (Q(1), Q(22365, 100000), Q(16931, 100000)),
                    (Q(2), Q(58202, 100000), Q(40077, 100000))):
        print('Coverage, certified upper cost:', h, float(cost_certificate(h,r,s)))
    for n, t, k, y in ((128, 40, 2, 4), (256, 48, 2, 5), (512, 64, 3, 5), (1024, 80, 3, 7)):
        print('N, word length, allowed transitions, cutoff; orders, lift bits, survivors:',
              n, t, k, y, word_test(n,t,k,y))
    print('Compatible adjacent grid sizes and surviving pair count:', adjacent_grid_example())
