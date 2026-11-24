"""Exact prime-band and binary digit checks for the Gaussian logarithm prefixes."""

from collections import defaultdict
from fractions import Fraction as Q
from math import isqrt

# Re(((1+i)/8)^j) = signs[(j-1) % 8] / 2^ceil(5j/2).
GAUSSIAN = (1, 0, -1, -1, -1, 0, 1, 1)


def terms(twice_cutoff, k):
    """Yield (coefficient, binary exponent, Taylor index) at a half-integral cutoff."""
    for j in range(1, twice_cutoff // 4 + 1):
        yield 2, 2*j, j
    for j in range(1, twice_cutoff // 6 + 1):
        yield (1+k)*(-1)**(j+1), 3*j, j
    for j in range(1, twice_cutoff // 8 + 1):
        yield 2*k, 4*j, j
    for j in range(1, twice_cutoff // 5 + 1):
        yield -2*k*GAUSSIAN[(j-1) % 8], (5*j+1)//2, j


def short_sum(twice_cutoff, k):
    return sum((Q(w, j << e) for w, e, j in terms(twice_cutoff, k)), Q(0))


def prefix(n, k):
    return sum((Q(w << (n-e), j) for w, e, j in terms(2*n, k)), Q(0))


def optimal_parameter_check():
    # Each interval [v/2,(v+1)/2) of the reciprocal scale x=N/p has this prime mass.
    losses = defaultdict(Q)
    for v in range(4, 200):
        base = short_sum(v, 0)
        slope = short_sum(v, 1) - base
        assert base > 0
        if slope:
            losses[-base/slope] += Q(2, v*(v+1))
    assert losses[5] == Q(1, 12)
    runner_up = max(mass for k, mass in losses.items() if k != 5)
    assert runner_up == Q(1, 15) and runner_up + Q(1, 100) < Q(1, 12)
    return losses[5], runner_up


def digit_word(start, width, k):
    """First width bits of the fractional part of 2^start log(2). k=None uses BBP."""
    q = width + (start+width+1).bit_length() + 8
    while True:
        s = start + q
        if k is None:
            summands = ((1, j, j) for j in range(1, s+1))
            tail_bound = 1
        else:
            summands = terms(2*s, k)
            tail_bound = 2 + abs(1+k) + 4*abs(k)
        total = count = 0
        for w, e, j in summands:
            residue = pow(2, s-e, j << q)
            total += w*residue // j
            count += 1
        low = (total-tail_bound) >> (q-width)
        high = (total+count+tail_bound) >> (q-width)
        if low == high:
            return low % (1 << width)
        q += 16


def check_residues(n, k):
    y = prefix(n, k)
    primes_checked = 0
    for p in range(3, n//2 + 1, 2):
        if p*p <= n//2 or any(p % d == 0 for d in range(3, isqrt(p)+1, 2)):
            continue
        # floor(2n/p) determines the four actual short-prefix lengths.
        model = (1 << n) * short_sum(2*n//p, k)
        difference = p*y - model
        assert difference.denominator % p and difference.numerator % p == 0
        if (k == 5 and n < 4*p and 3*p <= n) or (k == 2 and 5*p <= 2*n < 6*p):
            assert y.denominator % p
        primes_checked += 1
    return y.denominator.bit_length(), primes_checked


if __name__ == '__main__':
    print('Truncated lost prime mass, best and runner-up:', *optimal_parameter_check())
    for start in (256, 1024, 4096):
        print('Start, (denominator bits, large primes checked) for k=2,5:',
              start, check_residues(start, 2), check_residues(start, 5))
    for start in (0, 1000, 10000, 100000):
        word = digit_word(start, 64, 5)
        assert word == digit_word(start, 64, None)
        print(f'Binary start {start}, 64 bits in hex: {word:016X}')
