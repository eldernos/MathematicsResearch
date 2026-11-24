#!/usr/bin/env python3
"""Finite arithmetic checks for signed periodic weights and corrected log models."""

import argparse
from bisect import bisect_right
from fractions import Fraction
from math import gcd, isqrt
from localized_certificate import prime


def periodic_phases(base, p, weights):
    """Return cyclic power residues and the corresponding signed phase tests."""
    if base < 2 or not prime(p) or gcd(base, p) != 1 or not weights:
        raise ValueError('require a radix, a coprime prime and a nonempty period')
    d = len(weights)
    seen, residues = {}, []
    u = 1 % d
    while u not in seen:
        seen[u] = len(residues)
        residues.append(u)
        u = u * p % d
    cycle = residues[seen[u]:]
    # Horner evaluation of H(n) = sum A(n+i)/b^i / (1-b^-d).
    def amplitude(n):
        total = Fraction()
        for i in reversed(range(d)):
            total = Fraction(weights[(n+i) % d]) + total/base
        return total / (1-Fraction(1, base**d))
    amps = [amplitude(n) for n in cycle]
    return cycle, [sum(p**i * amps[(k-i) % len(amps)] for i in range(len(amps)))
                   for k in range(len(amps))]


def corrected_model(n, r):
    value = Fraction()
    for j in range(1, n+1):
        value = 2*value + Fraction(1, j)
    correction = Fraction(1, n+1)
    for j in range(r):
        value += correction
        correction *= Fraction(-j-1, n+j+2)
    return value


def model_shell(n):
    """Return denominator bit length and visits of the actual corrected model to [1/4,3/4)."""
    if n < 1:
        raise ValueError('positive shell length required')
    model = corrected_model(n, n)
    denominator = model.denominator
    residue = model.numerator % denominator
    hits = 0
    for _ in range(n):
        hits += denominator <= 4*residue < 3*denominator
        residue = (2*residue) % denominator
    return denominator.bit_length(), hits


def binomial_survivors(n):
    """Evaluate all partial-binomial-sum tests for primes in (n, 2n]."""
    partial, term = [1], 1
    for j in range(n):
        term = term*(n-j)//(j+1)
        partial.append(partial[-1]+term)
    return {p: partial[2*n-p] % p for p in range(n+1, 2*n+1) if prime(p)}


def log_bits(length):
    """Prove a binary cylinder using integer enclosures of sum 2^-j/j."""
    precision = length + 32
    while True:
        lower = sum((1 << (precision-j))//j for j in range(1, precision+1))
        # Each rounding error is <1, and the omitted scaled tail is <1.
        upper = lower + precision + 1
        shift = precision - length
        if lower >> shift == (upper-1) >> shift:
            return format(lower >> shift, f'0{length}b')
        precision += 32


def shell_statistics(n):
    """Count transitions on [n, 2n) and bound the mean square in units of log(2)^2.

    A transition with its next transition r places later has distance at least
    2^(-r-2) from 1/2. Concavity gives |cos(pi*x)| >= 2*dist(x, 1/2),
    so its spike costs at most (r+1)^2. One unit also covers a nontransition.
    """
    if n < 1:
        raise ValueError('shell size must be positive')
    length = 2*n+32
    while True:
        bits = log_bits(length)
        next_flip = length
        cost = hits = 0
        complete = True
        for i in reversed(range(n, length-1)):
            if bits[i] != bits[i+1]:
                if i < 2*n:
                    if next_flip == length:
                        complete = False
                        break
                    hits += 1
                    cost += (next_flip-i+1)**2
                next_flip = i
            elif i < 2*n:
                cost += 1
        if complete:
            return Fraction(hits, n), Fraction(cost, n)
        length += 32


def quadratic_statistics(length, cutoff):
    """Exact transition counts and least Fibonacci indices at shifts 0 through length-1."""
    if length < 1 or cutoff < 2:
        raise ValueError('positive length and Fibonacci index cutoff at least two required')
    scale = 1 << (length+1)
    scaled_square = scale*scale
    fractions = {
        'phi': (isqrt(5*scaled_square)-scale)//2,
        'sqrt(2)': isqrt(2*scaled_square)-scale,
        '1/sqrt(5)': isqrt(scaled_square//5),
    }
    transitions = {name: ((bits ^ (bits >> 1)) & ((1 << length)-1)).bit_count()
                   for name, bits in fractions.items()}
    fib = [1, 2]  # F_2, F_3, ...
    while fib[-1] < scale:
        fib.append(fib[-2]+fib[-1])
    small = 0
    for n in range(length+2):
        remainder = 1 << n
        parity = 0
        while remainder:
            index = bisect_right(fib, remainder)-1
            remainder -= fib[index]
            least = index+2
            parity ^= least % 3 != 2
        if n < length:
            small += least <= cutoff
        if n > 0:
            digit = parity ^ (least % 2 == 0)
            expected = (fractions['phi'] >> (length+1-n)) & 1
            if digit != expected:
                raise ArithmeticError(f'Zeckendorf and integer square-root digits differ at {n}')
    return transitions, small


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    tasks = parser.add_subparsers(dest='task', required=True)
    for name in ('binomial', 'shell', 'model'):
        tasks.add_parser(name).add_argument('n', nargs='+', type=int)
    periodic = tasks.add_parser('periodic')
    periodic.add_argument('base', type=int)
    periodic.add_argument('p', type=int)
    periodic.add_argument('weights', type=Fraction, nargs='+', help='A(0), A(1), ...')
    quadratic = tasks.add_parser('quadratic')
    quadratic.add_argument('n', nargs='+', type=int)
    quadratic.add_argument('--cutoff', type=int, default=4)
    args = parser.parse_args()
    if args.task == 'periodic':
        print('cycle, signed tests:', *periodic_phases(args.base, args.p, args.weights))
    elif args.task == 'binomial':
        for n in args.n:
            if n < 1:
                parser.error('positive n required')
            residues = binomial_survivors(n)
            cancelled = [p for p, r in residues.items() if r == 0]
            print(n, len(residues)-len(cancelled), 'of', len(residues), 'survive; cancelled:', cancelled)
    elif args.task == 'model':
        for n in args.n:
            bits, hits = model_shell(n)
            print(n, 'denominator bits', bits, 'first-frequency deficit ≥', Fraction(hits, n))
    elif args.task == 'quadratic':
        for n in args.n:
            flips, small = quadratic_statistics(n, args.cutoff)
            print(n, 'transitions', flips, 'least Fibonacci index <=', args.cutoff, 'at', small, 'shifts')
    else:
        for n in args.n:
            hits, moment = shell_statistics(n)
            print(n, 'transition fraction', hits, 'second moment ≤', moment, '* log(2)^2')
