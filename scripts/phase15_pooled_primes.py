#!/usr/bin/env python3
"""Measure the fixed mesh floor with exact cell choices and numerical characters."""

from cmath import exp
from fractions import Fraction
from math import pi, sin

from localized_certificate import prime


def good_primes(n):
    cutoff = 1
    while (cutoff + 1)**3 <= n:
        cutoff += 1
    return [p for p in range(3*n//4 + 1, n + 1) if p > 2 and prime(p)
            and all(pow(2, j, p) != 1 for j in range(1, cutoff+1))]


def pool(n, cells=8):
    if n < 1 or cells < 2:
        raise ValueError("a positive shell and at least two cells are required")
    primes = good_primes(n)
    if not primes:
        raise ValueError("the shell has no good primes")
    sample = n // 2 + 1
    angles = {p: [exp(2j*pi*k/p) for k in range(p)] for p in primes}
    tallies = [[0]*cells for _ in range(2)]
    moments = [[0j]*cells for _ in range(2)]
    targets = [0j, 0j]
    prefix = Fraction()
    for k in range(1, n + sample):
        prefix = (2*prefix + Fraction(1, k)) % 1
        if k < n:
            continue
        for model, y in enumerate((Fraction(), prefix)):
            targets[model] += exp(2j*pi*float(y))
            a, d = y.as_integer_ratio()
            for p in primes:
                residue = pow(2, k-p, p)
                # B = y - residue/p mod 1; endpoints use integer arithmetic.
                b = (a*p - d*residue) % (d*p)
                cell = cells*b//(d*p)
                tallies[model][cell] += 1
                moments[model][cell] += angles[p][residue]
    size = sample * len(primes)
    sinc = sin(pi/cells)/(pi/cells)
    rows = []
    for counts, sums, target in zip(tallies, moments, targets):
        assert sum(counts) == size
        variance = 1 - sum(abs(v)**2 / count for v, count in zip(sums, counts) if count)/size
        prediction = 1 - sinc**2*abs(target/sample)**2
        rows.append((variance, prediction))
    return rows


if __name__ == "__main__":
    print("K=8. N | target | pooled variance | prediction")
    for n in (256, 512, 1024):
        for label, (value, prediction) in zip(("zero", "log prefix"), pool(n)):
            print(f"{n:4} {label:12} {value:.6f} {prediction:.6f}")
