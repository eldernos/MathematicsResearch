#!/usr/bin/env python3
"""Finite Fredholm and product diagnostics on certified binary cylinders."""

from fractions import Fraction
from math import cos, exp, fsum, isqrt, ldexp, log, log1p, pi, sin

from discrepancy_experiments import log_bits


def shell_bits(length, signed):
    """Enclose a Stoneham series or signed shells with coefficients c_j = 1,0,1,0,... ."""
    total = Fraction()
    j = 0 if signed else 1
    while True:
        exponent = 3**j
        if exponent > length + 4:
            # All later exponents are distinct and |a_j / 3^j| <= 3.
            tail = Fraction(6, 1 << exponent)
            scale = 1 << length
            lo = (total - tail) * scale
            hi = (total + tail) * scale
            if lo // 1 == hi // 1:
                return format((lo // 1) % scale, f"0{length}b")
        coeff = 1
        if signed and j:
            coeff = int(j % 2 == 0) - 3 * int(j % 2 == 1)
        total += Fraction(coeff, exponent << exponent)
        j += 1


def diagnostics(bits, n, a):
    # Each phase uses 53 actual bits. At most 2^-53 is discarded per phase.
    phases = [int(bits[k:k + 53], 2) / 2**53 for k in range(n + 8)]
    escapes = [2 * sin(pi * t)**2 for t in phases]
    sharp = fsum(escapes[:n])
    radial = fsum(exp(-ldexp(1.0, k - n)) * e for k, e in enumerate(escapes))
    # The omitted radial tail is bounded by 4 exp(-256).
    log_growth = fsum(log((1-a)**2 + 4*a*cos(pi*t)**2) / 2 for t in phases[:n])
    q = 2*a / (1+a)**2
    deficit = n * log1p(a) - log_growth
    assert abs(radial - sharp) <= 2 + 1e-9
    assert q*sharp/2 - 1e-9 <= deficit <= q*sharp/(2*(1-2*q)) + 1e-9
    transitions = sum(bits[k] != bits[k+1] for k in range(n))
    return transitions, sharp/n, radial-sharp, deficit/n


def main():
    n = 1024
    length = n + 64
    inputs = {
        "ln2": log_bits(length),
        "Stoneham(2,3)": shell_bits(length, False),
        "signed shells": shell_bits(length, True),
        "zero": "0" * length,
        "one third": ("01" * length)[:length],
        "sparse powers": "".join("1" if k & (k-1) == 0 else "0"
                                 for k in range(1, length+1)),
    }
    print("N=1024, a=1/2. Input | transitions | mean escape | radial error | mean product deficit")
    for name, bits in inputs.items():
        hits, mean, error, deficit = diagnostics(bits, n, 0.5)
        print(f"{name:15} {hits:4} {mean:10.6f} {error:10.6f} {deficit:10.6f}")
    assert diagnostics(inputs["zero"], n, 0.5) == (0, 0, 0, 0)
    assert abs(diagnostics(inputs["one third"], n, 0.5)[1] - 1.5) < 1e-12

    print("Diagonal construction, a_N=1-1/N. N | moving log growth/N | endpoint log growth/N")
    for cutoff in (256, 1024, 4096):
        digits = ["0"] * (cutoff + 64)
        position = 16
        while position <= len(digits):
            digits[position-1] = "1"
            position += (position.bit_length() - 1) // 2
        bits = "".join(digits)
        a = 1 - 1/cutoff
        moving = log1p(a) - diagnostics(bits, cutoff, a)[3]
        initial = int(bits[:53], 2) / 2**53
        final = int(bits[cutoff:cutoff+53], 2) / 2**53
        endpoint = log(abs(sin(pi*final)/sin(pi*initial))) / cutoff
        assert log(a)/2 - 1e-9 <= moving - endpoint <= 1e-9
        print(f"{cutoff:4} {moving:12.7f} {endpoint:12.7f}")

    print("Powers-of-two digit positions, height 2^floor(sqrt(N)). N | exposed starts | escape upper bound")
    for cutoff in (1024, 16384, 262144):
        width = isqrt(cutoff) + cutoff.bit_length()
        exposed = set()
        position = 1
        while position < cutoff + width:
            exposed.update(range(max(0, position-width), min(position, cutoff)))
            position *= 2
        bound = Fraction(2*len(exposed), cutoff) + Fraction(20, (cutoff+1)**2)
        print(f"{cutoff:6} {len(exposed):6} {float(bound):.6f}")


if __name__ == "__main__":
    main()
