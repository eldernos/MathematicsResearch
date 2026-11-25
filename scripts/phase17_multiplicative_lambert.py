#!/usr/bin/env python3
"""Certify digits and measure two multiplicative Lambert series using integers."""

from collections import Counter
from fractions import Fraction
from math import isqrt, log
from time import perf_counter


PREFIXES = (4096, 16384, 65536, 131072)
GRID_BITS = 24
WORDS = ("0", "1", "00", "01", "10", "11", "101", "111")


def smallest_prime_factors(limit):
    factors = list(range(limit + 1))
    for prime in range(2, isqrt(limit) + 1):
        if factors[prime] == prime:
            for multiple in range(prime * prime, limit + 1, prime):
                if factors[multiple] == multiple:
                    factors[multiple] = prime
    return factors


def coefficients(factors, modulus):
    """Compare the Euler factors with an independent divisor convolution."""
    limit = len(factors) - 1
    f = [0, 1] + [0] * (limit - 1)
    c = f.copy()
    for n in range(2, limit + 1):
        prime = factors[n]
        sign = 0 if modulus % prime == 0 else (1 if prime % modulus == 1 else -1)
        f[n] = sign * f[n // prime]
        rest, exponent = n // prime, 1
        while factors[rest] == prime:
            rest //= prime
            exponent += 1
        local = {1: exponent + 1, -1: 1 - exponent % 2, 0: 1}[sign]
        c[n] = local * c[rest]
        assert 0 <= c[n] <= n

    convolution = [0] * (limit + 1)
    for divisor, value in enumerate(f[1:], start=1):
        if value:
            for n in range(divisor, limit + 1, divisor):
                convolution[n] += value
    assert convolution == c
    return c


def check_two_squares(c):
    limit = 4096
    squares = [i * i for i in range(-isqrt(limit), isqrt(limit) + 1)]
    representations = Counter(x + y for x in squares for y in squares if x + y <= limit)
    assert all(representations[n] == 4 * c[n] for n in range(1, limit + 1))


def certified_bits(c, precision):
    """Return b_1,...,b_precision, certifying the entire prefix at once."""
    cutoff = len(c) - 1
    # At cutoff M the scaled omitted tail is between 0 and M+2 since c(n) <= n.
    lo, hi = 0, cutoff + 2
    for n in range(cutoff, precision, -1):
        lo = (c[n] + lo) // 2
        hi = (c[n] + hi) // 2
    assert lo == hi, "Increase the number of coefficients used for the certificate"

    bits = bytearray(precision)
    carry = lo
    for n in range(precision, 0, -1):
        carry, bits[n - 1] = divmod(c[n] + carry, 2)
    return bits


def residue_grid(bits, size):
    """The integers floor(2^GRID_BITS * {2^n L}) for shifts 0 <= n < size."""
    mask = (1 << GRID_BITS) - 1
    code = 0
    for bit in bits[: GRID_BITS - 1]:
        code = (code << 1) | bit
    grid = []
    for bit in bits[GRID_BITS - 1 : size + GRID_BITS - 1]:
        code = ((code << 1) | bit) & mask
        grid.append(code)
    assert len(grid) == size
    return grid


def check_arrivals(c, grid):
    """Check exact reindexing on a finite truncation and bound its omitted tail."""
    cutoff = 256
    arrivals = Counter()
    for n in range(1, cutoff + 1):
        if c[n]:
            power = (c[n] & -c[n]).bit_length() - 1
            arrivals[n - power] += c[n] >> power

    scale = 1 << cutoff
    for shift in range(24, 120):
        head = sum(c[n] << (cutoff - n) for n in range(shift + 1, cutoff + 1))
        displaced = sum(
            mark << (cutoff - t) for t, mark in arrivals.items() if t > shift
        )
        denominator = scale >> shift
        assert (head - displaced) % denominator == 0
        lo = (head << GRID_BITS) // denominator
        hi = ((head + cutoff + 2) << GRID_BITS) // denominator
        assert lo == hi
        assert lo % (1 << GRID_BITS) == grid[shift]

    for level in range(1, 9):
        translated = sum(arrivals[n + level] for n in range(24, 120))
        by_source = 0
        for n in range(1, cutoff + 1):
            if c[n]:
                power = (c[n] & -c[n]).bit_length() - 1
                if 24 <= n - power - level < 120:
                    by_source += c[n] >> power
        assert translated == by_source


def word_count(grid, first, length, word):
    offset = GRID_BITS - len(word)
    value = int(word, 2)
    return sum(code >> offset == value for code in grid[first : first + length])


def discrepancy_enclosure(grid, size):
    """Enclose interval discrepancy by 2^-GRID_BITS on either side of the grid value."""
    scale = 1 << GRID_BITS
    upper, lower = 0, 0
    for rank, code in enumerate(sorted(grid[:size]), start=1):
        upper = max(upper, rank * scale - size * code)
        lower = min(lower, (rank - 1) * scale - size * code)
    estimate = Fraction(upper - lower, size * scale)
    error = Fraction(1, scale)
    return max(0, estimate - error), min(1, estimate + error)


def best_zero_cylinder(zero_runs, size):
    histogram = Counter(zero_runs[:size])
    outside = 0
    best = (Fraction(1), 0)
    for length in range(1, max(histogram) + 2):
        outside += histogram[length - 1]
        loss = Fraction(outside, size) + Fraction(1, 1 << length)
        best = min(best, (loss, length))
    return best


def report(bits, grid, exponent):
    zero_runs = [0] * len(grid)
    run = 0
    for shift in range(len(bits) - 1, -1, -1):
        run = 0 if bits[shift] else run + 1
        if shift < len(grid):
            zero_runs[shift] = run
    # A certified 1 after the final start makes every zero-run length exact.
    assert any(bits[len(grid) - 1 :])

    print("  Moving windows, H=ceil(N^(3/5)); counts in order", " ".join(WORDS))
    print("  N       H     counts                               ones * (log N)^kappa / H")
    for start in (2048, 8192, 32768, 65536, 122880):
        # Compute the ceiling exactly, using the fifth-power comparison.
        length = int(start ** (3 / 5))
        while length**5 < start**3:
            length += 1
        assert (length - 1) ** 5 < start**3 <= length**5
        counts = [word_count(grid, start, length, word) for word in WORDS]
        assert counts[0] + counts[1] == length
        assert counts[2] + sum(counts[3:6]) == length
        print(f"  {start:6d} {length:5d}   " + " ".join(f"{n:4d}" for n in counts)
              + f"     {counts[1] * log(start)**exponent / length:.4f}")

    print("  Prefix N    certified 1-D                  (1-D)*log^kappa  /loglog   best zero loss (L)")
    for size in PREFIXES:
        dlo, dhi = discrepancy_enclosure(grid, size)
        tau = Fraction(sum(bits[n] != bits[n + 1] for n in range(size)), size)
        zero_loss, length = best_zero_cylinder(zero_runs, size)
        assert dhi <= max(Fraction(2, 3), 1 - tau) + Fraction(1, size)
        assert 1 - dlo <= zero_loss
        gap_lo, gap_hi = 1 - dhi, 1 - dlo
        decimal_scale = 10**8
        floor_lo = (gap_lo.numerator * decimal_scale) // gap_lo.denominator
        ceil_hi = -((-gap_hi.numerator * decimal_scale) // gap_hi.denominator)
        scaled = float((gap_lo + gap_hi) / 2) * log(size)**exponent
        print(f"  {size:8d}   [{floor_lo / decimal_scale:.8f}, {ceil_hi / decimal_scale:.8f}]"
              f"       {scaled:7.4f}    {scaled / log(log(size)):7.4f}"
              f"      {float(zero_loss):.6f} ({length})")


def main():
    started = perf_counter()
    precision = max(PREFIXES) + 1024
    factors = smallest_prime_factors(precision + 1024)
    for name, modulus, exponent in (("chi_4", 4, 1 / 2), ("split p=1 mod 5", 5, 3 / 4)):
        c = coefficients(factors, modulus)
        if modulus == 4:
            check_two_squares(c)
        bits = certified_bits(c, precision)
        grid = residue_grid(bits, max(PREFIXES))
        check_arrivals(c, grid)
        print(f"{name}: {precision:,} digits certified; kappa={exponent:g}")
        report(bits, grid, exponent)
    print(f"Finite verification passed in {perf_counter() - started:.2f}s.")


if __name__ == "__main__":
    main()
