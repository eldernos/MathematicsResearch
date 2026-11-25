#!/usr/bin/env python3
"""Certify binary word counts and count displaced divisor terms on one window."""

import argparse
from collections import Counter
from math import isqrt


def divisor_counts(limit):
    """Sieve tau without factoring each integer."""
    counts = [0] * (limit + 1)
    for divisor in range(1, isqrt(limit) + 1):
        square = divisor * divisor
        counts[square] += 1
        for multiple in range(square + divisor, limit + 1, divisor):
            counts[multiple] += 2
    return counts


def certified_carry(counts, place):
    """Floor of the tail in units of 2**(-place), when both bounds agree."""
    end = len(counts) - 1
    lower, upper = 0, end + 2
    for m in range(end, place, -1):
        lower = (counts[m] + lower) // 2
        upper = (counts[m] + upper) // 2
    return lower if lower == upper else None


def certificate(start, length, k, depth):
    """Compare the true words with words formed from depth displaced levels."""
    if min(start, length, k, depth) < 1 or depth < k:
        raise ValueError("positive start, length and word size, and depth >= word size required")
    stop = start + length
    last_place = stop - 1 + depth
    guard = 2 * last_place.bit_length() + 16
    while True:
        end = last_place + guard
        counts = divisor_counts(end)
        carry = certified_carry(counts, last_place)
        # For m > end, m - floor(log2(m)) is nondecreasing and bounds its location.
        if carry is not None and end + 1 - ((end + 1).bit_length() - 1) > last_place:
            break
        guard *= 2

    actual = [0] * length
    rolling = 0
    for m in range(last_place, start, -1):
        carry, bit = divmod(counts[m] + carry, 2)
        rolling = (rolling >> 1) | (bit << (k - 1))
        if m <= stop:
            actual[m - 1 - start] = rolling

    columns = [0] * (last_place - start + 1)
    multiplicity = [0] * len(columns)
    for m in range(start + 1, end + 1):
        tau = counts[m]
        power = tau & -tau
        location = m - (power.bit_length() - 1)
        if start < location <= last_place:
            columns[location - start] += tau // power
            multiplicity[location - start] += 1

    mask = (1 << depth) - 1
    residue = 0
    for mass in columns[1 : depth + 1]:
        residue = (2 * residue + mass) & mask
    counts_actual = Counter(actual)
    counts_head = Counter()
    mismatches = 0
    for i, word in enumerate(actual):
        retained = residue >> (depth - k)
        counts_head[retained] += 1
        mismatches += retained != word
        if i + 1 < length:
            residue = (2 * residue + columns[i + depth + 1]) & mask
    arrivals = multiplicity[1 : length + 1]
    # At denominator 2 the signed one-term sum is -2 per source, while the
    # product of these same phases is (-1) to the number of arrivals.
    print(f"shifts [{start}, {stop}), word size {k}, retained depth {depth}")
    print("actual counts in binary order", [counts_actual[w] for w in range(1 << k)])
    print("retained counts in binary order", [counts_head[w] for w in range(1 << k)])
    print("starts with a changed word", mismatches)
    print("denominator-two arrival count", sum(arrivals))
    print("denominator-two sum of signs", sum((-1) ** a for a in arrivals))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=2**18)
    parser.add_argument("--length", type=int, default=2**18)
    parser.add_argument("--word", type=int, default=2)
    parser.add_argument("--depth", type=int, default=12)
    args = parser.parse_args()
    certificate(args.start, args.length, args.word, args.depth)
