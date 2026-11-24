#!/usr/bin/env python3
"""Certify middle-third visits of R_n at dyadic prefix lengths using integers."""

import argparse
from fractions import Fraction


def middle_hit(n: int, lo: int, modulus: int) -> bool:
    """The scaled residue lies in [lo, lo+n] modulo modulus, with n < modulus."""
    hi = lo + n
    for offset in (0, modulus):
        left = 3 * offset + modulus
        right = 3 * offset + 2 * modulus
        if left <= 3 * lo and 3 * hi <= right:
            return True
        if 3 * lo <= right and left <= 3 * hi:
            # Includes exact endpoints, such as R_3 mod 1 = 1/3.
            residue = Fraction()
            for j in range(1, n + 1):
                residue = (2 * residue + Fraction(1, j)) % 1
            return 1 <= 3 * residue <= 2
    return False


def prefix_rows(last_power: int):
    limit = 1 << last_power
    precision = limit + limit.bit_length() + 32
    modulus = 1 << precision
    residue = hits = age = total_age = 0
    for n in range(limit):
        # modulus * R_n = sum_{j=1}^n 2^(precision-j)/j. Rounding each
        # summand down gives total error at most n grid units.
        hit = middle_hit(n, residue, modulus)
        hits += hit
        age = 0 if hit else age + 1
        total_age += age
        size = n + 1
        if size & (size - 1) == 0:
            yield size, hits, total_age
        modulus >>= 1
        residue = (residue + modulus // size) % modulus


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('power', type=int, nargs='?', default=16,
                        help='count starts from 0 through 2^power - 1')
    args = parser.parse_args()
    if args.power < 0:
        parser.error('power must be nonnegative')
    print('N,hits,total_age')
    for row in prefix_rows(args.power):
        print(*row, sep=',')
