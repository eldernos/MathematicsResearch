"""Exact dyadic logarithm identities, shifted numerators and finite block certificates."""

from fractions import Fraction as Q
from itertools import combinations_with_replacement

from discrepancy_experiments import corrected_model, log_bits
from kernel_coverage import block_discrepancy


def relations(max_stride=6, budget=4):
    """Enumerate products with l1 coefficient bound; omit the single factor 1/2."""
    factors = [(k, sign) for k in range(1, max_stride + 1) for sign in (-1, 1)
               if (k, sign) != (1, -1)]
    letters = [(factor, exponent) for factor in factors for exponent in (-1, 1)]
    found = []
    for length in range(1, budget + 1):
        for word in combinations_with_replacement(letters, length):
            if len(set(item for item, _ in word)) != len(set(word)):
                continue  # A factor and its inverse would give a shorter representation.
            product = Q(1)
            for (k, sign), exponent in word:
                product *= Q(2**k + sign, 2**k)**exponent
            if (product > 1 and product.denominator == 1
                    and product.numerator.bit_count() == 1):
                found.append((product.numerator.bit_length() - 1, word))
    return found


def weight(m):
    return (0, 4, 3, 4, 0, 1)[(m - 1) % 6]


def shifted(n):
    return sum((Q(weight(j) << (n-j), j) for j in range(1, n+1)), Q(0))


def partial(v):
    return sum((Q(weight(j), j << j) for j in range(1, v+1)), Q(0))


def residue_of_rational(value, p):
    return value.numerator * pow(value.denominator, -1, p) % p


def finite_certificates(end, length=12):
    """Use a certified prefix of log(2) to test m log(2) on disjoint blocks."""
    precision = end + length + 30
    lower = int(log_bits(precision), 2)
    # Compare two series for each multiple against the independent binary enclosure.
    extra = 10
    cutoff = precision + extra
    optimal = shifted(cutoff)
    original = corrected_model(cutoff, 0)
    rows = []
    for m in (1, 2, 3, 5):
        for value, tail in ((m*optimal, Q(4*m, cutoff+1)),
                            (optimal+(m-1)*original, Q(m+3, cutoff+1))):
            # At this precision the two enclosures may straddle a rounding boundary.
            assert value < (m*(lower+1) << extra) and (m*lower << extra) <= value + tail
        stop = packed = passing = 0
        for start in range(end-length+1):
            q = 1 << (precision-start)
            a = (m*lower) % q
            error = Q(m << (length-1), q)
            if block_discrepancy(a, q, length) + 2*error <= Q(1, 3):
                passing += 1
                if start >= stop:
                    packed += length
                    stop = start + length
        rows.append((m, passing, packed))
    return rows


def diagonal_residues(p):
    """Iterate the step-normalized diagonal model over the prime field."""
    values = [0]
    for n in range(p-1):
        values.append(-2*(2*n+3)*(2*values[-1]+3)*pow(n+1, -1, p) % p)
    return values


def arctan_interval(q, bits):
    """Alternating bounds for arctan(1/q) from two consecutive partial sums."""
    total = Q(0)
    j = 0
    while True:
        term = Q((-1)**j, (2*j+1)*q**(2*j+1))
        next_sum = total + term
        if abs(term) * (1 << bits) <= 1:
            return min(total, next_sum), max(total, next_sum)
        total, j = next_sum, j+1


def pi_hex_transitions(start, length):
    """Certify transitions at indices 4j directly from Machin's identity."""
    bits = 4*(start+length)+2
    precision = bits + 12
    while True:
        a, b = arctan_interval(5, precision)
        c, d = arctan_interval(239, precision)
        lower, upper = (16*a-4*d)*(1 << bits), (16*b-4*c)*(1 << bits)
        if int(lower) == int(upper):
            word = int(lower)
            return sum(((word >> (bits-2-4*j)) & 3) in (1, 2)
                       for j in range(start, start+length))
        precision += 16


def golden_modulus_hits(n):
    """Use a growing Fibonacci denominator to certify interior visits through n."""
    q, successor, index = 1, 2, 2
    while q*q < (1 << (n+4)):
        q, successor, index = successor, q+successor, index+1
    residue = successor % q
    hits = 0
    for _ in range(n):
        hits += q <= 3*residue <= 2*q
        residue = (2*residue) % q
    return index, hits


def validate():
    for n in range(1, 90):
        y = shifted(n)
        direct = sum((Q(2 << (n-2*j), j) for j in range(1, n//2+1)), Q(0))
        direct += sum((Q((-1)**(j+1)*(1 << (n-3*j)), j) for j in range(1, n//3+1)), Q(0))
        assert y == direct
        for p in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43):
            if p*p > n:
                actual = residue_of_rational(p*y, p)
                predicted = pow(2, n, p)*residue_of_rational(partial(n//p), p) % p
                assert actual == predicted
    for p in (7, 13, 31, 43):
        values = diagonal_residues(p)
        for n, w in enumerate(values):
            current = corrected_model(n, n)
            step = corrected_model(n+1, n+1)-2*current
            assert w == residue_of_rational(3*current/step, p)
        for h in range(1, (p+1)//2):
            counts = [0]*p
            for left, right in zip(values, values[h:]):
                if left == right:
                    counts[left] += 1
            assert max(counts) <= h


if __name__ == '__main__':
    validate()
    found = relations()
    print('Relations by positive multiple:', {m: sum(j == m for j, _ in found)
                                               for m in sorted({j for j, _ in found})})
    for n in (128, 256, 512, 1024):
        y = shifted(n)
        print('N, denominator bits, Fibonacci index and hits:',
              n, y.denominator.bit_length(), golden_modulus_hits(n))
    print('Multiple, qualifying starts, disjoint positions:', finite_certificates(1024))
    print('Hexadecimal shifts of pi, transitions on [128,256):', pi_hex_transitions(128, 128))
