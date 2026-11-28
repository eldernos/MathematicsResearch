"""Exact finite certificates for Phase 24, nonlinear boundaries and approximation."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod


def vp(n, p):
    assert n
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def floor(x):
    return x.numerator // x.denominator


def nearest(x):
    return min(x % 1, (-x) % 1)


def coefficients(d, p, s, limit):
    """Convolve d copies, treating the slots as ordered and omitting zero indices."""
    atoms = []
    i = 1
    while i**d <= limit:
        atoms.append((i**d, Fraction(1, p ** (s * vp(i, p)))))
        i += 1
    row = {0: Fraction(1)}
    for _ in range(d):
        result = Counter()
        for m, value in row.items():
            for power, weight in atoms:
                if m + power > limit:
                    break
                result[m + power] += value * weight
        row = result
    return row


def enclosure(d, p, s, B, count):
    partial = sum(Fraction(1, p ** (s * vp(i, p)) * B ** (i**d))
                  for i in range(1, count + 1))
    tail = Fraction(B, (B - 1) * B ** ((count + 1)**d))
    return partial**d, (partial + tail)**d


def check_gaps():
    checked = 0
    for d, p, s, B in [(2, 3, 1, 4), (3, 3, 1, 4), (4, 5, 2, 16)]:
        limit = 180
        row = coefficients(d, p, s, limit)
        positions = sorted(row)
        # The second evaluation cuts off by coordinate, not by sum of powers.
        lo, hi = enclosure(d, p, s, B, 16 if d == 2 else 8)
        at_end = sum((c * B ** (limit - m) for m, c in row.items()), Fraction())
        # Make a rational comparison value whose first coefficients are identical.
        rational = (at_end + Fraction(2, 7)) / B**limit
        Q = rational.denominator
        R = Fraction()
        for M in range(1, limit):
            R = B * R + row[M]
            if M < d:
                continue
            q, A = R.denominator, R.numerator % R.denominator
            assert q == p ** vp(q, p) and q <= Fraction(M, d)**s
            next_m = next((n for n in positions if n > M), None)
            if next_m is None:
                continue
            g = next_m - M
            discounted = sum((c * Fraction(1, B ** (m - next_m))
                              for m, c in row.items() if m >= next_m), Fraction())
            rational_tail = B**M * rational - R
            assert rational_tail == (discounted + Fraction(2, 7 * B ** (limit-next_m))) / B**g
            residue = (-Q * A - 1) % q + 1
            scaled = Q * q * rational_tail
            assert scaled.denominator == 1 and scaled >= residue
            assert (scaled - residue) % q == 0
            # Bound the true tail independently by its missing coordinate terms.
            upper = B**M * hi - R
            lower = B**M * lo - R
            assert upper >= discounted / B**g > 0 and lower <= upper
            for length in (1, 2, 5, 9):
                scale = 2**length
                if scale * upper < 1:
                    assert floor(scale * B**M * hi) <= floor(scale * R) + 1
                if q * scale * upper < 1:
                    assert floor(scale * B**M * hi) == floor(scale * R)
            checked += 1
    cube_residues = {sum(i**3 for i in xs) % 9 for xs in product(range(9), repeat=3)}
    assert cube_residues == set(range(9)) - {4, 5}
    # Analytic input: log(2) > 2/3. Here we check only the rational margin.
    assert Fraction(390, 449) * 2 * Fraction(2, 3) > 1
    print(f"Gap and residue-lattice certificates: {checked} shifted prefixes")


def check_flagships():
    for d in (2, 3):
        nbits = 8192
        i = 1
        while 2 * i**d <= nbits + 128:
            i += 1
        lo, hi = enclosure(d, 3, 1, 4, i)
        scale = 1 << nbits
        bits_int = floor(scale * lo)
        assert bits_int == floor(scale * hi)
        bits = format(bits_int, f"0{nbits}b")
        width = 8
        words = {bits[j:j+width] for j in range(nbits - width + 1)}
        assert len(words) == 2**width
        midpoint = (lo + hi) / 2
        candidate = midpoint.limit_denominator(1 << 1024)
        assert abs(candidate - midpoint) > (hi - lo) / 2
        # Finite real-circle escape witnesses from actual window numerators.
        row = coefficients(d, 3, 1, 140)
        R = Fraction()
        witnesses = {Q: set() for Q in (1, 2, 3, 5, 7)}
        for m in range(1, 81):
            R = (4*R + row[m]) % 1
            L = 0
            while 4**L < (m+2)**(d+2):
                L += 1
            window = sum((row[m+j] / Fraction(4**j) for j in range(1, L+1)), R)
            # Compare phases without a discontinuity at the integer endpoint.
            exact_prefix = sum((row[i] * 4**(m-i) for i in range(1, m+1)), Fraction())
            omitted = 4**m * hi - exact_prefix - (window-R)
            assert omitted >= 0
            for Q in witnesses:
                if nearest(Q*window) - Q*omitted > Fraction(1, 5):
                    witnesses[Q].add((m-1)//20)
        assert all(blocks == set(range(4)) for blocks in witnesses.values())
        assert nearest(Fraction(4**17, 5)) == Fraction(1, 5)
        print(f"Flagship d={d}: all 256 eight-bit words in {nbits} digits; "
              "all rational denominators through 2^1024 excluded")


def check_arrivals(d, p, s, B, a, h, expected_coverage):
    U = p**a
    M = d * U**d
    E = s * d * a
    v = (h + s - 1) // s
    G = p ** (d * (a - v + 1))
    J = G // (d * 2**d * U**(d-1))
    modulus = p**h
    k = h - vp(B - 1, p)
    assert 0 < k <= a and h <= E
    # Use the exact maximal range for j as well as the conservative theorem bound.
    selected = {}
    j = 1
    while (d-1) * U**d + (U+j)**d < M + G:
        if j % p:
            selected[(d-1) * U**d + (U+j)**d] = j
        j += 1
    assert J < j
    # Include a full residue period when possible without growing the whole shell.
    last = max(max(selected, default=M), M + min(G-1, 500))
    row = coefficients(d, p, s, last)
    phase = Fraction()
    prev = 0
    prev_fractional = None
    innovations = Fraction()
    histogram = Counter()
    fractional_count = 0
    for m in sorted(row):
        gap = m - prev
        multiplier = pow(B, gap, p**E)
        phase = (multiplier * phase + row[m]) % 1
        innovations = (multiplier * innovations + row[m]) % 1
        if row[m].denominator > 1:
            if prev_fractional is not None:
                old_m, old_phase = prev_fractional
                full = pow(B, m-old_m, p**E) * old_phase + innovations
                assert full % 1 == phase
                if old_m >= M:
                    assert (phase.numerator - pow(B, m-old_m, modulus)
                            * old_phase.numerator) % modulus == 0
            prev_fractional = (m, phase)
            innovations = Fraction()
        prev = m
        if m < M:
            continue
        if m == M:
            anchor = phase.numerator
            assert anchor % p == 1
        else:
            assert (p**E * row[m]) % modulus == 0
        assert phase.denominator == p**E
        assert phase.numerator % modulus == anchor * pow(B, m-M, modulus) % modulus
        if row[m].denominator > 1:
            fractional_count += 1
        if m in selected:
            j = selected[m]
            assert row[m].denominator == p ** (s * (d-1) * a - vp(d, p))
            assert phase.numerator % modulus == anchor * pow(B, j**d, modulus) % modulus
            if j <= p**k:
                histogram[phase.numerator % modulus] += 1
    phi = (p-1) * p**(k-1)
    powers = Counter(pow(B, j**d, modulus) for j in range(1, p**k+1) if j % p)
    assert len(powers) == phi // gcd(d, phi)
    assert set(powers.values()) == {gcd(d, phi)}
    coverage = "empty" if not selected else "partial" if len(selected) < phi else "full"
    assert coverage == expected_coverage
    assert sum(histogram.values()) == min(len(selected), phi)
    if coverage == "full":
        assert histogram == Counter({anchor * u % modulus: n for u, n in powers.items()})
    print(f"Actual arrivals d={d}, p={p}, s={s}, a={a}, h={h}: "
          f"{fractional_count} fractional arrivals, {len(selected)} selected, "
          f"{coverage} first period")


def check_flagship_cube_arrival():
    # At a=6 the conservative J includes j=1. Evaluate this single
    # coefficient by counting unordered triples with their permutation weights.
    U = 3**6
    m = 2*U**3 + (U+1)**3
    roots = {x**3: x for x in range(1, 2*U)}
    coefficient = Fraction()
    for x_cube, x in roots.items():
        if 3*x_cube > m:
            break
        for y in range(x, 2*U):
            remainder = m - x_cube - y**3
            if remainder < y**3:
                break
            z = roots.get(remainder)
            if z is not None:
                assert x != z
                multiplicity = 3 if x == y or y == z else 6
                coefficient += Fraction(multiplicity, 3**vp(x*y*z, 3))
    assert coefficient.denominator == 3**11
    print("Flagship cube: selected j=1 coefficient at a=6 has depth 11")


def cf_word(word, tail):
    for digit in reversed(word):
        tail = Fraction(1, digit + tail)
    return tail


def check_scaled_grids():
    count = 0
    for p, B in ((3, 4), (3, 10), (5, 16)):
        w = vp(B-1, p)
        for d in (2, 3):
            u = 1 + vp(d, p)
            for k in range(u+1, u+4):
                modulus = p**(w+k)
                small = p**(w+u)
                for unit in (1, 2, p+1):
                    actual = Counter(unit * pow(B, j**d, modulus) % modulus
                                     for j in range(p**k) if j % p)
                    residues = {a % small for a in actual}
                    assert set(actual) == {z for a in residues for z in range(a, modulus, small)}
                    assert len(set(actual.values())) == 1
                    count += 1
    print(f"Scaled arrival phases: {count} complete unions of translated grids")


def check_continued_fractions():
    count = 0
    for word in product((1, 2), repeat=8):
        ends = sorted(cf_word(word, x) for x in (Fraction(), Fraction(1)))
        for q in range(1, 19):
            # Every infinite continuation is in the strict interior.
            a, b = (q*x for x in ends)
            for h in range(floor(a), floor(b)+2):
                assert not a <= h <= b
                assert q * min(abs(a-h), abs(b-h)) >= Fraction(1, 4)
            count += 1
    u = Fraction(1, 3)
    folds = []
    for m in (2, 5, 1, 7, 11, 3, 13):
        q = u.denominator
        folds.append((u, q, m))
        u += Fraction(1, m*q*q)
        assert u.denominator == m*q*q
    for old, q, m in folds:
        assert 0 < q*q*(u-old) <= Fraction(4, 3*m)
    print(f"Bad-approximation cylinders: {count} denominator intervals; "
          f"{len(folds)} exact reciprocal folds")


def check_growing_caps():
    """Independently compute lengths from convergents and masses by conditioning."""
    # (previous p,q; current p,q; mass)
    nodes = [(1, 0, 0, 1, Fraction(1))]
    inflation = Fraction(1)
    for depth in range(1, 8):
        cap = max(2, depth.bit_length())  # ceil(log2(depth+1))
        inflation *= 1 + Fraction(2, cap)
        new_nodes = []
        for a0, q0, a1, q1, mass in nodes:
            length = Fraction(1, q1*(q1+q0))
            children = []
            for digit in range(1, cap+1):
                a2, q2 = digit*a1+a0, digit*q1+q0
                child_length = abs(Fraction(a2, q2) - Fraction(a2+a1, q2+q1))
                children.append((a2, q2, child_length))
            retained = sum(child[2] for child in children)
            assert retained / length == Fraction(cap*q1, (cap+1)*q1+q0)
            for a2, q2, child_length in children:
                child_mass = mass * child_length / retained
                assert child_mass <= inflation * child_length
                assert child_length <= Fraction(1, 2**(depth-1))
                new_nodes.append((a1, q1, a2, q2, child_mass))
        nodes = new_nodes
        assert sum(row[-1] for row in nodes) == 1
    intervals = [(Fraction(1, 3), Fraction(3, 8)), (Fraction(4, 7), Fraction(5, 8))]
    outer = Fraction()
    for a0, q0, a1, q1, mass in nodes:
        left, right = sorted((Fraction(a1, q1), Fraction(a1+a0, q1+q0)))
        if any(left <= high and right >= low for low, high in intervals):
            outer += mass
        # Bound the irrationality constant at this convergent for every allowed
        # next digit and every tail in (0,1), via two rational endpoints.
        next_cap = max(2, (depth+1).bit_length())
        for digit in range(1, next_cap+1):
            for end in (digit, digit+1):
                y = Fraction(end*a1+a0, end*q1+q0)
                assert q1 * abs(q1*y-a1) >= Fraction(1, next_cap+2)
        assert q1*q1 >= 2**(depth-1)
    total_length = sum(high-low for low, high in intervals)
    assert outer <= inflation * (total_length + Fraction(2*len(intervals), 2**(depth-1)))
    for digits in product((0, 1), repeat=12):
        hits = [int(digits[j:j+2] == (0, 1)) for j in range(len(digits)-1)]
        tol = Fraction(1, 6)
        if abs(Fraction(sum(hits), len(hits)) - Fraction(1, 4)) > tol:
            assert any(abs(Fraction(sum(hits[i::2]), len(hits[i::2])) - Fraction(1, 4)) > tol
                       for i in (0, 1))
    print(f"Growing caps: {len(nodes)} depth-seven cylinders and 4096 binary word tests")


def primes_away(b):
    n = 2
    while True:
        if b % n and all(n % k for k in range(2, isqrt(n)+1)):
            yield n
        n += 1


def check_dense_metric():
    for b in (2, 3, 10):
        primes = primes_away(b)
        S = Fraction()
        shifted = Fraction()
        denominator = 1
        x = Fraction(17, 31)
        for n in range(1, 41):
            prime = next(primes)
            S += Fraction(1, prime * b**n)
            digit = (n*n + n//3) % b
            shifted = b * shifted + digit + Fraction(1, prime)
            denominator *= prime
            assert 0 < digit + Fraction(1, prime) < b
            assert shifted.denominator == denominator
        y = (x-S) % 1
        integer = floor(b**n*y)
        assert S + Fraction(integer, b**n) <= x - floor(x-S)
        assert x - floor(x-S) < S + Fraction(integer+1, b**n)
        assert S + y == x - floor(x-S)
    print("Synthetic digit sequences: exact denominators at 120 prefixes")


def sparse_coefficients(b, p, length):
    auxiliary = primes_away(b*p)
    radical = prod(prime for prime in range(2, b+1)
                   if b % prime == 0 and all(prime % j for j in range(2, isqrt(prime)+1)))
    D = 1
    for k in range(1, length + 1):
        prime = next(auxiliary) if isqrt(k)**2 == k else 1
        pole = p**k
        modulus = radical * prime
        residue = (prime * pow(b, 2**k, pole) - 1) * pow(modulus, -1, pole) % pole
        u = 1 + modulus * residue
        c = Fraction(u, pole * prime)
        assert 0 < c <= radical
        D *= p * prime
        yield c, D


def rational_badness(u):
    """Minimize l*|al-qh|/q by trying one full period of l, excluding equality."""
    a, q = u.numerator, u.denominator
    def cost(l):
        r = a*l % q
        return l * (min(r, q-r) if r else q)
    return Fraction(min(cost(l) for l in range(1, q+1)), q)


def check_shells():
    fold_checks = 0
    for q in range(2, 11):
        for a in range(1, q):
            if gcd(a, q) != 1:
                continue
            u = Fraction(a, q)
            for z in (Fraction(-3, 5), Fraction(1, 7), Fraction(2), Fraction(-1)):
                lower = min(abs(z), rational_badness(u) / (2*z.numerator**2))
                assert rational_badness(u + z/q**2) >= lower
                fold_checks += 1
    for b, p in ((2, 3), (4, 3), (6, 5)):
        data = list(sparse_coefficients(b, p, 6))
        seen = set()
        for labels in product((1, 2), repeat=len(data)):
            raw = U = Fraction()
            previous_q = 1
            previous_label = 0
            for k, ((c, D), label) in enumerate(zip(data, labels), 1):
                n = 2**k
                raw += c / b**n
                assert (raw*b**n).denominator == D
                d = c + Fraction(label-previous_label, b-1)
                assert (d * D * (b-1)).denominator == 1
                if k > vp(b-1, p):
                    assert vp(d.denominator, p) == k
                    unit = p**k * d / b**n
                    precision = p ** (k-vp(b-1, p))
                    assert (unit.numerator-unit.denominator) % precision == 0
                new = U + d / b**n
                if k > 1:
                    z = (new-U) * previous_q**2
                    assert z == d * Fraction(previous_q, b**(n//2))**2
                # Cancellation in the radix denominator is controlled once the
                # final numerator is smaller than every relevant prime power.
                E = (b-1)*D
                final = int(E*d)
                if final and all(abs(final) < r ** ((n//2)*vp(b, r))
                                 for r in range(2,b+1) if b%r == 0 and
                                 all(r%j for j in range(2,isqrt(r)+1))):
                    ratio = Fraction(new.denominator, b**n)
                    assert ratio.numerator <= E and ratio.denominator <= abs(final)
                for m in range(n+1, 2*n+1):
                    # At 2*n this partial sum still lacks the next sparse coefficient.
                    raw += Fraction(label, b**m)
                    assert (raw*b**m).denominator == D
                assert raw == new - Fraction(label, (b-1)*b**(2*n))
                U, previous_q, previous_label = new, new.denominator, label
            assert raw not in seen
            seen.add(raw)
        assert len(seen) == 2**len(data)
    print(f"Determinant folding: {fold_checks} inequalities; "
          "192 distinct shell choices across three radices")


def main():
    check_gaps()
    check_flagships()
    check_arrivals(2, 3, 3, 4, 4, 3, "full")
    check_arrivals(2, 3, 2, 4, 4, 3, "partial")
    check_arrivals(2, 5, 3, 16, 2, 2, "full")
    check_arrivals(3, 3, 3, 4, 3, 2, "full")
    check_arrivals(3, 3, 1, 4, 3, 2, "empty")
    check_arrivals(3, 5, 3, 16, 2, 2, "full")
    check_flagship_cube_arrival()
    check_scaled_grids()
    check_continued_fractions()
    check_growing_caps()
    check_dense_metric()
    check_shells()
    print("All exact finite certificates passed.")


if __name__ == "__main__":
    main()
