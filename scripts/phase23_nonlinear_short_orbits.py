"""Exact finite checks for the Phase 23 nonlinear and irrationality note."""

from bisect import bisect_left
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, gcd, isqrt, lcm, prod


def valuation(n, p):
    assert n != 0
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def factors(n):
    result = {}
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            exponent = valuation(n, divisor)
            result[divisor] = exponent
            n //= divisor**exponent
        divisor += 1
    if n > 1:
        result[n] = 1
    return result


def order(base, modulus):
    if modulus == 1:
        return 1
    phi = prod((p - 1) * p**(e - 1) for p, e in factors(modulus).items())
    for p, e in factors(phi).items():
        for _ in range(e):
            if pow(base, phi // p, modulus) != 1:
                break
            phi //= p
    return phi


def level_counts(power, p, limit):
    indices = []
    i = 1
    while i**power <= limit:
        indices.append((i**power, valuation(i, p)))
        i += 1
    result = defaultdict(Counter)
    for row in combinations_with_replacement(indices, power):
        position = sum(x for x, _ in row)
        if position <= limit:
            multiplicity = factorial(power) // prod(factorial(m) for m in Counter(row).values())
            result[position][sum(v for _, v in row)] += multiplicity
    return result


def innovation(levels, p, depth):
    return sum((Fraction(count, p**(level - depth)) for level, count in levels.items()
                if level > depth), Fraction())


def check_jumps():
    assert Fraction(390, 449) * 2 * Fraction(2, 3) > 1
    for p in (3, 5):
        rows = level_counts(2, p, 400 * p**2)
        hist = Counter()
        for n in range(2, 401):
            primes = factors(n)
            if any(e > 1 or q % 4 == 3 for q, e in primes.items()):
                continue
            if pow(n, (p - 1) // 2, p) != p - 1:
                continue
            expected = 2**sum(q % 4 == 1 for q in primes)
            for depth in (0, 1):
                jump = innovation(rows[p**2 * n], p, depth)
                assert jump == Fraction(expected, p**(2 - depth))
            hist[expected % p] += 1
        assert hist == ({1: 9, 2: 29} if p == 3 else {1: 1, 2: 30, 4: 1})
        print(f"squares p={p}, n<=400, H=1: residues/counts {sorted(hist.items())}")

    rows = level_counts(3, 3, 3**10)
    for m, levels in rows.items():
        assert m % 9 not in (4, 5)
        if m % 9 in (3, 6):
            assert set(levels) == {0}
        if m % 9 in (2, 7):
            assert all(level > 0 and count % 3 == 0 for level, count in levels.items())
    for a in range(1, 4):
        for depth in range(3 * a):
            jump = innovation(rows[3**(3 * a + 1)], 3, depth)
            assert jump.denominator == 3**(3 * a - depth)
            assert jump.numerator % 9 == 1


def check_actual_packets(power, p):
    rows = level_counts(power, p, 4096)
    stride = order(2, p)
    positions, phases, jumps = [], [], []
    phase = Fraction()
    previous = 0
    for m, levels in sorted(rows.items()):
        jump = innovation(levels, p, 0) % 1
        if jump:
            phase = (phase * 2**(stride * (m - previous)) + jump) % 1
            positions.append(m)
            phases.append(phase)
            jumps.append(jump)
            previous = m
    eligible = 0
    for i, initial in enumerate(phases):
        total = Fraction()
        for j in range(i + 1, min(i + 6, len(positions))):
            gap = positions[j] - positions[j - 1]
            total = (total * 2**(stride * gap) + jumps[j]) % 1
            span = positions[j] - positions[i]
            delta = (phases[j] - initial) % 1
            assert (initial * (2**(stride * span) - 1) + total) % 1 == delta
            pole = valuation(initial.denominator, p) - valuation(2**stride - 1, p) - valuation(span, p)
            if pole > valuation(total.denominator, p):
                assert delta.denominator == p**pole
                eligible += 1
    expected = {(2, 3): (643, 1871), (2, 5): (479, 1200), (3, 3): (164, 427)}
    assert (len(positions), eligible) == expected[power, p]
    print(f"power {power}, p={p}, m<=4096: {len(positions)} fractional arrivals, "
          f"{eligible} packets with surviving difference pole")


def check_packets():
    base, p, q, length = 2, 3, 81, 5
    jumps = [Fraction(5, 9), Fraction(2), Fraction(), Fraction(4, 27), Fraction(2, 3)]
    suffix = Fraction(7, 31)
    tails = [suffix]
    for jump in reversed(jumps):
        tails.append((jump + tails[-1]) / base)
    tails.reverse()
    words = set()
    for a in range(q):
        if a % p == 0:
            continue
        prefix = Fraction(a, q)
        initial = prefix + tails[0]
        digits = []
        for j, jump in enumerate(jumps):
            shadow = (prefix + tails[j]) % 1
            assert shadow == (base**j * initial) % 1
            digits.append(int(base * shadow))
            prefix = (base * prefix + jump) % 1
            assert prefix.denominator == q
        words.add(tuple(digits))
    assert len(words) == base**length
    print(f"packet: {len(words)} words of length {length} with fixed jumps and q={q}")


def certified_bits(power, digits):
    precision = digits + 40
    scaled = Fraction()
    i = 1
    while 2 * i**power <= precision:
        scaled += Fraction(1 << (precision - 2 * i**power), 3**valuation(i, 3))
        i += 1
    lower = scaled / 2**precision
    upper = (scaled + 1) / 2**precision
    assert int(2**digits * lower**power) == int(2**digits * upper**power)
    word = format(int(2**digits * lower**power), f"0{digits}b")
    assert len(word) == digits
    return word.count("1"), sum(a != b for a, b in zip(word, word[1:]))


def weighted_mass_check():
    p, base, d, shell, precision = 3, 2, 4, 3, 4
    # This fixture has gap one, but its subleading coefficient has an extra p.
    # A second fixture below removes that factor and tests the freezing condition.
    terms = [((2, 2, 2), 1), ((3, 3), -2), ((2, 4), 5), ((6,), 2), ((2, 3), 3)]
    modulus = p**precision
    scale = p**shell
    cuts = [scale**d * j for j in (1, 2, 3, 4, 7)]
    indices = range(1, isqrt(isqrt(cuts[-1])) + 1)
    powers = {i: i**d for i in indices}
    aux = {2: 5, 7: 11}
    units = {i: pow(aux.get(i, 1) * pow(base, 2 * powers[i], modulus), -1, modulus)
             for i in indices}
    values = {i: valuation(i, p) for i in indices}
    direct = [0] * len(cuts)
    frozen = [0] * len(cuts)
    for orders, coefficient in terms:
        for row in product(indices, repeat=len(orders)):
            position = sum(powers[i] for i in row)
            depth = 6 * shell - sum(s * values[i] for i, s in zip(row, orders))
            if position > cuts[-1] or depth >= precision:
                continue
            term = coefficient * p**depth * prod(units[i] for i in row)
            for j, cut in enumerate(cuts):
                if position <= cut:
                    direct[j] += term
        if sum(orders) != 6:
            continue
        # Enumerate independent reduced-coordinate grids, without radix or aux units.
        grids = []
        for s in orders:
            grid = [(Fraction(a, p**h)**d, s * h) for h in range((precision - 1) // s + 1)
                    for a in range(1, p**(h + 1)) if a % p]
            grids.append(grid)
        for row in product(*grids):
            level = sum(h for _, h in row)
            location = sum((z for z, _ in row), Fraction())
            for j, cut in enumerate(cuts):
                if level < precision and location * scale**d <= cut:
                    frozen[j] += coefficient * p**level
    residues = [n % modulus for n in direct]
    assert residues == [n % modulus for n in frozen] == [2, 41, 15, 15, 60]
    # The precise theorem's freezing window (including weight gap one).
    for shell in (4, 5):
        scale = p**shell
        for k in (1, 2):
            cut = (k * scale)**d
            # The discarded and auxiliary terms are p^precision multiples.
            # Enumerate all potentially visible indices with a separate bound per slot.
            total = 0
            for orders, coef in terms:
                gap = 6 - sum(orders)
                if gap * shell >= precision:
                    continue
                grids = [[i for i in range(1, k * scale + 1)
                          if s * (shell - valuation(i, p)) < precision] for s in orders]
                for row in product(*grids):
                    if sum(i**d for i in row) > cut:
                        continue
                    depth = 6 * shell - sum(s * valuation(i, p) for s, i in zip(orders, row))
                    unit = prod(pow(aux.get(i, 1) * pow(base, 2 * i**d, modulus), -1, modulus)
                                for i in row)
                    total += coef * p**depth * unit
            if k == 1:
                assert total % modulus == residues[0]
            else:
                assert total % modulus == weighted_at_two(modulus)
    # For L=2, J=1, at u=1, X_6 + X_5 has only index p visible.
    for shell, expected in ((1, 1 + p), (2, 1)):
        scale = p**shell
        raw = sum(p**(6 * shell - s * valuation(i, p)) * pow(base, -2 * i**d, p**2)
                  for s in (5, 6) for i in range(1, scale + 1))
        assert raw % p**2 == expected
    print(f"weighted residues mod {modulus}: {residues}")


def weighted_at_two(modulus):
    target = 2**4
    total = 0
    for orders, coefficient in (((2, 2, 2), 1), ((3, 3), -2), ((2, 4), 5), ((6,), 2)):
        grids = []
        for s in orders:
            grids.append([(Fraction(a, 3**h)**4, 3**(s * h)) for h in (0, 1)
                          for a in range(1, 3**(h + 1)) if a % 3])
        for row in product(*grids):
            if sum(x for x, _ in row) <= target:
                total += coefficient * prod(weight for _, weight in row)
    return total % modulus


def check_weight_and_orders():
    # Competing assignments at the same isolated multiset of losses.
    losses = (1, 5, 21)
    first = [sum(s * h for s, h in zip((1, 2, 4), row)) for row in permutations(losses)]
    second = [sum(s * h for s, h in zip((1, 3, 3), row)) for row in permutations(losses)]
    assert min(first) == 35 and first.count(35) == 1 and min(second) == 39
    assert (sum(3**h for h in first) - sum(3**h for h in second)) % 3**36 == 3**35
    sets = ((2, (3, 5, 7, 11, 13)), (3, (2, 5, 7, 11)), (8, (3, 5, 7, 13)))
    for base, primes in sets:
        for r in (1, 2, 3):
            radical_order = order(base, prod(primes))
            lift = 1
            for ell in primes:
                if ell > 2:
                    depth = valuation(base**order(base, ell) - 1, ell)
                    lift *= ell**max(0, r - depth)
            two_part = order(base, 2**r) if 2 in primes else 1
            assert order(base, prod(primes)**r) == lcm(radical_order, lift, two_part)


def check_weighted_rows():
    """Check the regular-row and small-coordinate counts near translated poles."""
    p, d = 3, 4
    tau = Fraction(1, 3)
    intervals = ((Fraction(1), Fraction(1) + Fraction(1, 81)),
                 (Fraction(2), Fraction(2) + Fraction(1, 27)))
    length = sum(right - left for left, right in intervals)
    rows = 0
    for level in (4, 5):
        common = p**level
        scale = common**d
        bounds = [(int(left * scale), int(right * scale)) for left, right in intervals]
        coordinates = [[(a * p**(level - h))**d for a in range(1, p**(h + 1))]
                       for h in range(level + 1)]
        for orders in ((1, 3), (1, 1, 2), (2, 3)):
            for losses in product(range(level + 1), repeat=len(orders)):
                if sum(s * h for s, h in zip(orders, losses)) > level:
                    continue
                for slot, g in enumerate(losses):
                    if 2 * len(orders) * g < level:
                        continue
                    fine = coordinates[g]
                    lower = bisect_left(fine, scale * tau**d)
                    assert lower <= tau * p**g
                    others = [coordinates[h] for i, h in enumerate(losses) if i != slot]
                    for fixed in product(*others):
                        shift = sum(fixed)
                        hits = sum(bisect_left(fine, right - shift, lower)
                                   - bisect_left(fine, left - shift, lower)
                                   for left, right in bounds)
                        assert hits <= p**g * length / (d * tau**(d - 1)) + len(bounds)
                        rows += 1
    assert rows
    print(f"weighted regular-row bounds and small-coordinate counts: {rows} rows")


def rational_constant(value):
    """The lattice minimum B(a/q); residues l in [1,q] suffice."""
    a, q = value.as_integer_ratio()
    best = q
    for l in range(1, q + 1):
        residue = a * l % q
        distance = min(residue, q - residue) if residue else q
        best = min(best, l * distance)
    return Fraction(best, q)


def max_partial_quotient(frac):
    a, b = frac.numerator, frac.denominator
    if b == 0:
        return 0
    a = abs(a) % b
    best = 0
    while a:
        q, r = divmod(b, a)
        best = max(best, q)
        b, a = a, r
    return best


def check_folding():
    cases = 0
    # Include q = 1 (integer u = 0 and u = 1) as well as q in [2, 16] and larger numerators c.
    for u in (Fraction(0, 1), Fraction(1, 1)):
        bad = rational_constant(u)
        assert bad == 1
        for c, d in product((-11, -5, -2, -1, 1, 2, 5, 11), (1, 2, 3, 5)):
            z = Fraction(c, d)
            assert rational_constant(u + z) >= min(abs(z), bad / (2 * z.numerator**2))
            cases += 1
    for q in range(2, 17):
        for a in range(1, q):
            if gcd(a, q) != 1:
                continue
            u = Fraction(a, q)
            bad = rational_constant(u)
            assert bad == rational_constant(Fraction(pow(a, -1, q), q))
            for c, d in product((-7, -5, -2, -1, 1, 2, 5, 7), (1, 2, 3)):
                z = Fraction(c, d)
                assert rational_constant(u + z / q**2) >= min(abs(z), bad / (2 * z.numerator**2))
                cases += 1
    assert cases == 1960
    print(f"determinant lemma: {cases} signed rational corrections")


def prefix_gaps(positions):
    largest = 0
    for old, new in zip(positions, positions[1:]):
        largest = max(largest, new - old)
        yield Fraction(largest, new)


def check_record_gaps():
    positions = [n for j in range(1, 20) for n in (2**j, 2**j + 1)]
    assert min(list(prefix_gaps(positions))[4:]) >= Fraction(1, 3)
    assert list(prefix_gaps(range(2, 257)))[-1] == Fraction(1, 256)
    # Keep just the changes of the record on the integer-filled stretches.
    start = 2
    largest = 1
    for _ in range(6):
        end = start**2
        assert Fraction(largest, end) <= Fraction(1, start)
        next_start = 2 * end
        largest = max(largest, next_start - end)
        start = next_start


def constructed_terms(b, p, count, filled):
    primes = [i for i in range(2, 100) if gcd(i, b * p) == 1
              and all(i % divisor for divisor in range(2, isqrt(i) + 1))]
    auxiliary = {j * j: ell for j, ell in enumerate(primes, 1)}
    terms = {}
    units = []
    for k in range(1, count + 1):
        n = 2**k
        ell = auxiliary.get(k, 1)
        modulus = p**k
        radix_modulus = prod(factors(b)) * ell
        u = 1 + radix_modulus * (((ell * pow(b, n, modulus) - 1)
                                  * pow(radix_modulus, -1, modulus)) % modulus)
        coefficient = Fraction(u, modulus * ell)
        assert 0 < coefficient <= b and gcd(u, b * p * ell) == 1
        terms[n] = coefficient
        root = isqrt(k)
        width = 2**(k - root - (root * root < k)) if filled else 0
        if filled:
            for j in set(range(1, width + 1, 2)) | {width}:
                terms[n + j] = Fraction(1)
        units.append((k, n + width, ell))
    return terms, units


def check_dense_regrouping():
    # Includes p dividing the block denominator and a composite radix.
    for b, p in ((2, 3), (4, 3), (6, 5)):
        core, endpoints = constructed_terms(b, p, 9, False)
        raw = dict(core)
        previous_weight = Fraction()
        grouped_prefix = Fraction()
        raw_prefix = Fraction()
        off_radix = 1
        previous_q = 1
        for k, n, ell in endpoints:
            stride = 1 << ((k.bit_length() - 1) // 2)
            assert stride**2 <= k < (2 * stride)**2
            weight = Fraction(1, b**stride - 1)
            block = sum((Fraction(1, b**j) for j in range(n + stride, 2 * n + 1, stride)), Fraction())
            assert block == weight * (Fraction(1, b**n) - Fraction(1, b**(2 * n)))
            for j in range(n + stride, 2 * n + 1, stride):
                raw[j] = raw.get(j, 0) + 1
            new_coeff = core[n] + weight - previous_weight
            grouped_prefix += new_coeff / b**n
            raw_prefix += core[n] / b**n + block
            assert raw_prefix == grouped_prefix - weight / b**(2 * n)
            depth_loss = valuation(b**order(b, p) - 1, p)
            if k > depth_loss:
                assert valuation(new_coeff.denominator, p) == k
                unit = p**k * new_coeff / b**n
                modulus = p**(k - depth_loss)
                assert unit.numerator * pow(unit.denominator, -1, modulus) % modulus == 1
                z = new_coeff * Fraction(previous_q, b**(n // 2))**2
                # Non-tautological height bound: numerator and denominator of z are bounded by
                # the proof's E_{k-1}^2 * E_k factor (no exponential b^{2^k} blowup).
                prev_E = off_radix * (b**stride - 1)
                curr_E = off_radix * p * ell * (b**stride - 1)
                assert abs(z.numerator) <= 2 * b * curr_E * prev_E**2 * (b**stride)
                assert z.denominator <= curr_E * (b * prev_E)**2
            previous_q = grouped_prefix.denominator
            previous_weight = weight
            off_radix *= p * ell
        assert max_partial_quotient(grouped_prefix) < 2**16
        # Direct convolution test for regrouped V^r (r = 2, 3): verify pole retention and
        # complementary denominator divisibility against ((b^{h_K}-1) * prod ell_j)^r.
        regrouped_terms = []
        prev_w = Fraction()
        max_stride = 1
        aux_prod = 1
        for k, n, ell in endpoints:
            stride = 1 << ((k.bit_length() - 1) // 2)
            w = Fraction(1, b**stride - 1)
            regrouped_terms.append((n, (core[n] + w - prev_w) / b**n))
            prev_w = w
            if n <= 511:
                max_stride = stride
                aux_prod *= ell
        comp_bound_base = (b**max_stride - 1) * aux_prod
        for degree in (2, 3):
            conv = {0: Fraction(1)}
            for _ in range(degree):
                nxt = defaultdict(Fraction)
                for pos, val in conv.items():
                    for n_pos, c_val in regrouped_terms:
                        if pos + n_pos <= 511:
                            nxt[pos + n_pos] += val * c_val
                conv = nxt
            # Check late shell K = 8 (256 <= n <= 511): pole depth is degree*8 - O(1) and
            # prime-to-bp part of denominator divides comp_bound_base^degree.
            partial_sum = sum((v for pos, v in conv.items() if pos <= 511), Fraction())
            den = partial_sum.denominator
            v_p = valuation(den, p)
            assert v_p >= degree * 8 - 8
            rem = den // (p ** v_p)
            for q_b in factors(b):
                while rem % q_b == 0:
                    rem //= q_b
            assert (comp_bound_base ** degree) % rem == 0
        phase = Fraction()
        active = 1
        ell_at = {n: ell for _, n, ell in endpoints}
        for n in range(1, 2**10):
            if n in ell_at:
                active *= p * ell_at[n]
            phase = (b * phase + raw.get(n, 0)) % 1
            assert phase.denominator == active
        assert active == off_radix
    print("positive dense schedule: exact regrouping, pole units and all shifted denominators in 3 radices")


def check_construction():
    b, p = 2, 3
    for filled in (False, True):
        terms, endpoints = constructed_terms(b, p, 9, filled)
        previous = Fraction()
        active = 1
        off_radix = {}
        for k, endpoint, ell in endpoints:
            active *= p * ell
            off_radix[k] = active
            chunk = sum((c / b**n for n, c in terms.items() if 2**k <= n <= endpoint), Fraction())
            current = previous + chunk
            assert current.denominator == active * b**endpoint
            z = chunk * previous.denominator**2
            # Non-tautological height bound: z has denominator dividing p^k * ell * b^{w_k}
            # and numerator bounded without any b^{2^k} factor.
            w_k = endpoint - 2**k
            assert z.denominator <= p**k * ell * b**(2 * w_k + 2)
            assert abs(z.numerator) <= 2 * b * p**k * ell * (active // (p * ell))**2 * b**(2 * w_k + 4)
            previous = current
        assert max_partial_quotient(previous) < 2**16
        shifted = Fraction()
        for n in range(1, endpoints[-1][1] + 1):
            shifted = (b * shifted + terms.get(n, 0)) % 1
            if n >= 2:
                assert shifted.denominator == off_radix[n.bit_length() - 1]

        # Direct finite convolution vs reflected upper-set mass on each shell.
        # Integer fillers are included in the direct calculation.
        limit = 511
        active_terms = [(n, c / b**n) for n, c in terms.items() if n <= limit]
        for degree in (1, 2, 3, 4):
            coefficients = {0: Fraction(1)}
            for _ in range(degree):
                convolution = defaultdict(Fraction)
                for position, value in coefficients.items():
                    for n, c in active_terms:
                        if position + n <= limit:
                            convolution[position + n] += c * value
                coefficients = convolution
            prefix = Fraction()
            limit_precision = 4
            mod = p**limit_precision
            for n in range(1, limit + 1):
                prefix += coefficients.get(n, 0)
                k = n.bit_length() - 1
                if k < 2 * limit_precision:
                    continue
                scaled = prefix * p**(degree * k)
                assert scaled.denominator % p
                reflected = sum(p**sum(row) for row in product(range(limit_precision), repeat=degree)
                                if sum(row) < limit_precision
                                and sum(2**(k - h) for h in row) <= n)
                residue = scaled.numerator * pow(scaled.denominator, -1, mod) % mod
                assert residue == reflected % mod
        print(f"all-prime {'clustered' if filled else 'doubling'}: 9 endpoint denominators and mixed prefixes checked")


def check_upper_sets():
    # Enumerate all finite 2-D antichains in a five by five box.
    tested = 0
    for size in range(1, 6):
        for xs, ys in product(combinations(range(5), size), repeat=2):
            corners = tuple(zip(xs, reversed(ys)))
            top = Counter()
            for j in range(1, size + 1):
                for sub in combinations(corners, j):
                    exponent = max(x for x, _ in sub) + max(y for _, y in sub)
                    top[exponent] += (-1)**(j + 1)
            assert sum(top.values()) == 1
            for p in (3, 5):
                numerator = sum(c * p**e for e, c in top.items())
                assert numerator % (p - 1) == 1
                precision = 9
                direct = sum(p**(x + y) for x in range(precision) for y in range(precision - x)
                             if any(a <= x and b <= y for a, b in corners))
                assert (direct * (1 - p)**2 - numerator) % p**precision == 0
            tested += 1
    assert tested == 251
    print(f"upper sets: {tested} antichains, two odd pole primes")


if __name__ == "__main__":
    check_jumps()
    check_packets()
    for power, p in ((2, 3), (2, 5), (3, 3)):
        check_actual_packets(power, p)
    for power in (2, 3):
        ones, transitions = certified_bits(power, 2048)
        assert (ones, transitions) == {2: (1044, 1023), 3: (983, 1100)}[power]
        print(f"power {power}, first 2048 binary digits: {ones} ones, {transitions} transitions")
    weighted_mass_check()
    check_weight_and_orders()
    check_weighted_rows()
    check_folding()
    check_record_gaps()
    check_upper_sets()
    check_construction()
    check_dense_regrouping()
    print("All exact checks passed.")
