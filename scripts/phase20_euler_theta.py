"""Phase 20, Tracks A1-A4 and B5: exact checks for Euler's product, its powers and theta values.

Run from the repository root with the standard library only:

    python -B scripts/phase20_euler_theta.py

Every radix expansion used below is certified by exact integer arithmetic. For an integer
coefficient series z = sum_m a(m) b^-m the script forms the exact integer
sum_{m <= K} a(m) b^(K-m), adds the exactly computed next window of coefficients, and bounds
the remainder by an explicit envelope |a(m)| <= C (m+1)^beta. The floor of b^K z is accepted only
when both ends of the resulting interval have the same floor. The circle samples
x_n = {b^n z}, 0 <= n < N, are read from T certified digits, so each lies in [y_n, y_n + b^-T),
and the extreme discrepancy is evaluated from the sorted samples by the exact formula
D = max(0, max_i(i/N - y_(i))) - min(0, min_i((i-1)/N - y_(i))). The truncation and floating
point rounding change D by less than 1e-12, far below every reported digit.

Sections: A1 Euler's product E_b; A2 E_b^2, E_b^3 and polynomials; A3 binary theta values;
A4 eta powers and weight-one averages; B5 sparse quadratic polynomials.
"""

import math
import sys
import time
from bisect import bisect_right
from collections import Counter

sys.set_int_max_str_digits(0)

START = time.time()
CHECKS = [0]


def check(condition, message):
    CHECKS[0] += 1
    if not condition:
        raise AssertionError(message)


def header(title):
    print()
    print(title)
    print("-" * len(title))


# ----------------------------------------------------------------------------------------------
# Exact arithmetic
# ----------------------------------------------------------------------------------------------

def pentagonal_terms(limit):
    """Generalized pentagonal numbers p <= limit with Euler's sign: [(p, sign)] sorted by p."""
    terms = [(0, 1)]
    k = 1
    while k * (3 * k - 1) // 2 <= limit:
        sign = -1 if k % 2 else 1
        terms.append((k * (3 * k - 1) // 2, sign))
        if k * (3 * k + 1) // 2 <= limit:
            terms.append((k * (3 * k + 1) // 2, sign))
        k += 1
    return terms


def dense(terms, limit):
    out = [0] * (limit + 1)
    for position, value in terms:
        if position <= limit:
            out[position] += value
    return out


def pentagonal_count_below(bound):
    """Number of generalized pentagonal numbers p with 1 <= p < bound."""
    count = 0
    k = 1
    while k * (3 * k - 1) // 2 < bound:
        count += 1
        if k * (3 * k + 1) // 2 < bound:
            count += 1
        k += 1
    return count


def series_value(coefficients, lo, hi, base, powers):
    """sum_{lo <= m < hi} coefficients[m] * base^(hi-1-m), by divide and conquer."""
    if hi - lo <= 64:
        value = 0
        for m in range(lo, hi):
            value = value * base + coefficients[m]
        return value
    mid = (lo + hi) // 2
    length = hi - mid
    if length not in powers:
        powers[length] = base**length
    return (series_value(coefficients, lo, mid, base, powers) * powers[length]
            + series_value(coefficients, mid, hi, base, powers))


def to_digits(value, base, length, powers=None):
    """The `length` base-`base` digits of 0 <= value < base^length, most significant first."""
    if powers is None:
        powers = {}
    if length <= 256:
        digits = [0] * length
        for i in range(length - 1, -1, -1):
            value, digits[i] = divmod(value, base)
        check(value == 0, "digit conversion overflow")
        return digits
    half = length // 2
    low = length - half
    if low not in powers:
        powers[low] = base**low
    high_part, low_part = divmod(value, powers[low])
    return to_digits(high_part, base, half, powers) + to_digits(low_part, base, low, powers)


def envelope_sum(beta, base):
    """An upper bound for sum_{i >= 1} (1+i)^beta base^-i."""
    total = 0.0
    i = 1
    while True:
        term = (1 + i)**beta * float(base)**(-i)
        total += term
        if i > 4 * beta + 50 and term < 1e-30 * total:
            break
        i += 1
    return total * 1.001 + 1e-9


def certified_digits(coefficients, base, want, C, beta):
    """Certified integer part and first `want` fractional digits of sum a(m) base^-m.

    `coefficients` holds a(0..len-1) exactly and |a(m)| <= C (m+1)^beta for m >= len.
    Returns (integer_part, digits, K) where the floor of base^K z was certified for some
    K >= want; the digits returned are its first `want` fractional digits.
    """
    length = len(coefficients)
    bound = int(math.ceil(C * length**beta * envelope_sum(beta, base))) + 2
    powers = {}
    for K in range(want, length - 64):
        window = length - 1 - K
        tail = series_value(coefficients, K + 1, length, base, powers)
        scale = base**window
        low, high = (tail - bound) // scale, (tail + bound) // scale
        if low == high:
            head = series_value(coefficients, 0, K + 1, base, powers)
            integer_part, fraction = divmod(head + low, base**K)
            if base == 2:
                digits = [int(ch) for ch in bin(fraction)[2:].zfill(K)]
            elif base == 10:
                digits = [int(ch) for ch in str(fraction).zfill(K)]
            else:
                digits = to_digits(fraction, base, K)
            return integer_part, digits[:want], K
    raise AssertionError("no certified cutoff found")


def exact_floor(coefficients, base, K, C, beta):
    """Certified floor(base^K z) as an integer, for the same data as certified_digits."""
    integer_part, digits, K2 = certified_digits(coefficients, base, K, C, beta)
    value = integer_part
    for digit in digits:
        value = value * base + digit
    return value


# ----------------------------------------------------------------------------------------------
# Circle samples and discrepancy
# ----------------------------------------------------------------------------------------------

DIGITS_PER_SAMPLE = {2: 52, 3: 33, 10: 15}


def samples(digits, base, count):
    """y_n = 0.d_{n+1}...d_{n+T} for 0 <= n < count (digits[0] is the first digit)."""
    T = DIGITS_PER_SAMPLE[base]
    check(len(digits) >= count + T, "not enough certified digits")
    modulus = base**T
    window = 0
    for i in range(T):
        window = window * base + digits[i]
    inverse = 1.0 / modulus
    out = [0.0] * count
    for n in range(count):
        out[n] = window * inverse
        window = (window * base) % modulus + digits[n + T]
    return out


def discrepancy(values):
    ordered = sorted(values)
    count = len(ordered)
    high = 0.0
    low = 0.0
    for i, y in enumerate(ordered):
        upper = (i + 1) / count - y
        if upper > high:
            high = upper
        lower = i / count - y
        if lower < low:
            low = lower
    return high - low


def circle_bounds(values, eps):
    """Finite two-sided bounds for 1 - D from circle distances to zero.

    Upper: the arc [-d, d] (enlarged infinitesimally) gives 1 - D <= 2d + #{||x|| > d}/N.
    Lower (separation lemma): for an arc J of length l, either J misses the closed ball
    B(0, eps), so its cost is at least 1 - #{||x|| > eps}/N, or J lies in B(0, l + eps) and the
    cost is at least l + #{||x|| > l + eps}/N.
    """
    distances = sorted(min(y, 1.0 - y) for y in values)
    count = len(distances)
    upper = 1.0
    lower_arc = 1.0
    i = 0
    while i < count:
        d = distances[i]
        j = i
        while j + 1 < count and distances[j + 1] == d:
            j += 1
        far = count - (j + 1)  # samples strictly farther than d
        upper = min(upper, 2 * d + far / count)
        lower_arc = min(lower_arc, max(0.0, d - eps) + far / count)
        i = j + 1
    far_eps = count - bisect_right(distances, eps)
    lower = min(1.0 - far_eps / count, lower_arc)
    return lower, upper


def runs(digits):
    """Run-length encoding [(digit, start_position, length)] with 1-based positions."""
    out = []
    i = 0
    while i < len(digits):
        j = i
        while j < len(digits) and digits[j] == digits[i]:
            j += 1
        out.append((digits[i], i + 1, j - i))
        i = j
    return out


def constant_word_profile(run_list, digit, L, limit):
    """Breakpoints (N, Z(N)) of Z(N) = #{0 <= n < N : digits n+1..n+L all equal `digit`}.

    Between consecutive breakpoints Z(N) - N/2 is linear, so its extreme values over all
    prefixes 1 <= N <= limit occur at the returned points."""
    points = [(0, 0)]
    count = 0
    for d, start, length in run_list:
        if d == digit and length >= L:
            lo = start - 1
            hi = min(start - 1 + length - L, limit - 1)  # inclusive range of valid starts
            if lo >= limit:
                break
            points.append((lo, count))
            count += hi - lo + 1
            points.append((hi + 1, count))
    points.append((limit, count))
    return points


def check_profile(points, bound, normalizer):
    """Check |Z(N) - N/2| <= bound(N) for every prefix N >= 1. On [N1, N2] the deviation is at
    most its larger endpoint value and bound is nondecreasing, so it suffices to compare that
    value with bound(max(N1, 1)). Returns the largest normalized deviation and Z(limit)."""
    worst = 0.0
    for (n1, z1), (n2, z2) in zip(points, points[1:]):
        dev = max(abs(z1 - n1 / 2), abs(z2 - n2 / 2))
        check(dev <= bound(max(n1, 1)), f"constant word deviation near prefix {n1}")
        if n2 >= 64:
            worst = max(worst, abs(z2 - n2 / 2) / normalizer(n2))
    return worst, points[-1][1]


def windows(digits, base, length, limit):
    """Integers encoding the words digits[i:i+length], 0 <= i < limit."""
    modulus = base**length
    value = 0
    for i in range(length):
        value = value * base + digits[i]
    out = [0] * limit
    for i in range(limit):
        out[i] = value
        value = (value * base) % modulus + digits[i + length]
    return out


def distinct_words(window_list, base, length, L):
    shift = base**(length - L)
    return len({w // shift for w in window_list})


def smallest_prime_factors(limit):
    spf = list(range(limit + 1))
    for i in range(2, int(limit**0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factor(n, spf):
    out = {}
    while n > 1:
        p = spf[n]
        out[p] = out.get(p, 0) + 1
        n //= p
    return out


def chi_minus4(p):
    return 0 if p % 2 == 0 else (1 if p % 4 == 1 else -1)


def kronecker_disc(D, p):
    """Kronecker symbol (D/p) for an odd prime p or p = 2."""
    if p == 2:
        if D % 2 == 0:
            return 0
        return 1 if D % 8 in (1, 7) else -1
    r = D % p
    if r == 0:
        return 0
    return 1 if pow(r, (p - 1) // 2, p) == 1 else -1


# ----------------------------------------------------------------------------------------------
# A1. Euler's product E_b
# ----------------------------------------------------------------------------------------------

def euler_block_digits(base, length):
    """Digits 1..length of E_b from the block formula of Theorem 1 in euler-product.md."""
    d = [0] * (length + 1)

    def put(i, v):
        if 1 <= i <= length:
            d[i] = v

    put(1, base - 2)
    put(2, base - 1)
    j = 1
    while j * (6 * j - 1) <= length:
        a = j * (6 * j - 1)
        c = j * (6 * j + 1)
        dd = (2 * j + 1) * (3 * j + 1)
        e = (2 * j + 1) * (3 * j + 2)
        put(a, 1)
        for i in range(c + 1, dd):
            put(i, base - 1)
        put(dd, base - 2)
        for i in range(dd + 1, e + 1):
            put(i, base - 1)
        j += 1
    return d[1:]


def section_a1():
    header("A1. Euler's product E_b = prod (1 - b^-k)")
    # Pentagonal number theorem, exact power series identity through q^1500.
    X = 1500
    product = [0] * (X + 1)
    product[0] = 1
    for n in range(1, X + 1):
        for m in range(X, n - 1, -1):
            product[m] -= product[m - n]
    check(product == dense(pentagonal_terms(X), X), "pentagonal number theorem")
    print(f"pentagonal number theorem: product through q^{X} equals the signed pentagonal series")

    for k in range(1, 20001):
        minus, plus, nxt = k * (3 * k - 1) // 2, k * (3 * k + 1) // 2, (k + 1) * (3 * k + 2) // 2
        check(plus - minus == k and nxt - plus == 2 * k + 1, "pentagonal gaps")
    for M in range(1, 200001, 997):
        P = pentagonal_count_below(M)
        check(math.sqrt(24 * M + 1) / 3 - 2 <= P <= math.sqrt(24 * M + 1) / 3, "pentagonal count")
    print("gaps: k inside pair k, 2k+1 between pairs k and k+1 (k <= 20000); "
          "#{1 <= p < M} lies in [sqrt(24M+1)/3 - 2, sqrt(24M+1)/3]")

    results = {}
    NMAX = 2**20
    for base in (2, 3, 10):
        T = DIGITS_PER_SAMPLE[base]
        want = NMAX + T + 8
        coefficients = dense(pentagonal_terms(want + 6000), want + 6000)
        integer_part, digits, _ = certified_digits(coefficients, base, want, 1.0, 0.0)
        check(integer_part == 0, "E_b in (0,1)")
        check(digits == euler_block_digits(base, want), f"block formula, base {base}")
        results[base] = digits
        print(f"base {base}: {want} certified digits agree with the block formula; "
              f"E_{base} = 0.{''.join(map(str, digits[:40]))}...")

    print()
    print("Sharp asymptotic 1 - D_N(E_b) ~ sqrt(2/3) log_b N / sqrt N  (rho_N = this value).")
    print("c_N = (1 - D_N) N / P_N - (1/2) log_b N with P_N = #{pentagonal 1 <= p <= N} stays bounded.")
    print(f"{'b':>3} {'N':>8} {'1-D_N':>10} {'ratio to rho_N':>15} {'c_N':>8} "
          f"{'sep. lower':>11} {'arc upper':>10} {'Lean upper':>11}")
    table = []
    for base in (2, 3, 10):
        ys = samples(results[base], base, NMAX)
        for e in range(10, 21, 2):
            N = 2**e
            prefix = ys[:N]
            gap = 1 - discrepancy(prefix)
            P = pentagonal_count_below(N + 1)
            rho = math.sqrt(2 / 3) * math.log(N) / (math.sqrt(N) * math.log(base))
            c = gap * N / P - 0.5 * math.log(N, base)
            lower, upper = circle_bounds(prefix, 1.0 / N)
            # Lean-backed finite inequality: 1 - D_N <= 4 b^-w + w #{1 <= p < N+w} / N.
            lean = min(4 * base**(-w) + w * pentagonal_count_below(N + w) / N for w in range(1, 60))
            check(lower - 1e-12 <= gap <= upper + 1e-12, "separation and arc bounds")
            check(gap <= lean + 1e-12, "Lean sparse transfer bound")
            if N >= 2**14:
                check(0.9 < gap / rho < 1.1, "leading constant sqrt(2/3)/log b")
                check(abs(c) < 0.5, "second-order term O(1/sqrt N)")
            table.append((base, N, gap / rho))
            print(f"{base:>3} {N:>8} {gap:>10.6f} {gap / rho:>15.4f} {c:>8.3f} "
                  f"{lower:>11.6f} {upper:>10.6f} {lean:>11.6f}")

    print()
    print("Word frequencies: all prefixes N <= 2^20, words 0^L and (b-1)^L.")
    print("Proved bound |Z_L(N) - N/2| <= (2L+3) sqrt(N/6) + 3L^2 + 5L + 7, checked at every prefix.")
    for base in (2, 3, 10):
        run_list = runs(results[base][:NMAX + 16])
        parts = []
        for L in (1, 2, 3, 4, 6, 8):
            pair = []
            worst_both = 0.0
            for digit in (0, base - 1):
                points = constant_word_profile(run_list, digit, L, NMAX)
                worst, count = check_profile(
                    points, lambda n, L=L: (2 * L + 3) * math.sqrt(n / 6) + 3 * L * L + 5 * L + 7,
                    lambda n, L=L: (L + 1) * math.sqrt(n))
                pair.append(count / NMAX)
                worst_both = max(worst_both, worst)
            parts.append(f"L={L}: {pair[0]:.5f}/{pair[1]:.5f} (max |Z-N/2|/((L+1)sqrt N) {worst_both:.3f})")
        print(f"  base {base}: freq(0^L)/freq((b-1)^L) at N=2^20; " + "; ".join(parts[:3]))
        print("          " + "; ".join(parts[3:]))
    # Digit frequencies: simple normality in base 2 only.
    d2 = results[2][:NMAX]
    print(f"  E_2 one-digit frequency at N=2^20: {sum(d2) / NMAX:.6f} (simply normal in base 2)")
    for base in (3, 10):
        counts = Counter(results[base][:NMAX])
        middle = sum(counts[v] for v in range(1, base - 1)) / NMAX
        check(middle < 4 / math.sqrt(NMAX) * 2, "middle digits have frequency O(1/sqrt N)")
        print(f"  E_{base}: frequency of digits 1..b-2 at N=2^20: {middle:.6f}")

    # Nondisjunctivity witnesses and complexity.
    text2 = "".join(map(str, results[2][:NMAX]))
    check("10001" not in text2 and "1000001" not in text2, "odd zero runs absent in E_2")
    zero_runs = Counter(length for d, s, length in runs(results[2][:NMAX]) if d == 0 and s > 1)
    check(all(length == 1 or length % 2 == 0 for length in zero_runs), "interior zero runs")
    for base in (3, 10):
        text = results[base][:NMAX]
        check(all(not (text[i] == 1 and text[i + 1] == 1) for i in range(NMAX - 1)), "11 absent")
    d = results[2]
    transitions = sum(1 for i in range(NMAX) if d[i] == 0 and d[i + 1] == 1)
    print(f"  missing words: 1 0^m 1 for odd m >= 3 in base 2 (interior zero-run lengths are 1 or even); "
          f"'11' in bases 3 and 10. Count of '01' in E_2 up to 2^20: {transitions} "
          f"= {transitions / math.sqrt(NMAX):.3f} sqrt N")
    wins = windows(results[2], 2, 16, 2**18)
    complexity = [distinct_words(wins, 2, 16, L) for L in (4, 8, 12, 16)]
    print(f"  distinct binary words of length 4, 8, 12, 16 in the first 2^18 digits of E_2: {complexity}")
    return results


# ----------------------------------------------------------------------------------------------
# A2. Powers and polynomials
# ----------------------------------------------------------------------------------------------

def square_coefficients(limit):
    terms = pentagonal_terms(limit)
    a = [0] * (limit + 1)
    for i, (p, s) in enumerate(terms):
        for q, u in terms[i:]:
            if p + q > limit:
                break
            a[p + q] += s * u * (1 if p == q else 2)
    return a


def jacobi_coefficients(limit):
    a = [0] * (limit + 1)
    k = 0
    while k * (k + 1) // 2 <= limit:
        a[k * (k + 1) // 2] = (-1)**k * (2 * k + 1)
        k += 1
    return a


PREFIX_CACHE = {}


def prefix_tables(coefficients):
    key = id(coefficients)
    if key not in PREFIX_CACHE:
        support, absolute = [0], [0]
        for m in range(1, len(coefficients)):
            support.append(support[-1] + (1 if coefficients[m] else 0))
            absolute.append(absolute[-1] + abs(coefficients[m]))
        PREFIX_CACHE[key] = (coefficients, support, absolute)
    return PREFIX_CACHE[key][1], PREFIX_CACHE[key][2]


def transfer_bound(coefficients, base, N, envelope_C, envelope_beta):
    """min over L of 2 sqrt(2 c_L) + L S_L / N with c_L = b^-L A*(N,L) / ((b-1) N): the
    coefficient transfer inequality (theta-and-modular.md, Lemma 1) optimized in eps.
    Here S_L = #{1 <= m <= N+L-1 : a(m) != 0} and A*(N,L) = sum_{m > L} |a(m)| b^-(m-L-N)_+."""
    support, absolute = prefix_tables(coefficients)
    best = float("inf")
    window = 400
    for L in range(1, 80):
        if N + L + window >= len(coefficients):
            break
        S = support[N + L - 1]
        A = absolute[N + L] - absolute[L]
        tail = 0.0
        for m in range(N + L + 1, N + L + window):
            tail += abs(coefficients[m]) * float(base)**(-(m - L - N))
        start = N + L + window
        tail += (envelope_C * (start + 1)**envelope_beta * float(base)**(-window)
                 * (1 + envelope_sum(envelope_beta, base)))
        c = float(base)**(-L) * (A + tail) / ((base - 1) * N)
        best = min(best, 2 * math.sqrt(2 * c) + L * S / N)
    return best


def section_a2(euler_digits):
    header("A2. E_b^2 (eta(12z)^2), E_b^3 (Jacobi) and polynomials in E_b")
    X = 2**20 + 7000
    a2 = square_coefficients(X)
    # Support and multiplicative formula c(12n+1) = a_2(n).
    small = 2**17
    spf = smallest_prime_factors(12 * small + 1)
    mismatches = 0
    for n in range(small + 1):
        f = factor(12 * n + 1, spf)
        supported = all(e % 2 == 0 for p, e in f.items() if p % 12 != 1)
        predicted = 1
        for p, e in f.items():
            if p % 12 == 1:
                predicted *= e + 1
        if supported:
            mismatches += abs(a2[n]) != predicted
        else:
            mismatches += a2[n] != 0
    check(mismatches == 0, "support criterion for eta(12z)^2")

    def c(m):
        return a2[(m - 1) // 12] if m % 12 == 1 else 0

    hecke = 0
    for p in range(5, int((12 * small + 1)**0.5) + 1):
        if spf[p] != p:
            continue
        check(abs(c(p)) == (2 if p % 12 == 1 else 0), "|c(p)|")
        check(c(p * p) == c(p)**2 - chi_minus4(p), "Hecke relation at p^2")
        if p**3 <= 12 * small + 1:
            check(c(p**3) == c(p) * c(p * p) - chi_minus4(p) * c(p), "Hecke relation at p^3")
        hecke += 1
    pairs = 0
    for m1 in range(1, 3000, 2):
        for m2 in range(m1 + 2, 3000, 6):
            if m1 * m2 <= 12 * small + 1 and math.gcd(m1, m2) == 1 and m1 % 3 and m2 % 3:
                check(c(m1 * m2) == c(m1) * c(m2), "multiplicativity")
                pairs += 1
    check(a2[7] == 0 and 85 == 2**2 + 9**2 == 6**2 + 7**2, "cancellation at n = 7")
    check(a2[12] == 0 and 145 == 1 + 144, "cancellation at n = 12")
    print(f"a_2(n) = c(12n+1) for n <= 2^17: nonzero exactly when every prime p != 1 (mod 12) has "
          f"even exponent, |c| = prod_(p = 1 mod 12)(e+1); Hecke relations at {hecke} primes; "
          f"multiplicativity on {pairs} coprime pairs; a_2(7) = a_2(12) = 0 although 85, 145 are "
          f"sums of two squares")

    two_square = 0
    for n in range(1, small + 1):
        f = factor(12 * n + 1, spf)
        two_square += all(e % 2 == 0 for p, e in f.items() if p % 4 == 3)
    support_small = sum(1 for n in range(1, small + 1) if a2[n])
    print(f"n <= 2^17: {support_small} indices with a_2(n) != 0 versus {two_square} with 12n+1 a sum "
          f"of two squares")
    print(f"{'X':>8} {'S(X)/X':>8} {'S(X)(log X)^(3/4)/X':>20} {'A(X)/X':>8} {'A(X)(log X)^(1/2)/X':>20}")
    for e in (12, 14, 16, 18, 20):
        Y = 2**e
        S = sum(1 for n in range(1, Y + 1) if a2[n])
        A = sum(abs(v) for v in a2[1:Y + 1])
        check(A <= (2 * math.sqrt(2 * Y / 3) + 2)**2, "A(X) = O(X) pair bound")
        print(f"{Y:>8} {S / Y:>8.4f} {S / Y * math.log(Y)**0.75:>20.4f} {A / Y:>8.4f} "
              f"{A / Y * math.log(Y)**0.5:>20.4f}")

    # Envelope: |a_2(m)| <= #{generalized pentagonals <= m} <= 2 sqrt(m) + 1 <= 3 (m+1)^(1/2).
    print()
    print("Discrepancy of E_b^2 against the transfer bound and log log N / (log N)^(3/4).")
    for base, nmax in ((2, 2**20), (3, 2**18)):
        T = DIGITS_PER_SAMPLE[base]
        _, digits, _ = certified_digits(a2, base, nmax + T + 8, 3.0, 0.5)
        ys = samples(digits, base, nmax)
        for e in range(10, int(math.log2(nmax)) + 1, 2):
            N = 2**e
            gap = 1 - discrepancy(ys[:N])
            bound = transfer_bound(a2, base, N, 3.0, 0.5)
            check(gap <= bound + 1e-12, "transfer bound for E^2")
            scale = math.log(math.log(N)) / math.log(N)**0.75
            scale_half = math.log(math.log(N)) / math.log(N)**0.5
            print(f"  b={base} N={N:>8}: 1-D_N={gap:.5f}  transfer bound={bound:.4f}  "
                  f"(1-D_N)/scale_3/4={gap / scale:.4f}  (1-D_N)/scale_1/2={gap / scale_half:.4f}")
    J = 3
    isolated = sum(1 for n in range(J + 1, 2**20)
                   if a2[n] and all(a2[n + j] == 0 and a2[n - j] == 0 for j in range(1, J + 1)))
    support = sum(1 for n in range(1, 2**20) if a2[n])
    print(f"  isolated support (no other nonzero coefficient within distance {J}) below 2^20: "
          f"{isolated}/{support} = {isolated / support:.3f}")

    # E^3: Jacobi's identity, digit blocks, discrepancy, frequencies.
    header("A2. E_b^3 = sum (-1)^k (2k+1) b^(-k(k+1)/2)")
    Y = 20000
    terms = pentagonal_terms(Y)
    cube = [0] * (Y + 1)
    for n in range(Y + 1):
        total = 0
        for p, s in terms:
            if p > n:
                break
            total += s * a2[n - p]
        cube[n] = total
    check(cube == jacobi_coefficients(Y), "Jacobi identity")
    print(f"Jacobi identity E^3 = sum (-1)^k (2k+1) q^(k(k+1)/2) checked through q^{Y}")
    a3 = jacobi_coefficients(2**20 + 9000)
    cube_digits = {}
    for base, nmax in ((2, 2**20), (3, 2**20)):
        T = DIGITS_PER_SAMPLE[base]
        _, digits, _ = certified_digits(a3, base, nmax + T + 8, 3.0, 0.5)
        cube_digits[base] = digits
        # Block structure after position 6: zeros, digits of 4j ending at T_2j, then the
        # (2j+1)-digit expansion of b^(2j+1) - 4j - 3 ending at T_(2j+1).
        j = 2
        blocks = 0
        while (2 * j + 1) * (2 * j + 2) // 2 <= len(digits):
            t_prev = (2 * j - 1) * (2 * j) // 2
            t_even = 2 * j * (2 * j + 1) // 2
            t_odd = (2 * j + 1) * (2 * j + 2) // 2
            four_j = to_digits(4 * j, base, t_even - t_prev)
            rest = to_digits(base**(2 * j + 1) - 4 * j - 3, base, 2 * j + 1)
            check(digits[t_prev:t_odd] == four_j + rest, "E^3 block formula")
            j += 1
            blocks += 1
        print(f"base {base}: {len(digits)} certified digits; block formula verified for {blocks} blocks "
              f"(j >= 2); E_{base}^3 = 0.{''.join(map(str, digits[:36]))}...")
    print()
    print("Sharp asymptotic 1 - D_N(E_b^3) ~ sqrt(2) log_b N / sqrt N  (rho3_N = this value);")
    print("c_N = (1 - D_N) N / K_N - log_b N with K_N = #{k >= 1 : k(k+1)/2 <= N}.")
    print(f"{'b':>3} {'N':>8} {'1-D_N':>10} {'ratio':>8} {'c_N':>8} {'sep. lower':>11} "
          f"{'arc upper':>10} {'paper upper':>12}")
    for base in (2, 3):
        ys = samples(cube_digits[base], base, 2**20)
        for e in range(10, 21, 2):
            N = 2**e
            prefix = ys[:N]
            gap = 1 - discrepancy(prefix)
            K = int((math.isqrt(8 * N + 1) - 1) // 2)
            rho = math.sqrt(2) * math.log(N) / (math.sqrt(N) * math.log(base))
            cN = gap * N / K - math.log(N, base)
            lower, upper = circle_bounds(prefix, 1.0 / N)
            # Paper upper bound: ||x_n|| <= 2(2k+1) b^-r before T_k, so
            # 1 - D_N <= 2 eps + (1/N) sum_{k : T_k <= N + R_k} min(R_k, k).
            paper = float("inf")
            for w in range(1, 80):
                eps = float(base)**(-w)
                far = 0
                k = 1
                while True:
                    R = max(0, math.ceil(math.log(2 * (2 * k + 1) / eps, base)))
                    if k * (k + 1) // 2 - min(R, k) >= N:
                        break
                    far += min(R, k)
                    k += 1
                paper = min(paper, 2 * eps + far / N)
            check(lower - 1e-12 <= gap <= upper + 1e-12, "separation and arc bounds, E^3")
            check(gap <= paper + 1e-12, "paper upper bound, E^3")
            if N >= 2**14:
                check(0.9 < gap / rho < 1.1, "leading constant sqrt(2)/log b")
                check(abs(cN) < 1.5, "second order term for E^3")
            print(f"{base:>3} {N:>8} {gap:>10.6f} {gap / rho:>8.4f} {cN:>8.3f} {lower:>11.6f} "
                  f"{upper:>10.6f} {paper:>12.6f}")
    print("  predicted centre of c_N: log_b(4 ln b) - 1/2 - [b odd]/(b-1) = "
          f"{math.log(4 * math.log(2), 2) - 0.5:.3f} (b=2), "
          f"{math.log(4 * math.log(3), 3) - 1.0:.3f} (b=3); oscillation is O(1)")
    NMAX = 2**20
    for base in (2, 3):
        run_list = runs(cube_digits[base][:NMAX + 16])
        parts = []
        for L in (1, 2, 4, 8):
            pair = []
            worst_both = 0.0
            for digit in (0, base - 1):
                points = constant_word_profile(run_list, digit, L, NMAX)
                worst, count = check_profile(
                    points,
                    lambda n, L=L: 2 * (L + math.log(n + 1, base) + 2) * math.sqrt(2 * n + 1) + 4 * L * L + 20,
                    lambda n, L=L: (L + math.log(n, base)) * math.sqrt(n))
                pair.append(count / NMAX)
                worst_both = max(worst_both, worst)
            parts.append(f"L={L}: {pair[0]:.4f}/{pair[1]:.4f} (max dev/((L+log_b N)sqrt N) {worst_both:.3f})")
        print(f"  base {base} freq(0^L)/freq((b-1)^L) at 2^20: " + "; ".join(parts))
    wins3 = windows(cube_digits[2], 2, 16, NMAX)
    wins1 = windows(euler_digits[2], 2, 16, NMAX)
    full = 0
    for L in range(1, 17):
        if distinct_words(wins3, 2, 16, L) == 2**L:
            full = L
        else:
            break
    check(full >= 8, "short binary words all occur in E_2^3")
    print(f"  every binary word of length <= {full} occurs in the first 2^20 digits of E_2^3 "
          f"(disjunctive: the digits of 4j appear verbatim); E_2 has "
          f"{distinct_words(wins1, 2, 16, 12)} distinct words of length 12 there")
    counts3 = Counter(cube_digits[3][:NMAX])
    print(f"  E_2^3 one-digit frequency {sum(cube_digits[2][:NMAX]) / NMAX:.5f}; E_3^3 digit-1 frequency "
          f"{counts3[1] / NMAX:.5f}")

    # Rational coefficients: (1/3) E_2 in base 2 and (1/2) E_3 in base 3.
    header("A2. Polynomials in E_b and rational scalars")
    euler = dense(pentagonal_terms(2**20 + 7000), 2**20 + 7000)
    for base, d, atoms, masses, limit in ((2, 3, (0, 1 / 3, 2 / 3), (1 / 6, 5 / 12, 5 / 12), 0.5),
                                           (3, 2, (0, 1 / 2), (1 / 3, 2 / 3), 2 / 3)):
        K = 2**20 + 80
        F = exact_floor(euler, base, K, 1.0, 0.0)
        G = F // d  # floor(b^K E / d)
        fraction = G % base**K
        digits = (to_digits(fraction, base, K) if base != 2
                  else [int(ch) for ch in bin(fraction)[2:].zfill(K)])
        ys = samples(digits, base, 2**20)
        values = []
        for N in (2**16, 2**18, 2**20):
            values.append(discrepancy(ys[:N]))
        found = []
        for atom in atoms:
            found.append(sum(1 for y in ys if min(abs(y - atom), 1 - abs(y - atom)) < 0.01) / len(ys))
        for got, want in zip(found, masses):
            check(abs(got - want) < 0.01, "limiting atom masses")
        check(abs(values[-1] - limit) < 0.02, "limiting discrepancy of E_b/d")
        print(f"  (1/{d}) E_{base} in base {base}: D_N at N=2^16,2^18,2^20 = "
              f"{', '.join(f'{v:.4f}' for v in values)} -> {limit:.4f}; masses near "
              f"{[round(a, 3) for a in atoms]}: {[round(m, 4) for m in found]} (predicted "
              f"{[round(m, 4) for m in masses]})")
    # Polynomials with Z[1/2] coefficients: 8 P(E_2) has integer coefficients.
    limit = 2**18 + 7000
    for label, (c1, c2, c3, C) in (("P(x) = 5/8 + 3x - 2x^3", (24, 0, -16, 80.0)),
                                    ("P(x) = 3 - 5x + x^2/4 - 7x^3", (-40, 2, -56, 220.0))):
        poly = [c1 * euler[m] + c2 * a2[m] + c3 * a3[m] for m in range(limit + 1)]
        _, digits, _ = certified_digits(poly, 2, 2**18 + 60, C, 0.5)
        ys = samples(digits, 2, 2**18)
        gaps = [1 - discrepancy(ys[:N]) for N in (2**14, 2**16, 2**18)]
        print(f"  8 P(E_2), {label}: 1 - D_N at N = 2^14, 2^16, 2^18 = "
              f"{', '.join(f'{g:.4f}' for g in gaps)} (in K_2; the x^2 term has the slow rate)")
    return a2, a3


# ----------------------------------------------------------------------------------------------
# A3. Binary quadratic forms
# ----------------------------------------------------------------------------------------------

def form_counts(a, b0, c, limit):
    disc = b0 * b0 - 4 * a * c
    r = [0] * (limit + 1)
    n_max = math.isqrt(4 * a * limit // (-disc)) + 1
    for n in range(-n_max, n_max + 1):
        # a m^2 + b0 n m + c n^2 <= limit
        A, B, C = a, b0 * n, c * n * n - limit
        root = B * B - 4 * A * C
        if root < 0:
            continue
        s = math.isqrt(root)
        lo = (-B - s) // (2 * A) - 1
        hi = (-B + s) // (2 * A) + 1
        for m in range(lo, hi + 1):
            value = a * m * m + b0 * m * n + c * n * n
            if 0 <= value <= limit:
                r[value] += 1
    return r, disc


def section_a3():
    header("A3. Theta values Theta_Q(1/b) = sum b^-Q(m,n)")
    X = 2**18 + 7000
    spf = smallest_prime_factors(2**16)
    forms = [(1, 0, 1), (1, 1, 1), (1, 0, 2), (1, 0, 5)]
    for a, b0, c in forms:
        r, disc = form_counts(a, b0, c, X)
        Y = 2**18
        lattice = sum(r[:Y + 1])
        area = 2 * math.pi * Y / math.sqrt(-disc)
        check(abs(lattice - area) <= 10 * math.sqrt(Y), "lattice point count")
        # Represented integers avoid odd powers of inert primes.
        for j in range(1, 2**16 + 1):
            if r[j]:
                for p, e in factor(j, spf).items():
                    if kronecker_disc(disc, p) == -1:
                        check(e % 2 == 0, "inert primes occur to even powers")
        S = sum(1 for j in range(1, Y + 1) if r[j])
        A = sum(r[1:Y + 1])
        C_env = 4 * math.sqrt(4 * a / -disc) + 2
        _, digits, _ = certified_digits(r, 2, Y + 60, C_env, 0.5)
        ys = samples(digits, 2, Y)
        line = []
        for e in (10, 14, 18):
            N = 2**e
            gap = 1 - discrepancy(ys[:N])
            bound = transfer_bound(r, 2, N, C_env, 0.5)
            check(gap <= bound + 1e-12, "transfer bound for theta")
            line.append(f"N=2^{e}: 1-D={gap:.4f} (bound {bound:.3f}, /scale {gap * math.sqrt(math.log(N)) / math.log(math.log(N)):.3f})")
        if (a, b0, c) == (1, 0, 1):
            # Effective width of a coefficient: digits of r_Q(j) after removing the trailing
            # zeros b^v_b(r_Q(j)). Shifts reading those trailing zeros stay near 0.
            for base in (2, 3):
                widths = []
                for Z in (2**12, 2**15, 2**18):
                    total = 0.0
                    count = 0
                    for j in range(1, Z + 1):
                        if r[j]:
                            v = r[j]
                            while v % base == 0:
                                v //= base
                            total += math.log(v, base)
                            count += 1
                    widths.append(total / count)
                print(f"  x^2+y^2, mean over the support of log_{base}(r_Q(j) / {base}^v): "
                      f"{', '.join(f'{w:.3f}' for w in widths)} at X = 2^12, 2^15, 2^18")
        name = f"{a}m^2{'+' + str(b0) + 'mn' if b0 else ''}+{c}n^2"
        print(f"  Q = {name:<12} disc {disc:>4}: sum r_Q(j<=2^18) - 2piX/sqrt|D| = {lattice - area:+.1f}; "
              f"S(X)sqrt(log X)/X = {S / Y * math.sqrt(math.log(Y)):.4f}; A(X)/X = {A / Y:.4f}")
        print("      " + "; ".join(line))


# ----------------------------------------------------------------------------------------------
# A4. Eta powers and weight-one averages
# ----------------------------------------------------------------------------------------------

def eta_power(r, limit):
    """Coefficients of prod (1-q^n)^r via n f_n = sum_k e_k ((r+1)k - n) f_(n-k)."""
    terms = [(p, s) for p, s in pentagonal_terms(limit) if p > 0]
    f = [0] * (limit + 1)
    f[0] = 1
    for n in range(1, limit + 1):
        total = 0
        for k, s in terms:
            if k > n:
                break
            total += s * ((r + 1) * k - n) * f[n - k]
        check(total % n == 0, "eta power recurrence")
        f[n] = total // n
    return f


def sparse_product(u, v, limit):
    out = [0] * (limit + 1)
    us = [(i, x) for i, x in enumerate(u[:limit + 1]) if x]
    vs = [(i, x) for i, x in enumerate(v[:limit + 1]) if x]
    for i, x in us:
        for j, y in vs:
            if i + j > limit:
                break
            out[i + j] += x * y
    return out


def quaternion_group(generators):
    def mul(p, q):
        a1, b1, c1, d1 = p
        a2, b2, c2, d2 = q
        return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
                a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)

    def key(q):
        return tuple(round(x, 9) + 0.0 for x in q)

    elements = {key((1.0, 0.0, 0.0, 0.0)): (1.0, 0.0, 0.0, 0.0)}
    frontier = list(elements.values())
    while frontier and len(elements) <= 1000:
        new = []
        for q in frontier:
            for g in generators:
                p = mul(q, g)
                if key(p) not in elements:
                    elements[key(p)] = p
                    new.append(p)
        frontier = new
    return list(elements.values())


def section_a4(a2, a3):
    header("A4. Weight-one averages: binary polyhedral groups and Eisenstein characters")
    phi = (1 + math.sqrt(5)) / 2
    groups = {}
    for n in range(2, 7):
        groups[f"2D_{n}"] = (quaternion_group([(math.cos(math.pi / n), math.sin(math.pi / n), 0.0, 0.0),
                                               (0.0, 0.0, 1.0, 0.0)]), 4 * n)
    t = (0.5, 0.5, 0.5, 0.5)
    groups["2T (A4)"] = (quaternion_group([(0.0, 1.0, 0.0, 0.0), (0.0, 0.0, 1.0, 0.0), t]), 24)
    i_unit, j_unit = (0.0, 1.0, 0.0, 0.0), (0.0, 0.0, 1.0, 0.0)
    groups["2O (S4)"] = (quaternion_group([i_unit, j_unit, t,
                                           (1 / math.sqrt(2), 1 / math.sqrt(2), 0.0, 0.0)]), 48)
    groups["2I (A5)"] = (quaternion_group([i_unit, j_unit, t, (0.0, 0.5, 1 / (2 * phi), phi / 2)]), 120)
    print(f"{'group':>9} {'order':>6} {'E|tr|':>8} {'P(tr=0)':>8}")
    for name, (elements, order) in groups.items():
        check(len(elements) == order, f"order of {name}")
        traces = [abs(2 * q[0]) for q in elements]
        mean = sum(traces) / order
        zero = sum(1 for x in traces if x < 1e-9) / order
        check(mean < 1, "E|tr| < 1 for every finite projective image")
        print(f"{name:>9} {order:>6} {mean:>8.4f} {zero:>8.4f}")
    print("Eisenstein E_1(chi1, chi2): |e(p)| = |1 + psi(p)|, psi = chi2/chi1 odd of even order m:")
    parts = []
    for m in (2, 4, 6, 8, 12, 24):
        mean = sum(abs(1 + complex(math.cos(2 * math.pi * j / m), math.sin(2 * math.pi * j / m)))
                   for j in range(m)) / m
        parts.append(f"m={m}: {mean:.4f}")
    print("  E|1+psi| " + ", ".join(parts) + f"; limit 4/pi = {4 / math.pi:.4f}; zero density 1/m")

    header("A4. Serre's lacunary eta powers and odd powers: E_2^r")
    X = 2**14
    print(f"{'r':>3} {'weight':>6} {'zero density':>12} {'1-D_N':>8} {'D_N':>8} {'freq(1)':>8} "
          f"{'max |a| bits':>12} {'width*density':>14}")
    euler = dense(pentagonal_terms(X + 3000), X + 3000)
    for r in (1, 2, 3, 4, 5, 6, 8, 10, 14, 26):
        if r == 1:
            f = euler
        elif r == 2:
            f = a2[:X + 3001]
        elif r == 3:
            f = a3[:X + 3001]
        else:
            f = eta_power(r, X + 3000)
        if r in (2, 3):
            check(f == eta_power(r, X + 3000), "recurrence agrees with direct coefficients")
        zero = sum(1 for v in f[1:X + 1] if v == 0) / X
        C_env = 3.0**(r - 1)
        _, digits, _ = certified_digits(f, 2, X + 60, C_env, (r - 1) / 2)
        D = discrepancy(samples(digits, 2, X))
        bits = max(abs(v) for v in f[:X + 1]).bit_length()
        width = max(0.0, (r / 2 - 1) / 2) * math.log2(X)
        print(f"{r:>3} {r / 2:>6} {zero:>12.4f} {1 - D:>8.4f} {D:>8.4f} {sum(digits[:X]) / X:>8.4f} "
              f"{bits:>12} {width * (1 - zero):>14.2f}")
        if r in (4, 5, 6, 8, 10, 14, 26):
            check(D < 0.05, "higher eta powers look equidistributed at N = 2^14")
        if r == 5:
            check(zero < 0.01, "eta^5 is not lacunary in this range")
    # Larger samples for weights 2 and 3 via sparse products.
    Y = 2**18
    e4 = sparse_product(a3[:Y + 3001], dense(pentagonal_terms(Y + 3000), Y + 3000), Y + 3000)
    e6 = sparse_product(a3[:Y + 3001], a3[:Y + 3001], Y + 3000)
    check(e4[:X + 1] == eta_power(4, X)[:X + 1], "E^4 two ways")
    for r, f in ((4, e4), (6, e6)):
        zero = sum(1 for v in f[1:Y + 1] if v == 0) / Y
        _, digits, _ = certified_digits(f, 2, Y + 60, 3.0**(r - 1), (r - 1) / 2)
        D = discrepancy(samples(digits, 2, Y))
        check(D < 0.02, "weight 2 and 3 eta powers look equidistributed at N = 2^18")
        print(f"  r={r} at N=2^18: zero density {zero:.4f}, D_N = {D:.5f}, sqrt(N) D_N = {D * math.sqrt(Y):.3f}")


# ----------------------------------------------------------------------------------------------
# B5. Sparse quadratic polynomials and the degree-three obstruction
# ----------------------------------------------------------------------------------------------

def section_b5():
    header("B5. Degree-two polynomials in unary quadratic series; degree three")
    X = 2**18 + 6000
    theta3 = [0] * (X + 1)
    k = 0
    while k * k <= X:
        theta3[k * k] += 1 if k == 0 else 2
        k += 1
    euler = dense(pentagonal_terms(X), X)
    product = sparse_product(theta3, euler, X)
    Y = 2**18
    # Support: m in supp => 24m+1 = t^2 + 24 k^2 with t = 6j - 1.
    representable = set()
    t = 1
    while t * t <= 24 * Y + 1:
        if math.gcd(t, 6) == 1:
            k = 0
            while t * t + 24 * k * k <= 24 * Y + 1:
                representable.add(t * t + 24 * k * k)
                k += 1
        t += 1
    for m in range(1, Y + 1):
        if product[m]:
            check(24 * m + 1 in representable, "support of Theta_3 E in values of t^2 + 24k^2")
    S = sum(1 for m in range(1, Y + 1) if product[m])
    A = sum(abs(v) for v in product[1:Y + 1])
    _, digits, _ = certified_digits(product, 2, Y + 60, 8.0, 0.5)
    ys = samples(digits, 2, Y)
    gap = 1 - discrepancy(ys)
    bound = transfer_bound(product, 2, Y, 8.0, 0.5)
    check(gap <= bound + 1e-12, "transfer bound for Theta_3 E_2")
    print(f"  Theta_3(1/2) E_2: S(X) sqrt(log X)/X = {S / Y * math.sqrt(math.log(Y)):.4f}, A(X)/X = {A / Y:.4f}, "
          f"1-D_N = {gap:.4f} <= transfer bound {bound:.3f} at N = 2^18")
    # Three squares: positive density 5/6 and an equidistributed-looking expansion.
    Z = 2**14 + 3000
    two = [0] * (Z + 1)
    root = math.isqrt(Z)
    for x in range(-root, root + 1):
        for y in range(-root, root + 1):
            if x * x + y * y <= Z:
                two[x * x + y * y] += 1
    reps = [0] * (Z + 1)
    for n in range(Z + 1):
        total = 0
        zz = 0
        while zz * zz <= n:
            total += two[n - zz * zz] * (1 if zz == 0 else 2)
            zz += 1
        reps[n] = total
    W = 2**14
    represented = 0
    for n in range(1, W + 1):
        m = n
        while m % 4 == 0:
            m //= 4
        excluded = m % 8 == 7
        check((reps[n] == 0) == excluded, "Legendre's three-square theorem")
        represented += not excluded
    _, digits, _ = certified_digits(reps, 2, W + 60, 20.0, 1.0)
    D = discrepancy(samples(digits, 2, W))
    check(D < 0.05, "Theta_3^3 shows no concentration")
    print(f"  Theta_3(1/2)^3: r_3(n) > 0 for {represented / W:.4f} of n <= 2^14 (limit 5/6 = {5 / 6:.4f}); "
          f"D_N = {D:.4f} at N = 2^14 (no concentration)")


def main():
    euler_digits = section_a1()
    a2, a3 = section_a2(euler_digits)
    section_a3()
    section_a4(a2, a3)
    section_b5()
    print()
    print(f"All {CHECKS[0]} checks passed in {time.time() - START:.1f} s.")


if __name__ == "__main__":
    main()
