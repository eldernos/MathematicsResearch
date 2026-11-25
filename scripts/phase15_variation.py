"""Phase 15: position-weighted transfer, lift concentration with a multiplicative mesh,
rigidity of eventual upper-band data, moving-prime thresholds, and certified ln 2 shells.

Digit and residue certificates are exact. Numerical character and Chernoff calculations use floating point.
Floating values are printed for orientation only; no conclusion depends on them.

    python3 -B scripts/phase15_variation.py           # shells through 2^14 (about a minute)
    python3 -B scripts/phase15_variation.py --full    # true-bit shells through 2^16
"""
import argparse
import cmath
import math
import random
import sys
from fractions import Fraction
from math import comb, isqrt, lcm, prod
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from discrepancy_experiments import corrected_model, log_bits  # noqa: E402
from localized_certificate import prime  # noqa: E402
from phase14_transition_windows import certified_positions  # noqa: E402
from strided_logarithm import residue_of_rational  # noqa: E402


# ---------------------------------------------------------------------------
# Certified binary digits of ln 2
# ---------------------------------------------------------------------------

def ln2_bits(length):
    """First `length` fractional bits of ln 2, certified by an integer enclosure.

    ln 2 = sum_{k>=0} 2 / (3 (2k+1) 9^k).  With t_k = floor(2^(P+1) / (3*9^k)) one has
    floor(t_k/(2k+1)) = floor(2^(P+1)/(3 (2k+1) 9^k)).  The loop stops at the first k with
    t_k = 0; the k summed floors lose less than k, and the omitted tail is below 9/8 * 1/(2k+1) < 1.
    Hence 2^P ln 2 lies in [lower, lower + k + 1).
    """
    precision = length + 64
    while True:
        t = (1 << (precision + 1)) // 3
        lower, k = 0, 0
        while t:
            lower += t // (2 * k + 1)
            t //= 9
            k += 1
        upper = lower + k + 1  # strict upper bound for 2^P ln 2
        shift = precision - length
        if lower >> shift == (upper - 1) >> shift:
            return format(lower >> shift, f"0{length}b")
        precision += 64


def transitions(bits, start, stop):
    """Indicator list tau[t] for start <= t < stop: b_t != b_(t+1), b_n = bits[n]."""
    return [bits[t] != bits[t + 1] for t in range(start, stop)]


# ---------------------------------------------------------------------------
# 1. Exact position weighting
# ---------------------------------------------------------------------------

def overlap_weights(n, width):
    """w_j = number of starts n <= s < 2n whose width-bit word has internal gap N+j."""
    m = width - 1
    return [min(j + 1, m, n + m - 1 - j) for j in range(n + m - 1)]


def check_weight_identity(tau, n, width):
    """tau[j] is the indicator at position n+j for 0 <= j < n+width-2."""
    m = width - 1
    direct = sum(sum(tau[s:s + m]) for s in range(n))
    weighted = sum(w * h for w, h in zip(overlap_weights(n, width), tau))
    assert direct == weighted
    assert sum(overlap_weights(n, width)) == n * m
    return direct


def minimal_incidence(h, m):
    """Least possible sum of overlapping incidences of h marks among offsets 0 <= j < n."""
    return h * (h + 1) // 2 if h <= m else m * (m + 1) // 2 + (h - m) * m


def rich_lower_bound(total, n, m, theta):
    """Starts with >= theta*m changes, from total incidence and C <= m (exact rational)."""
    value = (Fraction(total, m) - theta * n) / (1 - theta)
    return max(0, math.ceil(value))


# ---------------------------------------------------------------------------
# 2. Lift model: exact Bernoulli law, Chernoff bound and multiplicative mesh
# ---------------------------------------------------------------------------

def odd_part(value):
    while value % 2 == 0:
        value //= 2
    return value


def chernoff_log(weights, p, level):
    """float: log of min over s of e^{s*level} prod_j (1-p+p e^{-s w_j}), for independent
    Bernoulli(p) marks; this bounds P(sum w_j X_j <= level).  Golden search over s."""
    def f(s):
        return s * level + math.fsum(math.log1p(p * math.expm1(-s * w)) for w in weights)
    lo, hi = 0.0, 4.0 / max(weights)
    for _ in range(80):
        a, b = lo + 0.382 * (hi - lo), lo + 0.618 * (hi - lo)
        if f(a) < f(b):
            hi = b
        else:
            lo = a
    return f((lo + hi) / 2)


def lift_bound(n, width, share=Fraction(1, 4)):
    """Bound for the fraction of grid lifts whose weighted mark sum is <= share * n * m.

    The four classes j mod 4 use disjoint bits, so marks are independent inside a class
    with P(mark) = 5/16 for every fixed upper-band cell.  If the total is at most share
    times the total weight, some class is at most share times its own weight.
    """
    m = width - 1
    weights = overlap_weights(n, width)
    log_leb = []
    for c in range(4):
        cls = weights[c::4]
        log_leb.append(chernoff_log(cls, 5 / 16, float(share) * sum(cls)))
    leb = math.fsum(math.exp(v) for v in log_leb)
    bits_used = (n + m - 2) + 4                       # last offset plus its four cell bits
    grid = odd_part(lcm(*range(1, n + 1)))
    e = bits_used - (grid.bit_length() - 1)          # 2^e >= 2^K/M
    log2_mesh = max(e, 0) + math.log2(1 + 2.0 ** (-abs(e)))   # log2(1 + 2^e)
    log2_mult = (math.log2(leb) if leb > 0 else -math.inf) + log2_mesh
    return leb, bits_used, grid.bit_length() - 1, log2_mult


def phase14_additive_bound(n):
    """Phase 14: 4((59/64)(4/3)^(1/4))^(n/4) + 2^(n+3)/M for the unweighted first shell."""
    base = (59 / 64) * (4 / 3) ** 0.25
    grid = odd_part(lcm(*range(1, n + 1)))
    return 4 * base ** (n / 4) + 2.0 ** (n + 3 - (grid.bit_length() - 1))


def verify_multiplicative_mesh(n=10, modulus=3**11, seed=15):
    """Exact check: for a union E of level-K cylinders, an M-point grid (shifted by 1/(3M))
    has fraction in E within Leb(E)(1 -+ 2^K/M)."""
    rng = random.Random(seed)
    upper_cells = [rng.randrange(16) for _ in range(n)]
    level = n + 4                                   # one-bit refinement of the minimal n+3
    def marks(cyl):
        total = 0
        for j, i in enumerate(upper_cells):
            k = (cyl >> (level - j - 4)) & 15
            total += 5 <= (i + k) % 16 <= 9
        return total
    counts = [0] * (1 << level)
    for s in range(modulus):
        counts[((3 * s + 1) << level) // (3 * modulus)] += 1
    results = []
    for threshold in range(1, n):
        event = [marks(c) < threshold for c in range(1 << level)]
        leb = Fraction(sum(event), 1 << level)
        frac = Fraction(sum(c for c, e in zip(counts, event) if e), modulus)
        mesh = Fraction(1 << level, modulus)
        assert leb * (1 - mesh) <= frac <= leb * (1 + mesh)
        results.append((threshold, leb, frac))
    return level, modulus, results


# ---------------------------------------------------------------------------
# 3. Rigidity of eventual upper-band data
# ---------------------------------------------------------------------------

def upper_band_signature(value, u):
    return tuple(residue_of_rational(p * value, p) for p in range(u + 1, 2 * u + 1) if prime(p))


def rigidity_check(u0=10, span=14):
    """y'_u = y_u + 2^(u-u0) q keeps denominators, displacements and every upper-band
    residue at all tested u >= u0 iff v_p(q) >= 0 for p > u0 (and q in L_(2u0)^(-1) Z)."""
    models = {u: corrected_model(u, u) for u in range(u0, u0 + span + 1)}
    def test(q):
        failures = []
        for u, y in models.items():
            z = y + 2**(u - u0) * q
            if lcm(*range(1, 2 * u + 1)) % z.denominator:
                failures.append((u, "denominator"))
            if upper_band_signature(z, u) != upper_band_signature(y, u):
                failures.append((u, "upper band"))
            if u > u0:
                assert z - 2 * (models[u - 1] + 2**(u - 1 - u0) * q) == y - 2 * models[u - 1]
        return failures
    smooth = odd_part(lcm(*range(1, u0 + 1)))
    good = [Fraction(1, smooth), Fraction(-7, 3 * 2**4), Fraction(5, 9 * 7)]
    bad = [Fraction(1, 13), Fraction(1, 23), Fraction(2, 11 * 3)]
    for q in good:
        assert test(q) == [], q
    out = []
    for q in bad:
        failures = test(q)
        assert failures
        out.append((q, failures[0]))
    return smooth, out


def shift_noninvariance(length=4096):
    """Exact: K = sum 2^(-2^j) has O(log) transitions; K + 1/3 has about one per position."""
    precision = length + 64
    k_int = sum(1 << (precision - (1 << j)) for j in range(precision.bit_length()) if (1 << j) <= precision)
    third = (1 << precision) // 3
    out = []
    for name, value in (("K", k_int), ("K+1/3", k_int + third)):
        # Both enclosures have width < 2 units in the last of `precision` bits.
        lo, hi = value, value + 2
        shift = precision - length
        assert (lo % (1 << precision)) >> shift == ((hi - 1) % (1 << precision)) >> shift
        bits = format((lo % (1 << precision)) >> shift, f"0{length}b")
        out.append((name, sum(transitions(bits, 0, length - 1))))
    return out


# ---------------------------------------------------------------------------
# 4. Moving primes: uniform thresholds and classical incomplete sums
# ---------------------------------------------------------------------------

def band_primes(n):
    return [p for p in range(n + 1, 2 * n + 1) if prime(p)]


def uniform_failure_threshold(n, width):
    """Least r such that the product Q of the r smallest band primes exceeds 2^(width+1).
    Then the unit numerator 1 gives {2^j/Q} < 1/4 for all j < width, so no transition."""
    primes = band_primes(n)
    q, r = 1, 0
    while q <= 1 << (width + 1):
        q *= primes[r]
        r += 1
    for j in range(width):
        assert 4 * ((1 << j) % q) < q          # phase in [0, 1/4): no transition
    return r, len(primes)


def multiplicative_order(g, p):
    t, x = 1, g % p
    while x != 1:
        x = x * g % p
        t += 1
    return t


def korobov_check(n, lengths):
    """float: max over units a of |sum_{j<T} e_p(a 2^j)| against sqrt(p)(floor(T/t) + 2 + log t)."""
    rows = []
    for p in band_primes(n)[:12]:
        t = multiplicative_order(2, p)
        table = [cmath.exp(2j * math.pi * k / p) for k in range(p)]
        powers = [pow(2, j, p) for j in range(max(lengths))]
        for width in lengths:
            worst = 0.0
            for a in range(1, p):
                s = sum(table[a * x % p] for x in powers[:width])
                worst = max(worst, abs(s))
            # floor(T/t) complete periods (each <= sqrt p) plus one incomplete sum.
            bound = math.sqrt(p) * (width // t + 2 + math.log(t))
            assert worst <= bound + 1e-9
            rows.append((p, t, width, worst, bound))
    return rows


def joint_sample(n, width, pairs=3, samples=4000, seed=15):
    """float: sampled sup of |mean_{j<T} e_Q(a 2^j)| for Q a product of two band primes."""
    rng = random.Random(seed)
    primes = band_primes(n)
    rows = []
    for idx in range(pairs):
        p1, p2 = primes[2 * idx], primes[2 * idx + 1]
        q = p1 * p2
        worst = 0.0
        for _ in range(samples):
            a = rng.randrange(1, q)
            if a % p1 == 0 or a % p2 == 0:
                continue
            x, s = a, 0j
            for _ in range(width):
                s += cmath.exp(2j * math.pi * x / q)
                x = 2 * x % q
            worst = max(worst, abs(s) / width)
        rows.append((p1, p2, worst))
    return rows


# ---------------------------------------------------------------------------
# 5. Certified ln 2 shells
# ---------------------------------------------------------------------------

def escape_float(bits, n0, n1):
    """float: sum of 1 - cos(2 pi {2^n ln 2}) using 53 certified bits per position."""
    total = []
    for n in range(n0, n1):
        t = int(bits[n:n + 53], 2) / 2.0**53
        total.append(1 - math.cos(2 * math.pi * t))
    return math.fsum(total)


def true_shell(bits, n):
    width_small = isqrt(n)
    tau = transitions(bits, n, 3 * n - 2)            # positions n .. 3n-3
    count = sum(tau[:n])
    esc = escape_float(bits, n, 2 * n)
    # Lean per-position inequality: tau_n <= F_n <= 4 tau_n + F_(n+1) - F_n, so on a shell
    # count <= escape <= 4 count + 2.
    assert count - 1e-6 <= esc <= 4 * count + 2 + 1e-6
    sums = {}
    for width in (width_small, n):
        sums[width] = check_weight_identity(tau, n, width)
        words = [sum(tau[s:s + width - 1]) for s in range(n)]
        sums[width] = (sums[width], min(words), sum(4 * c >= width - 1 for c in words))
    return count, esc, sums


def crt_correlation(n):
    """float: mean of e(2^j a/A) e(2^j b/B) over the first shell, versus the true orbit.
    Cell-free version of the Phase 14 decomposition; the product is e(2^j y_N)."""
    modulus = lcm(*range(1, 2 * n + 1))
    upper = prod(band_primes(n))
    lower = modulus // upper
    from phase14_transition_windows import diagonal_residue
    v = diagonal_residue(n, modulus)
    a = v * pow(lower, -1, upper) % upper
    b = v * pow(upper, -1, lower) % lower
    su = sl = sp = 0j
    for _ in range(n):
        eu = cmath.exp(2j * math.pi * ((a << 64) // upper) / 2.0**64)
        el = cmath.exp(2j * math.pi * ((b << 64) // lower) / 2.0**64)
        su += eu
        sl += el
        sp += eu * el
        a, b = 2 * a % upper, 2 * b % lower
    return su / n, sl / n, sp / n


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true", help="true-bit shells through 2^16")
    args = parser.parse_args()
    top_true = 16 if args.full else 14

    assert ln2_bits(3000) == log_bits(3000)
    bits = ln2_bits(3 * 2**top_true)
    print("Certified ln 2 bits:", len(bits), "(atanh enclosure, agrees with Phase 14 for 3000 bits)")

    print("\n## True shells: transitions, escape (float), overlapping sums (exact)")
    print("N | transitions | escape/N | Re W | T=isqrt N: sum, min, rich(>=m/4) | T=N: sum, min, rich")
    for k in range(8, top_true + 1):
        n = 2**k
        count, esc, sums = true_shell(bits, n)
        w = isqrt(n)
        print(n, count, f"{esc / n:.5f}", f"{1 - esc / n:.5f}", sums[w], sums[n], sep=" | ")

    print("\n## Certified marks: Phase 14 quadratic transfer versus the weighted linear transfer")
    print("N | H marks in [0,N) | m | weighted certified incidence | worst-case minimum |"
          " Phase14 N/128 | new >= m/8 | new >= m/4")
    for k in range(8, 15):
        n = 2**k
        marks = certified_positions(n)
        width = isqrt(n)
        m = width - 1
        h = sum(marks[:n])
        weighted = check_weight_identity(marks, n, width)
        least = minimal_incidence(h, m)
        assert weighted >= least
        print(n, h, m, weighted, least, n // 128,
              rich_lower_bound(least, n, m, Fraction(1, 8)),
              rich_lower_bound(least, n, m, Fraction(1, 4)), sep=" | ")

    print("\n## Lift model: weighted quarter-share failure, multiplicative mesh (float logs)")
    print("N | T | Lebesgue bound | bits K | log2 M | log2 grid bound | Phase14 additive (T=N first shell)")
    for k in range(8, 15):
        n = 2**k
        for width in (isqrt(n), n):
            leb, used, logm, log2_grid = lift_bound(n, width)
            extra = f"{phase14_additive_bound(n):.3e}" if width == n else ""
            print(n, width, f"{leb:.3e}", used, logm, f"{log2_grid:.1f}", extra, sep=" | ")

    level, modulus, rows = verify_multiplicative_mesh()
    worst = max(abs(f / l - 1) for _, l, f in rows if l)
    print(f"\nMultiplicative mesh verified exactly: K={level}, M={modulus}, 2^K/M="
          f"{(1 << level) / modulus:.4f}, worst relative deviation {float(worst):.4f}")

    print("\n## Rigidity of eventual upper-band data")
    smooth, failures = rigidity_check()
    print(f"Shifts with denominator dividing {smooth} times 16 preserve the tests at anchor 10.")
    for q, failure in failures:
        print(f"  q = {q}: first failure at u={failure[0]} ({failure[1]})")
    for name, count in shift_noninvariance():
        print(f"  transitions in first 4095 gaps of {name}: {count}")
    # ln 2 + 1/3 = 1.026...; its fractional part has enclosure [lo, lo + 2) at 4200 bits.
    lo = int(bits[:4200], 2) + (1 << 4200) // 3 - (1 << 4200)
    assert 0 <= lo and (lo + 1) >> 104 == lo >> 104
    shifted_bits = format(lo >> 104, "04096b")
    print("  transitions in first 4095 gaps of ln 2 + 1/3:", sum(transitions(shifted_bits, 0, 4095)))

    print("\n## Moving primes")
    print("N | T | least r breaking uniformity | primes in (N,2N] | ratio")
    for k in (8, 10, 12, 14):
        n = 2**k
        for width in (isqrt(n), n // 4):
            r, total = uniform_failure_threshold(n, width)
            print(n, width, r, total, f"{r / total:.3f}", sep=" | ")
    print("Korobov completion check (float): p, ord, T, max|sum|, sqrt(p)(T//t+2+log t)")
    for row in korobov_check(256, (16, 256)):
        print("  ", row[0], row[1], row[2], f"{row[3]:.2f}", f"{row[4]:.2f}")
    print("Sampled two-prime means at N=256, T=256 (float):")
    for p1, p2, worst in joint_sample(256, 256):
        print(f"   Q={p1}*{p2}: sampled max |mean| = {worst:.4f}")

    print("\n## CRT correlation equals the true Weyl mean (float)")
    for k in (8, 10, 12):
        n = 2**k
        mu, ml, mp = crt_correlation(n)
        exact = escape_float(bits, n, 2 * n)
        print(n, f"|upper mean|={abs(mu):.4f}", f"|complement mean|={abs(ml):.4f}",
              f"Re product mean={mp.real:.5f}", f"1-escape/N={1 - exact / n:.5f}")

    print("\n## Entropy budget: N | T | K | floor log2 M | bound on log2(1 + 2^K/M) bits")
    for k in range(8, 15):
        n = 2**k
        width = isqrt(n)
        used = n + width + 1
        logm = odd_part(lcm(*range(1, n + 1))).bit_length() - 1
        e = used - logm
        assert e < 0
        print(n, width, used, logm, f"< 2^({e + 1})")   # log2(1 + 2^e) <= 2^e / ln 2 < 2^(e+1)


if __name__ == "__main__":
    main()
