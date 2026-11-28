"""Exact checks for dense character coefficients and quadratic-order descent."""

from collections import Counter
from fractions import Fraction
from math import gcd, isqrt, prod


def factor(n):
    factors = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        factors[n] = 1
    return factors


def character_table(modulus, generator, order):
    exponents = {}
    a = 1
    while a not in exponents:
        exponents[a] = len(exponents) % order
        a = a * generator % modulus
    assert len(exponents) == sum(gcd(n, modulus) == 1 for n in range(modulus))
    return exponents


def reduce_cyclotomic(v):
    # Prime order h: 1 + z + ... + z^(h-1) = 0.
    return tuple(a - v[-1] for a in v)


def multiply(x, y):
    h = len(x)
    out = [0] * h
    for i, a in enumerate(x):
        for j, b in enumerate(y):
            out[(i + j) % h] += a * b
    return reduce_cyclotomic(out)


def odd_part(n):
    return n // (n & -n)


def check_quintic_trace(value, phase):
    # The conjugate embeddings are paired by u^2 = chi(n stripped).
    h = 5
    root = (0, 1, 0, 0, 0)
    u = tuple(int(i == (3*phase) % h) for i in range(h))
    u_bar = [u[-i % h] for i in range(h)]
    real = multiply(value, u_bar)
    assert real == reduce_cyclotomic([real[-i % h] for i in range(h)])
    for beta in (root, (1, 0, 0, 0, 0), (0, 1, 0, 0, -1)):
        beta_u = multiply(beta, u)
        multiplier = reduce_cyclotomic([beta_u[i] + beta_u[-i % h] for i in range(h)])
        trace_term = multiply(beta, value)
        real_term = multiply(multiplier, real)
        # For a coefficient vector v, Tr(v) = h*v[0] - sum(v).
        assert h*real_term[0] - sum(real_term) == 2*(h*trace_term[0] - sum(trace_term))
        if beta == (0, 1, 0, 0, -1):
            assert bool(any(multiplier)) == (phase != 0)


def check_character(modulus, generator, h, limit):
    exponents = character_table(modulus, generator, h)
    totals = [[0] * h for _ in range(limit + 1)]
    for d in range(1, limit + 1):
        t = exponents.get(d % modulus)
        if t is not None:
            for n in range(d, limit + 1, d):
                totals[n][t] += 1
    one = (1,) + (0,) * (h - 1)
    norm_sum = [0] * h
    unit_product = one
    for j in range(h):
        v = list(one)
        v[j] += 1
        unit_product = multiply(unit_product, v)
        square = multiply(v, [v[-i % h] for i in range(h)])
        norm_sum = [a + b for a, b in zip(norm_sum, square)]
    assert unit_product == (2,) + (0,) * (h - 1)
    assert reduce_cyclotomic(norm_sum) == (2 * h,) + (0,) * (h - 1)
    plus, minus = [0], [0]
    for n in range(1, limit + 1):
        local_product = one
        common = 1
        permitted = True
        stripped = n
        for p, e in factor(n).items():
            t = exponents.get(p % modulus)
            if t is None:
                stripped //= p**e
                continue
            v = [0] * h
            for j in range(e + 1):
                v[j * t % h] += 1
            local_product = multiply(local_product, v)
            if t == 0:
                common *= e + 1
            elif (e + 1) % h == 0:
                permitted = False
        assert local_product == reduce_cyclotomic(totals[n])
        assert bool(any(local_product)) == permitted
        assert all(value % common == 0 for value in local_product)
        if h == 5:
            check_quintic_trace(local_product, exponents[stripped % modulus])
        if h == 3:
            x, y, _ = local_product
            plus.append(2 * x - y)
            minus.append(y)
            assert bool(plus[-1]) == permitted
            assert bool(y) == (permitted and exponents[stripped % modulus] != 0)
            assert x*x - x*y + y*y == permitted * common**2
    return plus, minus


def cubic_euler_bounds(modulus, generator, cutoff):
    """Outward rational enclosures for support density and odd-part mean."""
    exponents = character_table(modulus, generator, 3)
    scale = 10**12
    lo = hi = odd_factor_upper = scale
    for p in range(2, cutoff + 1):
        if factor(p) != {p: 1}:
            continue
        t = exponents.get(p % modulus)
        if t in (1, 2):
            den = p*p + p + 1
            lo = lo * (den-1) // den
            hi = (hi * (den-1) + den-1) // den
        elif t == 0:
            den = p*p*(p-1)
            odd_factor_upper = (odd_factor_upper * (den+2*p-1) + den-1) // den
    density_lower = Fraction(lo, scale) * (1 - Fraction(1, cutoff))
    density_upper = Fraction(hi, scale)
    odd_upper = density_upper * Fraction(odd_factor_upper, scale) / (1 - Fraction(3, cutoff))
    return density_lower, density_upper, odd_upper


def check_dense():
    plus, minus = check_character(7, 3, 3, 8192)
    for modulus, generator, order in [(9, 2, 3), (13, 2, 3), (11, 2, 5)]:
        check_character(modulus, generator, order, 2048)
    plus_phase = [2, 1, -1, -2, -1, 1]
    minus_phase = [0, 1, 1, 0, -1, -1]
    for phase, expected in [(plus_phase, (Fraction(4, 3), 2)),
                            (minus_phase, (Fraction(2, 3), Fraction(2, 3)))]:
        assert tuple(Fraction(sum(abs(x)**r for x in phase), 6) for r in (1, 2)) == expected
    # At a multiple of 7 the OTHER entry of a consecutive pair already fails.
    active_units = {2, 3, 4, 5}
    assert {r for r in range(7) if r in active_units and (r+1) % 7 in active_units} == {2, 3, 4}
    assert 1 not in active_units and 6 not in active_units
    for p in (2, 3, 5):
        # Truncate forbidden valuations below E. Consecutive forbidden events are disjoint.
        E = 6
        period = p**E
        bad = {a for a in range(1, period) if factor(a).get(p, 0) % 3 == 2}
        one_bad = sum(Fraction(p-1, p**(e+1)) for e in range(2, E, 3))
        assert Fraction(len(bad), period) == one_bad
        assert Fraction(sum(a not in bad and (a+1) % period not in bad for a in range(period)),
                        period) == 1 - 2 * one_bad
    cutoff = 4096
    for modulus, generator, bound in [(7, 3, Fraction(4, 5)), (9, 2, Fraction(21, 25)),
                                      (13, 2, Fraction(21, 25))]:
        density_lower, density_upper, odd_upper = cubic_euler_bounds(modulus, generator, cutoff)
        if modulus == 7:
            assert Fraction(3, 4) < density_lower <= density_upper < Fraction(751, 1000)
        assert odd_upper < bound
        for k, odd_mean in [(4, bound), (3, Fraction(2, 3)*bound)]:
            assert odd_mean/k < Fraction(1, 4) - Fraction(1, 2*2**k)
    for k in range(1, 11):
        b = 2**k
        assert sum(2**r for r in range(k)) == b-1
        assert Fraction(sum(min(j, b-1-j) for j in range(b)), b*b) == (
            Fraction(1, 4) - Fraction(1, 2*b))
    for p in (2, 5, 13, 29):
        x = Fraction(1, p)
        # Exact upper bound on the full series: odd(e+1) <= e+1 for e >= 2, and
        # (1-x) * sum_{e>=2} (e+1) x^e = (1-x) * (x^2*(3 - 2*x)/(1-x)^2) = x^2*(3 - 2*x)/(1-x).
        # Meanwhile (1-x)*(1 + x) + x^2*(3 - 2*x)/(1-x) = 1 + x^2*(2 - x)/(1-x) = 1 + (2p-1)/(p^2(p-1)).
        closed_upper = (1 - x) * (1 + x) + x * x * (3 - 2 * x) / (1 - x)
        expected_upper = 1 + Fraction(2 * p - 1, p * p * (p - 1))
        assert closed_upper == expected_upper <= 1 + Fraction(3, p * p)
        # Consistency check against the 20-term exact partial sum plus exact tail upper bound.
        partial = (1 - x) * sum(odd_part(e + 1) * x ** e for e in range(20))
        tail_upper = (1 - x) * (21 * x ** 20 / (1 - x) + x ** 21 / (1 - x) ** 2)
        assert partial + tail_upper <= expected_upper
    for seq in (plus, minus):
        # Move whole powers of b to the left in a finite signed polynomial.
        for k in (1, 2, 3, 4, 6):
            b = 2**k
            last = 80
            arrivals = Counter()
            absolute = Counter()
            for n, value in enumerate(seq[1:last+1], 1):
                if value:
                    odd = odd_part(abs(value))
                    v2 = (abs(value)//odd).bit_length()-1
                    v, r = divmod(v2, k)
                    reduced = value // b**v
                    assert abs(reduced) == odd * 2**r
                    arrivals[n-v] += reduced
                    absolute[n-v] += abs(reduced)
            raw = sum(value*b**(last-n) for n, value in enumerate(seq[1:last+1], 1))
            assert raw == sum(value*b**(last-t) for t, value in arrivals.items())
            # Orbit distance <= weighted absolute future arrivals, even on collisions.
            for j in range(last):
                denom = b**(last-j)
                rem = raw % denom
                envelope = sum(value*b**(last-t) for t, value in absolute.items() if t > j)
                assert min(rem, denom-rem) <= envelope
        # Threshold-displacement regressions (Phase 24 Audit 1): exercise actual
        # left-shifts at k=4 (plus, base 16) and signed collision cancellation at
        # k=3 (minus, base 8) on short shifted windows mod 7.
        def _cubic_proj_at(n_val, is_plus):
            loc = (1, 0, 0)
            for p, e in factor(n_val).items():
                t = exponents.get(p % modulus)
                if t is None:
                    continue
                vec = [0, 0, 0]
                for jj in range(e + 1):
                    vec[jj * t % 3] += 1
                loc = multiply(loc, vec)
            xx, yy, _ = loc
            return (2 * xx - yy) if is_plus else yy

        if modulus == 7:
            for is_plus, k_thr, win_start, win_end in (
                (True, 4, 15450, 15465),
                (False, 3, 46365, 46378),
            ):
                b_thr = 2**k_thr
                win_vals = {n_val: _cubic_proj_at(n_val, is_plus)
                            for n_val in range(win_start, win_end + 1)}
                if is_plus:
                    assert win_vals[15457] == 16
                else:
                    assert win_vals[46370] == -1 and win_vals[46371] == 8
                arr_w = Counter()
                abs_w = Counter()
                moved = False
                for n_val, val in win_vals.items():
                    if val:
                        od = odd_part(abs(val))
                        v2 = (abs(val) // od).bit_length() - 1
                        vv, rr = divmod(v2, k_thr)
                        if vv > 0:
                            moved = True
                        red = val // b_thr**vv
                        assert abs(red) == od * 2**rr
                        arr_w[n_val - vv] += red
                        abs_w[n_val - vv] += abs(red)
                assert moved
                if not is_plus:
                    # Exact signed cancellation at 46370 (-1 + 8/8 = 0).
                    assert arr_w[46370] == 0 and abs_w[46370] >= 2
                raw_w = sum(val * b_thr**(win_end - n_val) for n_val, val in win_vals.items())
                assert raw_w == sum(val * b_thr**(win_end - t_val) for t_val, val in arr_w.items())
                for j_val in range(win_start, win_end):
                    den_w = b_thr**(win_end - j_val)
                    rem_w = raw_w % den_w
                    env_w = sum(val * b_thr**(win_end - t_val) for t_val, val in abs_w.items() if t_val > j_val)
                    assert min(rem_w, den_w - rem_w) <= env_w
        for b in (2, 3, 10):
            # An exact finite signed tail checks orientation, signs and the scale b^d.
            tail = [Fraction(0)] * 81
            for n in reversed(range(80)):
                tail[n] = (seq[n+1] + tail[n+1]) / b
            for n in range(64):
                block = 0
                for d in range(1, 9):
                    block = b * block + seq[n+d]
                    assert b**d * tail[n] - tail[n+d] == block
    moments = [(sum(a != 0 for a in row[1:]), sum(map(abs, row)), sum(a*a for a in row))
               for row in (plus, minus)]
    assert moments == [(6154, 12176, 34416), (4081, 5662, 9324)]
    return moments


def reduced_forms(discriminant):
    forms = []
    for a in range(1, isqrt(-discriminant // 3) + 1):
        for b in range(-a, a + 1):
            c, rem = divmod(b*b - discriminant, 4*a)
            if rem or c < a or gcd(gcd(a, b), c) != 1:
                continue
            if b < 0 and (abs(b) == a or a == c):
                continue
            forms.append((a, b, c))
    return forms


def counts(form, limit):
    a, b, c = form
    disc_abs = 4*a*c - b*b
    out = [0] * (limit + 1)
    bound_y = isqrt(4*a*limit // disc_abs)
    for y in range(-bound_y, bound_y + 1):
        radius = isqrt(4*a*limit - disc_abs*y*y)
        for x in range(-((radius+b*y) // (2*a)), (radius-b*y) // (2*a) + 1):
            out[a*x*x + b*x*y + c*y*y] += 1
    return out


def kronecker_prime(D, p):
    if D % p == 0:
        return 0
    if p == 2:
        return 1 if D % 8 == 1 else -1
    return 1 if pow(D % p, (p-1)//2, p) == 1 else -1


def principal_form(D, f):
    # Norm on Z + f O_K; this basis need not be reduced.
    b = D % 2
    return (1, f*b, f*f*((b*b-D)//4))


def units(D):
    return {-3: 6, -4: 4}.get(D, 2)


def class_to_lower(form, p):
    # A unimodular basis with leading coefficient prime to p. Then complete
    # the square by a shear to make the middle and last coefficients divisible
    # by p and p^2 respectively. The overorder lattice divides this vector by p.
    a, b, c = form
    if a % p == 0:
        assert c % p  # p^2 divides the discriminant, and the form is primitive.
        a, b, c = c, -b, a
    for j in range(p):
        middle, last = 2*a*j+b, a*j*j+b*j+c
        if middle % p == last % (p*p) == 0:
            return a, middle//p, last//(p*p)
    raise AssertionError((form, p))


def check_forms():
    # D_K, conductor, C_Q / C_K, coefficient of P_g in the dyadic logarithmic term.
    examples = [
        (-3, 2, Fraction(1), 0), (-4, 2, Fraction(3, 4), 0),
        (-3, 3, Fraction(7, 9), 0), (-7, 2, Fraction(3, 4), 0),
        (-8, 2, Fraction(1, 2), 0), (-4, 3, Fraction(5, 9), 0),
        (-11, 2, Fraction(1), Fraction(1, 2)), (-4, 4, Fraction(7, 16), 0),
        (-3, 5, Fraction(13, 25), 0), (-23, 2, Fraction(3, 4), Fraction(20, 27)),
        (-3, 6, Fraction(7, 9), Fraction(3, 7)),
    ]
    class_numbers = {-12: 1, -16: 1, -27: 1, -28: 1, -32: 2, -36: 2, -44: 3,
                     -64: 2, -75: 2, -92: 3, -108: 3}
    limit = 4096
    for D, f, expected_mass, expected_dyadic in examples:
        mass = width = Fraction(0)
        weights = {}
        for d in range(1, f+1):
            if f % d:
                continue
            g = f // d
            forms = reduced_forms(D*g*g)
            h = len(forms)
            assert h in (1, 2, 3)
            weight = Fraction(1, d*d*gcd(h, 2))
            for p in factor(g):
                power = 2 if kronecker_prime(D, p) == -1 else 1
                weight *= 1 - Fraction(1, p**power)
            mass += weight
            weights[g] = weight
            if h == 3:
                survival_ratio = Fraction(7, 6) if (D, g) == (-23, 2) else 1
                width += weight * Fraction(2, 3) * survival_ratio
        assert mass == expected_mass and width / mass == expected_dyadic
        disc = D*f*f
        forms = reduced_forms(disc)
        assert len(forms) == class_numbers[disc]
        if disc == -108:
            assert weights == {6: Fraction(1, 2), 3: Fraction(1, 6),
                               2: Fraction(1, 12), 1: Fraction(1, 36)}
            assert weights[6]/mass == Fraction(9, 14)
        if disc == -92:
            assert weights == {2: Fraction(1, 2), 1: Fraction(1, 4)}
        total_reps = Counter()
        for form in forms:
            reps = counts(form, limit)
            for n, count in enumerate(reps):
                total_reps[n] += count
            for p, a in factor(f).items():
                lower_form = class_to_lower(form, p)
                A, B, C = lower_form
                assert B*B - 4*A*C == disc // (p*p)
                lower = counts(lower_form, limit // (p*p))
                assert all(reps[n] == 0 for n in range(p, limit+1, p) if n % (p*p))
                assert reps[::p*p] == lower
            # Direct counts for kQ test the dilation through the theta coefficients.
            for k in (2, 3):
                dilated = counts(tuple(k*v for v in form), limit)
                assert dilated == [reps[n//k] if n % k == 0 else 0 for n in range(limit+1)]
        for p, a in factor(f).items():
            chi = kronecker_prime(D, p)
            for e in range(limit.bit_length()):
                if p**e > limit:
                    break
                if e < 2*a:
                    ideals = p**(e//2) if e % 2 == 0 else 0
                else:
                    ideals = p**(a-1)*(p-chi)*sum(chi**j for j in range(e-2*a+1))
                assert total_reps[p**e] == units(disc)*ideals
        # Simultaneous descent for the principal form (including 2 and 3 at -108).
        reps = counts(principal_form(D, f), limit)
        lower = {g: counts(principal_form(D, g), limit) for g in range(1, f+1) if f % g == 0}
        for n in range(1, limit+1):
            fs = factor(n)
            d = prod(p**min(a, fs.get(p, 0)//2) for p, a in factor(f).items())
            m, g = n//(d*d), f//d
            assert reps[n] == (lower[g][m] if gcd(m, g) == 1 else 0)
    assert counts(principal_form(-23, 1), 2)[2] == 0
    assert counts((2, 1, 3), 2)[2] > 0
    assert kronecker_prime(-23, 2) == 1
    assert 1-Fraction(1, 2**2+2+1) == Fraction(6, 7)
    return len(examples)


if __name__ == "__main__":
    moments = check_dense()
    print("Cubic mod 7 at 8192 (support, absolute mass, square mass):", moments)
    print("Certified cubic dyadic thresholds for moduli 7, 9, 13: plus k >= 4, minus k >= 3")
    print("Quadratic discriminants checked through 4096:", check_forms())
