"""Exact finite checks for Phase 25 Track E. Run with python -B."""

from collections import Counter
from fractions import Fraction as F
from math import gcd, lcm, prod


def norm(x):
    r = x % 1
    return min(r, 1 - r)


def floor(x):
    return x.numerator // x.denominator


def ceil(x):
    return -floor(-x)


def ord_mod(b, q):
    assert gcd(b, q) == 1
    if q == 1:
        return 1
    r, order = b % q, 1
    while r != 1:
        r = r * b % q
        order += 1
    return order


def orbit(z, b, count):
    a, q = z.as_integer_ratio()
    r = a % q
    for _ in range(count):
        yield F(r, q)
        r = r * b % q


def binary_cycle(z):
    den = z.denominator
    power = den & -den
    pure = z * power
    return list(orbit(pure, 2, ord_mod(2, pure.denominator)))


def law(points):
    counts = Counter(points)
    return {x: F(n, len(points)) for x, n in counts.items()}


def discrepancy(masses):
    """Range of the signed distribution function, using both sides of each atom."""
    before, high, low = F(0), F(0), F(0)
    for x, mass in sorted(masses.items()):
        low = min(low, before - x)
        before += mass
        high = max(high, before - x)
    assert before == 1
    return high - low


def pad(v, p, q):
    return v * (1 - F(1, 2**p)) / (1 - F(1, 2**q))


def check_padding():
    total = 0
    for v in (F(5, 7), F(5, 56), F(1, 3), F(9, 62)):
        u = 1 / v
        old = binary_cycle(v)
        pu = len(binary_cycle(u))
        a = max((z.denominator & -z.denominator).bit_length() - 1 for z in (u, v))
        for e in (1, 2, 3, 4, 5):
            if gcd(e, len(old)) != 1:
                continue
            p = next(n for n in range(240, 500) if n % len(old) == 0 and (n-1) % e == 0)
            d = e * pu
            assert d < p
            q = p + d
            new = pad(v, p, q)
            w = u * (1 - F(1, 2**d))
            assert 1 / new - u == w / (2**p - 1)
            assert (2**(a + d) * w).denominator == 1
            assert (2**a * (2**q - 1) * new).denominator == 1
            assert gcd(q, e) == 1
            new_cycle = binary_cycle(new)
            actual = law(new_cycle)
            for offset in range(e):
                lane = list(orbit(new * 2**(a+offset), 2**e, q))
                assert law(lane) == actual
            ideal = {x: mass * F(p, q) for x, mass in law(old).items()}
            ideal[0] = ideal.get(0, F(0)) + F(d, q)
            # Uniform t modulo q, starting at time q, is past the preperiod.
            # p contains exactly an integer number of old cycles after time a;
            # reference 2^t v may have an initial preperiod, so use a phase
            # agreeing with it for t >= a.
            phase = ((a + len(old) - 1) // len(old)) * len(old)
            odd_den = (2**a * v).denominator
            seed = F((2**a * v).numerator * pow(2, -a, odd_den), odd_den)
            ref = list(orbit(seed * 2**phase, 2, p)) + [F(0)] * d
            assert law(ref) == ideal
            delta = F(1, 2**6)
            shifted = list(orbit(2**q * new, 2, q))
            bad = sum(norm(x-y) > delta for x, y in zip(shifted, ref))
            assert bad <= 2*a + 20
            assert abs(discrepancy(actual) - discrepancy(ideal)) <= 2*delta + F(bad, q)
            total += 1
    # One complete two-operation stage, with an input carrying a preperiod.
    v = pad(F(5, 56), 9, 13)
    u = 1/v
    pv, pu = len(binary_cycle(v)), len(binary_cycle(u))
    ell = lcm(pv, pu)
    a = max((z.denominator & -z.denominator).bit_length() - 1 for z in (u, v))
    assert ell > a
    vplus = v * (1 + F(1, 2**ell))
    uplus = 1/vplus
    assert law(binary_cycle(vplus)) == law(binary_cycle(v))
    assert (2**(2*ell)-1) % uplus.denominator == 0
    for r in range(ell):
        err = 2**r * u / (2**ell+1)
        assert 2**r * uplus == 2**r * u - err
        assert 2**(ell+r)*uplus == 2**r * (2**ell-1)*u + err
        if r >= a:
            assert (2**(ell+r)*uplus - err).denominator == 1
    old_mean = sum(map(norm, binary_cycle(u)), F(0)) / pu
    new_mean = sum(map(norm, orbit(uplus, 2, 2*ell)), F(0)) / (2*ell)
    assert new_mean <= old_mean/2 + (2*u + a + pu)/(2*ell)
    print(f"E1: {total} rational pads; composed contraction has {2*ell} verified band positions.")


def eventual(z, b):
    """Cycle phase that agrees with b^n z once the preperiod is over."""
    den = z.denominator
    a = 0
    while (g := gcd(den, b)) > 1:
        den //= g
        a += 1
    t = b**a*z
    phase = F(t.numerator * pow(b, -a, t.denominator), t.denominator) % 1
    return a, phase, ord_mod(b, phase.denominator)


def cut_and_fold(cut, b, m, d):
    folded = 1/cut
    ac, cphase, pc = eventual(cut, b)
    af, fphase, pf = eventual(folded, b)
    assert m % pc == d % pf == 0 and gcd(m, d) == 1
    q = m+d
    cp = cut * (1-F(1, b**m))/(1-F(1, b**q))
    fp = 1/cp
    w = folded * (1-F(1, b**d))
    assert (w*b**(af+d)).denominator == 1 and fp-folded == w/(b**m-1)
    assert ((b**q-1)*b**ac*cp).denominator == 1
    # Use the two proven period multiples rather than search a large order.
    assert ((b**(m*pf)-1)*b**(af+d)*fp).denominator == 1
    assert gcd(q, m*pf) == 1
    cpoints = list(orbit(cphase, b, pc))
    fpoints = list(orbit(fphase, b, pf))
    cut_ref = [cpoints[i % pc] for i in range(m)] + [F(0)]*d
    cut_actual = list(orbit(cp*b**q, b, q))
    delta = F(1, b**4)
    cut_bad = sum(norm(x-y) > delta for x,y in zip(cut_ref,cut_actual))
    assert cut_bad <= 2*ac+14
    assert abs(discrepancy(law(cut_ref))-discrepancy(law(cut_actual))) <= 2*delta+F(cut_bad,q)

    pair_counts = Counter()
    ref = []
    for i in range(pf, 2*pf):
        for s in range(m):
            phase = fpoints[(i*m+s) % pf]
            if s < d:
                other = fpoints[s % pf]
                pair_counts[phase,other] += 1
                phase = (phase+other) % 1
            ref.append(phase)
    assert len(pair_counts) == pf**2 and set(pair_counts.values()) == {d//pf}
    single = law(fpoints)
    conv = law([(x+y) % 1 for x in fpoints for y in fpoints])
    expected = {x: F(m-d,m)*single.get(x,0)+F(d,m)*conv.get(x,0) for x in single.keys() | conv.keys()}
    assert law(ref) == expected
    actual = list(orbit(fp*b**(m*pf), b, m*pf))
    bad = sum(norm(x-y) > delta for x,y in zip(ref,actual))
    assert bad <= pf*(2*af+14)
    assert abs(discrepancy(expected)-discrepancy(law(actual))) <= 2*delta+F(bad,m*pf)
    return cp, fp


def check_convolution():
    for b in (2, 3, 4, 5, 10):
        folded = F(b**4-1, (b**3-1)*b**2)
        cut_and_fold(1/folded, b, 596, 39)
        # A complete two-step round: first cut y, then cut x.
        y, x = cut_and_fold(F(1), b, 13, 2)
        x_next, y_next = cut_and_fold(x, b, 221, 15)
        assert x*y == x_next*y_next == 1
    for z in (F(-1), F(-2,7), F(0), F(9,10), F(99999,100000)):
        for cut_mass, rho in ((F(1,17), F(1,9)), (F(3,100), F(1,12))):
            za = (1-cut_mass)*z+cut_mass
            result = (1-rho)*za+rho*za**2
            assert 1-result == (1-cut_mass)*(1-z)*(1+rho*za)
    print("E1.2: 15 coprime period updates in bases 2, 3, 4, 5, 10; exact pair multiplicities and couplings.")


def valuation(n, p):
    assert n > 0
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def check_grids():
    cases = 0
    for b, p, exps in ((3, 2, (1, 2, 3, 4)), (5, 2, (1, 3, 4)),
                       (7, 3, (1, 2, 3)), (10, 3, (1, 2, 3)), (4, 3, (2, 3, 5))):
        for k in range(1, len(exps)+1):
            ms = exps[:k]
            q = prod(b**m-1 for m in ms)
            ep = valuation(q, p)
            stride = lcm(2, ord_mod(b, q // p**ep))
            size = p**max(0, ep-valuation(b**stride-1, p))
            assert size >= p**max(0, k*valuation(b-1, p)-valuation(b*b-1, p))
            period = ord_mod(b, q)
            for start in {1, pow(b, sum(ms), q)}:
                group = {start * pow(b, i*stride, q) % q for i in range(size)}
                assert group == {(start+j*(q//size)) % q for j in range(size)}
                assert discrepancy(law(list(orbit(F(start, q), b, period)))) <= F(1, size)
            for harmonic in (1, 2, p):
                length = ord_mod(b, size//gcd(size,harmonic))
                for n in {1, min(length,15), min(length+1,19)}:
                    powers = [pow(b, i, q) for i in range(n)]
                    surviving = sum(harmonic*(x-y) % size == 0 for x in powers for y in powers)
                    classes = Counter(i % length for i in range(n))
                    assert surviving == sum(v*v for v in classes.values())
                    assert F(surviving, n*n) <= F(1,n)+F(1,length)
                    if n <= length:
                        assert surviving == n
            assert pow(b, (-sum(ms)) % period, q) * pow(b, sum(ms), q) % q == 1
            L = 0
            while b**(L+1) <= q:
                L += 1
            for n in (1, max(1, L), 2*L+1):
                points = list(orbit(F(1, q), b, n))
                for h in range(L):
                    length = min(n, L-h)
                    assert all(x < F(1, b**h) for x in points[:length])
                    assert discrepancy(law(points)) >= F(length, n)-F(1, b**h)
            cases += 1
    print(f"E2: {cases} product denominators; exact grids, mean-square diagonal range and starting phases.")


def mahler_model(b, m, k):
    exps = [m**i for i in range(k)]
    s = sum(exps)
    a = prod(b**i-1 for i in exps)
    return a, s, m**k


def euler_model(b, k):
    s = k*(3*k+1)//2
    a = b**s
    for i in range(1, k+1):
        for exponent in (i*(3*i-1)//2, i*(3*i+1)//2):
            a += (-1)**i * b**(s-exponent)
    return a, s, s+2*k+1


def reciprocal_interval(b, model):
    a, s, next_exponent = model
    u = F(a, b**s)
    tail = F(b, (b-1)*b**next_exponent)
    assert u > tail
    return 1/(u+tail), 1/(u-tail)


def fixed_distance_lower(b, n, interval):
    lo, hi = (z * ((b-1)*b**n) for z in interval)
    if ceil(lo) <= floor(hi):
        return F(0)
    return min(norm(lo), norm(hi))


def check_separation(b, model, fine, n):
    a, s, _ = model
    lo, hi = fine
    rational = F(b**s, a)
    assert gcd(a, b) == 1 and a > b-1
    assert norm((b-1)*b**n*rational) >= F(1, a)
    err = max(abs(lo-rational), abs(hi-rational)) * ((b-1)*b**n)
    assert err < F(1, 2*a)
    assert fixed_distance_lower(b, n, fine) >= F(1, 2*a)
    assert any(fixed_distance_lower(b, j, fine) >= F(1, 2*b)
               for j in range(n, n+s+5))


def transition_measurement(b, interval, places):
    lo, hi = (x*b**places for x in interval)
    assert floor(lo) == floor(hi)
    n = floor(lo)
    digits = []
    for _ in range(places):
        n, digit = divmod(n, b)
        digits.append(digit)
    return sum(x != y for x, y in zip(digits, digits[1:]))


def check_partitions():
    examples = {}
    count = 0
    for b in (2, 3, 5, 10):
        for m in (3, 4, 5):
            for k in (3, 4, 5):
                model = mahler_model(b, m, k)
                _, s, nxt = model
                assert nxt-s == (m-2)*s+1
                fine = reciprocal_interval(b, mahler_model(b, m, k+1))
                for n in (0, (nxt-s)//2, nxt-s-6):
                    check_separation(b, model, fine, n)
                    count += 1
            if b == 2:
                examples[f"X(2,{m})"] = transition_measurement(
                    b, reciprocal_interval(b, mahler_model(b, m, 6)), 256)
        fine = reciprocal_interval(b, euler_model(b, 20))
        for k in range(5, 16):
            model = euler_model(b, k)
            n = 2*k+1-6
            check_separation(b, model, fine, n)
            count += 1
        if b == 2:
            examples["P(2)"] = transition_measurement(b, fine, 256)
        for k in (16, 32, 64, 128):
            r = F(b**(k*(k+1)//2), prod(b**j-1 for j in range(1, k+1)))
            lo, hi = fine
            assert 0 < lo-r <= hi-r <= lo*F(1, (b-1)*b**k)
            error_sum = (hi-r) * F(b**k-1, b-1)
            assert error_sum <= lo/(b-1)**2
            orbit_r = list(orbit(r, b, k))
            total = sum((norm((b-1)*x)/(b-1) for x in orbit_r), F(0))
            escapes = sum(fixed_distance_lower(b, n, fine) >= F(1, 2*b) for n in range(k))
            lower = F(escapes, 2*b*(b-1)) - error_sum
            assert total >= lower
            assert 1-discrepancy(law(orbit_r)) >= F(2, 5)*lower/k - F(1, k)
    print(f"E3/E4: {count} reciprocal-separation instances and 16 actual Euler orbit windows.")
    print("Finite measurement: transitions among 256 certified digits:", examples)


if __name__ == "__main__":
    check_padding()
    check_convolution()
    check_grids()
    check_partitions()
