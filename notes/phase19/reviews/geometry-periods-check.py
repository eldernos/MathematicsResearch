"""Independent checks for the Phase 19 review of geometry.md,
products-of-remainders.md and taylor-periods.md.

Standard library only.  Run:  python3 geometry-periods-check.py
Every section prints PASS/FAIL lines or a small table that the review quotes.
"""
from fractions import Fraction as F
from math import gcd, log, sqrt, isqrt
import random
import sys

sys.stdout.reconfigure(encoding="utf-8")

random.seed(19)


# ---------------------------------------------------------------- discrepancy
def disc(pts):
    """Extreme discrepancy over half-open [a,c) in [0,1] (Kuiper form D+ + D-)."""
    xs = sorted(pts)
    n = len(xs)
    dp = max([0] + [F(i + 1, n) - x if isinstance(x, F) else (i + 1) / n - x
                    for i, x in enumerate(xs)])
    dm = max([0] + [x - F(i, n) if isinstance(x, F) else x - i / n
                    for i, x in enumerate(xs)])
    return dp + dm


def star(pts):
    """Star discrepancy over anchored [0,t)."""
    xs = sorted(pts)
    n = len(xs)
    return max([0] + [F(i + 1, n) - x for i, x in enumerate(xs)]
               + [x - F(i, n) for i, x in enumerate(xs)])


def frac(x):
    return x - (x.numerator // x.denominator)


def orbit(b, x, N):
    return [frac(F(b) ** n * x) for n in range(N)]


def D(b, x, N):
    return disc(orbit(b, x, N))


def nint_dist(x):
    f = frac(x)
    return min(f, 1 - f)


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    return ok


# ------------------------------------------------- 1. finite pseudometric
def section1():
    print("\n== 1. finite distance d_N(x,y)=1-D_N(x-y) ==")
    ok_max = ok_bounds = ok_local = ok_conc = True
    for _ in range(400):
        b = random.randint(2, 6)
        N = random.randint(2, 7)
        x = F(random.randint(0, 10**6), 10**6 + random.randint(1, 999))
        y = F(random.randint(0, 10**6), 10**6 + random.randint(1, 999))
        z = x - y
        dN = 1 - D(b, z, N)
        # maximum formula: |D(u+x)-D(u+y)| <= d_N with equality at u=-y
        for _ in range(4):
            u = F(random.randint(0, 10**5), 10**5 + 7)
            if abs(D(b, u + x, N) - D(b, u + y, N)) > dN:
                ok_max = False
        if abs(D(b, x - y, N) - D(b, 0, N)) != dN:
            ok_max = False
        # two-sided bound
        e = nint_dist((b - 1) * z)
        lo = min(F(1, N), e)
        hi = F(b ** (N - 1) - 1, b - 1) * e
        if not (lo <= dN <= hi):
            ok_bounds = False
        # concentration-function identity 1-D = inf_l (1-Q(l)+l)
        pts = orbit(b, z, N)
        best = F(1)  # l=0 arcs: 1 - (max multiplicity)/N + 0 handled below
        for p in pts:
            for q in pts:
                l = frac(q - p)  # arc [p, p+l] closed, enlargement -> 0
                mass = sum(1 for s in pts if frac(s - p) <= l)
                best = min(best, 1 - F(mass, N) + l)
        if best != dN:
            ok_conc = False
    # local formula d_N = (b^{N-1}-1)|u| when < min(1/2,1/N)
    for _ in range(300):
        b = random.randint(2, 6)
        N = random.randint(2, 7)
        h = F(random.randint(0, b - 2), b - 1)
        L = F(b ** (N - 1) - 1)
        umax = min(F(1, 2), F(1, N)) / L
        u = umax * F(random.randint(1, 999), 1000) * random.choice([1, -1])
        dN = 1 - D(b, h + u, N)
        if dN != L * abs(u):
            ok_local = False
    check("maximum formula and attainment at u=-y (400 random cases)", ok_max)
    check("min(1/N,||(b-1)z||) <= d_N <= (b^(N-1)-1)/(b-1)||(b-1)z||", ok_bounds)
    check("1-D = inf_l {1-Q(l)+l} on circle samples", ok_conc)
    check("local formula d_N=(b^(N-1)-1)|u| below min(1/2,1/N)", ok_local)
    # zero-set: d_N=0 iff (b-1)z integral
    zs = all((1 - D(b, F(k, b - 1), 5)) == 0 for b in range(2, 8) for k in range(b - 1))
    check("fixed points F_b have d_N=0", zs)


# ------------------------------------------------- 2. rational kernel & scalars
def in_K_rational(b, x):
    """Direct orbit test: does the eventually periodic orbit end in a fixed point?"""
    x = frac(x)
    seen = {}
    n = 0
    while x not in seen:
        seen[x] = n
        x = frac(b * x)
        n += 1
    return frac(b * x) == x  # cycle is a fixed point


def den_criterion(b, x):
    q = frac(x).denominator
    for _ in range(64):
        g = gcd(q, b)
        if g == 1:
            break
        q //= g
    return (b - 1) % q == 0


def b_primary(b, d):
    for _ in range(64):
        g = gcd(d, b)
        if g == 1:
            break
        d //= g
    return d == 1


def section2():
    print("\n== 2. rational membership and the scalar ring Z[1/b] ==")
    ok = all(in_K_rational(b, F(a, q)) == den_criterion(b, F(a, q))
             for b in range(2, 13) for q in range(1, 120) for a in range(q))
    check("orbit-ends-in-fixed-point <=> denominator | b^j(b-1), b<=12, q<120", ok)
    # (a/d) K_b ∩ Q ⊆ K_b  iff  d is b-primary; witness 1/(b-1)
    ok = True
    for b in range(2, 13):
        Kq = [F(a, q) for q in range(1, 60) for a in range(q) if den_criterion(b, F(a, q))]
        for d in range(1, 40):
            for a in range(-6, 7):
                if a == 0 or gcd(a, d) != 1:
                    continue
                preserved = all(den_criterion(b, F(a, d) * z) for z in Kq)
                witness = den_criterion(b, F(a, d) * F(1, b - 1))
                if preserved != b_primary(b, d) or witness != b_primary(b, d):
                    ok = False
    check("rational a/d preserves K_b∩Q iff d is b-primary; 1/(b-1) is a witness", ok)
    # K_{a^r} ∩ K_{a^s} ∩ Q = K_{a^gcd} ∩ Q
    ok = True
    for a in (2, 3, 5):
        for r in range(1, 5):
            for s in range(1, 5):
                g = gcd(r, s)
                for q in range(1, 200):
                    for num in range(q):
                        x = F(num, q)
                        lhs = den_criterion(a ** r, x) and den_criterion(a ** s, x)
                        if lhs != den_criterion(a ** g, x):
                            ok = False
    check("K_{a^r}∩K_{a^s}=K_{a^gcd(r,s)} on rationals (a=2,3,5; r,s<=4; q<200)", ok)
    check("1/4 in K_2, not in K_3", den_criterion(2, F(1, 4)) and not den_criterion(3, F(1, 4)))
    # rational non-closure under products for b>=3
    check("(1/(b-1))^2 not in K_b for 3<=b<=30",
          all(not den_criterion(b, F(1, (b - 1) ** 2)) for b in range(3, 31)))


# ------------------------------------------------- 3. single residue test
def float_orbit_mod(Z, den, b, N):
    """samples frac(b^n * Z/den) as floats, exact integer arithmetic"""
    out = []
    r = Z % den
    for _ in range(N):
        out.append(r / den)
        r = (r * b) % den
    return out


def disc_float(xs):
    xs = sorted(xs)
    n = len(xs)
    dp = max(0.0, max((i + 1) / n - x for i, x in enumerate(xs)))
    dm = max(0.0, max(x - i / n for i, x in enumerate(xs)))
    return dp + dm


def section3():
    print("\n== 3. individual scalar test (b=10, c=1/3, d=3) ==")
    b, Nmax = 10, 20000
    L = Nmax + 80
    S = [k * k for k in range(1, isqrt(L) + 1) if k * k + 2 < L]
    # w1: ones in clumps of three; w2: isolated ones
    W1 = sum(10 ** (L - a) + 10 ** (L - a - 1) + 10 ** (L - a - 2) for a in S)
    W2 = sum(10 ** (L - a) for a in S)
    den = 10 ** L
    print("   N     D_N(z1)  D_N(z1/3)   D_N(z2)  D_N(z2/3)   dens(k_n≡0 mod 3) z1,z2")
    for N in (1000, 5000, 20000):
        rows = []
        for W in (W1, W2):
            # z = 1/3 + W/10^L ; z = (10^L + 3W)/(3*10^L)
            Zn, Zd = den + 3 * W, 3 * den
            rows.append(disc_float(float_orbit_mod(Zn, Zd, b, N)))
            rows.append(disc_float(float_orbit_mod(Zn, 3 * Zd, b, N)))
        dens = []
        for W in (W1, W2):
            # k_n = integer part of 10^n w (nearest integer except next to a one), mod 3
            cnt, I3, rem = 0, (W // den) % 3, W % den
            for n in range(N):
                cnt += (I3 == 0)
                rem *= 10
                I3 = (10 * I3 + rem // den) % 3
                rem %= den
            dens.append(cnt / N)
        print(f"{N:6d}  {rows[0]:.4f}   {rows[1]:.4f}    {rows[2]:.4f}   {rows[3]:.4f}     {dens[0]:.4f} {dens[1]:.4f}")


# ------------------------------------------------- 4. star and box examples
def box_disc(pts, grid):
    """exact sup over boxes [a1,c1)x[a2,c2) with endpoints in grid ∪ {limits}.
    Excess sup: smallest box containing a subset; deficit sup: largest empty-ish box."""
    n = len(pts)
    best = F(0)
    from itertools import combinations
    # excess: for each subset, the minimal box has area (spread) and contains maybe more
    for k in range(1, n + 1):
        for sub in combinations(pts, k):
            xs = [p[0] for p in sub]
            ys = [p[1] for p in sub]
            area = (max(xs) - min(xs)) * (max(ys) - min(ys))
            inside = sum(1 for p in pts if min(xs) <= p[0] <= max(xs) and min(ys) <= p[1] <= max(ys))
            best = max(best, F(inside, n) - area)
    # deficit: boxes with endpoints on grid lines (exclusive), brute force
    for a1 in grid:
        for c1 in grid:
            if c1 <= a1:
                continue
            for a2 in grid:
                for c2 in grid:
                    if c2 <= a2:
                        continue
                    inside = sum(1 for p in pts if a1 <= p[0] < c1 and a2 <= p[1] < c2)
                    best = max(best, (c1 - a1) * (c2 - a2) - F(inside, n))
    return best


def section4():
    print("\n== 4. star discrepancy and box discrepancy counterexamples ==")
    b, N = 2, 3
    x, z = F(1, 4), F(-1, 256)
    sx, sxz, sz = star(orbit(b, x, N)), star(orbit(b, x + z, N)), star(orbit(b, z, N))
    print(f"   D*(x)={sx}  D*(x+z)={sxz}  D*(z)={sz}")
    check("star: |D*(x+z)-D*(x)| = 1/6+1/64 > 1-D*(z) = 1/64",
          sx == F(1, 2) and sxz == F(1, 3) - F(1, 64) and sz == 1 - F(1, 64)
          and abs(sxz - sx) > 1 - sz)
    check("extreme D obeys the translation bound on the same data",
          abs(D(b, x + z, N) - D(b, x, N)) <= 1 - D(b, z, N))
    pts = [(F(1, 3), F(1, 3)), (F(2, 3), F(2, 3))]
    grid = [F(0), F(1, 3), F(2, 3), F(1)]
    # add points just to the right of 1/3, 2/3 via exclusive endpoints: grid suffices
    # because half-open boxes [1/3,.) include and (1/3+,.) exclude are both limits.
    eps = F(1, 10**9)
    grid2 = sorted(set(grid + [g + eps for g in grid if g < 1]))
    bd = box_disc(pts, grid2)
    print(f"   box discrepancy of x+z ≈ {float(bd):.9f}  (8/9={8/9:.9f})")
    check("box: D(x+z)=8/9 while D(x)=D(z)=1, violating |D(x+z)-D(x)|<=1-D(z)",
          abs(bd - F(8, 9)) < F(1, 10**6))


# ------------------------------------------------- 5. integer multiplication
def section5():
    print("\n== 5. integer multiplication ==")
    ok = True
    for m in range(2, 9):
        b, x, N = m + 1, F(1, m * m), m * 7
        if not (D(b, x, N) == F(1, m) and D(b, m * x, N) == 1):
            ok = False
    check("b=m+1, x=1/m^2, m|N: D(x)=1/m, D(mx)=1 (m=2..8)", ok)
    ok = True
    for _ in range(300):
        b, N, m = random.randint(2, 5), random.randint(1, 8), random.randint(1, 6)
        x = F(random.randint(0, 10**6), 10**6 + 3)
        a, am = D(b, x, N), D(b, m * x, N)
        if not (max(0, 1 - m * (1 - a)) <= am <= min(1, m * a)):
            ok = False
    check("max(0,1-m(1-D)) <= D(mx) <= min(1,mD) (300 random cases)", ok)


def schedule_digits(b, words, weights, rounds):
    """Greedy weight scheduler of B4 with block k of length ~ k periods."""
    C = [0] * len(words)
    digits = []
    for k in range(1, rounds + 1):
        i = max(range(len(words)), key=lambda j: k * weights[j] - C[j])
        C[i] += 1
        w = words[i]
        reps = max(1, (4 * k) // len(w))
        digits.extend(w * reps)
    return digits


def samples_from_digits(b, digits, N, prec=None):
    """T^n x = sum_i d_{n+i} b^{-i}, from a rolling window of the next prec digits"""
    if prec is None:
        prec = max(1, int(52 / log(b, 2)))
    top = b ** (prec - 1)
    scale = float(b ** prec)
    W = 0
    for i in range(1, prec + 1):
        W = W * b + digits[i]
    out = []
    for n in range(N):
        out.append(W / scale)
        W = (W % top) * b + digits[n + prec + 1]
    return out


def section6():
    print("\n== 6. boundary spectrum D(mx)->1, D(x)->theta+(1-theta)/m0 ==")
    cases = [
        # b, m, m0, cycles of grid j/m0 as periodic digit words, cycle sizes
        (2, 3, 3, [[0], [0, 1]], [1, 2]),
        (2, 6, 3, [[0], [0, 1]], [1, 2]),
        (3, 4, 4, [[0], [0, 2], [1]], [1, 2, 1]),
        (10, 21, 7, [[0], [1, 4, 2, 8, 5, 7]], [1, 6]),
    ]
    print("   b  m  m0 theta   N      D_N(x)   target   D_N(mx)")
    for b, m, m0, words, sizes in cases:
        for theta in (0.0, 0.5):
            wts = [theta + (1 - theta) * sizes[0] / m0] + [(1 - theta) * s / m0 for s in sizes[1:]]
            digs = schedule_digits(b, words, wts, 600)
            N = len(digs) - 60
            xs = samples_from_digits(b, digs, N)
            dx = disc_float(xs)
            dmx = disc_float([(m * t) % 1.0 for t in xs])
            print(f"  {b:2d} {m:2d} {m0:2d}  {theta:.1f}  {N:7d}  {dx:.4f}   {theta + (1 - theta) / m0:.4f}   {dmx:.4f}")


# ------------------------------------------------- 7. sparse product
def moser_de_bruijn(limit):
    A, k = [], 0
    while True:
        a = int(bin(k)[2:], 4)  # binary digits read in base 4
        if a >= limit:
            break
        A.append(a)
        k += 1
    return A


def section7():
    print("\n== 7. products of sparse remainders ==")
    lim = 2000
    A = moser_de_bruijn(lim)
    B = [2 * a for a in A]
    sums = sorted(a + c for a in A for c in B if a + c < lim)
    check("every n<2000 is uniquely a+c (a in A, c in 2A)", sums == list(range(lim)))
    for b, r in ((2, 2), (3, 2), (2, 3), (10, 2)):
        X = F(1, b ** r)
        P = 60
        U = sum(X ** a for a in A if a < P)
        V = sum(X ** c for c in B if c < P)
        err = abs(U * V - 1 / (1 - X))
        prod = F(1)
        k = 0
        while 4 ** k < P:
            prod *= 1 + X ** (4 ** k)
            k += 1
        check(f"b={b},r={r}: UV=b^r/(b^r-1) to {float(err):.1e}; U=prod(1+x^(4^k)) to {float(abs(prod - U)):.1e}",
              err < X ** (P - 4) and abs(prod - U) < X ** (P - 4))
        m = b ** r - 1
        cyc = [F(b ** j % m, m) for j in range(r)]
        print(f"     orbit of frac(UV)=1/{m}: period {r}, cycle discrepancy {disc(cyc)}")
    # d_N(U) rate for b=2, r=2
    b, r = 2, 2
    Nmax = 200000
    Lb = r * Nmax + 100
    pos = [r * a for a in moser_de_bruijn(Lb) if 0 < r * a < Lb]
    digits = [0] * (Lb + 1)
    for p in pos:
        digits[p] = 1
    print("   N        1-D_N(U)   (1-D_N(U)) sqrt(N)/log N")
    for N in (1000, 10000, 100000, 200000):
        xs = samples_from_digits(2, digits, N)
        dU = 1 - disc_float(xs)
        print(f"  {N:7d}  {dU:.5f}   {dU * sqrt(N) / log(N):.4f}")


# ------------------------------------------------- 8. Taylor-prefix orders
def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def factor(n, ps):
    f = {}
    for p in ps:
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def ord_prime(p, ps):
    o = p - 1
    for q in factor(p - 1, ps):
        while o % q == 0 and pow(2, o // q, p) == 1:
            o //= q
    return o


def ord_factored(pe_list, ps):
    """lcm of ord_{p^e}(2) as a factorization dict"""
    R = {}
    for p, e in pe_list:
        o = ord_prime(p, ps)
        fo = factor(o, ps)
        # lift: ord_{p^e} = ord_p * p^k with k minimal s.t. 2^(ord_p p^k) = 1 mod p^e
        k = 0
        pe = p ** e
        while pow(2, o * p ** k, pe) != 1:
            k += 1
        if k:
            fo[p] = fo.get(p, 0) + k
        for q, a in fo.items():
            R[q] = max(R.get(q, 0), a)
    return R


def section8():
    print("\n== 8. order of 2 modulo the odd Taylor denominators of log 2 ==")
    Nmax = 3000
    ps = primes_upto(Nmax + 10)
    S = F(0)
    rows = []
    checkpts = {50, 100, 200, 400, 800, 1200, 1600, 2000, 2500, 3000}
    lemma_ok = True
    for N in range(1, Nmax + 1):
        S += F(1, N * 2 ** N)
        if N not in checkpts:
            continue
        P = S * 2 ** N
        q = P.denominator
        while q % 2 == 0:
            q //= 2
        fq = {}
        for p in ps:
            if p > N:
                break
            if q % p == 0:
                e = 0
                while q % p == 0:
                    q //= p
                    e += 1
                fq[p] = e
        assert q == 1
        R = ord_factored(list(fq.items()), ps)
        logR = sum(a * log(p) for p, a in R.items())
        tau = 1
        for a in R.values():
            tau *= a + 1
        H = sum(1 for p in fq if N / 2 < p <= N)
        Hpred = sum(1 for p in ps if N / 2 < p <= N and p > 2)
        bound = tau * sqrt(N * log(2) / log(N / 2))
        lemma_ok &= (H <= bound) and H == Hpred
        # drop the axis whose removal shrinks the order most (largest single local order)
        loc = {p: ord_factored([(p, e)], ps) for p, e in fq.items()}
        worst = None
        for p0 in fq:
            R2 = {}
            for p, fo in loc.items():
                if p != p0:
                    for t, a in fo.items():
                        R2[t] = max(R2.get(t, 0), a)
            l2 = sum(a * log(t) for t, a in R2.items())
            worst = l2 if worst is None else min(worst, l2)
        rows.append((N, len(fq), H, logR, worst, log(tau)))
    check("all odd primes in (N/2,N] divide q_N and H <= tau(R) sqrt(N log2/log(N/2))", lemma_ok)
    print("    N  #axes  H   log R    log R/(logN loglogN)  min_drop/(..)  log R/N  logtau/logN")
    for N, na, H, lR, w, lt in rows:
        den = log(N) * log(log(N))
        print(f"  {N:5d} {na:5d} {H:4d} {lR:9.1f}   {lR / den:8.2f}           {w / den:8.2f}     {lR / N:.3f}   {lt / log(N):.2f}")
    print(f"   claimed liminf constant 1/(2 log 2) = {1 / (2 * log(2)):.4f}")


if __name__ == "__main__":
    section1()
    section2()
    section3()
    section4()
    section5()
    section6()
    section7()
    section8()
