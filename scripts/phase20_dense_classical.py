#!/usr/bin/env python3
"""Phase 20, Tracks D1-D4 and E1-E3: exact-arithmetic checks and finite diagnostics.

Run from the repository root:

    python -B scripts/phase20_dense_classical.py

Standard library only.  Every real number is represented by a certified integer
enclosure ``lo <= b^K x <= hi``.  Digits are reported only when both endpoints give
the same floor at the requested precision.  Orbit points use P-digit truncations,
which move every sorted sample by less than b^-P in one direction, so each reported
extreme discrepancy is within b^-P of the exact finite value (Phase 17, Section 7).

Exact identities (character orthogonality, Jacobi, Legendre, Ramanujan congruences,
Möbius collapse, the radix-primary reciprocal criterion, ...) are checked with
integers or Fractions; a failed check makes the script exit with status 1.  The
discrepancy values are finite measurements and prove no asymptotic statement.
"""

from __future__ import annotations

import math
import sys
from decimal import Decimal, getcontext
from fractions import Fraction

FAILURES: list[str] = []


def check(cond: bool, msg: str) -> None:
    if not cond:
        FAILURES.append(msg)
        print("  FAIL:", msg)


def header(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Certified enclosures and discrepancy
# ---------------------------------------------------------------------------


class Enc:
    """Real number x with lo <= b^K x <= hi (integers)."""

    def __init__(self, b: int, K: int, lo: int, hi: int):
        assert lo <= hi
        self.b, self.K, self.lo, self.hi = b, K, lo, hi

    def _same(self, o: "Enc") -> None:
        assert self.b == o.b and self.K == o.K

    def __add__(self, o: "Enc") -> "Enc":
        self._same(o)
        return Enc(self.b, self.K, self.lo + o.lo, self.hi + o.hi)

    def __sub__(self, o: "Enc") -> "Enc":
        self._same(o)
        return Enc(self.b, self.K, self.lo - o.hi, self.hi - o.lo)

    def scale(self, c: int) -> "Enc":
        a, d = self.lo * c, self.hi * c
        return Enc(self.b, self.K, min(a, d), max(a, d))

    def plus_int(self, c: int) -> "Enc":
        s = c * self.b ** self.K
        return Enc(self.b, self.K, self.lo + s, self.hi + s)

    def __mul__(self, o: "Enc") -> "Enc":
        self._same(o)
        prods = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        B = self.b ** self.K
        return Enc(self.b, self.K, min(prods) // B, -((-max(prods)) // B))

    def power(self, k: int) -> "Enc":
        r = self
        for _ in range(k - 1):
            r = r * self
        return r

    def recip(self) -> "Enc":
        assert self.lo > 0
        B2 = self.b ** (2 * self.K)
        return Enc(self.b, self.K, B2 // self.hi, -((-B2) // self.lo))

    def digits(self, D: int) -> tuple[int, list[int]]:
        """Integer part and the first D certified fractional digits."""
        assert D <= self.K
        s = self.b ** (self.K - D)
        a, c = self.lo // s, self.hi // s
        if a != c:
            raise ValueError("enclosure too wide for %d digits" % D)
        ip, fr = divmod(a, self.b ** D)
        return ip, to_digits(fr, self.b, D)


def to_digits(v: int, b: int, nd: int) -> list[int]:
    if nd <= 48:
        out = [0] * nd
        for i in range(nd - 1, -1, -1):
            v, out[i] = divmod(v, b)
        return out
    lo_n = nd // 2
    hi, lo = divmod(v, b ** lo_n)
    return to_digits(hi, b, nd - lo_n) + to_digits(lo, b, lo_n)


def from_coeffs(b: int, K: int, coeff, tail_lo: int, tail_hi: int) -> Enc:
    """x = sum_{m>=0} coeff(m) b^-m, with b^K * (tail beyond K) in [tail_lo, tail_hi]."""
    S = 0
    for m in range(K + 1):
        S = S * b + coeff(m)
    return Enc(b, K, S + tail_lo, S + tail_hi)


def precision(b: int) -> int:
    P = 1
    while b ** P < 2 ** 40:
        P += 1
    return P


def orbit_points(digs: list[int], b: int, N: int) -> list[float]:
    P = precision(b)
    assert len(digs) >= N + P
    BP = b ** P
    w = 0
    for i in range(P):
        w = w * b + digs[i]
    pts = []
    for n in range(N):
        pts.append(w / BP)
        w = (w * b + digs[n + P]) % BP
    return pts


def disc(points: list[float]) -> float:
    ys = sorted(points)
    M = len(ys)
    hi = lo = 0.0
    for i, y in enumerate(ys, 1):
        hi = max(hi, i / M - y)
        lo = min(lo, (i - 1) / M - y)
    return hi - lo


def disc_profile(x: Enc, Ns: list[int]) -> dict[int, float]:
    P = precision(x.b)
    _, digs = x.digits(max(Ns) + P)
    pts = orbit_points(digs, x.b, max(Ns))
    return {N: disc(pts[:N]) for N in Ns}


def fmt(prof: dict[int, float]) -> str:
    return "  ".join("D_%d=%.4f" % (N, v) for N, v in prof.items())


# ---------------------------------------------------------------------------
# Arithmetic helpers
# ---------------------------------------------------------------------------


def partitions(M: int) -> list[int]:
    p = [0] * (M + 1)
    p[0] = 1
    for n in range(1, M + 1):
        s, k = 0, 1
        while True:
            g1 = k * (3 * k - 1) // 2
            if g1 > n:
                break
            sgn = 1 if k % 2 else -1
            s += sgn * p[n - g1]
            g2 = k * (3 * k + 1) // 2
            if g2 <= n:
                s += sgn * p[n - g2]
            k += 1
        p[n] = s
    return p


def pentagonal_coeffs(M: int) -> list[int]:
    """Coefficients of prod_{k>=1} (1 - q^k) through q^M."""
    c = [0] * (M + 1)
    k = 0
    while True:
        done = True
        for kk in ([0] if k == 0 else [k, -k]):
            g = kk * (3 * kk - 1) // 2
            if g <= M:
                c[g] += -1 if kk % 2 else 1
                done = False
        if done and k > 0:
            break
        k += 1
    return c


def sparse_mul(a: list[int], c: list[int], M: int) -> list[int]:
    out = [0] * (M + 1)
    sa = [(i, v) for i, v in enumerate(a[: M + 1]) if v]
    sc = [(j, v) for j, v in enumerate(c[: M + 1]) if v]
    for i, u in sa:
        for j, v in sc:
            if i + j > M:
                break
            out[i + j] += u * v
    return out


def divisor_sums(M: int, k: int) -> list[int]:
    s = [0] * (M + 1)
    for d in range(1, M + 1):
        dk = d ** k
        for m in range(d, M + 1, d):
            s[m] += dk
    return s


def dirichlet_one_star(w, M: int) -> list[int]:
    """c(n) = sum_{d | n} w(d) for 1 <= n <= M (c[0] = 0)."""
    c = [0] * (M + 1)
    for d in range(1, M + 1):
        wd = w(d)
        if wd:
            for m in range(d, M + 1, d):
                c[m] += wd
    return c


def mobius(M: int) -> list[int]:
    mu = [1] * (M + 1)
    mu[0] = 0
    is_comp = [False] * (M + 1)
    primes = []
    for i in range(2, M + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > M:
                break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def poly_tail(C: float, k: float, K: int, b: int) -> int:
    """Integer >= C * sum_{j>=1} (K+j)^k b^-j  (needs e^{k/(K+1)} < b)."""
    lam = math.exp(k / (K + 1)) / b
    assert lam < 1
    val = C * (K + 1) ** k * (1 / b) / (1 - lam)
    return int(2 * val) + 2


def subexp_tail(alpha: float, K: int, b: int) -> int:
    """Integer >= sum_{j>=1} exp(alpha sqrt(K+j)) b^-j (Lemma D1.2 with C = 1, n = K)."""
    lam = math.exp(alpha / (2 * math.sqrt(K))) / b
    assert lam < 1
    val = math.exp(alpha * math.sqrt(K)) * lam / (1 - lam)
    return int(2 * val) + 2


def chi4(m: int) -> int:
    return 0 if m % 2 == 0 else (1 if m % 4 == 1 else -1)


def chi8(m: int) -> int:
    return {1: 1, 3: -1, 5: -1, 7: 1}.get(m % 8, 0)


def chim8(m: int) -> int:
    return {1: 1, 3: 1, 5: -1, 7: -1}.get(m % 8, 0)


def chim3(m: int) -> int:
    return {1: 1, 2: -1}.get(m % 3, 0)


def lambert_enc(b: int, K: int, w, bound_C: int = 1) -> Enc:
    """sum_m w(m)/(b^m - 1) = sum_n (1*w)(n) b^-n with |1*w| <= bound_C * tau(n) <= C n."""
    c = dirichlet_one_star(w, K)
    t = poly_tail(bound_C, 1, K, b)
    neg = any(v < 0 for v in c)
    return from_coeffs(b, K, lambda m: c[m], -t if neg else 0, t)


def cycle_disc(num: int, den: int, b: int) -> float:
    """Extreme discrepancy of the uniform measure on the purely periodic part of num/den."""
    g = math.gcd(num, den)
    num, den = num // g, den // g
    while math.gcd(den, b) > 1:  # move to the purely periodic tail
        num = (num * b) % den
        g = math.gcd(num, den)
        num, den = num // g, den // g
    if den == 1:
        return 1.0
    seen, r = [], num % den
    start = r
    while True:
        seen.append(Fraction(r, den))
        r = (r * b) % den
        if r == start:
            break
    ys = sorted(seen)
    M = len(ys)
    hi = lo = Fraction(0)
    for i, y in enumerate(ys, 1):
        hi = max(hi, Fraction(i, M) - y)
        lo = min(lo, Fraction(i - 1, M) - y)
    return float(hi - lo)


def in_Kb_rational(num: int, den: int, b: int) -> bool:
    """A rational is in K_b iff its reduced denominator divides b^j (b-1) (Phase 19)."""
    g = math.gcd(num, den)
    den //= g
    while True:
        g = math.gcd(den, b)
        if g == 1:
            break
        den //= g
    return (b - 1) % den == 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

NS = [1000, 2000, 4000]
NMAX = max(NS)
ALPHA = math.pi * math.sqrt(2.0 / 3.0)


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    PMAX = 7000
    p = partitions(PMAX)

    # ------------------------------------------------------------------ D1
    header("D1. Certified carry windows for P_b = sum p(m) b^-m")
    worst = min(ALPHA * math.sqrt(n) - math.log(p[n]) for n in range(1, PMAX + 1))
    check(worst > 0, "elementary bound p(n) <= exp(pi sqrt(2n/3))")
    print("  p(n) <= exp(pi*sqrt(2n/3)) for 1<=n<=%d; least log-margin %.4f" % (PMAX, worst))
    for n in (1000, 4000, 7000):
        hr = p[n] * 4 * math.sqrt(3) * n / math.exp(ALPHA * math.sqrt(n))
        print("  Hardy-Ramanujan ratio at n=%d: %.5f" % (n, hr))
    A = 2
    print("  window L(N) = ceil((a sqrt N + A ln N + ln(1/(sqrt b - 1)) + a^2/ln b)/ln b), A=2")
    for b in (2, 3, 5, 7, 11):
        for N in (1000, 4000):
            L = math.ceil((ALPHA * math.sqrt(N) + A * math.log(N)
                           + math.log(1 / (math.sqrt(b) - 1)) + ALPHA ** 2 / math.log(b)) / math.log(b))
            check(L <= 2 * ALPHA * math.sqrt(N) / math.log(b), "L(N) in the range of Lemma D1.2")
            n = N - 1  # p is nondecreasing, so T(n,L) <= T(N-1,L) for n < N
            J = L + 400
            # exact head of T(n, L) scaled by b^J, plus analytic remainder beyond J
            head = sum(p[n + j] * b ** (J - j) for j in range(L + 1, J + 1))
            rem = subexp_tail(ALPHA, n + J, b)
            ok = (head + rem) * N ** A <= b ** J
            check(ok, "T(N-1, L(N)) <= N^-2 for b=%d N=%d" % (b, N))
            # least window with the same certified property
            Lmin = L
            while Lmin > 1:
                h2 = sum(p[n + j] * b ** (J - j) for j in range(Lmin, J + 1))
                if (h2 + rem) * N ** A <= b ** J:
                    Lmin -= 1
                else:
                    break
            print("  b=%2d N=%4d: L(N)=%4d  least certified L=%4d  L(N)/sqrt N=%.3f  a/ln b=%.3f"
                  % (b, N, L, Lmin, L / math.sqrt(N), ALPHA / math.log(b)))
    # triangular-coordinate identity: R_{n,L} depends only on a(n+j) mod b^j
    b, L = 3, 25
    for n in (10, 500, 2500):
        R1 = sum(p[n + j] * b ** (L - j) for j in range(1, L + 1)) % b ** L
        R2 = sum((p[n + j] % b ** j) * b ** (L - j) for j in range(1, L + 1)) % b ** L
        check(R1 == R2, "triangular reduction of R_{n,L}")
    print("  R_{n,L} = sum_j (a(n+j) mod b^j) b^(L-j) mod b^L: checked (b=3, L=25)")

    # ------------------------------------------------------------------ D2
    header("D2. Partition constants P_b, b in {2,3,5,7,10,11}")
    profiles = {}
    for b in (2, 3, 5, 7, 10, 11):
        Pp = precision(b)
        D = NMAX + Pp
        K = D + 30
        while True:
            t = subexp_tail(ALPHA, K, b)
            if b ** (K - D) > 4 * t:
                break
            K += 10
        Pb = from_coeffs(b, K, lambda m: p[m], 0, t)
        # independent route: P_b = 1/E_b with E_b from the pentagonal theorem
        pc = pentagonal_coeffs(K)
        Eb = from_coeffs(b, K, lambda m: pc[m], -1, 1)
        Pinv = Eb.recip()
        ipa, da = Pb.digits(D)
        ipb, db = Pinv.digits(D)
        check(ipa == ipb and da == db, "P_%d digits agree with 1/E_%d" % (b, b))
        prof = disc_profile(Pb, NS)
        profiles[b] = prof
        print("  b=%2d K=%d: %d digits agree with 1/E_b.  %s" % (b, K, D, fmt(prof)))
        if b in (5, 7, 10, 11):
            ell, r = {5: (5, 3), 7: (7, 4), 10: (5, 3), 11: (11, 5)}[b]
            # n with n+1 ≡ 24^{-1}... i.e. p(n+1) ≡ 0 mod ell
            sel = [da[n] for n in range(NMAX) if n % ell == r]
            for n in range(NMAX):
                if n % ell == r:
                    check(p[n + 1] % ell == 0, "Ramanujan congruence at %d" % (n + 1))
            cnt = [sel.count(d) for d in range(b)]
            exp_ = len(sel) / b
            chi2 = sum((c - exp_) ** 2 / exp_ for c in cnt)
            print("    first digit of x_n on n≡%d mod %d (p(n+1)≡0 mod %d): counts %s chi2=%.1f (df=%d)"
                  % (r, ell, ell, cnt, chi2, b - 1))
            # exact identity d_1(x_n) ≡ p(n+1) + floor(T_{n+1}) (mod b)
            H, bad = 0, 0
            F = ipa  # floor(b^m P) built digit by digit
            for m in range(0, 400):
                H = H * b + p[m] if m > 0 else p[0]
                if m > 0:
                    F = F * b + da[m - 1]
                Tfloor = F - H  # floor(T_m)
                if m >= 1:
                    # digit d_{m} = first digit of x_{m-1}; check against p(m) + floor(T_m)
                    if (p[m] + Tfloor) % b != da[m - 1] % b:
                        bad += 1
            check(bad == 0, "first-digit carry identity base %d" % b)
            print("    identity d_1(x_n) ≡ p(n+1)+floor(T_{n+1}) (mod b) verified for n<399")
    for (ell, mod, delta) in ((5, 25, 24), (7, 49, 47), (11, 121, 116)):
        okc = all(p[n] % mod == 0 for n in range(delta, PMAX + 1, mod))
        check(okc, "p(%dn+%d) ≡ 0 mod %d" % (mod, delta, mod))
    print("  p(25n+24)≡0 (25), p(49n+47)≡0 (49), p(121n+116)≡0 (121) through n<=%d" % PMAX)
    # pentagonal circle recurrence x_n ≡ sum eps_k x_{n-g_k} + rho_n
    K = NMAX + 400
    PbE = from_coeffs(2, K, lambda m: p[m], 0, subexp_tail(ALPHA, K, 2))
    ip2, dg = PbE.digits(NMAX + 100)
    Pval = ip2 + sum(dg[i] * 2.0 ** -(i + 1) for i in range(60))

    def xs(n):
        return sum(dg[n + i] * 2.0 ** -(i + 1) for i in range(52))
    gs = []
    k = 1
    while k * (3 * k - 1) // 2 < NMAX:
        sg = 1 if k % 2 else -1
        gs += [(k * (3 * k - 1) // 2, sg), (k * (3 * k + 1) // 2, sg)]
        k += 1
    for n in (100, 1000, 3000):
        s = sum(e * xs(n - g) for g, e in gs if g <= n)
        rho = sum(e * Pval * 2.0 ** (n - g) for g, e in gs if g > n and g - n < 60)
        err = (s + rho - xs(n)) % 1.0
        err = min(err, 1 - err)
        check(err < 1e-9, "pentagonal circle recurrence at n=%d" % n)
    print("  circle recurrence x_n ≡ Σ ε_k x_(n-g_k) + ρ_n (mod 1) checked at n=100,1000,3000")

    # ------------------------------------------------------------------ D3
    header("D3. Theta powers, Eisenstein values and eta powers (base 2 unless noted)")
    M = 3000
    th = [0] * (M + 1)
    j = 0
    while j * j <= M:
        th[j * j] += 1 if j == 0 else 2
        j += 1
    r2 = sparse_mul(th, th, M)
    r3 = sparse_mul(r2, th, M)
    r4 = sparse_mul(r3, th, M)
    sig1 = divisor_sums(4 * M, 1)
    jac = all(r4[n] == 8 * sum(d for d in range(1, n + 1) if n % d == 0 and d % 4) for n in range(1, 400))
    check(jac, "Jacobi four-square formula")
    # theta^4 = (4 E_2(q^4) - E_2(q))/3 coefficientwise: r4(n) = 8 sigma(n) - 32 sigma(n/4)
    ok = all(r4[n] == 8 * sig1[n] - (32 * sig1[n // 4] if n % 4 == 0 else 0) for n in range(1, M + 1))
    check(ok, "theta^4 = (4E_2(q^4) - E_2(q))/3")

    def legendre_exc(n):
        while n % 4 == 0 and n > 0:
            n //= 4
        return n % 8 == 7
    ok = all((r3[n] > 0) == (not legendre_exc(n)) for n in range(1, M + 1))
    check(ok, "Legendre three-square criterion")
    dens3 = sum(1 for n in range(1, M + 1) if r3[n]) / M
    dens2 = sum(1 for n in range(1, M + 1) if r2[n]) / M
    print("  Jacobi r_4 formula, theta^4=(4E_2(q^4)-E_2(q))/3, Legendre criterion: checked through %d" % M)
    print("  support density through %d: r_2: %.4f (zero density, ~K/sqrt(log X)), r_3: %.4f (limit 5/6)"
          % (M, dens2, dens3))
    D = NMAX + 40
    K = D + 60
    Th = from_coeffs(2, K, lambda m: (1 if m == 0 else (2 if math.isqrt(m) ** 2 == m else 0)), 0, 2)
    for name, x in (("Theta(1/2)", Th), ("Theta^2", Th.power(2)), ("Theta^3", Th.power(3)),
                    ("Theta^4", Th.power(4))):
        print("  %-12s %s" % (name, fmt(disc_profile(x, NS))))
    # Eisenstein values
    KE = D + 220
    sig = {k: divisor_sums(KE + 1, k) for k in (1, 3, 5)}
    for name, k, c0 in (("E_2(1/2)", 1, -24), ("E_4(1/2)", 3, 240), ("E_6(1/2)", 5, -504)):
        t = poly_tail(abs(c0), k + 1, KE, 2)  # sigma_k(n) <= n^k tau(n) <= n^{k+1}
        x = from_coeffs(2, KE, lambda m, k=k, c0=c0: 1 if m == 0 else c0 * sig[k][m], -t, t)
        print("  %-12s %s" % (name, fmt(disc_profile(x, NS))))
    # Delta identity: (E4^3 - E6^2)/1728 = q prod(1-q^n)^24
    Mt = 200
    s3 = divisor_sums(Mt, 3)
    s5 = divisor_sums(Mt, 5)
    E4 = [1] + [240 * s3[n] for n in range(1, Mt + 1)]
    E6 = [1] + [-504 * s5[n] for n in range(1, Mt + 1)]
    lhs = [a - c for a, c in zip(sparse_mul(sparse_mul(E4, E4, Mt), E4, Mt), sparse_mul(E6, E6, Mt))]
    eta = pentagonal_coeffs(Mt)
    e24 = [1] + [0] * Mt
    for _ in range(24):
        e24 = sparse_mul(e24, eta, Mt)
    ok = all(lhs[n] == 1728 * (e24[n - 1] if n >= 1 else 0) for n in range(Mt + 1))
    check(ok, "Delta = (E4^3 - E6^2)/1728 = q prod (1-q^n)^24")
    print("  Delta identity checked through q^%d (tau(2)=%d, tau(3)=%d)" % (Mt, e24[1], e24[2]))
    pcK = pentagonal_coeffs(K)
    Eb2 = from_coeffs(2, K, lambda m: pcK[m], -1, 1)
    for k in (1, 3, 4, 6):
        print("  E_2^%d (Euler function power) 1-D: %s" % (
            k, "  ".join("%d:%.4f" % (N, 1 - v) for N, v in disc_profile(Eb2.power(k), NS).items())))
    # Jacobi cube identity
    c3 = sparse_mul(sparse_mul(pcK[:801], pcK[:801], 800), pcK[:801], 800)
    jc = [0] * 801
    kk = 0
    while kk * (kk + 1) // 2 <= 800:
        jc[kk * (kk + 1) // 2] = (-1) ** kk * (2 * kk + 1)
        kk += 1
    check(c3 == jc, "Jacobi identity for prod(1-q^n)^3")
    print("  Jacobi: prod(1-q^n)^3 = sum (-1)^k (2k+1) q^(k(k+1)/2) checked through q^800")
    # theta^2 = 1 + 4 L_{chi4}(b) in K_b for every base: finite diagnostics
    for b in (2, 3, 5):
        Pp = precision(b)
        Kb = NMAX + Pp + 60
        Lb = lambert_enc(b, Kb, chi4)
        print("  base %d: 1 - D_N(L_chi4(b)) = %s" % (
            b, "  ".join("%d:%.4f" % (N, 1 - v) for N, v in disc_profile(Lb, NS).items())))

    # Theta^4 vs L_chi4^2 transfer (binary)
    L4 = lambert_enc(2, K, chi4)
    th4 = disc_profile(Th.power(4), NS)
    l2 = disc_profile(L4 * L4, NS)
    l1 = disc_profile(L4, NS)
    for N in NS:
        lhs = abs(th4[N] - l2[N])
        rhs = (1 - l1[N]) + 7 / N + 8 * 2 ** -40
        check(lhs <= rhs, "|D(Theta^4)-D(L^2)| <= 1-D(L)+7/N at N=%d" % N)
        print("  N=%d: |D(Theta^4) - D(L_chi4^2)| = %.4f <= 1 - D(L_chi4) + 7/N = %.4f" % (N, lhs, rhs))

    # ------------------------------------------------------------------ D4
    header("D4. Products and reciprocals in K_b")
    # (a) radix-primary reciprocal criterion, exhaustive on small supports
    import itertools
    for b in (2, 3, 5):
        for size in range(1, 5):
            for Mset in itertools.combinations(range(1, 8), size):
                mk = max(Mset)
                Q = b ** mk - sum(b ** (mk - m) for m in Mset)
                pred = (b - 1) % Q == 0
                check(in_Kb_rational(b ** mk, Q, b) == pred, "reciprocal criterion b=%d %s" % (b, Mset))
                if b >= 3:
                    check(pred == (Mset == (1,)), "b>=3: only z=1/b")
                else:
                    check(pred == (Mset == tuple(range(1, size + 1))), "b=2: only z=1-2^-K")
    print("  1/(1 - sum_{m in M} b^-m) in K_b  <=>  Q | b-1: checked for all M ⊆ {1..7}, |M|<=4, b=2,3,5")
    for b in (2, 3, 10):
        print("  b=%2d: D(cycle of 1-b^-2)=1 (radix-primary), D(cycle of b^2/(b^2-1))=%.4f"
              % (b, cycle_disc(b * b, b * b - 1, b)))
    # (b) infinite construction, stage k=2: z = 1/4 + 2^-m2 + (later terms beyond 10^6)
    m2 = 1080
    check(m2 % 54 == 0 and pow(2, m2, 81) == 1, "2^m2 ≡ 1 mod 81")
    Q2 = 3 * 2 ** (m2 - 2) - 1
    Ky = 4 * m2 + 200
    num = 2 ** Ky * 2 ** m2
    y2 = Enc(2, Ky, num // Q2, num // Q2 + 1)
    Ns = [m2, 2 * m2, 3 * m2, 4 * m2]
    prof = disc_profile(y2, Ns)
    band = [cycle_disc(1, 3 ** (j + 1), 2) for j in range(4)]
    band[0] = cycle_disc(4, 3, 2)
    print("  y = 1/(1-1/4-2^-1080-...): %s" % fmt(prof))
    print("  predicted band cycle discrepancies (units mod 3^(j+1), j=0..3): %s"
          % ", ".join("%.4f" % v for v in band))
    for J, N in enumerate(Ns, 1):
        bound = sum(band[:J]) / J + 0.02
        check(prof[N] <= bound, "band average bound at N=%d" % N)
    check(prof[4 * m2] < 0.3, "D_N(1/(1-z)) far from 1 at N=4 m2")
    # (c) squaring is not closed: x = U + V (Moser-de Bruijn, r=2)
    Aset = set()
    for v in range(0, 4096):
        if all(((v >> i) & 1) == 0 for i in range(1, 13, 2)):
            Aset.add(v)
    KU = NMAX + 300
    U = from_coeffs(2, KU, lambda m: 1 if (m % 2 == 0 and m // 2 in Aset) else 0, 0, 1)
    V = from_coeffs(2, KU, lambda m: 1 if (m % 4 == 0 and m // 4 in Aset) else 0, 0, 1)
    X = U + V
    UV = U * V
    ipuv, duv = UV.digits(NMAX)
    check(all(d == (1 if i % 2 == 1 else 0) for i, d in enumerate(duv[:NMAX - 20])), "UV = 4/3")
    for name, x in (("U", U), ("U^2", U * U), ("x=U+V", X), ("x^2", X * X)):
        print("  %-6s %s" % (name, fmt(disc_profile(x, NS))))
    print("  x^2 ≡ 2UV = 8/3 (mod K_2); limiting cycle discrepancy of 8/3: %.4f" % cycle_disc(8, 3, 2))

    # ------------------------------------------------------------------ E1
    header("E1. Residue-class Erdős–Borwein sums and real characters")
    Mc = 3000
    chars8 = {"chi4": chi4, "chi8": chi8, "chi-8": chim8}
    one8 = {nm: dirichlet_one_star(f, Mc) for nm, f in chars8.items()}
    odd = dirichlet_one_star(lambda m: m % 2, Mc)
    for r in (1, 3, 5, 7):
        cr = dirichlet_one_star(lambda m, r=r: 1 if m % 8 == r else 0, Mc)
        ok = all(4 * cr[n] - odd[n] == sum(f(r) * one8[nm][n] for nm, f in chars8.items())
                 for n in range(1, Mc + 1))
        check(ok, "4A_%d - E_odd = Σ χ(%d) L_χ" % (r, r))
    print("  value table: r      1  3  5  7")
    for nm, f in chars8.items():
        print("               %-6s %s" % (nm, "  ".join("%+d" % f(r) for r in (1, 3, 5, 7))))
    print("  4A_r - E_odd = χ4(r)L_χ4 + χ8(r)L_χ8 + χ-8(r)L_χ-8: coefficientwise through n=%d" % Mc)
    # mod 24: characters chi_{-3}^a chi_{-4}^b chi_8^c
    gens = [chim3, chi4, chi8]
    chars24 = []
    for a in (0, 1):
        for bb in (0, 1):
            for c in (0, 1):
                def f(m, a=a, bb=bb, c=c):
                    if math.gcd(m, 24) != 1:
                        return 0
                    return (gens[0](m) if a else 1) * (gens[1](m) if bb else 1) * (gens[2](m) if c else 1)
                chars24.append(f)
    ones24 = [dirichlet_one_star(f, Mc) for f in chars24]
    for r in (1, 5, 7, 11, 13, 17, 19, 23):
        cr = dirichlet_one_star(lambda m, r=r: 1 if m % 24 == r else 0, Mc)
        ok = all(8 * cr[n] == sum(f(r) * o[n] for f, o in zip(chars24, ones24)) for n in range(1, Mc + 1))
        check(ok, "8A_{%d,24} = Σ χ(%d) L_χ" % (r, r))
        # nonnegativity and sparse support of each 1*chi for nonprincipal chi
    for f, o in zip(chars24[1:], ones24[1:]):
        check(min(o[1:]) >= 0, "1*χ >= 0 for real χ")
    sup = [sum(1 for n in range(1, Mc + 1) if o[n]) / Mc for o in ones24[1:]]
    print("  8A_{r,24} = Σ_χ χ(r) L_χ for all 8 classes: checked; support densities of 1*χ through %d: %s"
          % (Mc, ", ".join("%.3f" % s for s in sup)))
    # finite discrepancy comparison, binary
    K = NMAX + 40 + 60
    Ar = {r: lambert_enc(2, K, lambda m, r=r: 1 if m % 8 == r else 0) for r in (1, 3, 5, 7)}
    Eo = lambert_enc(2, K, lambda m: m % 2)
    Lc = {nm: lambert_enc(2, K, f) for nm, f in chars8.items()}
    pa = {r: disc_profile(x, NS) for r, x in Ar.items()}
    pe = disc_profile(Eo, NS)
    pl = {nm: disc_profile(x, NS) for nm, x in Lc.items()}
    for r in (1, 3, 5, 7):
        print("  A_%d: %s" % (r, fmt(pa[r])))
    print("  E_odd: %s" % fmt(pe))
    for nm in chars8:
        print("  1-D_N(L_%s): %s" % (nm, "  ".join("%d:%.4f" % (N, 1 - v) for N, v in pl[nm].items())))
    for N in NS:
        bound = sum(1 - pl[nm][N] for nm in chars8) + 2 / N + 8 * 2 ** -40
        gap = max(abs(pa[r][N] - pe[N]) for r in (1, 3, 5, 7))
        check(gap <= bound, "E1 transfer inequality at N=%d" % N)
        print("  N=%d: max_r |D(A_r) - D(E_odd)| = %.4f <= Σ(1-D(L_χ)) + 2/N = %.4f" % (N, gap, bound))
    # base 3, modulus 3: A_{1,3}(3) - A_{2,3}(3) = L_{chi_{-3}}(3) (integer combination, any base)
    K3 = NMAX + precision(3) + 60
    a1 = disc_profile(lambert_enc(3, K3, lambda m: 1 if m % 3 == 1 else 0), NS)
    a2 = disc_profile(lambert_enc(3, K3, lambda m: 1 if m % 3 == 2 else 0), NS)
    l3 = disc_profile(lambert_enc(3, K3, chim3), NS)
    for N in NS:
        lhs = abs(a1[N] - a2[N])
        rhs = 1 - l3[N] + 4 * 3 ** -precision(3)
        check(lhs <= rhs, "base-3 class difference at N=%d" % N)
        print("  base 3, N=%d: |D(A_{1,3}) - D(A_{2,3})| = %.4f <= 1 - D(L_χ-3(3)) = %.4f" % (N, lhs, rhs))

    # ------------------------------------------------------------------ E2
    header("E2. Logarithmic Euler product and the Möbius collapse")
    Mk = 1500
    mu = mobius(Mk)
    sm1 = [Fraction(0)] + [Fraction(s, n) for n, s in enumerate(divisor_sums(Mk, 1)) if n >= 1]
    ok = True
    for Kk in range(1, Mk + 1):
        tot = sum(mu[m] * sm1[Kk // m] for m in range(1, Kk + 1) if Kk % m == 0)
        if tot != Fraction(1, Kk):
            ok = False
            break
    check(ok, "μ * σ_{-1} = 1/K")
    print("  (μ * σ_{-1})(K) = 1/K exactly for K <= %d: chronological prefixes are Taylor prefixes" % Mk)
    getcontext().prec = 90
    ln2 = Decimal(2).ln()
    for Mtr in (10, 20, 40):
        tot = Decimal(0)
        for m in range(1, Mtr + 1):
            if mu[m]:
                q = Decimal(2) ** (-m)
                F = Decimal(0)
                n = 1
                while True:
                    term = Decimal(sm1[n].numerator) / Decimal(sm1[n].denominator) * q ** n
                    F += term
                    if term < Decimal(10) ** -85:
                        break
                    n += 1
                tot += mu[m] * F
        err = abs(ln2 - tot)
        check(err <= Decimal(16) / 9 * Decimal(2) ** (-Mtr), "truncation error bound M=%d" % Mtr)
        print("  M=%2d: |ln 2 - Σ_{m<=M} μ(m)F(2^-m)| = %.3e  (bound (16/9)2^-M = %.3e)"
              % (Mtr, float(err), 16 / 9 * 2.0 ** -Mtr))
    for N in (60, 120, 240):
        pref = sum(Fraction(mu[m], 1) * sm1[n] * Fraction(1, 2 ** (m * n))
                   for m in range(1, N + 1) for n in range(1, N // m + 1) if mu[m])
        tay = sum(Fraction(1, k * 2 ** k) for k in range(1, N + 1))
        check(pref == tay, "Euler-product prefix equals Taylor prefix N=%d" % N)
        den = (pref * 2 ** N).denominator
        while den % 2 == 0:
            den //= 2
        primes = [q for q in range(N // 2 + 1, N + 1) if q > 2 and all(q % d for d in range(2, math.isqrt(q) + 1))]
        check(all(den % q == 0 for q in primes), "primes in (N/2,N] divide q_N")
        print("  N=%3d: prefix = Taylor prefix; all %d odd primes in (N/2,N] divide q_N" % (N, len(primes)))

    # ------------------------------------------------------------------ E3
    header("E3. Normal + kernel syntheses (base 2)")
    K = NMAX + 140
    ks = []
    k = 1
    while 3 ** k <= K + 80:
        ks.append(k)
        k += 1
    kmax = ks[-1]
    numa = sum(2 ** (K - 3 ** k) * 3 ** (kmax - k) for k in ks if 3 ** k <= K)
    # terms with 3^k > K contribute < 1 after scaling; the exact numerator below handles all retained terms
    alpha = Enc(2, K, numa // 3 ** kmax, numa // 3 ** kmax + 2)
    pa_ = disc_profile(alpha, NS)
    print("  α_{2,3} (Stoneham): %s" % fmt(pa_))
    pcK = pentagonal_coeffs(K)
    comps = {
        "E_2 (Euler fn)": from_coeffs(2, K, lambda m: pcK[m], -1, 1),
        "Theta_3(1/2)": from_coeffs(2, K, lambda m: (1 if m == 0 else (2 if math.isqrt(m) ** 2 == m else 0)), 0, 2),
        "L_chi4": lambert_enc(2, K, chi4),
    }
    for nm, Z in comps.items():
        pz = disc_profile(Z, NS)
        px = disc_profile(alpha + Z, NS)
        for N in NS:
            check(abs(px[N] - pa_[N]) <= 1 - pz[N] + 4 * 2 ** -40, "sharp translation %s N=%d" % (nm, N))
        print("  α + %-14s %s   (1-D(Z) at %d: %.4f)" % (nm, fmt(px), NMAX, 1 - pz[NMAX]))

    header("Summary")
    if FAILURES:
        print("%d check(s) failed" % len(FAILURES))
        return 1
    print("All exact checks passed.  Discrepancy values are finite measurements.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
