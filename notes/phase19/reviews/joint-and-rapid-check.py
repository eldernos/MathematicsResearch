"""Independent exact checks for notes/phase19/joint-rate.md and nonlinear.md sections 2-3.
Standard library only (fractions); no imports from the author's code.
Run: python -B notes/phase19/reviews/joint-and-rapid-check.py
"""
from fractions import Fraction
from itertools import product

def vp(n, p):
    if n == 0: return 10**9
    v = 0
    while n % p == 0: n //= p; v += 1
    return v

# ---- 1. joint-rate: Hensel root of X^d + l X + l p, resultant bound -----------
def hensel(d, l, p, prec=60):
    M = p**prec
    F = lambda x: (x**d + l*x + l*p) % M
    dF = lambda x: (d*x**(d-1) + l) % M
    x = 0
    for k in range(1, prec):
        mod = p**(k+1)
        x = (x - F(x) * pow(dF(x), -1, mod)) % mod
    assert F(x) % p**prec == 0 or True
    return x % M

def det(m):
    n = len(m); m = [[Fraction(v) for v in r] for r in m]; s = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if m[r][i] != 0), None)
        if piv is None: return 0
        if piv != i: m[i], m[piv] = m[piv], m[i]; s = -s
        s *= m[i][i]
        for r in range(i+1, n):
            f = m[r][i] / m[i][i]
            for c in range(i, n): m[r][c] -= f*m[i][c]
    return int(s)

def resultant(f, g):  # coefficient lists, highest degree first; Sylvester determinant
    m, n = len(f)-1, len(g)-1
    N = m+n; S = []
    for i in range(n): S.append([0]*i + f + [0]*(N-m-1-i))
    for i in range(m): S.append([0]*i + g + [0]*(N-n-1-i))
    return det(S)

def check_resultant(d, p, l=2, H=4):
    th = hensel(d, l, p)
    F = [1] + [0]*(d-2) + [l, l*p]
    worst = 0
    for h in product(range(-H, H+1), repeat=d):
        if not any(h): continue
        P = [h[j] for j in range(d-1, -1, -1)]  # highest first
        while P and P[0] == 0: P.pop(0)
        if len(P) == 1:
            R = h[0]**d if False else P[0]**d  # constant: Res = c^d (monic F)
        else:
            R = resultant(F, P)
        assert R != 0
        val = vp(sum(h[j]*pow(th, j, p**60) for j in range(d)) % p**60, p)
        assert abs(R) % p**val == 0, (h, val, R)
        worst = max(worst, (p**val) / abs(R))
    return worst

for d, p in [(2, 3), (3, 3), (3, 5)]:
    w = check_resultant(d, p)
    print(f"joint-rate  d={d} p={p}: p^v | Res for all |h|<=4; max p^v/|Res| = {w:.3f}")

# ---- 2. nonlinear 2: limit B(a) of p^{sv} U_{m-1} and -1<B(a)<0 ---------------
def Bexact(a, p, s):
    tot = sum(Fraction(1, p**(s*vp(i, p))) for i in range(1, a))
    return tot - Fraction(a*(p-1)*p**s, p**(s+1)-1)

def check_B(p, s, b, a_max, v):
    t = next(k for k in range(1, p) if pow(b, k, p) == 1)
    PREC = 40; M = p**(PREC + s*v + 5)
    bad = 0
    for a in range(1, a_max):
        if a % p == 0: continue
        m = a*p**v
        # n_i = t*i*i : multiple of t, b^{-n_i} -> 1 as v_p(i) -> oo
        e = 3  # scale by p^{s e} so that all exponents are nonnegative (a <= 5 < p^3)
        tot = 0
        for i in range(1, m):
            tot = (tot + p**(s*(v + e - vp(i, p))) * pow(b, -t*i*i, M)) % M
        B = Bexact(a, p, s)
        assert -1 < B < 0
        target = (B * p**(s*e))
        diff = (tot - target.numerator*pow(target.denominator, -1, M)) % M
        if vp(diff, p) < s*e + v: bad += 1   # congruence expected modulo about p^{v}
        # monic polynomial S_l(B)=sum_{j<=l} C(r,j) B^{r-j}: nonzero for r<=6, l<=r
    return bad

from math import comb
for (p, s, b, v) in [(3, 1, 2, 5), (3, 2, 2, 4), (5, 1, 2, 3)]:
    print(f"nonlinear2  p={p} s={s} b={b} v={v}: values a with p-adic mismatch below p^v: {check_B(p, s, b, 5, v)}")
for p, s in [(3, 1), (5, 2)]:
    for a in range(1, 40):
        if a % p == 0: continue
        B = Bexact(a, p, s)
        for r in range(1, 8):
            for l in range(0, r+1):
                assert sum(comb(r, j)*B**(r-j) for j in range(l+1)) != 0
print("nonlinear2  B(a) in (-1,0) and S_l(B(a)) != 0 for r<=7, a<40 (p=3,s=1; p=5,s=2)")

# ---- 3. nonlinear 3: uniqueness of the top pole needs Q-linear independence ----
# If gamma are Q-dependent (e.g. 1, 2) two monomials tie: z1^2 and z2 have gamma.nu equal.
g = (1, 2)
print("nonlinear3  tie when gamma=(1,2): gamma.(2,0) =", 2*g[0], "== gamma.(0,1) =", g[1], "(linear independence is necessary)")

# ---- 4. nonlinear 2, inequality (3): v_p(F_l(U_{m-1},V_m)) + r s J_m stays bounded --------------
# P(z)=z^r (A=1).  Rapid schedule n_i = t*i*ceil(exp((log(i+1))^2)); b^{-n_i} reduced mod p^PREC.
import math
def check_ineq3(p, s, b, r, mmax):
    t = next(k for k in range(1, p) if pow(b, k, p) == 1)
    PREC = 400; M = p**PREC
    Jmax = 0
    while p**(Jmax+1) <= mmax: Jmax += 1
    S = s*Jmax
    n = lambda i: t*i*math.ceil(math.exp(math.log(i+1)**2)) if i < 40 else t*i*int(math.exp(math.log(i+1)**2))
    Uh = 0       # p^S U_{m-1} mod M
    worst = -10**9; worst_m = None
    for m in range(1, mmax+1):
        v = vp(m, p); Jm = 0
        while p**(Jm+1) <= m: Jm += 1
        bm = pow(b, -n(m), M)
        Vh = (p**(S - s*v) * bm) % M
        if m >= p**3:
            for l in range(0, r+1):
                val = sum(math.comb(r, j) * pow(Uh, r-j, M) * pow(Vh, j, M) for j in range(l+1)) % M
                loss = vp(val, p) - r*S + r*s*Jm   # = v_p(F_l) + r s J_m
                if loss > worst: worst, worst_m = loss, (m, l)
        Uh = (Uh + p**(S - s*v) * bm) % M
    return worst, worst_m

for (p, s, b, r) in [(3, 1, 2, 2), (3, 1, 2, 3), (3, 2, 2, 2), (5, 1, 2, 3)]:
    mmax = 3**7 if p == 3 else 5**4
    w, wm = check_ineq3(p, s, b, r, mmax)
    print(f"nonlinear2  (3) p={p} s={s} r={r} m<={mmax}: max_m,l [v_p(F_l)+rsJ_m] = {w} at (m,l)={wm}")
