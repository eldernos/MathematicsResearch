# Independent check of the Phase 18 even-Legendre odd-grid pi construction.
from fractions import Fraction as F
from math import comb, gcd, log, log2, sqrt
import sys
sys.set_int_max_str_digits(0)

def pi_fixed(bits):
    # pi * 2^bits via Machin with integer arithmetic, guard bits; returns integer approx with |err|<=4
    g = 40; B = bits + g; one = 1 << B
    def atan_inv(x):
        s = 0; t = one // x; k = 0; x2 = x*x
        while t:
            s += t // (2*k+1) if k % 2 == 0 else -(t // (2*k+1))
            t //= x2; k += 1
        return s
    return (16*atan_inv(5) - 4*atan_inv(239)) >> g

def legendre_even_H(D):
    # H_D(y) = P_{2D}(sqrt y); coefficients list c[m] for y^m, m=0..D
    n = 2*D
    c = [F(0)]*(D+1)
    for k in range(D+1):
        c[D-k] = F((-1)**k * comb(n, k) * comb(2*n-2*k, n), 2**n)
    return c

def H_eval(c, y):
    s = F(0)
    for a in reversed(c): s = s*y + a
    return s

def quotient(c, root):  # (H(y)-H(root))/(y-root) via synthetic division
    D = len(c)-1; q = [F(0)]*D; acc = F(0)
    for m in range(D, 0, -1):
        acc = acc*root + c[m]; q[m-1] = acc
    return q

def run(ident, n, check=True):
    D = 1; cache = {}
    while True:
        c = legendre_even_H(D)
        hs = [H_eval(c, -a*a) for (_, a) in ident]
        if min(abs(h) for h in hs) >= 2**n: break
        D += 1
    # integral of R_D(x^2)
    I = F(0)
    for (ci, a), h in zip(ident, hs):
        q = quotient(c, F(-a*a))
        I += F(ci*a) / h * sum(qm / (2*m+1) for m, qm in enumerate(q))
    L = 1
    for j in range(1, 2*D, 2): L = L*j // gcd(L, j)
    u = L * 2**n * I
    num = -round(u)   # Python rounds half to even; tie never hit here in practice
    Y = F(num, L)
    qn = Y.denominator
    res = dict(n=n, D=D, Lbits=L.bit_length(), qbits=qn.bit_length(), odd=qn % 2 == 1)
    if check:
        P = 4*(n + L.bit_length() + 80)
        pin = F(pi_fixed(P), 2**P)  # pi within 2^-P * ~5
        err = abs(F(2**n)*pin - Y)
        res['log2err'] = log2(err) if err else None
        # nearest grid comparison
        ng = round(L * 2**n * pin)
        res['nearest_grid'] = (ng == num)
        # analytic part: 2^n pi + 2^n I
        an = abs(2**n*pin + 2**n*I)
        res['log2analytic'] = log2(an) if an else None
        res['log2_rho_pred'] = -2*D*log2(min(a for _, a in ident) + sqrt(min(a for _, a in ident)**2+1))
    return res

machin = [(16,5),(-4,239)]
stormer = [(24,8),(8,57),(4,239)]
euler = [(4,2),(4,3)]

if __name__ == '__main__':
    from math import gcd
    from sympy import factorint, n_order   # only for the period comparison
    def lcm(a, b): return a*b//gcd(a, b)
    for name, ident in [('euler', euler), ('machin', machin), ('stormer', stormer)]:
        for n in [10, 40, 100, 600]:
            print(name, run(ident, n))
    for name, ident in [('euler', euler), ('machin', machin), ('stormer', stormer)]:
        agree = 0; worst = 1e9
        for n in range(1, 301):
            r = run(ident, n); agree += r['nearest_grid']
            worst = min(worst, -r['log2err'] - (r['Lbits'] - 1))
        print(name, 'n=1..300 nearest-grid agreement', agree, '/ 300; min(-log2 err - log2 L_D) =', round(worst, 2))
    for name, ident, n in [('machin', machin, 100), ('machin', machin, 600), ('euler', euler, 600)]:
        D = run(ident, n, check=False)['D']
        c = legendre_even_H(D); hs = [H_eval(c, -a*a) for _, a in ident]
        I = sum(F(ci*a)/h*sum(qm/(2*m+1) for m, qm in enumerate(quotient(c, F(-a*a))))
                for (ci, a), h in zip(ident, hs))
        L = 1
        for j in range(1, 2*D, 2): L = lcm(L, j)
        q = F(-round(L*2**n*I), L).denominator
        o = 1
        for p, k in factorint(q).items(): o = lcm(o, n_order(2, p**k))
        print(name, 'n', n, 'D', D, 'log2 q', round(log2(q), 1), 'log2 ord_q(2)', round(log2(o), 1))
