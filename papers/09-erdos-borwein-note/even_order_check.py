"""Exact-arithmetic check of Proposition 7.2 (even-order sharpness of the parity bound).

For even r and integers L > r, build the law  sum_{n<=s} u_n delta_n + eps delta_L  (s = r-1) with
eps = 1/(L)_r and u_n = w_n - (1/n!) sum_{k=n}^{s} (-1)^(k-n)/(k-n)! * delta_k, delta_k = eps*(L)_k,
and verify in exact rational arithmetic: total mass 1, E(N)_k = 1 for 1 <= k <= r, all weights > 0,
and that E(-1)^N exceeds e_s = sum_{k<=s} (-2)^k/k! by a positive amount of order 1/L.
Run:  python -B papers/09-erdos-borwein-note/even_order_check.py
"""
from fractions import Fraction as F
from math import factorial


def ff(n, k):
    out = 1
    for i in range(k):
        out *= n - i
    return out


def partial_exp_minus_one(m):
    return sum(F((-1) ** j, factorial(j)) for j in range(m + 1))


def e_odd(s):
    return sum(F((-2) ** k, factorial(k)) for k in range(s + 1))


def construct(r, L):
    s = r - 1
    eps = F(1, ff(L, r))
    u = []
    for n in range(s + 1):
        w = F(1, factorial(n)) * partial_exp_minus_one(s - n)
        corr = sum(F((-1) ** (k - n), factorial(n) * factorial(k - n)) * eps * ff(L, k)
                   for k in range(n, s + 1))
        u.append(w - corr)
    return u, eps


def main():
    for r in (2, 4, 6, 8, 10, 12):
        s = r - 1
        for L in (10 ** 2, 10 ** 3, 10 ** 5):
            u, eps = construct(r, L)
            assert sum(u) + eps == 1
            for k in range(1, r + 1):
                assert sum(u[n] * ff(n, k) for n in range(s + 1)) + eps * ff(L, k) == 1, (r, L, k)
            assert all(x > 0 for x in u) and eps > 0, (r, L)
            parity = sum(u[n] * (-1) ** n for n in range(s + 1)) + eps * (-1) ** L
            excess = parity - e_odd(s)
            assert excess > 0                      # the bound e_s is never attained
            print("r=%2d L=%6d  excess over e_%d = %.3e   L*excess = %.4f" % (r, L, s, float(excess), float(excess * L)))
    # the unique vanishing weight of the odd-order primal law is w_{r-2}
    for r in (2, 4, 6, 8, 10, 12):
        s = r - 1
        w = [F(1, factorial(n)) * partial_exp_minus_one(s - n) for n in range(s + 1)]
        assert [n for n in range(s + 1) if w[n] == 0] == [r - 2]
    print("even-order check: all assertions passed")


if __name__ == "__main__":
    main()
