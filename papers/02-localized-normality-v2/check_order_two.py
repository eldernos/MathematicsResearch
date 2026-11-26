"""Exact arithmetic for Example A.2 of Paper II, version 2.0.

b = 36, S = {2, 3, 7}, order s = 2, cutoff n = 186, selected prime p = 7.
Prints the facts quoted in the paper. Only the standard library is used.

    python check_order_two.py
"""
from fractions import Fraction
from math import isqrt

b, S, s, n, p = 36, (2, 3, 7), 2, 186, 7


def smooth(m, primes):
    for q in primes:
        while m % q == 0:
            m //= q
    return m == 1


def v(q, x):
    """q-adic valuation of a nonzero rational x."""
    x = Fraction(x)
    num, den, k = x.numerator, x.denominator, 0
    while num % q == 0:
        num //= q
        k += 1
    while den % q == 0:
        den //= q
        k -= 1
    return k


indices = [m for m in range(1, n + 1) if smooth(m, S)]
R = sum(Fraction(b ** (n - m), m ** s) for m in indices)

# Facts checked by the Lean declaration order_two_deep_counterexample.
k = 0
while p ** (k + 1) <= n:
    k += 1
assert k == 2                                     # Nat.log 7 186 = 2
assert max(indices) + 16 <= n                     # every index is at least 16 old
assert R.denominator == 7                         # (powerShifted 36 2 {2,3,7} 186).den = 7

# Further arithmetic quoted in the paper (not part of the Lean statement).
print("number of indices:", len(indices))
print("largest index:", max(indices), "age of the largest index:", n - max(indices))
print("denominator of R_{2,186}:", R.denominator)
x = p ** 4 * R / Fraction(b) ** n                 # 7^4 b^{-186} R_{2,186}
print("7^4 b^-186 R mod 7^4:", (x.numerator * pow(x.denominator, -1, p ** 4)) % p ** 4,
      "(4*7^3 = %d)" % (4 * p ** 3))
# Rows of the order-two moment at precision 3 for the cofactors {2,3}:
T = [m for m in range(1, 200) if smooth(m, (2, 3))]
w = pow(pow(b, -1, p ** 3), p ** 2, p ** 3)       # (b^{-1})^{p^{L-1}} mod p^L, L = 3
t = Fraction(n, p ** k)                           # t = 186/49
row0 = sum(pow(m, -2, p ** 3) * pow(w, m, p ** 3) for m in T if m <= t) % p ** 3
row1 = sum(pow(m, -2, p ** 3) * pow(w, m, p ** 3) for m in T if m <= p * t) % p ** 3
print("w mod 343:", w, " row 0:", row0, " p^2 * row 1 mod 343:", (p ** 2 * row1) % p ** 3,
      " moment at precision 3:", (row0 + p ** 2 * row1) % p ** 3)
