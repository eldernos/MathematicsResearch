"""Enclosures of D_N(xi; 2) for xi = sum_k 3^(-v_3(k)) 2^(-2k^3) at N = 2^10, ..., 2^18.

Standard library only. The binary expansion of xi is computed exactly to P = N_max + 192 bits
as an integer X with X <= 2^P xi < X + K + 2 (K = number of terms with 2k^3 <= P). The point
{2^n xi} is then enclosed to within 2^-63 by the 64-bit window of X after bit n. The extreme
discrepancy of the windows is computed exactly with integer arithmetic from the sorted values,

    D_N = max_i (i/N - x_(i)) + max_i (x_(i) - (i-1)/N),        i = 1..N,

and Lemma 2.2 of the paper (with E = 0, epsilon = 2^-63) transfers it to the real orbit with an
additive error of at most 2^-62. The script prints N, D_N and N^(1/3) D_N (rounded outward).

Usage:  python -B papers/07-synthetic-expansions/checks/xi_discrepancy.py
"""
from fractions import Fraction


def v3(k: int) -> int:
    v = 0
    while k % 3 == 0:
        k //= 3
        v += 1
    return v


def windows(n_max: int) -> list[int]:
    P = n_max + 192
    X = 0
    k = 1
    while 2 * k**3 <= P:
        X += (1 << (P - 2 * k**3)) // 3 ** v3(k)
        k += 1
    # bit j of the fraction (1-indexed from the binary point) is bit P - j of X
    out = []
    mask = (1 << 64) - 1
    for n in range(n_max):
        out.append((X >> (P - n - 64)) & mask)
    return out


def extreme_discrepancy_scaled(ws: list[int]) -> Fraction:
    """Exact extreme discrepancy of the points w/2^64."""
    N = len(ws)
    s = sorted(ws)
    S = 1 << 64
    # work with integers: i*S - N*w  and  N*w - (i-1)*S, all over N*S
    plus = max(i * S - N * w for i, w in enumerate(s, start=1))
    minus = max(N * w - (i - 1) * S for i, w in enumerate(s, start=1))
    return Fraction(plus + minus, N * S)


def main() -> None:
    n_max = 1 << 18
    ws = windows(n_max)
    err = Fraction(1, 1 << 62)
    print("N        D_N (enclosure)            N^(1/3) D_N (enclosure)")
    for e in range(10, 19):
        N = 1 << e
        D = extreme_discrepancy_scaled(ws[:N])
        lo, hi = D - err, D + err
        # N^(1/3) = 2^(e/3); bound by exact rational powers via float with outward margin
        c = 2 ** (e / 3)
        print(f"2^{e:<2}  [{float(lo):.8f}, {float(hi):.8f}]   "
              f"[{float(lo) * c * (1 - 1e-12):.5f}, {float(hi) * c * (1 + 1e-12):.5f}]")


if __name__ == "__main__":
    main()
