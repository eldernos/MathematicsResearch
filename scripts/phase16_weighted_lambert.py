#!/usr/bin/env python3
"""Exact Phase 16 verification for Track 2: Weighted Lambert series for ln 2
and signed integer multiplicative Lambert series.

Verifies:
1. Exact Mobius inversion sum_{m|n} a_m = 1/n up to n = 2000, non-cancellation at P^+(m),
   and exact prime cancellations (e.g., a_21 = 4/7, a_42 = -2/7).
2. Exact finite Lambert-Taylor identity H_N^Lam = R_N, prime-band correspondence
   a_p * 2^{N-p} === 2^{N-p}/p (mod 1) for p in (N/2, N], and exact odd-denominator lower bound.
3. Empirical mean and variance of v_2(a_m) on odd m <= 200,000 vs 2 log log x and
   the sharp finite-x variance 6 log log x + C_2 - sum v_2(p-1)^2/p^2 - 2*pi^2/3.
4. Exact convolution identities, zero loci, 2-adic valuations, and certified binary digit
   statistics for integer signed multiplicative Lambert series:
   - L_{chi_4} = sum chi_4(m)/(2^m - 1) = sum (r_2(n)/4) 2^{-n}  (1-frequency -> 0, disjunctive)
   - L_{(-1)^omega} = sum (-1)^{omega(m)}/(2^m - 1)  (powerful support, 0 transitions)
   - L_{m a_m} = sum (m a_m)/(2^m - 1)  (zero 2-adic drift, linear growth)
   - L_{f_sym} = sum f_sym(m)/(2^m - 1)  (signed full-density positive drift, symmetric model).
"""

from __future__ import annotations

import math
from fractions import Fraction


def sieve_spf(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    for i in range(2, int(limit**0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factorize(n: int, spf: list[int]) -> list[tuple[int, int]]:
    res = []
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        res.append((p, e))
    return res


def v2(n: int) -> int:
    if n == 0:
        return -1
    n = abs(n)
    return (n & -n).bit_length() - 1


def a_coeff(m: int, spf: list[int]) -> Fraction:
    num = 1
    for p, _ in factorize(m, spf):
        num *= (1 - p)
    return Fraction(num, m)


def check_mobius_and_denominators(spf: list[int]):
    print("=== 1. Exact Mobius Inversion & Denominator Structure of a_m ===")
    N_check = 2000
    a_vals = [Fraction(0)] * (N_check + 1)
    for m in range(1, N_check + 1):
        a_vals[m] = a_coeff(m, spf)
        if m >= 2:
            facs = factorize(m, spf)
            p_max, e_max = facs[-1]
            # P^+(m)^{v_{P^+}(m)} || den(a_m)
            den = a_vals[m].denominator
            assert den % (p_max**e_max) == 0 and den % (p_max ** (e_max + 1)) != 0
            # |a_m| < 1
            assert abs(a_vals[m]) < 1
            # Sign (-1)^{omega(m)}
            assert (a_vals[m] > 0) == (len(facs) % 2 == 0)
            # Even factorization a_{2^e u} = -2^{-e} a_u
            if facs[0][0] == 2:
                e2 = facs[0][1]
                u = m >> e2
                assert a_vals[m] == -Fraction(1, 1 << e2) * a_vals[u]

    assert a_vals[21] == Fraction(4, 7)
    assert a_vals[42] == Fraction(-2, 7)

    # Verify sum_{m | n} a_m = 1/n for all 1 <= n <= 2000
    conv = [Fraction(0)] * (N_check + 1)
    for m in range(1, N_check + 1):
        am = a_vals[m]
        for n in range(m, N_check + 1, m):
            conv[n] += am
    for n in range(1, N_check + 1):
        assert conv[n] == Fraction(1, n), f"Mobius failed at n={n}"
    print(f"  Verified sum_{{m|n}} a_m = 1/n, P^+(m) non-cancellation, sign, and |a_m| < 1 for 1..{N_check}.")
    print(f"  Small-prime cancellation examples: a_21 = {a_vals[21]}, a_42 = {a_vals[42]}.")


def check_lambert_taylor_identities(spf: list[int]):
    print("\n=== 2. Lambert-Taylor Head Identity & Prime-Band Correspondence ===")
    for N in (16, 37, 64, 100):
        # Compute H_N^Lam = sum_{m=1}^N a_m sum_{r=1}^{floor(N/m)} 2^{N - m*r}
        H_lam = Fraction(0)
        for m in range(1, N + 1):
            am = a_coeff(m, spf)
            s = sum(1 << (N - m * r) for r in range(1, N // m + 1))
            H_lam += am * s
        # Compute R_N = sum_{n=1}^N 2^{N-n}/n
        R_N = sum(Fraction(1 << (N - n), n) for n in range(1, N + 1))
        assert H_lam == R_N
        # Verify prime-band identity a_p * 2^{N-p} === 2^{N-p}/p (mod 1) for p in (N/2, N]
        for p in range(N // 2 + 1, N + 1):
            if spf[p] == p:
                lhs = a_coeff(p, spf) * (1 << (N - p))
                rhs = Fraction(1 << (N - p), p)
                diff = lhs - rhs
                assert diff.denominator == 1, f"Non-integer diff at N={N}, p={p}"
        # Verify odd primes p in (N/3, N] \ {5} divide den(R_N)
        den_odd = R_N.denominator >> v2(R_N.denominator)
        for p in range(N // 3 + 1, N + 1):
            if spf[p] == p and p != 2 and p != 5:
                assert den_odd % p == 0, f"Expected p={p} | den_odd(R_{N})"

    # Verify Lambert vs Taylor truncation oscillation 2^N (L_N - S_N) at N = 60, 66 (67 prime)
    for N in (60, 66):
        # 2^N (L_N - S_N) = sum_{m=1}^N a_m * 2^{N % m} / (2^m - 1)
        # Approximate using float to high precision for display, exact sum for m <= N
        diff_float = sum(float(a_coeff(m, spf)) * (2.0 ** (N % m)) / (2.0**m - 1.0) for m in range(1, N + 1))
        # Compare with 1/(N+1) - sum_{k=1}^{40} a_{N+k} 2^{-k}
        tail_rhs = 1.0 / (N + 1) - sum(float(a_coeff(N + k, spf)) * (2.0 ** (-k)) for k in range(1, 41))
        assert abs(diff_float - tail_rhs) < 1e-3
        print(f"  N={N} (N+1={N+1}): 2^N(L_N - S_N) = {diff_float:+.6f} (tail formula = {tail_rhs:+.6f})")
    print("  Verified H_N^Lam = R_N, prime-band congruence, and odd-prime survival in (N/3, N]\\{5}.")


def check_v2_distribution(spf: list[int]):
    print("\n=== 3. Exact Distribution of v_2(a_m) on Odd m <= 200,000 ===")
    X = 200_000
    # Compute W(m) = sum_{p|m, p>2} v_2(p-1) via sieve
    W = [0] * (X + 1)
    primes_odd = [p for p in range(3, X + 1) if spf[p] == p]
    for p in primes_odd:
        vp2 = v2(p - 1)
        for m in range(p, X + 1, p):
            W[m] += vp2

    odd_vals = [W[m] for m in range(1, X + 1, 2)]
    n_odd = len(odd_vals)
    mean_emp = sum(odd_vals) / n_odd
    var_emp = sum((w - mean_emp) ** 2 for w in odd_vals) / n_odd

    # Exact prime sums A(X) and B(X)^2
    A_X = sum(v2(p - 1) / p for p in primes_odd)
    B2_X = sum((v2(p - 1) ** 2) / p for p in primes_odd)
    sq_corr = sum((v2(p - 1) ** 2) / (p * p) for p in primes_odd)
    llx = math.log(math.log(X))
    # Missing-corner correction: sum_{p,q <= X, pq > X} v_2(p-1)v_2(q-1)/(pq) ~ 2*pi^2/3
    # Compute exact finite-X variance prediction from prime sums + corner term:
    # Actually we can compute exact corner sum using prefix sums of v2(p-1)/p!
    # For each prime p, find sum_{q > X/p, q <= X} v2(q-1)/q
    pref = [0.0] * (X + 1)
    s = 0.0
    p_idx = 0
    for i in range(1, X + 1):
        if p_idx < len(primes_odd) and primes_odd[p_idx] == i:
            s += v2(i - 1) / i
            p_idx += 1
        pref[i] = s
    corner = 0.0
    for p in primes_odd:
        cut = X // p
        if cut < X:
            corner += (v2(p - 1) / p) * (pref[X] - pref[cut])
    var_pred = B2_X - sq_corr - corner

    # Exact finite-X odd-multiple expectation vs continuous prime sum A(X)
    exact_odd_mean = sum(v2(p - 1) * (((X // p) + 1) // 2) for p in primes_odd) / n_odd
    print(f"  X = {X:,}, log log X = {llx:.5f}")
    print(f"  2*log log X = {2*llx:.5f}, prime sum A(X) = {A_X:.5f}, exact odd-mult = {exact_odd_mean:.5f}, empirical mean = {mean_emp:.5f}")
    print(f"  6*log log X = {6*llx:.5f}, B(X)^2 = {B2_X:.5f}, corner = {corner:.5f} (asymptotic 2*pi^2/3 = {2*math.pi**2/3:.5f})")
    print(f"  Finite-X predicted variance = {var_pred:.5f}, empirical variance = {var_emp:.5f}")
    assert abs(mean_emp - exact_odd_mean) < 1e-12
    assert abs(mean_emp - A_X) < 0.06  # O(1 / log X) rounding bias from odd multiples in (X/3, X]
    assert abs(var_emp - var_pred) < 0.15


def exact_binary_bits_from_coeffs(c: list[int], max_pos: int, tail_bound_fn) -> tuple[list[int], int]:
    """Compute exact certified binary digits b_1..b_{max_pos} of sum_{n>=1} c[n] 2^{-n}
    where |sum_{n > M} c[n] 2^{M - n}| <= tail_bound_fn(M).
    Propagates exact integer lower/upper endpoints backward from M.
    """
    M = len(c) - 1
    tb = tail_bound_fn(M)
    # Scaled by 2^M: true sum = sum_{n=1}^M c[n] 2^{M-n} + rem, |rem| <= tb
    # Compute integer interval [lo, hi] at position M
    # We propagate backward: at step n from M down to 1, fractional part is (c[n] + carry) / 2
    lo = -tb
    hi = tb
    # Actually forward/backward with exact big ints is super fast up to M = 65536 using block carry!
    # Let's use exact big integer? For M = 65536, big int is 65536 bits = 8KB, super fast in Python!
    # Wait: building sum c[n] 2^{M-n} with divide-and-conquer or word-packing is O(M)!
    # Even simpler: maintain a signed integer carry from right to left!
    # At index n (from M down to 1):
    #   tot_lo = c[n] + lo_carry,  bit_lo = tot_lo & 1,  lo_carry = tot_lo >> 1
    #   tot_hi = c[n] + hi_carry,  bit_hi = tot_hi & 1,  hi_carry = tot_hi >> 1
    # Wait: if lo_carry == hi_carry at some position k, then ALL bits 1..k are 100% CERTIFIED EXACT!
    lo_c = -tb
    hi_c = tb
    bits = [0] * (M + 1)
    first_uncertain = M + 1
    for n in range(M, 0, -1):
        t_lo = c[n] + lo_c
        t_hi = c[n] + hi_c
        b_lo = t_lo & 1
        b_hi = t_hi & 1
        lo_c = t_lo >> 1
        hi_c = t_hi >> 1
        if b_lo == b_hi and lo_c == hi_c:
            bits[n] = b_lo
        else:
            bits[n] = b_lo
            first_uncertain = min(first_uncertain, n)
    certified_up_to = min(max_pos, first_uncertain - 1)
    return bits, certified_up_to


def check_integer_lambert_regimes(spf: list[int]):
    print("\n=== 4. Four-Regime Integer Signed Multiplicative Lambert Series ===")
    M = 132096  # certify through 2^17 = 131072 with 1024 guard bits for powerful-number gaps
    N_cert = 131072

    # (a) chi_4: c_{chi_4}(n) = r_2(n)/4 = prod_{p^e || n} (e+1 if p=1(4), (1+(-1)^e)/2 if p=3(4), 1 if p=2)
    c_chi4 = [0] * (M + 1)
    for n in range(1, M + 1):
        val = 1
        for p, e in factorize(n, spf):
            if p == 2:
                continue
            elif p % 4 == 1:
                val *= (e + 1)
            else:
                if e % 2 == 1:
                    val = 0
                    break
        c_chi4[n] = val
    # Verify convolution (chi_4 * 1) = c_chi4 for n <= 500
    for n in range(1, 501):
        conv_n = sum((0 if d % 2 == 0 else (1 if d % 4 == 1 else -1)) for d in range(1, n + 1) if n % d == 0)
        assert conv_n == c_chi4[n]
    bits_chi4, cert_chi4 = exact_binary_bits_from_coeffs(c_chi4, N_cert, lambda m: m + 2)
    assert cert_chi4 >= N_cert
    print("  L_{chi_4} (c(n) = r_2(n)/4): certified 1-frequency across dyadic shells:")
    for k in range(10, 17):
        lo, hi = 1 << k, 1 << (k + 1)
        ones = sum(bits_chi4[lo:hi])
        freq = ones / (hi - lo)
        # Compare with Landau-Ramanujan scale 1/sqrt(log N)
        lr_scale = freq * math.sqrt(math.log(lo))
        print(f"    [2^{k:2d}, 2^{k+1:2d}): 1-freq = {freq:.5f}, freq*sqrt(log N) = {lr_scale:.4f}")

    # (b) f(m) = (-1)^{omega(m)}: c(p^e) = 1 - e, supported ONLY on powerful numbers!
    c_alt = [0] * (M + 1)
    powerful_count = 0
    for n in range(1, M + 1):
        val = 1
        for _, e in factorize(n, spf):
            val *= (1 - e)
            if val == 0:
                break
        c_alt[n] = val
        if val != 0:
            powerful_count += 1
    for n in range(1, 301):
        conv_n = sum(((-1) ** len(factorize(d, spf))) for d in range(1, n + 1) if n % d == 0)
        assert conv_n == c_alt[n]
    bits_alt, cert_alt = exact_binary_bits_from_coeffs(c_alt, N_cert, lambda m: m + 2)
    assert cert_alt >= N_cert
    trans_alt = sum(1 for i in range(1, N_cert) if bits_alt[i] != bits_alt[i + 1])
    print(f"  L_{{(-1)^omega}}: powerful count <= {M} is {powerful_count} (~ {math.sqrt(M)*2.173:.1f});")
    print(f"    transitions in first {N_cert} bits = {trans_alt} (density = {trans_alt/N_cert:.5f} -> 0)")

    # (c) g(m) = m * a_m = prod_{p|m}(1-p): c_g(n) = prod_{p^e||n} (1 + e(1-p))
    c_g = [0] * (M + 1)
    zero_cnt = 0
    odd_cnt = 0
    for n in range(1, M + 1):
        val = 1
        for p, e in factorize(n, spf):
            val *= (1 + e * (1 - p))
        c_g[n] = val
        assert abs(val) <= n
        assert (val == 0) == (n % 4 == 2)
        if val == 0:
            zero_cnt += 1
        elif val % 2 != 0:
            odd_cnt += 1
    for n in range(1, 301):
        conv_n = sum(math.prod(1 - p for p, _ in factorize(d, spf)) for d in range(1, n + 1) if n % d == 0)
        assert conv_n == c_g[n]
    bits_g, cert_g = exact_binary_bits_from_coeffs(c_g, N_cert, lambda m: 2 * m + 4)
    assert cert_g >= N_cert
    ones_g = sum(bits_g[1 : N_cert + 1])
    trans_g = sum(1 for i in range(1, N_cert) if bits_g[i] != bits_g[i + 1])
    print(f"  L_{{m a_m}}: exact zero frac = {zero_cnt/M:.5f} (1/4), odd frac = {odd_cnt/M:.5f} (2/3);")
    print(f"    first {N_cert} bits: 1-freq = {ones_g/N_cert:.5f}, transition frac = {trans_g/N_cert:.5f}")

    # (d) f_sym: f(2^e)=2 (e>=1), f(p)=-3, f(p^e)=0 (e>=2) -> c_sym(2^e u) = (2e+1)(-2)^{omega(u)}
    c_sym = [0] * (M + 1)
    for n in range(1, M + 1):
        facs = factorize(n, spf)
        e2 = facs[0][1] if (facs and facs[0][0] == 2) else 0
        omega_odd = len(facs) - (1 if e2 > 0 else 0)
        c_sym[n] = (2 * e2 + 1) * ((-2) ** omega_odd)
    for n in range(1, 301):
        def fsym(d):
            val = 1
            for p, e in factorize(d, spf):
                if p == 2:
                    val *= 2
                elif e == 1:
                    val *= -3
                else:
                    return 0
            return val
        assert sum(fsym(d) for d in range(1, n + 1) if n % d == 0) == c_sym[n]
    bits_sym, cert_sym = exact_binary_bits_from_coeffs(c_sym, N_cert, lambda m: 2 * m + 4)
    assert cert_sym >= N_cert
    ones_sym = sum(bits_sym[65536:131072])
    trans_sym = sum(1 for i in range(65536, 131071) if bits_sym[i] != bits_sym[i + 1])
    print(f"  L_{{f_sym}} on [2^16, 2^17): 1-freq = {ones_sym/65536:.5f}, transition frac = {trans_sym/65536:.5f}")


def main():
    spf = sieve_spf(200_005)
    check_mobius_and_denominators(spf)
    check_lambert_taylor_identities(spf)
    check_v2_distribution(spf)
    check_integer_lambert_regimes(spf)
    print("\nAll Phase 16 Track 2 weighted Lambert checks passed.")


if __name__ == "__main__":
    main()
