#!/usr/bin/env python3
"""Exact Phase 16 verification for Track 6: independent-prime product alpha(2,3)*alpha(2,5).

Verifies:
1. Exact Mahler/Newton decay v_p(Delta^k g(0)) >= k + 1 and agreement with direct summation.
2. High-precision Hensel lifting of zeta_{3,a,b} (mod 3^55) and zeta_{5,b,a} (mod 5^42).
3. Exact single-shape maximum relative length (4/11 at (1,1), <= 2/13 for all other shapes).
4. Analytic fixed-axis separation v_3(zeta_{3,a,b1} - zeta_{3,a,b2}) = b1 - 1 and
   v_5(zeta_{5,b,a1} - zeta_{5,b,a2}) = a1 - 1.
5. Finite non-coincidence certificates yielding unconditional upper bounds on D_infty(x)
   down to 4/11 + 2.85e-10 (slashing Phase 14's 0.37048).
6. Modest-depth (2,2), (3,3) separation diagnostics and actual shell-loss scan up to K = 200,000.
7. Base-variation derivative test for beta = 2*exp(3t) (unit derivative at beta = 2 vs
   degeneracy at beta = 5 mod 9).
"""

from __future__ import annotations

import math
from fractions import Fraction


def vp(n: int, p: int) -> int:
    """Exact p-adic valuation of nonzero integer n (returns -1 for 0)."""
    if n == 0:
        return -1
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def x_term_mod(j: int, p: int, q: int, mod: int, phi_mod: int) -> int:
    """Compute x_j = q^{-j} * 2^{-q^j} mod p^D (where mod = p^D, phi_mod = p^{D-1}(p-1))."""
    q_inv_j = pow(q, -j, mod)
    exp2 = pow(q, j, phi_mod)
    two_inv_qj = pow(2, -exp2, mod)
    return (q_inv_j * two_inv_qj) % mod


def S_direct_mod(m: int, p: int, q: int, D: int) -> int:
    """Direct sum S_m = sum_{j=1}^m q^{-j} 2^{-q^j} mod p^D."""
    mod = p ** D
    phi_mod = (p - 1) * (p ** (D - 1))
    total = 0
    for j in range(1, m + 1):
        total = (total + x_term_mod(j, p, q, mod, phi_mod)) % mod
    return total


def build_mahler_coeffs(p: int, q: int, u: int, D: int) -> list[int]:
    """Compute Delta^k g(0) mod p^D for k = 0..D-2 where g(z) = S_{u(z+1)} - S_{uz}.

    Since v_p(Delta^k g(0)) >= k + 1, truncating at k = D - 2 is exact modulo p^D!
    Uses the finite difference table of g(0), g(1), ..., g(D-2) mod p^D.
    """
    mod = p ** D
    phi_mod = (p - 1) * (p ** (D - 1))
    # Compute g(z) = sum_{i=1}^u x_{i + u*z} mod p^D for z = 0..D-2
    n_pts = max(1, D - 1)
    vals = []
    for z in range(n_pts):
        s = 0
        base = u * z
        for i in range(1, u + 1):
            s = (s + x_term_mod(base + i, p, q, mod, phi_mod)) % mod
        vals.append(s)
    # Forward difference table
    coeffs = []
    cur = vals
    for k in range(n_pts):
        coeffs.append(cur[0] % mod)
        if k + 1 < n_pts:
            cur = [(cur[i + 1] - cur[i]) % mod for i in range(len(cur) - 1)]
    return coeffs


def binom_p_adic_mod(z: int, r: int, p: int, D: int) -> int:
    """Compute C(z, r) = z(z-1)...(z-r+1) / r! as a p-adic integer mod p^D."""
    # Since r! can have p-factors, track exact p-valuation of numerator & denominator
    v_den = 0
    den_unit = 1
    mod = p ** D
    for i in range(1, r + 1):
        t = i
        while t % p == 0:
            t //= p
            v_den += 1
        den_unit = (den_unit * t) % mod

    v_num = 0
    num_unit = 1
    # Need extra precision in z? No, z is an exact integer (or residue mod p^{D + v_den})
    for i in range(r):
        val = z - i
        if val == 0:
            return 0
        while val % p == 0:
            val //= p
            v_num += 1
        num_unit = (num_unit * val) % mod

    assert v_num >= v_den, f"Unexpected negative valuation for C({z}, {r})"
    diff = v_num - v_den
    if diff >= D:
        return 0
    inv_den = pow(den_unit, -1, mod)
    return (num_unit * inv_den * pow(p, diff, mod)) % mod


class MahlerEvaluator:
    """Exact p-adic evaluator for S_{uz} and G_{a,b}(a + uz) modulo p^D."""

    def __init__(self, p: int, q: int, u: int, D: int):
        self.p = p
        self.q = q
        self.u = u
        self.D = D
        self.mod = p ** D
        self.phi_mod = (p - 1) * (p ** (D - 1))
        self.coeffs = build_mahler_coeffs(p, q, u, D)
        # Verify exact Mahler decay v_p(Delta^k g(0)) >= k + 1!
        for k, c in enumerate(self.coeffs):
            if c != 0:
                val = vp(c, p)
                assert val >= k + 1, f"Mahler decay failed at p={p}, k={k}: v_p={val}"

    def S_uz(self, z: int, prec: int | None = None) -> int:
        """Evaluate S_{uz} mod p^prec using Newton series sum_{k=0}^{prec-2} Delta^k g(0) C(z, k+1).

        Notice that since v_p(Delta^k g(0)) >= k + 1, C(z, k+1) is multiplied by at least p^{k+1},
        so we only need C(z, k+1) mod p^{prec - (k+1)}, and for nonnegative integer z the binomial
        coefficient is an ordinary integer! Even better, we can pass z as a nonnegative integer
        (representing z in Z_p mod p^{prec + ...}).
        """
        if prec is None:
            prec = self.D
        assert prec <= self.D
        mod = self.p ** prec
        p = self.p
        total = 0
        # Maintain C(z, k+1) incrementally via numerator/denominator p-valuation!
        # For r = 1..prec-1: C(z, r) = prod_{i=0}^{r-1} (z - i) / r!
        # Since Delta^{r-1} g(0) has v_p >= r, we need C(z, r) mod p^{prec - r}.
        # Using z >= 0 (an ordinary integer, e.g., the canonical residue in [0, p^{prec})):
        # wait: C(z, r) as a rational depends on z mod p^{prec - r + v_p(r!)}!
        # Wait: if z is only known mod p^{prec-1}, does S_{uz} mod p^prec depend ONLY on z mod p^{prec-1}?
        # YES! Because S_{u(z + p^{prec-1})} - S_{uz} === 0 (mod p^prec) by the isometry theorem!
        # Let's compute C(z, r) using exact integer arithmetic when z >= 0!
        # Wait: to avoid huge integers when z ~ p^55, compute C(z, r) mod p^{prec - r} directly!
        v_num = 0
        num_unit = 1
        v_den = 0
        den_unit = 1
        # Work mod p^prec for the unit parts (more than enough since we never need > prec)
        for k in range(prec - 1):
            r = k + 1
            term_z = z - k
            if term_z == 0:
                break
            while term_z % p == 0:
                term_z //= p
                v_num += 1
            num_unit = (num_unit * term_z) % mod

            t = r
            while t % p == 0:
                t //= p
                v_den += 1
            den_unit = (den_unit * t) % mod

            c = self.coeffs[k]
            if c == 0:
                continue
            diff = v_num - v_den
            # c already divisible by p^{k+1}, so total valuation is v_p(c) + diff
            if diff >= prec:
                continue
            inv_den = pow(den_unit, -1, mod)
            binom_mod = (num_unit * inv_den * pow(p, diff, mod)) % mod
            total = (total + c * binom_mod) % mod
        return total

    def G_ab(self, a: int, b: int, z: int, prec: int | None = None) -> int:
        """Evaluate G_{a,b}(a + u*z) mod p^prec for a >= 1, b >= 1.

        Recall:
          m = a + u*z, so m - a = u*z.
          G_{a,b}(m) = S_{m-a} + p * (S_{m-1} - S_{m-a}) + p^b * x_m
                     = S_{uz} + p * sum_{r=1}^{a-1} x_{uz + r} + p^b * x_{uz + a}.
        """
        if prec is None:
            prec = self.D
        mod = self.p ** prec
        phi_mod = (self.p - 1) * (self.p ** (prec - 1))
        val = self.S_uz(z, prec)
        uz = self.u * z
        if a > 1:
            mid = 0
            for r in range(1, a):
                mid = (mid + x_term_mod(uz + r, self.p, self.q, mod, phi_mod)) % mod
            val = (val + self.p * mid) % mod
        if b < prec:
            last = x_term_mod(uz + a, self.p, self.q, mod, phi_mod)
            val = (val + pow(self.p, b, mod) * last) % mod
        return val

    def find_zero(self, a: int, b: int, target_digits: int) -> int:
        """Hensel lift the unique zero zeta_{p,a,b} mod p^{target_digits}.

        Recall v_p(G_{a,b}(a + u*z)) = 1 + v_p(z - zeta_{p,a,b}).
        So G_{a,b}(a + u*z) === 0 (mod p^{t+1}) determines z mod p^t uniquely!
        """
        assert target_digits + 1 <= self.D
        p = self.p
        # Step t = 1: find z in {0, ..., p-1} with G_{a,b}(a + u*z) === 0 (mod p^2)
        z = None
        for cand in range(p):
            if self.G_ab(a, b, cand, prec=2) == 0:
                assert z is None, "Multiple roots mod p!"
                z = cand
        assert z is not None, f"No root found mod {p} for ({a},{b})"

        # At each step, we know G(z) === 0 (mod p^{t+1}), and
        # G(z + c * p^t) === G(z) + c * p^t * S_u (mod p^{t+2}).
        # Since S_u / p is a fixed unit (6/3=2 mod 3 for p=3; 15/5=3 mod 5 for p=5),
        # we can lift linearly one digit at a time!
        su_unit = (S_direct_mod(self.u, p, self.q, 2) // p) % p
        su_inv = pow(su_unit, -1, p)

        p_pow = p
        for t in range(1, target_digits):
            # Evaluate G(z) mod p^{t+2}
            g_val = self.G_ab(a, b, z, prec=t + 2)
            assert g_val % (p_pow * p) == 0, f"Lift invariant broke at t={t}"
            digit_err = (g_val // (p_pow * p)) % p
            c = (-digit_err * su_inv) % p
            z += c * p_pow
            p_pow *= p
        # Final verification
        assert self.G_ab(a, b, z, prec=target_digits + 1) == 0
        return z


def exact_single_shape_max(a: int, b: int) -> tuple[Fraction, Fraction]:
    """Compute exact supremum of relative length (V(r)-U(r))/V(r) for single shape (a,b).

    For r = Q/P in (1/5, 3):
      U(r) = max(1 + r/5^a, r + 1/3^b)
      V(r) = min(1 + r/5^{a-1}, r + 1/3^{b-1}, 3, 5r)
    Since U(r) is convex piecewise linear and V(r) is concave piecewise linear,
    (V(r) - U(r))/V(r) = 1 - U(r)/V(r) is maximized at a breakpoint of U or V!
    """
    A1 = Fraction(1, 5 ** a)
    A0 = Fraction(1, 5 ** (a - 1))
    B1 = Fraction(1, 3 ** b)
    B0 = Fraction(1, 3 ** (b - 1))

    # All candidate breakpoints for r > 0:
    # U breakpoint: 1 + A1*r = r + B1  => r = (1 - B1) / (1 - A1)
    cands = [Fraction(1, 5), Fraction(3, 1)]
    cands.append((1 - B1) / (1 - A1))
    # V breakpoints: pairwise intersections of {1 + A0*r, r + B0, 3, 5*r}
    lines_V = [(Fraction(1), A0), (B0, Fraction(1)), (Fraction(3), Fraction(0)), (Fraction(0), Fraction(5))]
    lines_U = [(Fraction(1), A1), (B1, Fraction(1))]
    all_lines = lines_V + lines_U
    for i in range(len(all_lines)):
        c1, m1 = all_lines[i]
        for j in range(i + 1, len(all_lines)):
            c2, m2 = all_lines[j]
            if m1 != m2:
                r = (c2 - c1) / (m1 - m2)
                if Fraction(1, 5) <= r <= Fraction(3, 1):
                    cands.append(r)

    best_ratio = Fraction(0)
    best_r = Fraction(1)
    for r in cands:
        u_val = max(1 + A1 * r, r + B1)
        v_val = min(1 + A0 * r, r + B0, Fraction(3), 5 * r)
        if v_val > u_val:
            ratio = (v_val - u_val) / v_val
            if ratio > best_ratio:
                best_ratio = ratio
                best_r = r
    return best_ratio, best_r


def verify_mahler_and_zeros() -> tuple[MahlerEvaluator, MahlerEvaluator]:
    print("=== 1. Mahler/Newton Decay & Direct Cross-Check ===")
    ev3 = MahlerEvaluator(3, 5, 2, 56)
    ev5 = MahlerEvaluator(5, 3, 4, 43)

    # Cross-check S_{uz} against direct sum for m up to 160 mod p^{20}
    for z in range(1, 80):
        assert ev3.S_uz(z, 20) == S_direct_mod(2 * z, 3, 5, 20)
    for z in range(1, 40):
        assert ev5.S_uz(z, 18) == S_direct_mod(4 * z, 5, 3, 18)
    print("  Mahler decay v_p(Delta^k g(0)) >= k+1 verified for p=3 (D=56) and p=5 (D=43).")
    print("  Exact agreement with direct summation verified for all z < 80 (p=3) and z < 40 (p=5).")

    # Compute high-precision zeros for (1,1)
    z3_11 = ev3.find_zero(1, 1, 55)
    z5_11 = ev5.find_zero(1, 1, 42)
    alpha3_11 = 1 + 2 * z3_11
    alpha5_11 = 1 + 4 * z5_11

    # Verify Phase 14 worked example: (K, L) = (49, 33) -> one-corner classes
    # Phase 14 says: ternary classes for L are 3, 9, 27 mod 6, 18, 54
    # quinary classes for K are 9, 49, 349 mod 20, 100, 500
    assert alpha3_11 % 6 == 3
    assert alpha3_11 % 18 == 9
    assert alpha3_11 % 54 == 27
    assert alpha5_11 % 20 == 9
    assert alpha5_11 % 100 == 49
    assert alpha5_11 % 500 == 349

    # Print first 15 base-p digits of zeta_{3,1,1} and zeta_{5,1,1}
    d3 = []
    t = z3_11
    for _ in range(20):
        d3.append(t % 3)
        t //= 3
    d5 = []
    t = z5_11
    for _ in range(15):
        d5.append(t % 5)
        t //= 5
    print(f"  zeta_{{3,1,1}} base-3 digits (first 20): {d3}")
    print(f"  zeta_{{5,1,1}} base-5 digits (first 15): {d5}")
    print(f"  alpha_{{3,1,1}} mod 54 = {alpha3_11 % 54} (matches Phase 14 = 27)")
    print(f"  alpha_{{5,1,1}} mod 500 = {alpha5_11 % 500} (matches Phase 14 = 349)")
    return ev3, ev5


def verify_single_shapes():
    print("\n=== 2. Exact Single-Shape Maximum Relative Length ===")
    best_all = Fraction(0)
    best_non11 = Fraction(0)
    best_non11_info = None
    for a in range(1, 25):
        for b in range(1, 25):
            ratio, r = exact_single_shape_max(a, b)
            if ratio > best_all:
                best_all = ratio
            if (a, b) != (1, 1) and ratio > best_non11:
                best_non11 = ratio
                best_non11_info = (a, b, r)
    r11, at11 = exact_single_shape_max(1, 1)
    r12, at12 = exact_single_shape_max(1, 2)
    r21, at21 = exact_single_shape_max(2, 1)
    assert r11 == Fraction(4, 11) and at11 == Fraction(5, 6)
    assert r12 == Fraction(2, 13) and at12 == Fraction(10, 9)
    assert r21 == Fraction(4, 41) and at21 == Fraction(25, 36)
    assert best_non11 == Fraction(2, 13)
    print(f"  (1,1): max = {r11} ({float(r11):.12f}) at r = {at11}")
    print(f"  (1,2): max = {r12} ({float(r12):.12f}) at r = {at12}")
    print(f"  (2,1): max = {r21} ({float(r21):.12f}) at r = {at21}")
    print(f"  Max over all (a,b) != (1,1) in [1..24]^2: {best_non11} at {best_non11_info}")


def verify_fixed_axis_separation(ev3: MahlerEvaluator, ev5: MahlerEvaluator):
    print("\n=== 3. Analytic Fixed-Axis Separation Check ===")
    # Check v_3(zeta_{3,a,b1} - zeta_{3,a,b2}) = b1 - 1 for 1 <= b1 < b2 <= 10, 1 <= a <= 6
    for a in range(1, 7):
        zs = {b: ev3.find_zero(a, b, 20) for b in range(1, 11)}
        for b1 in range(1, 10):
            for b2 in range(b1 + 1, 11):
                assert vp(zs[b1] - zs[b2], 3) == b1 - 1
    # Check v_5(zeta_{5,b,a1} - zeta_{5,b,a2}) = a1 - 1 for 1 <= a1 < a2 <= 8, 1 <= b <= 6
    # Recall for p=5, G^{(5)}_{b,a}(K) = S_{K-b} + 5(S_{K-1}-S_{K-b}) + 5^a x_K,
    # so find_zero takes (b, a) as (first_param, second_param)!
    for b in range(1, 7):
        zs = {a: ev5.find_zero(b, a, 15) for a in range(1, 9)}
        for a1 in range(1, 8):
            for a2 in range(a1 + 1, 9):
                assert vp(zs[a1] - zs[a2], 5) == a1 - 1
    print("  Verified v_3(zeta_{3,a,b1}-zeta_{3,a,b2}) = b1-1 and v_5(zeta_{5,b,a1}-zeta_{5,b,a2}) = a1-1.")


def certify_noncoincidence_ladder(ev3: MahlerEvaluator, ev5: MahlerEvaluator):
    r"""Certify pairwise non-coincidence on a ladder of (eta, delta) grids!

    Rigorous accounting:
    Fix eta in (0, 1/2) and delta in (0, 1).
    Outside the boundary strip B_eta (density <= (11/4)*eta) and the initial prefix [0, delta*N)
    (density <= delta):
      - Every nonrectangular position n in [delta*N, N) \ B_eta has
        1 <= a <= A(eta) = 1 + floor(log_5(1/eta)) and
        1 <= b <= B(eta) = 1 + floor(log_3(1/eta)).
      - Any two positions n1, n2 in [delta*N, N) have n1/n2 in (delta, 1/delta), so:
        |K1 - K2| <= R_K := floor(log_3(1/delta)) + 1
        |L1 - L2| <= R_L := floor(log_5(1/delta)) + 1.
      - Wait: check! K = floor(log_3 n). Since n1 < N and n2 >= delta*N:
        log_3(n1) - log_3(n2) < log_3(1/delta), so floor(log_3 n1) - floor(log_3 n2) <= floor(log_3(1/delta)) + 1!
      - Suppose at depths (h, k):
        (i)  2 * 3^{h-1} > R_L and 4 * 5^{k-1} > R_K  (rules out two distinct shells of the SAME shape),
        (ii) For EVERY pair of DISTINCT shapes (a1, b1) != (a2, b2) in [1..A] x [1..B],
             there is NO pair (dL, dK) with |dL| <= R_L and |dK| <= R_K such that BOTH
               (alpha3(a1, b1) - alpha3(a2, b2)) === dL (mod 2 * 3^{h-1})  AND
               (alpha5(b1, a1) - alpha5(b2, a2)) === dK (mod 4 * 5^{k-1}).
             (Note: in fact, we check if at least ONE of the two congruences fails for all |dL| <= R_L or all |dK| <= R_K!)
      - Then in [delta*N, N) \ B_eta, AT MOST ONE shape (a, b) at AT MOST ONE shell (K, L)
        can intersect F_{h,k}!
      - The set of positions in that single shape (a, b) at shell (K, L) is a single interval [U, V)
        with (V - U)/V <= 4/11 (and for any cutoff N >= U, (min(N, V) - U)/N <= (V - U)/V <= 4/11!).
      - Therefore, for all sufficiently large N:
          #(F_{h,k} cap [0, N)) / N <= 4/11 + (11/4)*eta + delta + o(1),
        hence D_infty(alpha(2,3)*alpha(2,5)) <= 4/11 + (11/4)*eta + delta!
    """
    print("\n=== 4. Certified Non-Coincidence Ladder Down to 4/11 + 2.85e-10 ===")
    # Precompute zeros up to A = 15, B = 22 (330 shapes) at high precision
    A_max, B_max = 15, 22
    H_max, K_max = 35, 25  # moduli 2*3^34 and 4*5^24
    # Wait: alpha3 = a + 2*zeta_{3,a,b}, determined mod 2*3^{h-1} from zeta mod 3^{h-1}
    # alpha5 = b + 4*zeta_{5,b,a}, determined mod 4*5^{k-1} from zeta mod 5^{k-1}
    # Note: in ev5, G^{(5)}_{b,a}(K) has a_param = b, b_param = a!
    # Double-check indexing from mixed-interpolation.md:
    # For ternary (p=3, q=5): a = L - J (top ternary row deficit), b = K - I_L (top quinary col deficit)
    #   G^{(3)}_{a,b}(L) = S_{L-a} + 3(S_{L-1} - S_{L-a}) + 3^b x_L, failure sheet L = a + 2z
    # For quinary (p=5, q=3): roles of (p, q) swap!
    #   H = L, m = K, J_5 = K - b (so a_5 = b), b_5 = L - J = a!
    #   G^{(5)}_{b,a}(K) = S_{K-b} + 5(S_{K-1} - S_{K-b}) + 5^a x_K, failure sheet K = b + 4z!
    alpha3 = {}
    alpha5 = {}
    for a in range(1, A_max + 1):
        for b in range(1, B_max + 1):
            z3 = ev3.find_zero(a, b, H_max - 1)
            z5 = ev5.find_zero(b, a, K_max - 1)
            alpha3[(a, b)] = a + 2 * z3
            alpha5[(a, b)] = b + 4 * z5

    tiers = [
        ("Tier 1 (modest)", Fraction(1, 1000), Fraction(1, 10000)),
        ("Tier 2 (micro)", Fraction(1, 10**6), Fraction(1, 10**7)),
        ("Tier 3 (nano)", Fraction(1, 10**10), Fraction(1, 10**11)),
    ]

    for label, eta, delta in tiers:
        A = 1 + int(math.floor(math.log(float(1 / eta), 5)))
        B = 1 + int(math.floor(math.log(float(1 / eta), 3)))
        # Exact integer verification of A and B: 5^A > 1/eta and 3^B > 1/eta
        while Fraction(1, 5**A) >= eta:
            A += 1
        while Fraction(1, 3**B) >= eta:
            B += 1
        R_K = int(math.floor(math.log(float(1 / delta), 3))) + 2
        R_L = int(math.floor(math.log(float(1 / delta), 5))) + 2
        assert 3 ** (R_K - 1) > int(1 / delta)
        assert 5 ** (R_L - 1) > int(1 / delta)

        shapes = [(a, b) for a in range(1, A + 1) for b in range(1, B + 1)]
        # Find minimal (h, k) that separates all pairs!
        # Start with h, k large enough for same-shape separation
        h = 2
        while 2 * (3 ** (h - 1)) <= R_L:
            h += 1
        k = 2
        while 4 * (5 ** (k - 1)) <= R_K:
            k += 1

        # Search smallest (h, k) with h <= H_max, k <= K_max that separates all pairs
        # Use a balanced search: increase whichever modulus is smaller until zero collisions
        while True:
            mod3 = 2 * (3 ** (h - 1))
            mod5 = 4 * (5 ** (k - 1))
            # Check all pairs
            collisions = 0
            for i in range(len(shapes)):
                s1 = shapes[i]
                a3_1 = alpha3[s1] % mod3
                a5_1 = alpha5[s1] % mod5
                for j in range(i + 1, len(shapes)):
                    s2 = shapes[j]
                    d3 = (a3_1 - alpha3[s2]) % mod3
                    if d3 > mod3 // 2:
                        d3 -= mod3
                    if abs(d3) <= R_L:
                        d5 = (a5_1 - alpha5[s2]) % mod5
                        if d5 > mod5 // 2:
                            d5 -= mod5
                        if abs(d5) <= R_K:
                            collisions += 1
                            break
                if collisions:
                    break
            if collisions == 0:
                break
            if mod3 < mod5 and h < H_max:
                h += 1
            elif k < K_max:
                k += 1
            elif h < H_max:
                h += 1
            else:
                raise RuntimeError(f"Could not separate {label} within H_max={H_max}, K_max={K_max}")

        bound = Fraction(4, 11) + Fraction(11, 4) * eta + delta
        print(
            f"  {label}: eta={eta}, delta={delta}, grid={A}x{B} ({len(shapes)} shapes), "
            f"R_K={R_K}, R_L={R_L}"
        )
        print(
            f"    Certified zero collisions at depths (h, k) = ({h}, {k}) "
            f"[moduli {2*3**(h-1)}, {4*5**(k-1)}]"
        )
        print(
            f"    Unconditional bound: D_infty <= {float(bound):.13f} "
            f"(4/11 + {float(bound - Fraction(4, 11)):.3e})"
        )
        assert bound < Fraction(4631, 12500)  # strictly below Phase 14's 0.37048


def scan_actual_shells(ev3: MahlerEvaluator, ev5: MahlerEvaluator):
    print("\n=== 5. Actual Nonrectangular Shell-Loss Scan (K up to 200,000) ===")
    # For shape (1,1), a shell (K, L) has nonempty (1,1) interval iff
    # max(P + Q/5, Q + P/3) < P + Q  (always true) AND P < 3P, Q < 5Q,
    # and for the (1,1) interval to lie inside [max(P, Q), min(3P, 5Q)):
    # we need P + Q/5 < 3P (r < 10) and Q + P/3 < 5Q (r > 1/12), wait:
    # actually shape (1,1) requires K = floor(log_3 n), L = floor(log_5 n),
    # J = floor(log_5(n - P)) = L - 1, I_L = floor(log_3(n - Q)) = K - 1,
    # which means 1/12 < Q/P < 10? Wait: P + Q/5 < 5Q (always) and Q + P/3 < 3P (r < 8/3),
    # and P + Q/5 >= Q (r <= 5/4) or Q + P/3 >= P (r >= 2/3) — wait, max(P+Q/5, Q+P/3) is
    # always >= max(P, Q), and min(P+Q, 3P, 5Q) > max(P+Q/5, Q+P/3) iff r in (1/12, 8/3)!
    # Check exact condition: 1/3 < r < 5 (since n in [P, 3P) cap [Q, 5Q) nonempty iff 1/5 < r < 3).
    # For each K in 1..200000, find all L with 1/5 < 5^L / 3^K < 3 (at most 2 values of L per K!).
    z3_11 = ev3.find_zero(1, 1, 30)
    z5_11 = ev5.find_zero(1, 1, 22)
    a3_11 = 1 + 2 * z3_11
    a5_11 = 1 + 4 * z5_11

    log3_5 = math.log(3.0) / math.log(5.0)
    best_joint = (0, 0, 0, 0)  # (min(h,k), h+k, K, L)
    best_sum = (0, 0, 0, 0)
    joint_hits_ge2 = 0
    joint_hits_ge3 = 0
    total_pairs = 0
    for K in range(2, 200001):
        # 3^K / 5 < 5^L < 3 * 3^K  <=> K*log_5(3) - 1 < L < K*log_5(3) + log_5(3)
        lo = int(math.floor(K * log3_5 - 1.0))
        hi = int(math.ceil(K * log3_5 + log3_5))
        for L in range(max(2, lo), hi + 1):
            # Exact check 1/5 < 5^L / 3^K < 3 using log (safe margin)
            lr = L * math.log(5.0) - K * math.log(3.0)
            if not (-math.log(5.0) < lr < math.log(3.0)):
                continue
            total_pairs += 1
            # Compute ternary loss h and quinary loss k for shape (1,1)
            if (L - a3_11) % 2 != 0:
                h = 0
            else:
                h = 1 + vp((L - a3_11) // 2, 3)
            if (K - a5_11) % 4 != 0:
                k = 0
            else:
                k = 1 + vp((K - a5_11) // 4, 5)
            if h >= 2 and k >= 2:
                joint_hits_ge2 += 1
            if h >= 3 and k >= 3:
                joint_hits_ge3 += 1
            if (min(h, k), h + k) > (best_joint[0], best_joint[1]):
                best_joint = (min(h, k), h + k, K, L, h, k)
            if h >= 1 and k >= 1 and (h + k) > best_sum[0]:
                best_sum = (h + k, K, L, h, k)

    print(f"  Scanned {total_pairs} overlapping shell pairs (K <= 200,000) for shape (1,1).")
    print(f"  Pairs with h >= 2 and k >= 2: {joint_hits_ge2}")
    print(f"  Pairs with h >= 3 and k >= 3: {joint_hits_ge3}")
    print(f"  Deepest balanced joint loss: min(h,k)={best_joint[0]}, (h,k)=({best_joint[4]},{best_joint[5]}) at (K,L)=({best_joint[2]},{best_joint[3]})")
    print(f"  Largest joint sum h+k (with h,k>=1): h+k={best_sum[0]}, (h,k)=({best_sum[3]},{best_sum[4]}) at (K,L)=({best_sum[1]},{best_sum[2]})")


def verify_base_variation():
    print("\n=== 6. Base-Variation Metric Derivative Verification ===")
    # Check beta = 2 * (1 + 3*t) mod 9 (or mod 27):
    # For beta in Z_3^x, S_m(beta) = sum_{j=1}^m 5^{-j} beta^{-5^j}
    # At beta = 2: S_2(2) = 5^{-1}*2^{-5} + 5^{-2}*2^{-25} mod 9
    for beta in (2, 5, 8):
        # Compute S_2(beta) mod 9
        s2 = (pow(5, -1, 9) * pow(beta, -5, 9) + pow(5, -2, 9) * pow(beta, -25, 9)) % 9
        print(f"  beta = {beta} (mod 9): S_2(beta) mod 9 = {s2} (v_3 = {vp(s2, 3) if s2 else 'inf'})")

    # Verify d/dt [G^{(3)}_{1,1}(1 + 2z; 2*exp(3t))] / 3 === -z (mod 3) at t = 0
    # Numerically in Z_3 using finite difference (G(beta1) - G(beta0)) / 9 mod 3 where beta1 = 2*(1 + 3) = 8?
    # Better: beta(t) = 2 * (1 + 3*t) mod 27 with t = 3 (step dt = 3, so beta1 = 2 + 18 = 20 mod 27)
    def G11_beta(beta: int, z: int, mod: int) -> int:
        phi = 2 * (mod // 3)
        m = 1 + 2 * z
        def xj(j):
            return (pow(5, -j, mod) * pow(beta, -pow(5, j, phi), mod)) % mod
        s_prev = sum(xj(j) for j in range(1, m)) % mod
        return (s_prev + 3 * xj(m)) % mod

    # At beta0 = 2, beta1 = 2 * (1 + 3*3) = 20 (dt = 3):
    # (G(beta1) - G(beta0)) / (3 * dt) = (G(20) - G(2)) / 9 mod 3 should equal -z mod 3!
    for z in range(1, 10):
        g0 = G11_beta(2, z, 27)
        g1 = G11_beta(20, z, 27)
        diff = (g1 - g0) % 27
        assert diff % 9 == 0
        deriv_div3 = (diff // 9) % 3
        assert deriv_div3 == (-z) % 3, f"Mismatch at z={z}: got {deriv_div3}, expected {(-z)%3}"
    print("  Verified (1/3) * d/dt G^{(3)}_{1,1}(1+2z; 2*exp(3t))|_{t=0} === -z (mod 3) for z = 1..9.")
    print("  At z = zeta_{3,1,1}(2) === 1 (mod 3), derivative is a 3-adic unit => local isometry in t!")


def main():
    ev3, ev5 = verify_mahler_and_zeros()
    verify_single_shapes()
    verify_fixed_axis_separation(ev3, ev5)
    certify_noncoincidence_ladder(ev3, ev5)
    scan_actual_shells(ev3, ev5)
    verify_base_variation()
    print("\nAll Phase 16 Track 6 mixed-product checks passed.")


if __name__ == "__main__":
    main()
