# Reviewer packet: Paper II, version 2.0

Evidence for the theorems below is the Lean kernel (pinned `e4809cf561573aef588e6ffc491a35cdb79fd9ec`); the written proofs are the object of review. No independent human has reviewed them.

## 1. Statement

Let S be a finite set of primes, b >= 2, M(S) the positive integers with all prime factors in S (including 1), J = {p in S : p does not divide b}. For P in Q[X] and s >= 0 put X(P,s) = sum over m in M(S) of P(m) m^{-s} b^{-m}; X_s = X(1,s).

**Theorem A** (kernel-verified: `unsigned_discrepancy_limit`, `unsigned_finite_support_normal`). For s >= 1, the interval discrepancy D_N(X_s) of the radix-b shifts tends to 0 if J is nonempty and to 1 if J is empty.

**Theorem B** (kernel-verified: `full_rational_normal_iff`, `rational_boundary`). For P != 0 with order of vanishing r at 0, X(P,s) is normal iff r < s and J is nonempty; otherwise every restriction of the support is nonnormal.

**Theorem C(i)** (kernel-verified: `joint_full_polynomial_orders`). If J is nonempty, s_1,...,s_d are distinct positive integers and P_i(0) != 0, the vectors ({b^n X(P_i,s_i)})_i are uniformly distributed in [0,1)^d.

## 2. Shortest complete proof (with all external inputs)

External inputs: (E1) Weyl's criterion in one and several variables. (E2) Vandehey, J. Anal. Math. 138 (2019), Corollary 1.2 (arXiv:1606.07911 numbering): for a finite prime set P, m supported on P, gcd(a,m) = gcd(m,b) = 1, N >= m^epsilon: |sum_{n=1}^N e(a b^n / m)| <= C N m^{-delta} (1 + log m). (E3) Poincare recurrence for a rotation of the circle. (Lean contains an independent proof of (E2): `fixed_support_orbit_estimate`.)

**Step 1 (Lemma 2.1, transfer).** Partition [0,N) into blocks [u,u+B), B = floor(sqrt N); discard blocks within B of an index in M(S) (there are O((log N)^|S|) such indices up to 2N, so o(N) positions). On a retained block R_{u+i} = b^i R_u for the rational prefix R_n = sum_{m<=n} a_m b^{n-m}, the real orbit is within o(1) of it, and den(R_u) is supported on a fixed finite set of primes not dividing b and is at most B^C (clear the primes of S dividing b by the age u-m >= B and the coefficient denominator by D_0; each m has prime exponents at most log_2(N+2B)). By (E2) with L = B >= q^{1/C}, the shifts of a block with den(h R_u) = q >= Q_0 have discrepancy at most epsilon for large N.

**Step 2 (local test, Lemma 3.1).** Fix p in J, T = M(S minus {p}), w the Teichmuller lift of b^{-1} mod p, U(t) = sum_{i>=0} p^{is} sum_{m in T, m <= p^i t} w^m m^{-s} for 1 <= t < p. For p^k <= n < p^{k+1}, k >= 2(L-1): if U(n/p^k) is nonzero mod p^L then v_p(den R_{s,n}) >= ks - (L-1). Hence D_infinity <= C_{p,s,L}, the worst-prefix certificate of the failed set E_{p,s,L} = {t : U(t) = 0 mod p^L}, and C <= (1 + 1/(p-1)) |E|.

**Step 3 (nullity, Theorem 4.1).** |{t : U(t) = 0}| = 0. Suppose not. U(pt) = p^{-s} U(t). If T = {1}, U is a unit. Otherwise take cofactor primes q_1..q_d (including r). Poincare recurrence for the rotation by -h_j log_p q_j, where h_j is an eventual period of q_j^n mod (p-1), gives a_j in h_j Z_{>0} such that G(t) - q_j^{-a_j s} G(t / q_j^{a_j}) again has a zero set of positive measure; iterate over j. The resulting moment has coefficients A(m) = sum over I with Q_I | m of (-1)^|I| w^{m / Q_I} (Q_I = prod_{j in I} q_j^{a_j}). A(m) = 0 once some v_{q_j}(m) >= L_j + a_j (pair I with I union {j}), so only finitely many rays c r^l survive (c in a finite set), with A(r^l) = w^{r^l} a unit. Thresholds c r^l / p^i in [1,p) are distinct; those in rows at most H apart have logarithms at distance >= eta > 0, where (H+1)s exceeds the maximal valuation V of nonzero values of A. On a short piece [t_1, t_2) a bare-ray threshold exists (log_p r irrational). The first nonzero jump has valuation <= is + V and the remaining rows are divisible by p^{(i+H+1)s}, so G(t_1) != G(t_2). Each piece has at most one zero of G, contradicting positive measure.

**Step 4 (Theorem A).** J nonempty: combine Steps 1-3. J empty: prefixes are integral, so [delta, 1-delta) has frequency o(1).

**Step 5 (Theorem B).** If r < s, write D P = X^r G, G in Z[X], G(0) != 0. The prefix of D X(P,s) is G(0) R_{t,n} (t = s - r) plus a part of valuation >= -k(t-1) at p; by Step 2 the first has valuation <= v_p(G(0)) - kt + L - 1 which is smaller for k large. Apply Steps 1-3 with order t. If r >= s or J empty, DP(m)/m^s is integral, so shifted prefixes lie in D_0^{-1} Z on retained blocks; an interval inside a gap of the grid has frequency o(1).

**Step 6 (Theorem C(i)).** For 0 != h in Z^d, let I = {i : h_i != 0}, t = max_{i in I} s_i, and Q = sum_{i in I} h_i X^{t-s_i} P_i. The index j with s_j = t is unique, so Q(0) = h_j P_j(0) != 0. Then sum_i h_i X(P_i,s_i) = X(Q,t), normal by Theorem B, so the Weyl sums vanish; apply the multidimensional Weyl criterion (E1).

## 3. Evidence label and reproduction

- Theorems A, B, C(i): **Kernel-verified**. Reproduce with `papers/02-localized-normality-v2/check.sh` and `lake env lean papers/02-localized-normality-v2/AuditDeclarations.lean` (see `VERIFICATION.md`). Mathlib-only statements: `PaperII.unsignedClassification`, `PaperII.polynomialClassification`, `PaperII.jointPolynomial` in `Statements.lean`/`Check.lean`; axioms reported: `propext`, `Classical.choice`, `Quot.sound`.
- Lemma 2.1: **Paper proof** with external input (E2).
- Steps 2-3 as written: the kernel proves the statements (`discrepancy_le_certificate`, `unsigned_persistent_null`); the text is the explanation.

## 4. Steps on which review is wanted

1. Step 3: the recurrence step (return time taken as a multiple of the eventual period of q_j^n mod (p-1), including when q_j divides p-1, and p = 2 where the congruence is trivial); survival of the bare ray r^l after all differences; the separation of thresholds restricted to rows at bounded distance; why the zero set of the differenced moment retains positive measure.
2. Step 1: whether Corollary 1.2 of Vandehey applies as used (blocks of length B with reduced denominator between a large constant and B^C, numerators arbitrary after multiplication by h).
3. The literature comparison (`LEDGER.md`): in particular whether any earlier result for three or more generators with a radix prime at order one (or for higher orders on mixed supports) implies Theorem A; and the overlaps with Mira's notes (S09 Theorems 1-2; second archive S07), Mira Cult's note of 24 November 2026, and Sude's `xi-normality`, `xi-family` and `stoneham-prime-support`.
4. The correspondence of the Lean definitions (`maskedValue`, `JointUniform`, `radixDiscrepancy`) with the displayed series and frequencies.
