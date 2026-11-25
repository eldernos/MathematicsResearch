# Reviewer packet: Paper II, version 2.0

Lean statements are pinned at `e4809cf561573aef588e6ffc491a35cdb79fd9ec`; the written proofs are the object of review. No independent human has reviewed them. This packet is an excerpt of the paper: it states Theorems A and B in full and Theorem C(i), and gives the proof of these three. Theorems C(ii), (iii), D, E, F and the other results of the paper are not part of the packet.

## 1. Statement

Let S be a finite set of primes, b >= 2, M(S) the positive integers with all prime factors in S (including 1), J = {p in S : p does not divide b}. For P in Q[X] and s >= 0 put X_A(P,s) = sum over m in A of P(m) m^{-s} b^{-m} for A a subset of M(S), X(P,s) = X_{M(S)}(P,s) and X_s = X(1,s).

**Theorem A** (kernel-verified: `unsigned_discrepancy_limit`, `unsigned_finite_support_normal`). For s >= 1, the interval discrepancy D_N(X_s) of the radix-b shifts tends to 0 if J is nonempty and to 1 if J is empty.

**Theorem B.** Let P != 0 have order of vanishing r at 0 and let s >= 0.
(i) X(P,s) is normal iff r < s and J is nonempty (kernel-verified: `full_rational_normal_iff`).
(ii) If r >= s or J is empty, then for every restriction A of M(S) there is an integer L >= 1 coprime to b with liminf_N D_N(X_A(P,s)) >= 1/L; in particular X_A(P,s) is not normal (kernel-verified: `rational_boundary`, which quantifies over the mask before giving L). The written proof below gives one L = D_0 for all A.
(iii) If P is in Z[X] and (r >= s or J is empty), then D_N(X_A(P,s)) tends to 1 for every restriction A (kernel-verified: `integer_mask_maximal`).

**Theorem C(i)** (kernel-verified: `joint_full_polynomial_orders`). If J is nonempty, s_1,...,s_d are distinct positive integers and P_i(0) != 0, the vectors ({b^n X(P_i,s_i)})_i are uniformly distributed in [0,1)^d.

## 2. Shortest complete proof (with all external inputs)

External inputs: (E1) Weyl's criterion in one and several variables. (E2) Vandehey, J. Anal. Math. 138 (2019), Corollary 1.2 (numbering of the author manuscript arXiv:1606.07911v1, pp. 2-3): for a fixed finite prime set P, m supported on P, gcd(a,m) = gcd(m,b) = 1, N >= m^epsilon: |sum_{n=1}^N e(a b^n / m)| <= C N m^{-delta} (1 + log m). (E3) Poincare recurrence for a rotation of the circle. (Lean contains an independent proof of (E2): `fixed_support_orbit_estimate`.)

**Step 1 (Lemma 2.1, transfer).** Partition [0,N) into blocks [u,u+B), B = floor(sqrt N); discard blocks within B of an index in M(S) (there are O((log N)^|S|) such indices up to 2N, so o(N) positions). On a retained block R_{u+i} = b^i R_u for the rational prefix R_n = sum_{m<=n} a_m b^{n-m}, the real orbit is within o(1) of it, and den(R_u) is supported on a fixed finite set of primes not dividing b and is at most B^C (clear the primes of S dividing b by the age u-m >= B and the radix part of the coefficient denominator likewise; each m has prime exponents at most log_2(N+2B)). Given epsilon > 0, first fix the finitely many frequencies h used in the Fourier smoothing and the interval grid, then choose the denominator threshold Q_0 for these frequencies, then N_0. By (E2) with L = B >= q^{1/C}, for N >= N_0 the shifts of a block with den(h R_u) = q >= Q_0 have discrepancy at most epsilon.

**Step 2 (local test, Lemma 3.1).** Fix p in J, T = M(S minus {p}), w the Teichmuller lift of b^{-1} mod p, U(t) = sum_{i>=0} p^{is} sum_{m in T, m <= p^i t} w^m m^{-s} for 1 <= t < p. For p^k <= n < p^{k+1}, k >= 2(L-1): if U(n/p^k) is nonzero mod p^L then v_p(den R_{s,n}) >= ks - (L-1). This valuation statement is the written step. Given it, D_infinity <= C_{p,s,L}, the worst-prefix certificate of the failed set E_{p,s,L} = {t : U(t) = 0 mod p^L}, uses Step 1 and the kernel-verified inequality `discrepancy_le_certificate`; also C <= (1 + 1/(p-1)) |E|.

**Step 3 (nullity, Theorem 4.1).** |{t : U(t) = 0}| = 0. Suppose not. U(pt) = p^{-s} U(t). If T = {1}, U is a unit. Otherwise fix one cofactor prime r in S minus {p} (the ray prime) and let q_1,...,q_d be the **other** cofactor primes; r is not used in any difference. Poincare recurrence for the rotation by -h_j log_p q_j, where h_j is an eventual period of q_j^n mod (p-1), gives a_j in h_j Z_{>0} such that G(t) - q_j^{-a_j s} G(t / q_j^{a_j}) again has a zero set of positive measure; iterate over j = 1,...,d. The resulting moment has coefficients A(m) = sum over subsets I of {1,...,d} with Q_I | m of (-1)^|I| w^{m / Q_I} (Q_I = prod_{j in I} q_j^{a_j}). A(m) = 0 once some v_{q_j}(m) >= L_j + a_j (pair I with I union {j}), so only finitely many rays c r^l survive (c in a finite set prime to p r), and A(r^l) = w^{r^l} is a unit because no q_j divides r^l, so only I empty contributes. (If r were also used in a difference, A(r^l) would involve a term with Q_I | r^l once l reaches the shift, and the unit assertion would fail.) Thresholds c r^l / p^i in [1,p) are distinct; those in rows at most H apart have logarithms at distance >= eta > 0, where (H+1)s exceeds the maximal valuation V of nonzero values of A. On a short piece [t_1, t_2) a bare-ray threshold exists (log_p r irrational). The first nonzero jump has valuation <= is + V and the remaining rows are divisible by p^{(i+H+1)s}, so G(t_1) != G(t_2). Each piece has at most one zero of G, contradicting positive measure.

**Step 4 (Theorem A).** J nonempty: combine Steps 1-3 (the limit is 0). J empty: every m in M(S) with m <= N+2B has m^s dividing b^{sH}, H = ceil(log_2(N+2B)), so on retained blocks the weights b^{u-m}/m^s are integers and the shifted prefixes are integral; the interval [delta, 1-delta) then has frequency o(1), so liminf D_N >= 1 - 2 delta for each delta and D_N tends to 1.

**Step 5 (Theorem B).** Write D P = X^r G with G in Z[X], G(0) != 0 and D > 0 an integer, and D = D_b D_0 with D_b | b^l and gcd(D_0, b) = 1.
- (i), sufficiency: r < s, t = s - r, p in J. The prefix of D X(P,s) is G(0) R_{t,n} plus a part of valuation >= -k(t-1) at p; by Step 2 the first has valuation <= v_p(G(0)) - kt + L - 1 which is smaller for k large. Apply Steps 1-3 with order t. Necessity is (ii).
- (ii), (iii), case r >= s: DP(m)/m^s = m^{r-s} G(m) is an integer for all m. D_b divides b^{u-m} once u - m >= l, so every shifted summand lies in D_0^{-1} Z.
- (ii), (iii), case J empty: DP(m)/m^s need **not** be an integer (for P = 1, s = 1, b = 2, S = {2} it is 1/m). Instead m^s divides b^{sH} for m <= N+2B, and on retained blocks u - m >= B > sH + l, so b^{u-m} clears D_b m^s and again every shifted summand lies in D_0^{-1} Z.
- In both cases the shifts are within o(1) of D_0^{-1} Z / Z outside o(N) positions, for every restriction A, so the interval [delta, 1/D_0 - delta) has frequency o(1) and liminf D_N >= 1/D_0: this is (ii) with L = D_0. For integral P take D = 1, D_0 = 1: D_N tends to 1, which is (iii). The identification L = D_0 is a written step; the kernel statement is `rational_boundary`.

**Step 6 (Theorem C(i)).** For 0 != h in Z^d, let I = {i : h_i != 0}, t = max_{i in I} s_i, and Q = sum_{i in I} h_i X^{t-s_i} P_i. The index j with s_j = t is unique, so Q(0) = h_j P_j(0) != 0. Then sum_i h_i X(P_i,s_i) = X(Q,t), normal by Theorem B(i), so the Weyl sums vanish; apply the multidimensional Weyl criterion (E1).

## 3. Evidence label and reproduction

- Theorem A: **Kernel-verified**. Theorem B(i), (ii), (iii) and Theorem C(i): **Kernel-verified**, one declaration each as listed in section 1. The mathlib-only restatements `PaperII.unsignedClassification` (the limit statement and the normality for J nonempty), `PaperII.polynomialClassification` (the equivalence B(i) only) and `PaperII.jointPolynomial` (C(i)) are in `Statements.lean`/`Check.lean`; they do not restate B(ii), B(iii) or the "J empty is nonnormal" clause of Theorem A, which are covered by the library statements `rational_boundary`, `integer_mask_maximal` and `unsigned_discrepancy_limit`. Reported axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Reproduce with `papers/02-localized-normality-v2/check.sh` and `lake env lean papers/02-localized-normality-v2/AuditDeclarations.lean` (the latter exits with an error on a missing declaration or an unexpected axiom) from the release that contains these files, against a library build compatible with the pin; the bare checkpoint does not contain them (see `VERIFICATION.md`).
- Lemma 2.1: **Paper proof** with external input (E2).
- Step 2: **Lean-supported paper proof**: the valuation statement is written; the inequality D_infinity <= C_{p,s,L} is `discrepancy_le_certificate`.
- Step 3 as written: the kernel proves the statement (`unsigned_persistent_null`); the text is the explanation.

## 4. Steps on which review is wanted

1. Step 3: the recurrence step (return time taken as a multiple of the eventual period of q_j^n mod (p-1), including when q_j divides p-1, and p = 2 where the congruence is trivial); survival of the bare ray r^l after all differences over the **other** cofactor primes; the separation of thresholds restricted to rows at bounded distance; why the zero set of the differenced moment retains positive measure.
2. Step 1: whether Corollary 1.2 of Vandehey applies as used (blocks of length B with reduced denominator between a large constant and B^C, numerators arbitrary after multiplication by h), and the order of the choices of the frequencies, the denominator threshold and N_0.
3. Step 5: the two-case clearing argument for the lower bound and the integral clause, in particular the case J empty.
4. The literature comparison (`LEDGER.md`): in particular whether any earlier result for three or more generators whose least prime divides the radix at order one (or for higher orders on such mixed supports) implies Theorem A; the extensions of Sude's Theorem 5.1, his binary argument and his Lemma 4, and of Mira's Theorem 2, that the paper attributes to the proofs rather than the statements; and the overlaps with Mira's notes (S09 Theorems 1-2; September S07; the second archive S07 of 7 October 2026), Mira Cult's note of 24 November 2026, Kano's Theorem 1 and Vandehey's Theorem 7.4.
5. The correspondence of the Lean definitions (`maskedValue`, `JointUniform`, `radixDiscrepancy`) with the displayed series and frequencies.
