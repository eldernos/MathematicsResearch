# Reviewer packet

Scope: a research note on the binary digits of the Erdős–Borwein constant E = Σ 1/(2^n − 1). It does not claim normality or non-normality of E. Review is requested on the three items below. Lean links are pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec`.

## Notation

τ(m) = 2^V(m)·U(m), U(m) odd; t(m) = m − V(m); C(t) = Σ_{t(m)=t} U(m). For a shift n: R_D(n) = (Σ_{d≤D} 2^(D−d) C(n+d)) mod 2^D and Y_D(n) = Σ_{d>D} C(n+d) 2^(D−d). Digit n+1 of E equals 1 iff 2^(D−1) ≤ (R_D + ⌊Y_D⌋) mod 2^D (Lemma 2.1). I = [N, 2N); f_I is the proportion of ones among digits n+1, n ∈ I. μ = E U_* = Π_p E odd(B_p+1) ∈ [2.0762592, 2.0763285]. Q_D is the law of R_D when the columns are independent Poisson(1) numbers of i.i.d. marks distributed as U_*.

## Item 1: Theorem 5.1 (Lean-supported paper proof)

**Statement.** With λ = 1/557 and Ψ_16(r) = 1[r ≥ 2^15] + Σ_{k=1}^{556} (1 − k/557)·1[r = 2^15 − k]: for every sequence of windows I = [N, 2N), N → ∞, limsup f_I ≤ limsup E_I Ψ_16(R_16) + μ/557. Hence limsup E_I Ψ_16(R_16) < 0.4962723 implies limsup f_I < 1/2. Under Q_16, E Ψ_16 ≤ 0.4960081.

**Proof.**
1. Pointwise dual inequality [Lean `carry_knapsack_le`, https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L375]: 1[2^15 ≤ (r+c) mod 2^16] ≤ Ψ_16(r) + c/557 for all naturals r, c.
2. Put r = R_16(n) and c = ⌊Y_16(n)⌋ ≤ Y_16(n); apply Lemma 2.1.
3. Average over n ∈ I and use Proposition 3.1(c): E_I Y_16 = μ + o(1).
4. E_{Q_16} Ψ_16 ≤ 0.4960081 is a finite certificate: `scripts/phase17_erdos_borwein_bias.py` section C prints "D=16 LP dual certificate: lambda = 1/557, value <= 0.49973577" and "E_Q16[Psi_16] <= 0.49600807".

**External inputs.** None. Proposition 3.1(c) is elementary. Put a = U * Möbius (so U = 1 * a). Since U(p) = U(1), a vanishes at integers having a prime to exactly the first power. Also |a(q)| ≤ τ(q), so Σ_{N+d ≤ m < 2N+d} U(m) = Nμ + O(N^(1/2+ε)). The sources with t(m) ∈ [N+d, 2N+d) differ from m ∈ [N+d, 2N+d) by O(log N) integers. The terms d > N are superexponentially small.

**Steps where review is wanted.** (a) Lemma 2.1 and the reindexing in Proposition 3.1(b),(c). (b) Uniformity in d and the strip estimate. (c) That λ = 1/557 and the certified value are correctly taken from the script.

**Reproduction.** `python -B scripts/phase17_erdos_borwein_bias.py` (about 20 s). Independent float cross-check: `python -B papers/09-erdos-borwein-note/crosscheck.py` (about 10 s, needs numpy) gives E Ψ_16 ≈ 0.4960055 (float, truncated mass).

## Item 2: Theorem 7.1 (Lean-supported paper proof)

**Statement.** For odd r and any law of N ∈ ℤ≥0 with E (N)_k = 1 for 1 ≤ k ≤ r: E(−1)^N ≥ e_r := Σ_{k≤r} (−2)^k/k!, with equality for w_n = (1/n!) Σ_{j=0}^{r−n} (−1)^j/j! on {0,…,r}. Values: e_1 = −1, e_3 = −1/3, e_5 = 1/15, e_7 = 41/315, e_9 = 383/2835.

**Proof.** Dual: q_r(n) = Σ_{k≤r} (−2)^k C(n,k) satisfies q_r(n) ≤ (−1)^n [Lean `parity_bonferroni_dual_le`, https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L432], and E q_r(N) = Σ (−2)^k E C(N,k) = e_r. Primal: w_n ≥ 0 because the partial sums of the series of e^(−1) are nonnegative; its binomial moments are 1/k! by Σ_{i+j≤m} (−1)^j/(i! j!) = Σ_{l≤m} (1−1)^l/l! = 1; and (−1)^n = Σ_k (−2)^k C(n,k) gives E(−1)^N = e_r.

**External inputs.** None. The related framework is the majorant–minorant method for sharp Bonferroni-type bounds (M. Sibuya, Ann. Inst. Statist. Math. 43 (1991), 261–285; J. Galambos and I. Simonelli, *Bonferroni-type inequalities with applications*, Springer, 1996). A referee model read Sibuya's paper and found no statement of the parity functional or of the value Σ_{k≤r}(−2)^k/k!; see LEDGER.md. For even r, Proposition 7.2 shows inf E(−1)^N = e_{r−1}, not attained.

**Steps where review is wanted.** Whether this is a known special case of sharp Bonferroni-type bounds (the framework is expected to cover it; the explicit value may or may not appear in the literature). Only the pointwise inequality is formalized; the moment bookkeeping is not.

**Reproduction.** `crosscheck.py` section 4 (exact fractions); script section F.

## Item 3: Theorem 7.5 (Lean-supported paper proof)

**Statement.** Suppose that, along a sequence of windows [N_j, 2N_j), all mixed factorial moments of total order ≤ 92 of the marked column counts N_{d,c}(n) (1 ≤ d ≤ 16, c odd mod 2^d, counting sources at position n+d with mark ≡ c mod 2^d) converge to their Poisson values. Then limsup f_I ≤ 0.499856 < 1/2.

**Proof.** For a configuration n⃗ and even t, let B_t(n⃗) be the truncation at total degree |n⃗| + t of Jordan's formula for 1[N⃗ = n⃗]. Vandermonde gives B_t(n⃗) = 1[N⃗ = n⃗] + Π C(N_i, n_i)·C(M−1, t)·1[M ≥ 1] ≥ 1[N⃗ = n⃗], where K = Σ N_i and M = K − |n⃗|. Then Φ = Σ_{|n⃗|<92} Ψ_16(n⃗) B_{t(n⃗)}(n⃗) + C(K, 92) is a polynomial of degree ≤ 92 with Φ ≥ Ψ_16(R_16). Under the Poisson law (K ~ Poisson(16)), E Φ ≤ E_{Q_16} Ψ_16 + E Σ_{j<92} C(K,j) C(K−j−1, t_j) + 16^92/92! ≤ E_{Q_16} Ψ_16 + 1.197×10^(−4). The last bound is a finite certificate (exact fractions for K ≤ 360, a 4^K tail bound beyond). Add μ/557 as in Item 1. The same pointwise inequality Φ ≥ Ψ_16 gives f(1) < 1/2 for every law in the information class I_{16,92}, hence r_min(16) ≤ 92.

**Steps where review is wanted.** The Vandermonde collapse; the pointwise inequality Φ ≥ Ψ_16 for configurations with |n⃗| ≥ 92; the tail bound beyond K = 360 (script section F, `KMAX`).

**Reproduction.** Script section F ("RESULT F2"); `crosscheck.py` section 4 gives the excess 1.19675×10^(−4) for K ≤ 360.

## What is not claimed

No statement about normality of E. The model Q_∞ is a heuristic; the note proves only implications and finite-information obstructions. The written proofs have been checked only by AI models from different providers; no human specialist has reviewed them.
