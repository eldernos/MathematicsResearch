# Reviewer packet: Disjunctive but Nonnormal Multiplicative Lambert Series (v1.0)

Author: Christopher Anderson (Independent Researcher). AI assistance is disclosed in the manuscript. The written proofs have not had human expert review.

## Setting

Primes are p, q. Fix q₀, a reduced residue a₀ mod q₀, δ ∈ (0,1), and a set S of primes not dividing q₀ that contains every prime ≡ a₀ (mod q₀) and satisfies Σ_{p≤x, p∈S} 1/p = δ log log x + O(1). Let c : ℕ → ℤ_{≥0} be multiplicative with c(1) = 1 and c(pᵉ) ≤ e+1, c(p) = 2 for p ∈ S, c(p) = 0 for p ∉ S with p ∤ q₀, and c(p₀^{2u}) = 2u+1 for one p₀ ∈ S and all u ≥ 0. Put κ = 1−δ, L = Σ_{n≥1} c(n)2⁻ⁿ = Σ_{m≥1} (c∗μ)(m)/(2ᵐ−1), and x_n = {2ⁿL}. A word w of length k and value u occurs at shift n iff x_n ∈ I_w = [u2^{−k}, (u+1)2^{−k}). Let #_w(N,H) = #{N ≤ n < N+H : x_n ∈ I_w}. D_N is the extreme discrepancy of x_0, …, x_{N−1} over half-open intervals.

Examples: c = χ∗1 for nonprincipal real χ (δ = 1/2), with c = r₂/4 for χ₄; and f completely multiplicative with f(p) = 1 for p ≡ 1 (mod 5), f(p) = −1 for other p ≠ 5, f(5) = 0, c = f∗1 (δ = 1/4).

Prior work on the flagship example: for 1 + 4L_{χ₄} = θ₃(1/2)², Bailey, Borwein, Crandall and Pomerance, J. Théor. Nombres Bordeaux 16 (2004) 487–518, Theorem 9.4 (p. 509) and the paragraph after it, give #ones among the first M digits ∼ C₀M/√(log M), C₀ ≈ 0.7996. This implies the one-bit case of Corollary 1.1 for χ₄ with an asymptotic constant, and the one-bit count in windows ηN ≤ H ≤ N. What is new here is short windows N^a ≤ H, all words, the discrepancy order and the general class.

## Exact statements

**Theorem A.** Assume (H1)–(H4) (the harmonic sum has a bounded remainder, and (H4) is the condition at p₀). For fixed 7/12 < a ≤ 1 and a fixed word w, for N ≥ N₀(w,a) and N^a ≤ H ≤ N: if w contains a 1 then #_w(N,H) ≍_{w,a} H/(log N)^κ; and H − #_{0^k}(N,H) ≍_{k,a} H/(log N)^κ. The upper bounds hold for every fixed a > 0 under (H1)–(H3). Theorem 10.3 extends the lower bounds to a > 0.53 using Kumchev, Q. J. Math. 53 (2002), main Theorem.

**Theorem B.** 1 − D_N(L) ≍ (log log N)/(log N)^κ.

**Corollary 1.2.** sup_x |D_N(x+L) − D_N(x)| = 1 − D_N(L) for every N ≥ 1 (attained at x = 0), hence of the order in Theorem B. The identity for every real z is Theorem 3.1 of the companion manuscript C. Anderson, *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*, v1.0 (same release).

**Theorem C.** For odd χ of any modulus and algebraic 0 < |q| < 1, Σ χ(m)qᵐ/(1−qᵐ) is transcendental.

Evidence labels: Theorems A, B and Corollary 1.1 are Lean-supported paper proofs. In Corollary 1.2 the identity is Kernel-verified (it is a result of the companion manuscript) and the order is a paper deduction. Theorem C is a paper proof.

## Proof sketch with every external input

1. **Odd-part reindexing (Lemma 2.2).** Write c(m) = 2^{V(m)}U(m), U odd, and t(m) = m − V(m) ∈ [m/2, m]. Then x_n = {A(n)} with A(n) = Σ_{t(m)>n} U(m)2^{n−t(m)} ≥ 0, so x_n ≤ A(n).
2. **Upper bounds (Lemma 3.1, Lemma 3.2, Prop. 3.3).** Apply Shiu, J. Reine Angew. Math. 313 (1980), Thm 1, p. 163, to U with modulus 2 and class 1 after separating powers of two (Shiu requires 0 < a < k). This gives Σ_{x−y<m≤x} U(m) ≪ y/(log x)^κ for y ≥ x^σ. The finite reindexing Σ_{n∈window} C(n+d) = Σ_{t(m)∈window+d} U(m) (Lean `arrival_sum`) then gives Σ_{window} A(n) ≪ H/(log N)^κ. Since x_n ≥ 1/2 implies A(n) ≥ 1/2, the number of ones is at most 2ΣA(n) (Lean `nonneg_one_bit_count_le`).
3. **Planting (Prop. 5.3).** Take θ = min(1/4, (a−ν_*)/2) and ν_* < ν < a−θ, with ν_* = 7/12 (or 0.53 via Kumchev). For squarefree m ≤ N^θ built from S∖{p₀} with ω(m) ≤ 2 log log N, put b = p₀^{2u}m and j₀ = k+2+ω(m), and let p ≡ a₀ (mod q₀) be prime with N ≤ bp − j₀ < N+H. Then c(bp)2^{−j₀} = (2u+1)2^{−k−1}, the midpoint of I_w. The number of such p is (1+o(1))Y/(φ(q₀) log X) with Y = H/b, by the single term q = q₀ of Perelli–Pintz–Salerno, Invent. Math. 79 (1985), Theorem p. 2 (y = x^θ, 7/12 < θ ≤ 1).
4. **Sieve (Lemma 4.7).** For each offset h = j − j₀ with 1 − R ≤ j ≤ J = ⌈10 log log N⌉ and j ≠ j₀, sift the integers n in the progression by n ≢ 0 (mod q) for primes q ≤ z = Y^{1/4} with q ∤ q₀, and also by bn+h ≢ 0 (mod q) for primes q ∉ S, q ∤ q₀, with (log N)² < q ≤ z. Selberg's sieve with trivial remainders, proved in full, bounds the survivors by O(Y(log log N)^κ/(log N)^{1+κ}). Primes with c(bp+h) > 0 survive unless q² | bp+h, which happens O(Y/(log N)²) times. Summed over the O(log log N) offsets the total is o(Y/log N). This uses κ > 0.
5. **Far tail.** For J < j ≤ N, bound c(bp+h) ≤ τ(bp+h) ≤ 2Σ_{d≤2√N} 1_{d|bp+h}. Montgomery–Vaughan, Mathematika 20 (1973), Thm 2, (1.10), p. 121, applies with d′ ≤ 2√N ≤ Y^β, β = 1/2 + 1/(4(a−θ)) < 1, which holds since a − θ > 1/2. Together these give Σ_p Σ_{j>J} c(bp+h)2^{−j} ≪ YJ2^{−J}. Markov's inequality then removes o(Y/log N) primes.
6. **Distinctness.** The start n determines j₀ (the first nonzero coefficient after n), hence bp, hence p (the largest prime factor) and m. Summing Y/log N over m with Σ 1/m ≫ (log N)^δ (Rankin) gives ≫ H/(log N)^κ occurrences.
7. **Discrepancy.** Upper bound: 1 − D_N ≤ 2^{−L} + (L−1)/N + L·F_N(1/2,1) (Lean `one_sub_discrepancy_le_one_bits`) with L = ⌈κ log₂ log N⌉. Lower bound: plant w = 1 with R = ⌊(κ/2) log₂ log M⌋ zero coefficients to the left. This gives R disjoint marked starts per planted one in [3ε, 1/2), ε = 2^{−R}/4, while [0, ε) carries mass at least 1/2. Then apply the Lean inequality `one_sub_discrepancy_ge_of_separated_mass`.
8. **Transcendence.** Hamieh–Murty, Int. J. Number Theory 12 (2016): Thm 1.1 (p. 766) at k = 1 for primitive χ. For imprimitive χ, Σ χ(m)qᵐ/(1−qᵐ) equals an algebraic constant plus half of F(τ) = Σ_{d|P} μ(d)χ*(d)E_{1,χ*}(dτ), a nonzero weight-one form on Γ₁(q*P) with algebraic coefficients. Thm 3.1 (p. 771) applies.

## Reproduction

- Manuscript and maps: `papers/06-multiplicative-lambert/` (`paper.pdf`, `VERIFICATION.md`, `LEDGER.md`).
- Lean, pinned at e4809cf (also [WeightedLambertIdentities.lean L21](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L21) for the finite Lambert head): [Phase17DiscrepancyBounds.lean L98](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L98), [L123](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L123), [SharpTranslation.lean L386](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386), [ErdosBorweinArrivals.lean L41](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L41), [WeightedLambertIdentities.lean L166](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/WeightedLambertIdentities.lean#L166).
- Finite certificate: `python -B scripts/phase17_multiplicative_lambert.py` (about 2 s; certifies 132,096 digits of each example).

## Steps on which review is wanted

1. **Lemma 4.7 and its use in Prop. 5.3:** the sieve of dimension 1+κ with lower cutoff z₀ = (log N)², the bound Π_{q≤w}(1−g(q)) ≪ (log z₀)^κ/(log w)^{1+κ}, and the count of the square-divisible exceptions.
2. **Lemma 4.4 and Lemma 10.2:** the derivation from Perelli–Pintz–Salerno, uniformly over X ≍ N/b, b ≤ N^θ; and the derivation of the fixed-progression lower bound for ν > 0.53 from the single term q = q₀ of Kumchev's (1.10) together with the minorant properties (i)–(ii) (checked against the author's posted text only).
3. **Far tail:** the divisor-sum reduction to Montgomery–Vaughan, including the nonunit-residue case and the injectivity of d ↦ (gcd(d,b), d/gcd(d,b)).
4. **Theorem B lower bound:** disjointness of the marked starts and the balance between ε and Δ.
5. **Theorem C, imprimitive case:** applicability of Hamieh–Murty Theorem 3.1 to the form F on Γ₁(q*P).
