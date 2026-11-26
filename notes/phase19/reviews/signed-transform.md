# Review: "An infinite signed Mahler transform of the logarithm"

Scope: the final section of `notes/phase19/taylor-periods.md` (checkout `MathematicsResearch-phase19`, HEAD 8fd9874 plus uncommitted edits). Independent check; other tracks not re-reviewed.

**Verdict: no errors found. Two minor wording suggestions.**

## Checks

1. **Identity and signs.** ∏_{j≥0}(1+x^{2^j}) = 1/(1−x) on 0<x<1 (telescoping, then J→∞). Taking logs, −log(1−x) = Σ_j log(1+x^{2^j}) = Σ_j Σ_k (−1)^{k−1}x^{k2^j}/k. Swapping sums is justified by absolute convergence, since Σ_j Σ_k x^{k2^j}/k = Σ_j −log(1−x^{2^j}) < ∞. This gives Σ_k (−1)^{k−1}H(x^k)/k, as stated. ✔
2. **Remainder sign and bounds.** log(1+z) − T_K(z) = (−1)^K ∫_0^z u^K/(1+u) du, so (−1)^K(log 2 − A_K) = Σ_j ∫_0^{2^{−2^j}} u^K/(1+u) du is a sum of positive terms, all with the same sign. ✔
   - Lower bound: keep j=0 and use 1/(1+u) ≥ 2/3 on [0,1/2], giving (2/3)·2^{−(K+1)}/(K+1). ✔
   - Upper bound: use 1/(1+u) ≤ 1 and enlarge the powers 2^j to all integers m≥1, giving Σ_m 2^{−m(K+1)}/(K+1) = 2^{−(K+1)}/((K+1)(1−2^{−(K+1)})). ✔
   - Numerically confirmed for K=1..59 at 80 digits.
3. **Threshold.** The two bounds differ by a factor between 2/3 and 1+o(1), so 2^N|log 2 − A_K| → 0 exactly when K+1+log₂(K+1) − N → +∞. "Sharp up to an absolute factor" is right. It follows that K ≥ N − log₂N − ω(1) = N − O(log N), and the O is attainable, so the "or K larger" clause is accurate. ✔
4. **Odd-part coefficient.** For k=d2^a, H(x^{d2^a}) = H(x^d) − Σ_{i<a} x^{d2^i}. For odd d, the coefficient of H(2^{−d}) is (1/d)(1 − Σ_{a=1}^m 2^{−a}) = 1/(d2^m) with m=⌊log₂(K/d)⌋, exactly as stated (the sign is + for a=0 and − for a≥1 because k is then even). Checked exactly for K∈{3,7,20,50}, d∈{1,3,5,7}. For d=3 and K≥3 the coefficient is 1/(3·2^m), which is nondyadic. ✔ The "no +j" remark is correct: the exponents are d2^j directly. The kernel-exclusion conclusion also depends on the isolated-insertion criterion in `logarithm-rays.md`, which was not re-audited here.
5. **Prime-band transfer.** In the radix-2 prefix to N, the term of A_K at (k,j) is ±2^{−k2^j}/k, with k2^j ≤ N. If an odd prime p ∈ (N/2, N] divides k then k ≥ p > N/2, so k=p and j=0 (2p > N), and p ≤ K is needed for the term to be present. So 2^{−p}/p is the only term with p in its denominator, and the p-adic valuation of the prefix is exactly −1. Brute-force check for N∈{40,64,100}, K∈{N−8,N,N+30}. ✔ At the moving cutoff, K ≥ N−O(log N) leaves (N/2, N−O(log N)] with ~N/(2 log N) primes, which is the hypothesis H ≫ N/log N of the earlier lemma, with the same prefix length N. The earlier proof used only the set of primes dividing M, not the shape of the numerator, so it transfers verbatim with the same constant 1/(2 log 2). Deleting one axis is covered. Terms with k>N contribute nothing to the prefix, so K ≫ N changes nothing. ✔

## Suggestions (wording, not errors)

- Say explicitly that the order bound is for the prefix of A_K of length N, with K=K(N) tied to N by the threshold. As written, the sentence "Consequently its odd denominator ..." could be read as a statement about the fixed A_K.
- "Quantified moving-tail obstruction" could say what is obstructed: complete-period methods applied to the approximant A_{K(N)}. The section does not claim anything for the orbit of log 2 itself, and it should not.

## Historical precedent and scope

- The product ∏(1+x^{2^j}) = 1/(1−x) is Euler's, from his partition theory (*Introductio in analysin infinitorum*, 1748; it expresses uniqueness of binary expansions). The first display is therefore not a new identity. The element that is new in this repository is the use of H(x^k) as the rows of an expansion at x=2^{−k}.
- H(x)=Σx^{2^j} is the standard lacunary Mahler function (H(x²)=H(x)−x). At x=1/2 it gives the Kempner–Mahler number, known transcendental (Kempner 1916, Mahler 1929). I did not verify theorem numbers; cite after checking.
- Scope as "classical obstruction": acceptable only as a transfer of the Phase 18/Taylor prime-band argument to a more general family of approximants. It is not a new obstruction on log 2, and the section's closing sentence says this correctly. The phrase "outside the finite differential algebra" is accurate, since the sum is infinite in k. It should not be taken to say that the infinite series escapes the obstruction. The section shows that the retained length K must be ≈ N, so the approximant remains in the same prime-band regime.
