# Independent review of odd prime-power degrees on the dyadic Stoneham axis

**Verdict.** Fix an odd integer *b* ≥ 3, an odd prime *q* and an integer *r* ≥ 1. Put *d* = *q*ʳ and let α be the standard positive-index Stoneham number with terms $2^{-j}b^{-2^j}$ for *j* ≥ 1. Every rational polynomial of degree exactly *d* takes a base-*b* normal value at α. The cubic conclusion allows every rational quadratic, linear and constant coefficient. I find the proof valid. This is a paper deduction from the baseline `944e0c4`. The baseline Lean statements for polynomial normality require an odd **denominator** prime. Here the denominator prime is 2 and *q* controls the degree. [Baseline theorem correspondence](../../../papers/01-stoneham-polynomials/CORRESPONDENCE.md)

## The polynomial congruence

Let ℕ start at zero and let *U* be a nonempty upper set in ℕᵈ invariant under one full cyclic rotation. For each total weight *s* the finite slice of *U* is a union of rotation orbits. Orbit sizes divide *q*ʳ, so each orbit of size greater than one contributes zero modulo *q*. In dimension nine, for example, a nonconstant tuple with period three has orbit size three. The only one-element orbits are constant tuples. The diagonal meets *U* because the maximum coordinate of any member gives a diagonal tuple above it. The diagonal indices in *U* therefore form a tail beginning at some *M* ≥ 0.

Write $F_U(z)=\sum_{v\in U} z^{\sum_i v_i}$. The slice argument gives the following identity in the formal power series ring over the field with *q* elements.

```math
(1-z^d) F_U(z) = z^{dM}.
```

Over the integers, the finite orthant expansion gives $K_U(z)=(1-z)^d F_U(z)$ in $\mathbb Z[z]$. Frobenius gives $(1-z)^d=1-z^d$ in characteristic *q*. Comparing coefficients yields the stronger polynomial congruence $K_U(z)\equiv z^{dM}\pmod q$. Hence $K_U(2)\equiv 2^M\not\equiv0\pmod q$. Evaluation at 2 takes place **after** obtaining a polynomial identity. Independently, the original series at 2 converges in the 2-adic integers, where its sum is $(-1)^d K_U(2)$. No evaluation of the infinite series at 2 in the reals or the finite field is needed. [Orthant proof](../../../papers/01-stoneham-polynomials/paper.tex#L127)

The hypotheses matter. In dimension three, the asymmetric upper set $(\mathbb N^2\setminus\{(0,0)\})\times\mathbb N$ has numerator $2z-z^2$, which vanishes at 2. For every even *d*, the fully symmetric upper set omitting just the origin has numerator $1-(1-z)^d$, which also vanishes at 2. For degree 15, rotation can have orbits of sizes 3 and 5, so dropping all nonconstant orbits modulo a single prime would be invalid. These examples delimit the argument and leave normality in other degrees a separate question.

## Uniformity and the passage to a polynomial

Fix a common anchor in the upper sets. Coordinatewise limits of their indicators preserve membership of the anchor, upper closure and cyclic symmetry. This is a closed subset of the compact product of copies of $\{0,1\}$ indexed by ℕᵈ. The 2-adic mass modulo $2^L$ depends only on the finitely many tuples of weight below *L*. If no common *L* detects every mass, a sequence with valuations tending to infinity has a convergent subsequence whose limit has zero mass. The polynomial congruence excludes this. The anchor is essential. Translating the whole orthant by $(m,\ldots,m)$ gives valuation *dm*. [Existing compactness argument](../../../NormalityChecker/StonehamPolynomialOrthant.lean#L157)

At a positive position *n*, put $k=\lfloor\log_2 n\rfloor$ and $t=n/2^k\in[1,2)$. A prefix of αᵈ includes every **ordered** tuple of positive indices satisfying $s(j)=\sum_i2^{j_i}\le n$, with its full multiplicity. Under $v_i=k-j_i$ the infinite cut is $U_t=\{v:\sum_i2^{-v_i}\le t\}$. It is permutation invariant and contains the constant tuple with entries $J=\lceil\log_2 d\rceil$. Actual tuples satisfy $v_i<k$. For $k\ge 2L$, all points with weight below *L* satisfy this restriction and have $j_i\ge L$. Since *b* is odd, Euler's theorem gives $b^{2^{j_i}}\equiv1\pmod{2^L}$. For the true shifted prefix $R_{d,n}=\sum_{s(j)\le n}2^{-\sum j_i} b^{n-s(j)}$, it follows that

```math
2^{dk} b^{-n} R_{d,n} \equiv F_{U_t}(2) \pmod {2^L}.
```

This bounds the loss in the denominator by *L* − 1 at every sufficiently late position, including insertion endpoints. The zeroth index would change the finite prefix. The formal development uses a zero-index internal series and recovers the public positive-index series by shifting the multiplier and rescaling. [Index conversion](../../../NormalityChecker/StonehamPolynomial.lean#L40) · [Prefix and radix factors](../../../NormalityChecker/StonehamPolynomialPrefix.lean#L116)

Clear the rational coefficients once. A leading integer coefficient *A* ≠ 0 costs at most $v_2(A)$ additional powers of 2. Every lower-degree prefix, including its integer coefficient, has denominator dividing $2^{(d-1)k}$. Its sum has the same bound. For large *k* the leading pole is strictly larger, so it survives addition. The degree-zero prefix is the integer $b^n$. For the resulting polynomial the denominators grow uniformly, are powers of 2 and are at most $n^d$. The real shifted tails tend to zero by domination by $2^{-\sum j_i}$ for each monomial. At most $O((1+\log N)^d)$ tuples insert through *N*. Removing the blocks meeting those locations costs $o(N)$ for block length $\lfloor\sqrt N\rfloor$. On the other late blocks the prefixes advance by multiplication by *b*, and the fixed-support short-orbit theorem applies at the prime 2 for odd *b*. Weyl's criterion gives normality for the cleared polynomial and rational scaling transfers it back. None of these steps requires the lower powers to be normal on their own. [Real tails](../../../NormalityChecker/StonehamPolynomialExpansion.lean#L74) · [Short-orbit estimate](../../../NormalityChecker/SmoothOrbit.lean#L207) · [Polynomial and rational projection proof](../../../papers/01-stoneham-polynomials/paper.tex#L259)

Three scope extensions follow from the argument.

- A leading power of one generator $\alpha_{b^m,2}$ with fixed positive *m* still has a symmetric cut. Arbitrary strictly lower-degree products of $\alpha_{b^{m_i},2^{e_i}}$ with positive integer parameters are allowed. Each included tuple has $e_i j_i\le k$, which suffices for the upper denominator bound on those products. Varying multipliers or strides within the **leading** product requires separate evidence of symmetry or nonvanishing.
- Distinct powers with exponents chosen from 1 and the odd prime powers have jointly uniform base-*b* shifts. Each nonzero integer projection has one of those leading degrees. Degree one follows from classical Stoneham normality and rational affine invariance. A joint statement that also includes both exponents 1 and 2 would require every quadratic projection.
- Separately, if all strides in the leading dyadic product have a common divisor *g* ≥ 2, use weights $e_i/g$ and evaluate their orthant numerator at $2^g$. Its integer value is 1 modulo $2^g-1$, since the numerator at 1 is 1. The same compactness and denominator argument works in every degree, with arbitrary positive multipliers in that leading product. The univariate case $\alpha_{b,2^g}$ already appears in the baseline note's composite-parameter deduction, which treats every even parameter greater than 2 coprime to the radix. [Weighted numerator and denominator arguments](../../../papers/01-stoneham-polynomials/paper.tex#L127) · [Baseline composite-parameter scope](../../stoneham-powers-products.md#related-parameters-and-the-limit-of-the-argument)

## An exact check for cubes

For *d* = 3, precision 7 suffices for the actual cuts. Sum $2^{v_1+v_2+v_3}$ over ordered nonnegative triples of total weight below 7 and $\sum_i2^{-v_i}\le t$. The table lists all new cuts below 2, with all earlier contributions included in the first entry. Each residue applies from its listed left endpoint up to the next one.

| Cut interval | Left endpoints of cells | Respective mass residues modulo 128 |
| --- | --- | --- |
| [1, 9/8) | 1, 17/16 | 32, 96 |
| [9/8, 5/4) | 9/8 | 64 |
| [5/4, 3/2) | 5/4, 21/16, 11/8 | 48, 48, 112 |
| [3/2, 2) | 3/2, 49/32, 25/16, 13/8, 7/4 | 40, 40, 104, 72, 120 |

For *k* ≥ 7, each retained tuple of weight *w* ≤ 6 has $k-v_i\ge 7-w\ge1$. Thus each radix factor is 1 modulo $2^{7-w}$ before multiplication by $2^w$. The loss from the denominator exponent *3k* is exactly 5 on $[1,9/8)$, 6 on $[9/8,5/4)$, 4 on $[5/4,3/2)$ and 3 on $[3/2,2)$. This verifies the cubic denominator estimate by finite arithmetic without an appeal to compactness. The accompanying script also checks the congruence for all 19 nonempty cyclic upper sets generated in $\{0,1,2\}^3$. The baseline also contains a general finite cell checker using multiset multiplicities. An independent positive-index recurrence verifies the four losses at all 2,688 radix-position pairs for *b* = 3, 5, 7 and *k* = 7, 8, 9. [Independent check](check_symmetric_degree.py) · [Baseline cell checker](../../../scripts/stoneham_power_cells.py)

## Quadratic projections with equal valuations

The symmetric upper set omitting the origin actually occurs for the square throughout $3/2\le t<2$. Write $S_k=\sum_{j=1}^k 2^{-j}b^{-2^j}$ and $L_k=2^{-k}b^{-2^k}$. The linear prefix is $b^n S_k$ and the quadratic prefix is $b^n(S_k^2-L_k^2)$, as only the pair $(k,k)$ is omitted from the *k* by *k* square. For integers *A* ≠ 0 and *B*, set

```math
\delta_j=\frac{b^{-2^j}-1}{2^j},\qquad H_k=1+\sum_{j=1}^k\delta_j,\qquad T_k=H_k-1+\delta_k.
```

In the 2-adics, $S_k=H_k-2^{-k}$ and $L_k=\delta_k+2^{-k}$. Expanding $A(S_k^2-L_k^2)+B S_k$ leaves a 2-adic integer minus $2^{-k}(2A+B+2A T_k)$. The true prefix is dyadic, and $b^n$ is a 2-adic unit. Its reduced denominator is exactly $2^{\max(0,k-v_2(2A+B+2A T_k))}$, with the usual convention for zero. An integer constant coefficient does not affect this calculation.

Put $s=v_2(b^2-1)-1\ge2$. Then $v_2(\delta_1)=s$ and $\delta_{j+1}=\delta_j+2^{j-1}\delta_j^2$, so every $\delta_j$ has valuation *s*. At each fixed precision $2^h$ with *h* > *s*, their residues eventually stabilize at a value of valuation *s*. The successive differences $T_{k+1}-T_k=2\delta_{k+1}-\delta_k$ then equal that same residue modulo $2^h$. Consequently $T_k$ visits **every** multiple of $2^s$ modulo $2^h$ infinitely often.

It follows that if $v_2(2A+B)<v_2(2A)+s$, the valuation in the denominator formula is the fixed value $v_2(2A+B)$. On the earlier part $1\le t<3/2$ the square has exact loss 2 from *2k* for *k* ≥ 3. At reflected weight two, $(1,1)$ contributes and the pair $(0,2),(2,0)$ enters together, so the scaled numerator is 4 modulo 8. Lower weights are absent. The quadratic pole here eventually dominates every linear term. Thus the indicated coefficient condition gives normality of $A\alpha^2+B\alpha$ on combining both parts of the shell. It includes the pure square and some cases with $v_2(B)=v_2(2A)$.

If $v_2(2A+B)\ge v_2(2A)+s$, the additional loss relative to *k* on the upper part of the shell is unbounded. Indeed the target $-(2A+B)/(2A)$ belongs to $2^s\mathbb Z_2$, so the visitation statement gives arbitrarily large *k* with arbitrarily high precision of cancellation. In particular this happens for $X^2-2X$ in every odd radix. At *b* = 3, *k* = 3, *n* = 12, the prefixes of α and α² are $249399/8$ and $7315/4$, and their quadratic projection is the integer −60521. Unbounded loss relative to *k* leaves open whether the reduced pole itself tends to infinity. This obstruction to a bounded-loss proof supplies no counterexample to normality or to the cubic result.

## Literature and evidence

I checked the literature comparison and references available in the checkout. Bailey–Crandall cover the single coprime-parameter generator. Wall covers rational affine changes. Wagner and Kano–Shiokawa treat families of polynomially normal numbers under growth hypotheses. Here the relevant exponents $\lambda_j=j$, $\mu_j=2^j$ have $\lambda_j/\mu_{j-1}\to0$ and $(\log\mu_j)/\lambda_j=\log2$; the two divergence hypotheses quoted for the Kano–Shiokawa construction fail. Vandehey supplies the analytic short-orbit input. Mira's cited joint theorem concerns distinct linear series, and the cited two-summand result concerns sums of generators. I found no exact antecedent for the dyadic cubic or odd prime-power-degree statement in those local comparisons. Historical priority remains unresolved. The new congruence, degree extension and quadratic analysis in this report have paper proofs. The Python computations check finite instances independently. [Baseline literature review](../../../papers/01-stoneham-polynomials/REVIEW.md#literature-and-scope-of-priority-review) · [Bibliography](../../../papers/01-stoneham-polynomials/references.bib)
