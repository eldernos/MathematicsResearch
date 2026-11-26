# Dyadic Stoneham powers through degree fifteen

**Theorem.** Let *b* ≥ 3 be odd and let α be the positive-index Stoneham number defined below. For every rational polynomial *P* of degree 3 through 15, *P*(α) is normal in base *b*. The degrees added to the Phase 13 dyadic polynomial family are 4, 6, 8, 10, 12, 14 and 15. The quartic polynomial theorem has a Lean kernel proof. For the full degree range the proof combines an exhaustive integer certificate below with the leading-denominator normality criterion. The certificate covers every real cutoff in a shell. [Quartic normality](../../NormalityChecker/DyadicQuartic.lean) · [Kernel grid computation](../../NormalityChecker/DyadicMassCells.lean) · [Arithmetic certificate](../../scripts/phase14_dyadic_power_cells.py)

For a positive integer *d* write *R* for the shifted prefix, including each **ordered** positive-index tuple at its insertion. At position *n* put *k* = ⌊log₂ *n*⌋ and *t* = *n*/2ᵏ. Thus 1 ≤ *t* < 2. Write *e* for the exponent of the reduced dyadic denominator.

```math
\alpha=\sum_{j\ge1}\frac{1}{2^j b^{2^j}},
\qquad
R_{d,n}=\sum_{2^{j_1}+\cdots+2^{j_d}\le n}
\frac{b^{n-2^{j_1}-\cdots-2^{j_d}}}{2^{j_1+\cdots+j_d}}.
```

For *d* = 4 and *k* ≥ 4, the value of *e* is 4*k* − 8 on [1, 3/2), 4*k* − 7 on [3/2, 7/4), and 4*k* − 8 on [7/4, 2). For *d* = 15 and *k* ≥ 23, it is 15*k* − ℓ(*t*), with 45 ≤ ℓ(*t*) ≤ 64. At *t* = 133/128 the loss is exactly 64. All the endpoints below belong to the interval on their right.

## An integer recurrence for the infinite symmetric cut

Reflect each coordinate to its deficit *vᵢ* = *k* − *jᵢ*. For real *x*, give a vector of nonnegative deficits weight 2 raised to the sum of its entries. Let *M*ₐ(*x*) be the sum of these weights over vectors of length *a* with $\sum_i 2^{-v_i}\le x$, taken in the 2-adic integers. There are finitely many vectors of each weight exponent. In dimension zero put *M*₀(*x*) = 1 for *x* ≥ 0 and 0 otherwise. For *a* > 0 the mass is zero at *x* ≤ 0 and equals (−1)ᵃ at *x* ≥ *a*, by the geometric sum in each coordinate. Between those boundaries,

```math
M_a(x)=\sum_{m=0}^a {a\choose m}2^{a-m}M_{a-m}\bigl(2(x-m)\bigr).
```

Indeed, choose the *m* coordinates of deficit zero and subtract one from each remaining deficit. This partitions the cut exactly. The formula evaluates to an ordinary integer. A call with *m* > 0 decreases the dimension, and consecutive calls with *m* = 0 double a positive cutoff until it reaches the full-box boundary. The same proof evaluates strict cuts using *M*₀(*x*) = 1 for *x* > 0 and the full-box shortcut at *x* > *a*. For example, the weak quartic mass at 1 is 2304, its strict mass there is −4096, and its strict mass at 2 is −256. The shell starts with the weak cut at 1.

## A finite proof covering the continuous shell

Fix a precision *L*. Sort the deficits of each tuple and let *cᵢ* be the multiplicity of letter *i*. Put *w* = Σ *i cᵢ*, *C* = *d*! / ∏ *cᵢ*! and τ = Σ *cᵢ*2⁻ⁱ. The orbit enters at exactly τ and contributes *C*2ʷ. Only *w* < *L* can contribute modulo 2ᴸ. Discard τ ≥ 2, collect the remaining contributions at max(1, τ), and accumulate in increasing order. Between consecutive locations the residue is constant for **every real** *t*. Strict left limits at interior locations have the preceding residue. This gives a decision procedure for nonvanishing at a prescribed precision. A vanishing residue at one precision calls for a higher precision or an independent zero identity.

The checker chooses the next exponent *i* and the number *c* of its occurrences. Choosing their places multiplies the current multiplicity by the binomial coefficient for those positions. If *r* further letters remain, they have weight at least *r*(*i* + 1). Once that weight plus the weight already chosen and the current multiplicity order reach *L*, every completion vanishes. A second pruning bound comes from equalizing the remaining exponents under the weight budget. Replacing exponents *u*, *v* with *u* + 1, *v* − 1 when *u* + 1 < *v* decreases their insertion sum. The two nearest integers to the remaining mean therefore give its smallest possible value. A minimum already at 2 lies outside the shell. These bounds preserve every potentially nonzero orbit. A second verifier omits both pruning rules, enumerates all sorted tuples of weight below the precision, and computes the factorial multiplicity directly. At degree 15 it reproduces the full residue table from 7,298,397 multisets.

| Degree | Least passing bits | Nonzero jump locations including 1 | Sufficient first shell |
| ---: | ---: | ---: | ---: |
| 3 | 7 | 9 | 5 |
| 4 | 9 | 4 | 4 |
| 5 | 16 | 37 | 9 |
| 6 | 25 | 208 | 15 |
| 7 | 25 | 131 | 13 |
| 8 | 34 | 340 | 17 |
| 9 | 36 | 296 | 16 |
| 10 | 37 | 133 | 13 |
| 11 | 46 | 632 | 19 |
| 12 | 47 | 242 | 15 |
| 13 | 56 | 977 | 21 |
| 14 | 60 | 906 | 21 |
| 15 | 65 | 1302 | 23 |

For each row the script verifies a nonzero cumulative residue everywhere and exhibits an endpoint with residue 2ᴸ⁻¹. This proves minimality of the displayed precision. It also checks the independent integer recurrence on both sides of every listed jump. Thus there are **no zero-mass cells** of the actual weak cuts in any of these degrees. This is a statement about the Stoneham cuts. Even-dimensional symmetric upper sets in general can have exact zero mass.

### Transfer to the actual positive-index sum

Write *B* = 2ᵈᵏ *b*⁻ⁿ *R* in the rationals of odd denominator. A retained orbit with largest deficit *a* is present for *k* ≥ *a* + 1. Its contribution to *B* is the mass contribution multiplied by the inverse of *b* raised to its integer insertion position. For odd *b* and *j* ≥ 1, *b* raised to 2ʲ is 1 modulo 2ʲ⁺², by the odd-square congruence modulo 8 and repeated squaring. The product of all the inverse factors is consequently 1 modulo 2ᵏ⁻ᵃ⁺². Write *h* = *w* + ν₂(*C*). Each orbit of order *h* < *L* agrees with its frozen contribution at precision *L* as soon as

```math
k\ge\max\{a+1,\ a+L-h-2\}.
```

All other orbits have order at least *L*, whether they are absent because of the positive-index restriction or present with an odd radix unit. Taking the maximum over the finite list gives the last column. Therefore $B\equiv M_d(t)\pmod{2^L}$, and the exact denominator exponent is $e=dk-\nu_2(M_d(t))$ in the stated shells.

### Complete quartic calculation

There are only five contributing orbits at precision nine. The entries in the last column already include every permutation.

| Ordered increasingly by deficit | Cut | Contribution modulo 512 |
| --- | ---: | ---: |
| (2, 2, 2, 2) | 1 | 256 |
| (1, 1, 2, 2) | 3/2 | 384 |
| (1, 1, 1, 3) | 13/8 | 256 |
| (0, 2, 2, 2) | 7/4 | 256 |
| (1, 1, 1, 2) | 7/4 | 128 |

The four successive residues are 256, 128, 384 and 256. All five orbits have largest deficit at most three, and their radix units only need precision two bits. This proves the quartic profile from *k* = 4.

For completeness the prefix is empty for *n* < 8. On [8, 12), [12, 14), [14, 16), the denominator exponents are 4, 5, 3. To see this, normalize the numerator by 2¹². The successive unshifted insertion coefficients at positions 8, 10, 12, 14 are 256, 512, 384, 384. Between insertions multiply by *b* at every position. At each even endpoint, the earlier radix factors are even powers of an odd integer, hence 1 modulo 8. Reduction modulo 1024 gives respectively 256, 768, 128, 512. Multiplication by an odd radix preserves the order up to the next insertion.

### Complete degree-fifteen denominator losses

The table gives the left endpoint and loss for each maximal interval of constant order. Read **down** each pair of columns, then continue with the next pair. The last interval ends at 2.

| Start | Loss | Start | Loss | Start | Loss |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 59 | 41/32 | 56 | 25/16 | 50 |
| 33/32 | 63 | 21/16 | 54 | 13/8 | 49 |
| 133/128 | 64 | 11/8 | 53 | 53/32 | 50 |
| 67/64 | 62 | 45/32 | 55 | 27/16 | 48 |
| 17/16 | 58 | 91/64 | 58 | 7/4 | 47 |
| 9/8 | 57 | 183/128 | 59 | 57/32 | 48 |
| 37/32 | 58 | 23/16 | 52 | 29/16 | 46 |
| 19/16 | 56 | 3/2 | 51 | 15/8 | 45 |
| 5/4 | 55 | 49/32 | 52 | | |

## What survives on a zero cell?

Here is a first-order computation for any coordinate-permutation-invariant upper set *U* given by a fixed clipped alphabet. Choose *m* so that replacing every deficit by its minimum with *m* preserves membership. Such an *m* exists for a fixed upper set by Dickson's lemma. Let *F* be the homogeneous polynomial that sums the products of letters over all accepted clipped words. Use letters λᵢ = 2ⁱ for *i* < *m* and λₘ = −2ᵐ, the sum of the infinite tail. Thus *F*(λ) is the exact leading mass. Let *Sᵢ* be the mass of the section with its first coordinate clipped to *i*. Symmetry gives ∂ᵢ*F*(λ) = *dSᵢ*.

For *j* ≥ 1 define $\delta_j=(b^{-2^j}-1)/2^j$. The odd-square congruence gives δⱼ ∈ 4ℤ₂. For *k* ≥ *m*, the actual positive-index, radix-weighted letters of the reflected box are exactly λᵢ + 2ᵏ*hᵢ* with

```math
h_i=\delta_{k-i}\quad(i<m),\qquad
h_m=1+\sum_{j=1}^{k-m}\delta_j .
```

The tail identity sums 2ᵛ over *m* ≤ *v* < *k*, then restores the individual radix units. If *F*(λ) = 0, ordinary polynomial expansion gives the secondary congruence

```math
2^{-k} F(\lambda+2^k h)\equiv d\sum_{i=0}^m S_i h_i \pmod {2^k}.
```

In particular if *Sₘ* is odd and *k* > ν₂(*d*), the normalized numerator has exact order *k* + ν₂(*d*). The reduced dyadic denominator exponent is (*d* − 1)*k* − ν₂(*d*) after the odd radix is cleared. This supplies a secondary order even when arbitrary-depth leading-mass tests vanish. More generally the displayed congruence determines the exact order whenever its right side is nonzero modulo 2ᵏ. If that residue is zero, more terms of the polynomial expansion are needed.

In the square the actual cut on [3/2, 2) omits just the origin. Its mass is exactly 1 − 1 = 0. The tail section has mass −1, hence the reduced denominator is 2ᵏ⁻¹ for *k* ≥ 2. On [1, 3/2) the residue is 4 modulo 8. This classifies the square's zero and nonzero cells and recovers its secondary order. For every even dimension *d*, the clipped upper set omitting just the origin has the same zero and tail-section behavior. In the recurrence it occurs for *d* − 1/2 ≤ *x* < *d*. Its positive-index box omits the tuple with all indices *k*. For *k* ≥ 2 the cleared numerator is *Aₖ*ᵈ − 1, where *Aₖ* is the integer obtained from the axis sum by multiplying by 2ᵏ and by *b* raised to 2ᵏ. The square identity ν₂(*Aₖ*² − 1) = *k* + 1 and the lifting-the-exponent lemma applied to (*Aₖ*²)ᵈᐟ² − 1 give exact order *k* + ν₂(*d*) for **every** even *d* ≥ 2. For *d* > 2 later indices may already have entered the unrestricted power prefix at those positions, so the conclusion here concerns the restricted box. [Kernel even-box mass and numerator order](../../NormalityChecker/DyadicMissingDiagonal.lean) · [Actual square proof](../phase13/parameter-two-square.md)

### Secondary cancellation for an arbitrary fixed zero cut

There is a sharper dichotomy when the tail section has nonzero mass. Put $C_k=\sum_i S_i h_i$, let $s=\nu_2(b^2-1)-1$, and write $\delta$ for the 2-adic limit of the $\delta_j$. Squaring $1+2^j\delta_j=b^{-2^j}$ gives
$\delta_{j+1}=\delta_j+2^{j-1}\delta_j^2$. Thus all the $\delta_j$ and their limit have order *s* ≥ 2. Moreover $\nu_2(\delta-\delta_j)\ge j-1+2s$.

Suppose $S_m\ne0$, put $h=s+\nu_2(S_m)$ and let $a$ be the residue of $S_m+\delta\sum_{i<m}S_i$ modulo $2^h$. The finite sum of the $\delta_j$ in the last letter is a multiple of $2^s$. Consequently $C_k\equiv a\pmod{2^h}$ eventually. At any higher **fixed** precision $2^H$, the difference $C_{k+1}-C_k$ is eventually congruent to $S_m\delta$ because all the short letters have stabilized. This step has order exactly *h*, so the sequence visits every lift of *a* modulo $2^H$ infinitely often.

- If $a\ne0$, set $u=\nu_2(a)<h$. For all sufficiently large *k* the cleared numerator has exact order $k+\nu_2(d)+u$. The reduced denominator exponent is $(d-1)k-\nu_2(d)-u$.
- If $a=0$, the extra loss from $(d-1)k$ is unbounded. Choose arbitrarily large *H* and then a visit with $C_k\equiv0\pmod{2^H}$ and $k>H+\nu_2(d)$. The secondary congruence puts at least $k+H+\nu_2(d)$ factors of two in the numerator. This argument alone gives no lower bound tending to infinity for the remaining denominator.

If $S_m=0$, then $C_k\to\delta\sum_{i<m}S_i$. A nonzero sum gives a fixed secondary loss $\nu_2(d)+s+\nu_2(\sum_{i<m}S_i)$. When the sum also vanishes, the bound on $\delta-\delta_j$ gives $\nu_2(C_k)\ge k-O_m(1)$, with infinite order allowed. The denominator exponent is then at most $\max(0,(d-2)k+O_m(1))$. The floor at zero also covers an empty one-dimensional cut. All these statements concern a single clipped upper set as *k* varies. Uniformity across a family with increasing clipping depth would require further bounds. The square calculation for polynomial projections in Phase 13 uses the same stabilization of the radix units. [Quadratic analysis](../phase13/reviews/symmetric-degree.md#quadratic-projections-with-equal-valuations)

## Normality, scope and reproducibility

Clear the rational coefficients of *P* by a common positive integer. A nonzero leading coefficient costs its own fixed 2-adic order. Every strictly lower term has denominator dividing 2⁽ᵈ⁻¹⁾ᵏ, so eventually it cannot cancel the leading pole of order at least *dk* − (*L* − 1) − ν₂(*lead*). Up to position *N* the ordered products have only *O*((1 + log *N*)ᵈ) insertion positions. Their shifted real tails tend to zero by domination by the summable product of coefficient weights. On clean blocks the shifted prefix advances by multiplication by *b*. The fixed-support short-orbit estimate for an odd radix applies to the growing dyadic denominators, which are at most polynomial in the position. The arithmetic certificate gives normality, and rational scaling transfers it back. Multidimensional Weyl applied to all nonzero integral projections also gives joint uniform distribution for the powers with exponents 3 through 15 together with **either** exponent 1 or exponent 2. For a projection supported only on that last coordinate use the classical linear theorem or the proved square theorem. [Normality from a retained pole](../../NormalityChecker/StonehamPolynomialRetention.lean) · [Short-orbit estimate](../../NormalityChecker/SmoothOrbit.lean) · [Positive-index expansion](../../NormalityChecker/StonehamPolynomialExpansion.lean)

Lean expands the single-axis polynomial on an integer position grid, takes its fourth power, and certifies the four nonzero jumps by kernel reduction. Its existing internal monomial starts at index zero with multiplier two. It equals 2ᵈ times the positive-index power. The internal cut has threshold *t*/2, so every accepted deficit is at least one. Subtracting one from all coordinates gives the physical cut and divides its mass by 2ᵈ. This explains the four extra bits in the quartic kernel calculation. The quartic normality statement refers directly to the positive-index α. The first-shell refinements and the degree-15 table above have arithmetic proofs and independent finite tests. The degree-15 normality deduction uses the external integer certificate together with the conditional grid-to-normality step in Lean.

The Phase 13 symmetry argument treats every cyclically symmetric upper set in odd prime-power dimension. In degree 15, tuples of periods three and five obstruct the single-prime orbit deletion used there. In degree four the symmetric upper set missing only the origin already has zero mass. The present computation uses the position of each orbit in the actual cut. A general theorem for all higher degrees would need a nonvanishing argument, an adequate secondary-order bound on any actual zero cells, or another normality argument. The reported finite range supplies no general termination bound for a precision search. [Symmetric-degree review](../phase13/reviews/symmetric-degree.md) · [Phase 13 kernel theorem](../../NormalityChecker/StonehamOddDegree.lean)

Bailey–Crandall prove normality for the individual coprime-parameter generator. Wagner and Kano–Shiokawa construct families with polynomial normality under different hypotheses. For this generator the coefficient exponent is *j* and the radix exponent is 2ʲ, so *j*/2ʲ⁻¹ tends to zero and (log 2ʲ)/*j* is constant. These fail the divergence conditions in the cited Kano–Shiokawa construction. Vandehey's short-orbit bounds concern the analytic input; the specific issue here is the reduced denominator after a symmetric convolution. This comparison uses the source review and bibliography available in the checkout. Historical priority for the particular degrees remains unresolved. [Bailey–Crandall](https://doi.org/10.1080/10586458.2002.10504704) · [Kano–Shiokawa](https://www.math.keio.ac.jp/wp-content/uploads/2022/03/91006.pdf) · [Vandehey](https://arxiv.org/abs/1606.07911) · [Literature comparison and primary references](../../papers/01-stoneham-polynomials/REVIEW.md#literature-and-scope-of-priority-review)

Run from the repository root with the pinned Lean toolchain and Python 3. The degree-15 option prints the 26 intervals in order. The audit option adds the independent enumeration of all weight-bounded multisets. The default run checks 3066 actual quartic radix/position pairs. It also checks 183 degree-15 pairs using a positive-index recursion that chooses the multiplicity of the largest index. These include complete small shells, points on both sides of selected jumps starting at *k* = 23, and a late shell at *k* = 70.

```sh
lake build NormalityChecker.DyadicMassCells NormalityChecker.DyadicQuartic NormalityChecker.DyadicMissingDiagonal
python3 scripts/phase14_dyadic_power_cells.py --audit
python3 scripts/phase14_dyadic_power_cells.py --cells 15
```
