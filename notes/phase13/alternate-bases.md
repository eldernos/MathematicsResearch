# The Stoneham square in radix 48

**Theorem.** Let α be the standard Stoneham number with parameters 2 and 3, starting at index one,

```math
\alpha=\sum_{j=1}^{\infty}\frac{1}{3^j 2^{3^j}}.
```

Its square is binary normal and fails even simple normality in radix 48. The lower limiting frequency of the digit zero in radix 48 is at least *v* − ½, where *v* = 3/log₂ 48. The bound is approximately **0.0371567**, above the simple-normal frequency 1/48 ≈ 0.0208333. The same lower bound holds for the starting frequency of every fixed word consisting entirely of zeros. Every rational polynomial in α of degree at most two is nonnormal in radix 48. The zero-word assertion here concerns the square. [Binary normality and the exact square prefix](../stoneham-square.md) · [Lean proofs for radix 48](../../NormalityChecker/AlternateBaseStoneham.lean)

Write $`D_N(B,x)`$ for the supremum over intervals [*s*,*t*) ⊆ [0,1) of the absolute difference between *t* − *s* and the fraction of positions 0 ≤ *n* < *N* with fractional part {*B*ⁿ*x*} in that interval. With *u* = ½, Lean proves both bounds

```math
\liminf_{N\to\infty}D_N(48,\alpha^2)\ge v-u,
\qquad
\limsup_{N\to\infty}D_N(48,\alpha^2)\ge\frac{3(v-u)}{2v}.
```

The second lower bound is approximately **0.1037594**. The constants count positions supplied by a particular family of intervals. Other positions can contribute to the discrepancy. [Discrepancy theorem](../../NormalityChecker/AlternateBaseStoneham.lean) · [Counting at arbitrary cutoffs](../../NormalityChecker/AlternateBaseCoverage.lean)

## Where the zero digits come from

Set *Q* = 3ᵏ and let *x*ₖ be the partial sum for α through *j* = *k*. An ordered pair in the square inserts at 3ⁱ + 3ʲ. When both indices are at most *k* the location is at most 2*Q*. If either is greater, the location exceeds 3*Q*. Thus the entire prefix through 2*Q* equals *x*ₖ². Its denominator divides $`2^{2Q}3^{2k}`$. For a position *n* ≥ *Q*/2, the factor 48ⁿ = 2⁴ⁿ 3ⁿ clears both exponents for all sufficiently large *k*. [Square expansion](../stoneham-square.md)

The missing tail is positive. Its binary exponent is at least 3*Q*, and the sum of the remaining coefficient weights 3⁻ⁱ⁻ʲ tends to zero. Consequently 48ⁿ(α² − *x*ₖ²) tends to zero uniformly for *n* ≤ *vQ*, since $`48^n\le 2^{3Q}`$ there. The interval of certified positions is

```math
\tfrac12 Q\le n<vQ,\qquad v=\frac{3\log 2}{\log 48}>\tfrac12.
```

The strict inequality follows from 48 < 2⁶. Given a fixed length *m*, the fractional parts throughout every sufficiently late interval lie in [0,48⁻ᵐ). This is the radix-48 cylinder for *m* zeros, with overlapping starts counted. The exact comparison *v* − ½ > 1/48 follows from 48²⁵ < 2¹⁴⁴. [Kernel proofs of the zero windows and the zero-digit excess](../../NormalityChecker/AlternateBaseStoneham.lean)

## Standard polynomials in an alternate radix

Let *b*, *c* ≥ 2 be integers, *d* ≥ 1 a degree bound, *P* a rational polynomial of degree at most *d*, and *a* a positive integer. Put *B* = *b*ᵃ*c* and

```math
\alpha_{b,c}=\sum_{j=1}^{\infty}\frac{1}{c^j b^{c^j}}.
```

**Theorem.** Every such $`P(\alpha_{b,c})`$ is nonnormal in radix *B* whenever *a* > (*c*ᵈ − 1) logᵦ *c*. When *d* < *c*, it also suffices that *a* > *d* logᵦ *c*/(*c* − *d*). Either condition works simultaneously for all rational coefficients through the chosen degree. The alternate-radix proof applies to composite *c* and to parameters with common factors. For the construction-radix conclusion in Paper I, take *c* an odd prime power coprime to *b* and *P* nonconstant. Each such polynomial image is then normal in *b* and fails absolute normality. The degree bound is fixed before the radix threshold is chosen. [Alternate-radix theorems](../../NormalityChecker/AlternateBaseStoneham.lean) · [Paper I](../../papers/01-stoneham-polynomials/paper.pdf) · [Construction-radix proof notes](../stoneham-powers-products.md)

### A gap and an integer prefix

For a degree *r*, the locations are the sums of *r* powers *c*ʲ with *j* ≥ 1. The empty sum gives location zero. Suppose integers 0 < *U* < *V* have the following property for every *r* ≤ *d* and *Q* = *c*ᵏ. Every such location is at most *UQ* or at least *VQ*. Define the observation endpoints

```math
u=\frac{U}{a},\qquad v=\frac{V\log b}{\log B}.
```

The window has positive length precisely when *a*(*V* − *U*) > *U* logᵦ *c*. Take a positive common denominator *D* for all coefficients of *P*. Expand $`DP(\alpha_{b,c})`$ in ordered tuples, and retain exactly the locations at most *UQ*. A common denominator is $`b^{UQ}c^{d\lfloor\log_c(UQ)\rfloor}`$. For *n* ≥ *uQ*, *an* ≥ *UQ* and *n* eventually exceeds the latter logarithmic exponent. Hence *B*ⁿ times this prefix is an integer. This argument uses divisibility throughout and accommodates cancellation between degrees and coefficient signs. [Window and denominator proof](../../NormalityChecker/AlternateBaseStoneham.lean)

Every omitted term has location at least *VQ*. For each degree *r*, the absolute coefficient weights have finite sum, since the sum over *j* ≥ 1 of *c*⁻ʲ is 1/(*c* − 1). Their total on locations ≥ *VQ* therefore tends to zero. For *n* < *vQ*, the multiplier *B*ⁿ is at most *b* to the power *VQ*. The difference between the shifted value and its integer prefix tends uniformly to zero on the window, including positions next to its upper endpoint. The Lean proof reuses the true shifted-tail theorem at radix-*b* position *VQ* − 1, where the prefix still contains exactly the retained terms. [Polynomial expansion and true tail](../../NormalityChecker/StonehamPolynomialExpansion.lean) · [Integer clearance for the standard starting index](../../NormalityChecker/AlternateBaseStoneham.lean)

### Gaps in every degree

For *d* < *c*, use *U* = *d* and *V* = *c*. Either all powers in the tuple are at most *Q*, or one of them is already at least *cQ*. For the square, this gives *U* = 2, *V* = 3 and the radix 48 at *a* = 4.

For unrestricted *d*, use *U* = *c*ᵈ − 1 and *V* = *c*ᵈ. The following integer observation explains this choice. If *S* is a sum of *r* powers of *c*, *M* is divisible by *c* to the power *k* + *r*, and *S* < *M*, then *M* − *S* ≥ *c*ᵏ. Indeed, if every summand is divisible by *c*ᵏ, the positive difference is a multiple of *c*ᵏ. Otherwise remove one summand smaller than *c*ᵏ. Induction on the number of terms, now with *k* + 1, gives a deficit of at least *c*ᵏ⁺¹ before restoring the summand. After restoration at least *c*ᵏ remains. Apply this with *M* = *c*ᵈ*Q* and *r* ≤ *d*. [Formal normalized-gap lemmas](../../NormalityChecker/AlternateBaseStoneham.lean)

## Discrepancy at every cutoff

Both choices above satisfy *v* ≤ *cu*. Consider the disjoint windows [*uc*ᵏ,*vc*ᵏ) and put *w* = *v* − *u*. Immediately before the window of scale *Q*, the preceding windows contain *wQ*/(*c* − 1) + O(*k*) integer positions. At its right endpoint the count is *cwQ*/(*c* − 1) + O(*k*). Each endpoint rounding costs at most one per window. Dividing by the corresponding cutoff gives the lower and upper limiting shares of the union,

```math
\rho_- = \frac{v-u}{(c-1)u},\qquad
\rho_+ = \frac{c(v-u)}{(c-1)v}.
```

For an intermediate cutoff, the count grows by one per position inside the current window, then stays constant until the next starts. Its ratio to the cutoff increases on the first segment and decreases on the second. Thus the left-endpoint share controls **every** sufficiently large cutoff up to an error tending to zero. A fixed number of early windows has zero limiting share. [Kernel count with endpoint rounding and the partial last window](../../NormalityChecker/AlternateBaseCoverage.lean)

For an integer polynomial the shift on these windows can approach an integer from either side. For each fixed 0 < δ < ½, all sufficiently late windows miss the single middle interval [δ,1 − δ). Its frequency deficit is at least the window share minus 2δ. Letting δ decrease to zero gives discrepancy lower bounds ρ₋ and ρ₊. For the square the sign of the tail also locates the visits at the zero end itself. [Integer-window discrepancy](../../NormalityChecker/AlternateBaseWindows.lean)

For rational coefficients apply this to *y* = $`DP(\alpha_{b,c})`$. The inverse image of an interval under multiplication by *D* modulo one is a union of *D* disjoint intervals. At **each** prefix length this gives $`D_N(B,Dx)\le D\,D_N(B,x)`$. Hence the lower bounds for the original polynomial are $`\rho_-/D`$ for the liminf and $`\rho_+/D`$ for the limsup. One may use the least common denominator. Rational translations and nonzero rational scalings preserve qualitative normality and nonnormality. Discrepancy can change under such operations. For example, in base 2 the constant zero has limiting discrepancy 1, whereas the orbit of 1/3 alternates between 1/3 and 2/3 and has limiting discrepancy 2/3. [Finite-prefix dilation inequality](../../NormalityChecker/AlternateBaseDilation.lean) · [Polynomial discrepancy](../../NormalityChecker/AlternateBaseStoneham.lean) · [Affine normality equivalences](../../NormalityChecker/FourierTest.lean)

## Relation to the literature

Bailey and Borwein’s Theorem 2 proves nonnormality of the generator in radices *B* = *b*ᵖ*c*ᑫ*r* under their hypotheses. Example 1 explicitly lists **48** for the generator with parameters 2 and 3. Their proof clears the prefix of the degree-one series and locates long zero strings. Equations (19)–(22) add the lengths of successive strings, using the cutoff $`c^m+Z_m`$. For *p* = *a*, *q* = *r* = 1 their condition is precisely the degree-one coordinate-gap condition above. For *p* = 1 their endpoint constant is ρ₊. For larger *p*, the right endpoint of the current string is near $`c^m/p+Z_m`$, which is the cutoff used for ρ₊ here. Their Theorem 3 treats sums of two generators in certain common alternate radices. Squaring introduces the pair locations 3ⁱ + 3ʲ. These determine the distinct clearance and tail endpoints for the present square. Bailey and Borwein include the index-zero term 1/*b*. The present square always uses the positive-index series, and the polynomial theorem also covers rational changes of the generator’s origin by polynomial substitution. [Bailey–Borwein, §§3–4](https://www.davidhbailey.com/dhbpapers/nonnormality.pdf) · [Published article](https://doi.org/10.1007/s11139-012-9417-3)

Stoneham and Bailey–Crandall concern normality of the individual generators in the construction radix. Wagner and Kano–Shiokawa constructed rings with normality and nonnormality in specified bases using other lacunary schedules. For the standard schedule, the exponents in the notation of Kano–Shiokawa are λⱼ = *j* and μⱼ = *c*ʲ. Here λⱼ/μⱼ₋₁ tends to zero and (log μⱼ)/λⱼ equals log *c*. Hypotheses (15)–(16) require both quantities to diverge. Paper I gives the construction-radix comparison in detail. The gap argument here supplies an explicit alternate radix for each fixed degree bound of this particular generator. The question of normality in radix 3 remains separate. [Stoneham](https://doi.org/10.4064/aa-22-3-277-286) · [Bailey–Crandall](https://doi.org/10.1080/10586458.2002.10504704) · [Wagner](https://doi.org/10.1006/jnth.1995.1114) · [Kano–Shiokawa](https://doi.org/10.1007/BF02760950) · [Paper I literature comparison](../../papers/01-stoneham-polynomials/REVIEW.md) · [Radix-three results for the generator](../ternary-stoneham-complexity.md)

The four Lean modules can be checked together from the repository root with `lake build NormalityChecker.AlternateBaseStoneham`.
