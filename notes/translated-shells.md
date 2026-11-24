# Rational translations of signed Stoneham expansions

Fix an integer base *b* ≥ 2, a prime *p* coprime to *b*, and a bounded sequence of integers *c*₀, *c*₁, …. Put *a*₀ = *c*₀ and *a*ⱼ = *c*ⱼ − *pc*ⱼ₋₁ for *j* ≥ 1. The associated real number is

```math
X=\sum_{j=0}^{\infty}\frac{a_j}{p^j b^{p^j}}.
```

Among the integers 0 ≤ *n* < *N*, let *Z*(*N*) count those in a shell [*p*ʲ, *p*ʲ⁺¹) with *c*ⱼ = 0. Position 0 belongs to the regular part. Write $`D_N(y)`$ for the supremum, over half-open intervals *I* ⊆ [0,1), of the absolute difference between their length and the proportion of the first *N* fractional parts {*b*ⁿ*y*} in *I*. Put $`D_\infty(y)=\limsup_N D_N(y)`$. For rational *r*, let νᵣ be uniform measure on one period of the eventual orbit of *r* under multiplication by *b* modulo 1. Write *D*(*r*) for its interval discrepancy.

**Theorem.** For every nonzero integer *m* and every rational *r*, all prefix cutoffs satisfy

```math
D_N(mX+r)-\frac{Z(N)}{N}D(r)\longrightarrow 0.
```

Consequently *D*∞(*mX* + *r*) = *D*∞(*X*) · *D*(*r*). Both statements and the convergence of the rational prefix discrepancy to *D*(*r*) are kernel-verified. The limsup theorem permits zero patterns with oscillating densities. [Prefix theorem and product formula](../NormalityChecker/TranslatedShells.lean#L179) · [Untranslated theorem](signed-shell-discrepancy.md)

## Proof for every cutoff

Let *P*ₙ be *b*ⁿ times the sum truncated at the last insertion *p*ʲ ≤ *n*. The signed tail *b*ⁿ*X* − *P*ₙ tends to zero. For *p*ʲ ≤ *n* < *p*ʲ⁺¹ the rational prefix differs by an integer from

```math
\frac{b^{n-p^j}c_j}{p^j}.
```

Thus on a zero shell *P*ₙ is integral. On other shells its reduced denominator divides *p*ʲ and is at least *p*ʲ/*C* if |*c*ⱼ| ≤ *C*. These facts hold for both signs of the phases. [Prefix identity and signed tail](../NormalityChecker/SignedPhases.lean#L52)

**Regular positions.** After a fixed index *s*, the reduced denominator of *b*ⁿ*r* divides a fixed *q* coprime to *b*. Indeed these denominators decrease by divisibility. At their minimum a further multiplication by *b* already preserves the denominator. Euler’s theorem then supplies a period *L*, also for *q* = 1. Set *Y*ₙ = *mP*ₙ + *b*ⁿ*r*. Its denominator divides *qp*ʲ. Conversely the identity *P*ₙ = (*Y*ₙ − *b*ⁿ*r*)/*m* gives

```math
\frac{p^j}{C\,|m|\,q}\leq \mathrm{den}(Y_n)\leq qp^j.
```

All sufficiently late regular blocks therefore have arbitrarily large denominators supported on the fixed primes dividing *pq*, coprime to *b*. Within one shell the prefixes form an exact rational radix orbit. The fixed-support estimate, with the signed tail added back, supplies uniform interval counts on these blocks. [Rational preperiod and period](../NormalityChecker/RationalOrbitCycle.lean#L13) · [Uniform short-orbit estimate](../NormalityChecker/SupportDiscrepancy.lean#L35)

More explicitly, choose *k* with *B*² ≤ *N* < *p*²*B*², where *B* = *p*ᵏ. Omit the first block of length *B* and the final incomplete block, at most 2*B* positions in total. Every other aligned block of length *B* lies wholly in one shell, since every intervening boundary is a multiple of *B*. For large *k*, *N* ≤ *B*³ and *q* ≤ *B*, so each regular starting denominator is at most *B*⁴. The interval count error of such a block is at most ε*B* for large *k*, simultaneously for every test interval. The discarded proportion tends to zero even if *N* is one position past a boundary.

**Zero positions.** Form a comparison sample by retaining the true lifts *b*ⁿ(*mX* + *r*) on regular positions and substituting *Y*ₙ on zero positions. On the latter its fractional part is exactly {*b*ⁿ*r*}. For any interval, a block of *B* consecutive positions after *s* has count error at most *L* relative to *B*νᵣ(*I*). Each full period gives exactly its mean and the remainder has length less than *L*. The preperiod is absorbed in the first discarded block. Put $`z_N=Z(N)/N`$. Summing the two kinds of block gives, uniformly over *I*, the comparison frequency

```math
(1-z_N)|I|+z_N\nu_r(I)+o(1).
```

Taking the supremum gives $`z_N D(r)+o(1)`$ for this sample. [Periodic counting error](../NormalityChecker/RationalOrbitCycle.lean#L59) · [Comparison sample and block sum](../NormalityChecker/TranslatedShells.lean#L48)

**Signed tails at an atom.** Extreme interval discrepancy is continuous under perturbations tending to zero on the circle. To see this with the half-open convention, use the periodic sawtooth *h*(*t*) = ⌈*t*⌉ − *t*. For real lifts *u*ₙ put *F*(*t*) equal to the average of *h*(*t* − *u*ₙ) over *n* < *N*. Then *F*(*d*) − *F*(*a*) equals the centered frequency on [*a*,*d*) for 0 ≤ *a* ≤ *d* ≤ 1. Discrepancy is the oscillation of *F*. Periodicity allows the endpoints to pass through 0 or 1.

Suppose |*u*ₙ − *v*ₙ| ≤ δ for *n* ≥ *K*, after any integer adjustments of the lifts. Monotonicity of the ceiling bounds the centered increment for *u* at *a*, *d* by that for *v* at *a* − δ, *d* + δ, plus 2δ. The first *K* terms cost at most 2*K*/*N*. Exchanging the two samples bounds the absolute difference of their discrepancies by 2δ + 2*K*/*N*. In the present comparison the error on zero positions is precisely *m*(*b*ⁿ*X* − *P*ₙ). Send *N* to infinity and then δ to zero. The untranslated theorem identifies limsup $`z_N`$ with *D*∞(*X*). [Circle perturbation theorem](../NormalityChecker/CircleDiscrepancy.lean#L137)

The distinction matters even for a fixed endpoint. In base 2 with *p* = 3, repeat the phases −1, 0 and translate by 1/3. In a zero shell the first omitted insertion is negative and dominates the tail. Indeed the omitted terms pair a negative term with a positive term of the same coefficient magnitude at a later radix position. At the ends of these shells $`z_N`$ tends to 3/4. Half of their positions, up to a bounded error per shell, have translation atom 1/3. They approach it from below and enter [0,1/3). The comparison atoms at 1/3 are excluded from that interval. The CDF error there tends to 3/8 along these cutoffs, although the discrepancy error tends to zero.

## Periodic examples and small positive discrepancies

The binary orbit of 1/3 alternates between 1/3 and 2/3. Its discrepancy is 2/3, as witnessed by intervals containing both atoms with length approaching 1/3. The product formula gives the following results for *p* = 3 and every integer *m* ≠ 0. [Kernel-verified examples](../NormalityChecker/TranslatedShells.lean#L259) · [Rational factor](../NormalityChecker/SharpDiscrepancy.lean#L157)

| Repeating phases | Discrepancy of X | Discrepancy of mX + 1/3 |
| --- | ---: | ---: |
| 1, 1, 1, 0 | 27/40 | 9/20 |
| 1, 0 | 3/4 | 1/2 |
| 1, 0, 0 | 12/13 | 8/13 |

**A fixed transcendental example.** Let *Y* be the binary *p* = 3 expansion with phases 1, 0 repeated. For *k* ≥ 1 put *Y*ₖ = *Y* + 3⁻ᵏ. Each *Y*ₖ is transcendental by the Roth argument for *Y* and rational translation. On paper their discrepancies are exactly

```math
D_\infty(Y_k)=\frac34\frac{2}{3^k}=\frac{1}{2\cdot 3^{k-1}}.
```

Indeed 2 has order 2 · 3ᵏ⁻¹ modulo 3ᵏ. Any exponent giving 1 must be even, and the lifting-the-exponent identity gives *v*₃(4ᵗ − 1) = 1 + *v*₃(*t*). The orbit visits every unit modulo *q* = 3ᵏ exactly once. To compute its discrepancy, sort an equally weighted period as *y*₀ < ⋯ < *y*ₗ₋₁ with *L* points. The left and right limits of the centered CDF at *y*ⱼ are $`j/L-y_j`$ and $`(j+1)/L-y_j`$. Between atoms the CDF error decreases with slope −1. Its oscillation is therefore

```math
\frac1L+\max_j(j/L-y_j)-\min_j(j/L-y_j).
```

For the units modulo *q*, *L* = 2*q*/3 and the pairs of sorted numerators are 3*t*+1, 3*t*+2. The offsets are −1/*q* and −1/(2*q*), giving 2/*q*.

Lean proves a more general qualitative conclusion. For **any** integer *t* ≥ 2 coprime to *b*, the rational factors *D*(*t*⁻ᵏ) are positive and tend to zero. Positivity follows from the empty interval [1/(2*q*),1/*q*) for any rational orbit with denominator dividing *q*. For convergence, fix a finite set of nonzero Fourier frequencies. The fixed-support orbit estimate applies to the rational start 1/*t*ᵏ uniformly for all prefix lengths *N* ≥ *t*ᵏ once *k* is large. The finite Fourier interval bound then makes the limsup discrepancy arbitrarily small. Consequently every signed expansion of positive discrepancy has explicit translates with arbitrarily small strictly positive discrepancy. The transcendence here uses Roth or Ridout as an external theorem. [Kernel existence and positivity](../NormalityChecker/TranslatedShellExamples.lean) · [Transcendence argument](signed-shell-discrepancy.md#irrationality-lean-and-transcendence-paper-corollaries)

### De Bruijn translations

Take a base-*b* cyclic de Bruijn word of order *h* ≥ 1. Its length is *L* = *b*ʰ and every length-*h* word occurs exactly once, including those that cross the end. If the digit block represents the integer *A* with leading zeroes retained, *r* = *A*/(*b*ᴸ−1) has those digits on repeat. Each of its *L* rotations lies in a different interval [*j*/*L*, (*j*+1)/*L*). An Euler circuit on the graph of (*h*−1)-digit words constructs such a cycle. An *h*-digit edge joins its prefix to its suffix, every vertex has indegree and outdegree *b*, and appending the target digits gives a path between any two vertices. At order one this is a single vertex with *b* loops.

There is an exact paper formula. Write the sorted orbit points as *y*ⱼ = (*j* + *v*ⱼ)/*L*. The residuals *v*ⱼ = {*b*ʰ*y*ⱼ} permute the same orbit, since shifting a cyclic word by *h* places permutes its rotations. The preceding oscillation formula gives

```math
D(r)=\frac{1+\max_j y_j-\min_j y_j}{L}.
```

In particular 1/*L* ≤ *D*(*r*) < 2/*L*. The binary word 0011 gives *r* = 1/5 and *D*(*r*) = 2/5. The word 00010111 gives *r* = 23/255, with extremal rotations 23/255 and 226/255. Its factor is 229/1020. Lean proves the upper bound and strict positivity from the one-visit-per-cell condition and checks the eight cells of the second example by kernel computation. [Finite condition and checked word](../NormalityChecker/TranslatedShellExamples.lean#L41)

## Several periodic orbits and rational division (paper)

Suppose the comparison sample has a regular part with uniform interval count error *o*(*N*) and finitely many exceptional classes. In class *h*, suppose that visits, measured against a fixed periodic orbit measure νₕ, have error *o*(*N*) uniformly in intervals and prefix cutoffs. For instance, this holds for a union of *o*(*N*) consecutive runs following that orbit, with uniformly bounded preperiod and period. Let *z*ₕ(*N*) be its fraction of the prefix. If the true samples approach their comparisons in circle distance apart from *o*(*N*) observations for every fixed tolerance, the same perturbation proof applies. The full discrepancy is

```math
\sup_I\left|\sum_h z_h(N)\big(\nu_h(I)-|I|\big)\right|+o(1).
```

Weights may oscillate. If they converge, insert their limits. For finitely many atoms one computes this value by taking the largest right limit minus the smallest left limit of the centered cumulative mass function, allowing the two sides of each jump. The sum of the individual discrepancies weighted by *z*ₕ is an upper bound. Equality requires intervals approaching a common extremum with the same sign for all positive-weight classes. In base 3 both 0 and 1/2 are fixed points, each with discrepancy 1. Their equal mixture has discrepancy 1/2. Such a mixture is also a radix-orbit limit. Concatenate ternary blocks of *j* zeroes and *j* ones for *j* = 1, 2, … . The two digit classes each have density 1/2, the boundaries have density zero, and away from a boundary the shifts approach the appropriate constant digit tail.

For a rational multiplier *h*/*d* with *d* > 0 and *h* ≠ 0, the integer part of the zero-shell prefix now matters. At the left endpoint *p*ʲ of a zero shell let *A*ⱼ = *P* at that endpoint, an integer. The comparison orbit there starts at the rational phase

```math
\frac{h A_j}{d}+b^{p^j}r \pmod 1.
```

Its denominator divides *d* times the denominator of *r*. Hence only finitely many eventual periodic orbits arise. Each zero shell has a uniformly bounded preperiod, and the number of shells meeting a prefix is *O*(log *N*). Classify each shell by its actual eventual orbit and use its actual prefix length in the finite-mixture formula above. Regular-shell denominators still grow. Recovering *P*ₙ by multiplying the translated prefix minus *b*ⁿ*r* by *d*/*h* gives a fixed-factor lower bound from the denominator of *P*ₙ. The upper denominator divides *dp*ʲ times the denominator of *r*. After a fixed number of shifts into each shell the base-prime factors have cleared. For a block proof discard the first block in each shell if necessary, at total cost *O*(*B* log *N*) = *o*(*N*) when *B* is comparable to √*N*. All other nonzero blocks meet the same smooth-orbit estimates.

One sufficient hypothesis for the original factor *D*(*r*) is a fixed *K* with $`d\mid b^K hA_j`$ on every sufficiently late zero shell. Then the division residue clears after *K* positions there. This includes any *d* dividing a power of the base. More generally it suffices that all exceptional classes with orbits different from νᵣ have upper density zero. Knowledge of normality under rational affine changes alone gives no numerical factor.

**Counterexample, including a transcendental input.** In base 2 with *p* = 3, adding 1 to the initial phase alone adds 1/2 − 1/8 = 3/8 to the real number. With *Y* as above, take *X* = 9*Y* + 3/8, itself a bounded signed expansion by linearity of the jumps. Its phases are nine times those of *Y* except for the initial increment. Thus *D*∞(*X*) = 3/4. Yet *X*/9 = *Y* + 1/24, whose translation has eventual orbit {1/3,2/3}. The product theorem gives *D*∞(*X*/9) = 1/2. Lean verifies both numerical discrepancies. Transcendence follows from the paper argument for *Y*. Even the single finite phase perturbation gives the rational counterexample *D*∞(3/8) = 1 and *D*∞(1/24) = 2/3. [Kernel division example](../NormalityChecker/TranslatedShellExamples.lean#L182)

## Cyclotomic resonances (paper extension)

Use the existing cyclotomic model with an odd prime *p* coprime to *b*, finitely many positive indices, rational weights, and *S* ≥ 1 at least their maximum. Let *U* be the repository’s integer-cleared sum, including the factor *p*−1. On scale [*Sp*ᵏ, *Sp*ᵏ⁺¹), the cells [*up*ᵏ, (*u*+1)*p*ᵏ) are indexed by *S* ≤ *u* < *pS*. A cell is resonant when its cell polynomial is divisible by the cyclotomic polynomial of order equal to the multiplicative order of *b* modulo *p*. Let *R* be the set of resonant cell indices. Let $`Z_R(N)`$ count positions in those cells strictly before *N*, including just the part of the last cell already present. [Cell polynomials and resonance test](../NormalityChecker/CyclotomicClassification.lean) · [Verified real approximation on each cell](../NormalityChecker/CyclotomicCell.lean#L67)

For every integer *m* ≠ 0 and rational *r* the same proof gives

```math
D_N(mU+r)-\frac{Z_R(N)}{N}D(r)\longrightarrow0.
```

Here is the added arithmetic step. In a fixed cell the verified model differs from *b*ⁿ*U*, modulo integers, by *O*(*p*⁻ᵏ) uniformly up to the last observation. Its rational part at offset *i* is $`A b^i/p^{k+E}`$. On resonance take *A* = 0. Off resonance the fixed nonzero *p*-adic cell coefficient has a fixed valuation, so for large *k* the reduced denominator is a fixed power of *p* times *p*ᵏ, with a constant depending only on the cell. The base powers are units at *p*. Integer multiplication and rational translation preserve denominator growth by the same fixed-factor bounds as above. On a partial cell of length *T* ≥ η*p*ᵏ the resulting denominator is at most *T*² for large *k*, so the fixed-support estimate gives uniform interval error *o*(*p*ᵏ). A shorter partial cell costs at most η*p*ᵏ. Send η to zero. There are a fixed number of cells per scale, and summing these errors over earlier scales is a geometric sum with vanishing relative error. On the resonant cells the rational orbit count and signed circle perturbation complete the argument. [Valuation and partial-cell model](../NormalityChecker/CyclotomicFourier.lean)

At *N* = *ip*ᵏ, *S* ≤ *i* ≤ *pS*, completed earlier scales contribute |*R*|(*p*ᵏ−1)/(*p*−1) positions and the current scale contributes *p*ᵏ times the number of resonant indices strictly below *i*. Inside each cell the density is monotone, since it is a ratio of affine functions of *N* with positive denominator. Thus the limsup for *mU* + *r* is *D*(*r*) times

```math
\max_{S\le i\le pS}
\frac{|R|/(p-1)+|R\cap[S,i)|}{i}.
```

For the binary triple with *p* = 7, indices 1, 2, 3 and respective weights 1, 2, 3, take *S* = 3. The cleared sum is six times the original sum. The cyclotomic order is 3. The three polynomial coefficients are equal precisely on cells *u* = 3, 4, 5, 6, where all depths are zero. On cells 7 through 13 only the first depth has increased, and on 14 through 20 the first two have increased. The resonant boundary fractions at *i* = 3 and 7 are respectively 2/9 and 2/3, with the maximum at 7. Adding 1/3 to the cleared sum therefore gives limiting discrepancies 4/27 and 4/9 at these boundary sequences and limsup 4/9 over all prefixes. Removing the integer clearing factor invokes the division problem above. The repository’s kernel theorem gives the two original weak limits; the all-cutoff translated cyclotomic formulas in this section are paper deductions. [Verified triple and its two boundary masses](../NormalityChecker/CyclotomicExamples.lean#L56)
