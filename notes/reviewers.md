# Note for reviewers

## Result under review

Which finite rational combinations of Stoneham-type components are normal in their construction base? Fix integers $`b\ge 2`$ and an odd **prime** $`p`$ coprime to $`b`$. Let $`M`$ be a finite set of positive integers, let $`a_m`$ be arbitrary rationals, and put

```math
T_{b,p,m}=\sum_{j=0}^{\infty}\frac{b^{-m p^j}}{m p^j},
\qquad F=\sum_{m\in M}a_m T_{b,p,m}.
```

Choose any positive integer $`S`$ at least as large as every index in $`M`$. Let $`d`$ be the multiplicative order of $`b`$ modulo $`p`$. For the integers $`S\le u\lt pS`$, form the rational polynomials

```math
j_m(u)=\left\lfloor\log_p\left\lfloor u/m\right\rfloor\right\rfloor,
\qquad
P_u(X)=\sum_{m\in M}\frac{a_m}{m p^{j_m(u)}}X^m .
```

**Theorem.** The real number $`F`$ is normal in base $`b`$ if and only if the $`d`$-th cyclotomic polynomial divides none of the $`P_u`$ in $`\mathbb{Q}[X]`$. The definition of normality counts overlapping words of every positive length over all prefix endpoints. The result includes signed and zero coefficients, indices divisible by $`p`$, and the empty family. The executable function returns a Boolean and a companion function lists every failed cell. Its correctness theorem is restricted to the parameter domain above. [Classification](../NormalityChecker/CyclotomicClassification.lean) · [Executable test and correctness](../NormalityChecker/CyclotomicTest.lean) · [Definition of normality](../NormalityChecker/Basic.lean)

## Why the polynomial occurs

Let $`D`$ be the product of the reduced denominators of $`a_m/m`$, set $`c_m=D a_m/m\in\mathbb{Z}`$, and put $`L=(p-1)D`$. At scale $`k`$, the cell with index $`u`$ consists of the positions $`n=u p^k+i`$ for $`0\le i\lt p^k`$. Component $`m`$ has completed exactly the terms through depth $`J_m=k+j_m(u)`$. The next insertion can occur at the right endpoint.

### Lift the inverse of the base

Let $`w\in\mathbb{Z}_p`$ be the root of $`X^d-1`$ reducing to $`b^{-1}`$ modulo $`p`$. Hensel's lemma applies since $`d`$ divides $`p-1`$ and the derivative at that residue is a unit. Reduction modulo $`p`$ shows that $`w`$ has exact order $`d`$. From $`bw\equiv1\pmod{p}`$ and $`w^p=w`$, taking successive $`p`$-th powers gives $`b^{p^j}w\equiv1\pmod{p^j}`$ at every insertion. [Hensel lift and precision](../NormalityChecker/CyclotomicLift.lean)

### Keep all completed insertions

Set $`E=\max_m j_m(u)`$, with $`E=0`$ for the empty set, and $`t=k+E`$. After clearing $`p^t`$, the contribution at depth $`j`$ contains $`p^{t-j}b^{n-mp^j}`$. Its residue modulo $`p^t`$ is $`p^{t-j}b^n w^m`$. Multiplication by $`p-1`$ and summation over $`0\le j\le J_m`$ give the factor $`p^{t+1}-p^{t-J_m}`$. Thus the completed numerator for $`b^n L F`$ is congruent to $`-b^n W`$ modulo $`p^t`$, where

```math
W=\sum_{m\in M} c_m p^{E-j_m(u)} w^m = Dp^E P_u(w).
```

The omitted real tail after scaling has absolute value at most $`p^{-k}\sum_m |c_m|`$, including near the end of the cell. Clearing the rational denominators before forming the congruence also handles coefficients with a factor of $`p`$ in their denominator. [Prefix calculation and tail](../NormalityChecker/CyclotomicCell.lean)

### Classify the cell

In $`\mathbb{Q}_p`$ the minimal polynomial of $`w`$ over $`\mathbb{Q}`$ is $`\Phi_d`$. Hence $`W=0`$ exactly in the divisibility case. Then each scaled shift approaches an integer uniformly on the cell. If $`W\ne0`$, write $`-W=p^v U`$ with $`U`$ a unit. The valuation $`v`$ is fixed on this cell at every scale. For each fixed nonzero integer frequency $`h`$, the multiplier $`hp^v`$ remains fixed and nonzero, and $`b^{u p^k}U`$ reduces to a unit. The uniform incomplete-orbit estimate applies to every partial cell. Its bound is $`o(p^k)`$ as $`k`$ grows, since $`E`$ is fixed. [Fourier estimate on cells](../NormalityChecker/CyclotomicFourier.lean) · [Unit-orbit estimate](../NormalityChecker/StonehamOrbit.lean)

### Pass to the full expansion

When all cells are nonresonant, adding complete scales and the last partial cell gives vanishing Fourier means at all prefix endpoints. Weyl's criterion and invariance under positive integer dilation give normality of $`F`$. When a cell is resonant, the Fourier mean at frequency one has a positive subsequential limit for $`L F`$, given below. Normality of $`F`$ would force this limit to be zero. [Transfer across scales](../NormalityChecker/ScaleTransfer.lean) · [Endpoint limits](../NormalityChecker/CellLimits.lean) · [Formal equivalence](../NormalityChecker/CyclotomicClassification.lean)

A concrete pitfall occurs at $`b=2,p=7`$ for $`T_{2,7,1}+10T_{2,7,2}`$. On the cell $`u=2`$ the polynomial is $`X+5X^2`$. The inverse of two is four modulo seven, and $`4+5\cdot4^2=84`$ vanishes modulo seven. $`\Phi_3=X^2+X+1`$ cannot divide this nonzero quadratic with zero constant term. The same degree and constant-term argument works on every cell of this two-term family. Reduction at a single precision can therefore misclassify a normal sum.

## How the executable test avoids algebraic-number arithmetic

The program finds $`d`$ by bounded search with modular exponentiation. It groups the coefficients of $`P_u`$ by exponent modulo $`d`$, obtaining a vector of $`d`$ rational numbers. For each proper positive divisor $`e`$ of $`d`$, it multiplies this vector by $`X^e-1`$ modulo $`X^d-1`$ using a cyclic shift and subtraction.

The final vector is zero exactly when $`X^d-1`$ divides $`P_u\prod_{e\mid d,\ e\lt d}(X^e-1)`$. The identity $`X^d-1=\prod_{e\mid d}\Phi_e`$ proves one direction, since each proper $`\Phi_e`$ divides its corresponding factor. For the converse, evaluate at a primitive complex $`d`$-th root. Every proper-divisor factor there is nonzero, so $`P_u`$ must vanish. The mathematical proof uses roots of unity. Each execution uses natural numbers and exact rationals. [Cyclic-vector proof](../NormalityChecker/CyclotomicTest.lean)

## Exact statistical prediction

Let $`R`$ be the number of failed cells in $`S\le u\lt pS`$ and $`w_S=R/((p-1)S)`$. At the endpoints $`N=S p^k`$, the empirical distributions of the first $`N`$ shifts of **$`L F`$ modulo one** converge weakly on the circle to

```math
(1-w_S)\lambda+w_S\delta_0 ,
```

where $`\lambda`$ is uniform probability measure. The Lean statement gives the limit for every continuous complex-valued function on the circle. At a nonzero frequency each complete cell contributes either zero or one to its limiting average. Summing the preceding scales gives precisely $`w_S`$. Density of trigonometric polynomials extends the formula to continuous test functions. The origin is a single point on the circle, so a weak limit with an atom there does not by itself assign that atom to a particular half-open digit interval. [Continuous-test-function theorem](../NormalityChecker/CyclotomicDistribution.lean)

- For $`b=2,p=3`$, evaluating at $`-1`$ recovers the original rational cell coefficient and the two Boolean checkers agree on every admissible input.
- For $`b=10,p=3`$, the root is $`1`$. With a nonempty family of positive rational coefficients every $`P_u(1)`$ is positive. The whole family of sums is decimal normal.
- For $`b=2,p=7`$, the sum $`F=T_{2,7,1}+2T_{2,7,2}+3T_{2,7,3}`$ is binary nonnormal. The first resonant cell has $`P_3=X+X^2+X^3=X\Phi_3`$. For the orbit of $`6F`$, the atom at zero has weight $`2/9`$ along $`N=3\cdot7^k`$ and $`2/3`$ along $`N=7^{k+1}`$. Different choices of endpoints yield genuinely different limiting distributions. [Verified specializations](../NormalityChecker/CyclotomicExamples.lean)

## Relation to prior work

| Source | Relevant result and scope |
| --- | --- |
| Stoneham (1973), Bailey and Crandall (2002) | Individual normal constants and sufficient conditions for more general lacunary series. Bailey and Crandall's Theorem 4.8 imposes growth conditions on two sequences of exponents. [Stoneham](https://doi.org/10.4064/aa-22-3-277-286) · [Bailey and Crandall](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf) |
| Kano (1993) | Theorem 1 gives a sufficient normality criterion for numerators over products of two growing powers. Its restrictions on successive denominator exponents and divisibility of numerators are relevant when determining which special cases already follow from the literature. [Institutional copy, pp. 909–919](https://ocu-omu.repo.nii.ac.jp/record/2009394/files/111F0000002-03004-15.pdf) |
| Vandehey (2019) | Theorems 7.2 and 7.4 connect incomplete modular-orbit estimates with normality. Theorem 7.4 uses unit numerators, a denominator divisibility chain, and a spacing hypothesis. The present argument identifies the exact cancellation obstruction for interleaved, rationally weighted schedules. [Primary preprint, §7](https://arxiv.org/abs/1606.07911) |
| Bailey and Borwein (2012), subsequent Lean development (2026) | Section 4 asks about two standard constants with the same base and two denominator parameters. The later repository proves that two-sum statement. Here one prime parameter is fixed, and the insertion multipliers and rational coefficients vary. Neither theorem contains the other in its full parameter range. [Published paper](https://doi.org/10.1007/s11139-012-9417-3) · [Author manuscript](https://www.davidhbailey.com/dhbpapers/nonnormality.pdf) · [Two-sum development](https://github.com/CaptainSude/Stoneham-sum-normal/tree/f4d3d1f01d00c57425c684409849053e58e42261) |

The comparison used the author manuscripts, Kano's institutional copy, the public two-sum development, and bibliographic title searches. Priority for the cyclotomic equivalence or the exact mixture is unestablished. Particularly valuable review would identify earlier necessary-and-sufficient criteria for these schedules, check the common scaling at coincident insertions, and compare the stated weak limit with existing quantitative distribution results.

## Certificates for infinite series

For every odd prime $`p`$, the logarithmic sum over indices $`2^a p^j`$ is binary normal. More generally, the result holds in base $`b`$ with a generator $`q\ge2`$ dividing $`b`$ in place of two. The prime $`p`$ must be coprime to $`b`$. The main point for review is the separation of two exceptional cutoffs by a top-layer insertion and the resulting bound for partial blocks. The formalization gives an interval discrepancy bound of $`O(1/\log\log N)`$ for every prefix length sufficiently large in terms of the fixed parameters. The proof note identifies the earlier localized-logarithm manuscript and its stronger rate in one special case. [Mixed logarithm note](mixed-localized-logarithms.md) · [Formal theorem](../NormalityChecker/LocalizedMixed.lean) · [Exact special case for five](localized-logarithms.md) · [Composite-generator argument and its formal status](composite-generators.md)

A second executable test gives a sufficient condition for a polylogarithm supported on a finite set of primes. The decimal order-one example on $`\{2,3,5\}`$ has five complete-prefix residues modulo 9. Multiple surviving off-base primes are now covered by a Lean proof of the qualitative polynomial-length consequence of Vandehey’s Corollary 1.2. The three binary certificates consequently prove normality. For mixed support $`q^a c^j`$, Lean proves normality at every integer order $`s\ge1`$ for composite as well as prime $`c`$, using denominator growth away from an exceptional set. [Finite certificates and examples](localized-certificates.md) · [Proof and parameter ranges](arithmetic-certificates.md)

For an application outside localized polylogarithms, a binary Stoneham component remains normal after adding the terms $`3^{-\lfloor\log_3m\rfloor}2^{-m^r}`$ for any integer $`r\ge1`$. The cases of squares and cubes use local denominator dominance, and the linear case follows from an exact identity for a dense expansion. We would especially welcome comparisons with previous normality-preserving transformations and review of two quantifiers in the proofs. The translation count is fixed before the modulus grows, and the tolerance on the exceptional set is fixed before the scale grows. [Perturbation theorem and worked proof](arithmetic-certificates.md#insertions-at-squares-cubes-and-every-digit) · [Vandehey’s original paper](https://arxiv.org/abs/1606.07911)

## Polynomial weights and approximate orbits

The dense theorem concerns every nonzero rational polynomial $`P`$ of degree below $`s`$ on power intervals, in every pair of coprime radices $`b,c\ge2`$. A polynomial antidifference turns the dense series into a signed boundary series. The mixed theorem permits $`P(m)/m^s`$ on $`m=q^a c^j`$. In reviewing these results, the decisive arithmetic step is uniform stabilization of the numerator at a prime dividing $`c`$, followed by dominance of the largest layer in a **difference** of prefixes. For periodic weights whose period divides $`c-1`$, one finite rational sum determines whether the expansion vanishes or is normal. The signed alternating example realizes the zero case. [Proofs, hypotheses and example](polynomial-certificates.md)

Vandehey’s Theorem 7.4 already implies the constant-numerator single-axis result on every infinite subsequence here. We would welcome references covering varying signed numerators, cancellation across mixed denominator layers, or the precise dense polynomial family after symbolic summation. The qualitative fixed-support estimate used by Lean is internal. Assessing the historical priority of its applications requires a separate literature judgment. [Comparison with prior constructions](polynomial-certificates.md#comparisons-and-open-scope) · [Vandehey, §7.2](https://arxiv.org/pdf/1606.07911)

The approximate certificate allows different rational models on different blocks. For the full logarithm the new construction gives linear-length shadowing, while its denominators can acquire unbounded primes. Independent scrutiny of the denominator obstruction and of potential orbit estimates on most block starts would bear directly on the open four-window discrepancy objective. [Approximate certificate](../NormalityChecker/ArithmeticCertificate.lean) · [Logarithm model and paper obstruction](logarithm-correlations.md#rational-models-on-linear-length-blocks)

## Finite-support discrepancy

The order-$`s`$ prime-restricted series has maximal discrepancy exactly when every support prime divides the radix. An exact finite bound tracks passing and failing regions even in incomplete geometric scales. Independent review would help identify prior results on positive-density uniform orbit segments for smooth supports, and on the metric scope of rational block models. [Proof, examples and open scope](finite-support-discrepancy.md)

## Verification and open scope

The research and formalization are AI-assisted. The repository pins Lean and Mathlib, builds the library, audits the listed theorems for transitive axioms, and replays the project modules through the kernel. The original binary checkpoint remains available for comparison. [Verification instructions](../README.md#reproduce-and-review) · [Audit](../Audit.lean) · [Previous checkpoint](https://github.com/eldernos/MathematicsResearch/tree/research-checkpoint-2)

The equivalence is for finite families with an odd prime parameter. The earlier individual-normality and paired-nonnormality theorems also cover some composite parameters. Passing to the infinite decomposition of $`\ln 2`$ would require cancellation estimates uniform in a growing family. The project has no classification of $`\ln 2`$ or $`\pi`$.
