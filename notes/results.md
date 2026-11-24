# Results and examples

## Phase 11

**Binary normality of all positive powers of the standard Stoneham number is kernel-verified.** More generally every nonconstant rational polynomial in an odd-prime-parameter Stoneham number is normal in its construction radix. The unsigned finite-prime question also has a complete answer: discrepancy tends to zero when any support prime is off-base, and to one otherwise. For the ordinary constants ln 2, π, *e*, the golden ratio and the natural logarithm and arctangent candidates, this phase establishes no strict asymptotic discrepancy bound below one.

| Investigation | Conclusion and evidence |
| --- | --- |
| Nonlinear Stoneham constants | Lean proves the square's exact denominator profile, normality for every rational polynomial in the odd-prime family, and normality of products on independent strides of one prime. For independent parameters 3 and 5, Lean verifies irrationality and discrepancy at most 43/45. The mixed-product transcendence corollary uses Ridout on paper. In base three the original constant has superlinear ordinary factor complexity by a separate Subspace Theorem argument. [Ternary recurrence estimate](ternary-stoneham-complexity.md) [Square](stoneham-square.md) · [General proof, examples and literature](stoneham-powers-products.md) |
| Corrected models of ln 2 | Lean proves the finite common denominator and signed integral residual; Stirling and the prime number theorem give upper rates 0.746090, 1.095663 and 1.962602 for forward lengths one half, one and two times the starting position. The uncorrected rate one half and the general signed-logarithm band formula are now kernel-verified for reduced denominators. The sharp optimality deduction takes Bang’s primitive divisors as an explicit input. [Models, comparison and congruences](corrected-strides.md) |
| Classical escape target | Prime-power tests cover sublinear growing lengths. Exact arithmetic excludes all words with at most three changes in two reported windows. An entropy comparison counts hypothetical residues and does not bound the frequency of the prescribed residue in arbitrarily late windows. The target of 0.9999 for ln 2 remains open. [Sieve and simultaneous observations](sublinear-residue-windows.md) |
| Exact finite-support theory | Lean proves the all-orders, all-prefix persistent discrepancy theorem, the maximum on the actual log-flow closure, and nullity of each individual off-base failed region. Positive persistent mass is impossible on the unsigned full support with an off-base prime. A paper proof gives finite termination for every two-prime full support and constructs a fixed mask with failures at all depths. The full-support question with multiple cofactors remains open at small orders. [Finite-depth analysis](fixed-depth-question.md) · [Joint theorem](higher-order-joint.md) · [Nullity proof](unsigned-finite-support.md) |
| Rational translations | Lean verifies the product with the discrepancy of the rational orbit, including signed tails, the values 9/20, 1/2 and 8/13, and arbitrarily small positive discrepancy factors. A finite-mixture treatment covers rational division and integer-cleared cyclotomic examples on paper. [Translated shells and examples](translated-shells.md) |
| Polynomial weights and masks | Full-support rational polynomial normality is equivalent to a residual pole at zero and an off-base support prime. The bounded-gap mask bounds, periodic window densities, infinite-axis theorem, and two rational examples with discrepancy 2/3 are kernel-verified. A nonmonomial sampled denominator needs unit values at the selected prime and fixed finite denominator support. [Classification](polynomial-masks.md) · [Full rational theorem](../NormalityChecker/FullPolynomialNormality.lean) |
| Signed spectrum | Lean verifies both directions of the lexicographic characterization, the isolated zero, all positive accumulation points and periodic approximation. The dimension, translated spectrum and comparison with symbolic dynamics have paper proofs. [Spectrum and changing schedules](attainable-shell-histories.md) |
| Independent classical constants | Lean checks short returns of factorial Taylor numerators and denominator rates for the dyadic logarithms. A moving-window result for *e*, shrinking finite-prefix bounds for π and 1/√5, and the two-thirds binary denominator rate for Gaussian π and arctangent models are paper deductions. [Gaussian numerator arithmetic](gaussian-arctangent-denominators.md) · [Direct prime-square estimates](dyadic-prefix-residues.md) [Proofs and published inputs](classical-approximants.md) |

## Phase 10

The following table records the status at the Phase 10 checkpoint. The Phase 11 proofs above supersede its open finite-support question and formalize several of its paper deductions.

**The binary discrepancy bound of 0.9999 for ln 2 remains open.** The arithmetic advance is an alternative series with exact shifted denominator growth rate one half and a proof that this rate is optimal among binary-exponent truncations of finite dyadic logarithm identities. The remaining question is whether the actual binary orbit has a sufficiently large lower share of locally distributed blocks or an equivalent quantitative escape estimate.

| Investigation | Evidence and scope |
| --- | --- |
| Coverage and actual numerators of ln 2 | Lean proves the fixed-quality and intermittent-shell implications and bounds repetitions of each prescribed normalized diagonal residue. A published irrationality measure improves the individual run bound on paper. Finite exact certificates cover 888 of the first 1,024 positions in disjoint twelve-position blocks. A large-prime sieve independently excludes all words with at most one transition at five diagonal starts. Positive limiting coverage and the required moment and cylinder bounds remain open. [Coverage proofs and finite scope](intermittent-coverage.md) · [Numerator proof](strided-logarithm.md#repetitions-of-a-prescribed-diagonal-numerator-residue) |
| Alternative representations and integer multiples | Lean proves the two-stride series, its pointwise error and denominator bounds, the full-degree Chebyshev error, and the integer-multiple cosine inequality. The exact denominator rate, optimality theorem and binary-run transfer have paper proofs. The bounded product search uses rational arithmetic. [Series and supporting arithmetic](strided-logarithm.md) · [Transfer between multiples](intermittent-coverage.md#multiplying-a-constant-and-returning-to-the-binary-orbit) |
| Joint prime failures | Lean proves the exact limiting discrepancy formula at order one for every finite support and checks a failure of deepest-cell clearing at order two. A paper argument uses all orders up to the specified order to obtain a replacement. An explicit unsigned support with an off-base prime and positive persistent joint mass remains open. [Proof, compact phase space and examples](joint-persistent.md) |
| Polynomial weights and masks | Exact local valuations, finite window counts and signed tail bounds are kernel-verified. The full classification, retained-power and bounded-gap discrepancy bounds are paper deductions. Rational coefficients preserve the positive conclusions. Explicit rational examples in the maximal integer cases have discrepancy 2/3. [Classification and counterexamples](polynomial-masks.md) |
| Signed Stoneham phases | Lean proves the all-prefix asymptotic, the periodic formula, all three stated rational discrepancies, and the irrationality criterion. The attainable spectrum and transcendence follow on paper, using Roth or Ridout for transcendence. [Statements, proofs and examples](signed-shell-discrepancy.md) |
| Golden ratio and π | A published digit-change estimate gives a growing lower count for least Zeckendorf indices at most three. A paper inequality transfers hexadecimal discrepancy bounds to binary. The growing-modulus and Machin tests give finite exact counts. A positive asymptotic escape density for either constant remains open. [Proofs and computations](intermittent-coverage.md#hexadecimal-observations-for-π) |

## Quantitative discrepancy on finite prime supports

The checker sharpens the bound by counting failed modular cells through every prefix endpoint. In base 7 with support $`\{2,3,5\}`$, testing at powers of five returns $`5/12`$, $`1/4`$, and zero. Several primes can certify the same prefix. Only their simultaneous failures are charged. [Checker and soundness](../NormalityChecker/DiscrepancyChecker.lean) · [Overlaps and the binary example](overlapping-certificates.md)

When $`s=1`$ and $`p`$ is the only off-base prime, let $`Z\subseteq[1,p)`$ be the intersection of the failed regions at all precisions. The exact discrepancy is

```math
D_\infty=\max_{1\le t\le p}\frac{|Z|/(p-1)+|Z\cap[1,t)|}{t}.
```

Here $`|\cdot|`$ is Lebesgue measure. Normality is equivalent to $`|Z|=0`$. The endpoint $`t`$ accounts for prefixes ending partway through a scale. For general radix orbits, a uniformly distributed share $`g`$ across all long prefixes implies $`D_\infty\le1-g`$. Correct limiting frequencies for all 256 binary words of length eight give $`D_\infty\le1/128`$. [Proof of the exact formula and worked examples](persistent-discrepancy.md) · [Partial-uniformity theorems](../NormalityChecker/PartialUniformity.lean)

See the [polynomial kernel construction and finite coverage experiments](complementary-models.md) for complementary models of the classical constants.

## Normality from rational prefixes

A general Lean theorem proves normality if most blocks are approximated, in mean distance modulo one, by rational radix orbits. Each block can choose its own model. Its reduced denominator must grow, have prime factors from a fixed set coprime to the radix, and be polynomially bounded in the block length. Finite Fourier and interval-count bounds account for model error, orbit cancellation, exceptional blocks and the unfinished final block. [Certificate theorem](../NormalityChecker/ArithmeticCertificate.lean) · [Interval-count bound](../NormalityChecker/ApproximateDiscrepancy.lean) · [Proof guide](polynomial-certificates.md) · [Orbit estimate](../NormalityChecker/SmoothOrbit.lean)

| Application | Kernel-verified conclusion |
| --- | --- |
| Dense polynomial weights | For coprime $`b,c\ge2`$, every nonzero rational polynomial $`P`$ of degree below $`s`$ gives a base-$`b`$ normal sum with terms $`P(n)/(c^{s\lfloor\log_c n\rfloor}b^n)`$ at positive integer positions. [Proof and binary example](../NormalityChecker/DensePolynomial.lean) |
| Mixed rational weights | For $`m=q^a c^j`$, the sum of $`P(m)/(m^s b^m)`$ over all exponent pairs is base-$`b`$ normal under the same polynomial conditions, with $`b,q,c\ge2`$, $`q\mid b^A`$ for some $`A`$, and $`\gcd(b,c)=1`$. This includes finite signed rational combinations of different localized orders with a nonzero combined numerator. [Mixed and restricted-axis theorems](../NormalityChecker/RationalWeights.lean) |
| Periodic weights on power intervals | If the period $`d`$ divides $`c-1`$, a finite rational sum over one period determines whether the dense sum is zero or normal. This includes restrictions to any nonempty set of residue classes. [Periodic test](../NormalityChecker/PeriodicWeights.lean) |
| Periodic weights of arbitrary period | At order one and prime $`p\nmid b`$, cyclic weighted sums classify normality for every rational periodic coefficient sequence, including periods divisible by $`p`$. A binary period-four example has one vanishing cyclic sum and is nonnormal. [Classification and example](../NormalityChecker/PeriodicClassification.lean) |
| Independent prime exponents | A passing residue test proves normality at any positive integer order. The earlier order-one certificates for $`\{2,5,7\}`$, $`\{2,5,11\}`$ and $`\{2,5,7,11,13\}`$ now give binary normality. |
| A Stoneham constant with polynomially spaced insertions | Adding $`\sum_{m\ge1}3^{-\lfloor\log_3m\rfloor}2^{-m^r}`$ to the binary Stoneham component with parameter 3 preserves normality for every positive integer $`r`$. For the dense case $`r=1`$, the perturbed sum is exactly $`3-3S`$, where $`S`$ includes the initial term $`1/2`$. |

The mixed and perturbed families have unconditional proofs. The research note gives the conditions behind each certificate, its relation to published exponential-sum estimates, and the obstruction that remains for $`\ln 2`$. [Mixed series](../NormalityChecker/MixedPowers.lean) · [Finite-support checker](../NormalityChecker/SmoothCertificates.lean) · [Perturbations](../NormalityChecker/PolynomialInsertions.lean)

## The cyclotomic checker

Fix a base $`b\ge2`$ and an odd prime $`p`$ coprime to $`b`$. The input is a finite set of positive indices $`M`$ and rational coefficients $`a_m`$. It specifies the real number

```math
F=\sum_{m\in M}a_m T_{b,p,m},\qquad
T_{b,p,m}=\sum_{j=0}^{\infty}\frac{1}{m p^j b^{m p^j}}.
```

Let $`d`$ be the multiplicative order of $`b`$ modulo $`p`$ and choose a positive $`S`$ at least as large as every index. For each integer $`S\le u\lt pS`$, form the rational polynomial

```math
P_u(X)=\sum_{m\in M}\frac{a_m X^m}{m p^{j_m(u)}},
\qquad j_m(u)=\left\lfloor\log_p\left\lfloor u/m\right\rfloor\right\rfloor.
```

**The sum is normal in base $`b`$ exactly when $`\Phi_d`$ divides none of these polynomials.** The implementation tests divisibility using a cyclic vector of rational coefficients. [Lean equivalence](../NormalityChecker/CyclotomicClassification.lean) · [Executable checker](../NormalityChecker/CyclotomicTest.lean)

```lean
import NormalityChecker
open NormalityChecker

#eval cyclotomicNormalTest 10 3 {1, 2, 3, 4} (fun m => 1 / (m + 1)) -- true
#eval cyclotomicNormalTest 2 7 {1, 2, 3} (fun m => m)               -- false
#eval (resonanceWitnesses 2 7 3 {1, 2, 3} (fun m => m)).sort       -- [3, 4, 5, 6]
```

For $`b=10,p=3`$, **every** nonempty finite family with positive rational weights is decimal normal. For $`b=2,p=7`$, the three-term sum in the example is binary nonnormal. Its orbit after scaling by six has two different subsequential limits. The point mass at zero has weight $`2/9`$ at endpoints $`3\cdot7^k`$ and $`2/3`$ at endpoints $`7^{k+1}`$. In each case the remaining mass is uniform on the circle. [Verified examples](../NormalityChecker/CyclotomicExamples.lean) · [Distribution theorem](../NormalityChecker/CyclotomicDistribution.lean)

## The original binary checker

At $`b=2,p=3`$ the generalized checker agrees with the original checker for the components

```math
T_m=\sum_{j=0}^{\infty}\frac{1}{m3^j 2^{m3^j}}.
```

For any finite set of positive indices and any rational coefficients, Lean now proves a necessary-and-sufficient test for binary normality of $`F=\sum a_m T_m`$. Pick $`S`$ at least the largest index. On each of the finitely many cells $`S\le u\lt 3S`$, compute $`j_m=\lfloor\log_3\lfloor u/m\rfloor\rfloor`$ and $`H_u=\sum_m a_m(-1)^m/(m3^{j_m})`$. Then $`F`$ is binary normal exactly when every $`H_u`$ is nonzero.

The consequences include binary normality of each $`T_m`$, binary normality of every ordered finite partial sum of the logarithmic decomposition, and the equivalence

```math
T_1+aT_2\text{ is binary normal}\quad\Longleftrightarrow\quad a\notin\lbrace 2/3,2\rbrace\quad (a\in\mathbb{Q}).
```

The unweighted sum $`T_{20}+T_{28}+T_{35}`$ is nonnormal. The finite test is executable and its correctness theorem refers directly to overlapping digit blocks. [Mathematical proof](finite-sums.md) · [Lean classification and checker](../NormalityChecker/FiniteClassification.lean)

```lean
import NormalityChecker
open NormalityChecker
#eval binaryNormalTest {1, 2} (fun _ => 1)         -- true
#eval binaryNormalTest {20, 28, 35} (fun _ => 1) -- false
```

## Normality of two-generator localized logarithms

For every odd prime $`p`$, restricting the series for ln 2 to indices $`2^a p^j`$ gives a **binary-normal number**. More generally, if $`q\ge2`$ divides the base $`b`$ and $`p`$ is an odd prime coprime to $`b`$, Lean proves normality in base $`b`$ of

```math
X_{b,q,p}=\sum_{j,a\ge0}\frac{1}{q^ap^j b^{q^ap^j}}.
```

For each fixed triple, Lean also proves that the interval discrepancy of the first $`N`$ shifts is $`O(1/\log\log N)`$. This includes decimal normality for the prime pairs $`\{2,7\}`$ and $`\{5,11\}`$. The proof bounds the proportion of digit positions where many factors of $`p`$ disappear from the reduced denominator. The earlier binary $`\{2,5\}`$ result also identifies exactly where one factor of five cancels. [General proof and prior work](mixed-localized-logarithms.md) · [Literal series theorem](../NormalityChecker/LocalizedMixed.lean) · [Discrepancy rate](../NormalityChecker/LocalizedDiscrepancy.lean) · [Exact calculation for five](localized-logarithms.md)

## Finite certificates for infinite prime-restricted sums

The logarithmic series supported on $`2^a3^j5^c`$ is **decimal normal**. Five residues modulo 9 certify every sufficiently large rational prefix. More generally, an executable test checks every cell of a finite partition. Success proves normality for a fixed finite prime support with a selected prime coprime to the base. This also gives decimal normality for the supports $`\{2,5,7\}`$ and $`\{2,5,11\}`$, and base-30 normality for $`\{2,3,5,7\}`$. [Proof and worked certificates](localized-certificates.md) · [Literal three-exponent theorem](../NormalityChecker/LocalizedExamples.lean)

## The two arithmetic milestones

The logarithm series gives the rational prefixes

```math
A_n=\sum_{j=1}^{n}\frac{1}{j2^j},\qquad
R_n=2^n A_n.
```

Let $`Q_n`$ be the reduced denominator of $`R_n`$ and $`D_n`$ the least common multiple of the integers from 1 through $`n`$, with $`D_0=1`$.

1. **Exact cancellation.** For every odd prime $`p`$ and every $`a\ge1`$ with $`p^a\le n\lt p^{a+1}`$, let $`k=\lfloor n/p^a\rfloor`$. Then $`p^a\mid Q_n`$ if and only if $`p`$ does not divide the reduced numerator of $`A_k`$. For example, $`Q_{10}=63`$. To see why a short prefix suffices, clear denominators with $`D_n`$ and reduce modulo $`p`$. Only indices divisible by $`p^a`$ can contribute. On those indices Fermat's theorem gives $`2^{jp^a}\equiv2^j\pmod{p}`$. [PrimeCancellation.lean](../NormalityChecker/PrimeCancellation.lean)
2. **Quantitative loss.** For $`n\ge8`$ the checked bound is $`0\le\log(D_n/Q_n)\le116n^{2/3}`$. For a cutoff $`K\ge2`$ with $`n\le K^3`$, three copies of $`D_{K^2}`$ cover all powers of primes at most $`K^2`$. Each larger prime occurs to exponent at most one. If it cancels, the first theorem puts it in a numerator of $`A_1,\ldots,A_K`$. Chebyshev's upper bound gives a total log loss of at most $`29K^2`$. Taking $`K=\lceil n^{1/3}\rceil`$ gives the stated inequality. Mathlib's prime number theorem for $`D_n`$ then gives $`\log Q_n/n\to1`$. [DenominatorGrowth.lean](../NormalityChecker/DenominatorGrowth.lean)

## Which digit questions the proofs settle

| Question | Lean result |
| --- | --- |
| How can approximations certify normality in an integer base $`b\ge2`$? | If $`b^n x-u_n\to0`$, normality of $`x`$ is equivalent to uniform distribution of $`u_n`$ modulo one. The proof starts from frequencies of overlapping digit blocks and handles wraparound at integer boundaries. [Distribution.lean](../NormalityChecker/Distribution.lean) |
| What does this give for $`\log 2`$? | $`R_0=0`$, $`R_{n+1}=2R_n+1/(n+1)`$ and $`0\le 2^n\log 2-R_n\le1/(n+1)`$. Binary normality is equivalent to uniform distribution of this exact rational recurrence. [LogTwo.lean](../NormalityChecker/LogTwo.lean) |
| Does the proposed cancellation example work? | For $`T_m=\sum_{j\ge0}2^{-m3^j}/(m3^j)`$, the sum $`T_1+2T_2`$ fails binary normality. For every $`k\ge2`$, every start $`2\cdot3^k\le n\lt 3^{k+1}`$ has next block `00`. That gives at least $`1/3`$ of the first $`3^{k+1}`$ starts, above the required $`1/4`$. [Resonance.lean](../NormalityChecker/Resonance.lean) |
| How are the components related to $`\log 2`$? | Summing $`T_m`$ over positive $`m`$ indivisible by three gives exactly $`\log 2`$. For each $`K\ge1`$, using **all** such indices $`m\le K`$, the sum $`\sum f(m)/m`$ is nonzero for every choice of odd integers $`f(m)`$. This proves the parity step used by the finite classification. [OrderedComponents.lean](../NormalityChecker/OrderedComponents.lean) |

## Finite sums and incomplete orbits

For $`T_1+aT_2`$, Lean proves that binary normality requires $`a\notin\lbrace 2/3,2\rbrace`$. The coefficient $`2/3`$ pairs the $`j`$-th term of $`T_2`$ with the $`(j+1)`$-st term of $`T_1`$. For $`k\ge3`$, every start in $`[3^k,2\cdot3^k)`$ has next block `00`. This accounts for at least half the starts in a prefix ending at $`2\cdot3^k`$. [Resonance.lean](../NormalityChecker/Resonance.lean)

For every $`q=3^k`$ with $`k\ge2`$, $`3\nmid A`$, and every interval of exponents $`[u,u+N)`$, the checked incomplete-sum bound is

```math
\left|\sum_{n=u}^{u+N-1}\exp(2\pi i A2^n/q)\right|\le 5\sqrt q(1+\log q).
```

With $`r=\lceil k/2\rceil`$, cubing shows $`2^{2\cdot3^{r-1}}=1+c3^r`$ with $`c\equiv1\pmod{3}`$. The square of $`c3^r`$ vanishes modulo $`q`$. Splitting the exponent into stride classes therefore gives geometric series modulo $`m=3^{k-r}`$. Multiplication by a unit permutes the powers of two over each period. The geometric bounds sum to at most $`m(1+\log m)`$ per period of row indices, by the harmonic sum estimate. The final incomplete row of exponents costs at most one stride. The restriction $`k\ge2`$ matters for an estimate uniform in $`N`$ since the complete sum modulo three need not vanish. [Linearization](../NormalityChecker/Linearization.lean) · [Interval estimate](../NormalityChecker/OrbitSum.lean)

## Polylogarithms and separated positions

The exact prime criteria now cover all integer radices $`b\ge2`$ and all positive orders $`s`$. The checked loss bound is $`4s(21+7s+b)n^{2/3}`$ for $`n\ge b^3`$. The short proof note gives the exceptional-prime rule, the $`s=0`$ case, and links to the Lean statements. [Arithmetic note](denominators.md)

For any starting index and lag, the rational recurrence satisfies

```math
0\le R_{n+r}-2^rR_n
=\sum_{j=1}^r\frac{2^{r-j}}{n+j}
\le\frac{2^r-1}{n+1}.
```

Lean proves that $`\log 2`$ is binary normal exactly when the Cesàro means of $`e^{2\pi i h R_n}`$ vanish for every odd integer $`h`$. At any one fixed positive lag $`r`$, one can equivalently test $`R_{n+r}-R_n`$. For growing lags, subtracting the explicit drift $`(2^r-1)/(n+1)`$ from $`R_{n+r}-2^rR_n`$ gives an error of at most $`(2^r-r-1)/(n+1)^2`$. At $`n=a2^k`$ and $`r=k`$ the uncorrected drift tends to $`1/a`$. [Proofs and open estimate](logarithm-correlations.md) · [Fourier criteria](../NormalityChecker/FourierTest.lean) · [Growing lags](../NormalityChecker/GrowingLags.lean)

## Quantitative nonnormality in every radix

Write $`T_{b,c,m}=\sum_{j\ge0} b^{-mc^j}/(mc^j)`$. For integers $`b\ge2`$, odd $`c\ge3`$, $`1\le m\lt l\lt c`$, assume $`c\mid b^{l-m}+1`$. Lean proves that $`mT_{b,c,m}+lT_{b,c,l}`$ is irrational and nonnormal in base $`b`$. For **every** fixed length $`r`$, the upper limiting frequency of the all-zero block is at least $`(c-l)/(c-1)`$. For the original binary pair this gives $`1/2`$. Both summands are positive and individually normal in base $`b`$. In every base one can choose a single pair to exceed any prescribed threshold below one for all these block lengths. [General theorem](../NormalityChecker/GeneralResonance.lean) · [Cumulative count](../NormalityChecker/ResonantDensity.lean) · [Proof for the normal summands](normal-summands.md)

The divisibility $`c^{j+1}\mid (b^{l-m})^{c^j}+1`$ follows from factoring a difference of $`c`$-th powers. The geometric factor is divisible by $`c`$ because its terms agree modulo $`c`$ and there are $`c`$ of them. On $`[lc^k,c^{k+1})`$ all inserted pairs shift to integers, and the strictly positive tail is at most $`2/((c-1)c^k)`$. For fixed $`r`$ this forces the next $`r`$ digits to be zero from some scale onward. Adding the disjoint intervals through scale $`k`$ and dividing by $`c^{k+1}`$ gives the bound. The strictly positive tails also rule out a rational sum, whose nonzero distances from integers after shifting would be bounded below by the reciprocal of its denominator.

For a general expansion $`b^n x=P_n+E_n`$ with $`E_n\to0`$, Lean also proves nonnormality when the residues of $`P_n`$ visit a fixed finite set with positive upper density. The centers can lie anywhere modulo one and the remainders may have either sign. [Prefix certificate](../NormalityChecker/Concentration.lean)

## Binary transitions and discrepancy

Lean proves that the upper limiting interval discrepancy of a binary expansion is strictly below one exactly when its digit transitions have positive lower density. If that density is $`t`$, the discrepancy is at most $`\max(2/3,1-t)`$. The period-two orbit of $`1/3`$ attains the constant $`2/3`$. [Sharp bound](../NormalityChecker/SharpDiscrepancy.lean)

For ln 2, this condition is equivalent to positive lower density of visits of the rational residues $`\{R_n\}`$ to the closed middle third. Every sufficiently late window $`[n,34n)`$ contains such a visit and a true digit transition. That yields an unconditional logarithmic count. A linear count, which would give a fixed discrepancy bound below one, remains open. [Proof and arithmetic obstacle](transition-discrepancy.md)

For the same recurrence, a positive lower limit of the average of $`1-\cos(2\pi R_n)`$ is also equivalent to discrepancy below one. Bounding the mean time elapsed since a middle-third hit would give an explicit lower density. Controlling the miss frequency for one fixed window length also suffices. The proof note gives the uniform-orbit benchmark and an exact finite experiment with 65,536 starts. [First-frequency proof and aggregate gap estimates](transition-discrepancy.md#first-frequency-escape)

## Open proof obligations

For the ordered normal sum $`F_K`$, the scaled error $`(K+1)2^K(\log 2-F_K)`$ is within $`1/(K+1)`$ of $`6/7,5/7,3/7`$ for $`K\equiv0,1,2\pmod{3}`$ respectively. Adding the corresponding rational correction to $`F_K`$ gives a normal sum $`G_K`$ with $`|2^n(\log 2-G_K)|\le 2^n/((K+1)^2 2^K)`$. The remaining step is to control Fourier averages as $`K`$ grows with the digit position. The finite classification allows its cutoff to depend on every nonzero cell coefficient. [Derivation and limits of the approximation](ordered-tail.md)

The corrected prefix $`C_n(n)`$ shadows $`2^{n+i}\ln 2`$ after $`i`$ doublings with error at most $`1/\sqrt{n+1}`$ for $`0\le i\le2n`$. For each $`\varepsilon>0`$, its reduced denominator $`Q_{n,n}`$ satisfies $`\log Q_{n,n}>(1-\varepsilon)n`$ outside a set of upper Banach density zero. The same holds for indices losing at least an $`\varepsilon`$ fraction of the primes in $`(n,2n]`$. Both estimates are uniform over all sufficiently long windows. Every adjacent pair also satisfies $`\max(Q_{n,n},Q_{n+1,n+1})\ge2^n`$. Individual dyadic starts can still be exceptional. At those starts a fixed positive first-frequency deficit on every sufficiently late complete block would prove a discrepancy bound below one. Another sufficient condition is a bounded mean square of $`-\log|\cos(\pi 2^n\ln2)|`$. Both estimates for the actual logarithm remain open. [Prime-survival proof](log-shadow-primes.md) · [Moment and dyadic criteria](classical-discrepancy.md)

For $`\varphi`$, binary discrepancy is strictly below one exactly when, for some fixed $`K`$, a positive lower density of the powers $`2^n`$ have a Zeckendorf summand of index at most $`K`$. Proving this density remains open. For $`\pi`$, a corrected BBP prefix gives a rational model over linearly many hexadecimal shifts. Unique upper-range primes survive in the uncorrected BBP denominator. [Quadratic and BBP proofs, experiments and literature](classical-discrepancy.md)

For $`\log 2`$, the rational prefixes eventually avoid every fixed finite set of exact residues modulo one. Approximate concentration remains possible. Proving cancellation uniformly over partial dyadic intervals at every odd frequency, or exhibiting persistent bias at one fixed odd frequency, would decide binary normality. The normality of $`\log 2`$ and $`\pi`$ remains open. [Exact obstruction](../NormalityChecker/DenominatorGrowth.lean) · [Dyadic criterion](logarithm-correlations.md)
