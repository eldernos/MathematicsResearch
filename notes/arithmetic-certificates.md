# Normality certificates for arithmetic expansions

The exact rational-prefix certificate below is the zero-error case of the approximate block theorem. For the finite Fourier bound, mixed rational weights, and dense polynomial expansions, see the [polynomial certificate proof guide](polynomial-certificates.md).

A rational approximation to a digit shift can lose many denominator factors and still be useful. For Weyl's criterion, what matters is whether its **reduced** denominator grows on sufficiently many blocks and whether the radix orbit cancels before the next insertion. This note gives the precise conditions and three ways of meeting them. [General certificate](../NormalityChecker/ArithmeticCertificate.lean) · [Definition of normality](../NormalityChecker/Basic.lean)

| Family or estimate | Result in Lean | Scope |
| --- | --- | --- |
| Modular orbits on a fixed set of denominator primes | Uniform cancellation for every fixed polynomial relation between denominator and block length | Qualitative estimate, with the prime set fixed before taking limits |
| Polylogarithms on a fixed finite prime support | A successful finite modular test implies normality at every specified positive integer order | Zero cells have an exact prefix-weighted discrepancy bound. [Partial certificates](finite-support-discrepancy.md) |
| Mixed generators $`q^a c^j`$ | Normal for every positive integer order | $`q,c\ge2`$, $`q\mid b^A`$ for some $`A`$, and $`\gcd(b,c)=1`$ |
| Binary Stoneham component with insertions at $`m^r`$ | Normal for every integer $`r\ge1`$ with the weights below | Local denominator dominance for $`r\ge2`$ and an exact sum for $`r=1`$ |
| Dense rational telescoping terms | Adding a certified difference preserves normality under the stated convergence assumptions | The certificate supplies an antidifference and the boundary term |

All normality assertions in the table have proofs in the repository. The sharper published exponential-sum estimates and the pole argument at the end of this note have a different status. The former are literature comparisons and the latter is a mathematical argument for review.

## What a certificate must establish

Write $`P_n`$ for a rational prefix with $`b^n x-P_n\to0`$. At scale $`N=(LB)^k`$ split each cell of length $`N`$ into $`L^k`$ blocks of length $`T=B^k`$, for fixed integers $`L>1`$ and $`B\ge1`$. The cells cover $`[N,LB N)`$. Fix $`c`$ coprime to $`b`$ and a polynomial exponent $`d`$. For every denominator floor $`M`$ and every $`\eta>0`$, eventually all but at most $`\eta L^k`$ block starts in each cell must satisfy the following conditions.

1. The reduced denominator $`Q`$ of $`P_n`$ is at least $`M`$, divides a power of $`c`$, and satisfies $`Q\le T^d`$.
2. Throughout the block, $`P_{n+i}=b^i P_n`$.

Multiplication by a fixed nonzero Fourier frequency $`h`$ can reduce $`Q`$ by at most $`|h|`$. The short-orbit estimate below thus controls every good full block. Exceptional blocks cost at most their total length. Stopping inside the final block costs at most $`T`$, a fraction $`L^{-k}`$ of the cell. This last bound is why cancellation holds for **every prefix length**. A schedule can meet the certificate after discarding a vanishing proportion of blocks, even though some individual gaps are short. [Block assembly](../NormalityChecker/CertificateBlocks.lean) · [Arithmetic hypotheses and Fourier transfer](../NormalityChecker/ArithmeticCertificate.lean)

## The fixed-prime-set estimate

Put $`e(t)=\exp(2\pi i t)`$. Fix integers $`b,c\ge2`$ with $`\gcd(b,c)=1`$. For each fixed integer $`d\ge1`$ and $`\epsilon>0`$, there is a threshold $`M(b,c,d,\epsilon)`$ such that

```math
\left|\sum_{i=0}^{T-1}e(Ab^i/Q)\right|\le\epsilon T
\quad\text{if}\quad
\gcd(A,Q)=1,\quad M\le Q\le T^d,\quad Q\mid c^j\text{ for some }j.
```

The threshold is uniform in the reduced numerator, the block length, and the exponents of the individual primes. If $`v_Q`$ is the multiplicative order of $`b`$ modulo $`Q`$, the linear period bound $`Q\le C v_Q`$ holds with $`C=b^{\varphi(c^2)}-1`$. Taking the totient of $`c^2`$ ensures that the lifting base is 1 modulo 4 when 2 divides $`c`$. [Period lemma](../NormalityChecker/StonehamOrder.lean) · [Fixed-support estimate](../NormalityChecker/SmoothOrbit.lean)

Here is how the short-block argument works. Use a scale $`K`$ with $`K^3\le T`$. Orthogonality and translation on a complete period give arbitrarily small normalized sums as $`Q\to\infty`$. Splitting into periods leaves at most $`Q`$ untreated terms. This proves the starting range $`Q\le K^2`$. Assume cancellation through $`K^{d+2}`$ and consider $`K^{d+2}<Q\le K^{d+3}`$. Dividing off primes from the fixed support gives $`D\mid Q`$ with $`K\le D\le cK`$. Translate the sum by multiples of the period $`v=v_D\le D`$. For two translates $`a<t<H`$, the reduced denominator of the correlation is $`Q/g`$, where

```math
g=\gcd\bigl(Q,b^{(t-a)v}-1\bigr),\qquad D\le g\le C(t-a)v\le CHcK.
```

The upper bound uses the period lemma at modulus $`g`$. Consequently $`Q/g\le K^{d+2}`$, while $`Q/g`$ still tends to infinity for each fixed $`H`$. The induction hypothesis controls the correlations. Cauchy–Schwarz applied to the translated sums controls the original sum. Choosing $`H`$ first makes the diagonal contribution small, and then $`Hv/T\to0`$ controls the translation endpoints. Choosing $`K=2^{\lfloor\log_8 T\rfloor}`$ covers arbitrary lengths and yields the stated polynomial range. [Finite differencing inequality](../NormalityChecker/OrbitDifferencing.lean) · [Induction](../NormalityChecker/SmoothOrbit.lean)

Vandehey's Corollary 1.2 supplies quantitative decay when $`T\ge Q^\epsilon`$, and his paper also obtains estimates in shorter ranges. The Lean proof establishes the qualitative consequence above. It can discharge the analytic hypothesis `SmoothOrbitEstimate` directly. Vandehey's Theorem 7.4 concerns series with strictly increasing coefficient denominators in a divisibility chain and a spacing condition. The checker here instead examines reduced **prefix** denominators and can allow exceptional blocks. Priority for particular applications remains a question for review. [Vandehey, *Differencing methods for Korobov-type exponential sums*](https://arxiv.org/abs/1606.07911) · [Earlier Lean development for Stoneham sums](https://github.com/CaptainSude/Stoneham-sum-normal/tree/f4d3d1f01d00c57425c684409849053e58e42261)

## Positive orders and composite generators

For $`s\ge1`$, consider the series with indices $`m=q^a c^j`$ and summands $`m^{-s}b^{-m}`$. Let $`q\mid b^A`$ for some fixed $`A`$ and $`\gcd(b,c)=1`$. Then $`q`$ and $`c`$ are coprime, so the index uniquely determines the two exponents. The shifted tail is bounded by $`(n+1)^{-s}\sum_{i\ge1}b^{-i}`$. The general Lean tail lemma only needs the late coefficients to tend uniformly to zero. [Tail lemma](../NormalityChecker/IndexedExpansion.lean) · [Literal series and normality](../NormalityChecker/MixedPowers.lean)

Fix any prime $`p\mid c`$. In a half-open interval of cutoffs $`(u,v]`$ with $`v\le qu`$, at most one new index occurs for each exponent $`j`$. Its local norm is $`p^{s j v_p(c)}`$. The term on the largest new layer therefore determines the local norm of the difference of the unshifted prefixes. Shifting either prefix by its radix power preserves its local norm. If an insertion on layer $`j`$ lies between two cutoffs, at least one endpoint has local norm at least $`p^{s j v_p(c)}`$. [Primewise separation](../NormalityChecker/CompositeLayers.lean)

On a cell of size $`K^2`$, where $`K=c^k`$, use blocks of length $`K`$. The established mesh of $`q^a/c^i`$ places an insertion with $`j=2k-i\ge k`$ between any two block starts separated by a fixed positive fraction of the cell, once $`k`$ is large enough. Both starts cannot have denominator below a prescribed $`M`$. The starts with small denominator therefore occupy arbitrarily small relative width. One prime divisor of $`c`$ suffices for this step because the orbit estimate requires the **whole denominator** to diverge. The proof also charges at most two blocks per insertion. There are $`O((\log N)^2)`$ insertions through $`N`$. The base factors of $`m^s`$ clear within $`O_{b,q,c,s}(\log N)`$ shifts. [Mesh](../NormalityChecker/LocalizedMeshRate.lean) · [Exceptional starts, clearing and normality](../NormalityChecker/MixedPowers.lean)

After clearing, every denominator divides $`c^{s\lfloor\log_c n\rfloor}\le n^s`$. Thus for $`T\asymp\sqrt n`$ any fixed exponent strictly larger than $`2s`$ in the polynomial-range estimate suffices eventually. The formal proof uses a looser fixed exponent for convenience. A new orbit estimate for each order is unnecessary. The earlier explicit discrepancy rate concerns the order-one prime-generator hypotheses. [Earlier rate and hypotheses](mixed-localized-logarithms.md#quantitative-interval-discrepancy)

For prime supports with **independent** exponents one can instead test all top-layer residues. At modulus $`p^L`$ the contribution from cofactor $`r`$ in layer $`k-i`$, after normalization by $`p^{sk}`$, is $`(p^i/r)^s w^r`$, where $`w`$ is the stabilized inverse radix. All layers with $`is\ge L`$ vanish. A passing test forces $`p^{sk-L+1}`$ to divide the shifted denominator on sufficiently late scales. `passesPower` checks an exact finite partition, and `normal_of_power_certificate` proves normality directly from success. Taking $`c`$ to be the product of the off-base primes works for arbitrary fixed support. The binary order-one examples on $`\{2,5,7\}`$, $`\{2,5,11\}`$, and $`\{2,5,7,11,13\}`$ are now unconditional corollaries. [Modular reduction](../NormalityChecker/LocalizedCertificate.lean) · [Analytic implication and unconditional theorems](../NormalityChecker/SmoothCertificates.lean) · [Worked examples](localized-certificates.md)

## Insertions at squares, cubes and every digit

Let $`S=\sum_{j\ge0}3^{-j}2^{-3^j}`$, including the initial term $`1/2`$. Lean proves binary normality of

```math
S+Z_r,\qquad Z_r=\sum_{m\ge1}3^{-\lfloor\log_3 m\rfloor}2^{-m^r}
```

for every positive integer $`r`$. For $`r\ge2`$ and $`3^j\le n<3^{j+1}`$, the shifted Stoneham prefix has 3-adic norm exactly $`3^j`$. If $`m^r\le n`$ then $`m<3^j`$ once $`j\ge1`$. Consequently the perturbation prefix has denominator dividing $`3^{j-1}`$. Even when insertions coincide, the larger local norm survives addition. Both shifted tails tend to zero. At scale $`N=16^k`$ the square schedule already bounds every higher degree, with $`O(N^{1/2})`$ insertions. Taking $`T=N^{1/4}`$ charges a proportion $`O(N^{-1/4})`$. The denominator is of order $`N`$ on this scale, and the qualitative short-orbit estimate controls the good blocks. [General perturbation theorem](../NormalityChecker/DominatedPerturbation.lean) · [Polynomial schedules](../NormalityChecker/PolynomialInsertions.lean)

The proposed cubic block length also works by a shorter paper argument. For $`T\asymp N^{3/5}`$, charging cubic insertions costs $`O(N^{1/3}T/N)=O(N^{-1/15})`$. At each fixed nonzero frequency, the existing binary orbit bound is $`O(\sqrt N\log N)`$, so its normalized contribution is $`O(N^{-1/10}\log N)`$. With squares, this charging method needs $`T=o(\sqrt N)`$ and the square-root orbit bound alone does not provide a saving there. The general proof above supplies precisely the shorter-block cancellation. [Elementary binary orbit bound](../NormalityChecker/OrbitSum.lean)

For $`r=1`$ there are no insertion-free blocks. Instead, on $`3^j\le m<3^{j+1}`$, the coefficient is constant. The sum of the radix weights on that interval is $`2(2^{-3^j}-2^{-3^{j+1}})`$. Summing the two boundary terms over $`j`$ gives $`Z_1=3-4S`$, hence $`S+Z_1=3-3S`$. The general identity `radix_plateau_sum` groups any summable geometric series with coefficients constant on these power intervals. [Regrouping identity](../NormalityChecker/RadixTelescoping.lean) · [Identity and normality at degree one](../NormalityChecker/PolynomialInsertions.lean)

## Rational telescoping and the logarithm barrier

If rational coefficients satisfy $`a_n=r_n+H_n-H_{n+1}/b`$, the first $`N`$ weighted terms differ from those of $`r`$ by exactly $`H_0-b^{-N}H_N`$. With summable weighted $`r`$ and $`H`$, the two infinite sums differ by the rational $`H_0`$, and their normality agrees. For example, adding $`1/(n+1)-1/(b(n+2))`$ to any such coefficient sequence introduces a term at every position and changes the value by exactly 1. If $`a,r`$ are rational functions, finding rational $`H`$ is a first-order linear difference equation of the type studied by Abramov. When the weighted difference is hypergeometric, Gosper's algorithm searches for a hypergeometric antidifference. The Lean theorem verifies a supplied identity and its convergence hypotheses. [Formal identity](../NormalityChecker/RadixTelescoping.lean) · [Abramov (1989)](https://www.sciencedirect.com/science/article/pii/S0041555389800023) · [Gosper (1978)](https://doi.org/10.1073/pnas.75.1.40)

The coefficients of $`\ln 2`$ change at every position. There is a concrete obstruction to applying the rational telescope above. With indices starting at zero, the weighted coefficient for $`\ln 2`$ is $`1/(2(n+1))`$. Suppose this coefficient, up to a polynomial, equaled $`H(n)-H(n+1)/2`$ for a rational function $`H`$. Its single pole at $`-1`$ forces $`H`$ to have a pole in the integer translate class of $`-1`$. If the first and last such poles are $`u\le v`$, the difference has poles at **both** $`u-1`$ and $`v`$. At each of these locations only one summand has a pole. This contradicts the single pole on the other side. This pole argument is a paper observation. The four-window target for the logarithmic recurrence still requires an unconditional bound on misses through every sufficiently large prefix. Neither the localized estimates nor the dense degree-one identity supplies that bound. [Four-window objective](transition-discrepancy.md#one-fixed-window-length-suffices) · [Denominator growth for ln 2](../NormalityChecker/DenominatorGrowth.lean)
