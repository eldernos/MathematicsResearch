# Normality of polynomial-weighted expansions

For coprime integers $`b,c\ge2`$, a nonzero rational polynomial $`P`$, and an integer $`s>\deg P`$, Lean proves that the following densely supported series is normal in base $`b`$.

```math
Y=\sum_{n\ge1}\frac{P(n)}{c^{s\lfloor\log_c n\rfloor}b^n}.
```

The same arithmetic argument proves normality with weight $`P(m)/m^s`$ on the mixed support $`m=q^a c^j`$, for $`q\ge2`$ dividing some power of $`b`$. Thus a finite rational linear combination of localized polylogarithmic orders on the **same** support is normal whenever its combined numerator is nonzero. For example, the weights $`7/m-3/m^2+5/m^4`$ give $`P(X)=7X^3-3X^2+5`$ and $`s=4`$. The theorem allows negative coefficients and composite $`c`$. [Dense theorem](../NormalityChecker/DensePolynomial.lean) · [Mixed theorem](../NormalityChecker/RationalWeights.lean)

## From every digit to the power boundaries

On the rational polynomials of degree less than $`s`$, consider $`H(X)\mapsto H(X)-H(X+1)/b`$. Translation preserves the leading coefficient. A nonzero polynomial in the kernel would have leading coefficient $`h=h/b`$, which is impossible. This linear endomorphism of a finite-dimensional space is therefore bijective. Taking the unique preimage of $`P`$ gives an antidifference of degree less than $`s`$. Since $`P\ne0`$, its preimage is nonzero.

Put $`F(n)=H(n)b^{-n}`$. The summand inside each plateau is a constant multiple of $`F(n)-F(n+1)`$. Summing the half-open interval $`[c^j,c^{j+1})`$ leaves both endpoints. Polynomial growth times geometric decay justifies regrouping the series. With the initial boundary displayed separately the result is

```math
Y=\frac{H(1)}b+(1-c^s)\sum_{j\ge1}\frac{H(c^j)}{c^{sj}b^{c^j}}.
```

Equivalently, including $`j=0`$ changes the outside constant to $`c^s H(1)/b`$. The nonzero integer multiplier and the rational translation preserve normality. The formal boundary theorem also allows any rational antidifference with absolutely summable radix weights whose values **at the powers of** $`c`$ agree with a suitable polynomial. This lets a reviewer test a piecewise formula directly. [Boundary identity, degree argument and normality](../NormalityChecker/DensePolynomial.lean) · [Signed dilation](../NormalityChecker/RationalWeights.lean)

For $`b=2,c=3,s=2,P(X)=X`$, one has $`H(X)=2X+2`$. Both the identity below and the binary normality of its left side are individual audited declarations.

```math
\sum_{n\ge1}\frac{n}{3^{2\lfloor\log_3 n\rfloor}2^n}
=2-16\sum_{j\ge1}\frac{3^j+1}{3^{2j}2^{3^j}}.
```

## Why signed orders survive together

Cancel the largest power $`X^t`$ dividing the numerator of the sparse series. Clear a common integer denominator of the remaining coefficients. Up to a fixed rational multiplier the weight becomes $`G(m)/m^r`$, where $`G\in\mathbb Z[X]`$, $`G(0)\ne0`$ and $`\deg G<r=s-t`$. The last inequality gives a vanishing shifted real tail on the injective insertion schedule, even with signed terms. [Reduction of rational weights](../NormalityChecker/RationalWeights.lean) · [Shifted tail estimate](../NormalityChecker/IndexedExpansion.lean)

Choose a prime $`p\mid c`$. If $`m=q^a c^j`$, then $`|m|_p=|c|_p^j`$ since $`q`$ is a unit at $`p`$. Also $`m\mid G(m)-G(0)`$. Once $`|c|_p^j<|G(0)|_p`$, this gives $`|G(m)|_p=|G(0)|_p`$ simultaneously for every $`a`$. The norm of a term in layer $`j`$ is now $`|G(0)|_p |c|_p^{-rj}`$. Below the stabilization threshold the term norms have a uniform upper bound because the numerators are integers. A sufficiently high layer dominates **both** those early terms and all preceding stabilized layers, provided there is at most one term at each layer. This last qualification matters for mixed supports. [Primewise stabilization and dominant term](../NormalityChecker/PolynomialLayers.lean)

On a single geometric axis, the whole prefix has distinct layers. In fact an arbitrary infinite subsequence of exponents suffices. For each denominator cutoff choose one sufficiently large selected exponent. Every later prefix includes it. This proves normality even with arbitrarily long gaps between selected exponents. It covers progression restrictions on $`c^j`$ whenever the selected progression is visited infinitely often. With only finitely many visits the sum is rational. [Restricted-axis theorem](../NormalityChecker/RationalWeights.lean)

On the mixed support, use the **difference of two unshifted prefixes** at cutoffs $`n<m\le qn`$. Each layer inserts at most one term in $`(n,m]`$. A high insertion therefore forces at least one of the two prefixes to have a large reduced denominator. The threshold mesh forces the starts with small denominator into a short interval. The existing sparse-insertion count, clearing delay, and fixed-prime-set orbit estimate now apply. This proof uses a single prime divisor of $`c`$ to witness growth and allows every prime divisor of $`c`$ in the smooth modulus. [Shared block proof](../NormalityChecker/MixedPowers.lean) · [Fixed-support estimate](../NormalityChecker/SmoothOrbit.lean)

## A finite test for periodic weights

Let $`A`$ be a rational coefficient of period $`d\ge1`$, with $`c\equiv1\pmod d`$, $`s\ge1`$, and $`b,c\ge2`$ coprime. Every plateau begins in class one. Compute one rational number

```math
W=\sum_{i=0}^{d-1} A(1+i)b^{-i}.
```

Lean proves that the dense plateau-weighted expansion with numerator $`A(n)`$ equals zero if $`W=0`$, and is base-$`b`$ normal if $`W\ne0`$. To see why, let $`F(x)`$ be the same discounted period starting at class $`x`$, divided by $`1-b^{-d}`$. Subtracting $`F(x+1)/b`$ from $`F(x)`$ leaves $`A(x)`$. Every power boundary has the same value $`F(1)`$, so a nonzero boundary invokes the constant-polynomial theorem. When $`F(1)=0`$ the boundary identity gives zero exactly. In particular, indicators of nonempty sets of residue classes pass the test, since a complete discounted period then has a positive contribution. [Periodic test and one-period computation](../NormalityChecker/PeriodicWeights.lean)

In base two with $`c=3`$, coefficients $`1`$ at even positions and $`-1/2`$ at odd positions give $`W=-1/2+1/2=0`$. The concrete identity holds even for $`s=0`$. Other periods can visit several boundary classes. On mixed supports with two independent exponents, restricting to residue classes also requires a mesh of selected insertions. These cases remain outside the periodic test. [Verified zero example and boundary criterion](../NormalityChecker/DensePolynomial.lean)

## Approximate blocks and quantitative control

A good block of length $`B`$ may use its own rational $`y=A/Q`$. For observations $`f_i`$, write $`e(t)=\exp(2\pi i t)`$ and let $`\|t\|`$ denote the distance to the nearest integer. At each integer frequency $`h`$,

```math
\left|\sum_{i<B} e(h f_i)\right|
\le \left|\sum_{i<B}e(h b^i y)\right|
 +2\pi |h|\sum_{i<B}\left\|f_i-b^i y\right\|.
```

Subtract the nearest integer at each position before using the Lipschitz bound for the character. On a cell of $`K`$ blocks, suppose the normalized orbit sum is at most $`\epsilon`$ and the mean distance is at most $`\delta`$ on every good block. If $`E`$ contains the exceptional block indices, then **every** prefix of the cell has Fourier sum bounded by

```math
(\epsilon+2\pi |h|\delta)KB+(|E|+1)B.
```

The final $`B`$ pays for the unfinished block. The qualitative certificate fixes $`h`$ first. Model denominators must grow away from exceptions, have fixed coprime prime support, and satisfy $`Q\le B^d`$ for one fixed exponent. The exact-orbit theorem is its zero-error specialization. [Finite Fourier bound and both certificates](../NormalityChecker/ArithmeticCertificate.lean)

For a finite interval count, suppose the same orbit bound holds simultaneously at every integer frequency $`0<|h|<H`$, with $`H\ge1`$. Let $`U=(\epsilon+2\pi H\delta)KB+(|E|+1)B`$. For any prefix of length $`T\le KB`$, write $`A_T(I)`$ for the number of its observations modulo one in the half-open interval $`I\subseteq[0,1)`$. For every smoothing width $`w>0`$, Lean proves

```math
\left|A_T(I)-T\,|I|\right|
\le 2\left[T\left(4w+\frac3H+\frac{1}{w^2H}\right)+HU\right].
```

Dividing by $`T>0`$ gives a bound uniform over intervals. A rate for a particular expansion requires estimates of $`U`$ as $`H`$ increases. [Formal interval-count bound](../NormalityChecker/ApproximateDiscrepancy.lean)

## Comparisons and open scope

Bailey and Crandall’s Corollary 4.9(v) treats unit weights on a selected geometric axis with ultimately nondecreasing exponent gaps. Vandehey’s Theorem 7.4 already covers the unit-numerator single-axis series with **any** infinite selection here. Indeed, for increasing selected exponents $`j_k`$, take $`m_k=c^{j_k}`$ and denominator $`c_k=c^{s j_k}`$. These form a divisibility chain, and $`m_k-m_{k-1}\ge(1-1/c)m_k`$ dominates the subpower spacing requirement. Finite initial terms are rational. Polynomial numerators and mixed supports require an additional argument about the *reduced prefix*, given above. The polynomial antidifference is a special case of classical symbolic summation. The distributional step comes after collecting its boundary terms. Independent assessment of priority for the combined statements remains open. [Bailey and Crandall, Theorem 4.8 and Corollary 4.9](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf) · [Vandehey, §7.2](https://arxiv.org/pdf/1606.07911) · [Gosper, 1978](https://doi.org/10.1073/pnas.75.1.40)

The dense polynomial examples admit exact sparse reductions. A dense application of the approximate certificate that lacks such a reduction remains open. The logarithmic recurrence now has long accurate rational models, with a separate obstacle at the denominator step. [Logarithm block estimates](logarithm-correlations.md#rational-models-on-linear-length-blocks)
