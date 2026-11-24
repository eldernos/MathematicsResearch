# A two-sided test for the binary expansion of log 2

Let $R_0=0$, $R_{n+1}=2R_n+1/(n+1)$, and $e(t)=\exp(2\pi i t)$. The initial terms are $0,1,5/2,16/3$. The shift error satisfies $0\le 2^n\log 2-R_n\le1/(n+1)$. Two equivalent ways to settle the binary normality question follow from the formal results.

* **Normality.** Fix any positive integer lag $r$. For every odd integer $h$, prove
  $$
  \sup_{0\le T\le M}\frac1M
  \left|\sum_{n=M}^{M+T-1} e\!\left(h(R_{n+r}-R_n)\right)\right|
  \longrightarrow 0,\qquad M=2^k\longrightarrow\infty.
  $$
  This condition is necessary and sufficient. The normalization is by the scale $M$, so very short intervals cause no problem.
* **Nonnormality.** Find one odd integer $h$, one real $\delta>0$, and arbitrarily large $N$ for which
  $$
  \left|\frac1N\sum_{n<N}e(hR_n)\right|\ge\delta.
  $$
  Existence of such a witness is also necessary and sufficient. The same $h$ and $\delta$ must work for unbounded $N$.

Both statements are tests in terms of infinite estimates. The finite component checker in this repository is executable because its separate arithmetic classification reduces that family to finitely many rational tests. [Exact statements](../NormalityChecker/FourierTest.lean) · [Finite classification](finite-sums.md)

## Why the tests work

For an orbit normal in base $b$, approximate the character $e(ht)$ on each of the $q=b^k$ word intervals by its value at the left endpoint. The error is at most $2\pi|h|/q$. For fixed $k$, the limiting mean of the step function is $q^{-1}\sum_{j<q}e(hj/q)$, since each word has limiting frequency $1/q$. If $q>|h|>0$, the sum is zero by orthogonality. Letting $k$ grow proves the necessary direction of the Fourier criterion. Weyl's theorem gives the converse. A perturbation tending to zero changes each fixed-frequency mean by a quantity tending to zero. In base two a factor of two in $h$ just shifts the exact orbit one position, so the odd frequencies suffice. [Fourier test](../NormalityChecker/FourierTest.lean) · [Approximation and odd frequencies](../NormalityChecker/Correlations.lean)

For a fixed $r\ge1$, differencing two shifted approximations gives
$$
R_{n+r}-R_n=2^n(2^r-1)\log 2+o(1).
$$
The multiplier $2^r-1$ is a positive integer. Normality is invariant under such a multiplier. To see the less immediate direction, take an arbitrarily large set of time shifts with $b^t$ in a common residue class modulo the multiplier. Distinct translates of a nonconstant character are then orthogonal in the limit under the scaled normality hypothesis. Cauchy–Schwarz forces the original mean to vanish. Finally, cancellation of all initial means implies the dyadic bound by subtracting sums through $M$ and $M+T$. The converse follows by summing complete dyadic blocks and the last partial block. [Dilation and orthogonal shifts](../NormalityChecker/Dilation.lean) · [Dyadic cells](../NormalityChecker/ScaleTransfer.lean)

## What changes at growing lags?

Put $D_{n,r}=R_{n+r}-2^rR_n$ and $B_{n,r}=(2^r-1)/(n+1)$. The exact finite recurrence gives
$$
0\le B_{n,r}-D_{n,r}\le\frac{2^r-r-1}{(n+1)^2}.
$$
In the induction step, the new reciprocal contributes $1/(n+1)-1/(n+r+1)\le r/(n+1)^2$ in addition to twice the previous error. Consequently $e(hR_n+gR_{n+r})$ can be replaced by $e((h+2^rg)R_n+g B_{n,r})$ with error at most $2\pi|g|(2^r-r-1)/(n+1)^2$. For fixed $h,g$ this tends to zero whenever $2^r=o(n^2)$. At $n=a2^k$, $r=k$, with $a$ a fixed positive integer, the unwrapped drift $D_{n,r}$ tends to $1/a$. For $a=2$ the omitted drift would change a frequency-one character by a factor tending to $-1$. [Drift bounds and limit](../NormalityChecker/GrowingLags.lean)

## Where the proof stops

The denominator-growth theorem rules out exact recurrence to any finite set of residue classes for these particular $R_n$. If two prefixes agree with the same real center modulo integers, they have the same reduced denominator. But $1/Q_n\to0$, so every fixed denominator eventually disappears. This leaves the frequency of *near* returns open. [Finite-set obstruction](../NormalityChecker/DenominatorGrowth.lean)

The finite-component orbit estimate works with a fixed set of insertion schedules and a common modulus on a cell. The logarithm introduces a term at every position. Its local recurrence controls the phase error, but the resulting model still contains the oscillatory factor involving $R_n$. The missing estimate is the dyadic bound above for all odd $h$, or a persistent bias for one fixed $h$. Checking only complete dyadic blocks would also leave the partial last block uncontrolled. No such cancellation estimate or bias witness is known here.

## Rational models on linear-length blocks

Let $`R_n`$ be the rational prefix with $`R_0=0`$ and $`R_{n+1}=2R_n+1/(n+1)`$. For $`0\le r\le n`$, put

```math
g_r(n)=\frac{r!\,n!}{(n+r+1)!},\qquad C_r(n)=R_n+\sum_{k=0}^{r-1}(-1)^k g_k(n).
```

**Verified inequality.** The one-step defect is exactly $`C_r(n+1)-2C_r(n)=(-1)^r g_r(n)`$. Indeed $`g_r(n)-g_r(n+1)=g_{r+1}(n)`$. The ratio of successive differences at $`m\ge n`$ is $`(k+1)/(m+k+2)\le1/2`$ for $`k<r`$, so $`g_r(m)\le2^{-r}/(n+1)`$. Propagating this defect over $`i`$ steps gives the bound $`(2^i-1)2^{-r}/(n+1)`$. The correction order is held fixed over that entire block. Dividing by $`2^i`$ and letting $`i`$ increase, the endpoint contributes a vanishing error because both the correction and the original shifted tail stay bounded. Thus

```math
\left|2^n\ln 2-C_r(n)\right|\le\frac{2^{-r}}{n+1}.
```

Setting $`y_n=C_n(n)`$ gives a single rational doubling orbit which shadows the **actual** shifts $`2^{n+i}\ln 2`$ with error at most $`1/(n+1)`$ at every $`0\le i\le n`$. Lean also gives a direct prefix estimate $`|R_{n+i}-2^iy_n|\le3/(n+1)`$. All distances here are unwrapped. The improvement from logarithmic to linear block length comes from cancelling the insertion defect to order $`n`$. [Definitions and proofs](../NormalityChecker/LogShadow.lean)

**Denominator obstruction (paper calculation).** These particular models introduce unbounded denominator primes. For any prime $`p=2n-1>3`$, $`R_n`$ has denominator prime to $`p`$, since its terms only divide by integers through $`n`$. All corrections through $`g_{n-3}(n)`$ are also integral at $`p`$. The denominator of $`g_{n-2}(n)`$ contains exactly one $`p`$, and its numerator is a unit. Including the last correction multiplies that term, up to sign, by

```math
1-\frac{g_{n-1}(n)}{g_{n-2}(n)}=1-\frac{n-1}{2n}=\frac{n+1}{2n}.
```

The multiplier is a unit at $`p`$ since $`n+1<p`$ and $`2n=p+1`$. Therefore $`p`$ survives in the reduced denominator of $`C_n(n)`$. This rules out one fixed prime support at **all** starts. The subsequent density theorem gives an exponential lower bound for almost every integer start. For each $`\varepsilon>0`$, the starts losing at least an $`\varepsilon`$ fraction of primes in $`(n,2n]`$ have upper Banach density zero, uniformly over long windows. The behavior of the specific numerators on dyadic starts remains open. The existing fixed-window target still asks for a positive frequency of middle-third visits. The shadowing inequality controls approximation error and supplies no visit-frequency estimate by itself. [Denominator proof and sharper shadow](log-shadow-primes.md) · [Four-window target](transition-discrepancy.md#one-fixed-window-length-suffices) · [Approximate certificate hypotheses](../NormalityChecker/ArithmeticCertificate.lean)
