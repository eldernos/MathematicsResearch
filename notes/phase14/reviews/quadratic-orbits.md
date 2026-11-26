# Quadratic images of the dyadic Stoneham number

**Independent review, based on Phase 13 at `6d653be`.** Let *b* ≥ 3 be odd, let α be the sum of $`2^{-j}b^{-2^j}`$ over positive integers *j*, and put $`x=(A\alpha^2+B\alpha+C_0)/D`$ for integers $`A\ne0,B,C_0`$ and $`D\gt 0`$. Use half-open intervals in $`[0,1)`$ and count shifts $`0\le n\lt N`$. Write $`D_N(x)`$ for the supremum of the absolute interval-frequency error and $`D_\infty(x)`$ for its limsup.

Let $`y_k`$ be the actual rational prefix of *x* at the start of the last part $`[3\cdot2^{k-1},2^{k+1})`$ of shell *k*, advanced by a fixed number of radix shifts to clear primes dividing *b*. Let $`\Delta_b(y)`$ be the discrepancy of the uniform probability on the eventual orbit of the rational point *y*. Then

```math
D_\infty(x)=\frac14\limsup_{k\to\infty}\Delta_b(y_k).
```

The ordinary orbit is equidistributed exactly when the upper-shell denominators tend to infinity. Every such *x* has logarithmically weighted equidistribution and $`\liminf_N D_N(x)=0`$. These are paper deductions. The factor 1/4 is the exact maximum weight of an isolated plateau. Existence of a rational quadratic with $`D_\infty(x)=1/4`$ in this family remains open in this review. The proof gives an exact condition for attainment below. [Phase 13 quadratic identity](../../phase13/reviews/symmetric-degree.md#quadratic-projections-with-equal-valuations) · [Kernel-verified square profile](../../../NormalityChecker/ParameterTwoSquareProfile.lean)

## An exact 2-adic slope

Normalize $`v=v_2`$ by $`v(2)=1`$ and $`v(0)=+\infty`$. Put $`s=v(b^2-1)-1\ge2`$ and $`\delta_j=(b^{-2^j}-1)/2^j`$. We have $`v(\delta_1)=s`$ and

```math
\delta_{j+1}-\delta_j=2^{j-1}\delta_j^2.
```

Induction gives $`v(\delta_j)=s`$. The increments have strictly increasing valuations $`j-1+2s`$, so $`\lambda=\lim_j\delta_j`$ exists, $`v(\lambda)=s`$, and $`v(\delta_j-\lambda)=j-1+2s`$. Set $`e_j=\delta_j-\lambda`$, $`C=\lambda+\sum_{j\ge1}e_j`$, and $`T_k=\sum_{j=1}^k\delta_j+\delta_k`$. Set $`E_k=e_k-\sum_{j\gt k}e_j`$. Direct subtraction gives

```math
T_k=k\lambda+C+E_k.
```

In $`E_k`$ the unique summand of least valuation is $`e_k`$, giving the sharp equality $`v(E_k)=k-1+2s`$. The same argument gives $`v(C-\lambda)=2s`$ and $`v(C)=s`$.

For a cutoff *n*, let $`S_n^*`$ denote the shifted prefix for α, obtained by keeping indices $`2^j\le n`$ and multiplying each term by $`b^n`$. Let $`U_n^*`$ be the corresponding ordered-pair prefix for α² with $`2^i+2^j\le n`$. The integer-polynomial prefix is $`R_n=A U_n^*+B S_n^*+C_0b^n`$. In the plateau write $`S=\sum_{j=1}^k2^{-j}b^{-2^j}`$ and $`L=2^{-k}b^{-2^k}`$. The admitted square is $`S^2-L^2`$. At $`k=1`$ the sole plateau position is 3 and the same expression is zero, matching the empty square prefix. Substituting $`S=1+\sum_{j\le k}\delta_j-2^{-k}`$ and $`L=\delta_k+2^{-k}`$ shows that

```math
b^{-n}R_n+2^{-k}(2A+B+2AT_k)\ \in\ \mathbb Z_2 .
```

The actual $`R_n`$ is dyadic and $`b^n`$ a 2-adic unit. Its reduced denominator $`q_k`$ is constant on this plateau. Put

```math
a=v(2A\lambda),\qquad
\kappa=-\frac{2A+B+2AC}{2A\lambda}.
```

Since $`v(2AE_k)\ge k`$, the coefficients $`2A+B+2AT_k`$ and $`2A\lambda(k-\kappa)`$ agree modulo $`2^k`$. For $`k\ge1`$ write $`q_k=2^{f_k}`$. Clipping the exponent at zero gives the following exact formula, including at equality of the two leading valuations.

```math
f_k=\max\{0,k-a-v(k-\kappa)\}.
```

If $`v(2A+B)\lt a`$, then $`\kappa\notin\mathbb Z_2`$, $`v(k-\kappa)=v(2A+B)-a`$ for every *k*, and the denominators grow. Otherwise $`\kappa\in\mathbb Z_2`$. For every *h* there are arbitrarily large $`k\equiv\kappa\bmod 2^h`$, allowing arbitrarily large loss from the exponent *k*. Bounded denominators along an infinite subsequence require the stronger $`v(k-\kappa)\ge k-O(1)`$.

For algebraic $`\kappa\in\mathbb Z_2`$, take its primitive minimal polynomial $`F\in\mathbb Z[X]`$ of degree *d*. Since $`F(\kappa)=0`$, the difference quotient at the integers *k* belongs to $`\mathbb Z_2`$. Consequently $`v(k-\kappa)\le v(F(k))`$. At $`F(k)\ne0`$ the integer size bound gives

```math
v(F(k))\le\log_2|F(k)|\le d\log_2(k+1)+O_F(1).
```

Thus $`f_k\to\infty`$. This includes negative integers and zero. For $`\kappa`$ a positive integer the one index $`k=\kappa`$ gives $`q_k=1`$. Every other index satisfies the same bound. Integers are among the parameters with unbounded loss, and all give denominator growth.

## Detecting bounded denominators

For a fixed integer $`H\ge0`$, if $`k\lt l`$ and $`f_k,f_l\le H`$, then for $`k\gt a+H`$ the integer $`l-k`$ is divisible by $`2^{k-a-H}`$. In particular

```math
l\ \ge\ k+2^{k-a-H}.
```

At each fixed threshold the exceptional shell indices therefore have gaps tending to infinity and natural density zero **among shell indices**.

There is a direct binary-digit criterion. If $`\kappa\in\mathbb Z_2`$ has infinitely many ones, let $`r_1\lt r_2\lt \cdots`$ be their positions, starting the bit numbering at zero. Write $`m_j=\sum_{i\le j}2^{r_i}`$. Then

```math
q_k\longrightarrow\infty
\quad\Longleftrightarrow\quad
m_j-r_{j+1}\longrightarrow+\infty .
```

Indeed $`v(m_j-\kappa)=r_{j+1}`$. Conversely, along any unbounded sequence of *k* with bounded $`q_k`$, put $`t=v(k-\kappa)`$. Eventually $`2^t\gt k`$ and $`t`$ is finite. Then *k* is the least nonnegative truncation of $`\kappa`$ below bit *t*. Its bit *t* is zero while that of $`\kappa`$ is one. Hence $`k=m_j`$ and $`t=r_{j+1}`$. Finite binary expansions were covered by the integer case. A freely chosen 2-adic parameter can satisfy $`r_{j+1}=m_j+1`$ indefinitely, starting for instance at $`r_1=2`$. Realizing such a parameter with a rational quadratic in a specified odd radix is a separate arithmetic problem.

## Counting the real orbit at every cutoff

Write $`a_k=3\cdot2^{k-1}`$ and $`u_k=2^{k+1}`$. Set $`p_n=R_n/D`$. The difference $`b^nx-p_n`$ tends to zero in the real absolute value for either sign of the coefficients. For each omitted monomial term the radix factor has size at most one and the coefficient weights are absolutely summable. Each fixed term is eventually included. Between insertions the rational prefixes advance exactly by multiplication by *b*. Choose $`h\ge0`$ such that the part of $`D`$ supported on primes of *b* divides $`b^h`$. Define

```math
y_k=\{b^h p_{a_k}\},\qquad Q_k=\operatorname{den}(y_k).
```

For all large *k* this is the actual prefix at $`a_k+h`$ modulo one. Its denominator is coprime to *b*, satisfies $`q_k\mid Q_k\mid Dq_k`$, and has support among the fixed primes of $`2D`$ coprime to *b*. These divisibilities follow by multiplying by *D* to recover $`b^hR_{a_k}`$ and by using $`Dq_k`$ as a common denominator. Shifting farther around its cycle preserves its uniform measure. Keeping the integer part of $`R_{a_k}`$ through the division by *D* is essential.

For $`k\ge2`$, on the earlier half $`[2^k,a_k)`$ the square prefix has denominator exactly $`2^{2k-2}`$, and the linear prefix has denominator dividing $`2^k`$. For large *k*, the numerator of the leading term leaves exact pole order $`2k-2-v(A)\gt k`$ after addition. On a clean stretch after *h* shifts from the last insertion the reduced denominator for $`p_n`$ is at least that dyadic power. It is at most $`D2^{2k}`$ and is coprime to *b*. The following two counting consequences hold uniformly in half-open intervals and partial shell cutoffs.

1. A portion of the earlier half contributes its length times interval length with error $`o(2^k)`$. The same holds for the plateau along any sequence with $`Q_k\to\infty`$. To see this, partition into blocks of length $`L=2^{\lfloor k/2\rfloor}`$. At most $`O(k)`$ insertions occur in a shell, since on the earlier half only the new arms and the shell boundary can enter. Drop blocks meeting an insertion or the next *h* positions, and the incomplete end blocks. Their total length is $`O_{h}(kL)=o(2^k)`$. Every retained starting denominator is at most $`L^5`$ eventually, has fixed support coprime to *b*, and tends uniformly to infinity on the portion in question. The fixed-support short-orbit estimate gives $`o(L)`$ interval error per block. It also gives $`\Delta_b(y_k)\to0`$ when $`Q_k\to\infty`$, by taking a multiple of a full period of length at least $`Q_k`$. [Short-orbit theorem](../../../NormalityChecker/SmoothOrbit.lean) · [Uniform interval estimate](../../../NormalityChecker/SupportDiscrepancy.lean)
2. When $`y_k`$ has a fixed eventual orbit $`\mathcal O`$ of length *m*, any initial portion of its plateau contributes its length times the uniform mass $`\nu_{\mathcal O}(I)`$ with error $`O(h+m)`$. The preperiod costs at most *h* positions and the incomplete final period costs fewer than *m*. This count includes atoms at the left interval endpoint under the specified convention.

Let $`w_{k,N}=\max(0,\min(N,u_k)-a_k)/N`$ and put $`\Delta_k=\Delta_b(y_k)`$. A stronger all-prefix conclusion is

```math
D_N(x)-\max_{k\ge2} w_{k,N}\Delta_k\longrightarrow0 .
```

To prove it, take any sequence of cutoffs tending to infinity. Write $`2^K\lt N\le2^{K+1}`$, assigning an exact power of two to the shell just completed. Extract diagonally so that, for every fixed lag $`i\ge0`$, $`Q_{K-i}`$ tends to infinity or $`y_{K-i}`$ is a fixed rational point. This is possible since bounded denominators give a finite set of fractional parts. At most one lag can have bounded denominator on this subsequence. Two such lags would give bounded $`q`$ at a fixed positive index distance, contradicting separation.

Fix *J* and keep lags $`0,\ldots,J-1`$. The total earlier mass is at most $`2^{1-J}`$. Apply the two block counts to these finitely many shells. If one has bounded denominator, its included plateau weight is $`w`$ and its cycle measure is $`\nu`$. The empirical measure of the rational prefixes has interval counts $`(1-w)|I|+w\nu(I)`$ up to $`O(2^{-J})+o_J(1)`$ uniformly in *I*. If all retained denominators diverge, take $`w=0`$. The discrepancy of that mixture is exactly $`w\Delta(\nu)`$. For the proposed maximum, every other retained $`\Delta_k`$ tends to zero and every discarded weight is at most $`2^{1-J}`$. Let *J* tend to infinity. This proves the strong formula for the rational sample on the extracted subsequence, hence on all cutoffs by the subsequence criterion.

For the real sample, fixed interval counts need care at atoms. For instance $`\delta_{1-1/j}`$ tends weakly to $`\delta_0`$ on the circle, while $`[0,1/2)`$ has masses zero and one. For extreme discrepancy all circular arcs may be used, since taking a complement negates the centered mass and produces an ordinary interval for a wrapping arc. If two samples agree within circle distance $`\epsilon`$ after *M* terms, enlarge any arc by $`\epsilon`$ at each end, paying at most $`2\epsilon`$ in length and $`M/N`$ in exceptional mass. One may take a slightly larger enlargement to include both endpoints. Exchanging the samples and using complements gives a discrepancy difference at most $`2\epsilon+O(M/N)`$. This transfers the proven rational discrepancy to the real orbit, including shifts that cross the cut at zero. [Kernel-verified circle perturbation lemma](../../../NormalityChecker/CircleDiscrepancy.lean#L137)

For each *k*, $`w_{k,N}`$ increases up to $`N=u_k`$, where it equals exactly $`1/4`$, and decreases afterwards. This cutoff includes the observation at $`u_k-1`$ and excludes the new diagonal at $`u_k`$. Each fixed *k* has $`w_{k,N}\to0`$ as $`N\to\infty`$. Taking limsups proves the formula in the introduction. A finite cycle has positive discrepancy, for example at least the mass of one atom by using arbitrarily short arcs. Thus $`D_\infty(x)=0`$ exactly when $`q_k\to\infty`$, with no assumption about numerical discrepancy under rational scaling.

## Ordinary and logarithmic cutoffs

For any $`\epsilon\gt 0`$, all sufficiently large $`N`$ with $`D_N(x)\gt \epsilon`$ have a shell of bounded $`Q_k`$ within a fixed number of the most recent shells. Indeed the all-prefix maximum must exceed $`\epsilon/2`$, old weights decrease geometrically, and $`\Delta_k\gt \epsilon/2`$ bounds $`Q_k`$ uniformly by the short-orbit estimate. Separation gives density zero for the exceptional indices and for any fixed finite union of their translates. Each dyadic shell costs $`O(1)`$ in the sum of $`1/N`$ and the first *K* shells have total cost asymptotic to $`K\log2`$. Therefore

```math
\frac{1}{\log X}\sum_{1\le N\le X}\frac{D_N(x)}{N}\longrightarrow0,
\qquad \liminf_{N\to\infty}D_N(x)=0 .
```

Partial summation now gives equidistribution with observation weights $`1/(n+1)`$, uniformly in the test interval. Indeed its centered partial sums at *N* are bounded by $`ND_N(x)`$, so the absolute weighted error through *X* is bounded by $`D_X(x)+\sum_{N\lt X}D_N(x)/(N+1)`$. One recurring bounded plateau occupies an ordinary fraction $`1/4`$ at its end, however rare its shell indices. If $`D_\infty(x)\gt 0`$, the successive discrepancy differences are at most $`1/(N+1)`$, so every value between zero and $`D_\infty(x)`$ is a subsequential ordinary discrepancy.

## When the factor is attained

$`D_\infty(x)=1/4`$ holds exactly when $`Q_k\mid b-1`$ infinitely often. A finite cycle has discrepancy one precisely when it is a singleton. For a cycle of length at least two, an arc containing all its points has length bounded below by a positive constant, and an arc omitting some point has mass at most $`1-1/|\mathcal O|`$. Taking complements gives the same strict bound for deficits. Since $`\Delta_k\to0`$ along diverging $`Q_k`$, a limsup of one requires a recurring singleton. Its reduced denominator divides $`b-1`$. If a nonnormal rational quadratic exists in a given radix, multiply it by a bounded denominator recurring infinitely often. Its new cycle at those plateaus is $`\{0\}`$, so that integer multiple attains $`1/4`$. More generally, every positive $`D_\infty(x)`$ here is rational. A subsequence realizing a positive limsup eventually has bounded $`Q_k`$, so the maximum is attained by a recurring finite rational cycle. Its discrepancy is rational by taking the one-sided extrema of its centered cumulative distribution at the finitely many rational atoms.

For an **integer polynomial** the orbit factor is elementary. Write the reduced $`y_k=c/2^f`$ with $`f=f_k`$. If $`b\equiv1\bmod4`$, put $`t=v(b-1)`$. Its cycle consists of one residue class modulo $`2^{\min(f,t)}`$ among residues modulo $`2^f`$. Successive squaring gives $`v(b^{2^j}-1)=t+j`$, so the order equals the size of that class. The resulting grid has discrepancy $`2^{-\max(0,f-t)}`$. In particular $`D_\infty`$ is one quarter of this expression evaluated at $`\liminf f_k`$, interpreted as zero at infinity.

If $`b\equiv3\bmod4`$, the cycle is a singleton for $`f\le1`$. For $`f\ge2`$, put $`M=2^{\min(f,v(b^2-1))}`$ and let *d* be the residue of $`c(b-1)`$ in $`[0,M)`$. Applying the preceding order argument to $`b^2`$ gives two distinct residue classes, $`c`$ and $`bc`$ modulo *M*. Each cell of width $`M/2^f`$ contains two atoms. On a cell the centered cumulative distribution decreases with slope −1 and jumps by $`M/(2\cdot2^f)`$ at each atom. Its oscillation is the larger of the two gaps, hence

```math
\Delta_b(c/2^f)=\frac{\max(d,M-d)}{2^f}.
```

For example in base 3 the factors for $`1/4`$ and $`1/8`$ are $`1/2`$ and $`3/4`$, respectively. Thus the orbit discrepancy need not decrease with the dyadic denominator in this radix.

## The projection X² − 2X

Here $`\kappa=-C/\lambda`$ and $`v(\kappa+1)=s`$. Its binary expansion starts with *s* ones followed by a zero. In base 3 it is $`235\bmod256`$, giving $`v(3-\kappa)=3`$ at the Phase 13 integer plateau. Arbitrarily large valuation loss, the bound $`1/4`$, logarithmically weighted equidistribution, and ordinary lower discrepancy zero all follow. It is normal if this parameter is an integer. For an infinite binary expansion, ordinary normality is equivalent to $`m_j-r_{j+1}\to+\infty`$. Verifying that condition or producing infinitely many failures remains open for this projection.

The 2-adic logarithm gives $`\lambda=\tfrac12\log(b^{-2})`$, by taking $`\exp(2^j\lambda)=b^{-2^j}`$. Expanding the exponential and summing the convergent geometric series in $`\mathbb Q_2`$ gives

```math
C=\lambda+\sum_{m\ge2}\frac{\lambda^m}{m!}
                      \frac{2^{m-1}}{1-2^{m-1}} .
```

The interchange follows from $`s\ge2`$ and $`v(m!)\le m-1`$, which make the double series summable in either order. Yu's explicit bounds on $`v(\xi_1^{n_1}\cdots\xi_d^{n_d}-1)`$ assume fixed algebraic bases and integral exponents. For example, proving $`\exp(C)`$ algebraic would give the required setting for $`\exp(k\lambda+C)`$, because $`\exp(\lambda)=\pm b^{-1}`$ is algebraic and $`v(\exp(z)-1)=v(z)`$ on $`4\mathbb Z_2`$. The displayed infinite correction supplies no such algebraicity statement. I find no direct application of those bounds that controls this particular $`\kappa`$. [Yu, *p-adic logarithmic forms and group varieties III*](https://doi.org/10.1515/FORUM.2007.009)

**Independent finite checks.** For every odd base from 3 to 31, modular iteration at 128-bit precision verified all 1,200 exact $`E_k`$ valuations for $`1\le k\le80`$. An independent forward recurrence inserted each positive-index ordered pair at $`2^i+2^j`$ and each linear term at $`2^j`$. The modular constants were computed from the recurrence by taking $`\lambda=\delta_{129}\bmod 2^{128}`$ and summing $`e_j`$ through $`j=129`$ at that precision. At every plateau cutoff from shell 2 through position 1,023 it agreed with the exponent formula for the eight coefficient triples $`(1,0,0)`$, $`(1,-2,0)`$, $`(2,-4,7)`$, $`(-3,6,-5)`$, $`(4,1,-7)`$, $`(1,6,3)`$, $`(3,-30,4)`$, and $`(4,-8,3)`$, totaling 61,200 exact fractions. Sorting the full rational cycles in the same radices checked the explicit factors at all 3,840 reduced dyadic points of denominator at most 256, including zero. The finite checks support the calculations and give no asymptotic evidence of recurring bounded denominators for a particular quadratic.
