# Prime survival in the corrected models of ln 2

Write $R_n=\sum_{k=1}^n 2^{n-k}/k$, and let $Q_{n,r}$ be the reduced denominator of

```math
C_r(n)= R_n+\sum_{j=0}^{r-1}(-1)^j\frac{j!\,n!}{(n+j+1)!}.
```

For every fixed $\varepsilon>0$, both of the following sets have **upper Banach density zero**. This means that the fraction of exceptions in $[A,A+T)$ tends to zero as $T\to\infty$, uniformly in the starting index $A$.

- Indices $n$ for which $\log Q_{n,n}\le(1-\varepsilon)n$.
- Indices $n$ for which at least an $\varepsilon$ fraction of the primes $n<p\le2n$ disappear from $Q_{n,n}$.

In particular, windows beginning at $2^k$ are covered however slowly their lengths tend to infinity. The single index $2^k$ can still be exceptional. An elementary pointwise bound gives $\max(Q_{n,n}, Q_{n+1,n+1})\ge 2^n$ for every $n$. [Uniform bounds in moving windows](../NormalityChecker/WindowShadow.lean) · [Exact adjacent step](../NormalityChecker/DiagonalStep.lean) · [Natural-density corollaries](../NormalityChecker/TypicalShadow.lean)

## How long the model follows the logarithm

The finite differences have the beta-integral representation $j!n!/(n+j+1)!=\int_0^1 t^n(1-t)^j\,dt$. The expression for $2^n\log 2-R_n$ has integrand $t^n/(2-t)$. Subtracting $r$ alternating geometric terms yields the identity

```math
2^n\log2-C_r(n)=(-1)^r\int_0^1\frac{t^n(1-t)^r}{2-t}\,dt.
```

For $r=n$, the absolute error is at most $(n!)^2/(2n+1)!$. The beta-integral recurrence gives $4^n(n!)^2/(2n+1)!\le1/\sqrt{n+1}$. Hence at **every** shift $0\le i\le2n$, including the last one, the unwrapped error of the same model is at most $1/\sqrt{n+1}$. [Integral identity and inclusive endpoint estimate](../NormalityChecker/LogShadowIntegral.lean)

For $0\le r\le\theta n$ with fixed $\theta<1$, each odd prime $(n+r)/2<p\le n$ occurs in precisely one prefix term and divides none of the correction denominators. Summing $\log p$ over the smaller interval $((1+\theta)n/2,n]$ gives $\log Q_{n,r}\ge((1-\theta)/2-\varepsilon)n$ uniformly in these $r$, for every $\varepsilon>0$ and all sufficiently large $n$. [Prime survival](../NormalityChecker/ShadowDenominator.lean) · [Subcritical growth](../NormalityChecker/ShadowGrowth.lean)

## The diagonal binomial test

For $n<p\le2n$, put $d=2n-p$. The exact criterion is

```math
p\mid Q_{n,n}\quad\Longleftrightarrow\quad T_n:=\sum_{j=0}^{d}\binom nj\ne0\pmod p.
```

The prefix $R_n$ has no pole at $p$. The common correction denominator $(2n)!$ contains $p$ exactly once. At that denominator the $j$th signed correction numerator is $A_j=(-1)^j j!n!\prod_{m=n+j+2}^{2n}m$. Put $l=p-n-1$. The earlier $A_j$ vanish modulo $p$, while $A_l$ is a unit. The relation $(n+j+2)A_{j+1}=-(j+1)A_j$ gives $A_{l+a}=A_l\binom na\pmod p$ for $0\le a\le d$. Summing proves the criterion. [Binomial survival theorem](../NormalityChecker/BinomialShadow.lean)

## An exact obstruction on every adjacent pair

Put $y_n=C_n(n)$ and $D_n=2(2n+1)\binom{2n}{n}$. The one-step prefix recurrence and the extra diagonal correction combine to give

```math
y_{n+1}-2y_n=(-1)^n\frac{3}{D_n}.
```

Indeed the two factorial quotients are $(n!)^2/(2n+1)!$ and exactly half that value, with the same sign. Clearing the least common multiple of the two reduced model denominators gives $D_n\mid3\operatorname{lcm}(Q_{n,n},Q_{n+1,n+1})$. For $n\ge4$, $4^n<n\binom{2n}{n}$, and checking the first four indices gives $\max(Q_{n,n},Q_{n+1,n+1})\ge2^n$ at every index. Each prime $p>3$ with $n<p\le2n+1$ occurs in at least one member of the pair, including the endpoints $p=n+1$ and $p=2n+1$ when prime. [Exact step and denominator bound](../NormalityChecker/DiagonalStep.lean) · [Prime-by-prime result](../NormalityChecker/AdjacentShadow.lean)

## Why repeated cancellations are scarce

Fix $p>3$. Let $H_n=\binom n{d+1}\bmod p$ with $\lceil p/2\rceil\le n<p$. This is a unit. When $n+1<p$, Pascal's rule and $d\equiv2n\pmod p$ give the following two recurrences in $\mathbb F_p$.

```math
2T_{n+1}=4T_n+3H_n,\qquad 2(2n+3)H_{n+1}=-(n+1)H_n.
```

The first immediately rules out $T_n=T_{n+1}=0$. Applying this to every prime $n+1<p\le2n$ shows that their product divides $Q_{n,n}Q_{n+1,n+1}$ for $n\ge3$. The logarithm of this prime product is $n+o(n)$. [Adjacent survival](../NormalityChecker/AdjacentShadow.lean)

For $h>0$, $2h<p$, iterating the recurrences gives a polynomial of degree at most $h$ vanishing at any $n$ with $n+h<p$ and $T_n=T_{n+h}=0$. For clarity, take $D_j(X)=2(2(X+j)+3)$, $V_0=1$, $W_0=0$, and form

```math
V_{j+1}=-(X+j+1)V_j,\qquad W_{j+1}=D_j(2W_j+3V_j).
```

If $T_n=0$, then $H_nW_h(n)=2T_{n+h}\prod_{j<h}D_j(n)$. Also $V_j(-1)=0$ for $j\ge1$, $W_1(-1)=6$, and $W_{j+1}(-1)=2D_j(-1)W_j(-1)$ for $j\ge1$. Every factor here is nonzero since $2h<p$. Thus $W_h$ is a nonzero polynomial. The field root bound and injectivity of reduction on $0\le n<p$ give at most $h$ such pairs. [Polynomial obstruction and root count](../NormalityChecker/ShadowCancellations.lean)

For any $H$ with $2H<p$, group candidate indices into consecutive intervals of $H+1$ integers. Each interval contains at most one first failure. Every later failure shares its interval with an earlier failure at a gap $1\le h\le H$. The number $E_p$ of failing indices satisfies

```math
E_p\le \left\lfloor\frac p{H+1}\right\rfloor+1+H^2.
```

Choosing $H$ of order $p^{1/3}$ gives $E_p=O(p^{2/3})$. To obtain the result for integer indices, sum the missing prime weights $L_n=\sum_{n<p\le2n,\ p\nmid Q_{n,n}}\log p$ in the opposite order. The finite bound in Lean is

```math
\sum_{n<N} L_n\le\vartheta(2N)\left(\frac{2N}{H+1}+1+H^2+2H+4\right).
```

First let $N\to\infty$ with $H$ fixed, then let $H\to\infty$. The sum is $o(N^2)$. A set of $m$ distinct nonnegative indices has sum at least $m(m-1)/2$, so the indices costing $L_n\ge\delta n$ have density zero. The prime number theorem gives $\vartheta(2n)-\vartheta(n)\sim n$. On $(n,2n]$ the log weights differ by at most $\log2$. These observations yield both density-zero statements above. The one-frequency test still requires an estimate on the orbit of the particular numerator. [Double count, averaging and natural-density proofs](../NormalityChecker/TypicalShadow.lean)

## Why the bound holds in moving windows

In a window $[A,A+T)$, group cancellations for a fixed prime into consecutive bins of length $H+1$ starting at $A$. At most $T/(H+1)+1$ observations can be first in their bin. Every other observation is the upper endpoint of a pair separated by $h\le H$. The polynomial bound for pairs holds throughout the prime's residue interval, so all bins together contribute at most $H^2$ additional observations. Double counting with log weights gives

```math
\sum_{A\le n<A+T}L_n\le\vartheta(2(A+T))\left(\frac{T}{H+1}+1+H^2+2H+4\right).
```

For $A\le T$, the initial interval $[0,2T)$ contains the window and the natural-density estimate applies. For $A>T$, Chebyshev's upper bound gives $\vartheta(2(A+T))\le12A$. Each late exceptional index costs at least $\delta n\ge\delta A$ for some $\delta>0$ depending on the tolerance. After dividing by $\delta AT$, the surviving upper bound is at most $12/(\delta(H+1))+O_H(1/(\delta T))$. Choosing $H$ first and then $T$ makes the exceptional fraction arbitrarily small, uniformly over $A$. The pointwise cost bounds use the prime number theorem for $\vartheta$, proved in Mathlib. [Window double count](../NormalityChecker/TypicalShadow.lean) · [Upper Banach density](../NormalityChecker/WindowShadow.lean)

## Finite reproduction

| $n$ | Primes in $(n,2n]$ | Survive |
| ---: | ---: | ---: |
| 100 | 21 | 20 |
| 500 | 73 | 73 |
| 1,000 | 135 | 135 |
| 2,000 | 247 | 247 |
| 5,000 | 560 | 560 |

At $n=100$ the cancellation is $p=101$. The script computes the integer partial-binomial sums exactly. The tests compare them with independently reduced rational corrections at small indices. [Experiment](../scripts/discrepancy_experiments.py) · [Tests](../scripts/test_localized_certificate.py)

```sh
python3 scripts/discrepancy_experiments.py binomial 100 500 1000 2000 5000
```
