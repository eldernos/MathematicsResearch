# A finite rational test for binary normality

Let $M$ be a finite set of positive integers, let $a_m$ be rational, and write
$$
T_m=\sum_{j\ge0}\frac{2^{-m3^j}}{m3^j},\qquad F=\sum_{m\in M}a_mT_m .
$$
Choose any positive integer $S\ge\max M$, or $S=1$ for an empty set. For each integer $S\le u<3S$, let $j_m(u)$ be the largest $j\ge0$ with $m3^j\le u$. Compute
$$
H_u=\sum_{m\in M}\frac{a_m(-1)^m}{m3^{j_m(u)}} .
$$

**Theorem.** $F$ is binary normal if and only if every $H_u$ is nonzero. This test also works for negative coefficients, zero coefficients and indices divisible by three. The implementation chooses $S=\max(1,\max M)$ and uses exact rational arithmetic. Normality uses the limiting frequencies of all finite overlapping binary blocks. [Classification and executable test](../NormalityChecker/FiniteClassification.lean) · [Definition of normality](../NormalityChecker/Basic.lean)

For comparison with the piecewise function in the research conversation, take $S=3^d\ge\max M$. If $m=3^\ell r$ with $1\le r<3$, the insertion depth on $[u/S,(u+1)/S)$ is $d-\ell$ at and above $r$, and $d-\ell-1$ below $r$. Thus $S H_u$ equals the proposed piecewise function. Each discontinuity is a grid point. A finer grid can repeat the same test.

## The arithmetic on one cell

Choose an integer $D>0$ such that $c_m=Da_m/m$ is integral for every $m$. Consider $n=u3^k+i$, $0\le i<3^k$. For each component use its prefix through $J=k+j_m(u)$. Then $m3^J\le n+1\le m3^{J+1}$. At equality with the next insertion the omitted term is included in the tail bound.

Since $2^{3^j}\equiv-1\pmod{3^{j+1}}$, the term $2^{n+1-m3^j}/3^j$ equals $(-1)^m2^{n+1}/3^j$ modulo one. Summing this geometric progression through $J$ leaves $-(-1)^m2^n/3^J$ modulo one. The uninserted exponents increase at least one position per index, so their shifted sum lies between zero and $2/3^{J+1}$. After summing with signed integer weights, there is an integer $z$ with
$$
\left|2^{n+1}DF+2^n DH_u/3^k-z\right|
\le 3^{-k}\sum_{m\in M}2|c_m|.
$$
This estimate is uniform over the cell, including partial final cells. [Prefix congruence and tails](../NormalityChecker/Insertion.lean) · [Cell approximation](../NormalityChecker/CellModel.lean)

## A cell with zero coefficient

If $H_u=0$, all $3^k$ shifts in that cell approach the grid of multiples of $1/D$ modulo one. They occupy a proportion tending to $1/(u+1)$ of the prefix ending just after the cell. For a normal number and a fixed finite set of $d$ centers modulo one, the upper frequency within distance $\varepsilon$ of those centers is at most $2d\varepsilon$. The proof counts integer translates of intervals using floor differences, including intervals that cross zero. Choosing a small enough radius yields a contradiction. [Finite-set concentration certificate](../NormalityChecker/Concentration.lean)

## Cells with nonzero coefficients

Write $e(t)=\exp(2\pi i t)$. For a fixed nonzero integer frequency $h$, the model character on the cell is $e(A2^n/3^{k+E})$ with fixed nonzero integer $A$, since $DH_u$ has a power-of-three denominator. Remove the fixed power of three dividing $A$. For the remaining unit multiplier and modulus $q$, the sum over any consecutive exponent interval has norm at most $5\sqrt q(1+\log q)$ for $q\ge9$.

To obtain this estimate, let $r=\lceil(\log_3 q)/2\rceil$ and $L=2\cdot3^{r-1}$. The identity $2^L=1+c3^r$ has $c\equiv1\pmod3$. All quadratic and higher terms vanish modulo $q$ when this quantity is raised to a nonnegative integer power. Splitting into rows of stride $L$ gives geometric sums with ratio $e(v/m)$, $m=q/3^r$. Their norms are at most $m/(2\min(v,m-v))$ for $1\le v<m$. The order of two modulo $m$ is $2m/3$, so in each such period of row indices the residues $v$ are distinct. Bounding the reciprocal sums by the harmonic sum gives at most $m(1+\log m)$ per period. The rows comprise one or three periods, and the last incomplete rectangle contributes at most $L$. [Modular lift and order](../NormalityChecker/Linearization.lean) · [Incomplete sum](../NormalityChecker/OrbitSum.lean)

The orbit bound is $o(3^k)$, uniformly in the last endpoint. The true and model characters differ by $O(3^{-k})$ per position for fixed $M,h,D$. There are only $2S$ cells per scale. Complete scales have geometrically increasing lengths. Summing the cell estimates, including the partial last cell, proves that the Fourier means tend to zero at every nonzero frequency for $2DF$. [Passage to arbitrary prefixes](../NormalityChecker/ScaleTransfer.lean)

One final step removes the integer multiplier. For any integer $d>0$, there are arbitrarily large finite sets of distinct shifts $t$ with $2^t$ equal modulo $d$. For $a\ne b$ in one such set the difference $h(2^a-2^b)$ is a nonzero multiple of $d$. Its Fourier mean tends to zero by the hypothesis on $dF$. Averaging $K$ time translates of $e(h2^nF)$ therefore has limiting mean-square $1/K$, after normalizing the translate sum by $K$. Each fixed translation changes the original mean by a vanishing endpoint error. Cauchy–Schwarz followed by $K\to\infty$ forces the original mean to vanish. Applying this with $d=2D$ and using Weyl’s criterion proves binary normality of $F$. [Integer dilation](../NormalityChecker/Dilation.lean) · [Weyl criterion](../NormalityChecker/Analysis/Weyl.lean)

## Consequences and scope

- For $T_1+aT_2$ the two tests, up to nonzero factors, are $-1+a/2$ and $-1+3a/2$. The two exceptional rational coefficients are exactly $2$ and $2/3$.
- Each $T_m$ with $m>0$ is binary normal. The unweighted sum $T_{20}+T_{28}+T_{35}$ fails the test at $u=84$.
- Every ordered sum over $1\le m\le K$, $3\nmid m$, is binary normal for $K\ge1$. Clear the powers of three in $H_u$. The remaining signed numerator over each $m$ is odd. The unique largest power of two among the indices prevents the resulting sum from vanishing. [Lean corollaries](../NormalityChecker/FiniteClassification.lean) · [Parity argument](../NormalityChecker/OrderedComponents.lean)

The constants in the cell argument depend on the finite family. Applying it to $\log 2$ would require estimates with an increasing number of components and changing coefficients and scales. Convergence of the ordered sums to $\log 2$ alone gives no control of those digit frequencies.

The classical context includes Stoneham’s construction and Wall’s results on rational transformations of normal numbers. The proofs here give the deductions directly for this family. Originality of the finite classification has not been established. [Stoneham, Acta Arithmetica (1973)](https://doi.org/10.4064/aa-22-3-277-286) · [Bailey and Crandall, Random Generators and Normal Numbers](https://doi.org/10.1080/10586458.2002.10504704)
