# The omitted tail of the ordered normal sums for log 2

Write $F_K=\sum_{1\le m\le K,\,3\nmid m} T_m$. Each $F_K$ for $K\ge1$ is binary normal, and the infinite series equals $\log 2$. How accurately does $F_K$ represent a particular shift of the logarithm?

For every $K\ge0$ define $c_K$ by the table.

| $K\bmod 3$ | 0 | 1 | 2 |
|---|---:|---:|---:|
| $c_K$ | $6/7$ | $5/7$ | $3/7$ |

The following uniform bound is proved in Lean:
$$
\left|(K+1)2^K(\log 2-F_K)-c_K\right|\le\frac1{K+1}.
$$
Thus the scaled error has three explicit subsequential limits. Adding the rational correction gives another binary normal number for each $K\ge1$,
$$
G_K=F_K+\frac{c_K}{(K+1)2^K},\qquad
\left|2^n(\log 2-G_K)\right|\le\frac{2^n}{(K+1)^2 2^K}.
$$
These are deductions for this decomposition. The project makes no claim of priority. [Theorems and proofs](../NormalityChecker/OrderedTail.lean) · [Normality of the ordered sums](../NormalityChecker/FiniteClassification.lean)

## Where the three constants come from

Set $A=K+1$, let $i\ge0$, write $m=A+i$, and put $w_i=2^{-i-1}$. Only indices with $3\nmid m$ contribute. The first term of $T_m$, after multiplication by $A2^K$, is $Aw_i/m$. Replacing this by $w_i$ costs $iw_i/m\le iw_i/A$.

The rest of $T_m$ is exactly $T_{3m}$ by reindexing. The geometric majorant $T_s\le2\cdot 2^{-s}/s$ gives $T_{3m}\le 2^{-m}/m^2$ for $m\ge1$. Its scaled contribution is at most $Aw_i/m^2\le w_i/A$. Thus an active index contributes an error between $-iw_i/A$ and $w_i/A$ relative to its proposed leading term. An inactive index contributes zero to both sums. Since $\sum_i w_i=\sum_i iw_i=1$, the total error is between $-1/A$ and $1/A$.

It remains to sum $w_i$ over the active residues. The mask repeats every three indices and the weights drop by $1/8$ after each period. For $K\equiv0,1,2\pmod3$ respectively, the first three retained weights sum to $3/4,5/8,3/8$. Multiplication by $1/(1-1/8)$ gives the table.

## Consequences for digit shifts

On any schedules $K=K(i)$ and $n=n(i)$, the unwrapped shift error $2^n(\log 2-F_K)$ tends to zero **if and only if** $2^n/((K+1)2^K)$ tends to zero. The necessity follows even from the first omitted term among $K+1$ and $K+2$, at least one of which is indivisible by three.

The failure of approximation can persist modulo one. For $K\ge2$, at $n=K+\lfloor\log_2(K+1)\rfloor-2$ the shifted omitted tail lies in $(1/64,1/2]$. Its distance from every integer exceeds $1/64$. The corrected $G_K$ tracks the shift even at $n=K+\lfloor\log_2(K+1)\rfloor$, with error at most $1/(K+1)$.

The correction controls individual shifted values as the cutoff changes. The finite normality theorem gives limiting frequencies for each *fixed* $G_K$. Using the correction to establish normality of $\log 2$ still requires cancellation estimates uniform over the cutoffs and partial intervals involved. [Precise Fourier estimate still needed](logarithm-correlations.md)
