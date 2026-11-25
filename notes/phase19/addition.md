# The exact addition spectrum of extreme discrepancy

Fix an integer base $b\ge2$. For $N\ge1$, let $D_N(z)$ be the supremum, over half-open circle arcs $I$, of the absolute difference between the proportion of $\{b^n z\}$ in $I$ for $0\le n<N$ and the length $|I|$. Here $\{s\}$ denotes fractional part. An arc and its complement have opposite excesses, so the positive supremum suffices. This is also the extreme discrepancy over ordinary intervals in $[0,1)$.

**Theorem.** A triple $(\alpha,\beta,\gamma)\in[0,1]^3$ occurs as the three limits for $x,y,x+y$ if and only if

$$
\max(0,\alpha+\beta-1)\le\gamma\le 1-|\alpha-\beta|.
$$

Fix any odd prime $p\nmid b$, and put $t=\mathrm{ord}_p(b)$. Every permitted triple has witnesses of the form

$$
x=\sum_{k\ge1}c_k b^{-tk^3},\qquad y=\sum_{k\ge1}d_k b^{-tk^3},
$$

with $0<c_k,d_k\le1$ rational of reduced denominator a power of $p$ (including $1$). For every $N\ge1$,

$$
\max\bigl(|D_N(x)-\alpha|,|D_N(y)-\beta|,|D_N(x+y)-\gamma|\bigr)
\le C_{b,p}N^{-1/3}.
$$

The same constant works on the whole closed region. Both series are uniformly computable from Cauchy names for an admissible triple. The three projected orbit laws converge weakly to $\alpha\delta_0+(1-\alpha)\lambda$ and the corresponding laws with $\beta,\gamma$, where $\lambda$ is normalized length on the circle.

## The five vertices

At any cutoff write $a=D_N(x)$, $b'=D_N(y)$ and $c=D_N(x+y)$. The sharp translation theorem gives $|c-a|\le1-b'$ and, interchanging the summands, $|c-b'|\le1-a$. Thus $c\ge a+b'-1$, $c\le1+a-b'$ and $c\le1+b'-a$. This proves necessity even at each finite cutoff and along any common subsequence of convergent values. [Phase 18 proof](../phase18/translations.md) · [Lean theorem sharp_translation](../../NormalityChecker/SharpTranslation.lean)

For the converse set $s=\max(0,(\alpha+\beta+\gamma-1)/2)$. The three facet inequalities say $\alpha+\beta+\gamma-1$ is at most each of $2\alpha,2\beta,2\gamma$. Hence $s\le\min(\alpha,\beta,\gamma)$. The following weights are nonnegative, the last one by $2s\ge\alpha+\beta+\gamma-1$. They sum to one.

| Projected point-mass indicators for x, y, x+y | Pair of target states modulo one | Weight |
| --- | --- | --- |
| (1, 1, 1) | $(0,0)$ | $s$ |
| (0, 1, 0) | $(u,0)$ | $\beta-s$ |
| (1, 0, 0) | $(0,u)$ | $\alpha-s$ |
| (0, 0, 1) | $(u,-u)$ | $\gamma-s$ |
| (0, 0, 0) | $(u,u)$ | $1-\alpha-\beta-\gamma+2s$ |

For each projected coordinate the total weight marked 1 equals its requested limit. Write $w_i$ for the five weights in table order. In block $k\ge1$ use $u=1/q_k$, where $q_k$ is the smallest power of $p$ strictly greater than $k$. Thus $k<q_k\le pk$. Every active projection is one of $u,-u,2u$, all of exact denominator $q_k$ because $p$ is odd.

## Scheduling and positive coefficients

Put $n_k=tk^3$, $h_k=n_{k+1}-n_k$, and use $(0,0)$ in block $0$. Block $k$ controls the times $n_k,\ldots,n_{k+1}-1$. Before choosing block $k\ge1$, let $C_i$ count type $i$ among the previous $k-1$ choices. Choose a type maximizing $kw_i-C_i$, breaking ties by the table order. The deficits sum to one, so the chosen type has positive deficit. Immediately after the choice its overcount relative to $kw_i$ is at most one. Unchosen overcounts can only decrease. Starting from zero, each overcount remains at most one and, by their zero sum, at least $-4$.

There is a uniform implementation from arbitrary Cauchy names, including at equality in any comparison. Compute rational $\widehat w_i$ with $|\widehat w_i-w_i|\le1/(20k)$; the finite formulas with absolute value and maximum are computable. Compare $k\widehat w_i-C_i$ exactly and take the first maximizer. The largest true deficit is at least $1/5$, so the chosen true deficit is at least $1/5-2/20>0$. The same count bounds follow. This rational procedure may schedule different types from the exact rule.

For either coordinate let $u_k\in[0,1)$ be its prescribed state and put $u_0=0$. Choose its coefficient at $n_k$ as the representative in $(0,1]$ of $u_k-b^{n_k-n_{k-1}}u_{k-1}$ modulo one. Its denominator divides $\max(q_k,q_{k-1})$ for $k\ge2$, and divides $q_1$ at $k=1$. Multiplying the partial sum through $k$ by $b^{n_k}$ gives fractional part $u_k$, by induction. The sum of the two partial series consequently has the *sum* of their prescribed states modulo one, including exact cancellation. Each omitted scalar tail after insertion $k$ is at most $B b^{-n_{k+1}}$ with $B=b/(b-1)$, by geometric summation. This also supplies a uniform computable error bound for the series. [Positive recurrence and complete-period estimate](../phase18/programming.md)

## Every prefix, including unfinished blocks

Fix a projection $z=x,y$ or $x+y$ with prescribed value $\delta$. For $N\ge t$ let $K$ be determined by $n_K\le N<n_{K+1}$. Let $\ell_k=|[0,N)\cap[n_k,n_{k+1})|$, and let $Z$ count the observed times in blocks marked 1 for this projection, including block zero. The model in block $k$ follows the projected target under multiplication by $b$.

**Time proportion.** Two types in the table are marked 1 for each projection. Thus the prefix sums of the deviations of their aggregate indicator from $\delta$ have absolute value at most $8$. Summation by parts with the increasing weights $h_k$ bounds the error over completed blocks $1,\ldots,K-1$ by $16h_{K-1}$ (zero when $K=1$). The unfinished block costs at most $h_K$, and the initial block at most $t$. Hence $|Z-N\delta|\le t+17h_K$.

**Active periods.** Write $v=v_p(b^t-1)$. For a unit numerator of denominator $q=p^e$, the Phase 18 prime-power lemma bounds the full-period arc discrepancy by $\min(1,p^v/q)$ and the period by $q$. This applies to either sign and to $2u$. Dividing an observed active piece into complete periods and one remainder gives a count error at most $\ell_k p^v/q_k+q_k$ relative to length. Since $h_k=t(3k^2+3k+1)\le7tk^2$ for $k\ge1$, all active count errors sum to at most

$$
H=(7t p^v+p)K(K+1)/2 .
$$

Consequently the model counts differ on every arc from $Z\delta_0+(N-Z)\lambda$ by at most $H$. This comparison uses the same atom for every retired piece, which is what permits adding the type weights in a discrepancy calculation.

**True orbits.** At a time $n$ within block $k$, each real coordinate differs modulo one from its model by at most $B b^{-(n_{k+1}-n)}$. For the sum use $2B$. With $W=\lceil\log_b(2B(K+1))\rceil$ and $\epsilon=1/(K+1)$ the projected error is at most $\epsilon$ outside at most $E=(K+1)W$ times. Enlarge any arc at both ends by $\epsilon+\eta$ for $\eta>0$, capping at the whole circle. Both inclusions, from good observations into the enlarged model arc and from good model points into the enlarged observation arc, show that the two scalar discrepancies, for the true sample and for the reference law $(Z/N)\delta_0+(1-Z/N)\lambda$, differ by at most $(E+H)/N+2\epsilon$ after $\eta\downarrow0$. This comparison holds even when an endpoint meets an atom. The reference discrepancy is exactly $Z/N$ by arbitrarily short arcs about zero. Thus simultaneously for the three projections,

$$
|D_N(z)-\delta|\le
\frac{H+(K+1)W+t+17h_K}{N}+\frac{2}{K+1}.
$$

Here $N\asymp_t K^3$. For $N<t$ use $|D_N(z)-\delta|\le1$ and increase $C_{b,p}$. This proves the stated all-prefix rate. For weak convergence, model counts differ from the reference on every arc by $O(K^2/N)$ after normalization. Approximate each continuous test uniformly by step functions on a fixed finite arc partition. The small tails on good times and the vanishing proportion of bad times transfer convergence to the actual orbit.
