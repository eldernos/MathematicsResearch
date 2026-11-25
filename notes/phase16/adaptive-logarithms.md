# Adaptive dyadic logarithm identities: the 5/12 obstruction, its height threshold and its failure at linear height

**Theorem 1 (adaptive 5/12 obstruction; paper proof with an exact finite certificate).** At each cutoff $N\ge1$ choose any finite rational combination $S^{(N)}$ of the real sources $A_{k,\pm}$, the Gaussian sources $G_{t,\pm}$ (all four phases $(\pm1\pm i)/2^t$) or, more generally, the flat trace sources of Phase 15 Theorem A, with $S^{(N)}(\infty)=\log 2$. Let $q_N$ be the reduced denominator of $Y_N=2^NS^{(N)}(N)$, computed with the homogeneous cutoffs. Let $\theta_N\in\mathbb Q^4$ be the collapsed parameter vector of $S^{(N)}$ (§1) and $H_N$ its height. If $\log H_N=o(N)$, then

```math
\frac{\log q_N}{N}-\rho(\theta_N)\longrightarrow 0 ,
```

where $\rho(\theta)$ is the Phase 14 rate of the *fixed* formula with parameters $\theta$. Consequently

```math
\liminf_{N\to\infty}\frac{\log q_N}{N}\ \ge\ \frac{5}{12},
```

and the gap survives adaptivity: every limit point of $(\log q_N)/N$ lies in $\{5/12\}\cup[13/30,\infty)$. If $\theta_N\ne(0,0,0,-5)$ for all large $N$, the lower limit is at least $13/30$.

**Theorem 2 (linear heights below a certified threshold).** The same two conclusions, $\liminf\ge5/12$ and $\liminf\ge13/30$ away from the minimizer, hold under $\log H_N\le N/528$ and $\log H_N\le N/839$ respectively when $\theta_N\in\mathbb Z^4$. They hold under $\log H_N\le N/562$ and $N/862$ for rational $\theta_N$.

**Theorem 3 (sharpness).** For every $\varepsilon\in(1/12,\,19/60)$ there are integers $c_N$ with $\log|c_N|=(\varepsilon+o(1))N$ such that the formulas $\theta_N=(0,0,0,c_N)$ satisfy $\limsup(\log q_N)/N\le 1/2-\varepsilon<5/12$. With unrestricted height, integer vectors $\theta_N$ with $u=0$ achieve $\log q_N=O(N^{2/3})$, that is, rate zero, using $\log H_N\le(1+o(1))N$. The exact minimum adaptive rate with unrestricted height is therefore $0$. Among **integer** sequences on the one-parameter line $\theta=(0,0,0,c)$, the minimum adaptive rate is exactly $11/60$ (attained at unrestricted height). Over **rational** $c_N\in\mathbb Q$ on the same line, no positive floor survives: taking $c_N=(\operatorname{round}(2^N\log 2)-2^NB(N))/Y_c(N)$ makes $Y_N\in\mathbb Z$, giving $q_N=1$ (rate $0$) and shifted error at most $1/2$.

**Proposition 4 (the shifted error).** For every adaptive formula, $2^N\log2-Y_N=E_0(N)-\theta_N\cdot Y(N)$, where $Y(N)\in\mathbb Q^4$ is the vector of shifted prefixes of the four zero-limit directions and $E_0(N)=O(1)$. Each $N\,Y_i(N)$ converges to an explicit 60-periodic function of $N$ that never vanishes. For **integer** $c_N$ on the line $\theta=(0,0,0,c)$, this forces $|c_N|\le16N(|2^N\log2-Y_N|+O(1))$. Every integer line construction of Theorem 3 therefore has exponentially large shifted error, and any subexponential error on the integer $c$-line implies $\log H_N=o(N)$ and hence rate at least $5/12$. (By contrast, rational $c_N$ can achieve $q_N=1$ and error $\le 1/2$ as noted above, at height $e^{(2+o(1))N}$.) In two or more dimensions, finite exact plane instances at $N=120,240,480$ reduce the shifted error (below $2^{-6}$, and down to $2^{-15.2}$ at $N=480$) together with denominators smaller than those of the fixed minimizer at the same cutoff.

All logarithms are natural. The proofs are paper deductions resting on Phase 14 (Grechkoseeva, Bang) and Phase 15 Theorem A; the 730-node branch-and-bound certificate of §2 is also **kernel-verified** in [AdaptiveLogarithmBounds.lean](../../NormalityChecker/AdaptiveLogarithmBounds.lean), and the remaining finite parts are exact computations in [phase16_adaptive_log.py](../../scripts/phase16_adaptive_log.py). [Phase 14 classification](../phase14/gaussian-relations.md) · [Phase 15 Theorem A](../phase15/arithmetic-lifts.md) · [Lean statements of Phase 14](../../NormalityChecker/GaussianLogarithmRelations.lean)

## 0. Status of the results

| Result | Status | Evidence |
| --- | --- | --- |
| Collapse to $\theta_N\in\mathbb Q^4$ and $H_N\le 4H_{\rm touch}$ (§1) | Paper proof | Raw identity with 23 sources, strides up to 50 and coefficients $10^{30}$ checked on 160 cells |
| Uniform cell lemma $m_V(\theta)\ge5/12-1/V$ for all $\theta\in\mathbb Q^4$ (§2) | Exact certificate | Branch and bound over $(a,u,b,c)$, 40 branchings for $5/12$, 52 for $13/30$ |
| Theorem 1: $(\log q_N)/N=\rho(\theta_N)+o(1)$ under $\log H_N=o(N)$ (§3) | Paper proof | Frobenius support predictions match exact $q_N$ for each of 8 formulas at all 282 prime/cutoff pairs ($N=120,240,480$) |
| Theorem 2: thresholds $N/528$, $N/839$ (§4) | Paper proof with exact relaxed certificate | Relaxed branch and bound, bisection on $\varepsilon=1/k$ |
| Theorem 3: line constructions and rate $0$ (§5) | Paper proof (CRT); exact instances | $N=120,240,480$, zero support mismatches |
| Line floor $11/60$ (§5) | Paper proof | Constant cells found by computation to $v=399$, beyond by a prime in short intervals |
| Proposition 4: error identity and periodic limit, $\min|g_c|=1/15$ (§6) | Paper proof, exact limit | Limits compared with $N\,Y_i(N)$ at three cutoffs |
| Joint error/denominator reduction in dimension $\ge2$ (§6) | Exact instances, heuristic frontier | LLL with an error column |
| Critical exponent between $1/528$ and $1/12$ | Open; conjecturally $1/12$ | Lattice heuristic (§7) |

## 1. Reduction to four parameters and the height of the collapse

Write $B=2A_2+A_3-A_6$ and $f_a=A_1-B$, $f_u=G_1-B$, $f_b=G_2+A_2-A_4-B$, $f_c=G_3+2A_2-2A_4-B$. These four prefixes have value $0$ at infinity. Every fixed formula for $\log 2$ in the alphabet satisfies, **at every real cutoff**,

```math
S=B+a f_a+u f_u+b f_b+c f_c ,
```

for a unique $\theta=(a,u,b,c)\in\mathbb Q^4$ (Phase 14). The argument applies at each $N$ separately, so an adaptive sequence $S^{(N)}$ collapses to a sequence $\theta_N$. Then $Y_N=2^NS_{\theta_N}(N)$ depends only on $\theta_N$. The eight coefficients of $A_1,A_2,A_3,A_4,A_6,G_1,G_2,G_3$ are integer affine functions of $\theta$:

```math
a_6=a+u+b+c-1,\quad a_4=-b-2c,\quad a_3=-a_6,\quad a_2=-a_4-2a_6 .
```

Let $D_N$ be the least common denominator of $\theta_N$ and put $H_N=\max(D_N,D_N|a|,D_N|u|,D_N|b|,D_N|c|)$.

**(a) The clean hypothesis is on $H_N$.** All estimates below use only $H_N$.

**(b) The raw height and the strides.** The four coordinates of $\theta$ are the aggregated coefficients of $A_1,G_1,G_2,G_3$ after the sign identities $A_{k,-}=A_{2k}-A_k$ and $G_{t,-}=A_{4n}-A_{2n}-G_t$ ($n=2t-1$). Conjugate phases have the same real part. Neither identity moves weight onto $A_1$ or onto any $G_t$ from a different source, because $2k\ge2$, $2n\ge2$ and $G_{t,-}$ feeds only $G_t$. Hence

```math
a=c(A_{1,+})-c(A_{1,-}),\qquad u=\sum_{\text{4 phases},\,t=1}\pm c,\quad b=\sum_{t=2}\pm c,\quad c=\sum_{t=3}\pm c .
```

The valuation descent forces the aggregated coefficients of every other stride to vanish *exactly*. Huge coefficients on large strides can therefore cancel without ever reaching $\theta$. Only the fourteen *touching* signed-alphabet sources $A_{1,\pm}$ (2 sources) and $G_{t}$ with $t\le3$ in all four phases (12 sources) enter. If $H_{\rm touch}$ is the height of their aggregated coefficient vector in the signed alphabet, then

```math
H_N\ \le\ 4\,H_{\rm touch}\ \le\ 4\,H_{\rm raw},
```

with no dependence on the maximal stride $M_{\rm raw}$ or on the number of terms. For flat trace sources each irreducible source contributes a coefficient in $\{-1,0,1\}$ to each of $A_1,G_1,G_2,G_3$. This follows by inspecting the four cases of the Theorem A proof: $A_1$ arises only from $nd/2=1$, and each $G_{(m+1)/2}$ only from one divisor $d$ with coefficient $\pm\mu$. A reducible source is the sum over its irreducible factors, so flat traces use the separate degree-weighted bound

```math
H_N\ \le\ D_{\rm touch}\,\max\Bigl(1,\ \sum_{s\ \rm touching}\deg(f_s)\,|c_s|\Bigr).
```

Here a source touches the four coordinates only when its stride is $n\in\{1,2,3,5\}$. There are infinitely many flat sources of stride $1$, so the weighted $\ell^1$ norm, rather than the maximum, is the relevant raw height for flat traces. Either way $\log H_{\rm raw}=o(N)$ (for the signed alphabet), or $\log$ of the weighted touching norm $=o(N)$ (for flat traces), suffices, and arbitrarily large strides cannot inflate $H_N$. The script builds a raw identity for $\theta=(3/7,-1/2,-2,5)$ padded with zero relations of coefficient $10^{30}$ at strides up to 50. It checks the identity on 160 cells and recovers $H_N=70$ from $H_{\rm raw}\approx10^{31.6}$.

## 2. The uniform finite-cell lemma

On the half-open cell $[v/2,(v+1)/2)$ the prefix $S_\theta$ is an affine form $\ell_v(\theta)=r_v\cdot(1,\theta)$ with fixed rational $r_v\in\mathbb Q^5$. Put $m_v=2/(v(v+1))$ and

```math
m_V(\theta)=\sum_{1\le v<2V,\ \ell_v(\theta)\ne0} m_v .
```

**Lemma.** For every integer $V\ge36$ and **every** $\theta\in\mathbb Q^4$, with no dependence on height,

```math
m_V(\theta)\ \ge\ \frac{5}{12}-\frac1V ,
```

with equality only at $\theta_{\min}=(0,0,0,-5)$. Every $\theta\ne\theta_{\min}$ has $m_V(\theta)\ge 13/30-1/V$.

*Proof.* Run the Phase 14 branch and bound on cells $v=1,\dots,71$ ($x<36$) in all four variables. A zero row costs nothing, a nonzero constant row costs $m_v$, and a nonconstant row splits into a zero branch, which adjoins the pivot, and a nonzero branch, which pays $m_v$ and forgets its inequation. Along the truthful path of any $\theta$ the amount spent equals its exact mass on the cells processed. A branch is discarded once it has spent $13/30$. The first cell has row $(0;0,1,0,0)$, that is $S(1/2)=u$, so $u\ne0$ is pruned at once with mass $1$. Exactly two leaves survive, both points:

| Leaf | Mass on $v\le71$ | Full rate |
| --- | ---: | ---: |
| $(0,0,0,-5)$ | $7/18$ | $5/12$ |
| $(0,0,0,-2)$ | $73/180$ | $13/30$ |

Both leaves are positive on every cell $v\ge8$: exactly on $8\le v<18$, and beyond by the Phase 15 tail bound $|S(x)-\log2|\le4C2^{-x}$ with $C=34$ and $16$. Their masses on $v<2V$ are therefore $7/18+\sum_{72\le v<2V}m_v=5/12-1/V$ and $13/30-1/V$. Every pruned $\theta$ already has $m_V(\theta)\ge13/30>5/12-1/V$. $\square$

The inequality really is uniform. It concerns only *which* cells vanish exactly, and that pattern is decided by the finite tree. The script verifies the two closed forms exactly for $36\le V\le400$.

**Tree statistics (for formalization).**

| Pruning bound | Nodes | Branchings | Pruned | Leaves | Constant rows | Zero rows | Depth | Pivot entries |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $5/12$ (suffices for the lemma's first claim) | 484 | 40 | 39 | 2 | 377 | 26 | 18 | ≤ 15 bits |
| $13/30$ (also gives the runner-up) | 730 | 52 | 51 | 2 | 591 | 34 | 24 | ≤ 21 bits |

The input data are the 71 rows $r_v$, 355 rationals with entries of at most 134 bits and a common denominator of 134 bits. Each row is a finite sum of at most 71 explicit dyadic-harmonic terms. The 730-node branch-and-bound tree (for the stronger $13/30$ threshold) is kernel-verified in [NormalityChecker/AdaptiveLogarithmBounds.lean](../../NormalityChecker/AdaptiveLogarithmBounds.lean) (`global_cell_mass_bound`, `minimizer_mass71`, `runnerup_mass71`), using pure-integer row certificates checked by `decide` with only the standard Lean axioms.

## 3. Proof of Theorem 1

Fix $V\ge36$ and let $N>2V^2$. For $1\le v<2V$ let $P_v$ be the odd primes with $2N/(v+1)<p\le2N/v$. Then $p>N/V>2V$, so $p^2>2N$, and $p$ does not divide any denominator of the fixed rows $r_v$. Those denominators divide $2^{O(V)}\,\mathrm{lcm}(1,\dots,2V)$. If moreover $p\nmid D_N$, the Phase 14 Frobenius congruence applies coefficientwise to the eight sources, whose largest Taylor index is $2N$ (from $G_1$):

```math
p\,Y_N\equiv 2^N S_{\theta_N}(N/p)=2^N\ell_v(\theta_N)\pmod p .
```

Hence, for every prime $p\in P_v$ with $p\nmid D_N$, we have $p\mid q_N$ if and only if $p$ does not divide the integer $\Pi_{N,v}=\mathrm{den}(r_v)\,D_N\,\ell_v(\theta_N)$. If $\ell_v(\theta_N)\ne0$, then $0<|\Pi_{N,v}|\le K_v H_N$ with $K_v=\mathrm{den}(r_v)\,\|r_v\|_1=e^{O(v)}$. So in an active cell at most $\log H_N+\log K_v$ of log-weight is lost to the numerator. Over all cells at most $\log D_N\le\log H_N$ is lost to primes $p\mid D_N$. By the prime number theorem $\sum_{p\in P_v}\log p=m_vN+o_V(N)$. Therefore

```math
\frac{\log q_N}{N}\ \ge\ m_V(\theta_N)-\frac{(2V+1)\log H_N+O(V^2)}{N}-o_V(1).
```

For the upper bound, a prime $p>\sqrt{2N}$ with $p\nmid D_N$ in an inactive band does not divide $q_N$. Primes up to $\sqrt{2N}$ contribute $O(\sqrt N\log N)$, the dyadic part $O(\log N)$, primes dividing $D_N$ at most $2\log D_N$, and all bands $v\ge2V$ together at most $\vartheta(N/V)=N/V+o(N)$. Since $0\le\rho(\theta)-m_V(\theta)\le\sum_{v\ge2V}m_v=1/V$,

```math
\Bigl|\frac{\log q_N}{N}-\rho(\theta_N)\Bigr|\ \le\ \frac2V+O\Bigl(\frac{V\log H_N+V^2}{N}\Bigr)+o_V(1).
```

Let $N\to\infty$ and then $V\to\infty$. The constants follow from the Lemma: $\rho(\theta)\ge m_V(\theta)\ge5/12-1/V$, and $\rho(\theta)\ge13/30$ for $\theta\ne\theta_{\min}$. $\square$

*Quantitative form.* With $\varepsilon_N=\log H_N/N$ and an effective prime number theorem, the choice $V\asymp\varepsilon_N^{-1/2}$ gives $(\log q_N)/N\ge5/12-O(\sqrt{\varepsilon_N})-o(1)$. Theorem 2 shows that this loss does not actually occur once $\varepsilon_N\le1/528$.

*The second least value.* Under $\log H_N=o(N)$ the rate of an adaptive sequence approaches $\rho(\theta_N)$. A run of indices with $\theta_N\ne\theta_{\min}$ has rates at least $13/30-o(1)$. Thus adaptivity at subexponential height cannot produce any limit point strictly between $5/12$ and $13/30$.

## 4. Proof of Theorem 2 (explicit linear threshold)

Let $\log H_N\le\varepsilon N$. In the proof above an active cell loses at most $\log H_N+O(1)\le\varepsilon N+O(1)$. This is sharpened in two ways.

1. *Classes.* Fix the affine space $F$ cut out by the cells on which $\theta_N$ vanishes. If two active cells have proportional forms on $F$, then $\ell_v=\lambda\ell_w$ there, and all cancelled primes of both bands divide the single numerator of $\ell_w(\theta_N)$. A class of mutually proportional forms therefore loses at most $\varepsilon N+O(1)$ in total. A form that is constant on $F$ loses only $O(1)$, since its value is a fixed rational.
2. *Points.* If $F$ is a single point, then $\theta_N$ is a fixed vector and its rate is the exact fixed rate.

The relaxed branch and bound charges $(m_v-\varepsilon)^+$ to a nonzero branch for pruning, which underestimates the class charge because $\sum(m_i-\varepsilon)^+\le(\sum m_i-\varepsilon)^+$. At a leaf it regroups the active cells into classes on $F$ and charges $(\text{class mass}-\varepsilon)^+$. At a point it substitutes the exact rate. Cells with $m_v\le\varepsilon$ and the tail are dropped, which only lowers the bound. Branches whose recorded nonzero cells vanish identically on $F$ are empty and are discarded. For rational $\theta_N$ a further global $\varepsilon$ is subtracted for primes of $D_N$. Bisection over $\varepsilon=1/k$ gives:

| Conclusion | Integer $\theta_N$ | Rational $\theta_N$ |
| --- | --- | --- |
| $\liminf(\log q_N)/N\ge5/12$ | $\varepsilon=1/528$ certified, $1/527$ fails | $1/562$, $1/561$ fails |
| $\liminf\ge13/30$ when $\theta_N\ne\theta_{\min}$ | $1/839$ | $1/862$ |

The trees are tiny (about 100 to 150 nodes). The binding leaf is the line $\theta=(0,0,0,c)$, where many small classes each lose $\varepsilon$. The relaxation fails at about $1/527$ only because it charges every class separately. It does not exhibit a formula.

## 5. Sharpness: adaptive formulas below 5/12 at linear height

**The $c$-line.** On $\theta=(0,0,0,c)$ the cells take the following values:

| Cells $v$ | 1–3 | 4 | 5 | 6, 7 | 8–11 | 12–14 | 15 | … |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $\ell_v$ | $0$ | $1/2$ | $(c+2)/4$ | $(c+5)/8$ | $11/16$ | $(c+265/3)/128$ | $(c+265/2)/192$ | roots $\approx -2^{v/2}$ |

The cells constant along the line are exactly $1,2,3$ (zero) and $4,8,9,10,11$ (positive). They are found by computation for $v\le399$. For $v\ge150$ the $G_3$ coefficient of $\ell_v$ has a pole at a prime $p\in(v/6,v/5]$ (Nagura's prime in $(x,6x/5]$ for $x\ge25$), and no other source in $f_c$ reaches index $p$. So every such cell is nonconstant. Because every prime $p\in P_4\cup P_8\cup P_9\cup P_{10}\cup P_{11}$ has $p\nmid D_N=1$ for **integer** $c_N\in\mathbb Z$ and $p\nmid\operatorname{num}(\ell_v)$ once $N$ is large, **every integer sequence** $c_N\in\mathbb Z$, of arbitrary height, has $\liminf(\log q_N)/N\ge1/10+1/12=11/60$ on this line. (Over rational $c_N\in\mathbb Q$, primes in the constant cells can divide $D_N$: as noted in Theorem 3, choosing $c_N=(\operatorname{round}(2^N\log 2)-2^NB(N))/Y_c(N)$ yields $Y_N\in\mathbb Z$, $q_N=1$, and shifted error $\le1/2$.)

*Construction.* Choose bands to cancel: the class $\{6,7\}$ (mass $1/12$), then $5$ ($1/15$), then the classes from $v\ge12$ (total $1/6$), taking a subset of primes in the last band to reach total mass $\varepsilon$. By the CRT pick the unique integer $c_N\in[M,2M)$, where $M=\prod p$, with $c_N\equiv-5\pmod p$ on bands 6 and 7, $c_N\equiv-2$ on band 5, and $c_N\equiv$ root of $\ell_v$ on the others. The $c$-coefficient of each of these cells is a nonzero rational, so it is a unit at all large $p$. Then $M\le c_N<2M$, so $\log|c_N|=(\varepsilon+o(1))N$. The cancelled primes do not divide $q_N$, and the bands of cells 1–3 are absent. The remaining primes give $\log q_N\le(1/2-\varepsilon+o(1))N$, because $1/2$ is the total mass on the line apart from cells 1–3. Accidental further cancellations only lower $q_N$. This proves the first claim of Theorem 3. At unrestricted height, letting $V(N)\to\infty$ cancels all nonconstant bands up to $V(N)$ and attains the integer line floor $11/60$ (with $\varepsilon=19/60$).

**Rate zero.** On $u=0$ the cells $v\ge2$ are never constant. This is checked by computation for $v\le399$. For $v\ge100$ the $G_2$ term of $f_b$ has a pole at a prime in $(v/4,v/3]$ and no other source of $f_b$ reaches it. Set $u=0$, which kills band 1 for free. Cancel every band $2\le v\le N^{1/3}$ by the CRT, solving each prime's congruence in a coordinate with a unit coefficient. The bad primes of band $v$ divide a fixed numerator of size $e^{O(v)}$, costing $O(N^{2/3})$ in total. The bands $v>N^{1/3}$ contain only primes up to $2N^{2/3}$. Thus $\log q_N=O(N^{2/3})$ with $\log H_N\le\vartheta(N)+O(1)=(1+o(1))N$. Rank does not limit the attainable rate. Any family whose cells are nonconstant reaches rate $0$. **The exact unrestricted minimum is $0$**, and in Phase 14's stronger sense the minimum on a fixed one-parameter line is its floor of constant cells.

**What rank buys: height.** One integer congruence per prime defines a coset of index $M=\prod p$ in a $k$-dimensional family. CRT gives height $M$ rigorously. Lattice reduction finds coset points of height about $M^{1/k}$, which is the generic covering radius. The script uses LLL with Babai's nearest plane. Measured exponents: $\log H/\log M=0.36,\,0.39,\,0.37$ for $k=3$ at $N=120,240,480$.

**Exact instances.** In the table, $\log M/N$ is the cancelled modulus, cong$/N$ the log-weight of primes in nonzero cells whose residue vanishes, and zero$/N$ the weight of primes in exactly vanishing cells. “mism” counts primes $p>\sqrt{2N}$ where the Frobenius prediction disagrees with the exact $q_N$; it is $0$ throughout. The finite-$N$ values fluctuate around the limits by the prime number theorem in short bands. Even the fixed minimizer shows $0.39$, $0.36$ and $0.41$ below $5/12$. The meaningful comparisons are therefore with the minimizer at the same $N$ and with the cancelled weights.

| $N$ | Formula | $\log q_N/N$ | $\log H_N/N$ | $\log M/N$ | $\log_2$ error | Limit rate |
| ---: | --- | ---: | ---: | ---: | ---: | --- |
| 120 | fixed $(0,0,0,-5)$ | 0.3919 | 0.0134 | – | −5.4 | 5/12 |
| 120 | $c$-line, cancel 5,6,7 | 0.2975 | 0.1409 | 0.1531 | +15.5 | ≤ 7/20 |
| 120 | plane $u=a=0$, cancel 3,5,6,7, small error | 0.2418 | 0.3121 | 0.3301 | −6.7 | ≤ 7/20 |
| 240 | fixed $(0,0,0,-5)$ | 0.3578 | 0.0067 | – | −6.3 | 5/12 |
| 240 | $c$-line, cancel 5,6,7 | 0.3339 | 0.1185 | 0.1256 | +31.2 | ≤ 7/20 |
| 240 | plane, cancel 3,5,6,7, small error | 0.3410 | 0.2459 | 0.2700 | −8.3 | ≤ 7/20 |
| 480 | fixed $(0,0,0,-5)$ | 0.4066 | 0.0034 | – | −7.3 | 5/12 |
| 480 | fixed $(0,0,0,-2)$ | 0.4172 | 0.0014 | – | −7.8 | 13/30 |
| 480 | $c$-line, cancel 5,6,7 | 0.3504 | 0.1293 | 0.1368 | +78.7 | ≤ 7/20 |
| 480 | $c$-line, cancel all $v\ge5$ | 0.2452 | 0.2341 | 0.2361 | +151.3 | 11/60 |
| 480 | $u=0$, cancel all $v\ge2$ (LLL) | 0.0706 | 0.3322 | 0.9028 | +220.8 | 0 |
| 480 | plane, cancel 3,5,6,7, small error | 0.3341 | 0.2887 | 0.3011 | −8.1 | ≤ 7/20 |
| 480 | plane, cancel 3–7, small error | 0.2482 | 0.3933 | 0.4019 | −15.2 | ≤ 1/4 |
| 480 | $u=0$, cancel all $v\ge2$, small error | 0.0870 | 0.4463 | 0.9028 | −4.6 | 0 |

In the line rows $\log H_N\approx\log M$, as the CRT predicts. In the $u=0$ row LLL chooses $a=0$, so band 2 vanishes exactly rather than by congruence. The residual $0.07$ at $N=480$ is the contribution of primes below $\sqrt{2N}$ and their powers.

## 6. The shifted approximation error

Since $f_a,f_u,f_b,f_c$ vanish at infinity, $Y_i(N)=2^Nf_i(N)$ is rational and

```math
2^N\log2-Y_N=E_0(N)-\theta_N\cdot Y(N),\qquad E_0(N)=2^N\bigl(\log2-B(N)\bigr)=O(1).
```

**Periodic limit.** For $A_k$ the shifted tail times $N$ tends to $k\,2^{N\bmod k}/(2^k-1)$. For $G_t$ with $n=2t-1$ and $J=\lfloor2N/n\rfloor$ it tends to

```math
n\sum_{j>J}w_j\,2^{\,N-\lceil nj/2\rceil},
```

which is summed exactly over one period of eight. The error is $O(1/N)$ because $N/(J+m)$ differs from its limit by $O(m/N)$ against a geometric weight. Thus $N\,Y_i(N)=g_i(N\bmod60)+O(1/N)$ with explicit rational $g_i$. The script checks the period and finds

```math
\min_r|g_a(r)|=\min_r|g_u(r)|=\min_r|g_b(r)|=\tfrac13,\qquad \min_r|g_c(r)|=\tfrac1{15}.
```

The measured $N\,Y_c(N)$ is $0.252$, $0.259$, $0.263$ at $N=120,240,480$, within $0.04/0.02/0.01$ of the limit.

**On the integer $c$-line the error forbids height.** For $c_N\in\mathbb Z$ on $\theta=(0,0,0,c_N)$, we have $2^N\log2-Y_N=E_0(N)-c_N\,Y_c(N)$ and $|Y_c(N)|\ge1/(16N)$ for large $N$. If the shifted error is $e^{o(N)}$ then $\log|c_N|=o(N)$, and Theorem 1 gives rate at least $5/12$. If the error is at most $e^{N/528}$, Theorem 2 gives the same. Every integer line construction of §5 has error about $|c_N|/N$. This is visible as $\log_2|\text{error}|=+78.7$ and $+151.3$ at $N=480$. (For rational $c_N\in\mathbb Q$, height comes from the denominator $D_N$ as well as the numerator, so $|c_N|$ can stay bounded while $D_N\approx e^{2N}$, as in $c_N=(\operatorname{round}(2^N\log 2)-2^NB(N))/Y_c(N)$.)

**Small combinations of tails do exist.** The vector $Y(N)$ is a rational linear form with denominators near $e^{2N}$. Dirichlet's theorem gives integer $\theta$ of height $H$ with $|\theta\cdot Y(N)|\lesssim H^{-3}/N$. Examples: height $3678$ gives $9.4\times10^{-15}$ at $N=120$, and height $1.2\times10^{17}$ gives $9.4\times10^{-56}$ at $N=480$. No fixed nonzero $\theta$ satisfies $\theta\cdot Y(N)=0$ for all $N$. That would make a zero-limit prefix vanish at every integer cutoff, hence on every cell (Phase 14), contradicting independence. An error constraint therefore removes exactly one dimension from the lattice count: a coset of index $M$ in a $k$-dimensional family meets the slab $|\text{error}|\le\delta$ inside a box of height $H$ about $H^{k-1}\delta N/M$ times. The error-constrained plane rows of §5 realize this with $\log H\approx\log M$ ($k=2$). They are below the fixed minimizer at every tested $N$, with errors $2^{-6.7}$ to $2^{-15.2}$.

**Answer to the error question.** With bounded or subexponential shifted error, the integer one-parameter mechanism behind Theorem 3 is excluded rigorously, whereas rational $c_N$ escape via $D_N\approx e^{2N}$. In dimension at least two, the finite plane instances at $N=120,240,480$ give concrete evidence that integer vectors can reduce both error and denominator simultaneously; an asymptotic lower bound on the error for general $\theta_N\in\mathbb Z^4$ is not available, since the error is a single real linear form.

## 7. The critical exponent: what is proved and what is expected

Let $\varepsilon^*$ be the infimum of $\varepsilon$ for which some adaptive sequence with $\log H_N\le\varepsilon N$ has $\liminf(\log q_N)/N<5/12$. Theorems 2 and 3 give

```math
\frac1{528}\ \le\ \varepsilon^*_{\mathbb Z}\ \le\ \frac1{12}.
```

The upper bound is rigorous (CRT on the line). The lower bound is rigorous because the per-class loss is at most $\log H_N$. The gap comes from the possibility that several classes are cancelled simultaneously by one integer $c$ of height $H$ with $\prod Q_i\gg H$. That would require coincidences such as $Q_{67}m-Q_5m'=3$ with small $m,m'$, where $Q_{67}$ and $Q_5$ are products of primes from two disjoint bands. Choosing subsets of primes multiplies the number of trials by only $e^{O(N/\log N)}$. A counting heuristic therefore predicts no such coincidence, and that a $k$-dimensional family cancels at most $k\log H$ in total. Under that heuristic, beating $5/12$ in a family of dimension $k$ with generic active mass $M_F$ requires $\varepsilon>(M_F-5/12)/k$.

The script (option `--frontier`) enumerates every affine family cut out by zero cells $v\le71$: 71 hyperplanes, 2449 planes and 54356 lines. For each it computes the generic active mass from cells $v\le120$ plus the tail. The minima are attained by the expected families:

| Dimension $k$ | Best family | Generic mass $M_F$ | Needed $\varepsilon$, no error constraint: $(M_F-5/12)/k$ | Needed $\varepsilon$, error $e^{o(N)}$: $(M_F-5/12)/(k-1)$ |
| ---: | --- | ---: | ---: | ---: |
| 1 | $c$-line $a=u=b=0$ | $1/2$ | $1/12$ | impossible (§6) |
| 2 | plane $u=a=0$ | $2/3$ | $1/8$ | $1/4$ |
| 3 | $u=0$ | $1$ | $7/36$ | $7/24$ |
| 4 | $\mathbb Q^4$ | $2$ | $19/48$ | $19/36$ |

Under the heuristic the frontier without an error constraint is: rate $5/12$ for $\varepsilon\le1/12$, then $1/2-\varepsilon$ on the line up to $\varepsilon=1/6$, then $2/3-2\varepsilon$ on the plane, reaching $0$ at $\varepsilon=1/3$. This matches the measured rate-zero heights $\log H/N\approx0.29$–$0.34$. With the error constrained, the frontier starts at $1/4$, and rate zero needs about $\varepsilon=1/2$ (measured $0.38$–$0.45$ at these finite $N$).

**Conjecture.** $\varepsilon^*_{\mathbb Z}=1/12$ without an error constraint, and $\varepsilon^*=1/4$ when the shifted error is required to be $e^{o(N)}$. A proof would need to exclude the coincidences above uniformly in $N$. That is an $S$-unit-type problem with moving prime sets, and nothing in Phases 14–15 addresses it.

## 8. Scope

* Theorems 1–2 cover every adaptive choice in the real+Gaussian alphabet and in the flat trace alphabet. Within that alphabet the fixed-formula theory transfers to adaptive formulas exactly as long as heights are subexponential, and robustly up to $N/528$.
* The adaptive formulas of Theorem 3 lie in the same alphabet and use the same homogeneous cutoffs. They show that the hypothesis on $H_N$ cannot be removed. They do not approximate $2^N\log2$ well: the line formulas have exponentially large error, and only the higher-dimensional examples keep the error bounded.
* Non-flat sources (for example $1+\sqrt{-7}$) and position-dependent corrections remain outside, as in Phases 14–15. Unrestricted rational approximants reach rate $0$ trivially by rounding (Phase 14). The point of Theorem 3 is that rate $0$ is reachable inside the alphabet as well, at height $e^{N+o(N)}$, or about $e^{N/3}$ after lattice reduction.
* A denominator rate says nothing about normality; see the residual limits recorded in Phase 15.

## 9. Reproduction

```sh
python -B scripts/phase16_adaptive_log.py           # about 5 seconds
python -B scripts/phase16_adaptive_log.py --quick   # omits N = 480
python -B scripts/phase16_adaptive_log.py --frontier  # adds the §7 enumeration, about 9 minutes
```

The program is dependency-free. Rows, trees, thresholds, prefixes, denominators and support predictions are exact. The shifted error compares the exact rational $Y_N$ with a dyadic enclosure of $2^N\log2$ of radius below $2^{-3N-390}$. Logarithms in the tables are rounded summaries of exact integers. The run ends with `All Phase 16 adaptive-logarithm checks passed.`
