# Review of the Phase 19 nonlinear note: normality of quadratic images through null shell levels

Status: **complete** (2026-11-25).

This is an independent adversarial review of the Phase 19 nonlinear note. Its main claim is that every rational quadratic polynomial in $C(b,p,s,d)$ with $d\ge3$ and $s\ge1$ is normal to base $b$. This includes the flagship square $C(2,3,1,3)^2$, which Phase 18 left open with $\limsup_N D_N<2.94\cdot10^{-10}$. I re-derived every estimate by hand. I also attacked these points specifically:
- degenerate rows and degenerate points;
- localization near the ends of the shell;
- second moments at shrinking radii;
- the passage from $p$-adic levels to real orbits;
- the results on denser schedules.

The numerical checks were written without importing or copying the author's code. The earlier proofs are [Phase 18 algebra](../../phase18/algebra.md) and the [all-prefix criterion](../../phase18/principal.md#a-fixed-support-criterion-for-all-prefixes).

**Verdict.** Every estimate closes. I record the square theorem, the quadratic-form theorem, the universal-schedule theorem and the separated-growth theorem as **proved** (paper proofs). The external inputs are listed in the last section. No stated claim was found false. The objections below are presentation points, together with one scope remark (O5).

## Material reviewed

The draft is commit `85a0983` on the author's branch `t3/phase19-nonlinear-zero-set`, recorded with identical blobs as `ff756bd` on `research/phase-19-operations`. The draft was already written and committed, so I did not need to ask the author for it.

| File | Blob SHA-1 |
|---|---|
| `notes/phase19/nonlinear.md` | `8a6b674ed43ca80377adae47363faf1eb9be8eca` |
| `scripts/phase19_nonlinear.py` | `9432c1156fdc7cc8f7ce517aabab1ae68bed9962` |

`python -B scripts/phase19_nonlinear.py` passes in the author's checkout. The independent checks are in [nonlinear-check.py](nonlinear-check.py). Run them with `python -B notes/phase19/reviews/nonlinear-check.py`, which takes about 5 seconds.

## Verdict by claim

| Claim | Status |
|---|---|
| S1. Freezing: $p^{2sJ}b^{-n}R_n\equiv M(u)\pmod{p^L}$ uniformly in $u$ for late $J$ | Closed; checked against direct convolution |
| S2. Primitive jump $2p^{sH}$ at $x=c/p^H$, $p\nmid c$, and the grid family at distance $\ge p^{-H}$ | Closed |
| S3. Collision estimate (1) and a positive proportion of isolated primitive centers | Closed (O1, O3); main term matches numerically to 1% |
| S4. Almost every $x$ lies in infinitely many $G_H$ (second moment) | Closed (O2) |
| S5. Every level set $\{M=w\}$, $w\in\mathbb Z_p$, is null | Closed |
| S6. Transfer to real orbits and normality of every rational quadratic in $C(b,p,s,d)$ | Closed |
| Q. Quadratic forms in several orders $X_a=C(b,p,a,d)$ and joint uniformity of monomials | Closed (O4) |
| U. Universal polynomial normality under rapid variation, including $n_i=ti\lceil e^{(\log(i+1))^2}\rceil$ | Closed |
| G. Algebraically independent generators with separated pole growth, normal and Liouville | Closed |
| D. Dyadic interval criterion (sufficient condition only) | Closed as stated; it fails in degree 2 |
| Scope paragraph | Correct; one clarifying clause suggested (O5) |

## 1. The square theorem

Fix $b$, an odd prime $p\nmid b$, $t=\operatorname{ord}_p(b)$, $d\ge3$, $s\ge1$, and $a_0=v_p(b^t-1)$.

### S1. The frozen mass and its finite reductions

On shell $J$ write $n=tp^{dJ}u$ with $1\le u<p^d$. An index $i$ in the ordered square satisfies $i<p^{J+1}$, so $i=p^{J-h}a$ with $0\le h\le J$ and $p\nmid a$. Then
- $p^{sJ}w(i)=p^{sh}$;
- $z=i/p^J=a/p^h<p$;
- $(i,j)$ is retained precisely when $z^d+y^d\le u$.

These are exactly the pairs in $M(u)$ with both losses at most $J$. Pairs of total loss $h+k\ge L/s$ vanish modulo $p^L$. For the others, lifting the exponent gives $v_p(b^{ti^d}-1)=a_0+d(J-h)$, which is at least $L$ once $J\ge\lfloor(L-1)/s\rfloor+\max\big(0,\lceil (L-a_0)/d\rceil\big)$, uniformly in $u$. This is the Phase 18 threshold. For fixed $L$ only finitely many pairs matter, so $M\bmod p^L$ is a right-continuous step function. Hence $E_L=\{M\equiv0\bmod p^L\}$ is a finite union of intervals, and $\bigcap_LE_L=\{M=0\}$.

*Check.* At every breakpoint and just below it, in shells $J=4,5$ of the flagship, the normalized prefix computed from the original indices agrees with $M(u)$ modulo $3^3$ and $3^4$. There are 230,784 cutoffs in all.

### S2. The primitive jump

Modulo $p^{sH+1}$ only pairs of total loss at most $H$ jump.
- A pair $(1,y)$ or $(y,1)$ with $y$ of loss $v$ jumps at $x=y\in p^{-v}\mathbb Z$, with weight $p^{sv}$. This includes $(1,1)$ at $x=1$.
- At $x_0=c/p^H$ with $p\nmid c$ and $H\ge1$, the two pairs $(1,x_0)$ and $(x_0,1)$ are distinct and give $2p^{sH}$. This is nonzero modulo $p^{sH+1}$ because $p$ is odd.
- Every other point of $\bigcup_{v\le H}p^{-v}\mathbb Z$ is at distance at least $p^{-H}$ from $x_0$, which exceeds $\delta_H=\epsilon/(Hp^H)$.

Hence, if no competitor of total loss at most $H$ lies within $\delta_H$, then $M\bmod p^{sH+1}$ is constant on $(x_0-\delta_H,x_0)$ and on $[x_0,x_0+\delta_H)$, and the two constants differ by $2p^{sH}$. A competitor exactly at $x_0$ is at distance $0$, so it is excluded by isolation.

### S3. The collision estimate

I re-derived each ingredient. All of them hold as stated.

**Small rows.** Rows with $v<2H/5$ have $k\le v$, so $v+k<4H/5$. At most $H^2$ loss pairs carry at most $p^{v+k+2}$ points each, so these rows hold $O(H^2p^{4H/5})$ points.

**Rows with $B$ near zero.** For $y>0$ one has $|y^d-1|\ge|y-1|$, so $|B|\le\eta$ forces $0<|a-p^k|\le\eta p^k$. That gives at most $2\eta p^k$ numerators, and none when $\eta p^k<1$. Each such row has $O(p^v)$ points, for a total of $O(\eta Hp^H)=O(H^{-5}p^H)$.

**Points removed inside a row.** The conditions $z\le\eta$ and $|(d-2)B-(d+1)z^d|\le\eta^d$ remove $z$-intervals of length $O(\eta)$, by $w^d-z^d\ge(w-z)^d$. This costs $O(\eta p^v+1)$ per row. Summed over the $O(p^{k})$ rows of each loss pair, the cost is $O(\eta Hp^H+H^2p^{H/2})$.

**The third derivative.** Write $x=f_y(z)=(z^d+B)^{1/d}$. I recomputed:
- $f'=z^{d-1}x^{1-d}>0$;
- $f''=(d-1)Bz^{d-2}x^{1-2d}$;
- $f'''=(d-1)Bz^{d-3}x^{1-3d}\big((d-2)B-(d+1)z^d\big)$.

For $B<0$ and $d\ge3$ the last factor has modulus at least $(d-2)|B|$. For $d=3$ and $B>0$ it vanishes only at $z=(B/4)^{1/3}$, which is removed. On the retained set,

$$
c_K\,\eta^{2d-2}\le|f'''|\le C_{K,p,d},
$$

since $x$ ranges over a compact subset of $(0,(p^d-1)^{1/d})$.

The derivative $f''''$ equals $(d-1)Bx^{1-4d}z^{d-4}$ times a polynomial in $z$ of degree bounded in terms of $d$. Hence there are $O_d(1)$ monotonicity intervals, and $O(\log H)$ dyadic pieces in each row.

**The exponential sum (2).** On a piece, $g=lp^Hf_y(m/T)$ satisfies $\lambda\le|g'''|\le2\lambda$ with $\lambda=lp^HD/T^3$. Weyl differencing with $Q=\lambda^{-1/3}$ and the second-derivative test give

$$
|S|^2\ll \frac{N^2}{Q}+N^2(Q\lambda)^{1/2}+\frac{N}{(Q\lambda)^{1/2}},
$$

so $|S|\ll N\lambda^{1/6}+N^{1/2}\lambda^{-1/6}$ for $N\le pT$. This is Graham–Kolesnik Theorem 2.6. If the piece is shorter than $Q$, the trivial bound $N<\lambda^{-1/3}$ is at most $T^{1/2}\lambda^{-1/6}$ exactly when $\lambda\ge T^{-3}$. That holds because $p^HD\ge1$ for large $H$ (O3).

With $2H/5\le v\le H$ and $l\le H^4$:
- $\lambda^{1/6}\le H^{O(1)}p^{(H-3v)/6}\le H^{O(1)}p^{-H/30}$;
- $T^{-1/2}\lambda^{-1/6}=(lD)^{-1/6}p^{-H/6}$, independently of $v$.

**Erdős–Turán.** With cutoff $H^4$ the error per piece is $N/H^4+\sum_{l\le H^4}|S_l|/l$. Over the $O(\log H)$ pieces of a row this is $O(TH^{-3})$. The rows of loss pair $(v,k)$ have $O(p^{k+v})$ points in total, so the sum over rows is $O(H^{-2}p^H)$.

**The main term.** For loss pair $(v,k)$, the slab $1+x_1^d<z^d+y^d\le1+x_2^d$ has area $O(|I^+|)$, and its lattice count has error $O(p^v+p^k)$ by column-wise monotone Riemann sums. Two sums control the totals:
- $\sum_{k\le v,\,v+k\le H}p^{v+k}\sim\frac{H}{2}\frac{p}{p-1}p^H$;
- $\sum_{k\le v,\,v+k\le H}p^v=O(p^H)$.

Hence the main term is $(2\epsilon/H)\cdot O(|I|Hp^H)=O(\epsilon|I|p^H)$. The lattice error contributes $O(\epsilon p^H/H)$.

**Isolated centers.** Each competitor spoils at most one center, since $\delta_H<p^{-H}/2$. Write $C=C_{p,d,K}$ for the constant in (1). With $\epsilon<(1-1/p)/(2C)$, at least $\big((1-1/p)-C\epsilon\big)|I|p^H-o(p^H)$ primitive centers in $I$ are isolated.

*Checks.* For $(p,d)=(3,3)$ and $x\in[1/2,5/2]$, I counted ordered competitor endpoints within $\epsilon/(H3^H)$ of $3^{-H}\mathbb Z$. The table compares $B_H/(\epsilon\cdot\#\text{centers})$ with the equidistribution prediction $(2\epsilon/H)\cdot\#\text{competitors}$, normalized the same way.

| $H$ | predicted | measured, $\epsilon=1/8$ | measured, $\epsilon=1/32$ |
|---|---|---|---|
| 8 | 4.638 | 4.594 | 4.382 |
| 9 | 4.656 | 4.617 | 4.605 |
| 10 | 4.670 | 4.635 | 4.699 |

The main term of (1) is therefore realized almost exactly.

I also tested isolation exactly, against every jump of $M\bmod p^{sH+1}$ from every pair, with radius $1/(8Hp^H)$. The isolated fraction is
- $0.83$–$0.86$ for $(p,s,d)=(3,1,3)$ at $H\le9$ and for $(3,2,3)$ at $H\le6$;
- $0.80$ for $(5,1,3)$ at $H=5$;
- $0.835$ for $(3,1,4)$ at $H=6$.

At every isolated center the jump was exactly $2p^{sH}$ modulo $p^{sH+1}$.

### S4. Second moments at shrinking radii

The lower bound $|I\cap G_H|\ge c\epsilon|I|/H$ uses disjoint good intervals around isolated centers in the middle half of $I$. For $n<m$, enlarge both sets to the full grids. Each coarse interval meets at most $2(\delta_n+\delta_m)p^m+1$ fine centers, so

$$
|I\cap G_n\cap G_m|\le(|I|p^n+2)\Big(\frac{4\epsilon^2}{nmp^n}+\frac{2\epsilon}{mp^m}+\frac{4\epsilon^2}{m^2p^m}\Big)
\ll|I|\Big(\frac{\epsilon^2}{nm}+\frac{\epsilon p^{n-m}}{m}\Big)
$$

once $|I|p^n\ge1$. Put $A=\sum_{L\le H\le U}1/H$. Then
- the off-diagonal sum is at most $|I|(4\epsilon^2A^2+O(\epsilon A))$, because $\sum_{n<m}p^{n-m}\le1/(p-1)$;
- the diagonal sum is at most $2\epsilon|I|A(1+o(1))$.

Cauchy–Schwarz then gives $|I\cap\bigcup_{H\ge L}G_H|\ge(c^2/4-o(1))|I|$ as $U\to\infty$. The correlation bound is in fact pessimistic. A primitive center at level $m$ is at distance at least $p^{-m}$ from $p^{-n}\mathbb Z$. Therefore $G_n\cap G_m=\varnothing$ whenever $p^{m-n}<(n/\epsilon)(1-\epsilon/m)$.

### S5. Null level sets

Take $x$ in a good interval about $x_0$. The ball $B(x,2\delta_H)$ contains both flanks, and one whole flank of length $\delta_H$ misses $\{M=w\}$. So the relative density of $\{M=w\}$ in that ball is at most $3/4$, and $\delta_H\to0$. Measurability holds because $\{M=w\}=\bigcap_L\{M\equiv w\bmod p^L\}$ is a countable intersection of finite unions of intervals.

**Localization near the ends of the shell.**
- Near $x=0$, that is $u\to1^+$, the factor $x^{1-3d}$ in $f'''$ is unbounded, which is why the note works on compact $K$.
- Near $x\to(p^d-1)^{1/d}$ nothing degenerates.
- The level set in $u$ is the image of a null set under the $C^1$ map $x\mapsto1+x^d$, exhausted by countably many $K$, so it is null.

### S6. From $p$-adic levels to real orbits

**Density of failed shifts.** At cutoff $N=tp^{dJ}y$, the failed shifts number at most $t|E_L|\sum_{j\le J}p^{dj}+O_L(J)$. Their upper density is therefore at most $p^d|E_L|/(p^d-1)$. Continuity from above gives $|E_L|\to|\{M=0\}|=0$.

**Depth for a quadratic.** Take $P=AX^2+BX+C_0$ with integral coefficients and $g=v_p(A)$. Off $E_L$ the depth is at least $2sJ-L+1-g$. The linear part has depth at most $sJ$, since $K(n)<p^{J+1}$.

**Hypotheses of the criterion.**
1. There are $O(N^{2/d})$ insertions, and $2/d<1$.
2. The denominators divide $p^{2sJ}\le(n/t)^{2s/d}$.
3. For fixed $M$, the shifts with $q_n<M$ lie, in late shells, in the failed set at every precision $L$, so they have density zero.

The coefficients satisfy $|a_m|\le m$. Rational coefficients reduce as in E1. The Phase 18 review records the criterion itself as closed. Its analytic core is the kernel-verified `fixed_support_orbit_estimate`.

*Check.* The relative measure of $E_L$ for the flagship is:

| $L$ | 1 | 2 | 4 | 6 | 8 | 10 | 11 |
|---|---|---|---|---|---|---|---|
| $\lvert E_L\rvert/26$ | 0.3077 | 0.0883 | 0.0213 | 1.68e-3 | 2.04e-4 | 2.90e-5 | 1.13e-5 |

Equivalently $3^L|E_L|/26\in[0.79,2.02]$. The first entry is $8/26$, from the cells $[1,2)\cup[9,16)$. This is consistent with an atomless mass whose density near $0$ is comparable to Haar measure. It also agrees with the Phase 18 failed-cell bounds.

## 2. Quadratic forms in several orders (claim Q)

Take the least first order $a_*$ among the top-weight monomials $X_{a}X_{D-a}$, and let $A$ be its coefficient with $g=v_p(A)$. Work at precision $a_*H+g+1$.

- *The chosen monomial.* A pair contributes only if $a_*h+(D-a_*)k\le a_*H$, which forces $h+k\le H$.
- *Other top-weight quadratics.* They have both orders above $a_*$, so their contributing pairs have $h+k\le(a_*H+g-g')/(a_*+1)<H$ eventually.
- *Top-weight linear term.* It jumps at $x=(z^d-1)^{1/d}$ with $z>1$ and $Dh\le a_*H+g$. That is $O(p^{H/2})$ endpoints, so removing nearby centers costs $o(p^H)$.
- *The jump.* At a surviving isolated center the jump is $A(p^{a_*H}+p^{(D-a_*)H})$, of valuation $a_*H+g$ in both cases ($2$ is a unit when $a_*=D-a_*$). The other top-weight jumps there have valuation at least $a'H+g'>a_*H+g$.
- *Lower weights.* Lower-weight terms lose at least $J$ after normalization by $p^{DJ}$. Linear and quadratic terms use the same $J$, because $\lfloor\log_p\lfloor(n/t)^{1/d}\rfloor\rfloor=\lfloor\log_p(n/t)^{1/d}\rfloor$.

The tied-weight example $3X_1X_3-X_2^2+X_4$ in the author's script exercises a case where three terms share weight four.

## 3. Universal schedules under rapid variation (claim U)

This is the denser-schedule result: consecutive ratios may tend to one.

**Estimate (3) is purely arithmetic.**
- If $J_m-v_p(m)\to\infty$, then $m$ is eventually not a power of $p$. So $U_{m-1}$ has exact valuation $-sJ_m$, and $AU_{m-1}^r$ wins by at least $s(J_m-v)$.
- If $J_m-v$ stays bounded, the limit $p^{sv}U_{m-1}\to B(a)$ uses only hypothesis 2 at each fixed layer, together with the count $a(p-1)p^{h-1}$ of indices of valuation $v-h$ below $ap^v$. The real bounds $-1<B(a)<0$ and the monic integer polynomial in $B(a)$ exclude a zero limit.

**Steps that use growth.** I checked each one.
- Non-grid tuples vanish modulo $p^L$, in every degree.
- If all grid exponents are at most $n/r$, the valuation of the normalized prefix is $g$.
- Otherwise the last grid index $m$ satisfies $m-p^{J-H}\le(1-p^{-H-1})m$, so every earlier grid exponent is at most $w_m=o(n_m)$.
- $m>K/p$ by rapid variation with $c=1/p$, so $J_m\ge J-1$ and the valuation is at most $C+rs<L$.
- Consecutive members of $S_H$ have ratio at least $1+p^{-H-1}$, so their exponents grow faster than any geometric sequence. Hence $\sum_{m\in S_H,\,n_m\le N}(w_m+1)=o(N)$.
- $K(N)=N^{o(1)}$ follows from $n_{2i}/n_i\to\infty$.

**The example.** $n_{\lfloor ci\rfloor}/n_i\approx c\,e^{2\log c\log i}\to0$ and $n_{i+1}/n_i\to1$. Hypothesis 2 follows from $ti\mid n_i$ by lifting the exponent. The note's claim of transcendence without the Liouville property for this example is correct and properly scoped.

## 4. Separated pole growth (claim G)

- The depth of $U^{\nu-j}V^j$ is exactly $\sum_a\nu_ae_{a,k-1}+\sum_aj_a(e_{a,k}-e_{a,k-1})$.
- Linear independence of the $\gamma_a$ makes the top value of $\gamma\cdot\nu$ unique, and the top allowed value of $\gamma\cdot j$ unique within the winning monomial.
- Since $f_k-f_{k-1}\sim\sqrt{\log k}$ tends to infinity and is $o(f_{k-1})$, both margins tend to infinity. The fixed binomial coefficients cannot cancel the unique deepest term.
- The denominators are at most $n_k^{O(1)}$ and the tuple count is $O((\log N)^r)$.
- The Liouville estimate uses $n_{k+1}/n_k\to\infty$ against denominators $b^{rn_k+O(\log n_k)}$.

No congruence $t\mid n_k$ is needed here, and none is used.

## 5. Dyadic paragraph and scope

**The dyadic criterion.** Thresholds of $r$-tuples lie in the compact countable set $rD$. At each fixed precision only finitely many tuples matter. So $M_r$ is constant on each complementary interval, and the criterion is a correct sufficient condition. It is **not satisfied in degree 2**: Phase 16 gives $M_2=0$ on $[3/2,2)$. The note therefore makes no new unconditional dyadic claim, which matches its last sentence.

**The scope paragraph** is accurate. The count of $r$-tuples of total loss at most $H$ is about $H^{r-1}p^H/(r-1)!$. A single primitive grid at radius $1/(H^{r-1}p^H)$ has summable lengths for $r\ge3$, so the second-moment step fails. O5 records a smaller point about the precision when $p\mid r$.

## Objections and suggested edits

**O1. Uniformity in (1).** Every error term in (1) is uniform over $I\subset K$:
- $O(H^2p^{4H/5})$ from small rows;
- $O(H^{-5}p^H)$ from removed rows and points;
- $O(H^{-2}p^H)$ from Erdős–Turán;
- $O(\epsilon p^H/H)$ from lattice errors.

Writing $o_I(p^H)$ suggests otherwise. The dependence on $I$ enters only through the threshold $H_0(I)$ beyond which $\epsilon|I|p^H$ dominates. I suggest writing $o(p^H)$ and stating $c=(1-1/p)-C_{p,d,K}\epsilon$.

**O2. Constants in the second moment.** The bound $|I\cap\bigcup_{H\ge L}G_H|\ge c'|I|$ is proved for $L\ge L_0(I)$. It extends to all $L$ because $\bigcup_{H\ge L}G_H$ decreases in $L$. This is what makes $c'$ independent of $I$ and $L$, and one sentence would make it explicit. The emptiness of $G_n\cap G_m$ for $p^{m-n}<(n/\epsilon)(1-\epsilon/m)$ is a cheap sanity check worth recording.

**O3. Short pieces in (2).** "Also for a short overlap or summation interval" needs the inequality $\lambda\ge T^{-3}$, that is $lp^HD\ge1$. It holds because $D\ge H^{-O(1)}$, and it should be stated. Graham–Kolesnik Theorem 2.6 states the third-derivative bound directly; Theorem 2.2 is the second-derivative test.

**O4. Linear endpoints in Q.** The removal threshold $Dh\le a_*H+g$ ignores the valuation of the linear coefficient, so it removes a superset. That is harmless. The endpoints are $x=(z^d-1)^{1/d}$ for $z>1$ only, and saying so would help the reader.

**O5. Valuation of the basic jump when $p\mid r$ (scope remark only).** In an $r$-fold convolution the basic family $(1,\ldots,1,y)$, with $y$ of loss $H$, has $r$ orderings. Its jump $rp^{sH}$ therefore has valuation $sH+v_p(r)$, not $sH$. For $p=r=3$ the families $(1,1,y)$, $(1,2,y)$ and $(2,2,y)$ have $3$, $6$ and $3$ orderings. A cube argument at $p=3$, for instance for $C(2,3,1,4)^3$, which Phase 18 leaves open at $s=1<3$, would therefore have to work at precision $sH+2$.

For $s=1$ that precision admits extra competitors of total loss $H+1$. Only the diagonal tuples $(y,y,y)$ qualify, because the other orbits have $3$ or $6$ orderings, and there are only $O(p^{(H+1)/3})$ of them. So this is bookkeeping and not a new obstruction. The decisive failure is still the summability of radii identified in the note. The note is correct as written. One clause recording the valuation shift would stop a reader from assuming that the jump $2p^{sH}$ carries over as $rp^{sH}$ with the same precision.

## External inputs and what is proved

The square, quadratic-form, universal-schedule and separated-growth theorems are proved on paper, assuming:
1. the van der Corput second- and third-derivative tests (Graham–Kolesnik, Theorems 2.2 and 2.6);
2. the Erdős–Turán inequality;
3. the Lebesgue density theorem and Cauchy–Schwarz;
4. the Phase 18 all-prefix criterion and rational reduction E1, both reviewed as closed. The criterion rests on the kernel-verified fixed-support orbit theorem.

Nothing in this note is kernel-verified. In particular, **$C(2,3,1,3)^2$ is normal to base 2**, and so is every rational quadratic in $C(2,3,1,3)$. The shifts of $(C,C^2)$ are jointly uniformly distributed, and an algebraic $C(b,p,s,d)$ would have degree at least 3. The method gives no rate of convergence. Cubes and higher degrees at $s<r$ remain open.
