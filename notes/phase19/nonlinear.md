# Nonlinear normality on power schedules and rapidly varying schedules

Let $b\ge2$, let $p$ be an odd prime coprime to $b$, and put $t=\operatorname{ord}_p(b)$. For positive integers $s,d$, write

$$
 C(b,p,s,d)=\sum_{i\ge1}p^{-s v_p(i)}b^{-t i^d}.
$$

**Square theorem.** For $d\ge3$ and $s\ge1$, every rational polynomial of degree two in $C(b,p,s,d)$ is normal in base $b$. In particular the binary shifts of
$(C(2,3,1,3),C(2,3,1,3)^2)$ are jointly uniformly distributed. The new case is $s=1$. The proof shows that the limiting $p$-adic square mass has an atomless distribution when the real shell parameter is sampled uniformly. It allows individual parameters at which the mass vanishes.

The same conclusion holds for every nonconstant rational polynomial of total degree at most two in **any finite set of distinct orders** $X_a=C(b,p,a,d)$ at the same prime and degree $d$. In particular all the distinct linear and quadratic monomials in these generators have jointly uniformly distributed shifts. The argument separates mixed terms with the same maximal pole growth by their responses at a primitive grid point.

**Universal schedules.** For a valuation-weighted series on exponents $n_i$, rapid variation in the index and a $p$-adic phase condition suffice for normality of every nonconstant rational polynomial. One example has $\log n_i\sim(\log i)^2$ and $n_{i+1}/n_i\to1$. A separate construction below gives finite sets of algebraically independent generators for which every nonconstant rational polynomial in all the generators is normal and Liouville.

These are paper proofs. The arithmetic inputs are the fixed-support short-orbit theorem and the rational-prefix and real-tail transfer in Phase 18. The estimates for jumps, the measure argument and the extensions of the schedules are given below. [Phase 18 algebra](../phase18/algebra.md) · [All-prefix criterion](../phase18/principal.md#a-fixed-support-criterion-for-all-prefixes) · [Fixed-support orbit theorem](../../NormalityChecker/SmoothOrbit.lean)

## 1. The square mass and its primitive grid of jumps

On $1\le u<p^d$ a coordinate is $z=a/p^h$, with $h\ge0$, $a$ a positive integer and $p\nmid a$. Only $0<z<p$ is needed. Call $h$ its loss. Define

$$
 M(u)=\sum_{z^d+y^d\le u}p^{s(h+k)}\ \in\mathbb Z_p ,
$$

where the pairs are ordered and $k$ is the loss of $y$. At any fixed total loss there are finitely many pairs. The truncation to $h+k\le H$ determines $M\bmod p^{sH+1}$ uniformly. Let $x=(u-1)^{1/d}$. Work on compact subintervals of $0<x<(p^d-1)^{1/d}$. The endpoint $u=1$ has measure zero, and $du=d x^{d-1}\,dx$ in the interior.

Pairs with a coordinate equal to 1 have their jumps at $x=c/p^v$, where $v\le H$. The *primitive* centers at level $H\ge1$ are those with $v=H$ and $p\nmid c$. Exactly two ordered pairs with a coordinate equal to 1 give such a center. Their combined jump is $2p^{sH}$, nonzero modulo $p^{sH+1}$. All the other centers from this same family are at distance at least $p^{-H}$. We show that sufficiently many primitive centers also have room on both sides before the next jump from another pair.

### Counting competing endpoints

Fix a compact interval $K$ in the open $x$-range. Fix a nondegenerate interval $I\subset K$, and $0<\epsilon<1/4$. Set

$$
 \delta_H=\frac{\epsilon}{H p^H}.
$$

For all sufficiently large $H$, at least $c |I|p^H$ primitive centers in $I$ have **no endpoint of total loss at most $H$ from a pair with both coordinates different from 1** within distance $\delta_H$. Here $c>0$ and the choice of sufficiently small fixed $\epsilon>0$ can be made uniformly in $I\subset K$. The starting $H$ may depend on $I$.

To prove this, order a competing pair by losses $v\ge k$, with $v+k\le H$. Let $y=a/p^k\ne1$ be the coarser coordinate and $z=m/p^v$ the finer one. In upper bounds we may allow all fine numerators. In the $x$-coordinate an endpoint is

$$
 f_y(z)=(z^d+B)^{1/d},\qquad B=y^d-1.
$$

For a collision it must lie in the $\delta_H$-enlargement $I^+$ of $I$ and satisfy $\|p^H f_y(z)\|\le\epsilon/H$, with $\|\cdot\|$ denoting distance to the nearest integer. Each competing endpoint spoils at most one primitive center. The number $B_H(I)$ of competitors meeting both tests, counted with multiplicity, satisfies

$$
 B_H(I)\le C_{p,d,K}\epsilon |I|p^H+o_I(p^H).                 \tag{1}
$$

All estimates take $H$ large enough that $I^+$ stays in a slightly larger fixed compact interval in the open range.

**Removing small or degenerate rows.** The rows with $v<2H/5$ have $O_p(H^2 p^{4H/5})$ points altogether. In the remaining rows put $\eta=H^{-6}$. Remove rows with $|B|\le\eta$. For $y\ne1$ this is possible only when $0<|y-1|\le C_d\eta$. Counting nonzero integer offsets from $p^k$ gives $O_d(\eta p^k)$ such numerators, including when this bound is below one. Also remove points with $z\le\eta$ or

$$
 |(d-2)B-(d+1)z^d|\le\eta^d.
$$

For each row these two conditions cover intervals of total length $O_d(\eta)$, since $z\ge0$ and $w^d-z^d\ge(w-z)^d$ for $w\ge z$. Their cost per row is $O_d(\eta p^v+1)$. The sums

$$
 \sum_{k\le v,\ k+v\le H}p^{k+v}=O_p(Hp^H),\qquad
 \sum_{k\le v,\ k+v\le H}p^k=O_p(H^2p^{H/2})
$$

show that all these removals cost $o(p^H)$, even charging every removed point as a collision.

**Distribution in a row.** On the remaining part of each row with $f_y(z)\in I^+$,

$$
 f_y'''(z)=(d-1)Bz^{d-3}(z^d+B)^{1/d-3}
              \big((d-2)B-(d+1)z^d\big).
$$

Its magnitude is between $H^{-O_d(1)}$ times a positive $K,d$-constant and a fixed $K,d,p$-constant. Partition into $O_{K,d,p}(\log H)$ intervals on each of which it has constant sign and magnitude between some $D$ and $2D$. Indeed its derivative has a polynomial numerator of bounded degree after removing powers of $z$ and $z^d+B$, so there are boundedly many monotonicity intervals. An identically constant derivative on a component needs no monotonicity cuts.

Put $T=p^v$. For each integer $1\le l\le H^4$, the phase $g(m)=l p^H f_y(m/T)$ on such a piece has third derivative of magnitude between $\lambda=l p^H D/T^3$ and $2\lambda$. The third-derivative estimate, with the ambient length $O_p(T)$, gives

$$
 \left|\sum_m e^{2\pi i g(m)}\right|
 \ll_p T\big(\lambda^{1/6}+T^{-1/2}\lambda^{-1/6}\big).       \tag{2}
$$

For clarity, difference the sum with shifts up to $Q=\lfloor\lambda^{-1/3}\rfloor$. Here $1\le Q\le T$ for large $H$. The phase increment at shift $a$ has second derivative of constant sign and magnitude between $a\lambda$ and $2a\lambda$ on the overlap interval. The classical van der Corput second-derivative bound on that interval is $O_p(T\sqrt{a\lambda}+1/\sqrt{a\lambda})$. The differencing inequality, extending the sum by zero outside the piece, bounds the squared normalized sum by $O_p(1/Q+\sqrt{Q\lambda}+1/(T\sqrt{Q\lambda}))$. This gives (2), also for a short overlap or summation interval. One source for the second-derivative test is Graham and Kolesnik, *Van der Corput's Method of Exponential Sums*, Chapter 2.

Since $2H/5\le v\le H$, the first term in parentheses in (2) is at most $H^{O(1)}p^{-H/30}$, and the second is at most $H^{O(1)}p^{-H/6}$. Erdős–Turán with cutoff $\lfloor H^4\rfloor$, in unnormalized form, now bounds the collision count on the retained part of a row by

$$
 (2\epsilon/H)\,\#\{m\text{ on the retained part}\}+O_{K,d,p}(T H^{-3}).
$$

The error includes the dyadic partition and the harmonic sum over $l$. Summing it over rows costs $O(H^{-2}p^H)$.

**Localizing the main term.** For any pair of losses, the number of all grid points $0<y,z<p$ with $f_y(z)\in I^+$ is

$$
 O_{K,d,p}\big(|I^+|p^{v+k}+p^v+p^k\big).
$$

The planar area of the slab is $O(|I^+|)$. Indeed the positive quadrant area below $z^d+y^d\le 1+x^d$ is a constant times $(1+x^d)^{2/d}$, which has bounded derivative here. Intersecting the slab with the coordinate square only reduces its area. For the lattice error, each sublevel region cut by the square lies below a decreasing graph. Counting one column at a time and comparing the monotone Riemann sum to the integral costs $O_p(p^v+p^k)$ on this rectangular grid, with either endpoint convention. Subtract the two sublevel counts. Also $\sum_{k\le v,\ k+v\le H}p^v=O_p(p^H)$, by summing first over $v\le H-k$. Multiplying the slab count by $2\epsilon/H$ proves (1), together with the errors above. There are $(1-1/p)|I|p^H+O(1)$ primitive centers in $I$. Choosing $\epsilon$ sufficiently small completes the claim.

### From isolated jumps to null level sets

Call the intervals of radius $\delta_H$ about the isolated primitive centers good, and write $G_H$ for their union on the compact range under consideration. The isolation condition refers to all competing endpoints, including those approaching the range from outside. Each of the two open halves of a good interval has a constant residue for $M\bmod p^{sH+1}$, and their residues differ by $2p^{sH}$.

Almost every $x$ in the interior of $K$ lies in infinitely many $G_H$. Here it matters that $\sum 1/H$ diverges. For an interval $I$ in the interior, use centers in its middle half in the lower bound, giving

$$
 |I\cap G_H|\gg |I|\epsilon/H
$$

eventually. For $n<m$ sufficiently large (depending on $I$), the full grids give

$$
 |I\cap G_n\cap G_m|
 \ll |I|\left(\frac{\epsilon^2}{nm}
                 +\frac{\epsilon p^{n-m}}{m}\right).
$$

Indeed $O(|I|p^n)$ coarse intervals meet $I$. Each meets at most $O(1+\delta_n p^m)$ fine intervals of length $2\delta_m$. The diagonal has $|I\cap G_n|\ll |I|\epsilon/n$. For $S=\sum_{H=L}^U {\bf1}_{G_H}$ and $A=\sum_{H=L}^U 1/H$, these bounds give $\int_I S\gg |I|\epsilon A$ and $\int_I S^2\ll |I|(\epsilon^2 A^2+\epsilon A)$. Cauchy–Schwarz and then $U\to\infty$ give $|I\cap\bigcup_{H\ge L}G_H|\ge c'|I|$ with $c'>0$ independent of $I,L$. Taking $L\to\infty$ and applying the Lebesgue density theorem to the complement proves the assertion.

Fix any $w\in\mathbb Z_p$. At a point of $G_H$, the interval of radius $2\delta_H$ centered there contains both flanks of its good interval. At least one whole flank of length $\delta_H$ misses $\{M=w\}$. A point in infinitely many $G_H$ therefore cannot be a density point of that level set. The mass is measurable by its finite step-function reductions. The density theorem proves that each level set has measure zero. Exhaustion by compact intervals and the change back to $u$ prove the assertion on the whole shell.

### Transfer to real radix orbits

For a large shift $n$, write $J=\lfloor\log_p((n/t)^{1/d})\rfloor$ and $u=n/(t p^{dJ})$. Let $R_n$ be the shifted rational prefix of the ordered square convolution. For each fixed precision $L$, Phase 18's freezing argument gives $p^{2sJ}b^{-n}R_n\equiv M(u)\pmod {p^L}$ uniformly for sufficiently large $J$. Indeed indices of retained loss $h$ have the form $a p^{J-h}$, and $b^{t(a p^{J-h})^d}\to1$ uniformly at each bounded loss. On $\{M\not\equiv0\bmod p^L\}$ the pole has depth at least $2sJ-L+1$. An integral leading coefficient costs its fixed valuation, and the linear and constant terms have depth at most $sJ$.

The finite union of failed cells $E_L=\{u:M(u)\equiv0\bmod p^L\}$ decreases to a null set. For fixed $L$, integer sampling incurs $O_L(1)$ rounding error per shell. At any cutoff in shell $J$, all failed positions through it occupy at most $t|E_L|\sum_{j\le J}p^{dj}+O_L(J+1)$ shifts, plus finitely many initial shifts. Dividing by the cutoff gives upper density at most $p^d|E_L|/(p^d-1)$. Taking $L\to\infty$ gives density zero for every bounded-denominator cap. The ordered square has $O(N^{2/d})$ tuple insertions, polynomially bounded coefficients, and shifted denominators dividing $p^{2sJ}$. The all-prefix criterion gives normality. For rational polynomial coefficients, clear the fixed common denominator as in Phase 18 E1, absorbing its radix-prime factors by a fixed orbit shift. Multidimensional Weyl and the known degree-one result give joint uniformity of the pair. In particular an algebraic $C(b,p,s,d)$ must have degree at least three.

### Quadratic forms in distinct orders on the same schedule

Let $P$ be any nonconstant integral polynomial of total degree at most two in finitely many $X_a=C(b,p,a,d)$. Give a linear term $X_a$ weight $a$, and $X_aX_c$ weight $a+c$. Write $D$ for the largest weight present after collecting like terms. A term of weight less than $D$ loses at least $J$ powers of $p$ after normalization by $p^{DJ}$. If the sole top-weight term is linear, its exact pole $DJ$ before multiplication by its coefficient proves retention immediately.

Otherwise, among the top-weight quadratic terms $X_aX_{D-a}$ with $a\le D-a$, take the least first order $a_*$. There is exactly one such monomial with this first order because its partner is $D-a_*$. Write $A\ne0$ for its coefficient, $g=v_p(A)$, and examine the top-weight mass at precision $a_*H+g+1$. The mass is the sum of the quadratic kernels above with the ordered weight $p^{ah+ck}$ for $X_aX_c$ in place of $p^{s(h+k)}$, multiplied by their coefficients. A possible linear term of weight $D$ has threshold $z^d\le u$ and weight $p^{Dh}$. As before these masses freeze uniformly at every fixed precision. For the chosen monomial, pairs of total loss above $H$ vanish at the selected precision after multiplication by $A$. Every other top-weight quadratic monomial has both orders strictly larger than $a_*$, so its pairs above total loss $H$ also vanish for sufficiently large $H$.

Use the same isolated primitive centers as before. Remove any center within $\delta_H$ of a linear endpoint with $Dh\le a_*H+g$. This costs $O_{P,p}(p^{H/2})$ centers since $D\ge2a_*$, with at most one center lost per endpoint. The counting lemma and its second-moment conclusion therefore still hold. At a remaining center the chosen monomial contributes a jump

$$
 A\big(p^{a_*H}+p^{(D-a_*)H}\big).
$$

When $a_*=D-a_*$, its valuation is $a_*H+g$ since $p$ is odd. If the two orders differ, its valuation is again $a_*H+g$. All other quadratic jumps at that center have valuation greater than $a_*H+g$ for sufficiently large $H$, including their coefficients. The two flanks thus have different top-weight residues. The density-point proof shows that every level set of this combined mass is null. The real transfer uses nominal depth $DJ$ and the same $O_P(N^{2/d})$ insertion count. Clearing rational coefficients proves the stated quadratic-form theorem; applying it to each nonzero integer combination proves joint uniformity of the distinct monomials.

**Scope of the jump argument.** It gives no explicit discrepancy rate or pointwise lower bound on the mass. For an $r$-fold convolution the elementary total grid count at loss through $H$ is $O_{p,r}(H^{r-1}p^H)$. Targeting a single primitive grid at radius $1/(H^{r-1}p^H)$ gives a convergent sum of neighborhood lengths for $r>2$. An extension by this method would need additional primitive families or a stronger collision estimate. For the Phase 17 dyadic leading mass the shell parameter enters through sums of powers of two. The curved two-coordinate grids and the nonzero jump $2\bmod p$ used above are absent. In the mixed Stoneham problem the relevant variables are coupled integer shell indices. Real shell nullity alone does not control their visits to growing-depth residue classes. [Dyadic classification](../phase17/dyadic-stoneham-classification.md) · [Mixed shell-index inequalities](../phase17/mixed-product-orbits.md)

For the dyadic problem there is a precise transfer. Let $D=\{0\}\cup\{2^{-j}:j\ge0\}$. The $r$-fold sum $rD$ is compact and countable. On each complementary open interval the dyadic mass $M_r(t)$ is constant, since no tuple threshold occurs there. Thus its real-shell distribution is **purely atomic**. Its zero set on $[1,2)$ has measure zero exactly when the mass is nonzero on every complementary interval in that shell. This interval condition suffices for normality of all degree-$r$ rational polynomials in $\alpha_{b,2}$ for odd $b$, even allowing zeros on $rD$. Indeed the mod-$2^L$ truncation has finitely many cells, and its failed measure decreases to zero under the condition. On shell $n=2^Jt$, the normalized $r$-fold prefix freezes uniformly at each fixed precision since $b^{2^{J-h}}\to1$ in $\mathbb Z_2$ for bounded $h$. The preceding geometric shell count and denominator separation apply with maximal depth $rJ$, lower degrees at most $(r-1)J$, and $O_r((1+\log N)^r)$ tuples. Determining the open plateau values in unresolved degrees remains necessary for this sufficient test. [Dyadic prefix normalization](../phase16/dyadic-stoneham.md)

## 2. Universal polynomial normality with consecutive ratios tending to one

Let $n_i$ be strictly increasing positive multiples of $t$, and put $X=\sum_{i\ge1}p^{-s v_p(i)}b^{-n_i}$. Assume

1. $n_{\lfloor c i\rfloor}/n_i\to0$ for each fixed $0<c<1$ (rapid variation).
2. $b^{-n_i}\to1$ in $\mathbb Z_p$ whenever $v_p(i)\to\infty$.

Then $P(X)$ is base-$b$ normal for every nonconstant $P\in\mathbb Q[z]$. In particular $X$ is transcendental, and the shifts of $(X,X^2,\ldots,X^r)$ are jointly uniformly distributed in every finite dimension. An explicit schedule is

$$
 n_i=t i\,\left\lceil\exp\big((\log(i+1))^2\big)\right\rceil .
$$

Here $ti\mid n_i$ ensures the second hypothesis by lifting the exponent. The log ratio at index $\lfloor ci\rfloor$ is $2\log c\log i+O_c(1)$, while the consecutive log differences tend to zero. The argument gives transcendence for this example. The usual Liouville truncation estimate requires larger consecutive gaps in the ratio $n_{i+1}/n_i$.

**Arithmetic estimate independent of schedule growth.** Work with integral $P$ of degree $r$, leading coefficient $A\ne0$. Set $V_i=p^{-s v_p(i)}b^{-n_i}$ and $U_k=\sum_{i\le k}V_i$. Define the partial Taylor polynomial

$$
 F_l(U,V)=\sum_{j=0}^l P^{(j)}(U)V^j/j!,\qquad 0\le l\le r .
$$

There is a constant $C$ such that, for every sufficiently large $m$ and every $l$,

$$
 v_p(F_l(U_{m-1},V_m))\le -rs\lfloor\log_p m\rfloor+C.       \tag{3}
$$

This is the arithmetic part of the Phase 18 fast-schedule proof. Only the phase hypothesis and $t\mid n_i$ enter (3). To recall the proof, set $v=v_p(m)$, $J_m=\lfloor\log_p m\rfloor$. If $J_m-v\to\infty$, $U_{m-1}$ has exact valuation $-sJ_m$ by counting its highest indices modulo $p$. Then $AU_{m-1}^r$ has uniquely least valuation eventually. If $J_m-v$ is bounded along a sequence, extract a subsequence with $a=m/p^v$ and $l$ fixed. We have $p^{sv}V_m\to1$ and $p^{sv}U_{m-1}\to B(a)$, where

$$
 B(a)=\sum_{i<a}p^{-s v_p(i)}
          -a\frac{(p-1)p^s}{p^{s+1}-1},\qquad -1<B(a)<0 .
$$

The sum starts at $i=1$. Indices divisible by $p^v$ give the finite sum in the limit. Indices of valuation $v-h$ for $h\ge1$ contribute $a(p-1)p^{h-1}p^{sh}$ in the limit at each fixed $h$; the higher tail vanishes $p$-adically. The real inequality follows from $B(a)+1=\sum_{h\ge1}(p^{-s(h-1)}-p^{-sh})\{a/p^h\}$, since $p\nmid a$. The limit of $p^{rsv}F_l$ is $A\sum_{j=0}^l\binom rj B(a)^{r-j}$. The sum is a monic integer polynomial in $B(a)$, whose rational roots must be integers. The two subsequence alternatives prove (3) by contradiction. [Phase 18 plateau arithmetic](../phase18/algebra.md#universal-polynomial-normality-for-fast-schedules)

**Sparse indices at a fixed precision.** At cutoff $n$, let $K=\max\{i:n_i\le n\}$, $J=\lfloor\log_p K\rfloor$. Choose an integer $L>\max(C+rs,v_p(A),0)$, then a fixed $H\ge0$ with $s(H+1)\ge L$. For large $J$, after multiplying any unshifted prefix by $p^{rsJ}$, tuples involving an index $i\le K$ with $v_p(i)<J-H$ vanish modulo $p^L$. This follows by bounding every other loss by its maximal pole $sJ$; it holds also in lower degrees. The surviving indices lie on the grid of multiples of $p^{J-H}$.

If all those grid indices have $n_i\le n/r$, the normalized cutoff equals $p^{rsJ}P(U_K)\bmod p^L$. Its valuation is $v_p(A)<L$ for large $J$, by the exact pole of $U_K$. Otherwise let $m$ be the last grid index through $K$, so $n/r<n_m\le n$. Distinct grid indices differ by at least $p^{J-H}\ge m/p^{H+1}$. Thus the exponent of every earlier grid index is at most

$$
 w_m=n_{\lfloor(1-p^{-H-1})m\rfloor}=o(n_m).
$$

In particular only this last grid index can have exponent above $n/r$ eventually. Also $m>K/p$ for sufficiently large $K$, since $n_{\lfloor K/p\rfloor}=o(n_K)$ and $n_m>n/r\ge n_K/r$. Hence $J_m\ge J-1$.

Outside the intervals $[j n_m,j n_m+r w_m]$, $1\le j\le r$, a tuple of grid indices with $j$ copies of $m$ fits precisely when $j n_m\le n$. This includes $j=0$ since $r w_m<n_m$. There is no grid index strictly between $m$ and $K$. The normalized prefix therefore agrees modulo $p^L$ with

$$
 p^{rsJ}F_l(U_{m-1},V_m),\qquad l=\min(r,\lfloor n/n_m\rfloor).
$$

By (3) its valuation is at most $C+rs(J-J_m)\le C+rs<L$. This comparison keeps all partially present low-valuation tuples in the original prefix and charges their residues to zero at the selected precision.

**All-prefix cost.** Every candidate $m$ belongs to $S_H=\{m:J_m-v_p(m)\le H\}$. Consecutive sufficiently large members $m<m'$ of $S_H$ satisfy $m'/m\ge1+p^{-H-1}$, since both are divisible by $p^{J_m-H}$. Rapid variation gives $n_{m'}/n_m\to\infty$ along these centers. The total length of the discarded integer intervals through any $N$ is $O_r(\sum_{m\in S_H,\ n_m\le N}(w_m+1))=o(N)$. Indeed their exponent sequence is eventually at least geometric, and $w_m+1=o(n_m)$. This counts a partially observed interval at the current cutoff as well. On the complement the shifted pole has depth at least $rsJ-L+1$.

Rapid variation implies $n_i/i^a\to\infty$ for each fixed $a>0$, by iterating $n_{2i}/n_i\to\infty$ along powers of two and using monotonicity. Hence $K(N)^r=N^{o(1)}$ bounds the $r$-fold insertion count up to a constant for all degrees through $r$. Collision coefficients are polynomially bounded, and every shifted denominator divides $p^{rsJ}\le(n+1)^{rs}$. The all-prefix criterion and the rational-coefficient reduction finish the proof. Evaluating an algebraic relation would give zero, and applying multidimensional Weyl to polynomial combinations gives the two stated consequences.

## 3. Several generators with separated pole growth

Fix any finite list of positive real numbers $\gamma_1,\ldots,\gamma_m$ linearly independent over $\mathbb Q$. For instance take successive powers $1,\xi,\ldots,\xi^{m-1}$ of $\xi=2^{1/m}$ (Eisenstein at 2). Let $f_k=k\sqrt{\log(k+1)}$, $n_k=\lceil e^{f_k}\rceil$, and set

$$
 e_{a,k}=\lfloor\gamma_a f_k\rfloor,\qquad
 X_a=\sum_{k\ge1}p^{-e_{a,k}}b^{-n_k},\qquad 1\le a\le m .
$$

Every nonconstant $P\in\mathbb Q[z_1,\ldots,z_m]$ gives a normal Liouville number $P(X_1,\ldots,X_m)$ in base $b$. In particular these generators are algebraically independent, and any finite list of distinct nonconstant monomials in them has jointly uniformly distributed shifts. All coordinates here share the prime $p$. Their different rates of pole growth distinguish the monomials. This construction has $\log n_k=o(k\log k)$ and $n_{k+1}/n_k\to\infty$.

Clear coefficients and write $r=\deg P$. In shell $n_k\le n<n_{k+1}$, discard $[j n_k,j n_k+r n_{k-1}]$ for $1\le j\le r$. The total through $N$ is $o(N)$, by geometric summation and $n_{k-1}/n_k\to0$. Let $U_a$ be the old prefix before $k$, $V_a=p^{-e_{a,k}}b^{-n_k}$. On each remaining interval the prefix is the multivariate expansion of $P(U+V)$ restricted to terms with total number $|j|\le \min(r,\lfloor n/n_k\rfloor)$ of new factors. Since $f_k-f_{k-1}\to\infty$, eventually $U_a$ has uniquely largest individual pole $e_{a,k-1}$ at its last term.

For a monomial $z^\nu$ in $P$, a surviving choice $0\le j_a\le\nu_a$ has pole depth before its fixed integer coefficient

$$
 \sum_a \nu_a e_{a,k-1}
       +\sum_a j_a(e_{a,k}-e_{a,k-1}).
$$

The first sum is $f_{k-1}\gamma\cdot\nu+O_P(1)$; the second is $(f_k-f_{k-1})\gamma\cdot j+O_P(1)$. The largest $\gamma\cdot\nu$ among the participating monomials is positive and unique. Its $j=0$ choice always survives. Since $f_k-f_{k-1}=o(f_k)$, every other monomial has smaller depth by a quantity tending to infinity. Within the winning monomial the largest allowed $\gamma\cdot j$ is again unique. Its advantage over any other allowed vector tends to infinity since $f_k-f_{k-1}\to\infty$; there are only finitely many cutoffs in the number of new factors. The fixed coefficients, including binomial factors for repeated variables, preserve this unique deepest term eventually. Thus the pole tends to infinity off the discarded intervals.

All shifted denominators divide $p^{r\max_a e_{a,k}}$, bounded by a fixed power of $n_k+1$. There are $O_P((1+\log N)^r)$ tuple insertions and polynomially bounded collision coefficients. Normality follows as before. For the Liouville assertion truncate every variable through $k$. The resulting rational values have denominators at most a fixed coefficient denominator times $b^{r n_k}p^{r\max_a e_{a,k}}$. The real error is $O_P(b^{-n_{k+1}})$ by boundedness of the partial derivatives on a compact box containing the prefixes. Since $n_{k+1}/n_k\to\infty$, these errors beat every fixed inverse power of the denominator bound. The rational values approach an irrational by normality, so there are infinitely many distinct approximants. Algebraic independence follows by applying the theorem to a hypothetical relation, and joint uniformity follows by multidimensional Weyl.

## Exact checks

Run `python -B scripts/phase19_nonlinear.py` from the repository root. It enumerates ordered pairs on a common integer grid, checks both flanks of isolated centers with rational endpoints, and compares the frozen residues against direct binary convolution on both sides of every retained jump in a test shell. It also recovers the third derivative from three exact Taylor coefficients of the implicit polynomial equation. The asymptotic collision bound and the full-measure limsup follow from the analytic estimates above. [Exact checker](../../scripts/phase19_nonlinear.py)
