# Polynomials of every degree below the schedule degree

Let $b\ge2$, let $p$ be an odd prime with $p\nmid b$, put $t=\operatorname{ord}_pb$, and for integers $s\ge1$, $d\ge2$ let

$$
 C=C(b,p,s,d)=\sum_{i\ge1}p^{-sv_p(i)}\,b^{-ti^d}.
$$

**Theorem C3.** If $r\ge1$ and $d\ge r+1$, then $P(C)$ is normal in base $b$ for every nonconstant $P\in\mathbb Q[x]$ of degree at most $r$. Consequently $C(b,p,s,d)$ is not algebraic of degree less than $d$, and the shifts of $(C,C^2,\ldots,C^{d-1})$ are jointly uniformly distributed. In particular $C(2,3,1,4)$, its square and its cube are jointly normal in base 2.

For $r=2$, $d\ge3$ this is the Phase 19 square theorem (OP-14). The new cases are $r\ge3$. The proof is a written argument (reviewed independently in [track-c-review.md](reviews/track-c-review.md), with all three major referee findings repaired below); it gives no explicit rate. Its external inputs are the $q$-th derivative test (Titchmarsh, Theorem 5.13), the Erdős–Turán inequality, the divisor bound, the Lebesgue density theorem, and the Phase 18–19 freezing and all-prefix transfer. [Phase 19 square theorem](../phase19/nonlinear.md) · [Exact checks](../../scripts/phase20_normality.py)

## 1. The $r$-fold mass and the transfer

A coordinate is $z=a/p^h$ with $h\ge0$, $p\nmid a$ and $0<z<p$; $h$ is its loss. An $r$-tuple has level $\sum h_i$ and sum $S(z)=\sum z_i^d$. For $1\le u<p^d$ put

$$
 M_r(u)=\sum_{\text{ordered } z:\ S(z)\le u}p^{\,s(h_1+\cdots+h_r)}\in\mathbb Z_p .
$$

Only tuples of level at most $\lfloor(L-1)/s\rfloor$ affect $M_r\bmod p^{L}$. Write a shift as $n=tp^{dJ}u$. Index $i=ap^{J-h}$ gives $z=i/p^J$, weight $p^{sJ}p^{-sv_p(i)}=p^{sh}$, and $b^{ti^d}\to1$ in $\mathbb Z_p$ uniformly at bounded loss. So the Phase 19 freezing argument gives, for a degree-$r$ integral $P_0$ with leading coefficient $A$,

$$
 p^{rsJ}b^{-n}R_n\equiv A\,M_r(u)\pmod{p^L}\qquad(J\ge J_0(L)).
$$

Lower degrees have depth at most $(r-1)sJ$ and vanish. Failed shifts at precision $L$ lie in the finitely many cells of $\{M_r\equiv0\bmod p^{L-v_p(A)}\}$, whose measure decreases to $|\{M_r=0\}|$. The all-prefix criterion of Phase 18 needs $O(N^{r/d})=O(N^{1-\eta})$ tuple insertions, which holds exactly when $d\ge r+1$. It also needs denominators dividing $p^{rsJ}\le(n+1)^{rs/d}$, and density zero of small denominators. Rational coefficients are removed with `normal_mul_nat_iff`. Hence:

> **Reduction.** For $d\ge r+1$, Theorem C3 holds as soon as $\{u:M_r(u)=0\}$ has Lebesgue measure zero.

We prove the stronger statement that every level set of $M_r$ is null.

## 2. Why one primitive family stops at $r=3$

Phase 19 isolated the centres $(1,c/p^H)$. For $r$-fold sums the competitors of level at most $H$ number $\Theta(H^{r-1}p^H)$, so the natural radius is $\delta_H=\epsilon/(H^{r-1}p^H)$. A single family of $\Theta(p^H)$ centres then covers measure $\Theta(\epsilon H^{1-r})$. For $r=3$ this is summable, and neither Borel–Cantelli nor a second moment can reach full measure. The exact controls agree: for $p=3$, $d=4$, $H=2,\ldots,6$, the isolated measure of the family $(1,1,c/3^H)$ times $H^2$ stays at $0.016$–$0.017$.

## 3. Positive measure at every level suffices

Let $\mathcal G_H$ be a set of level-$H$ centres, each isolated: no other tuple sum relevant at precision $\pi_H$ lies within $\delta_H$, and the jump of $M_r\bmod p^{\pi_H}$ at the centre is nonzero. Let $G_H$ be the union of the intervals of radius $\delta_H/2$ about them. These intervals are disjoint.

**Lemma 2.** Suppose that for every interval $I$ in a compact subinterval $K'$ of $(1,p^d)$ one has $|I\cap G_H|\ge c|I|$ for infinitely many $H$, with $c>0$ independent of $I$. Then every level set of $M_r$ on $K'$ is null.

*Proof.* Reverse Fatou for sets gives $|I\cap\limsup G_H|\ge\limsup|I\cap G_H|\ge c|I|$. So the complement of $\limsup G_H$ has density at most $1-c$ at every point, and by the Lebesgue density theorem it is null. Let $x\in G_H$ lie within $\delta_H/2$ of the centre $\xi$. The interval of radius $2\delta_H$ about $x$ contains both flanks $(\xi-\delta_H,\xi)$ and $(\xi,\xi+\delta_H)$. These flanks carry distinct constant residues, so a level set $\{M_r=w\}$ misses one flank, which is a quarter of that interval. A point in infinitely many $G_H$ is therefore not a density point of $\{M_r=w\}$. The level set is measurable as a limit of step functions, so it is null. $\square$

No second-moment estimate is needed. The task is to make a **positive proportion** of $\Theta(H^{r-1}p^H)$ centres isolated at radius $\delta_H$.

## 4. Anchor families

Assume $r\ge3$ throughout Sections 4–6 (the cases $r=1,2$ are already proved in Phases 18–19). Put $\theta=(2r)^{-1/d}$. An **anchor** is an $(r-1)$-tuple $y=(y_1,\ldots,y_{r-1})$ with $y_i=a_i/p^{h_i}\le\theta$ and losses that are **dominant**:

$$
 h_1\ge1,\qquad h_2\ge\max(2h_1+1,\lceil(\log H)^2\rceil),\qquad
 h_j\ge2(h_1+\cdots+h_{j-1})+1\ (j\ge3),\qquad k=\textstyle\sum h_i\le\kappa H ,
$$

with $0<\kappa<\min(c/d,\,1/(2r))$ chosen in Section 5 (in particular $\kappa<1/2$, so $v=H-k>k\ge h_{r-1}$).

A **centre** is $(y,z)$ with $z=m/p^v$, $p\nmid m$, $v=H-k$, and $S=B_y+z^d\in K'$, where $B_y=\sum y_i^d<1/2$. Then $z^d>1/2$. The losses satisfy $1\le h_1<\cdots<h_{r-1}<v$, so they are strictly increasing and no two distinct centres $(y,z)$ are permutations of each other; in particular, any two distinct isolated centres are relevant competitors for each other and thus separated by $>\delta_H$, making the radius-$\delta_H/2$ intervals in $G_H$ pairwise disjoint. Exactly $r!$ ordered tuples sit at each centre and its jump is $r!\,p^{sH}$. Work at precision $\pi_H=sH+e_r+1$ with $e_r=v_p(r!)$. Then the jump is nonzero, and the relevant competitors are all tuples of level at most $H+\lfloor e_r/s\rfloor$. For $p>r$ this is precision $sH+1$ and level at most $H$. For $p=3$ and $r=3$, $s=1$ it is precision $H+2$, and among level-$(H+1)$ tuples only the diagonal ones matter, but including all of them costs only a factor $p$.

The dominant classes with $k\le\kappa H$ form a positive proportion of all loss vectors: there are $\gg_r(\kappa H)^{r-1}$ of them. Each anchor class has $\asymp p^k$ anchors and each anchor has $\gg|I|p^{v}$ centres in $I$. So the number of centres in $I$ is $\gg\kappa^{r-1}|I|H^{r-1}p^H$.

## 5. The pair-correlation bound

Count pairs (centre, competitor) with $|S(\text{competitor})-S(\text{centre})|\le\delta_H$. Write a competitor as $(w,x)$, where $x=m'/p^{v'}$ is its coordinate of largest loss and $w$ holds the other $r-1$ coordinates; its level is $H'\le H+\lfloor e_r/s\rfloor$, so $v'\ge H'/r$. A **row** is a pair (anchor $y$, competitor coarse part $w$). For a fixed pair of loss tuples $(h,h')$, there are at most $p^{k+H'-v'+2r}$ rows; summing over all pairs of loss tuples multiplies row counts by $H^{O(r)}$. Put $B=\sum w_i^d-B_y$ and $f_B(x)=(x^d+B)^{1/d}$. A collision forces $|f_B(x)-z|\le\delta'=C_d\delta_H$. Since $z^d>1/2$, each $x$ meets at most one centre of the anchor, and the condition reads $\|p^vf_B(x)\|\le\eta_0=p^v\delta'\asymp\epsilon p^{-k}H^{1-r}$. Moreover, on colliding points $S(w,x)\in I^+\subset(1,p^d)$ and $B_y<1/2$ force $x^d+B\in[1/4,p^d+1]$ (for both signs of $B$) and $|B|\le rp^d$.

**Rows with $B=0$ (rational separation and coincidences).** When $B=0$, a collision gives $|x-z|\le\delta'=C_d\epsilon H^{1-r}p^{-H}$. Since $v=H-k\le H$ and $v'\le H'\le H+\lfloor e_r/s\rfloor$, any $x\ne z$ satisfies

$$
 |x-z|=\left|\frac{m'}{p^{v'}}-\frac{m}{p^v}\right|\ge p^{-\max(v,v')}\ge p^{-H-\lfloor e_r/s\rfloor}.
$$

Because $r\ge3$ implies $H^{1-r}\to0$ while $C_d\epsilon$ and $\lfloor e_r/s\rfloor$ are fixed, for all sufficiently large $H$ we have $\delta'<p^{-H-\lfloor e_r/s\rfloor}$, forcing $x=z$. Since $p\nmid m$ and $p\nmid m'$, equality $x=z$ forces $v'=v$, and therefore fixes the competitor's coarse loss to

$$
 k'=H'-v'=H'-v=k+(H'-H)\le k+\lfloor e_r/s\rfloor.
$$

- *If $w=y$ as multisets,* then $(w,x)$ is a permutation of the centre $(y,z)$ itself, contributing nothing.
- *If $w\ne y$ as multisets,* we peel coordinates from $j=r-1$ down to $2$ (the balanced example $59^4+158^4=133^4+134^4$ shows that non-dominant anchors do admit $B=0$ coincidences at $p=5$). Suppose coordinates above $j$ have been matched and peeled off, leaving anchor loss $k_j=h_1+\cdots+h_j$ and remaining competitor coarse loss $k'_j=k_j+(H'-H)\le k_j+\lfloor e_r/s\rfloor$. The remaining anchor sum has $v_p(\sum_{i\le j}y_i^d)=-dh_j$. Dominance $h_j\ge2k_{j-1}+1$ implies $k_j=k_{j-1}+h_j\le\tfrac32h_j-\tfrac12$, so

  $$
   k'_j\le\tfrac32h_j-\tfrac12+\lfloor e_r/s\rfloor<2h_j
  $$

  for all sufficiently large $H$, because $h_j\ge h_2\ge\lceil(\log H)^2\rceil\to\infty$ while $\lfloor e_r/s\rfloor$ is fixed. Hence $w$ cannot have two remaining coordinates of loss $\ge h_j$; nor can it have a unique coordinate of loss $>h_j$ (making $v_p(\sum w_i^d)<-dh_j$) or all coordinates of loss $<h_j$ (making $v_p(\sum w_i^d)>-dh_j$). Thus $w$ has a unique remaining coordinate $c/p^{h_j}$ of loss $h_j$. If $c=a_j$, peel it off and descend. Otherwise $a_j^d-c^d=p^{dh_j}V_0\ne0$, where $V_0$ is fixed by the lower coordinates. Since $a_j-c$ divides $a_j^d-c^d$ and $c\mapsto(c+e)^d-c^d$ is strictly increasing in $c>0$ for fixed $e>0$, there are at most $2\tau(|a_j^d-c^d|)\ll_{\epsilon'}p^{\epsilon'dh_j}$ pairs $(a_j,c)$. The already-peeled coordinates ($i>j$) contribute at most $p^{k-k_j+O(r)}$ choices, and the lower coordinates ($i<j$) of $y$ and $w$ have losses $k_{j-1}$ and $k'_{j-1}\le k_{j-1}+\lfloor e_r/s\rfloor$, giving at most $O_{p,r}(k^rp^{2k_{j-1}})$ choices. Multiplying yields exponent $(k-k_j)+2k_{j-1}+\epsilon'dh_j=k-h_j+k_{j-1}+\epsilon'dh_j\le k-(\tfrac12-\epsilon'd)h_j$. After all peelings down to $j=1$, $y_1^d=w_1^d$ forces $w_1=y_1$ (and $H'=H$), contradicting $w\ne y$. Each nontrivial pair $(y,w)$ shares at most $p^{v+1}$ fine coordinates $z=x$; choosing $\epsilon'=1/(6d)$ and summing over $j\ge2$ (where $h_j\ge(\log H)^2$) and all loss tuples gives $O(H^{O(r)}p^{H-(\log H)^2/3})=o(p^H)$.

**Rows with $0<|B|<p^{-cH}$.** $B$ has denominator dividing $p^{dg}$, where $g$ is the largest coarse loss, so $|B|\ge p^{-dg}$ and $g>cH/d$. Because $\kappa<c/d$, the coordinate attaining $g$ is in $w$. Varying it confines it to a set of diameter $\le(2p^{-cH})^{1/d}$, which holds $\le2^{1/d}p^{g-cH/d}+1<3p^{g-cH/d}$ lattice points (since $g>cH/d\implies p^{g-cH/d}>1$). Charging every fine point and summing over all loss tuples gives $O(H^{O(r)}p^{k+H'-cH/d})\le O(H^{O(r)}p^{H-(c/d-\kappa)H})$.

**Rows with $|B|\ge p^{-cH}$.** For $q\ge2$,

$$
 f_B^{(q)}(x)=(d-1)B\,x^{d-q}(x^d+B)^{1/d-q}\,\Phi_q(x^d,B),
$$

where $\Phi_2=1$ and

$$
 \Phi_{q+1}=\big[(d-q)(X+B)+(1-qd)X\big]\Phi_q+dX(X+B)\,\partial_X\Phi_q .
$$

Here $\Phi_q$ is homogeneous of degree $q-2$ with leading coefficient $(-1)^q(d+1)(d+2)\cdots(d+q-2)\ne0$. For instance $\Phi_3=(d-2)B-(d+1)X$ and $\Phi_4=(d+1)(d+2)X^2-(d+1)(4d-7)BX+(d-2)(d-3)B^2$. The script checks these formulas exactly.

Put $\eta=p^{-2\kappa H}$ and $\rho=\eta^{d(q-2)}$, and remove the points with $x\le\eta$ or $|\Phi_q(x^d,B)|\le\rho$. The second set is at most $q-2$ pieces of diameter $O(\eta)$, by $|x^d-x'^d|\ge|x-x'|^d$. Because $k+H'-v'\le(\kappa+1-1/r)H+O(1)\le(1-\kappa)H+O(1)$ (using $\kappa<1/(2r)$), summing over all loss tuples bounds the removed points by $O(H^{O(r)}(\eta p^{k+H'}+qp^{k+H'-v'}))=O(H^{O(r)}p^{H-\kappa H})$.

On the rest, **because $q\le r+1\le d$** and $x^d+B\in[1/4,p^d+1]$, one has $D_{\min}\le|f_B^{(q)}|\le C$ with $D_{\min}\gg p^{-\gamma H}$ and $\gamma=c+2\kappa(d(q-1)-q)$. For the upper bound on collisions, drop the coprimality condition $p\nmid m'$ so that $m'$ runs over **consecutive** integers in each piece (this only increases the collision count and multiplies the main term $N_{\text{row}}$ by at most $p/(p-1)$). Monotonicity and dyadic ranges cut each row into $O(qH)$ pairwise-disjoint pieces on which $|f_B^{(q)}|$ has constant sign and ratio at most $2$. Apply Erdős–Turán with $L=\lceil p^kH^{r+1}\rceil$ harmonics to $\|p^vf_B(m'/p^{v'})\|\le\eta_0$. On each piece $P$ of length $\le pT$ ($T=p^{v'}\ge1$, including $v'=0$), Titchmarsh's Theorem 5.13 with $K_q=2^{q-1}$ applies unconditionally to the phase $g(m')=lp^vf_B(m'/p^{v'})$ (whose $q$-th derivative satisfies $\lambda\asymp lp^vD/p^{qv'}$), giving $|\sum_{m'\in P}e(g(m'))|\ll_q T\lambda^{1/(2K_q-2)}+T^{1-2/K_q}\lambda^{-1/(2K_q-2)}$ (the regimes $\lambda\ge1$ and $T^{K_q-1}\lambda\le1$ are trivially dominated by the first and second terms, and $1-2/K_q\ge0$). Summing $1/l$ over $1\le l\le L$ gives $\sum_{l\le L}l^{-1+1/(2K_q-2)}\asymp L^{1/(2K_q-2)}\asymp p^{k/(2K_q-2)}H^{(r+1)/(2K_q-2)}$ (cancelling $p^{-k}$ from $p^v=p^{H-k}$) in the first term and $\sum_{l\le L}l^{-1-1/(2K_q-2)}=O_q(1)$ in the second. Summing over all rows and loss tuples gives $H^{O(r)}(p^{E_1}+p^{E_2})$, where

$$
 E_1=k+H'+\frac{H-qv'}{2K_q-2},\qquad
 E_2=k+H'-\frac{2v'}{K_q}+\frac{qv'-H+k}{2K_q-2}+\frac{\gamma H}{2K_q-2}.
$$

Because the pieces of each row are disjoint, $\sum_{\text{pieces}}N_{\text{piece}}/L\le N_{\text{row}}/L$, so the Erdős–Turán $L^{-1}$ term summed over all rows (across all anchor losses $k$) is $O\bigl(\sum_y p^{-k}H^{-r-1}\cdot H^{r-1}p^H\bigr)=O(H^{r-3}p^H)=o(H^{r-1}p^H)$.

**Choosing $q$ (uniform margin for all $r\ge3$ and all $0\le\beta\le1$).** Write $\alpha=v'/H$ and $\beta_0=\min(1,H'/H)$, so $\beta_0/r\le\alpha\le\beta_0+O(1/H)$ and the excess $(H'-H)^+\le\lfloor e_r/s\rfloor$ adds only $O_{p,r}(1)$ to $E_1,E_2$. Replacing $H'/H$ by $\beta\in[0,1]$ at $\kappa=\gamma=0$,

$$
 \frac{E_1}{H}=\beta+\frac{1-q\alpha}{2K_q-2},\qquad
 \frac{E_2}{H}=\beta+\alpha\left(\frac{q}{2K_q-2}-\frac{2}{K_q}\right)-\frac{1}{2K_q-2}.
$$

We verify the exact uniform margin $\sigma_r=\frac{1}{r(2^{r+1}-2)}>0$ for every $r\ge3$ using $q\in\{4,5,\ldots,r+1\}$:

1. *Covering $\alpha\in[1/r,1]$ at $\beta=1$:* Since $E_1$ decreases and $E_2$ increases in $\alpha$ for $q\ge4$:
   - On $[1/3,1]$ choose $q=4$ ($2K_4-2=14$): at $\alpha=1/3$, $1-E_1/H=1/42$; at $\alpha=1$, $1-E_2/H=1/28$. Both exceed $\sigma_r$ for $r\ge3$ (with equality $\sigma_3=1/42$).
   - For each $q\in\{5,\ldots,r+1\}$, on $[1/(q-1),\,1/(q-2)]$ choose order $q$: at $\alpha=1/(q-1)$, $1-E_1/H=\frac{1}{(q-1)(2K_q-2)}\ge\sigma_r$; at $\alpha=1/(q-2)$, $1-E_2/H=\frac{2-4/K_q}{(q-2)(2K_q-2)}>\frac{1}{(q-1)(2K_q-2)}\ge\sigma_r$.
2. *Regime $\alpha\ge1/r$ and $0\le\beta\le1$:* Both $E_1/H$ and $E_2/H$ have slope $+1$ in $\beta$, so lowering $\beta$ from $1$ only increases both margins.
3. *Regime $0\le\alpha<1/r$ and $0\le\beta\le r\alpha$ (including $\alpha=\beta=0$):* Choose $q=r+1\ge4$. Substituting $\beta\le r\alpha$ gives

   $$
    \frac{E_1}{H}\le\frac{1}{2K_{r+1}-2}+\alpha\left(r-\frac{r+1}{2K_{r+1}-2}\right),\qquad
    \frac{E_2}{H}\le\alpha\left(r+\frac{r-3+4/K_{r+1}}{2K_{r+1}-2}\right)-\frac{1}{2K_{r+1}-2}.
   $$

   Since $2K_{r+1}-2=2^{r+1}-2\ge14$, both $\alpha$-coefficients are strictly positive, so both bounds are maximized at $(\alpha,\beta)=(1/r,1)$, where $1-E_1/H=\sigma_r$ and $1-E_2/H=\frac{3-4/K_{r+1}}{r(2^{r+1}-2)}>\sigma_r$.

Finally, $c$ enters $E_2$ divided by $2K_q-2\ge14$, so choosing $c<\sigma_r$ and then $\kappa>0$ small enough (with $\kappa<\min(c/d,\,1/(2r))$) keeps both perturbed exponents $\le(1-\sigma_r/2)H+O_{p,r}(1)$ across all competitor classes (for example, $\sigma_3=1/42$, $\sigma_4=1/120\approx0.00833$, $\sigma_5=1/310\approx0.00323$, $\sigma_6=1/756\approx0.00132$).

For $r=3$, $d=4$ a single order $q=4$ works with $\kappa=1/200$ and $c=1/8$. The smallest margin over all $(\alpha,\beta)$ is $0.0157$, attained by the competitor $(0,0,H)$ in $E_2$. The margin $1/42-1/200$ in $E_1$ is attained by the balanced competitor $(H/3,H/3,H/3)$.

**Main term.** $\sum_{\text{rows}}2\eta_0N_{\text{row}}=2p^v\delta'\sum_y\#\{\text{competitors}:S\in I^+\}$ (up to the constant factor $p/(p-1)$ from dropping $p\nmid m'$). For $u\le p^d$, $R_u=\{z\in(0,p)^r:S(z)\le u\}$ has volume $c_{r,d}u^{r/d}$, so the slab volume is bounded by $O_{r,d}(|I^+|)$. On each loss-vector grid $\Lambda=\prod_{j=1}^r p^{-h'_j}\mathbb Z_{>0}$ (with $\sum h'_j=H'$), associating to each $x\in R_u\cap\Lambda$ the interior-disjoint lower box $\prod_j[x_j-p^{-h'_j},x_j]\subset\overline{R_u}$ gives $\#(R_u\cap\Lambda)\le p^{H'}\operatorname{Vol}(R_u)$, while covering $R_u$ by upper boxes $\prod_j[x_j,x_j+p^{-h'_j}]$ based at $\Lambda_{\ge0}\cap\overline{R_u}$ and bounding boundary points with some $x_j=0$ gives $\#(R_u\cap\Lambda)\ge p^{H'}\operatorname{Vol}(R_u)-(p+1)^{r-1}\sum_{j=1}^r p^{H'-h'_j}$. Differencing at the two endpoints of $I^+$ gives slab count $\le p^{H'}(\operatorname{Vol}(R_{u_2})-\operatorname{Vol}(R_{u_1}))+(p+1)^{r-1}\sum_{j=1}^r p^{H'-h'_j}$. Summing $\sum_j p^{H'-h'_j}$ over all $\binom{H'+r-1}{r-1}$ loss vectors yields $r\sum_{m=0}^{H'}p^m\binom{m+r-2}{r-2}=O_{r,p}(H^{r-2}p^{H'})$. Hence the main term is $\le C\epsilon\sum_y p^v|I|+o(H^{r-1}p^H)\le C'\epsilon\cdot\#\text{centres}(I)$, with $C'$ independent of $\kappa$ and $I$.

## 6. Conclusion of the proof

For $\epsilon$ small, at least half of the centres in the middle half of $I$ are isolated once $H\ge H_0(I)$. Hence $|I\cap G_H|\ge c''\epsilon\kappa^{r-1}|I|$ for all large $H$, with $c''$ independent of $I$. Lemma 2 makes every level set of $M_r$ null, and the reduction of Section 1 proves Theorem C3. $\square$

## 7. Corrections to the proposed strategy

- **The anchor loss must be small.** Rows number about $p^k$ anchors times $p^{H'-v'}$ coarse competitors, so the exponential-sum saving must beat $p^{k}$. Anchors with $v\in[0.55H,0.7H]$, that is $k\ge0.3H$, give $E_1>H$ at balanced competitors. Taking $k\le\kappa H$ with $\kappa$ fixed and small, below $1/42$ for $r=3$, still leaves $\Theta(\kappa^{r-1}H^{r-1}p^H)$ centres. The measure at level $H$ is then $\asymp\epsilon\kappa^{r-1}$: constant, as the brief predicted.
- **The test must be organised by row.** For each row, the centre's fine lattice is absorbed into a mod-1 test and the competitor's fine coordinate is summed. Summing over one coordinate with all others fixed and without a mod-1 lattice fails for balanced competitors.
- **Exact coincidences $B=0$ occur.** Balanced anchors admit them, as in $59^4+158^4=133^4+134^4$. They are excluded by dominance together with the divisor bound. No Heath-Brown-type surface bound is needed.
- **Degenerate rows.** Separating $|B|\ge p^{-dg}$ for $B\ne0$ handles small $|B|$. It needs $\kappa<c/d$.
- **The derivative order is capped.** The upper bound on $f_B^{(q)}$ needs $q\le d$, which holds since $q\le r+1\le d$. The transfer independently needs $d\ge r+1$. The case $d=r$ (for example cubes on $tk^3$) remains open.
- **Edge cases.** For $p=3\le r$ one uses precision $sH+v_p(r!)+1$. Integer coordinates ($h=0$) are allowed for competitors. Permutations of the centre only occur in rows with $B=0$ and $w=y$. The case $s=1$ needs no change.

## 8. Scope and open questions

- **No rate.** As in OP-14, the argument proves density zero of failed shifts without an explicit rate.
- **Mixed orders.** Cubic forms in several distinct orders $X_a=C(b,p,a,d)$ are not covered. The weights $p^{a_1h_1+\cdots}$ break the symmetric jump $r!p^{sH}$, so the anchor choice must follow the smallest order. This is plausible but unchecked.
- **The case $d=r$** is open. The insertion count is no longer sparse.
- **Lean targets.** Arithmetic pieces that could be formalized: the coincidence peeling lemma, namely a unique top-loss coordinate under dominance via `padicValRat` of sums; the divisor bound $\#\{(a,c):a^d-c^d=M\}\le\tau(M)$; the finite jump identity for the truncated mass; and the polynomial recurrence for $\Phi_q$ as an identity in $\mathbb Z[d][X,B]$. The derivative tests and the measure theory remain written deductions.

## 9. Exact checks

`python -B scripts/phase20_normality.py` performs the following checks.

- **Derivatives.** It verifies $f_B^{(q)}=(d-1)Bx^{d-q}(x^d+B)^{1/d-q}\Phi_q$ against exact Taylor coefficients of $y^d=x^d+B$ for $d=4,\ldots,7$ and $q=2,\ldots,6$, together with the leading coefficients and $\Phi_4$.
- **Isolated measure.** For the cubic mass with $d=4$, $s=1$, at $p=3$ ($H\le6$) and $p=5$ ($H\le3$), it enumerates every relevant triple. With $\epsilon=1/4$, the isolated measure of all level-$H$ centres, normalized by $H^2/((H+1)(H+2))$, stays near $0.0019$–$0.0024$ of the window. The single primitive family decays like $H^{-2}$.
- **Flanks.** At sampled isolated centres, the flank residues of $M_3$, recomputed from all tuples through level $H+1$, differ by exactly $r!/(\text{stabilizer})\cdot p^H$, a nonzero value modulo $p^{H+1+v_p(6)}$.
- **Coincidences.** It confirms the balanced quartic coincidence. At $p=3$, losses up to 4, the nontrivial equal sums of two fourth powers include none against a dominant anchor.
- **Margins.** It finds positive exponent margins for $r=3,\ldots,8$.

These finite computations illustrate the mechanism. They do not prove the asymptotic estimates.

[Checker](../../scripts/phase20_normality.py)
