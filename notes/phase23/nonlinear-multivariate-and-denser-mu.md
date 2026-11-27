# Nonlinear equality boundaries, several orders, and an all-prime number of exponent two

Let $b\ge2$, let $p\nmid b$ be an odd prime, let $t=\operatorname{ord}_p b$, and put
$$
 C_s(d)=\sum_{i\ge1}p^{-s v_p(i)}b^{-t i^d}.
$$
Here $s$ is a positive integer. Write $D_N(x;b)$ for interval discrepancy of the first $N$ shifts $\{b^n x\}$, $D^+=\limsup D_N$, and $K_b=\{x:D_N(x;b)\to1\}$. All-prime support means that each prime away from the radix eventually divides every reduced **shifted prefix** denominator of the specified expansion. The irrationality exponent $\mu(x)$ concerns rational approximations to the real number itself.

* **Paper proof, C1.** The square $C_s(2)^2$ is irrational when $s<(390/449)t\log b$. This includes every $s=1$, in particular $C(2,3,1,2)^2$. On an explicit positive relative proportion of square arrivals we determine the limiting distribution of the fractional innovation, for both splitting types of $p$. Over any subpower number of consecutive fractional arrivals the net change of the actual arrival phase typically has denominator $Y^{s+o(1)}$ at positions of size $Y$.
* **Paper proof, C1–C2.** At density one of starts, the exact jumps and every reduced prefix denominator throughout a packet of length $\lfloor\beta\log_b N\rfloor$, for any fixed $0<\beta<s$, admit every word on that packet when the initial numerator varies. This includes the cubic $C_1(3)^3$ for $(b,p)=(2,3)$, and allows arbitrarily many intervening arrivals.
* **Paper proof, C3.** The effective discrepancy exponent $d/(d-1)$ in $\log\log N$ holds for distinct orders and arbitrary rational polynomials of degree $r<d$, including tied maximal weighted degrees. It also holds with growing auxiliary support under the order budget in §4.
* **Paper proof, C4.** A doubling schedule with an odd pole prime admits polynomial normality in every degree, all-prime support, and $\mu=2$ simultaneously. Both an oscillating schedule and a positive series with positions $n_j\asymp j\sqrt{\log j}$, $n_{j+1}/n_j\to1$, have the same three properties. The latter uses exact regrouping. For ordinary truncation separation, the best exponent certifiable by distinct-prefix truncation separation is at least $(3+\sqrt5)/2$ for every schedule, with equality at geometric ratio $(3+\sqrt5)/2$.

[Exact checks](../../scripts/phase23_nonlinear_short_orbits.py) · [Weighted peeling and Theorem M](../phase21/multivariate-and-dense-allprime.md) · [Averaged isolation and Theorem Q](../phase21/nonlinear-boundary.md) · [Retirement and the equality boundary](../phase22/nonlinear-equality-boundary.md) · [Short orbits and truncation separation](../phase22/short-orbits-and-irrationality.md)

## 1. Squares at the equality boundary

**Theorem 1 (Paper proof, with an external gap theorem).** If $s<(390/449)t\log b$, then $C_s(2)^2$ is irrational. Consequently its expansion has infinitely many digit transitions and is not eventually periodic.

Write $c(m)=\sum_{i^2+j^2=m,\ i,j\ge1}p^{-s(v_p(i)+v_p(j))}$. At position $tM$ the shifted prefix has denominator dividing $p^{2s\lfloor\log_p\sqrt M\rfloor}\le M^s$. If $C_s(2)^2=A/Q$, its strictly positive shifted tail is therefore at least $1/(QM^s)$, including at a shift with integral prefix. Let $M,M+g$ be consecutive sums of two squares allowing zero coordinates. The bound $c(m)\le r_2(m)\le4\tau(m)\ll_\epsilon m^\epsilon$ also covers the case that an endpoint has only a zero-coordinate representation. Thus the shifted tail is
$$
 \ll_{\epsilon,b,t} b^{-tg}(M+g)^\epsilon .
$$
There are infinitely many such gaps between positive integers represented as sums of two squares (zero coordinates allowed) with $g\ge(390/449-o(1))\log M$ (natural logarithm), by Dietmann, Elsholtz, Kalmynin, Konyagin and Maynard. Consecutive squares give $M+g\ll M$. Choosing $\epsilon$ smaller than the strict margin contradicts the lower bound. Finally $b^t\ge p+1\ge4$, and $\log 4>449/390$ (for instance $\log 2>2/3$ by the midpoint bound for the integral of $1/x$ on $[1,2]$). The proof uses rare long gaps, so no positive transition density follows. [External input, Theorem 1 (accepted manuscript)](https://doi.org/10.1093/imrn/rnac130)

Write $z_H(m)=\sum_{\ell>H}p^{-s(\ell-H)}$ over the ordered pairs at $m$ of level $\ell=v_p(i)+v_p(j)$. The integral-coefficient series $X_H$ and the series $Z_H$ with coefficients $z_H(m)$ satisfy $p^{sH} C_s(2)^2=X_H+Z_H$. For fixed $H$, the Phase 22 result gives $|D_N(p^{sH}C_s(2)^2)-D_N(Z_H)|\ll_{b,p,s}(\log\log N+H)/\sqrt{\log N}$, so $D_N(p^{sH}C_s(2)^2)$ and $D_N(Z_H)$ agree to that order.

**Theorem 2 (Paper proof).** Set $k=\lceil(H+1)/2\rceil$, $D=p^{s(2k-H)}$, $a=\operatorname{ord}_D 2$. Let $F$ consist of squarefree sums of two squares $n>1$ with $(n/p)=-1$. At $m=p^{2k}n$,
$$
 z_H(m)=2^{\omega_1(n)}/D,\qquad
 \omega_1(n)=\#\{\ell\mid n:\ell\equiv1\bmod4\}.
$$
As $n\le Y$ ranges over $F$, the fractional parts are asymptotically uniform on the $a$ residues $2^j/D\bmod1$. This describes the innovation $y_{i+1}-b^{g_i}y_i\bmod1$, where $g_i$ is the gap in radix shifts. The ordinary difference $y_{i+1}-y_i\bmod1$ also contains $(b^{g_i}-1)y_i$.

To prove the formula, put $u=\min(v_p(i),v_p(j))$ in any representation. Necessarily $u\le k$. If $u<k$, division by $p^{2u}$ gives a primitive pair modulo $p$ whose squares sum to zero. Both entries must be units. Its level is $2u\le H$, so it retires, even when $p\equiv1\bmod4$. For $u=k$, the nonsquare condition on $n$ forces two units, and precisely the rescaled representations of $n$ survive. The two-square formula gives their ordered positive count $2^{\omega_1(n)}$, since squarefree $n>1$ is not a square. For $p\equiv3\bmod4$ the first case cannot occur.

Here are details of the counting input. On squarefree integers prime to $p$ with no prime factor $3\bmod4$, weight $n$ by $z^{\omega_1(n)}$, for an $a$-th root of unity $z$. The Euler product for its Dirichlet series in the complex variable $\sigma$ has linear prime terms $z\,1_{\ell=1\bmod4}\ell^{-\sigma}$ away from $2p$. It factors as $(\zeta(\sigma)L(\sigma,\chi_{-4}))^{z/2}$ times a residual Euler factor converging absolutely for $\Re\sigma>1/2$ (with the terms of order $\ell^{-2\sigma}$ absolutely summable). The Legendre twist has first-order factors $L(\sigma,\chi_p)^{z/2} L(\sigma,\chi_p\chi_{-4})^{z/2}$, both characters nonprincipal. The factor at 2 and the omitted factor at $p$ are finite corrections. Selberg–Delange gives a positive main term of order $Y/\sqrt{\log Y}$ for the untwisted $z=1$, $o(Y/\sqrt{\log Y})$ for untwisted $z\ne1$ since $\Re z<1$, and the same little-oh for every twist (zeta exponent zero). Taking half the difference imposes $(n/p)=-1$. Finite Fourier inversion proves the assertion. This uses the same external Selberg–Delange theorem as Phase 22 Proposition B″. In particular, for every odd $p$, the total number of fractional arrivals is $\asymp_H Y/\sqrt{\log Y}$, by Landau's upper bound. The distribution just proved is restricted to $p^{2k}F$.

## 2. Packets of successive arrivals, including the cubic

**Aggregate denominator law for squares (Paper proof).** Fix $H$. Enumerate all fractional arrivals of $Z_H$ by their unscaled positions $m_i$; write $y_i$ for the rational phase of its shifted prefix at $tm_i$ and $e_i=\log_p\operatorname{den}(y_i)$. Take any integer $M=M(Y)\ge1$ with $\log M=o(\log Y)$. For a relative proportion tending to one of the starts $Y/2\le m_i\le Y$, simultaneously for $1\le j\le M$,
$$
 \log_p\operatorname{den}(y_{i+j}-y_i)
 =e_i-v_p(b^t-1)-v_p(m_{i+j}-m_i).
 \tag{A}
$$
In particular $\log\operatorname{den}(y_{i+j}-y_i)/\log Y\to s$ in relative density, uniformly in this range. The law concerns the actual numerators propagated through the packet and both splitting types of $p$.

Here is why the pole estimate can be sampled at arrivals, which have zero ordinary density. Theorem 2 gives $\gg_H Y/\sqrt{\log Y}$ arrivals in the dyadic interval, by subtracting its asymptotics at the endpoints. For fixed $L$, the bad frozen set in each normalized shell for the square has finitely many component intervals and total length $O((\log L)^{-2})$ by Phase 21 Theorem Q at $d=r=2$. On each other cell $e_i\ge s\log_p Y-O_{H,L}(1)$ by freezing and fixed-depth retirement. The relevant shifts meet only $O_{p}(1)$ shells. Landau's two-square asymptotic bounds the count of all square-sum positions in the bad cells by
$$
 O((\log L)^{-2}Y/\sqrt{\log Y})+o_L(Y/\sqrt{\log Y}).
$$
Indeed in the position variable the total cell length is $O(Y(\log L)^{-2})$; differencing the summatory function at their endpoints in $[Y/2,Y]$ gives a uniform absolute little-oh for each fixed cell. Take $Y\to\infty$, then $L\to\infty$. Together with the elementary denominator upper bound $Y^s$, this gives $e_i/\log_p Y\to s$ in relative density, now at the *fractional arrivals*.

Fix small $\delta>0$ with $3\delta<s$. Omit the last $M$ starts before $Y$. Spans $m_{i+M}-m_i>Y^\delta$ cost at most $M Y^{1-\delta}$ starts by telescoping. Through $Y$ there are $O(Y^{1-\delta/s}(1+\log Y))$ positions with innovation denominator at least $Y^\delta$, by the valuation-vector count below, and each costs at most $M$ starts. Both costs are negligible on the arrival counting scale. For the other starts the propagated innovation $y_{i+j}-b^{t(m_{i+j}-m_i)}y_i\bmod1$ has denominator below $Y^\delta$, since the denominators are nested prime powers. The term $(b^{t(m_{i+j}-m_i)}-1)y_i$ has pole exponent exactly $e_i-v_p(b^t-1)-v_p(m_{i+j}-m_i)$ by LTE. With relative probability tending to one this is bigger than $\delta\log_p Y$, so the pole survives without cancellation. This proves (A); taking arbitrarily small fixed $\delta$ gives the limiting exponent. A denominator tending to infinity does not bound the distance of a phase change from zero on the real circle.

Use $r=d=2$ or $3$. Let $c_j$ denote the full convolution coefficient at shift $j$ (zero off the schedule), let $R_n=\sum_{i\le n}c_i b^{n-i}$, and let $T_n=\sum_{i>n}c_i b^{n-i}$. Then $R_{n+1}=bR_n+c_{n+1}$, $T_{n+1}=bT_n-c_{n+1}$. For a packet of $B$ shifts the cumulative innovation through $j\le B$ is exactly
$$
 V_j=\sum_{i=1}^j b^{j-i}c_{n+i},\qquad R_{n+j}=b^jR_n+V_j .
$$
In particular the exact distribution conditioned on a *specified* incoming numerator is a deterministic pushforward. Single-site jump frequencies do not specify that incoming numerator.

**Packet lemma (Paper proof).** Let $\operatorname{den}R_n=q=p^e>1$. Suppose each innovation in the next $B$ shifts belongs to $p^{1-e}\mathbb Z_{(p)}$ and has denominator a power of $p$. Replacing $R_n\bmod1$ by any unit numerator $a/q$ preserves every reduced denominator up through $n+B$. Keep even the true future tails $T_{n+j}$ fixed. If $2b^B\le q$, every base-$b$ word of length $B$ occurs in this family of continuations. Indeed all innovations have lower pole order, and
$$
 b^j a/q+V_j+T_{n+j}=b^j(a/q+T_n).
$$
The unit grid on the circle has maximum spacing $2/q$. Every translated half-open word cylinder of length $b^{-B}$ therefore contains a grid point. This holds also for $Z_H$ with its own coefficients and tails.

**Density of eligible starts (Paper proof).** Fix $0<\beta<s$, and put $B=\lfloor\beta\log_b N\rfloor$. On $[N/2,N]$, Phase 21 Proposition D gives $q\ge N^{\beta'}$ outside $o(N)$ shifts for each $\beta<\beta'<s$, since $rsJ=s\log_p N+O(1)$ there. This follows first with fixed depth defect and then by sending the defect to infinity. Fixed $H$ retirement divides the denominator by at most $p^{sH}$, which can be absorbed by taking a slightly larger intermediate exponent. An innovation with pole order at least $\log_p(N^{\beta'})$ requires a tuple of total level $h\ge (\beta'/s)\log_p N$. Through $2N$, a fixed vector of losses (here actual valuations) occurs at most $O(Np^{-h})$ times by bounding each coordinate by $(2N/t)^{1/d}$ and counting multiples. Summing the $O_r((1+h)^{r-1})$ valuation vectors and charging $B$ starts per occurrence costs $O(BN^{1-\beta'/s}(1+\log N)^{r-1})=o(N)$. Off these two exceptions the packet lemma applies. The argument does not require sparsity of sums of three cubes.

For the flagship cubic the residues modulo 9 give additional exact information. At $m\equiv\pm3\bmod9$ all three cubes are units with the same sign modulo 9, so $z_H(m)=0$ for every $H\ge0$. At $m\equiv\pm4$ there are no triples. At $m\equiv\pm2$ exactly one coordinate is divisible by 3, and its three possible slots supply a factor of 3 in each level count. Infinitely many arrivals nevertheless have unbounded fractional depth. At $m=3^{3a+1}$, AM–GM gives $ijk\le m/3=3^{3a}$, with equality only for $i=j=k=3^a$. All other triples have level at most $3a-1$ and occur in cyclic orbits of size three. For $3a>H$,
$$
 3^{3a-H}z_H(3^{3a+1})\equiv1\bmod9.
$$
Thus the reduced denominator there is exactly $3^{3a-H}$. Exact forced innovations at sparse positions coexist with the packet obstruction.

**Conditional cubic irrationality criterion.** If consecutive sums of three positive cubes $M,M+g$ have $\limsup g/\log M>2/(3\log2)$, the flagship cube is irrational. Indeed its shifted prefix denominator is at most $M$, whereas its tail is $O_\epsilon(2^{-2g}(M+g)^{1/3+\epsilon})$. To bound a coefficient at $m$, fix the first of $O(m^{1/3})$ indices. For the remaining equation $j^3+k^3=B>0$, $j+k$ divides $B$ and determines $jk$, giving at most $2\tau(B)$ ordered pairs. Also $M+g\ll M$ by using $i^3+1+1$. The claimed constant is $(1+1/3)/(2\log2)$. As in Theorem 1 the positive tail contradicts the rational lower bound $1/(QM)$ on the indicated subsequence. Ghidelli's unconditional theorem supplies gaps of order at least $\sqrt{\log N}/(\log\log N)^2$ up to $N$ between sums of three nonnegative cubes (a run of non-values of the nonnegative form is a fortiori a run of non-values of the positive form). Its stated bound does not supply the logarithmic constant in this criterion. [External input, Ghidelli](https://doi.org/10.1112/jlms.12312)

**Conditional.** For squares, an estimate on the *actual* incoming numerators can close the discrepancy question. For example divide a prefix into consecutive packets, write $\lambda_n=\{R_n+T_n\}$ at each packet start, and let $m_n$ be its length. If for some fixed $\epsilon,\eta>0$, every sufficiently large prefix and every circle arc $I$ of length $\epsilon$ satisfy
$$
 \sum_{\rm packets}\#\{0\le j<m_n:\{b^j\lambda_n\}\notin I\}\ge\eta N ,
$$
then $D^+\le1-\min(\epsilon,\eta)$ by the concentration form of discrepancy. One can use $R_{n+j}$ alone for squares with an arbitrarily small fixed enlargement of the tested arc and an $o(N)$ exceptional set, by Phase 22 Proposition M. For cubes one must also control the tails, or include them as in the display. The packet lemma shows why even exact innovations and denominators over a logarithmic window cannot furnish this input uniformly in the incoming numerator.

**Open.** The full jump histogram and actual asymptotic digit-transition frequencies, disjunctivity, and $D^+<1$ for the named square and cube are unresolved here. Irrationality of the flagship cube and of squares outside Theorem 1's parameter range is also unresolved here. The obstruction changes an incoming numerator locally. It makes no assertion that the alternative numerators occur globally in the given series.

## 3. Effective averaged isolation for several orders

**Theorem 3 (Paper proof).** Take distinct positive integers $s_1<\cdots<s_m$, $X_a=C_{s_a}(d)$, and a nonconstant rational polynomial $P$ of total degree $r<d$. Then
$$
 D_N(P(X_1,\ldots,X_m);b)\ll_{P,b,p,d,\mathbf s}(\log\log N)^{-d/(d-1)} .
$$
If the maximal weighted degree occurs only in a linear term, one has $D_N\ll N^{-\eta}$ for some $\eta>0$. In particular this holds for every nonconstant linear form.

Write $b^c P=Y/D$, $Y=\sum A_\nu X^\nu$ integral, $D>0$ coprime to $b$, and absorb the fixed shift $c$ at the end. Put $S=\max s\cdot\nu$ and let $T$ be the maximizers. For $n=tp^{dJ}u,\ 1\le u<p^d$, normalize the *unshifted* prefix of $Y$ by $p^{SJ}$. A coordinate $i=p^J z$ has $z=a/p^h\in(0,p)$, $p\nmid a$, $0\le h\le J$. Each term has valuation at least $(S-s\cdot\nu)J+\sum s_i h_i$. If
$$
 J\ge\max\{L,\lceil L/s_1\rceil+\lceil L/d\rceil\},
$$
all lower weighted degrees vanish modulo $p^L$, even for a weight gap of one. *(Phase 21 erratum: the freezing display of Phase 21 Theorem M stated only $J\ge\lceil L/s_1+L/d\rceil$, which omits $J\ge L$ and fails at a weight gap of one, as verified by the script's fixture at $L=2,J=1,u=1$. This is harmless for qualitative Theorem M where $L$ is fixed and $J\to\infty$, and is repaired by the display above for the effective rate.)* For a surviving tuple $h_i<L/s_1$, and $v_p(b^{ti^d}-1)=v_p(b^t-1)+d(J-h_i)\ge L$. Thus the normalized residue is the weighted mass $M(u)=\sum_{\nu\in T} A_\nu\sum_{\sum z_i^d\le u}p^{\sum s_i h_i}\bmod p^L$ on the unrestricted loss grids. Division by $D$ changes the depth by a fixed amount. A single linear maximizer gives, after removing its coefficient, residue $\lfloor u^{1/d}\rfloor\in[1,p-1]$ modulo $p$.

For the nonlinear case we prove, uniformly in $w\in\mathbb Z_p$,
$$
 |\{u\in[1,p^d):M(u)\equiv w\bmod p^L\}|\ll(\log L)^{-d/(d-1)}. \tag{1}
$$
Take the lexicographically least sorted order list among $T$, smallest order $s_*$, multiplicity $l$ of $s_*$, and its target monomial $\nu_*$, as in Theorem M. Every tied list has entries at least $s_*$ and at most $l$ copies of it. No two tied lists are proper prefixes. Fix the higher-order coordinates and pair their ascending orders with descending bounded losses $g_j$, with the sequential numerator avoidance of Theorem M §2. Its existence uses the divisor bound for the finitely many already chosen smaller losses. For the remaining $l-1$ free anchor losses choose boxes of length $\asymp H$, each loss $\ge\lambda H$, each larger than $6s_m$ times the sum of the preceding losses plus the fixed precision constant, and all together with the bounded losses of sum $k\le\kappa H$. Such boxes exist for any sufficiently small fixed $\kappa>0$ by choosing $\lambda>0$ sufficiently small. For $l=1$ there are no such boxes and $k$ is fixed. The last loss is $v=H-k$. The anchors have coordinates in $(0,(2r)^{-1/d}]$; the last coordinate is determined up to its grid choice by the target interval. The minimal weight is $s_*H+c_g$ with $c_g$ fixed. Put
$$
 \pi_H=s_*H+c_g+1+v_p(A_{\nu_*}\textstyle\prod_a\nu_{*,a}!),\quad
 V=H^{l-1}p^H,\qquad \delta=\epsilon/V .
$$
All relevant competitors have unweighted loss $H'\le H+C$ for a fixed $C$. A centre isolated from other relevant sums has a nonzero jump modulo $p^{\pi_H}$. The surviving assignment of orders to the descending losses has multiplicity $\prod_a\nu_{*,a}!$; any other assignment has a weight increase exceeding the fixed precision offset. The following union-of-intervals estimate gives a uniform replacement for the Lebesgue-point step in Theorem M.

**Weighted isolation estimate.** Fix the parameter order: choose small $c>0$ for the coarse-difference cutoff, then $\kappa\in(0,\min(c/d,1/(2(s_*+1)),1/(s_m+2)))$ and $\lambda>0$ small enough for the ordered free-loss boxes, then $\mu_0\in(0,\min(1/d,1/(2r)))$ strictly smaller than $\lambda/3$, $1/(2(s_*+1))-\kappa$, and the GF-11 / Lemma I row margins ($1/[r(2^{r+1}-2)]$ for $r\ge3$, $1/12$ for $r=2$), and finally $A,H_*,\epsilon_0>0$. Then for $H\ge H_*$, $p^{-\mu_0 H/8}\le\epsilon\le\epsilon_0$, $0<\tau\le1$, and a union $E$ of $J_E\ge1$ intervals in $[1,p^d)$, the count of candidate centres in $E$ is at least $A^{-1}|E|V-AJ_EH^Ap^{\kappa H}$. The count that must be rejected for collisions is at most
$$
 A\epsilon(\tau^{1-d}|E|+\tau)V + A J_E H^A p^{(1-\mu_0)H}. \tag{2}
$$
Count centres initially as tuples in the prescribed ordered loss boxes. After removing collisions the remaining centres are distinct.

For the first bound, each anchor gives $\gg |E|p^v-O(J_E)$ choices by the derivative upper bound $dp^{d-1}$ and the unit-grid count. Per free loss vector there are $\asymp p^{k-\sum g_j}$ anchors, and there are $\asymp H^{l-1}$ vectors. This includes $l=1$.

For (2), here are the adaptations to the row estimates of [GF-11 §5](../phase20/cubic-power-schedule.md) and [Lemma I](../phase21/nonlinear-boundary.md) (whose explicit Titchmarsh 5.13 row-margin parameters carry over unchanged under $H'\le H+C$, $v'\ge H'/r$, and $q\le r+1\le d$; for manuscript publication these should be packaged as a standalone multivariate Lemma I). They account separately for the number of slots in a competitor and the number of minimal-order slots in the centre.

1. With largest competitor loss $v'$, write the coarse power-sum difference as $B$. For $B=0$ rational spacing forces equality of the fine coordinates because $C_d\delta<p^{-H-C}$, by choosing $\epsilon_0$ small. The fine coordinate must have order $s_*$, since $v>(s_m+1)k+O(1)$ for small $\kappa$. Remove its weight. At a free loss $h$, the weight remaining is at most $s_*h+s_m\sum_{\rm earlier} h_i+O(1)$. The unweighted loss is $<3h/2$; equality of coarse power sums then forces a unique loss $h$ by valuation. A larger order on it exceeds budget. If its numerator differs, fixing the smaller coordinates leaves a nonzero equation $a^d-c^d=M_0$ with $O_{\epsilon_{\rm div}}(p^{\epsilon_{\rm div} d h})$ solutions. Relative to the $p^h$ numerator choices, the extra choices for the competitor's smaller losses cost at most $p^{h/2+O(1)}H^{O(r)}$. This loses at least $p^{h/3}$ with $\epsilon_{\rm div}\le1/(6d)$. A matching numerator peels. Once all $l$ minimal slots match, lexicographic minimality forces the next remaining order to be at least the target order. The bounded-loss choices in Theorem M force equality successively: at $g_j$ the remaining loss is $<2g_j$, a larger order exceeds budget, and the chosen numerator excludes every nonzero $a_j^d-c^d$ from the smaller coordinates. Positivity precludes unpaired leftover slots. Thus exact coincidences off the prescribed assignments cost $O(H^{O(r)}p^{H-\lambda H/3})$, or zero if there are no free losses. A degree-one competitor in a nonlinear tie has order $>s_*$; it costs $O(H^{O(r)}p^{(\kappa+s_*/(s_*+1))H})$ even charging once per anchor, so take $\kappa<1/(2(s_*+1))$.
2. For other competitors $j\in[2,r]$, $H'/r\le v'\le H'\le H+C$. There are $O(H^{O(r)}p^{k+H'-v'})$ rows for given losses. A nonzero $|B|<p^{-cH}$ forces a competitor coarse coordinate of loss $>cH/d$; varying it over the permitted interval of length $O(p^{-cH/d})$ saves $p^{(c/d-\kappa)H}$ in the full count. For $|B|\ge p^{-cH}$ the same derivative of $(x^d+B)^{1/d}$ occurs as in GF-11. The removed small-$x$ and small-derivative-factor pieces cost $O(H^{O(r)}p^{(1-\kappa)H})$. Choose the row cutoff $\lceil p^k H^{l+1}/\epsilon\rceil$. For derivative order $q$ put $K_q=2^{q-1}$. Up to $O(\log H)$ and the extra $\log_p(1/\epsilon)/(2K_q-2)$ in the first term, the two error exponents are
   $$
   k+H'+(H-qv')/(2K_q-2),\qquad
   k+H'-2v'/K_q+(qv'-H+k+\gamma H)/(2K_q-2),
   $$
   with $\gamma=c+2\kappa(d(q-1)-q)$. The GF-11 margin $1/[r(2^{r+1}-2)]$ for $r\ge3$, and the Lemma I margin $1/12$ for $r=2$, apply because $H'\le H+O(1)$ and $v'\ge H'/r$. Here $q\le r+1\le d$. Our parameter order chooses $c$ small, then $\kappa<c/d$ small, then $\mu_0$ smaller than the resulting positive margins and the savings in step 1. Intersecting each row with $E^+$, the $O(\delta)$-enlargement of $E$, gives at most $J_E+O_r(H)$ pieces by monotonicity. The first derivative-test term sums linearly in the lengths, and the concave second term costs at most this piece count. Even bounding each piece by the full row bound costs only $J_E H^{O(r)}$. These errors fit the last term of (2).
3. The surviving main term is $O(\epsilon)$ times the weighted-budget **count** of competitor points in $E^+$, allowing non-unit numerators for the fine row grid. Indeed each anchor contributes a factor $O(\epsilon p^{-k}H^{1-l}+1/L_{\rm ET})$, which sums to $O(\epsilon)$ over all anchors. For any tied list the sum of $p^{H'}$ over its admissible loss vectors is $O(V)$. For $j_0\ge1$ minimal slots, fix the larger orders $o_i$ and losses $e_i$. Summing the $j_0$ minimal losses costs $O(H^{j_0-1}p^{H+C-\sum o_i e_i/s_*})$; multiply by $p^{\sum e_i}$ and sum a convergent product since every $o_i>s_*$. If $j_0=0$ the sum is exponentially smaller. This accounts for **all** lower multiplicities without dropping a merely $O(1/H)$ relative error.
4. Put $\tau'=\max(\tau,p^{-\mu_0 H})$, $g_0=H/(2r)$. Vectors of total loss $<H/2$ cost $O(H^{O(r)}p^{H/2})$. Otherwise there is a coordinate of loss $g\ge g_0$. If any such coordinate is $\ge\tau'$, fix the others and vary it. At most $p^g |E^+|/(d(\tau')^{d-1})+O(J_E)$ grid points qualify. Summing by step 3 bounds the main count by $O((\tau')^{1-d}|E^+| V)$, with error $O(J_E H^{O(r)}p^{H-g_0})$. If all large-loss coordinates are below $\tau'$, choose one of them. Its positive grid has at most $\tau' p^g$ such points, giving $O(\tau' V)$ globally. This treats fixed higher-order slots even when their translated power sum lies inside $E$ and the remaining-coordinate density is singular. Since $|E^+|\le |E|+O(J_E\delta)$, the enlargement costs $O(J_E p^{(d-1)\mu_0 H})$ after multiplying by $O(\epsilon)$. Shrinking $\mu_0<1/(2r)$ absorbs all errors in (2).

For completeness, iterate (2) on an outer interval cover of the set in (1), starting from $[1,p^d)$. For current length $x$, take $\tau=(x/p^d)^{1/d}$, $\epsilon=c_P x^{(d-1)/d}$ with $c_P$ small. The first term of (2) costs at most a quarter of the centre main term. Use levels starting at $H_0\asymp 1+\log\log L$ with sufficiently large constant, multiplying each time by an integer $\Gamma>4/\mu_0$. The preceding deletions have $O((j+1)H_{\rm prev}^{O(r)}p^{H_{\rm prev}})$ components, so the second term of (2) and the endpoint loss are $o(xV)$ while $x>(\log L)^{-d/(d-1)}$. This choice also gives $\epsilon\ge p^{-\mu_0 H/8}$. At each isolated centre one flank of length $\delta/2$ misses the target residue, as long as $\pi_H\le L$; disjointness loses at most $O(J_E)$ boundary flanks. The new length is $\le x(1-c'_P x^{(d-1)/d})$. Its inverse power $x^{-(d-1)/d}$ increases by a fixed positive amount. There are $\gg\log L$ available levels unless the stopping threshold is reached, proving (1). All parameter choices can be made by strict inequalities or finite searches as in the linked row bounds.

## 4. From the weighted mass to digits and auxiliary orders

Choose $L=\lfloor c_0\log N\rfloor$ with $c_0>0$ sufficiently small. All $n\ge\sqrt N$ are then frozen, $L\le (S/(8d))\log_p N$, and $O(\log N\,L^r p^{L/s_1})=o(N^{r/d})$. The latter bounds the total cell count in all shells. In a full or partial shell the shift grid has mesh $1/(tp^{dJ})$. Counting on its cells costs $O(1)$ per cell in addition to the full-shell failed measure times $tp^{dJ}$. The geometric shell sizes sum to $O(N)$, so (1) discards $O(N(\log L)^{-d/(d-1)})$ shifts. A linear top term needs no such discard. All retained shifted denominators have $p$-exponent in $[SJ-L-O_P(1),SJ+O_P(1)]$.

Allow now an auxiliary denominator $\mu_i$ at the coefficients of each $X_a$, with $\mu_i=\ell_j$ at increasing $i=k_j$ prime to $p$, and 1 otherwise; $\ell_j$ are the increasing primes away from $bp$. Write $\Lambda_K=\prod_{k_j\le K}\ell_j$. The numerator of each coefficient remains 1. At an auxiliary index the loss is $J$; its term among the maximizers vanishes modulo $p^L$ because $s_1J\ge L$. At a nonmaximizer the prior weight-gap estimate suffices. Each prime $\ell_j$ occurs in exactly one coefficient of each coordinate and survives in its shifted prefixes. The top $p$-valuation in a single coordinate is also exact on late shells: the loss-zero terms have count between 1 and $p-1$ and all their unshifted units are 1 modulo $p$.

**Hybrid extension (Paper proof).** The rate of Theorem 3 holds if
$$
 \limsup_{K\to\infty}\frac{\log\operatorname{ord}_{\Lambda_K^r}(b)}{\log K}<d-r . \tag{3}
$$
The fixed-support case of Theorem 3 takes $\Lambda=1$. To prove both, cut at all insertion positions, cells and shell edges. There are $O(N^{r/d})$ pieces. Choose $\sigma>0$ so that the auxiliary stride (including the fixed part of $D$) is $O(N^{1-r/d-4\sigma})$ by (3), with $K=\lfloor(N/t)^{1/d}\rfloor$. Overlap with a fixed denominator costs a fixed factor by lifting orders from $\Lambda^r$ to $D'\Lambda^r$ for the prime-to-$bp$ part $D'$ of $D$ (one may multiply the order by $D'\varphi(D')$). Discard pieces shorter than $2N^{1-r/d-\sigma}$, the first $\sqrt N$ shifts, and a final $O_P(\log N)$ buffer per piece. Cut at $\sqrt N$ before the short-piece discard. Off buffers the real tail is $O(N^{-1})$: each coefficient at exponent $j$ is $O_P((j+1)^r)$ by tuple counting, so a sufficiently large buffer absorbs it.

On each retained piece of length $T'\gg N^{1-r/d-\sigma}$, Erdős–Turán up to $N^\xi$ reduces to the orbit of $hR$, with denominator $p^e Q$. Here $Q\mid D'\Lambda_K^r$ and $c_1\log N\le e\le c_2\log N$ uniformly for small $\xi>0$, since $v_p(h)\le \xi\log_p N$. Splitting at stride $\tau=\operatorname{lcm}(t,\operatorname{ord}_Q b)$ leaves $M_0=\lceil T'/\tau\rceil\gg N^{2\sigma}$. The principal-unit parameter is $v_p(b^\tau-1)=v_p(b^t-1)+v_p(\operatorname{ord}_Q b)=o(\log N)$ by Phase 22 Lemma D for increasing auxiliary primes, and is bounded for fixed support. Thus $p^{\theta e}\le M_0$ with fixed $\theta>0$, $v_p(b^\tau-1)<e$, and the $3\log_p(M_0)/16-1$ condition of Lemma A holds. Corollary B gives $O(T' N^{-\eta_1})$ for each harmonic. Summing and adding buffers gives a power saving apart from the failed cells, proving both assertions, including $d=r+1$.

For insertion budgets one can compute the precise auxiliary order without multiplying two overlapping costs. For odd $\ell\mid\Lambda$ put $w_\ell=v_\ell(b^{\operatorname{ord}_\ell b}-1)$; with $O_\Lambda=\operatorname{ord}_{\Lambda}b$ and $E=\prod_{\ell\mid\Lambda,\ \ell>2}\ell^{(r-w_\ell)_+}$, the order for odd $\Lambda$ is exactly $\operatorname{lcm}(O_\Lambda,E)=O_\Lambda E/\gcd(O_\Lambda,E)$ by LTE and CRT. For even $\Lambda$ take the additional lcm with $\operatorname{ord}_{2^r} b$. This can permit earlier specific introductions. In general it gives the previous sufficient scale $\log(t k_j^d)\ge((r-1)d/(d-r)+\epsilon)j\log j$ eventually for $r\ge2$, using the Phase 22 Lemma D bound $\log A_b(\ell_j)\ll_b j\log\log j$ and the prime number theorem. For $r=1$, the sufficient bound is $\log(t k_j^d)\ge(d/(d-1)+\epsilon)\log A_b(\ell_j)$. No universal strict improvement in the leading $j\log j$ order for $r\ge2$ follows merely by deleting the overlap, since every odd factor of $E$ must still divide the stride when the full auxiliary power occurs.

## 5. Which schedules admit uniform truncation separation?

**Proposition 4 (Paper proof).** Let $U_k$ be distinct increasing rational prefixes of $\xi$, $q_k=\operatorname{den}U_k$, $a_k=\log_b q_k$, $t_k=-\log_b(\xi-U_k)$, and $g_k=t_k-a_k-\log_b2$. For $x=\log_b Q$ the best distinct-prefix bound from the half-distance triangle inequality has exponent
$$
 1+\frac{\inf_{g_k\ge x}a_k+\log_b2}{x}.
$$
Indeed $g_k\ge x$ is exactly the gate $\xi-U_k\le1/(2Qq_k)$; for $A/Q\ne U_k$ the certified distance is $1/(2Qq_k)$. If $A/Q=U_k$ in reduced form its actual exponent is $t_k/a_k$. Thus taking the larger of the limsup of each type gives a valid upper bound for $\mu$. The displayed optimization is exact for the stipulated certificate, including arbitrary choices among multiple prefixes. No claim of optimality among Diophantine methods is implicit.

Suppose $a_k=n_k+o(n_k)$, $t_k=n_{k+1}+o(n_{k+1})$, where $n_k$ are strictly increasing positive integers. For $\Lambda=\limsup n_{k+1}/n_k<\infty$ there is a uniform finite certificate **if and only if**
$$
 \liminf_{k\to\infty}\frac{\max_{i<k}(n_{i+1}-n_i)}{n_k}>0. \tag{4}
$$
Indeed the records of $g_i$ up to $k-1$ differ from the maximum gap up to $k-1$ by $o(n_k)$, uniformly by splitting off finitely many early terms. If the positive lower bound holds, gates are unbounded. At the first $k$ with $g_k\ge x$, one has $x>\max_{i<k}g_i\gg n_k$. Conversely if (4) fails choose $k\to\infty$ with preceding gate maximum $o(n_k)$. Choose $Q\to\infty$ with its log just above that maximum and still $o(n_k)$ (for example also require $\log_b Q\ge\sqrt{n_k}$). Every eligible prefix then has index at least $k$ and cost at least $(1-o(1))n_k$. If $\Lambda=\infty$, the prefixes themselves give unbounded approximation exponents, and exclude rationality by positive tails and rational separation. No finite conclusion then holds.

In particular ratios tending to one fail (4), since the preceding maximum gap is $o(n_k)$. Ratios bounded above and bounded away from one eventually satisfy it. Both outcomes occur with $\liminf=1<\limsup=2$. The positions $2^j,2^j+1$ have a preceding gap comparable to their size. For failure, concatenate the full integer intervals $[a_j,a_j^2]$, $a_1=2,\ a_{j+1}=2a_j^2$. At $a_j^2$ the preceding maximum gap is $O(a_j)$. The criterion concerns the positions, subject to the denominator and tail assumptions stated above.

For $1<\Lambda<\infty$ with unbounded gates, take $Q$ with log just above a record $g_i$. Eligible later prefixes cost $\ge(1-o(1))n_{i+1}$, while $g_i\le (1-1/\Lambda+o(1))n_{i+1}$. The distinct-prefix certificate therefore costs at least $1+\Lambda/(\Lambda-1)$ in the limsup. The equal-prefix exponents have limsup $\Lambda$. Even optimized across schedules, this two-case certificate costs at least $\max(\Lambda,1+\Lambda/(\Lambda-1))\ge(3+\sqrt5)/2$. Geometric positions with limiting ratio $(3+\sqrt5)/2$ attain it, since there $g_i\sim(\Lambda-1)n_i$. The next argument uses the actual residue of a rational determinant, which this certificate discards.

## 6. A determinant estimate at successive prefixes

For a reduced rational $u=a/q$ define
$$
 B(u)=\inf_{l\ge1,\ h/l\ne u} l^2|u-h/l|
     =\min_{\substack{l,L\ne0\\ L\equiv al\bmod q}}\frac{|lL|}{q}>0 .
$$
Both coordinates in the minimum are integers. Swapping the coordinates shows $B(a/q)=B(a^{-1}/q)$ for $q>1$, with inverse modulo $q$. For $q=1$ use the integer 0 as inverse representative. In all cases $B(u)\le1$.

**Lemma 5 (Paper proof).** Let $z=c/d_z\ne0$ in lowest terms, $d_z>0$, and $v=u+z/q^2$. Then
$$
 B(v)\ \ge\ \min\{|z|,B(u)/(2c^2)\}. \tag{5}
$$
For a fraction $h/l\ne v$, put $L=al-qh,\ w=l/q>0$; then $l^2|v-h/l|=w|L+zw|$. If $L=0$, $w$ is a positive integer. If $|L|\ge2|z|w$ the result is at least $w|L|/2\ge B(u)/2$. Otherwise $0<|L|<2|z|w$ and $w=m+(a^{-1}/q)L$ for an integer $m$. Since $w+L/z\ne0$, testing $B(a^{-1}/q)$ with denominator $|cL|$ gives
$$
 |w+Ld_z/c|\ge B(u)/(c^2 |L|).
$$
Multiplying by $w|z|$ yields (5). Large partial quotients of the new prefix are thus controlled even if a new prime prevents a literal integral continued-fraction fold (compare the classical folding lemma for $\sum u^{-2^k}$ of Shallit 1979 and van der Poorten–Shallit 1992).

## 7. All degrees, every off-radix prime, and exact exponent two

**Theorem 6 (Paper proof).** Fix any $b\ge2$ and any odd $p\nmid b$. At $n_k=2^k$, $k\ge1$, place the coefficient $c_k=u_k/(p^k\mu_k)$. At each square index $k=j^2$ put $\mu_k=\ell_j$, the $j$-th prime away from $bp$, and use $\mu_k=1$ elsewhere. Choose the least positive solution of
$$
 u_k\equiv \mu_k b^{2^k}\pmod {p^k},\qquad
 u_k\equiv1\pmod{\operatorname{rad}(b)\mu_k}.
$$
The resulting sum $W=\sum c_k b^{-2^k}$ is all-prime, $\mu(W)=2$, and every nonconstant $P(W)$, $P\in\mathbb Q[X]$, is base-$b$ normal, with $D_N\ll_P N^{-\eta_P}$. *(Compared with Phase 22 Theorem S, which attains $\mu=p\ge3$ on a Stoneham schedule, three mechanisms change: the twisted CRT numerators replace $t\mid n_k$, the anchored upper-set lemma replaces the Phase 13/14 periodic-mass input, and Lemma 5 replaces truncation separation, which could certify at best $\max(2,3)=3$ at ratio $2$.)*

There is also a denser version. Put $w_k=2^{k-\lceil\sqrt k\rceil}$. After $2^k$ insert a coefficient 1 at every odd offset in $[1,w_k]$ and at $w_k$ itself (once). The resulting $W'$ is all-prime, satisfies $\mu(W')=2$, and every nonconstant $P(W')$ is normal. Its consecutive position ratios have liminf 1 and limsup 2. Through $N$ the number of positions is $N^{1-o(1)}$ and their density tends to zero. Indeed even the preceding complete cluster has $\gg 2^{k-1-\lceil\sqrt{k-1}\rceil}$ positions for $2^k\le N<2^{k+1}$, while $\sum_{j\le k} w_j=o(2^k)$. The proof permits arbitrary subsets of integer offsets containing the endpoint; the stated choice gives a concrete count. Below, set $w_k=0$ for the first construction.

**Denominators and exponent.** CRT gives $0<c_k\le\operatorname{rad}(b)$, and $u_k$ is a unit at every prime dividing $bp\mu_k$. Put $D_k=p^k\prod_{j^2\le k}\ell_j$. Every shifted prefix from $2^k$ until $2^{k+1}$ has exact denominator $D_k$: the last distinguished term has a unique deepest $p$-pole, and each auxiliary prime occurs just once. At the endpoint $m_k=2^k+w_k$ the unshifted prefix $U_k$ has exact denominator $q_k=D_k b^{m_k}$, since the final coefficient is a unit at each prime of $b$ after clearing the off-radix denominator. In particular $\log D_k=O(k+\sqrt{k}\log(k+1))$.

Write $U_{k+1}=U_k+z_k/q_k^2$. The next cluster sums to $A/(p^{k+1}\mu_{k+1}b^{2^{k+1}+w_{k+1}})$ with positive integer $A\ll_b p^{k+1}\mu_{k+1} b^{w_{k+1}}$, by the geometric sum of the coefficient bounds. Since $2\cdot 2^k=2^{k+1}$, the numerator and denominator of reduced $z_k$ have logarithms $O_b(k+\log D_k+\log\mu_{k+1}+w_k+w_{k+1})=o(2^k)$. The bound also controls $\log^+(1/|z_k|)$. Formula (5) gives $\log(1/B(U_k))=o(2^k)$: a sum of $o(2^i)$ up to $k$ is $o(2^k)$ by a geometric tail split. Given any large $l$, choose the first $k$ with $2^k\ge4\log_b l$. Then $2^k<8\log_b l$, $q_k>l$, and
$$
 |U_k-h/l|\ge B(U_k)/l^2=l^{-2-o(1)},\qquad
 0<W^{(\prime)}-U_k\ll_b b^{-2^{k+1}}\ll l^{-8}.
$$
Here $W^{(\prime)}$ means the chosen construction. The first lower bound is uniform in $h$. Subtracting the tail excludes rationality (also test multiples of a hypothetical fixed denominator) and gives $\mu\le2$. Dirichlet's theorem gives the reverse inequality.

**Pole retention in any fixed degree $r$.** The odd pole prime is independent of the doubling ratio. For $2^K\le n<2^{K+1}$, reflect distinguished indices by $h_i=K-i$. The admissible region on the infinite lattice $\mathbb N_0^r$ is the upward-closed set
$$
 U=\{\mathbf h:\sum_i2^{-h_i}\le n/2^K\}.
$$
It contains $(\lceil\log_2 r\rceil,\ldots,\lceil\log_2 r\rceil)$ for every $n$. There is a uniform finite $L=L(r,p)$ for which $\sum_{\mathbf h\in U} p^{|\mathbf h|}\not\equiv0\bmod p^L$ for every upward-closed set containing this anchor. To see this, Dickson's lemma gives a finite nonempty list of minimal vectors. Inclusion–exclusion on their upper orthants writes the generating series as $F(x)/(1-x)^r$, where $F\in\mathbb Z[x]$ and $F(1)=1$ by the alternating sum over all nonempty subfamilies. Hence $F(p)\equiv1\bmod(p-1)$ is nonzero for $p\ge3$. Evaluation in $\mathbb Z_p$ is valid since $1-p$ is a unit. The anchored upper sets are closed in the compact product $\{0,1\}^{\mathbb N_0^r}$; the residue modulo $p^L$ depends only on $|\mathbf h|<L$. Compactness gives the uniform $L$; testing finite truncated upper sets also gives a terminating search for one.

Normalize the unshifted prefix of the $r$-th power by $p^{rK}$. For $|\mathbf h|<L$ all indices satisfy $i\ge K-L+1$; for $K\ge2L$ they are valid positive indices and $u_i b^{-2^i}/\mu_i\equiv1\bmod p^L$ by construction. Thus the surviving mass agrees with the upper-set sum modulo $p^L$. Every tuple using an integer filler, and every lower-degree term, has denominator depth at most $(r-1)K$. Consequently for any fixed degree-$r$ rational polynomial the shifted prefix has $p$-exponent $rK+O_P(1)$ at **every** sufficiently late shift. This permits a new prime at any prescribed square index without changing the relevant mass.

**Digit transfer.** For $K=\lfloor\log_2 N\rfloor$, all insertions through $N$ lie within intervals $[v,v+r w_K]$ around sums $v$ of at most $r$ distinguished positions. Include zero; there are $O_r((K+1)^r)$ intervals. Remove their union, early shifts $n<\sqrt N$, buffers $C_P\log N$ preceding each interval and the endpoint $N$, and remaining components shorter than $N^{1/3}$. Removing a final buffer before $N$ also protects a last incomplete run. The cost is
$$
 O_P\big(\sqrt N+(K+1)^r(1+r w_K+\log N+N^{1/3})\big)=o(N).
$$
Coefficient growth is polynomial in the exponent, uniformly by the bounded coefficients and tuple count, giving shifted tail $O(N^{-1})$ off buffers. For $W$ the discarded proportion is a power saving. On each retained run (starting at or above $\sqrt N$, so the shell index satisfies $K_0\ge\tfrac12\log_2 N$, with length $T'\ge N^{1/3}$), the complementary order $\tau$ is $N^{o(1)}$ since $\log\prod_{j^2\le K}\ell_j=O(\sqrt K\log(K+1))$, so $M_0=\lceil T'/\tau\rceil\ge N^{1/3-o(1)}$. The principal-unit valuation is $o(\log N)$ (even the log of that order is $o(\log N)$). For sufficiently small fixed $\xi>0$, the pole exponent $e$ after multiplication by any $h\le N^\xi$ satisfies $c_1\log N\le e\le c_2\log N$, so $p^{\theta e}\le M_0$ for a fixed $\theta>0$. Corollary B, Lemma A and Erdős–Turán (up to $N^\xi$) now give a power-saving discrepancy on each retained component as in §4. Adding the removed shifts proves normality, and proves the stated power rate for $W$. Polynomial normality in all degrees also implies transcendence of $W,W'$, since a polynomial relation with rational coefficients would yield the constant zero.

## 8. A positive series with consecutive ratios tending to one

**Theorem 7 (Paper proof).** Keep the distinguished terms $c_k b^{-2^k}$ of Theorem 6. Write $h_k$ for the largest power of two at most $\sqrt k$. In the shell $(2^k,2^{k+1}]$ add a coefficient 1 at the positive offsets $h_k,2h_k,\ldots,2^k$ from $2^k$, combining the endpoint with the next distinguished term. Call this positive series $V$. Its occupied positions $n_j$ satisfy
$$
 n_j\asymp j\sqrt{\log j},\qquad n_{j+1}/n_j\longrightarrow1 .
$$
Every off-radix prime persists in its shifted prefix denominators, $\mu(V)=2$, and every rational polynomial of positive degree evaluated at $V$ has $D_N\ll_P N^{-\eta_P}$.

Indeed the preceding complete shell alone provides $\gg2^k/\sqrt k$ occupied positions through any $N\in[2^k,2^{k+1})$. Summing $2^i/h_i$ up to $k$ gives the matching upper bound, by splitting at $k/2$; the largest gap on the shell is $h_k$. Integer insertions preserve the exact shifted denominators $D_k$. To see what prefix separation misses, set $\lambda_0=0$, $\lambda_k=1/(b^{h_k}-1)$ for $k\ge1$. Finite geometric summation gives the exact identities
$$
 \sum_{j=1}^{2^k/h_k}b^{-2^k-jh_k}
   =\lambda_k(b^{-2^k}-b^{-2^{k+1}}),\qquad
 V=\sum_{k\ge1}d_k b^{-2^k},\quad d_k=c_k+\lambda_k-\lambda_{k-1}.
$$
In particular the dense support and its original prefix denominators are features of a specified positive expansion; arithmetic control comes from its second expansion.

The two denominators of the correction divide $b^{h_k}-1$, since $h_{k-1}\mid h_k$. Their $p$-exponents are bounded by $a_0=v_p(b^t-1)$: when $t\mid h_k$, LTE gives $a_0+v_p(h_k/t)=a_0$, and otherwise the exponent is zero. In a reflected tuple the normalized unit $p^i b^{-2^i}d_i$ therefore equals 1 modulo $p^{i-a_0}$ for $i>a_0$. Early indices have fixed finite pole depths. For any sufficiently late shell and fixed precision $L$, tuples using an early index vanish after multiplication by $p^{rK}$ because they have a depth defect at least $K-O(1)$. All other tuples still vanish for loss $\ge L$ and agree with the upper-set mass for loss $<L$ once $K\ge2L+a_0$. The complementary denominator in a degree-$r$ prefix divides, up to the fixed polynomial denominator, the prime-to-$bp$ part of
$$
 \left((b^{h_K}-1)\prod_{j^2\le K}\ell_j\right)^r .
$$
Its logarithm is $O_{P,b}(\sqrt K\log(K+1))=o(K)$. The regrouped coefficients are bounded in absolute value and there are $O_P((1+\log N)^r)$ insertions through $N$. The proof of Theorem 6 for the unfilled doubling schedule applies, including the power saving.

For the exponent, let $\widetilde U_k=\sum_{i\le k}d_i b^{-2^i}$, $q_k=\operatorname{den}\widetilde U_k$. A common off-radix denominator is $E_k=D_k(b^{h_k}-1)$, with $\log E_k=O_b(k+\sqrt k\log(k+1))$. Put $A_k=E_k d_k$, an integer with $0<|A_k|\ll_b E_k$ for $k>a_0$ by the distinct $p$-depths. The numerator over $E_k b^{2^k}$ is congruent to $A_k\bmod b^{2^{k-1}}$. For all large $k$, each prime of $b$ has the same valuation in that numerator as in $A_k$, since $|A_k|\le\exp(O_b(k+\sqrt k\log(k+1)))$. Consequently $q_k/b^{2^k}$ is a rational of numerator and denominator at most $\exp(O_b(k+\sqrt k\log(k+1)))$: cancellation in the off-radix factor is at most $E_k$, and that in the radix factor at most $|A_k|$. In
$$
 \widetilde U_{k+1}-\widetilde U_k
 =z_k/q_k^2,\qquad z_k=d_{k+1}(q_k/b^{2^k})^2 ,
$$
both heights of the nonzero signed correction have logarithm $O_b(k+\sqrt k\log(k+1))$. Apply (5) from a sufficiently large fixed index. This gives $\log(1/B(\widetilde U_k))=O_b(k^2+k^{3/2}\log(k+1))=o(2^k)$. The absolute tail is $O_b(b^{-2^{k+1}})$. Choosing $2^k\in[4\log_b l,8\log_b l)$ again gives $q_k>l$ and $|V-h/l|\ge l^{-2-o(1)}$, proving $\mu(V)=2$.

For comparison, a raw positive prefix ending at an ordinary insertion $n_j$ has exact radix factor $b^{n_j}$, since its last coefficient is 1. At $n_j=2^k$ its regrouped final coefficient is $c_k-\lambda_{k-1}$; the same numerator argument gives $\log_b q=n_j+o(n_j)$. The positive raw tail begins at $n_{j+1}$ with coefficient at least 1 for all sufficiently late raw insertions (including the endpoint), so its negative base-$b$ log is $n_{j+1}+O_b(1)$. Thus (4) genuinely fails on these raw prefixes, while regrouping proves the optimal real exponent.

**Open.** These constructions do not determine $\mu$ for the specified polynomial or quasi-polynomial schedules of Theorems H and U. Their coefficients do not provide the geometric block identity used here. The distinction is between the obstruction to a certificate from a given sequence of prefixes and the irrationality exponent of its limit.

## 9. Exact verification and finite measurements

Run **python -B scripts/phase23_nonlinear_short_orbits.py**. The script uses integers and rational fractions throughout.

* **Finite measurement, actual arrivals.** With $H=0,b=2,s=1$ and unscaled $m\le4096$, the square has 643 fractional arrivals for $p=3$ and 479 for $p=5$. The flagship cube has 164. Testing spans of one through five fractional arrivals, the aggregate pole survives the computed innovation in respectively 1871, 1200 and 427 packets. The script checks the recurrence in every packet and the exact denominator whenever the strict pole inequality holds.
* **Finite measurement, selected square innovations.** For $n\le400$ in $F$, $H=1,s=1$, the counts indexed by the numerator modulo $D$ are $(1:9,2:29)$ for $p=3$ and $(1:1,2:30,4:1)$ for $p=5$. These small-range histograms are far from the uniform limit law (as expected, since convergence in $\omega_1$ occurs at scale $\log\log Y$) and are not evidence for that limiting law; the script independently counts ordered representations at the scaled positions, including all retired levels.
* **Finite measurement, digits.** Among the first 2048 binary digits of the flagship square there are 1044 ones and 1023 changes between adjacent digits. The flagship cube has 983 ones and 1100 changes. The denominator for both transition frequencies is 2047. An enclosing interval for the original series certifies each entire word before counting.
* **Finite certificates.** A packet with $q=81,b=2$ realizes all 32 length-five words with its innovations and future tail held fixed. A mixed-degree, tied-order fixture has normalized residues $2,41,15,15,60\bmod81$; separate fixtures check the weight-one deficit, the full freezing window, and different assignments of the higher orders. The exact order factorization is checked with overlapping factors, including the prime 2.
* **Finite certificates, exponent two.** The script verifies (5) on 1960 signed corrections (including $q=1$ and larger numerators) by independently minimizing over a complete residue system. It checks orthant inclusion–exclusion on 251 antichains at $p=3,5$, exact prefix denominators, explicit $z_k$ height bounds and maximum continued-fraction partial quotients in both constructions of Theorem 6, and direct convolutions against reflected residues. For Theorem 7 it checks the geometric regrouping, normalized units, explicit $z_k$ height bounds, direct convolutions $\widetilde V^2$ and $\widetilde V^3$ against the complementary denominator bound, and every displayed-series prefix denominator through shift 1023 in three different radices, including a case where $p\mid b^{h_k}-1$.
