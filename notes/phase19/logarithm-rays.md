# Numerical visibility of the deterministic summands of log 2

Write $e_{d,j}=d2^j+j$ for $d$ odd and positive, $j\ge0$, and
$$
 Z_d=\sum_{j\ge0}2^{-e_{d,j}},\qquad L_d=Z_d/d.
$$
The ordinary Taylor series gives $\log2=\sum_{d\ {\rm odd}}L_d$. Phase 18 proved that every finite sum of these rows is deterministic for binary addition. Here the stronger question is exactly which rational scalings and combinations preserve **numerical** discrepancy uniformly in the translated input. [Phase 18 horizontal decomposition](../phase18/classical.md#theorem-f31-horizontal-dyadic-ray-decomposition-into-deterministic-summands)

**Coefficient criterion.** For any finite set $S$ of distinct odd indices and rationals $r,c_d$,
$$
 r+\sum_{d\in S}c_d Z_d\in K_2
 \quad\Longleftrightarrow\quad r\in\mathbb Z[1/2]\ \text{ and every }c_d\in\mathbb Z[1/2].
$$
Every one of these combinations is nevertheless a universal *normality*-preserving translation. Every nonempty combination with some nonzero row coefficient is transcendental.

For the numerical test, multiply by a fixed power of two to clear all radix-primary factors of the coefficient denominators. This preserves membership in $K_2$ in both directions. If the row weights are now integers, their contribution has vanishing mean circular displacement: the number of exponents through $N$ is $O_S(\log N)$, the absolute coefficients are bounded, and the total error on shifts at least $2\log_2 N$ before the next insertion is $O_S(N^{-2})$. The remaining rational belongs to $K_2$ exactly when dyadic.

In the other direction let $Q$ be the common odd denominator. At an event the shifted-prefix residue in $\mathbb Z/Q\mathbb Z$ is multiplied by a power of two from the preceding event and incremented by the integer numerator of the incoming weight. Late events on different rows are isolated by gaps proportional to their original positions. Indeed put $h_d=\lfloor\log_2 d\rfloor$ and $a_d=d/2^{h_d}\in[1,2)$. They are distinct because the indices are distinct and odd. In shell $k$ each row inserts at $a_d2^k+k-h_d$. The cyclic list of leading coordinates, continued with twice the first coordinate at the shell boundary, has strictly positive gaps. This gives a fixed lower bound on the ratio of each late gap to its right endpoint. At every insertion of a nonintegral weight either the preceding or following plateau has nonzero residue, since the increment is nonzero modulo $Q$. Every sample of that rational plateau is at distance at least $1/Q$ from zero on the circle. Away from the last $O(\log N)$ shifts the true tail is $o(1)$. Consequently the mean distance has positive upper limit at the ends of infinitely many such plateaus. This excludes $K_2$, irrespective of the constant $r$.

For determinism, all completed samples lie on a single finite rational grid after the fixed initial shifts, and the same tail estimate puts every empirical circle limit on that grid. All such invariant measures have entropy zero, so Rauzy applies. For transcendence clear *all* fixed denominators and remove the constant. After any sufficiently late event at $m$, the positive or negative tail is asymptotic to the very next nonzero term: its coefficient is from a fixed finite nonzero set and subsequent gaps tend to infinity. The rational partial sum has denominator dividing $2^m$, and for some fixed $\eta>0$ the error is $O(2^{-(1+\eta)m})$ by the proportional gaps. It is nonzero. Rational separation first excludes rationality, and then Ridout's restricted-denominator theorem excludes algebraic irrationality. [Restricted-denominator application](../phase18/principal.md#other-schedules-irrationality-and-transcendence) · [Numerical preserver classification](geometry.md#asymptotic-kernel-and-arithmetic-operations)

## Exact limiting discrepancies of an individual row

For $d=1$, $D_N(L_1)\to1$. For $d>1$ there is a finite rational calculation of both $D^-(L_d)$ and $D^+(L_d)$; in particular
$$
 1/d\le D^-(L_d)\le D^+(L_d)\le1-\min(1/6,1/d).
$$
Put $e_j=e_{d,j}$ and take $r_0=1$. At the insertion $e_j$ the rational shifted-prefix state is $r_j/d\bmod1$, where
$$
 r_{j+1}\equiv 2^{d2^j+1}r_j+1\pmod d .
$$
The multipliers are eventually periodic in $j$ since $d2^j+1$ is eventually periodic modulo $\operatorname{ord}_d(2)$. Thus the finite states $r_j$, augmented by the multiplier phase, become periodic. Let $\nu_j$ be uniform on the doubling cycle of $r_j/d$ and use the periodic tail extended in both directions. For each periodic phase $j$ put
$$
 B_j=\sum_{h\ge1}2^{-h}\nu_{j-h}.
$$
These are rational measures, computed with one finite geometric sum. The empirical cluster measures of $L_d$ are exactly
$$
 (1-v)B_j+v\nu_j,\qquad 0\le v\le1/2 ,
$$
over its periodic phases. To prove this, a full preceding gap at index $j-h$ has length $d2^{j-h}+1$ and the starting cutoff is $e_j=d2^j+j$. The weights converge in total variation to $2^{-h}$ since the sum of their rounding errors is $O(j/e_j)$ and an initial transient has bounded length. For $e_j\le N<e_{j+1}$ the unfinished part has weight $v=(N-e_j)/N$ ranging asymptotically over $[0,1/2]$. Each partial cycle has bounded unnormalized counting error on every arc. Summing these costs and discarding logarithmic neighborhoods before each late insertion costs $O_d((\log(2N))^2/N)$ in scalar discrepancy by arc enlargement, uniformly in the unfinished gap. Endpoints are obtained by limits. The empirical laws therefore have the indicated cluster set and the scalar discrepancies have its image under extreme discrepancy.

For a measure on this grid, its discrepancy is the maximum over consecutive cyclic groups of atoms of their total mass minus the distance along the group from its first to its last point; include groups of a single atom. This follows by shortening a positive-excess arc and taking endpoint limits. Along each displayed measure segment this is the maximum of finitely many rational affine functions of $v$. Their breakpoints and endpoints determine rational minima and maxima, giving an exact finite algorithm.

The lower bound follows by a gap of length $1/d$. Successive plateaus cannot both have state zero. At a shell boundary the weight of zero plateaus is at most $1/2+1/8+\cdots=2/3$; this follows by grouping consecutive pairs of past plateaus. Between boundaries it interpolates monotonically, so the same cap holds for every limit. Every nonzero cycle has at least two points since zero is the only binary fixed point. An arc shorter than $1/d$ therefore misses at least half of the nonzero-cycle mass, or at least $1/6$ of the total. Any longer arc costs at least $1/d$ in the concentration formula. This proves the upper bound.

**Odd part three.** Here $r_0=1$, $r_1=2$ and every subsequent $r_j=2$. All the cycles are $\{1/3,2/3\}$. Hence $D_N(L_3)=2/3+O((\log(2N))^2/N)$, so the largest numerical discrepancy change on adding this transcendental row tends to $1/3$. Multiplying the same row by three makes that change tend to zero. This is a concrete decomposition of the actual Taylor series into one dyadic row in $K_2$ and infinitely many individually deterministic rows outside it. The distributions of finite combinations do not establish a discrepancy bound for the entire logarithm.

**Odd part five.** Here $r_1=0,r_2=1$ and from $j=2$ the update is $r\mapsto2r+1\bmod5$. Thus zero recurs every fourth plateau and every nonzero state visits all four nonzero fifths. The possible weights $w$ of zero in the limiting measures fill $[1/15,8/15]$: the largest geometric boundary weight is $(1/2)/(1-2^{-4})=8/15$, and three successive nonzero shells halve it down to $1/15$. The other four grid points have equal mass $(1-w)/4$. When $w\ge1/5$, start an arc at zero; each additional included grid point costs $1/5$ in length and adds at most $1/5$ in mass. The maximal excess is $w$. When $w\le1/5$, the four consecutive nonzero points each have mass at least $1/5$, and give maximal excess $2/5-w$ (including zero cannot increase it beyond this). Hence $D^-(L_5)=1/5$ and $D^+(L_5)=8/15$. In both examples the extremal statements concern **the original summands** of $\log2$, with their factors $1/d$. [Exact cycle calculator](../../scripts/phase19_horizontal.py)
