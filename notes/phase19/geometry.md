# Extreme discrepancy as a translation distance

Fix $b\ge2$, use $Tz=bz\bmod1$ on the circle, and let $D_N(z)$ be the extreme interval discrepancy of $z,Tz,\ldots,T^{N-1}z$. Put $F_b=\{c:(b-1)c=0\bmod1\}$ and $d_N(x,y)=1-D_N(x-y)$ for $N\ge1$. Distance to the nearest integer is written $\|\cdot\|$.

## Finite distance, including its zero set

The sharp translation theorem gives an isometric description of the deficit:
$$
 d_N(x,y)=\max_u |D_N(u+x)-D_N(u+y)|.
$$
Use the finite theorem at $u+y$, and take $u=-y$ for equality. Thus symmetry, nonnegativity, the triangle inequality and translation invariance hold. The diagonal vanishes. For $N=1$ this is the zero pseudometric. [Sharp translation in Lean](../../NormalityChecker/SharpTranslation.lean)

For a circle sample with empirical law $\mu$, let $Q_\mu(l)$ be the supremum of its mass in an arc of length $l$. By complementation a deficit on a circle arc is the positive excess on its complement. Consequently
$$
 1-D(\mu)=\inf_{0\le l\le1}\{1-Q_\mu(l)+l\}.
$$
Arcs are half-open, with arbitrarily small enlargement allowed when taking the infimum. This is an exact use of the classical concentration function. For an empirical measure any arc missing at least one sample costs at least $1/N$. Any arc containing all samples has length at least the circle distance between any pair. At $N\ge2$, using the first two points for a lower bound, and rotating away the nearest fixed point for the upper bound, gives, with $z=x-y$,
$$
 \min(1/N,\|(b-1)z\|)\ \le\ d_N(x,y)\
 \le\frac{b^{N-1}-1}{b-1}\|(b-1)z\|.
$$
Indeed write $z=h+u$ with $(b-1)h$ integral and $|u|=\|(b-1)z\|/(b-1)$. Up to rotation the entire sample lies on a real segment of length $(b^{N-1}-1)|u|$. If the segment exceeds one the upper bound is automatic. Thus the finite quotient is the circle $\mathbb R/((b-1)^{-1}\mathbb Z)$ with its ordinary topology, identified with $\mathbb T$ by multiplication by $b-1$. More precisely $d_N(x,y)=(b^{N-1}-1)|u|$ when this quantity is smaller than $\min(1/2,1/N)$, by using the first and last points. The finite metric is locally linear on this quotient.

## Asymptotic kernel and arithmetic operations

Write $d^+=\limsup d_N$, and $M_N(w)=N^{-1}\sum_{n<N}\|b^n w\|$. The limsup preserves the pseudometric inequalities. Its algebraic quotient is $\mathbb R/K_b$, where
$$
 K_b=\{z:D_N(z)\longrightarrow1\}
     =F_b+\{w:M_N(w)\longrightarrow0\}
$$
with circle fixed points lifted to $\mathbb R$. Precisely these translations change numerical discrepancy by $o(1)$ for every input, uniformly over all inputs. The maximum formula also gives $d^+(x,y)=\max_u\limsup_N|D_N(u+x)-D_N(u+y)|$. The kernel is dense in the ordinary topology since it contains every radix-primary rational. The ordinary quotient topology is indiscrete since every nonempty open saturated set meets every dense coset and hence contains it. The quotient metric is different: a normal number divided by $b^j$ tends to zero as a real number and has $d^+$-distance one from zero for every $j$. [Phase 18 fixed-point classification](../phase18/translations.md#the-exact-worst-case-change)

**Universal scalar ring.** For a reduced rational $a/d$, $d>0$, the inclusion $(a/d)K_b\subseteq K_b$ holds exactly when every prime of $d$ divides $b$. Integer multiplication follows by the triangle inequality. Division by $b^j$ changes only a fixed initial portion of the shifted orbit; thus all of $\mathbb Z[1/b]$ acts. Conversely a rational is in $K_b$ exactly when its ultimately periodic orbit ends in a fixed point, equivalently its reduced denominator divides $b^j(b-1)$ for some $j$. Test the multiplier on $1/(b-1)\in K_b$. If $p\mid d$ and $p\nmid b$, the image has denominator valuation $v_p(b-1)+v_p(d)$, too large. This proves necessity even if the other prime factors of the denominator could cancel.

**Individual scalar test.** If $z\in K_b$ has limiting fixed point $c\in[0,1)$, let $k_n$ be a nearest integer to $b^nz-c$, breaking ties consistently. For reduced $a/d$, $(a/d)z\in K_b$ iff $z/d\in K_b$: use Bézout's identity with $d(z/d)=z$. The latter holds iff for some residue $r\bmod d$ the indices $k_n\equiv r\bmod d$ have density one and $(c+r)/d$ is fixed modulo one. Indeed the true samples of $z/d$ have vanishing mean circle distance from the finite grid samples $(c+(k_n\bmod d))/d$. Distinct points of this grid are separated. Concentration on a single fixed point is therefore equivalent to the stated single-residue condition. In fact if one residue has density one, the resulting point mass is invariant under $T$ by telescoping, so the fixed-point condition follows. In particular rational division of a numerical preserver can preserve normality of every normal input (by rational affine invariance and conjugation) while changing the numerical discrepancy of another input. This reduces the rational-scaling question for the Phase 17 Lambert and sparse classes whenever their residue data are available. [Rauzy and the numerical subclass](../phase18/translations.md)

**Powers of the radix.** Vanishing mean displacement is equivalent in bases $b$ and $b^h$. Restricting a density-one set to multiples of $h$ preserves density one in the subsequence. Conversely decompose into $h$ residue classes and use $\|b^j t\|\le b^j\|t\|$. Hence $K_b\subseteq K_{b^h}$, strictly if $h>1$, as witnessed by $1/(b^h-1)$. More generally $K_{a^r}\cap K_{a^s}=K_{a^{\gcd(r,s)}}$: the mean-zero subgroup is common to both, and its intersection with rational points of order coprime to $a$ is zero. Thus both limiting fixed points must coincide modulo one and have order dividing $\gcd(a^r-1,a^s-1)=a^{\gcd(r,s)}-1$. For unrelated radices invariance fails already on rationals: $1/4\in K_2$ and $1/4\notin K_3$. The rational-membership test above decides every such rational example. No classification of irrational simultaneous preservers in multiplicatively independent bases is used.

## Integer multiplication: quantitative bounds and an exact boundary spectrum

For $m\ge1$, writing $\alpha=D_N(x)$, one has
$$
 \max(0,1-m(1-\alpha))\le D_N(mx)\le\min(1,m\alpha).
$$
The lower bound is the pseudometric triangle inequality for $mx$ as a sum of $m$ copies. For the upper bound the inverse image of a half-open interval under multiplication by $m$ consists of $m$ disjoint arcs of total length equal to the interval length. The bounds apply to negative multipliers with $|m|$ by the symmetry of $d_N$. The factor $m$ in $d_N(mx,my)\le m d_N(x,y)$ is attained at small nonzero displacements for each $N\ge2$, by the local formula. The upper factor in $D_N(mx)\le mD_N(x)$ is sharp across radices: take $b=m+1$, $x=1/m^2$ and $m\mid N$. The first orbit is an equally spaced translated $m$-grid, since $(m+1)^n\equiv1+nm\bmod m^2$. Its image is a fixed point. At a fixed radix there are additional restrictions: $|D_N(b^j x)-D_N(x)|\le j/N$.

There is an exact classification on the boundary $D_N(mx)\to1$. Factor $m=m_0 m_b$ where $(m_0,b)=1$ and $m_b\mid b^j$ for some $j$. Then the set of attainable *limits* of $D_N(x)$ on this boundary is
$$
 [1/m_0,1].
$$
In fact $\liminf D_N(x)\ge1/m_0$. Since multiplication by $m_b$ and division by $m_b$ both preserve $K_b$, $m_0x\in K_b$. Its samples concentrate at some $c\in F_b$, so the samples of $x$ concentrate in arbitrarily small neighborhoods of the $m_0$ evenly spaced solutions of $m_0u=c$. An interval strictly inside a gap of this grid has vanishing limiting mass. Exhausting the gap gives the bound, including when $m_0=1$.

For sufficiency use the cubic schedule of Phase 18. Assign finite rational cycle types whose time-averaged law is $\theta\delta_0+(1-\theta)U_{m_0}$, where $U_{m_0}$ is uniform on the grid $j/m_0$ and $0\le\theta\le1$. Multiplication by $b$ permutes this grid and its cycle weights in $U_{m_0}$ are their cardinalities divided by $m_0$. All these target states map to zero under $m$. The exact rational-state recurrence supplies $x$ with positive coefficients, bounded count error on each finite cycle up to one unfinished period, and $O_{b,m}(N^{-1/3})$ total discrepancy error by cubic scheduling. The tail at good shifts of $mx$ is at most $m$ times that at $x$, with the same exceptional positions. The mixture has discrepancy exactly $\theta+(1-\theta)/m_0$: convexity and $D(U_{m_0})=1/m_0$ give the upper bound, and shrinking arcs at zero detect that much mass. This ranges over the whole claimed interval. Computable weights give computable examples by rational approximation in the scheduler. [Cubic finite-cycle construction](../phase18/programming.md#b4-periodic-components-and-irregular-limits)

## An explicit inverse bound for dilation

Finite discrepancies of $x$ and $mx$ also satisfy a restriction close to the normal endpoint which cannot be obtained just from the two elementary linear bounds. For every $h,N,m\ge1$ put $\beta=D_N(mx)$. Then
$$
 D_N(x)\ \le\ \frac{h-1}{2N}
       +\frac{m}{\sqrt h}\sqrt{\tfrac14+4/(b-1)}
       +\left(m+2\sum_{j=0}^{h-1} b^j\right)\beta .
$$
In particular along all prefixes with $\beta\to0$ this gives the quantitative inverse transfer $D_N(x)\ll_{b,m}(\log(2/\beta))^{-1/2}+\log(2N)/N$. This upper estimate need not be optimal.

Let $\mu$ and $\nu$ be the two $N$-sample laws. On every half-open circle arc $J$ of length at most $1/m$, $\mu(J)\le\nu(mJ)\le m|J|+\beta$ (use the whole circle when the length is exactly $1/m$). For an interval $I$ of length $v$, let $A_h(x)=h^{-1}\sum_{j<h}{\bf1}_I(T^jx)$. Comparing shifted and initial prefixes costs at most $j/N$ per translate, so $|\mu(I)-\int A_h\,d\mu|\le(h-1)/(2N)$. Subdivide the circle at the inverse images under $T^j$ of both endpoints of $I$ for $0\le j<h$, and at the regular grid of size $m$. This makes at most the displayed number of half-open cells, each of length at most $1/m$, on which $|A_h-v|$ is constant. Apply the arc bound on each to get
$$
 \int |A_h-v|\,d\mu\le m\int |A_h-v|\,d\lambda+
              \left(m+2\sum_{j<h} b^j\right)\beta .
$$
For Haar measure, $|\lambda(I\cap T^{-j}I)-v^2|\le2 b^{-j}$: on every complete cell of length $b^{-j}$ inside $I$ the count integral is exactly its length times $v$, and the two partial cells cost at most $2b^{-j}$. Invariance gives the same covariance at any two times separated by $j$. Summing the diagonal variance $v(1-v)\le1/4$ and these off-diagonal bounds gives $\int (A_h-v)^2\,d\lambda\le(1/4+4/(b-1))/h$. Cauchy–Schwarz proves the result. For the last bound take $h=\max(1,\lfloor\frac12\log_b(1/\beta)\rfloor)$. One sample in a shrinking arc gives $\beta\ge1/N$, and $\sqrt\beta\ll1/\sqrt{\log(2/\beta)}$. In particular among limiting pairs with second coordinate zero the only first coordinate is zero, consistently with classical rational-dilation invariance.

## How far the geometry extends

The scalar comparisons above concern extreme, unanchored discrepancy. In base two take $N=3$, $x=1/4$, $z=-1/256$. For star discrepancy, computed with anchored intervals $[0,t)$, $D_N^*(x)=1/2$, $D_N^*(x+z)=1/3-1/64$ and $D_N^*(z)=1-1/64$. The change exceeds $1-D_N^*(z)$. Anchoring breaks rotation invariance. The finite maximum formula also fails for two-dimensional extreme box discrepancy: in binary at $N=2$, take $x=(1/3,0)$ and $z=(0,1/3)$. Each has discrepancy one by a thin coordinate strip. The sum consists of the two diagonal points at $1/3,2/3$, with box discrepancy $8/9$. A box containing both has area at least $1/9$, with equality approached, while a box of area greater than $8/9$ contains both points. A box containing just one costs at most $1/2$ in centered frequency.

There is a sharp comparison with the Ky Fan distance from a circle-valued sample to the set of constant samples. For its law $\mu$, define $k(\mu)$ as the infimum, over centers $c$ and $\epsilon\ge0$, of $\epsilon$ for which $\mu(\|u-c\|>\epsilon)\le\epsilon$. Then
$$
 k(\mu)\le 1-D(\mu)\le 3k(\mu).
$$
Indeed the concentration formula gives $1-D(\mu)=\inf_{c,r}\{\mu(\|u-c\|>r)+2r\}$ for $0\le r\le1/2$, with arbitrarily small enlargement at atoms. If the two terms are $E$ and $2r$, tolerance $\max(E,r)$ is admissible in the Ky Fan definition. Conversely a Ky Fan tolerance $\epsilon\le1/2$ bounds the cost by $3\epsilon$, and tolerance $1/2$ always suffices. Haar measure has $k=1/3$ and $D=0$. For $(1-h)\delta_0+h\delta_{1/2}$ with $0<h<1/4$, $k=h=1-D$: a ball of radius below $h$ cannot include both atoms and misses at least $h$, while the concentration cost with radius zero is $h$. Thus both comparison constants are sharp for probability laws. This compares concentration around the best constant; it uses no independence assumption.

For a genuine probability-metric comparison, the circle Wasserstein distance $W_1$ to Haar measure changes by at most $\inf_c N^{-1}\sum_{n<N}\|T^nz-c\|$ on translating $x$ by $z$: couple corresponding samples after a fixed rotation and use the triangle inequality. This proof supplies an upper bound for a different observable. Entropy of invariant empirical limits enters at the larger Rauzy class and has no finite-prefix identification with $d_N$. [Literature comparison](literature.md)
