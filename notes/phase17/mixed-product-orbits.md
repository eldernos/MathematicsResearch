# Exceptional orbits of independent-prime Stoneham products

Let $\alpha(B,p)=\sum_{j\ge1}p^{-j}B^{-p^j}$ for an integer radix $B\ge2$ and an odd prime $p$ coprime to $B$. For $x=\alpha(B,p)\alpha(B,q)$ with $p<q$, let $D_N(x)$ be the extreme interval discrepancy of the shifts $\{B^n x\}$ for $0\le n<N$, and put $D^+(x)=\limsup_N D_N(x)$.

**Results.** Every subsequential empirical limit is a mixture of Lebesgue measure and rational radix cycles, with weights given by normalized lengths of actual prefix intervals. Discrepancy converges to that of the mixture on the same subsequence. For $(B,p,q)=(2,3,5)$ the cycles have explicit discrepancies, and $D^+(x)\le4/11$ holds exactly when the upper density of integer shifted prefixes is at most $4/11$. Any excess requires integer plateaus at comparable scales, including a primary plateau near its geometric optimum. A finite arithmetic test gives the interpolation, spacing and logarithmic results for infinitely many radices for every pair of distinct odd primes. For example,

~~~math
D^+\bigl(\alpha(2,3)\alpha(2,7)\bigr)
\le \frac{11250083}{30000000}=\frac38+\frac{83}{30000000}.
~~~

These statements use paper proofs and exact finite checks. Existing kernel-checked inputs and open arithmetic questions are listed below. [Phase 14 interpolation](../phase14/mixed-interpolation.md) · [Phase 16 precision](../phase16/mixed-product-precision.md) · [Exact checker](../../scripts/phase17_mixed_product_orbits.py)

## D1. Empirical measures and rational cycles

Let $P=p^K$, $Q=q^L$ be the largest powers of the two primes at most $n$. The unshifted prefix $C_n$ sums $(p^i q^j)^{-1}B^{-p^i-q^j}$ for $i,j\ge1$ with $p^i+q^j\le n$. Set $R_n=B^n C_n$ and $A_n=PQR_n$. If the next insertion is at $n+g$, then

~~~math
0<B^n x-R_n\le \frac{B^{-g}}{(p-1)(q-1)} .
~~~

The error is also $O(1/n)$, uniformly including positions just before insertions. Every omitted pair has $p^i>n/2$ or $q^j>n/2$, and the corresponding geometric tails in $p^{-i}$ and $q^{-j}$ give that bound.

Within a shell $(K,L)$ the shape $(a,d)$ is given by $a=L-\#\{j\ge1:P+q^j\le n\}$ and $d=K-\#\{i\ge1:p^i+Q\le n\}$. The rectangle occurs precisely when $P+Q\le n$. Otherwise $a,d\ge1$ once both axes are available. All cells below both top axes are present because $P/p+Q/q<n$. Consequently the shape and shell determine the prefix and cut out a half-open interval $I=[U,V)$ of integer positions. These intervals partition the shells, up to finitely many initial positions. On $I$, $C_n=C_U$ and $R_n=B^{n-U}R_U$. Its reduced denominator $m_I$ is constant and divides $p^K q^L$. Write $\nu_I$ for the uniform measure on the radix cycle containing $\{R_U\}$.

Let $w_{I,N}=|I\cap[0,N)|/N$ and let $\lambda$ be Lebesgue probability on the circle. For an integer $M\ge1$ put

~~~math
\sigma_{N,M}=\left(1-\sum_{m_I\le M} w_{I,N}\right)\lambda+
                 \sum_{m_I\le M}w_{I,N}\nu_I .
~~~

For every $\epsilon>0$, there is $M_0$ such that for each fixed $M\ge M_0$ the empirical measures of $\{R_n\}$ and $\sigma_{N,M}$ differ on every circle arc by at most $\epsilon+o_M(1)$. Use blocks of length $\lfloor\sqrt N\rfloor$ and discard those meeting a shell boundary or insertion, and the last short block. There are $O((\log N)^2)$ boundaries below $N$. On each remaining block the denominator is at most $N^2$ and the points follow an exact radix orbit. For $m_I>M$ the fixed-support short-orbit estimate and interval Fourier approximation give error at most $\epsilon$ times the block length, using $m_I\le\lfloor\sqrt N\rfloor^5$ for large $N$. For $m_I\le M$ the period is at most $M$, so a partial block differs from its length times $\nu_I$ by at most $M$ on every arc. The accumulated incomplete-cycle cost is $O(M/\sqrt N)$. This uses the actual weight even when $N$ stops inside a plateau. Discarded blocks cost at most their normalized length. [Fixed-support estimate](../../NormalityChecker/SmoothOrbit.lean) · [Interval transfer](../../NormalityChecker/SupportDiscrepancy.lean)

For coupled circle samples within distance $t$ except on mass $e$, enlarging and contracting arcs bounds the difference of extreme discrepancies by $2t+e$. Wrapped arcs have complementary nonwrapping arcs, so the circle convention gives the ordinary extreme discrepancy. By the tail bound the true empirical measure $\mu_N$ and that of the rational orbit have a coupling with $t,e\to0$. Thus $\sigma_{N,M}$ approximates $\mu_N$ weakly and approximates $D_N$ in discrepancy in the iterated limit $N\to\infty$ then $M\to\infty$. One can also take sufficiently slowly increasing $M=M(N)$. For a recent window $[\delta N,N)$ intersect each plateau with the window before computing its weight, at cost at most $\delta+O(1/N)$. Letting $\delta\to0$ slowly gives vanishing error. Counts on an arc ending at a shifted atom may have persistent error. The weak approximation and the scalar discrepancy comparison account for this endpoint behavior. [Circle perturbation](../../NormalityChecker/CircleDiscrepancy.lean)

Index the countable set of rational cycles with $p,q$-smooth reduced denominators by $c$. Sum $w_{I,N}$ over plateaus of cycle $c$ to get $w_{c,N}$. Let $\mathcal W$ be all coordinatewise cluster points $w=(w_c)_c$ as $N\to\infty$. Each has $\sum_c w_c\le1$. Set

~~~math
\sigma(w)=\left(1-\sum_c w_c\right)\lambda+\sum_c w_c\nu_c .
~~~

Uniformly in the starting numerator, $\Delta_B(\nu_c)\to0$ as the denominator tends to infinity. Apply the fixed-support estimate to arbitrarily long integer multiples of its period and use interval Fourier approximation. Removing terms with denominator greater than $M$ from $\sigma(w)$ and adding their mass to $\lambda$ therefore costs at most $\sup_{m_c>M}\Delta_B(\nu_c)$ on all arcs. With the finite-$M$ estimates this proves that on any sequence with coordinate limit $w$, one has $\mu_N\to\sigma(w)$ weakly and $D_N(x)\to\Delta(\sigma(w))$. Every sequence admits such a subsequence by diagonal extraction. In particular,

~~~math
D^+(x)=\max_{w\in\mathcal W}\Delta(\sigma(w)).
~~~

Extraction on a sequence approaching the limsup gives attainment. This law uses actual plateau configurations and remains valid if their cycles share atoms.

If rectangular denominators grow, and for each fixed $M,\delta>0$ all but at most one nonrectangular plateau of denominator at most $M$ in $[\delta N,N)$ have total weight tending to zero, then

~~~math
D_N(x)-\max_I w_{I,N}\Delta(\nu_I)\longrightarrow 0,\qquad
D^+(x)=\limsup_{U\to\infty}\frac{V-U}{V}\Delta(\nu_{[U,V)}) .
~~~

For the first formula retain the one recent cycle, at cost $\delta+\epsilon(M)+\sup_{m_c>M}\Delta_B(\nu_c)+o(1)$ in the envelope (or pass directly to the subsequential limits $\sigma(w)$ above, each of which has at most one active cycle). For the second, the weight of an individual interval is maximized at $N=V$, and every fixed interval has weight tending to zero. Both formulas use only nonrectangular intervals.

### Exact binary cycles

For reduced denominator $m=3^r5^s>1$, let $m_0$ be the product of the primes present. For positive exponents the orders of $2$ are $2\cdot3^{r-1}$ and $4\cdot5^{s-1}$ by lifting the orders at the primes, using $v_3(2^2-1)=v_5(2^4-1)=1$. Take their least common multiple when both primes occur. The subgroup generated by $2$ has index one for a pure power and two for mixed support. The indices at $m$ and $m_0$ agree, so each numerator coset consists of all lifts of its pattern modulo $m_0$. These patterns are $\{1,2\}$, $\{1,2,3,4\}$, and either $\{1,2,4,8\}$ or $\{7,11,13,14\}$, respectively.

For a mixture with atom masses $\rho_i$ at sorted points $t_i$, put $W=\sum_i\rho_i$. The discrepancy is the range of the centered cumulative function. At $t_i$ include both values $\sum_{j<i}\rho_j-Wt_i$ and $\sum_{j\le i}\rho_j-Wt_i$, and include the endpoint values. This follows by expressing interval errors as differences of cumulative values and taking one-sided limits. The $m/m_0$ equal cells of a cycle have identical scaled residue patterns and equal masses, giving

~~~math
\Delta(\nu_I)=\frac{m_0}{m_I}
\begin{cases}
2/3 & m_0=3,\\
2/5 & m_0=5,\\
11/20 & m_0=15 .
\end{cases}
~~~

The mixture of the two $15$-cycles with weight $1/4$ each and weight $1/2$ on $\lambda$ has discrepancy $7/60$. The sum of their weighted discrepancies is $11/40$. For $m_I=1$ the cycle is $\delta_0$ and its discrepancy is one.

The test for the singleton is $3^K5^L\mid A_U$. For $m_I=3^r5^s>1$, the numerator selecting the coset is $A_U/(3^{K-r}5^{L-s})$ modulo $m_0$. The binary tests below require $L\equiv a\bmod2$ and $K\equiv d\bmod4$, plus one residue class at each higher precision on each axis. Any fixed lifting depths are attainable at arbitrarily late shells of the primary shape near its real geometric optimum. Thus these fixed congruences do not decide the integer case. The checker finds no nonempty integer prefix through $n=3^{12}$, checking every switch boundary and its predecessor. The existence of such a plateau beyond the checked range, and the existence of infinitely many, remain unresolved.

## D2. The three-place problem

Write $\alpha_3(a,d)=a+2\zeta_{3,a,d}$ and $\alpha_5(d,a)=d+4\zeta_{5,d,a}$ for the local zeros in shell-index coordinates, defined in D4. A nonrectangular plateau of denominator $3^r5^s$ with $K>r$, $L>s$ satisfies

~~~math
-\log 5<L\log 5-K\log 3<\log 3,\qquad
v_3(L-\alpha_3(a,d))\ge K-r-1,\qquad
v_5(K-\alpha_5(d,a))\ge L-s-1 .
~~~

Conversely, the two local inequalities and torsion congruences give denominator dividing $3^r5^s$ at an active shell of that shape, by the exact loss formula.

For own prime $p$ and other prime $q$, put $x_j(\beta)=q^{-j}\beta^{-q^j}$ and $S_m(\beta)=\sum_{j=1}^m x_j(\beta)$. Directly from $x_j(\beta^q)=q x_{j+1}(\beta)$ one has

~~~math
S_m(\beta^q)=q S_{m+1}(\beta)-\beta^{-q},\qquad
G_{a,d}(m;\beta^q)=qG_{a,d}(m+1;\beta)-\beta^{-q},
~~~

where $G_{a,d}(m)=S_{m-a}+p(S_{m-1}-S_{m-a})+p^d x_m$ for $m\ge a$. The identities extend on matching analytic index sheets by density. The change $\beta\mapsto\beta^{q^u}$ advances $m$ by $u$ and subtracts $q^uS_u(\beta)$. Thus a zero at the new base gives a prescribed inhomogeneous value at the old base. Subtracting the infinite sum gives a homogeneous equation for the difference at real $\beta>1$. The infinite sum diverges at $p$-adic units because the summands have norm one.

There is a local obstruction to analytic normalization at the ternary place. Set $A=q^u$ and $\beta=\omega\exp T$ with torsion part $\omega$. An analytic function $F$ near $T=0$ solving $F(AT)=AF(T)-A S_u(\omega\exp T)$ would require $\sum_{j=1}^u\omega^{-q^j}=0$, by differentiation. For $(p,q,B)=(3,5,2)$ this sum is $-2$. For $(5,3,2)$ it vanishes because the torsion powers alternate between opposite fourth roots. There the coefficient of $T$ is free and the other coefficients are obtained by division by $A^j-A$, $j\ne1$. For $j\ge2$, the loss $v_p(A^j-A)=v_p(A-1)+v_p(j-1)$ leaves a positive convergence radius. This identity concerns the base variable. The exceptional-shell question concerns index zeros at a fixed base.

An algebraic index zero at either place would suffice for each fixed shape. If $\alpha_p\in\mathbb Z_p$ is algebraic over $\mathbb Q$, take a nonzero integer polynomial $F$ with $F(\alpha_p)=0$. For integers $m$ outside its finite zero set, $v_p(m-\alpha_p)\le v_p(F(m))=O(\log m)$, since $F(m)$ is a nonzero integer of polynomial growth and its divided difference at $m,\alpha_p$ is integral locally. This conflicts with the required depth because $K\asymp L$. Infinitely many bounded-denominator shells for a fixed shape would force both index zeros to be transcendental over $\mathbb Q$ and to admit integer approximations of unbounded quality.

- Real Baker bounds can bound the nonzero form $K\log3-L\log5$ from below by a negative power of the index height. The allowed real interval here has fixed length. On any fixed-depth residue classes an irrational rotation produces arbitrarily late ratios in every open subinterval of the admissible overlap. A $p$-adic logarithm bound would require local linear forms in logarithms of algebraic units with controlled coefficients. No such expression for the approximation to either zero follows from the base identities.
- Classical Mahler specialization in the contracting disc concerns the convergent series in the base variable. Here the local arguments are units, the opposite-prime iterate is indifferent on principal units, and each index zero is defined implicitly. The local quinary normalization does not change these requirements.
- Ridout and the $S$-adic Subspace Theorem for algebraic linear forms require algebraic approximands or fixed algebraic coefficients. The arithmetic description of these zeros is missing. Increasing residue truncations instead give moving coefficients with heights potentially of the order of the inverse errors. Fixed-form estimates do not supply a contradiction. For fixed algebraic zeros the polynomial argument above already suffices.
- Ultrametric separation bounds the number of exceptional scales, allowing an infinite sequence with very large gaps.

For $(1,1)$ one has $G_{1,1}(m)=S_{m-1}+p x_m$. At the ternary place and $\beta=2\exp(3T)$, the reduction of $\partial_T G/3$ modulo $3$ on $m=1+2z$ is $-z$. Since $\zeta_{3,1,1}\equiv1\bmod3$, its implicit derivative in $T$ is a unit and the root varies isometrically on a sufficiently small base ball about $2$. The normalized base derivative at the quinary place vanishes modulo $5$. The ternary isometry yields an almost-everywhere exclusion in that local arithmetic base ball for the primary shape. At fixed retained-layer cap, the Haar measure for a shell $(K,L)$ is $O(3^{-K})$. There are $O(1)$ overlapping choices of $L$ at each $K$, so the events are summable. This leaves the specific integer base $2$ undecided. [Base derivative calculation](../phase16/mixed-product-precision.md)

For both places, the binary roots on any fixed nonrectangular shape also exclude exact integer arguments on their compatible sheet. At $m\ge a$, $G_{a,d}(m)$ is a positive rational. For $m<a$, extend $S_j$ by $S_j=-\sum_{i=j+1}^{0}x_i$ at negative integers, as follows from the recurrence and analytic interpolation. At $i=-h<0$, the factor $2^{-q^i}$ uses compatible $q^h$-th roots of $1/2$, since the opposite prime $q$ is coprime to $p-1$. If a negative index occurs in $G$, its lowest index has nonzero coefficient, equal to $p-1$ for $a>1$ and $p^d-1$ for $a=1$. Writing the lowest such index as $-H$, the radicals are powers of $2^{-1/q^H}$ with exponents $q^{H-h}$. These powers and $1$ are linearly independent over $\mathbb Q$ by Eisenstein for the inverse root. If no negative index occurs with $m<a$, then $m-a=-1$ and $m\ge0$. For $m\ge1$ the expression is positive because $(1-p)S_{-1}=(p-1)/2$ and the remaining terms are positive or zero. At $m=0$ it is $(p^d-1)/2>0$. This proves $\zeta_{p,a,d}\notin\mathbb Z$ and leaves the problem of approximations by ordinary integers open.

## D3. Shape co-occurrence and the exact \(4/11\) bound

For fixed $a$, $\alpha_p(a,d)$ converges to $\alpha_p(a,\infty)$ as $d\to\infty$, where the last term $p^d x_m$ is omitted. For $d_1<d_2\le\infty$ the valuation of the difference is exactly $v_p(u)+d_1-1$. The two functions differ by $p^{d_1}$ times a unit, and each function divided by $p$ is an isometry in $z=(m-a)/u$. To vary the first deficit, write $a=r+u k$ and $m=r+u z$ on a fixed sheet. The $k$-dependence is through $(1-p)S_{u(z-k)}$ in

~~~math
G_{a,d}(m)=(1-p)S_{m-a}+p S_{m-1}+p^d x_m .
~~~

At fixed $d$, changing $k$ by $\Delta k$ changes the root in $z$ by valuation exactly $v_p(\Delta k)$. This follows from the isometries for $S_{uz}/p$ and $G/p$. Thus the map from $k$ to the root in $z$ extends to an onto isometry of $\mathbb Z_p$. Along ordinary $a\to\infty$ on that sheet the cluster set of $\alpha_p(a,d)$ is the whole coset $r+u\mathbb Z_p$. For the simultaneous pair of roots, one deficit tending to infinity while the other is fixed leaves one coordinate ranging over such a coset and sends the other to its fixed-axis limit.

Two fixed shapes recurring in comparable exceptional shells must have integer zero differences with compatible sheet residues. Indeed a subsequence fixes the bounded offsets $(d_K,d_L)$ and the growing depths give

~~~math
\alpha_3(a_1,d_1)-\alpha_3(a_2,d_2)=d_L,\qquad
\alpha_5(d_1,a_1)-\alpha_5(d_2,a_2)=d_K .
~~~

The offsets must satisfy $d_L\equiv a_1-a_2\bmod2$ and $d_K\equiv d_1-d_2\bmod4$. For a compatible offset on one axis, align the two index arguments. Subtraction cancels the common initial sum and leaves a finite combination of consecutive endpoint terms with rational coefficients. The term of largest index with differing weight has nonzero coefficient. When the arguments differ, their last nonzero indices differ, and when they agree a distinct shape changes the last weight or a step in the weights. Factoring the common $q^{-j}$ at the first remaining index $j$ gives a nonzero polynomial with rational coefficients at $X=\beta^{-q^j}$ on the selected sheet, since consecutive terms involve $X,X^q,X^{q^2},\ldots$. An exact aligned common zero therefore forces this local unit to be algebraic. The additional equation $G=0$ still contains the interpolated initial sum. The identities above do not rule out both algebraic-unit constraints at the relevant roots.

Non-coincidence for all compatible offsets would imply the single-plateau law in D1. For each fixed recent window and bulk strip, only finitely many offsets and shapes are involved, and for sufficiently large depths they exclude any second bulk plateau. The discarded boundary mass can be made arbitrarily small. It would also imply $D^+(x)\le4/11$ by the single-shape bound. The integer equalities alone are necessary for co-occurrence. The shells must also be simultaneously active and achieve the growing depths. In particular the zero-slack bound need not resolve every compatible pair.

### Exact reduction to integer-prefix density

Set $m_*=4/11$, $\gamma=2.85\cdot10^{-10}$ and

~~~math
C_0=\limsup_{N\to\infty}\frac{\#\{0\le n<N:R_n\in\mathbb Z\}}N .
~~~

The Phase 16 certificate bounds the upper density of every fixed bounded-denominator set by $S=m_*+\gamma$ with the same $S$ for each cap. Every subsequential profile therefore has total atomic weight $w_0+w\le S$, with $w_0$ the weight of $\delta_0$ and $w$ the weight of all other cycles. Every nontrivial binary cycle has discrepancy at most $2/3$, so $\Delta(\sigma)\le w_0+(2/3)w\le S-w/3$. If $\Delta(\sigma)>m_*$, this yields $w<3\gamma$ and $w_0>m_*-2\gamma$.

For every nontrivial cycle and $0<t<1$, its masses in $[0,t)$ and $[t,1)$ are at most $(15/4)t$ and $(15/4)(1-t)$, respectively. There are at most $mt$ or $m(1-t)$ nonzero grid points on the respective sides and the period is at least $4m/15$. The centered cumulative function at $t>0$ is

~~~math
w_0(1-t)+\sum_{c\ne0} w_c\bigl(\nu_c([0,t))-t\bigr).
~~~

The endpoint bounds place its value in $[0,w_0]$ if $w_0\ge(11/4)w$. The range is then exactly $w_0$ by the jump at zero. This dominance holds whenever $\Delta(\sigma)>m_*$. Every profile also has discrepancy at least $w_0$, by taking short arcs about zero. The largest $w_0$ is $C_0$ by subsequence extraction. Consequently

~~~math
D^+(x)\le4/11\quad\Longleftrightarrow\quad C_0\le4/11 .
~~~

If either exceeds $4/11$, then $D^+(x)=C_0$. If there are only finitely many nonempty integer prefixes, the stronger bound $D^+(x)\le(2/3)S$ follows. The fixed-depth joint failure sets approach the geometric cap along primary intervals, but this does not give positive subsequential weight to any fixed reduced denominator. The proposed upper bound makes no claim of equality for the actual discrepancy.

An excess of integer mass needs two distinct scales. The last Phase 16 certificate, with denominator cap one, leaves at most $\gamma+o(1)$ outside the single bulk interval. Thus along any sequence realizing $C_0>m_*$ the main interval has shape $(1,1)$ and its ratio $r=Q/P$ lies in $(41/50,21/25)$ for large cutoffs. The nonprimary bound and the primary weight function in D4 give gaps greater than $\gamma$ outside these conditions. For ratios in this range an earlier nonrectangle in the same shell has $d=2$ or has $d=1$ and $a=2$. Indeed $P/9<n-Q<P$ before the primary interval, and if $d=1$ there then $Q+P/3\le n<P+Q/5$ implies $Q/25<n-P<Q/5$. Both cases violate one primary torsion congruence. On $[Q,P)$ the preceding shell is $(K-1,L)$, and all its shapes have $a=1$. Quinary torsion would require $d\equiv0\bmod4$ there, and $v_3(\alpha_3(1,1)-\alpha_3(1,d))=0$ excludes even joint ternary depth two against the primary interval. Later positions in the primary shell are rectangles. Also $N<\min(3P,5Q)=3P$ eventually on the sequence since otherwise the primary weight is at most $(2/3)/3$. Hence any surplus comes from earlier integer plateaus before $Q$. If the surplus stays at least $\varepsilon>0$, choose a recent window and boundary strip that together discard less than $\varepsilon/2$. An earlier integer plateau of positive relative size must remain on a subsequence with fixed shape and fixed offsets, by the finite grid and the finite number of recent shells. Bounding this possible excess of integer-prefix mass is the remaining zero-slack problem.

## D4. An infinite family

For each of the two ordered pairs of axes use the following finite hypotheses. In their formulation $p$ is the own prime, $q$ the other, and $\omega$ the Teichmüller part of the integer radix $B$ in $\mathbb Z_p^\times$.

1. There is a positive integer $u$ with $q^u\equiv1\bmod p$ and $\omega^{q^{j+u}}=\omega^{q^j}$ for all $j\ge1$.
2. For $x_j=q^{-j}B^{-q^j}$, $S_u\equiv0\bmod p$, while $S_i$ is a unit for $1\le i<u$.
3. $v_p(S_u)=1$.

For condition 1 let $t=\operatorname{ord}_p(B)$. Require $v_q(t)\le1$ and take $u$ a multiple of $\operatorname{ord}_p(q)$ and the order of $q$ modulo the prime-to-$q$ part of $t$, with order one modulo one. The possible $q$-part of $t$ is already absorbed by each exponent starting at $j=1$. These tests allow $p\mid u$. Under condition 1, condition 2 is exactly the requirement that $p\mid S_m$ iff $u\mid m$. Condition 3 is exactly the unit condition on the normalized index derivative for the lift below. These are hypotheses for the uniform one-sheet, simple-zero mechanism. Multiple sheets or a degenerate derivative call for different arithmetic tests.

**Valuations and interpolation.** Euler's theorem gives $B^{P-p^i}\equiv1\bmod p^i$. Multiplication by $p^{K-i}$ and the geometric sum in each opposite-axis fibre give

~~~math
(p-1)B^P A_n+B^n q^L G_{a,d}(L)\equiv0\pmod{p^K},
~~~

using $G_{0,0}(L)=S_L$ for rectangles. The geometric sum is $(p-1)\sum_{i=1}^{I_j}p^{K-i}=p^K-p^{K-I_j}$, with $I_j=\#\{i\ge1:p^i+q^j\le n\}$. The weights $p^{K-I_j}$ are $1,p,p^d$ across the ranges $j\le L-a$, $L-a<j<L$, and $j=L$ in a nonrectangle. The lost layers therefore equal $\min(K,v_p(G_{a,d}(L)))$. At the other prime the shape coordinates swap.

Put $A=q^u$ and $T=\log_p(B/\omega)$. Interpolation on the sheet $i+uz$ is

~~~math
x_{i+uz}=q^{-i}A^{-z}\omega^{-q^i}\exp(-q^i T A^z).
~~~

Since $\log A,T\in p\mathbb Z_p$, this is analytic in $z$ on a disc of radius slightly greater than one. For $g(z)=\sum_{i=1}^u x_{i+uz}$, the forward differences satisfy $v_p(\Delta^k g(0))\ge k+1$. Expand the last exponential about $A^z=1$. A term of degree $h$ in $A^z-1$, combined with the outer factor $A^{-z}$, has $k$-th differences divisible by $p^k$, by binomial expansion and $(A^{j-1}-1)^k\in p^k\mathbb Z_p$. The degree-zero terms sum to $S_u(A^{-1}-1)^k$. For $h\ge1$ the coefficient has valuation at least $h-v_p(h!)\ge1$. Thus

~~~math
S_{uz}=\sum_{k\ge0}\Delta^k g(0)\binom{z}{k+1}
~~~

truncates exactly at $k=D-2$ modulo $p^D$. Its analyticity on a disc of radius greater than one follows from this coefficient bound, $v_p((k+1)!)\le k/(p-1)$, and the Gauss norm of the binomial numerator. It agrees with the discrete sum at nonnegative integers by Newton interpolation and telescoping. Adding finitely many terms interpolates $S$ on the other sheets and gives the signed shifts used above.

For $v_p(y)=t\ge0$, Vandermonde and $\binom{y}{j}=(y/j)\binom{y-1}{j-1}$ bound the increment of each Mahler term with $k\ge1$ by valuation at least $t+k+1-\lfloor\log_p(k+1)\rfloor\ge t+2$. The term $k=0$ contributes $yS_u$. Every additional $x_{i+uz}$ changes by a multiple of $p^{t+1}$, by its analytic expression. Hence

~~~math
S_{u(z+y)}-S_{uz}\equiv yS_u\pmod{p^{t+2}},\qquad
G_{a,d}(a+u(z+y))-G_{a,d}(a+uz)\equiv yS_u\pmod{p^{t+2}} .
~~~

The second formula also holds for $d=\infty$. Dividing the functions by $p$ gives isometries, bijective by their induced maps on finite quotients. Passing to difference quotients gives normalized derivative $S_u/p\bmod p$. Off the sheet $m\equiv a\bmod u$, the value is a unit. On the sheet the unique zero is $\zeta_{p,a,d}$ and

~~~math
\alpha_p(a,d)=a+u\zeta_{p,a,d},\qquad
v_p(G_{a,d}(a+uz))=1+v_p(z-\zeta_{p,a,d}) .
~~~

The loss test at depth $h$ thus selects a single residue of the opposite index modulo $u p^{h-1}$, including when $p\mid u$. On rectangles $a=0$ and the zero is $0$. The lost $p$-layers are then at most $1+\lfloor\log_p L\rfloor$, so rectangular denominators grow uniformly. The mixture theorem applies with only nonrectangles contributing bounded-denominator plateaus apart from finitely many positions at each cap.

**Boundary strips and exact single-shape geometry.** For $0<\eta<1/2$ the upper density of $P>(1-\eta)n$ is $p\eta/(p-1)$. Put $t=p^{\lfloor\log_p(N-1)\rfloor}/N$. The last strip contributes $\min(1-t,\eta t/(1-\eta))$ and the earlier strips together contribute $\eta t/((1-\eta)(p-1))+o(1)$. The function peaks at $t=1-\eta$, approached by cutoffs at the end of a strip. Therefore the union of strips for $p,q$ has upper density at most $(p/(p-1)+q/(q-1))\eta$. Outside it, the deficits lie in a grid $a\le A_\eta$, $d\le D_\eta$, where $q^{A_\eta}>1/\eta$ and $p^{D_\eta}>1/\eta$. For example, $n-P\ge\eta n\ge\eta Q$ and $n-P<q^{L-a+1}$ give $q^{a-1}<1/\eta$.

Put $r=Q/P$. For fixed positive deficits and all sufficiently late shells the shape interval has endpoints $Pu_0(r),Pv_0(r)$ when $v_0>u_0$, where

~~~math
u_0(r)=\max(1+r/q^a,r+1/p^d),\qquad
v_0(r)=\min(1+r/q^{a-1},r+1/p^{d-1},p,qr).
~~~

If $a=L$ or $d=K$, the corresponding lower expression is $1$ or $r$ because the fibre is empty. This changes the lower endpoint by at most one. The weight through any cutoff is at most $1-u_0/v_0+O(1/N)$ when the interval is nonempty. For $(1,1)$, $v_0\le1+r$, so use $\min((1-1/q)r,1-1/p)/(1+r)$. This increases and then decreases, with unique maximum at $r_*=q(p-1)/(p(q-1))$. There $v_0=1+r_*$ since $1/(q-1)<r_*<p-1$. The maximum equals

~~~math
M_{p,q}=\frac{(p-1)(q-1)}{2pq-p-q}.
~~~

For $a\ge2$, feasibility forces $r<q/(q-1)$ by $1+r/q^{a-1}>r$. The first upper and lower lines bound the relative length by $(1-1/q)x/(1+x)$ for $x=r/q^{a-1}<1/(q-1)$, giving at most $(q-1)/q^2$. For $d\ge2$, feasibility forces $r>1-p^{1-d}$. The second lines give the analogous $(p-1)/p^2$ bound. Both are smaller than $M_{p,q}$. The maximum for the primary shape is a lower bound for the upper density of every fixed joint-depth failure set. In fixed congruence classes of $K,L$, the shell ratios are dense on every open subinterval of the overlap region by irrational rotation, and they can approach $r_*$ at arbitrarily late shells.

**Separation and sampling.** Let $u$ be the period at $p$ and $v$ at $q$. Two shells of a fixed shape with losses at least $h_i,k_i$ satisfy

~~~math
u p^{\min(h_1,h_2)-1}\mid L_2-L_1,\qquad
v q^{\min(k_1,k_2)-1}\mid K_2-K_1.
~~~

Active shells are ordered componentwise since both indices are nondecreasing with position. If one index is fixed, the other varies by at most a constant depending on the primes, since $p^K\asymp q^L$. The displayed moduli eventually exceed these constants for bounded denominators or linear retained-layer caps. Both differences are then nonzero and each is at least its indicated modulus. For bounded denominators this gives $\log U_2\ge c_M U_1$, using $U_i\asymp p^{K_i}\asymp q^{L_i}$. If the retained fractions are at most $\theta<1$ on their respective axes, it gives $\log U_2\ge c_\theta U_1^{1-\theta}$ instead.

For fixed depths $(h,k)$ the flow at time $t=\log n$ with coordinates $t/\log p$ and $t/\log q$ modulo $v q^{k-1}$ and $u p^{h-1}$ is equidistributed by irrationality of $\log p/\log q$. The fraction parts determine the shape, except when an endpoint would use an exponent below one. Those positions lie in bounded-width intervals following the axes and have bounded total logarithmic cost. The shape boundaries and axes have Haar measure zero. At each fractional pair there is exactly one residue cell per axis matching its test. Therefore the marginal and joint logarithmic densities are respectively

~~~math
\frac1{u p^{h-1}},\qquad \frac1{v q^{k-1}},\qquad
\frac1{u v p^{h-1}q^{k-1}} .
~~~

The joint law also holds conditional on every fixed shape with positive logarithmic density. Real and integer memberships agree between switch positions at powers or sums of powers, apart from the bounded logarithmic cost above. Replacing the integral weight $\log(1+1/n)$ by $1/n$ costs $O(1)$.

For fixed depths $(h,k)$ and every $\epsilon>0$, the orbit estimate in D1 gives $D_N(x)\le\epsilon+F_{h,k}(N)/N$ eventually, where $F_{h,k}(N)$ counts joint failures. Indeed any fixed denominator cap forces the fixed losses for sufficiently large shells. Partial summation with the joint logarithmic law and then increasing the depths yield $\sum_{N\le X}D_N(x)/N=o(\log X)$ and $\liminf D_N(x)=0$.

For $\epsilon>0$, choose a denominator cap so that $D_N>\epsilon$ forces a positive proportion of bounded-denominator positions. Choose $\eta,\delta$ small enough that the strips and early segment $[0,\delta N)$ cannot account for them. Some exceptional plateau of the finite bulk grid must then meet $[\delta N,N)$. For each fixed shape its successive plateau starts have $m_j=\log U_j$ with $m_{j+1}\ge c_M e^{m_j}$ eventually. Each plateau has $V_j/U_j\le p$ and accounts for at most a bounded number of integer logarithmic bins. The number of bins up to $T$ is $O_\epsilon(\log^* T)$ and the sum of their reciprocal indices converges, counting each shape separately. It follows that

~~~math
\#\{m\le T:\exists N\in[e^m,e^{m+1}),\ D_N(x)>\epsilon\}
=O_\epsilon(\log^* T),\qquad
\sum_{D_N(x)>\epsilon,\ N\ge2}\frac1{N\log N}<\infty .
~~~

The corresponding bad-cutoff harmonic weight up to $X$ is $O_\epsilon(\log^*\log X)$.

**Infinitely many radices for every prime pair.** Impose $B\equiv1+pc\bmod p^2$ on the own axis, so $\omega=1$ and $x_j\equiv q^{-j}-pc\bmod p^2$. If $q\not\equiv1\bmod p$, take $u=\operatorname{ord}_p(q)>1$. The geometric sum vanishes modulo $p$ precisely at multiples of $u$, and precisely one $c\bmod p$ makes $S_u$ vanish modulo $p^2$. If $q\equiv1\bmod p$, take $u=p$. Now $S_i\equiv i\bmod p$ and $S_p\equiv p\bmod p^2$ for every $c$, since $p$ is odd. Make these choices independently at the other prime and combine them modulo $(pq)^2$ by the Chinese remainder theorem. Every resulting class contains infinitely many valid $B\ge2$.

### Exact finite depth certificates

For a fixed window and grid, choose radii $R_K>\log_p(1/\delta)+1$, $R_L>\log_q(1/\delta)+1$. Compute the two residue classes for every shape at depths $(h,k)$, requiring the moduli $u p^{h-1},v q^{k-1}$ to exceed $R_L,R_K$, respectively. For each pair of distinct shapes test whether both centered residue differences have absolute values at most $R_L,R_K$. If no pair passes, at most one bulk shape and shell meets the joint test. The resulting unconditional bound is $M_{p,q}+(p/(p-1)+q/(q-1))\eta+\delta$. The checker uses exact powers to choose the grid and radii, and exact rational and integer comparisons.

With $\eta=10^{-6}$ and $\delta=10^{-7}$:

- $(2,3,7)$ has periods $(3,6)$ and block sums $(6\bmod9,7\bmod49)$. The $8$ by $13$ grid with radii $(16,10)$ separates at depths $(3,9)$. The geometric maximum is $3/8$ at $r=7/9$, and the discrepancy bound is $11250083/30000000$.
- $(2,3,13)$ has periods $(3,6)$ and block sums $(6\bmod9,65\bmod169)$. The $6$ by $13$ grid with radii $(16,8)$ separates at depths $(2,7)$, giving $720004991/1860000000$.
- $(36,5,7)$ has periods $(4,6)$ and block sums $(10\bmod25,21\bmod49)$. The $8$ by $9$ grid with radii $(12,10)$ separates at depths $(5,4)$, giving $720004379/1740000000$.
- $(2,5,7)$ and $(3,5,7)$ have block sum $0\bmod25$ at period $4$ on the $5$-axis. The former also has several failing sheets at period $6$ on the $7$-axis. For $(2,3,11)$ the $3$-axis has block sum $0\bmod9$ at period $2$, and the $11$-axis has first-layer zeros at $3,6,13,20$ in period $20$. These triples fail the stated arithmetic hypotheses.

## Proof status and reproduction

The general mixture law, binary cycle formulas and integer-density equivalence, axis limits and base identities, and infinite-family extension are paper results. The command below checks rational cycle discrepancies and mixtures, finite Mahler truncations and zero lifts, axis limits, switch-boundary valuations, shape maxima, and depth certificates.

~~~sh
python -B scripts/phase17_mixed_product_orbits.py
~~~

Existing Lean proves the binary endpoint congruences and first lifts, primary geometry and separation cores, the fixed-support orbit estimate, and circle perturbation. The new core lemmas suitable for formalization are interval counting with a bounded-denominator cycle component, the periodic residue grid for $3^r5^s$, integer-mass dominance, and the generic fibre and Newton arguments. [Endpoint interpolation](../../NormalityChecker/ProductThreeFiveInterpolation.lean) · [Phase 16 cores](../../NormalityChecker/Phase16StonehamBounds.lean) · [Quadratic plateau analogue](../phase14/plateau-spectrum.md)

The open arithmetic questions are growing-depth nonexistence for bounded-denominator shells at the fixed radix $2$, compatible integer differences of distinct index zeros, and the exact upper bound on integer-prefix density. Ordinary binary normality would follow if for every fixed shape at least one axis zero had a logarithmic integer-approximation bound, by using the finite bulk grid and then shrinking the boundary strips.
