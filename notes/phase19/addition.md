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

The same constant works on the whole closed region. Both series are uniformly computable from Cauchy names for an admissible triple, and the witnesses can be chosen algebraically independent. The three projected orbit laws converge weakly to $\alpha\delta_0+(1-\alpha)\lambda$ and the corresponding laws with $\beta,\gamma$, where $\lambda$ is normalized length on the circle.

Generic-point existence for invariant torus laws and the five vertex laws already give a short qualitative sufficiency proof. The constructive assertions here are the common cubic schedule, uniform all-prefix rate, computability and algebraic independence. The same facets occur in the point-entropy inequalities of Bergelson and Downarowicz; the entropy and discrepancy observables differ on general orbit laws. [Source comparison](literature.md)

The unconditional qualitative theorem for every radix and simultaneous rank-one mixture realization are [proved in Lean](../../NormalityChecker/AdditionSpectrum.lean). The formal construction uses a block schedule adapted to complete periods. The following cubic schedule also gives the stated rate, a separate written conclusion.

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

There is a uniform implementation from arbitrary Cauchy names, including at equality in any comparison. The computable operations in the weight formulas give rational $\widehat w_i$ with $|\widehat w_i-w_i|\le1/(20k)$. Compare $k\widehat w_i-C_i$ exactly and take the first maximizer. The largest true deficit is at least $1/5$, so the chosen true deficit is at least $1/5-2/20>0$. The same count bounds follow. This rational procedure may schedule different types from the exact rule.

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

## Algebraically independent coordinates

**Strengthening.** The witnesses $x,y$ can be algebraically independent over $\mathbb Q$ for every admissible triple, with the same order of error uniform in the triple. A single algorithm produces such a pair from names for a computable admissible triple. In particular $x,y,x+y$ are all transcendental, including on every face and vertex. The three-component vector itself satisfies the polynomial relation $X+Y-Z=0$.

Fix the preceding nominal type sequence independently of any later overrides. At indices $k$ that are powers of two allow arbitrary targets in $(q_k^{-1}\mathbb Z/\mathbb Z)^2$. Charge every position of an overridden block as a possible model count error relative to the nominal model. Through $N$ the extra count is bounded by

$$
\sum_{2^j\le K}h_{2^j}\le7t\sum_{2^j\le K}4^j\le(28t/3)K^2.
$$

The next ordinary block recovers its programmed state exactly, even though its insertion coefficient may have changed. The positive-coefficient tail bound holds across all overrides.

Enumerate the nonzero polynomials $P(X,Y)\in\mathbb Z[X,Y]$. Suppose a finite coefficient prefix through index $J$ has been fixed and take the next polynomial, with degrees $d_x,d_y$ in the respective variables. Choose a power of two $k>J$ such that $q_k>\max(d_x,d_y)$ and $2B b^{-h_k}<1/q_k$. Fill intervening blocks by their nominal targets. At $k$ consider targets $a/q_k$ in the first coordinate for $0\le a\le d_x$ and $a'/q_k$ in the second coordinate for $0\le a'\le d_y$. Provisionally continue all candidates with the nominal targets forever. The first-coordinate real depends only on $a$ and the second only on $a'$. After the shift by $n_k$ the targets have mutual circle distances at least $1/q_k$, while each tail has size at most $B b^{-h_k}$. Hence the resulting real values in each coordinate are distinct.

The resulting Cartesian grid contains a pair where $P\ne0$. Otherwise, at each second-coordinate value the polynomial in $X$ has more roots than its degree. Each coefficient as a polynomial in $Y$ then has more roots than its degree, contrary to $P\ne0$. This includes polynomials in just one of the variables and nonzero constants.

To find a certified pair, extend the provisional prefixes in parallel, in the sense of testing all finitely many candidates at each successive depth $L\ge k$. Each scalar partial sum $S_L$ has all its continuations in $[S_L,S_L+B b^{-n_{L+1}}]$. Evaluate $P$ by rational interval arithmetic on the product boxes. As their widths vanish, a box about a nonzero value eventually excludes zero. Fix its target choices and all intervening nominal choices through $L$. Every future continuation retains that certificate. Repeat with a fresh power of two beyond $L$. All searches terminate and the growing prefixes compute both reals with the stated tail modulus. For arbitrary real triples the same argument works relative to names for the inputs. This proves independence through explicit avoidance of polynomial relations on **both** coordinates.

## Finite linear forms and joint Haar measures

Let $M$ be an integer matrix with $d$ columns. Write $m$ for a row and $\chi_m(u)=m\cdot u\bmod1$ for its character on $\mathbb T^d$. Take a finite family of connected rational subtori $H_i=B_i\mathbb T^{r_i}\subseteq\mathbb T^d$, with integer matrices $B_i$, and weights $w_i\ge0$ summing to one. Rank zero denotes the trivial subgroup. For normalized Haar measure $\lambda_{H_i}$, its projection by $\chi_m$ is $\delta_0$ when $mB_i=0$ and circle Haar measure otherwise. Indeed the image is a connected compact subgroup of the circle, and the pushed-forward measure is translation invariant there. Thus the projected discrepancy of $\sum_i w_i\lambda_{H_i}$ is exactly

$$
\delta_m=\sum_{i:\,mB_i=0} w_i .
$$

**Quantitative realization.** There is a vector $u$ of positive series on the same one-prime cubic schedule whose **joint** radix orbit law converges weakly to this Haar mixture. For every fixed $m\in\mathbb Z^d$ it satisfies $D_N(m\cdot u)=\delta_m+O_{b,p,m,(B_i)}(N^{-1/3})$, with constant independent of the weights. The same vector works for all $m$, hence there is a common constant for any prescribed finite list. For computable weights the vector is computable, and the sparse construction can make its $d$ coordinates algebraically independent.

Here is a direction for each block that works even on a higher-dimensional subtorus. In $\mathbb Z_p$ let $\theta=\sum_{j\ge1}p^{j!}$, and use its computable residues modulo $q_k$. It is transcendental over $\mathbb Q$. Indeed if a nonzero $F\in\mathbb Z[X]$ vanished there, the strictly increasing integer truncations $a_s=\sum_{j=1}^s p^{j!}$ would satisfy $p^{(s+1)!}\mid F(a_s)$. But $a_s\le2p^{s!}$, so eventually $0<|F(a_s)|<p^{(s+1)!}$ by the degree bound and the finiteness of the integer roots.

In a block of type $i$ with $r_i>0$, reduce $B_i(1,\theta,\ldots,\theta^{r_i-1})^{\mathsf T}$ modulo $q_k$ coordinatewise and divide its residue vector by $q_k$ to obtain the target. Use zero in rank zero. If $mB_i=0$ the projected target is zero. Otherwise its numerator, before reduction, is a nonzero $p$-adic integer given by the polynomial with coefficient row $mB_i$ at $\theta$. Its valuation $s_i(m)$ is finite and can be found by testing successive residues. Once $q_k=p^e$ with $e>s_i(m)$, the reduced projected denominator is $p^{e-s_i(m)}$. Thus its complete-period discrepancy is at most $p^{v+s_i(m)}/q_k$, and its period at most $q_k$. For earlier $e\le s_i(m)$ the same count bound $\ell_k p^{v+s_i(m)}/q_k+q_k$ is trivial. This argument allows a nonprimitive $b$ and prime divisors of the entries of $M$.

Use the preceding deficit scheduler for $h$ types, computing the weights to within $1/(4hk)$ in its rational version. Every overcount is between $-(h-1)$ and $1$. Summation by parts thus costs $O_h(h_K)$ for the aggregate of the types annihilated by any row. The projected scalar tail costs at most $\|m\|_1 B b^{-(n_{k+1}-n)}$. The previous arc estimates, with these constants, give the claimed rates and weak convergence of each projected law. The zero row gives discrepancy one identically. The Fourier coefficient at each $m$ therefore tends to that of the proposed joint mixture. Trigonometric polynomials are uniformly dense in the continuous functions on $\mathbb T^d$, proving joint weak convergence. The sparse modification proof uses a Cartesian grid in $d$ variables, with the root-count argument iterated one variable at a time. Its $O(K^2)$ charge also preserves every fixed Fourier limit.

For a finite row list these Haar mixtures give the convex hull of the indicator vectors of its **flats**. Here a flat is a subset containing exactly the listed rows in its rational linear span, including duplicates and zero rows when appropriate. Annihilation by a rational subspace gives a flat. Conversely, use the common kernel of the rows of a flat as the rational direction space of $H$. Clearing denominators in a basis gives an integer matrix $B$ and recovers exactly the chosen flat. This describes the precise range *within these mixtures*. For the addition triple the only flats give precisely the five vertices above. For the row list $(1),(3)$ the flat hull is the diagonal, but in base two $u=1/3$ has limiting discrepancies $(2/3,1)$, from the two-cycle $\{1/3,2/3\}$ and the fixed point zero. Thus other invariant laws enlarge the range.

For rational rows choose one common positive denominator $Q$ and put $M=QA$ for the given matrix $A$. Construct the freely chosen real inputs as $x=Qu$, so $Ax=Mu$ as **real** vectors before reduction modulo one. Conversely every real input arises this way. This covers simultaneous rational forms, including the original coordinates when the identity rows are appended to $A$. The positive one-prime coefficient bound applies to $u$, so multiplication by $Q$ gives coefficients at most $Q$ for $x$. Division by $Q$ on circle representatives would depend on the chosen lifts.

## The exact spectrum for any number of summands

**Theorem.** For $d\ge1$ prescribe limiting discrepancies $\delta_i$ for $x_1,\ldots,x_d$ and $\delta_{d+1}$ for $S=x_1+\cdots+x_d$. Write $e_i=1-\delta_i$. The full spectrum is described by

$$
0\le e_i\le1,\qquad e_i\le\sum_{j\ne i}e_j\quad(1\le i\le d+1).
$$

Every such prescription has simultaneous all-prefix error $O_{b,p,d}(N^{-1/3})$, uniformly in the vector, with algebraically independent inputs and a uniform computable construction from computable prescriptions.

For necessity put $e_N(z)=1-D_N(z)$. Sharp translation gives $e_N(u+v)\le e_N(u)+e_N(v)$ and $|e_N(u+v)-e_N(u)|\le e_N(v)$. Applying the first inequality repeatedly handles the output $S$. For input $x_i$, add the other summands one at a time in the second inequality to get $e_N(x_i)\le e_N(S)+\sum_{j\le d,\,j\ne i}e_N(x_j)$. These inequalities already hold at each $N$.

The described polytope is the convex hull of the zero vector and the binary vectors with at least two ones. Every listed vector satisfies the inequalities. At a point satisfying $e_i=\sum_{j\ne i}e_j$, a convex decomposition is $(1-e_i)0+\sum_{j\ne i}e_j(\mathbf1_i+\mathbf1_j)$, where $\mathbf1_i$ is the $i$th coordinate vector. Every vertex with all balance inequalities strict must be a cube vertex, since any coordinate strictly between zero and one would allow a small perturbation in both directions. A singleton support violates its own balance inequality. This proves the convex-hull assertion, including $d=1$ where the coordinates must coincide.

To realize a binary vertex, take a line with integer direction $(a_1,\ldots,a_d)$. We want precisely the selected entries of $(a_1,\ldots,a_d,\sum_i a_i)$ nonzero. On a selected support of size $r\ge2$, assign $r-1$ entries the value $1$ and the last the value $-(r-1)$, giving values of sum zero on the support. Negate the output entry to obtain the desired relation, and take all unselected entries zero. Haar on this line projects to Haar at each selected entry and to $\delta_0$ elsewhere. Use the trivial subtorus for the all-zero deficit. The preceding mixture construction proves the theorem for every convex combination. The possible directions form a finite list depending only on $d$.

For an effective version one need not decide whether a computable vector lies on a facet. At step $k$ enumerate rational convex combinations of these finite vertices until their mean vector is certified within $2^{-k}$ of $e$ in maximum norm, using progressively refined rational input approximations and dovetailing comparisons. Density gives termination, including at the vertices. If $w_i(k)$ are the resulting rational type weights, choose a maximizer of $\sum_{j=1}^k w_i(j)-C_i(k-1)$. The true deficits in this scheduling rule sum to one, and the same overcount induction gives bounded differences from the cumulative type weights. Summing those count errors over the types active in a given projection costs a constant depending only on $d$. The cumulative requested activity in that projection differs from $ke_i$ by at most $\sum_{j=1}^k 2^{-j}\le1$. Summation by parts, the period and tail bounds, and sparse polynomial avoidance now apply unchanged. In this algorithm only the projected limiting discrepancies are prescribed.

## A dependency missed by testing the addition triples separately

Put $u=x+y$, $v=x+z$, $w=y+z$. At every cutoff,

$$
D_N(u)+D_N(v)+D_N(w)\le 2+2\min(D_N(x),D_N(y),D_N(z)).
$$

In fact $D_N(u+v)\ge D_N(u)+D_N(v)-1$, and $u+v=2x+w$ gives $D_N(2x)\ge D_N(u+v)+D_N(w)-1$. The preimage of a half-open arc under doubling consists of two arcs whose lengths sum to the length of the original arc, so $D_N(2x)\le2D_N(x)$. Permute $x,y,z$ to finish. For the six listed forms take desired discrepancies zero for $x,y,z$ and one for each pair sum. Each of the three individual addition triples $(0,0,1)$ is attained by our theorem. Together they would give $3\le2$. The obstruction applies to every orbit law, including laws outside the Haar-mixture family.

## The full finite-form spectrum by polyhedral approximation

There is also a general membership criterion, without a Haar-mixture assumption. Fix $b$ and a nonempty finite integer row list $M$. Denote the spectrum of simultaneous full limits by $S$ and the invariant probability laws for $u\mapsto bu$ on $\mathbb T^d$ by $\mathcal M_b$. Write $D(\nu)=\sup_I|\nu(I)-\lambda(I)|$ for circle probability laws. Then

$$
S=\bigl\{\,\bigl(D((\chi_m)_*\mu)\bigr)_{m\in M}:\mu\in\mathcal M_b\,\bigr\}.
$$

For necessity take a weakly convergent subsequence of the joint empirical laws. Its limit is invariant by telescoping. Each character is continuous. To see weak continuity of $D$ at any law, choose a circle grid of mesh at most $\eta$ avoiding its atoms at the endpoints. The positive discrepancy lies between the maximum grid-arc excess and that maximum plus $2\eta$, by enlargement. The finitely many grid masses converge, and $\eta$ is arbitrary. For sufficiency lift an invariant law to the digit-vector full shift by the coordinatewise terminating convention on $[0,1)$. This measurable digit map intertwines the dynamics. Every invariant full-shift law has a generic sequence by the specification theorem. Its continuous radix projection to the torus gives a generic point for the desired law. In particular $S$ is compact and path connected by continuous projection of the convex compact set of invariant laws. [Sigmund, *On dynamical systems with the specification property*](https://doi.org/10.1090/S0002-9947-1974-0352411-X) · [Madritsch and Mance, an explicit generic-sequence construction](https://arxiv.org/abs/1206.4950)

**Finite approximation theorem.** For every $L\ge1$ one can compute a finite union of rational polytopes $S_L$ with

$$
d_{\mathrm H,\infty}(S,S_L)\le 2b^{-L}\max_{m\in M}\|m\|_1.
$$

Here $d_{\mathrm H,\infty}$ is the two-sided Hausdorff distance in the maximum norm. Thus a vector belongs to $S$ exactly when its distance to $S_L$ is at most the right side for every $L$. In particular an infeasible rational prescription has a finite certificate. The number of word masses is $b^{dL}$ before subdividing into polytopes.

To construct $S_L$, take the alphabet of $d$-component base-$b$ digits. Assign nonnegative masses $f_w$ summing to one to its words of length $L$. For each word $v$ of length $L-1$ impose $\sum_a f_{av}=\sum_a f_{va}$. These are the stationary word distributions. Indeed such masses give flows on the directed graph with each word pointing from its prefix to its suffix of length $L-1$. A nonzero balanced flow contains a positive directed cycle. Subtract the smallest edge mass on the cycle from all its edges and repeat. At least one edge disappears at each step. The resulting positive combination of cycles, normalized by their lengths, gives a mixture of periodic symbolic laws with exactly those word masses. This works at $L=1$ with one empty vertex. Conversely every invariant symbolic law satisfies the balance equations. [Bochi and Zhang, Propositions 3.2 and 3.5, for the binary graph](https://arxiv.org/pdf/1501.00961)

Put $Q=b^L$. For each word $w$, let $j(w)$ be its vector of $L$-digit integer numerators and place mass $f_w$ at $j(w)/Q$. For row $m$, compute the residue $r_w=m\cdot j(w)\bmod Q$. For $a,c\in\{0,\ldots,Q-1\}$ put $s=(c-a)\bmod Q$ in the same residue range. The grid-law discrepancy is

$$
\max_{a,c}\left(\sum_{w:\,(r_w-a)\bmod Q\,\le s} f_w-\frac{s}{Q}\right).
$$

The inclusive cyclic range accounts for both extreme atoms. Arcs enclosing that range can have length arbitrarily close to $s/Q$ from above. Conversely a positive-excess arc contains grid points and can be shortened to the span from its first to its last grid point without losing mass in the limiting supremum. This proves the formula, including $a=c$. It is a finite maximum of rational affine functions of the masses. For each choice of a maximizing range in each row, intersect the flow polytope with the corresponding weak linear inequalities. The joint discrepancy map is affine on that cell. The union of the rational polytope images of these cells is $S_L$.

Each infinite digit sequence is within $1/Q$ in each circle coordinate of its first-$L$-digit truncation, even for the noncanonical expansion of zero. Under $m$ the paired circle distance is at most $\|m\|_1/Q$. Coupling the two laws by the sequence and enlarging arcs both ways changes the scalar discrepancy by at most $2\|m\|_1/Q$. Every invariant torus law has a digit lift as above, and every finite feasible flow extends to an invariant symbolic law by the cycle decomposition. The two directions give the asserted Hausdorff estimate. Compactness of $S$ then gives the membership test by letting $L$ grow.

## Scope and prior work

Classical specification and generic-sequence theorems already realize the joint invariant measures in the qualitative characterization, including each of the five-component mixtures. Bergelson and Downarowicz give bounds for lower and upper entropy under addition in Proposition 4.9 and sharpness examples in §4.3. Their Theorem 4.29 treats universal preservation of normality. Those results concern entropy and normality. Here the coordinates of the spectrum are the numerical extreme interval discrepancies. [Sigmund (1974)](https://doi.org/10.1090/S0002-9947-1974-0352411-X) · [Madritsch and Mance](https://arxiv.org/abs/1206.4950) · [Bergelson and Downarowicz, authors' text](https://arxiv.org/html/2506.12929v1)

The [Phase 18 construction](../phase18/programming.md) supplies the scalar programming method, positive coefficient recurrence, scheduler estimate and period calculation. What the exact triple adds is the matching five-vertex description and a simultaneous one-prime arithmetic realization, uniform at every prefix and at every boundary triple. The polynomial avoidance proves effective algebraic independence within that same rate class. Avoidance of algebraic relations in perfect sets has classical precedents. For any number of summands the polygon inequalities for the deficits are sufficient as well as necessary. For general finite forms the arithmetic construction realizes joint Haar mixtures, and the word-flow approximation gives an explicit two-sided error for the full spectrum. The underlying circulation and locally constant rotation polytopes have established descriptions. We found no statement of the quantitative discrepancy spectrum in these sources. [Mycielski (1964), original article](https://matwbn.icm.edu.pl/ksiazki/fm/fm55/fm55112.pdf) · [Ziemian (1995), original article](https://matwbn.icm.edu.pl/ksiazki/fm/fm146/fm14628.pdf) · [Bochi and Zhang, §3](https://arxiv.org/pdf/1501.00961)

## Exact finite checks

Run the [standard-library certificate](../../scripts/phase19_addition.py) from the repository root.

~~~sh
python -B scripts/phase19_addition.py
~~~

It checks all 2,197 triples on the grid of twelfths, including the 1,105 admissible ones, and 2,448 projected cubic-series prefixes using exact fractions. For $b=2$, $p=3$ and limit triple $(1/4,1/2,3/8)$, at $N=100$ the discrepancies of the **infinite** series lie in the intervals below, in table coordinate order. The calculation encloses the omitted tails after the sixth insertion.

$$
10^{-6}[469999,470000],\qquad
10^{-6}[189722,189723],\qquad
10^{-6}[318888,318889].
$$

The general sum check decomposes 1,153 feasible prescriptions for one through four summands. Additional checks certify five successive polynomial exclusions (one requires extending past the override), exercise 7,920 rational prefixes for the six-form inequality, and compare subtorus projections at seven prime-power depths. Four levels of stationary word flows include a wrapping projection and the all-ones representation of zero. These computations exercise finite instances of the paper results.

For the exact three-coordinate spectrum there is also a cluster-set version. Every nonempty compact connected subset $F$ of the feasible polytope occurs as the cluster set of the three discrepancies. The five weight formulas depend continuously on the triple, so the map sending a point of $F$ to its five-vertex invariant mixture has a compact connected image. The specification theorem for the toral endomorphism realizes exactly this set of empirical limits. Continuity of the three projected scalar discrepancies then gives precisely $F$. Connectedness and compactness are necessary because consecutive empirical averages have vanishing distance. This qualitative corollary does not assert a rate when the target itself varies. For effective height-uniform control of joint boxes with full Haar target see the [algebraic direction construction](joint-rate.md).
