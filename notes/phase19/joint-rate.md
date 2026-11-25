# A polynomial rate for joint boxes on a full torus

Fix $d\ge2$, $b\ge2$, and an odd prime $p\nmid b$. There are computable positive rational-coefficient series $x_1,\ldots,x_d$ on the **same cubic schedule** such that the joint radix samples in $[0,1)^d$ satisfy
$$
 D_N^{\mathrm{box}}(x_1,\ldots,x_d;b)
 \ll_{b,p,d} N^{-1/(3d+1)}(\log(2N))^d .
$$
Here boxes are products of half-open intervals and the reference measure is $d$-dimensional Lebesgue measure. This estimate is for a full torus. It does not assert uniform convergence of box masses to an atomic subtorus mixture at moving endpoints.

Take $\ell=2$, different from the odd prime $p$, and put $F(X)=X^d+\ell X+\ell p$. Eisenstein at $\ell$ gives irreducibility; Hensel lifting the simple root $0\bmod p$ gives an effectively computable root $\theta\in\mathbb Z_p$. For each $k\ge1$ set $q_k=p^{1+\lfloor\log_p k\rfloor}$ and let $v_{j,k}$ represent $\theta^{j-1}\bmod q_k$ in $[0,q_k)$. At $n_k=t k^3$, $t=\operatorname{ord}_p(b)$, program state $v_{j,k}/q_k$ in coordinate $j$ by the positive recurrence of Phase 18. The sum in each coordinate is then determined by explicitly computable rationals of size at most one. [State recurrence](../phase18/programming.md#b1-the-exact-coefficient)

For a nonzero integer frequency vector $h$ of height $\max_j|h_j|\le H$, put $P(X)=\sum_{j=1}^d h_jX^{j-1}$. The integer resultant $\mathrm{Res}(F,P)$ is nonzero, since $\deg P<d$. The product over the fixed complex roots bounds its magnitude by $C_{p,d}H^d$. All the roots of $F$ in a splitting field over $\mathbb Q_p$ are integral. The same product there shows that the resultant is divisible by $p^{v_p(P(\theta))}$, whence
$$
 p^{v_p(P(\theta))}\le C_{p,d}H^d .
$$
This replaces the potentially very large height-dependent valuation losses of a Liouville direction with a polynomial bound.

Write $a=v_p(b^t-1)$. At all indices $k>p^a C_{p,d}H^d$ the scalar rational model for the character $h$ has reduced denominator $p^e$ with $e>a$, since $q_k>k$. Its complete-period exponential sum vanishes: the complete orbit is a union of translated equally spaced grids of size at least $p$. Its period is at most $q_k\le pk$. Thus an arbitrary initial portion of this block, including one cut off at time $N$, costs at most $q_k$ in absolute exponential sum. All earlier blocks together cost $O_{b,p,d}(H^{3d})$ by the cubic schedule. Through $N$ there are $K=O_b((N/t)^{1/3}+1)$ blocks with insertions, and the sum of the possible unfinished-period costs is $O_{b,p}(K^2+1)$. In each block the sum over all its shifts of the absolute real tail in any one coordinate is $O_b(1)$ by summing the geometric tail from the next insertion. Thus transferring the projected exponential sum to the actual samples costs $O_{b,d}(H(K+1))$, uniformly in $h$. The finite interval preceding the first insertion has bounded cost. [Grid proof](grids.md)

The Erdős–Turán–Koksma inequality bounds star discrepancy by a dimension-dependent constant times $1/H$ plus the sum of normalized character errors for $0<\|h\|_\infty\le H$, weighted by $\prod_j 1/\max(1,|h_j|)$. These weights have total $O_d((\log(2H))^d)$. The preceding estimates therefore give
$$
 D_N^*\ll_{b,p,d} H^{-1}+(\log(2H))^d
     (H^{3d}/N+N^{-1/3}+H N^{-2/3}).
$$
Take $H=\max(1,\lfloor N^{1/(3d+1)}\rfloor)$. Inclusion–exclusion at the corners of a general box bounds its error by $2^dD_N^*$, proving the assertion. This is a multidimensional character argument independent of the scalar translation identity. The classical generic-point theorem gives qualitative realizations; the rate and explicit choice of arithmetic directions are the additional conclusions here. [Kuipers and Niederreiter, *Uniform Distribution of Sequences*, Chapter 2, §2](https://web.maths.unsw.edu.au/~josefdick/preprints/KuipersNied_book.pdf)

The construction controls linear characters and boxes. Polynomial closure requires the independent leading-pole arguments in the [nonlinear proof](nonlinear.md). The exponent is the result of balancing this estimate; no optimality is asserted. [Finite Hensel and flow checks](../../scripts/test_phase19_forms.py)
