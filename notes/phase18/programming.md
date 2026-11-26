# Programming rational radix orbits

For every integer base $b\ge2$ and every $\delta\in[0,1]$ there is a positive rational-coefficient series $x=\sum_{k\ge1}c_k b^{-tk^3}$ whose **extreme interval discrepancy** satisfies

$$
|D_N(x;b)-\delta|\ \le\ C_{b,p}N^{-1/3}\qquad(N\ge1).
$$

Here $p$ is any odd prime coprime to $b$, $t$ is the order of $b$ modulo $p$, and every $c_k$ belongs to $(0,1]$ and has reduced denominator a power of $p$. The constant is uniform in $\delta$. The canonical coefficients below give an irrational number at both endpoints and throughout the interval. Computable inputs have a uniform computable variant. A sparse choice of coefficients also gives transcendental realizations with the same rate.

The all-prefix discrepancy and limit-set conclusions have paper proofs. The [positive recurrence and its dense representation](../../NormalityChecker/Phase18Synthetic.lean) are also kernel-verified. The [exact arithmetic checks](../../scripts/phase18_programming.py) exercise finite instances. The prime-power period estimate is the only arithmetic input from [the principal family](principal.md). Write $\mathbb T=\mathbb R/\mathbb Z$, $T(x)=bx\bmod 1$, and $\lambda$ for normalized length. For a probability measure $\mu$ set $D(\mu)=\sup_I|(\mu-\lambda)(I)|$, and write $D_N(x;b)$ for $D$ of the empirical measure of $T^n x$, $0\le n<N$. Here $I$ ranges over half-open circle arcs. This equals the usual supremum over ordinary intervals in $[0,1)$, since a wrapping arc has an ordinary interval as complement. Complementation also lets us take the supremum of the positive excess. Base-$b$ normality is equivalent to $D_N\to0$.

## B1. The exact coefficient

Let $0=n_0<n_1<\cdots$ be integers, let $u_0=0$, and choose any rational $u_k\in[0,1)$. Set $R_0=0$. At step $k$, put $B=b^{n_k-n_{k-1}}$ and take $c_k$ to be the representative in $(0,1]$ of $u_k-Bu_{k-1}$ modulo one. Then

$$
R_k=B R_{k-1}+c_k
    =b^{n_k}\sum_{i=1}^k c_i b^{-n_i},
\qquad \{R_k\}=u_k .
$$

Indeed, $R_0-u_0$ is integral and $R_k-u_k=B(R_{k-1}-u_{k-1})+(Bu_{k-1}+c_k-u_k)$ is integral by construction. This proves existence and uniqueness for the given positive coefficient convention, including $c_k=1$ when the residue vanishes.

Here is the **reduced** denominator. Write $u_{k-1}=a/d$ and $u_k=a'/d'$ in lowest terms, including $0=0/1$. Put $g=\gcd(B,d)$, $d_*=d/g$, $a_*=Ba/g$, $L=\operatorname{lcm}(d_*,d')$, and $v=a'(L/d')-a_*(L/d_*)$. Then

$$
\operatorname{den}(c_k)=\frac L{\gcd(L,v)}.
$$

This follows by reducing $v/L$ modulo one. In particular, if a prime occurs to unequal exponents in $d_*$ and $d'$, the larger exponent survives, since just one of the two scaled numerators is a unit at that prime. At equal positive exponents further cancellation depends on the numerators. For an off-radix prime $p$ and targets of reduced denominators $p^i,p^j$ one has $d_*=d$, and the coefficient denominator is $p^{\max(i,j)}$ if $i\ne j$. The formula also covers all equal-depth cancellations and two consecutive zero targets.

Each summand has a dense positive representation. For $h=n_k-n_{k-1}$ its group consists of $c_k(b-1)b^{-m}/(b^h-1)$ at every position $n_{k-1}<m\le n_k$. Summing the finite geometric series gives exactly $c_k b^{-n_k}$. The total is bounded by $\sum_{m\ge1}b^{-m}=1/(b-1)$, so grouping preserves its value.

## G1. A finite certificate for every observation window

Suppose an absolutely summable raw series has been partitioned into groups with values $g_i$. A group may itself be infinite. Take model values $s_i$, for example $c_i b^{-n_i}$, and write $x=\sum_i g_i$. For $n_k\le n<n_{k+1}$ put

$$
y_n=\left\{b^n\sum_{i\le k}s_i\right\}.
$$

Assume a certificate bounds the number of $n<N$ with circle distance $d(T^nx,y_n)>\epsilon$ by $E$. One sufficient per-position bound is

$$
d(T^nx,y_n)
\le \left\| b^n\sum_{i\le k}(g_i-s_i)\right\|
      + b^n\sum_{i>k}|g_i|,
$$

where $\|v\|$ is distance to the nearest integer. The identity behind this bound uses absolute convergence, including for a partition into infinite groups. Certified intervals for group errors must control their **shifted accumulated error**. Alternatively one can bound the actual signed residual directly. If a model uses only part of a raw group at a cutoff, its omitted part belongs in this residual.

Split the $N$ model positions into active positions $A$ and $Z$ remaining positions, with $|A|+Z=N$. Suppose for **every** arc $I$,

$$
\left|\#\{n\in A:y_n\in I\}-|A|\,|I|\right|\le H.
$$

Let $\rho$ be the empirical probability measure of the remaining model positions (arbitrary if $Z=0$). Then for $N>0$ and $\epsilon\ge0$,

$$
\left|D_N(x;b)-\frac ZN D(\rho)\right|
\le \frac{H+E}{N}+2\epsilon. \tag{1}
$$

To see both directions, put $\nu=(|A|\lambda+Z\rho)/N$. The model count of each arc differs from $N\nu(I)$ by at most $H$. Enlarge an arc $I$ at each end by $\epsilon+\eta$ for any $\eta>0$, taking the whole circle when necessary. Every good observation in $I$ has model in the enlarged arc, and every good model in $I$ has observation in the enlargement. The first inclusion bounds the empirical excess on $I$ by $D(\nu)+(H+E)/N+2(\epsilon+\eta)$. The second bounds the excess of $\nu$ by the empirical discrepancy plus the same error. Take suprema and let $\eta\downarrow0$. Finally $D(\nu)=(Z/N)D(\rho)$ by linearity of the excess. The enlargement also covers a model and an observation lying on opposite sides of zero.

With $y_n=0$ at all retired positions, $D(\rho)=1$ by arbitrarily short arcs about zero. Thus (1) gives the matching upper and lower bounds for $D_N-Z/N$. More generally, if the reduced denominators at the remaining positions are at most $Q$, their models lie in a finite set of size $M\le\sum_{d=1}^Q d$. Some atom has mass at least $1/M$ when $Z>0$. Consequently

$$
\frac{Z}{MN}-\eta_N\ \le\ D_N(x;b)\ \le\ \frac ZN+\eta_N,
\qquad \eta_N=(H+E)/N+2\epsilon .
$$

If $\eta_N\to0$ and $Q$ is fixed, vanishing density of these positions is necessary and sufficient for normality. The upper bound need not be an equality for a general finite orbit. This criterion also applies when $H$ comes from a short-orbit estimate instead of complete periods. For a translated observation window $[M,M+N)$ the proof is identical with all counts restricted to that window. In the period bounds below one then takes $\ell_k$ to be its overlap with the block and starts the orbit at the first observed phase.

## B2. Active and retired intervals

Number the observation intervals $[n_k,n_{k+1})$ by $k\ge0$. Write $h_k=n_{k+1}-n_k$ for their lengths and $\ell_k=\max(0,\min(N,n_{k+1})-n_k)$ for the lengths observed through a prefix of size $N$. The model is $y_{n_k+j}=T^j u_k$ for $0\le j<h_k$. Retire block zero and any chosen subsequent blocks by setting $u_k=0$. In an active block choose $u_k=a_k'/q_k$ in lowest terms with $q_k=p^{e_k}$, $e_k\ge1$. The simplest numerator is one.

We use the following form of the [prime-power period lemma](principal.md). For an odd prime $p\nmid b$, set $v=v_p(b^t-1)$. A complete orbit through any unit numerator modulo $p^e$ has period $P=t p^{\max(e-v,0)}\le p^e$ and extreme discrepancy at most $d_e=\min(1,p^{v-e})$. For $e>v$ the orbit is a union of equally sized residue classes modulo $p^v$. The bound applies to every arc and every initial phase, including when $b$ is not primitive modulo $p$. For $e\le v$ the displayed discrepancy bound is simply one.

There are $\lfloor\ell_k/P_k\rfloor$ complete periods in each observed active piece and $r_k=\ell_k\bmod P_k$ other positions. Each complete period has count error at most $P_k d_{e_k}$, and the remaining count has error at most $r_k$. Thus we can use

$$
H_N=\sum_{k\ {\rm active}}\big((\ell_k-r_k)d_{e_k}+r_k\big). \tag{2}
$$

Only finitely many terms are nonzero. For $B_0=b/(b-1)$, positivity, $c_i\le1$ and distinct insertion positions give the real tail estimate

$$
0< b^n\sum_{i>k}c_i b^{-n_i}\le B_0 b^{-(n_{k+1}-n)}.
$$

Given $\epsilon>0$, choose an integer $W\ge0$ with $B_0b^{-W}\le\epsilon$. Count only observed positions with $n_{k+1}-n<W$ in $E_N$. If $K$ is the largest $k$ with $n_k\le N$, then $E_N\le (K+1)W$. This includes the first block and a partially observed final block, even when that block has a very distant right endpoint.

For any schedule and mask, (1) with (2) gives $D_N=Z(N)/N+o(1)$ if $H_N=o(N)$ and some $\epsilon_N\to0$ has $E_N=o(N)$. On the good retired positions the true orbit is within $\epsilon_N$ of zero. On the active positions the count differs from $(N-Z)|I|$ by at most $H_N+E_N+2\epsilon_N(N-Z)$, by the same enlargement and complementation. Thus active positions of positive limiting proportion have uniform conditional distribution. The unnormalized estimate still applies when their proportion tends to zero.

One convenient sufficient condition is $n_k/k\to\infty$ and, along active $k\to\infty$,

$$
e_k\to\infty,\qquad P_k=o(h_k),\qquad P_k=o(n_k).
$$

Indeed, the complete-block errors are $o(h_k)$ term by term, hence $o(N)$ in total after separating any fixed initial segment. The unfinished block contributes at most $\ell_K d_{e_K}+P_K=o(N)$ if active. A fixed finite active set causes only bounded count error. Choose $W=\lfloor\sqrt{N/(K+1)}\rfloor$ and $\epsilon_N=B_0b^{-W}$. These hypotheses are sufficient tests for (2) and can be weakened whenever shorter pieces have a better bound.

Two examples show why the qualifications matter.

- With $n_k=2k$, $b=2$, and every target zero, all coefficients are one and $x=1/3$. Its orbit alternates $1/3,2/3$ and its limiting discrepancy is $2/3$, although every model position is retired. The omitted real tail has positive size on a positive density of positions.
- Fix $n_1=1$, set $q_k=p^{n_k^2}$, $n_{k+1}=n_k+q_k^2$, and program $u_k=1/q_k$. Then $q_k\to\infty$ and $P_k/h_k\to0$. At cutoff $n_{k+1}$ the last complete block covers proportion tending to one and has count error $o(h_k)$ by (2) and the tail bound. But its first $\lfloor\frac12\log_b q_k\rfloor$ positions have models at most $q_k^{-1/2}$ and uniformly vanishing tails. They outnumber the preceding $n_k$ positions by a factor tending to infinity. At these intermediate cutoffs $D_N\to1$. Full-gap uniformity alone does not control unfinished intervals.

## B3. The cubic construction and an explicit error

Set $n_k=tk^3$, $u_0=0$. For $k\ge1$ let

$$
e_k=1+\lfloor\log_p k\rfloor,\qquad
q_k=p^{e_k},\qquad
a_k=\lfloor k\delta\rfloor-\lfloor(k-1)\delta\rfloor .
$$

Retire the block if $a_k=1$ and choose $u_k=1/q_k$ otherwise. This assigns the mask at the **left** endpoint $n_k$ and gives $k<q_k\le pk$, including powers of $p$. For $K\ge1$ with $tK^3\le N<t(K+1)^3$, set $W=\lceil\log_b(B_0(K+1))\rceil$, $\epsilon=1/(K+1)$. Since $h_k=t(3k^2+3k+1)\le7tk^2$ for $k\ge1$, the active error (2) is at most

$$
H_N\le\sum_{k=1}^K(h_k p^v/q_k+q_k)
\le(7tp^v+p)K(K+1)/2.
$$

More generally, suppose $|\sum_{i=1}^j(a_i-\delta)|\le C$ for all $j$. For $k=1,\ldots,K-1$, summation by parts writes the completed weighted error as the last prefix error times $h_{K-1}$ minus the sum of earlier prefix errors times successive differences of $h$. It has absolute value at most $2C h_{K-1}$ since the weights increase. For $K=1$ that sum is empty. The unfinished weight is at most $h_K$ and the initial contribution costs at most $t$. We obtain, at **every** such cutoff,

$$
|D_N(x;b)-\delta|
\le \frac{(7tp^v+p)K(K+1)/2+(K+1)W+t+(2C+1)h_K}{N}
       +\frac{2}{K+1}. \tag{3}
$$

The specified floor word has $C=1$. Since $N\asymp_t K^3$, (3) is $O_{b,p}(N^{-1/3})$. For $1\le N<t$ the bound $|D_N-\delta|\le1$ suffices. This proves an ordinary discrepancy **limit** at every value. In the [signed Stoneham spectrum](../attainable-shell-histories.md), geometric shells give a restricted set of upper discrepancies. There a single shell can have positive asymptotic weight, whereas here $h_k/n_k\to0$.

For example, take $b=2$, $p=3$, $\delta=2/5$. The first five insertions have exponents $2,16,54,128,250$. Their target residues are $1/3,1/3,0,1/9,0$ and the positive coefficients are $1/3,1,2/3,1/9,5/9$. At the second insertion $2^{14}/3$ already has the target residue, so the coefficient is exactly one. At the fifth insertion $2^{122}\equiv4\pmod9$, giving $5/9$ to retire the prefix.

The orbit measures converge weakly on the circle to $(1-\delta)\lambda+\delta\,\delta_0$, where $\delta_0$ denotes unit mass at zero. Indeed the active model counts have uniform error $o(N)$, and almost all of the retired mass lies in any fixed neighborhood of zero. Equivalently, test against continuous functions and use uniform continuity. For $\delta<1$ the limit has a nonzero Lebesgue component. Every rational orbit is eventually periodic, so its limit is finitely supported. For $\delta=1$ all coefficients equal one. The base-$b$ expansion has isolated ones at $tk^3$ and unbounded gaps of zeros, which excludes eventual periodicity and hence rationality. The discrepancy value one by itself would allow a rational number, for example zero. The all-active endpoint $\delta=0$ is normal.

### Computability at integer floor boundaries

For a specified rational $\delta$ use exact integer division. For a specified computable irrational $\delta$, refining rational enclosures of $k\delta$ eventually determines each floor for $k\ge1$. There is no uniform exact floor test from arbitrary Cauchy names at rational boundaries. A uniform construction for the limiting value instead computes rational $d_k\in[0,1]$ with $|d_k-\delta|\le2^{-k}$, sets $S_0=0$, $S_k=\sum_{i=1}^k d_i$, and uses $a_k=\lfloor S_k\rfloor-\lfloor S_{k-1}\rfloor$. These are bits and $|\sum_{i=1}^k a_i-k\delta|\le2$, so (3) applies with $C=2$. Only rational floors occur. The tail after $K$ insertions has absolute size at most $B_0 b^{-n_{K+1}}$. This yields a Cauchy name for $x$ uniformly from one for $\delta$.

### Transcendental realizations

One can change the mask freely at indices $k=2^j$ without changing the rate or limiting measure. Through cutoff $N$ the changed weight is at most $7t\sum_{2^j\le K}4^j\le(28t/3)K^2$ and the active error estimate is uniform in the mask. Distinct choices at any sufficiently large such $k$ give distinct numbers. At position $n_k$ their target states are separated by $1/q_k$, while each true orbit lies within $B_0b^{-h_k}$ of its own target. Eventually $2B_0b^{-h_k}<1/q_k$. Thus every $\delta$ has continuum many realizations with (3) plus this extra weight divided by $N$. All but countably many are transcendental.

For computable $\delta$ one can even select a **computable transcendental** realization. Effectively list the real algebraic numbers $\alpha_j$, repetitions allowed. For instance, enumerate integer polynomials with rational intervals of strict sign change and bisect each such interval, handling a zero midpoint exactly. Each algebraic real occurs by taking an isolating interval of its separable minimal polynomial. Assign the $j$th entry a distinct successive power of two $k$ large enough that $B_0b^{-h_k}<1/(8q_k)$. Compute a rational approximation to $b^{n_k}\alpha_j$ within $1/(16q_k)$. Choose the farther of the two targets $0,1/q_k$ in circle distance from this rational, with either tie resolved deterministically. By the triangle inequality the chosen target is at least $1/(2q_k)-1/(16q_k)$ from $T^{n_k}\alpha_j$. The true orbit at $n_k$ still differs from it, independently of all future choices. The sparse indices and the resulting coefficients are computable, and $x$ differs from every $\alpha_j$. This selection proves transcendence for the variant. The preceding proofs establish irrationality for the canonical cubic floor word without determining its algebraic degree.

## B4. Periodic components and irregular limits

**Finite mixtures.** In a cubic block choose any of the following models. A periodic rational point of period $P$ models the uniform measure on its cycle with arc count error at most $\ell_k\bmod P$. Zero is its one-point special case. An orbit of increasing prime-power denominator models $\lambda$ with count error (2), which applies to every unit numerator in every coset covered by the period lemma. More generally a periodic orbit of discrepancy $d$ models $\lambda$ with error at most $\ell_k d+P$. Thus sufficiently fine cycles can replace the prime-power orbits whenever these errors sum to $o(N)$. Finite cycles with the same denominator can yield distinct components when their multiplicative cosets differ.

In general let $\mu_k$ be the intended probability law for block $k$, with $\mu_0=\delta_0$. Suppose every arc has model count error at most $H_k(\ell_k)$ relative to $\ell_k\mu_k(I)$. Then for $\nu_N=N^{-1}\sum_k\ell_k\mu_k$ the proof of (1) gives

$$
|D_N-D(\nu_N)|\le N^{-1}\bigg(E_N+\sum_k H_k(\ell_k)\bigg)+2\epsilon .
$$

If these bounds tend to zero with $\epsilon\to0$, the true empirical measures and $\nu_N$ also have the same weak limit points along corresponding subsequences. Indeed the models differ from $\nu_N$ on every arc by $o(1)$. For any continuous test function approximate it uniformly by a step function on a fixed finite arc partition, then use the circle tail bound and uniform continuity for the true observations.

To prescribe finite weights $w_i\ge0$ summing to one, after $k-1$ choices with counts $C_i$ choose a type maximizing $kw_i-C_i$. These deficits sum to one. The chosen deficit is positive, so the updated overcount $C_i(k)-kw_i$ is at most one for that type. The others' overcounts can only decrease. Induction and the zero sum of the overcounts give $-(m-1)\le C_i(k)-kw_i\le1$ for $m$ types. The same weighted sum by parts used in (3) gives time proportions $w_i+O_m(K^2/N)$ with the unfinished block included (the implicit constant also depends on $t$). For fixed periodic types and cubic active types as in B3 the true measures therefore converge to the indicated mixture. Their scalar discrepancies approach its discrepancy at rate $O_{b,p,m,P_{\max}}(N^{-1/3})$, where $P_{\max}$ bounds the periods of the fixed cycles.

**All pairs of extreme discrepancies.** Fix $0\le\alpha\le\beta\le1$. Put $K_1=2$, $K_{j+1}=K_j^2$. Define desired rates $\theta_k$ equal to $\alpha$ for odd $j$ and $\beta$ for even $j$ on $[K_j,K_{j+1})$, taking $\theta_1=\alpha$. Use mask bits formed by successive floors of $\sum_{i=1}^k\theta_i$. For every prefix the unweighted rounding error has magnitude at most one. The weighted error through $N$ is at most $t+3h_K$ by summation by parts, now applied to $a_i-\theta_i$. Every weighted average of the $\theta_i$ is between $\alpha$ and $\beta$. At the ends $N=tK_{j+1}^3$ the preceding stages have weight at most $tK_j^3=o(N)$, so both endpoints are achieved as subsequential limits. By (1)–(2), $D_N-Z(N)/N=O_{b,p}(N^{-1/3})$ uniformly. Hence $(\liminf D_N,\limsup D_N)=(\alpha,\beta)$. All intermediate values occur since $Z(N)/N$ changes by at most $1/(N+1)$ per step. For computable endpoints use rational approximations within $2^{-i}$ before each addition as above. This gives the same conclusion from arbitrary Cauchy names.

### Which weak limit sets can occur?

Allow arbitrary rational targets in B1. On **the circle**, the sets of weak limit points of the resulting radix-orbit measures, already for cubic insertions, are exactly the nonempty compact connected subsets of the $T$-invariant probability measures. Here the coefficient denominators may use many primes. The more restrictive one-prime construction above supplies the explicit rate for its specified mixtures.

For necessity, probability measures on the compact circle form a compact metrizable space in the weak topology. For concreteness use the bounded Lipschitz distance, the supremum of integral differences over real functions of supremum norm and Lipschitz constant at most one. This metrizes weak convergence by uniform approximation and compactness of the test family. For an empirical measure $\mu_N$ and any continuous $f$, the integral of $f\circ T-f$ telescopes to $(f(T^Nx)-f(x))/N$. Every limit is invariant. Successive empirical measures are at distance at most $2/(N+1)$. Their cluster set is nonempty and compact. If it were disconnected, two disjoint nonempty compact pieces would have positive separation. The measures would eventually lie in their disjoint small neighborhoods, visit both infinitely often, and have to cross their separation in a single step. This contradicts the step bound.

For sufficiency we give the construction, including the two approximation facts it uses.

1. **Periodic rational orbit measures approximate every invariant measure $\mu$.** For a desired tolerance, retain finitely many tests forming a uniform net of the bounded Lipschitz family. Choose integers $r$ large and $L$ large compared with $r$. By invariance, the vector of integrals of the tests is the expectation under $\mu$ of their length-$L$ orbit averages. To approximate this expectation by a finite rational convex combination, partition the bounded range into small boxes, choose a representative of each box of positive mass, and approximate the weights by rationals summing to one. Concatenate the first $L$ base-$b$ digits of the representative starting points, repeating each word in the multiplicity of its rational weight. Repeat the concatenation periodically to obtain a rational point of period at most the word length $M$ (denominator dividing $b^M-1$). On all but at most $r$ offsets of each word, the new and original orbit have at least $r$ matching initial digits and circle distance at most $b^{-r}$. The remaining offsets have test difference at most two. Thus the error from concatenation is at most $b^{-r}+2r/L$, plus the box, weight and finite-net errors. These can be made arbitrarily small. Use the terminating digit convention for a base-$b$ rational representative. An all-$(b-1)$ periodic word represents zero on the circle and satisfies the same distance bound.
2. **A compact connected metric set $F$ admits a sequence $\mu_j$ with cluster set $F$ and successive distances tending to zero.** Fix a point of $F$. For any $\eta>0$ two points can be joined by a finite chain in $F$ of steps $<\eta$, since each chain-reachability class and its complement are relatively open. Starting and ending at the fixed point, visit a finite $1/s$-net using such chains with $\eta=1/s$, for $s=1,2,\ldots$. Concatenate these finite lists, including at least one point per list.

Choose a rational cycle with law $\pi_j$ within $1/j$ of $\mu_j$ and period $P_j$. Select integers $K_j$ with $K_1\ge\max(2,P_1)$ and $K_{j+1}\ge\max(K_j^2,P_{j+1})$. For $K_j\le k<K_{j+1}$ use a point on that cycle as $u_k$ in each block. Earlier targets can be zero. In an observed piece of length $\ell_k$ the difference between the sum of a bounded Lipschitz test and $\ell_k\int f\,d\pi_j$ is at most $2P_j\le2k$, by division into periods. Summing the errors including the unfinished piece gives $O(K^2)$ through $N$. The tail adds at most $N\epsilon+2E_N$ on such tests. The measures therefore track the time-weighted cycle laws with bounded Lipschitz error $O_{b,t}(N^{-1/3})$ using the cubic tail choices.

At the end of stage $j$ the weight of earlier stages is at most $(K_j/K_{j+1})^3$, so those boundary measures approach $\mu_j$ in distance. Throughout stage $j$ the weighted law is a convex combination of the previous boundary law and $\pi_j$. Both are within $o(1)$ of $\mu_j$, using the vanishing steps between successive targets. Convexity of the test bound proves that every limit lies in $F$. The boundary subsequences attain every point of $F$, proving the converse.

This construction uses the usual periodic-word approximation for the full shift and the concatenation principle of symbolic dynamics. The generic-point and connected-limit-set phenomena have classical specification precedents. One source is [Sigmund, *On dynamical systems with the specification property* (1974)](https://doi.org/10.1090/S0002-9947-1974-0352411-X). Here B1 converts the target orbits into positive coefficients on a fixed arithmetic schedule. The elementary proof above makes the cost of resets and unfinished pieces explicit.

For completeness, weak convergence $\mu_i\to\mu$ on the circle implies **scalar** convergence $D(\mu_i)\to D(\mu)$ even with atoms. Rotate a finite equally spaced grid of mesh $\le\eta$ so that all endpoints avoid the at most countably many atoms of $\mu$. The masses of the finitely many grid arcs converge. Every arc can be enlarged to a grid arc (possibly the full circle) at length cost at most $2\eta$. Taking positive excesses bounds each discrepancy by the maximum grid excess plus $2\eta$, and the grid maximum is itself at most the discrepancy. Let $\eta\downarrow0$. Thus the scalar cluster set corresponding to $F$ is $D(F)$, a compact interval. This scalar fact does not assert uniform convergence of the masses of arcs whose endpoints move through an atom.

## Reproducing the finite checks

From the repository root, run the [Python certificate](../../scripts/phase18_programming.py).

~~~sh
python -B scripts/phase18_programming.py
~~~

It uses integer arithmetic and exact fractions. For a finite orbit represented by residues $r_0\le\cdots\le r_{N-1}$ modulo $d$, put $s_i=id-Nr_i$ with $0\le i<N$. The extreme discrepancy is $(\max s_i+d-\min s_i)/(Nd)$, the range between the largest post-jump and smallest pre-jump values of the empirical cumulative distribution minus length. This includes duplicate points by sorting with multiplicity. The script cross-checks the formula by direct enumeration of shortest enclosing arcs on small samples. For a truncation through insertion $J$ and $N\le n_J$, the omitted terms move each of the first $N$ orbit points by at most $B_0 b^{N-1-n_{J+1}}$. Arc enlargement bounds the absolute discrepancy error by twice this quantity. Consequently the checks against (1) apply to the infinite series. For the binary example with $p=3$ and $\delta=2/5$, at $N=400$ the certified interval is $[549027/10^6,549028/10^6]$.
