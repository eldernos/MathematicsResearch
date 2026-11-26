# The Fredholm series and the endpoint of the binary product

Let $e(t)=\exp(2\pi i t)$, $z=e(x)$, $t_n=\{2^nx\}$, and $E(t)=1-\cos(2\pi t)$. Write $D_N(x)$ for the extreme discrepancy of the first $N$ binary shifts, and $D_\infty=\limsup_N D_N$. Positive lower mean of $E(t_n)$ is equivalent to $D_\infty<1$. In fact the lower transition density is between one quarter of this lower mean and the lower mean itself. [First-frequency theorem](../../NormalityChecker/FirstFrequency.lean) · [Discrepancy criterion](../transition-discrepancy.md#first-frequency-escape)

## A uniform radial comparison

Set $L(w)=\sum_{n\ge0}w^{2^n}$ for $|w|<1$. Absolute convergence follows by comparison with the full geometric series. Removing the first term gives $L(w)=w+L(w^2)$. At $r_N=\exp(-2^{-N})$ put $H_N(x)=L(r_N)-\Re L(r_N z)$. The series at $r_N$ is real. For every real $x$ and integer $N\ge0$,
$$
\left|H_N(x)-\sum_{0\le n<N}E(t_n)\right|\le 2 .
$$
Indeed the smoothed sum has nonnegative weights $\exp(-2^{n-N})$. The loss below the cutoff is at most $2\sum_{n<N}2^{n-N}<2$, by $1-e^{-s}\le s$. The added tail is at most $2\sum_{j\ge0}e^{-2^j}\le 2\sum_{j\ge0}2^{-j-1}=2$, since $2^j\ge j+1$ and $e\ge2$. Their difference gives the asserted two-sided bound. Taking lower limits gives
$$
D_\infty(x)<1\quad\Longleftrightarrow\quad \liminf_{N\to\infty}H_N(x)/N>0.
$$
Both the uniform inequality and the equivalence are kernel-verified. For ln 2 the angle is $e(\ln2)$ throughout. The same cutoff comparison for the constant observable one gives $L(r_N)=N+O(1)$. The first-frequency theorem implies that a lower radial mean of at least $0.0004$ would suffice for $D_\infty\le0.9999$. [Lean statements](../../NormalityChecker/FredholmOrbit.lean) · [Transition bound on discrepancy](../phase14/transition-windows.md)

The following paper deduction interpolates between dyadic radii. For $r=e^{-s}$ choose $N=\lfloor\log_2(1/s)\rfloor$ for $0<s<1$. Nonnegativity sandwiches $L(r)-\Re L(rz)$ between $H_N$ and $H_{N+1}$. The two sharp sums differ by at most two. This proves the corresponding lower-limit criterion with denominator $\log_2(1/s)$ for unrestricted $s\downarrow0$. There is no passage from a single favorable subsequence to a lower limit here.

The classical positive-axis divergence at 1 also follows directly from the positive series. Repeated use of the functional equation shows radial divergence of its real part at every root of unity of order a power of two, since only finitely many initial terms can have other phases. These points are dense, so the disk admits no holomorphic continuation through a boundary arc. This gives an elementary proof of the natural boundary that also follows from Hadamard’s gap theorem. At a rational angle of odd denominator the phases are periodic, and the radial mean of the deficit equals the cycle mean. Brent, Coons and Zudilin exploit root-of-unity radial behavior for algebraic independence of *interior* Mahler values. Poulet and Rivoal analyze radial expansions at the positive axis under specified Mahler hypotheses. Neither result estimates the lower mean at the angle of ln 2. The logarithm gives exact rational-prefix recurrences and is irrational, which rules out periodicity of its angle. Evaluating the analytic estimates at that point still requires an orbit estimate. [Brent–Coons–Zudilin](https://arxiv.org/abs/1412.7906) · [Poulet–Rivoal](https://rivoal.perso.math.cnrs.fr/articles/asympmahler.pdf) · [Logarithm recurrence](../classical-discrepancy.md)

## The fixed interior parameter

Write $P_N(a,z)=\prod_{n<N}(1+az^{2^n})$. Difference of squares gives $(1-z)P_N(1,z)=1-z^{2^N}$ for every $z$, including $z=1$ in this undivided form. Lean verifies this polynomial identity. [Kernel product identity](../../NormalityChecker/FredholmOrbit.lean)

The interior estimates and zero-distribution criterion below have paper proofs. At $z=1$, $P_N(1,1)=2^N$. For $0<a<1$ set $q=2a/(1+a)^2$ and let $U_N=N\log(1+a)-\log|P_N(a,z)|$. Factoring each squared modulus gives
$$
U_N=-\tfrac12\sum_{n<N}\log(1-qE(t_n)),\qquad
\frac q2\sum_{n<N} E(t_n)\ \le U_N\le\
\frac{q}{2(1-2q)}\sum_{n<N} E(t_n).
$$
Use $y\le-\log(1-y)\le y/(1-2q)$ for $0\le y\le2q<1$. Thus $\limsup_N |P_N(a,z)|^{1/N}<1+a$ for one (equivalently every) fixed interior $a$ exactly when $D_\infty(x)<1$. All zeros in $a$ are $-e(-2^nx)$. The fraction outside any fixed neighborhood of $-1$ goes to zero along a subsequence exactly in the weak-concentration sense: the empirical zero measures tend to $\delta_{-1}$ along that subsequence iff the mean of $E$ tends to zero there. Indeed the squared distance of each zero from $-1$ is $2E(t_n)$. This identifies the arithmetic zero-distribution estimate the fixed parameter needs. Harmonicity of $\log|P_N|$ in the open parameter disk gives no such estimate from its value at one boundary point.

## A moving parameter still cannot recover a fixed interior deficit

**Theorem (paper proof).** Given *any* deterministic sequence $0<a_N<1$ with $a_N\to1$, there is an irrational $x$ such that $D_N(x)\to1$ while
$$
\frac1N\log|P_N(a_N,e(x))|\longrightarrow0,\qquad
\frac1N\log|P_N(1,e(x))|\longrightarrow0 .
$$
At every fixed $0<a<1$ the same $x$ has $N^{-1}\log|P_N(a,e(x))|\to\log(1+a)$. In particular even a deficit tending to the full $\log 2$ on a prescribed approach to the boundary can coexist with zero deficit at *all* fixed positive interior parameters.

**Construction.** Write $d_N=1-a_N$ and $h(k)=\max(2^{-\sqrt{k}},\sqrt{\sup_{m\ge k}d_m})$ for $k\ge1$. This decreases to zero. Start with $p_1$ so large that $h(p_1)\le1/4$, put $p_{j+1}=p_j+\lfloor\log_2(1/h(p_j))\rfloor$, and take ones at precisely the fractional digit positions $p_j$. The gaps tend to infinity, so their number through $N$ is $o(N)$ and the binary expansion is aperiodic. For $p_j\le k<p_{j+1}$ the fractional part of $2^kx$ is at least $2^{-(p_{j+1}-p_j)}\ge h(k)$ and at most $(1/2)/(1-1/4)=2/3$. Hence $\|2^k x\|_{\mathbb R/\mathbb Z}\ge h(k)$ there. For each fixed $b$ the proportion of shifts whose next $b$ digits contain a one tends to zero. Testing $[0,2^{-b})$ and then letting $b\to\infty$ proves $D_N(x)\to1$. The same observation shows that the mean of $E$ tends to zero. This separation construction comes from Phase 13. [Antecedent and proof](../phase13/logarithm-transitions.md#a-sharp-sparse-example)

**Comparison of the products.** Use $|1-e(t)|\ge4\|t\|_{\mathbb R/\mathbb Z}$. For $p_1\le n+1\le N$, the identity $1-e(2t)=(1-e(t))(1+e(t))$ gives $|1+e(t_n)|\ge2h(n+1)\ge2\sqrt{d_N}$. The finitely many earlier factors are nonzero, so this last lower bound holds for them too once $N$ is large. For each unit $u=e(t_n)$,
$$
\frac{|1+a_Nu|^2}{|1+u|^2}=a_N+\frac{d_N^2}{|1+u|^2}.
$$
The ratio lies between $a_N$ and $a_N+d_N/4$, uniformly for $0\le n<N$. Its half-log therefore tends uniformly to zero. At the endpoint, the numerator $|1-e(2^Nx)|$ lies between $4\,2^{-\sqrt N}$ and two. The product identity proves the endpoint limit, and the uniform comparison proves the moving limit. The comparison for fixed $a$ gives the final assertion.

For fixed $N$, the endpoint logarithm weighs zeros close to $+1$ especially heavily. With $v_n=-\log|\cos(\pi t_n)|$ and irrational $x$, telescoping gives $\sum_{n<N}v_n=N\log2+O_x(1)-\log|\sin(\pi t_N)|$. A sufficient arithmetic estimate is $\limsup_N N^{-1}\sum_{n<N}(v_n-K)_+<\log2$ for some finite $K>0$. This leaves positive lower mass in $\min(v_n,K)$. The quotient $\min(v(t),K)/E(t)$ extends boundedly to the circle, with limit $1/4$ at zero, so this estimate proves strict discrepancy. The construction above shows why a scale moving toward the singularity can miss the issue. The 2026 preprint of Gohlke, Lamprinakis and Schmeling treats the related family of logarithmic potentials under doubling and distinguishes the cosine singularity at shift one half. Proposition 2.9 and its proof record the exceptional measure concentrated at zero. Their thermodynamic statements and the earlier finite cosine identity establish context for this obstruction. The diagonal construction here extends the repository's separation counterexample. No historical priority is claimed. [Singular potentials, Proposition 2.9 and proof](https://arxiv.org/html/2603.19001v1) · [Phase 13 spike estimates](../phase13/logarithm-transitions.md#aggregate-age-and-the-cosine-spikes)

## Finite controls

The accompanying program constructs certified binary cylinders for ln 2, the base-two Stoneham number with parameter three, and the signed series of Theorem III with phase coefficients alternating 1, 0. The latter has upper discrepancy 3/4. Bailey and Crandall give the normal Stoneham control. [Signed-shell theorem](../../docs/survey.md#iii-exact-discrepancy-and-resonance) · [Bailey–Crandall](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf)

For the moving-parameter construction with $a_N=1-1/N$, the normalized moving and endpoint log growths at $N=4096$ are about 0.0020054 and 0.0021270. The program also evaluates the sharp and radial means on each cylinder and on rational and sparse inputs. The printed transcendental evaluations are floating-point diagnostics. The proof above establishes the uniform error and the limiting counterexample independently of floating-point arithmetic. [Reproduction](../../scripts/phase15_fredholm.py)
