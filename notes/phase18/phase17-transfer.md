# Consequences of the completed Phase 17 checkpoint

Phase 17 provides two distinct inputs to synthesis. Its multiplicative Lambert theorem gives explicit discrepancy deficits, and its Legendre–Bezout construction shows how to round a whole integral using one rational grid. The first yields exact orders for translations. The second gives all-shift rational approximants to π with **linear shadowing windows**. The comparison below uses Phase 17 at commit `17e57702e4cbd6b66a9157636b30ab3802116a4b`. [Phase 17 checkpoint](../phase17/README.md)

## Linear windows for pi

Fix a finite identity $\pi=\sum_i c_i\arctan(1/a_i)$ with integer coefficients, positive integer poles and $a_*=\min_i a_i\ge2$. Discard zero coefficients. Put $\rho_a=a+\sqrt{a^2+1}$ and $\rho=\rho_{a_*}$. For **each** sufficiently large integer binary shift $n$, the following rational algorithm, using only $n,c_i,a_i$, produces a rational $Y_n$ of odd reduced denominator $q_n$. It satisfies
$$
 \limsup_{n\to\infty}\frac{\log q_n}{n}\le\frac{\log 2}{\log\rho},
 \qquad
 \liminf_{n\to\infty}\frac{-\log_2|2^n\pi-Y_n|}{n}\ge\frac1{\log\rho}.
$$
Here a lower bound of $\tau n+o(n)$ bits gives $o(1)$ circle error uniformly through the first $\lfloor(\tau-\epsilon)n\rfloor$ successive doublings for each $0<\epsilon<\tau$. The same $Y_n$ models that entire window. The separately computed $Y_{n+1}$ may change. For Machin choose $a_*=5$, and for Størmer choose $a_*=8$. The small-rate assertion is across fixed identities; the constants and window slopes depend on the chosen poles. [Arctangent identities and the Chebyshev construction](classical.md) · [Preceding Legendre–Bezout theorem for ln 2](../phase17/classical-approximants.md#4-linear-windows-from-the-legendre-kernel-and-what-they-are)

**Algorithm.** Let $P_j$ be the Legendre polynomial with $P_j(1)=1$. For $D\ge1$ set $H_D(y)=P_{2D}(\sqrt y)$, a rational polynomial of degree $D$, and put $h_{i,D}=H_D(-a_i^2)$. Use the first $D$ such that $\min_i|h_{i,D}|\ge 2^n$. Compute
$$
 R_D(y)=\sum_i \frac{c_i a_i}{h_{i,D}}\,
               \frac{H_D(y)-h_{i,D}}{y+a_i^2},\qquad
 L_D=\mathrm{lcm}(1,3,\ldots,2D-1).
$$
The quotients are polynomials of degree at most $D-1$. Set $Y_n=-\mathrm{round}(L_D 2^n\int_0^1R_D(x^2)\,dx)/L_D$, using either fixed tie convention. The scalar integral is rational by the moments $1/(2j+1)$. All comparisons determining $D$, the integrals, and the rounding use rational arithmetic. Every point of this grid is a moment of an integer polynomial in $x^2$ of degree at most $D-1$ in $x^2$: the integers $L_D/(2j+1)$ have gcd one. This is the odd-denominator form of the correlated rounding in Phase 17.

**Size of the degree.** Laplace's integral representation gives
$$
 |P_{2D}(ia)|=\pi^{-1}\int_0^\pi
        (a+\sqrt{a^2+1}\cos\theta)^{2D}\,d\theta .
$$
To continue the real-argument integral to $ia$, expand the integrand: odd cosine moments vanish and the remaining expression is polynomial in its argument. The maximum absolute value inside the power is $\rho_a$, attained at zero. An interval of positive length has absolute value at least $\rho_a-\epsilon$ for every sufficiently small fixed $\epsilon>0$. Taking $2D$-th roots proves convergence to $\rho_a$; the upper bound is $\rho_a^{2D}$. These facts hold simultaneously for the finitely many poles. Thus $\log_2\min_i|h_{i,D}|=2D\log_2\rho+o(D)$. The first crossing of $2^n$ exists and obeys $D/n\to1/(2\log_2\rho)$: apply the upper and lower asymptotic bounds at $D$ and $D-1$. This avoids any assumption about the monotonicity of a rounding operation. [Laplace formula, DLMF 18.10.5](https://dlmf.nist.gov/18.10.E5)

**Analytic remainder.** For $r=\rho_a^{-2}$ and $x=\cos\theta$, the geometric series for the Poisson kernel gives the uniformly convergent expansion
$$
 \frac1{x^2+a^2}=\frac{4r}{1-r^2}
          \left(1+2\sum_{j\ge1}(-r)^j T_{2j}(x)\right).
$$
Indeed $r+r^{-1}=2(2a^2+1)$. Truncation at $j=D-1$ gives an even polynomial of degree below $2D$ with uniform error at most $C_a r^D$. Orthogonality on $[-1,1]$ and evenness annihilate its integral against $P_{2D}$ on $[0,1]$. On this interval $|P_{2D}|\le1$, also from Laplace's formula. Thus the remaining integral against $(x^2+a^2)^{-1}$ is $O_a(\rho_a^{-2D})$. [Legendre orthogonality, DLMF Table 18.3.1](https://dlmf.nist.gov/18.3)

By polynomial division and $\int_0^1 a/(x^2+a^2)\,dx=\arctan(1/a)$,
$$
 \pi+\int_0^1 R_D(x^2)\,dx
 =\sum_i\frac{c_i a_i}{h_{i,D}}\int_0^1\frac{P_{2D}(x)}{x^2+a_i^2}\,dx .
$$
Since $2^n/|h_{i,D}|\le1$, rounding the rational integral gives the finite bound
$$
 |2^n\pi-Y_n|\le\frac1{2L_D}+C\rho^{-2D},\qquad q_n\mid L_D.
$$
The prime number theorem gives $\log L_D=2D+o(D)$ by removing only the powers of 2 from $\mathrm{lcm}(1,\ldots,2D-1)$. Since $\log\rho>1$ for $a_*\ge2$, $L_D\rho^{-2D}\to0$. The degree estimate now proves both claimed limits.

**Exact finite control.** At $n=600$, Machin's poles give $D=91$, a reduced denominator of bit length 257 and absolute shifted error at most $2^{-261}$. Størmer's poles give $D=76$, a 212-bit denominator and error at most $2^{-213}$. The [reproduction script](../../scripts/phase18_classical.py) verifies both families at every $n=1,\ldots,256$ and at $512,600,800$. It computes the kernel and rounded model using exact rationals, then bounds the reference value by successive rational partial sums of Machin's alternating arctangent series. The reference value plays no role in choosing $D$ or $Y_n$.

**Where distribution enters.** Whenever $L_D2^n\pi$ is farther than $C L_D\rho^{-2D}$ from a rounding tie, $L_DY_n$ is exactly its nearest integer. Thus an arithmetically computable linear window can coincide with the nearest-grid model. No distribution of these grid numerators has been assumed. For an irrational $x$ of finite irrationality exponent and any $\mu>\mu(x)$, a rational $A/q$ approximating $2^n x$ to $T$ bits satisfies $T\le(\mu-1)n+\mu\log_2q+O(1)$, by rational separation at denominator at most $2^nq$. Along a subsequence with $\log q\gg n$, such a window cannot reach $q^\eta$ for fixed $\eta>0$. The upper rate in this construction does not establish a positive lower rate for its reduced $q_n$. Additional denominator and numerator control would be needed to use either a fixed-support short-orbit estimate or the growing-grid theorem. [Phase 17 window–denominator barrier](../phase17/classical-approximants.md#6-the-windowdenominator-barrier) · [Phase 18 summation criteria](summation.md)

## An exact translation rate for every Lambert support density

Under the full hypotheses in Phase 17 Track B, let $\delta\in(0,1)$ be its **prime-support parameter** and $L_f$ the associated binary Lambert number. Write $D_N$ for binary extreme discrepancy. For all sufficiently large $N$,
$$
 \max_x |D_N(x+L_f)-D_N(x)|
 =1-D_N(L_f)\asymp_{f,S,q_0,\delta}
       \frac{\log\log N}{(\log N)^{1-\delta}} .
$$
The equality is the sharp finite translation theorem, attained at $x=0$. The order is precisely the Phase 17 two-sided bound; its constants depend on the fixed arithmetic data. Thus each eligible $L_f$ preserves **both** limiting discrepancies for every input, including the classical targets. Adding it to the programmed cubic example of discrepancy limit $\theta$ preserves $\theta$, with error bounded by the sum of the cubic rate and the displayed Lambert rate. Here $\delta$ and $\theta$ can be chosen independently. Sparse word occurrences, even disjunctivity by itself, would give no such rate. [Lambert hypotheses and proof](../phase17/multiplicative-lambert.md) · [Kernel-checked finite identity](../../NormalityChecker/SharpTranslation.lean)

For example, take the Erdős–Borwein constant $E$. In fact $E$ and $E+L_f$ have the same complete set of empirical **circle-measure** limits. In binary, discrepancy tending to one for $L_f$ forces its mean circle displacement to zero by the [fixed-point classification](translations.md#the-exact-worst-case-change). For every Lipschitz function $g$ the difference of the two empirical averages is at most its Lipschitz constant times that mean. Compactness and approximation of continuous tests give the assertion. This transfers the strict upper discrepancy conclusion for $E$ to the translate. Correct limiting frequencies for individual digit intervals still need attention to endpoint atoms. The Phase 17 finite-column and moment obstructions concern the arithmetic statistics used to certify a digit bias; weak convergence does not supply missing divisor correlations. [Phase 17 Erdős–Borwein tests](../phase17/erdos-borwein-bias.md)

## The mixed product and the scope of synthesis

For $Z=\alpha(2,3)\alpha(2,5)$ the Phase 17 empirical-mixture law retains the actual cycle weights, which can change discrepancy when combined. If $C_0$ denotes the **upper density of integer shifted prefixes** defined there, its theorem gives $D^+(Z)\le4/11$ exactly when $C_0\le4/11$. Therefore the lower limit of the worst translation change for $Z$ is at least $7/11$ exactly when $C_0\le4/11$. Its proven $\liminf D_N(Z)=0$ also gives upper limit one for the worst translation change. These conclusions are equivalences or subsequential conclusions for the unmodified product. For the synthetic product $XY'$ the Phase 18 correction makes each opposite-axis prefix a unit, so every late convolution cutoff retains a pole. Removing the correction introduces a rational multiple of the normal first factor. It cannot be removed using a universal normality-preserving translation. [Phase 17 exceptional cycles](../phase17/mixed-product-orbits.md) · [Synthetic product construction](algebra.md#e3-a-product-whose-opposite-axis-prefix-stays-a-unit)

Phase 17's undecidability theorem provides a further boundary. Even under its transcendental endpoint promise there is no algorithm deciding normality from arbitrary computable digit names. The positive rational-state recurrence synthesizes examples *from prescribed states*. Its computable forward construction does not invert arbitrary names or recognize all eligible remainders. Conversely Phase 17's echelon-degree Weyl lemma transfers normality of the needed polynomial degrees to joint uniformity; the missing arithmetic input for a new family is a proof of those degrees. Phase 18 supplies that input for factorial schedules and the specified degree range on power schedules. [Formal degree criterion](../../NormalityChecker/Phase17DiscrepancyBounds.lean) · [Digit-name theorem](../../NormalityChecker/ComputableNormalityUndecidability.lean)

There is also a direct recognition obstruction for the synthetic theory. Under the Phase 17 promise that the input is a computable name for a transcendental binary real whose discrepancy tends to either zero or one, it is undecidable whether translation by the input preserves the numerical discrepancy of every real up to $o(1)$. Neither answer is semidecidable under this promise. Indeed the sharp maximum and attainment at zero identify this translation property exactly with the branch $D_N\to1$, the complement of normality on the promise. A recognizer or corecognizer would therefore contradict the corresponding, already kernel-verified, digit-name theorem. This conclusion concerns recognition from the promised names. An explicit arithmetic expression can carry additional information, as the Lambert and positive-programming examples do.
