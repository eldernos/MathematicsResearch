# Distribution of rational quadratics on the parameter-two Stoneham axis

**Theorem.** Fix an odd radix *b* ≥ 3. Let *A*, *B*, *C*₀ be integers with *A* ≠ 0, and let *D* be a positive integer. These parameters allow every rational polynomial of degree two. Put

$$
\alpha=\sum_{j\ge1}\frac{1}{2^j b^{2^j}},\qquad
x=\frac{A\alpha^2+B\alpha+C_0}{D},\qquad u_n=\{b^n x\}.
$$

For each digit position *n*, form the shifted rational prefix of the **integer** polynomial by inserting precisely those terms whose radix exponents have been reached. The double sum counts ordered pairs of positive indices.

$$
P_n=A\sum_{2^i+2^j\le n}\frac{b^{n-2^i-2^j}}{2^{i+j}}
+B\sum_{2^j\le n}\frac{b^{n-2^j}}{2^j}+C_0 b^n .
$$

Let *q*ₖ be the positive reduced denominator of *P*ₙ at *n* = 3 · 2ᵏ⁻¹, for *k* ≥ 1. For an interval *I* = [*a*, *c*) in [0, 1], write |*I*| = *c* − *a*. Let *D*ₙ(*x*) denote the extreme interval discrepancy, the supremum over *I* of the absolute difference between its observed frequency among *u*₀, …, *u*ₙ₋₁ and |*I*|. Then

1. *x* is normal in base *b* if and only if *q*ₖ → ∞.
2. Every such *x* satisfies limsup *D*ₙ(*x*) ≤ 1/4 and liminf *D*ₙ(*x*) = 0.
3. Every interval has the correct logarithmically weighted frequency. With $H_N=\sum_{j=1}^N 1/j$,

   $$
   \lim_{N\to\infty}\frac{1}{H_N}
       \sum_{n=0}^{N-1}\frac{\mathbf 1_I(u_n)}{n+1}=|I|.
   $$
4. If the 2-adic number κ in the arithmetic formula below is algebraic over ℚ, then *x* is normal.

All four assertions are kernel-verified. The public declarations are `normal_iff_upper_denominator`, `quadratic_discrepancy_limits`, `quadratic_log_equidistribution` and `normal_of_algebraic_kappa`. Their index *j* labels the midpoint 3 · 2ʲ, so *k* = *j* + 1. Multiplying a choice of cleared coefficients and *D* by a common positive integer changes the reduced denominators by at most that fixed factor and gives the same growth criterion. [Lean statements and proofs](../../NormalityChecker/ParameterTwoQuadraticOrbits.lean)

## The two halves of a shell

Write $L=2^{k-1}$. Shell *k* is [2*L*, 4*L*). On [2*L*, 3*L*) the unscaled square prefix has denominator $2^{2k-2}$ for *k* ≥ 2. The linear prefix has denominator dividing $2^k$. For all sufficiently large *k*, the square term after multiplication by *A* has the strictly larger pole, so the integer polynomial has exact denominator $2^{2k-2-v_2(A)}$ throughout this half. On [3*L*, 4*L*) there are no further insertions. The prefix at 3*L* + *i* is $b^i P_{3L}$ and has the same dyadic denominator as $P_{3L}$ because *b* is odd. [Square profile](../phase13/parameter-two-square.md) · [Quadratic denominator proof](quadratic-denominators.md)

In the 2-adics put $\delta_j=(b^{-2^j}-1)/2^j$, $\lambda=\lim_j\delta_j$ and $C=\lambda+\sum_{j\ge1}(\delta_j-\lambda)$. The arithmetic calculation gives $\lambda\ne0$ and

$$
\kappa=-\frac{2A+B+2AC}{2A\lambda},\qquad
q_k=\max\{1,2^k|2A\lambda|_2\,|k-\kappa|_2\}.
$$

If $i<j$ and $q_i,q_j\le M$, the ultrametric inequality gives $|j-i|_2\le M/(2^i|2A\lambda|_2)$. A nonzero integer *m* has $|m|\ge1/|m|_2$. Consequently

$$
j-i\ \ge\ \frac{2^i |2A\lambda|_2}{M}.
$$

For each fixed denominator cutoff *M* and fixed window length *h*, every sufficiently late window of *h* shell indices thus has at most one exception. This includes an index that equals κ. When κ is algebraic, evaluating a nonzero integral polynomial annihilating κ at the integers gives $v_2(k-\kappa)=O(\log k)$ away from its finitely many integer roots. This proves the fourth assertion using the first. [Separation and polynomial evaluation proofs](../../NormalityChecker/ParameterTwoQuadraticHeight.lean)

## Uniform counts on complete and partial good halves

The true shifts satisfy $b^n D x-P_n\to0$. For the linear series and the ordered square, each omitted term in the shifted tail is bounded by its coefficient in absolute value. Each fixed term eventually enters the prefix, and these coefficient majorants are summable. Between insertions $P_{n+i}=b^i P_n$. [Actual-tail and propagation lemmas](../../NormalityChecker/QuadraticOrbitModel.lean)

For any ε > 0 there are *M* and a shell threshold such that the following estimate holds simultaneously for every interval *I* and every $0\le T\le L$. Take $s=2L$ on every lower half and $s=3L$ on an upper half satisfying $q_k\ge M$. Then

$$
\left|\sum_{i<T}\bigl(\mathbf 1_I(u_{s+i})-|I|\bigr)\right|\le\varepsilon L.
$$

Here the normalization by *L* includes short segments for which a relative error of order ε*T* would be unjustified. To prove the estimate first multiply the integer value by a fixed nonzero rational *z* whose denominator is coprime to *b*. Write *Y*ₙ = *zP*ₙ. Its denominator divides $\mathrm{den}(z)2^{2k}$, and the identity $P_n=z^{-1}Y_n$ gives $\mathrm{den}(P_n)\le\mathrm{den}(z^{-1})\mathrm{den}(Y_n)$. Cut the half into blocks of length $U=2^{\lfloor(k-1)/2\rfloor}$. There are $O(k^2)$ candidate insertions through the shell, so discarding blocks meeting an insertion and the final unfinished block costs $O((1+k^2)U)=o(L)$ starts. On each remaining block the model follows one rational radix orbit. Its starting denominator divides a power of the fixed integer $2\,\mathrm{den}(z)$, is at most $U^8$ eventually, and is uniformly large on the selected halves. The fixed-support short-orbit estimate and its interval-count corollary apply with one cutoff for all tested intervals. They include the error of the real shifted tail. [Fixed-support estimate](../../NormalityChecker/SmoothOrbit.lean) · [Interval transfer](../../NormalityChecker/SupportDiscrepancy.lean)

For the original coefficient denominator *D*, choose an integer *v* ≥ 0 such that $z=b^v/D$ in lowest terms has denominator coprime to *b*. This absorbs every prime power of *D* above primes dividing *b*. The preceding proof counts the actual shifts $u_{n+v}$. Replacing a window of *T* such shifts by the one starting *v* places earlier costs at most $2v$ in the centered count. Absorb this fixed endpoint error into ε*L*. This is a direct comparison of intervals in the orbit of *x* and gives the stated bound for arbitrary *D*. [Kernel proof for rational coefficients](../../NormalityChecker/QuadraticOrbitShells.lean)

## Normality and its obstruction

If $q_k\to\infty$, both halves satisfy the uniform estimate beyond a fixed shell. Summing the geometric progression of their lengths and including the last partial half gives a centered prefix count $O(\varepsilon N)+O_\varepsilon(1)$ for every interval. Let ε decrease to zero to obtain normality.

Conversely, suppose $q_k\le M$ infinitely often. The character of integer frequency $h=D\,M!$ has value one on every divided prefix $P_n/D$ of those upper halves. Since the shifted tail tends to zero, the corresponding true character has sum $L+o(L)$ over [3*L*, 4*L*). If *x* were normal, its full character sums through *N* would be $o(N)$ by Weyl's criterion. Subtraction at 4*L* and 3*L* would make this very block sum $o(L)$. Its length is a fixed proportion of both endpoints, so even arbitrarily far apart obstructions preclude full normality. The Lean proof uses the same factorial character after applying the proved integer-multiplication equivalence for normality. [Necessity](../../NormalityChecker/QuadraticOrbitModel.lean) · [Sufficiency](../../NormalityChecker/QuadraticOrbitTransfer.lean)

## Ordinary and logarithmic averaging

Fix ε and its associated cutoff *M*. Charge the upper halves with $q_k<M$ at one unit per observed position. Put the centered indicator equal to zero on those halves. Its remaining full and partial half sums have the uniform ε*L* bound. Summing the shells gives an error $O(\varepsilon N)+O_\varepsilon(1)$, uniformly over intervals. The entire cost of the marked positions is bounded by their number.

For each *h*, among the last *h* shells through a sufficiently late cutoff *N* there is at most one marked half. Earlier positions cost $O(2^{-h}N)$. Even if *N* ends inside the marked half [3*L*, 4*L*), its observed length is $\max(0,\min(N,4L)-3L)\le N/4$. The maximum fraction occurs at $N=4L$. Sending first *N*, then *h*, to infinity and then ε to zero gives the upper bound 1/4. For the lower limit, any sufficiently late run of $2h$ shells has at most one mark. One of its two runs of *h* shells is completely good. At that run's right endpoint, all earlier positions together cost at most $2^{-h}N$. These endpoints establish liminf zero. [Ordinary-prefix geometry](../../NormalityChecker/QuadraticOrbitTransfer.lean)

On a good half starting at *s*, partial summation with the decreasing weights $1/(s+i+1)$ bounds the weighted centered sum through any endpoint by $\varepsilon L/(s+1)\le\varepsilon$. A marked half costs at most one unit of harmonic mass. Among the first *K* shell indices there are $o(K)$ marks, by applying the window separation at arbitrary fixed *h*. There are two halves per shell and $H_N\ge\log(N+1)$, so division by $H_N$ gives a limiting error bounded by a constant times ε. The final unfinished shell has bounded harmonic mass. Letting ε decrease to zero proves logarithmically weighted equidistribution, including all radix-word cylinders. [Harmonic normalization and partial summation](../../NormalityChecker/QuadraticOrbitLog.lean)

For example, take $b=3$ and $x=(\alpha^2-2\alpha)/6$. At $k=3$, $P_{12}=7315/4-2(249399/8)=-60521$, hence $q_3=1$. The fractional parts of $P_n/6$ for $12\le n<16$ are $1/6,1/2,1/2,1/2$. A single radix shift changes the scaling factor from $1/6$ to $1/2$, as in the rational-coefficient proof. This finite integer prefix illustrates the obstruction that would have to recur with bounded denominator to disprove normality. The growth of $q_k$ for $X^2-2X$ remains open. [Worked square prefixes](../phase13/parameter-two-square.md) · [Arithmetic obstruction and logarithm estimates](quadratic-denominators.md)

Wall's theorem supplies qualitative normality under rational affine changes. The partial-shell count above is what transfers the numerical discrepancy bound and the logarithmic assertion. Vandehey's short exponential-sum estimates give a quantitative antecedent for the fixed-support input. The kernel proof here uses the repository's qualitative differencing proof. [Wall and Vandehey bibliography](../../papers/01-stoneham-polynomials/references.bib) · [Vandehey, *Differencing methods for Korobov-type exponential sums*](https://doi.org/10.1007/s11854-019-0038-2)
