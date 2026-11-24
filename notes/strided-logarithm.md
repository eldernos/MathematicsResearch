# Half-length denominators for binary shifts of ln 2

Let $w(j)$ repeat the six values $0,4,3,4,0,1$, starting at $j=1$. For $N\ge0$ form the rational number

$$
Y_N=\sum_{j=1}^N\frac{w(j)2^{N-j}}j.
$$

**Theorem.** Its reduced denominator $q_N$ divides $\mathrm{lcm}(1,\ldots,\lfloor N/2\rfloor)$, and $\log q_N=N/2+o(N)$. At every position,
$0\le 2^N\ln 2-Y_N\le4/(N+1)$. Among binary-exponent truncations of finite integer combinations of $\log(1\pm2^{-k})$ equal to a fixed nonzero integer multiple of $\ln 2$, the smallest possible limiting exponential rate of the shifted denominator is $1/2$. The standard series has rate 1. The comparison concerns this prescribed truncation rule. The actual half-length exponent and general prime-band limit now have Lean proofs. The code also verifies the optimality reduction with the finite primitive-divisor input supplied by Bang’s classical theorem. [Phase 11 formalization](corrected-strides.md#actual-rates-for-the-uncorrected-logarithms) Lean verifies the series identity, the pointwise error, the common-denominator bound, and survival of every prime greater than 2 in the band $N/3<p\le N/2$. [Lean statements](../NormalityChecker/StridedLogarithm.lean) · [Exact reproduction](../scripts/strided_logarithm.py) · [Standard denominator theorem](../NormalityChecker/DenominatorGrowth.lean)

## The representation

The identity $(1+2^{-3})/(1-2^{-2})^2=2$ gives

$$
\ln 2=2\sum_{j\ge1}\frac{4^{-j}}j+
              \sum_{j\ge1}\frac{(-1)^{j+1}8^{-j}}j .
$$

Grouping by the binary exponent $m$ gives weight 4 when $2\mid m$, plus $3(-1)^{m/3+1}$ when $3\mid m$. This gives the six nonnegative weights above. Absolute convergence justifies regrouping. Multiplication by $2^N$ leaves an integer power of two in every retained term of the two series. Their remaining denominators are indices $j\le N/2$ and $j\le N/3$. The tail in the grouped series is bounded by $4\sum_{i\ge1}2^{-i}/(N+1)$. All statements apply at odd $N$ and at partial periods of the coefficient pattern.

## The residue of the actual numerator

More generally, consider any fixed finite integer combination of these dyadic logarithms. Expand and group by binary exponent to obtain coefficients $W(j)$ in $\sum W(j)/(j2^j)$. Each contribution has the form of a fixed integer times $\mathbf1_{k\mid j}$, possibly times $(-1)^{j/k}$. Set $P_v=\sum_{j\le v}W(j)/(j2^j)$ and $Y_N=2^NP_N$. For every odd prime $p$ coprime to all strides and satisfying $p^2>N$, the rational $pY_N$ has a well-defined residue modulo $p$ and

$$
pY_N\equiv 2^N P_{\lfloor N/p\rfloor}\pmod p.
$$

Indeed only the terms at $j=p\ell$ survive multiplication by $p$ and reduction. Here $W(p\ell)=W(\ell)$, $\ell<p$, and $2^{p\ell}\equiv2^\ell\bmod p$. If $Y_N=A_N/q_N$ in lowest terms and the displayed residue is a unit, $p$ divides $q_N$ exactly once and $A_N\bmod p$ is this residue times $q_N/p$. A zero residue means $p$ is absent. In particular, on $N/3<p\le N/2$ the two-stride model has residue $2^{N-1}\bmod p$ for $p>3$. These are congruences for the specified numerators.

There is an exact denominator-rate formula for every such finite representation:

$$
\lim_{N\to\infty}\frac{\log q_N}{N}
 =\sum_{\substack{v\ge1\\P_v\ne0}}\left(\frac1v-\frac1{v+1}\right).
$$

Fix an integer $V$. In each of the first $V$ intervals $N/(v+1)<p\le N/v$, the test uses one fixed rational $P_v$. For large $N$ these primes exceed $\sqrt N$, avoid the strides, and exceed every prime factor of the nonzero numerators and denominators on the finite list. Thus each interval either survives in full or contributes zero. The prime number theorem gives the displayed weights. All denominator powers have exponents at most those of $\mathrm{lcm}(1,\ldots,N)$. The first powers below $N/(V+1)$ cost at most $\vartheta(N/(V+1))$, and **all** powers beyond the first cost at most $\sqrt N\log N$ by charging $\log N$ to each prime up to $\sqrt N$. Divide by $N$, then let $V$ tend to infinity. In the two-stride model $P_1=0$ and every $P_v$ for $v\ge2$ is positive. The sum telescopes to $1/2$.

## Why half is optimal in this class

Rewrite $\log(1+x)=\log(1-x^2)-\log(1-x)$ at each stride. This preserves the formal coefficient of every binary exponent, hence also every truncation. Write the result as $\sum_k b_k\log(1-2^{-k})=m\ln 2$. For a largest remaining $k>6$, Bang's primitive-divisor theorem gives an odd prime dividing $2^k-1$ which divides none of $2^i-1$ for $1\le i<k$. Taking its valuation in the product identity forces $b_k=0$. Descending leaves indices at most six. The primes 31 and 5 force $b_5=b_4=0$. At 7 and 3 the two equations are $b_3=-b_6$ and $b_2=-2b_6$, since $63=3^2\cdot7$. The power of two gives $m=b_6-b_1$. This also classifies the identities independently of the finite search. [Primitive divisors, historical theorem and references](https://doi.org/10.1017/S1446788715000269)

If $b_1=0$, the coefficient sequence is $m w(j)$ and the rate is $1/2$. Otherwise $P_1\ne0$, so $v=1$ alone contributes $1/2$. Since $P_v\to m\ln 2\ne0$, sufficiently large $v$ also contribute, proving strict inequality. The optimal series is unique coefficient by coefficient after normalization to $m=1$. This conclusion allows arbitrary finite stride cutoffs and arbitrary fixed integer coefficient bounds.

## Other exact series and controlled kernels

Write $A(q)=\sum_{j\ge0}q^{-(2j+1)}/(2j+1)=\mathrm{atanh}(1/q)$. The quotient $(q+1)/(q-1)$ gives $2A(5)+2A(7)=\ln(3/2)+\ln(4/3)=\ln 2$ and $2A(3)=\ln2$. Truncating $A(q)$ after $J$ terms leaves a positive error at most $q^{-(2J+1)}/((2J+1)(1-q^{-2}))$. These odd-denominator series introduce powers of 3 or of 5 and 7 in their rational truncations. They lie outside the optimality theorem.

For the dyadic identities, put $L_k^+=\sum_{j\ge1}(-1)^{j+1}2^{-kj}/j$ and $L_k^-=-\sum_{j\ge1}2^{-kj}/j$. Then $2L_1^+-L_3^+$, $L_1^+-L_2^-$ and $L_3^+-2L_2^-$ all equal $\ln2$. The first has periodic grouped coefficients $(2,-2,-1,-2,2,1)$, the second recovers the constant coefficient 1, and the third gives the optimal six-term pattern. An exhaustive rational product search over $1\le k\le6$, omitting $1-2^{-1}$ and imposing total absolute coefficient at most four, gives seven identities for $\ln2$ and one for $2\ln2$. One further product is $(1+2^{-1})(1+2^{-2})/(1-2^{-4})=2$. The length-four identity for $2\ln2$ doubles $L_1^+-L_2^-$. Every candidate is checked by exact exponentiation of rationals. For a fixed multiple $m\ge2$, both $mY_N$ and $Y_N+(m-1)R_N$ model $2^N m\ln2$, where $R_N$ is the original prefix. The second series has weights $w(j)+m-1>0$ and denominator rate 1 by the same prime-sum theorem, while the first has rate $1/2$. The program cross-checks both rational enclosures against an independently certified binary cylinder for each of the four multiples in the block experiment. [Search and tests](../scripts/strided_logarithm.py)

For the existing moment models in radix $B=2$ or 16, choose exactly one polynomial in each degree $d$,
$F_d(t)=T_d(2t-1)/T_d(2B-1)$, where $T_d(\cos\theta)=\cos(d\theta)$. The sharp uniform norm on [0,1] is $1/T_d(2B-1)$. For $d>0$, a smaller norm for a degree-at-most-$d$ polynomial normalized at $B$ would give $d$ roots of the difference by alternating signs at the $d+1$ extrema, and an additional root at $B$. For $d=0$ the normalization fixes the constant. All roots of the numerator lie in (0,1), so its coefficients alternate and their absolute sum is $T_d(3)$. Thus the normalized coefficient sum in absolute value is at most one. The recurrence $T_{d+1}(z)=2zT_d(z)-T_{d-1}(z)$ computes the rational coefficients exactly. In the logarithmic model the error is at most $1/((N+1)T_d(3))$. At degree four the normalization is 577, compared with 289 for the square of the degree-two kernel. [Lean norm and logarithmic error](../NormalityChecker/ChebyshevModels.lean) · [Polynomial moment identity](../NormalityChecker/LogPolynomialKernel.lean) · [Classical Chebyshev formulas](https://dlmf.nist.gov/18.5)

The beta-integral kernel $(1-t)^r$ has a different dependence on position, with error at most $N!r!/(N+r+1)!$. At large $N$ this can be much smaller than a fixed-degree uniform envelope. Padé methods exploit common divisors of the denominators of the approximant and of its target. For example Rivoal's Theorem 4(ii), remark 2, gives $|\ln2-u/(d_m2^m)|\ge(d_m2^m)^{-1.948967}$ for every integer $u$ and all sufficiently large $m$, with $d_m=\mathrm{lcm}(1,\ldots,m)$. This is an exclusion near a specific grid. It supplies neither equidistribution on that grid nor an estimate on the fraction of long binary runs. [Rivoal](https://doi.org/10.4171/RMI/519) · [Beta-integral estimates](log-shadow-primes.md)

## Repetitions of a prescribed diagonal numerator residue

Let $y_n$ be the earlier diagonal beta model, $\delta_n=y_{n+1}-2y_n$ and $U_n=3y_n/\delta_n$. The diagonal step gives
$\delta_n=3(-1)^n/[2(2n+1)\binom{2n}{n}]$. Consequently $U_0=0$ and

$$
(n+1)U_{n+1}=-2(2n+3)(2U_n+3).
$$

In particular $n!U_n$ is an explicit integer. For a prime $p>3$ and $0\le n<p$, reduce $U_n$ modulo $p$. On $n<p\le2n$, the step has valuation $-1$, so this residue is $p y_n$ multiplied by the explicit unit $3/(p\delta_n)$. It distinguishes residues even when the prime survives in both models.

**Theorem (Lean).** For any $c$ in the field of $p$ elements and any $0<h<p/2$, at most $h$ integers $0\le n<n+h<p$ satisfy $U_n=U_{n+h}=c\bmod p$. The same estimate holds on the whole initial field range, including before the diagonal step has a pole. [Actual numerator, modular recurrence and root bound](../NormalityChecker/DiagonalNumerator.lean)

To see why, start the recurrence at the symbolic index $X$ with value $c$ and iterate $h$ times. Before cancellation the result is $A_h/B_h$ with $B_h=\prod_{i=1}^h(X+i)$ and both degrees at most $h$. Every repetition is a root of $A_h-cB_h$. For $c\ne0$, the last numerator factor vanishes at $X=-h-1/2$, while the denominator is a product of nonzero half-integers because $2h<p$. For $c=0$, evaluate at $X=-1$. The first numerator is nonzero there, every subsequent denominator vanishes there, and the subsequent numerator factors contain only powers of 2 and the nonzero odd factors $2j+1$ for $j<h$, in addition to the initial factor 3. The polynomial is nonzero in both cases.

In any interval of $T$ consecutive indices within $[0,p)$, a fixed residue occurs at most $\lceil T/(H+1)\rceil+H(H+1)/2$ times for $1\le H<p/2$. Split into bins of $H+1$ consecutive indices. After the first occurrence in each bin, charge the next occurrence to a returning pair at gap at most $H$. Sum the theorem over these gaps. In particular each prescribed residue occurs $O(p^{2/3})$ times in the full range, uniformly in $c$. These are restrictions on the actual numerator across adjacent and separated models. Binary low-transition cylinders are **real intervals** at each starting index, and the change from the modular unit normalization to those real intervals depends on the index and the whole denominator. A positive-density estimate for those cylinders remains open.

The exact program checks the diagonal recurrence against independently reduced beta models and the two-stride residue against independently summed prefixes. At $N=128,256,512,1024$ the two-stride denominators have respectively 89, 183, 359 and 742 binary digits. All four are finite measurements. [Run the reproduction](../scripts/strided_logarithm.py)

## An arithmetic sieve for low-transition binary words

The diagonal model follows enough shifts to test an entire word of length $n$ at starting position $n$. The following construction uses its residues at large primes **without choosing a lift to the full denominator**. Put $M=2n$, $L=\mathrm{lcm}(1,\ldots,M)$, and let $P$ be the product of primes $\sqrt M<p\le M$. Define $H=L/P$. The data below determine the fractional part of the actual diagonal rational $y_n$ up to a translate of the equally spaced grid of $H$ points.

First express $y_n=\sum_{k=1}^{2n} a_k/k$ over integers. The prefix gives $a_k=2^{n-k}$ for $1\le k\le n$. For $k=n+\ell+1$, the coefficient is the coefficient of $t^\ell$ in
$$
\sum_{j=0}^{n-1}(-1)^j(1-t)^j=\frac{1-(-1)^n(1-t)^n}{2-t}.
$$
Indeed integrating each summand against $t^n$ gives the beta corrections. In particular $Ly_n$ is integral. For each $p\mid P$, only denominators $k=pj$ contribute after multiplying by $p$ and reducing modulo $p$. Compute the simultaneous residue $0\le r<P$ by the Chinese remainder theorem from
$$
r\equiv (L/p)\sum_{j\le M/p} a_{pj}/j\pmod p.
$$
There are at most $\sqrt M$ terms per prime. Canceled primes also supply congruences, with residue zero. The possible fractional parts are exactly $r/L+j/H$ for $0\le j<H$ given these congruences alone. The unreduced common denominator keeps the calculation independent of which primes survive reduction.

**Size of the remaining grid (paper theorem).** Its size satisfies $\log H=2\sqrt M+o(\sqrt M)$, whereas $\log L=M+o(M)$. Indeed, writing $\vartheta(x)=\sum_{p\le x}\log p$ gives
$$
\log H=\vartheta(\sqrt M)+\sum_{a=2}^{\lfloor\log_2 M\rfloor}\vartheta(M^{1/a}).
$$
The first term and the square-power term each contribute $\sqrt M+o(\sqrt M)$ by the prime number theorem. Higher powers cost $O(M^{1/3}\log M)$ by the Chebyshev upper bound.

**Exact exclusion.** Let $B=2^T$, let $0\le a<B$ encode a length-$T$ binary word, and put $\eta=1/((2n+1)\binom{2n}{n})$. If the word occurs at $\{2^n\ln 2\}$ then the grid must intersect the closed interval $[a/B-\eta,(a+1)/B+\eta]$ modulo one, by the verified integral error bound. Equivalently the following inequality is necessary:
$$
\left\lceil\frac{L(a/B-\eta)-r}{P}\right\rceil
\ \le\
\left\lfloor\frac{L((a+1)/B+\eta)-r}{P}\right\rfloor .
$$
Unrestricted integer lifts in this test include both endpoints of the circle. Each word admits at most $1+\lfloor H(2^{-T}+2\eta)\rfloor$ lifts in the unwrapped interval. For $T=n$ this is at most one for all sufficiently large $n$. If $T$ is fixed instead, $H\ge2^T$ eventually and every cylinder contains a grid point. In particular, these large-prime data alone cannot exclude even one fixed twelve-bit word at sufficiently large positions. Information from the small-prime part or a statistical constraint on the full lift would be needed for that strategy. [Beta error bound](../NormalityChecker/LogShadowIntegral.lean)

**Finite exact computation.** The $2T$ words with at most one transition are the two constant words and the words with one final run of opposite bits. For $T=n$ at starts $64,128,256,512,1024$, the integer test rejects **all** of them, even allowing every possible small-prime lift. The respective bit lengths of $H$ are 33, 43, 64, 97 and 134. The true logarithm has at least two transitions among those $n$ digits in each example. The argument gives an arithmetic test for any specified list of low-transition words at any start. A lower bound proportional to the word length on a sufficient share of arbitrarily late shells remains open. [Integer sieve and checks against the fully reduced models](../scripts/strided_logarithm.py)
