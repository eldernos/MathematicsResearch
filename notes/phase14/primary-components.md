# Genuine prime-primary characters on growing logarithm windows

Write $e(t)=\exp(2\pi i t)$ and $e_q(a)=e(a/q)$. The rational prefix $Y_n$ is obtained by multiplying the Taylor series for $2\log(4/3)+\log(9/8)$ by $2^n$ and retaining exponents through $n$. Let $c_p(n)$ be its $p$-primary component in $\mathbb Q/\mathbb Z$: its order is a power of $p$, and subtracting it leaves a rational with denominator prime to $p$. This definition specifies its phase uniquely. The previous checkpoint gave one-prime cancellation on proportional subintervals. Here the projection is onto an arbitrary fixed number of primes and the interval may have any fixed positive power length. [Previous one-prime estimate](../phase13/complementary-characters.md) · [Combined rational prefix](../../NormalityChecker/StridedLogarithm.lean)

## Simultaneous cancellation

Fix an integer $r\ge1$ and $0<\delta<1$. At a large real scale $X$ select primes in $[2X/5,9X/20]$. Exclude those with $\operatorname{ord}_p(2)\le X^{1/3}$, and call the remaining set $G_X$. For every choice of distinct $p_1,\ldots,p_r\in G_X$ and every consecutive interval $I\subset [X,11X/10]$ of at least $X^\delta$ integers, one has
```math
 \left|\frac1{|I|}\sum_{n\in I}e\!\left(\sum_{i=1}^r h_i c_{p_i}(n)\right)\right|
 \le C_{r,\delta}X^{-\gamma_{r,\delta}}
```
for some $\gamma_{r,\delta}>0$, uniformly in the integer coefficients $h_i$ as long as $p_i\nmid h_i$ for at least one $i$. This is a paper application of Bourgain and Chang's incomplete exponential-sum theorem. The excluded set has size $O(X^{2/3}/\log X)$, since every such prime divides $\prod_{1\le t\le X^{1/3}}(2^t-1)$, whose logarithm is $O(X^{2/3})$. The prime number theorem in these fixed proportional intervals gives $|G_X|\asymp X/\log X$. [Bourgain–Chang, Theorem 2.5 and hypotheses (1)–(2)](https://doi.org/10.1016/j.crma.2004.08.007)

**Arithmetic identification.** For each selected $p$, we have $2p\le n<3p$. In the stride-two sum only the term with index $p$ has a pole. Its value $2^{n-2p+1}/p$ differs from $2^{n-1}/p$ by an integer by Fermat's theorem. There is no pole in the stride-three sum. Consequently $c_p(n)=2^{n-1}/p\bmod 1$ throughout the interval. Remove the coordinates for which $p_i\mid h_i$. On the remaining support $S$, put
```math
 Q=\prod_{p\in S}p,\qquad a=\sum_{p\in S}h_p\,Q/p.
```
Then $(a,Q)=1$ by reduction at each prime, and the summand is exactly $e_Q(a2^{n-1})$. Lean verifies the identified single-prime component, the denominator of the remainder after simultaneous removal, the sum identity, and coprimality. [Formal arithmetic](../../NormalityChecker/LogarithmPrimaryCharacters.lean)

**Incomplete sums.** The number of prime factors of $Q$ is bounded by $r$, each exceeds $Q^{1/(2r)}$ for large $X$, and $Q\le X^r$. With $\epsilon=\min(\delta,1/3)/(2r)$ one has $|I|>Q^\epsilon$ and every local multiplicative order exceeds $Q^\epsilon$. Absorb the first exponent into the unit numerator to use Theorem 2.5, which is uniform in that numerator. It gives the claimed bound since $Q\ge2X/5$. With a single surviving prime one may use the prime-modulus specialization of the same sum-product argument. The constants depend on the fixed support-size bound and the window exponent. The source supplies existence of a saving; this note does not give a numerical value for $\gamma_{r,\delta}$.

## Distribution across primes at a typical actual start

For a fixed $n$ form the empirical measure placing equal mass at $c_p(n)$ for all $p\in G_X$. Let $d_X(n)$ denote its extreme interval discrepancy. Uniformly over the same windows $I$, for some $\beta_\delta>0$,
```math
  \frac1{|I|}\sum_{n\in I}d_X(n)^2 \ll_\delta X^{-\beta_\delta}.
```
To see this let $M=|G_X|$ and let $F_n(h)$ be the mean of $e(h c_p(n))$ over its primes. On expanding $|F_n(h)|^2$ there are $M$ diagonal terms of size one. For every off-diagonal term, the theorem for two primes applies to $(h,-h)$ uniformly for $1\le h\le\sqrt X$. Thus the mean square of $F_n(h)$ in the window is $O(M^{-1}+X^{-\gamma_{2,\delta}})$. The one-dimensional Erdős–Turán inequality with $H=\lfloor\sqrt X\rfloor$, followed by weighted Cauchy–Schwarz on the harmonic sum, bounds the mean square discrepancy by $O(H^{-2}+(1+\log H)^2(M^{-1}+X^{-\gamma_{2,\delta}}))$. This gives the assertion. Including the excluded primes changes the empirical discrepancy by $O(X^{-1/3})$, so a power saving still holds. The sample here is the set of actual primary components **across primes at one start**. It has a different index from the real digit orbit. [Erdős–Turán input and conventions](../phase13/quantitative-normality.md)

## The uncontrolled Fourier direction

Writing $P_S(n)=\sum_{p\in S}c_p(n)$ and $R_S(n)=Y_n-P_S(n)$, the mixed character with frequencies $(h,k)$ is $e(kY_n+(h-k)P_S(n))$. Products for two distinct subsets have correlations controlled on their symmetric difference whenever $0<|h-k|<2X/5$. The independent review shows that almost every fixed-size subset then has small mixed means simultaneously on all eligible windows and all sufficiently small integer frequencies with $h\ne k$. The proof bounds exceptional subsets by the Gram matrix estimate $m^2\tau^2\le m+m(m-1)\rho$ for $m$ aligned means at least $\tau$ and off-diagonal correlations at most $\rho$. The equal-frequency character $e(hY_n)$ is exactly the missing direction. [Independent proof and scope](reviews/primary-characters.md) · [Lean Gram and alignment lemmas](../../NormalityChecker/LogarithmPrimaryCharacters.lean)

There is a precise obstruction to recovering that direction from odd-primary data alone. Given any rational $y$, target $t\in\mathbb R$ and integer $m\ge0$, put $z=y+2^{-m}\lfloor2^m(t-y)\rfloor$. Then $0\le t-z<2^{-m}$. The difference has power-of-two denominator, so even the entire list of odd-primary components agrees. Either reduced denominator divides $2^m$ times the other. These assertions are checked in Lean. Taking $t=2^n\beta$ and $m\asymp\log n$ can shadow an orbit with zero lower transition density while preserving all odd-primary projections of the original rational prefixes and their exponential denominator rate. Such a construction need not satisfy the logarithm's exact recurrence. Controlling that recurrence together with the missing diagonal character is the remaining arithmetic problem. [Finite denominator-preserving theorem](../../NormalityChecker/LogarithmPrimaryCharacters.lean) · [Countermodels with the precise common-denominator bound](reviews/primary-characters.md)

The script `python3 -B scripts/check_phase14_cancellation.py` checks the coprime remainders and the signed CRT arguments against reduced rational prefixes without using a floating-point phase.
