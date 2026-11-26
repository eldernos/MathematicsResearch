# Primary characters of the binary logarithm prefix

Fix an integer $r\ge1$ and $0<\delta<1$. Let $X$ tend to infinity, take integer positions in $J_X=[X,11X/10]$, and let $G_X$ consist of primes in $[2X/5,9X/20]$ for which the multiplicative order of $2$ exceeds $X^{1/3}$. Write $Y_n$ for the rational two-stride prefix approximating $2^n\log 2$, $e(x)=\exp(2\pi i x)$, and $e_q(a)=e(a/q)$. For each $p\in G_X$ let $c_p(n)$ be the $p$-primary component of $Y_n$ in $\mathbb Q/\mathbb Z$. Thus it has prime-power order at $p$, and the remaining summand has order coprime to $p$.

**Reviewed theorem.** There exists $\eta=\eta(r,\delta)>0$ such that for every set $S\subset G_X$ of size at most $r$, every tuple of integers $(h_p)_{p\in S}$ with at least one $h_p\not\equiv0\pmod p$, and every interval $I\subset J_X$ of $T\ge X^\delta$ consecutive integer positions,

```math
\left|\frac1T\sum_{n\in I}e\!\left(\sum_{p\in S}h_p c_p(n)\right)\right|
\ll_{r,\delta} X^{-\eta}.
```

The statement holds uniformly in the primes, frequencies and starting position. There are also estimates for the complementary summands for most choices of $S$, proved below. The frequency that gives the full real character remains undetermined. These are paper deductions at repository revision `6d653be`. The Lean inputs are the prefix identity and tail estimate. [Local identity](../../../NormalityChecker/StrideDenominatorRate.lean#L123) · [Real tail](../../../NormalityChecker/StridedLogarithm.lean#L119)

## The component and the conductor

Throughout the two bands, $20/9\le n/p\le11/4$. Thus $\lfloor n/p\rfloor=2$, and $n<p^2$ for large $X$. The defining sum gives $Y_2=2$. The theorem `short_prefix_regular` says that $Y_n-2^{n-2}Y_2/p$ has denominator coprime to $p$. Consequently $c_p(n)=2^{n-1}/p\pmod1$, of order exactly $p$. In reduced form $Y_n=A/(pd)$, this same component is $u/p$ with $u\equiv A d^{-1}\pmod p$, since $p\mid A-ud$. This accounts for the inverse of the complementary denominator. [Prefix definition](../../../NormalityChecker/StridedLogarithm.lean#L27) · [Short-prefix theorem](../../../NormalityChecker/StrideDenominatorRate.lean#L123)

Set $Q=\prod_{p\in S}p$ and $b=\sum_{p\in S}h_p(Q/p)$. Adding the already normalized fractions gives the joint character $e_Q(b2^{n-1})$. Its numerator satisfies $b\equiv h_p(Q/p)\pmod p$. Hence it is a unit modulo $Q$ precisely when every coordinate frequency is nonzero modulo its own prime. In general let $S'=\{p\in S:p\nmid h_p\}$ and set

```math
q=\prod_{p\in S'}p=\frac{Q}{\gcd(b,Q)},\qquad
a=\sum_{p\in S'}h_p(q/p).
```

The character is $e_q(a2^{n-1})$, with $\gcd(a,q)=1$ for $q>1$. The empty support gives the constant one. There is no second CRT inverse in $a$.

## Orders, short windows and joint counts

For $K=\lfloor X^{1/3}\rfloor$ every excluded prime divides $\prod_{t=1}^K(2^t-1)$. The logarithm of this product is at most $(\log 2)K(K+1)/2$, and each excluded prime contributes at least $\log(2X/5)$. There are $O(X^{2/3}/\log X)$ exclusions. The prime number theorem gives $\sim X/(20\log X)$ primes in the band, so the excluded fraction is $O(X^{-1/3})$, also $O_r(X^{-1/3})$ for distinct $r$-tuples with any excluded entry. The same proof accommodates any fixed order threshold $X^\alpha$ with $0<\alpha<1/2$, at relative cost $O(X^{2\alpha-1})$.

For $q>1$ as above, choose $\varepsilon=\min(\delta,1/3)/(2r)$. Then $q\le X^r$, every prime divisor exceeds $q^{1/(2r)}$ for large $X$, and both $T$ and every local order exceed $q^\varepsilon$. The number of prime factors counted with multiplicity is less than $r+1$. These check the standing hypotheses (1)–(2) and the strict inequalities of Bourgain–Chang, Theorem 2.5. For $I=\{L,\ldots,L+T-1\}$ substitute $n=L+s-1$ for $1\le s\le T$. The coefficient becomes $a2^{L-2}$, a unit modulo $q$. The theorem bounds this incomplete sum directly by $CTq^{-\sigma}$ for some $\sigma>0$. It requires neither completion to a period nor coprimality of the local orders. For the prime conductor, Bourgain's prime-field Theorem 3.2 with one base gives the same bound. Finally $q\ge2X/5$, and the constants can be chosen for all support sizes up to $r$. [Bourgain–Chang, pp. 464 and 466, Theorem 2.5](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2004.08.007.pdf) · [Bourgain, p. 325, Theorem 3.2](https://www.numdam.org/item/10.1016/j.crma.2004.06.013.pdf)

Uniformity over all frequencies already fails at a logarithmic length for one good prime. At a prescribed start $L$, take $h_p\equiv (2^{L-1})^{-1}\pmod p$. The first $T$ values are $e_p(2^j)$ for $0\le j<T$. Their mean differs from one by at most $2\pi(2^T-1)/(Tp)$, which tends to zero for $T=\lfloor\log_2 p\rfloor$. The theorem leaves a gap between this obstruction and polynomial lengths.

For half-open intervals $B_p\subset[0,1)$, the fraction of $n\in I$ with every $c_p(n)\in B_p$ differs from $\prod_{p\in S}|B_p|$ by $O_{r,\delta}(X^{-\eta}(\log X)^r+X^{-1})$. Indeed, on the grid of denominator $p$ the normalized Fourier coefficients of an interval indicator have total absolute value $O(\log p)$ by the geometric-series bound. Multiply the Fourier expansions and use the theorem on every nonconstant term. Each constant coefficient differs from $|B_p|$ by at most $1/p$. Taking dyadic intervals gives joint binary word counts for these primary components. The support bound is fixed throughout. A character involving every prime of the growing band has a conductor beyond this application.

## What follows for the complementary factors

Put $P_S(n)=\sum_{p\in S}c_p(n)$ and $R_S(n)=Y_n-P_S(n)$ modulo one. For distinct sets $S,U$ of $r$ primes, $e(R_S(n))\overline{e(R_U(n))}=e(P_U(n)-P_S(n))$. The common prefix cancels. The reviewed theorem with support bound $2r$ therefore controls this correlation for **every** such pair, including overlapping sets.

There is a stronger conclusion for **most** individual complements. For some $\beta=\beta(r,\delta)>0$, a relative-density-one family of $r$-subsets $S$ of $G_X$ satisfies, simultaneously for all windows in the theorem and all integers $|h|,|k|\le X^\beta$ with $h\ne k$,

```math
\left|\frac1T\sum_{n\in I}e\big(hP_S(n)+kR_S(n)\big)\right|\ll X^{-\beta}.
```

To prove this, fix a window $B$, write $\mathbb E_B$ for its uniform average, and set $v_S(n)=e(kY_n+(h-k)P_S(n))$. Assume $0<|h-k|<2X/5$. For $S\ne U$, the inner product $\mathbb E_B v_S\overline{v_U}$ has nonempty support on their symmetric difference. Suppose all its off-diagonal absolute values are at most $\rho$. If $m$ sets satisfy $|\mathbb E_B v_S|>\tau$, align the phases of these $m$ averages. Cauchy–Schwarz applied to their sum gives

```math
m^2\tau^2 \le m+m(m-1)\rho.
```

Hence at most $2\tau^{-2}$ sets are exceptional whenever $\rho\le\tau^2/2$. The bound holds for any common sequence in place of $Y_n$.

Partition $J_X$ into consecutive blocks of $\lfloor X^{\delta/2}\rfloor$ positions and a final remainder. On each full block the reviewed theorem with parameters $2r,\delta/3$ gives $\rho\ll X^{-\eta_0}$, uniformly in $h-k$. Choose $0<\beta<\min(\eta_0/2,\delta/8)$ and set $\tau=X^{-\beta}$. Summing the exceptional-set bound over $O(X^{1-\delta/2})$ blocks and $O(X^{2\beta})$ frequency pairs excludes at most $O(X^{1-\delta/2+4\beta})$ sets. This is even $o(|G_X|)$, so after any $r-1$ primes have been prescribed, only $o(|G_X|)$ choices of the final prime can be exceptional. Every $I$ of length at least $X^\delta$ is covered by its full blocks except for at most $2X^{\delta/2}$ endpoint positions. Their contribution to its mean is $O(X^{-\delta/2})$, proving the claim with the same exceptional family for every window.

Taking $h=0$ gives power cancellation for every low nonzero frequency of the residual, for most $S$. The one-dimensional Erdős–Turán inequality then bounds its interval discrepancy by $O(X^{-\beta}\log X)$. The exact residual orbit is that of the shifted number $\log 2-\tfrac12\sum_{p\in S}1/p$. Its circle distance from $R_S(n)$ is at most $4/(X+1)$, so enlarging or shrinking test intervals by that amount gives the same discrepancy bound. In particular, each fixed word of length $d$ has frequency $2^{-d}+O(X^{-\beta}\log X)$ on the specified windows for these shifted numbers. Both the rational shift and the choice of primes depend on the band. [Prefix tail](../../../NormalityChecker/StridedLogarithm.lean#L119) · [Erdős–Turán inequality, Theorem 2.2(9)](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf#page=4)

On the diagonal $h=k$, the summand is exactly $e(kY_n)$ for every $S$. In particular the unweighted product of the selected first character and its residual equals $e(Y_n)$. Replacing it by $e(2^n\log 2)$ costs at most $8\pi/(X+1)$ pointwise. Cancellation of the selected and residual averages, even with the off-diagonal mixed estimates, leaves this diagonal average free.

## Testing transfer to the original binary digits

Two constructions isolate the information missing from a transfer to $\log 2$.

* **Preserve the recurrence on a prescribed window.** Given its last index $H$ and a word length $d$, take a dyadic rational $A$ with $0<\log 2-A<2^{-H-d}$. The prefixes $Y'_n=Y_n-2^n A$ obey the original inhomogeneous recurrence, have every original odd-primary component, and satisfy the original tail bound for the new target $\log 2-A$. At every start in the window the target's next $d$ bits are zero. This changes the initial value to $-A$ and chooses $A$ for that window. [Recurrence](../../../NormalityChecker/StrideDenominatorRate.lean#L15) · [Phase13 finite-window obstruction](../../phase13/complementary-characters.md#obstructions-at-the-real-place)
* **Preserve the data at every scale.** Choose the irrational $x=\sum_{j\ge0}2^{-2^j}$, whose binary ones and transitions have density zero. For $n\ge2$ let $g_n$ be the largest power of two at most $\lfloor n/2\rfloor$. Define the rational $Y'_n=Y_n+\lfloor g_n(2^nx-Y_n)\rfloor/g_n$. The added dyadic preserves every odd-primary component for every $n$, and the denominator still divides $\operatorname{lcm}(1,\ldots,\lfloor n/2\rfloor)$. Moreover $0\le2^nx-Y'_n<1/g_n\le4/(n+1)$ since $n+1\le4g_n$. One can take $Y'_0=Y'_1=0$. This construction preserves the initial value, common denominator bound, one-sided tail precision and all the tested characters on all bands. It changes the recurrence. Thus even these simultaneous local data are compatible with zero limiting frequency of the word $1$. [Common denominator](../../../NormalityChecker/StridedLogarithm.lean#L48) · [Sparse binary orbit](../../phase13/logarithm-transitions.md#a-sharp-sparse-example)

The actual recurrence together with $Y_0=0$ uniquely specifies the logarithm prefix. Neither comparison changes a digit of the actual $\log 2$. A word-density conclusion for that number still needs information about the diagonal real averages or another input using this specific solution.

As a finite arithmetic check, at $X=1000$ and $p=401,421,443$ the reduced-denominator CRT formula agrees with $2^{n-1}/p$ in all 303 prime-position pairs. Testing $h_p\in\{0,1,-1,p\}$ gives the stated conductor and phase in all 6,464 cases. These checks use the exact rational recurrence and do not estimate asymptotic rates.
