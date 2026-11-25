# How long are the rational periods in the actual Taylor orbit of log 2?

At binary shift $N$, let $P_N=2^N\sum_{j=1}^N( j\,2^j)^{-1}$, and let $q_N$ be the odd part of its reduced denominator. Then
$$
 \liminf_{N\to\infty}
 \frac{\log \operatorname{ord}_{q_N}(2)}{\log N\,\log\log N}
 \ \ge\ \frac{1}{2\log 2}.
$$
The same inequality holds after deleting any one prime-power axis, chosen separately for each $N$. More generally it holds for any off-radix modulus retaining a fixed positive proportion of the primes in $(N/2,N]$. All logarithms are natural. This is a lower bound for the order of the **specific radix** in the unit group. Exponential growth of $q_N$ on its own only gives a linear lower bound by $q_N\mid 2^{\operatorname{ord}_{q_N}(2)}-1$.

## Counting the possible local orders

Fix $b\ge2$ and $0<c<C$. Let $M>0$ be coprime to $b$, let $R=\operatorname{ord}_M(b)$ (one when $M=1$), and let $H$ count prime factors $\ell$ of $M$ in $(cN,CN]$. At such a prime the local order $d=\operatorname{ord}_\ell(b)$ divides $R$. For fixed $d$, these distinct primes divide $b^d-1$, giving at most $d\log b/\log(cN)$ candidates when $cN>1$. Every such prime is also of the form $1+jd$, $j\ge1$, giving at most $CN/d$ candidates. The smaller bound is at most the geometric mean. With $\tau$ the number of positive divisors,
$$
 H\ \le\ \tau(R)\sqrt{CN\log b/\log(cN)} .
$$
If $H\gg N/\log N$, this forces $\log\tau(R)\ge(\tfrac12-o(1))\log N$. In particular $R$ beats every polynomial in $N$. To get the constant above, here is the needed elementary upper half of the maximal-order estimate for $\tau$. Put $u=\log R$. For fixed $0<\varepsilon<1$ the primes at most $u^{1-\varepsilon}$ contribute at most $O(u^{1-\varepsilon}\log(u+2))=o(u/\log u)$ to $\log\tau(R)$, because every exponent is at most $u/\log2$. The larger primes, with exponents $a_p$, contribute at most $(\log 2)\sum a_p\le(\log 2)u/((1-\varepsilon)\log u)$. Let $\varepsilon$ tend to zero. Thus $\log\tau(R)\le(\log2+o(1))u/\log u$. The crude bound $\tau(R)\le R$ already gives $u\ge(1/2-o(1))\log N$, whence $\log u\ge\log\log N-O(1)$. Combining proves the stated liminf. The same calculation replaces $1/2$ by $\eta-1/2$ if $H\ge N^{\eta-o(1)}$ with $\eta>1/2$.

## Application to classical prefixes and proposed grids

For every odd prime $N/2<p\le N$, the term at $p$ is the only Taylor prefix term with negative $p$-valuation. Its numerator after the shift is a power of two. Thus all such primes divide $q_N$. The prime number theorem gives $H\sim N/(2\log N)$. Removing $o(N/\log N)$ prime axes, or subtracting any rational whose denominator meets only that many of these primes, preserves the hypothesis. Subtracting completed dyadic groups preserves every odd denominator valuation. The same argument applies to the $b$-ary $\operatorname{Li}_s(1/b)$ prefix for each positive integer $s$: omit the finitely many primes dividing $b$. For the signed BBP and Bellard prefixes use the established fixed-band *survival after reduction*. For example one may choose a closed subinterval of $(N/2,N)$ away from the finitely many band endpoints in the earlier proof; it contains $\gg N/\log N$ surviving primes. [Taylor grouping](../phase18/prime-delay.md) · [Signed BBP and Bellard survival](../phase18/reviews/classical-sources.md#the-bbp-and-bellard-denominators-f5)

Write $q_N=p^eQ_N$ for any chosen odd axis. To stay in one fixed residue class modulo the complement while sampling the $p$-grid, a return time must be divisible by $\operatorname{ord}_{Q_N}(2)$. This applies to every starting unit. Thus on any window of length $N^A$, with $A$ fixed, there are eventually no two distinct points of the model having the same residue modulo $Q_N$. The simple full-period count and the complete-grid traversal proof cannot certify even a positive share of such windows. The real approximation supplied by the ordinary Taylor truncation itself is only of order $1/N$ after the shift, before further doublings. Other rational approximants with cancellation of a macroscopic set of primes, shorter-orbit exponential sums, or different groupings face different questions. In particular the argument places no lower bound on the discrepancy of the true orbit of $\log 2$.

The counting lemma concerns a modulus with many distinct large prime factors. Growth of a denominator or its largest prime factor alone would not imply it: modulus $b^k-1$ has order dividing $k$. This explains the different outcome for the intentionally delayed all-primes construction: there the support grows on the scale of the logarithm of the observation cutoff, and its full period actually fits in the available plateaus. [Surviving grids](grids.md)

In particular there is a density constraint even on *synthetic* all-prime schedules. Suppose at observation time $F(L)$ the complement still contains $\gg L/\log L$ primes in $(L/2,L]$, and a complete complementary period is to fit within $F(L)^A$ for fixed $A>0$. Then necessarily
$$
 \liminf \frac{\log F(L)}{\log L\,\log\log L}\ \ge\ \frac1{2A\log2}
$$
along the cutoffs where both properties hold. A schedule polynomial in $L$ fails this test, regardless of the pole depth on the distinguished axis. This lower bound concerns complete-period methods; an incomplete-orbit theorem could have a different range.

## An infinite signed Mahler transform of the logarithm

Let $H(x)=\sum_{j\ge0}x^{2^j}$, so $H(x^2)=H(x)-x$. The telescoping product $\prod_{j=0}^J(1+x^{2^j})=(1-x^{2^{J+1}})/(1-x)$ gives the exact infinite identity
$$
 -\log(1-x)=\sum_{k\ge1}\frac{(-1)^{k-1}}{k}\,H(x^k),\qquad 0<x<1 .
$$
After taking logarithms and Taylor expanding, absolute convergence follows from $\sum_j-\log(1-x^{2^j})<\infty$. This is outside the *finite* differential algebra in the Phase 18 obstruction. The issue for synthesis is how much of the identity must be retained at an observation scale; here the answer is sharp up to an absolute factor.

Let $A_K$ retain $1\le k\le K$ at $x=1/2$. For each $j$, the alternating Taylor remainder for $\log(1+z)$ equals $(-1)^K\int_0^z u^K/(1+u)\,du$ at $z=2^{-2^j}$. All outer remainders therefore have the same sign. The first term bounds their absolute sum below by $(2/3)\,2^{-(K+1)}/(K+1)$. Summing the geometric upper bound over all positive integer exponents in place of the powers of two gives
$$
 \frac23\,\frac{2^{-(K+1)}}{K+1}
 \le (-1)^K(\log2-A_K)
 \le\ \frac{2^{-(K+1)}}{(K+1)(1-2^{-(K+1)})}.
$$
Thus $2^N|\log2-A_{K(N)}|\to0$ exactly when $K+1+\log_2(K+1)-N\to+\infty$.

Each fixed $A_K$ is a finite rational combination of the sparse rows $H(2^{-k})$, hence a universal normality-preserving translation by the finite-grid entropy argument. Its numerators also admit a precise test. Reducing $k=d2^a$ to odd $d$ by the functional equation leaves coefficient $1/(d2^{\lfloor\log_2(K/d)\rfloor})$ on $H(2^{-d})$ and a rational constant. The isolated-insertion proof for horizontal logarithm rows applies with exponents $d2^j$ (here there is no $+j$). For $K\ge3$ the coefficient at $d=3$ is nondyadic, so $A_K$ lies outside the numerical-preserver kernel. [Residue criterion](logarithm-rays.md)

At a moving cutoff with the required absolute accuracy one has $K\ge N-O(\log N)$, or $K$ is even larger. For every odd prime $N/2<p\le\min(K,N)$, the chronological radix prefix of $A_K$ contains the term $2^{-p}/p$ and no other term whose coefficient denominator is divisible by $p$: an eligible index $k$ divisible by $p$ is already at least $p$ and its next multiple or next doubled exponent exceeds $N$. Consequently its odd denominator, even after deletion of one prime axis, satisfies the same superpolynomial order lower bound as the Taylor prefix. The infinite signed identity supplies computable deterministic components and a quantified moving-tail obstruction. It leaves the distribution of the full logarithm open.
