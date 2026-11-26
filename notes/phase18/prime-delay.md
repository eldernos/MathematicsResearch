# How long a positive Taylor group must wait

Let $a_m=1/(m2^m)$, $m\ge1$. Consider an arbitrary partition of these terms into finite groups having dyadic rational sums. No ordering within a group, common odd part or bound on the number of its members is assumed. A group is complete by cutoff $N$ if its greatest original index is at most $N$.

## A logarithmic delay factor

Let $p$ be an odd prime, $1\le k<p$ and $L_k=\mathrm{lcm}(1,\ldots,k)$. If $p\ge 2^kL_k$, **every** group of terms from the first $kp$ indices containing a multiple of $p$ has a reduced denominator divisible by $p$. In fact this holds through any cutoff $N$ with $\lfloor N/p\rfloor=k$.

For a finite index set $G\subset[1,N]$ meeting $p\mathbb Z$, multiply its sum by $p$. Terms with indices prime to $p$ vanish modulo $p$ in the ring of rationals integral at $p$. The remaining terms yield
$$
 p\sum_{m\in G}a_m\ \equiv\ \sum_{j\in S}\frac1{j2^j}\pmod p,\qquad
 S=\{j\le k:pj\in G\}.
$$
Indeed $k<p$ ensures each such index has exactly one $p$ factor, and $2^{pj}\equiv2^j\bmod p$. Multiplication by $2^k L_k$, a unit modulo $p$, gives a positive integer strictly smaller than $2^k L_k$, since $S$ is nonempty and $\sum_{j\in S}1/(j2^j)<1$. It cannot vanish modulo $p$. This argument also supplies a finite obstruction test at smaller primes by testing the restricted subset sums modulo $p$.

Write $M(p)$ for the last original index in any dyadic group containing $a_p$. Since $\log L_k=k+o(k)$ by the prime number theorem, for every $c<1/(1+\log 2)$ and all sufficiently large primes $p$, choose $k=\lfloor c\log p\rfloor$. Then $p>2^k L_k$ and $M(p)\ge (k+1)p$. In particular
$$
 \liminf_{p\to\infty}\frac{M(p)}{p\log p}\ge\frac1{1+\log 2}.
$$
The logarithms in this estimate are natural. The same lower bound applies to completion of a group containing any of the first $k$ multiples of $p$. In a grouping restricted to common odd part $p$, the last term $m=p2^j$ has strictly largest dyadic exponent $m+j$, so a completed dyadic group then has reduced denominator exactly $2^{m+j}$. In unrestricted groups distinct indices can tie in dyadic exponent. The lower bound on $M(p)$ alone does not give that denominator formula for them. [Repository PNT and denominator estimates](../denominators.md) · [Common odd part construction](classical.md)

## Number of terms still in incomplete groups

There are $\gg N\log\log N/\log N$ distinct original indices $m\le N$ whose groups must still be incomplete at $N$, for every sufficiently large $N$. Take a small fixed $d>0$ with $2d(1+\log 2)<1$. For each $1\le j\le d\log N$, take primes $N/(2j)<p\le N/j$ and mark $m=jp$. Then $p>\sqrt N$ eventually and $k=\lfloor N/p\rfloor\le 2d\log N<p$. Uniformly over this range, $2^k L_k<p$ by the preceding asymptotic (bounded $k$ cause no problem). A finished group containing $m$ would violate the subset obstruction. The marked indices are distinct, since an integer at most $N$ cannot have two prime factors greater than $\sqrt N$. By the prime number theorem $\pi(x)-\pi(x/2)\gg x/\log x$ for every sufficiently large real $x$; here even the least $N/j$ tends to infinity. Summing the bounds $\gg N/(j\log N)$ proves the claim. This counts indices in unfinished groups. Many indices may belong to the same group, so it is not a lower bound of that order on the number of distinct groups.

There is also an exact invariant at the original observation cutoff. Denote by $P_N=2^N\sum_{m\le N}a_m$ the shifted Taylor prefix and by $U_N$ the shifted sum of the portions of **all unfinished groups** lying at or before $N$. Their difference is a dyadic rational, the sum over groups completed by $N$. For every odd prime $p$,
$$
 v_p(\mathrm{den}\,U_N)=v_p(\mathrm{den}\,P_N).
$$
Indeed adding a $p$-integral number preserves a negative valuation and preserves integrality otherwise. In particular the logarithm of the odd denominator of the combined unfinished pieces is $N+o(N)$. For the lower bound, choose $C>1+\log 2$. All primes $CN/\log N<p\le N$ meet the subset obstruction with $k=\lfloor N/p\rfloor$, and the PNT gives log product $N+o(N)$. For the upper bound the odd denominator divides $L_N$. Thus regrouping into positive dyadic sums cannot remove the exponential odd-denominator cost **at the original Taylor cutoffs** unless the incomplete groups are modeled by some additional means. The equality of odd denominators itself only uses dyadicity of completed groups. A different observation model or a transformed infinite identity may have other costs.
