# Phase 19 Track E. Positive multiples of a prime in the logarithm series

Write $a_m=1/(m2^m)$, so that $\log 2=\sum_{m\ge1}a_m$. For an odd prime $p$, how far must a finite set of these positive terms extend before it contains $a_p$ and has a dyadic rational sum? The answer is exactly $p\,k(p)$ for every $p\ge5$. Here $k(p)$ is the least largest multiplier in a positive cancellation of the simple pole at $p$, a subset-sum problem modulo $p$. The proved range is

```math
\left(\frac{1}{\log 2}-o(1)\right)\log p\ \le\ k(p)\ \le\ 3\sqrt{4p-3}
```

The lower bound holds for all primes outside a set of relative density $O(1/\log X)$ in $(X/2,X]$, and the upper bound holds for every $p\ge41$. For every $p\le10^6$ the exact value exceeds $\log_2 p$ by at most $5.2$. Its distribution follows a random subset-sum model except in the far lower tail.

**Scope.** Nothing here gives normality, or an asymptotic discrepancy bound below one, for $\log 2$ or any other classical constant. The results concern finite positive regroupings of the Taylor series and the reduced denominators of its shifted prefixes. All finite assertions are checked in exact arithmetic by [`scripts/phase19_classical.py`](../../scripts/phase19_classical.py). An independent cross-provider review proved the same-cutoff lifting theorem and refined the average-loss exponent. One proof of each is kept below, and the refinement is cited rather than repeated. [Independent review](reviews/classical.md)

Logarithms are natural unless a base is written. $v_p$ is the $p$-adic valuation, $L_k=\mathrm{lcm}(1,\ldots,k)$ and $q_p(a)=(a^{p-1}-1)/p$ is the Fermat quotient.

## Summary

| Result | Statement | Evidence |
| --- | --- | --- |
| Same-cutoff lifting (§2) | For $p\ge5$ the least last index of a positive dyadic group containing $a_p$ is exactly $p\,k(p)$. For $p=3$ it is $12$. | Proof, and 2,260 explicit groups for $5\le p\le 20000$ |
| Upper bounds (§3) | $k(p)\le p-1$ for $p\ge5$. $k(p)\le\lceil3\sqrt{4p-3}\rceil$ for $p\ge41$. A Fourier non-concentration hypothesis gives $k(p)=O(\log p)$. | Proofs |
| Lower bounds for almost all primes (§4) | At most $2^{k-1}\cdot1.7320\,k/\log Y$ primes $p>\max(k,Y)$ have $k(p)\le k$. Hence $k(p)\ge\log_2p-2\log_2\log_2p$ off a set of relative density $O(1/\log X)$. | Proof, exact lists for $k\le12$ |
| Partitions (§4) | Every positive dyadic partition has $M(p)\ge p(\log_2p-2\log_2\log_2p)$ for almost all $p$, and closing index $M_N\ge(1-o(1))N\log_2N$. | Proof |
| Glaisher blocks (§5) | The full first block of multiples of $p$ sums to $q_p(2)$ modulo $p$. The odd block sums to $\frac34q_p(3)$. Analogues hold in base $b$ and in order two. | Proof, exact check for $p\le5000$ |
| Wieferich bands (§5) | In the band $\lfloor n/p^a\rfloor=p-1$ the shifted prefix keeps its full power $p^a$ exactly when $p$ is not a Wieferich prime. | Proof, exact valuations at 1093 and 3511 |
| Average loss (§6) | The mean of $\log(L_n/Q_n)$ over $n\le X$ is at most $3.5\sqrt X$ for $X\ge100$. The review refines this to $O(X^{3/7})$. | Proof, review, exact losses |

## 1. The local problem

For an odd prime $p$ and $p\nmid j$ write $x_j(p)\equiv(j2^j)^{-1}\pmod p$. Clearing one factor of $p$ from $a_{jp}$ and applying Fermat's theorem gives the following.

**Lemma 1.1 (one-pole reduction).** *For a finite set $G\subset[1,p^2)$ of indices,*

```math
v_p\Bigl(\sum_{m\in G}a_m\Bigr)\ge0\quad\Longleftrightarrow\quad\sum_{j:\ pj\in G}x_j(p)\equiv0\pmod p.
```

Indeed every multiple of $p$ below $p^2$ is $jp$ with $j<p$, and $p\,a_{jp}=1/(j2^{jp})\equiv1/(j2^j)$. Terms prime to $p$ are $p$-integral. This is the [Phase 18 prime-index obstruction](../phase18/prime-delay.md).

**Definitions.** Let $k(p)$ be the least value of $\max S$ over sets $S\subset[1,p-1]$ with $1\in S$ and $\sum_{j\in S}x_j(p)\equiv0\pmod p$, with $k(p)=\infty$ if there is none. Let $k^*(p)$ be the same minimum over all nonempty $S$, without requiring $1\in S$. Let $M_{\rm glob}(p)$ be the least $\max G$ over finite $G\ni p$ with $\sum_{m\in G}a_m\in\mathbb Z[1/2]$. In a partition $\mathcal P$ of the positive integers into finite groups with dyadic sums, $M(p)$ denotes the largest index in the group containing $p$, so $M(p)\ge M_{\rm glob}(p)$.

The smallest values are $k(5)=2$, $k(13)=3$, $k(11)=k(41)=4$ and $k(7)=6$. For $p=3$ the residues $x_1(3)=x_2(3)=2$ admit no cancellation inside $[1,2]$; the first admissible multiplier set is $\{1,4\}$.

## 2. Global completion costs nothing beyond local cancellation

**Lemma 2.1 (translation growth).** *If $r_1,\ldots,r_n$ are nonzero residues modulo a prime $q$, their subset sums (empty sum included) occupy at least $\min(q,n+1)$ residues.*

*Proof.* If $A\cup(A+r)=A$ for a nonzero $r$, then $A$ is invariant under translation by $r$, which generates $\mathbb Z/q$, so $A$ is empty or everything. Each new element therefore enlarges a proper nonempty set of sums. $\square$

In particular the $q-1$ residues $x_1(q),\ldots,x_{q-1}(q)$ represent every residue modulo $q$ as a subset sum. The script confirms this directly for every odd $q<400$.

**Theorem 2.2 (same-cutoff lifting).** *Let $p$ be an odd prime and $S\subset[1,p-1]$ nonempty with $\sum_{j\in S}x_j(p)\equiv0\pmod p$. Put $k=\max S$. There is a finite $G$ with*

1. *$G\cap p\mathbb Z=pS$ and $\max G=pk$,*
2. *every element of $G\setminus pS$ at most $k(k-1)$,*
3. *$\sum_{m\in G}a_m\in\mathbb Z[1/2]$, with reduced denominator exactly $2^{pk+v_2(k)}$.*

*Proof.* Start with $G=pS$. Its $p$-adic part is integral by Lemma 1.1, and every other odd prime in its denominators divides some $j\le k$. Process the odd primes $q<p$ that occur in decreasing order. At $q$, let $T$ be the sum of the current terms divisible by $q$. While $v_q(T)=-e<0$, let $c\equiv q^eT\pmod q$ be the leading digit and add the terms $a_{q^et}$ for a set of $t\in[1,q-1]$ with

```math
\sum_t x_t(q)\equiv-c\pmod q.
```

Lemma 2.1 provides such a set, because $q^ea_{q^et}=1/(t2^{q^et})\equiv x_t(q)$ by Fermat. The valuation of $T$ then rises above $-e$.

Each added index $q^et$ has $q$-valuation exactly $e$ and all other odd prime factors below $q$, since $t<q$. So it never disturbs a prime already processed. It is new: an equal existing term at a larger prime $q_1$ or in $pS$ would force $q_1\mid t$ or $p\mid t$, and an equal term from a deeper level at $q$ would force $q\mid t$. It is prime to $p$, so the $p$-adic part is untouched. By induction every odd prime power met during the process divides a multiplier $j\le k$ or some $t<q_1\le k$. Hence $q^e\le k$, $t\le q-1\le k-1$ and $q^et\le k(k-1)<pk$. When all primes are processed the sum is dyadic.

For the reduced denominator compare the dyadic exponents $m+v_2(m)$. At $m=pk$ it is $pk+v_2(k)$. Earlier multiples $pj$ have $pj+v_2(pj)\le p(k-1)+\log_2k<pk$, and added terms have $m+v_2(m)\le k(k-1)+2\log_2k<pk$. A unique minimal $2$-adic valuation fixes the valuation of the sum. $\square$

The review found the same construction independently and added the exact retirement exponent in item 3.

**Corollary 2.3.** *For every prime $p\ge5$, $M_{\rm glob}(p)=p\,k(p)$. Also $M_{\rm glob}(3)=12$.*

*Proof.* Theorem 3.1 below gives $k(p)\le p-1$. Let $G\ni p$ be dyadic. If $\max G\ge p^2$ then $\max G>p\,k(p)$. Otherwise Lemma 1.1 turns $G\cap p\mathbb Z$ into an admissible $S\ni1$, so $\max G\ge p\max S\ge p\,k(p)$. Theorem 2.2 attains the bound. For $p=3$, an index $9$ in $G\subset[1,11]$ would be the only term with a double pole. Without it the multiples of 3 are among 3 and 6, whose residues are both $2$ modulo 3, so neither $\{3\}$ nor $\{3,6\}$ cancels the simple pole. The pair $\{3,12\}$ sums to $683/2^{14}$. $\square$

**Comparison with single rays.** Restricting a group to the ray $\{p2^i\}$, as in Phase 18, costs $p2^K$ for the least admissible $K$. Among the primes $5\le p\le20000$ the single-ray minimum is strictly larger than $p\,k(p)$ for all but four. For example, at $p=1009$ the costs are $8072$ and $1{,}033{,}216$. Phase 18 proved that single-ray groups cost more than $p^{3/2}/\log p$ for almost all $p$. The general minimum is at most $p\lceil3\sqrt{4p-3}\rceil$ for every $p\ge41$, and is near $p\log_2p$ in the data. [Phase 18 single rays](../phase18/classical.md#theorem-f22-superlinear-worst-case-and-super-square-root-typical-delay-on-single-rays)

**Partitions.** One prescribed group extends to a full positive dyadic partition: the review reserves constant-residue tail progressions on the finitely many affected odd rows. Achieving $M(p)=p\,k(p)$ for all $p$ in a single partition is open. Theorem 2.2 draws its corrections from small indices, and many primes compete for them. For instance the corrections at $q=3$ that introduce no new prime are the terms $3^e2^i$, which are exponentially sparse.

## 3. Upper bounds for the local problem

**Theorem 3.1 ($k(p)<p$).** *For every prime $p\ge5$, $k(p)\le p-1$.*

*Proof.* $x_2(p)/x_3(p)=24/8=3$, which is not $\pm1$ modulo $p$. So $0$, $x_2$, $x_3$ and $x_2+x_3$ are distinct. Lemma 2.1 applied to the remaining $p-4$ nonzero residues $x_4,\ldots,x_{p-1}$ fills $\mathbb Z/p$. Thus $-x_1\neq0$ is a nonempty subset sum. $\square$

This short argument is from the independent review.

**Lemma 3.2 (collisions).** *For $1\le i<i+d\le p-1$, $x_i(p)=x_{i+d}(p)$ holds exactly when $i(2^d-1)\equiv-d2^d\pmod p$. Hence each lag $d$ has at most one colliding pair. Any $n$ consecutive indices in $[1,p-1]$ carry at least $(n+1)/3$ distinct residues.*

*Proof.* The equation is $i2^i\equiv(i+d)2^{i+d}$. If $2^d\equiv1$ it reads $0\equiv-d$, which is impossible for $0<d<p$; otherwise it fixes $i$ modulo $p$. Let the value classes among the $n$ indices have sizes $r_1,\ldots,r_s$. Pairs inside classes have distinct lags in $[1,n-1]$, so $\sum_c\binom{r_c}2\le n-1$. For every integer $r\ge1$,

```math
r-1\le\frac r3+\frac13\binom r2,
```

which is equivalent to $(r-2)(r-3)\ge0$. Summing gives $n-s\le n/3+(n-1)/3$, so $s\ge(n+1)/3$. $\square$

**Theorem 3.3 (square-root bound).** *For every prime $p\ge41$,*

```math
k(p)\le\left\lceil3\sqrt{4p-3}\right\rceil.
```

*Proof.* Put $K=\lceil3\sqrt{4p-3}\rceil$. Since $9(4p-3)\le(p-1)^2$ for $p\ge41$, we have $K\le p-1$. The $K-1$ indices $2,\ldots,K$ carry a set $A$ of at least $K/3\ge\sqrt{4p-3}$ distinct residues by Lemma 3.2. By the Dias da Silva–Hamidoune theorem, sums of $h=\lfloor|A|/2\rfloor$ distinct elements of $A$ take at least $\min(p,h(|A|-h)+1)=\min(p,\lfloor|A|^2/4\rfloor+1)=p$ values. So $-x_1$ is a sum of distinct residues realized by distinct indices in $[2,K]$. $\square$

The review independently reached the same scale with a Cauchy–Schwarz count of distinct residues. Reserving index 1 before applying the restricted-sumset theorem is essential. [Dias da Silva and Hamidoune, 1994](https://doi.org/10.1112/blms/26.2.140)

**Theorem 3.4 (conditional logarithmic bound).** *Let $K\ge2$ and $0<c\le1$, and suppose that for every $h\not\equiv0\pmod p$*

```math
\Bigl|\sum_{j=2}^{K}e\bigl(h\,x_j(p)/p\bigr)\Bigr|\le(1-c)(K-1),\qquad e(u)=e^{2\pi iu}.
```

*If $c(K-1)>4\log(p-1)$, then $k(p)\le K$.*

*Proof.* The number of sets $S\subset[2,K]$ with $x_1+\sum_Sx_j\equiv0$ equals

```math
\frac1p\sum_{h=0}^{p-1}e(hx_1/p)\prod_{j=2}^K\bigl(1+e(hx_j/p)\bigr).
```

The term $h=0$ is $2^{K-1}/p$. For $h\ne0$ write $\theta_j=hx_j/p$ and $\|\cdot\|$ for the distance to the nearest integer. Then $|1+e(\theta)|=2|\cos\pi\theta|$, and $\log\cos u\le-u^2/2$ gives $|\cos\pi\theta|\le\exp(-\pi^2\|\theta\|^2/2)$. From $1-\cos2\pi\theta\le2\pi^2\|\theta\|^2$ and the hypothesis, $\sum_j\|\theta_j\|^2\ge c(K-1)/(2\pi^2)$. Each product is therefore at most $2^{K-1}e^{-c(K-1)/4}$, and the $p-1$ terms with $h\ne0$ cannot cancel the main term. $\square$

The hypothesis asks only that no dilate of $\{x_2,\ldots,x_K\}$ concentrate near zero. Under square-root cancellation it holds with $K\approx4\log p$. No current exponential-sum method treats sums of length $O(\log p)$ over this mixed sequence. Bourgain-type estimates cover short geometric progressions $g^j$, but not $2^{-j}/j$.

**Random-model prediction.** If the residues behaved like independent uniform residues, the $2^{K-1}$ admissible sums would miss the target with probability about $\exp(-2^{K-1}/p)$. The model predicts $k(p)=\log_2p+O(1)$ for most $p$, with a doubly exponential upper tail. Its prediction for the largest excess over $p\le X$ is $\log_2\log X+O(1)$. Section 7 compares the data with this model. We conjecture $k(p)=\log_2p+O(\log\log p)$, and hence $M_{\rm glob}(p)=(1+o(1))\,p\log_2p$.

## 4. Lower bounds for almost all primes

**Theorem 4.1 (exceptional primes).** *Let $k\ge1$ and $Y\ge3$. Fewer than $2^{k-1}\cdot1.7320\,k/\log Y$ primes $p>\max(k,Y)$ satisfy $k(p)\le k$. Fewer than $(2^k-1)\cdot1.7320\,k/\log Y$ satisfy $k^*(p)\le k$.*

*Proof.* For nonempty $S\subset[1,k]$ put

```math
N_S=\sum_{j\in S}\frac{2^{k-j}L_k}{j}.
```

This is a positive integer with $N_S<2^kL_k\log2$, because $\sum_{j\ge1}1/(j2^j)=\log2$. For $p>k$ the factor $2^kL_k$ is a unit modulo $p$, and $2^kL_k\sum_{j\in S}x_j(p)\equiv N_S$. So $S$ cancels the pole at $p$ exactly when $p\mid N_S$. By Rosser and Schoenfeld, $\psi(x)<1.03883x$, so $\log N_S<k\log2+\psi(k)<1.7320\,k$. Each $N_S$ has fewer than $1.7320\,k/\log Y$ prime factors above $Y$. Sum over the $2^{k-1}$ sets containing 1, or over all $2^k-1$ nonempty sets. $\square$

The exact sets for $k\le12$ are computed by factoring every $N_S$. They agree with the bitset survey below $2\times10^5$. The counts of primes $p>k$ with $k(p)\le k$ are $0,1,2,6,13,27,53,109,205,370,711,1440$ for $k=1,\ldots,12$. The first new primes at $k=4$ are $11,41,107,131$, from the numerators $33,41,107,131$.

**Corollary 4.2.** *As $X\to\infty$, the number of primes $p\in(X/2,X]$ with $k(p)\le\log_2X-2\log_2\log_2X$ is at most $0.866\,X/(\log_2X\cdot\log(X/2))=O(\pi(X)/\log X)$. For any fixed $c$, at most a proportion $(1.732+o(1))2^{-c}$ of these primes have $k(p)\le\log_2X-\log_2\log_2X-c$.*

*Proof.* Insert $k=\lfloor\log_2X-2\log_2\log_2X\rfloor$, respectively $k=\lfloor\log_2X-\log_2\log_2X-c\rfloor$, and $Y=X/2$ in Theorem 4.1, and compare with $\pi(X)-\pi(X/2)\sim X/(2\log X)$. $\square$

At $X=10^6$ the threshold is $k\le11$. Exactly 18 of the 36,960 primes in $(5\times10^5,10^6]$ fall below it, against the bound 3,311. At $X=2\times10^5$ the threshold is $k\le9$, and 6 of the 8,392 primes in $(10^5,2\times10^5]$ fall below it.

**Corollary 4.3 (all positive dyadic partitions).** *In every partition of the positive integers into finite groups with dyadic sums:*

1. *$M(p)>p\,(\log_2p-2\log_2\log_2p)$ for all primes $p$ outside a set with $O(X/\log^2X)$ elements up to $X$;*
2. *the index $M_N$ needed to close every group meeting $[1,N]$ satisfies $M_N\ge(1-o(1))N\log_2N$.*

*Proof.* (1) By Lemma 1.1, a dyadic group containing $p$ and ending at or before $kp<p^2$ yields $S\ni1$ with $\max S\le k$. Apply Corollary 4.2 on dyadic ranges. (2) For fixed $\varepsilon>0$ the interval $(N(1-\varepsilon),N]$ contains $\gg\varepsilon N/\log N$ primes, more than the exceptional count. Choose one outside the exceptional set. $\square$

In natural logarithms this replaces the Phase 18 constant $1/(1+\log2)\approx0.5906$ by $1/\log2\approx1.4427$ for almost all primes. For every individual prime the Phase 18 bound $p\le2^kL_k$ is still the best available. The two agree with the random model up to the factor between $\log_2p$ and the true $k(p)$. [Phase 18 prime delay](../phase18/prime-delay.md) · [Strategy B2](../phase18/classical.md#theorem-f24-persistence-of-the-exponential-denominator-growth-obstruction)

## 5. Glaisher blocks and Wieferich exceptions

**Lemma 5.1 (Glaisher's congruence).** *For an odd prime $p$ and a $p$-integral rational $y$,*

```math
\sum_{j=1}^{p-1}\frac{y^j}{j}\equiv\frac{1-y^p-(1-y)^p}{p}\pmod p.
```

*Proof.* For $1\le j\le p-1$, $\binom pj=\frac pj\binom{p-1}{j-1}$ and $\binom{p-1}{j-1}\equiv(-1)^{j-1}\pmod p$. Expand $(1-y)^p$, use $(-y)^p=-y^p$, and divide by $p$. $\square$

This is the congruence Granville takes as his starting point, credited there to Glaisher. [Granville, 2004](https://emis.univie.ac.at/journals/INTEGERS/papers/e22/e22.pdf)

**Theorem 5.2 (block sums).** *For every prime $p\ge5$:*

1. *$\sum_{j=1}^{p-1}x_j(p)\equiv q_p(2)$;*
2. *$\sum_{j\ \text{odd},\ j<p}x_j(p)\equiv\frac34q_p(3)$;*
3. *for an integer $b\ge2$ with $p\nmid b(b-1)$, $\sum_{j=1}^{p-1}(jb^j)^{-1}\equiv b^{-1}q_p\bigl(b^b/(b-1)^{b-1}\bigr)$;*
4. *$\sum_{j=1}^{p-1}(j^22^j)^{-1}\equiv-\frac12q_p(2)^2$.*

*Proof.* Item 1 is Lemma 5.1 at $y=1/2$, since $(1-2^{1-p})/p\equiv q_p(2)$. At $y=-1/2$ the lemma gives $q_p(2)-\frac32q_p(3)$ for the alternating sum. Averaging this with item 1 gives item 2. For item 3 take $y=1/b$ and write $b^p=b(1+p\,q_p(b))$ and $(b-1)^p=(b-1)(1+p\,q_p(b-1))$. The numerator becomes $p\bigl(b\,q_p(b)-(b-1)q_p(b-1)\bigr)$. Logarithmic additivity of $q_p$ modulo $p$ gives the stated form. For item 4, Granville proved $\sum_{j=1}^{p-1}2^j/j^2\equiv-q_p(2)^2$. The substitution $j\mapsto p-j$ turns $(j^22^j)^{-1}$ into $2^{j-1}/j^2$. $\square$

The script checks all four items for every prime $5\le p\le5000$, with $b\in\{3,5,10\}$ in item 3. A one-off run extended the check to $p<20000$.

**Corollary 5.3 (complete blocks).** *The full first block $\{jp:1\le j\le p-1\}$ cancels the pole at $p$ exactly when $p$ is a Wieferich prime. The odd block, which contains $a_p$, cancels it exactly when $p$ is a Wieferich prime to base 3.*

The only known Wieferich primes are 1093 and 3511, and there are no others below $6.7\times10^{15}$. The only known base-3 examples are 11 and 1006003. By Theorem 3.3 these complete blocks are far from optimal, yet they are the natural choices of complete residue systems. Arithmetic decides them. [Dorais and Klyve, 2011](https://cs.uwaterloo.ca/journals/JIS/VOL14/Klyve/klyve3.html) · [Montgomery, 1993](https://www.ams.org/mcom/1993-61-203/S0025-5718-1993-1182246-5/)

**Corollary 5.4 (actual reduced denominators).** *Let $Q_n$ be the reduced denominator of the shifted prefix $R_n=2^n\sum_{m\le n}a_m$, and let $p$ be an odd prime with $(p-1)p^a\le n<p^{a+1}$. Then $p^a\mid Q_n$ exactly when $p$ is not a Wieferich prime. For $a=1$ a Wieferich prime disappears from $Q_n$ completely.*

The same holds for the shifted prefix of $\mathrm{Li}_2(1/2)$ with $p^{2a}$. For the base-$b$ prefix of $\log(b/(b-1))$ the exceptional primes are the Wieferich primes to base $b^b/(b-1)^{b-1}$.

*Proof.* The repository classification states that $p^{as}\mid Q_n$ exactly when $p$ does not divide the reduced numerator of $\sum_{j\le k}1/(j^sb^j)$, where $k=\lfloor n/p^a\rfloor$. Here $k=p-1$, so Theorem 5.2 applies. $\square$ [Prime survival in truncated polylogarithms](../denominators.md#which-prime-powers-survive)

The script computes the valuations directly from the multiples of $p$. At $p=1093$ and at both ends of the band $[1092\cdot1093,\,1093^2)$, and likewise at $p=3511$, it finds $v_p(Q_n)=0$. The neighbouring primes 1091, 1097 and 3499 keep their factor. For $a=2$ at $p=1093$, both ends of $[1092\cdot1093^2,\,1093^3)$ give $v_p(Q_n)=1$. So one factor of $1093$ survives there.

## 6. Average loss of the reduced denominator

Write $L_n=\mathrm{lcm}(1,\ldots,n)$ and let the loss be $\log(L_n/Q_n)$. The repository proves the pointwise bound $116\,n^{2/3}$ for the logarithm. [Pointwise bound](../denominators.md#how-much-can-cancel)

**Theorem 6.1.** *For $X\ge100$,*

```math
\frac1X\sum_{n=1}^X\log\frac{L_n}{Q_n}\le3.5\sqrt X.
```

*Proof.* Count the radix prime 2, and the odd primes $p\le\sqrt n$, as small. They cost at most their full exponent, in total at most $\pi(\sqrt n)\log n<2.5102\sqrt n$ by Rosser–Schoenfeld when $n\ge4$, and at most $\log3$ when $n\le3$. An odd prime $p>\sqrt n$ divides $L_n$ once. It is lost exactly when $p$ divides the reduced numerator $U(k)$ of $A_k=\sum_{j\le k}1/(j2^j)$ with $k=\lfloor n/p\rfloor<p$. For a fixed pair $(k,p)$ there are at most $p\le X/k$ such $n\le X$. Since $\sum_{p\mid U(k)}\log p\le\log U(k)<1.7320\,k$ and $k<\sqrt X$,

```math
\sum_{n\le X}\ \sum_{\substack{p>\sqrt n\\ p\ \text{lost}}}\log p\ \le\ \sum_{k<\sqrt X}\frac Xk\cdot1.7320\,k\ \le\ 1.7320\,X\sqrt X.
```

The small primes contribute at most $2.5102\,X^{-1}\sum_{n\le X}\sqrt n\le1.70\sqrt X$ to the mean for $X\ge100$. $\square$

**Refinement in the review.** The review proves the exponent $3/7$. Zeros of $A_k$ modulo $p$ at both $k$ and $k+h$ make $\sum_{i=1}^h2^{-i}/(k+i)\equiv0$. Clearing denominators gives a polynomial in $k$ of degree at most $h-1$. Its value at $-1$ is $2^{h-1}(h-1)!\not\equiv0$, so at most $h-1$ pairs have lag $h$. Splitting into blocks of length $H=\lceil K^{1/3}\rceil$ gives $Z_p(K)\le K/H+H^2/2+1=O(K^{2/3})$ zeros up to $K<p$. Four ranges of primes then cost $O(X^{3/7})$ each: $p\le X^{3/7}$; exponent two with $k\le X^{1/7}$; exponent one with $p>X^{4/7}$; and the remaining exponent-one primes through the sum $X^{-1/3}\sum_{p\le X^{4/7}}p^{1/3}\log p$. I rechecked the lag polynomial, the block count and each range, and agree. [Full argument](reviews/classical.md#a-refinement-of-the-average-denominator-loss-estimate)

**Exact losses.** The script computes $Q_n$ exactly for $n\le2000$ and checks the loss prime by prime against this decomposition. That includes $n=3$, where $R_3=16/3$ loses the radix factor 2. The mean losses for $X=100$, $500$, $1000$ and $2000$ are $2.90$, $4.83$, $6.69$ and $7.78$. The largest loss up to 2000 is $19.94$, at $n=1855$. Up to $3\times10^5$ there are exactly 174 large-prime drop pairs $(k,p)$, beginning $(2,5),(4,131),(5,661),(6,1327),(7,1163)$. Their mean contribution over $n\le3\times10^5$ is $3.79$. Heuristically each $U(k)$ meets primes near $X/k$ with probability $\asymp1/p$, so this part should be of order $\log X$. The proved bounds are far larger.

## 7. Computations

**Exact local minima.** A bitset dynamic program over $\mathbb Z/p$ computes $k(p)$ and $k^*(p)$ for every odd prime up to $10^6$. Running time is about 210 s with `--limit 1000000`; the default limit is $2\times10^5$. Results:

- $k(p)\le p-1$ for all $p\ge5$, as Theorem 3.1 requires.
- The largest excess $k(p)-\log_2p$ is $5.19$, at $p=920393$ with $k=25$.
- The smallest is $-9.74$, at $p=436967$ with $k=9$.
- The sums of $k(p)$ over odd primes through 100, 1,000 and 10,000 are 151, 1,480 and 15,090, agreeing with the review's independent meet-in-the-middle computation.

For the 78,473 primes $100<p\le10^6$, the values of $k(p)-\lceil\log_2p\rceil$ are distributed as follows:

| $k(p)-\lceil\log_2p\rceil$ | $\le-8$ | $-7$ | $-6$ | $-5$ | $-4$ | $-3$ | $-2$ | $-1$ | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| primes | 127 | 200 | 390 | 893 | 1626 | 3179 | 6178 | 10622 | 16097 | 19225 | 14449 | 5011 | 470 | 6 |

The geometric lower tail and the abrupt upper cutoff are the shapes the random model predicts. On $100<p\le2\times10^5$ the script replaces the residues by independent uniform ones, three times with fixed seeds, and compares histograms. The chi-square statistic is $31.0$ on 15 cells. About $16$ of it comes from the pooled far lower tail, where 3 primes have $k(p)\le\lceil\log_2p\rceil-9$ against $21.6$ expected. The 13 central cells and the upper tail contribute about $15$. The mean excess $k(p)-\log_2p$ is $0.680$. Below the bulk the actual primes are slightly rarer than the model's. A small $k(p)$ forces $p$ to divide one of a few fixed integers $N_S$ (Theorem 4.1), while the model draws independent residues at every prime. The $k^*(p)$ minimum agrees with $k(p)$ for 58% of these primes, and the largest difference is 11.

**Global groups.** For each prime $5\le p\le20000$ the script reconstructs a minimal set $S$, builds the group of Theorem 2.2, and verifies exactly that its sum is dyadic. It also checks that the group's largest index is $p\,k(p)$, that its multiples of $p$ are exactly $pS$, and that the remaining indices lie below $k(p)^2$. The example at $p=7$ is

```math
G=\{3,6,7,15,21,35,42\},
```

with sum $399245531709/2^{43}$, the value the review also recorded.

## 8. What remains open

- A bound $k(p)=O(\log p)$, even for almost all $p$, would need equidistribution of the subset sums of an explicit sequence of length $O(\log p)$ modulo $p$. Theorem 3.4 isolates the required non-concentration.
- Whether one positive dyadic partition can achieve $M(p)\le p^{O(1)}$ for every prime simultaneously.
- Lowering the average-loss exponent below $3/7$, or the pointwise exponent below $2/3$.
- The digit distribution of $\log2$. The completed groups have zero odd denominator, and the unfinished groups keep the full odd denominator of the prefix at every original cutoff. [Phase 18 invariant](../phase18/prime-delay.md#number-of-terms-still-in-incomplete-groups)

## Sources

- J. A. Dias da Silva and Y. O. Hamidoune, *Cyclic spaces for Grassmann derivatives and additive theory*, Bull. London Math. Soc. 26 (1994), 140–146. [DOI](https://doi.org/10.1112/blms/26.2.140)
- A. Granville, *The square of the Fermat quotient*, Integers 4 (2004), A22. The order-two congruence, with Glaisher's congruence as starting point. [PDF](https://emis.univie.ac.at/journals/INTEGERS/papers/e22/e22.pdf)
- J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94. The bounds $\psi(x)<1.03883x$ and $\pi(x)<1.25506x/\log x$.
- F. G. Dorais and D. Klyve, *A Wieferich prime search up to $6.7\times10^{15}$*, J. Integer Seq. 14 (2011), 11.9.2. [Article](https://cs.uwaterloo.ca/journals/JIS/VOL14/Klyve/klyve3.html)
- P. L. Montgomery, *New solutions of $a^{p-1}\equiv1\pmod{p^2}$*, Math. Comp. 61 (1993), 361–363. [Article](https://www.ams.org/mcom/1993-61-203/S0025-5718-1993-1182246-5/)

## Reproduction

```sh
python3 -B scripts/phase19_classical.py
python3 -B scripts/phase19_classical.py --limit 1000000 --group-limit 20000
```

The script uses only the Python standard library. It ends with `All Phase 19 classical checks passed.`
