# A product of two sparse numerical preservers

For any integer $b\ge2$ and $r\ge2$, there are two explicit irrational elements of $K_b$ whose product is a rational outside $K_b$. Let $A$ be the classical Moser–de Bruijn sequence, the set of nonnegative integers whose binary digits are zero in odd-numbered positions, numbering the units bit by zero. Let $B=2A$. Every nonnegative integer has a unique decomposition as $a+c$ with $a\in A,c\in B$, by splitting its binary digits into even and odd positions. Put
$$
 U=\sum_{a\in A}b^{-ra},\qquad V=\sum_{c\in B}b^{-rc}.
$$
Each sum has a term at zero. Apart from that integer, each radix expansion consists of separated ones on a set of counting function $O(\sqrt N)$. Indeed below $4^j$ there are $2^j$ possibilities for the even-position bits and likewise for the odd-position bits. This bound gives vanishing density, infinitely many ones and arbitrarily long runs of zeros. Both numbers are irrational by eventual periodicity of rational digits. Discarding a logarithmic neighborhood before each insertion gives, uniformly in $x$,
$$
 |D_N(x+U)-D_N(x)|+|D_N(x+V)-D_N(x)|
 = O_{b,r}(\log(2N)/\sqrt N).
$$
The real tails on the other positions are bounded by a geometric series in the neighborhood width. [Finite translation bound](../phase18/translations.md#sparse-signed-integers)

Absolute convergence and the unique additive decomposition give $UV=\sum_{n\ge0}b^{-rn}=b^r/(b^r-1)$. Its reduced denominator is coprime to the radix and exceeds $b-1$. Consequently $UV\notin K_b$, although this rational translation preserves normality by rational affine invariance. More precisely its orbit consists of the points represented by rotations of the cyclic word of length $r$ with one digit 1 and $r-1$ zeros (the fractional part is $1/(b^r-1)$). Its period is $r$, since $b^j-1<b^r-1$ for $0<j<r$. Its limiting discrepancy equals that of this nontrivial finite cycle, strictly below one. This example separates closure under multiplication from closure under addition and multiplication by scalars in $\mathbb Z[1/b]$. [Scalar classification](geometry.md#asymptotic-kernel-and-arithmetic-operations)

For any established normal number $X$ in this radix, $X+U$ and $X+V$ are explicit normality-preserving decompositions with the stated numerical rates. One may also replace either remainder by any finite sum of copies or radix-primary rational multiples, adjusting the clearing prefix. The product example does not decide whether two members of this sparse subclass can have a normal product.

## Sharp rates from missing digits in the insertion indices

More generally let $h\ge3$, let $S\subseteq\{0,\ldots,h-2\}$ contain zero and have $s\ge2$ digits, and let $A_S$ be the nonnegative integers having only digits in $S$ in base $h$. Put $\sigma=\log s/\log h$, choose an integer $r\ge2$, and set $W=\sum_{a\in A_S}b^{-ra}$. Then
$$
 \max_x |D_N(x+W)-D_N(x)|=1-D_N(W)
 \asymp_{b,h,S,r} \left(\frac{\log N}{N}\right)^{1-\sigma}.
$$
For the two factors above this gives $\asymp\sqrt{\log N/N}$. At scale $L$ many backward neighborhoods overlap, so adding up their individual lengths would give an extra factor of $\sqrt L$. For $b\ge3$, failure of multiplicative closure of $K_b$ already occurs on the rational $1/(b-1)$ and its square. The sparse examples belong to the smaller mean-zero subgroup in every radix, including binary, where the rational elements of $K_2$ themselves form a ring.

**Neighborhood count.** The number of elements of $A_S$ below $X$ is $\asymp X^\sigma$ for $X\ge2$, by bounding $X$ between consecutive powers of $h$. For $1\ll L\ll N$, take the least $k$ with $rh^k\ge 2(h-1)L$. The fine digits below $h^k$ lie in $[0,\kappa(h^k-1)]$ for $\kappa=\max S/(h-1)<1$. Thus the support $rA_S$ splits into clusters with first positions $rh^k a$, $a\in A_S$, width at most $\kappa rh^k$, and a gap before each noninitial cluster of at least $(1-\kappa)rh^k\ge2L$. There are $O((N/L)^\sigma)$ clusters that can meet $[0,N+L]$. Their backward $L$-neighborhoods have total length $O(N^\sigma L^{1-\sigma})$. Conversely $\gg(N/L)^\sigma$ noninitial clusters start in $[L,N)$, and at each such start $m$ the $L-1$ shifts $m-j$, $2\le j\le L$, see their next digit at exactly distance $j$. These sets are disjoint. This provides the matching lower count.

**Upper discrepancy deficit.** Choose $L=\lceil2\log_b N\rceil$. Uncharged shifts lie in $[0,C b^{-L}]$ modulo one, for a fixed $C$, by the geometric tail of the sparse digits. The concentration formula gives $1-D_N(W)\ll (L/N)^{1-\sigma}+b^{-L}$. In particular at least half the samples are within $C N^{-2}$ of zero for all sufficiently large $N$.

**Lower discrepancy deficit.** Put $R_N=(\log N/N)^{1-\sigma}$ and $L=\lfloor(1-\sigma)\log_b N/2\rfloor$. An arc of length at least $R_N$ costs at least $R_N$ in the concentration formula. A shorter arc that misses all the near-zero samples costs at least $1/2$. If it includes one such sample, every point of that arc has circle distance from zero at most $R_N+C N^{-2}$. At each of the $\gg N^\sigma L^{1-\sigma}$ shifts with next digit at distance $2\le j\le L$ counted above, the true fractional part is between $b^{-j}$ and $b^{-j}/(1-b^{-r})\le1/3$. Its circle distance from zero is therefore at least $b^{-L}$, strictly greater than $R_N+C N^{-2}$ for large $N$. All these shifts are missed. This gives the lower bound by taking the infimum over arcs. The rate concerns the worst translated input; the sharp translation identity gives equality at $x=0$.
