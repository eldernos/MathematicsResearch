# Nearby Taylor cutoffs retain the full odd-denominator rate

Let $T_j=\sum_{k=1}^j 2^{-k}/k$. Fix an integer $K\ge1$, a nonnegative integer width $h$, and a binary shift $N\ge0$. Take any nonempty finite family of cutoffs $K\le j_i\le K+h$ and integers $a_i$ with $\sum_i a_i=1$. Write $q$ for the odd part of the reduced denominator of $2^N\sum_i a_i T_{j_i}$. All logarithms below are natural.

**Theorem (paper proof).** If $h=o(K)$, then $\log q=K+o(K)$ as $K\to\infty$, uniformly in the shift, the number of rows, their cutoffs and their coefficients.

**Proof.** Fix $v\ge1$. For sufficiently large $K$, each prime in

$$
\frac{K+h}{v+1}<p\le\frac K v
$$

is odd, exceeds $v$, and satisfies $p^2>K+h$. Exactly the multiples $p,2p,\ldots,vp$ occur in every row. Multiplication by $p$ makes every row integral at $p$. Fermat’s congruence $2^p\equiv 2\bmod p$ gives

$$
p\,2^N T_{j_i}\equiv 2^N T_v\pmod p.
$$

The positive rational $T_v$ is fixed. Only finitely many primes divide its numerator or denominator. Outside these exceptions the common residue survives every affine combination, because its coefficients sum to one. Thus each such prime divides $q$ exactly once, with no dependence on the coefficient heights.

For fixed $V$, the bands for $1\le v\le V$ are disjoint. By the prime number theorem in the form $\sum_{p\le x}\log p=x+o(x)$, their total mass divided by $K$ tends to $\sum_{v=1}^V(1/v-1/(v+1))=1-1/(V+1)$. Let $V\to\infty$ after taking the lower limit. The odd denominator divides $\mathrm{lcm}(1,\ldots,K+h)$, whose logarithm is $K+o(K)$ by the prime number theorem. This proves the uniform assertion.

On every surviving prime, the differences between the row numerators have zero image after clearing the common denominator with its single factor of $p$. The reference row has nonzero image. This is the infeasible case of the affine gcd criterion, even for the family consisting of every cutoff in the interval. The affine hypothesis matters. The difference $2^N(T_{K+1}-T_K)$ has odd denominator dividing $K+1$.

**A linear-width counterexample.** With every cutoff from $K$ to $2K$ available, an integer affine combination has odd denominator one. Work modulo dyadic rationals, in $\mathbb Q/\mathbb Z[1/2]$. The increment $T_k-T_{k-1}$ has order equal to the odd part of $k$. For $K<k\le2K$, the least common multiple of these orders is the odd part $D$ of $\mathrm{lcm}(1,\ldots,2K)$, because every integer up to $2K$ has a multiple in $(K,2K]$. The elements killed by $D$ form a cyclic group of order $D$ (multiplication by two is invertible modulo $D$). The increments generate its entirety since their orders have least common multiple $D$. In particular, an integer combination of the increments represents $-T_K$. Adding it to $T_K$ gives the claimed affine combination. This construction places no bound on either its coefficient norm or its real error.

## The minimum at proportional width

**Theorem (paper proof).** Suppose all integer cutoffs in $[K,K+h]$ are available. Let $q_0$ be the odd denominator of $T_K$, and $B$ the least common multiple of the odd parts of $K+1,\ldots,K+h$, with empty lcm one. The exact minimum odd denominator over all integer affine combinations is

$$
q_{\min}=\prod_{\substack{p^e\parallel q_0\\p^e\nmid B}}p^e.
$$

Indeed, the allowable adjustments are precisely integer combinations of successive increments. Modulo dyadic rationals these generate the whole cyclic subgroup killed by $B$, by the order argument above. If $p^e\parallel q_0$ and $p^e\nmid B$, every possible adjustment has smaller $p$-primary order, so the full $p^e$ survives. Every other primary component of $T_K$ can be canceled simultaneously by one member of that subgroup. Multiplication by $2^N$ preserves all odd orders.

For fixed $c>0$ and $h=\lfloor cK\rfloor$, it follows that

$$
\lim_{K\to\infty}\frac{\log q_{\min}}{K}
=\sum_{1\le v<1/c}\left(\frac1v-\frac{1+c}{v+1}\right).
$$

To see this, primes $p\le\sqrt{K+h}$ together contribute at most $O(\sqrt{K+h}\log K)$ to $\log q_0$. Each larger prime in $q_0$ occurs once. It survives the minimization exactly when no multiple falls in $(K,K+h]$. With $v=\lfloor K/p\rfloor\ge1$, this is precisely the band in the preceding proof. For nonempty bands one must have $vh<K$, so only boundedly many $v$ occur. A boundary band with $v=1/c$ has length $O_c(1)$ and contributes $o(K)$. On every remaining band the fixed residue is nonzero except at the finitely many numerator primes already identified. Apply the prime number theorem to these intervals. For example, at width $K/2$ the minimum rate is $1/4$. This is an optimum over all coefficients without a precision constraint.

**A family with a certified error budget.** Take $N=K$, $0<c\le1$, and write $R_j=2^K T_j$. For the odd primes $K/2<p\le(K+h)/2$ form

$$
X=R_K-4\sum_p(R_{2p}-R_{2p-1}).
$$

Each added increment is $-2^{K-2p+1}/p$. At the selected prime the only offending term of $R_K$ comes from $k=p$. Their sum is $2^{K-2p}(2^p-2)/p$, which is integral at $p$. All other odd denominator factors are preserved. Thus the odd denominator is exactly $q_0/\prod p$ and its logarithm is $(1-c/2)K+o(K)$. The coefficient norm is at most $1+8\,\#\{p\}$. Each row has unwrapped error at most $2^{K-j}/(j+1)$. The paired indices are distinct and at least $K$, so even the sum of the errors charged to the absolute coefficients is at most $9/(K+1)$. This guarantees tolerance $2^{-8}$ through every $j\ge0$ with $9\cdot2^{j+8}\le K+1$.

The largest selected prime satisfies $2p_{\max}=(1+c)K+o(K)$ by the prime number theorem. Its increment has uniquely smallest 2-adic valuation $K-2p_{\max}+1$ for large $K$, since $R_K$ has dyadic denominator exponent at most $\lfloor\log_2 K\rfloor$. Hence the logarithm of the **full** denominator of this particular family is $[1+c(\log 2-1/2)]K+o(K)$. The dyadic cost exceeds the saved odd log mass. At $K=2048$ and $h=1024$, the construction removes 70 odd primes, uses coefficient norm 561, and leaves a dyadic denominator exponent of 1013. The sum of the individually charged error bounds certifies shifts 0 through 2 at the stated tolerance. [Exact minimum and precision checks](../../scripts/phase15_taylor.py)

**Scope and prior work.** Shiu’s Theorem 2 gives the corresponding short-sum test for ordinary harmonic denominators. The repository’s denominator-growth results establish the single-row dyadic rate and the fixed-band residue argument. The uniform assertion uses the fact that all nearby rows contain exactly the same multiples. It rules out improving the exponential rate by adding more such rows, even if coefficient cost is ignored. Different series and the distribution of their real numerators require additional estimates. [Shiu, Theorem 2](https://arxiv.org/abs/1607.02863v2) · [Single-row theorem](../../NormalityChecker/DenominatorGrowth.lean) · [Strided prime bands](../strided-logarithm.md) · [Affine feasibility](../../NormalityChecker/AffineDenominator.lean)

## Feasible rows with large minimum height

In the general lifting problem, write the free coefficients as a vector in $\mathbb Z^r$, where $r=d-1$. Reduction modulo $M>0$ maps this vector to its dot product with the row differences. If $g$ is their gcd together with $M$, the image has $M/g$ elements. Thus the kernel lattice has index $M/g$. A box of radius $H$ in the maximum norm can meet at most $(2H+1)^r$ cosets. This volume count is a necessary condition for covering every offset. It gives no upper bound for the distance to the particular affine lattice specified by the target numerator.

For example set $M=2m$, take a reference numerator congruent to $m$, and take all the other numerators congruent to $m+1$. They can be pairwise distinct. The gcd is one and the sum $t$ of the free coefficients must satisfy $t\equiv m\bmod 2m$. The $\ell^1$ coefficient norm is at least $|t|+|1-t|\ge2m-1$, attained by using one free coefficient $m$ and reference coefficient $1-m$. One may make every row approximate the same preassigned real arbitrarily closely by choosing a sufficiently large common denominator $ML$ with $\gcd(L,M)=1$ and selecting nearby distinct numerators in those residue classes. This example explains why a growing row count, a lattice determinant, and small individual errors do not ensure a small coefficient cost for the prescribed coset.
