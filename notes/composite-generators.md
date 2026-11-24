# Two generators with an odd composite denominator parameter

Take integers $`b,q,c\ge2`$ with $`c`$ odd and coprime to $`b`$. Suppose every prime divisor of $`q`$ divides $`b`$. For example, $`b=10,q=4,c=21`$ meets these hypotheses. The following is the checkpoint-7 argument for base-$`b`$ normality of

```math
X=\sum_{a,j\ge0}\frac{1}{q^a c^j b^{q^a c^j}}.
```

The normality conclusion now has a Lean proof for every positive integer order and every $`c\ge2`$ coprime to $`b`$. The proof below records the earlier order-one route, which establishes simultaneous denominator survival on paper. The formal proof uses separation at one prime and the qualitative short-orbit estimate. [Proof comparison](arithmetic-certificates.md#positive-orders-and-composite-generators) · [Formal series theorem](../NormalityChecker/MixedPowers.lean) · [Primewise separation](../NormalityChecker/CompositeLayers.lean)

## Separation and simultaneous denominator survival

Let $`P_n=b^n\sum_{q^a c^j\le n}1/(q^a c^j b^{q^a c^j})`$. Fix a prime $`r\mid c`$ and write $`e_r`$ for its multiplicity in $`c`$. Since $`q`$ and $`b`$ are units at $`r`$, the unshifted summand on layer $`j`$ has $`r`$-adic norm $`r^{e_r j}`$. Between integer cutoffs $`s<t\le qs`$, there is at most one new index with any given $`j`$. Thus the term with the largest new $`j`$ has strictly larger norm than the others. The ultrametric inequality implies that any intervening insertion on layer $`j`$ forces

```math
\max\bigl(|P_s|_r,|P_t|_r\bigr)\ge r^{e_r j}.
```

The exponent $`e_r`$ accounts for repeated prime factors in $`c`$. For different primes, different endpoints can supply the large norm. [Formal separation theorem](../NormalityChecker/CompositeLayers.lean)

Fix a cell $`[u c^m,(u+1)c^m]`$, with $`1\le u<c^6`$. Its endpoint ratio is at most $`q`$. Since $`c`$ and $`q`$ are coprime, the threshold mesh supplies one $`J`$ so every normalized subinterval of a prescribed width $`\eta>0`$ contains some $`q^a/c^i`$ with $`i\le J`$. For $`m\ge J`$ this threshold is an insertion on layer $`m-i`$. For a fixed $`r`$, two positions with $`|P_n|_r<r^{e_r(m-J)}`$ therefore lie less than $`\eta c^m`$ apart. Cover the bad positions by one such interval **per prime divisor**. If $`d`$ is the number of distinct primes dividing $`c`$, the total width is at most $`d\eta c^m`$. At a position outside their union, the reduced denominator of $`P_n`$ is divisible by $`c^{m-J}`$. [Mesh for arbitrary coprime integer generators](../NormalityChecker/LocalizedMeshRate.lean)

## Cancellation through every prefix

Set $`K=c^k`$, $`m=6k`$, and use blocks of length $`K^5`$ on $`[K^6,c^6K^6)`$. The number of insertions through this scale is $`O_{q,c}((k+1)^2)`$. The indices are distinct because $`\gcd(q,c)=1`$. Choose a fixed $`A`$ with $`q\mid b^A`$, for example the largest exponent in the prime factorization of $`q`$. At position $`n`$, the factor $`q^a`$ of an earlier index $`q^a c^j`$ has cleared as soon as $`n-q^a c^j\ge Aa`$. Here $`Aa=O(k+1)<K^5`$ eventually. Discard the block containing each insertion and its successor, including insertions immediately before the cell. The final partial block costs at most $`K^5`$ positions. For each prime $`r\mid c`$, charging the full blocks whose starts lie in its bad interval costs at most $`\eta K^6+K^5`$ per cell.

At a remaining start $`s`$, the denominator of $`P_s`$ divides $`c^{\lfloor\log_c s\rfloor}`$ and is at least $`c^{6k-J}`$. For a fixed nonzero Fourier frequency $`h`$, the reduced denominator $`Q`$ of $`hP_s`$ is therefore between $`K^6/(c^J|h|)`$ and $`c^6K^6`$. Write $`v_Q`$ for the multiplicative order of $`b`$ modulo $`Q`$. The formal period lemma applies to **every divisor** of a power of $`c`$ and gives

```math
Q\le (b^{\varphi(c)}-1)\,v_Q.
```

For sufficiently large $`k`$, the period exceeds $`K^5`$. The reduced numerator is a unit, so the same incomplete-orbit inequality as in the prime case gives a character sum $`O_c(K^4)`$ on each good block. The shifted tail is at most $`1/(n+1)`$ by comparison with the full logarithmic series in base two. Normalizing a partial cell by $`K^6`$ now costs $`O_{b,q,c,h,J}((k+1)^2/K)+d\eta`$. Take $`k\to\infty`$ first, then $`\eta\downarrow0`$. Summing the cells gives Weyl cancellation through all prefixes. This argument uses only the elementary period and incomplete-orbit estimates already in the repository. [Order for divisors of composite powers](../NormalityChecker/StonehamOrder.lean) · [Incomplete-orbit bound](../NormalityChecker/StonehamOrbit.lean) · [Prefix transfer](../NormalityChecker/ScaleTransfer.lean)

The cutoff bound $`Q\le c^6 K^6`$ uses the single exponent $`j`$ shared by all primes dividing $`c`$. With independent exponents for several off-base primes, the product of the available prime powers can be much larger. The finite-support proof now uses the kernel-verified qualitative short-orbit estimate for that case. [Finite-support comparison](localized-certificates.md#several-surviving-denominator-primes)
