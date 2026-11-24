# Normality of mixed two-generator localized logarithms

Let $`b,q\ge2`$ be integers with $`q\mid b`$, and let $`p`$ be an odd prime coprime to $`b`$. Then

```math
X_{b,q,p}=\sum_{j=0}^{\infty}\sum_{a=0}^{\infty}
\frac{1}{q^a p^j b^{q^a p^j}}
```

is normal in base $`b`$. In particular, the series for $`\log 2`$ restricted to indices whose prime factors lie in $`\{2,p\}`$ is binary normal for **every odd prime** $`p`$. The theorem gives decimal normality for the supports $`\{2,7\}`$ and $`\{5,11\}`$ as well. A composite divisor $`q`$ is allowed. In that case the indices use powers of the single generator $`q`$. For instance, $`q=6`$ uses $`6^a`$, so the exponents of two and three in this cofactor are equal. Lean's `Localized.series_normal` states the result for the displayed series. [General and binary theorems](../NormalityChecker/LocalizedMixed.lean) · [Definition of normality](../NormalityChecker/Basic.lean)

## How frequently can denominator cancellation occur?

Write $`P_n`$ for the sum of $`b^{n-m}/m`$ over all supported $`m=q^ap^j\le n`$, and $`Q_n`$ for its reduced denominator. On $`p^k\le n\lt p^{k+1}`$ the largest available power of $`p`$ is $`p^k`$. For every $`\varepsilon\gt0`$, all sufficiently large $`L`$ satisfy the following bound for all sufficiently large $`k`$:

```math
\frac{\#\{p^k\le n\lt p^{k+1}:v_p(Q_n)\le k-L\}}{(p-1)p^k}
\le\varepsilon.
```

This includes positions at insertions and immediately afterward, when other factors can still occur in the denominator. For the pair $`\{2,5\}`$, the earlier exact calculation goes further and identifies every position where one factor of five disappears. [General density bound, `severe_loss_rare`](../NormalityChecker/LocalizedMesh.lean) · [Exact exponent for five](localized-logarithms.md)

**Separation.** Take two integer cutoffs $`s\lt t\le qs`$. In $`(s,t]`$, at most one term with a given exponent $`j`$ enters. Two such indices would have ratio at least $`q`$, while the smaller index is strictly greater than $`s`$. In the difference $`b^{-t}P_t-b^{-s}P_s`$, a newly inserted term $`1/(q^ap^j b^{q^ap^j})`$ has $`p`$-adic norm exactly $`p^j`$. If there is any insertion, its largest $`j`$ is unique. The ultrametric inequality gives the sum exactly the norm of that term. Since $`b`$ is a $`p`$-adic unit, each new index with exponent $`j`$ therefore forces

```math
\max\{|P_s|_p,|P_t|_p\}\ge p^j.
```

Equivalently, if a term from the top $`L`$ layers separates the cutoffs, their normalized unshifted prefixes have different residues modulo $`p^L`$. This comparison takes place within each scale and requires no stabilization of a residue across scales. [Proof of `separated_prefixes`](../NormalityChecker/LocalizedLayers.lean)

**A finite mesh.** Divide positions by $`p^k`$. A term on layer $`j=k-i`$ enters at $`q^a/p^i`$. The ratio $`\log p/\log q`$ is irrational, since equality of positive powers of $`p`$ and $`q`$ would give $`p\mid q`$. The forward rotation by $`-\log p`$ on the circle of circumference $`\log q`$ is dense. Consequently every open interval above one contains a threshold with $`a,i\ge0`$. Given $`u\ge1`$ and a width $`\delta\gt0`$, use a finite grid on $`[u,u+1]`$ and choose a threshold inside each grid interval. With the grid spacing less than $`\delta/2`$, every subinterval of width $`\delta`$ contains a threshold from some layer $`i\le J`$, with $`J`$ independent of $`k`$. [Forward rotation and finite mesh](../NormalityChecker/LocalizedMesh.lean)

Now $`u+1\le qu`$. Thus any two positions in this cell having $`|P_n|_p\lt p^{k-J}`$ are less than $`\delta p^k`$ apart. They need not occupy the whole interval between them. Its diameter alone bounds their number by $`\delta p^k+1`$. Since $`|P_n|_p\le p^{v_p(Q_n)}`$, choosing $`L\gt J`$ covers the stated denominator exception. Sum over $`u=1,\ldots,p-1`$ and absorb the integer endpoint errors by taking $`k`$ sufficiently large. [Exceptional diameter and shell count](../NormalityChecker/LocalizedMesh.lean)

## Fourier cancellation through every prefix

Unique factorization with respect to $`p`$ identifies each support index with one exponent pair. The omitted shifted tail satisfies $`0\le b^n X_{b,q,p}-P_n\le1/(n+1)`$. Fix a nonzero integer frequency $`h`$, let $`K=p^k`$, and cover $`[K^6,p^6K^6)`$ by cells $`[uK^6,(u+1)K^6)`$. Split a cell up to the desired cutoff into full blocks of length $`K^5`$ and one remainder. [Reindexing and tail bound](../NormalityChecker/LocalizedExpansion.lean)

- **Insertions.** Mark the block containing each insertion and the following block, including an insertion immediately before the cell. There are $`O_p((k+1)^2)`$ such blocks. At every other full block start $`s`$, each previous index $`m=q^ap^j`$ satisfies $`s-m\ge a`$. Thus $`q^a\mid b^{s-m}`$ and $`Q_s`$ is a power of $`p`$ at most $`s`$. Within the block $`P_{s+i}=b^iP_s`$. [Denominator and orbit identities](../NormalityChecker/LocalizedLayers.lean) · [Block construction](../NormalityChecker/LocalizedMixed.lean)
- **Severe losses.** Choose $`\delta`$ and its mesh depth $`J`$ before taking $`k`$ large. Apply separation at exponent $`6k`$. All block starts with $`|P_s|_p\lt p^{6k-J}`$ have diameter at most $`\delta K^6`$ within a cell. Their starts are $`K^5`$ apart, so charging their whole blocks costs at most $`\delta K^6+K^5`$. This count also holds when the cutoff is inside the exceptional region. [Partial-cell estimate](../NormalityChecker/LocalizedMixed.lean)
- **Surviving blocks.** The reduced denominator $`Q`$ of $`hP_s`$ is a power of $`p`$ with $`K^6/(p^J|h|)\le Q\le p^6K^6`$. Its modular period is at least $`Q/(b^{\varphi(p)}-1)`$. For large $`K`$ this exceeds the block length. The incomplete-orbit bound with $`K^4`$ translates gives a character sum of magnitude at most $`(p^6+2)K^4`$ per block. [Incomplete-orbit bound](../NormalityChecker/StonehamOrbit.lean) · [Period bound](../NormalityChecker/StonehamOrder.lean)

There are at most $`K`$ full blocks. After division by $`K^6`$, the partial-cell bound is $`\delta+O_p((k+1)^2/K)`$. The remainder costs at most $`1/K`$ and is included in the bound. Let $`k`$ grow with $`h,\delta,J`$ fixed and then let $`\delta`$ tend to zero. Summation over the geometric scales and transfer through the tail give Weyl cancellation for every nonzero $`h`$ and every final cutoff. [Kernel-checked assembly](../NormalityChecker/LocalizedMixed.lean) · [Scale transfer](../NormalityChecker/ScaleTransfer.lean)

## Quantitative interval discrepancy

Let $`D_N`$ be the supremum over all half-open intervals in $`[0,1)`$ of the absolute difference between the observed shift frequency and the interval length. For each fixed admissible triple, Lean proves that there are constants $`A>0`$ and $`N_0`$ such that, for **every** $`N\ge N_0`$,

```math
D_N(X_{b,q,p})\le \frac{A}{\log\log N}.
```

The constants depend on the triple. The estimate includes prefixes ending inside a cell and applies to the shifts of the infinite series. [Formal discrepancy theorem](../NormalityChecker/LocalizedDiscrepancy.lean)

**How many layers suffice?** For precision $`M\ge1`$, Dirichlet approximation supplies $`1\le i\le M`$ and $`a\ge0`$ with $`0<|i\log p-a\log q|\le\log q/(M+1)`$. The integers $`p^i`$ and $`q^a`$ differ by at least one. Comparing their logarithms gives the lower bound $`1/(qp^M)`$ for the same difference. Multiples of this short rotation step fill the circle of circumference $`\log q`$ to within one step. On $`[1,C]`$, where $`C=p^6`$, each interval of width $`3C\log q/(M+1)`$ contains a threshold $`q^a/p^i`$ with $`i\le J=Mq^2p^M`$. This gives an explicit width for the set of bad block starts. [Effective mesh](../NormalityChecker/LocalizedMeshRate.lean)

**How do intervals follow from characters?** Set $`z=M+1`$, take $`H=z^3`$ equally spaced circle points and smooth at distance $`1/z`$. The squared geometric sum on this grid gives a partition of unity. Its contribution from nodes farther than $`1/z`$ is at most $`z^2/H`$. On a good block of $`K^5`$ positions, every nonzero frequency below $`H`$ has a sum of size $`O_{b,p}(K^4)`$, including the cost of replacing the rational prefixes by the true orbit. The interval count therefore has relative error $`O_{b,p}(1/z+H/K)`$. Apply this estimate **inside good blocks**. Each exceptional position then costs at most one in the centered interval count, uniformly in $`H`$. [Finite Fourier inequality](../NormalityChecker/IntervalFourier.lean) · [Application to the actual radix shifts](../NormalityChecker/LocalizedDiscrepancy.lean)

**How does the cutoff enter?** Write $`K=p^k`$. There is a fixed integer $`R\ge2`$ such that $`k\ge R^{M+1}`$ suffices for the mesh, the simultaneous period bounds, and the $`O((k+1)^2)`$ insertion blocks. From that scale onward the centered count on any partial cell is $`O(C^k/z)`$. When $`C^{R^{M+2}}\le N<C^{R^{M+3}}`$, the entire earlier prefix costs at most $`N/z`$. Summing the remaining complete cells and the last partial cell costs $`O(N/z)`$. Since $`\log\log N=O(M+1)`$, the displayed discrepancy bound follows. [Finite prefix transfer](../NormalityChecker/ScaleTransfer.lean)

## Prior results and the three-prime obstruction

The manuscript *Binary normality of a localized logarithm* proves the binary $`\{2,3\}`$ case and gives a stronger discrepancy rate for that example. Its finite-prime theorem covers supports entirely coprime to the base and binary supports containing three. The mixed pair here shares a divisor with the base and can omit three. The earlier manuscript also traces the localized logarithm to Dibag. Priority for the general mixed case remains open to independent literature review. [Manuscript, §§4–5 and accompanying Lean development](https://github.com/CaptainSude/xi-normality/tree/06961817c7f61181ed9a5c73badb8d908d6ccdcc) · [Dibag (1989)](https://doi.org/10.1016/0021-8693(89)90180-4)

Two independent cofactors can defeat the separation step. In base ten with support $`\{2,3,5\}`$, consider the cutoffs $`3s`$ and $`5s`$ for $`s=3^j`$, $`j\ge1`$. The highest newly inserted layer contains **both** $`4s`$ and $`5s`$. After multiplying their unshifted contributions by $`s`$, their sum is $`(5\cdot10^s+4)/(20\cdot10^{5s})`$. The numerator is 9 modulo 27, since $`10^3\equiv1\pmod{27}`$. Two powers of three cancel in this pair. Lower layers can affect the full difference, but cannot restore the missing leading residue. The [full-prefix certificate](localized-certificates.md) accounts for same-layer sums and proves decimal normality for this support. For the full series for $`\log 2`$, there is the additional difficulty that every position is an insertion. [Verified valuation of the combined numerator](../NormalityChecker/LocalizedLayers.lean) · [Unresolved estimates for ln 2](transition-discrepancy.md)
