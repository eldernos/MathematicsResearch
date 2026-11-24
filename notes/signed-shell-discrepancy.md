# Exact discrepancy of signed Stoneham expansions

Let $`b\ge2`$ be an integer and $`p`$ a prime coprime to $`b`$. Let $`(c_j)_{j\ge0}`$ be any bounded sequence of integers. Put $`a_0=c_0`$ and $`a_{j+1}=c_{j+1}-pc_j`$. Consider the real number

```math
X=\sum_{j=0}^{\infty}\frac{a_j}{p^j b^{p^j}}.
```

Shell $`j`$ consists of the integer positions $`p^j\le n<p^{j+1}`$. It is a zero shell if $`c_j=0`$. The first $`N`$ observations are the fractional parts of $`b^nX`$ for $`0\le n<N`$. Position zero precedes all shells. Write $`Z(N)`$ for the number of zero-shell positions among these $`N`$ starts and $`D_N`$ for their interval discrepancy, the supremum over $`0\le a<d\le1`$ of the absolute difference between the frequency in $`[a,d)`$ and its length.

**Theorem (Lean).** For every such sequence and every sequence of prefix lengths tending to infinity,

```math
D_N-\frac{Z(N)}{N}\longrightarrow 0.
```

In particular $`D_\infty=\limsup_N Z(N)/N`$. The count uses the zero set of the phase sequence $`c_j`$. The hypotheses allow $`p=2`$ in any odd radix. [Exact discrepancy theorem](../NormalityChecker/SignedShellDiscrepancy.lean#L144) · [Signed expansion and qualitative normality classification](../NormalityChecker/SignedPhases.lean)

## Why the two parts have these frequencies

Let $`R_j`$ be the rational partial sum through insertion $`j`$. For $`p^j\le n<p^{j+1}`$ put $`P_n=b^nR_j`$. The power-boundary identity gives

```math
P_n\equiv\frac{b^{n-p^j}c_j}{p^j}\pmod{1}.
```

The signed error $`b^nX-P_n`$ tends to zero as $`n\to\infty`$. Indeed $`|a_i|\le(p+1)C`$ if $`|c_i|\le C`$, and the omitted exponents $`p^i`$ are distinct integers greater than $`n`$. One may bound their shifted geometric sum by $`1/(b-1)`$ and their coefficients by $`(p+1)C/p^{j+1}`$. On a zero shell $`P_n`$ is an integer. For every $`0<\delta<1/2`$, all sufficiently late zero-shell observations therefore miss $`[\delta,1-\delta)`$. Both a negative remainder and an exact zero are covered. [Shifted remainder and phase within a shell](../NormalityChecker/SignedPhases.lean) · [Central-interval exclusion](../NormalityChecker/SignedShellDiscrepancy.lean#L115)

On a nonzero shell the reduced denominator of $`P_n`$ divides $`p^j`$ and is at least $`p^j/C`$, since $`p`$ is coprime to $`b`$. To see uniformity all the way to an arbitrary cutoff, choose $`k`$ by $`p^{2k}\le N<p^{2k+2}`$ and divide the prefix into blocks of length $`B=p^k`$. Discard the initial block and the last incomplete block, at a cost of at most $`2B`$. Each remaining block starts at a multiple of $`B`$ at least $`B`$. Every later shell boundary is a multiple of $`B`$, so the whole block has the same phase. Within it $`P_{n+i}=b^iP_n`$. On nonzero blocks the initial denominator grows uniformly with $`k`$, and is at most $`p^j\le N\le B^3`$ for $`k\ge2`$. The fixed-prime short-orbit bound with the signed remainder estimate thus gives count error at most $`\eta B`$ on each such block, simultaneously for every interval, for all sufficiently large $`k`$. Summing and letting $`\eta\downarrow0`$ gives nonzero-shell visits to any interval $`I`$ equal to $`(N-Z(N))|I|+o(N)`$ uniformly in $`I`$. [Uniform interval bound for short orbits](../NormalityChecker/SupportDiscrepancy.lean) · [Selected-shell uniformity](../NormalityChecker/SignedShellDiscrepancy.lean#L24)

The zero shells can contribute at most $`Z(N)`$ in absolute count error. For a matching lower bound, take the deficit of the single central interval $`[\delta,1-\delta)`$. Only finitely many zero-shell positions can visit it. Its frequency deficit is $`(1-2\delta)Z(N)/N+o(1)`$ for fixed $`\delta`$. Letting $`\delta\downarrow0`$ gives the theorem even if the signs of the tails change from shell to shell. [Two-sided discrepancy estimate](../NormalityChecker/SignedShellDiscrepancy.lean#L144)

## Periodic phases and cutoffs within shells

Let $`z_j`$ be 1 if $`c_j=0`$ and 0 otherwise. Write $`H_j=Z(p^j)/p^j`$ for the density **before** shell $`j`$, so $`H_0=0`$. Direct counting gives

```math
H_{j+1}=\frac{H_j+(p-1)z_j}{p}.
```

For any cutoff between $`p^j`$ and $`p^{j+1}`$, including the two endpoints,

```math
\frac{Z(N)}{N}=\frac{p^jH_j+(N-p^j)z_j}{N}.
```

Within a zero shell the fraction increases or stays constant. Within a nonzero shell it decreases or stays constant. Thus the upper density over all cutoffs equals the limsup of the boundary densities. Iteration gives $`H_{j+1}=(p-1)\sum_{i=0}^j z_{j-i}/p^{i+1}`$.

If $`c`$ has period $`L\ge1`$, the map over a whole period contracts by $`p^{-L}`$. The limiting boundary density **after** a shell of residue $`r`$ is a geometric series. Read $`r-i`$ modulo $`L`$. Its largest value gives

```math
D_\infty=\frac{p-1}{p(1-p^{-L})}
\max_{0\le r<L}\sum_{i=0}^{L-1}\frac{z_{r-i}}{p^i}.
```

Lean computes the same maximum using the density **before** each shell. Set $`M_r=Z(p^r)`$ and $`A=M_L/(p^L-1)`$. The cycle scores are $`(M_r+A)/p^r`$ for $`0\le r<L`$. They satisfy the displayed boundary recurrence and return to $`A`$ after $`L`$ steps. The actual boundary density differs from this periodic solution by $`-A/p^j`$. The maximum is therefore attained asymptotically. The same formula applies on paper to an eventually periodic zero pattern, since finitely many changed shells affect the density by $`O(1/N)`$. [Kernel theorem and rational score calculation](../NormalityChecker/SignedShellDiscrepancy.lean#L335)

Here $`b=2`$, $`p=3`$, and the listed phase word starts with $`c_0`$. The table gives the full limiting cycle in boundary order before each shell. Lean verifies all three discrepancy equalities. [Three binary examples](../NormalityChecker/SignedShellDiscrepancy.lean#L411)

| Repeating phase word | Boundary densities before successive shells | Binary discrepancy |
| --- | --- | --- |
| 1, 1, 1, 0 | 27/40, 9/40, 3/40, 1/40 | **27/40** |
| 1, 0 | 3/4, 1/4 | **3/4** |
| 1, 0, 0 | 12/13, 4/13, 10/13 | **12/13** |

## Which values occur? (Paper proof)

For a fixed admissible $`b,p`$, all binary zero patterns occur already with $`c_j=1-z_j`$. Let $`\sigma`$ delete the first digit of a one-sided binary word $`s=s_0s_1\ldots`$ and define

```math
V_p(s)=(p-1)\sum_{i=0}^{\infty}\frac{s_i}{p^{i+1}}.
```

**The spectrum consists exactly of $`V_p(s)`$ for the words $`s`$ lexicographically at least as large as every suffix $`\sigma^h s`$, $`h\ge1`$.** For $`p=2`$ a dyadic value is included whenever it has at least one expansion satisfying the suffix condition.

*Necessity.* Write the reverse history after shell $`j`$ as $`h_j=z_jz_{j-1}\ldots z_0 00\ldots`$. Its value is $`H_{j+1}`$. Take the compact set of all subsequential limits of these histories as $`j\to\infty`$. It is closed under deleting the first digit because $`\sigma h_j=h_{j-1}`$ for $`j\ge1`$. It has a lexicographically largest word $`s`$, obtained by choosing the largest possible digit at each successive position. Hence all its suffixes are at most $`s`$. The map $`V_p`$ is continuous and order preserving in the weak sense, including the binary ambiguity. Its value at $`s`$ equals the limsup of the boundary densities.

*Sufficiency.* For each $`m=1,2,\ldots`$, append $`m`$ zero bits followed by the reverse of the first $`m`$ bits of $`s`$ to the chronological zero pattern. After $`k`$ bits of this reversed prefix, $`1\le k\le m`$, the history starts with $`s_{m-k},\ldots,s_{m-1}`$ and then $`m`$ zeros. Its value is at most $`V_p(\sigma^{m-k}s)+p^{-(k+m)}\le V_p(s)+p^{-(k+m)}`$. The histories during the zero padding only decrease in value. At the end of the reversed prefix the first $`m`$ digits agree with $`s`$, and its value is within $`p^{-m}`$ of $`V_p(s)`$. This proves equality. Repeating one such padded block periodically gives a periodic maximum tending to $`V_p(s)`$ as $`m\to\infty`$.

The suffix conditions are closed in the compact binary word space. Thus the spectrum is compact, the periodic values are dense in it, and its smallest positive value is $`(p-1)/p`$, obtained from $`1000\ldots`$. A zero shell forces at least this limiting density whenever zero shells recur infinitely often. The spectrum contains uncountably many points. For example, begin a word with $`110`$ and then concatenate arbitrary blocks $`00`$ and $`10`$. Every proper suffix is smaller. For $`p>2`$ the spectrum lies in the zero-measure Cantor set with radix-$`p`$ digits $`0,p-1`$. For $`p=2`$ the spectrum also has measure zero. A maximal word beginning with exactly $`m`$ ones cannot contain a run of $`m+1`$ ones, whereas almost every binary expansion contains such a run for every $`m`$ (test disjoint blocks). The all-ones word gives 1. Extremal conditions on suffixes also occur in the literature on digit expansions. [Allouche, *A note on univoque self-Sturmian numbers*](https://doi.org/10.1051/ita:2007058)

## Irrationality (Lean) and transcendence (paper corollaries)

**Lean proves that the expansion is irrational exactly when infinitely many phases are nonzero.** If a rational has reduced denominator $`q`$, every shifted fractional part belongs to the grid of multiples of $`1/q`$. Across the nonzero shells the interval $`[1/(2q),1/q)`$ has to receive the uniform share, up to an error $`o(N)`$ relative to the prefix. If $`c_j\ne0`$, the cutoff $`N=2p^j`$ includes at least $`p^j`$ regular positions. This contradicts the grid if these shells recur infinitely often. In the other direction, an eventually zero phase sequence gives a finite rational sum. [Kernel irrationality criterion](../NormalityChecker/SignedShellDiscrepancy.lean#L448)

The following approximation argument proves the same irrationality criterion and the transcendence corollaries for any integers $`b,p\ge2`$, including composite $`p`$ and shared prime factors. The reduced denominator $`q_j`$ of $`R_j`$ divides $`Q_j=p^j b^{p^j}`$. The tail satisfies

```math
|X-R_j|\le \frac{2(p+1)C}{p^{j+1}b^{p^{j+1}}}.
```

Indeed all omitted coefficients are bounded by $`(p+1)C/p^{j+1}`$, and the remaining powers of $`b^{-1}`$ fit inside the geometric tail over all integer exponents starting at $`p^{j+1}`$. Thus $`Q_j|X-R_j|\to0`$. If $`X=u/v`$ with $`v>0`$, any distinct $`R_j`$ has distance at least $`1/(vQ_j)`$ from $`X`$. Hence $`R_j=X`$ eventually, so every sufficiently late $`a_{j+1}`$ vanishes. The recurrence then forces $`c_{j+1}=pc_j`$ eventually, and boundedness forces these phases to be zero.

For irrational $`X`$ the approximants $`R_j`$ contain infinitely many distinct reduced fractions, since $`R_j\to X`$. For any fixed $`1<\mu<p`$, the displayed estimate gives $`0<|X-R_j|<Q_j^{-\mu}\le q_j^{-\mu}`$ eventually, since the positive term $`(p-\mu)p^j\log b`$ dominates $`O(j)`$. When $`p\ge3`$, choose $`2<\mu<p`$. Roth’s theorem forbids these infinitely many approximations to an algebraic irrational. In particular each of the three binary examples is **transcendental**. [Roth, *Rational approximations to algebraic numbers*](https://doi.org/10.1112/S0025579300000644)

Ridout’s theorem also covers $`p=2`$. Every prime factor of $`q_j`$ belongs to the fixed finite set of primes dividing $`pb`$. The restricted-denominator form of Ridout’s theorem allows only finitely many reduced approximants of an algebraic irrational with such denominators and exponent $`\mu>1`$. Choose $`1<\mu<2`$. Thus every bounded-phase example with infinitely many nonzero phases is transcendental for every admissible $`p`$, and every value in the spectrum is realized by a transcendental number. The zero padding in the sufficiency construction ensures infinitely many $`c_j=1`$. Roth’s and Ridout’s theorems are classical external inputs to these paper deductions. [Ridout, *The p-adic generalization of the Thue–Siegel–Roth theorem*](https://doi.org/10.1112/S0025579300001339)

The discrepancy equalities concern the signed sparse series $`X`$ with its stated coefficients. The earlier reduction of dense periodic weights uses rational scaling and translation to transfer normality. Transferring a numerical discrepancy through such a change requires its own argument. [Dense periodic classification](persistent-discrepancy.md#a-finite-classification-for-signed-periodic-weights) · [Background on Stoneham and short-orbit results](reviewers.md)
