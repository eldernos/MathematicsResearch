# Binary normality of the localized logarithm on two and five

Restrict the series for the natural logarithm of two to indices whose only prime factors are two and five, keeping the index one. The resulting number is binary normal. For each binary word of length $`r\ge 1`$, the fraction of its occurrences among the first $`N`$ overlapping starting positions tends to $`2^{-r}`$ as $`N`$ tends to infinity. Lean proves this for the literal series

```math
X=\sum_{j=0}^{\infty}\sum_{a=0}^{\infty}
\frac{1}{2^a5^j\,2^{2^a5^j}}.
```

The declaration `LocalizedFive.series_binary_normal` has no hypotheses. Unique factorization identifies the double sum with the restricted single sum. [Normality theorem](../NormalityChecker/LocalizedNormality.lean) · [Series and reindexing](../NormalityChecker/LocalizedSeries.lean) · [Digit-block definition](../NormalityChecker/Basic.lean)

## Why examine this prime set?

The September 2026 manuscript *Binary normality of a localized logarithm* supplies a direct precedent. Its accompanying Lean development treats the binary prime set $`\{2,3\}`$. Its section on finite-prime extensions gives a paper proof when all selected primes are coprime to the base, and also in base two when the set contains three. The suggested $`\{3,5\}`$ example falls under both cases. For $`\{2,5\}`$, the base shares the factor two and the set omits three. The proof below follows the manuscript's strategy of controlling rational truncations between insertions. The calculation modulo 25 resolves a further cancellation. Priority for this particular example remains a question for literature review. [Prior manuscript, §5 “Finite-prime extensions”](https://github.com/CaptainSude/xi-normality/blob/06961817c7f61181ed9a5c73badb8d908d6ccdcc/paper/localized-logarithm-normality.pdf) · [Scope of the accompanying formalization](https://github.com/CaptainSude/xi-normality/tree/06961817c7f61181ed9a5c73badb8d908d6ccdcc) · [Dibag on the localized logarithm](https://doi.org/10.1016/0021-8693(89)90180-4)

## Exactly one factor of five can cancel

Let $`P_n`$ be the sum of $`2^{n-m}/m`$ over the allowed indices $`m\le n`$, and let $`q_n`$ be its reduced denominator. If $`5^k\le n\lt 5^{k+1}`$ and $`k\ge2`$, the exponent of five in $`q_n`$ is $`k-1`$ for $`2\cdot5^k\le n\lt4\cdot5^k`$ and $`k`$ everywhere else. The next potentially available factor of five always survives. [Exact denominator theorem](../NormalityChecker/LocalizedFive.lean)

To see the cancellation, put $`u=\lfloor n/5^{k-1}\rfloor`$. Reduce $`5^k2^{-n}P_n`$ modulo 25. This is well-defined because its remaining denominators are powers of two. Terms with $`j\le k-2`$ vanish. For either remaining layer, $`2^{-5^j}\equiv18\pmod{25}`$ because $`2^{-1}\equiv13`$, $`13^5\equiv18`$ and $`18^5\equiv18`$. Thus a cofactor $`2^a`$ contributes $`13^a18^{2^a}`$ on the top layer and five times that on the preceding layer. The top layer includes $`5\cdot2^a\le u`$, and the preceding layer includes $`2^a\le u`$. These are all the possibilities.

| Integer cell $`u`$ | 5–7 | 8–9 | 10–15 | 16–19 | 20–24 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Normalized residue modulo 25 | 13 | 23 | 10 | 15 | 9 |

The residues 10 and 15 have exactly one factor of five. All five cells have nonzero residue modulo 25. This is a finite calculation covering every scale $`k\ge2`$.

## From denominator survival to frequencies

Fix a nonzero integer Fourier frequency $`h`$. Put $`K=5^s`$. Partition each interval of length $`K^6`$ in the scale range $`[K^6,15625K^6)`$ into blocks of length $`K^5`$. The following bounds hold uniformly in the final cutoff of the interval. [Block estimates and assembly](../NormalityChecker/LocalizedNormality.lean)

1. **Exceptional blocks.** Mark the block containing each allowed index and the following block. There are at most $`2(18(s+1)+1)^2`$ marked blocks, since each possible exponent $`a,j`$ is at most $`18(s+1)`$. On an unmarked block starting at $`n`$, all earlier terms have shifted far enough to clear their powers of two, and no new term enters. Thus $`P_{n+i}=2^iP_n`$ throughout the block. The reduced denominator $`q`$ of $`hP_n`$ is a power of five, with $`n/(25|h|)\lt q\le n`$.
2. **Cancellation on each unmarked block.** The period of two modulo $`q`$ is at least $`q/15`$. Write $`hP_n=A/q`$ in lowest terms. For any initial segment of length $`T\le K^5`$, sum the additive characters of $`A2^i/q`$. For sufficiently large $`s`$ the segment fits in the period. Additive orthogonality gives total squared norm $`Tq`$ when the starting numerator ranges over all residues. Among the $`H=K^4`$ distinct shifts of $`A`$, at least one sum has norm at most $`q/\sqrt H`$, since $`T\le q`$. Translating its start back changes at most $`2H`$ terms. The original sum therefore has norm at most $`15627K^4`$. [Orthogonality and explicit bound](../NormalityChecker/StonehamOrbit.lean) · [Period bound](../NormalityChecker/StonehamOrder.lean)
3. **Every prefix.** There are at most $`K`$ full blocks and one final partial block. Bounding marked blocks and the partial block by their lengths gives a total Fourier sum of order $`(s+1)^2K^5`$. Division by $`K^6`$ gives a bound tending to zero. The omitted series tail satisfies $`0\le2^nX-P_n\le1/(n+1)`$. The project's scale-summation lemma and Weyl criterion now give normality for every prefix endpoint. [Tail bound](../NormalityChecker/LocalizedSeries.lean) · [Scale summation](../NormalityChecker/ScaleTransfer.lean) · [Fourier criterion](../NormalityChecker/FourierTest.lean)

## Where this argument stops

The proof uses both the bounded loss of powers of five and the low number of insertion blocks. For the full logarithm every positive integer is an insertion. Marking insertion blocks would mark the entire scale. A concrete next step toward enlarging the prime set is to test whether additional cofactors permit cancellation on both top layers at once. If several odd primes survive, the analytic estimate must also handle their product in the reduced denominator. Vandehey gives incomplete-orbit estimates supported on a fixed finite set of primes, with constants depending on that set. Passing to all primes would require additional uniform control. [Vandehey, *Differencing methods for Korobov-type exponential sums*](https://doi.org/10.1007/s11854-019-0038-2)
