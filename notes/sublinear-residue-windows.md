# Low-transition words on growing windows

For a corrected logarithm model at position $`n`$, let $`M,D,K,L_M`$ be as in the two-stride construction, and let $`L=KL_M`$. The true shifted value is within a known rational error $`\eta`$ of the model, whose numerator at denominator $`L`$ is integral. A simultaneous residue $`r\bmod P`$ for part of this numerator places its fractional part on the grid $`r/L+j/H`$ modulo one, where $`H=L/P`$.

## Adjustable precision and its limitation

Fix $`3\le y\lt M`$. Take $`P`$ to be $`K`$ times the product of the **full** prime powers $`p^v\Vert L_M`$ for $`p\gt y`$. Each large-prime calculation uses only indices divisible by $`p`$, at most $`M/p`$ of them. The separate $`K`$-residue needs only the correction rows. The exact number of remaining lifts is

```math
H=\prod_{p\le y}p^{\lfloor\log_p M\rfloor}.
```

This formula counts possibilities before imposing any further information about the small primes. For $`y=M^\gamma`$, $`0\lt \gamma\lt 1`$ fixed, write $`j=\lfloor1/\gamma\rfloor`$. Then

```math
\log H=(j+o(1))M^\gamma .
```

Indeed the log is $`\sum_{a\ge1}\vartheta(\min(y,M^{1/a}))`$. The first $`j`$ terms equal $`\vartheta(y)`$, including the equality case. The rest total $`O(M^{1/(j+1)}\log M)=o(y)`$. This rate improves on leaving *all* higher prime powers unresolved. [Actual prime-power and scale residues](corrected-strides.md#prime-powers-and-the-extra-factor-of-three)

For a length $`T`$ and word integer $`0\le u\lt 2^T`$, put $`I=[u2^{-T},(u+1)2^{-T}]`$. The exact exclusion test is that the closed interval

```math
\left[\frac{L(u2^{-T}-\eta)-r}{P},\frac{L((u+1)2^{-T}+\eta)-r}{P}\right]
```

contains no integer. Closed enlargement handles either sign of the model error and the cut at zero. There are $`2\sum_{i=0}^a\binom{T-1}i`$ words with at most $`a`$ changes. On **every** sufficiently late start the test can be run with $`T`$ of order $`\sqrt n`$. For $`T=n^\delta`$, $`0\lt \delta\lt 1`$, take both correction orders $`\lceil cT/\log(n/T)\rceil`$ with $`c\gt \log2`$. Indeed $`B(m,r)\le r!/(m+1)^{r+1}`$ and $`\log((m+1)/r)=\log(n/T)+O(\log\log n)`$, for $`m`$ of order $`n`$. Thus $`2^T\eta\to0`$, with $`M=n/2+o(n)`$. A cutoff exponent $`\gamma\lt \delta`$ leaves $`\log H=o(T)`$ while the longest local prime sum has length $`O(M^{1-\gamma})=o(n)`$.

There are two different uniform estimates here. If $`H\ge2^T`$, **every** length-$`T`$ cylinder contains an admissible lift of **each** residue. In the opposite regime, for any list of $`W`$ words, the fraction of the $`P`$ possible residues admitting *some* lift into their enlargements is at most

```math
\min\!\left(1,W\left[H(2^{-T}+2\eta)+1/P\right]\right).
```

Count points on the full $`1/L`$ grid in each enlargement and then reduce their numerators modulo $`P`$. If $`a=\lfloor\rho(T-1)\rfloor`$ with $`0\lt \rho\lt 1/2`$, binary entropy gives $`W\le2\exp((T-1)h(\rho))`$, where $`h(\rho)=-\rho\log\rho-(1-\rho)\log(1-\rho)\lt \log2`$. For the sublinear choices above the bound is exponentially small in $`T`$. It is a counting theorem over hypothetical residues. It places no probabilistic law on the one CRT residue computed from $`\ln2`$.

## Simultaneous observations

Suppose two models refer to the same true phase with respective errors $`\eta_1,\eta_2`$. Their possible phases are $`u+j/h`$ and $`v+k/l`$ modulo one. Let $`g=\gcd(h,l)`$ and $`m=\mathrm{lcm}(h,l)`$. The differences modulo one form the translated $`1/m`$ grid; each difference has exactly $`g`$ pairs above it, since the image of the difference homomorphism has size $`m`$ and its domain has size $`hl`$. If $`2m(\eta_1+\eta_2)\lt 1`$, compatibility with the two error bounds picks at most one difference. For enclosures of the actual same phase at least one pair exists, leaving exactly $`g`$ compatible pairs under the distance test. When the first model starts $`e`$ bits earlier, double its offset $`e`$ times, use the new grid size $`h/\gcd(h,2^e)`$, and multiply its error by $`2^e`$ before applying the rule. Lean verifies that any two compatible lifts differ by the same rational displacement on both grids, and that its denominator divides the gcd. [Kernel grid theorem](../NormalityChecker/ResidueWindows.lean)

For a finite check, use models at 512 and 513, both accurate through 64 additional shifts. Leave the ordinary primes $`\{2,3,5\}`$ unresolved in the first and $`\{2,3,7\}`$ in the second, retaining both extra correction residues. After advancing the first by one bit, the lift counts are 3,888,000 and 3,048,192. Exact rational arithmetic verifies the strict inequality above and gives **31,104** compatible pairs. Conversely if the two models test the same odd prime powers on a common denominator and their exact rational displacement is accounted for, the affine congruences for the second numerator pull back to those already imposed on the first. Repetition of overlapping tests need not give independent information. [Executable comparison](../scripts/corrected_strides.py)

## Exact results for the prescribed logarithm residue

At each start below, the program first chooses the least orders that make each of the two finite error bounds at most $`2^{-T}/(2(T+1))`$. It computes the prime residues, then tests **every** word at the indicated transition budget against **every** lift via the integer-interval criterion.

| Start | Word length | Changes allowed | Prime cutoff | Correction orders | Remaining lift count in bits | Surviving words |
| ---: | ---: | ---: | ---: | --- | ---: | ---: |
| 128 | 40 | 2 | 4 | 7, 7 | 11 | 0 |
| 256 | 48 | 2 | 5 | 8, 7 | 21 | 0 |
| 512 | 64 | 3 | 5 | 9, 8 | 23 | 0 |
| 1,024 | 80 | 3 | 7 | 10, 9 | 33 | 0 |

These are exact exclusions for the actual constant on four finite windows. The fixed-quality, intermittent-shell, mean-gap and truncated-moment implications still require an estimate on arbitrarily late true positions. A sufficient new arithmetic input would be to exclude the low-transition list with fixed $`\rho\gt 0`$ for the computed residue on disjoint windows occupying a fixed lower share of all sufficiently long prefixes. The entropy estimate alone does not establish that input. [Tests](../scripts/test_phase_eleven.py) · [Prefix and shell criteria](intermittent-coverage.md)
