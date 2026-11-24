# Discrepancy certificates for finite prime supports

Let $`b\ge2`$, let $`P`$ be a finite set of primes, and let $`s\ge1`$ be an integer. The support includes 1, including when $`P`$ is empty. Write

```math
X=\sum_{m\ge1,\;q\mid m\Rightarrow q\in P\ (q\;\mathrm{prime})}\frac{1}{m^s b^m}.
```

Here $`D_N`$ is the supremum over all half-open intervals in the unit interval of the absolute difference between their observed frequency among the first $`N`$ radix shifts and their length. Write $`D_\infty=\limsup_N D_N`$.

**Lean proves that $`D_\infty(X)=1`$ if and only if every prime in $`P`$ divides $`b`$.** Each $`p\in P`$ coprime to $`b`$ gives the bound $`D_\infty(X)\le1-1/(p-1)`$. Taking the smallest such prime gives the strongest universal bound of this form. In particular, every support containing 2 gives normality in every odd base. [Classification and corollary](../NormalityChecker/MaximalSupport.lean)

## What one passing cell buys

Fix $`p\in P`$ coprime to the radix and consider $`p^k\le n<p^{k+1}`$. For the shifted rational prefix $`R_n=\sum_{m\le n} b^{n-m}/m^s`$ on the support, the normalized unshifted prefix $`p^{ks}b^{-n}R_n`$ is integral at $`p`$. Its residue at precision $`p^L`$ depends only on a finite partition of $`[1,p)`$ at sufficiently large scales. A nonzero cell residue implies $`p^{ks-L+1}\mid\mathrm{den}(R_n)`$. Refining a zero cell can uncover passing subcells. Every finer zero cell has a zero parent because both residues represent the same rational prefix at a sufficiently late common scale. [Residue calculation](../NormalityChecker/LocalizedCertificate.lean) · [Refinement and survival](../NormalityChecker/DiscrepancyChecker.lean)

At the first precision, $`1\le n/p^k<2`$ admits just the cofactor 1 in the top layer. Its residue is a unit. The lower density of this guaranteed region is $`1/(p-1)`$, attained asymptotically at ends of scales. If every support prime divides the radix, sufficiently many shifts after each insertion clear its denominator entirely. The insertion count and the clearing delays have zero relative cost. The shifted tail tends to zero, so every fixed interval $`[\delta,1-\delta)`$ has limiting frequency zero for $`0<\delta<1/2`$. Its length can be arbitrarily close to one. [Clean-block transfer](../NormalityChecker/WeightedBlocks.lean) · [Interior-frequency theorem](../NormalityChecker/MaximalSupport.lean)

## Partial certificates and unfinished scales

Let $`Z_L`$ be the union of half-open failing cells in $`[1,p)`$. The following is a kernel-checked upper bound, with lengths measured in the normalized coordinate.

```math
D_\infty(X)\le C_L=\max_{1\le t\le p}
\frac{|Z_L|/(p-1)+|Z_L\cap[1,t)|}{t}.
```

At the cutoff $`t p^k`$, previous complete scales contribute at most $`p^k|Z_L|/(p-1)`$ failed observations. The current scale contributes up to $`p^k|Z_L\cap[1,t)|`$. Between consecutive boundaries the ratio is monotone or constant, since its numerator is affine. Lean proves the discrete inequality at **every integer cutoff** on the grid, including cutoffs inside a cell. Since $`C_L\le p|Z_L|/(p-1)`$, arbitrarily small exceptional length suffices for normality. [Exact prefix accounting](../NormalityChecker/CellProfile.lean) · [Checker and shrinking-cell theorem](../NormalityChecker/DiscrepancyChecker.lean)

For the analytic step, divide a prefix of length $`N`$ into blocks of length $`2^{\lfloor\log_4 N\rfloor}`$. Blocks near an insertion, the initial block, and the unfinished block cost $`o(N)`$ for fixed support. On each remaining block the rational prefix follows an exact radix orbit. Every later denominator divides the starting denominator. One passing position therefore gives a large starting denominator. All denominator primes belong to a fixed set coprime to the radix, and the denominator is polynomially bounded in block length. The fixed-support orbit estimate and finite Fourier smoothing control every test interval with a common cutoff. A block with no passing position costs at most one unit per observation. This gives the coefficient **one** in front of the failed fraction. [Uniform interval transfer](../NormalityChecker/SupportDiscrepancy.lean) · [Internal modular estimate](../NormalityChecker/SmoothOrbit.lean)

| Base | Support | Selected prime | $`C_1`$ | $`C_2`$ | $`C_3`$ |
| --- | --- | ---: | ---: | ---: | ---: |
| 7 | 2, 3, 5 | 5 | 5/12 | 1/4 | 0 |

At precision one the only failed interval is $`[2,3)`$. Its full-scale fraction is $`1/4`$, yet a prefix ending at $`t=3`$ has limiting failed fraction $`(1/4+1)/3=5/12`$. Lean evaluates all three values by kernel reduction. This example also has a direct normality proof using the selected prime 2. To reproduce the intermediate calculation, run `python3 scripts/localized_certificate.py 7 5 2 2 3 5`. The CLI takes $`L`$ and Lean takes $`\ell=L-1`$. The Python implementation uses rational insertion boundaries, and CI compares its residues with exact rational prefixes. [Checker](../scripts/localized_certificate.py) · [Tests](../scripts/test_localized_certificate.py)

## How far polynomial-denominator models can reach

**Paper result, with the finite word inequality verified in Lean.** For each fixed $`b\ge2`$ and exponent $`d`$, a sufficiently small fixed mean orbit error already has exponentially small probability at a prescribed block start. This conclusion permits all rational models of denominator at most $`T^d`$. [Finite word inequality](../NormalityChecker/ModelCounting.lean)

For a fixed model $`y`$ and Lebesgue-uniform $`x\in[0,1)`$, $`z=\{b^n x-y\}`$ is uniform. Put $`a=b^2`$, $`J=\lfloor T/2\rfloor`$. The first $`J`$ base-$`a`$ digits of $`z`$ give equiprobable words. At each occurrence of digit 1, the corresponding even shift lies in $`[1/a,2/a)`$, at distance at least $`1/a`$ from an integer. Mean circle distance at most $`\eta`$ allows at most $`K=\lfloor a\eta T\rfloor`$ occurrences. Give the distinguished digit weight 1 and every other digit weight 2. The sum of all word weights is $`(2a-1)^J`$, and each accepted word has weight at least $`2^{J-K}`$ for $`K\le J`$. Its probability is therefore bounded by $`2^K(1-1/(2a))^J`$. Taking $`\eta=1/(16a^2)`$ and $`T\ge2`$ gives at most $`\exp(-J/(4a))`$.

There are at most $`O(T^{2d})`$ rational models modulo one. The existing certificate schedules $`T=B^k`$ with fixed $`B\ge2`$ and at most $`O(L^k)`$ possible starts per scale. These starts add only a polynomial factor in $`T`$. The sum over scales converges, so the first Borel–Cantelli lemma gives almost-sure eventual failure even to find one such block on this schedule. Countably many choices of integer parameters preserve the null set. The case $`B=1`$ cannot meet growing denominator floors. A shifted-prefix error tending to zero changes the block mean by $`o(1)`$. This argument concerns prescribed schedules and Lebesgue measure. It singles out no particular constant.

## Growing support and shifted weights

If $`h`$ is the first missing positive index, the binary logarithmic gap satisfies the following support-independent bound. Its lower endpoint is the first omitted term. Its upper endpoint follows by bounding the remaining weights by $`1/h`$ and summing the geometric tail. For prime supports the first missing index is the least omitted prime by factorization. [Lean theorem](../NormalityChecker/LocalizedLogGap.lean)

```math
\frac{1}{h2^h}\le \log 2-X_{2,P,1}\le\frac{2}{h2^h}.
```

Uniformly small unwrapped error after $`N`$ shifts requires $`2^{N-h}/h\to0`$. All indices below $`h`$ are already present. The clean-block proof pays $`O((1+\log N)^{|P|}/\sqrt N)`$ at fixed order and support, and its orbit cutoff also depends on the off-base primes. The gap estimate controls approximation uniformly in $`P`$. A discrepancy estimate effective on the resulting dense schedule remains open. The four-position middle-third miss objective for $`\ln 2`$ remains open as well. [Four-position objective](transition-discrepancy.md#one-fixed-window-length-suffices)

For a different rational weight, take $`1/(m+1)`$ on the geometric axis $`m=c^i`$. At $`t=2^{j+1}`$ the shifted prefix at $`n=c^t`$ has a prime divisor of its reduced denominator exceeding $`2^{j+2}`$, for every $`c\ge2`$. Indeed $`c^t+1`$ is a square plus one with an odd prime divisor $`p`$. The order of $`c`$ modulo $`p`$ is $`2t`$. Thus $`p`$ divides no earlier $`c^i+1`$, and the newest numerator equals one. This proves an obstruction for the actual prefixes. Normality of the expansion and the usefulness of different models remain open. [Lean proof](../NormalityChecker/ShiftedWeights.lean)

## Periodic weights and literature

For any positive period, a periodic antidifference whose values at the boundaries $`c^j`$ lie in $`\{0,C\}`$, with $`C\ne0`$ attained for unbounded $`j`$, gives normality. The proof telescopes and applies the existing normality theorem for an infinite restriction of a geometric axis. For example, $`c=3,d=4`$ permits alternate powers to contribute. [Periodic theorem](../NormalityChecker/PeriodicWeights.lean)

Bailey and Crandall give normality criteria for lacunary constructions. Vandehey gives quantitative exponential-sum estimates for fixed smooth moduli and applications to normality. The discrepancy certificate uses an internal qualitative estimate and charges failed cells by their prefix lengths. The relation of the full finite-support classification to prior constructions deserves independent review. [Bailey and Crandall](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf) · [Vandehey, Corollary 1.2 and §7](https://arxiv.org/pdf/1606.07911)
