# Taylor numerators, digit changes and logarithms at rational arguments

## Factorial truncations of e

Let $`A_0=1`$, $`A_{n+1}=(n+1)A_n+1`$, and $`Q_n=n!/\gcd(n!,A_n)`$. The truncation of $`e`$ through $`1/n!`$ is $`A_n/n!`$. For every integer modulus $`q\ge1`$, $`A_{q+n}\equiv A_n\bmod q`$: at a multiple of $`q`$ the recurrence resets to 1 and the subsequent multipliers repeat. In particular the exponent of $`p`$ in $`Q_n`$ equals $`v_p(n!)-\min(v_p(n!),v_p(A_n))`$. For any given power $`p^a`$ its cancellation test needs only $`A_{n\bmod p^a}\bmod p^a`$. These identities and the periodicity are precedents in Sondow and Schalm. [Lean recurrence and residue theorem](../NormalityChecker/FactorialNumerators.lean) · [Sondow–Schalm, especially Appendix A](https://arxiv.org/abs/0709.0671)

**Short returns (Lean).** In any full period modulo $`p`$, the number of starts at which both $`A_n`$ and $`A_{n+h}`$ vanish is at most $`h-1`$ for $`h\ge1`$. Iterating from zero gives the polynomial $`F_1=1`$, $`F_{h+1}(X)=(X+h+1)F_h(X)+1`$. Its degree is at most $`h-1`$ at gap $`h`$ and $`F_h(-h)=1`$, so the field root bound applies. The statement includes pairs crossing the period boundary. Sondow and Schalm already use the related integer gap polynomials to bound gcds of nearby Taylor numerators. [Kernel pair bound](../NormalityChecker/FactorialNumerators.lean) · [Earlier gap polynomials, §3](https://arxiv.org/abs/0709.0671)

**Denominator survival in moving windows (paper).** For every $`\varepsilon\gt 0`$, the set of $`n`$ with $`\log Q_n\lt (1-\varepsilon)\log n!`$ has upper Banach density zero. In particular the actual denominator retains the full leading logarithmic growth on a density-one set.

For $`T\le p`$ enumerate the zeros modulo $`p`$ in any interval of $`T`$ consecutive indices. Split it into bins of $`H+1`$ integers. After the first zero in each bin, charge every further zero to a pair at distance $`1\le h\le H`$. The starting residues in this interval are distinct, so the short-return theorem gives an upper count $`\lceil T/(H+1)\rceil+H(H-1)/2`$. Taking $`H`$ of order $`T^{1/3}`$ gives $`O(T^{2/3})`$ uniformly. For $`T\ge p`$ splitting into periods gives $`O(Tp^{-1/3})`$.

In a window $`[x,x+T)`$, put $`X=x+T`$. A contributing prime costs at most $`v_p(n!)\log p\le X\log p/(p-1)`$ at each zero. Using the two bounds on the appropriate sides of $`p=T`$ gives

```math
\sum_{x\le n\lt x+T}\log\gcd(n!,A_n)
\ll X\left(T+T^{2/3}\log(2X)\right).
```

Here $`\sum_p(\log p)/((p-1)p^{1/3})\lt \infty`$, and partial summation of the Chebyshev upper bound gives $`\sum_{p\le X}(\log p)/(p-1)=O(\log(2X))`$. If $`x\ge T`$, divide by the price $`\varepsilon\log(x!)`$ per exceptional observation and by $`T`$. The fraction is $`O_\varepsilon(1/\log(2x)+T^{-1/3})`$ at large $`x`$. For $`x=0`$, the sharper initial-interval sum is $`O(T^2)`$ since no prime exceeds $`T`$. Discard $`n\lt \delta T`$ and apply the same price estimate to obtain ordinary density zero, then let $`\delta\downarrow0`$. Every window with $`x\lt T`$ embeds in $`[0,2T)`$, completing uniformity. This calculation concerns factorial denominators. A binary shift clears only powers of two and retains an increasing set of odd primes.

The exact scaled remainder is

```math
n!e-A_n=\int_0^1 t^n e^{1-t}\,dt.
```

Expanding $`e^{1-t}`$ with nonnegative terms gives $`n!/(n+j+1)!`$ after integration of the $`j`$th term. Thus polynomial Taylor corrections to this kernel simply extend the original truncation. A different integral uses $`P(t)=t^m(1-t)^m`$, for which integration by parts gives

```math
\int_0^1e^{1-t}P(t)\,dt
=e\sum_{\ell=0}^{2m}P^{(\ell)}(0)-\sum_{\ell=0}^{2m}P^{(\ell)}(1).
```

Divide both coefficients by $`m!`$ to get integers. The resulting rational is the classical diagonal Padé approximant to $`e`$ at 1, giving $`3,19/7,193/71`$ for $`m=1,2,3`$. Its linear-form error is at most $`e\,m!/(2m+1)!`$. The absolute coefficient of $`e`$ is at most $`e^{1/2}(2m)!/m!`$: read the terms backwards and use $`\binom m j(2m-j)!/(2m)!\le2^{-j}/j!`$. It is nonzero by the alternating bound, since successive reversed absolute terms decrease by at least a factor two. The product of error and denominator is therefore below $`e^{3/2}/(2m+1)`$, so Legendre's criterion gives a continued-fraction convergent for $`m\ge4`$. In contrast, Berndt, Kim and Zaharescu prove that the only coincidences of *ordinary Taylor partial sums* with convergents are $`2`$ and $`8/3`$. This distinction matters when comparing rational models from the known continued fraction $`[2;1,2,1,1,4,1,1,6,\ldots]`$. [Berndt–Kim–Zaharescu](https://doi.org/10.1016/j.aim.2013.08.010)

## Quadratic irrationals

Kaneko gives at least $`(1-\varepsilon)\sqrt{N/2}`$ binary changes through position $`N`$ for $`1/\sqrt5`$, for every $`\varepsilon\gt 0`$ and sufficiently large $`N`$. The counts of 01 and 10 differ by at most one. Using the repository's sharp finite transition inequality therefore gives, for each $`c\lt 1/\sqrt2`$,

```math
D_N^{(2)}(1/\sqrt5)\le1-c/\sqrt N
```

eventually. The term $`1/N`$ and the difference of endpoint indexing conventions are absorbed in the strict choice of $`c`$. This is a pointwise finite-prefix gap tending to zero. [Kaneko, Theorem 2.1 and example on pp. 148–149](https://www.math.tsukuba.ac.jp/~kanekoha/b-aryexpansion%28revised%29.pdf) · [Finite transition-discrepancy theorem](../NormalityChecker/SharpDiscrepancy.lean)

The identity $`2\varphi=1+5/\sqrt5`$ does not transfer a lower transition count in this direction by the available multiplier inequality. For example take $`z=1/5+\sum_{j\ge2}2^{-j!}`$. Outside a density-zero set the shifted lacunary part tends to an integer in circle distance (omit a slowly growing neighborhood before each insertion). Thus $`z`$ has limiting transition frequency $`1/2`$, that of the cycle $`1/5,2/5,4/5,3/5`$, while $`5z`$ has transition frequency tending to zero. Both numbers are irrational. This illustrates the need for statistics specific to $`\varphi`$.

There is an unconditional count with a growing least Zeckendorf index cutoff. If $`n`$ is a transition of $`\varphi`$, then $`\|2^{n-j}\varphi\|\ge2^{-j}/4`$ for $`0\le j\le n`$. The verified upper bound $`\|M\varphi\|\le\varphi^{1-k(M)}`$ implies $`k(2^{n-j})\le 1+(j+2)\log_\varphi2`$. The quadratic norm lower bound $`|\varphi-A/2^m|\gg 2^{-2m}`$ implies a transition in every sufficiently late $`[m,2m+C]`$: an unbroken run would approximate an endpoint of the binary cylinder too well. Select disjoint such windows with starting positions increasing by a factor four from $`2L+C`$ to $`N/4`$. Their transitions have disjoint preceding $`L`$ positions. For $`1\le L\le N/16`$ and sufficiently large $`N/L`$, this yields

```math
\#\{n\lt N:k(2^n)\le 1+(L+2)\log_\varphi2\}\gg L\log(N/L).
```

The fixed-cutoff lower bound from Bugeaud–Evertse remains stronger for some small $`L`$. Positive lower density at a fixed cutoff remains open. [Verified Zeckendorf estimate](../NormalityChecker/GoldenOrbit.lean) · [Fixed cutoff and growing Fibonacci tests](intermittent-coverage.md#growing-fibonacci-moduli-for-the-golden-ratio)

## Hexadecimal and decimal shifts of π

A near-maximal discrepancy prefix must concentrate near a **fixed point** of the radix map. For example a hexadecimal fixed point $`j/15`$ can have a nonzero first-frequency deficit even when discrepancy is maximal. For an elementary quantitative test, fix $`a=1/[2(b+1)]`$ and count

```math
G_N=\#\{n\lt N:\|(b-1)b^n x\|\ge a\}.
```

For any arc of length $`\delta\lt a/b`$ containing consecutive orbit points $`u,bu\bmod1`$, one has $`\|(b-1)u\|\le\delta`$. Every other point $`v`$ of the arc satisfies $`\|(b-1)v\|\le b\delta\lt a`$. Hence such an arc contains no counted observation. An arc containing no consecutive observations has at most $`\lceil N/2\rceil`$ visits. Longer intervals whose complements are also longer than $`\delta`$ have discrepancy at most $`1-\delta`$. Using arcs and their complements, for sufficiently large $`N`$ this gives $`D_N^{(b)}(x)\le\max(1-\delta,1-G_N/N)`$.

For $`x=\pi`$, Zeilberger and Zudilin give $`\mu(\pi)\lt 8`$. The same upper bound holds for $`(b-1)\pi`$. If $`L`$ consecutive shifts beginning at $`m`$ have nearest-integer errors below $`a`$, the nearest integers $`u_j`$ must satisfy $`u_{j+1}=bu_j`$ since $`(b+1)a\lt 1`$. Therefore $`|(b-1)\pi-u_m/b^m|\lt a b^{-(m+L-1)}`$. The published irrationality measure bounds $`m+L\le 8m+O(1)`$ for sufficiently late $`m`$. Geometrically disjoint test windows give $`G_N\gg_b\log N`$ on every sufficiently long prefix. In particular **both hexadecimal and decimal discrepancy of π are at most $`1-c_b\log N/N`$** eventually, for some $`c_b\gt 0`$. This paper deduction does not furnish a fixed strict asymptotic bound. [Irrationality measure of π](https://arxiv.org/abs/1912.06345) · [Verified BBP identity and shifted models](../NormalityChecker/BBPShadow.lean)

In base 16 one can test the *fifteenth* cosine frequency of the corrected BBP model to detect escape from these fixed points. A lower limiting mean of $`1-\cos(2\pi\,15 u)`$ of at least $`\varepsilon\gt 0`$ implies a positive $`G_N/N`$ for a sufficiently small fixed $`a`$: bound the integrand by $`2\pi^2a^2`$ below the cutoff and by 2 elsewhere. Finite mean circle approximation errors transfer at cost at most $`30\pi`$ times their mean. This specifies a sufficient arithmetic estimate on the actual BBP numerators; the preceding argument supplies only logarithmically many visits.

For the decimal expansion, a run of copies of one digit gives a rational approximation with denominator dividing $`9\cdot10^m`$ when the run follows digit $`m`$. The same measure bound implies at least $`c\log N`$ decimal digit changes through $`N`$. At least one of the 90 ordered unequal pairs consequently recurs infinitely often. More generally at least $`h+1`$ length-$`h`$ words recur infinitely often: after discarding occurrences of the finitely occurring words, a tail with at most $`h`$ such factors would be eventually periodic by the Morse–Hedlund argument. Indeed the number of factors must increase with length at each step up to $`h`$, unless all shorter factors have a unique continuation. These arguments do not identify a specified decimal digit, such as 0, occurring infinitely often in π.

## Dyadic logarithms and arctangents

For every fixed $`k\ge1`$, the natural logarithm $`L_k=\ln(2^k/(2^k-1))`$ is transcendental by Lindemann's theorem. At position $`N`$, put $`m=\lfloor N/k\rfloor`$ and use the prefix $`\sum_{j\le m}2^{N-kj}/j`$. Its **reduced** denominator has logarithm $`N/k+o(N)`$. Lean proves this along all integer positions. The order-one polylogarithm at radix $`2^k`$ loses $`O_k(m^{2/3})`$ in log denominator compared with $`L_m=\mathrm{lcm}(1,\ldots,m)`$, by the existing valuation bound. The leftover multiplier $`2^{N\bmod k}`$ changes log denominator by at most $`k\log2`$. The sequence has unbounded denominator prime support and positive exponential rate for every fixed $`k`$. In particular arbitrarily small rates across this family give no fixed-$`k`$ positive lower escape estimate. [Lean rate and truncation identity](../NormalityChecker/DyadicLogRates.lean) · [Polylogarithm valuation bound](../NormalityChecker/PolylogGrowth.lean) · [Rivoal's restricted-denominator approach](https://doi.org/10.4171/RMI/519)

More generally the Phase 10 band formula works for any finite dyadic logarithm combination summing to $`\ln R\ne0`$, for positive rational $`R`$. Its rate is the sum of $`1/v-1/(v+1)`$ over its nonzero partial sums $`P_v`$. This includes signed series such as $`\ln(1+2^{-k})`$; their alternating partial sums indexed by series term are positive, and the binary-position exponent again gives rate $`1/k`$. Existence of a dyadic logarithm identity representing a given $`R`$ is an independent arithmetic condition. [General band formula](strided-logarithm.md#the-residue-of-the-actual-numerator)

For $`\arctan(1/2)`$ use $`W(j)=0`$ for even $`j`$ and $`W(j)=(-1)^{(j-1)/2}`$ for odd $`j`$. This character satisfies $`W(pj)=W(p)W(j)`$ at every odd prime. The large-prime numerator test acquires only the unit factor $`W(p)`$, with $`P_v=\sum_{j\le v}W(j)/(j2^j)\gt 0`$ for every $`v\ge1`$. The same prime-band proof therefore gives log denominator $`N+o(N)`$, and the unwrapped shifted error is at most $`1/(N+1)`$. More generally $`\arctan(2^{-k})`$ has rate $`1/k`$ by the same stride rescaling. Each value is transcendental because $`e^{2i\arctan y}=(1+iy)/(1-iy)`$ is algebraic for nonzero rational $`y`$, invoking Lindemann. Normality and a strict asymptotic discrepancy bound for these natural constants remain open here.

A pair of Gaussian logarithm series gives a faster arctangent model. For both π and arctan(1/2), its binary shifted denominators have rate 2/3 and an exact common short-numerator test. For the direct logarithm and arctangent prefixes there is also a uniform two-digit prime residue bound in each one-pole window. [Gaussian model and literature](gaussian-arctangent-denominators.md) · [Prime-square estimate](dyadic-prefix-residues.md)
