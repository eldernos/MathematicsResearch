# Binary word frequencies and the odd part of the divisor function

Let $`E=\sum_{m\ge1}(2^m-1)^{-1}=\sum_{m\ge1}\tau(m)2^{-m}`$, where $`\tau`$ counts positive divisors. Write $`e(x)=\exp(2\pi i x)`$. Factor $`\tau(m)=2^{V(m)}U(m)`$ with $`U(m)`$ odd. The term indexed by $`m`$ then places the integer $`U(m)`$ at binary position $`t(m)=m-V(m)`$. Several terms can reach the same position. Define their total $`C(t)=\sum_{t(m)=t}U(m)`$ and call each $`U(m)`$ a mark. A shift $`n`$ reads from fractional digit $`n+1`$.

**An unconditional obstruction.** Use the uniform distribution on shifts $`N\le n<2N`$. Pack the first 32 displaced coefficients into the integer

```math
R_{32}(n)=\left(\sum_{d=1}^{32}2^{32-d}C(n+d)\right)\bmod 2^{32}.
```

There is an explicit comparison law $`Q_{32}`$ on these integers. At each of the 32 positions independently, place a Poisson number of marks with mean one and give them the limiting one-source odd-part distribution described below. If the frequency of ones in the binary expansion of $`E`$ tends to $`1/2`$, then

```math
\liminf_{N\to\infty} d_{\rm TV}\bigl(\mathcal L(R_{32}(n)),Q_{32}\bigr)>0.006 .
```

Here $`d_{\rm TV}`$ is the supremum of the absolute probability difference over events. Thus even **simple normality requires a detectable departure from this independence model in a fixed finite statistic**. The proof uses a certified enclosure $`[0.492230,0.492685]`$ for the one-frequency of the comparison law continued to infinitely many positions. This is a conditional candidate for the digits of $`E`$. The actual limiting one-frequency and the existence of all limiting word frequencies remain open. [Exact model computation](../../scripts/erdos_borwein_poisson.py) · [Finite Lean transfers](../../NormalityChecker/ErdosBorweinArrivals.lean)

At each fixed remaining denominator $`2^d`$ the mean number of actual terms tends to **one**, and their marks have an explicit limiting distribution. The signed sum of individual phase changes has a limit at every harmonic, with a Gaussian profile in the original offsets. On dyadic windows a pointwise local limit separates each odd residue class at an exact valuation, including its first correction. A separate estimate reduces the full Fourier product to any band of width $`A(N)\sqrt{\log\log N}`$ about $`\log\log N`$, for arbitrarily slowly diverging $`A(N)`$, on all fixed-power windows. The correlations between arrivals govern the full product.

## Counting each source at its remaining denominator

Let $`I=[N,N+H)\cap\mathbb Z`$, and write $`\mathbb E_I`$ for the uniform average. The contribution at raw offset $`j=m-n`$ is integral when $`j\le V(m)`$. Otherwise its remaining denominator is $`2^d`$ with $`d=j-V(m)\ge1`$. Absolute convergence and the finite integral part give

```math
e(h2^n E)=e\left(h\sum_{d\ge1}2^{-d}C(n+d)\right)
```

for every integer $`h`$. At fixed $`d`$ there is exactly one possible reading position for source $`m`$, namely $`n=t(m)-d`$. For any complex test $`F`$ one therefore has the exact first-moment identity

```math
\sum_{n\in I}\ \sum_{t(m)=n+d} F(U(m))
=\sum_{t(m)-d\in I} F(U(m)).
```

Taking $`F=1`$ counts sources including multiplicity. For $`1\le d\le N`$, the condition on the right differs from $`m\in I+d`$ only within $`O(\log N)`$ of its two endpoints. Indeed $`0\le V(m)\le\log_2 m`$, and $`t(m)\ge m/2`$ for $`m\ge4`$. In this range all relevant $`m`$ are $`O(N)`$. In particular the mean count on each such level is $`1+O((\log N)/H)`$. The same identity holds with source-dependent weights, including restrictions on $`V(m)`$. [Kernel-checked source phase and finite reindexing](../../NormalityChecker/ErdosBorweinArrivals.lean)

For a random model of **one ordinary integer**, take independent exponents $`B_p`$ with $`\Pr(B_p=a)=(1-1/p)p^{-a}`$ for each prime $`p`$ and $`a\ge0`$. Put $`U_* = \prod_p \mathrm{odd}(B_p+1)`$, where $`\mathrm{odd}`$ removes all factors of two. This product is almost surely finite since only exponents at least two can change it. Write $`\nu`$ for its law and $`\mu=\mathbb E U_*`$. In particular $`\nu(1)\ge\prod_p(1-p^{-2})>0`$. For every $`a\ge0`$, $`\mathrm{odd}(a+1)\le1+2\lfloor a/2\rfloor`$. Consequently

```math
\mu\le\prod_p\left(1+\frac{2}{p^2-1}\right)
=\frac{\zeta(2)^2}{\zeta(4)}=\frac52 .
```

All fixed positive moments are finite by the same Euler product convergence at prime exponent two.

For any fixed $`b\ge0`$, $`|F(u)|\le u^b`$, and $`\epsilon>0`$, the mean marked count, uniformly for $`1\le d\le N`$, equals

```math
\mathbb E F(U_*)+O_{b,\epsilon}\left(\frac{N^{1/2+\epsilon}}H\right).
```

To see this, set $`g(m)=F(U(m))`$ and convolve with the Möbius function to get $`a(q)=\sum_{r\mid q}\mu_{\rm M}(r)g(q/r)`$. If any prime divides $`q`$ exactly once, pairing $`r`$ with $`pr`$ gives $`a(q)=0`$. On the remaining integers $`|a(q)|\le2^{\omega(q)}\tau(q)^b`$, with $`\omega`$ the number of distinct primes. The sum of this bound times $`q^{-1/2-\epsilon}`$ over integers with all prime exponents at least two converges by its Euler product. Counting multiples of each $`q\ll N`$ in $`I+d`$ gives the stated error, including extension of the main sum $`\sum a(q)/q`$ to infinity (take $`0<\epsilon<1/2`$). This sum is $`\mathbb E F(U_*)`$ by the same divisor expansion on the independent prime exponents. Indeed, $`q`$ divides the random prime exponents with probability $`1/q`$, the expansion uses only the almost surely finite squarefull part, and the series of expected absolute values converges. The two endpoint strips cost $`O_{b,\epsilon}(N^\epsilon\log N)`$ before division by $`H`$.

In what follows call $`N^{1/2+\eta}\le H\le N`$ a long window, with $`0<\eta<1/2`$ fixed. For fixed $`D\ge0`$ the mean unwrapped tail on long windows is

```math
\mathbb E_I\sum_{d>D}2^{-d} C(n+d)=(\mu+o(1))2^{-D}.
```

Indeed the estimate for $`F(u)=u`$ is uniform up to $`d=N`$. Beyond this, $`C(t)\ll(t+1)^2`$ follows from $`m\le2t+4`$ and $`\tau(m)\le m`$. This tail control pays for real binary carries, including those produced by many sources at one position.

## Where the signed contribution comes from

Set $`T=\log\log N`$. For fixed $`d\ge1`$ and $`-\infty\le a<b\le\infty`$, restrict the inner marked count to raw offsets $`T+a\sqrt T <m-n\le T+b\sqrt T`$. Its mean on long windows tends to

```math
(\Phi(b)-\Phi(a))\,\mathbb E F(U_*),
```

where $`\Phi`$ is the standard Gaussian distribution function. This holds for every $`F`$ of fixed polynomial growth on odd integers. The conclusion is an integrated local estimate for an **exact** remaining denominator and the true odd part.

Here are details of the decorrelation. After reindexing, $`m-n=V(m)+d`$. For ordinary $`m`$ on $`I+d`$, conditional on any fixed residue class modulo a fixed $`Q`$, $`(\omega(m)-T)/\sqrt T`$ tends to the standard Gaussian. One elementary moment proof takes primes $`p\le y=N^{1/T^2}`$ coprime to $`Q`$. Each fixed joint divisibility test for distinct primes has the independent Bernoulli expectation, of parameters $`1/p`$, with error $`O_Q(1/H)`$ by the Chinese remainder theorem. For each fixed moment order $`r`$ the total centered-moment error is $`O_{Q,r}((1+T)^r y^r/H)=o(1)`$. The independent sum has mean $`T+O(\log T)`$ and variance $`T+O(\log T)`$ by Mertens' theorem. Its centered normalized moments tend to the Gaussian moments. A prime appearing once contributes zero, pairings contribute the Gaussian moment, and repeated blocks of size above two save at least one half-power of the variance. Primes in $`(y,N^{1/4}]`$ add $`O_Q(\log T)`$ factors on average by the same one-prime count. Larger primes contribute $`O(1)`$ by size. The primes of $`Q`$ add at most $`\omega(Q)`$.

The inequality $`|V(m)-\omega(m)|\le\sum_{p^e\mid m,\ e\ge2}1`$ changes the normalized variable by $`o(1)`$ in probability. The unnormalized expectation on a long window is bounded because the reciprocal-power sum converges, and the $`O(\sqrt N\log N)`$ possible prime powers contribute $`O(\sqrt N\log N/H)`$ from counting errors. Conditioning on a fixed class costs a bounded factor. To fix the odd mark, first keep primes $`p\le P`$ and distinguish exponents below a fixed cutoff $`L`$, using residue classes modulo $`\prod_{p\le P} p^L`$. Ignored events have upper probability at most $`\sum_{p>P}p^{-2}+\sum_{p\le P}p^{-L}+o(1)`$ on long windows. Send $`N`$, then $`L`$, then $`P`$ to infinity. This gives the Gaussian factor independently of the mark for bounded tests, and uniform bounded higher moments from the divisor expansion give the extension by truncation. This argument averages over the raw offsets at each fixed denominator. It gives no independence across two source integers.

For example, sum $`e(h\tau(n+j)2^{-j})-1`$ over individual $`j\ge1`$ and average over $`I`$. The limit, also valid with the above Gaussian factor if the sum is restricted to that offset band, is

```math
\kappa(h)=\sum_{d\ge1}\left(\mathbb E e(hU_*/2^d)-1\right).
```

The bound $`|e(x)-1|\le2\pi|x|`$ and the mean tail justify summation. Without the band restriction the rate is $`O_{h,\epsilon}(N^{1/2+\epsilon}/H)`$, by applying the uniform marked estimate to $`2^d(e(hu/2^d)-1)`$, whose modulus is at most $`2\pi|h|u`$. For odd $`h`$ the $`d=1`$ term is exactly $`-2`$ and the real part of the $`d=2`$ term is $`-1`$. For every nonzero integer $`h`$, $`\kappa(2h)=\kappa(h)`$. This is a signed **sum of individual changes**. The full statistic multiplies the phases at each reading position before averaging.

### A pointwise signed local limit on dyadic windows

There is a sharper one-source result on $`I=[N,2N)`$. Fix $`r\ge1`$ and a complex function $`F`$ on odd residue classes modulo $`2^r`$. Put $`p_T(k)=e^{-T}T^k/k!`$ for $`k\ge0`$ and $`p_T(-1)=0`$. Write $`q_T(k)=p_T(k-1)-p_T(k)`$ for its first difference. Let $`M_F(k)`$ be the mean of $`F(U(m))1_{V(m)=k}`$ on $`I`$. There is an explicit constant $`\gamma_F`$ such that the approximation $`L_F(k)=\nu(F)p_T(k)+\gamma_F q_T(k)`$ satisfies, uniformly in integers $`k\ge0`$,

```math
M_F(k)-L_F(k)=O_{r,F}(T^{-3/2}).
```

Here $`\nu(F)=\mathbb E F(U_*)`$. For $`|k-T|\le A\sqrt T`$ with fixed $`A`$, the Poisson mass is of order $`T^{-1/2}`$ and its first difference is $`O_A(T^{-1})`$. In particular the conditional odd residue law tends uniformly to $`\nu\bmod 2^r`$ in the central band, with error $`O_{A,r}(T^{-1/2})`$. The formula allows the signed test $`F(u)=e(hu/2^r)-1`$ at the exact raw offset $`j=k+r`$. Moving the interval from $`I`$ to $`I+j`$ costs $`O_F(j/N)`$. This gives the contribution of an individual offset at a specified dyadic order.

Expand $`F`$ in characters of the finite group of odd residues. For one such character $`\chi`$, let $`v(a)=v_2(a+1)`$, $`u(a)=\mathrm{odd}(a+1)`$, and set $`L_\chi(w,z)=\sum_{a\ge0}\chi(u(a))z^{v(a)}w^a`$. Define

```math
G_\chi(s,z)=\prod_p (1-p^{-s})^z L_\chi(p^{-s},z).
```

The Dirichlet series of $`\chi(U(m))z^{V(m)}`$ is $`\zeta(s)^z G_\chi(s,z)`$ for $`\Re s>1`$. The terms of degree one in $`p^{-s}`$ cancel in $`G_\chi`$ because $`u(1)=1`$ and $`v(1)=1`$. Uniformly for $`|z|\le2`$, both local power series have polynomially bounded coefficients since $`|z|^{v(a)}\le a+1`$ and $`|\binom za|\le a+1`$. The Dirichlet coefficients of $`G_\chi`$ thus have absolutely bounded sum with weight $`m^{-3/4}`$ uniformly on that disk. In particular they satisfy the logarithmically weighted absolute-convergence hypothesis of Selberg's Theorem 2. [Selberg, *Note on a paper by L. G. Sathe*, pp. 84–85](https://people.clas.ufl.edu/alladik/files/selberg-note-on-a-paper-by-sathe-1953.pdf)

Write $`A_\chi(z)=G_\chi(1,z)/\Gamma(z)`$, using the entire reciprocal gamma function. Selberg's uniform estimate at $`2N`$ and $`N`$, followed by subtraction, gives the dyadic mean $`A_\chi(z)\exp(T(z-1))+O(1/\log N)`$ for $`|z|=1`$. The change from $`\log\log(2N)`$ to $`T`$ is $`O(1/\log N)`$. At $`z=1`$ the Euler product gives $`A_\chi(1)=\nu(\chi)`$. Invert on the unit circle and expand the analytic multiplier to first order at one. The constant term gives $`p_T(k)`$ and the linear factor $`z-1`$ gives its first difference. The quadratic remainder is bounded in the inversion integral by a constant times

```math
\int_{-\pi}^{\pi} \theta^2\exp[-T(1-\cos\theta)]\,d\theta
\ll T^{-3/2},
```

independently of $`k`$. Combining characters gives $`\gamma_F`$ as the same linear combination of the $`A'_\chi(1)`$. The dyadic proof uses Selberg's classical one-variable theorem. Subtraction at the endpoints of a short window would amplify its error by $`N/H`$. Mira's prime-conditioned estimates address a different sampling measure.

### A narrower raw-offset band on every power window

Fix $`0<\delta\le1`$, $`N^\delta\le H\le N`$, $`0\le B\le T/4`$, and let $`S_B(n)`$ be the sum of $`\tau(n+j)2^{-j}`$ over positive raw offsets with $`|j-T|\le B`$. For fixed $`h`$ the phase error satisfies

```math
\mathbb E_I |e(h2^n E)-e(h S_B(n))|
 \ll_{\delta,h} e^{-B^2/(3T)}.
```

This removes the $`\sqrt{\log T}`$ width factor in the earlier sufficient band for an $`o(1)`$ error. To prove it, bound the chord by $`2\pi |h|`$ times the sum of $`2^{-d}U(m)`$ on omitted nonintegral terms. At fixed $`d\le N`$ sum over the enlarged source interval $`[N+d,N+H+d+O(\log N)]`$. Shiu's short-interval bound for the nonnegative multiplicative functions $`U(m)\exp(\pm r V(m))`$, $`r=B/T`$, gives means $`\ll_\delta\exp((e^{\pm r}-1)T)`$ there. Indeed their prime values are $`e^{\pm r}`$ and their common growth bounds follow from $`Ue^{rV}\le\tau^2`$ for $`r\le1/4`$. Use a length exponent strictly below $`\delta`$ on the translated intervals. Uniform dependence on these fixed majorants, including the reduction to an unrestricted interval, is detailed in the earlier note. [Shiu's theorem](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0313?tify=%7B%22pages%22%3A%5B167%5D%7D) · [Uniform constants and unrestricted form](../phase13/erdos-borwein.md#an-unconditional-localization-of-the-divisor-fourier-statistic)

The early event $`V(m)+d<T-B`$ costs a factor $`e^{r(T-B-d)}`$ against the negative exponential moment. The late event costs $`e^{-r(T+B-d)}`$ against the positive moment. Summing $`2^{-d}e^{\pm rd}`$ costs an absolute constant. Both exponents are at most $`-rB+e^{1/4}r^2T/2\le-B^2/(3T)`$. The remaining $`d>N`$ have exponentially small total weight. Thus $`B=A(N)\sqrt T`$ with any $`A(N)\to\infty`$ suffices, enlarging the retained set if necessary via the same absolute omitted-mass bound. On long windows the preceding Gaussian calculation also gives, for fixed $`A`$, a limiting upper bound $`4\pi |h|\mu\Phi(-A)`$ on the error for $`B=A\sqrt T`$.

## A test for independence and a conditional word law

The external hypothesis considered here is convergence in law, for each fixed $`D`$, of $`(C(n+1),\ldots,C(n+D))`$ on dyadic windows to independent copies of $`J=\sum_{i=1}^K U_i`$, where $`K`$ is Poisson of mean one and the $`U_i`$ are independent with law $`\nu`$, independent of $`K`$. This hypothesis concerns integer column totals. It already suffices to assume convergence of their packed residues for each $`D`$. Neither form follows from the one-source results.

Under this hypothesis the limiting circle measure of $`2^nE`$ is the law of $`X=\{\sum_{d\ge1}2^{-d}J_d\}`$ for independent copies $`J_d`$. Indeed its finite heads converge by hypothesis, and the discarded mean mass for both sums is $`(\mu+o(1))2^{-D}`$ on taking $`N\to\infty`$ first. Halving a prefix into dyadic windows gives the same limit on prefixes, with endpoint errors $`O(\log N/N)`$. The Fourier coefficient at $`h`$ is $`\exp(\kappa(h))`$ by the generating function of a Poisson variable. Absolute convergence gives a **nonzero** coefficient at every $`h`$. In particular $`|\exp(\kappa(1))|>e^{-7}`$. The first three negative real contributions total at most $`2+1+2`$ in absolute value, and the rest cost at most $`2\pi\mu/8\le5\pi/8`$.

For a word of length $`k`$ and value $`v`$, let $`Q_D`$ be the law of the packed residue of the first $`D`$ independent columns, $`D\ge k`$. The conditional frequency is the limit of $`Q_D([v2^{D-k},(v+1)2^{D-k}))`$. With $`p_0=(1+e^{-2})/2`$, the error at finite $`D`$ is at most

```math
2(\mu+1)p_0^D\le 7(3/5)^D.
```

In fact $`J`$ has the parity of $`K`$, so the larger parity probability is $`p_0`$. Every packed residue has mass at most $`p_0^D`$. Reveal the columns from the least significant end. To reach a specified residue, each successive column must have a prescribed parity after the previously revealed carry. Its conditional chance is at most $`p_0`$. The independent remaining tail in units of $`2^{-D}`$ is a nonnegative variable $`Y`$ of mean $`\mu`$. Conditional on $`Y`$, at most $`2\lceil Y\rceil`$ grid cells can cross the two word endpoints. This proves the error bound. Conditioning on the same tail, any specified point on the circle has probability at most $`p_0^D`$ for every $`D`$, proving absence of atoms and justifying the word limits.

**Certified one-bit enclosure.** The model script uses $`D=24`$ and integer lower bounds on all probability masses on a grid of step $`2^{-80}`$. It retains primes through 65536, odd products through 255, and column totals through 383. For each retained prime it convolves the geometric exponent probabilities multiplicatively. All larger primes leave the product unchanged with probability at least $`1-1/65536`$ by the sum of inverse squares. Writing $`b_j=\Pr(J=j)`$, differentiation of $`\exp(\sum_{u\ge1}\nu(u)z^u-1)`$ gives

```math
b_0=e^{-1},\qquad jb_j=\sum_{u=1}^j u\nu(u)b_{j-u}.
```

An odd-order alternating partial sum bounds $`b_0`$ below. Every remaining recurrence coefficient is nonnegative. Start the finite head with carry zero, pass a carry $`c`$ to $`\lfloor(c+j)/2\rfloor`$ at each deeper column, and at the first column count the parity of $`c+j`$. Only lower masses for even and odd are used. The missing total covers all truncations and rounding, and the cylinder error above covers the infinite tail. The resulting outward-rounded range in millionths is **492230 to 492685**. This interval concerns the specified Poisson hypothesis. [Reproducible integer calculation](../../scripts/erdos_borwein_poisson.py)

**Proof of the unconditional obstruction.** Write $`f_I`$ for the actual proportion of ones and $`p_*`$ for the infinite model's one-frequency. For fixed $`D\ge1`$ and integer $`1\le s\le 2^{D-1}`$ let $`\Delta_D=d_{\rm TV}(\mathcal L(R_D(n)),Q_D)`$. The unwrapped discarded actual tail, in units of $`2^{-D}`$, has mean $`\mu+o(1)`$ on long windows. Outside an event of probability at most $`(\mu+o(1))/s`$ its integer carry is below $`s`$. A zero can become a one only from the last $`s`$ grid cells of the lower half, and a one can become a zero only from the last $`s`$ cells of the upper half. Bound the chance of each enlarged half by its model probability plus $`\Delta_D`$, then use the model's maximum atom and its cylinder error. Set $`\epsilon_{D,s}=(s+7)(3/5)^D+\mu/s`$. The resulting unconditional bound is

```math
|f_I-p_*|\le \Delta_D+\epsilon_{D,s}+o(1).
```

For $`D=32`$, $`s=4096`$ the total carry error is less than $`0.001`$ eventually. If prefix one-frequency tends to $`1/2`$, subtraction of consecutive prefix counts gives $`f_{[N,2N)}\to1/2`$. The certified bound on $`p_*`$ now gives the stated strict gap in total variation. [Kernel-checked finite carry criterion](../../NormalityChecker/ErdosBorweinArrivals.lean)

## The missing arithmetic and a finite check

Already the ordered two-source count for destinations separated by a fixed $`b`$ depends on an exact valuation difference. Let $`A_k`$ consist of positive $`m`$ with $`m+k\ge1`$, $`t(m)\in I`$, and $`V(m+k)-V(m)=k-b`$. For mark tests $`F,G`$ the normalized count is

```math
\frac1H\sum_{k\ne0}\sum_{m\in A_k}F(U(m))G(U(m+k)).
```

This follows from $`t(m+k)-t(m)=k-(V(m+k)-V(m))`$. For $`b=0`$ it counts ordered distinct sources at one position. The independent marked Poisson process has factorial moment $`\nu(F)\nu(G)`$ at each such separation. Convergence of unbounded factorial moments would also require tail control. A one-variable Gaussian law, even with the exact mark distribution and the right signed first moment, leaves this two-source diagonal undetermined. The finite-residue obstruction above avoids assuming any factorial-moment convergence.

As an independent finite check, there are **67135, 63695, 63696, 67618** starts of the overlapping words 00, 01, 10, 11 respectively on $`2^{18}\le n<2^{19}`$. Using just the first 12 displaced levels changes the word at 486 of these 262144 starts. The denominator-two level receives 262145 sources, while the sum of its row signs $`(-1)^{C(n+1)}`$ is 14434. The signed *individual* changes on that same level sum to $`-524290`$. The distinction persists even in a calculation that uses no floating point. The script sieves $`\tau`$ through $`M`$ and propagates both integer carry endpoints from the bound $`0\le\sum_{j\ge1}\tau(M+j)2^{-j}\le M+2`$ until they agree at the last required digit. It checks that every later source has displaced position beyond the retained columns. Crandall's §6 reports Mitchell's much larger computation of the first $`2^{43}`$ bits, with 4436987456570 ones. Both are finite observations. [Exact digits and arrival counts](../../scripts/erdos_borwein_arrivals.py) · [Crandall, §§6–7](https://math.colgate.edu/~integers/m23/m23.pdf)

### Primary versions and scope

Checked on 24 November 2026. At Mira Cult's public repository head `357d26a`, the last change to the claim 0002 research folder is `1498319`. The theorem gives a positive lower proportion for each fixed word on every sufficiently late window with $`N^a\le H\le N`$, $`7/12<a\le1`$. Its weighted prime-conditioned local comparison treats bank counts and marked errors at an actual designated incidence. The attached valuation-atom note gives true upper bounds on its specified shells and explicitly distinguishes its conclusion from a full local limit for $`V`$. The two public normality gists still end at the September and October revisions catalogued in Phase 13. [Mira's public tree](https://github.com/Mira-Cult/math/tree/357d26a23fbbee5c900098938744ab732b84d03a/notes/number-theory/normal-numbers) · [Theorem](https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/README.md) · [Valuation estimates](https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/valuation-atom-bound.md) · [Weighted local-limit audit](../phase13/reviews/erdos-local-limit.md)

Captain Sude's September repositories still have heads `bd98789` (conditional Lean disjunctivity), `d51e93e` (unconditional disjunctivity and quantitative prefix count), and `fe33be2` (limiting frequencies and nonnormality for the **different** powers $`m^r`$, $`r\ge2`$). Campbell's arXiv record lists only v1, proving infinitely many occurrences of 11. None of these sources gives the joint displaced-column law used as the comparison here. The analytic estimates and the obstruction in this note are paper deductions. Lean checks the finite phase identity, source reindexing, column mass bound for phase errors, and the one-bit carry criterion. [First Lean release](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906) · [Elementary archive](https://github.com/CaptainSude/erdos-borwein-disjunctivity-elementary/tree/d51e93e91ff43efef6918efdd4258bbd43bad7aa) · [Power theorem](https://github.com/CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality/blob/fe33be210446c6c0b127ca7757fc8f1182c5b541/lean/PowerLambert/Results.lean) · [Campbell's version record](https://arxiv.org/abs/2605.24160)

```sh
lake env lean NormalityChecker/ErdosBorweinArrivals.lean
python3 scripts/erdos_borwein_arrivals.py
python3 scripts/erdos_borwein_poisson.py
```
