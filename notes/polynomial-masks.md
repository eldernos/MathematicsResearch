# Polynomial weights on masked smooth supports

Let *S* be a finite set of primes. A positive integer is *S*-smooth if all its prime factors belong to *S*, so 1 is smooth even when *S* is empty. Fix a base *b* ≥ 2, an integer *s* ≥ 1 and a nonzero polynomial *P* with integer coefficients. Write $P(X)=X^rG(X)$ with *G*(0) ≠ 0. For any set *A* of retained *S*-smooth positive integers, put

```math
x_A=\sum_{m\in A}\frac{P(m)}{m^s b^m}.
```

For an interval *I* = [*a*, *c*) in [0, 1), count the fractional parts of *b*ⁿ*x* for 0 ≤ *n* < *N* that belong to *I*. The interval discrepancy $D_N(x)$ is the supremum over *I* of the absolute difference between its observed frequency and its length. Write $D_\infty(x)=\limsup_N D_N(x)$.

**Theorem (Lean).** On the full smooth support, $D_\infty(x_A)=1$ exactly when *r* ≥ *s* or every prime of *S* divides *b*. In these cases the discrepancy tends to 1. If *r* < *s*, every *p* ∈ *S* with *p* ∤ *b* gives

```math
D_\infty(x_A)\le 1-\frac{1}{p-1}.
```

The same upper bound holds for any mask retaining *p*ᵏ for every sufficiently large *k*. Thus a mask retaining all sufficiently late powers of 2 gives normality in every odd base when *r* < *s*. The maximal-discrepancy implications hold for every mask. The degree of *P* is unrestricted. The signed-tail and discrepancy arguments apply directly to the masked series. [Full classification and maximal limit](../NormalityChecker/MaskGrid.lean) · [Retained powers and odd-base normality](../NormalityChecker/MaskWindows.lean)

**Stronger full-support conclusion (paper).** When *r* < *s* and at least one support prime does not divide *b*, the full-support number is normal in base *b*. This holds for rational coefficients as well. Lean proves that each unsigned discrepancy certificate at order *s* − *r* also bounds the polynomial series. The remaining input, that those certificates become arbitrarily small for every such full support, is proved in the unsigned finite-support note. [Polynomial certificate comparison](../NormalityChecker/MaskDominance.lean) · [Unsigned zero-width proof](unsigned-finite-support.md)

## What survives in the reduced prefix

Suppose *t* = *s* − *r* > 0. Write $R_n$ for the shifted rational prefix, with one summand $b^{n-m}G(m)/m^t$ for each retained *m* ≤ *n*. Fix *p* ∤ *b* and write *v* for the exponent of *p* in |*G*(0)|. Let *p*ᵏ be retained, *k* > *v*, and *p*ᵏ ≤ *n* < 2*p*ᵏ. Then the reduced denominator of $R_n$ contains **exactly** *kt* − *v* factors of *p*.

Indeed *m* divides *G*(*m*) − *G*(0). With $v_p(0)=+\infty$, an index with $j=v_p(m)$ therefore satisfies $v_p(G(m))\ge\min(j,v)$, with equality to *v* whenever *j* > *v*. The top index *m* = *p*ᵏ gives term valuation *v* − *kt*. Every other positive *m* ≤ *n* has *j* < *k*, since the next multiple of *p*ᵏ is 2*p*ᵏ. For *j* ≥ *v* its term valuation is at least *v* − *jt*, strictly above the top value. For *j* < *v* it is at least −(*t* − 1)*j*, again strictly above *v* − *kt* because *v* < *k*. Powers of *b* are units at *p*. The unique smallest valuation persists in the sum, proving the assertion for every subset of the other indices. This accounts for the fixed loss even when *p* divides the leading nonzero coefficient of *P* at zero. [Exact local norm and reduced exponent](../NormalityChecker/PolynomialMasks.lean)

For example, take *b* = 5, *S* = {2, 3, 5}, *s* = 5 and $P(X)=12X^4+X^5+3X^{10}$. The weight is $12/m+1+3m^5$. On every retained dyadic scale with *k* ≥ 3 the exact exponent of 2 is *k* − 2 throughout $[2^k,2^{k+1})$. Keeping every sufficiently late power of 2 is enough for base-five normality, with arbitrary choices at the other smooth indices. [Formal example and exact exponent](../NormalityChecker/MaskExamples.lean)

## Transfer from rational prefixes to the orbit

Write $a_m=P(m)/m^s$ on *A* and zero elsewhere. There are constants *C* and *d* ≥ 0 with $|a_m|\le C(m+1)^d$. Polynomial growth gives absolute convergence. If the next *g* positions after *n* contain no insertion, the shifted real tail satisfies

```math
|b^n x_A-R_n|
\le C K_{b,d}(n+g+2)^d b^{-(g+1)},\qquad
K_{b,d}=\sum_{j\ge0}(j+1)^d b^{-j}.
```

To see this, write the remaining indices as *n* + *g* + 1 + *j* and use $n+g+2+j\le(n+g+2)(j+1)$. For large-degree numerators the unwrapped tail can be large immediately before an insertion. We use the bound on positions with a gap ahead. [Kernel gap estimate](../NormalityChecker/PolynomialMasks.lean) · [Uniform estimate for the signed series](../NormalityChecker/MaskedSeries.lean)

At prefix length *N*, split [0, *N*) into blocks of length $B=\lfloor\sqrt N\rfloor$. Omit the first and last partial or boundary blocks. For each remaining block [*u*, *u* + *B*), omit it if an insertion lies in [*u* − *B*, *u* + 2*B*]. Up to *N* + 2*B* there are at most $(1+\lfloor\log_2(N+2B)\rfloor)^{|S|}$ smooth indices, by recording the exponents of the primes in *S*. Each insertion omits at most four blocks. The total omitted length is $O(B(1+\log N)^{|S|})=o(N)$, uniformly in the mask for fixed *S*. On every remaining block the prefix follows the exact orbit $R_{u+i}=b^iR_u$. At each position of the block we can take *g* = *B* in the tail bound, giving a uniform error tending to zero. Lean uses the dyadic block length $2^k$ for $4^k\le N<4^{k+1}$. [Smooth insertion count](../NormalityChecker/LocalizedClearing.lean) · [Two-sided clean-block transfer](../NormalityChecker/MaskedSeries.lean)

Write *c* for the product of the primes in *S* that do not divide *b*, with empty product 1, and $H=\lceil\log_2(N+2B)\rceil$. For *m* ≤ *u*, each prime exponent in *m* is at most *H*, so $m^t\mid b^{Ht}c^{Ht}$. All retained *m* ≤ *u* have age *u* − *m* ≥ *B* ≥ *Ht* for large *N*. Thus $\mathrm{den}(R_u)\mid c^{Ht}$. This common denominator has fixed prime support coprime to *b* and is at most *B*ᴸ for a fixed *L* and all sufficiently large *N*. Signed integer numerators do not change the common denominator. [Kernel clearing bound](../NormalityChecker/PolynomialMasks.lean)

Let *W* be the union of the integer intervals $[p^k,2p^k)$ over retained powers *p*ᵏ. If a remaining block meets *W* at *n*, the reduced denominator at *n* divides that at its start *u*. Since *n* ≥ *B* and *p*ᵏ > *n*/2, the exact exponent *kt* − *v* forces the starting denominators of all such blocks to grow uniformly with *N*. For a fixed nonzero Fourier frequency *h*, multiplying by *h* removes at most a factor |*h*| from the denominator. The fixed-prime-support orbit bound now gives an average Fourier sum tending uniformly to zero on these blocks for the rational orbit. The real orbit has the same estimate, since the character changes by at most $2\pi|h|$ times the real tail error. Finite Fourier smoothing, first fixing the frequency cutoff and then increasing it, gives interval errors $o(B)$ uniformly over these blocks and all intervals. [Fixed-support estimate](../NormalityChecker/SmoothOrbit.lean) · [Uniform interval smoothing](../NormalityChecker/IntervalFourier.lean)

Charge each other block its full length and each omitted position one unit. The controlled blocks cover at least $|W\cap[0,N)|-o(N)$ indices. With $g_W=\liminf_N |W\cap[0,N)|/N$, this proves

```math
D_\infty(x_A)\le 1-g_W .
```

For *p* = 2 with every sufficiently late power retained, *W* contains a final interval of integers. Vanishing interval discrepancy then gives the limiting frequencies of all radix words. [Masked-series transfer](../NormalityChecker/MaskedDiscrepancy.lean) · [Window-density bound](../NormalityChecker/MaskDensity.lean) · [From discrepancy to digit normality](../NormalityChecker/SupportDiscrepancy.lean)

## Full support and higher-order cancellation

Put *t* = *s* − *r* > 0. Clear rational coefficients with a nonzero integer *D* and write the effective integral numerator as *G*. Fix a prime *p* in the support with *p* ∤ *b* and let *v* be the exponent of *p* in |*G*(0)|. At a shift in the scale from *p*ᵏ up to *p*ᵏ⁺¹, every index in the prefix has at most *k* factors of *p*. Since *m* divides *G*(*m*) − *G*(0), the nonconstant part has reduced denominator exponent at most *k*(*t* − 1). This estimate allows arbitrary signs and polynomial degree.

At precision *L* = ℓ + 1, a passing unsigned cell gives denominator exponent at least *kt* − ℓ for the prefix with numerator 1. Multiplying this prefix by *G*(0) costs *v* factors of *p*. Once *k* > ℓ + *v*, its exponent exceeds the bound for the nonconstant part. The ultrametric inequality preserves the dominant term. Dividing by the coefficient-clearing integer *D* preserves the resulting lower bound on the denominator of the actual series. The same passing cells therefore control the polynomial series, and the unsigned certificate at precision *L* is an upper bound for its discrepancy. A concrete kernel consequence is binary normality for every rational numerator nonzero at zero on the full support {2, 5, 13} with a simple pole, since the unsigned certificate already vanishes at precision two. The unsigned zero-width theorem makes the bounds tend to zero on all full finite supports with an off-base prime. [Kernel comparison and conditional normality](../NormalityChecker/MaskDominance.lean) · [5 and 13 example](../NormalityChecker/MaskExamples.lean) · [Paper proof of the unsigned input](unsigned-finite-support.md)

## Maximal discrepancy

If *r* ≥ *s*, every $P(m)/m^s$ is an integer, so every shifted prefix is an integer. If *r* < *s* and every support prime divides *b*, the clearing estimate with *c* = 1 makes the prefix integral on every remaining block. In both cases the real orbit is within a distance tending to zero of an integer except on $o(N)$ positions. For any fixed $0<\delta<1/2$, the interval $[\delta,1-\delta)$ thus has frequency tending to zero. Its length tends to one as *δ* decreases. This proves $D_N(x_A)\to1$ for every mask in these cases, including finite and empty masks. For the full support an off-base prime with *r* < *s* gives a strictly smaller upper bound as above. For a general mask, even an off-base support prime can have all of its powers and multiples deleted. [Concentration on a grid and the full classification](../NormalityChecker/MaskGrid.lean)

## Periodic and bounded-gap masks

Let $k_1<k_2<\dots$ be exactly the exponents of the retained powers of *p*. If there are infinitely many, the lower density of *W* is

```math
g_W=\liminf_{i\to\infty}\sum_{j<i}p^{k_j-k_i}.
```

At the cutoff $N=p^{k_i}$ the number of earlier covered indices is exactly $\sum_{j<i}p^{k_j}$. The covered fraction increases inside a covered interval and decreases across the following gap, so its lower limit occurs along these left endpoints. Finitely many retained powers give density zero. At any integer cutoff *N*, each selected exponent *k* contributes $\max(0,\min(N,2p^k)-p^k)$ indices. The disjoint-window count is kernel-checked for every finite selection and cutoff. [Finite window count](../NormalityChecker/PolynomialMasks.lean) · [Exact endpoint lower density](../NormalityChecker/MaskDensity.lean)

- If every sufficiently late exponent is retained, the geometric sum gives $g_W=1/(p-1)$. [Single-class density](../NormalityChecker/MaskDensity.lean)
- If consecutive retained exponents eventually differ by at most an integer *h* ≥ 1, then $g_W\ge\sum_{j\ge1}p^{-jh}=1/(p^h-1)$. Equality for the window density occurs for one retained exponent class modulo *h*. This yields $D_\infty\le1-1/(p^h-1)$, without requiring periodicity. [Bounded-gap theorem](../NormalityChecker/MaskWindows.lean)
- Suppose the retained exponents are eventually periodic with period *h*, and let *E* be their nonempty set of residues. For *a* ∈ *E*, let $J_a$ be the integers $1\le j\le h$ with $a-j\bmod h\in E$. Grouping previous windows by periods gives the exact density
  ```math
  g_W=\min_{a\in E}\frac{\sum_{j\in J_a}p^{h-j}}{p^h-1}.
  ```
  For example, retaining exponents 0 and 1 modulo 3 for *p* = 3 gives $g_W=\min(4,10)/26=2/13$, hence $D_\infty\le11/13$. These are exact densities of the certified windows. Further positions may also be uniformly distributed. Lean computes the equivalent maximum missed fraction over the integer cells of one period and proves equality for the actual missed-window fraction after finite changes. [Periodic mask theorem and exact 11/13 computation](../NormalityChecker/MaskPeriods.lean)
- For a mask periodic in the **index** *m* modulo *d*, iterate $u\mapsto pu\bmod d$ starting at 1 modulo *d*. Its finite eventual cycle determines *h* and *E*, including when *p* divides *d*. A cycle with no retained residue gives no windows by this test. Bounded gaps in integer indices alone do not imply bounded gaps in retained power exponents. For example, retaining multiples of 3 deletes every power of 2. [Eventual period of the modular power orbit](../NormalityChecker/MaskPeriods.lean)
- Unbounded gaps between successive retained exponents give $g_W=0$, since at the end of such a gap the previous covered length is at most $2p^{k_{i-1}}$. Additional structure can give a stronger result. On a support consisting only of retained powers of *p*, the largest retained exponent before the cutoff tends to infinity, however long the gaps. The same valuation comparison proves denominator growth at every sufficiently late position. The block proof then gives normality whenever *r* < *s* and infinitely many exponents are retained. Lean proves this for polynomial numerators of arbitrary degree, with rational coefficients. A finite mask is nonnormal, so infinitely many retained powers are necessary and sufficient on the axis. [Unbounded-gap density](../NormalityChecker/MaskDensity.lean) · [Unrestricted infinite-axis theorem](../NormalityChecker/MaskAxis.lean)

## Rational coefficients

For $P\in\mathbb Q[X]$ choose *L* ≥ 1 such that $LP=X^rG$ with $G\in\mathbb Z[X]$ and *G*(0) ≠ 0. For *r* < *s* the valuation of the actual shifted prefix on a retained first cell is $v_p(G(0))-kt-v_p(L)$ for *k* > $v_p(G(0))$. Split $L=L_b L_0$, with $L_b$ supported on primes dividing *b* and $L_0$ coprime to *b*. Allow the additional fixed clearing delay $\lambda$ with $L_b\mid b^\lambda$. On clean blocks the common denominator divides $L_0c^{Ht}$, so its prime support is still fixed and coprime to *b*. The same proof gives all the upper bounds and the odd-base normality result **for the rationally weighted number itself**. This direct argument matters because multiplying a real by an integer need not preserve the value of its discrepancy. [Exact rational exponent](../NormalityChecker/MaskAxis.lean) · [Direct rational discrepancy bound](../NormalityChecker/MaskClassification.lean) · [Cancellation at zero](../NormalityChecker/MaskRational.lean)

In the maximal cases for the cleared polynomial, clean shifts of the rationally weighted value approach the grid with spacing $1/L_0$, after the same extra clearing delay. Every interval strictly inside one grid gap has frequency tending to zero. Hence $\liminf_N D_N\ge1/L_0$, implying nonnormality. When $L_0=1$ the discrepancy tends to one. In general equality to one can fail, even on a nonempty full smooth support. [Grid lower bound and nonnormality](../NormalityChecker/MaskRational.lean)

For example, take *b* = 2, *S* = {3}, *s* = 1 and $P(X)=X^2/3$. The term at *m* = 1 contributes $1/6$. At every later *m* = 3ʲ the weight *m*/3 is integral. The integer-weight remainder has shifted distance to the nearest integer tending to zero off the omitted blocks. Thus the orbit agrees up to vanishing circle distance on a density-one set with the alternating points $1/3,2/3$ of the rational orbit. Their equally weighted measure has interval discrepancy $2/3$. An arc containing both points has length at least $1/3$, an empty arc has length at most $2/3$, and an arc containing one point has error at most $1/2$. Arcs of length arbitrarily close to $1/3$ contain both. To transfer this value across the perturbation, enlarge or shrink each test arc by the tail error at both ends and charge the omitted positions their fraction. A wrapping arc has the same absolute discrepancy as its complement. This shows $D_N\to2/3$. Lean obtains the upper bound from the sharp binary transition inequality, since clean shifts lie in the middle half; the short interval about both thirds gives the matching lower bound. [Both limiting examples](../NormalityChecker/MaskThirds.lean)

The all-base-primes case can also give the value $2/3$ with nonempty full support and *r* < *s*. Take *b* = 2, *S* = {2}, *s* = 1 and $P=1/3$. At an insertion $m=2^j$ the summand is $1/(3\cdot2^{2^j+j})$. On a clean block let *J* be the largest exponent inserted before its start. Once the powers of 2 have cleared, the numerator modulo 3 at shift *n* is congruent to
$(-1)^n\sum_{j=0}^J(-1)^{2^j+j}$. The sum is −1 for even *J* and −2 for odd *J*. Thus every clean block alternates between $1/3$ and $2/3$, up to the vanishing real error. The two frequencies each tend to one half, giving the same limiting discrepancy. A rational polynomial such as $P(X)=X^{s+1}(X-1)/2$ gives an integral weight at every positive index and therefore maximal discrepancy even in odd bases. [Dyadic reciprocal example](../NormalityChecker/MaskThirds.lean) · [Integer-valued quadratic weight](../NormalityChecker/MaskExamples.lean)

## A nonmonomial denominator

For integral polynomials *P* and *Q*, consider weights *P*(*m*)/(*m*ᵗ*Q*(*m*)) with *P*(0) ≠ 0 and *t* ≥ 1. Fix an off-base prime *p*. On any retained first cell, the polynomial exponent formula remains valid if *p* divides none of the retained denominator values *Q*(*m*) in the prefix. For transfer to discrepancy, assume additionally that the prime factors of the absolute values |*Q*(*m*)| at all retained indices belong to one fixed finite set. The same upper bound by the missed-window fraction then follows. The local unit condition and the global finite-support condition serve different steps of the proof. [Quotient exponent and discrepancy](../NormalityChecker/MaskQuotients.lean)

To see the local claim, take the product *D* of the retained values *Q*(*m*). The polynomial $F(Y)=\prod_m(Q(m)-Y)$ has constant term *D*. Define $U(Y)=(D-F(Y))/Y$, which has integer coefficients. At every retained index, $U(Q(m))Q(m)=D$. At the retained power *p*ᵏ, the right side is a unit at *p*, so $U(Q(p^k))$ is also a unit. Reducing the polynomial at zero shows that $U(Q(0))$ is a unit as well. The cleared polynomial $P(X)U(Q(X))$ therefore has exactly the original numerator loss at zero. For the global estimate, the bit length of |*Q*(*m*)| grows at most linearly with the bit length of *m*. Its fixed prime support supplies the common modulus on clean blocks. [Finite polynomial reciprocal and clean moduli](../NormalityChecker/MaskQuotients.lean)
