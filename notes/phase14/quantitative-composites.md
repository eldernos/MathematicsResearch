# Effective discrepancy for polynomials of a coprime Stoneham number

**Theorem (paper deduction).** Let *b*, *c* ≥ 2 be coprime integers and let *P* be a rational polynomial of degree *d* ≥ 1. Define the Stoneham number and its polynomial image by

```math
\alpha_{b,c}=\sum_{j=1}^{\infty}\frac{1}{c^j b^{c^j}},
\qquad x=P(\alpha_{b,c}).
```

Write $D_N(x;b)$ for the supremum over half-open intervals [*u*, *v*) ⊆ [0, 1] of the absolute difference between *v* − *u* and the proportion of 0 ≤ *n* < *N* with fractional part {*b*ⁿ*x*} in the interval. With $\delta_d=1/[2(2^{d+1}-2)]$, every *N* ≥ 2 satisfies

```math
D_N(x;b)\le C(b,c,P)\,N^{-\delta_d}.
```

This holds for **every degree when *c* > 2**. When **the parameter is 2**, it holds for all rational polynomials of odd prime-power degree, for degree one, and for $P(z)=Az^2+E$ with $A\ne 0$. The coefficient test below gives further dyadic quadratics. The exponent is independent of *b* and *c*. The constant and a starting threshold for the estimates in the proof are computable. A word of length *w* and integer value *m* corresponds to the interval [*m*/*b*ʷ, (*m* + 1)/*b*ʷ), including words with leading zeroes. Requiring starts to fit within the first *N* digits changes the count by at most *w* − 1. [All-prime denominator bounds](../../NormalityChecker/QuantitativeCompositeDenominators.lean) · [Finite discrepancy transfer](../../NormalityChecker/QuantitativeStonehamSupport.lean) · [Phase 13 theorem](../phase13/quantitative-normality.md)

The sharper bound is $D_N(x;b)\ll N^{-\eta_d}(1+\log N)^\ell$, with natural logarithms.

| Degree | Power saving | Logarithmic power | Parameter range |
| --- | ---: | ---: | --- |
| One | 1/2 | 2 | Every coprime parameter |
| Two | 1/6 | 3/2 | Every quadratic for *c* > 2, and the indicated dyadic quadratics |
| Three | 1/14 | 5/4 | Every cubic for every coprime parameter |
| Higher degrees covered above | $\eta_d$ from the recurrence below | 1 + 2¹⁻ᵈ | Every *c* > 2, and odd prime-power degrees at *c* = 2 |

In particular the same quadratic estimate applies in base 2 to the square of α₂,₇₇ and in base 3 to the square of α₃,₂. Counting pieces at each length improves the Phase 13 logarithmic powers 2 and 51/28 for squares and cubics respectively. [Insertion gap estimate](../../NormalityChecker/QuantitativeStonehamGaps.lean) · [Earlier estimates and source audit](../phase13/reviews/quantitative-coverage.md)

## Arithmetic at every insertion

For degree *a* ≥ 1 let $R_a(n)$ be the shifted prefix of $\alpha^a$. For an ordered tuple *j* of *a* positive integers, define its insertion position $s(j)=\sum_i c^{j_i}$ and its weight $w(j)=c^{-\sum_i j_i}$. Including all tuples at their insertion gives

```math
R_a(n)=\sum_{s(j)\le n} w(j)b^{n-s(j)}.
```

Put $R_0(n)=b^n$ and extend linearly to polynomial prefixes. For $n\ge1$ set $k=\lfloor\log_c n\rfloor$. Every included index is at most *k*, so $c^{ak}R_a(n)$ is an integer.

**Rational coefficients.** Let *D* be a common positive denominator and write it as *D*ᵦ *D*₀, where every prime of *D*ᵦ divides *b* and gcd(*D*₀, *b*) = 1. Choose *t* with *D*ᵦ dividing *b*ᵗ. Then *b*ᵗ*x* = *Y*(α)/*D*₀ with *Y* an integer polynomial of the same degree. The interval counts for these two orbits differ by at most *t* for every *N*. If *q* is the reduced denominator of the prefix of *Y* and *Q* the reduced denominator after division by *D*₀, then *q* ∣ *Q* and *Q* ∣ *D*₀*q*. Thus the possible primes of *Q* divide *cD*₀ and are coprime to *b*. The constant coefficient is included in the same transformation. [Division and frequency arithmetic](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

**Full denominator growth.** For *c* > 2 and each prime *p* ∣ *c*, put *e* = *v*ₚ(*c*). There is a precision *l*ₚ ≥ 1 such that the integer $c^{dk}R_d(n)$ has valuation at most *l*ₚ − 1 on every sufficiently late shell. For *c* = 2 and *d* an odd prime power the symmetric mass theorem gives the same statement with *p* = 2. For degree one in either family the newest summand is a unit modulo *c* after clearing *c*ᵏ. Explicit thresholds follow below. Let *A* be the nonzero leading coefficient of *Y*, set *h*ₚ = *l*ₚ − 1 + *v*ₚ(|*A*|), and take *ek* > *h*ₚ. All lower terms multiplied by *c*ᵈᵏ are multiples of *p*ᵉᵏ. The valuation of the leading term therefore survives addition. Multiplying the bounds at **all** primes of *c* gives $c^{dk}/F\le q\le c^{dk}$ with $F=\prod_{p\mid c}p^{h_p}$. Since $c^k\le n<c^{k+1}$, the reduced denominator after division satisfies

```math
\frac{n^d}{c^d F}\le Q\le D_0 n^d .
```

The Lean theorem `polynomial_prefix_denominators` gives divisibility on both sides, including division by any fixed positive denominator. Its zero-index power with dilation *c* equals *c*ᵃ times the positive-index prefix in degree *a*. Thus its integer coefficients may be taken as *c*ᵈ⁻ᵃ times the coefficients of *Y* with a final divisor *D*₀*c*ᵈ. The direct positive-index calculation gives the displayed upper constant. [Whole-denominator theorem](../../NormalityChecker/QuantitativeCompositeDenominators.lean) · [Periodic pole retention at each prime](../../NormalityChecker/PeriodicPolynomialNormal.lean) · [Dyadic pole retention](../../NormalityChecker/StonehamOddDegree.lean)

**Dyadic squares.** Suppose *b* is odd, *c* = 2, *k* ≥ 2 and 2ᵏ ≤ *n* < 2ᵏ⁺¹. The reduced denominator of the square prefix is 2²ᵏ⁻² for *n* < 3 · 2ᵏ⁻¹ and 2ᵏ⁻¹ starting at that midpoint. Multiplication by the nonzero integer *A* loses at most a factor |*A*|, and adding an integer constant times *b*ⁿ preserves the denominator. After rational coefficient division this gives, uniformly on the entire shell *X* = 2ᵏ,

```math
\frac{X}{2|A|}\le Q\le \frac{D_0 X^2}{4}.
```

More generally write *Y*(*z*) = *Az*² + *Bz* + *E* and set σ = *v*₂(*b*² − 1) − 1. The same slopes hold if *v*₂(2*A* + *B*) < *v*₂(2*A*) + σ, with *v*₂(0) = ∞. On the lower half the quadratic pole 2*k* − 2 − *v*₂(*A*) eventually exceeds *k*. On the upper half the Phase 13 calculation gives a pole of order max(0, *k* − *v*₂(2*A* + *B* + 2*A T*ₖ)), where *T*ₖ belongs to $2^\sigma\mathbb Z_2$. Under the strict inequality that valuation equals *v*₂(2*A* + *B*) for every *k*. It suffices to take *k* ≥ max(3 + *v*₂(*A*), 1 + *v*₂(2*A* + *B*)). For example the strict test fails for *z*² − 2*z*, where the loss on the upper half is unbounded. Its discrepancy rate remains open here. [Exact square profile](../../NormalityChecker/ParameterTwoSquareProfile.lean) · [Quadratic perturbation calculation](../phase13/reviews/symmetric-degree.md#quadratic-projections-with-equal-valuations)

## Computing a precision and its threshold

The following search works with ordinary integers, rational comparisons and finite fields. It can inspect just the actual cuts. Fix *p* ∣ *c* and a trial precision *l* ≥ 1. Starting at *a*₀ = *b*⁻¹ mod *p*, iterate *a*ⱼ₊₁ = *a*ⱼᶜ mod *p* to the first repeated residue. Record the preperiod length *J* and the cycle length *h*, and index the cycle from 0 at *J*. For each residue *a* in the cycle take its representative in [1, *p* − 1] and compute its lift as *a* raised to *p*ˡ⁻¹ modulo *p*ˡ. This preserves its residue and its (*p* − 1)-st power is 1 by Euler's theorem. These two properties characterize the Teichmüller lift modulo *p*ˡ, since the kernel of reduction on units has order *p*ˡ⁻¹. For *p* = 2 the lift is 1. Write *z*ⱼ for the lifted periodic sequence extended to all integer indices with this alignment. Since the principal-unit part of *b*⁻¹ has order dividing *p*ˡ⁻¹ modulo *p*ˡ, we have $b^{-c^j}\equiv z_j\pmod{p^l}$ as soon as *j* ≥ *J* and *ej* ≥ *l* − 1. [Reflected cycles and the principal-unit congruence](../../NormalityChecker/PeriodicPolynomialPrecision.lean) · [Independent composite proof](../phase13/reviews/composite-polynomials.md)

Put *B*ₗ = ⌊(*l* − 1)/*e*⌋. Reflect each coordinate as *v*ᵢ = *k* − *j*ᵢ, write |*v*| = ∑ᵢ *v*ᵢ, and set $u=n/c^k$ in [1, *c*). Let *s* be the residue of *k* modulo *h*. After multiplying the top prefix by *c*ᵈᵏ *b*⁻ⁿ, its residue modulo *p*ˡ is

```math
M_{s,l}(u)=
\sum_{v} c^{|v|}\prod_{i=1}^d z_{s-v_i}.
```

Here the sum runs over nonnegative *v* with |*v*| ≤ *B*ₗ and $\sum_i c^{-v_i}$ ≤ *u*. Terms of larger weight vanish modulo *p*ˡ. Every retained *k* − *v*ᵢ is a positive index on the correct cycle at the required precision for $k\ge K_p(l)$, where

```math
K_p(l)=B_l+\max\{1,J,\lceil(l-1)/e\rceil\}.
```

For each phase *s*, check this residue at *u* = 1 and at each distinct tuple sum $\sum_i c^{-v_i}$ strictly between 1 and *c*. At a jump include **all** tuples with that sum. Between successive jumps the residue is constant. Multiplication of each threshold by $c^{B_l}$ converts sorting and comparisons to integer operations. Try *l* = 1, 2, … until every tested residue in every phase is nonzero. This covers all shell positions, including exact insertions, using only residues modulo *p*ˡ.

**Why the search halts.** The infinite cut is an upper set containing the constant vector with entries $\lceil\log_c d\rceil$. For *c* > 2 every such upper set has nonzero periodic mass in each phase. Briefly, the one-coordinate sum is an algebraic number with nonzero conjugates of modulus at most 1/(*c* − 1). It is nonintegral, and inclusion–exclusion on the finitely many minimal orthants expresses the mass as a monic polynomial in it with algebraic-integer coefficients. The family of upper sets containing the anchor is compact and the mass modulo each *p*ˡ depends on finitely many coordinates. Some common precision therefore detects all those masses. For *c* = 2 and *d* = *q*ʳ with *q* an odd prime, the actual cuts are permutation invariant. In characteristic *q* all nonconstant rotation orbits in each weight slice have cardinal divisible by *q*. The orthant numerator is congruent to the diagonal monomial, hence is nonzero at 2. Compactness on the closed symmetric family gives the required binary precision. The finite actual-cut test must succeed by these results, even if it succeeds earlier than a test over all anchored upper sets. Finitely many phases and primes suffice. Choose *k* at least every *K*ₚ(*l*ₚ) and every ⌊*h*ₚ/*e*⌋ + 1 to treat *Y* on a common tail. [Periodic nonvanishing](../../NormalityChecker/PeriodicPolynomialMass.lean) · [Uniform periodic precision](../../NormalityChecker/PeriodicPolynomialPrecision.lean) · [Uniform symmetric precision](../../NormalityChecker/StonehamSymmetricMass.lean)

For example take *b* = 2, *c* = 77 and the pure square. The table gives finite actual-cut checks. The final column counts the cells over all phases at the indicated precision. The final row checks a cycle with a nonempty preperiod.

| Base, parameter, degree | Prime | Preperiod followed by cycle mod the prime | Passing precision | Sufficient shell index | Cells checked |
| --- | ---: | --- | ---: | ---: | ---: |
| 2, 77, 2 | 7 | (4, 2) | 3 | 4 | 8 |
| 2, 77, 2 | 11 | (6, 8, 2, 7) | 5 | 8 | 24 |
| 3, 2, 3 | 2 | (1) | 7 | 12 | 11 |
| 7, 93, 2 | 31 | 9, then (16, 4, 2, 8) | 3 | 4 | 16 |

Thus for the square with parameter 77, from *k* = 8 onward its denominator is at least 77²ᵏ/(7² · 11⁴). The following Python 3 code reproduces the cell counts and checks the precision in each row. The argument `cycle` starts at the first periodic index `J`.

```python
from collections import defaultdict
from itertools import product
from math import prod


def check_cells(c, p, e, d, precision, J, cycle):
    B = (precision - 1) // e
    scale, modulus = c**B, p**precision
    units = [pow(a, p**(precision - 1), modulus) for a in cycle]
    cells = 0
    for s in range(len(cycle)):
        jumps = defaultdict(int, {scale: 0})
        for v in product(range(B + 1), repeat=d):
            if sum(v) > B:
                continue
            location = sum(c**(B - i) for i in v)
            if location < c * scale:
                phase = prod(units[(s - i - J) % len(cycle)] for i in v)
                jumps[max(scale, location)] += c**sum(v) * phase
        residue = 0
        for location in sorted(jumps):
            residue = (residue + jumps[location]) % modulus
            if residue == 0:
                return 0
        cells += len(jumps)
    return cells


assert check_cells(77, 7, 1, 2, 3, 0, [4, 2]) == 8
assert check_cells(77, 11, 1, 2, 5, 0, [6, 8, 2, 7]) == 24
assert check_cells(2, 2, 1, 3, 7, 0, [1]) == 11
assert check_cells(93, 31, 1, 2, 3, 1, [16, 4, 2, 8]) == 16
```

Direct positive-index summation agreed with the reflected residues at every jump on two complete cycles beginning at each listed threshold. The dyadic cube also has a separate direct proof of the sharper threshold *k* = 7. [Independent cube calculation](../phase13/reviews/symmetric-degree.md#an-exact-check-for-cubes)

## Clean pieces at every length

Write *x′* = *b*ᵗ*x*. Its real orbit differs from the shifted rational prefix by at most *K*/(*n* + 1) at every index *n*. Indeed, if a degree-*a* tuple is omitted then one coordinate satisfies *c*ʲ ≥ (*n* + 1)/*a*. Summing the geometric tail in that coordinate and all weights in the other coordinates gives the bound *a*²(1 − 1/*c*)⁻ᵃ/(*n* + 1). The omitted radix factor is at most one. Sum these bounds against the absolute coefficients of *Y*/*D*₀ to obtain *K*. The constant term has zero error. [Kernel real-tail bound](../../NormalityChecker/QuantitativeStonehamTail.lean)

Let *X* = 2ᵘ and take any integer 1 ≤ *T* ≤ *X*. Partition [*X*, *X* + *T*) at its distinct interior insertions. On each piece starting at *a*, the prefix at *a* + *i* equals *b*ⁱ times the prefix at *a*, for 0 ≤ *i* < *length*. Every insertion at *a* has already been included. An insertion at *X* + *T* belongs to the next interval. A singleton final piece contributes its one sample. [Clean propagation](../../NormalityChecker/StonehamPolynomialExpansion.lean)

**Length estimate.** If the piece lengths are $L_1,\ldots,L_J$, then for any real γ > 0

```math
\sum_{j=1}^J L_j^{\gamma}\le M_{d,\gamma} X^{\gamma}.
```

To see this, group lengths into ranges 2ʲ ≤ *L* < 2ʲ⁺¹, where 0 ≤ *j* ≤ *u*. Write *U* = 2ʲ and *m* = *u* + 1 − *j*, so *U*2ᵐ = 2*X*. Starts in one range are *U*-separated because the preceding piece already has length at least *U*. An insertion is a sum of at most *d* powers of *c*. Pad the vector with zeros and replace all coordinates below *U* by zero. In [*U*, *U*2ᵐ) there are at most *m* + 1 possible powers, since successive powers grow by a factor of at least two. Including zero gives at most (*m* + 2)ᵈ truncated vectors. For each such vector with sum *z*, the original starts lie in [*z*, *z* + (*d* + 1)*U*). There are at most *d* + 1 separated starts there. Allow one more start for *X*. In particular the number in this length range is at most 1 + (*d* + 1)(*m* + 2)ᵈ. This argument depends only on the actual length, so it includes the shortened final piece. [Kernel packing and finite moment estimate](../../NormalityChecker/QuantitativeStonehamGaps.lean)

Set *z* = 2⁻ᵞ and reindex by *i* = *u* − *j*. After dividing by $X^\gamma$ the sum is bounded by $2^\gamma\sum_{i\ge0}[1+(d+1)(i+3)^d]z^i$. Since $(i+3)^d\le 3^d d! \binom{i+d}{d}$, the binomial series gives the computable choice

```math
M_{d,\gamma}=2^\gamma\left(\frac{1}{1-z}+
\frac{(d+1)3^d d!}{(1-z)^{d+1}}\right).
```

In degree one the required γ is zero and there are at most two pieces. For the other length exponent ν ≥ 1 use $\sum_j L_j^\nu\le T^\nu\le X^\nu$ by superadditivity.

## From reduced moduli to arbitrary final cutoffs

We use Vandehey's Theorem 5.1 and the interval Erdős–Turán inequality as external analytic inputs. Write $\mathrm e(y)=\exp(2\pi i y)$. At depth *k* ≥ 0 take $\alpha=1/(2^{k+2}-2)$ and $r=2^{-k}$. Vandehey bounds the absolute sum of $\mathrm e(ab^i/q)$ on every positive length *L* by

```math
\bigl(A_k q^{\alpha}L^{\gamma}+B_k q^{-\alpha}L^{\nu}\bigr)(1+\log q)^r.
```

Here gcd(*a*, *q*) = 1 and the primes of *q* belong to a fixed finite set *S* coprime to *b*. For *q* > 1 replace the numerator by *ab*⁻¹ mod *q* in the theorem indexed from 1 to *L* to obtain indices 0 through *L* − 1. For *q* = 1 the sum has modulus *L*, covered by *B*ₖ ≥ 1 and ν ≥ 1. Lemma 2.3 removes the single-period length restriction before the iteration in Proposition 4.1. This permits every short piece used above. The auxiliary divisor in preprint (12) must take its prime product over the primes **dividing the current modulus** and take the additional factor for 4 exactly when 4 divides that modulus. In the induction take common upper bounds at the previous depth, then maximize the new constants over the finitely many actual supports contained in *S*. Equation (3), Lemma 4.2 and Theorem 5.1 compute these constants from orders, valuations, finite products and recursions. [Vandehey, preprint §§2, 4–5](https://arxiv.org/pdf/1606.07911v1) · [Published article](https://doi.org/10.1007/s11854-019-0038-2) · [Audit of the support correction](../phase13/reviews/quantitative-coverage.md#which-exponential-sums-are-covered)

Take *S* to be the primes of *cD*₀. At Fourier frequency *h* the rational starting point on a clean piece has reduced denominator *q* = *Q*/gcd(*h*, *Q*). The positive power of *q* costs at most $Q^\alpha$. The negative power contributes *Q*⁻ᵅ gcd(*h*, *Q*)ᵅ. Define $G(Q)=\sum_{t\mid Q}t^{\alpha-1}$. Grouping by the gcd and enlarging each class to all multiples gives

```math
\sum_{h=1}^H\frac{\gcd(h,Q)^\alpha}{h}
\le (1+\log H)G(Q).
```

Expanding a finite product of convergent geometric series bounds $G(Q)$ by $\prod_{p\in S}(1-p^{\alpha-1})^{-1}$, since α < 1. This applies separately to every piece, including when a frequency removes a prime entirely. For example, if *Q* = 77 and *h* = 7, the orbit bound is applied at 11. If *h* = 77 it is applied at 1. `discrepancy_of_denominator_range` combines this Euler product, the reduced-frequency calculation and the all-length bound with Erdős–Turán. It permits independent lower and upper denominator bounds on each shell. [Kernel finite transfer and Euler product](../../NormalityChecker/QuantitativeStonehamSupport.lean) · [Frequency denominator identity](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

Write $D_{X,T}$ for interval discrepancy on [*X*, *X* + *T*). Erdős–Turán in count form bounds $T D_{X,T}$ by an absolute constant times the sum of $T/(H+1)$ and the harmonically weighted character sums. An effective choice is 4 using the degree-*H* Selberg interval majorant and minorant. Replacing the real values by the clean rational orbits costs at most 2π*hKT*/*X* per frequency and hence at most 2π*KH* in the weighted sum. Use *H* = ⌊√*X*⌋. If $c_-X^\lambda\le Q\le c_+X^d$ on the shell, set $u_+=d\alpha+\gamma$ and $u_-=\nu-\lambda\alpha$. With $L_X=1+\log X$ the finite transfer and length estimate give

```math
T D_{X,T}\ll \sqrt{X}+L_X^{1+r}(X^{u_+}+X^{u_-}).
```

All implied constants are uniform in *T*, the test interval and the individual piece lengths. For the full-growth families use λ = *d*, absorbing the factor 2ᵈ from *n* < 2*X* into *c*₊. For dyadic squares use (*d*, λ) = (2, 1). At depth one, (α, γ, ν) = (1/6, 1/2, 1), so both exponents in the latter bound equal 5/6. In particular the upper half contributes the same power of *X* as the lower half. [All-prefix audit](../phase13/reviews/quantitative-and-mixed.md) · [Erdős–Turán, Bailey–Crandall Theorem 2.2(9)](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf#page=4)

**The exponents.** For a full-growth family use depth *k* = *d* − 1. The following rational recurrence computes Vandehey's exponents and both savings from *d* alone. Start with $s_0=2$. For *i* ≥ 0 put $a_i=1/(4\cdot 2^i-2)$, $t_i=s_i-4+2^{1-i}$ and set

```math
s_{i+1}=s_i+1-a_i t_i .
```

Then α = *a*ₖ, γ = 1 − *a*ₖ*s*ₖ and ν = 1 + *a*ₖ*t*ₖ. In particular γ > 0 for *k* ≥ 1 by Vandehey's recurrence, γ₀ = 0 and ν ≥ 1. The rational margin gives *s*ₖ > *k* + 3/2 and *s*ₖ ≤ *k* + 2, hence *d* − *t*ₖ ≥ 1. Thus $1-u_+=a_k(s_k-d)>a_k/2$ and $1-u_-=a_k(d-t_k)\ge a_k$. The sharper exponent in the table is

```math
\eta_d=\min\{1/2,1-u_+,1-u_-\}>\delta_d .
```

In degree two this gives 1/6, and in degree three it gives 1/14. The dyadic-square calculation gives the same η₂ using its own lower slope. [Kernel margin](../../NormalityChecker/QuantitativeStonehamExponents.lean) · [Identification with Vandehey's recurrence](../phase13/reviews/quantitative-coverage.md#exponents-at-the-same-depth)

For each interval, add **count errors** over complete dyadic shells and the last partial shell. Every shell-prefix error is at most a computable constant times $X^{1-\eta_d}(1+\log X)^{1+r}$. The ratio between successive powers is $2^{1-\eta_d}\ge\sqrt{2}$. Early shells can be charged their total length, at most $2c^{k_0}$ when $k_0$ is the chosen arithmetic shell index, and index zero costs at most one. Dividing by *N* and taking the supremum gives the log-refined rate for every *N* ≥ 2. The shift by *t* costs at most *t*/*N*. To obtain the pure power, maximize $(1+u)^{1+r}\exp(-u(\eta_d-\delta_d))$ at $u=\max(0,(1+r)/(\eta_d-\delta_d)-1)$. This also gives an effective multiplier. All real constants in the proof can be rounded upward to rational bounds using the strict margins. [Kernel dyadic summation](../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

## Verification

The new Lean modules combine the local denominator bounds at all primes, bound the length moment of insertion gaps at an arbitrary cutoff, and prove the fixed-support Euler factor and the finite discrepancy theorem with Vandehey and Erdős–Turán as explicit hypotheses. The proof of termination, the evaluation of the length bound and the assembly of the real-orbit estimates are paper deductions. The table records finite modular computations. The square's exact denominator and the earlier periodic and symmetric nonvanishing theorems are kernel-verified inputs. The quadratic coefficient test uses the linked Phase 13 paper calculation.

```sh
lake build NormalityChecker.QuantitativeCompositeDenominators NormalityChecker.QuantitativeStonehamGaps NormalityChecker.QuantitativeStonehamSupport
for module in QuantitativeCompositeDenominators QuantitativeStonehamGaps QuantitativeStonehamSupport; do
  lake env leanchecker "NormalityChecker.$module"
done
```
