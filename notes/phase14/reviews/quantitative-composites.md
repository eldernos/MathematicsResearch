# Independent review of effective Stoneham discrepancy

**Signed off at `c9d4cab`.** Let *b*, *c* ≥ 2 be coprime, let α be the sum of $`c^{-j}b^{-c^j}`$ over positive *j*, and let *P* be a rational polynomial of degree *d* ≥ 1. For every *N* ≥ 2, the interval discrepancy of the first *N* fractional parts of $`b^nP(\alpha)`$, starting at *n* = 0, is at most $`C(b,c,P)N^{-1/[2(2^{d+1}-2)]}`$ with computable *C*. I confirm this for every degree at *c* > 2. At *c* = 2 I confirm degree one, odd prime-power degrees, and the quadratics satisfying the coefficient test below, including every affine function of the square with nonzero slope. In the covered quadratic and cubic cases the stronger bounds are $`O(N^{-1/6}(1+\log N)^{3/2})`$ and $`O(N^{-1/14}(1+\log N)^{5/4})`$, respectively. The logarithmic powers are upper-bound exponents. Their optimality would require a separate lower-bound argument. [Track D theorem and proof](../quantitative-composites.md)

## A finite cutoff at every prime

Fix a prime *p* dividing *c*, write $`e=v_p(c)`$, and let $`k=\lfloor\log_c n\rfloor`$. Write $`R_d(n)`$ for the shifted prefix of the power, incorporating all tuples with $`\sum_i c^{j_i}\le n`$. Multiplying it by $`c^{dk}b^{-n}`$ changes the summand for $`v_i=k-j_i`$ to $`c^{\sum_i v_i}\prod_i b^{-c^{k-v_i}}`$. At precision $`p^l`$ only weights $`\sum_i v_i\le B=\lfloor(l-1)/e\rfloor`$ can survive.

Iterate the *c*th power map from $`b^{-1}\bmod p`$. If its cycle starts at index *J* and has length *h*, the coordinate with reflected index *v* uses cycle entry $`(k-v-J)\bmod h`$, counting from zero. For a cycle residue *a*, the lift $`a^{p^{l-1}}\bmod p^l`$ reduces to *a* and has order dividing *p* − 1. The kernel of reduction has order $`p^{l-1}`$. Thus the principal-unit factor of the original inverse radix disappears once $`e(k-v)\ge l-1`$, also at *p* = 2. The stated cutoff

```math
k\ge B+\max\{1,J,\lceil(l-1)/e\rceil\}
```

therefore puts every surviving coordinate on the correct cycle at a positive original index. For each phase the truncated sum changes only at the finitely many numbers $`\sum_i c^{-v_i}`$. Testing 1 and every distinct jump strictly between 1 and *c*, after adding all tied tuples, covers the whole half-open shell. The excluded endpoint *c* is 1 on the next shell.

For termination, every cut is an upper set through the constant vector with entries $`\lceil\log_c d\rceil`$. At *c* > 2 the periodic mass is nonzero for every such set and each phase. The one-coordinate periodic sum has all conjugates of absolute value in $`(0,1/(c-1)]`$, so it is nonintegral. The mass is a monic polynomial in that sum with integral algebraic coefficients. At *c* = 2 and $`d=q^r`$ for an odd prime *q*, the cuts are symmetric. Rotation in *q*-power dimension leaves the diagonal contribution modulo *q*, giving the limiting integer mass $`-2^m\bmod q`$ for the first occupied diagonal index *m*. In each case the family through the anchor is compact, and the residue at each precision depends on a finite set of coordinates. Nonvanishing gives a common passing precision, first per phase and then over the finitely many phases. The search requires no numerical bound from compactness. [Periodic mass](../../../NormalityChecker/PeriodicPolynomialMass.lean) · [Uniform periodic precision](../../../NormalityChecker/PeriodicPolynomialPrecision.lean) · [Uniform binary precision](../../../NormalityChecker/StonehamSymmetricMass.lean)

I independently found the cycles by iteration and the lifts by searching the roots of $`z^{p-1}=1\bmod p^l`$. Starting at the resulting shell threshold *K*, I summed **all** positive-index ordered tuples over two complete phase cycles. The counts in the last column include the first and last integer in each shell and both sides of each interior insertion, counted once per position. Every residue agreed with the reflected calculation. The final row also tests $`v_p(c)>1`$.

| Base, parameter, degree | Prime | Preperiod, period | First passing precision | Shell threshold | Reflected cells | Direct positions |
| --- | ---: | --- | ---: | ---: | ---: | ---: |
| 2, 77, 2 | 7 | 0, 2 | 3 | 4 | 8 | 52 |
| 2, 77, 2 | 11 | 0, 4 | 5 | 8 | 24 | 200 |
| 3, 2, 3 | 2 | 0, 1 | 7 | 12 | 11 | 292 |
| 7, 93, 2 | 31 | 1, 4 | 3 | 4 | 16 | 136 |
| 3, 20, 2 | 2 | 0, 1 | 5 | 4 | 4 | 22 |

## Combining poles and treating the dyadic square

Shift the orbit by *t* positions to clear the radix-prime part of a common coefficient denominator. Write its new value as $`Y(\alpha)/D_0`$ with *Y* integral, leading coefficient *A*, and $`\gcd(D_0,b)=1`$. The shift changes an interval count by at most *t*. For each $`p\mid c`$ the top term of the prefix of *Y*, cleared by $`c^{dk}`$, has valuation at most $`h_p=l_p-1+v_p(A)`$. Every lower term has valuation at least $`ek`$. Taking *k* beyond all local thresholds with $`ek>h_p`$ rules out cancellation at every prime simultaneously. The gcd of the cleared numerator with $`c^{dk}`$ therefore divides $`F=\prod_{p\mid c}p^{h_p}`$. If the resulting reduced fraction is $`a/q`$, division by $`D_0`$ gives denominator $`Q=qD_0/\gcd(a,D_0)`$. Consequently

```math
\frac{n^d}{c^d F}\le Q\le D_0 n^d.
```

For the pure square at *c* = 77 this gives $`q\ge 77^{2k}/(7^2 11^4)`$ for every *k* ≥ 8. In degree one the newest summand of the cleared linear prefix is already a unit modulo *c*. [All-prime divisibility theorem](../../../NormalityChecker/QuantitativeCompositeDenominators.lean)

For *c* = 2 write $`Y(z)=Az^2+Bz+E`$, $`X=2^k`$, and $`\sigma=v_2(b^2-1)-1`$. Use $`v_2(0)=+\infty`$. The pure square has denominator $`X^2/4`$ before $`3X/2`$ and $`X/2`$ from that midpoint onward for *k* ≥ 2. On the first half its pole after multiplication by *A* exceeds the linear pole once $`2k-2-v_2(A)>k`$. On the second half the only omitted pair among indices through *k* is $`(k,k)`$. Expanding that truncated square gives a pole of order $`\max(0,k-v_2(2A+B+2AT_k))`$, where $`T_k\in 2^\sigma\mathbb Z_2`$. If $`v_2(2A+B)<v_2(2A)+\sigma`$, the upper-half valuation is exactly $`v_2(2A+B)`$. Both conclusions hold at the stated threshold $`k\ge\max(3+v_2(A),1+v_2(2A+B))`$. For a general passing quadratic the comparability constants can change. For example, $`z^2+2z`$ at *b* = 3 has upper-half denominator $`X/4`$. The strict test is sufficient. For $`z^2-2z`$ the loss relative to *k* is unbounded, and this proof supplies no rate. [Exact square profile](../../../NormalityChecker/ParameterTwoSquareProfile.lean) · [Upper-half coefficient identity](../../phase13/reviews/symmetric-degree.md#quadratic-projections-with-equal-valuations)

As a finite check, I advanced the cleared linear and square numerators at each digit for bases 3, 5, 7, 9, 15 and 17 on shells 2 through 9. The pure-square formula agreed at all 6,120 positions, including every midpoint.

## From the original orbit sum to every prefix

Vandehey’s Theorem 5.1 bounds the absolute unnormalized sum for every reduced numerator and every positive length *L*. Lemma 2.3 handles full periods and a remainder, and Proposition 4.1 propagates the all-length assertion. At reduced modulus *m* > 1, changing the numerator by $`b^{-1}\bmod m`$ moves the initial index from 1 to 0. At *m* = 1 the sum is exactly *L*, covered by $`B_k\ge1`$ and $`\nu_k\ge1`$. In preprint (12) take the radical of the current modulus. For $`p^a\parallel m`$ and $`0<x<1`$, give the auxiliary divisor exponent $`1+\lfloor xa\rfloor`$, raising this to at least 2 at *p* = 2 when $`4\mid m`$. The divisor then divides *m*, has the same prime support, and lies between $`m^x`$ and $`2\,\mathrm{rad}(m)m^x`$ as required by (13). Common bounds from the previous induction depth and a maximum over the finitely many current supports give computable constants. [Vandehey, §§2, 4–5, preprint numbering](https://arxiv.org/pdf/1606.07911v1)

For frequency *h* the starting denominator becomes $`m=Q/\gcd(h,Q)`$. Write α for Vandehey’s modulus exponent. The positive power is bounded by $`Q^\alpha`$. Put $`G_\alpha=\prod_{p\mid cD_0}(1-p^{\alpha-1})^{-1}`$. Grouping the negative power by $`g=\gcd(h,Q)`$ and summing reciprocals of multiples of *g* gives

```math
\sum_{h=1}^H\frac{\gcd(h,Q)^\alpha}{h}
\le (1+\log H)G_\alpha.
```

Here $`0<\alpha\le 1/2`$. This bound is uniform in the starting denominator, the frequency cutoff and every support left after reduction. The interval Erdős–Turán inequality in count form applies to half-open intervals. A constant 4 suffices with cutoff term $`T/(H+1)`$ by the Selberg majorant and minorant, whose mean error is $`1/(H+1)`$ and whose nonzero Fourier coefficients are bounded by $`1/(\pi h)+1/(H+1)`$. [Frequency transfer](../../../NormalityChecker/QuantitativeStonehamSupport.lean) · [Bailey–Crandall, Theorem 2.2(9)](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf#page=4)

For an omitted positive-index tuple of degree *a*, some coordinate has $`c^j\ge(n+1)/a`$. Summing $`c^{-j}`$ on that tail, the full geometric sums in the remaining coordinates, and then over the *a* choices gives at most $`a^2(1-1/c)^{-a}/(n+1)`$. The omitted radix factor is at most one. Summing against the absolute coefficients bounds the real error by $`K/(n+1)`$ at each actual position. Split $`[X,X+T)`$, $`1\le T\le X=2^u`$, at interior insertions. The rational prefix advances exactly by multiplication by *b* inside a piece, since every insertion at its start has been included. The total Fourier-weighted replacement error is at most $`2\pi KHT/X`$, also when the final piece has length one. [Real-tail theorem](../../../NormalityChecker/QuantitativeStonehamTail.lean) · [Clean propagation](../../../NormalityChecker/StonehamPolynomialExpansion.lean)

For piece lengths in $`[U,2U)`$, $`U=2^j`$, put $`i=u-j`$. The starts are *U*-separated. Discarding insertion coordinates below *U* leaves at most $`(i+3)^d`$ ordered vectors, each covering starts in an interval of width $`(d+1)U`$. Allow one additional start for *X*. Thus for $`\gamma>0`$ the length moment divided by $`X^\gamma`$ is bounded by $`2^\gamma\sum_{i\ge0}[1+(d+1)(i+3)^d]2^{-i\gamma}`$, an effectively bounded convergent series. Using the **actual** last length makes this uniform in *T*. Degree one has at most two pieces and allows $`\gamma=0`$. For $`\nu\ge1`$ the other moment is at most $`T^\nu`$. This removes the extra logarithm incurred by counting all pieces alike. [Finite length moment](../../../NormalityChecker/QuantitativeStonehamGaps.lean)

## Exact margins and logarithmic powers

At depth $`k=d-1`$, put $`a_k=1/(2^{k+2}-2)`$, $`s_k=(1-\gamma_k)/a_k`$ and $`t_k=(\nu_k-1)/a_k`$. Equation (15) of the preprint gives $`s_k-t_k=4-2^{1-k}`$. Its recurrence gives $`s_0=2`$ and $`s_{k+1}=s_k+1-a_k t_k`$. Since $`\nu_k\ge1`$, we have $`s_k\le k+2`$, $`t_0=t_1=0`$ and $`0\le t_j\le j-1`$ for *j* ≥ 2. The cumulative loss is strictly less than $`\sum_{j\ge2}(j-1)2^{-j-1}=1/2`$. Hence $`s_k>k+3/2`$ and $`d-t_k\ge1`$. In the full-growth case the two savings are $`a_k(s_k-d)>a_k/2`$ and $`a_k(d-t_k)\ge a_k`$. This proves the strict rational margin in every degree. [Exponent lemma](../../../NormalityChecker/QuantitativeStonehamExponents.lean) · [Vandehey, Theorem 5.1 and (15)](https://arxiv.org/pdf/1606.07911v1#page=14)

The table gives the savings in the two Vandehey terms using the denominator size on each indicated range. In the dyadic square the controlling term switches at the midpoint.

| Range | Alpha | Gamma | Nu | Saving from positive modulus power | Saving from negative modulus power | Log power |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Linear | 1/2 | 0 | 1 | 1/2 | 1/2 | 2 |
| Quadratic with full growth, or first half of covered dyadic quadratic | 1/6 | 1/2 | 1 | 1/6 | 1/3 | 3/2 |
| Second half of covered dyadic quadratic, midpoint included | 1/6 | 1/2 | 1 | 1/3 | 1/6 | 3/2 |
| Cubic | 1/14 | 5/7 | 29/28 | 1/14 | 5/28 | 5/4 |

With $`H=\lfloor\sqrt X\rfloor`$, the truncation and real-tail errors cost $`O(\sqrt X)`$ counts. The single harmonic logarithm and Vandehey’s $`2^{-k}`$ log power give $`1+2^{1-d}`$. Write η for the minimum of the two savings and 1/2. For each test interval sum the count errors over complete dyadic shells and the final partial shell. The power $`X^{1-\eta}`$ grows by a factor of at least $`\sqrt2`$ per shell, so the sum through *N* is $`O(N^{1-\eta}(1+\log N)^{1+2^{1-d}})`$. The finitely many early samples cost their computable length, and the fixed shift costs at most *t*. Division by *N* gives the asserted discrepancy for every prefix. The strict gap $`\eta>a_k/2`$ absorbs the logarithm effectively by maximizing $`(1+u)^{1+2^{1-d}}\exp[-(\eta-a_k/2)u]`$ over $`u\ge0`$. [Partial-shell summation](../../../NormalityChecker/QuantitativeStonehamDiscrepancy.lean)

## Scope of Lean verification

I re-elaborated all three new module sources at `c9d4cab` with Lean 4.36.0 and ran `leanchecker` successfully on each. `polynomial_prefix_denominators` proves eventual divisibility with existential loss and cutoff for its zero-index model. A degree-*a* model with dilation *c* equals $`c^a R_a`$ by reindexing, so a common factor $`c^d`$ suffices across the polynomial. The explicit prime-by-prime loss *F*, the terminating actual-cut algorithm and its computed thresholds are deductions in the note. `square_shell_denominator` uses the existing exact positive-index profile for the pure square. The mixed quadratic coefficient criterion uses the upper-half algebra above.

`clean_length_moment` bounds the finite sum over length classes. The convergent series evaluation is the paper step. `discrepancy_of_denominator_range` proves the finite estimate with the Euler factor, separate lower and upper denominator bounds, a supplied partition and a supplied real error bound. Its hypotheses explicitly include `FixedSupportBound` and `ErdosTuran`. The quantitative discrepancy theorem for the real polynomial value, including the numerical rate for every *N*, is a paper deduction from those analytic inputs and the checked arithmetic and finite estimates.
