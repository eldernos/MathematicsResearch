# Which odd radices resonate for the Stoneham quadratic?

**Theorem.** Let *b* ≥ 3 be odd, and consider the polynomial *X*² − 2*X* at the positive-index Stoneham number

```math
X_b=\sum_{j\ge1}\frac{1}{2^j b^{2^j}}.
```

Expand the polynomial as a sum of terms with factors *b*<sup>−*e*</sup>. Multiply by *b*<sup>*n*</sup> and keep the terms with *e* ≤ *n*. On the upper half of shell *k* ≥ 1, given by 3·2<sup>*k*−1</sup> ≤ *n* < 2<sup>*k*+1</sup>, the reduced denominator of this rational prefix is independent of *n*. Call it *qₖ(b)*. Write *v* for the 2-adic valuation, with *v*(0) = +∞, and put *s(b)* = *v*(*b*² − 1) − 1. Fix integers *s* ≥ 2, *H* ≥ 0 and *k* ≥ 1, and set *t* = *k* − 1 − *s* − *H*. Suppose *t* > *s*.

- If *v*(*k* + 1) ≠ *s*, there are no radices with *s(b)* = *s* and *qₖ(b)* ≤ 2<sup>*H*</sup>.
- If *v*(*k* + 1) = *s*, such radices form exactly two opposite residue classes modulo 2<sup>*t*</sup>. After choosing the sign representative of *b* congruent to 1 modulo 4, they form exactly one class.

For example, take *k* = 11, *s* = 2 and *H* = 0. The upper prefix is integral precisely for *b* ≡ 93 or 163 modulo 256 in this stratum. With *H* = 1 the two classes reduce to 93 and 35 modulo 128.

## The coordinate on the normalized radices

Write *u* for whichever of ±*b* is 1 modulo 4. Put λ = log(*u*⁻¹) ∈ 4ℤ₂. For *j* ≥ 1 define

```math
\delta_j=\frac{b^{-2^j}-1}{2^j},\qquad
C=\lambda+\sum_{j\ge1}(\delta_j-\lambda),\qquad
\kappa=-\frac{C}{\lambda}.
```

The sign disappears because 2<sup>*j*</sup> is even. For *b* ≥ 3, λ ≠ 0. We prove that κ + 1 = *F*(λ), where

```math
F(x)=\sum_{m\ge1}a_m x^m,\qquad
a_m=\frac{2^m}{(2^m-1)(m+1)!}.
```

The map *F* is a bijective isometry of 4ℤ₂ onto itself. Thus *u* ↦ *F*(log(*u*⁻¹)) gives a bijective isometry from 1 + 4ℤ₂ onto 4ℤ₂. At *u* = 1 this series has value zero, which supplies the extension at the point where the quotient defining κ has zero denominator. The valuation of its value is *v*(*u* − 1), since *F*(0) = 0 and inversion preserves unit distances. For integer radices this is *s(b)* because *v*(*u* + 1) = 1 and (*u* − 1)(*u* + 1) = *b*² − 1.

### Taylor expansion and interchange of the sums

Let *d₂(n)* be the sum of the binary digits of *n*. Counting the even factors in a factorial repeatedly gives *v*(*n*!) = Σ<sub>ℓ≥1</sub> ⌊*n*/2<sup>ℓ</sup>⌋. Each binary digit equal to 1 in position *i* contributes 2<sup>*i*</sup> − 1 to this sum, so *v*(*n*!) = *n* − *d₂(n)*. The factor 2<sup>*m*</sup> − 1 is odd. Hence

```math
v(a_m)=d_2(m+1)-1\ge0,\qquad a_1=1.
```

The exponential and logarithm series converge on 4ℤ₂ and 1 + 4ℤ₂, respectively. For *x* ∈ 4ℤ₂ the terms of exp(*x*) beyond the linear term have valuation at least *v*(*x*) + 1, by the factorial formula. For log(1 + *z*), the degree-*n* term has valuation *nv*(*z*) − *v*(*n*), which tends to infinity. The formal inverse and addition identities for these power series apply here. For instance, in log(exp(*x*)) the term indexed by *r* positive degrees *n₁*, …, *nᵣ* of total degree *N* has valuation at least *N* + *r* − *v*(*r*) when *v*(*x*) ≥ 2. In exp(log(1 + *z*)) the corresponding lower bound is *N* + *r* − *v*(*r*!) ≥ *N*. Each total degree has only finitely many compositions. These estimates justify regrouping by degree. The exponential addition identity follows by the binomial theorem and the same factorial bound on its two indices. In particular, exp(2<sup>*j*</sup>λ) is the 2<sup>*j*</sup>th power of *u*⁻¹.

For λ ≠ 0, Taylor expansion gives

```math
\frac{\delta_j-\lambda}{\lambda}
 =\sum_{m\ge1}\frac{2^{jm}\lambda^m}{(m+1)!}.
```

Writing *s* = *v*(λ) ≥ 2, each summand has valuation

```math
(j-1)m+sm+d_2(m+1)-1\ \ge\ (j-1)+2m.
```

For any fixed precision only finitely many pairs (*j*, *m*) contribute. This proves convergence of the double family, allows either order of summation, and shows δⱼ → λ. Summing the geometric series in *j* gives 2<sup>*m*</sup>/(1 − 2<sup>*m*</sup>). The minus sign in κ therefore gives the positive coefficient *aₘ* above.

An equivalent verification avoids the double sum. Coefficient comparison gives

```math
e^{2x}-1-2x=2x\big(F(2x)-F(x)\big).
```

Put *x* = 2<sup>*j*−1</sup>λ and divide by 2<sup>*j*</sup>. Then δⱼ − λ = λ(*F*(2<sup>*j*</sup>λ) − *F*(2<sup>*j*−1</sup>λ)). The first *J* corrections sum to λ(*F*(2<sup>*J*</sup>λ) − *F*(λ)). Passing to the limit gives *C* = λ(1 − *F*(λ)). This is the identity used in the Lean proof.

### Distance and surjectivity

For *x*, *y* ∈ 4ℤ₂, the difference of their *m*th powers is (*x* − *y*) times a sum of *m* monomials of degree *m* − 1 in *x* and *y*. That sum belongs to 4<sup>*m*−1</sup>ℤ₂. Since each *aₘ* is integral, *R(x)* = *F(x)* − *x* satisfies

```math
|R(x)-R(y)|_2\le\tfrac14|x-y|_2.
```

The linear term gives |*F(x)* − *F(y)*|₂ = |*x* − *y*|₂. For any *z* ∈ 4ℤ₂ the map *x* ↦ *z* − *R(x)* preserves this complete ball and contracts distances by a factor of at most 1/4. Its unique fixed point solves *F(x)* = *z*. The same argument with coefficients 1/*m*! gives a contraction factor of at most 1/2 for exp(*x*) − 1 − *x*. Thus exp is a bijective isometry from 4ℤ₂ onto 1 + 4ℤ₂. Its inverse log and the map *u* ↦ *u*⁻¹ preserve distances there.

## Counting radices in a shell

The exact upper-shell denominator theorem specializes to

```math
q_k(b)=\max\big(1,2^{k-1-s(b)}|k-\kappa(b)|_2\big).
```

It applies throughout the indicated closed-left upper half-shell and also covers exact cancellation. For *s(b)* = *s* and *H* ≥ 0 the requested inequality is equivalent to *F*(λ) ≡ *k* + 1 modulo 2<sup>*t*</sup>. If *H* < 0, a positive denominator cannot meet the threshold. When *t* > *s*, every element of a residue ball meeting valuation *s* has that same valuation. This proves necessity. Conversely, if *v*(*k* + 1) = *s*, the unique *u₀* with *F*(log(*u₀*⁻¹)) = *k* + 1 has *v*(*u₀* − 1) = *s*. By the isometry, the whole solution ball is exactly *u* ≡ *u₀* modulo 2<sup>*t*</sup>. Both signs occur among positive integer radices, and the two classes are distinct already modulo 4. The strict boundary matters. For *t* ≤ *s*, the entire stratum meets the threshold if *k* + 1 is divisible by 2<sup>*t*</sup> (automatically for *t* ≤ 0), and otherwise none of it does.

On the stratum, normalized additive Haar probability gives this ball mass 2<sup>*s*+1−*t*</sup> in the admissible case. Indeed the normalized stratum is one class modulo 2<sup>*s*+1</sup>. The two signs double both numerator and denominator for all odd radices in that stratum. The density of the good classes among all positive integers is 2<sup>1−*t*</sup>, or 2<sup>2−*t*</sup> among the odd integers. These integer natural densities follow from periodicity at this fixed shell. Multiplicative Haar probability on the units gives the same relative proportions, since multiplication by an odd unit permutes the residue classes.

For the example *k* = 11, *s* = 2 and *H* = 0, the precision is *t* = 8. At the normalized radix 93, λ = −log(93) ≡ 44 modulo 256. Only the terms through degree three can contribute at this precision. They give

```math
F(44)\equiv 44+\frac{2\cdot44^2}{9}+\frac{44^3}{21}
\equiv 44+32+192\equiv12\pmod{256}.
```

Here 12 = *k* + 1, so the normalized class is 93 modulo 256, and negation gives 163.

## Fixing a radix and varying the shell

For a fixed *s* and *H*, the conditional Haar probabilities of the shell events have a convergent sum in *k*. The first Borel–Cantelli lemma gives finitely many hits for Haar-almost every normalized 2-adic radix of that stratum. Intersecting over integer *H* ≥ 0 shows *qₖ* → ∞ almost surely, where the denominator formula defines the profile at a 2-adic radix. The positive integer radices form a countable Haar-null set. This argument gives no individual integer-radix finiteness statement.

There is a deterministic sparsity statement for **every** fixed odd integer *b* ≥ 3. If two shells *k* < ℓ hit the same threshold and *tₖ* = *k* − 1 − *s(b)* − *H* > 0, both shell indices are congruent to κ(*b*) modulo 2<sup>*tₖ*</sup>. In particular

```math
\ell-k\ge 2^{k-1-s(b)-H}.
```

Thus these shell indices have natural density zero, even if there are infinitely many of them. Equivalently, *qₖ(b)* tends to infinity in density over **shell indices**. One can also see this by fixing any *d*: all sufficiently late hits lie in the single class κ(*b*) modulo 2<sup>*d*</sup>, which has index density 2<sup>−*d*</sup>. Neither argument weights a shell by its number of digit positions.

There is a sufficient arithmetic condition for eventual growth. If κ(*b*) = *a/d* is rational in lowest terms, then *d* is odd because κ(*b*) is 2-adically integral. Apart from the possible index with *dk* = *a*, one has 2<sup>*v*(*k*−κ)</sup> ≤ |*dk* − *a*| in the ordinary absolute value. The denominator formula gives *qₖ(b)* ≥ 2<sup>*k*−1−*s(b)*</sup>/|*dk* − *a*|, which tends to infinity. The isometry alone does not establish this rationality for any given *b*.

Infinite hits really do occur in the 2-adic parameter space. Within a fixed valuation stratum and for fixed *H*, the union of the target balls for *k* ≥ *K* is open and dense for every *K*. Every given subball contains arbitrarily large positive integers *k* + 1 of its prescribed residue, and eventually *tₖ* exceeds its defining precision. The intersection over *K* is therefore a dense Gδ by Baire's theorem, although it has Haar measure zero. Transporting it by the radix isometry proves the corresponding assertion for 2-adic radices. Whether a specified ordinary radix lies in this exceptional set requires additional arithmetic information about its phase.

## Evidence

The coefficient valuation, convergence estimates and bijective isometry of the series are kernel-verified. The arithmetic identification uses the actual slope and intercept and proves the isometry for the phases of any two odd integer radices ≥ 3. The finite residue theorem proves both the necessary target valuation and the exact two opposite classes for the actual prefix denominator. The density, sparsity and Baire-category statements are paper deductions. [Taylor series and isometry](../../NormalityChecker/ResonantRadixSeries.lean) · [Identification and radix-centre theorem](../../NormalityChecker/ResonantRadix.lean) · [Radix classes](../../NormalityChecker/ResonantRadixClasses.lean) · [Upper-shell arithmetic](../../NormalityChecker/ParameterTwoQuadratic.lean)

The finite checks compare log with the dyadic-power definition, verify the compatible quotient permutations through modulus 4096, evaluate the prefix directly at every upper position for 3 ≤ *b* ≤ 31 odd and 1 ≤ *k* ≤ 6, and check both signed classes across moduli 8 through 1024. For moduli through 128, the direct modular prefix check covers a full period of shell residues. For each larger modulus and stratum it covers 33 consecutive shells and the first admissible shell beyond the cutoff *H* ≥ 0. Run `python3 -B scripts/test_resonant_radices.py`. [Exact tests](../../scripts/test_resonant_radices.py)
