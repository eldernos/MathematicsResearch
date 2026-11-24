# Rational polynomials of Stoneham numbers with a composite parameter

Let *b* ≥ 2 and *c* > 2 be coprime integers. Define the positive-index Stoneham number by

```math
\alpha_{b,c}=\sum_{j=1}^{\infty}\frac{1}{c^j b^{c^j}}.
```

**Theorem.** For every nonconstant rational polynomial *P*, the real number
*P*(α<sub>*b*,*c*</sub>) is normal in base *b*. Thus every word of length *m* occurs with limiting frequency
*b*<sup>−*m*</sup> in its fractional digits. The argument applies to prime and composite *c*.

**Formal scope.** Lean verifies the theorem whenever there is a prime *p* dividing *c* for which
the inverse radix powers converge to a unit in ℚ<sub>*p*</sub>. This includes every even *c* > 2.
It verifies the retained denominator bound in this case for products with arbitrary positive
strides and radix dilations, and normality for rational combinations with one strictly highest-degree
monomial. The proof for cycles of length greater than one, given below, concerns univariate
polynomials. [Independent statements](../../NormalityChecker/CompositePolynomialStatements.lean) ·
[Unit-limit and even-parameter proofs](../../NormalityChecker/CompositePolynomial.lean) ·
[Product and sum theorem](../../NormalityChecker/StonehamPolynomial.lean) ·
[Paper I and its original scope](../../papers/01-stoneham-polynomials/paper.pdf)

## The constant local unit

Fix a prime *p* dividing *c* and write *a* = *v*<sub>*p*</sub>(*c*). Work first with a power
of degree *d* ≥ 1. For a position *n*, put *k* = ⌊log<sub>*c*</sub> *n*⌋ and *t* = *n*/*c*<sup>*k*</sup>.
The shifted rational prefix *R*<sub>*n*</sub> contains the terms of the expanded power
with insertion position *s*(*j*) = ∑ᵢ *c*<sup>*j*ᵢ</sup> ≤ *n*, multiplied by *b*<sup>*n*</sup>.
All indices *j*ᵢ are positive and at most *k*. Reflect by *v*ᵢ = *k* − *j*ᵢ. Set

```math
U_t=\left\{v\in\mathbb N^d:\sum_i c^{-v_i}\le t\right\}.
```

This is an upper set for the coordinatewise order. All these sets contain one fixed constant
vector (*J*, …, *J*) with *d* ≤ *c*<sup>*J*</sup>. Write |*v*| = ∑ᵢ *v*ᵢ. After multiplying
the prefix by *c*<sup>*dk*</sup>*b*<sup>−*n*</sup>, each actual tuple contributes
*c*<sup>|*v*|</sup> ∏ᵢ *b*<sup>−*c*<sup>*k*−*v*ᵢ</sup></sup>. At precision *p*<sup>*L*</sup> only |*v*| < *L* matters.
For large enough *k* every such tuple has positive original indices.

If *b*<sup>−*c*<sup>*j*</sup></sup> converges to a unit, its residues at any fixed precision eventually coincide.
The same unit factor therefore multiplies every remaining tuple. For any nonempty upper set *U*,
Dickson's lemma gives finitely many minimal vertices and inclusion–exclusion gives

```math
\sum_{v\in U}c^{|v|}=\frac{K_U(c)}{(1-c)^d},\qquad K_U(1)=1,\qquad K_U\in\mathbb Z[X].
```

This identity holds in ℚ<sub>*p*</sub>. Since *K*<sub>*U*</sub>(*c*) ≡ 1 modulo *c* − 1 and *c* > 2,
its numerator is nonzero. The integer *c* used in this congruence can be composite even when the
valuation is at *p* = 2. For even *c*, *b* is odd, and φ(2<sup>*L*</sup>) divides *c*<sup>*j*</sup>
for all large *j*. Euler's theorem gives limit 1 in ℚ₂. The same upper-set argument with weights
*e*ᵢ uses ∏ᵢ(1 − *c*<sup>*e*ᵢ</sup>) as denominator. [Orthant lemma and compactness](../../NormalityChecker/StonehamPolynomialOrthant.lean) ·
[Retained prime powers](../../NormalityChecker/StonehamPolynomialPrefix.lean)

## The periodic unit at an arbitrary divisor

Take any prime *p* dividing *c*. Let ω be the Teichmüller lift of *b*⁻¹ modulo *p*
(take ω = 1 at *p* = 2). Its order *m* divides *p* − 1. Write *b*⁻¹ = ω(1 + *p z*) in ℤ<sub>*p*</sub>.
Raising a principal unit congruent to 1 modulo *p*<sup>*s*</sup>, *s* ≥ 1, to the *p*th power
gives 1 modulo *p*<sup>*s*+1</sup> by the binomial theorem, including at 2. Thus

```math
 b^{-c^j}\equiv \omega^{c^j}\pmod {p^{1+aj}}.
```

Repeated multiplication by *c* modulo *m* is eventually periodic. More explicitly, factor
*m* = *m*₀*m*₁, where every prime of *m*₀ divides *c* and gcd(*m*₁,*c*) = 1.
For large *j* the residue of *c*<sup>*j*</sup> is zero modulo *m*₀, and modulo *m*₁ it has period
*h* = ord<sub>*m*₁</sub>(*c*), with *h* = 1 for *m*₁ = 1.
In particular the unit-limit hypothesis is equivalent to *m*₁ dividing *c* − 1.
Indeed distinct powers of ω have distinct reductions modulo *p*, while the principal-unit
factor tends to one. [Teichmüller lift in Lean](../../NormalityChecker/CyclotomicLift.lean)

Fix one residue class of *k* modulo *h*. For *v* ≥ 0 put *u*<sub>*v*</sub> = ω<sup>*c*<sup>*j*</sup></sup>,
using any sufficiently large *j* ≡ *k* − *v* modulo *h*. These coefficients lie in the
number field *K* = ℚ(ω) inside ℚ<sub>*p*</sub> and repeat with period *h*.
At a fixed precision the reflected numerator agrees, for all sufficiently large *k* in this class,
with the following convergent sum over *U* = *U*<sub>*t*</sub>:

```math
 H(U)=\sum_{v\in U}\prod_{i=1}^d c^{v_i}u_{v_i}.
```

The error estimate is uniform in *n* on the shell. Every retained coordinate has *v*ᵢ < *L*,
so *k* − *v*ᵢ eventually exceeds both the preperiod and the threshold for the principal-unit congruence.

## Why a periodic mass cannot vanish

The one-dimensional sum splits into its *h* exponent classes. In ℚ<sub>*p*</sub> it equals
the image of the following element of *K*:

```math
 S=\sum_{v\ge0}c^v u_v=\frac{\sum_{r=0}^{h-1}c^r u_r}{1-c^h}.
```

Every complex embedding σ of *K* takes the coefficients to roots of unity. The last term
of the numerator has absolute value *c*<sup>*h*−1</sup>, strictly greater than the sum of
the absolute values of its predecessors. Consequently

```math
 0<|\sigma(S)|\le\frac{1+c+\cdots+c^{h-1}}{c^h-1}
 =\frac{1}{c-1}<1.
```

The field norm of *S* has absolute value strictly between zero and one. A nonzero algebraic
integer has nonzero integer norm, so *S* is not integral over ℤ.

For *a* ≥ 0, put *B*<sub>*a*</sub> = ∑<sub>*v* < *a*</sub> *c*<sup>*v*</sup>*u*<sub>*v*</sub>.
This is an algebraic integer. The mass of the orthant with vertex *a* ∈ ℕ<sup>*d*</sup> is
∏ᵢ(*S* − *B*<sub>*a*ᵢ</sub>), by convergence of the geometric tails. If *a*₁, …, *a*ₛ
are the minimal vertices of *U*, let *a*<sub>*I*</sub> be their coordinatewise maximum over the
nonempty index subset *I*. Inclusion–exclusion now gives *H*(*U*) = *F*<sub>*U*</sub>(*S*) for

```math
 F_U(X)=\sum_{\varnothing\ne I\subseteq\{1,\ldots,s\}}
 (-1)^{|I|+1}\prod_{i=1}^d\bigl(X-B_{(a_I)_i}\bigr).
```

All coefficients belong to the ring of integers of *K*. The leading coefficient is
∑<sub>*r* = 1</sub><sup>*s*</sup>(−1)<sup>*r*+1</sup> binom(*s*,*r*) = 1 since *s* ≥ 1.
If the mass vanished in ℚ<sub>*p*</sub>, it would vanish in *K*, making *S* integral over
its ring of integers and hence over ℤ. This proves nonvanishing for every nonempty upper
set, in every shell class. The identical one-dimensional cycle in all coordinates is
the reason a **single** monic polynomial suffices for powers of one generator.

For example, take *b* = 2 and *c* = 35. At *p* = 5 the inverse radix has order 4 and
35 ≡ −1 modulo 4. At *p* = 7 its order is 3 and 35 ≡ −1 modulo 3. Neither prime
gives a constant cycle. At 5, choosing even *k* gives *u*<sub>*v*</sub> = (−1)<sup>*v*</sup>ω,
where ω² = −1. The full sum is ω/36. For *d* = 2 and 1 + 1/35 ≤ *t* < 2 the cut omits
only the origin, so its mass is (*ω*/36)² − ω² = 1295/1296, with 5-adic valuation one.
Every nonconstant rational polynomial in α₂,₃₅ is binary normal by the periodic argument.

## Uniform denominator growth and the normality criterion

In each of the finitely many shell classes there is a single *L* for which every upper set containing
the anchor has nonzero mass modulo *p*<sup>*L*</sup>. Otherwise take a sequence of failing upper sets
with precision tending to infinity. Their indicators have a subsequence eventually constant at
each vector, by diagonal extraction on ℕ<sup>*d*</sup>. The limit is an upper set containing the anchor.
At each fixed precision only finitely many terms contribute, so the limiting mass is zero at
every precision. This contradicts nonvanishing. Take the maximum of the finitely many precision
bounds over the shell classes.

The reduced denominator of *R*<sub>*n*</sub> divides *c*<sup>*dk*</sup>. Its *p*-valuation is at
least *adk* − *O*(1) on all sufficiently late shells. Multiplication by a fixed nonzero integer
changes this lower bound by at most the valuation of the multiplier. Clear coefficient denominators
in *P*. The lower-degree part has denominator dividing *c*<sup>(*d*−1)*k*</sup>, so its pole at
*p* is strictly smaller for large *k*. The combined reduced denominator therefore tends uniformly
to infinity, has fixed prime support dividing *c*, and is at most *n*<sup>*d*</sup>.

The remaining estimates apply without change for composite *c*. The shifted real tail tends to
zero by dominated convergence, with dominating weights ∏ᵢ *c*<sup>−*j*ᵢ</sup>. Only
*O*((1 + log *N*)<sup>*d*</sup>) insertions occur up to position *N*. Blocks of length ⌊√*N*⌋
meeting an insertion cover *o*(*N*) positions; on each other block the prefix follows an exact
radix orbit. The fixed-support short-orbit estimate applies because the reduced denominator is
polynomially bounded in the block length and all its prime factors are coprime to *b*. Weyl's
criterion gives normality and rational scaling restores the original coefficients.
[Shifted tail](../../NormalityChecker/StonehamPolynomialExpansion.lean) ·
[Short-orbit estimate](../../NormalityChecker/SmoothOrbit.lean) ·
[Arithmetic certificate](../../NormalityChecker/ArithmeticCertificate.lean)

At *c* = 2 the full one-dimensional sum with constant unit 1 equals −1. The square cut omitting
only the origin then has mass zero. The proof above uses *c* > 2 essentially.
