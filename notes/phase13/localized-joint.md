# Distinct localized orders on one support

**Theorem (Paper II, Corollary 1.3).** Let *b* ≥ 2 be an integer and *S* a finite set of primes. Let *M(S)* consist of the positive integers whose prime factors belong to *S*, including 1. Suppose some *p* ∈ *S* does not divide *b*. For each positive integer *s*, put

```math
X_s=\sum_{m\in M(S)}\frac{1}{m^s b^m}.
```

Choose any finite list of distinct positive orders $s_1,\ldots,s_d$. At position *n*, put $x_i(n)=\{b^nX_{s_i}\}$, where braces denote fractional part. For every box with 0 ≤ *a*ᵢ ≤ *c*ᵢ ≤ 1 in each coordinate, the proportion of positions 0 ≤ *n* < *N* for which *a*ᵢ ≤ *x*ᵢ(*n*) < *c*ᵢ for **every** *i* tends to

```math
\prod_{i=1}^d(c_i-a_i).
```

One off-radix prime suffices, even when the other primes in *S* divide *b*. The public statement defines both the series and the common position count using only mathlib. Its proof identifies the positive-index series with the library's localized polylogarithm. [Independent statement](../../NormalityChecker/LocalizedJointStatements.lean) · [Lean proof](../../NormalityChecker/LocalizedJoint.lean) · [Paper II](../../papers/02-localized-normality/paper.pdf)

For example, take *b* = 10, *S* = {2, 3, 5}, and the three orders 4, 1, 3 in that order. The box [1/4, 1/2) × [0, 1) × [1/2, 3/4) has limiting frequency 1/16. Repeating an order would put a pair of coordinates on the diagonal. The box [0, 1/2) × [1/2, 1) would then have zero visits at every cutoff despite its area of 1/4. Both counts have Lean checks. If every support prime divides *b*, even one positive-order coordinate has interval discrepancy tending to one. Order zero also gives a nonnormal unsigned coordinate by the polynomial classification. [Worked checks](../../scripts/test_localized_joint.lean) · [All-radix case](../../NormalityChecker/UnsignedNormality.lean) · [Pole criterion](../../NormalityChecker/FullPolynomialNormality.lean)

## From one pole to a rectangle

More generally, give coordinate *i* the rational weight $P_i(m)/m^{s_i}$ on the same support, where *P*ᵢ is a polynomial over the rationals, *P*ᵢ(0) ≠ 0, and the positive pole orders are distinct. This permits negative coefficients and unrestricted numerator degrees. Fix a nonzero integer vector *h*. Let *I* contain the indices where *h*ᵢ ≠ 0, and let *t* be the largest order among these indices. With the common denominator *m*ᵗ, the numerator is

```math
Q(X)=\sum_{i\in I}h_i X^{t-s_i}P_i(X).
```

Exactly one summand contributes to *Q*(0). At the unique index *j* of order *t* it gives *h*ⱼ*P*ⱼ(0) ≠ 0. For instance, with the orders 4, 1, 3 above, unit numerators, and *h* = (0, −2, 1), the common denominator has order 3 and *Q*(*X*) = 1 − 2*X*². Absolute convergence allows the finite sum of series to be collected term by term. The resulting scalar series has a pole at zero and is base-*b* normal by the full-support scalar classification. [Collection of the character and polynomial theorem](../../NormalityChecker/LocalizedJoint.lean) · [Scalar classification](../../NormalityChecker/FullPolynomialNormality.lean)

The torus character indexed by *h* at the *n*th vector is the complex exponential $e^{2\pi i b^n y}$, where *y* is this scalar sum. Taking fractional parts in the coordinates leaves the character unchanged. Scalar normality makes every nonconstant character average tend to zero. The constant character averages to one. Trigonometric polynomials are uniformly dense in the continuous functions on the torus, so continuous averages converge to Haar integrals. For each side of a box, bound its indicator above and below by continuous functions differing only near the endpoints. Their products bound the box indicator, and their integrals tend to the product of the side lengths. This proves the half-open rectangle statement, including sides of length zero or one. The same Lean theorem supplies this step for the existing Stoneham power result. [General Weyl proof](../../NormalityChecker/JointWeyl.lean) · [Stoneham application](../../NormalityChecker/StonehamJoint.lean)

## Common masks

On a single prime-power axis *M*({*p*}), retain an arbitrary common set of exponents. For *p* ∤ *b* and a nonempty vector with the polynomial numerators and orders above, **joint uniformity holds exactly when the retained exponents are unbounded**. The character calculation still gives the same *Q* on every retained index. The scalar infinite-axis theorem applies even if the gaps between retained exponents grow arbitrarily large. Conversely, a joint limit gives scalar normality by taking a digit cylinder in one coordinate and the full interval in all the others. A finite mask gives a rational value in that coordinate. The tests include the exponents 1, 2, 4, 8, … with two different signed polynomial numerators. [Joint mask classification](../../NormalityChecker/LocalizedJoint.lean) · [Scalar axis theorem](../../NormalityChecker/MaskAxis.lean) · [Worked mask](../../scripts/test_localized_joint.lean)

A second kernel result allows a mixed support and an odd radix. If 2 belongs to *S* and the common mask retains every sufficiently large power of two, all other smooth indices may be retained or discarded arbitrarily. The scalar window theorem applies to *Q* for each character. For larger selected primes the analogous scalar first-window estimate can leave a positive discrepancy bound. [Vector theorem](../../NormalityChecker/LocalizedJoint.lean) · [Window bounds](../../NormalityChecker/MaskWindows.lean)

There cannot be a cutoff for a prescribed frequency error that is uniform over all unbounded masks, even for one coordinate. Given any *N*, retain only the powers *p*ᵏ with *k* ≥ *K*, where *p*ᴷ ≥ *N* + 2. For 0 ≤ *n* < *N*, the shifted unsigned order-one sum is bounded above by the sum of $b^{n-m}$ over all integers *m* ≥ *p*ᴷ. This is at most 2*b*⁻³ ≤ 1/4. Every one of the first *N* shifts lies in [0, 1/2), and every such tail mask still gives a normal number. This uniform-cutoff obstruction follows directly from the geometric bound and the axis theorem.

## What can be computed in certificate depth

Fix one off-radix prime *p*, a finite set of positive orders *T*, and a positive rational tolerance ε. At depth *k* the checker works modulo *p*ᵏ⁺¹, on cells of width *p*⁻ᵏ in [1, *p*). Write *Z*ₛ(*k*) for the set of failed cells of order *s*. An executable Lean function searches increasing depths until every order in *T* satisfies

```math
\frac{2\,|Z_s(k)|}{p^k}<\varepsilon.
```

The failed regions are nested under refinement. Their lengths tend to zero by the unsigned nullity theorem. Since *T* is finite, the search terminates. The worst-prefix certificate at every finer depth is bounded by twice the length at the reported depth. Thus this algorithm computes a modulus for the **finite certificates**. Its input and output concern precision. The Weyl proof above gives a limiting frequency for each rectangle and supplies no computable digit-position cutoff *N* in terms of this depth. [Executable search and proof](../../NormalityChecker/LocalizedCertificateModulus.lean) · [Nullity and worst-prefix bound](../../NormalityChecker/UnsignedNormality.lean)

For *b* = 4, *S* = {2, 3, 11}, *p* = 3, *T* = {1, 2}, and ε = 9/10, the search returns *k* = 2. At that depth the order-one failed region is [2, 22/9), so twice its length is 8/9 and the exact worst-prefix certificate is 3/11. The order-two failed region is empty. The positive-tolerance search therefore succeeds while the order-one test still has failed cells. [Kernel arithmetic checks and executable evaluation](../../scripts/test_localized_joint.lean) · [Exact cell checker](../../scripts/localized_certificate.py)

Requiring **every** cell to pass at some precision is a different termination question. The repository's paper argument gives finite termination on full two-prime supports and at all sufficiently large orders for fixed selected *p*. At small orders with several cofactor primes, the general full-support question remains open here. A fixed cofactor mask in the existing notes fails at every precision. Its construction uses a restricted support. [Finite-termination arguments and fixed mask](../fixed-depth-question.md)

## Rational functions with controlled denominator primes

Write a rational function after clearing coefficient denominators as $A(X)/(X^u G(X))$, with integer polynomials *A*, *G*, with *G*(0) ≠ 0, and with *A*, *G* coprime over the rationals. On the whole axis *m* = *p*ᵏ, a fixed finite set contains every prime of every **reduced coefficient denominator** if and only if *G* is constant. If *G* is nonconstant, new denominator primes occur at arbitrarily late exponents where *G*(*p*ᵏ) ≠ 0. The finitely many singular evaluations may be omitted. For example, *A* = 1, *u* = 1, *G*(*X*) = *X* + 1 escapes every finite set already on the dyadic axis. The proof concerns denominator support. It leaves the normality of that example undecided. [Denominator theorem](../../NormalityChecker/LocalizedDenominatorPrimes.lean) · [Dyadic example](../../scripts/test_localized_joint.lean)

Here is the prime-divisor argument. Given a finite set of primes *E*, choose *j* with *G*(*p*ʲ) ≠ 0, then an integer *L* larger than both |*G*(0)| and |*G*(*p*ʲ)|. Take *M* to be the product of *q*ᴸ over *q* ∈ *E* other than *p*. Along exponents *k* = *j* + φ(*M*)*v*, Euler's theorem gives *p*ᵏ ≡ *p*ʲ modulo *M*. Once *k* ≥ *L*, we also have *p*ᵏ ≡ 0 modulo *p*ᴸ. No *q*ᴸ with *q* ∈ *E* divides *G*(*p*ᵏ) on this tail. If all its prime factors belonged to *E*, its absolute value would be bounded by the product of those prime powers. A nonconstant polynomial is unbounded in absolute value along this progression, giving the contradiction.

To account for reduction of fractions, clear the denominators in a polynomial Bézout identity for *A* and *G*. Every common prime divisor of their values divides a single fixed nonzero integer *D*. Include those primes in *E*. A new prime dividing *G*(*p*ᵏ) survives in the reduced denominator of the rational coefficient. Conversely, for constant *G*, the primes dividing its value together with *p* suffice. Every nonempty full smooth support contains a whole prime-power axis, so the same obstruction applies there. For constant *G* the rational functions are Laurent polynomials, and the distinct positive pole orders are covered by the joint theorem above. [Kernel proof](../../NormalityChecker/LocalizedDenominatorPrimes.lean)

## Signed periodic weights on one axis

At order one, allow the numerator *H*(*m* mod *d*) to be any rational residue weight, with *d* ≥ 1, and retain all *m* = *p*ʲ. Choose a preperiod *J* and a positive period *L* of *p*ʲ modulo *d*. At each residue *z* on its eventual cycle compute

```math
W(z)=\sum_{r=1}^{L}p^{L-r} H(p^r z).
```

For *p* ∤ *b*, the sparse sum is base-*b* normal exactly when every such *W*(*z*) is nonzero. To see the reduction, put *A*(*z*) = *H*(*z*) − *H*(*z* + 1) / *b*. Telescoping its radix-discounted period recovers *H* as the periodic antidifference. The existing dense-series identity then expresses that series as a rational translate of (1 − *p*) times the sparse series. Normality is invariant under these operations, and the dense cycle criterion gives the stated finite test. [Sparse periodic classification](../../NormalityChecker/LocalizedSignedAxis.lean) · [Dense cycle theorem](../../NormalityChecker/PeriodicClassification.lean)

In base 2 with *p* = 3 and *d* = 4 the power cycle is 1, 3. Weights *H*(1) = 1 and *H*(3) = −1 give window values −2 and 2, hence a normal sum. Changing the second weight to −3 gives window values −8 and 0, hence a nonnormal sum although every supported coefficient is nonzero. The signs and magnitudes affect cancellation. This classification covers one axis at order one. [Positive and negative checks](../../scripts/test_localized_joint.lean)

## Earlier results and verification

Mira's S09, Theorem 1, treats the full unsigned scalar series when all support primes are coprime to the radix. S09, Theorem 2, gives joint uniformity for distinct prime/order pairs on singleton supports. Its fixed-prime specialization overlaps the present corollary. Corollary 1.3 of Paper II instead keeps the entire finite support fixed across the coordinates and permits radix primes in that support. The Lean development verifies that corollary as stated. [Mira, S09](https://gist.github.com/Mira-acc/ea2791119de611279237096e35cbc976/d699a69c2037ee4420bfb8e1e0ad0b310bbc8eb0) · [Paper II](../../papers/02-localized-normality/paper.pdf)

For scalar order one on a singleton, the extra term at *m* = 1 differs from the usual Stoneham series by 1/*b*. Bailey and Crandall treat coprime Stoneham parameters. Vandehey's Theorem 7.4 covers scalar unsigned positive orders on arbitrary infinite restrictions of one coprime prime-power axis. Two incomparable support primes preclude that divisibility-chain argument on a full mixed support. The earlier binary {2, 3} localized-logarithm manuscript gives a quantitative order-one estimate for that particular support. [Bailey–Crandall, Corollary 4.9](https://doi.org/10.1080/10586458.2002.10504704) · [Vandehey, Theorem 7.4](https://arxiv.org/abs/1606.07911) · [Earlier localized-logarithm manuscript](https://github.com/CaptainSude/xi-normality/blob/06961817c7f61181ed9a5c73badb8d908d6ccdcc/paper/localized-logarithm-normality.pdf)

To replay the examples and the axiom check from the project root, run

```sh
lake build NormalityChecker.LocalizedJoint NormalityChecker.LocalizedCertificateModulus NormalityChecker.LocalizedDenominatorPrimes NormalityChecker.LocalizedSignedAxis NormalityChecker.StonehamJoint
lake env lean scripts/test_localized_joint.lean
```

The audit checks the localized results and the original Stoneham joint statement against the axioms `propext`, `Classical.choice`, and `Quot.sound`. [Test and audit source](../../scripts/test_localized_joint.lean)
