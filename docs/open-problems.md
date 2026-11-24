# Open problems and limitations

This page lists what the repository has **not** proved, with the strongest partial results and where they stop. A result that bounds discrepancy, certifies part of an orbit or checks a finite range is listed with its exact scope.

## Classical constants

**Normality of ln 2, π and *e*.** Open in every base. Nothing here settles it.

**A discrepancy bound below one.** For none of these constants, nor the golden ratio, is any bound *D*∞ < 1 known from this work. In particular **the binary bound *D*∞ ≤ 0.9999 for ln 2 remains open.**

What is proved points at the obstacle rather than past it.

- Binary discrepancy is below one exactly when digit transitions have positive lower density. For ln 2 the proved transition count grows only logarithmically. [Sharp transition theorem](../notes/transition-discrepancy.md) · [CC family](results.md#classical-constant-arithmetic)
- A mean first-frequency deficit of 0.0128 in each four sufficiently late dyadic shells would give *D*∞ ≤ 0.9999 for ln 2. No such deficit is known. [Moment and dyadic criteria](../notes/classical-discrepancy.md)
- The shifted denominators of every finite dyadic identity for ln 2 grow exponentially, at rate at least one half, so the fixed-support certificates do not apply. [Half-rate series and optimality](../notes/strided-logarithm.md) · [Classical-constant figure](figures.md#classical-denominator-growth)
- Exact finite computations cover initial segments: for example, finite certificates cover 888 of the first 1,024 positions of ln 2 in twelve-position blocks, and a sieve excludes low-transition words on finite windows. **Finite digit tests are not asymptotic progress.** [Coverage proofs and finite scope](../notes/intermittent-coverage.md) · [Sieve](../notes/sublinear-residue-windows.md)

**Restricted versus unrestricted logarithms.** The finite-support theorem ([LS-01](results.md#ls-01)) proves normality of Σ 1/(*m*ˢ*b*ᵐ) when *m* ranges over integers built from a *finite* set of primes. The ordinary series for ln 2 uses every positive integer. Normality on every finite support does not pass to the limit, and no uniform estimate of the required kind is known.

## Stoneham-type numbers

**The mixed-prime product.** The binary product with parameters 3 and 5 has upper discrepancy at most 27/40. Both top layers can be lost together for arbitrarily many depths. A proof of normality would have to control the remaining denominator throughout almost all positions. [All-prefix upper bound and local tests](../notes/phase13/independent-axes.md)

**Parameter two.** In odd radices the square and every rational polynomial of odd prime-power degree are covered. On the upper half-shell of a quadratic, linear and quadratic denominators can have equal order. For the polynomial *X*² − 2*X*, the additional loss can be arbitrarily large. Whether its denominators still grow sufficiently remains open. [Exact obstruction](../notes/phase13/reviews/symmetric-degree.md)

**Ternary normality of the binary Stoneham number.** Normality of α with *b* = 2 and *p* = 3 in base 3 is open. A paper proof gives superlinear growth of the number of distinct ternary words. [Ternary word complexity](../notes/ternary-stoneham-complexity.md)

**Rational functions and several independent generators.** [ST-01](results.md#st-01) covers polynomials in one Stoneham number, and [ST-04](results.md#st-04) covers combinations of products along one prime axis with a unique monomial of top degree. Rational functions such as 1/α, and general polynomials in Stoneham numbers on different prime axes, are not covered.

## Certificates and finite-support theory

**Finite termination.** On every unsigned full support with an off-base prime, the worst-prefix certificate tends to zero ([LS-03](results.md#ls-03)). Whether it reaches zero at a finite depth is proved for two-prime supports on paper and is open in general. A fixed mask has failures at all depths. [Finite-depth analysis](../notes/fixed-depth-question.md)

**Positive persistent mass on generalized supports.** Intermediate discrepancy occurs for signed, masked and weighted families. For unsigned full supports it is impossible. The classification of masked supports with nonmonomial polynomial denominators is incomplete. [Polynomial masks](../notes/polynomial-masks.md)

## Novelty and review

**Historical priority.** Each result has been compared with the literature known to the project (Stoneham; Korobov; Bailey and Crandall; Wagner; Kano and Shiokawa; Coons; Vandehey; Dibag; recent Stoneham-sum and localized-logarithm manuscripts), but a search that finds nothing does not establish novelty. [Literature comparisons](../notes/reviewers.md#relation-to-prior-work)

**Independent review.** The Lean kernel has checked the formal statements. Whether each formal statement captures the intended mathematics, and whether the written proofs are complete, needs review by mathematicians outside the project. None of the manuscripts has been peer reviewed. [Guide for mathematicians](guide-mathematicians.md) · [Guide for Lean reviewers](guide-formal-review.md) · [Contributing](../CONTRIBUTING.md)
