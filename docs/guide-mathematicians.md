# Guide for mathematicians

This guide explains how to check one result from this repository without reading anything else, and suggests an order for each family.

## Checking a single result

1. **Find the identifier.** The [curated result index](results.md) lists every major result by topic with a permanent identifier such as ST-01. The README states the three principal theorems in full.
2. **Read the statement and its scope.** Each entry gives the exact hypotheses and, under *Scope*, the conventions and what is not claimed. The *Evidence* line says whether the conclusion is a Lean theorem, a Lean core with a written deduction, a written proof, or an exact finite computation.
3. **Read the proof.** The *Proof* links go to the research notes, which are complete written proofs with worked examples. The manuscripts in [papers/](../papers/README.md) give the same proofs in conventional form, with each paper's reviewer guide (`REVIEW.md`) listing the points that most need checking.
4. **Check the literature.** The [comparison with prior work](../notes/reviewers.md#relation-to-prior-work) records the closest results known to the project and what each one covers. Priority has not been established.
5. **Check the formal statement, if you wish.** The *Lean* links open the declaration at its source line. The [guide for Lean reviewers](guide-formal-review.md) explains the definitions behind the statements.
6. **Report.** A correction, a missing hypothesis or an earlier reference is most useful as a [GitHub issue](../CONTRIBUTING.md) quoting the identifier.

## Suggested reading by family

**Stoneham polynomial images (Paper I).** Start with Theorem I in the README, then the [proof for all degrees](../notes/stoneham-powers-products.md), which explains the upper-orthant generating function and the congruence *K*(*p*) ≡ 1 (mod *p* − 1). The [square note](../notes/stoneham-square.md) works the case of degree two in full and gives exact denominators. Then [ST-01 to ST-06](results.md#stoneham-polynomial-images-and-products) and the [Paper I directory](../papers/01-stoneham-polynomials).

**Finite prime supports (Paper II).** Start with Theorem II, then [persistent discrepancy](../notes/persistent-discrepancy.md) for the exact formula with one off-base prime, [higher-order joint failures](../notes/higher-order-joint.md) for all orders, and the [nullity proof](../notes/unsigned-finite-support.md). The [order-two counterexample](../notes/joint-persistent.md#higher-orders-and-the-lower-order-residues-paper-proof) explains why a naive argument fails. Polynomial weights and masks are in [polynomial-masks.md](../notes/polynomial-masks.md). Then [LS](results.md#localized-logarithms-and-polylogarithms) and [MW](results.md#polynomial-weights-and-masked-supports) and the [Paper II directory](../papers/02-localized-normality).

**Signed expansions and resonance (Paper III).** The [cyclotomic classification](../notes/reviewers.md#finite-combinations-of-stoneham-type-components) shows how resonance arises in finite combinations. Then [signed shells](../notes/signed-shell-discrepancy.md), [rational translations](../notes/translated-shells.md) and the [spectrum](../notes/attainable-shell-histories.md), and [CR and DS](results.md#exact-discrepancy-and-symbolic-spectra).

**Certificates (Paper IV).** [Polynomial certificates](../notes/polynomial-certificates.md), [overlapping certificates](../notes/overlapping-certificates.md), [coverage](../notes/intermittent-coverage.md) and [limits of smooth models](../notes/finite-support-discrepancy.md#how-far-polynomial-denominator-models-can-reach). Several components are standard tools in a new arrangement; the index says which are new applications.

**Classical constants (Paper V).** [The half-rate series and its optimality](../notes/strided-logarithm.md), then [corrected models](../notes/corrected-strides.md) and the [transition criterion](../notes/transition-discrepancy.md). These results describe the arithmetic of approximations; they prove nothing about normality of ln 2, π or *e*. The [open problems](open-problems.md) state exactly what is missing.

## What to look for

- **Scope of each conclusion.** Normality, exact discrepancy, an upper bound and partial coverage are different statements. The [framework page](framework.md#strength-of-a-conclusion) defines each.
- **External inputs.** Some deductions use Roth's theorem, Ridout's theorem, Bang's primitive-divisor theorem, the prime number theorem or published digit-change estimates. They are named in the *External inputs* field.
- **Finite computations.** Exact computations over finite ranges illustrate or check statements but do not establish limits.
