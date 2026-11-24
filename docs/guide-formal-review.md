# Guide for Lean reviewers

This guide is for readers who want to check that a formal statement says what the prose claims, and to reproduce the verification. Lean guarantees that proofs are correct relative to the definitions; this guide points at the definitions and conventions where a mismatch could hide.

## 1. Reproduce

Follow [docs/verification.md](verification.md). `scripts/verify.sh` builds the library, audits axioms, runs the manuscript statement checks, validates the declaration directory and the documentation, and replays every module through the kernel.

To inspect one declaration interactively, create a scratch file in the repository root:

```lean
import NormalityChecker
#check @NormalityChecker.StonehamPolynomial.prime_power_polynomial_normal
#print axioms NormalityChecker.StonehamPolynomial.prime_power_polynomial_normal
```

and run `lake env lean <file>`.

## 2. The definitions that carry the meaning

| Notion | Lean definition | Conventions to check |
| --- | --- | --- |
| Radix shift | [`shift`](../NormalityChecker/Basic.lean#L15) | `shift b x n = Int.fract (b ^ n * x)`; the first observation is *n* = 0 |
| Frequency | [`frequency`](../NormalityChecker/Basic.lean#L18) | proportion of 0 ≤ *n* < *N* with *a* ≤ *u n* < *c*; half-open intervals |
| Normality | [`NormalIn`](../NormalityChecker/Basic.lean#L23) | every word of every length *k* ≥ 1 has limiting frequency *b*⁻ᵏ, via the half-open cylinder [*m*/*b*ᵏ, (*m*+1)/*b*ᵏ); this selects the terminating expansion at radix rationals |
| Interval discrepancy | [`radixDiscrepancy`](../NormalityChecker/BinaryDiscrepancy.lean#L11) | supremum over 0 ≤ *a* < *c* ≤ 1 of the absolute frequency error; *D*∞ is `limsup … atTop` |
| Stoneham number | [`StonehamPolynomial.alpha`](../NormalityChecker/StonehamPolynomial.lean#L41) | sum over *j* ≥ 0 of 1/(*p*^(*j*+1) *b*^(*p*^(*j*+1))), i.e. the classical series from index 1 |
| Finite-support polylogarithm | [`powerValue`](../NormalityChecker/SmoothCertificates.lean#L44) | coefficient 1/*m*ˢ at every *m* ≥ 1 whose prime factors lie in *S* (including *m* = 1); position *m* is digit *m* |
| Signed shell expansion | [`SignedPhases.value`](../NormalityChecker/SignedPhases.lean#L19) | *a*₀ = *c*₀, *a*ⱼ₊₁ = *c*ⱼ₊₁ − *p c*ⱼ; term *a*ⱼ/(*p*ʲ *b*^(*p*ʲ)) from *j* = 0 |
| Weighted and masked supports | [`maskedValue`](../NormalityChecker/MaskedSeries.lean#L86) | the mask selects indices; the polynomial weight is evaluated at the index |

Some families have several equivalent definitions in different developments. Where they are identified, the identification is a theorem or `rfl`: for example the [Paper I check](../papers/01-stoneham-polynomials/check.lean) proves `StonehamStatements.stoneham = StonehamPolynomial.alpha` by `rfl` and checks the starting index across three developments.

## 3. Minimal statement modules

For the two principal papers, statement modules restate the main theorems using only Mathlib definitions, so a reviewer can read the statement without the rest of the library:

- [NormalityChecker/StonehamStatements.lean](../NormalityChecker/StonehamStatements.lean): polynomial normality and joint uniformity of Stoneham powers, proved in [StonehamJoint.lean](../NormalityChecker/StonehamJoint.lean) (`polynomial_statement_checked`, `joint_statement_checked`).
- [papers/02-localized-normality/Statements.lean](../papers/02-localized-normality/Statements.lean) and [Check.lean](../papers/02-localized-normality/Check.lean): the finite-support classification in Mathlib-only terms.

## 4. A checklist for each principal statement

For each entry of the [result index](results.md) marked *Lean*:

1. Open the first Lean link and read the hypotheses. Compare them with the *Statement* and *Scope* fields.
2. Check degenerate cases: empty support, the zero polynomial, *b* dividing a power of *p*, *p* = 2, constant phases, prefix length 0.
3. Check the indexing: does the series start at 0 or 1; is position 0 observed; are intervals half-open?
4. Check that the conclusion is the claimed one: `NormalIn` versus a statement about one block length; `limsup` versus `Tendsto`; an upper bound versus an equality.
5. Confirm the declaration is in [Audit.lean](../Audit.lean) or in a paper check file, or run `#print axioms` yourself.

Entries marked *Lean + written deduction* name the deduction and its external inputs; the Lean part is listed first.

## 5. Finding declarations

- The [complete directory](theorems.md) lists all public theorems by topic and module with docstring summaries.
- [declarations.json](data/declarations.json) gives, for every theorem, its fully qualified name, module, file, line range and docstring. It is regenerated from the compiled environment, so line numbers are exact.
- Source links in the indexes point to current files; the [result index](results.md) also gives Checkpoint 11 permalinks.

## 6. Reporting a problem

A mismatch between a formal statement and its description is a serious error even when the proof is correct. Please report it with the [correction template](../.github/ISSUE_TEMPLATE/correction.md), quoting the result identifier and the declaration.
