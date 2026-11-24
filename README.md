# Normality certificates for arithmetic expansions

**Theorem (maximal discrepancy for finite prime supports).** Let *b* ≥ 2 and *s* ≥ 1 be integers, and let *P* be a finite set of primes. Let *S* consist of 1 and all larger integers whose prime divisors belong to *P*. Define

```math
X = \sum_{m \in S} \frac{1}{m^s b^m}.
```

For each *N*, take the fractional parts of the first *N* radix shifts of *X*, starting with *X* itself. Their interval discrepancy is the supremum, over half-open intervals in [0, 1), of the absolute difference between the observed frequency and the interval length. Write *D* for the limit superior of these discrepancies as *N* tends to infinity.

**Then *D* = 1 if and only if every prime in *P* divides *b*.** Each prime *p* in *P* that does not divide *b* gives the bound

```math
D \le 1 - \frac{1}{p-1}.
```

In particular, if 2 belongs to *P* and *b* is odd, then *X* is normal in base *b*. [Formal theorem](NormalityChecker/MaximalSupport.lean) · [Proof and examples](notes/finite-support-discrepancy.md)

## From a modular test to exact discrepancy

At each precision the checker partitions the digit positions into intervals. On a passing interval, a prime power survives in the reduced denominator of a rational prefix. Cancellation in the resulting modular orbit controls the digit frequencies there. Counting the remaining positions up to each possible endpoint gives a rational upper bound on *D*. Several primes can certify the same position. Only positions where all their tests fail count toward the bound. [Certificate theorem](NormalityChecker/DiscrepancyChecker.lean) · [Overlapping certificates](notes/overlapping-certificates.md)

When *s* = 1 and exactly one prime *p* in *P* does not divide *b*, the bounds converge to the exact discrepancy. In the normalized scale [1, *p*), let *Z* be the set of positions that fail the modular test at every precision. Let *L*(*t*) be the length of the part of *Z* between 1 and *t*. Then

```math
D = \max_{1 \le t \le p} \frac{L(p)/(p-1) + L(t)}{t}.
```

Thus *X* is normal in base *b* exactly when *Z* has measure zero. [Formal theorem](NormalityChecker/PersistentRegion.lean) · [Proof of the exact formula](notes/persistent-discrepancy.md)

## Other results

- **Finite sums of Stoneham-type numbers.** For rational coefficients, a finite cyclotomic divisibility test decides normality in the construction base. The examples include pairs of normal summands whose sum is nonnormal. [Classification](NormalityChecker/CyclotomicClassification.lean) · [Executable test](NormalityChecker/CyclotomicTest.lean)
- **Normality from rational approximations.** A general certificate transfers cancellation from rational radix orbits to digit frequencies. Its applications include localized polylogarithms, dense polynomial weights, periodic coefficients and sparse perturbations. [General theorem](NormalityChecker/ArithmeticCertificate.lean) · [Results and worked examples](notes/results.md)
- **Classical constants.** Polynomial integral identities give rational models for shifts of ln 2 and π. For the golden ratio, binary discrepancy below one is equivalent to a positive lower density of powers of two with a bounded least Zeckendorf index. A strict asymptotic discrepancy bound for any of these three constants remains open here. [Models and finite experiments](notes/complementary-models.md) · [Classical discrepancy questions](notes/classical-discrepancy.md)

## Reproduce and review

[![Lean verification](https://github.com/eldernos/MathematicsResearch/actions/workflows/lean.yml/badge.svg)](https://github.com/eldernos/MathematicsResearch/actions/workflows/lean.yml)

The repository pins Lean and Mathlib to v4.36.0. With Elan installed, run these commands from the repository root.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get $(sed -nE 's/^(public )?import (Mathlib\.[A-Za-z0-9_.]+)$/\2/p' NormalityChecker/*.lean NormalityChecker/Analysis/*.lean | sort -u)
scripts/verify.sh
```

Verification runs the exact-arithmetic tests, builds the library, audits the listed theorems for transitive axioms, and replays the project modules through the Lean kernel. The audit permits `propext`, `Classical.choice` and `Quot.sound`. The exact-discrepancy checkpoint at `8bf9f04` is preserved as `research-checkpoint-8`. [Axiom audit](Audit.lean) · [Verification workflow](.github/workflows/lean.yml) · [Checkpoint](https://github.com/eldernos/MathematicsResearch/tree/research-checkpoint-8)

The research and formalization are AI-assisted. The review guide compares the statements with the literature and identifies questions of mathematical priority. Original contributions use the MIT license. The port of Trevor Morris’s Weyl criterion retains its Apache-2.0 license. [Guide for reviewers](notes/reviewers.md) · [Research conversation](https://chatgpt.com/share/6b04aebe-d930-83e9-9175-772054b7d221) · [MIT license](LICENSE) · [Weyl criterion and attribution](NormalityChecker/Analysis/Weyl.lean)
