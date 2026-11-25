# Theorem verification map: Paper III, version 1.2

Evidence labels follow [the Wave 2 contract](../WAVE2-CONTRACT.md). The declaration-level correspondence, with every pinned link, is in [CORRESPONDENCE.md](CORRESPONDENCE.md). All Lean links point to Checkpoint 11 (`a09e011720bc74396a27f4cb3ce2d8a5b3ce5035`). Each cited Lean file is byte-identical at `e4809cf561573aef588e6ffc491a35cdb79fd9ec`, where the wave 2 clean-checkout build, axiom audit and kernel replay were run.

| Result | Statement (short) | Evidence | External inputs |
| --- | --- | --- | --- |
| Theorem 1 (2), DS-01 | Discrepancy minus zero-shell density tends to 0 at every cutoff | Kernel-verified (`discrepancy_sub_zeroDensity_tendsto`, `limsup_discrepancy_eq_zeroDensity`) | none |
| Theorem 1 (3), DS-03 | Rational translation multiplies the main term by the rational-orbit discrepancy | Kernel-verified (`translated_discrepancy`, `translated_limsup`) | none |
| Lemma 2 | Interval estimate for incomplete rational orbits on a fixed support | Lean-supported paper proof (order and character inputs in Lean) | none |
| Theorem 3, CR-01 | Cyclotomic resonance criterion for finite rational combinations | Kernel-verified (`cyclotomic_normal_iff`, `cyclotomicNormalTest_correct`) | none |
| Equation (7) | All-cutoff distribution of the integer-cleared sum | Paper proof | none |
| Lemma 4, Lemma 5 | Shell phases; finite circle transfer across atoms | Lean-supported paper proof | none |
| Proposition 6, DS-02 | Periodic discrepancy as a maximum of cycle scores | Kernel-verified for the periodic maximum (`periodic_discrepancy`); the reversed-series derivations are paper proofs | none |
| Theorem 7, DS-04 | Attainable upper discrepancies equal suffix-maximal history values | Kernel-verified (`attainable_discrepancy_iff`) | Kaneko–Steiner, for context only |
| Corollary 8 | Compactness and approximation of the spectrum | Kernel-verified (`isCompact_historySpectrum` and companions) | none |
| Proposition 9 | de Bruijn examples of small positive discrepancy | Lean-supported paper proof (bounds and the eight-cell example in Lean; the exact extremal formula is written) | none |
| Theorem 10 | Rationality versus transcendence of the signed expansions | Lean-supported paper proof (`irrational_iff_frequently_nonzero`) | Roth (1955), Ridout (1957) |
| Theorem 11, CR-03 | Two positive normal summands with a nonnormal irrational sum | Kernel-verified (`severe_normal_summands` and companions) | none |

## What is completely kernel-verified

Theorems 1, 3, 7 and 11, Corollary 8, and the periodic maximum in Proposition 6, each as stated in the library's definitions. The definitions are listed in the first row of [CORRESPONDENCE.md](CORRESPONDENCE.md), and [check.lean](check.lean) restates the principal conclusions and audits 18 declarations.

## External analytic dependencies

Roth's theorem and Ridout's theorem, which are used only for the transcendence conclusions of Theorem 10.

## Reproduce

```sh
lake build
lake env lean papers/03-signed-resonance-v1.2/check.lean
python3 papers/03-signed-resonance-v1.2/figures/generate.py
wsl -d Ubuntu -- bash papers/wsl-build.sh 03-signed-resonance-v1.2   # on Windows; papers/build.sh elsewhere
```
