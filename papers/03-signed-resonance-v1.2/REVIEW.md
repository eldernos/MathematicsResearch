# Reviewer guide to Paper III

[Manuscript](paper.pdf) · [LaTeX](paper.tex) · [Theorem correspondence](CORRESPONDENCE.md) · [Bibliography](references.bib)

**Status.** Complete draft for mathematical review. The arithmetic baseline is Checkpoint 11, `a09e011720bc74396a27f4cb3ce2d8a5b3ce5035`. The implementation checkout began at `0e58f3e8a8351f0923b80e693ff76a7ece539c87`. The manuscript introduces no library theorem. The result identifiers follow the [publication registry](https://github.com/eldernos/MathematicsResearch/blob/92cd9a59c1053a472c6786cb8de498bc76d11daf/docs/results.md).

## Structure and scope

Theorem 3 (CR-01) classifies finite rational sums with one odd prime parameter. Theorem 1 (DS-01 and DS-03) determines the discrepancy of a separate series with bounded integer phases at every prefix, up to an error tending to zero. Proposition 6 (DS-02) and Theorem 7 (DS-04) use the latter to compute periodic discrepancies and classify all upper discrepancies.

Both arithmetic proofs require uniform counts for incomplete rational orbits whose denominators grow on a fixed finite set of primes. Lemma 2 proves the needed estimate directly. Equation (7) applies the signed-shell comparison argument to the integer-cleared cyclotomic sum. These shared steps justify a single manuscript. Appendix A treats the explicit normal summands separately because their odd parameter may be composite and their quantitative conclusion is a lower frequency bound. The symbolic argument in §5 can be read independently from the boundary recurrence.

## Points for mathematical review

- **Finite sums.** Inspect the clearing factor (*p* − 1)·*D* in Theorem 3, especially for coincident insertions, indices divisible by the prime, signed rational weights and the empty family. The weak limits and equation (7) refer to the cleared sum. Table 1 concerns the jump series.
- **Uniformity and atoms.** In Lemma 2 the error is measured against the denominator for every partial length. In equation (6) the uniform interval count belongs to the comparison sample. Lemma 5 transfers its extreme discrepancy to the true sample across endpoints carrying atoms. Position zero contributes to the regular part.
- **Symbolic and numerical conclusions.** In Proposition 6 the first maximum uses the densities before shells. In Theorem 7 histories read chronology backwards and at least one coding suffices at a dyadic rational. For rational translation, the multiplier must be a nonzero integer. The division-by-nine example checks this restriction.
- **Diophantine input.** Proposition 9 proves the exact residual-rotation formula on paper. Lean supplies the one-visit upper bound and positivity. Theorem 10 proves rationality versus transcendence using the unreduced common denominators, a distinct-approximant argument and external Roth or Ridout. The discrepancy values in Table 1 are rational; their realizing numbers are transcendental.

## Literature search and priority

Searches on 24 November 2026 used the following query strings and followed the cited primary sources. The comparisons concern the hypotheses and outcomes in this manuscript.

| Search | Findings |
| --- | --- |
| “Stoneham numbers rational linear combinations nonnormal sums same base cyclotomic resonance normal numbers”; “normal nonnormal numbers rings Kano Shiokawa sums Stoneham Bailey Borwein” | Bailey–Borwein study nonnormality in other bases and pose the standard two-sum question. The 2026 manuscript fixes the construction radix for two standard constants. Our finite weights multiply components with varying radix dilation on a single prime axis. The ring literature establishes additive normality in specific constructions. [Bailey–Borwein](https://doi.org/10.1007/s11139-012-9417-3) · [two-sum manuscript](https://github.com/CaptainSude/Stoneham-sum-normal/tree/f4d3d1f01d00c57425c684409849053e58e42261) · [Kano–Shiokawa](https://doi.org/10.1007/BF02760950) · [Wagner](https://doi.org/10.1006/jnth.1995.1114) |
| “non normal sum normal numbers explicit Korobov type Kano linear combination normal numbers”; “Vandehey differencing methods Korobov type exponential sums Theorem 7.2” | Stoneham used successive numerator differences in 1970. Kano gives the original schedule in §1, the sufficient nondivisibility criterion in Theorem 1 and a transcendence argument in Theorem 2. The present jump series with eventually unit phases already satisfies that normality test. Vandehey studies incomplete-orbit bounds and their use with lacunary sums. [Stoneham](https://doi.org/10.4064/aa-16-3-239-254) · [Kano](https://doi.org/10.18910/10356) · [Vandehey, §7](https://arxiv.org/abs/1606.07911) |
| “limsup fractional parts powers of 2 spectrum limsup binary shift largest suffix Mahler orbit closure lexicographic Allouche”; “Baiocchi Komornik expansions in non integer bases suffixes expansion of one Allouche univoque self Sturmian” | Kaneko–Steiner already study precisely the lexicographic sup-words, closure by periodic words and the first positive word. Baiocchi–Komornik Theorem 2.5(a) treats infinite quasi-greedy expansions of one. Allouche uses a complementary suffix restriction for univoque expansions. Carminati–Tiozzo §2 gives the doubling-hole parameter set, which equals the reflection of the binary spectrum. [Kaneko–Steiner](https://doi.org/10.1112/mtk.12250) · [Baiocchi–Komornik](https://arxiv.org/abs/0710.3001) · [Allouche](https://doi.org/10.1051/ita:2007058) · [Carminati–Tiozzo](https://doi.org/10.1017/etds.2015.135) |
| “signed Stoneham number discrepancy rational translation spectrum de Bruijn”; “de Bruijn discrepancy consecutive cycles Becher Carton discrepancy normal numbers constructions” | De Bruijn supplies the cyclic-word antecedent. Becher–Carton analyze discrepancy of infinite expansions built from finite necklaces. The manuscript uses a single finite rational cycle and computes its extreme discrepancy before applying the translation product. [de Bruijn](https://research.tue.nl/en/publications/a-combinatorial-problem/) · [Becher–Carton](https://doi.org/10.1016/j.jco.2019.03.003) |

Priority remains open for the exact cyclotomic equivalence on this finite family, the every-cutoff signed and translated equalities, and the quantitative lower bound for these explicit normal summands. The identification of signed Stoneham discrepancies with the lexicographic sup-word set is the historical question concerning Theorem 7. The compactness and periodic closure of the word set have direct antecedents. Transcendence follows from classical approximation theorems. An expert in arithmetic normality can review these comparisons and the proofs before the owner considers authorship or submission.

## Reproduce

From the repository root with the pinned Lean toolchain, mathlib, Python 3, pdfLaTeX, TikZ, BibTeX and latexmk available:

```sh
python3 papers/03-signed-resonance/figures/generate.py
papers/build.sh 03-signed-resonance
lake build NormalityChecker.CyclotomicExamples NormalityChecker.ShellHistories NormalityChecker.TranslatedShellExamples
lake env lean papers/03-signed-resonance/check.lean
```

The [check file](check.lean) verifies the finite sum and polynomial definitions, zero-count convention, jump initialization, all-cutoff and periodic statements, translation product's prefix form, and suffix characterization. It also checks 18 declarations for dependencies outside `propext`, `Classical.choice` and `Quot.sound`. The common-denominator normality argument and the auxiliary examples are mapped to pinned declarations in the [correspondence table](CORRESPONDENCE.md).

Figure 1 joins samples of the exact leading terms at 145 integer cutoffs. Figure 2 shows both symbolic radices and enumerates all 510 binary words of lengths one through eight. The [prefix data](figures/prefix.csv), [spectrum data](figures/spectrum.csv) and [generator](figures/generate.py) use integer counts and rational arithmetic. Only display coordinates are rounded. The paper-local figures compare the two prefix terms and the two radix spectra on common axes. Additional portal plots show all three periodic examples and finer ternary resolution. [Portal figure sources](https://github.com/eldernos/MathematicsResearch/tree/92cd9a59c1053a472c6786cb8de498bc76d11daf/scripts/figures)

**Validation of this draft.** Two pdfLaTeX/latexmk builds in different output directories produced the same 11-page PDF with SHA-256 `428517af7a61a8f96537d1c4a582d99e0c7e1a3ced7d7fa1ed00b2c61e8a2004`. All pages were rendered for inspection. The final log has no unresolved citations or references, missing characters or box warnings. The 74 source links in the correspondence table were checked against declarations at the pinned commit. An independent direct count reproduced the 145 prefix rows; the fixed-point recurrence reproduced all 1,020 plotted period/radix calculations.
