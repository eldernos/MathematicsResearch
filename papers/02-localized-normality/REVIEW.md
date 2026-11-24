# Paper II reviewer guide

[Manuscript (PDF)](paper.pdf) · [LaTeX source](paper.tex) · [Bibliography](references.bib) · [Public statements](Statements.lean) · [Correspondence proofs and axiom checks](Check.lean)

The main results are Theorems 1.1 and 1.2. Section 4 proves that persistent cancellation at each individual off-radix prime has measure zero. Section 5 treats rational polynomial weights and restrictions. Appendix A gives the exact joint formula through every prefix. Keeping the formula in an appendix allows a referee to verify the classification using only the single-prime upper bound, and to examine the stronger local clearing equivalence separately.

## Correspondence with the checkpoint

The prefixes **L** and **P** below stand for `NormalityChecker.LocalizedSupport` and `NormalityChecker.PolynomialMasks`. Each source link selects a declaration at commit `a09e011720bc74396a27f4cb3ce2d8a5b3ce5035`. Table 1 in the manuscript also links the supporting declarations.

| Registry ID | Assertion and hypotheses | Checkpoint declaration |
| --- | --- | --- |
| LS-01 | For a finite prime set, integer radix ≥ 2 and positive integer order, the unsigned series has interval discrepancy tending to zero when some support prime does not divide the radix, and tending to one otherwise. | [L.unsigned_discrepancy_limit](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/UnsignedNormality.lean#L194), [L.unsigned_finite_support_normal](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/UnsignedNormality.lean#L187) |
| LS-03 | For **each** chosen off-radix prime, the persistent order-*s* failed set is null and its computable worst-prefix bound tends to zero with precision. | [L.unsigned_persistent_null](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/UnsignedNormality.lean#L120), [L.unsigned_certificate_tendsTo_zero](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/UnsignedNormality.lean#L144) |
| MW-01 | For every nonzero rational polynomial on full support, normality is equivalent to a pole at zero after cancellation and the presence of an off-radix prime. The Lean theorem includes *s* = 0. | [P.full_rational_normal_iff](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/FullPolynomialNormality.lean#L15), [P.rational_grid](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/MaskRational.lean#L25) |
| MW-01, restrictions | For a residual pole, retained first windows bound discrepancy by their missed upper density. On one off-radix prime-power axis, unbounded retained exponents are necessary and sufficient. General numerator statements use cancellation of a common power of the variable. | [P.rational_window_bound](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/MaskClassification.lean#L122), [P.axis_normal_iff](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/MaskAxis.lean#L138), [P.masked_cancel](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/MaskGrid.lean#L158) |
| LS-02 | For all positive orders the discrepancy tracks the length of simultaneous persistent failures at every off-radix prime and every order from 1 through *s*. Its limsup is the limiting joint upper density of the finite failed cells and the maximum on the actual log-flow closure. | [L.discrepancy_tracks_jointPhase](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/HigherOrderPrefix.lean#L276), [L.jointOrder_density_tendsTo_discrepancy](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/HigherOrderPrefix.lean#L370), [L.discrepancy_eq_log_flow_max](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/HigherOrderPhase.lean#L412) |

### Points for mathematical review

- In the recurrence proof, check the return in logarithmic measure, eventual periodicity when a generator divides *p* − 1, survival of the bare ray after every difference, and the separation restricted to rows at bounded distance. It is the fibers of the **differenced** moment that are finite. The original moment is proved to have a null zero set. [Detailed proof note](../../notes/unsigned-finite-support.md)
- For polynomial weights, check the dominance inequality *v* − *kt* + *L* − 1 < −*k*(*t* − 1), then clear the radix part of the rational coefficient denominator on each clean block. A rational boundary example has discrepancy tending to 2/3. Exact window densities for masks give upper bounds for their discrepancy. [Polynomial and mask arithmetic](../../notes/polynomial-masks.md) · [Both 2/3 limits](../../NormalityChecker/MaskThirds.lean)
- In Appendix A the local prefix identity holds at **every real point** in the unit interval of a digit position. This justifies using length of the discarded set. The passage from real to integer counts at fixed precision has bounded error because the late mesh boundaries are integers. [All-orders derivation](../../notes/higher-order-joint.md)
- The order-two example has radix 36, primes 2, 3, 7, and shift 186. The scale exponent is 2, the deepest test has precision 3, and the failed residue leaves exact denominator 7. Proposition 6.1 on one-sided zeros is a paper deduction. The additional finite-termination results in the linked note have external Diophantine input. A general proof of termination with several cofactor primes at fixed small order remains open here. [Kernel-checked counterexample](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/JointPersistent.lean#L378) · [Finite-depth paper deductions](../../notes/fixed-depth-question.md)
- The public statement uses half-open intervals, shifts starting at zero, positive indices starting at one and all radix words including leading zeroes. The unsigned number includes the term 1/*b* even for the empty prime set. The full polynomial includes *P*(1)/*b*. Arbitrary masks may remove that term. The empirical definitions agree by unfolding, while the series comparison proves the prime-divisor condition and reindexes the polynomial sum past its zero-index term. [Public contract](Statements.lean) · [Proof entry point](Check.lean)

## Earlier literature and priority review

Primary-source comparison completed on 24 November 2026. Searches included “localized logarithm normality finite prime support”, “localized polylogarithm normality smooth numbers rational normal base logarithm”, “Dibag Generalization of the von Staudt-Clausen theorem”, and “differencing methods for Korobov-type exponential sums Vandehey Corollary 1.2”. The three journal citations were cross-checked against their DOI records. The 2026 citation uses the title and revision of the manuscript PDF, which has no author byline.

| Source | Comparison checked |
| --- | --- |
| Dibag, 1989 | Definitions 1.1–1.2 localize the logarithm; the application concerns generalized Bernoulli coefficients. The positive generating function in this paper is obtained by sign change. [Original article](https://doi.org/10.1016/0021-8693(89)90180-4) · [Institutional copy](https://hdl.handle.net/11693/26254) |
| Bailey and Crandall, 2002 | Corollary 4.9(i) contains the order-one singleton prime case, up to the first term 1/*b*, for coprime radix and parameter. [Article](https://doi.org/10.1080/10586458.2002.10504704) · [Authors’ copy](https://www.davidhbailey.com/dhbpapers/bcnormal.pdf) |
| Vandehey, 2019 | Corollary 1.2 gives short-orbit cancellation for a fixed finite set of denominator primes. Theorem 7.4 already implies every unsigned positive order on an infinite restriction of one off-radix prime-power axis. Its divisibility chain need not hold on a full support containing two incomparable primes. [Article](https://doi.org/10.1007/s11854-019-0038-2) · [Author manuscript](https://arxiv.org/abs/1606.07911) |
| *Binary normality of a localized logarithm*, 2026 | Theorems 1.1 and 4.1 cover binary {2,3} at order one, including a quantitative discrepancy estimate. Theorem 5.1 treats nonempty supports wholly coprime to the radix and binary supports containing 3, at order one. Section 6 specifies the scope of the separate Lean verification. [Pinned manuscript](https://github.com/CaptainSude/xi-normality/blob/06961817c7f61181ed9a5c73badb8d908d6ccdcc/paper/localized-logarithm-normality.pdf) |

The classification strictly extends the indicated statements in their support and weight hypotheses. Priority for arbitrary mixed supports, rational polynomial weights of unrestricted degree and the recurrence argument requires independent specialist review. No fixed-support conclusion passes to the unrestricted logarithm.

## Reproduction

Use the toolchain pinned in the repository. The public statement file is independent of the project imports. The shell entry point compiles it into a temporary module tree, imports it and the established proofs, and audits the new conclusions. Run from the repository root.

```sh
lake build
papers/02-localized-normality/check.sh
lake env lean Audit.lean
NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean
```

Both public conclusions report precisely `[propext, Classical.choice, Quot.sound]`. In this checkout the declaration-directory check verifies 776 public theorems and lemmas at the checkpoint. The two statement proofs are outside the default build target and the directory.

The exact order-one finite tests in Section 6 can be reproduced with the existing rational checker. Its argument for precision is *L*, while the Lean cell coordinate uses *L* − 1.

```sh
for L in 1 2 3; do python3 scripts/localized_certificate.py 32 31 "$L" 2 31; done
```

The successive worst-prefix bounds are 1/2, 31/960 and 0. A larger fixed case first passes at precision 12. For radix 82967135716, selected prime 3 and support {2,3,17,41,103,311,929}, the bounds at levels 9–12 are 1569/32768, 1569/32768, 1937/49152 and 0. These are exact finite computations. [Finite tests and the varying-support construction](../../notes/joint-persistent.md#what-finite-refinement-can-detect)

The figure is theorem-derived. Each of its 56 entries is 1 exactly when every prime in the row's support divides the radix at the head of its column. Its generator writes a CSV, vector PDF and vector SVG. The tables of values and vector labels contain the same digits in either color or grayscale. [Data](figures/classification.csv) · [Generator](figures/classification.py) · [SVG](figures/classification.svg)

```sh
cd papers/02-localized-normality
python3 figures/classification.py           # Python 3 with pycairo and DejaVu Sans
export SOURCE_DATE_EPOCH=1795478400 FORCE_SOURCE_DATE=1 TZ=UTC
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

The figure also ships in PDF, so rebuilding the manuscript alone requires only LaTeX and BibTeX. The manuscript has been compiled and its pages visually checked. It is a research draft for expert review. Authorship, final attribution and submission remain with the project owner.
