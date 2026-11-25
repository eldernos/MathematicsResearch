# Verification map: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v1.0)

Lean links use one of two commits:

- Phase 18 modules are pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (research-checkpoint-18). Base: `E = https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker`.
- Phase 19 modules (AdditionSpectrum, DiscrepancyGeometry, SurvivingGrid, PrimePowerGrid) are pinned to `c2c9da683666b3b9368e5d4b5cb858caccf528f5`. Base: `P = https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker`.

Every line anchor below was checked against `git show <commit>:<path>`: the anchored line contains the declaration name. All 36 Lean URLs in the PDF resolve to existing lines.

The numbering is that of the built `paper.pdf`. Theorems A–F in the introduction restate theorems from later sections, as listed in the last column.

| No. | Statement (short) | Evidence | Lean declarations | External inputs | Reproduction |
| --- | --- | --- | --- | --- | --- |
| A | Normality switch: $D_N(X_0)\to1$ and $D_N(X_s)\to0$ for $s\ge1$ | Kernel-verified (= Thm 4.4) | see 4.4 | — | `lake build` (see Reproduce) |
| B | Rate for $d\ge s+2$, and $D_N(\xi)\le200N^{-1/3}$ | Lean-supported paper proof (= Thm 4.6 and Thm 3.1) | see 4.2 | — | `python -B scripts/phase18_principal.py` (finite enclosures) |
| C | Every $\delta$ at rate $N^{-1/3}$, all pairs, all limit sets | Lean-supported paper proof (= Thms 5.3, 6.1, 6.4) | see 5.1 | — | `python -B scripts/phase18_programming.py` |
| D | $\sup_x\lvert D_N(x+z)-D_N(x)\rvert=1-D_N(z)$, and the preserver classification | Kernel-verified identity (= Thm 7.1); classification is a paper proof (= Thm 7.4) | see 7.1 | — | `lake build` |
| E | Exact addition spectrum, uniform cubic rate | Kernel-verified qualitative statement (= Thm 8.1); rate is a Lean-supported paper proof (= Thm 8.2) | see 8.1 | — | `python3 -B scripts/phase19_addition.py` at `c2c9da6` |
| F | All-odd-prime normal Liouville sum, finite joint normality, rational totals | Lean-supported paper proof (= Thms 10.2–10.4) | see 10.2, 10.4 | KN Ch. 1 Thms 2.1, 6.2 | `python3 -B scripts/phase19_grids.py` at `c2c9da6` |
| 2.1 | Half-open arcs; $D$ = sup of positive excess; rotation invariance | Paper proof | — | — | — |
| 2.2 | Finite comparison $\lvert D(u)-D(v)\rvert\le E/N+2\epsilon$ | Paper proof (orbit case kernel-verified as `discrepancy_transfer`) | [E/Phase18Synthetic.lean#L583](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L583) | — | `python -B -m unittest scripts/test_phase18_summation.py` (translations with atoms) |
| 2.3 | Block certificate | Paper proof | — | — | — |
| 2.4 | Grids for $q=p^eQ$; count error $Lp^{c-e}+\tau p^{e-c}$ | Lean-supported paper proof: order and one-stretch count are Lean | [`stride_order` P/SurvivingGrid.lean#L43](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/SurvivingGrid.lean#L43), [`crt_period_count` P/PrimePowerGrid.lean#L337](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean#L337) | — | `phase19_grids.py` (240 full-orbit cases) |
| 2.5 | Prime-power orbits: error $\le p^vL/p^e+p^e$ | Paper proof (full-period case is `primePower_period_count`, [P/PrimePowerGrid.lean#L313](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean#L313)) | — | — | `phase18_programming.py` (B2: 66 orbits) |
| 3.1 | $D_N(\xi;2)\le200N^{-1/3}$; $D_N(\sum2^{-2k^3})\to1$ | Paper proof | (Step 1 is an instance of Thm 4.2) | — | `phase18_principal.py` prints $D_{1024}\in[0.593424,0.593425]$ |
| 4.1 | Geometric grouping; absolute convergence; infinite raw prime support | Kernel-verified | [`geometric_retirement_weight` L76](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L76), [`grouped_retirement_hasSum` L146](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L146), [`raw_prime_support_infinite` L290](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L290) | — | `lake build` |
| 4.2 | Exact reduced denominator $p^{s\lfloor\log_pK\rfloor}$ | Kernel-verified | [`shiftedPrefix_den` L110](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L110), [`fullPrefix_den` L157](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L157), [`maximalLayer_card` L67](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L67) | — | `phase18_principal.py` (12,987 prefix shifts) |
| 4.3 | Fixed-support short-orbit estimate | Kernel-verified | [`fixed_support_orbit_estimate` L207](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean#L207), [`SmoothOrbitEstimate` L16](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean#L16) | Related, not used: Vandehey, arXiv:1606.07911, Cor. 1.2 | `lake build` |
| 4.4 | Normality switch on schedules $n_k\ge k^2$, $t\mid n_k$ | Kernel-verified | [`discrepancy_switch` L436](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L436), [`normal_iff_pos` L444](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L444), [`polynomial_discrepancy_switch` L456](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L456) | Weyl's criterion is used only in the written outline (KN Ch. 1 Thm 2.1; Ch. 2 Thm 1.1) | `lake build` |
| 4.5 | $\sum p^{-sv_p(k)}b^{-t(k+1)!}$ is normal and Liouville | Lean-supported paper proof (normality is Thm 4.4; the hypotheses $n_k\ge k^2$ and $t\mid n_k$ for this schedule are not formalized; Liouville part is written) | as 4.4 | Liouville's theorem (classical) | — |
| 4.6 | Complete-period rate for $d\ge s+2$ | Lean-supported paper proof (denominator step = Thm 4.2) | as 4.2 | — | `phase18_principal.py` |
| 5.1 | Positive state programming; $p$-power coefficients | Kernel-verified | [`programState_fract` L383](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L383), [`programState_eq_prefix` L438](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L438), [`programmed_prefix_fract` L459](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L459), [`programCoeff_mem` L364](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L364), [`programCoeffs_prime_power` L426](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L426) | — | `phase18_programming.py` (12,288 transitions) |
| 5.2 | Modelled discrepancy $\lvert D_N-Z/N\rvert\le(H+(K+1)W)/N+\ldots$ | Paper proof | — | — | `phase18_programming.py` (G1, 291 windows) |
| 5.3 | Every $\delta\in[0,1]$ at rate $C_{b,p}N^{-1/3}$; weak limit; irrationality | Lean-supported paper proof (Lemma 5.1) | as 5.1 | — | `phase18_programming.py` ($b=2,p=3,\delta=2/5$, $N=400$: $D_N\in[0.549027,0.549028]$) |
| 6.1 | Every pair $(\alpha,\beta)$ of lower and upper limits | Lean-supported paper proof (Lemma 5.1) | as 5.1 | — | — |
| 6.2 | Limit sets are nonempty, compact, connected and invariant | Paper proof | — | — | — |
| 6.3 | Weak continuity of $D$ | Paper proof | — | — | — |
| 6.4 | Exactly the nonempty compact connected sets of invariant measures | Lean-supported paper proof (Lemma 5.1) | as 5.1 | Riesz representation (standard). Parthasarathy (1961) is a precedent for periodic density; it is not used as a black box | — |
| 7.1 | Sharp translation identity | Kernel-verified | [`sharp_translation` L343](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L343), [`sharp_translation_zero` L378](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L378), [`sharp_translation_isGreatest` L386](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386), [`sampleDisc_paired` L326](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L326) | — | `lake build`; `test_phase18_summation.py` |
| 7.2 | Transfer bound; eventually integral translations | Kernel-verified | [`discrepancy_transfer` L583](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L583), [`discrepancy_eventually_int` L642](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L642) | — | `lake build` |
| 7.3 | $1-D_N(x-y)$ is a pseudometric; its zero set for $N\ge2$ | Kernel-verified | [`discDist_triangle` L78](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L78), [`discDist_comm` L68](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L68), [`discDist_translate` L55](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L55), [`discDist_isGreatest` L87](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L87), [`radixDiscrepancy_lipschitz` L93](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L93), [`discDist_eq_zero_iff` L243](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L243) | — | `lake build` at `c2c9da6` |
| 7.4 | Universal numerical preservers: six equivalent conditions | Paper proof (uses 7.1 and 6.2) | — | — | — |
| 7.5 (Remark) | $\mathcal G(b)\subsetneq\mathcal D(b)$ (comparison with Rauzy) | Remark; external input | — | Rauzy, Acta Arith. 29 (1976) 211–225; Bergelson–Downarowicz arXiv:2506.12929v1 Defs. 3.5, 3.10, Thm. 3.12 | — |
| 8.1 | Exact addition spectrum (finite necessity, limiting sufficiency) | Kernel-verified | [`finite_necessity` L248](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L248), [`exact_addition_spectrum` L1486](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L1486), [`mixtureRealizable` L1470](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L1470) | — | `lake build` at `c2c9da6` |
| 8.2 | Uniform cubic rate for every admissible triple | Lean-supported paper proof (Lemma 5.1; necessity is 8.1) | as 5.1 | — | `python3 -B scripts/phase19_addition.py` at `c2c9da6` (2,448 prefixes) |
| 8.3 | Spectrum for $d$ summands (qualitative) | Lean-supported paper proof (realization step = `mixtureRealizable`; necessity and convex geometry are written) | as 8.1 | — | `phase19_addition.py` (1,153 decompositions) |
| 9.1 | Quadratic sparse remainder: finite bound, rate, irrationality | Lean-supported paper proof (the finite inequality is kernel-verified) | [`quadratic_sparse_transfer` L837](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L837) | — | `test_phase18_summation.py` |
| 9.2 | Factorial sparse remainder: Liouville, rate $O(\log^2N/N)$ | Lean-supported paper proof | [`sparse_discrepancy_transfer` L811](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L811) | — | — |
| 9.3 | Lambert remainders: max change $=1-D_N(L_\chi)$, with order from the companion paper | Paper proof (equality = Thm 7.1) | as 7.1 | Companion manuscript `papers/06-multiplicative-lambert` (two-sided deficit estimate; not yet released) | — |
| 10.1 | Exact denominators of prefixes of $\sum r_\ell Y_\ell$ | Paper proof | — | — | `phase19_grids.py` (325 insertion denominators) |
| 10.2 | $Y$ is normal and Liouville; $D_N(Y)\ll1/\log(2N)$ | Lean-supported paper proof (Lemma 2.4 steps) | as 2.4 | — | `phase19_grids.py` certifies $D_N(Y)<1/8$ at four prefixes near $16^{11}$ |
| 10.3 | Finite rational combinations of the $Y_\ell$; joint normality | Lean-supported paper proof (Lemma 2.4 steps) | as 2.4 | KN Ch. 1 Thm 2.1 (p. 7) and Thm 6.2 (p. 49) | — |
| 10.4 | Positive rationals with $\sum c_\ell Y_\ell=R$ | Lean-supported paper proof (existence of multipliers is kernel-verified) | [`hasSum_positive_rational_multiples` L15](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PositiveSummation.lean#L15) | — | — |
| 10.5 | Consecutive tails: $\overline M(E_k)+\overline M(E_{k+1})\ge1/4$ | Paper proof | — | KN Ch. 1 Cor. 1.1 (p. 3) | — |
| §11 | $(\xi,\xi^2)$ jointly normal | **Not claimed in this paper.** Written proof (Phase 19 `nonlinear.md`, independently audited by an AI reviewer), linked at `c2c9da6` | — | — | `python3 -B scripts/phase19_nonlinear.py` at `c2c9da6` |

KN = L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974. The theorem numbers and pages were checked against a text copy: Chapter 1, Corollary 1.1 (p. 3), Theorem 2.1 (p. 7), Theorem 6.2 (p. 49), Theorem 8.1 (p. 70); Chapter 2, Theorem 1.1 (p. 89).

## What is completely kernel-verified

The complete statements of Proposition 4.1, Theorem 4.2, Lemma 4.3, Theorem 4.4 (= Theorem A), Lemma 5.1, Theorem 7.1 (the identity in Theorem D), Corollary 7.2, Proposition 7.3 and Theorem 8.1 (the qualitative part of Theorem E) are Lean declarations. They use the paper's definitions of extreme discrepancy (`radixDiscrepancy`: supremum over $0\le a<c\le1$ of $\lvert\text{frequency in }[a,c)-(c-a)\rvert$) and normality (`NormalIn`: block frequencies with the terminating convention). The finite inequality in Theorem 9.1 is also kernel-verified.

These were checked in Lean 4.36.0 with the pinned Mathlib manifest:

- At `e4809cf`: 8,746 Lake jobs. The axiom audit of 1,593 public declarations accepted only `propext`, `Classical.choice` and `Quot.sound`, and an independent kernel replay covered all 248 module files (`notes/phase18/verification.md`).
- At `c2c9da6`: 8,754 jobs. The axiom audit covered 1,719 declarations with the same three axioms, and the replay covered all 252 modules (`notes/phase19/verification.md`).

This manuscript worktree did not rerun `lake build`, following the wave-2 contract. The statements were matched against the source text at the pinned commits.

Not kernel-verified:

- every rate (Theorems 3.1, 4.6, 5.3, 8.2, 9.1's rate, 10.2);
- the limit-set theorems (6.1, 6.4);
- the preserver classification (7.4);
- the convex geometry in 8.3;
- Section 10 beyond the cited grid steps and the multiplier existence.

## External analytic dependencies

- **Kuipers–Niederreiter (1974):** Weyl's criterion (Ch. 1 Thm 2.1, p. 7), multidimensional Weyl (Ch. 1 Thm 6.2, p. 49), Riemann-integrable test functions (Ch. 1 Cor. 1.1, p. 3), normality ⇔ uniform distribution (Ch. 1 Thm 8.1, p. 70), and uniform distribution ⇔ $D_N\to0$ (Ch. 2 Thm 1.1, p. 89).
- **Riesz representation and diagonal compactness** of $\mathcal P(\mathbb T)$. These are standard, and the paper gives a one-line justification.
- **Liouville's theorem** (Liouville numbers are transcendental). Classical.
- **Companion manuscript `06-multiplicative-lambert`:** the two-sided deficit $1-D_N(L_\chi)\asymp(\log\log N)/\sqrt{\log N}$, used only in Corollary 9.3.
- **Rauzy (1976) and Bergelson–Downarowicz (2025):** used only in Remark 7.5.
- **Not used as inputs:** Vandehey's Corollary 1.2, which is cited as the quantitative source of the qualitative Lemma 4.3 (itself kernel-verified), and the Phase 19 square theorem, which is mentioned but not claimed.

## Reproduce

From the repository root:

```sh
# Lean (long; uses the pinned toolchain). Checkpoint 18:
git checkout e4809cf561573aef588e6ffc491a35cdb79fd9ec && bash scripts/verify.sh
# Phase 19 modules:
git checkout c2c9da683666b3b9368e5d4b5cb858caccf528f5 && bash scripts/verify.sh
# Exact finite checks (standard library only)
python -B scripts/phase18_principal.py          # at e4809cf; exit 0 in this worktree
python -B scripts/phase18_programming.py        # at e4809cf; exit 0 in this worktree
python -B -m unittest scripts/test_phase18_summation.py   # 6 tests OK in this worktree
python3 -B scripts/phase19_addition.py          # at c2c9da6
python3 -B scripts/phase19_grids.py             # at c2c9da6
# Manuscript
wsl -d Ubuntu -- bash papers/wsl-build.sh 07-synthetic-expansions
```

The three Phase 18 scripts were run in this worktree on 25 November 2026 and passed: `phase18_principal.py` and `phase18_programming.py` exited with status 0, and the summation unit tests ran 6 tests, all OK. The Phase 19 scripts are cited from `notes/phase19/verification.md` and were not rerun here.
