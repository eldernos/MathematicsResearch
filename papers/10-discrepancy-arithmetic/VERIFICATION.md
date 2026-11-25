# Verification map: The Arithmetic of Extreme Discrepancy (v1.0)

Lean links use one of two commits:

- Checkpoint-18 modules (SharpTranslation, Phase18Synthetic) are pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec`. Base: `E = https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker`.
- Phase 19 modules (AdditionSpectrum, DiscrepancyGeometry, PrimePowerGrid) are pinned to `c2c9da683666b3b9368e5d4b5cb858caccf528f5`. Base: `P = https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker`.

All 30 Lean URLs embedded in the built `paper.pdf` were extracted with `pdfinfo -url` and checked with `git show <commit>:<path>`: each anchored line is the declaration line of the named theorem (30 of 30). The numbering below is that of the built PDF (16 pages). Theorems A–D in the introduction restate results from later sections.

| No. | Statement (short) | Evidence | Lean declarations | External inputs | Reproduction |
| --- | --- | --- | --- | --- | --- |
| A | Sharp translation identity; four equivalent forms of universal preservation | Kernel-verified identity (= Thm 3.1); classification is a Lean-supported paper proof (= Thm 3.3) | see 3.1 | — | `lake build` |
| B | Exact addition spectrum; cubic rate; computable, algebraically independent witnesses | Kernel-verified qualitative statement (= Thm 5.1); rate, computability and independence are Lean-supported paper proofs (= Thms 5.3, 5.4) | see 5.1, 2.5 | — | `python3 -B scripts/phase19_addition.py` at `c2c9da6` |
| C | Pseudometric $d_N$; kernel $K_b$; rational scalars $\mathbb Z[1/b]$; residue test | Kernel-verified pseudometric (= Prop 4.1); the rest are paper proofs (= Prop 4.3, Thm 4.5, Prop 4.6) | see 4.1 | — | `lake build` at `c2c9da6` |
| D | Integer dilation bounds and boundary spectrum $[1/m_0,1]$ | Lean-supported paper proof (= Prop 6.1, Thm 6.2) | see 6.1 | — | — |
| 2.1 | Arc excess formula, rotation invariance | Paper proof | — | — | — |
| 2.2 | Finite comparison $\lvert D(u)-D(v)\rvert\le E/N+2\epsilon$ | Paper proof (orbit case kernel-verified) | [`discrepancy_transfer` E/Phase18Synthetic.lean#L583](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L583) | — | — |
| 2.3 | Model comparison against a reference measure | Paper proof | — | — | — |
| (2) | $D(\theta\delta_0+(1-\theta)\lambda)=\theta$, $D(\theta\delta_0+(1-\theta)U_m)=\theta+(1-\theta)/m$ | Paper proof (displayed equation) | — | — | — |
| 2.4 | Prime-power orbit count (cited from manuscript C, Cor. 2.5) | Lean-supported paper proof: full-period count is Lean | [`primePower_period_count` P/PrimePowerGrid.lean#L313](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean#L313) | — | `lake build` at `c2c9da6` |
| 2.5 | Positive state programming (cited from manuscript C, Lemma 5.1) | Kernel-verified | [`programState_fract` L383](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L383), [`programState_eq_prefix` L438](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L438), [`programmed_prefix_fract` L459](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L459), [`programCoeff_mem` L364](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L364), [`programCoeffs_prime_power` L426](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L426) | — | `lake build` |
| 3.1 | $\sup_x\lvert D_N(x+z)-D_N(x)\rvert=1-D_N(z)$, attained at $0$ | Kernel-verified | [`sharp_translation` L343](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L343), [`radixDiscrepancy_zero` L357](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L357), [`sharp_translation_zero` L378](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L378), [`sharp_translation_isGreatest` L386](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386); paired-sample form [`sampleDisc_paired` L326](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L326) | — | `lake build` |
| (4) | Deficit bound $1-D_N(z)\le2\epsilon+E_N(z,\epsilon)/N$ | Paper proof (one line) | — | — | — |
| 3.2 | Transfer bound; eventually integral translations | Kernel-verified | [`discrepancy_transfer` L583](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L583), [`discrepancy_eventually_int` L642](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L642) | — | `lake build` |
| 3.3 | Universal numerical preservers: six equivalent conditions | Lean-supported paper proof ((i)⇔(ii) is Thm 3.1) | as 3.1 | — | — |
| 3.4 (Remark) | $K_b\subsetneq\mathcal D(b)$ (comparison with Rauzy) | Remark; external input | — | Rauzy, Acta Arith. 29 (1976) 211–225; Bergelson–Downarowicz arXiv:2506.12929v1, Defs. 3.5, 3.10, Thm. 3.12 | — |
| 3.5 | Quadratic sparse remainder: finite bound (kernel), rate, irrationality | Lean-supported paper proof | [`quadratic_sparse_transfer` L837](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L837) | — | `python -B -m unittest scripts/test_phase18_summation.py` at `e4809cf` |
| 3.6 | Factorial sparse remainder: Liouville, rate $O(N^{-1}\log^2N)$ | Lean-supported paper proof | [`sparse_discrepancy_transfer` L811](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L811) | Liouville's theorem (classical) | — |
| 4.1 | $d_N$ pseudometric, maximum formula, Lipschitz, zero set for $N\ge2$, integer Lipschitz | Kernel-verified | [`discDist_translate` L55](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L55), [`discDist_comm` L68](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L68), [`discDist_triangle` L78](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L78), [`discDist_isGreatest` L87](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L87), [`radixDiscrepancy_lipschitz` L93](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L93), [`discDist_eq_zero_iff` L243](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L243), [`discDist_intMul_le` L346](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L346) | — | `lake build` at `c2c9da6` |
| (5) | Two-sided local bound for $d_N$ | Paper proof | (related: `discDist_pos_bound`, P/DiscrepancyGeometry.lean#L293, not cited) | — | `python -B notes/phase19/reviews/geometry-periods-check.py` (§1, 300 exact cases) |
| 4.2 | Concentration formulas; $k\le1-D\le3k$ with sharp constants | Paper proof | — | Lévy (1939), Ky Fan (1943), Prokhorov (1956), Dudley (2002) §11.3: used only for terminology | — |
| 4.3 | Asymptotic pseudometric $d^+$; kernel $K_b=F_b+Z_0$ | Lean-supported paper proof | [`asymDist_triangle` L390](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L390), [`asymDist_intMul_le` L419](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean#L419) | — | `lake build` at `c2c9da6` |
| 4.4 | Rationals in $K_b$: denominator divides $b^j(b-1)$; $\lvert D_N(z/b)-D_N(z)\rvert\le1/N$ | Paper proof | — | — | geometry review script §2 ($b\le12$, $q<120$) |
| 4.5 | Universal rational scalars $=\mathbb Z[1/b]$ | Lean-supported paper proof (through Thm 3.3) | as 3.1, 4.3 | — | geometry review script §2 |
| 4.6 | Residue-density test for individual rational scalings | Paper proof | — | Bergelson–Downarowicz Prop. 4.25 (only for the remark that rational scalings preserve normality) | geometry review script §3 ($b=10$, $c=1/3$, $d=3$) |
| 5.1 | Exact addition spectrum: finite necessity; sufficiency in every base | Kernel-verified | [`finite_necessity` L248](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L248), [`polytope_eq_convexHull` L150](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L150), [`isExtremeIn_polytope_iff` L240](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L240), [`addSpectrum_eq` L1480](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L1480), [`exact_addition_spectrum` L1486](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L1486), [`mixtureRealizable` L1470](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean#L1470) | — | `lake build` at `c2c9da6` |
| (6) | Five convex weights | Paper proof (also Lean `fiveWeights`, P/AdditionSpectrum.lean#L120, not cited) | — | — | — |
| 5.2 | Deficit scheduler bounds $[-(r-1),1]$, also with approximate weights | Paper proof | — | — | `phase19_addition.py` |
| 5.3 | Uniform cubic rate for every admissible triple | Lean-supported paper proof (Lemma 2.5) | as 2.5, 2.4 | — | `python3 -B scripts/phase19_addition.py` at `c2c9da6` (2,448 prefixes; binary $N=100$ enclosures) |
| 5.4 | Computable, algebraically independent witnesses at the same rate | Lean-supported paper proof (Lemma 2.5) | as 2.5 | — | `phase19_addition.py` (five polynomial exclusions) |
| 5.5 | $d$-summand deficit polytope (qualitative) | Lean-supported paper proof (realization = `mixtureRealizable`; necessity and convex geometry written) | as 5.1 | — | `phase19_addition.py` (1,153 decompositions); `python -B notes/phase19/reviews/addition_check.py` (vertex enumeration $d\le4$) |
| 5.6 | Six-form inequality | Paper proof | — | — | `addition_check.py` (random non-orbit samples) |
| 6.1 | Finite dilation bounds | Lean-supported paper proof (lower bound = `discDist_intMul_le`) | as 4.1 | — | — |
| 6.2 | Boundary spectrum $[1/m_0,1]$ of dilation, with rate | Lean-supported paper proof (Lemma 2.5) | as 2.5 | — | geometry review script §6 (simulation, seven cases) |
| 6.3 | Moser–de Bruijn product of two sparse preservers is $b^r/(b^r-1)\notin K_b$ | Paper proof | — | Corollary 3.2 | geometry review script §7 |
| 6.4 (Remark) | Star and box counterexamples | Finite exact computation (remark) | — | — | exact values $1/2$, $61/192$, $63/64$ and $8/9$ recomputed with `fractions` on 25 November 2026; also geometry review script |

KN = L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974; Chapter 1, Theorem 8.1 (p. 70) and Chapter 2, Theorem 1.1 (p. 89) are cited in the introduction only.

## What is completely kernel-verified

The complete statements of Lemma 2.5, Theorem 3.1 (the identity in Theorem A), Corollary 3.2, Proposition 4.1 and Theorem 5.1 (the qualitative part of Theorem B) are Lean declarations, as are the finite inequality in Theorem 3.5 and the lower bound in Proposition 6.1. They use the paper's definition of extreme discrepancy (`radixDiscrepancy`: supremum over $0\le a<c\le1$ of $\lvert\text{frequency in }[a,c)-(c-a)\rvert$). The formal sufficiency proof of Theorem 5.1 uses a block schedule adapted to complete periods, not the cubic schedule of Theorem 5.3, and proves limits only.

Builds (Lean 4.36.0, pinned Mathlib manifest):

- At `e4809cf`: 8,746 Lake jobs; axiom audit of 1,593 public declarations with only `propext`, `Classical.choice`, `Quot.sound`; independent kernel replay of all 248 module files (`notes/phase18/verification.md`).
- At `c2c9da6`: 8,754 jobs; axiom audit of 1,719 declarations with the same three axioms; replay of all 252 modules (`notes/phase19/verification.md`).

This manuscript worktree did not rerun `lake build`, following the wave-2 contract. The statements were matched against the source text at the pinned commits.

Not kernel-verified: the preserver classification (3.3), the rates (3.5 beyond the finite inequality, 5.3, 6.2), computability and independence (5.4), the concentration and Ky Fan comparison (4.2), the asymptotic kernel description and the scalar results (4.3–4.6), the convex geometry of 5.5, the six-form inequality (5.6), the upper dilation bound and boundary spectrum (6.1–6.2), and the product example (6.3).

## External analytic dependencies

- **Kuipers–Niederreiter (1974):** normality is equivalent to $D_N\to0$ (introduction only).
- **Liouville's theorem** (Liouville numbers are transcendental), for Proposition 3.6.
- **Companion manuscript C** (`papers/07-synthetic-expansions`, same release): Lemma 2.4 (its Corollary 2.5, reproved here from the Lean full-period count) and Lemma 2.5 (its Lemma 5.1, kernel-verified).
- **Companion manuscript A** (`papers/06-multiplicative-lambert`): mentioned after Proposition 3.6 for the Lambert deficit; not used in any proof.
- **Rauzy (1976), Bergelson–Downarowicz (2025), Sigmund (1974), Kuiper (1960), Lévy (1939), Ky Fan (1943), Prokhorov (1956), Dudley (2002):** cited for comparison and terminology; none is used as a step in a proof. Bergelson–Downarowicz Proposition 4.25 is cited for the fact that nonzero rational scalings preserve normality, used only in a remark after Proposition 4.6.

## Reproduce

From the repository root:

```sh
# Lean (long; pinned toolchain)
git checkout e4809cf561573aef588e6ffc491a35cdb79fd9ec && bash scripts/verify.sh
git checkout c2c9da683666b3b9368e5d4b5cb858caccf528f5 && bash scripts/verify.sh
# Exact finite checks (standard library only)
python3 -B scripts/phase19_addition.py                    # at c2c9da6
python -B notes/phase19/reviews/addition_check.py          # at c2c9da6
python -B notes/phase19/reviews/geometry-periods-check.py  # at c2c9da6
python -B -m unittest scripts/test_phase18_summation.py   # at e4809cf
# Manuscript
wsl -d Ubuntu -- bash papers/wsl-build.sh 10-discrepancy-arithmetic
```

The manuscript build was run on 25 November 2026 and passed with no undefined references or citations (16 pages). The Lean pins were checked as described above. The four Python checks listed were rerun in this worktree on 25 November 2026 (Windows, Python 3, `PYTHONUTF8=1`) and all exited with status 0; the summation unit tests ran 6 tests, all OK. `phase19_addition.py` reported, among others, the six-form check on 7,920 rational orbit prefixes, and `addition_check.py` reproduced the binary $N=100$ enclosures.
