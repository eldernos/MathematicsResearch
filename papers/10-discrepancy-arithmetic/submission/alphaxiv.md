# The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations

**Authors:** Christopher Anderson (Independent Researcher)

**Version:** 1.0 (preprint draft, 25 November 2026)

**Categories:** math.NT (primary); math.DS, math.PR (cross-lists)

**MSC2020:** 11K38 (primary); 11K16, 11A63, 37A44, 60B10 (secondary)

**Keywords:** extreme discrepancy; radix expansions; normal numbers; translation; addition spectrum; Kuiper statistic; concentration function; Ky Fan metric; rational dilation; Lean 4 formalization

## Abstract

For an integer base $b\ge2$ let $D_N(x)$ be the extreme discrepancy of $x,bx,\ldots,b^{N-1}x$ modulo one. We prove the finite identity $\sup_x|D_N(x+z)-D_N(x)|=1-D_N(z)$, attained at $x=0$, and classify the translations that preserve both limiting discrepancies of every real number: they are the numbers $c+w$ with $(b-1)c\in\mathbb Z$ and $N^{-1}\sum_{n<N}\lVert b^nw\rVert\to0$.

The limits of $D_N(x)$, $D_N(y)$ and $D_N(x+y)$ are exactly the triples in $[0,1]^3$ with $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$. Every such triple is realized by positive rational expansions on a cubic schedule with simultaneous error $O(N^{-1/3})$, uniformly in the triple, by computable and algebraically independent witnesses. The analogous deficit polytope for $d$ summands is determined.

The translation deficit $1-D_N(x-y)$ is a pseudometric, an exact form of Lévy's concentration function comparable to the Ky Fan distance to constants. The rational scalars preserving its asymptotic kernel are exactly $\mathbb Z[1/b]$, and an individual rational scaling is decided by a residue-density test. On the boundary $D_N(mx)\to1$ the attainable limits of $D_N(x)$ form $[1/m_0,1]$, where $m_0$ is the part of $m$ prime to $b$.

The finite identity, the pseudometric axioms and the qualitative addition spectrum are verified by the Lean 4 kernel.

## Source and verification

- **Manuscript source and PDF:** `papers/10-discrepancy-arithmetic/` on the `publication/wave-2` branch. The release-commit link will be added at integration; every Lean link inside the paper is already pinned to the commits below.
- **Lean declarations (checkpoint 18):** pinned to [`e4809cf561573aef588e6ffc491a35cdb79fd9ec`](https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker):
  - [SharpTranslation.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean)
  - [Phase18Synthetic.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean)
- **Lean declarations (addition spectrum, distance, grids):** pinned to [`c2c9da683666b3b9368e5d4b5cb858caccf528f5`](https://github.com/eldernos/MathematicsResearch/tree/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker):
  - [AdditionSpectrum.lean](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/AdditionSpectrum.lean)
  - [DiscrepancyGeometry.lean](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/DiscrepancyGeometry.lean)
  - [PrimePowerGrid.lean](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean)
- **Theorem verification map:** `papers/10-discrepancy-arithmetic/VERIFICATION.md`.
- **Novelty ledger:** `papers/10-discrepancy-arithmetic/LEDGER.md`.

## Verification scope

Lean declarations checked by the kernel prove the complete statements of:

- the sharp translation identity and its transfer bound;
- the pseudometric axioms of $1-D_N(x-y)$ and its zero set at finite $N\ge2$, and the triangle inequality, translation invariance and integer Lipschitz bound of its asymptotic version;
- the finite necessity and the qualitative sufficiency of the addition spectrum in every base;
- the positive state recurrence used in the constructions;
- the finite sparse-translation inequality and the lower dilation bound.

Both builds' axiom audits accepted only `propext`, `Classical.choice` and `Quot.sound`. The following are written proofs, some with Lean-verified steps: the classification of universal preservers, the concentration and Ky Fan comparison, the description of the asymptotic kernel, the rational-scalar theorems (which use only the subgroup property of the kernel from Lean), the cubic rate, computability and algebraic independence of the addition witnesses, the convex geometry for $d$ summands, the six-form inequality, the dilation boundary spectrum and the product example. The identity is not presented as a new probability metric: it combines Kuiper's statistic, Lévy's concentration function and the Ky Fan and Lévy–Prokhorov distances. The addition polytope coincides with the polytope of Bergelson and Downarowicz's point-entropy inequalities (arXiv:2506.12929, Prop. 4.9 and Cor. 4.10(1)), for a different observable.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
