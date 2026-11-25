# Synthetic Arithmetic Expansions and Prescribed Discrepancy

**Authors:** Christopher Anderson (Independent Researcher)

**Version:** 1.0 (preprint draft, 25 November 2026)

**Categories:** math.NT (primary); math.DS (cross-list)

**MSC2020:** 11K16 (primary); 11K38, 11L07, 11J81, 37A44, 11A63 (secondary)

**Keywords:** normal numbers; extreme discrepancy; radix expansions; Stoneham and Korobov numbers; polynomial images; joint normality; invariant measures; Liouville numbers; Lean 4 formalization

## Abstract

Fix an integer base $b\ge2$, a prime $p\nmid b$, and let $t$ be the order of $b$ modulo $p$. Insert the coefficient $p^{-s v_p(k)}$ at base-$b$ position $tk^d$ for every $k\ge1$. For $s=0$ the extreme discrepancy tends to one, while for every integer $s\ge1$ the number is normal to base $b$. This switch holds on every strictly increasing schedule of multiples of $t$ dominating $k^2$, and it has been checked by the Lean 4 kernel together with the exact reduced denominator of every shifted prefix.

For odd $p$ and $d\ge s+2$, complete periods give an explicit power rate. For $\xi=\sum_k3^{-v_3(k)}2^{-2k^3}$ a short self-contained proof gives $D_N\le200N^{-1/3}$.

Choosing the rational state after each cubic insertion by a positive correction realizes every limiting discrepancy in $[0,1]$ with error $O(N^{-1/3})$, every pair of lower and upper limits, and every nonempty compact connected set of invariant measures as a limit set.

For odd $p$, $s\ge1$ and $d\ge3$, every nonconstant rational polynomial of total degree at most two in the numbers of this family with distinct orders $s$ on a common schedule is normal; in particular $\xi^2$ is normal and $(\xi,\xi^2)$ is jointly normal. The proof shows that the limiting $p$-adic mass of the shifted prefixes has Lebesgue-null level sets, by counting isolated jumps with van der Corput's method and a second-moment argument.

Finally, a positive binary series using every odd prime as a denominator prime is normal and Liouville, with $D_N=O(1/\log N)$, while positive rational multiples of its jointly normal components can sum to any positive rational.

## Source and verification

- **Manuscript source and PDF:** `papers/07-synthetic-expansions/` on the `publication/wave-2` branch. The release-commit link will be added at integration; every Lean link inside the paper is already pinned to the commits below.
- **Lean declarations (checkpoint 18):** pinned to [`e4809cf561573aef588e6ffc491a35cdb79fd9ec`](https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker):
  - [RetirementDenominator.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean)
  - [SmoothOrbit.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean)
  - [Phase18Synthetic.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean)
  - [PositiveSummation.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PositiveSummation.lean)
  - [SharpTranslation.lean](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean) (quoted identity only)
- **Lean declarations (grids):** pinned to [`c2c9da683666b3b9368e5d4b5cb858caccf528f5`](https://github.com/eldernos/MathematicsResearch/tree/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker):
  - [SurvivingGrid.lean](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/SurvivingGrid.lean)
  - [PrimePowerGrid.lean](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean)
- **Theorem verification map:** `papers/07-synthetic-expansions/VERIFICATION.md`.
- **Novelty ledger:** `papers/07-synthetic-expansions/LEDGER.md`.
- **Companion manuscript:** *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations* (`papers/10-discrepancy-arithmetic/`, same release), which proves the translation identity quoted here.

## Verification scope

Lean declarations checked by the kernel prove the complete statements of:

- the exact denominator identity;
- the normality switch (Theorem A);
- the fixed-support short-orbit estimate;
- the geometric grouping identities;
- the positive state recurrence;
- the sharp translation identity, quoted from the companion manuscript.

Both builds' axiom audits accepted only `propext`, `Classical.choice` and `Quot.sound`. The following are written proofs, some with Lean-verified steps: all convergence rates; the all-prefix criterion beyond the short-orbit estimate; the prescribed-limit and limit-set theorems; **the quadratic-image theorem, including the normality of $\xi^2$ (a paper proof, not formalized, reviewed only by AI models)**; and the infinite-sum constructions. Exact rational computations exercise finite instances only.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
