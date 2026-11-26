# alphaXiv AI Track Draft: Exceptional Orbits and Discrepancy of Stoneham Products

**Draft for owner approval. Do not upload without owner review.**

- **Title:** Exceptional Orbits and Discrepancy of Stoneham Products
- **Version:** 1.0 (`manuscripts-v2.0.0`)
- **Author:** Christopher Anderson (Independent Researcher)
- **Public contact route:** `https://github.com/eldernos/MathematicsResearch/issues`
- **Proposed categories:** `math.NT` (primary), `math.DS` (secondary) — confirm in the signed-in alphaXiv form
- **MSC2020:** Primary `11K16`; Secondary `11K38`, `11J81`, `11S80`, `37A44`
- **Keywords:** normal numbers, Stoneham constants, interval discrepancy, $p$-adic interpolation, Mahler series, logarithmic equidistribution, transcendence, Lean 4

## Abstract

For the product $x = \alpha(B,p)\alpha(B,q)$ of two Stoneham numbers with distinct odd prime parameters $p < q$ coprime to an integer radix $B \ge 2$, we show that every subsequential weak limit of the empirical radix-shift measures is a convex mixture of Lebesgue measure and rational periodic orbits supported on $\{p,q\}$, and that the scalar extreme interval discrepancy converges to that of the mixture. For the binary product $\alpha(2,3)\alpha(2,5)$, the upper discrepancy satisfies $D^+(x) \le 4/11 + 2.85 \times 10^{-10}$, and the threshold $D^+(x) \le 4/11$ is equivalent to the upper density $C_0$ of integer shifted prefixes being at most $4/11$ (with $D^+(x) = C_0$ whenever either fails). Ordinary binary normality of $\alpha(2,3)\alpha(2,5)$ remains open.

Under a finite pair of local $p$-adic simple-zero conditions—satisfied by infinitely many radices $B$ for every distinct odd prime pair $(p,q)$—Mahler interpolation yields a bijective $p$-adic isometry for each nonrectangular cutoff shape, logarithmic equidistribution, lower discrepancy $D^-(x) = 0$, and at most $O_\varepsilon(\log^* T)$ exceptional logarithmic scales up to $T$. For $(2,3,5)$ and $(2,5,3)$, Eisenstein irreducibility rules out integer shape roots. We also consolidate the kernel-verified $43/45$ bound for $\alpha(2,3)\alpha(2,5)$, transcendence and $D^+ < 1$ for general multiplicatively independent integer parameters via Ridout's theorem, and the kernel-verified plateau-cycle law and resonant-radix classification for rational quadratics in $\alpha(b,2)$, together with Lean-supported unconditional sub-quarter discrepancy bounds for explicit families (including a finite cycle enumeration for $b=5, D=9$).

## Verification scope

Three headline results are completely kernel-verified in Lean 4.36.0 at commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (axiom audit accepting only `propext`, `Classical.choice`, and `Quot.sound`): Theorem 6.1 (irrationality and $43/45$ upper discrepancy bound for $\alpha(2,3)\alpha(2,5)$, plus Remark 6.2's intermediate bounds $27/40$, $143881/250000$, and $4631/12500$), Theorem 7.1 (all-prefix plateau law, exact upper limit, $D^-=0$, logarithmic equidistribution, denominator normality criterion, exact $2$-adic denominator formula, and algebraicity sufficiency for rational quadratics in $\alpha(b,2)$), and Proposition 7.2 (two-class resonant-radix classification). Theorems A, 2.1, 3.4, and 6.3, Lemma 2.2, Propositions 3.1, 4.1, and 7.3, and Corollaries 4.3 and 7.4 are Lean-supported paper proofs combining formalized building blocks with written proofs (plus Ridout's restricted-denominator theorem for transcendence in Theorem 6.3, and a finite exact cycle enumeration for $b=5, D=9$ in Corollary 7.4). Lemma 3.2 and Proposition 3.3 are paper proofs, and Proposition 4.2 is an exact integer/rational finite certificate. No claim of ordinary normality is made for $\alpha(2,3)\alpha(2,5)$ or for $\alpha(b,2)^2 - 2\alpha(b,2)$. Independent human specialist review is outstanding.

## AI-use disclosure

> This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.

Suggested structured `ai_disclosure` ratings for owner confirmation on the AI Track form: `idea: ai`, `literature: ai`, `experiments: ai`, `analysis: ai`, `writing: ai` (project direction and release responsibility: Christopher Anderson).

## Pinned source and verification links (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`)

- Repository tree at pinned Lean checkpoint: `https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec`
- Lean verification & kernel replay record: `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md`
- Key Lean modules:
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFive.lean`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ProductThreeFiveInterpolation.lean`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase16StonehamBounds.lean`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/QuadraticPlateauSpectrum.lean`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ParameterTwoQuadraticOrbits.lean`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ResonantRadixClasses.lean`
- Exact Python certificate scripts:
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase16_mixed_product.py`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_mixed_product_orbits.py`
  - `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_dyadic_stoneham.py`
- Manuscript directory (on release branch): `papers/08-stoneham-product-orbits/` (`paper.tex`, `paper.pdf`, `VERIFICATION.md`, `LEDGER.md`, `metadata.toml`)

## Licence

CC BY 4.0 (select it in the alphaXiv form). Copyright 2026 Christopher Anderson. The licence covers this manuscript and its designated accompanying files; code in the repository is MIT. See `LICENSE-MANUSCRIPTS.md` in the repository.
