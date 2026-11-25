# alphaXiv / Preprint Submission Draft — Paper IV (Version 2.0)

*Draft for repository owner approval. Do not upload without owner authorization.*

- **Title:** Arithmetic Certificates for Normality and Mathematical Limitations
- **Version:** 2.0 (supersedes `papers/04-arithmetic-certificates`, version 1.1)
- **Authors:** Christopher Anderson
- **Affiliation:** Independent Researcher
- **Contact:** Corrections and comments via the repository issue tracker (`https://github.com/eldernos/MathematicsResearch/issues`)
- **Primary category:** `math.NT` (Number Theory)
- **Secondary categories:** `math.LO` (Logic), `cs.LO` (Logic in Computer Science)
- **MSC2020 Primary:** `11K16` (Normal numbers, radix expansions, Pisot numbers, Salem numbers, good lattice points, etc.)
- **MSC2020 Secondary:** `11K38`, `03D35`, `03F40`, `68V20`
- **Keywords:** normal numbers, discrepancy, exponential sums, rational orbit approximation, overlap rigidity, computable analysis, undecidability, Rosser independence, Lean 4

## Abstract

A radix orbit in base $b \ge 2$ is equidistributed if, for every positive tolerance and denominator floor, almost all blocks on a prescribed geometric schedule admit rational models with mean circle error below the tolerance, reduced denominators above the floor on a fixed prime support coprime to $b$, and denominators bounded by a fixed power of the block length. Partial coverage by disjoint low-discrepancy pieces yields a quantitative upper bound on the limiting discrepancy. Conversely, accurate fixed-support models on sufficiently long overlaps must agree modulo one after alignment (forcing eventually constant denominators along a chain), and a counting estimate (Theorem 4.1) shows that polynomial-denominator rational models meeting the mean circle error threshold $1/(16b^4)$ on an independently prescribed geometric schedule with polynomially many starts per scale occur only finitely often for Lebesgue-almost every real number.

Explicit pairs of computable binary streams separate odd-primary rational data (at error $< 2^{-n}$) and logarithmic word laws from ordinary normality, and eight barriers isolate the information lost by specific proof methods. Two uniform halting reductions show that neither binary normality nor nonnormality is computably enumerable on digit-program codes, even for transcendental values with limiting discrepancy $0$ or $1$. Lean 4 checks the fixed-support estimate, uniform overlap separation, certificate transfer, radix-orbit coverage bounds, the finite weighted word inequality of Theorem 4.1, and (under endpoint hypotheses) each individual halting-reduction and nonrecognizability declaration. A written Rosser argument gives consistency-relative independence for a theory-dependent digit program, establishing neither normality nor independence for classical constants.

## Source and verification links

### Pinned Lean 4 baseline (`e4809cf561573aef588e6ffc491a35cdb79fd9ec`)

- **Repository baseline:** https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec
- **Lean 4 modules:**
  - `NormalityChecker/ArithmeticCertificate.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ArithmeticCertificate.lean
  - `NormalityChecker/SmoothOrbit.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean
  - `NormalityChecker/QualityCoverage.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/QualityCoverage.lean
  - `NormalityChecker/PartialUniformity.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PartialUniformity.lean
  - `NormalityChecker/OrbitRigidity.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/OrbitRigidity.lean
  - `NormalityChecker/ModelCounting.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ModelCounting.lean
  - `NormalityChecker/ComputableNormalityUndecidability.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ComputableNormalityUndecidability.lean
- **Exact finite check script:** https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_limitations.py
- **Checkpoint verification record:** https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md

### Manuscript revision files (version 2.0; postdates `e4809cf`)

*(Pin to the immutable `manuscripts-v2.0.0` release tag once published.)*

- **Manuscript directory:** https://github.com/eldernos/MathematicsResearch/tree/publication/wave-2/papers/04-arithmetic-certificates-v2
- **LaTeX source (`paper.tex`):** https://github.com/eldernos/MathematicsResearch/blob/publication/wave-2/papers/04-arithmetic-certificates-v2/paper.tex
- **Statement and axiom check (`Check.lean`):** https://github.com/eldernos/MathematicsResearch/blob/publication/wave-2/papers/04-arithmetic-certificates-v2/Check.lean
- **Verification map (`VERIFICATION.md`):** https://github.com/eldernos/MathematicsResearch/blob/publication/wave-2/papers/04-arithmetic-certificates-v2/VERIFICATION.md

## Verification scope

Each numbered result in the manuscript carries an explicit evidence label. Lean 4.36.0 (replayed at trust level 0 at commit `e4809cf` with only `propext`, `Classical.choice`, and `Quot.sound`) completely verifies two single-declaration manuscript theorems: the qualitative fixed-support exponential-sum estimate (Theorem 1.2, after Vandehey's Corollary 1.2) and the uniform overlap-separation inequality (Theorem 3.1). The remaining formal links support **Lean-supported paper proof** statements: Theorem 1.1 composes two kernel-verified declarations directly; Proposition 2.1 uses four kernel-verified radix-orbit specializations; Corollary 3.2 bundles two individually verified overlap declarations; Theorem 4.1 uses Lean only for the finite weighted word inequality (`few_symbol_words`), while uniformity of the shifted point, the cylinder probability calculation, the union bound over rational models, and the Borel–Cantelli deduction are written; Lemma 7.1 and Theorems 7.3–7.4 bundle individually kernel-verified finite-edit, halting-reduction, and nonrecognizability declarations over `Nat.Partrec.Code` under explicit endpoint hypotheses, while the two-way transcendence deduction, bundling, endpoint existence (Proposition 7.2), and the partial-decider consequence (Corollary 7.5) are written. Propositions 5.1–5.2, the eight method obstructions in Section 6, Proposition 7.2, and the consistency-relative PA/ZFC Rosser independence construction (Theorem 8.1) are written paper proofs.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
