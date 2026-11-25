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

A radix orbit in base $b \ge 2$ is equidistributed if almost all blocks on a prescribed geometric schedule admit small mean-error rational models whose reduced denominators grow on a fixed prime support coprime to $b$ and stay bounded by a fixed power of the block length. Partial coverage by disjoint low-discrepancy pieces yields a quantitative upper bound on the limiting discrepancy. Conversely, two structural obstructions limit such certificates: accurate models on sufficiently long overlaps must agree modulo one after alignment (forcing eventually constant denominators along a chain), and a counting estimate shows that polynomial-denominator approximations on prescribed geometric schedules occur only finitely often for Lebesgue-almost every real number.

Explicit pairs of computable binary streams separate odd-primary rational data (at per-shift error $< 2^{-n}$) and logarithmic word laws (with disjunctivity) from ordinary normality, and eight targeted barriers isolate the information lost by specific normality-proof methods. Finally, two uniform bounded-evaluation halting reductions show that neither binary normality nor nonnormality is computably enumerable on arbitrary digit-program codes, even under the promise that the named real is transcendental with limiting binary discrepancy $0$ or $1$. Lean 4 checks the certificate, overlap-rigidity, word-counting, and halting-reduction theorems (the latter under explicit endpoint hypotheses). A separate written Rosser argument establishes consistency-relative independence for the normality sentence of a theory-dependent digit program in PA and ZFC, with no implication for any named classical constant.

## Source and verification links (pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec`)

- **Repository baseline:** https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec
- **Lean 4 modules:**
  - `NormalityChecker/ArithmeticCertificate.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ArithmeticCertificate.lean
  - `NormalityChecker/SmoothOrbit.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean
  - `NormalityChecker/QualityCoverage.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/QualityCoverage.lean
  - `NormalityChecker/OrbitRigidity.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/OrbitRigidity.lean
  - `NormalityChecker/ModelCounting.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ModelCounting.lean
  - `NormalityChecker/ComputableNormalityUndecidability.lean`: https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ComputableNormalityUndecidability.lean
- **Exact finite check script:** https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_limitations.py
- **Checkpoint verification record:** https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/notes/phase18/verification.md

## Verification scope

Each numbered result in the manuscript carries an explicit evidence label. Lean 4.36.0 (replayed at trust level 0 at commit `e4809cf` with only `propext`, `Classical.choice`, and `Quot.sound`) completely verifies the qualitative fixed-support exponential-sum estimate (Theorem 1.2, after Vandehey's Corollary 1.2), the uniform overlap-separation inequality (Theorem 3.1), finite-edit dyadic invariance (Lemma 7.1), and the uniform halting reductions and nonrecognizability theorems over arbitrary digit-oracle codes `Nat.Partrec.Code` under explicit endpoint hypotheses (Theorems 7.3–7.4). Theorem 1.1 composes two kernel-verified declarations directly; Proposition 2.1, Corollary 3.2, Theorem 4.1, and Corollary 7.5 are Lean-supported paper proofs combining kernel-verified steps with written arguments. Propositions 5.1–5.2, the eight method obstructions in Section 6, the elementary endpoint existence proof (Proposition 7.2), and the consistency-relative PA/ZFC Rosser independence construction (Theorem 8.1) are written paper proofs.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.
