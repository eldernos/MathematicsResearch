# Resonance and discrepancy in signed Stoneham expansions

**Version 1.2** (named-author edition of version 1.1, `papers/03-signed-resonance`; the mathematics is unchanged). Preprint draft.

## Abstract

See [abstract.txt](abstract.txt).

## Authors

Christopher Anderson, Independent Researcher.

## Categories and keywords

Primary: math.NT (Number Theory). Cross-list: math.DS, math.CO.

Keywords: normal numbers, discrepancy, Stoneham numbers, signed expansions, cyclotomic polynomials, suffix-maximal words, de Bruijn words, Lean 4.

MSC2020: 11K16 (primary); 11K38, 11A63, 68R15 (secondary).

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the correspondence table. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.

## Source and verification links

- Lean declarations, pinned at Checkpoint 11: <https://github.com/eldernos/MathematicsResearch/tree/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker>. Every cited file is byte-identical at research-checkpoint-18, `e4809cf561573aef588e6ffc491a35cdb79fd9ec`.
- Manuscript directory: `papers/03-signed-resonance-v1.2/` in the release `manuscripts-v2.0.0`. **[RELEASE LINK: to be added by the owner when the release exists.]**
- Declaration-level map: `CORRESPONDENCE.md`; evidence labels: `VERIFICATION.md`.

## Verification scope

Theorems 1, 3, 7 and 11, Corollary 8 and the periodic maximum of Proposition 6 are kernel-verified as stated in the library's definitions (axioms `propext`, `Classical.choice`, `Quot.sound` only). Lemmas 2, 4 and 5, Proposition 9 and Theorem 10 are Lean-supported paper proofs. Equation (7) is a paper proof. Theorem 10 uses Roth's and Ridout's theorems as external inputs for its transcendence conclusions. The symbolic spectrum relies on the suffix-maximal words of Kaneko and Steiner, credited in the paper.
