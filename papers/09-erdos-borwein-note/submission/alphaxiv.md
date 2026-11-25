# Finite-statistic thresholds and statistical obstructions for the binary digits of the Erdős–Borwein constant

*A research note inviting collaboration (version 1.0, 25 November 2026)*

## Abstract

Let $E=\sum_{n\ge1}1/(2^n-1)$ be the Erdős–Borwein constant. Whether its binary digits are normal is open, and this note proves neither normality nor nonnormality. Writing $\tau(m)=2^{V(m)}U(m)$ with $U(m)$ odd, the digits of $E$ are governed by the integers $V(n+j)$ and $U(n+j)$. We compare them with an explicit random model of independent Poisson columns whose first-digit frequency lies in [0.492450290, 0.492460864] (finite certificate). Using an unconditional estimate for the mean discarded tail, we determine which finite statistics of this model would force a digit frequency below 1/2: one bounded statistic of 16 columns suffices, while for every $D\le 15$ there are exact countermodels with the same $D$-column law and tail mean whose first-digit frequency is at least 1/2. Exact joint laws of every set of at most four columns do not decide the bias. Factorial-moment information of order at most 4 never decides it, order at most 8 fails on 16 columns, and an explicit order-92 witness suffices. The parity inequality behind these statements is verified in Lean. A Selberg–Vaaler majorant of degree 116 suffices, whereas no trigonometric certificate of degree at most 110 exists. We list the arithmetic correlation estimates that would settle these statistics, audit the bit counts in Crandall's 2012 paper against exact digits, credit related public work of Campbell, Captain Sude and Mira Cult, and propose three concrete collaborative computations and estimates.

## Authors

Christopher Anderson (Independent Researcher)

## Categories

Primary: math.NT (Number Theory). Suggested cross-list: math.PR (Probability).

## Keywords

Erdős–Borwein constant; binary digits; normal numbers; divisor function; Poisson model; parity Bonferroni inequality; Selberg–Vaaler majorant; research note

## MSC 2020

Primary 11K16. Secondary 11N37, 11Y60, 11K06.

## Status and scope

This is a research note, not an announcement of a result about normality. It does **not** prove that the Erdős–Borwein constant is normal or that it is not normal. The theorems concern which finite statistics of an explicit random model would suffice, or provably not suffice, to force a binary digit frequency different from 1/2. Each statement carries one evidence label (kernel-verified, Lean-supported paper proof, paper proof, finite certificate, conditional, external input). The note ends with three concrete collaboration targets.

## Use of AI tools

This manuscript was produced in an AI-assisted research project. Large language models proposed conjectures and proof strategies, wrote the proofs and the text, implemented the exact computations and Lean 4 formalizations, searched the literature and reviewed drafts across several model providers. The repository owner directed the project and is responsible for its release. The Lean kernel checked the declarations listed in the verification map. The written proofs, literature comparisons and priority statements have been checked only by AI models from different providers. They have not been checked by an independent human expert. Cross-model review is not peer review.

## Source and verification links (pinned)

- Repository at research-checkpoint-18: https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec
- Note directory (paper, bibliography, ledger, verification map): `papers/09-erdos-borwein-note/` on the `publication/wave-2` branch. The pinned checkpoint predates the note, so replace this line with the release commit link once the branch is tagged.
- Lean declarations used: [`carry_knapsack_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L375), [`parity_bonferroni_dual_le`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase17DiscrepancyBounds.lean#L432), [`source_phase`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L16), [`arrival_sum`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L41), [`one_bit_carry`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/ErdosBorweinArrivals.lean#L86)
- Certificate script: [`scripts/phase17_erdos_borwein_bias.py`](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/scripts/phase17_erdos_borwein_bias.py) (standard library only, about 20 s, ends with "all assertions passed")

## Verification scope

Lean checks two pointwise inequalities (the carry-knapsack dual and the parity Bonferroni dual) and three finite identities. Nothing in the note is completely kernel-verified: the tail-mean estimate, the linear-programming and dynamic-programming certificates, the Jordan-inversion argument for the order-92 witness and the Fourier computations are written proofs or computations. The Fourier-side certificates use IEEE arithmetic with explicit error radii rather than interval arithmetic. The Selberg–Vaaler majorant inequality is quoted from Vaaler (1985); we could not confirm its theorem number. The written proofs have been checked only by AI models; no human specialist has reviewed them.
