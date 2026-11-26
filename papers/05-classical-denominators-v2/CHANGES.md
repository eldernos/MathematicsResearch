# Changes in version 2.0

The revision supersedes Paper V v1.1. It uses the title *Denominator Growth and Rational Shadowing for Classical Constants* and the approved Christopher Anderson byline. The v1.1 sources, proofs, PDF, review records and tags remain in their published locations. [v1.1 manuscript](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/papers/05-classical-denominators/paper.pdf) · [Review guide](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/papers/05-classical-denominators/REVIEW.md) · [Correspondence map](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/papers/05-classical-denominators/CORRESPONDENCE.md)

| v1.1 section | v2.0 treatment |
| --- | --- |
| §§1–2, representations and prime cancellation | §§1–3 give the prime-band proof and fixed real optimum, then extend them to signed Gaussian sources and all balanced traces. §4 gives adaptive-height bounds and nearby Taylor cutoffs. The v1.1 quantitative cancellation estimates remain in the archive. |
| §3, signed integral corrections | §5 develops prescribed-shift Chebyshev and Legendre moment constructions. The earlier beta-integral estimates remain in v1.1. |
| §§4–5, prescribed numerators and binary word exclusions | §6 isolates the general window–denominator inequality and states the numeral and distribution limits explicitly. The detailed diagonal-residue and finite word estimates remain in v1.1. |
| §6, arctangents and π | §§5 and 7 include the even-Legendre all-shift construction, the Gaussian (2/3) rate and separate reduced-denominator proofs for the literal BBP and Bellard prefixes. |
| §7, factorial truncations | §7 retains a factorial and continued-fraction comparison and adds the obstruction to positive dyadic grouping. The periodic-numerator estimates remain in v1.1. |
| §8, discrepancy and finite observations | §§1, 6 and 7 delimit the digit conclusions for the five named constants. §8 gives exact regrouping results and a differential-algebra obstruction. |
| §9, formal verification | §10 and the companion map identify the Lean declarations, paper deductions, external dependencies and finite computations separately. |

The finite arithmetic of word counts, transition certificates and Fourier statistics belongs with revised Paper IV. The geometric-ray argument here concerns exact representations of two specific constants and finite collections of components. General summation and growing-support constructions are treated in the synthetic expansions manuscript (Paper C). This revision includes the arithmetic used in its own arguments and retains links to v1.1 for the omitted detail.

The unrefined Legendre numerator agrees with nearest-grid rounding under the stated tie separation test. A rational refinement returns the exact nearest point on the same grid. For unbalanced traces the revision gives upper bounds for shifted error and dyadic denominator cost. A general lower bound would require a separate sampling and cancellation argument. The window estimates are upper bounds on the required denominators. Independent human specialist review is outstanding.

Section 9 incorporates the approved follow-up checkpoint. It gives the exact minimum $p\,k(p)$ for one prime, the mean Taylor denominator-loss bound $O(X^{3/7})$, a superpolynomial period bound for the actual reduced moduli, a sharp threshold for the signed moving cutoff, and a finite discrepancy algorithm for individual horizontal rows. The period bound concerns complete periods and returns modulo the complement of one prime axis. [Follow-up verification](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/notes/phase19/verification.md)

## Revision after referee report 1

The manuscript was revised on 25 November 2026 in response to `papers/reviews/05-classical-denominators-v2/review-1.md`. The resolution is in `papers/reviews/05-classical-denominators-v2/resolution.md`. The version number remains 2.0. Principal changes, with the sections of the revised manuscript:

| Change | Location |
| --- | --- |
| The windows and grid exponents of the rounded Chebyshev and Legendre models are stated to be nearest-grid roundings, available for every real number, and are separated from the floors of §§2–4. The excess window $G_N$ is defined. | Abstract, §1, §5 (opening, Theorem 5.3, new Remark 5.4), §6, §10 |
| Window, prefix function, cell and balanced source defined at first use. | §1, §2 |
| Antecedents added: Størmer, Todd, Borwein–Borwein–Galway, Eswarathasan–Levine, Boyd, Shiu, Rogers, Brisebarre; Rivoal's theorems stated precisely. | §1, §2, bibliography, ledger |
| Parts I, II and III marked. Part III (§§7–9) keeps its sections and numbering. A roadmap paragraph and a final section "Scope and open questions" (§10) are added. | §1, §§2, 5, 7, 10 |
| Proofs of Theorem 3.1, Proposition 7.2, Theorem 8.2 and Theorem 9.5 expanded into numbered steps. | §3, §7, §8, §9 |
| Former Theorem 4.1 split into Theorem 4.1 (Lean-supported rate) and Proposition 4.2 (linear thresholds, Finite certificate). Later numbers in §4 shift by one. Theorem 8.2 relabelled Paper proof. Theorem 5.2 label line says what Lean checks. | §4, §5, §8 |
| The Catalan-type series for $\sqrt2$ and $\varphi$ ($\sqrt{1+4x}$ at $x=2^{-5},2^{-4}$) is removed. It is used nowhere else and has no verification row. | former §7 |
| Unverifiable citations marked; Takahashi equation numbers removed; Hadamard and Bailey–Crandall locators checked; Mira Cult cited as an unrefereed AI-assisted note by commit. | bibliography, §11 |
| Corrupted characters in `VERIFICATION.md` restored; announcement, abstract, summary, packet and inquiry updated. The abstract is now the same in the paper, `metadata.toml` and `submission/`. | companion files |
