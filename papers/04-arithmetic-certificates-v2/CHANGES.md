# Changes from Version 1.1 to Version 2.0

**Version 2.0 directory:** `papers/04-arithmetic-certificates-v2/`  
**Supersedes:** `papers/04-arithmetic-certificates/` (version 1.1, archived immutably at release `manuscripts-v1.1.0`)  
**Pinned Lean baseline:** `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (`research-checkpoint-18`; v1.1 was pinned to `a09e011720bc74396a27f4cb3ce2d8a5b3ce5035`)

---

## Summary of major changes

Version 2.0 consolidates the core certificate-and-obstruction theory of Paper IV (AC-01, AC-04, AC-02, AC-03, AC-10) with the systematic limitation results developed through checkpoint 18 (AC-11): finite-statistic countermodels separating odd-primary rational data and logarithmic word laws from ordinary normality, an eight-item taxonomy of method-specific proof barriers with paired witnesses, kernel-verified computability limitations on arbitrary digit-oracle program codes (`NormalityChecker/ComputableNormalityUndecidability.lean`), and a separate consistency-relative Rosser independence construction for theory-dependent digit programs.

All theorems, propositions, lemmas and corollaries now carry explicit Wave 2 evidence labels (`Kernel-verified`, `Lean-supported paper proof`, `Paper proof`), and the manuscript adopts the shared Wave 2 preamble, byline (Christopher Anderson, Independent Researcher), AI-use disclosure, metadata, verification map, novelty ledger, and submission package.

---

## Section-by-section mapping

| Version 1.1 (`papers/04-arithmetic-certificates/`) | Version 2.0 (`papers/04-arithmetic-certificates-v2/`) | Disposition |
| --- | --- | --- |
| §1 Rational approximations to digit shifts (Theorem 1, AC-01) & §2 Short sums on a fixed prime support (Theorem 2, AC-04) | §1 Normality from rational orbit models (Theorem 1.1 = AC-01; §1.1 Theorem 1.2 = AC-04) | Merged into §1; Theorem 1.2 explicitly titled as a qualitative form of Vandehey's Corollary 1.2; induction quantifiers tightened; Bailey–Crandall citation corrected to Theorems 3.2 and 4.8; Schmidt (1960), Wagner (1995), and Mira Cult (2026) added to literature positioning. |
| §3 Coverage and overlapping intervals: Proposition 3 (Partial coverage, AC-02) & fixed-mesh remark | §2 Partial coverage (Proposition 2.1 = AC-02 & fixed-mesh remark) | Retained with `Lean-supported paper proof` label noting Lean's specialization to radix orbits. |
| §3 Proposition 4 (Endpoint paths, AC-07) & §4 Joint denominator tests at several primes (Theorem 5 = AC-06, two-prime logarithmic density, worked $\{2,5,13\}$ example, Figure 1) | Archived in immutable v1.1 (cross-referenced briefly in §2 and §9) | Streamlined out of v2.0 body so v2.0 focuses cleanly on certificates and general limitations; the full unsigned localized-support classification resides in Paper II v2 (`papers/02-localized-normality-v2/`), while the $\{2,5,13\}$ first-precision enclosure remains reproducible via `scripts/overlap_certificate.py` and in archived v1.1. |
| §5 Separation on a shared segment (Theorem 6 = AC-03, Corollary 7, necessity examples) | §3 Separation on a shared segment (Theorem 3.1 = AC-03, Corollary 3.2, necessity examples) | Retained with updated `e4809cf` links and explicit evidence labels. |
| §6 A counting obstruction (Theorem 8 = AC-10) | §4 A counting obstruction (Theorem 4.1 = AC-10) | Retained with `Lean-supported paper proof` label isolating `few_symbol_words` from the paper measure/Borel–Cantelli deduction. |
| *(New in v2.0)* | §5 Countermodels for restricted data (Propositions 5.1–5.2: Pairs A and B, finite-prefix and de Bruijn remarks) | Added self-contained constructions separating odd-primary rational data (at error $<2^{-n}$) and logarithmic word laws (with disjunctivity) from ordinary normality. |
| *(New in v2.0)* | §6 Eight limits of particular methods (Items 1–8) | Added unified taxonomy of eight method-specific barriers with explicit comparisons and counterexamples (fixed-support certificates, overlaps/prescribed starts, nearby Taylor cutoffs, balanced trace sources, prime-by-prime statistics, higher-rank density/fixed projections, complex product endpoints, and irrationality exponents/digit runs). |
| *(New in v2.0)* | §7 Computability on digit-program names (Lemma 7.1, Proposition 7.2, Theorems 7.3–7.4, Corollary 7.5) | Added `Lean-supported paper proof` statements bundling individually kernel-verified finite-edit invariance, uniform forward/reverse halting reductions, s-m-n `Names` index maps, and nondecidability/non-c.e./non-co-c.e. exclusions under `TranscendentalZeroOnePromise` (parameterized by endpoint hypotheses), together with an elementary paper proof of two computable transcendental endpoints and full prior-art positioning (Ki–Linton 1994, Becher–Heiber–Slaman 2014/2015, Becher–Slaman 2014, Lutz–Mayordomo 2016/2021, Sierpiński, Turing, Rice, Specker). |
| *(New in v2.0)* | §8 Independence for theory-dependent descriptions (Theorem 8.1, Remark 8.2) | Added separate written section for the consistency-relative Rosser switch in PA and ZFC, with explicit uniform integer error bounds, weak-arithmetic scope note, and explicit statement that the results establish neither normality nor independence for named classical constants ($\ln 2, \pi, e, \sqrt{2}$, Erdős–Borwein). |
| §7 Formal correspondence and sources | §9 Formal verification and data availability & §10 Use of AI tools; companion `VERIFICATION.md`, `LEDGER.md`, `CHANGES.md`, `Check.lean`, `metadata.toml`, `submission/` | Upgraded to Wave 2 contract layout; registry IDs (`AC-01`–`AC-11`) and archived v1.1 references moved to §9; `Check.lean` expanded to audit 30 declarations (explicitly importing `PartialUniformity`) including all `ComputableNormalityUndecidability` theorems at `e4809cf`. |

---

## Resolution of v1.1 review findings carried into v2.0

- **Attribution of AC-04 (v1.1 Sonnet F1):** Theorem 1.2 is explicitly titled as a qualitative form of Vandehey's Corollary 1.2, and the induction quantifiers in its proof are stated explicitly (F10).
- **Bailey–Crandall pin-cites (v1.1 Sonnet F5a):** Corrected to Theorems 3.2 and 4.8.
- **Role of §4 `{2,5,13}` example (v1.1 Sonnet F2):** Removed from v2.0 body (retained in immutable v1.1 archive) with explicit note that Paper II gives the full unsigned localized-support classification.
- **Author attribution for `localized` (v1.1 Sonnet F5c):** Clarified in prose and `references.bib` that the PDF carries no individual author name and is hosted in the `CaptainSude/xi-normality` repository.
- **Definition of "arithmetic certificate" (v1.1 Sonnet F6):** Explicitly defined immediately after Theorem 1.1.
