# Claim-to-source novelty ledger: Digit-Mass Transfer and Nonnormality of Dense Arithmetic Lambert Series (v1.1, candidate draft)

A search cannot prove novelty. "Not located in the sources examined" means only that the sources listed here, read as described, did not contain the statement. A failed search is recorded as a failed search and never as evidence of novelty. Every written proof and every comparison below has been checked only by AI models. **Cross-model review is not independent human peer review.** No human specialist has read the proofs.

Reading labels: **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[M]** our own deduction; **[U]** unverified.

## Scope

This ledger covers Candidate Paper XIV, v1.1 (Phase 26 Track H2). The draft assembles accepted sources pinned at two commits:

- **Phase 24** (`04969b91f0c897ce55d21cb62c6b2c5aa3affe97`, registered as `GF-36` and `GF-40`): Track A (`notes/phase24/dense-digit-mass-and-lambert.md`), Track E §3 (`notes/phase24/classical-constants-and-joint-numerators.md`, sub-track E3) and the Lean 4 module `NormalityChecker/DigitMassTransfer.lean`. Both entries passed independent third-provider deep analytic audit in Phase 25 Stage 0.2 Audit A (`notes/phase25/reviews/phase24-analytic-audit-gf36-gf37-gf40.md`, 0 Critical, 0 Major).
- **Phase 25** (`c06c97dd7d942bdf46d727aa58309869af88d5e7`, registered as `GF-44`): the Lean 4 module `NormalityChecker/NafGeometricTransfer.lean` (Track I blueprint `notes/phase25/naf-geometric-transfer.md`) and the base-2 bounds of Track D (`notes/phase25/digit-complexity-and-lp-witnesses.md`, Theorem 2.5). Both notes were accepted after repair (`notes/phase25/reviews/track-i-review.md`, `track-d-review.md`).

**Phase 25 Track H2 (`notes/phase25/historical-provenance-lambert.md`) ran a dedicated 9-topic primary-source provenance search** covering Erdős (1948), P. Borwein (1991, 1992), Bailey–Crandall (2002), BBCP (2004 §9), Crandall (2012), Senge–Straus / Stewart / Mauduit–Rivat, NAF weight literature (Reitwiesner 1960, Bosma 2001, Heuberger–Prodinger 2001/2006), Mira Cult Claim 0002, and Captain Sude (`PowerLambert`, r ≥ 2). No new literature search was run for v1.1. Every priority judgment remains provisional pending independent human specialist review.

**Benchmark scope.** No statement in this draft changes the status of any entry of the fixed 50-constant roster (`BC-01`…`BC-50`). The entries for E(2), E_odd(2) and E₊(2) (`BC-37`–`BC-39`) are unchanged; their normality, simple normality, D⁺ < 1 and K₂ status remain open, and the existing record for `BC-37` is preserved. The proved nonnormality results concern q = 2^k with k ≥ 3 and base-b families with b ≥ 3, none of which is a roster entry. No statement of the draft gives D⁺ < 1 for any constant; D⁺(E₊(8);2) < 1 is open.

**Numbering.** v1.1 inserted Theorem B and Section 6. The former Theorems B, C, D, E are now C, D, E, F; former Section 6 statements 6.1–6.13 are now 7.1–7.15 (with the new Lemma 7.6 and Remark 7.12); former Sections 7–8 are now 8–9.

## Bibliography verification

| Key | Status |
| --- | --- |
| `KN` | L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences* (1974). Standard reference for the equivalence of normality with D_N → 0 **[S]**. Same record as Papers XI–XIII. |
| `erdos1948` | P. Erdős, *J. Indian Math. Soc. (N.S.)* **12** (1948), 63–66. The Paper IX ledger records that the scan was read (p. 63): irrationality of f(1/t), and hence of E = E(2). Here it is cited for irrationality only **[S]** (via the Paper IX ledger). |
| `borwein1991`, `borwein1992` | P. B. Borwein, *J. Number Theory* **37** (1991), 253–259, and *Math. Proc. Cambridge Philos. Soc.* **112** (1992), 141–146. Metadata verified via Crossref in the Paper IX ledger; contents not examined **[A]**. Cited only as context for irrationality of these Lambert series, without a precise statement. |
| `PaperIX` | Anderson, Paper IX (manuscripts-v2.0.0), on finite-statistic obstructions for E(2). Project work; not peer reviewed. Cited as context for the open status of E(2). |
| `Kummer1852` | E. E. Kummer, *J. reine angew. Math.* **44** (1852), 93–146. Classical source of the carry interpretation of p-adic valuations of binomial coefficients **[U]**: bibliographic record from secondary sources, original not examined. Lemma 2.1 is proved in full, so nothing depends on this citation. |
| `Reitwiesner1960` | G. W. Reitwiesner, "Binary arithmetic", *Advances in Computers* **1** (1960), 231–308. **[U]**: bibliographic record only, as in the Paper XI ledger. In v1.0 the minimal weight of the non-adjacent form was an **External input** to Lemma 6.6. In v1.1 it is not: NAF existence, non-adjacency and minimality are proved in Theorem 6.1(a) and kernel-verified (`exists_naf`, `nafWeight_eq_signedWeight`, `signedWeight_natAbs_le_card_of_signed_sum`), and Lemma 7.7 cites that theorem. The reference is kept only for historical attribution (introduction, Theorem 7.8(b)). |
| `SengeStraus73` | H. G. Senge and E. G. Straus, *Period. Math. Hungar.* **3** (1973), 93–100. External input for Theorems 5.1–5.2: only finitely many integers have bounded digit sums in two multiplicatively independent bases **[S]** (as stated in the Track A note and its review); original not examined. |
| `Stewart80` | C. L. Stewart, *J. reine angew. Math.* **319** (1980), 63–72. Effective version of Senge–Straus **[S]**; original not examined. Not needed for any conclusion of this draft. |
| `Tenenbaum` | G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed. (2015). Cited for the Turán–Kubilius inequality (ω(n) → ∞ on a set of density 1) and for the Selberg–Delange method mentioned in the GF-31 comparison **[S]**. Specific theorem numbers were not checked for this draft. |
| `Wirsing1967` | E. Wirsing, *Acta Math. Acad. Sci. Hungar.* **18** (1967), 411–467. External input for Proposition 8.2: a real multiplicative function with \|f\| ≤ 1 and Σ(1 − f(p))/p = ∞ has mean 0 **[U]**: theorem as stated in secondary sources, original not examined (as in the Paper XI ledger). |
| `Maxfield53` | J. E. Maxfield, *Pacific J. Math.* **3** (1953), 189–196. Classical equivalence of normality in bases b and b^k **[S]**. In Theorem 7.9 it is only an alternative to the kernel-verified radix descent. |
| `Topacogullari17` | B. Topacogullari, "On a certain additive divisor problem", *Acta Arith.* **181** (2017), 143–172 (DOI `10.4064/aa8643-5-2017`; also arXiv:1512.05770). Theorem 1.2 (p. 145) and formula (3.20) (pp. 170–171, equal to (3.19) in arXiv v2) directly checked in Phase 25 Stage 0.2 Audit A **[R]**. Used only in Remark 7.15. |
| `BaileyCrandall2002` | D. H. Bailey and R. E. Crandall, *Exp. Math.* **11** (2002), 527–546. Primary text read in earlier repository audits **[R]** (Track H2 Topic 3). Cited for binary normality and 2-density context on E(2). |
| `BBCP2004` | D. H. Bailey, J. M. Borwein, R. E. Crandall, and C. Pomerance, *J. Théor. Nombres Bordeaux* **16** (2004), 487–518. Section 9 (Theorem 9.4 on θ₃(1/2)²) read directly in the Numdam PDF **[R]** (Track H2 Topic 3). |
| `Bosma2001`, `HeubergerProdinger2001` | W. Bosma, *J. Théor. Nombres Bordeaux* **13** (2001), 27–41; C. Heuberger and H. Prodinger, *Computing* **66** (2001), 377–393. Classical NAF asymptotic density 1/3 and fixed-boundary +2/9 integer overhead verified via Track H2 Topic 5 **[S]** (contrasted with our free-boundary −7/(18L) floor in Theorem 7.8). |
| `SudePowerLambert2026` | Captain Sude, `generalized-Lambert-disjunctivity-and-nonnormality` (commit `fe33be21`, Sept 2026). Statement checked in Phase 13 / Track H2 Topic 7 **[R]**: disjunctivity and nonnormality for sparse power-Lambert series Σ (b^{m^r} − 1)^{−1} (r ≥ 2), disjoint from linear-exponent (r = 1) dense Lambert series. |
| `Lean4`, `Mathlib` | Standard Lean 4 and Mathlib references, matching Papers XII–XIII. |

All 20 entries are cited in `paper.tex` (0 uncited, 0 undefined, 0 duplicates; checked mechanically for v1.1 and confirmed by a BibTeX run with 0 warnings).

---

### Theorem A (Lemmas 2.1–2.4, Theorem 2.5, Proposition 2.10, Lemma 3.1, Corollary 3.3, Proposition 3.4, Theorem 4.1): kernel-verified digit-mass transfer and E(2^k)

- **Evidence.** **Kernel-verified** in `DigitMassTransfer.lean` (62 exported theorems, no `sorry`), plus, for Lemma 2.3 in v1.1, the Phase 25 declarations `signedWeight_natAbs_le_card_of_signed_sum` and `exists_naf`. The surrounding written parts are labelled in `VERIFICATION.md`.
- **Closest results.**
  - Kummer's carry identity for two summands (`Kummer1852`) and the subadditivity and submultiplicativity of digit sums are classical **[S]**. The carry-run injection proof of w_b(a+c) ≤ w_b(a)+w_b(c), and the failure of w_b(ac) ≤ w_b(a)w_b(c) for b ≥ 3, are elementary **[M]**; we claim no novelty for these lemmas themselves. Our contribution here is their Lean 4 formalization in the form used for the transfer.
  - Lemma 3.1 is the classical convolution method for mean values of arithmetic functions whose Möbius kernel is absolutely summable against 1/n (Wintner-type arguments) **[U]**. No source for it is cited in `references.bib`, and none was checked for this draft. No novelty is claimed for the lemma; the formalization without Tauberian input is ours.
  - The irrationality of E(2) and of related Lambert series is due to Erdős and P. Borwein (`erdos1948`, `borwein1991`, `borwein1992`) **[S]/[A]**. Finite digit statistics of E(2) are discussed in `PaperIX`.
  - The simple nonnormality of E(2^k) in base 2 and in every base 2^j for every k ≥ 3, with D⁻(E(2^k);2) ≥ 1/2 − 29/(20k), was **not located in the sources examined**. No search of the literature on digit distribution of Lambert series at q = 2^k was run **[M]**.
- **Relation.** Not located in the sources examined; no exhaustive search.

### Theorem B (Theorems 6.1–6.2, Corollary 6.3, Lemma 7.6, Remark 7.12): kernel-verified non-adjacent geometric transfer and E₊(2^k) for k ≥ 3

- **Evidence.** Parts (i)–(iii), Theorems 6.1 and 6.2: **Kernel-verified** in `NafGeometricTransfer.lean` at `c06c97dd7d942bdf46d727aa58309869af88d5e7` (2,034 lines, no `sorry`, 39 declarations in `Audit.lean`, `leanchecker` replay on `hail`, GitHub Actions `Lean verification` run `46129564650`). Part (iv), Corollary 6.3: **Lean-supported paper proof** whose only further inputs are the **Finite certificates** W₊ ≤ 0.912845 (Track E) and W₊ ≤ 0.908184 (Track A Theorem 7.2), both independently re-certified by `scripts/phase25_naf_transfer.py` (re-run on `hail` for this draft: 418,091 assertions, exit 0). Lemma 7.6: **Paper proof** (new for this draft, elementary). Remark 7.12 cites the register entry `GF-44` and is not used in any proof.
- **Closest results.**
  - Existence and minimal weight of the non-adjacent form are classical (`Reitwiesner1960`) **[U]**, and so is the bound |Σ_{i<K} e_i 2^i| < (2/3)·2^K for non-adjacent digits (it is the value of 1010…, a standard NAF fact) **[M]/[U]**. We claim no novelty for them; they are proved here, and the Lean formalization is ours.
  - The orbit-covering count (at most r·w_±(A) shifts meet [c, 1 − c], c = (2/3)·2^{−sr}), the universal real transfer D_N(x;2^s) ≥ 1 − (4/3)2^{−sr} − rsρ − ε for prefix NAF density ρ, and the 5/16 exclusion of 4-normality were **not located in the sources examined [M]**. Within the project, the base-2 inequality D⁻(x;2) ≥ 2(1/3 − limsup σ₁/N) and the bounds D⁻(E₊(8);2) ≥ 17431/300000 and ≥ 0.061210 were first obtained in Phase 25 Track D (Theorems 2.3, 2.5); Track I re-derived them in finite-NAF geometric form, added the base-4 bounds, and supplied the Lean blueprint. The kernel-verified constant 21/500 (from the DP-free majorant bound 93694/100000) is the Phase 25 Lean formalization. Track I's review (`track-i-review.md`) required exactly this attribution, and the draft follows it.
  - The LP ceiling 0.059108 and the order-3 barrier ḡ₃ = 1/4 quoted in Remark 7.12 are Track D results (`GF-44`, Theorems 2.6 and 1.7) **[M]**; the draft states them as register results with their own evidence labels.
  - No literature search on signed-digit or NAF methods for normality of specific constants was run beyond Track H2 Topic 5 (NAF weight literature).
- **Relation.** Not located in the sources examined.

### Theorem C (Lemma 3.2, Theorem 4.2, the thresholds of Theorem 5.2, Theorems 5.3–5.4): sharp constants and dense divisor-type families

- **Evidence.** **Paper proof** + **Finite certificate** (`scripts/phase24_digit_mass.py`, 3,095,904 checks; Remark 4.3 also uses `scripts/phase24_classical.py`).
- **Closest results.**
  - Lemma 3.2 has the shape of the classical probabilistic (Kubilius-type) model for multiplicative functions, with independent geometric exponents **[U]**. Its application to submultiplicative digit functionals such as s₂ and w_± of τ(n) was not located in the sources examined **[M]**.
  - The certified mean C_true ∈ [1.339103, 1.339116] of s₂(τ(n)) is ours **[M]**. Whether the mean binary digit sum of τ(n) appears in the literature was **not searched [U]**.
  - The base-b τ_b and unitary families and their thresholds k₀(b) are our deductions **[M]**.
- **Relation.** Not located in the sources examined.

### Theorem D (Theorems 5.1–5.2, Lemma 2.2(c)): base-dependence barrier and multiplicative dependence

- **Evidence.** **Paper proof** + **External input** (Senge–Straus; Stewart; Turán–Kubilius). Part (iii) is **Kernel-verified**.
- **Closest results.** The finiteness of integers with bounded digit sums in two multiplicatively independent bases is due to Senge–Straus (`SengeStraus73`), with an effective form by Stewart (`Stewart80`) **[S]**. Its use to show that the mean base-b digit mass of τ(n) and τ_r(n) is infinite, and the resulting dichotomy, are our deductions **[M]**.
- **Relation.** The dichotomy is a statement about the *method*. It does not show that E(9), E(25) or E(100) is normal or nonnormal in its natural base, and those questions remain **Open**.

### Theorem E (Theorems 7.1, 7.2, 7.8, 7.9, 7.11, Proposition 7.3, Lemmas 7.5, 7.7, Proposition 7.14, Remarks 7.10, 7.15): transition counts, cubic-character series and the four-state transducer

- **Evidence.** (i) **Lean-supported paper proof**; (ii)–(iii) **Paper proof** + **Finite certificate**. In v1.1, Lemma 7.7 uses the kernel-verified non-adjacent form instead of the external input `Reitwiesner1960`.
- **Closest results.**
  - The asymptotic NAF density 1/3 of random integers is classical **[U]/[S]** (`Bosma2001`, `HeubergerProdinger2001`) and agrees with A_L → 1/3.
  - The transition-count transfer (Theorem 7.1), the free-boundary closed formula A_L = 1/3 − (7 − (−1/2)^{L−1})/(18L), the signed-support floor (Theorem 7.9), and the resulting nonnormality of E₊(2^k) for k ≥ 3 with D⁻ ≥ 2.34 × 10⁻⁷ were **not located in the sources examined [M]**. That last bound is superseded quantitatively by the kernel-verified 21/500 of Theorem B; the transducer route is kept as an independent proof.
  - The identity a₊(n) = τ(n) − 2·1_{2∣n} τ(n/2) and the exact shifted identities of Proposition 7.14 are elementary **[M]**. Remark 7.15 depends on `Topacogullari17` **[R]**.
  - The cubic-character series L_±(2^k) were treated in radix 2^k in the Phase 23 register entry `GF-31`, which uses Selberg–Delange as external input. Proposition 7.3 gives the base-2 statement without that input **[M]**.
- **Relation.** Not located in the sources examined.

### Theorem F (Theorems 8.1, 8.3, Propositions 8.2, 8.4): carry-density thresholds

- **Evidence.** **Paper proof**; Proposition 8.2 uses **External input** (Wirsing 1967); Proposition 8.4 is **Conditional**.
- **Closest results.** The exact carry-balance reformulations of simple normality for E(4) and E\*(4) follow directly from Theorem 2.6 **[M]**. The density of {n : τ(n) is a power of 4} uses Wirsing's mean-value theorem (`Wirsing1967`) **[U]**.
- **Relation.** These are reformulations and obstructions, not resolutions. E(2), E(4), E₊(2) and E₊(4) remain **Open**, as do the simple normality of E₊(8) in base 2, D⁺(E₊(8);2) < 1, and the positive density of the collision set of Proposition 8.4. The register entry `GF-42` gives written proofs of D⁺ < 1 for E(2^k) (k ≥ 3) and for E₊(2^k) only for k ≥ k₀ with k₀ > 3.05 × 10¹⁰; the draft cites them in Remark 7.13 and Question 9.5 and does not use them.

## Outstanding checks before release

1. Independent human specialist verification of the provisional priority claims recorded in `notes/phase25/historical-provenance-lambert.md` (especially MathSciNet/zbMATH/OEIS checks on C_true = lim X⁻¹ Σ s₂(τ(n)), on free-boundary NAF transducer floors, and on NAF-based orbit-covering arguments for the normality of specific constants) and primary-text verification of entries still marked **[S]** or **[U]** (`Kummer1852`, `Reitwiesner1960`, `Bosma2001`, `HeubergerProdinger2001`, `SengeStraus73`, `Stewart80`, `Wirsing1967`, `Maxfield53`).
2. Owner release authorization (`metadata.toml`, `papers/manifest.toml`, `papers/SHA256SUMS`, `docs/registry/papers.toml`, committed `paper.pdf`). *(Done for v1.1: commit pinning to `04969b91f0c897ce55d21cb62c6b2c5aa3affe97` and `c06c97dd7d942bdf46d727aa58309869af88d5e7` with 179 mechanically verified Lean links, and two reproducible clean `pdflatex`/`bibtex` builds on `hail` with identical SHA-256 `819fedf564cbed01ef4b29effdef6f79bed7eefbe6ce43305c4df9a5edf1d5f2`; see `VERIFICATION.md`.)*
