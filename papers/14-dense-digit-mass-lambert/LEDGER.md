# Claim-to-source novelty ledger: Digit-Mass Transfer and Nonnormality of Dense Arithmetic Lambert Series (v1.0, candidate draft)

A search cannot prove novelty. "Not located in the sources examined" means only that the sources listed here, read as described, did not contain the statement. A failed search is recorded as a failed search and never as evidence of novelty. Every written proof and every comparison below has been checked only by AI models. **Cross-model review is not independent human peer review.** No human specialist has read the proofs.

Reading labels: **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[M]** our own deduction; **[U]** unverified.

## Scope

This ledger covers Candidate Paper XIV. The draft assembles three accepted Phase 24 sources: Track A (`notes/phase24/dense-digit-mass-and-lambert.md`), Track E §3 (`notes/phase24/classical-constants-and-joint-numerators.md`, sub-track E3), and the Lean 4 module `NormalityChecker/DigitMassTransfer.lean` (working tree, pending commit pinning before release). It also refers to the Phase 23 register entry `GF-31` for comparison. **No dedicated new external literature search was run for this candidate draft.** The priority statements below rest on the prior-art remarks already recorded in the source notes and in earlier ledgers of this project, and every priority question is therefore marked conservatively.

**Benchmark scope.** No statement in this draft changes the status of any entry of the fixed 50-constant roster (`BC-01`…`BC-50`). The entries for E(2), E_odd(2) and E₊(2) (`BC-37`–`BC-39`) are unchanged; their normality, simple normality, D⁺ < 1 and K₂ status remain open, and the existing record for `BC-37` is preserved. The proved nonnormality results concern q = 2^k with k ≥ 3 and base-b families with b ≥ 3, none of which is a roster entry.

## Bibliography verification

| Key | Status |
| --- | --- |
| `KN` | L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences* (1974). Standard reference for the equivalence of normality with D_N → 0 **[S]**. Same record as Papers XI–XIII. |
| `erdos1948` | P. Erdős, *J. Indian Math. Soc. (N.S.)* **12** (1948), 63–66. The Paper IX ledger records that the scan was read (p. 63): irrationality of f(1/t), and hence of E = E(2). Here it is cited for irrationality only **[S]** (via the Paper IX ledger). |
| `borwein1991`, `borwein1992` | P. B. Borwein, *J. Number Theory* **37** (1991), 253–259, and *Math. Proc. Cambridge Philos. Soc.* **112** (1992), 141–146. Metadata verified via Crossref in the Paper IX ledger; contents not examined **[A]**. Cited only as context for irrationality of these Lambert series, without a precise statement. |
| `PaperIX` | Anderson, Paper IX (manuscripts-v2.0.0), on finite-statistic obstructions for E(2). Project work; not peer reviewed. Cited as context for the open status of E(2). |
| `Kummer1852` | E. E. Kummer, *J. reine angew. Math.* **44** (1852), 93–146. Classical source of the carry interpretation of p-adic valuations of binomial coefficients **[U]**: bibliographic record from secondary sources, original not examined. Lemma 2.1 is proved in full, so nothing depends on this citation. |
| `Reitwiesner1960` | G. W. Reitwiesner, "Binary arithmetic", *Advances in Computers* **1** (1960), 231–308. Cited for the non-adjacent form and its minimal weight, which Lemma 6.6 uses as **External input** **[U]**: bibliographic record only, as in the Paper XI ledger. |
| `SengeStraus73` | H. G. Senge and E. G. Straus, *Period. Math. Hungar.* **3** (1973), 93–100. External input for Theorems 5.1–5.2: only finitely many integers have bounded digit sums in two multiplicatively independent bases **[S]** (as stated in the Track A note and its review); original not examined. |
| `Stewart80` | C. L. Stewart, *J. reine angew. Math.* **319** (1980), 63–72. Effective version of Senge–Straus **[S]**; original not examined. Not needed for any conclusion of this draft. |
| `Tenenbaum` | G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed. (2015). Cited for the Turán–Kubilius inequality (ω(n) → ∞ on a set of density 1) and for the Selberg–Delange method mentioned in the GF-31 comparison **[S]**. Specific theorem numbers were not checked for this draft. |
| `Wirsing1967` | E. Wirsing, *Acta Math. Acad. Sci. Hungar.* **18** (1967), 411–467. External input for Proposition 7.2: a real multiplicative function with \|f\| ≤ 1 and Σ(1 − f(p))/p = ∞ has mean 0 **[U]**: theorem as stated in secondary sources, original not examined (as in the Paper XI ledger). |
| `Maxfield53` | J. E. Maxfield, *Pacific J. Math.* **3** (1953), 189–196. Classical equivalence of normality in bases b and b^k **[S]**. In Theorem 6.8 it is only an alternative to the kernel-verified radix descent. |
| `Topacogullari17` | B. Topacogullari, "On a certain additive divisor problem", arXiv:1512.05770; year 2017 as cited in the Track E note. Theorem 1.2 and §3.5 were identified by the Track E reviewer **[S]**; the post-repair verifier did not re-read the text. Used only in Remark 6.13. |
| `Lean4`, `Mathlib` | Standard Lean 4 and Mathlib references, matching Papers XII–XIII. |

---

### Theorem A (Lemmas 2.1–2.4, Theorem 2.5, Proposition 2.10, Lemma 3.1, Corollary 3.3, Proposition 3.4, Theorem 4.1): kernel-verified digit-mass transfer and E(2^k)

- **Evidence.** **Kernel-verified** in `DigitMassTransfer.lean` (working tree; 62 exported theorems, no `sorry`). The surrounding written parts are labelled in `VERIFICATION.md`.
- **Closest results.**
  - Kummer's carry identity for two summands (`Kummer1852`) and the subadditivity and submultiplicativity of digit sums are classical **[S]**. The carry-run injection proof of w_b(a+c) ≤ w_b(a)+w_b(c), and the failure of w_b(ac) ≤ w_b(a)w_b(c) for b ≥ 3, are elementary **[M]**; we claim no novelty for these lemmas themselves. Our contribution here is their Lean 4 formalization in the form used for the transfer.
  - Lemma 3.1 is the classical convolution method for mean values of arithmetic functions whose Möbius kernel is absolutely summable against 1/n (Wintner-type arguments) **[U]**. No source for it is cited in `references.bib`, and none was checked for this draft. No novelty is claimed for the lemma; the formalization without Tauberian input is ours.
  - The irrationality of E(2) and of related Lambert series is due to Erdős and P. Borwein (`erdos1948`, `borwein1991`, `borwein1992`) **[S]/[A]**. Finite digit statistics of E(2) are discussed in `PaperIX`.
  - The simple nonnormality of E(2^k) in base 2 and in every base 2^j for every k ≥ 3, with D⁻(E(2^k);2) ≥ 1/120, was **not located in the sources examined**. No search of the literature on digit distribution of Lambert series at q = 2^k was run **[M]**.
- **Relation.** Not located in the sources examined; no exhaustive search.

### Theorem B (Lemma 3.2, Theorem 4.2, the thresholds of Theorem 5.2, Theorems 5.3–5.4): sharp constants and dense divisor-type families

- **Evidence.** **Paper proof** + **Finite certificate** (`scripts/phase24_digit_mass.py`, 3,095,904 checks; Remark 4.3 also uses `scripts/phase24_classical.py`).
- **Closest results.**
  - Lemma 3.2 has the shape of the classical probabilistic (Kubilius-type) model for multiplicative functions, with independent geometric exponents **[U]**. Its application to submultiplicative digit functionals such as s₂ and w_± of τ(n) was not located in the sources examined **[M]**.
  - The certified mean C_true ∈ [1.339103, 1.339116] of s₂(τ(n)) is ours **[M]**. Whether the mean binary digit sum of τ(n) appears in the literature was **not searched [U]**.
  - The base-b τ_b and unitary families and their thresholds k₀(b) are our deductions **[M]**.
- **Relation.** Not located in the sources examined.

### Theorem C (Theorems 5.1–5.2, Lemma 2.2(c)): base-dependence barrier and multiplicative dependence

- **Evidence.** **Paper proof** + **External input** (Senge–Straus; Stewart; Turán–Kubilius). Part (iii) is **Kernel-verified**.
- **Closest results.** The finiteness of integers with bounded digit sums in two multiplicatively independent bases is due to Senge–Straus (`SengeStraus73`), with an effective form by Stewart (`Stewart80`) **[S]**. Its use to show that the mean base-b digit mass of τ(n) and τ_r(n) is infinite, and the resulting dichotomy, are our deductions **[M]**.
- **Relation.** The dichotomy is a statement about the *method*. It does not show that E(9), E(25) or E(100) is normal or nonnormal in its natural base, and those questions remain **Open**.

### Theorem D (Theorems 6.1, 6.2, 6.7, 6.8, 6.10, Proposition 6.3, Lemmas 6.5–6.6, Proposition 6.12, Remarks 6.9, 6.13): signed transfer, E₊(2^k) and the transducer

- **Evidence.** (i) **Lean-supported paper proof**; (ii)–(iii) **Paper proof** + **Finite certificate**, with **External input** (NAF minimality, `Reitwiesner1960`) in Lemma 6.6.
- **Closest results.**
  - The non-adjacent form and its minimality are classical (`Reitwiesner1960`) **[U]**. The asymptotic NAF density 1/3 of random integers is classical folklore **[U]** and agrees with A_L → 1/3; no source for the density is cited.
  - The transition-count transfer (Theorem 6.1), the free-boundary closed formula A_L = 1/3 − (7 − (−1/2)^{L−1})/(18L), the signed-support floor (Theorem 6.8), and the resulting nonnormality of E₊(2^k) for k ≥ 3 were **not located in the sources examined [M]**. No search of the literature on signed-digit complexity of normal numbers was run.
  - The identity a₊(n) = τ(n) − 2·1_{2∣n} τ(n/2) and the exact shifted identities of Proposition 6.12 are elementary **[M]**. Remark 6.13 depends on `Topacogullari17` **[S]**.
  - The cubic-character series L_±(2^k) were treated in radix 2^k in the Phase 23 register entry `GF-31`, which uses Selberg–Delange as external input. Proposition 6.3 gives the base-2 statement without that input **[M]**.
- **Relation.** Not located in the sources examined.

### Theorem E (Theorems 7.1, 7.3, Propositions 7.2, 7.4): carry-density thresholds

- **Evidence.** **Paper proof**; Proposition 7.2 uses **External input** (Wirsing 1967); Proposition 7.4 is **Conditional**.
- **Closest results.** The exact carry-balance reformulations of simple normality for E(4) and E\*(4) follow directly from Theorem 2.6 **[M]**. The density of {n : τ(n) is a power of 4} uses Wirsing's mean-value theorem (`Wirsing1967`) **[U]**.
- **Relation.** These are reformulations and obstructions, not resolutions. E(2), E(4), E₊(2) and E₊(4) remain **Open**, and so does the positive density of the collision set of Proposition 7.4.

## Outstanding checks before release

1. Run a targeted literature search on: (a) mean values of digit sums of the divisor function, such as the mean of s₂(τ(n)); (b) digit distribution, simple normality and nonnormality of Lambert series Σ 1/(q^n ± 1) for q = 2^k; (c) signed-digit (NAF) complexity of normal numbers and of free-boundary words; (d) carry-based methods for digit frequencies of dense series. Record each source with a reading label.
2. Verify against primary texts or Crossref the records marked **[U]** or **[S]**: `Kummer1852`, `Reitwiesner1960`, `SengeStraus73`, `Stewart80`, `Wirsing1967`, `Maxfield53`, and the theorem number and year of `Topacogullari17`. Add a reference for Lemma 3.1 (Wintner-type mean values) or keep the explicit no-novelty disclaimer.
3. Compile the PDF (`pdflatex` × 3 + `bibtex`) and inspect numbering, layout and overfull boxes.
4. Commit and pin `NormalityChecker/DigitMassTransfer.lean`, `notes/phase24/` (with reviews), `scripts/phase24_digit_mass.py` and `scripts/phase24_classical.py`. Replace the working-tree Lean citations with commit-pinned links, and enter the Phase 24 registry entries.
