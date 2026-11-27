# Claim-to-source novelty ledger: All-Prime Polynomial Normality and Optimal Irrationality Exponents (v1.0, candidate draft)

A search cannot prove novelty. "Not located in the sources examined" means only that the sources listed here, read as described, did not contain the statement. A failed search is recorded as a failed search and never as evidence of novelty. Every written proof and every comparison below has been checked only by AI models. **Cross-model review is not independent human peer review**, and no human specialist has read the proofs.

Reading labels: **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[M]** our own deduction; **[U]** unverified.

## Scope

This ledger covers the material split off from the candidate Paper VII v2.0 (its former §9; see [`../07-synthetic-expansions-v2/CHANGES.md`](../07-synthetic-expansions-v2/CHANGES.md)), together with the Phase 23 Track C3–C4 additions. For the moved material, the literature positions repeat those of the [Paper VII v2.0 ledger](../07-synthetic-expansions-v2/LEDGER.md) as they stood before the split (entry "Theorem F"). **No new literature search was run for this draft.** The one exception is a bibliographic lookup of 27 November 2026: a web search confirmed the title, journal and DOI of Ghidelli's paper (arXiv listing), the volume and pages of Shallit (1979), and the author list of the DEKKM accepted manuscript.

## Bibliography verification

| Key | Status |
| --- | --- |
| `PaperVIIv2` | This project's companion candidate draft (unreleased), `papers/07-synthetic-expansions-v2`. Statement numbers 7.10, 7.18, 7.20, 7.23 and 7.24 come from a structural count of its `paper.tex` (27 November 2026), not from a compiled PDF **[R]**. |
| `PaperIv2` | Paper I v2.0, release `manuscripts-v2.0.0`. The statements of Lemmas 2.2–2.4 (paper proofs there) were read on 26 November 2026 for Paper VII v2.0 **[R]**. They were not re-read for this draft. |
| `Manai25` | arXiv:2508.09319. Only the abstract was read **[A]**; the theorem was not read. |
| `Shallit79` | J. Shallit, *J. Number Theory* **11** (1979) 209–217. Volume and pages were confirmed by web search against later citing literature; the DOI was not verified and is omitted **[S]**. The folding lemma for $\sum u^{-2^k}$ is attributed as in the Phase 23 Track C review, which did not re-read the source **[S]**. |
| `vdPS92` | A. J. van der Poorten and J. Shallit, *Folded continued fractions*, *J. Number Theory* **40** (1992) 237–250. The entry is copied from the Paper IV v2.0 bibliography **[S]**; the primary text was not read. |
| `DEKKM` | Dietmann, Elsholtz, Kalmynin, Konyagin and Maynard, IMRN, doi:10.1093/imrn/rnac130. Theorem 1 ($390/449$) was checked against the accepted manuscript by the Phase 23 Track C review **[S]**. It is cited here only as context (it is used in Paper VII v2.0); volume, pages and typeset numbering are **[U]**. |
| `Ghidelli20` | L. Ghidelli, *Arbitrarily long gaps between the values of positive-definite cubic and biquadratic diagonal forms*, J. London Math. Soc., doi:10.1112/jlms.12312, arXiv:1910.05070. The title was confirmed from the arXiv listing. Theorem 1.1 was checked by the Phase 23 Track C review **[S]**; volume and pages are **[U]**. Context only. |
| `Roth55`, `HR74`, `HW08` | As in the Paper VII v2.0 ledger **[S]/[U]**. The DOI of Roth (1955) is not verified and is omitted. |
| Other v1.0/v2.0 entries (`Stoneham73`, `Korobov72`, `KS93`, `BC02`, `Vandehey19`, `Bugeaud02`, `BHS15`, `KN`, `Lean4`, `Mathlib`, `MiraPoly`) | Status as recorded in the Paper VII v1.0 and v2.0 ledgers. |

---

### Theorem A (Theorem 4.2) and Theorem 4.3: protected poles and the universal Liouville example

- **Evidence.** Lean-supported paper proofs ([VERIFICATION.md](VERIFICATION.md)). Registry: [GF-10](../../docs/results.md#gf-10), [GF-15](../../docs/results.md#gf-15) (Corollary 4.4).
- **Closest results.**
  - Normal Liouville numbers: Kano–Shiokawa (1993), whose Remark 2 is per the Phase 18 audit **[S]**; Bailey–Crandall (2002); Bugeaud (2002); Becher–Heiber–Slaman (2015). Theorem A adds normality of every polynomial image and all-prime denominators for an explicit series.
  - Manai (arXiv:2508.09319) **[A]**: explicit numbers whose integer-valued polynomial images are absolutely normal. Theorem A uses one base, every rational polynomial, all-prime denominators and explicit rates. As far as the abstract shows, neither result contains the other **[M]**.
- **Relation.** Not located in the sources examined.

### Theorem B (Theorem 5.3): polynomial schedules with growing auxiliary support

- **Evidence.** Paper proof, quoting two results of Paper VII v2.0 (Theorems 5.1–5.2).
- **Closest results.**
  - Vandehey (2019, Theorem 5.1, Corollary 1.2) gives power savings on moduli with **fixed** prime support **[S]**. Lemma 3.1 is uniform in the base $b^\tau$ with $\tau$ growing, which Vandehey's results, as read in the Phase 13–14 audits, do not state **[S]**.
  - Lemma 3.5 (exact orders modulo $\Lambda^r$) is an elementary combination of LTE and CRT. We claim no novelty for it **[M]**.
- **Relation.** Not located in the sources examined. **Outstanding check:** a search for base-uniform short-orbit bounds on prime-power moduli (Korobov, Vandehey, Bourgain-type estimates) was not run.

### Theorem C (Theorems 6.2, 6.4): prescribed finite exponents

- **Evidence.** Paper proofs. Theorem 6.4 uses Paper I v2.0, Lemmas 2.2–2.4 (paper proofs there).
- **Closest results.**
  - The computation $\mu=\lambda$ for lacunary series with geometric gaps is the classical truncation argument (Lemma 5.4).
  - Without auxiliary primes $W_S$ is the Stoneham number $\alpha_{b,p}$. Its polynomial normality is Paper I v2.0, Theorem A (kernel-verified there), and, for a related family, Mira Cult's note S08 **[R in v1.0]**.
- **Priority.** The registry entry [GF-25](../../docs/results.md#gf-25) calls these "the first explicit non-Liouville all-prime polynomial normal numbers". No search supports a priority claim of that strength, and **the manuscript does not make it**.

### Theorem D (Proposition 6.1): the limit of truncation separation

- **Evidence.** Paper proof.
- **Relation.** This is a statement about a specific certificate, with no claim of optimality among Diophantine methods. Not located in the sources examined; no search was run **[M]**.

### Theorem E (Theorems 7.3, 7.4) and Lemmas 7.1–7.2: exponent two in all degrees

- **Evidence.** Paper proofs. The source is Phase 23 Track C4, whose review attacked the claims line by line: no Critical issue, post-repair ACCEPT.
- **Closest results.**
  - Almost every real number is normal and has $\mu=2$, by Borel and Khintchine. So the existence of normal numbers with $\mu=2$ is classical, and we make **no** priority claim for explicit normal numbers with exponent 2 as such.
  - The literature on explicit normal numbers with prescribed irrationality exponents was **not searched**. Possible sources include work of Bugeaud and of Becher, Bugeaud and Slaman, and Amou's exponent for Champernowne's number.
  - Lemma 7.1 is in the spirit of the folding lemma for continued fractions of $\sum u^{-2^k}$ (Shallit 1979; van der Poorten–Shallit 1992) **[S]**. The form proved here allows corrections that introduce new primes. Whether an equivalent determinant estimate is in the literature was not searched.
  - Lemma 7.2 combines Dickson's lemma, inclusion–exclusion and a compactness argument. No novelty is claimed for the method **[M]**.
- **Relation.** We did not locate the combination (all-prime support, polynomial normality in every degree, $\mu=2$, and in Theorem 7.4 ratios tending to one) in the sources examined.

## Outstanding checks before release

1. Read Manai, arXiv:2508.09319, and state the comparison from the theorem rather than from the abstract.
2. Search the literature on irrationality exponents of explicit normal numbers (Bugeaud; Becher–Bugeaud–Slaman; Amou on Champernowne) before any sentence suggests priority for Theorems C or E. The manuscript currently makes none.
3. Search for base-uniform short-orbit estimates on prime-power moduli (Lemma 3.1), and for determinant or folding estimates equivalent to Lemma 7.1.
4. Verify Shallit (1979), van der Poorten–Shallit (1992), DEKKM and Ghidelli against primary texts or Crossref; add DOIs only when verified.
5. Compile the PDF (`pdflatex`, `bibtex`). The tools are unavailable locally and on `hail`. Then confirm the cross-references to Paper VII v2.0 statement numbers.
6. Commit `scripts/phase23_nonlinear_short_orbits.py` and the Audit 2 repair of `scripts/phase22_short_orbits.py`. Register the Phase 23 Track C3–C4 material.
