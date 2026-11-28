# Verification map: Complete Reciprocal Discrepancy Spectra in Integer Radices (v1.0, candidate draft)

This file maps every numbered statement of Candidate Paper XV to its evidence labels: **Paper proof**, **Finite certificate**, **External input**, **Conditional**, or **Open**. **No result in this manuscript is kernel-verified in Lean 4.** The 256-bit digit-transition counts in Table 1 are **finite measurements only** and are never evidence for any asymptotic statement.

**Cross-model review is not independent human peer review.** The written proofs, the underlying repository notes, and the Audit III verification were checked only by AI models from different providers. No independent human specialist has read the proofs, and the assembled manuscript has not been peer reviewed.

**Status.** This is an **unreleased candidate draft** (Proposed Paper XV). It has no entry in `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml`, or `docs/registry/papers.toml`, and no `paper.pdf`, `metadata.toml`, or `submission/` directory is committed to the repository. Reproducible PDF compilation and log/text inspection were completed in `/tmp/paper15-build` on `hail` (see below), and `/tmp/paper15-build` was removed after verification.

## Statement map

All statement numbers below were confirmed directly against the compiled 28-page PDF (`pdftotext` extraction from the clean build on `hail`). "Track E (Phase 25)" is `notes/phase25/partitions-and-reciprocals.md` (pinned at commit `c06c97dd7d942bdf46d727aa58309869af88d5e7`, registered as `GF-45`); "Track A (Phase 26)" is `notes/phase26/toeplitz-determinants-and-uniformity.md` (working tree); "Track E (Phase 26)" is `notes/phase26/constructive-normality-and-reciprocal-spectra.md` (working tree).

| No. | Statement (short) | Evidence | Lean | External inputs | Source note and finite checks |
| --- | --- | --- | --- | --- | --- |
| A | (i) All-radix $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ and $\nu_N(1/x; b) \Rightarrow \mu_\alpha = \alpha\delta_0 + (1-\alpha)\lambda$ for per-$(b, \alpha)$ irrational $x(b, \alpha) \in M_b \subset K_b$; (ii) exact word frequencies away from $0$, adjacent-cylinder sum $f_N(0^L) + f_N((b-1)^L) \to \alpha + 2(1-\alpha)b^{-L}$, disjunctive nonnormality; (iii) computability for computable $\alpha$ (no multi-radix claim, no discrepancy rate) | **Paper proof** + **External input** | None | Stone–Weierstrass on $\mathbb{T}$ (`Rudin76`); Portmanteau on continuity sets (`Billingsley99`) | Track E (Phase 25) §E1.2 (`GF-45`); Audit III `m3`–`m6`; Track E (Phase 26) §E1.4; `scripts/phase25_partitions_reciprocals.py` |
| B | (i) Exact $\det((1-\alpha)I_r + \alpha J_r) = (1-\alpha)^{r-1}(1+(r-1)\alpha)$ and root limit $1-\alpha$; (ii) determinant-to-uniformity transfer; (iii) arithmetic sharpness across $[0, 1]$ via Theorem A reciprocal witnesses | **Paper proof** + **External input** (Portmanteau for open sets; inherits Theorem A for (iii)) | None | Portmanteau for open sets (`Billingsley99`); standard measure theory on $\mathbb{T}$ (general Szegő cited for context only, not used) | Track A (Phase 26) §§1, 2, 4 (A2, A4); Track E (Phase 25) §E1.2 |
| C | (i) Prime-power shifted uniform grids for complete periods ($b \ge 3$) and $D^-(R; b) = 0$; (ii) worst-start obstruction $D_N(1/Q; b) \ge \min(N, L-h)/N - b^{-h}$; (iii) single-cycle averaged short-orbit mean square $\le 1/N + 1/J_k$ (exact $1/N$ for $N \le J_k$) | **Paper proof**; (iii) uses **External input** | None | Weak$^*$ sequential compactness (`Billingsley99`) and Stone–Weierstrass (`Rudin76`) for (iii) | Track E (Phase 25) §E2 (Propositions E2.1–E2.3); `scripts/phase25_partitions_reciprocals.py` |
| D | (i) Mahler $X_{b,m}$ ($m \ge 3$): run bound $\frac{m}{m-2}n + O(1)$, $\gg \log N$ transitions/escapes, $1 - D_N \gg (\log N)/N$; (ii) Euler $P_b$: run bound $\frac{3}{8}n^2 + O(n+1)$, $\gg \log\log N$ transitions/escapes, $1 - D_N(P_b; b) \gg (\log\log N)/N$, and $1 - D_k(R_k^{(E)}; b) \gg (\log\log k)/k$ | **Paper proof**; (ii) uses **External input** | None | Euler's pentagonal number theorem at $z = 1/b$ (`Andrews1976` Ch. 1, `EulerE541`) | Track E (Phase 25) §§E3–E4 (Theorems E3, E4); `scripts/phase25_partitions_reciprocals.py` |
| 2.1 | Coupling comparison on $\mathbb{T}$ ($D$, $M$, $\widehat{\nu}(k)$, gluing) | **Paper proof** | None | — | Track E (Phase 25) §Definitions; Audit III §1.9 |
| 2.2 | Binary padding and binary contraction preserving $\gcd(P_v, e) = 1$ | **Paper proof** + **Finite certificate** | None | — | Track E (Phase 25) §E1.1; `phase25_partitions_reciprocals.py` (15 pads, 936 band positions) |
| 2.3 | Direct dyadic spectrum $\mathcal{A}_{\mathrm{conv}}(2^e) = [0, 1]$ | **Paper proof** | None | de Bruijn Eulerian cycle (`deBruijn46`) | Track E (Phase 25) Theorem E1 |
| 2.4 | Attribution and non-dyadic $+1$-inversion barrier (remark) | Context only | None | Bugeaud–Corvaja–Zannier (`BCZ03`) cited for context only, not used in proofs | Track E (Phase 25) §E1.1 boundary; `GF-38` Theorem C1.4 |
| 3.1 | Standalone Cut-and-Fold Comparison Lemma (explicit cycle & all-prefix constants, choice order $H$ then $(m, d)$) | **Paper proof** + **Finite certificate** | None | — | Track E (Phase 25) §E1.2; **Audit III `m4`**; `phase25_partitions_reciprocals.py` (15 updates across bases $2, 3, 4, 5, 10$) |
| 3.2 | All-radix limit measures $\mu_\alpha$ and $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ (including self-contained endpoints $\alpha = 0, 1$) | **Paper proof** + **External input** + **Finite certificate** | None | Stone–Weierstrass (`Rudin76`); Portmanteau (`Billingsley99`) | Track E (Phase 25) Theorem E1.2; `phase25_partitions_reciprocals.py` (exact factorization (3)) |
| 3.3 | Explicit computability procedure for computable $\alpha \in [0, 1]$ with modulus $\|x - x^{(i)}\| \le 3 b^{-m_{i+1}}$ | **Paper proof** | None | — | Track E (Phase 25) §E1.2; **Audit III `m5`** |
| 3.4 | Rate and scale: ineffectivity and doubly exponential growth (remark) | Exposition / qualitative boundary | None | — | **Audit III `m6`** (§1.12); `PaperXIII` cited for $\alpha = 0$ rate context |
| 4.1 | Exact compound-symmetric Toeplitz determinant $\det((1-\alpha)I_r + \alpha J_r) = (1-\alpha)^{r-1}(1+(r-1)\alpha)$ and $T_r((M_h)_*\mu_\alpha) = G_r(\alpha)$ | **Paper proof** | None | — | Track A (Phase 26) Proposition 4.1 (A4) |
| 4.2 | Gram–Schmidt monotonicity $(\det T_r)^{1/r} \le (\det T_m)^{1/m}$ and $T_b$-invariant Lebesgue decomposition $\mu_{\mathrm{ac}} = a(\mu)\lambda$ | **Paper proof** | None | Standard measure theory on $\mathbb{T}$ (Lebesgue decomposition, Riemann–Lebesgue) | Track A (Phase 26) Lemmas 1.1, 1.5, 2.2, 2.3 |
| 4.3 | Self-contained constant-density Szegő–Kolmogorov–Krein limit $(\det T_m(a\lambda + \rho_s))^{1/m} \to a$ | **Paper proof** | None | Inner/outer regularity on $\mathbb{T}$ (`GrenanderSzego58`, `Simon05` cited for context only) | Track A (Phase 26) Proposition 2.4 |
| 4.4 | Determinant-to-uniformity transfer and reciprocal sharpness across $[0, 1]$ | **Paper proof** + **External input** | None | Portmanteau for open sets (`Billingsley99`); uses Theorem 3.2 | Track A (Phase 26) Theorems 2.1, 3.1, 4.2 |
| 5.1 | Prime-power shifted grids ($b \ge 3$, $p \mid b-1$) and $D^-(R; b) = 0$ | **Paper proof** + **Finite certificate** | None | — | Track E (Phase 25) Proposition E2.1; `phase25_partitions_reciprocals.py` (16 denominators) |
| 5.2 | Worst-start obstruction $D_N(1/Q; b) \ge \min(N, L-h)/N - b^{-h}$ | **Paper proof** + **Finite certificate** | None | — | Track E (Phase 25) Proposition E2.2; `phase25_partitions_reciprocals.py` |
| 5.3 | Single-cycle averaged short-orbit mean-square cancellation | **Paper proof** + **External input** + **Finite certificate** | None | Weak$^*$ compactness (`Billingsley99`); Stone–Weierstrass (`Rudin76`) | Track E (Phase 25) Proposition E2.3; `phase25_partitions_reciprocals.py` (combinatorial collision counts) |
| 5.4 | Transfer from numerator-specific bounds (remark) | **Conditional** | None | Unproved hypothesis $D_{m_{k+1}}(R_k; b) = o(1)$ / uniform intermediate bound | Track E (Phase 25) §E2 Conditional remark |
| 6.1 | Self-contained finite fixed-point discrepancy inequality $1 - D_N \ge \frac{2}{5}\min_{c_0 \in F_b} M_N(z - c_0; b) - 1/N$ | **Paper proof** | None | — | `notes/phase23/binary-partition-and-carry-complexity.md` Lemma 5.3 (`GF-32`), re-proved in full here |
| 6.2 | Reciprocal separation lemma ($\|(b-1)b^n Z\| \ge 1/(2A)$, run bound, $F_b$-escape) | **Paper proof** + **Finite certificate** | None | — | Track E (Phase 25) §E3–E4; `phase25_partitions_reciprocals.py` (152 instances) |
| 6.3 | Mahler's $m$-ary partition constants $X_{b,m}$ ($m \ge 3$) and signed orbit recurrence | **Paper proof** + **Finite certificate** | None | — | Track E (Phase 25) Theorem E3; `phase25_partitions_reciprocals.py` |
| 6.4 | Euler's partition constant $P_b$ and initial-orbit discrepancy gap for $R_k^{(E)}$ | **Paper proof** + **External input** + **Finite certificate** | None | Euler's pentagonal number theorem (`Andrews1976` Ch. 1, `EulerE541`) | Track E (Phase 25) Theorem E4; **Audit III `m2`, `m8`**; `phase25_partitions_reciprocals.py` (16 Euler windows: 4 strictly positive, 12 vacuous) |
| Table 1 | 256-bit binary transition counts for $X_{2,3}, X_{2,4}, X_{2,5}, P_2$ | **Finite measurement only** | None | — | `phase25_partitions_reciprocals.py` (descriptive only; never used in proofs) |
| 7.1–7.5 | Open questions (non-zero Dirac rigidity, multi-radix spectra, effective rates, single-factor products, $X_{b,m}$ and $P_b$) | **Open** | None | — | Track E (Phase 25) §Open; Track E (Phase 26) Conjecture E1.C, §§E1.4–E1.6 |

## Audit III (`m4`–`m6` and hygiene) integration

Phase 26 Stage 0.2 Audit III (`notes/phase26/reviews/audit-3-gf45.md`, **0 Critical, 0 Major**, passed Paper XV gate) required three manuscript-level additions and several hygiene refinements, all incorporated into `paper.tex`:

- **`m4` (Standalone Cut-and-Fold Comparison Lemma):** Isolated as **Lemma 3.1** (`\label{lem:cutfold}`) in radix $b \ge 2$ with explicit constants: displacement $\le C b^{-H}$ / $\le F b^{-H}$, cycle exceptional mass $\le (2a + 2H + P_C)/q$ / $\le (2a + 2H + P_F)/m$, all-prefix ($N \ge m$) exceptional mass $\le 2\rho + 2(a + H + P_C)/m$ / $\le \rho + (2a + 2H + P_F)/m$, and explicit order of parameter choices ($H$ first, then $(m, d)$ with $(a + H + P_C + P_F)/m \to 0$).
- **`m5` (Explicit Computability Procedure):** Isolated as **Proposition 3.3** (`\label{prop:computable}`), giving the decidable test $\widehat{\mu_y}(k) \neq 1 \iff D_y \nmid k$, the sharp bound $|1 - \widehat{\mu_y}(k)| \ge 1 - \operatorname{Re}\widehat{\mu_y}(k) \ge 8/D_y^2$, explicit rational error budgets $\varepsilon_A, \varepsilon_B = \min(h_j^2, 16 h_j^2 / (25 D^4))$, explicit $H_A, H_B$ and denominator activation $b^d \ge j A_y$, and the explicit convergence modulus $|x - x^{(i)}| \le 3 b^{-m_{i+1}}$.
- **`m6` (Rate and Scale Remark):** Isolated as **Remark 3.4** (`\label{rem:ineffective}`), explicitly stating that the theorem is qualitative with no discrepancy convergence rate, explaining the at-least-doubly-exponential scale growth from period multiplication $P_{F'} \mid m P_F$ and polynomial-in-$j$ harmonic contraction, noting it is not a practical digit generator, and contrasting with the $\alpha = 0$ rate in `PaperXIII`.
- **Hygiene (`m1`, `m2`, `m3`, `m7`, `m8`, `m9`):** Exact external inputs listed without Erdős–Turán; digit transitions claimed only for $P_b$ and not for $R_k^{(E)}$; per-$(b, \alpha)$ non-simultaneous scope stated in Abstract, Theorem A, and Question 7.2; accurate 4-positive / 12-vacuous Euler window disclosure in §8; BF-10 single-factor distinction stated in Question 7.4 and `LEDGER.md`.

## Reproducible LaTeX compilation and PDF inspection record (Hail)

Compilation and inspection were performed exclusively on the remote Linux build server `hail` inside `/tmp/paper15-build` (no WSL used; no `paper.pdf` written to or committed in the repository; `/tmp/paper15-build` removed after verification).

- **Date:** 28 November 2026
- **Toolchain (`~/.TinyTeX/bin/x86_64-linux` on `hail`):**
  - `pdfTeX 3.141592653-2.6-1.40.29 (TeX Live 2026)` (`kpathsea version 6.4.2`)
  - `BibTeX 0.99e (TeX Live 2026)`
  - `Latexmk, John Collins, 25 November 2026. Version 4.90`
- **Reproduction command** (run inside a clean copy of `papers/15-reciprocal-discrepancy-spectra/` with sibling `../common/`):
  ```sh
  export PATH="$HOME/.TinyTeX/bin/x86_64-linux:$PATH"
  SOURCE_DATE_EPOCH=1795547923 FORCE_SOURCE_DATE=1 TZ=UTC \
    latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
  ```
- **Source checksums (SHA-256):**
  - `paper.tex`: `4c8c452d9d894ce9978bde309b0986b9fa8679efff7ac9702e25332e27903f99`
  - `references.bib`: `7e9a7e7db33d847898dbc0ad2b2f6b26d8ec35c7961e83944fd14a670238b882`
- **Two independent clean builds (`run1` and `run2` in `/tmp/paper15-build`):**
  - `run1` `paper.pdf` SHA-256: `4b4cfeeed99f47464d4de934376878e1460d972663f2b4aabcf0d63a9e5c9c16`
  - `run2` `paper.pdf` SHA-256: `4b4cfeeed99f47464d4de934376878e1460d972663f2b4aabcf0d63a9e5c9c16`
  - **Byte-for-byte identical:** `YES`
- **Log & structural checks:**
  - LaTeX errors: `0`
  - LaTeX / `hyperref` warnings: `0`
  - Undefined references / citations: `0` (`47` unique labels, `141` `\ref`/`\Cref`/`\eqref` calls; `10` BibTeX entries, `30` `\cite` calls, `0` uncited)
  - BibTeX warnings: `0` (`warning$ -- 0`)
  - Overfull / underfull `\hbox`es: `0`
  - `pdftotext` `??` occurrences: `0`
- **PDF metadata (`pdfinfo`):**
  - Pages: `28`
  - Page size: `612 x 792 pts (letter)`
  - File size: `611,137` bytes
  - PDF version: `1.7`
  - Title: `Complete Reciprocal Discrepancy Spectra in Integer Radices`
  - Author: `Christopher Anderson`
  - CreationDate / ModDate: `Tue Nov 24 13:18:43 2026 CST` (`SOURCE_DATE_EPOCH=1795547923`)
- **Cleanup:** `/tmp/paper15-build` deleted and verified absent on `hail`.

## Exact finite certificates and cross-provider model reviews (not human peer review)

- **Committed certificate script (`c06c97dd7d942bdf46d727aa58309869af88d5e7`):** Running `python -B scripts/phase25_partitions_reciprocals.py` on Windows (Python 3.13.13) exits `0` in exact `int`/`Fraction` arithmetic (zero floating-point operations) with output:
  - `E1: 15 rational pads; composed contraction has 936 verified band positions.`
  - `E1.2: 15 coprime period updates in bases 2, 3, 4, 5, 10; exact pair multiplicities and couplings.`
  - `E2: 16 product denominators; exact grids, mean-square diagonal range and starting phases.`
  - `E3/E4: 152 reciprocal-separation instances and 16 actual Euler orbit windows.` (The conservative lower bound `(2/5)*lower/k - 1/k` is strictly positive on the four windows `(2, 64)`, `(2, 128)`, `(3, 64)`, `(3, 128)` and negative, hence vacuous, on the remaining 12 tested windows: all $b = 5, 10$ windows and $k = 16, 32$ for $b = 2, 3$.)
  - `Finite measurement: transitions among 256 certified digits: {'X(2,3)': 131, 'X(2,4)': 138, 'X(2,5)': 146, 'P(2)': 111}` (finite measurements only).

| Material | Source note | Cross-provider model review (not human peer review) |
| --- | --- | --- |
| §§2–3, §§5–6 (`GF-45`) | `notes/phase25/partitions-and-reciprocals.md` | `notes/phase25/reviews/track-e-review.md` (Gemini 4 auditing Codex `gpt-6.2-astra`: ACCEPT WITH MINOR POLISH, 0 Critical, 0 Major, 8 Minor, all repaired); independently re-audited in Phase 26 Stage 0.2 Audit III (`notes/phase26/reviews/audit-3-gf45.md`: **VALIDATED**, 0 Critical, 0 Major, 9 Minor, passed Paper XV gate; 7 adversarial test suites passed across bases $3, 6, 7, 10, 12$). |
| §4 (Toeplitz transfer & sharpness) | `notes/phase26/toeplitz-determinants-and-uniformity.md` (§§1, 2, 4) | Phase 26 Track A working-tree note; self-contained proofs checked directly during drafting of Paper XV; no independent human specialist review. |
| §7 Question 7.1 (Dirac rigidity) | `notes/phase26/constructive-normality-and-reciprocal-spectra.md` (§E1.3, Conjecture E1.C) | Cited as an open question only; no theorem from Track E §E1.3 is claimed in Paper XV. |

## Pending before release

1. Independent human specialist peer review of the assembled manuscript and its provisional priority claims.
2. Owner release authorization (`metadata.toml`, optional committed `paper.pdf`, `submission/` package, and updates to `papers/manifest.toml`, `papers/SHA256SUMS`, `docs/registry/papers.toml`).
