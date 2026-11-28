# Verification map: Computable Badly Approximable Numbers with Polynomial Absolute Normality (v1.0, candidate draft)

This file maps every numbered statement of Candidate Paper XVI to its evidence labels: **Paper proof**, **Finite certificate**, **External input**, or **Open**. **No result in this manuscript is kernel-verified in Lean 4.** The floating-point Chebyshev-collocation eigenvalue estimates in Table 2 and the floating-point Kloosterman/hyperbola sanity ratios mentioned in Section 8 are **finite measurements only** and are never used as proof certificates.

**Cross-model review is not independent human peer review.** The written proofs, exact Python certificate scripts, Audit IV analysis, Track E independent re-certification, and literature checks were carried out only by AI models from different providers. No independent human specialist has read the proofs or performed a formal MathSciNet/zbMATH database search, and this assembled candidate manuscript has not been peer reviewed.

**Status.** This is an **unreleased candidate draft** (Proposed Paper XVI). It has no entry in `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml`, or `docs/registry/papers.toml`, and no `paper.pdf`, `metadata.toml`, or `submission/` directory is committed to the repository. Reproducible PDF compilation and log/text inspection were completed in `/tmp/paper16-build` on `hail` (see below), and `/tmp/paper16-build` was removed after verification.

## Statement map

All statement numbers below were confirmed directly against the compiled 25-page PDF (`pdftotext` extraction from the clean build on `hail`). "Track F2 (Phase 25)" is `notes/phase25/nonlinear-and-badly-approx.md` §2 (pinned at commit `c06c97dd7d942bdf46d727aa58309869af88d5e7`, registered as `GF-46`); "Track E (Phase 26)" is `notes/phase26/constructive-normality-and-reciprocal-spectra.md` §§E2–E4 (working tree).

| No. | Statement (short) | Evidence | Lean | External inputs | Source note and finite checks |
| --- | --- | --- | --- | --- | --- |
| A | Computable badly approximable polynomial-absolutely-normal numbers $x \in F_M$ ($q\|qx\| > 1/(M+2)$, $\mu(x) = 2$, $P(x)$ absolutely normal for every nonconstant $P \in \mathbb{Q}[X]$): (i) $M = 100, L = 52, s = 19/20$; (ii) $M = 14, L = 344, s = 18/19$ (and $M = 42, L = 4$); (iii) $M = 8, L = 226, s = 46/51$ (and $M = 14, L = 4$; $M = 30, L = 2$) | (i) **Paper proof**; (ii) **Paper proof + Finite certificate**; (iii) **Paper proof + Finite certificate + External input** | None | (i)–(ii) None; (iii) Weil (1948) + Estermann (1961) | Track F2 (Phase 25) Theorem 2.4 (`GF-46`); Track E (Phase 26) Theorem E2.2; `phase25_nonlinear_approx.py`, `phase26_constructive_spectra.py` |
| B | Exact optimality barriers of the two-block large-sieve architecture: $\mathcal{H}^{9/10}(F_7) = \mathcal{H}^{17/18}(F_{12}) = \mathcal{H}^{5/6}(F_4) = 0$; impossibility of $M \le 7$ (Weil), $M \le 12$ (elementary), and $M \le 4$ (any $\rho_{\mathrm{Klo}} \ge 0$); optimality of $M = 8$ on the Weil route | **Paper proof + Finite certificate** | None | None | Track E (Phase 26) Theorem E2.3; `phase26_constructive_spectra.py` (3 upper transfer-operator certificates) |
| C | (i) Positivity repair $D^Q \ge B_{M,L}^P$ for block weights + G1 regression ($D = 14{,}200 \to 461/900$ zeros; $D^* = 250{,}087 \to 900/900$ positive); (ii) complexity accounting (in-principle computability only, no discrepancy rate); (iii) Representation Lemma and computable all-prime full-density series $Z$ | (i)–(ii) **Paper proof + Finite certificate**; (iii) **Paper proof** + inherits Theorem A inputs/certificates | None | (i)–(ii) None; (iii) inherits Theorem A (Weil + Estermann for $1/10$, none for $1/16$ and $1/102$) | Track F2 (Phase 25) Theorem 2.4(3); Audit IV `G1`, `m10`; Track E (Phase 26) §§E3–E4; `phase26_constructive_spectra.py` |
| 2.1 | (1) Elementary Kloosterman fourth-moment bound $\|S(u,v;q)\| \le 2\tau(q)\gcd(u,v,q)^{1/4} q^{3/4}$; (2) elementary log-free modular-hyperbola rectangle bound ($16L_1L_2/q + 120\tau(q)q^{3/4}$); (3) Weil–Estermann refinement ($16L_1L_2/q + 90\tau(q)q^{1/2}$) | (1)–(2) **Paper proof**; (3) **Paper proof + External input** | None | (1)–(2) None; (3) Weil (1948) + Estermann (1961) | Track F2 (Phase 25) Lemma 2.1; `phase25_nonlinear_approx.py` (fourth-moment, 9 prime powers, 72 majorants, 367 split sums, exact $\zeta(7/4), \zeta(3/2)$) |
| 3.1 | Computable block-i.i.d. Frostman measures on $F_M$: (1) positivity test $D^Q \ge B_{M,L}^P$; (2) structural, stopping-time $\mathcal{W}(R)$, and Frostman $\mu(I) \le C_F\|I\|^s$ properties; (3) self-contained proof of $q\|qx\| > 1/(M+2)$ and $\mu(x) = 2$ | **Paper proof** | None | None | Track F2 (Phase 25) Lemma 2.2(1),(4); Phase 24 §3 convergent bound; Track E (Phase 26) §E3 |
| 3.2 | Pure-analytic hand-checkable lower bound $\Sigma(M,L,s) \ge 2^{-2s}\phi^{2(1-s)(L-1)}(1-\frac{2}{M+2})^L$, $\Sigma(100,52,19/20) > 1$, $e < 11/4$, $\log 2 > 2/3$ | **Paper proof** | None | None | Track F2 (Phase 25) Lemma 2.2(2); hand steps also cross-checked in `phase25_nonlinear_approx.py` |
| 3.3 | Transfer-operator identity $\Sigma(M,L,s) = (\mathcal{L}_s^L \mathbf{1})(1)$, supermultiplicativity, eigenfunction certificate lemma, and exact interval monotonicity on uniform grid $x_i = i/K$ | **Paper proof** | None | None | Track E (Phase 26) §E2.1; Track E review `m6`; `phase26_constructive_spectra.py` (17 transfer, 18 reversal, 3,125 supermultiplicativity checks) |
| 3.4 | Exact finite block-sum & barrier certificates: (i) transfer-operator lower certs $(14, 18/19, L=344)$ and $(8, 46/51, L=226)$; (ii) direct small-block $Q$-th root certs $(42, 4, 18/19)$, $(14, 4, 10/11)$, $(30, 2, 10/11)$; (iii) transfer-operator upper certs $(7, 9/10)$, $(12, 17/18)$, $(4, 5/6)$ | **Paper proof + Finite certificate** | None | None | Track F2 (Phase 25) Lemma 2.2(3); Track E (Phase 26) §§E2.2–E2.3; `phase25_nonlinear_approx.py`, `phase26_constructive_spectra.py` (4,000 interval inequalities; independently re-certified in `track-e-review.md`) |
| 3.5 | Proof of Theorem B: exact feasibility boundary $s^*(\rho) = (5-\rho)/(2(3-\rho))$, $\mathcal{H}^s(F_M) = 0$, mass-distribution exclusion of all Frostman measures for $M \le 7 / 12 / 4$ | **Paper proof + Finite certificate** | None | None | Track E (Phase 26) Theorem E2.3; `phase26_constructive_spectra.py` (100 LP threshold checks + 3 barrier certs) |
| 4.1 | Effective polynomial Fourier decay $\lvert\int e(\xi P(x))\,d\mu(x)\rvert \le \bar{C}(P)(1+\lvert\xi\rvert)^{-\eta}$ with explicit rational $(\eta, \bar{\xi}_0(P), \bar{C}(P))$ in Regime A ($s > 17/18$) and Regime B ($s > 9/10$) | Regime A: **Paper proof**; Regime B: **Paper proof + External input** | None | Regime A: None; Regime B: Weil (1948) + Estermann (1961) | Track F2 (Phase 25) Theorem 2.3; `phase25_nonlinear_approx.py` (3 simplified triples, majorants for $r = 1, 2, 3$); `phase26_constructive_spectra.py` (8 midpoint certs) |
| 5.1 | Proof of Theorem A and Theorem C(i): uniform $L^2$ moment bound with rational $\bar{K}_e$, continuous-partial-sum potential $\Psi$, repaired weight search $D^Q \ge B_{M,L}^P$, four rational error budgets, nested-cylinder selection, Weyl convergence, computability of $x$ and $P(x)$ | Inherits Theorem A (Regime (i) **Paper proof**; (ii) **Paper proof + Finite certificate**; (iii) **Paper proof + Finite certificate + External input**) | None | Regime (iii) only: Weil (1948) + Estermann (1961) | Track F2 (Phase 25) Theorem 2.4; Audit IV `G1`; Track E (Phase 26) §§E2.2, E3 |
| 5.2 | Zero-weight regression ($D = 14{,}200 \to 461/900$ zeros; $D^* = 250{,}087$) and explicit absence of discrepancy rate for $P(x)$ (remark) | **Paper proof + Finite certificate** | None | None | Audit IV `G1`, `m10`; Track E (Phase 26) §E3; `phase26_constructive_spectra.py` |
| 5.3 | Complexity accounting and alphabet-size trade-off ($M^L$ and $B_{M,L}$ digit counts, sample $\log_{10}\bar{\xi}_0(P)$ scales, doubly exponential runtime per block) | **Paper proof + Finite certificate** | None | None | Track F2 (Phase 25) §7 Q4; Audit IV §1.8, `G2`; Track E (Phase 26) §E3; `phase26_constructive_spectra.py` (6 size computations) |
| 5.4 | (1) Representation Lemma (every $x \notin S + \mathbb{Z}[1/b]$ has persistent all-prime expansion); (2) computable badly approximable all-prime series $Z$ ($q\|qZ\| > 1/10$ Regime (iii), $> 1/16$ Regime (ii), $> 1/102$ Regime (i)) | (1) **Paper proof**; (2) inherits Theorem A | None | (1) None; (2) Weil + Estermann for $1/10$, none for $1/16$ and $1/102$ | Track F2 (Phase 25) Theorem 2.4(3); Track E (Phase 26) §E4; Track E review `m7` |
| 5.5 | Representation vs. intrinsic content and simultaneous all-radix extension via $(X - S_b, b, h)$ (remark) | Exposition / scope | None | None | Track E (Phase 26) §E4; Audit IV `m8` |
| Table 1 | Certified parameter regimes, Frostman exponents, Diophantine bounds, and $M^L, B_{M,L}$ digit counts | **Paper proof + Finite certificate** (Weil + Estermann on Regime B rows) | None | Weil + Estermann on rows $(30, 2)$, $(14, 4)$, $(8, 226)$ | Proposition 3.2, Proposition 3.4, Proposition 5.3 |
| Table 2 | Descriptive Chebyshev-collocation float estimates of $\lambda_M(s)$ | **Finite measurement only** | None | None | `phase26_constructive_spectra.py` (`finite_measurements`, descriptive only; never enters proofs) |
| Table 3 | Exact admissible rational parameters $(\alpha, \beta, \theta)$ and decay exponents $\eta$ | **Paper proof + Finite certificate** | None | None | Theorem 4.1; `phase25_nonlinear_approx.py`, `phase26_constructive_spectra.py` |
| Table 4 | Comparison of prior literature and Paper XVI | Literature synthesis (see `LEDGER.md`) | None | Context citations only | Audit IV §§3.1–3.4; `LEDGER.md` |
| 7.1–7.5 | Open questions (cap $M = 2$, elementary $M = 13$, polynomial-time generation, effective discrepancy rates in $F_M$, closed-form badly approximable normal series) | **Open** | None | None | Track F2 (Phase 25) §7 Q3–Q5; Track E (Phase 26) §Open problems |

## Audit IV (`G1`–`G4`, `m1`–`m11`) and Track E (`E2`–`E4`) integration

Every Major finding and applicable Minor item from Phase 26 Stage 0.2 Audit IV (`notes/phase26/reviews/audit-4-gf46.md`) and every `E2`–`E4` finding from `notes/phase26/reviews/track-e-review.md` is integrated into `paper.tex`:

- **`G1` (Zero-weight defect repaired):** Lemma 3.1(1), Theorem 5.1 Step 3, and Theorem C(i) enforce the exact integer test $D^Q \ge B_{M,L}^P$, guaranteeing $p_{\mathbf{u}} > 0$ for every block $\mathbf{u} \in \{1, \dots, M\}^L$; Remark 5.2(1) records the exact $(30, 2, 10/11)$ regression ($D = 14{,}200 \implies 461/900$ zeros; $D^* = 250{,}087 \implies 900/900$ positive).
- **`G2` (Calibrated framing and §3.4 "must not claim" compliance):** Abstract, §1, and §6 state explicitly that existence down to $M = 2$ is classical (Kaufman 1980 + Baker in Montgomery 1994; Queffélec–Ramaré 2003; Hochman–Shmerkin 2015), that nothing here answers or strengthens Montgomery's existence question, that the contribution addresses a Turing-computable form of Queffélec's (2006) remark, that the algorithm is computable in principle only (not practical or polynomial time), and that lowering the cap to $M = 2$ remains open.
- **`G3` & `m11` (Focused manuscript scope):** The unrelated `F1` ($d = r$ packet/gap) and `F3` (classical Folding Lemma / locally varying series) sections of `GF-46` are excluded from Paper XVI.
- **`G4(a)–(d)` (Literature verification):** Resolved transparently in §1, §6, Table 4, and `LEDGER.md`: Montgomery (1994, Appendix, Problem 45, p. 204) via secondary excerpt verification; Hochman–Shmerkin (2015, Theorems 1.4, 1.5, 1.12 and §1.3.3, `arXiv:1302.5792`); Kaufman (1980) / Queffélec–Ramaré (2003) / Sahlsten–Stevens (2024) / Baker–Banaji (2025) / Algom–Rodriguez Hertz–Wang (2026) scope; Becher–Yuhjtman year corrected to *IMRN* 2019 (`arXiv:1704.03622`, fixing `m6`); and explicit disclosure that a formal MathSciNet/zbMATH database search has not been performed by a human specialist.
- **Audit IV Minor `m1`–`m10` and Track E `m6`–`m7`:** Certified Frostman exponent terminology (`m1`/§1.3); order $q\|qx\| \asymp 1$ without claiming $1/(M+2)$ sharp (`m2`); both Weil (1948) and Estermann (1961) named everywhere (`m3`); finite certificates distinguished from analytic proofs (`m4`); in-principle complexity highlighted (`m5`); axis bound $10\tau(q) \le 20\tau(q)$ noted (`m7`); multi-radix $(X - S_b, b, h)$ extension noted in Remark 5.5 (`m8`); $\eta$'s dependence on $(\alpha, \beta, \theta)$ stated explicitly (`m9`); absence of discrepancy rate for $P(x)$ stated in Abstract, Theorem C(ii), and Remark 5.2(2) (`m10`); 2-line supermultiplicativity proof included in Lemma 3.3(1) (Track E `m6`); explicit Weil–Estermann vs. elementary vs. analytic input labels on $1/10$, $1/16$, $1/102$ in Proposition 5.4(2) (Track E `m7`).

## Reproducible LaTeX compilation and PDF inspection record (Hail)

Compilation and inspection were performed exclusively on the remote Linux build server `hail` inside `/tmp/paper16-build` (no WSL used; no `paper.pdf` written to or committed in the repository; `/tmp/paper16-build` removed and verified absent after inspection).

- **Date:** 28 November 2026
- **Toolchain (`~/.TinyTeX/bin/x86_64-linux` on `hail`):**
  - `pdfTeX 3.141592653-2.6-1.40.29 (TeX Live 2026)` (`kpathsea version 6.4.2`)
  - `BibTeX 0.99e (TeX Live 2026)`
  - `Latexmk, John Collins, 25 November 2026. Version 4.90`
  - `pdfinfo version 26.01.0` (Poppler)
- **Reproduction command** (run inside a clean copy of `papers/16-computable-badly-approx-normality/` with sibling `../common/`):
  ```sh
  export PATH="$HOME/.TinyTeX/bin/x86_64-linux:$PATH"
  SOURCE_DATE_EPOCH=1795547923 FORCE_SOURCE_DATE=1 TZ=UTC \
    latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error paper.tex
  ```
- **Source checksums (SHA-256):**
  - `paper.tex`: `e344f3aa40ac22503abc6a8d3697cc944656612cb72205596d339ef8fcee2bcf`
  - `references.bib`: `0a9e69783967b94c78a58783290a1c4fc1e341056fc03378ba616e061006fb6f`
- **Two independent clean builds (`run1` and `run2` in `/tmp/paper16-build`):**
  - `run1` `paper.pdf` SHA-256: `cab8dff9c9392fe672c61e9991bf5b55bce8fefbd24d3fa887d30bc5b60d207e`
  - `run2` `paper.pdf` SHA-256: `cab8dff9c9392fe672c61e9991bf5b55bce8fefbd24d3fa887d30bc5b60d207e`
  - **Byte-for-byte identical:** `YES`
- **Log & structural checks:**
  - LaTeX errors: `0`
  - LaTeX / `hyperref` warnings: `0`
  - Undefined references / citations: `0` (`48` unique labels, `130` `\ref`/`\Cref`/`\eqref` calls; `31` BibTeX entries, `75` `\cite` calls, `0` uncited)
  - BibTeX warnings: `0` (`warning$ -- 0`)
  - Overfull / underfull `\hbox`es: `0`
  - `pdftotext` `??` occurrences: `0`
- **PDF metadata (`pdfinfo`):**
  - Pages: `25`
  - Page size: `612 x 792 pts (letter)`
  - File size: `694,361` bytes
  - PDF version: `1.7`
  - Title: `Computable Badly Approximable Numbers with Polynomial Absolute Normality`
  - Author: `Christopher Anderson`
  - CreationDate / ModDate: `Tue Nov 24 13:18:43 2026 CST` (`SOURCE_DATE_EPOCH=1795547923`)
- **Cleanup:** `/tmp/paper16-build` deleted and verified absent (`exists = False`) on `hail`.

## Exact finite certificates and cross-provider model reviews (not human peer review)

- **Committed Phase 25 certificate script (`c06c97dd7d942bdf46d727aa58309869af88d5e7`):** Running `python -B scripts/phase25_nonlinear_approx.py` on Windows (Python 3.13) exited `0` with output for F2:
  - `F2 Kloosterman & hyperbola: exact fourth-moment, 9 prime-power, 367 split-sum (max ratio=0.4952<1), 72 trapezoid-majorant, and exact zeta(7/4), zeta(3/2) certificates; float sanity max_elem=0.2611, max_weil=0.8493, emp_rect_excess/sqrt(q)=0.4162 (48 rects)`
  - `F2 block measures & exponents: hand-checkable M=100 L=52 steps certified; exact integer certs M=42 L=4 (s=18/19, 550612 distinct N, ratio=1.018523), M=14 L=4 (s=10/11, 8439 distinct N, ratio=1.014769), M=30 L=2 (s=10/11, 337 distinct N, ratio=1.025743); 3 exponent triples + computable rational majorants (r=1,2,3), 10000 concatenations, and 900-child martingale step verified`
- **Working-tree Phase 26 Track E certificate script:** Running `python -B scripts/phase26_constructive_spectra.py` on Windows (Python 3.13) exited `0` in `14.0 s` with exact E2/E3 counts:
  - `E2 exact transfer identities Sigma(M,L,1) = (L^L 1)(1)`: `17`
  - `E2 reversal multiset identities {q+p} = {q+q'}`: `18`
  - `E2 supermultiplicativity (q+p)(vw) <= (q+p)(v)(q+p)(w)`: `3,125`
  - `E2 exact transfer-operator interval inequalities`: `4,000`
  - `E2 lowered-cap certificates`: `2` (`M = 14, s = 18/19, lam = 501/500, L = 344`; `M = 8, s = 46/51, lam = 1003/1000, L = 226`)
  - `E2 barrier certificates`: `3` (`M = 7, s = 9/10, lam = 99/100`; `M = 12, s = 17/18, lam = 199/200`; `M = 4, s = 5/6, lam = 19/20`)
  - `E2 LP threshold checks`: `100`
  - `E2 (2.5) parameter certificates`: `8`
  - `E3 G1 regression / G1 fix`: `1 / 1` (`D = 14,200` with `461/900` zeros; `D* = 250,087` with `900/900` positive)
  - `E3 size computations`: `6`
  - Float isolation verified by AST audit in `track-e-review.md` §1: zero floats enter any exact theorem assertion.

| Material | Source note | Cross-provider model review (not human peer review) |
| --- | --- | --- |
| §§2, 3.1–3.2, 4, 5.1 (`GF-46` F2) | `notes/phase25/nonlinear-and-badly-approx.md` §2 | `notes/phase25/reviews/track-f-review.md` (post-repair accepted); independently re-audited in Phase 26 Stage 0.2 Audit IV (`notes/phase26/reviews/audit-4-gf46.md`: **0 Critical**, Major `G1`–`G3` repaired and integrated, `G4(a)–(d)` tracked in `LEDGER.md` and §6; independent stress suite passed). |
| §§3.3–3.5, 5.2–5.5 (Track E `E2`–`E4`) | `notes/phase26/constructive-normality-and-reciprocal-spectra.md` §§E2–E4 | `notes/phase26/reviews/track-e-review.md` (Gemini 4 auditing `E1`–`E5`): **0 Critical, 0 Major on `E2`–`E4`**; independent from-scratch re-certification of all five transfer-operator certificates (`M = 14, 8, 7, 12, 4`) with different initial guess, rounding denominator, and binary-search integer roots; `E2` Minor `m6`–`m7` incorporated into Paper XVI. (`E1` is not part of Paper XVI.) |

## Pending before release

1. Independent human specialist peer review of the assembled manuscript and a formal MathSciNet/zbMATH database search verifying provisional priority (Audit IV `G4(d)`).
2. Primary-text inspection of entries marked `[A/S]` or `[S]` in `LEDGER.md` (notably Montgomery 1994 p. 204, Kaufman 1980, Queffélec–Ramaré 2003, Hochman–Shmerkin 2015, Weil 1948, Estermann 1961).
3. Owner release authorization (`metadata.toml`, optional committed `paper.pdf`, `submission/` package, and updates to `papers/manifest.toml`, `papers/SHA256SUMS`, `docs/registry/papers.toml`).
