# Independent Review Report: `papers/09-erdos-borwein-note/` (v1.0)

- **Reviewer model:** Gemini 4 Neon, Antigravity
- **Date:** 2026-11-25
- **Reviewed commit:** `a21f3114debd1059866364e8ae85f81717833600` (branch `t3/review-erdos-borwein-note`, started from `publication/wave-2`)
- **Disclaimer:** AI model review; not independent human peer review.

---

## Verdict

**Major revision required before release.**

The core mathematical contributions of the note—the digit identity and tail-mean estimate (Lemma 2.1, Proposition 3.1), the certified enclosures for $\mu$, $\mathbb{E}(-1)^{c_1}$, and $p_*$ (Theorem 4.2), the sharp $D = 16$ column threshold and $D \le 15$ countermodels (Theorems 5.1 and 5.4), the $k \le 4$ column-hierarchy perturbations (Theorem 6.1), the parity Bonferroni inequality and moment bounds $9 \le r_{\min}(16) \le 92$ (Theorems 7.1, 7.4, and 7.5), and the Crandall audit (Proposition 10.1)—are mathematically sound and reproduce cleanly. No claim of normality or nonnormality of $E = \sum_{n \ge 1} 1/(2^n - 1)$ appears anywhere in the manuscript or submission files, and nothing is overstated as kernel-verified.

However, five major defects prevent immediate release: (1) Section 8 labels Theorems 8.2 and 8.3 as `Finite certificate` even though Section G uses non-interval IEEE 754 floating-point arithmetic with ad-hoc rounding cushions, violating `papers/WAVE2-CONTRACT.md`; (2) Tao–Teräväinen (`arXiv:2512.01739v2`) Theorem 1.7 is misquoted by a factor of $\sqrt{2}$ in `paper.tex`, and `submission/reviewer-inquiry.md` misapplies Theorem 3.1's Case (i) prime-band condition (3.2) to the non-pretentious Case (ii); (3) Remark 7.2 draws an invalid inference of an infimum from a single finite $L = 50{,}000$ check; (4) the committed `paper.pdf` is stale and has empty PDF `Author` metadata, violating `WAVE2-CONTRACT.md` Principle 5; and (5) `references.bib` has a broken LaTeX accent (`Th{'e}orie` rendering literally as `Th’eorie`), prints internal audit notes verbatim into the References section, omits `pages = {e8}` for `tao2016`, and leaves Vaaler (1985) unverified.

---

## Summary of Checklist Audits

### 1. Normality / nonnormality claims
**Pass.** Checked `paper.tex` (lines 29, 40, 48, 115, 171, 185, 192, 282, 313, 374, 395), `metadata.toml`, and all six files in `submission/` (`abstract.txt`, `alphaxiv.md`, `announcement.md`, `summary.md`, `reviewer-inquiry.md`, `reviewer-packet.md`). Every normality/nonnormality statement is explicitly conditional on an unproved hypothesis, and explicit disclaimers ("we do not claim that $E$ is normal, and we do not claim that it is not normal") appear prominently throughout.

### 2. Statements, proofs, and reproduction runs
All four verification scripts listed in `VERIFICATION.md` were re-executed from the repository root and passed with exit code `0`:
- `python -B scripts/phase17_erdos_borwein_bias.py` (`21.4s`, `all assertions passed`): reproduced every enclosure and table entry in Theorems 4.2, 5.1, 5.4, 6.1, 7.1, 7.4, 7.5, 8.2, 8.3, and Proposition 10.1.
- `python -B papers/09-erdos-borwein-note/crosscheck.py` (`all cross-checks passed`): reproduced $\mu \approx 2.0763242$, $\mathbb{E}_{Q_{16}}\Psi_{16} \approx 0.4960055$, $\mathbb{E}(-1)^{c_1} \approx 0.111493$, $p_* \approx 0.492456$, exact rational laws $L_1,\dots,L_{11},\rho_3,\rho_4,L^{(12)}$, Bonferroni excess $1.19675 \times 10^{-4}$ ($K \le 360$), and Selberg–Vaaler grid checks.
- `python -B scripts/erdos_borwein_poisson.py`: reproduced `492230 492685`.
- `python -B scripts/erdos_borwein_arrivals.py`: reproduced `[67135, 63695, 63696, 67618]`, `486`, `262145`, `14434`.

Mathematical verification of the proofs and exact-integer code confirmed:
- The digit identity (Lemma 2.1) and carry-knapsack sufficiency (Theorem 5.1) are valid; `dp_error(D)` in `phase17_erdos_borwein_bias.py` is rigorous because $Q_D - b_{\mathrm{LB}}^{\otimes D}$ is a positive measure of mass at most $D\delta_b$ across all disjoint events simultaneously, the carry never exceeds `JMAX = 511 < CW = 512`, and `WB = 18` bytes ($144$ bits) accommodates convolution entries $< 2^{137}$ without overflow.
- The $D \le 15$ countermodels (Theorem 5.4) properly belong to $\mathcal{I}_{D'}$ for all $D' \le D$ and satisfy $\mathbb{E} C_d \le \mu_{\mathrm{lo}} \le \mu$.
- The $K \in \{2,3,4,5\}$ product perturbations (Theorem 6.1) preserve all $(K-1)$-column marked laws and achieve certified shifts $s_K > \frac{1}{2} - p_*$.
- The parity Bonferroni inequality (Theorem 7.1), rational countermodels and combined attacks (Theorem 7.4), and order-92 multivariate Jordan truncation with $4^K$ tail bound beyond $K = 360$ (Theorem 7.5) are mathematically valid (aside from the even-order remark in Finding 3 and minor points in Findings 6–8).
- Section 8's IEEE double computations (Theorems 8.2–8.3) have comfortable numerical margins ($4.1 \times 10^{-5}$ at degree 116; quadrature weights $\ge 3.24 \times 10^{-3}$ at degree 110), and the mathematical error bounds in `kappa`/`phi`/`min_weight` are sound modulo floating-point rounding, **but** they are not interval-arithmetic proofs and cannot be labelled `Finite certificate` under `WAVE2-CONTRACT.md` (Finding 1).

### 3. Evidence labels and Lean line anchors
Checked all five Lean declarations against `git show e4809cf561573aef588e6ffc491a35cdb79fd9ec:<path>` and `pdfinfo -url papers/09-erdos-borwein-note/paper.pdf`:
- `NormalityChecker/ErdosBorweinArrivals.lean#L16` → `theorem source_phase` (exact match).
- `NormalityChecker/ErdosBorweinArrivals.lean#L41` → `theorem arrival_sum` (exact match).
- `NormalityChecker/ErdosBorweinArrivals.lean#L86` → `theorem one_bit_carry` (exact match).
- `NormalityChecker/Phase17DiscrepancyBounds.lean#L375` → `theorem carry_knapsack_le` (exact match).
- `NormalityChecker/Phase17DiscrepancyBounds.lean#L432` → `theorem parity_bonferroni_dual_le` (exact match).

Nothing is overstated as `Kernel-verified`; `paper.tex` Section 13 (line 402) and `VERIFICATION.md` (line 43) state explicitly that no theorem in the note is completely kernel-verified. The sole evidence-label violation is `Finite certificate` on Theorems 8.2 and 8.3 (Finding 1).

### 4. Exposition and PDF build
Ran `wsl -d Ubuntu -- bash papers/wsl-build.sh 09-erdos-borwein-note` (then restored the working tree's `paper.pdf` so the note remains unedited). Compilation succeeded with 0 undefined references or citations (16 pages), but revealed a stale committed `paper.pdf` (Finding 4), three overfull `\hbox`es up to `26.79pt` and one `hyperref` warning (Finding 9), broken/unprofessional bibliography entries and five `badness 10000` underfull lines (Finding 5), and residual repository-internal jargon (Finding 10).

### 5. Collaborative framing
**Appropriate and non-promotional.** The framing in `paper.tex` (subtitle and Section 12), `submission/abstract.txt` (223 words $\le 250$), `submission/announcement.md` (X post 271 characters $\le 280$), `submission/alphaxiv.md`, `submission/summary.md`, and `submission/reviewer-packet.md` is sober, transparent about AI assistance and lack of human review, and well-suited to an invitation for specialist collaboration. `submission/reviewer-inquiry.md` is appropriately framed and uses `[Name]` placeholders with no real email addresses, but Inquiry 1 needs correction on Tao–Teräväinen Theorem 3.1 (Finding 2) and Inquiry 2 can now incorporate the verified Sibuya (1991) and Galambos–Simonelli (1996) references.

---

## Numbered Findings

### Finding 1 — [Major] Section 8 floating-point computations overlabelled as `Finite certificate`
- **Location:** `paper.tex` lines 29 (abstract), 70 (Table 1), 312 (Theorem 8.2), 320 (Theorem 8.3), 332–334 (Remark 8.5); `VERIFICATION.md` lines 35–36, 39; `scripts/phase17_erdos_borwein_bias.py` lines 855–950.
- **Problem:** `papers/WAVE2-CONTRACT.md` (line 23) defines **Finite certificate** as *"An exact computation proving a finite statement."* Section G of `phase17_erdos_borwein_bias.py` computes `kappa(m)`, `phi(m)`, `selberg(N)`, and `min_weight` in standard round-to-nearest IEEE 754 floating-point arithmetic (`cmath.exp`, `math.tan`, a 256-step complex-power recurrence `e *= z`, and floating-point sums over 221 atoms) with ad-hoc hand-typed rounding cushions (`1e-10`, `1e-12`, `1e-9`), not directed rounding or interval arithmetic. Remark 8.5 (`paper.tex` line 333) candidly concedes that this is *"not as a formal proof."* Despite this, the theorem headers on lines 312 and 320 carry bare `\evidence{Finite certificate}` (without even the `(floating point)` qualifier of Table 1), and the abstract (line 29) presents the degree-116 and degree-$\le 110$ statements alongside the exact certificates without distinguishing their epistemic status. In addition, Theorem 8.2 relies on an external analytic input (Vaaler 1985, Theorems 18–19) that is not reflected in its evidence label.
- **Concrete fix:** Either (a) re-implement Section G in rigorous rational/interval arithmetic (e.g. `mpmath.iv` or integer/rational Taylor enclosures for $\sin,\cos,\exp,\cot$ at fixed scale $2^{-80}$, which is fast for $N \le 116$ and $221$ atoms) so Theorems 8.2 and 8.3 become genuine exact **Finite certificates** (with Theorem 8.2 noting Vaaler 1985 Theorems 18–19 as an external input), or (b) demote Theorems 8.2 and 8.3 from `Finite certificate` to clearly labelled **numerical evidence** (e.g., `Proposition` with a non-certificate disclosure) consistently across the abstract, theorem headers, Table 1, `VERIFICATION.md`, and `submission/`.

### Finding 2 — [Major] Misquoted constant in Tao–Teräväinen Theorem 1.7 and misread hypothesis in Theorem 3.1
- **Location:** `paper.tex` lines 349, 397; `submission/reviewer-inquiry.md` lines 13–15.
- **Problem:**
  1. `paper.tex` line 349 quotes Tao–Teräväinen (`arXiv:2512.01739v2`, Theorem 1.7) as giving $\Pr(\tau(n)=\tau(n+1)) = (c_\tau + O(\log_2^{-c} x))/\sqrt{2\pi\log_2 x}$. In the actual v2 TeX source (`main2.tex`, Theorem 1.7, `\label{consecutive-omega-thm}`), the denominator is **$2\sqrt{\pi\log_2 x} = \sqrt{4\pi\log_2 x}$**, not $\sqrt{2\pi\log_2 x}$ (off by a factor of $\sqrt{2}$, reflecting $\operatorname{Var}(\Omega(n) - \Omega(n+1)) \sim 2\log_2 x$).
  2. `submission/reviewer-inquiry.md` line 13 asks whether the technical condition (3.2) ($g_1(p) = 1$ for $\exp(\log^{1/11} X) \le p \le \exp(\log^{1/10} X)$) can be arranged for $g_\theta(m) = e(\theta V(m))\chi(U(m))$. In `arXiv:2512.01739v2` Theorem 3.1, condition (3.2) appears **only** in Case (i) (the real-valued equidistributed case), not in Case (ii) (the non-pretentious case, where the prime-band condition is commented out in `main2.tex`). Furthermore, because $g_\theta(p) = e(\theta)$ on primes is identical to Tao–Teräväinen's own Section 4.1 test function $e(\alpha \Omega_{>w}(n))$ (with $w=1$), their Section 4.1 proof of the pretentious-distance lower bound (eq. (4.6) / `\eqref{expy}`) applies directly to $g_\theta$ for $1/R \le \|\theta\| \le 1/2$, so Theorem 3.1(ii) *does* apply to $g_\theta$ at each fixed $\theta$ (with $\mathcal{L} = \exp(c_0 R^{-2} \log_2 X)$, giving an $L^1$-in-$\theta$, almost-all-scales analogue of Hypothesis E via Fubini, though not a single $\theta$-uniform exceptional set without discretization).
- **Concrete fix:** Change $\sqrt{2\pi\log_2 x}$ to $2\sqrt{\pi\log_2 x}$ on `paper.tex` line 349. Update `paper.tex` lines 349 and 397 and `submission/reviewer-inquiry.md` lines 13–15 to remove the misplaced concern about (3.2) and instead state accurately that Theorem 3.1(ii) applies to $g_\theta$ at fixed $\theta$ via the Section 4.1 pretentious-distance bound, leaving open (a) whether a single exceptional set works uniformly in $\theta$ (if needed beyond Fubini integration) and (b) the crucial passage from $r=2$ to $r \ge 3$ (and $r \ge 9$).

### Finding 3 — [Major] Invalid justification of the even-order infimum in Remark 7.2
- **Location:** `paper.tex` lines 256–258 (`Remark [Even order]`).
- **Problem:** Remark 7.2 states: *"This is the infimum for even $r \le 10$ (laws on $\{0,\dots,r-1\} \cup \{L\}$ with $L = 50{,}000$ verified in exact arithmetic to have the required moments, nonnegative weights and parity within $10^{-2}$ of $e_{r-1}$) and is never attained. We do not claim the infimum for general even $r$."* Exhibiting a single law at $L = 50{,}000$ with parity within $10^{-2}$ of $e_{r-1}$ only proves $\inf \mathbb{E}(-1)^N \in [e_{r-1}, e_{r-1} + 10^{-2})$; it does not prove that the infimum equals $e_{r-1}$. Ironically, the elementary $L \to \infty$ calculation already sketched in `notes/phase17/erdos-borwein-bias.md` (line 158) proves that $e_{r-1}$ is the exact infimum for **every** even $r \ge 2$: setting $w_L = 1/(L)_r > 0$ reduces the $(r-1)$-st binomial moment of the $\{0,\dots,r-1\}$ part by $\frac{1}{(r-1)!(L-r+1)}$, which lifts the unique zero weight $w^{(r-1)}_{r-2} = 0$ of $L_{r-1}$ to $+\frac{1}{(r-2)!(L-r+1)} + O(L^{-2}) > 0$ while keeping every other weight $w_n(L) = w^{(r-1)}_n + O(L^{-1}) > 0$ for large $L$, yielding $\mathbb{E}(-1)^N = e_{r-1} + O(L^{-1}) \to e_{r-1}$.
- **Concrete fix:** Either include this three-line $L \to \infty$ proof to establish the infimum $e_{r-1}$ for all even $r \ge 2$, or replace *"This is the infimum for even $r \le 10$"* by *"the infimum lies in $[e_{r-1}, e_{r-1} + 10^{-2})$ for even $r \le 10$."*

### Finding 4 — [Major] Committed `paper.pdf` is stale and lacks PDF author metadata; `paper.tex` sets empty `pdfauthor={}`
- **Location:** `papers/09-erdos-borwein-note/paper.pdf` and `paper.tex` line 4.
- **Problem:** Inspecting the committed `paper.pdf` with `pdfinfo` shows `Author:` is **empty** (`CreationDate: Tue Nov 24 13:18:43 2026 CST`, `573287` bytes), contradicting `papers/WAVE2-CONTRACT.md` Principle 5 (which requires `\makebyline` to populate the PDF author metadata as `Christopher Anderson`). Rebuilding cleanly with `wsl -d Ubuntu -- bash papers/wsl-build.sh 09-erdos-borwein-note` produces a `572762`-byte PDF with `Author: Christopher Anderson`. In addition, `paper.tex` line 4 still explicitly writes `\hypersetup{pdftitle={...},pdfauthor={}}`, which is confusing and redundant with `byline.tex`.
- **Concrete fix:** Delete `,pdfauthor={}` from `paper.tex` line 4 and rebuild `paper.pdf` via `wsl -d Ubuntu -- bash papers/wsl-build.sh 09-erdos-borwein-note` before release.

### Finding 5 — [Major] Bibliography syntax bug (`Th’eorie`), internal audit notes printed in References, missing article number, and unverified Vaaler entry
- **Location:** `references.bib` lines 20, 54, 60, 69–71, 82, 94, 106, 120, 132; `paper.tex` lines 317, 410; `paper.pdf` pp. 15–16.
- **Problem:**
  1. Line 54 (`tt2019`): `Journal de Th{'e}orie des Nombres de Bordeaux` is missing a backslash before `'e`, rendering literally as **`Journal de Th’eorie des Nombres de Bordeaux`** in `paper.pdf` [12].
  2. Lines 20, 60, 70, 82, 94, 106: internal verification notes (`"Bibliographic data checked via Crossref; contents not examined beyond the title."`, `"The full text could not be retrieved during this review; theorem number and page of the majorant used in the text are not verified."`) are stored in BibTeX `note = {...}` fields and printed verbatim in the published bibliography of `paper.pdf`!
  3. Lines 63–71 (`tao2016`): missing `pages = {e8}` (article number confirmed via Crossref).
  4. Line 106 (`vaaler1985`) & `paper.tex` line 317: Vaaler (1985) is now verified from the AMS PDF (**Theorems 18 and 19, pp. 210–212**; **Theorem 6, p. 193**); the disclaimer in `paper.tex` line 317 and `references.bib` line 106 should be replaced with the exact citation.
  5. Line 132 (`miragist`): `section S06` is not brace-protected and renders as `section s06` in `paper.pdf` [9].
  6. Line 120 (`sude2`): unbreakable 40-char commit and 64-char SHA-256 hex strings cause five `Underfull \hbox (badness 10000)` lines on p. 15, stretching `h t t p s :` across the column.
  7. `\bibliographystyle{plain}` (`paper.tex` line 410) drops the `doi` field from every `@article` entry, so no DOIs appear in the compiled PDF.
- **Concrete fix:** Fix `Th{\'e}orie` and `{S06}`; add `pages = {e8}` to `tao2016`; move all Crossref/audit remarks out of `note` into `LEDGER.md` or BibTeX `%` comments; update `paper.tex` line 317, `VERIFICATION.md`, `LEDGER.md`, and `submission/alphaxiv.md` with Vaaler (1985), Theorems 6, 18, and 19 (pp. 193, 210–212); wrap long hashes in `\texttt{\seqsplit{...}}` or `\nolinkurl{...}` (or move the full 64-char SHA-256 to `LEDGER.md`); and either include DOIs in `note = {\href{https://doi.org/...}{doi:...}}` or switch to a DOI-aware bibliography style.

### Finding 6 — [Minor] Slightly imprecise strip bound and unused variable in Proposition 3.1(b)
- **Location:** `paper.tex` line 132.
- **Problem:** Using only $0 \le V(m) \le \log_2 m$ and $1 \le d \le N$, an integer $m \ge 2N+d$ with $t(m) < 2N+d$ satisfies $m < 2N+d+\log_2 m \le 3N + \log_2(4N)$ (for $N \ge 4$), not $m \le 3N + \log_2 N$ (off by $\log_2 3$ if $V(m)$ approached $\log_2 m$; the tighter bound holds asymptotically only because $V(m) = o(\log m)$, which is not invoked). In the next sentence, the summation cutoff switches inconsistently from $q \le 3N + \log_2 N$ to $q > 4N$ and $q \le 4N$, and the symbol `$g$` in `"Finally $g = U = 1 * a$"` is never used again (a carryover from `notes/phase14/erdos-borwein-frequencies.md`).
- **Concrete fix:** Replace $3N + \log_2 N$ with $4N$ (for $N \ge 4$) in both places so the cutoff $4N$ is consistent throughout, and delete `$g =$`.

### Finding 7 — [Minor] Prose description of Theorem 4.2 does not match Section D of the certificate script
- **Location:** `paper.tex` line 157 vs. `scripts/phase17_erdos_borwein_bias.py` lines 653–674.
- **Problem:** `paper.tex` line 157 states: *"A carry dynamic programme over $48$ columns computes $\mathbb{E}(-1)^{c_1}$, and the depth truncation costs at most $2\mu p_0^{48}$ by Lemma 4.1; Proposition 2.2 gives $p_*$."* In the actual script (Section D), `pstar` is computed directly from the 48-column carry DP (`one_lb`, `zero_lb`) with truncation error $2(\mu_{\max}+1)p_0^{48}$, while $\mathbb{E}(-1)^{c_1}$ (`carry_sign`) uses the 47-column carry into column 1 (`d = 2..48`) with truncation bound $3 \cdot 2(\mu_{\max}+1)p_0^{48} > 2\mu p_0^{47}$. (Computing $p_*$ from `carry_sign` via Proposition 2.2 would in fact yield a narrower interval $[0.4924548, 0.4924563]$ than the reported $[0.492450290, 0.492460864]$.)
- **Concrete fix:** Rewrite line 157 to describe accurately how Section D encloses $p_*$ and $\mathbb{E}(-1)^{c_1}$ (or alternatively derive $p_*$ from `carry_sign` via Proposition 2.2 and update the reported enclosure).

### Finding 8 — [Minor] Overfull `\hbox`es and `hyperref` PDF-string warning
- **Location:** `paper.tex` lines 48–49 (`Overfull \hbox 26.79pt`), lines 246–247 (`Overfull \hbox 10.98pt`), lines 166–168 (`Overfull \hbox 2.20pt`), and line 159 (`hyperref` warning).
- **Problem:** Line 48 protrudes nearly 1 cm into the right margin on page 1 (triggered by the awkward `\linebreak[3]` and long unbreakable inline inequality); line 246 protrudes `10.98pt` on `parity_bonferroni_`; line 166 protrudes `2.20pt`; and `\section{The sharp $16$-column threshold}` on line 159 emits two `hyperref` warnings (`Token not allowed in a PDF string: removing 'math shift'`).
- **Concrete fix:** Remove `\linebreak[3]` and slightly rephrase line 48; add an earlier break or reword line 246 before `\texttt{parity\_bonferroni\_\allowbreak dual\_le}`; tighten line 166; and change line 159 to `\section{The sharp \texorpdfstring{$16$}{16}-column threshold}` (or plain `16`).

### Finding 9 — [Minor] Residual repository jargon in paper body and minor contract/text details
- **Location:** `paper.tex` lines 115, 138, 157, 217, 223, 278, 282, 294, 306, 340, 348, 374, 386; `metadata.toml` line 5.
- **Problem:**
  1. `paper.tex` line 217 mentions an internal registry code: `(registered in the repository as CC-30)`. Lines 115 and 157 name phase-numbered scripts (`phase16_erdos_borwein.py`, `phase17_erdos_borwein_bias.py`), and lines 138, 340, 348, 386 refer to "the repository notes." `WAVE2-CONTRACT.md` (line 95) restricts phase/repository references to Section 13, `VERIFICATION.md`, and `LEDGER.md`.
  2. `paper.tex` line 306 (Proposition 8.1) writes $A_I(2m) = A_{I+1}(m) = A_I(m) + O(m/N)$, whereas $|A_{I+1}(m) - A_I(m)| \le 2/N = O(1/N)$ uniformly in $m$.
  3. `paper.tex` line 278 has a typo `{0,..,r}` (two periods instead of `\dots`).
  4. `paper.tex` lines 282–295 (Theorem 7.5): the proof verifies $\limsup f_I < 0.499856$ along windows and asserts $r_{\min}(16) \le 92$ without adding the one-line observation that the same pointwise inequality $\Phi \ge \Psi_{16}$ yields $f(1) < 1/2$ for every law in $\mathcal{I}_{16,92}$.
  5. `metadata.toml` line 5 sets `status = "research note"` rather than `status = "preprint draft"` listed in `WAVE2-CONTRACT.md` line 45 (clarify if intentional for the research note).
- **Concrete fix:** Remove `CC-30` and phase-numbered script names from the main text (point to Section 13 instead); change $O(m/N)$ to $O(1/N)$ on line 306; fix `{0,\dots,r}` on line 278; add one sentence in the proof of Theorem 7.5 connecting $\Phi$ to $\mathcal{I}_{16,92}$; and confirm `metadata.toml`'s `status` value with the coordinator.

### Finding 10 — [Editorial] Literature omissions in `LEDGER.md` and `paper.tex`
- **Location:** `LEDGER.md`, `paper.tex` lines 38 and 376–389, `references.bib`.
- **Problem:** Several directly relevant published papers found via zbMATH Open and Google Scholar are missing from `LEDGER.md` and/or `paper.tex`: Bailey–Crandall (2002) (gives the dynamical equivalence for 2-normality of $E$ in Conjecture 5.3 / Theorem 5.5), P. Borwein (1991) (the earlier paper directly proving irrationality of $\sum 1/(q^n+r)$), Vandehey (2013) (addresses Erdős's 1948 Lambert-series proof), and Aragón Artacho–Bailey–Borwein–Borwein (2013) (digit walks on constants including $E$). In addition, `references.bib` lists `Crandall, Richard E.` whereas the INTEGERS PDF uses `Richard Crandall` and zbMATH indexes pp. `811–840`.
- **Concrete fix:** Add Bailey–Crandall (2002), Borwein (1991), Vandehey (2013), Aragón Artacho et al. (2013), Sibuya (1991), and Galambos–Simonelli (1996) to `LEDGER.md` (and cite Bailey–Crandall 2002 and Borwein 1991 in `paper.tex` Section 1 / Section 11).

---

## Literature Review Results (Task 3)

### (a) Vaaler (1985) — exact theorem numbers and majorant verification
Retrieved and read the primary AMS PDF (`https://www.ams.org/journals/bull/1985-12-02/S0273-0979-1985-15349-2/S0273-0979-1985-15349-2.pdf`):
- **Reference:** J. D. Vaaler, *Some extremal functions in Fourier analysis*, Bull. Amer. Math. Soc. (N.S.) **12** (1985), no. 2, 183–216, DOI `10.1090/S0273-0979-1985-15349-2`, Zbl `0575.42003`.
- **Exact theorem numbers and pages:**
  - **Theorem 6 (p. 193, eq. (2.28)):** gives the Fourier transform $\hat{J}(t) = \pi t(1 - |t|)\cot(\pi t) + |t|$ for $0 < |t| < 1$.
  - **Theorem 18 (p. 210, eq. (7.14)):** defines $\psi * j_N(x) = \sum_{0 < |n| \le N} (-2\pi i n)^{-1} \hat{J}\bigl(\frac{n}{N+1}\bigr) e(nx)$ (where $\psi(x) = x - \lfloor x \rfloor - \frac{1}{2}$ for $x \notin \mathbb{Z}$, $\psi(0)=0$) and proves $|\psi * j_N(x) - \psi(x)| \le (2N+2)^{-1} k_N(x)$ for all real $x$, where $k_N(x) = \sum_{|n| \le N} \bigl(1 - \frac{|n|}{N+1}\bigr) e(nx)$ is the periodic Fejér kernel (eq. (7.3), p. 207).
  - **Theorem 19 (pp. 211–212, eqs. (7.24)–(7.27)):** for any real-valued $1$-periodic function $f$ of bounded variation normalized at jump points by $f(x) = \frac{1}{2}(f(x+) + f(x-))$, the degree-$N$ trigonometric polynomial $m(f, N, x) = f * j_N(x) + (2N+2)^{-1} (dV_f) * k_N(x)$ satisfies $f(x) \le m(f, N, x)$ everywhere with $\int_{-1/2}^{1/2} (m(f, N, x) - f(x))\,dx = (2N+2)^{-1} V_f$.
  - **Theorem 20 (pp. 213–214, eqs. (8.3)–(8.4)):** specializes Theorem 19 to an interval characteristic function (with $V_f = 2$) to derive the sharp Erdős–Turán inequality.
- **Verification of the formula in Theorem 8.2 (`paper.tex` lines 313, 317):** Taking $f(x) = \frac{1}{2} + \psi(x) - \psi(x - \frac{1}{2})$ (the normalized indicator of $[1/2, 1)$ mod 1, with $dV_f = \delta_0 + \delta_{1/2}$), Theorem 19 yields
  $$S^+_N(x) = \frac{1}{2} + (\psi * j_N)(x) - (\psi * j_N)\bigl(x - \tfrac{1}{2}\bigr) + \frac{1}{2N+2}\bigl(k_N(x) + k_N\bigl(x - \tfrac{1}{2}\bigr)\bigr),$$
  whose Fourier coefficients match `paper.tex` line 313 verbatim: $\hat{S}(0) = \frac{1}{2} + \frac{1}{N+1}$, $\hat{S}(m) = \frac{i}{\pi m}\hat{J}\bigl(\frac{|m|}{N+1}\bigr)$ for odd $m$, and $\hat{S}(m) = \frac{1}{N+1}\bigl(1 - \frac{|m|}{N+1}\bigr)$ for even $m \ne 0$. Furthermore, at the jump points $x \in \{0, 1/2\}$, $(\psi * j_N)(x) - (\psi * j_N)(x-1/2) = 0$ and $k_N(0) = N+1$, so $S^+_N(0) = S^+_N(1/2) = 1 + \frac{k_N(1/2)}{2N+2} \ge 1$; hence $S^+_N(x) \ge \mathbf{1}_{[1/2,1]}(x) \ge \mathbf{1}_{[1/2,1)}(x)$ holds pointwise on all of $\mathbb{R}/\mathbb{Z}$ including both endpoints.

### (b) Parity Bonferroni bound vs. Sibuya (1991) and Galambos–Simonelli (1996)
Retrieved and read the full PDF of **M. Sibuya (1991)**, *Bonferroni-type inequalities; Chebyshev-type inequalities for the distributions on $[0, n]$*, Ann. Inst. Statist. Math. **43** (1991), no. 2, 261–285 (Zbl `0764.60022`, `https://www.ism.ac.jp/editsec/aism/pdf/043_2_0261.pdf`), and checked **M. Sibuya (1992)** (Math. Appl. 80, 165–194, Zbl `0789.60017`) and **J. Galambos & I. Simonelli (1996)**, *Bonferroni-Type Inequalities with Applications*, Springer (Zbl `0869.60014`), plus zbMATH and web searches for parity / even-number-of-events Bonferroni bounds:
- **What Sibuya (1991) proves:** Sibuya considers a discrete count $K$ on the finite integer interval $\{0, 1, \dots, n\}$ with binomial moments $S_r = \mathbb{E}\binom{K}{r}$. His Theorems 2.1, 3.1, 3.2, 3.3, and 7.1 develop the general *majorant–minorant polynomial method* (equivalent to linear programming / Chebyshev systems on the moment space $F_r$) to obtain the most stringent upper and lower bounds for the exact-count probabilities $p_m = \Pr(K = m)$ and tail probabilities $q_m = \Pr(K \ge m)$ in terms of $(S_1, \dots, S_r)$.
- **What Galambos–Simonelli (1996) prove:** They systematize Bonferroni-type inequalities for $p_m = \Pr(K = m)$ and $q_m = \Pr(K \ge m)$ (and multivariate extensions) via three general techniques: the method of polynomials (reducing general event inequalities to polynomial inequalities on binomial variables), geometric methods, and linear programming.
- **Does Theorem 7.1 already follow from Sibuya (1991) or Galambos–Simonelli (1996)?**
  - **Conceptually / methodologically:** Theorem 7.1 is a direct instance of the same polynomial minorant–majorant / LP-duality framework for binomial-moment spaces (specifically, the dual polynomial $q_r(n) = \sum_{k \le r} (-2)^k \binom{n}{k} \le (-1)^n$ with equality on $\{0, \dots, r\}$, paired with the primal law supported on $\{0, \dots, r\}$ whose binomial moments equal $1/k!$, is the exact complementary-slackness certificate in Sibuya's sense, extended from $[0, n]$ to $\mathbb{Z}_{\ge 0}$). Note also that the exact inclusion–exclusion identity $\Pr(N\text{ even}) - \Pr(N\text{ odd}) = \mathbb{E}(-1)^N = \sum_{k \ge 0} (-2)^k S_k$ is classical.
  - **As an explicit published statement:** Neither Sibuya (1991) (0 hits for `parity` or `Poisson`; deals exclusively with $p_m$ and $q_m$ on $[0, n]$) nor the surveyed summaries/indexes of Galambos–Simonelli (1996) state the parity functional $\mathbb{E}(-1)^N$ or the specific Poisson-moment sharp lower bound $\min \mathbb{E}(-1)^N = \sum_{k=0}^r (-2)^k/k!$ (and its sign change at $r = 5$). Thus, the note's qualified novelty stance ("possibly a special case of known extremal theory for given binomial moments; specific statement not located") is appropriate, and Sibuya (1991) and Galambos–Simonelli (1996) should be explicitly cited as the general methodological framework.

### (c) Crandall (2012) and Tao–Teräväinen (`arXiv:2512.01739v2`)
- **Crandall (2012):** Checked directly on `https://math.colgate.edu/~integers/m23/m23.pdf` and zbMATH Open (`Zbl 1266.11023`).
  - Exact title: *The Googol-th Bit of the Erdős–Borwein Constant*.
  - Author on PDF: `Richard Crandall` (Center for Advanced Computation, Reed College).
  - Venue: *INTEGERS* **12** (2012), `#A23` (received 11/5/11, accepted 2/25/12, published 3/1/12; zbMATH also records No. 5, pp. 811–840).
  - Section 6 (`pp. 7–9`) counts (`4359105565638` zeros, `4436987456570` ones, plus base-4, base-8, and base-16 tables) match the arrays in `phase17_erdos_borwein_bias.py` lines 988–995 verbatim.
- **Tao–Teräväinen (`arXiv:2512.01739`):** Retrieved and inspected the current arXiv source (`2512.01739v2`, submitted 2025-12-01, revised 2026-04-25; file `main2.tex`).
  - **Confirmed v2 theorem numbering** (all environments share the `theorem` counter within each section):
    - Theorem 1.1: Erdős #248 ($\omega(n+k) \le \Omega(n+k) \le Ck$).
    - Remark 1.2; **Theorem 1.3**: Erdős #69 (irrationality of $\sum \omega(n)/2^n$).
    - Remark 1.4; Definition 1.5 ($c_\tau$); Remark 1.6.
    - **Theorem 1.7** (`\label{consecutive-omega-thm}`): Problems of Erdős–Pomerance–Sárközy and Hildebrand — gives $\Pr(\tau(\mathbf{n}) = \tau(\mathbf{n}+1)) = \frac{c_\tau + O(\log_2^{-c} x)}{2\sqrt{\pi\log_2 x}}$ for $x \in \mathcal{X}$ outside an exceptional set of logarithmic density $\ll \log_2^{-c} X$. (**Note:** `paper.tex` line 349 misprints the denominator as $\sqrt{2\pi\log_2 x}$; see Finding 2.)
    - Theorem 1.8 (`\label{thm:smooth}`): consecutive smooth numbers.
    - **Theorem 3.1** (`\label{thm:correlation}`): quantitative two-point correlation estimate for $1$-bounded multiplicative $g_1, g_2$, with Case (i) Equidistributed (eqs. (3.1)–(3.2)) and Case (ii) Non-pretentious (eq. (3.3): $\exp(M(g_1; X^2, \log^{1/125} X)) \gg \mathcal{L}$), yielding eq. (3.4) for $N \in [\sqrt{X}, X] \setminus \mathcal{E}$ with $\frac{1}{\log X}\int_{\mathcal{E}} \frac{dt}{t} \ll \mathcal{L}^{-c}$, uniformly for $W \in [\mathcal{L}^c]$ and $b, h_1, h_2 = O(\mathcal{L}^c)$, $h_1 \ne h_2$.
  - **Could Theorem 3.1 apply to $e(\theta V)\chi(U)$?**
    **Yes, in Case (ii) (non-pretentious), for each fixed $\theta$ in the non-pretentious range $1/R \le \|\theta\| \le 1/2$:**
    1. Both $g_1(m) = e(\theta V(m))\chi_1(U(m))$ and $g_2(m) = e(-\theta V(m))\chi_2(U(m))$ are $1$-bounded multiplicative functions.
    2. On primes $p$, $\tau(p) = 2$ gives $V(p) = 1$ and $U(p) = 1$, so $g_1(p) = e(\theta)$ independently of $\chi_1$—identical to the prime values of Tao–Teräväinen's own Section 4.1 function $e(\alpha \Omega_{>w}(n))$ (with $w=1$).
    3. Case (ii) requires **only** eq. (3.3), **not** the prime-band condition (3.2) (which applies only to Case (i) and is commented out under Case (ii) in `main2.tex`).
    4. Since the pretentious distance $M(g_1; X^2, \log^{1/125} X)$ depends only on prime values $g_1(p)$, Tao–Teräväinen's Section 4.1 argument (lines 70–89 of Section 4.1 in `main2.tex`) directly yields $M(g_1; X^2, \log^{1/125} X) \gg R^{-2} \log_2 X$ for $1/R \le \|\theta\| \le 1/2$. Taking e.g. $R = L_N = (\log T)^2$ or $T^{1/4}$ ($T = \log_2 X$) and $\mathcal{L} = \exp(c_0 R^{-2} T)$ satisfies $\mathcal{L} \le \log X$ and $\exp(M) \gg \mathcal{L}$, while $\mathcal{L}^c \gg A_N \sqrt{T}$ and $\mathcal{L}^{-c} = o((A_N \sqrt{T})^{-1})$!
    5. **Caveat on $\theta$-uniformity:** Theorem 3.1's exceptional set $\mathcal{E} = \mathcal{E}_\theta$ depends on $g_1$ (hence on $\theta$). Thus Theorem 3.1(ii) does **not** immediately give a *single* exceptional set valid pointwise for all $\theta \in [1/L_N, 1/2]$ (as Hypothesis E is literally stated), because $V(m) \le \log_2 m$ makes a crude $\theta$-net require $\asymp \log N \gg \mathcal{L}^c$ points. However, for the actual application to $M_2(b)$, one integrates over $\theta$ and $x$ via Fubini/Minkowski—exactly as Tao–Teräväinen do in eq. (4.4) (`\eqref{high-frequency}`)—which **does** work directly with $\theta$-dependent $\mathcal{E}_\theta$ and finitely many $\chi_1, \chi_2 \bmod 2^r$, yielding $M_2(b) \to \nu(F)\nu(G)$ along almost all scales (assuming K2 / the low-frequency part). As the note itself emphasizes (Theorem 6.1), two-point correlations alone still cannot decide the bias; passing to $r \ge 3$ (and $r \ge 9$) remains the genuine barrier.

### (d) zbMATH Open and Google Scholar searches on Erdős–Borwein digits, normality, and binary expansion
Queried zbMATH Open (`api.zbmath.org/v1/document/_search`) and web/scholar indexes for `"Erdős–Borwein"`, `"Erdos-Borwein"`, `"1/(2^n-1)"`, `"Lambert series binary digits"`, `"Bailey Crandall 2-normal"`, `"Borwein 1/(q^n+r)"`, and `"Vandehey Erdos Lambert"`. Relevant published works missed by `LEDGER.md` (and/or omitted from `paper.tex`):
1. **D. H. Bailey and R. E. Crandall (2002)**, *Random generators and normal numbers*, Experimental Mathematics **11** (2002), no. 4, 527–546 (Zbl `1165.11328`). Section 5 (Conjecture 5.3, Theorem 5.5) establishes an explicit dynamical/equidistribution equivalence for 2-normality of $E$ and discusses 2-density; mentioned in `LEDGER.md` line 10 as "not cited" and in `notes/phase13/erdos-borwein.md` line 14, but missing from `LEDGER.md` entries and `paper.tex`.
2. **P. B. Borwein (1991)**, *On the irrationality of $\sum (1/(q^n + r))$*, J. Number Theory **37** (1991), no. 3, 253–259, DOI `10.1016/S0022-314X(05)80041-1`, Zbl `0718.11029`. Earlier paper directly covering $\sum 1/(q^n+r)$ (noted as unchecked in `LEDGER.md` line 22; `paper.tex` line 38 cites only Borwein 1992).
3. **F. J. Aragón Artacho, D. H. Bailey, J. M. Borwein, and P. B. Borwein (2013)**, *Walking on real numbers*, Math. Intelligencer **35** (2013), no. 1, 42–60, Zbl `1282.11088`. Experimental digit-walk and randomness study covering classical constants including the Erdős–Borwein constant.
4. **J. Vandehey (2013)**, *On an incomplete argument of Erdős on the irrationality of Lambert series*, Integers **13** (2013), Paper A58, 6 pp., Zbl `1284.11101`, `arXiv:1206.0340`. Examines Erdős's 1948 Lambert-series irrationality proof (identifying and resolving the negative-base gap while confirming the positive-base argument for $E$).
5. *(Tangential—irrationality/inequalities rather than digits, recorded for completeness of the zbMATH sweep):* M. Merca (2015), *A double inequality involving Erdős–Borwein constants*, Miskolc Math. Notes **16** (2015), no. 1, 277–281 (Zbl `1340.26050`); S. Murakami and Y. Tachiya (2025), *Linear independence of certain infinite series with monomial orders*, Int. J. Number Theory **21** (2025), no. 8, 1777–1794 (Zbl `1579.11115`).

No published paper on zbMATH Open or Google Scholar was found that states the Poisson-column model $Q_\infty$, the sharp $D = 16$ threshold, the $k \le 4$ column-hierarchy countermodels, the parity Bonferroni bound for $\mathbb{E}(-1)^N$, or the degree 110/116 Fourier thresholds.

### (e) Verification of bibliography entries (10 entries checked)

| BibTeX key | Source checked | Status | Notes / discrepancies |
| --- | --- | --- | --- |
| `erdos1948` | zbMATH (`Zbl 0032.01701`) + scan PDF (`users.renyi.hu/~p_erdos/1948-04.pdf`, 603,601 bytes) | **Verified** | Author, title, journal, vol. 12, pp. 63–66, 1948 match. |
| `borwein1992` | Crossref (`10.1017/S030500410007081X`) | **Verified** | Vol. 112, no. 1, pp. 141–146, 1992 match. (Should also cite Borwein 1991, *J. Number Theory* 37(3):253–259, for $\sum 1/(q^n+r)$.) |
| `crandall2012` | Primary PDF (`math.colgate.edu/~integers/m23/m23.pdf`) + zbMATH (`Zbl 1266.11023`) | **Verified (minor)** | Title, vol. 12, `#A23`, dates match. PDF prints `Richard Crandall` (no `E.`); Zbl also indexes pp. 811–840. |
| `campbell2026` | arXiv API (`2605.24160v1`) + zbMATH | **Verified** | Title, author, submitted `2026-05-22` match. |
| `tt2025` | arXiv API + e-print source (`2512.01739v2`, `main2.tex`) | **Verified** | Title, authors, v1 `2025-12-01`, v2 `2026-04-25` match; theorem numbers 1.3, 1.7, 3.1 confirmed (see Finding 2 for misquoted constant in `paper.tex`). |
| `tt2019` | Crossref (`10.5802/jtnb.1062`) | **Bug in `.bib`** | Metadata matches (vol. 30, no. 3, pp. 997–1015, 2019), **but** line 54 writes `Th{'e}orie` (missing `\`), rendering literally as `Th’eorie` in `paper.pdf`. |
| `tao2016` | Crossref (`10.1017/fmp.2016.6`) | **Incomplete** | Vol. 4, 2016 match; missing article number **`pages = {e8}`**. |
| `mrt2015` | Crossref (`10.2140/ant.2015.9.2167`) | **Verified** | Vol. 9, no. 9, pp. 2167–2196, 2015 match. |
| `heathbrown1984` | Crossref (`10.1112/S0025579300010743`) | **Verified** | Vol. 31, no. 1, pp. 141–149, 1984 match. |
| `vaaler1985` | Crossref (`10.1090/S0273-0979-1985-15349-2`) + AMS PDF + zbMATH (`Zbl 0575.42003`) | **Verified (update note)** | Vol. 12, no. 2, pp. 183–216, 1985 match. Theorems 6, 18, 19, 20 verified on primary PDF; remove "unverified" note. |
