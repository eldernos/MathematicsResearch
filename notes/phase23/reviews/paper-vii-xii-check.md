# Cross-Provider Verification Check: Paper VII v2.0 Split & Paper XII v1.0

- **Date:** 27 November 2026
- **Scope:** Read-only verification of `papers/07-synthetic-expansions-v2/` (Paper VII v2.0 candidate draft) and `papers/12-all-prime-normality-exponents/` (Paper XII v1.0 candidate draft).
- **Verdict:** **ACCEPT**

> **Cross-model review is not independent human peer review.** This check was performed by an AI model and does not constitute independent human peer review.

---

## 1. Archived-Release Immutability

Checked via `git status --short` and `git diff --stat` on:
- `papers/07-synthetic-expansions/`
- `papers/manifest.toml`
- `papers/SHA256SUMS`
- `papers/alphaxiv-records.toml`
- `docs/registry/papers.toml`

**Result: PASS.** Zero modifications to any archived release file or manifest/registry ledger.

---

## 2. LaTeX Structural Integrity

Checked independently with a Python parser over `paper.tex` and `references.bib` (stripping LaTeX comments and escaped braces):

| Check | Paper VII v2.0 (`2730` lines) | Paper XII v1.0 (`1034` lines) |
| --- | --- | --- |
| `\begin`/`\end` environment balance | PASS (0 errors, 0 unclosed) | PASS (0 errors, 0 unclosed) |
| Brace balance (`paper.tex` & `references.bib`) | PASS (`final=0, min=0`) | PASS (`final=0, min=0`) |
| Labels | 107 distinct (0 duplicates) | 46 distinct (0 duplicates) |
| `\ref`/`\cref`/`\Cref`/`\eqref` targets | 96 distinct, **0 undefined** | 35 distinct, **0 undefined** |
| `\cite` keys vs `references.bib` | 36/36 matched, **0 undefined, 0 uncited** | 21/21 matched, **0 undefined, 0 uncited** |
| Removed §9 labels in Paper VII v2.0 (18 labels) | **0 leftover occurrences** | N/A |

Cross-manuscript statement numbers cited by Paper XII (`Lemma 7.10`, `Theorem 7.18`, `Theorem 7.20`, `Lemma 7.23`, `Theorem 7.24`, and `§7.5` of Paper VII v2.0) were verified against a structural counter scan of `papers/07-synthetic-expansions-v2/paper.tex`: all 5 statement numbers match.

---

## 3. Mathematical Consistency (Phase 23 Audit 2 & Track C1–C4)

**Audit 2 (`GF-25`) repairs — PASS:**
- **Exact 2-adic order formula:** Paper XII Lemma 3.5(ii) (`lem:exactorder`) gives $e_2(b,r)=\max(0,r-v_2(b-1))$ for $b\equiv1\pmod4$, $\max(1,r-v_2(b+1))$ for $b\equiv3\pmod4, r\ge2$, and $0$ for $b\equiv3\pmod4, r=1$, replacing the earlier false lower bound.
- **$\operatorname{ord}_{16}(7)=2$:** Explicitly illustrated after Paper XII Lemma 3.5 ($b=7, r=4, 7^2\equiv1\pmod{16}$, so $\operatorname{ord}_{16}(7)=2<4$).
- **Sharpness constant:** Both Paper VII v2.0 (after Lemma 2.7) and Paper XII (after Lemma 3.1) give the exact geometric-sum ratio $|S|/M=\sin(\pi M/p^a)/(M\sin(\pi/p^a))\ge\sin(\pi/10)/(\pi/10)>0.983$ with $p^a\ge10$ and $A=\log_p(10M)+O(1/M)$.
- **Weak inequality $\operatorname{ord}_{M'}b\le M'$:** Explicitly used in both Paper VII v2.0 (after Corollary 2.8) and Paper XII (after Corollary 3.2), noting equality at $M'=1$.
- **Auxiliary-prime & run conventions:** Paper XII Lemma 3.3 uses $1+\omega(b)$ excluded primes; Paper VII v2.0 Theorem 7.21 and Paper XII Theorem 5.3 split at $\lceil\sqrt N\rceil$, trim $B=\lceil2\log_bN\rceil$, keep $T\ge T_0/2$, and apply the pointwise tail bound only at trimmed positions.

**Track C1–C4 consistency — PASS:**
- **`DEKKM Theorem 1`:** Paper VII v2.0 Theorem 9.11 (`thm:dekkm`, labeled *External input*) cites `\cite[Theorem~1]{DEKKM}` with $\limsup(\sigma_{n+1}-\sigma_n)/\log\sigma_n\ge390/449$ (natural logarithm, zero coordinates allowed) and notes that the general-discriminant theorem is too weak. Theorem 9.12 (`thm:squareirr`) deduces irrationality of $C(b,p,s,2)^2$ for $s<(390/449)\,t\log b$ (including all $s=1$).
- **Freezing threshold:** Paper VII v2.0 Theorem 7.20 (`eq:freezeJ`) and Paper XII Theorem 5.1 both state $J\ge J_1(L)=\max(L,\lceil L/s_1\rceil+\lceil L/d\rceil)$ and record the weight-gap fixture ($L=2,J=1,u=1$).
- **Multivariate effective rate:** Paper VII v2.0 Lemma 7.23 (`lem:wiso`) supplies the standalone weighted averaged isolation lemma with explicit parameter order $(c,\kappa,\lambda,\mu_0,A,H_*,\epsilon_0)$, and Theorem 7.24 (`thm:severalrate`) establishes $D_N\ll(\log\log N)^{-d/(d-1)}$ and $N^{-\eta_P}$ for a single linear maximizer; Paper XII Theorems 5.2–5.3 import and extend this cleanly to growing auxiliary support.
- **$\mu=2$ in all degrees (Paper XII Theorems 7.3–7.4):** Lemma 7.1 (`lem:determinant`), Lemma 7.2 (`lem:upperset`), Theorem 7.3 (`thm:doubling` for $W,W'$), and Theorem 7.4 (`thm:dense` for positive $V$ with $n_j\asymp j\sqrt{\log j}$, $n_{j+1}/n_j\to1$, and regrouping $d_k=c_k+\lambda_k-\lambda_{k-1}$) match Track C4, alongside Proposition 6.1's $(3+\sqrt5)/2$ truncation-separation ceiling.

---

## 4. Evidence Separation, Pending-PDF Note & Disclaimers

- **Strict evidence separation:** **PASS.** Both `VERIFICATION.md` files cleanly separate `Kernel-verified`, `Lean-supported paper proof`, `Paper proof`, `Finite certificate`, `External input`, `Conditional`, and `Open`, explicitly bounding Lean-supported claims to named finite cores and separating finite measurements from asymptotic proofs.
- **Paper XII Lemma 7.1 (`lem:determinant`):** Conservatively labeled **Paper proof** (does not cite `Phase23Cores.ratBadness_folding_step`), which is accurate and appropriate.
- **Pending-PDF compilation note:** **PASS.** Both `VERIFICATION.md` files (and `CHANGES.md` / `LEDGER.md`) explicitly state that `pdflatex` and `bibtex` are unavailable locally and on `hail`, that PDF compilation is pending before release, and that statement numbers come from a structural count of `paper.tex`.
- **Disclaimer:** **PASS.** Both `VERIFICATION.md` files, both `LEDGER.md` files, and the "Use of AI tools" sections of both `paper.tex` files explicitly include `Cross-model review is not independent human peer review.`

---

## 5. Non-Blocking Editorial Nits (Optional Pre-Release Cleanup)

1. `papers/07-synthetic-expansions-v2/paper.tex` line 13 (LaTeX comment only): still mentions `ProtectedPole` alongside `PowerSumPeeling`, whereas `ProtectedPole` moved to Paper XII (the prose in §11 already omits it).
2. `papers/07-synthetic-expansions-v2/LEDGER.md` line 113 (Outstanding check #4): still mentions "the Halberstam–Richert sieve statement", although `HR74` moved to Paper XII (as recorded on line 27 of the same file).

Neither nit affects mathematical correctness, LaTeX integrity, or evidence discipline.

---

## Final Verdict

**ACCEPT.** Both manuscripts (`papers/07-synthetic-expansions-v2/` and `papers/12-all-prime-normality-exponents/`) pass all structural, immutability, mathematical-consistency, and evidence-discipline checks for the Phase 23 split candidate drafts, with PDF typesetting and script commits honestly documented as pending owner release steps.

Cross-model review is not independent human peer review.
