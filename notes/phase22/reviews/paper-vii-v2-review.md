# Cross-Provider Referee Audit: Paper VII v2.0 Candidate Draft

- **Manuscript audited:** *Synthetic Arithmetic Expansions and Prescribed Discrepancy* (Version 2.0, candidate draft of 26 November 2026), [`papers/07-synthetic-expansions-v2/paper.tex`](../../../papers/07-synthetic-expansions-v2/paper.tex) (2,757 lines, 47 pages), with [`references.bib`](../../../papers/07-synthetic-expansions-v2/references.bib), [`VERIFICATION.md`](../../../papers/07-synthetic-expansions-v2/VERIFICATION.md), [`LEDGER.md`](../../../papers/07-synthetic-expansions-v2/LEDGER.md), and [`CHANGES.md`](../../../papers/07-synthetic-expansions-v2/CHANGES.md).
- **Referee:** Gemini 4 Neon (independent cross-provider review of draft prepared by Claude Opus 5.5).
- **Date:** 26 November 2026.
- **Verdict:** **ACCEPT AFTER REVISION**

> **Disclaimer.** This is an AI cross-model referee audit. **Cross-model review is not independent human peer review.** No human specialist has checked the written proofs, external citations, or literature claims of this manuscript.

---

## Executive Summary

The Paper VII v2.0 candidate draft is an unusually clean, mathematically serious consolidation of v1.0 with the higher-degree polynomial normality theory (§§7.5–7.9), base-uniform short-orbit estimates (§2.1), all-prime polynomial normality and irrationality exponents (§9), and the equality boundary $d = r$ (§10). Every main theorem (Theorems A–G) is mathematically true as stated, and **no Critical mathematical flaws** were found. In particular:

- **Both adapted proofs are sound.** Deducing Theorem 7.19 from the small-ball Theorem 7.18 (rather than the earlier constant-measure argument) is valid and cleaner, and the self-contained Lemma 10.5 (`lem:sparseint`) establishing $K_b$-absorption of $X_H$ passes a full constant-by-constant verification (only minor hypothesis guards are needed in Theorem 10.6 where Lemma 10.5 is invoked).
- **v1.0 backward compatibility is fully preserved.** `papers/07-synthetic-expansions/` is completely untouched (`git status` and `git diff` empty), every v1.0 label and statement number (A–E, 2.1–2.6, 3.1, 4.1–4.8, 5.1–5.4, 6.1–6.5, 7.1–7.9, 8.1–8.5) is preserved without shifting, and all 33 Lean declaration links across commits `e4809cf`, `c2c9da6`, and `347ec3f` match their exact lines and declaration names.
- **Open-problem discipline is strictly honored.** Correction B is respected everywhere: finiteness of $\mu(W_H)$ and non-Liouville status for both $W_H$ (Theorem 9.7 / Proposition 9.9) and the quasi-polynomial series (Remark 9.12) remain explicitly open. Likewise, normality (and even $\limsup_N D_N < 1$ or $D_N \not\to 1$) of $\xi^3$ and $C(b,p,s,2)^2$ remains explicitly open, and finite digit computations are kept strictly labeled as measurements.

However, the audit identified **6 Major findings** (localized proof slips, a double-shift notational bug in §10, an abstract overstatement, evidence-label contradictions, and pre-release reproducibility/wording blockers) and **12 Minor findings** that should be resolved before release. None threatens the truth of any main theorem; all admit short, concrete fixes.

---

## Severity-Classified Findings

### Critical Findings

**None.**

---

### Major Findings

#### M1. Insufficient freezing threshold in Theorem 7.20 (`paper.tex`, lines 1755–1760)
- **Location:** [`paper.tex:1755-1760`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1755-L1760) (Proof of Theorem 7.20, *Reduction*).
- **Issue:** The proof claims that for $J \ge \lceil L/s_1 + L/d \rceil$,
  $$p^{S^* J} b^{-n} R_n(P) \equiv M_P(u) \pmod{p^L},$$
  because "monomials outside $T$ carry a factor $p^J$." In Lemma 7.10 (single order $s$), lower-degree monomials carry $p^{(r-j)sJ}$ with $sJ \ge L$, so $J \ge \lceil L/s + L/d \rceil$ suffices. With several distinct orders $1 \le s_1 < \dots < s_m$, however, a monomial $\nu \notin T$ can have $S^* - s \cdot \nu = 1$, carrying only $p^J$. Whenever $1/s_1 + 1/d < 1$ (for instance $s_1 = 2, s_2 = 3, d = 5$, $P = X_2^2 + X_1 X_2$, where $S^* = 6$ and $s \cdot (1,1) = 5$), one has $\lceil L/s_1 + L/d \rceil < L$ for $L \ge 4$, so $p^J \not\equiv 0 \pmod{p^L}$ and the displayed congruence fails at the stated threshold.
- **Concrete fix:** Replace `J \ge \lceil L/s_1 + L/d \rceil` on line 1755 with `J \ge \max(L, \lceil L/s_1 + L/d \rceil)` (or `J \ge L + \lceil L/d \rceil`, matching Lemma 7.4). Because Theorem 7.20 is qualitative, nothing downstream changes.

#### M2. Double shift $b^n R_n$ in Section 10 contradicts the paper's definition of $R_n$ (`paper.tex`, lines 2479 and 2603)
- **Location:** [`paper.tex:2479`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2479) (Proposition 10.4) and [`paper.tex:2603`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2603) (§10.3 prose).
- **Issue:** Throughout §§4, 7, and 9 (lines 621, 707, 1110, 2050), $R_n(Z) = \sum_{m \le n} a_m b^{n-m}$ is already the **shifted** prefix (multiplied by $b^n$). Section 10 imports formulas from `notes/phase22/nonlinear-equality-boundary.md` (where $R_n$ denoted the *unshifted* prefix), writing on line 2479 "the shifted prefixes satisfy $\{b^n R_n(Z_H)\} = \{p^{sH} b^n R_n(C^r)\}$" and on line 2603 "so the orbit of $\{b^n R_n(Z_H)\}$ restarts only at the positions $\mathcal P_H^{\rm frac}$." Under the manuscript's definition of $R_n$, $b^n R_n$ multiplies by $b^{2n}$; on line 2603, $\{b^n R_n(Z_H)\}$ advances by $b^2$ per shift and is not the radix orbit of $Z_H$.
- **Concrete fix:** Delete the extra factor $b^n$ in both places, writing `\fr{R_n(Z_H)}=\fr{p^{sH}R_n(C^r)}` on line 2479 and `\fr{R_n(Z_H)}` on line 2603.

#### M3. Overstatement in the Abstract for polynomial-schedule and finite-exponent $\lambda$ constructions (`paper.tex`, lines 42–45)
- **Location:** [`paper.tex:42-45`](../../../papers/07-synthetic-expansions-v2/paper.tex#L42-L45) (Abstract).
- **Issue:** The sentence reads:
  > We construct explicit series whose shifted prefix denominators eventually contain every prime not dividing $b$ and **all of whose nonconstant rational polynomial images are normal**: a Liouville example, **examples on polynomial schedules**, and **examples with finite irrationality exponent $\lambda$ (degree at most $\lambda - 1$)** or $p$ (all degrees).
  Two inaccuracies arise:
  1. The polynomial-schedule examples $W_H$ (Theorem F(ii) / Theorem 9.7) are only proved normal for polynomials of degree $r \le d - 1$, not for *all* nonconstant polynomials. (The all-degree quasi-polynomial example of Remark 9.12 is stated without proof and is not on a polynomial schedule.)
  2. The geometric-schedule examples $W_G$ (Theorem F(iii) / Theorem 9.10) require $p > (r + 1)!$ in addition to $\lambda \ge \max(3, r + 1)$, so for a fixed prime $p$ they do not reach degree $\lambda - 1$ whenever $\lambda! \ge p$.
- **Concrete fix:** Rewrite lines 42–45 so the degree scope matches Theorem F exactly, e.g.: "We construct explicit series whose shifted prefix denominators eventually contain every prime not dividing $b$ and whose nonconstant rational polynomial images are normal: a Liouville example (all degrees), examples on polynomial schedules $tk^d$ (degree $< d$), and examples with finite irrationality exponent $\lambda$ (degree $\le r < \lambda$ when $p > (r+1)!$) or $p$ (all degrees)."

#### M4. Local hypothesis and arithmetic slips in Lemma 7.16 and Theorem 7.18 (`paper.tex`, lines 1624 and 1705)
- **Locations:** [`paper.tex:1624`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1624) (Proof of Lemma 7.16) and [`paper.tex:1705`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1705) (Proof of Theorem 7.18).
- **Issues:**
  1. **Uncapped $\alpha$ in Lemma 7.16 (line 1624):** The proof sets $\alpha = v'/H$ and $\beta = \min(1, H'/H)$ and applies Lemma 7.15, which requires $\beta/r \le \alpha \le \beta \le 1$. When $H' > H$ (which occurs whenever $p \le r$ and $s \le e_r$, e.g., $p = 3, r = 3, s = 1$ gives $H' = H + 1$) and the coarse losses of $w$ sum to $0$, we have $v' = H' > H$, so $\alpha = v'/H > 1 = \beta$, violating Lemma 7.15's hypothesis $\alpha \le \beta \le 1$.
  2. **Sum of subtracted fractions in Theorem 7.18 (line 1705):** The proof bounds the main collision term by $x H^{r-1} p^H / (4A)$ and "every error term" by $p^{(1-\mu/2)H} \le x H^{r-1} p^H / (4A)$, then deduces "Hence at least $x H^{r-1} p^H / (2A)$ centres with value in $X_j$ are isolated." Because there are **two** error terms—one subtracted from the lower bound on centres ($A N_j H^A p^{\kappa H}$) and one added to the upper bound on non-isolated centres ($A N_j H^A p^{(1-\mu)H}$)—plus the main collision term, these bounds only yield $(1 - \frac14 - \frac14 - \frac14) A^{-1} = \frac{1}{4A}$, not $\frac{1}{2A}$.
- **Concrete fixes:**
  1. On line 1624, set $\alpha = \min(1, v'/H)$. Then $\beta/r \le \alpha \le \beta \le 1$ holds in all cases, and $0 \le v' - \alpha H \le \lfloor e_r/s \rfloor = O(1)$ changes $E_1$ and $E_2$ by at most $O(1)$.
  2. On line 1705, bound each error term by $p^{(1-\mu/2)H} \le x H^{r-1} p^H / (8A)$ (which holds for large $L$ since $p^{\mu H/2} \gg (\log L)^{24}$), giving $(1 - \frac14 - \frac18 - \frac18) A^{-1} = \frac{1}{2A}$.

#### M5. Evidence-label contradictions across `paper.tex` and `VERIFICATION.md`
- **Locations:** [`paper.tex:321`](../../../papers/07-synthetic-expansions-v2/paper.tex#L321), [`paper.tex:1661`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1661), [`paper.tex:1725`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1725), [`paper.tex:1743`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1743), [`paper.tex:2721`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2721), and [`VERIFICATION.md:99`](../../../papers/07-synthetic-expansions-v2/VERIFICATION.md#L99).
- **Issues:**
  1. Line 2721 of `paper.tex` asserts: "In particular Theorems 7.1, 7.19, 7.20, 7.18, 7.21 and Corollaries 7.2, 7.22 are paper proofs and are not formalized." This directly contradicts the `\evidence{Lean-supported paper proof}` labels attached to Theorem 7.19 (line 1725) and Theorem 7.20 (line 1743), as well as `VERIFICATION.md` lines 84–85. (Note also an internal asymmetry: Theorem 7.18 is labeled `Paper proof` despite directly invoking Lean-supported Lemmas 7.12 and 7.16, whereas Theorem 7.19 is labeled `Lean-supported paper proof` via 7.18 and 4.3.)
  2. `VERIFICATION.md` line 99 describes the external input for Theorem 9.11—`PaperIv2`, Lemmas 2.2–2.4—as `(Lean-supported there)`. Checking [`papers/01-stoneham-polynomials-v2/paper.tex`](../../../papers/01-stoneham-polynomials-v2/paper.tex#L237-L296) shows that Lemmas 2.2 (`refllemma`, L245), 2.3 (`losslemma`, L262), and 2.4 (`poles`, L280) are all labeled `\evidence{Paper proof}` (only Lemma 2.5 and Theorem A are Lean-supported there).
  3. Line 321 of `paper.tex` defines five statement labels ("Each numbered statement carries one label: ... *Finite certificate* ..."), yet no numbered statement in `paper.tex` carries `\evidence{Finite certificate}` (Proposition 7.17 carries `\evidence{Paper proof}`, though `VERIFICATION.md` L82 and `paper.tex` L2736 describe its finite part as a finite certificate).
- **Concrete fixes:**
  1. Reword `paper.tex` line 2721 so it accurately separates the purely written statements (7.1, 7.2, 7.21, 7.22; and 7.18 if kept `Paper proof`, though labeling 7.18 `Lean-supported paper proof` via 7.12 and 7.16 is more consistent) from the `Lean-supported paper proof` theorems (7.19, 7.20), stating clearly that the full statements and analytic/measure-theoretic steps of all of them are not formalized.
  2. In `VERIFICATION.md` line 99, change `(Lean-supported there)` to `(Paper proofs there)`.
  3. Either attach `\evidence{Paper proof; finite certificate}` to Proposition 7.17 or rephrase line 321 so *Finite certificate* is introduced for certified finite sub-claims rather than promising a standalone statement banner that never occurs.

#### M6. Reproducibility gaps in Proposition 7.17 and internal workflow language in §13 (`paper.tex`, lines 1663–1674, 2732–2738, 2750–2753)
- **Locations:** [`paper.tex:1663-1674`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1663-L1674), [`paper.tex:2732-2738`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2732-L2738), [`paper.tex:2750-2753`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2750-L2753).
- **Issues:**
  1. **Proposition 7.17 ($H = 4, 5$):** For $H = 4$, $\rho_4 = 1/8193 \approx 1.22 \times 10^{-4} < \delta_4 = 1/5184 \approx 1.93 \times 10^{-4}$; for $H = 5$, $\rho_5 = 1/14855 \approx 6.73 \times 10^{-5} < 2\delta_5 = 1/12150 \approx 8.23 \times 10^{-5}$. Consequently, the target interval $(2 + \rho_H + \delta_H, 2 + 2\rho_H - \delta_H)$ is **empty** for $H = 4$ and $H = 5$ (the "no isolated centre" clause is vacuously true there, though the $\delta_H$-net property on $(2 + \rho_H, 2 + 2\rho_H]$ does hold—I verified $H = 4, \dots, 14$ independently in Python with exact rationals). Moreover, the $H = 4$ exact check cited on lines 1673 and 2737–2738 was run in an uncommitted scratch script and is **not** in `scripts/phase21_nonlinear.py` (which tests `H in (6, 10, 100, 1000, 4000)`). Simply stating Proposition 7.17 for $H \ge 6$ eliminates both the empty-interval cases ($H = 4, 5$) and the missing repository check for $H = 4$ (or else add $H = 4$ to `scripts/phase21_nonlinear.py` and drop the unnecessary $\pm \delta_H$ shrinkage on the interval, since the net gap is strictly $< 2\delta_H$ so every point of $(2+\rho_H, 2+2\rho_H]$ already lies strictly within $\delta_H$ of a competitor).
  2. **Untracked scripts referenced as present in release:** Lines 2732–2734 state that `scripts/phase22_short_orbits.py` and `scripts/phase22_nonlinear_boundary.py` are in the repository at release; both are currently untracked in git (already flagged in `VERIFICATION.md` L140 and `LEDGER.md` L92—must be committed before release).
  3. **Internal workflow phrasing in §13:** Lines 2750–2753 expose internal development workflow details ("rests on source arguments that each had one cross-provider model review, with the findings repaired and the repairs re-read by a model; the assembled manuscript has not yet been reviewed as a whole").
- **Concrete fixes:** Change $H \ge 4$ to $H \ge 6$ in Proposition 7.17 (or add $H = 4$ to `scripts/phase21_nonlinear.py` and explain the empty-interval boundary); commit the two Phase 22 scripts before release; and rewrite lines 2750–2753 in §13 to match v1.0's clean disclosure style (stating that the written proofs have been checked only by AI models from different providers, that cross-model review is not independent human peer review, and that no human specialist has read them).

---

### Minor Findings

1. **Lemma 2.9 prime-exclusion count and $\log\log$ guard ([`paper.tex:537`](../../../papers/07-synthetic-expansions-v2/paper.tex#L537), [`paper.tex:544`](../../../papers/07-synthetic-expansions-v2/paper.tex#L544)):** Line 544 writes `\pi(x) - 2 - x^{2/3}\log_2 b \le d(M) x^{2/3}`, implicitly assuming at most two primes divide $pb$. For composite $b$ (e.g., $b = 6, p = 5$), more than two primes divide $pb$. Replace `2` with `\omega(pb)` (note $\omega(pb) \le 1 + \log_2 b$ keeps $x_0(b)$ independent of $p$). Also guard `\log\log\ord_\Lambda b` on line 537 by requiring $\ord_\Lambda b \ge 3$ (or writing `\log\log(\ord_\Lambda b + 3)`).
2. **Theorem 10.6 edge-case guards for Lemma 10.5 ([`paper.tex:2517-2518`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2517-L2518)):** Lemma 10.5 requires $\epsilon \in (0, 1)$ and $1 \le L \le N$. In Theorem 10.6, $\rho = (1 + S(2N))/N$ can satisfy $\rho \ge 1$ for small $N$ (e.g., $N = 3, t = 1$), and $L = \lceil \log_b(6 C_F / ((b-1)\rho^2)) \rceil$ can be $\le 0$ for large $b, t$ and $H = 0$ (e.g., $p = 10007, b = 10000, t = 10006$). Fix by putting $L = \max(1, \lceil \log_b(6 C_F / ((b-1)\rho^2)) \rceil)$ and noting that both $\rho \ge 1$ (bounded $N$) and $L > N$ (which forces $sH \gg N$) are trivial.
3. **Sharpness example after Lemma 2.7 ([`paper.tex:504-506`](../../../papers/07-synthetic-expansions-v2/paper.tex#L504-L506)):** For $G = 1 + p^a$ and $M = \lfloor p^a/10 \rfloor$, the claims $|S| > 0.98 M$ and $M \ge p^{e/2 - 3}$ fail when $p^a < 10$ (e.g., $p = 3, a \in \{1, 2\}$ gives $M = 0$). Add "for $p^a \ge 10$ (in particular $a \ge 3$)."
4. **Corollary 2.8 hypotheses ([`paper.tex:516-517`](../../../papers/07-synthetic-expansions-v2/paper.tex#L516-L517)):** Explicitly require $\gcd(M', b) = 1$ (so $\ord_{M'} b$ is defined) and note that an empty maximum over $\ell \mid \Lambda$ is taken as $0$.
5. **Ambiguous definition of "relevant" and variable reuse in §7.6 ([`paper.tex:1473-1475`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1473-L1475), [`paper.tex:1481-1482`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1481-L1482)):** Line 1482 ("unless $\ell \le H + \lfloor e_r/s \rfloor$; call the other tuples *relevant*") reads awkwardly because "the other tuples" could parse as $\ell > H + \lfloor e_r/s \rfloor$. Rewrite as "call the tuples with $\ell \le H + \lfloor e_r/s \rfloor$ *relevant*." Also, $a_j$ is used for the box endpoint on line 1473 and immediately reused for the anchor numerator on line 1475.
6. **Domain boundary in Lemma 7.12 ([`paper.tex:1487`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1487)):** $M_r(u)$ is defined on $[1, p^d)$ on line 1415, so $(\xi - \delta_H, \xi)$ or $[\xi, \xi + \delta_H)$ can extend slightly outside $[1, p^d)$ if $\xi$ is within $\delta_H$ of $1$ or $p^d$. Either intersect with $[1, p^d)$ or state that the defining sum extends to all $u \in \R$.
7. **Two wording slips in Lemma 7.16 ([`paper.tex:1618-1621`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1618-L1621)):**
   - Lines 1618–1619: "Drop the condition $p \nmid m'$, so that $m'$ runs over consecutive integers; this at most multiplies counts by $p/(p-1)$." Dropping $p \nmid m'$ simply gives a valid upper bound on the collision count; the claim that it multiplies counts by at most $p/(p-1)$ is unnecessary and false for arbitrary subsets of integers.
   - Line 1621: "where $|f_B^{(q)}|$ changes sign" should be "where $f_B^{(q)}$ changes sign."
8. **Constant wording in Theorem 7.21 ([`paper.tex:1863`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1863)):** Writes `at most C_* N (\log L)^{-d/(d-1)}` for discarded failed runs, where $C_*$ is the constant from Theorem 7.18; because shell sampling introduces the factor $p^d/(p^d - 1)$ and the cell-boundary term adds $O(N^{r/d})$, write `O(N (\log L)^{-d/(d-1)})` instead.
9. **Implicit step in Theorem 9.3 Liouville proof ([`paper.tex:2172-2173`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2172-L2173)):** For $r = 1$ with $\Lambda_k$ squarefree, $\pi_k = A_b(\max_{\ell \mid \Lambda_k} \ell)$ can be exponentially smaller than $\Lambda_k$, so deriving $\log \Lambda_k = o(n_k)$ from $(\text{P}_1)$ relies on $\Lambda_k \mid b^{A_b(\ell_{\max})} - 1 \implies \log \Lambda_k < \pi_k \log b = o(n_k)$. Adding that one-line explanation (as done in Theorem 9.10, line 2359) makes the step transparent. Also note the empty-max convention when $\Lambda_k = 1$.
10. **Edge case $h = 0$ in Lemma 10.3 ([`paper.tex:2452-2454`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2452-L2454)):** The strict inequality `< 2\pi |h| \epsilon / (b-1)` fails for $h = 0$ ($0 < 0$). Restrict to nonzero integers $h$, or change `<` to `\le`.
11. **Minor precision polish in §1 and §10 ([`paper.tex:232-233`](../../../papers/07-synthetic-expansions-v2/paper.tex#L232-L233), [`paper.tex:2434`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2434), [`paper.tex:2630-2631`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2630-L2631)):**
    - Theorem G(iv) (L232–233): change "can only be shown to satisfy $D_N(X_H) \to 1$ if" to "is shown by the sparse-series transfer to satisfy $D_N(X_H) \to 1$ only if" (avoiding an unintended impossibility claim over all methods).
    - Proposition 10.1 (L2434): note that $3 \le L \le v_p(A) + 2$ is absorbed into $C_P$ before taking $M_r \bmod p^{L - v_p(A)}$.
    - §10.3 (L2630–2631): "is at least $(\log N)^{s/2}$" should be `$\gg_{\epsilon, p, s} (\log N)^{s/2}$`, since $p^{H(N)} \gg_\epsilon \sqrt{\log N}$ carries an implied constant.
12. **Editorial, macro, and bibliography hygiene:**
    - [`paper.tex:280`](../../../papers/07-synthetic-expansions-v2/paper.tex#L280): Uses unexplained shorthand `S08` ("and S08 uses the exponential schedule $c^k$"); replace with `and \cite{MiraPoly} uses...`.
    - [`paper.tex:16`](../../../papers/07-synthetic-expansions-v2/paper.tex#L16): Unused macro `\newcommand{\Mr}{M_r}`.
    - [`references.bib:396`](../../../papers/07-synthetic-expansions-v2/references.bib#L396) vs [`LEDGER.md:28,89`](../../../papers/07-synthetic-expansions-v2/LEDGER.md#L28): `Roth55` includes `doi = {10.1112/S0025579300000644}` despite `LEDGER.md` marking it `[U]` ("DOI not checked against Crossref in this pass") and adopting the policy "add DOIs only when verified" (applied to `Hooley71`). Either verify the DOI against Crossref or omit it until verified.
    - [`references.bib:216,225`](../../../papers/07-synthetic-expansions-v2/references.bib#L216) vs [`references.bib:262,278`](../../../papers/07-synthetic-expansions-v2/references.bib#L262): `PaperI` and `PaperIII` use `author = {{Christopher Anderson}}` (sorting under C in `plainurl`), whereas `CompanionH` and `PaperIv2` use `author = {Anderson, Christopher}` (sorting under A). Harmonize to `{Anderson, Christopher}`.

---

## Detailed Proof-by-Proof Verification Summary

### 1. Adapted Proofs (Explicit Focus)

- **Theorem 7.19 (`thm:higher`, lines 1725–1738) — deduced from Theorem 7.18:**
  - *Checked:* For $\deg P = 1$ and $d \ge 2$, $M_1(u) \equiv \lfloor u^{1/d} \rfloor \not\equiv 0 \pmod p$ on $[1, p^d)$, so $\{M_1 = 0\} = \emptyset$ and Lemma 7.11 applies. For $2 \le \deg P \le r < d$, Theorem 7.18 holds for all $r', d \ge 2$ and gives $|\{M_{\deg P} = 0\}| = 0$, whence Lemma 7.11 gives normality. Algebraic degree $< d$ and joint normality of $(C, \dots, C^{d-1})$ follow by taking $r = d - 1$ and Weyl's criterion.
  - *Unified anchor family in Lemma 7.16:* Verified that the box $h_j \in [a_j, 2a_j]$ with $a_j = \kappa H 6^{j-r}/4$ satisfies $h_1 \ge h_{\min}$, $h_2 \ge \max(2h_1 + 1, \lambda H)$ (since $a_2 = 6a_1 > 4a_1 + 1$ and $a_2 = 9\lambda H$), $h_j \ge 2(h_1 + \dots + h_{j-1}) + 1$ (since $4 \sum_{i<j} a_i < \frac45 a_j$), and $k \le \frac1{10}\kappa H < \kappa H$, giving $\gg_r (\kappa H)^{r-1}$ dominant vectors.
  - *Verdict:* **Mathematically sound** (subject to M4's minor fixes in Lemma 7.16 and Theorem 7.18, and M5's label consistency fix).

- **Lemma 10.5 (`lem:sparseint`, lines 2491–2506) & Theorem 10.6 (`thm:absorb`, lines 2508–2520) — self-contained $K_b$ absorption:**
  - *Checked every step and constant of Lemma 10.5:*
    - Absolute convergence holds from $a_m \le C_F m$; integrality of $a_m \ge 0$ gives $\{b^n F\} = \{T_n\}$ with $T_n = \sum_{m>n} a_m b^{n-m} \ge 0$.
    - Shifts $n < N$ with an insertion in $(n, n+L]$ number at most $L S(N + L - 1) \le L S(N + L)$.
    - Swapping summation for $m \in [L+1, N+L]$: $\sum_{n=0}^{m-L-1} b^{n-m} < b^{-L}/(b-1)$, contributing $\le C_F (N + L) b^{-L}/(b-1) \le 2 C_F N b^{-L}/(b-1)$ since $L \le N$.
    - Swapping summation for $m > N + L$ ($m = N + j, j > L$): $\sum_{n=0}^{N-1} b^{n-m} < b^{-j}/(b-1)$. Partial summation with $A(X) = \sum_{m \le X} a_m \le C_F X$ gives:
      $$\sum_{j>L} a_{N+j} b^{-j} \le \Bigl(1 - \frac1b\Bigr) C_F \sum_{j>L} (N+j) b^{-j} = C_F b^{-(L+1)}\Bigl(N + L + 1 + \frac1{b-1}\Bigr) \le \frac12 C_F (N + L + 2) b^{-L} \le 2 C_F N b^{-L},$$
      valid for all $b \ge 2$ and $1 \le L \le N$ (so the proof's $C_F (N + L + 2) b^{-L}/(b-1) \le 4 C_F N b^{-L}/(b-1)$ and combined constant $6$ hold with room to spare).
    - Markov's inequality plus Lemma 2.1 on $I = [0, \epsilon)$ (valid since $0 \le T_n < \epsilon < 1 \implies \{b^n F\} = T_n \in [0, \epsilon)$) yields the claimed bound.
  - *Checked Theorem 10.6:* Support count via Landau, mass bound $C_F = \pi p^{sH}/(4t)$ via Proposition 10.4, and $L \le 2\log_b(1/\rho) + sH \log_b p + O_{b,t}(1)$ give $1 - D_N(X_H) \le \rho(L + 2) \ll_{b,p,t} (\log\log N + sH)/\sqrt{\log N}$ uniformly in $H \ge 0$, with $L > N$ forcing $sH \gg N$ (trivial). Only Minor 2 (guarding $\rho \ge 1$ and $L \le 0$) needs tightening.
  - *Verdict:* **Lemma 10.5 is 100% sound**; Theorem 10.6 is sound with Minor 2.

### 2. Short Orbits (§2.1) and Higher-Degree Polynomial Normality (§§7.5–7.9)

- **Lemma 2.7 (`lem:uniformorbit`):** Verified LTE for all $G \equiv 1 \pmod p$, $G \ne 1$ ($p$ odd), strict complete-period bound $|S| < p^X$, stride Cauchy–Schwarz inequality, induction constants $C_n < 4 + 2\sqrt{5} < 9$, all three cases of stride exponent $k \in [0, \kappa]$, exact cancellation in $X_h = e_h - A = X_1 - j \ge \frac5{16} L_0 - \frac34 \ge 1$, and $W + n_\theta \kappa \ge L_0/\theta$. **Completely airtight.** (See Minor 3 for $p^a \ge 10$ in the sharpness remark.)
- **Corollary 2.8 (`cor:split`):** Verified $A(G) = a_0 + v_p(T_Q)$ (using $p \nmid t$), CRT splitting, $18 T (\tau/T)^\delta$, and $v_p(\ord_{\ell^k} b) = v_p(\ord_\ell b) \le v_p(\ell - 1)$. **Sound** (see Minor 4).
- **Lemma 2.9 (`lem:largestprime`):** Divisor-counting argument sound except for the prime-count slip `- 2` vs `- \omega(pb)` and the $\log\log\ord_\Lambda b$ guard (Minor 1).
- **Lemmas 7.10–7.15:** All verified line-by-line. In Lemma 7.15, checked $q 2^q > 4(2^q - 2)$ at $q = 4$ ($64 > 56$), all endpoint margins, and both slopes for $\alpha < 1/r$. **All sound.** (See Minor 5–6.)
- **Lemma 7.16 (`lem:avgiso`):** Checked centres count (including the universal lower bound $(1 - 1/p)M - 2$ for integers prime to $p$ in an interval of length $M$), $B = 0$ peeling + divisor bound ($p^{H - h_j + k_{j-1} + h_j/6} \le p^{(1-\lambda/3)H}$), small $|B|$ count, removed points, polynomiality and non-vanishing of $|f_B^{(q)}| = D$ in $X = x^d$ (RHS degree strictly exceeds LHS degree for both $q \le d$ and $q > d$), exact cancellation of $p^{\pm k/(2K_q-2)}$ in $E_1$, both exponents $E_1, E_2$, and regular/irregular competitor bounds. **Sound** subject to M4(1) (`\alpha = \min(1, v'/H)`) and Minor 7.
- **Proposition 7.17 (`prop:nouniform`):** Verified analytically that $R_H^{3/4} > 2^{3/4} \cdot 32 H^2$ yields $8((2\rho_H)^{1/4} 3^H)^3 < \frac12 (2\delta_H 3^{4H})$ and hence $8 a_{\rm hi}^3 \le 2 \delta_H 3^{4H}$ for all $H \ge 5$, and verified independently in Python with exact fractions that the net works for $H = 4, \dots, 14$ and that $R_{4000}^{126} < 3^{4000}$. Flagged M6(1) for the empty interval at $H = 4, 5$ and missing repository script coverage of $H = 4$.
- **Theorem 7.18 (`thm:smallball`):** Verified geometric level spacing $m(L) \gg \log L$, component count recursion $N_{j+1} \le N_j + p H^{r-1} p^H \le A H_{j+1}^A p^{H_{j+1}}(j+2)$, $c_1 = 1/(40 p^d A^3)$, and Bernoulli recursion $y_{j+1} \ge y_j + a c_1$. **Sound** subject to M4(2) (`8A` on line 1705).
- **Theorem 7.20 (`thm:several`):** Checked lexicographic target selection, sequential bounded anchor construction, rearrangement-inequality gap $G_0$ for all non-optimal assignments, free and bounded peeling, competitor counts, upper/lower lattice packing bounds, convergence and $L^1$ integrability of $f$, reverse Fatou, and Lebesgue-point contradiction (including the $n_* = 1$ edge case). **Brilliant and sound** subject to M1 (`J \ge \max(L, \lceil L/s_1 + L/d \rceil)`).
- **Theorem 7.21 (`thm:effective`) & Corollary 7.22 (`cor:flagship2`):** Checked all three constraints on $c_0$, freezing below $\sqrt{N}$, cell count $O(N^{r/d})$, coefficient bound $O(m^{(r-1)/d})$ and buffer absorption, exponent margins $\theta = \min(1, (d-r-1/2)/(rs))$, $e \ge \frac{rs}{4d}\log_p N - O(1)$, and numerical check $\delta = 2^{-19}$ at $(2,2,3)$. **Sound** (see Minor 8).

### 3. All-Prime Polynomial Normality and Irrationality Exponents (§9)

- **Lemma 9.1 (`lem:poledom`) & Theorem 9.2 (`thm:allprime`):** Checked ultrametric pole dominance, window decomposition $\mathcal W_{k,i}$, Kummer's bound $v_p(\binom{r}{l}) \le \log_p r$, exact rate constants $3(\log 2)^{1/3}$ and $r \log p / (\log 2)^{2/3}$, and Liouville bound. **Sound.**
- **Theorem 9.3 (`thm:protected`), Lemma 9.4 (`lem:Ax`), Corollary 9.5 (`cor:dense`):** Checked monotonicity of $p^{r e_k} \pi_k$, $\ord_{\Lambda_k^r} b \mid \Lambda_k^{r-1} A_b(\ell_{\max})$ for squarefree $\Lambda_k$, Selberg sieve singular series $m/\varphi(m)$ in Lemma 9.4, and all three dense schedules in Corollary 9.5. **Sound** (see Minor 9).
- **Theorem 9.7 (`thm:hybrid`):** Checked exact denominators, vanishing of auxiliary indices mod $p^L$ (relying on $p \nmid k_j$), Lemma 2.9 application for $A(G) = O(\log N/\log\log N)$, and the example $k_j = 2^{2^{j-1}}$ ($p$ odd). **Sound.**
- **Lemma 9.8 (`lem:truncation`) & Proposition 9.9 (`prop:ratioone`):** Checked separation inequality \eqref{eq:separation}, the $d = 2$ case where $\log \Lambda_K = o(K)$ makes the prefactor $o(\rho_k)$, and exact exponent $\psi(Q)$. Correction B is explicitly respected on line 2304. **Sound.**
- **Theorem 9.10 (`thm:geometric`):** Checked CRT bound $c_k \le \mathrm{rad}(b)$, strict lex/position equivalence under $r < \lambda$, candidate bound $(r+1)!$ on tied top ordered tuples, factorization of $A_r$ even when $p \mid A_r$, digit-run cutoffs, both explicit index sequences $k_j$, and $\mu(W_G) = \lambda$ for $\lambda \ge 3$. **Sound.**
- **Theorem 9.11 (`thm:stoneham`):** Checked $c_{k_j} \le p^{j - k_j} \mathrm{rad}(b) \le \mathrm{rad}(b)$, verbatim transfer of `PaperIv2` Lemmas 2.2–2.4 modulo $p^l$ for $k \ge k_{l-1} + l$, lower-degree domination, $A(G) = O(\log\log N)$, and $\mu(W_S) = p$. **Sound** (see M5(2) regarding `VERIFICATION.md` L99).
- **Remark 9.12 (`rem:quasipoly`):** Clearly marked as stated without proof and unused, with finiteness of $\mu$ and non-Liouville status explicitly left open. **Compliant.**

### 4. The Equality Boundary $d = r$ (§10)

- **Proposition 10.1 (`prop:depthtight`):** Valid for all $d \ge 2, r \ge 2$ since Lemma 7.10 and Theorem 7.18 require no sparsity (see Minor 11 for $L \le v_p(A) + 2$).
- **Lemmas 10.2–10.3:** Both verified (see Minor 10 for $h = 0$ in Lemma 10.3).
- **Proposition 10.4 (`prop:filtration`):** Mass bound $V_{r,d} Y^{r/d}$ verified; see **M2** for the spurious `b^n` in `{b^n R_n(Z_H)}`.
- **Lemma 10.5 & Theorem 10.6:** Verified in §1 above.
- **Lemma 10.7 (`lem:intmult`), Wall's converse, & Corollary 10.8 (`cor:retire`):** Both inequalities, the ergodic Wall converse, and the sharp-translation combination verified. **Sound.**
- **Theorem 10.9 (`thm:runs`):** Verified $p^{2k_H} \mathcal S^+ \subseteq \mathcal P_H \subseteq \mathcal S^+$, the gap reduction from $\mathcal S^+$ to $\mathcal S$ via $k^2 < k^2 + 1 < (k+1)^2$, Hooley moment Markov bound, Bambah–Chowla final-gap domination (and initial-gap triviality), and threshold $\epsilon < s / (2 \ln b)$. **Sound.**
- **Proposition 10.10 (`prop:fractional`):** Verified $v_p(i^2+j^2) = 2\min(v_p(i),v_p(j))$ for $p \equiv 3 \pmod 4$, automatic $p \nmid n$ for squarefree $n \in \mathcal S$, representation count $r_2(n)/4 = 2^{\omega_1(n)}$ prime to $p$, non-principality of $\chi_p$ and $\chi_p \chi_{-4}$, and Selberg–Delange asymptotics. Also independently verified the example $16810$ has exactly 6 ordered positive representations, all of 3-adic level 1. **Sound.**
- **§10.4 Cubic boundary & Remark 10.11:** Verified $V_{3,3}/6 \approx 0.118679$, conditional framing on density zero of sums of three cubes, and explicit openness of $\xi^3$ and $C(b,p,s,2)^2$ in Theorem G, §10.4, Remark 10.11, and Question 11.1. **Sound** (see Minor 11).

---

## v1.0 Backward Compatibility, LaTeX, Citations & Hygiene Audit

1. **v1.0 immutability & numbering:** Confirmed `papers/07-synthetic-expansions/` has zero modifications. Automated structural diff confirmed that Sections 2 (pre-2.1), 3–6, 7 (pre-7.5), and 8 match v1.0 verbatim except for updated Remarks 4.8 and 7.9 and added `\label` tags on subsections 7.1–7.4. Zero v1.0 labels were deleted or shifted. `CHANGES.md` accurately lists every new, upgraded, and unchanged result and every remaining release blocker.
2. **LaTeX & cross-references:** All 102 referenced labels are defined among 111 labels (zero undefined, zero duplicates); all `\cite` keys appear in `references.bib`, and every entry in `references.bib` is cited (zero missing, zero unused, zero duplicates). All 33 Lean links (`\lean`, `\leanP`, `\leanR`) resolve to the exact declaration and line number at commits `e4809cf`, `c2c9da6`, and `347ec3f` (`HEAD` matches `347ec3f`).
3. **Internal process language:** Zero mentions of "Phase 20/21/22", "Track", "subagent", model names, or registry IDs (`GF-*`, `SY-*`, `OP-*`) appear in the mathematical prose of `paper.tex` (the only `phase*` strings are literal filenames of cited Lean modules and repository scripts in §12). The only process-language leaks are `S08` on line 280 (Minor 12) and the internal review-cycle phrasing on lines 2750–2753 (M6(3)).
4. **Bibliography hygiene:** `references.bib` is notably transparent (marking unverified secondary entries with `note = {Unverified: ...}` and `Manai25` with `Only the abstract was read`). Only `Roth55` (DOI included despite `[U]` status in `LEDGER.md`) and author-brace formatting (`PaperI`/`PaperIII` vs `CompanionH`/`PaperIv2`) need cleanup (Minor 12).

---

## Structural Assessment: Length (47 pp. vs 24 pp.) and Companion-Paper Split Question

At 47 pages (1.96× v1.0's 24 pages), the draft is long for an update to an already-published preprint, so the owner should make an explicit scope decision before release:

- **Mathematical cohesion:** The manuscript actually weaves two related but distinguishable research arcs around the shared engine of Lemma 2.7 (`lem:uniformorbit`):
  1. **The $C(b,p,s,d)$ arc (§§1–8, §10; ~39 pages):** Valuation-weighted expansions on polynomial schedules—the switch (Theorem A), complete-period rates (Theorem B), prescribed discrepancy/limit sets (Theorem C), polynomial images for $r < d$ with rates (Theorem D), the v1.0 infinite sum (Theorem E), and the exact sharpness/obstruction theory at $d = r$ (Theorem G / §10). **Section 10 belongs tightly with Section 7**: it directly reuses Lemma 7.10 and Theorem 7.18 and directly explains v1.0 Question 1b ($\xi^3$ and $C(b,p,s,2)^2$).
  2. **The all-prime + irrationality-exponent arc (§9; ~8 pages):** Protected-pole Taylor dominance (`ProtectedPole.lean`), Selberg sieve lcm bounds, all-prime schedules across super-exponential/polynomial/geometric/Stoneham growth regimes, Roth's theorem, and exact irrationality exponents $\mu = \lambda$ and $\mu = p$ (importing Paper I v2.0 Lemmas 2.2–2.4).
- **Recommendation to the owner:**
  - **Option 1 (Keep unified as a 47-page Paper VII v2.0):** Completely defensible mathematically—47 pages is standard for a full-length analytic number theory paper, and keeping §2.1, §7.9, §8, and §9 under one roof avoids repeating notation and splitting the `ProtectedPole` / `PowerSumPeeling` formalizations across two preprints.
  - **Option 2 (Split before release):** If the owner prefers shorter (~30–38 page) papers, **split §9 alone** (not §9–§10 together) into a companion Paper XII (*All-Prime Polynomial Normality and Irrationality Exponents*). Splitting §10 away from §7 would artificially sever the $d = r$ boundary analysis from the $r < d$ theorem it directly complements.

---

## Pre-Release Revision Checklist

Before finalizing Paper VII v2.0 for release, the author should:

1. Fix **M1** (`paper.tex` L1755: `J \ge \max(L, \lceil L/s_1 + L/d \rceil)`).
2. Fix **M2** (`paper.tex` L2479, L2603: remove spurious `b^n` before `R_n`).
3. Fix **M3** (`paper.tex` L42–45: qualify degree bounds in Abstract for polynomial and geometric schedules).
4. Fix **M4** (`paper.tex` L1624: `\alpha = \min(1, v'/H)`; L1705: `8A` in place of `4A`).
5. Fix **M5** (`paper.tex` L2721 and L321/L1661 label consistency; `VERIFICATION.md` L99 change `(Lean-supported there)` to `(Paper proofs there)`).
6. Fix **M6** (restrict Proposition 7.17 to $H \ge 6$ or commit $H = 4$ into `scripts/phase21_nonlinear.py`; commit the two untracked Phase 22 scripts; clean internal workflow phrasing in §13 L2750–2753).
7. Apply Minor fixes 1–12 and resolve the owner's decision on keeping v2.0 unified vs. splitting §9 into a companion Paper XII, plus the standard release steps already listed in `CHANGES.md` and `LEDGER.md`.

---

## Post-Repair Verification

- **Date:** 26 November 2026.
- **Referee:** Gemini 4 Neon (post-repair cross-provider verification).
- **Final Verdict:** **ACCEPT**

> **Disclaimer.** Cross-model review is not independent human peer review. This post-repair verification confirms that the AI-written revisions accurately address the findings of the prior AI audit; no human specialist has read the manuscript or its proofs.

### Verification of Major Repairs (M1–M6)

- **M1 — VERIFIED** ([`paper.tex:1762-1767`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1762-L1767)): Theorem 7.20 (*Reduction*) now sets the freezing threshold to $J \ge \max(L, \lceil L/s_1 + L/d \rceil)$ and explicitly explains that monomials outside $T$ carry $p^{(S^* - s \cdot \nu)J}$ with $S^* - s \cdot \nu \ge 1$, which vanishes modulo $p^L$ because $J \ge L$.
- **M2 — VERIFIED** ([`paper.tex:2489`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2489), [`paper.tex:2614`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2614)): The spurious factor $b^n$ is removed in both Proposition 10.4 (`\fr{R_n(Z_H)}=\fr{p^{sH}R_n(C^r)}`) and §10.3 (`\fr{R_n(Z_H)}`), with zero remaining occurrences of `b^n R_n` in §10.
- **M3 — VERIFIED** ([`paper.tex:41-45`](../../../papers/07-synthetic-expansions-v2/paper.tex#L41-L45)): The Abstract now states the exact degree scopes matching Theorem F: Liouville example (all degrees), polynomial schedules $tk^d$ (degree less than $d$), finite irrationality exponent $\lambda$ (degree $r < \lambda$, for primes $p > (r+1)!$), and exponent $p$ (all degrees).
- **M4 — VERIFIED** ([`paper.tex:1626-1627`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1626-L1627), [`paper.tex:1709-1712`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1709-L1712)): Lemma 7.16 now uses $\alpha = \min(1, v'/H)$ and $\beta = \min(1, H'/H)$ (checking $\beta/r \le \alpha \le \beta \le 1$ and noting $0 \le v' - \alpha H \le \lfloor e_r/s \rfloor$ shifts exponents by $O(1)$). Theorem 7.18 now bounds each of the two error terms by $p^{(1-\mu/2)H} \le x H^{r-1} p^H/(8A)$, yielding $(1 - \frac18 - \frac14 - \frac18) A^{-1} = \frac{1}{2A}$.
- **M5 — VERIFIED** ([`paper.tex:318-322`](../../../papers/07-synthetic-expansions-v2/paper.tex#L318-L322), [`paper.tex:1664`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1664), [`paper.tex:1691`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1691), [`paper.tex:2731-2734`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2731-L2734), [`VERIFICATION.md:82-83,99`](../../../papers/07-synthetic-expansions-v2/VERIFICATION.md#L82-L99), [`LEDGER.md:17`](../../../papers/07-synthetic-expansions-v2/LEDGER.md#L17)): §1 defines *finite certificate* as an additional label alongside the four primary labels; Proposition 7.17 carries `Paper proof; finite certificate`; Theorem 7.18 carries `Lean-supported paper proof` (matching Lemmas 7.12, 7.16 and Theorem 7.19); §12 cleanly separates `Paper proof` statements (7.1, 7.2, 7.21, 7.22) from `Lean-supported paper proof` statements (7.18–7.20); and `VERIFICATION.md`/`LEDGER.md` accurately record Paper I v2.0 Lemmas 2.2–2.4 as `Paper proof` there.
- **M6 — VERIFIED** ([`paper.tex:1666-1681`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1666-L1681), [`paper.tex:2747-2761`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2747-L2761), [`VERIFICATION.md:114-116,142`](../../../papers/07-synthetic-expansions-v2/VERIFICATION.md#L114-L116), [`CHANGES.md:61,74,91`](../../../papers/07-synthetic-expansions-v2/CHANGES.md#L61)): Proposition 7.17 is now stated for $H \ge 6$ (where $\rho_H > 2\delta_H$ makes the interval nonempty and matches `scripts/phase21_nonlinear.py`), with an explicit note on $H = 4, 5$; §12 no longer cites an uncommitted scratch script; §13 is completely cleaned of internal workflow phrasing while keeping the explicit non-peer-review disclaimer; and `VERIFICATION.md`/`CHANGES.md` accurately record `GF-24`, `GF-25` (while declining `GF-25`'s unsupported priority phrasing), the untracked `Phase22Cores.lean` and two Phase 22 scripts as pre-release commit items, and the §9 companion-paper split option for the owner.

### Verification of Minor Repairs (1–12)

All 12 Minor items have been checked and verified:

1. **Lemma 2.9** ([`paper.tex:537,544`](../../../papers/07-synthetic-expansions-v2/paper.tex#L537-L544)): uses $\pi(x) - \omega(pb) - x^{2/3}\log_2 b$ with $\omega(pb) \le 1 + \log_2 b$, and $\log(\ord_\Lambda b + 3)/\log\log(\ord_\Lambda b + 3)$. **Verified.**
2. **Theorem 10.6** ([`paper.tex:2528-2530`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2528-L2530)): sets $L = \max(1, \lceil \log_b(6 C_F/((b-1)\rho^2)) \rceil)$ and observes cleanly that if $\rho \ge 1$ or $L > N$ then $\rho(L+2) > 1 \ge 1 - D_N(X_H)$ (valid because $L \ge 1$ and $\rho = (1+S(2N))/N \ge 1/N$), so Lemma 10.5 is invoked only when $\epsilon \in (0,1)$ and $1 \le L \le N$. **Verified.**
3. **Lemma 2.7 sharpness remark** ([`paper.tex:506`](../../../papers/07-synthetic-expansions-v2/paper.tex#L506)): restricted to $p^a \ge 10$. **Verified.**
4. **Corollary 2.8** ([`paper.tex:517`](../../../papers/07-synthetic-expansions-v2/paper.tex#L517)): requires $\gcd(M', pb) = 1$ and states empty maximum $= 0$. **Verified.**
5. **§7.6** ([`paper.tex:1475,1484`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1475-L1484)): box endpoints renamed $\beta_j$; "relevant" defined directly. **Verified.**
6. **§7.5 / Lemma 7.12** ([`paper.tex:1421-1424`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1421-L1424)): defining sum of $M_r(u)$ extended to all $u \in \R$, removing boundary effects near $1$ and $p^d$. **Verified.**
7. **Lemma 7.16** ([`paper.tex:1621,1623`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1621-L1624)): drops the invalid $p/(p-1)$ factor and fixes `where f_B^{(q)} changes sign`. **Verified.** (Cosmetic leftover noted below.)
8. **Theorem 7.21** ([`paper.tex:1870`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1870)): `O(N(\log L)^{-d/(d-1)})` shifts. **Verified.**
9. **Theorem 9.3** ([`paper.tex:2179-2182`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2179-L2182)): explicitly proves $\log \Lambda_k < \pi_k \log b = o(n_k)$ in the squarefree case via $\Lambda_k \mid b^{\ord_{\Lambda_k} b} - 1$, with the empty-maximum convention. **Verified.**
10. **Lemma 10.3** ([`paper.tex:2462`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2462)): stated for every nonzero integer $h$. **Verified.**
11. **Theorem G(iv), Proposition 10.1, §10.3** ([`paper.tex:232-233`](../../../papers/07-synthetic-expansions-v2/paper.tex#L232-L233), [`paper.tex:2442-2444`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2442-L2444), [`paper.tex:2642`](../../../papers/07-synthetic-expansions-v2/paper.tex#L2642)): sparse-series transfer attribution, $3 \le L \le v_p(A)+2$ absorption, and $\gg_{\epsilon,p,s}(\log N)^{s/2}$ all applied cleanly. **Verified.**
12. **Prose, macros, and bibliography** ([`paper.tex:16,280`](../../../papers/07-synthetic-expansions-v2/paper.tex#L280), [`references.bib:216,225,388-396`](../../../papers/07-synthetic-expansions-v2/references.bib#L388-L396)): `S08` replaced by `\cite{MiraPoly}`, unused `\Mr` macro removed, unverified `Roth55` DOI removed, and `PaperI`/`PaperIII` author fields harmonized to `Anderson, Christopher`. **Verified.**

### Integrity Check & Non-Blocking Cosmetic Nits

- Automated integrity checks rerun on the revised draft confirm zero missing/unused bibliography keys, zero undefined/duplicate labels, zero shifted/removed v1.0 labels, zero modifications to `papers/07-synthetic-expansions/`, and zero internal process language in `paper.tex`.
- Three purely cosmetic, non-blocking nits remain for optional cleanup during final release packaging:
  1. [`paper.tex:1624`](../../../papers/07-synthetic-expansions-v2/paper.tex#L1624): `on which |f_B^{(q)}| has constant sign and ratio at most 2` (the bars around `f_B^{(q)}` can be dropped for "constant sign", matching the fix on L1623).
  2. [`LEDGER.md:37,60,73`](../../../papers/07-synthetic-expansions-v2/LEDGER.md#L37): three lingering clauses still state that the Phase 22 results "have no registry entry yet", now superseded by `GF-24`/`GF-25` on lines 67 and 93 of the same file.
  3. [`CHANGES.md:30`](../../../papers/07-synthetic-expansions-v2/CHANGES.md#L30): the statement-correspondence table row for §13 still summarizes the pre-revision wording (whereas line 74 accurately reflects the cleaned §13).

### Conclusion

All 6 Major findings and all 12 Minor findings have been satisfactorily resolved. The Paper VII v2.0 candidate draft is **ACCEPTED** from a cross-provider mathematical and structural referee standpoint, subject only to the owner's release steps (committing the untracked Phase 22 scripts and `Phase22Cores.lean`, running the final portal/packaging steps, and deciding whether to keep the unified 48-page v2.0 or split §9 into a companion Paper XII).
