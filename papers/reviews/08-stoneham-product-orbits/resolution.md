# Resolution of Referee Report 1 on Manuscript D (*Exceptional Orbits and Discrepancy of Stoneham Products*, v1.0)

- **Reviser model:** Gemini 4 Neon (Google DeepMind)
- **Date:** 25 November 2026
- **Commit reviewed:** `a7ad257` (as named in `review-1.md`; revision starts from `9a64d5b3eb2a1f2a9545c8a8fc20c4bd4622b718` on branch `publication/wave-2` / worktree branch `t3/revise-stoneham-referee`)
- **Status:** **AI model review and revision; not independent human peer review.**

The referee report is `papers/reviews/08-stoneham-product-orbits/review-1.md` (Claude Sonnet 5.5; verdict: *mathematically sound; accept after revision*; counts: 0 critical, 2 major, 14 minor, 5 editorial). Line numbers below refer to the revised `papers/08-stoneham-product-orbits/paper.tex` (rebuilt PDF: 18 pages, no undefined references or citations). Adding Lemma 2.2 does not shift later Section 2 numbers; extracting Lemma 3.2 (Finding 20) renumbers former Proposition 3.2 to Proposition 3.3 and former Theorem 3.3 to Theorem 3.4, with all companion files (`VERIFICATION.md`, `LEDGER.md`, `submission/*`) synchronized accordingly. No Lean files, `papers/common/`, `papers/0[1-5]-*`, the registry, the README, or other manuscripts were modified.

| Finding | Severity | Disposition |
| --- | --- | --- |
| 1. Scope and evidence conflation in abstract and submission texts | Major | Accepted |
| 2. Uniform-in-$N$ consequence of Theorem 2.1 unstated | Major | Accepted |
| 3. Ridout's theorem locator unverified | Minor | Accepted |
| 4. Thin `Lean-supported paper proof` labels | Minor | Partly accepted |
| 5. Proposition 3.2 (now 3.3) vacuous $m=a-1$ case | Minor | Accepted |
| 6. Proposition 4.1 compressed last sentence and sharpness wording | Minor | Accepted |
| 7. Section 7 `R_n` not fully defined | Minor | Accepted |
| 8. Unlabelled assertions at end of Section 7 | Minor | Accepted |
| 9. Notation clashes ($\lambda, K, c, D, A, d$) | Minor | Accepted |
| 10. Logarithmic equidistribution used before definition | Minor | Accepted |
| 11. Korobov and Bourgain antecedents for short-orbit estimate | Minor | Accepted |
| 12. Bibliography attributions and citation detail (a–f) | Minor | Accepted |
| 13. Generic search records in `LEDGER.md` | Minor | Accepted |
| 14. Phase 19 consistency and open-problem obstruction | Minor | Accepted |
| 15. Abstract "exact bound 4/11" / `metadata.toml` "sharp bound 4/11" | Minor | Accepted |
| 16. Abstract omits coprimality hypothesis | Minor | Accepted |
| 17. Repository process language in Section 6 | Editorial | Accepted |
| 18. Undefined coined terms | Editorial | Accepted |
| 19. Organization (Section 1 roadmap, Section 6 opening) | Editorial | Accepted |
| 20. Density in Sections 2–3 (Lemma 3.2, Claim 1, paragraph breaks) | Editorial | Accepted |
| 21. Submission inquiry templates pose multiple questions | Editorial | Accepted |
| Paper III audit Phase 19 update (`papers/wave2-audits/paper-III-audit.md`) | Audit note | Accepted |

---

## Major findings

### 1. Scope and evidence conflation in the abstract and all submission texts — Accepted
- **Changes:** Narrowed the scope of the unconditional sub-quarter discrepancy bounds to explicit families (specifically $(\alpha^2-2\alpha+C)/3$ for odd $b\equiv2\pmod3$, $C\not\equiv1\pmod3$, and $(\alpha^2-2\alpha)/9$ for $b=5$) and separated the kernel-verified plateau-cycle law and resonant-radix classification from the Lean-supported paper proofs and finite cycle enumeration.
- **Locations:** `paper.tex:12–14`, `metadata.toml:8`, `submission/abstract.txt` (231 words, limit 250), `submission/alphaxiv.md` (`## Abstract` and `## Verification scope`), `submission/summary.md`, `submission/announcement.md` (forum post; X post unchanged at 260 chars, limit 280), `submission/reviewer-packet.md` (§4).

### 2. Uniform-in-$N$ consequence of Theorem 2.1 used but never stated — Accepted
- **Changes:** Added **Lemma 2.2** (`\label{lem:uniform}`, `\evidence{Lean-supported paper proof}`), stating and proving that for every $\varepsilon>0$ there exist $M,N_0\ge1$ with $D_N(x)\le\varepsilon+N^{-1}\#\{0\le n<N:\den(R_n)\le M\}$ for all $N\ge N_0$ from the uniform-in-$N$ block estimate of Theorem 2.1 and `CircleDiscrepancy.disc_sub_tendsto`. Invoked Lemma 2.2 explicitly in Theorem 3.4(ii) and Corollary 4.3.
- **Locations:** `paper.tex:109–117` (Lemma 2.2), `paper.tex:244` (Theorem 3.4(ii)), `paper.tex:310–313` (Corollary 4.3), `paper.tex:456` (Formal verification), `VERIFICATION.md`, `LEDGER.md`, `submission/alphaxiv.md`, `submission/reviewer-packet.md`.

---

## Minor findings

### 3. Ridout's theorem citation not pinned to a verifiable statement — Accepted
- **Changes:** Stated the exact $S$-integer-denominator corollary used ($|\alpha-u/t|<t^{-1-\epsilon}$ has only finitely many solutions with $t$ supported on a finite prime set $S$), cited `\cite{ridout57,ridout}` without the unverified `[Theorem, p. 125]` and `(\mu=1,\nu=0)` parametrization, and recorded that the page-level locator is unverified in primary text.
- **Locations:** `paper.tex:366`, `VERIFICATION.md` (Theorem 6.3 row and External analytic dependencies), `LEDGER.md` (unverified-locators list and Theorems 6.1/6.3), `submission/reviewer-packet.md` (§4).

### 4. `Lean-supported paper proof` labels thin for Theorem A, Proposition 3.1, Theorem 3.3 (now 3.4), and Corollary 4.3 — Partly accepted
- **Changes:** Kept the exact contract label `\evidence{Lean-supported paper proof}` per `papers/WAVE2-CONTRACT.md` (rather than introducing a non-contract label for Theorem A), and added explicit "Formalized in Lean: … Not formalized: …" / "Inherited formalized steps: …" splits directly in the text for all four results, including explicit links to the inherited Lean declarations in Corollary 4.3.
- **Locations:** `paper.tex:47` (Theorem A), `paper.tex:148` (Proposition 3.1), `paper.tex:217` (Theorem 3.4), `paper.tex:310` (Corollary 4.3), `VERIFICATION.md`.

### 5. Proposition 3.2 (now 3.3): vacuous case and confusing sentence — Accepted
- **Changes:** Removed the vacuous $m=a-1$ paragraph and stated explicitly that $u\in\{2,4\}$ with $m=a+uz<a$ forces $m\le a-u\le a-2$ (so $m=a-1$ cannot occur, and $m\ge1$ automatically implies $a\ge3$).
- **Locations:** `paper.tex:195`.

### 6. Proposition 4.1, last sentence: compressed sketch and sharpness wording — Accepted
- **Changes:** Defined the *$(h,k)$-joint-depth failure set* before Proposition 4.1, expanded the final paragraph of the proof with the explicit congruence/irrational-rotation step showing simultaneous realization of $K\equiv K_0\bmod M_K$, $L\equiv L_0\bmod M_L$ and $r=q^L/p^K\to r_*$, and clarified in Section 1 that $4/11$ is sharp for the bounded-denominator density method rather than known to be sharp for $D^+(x)$ itself.
- **Locations:** `paper.tex:47` (Section 1), `paper.tex:262, 268, 275–279` (Section 4).

### 7. Section 7: `R_n` not fully defined — Accepted
- **Changes:** Displayed the explicit formula for $R_n$ including the coefficients $A, E, C$.
- **Locations:** `paper.tex:371–374`.

### 8. Unlabelled assertions at end of Section 7 — Accepted
- **Changes:** Dropped the unlabelled function-field transcendence assertion over $\C(\lambda, e^{\lambda/2^m})$ (which is not proved or used in the manuscript) and placed the general $D=2^e D_1$ observation inside an explicit `Remark` stating that it is recorded without proof here.
- **Locations:** `paper.tex:449–453`.

### 9. Notation clashes — Accepted
- **Changes:** Renamed the $2$-adic limit in Section 7 from $\lambda$ to $\lambda_2$ (preserving $\lambda$ exclusively for Lebesgue measure); renamed the threshold index $K$ in Theorem 2.1 to $n_0$; wrote rational $B$-cycles as $\mathfrak c$ (with $m_{\mathfrak c}, \nu_{\mathfrak c}, w_{\mathfrak c,N}, w_{\mathfrak c}$); renamed Section 4 shape-grid dimensions $(A,D)$ to $(a_{\max}, d_{\max})$; renamed $A=q^u$ and $c$ in Proposition 3.1 to $\rho=q^u$ and $c_0$; renamed $A_0, D_0$ in Proposition 4.1 to $M_K, M_L$; renamed exponent $d$ in Theorem 2.1 to $r$; and noted at the start of Section 6 that integer parameters $c, d$ are unrelated to the shape coordinate $d$.
- **Locations:** `paper.tex` throughout (Sections 2–7), `VERIFICATION.md`, `LEDGER.md`, `submission/reviewer-packet.md`.

### 10. Logarithmic equidistribution used before defined — Accepted
- **Changes:** Defined logarithmic equidistribution (with harmonic weights $1/(n+1)$ in the sense of Tsuji) in Section 1 immediately before Theorem A, and referred back to Section 1 in Theorem 3.4(iii).
- **Locations:** `paper.tex:26–30`, `paper.tex:253`.

### 11. Antecedents for the short-orbit estimate — Accepted
- **Changes:** Added a sentence in the proof of Theorem 2.1 citing Korobov (1970, 1972) and Bourgain (2005, 2008), explaining why their general-modulus orbit-length and divisor-order hypotheses are unavailable for arbitrary $\{p,q\}$-smooth prefix denominators with $m\le T^r$, making Vandehey's fixed-prime-support bound and `SmoothOrbit` the relevant input. Added all four bibliographic entries (with DOIs) to `references.bib` and documented them in `LEDGER.md`, `VERIFICATION.md`, and `submission/reviewer-packet.md`.
- **Locations:** `paper.tex:73`, `references.bib:57–95`, `LEDGER.md` (Theorem 2.1 & Lemma 2.2), `VERIFICATION.md`, `submission/reviewer-packet.md`.

### 12. Bibliography: attributions and citation detail — Accepted
- **Changes:** (a) Stated Stoneham's (1973) primitive-root modulo $c^2$ hypotheses in `paper.tex:49` and flagged primary-text confirmation in `LEDGER.md` (and removed the unconfirmed `Corollary 4.9(i), p. 536` locator from `paper.tex:49`, flagging it in `LEDGER.md`); (b) re-attributed Kamae (1973) to normality-preserving subsequence selections and Rauzy (1976) / Weiss (2000) to additive preservers (`paper.tex:49`, `LEDGER.md`); (c) softened Mahler/Robert in `paper.tex:165` to classical context (`cf.`) since convergence is proved directly from $v_p(\nabla^k g(0))\ge k+1$, and dropped unconfirmed page locators in `VERIFICATION.md`; (d) replaced unverified Bergelson–Downarowicz `Thm. 8.1` / `Cor. 8.14` in `LEDGER.md` with verified `§§8.4–8.5` and an explicit unverified-theorem-number note; (e) marked Wall (1949) as `unverified` in `references.bib:168` and `LEDGER.md`; (f) retained `twosum` and `mira` as pinned repository entries.
- **Locations:** `paper.tex:49, 165`, `references.bib:168`, `VERIFICATION.md`, `LEDGER.md`.

### 13. `LEDGER.md` search record is generic — Accepted
- **Changes:** Replaced the generic search lines in `LEDGER.md` with dated (`25 November 2026`), theorem-specific query strings, databases, reference trails, negative results, and a top-level summary of unverified bibliographic locators.
- **Locations:** `LEDGER.md` (all five entries and header list).

### 14. Phase 19 consistency and open-problem obstruction — Accepted
- **Changes:** Added plain-language sentences (with no phase vocabulary) to the Remark at the end of Section 5 and the closing paragraph of Section 7 explaining why real-parameter curvature/second-moment arguments stop at coupled integer shell indices $(K,L)$ and at the discrete, piecewise-constant dyadic leading mass. Added Phase 19 cross-references pinned to `c2c9da683666b3b9368e5d4b5cb858caccf528f5` (`notes/phase19/nonlinear.md`) in `LEDGER.md` under Theorem A and Theorem 7.1, and noted `notes/phase19/nonlinear.md` in `VERIFICATION.md`. Kept `lean_commit = e4809cf561573aef588e6ffc491a35cdb79fd9ec` unchanged since no Phase 19 Lean declaration is used.
- **Locations:** `paper.tex:341, 453`, `LEDGER.md`, `VERIFICATION.md`.

### 15. Abstract "exact bound 4/11"; `metadata.toml` "sharp bound 4/11" — Accepted
- **Changes:** Replaced both with "the threshold $4/11$" (and aligned `submission/abstract.txt`, `submission/alphaxiv.md`, `submission/announcement.md`).
- **Locations:** `paper.tex:13`, `metadata.toml:8`, `submission/abstract.txt`, `submission/alphaxiv.md`, `submission/announcement.md`.

### 16. Abstract omits standing coprimality hypothesis — Accepted
- **Changes:** Added "coprime to the radix $B$" to the opening sentence of the abstract in both `paper.tex` and `metadata.toml`.
- **Locations:** `paper.tex:13`, `metadata.toml:8`.

---

## Editorial findings

### 17. Repository process language in the body — Accepted
- **Changes:** Replaced the process sentence at the start of Section 6 with a bibliographic reference (`\cite{paper1v1}`) to the earlier companion preprint (`manuscripts-v1.1.0`), stating that the results are proved here for completeness.
- **Locations:** `paper.tex:345`, `references.bib:241–246`.

### 18. Undefined coined terms — Accepted
- **Changes:** Paraphrased "zero-slack barrier" cleanly as "barrier $4/11$ (with zero additive slack)" (`paper.tex:47`), and explicitly defined *bulk shapes* (`paper.tex:242`), *primary shape* / *primary $(1,1)$ plateaus* (`paper.tex:262`), *$(h,k)$-joint-depth failure set* (`paper.tex:262`), and *lifted loss residues* (`paper.tex:283`) on first use.
- **Locations:** `paper.tex:47, 242, 262, 283`.

### 19. Organization — Accepted
- **Changes:** Added a concise section-by-section roadmap paragraph at the end of Section 1 (`paper.tex:51`) and rewrote the opening sentence of Section 6 (`paper.tex:345`) to eliminate chronological-draft phrasing while explaining how the elementary kernel-verified $43/45$ bound complements Sections 3–5.
- **Locations:** `paper.tex:51, 345`.

### 20. Density in Sections 2–3 — Accepted
- **Changes:** Split the weak-convergence and direct discrepancy-transfer arguments in Theorem 2.1 into separate paragraphs (`paper.tex:100–102`); extracted the Teichmüller and backward analytic continuation computation as **Lemma 3.2** (`\label{lem:teich}`, `paper.tex:176–187`, renumbering former Proposition 3.2 to Proposition 3.3 and Theorem 3.3 to Theorem 3.4); and displayed the two-case monotonicity argument in Theorem 3.4(ii) as **Claim 1** (`paper.tex:228–235`). Updated numbering across `VERIFICATION.md`, `LEDGER.md`, `submission/alphaxiv.md`, `submission/reviewer-inquiry.md`, and `submission/reviewer-packet.md`.
- **Locations:** `paper.tex:100–102, 176–187, 228–235` and companion files.

### 21. Submission templates (`submission/reviewer-inquiry.md`) — Accepted
- **Changes:** Rewrote both inquiry templates so each names one concrete result, cites one closest prior work, and poses one specific question: Template 1 asks about the uniform-arc block argument and circle-enlargement transfer in Theorem 2.1 and Lemma 2.2 (referencing Vandehey 2019); Template 2 asks about $p$-adic approximation measures for the implicit Mahler-series roots $\zeta_{p,a,d}$ of Proposition 3.1 / Theorem 3.4 (referencing Bugeaud–Laurent 1996 and Bugeaud 2012, removing the unrelated dyadic $\kappa_0$ question).
- **Locations:** `submission/reviewer-inquiry.md`.

---

## Paper III audit update (`papers/wave2-audits/paper-III-audit.md`) — Accepted
- **Changes:** Added one sentence to Section 3 noting that the completed Phase 19 research (merged at `c2c9da683666b3b9368e5d4b5cb858caccf528f5`) does not change the recommendation to retain Paper III v1.1 unchanged: its translation, dilation, and addition-spectrum results neither conflict with Paper III's `CR`/`DS` theorems nor affect item 2 (which rests on Paper III's uniformity and concentration theorems rather than the retracted prime-5 valuation paragraph of the Phase 18 review).
- **Locations:** `papers/wave2-audits/paper-III-audit.md:22`.

---

## Verification of this revision

- **LaTeX build:** `wsl -d Ubuntu -- bash papers/wsl-build.sh 08-stoneham-product-orbits` succeeded (exit code 0, 18 pages, no undefined references or citations).
- **Lean pins:** All 32 unique `NormalityChecker/*.lean#L*` anchors across `paper.tex` and `VERIFICATION.md` were checked against `git show e4809cf:NormalityChecker/<File>.lean`; every anchor lands on the stated declaration.
- **Submission constraints:** `submission/abstract.txt` is 231 words (limit 250); the X post in `submission/announcement.md` is 260 characters (limit 280); `metadata.toml` parses cleanly with all 14 required keys.

---

## Questions reserved for a human specialist

1. **Primary-text bibliographic locators:** Verify the exact theorem number, page, and $(\mu,\nu)$ parametrization in Ridout (1957, *Mathematika* 4, 125–131) and Ridout (1958, *Mathematika* 5, 40–48); confirm the exact primitive-root modulo $c^2$ hypotheses in Stoneham (1973), the corollary/page locator in Bailey–Crandall (2002), Wall's 1949 Berkeley thesis text, the exact multiplication-counterexample theorem numbers in Bergelson–Downarowicz (2025, `arXiv:2506.12929` §§8.4–8.5), and the primary-text theorem statements in Korobov (1970, 1972) and Bourgain (2005, 2008).
2. **Mixture law and uniform-in-$N$ transfer (Theorem 2.1 & Lemma 2.2):** Confirm the $O(M/\sqrt N)$ incomplete-cycle error summation across $\lceil N/\lfloor\sqrt N\rfloor\rceil$ blocks and the circle-enlargement transfer across atomic endpoints.
3. **Local $p$-adic interpolation and Eisenstein step (Proposition 3.1, Lemma 3.2, Proposition 3.3):** Audit the $v_p(\nabla^k g(0))\ge k+1$ expansion and Chu–Vandermonde increment congruence (including $p\mid u$), the empty-fibre boundary cases $a=L$ and $d=K$, and the backward analytic continuation / compatible $q^h$th-root bookkeeping in Lemma 3.2.
4. **Threshold equivalence and certificate assembly (Corollary 4.3 & Section 5):** Check the finite-grid non-coincidence assembly in Corollary 4.3, the endpoint grid-point counts $\lceil mt\rceil-1<mt$ and $m-\lceil mt\rceil\le m(1-t)$, and the dominance step $w_0\ge\frac{11}{4}w'\implies\Delta(\sigma(w))=w_0$.
5. **Ridout application with shared prime factors (Theorem 6.3):** Confirm that the isolated-insertion gap $\eta P$ and denominator bound $t\le B^s s^2$ satisfy all hypotheses of Ridout's theorem when $\gcd(c,d)>1$.
6. **Dyadic and modulo-$3$/modulo-$9$ cycle bounds (Proposition 7.3 & Corollary 7.4):** Audit the written two-grid discrepancy bounds and advise whether any $p$-adic transcendence or Diophantine-approximation method can bound $v_p(m-\zeta_{p,a,d})$ or $v_2(k-\kappa_0(b))$ at fixed integer radices.
7. **Historical priority:** Confirm through MathSciNet / zbMATH Open whether any prior work studies products of Stoneham or Korobov series on distinct prime axes, countable-cycle mixture discrepancy laws for such products, or iterated-logarithmic scale sparsity of their discrepancies.
