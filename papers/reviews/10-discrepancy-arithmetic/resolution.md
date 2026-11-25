# Resolution of Referee Reports 1 and 2 on Manuscript H (*The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*, v1.0)

- **Reviser model:** Claude Sonnet 5.5 (Anthropic)
- **Date:** 25 November 2026
- **Commits reviewed:** review 1 names `9a64d5b3eb2a1f2a9545c8a8fc20c4bd4622b718`; review 2 names `40f8fb69656f3257f408c0538b56bf768132ce21`. The revision starts from `f65b1c745a5fee8dfef858f95a47024b1ca5d158` (branch `publication/wave-2`, worktree branch `t3/revise-discrepancy-referees`). Lean links remain pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec` and `c2c9da683666b3b9368e5d4b5cb858caccf528f5`.
- **Status:** **AI model review and revision; not independent human peer review.**

The reports are `review-1.md` (Gemini 4 Argon; accept with minor revisions; 4 minor and 3 editorial findings) and `review-2.md` (Gemini 4 Neon; minor revision; 3 major and 4 minor findings, several with sub-items). Line numbers refer to the revised `papers/10-discrepancy-arithmetic/paper.tex` unless stated. The rebuilt PDF has 16 pages, no undefined references or citations, and PDF author `Christopher Anderson`; it is byte-identical on a second build. All 36 distinct pinned Lean URLs in the PDF (39 link annotations) were checked against `git show <commit>:<path>` (0 mismatches), as were all 37 Lean links in `VERIFICATION.md`. No Lean files, `papers/common/`, `papers/0[1-5]-*`, the registry, the README or other manuscripts were modified, and the `\bibliographystyle` line is unchanged.

I verified the factual claim of Finding R2-1 myself against the arXiv PDF of `arXiv:2506.12929v1` (text extracted locally): Section 8 uses ordinary binary digits, and the word "signed" does not occur anywhere in the paper. I also read Proposition 4.25 and the remark on Kamae after Proposition 4.9 in the same text. I added one new file, `checks/cubic_boundary_check.py` (exact rational check of the cubic schedule of Theorem 6.2(b)), in response to R2-2.3.

## Disposition summary

| Finding | Severity | Disposition |
| --- | --- | --- |
| R1-1. Evidence label of Theorem 4.5 inconsistent | Minor | Accepted |
| R1-2. lcm denominator bound unproved | Minor | Accepted |
| R1-3. Boundary case $l=1-2\epsilon$ in Lemma 2.2 | Minor | Accepted |
| R1-4. Unused $p$ and $t=\operatorname{ord}_p b$ in Theorem 6.2(b) | Minor | Accepted |
| R1-5. `Levy39` volume | Editorial | Accepted |
| R1-6. Lower summation index | Editorial | Accepted |
| R1-7. Second citation of BD25 Proposition 4.25 | Editorial | Accepted |
| R2-1. BD25 Section 8 mischaracterized as signed digits | Major | Accepted |
| R2-2. Contradictions in `VERIFICATION.md` (items 1–5) | Major | Accepted (5 of 5) |
| R2-3. Bibliography (items 1–4) | Major | Accepted 1 and 3; item 2 deferred to the coordinator; item 4 partly accepted |
| R2-4. Lower summation bounds | Minor | Accepted |
| R2-5. Lean citation gaps (items 1–4) | Minor | Accepted (4 of 4) |
| R2-6. Exposition and typesetting (items 1–4) | Minor | Accepted 1–3; item 4 partly accepted |
| R2-7. Submission package (items 1–5) | Minor | Accepted 2–5; item 1 deferred to integration |

---

## Report 1 (Gemini 4 Argon)

### R1-1. Theorem 4.5 evidence label — Accepted
- **Change:** I chose the reviewer's second option and kept the label `Lean-supported paper proof`, but the reviewer is right that the stated Lean step was not accurate: the proof of Theorem 4.5 does not use Theorem 3.1 directly. The proof now names the actual Lean-supported step, the subgroup property of $K_b$, which follows from the kernel-verified triangle inequality for $d^+$ (`asymDist_triangle`), and says that Lemma 4.4, the valuation argument and (through Lemma 4.4) Theorem 3.3 are written (`paper.tex` l. 544–547). The proof of Proposition 4.3 now spells out that the kernel is $\{z:D_N(z)\to1\}$ and that its subgroup property follows from the triangle inequality and translation invariance (`asymDist_translate` L381, newly linked; l. 507–511). Section 8 now lists Proposition 4.3 (see R2-2.1) and states that Theorem 4.5 uses only the subgroup property from Lean (l. 916–921).
- **Companion files:** `VERIFICATION.md` row C now reads "Kernel-verified pseudometric (= Prop 4.1); Prop 4.3 and Thm 4.5 are Lean-supported paper proofs; Prop 4.6 is a paper proof"; rows 4.3 and 4.5 describe the Lean and written steps; `LEDGER.md` (Proposition 4.3/4.5/4.6 entry), `submission/reviewer-packet.md` §4 and `submission/alphaxiv.md` (verification scope) agree.

### R1-2. lcm denominator bound — Accepted
- **Change:** After Lemma 2.5 the text now proves the sharper bound: since $\{R_{k-1}\}=u_{k-1}$, the number $c_k-(u_k-b^{n_k-n_{k-1}}u_{k-1})$ is an integer, so $\operatorname{den}c_k$ divides $\operatorname{lcm}(\operatorname{den}u_k,\operatorname{den}u_{k-1})$. It also records that the Lean declaration `programCoeffs_den_dvd` (L416, newly linked) gives only the product bound, which suffices for prime powers (`paper.tex` l. 254–259). The proof of Theorem 6.2(b) cites the lcm bound and says explicitly that it is a written step (l. 830–833); see R2-5.2.

### R1-3. Boundary case $l=1-2\epsilon$ in Lemma 2.2 — Accepted
- **Change:** The proof now reads: if $l\ge1-2\epsilon$ then $\mu_u(I)-l\le1-l\le2\epsilon$; if $l<1-2\epsilon$ then $v_n$ lies in the half-open arc $[\theta-\epsilon,\theta+l+\epsilon)$, of length $l+2\epsilon<1$. The auxiliary $\eta$ is removed altogether, which is simpler than bounding it (`paper.tex` l. 187–194). The inclusion holds because $u_n<\theta+l$ strictly.

### R1-4. Unused $p$ and $t=\operatorname{ord}_p(b)$ in Theorem 6.2(b) — Accepted
- **Change:** I took the reviewer's second option: a sentence after the statement says that $p$ enters only through $t$, which fixes the schedule $n_k=tk^3$ of Theorem 5.3, and that the proof works for every fixed integer $t\ge1$ (l. 813–814). The constant stays $C_{b,p,m}$ (see R2-5.3).

### R1-5. Missing volume of `Levy39` — Accepted
- **Change:** `volume = {67}` added to `references.bib`. I confirmed volume 67, pages 1–41, from the Numdam record `BSMF_1939__67__1_0` (its citation metadata). `LEDGER.md` now records this instead of "no volume is given".

### R1-6. Lower summation index — Accepted
- **Change:** $\sum_{k\ge1}$ in Theorem B (l. 77), after Lemma 2.5 (l. 260), Theorem 5.3 (l. 641) and Theorem 6.2(b) (l. 810); $\sum_{1\le i\le k}$ in Lemma 2.5 (l. 245). See also R2-4.

### R1-7. Second citation of BD25 Proposition 4.25 — Accepted
- **Change:** `VERIFICATION.md` (row 4.6 and "External analytic dependencies") now states that Proposition 4.25 is cited twice, in the introduction after Theorem D and in the remark after Proposition 4.6, and that neither use is a step of a proof. I read the proposition in the arXiv text: it gives $\underline h(qx)=\underline h(x)$ and $\overline h(qx)=\overline h(x)$ for every nonzero rational $q$, and hence preservation of normality and determinism; `LEDGER.md` now says so verbatim-checked. Also: the introduction's remark on Wall is reworded (see R2-3.4).

---

## Report 2 (Gemini 4 Neon)

### R2-1. BD25 Section 8 mischaracterized — Accepted (verified against the primary text)
- **Verification:** In `arXiv:2506.12929v1`, Section 8 is "Behavior of normal and deterministic numbers under multiplication". Theorem 8.11 shows that $xy$ is deterministic for the normal number $x$ of §8.2 and the number $y$ of §8.3 whose binary digits are the indicator of $\{0\}\cup\mathsf{FS}((n_k))$; the proof shows that the binary expansion of $xy$ has density zero of switches ($01$, $10$). Proposition 8.13 shows that $1/y$ is deterministic, with an expansion of density zero of ones. Corollary 8.14 takes $a=xy$ and $b=1/y$, both deterministic with $ab=x$ normal. All binary expansions are ordinary $\{0,1\}$ sequences, and "signed" does not occur in the paper.
- **Change (paper):** the passage after Proposition 6.3 (l. 866–877) now says that Bergelson and Downarowicz construct, in base 2 and with ordinary binary digits, a number $a$ with density zero of digit switches and a number $1/y$ with density zero of ones whose product is normal, citing Theorem 8.11, Proposition 8.13 and Corollary 8.14. It gives the reason that both factors satisfy $M_N\to0$ (each maximal run of equal digits, respectively each digit 1, contributes $O(1)$ to $\sum_{n<N}\lVert2^nw\rVert$), which I checked, and calls their example stronger in base 2. The false contrast "positive digits" is removed; the genuine distinctions (every base, explicit rational product, explicit rate for the factors) are kept.
- **Change (ledger):** the Proposition 6.3 entry, its search record and the bibliography-verification paragraph now describe Section 8 from the primary text, name the three results, and state that the earlier "signed digits" description was an error inherited from a research note.

### R2-2. Contradictions and inaccurate records in `VERIFICATION.md` — Accepted (5 of 5)
1. **Row C versus rows 4.3, 4.5 and `paper.tex` §8 — accepted.** Row C corrected as in R1-1. Section 8 of the paper now lists Proposition 4.3 (the triangle inequality and the integer Lipschitz bound for $d^+$ are Lean; the kernel description is written) and says Theorem 4.5 uses only the subgroup property from Lean (`paper.tex` l. 916–925). `submission/alphaxiv.md` is aligned.
2. **Row 3.5 script — accepted.** The reviewer is right that none of the six tests concerns $Z=\sum2^{-k(k+1)}$. Row 3.5 now cites `lake build` at `e4809cf` for the kernel-verified finite inequality and says no script covers the rate or irrationality. `scripts/test_phase18_summation.py` (`test_translation_with_boundary_crossings`) moved to row 3.1 as a finite check of Theorem 3.1 and Corollary 3.2 on rational shifts; the "Reproduce" section says the same. `lake build` entries now say "at `e4809cf`" or "at `c2c9da6`", and the section "What is completely kernel-verified" says that these refer to the recorded full builds, which this worktree did not rerun.
3. **Row 6.2: "seven" versus eight, and linear versus cubic — accepted.** Row 6.2 now says eight cases (four $(b,m,m_0)$ tuples times $\theta\in\{0,0.5\}$) and that §6 of `geometry-periods-check.py` is a floating-point simulation of a linear digit-word block schedule that prints a table and asserts nothing. I took the reviewer's second option as well: `checks/cubic_boundary_check.py` is a new standard-library script that builds the actual cubic schedule $n_k=tk^3$ (greedy scheduler with exact rational weights, coefficients from Lemma 2.5), asserts $0<c_k\le1$, $\operatorname{den}c_k\mid m_0$ and $\{R_k\}=u_k$, and computes $D_N(x)$ and $D_N(mx)$ in exact integer arithmetic. It covers 10 cases $(b,m,\theta)$ with $t\in\{1,\operatorname{ord}_pb\}$, cross-checks its discrepancy routine against the definition on 200 random samples, exits with status 0 in about 7 seconds, and gives a largest $(|D_N(x)-\delta|+|1-D_N(mx)|)N^{1/3}$ of 3.28 at the sampled $N\le12{,}000$ (it asserts an empirical ceiling of 10). It is a finite check, not a proof; `VERIFICATION.md` and `LEDGER.md` say so. Row 6.1 also cites §5 of the geometry script (300 random cases).
4. **Lean URL count — accepted.** Replaced by "39 Lean link annotations pointing to 36 distinct URLs (three declarations are linked twice)". The numbers changed from 33 and 30 because six links were added in this revision: `programCoeffs_den_dvd`, `discrepancy_deficit_le`, `discDist_nonneg`, `discDist_self`, `asymDist_translate` and `finite_necessity'`. All 36 URLs were checked at their commits.
5. **Liouville — accepted.** Proposition 3.6 claims only that $Z_!$ is a Liouville number, proved by the direct approximation estimate. The "Liouville's theorem" bullet is removed from the external dependencies and from row 3.6 (which now says no transcendence is claimed).

### R2-3. Bibliography — Accepted 1 and 3; 2 deferred; 4 partly accepted
1. **`Levy39` volume — accepted** (see R1-5); `LEDGER.md` l. 15 updated.
2. **`\bibliographystyle{plain}` drops DOIs and URLs — deferred, by instruction.** The task forbids changing the style line because the coordinator will switch the style globally to one that prints DOIs. All `doi` and `url` fields are in `references.bib` and are unchanged.
3. **Doubled year in `BD25` — accepted.** `howpublished` is now `arXiv:2506.12929 [math.DS], version 1, 15 June`; the rendered entry reads "version 1, 15 June, 2025."
4. **Wall, Kamae, Kuiper — partly accepted.**
   - *Kamae:* accepted. `Kamae76` (T. Kamae, *Normal numbers and ergodic theory*, Lecture Notes in Mathematics 550, pp. 253–269, Springer, 1976, doi:10.1007/BFb0077494) is added. Author, title, pages, year and DOI match the Crossref record; the volume number 550 and the symposium title are as in BD25's reference list. The introduction now cites it only for the attribution that BD25 make (their remark after Proposition 4.9: Kamae introduced a point entropy equal to the upper entropy and proved inequality (d)). Kamae's paper was not read; the ledger says so.
   - *Wall:* declined as a bibliography entry. The thesis (Berkeley, 1949) could not be consulted and the contract forbids unverified entries. The unreferenced phrase "a classical theorem of Wall" is replaced by "the classical theorem of Wall on normality quoted there" (l. 113–114), and the ledger lists Wall as unverified.
   - *Maxfield:* not cited in the paper, so no entry.
   - *Kuiper:* declined. The entry follows the DOI record (*Indagationes Mathematicae (Proceedings)* 63:38–47). I could not verify the proposed identification with *Indag. Math.* 22 against a primary source, so I did not add it.

### R2-4. Lower summation bounds — Accepted
- **Change:** $1\le i\le k$ in Lemma 2.5 (l. 245); $k\ge1$ in Theorem B (l. 77), after Lemma 2.5 (l. 260), Theorem 5.3 (l. 641) and Theorem 6.2(b) (l. 810); in the proof of Theorem 5.3, $h_k\le7tk^2$ is now stated "for $k\ge1$", $q_k$ is defined "for $k\ge1$" (l. 651–652) and $H=\sum_{1\le k\le K}$ (l. 669).

### R2-5. Lean citation gaps — Accepted (4 of 4)
1. **`discDist_nonneg` (L39) and `discDist_self` (L51)** added to the list in Proposition 4.1 (l. 430–431) and to row 4.1 of `VERIFICATION.md`.
2. **Denominator bound in Theorem 6.2(b):** see R1-2. The proof now says that $\operatorname{den}c_k\mid m_0$ uses the written lcm bound because the Lean declaration gives only $m_0^2$; row 6.2 and the ledger say the same.
3. **Constant subscript:** $O_{b,m}(K^2)$ changed to $O_{b,p,m}(K^2)$ (l. 835); the remark about $t$ is R1-4.
4. **Understatements in `VERIFICATION.md`:** equation (4) is now cited as the kernel-verified `discrepancy_deficit_le` (L524; also linked in the paper after (4), l. 297) and its row is relabelled `Kernel-verified`; the `max`/`abs` form of (1) is linked as `finite_necessity'` (L260) in the proof of Theorem 5.1 (l. 594) and in row 5.1. The statement of `discrepancy_deficit_le` matches (4): `farCount` counts $n<N$ with $\lVert b^nz\rVert>\epsilon$.

### R2-6. Exposition and typesetting — Accepted 1–3; 4 partly accepted
1. **Remark 3.4:** "the two fixed points $0^\infty$ and $(b-1)^\infty$ of the shift" (l. 362).
2. **Proposition 4.6:** the step is now written out: $|e_n|=\lVert b^n(z-c)\rVert$ since $bc\equiv c$, so $N^{-1}\sum_{n<N}|e_n|=M_N(z-c)\to0$ by Theorem 3.3(vi), and Markov's inequality gives $\#\{n<N:|e_n|>\rho\}=o(N)$ (l. 560–564).
3. **Proposition 6.3:** $w=\lceil\log_b(N+1)\rceil$, as in the other sparse-remainder proofs (l. 858). I left the bound "within $2b^{-w}$", which is safe, as the reviewer notes.
4. **Underfull boxes — partly accepted.** The two bibliography entries that triggered badness-10000 boxes now carry `\allowbreak` points (`\path` from `xurl` was tried first and breaks inside words, so I did not keep it); those boxes are gone. Four mild underfull paragraphs remain (badness at most 4096, the largest in the Lean-name paragraph after Lemma 2.5); there are no overfull boxes. I did not reflow them.

### R2-7. Submission package — Accepted 2–5; 1 deferred
1. **Release-commit placeholder in `submission/alphaxiv.md`** — deferred to integration. There is no release commit yet; the text already says the link will be added at integration, and the Lean links in the paper are pinned.
2. **`alphaxiv.toml`** — `Gemini 4 Neon` added as referee 2, the Argon entry now says "report 1 (AI model review; not independent human peer review)", and a `Claude Sonnet 5.5` entry records this revision. `owner_confirmed = false` is left as it is, since it is the owner's decision.
3. **`reviewer-inquiry.md`** — `\pmod 1` added to $q_n\equiv p_n\pm r_n$. The release-link placeholder is intentional in a draft and is kept.
4. **`reviewer-packet.md`** — `PrimePowerGrid.primePower_period_count` (P L313, through Lemma 2.4) added to the Lean-supported steps of Theorems 5.3–5.4; §4 aligned with R1-1.
5. **`abstract.txt`** — `\mathbb{Z}[1/b]` replaced by `Z[1/b]`, matching `metadata.toml`; the abstract is still under 250 words.

---

## Unchanged by this revision
- `metadata.toml` (abstract, version, registry identifiers), `submission/summary.md` and `submission/announcement.md` needed no change.
- `papers/SHA256SUMS` was not touched; `python papers/check_release.py` reports that it differs from the manuscript PDFs; the file records only the five archived PDFs, so the message is not caused by this revision. Also, `--verify-pins` needs a Windows `pdfinfo`, which is not installed. I used the WSL Poppler and my own script for the pin check instead.

## Questions reserved for a human specialist
1. **Folklore status of Theorem 3.1.** Is the finite identity $\sup_x|D_N(x+z)-D_N(x)|=1-D_N(z)$, or the paired-sample inequality $D(q)\le D(p)+1-D(r)$, recorded in the literature on Kuiper's statistic, circular concentration functions or probability metrics (for instance in exercises of Kuipers–Niederreiter, Chapter 2, or Drmota–Tichy)? Both referees found it elementary once written in concentration form.
2. **Entropy side of the addition polytope.** Is the five-vertex polytope known to be the exact set of attainable point-entropy triples in Bergelson–Downarowicz (their §4.3, Examples 4.20–4.23, which I did not read in full), or is completeness open there?
3. **Theorem 3.3, (i)⇒(vi).** Is the argument that the nearest fixed point $f_N$ is eventually constant (consecutive empirical measures differ by $O(1/N)$) complete?
4. **Theorem 5.3 and Lemma 5.2.** The scheduler bounds with approximate weights, the summation by parts giving $|Z-\delta N|\le t+17h_K$, and the choice of $W$.
5. **Theorem 5.4.** The override and certificate-survival argument for algebraic independence (permanence of the interval enclosures under every later choice of coefficients in $(0,1]$).
6. **Rauzy's theorem.** The comparison with $\mathcal D(b)$ in Remark 3.4 relies on Bergelson–Downarowicz's reformulation (Definitions 3.5, 3.10, Theorem 3.12); Rauzy's original theorem number and the primary text were not available.
7. **Attributions not checked in primary sources.** Wall's thesis (normality under rational multiplication) and Kamae's paper (inequality (d)) are cited only through Bergelson–Downarowicz; Moser (1962) and de Bruijn (1964) for the decomposition used in Proposition 6.3 are not cited. A specialist should say whether the Moser–de Bruijn product example is known and whom to credit.
8. **Version of Bergelson–Downarowicz.** Only arXiv v1 was read. If a revised or journal version renumbers Section 8 or Proposition 4.25, the theorem numbers cited here need updating.
9. **Optimality of the exponent $1/3$** (Question 7.1) and whether the Haar-mixture and joint-spectrum extensions mentioned in `LEDGER.md` are worth a separate paper.
