# Resolution of referee report 1: `papers/09-erdos-borwein-note/` (v1.0)

- **Reviser model:** Claude Sonnet 5.5 (Claude Code, T3 Code)
- **Date:** 2026-11-25
- **Report addressed:** `review-1.md` (Gemini 4 Neon, Antigravity; verdict: major revision; reviewed commit `a21f3114debd1059866364e8ae85f81717833600`)
- **Commit reviewed by the reviser (starting point of this revision):** `f65b1c7` (branch `publication/wave-2` at the time the revision branch `t3/revise-erdos-borwein-note` was created). The revised files are in the commit that adds this file.
- **Status:** AI model review and revision; not independent human peer review.

The revised note (`paper.tex`, 19 pages) still makes **no claim of normality or nonnormality** of E = Σ 1/(2^n − 1). It rebuilds with `wsl -d Ubuntu -- bash papers/wsl-build.sh 09-erdos-borwein-note` with no undefined references or citations and no overfull or underfull boxes, and the PDF author metadata is `Christopher Anderson`. No Lean file, `papers/common/`, `papers/0[1-5]-*`, registry, README, other manuscript or `\bibliographystyle` line was changed.

Summary of dispositions: Findings 1, 2, 3, 4, 6, 7, 8, 10 accepted; Findings 5 and 9 accepted with one sub-item each partly accepted or declined (stated below). New material: Proposition 7.2 (even-order sharpness), the Section 9 observation on Tao–Teräväinen, five new bibliography entries, and the script `even_order_check.py`.

## Finding 1 (Major): floating-point Section 8 overlabelled as Finite certificate. **Accepted** (option b: relabel)

- Theorems 8.2 and 8.3 are now **Propositions 8.2 and 8.3** with the label **Numerical evidence**. The note does not redo the computations in interval arithmetic and therefore does not keep the label "Finite certificate" for them. The statements are worded as numerical results ("the floating-point evaluation gives a value at most 0.4999592 …", "if these computed values are correct …").
- The label is consistent across the abstract (`paper.tex`, `submission/abstract.txt`, `alphaxiv.md`, `metadata.toml`, `summary.md`), the summary item (v) in Section 1, Table 1 and its caption, the proposition headers, Remark 8.4, Remark 8.5 (floating point) and Section 13, and `VERIFICATION.md` and `LEDGER.md`. "Numerical evidence" is not in the contract's label list; it is defined in the Table 1 caption and in `VERIFICATION.md` as a label weaker than Finite certificate. The coordinator may wish to add it to `papers/WAVE2-CONTRACT.md`.
- Remark 8.5 now says that the computations use round-to-nearest IEEE doubles, C-library elementary functions and hand-chosen margins, are not proofs, and that an interval or exact-rational recomputation would upgrade the label.
- Vaaler (1985) is stated as an **External input** with the theorem numbers the referee verified: Theorem 6 (p. 193, Ĵ), Theorem 18 (p. 210, ψ*j_N and the Fejér bound), Theorem 19 (pp. 211–212, the majorant), Theorem 20 (pp. 213–214, interval case). The proof of Proposition 8.2 now derives the Fourier coefficients from Theorem 19 applied to f = 1/2 + ψ(x) − ψ(x − 1/2) and records the endpoint check S⁺_N(0) = S⁺_N(1/2) ≥ 1, so the majorant inequality holds on all of ℝ/ℤ. The "unverified" markers in the paper, bibliography, ledger and verification map are removed. **Caveat:** these theorem numbers rest on the referee's reading of the AMS PDF; the reviser's automated download of the AMS PDF returned an HTML page, so the numbers are recorded as "as read by the referee" and are reserved for a human check.
- Location: `paper.tex` abstract, Section 1 (item v, Table 1), Section 8 (Propositions 8.2, 8.3, Remarks 8.4, 8.5), Section 13.

## Finding 2 (Major): Tao–Teräväinen Theorem 1.7 and Theorem 3.1. **Accepted**

- Theorem 1.7 quotation corrected to Pr(τ(n) = τ(n+1)) = (c_τ + O(log₂^{−c} x)) / (2√(π log₂ x)) (`paper.tex`, Section 9, "What we know of the literature").
- `submission/reviewer-inquiry.md`, Inquiry 1: the misplaced question about condition (3.2) is removed. The inquiry now states that (3.2) belongs to case (i), that g_θ(p) = e(θ) at every prime, that the referee's reading is that case (ii) applies at each fixed θ, and asks (1) whether that reading is correct including the shift range and the characters modulo 2^r, and (2) whether a single exceptional set uniform in θ is available; it names the passage to r ≥ 3 as the step the author cannot see. Inquiry 2 now cites Sibuya (1991) and Galambos–Simonelli (1996) precisely and mentions Proposition 7.2.
- The referee's finding that the pretentious-distance argument of their Section 4.1 shows that Theorem 3.1(ii) applies to e(θV)χ₁(U) at each fixed θ ∈ [1/R, 1/2] is incorporated as an **"Observation (not a theorem; fixed θ only)"** in Section 9, with the elementary computation (the pretentious distance is (1 − cos 2πθ)Σ 1/p ≫ R⁻² log₂ X because g_θ(p) = e(θ)), the L¹-in-θ almost-all-scales consequence by Fubini (their eq. (4.4)), and the limitations: the exceptional set depends on θ, so no single θ-uniform exceptional set (a θ-net needs about log N points); two-point only; r ≥ 3 (and r ≥ 9) open; two-point information cannot decide the bias (Theorem 6.1). The text states that the statement of case (ii) was read by a referee and not re-derived, and that the bookkeeping of the shift range of Hypothesis E was not checked. Target T3 (Section 12) was updated to match. The earlier sentence "we do not assert that it applies" was replaced accordingly.
- Not done: the reviser did not read the arXiv source of v2 and did not verify case (ii) independently.

## Finding 3 (Major): Remark 7.2, even-order infimum. **Accepted**

- The remark is replaced by **Proposition 7.2 (Even order)**, a Lean-supported paper proof (Lean step: the dual inequality inside Theorem 7.1): for every even r ≥ 2, inf E(−1)^N = e_{r−1} over laws with E(N)_k = 1 for 1 ≤ k ≤ r, and the infimum is not attained. The proof is written out: lower bound by Theorem 7.1 at the odd order r − 1; approximation by the laws on {0, …, r−1} ∪ {L} with ε = 1/(L)_r, δ_k = ε(L)_k = 1/(L−k)_{r−k}, weights u_n = w_n − (1/n!) Σ_{k=n}^{r−1} (−1)^{k−n} δ_k/(k−n)!, positivity (the weight u_{r−2} = (δ_{r−1} − δ_{r−2})/(r−2)! ≈ 1/((r−2)! L) lifts the unique zero weight of the odd-order primal law), and parity e_{r−1} + O(1/L); non-attainment from Δ(t) > 0 for t ≥ r and uniqueness of the law on {0, …, r−1}. The finite witness L = 50,000 is gone.
- Added `papers/09-erdos-borwein-note/even_order_check.py`: exact rational check of mass, moments up to order r, positivity and positive excess for r = 2, 4, …, 12 and L = 10², 10³, 10⁵ (passes). Listed in `VERIFICATION.md` (new row) and Section 13.
- Location: `paper.tex` Section 7 (Proposition 7.2); the numbering of later items is unchanged because remarks and propositions share a counter.

## Finding 4 (Major): stale PDF and `pdfauthor={}`. **Accepted**

- Removed the `pdfauthor={}` override (`paper.tex` line 4); the shared byline sets the author. `paper.pdf` rebuilt: `pdfinfo` reports `Author: Christopher Anderson`, 19 pages, built from the revised sources.

## Finding 5 (Major): bibliography. **Accepted, one sub-item partly**

- `tt2019`: `Th{\'e}orie` fixed.
- Internal audit notes removed from every `note` field (all "checked via Crossref", "not examined", "unverified" text); the record of what was verified is in `LEDGER.md`. The comment line at the top of `references.bib` points there. The `erdos1948` and `sude1` notes were also cleaned of audit remarks.
- `tao2016`: `pages = {e8}` added. `vaaler1985`: "unverified" removed; the note lists Theorems 6, 18, 19, 20.
- `miragist`: `{S06}` brace-protected (prints "S06"). `sude2`: the 64-character SHA-256 was removed from the bibliography (it stays in `LEDGER.md`), `\texttt` hash strings replaced by short hashes, full commit kept inside breakable URLs; the five underfull lines are gone.
- **Partly accepted:** `\bibliographystyle{plain}` drops the `doi` field. The style line is unchanged as instructed; each entry with a DOI now carries `note = {\url{https://doi.org/…}}`, so DOIs print.
- **Declined (minor):** `crandall2012` keeps the author as "Richard E. Crandall" (his full name; the journal PDF prints "Richard Crandall") and the single page designation `#A23`; the zbMATH page range 811–840 is an issue-level artefact and is not used.
- New entries (each checked against Crossref or the arXiv API; see `LEDGER.md`): `borwein1991`, `baileycrandall2002`, `aabb2013`, `vandehey2013`, `sibuya1991`, `gs1996` (a book entry with publisher and year; not in Crossref and not read).

## Finding 6 (Minor): Proposition 3.1(b). **Accepted**

- The cutoff is now 4N throughout: the proof shows that m − log₂ m is increasing for m ≥ 2 and 4N − log₂(4N) ≥ 3N ≥ 2N + d for N ≥ 4, so every relevant m ≤ 4N, and the strip contains at most 2 log₂(4N) + 2 integers; the sum over q is over squarefull q ≤ 4N. The unused "g =" is removed. The same fix is in `submission/reviewer-packet.md`.

## Finding 7 (Minor): Theorem 4.2 prose vs script. **Accepted**

- The method paragraph now describes the script: the carry DP over columns 2–48 gives certified bounds from which E(−1)^{c₁} is enclosed (47-column carry, truncation charge a multiple of 2(μ_max + 1)p₀⁴⁸); p_* is enclosed directly from the 48-column DP with charge 2(μ_max + 1)p₀⁴⁸; Proposition 2.2 relates the two, and the reported (direct) enclosure of p_* is slightly wider than the one Proposition 2.2 would give. The reported numbers are unchanged. Recorded in `LEDGER.md` (Theorem 4.2 entry) and `VERIFICATION.md`.

## Finding 8 (Minor): overfull boxes and the hyperref warning. **Accepted**

- `\linebreak[3]` removed and summary item (i) reworded; the Theorem 5.1 statement reworded; `parity\_\allowbreak bonferroni\_\allowbreak dual\_\allowbreak le` allows breaks; the section title uses `\texorpdfstring{$16$}{16}`; `miragist`/`sude2` entries shortened. The final build has no Overfull/Underfull box and no hyperref warning.

## Finding 9 (Minor): jargon and small items. **Accepted, one sub-item partly**

- `CC-30` removed from the body (the earlier 32-column statement is described without a registry code). Script names `phase16_…` and `phase17_…` appear only in Section 13; elsewhere the text says "the certificate script of Section 13". "Repository notes" references (Remark 3.2, Section 9 bullets and preamble, the Mira Cult audit remark, the Crandall orientation sentence) are rewritten; the local limit law for V is now described as expected and unused. The reproduction pointers "script section C/E/F/H" remain, since Section 13 defines the script.
- Proposition 8.1: A_I(2m) = A_{I+1}(m) with I + 1 = [N+1, 2N+1) and |A_{I+1}(m) − A_I(m)| ≤ 2/N uniformly in m, hence O(1/N); the proof now says why.
- `{0,..,r}` replaced by `\dots`.
- Theorem 7.5: added the observation that the pointwise inequality Φ ≥ Ψ₁₆ together with the carry-knapsack bound and E c ≤ μ gives f(1) < 1/2 for every law in 𝓘_{16,92}, hence r_min(16) ≤ 92 (also in `reviewer-packet.md` and `VERIFICATION.md`).
- **Partly accepted:** `metadata.toml` `status` changed from "research note" to "preprint draft" to follow `WAVE2-CONTRACT.md` (all other manuscripts use it). The title page still says "research note" and "1.0 (research note)". The coordinator should confirm whether "research note" was intended as a distinct status. `registry_ids` was not changed (registry is out of scope).

## Finding 10 (Editorial): literature omissions. **Accepted**

- Added to `paper.tex` (Section 1, and a new "Published background" paragraph in Section 11) and to `LEDGER.md`: Bailey–Crandall (2002), Experiment. Math. 11(4), 527–546, Section 5 (Conjecture 5.3 and the theorem that follows it: 2-normality of E is equivalent to equidistribution of an explicit sequence; the theorem is numbered 5.4 in the author preprint of March 2003 that the reviser read and 5.5 in the referee's reading of the journal version, which is stated in the text); P. B. Borwein (1991), J. Number Theory 37(3), 253–259 (metadata only; whether 1991 or 1992 first covers q = 2, r = −1 is stated as unknown); Aragón Artacho–Bailey–Borwein–Borwein (2013), Math. Intelligencer 35(1) (as reported by the referee; not read); Vandehey (2013), Integers 13, #A58 (negative-base completion of Erdős's argument).
- Recorded that the parity bound (Theorem 7.1, and Proposition 7.2) fits the Sibuya (1991) majorant–minorant framework and Galambos–Simonelli (1996), is not stated there on the referee's reading (and the reviser's text search of Sibuya's PDF finds no "parity" or "Poisson"), and that no priority is claimed: Section 11 paragraph "Sharp Bonferroni-type bounds", the `LEDGER.md` Theorem 7.1 entry, and `reviewer-inquiry.md` Inquiry 2.
- `LEDGER.md` updated throughout: scope-of-search record for the revision, the caution table (Vaaler, Tao–Teräväinen v2 with the corrected quotation, new keys, Borwein), credit entries, the Theorem 4.2, 7.1/7.2 and 8.2/8.3 entries. The two tangential papers (Merca 2015; Murakami–Tachiya 2025) are recorded in the ledger but not cited, since they concern irrationality or inequalities, not digits.

## Other files touched

`VERIFICATION.md` (relabelled rows, new Proposition 7.2 row, Vaaler external input, floating-point note, reproduction command), `metadata.toml` (abstract, status), `submission/abstract.txt` (236 words), `submission/alphaxiv.md`, `submission/summary.md`, `submission/reviewer-packet.md`, `submission/reviewer-inquiry.md`, `references.bib`, `paper.pdf`. Not touched: `announcement.md` (no change needed), `alphaxiv.toml`, `crosscheck.py`, scripts, Lean.

## Questions reserved for collaborators

1. **Interval or exact-rational recomputation** of Section 8 (φ(m), the degree-116 evaluation, the degree-110 quadrature weights). Who can supply it? It would restore the label "Finite certificate", with Vaaler's majorant property remaining an external input.
2. **Vaaler (1985):** an independent human confirmation of Theorems 6, 18, 19 and 20 as stated, in particular the pointwise endpoint behaviour of the majorant.
3. **Tao–Teräväinen v2:** does case (ii) of Theorem 3.1 apply to g_θ = e(θV)χ(U) as read (including uniformity in the shifts and in characters modulo 2^r)? Can a single exceptional set be made uniform in θ? Is there any route from two points to r ≥ 3 (and r ≥ 9) points?
4. **Sharp Bonferroni bounds:** is the value Σ_{k≤r}(−2)^k/k! for inf E(−1)^N (odd r), and e_{r−1} for even r, stated in the Sibuya / Galambos–Simonelli literature or elsewhere? (Galambos–Simonelli was not read.)
5. **Bailey–Crandall (2002):** the theorem number of the 2-normality equivalence in the journal version (5.4 or 5.5); and whether their Section 5 contains any frequency statement for E beyond the equivalence.
6. **P. Borwein (1991) vs (1992):** which first covers q = 2, r = −1; and the contents of Aragón Artacho et al. (2013) on E.
7. **Crandall's counts (target T1):** Mitchell's raw output or independent certified shell frequencies to s ≈ 30, to decide the orientation of the counts.
8. **Coordinator decisions:** whether "Numerical evidence" should be added to the contract's label list; whether `status` should be "preprint draft" or a distinct "research note".
