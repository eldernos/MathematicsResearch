# Resolution of the referee reports on Manuscript A (*Disjunctive but Nonnormal Multiplicative Lambert Series*, v1.0)

- **Reviser model:** Claude Opus 5.5 (Anthropic), Claude Code in T3 Code
- **Date:** 25 November 2026
- **Commits reviewed:** both reports reviewed `dedc430` (`dedc4302b1f68576f8adfcdde28c5d3642d03d22`), with Lean pinned at `e4809cf561573aef588e6ffc491a35cdb79fd9ec`. The revision starts from `f65b1c7` on `publication/wave-2` (worktree branch `t3/revise-lambert-referee-reports`).
- **Status:** **AI model review and revision; not independent human peer review.**

Reports: `review-1.md` (GPT-6.2 Astra, OpenAI Codex; verdict: major revisions; no critical mathematical defect) and `review-2.md` (Gemini 4 Argon, Antigravity; verdict: accept with minor revisions). Locations refer to the revised `papers/06-multiplicative-lambert/paper.tex` and the rebuilt PDF (21 pages). The headline theorems keep their numbers. New numbered items are confined to §10 (Theorem 10.1, Lemma 10.2, Theorem 10.3). Equation (4), the prime-input hypothesis (P_ν), is new in §4, so the former (4) is now (5). No Lean files, `papers/common/`, `papers/0[1-5]-*`, the registry, the README or other manuscripts were modified. The `\bibliographystyle` line is unchanged.

## Primary sources checked for this revision

- **Bailey–Borwein–Crandall–Pomerance 2004** (J. Théor. Nombres Bordeaux 16, 487–518, DOI 10.5802/jtnb.457). Read in the Numdam scan, §9, pp. 505–512. Checked: the definitions of z and z′ with z′² = Σ r₂(n)2⁻ⁿ (p. 505); Theorem 9.4 with C₀ ≈ 0.7996 and the paragraph after it on z′² (p. 509); Lemmas 9.5 and 9.6 (p. 509); the proof with the isolated set S_N (pp. 509–511); the formula for C₀ (p. 511); and the remark that the T_g(N) asymptotics follow from Landau's formula (pp. 511–512).
- **Kumchev 2002** (Q. J. Math. 53, 479–501). Main Theorem (i)–(iii) and (1.7)–(1.10) read in the author's posted text (pp. 2–3, a draft dated 11 September 2015). Crossref record for the metadata. The journal printing was **not** accessible.
- **Baker–Harman–Pintz 1997** (LMS Lecture Note Ser. 237, pp. 1–54). Theorem 3(I) on p. 4, read in the publisher preview, plus the Crossref record. The printed display reads 0.99M/ℒ < π(x;q,a) − π(x−M;q,a) < 1.01M/ℒ without the factor 1/φ(q); Kumchev's restatement (1.3) includes it.
- **Erdős 1948**, p. 63 (scan). The theorem covers g(x) = Σ xⁿ sin(nπ/2)/(1−xⁿ); Chowla is credited in the footnote.
- **Luca–Tachiya 2014.** Crossref record with abstract.
- **Bailey–Crandall 2002.** Authors' posted text, §5 (Conjecture 5.3, Theorem 5.4), plus Crossref.
- **Duverney–Tachiya (2019 manuscript).** Used for the Chowla citation and the historical account.
- **Companion manuscript H.** `papers/10-discrepancy-arithmetic/paper.tex` and the built PDF, Theorem 3.1.

## Report 1 (GPT-6.2 Astra)

| # | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| 1 | BBCP 2004 already gives the one-bit asymptotic for the flagship example; credit irrationality precedents | Major | Accepted |
| 2 | Published fixed-progression bounds (BHP 1997, Kumchev 2002) answer the window question | Major | Accepted (range extended to a > 0.53 in a separate theorem) |
| 3 | Abstract omits (H4) and the bounded harmonic remainder; Example 1.3 overclaims | Major | Accepted |
| 4 | Checked-in PDF has the obsolete anonymous byline | Major | Accepted |
| 5 | Coefficient support vs digit positions; quarter-density wording; summary wording; Shiu attribution | Minor | Accepted |
| 6 | Two meanings of ω in the Selberg sieve | Minor | Accepted |
| 7 | Positive weight and nonzero nome in Theorem 9.1 | Minor | Accepted |
| 8 | Quantifiers, notation clash, packet step 4, announcement, release pin, companion, Calude–Priese–Staiger note | Editorial | Partly accepted |

**R1.1 (accepted).** Bailey, Borwein, Crandall and Pomerance (2004) are now credited in the following places:
- **Abstract** (paper.tex l. 24 ff.; `metadata.toml`; `submission/abstract.txt`; `submission/alphaxiv.md`): a sentence stating their asymptotic C₀M/√(log M) for θ₃(1/2)² = 1 + 4L_{χ₄}, and what is new beyond it.
- **Introduction** (new paragraph at l. 74). It gives Theorem 9.4 (p. 509) and the paragraph after it, and derives the prefix and macroscopic-window (ηN ≤ H ≤ N) one-bit asymptotics for L_{χ₄}. It says this is stronger than Corollary 1.1 for w = 1 in that example. It names the isolated-coefficient overlap and lists what is new: windows H ≥ N^a with a < 1, all words, the discrepancy order, and the general class.
- **§1.4** (new paragraph "The theta-square example", l. 286). It describes the BBCP statement and Lemma 9.5. It records that the T_g(N) asymptotics in BBCP are indicated as corollaries of Landau's formula. It sets out the methodological overlap and the exact list of additions.
- **Narrowed claims.** The priority sentence in §1.4 now opens "Apart from the one-bit results of [BBCP] for χ₄". Question Q1 now states that BBCP answer it for χ₄, w = 1 and windows ηN ≤ H ≤ N, with limit C₀.
- **Irrationality precedents** (new paragraph "Irrationality", l. 313; end of the new introduction paragraph; Example 1.3):
  - Chowla 1947 for t ≥ 5. The bibliography entry is marked unverified because the full text was not examined.
  - Erdős 1948, whose second series has weight sin(nπ/2) = χ₄(n).
  - Luca–Tachiya 2014, for eventually periodic rational numerator sequences that are not eventually zero, at every integer base |q| > 1. This covers all real characters, even and imprimitive ones included.
- **Bibliography and files.** New bibliography entries: `BBCP2004`, `Chowla1947`, `LucaTachiya2014`. The Theorem A, Theorem B and audit sections of `LEDGER.md` were rewritten with quotations and an explicit "specializes and is weaker than BBCP" relation for χ₄ and the digit one. `submission/summary.md`, `announcement.md`, `alphaxiv.md` and `reviewer-packet.md` all credit BBCP.

**R1.2 (accepted).** I carried out the adjustment and kept it separate from the headline theorems, which still rest on Perelli–Pintz–Salerno (checked against the printed source).
- **Equation (4), §4.** The lower-bound input (P_ν) is defined for one fixed progression in every interval (X, X+Y] with Y ≥ (X+Y)^ν. Lemma 4.4 gives it for ν > 7/12.
- **Proposition 5.3** (l. 775) is now stated for any ν_* ≥ 1/2 such that (P_ν) holds for all ν > ν_*. The parameters are θ = min{1/4, (a−ν_*)/2} and ν = ½(ν_* + a − θ). The far-tail exponent 7/8 is replaced by β = ½ + 1/(4(a−θ)) ∈ (1/(2(a−θ)), 1), as the referee suggested, which gives log(Y/d′) ≥ (1−β) log Y. The lower-bound constants c_P replace the asymptotic in (5), in the counting step and in the final sum.
- **§10.1** (rewritten, l. 1107):
  - Theorem 10.1 quotes Kumchev's main theorem exactly as posted by the author.
  - Lemma 10.2 proves (P_ν) for every ν > 0.53. It uses the single term q = q₀ of (1.10) with h = z = Y and x = 3(X+Y)/2, together with the minorant property (i) and the long-interval mass (ii).
  - Theorem 10.3 states that the lower bounds of Theorem A and the window statement of Corollary 1.1 hold for every fixed a > 0.53. Its evidence label is **Paper proof**, with the external input and the version caveat stated.
- **Baker–Harman–Pintz Theorem 3(I)** (p. 4) is cited as giving ν > 11/20 after subdivision. The text records Kumchev's remark that 0.525 is out of reach for progressions.
- **Other places.** Question Q2 is reframed as "below 0.53". Theorem A is followed by a sentence pointing to Theorem 10.3. Reviewer inquiry 2 is rewritten to ask whether the single-modulus use of (1.10) is legitimate and whether the published statement matches the posted one. `VERIFICATION.md` has new rows (Theorem 10.1, Lemma 10.2, Theorem 10.3) and new external-input rows. `LEDGER.md` has a new Theorem 10.3 entry. New bibliography entries: `Kumchev2002`, `BHP1997`.
- **Not claimed.** The abstract keeps a > 7/12, because the version of record of Kumchev's paper was not examined.

**R1.3 (accepted).**
- **Abstract** (paper, `metadata.toml`, `abstract.txt`, `alphaxiv.md`): states the bounded-remainder hypothesis Σ_{p≤x,p∈S} 1/p = δ log log x + O(1) and (H4), c(p₀^{2u}) = 2u+1.
- **Theorem A** (l. 148): restates both conditions in its statement and says that the upper bounds need only (H1)–(H3). A paragraph after it explains where (H4) and the bounded remainder are used (Proposition 5.3; Lemmas 3.1, 4.5, 4.6).
- **Example 1.3** (l. 222): "satisfies all theorems above" is replaced by the explicit list (Theorems A and B, Corollaries 1.1 and 1.2). Transcendence is claimed only for odd χ, with a pointer to Remark 9.2 for even χ.

**R1.4 (accepted).** Rebuilt with `wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert`. Page 1 reads "Christopher Anderson / Independent Researcher / Version 1.0 · 25 November 2026 · manuscripts-v2.0.0", and `pdfinfo` reports `Author: Christopher Anderson`. `papers/SHA256SUMS` has no entry for this manuscript and was not touched; recording checksums is left to the release integration.

**R1.5 (accepted).**
- **Example 1.3:** now says "c_{χ₄}(n) > 0 exactly when n is a sum of two squares", and adds a parenthesis: c(3) = 0, yet the third digit is 1 because of carries from c(4) and c(5). I verified this numerically.
- **Quarter-density example:** the abstract, `metadata.toml`, `summary.md` and the forum announcement now say "c(p) = 2 exactly at the primes p ≡ 1 (mod 5)". Example 1.4 already defined c = f∗1 correctly.
- **`summary.md`:** now reads "b = p₀^{2u}m with m squarefree", and attributes the short-interval bound for U to Shiu with x^σ ≤ y ≤ x.

**R1.6 (accepted).** In Lemma 4.7 the class count is now ρ(q) = |Ω_q|, extended multiplicatively as ρ(d) = ∏_{q|d} |Ω_q|. The proof states |r_d| ≤ ρ(d) ≤ 2^{ω(d)}, with ω the number of distinct prime factors, which is defined explicitly there and in Lemma 4.6. The application in Proposition 5.3 now writes ρ(q) ≤ q−1.

**R1.7 (accepted).**
- Theorem 9.1(a) now requires 0 < |q| < 1.
- Theorem 9.1(b) now requires weight k ≥ 1, followed by a sentence: a nonzero constant of weight 0 would be a counterexample, and (b) is used only in weight one.
- The §1.4 transcendence sentence now reads "of positive weight … with 0 < |q| < 1".
- The `VERIFICATION.md` paraphrase was updated to match.

**R1.8 (partly accepted).**
- **Accepted:**
  - Corollary 1.1 now reads "for each fixed 7/12 < a ≤ 1 … every window [N, N+⌈N^a⌉) with N ≥ N₀(w,a)".
  - The integer in Lemma 7.1 and in the proof of Theorem B is renamed ℓ, with a note that Lean calls it `L`, so D_N(L) unambiguously refers to the Lambert value.
  - Step 4 of `reviewer-packet.md` now excludes j = j₀ and primes dividing q₀.
  - The short announcement states N^a ≤ H ≤ N (267 characters).
  - The companion manuscript cited for the translation identity is H, which is in this tree (see "Coordinator items" below).
- **Not done:** the release-pin placeholder in `alphaxiv.md` stays a placeholder, because the release commit does not exist yet. It is an integration task.
- **Declined:** retiring the "unverified" note on Calude–Priese–Staiger. The cited URL returned HTTP 404 at revision, so I could not check the primary text, and the note and the ledger entry remain.

**Analytic checks in report 1 (no finding).**
- The referee's remarks on Huxley's role, Huxley–Iwaniec and the zero-density alternative require no change.
- The ledger now lists Campbell 2026 as a preprint ("submitted for publication"), not as a published result.
- The referee suggested Vandehey and Rivoal as further antecedents. I did not examine them; the ledger records them as "referee-suggested, not examined".

## Report 2 (Gemini 4 Argon)

| # | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| 1 | Committed PDF predates the byline update and lacks Author metadata | Minor | Accepted (same as R1.4) |
| 2 | Add `A23` to Crandall 2012; cite Crandall 2012 or Bailey–Crandall 2002 for the normality of E | Minor | Partly accepted |
| 3 | Reconcile the DNNS 1996 verification note | Minor | Accepted (marked unverified) |
| 4 | Cite Captain Sude's fe33be2 and Mira Cult's S06 gist in §1.4 | Minor | Accepted |
| 5 | Right-endpoint bound 5N in Lemma 3.2 for small N | Minor | Accepted |
| 6 | Add `lambert_head_eq_taylor` to the alphaXiv list | Editorial | Accepted |

**R2.1 (accepted).** See R1.4: the PDF was rebuilt and the Author field checked. `SHA256SUMS` is left to integration because this manuscript has no entry yet.

**R2.2 (partly accepted).**
- **Accepted:** the introduction now cites `BaileyCrandall2001`, the new `BaileyCrandall2002` (Experiment. Math. 11 (2002), no. 4, 527–546, §5, Conjecture 5.3 and Theorem 5.4; checked in the authors' posted text) and `Crandall2012` for the normality of E.
- **Declined:** adding the article number `A23` to `Crandall2012`. I could not confirm it from Crossref or the publisher page, which refused automated access. Crossref gives volume 12, issue 5, and `number = {5}` was added instead.

**R2.3 (accepted).** I could not read the full DNNS text (the Project Euclid page returned an empty body). The entry now carries `note = {unverified: metadata checked against the Crossref record; full text not examined}` and `number = {9}`. It is listed among the unverified entries in the `LEDGER.md` bibliography section, and the Theorem C ledger entry was updated to match. It is cited only as an aside.

**R2.4 (accepted).**
- §1.4 "Disjunctive nonnormal numbers" (l. 352) contrasts Captain Sude's Σ (b^{m^r} − 1)^{−1}, which has positive word frequencies, with the zero frequencies and D_N → 1 of our constants. New bibliography entry: `SudePower`, pinned at fe33be2.
- The Erdős–Borwein paragraph (l. 333) cites Mira Cult's 7 October 2026 gist, note S06 (revision 41b5a78), for the earlier prefix bound N exp(−C_w(log log N)² log log log N). New bibliography entry: `MiraGist`.

**R2.5 (accepted).** Lemma 3.2 (l. 494 ff.) now states that the right endpoint is at most 2N + 2s + H + B ≤ 5N once N is large in terms of s, that then H + B ≥ N^σ ≥ (5N)^{σ/2}, and that the remaining finitely many N contribute O_{σ,s}(1).

**R2.6 (accepted).** `lambert_head_eq_taylor` (WeightedLambertIdentities.lean L21) was added to `submission/alphaxiv.md` and to the reproduction list in `reviewer-packet.md`.

## Coordinator items

- **Translation identity.** Every citation of the synthetic-expansions manuscript for this identity has been replaced: in paper.tex (l. 203, Theorem 8.1 and the paragraph after it, §1.5, the §11 table), in `references.bib` (the entry `SyntheticCompanion` was removed and `DiscrepancyCompanion` added), and in `LEDGER.md`, `VERIFICATION.md` and `submission/{alphaxiv,summary,reviewer-packet}.md`. The new citation is C. Anderson, *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*, version 1.0, preprint, same release (manuscripts-v2.0.0), Theorem 3.1 (Theorem A in its introduction), with the Lean link `NormalityChecker.SharpTranslation.sharp_translation_isGreatest` pinned at e4809cf, L386. Corollary 1.2 remains this paper's own corollary.
- **Evidence labels** are unchanged for Theorems A, B and C and Corollaries 1.1 and 1.2. Theorem 10.3 is a new Paper proof.

## Verification of the revision

- **LaTeX build:** `wsl -d Ubuntu -- bash papers/wsl-build.sh 06-multiplicative-lambert` exits 0. The PDF has 21 pages, with no undefined references or citations and no overfull boxes. `pdfinfo` gives Author: Christopher Anderson and Title: Disjunctive but nonnormal multiplicative Lambert series.
- **Lean pins:** I extracted every `NormalityChecker/*.lean#L*` anchor in paper.tex, `VERIFICATION.md`, `LEDGER.md`, `references.bib` and `submission/*.md` (14 distinct anchors) and compared each with `git show e4809cf:<path>`. Every anchor lands on the named declaration or definition. `check_release.py --verify-pins` could not run here: Windows has no `pdfinfo`, and in WSL git could not read this worktree's objects.
- **Finite certificate:** `python -B scripts/phase17_multiplicative_lambert.py` passes, and its enclosures match §10.2.
- **Submission constraints:** `abstract.txt` has 248 words (limit 250); the X post has 267 characters (limit 280); `metadata.toml` parses.

## Questions reserved for a human specialist

1. **BBCP comparison.** Is the description of Bailey–Borwein–Crandall–Pomerance §9 complete and fair? In particular, has their isolated-coefficient argument (Lemma 9.5 and the set S_N) been extended elsewhere to arbitrary words, to short windows or to other multiplicative coefficient sequences, which would narrow the claimed additions further? Are the asymptotics for T_g(N) that they leave to Landau's formula routine?
2. **Kumchev input (Lemma 10.2, Theorem 10.3).** Does the printed theorem in Q. J. Math. 53 (2002) agree with the author's posted text quoted as Theorem 10.1? Is the implied constant in (1.8) independent of x and y? Is the single-modulus, single-length use of (1.10) legitimate? Is any fixed-progression lower bound known below exponent 0.53?
3. **Sieve step (Lemma 4.7 and Proposition 5.3).** The sieve has dimension 1+κ with lower cutoff z₀ = (log N)². Check the bound ∏_{q≤w}(1−g(q)) ≪ (log z₀)^κ/(log w)^{1+κ} and the count of the square-divisible exceptions, summed over O(log log N) offsets.
4. **Far tail with β < 1.** Check the divisor-sum reduction to Montgomery–Vaughan with d′ ≤ Y^β, including nonunit residues and the injectivity of d ↦ (gcd(d,b), d/gcd(d,b)).
5. **Theorem B lower bound.** Check the disjointness of the marked preceding starts and the balance of ε = 2^{−R}/4 against Δ.
6. **Theorem C, imprimitive case.** Check that Hamieh–Murty Theorem 3.1 applies to the weight-one form F on Γ₁(q_*P) with integral-power q-expansion.
7. **Unverified sources.** Check the primary texts of Chowla (1947), Duverney–Nishioka–Nishioka–Shiokawa (1996), Calude–Priese–Staiger (1997) and Luca–Tachiya (2014, full text). The last is the source of the claim that all real characters are covered.
8. **Priority.** Search MathSciNet and zbMATH for earlier word-count or discrepancy results for binary expansions of θ₃(q)² or of Lambert series with multiplicative coefficients.
