# Resolution of Referee Report 1 on Paper II, version 2.0

- Reviser model — Claude Sonnet 5.5 (Anthropic)
- Date — 25 November 2026
- Commit reviewed — `fe209690b9111f41e93571f8efaf40146a305b9e`, as named in the report; the revision starts from `22f50c782d21d5c40f55e0fb13255d37d4623184` (branch `publication/wave-2` after the merge of the report)
- AI model review and revision; not independent human peer review

The report is `papers/reviews/02-localized-normality-v2/review-1.md` (GPT-6.2 Sol). Locations below are in `papers/02-localized-normality-v2/paper.tex` after the revision; section numbers are those of the rebuilt PDF (18 pages). The report found no critical defect in Theorems A–F or in the nullity proof; nothing in the revision changes a theorem statement except that Theorem B is split into parts (i)–(iii) with the integral clause parenthesized, and Theorem F is stated for the sum over the integers `q^a p^j`. No Lean library file, `papers/common/`, `papers/0[1-5]-*`, the registry, the README or another manuscript was modified. `Statements.lean` and `Check.lean` were not edited. `AuditDeclarations.lean` was edited (finding 6).

| Finding | Disposition |
| --- | --- |
| 1. Qualify the abstract; repair the reviewer packet | Accepted |
| 2. Credit and narrow priority | Accepted; two reductions are recorded as adaptations that were not independently verified (Kano, Vandehey) |
| 3. Match labels to the exact statements | Accepted |
| 4. Repair the outline of Theorem F | Accepted |
| 5. Make older work traceable | Accepted |
| 6. Reproducibility | Partly accepted (the release links cannot be filled by the reviser) |
| 7. Terminology and placement | Accepted |

## 1. Qualify the abstract and repair the reviewer packet — accepted

- **Abstract** (paper.tex:16–18; `submission/abstract.txt`, now 249 words, `alphaxiv.md`, `summary.md`, `announcement.md` and the `abstract` key of `metadata.toml`). The joint assertion now assumes `J` nonempty on one common support; the polynomial classification says "over all of M(S)"; the window claim has the pole, a prime `p` in `J` and the retained windows `[p^k,2p^k)`; the common depth has the selected prime `p` in `J`. The credit of Captain Sude, Mira and Mira Cult and the scope of the extension (finding 2) are in the abstract itself and in the summary, post and forum paragraph.
- **Theorem B** (paper.tex:47–56). The report's reading ("or J is empty" as a separate sufficient condition) is removed: part (iii) reads "If `P` is in `Z[X]` and (`r >= s` or `J` is empty)". Part (ii) puts "for every restriction `A`" before the integer `L`, matching `rational_boundary`, and states the written strengthening `L = D_0`, independent of `A`.
- **Proof of the lower bound and integral clause** (Section 5, paper.tex:214–223). Split into the case `r >= s` (the cleared weight `m^{r-s}G(m)` is an integer) and the case `J` empty (the weight need not be an integer, e.g. `1/m` for `P = 1`, `s = 1`, `b = 2`, `S = {2}`; old radix shifts clear `D_b m^s`). The proof of the failing cases is no longer described as "the kernel-verified one".
- **Reviewer packet** (`submission/reviewer-packet.md`, rewritten). Step 3 retains the ray prime `r` and differences only over the other cofactor primes, with a remark on why `A(r^l) = w^{r^l}` fails otherwise; Step 5 is split into the two cases above; the packet now states the liminf bound and the integral clause (and says it is an excerpt); Step 1 fixes the finitely many test frequencies, then `Q_0`, then `N_0`; Step 2 distinguishes the written valuation step from the kernel-verified inequality `discrepancy_le_certificate`; the evidence section no longer says that `PaperII.polynomialClassification` covers B(ii)–(iii).
- **Inquiry drafts** (`submission/reviewer-inquiry.md`): the second draft now carries the Kano/Vandehey comparison of finding 2, and both are marked as not to be sent before the packet and links are final.

## 2. Credit and narrow the priority claims — accepted, with qualifications

- **Public abstracts.** Credit is in the abstract, `alphaxiv.md` (verification scope), `summary.md`, `announcement.md`.
- **Section 1.2** (paper.tex:95–118, rewritten). It now separates what a source *states* from what follows from its *proof by an adaptation*, and says that the adaptations are our deductions. The "do not state" list (a)–(f) is replaced by "What follows from the proofs of these sources" (paper.tex:104–110, items (1)–(3)) and "Our contribution relative to these sources" (paper.tex:114), narrowed as follows: (a) order one on supports with at least three primes whose least prime divides `b`, other than `b = 2` with `3` in `S`; (c) orders `s >= 2` outside the adaptations; (d), (e), (f) restricted to what is not obtained from Mira's theorem on singleton supports, from the periodic-array theorem of October S07, or from Kano's and Vandehey's theorems.
- **The three concrete omissions.** (1) Least prime off the radix, any order, polynomial pole: I read the pinned proofs (Sude `xi-normality`, proof of Theorem 5.1 (1) and the binary case; Mira Cult, proof of Theorem 2) on 25 November 2026 and agree that only `p = min S` off the radix is used, the other radix primes being cleared as in Sude's binary mixed case. (2) Binary with `3` in `S` for all `s`: I recomputed `2^{-3^k} -> -1` in `Z_3`, the limit `-1 + 2^{-s}` and its valuation `0` (odd `s`) or `1 + v_3(s/2) < s` (even `s`), by lifting the exponent. (3) The `xi-family` slope argument at higher orders: recorded as the report states it; I read the proof of Lemma 4 and found its structure compatible, but did not carry out the adaptation. The singleton-support perturbation argument (Theorem B sufficiency and C(i) via Mira's Theorem 1) and the periodic-array case of C(ii) via October S07 Theorem 9.1 are stated in paper.tex:112 as deductions, from the report; I did not re-derive the rank computation in October S07.
- **Qualification on Kano and Vandehey** (paper.tex:98). The report reads Kano's Theorem 1 (p. 911) as allowing signed integer numerators with `|A_j| << p^{lambda_j}`, `p^{lambda_j - lambda_{j-1}}` not dividing `A_j` and `p^{lambda_j} << mu_j`. The only copy I could open is an OCR text in which these displayed hypotheses are garbled, so I did not confirm them. The paper therefore states that Theorem 1 allows signed integer numerators "under growth and divisibility conditions", describes the reduction (with `mu_j = p^{k_j}`, `lambda_j = k_j` minus the numerator valuation), and says "subject to a check of its hypotheses that we have not carried out in detail". For Vandehey, Theorem 7.4 is stated for unit numerators and the adaptation to signed polynomial numerators at orders `s >= 2` is marked as not carried out. This is a partial acceptance of that bullet: the credit is given, the exact hypotheses remain for a specialist (see the closing list).
- **Ledger** (`LEDGER.md`): new section "Exact statements versus extensions of their proofs"; September S07/T29 and October S07 are named separately; Theorem A–F entries updated; the referee's search record is added.

## 3. Match the verification labels to the exact statements — accepted

I checked every cited declaration at `e4809cf` with `git show` (all 46 distinct pins in the paper and the 47 in the verification map resolve to the stated line and name). Changes:

- **Section 12** (paper.tex:334–337). Kernel-verified now means one Lean declaration (library or `Check.lean`); a Lean-supported paper proof names the declarations and states the written combining step. The paragraph on `Statements.lean`/`Check.lean` says that they restate only the limit statement and normality for `J` nonempty of Theorem A, the equivalence of Theorem B(i) and Theorem C(i), and not B(ii)–(iii) or C(ii)–(iii); it says that they are run from the release (the bare checkpoint omits them). `alphaxiv.md` "Verification scope" is rewritten likewise.
- **Theorem E** (paper.tex:85–90). `exists_common_depth` (existence), `certificateModulus` = `Nat.find` (least depth), `certificateModulus_spec` (all finer depths): Kernel-verified. The final `Dinf(X_s) < eps` needs `discrepancy_le_certificate`: relabelled Lean-supported paper proof, with the chain written.
- **Theorem D** (paper.tex:69–83). The cancellation identity (equation (2)) `X_A(P,s) = X_A(Q,t)` is stated and tied to `masked_cancel`. D(ii)'s first display is `rational_pole_bound` (Kernel-verified); the two consequences use `late_powers_discrepancy`, `normal_of_late_twos` and D(iii) uses `axis_normal_iff`, which are stated for `Q(0) != 0` and `t > 0`, so these are relabelled Lean-supported paper proofs whose only written step is the rewriting. D(i) keeps its label.
- **Theorem F** (paper.tex:91–93). Stated for the sum over the integers `q^a p^j`, which is `Localized.value`; cites `discrepancy_rate`, `series_normal` (displayed double series) and `value_eq_series`. Kept Kernel-verified; the three declarations cover the normality and the rate with the identity stated.
- **Remark 6.2** (paper.tex:252–254). `quotient_window_bound` assumes an eventual implication and a count of bad positions; the passage to `1 - g` is the density deduction of D(i). Relabelled Lean-supported paper proof.
- **Example 11.2** (paper.tex:329–332). The four kernel facts are listed (`Nat.log 7 186 = 2`; membership of `186` in the failed cells of depth `2` for `{2,3}`; `m + 16 <= 186` for every smooth index; denominator `7`). The row residues, the 38 terms, the largest index `168`, the age `18` and the residue `4*7^3 mod 7^4` are labelled Finite certificate and reproduced by the new `check_order_two.py` (output `38, 168, 18, 49, 294, 0, 1372`).
- **Other labels** made explicit per assertion: Theorem B (i)–(iii), Theorem 11.1 (one declaration per assertion), Table 1 rows, `VERIFICATION.md` (rewritten, one row per numbered result, including the renumbered Section 11 results).
- **Lemma 3.1, Theorem C, Theorem 4.1, Proposition 6.3, Example 5.1, Corollary 6.1**: statements and labels were checked against the pinned declarations and left unchanged.

## 4. Repair or shorten the outline of Theorem F — accepted

The outline (paper.tex:292–302) is rewritten. It now states: at most one index per layer `j` enters `(s,t]` for `s < t <= qs`; the inserted terms have pairwise different `p`-adic absolute values and the difference has the absolute value of the inserted term with the **largest** `j` (not of an arbitrary top-layer term); bad block starts cannot straddle a threshold in the protected layers, which gives a **diameter** bound for them, explicitly not a statement that the set losing a fixed number of layers has vanishing relative size; Dirichlet returns of size at most `log q/(M+1)` together with `|p^i - q^a| >= 1` give the step lower bound `1/(q p^M)` and the mesh depth `M q^2 p^M` (`effective_threshold_mesh`); blocks of length `K^5` on the `K^6` scale, removal of insertion blocks and bad blocks, the incomplete-orbit estimate for prime powers (`stoneham_orbit_small`, `stoneham_order_bound`), smoothing (`interval_count_bound`), the threshold `k >= R^{M+1}` and geometric summation giving `A/log log N` at every prefix. The separate "Paper proof" label is removed; the text says it describes the structure of a kernel-verified proof. I checked each step against `notes/mixed-localized-logarithms.md` at the pin and the Lean statements; I did not need to downgrade Theorem F. The outline remains an outline, not a complete proof.

## 5. Make the older work traceable — accepted

- `references.bib`: the six `url` fields are now printed through `note` (BibTeX `plain` drops `url`); the Sude entries point to the `.tex` files that were read. Verified in the rebuilt bibliography.
- Xi-family Theorem 2 (rational combinations, `a` and `b` fixed) is cited; the role of Lemma 4 (bounded-row separation for periodic weights, up to a finite set of exponent differences) is acknowledged and the "cannot be varied" sentence is replaced by the identity `F(1/b) - p^{-1}F(b^{-p}) = 1/b` (paper.tex:102, 112).
- Sude's Stoneham criterion: "arbitrary `c`, in particular composite `c`", with the zero-digit-frequency observation giving `D_N -> 1` on the singleton all-radix case (paper.tex:98).

## 6. Make source checking reproducible — partly accepted

- Accepted: Vandehey is cited as arXiv:1606.07911v1, Corollary 1.2, pp. 2–3, with journal metadata distinguished from the edition used (paper.tex:142; `references.bib`; `VERIFICATION.md`; `LEDGER.md`). The reproduction paragraph says to run the statement files from the release with a compatible library build.
- Accepted and tested: `AuditDeclarations.lean` throws on a missing declaration or an unexpected axiom and now audits 42 declarations (it adds `value_eq_series` and `series_normal`; the earlier text in `VERIFICATION.md` said 41, which miscounted the file's 40). I ran it against the oleans of `~/wave2-verify/repo`: exit status 0 with 42 `OK` lines; on a copy with a nonexistent name added, exit status 1 with "missing declaration".
- Not done: "fill in the submission's release links". The release tag and URL do not exist yet. `alphaxiv.md` now has an explicit marker "RELEASE LINK: to be added by the owner before this packet is distributed", and the inquiry drafts keep `[link]`.

## 7. Tighten terminology and placement — accepted

- Weyl (paper.tex:269): now applied to the vector `({b^n Y_i})_i`, with the box indicator bracketed between products of one-dimensional continuous functions.
- "Recorded there" and vague repository references: the paragraph in Section 10 about unrelated repository notes is removed from the paper and recorded in `VERIFICATION.md`; the Section 11 sentence now points to Appendix A of version 1.1 (Theorem A.1, Lemma A.2, Corollary A.3) with the file path.
- Placement: the former Appendix A is now Section 11 (paper.tex:316–332), before "Formal verification and data availability" (Section 12) and "Use of AI tools" (Section 13), so that these two end the paper. Consequences: Theorem A.1 is now Theorem 11.1 and Example A.2 is Example 11.2; `CHANGES.md` and `VERIFICATION.md` record the renumbering.
- Announcement: the short post and forum paragraph name the overlap and the extensions instead of an unqualified lead.

## Points in the report that are not numbered findings

- The "Independent mathematical checks" confirm the intended statements and proofs; they ask for no change.
- Keep September S07 and October S07 identifiable in the ledger: done.
- Dibag's Definitions 1.1–1.2: the report could not access the original; the ledger records this as still to be checked independently. I did not change the citation.
- Phase 19: no Phase 19 declaration is used; Lean pins remain at `e4809cf`.

## Verification of this revision

- LaTeX build (`wsl -d Ubuntu -- bash papers/wsl-build.sh 02-localized-normality-v2`): exit status 0, no undefined references or citations, no overfull boxes; 18 pages (15 before the revision, which added the rewritten related-work, rate-outline and verification text); PDF author "Christopher Anderson".
- `python papers/02-localized-normality-v2/check_order_two.py`: reproduces the Example 11.2 arithmetic.
- `AuditDeclarations.lean`: as in finding 6.
- All 46 distinct `\decl` pins of the paper were re-checked against `git show e4809cf` (name on the stated line).
- Not run in this revision: `Check.lean` and `check.sh` (unchanged files), `scripts/localized_certificate.py`, and `papers/check_release.py --verify-pins` (needs Poppler `pdfinfo` on the Windows path; the plain `check_release.py` reports that `SHA256SUMS` differs from the manuscript PDFs, for the extra v2 PDFs; the five archived PDFs still match `SHA256SUMS`).

## Questions still reserved for a human specialist

1. The recurrence and finite-monoid differencing step of Theorem 4.1 (return time as a multiple of the eventual period, including `q_j | p-1` and `p = 2`), the survival of the bare ray, and the separation restricted to rows at bounded distance.
2. Whether Vandehey's Corollary 1.2 applies exactly as used in Lemma 2.1 (block length `B`, reduced denominators between a large threshold and `B^C`, numerators arbitrary after multiplication by `h`), and whether Bourgain's estimate could replace it.
3. The adaptation claims of Section 1.2: items (1)–(3) (least prime off the radix; binary with `3` at all orders; `xi-family` Lemma 4 at higher orders), the perturbation argument for singleton supports, and the rank computation for periodic common masks via October S07 Theorem 9.1.
4. The exact hypotheses of Kano's Theorem 1 at p. 911, whether the reduction of the order-one signed axis case holds as described, and whether Vandehey's proof of Theorem 7.4 adapts to signed polynomial numerators at orders `s >= 2`.
5. Priority: whether any earlier result for three or more generators whose least prime divides the radix (or for orders `s >= 2` on such supports) implies Theorem A; the zbMATH Open and MathSciNet searches the reviser could not run; Google Scholar.
6. The correspondence of the library definitions (`maskedValue`, `radixDiscrepancy`, `NormalIn`, `JointUniform`) with the displayed series and frequencies, beyond the three mathlib-only restatements.
7. Dibag's Definitions 1.1–1.2, and the version-of-record numbering of Vandehey's Corollary 1.2 and Theorem 7.4.
8. The outline of Theorem F against the Lean proof, in particular the constants `R` and the passage from `1/(M+1)` to `A/log log N`.
