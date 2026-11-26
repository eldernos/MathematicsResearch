# Resolution of Referee Report 1 on Paper V, version 2.0 (*Denominator Growth and Rational Shadowing for Classical Constants*)

- **Reviser model:** Claude Sonnet 5.5 (`claude-sonnet-5-5`), Anthropic
- **Date:** 25 November 2026
- **Commit reviewed:** `e0c222a17ed7b44bdbd726e56022b1534a4935ec`, as named in `review-1.md`. The revision starts from `f65b1c745a5fee8dfef858f95a47024b1ca5d158` (branch `publication/wave-2` at the start of the task, worktree branch `t3/revise-classical-denominators`).
- **Status:** **AI model review and revision; not independent human peer review.**

The report is `papers/reviews/05-classical-denominators-v2/review-1.md` (Claude Sonnet 5.5; verdict: accept after major revision; no critical finding; 3 major, 12 minor and 5 editorial, 20 findings in all). Locations below refer to the revised `papers/05-classical-denominators-v2/paper.tex` and its rebuilt PDF (28 pages, up from 22; no undefined references or citations; PDF author `Christopher Anderson`). The revision keeps one manuscript, as instructed. No Lean file, `papers/common/`, `papers/0[1-5]-*`, registry, README or other manuscript was modified, and the `\bibliographystyle` line is unchanged.

Section numbering changed in two places. The former Theorem 4.1 is now Theorem 4.1 (rate) plus Proposition 4.2 (thresholds), so the former Propositions 4.2 and 4.3 are now 4.3 and 4.4. A new Remark 5.4 shifts the former Proposition 5.4 to 5.5. `VERIFICATION.md` (24 rows), `LEDGER.md`, `CHANGES.md`, `metadata.toml` and `submission/` were updated to match.

| # | Severity | Finding | Disposition |
| --- | --- | --- | --- |
| 1 | Major | Windows and exponents are nearest-grid rounding compared with an incomparable class | Accepted, with one correction to the proposed fix |
| 2 | Major | Missing antecedents | Accepted; verification is partial and marked |
| 3 | Major | Length and form; compressed proofs | Partly accepted (no split into several papers, as instructed) |
| 4 | Minor | "Shadowing" and "window" undefined | Accepted; title kept |
| 5 | Minor | Theorem 4.1 label | Accepted |
| 6 | Minor | Theorem 8.2 label | Accepted |
| 7 | Minor | Unverifiable or misplaced citations | Partly accepted |
| 8 | Minor | Redundant positivity check in Theorem 2.2 | Accepted |
| 9 | Minor | Repository vocabulary | Accepted |
| 10 | Minor | X post | Accepted |
| 11 | Minor | Corrupted characters in `VERIFICATION.md` | Accepted |
| 12 | Minor | Theorem 5.2 label | Accepted |
| 13 | Minor | Ray uniformity versus scope | Accepted |
| 14 | Minor | No conclusion section | Accepted |
| 15 | Minor | Abstracts differ between files | Accepted |
| 16 | Editorial | Line 346 unparseable | Accepted |
| 17 | Editorial | Line 399 unclear | Accepted |
| 18 | Editorial | Section 7 title | Accepted |
| 19 | Editorial | Introduction ordering | Accepted |
| 20 | Editorial | Proposition 7.1 sign hypothesis | Accepted |

## Major findings

### 1. Windows and exponents are nearest-grid rounding — accepted, with a correction
- **Changes.**
  - Abstract: the "smaller denominator exponents" sentence is replaced by the statement that Part II rounds polynomial moments on the grid (1/lcm(1,…,D))ℤ, that the windows have length at least log₂ of the grid denominator up to o(1), that this is the benchmark for every real number, and that these windows are not compared with the floors.
  - §1, paragraph "Rounded models and windows": defines the window, states that the models are nearest-grid roundings, that grid exponents and slopes record the choice of grid, and that the floors 5/12, 13/30, 1/2 concern truncation without rounding.
  - New Remark 5.4 (after Theorem 5.3): defines the excess window G_N = T_N − log₂ q_N, shows that every real number has a nearest-grid model with G_N ≥ 1 (and, with q = N+1, exponential rate 0 with error ≤ 1/(2N+2)), says what §5 does establish (integer polynomial realization with D ≈ N/log₂ρ, crossing degree, identification test), and states that Theorem 5.3 proves G_N ≥ 1 − o(1) and no upper bound.
  - §5 opening sentence labels the section a construction of explicit moments and of a test. Theorem 5.3 carries a pointer to Remark 5.4. The example paragraph now says "grid exponents" and that they are not compared with 5/12.
  - The sentence "every real target has a nearest point on any rational grid" stays in Remark 6.2 with a pointer to Remark 5.4. §6 and §10 restate the point.
  - Title not renamed; "rational shadowing" is defined at first use (item 4).
- **Correction to the proposed fix.** The report proposes that the paper proves G_N = O(1) for these models. That is not what Theorem 5.3 gives. It gives q_N | L_D and error ≤ (2L_D)⁻¹ + o(1/L_D), hence T_N ≥ log₂ L_D + 1 − o(1) and G_N ≥ 1 − o(1). Without a control on gcd(numerator, L_D), the reduced denominator may be much smaller than L_D, and G_N could then be large. Remark 5.4 therefore states the lower bound, says that no upper bound is proved, and records the unbounded excess window as the kind of result that would be new (open question 2 in §10).
- **Rivoal comparison.** Added in §1 with precise statements (item 2).

### 2. Missing antecedents — accepted; verification partial
- **Changes.** New bibliography entries `bbg`, `storm`, `todd`, `boyd`, `el`, `shiu`, `rogers`, `bris`. §1 paragraph "Antecedents" and §2 (Bang's theorem sentence) use them; the ledger is rewritten accordingly (entries A, 4.1–4.4, 5.1–5.2, 5.3–5.5, 8.2, 9.1–9.2 and "Bibliographic access").
- **Borwein–Borwein–Galway (Canad. J. Math. 56, 2004, 897–925).** Read in full from the publisher's PDF. Verified: abstract; Theorem 3 (Bang's theorem for b^m − 1), p. 913; Theorem 4 (no non-Aurifeuillian binary Machin-type formula for ln 23 or ln 89, by a valuation descent at a primitive prime of 2¹¹ − 1), p. 914; Theorem 7 (no b-ary Machin-type arctangent formula for π, b > 2), p. 918; Theorems 1 and 2 (exclusion criteria by Gaussian primes). The descent in Theorem 4 is the same device as the descent in our Theorem 2.2. The paper now says so, and says what is different: BBG treat exact identities, and neither truncation at a cutoff, nor reduced denominators, nor rates. The ledger relation line for entry A is rewritten to say this and to say that we have not located the all-cutoff reduction there.
- **Størmer 1896 and Todd 1949.** Cited in §1. **Not read.** Bibliographic data come from reference list entries [16] and [20] of Kroesche–Littlejohn–Reinhart, arXiv:2511.03030, which also describes the Z[i] method and Todd's Theorems A and B. Both bib entries carry `note = {unverified…}` and appear in the ledger as unverified. The Størmer/Todd description in the paper is limited to what BBG §2.1 states.
- **Harmonic-number p-adic literature.** Shiu (arXiv:1607.02863v2; Theorem 2 read in the arXiv HTML, no page numbers there) states the band structure m p^a ≤ n < (m+1)p^a. Rogers (arXiv:0708.2439; Definition 2.1 and Theorem 2.3 read) defines J_p(y) for y = 1, …, p−1, which contains the residue y ≡ 2⁻¹ that gives our weighted sums. Eswarathasan–Levine (data from Crossref and Shiu's reference list) and Boyd (abstract only) are cited for the unweighted case. §1 and the ledger now credit the prime-band formula of Proposition 2.1 as the weighted analogue of this mechanism. In Proposition 9.2 the sentence "the weighted counterpart of Sanna's short-range bound" is kept, and Rogers is added in the ledger and the verification map as the study of the weighted zero sets.
- **Rivoal.** §1 now states his Theorems 1, 3 and 4 precisely (read from the EMS PDF): lower bounds for |log(1 − a/b) − u/(d_m^s (bc)^m)|, 0 < |a/b| < 1, s ∈ {0,1}; consequences for convergents. It compares denominators: ours are 2^N L_D with independent indices, his share one index m, and log 2 is the boundary case a/b = −1, which he does not cover (his Remark 1 attributes a bound for log 2 with denominators d_m to Dubitskas, which we did not read and do not cite).
- **Brisebarre 2001.** Cited in §1 with the abstract-level description only (a class of polynomials generalizing the Legendre polynomials). **Abstract only.** Alladi–Robinson was already cited.
- **Not adopted.** The report asks in item 7.1 whether de la Vallée Poussin should also be cited for progressions. See item 7.
- **Open for a human specialist.** Whether Størmer, Todd or the BBG exclusion argument contain a statement equivalent to Theorem 2.2 or 3.1, and whether a Rivoal-type result already gives the prescribed-shift moment grid. Both are listed in §10 and below.

### 3. Length and form — partly accepted
- **Accepted.** Parts I, II and III are marked (`\partmark`) before §2, §5 and §7. §1 has an "Organization" paragraph. A new §10 "Scope and open questions" precedes the verification section (see item 14). The proofs the report names are expanded:
  - **Theorem 3.1** (§3): five labelled steps — the Kummer/Galois computation of s, the radius reduction to g(X^r), the formal identity Θ_x(ρ_n Φ), the case h even, and the case h odd, with the subcases 8 ∤ M (including 4 ∥ M and M = m or 2m), 16 | M, and M = 8m. The involution τ ↦ τ + (M/2)·1[τ ≡ ±3 (8)] is shown to preserve units (τ + M/2 stays odd and keeps its residues modulo the odd primes of M) and the class modulo 8 (8 | M/2), so it is a bijection.
  - **Proposition 7.2** (§7): the four BBP slots, the three Bellard slot families, their ranges, congruences and absolute-sum bounds, the nonvanishing at j = 1, the exceptional-prime and range arguments, and the PNT-in-progressions count.
  - **Theorem 8.2** (§8): six steps — the fresh-prime recursion and its disjointness and exhaustion, the BBP version with primes of u⁴ + 1, the shifted-prefix structure and denominator valuations, the shell and block decomposition, the Fourier estimate with the exact quantifier structure of the Lean statement, and Weyl's criterion with the dilation argument.
  - **Theorem 9.5** (§9): six steps — finite grids and the O(N⁻²) tail, the mean-distance criterion (both directions), the dyadic classification with plateaus, the individual-row recursion and the measures μ_{j,v}, the discrepancy of a grid law and the affine-in-v argument, and the full d = 3 and d = 5 calculations.
- **Not adopted.** The report's split into two papers and a note was not made, because the task is to revise this manuscript and not to create new ones. The proofs were kept in the text rather than moved to an appendix, and §§7–9 stay in the body as Part III. The page count rose from 22 to 28.
- **Dropped, partly accepted.** The report suggests dropping the e, √2 and φ continued-fraction material. I dropped only the paragraph with the series √(1+4x) at x = 2⁻⁵, 2⁻⁴ (used nowhere else, no verification row). The continued-fraction and Pell paragraphs and the Lean-pinned golden-ratio criterion stay, since the scope remark about the five constants relies on them.

## Minor findings

### 4. "Shadowing" and "window" undefined — accepted; title kept
§1 defines window (largest j with 2^j|2^N ξ − Y_N| ≤ η, the number of binary digits after position N reproduced by the model) and says that "rational shadowing" means only this and says nothing about digits beyond the window; the scope sentence is in the adjacent paragraph. The abstract defines window in one clause. §5 retains the formal definition and T_N. I did not rename the paper, because the title is shared with `metadata.toml`, the portal and the submission files and the first-use definition removes the ambiguity.

### 5. Theorem 4.1 label — accepted
Split into Theorem 4.1 (the rate statement, Lean-supported paper proof, as before) and Proposition 4.2 (the four linear thresholds), labelled **Finite certificate**, with the statement that Python, not Lean, performs the enumeration and that the reduction of the asymptotic statement to the enumeration is the written argument that follows. `VERIFICATION.md` row 4.2 and the ledger give the script and its output (730 nodes at 13/30; 484 at 5/12).

### 6. Theorem 8.2 label — accepted
Relabelled **Paper proof**. The text after the statement says that one Lean-checked estimate supports Step 5 (`fixed_support_orbit_estimate`; the Lean predicate `SmoothOrbitEstimate b c` has exactly the quantifier structure used there: coprime b, c > 1, any d and η, y with den(y) ≥ M₀ and den(y) dividing a power of c, den(y) ≤ T^d) and that `hasSum_prime_rays_logTwo` is a different fixed-prime identity not used in the proof. `VERIFICATION.md` row 8.2 says the same.

### 7. Citations — partly accepted
1. **Hadamard.** Checked in the optical-character layer of the Numdam scan: §19, pp. 218–219, states that the sum of the logarithms of the primes below x in an arithmetic progression of modulus k is asymptotic to x/φ(k) (the OCR garbles the denominator but the sentence is readable), and that it "comprend" the case k = 1. The locator is now "§19, p. 219". De la Vallée Poussin 1896 was **not** added: the cited statement is in Hadamard, and I did not examine the other memoir.
2. **Takahashi.** The equation numbers "(11)–(19)" are removed from Proposition 7.1. The classical identities are credited to Machin (1706) and Størmer with a pointer to BBG §2.1, and Takahashi stays only as a pointer to their use in digit extraction.
3. **Bang.** The bib entry carries `note = {unverified…}`, and §2 says Bang's article was not read; the statement is also Zsigmondy's and BBG's Theorem 3, p. 913.
4. **Mira Cult.** The bib entry now reads "unrefereed, AI-assisted public note, cited by commit 357d26a" with no date. Theorem 1 is as the paper says (confirmed by reading the note), and the note's own disclaimers (no priority claim, not a formal verification, OpenAI models assisted) are recorded in the ledger.
5. **Bailey–Crandall 2002.** Corollary 4.9(i) checked in the author manuscript with journal pagination: it says that the generalized Stoneham numbers Σ 1/(c^{n_i} b^{c^i}) are b-normal; it is on p. 536. The locator is added.

### 8. Theorem 2.2 positivity check — accepted
The sentence "direct summation on 8 ≤ v < 18" is removed. The proof now says that the Lean masses 7/18 and 73/180 concern cells 1 ≤ v ≤ 71, that beyond them only S_θ(x) ≠ 0 for x ≥ 36 is needed (the cells v ≥ 72 have total mass 1/36), and that |S(x) − log 2| ≤ 4C·2^{−x} with C = 34, 16 gives 4·34·2⁻⁹ < 0.27 < log 2, so S_θ(x) ≠ 0 for x ≥ 9.

### 9. Repository vocabulary — accepted
"Prefix function" is defined in §1 (the map x ↦ S(x)). "Cell v" is defined in §2 after Proposition 2.1 (the band 2N/(v+1) < p ≤ 2N/v, normalized weight m_v = 2/(v(v+1)), occupied when S(v/2) ≠ 0), and "half-cell", "M₇₁" and "pays its mass" are replaced. "The verification material" is replaced by a reference to `scripts/phase16_adaptive_log.py` in Proposition 4.2. §11 describes the checkpoint by its SHA and purpose ("research-checkpoint-18, commit e4809cf…, the repository state at which the Lean declarations were checked") and the follow-up checkpoint by its SHA.

### 10. X post — accepted
`submission/announcement.md` now reads (272 characters): "A preprint shows that, among fixed truncated identities for ln 2 built from balanced traces, reduced denominators grow at rates at least 5/12 (next 13/30). A second part rounds polynomial moments to nearest grid points. Digits, normality and discrepancy of ln 2 stay open." The forum paragraph is rewritten to say the floors concern truncation without rounding and that the rounded models are nearest-grid roundings.

### 11. Corrupted characters — accepted
Restored in `VERIFICATION.md` (former lines 33, 40–42, 77, 79): 1 ≤ v ≤ 71, (0,0,0,−5) and (0,0,0,−2), 2^k − 1, n ≥ 7, O(√x log x), and the π errors 2^(−261) and 2^(−213). No other "?" remains outside URLs. Line 64 of `LEDGER.md` contains a question mark that is part of the Sondow–Schalm title and was left.

### 12. Theorem 5.2 label — accepted
The label stays Lean-supported, with an added line stating that Lean checks only the divisibility of the polynomial moment and the rounding-error bound, and that the first crossing, the exponent, the floor D⁻² and the PNT input are written proofs. `VERIFICATION.md` row 5.2 and the ledger say the same.

### 13. Ray uniformity versus scope — accepted
The scope paragraph of §1 and Remark 6.2 now say that the ray components of Theorem 8.2 are jointly uniform, that their sum (log 2 or π) is not covered, and that the explicit example after Theorem 8.2 shows that uniformity of finitely many components does not pass to an infinite sum. §10 repeats it.

### 14. No conclusion — accepted
New §10 "Scope and open questions": what is proved, what is not proved (with the scope sentence), six open questions, and the review status. The verification and AI-use sections follow it.

### 15. Abstracts differ — accepted
One abstract (247 words in plain text) is now used in `paper.tex`, `metadata.toml`, `submission/abstract.txt` and the abstract section of `submission/alphaxiv.md`. It no longer contains "exhibit failure of the rate floor" or "construct large-height identities", and uses "identities of larger height below the floor".

## Editorial findings

### 16. Line 346 — accepted
§6 now names Vandehey's two hypotheses: the denominator of y is supported on a fixed finite set of primes not dividing b, and the length T is at least a fixed power of that denominator. It explains that the Legendre reduced denominators divide L_D, whose support contains every prime up to D.

### 17. Line 399 — accepted
Replaced: with N = ⌊2 log₂ q⌋ the model 2^N p/q has reduced log-denominator at most (½ log 2 + o(1))N and shifted error 2^N|ξ − p/q| = O(1), so its window at every tolerance η < 1 is bounded.

### 18. Section 7 title — accepted
Retitled "Arctangents, digit-extraction series and factorial truncations".

### 19. Introduction ordering — accepted
The definition of balanced sources now states that all roots have the same radius so every term is cut off at the same binary scale, and points to Remark 3.2 (the unbalanced remark) for why the balanced class is the natural one.

### 20. Proposition 7.1 — accepted
The statement notes "(the positivity is used below)" and the proof says that a, c > 0 makes aB₂ + cB₃ a sum of positive terms and that mixed signs could cancel.

## Phase 19 items

Kept with their exact labels, in §9 and unchanged in statement: the horizontal Taylor rows and their discrepancy spectra (Theorem 9.5, Paper proof; row 3 gives 2/3 and 2/3, row 5 gives 1/5 and 8/15), the deterministic remainder classification for finite combinations of rows (the same theorem, with a finite rational grid support and the dyadic criterion), the exact earliest completion p·k(p) (Proposition 9.1, Paper proof), and the superpolynomial multiplicative-order obstruction (Theorem 9.3, Paper proof, with Proposition 9.4). The closing paragraph of §9 keeps the distinction between classifying individual summands and classifying the full logarithm, and §10 repeats it.

## What I checked, and what I did not

- **Pins.** All 14 Lean anchors resolve at `e4809cf561573aef588e6ffc491a35cdb79fd9ec` to the named declarations: the 12 in `paper.tex` (`dyadicRe_eq` 55, `insertion_iff` 66, `gaussian_re_frobenius` 85, `norm_valuation_system` 122, `global_cell_mass_bound` 1158, `minimizer_mass71` 1210, `runnerup_mass71` 1220, `shifted_poly_integral_den_dvd` 73, `rounding_integral_error` 94, `golden_discrepancy_iff_small_index` 190, `hasSum_prime_rays_logTwo` 32, `fixed_support_orbit_estimate` 207) and the 2 in `VERIFICATION.md` (`LogarithmBands.denominator_rate` 89, `DyadicRelations.optimal_rate` 94). `papers/check_release.py` pin validation of the PDF annotations reports no errors. The full `check_release.py` run stops at the aggregate `papers/SHA256SUMS`, which is maintained at release assembly (this is expected and is noted in `VERIFICATION.md`).
- **Build.** `wsl -d Ubuntu -- bash papers/wsl-build.sh 05-classical-denominators-v2` exits 0: 28 pages, no undefined references or citations, PDF Title and Author set (Author: Christopher Anderson). I inspected the rendered pages for the abstract, Theorem 3.1, Proposition 7.2 and Theorem 9.5.
- **Mathematics.** I re-derived by hand every expanded step above, including the d = 3 and d = 5 cycles, the weight table [1/15, 8/15] and the discrepancy max(w, 2/5 − w). I ran `phase19_horizontal.py` from the pinned object (row 3: 2/3, 2/3; row 5: 1/5, 8/15). As a new independent check of the slot analysis in Proposition 7.2 I computed the exact BBP prefixes for M = 100, 200 and Bellard prefixes for M = 100, 200 and compared the set of odd primes above 0.1 N dividing the reduced denominator with the predicted ranges. There was no discrepancy in either direction, and log q/N = 1.4737, 1.4634 (BBP) and 0.9954, 0.9952 (Bellard). I did not rerun `phase16_adaptive_log.py`, `phase17_classical_approximants.py`, `phase18_classical.py` or any Lean build. The numbers quoted in Proposition 4.2 are those of the report's rerun.
- **Literature.** See items 2 and 7 and the lists in `VERIFICATION.md` and `LEDGER.md`. Not read at the source: Bang, Størmer, Todd, Eswarathasan–Levine, Boyd (abstract only), Brisebarre (abstract only), Dubitskas.

## Questions reserved for a human specialist

1. **Theorem 3.1.** Is the phase-orbit computation correct in every case, in particular the 2-adic twist at 16 | M, the M = 8m case with g_± · P_m, and the claim that the Kummer group has order r = e (odd e) or e/2 (even e)?
2. **Theorem 2.2.** Is the largest-height descent sufficient when one height is occupied by both a real stride and a Gaussian index, and does it follow from, or differ from, the exclusion arguments of Borwein–Borwein–Galway §3 or of Størmer and Todd?
3. **Antecedents.** Do Størmer, Todd, Borwein–Borwein–Galway or the Machin-type literature already contain an all-cutoff reduction of balanced traces to the sources A_k and G_t? Does a restricted-denominator Padé result in the line of Rivoal, Dubitskas, Brisebarre, Hata or Marcovecchio already give the integer-polynomial realization of the nearest grid point to 2^N log 2 or 2^N π with the multiplier prescribed independently of the degree?
4. **Windows.** Do Rivoal's Theorem 4 or the Dubitskas bound limit the excess window G_N for log 2 itself along the diagonal, and is the reduced denominator of the Legendre models equal to L_D up to a bounded factor?
5. **Primary texts.** Bang (1886), Størmer (1896), Todd (1949), Eswarathasan–Levine (1991) and the full Boyd (1994) and Brisebarre (2001) papers could not be read. Does de la Vallée Poussin 1896 contain the progression statement independently of Hadamard §19?
6. **Theorem 8.2.** Is the shell-and-block argument complete, in particular the buffer of the dyadic denominator parts and the uniformity of the Lean estimate over the support, and does it need more than Vandehey's Corollary 1.2?
7. **Theorem 9.5.** Is the equivalence between uniform preservation of discrepancy and vanishing mean distance (Step 2) stated with the right half-open arc conventions, and are the extremal arc groups in the cyclic discrepancy formula complete?
8. **Proposition 7.2.** Is the sign bookkeeping for the Bellard slots, which uses magnitudes only, acceptable as written, and are the slot bounds for the BBP formula tight enough that no residue class of p modulo 8 is missed?
