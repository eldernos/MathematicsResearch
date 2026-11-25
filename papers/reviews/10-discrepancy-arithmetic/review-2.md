# Referee Report 2: *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations* (v1.0)

- **Manuscript:** `papers/10-discrepancy-arithmetic/` (v1.0, 25 November 2026)
- **Reviewer model:** Gemini 4 Neon, Antigravity
- **Date:** 2026-11-25
- **Reviewed commit:** `40f8fb69656f3257f408c0538b56bf768132ce21`
- **Review scope:** Lean 4 correspondence, explicit constructions and rates, bibliography accuracy, presentation, build, and submission package
- **Status notice:** AI model review; not independent human peer review.

---

## Verdict: Minor Revision

The manuscript is mathematically sound, clearly written, and well scoped. Its main theorems are stated up front in the introduction with clear notation, no new probability metric is claimed, and every **Kernel-verified** claim in `paper.tex` corresponds to a complete Lean 4 declaration at the pinned commits under matching definitions (half-open intervals $[a,c)$, indexing from $n = 0$, extreme discrepancy `radixDiscrepancy`, `IsGreatest`, and `Tendsto` limits). All four verification scripts listed in `VERIFICATION.md` exit cleanly with status 0, and `wsl -d Ubuntu -- bash papers/wsl-build.sh 10-discrepancy-arithmetic` reproduces the committed 16-page `paper.pdf` byte-for-byte with zero LaTeX errors and zero undefined references or citations.

No critical mathematical errors or Lean overstatements were found. Three **Major** issues require revision before publication: (1) a factual mischaracterization of Bergelson–Downarowicz (2025) Section 8 as using "signed sparse digits" (in the primary arXiv text both factors are ordinary nonnegative binary numbers); (2) internal contradictions and mismatched script/case-count records in `VERIFICATION.md`; and (3) bibliography omissions and rendering issues (`Levy39` omits `volume = {67}`, `\bibliographystyle{plain}` suppresses all DOIs and URLs from the built PDF, and `BD25` prints a doubled year). Four **Minor** findings cover unspecified summation lower bounds, minor Lean-citation omissions and precision gaps, small proof/typesetting items, and submission-package updates.

---

## Numbered Findings

### Finding 1 — Mischaracterization of Bergelson–Downarowicz Section 8 as using "signed sparse digits"
- **Severity:** Major
- **Location:** `paper.tex` L848–851; `LEDGER.md` L18, L92
- **Problem:** Following Proposition 6.3, `paper.tex` L848–851 writes:
  > "Bergelson and Downarowicz construct, in base $2$ and with signed sparse digits, two numbers whose digit changes or ones have density zero and whose product is normal \cite[Section~8]{BD25}; both factors then have $M_N\to0$, so their example is a stronger statement of the same kind. The example here uses positive digits, gives an explicit rational product and holds in every base."

  Direct inspection of the primary source (`arXiv:2506.12929v1`, Subsections 8.3–8.5: Theorem 8.11, Proposition 8.13, Corollary 8.14) shows that neither factor uses signed digits:
  - $y$ (Section 8.3) has ordinary unsigned binary digits $\{0,1\}$ given by the indicator of $S = \{0\} \cup \mathsf{FS}((n_k)_{k\ge 1})$.
  - $a = xy$ (Theorem 8.11) is a positive real number whose standard binary expansion in $\{0,1\}^{\mathbb N}$ has density zero of switches (`01`/`10`).
  - $b = 1/y$ (Proposition 8.13) is a positive real number in $(0,1)$ whose standard binary expansion is $\lim B_k$ with $B_1 = 11$, $B_{k+1} = (B_k 0^{n_k})^{n_{k+1}/(2n_k)}$, having density zero of ones.
  - The word "signed" does not appear anywhere in Section 8 of `BD25`.

  The contrast "The example here uses positive digits" therefore attributes a nonexistent distinction to Proposition 6.3. This error appears to have entered from `notes/phase19/products-of-remainders.md` (`LEDGER.md` L18 notes that Section 8 was not re-read for this manuscript).
- **Fix:** Revise `paper.tex` L848–851 (and `LEDGER.md` L92) to state accurately that Bergelson–Downarowicz (Section 8, specifically Theorem 8.11, Proposition 8.13 and Corollary 8.14) construct in base $2$ two positive numbers—one with density-zero digit switches and one with density-zero ones—whose product is normal, and remove the "signed sparse digits" / "positive digits" contrast. Retain the genuine distinctions: Proposition 6.3 works in every base $b \ge 2$, both factors have density-zero ones with explicit rate $O(\log(2N)/\sqrt N)$, and their product is an explicit rational $b^r/(b^r-1)$ by a short Moser–de Bruijn argument.

### Finding 2 — Internal contradictions and inaccurate reproduction records in `VERIFICATION.md`
- **Severity:** Major
- **Location:** `VERIFICATION.md` L8, L14, L27–28, L44, L66; `paper.tex` L894–899
- **Problem:** Several entries in `VERIFICATION.md` contradict `paper.tex`, `submission/alphaxiv.md`, or the scripts they cite:
  1. **Evidence-label contradiction for Theorem C / Proposition 4.3 / Theorem 4.5 (`VERIFICATION.md` L14 vs. L32, L34 and `paper.tex` L488, L521):** Row C states `"Kernel-verified pseudometric (= Prop 4.1); the rest are paper proofs (= Prop 4.3, Thm 4.5, Prop 4.6)"`. However, `paper.tex` L488 and L521 and `VERIFICATION.md` L32 and L34 classify both Proposition 4.3 and Theorem 4.5 as **Lean-supported paper proofs** (`asymDist_triangle`, `asymDist_intMul_le`, etc., are kernel-verified in `DiscrepancyGeometry.lean`), and `submission/alphaxiv.md` L41 explicitly lists the asymptotic pseudometric axioms as kernel-verified. Likewise, `paper.tex` L894–899 omits Proposition 4.3 from its itemized list of Lean-supported vs. written results.
  2. **Wrong reproduction script for Theorem 3.5 (`VERIFICATION.md` L27):** Row 3.5 lists `python -B -m unittest scripts/test_phase18_summation.py` at `e4809cf`. Inspection of `scripts/test_phase18_summation.py` shows that none of its 6 tests touches $Z = \sum_{k\ge 1} 2^{-k(k+1)}$ or Theorem 3.5 (`test_translation_with_boundary_crossings` tests Theorem 3.1 / Corollary 3.2 on rational shifts). Meanwhile, Row 3.5 omits `lake build` at `e4809cf` for the kernel-verified declaration `quadratic_sparse_transfer`.
  3. **Wrong case count and mismatched construction for Theorem 6.2 (`VERIFICATION.md` L44):** Row 6.2 describes `notes/phase19/reviews/geometry-periods-check.py` §6 as `"simulation, seven cases"`. The script actually runs **eight** cases (four $(b,m,m_0)$ tuples $\times$ $\theta \in \{0, 0.5\}$; only the summary table in `notes/phase19/reviews/geometry-periods.md` omitted the row `(2, 6, 3, 0.0)`). More substantively, §6 simulates a *linearly* growing digit-word block schedule (`reps = max(1, (4 * k) // len(w))`), **not** the cubic schedule $n_k = t k^3$ with positive coefficients $c_k \in (0,1]$ of denominators dividing $m_0$ proved in Theorem 6.2(b).
  4. **Lean URL count (`VERIFICATION.md` L8):** States `"All 30 Lean URLs embedded in the built paper.pdf were extracted with pdfinfo -url ... (30 of 30)"`. The built `paper.pdf` actually contains **33** Lean hyperlink annotations pointing to **30 distinct** URLs (three declarations—`discrepancy_transfer`, `mixtureRealizable`, `discDist_intMul_le`—are linked twice).
  5. **Unused external dependency for Proposition 3.6 (`VERIFICATION.md` L28, L66):** Lists `"Liouville's theorem (Liouville numbers are transcendental)"` as an external input for Proposition 3.6. However, Proposition 3.6 (`paper.tex` L385–388) only claims that $Z_!$ is a Liouville number, never asserting transcendence.
- **Fix:**
  1. Update Row C in `VERIFICATION.md` L14 to read `"Kernel-verified pseudometric (= Prop 4.1); Prop 4.3 and Thm 4.5 are Lean-supported paper proofs; Prop 4.6 is a paper proof"`, and mention Proposition 4.3 in `paper.tex` L894–899.
  2. Update Row 3.5 to cite `lake build` at `e4809cf`, and attach `test_phase18_summation.py` to Rows 3.1/3.2 (where `test_translation_with_boundary_crossings` applies).
  3. Update Row 6.2 to `"eight cases"` and note that §6 is a linear digit-word simulation rather than a check of the cubic schedule (or add an exact-rational check of the cubic schedule).
  4. Clarify L8 as `"30 distinct Lean URLs (33 link instances)"`.
  5. Remove `"Liouville's theorem"` from `VERIFICATION.md` L28 and L66 (or state transcendence in Proposition 3.6).

### Finding 3 — Bibliography omissions and rendering defects (`Levy39`, `plain.bst` stripping DOIs/URLs, doubled year in `BD25`)
- **Severity:** Major
- **Location:** `references.bib` L20–26, L38–45, L47–55, L90–104; `paper.tex` L114, L136, L916; `paper.pdf` pp. 15–16
- **Problem:**
  1. **Missing volume in `Levy39` (`references.bib` L38–45):** The entry omits `volume`. `LEDGER.md` L15 explains that Crossref returned an inconsistent volume (`2` for DOI `10.24033/bsmf.1288`). Checking the primary archival record on Numdam (`https://www.numdam.org/item/BSMF_1939__67__1_0/`) unambiguously establishes **Tome 67 (1939), pp. 1–41** (which `LEDGER.md` L28 and `notes/phase19/literature.md` L72 already cite).
  2. **`\bibliographystyle{plain}` (`paper.tex` L916) suppresses every DOI and URL in the built PDF:** Although `references.bib` provides verified DOIs or URLs for 12 of 13 entries per `WAVE2-CONTRACT.md` L44, standard `plain.bst` ignores `doi` and `url` fields. Consequently, **zero** DOIs or URLs appear in the References of `paper.pdf` (pp. 15–16)—not even the repository links for `CompanionC` and `CompanionLambert`.
  3. **Doubled year in `BD25` (`references.bib` L23–24, `paper.pdf` p. 15):** Because `howpublished` ends with `15 June 2025` and `year = {2025}`, `plain.bst` renders `[3]` as `... version 1, 15 June 2025, 2025.`
  4. **Unverified/uncited attributions (`paper.tex` L114, L136):** Wall (1949) and Kamae (1976) are cited by name in the introduction without bibliography entries (`LEDGER.md` L20 candidly flags this). Also `Kuiper60` (`references.bib` L50–51) follows ScienceDirect/Crossref's `Indagationes Mathematicae (Proceedings), 63:38–47`, which is accurate to the DOI metadata (`10.1016/S1385-7258(60)50006-0`), though standard mathematical convention distinguishes *Nederl. Akad. Wetensch. Proc. Ser. A* **63** from *Indag. Math.* **22**.
- **Fix:**
  1. Add `volume = {67}` to `Levy39` in `references.bib` (and update `LEDGER.md` L15).
  2. Either switch `\bibliographystyle{plain}` to a DOI/URL-aware style (e.g., `plainnat` with `natbib`, as used in `06-multiplicative-lambert`, or `plainurl`) or include DOIs/URLs in `note` if `plain` is kept across the release.
  3. Remove the trailing year from `BD25`'s `howpublished` (e.g., `arXiv:2506.12929 [math.DS], v1 (15 June)`) or drop `year` duplication so `2025, 2025` is eliminated.
  4. Optionally add verified entries for Wall (1949) / Maxfield (1953) and Kamae (1976), and note `= Indag. Math. 22` if desired for `Kuiper60`.

### Finding 4 — Missing lower summation bounds in series and active-error sums
- **Severity:** Minor
- **Location:** `paper.tex` L77, L243, L254, L627, L637, L655, L796
- **Problem:** Lemma 2.5 (`paper.tex` L241–243) sets $n_0 = 0$, $R_0 = 0$, and defines $c_k \in (0,1]$ from $R_{k-1}$—hence for $k \ge 1$ only (matching Lean's `programState_eq_prefix`, where the sum runs over `k ∈ range L` with `programCoeffs ... k = c_{k+1}` at exponent `n (k + 1)`). Yet L243 writes $R_k = b^{n_k} \sum_{i \le k} c_i b^{-n_i}$ without $i \ge 1$, and L77, L254, L627, and L796 write $\sum_k c_k b^{-tk^3}$ or $\sum_k c_k b^{-n_k}$ without $k \ge 1$ (unlike L367 and L386, which write $k \ge 1$ and $k \ge 2$). In Theorem 5.3, L637 states $h_k \le 7 t k^2$ (valid for $k \ge 1$, false at $k = 0$ where $h_0 = t$) and L655 defines $H := \sum_{k \le K} (p^v h_k / q_k + q_k)$ without $k \ge 1$, even though $q_k = p^{1+\lfloor \log_p k \rfloor}$ is undefined at $k = 0$ and block $0$ is retired.
- **Fix:** Specify $1 \le i \le k$ in L243, $k \ge 1$ in L77, L254, L627, L637 (for $h_k \le 7tk^2$), and L796, and $1 \le k \le K$ in L655.

### Finding 5 — Lean citation completeness and precision gaps in Proposition 4.1 and Theorem 6.2(b)
- **Severity:** Minor
- **Location:** `paper.tex` L423–429, L814, L817, L821; `VERIFICATION.md` L23, L29, L36
- **Problem:**
  1. **Omitted pseudometric declarations in Proposition 4.1 (`paper.tex` L423–429, `VERIFICATION.md` L29):** Both lists cite `discDist_translate`, `discDist_comm`, `discDist_triangle`, `discDist_isGreatest`, `radixDiscrepancy_lipschitz`, `discDist_eq_zero_iff`, and `discDist_intMul_le`, but omit `discDist_nonneg` (`DiscrepancyGeometry.lean#L39`) and `discDist_self` (`DiscrepancyGeometry.lean#L51`), both of which are present and kernel-verified at `c2c9da6`.
  2. **Denominator bound in Theorem 6.2(b) (`paper.tex` L814, L821):** The proof cites Lemma 2.5 as its Lean-supported step and asserts that the coefficients $c_k$ have denominators dividing $m_0$. In Lean, `programCoeffs_den_dvd` (`Phase18Synthetic.lean#L416`) proves only `(programCoeffs ...).den ∣ (u (k+1)).den * (u k).den`, which yields divisibility by $m_0^2$. Divisibility by $m_0$ holds mathematically via the $\mathrm{lcm}(\den u_k, \den u_{k-1})$ remark at `paper.tex` L253 (outside the kernel-verified lemma), so the denominator sharpening in Theorem 6.2(b) is a paper step rather than a direct corollary of the Lean declaration.
  3. **Constant subscript in Theorem 6.2(b) (`paper.tex` L817):** Writes `$O_{b,m}(K^2)$` for the model count error, whereas $h_K = t(3K^2+3K+1)$ contains $t = \ord_p(b)$, so the implied constant depends on $p$ as well (matching $C_{b,p,m}$ in L797). Note also that $p$ and $t$ play no role in Theorem 6.2(b) beyond scaling the block schedule $n_k = t k^3$; a half-sentence noting that $n_k = k^3$ works equally well (with $t$ retained to share the schedule of Theorem 5.3) would clarify why $p$ appears in the hypothesis.
  4. **Minor understatements in `VERIFICATION.md`:** Equation (4) (`VERIFICATION.md` L23) is also kernel-verified as `Phase18Synthetic.discrepancy_deficit_le` (L524 at `e4809cf`), and the `max/abs` form of (1) is `AdditionSpectrum.finite_necessity'` (L260 at `c2c9da6`).
- **Fix:** Add `discDist_nonneg` and `discDist_self` to the declaration list in Proposition 4.1 and `VERIFICATION.md` L29; clarify in Theorem 6.2(b) L814/L821 that divisibility of $\den c_k$ by $m_0$ uses the $\mathrm{lcm}$ remark at L253 (not only the Lean product bound); change `$O_{b,m}(K^2)$` to `$O_{b,p,m}(K^2)$` at L817.

### Finding 6 — Minor proof exposition and typesetting polish in `paper.tex`
- **Severity:** Minor
- **Location:** `paper.tex` L355, L549, L839–840; `references.bib` L94, L102
- **Problem:**
  1. **Remark 3.4 (`paper.tex` L355):** `"supported on the two fixed points of the shift"` is slightly imprecise because the full shift on $\{0,\ldots,b-1\}^{\mathbb N}$ has $b$ fixed points $d^\infty$; only the two constant sequences $0^\infty$ and $(b-1)^\infty$ correspond to $0 \in \mathbb T$.
  2. **Proposition 4.6 (`paper.tex` L549):** `"by Theorem 3.3, |e_n| \to 0 outside a set of density zero"` skips the one-line step from $M_N(z-c) \to 0$ with $|e_n| \le 1/2$ to convergence in density (Koopman–von Neumann / Markov).
  3. **Proposition 6.3 (`paper.tex` L839–840):** Takes $w = \lceil \log_b N \rceil$ (which equals $0$ at $N = 1$, still valid asymptotically, though $w = \lceil \log_b(N+1) \rceil$ matches L380 and L393) and states the remainder is within $2 b^{-w}$ (safe, matching `sparse_near` with $B=1$, though $\sum_{j\ge w+1} b^{-j} = b^{-w}/(b-1) \le b^{-w}$).
  4. **Underfull `\hbox` (badness 10000) in bibliography:** `paper.pdf` compiles cleanly with zero overfull boxes, but entries `[1]` and `[2]` trigger badness-10000 underfull `\hbox` warnings because `\texttt{papers/06-multiplicative-lambert}` and `\texttt{papers/07-synthetic-expansions}` cannot hyphenate (`paper.tex` L247–256 also has a badness-4096 underfull box from long Lean names).
- **Fix:** Replace `"the two fixed points of the shift"` at L355 with `"the two fixed points 0^\infty and (b-1)^\infty of the shift"`; add `"(since |e_n| \le 1/2 and M_N(z-c) \to 0)"` at L549; use `\path{...}` (from `xurl`, already loaded in `preamble.tex`) for directory paths in `references.bib` L94 and L102.

### Finding 7 — Submission-package pre-release placeholders and minor omissions
- **Severity:** Minor
- **Location:** `submission/alphaxiv.md` L25; `submission/alphaxiv.toml` L7, L27–30; `submission/reviewer-inquiry.md` L21, L36; `submission/reviewer-packet.md` L35; `submission/abstract.txt` L1
- **Problem:** The submission package is accurate in tone, conforms to `WAVE2-CONTRACT.md` (author `Christopher Anderson`, `Independent Researcher`, verbatim AI-use disclosure in `paper.tex` and `alphaxiv.md`, `abstract.txt` is 214 words $\le 250$, X post in `announcement.md` is 238 characters $\le 280$, all 9 `registry_ids` in `metadata.toml` exist in `docs/registry/{OP,SY}.toml`, and no new probability metric is claimed). Minor items to address before release:
  1. `submission/alphaxiv.md` L25 contains the placeholder `"The release-commit link will be added at integration"`.
  2. `submission/alphaxiv.toml` L7 still has `owner_confirmed = false` (awaiting owner sign-off), and L27–30 lists only `Gemini 4 Argon` as referee; update to include both parallel reviews (`Gemini 4 Neon`) before submission.
  3. `submission/reviewer-inquiry.md` L21 has an unresolved link placeholder (expected for a draft), and L36 writes `q_n \equiv p_n \pm r_n` without `\pmod 1`.
  4. `submission/reviewer-packet.md` L35 omits `PrimePowerGrid.primePower_period_count` (used by Theorem 5.3 via Lemma 2.4) when listing the Lean-verified steps of Theorems 5.3–5.4.
  5. `submission/abstract.txt` L1 uses `\mathbb{Z}[1/b]` (whereas `metadata.toml` uses plain `Z[1/b]`, and `WAVE2-CONTRACT.md` L51 requests "no TeX macros apart from simple `$...$`").
- **Fix:** Fill in release-commit links at integration, add `Gemini 4 Neon` to `submission/alphaxiv.toml`, add `\pmod 1` in `reviewer-inquiry.md` L36, mention `PrimePowerGrid.primePower_period_count` in `reviewer-packet.md` L35, and optionally replace `\mathbb{Z}[1/b]` in `abstract.txt` with `Z[1/b]` if strict macro-free plain text is desired.

---

## Detailed Verification Summary

### 1. Lean 4 Correspondence Audit

All 33 `\lean`/`\leanP` references in `paper.tex` (30 distinct URLs) and all 31 Lean URLs in `VERIFICATION.md` were extracted and verified programmatically against `git show <commit>:NormalityChecker/<File>.lean` at `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (`E`) and `c2c9da683666b3b9368e5d4b5cb858caccf528f5` (`P`): **0 line or name mismatches**.

**Definition matching (`NormalityChecker/Basic.lean` and `BinaryDiscrepancy.lean`, identical at `E` and `P`):**
- `shift b x n := Int.fract ((b : ℝ) ^ n * x)` matches $\fr{b^n x}$ indexed from $n = 0$.
- `frequency u a c N := ((range N).filter (fun i => a ≤ u i ∧ u i < c)).card / (N : ℝ)` matches half-open intervals $[a,c)$ over $0 \le n < N$.
- `radixDiscrepancy b x N := sSup {d | ∃ a c : ℝ, 0 ≤ a ∧ a < c ∧ c ≤ 1 ∧ d = |frequency (shift b x) a c N - (c - a)|}` matches `paper.tex` L42 verbatim.
- `Near y ε := ∃ j : ℤ, |y - j| ≤ ε` and `farCount` (`Phase18Synthetic.lean` L510–516) match $E_N(z,\epsilon) = \#\{n < N : \dist{b^n z} > \epsilon\}$ (`paper.tex` L287).
- `Tendsto (radixDiscrepancy b x) atTop (𝓝 α)` and `asymDist b x y := limsup (fun N => discDist b N x y) atTop` match the paper's limit and $\limsup$ definitions.

**Kernel-verified statements audited:**

| Manuscript result | Pinned Lean declarations | Complete match? | Notes |
| --- | --- | --- | --- |
| Lemma 2.5 (`lem:program`, L240) | `Phase18Synthetic`: `programCoeff_mem` (L364), `programState_fract` (L383), `programCoeffs_prime_power` (L426), `programState_eq_prefix` (L438), `programmed_prefix_fract` (L459) at `E` | Yes (bundle of 5) | Minor paper indexing slip $\sum_{i \le k}$ (Finding 4); L253 $\mathrm{lcm}$ remark is outside the lemma (Finding 5). |
| Theorem 3.1 (`thm:sharp`, L262) / Thm A identity | `SharpTranslation`: `sharp_translation` (L343), `radixDiscrepancy_zero` (L357), `sharp_translation_zero` (L378), `sharp_translation_isGreatest` (L386), `sampleDisc_paired` (L326) at `E` | Yes | Exact, complete match including attainment at $x = 0$. |
| Corollary 3.2 (`cor:transfer`, L292) | `Phase18Synthetic`: `discrepancy_transfer` (L583), `discrepancy_eventually_int` (L642) at `E` | Yes | Exact match; eq. (4) is also verified at L524 (`discrepancy_deficit_le`). |
| Proposition 4.1 (`prop:metric`, L407) / Thm C metric | `DiscrepancyGeometry`: `discDist_translate` (L55), `discDist_comm` (L68), `discDist_triangle` (L78), `discDist_isGreatest` (L87), `radixDiscrepancy_lipschitz` (L93), `discDist_eq_zero_iff` (L243), `discDist_intMul_le` (L346) at `P` | Yes | `discDist_nonneg` (L39) and `discDist_self` (L51) also exist at `P` and should be cited (Finding 5). |
| Theorem 5.1 (`thm:addition`, L567) / Thm B qualitative | `AdditionSpectrum`: `polytope_eq_convexHull` (L150), `isExtremeIn_polytope_iff` (L240), `finite_necessity` (L248), `mixtureRealizable` (L1470), `addSpectrum_eq` (L1480), `exact_addition_spectrum` (L1486) at `P` | Yes | Exact match (`mem_polytope_iff` L71 bridges `polytope` and eq. (1)). |

Lean-supported steps (`PrimePowerGrid.primePower_period_count` L313, `Phase18Synthetic.sparse_discrepancy_transfer` L811 and `quadratic_sparse_transfer` L837, `DiscrepancyGeometry.asymDist_triangle` L390 and `asymDist_intMul_le` L419) were likewise inspected and match the cited steps accurately. The abstract (`paper.tex` L32–33) makes no overstatement of Lean scope.

### 2. Explicit Constructions, Rates, Counterexamples, and Script Reruns

All four scripts named in `VERIFICATION.md` were rerun from the worktree root with `PYTHONUTF8=1` and exited with status 0:
- `python -B scripts/phase19_addition.py` — passed (1,105 admissible triples out of 2,197 on twelfths; 2,448 cubic prefixes; binary $N=100$ enclosures $10^{-6}[469999,470000]$, $[189722,189723]$, $[318888,318889]$; 5 polynomial avoidance certificates; 1,153 $d$-summand decompositions; 7,920 six-form prefixes).
- `python -B notes/phase19/reviews/addition_check.py` — passed (brute-force vertex check $d = 1\ldots 4$; 400 non-orbit paired samples; six-form equality on $\{0, 1/2\}$; independent binary $N=100$ enclosure check).
- `python -B notes/phase19/reviews/geometry-periods-check.py` — passed (all 8 sections, including 400 finite-distance tests, exhaustive rational membership $b \le 12, q < 120$, base-10 residue-density test, star and box counterexamples, integer dilation bounds, 8 boundary-spectrum simulations, Moser–de Bruijn product checks).
- `python -B -m unittest scripts/test_phase18_summation.py` — passed (6 tests, OK; see Finding 2 on its scope).

Hand checks and independent exact-rational checks confirmed:
- **Theorem 5.3 (uniform cubic rate):** Weight nonnegativity, Lemma 5.2 greedy scheduler overcount bounds $[-(r-1), 1]$ with rational approximation tolerance $1/(4rk)$ (giving chosen true deficit $\ge 1/(2r) > 0$ so zero-weight types are never chosen), summation by parts $|Z - \delta N| \le t + 17 h_K$, active count bound $H \le (7tp^v + p)K(K+1)/2$, geometric tail window $W = \lceil \log_b(\frac{2b}{b-1}(K+1)) \rceil$, and uniformity of $C_{b,p}$ all hold.
- **Theorem 5.4 (computable, algebraically independent witnesses):** Power-of-two override cost $\le \frac{28t}{3} K^2$, distinctness of candidate coordinates via $b^{n_k} x_a \in a/q_k + (0, 1/(2q_k)) \pmod 1$, grid nonvanishing, and survival of interval certificates under arbitrary future coefficients in $(0,1]$ all hold. Independently verified in exact rational arithmetic on the interior triple $(1/4, 1/2, 3/8)$ (beyond the vertex $(1,1,1)$ tested in `phase19_addition.py`) for three bivariate polynomials, certifying at depths `(1,1), (2,2), (4,4)`.
- **Theorem 4.5 & Proposition 4.6 ($\mathbb Z[1/b]$ classification and residue-density test):** Valuation test at $1/(b-1)$ and the base-10 example $z = 1/3 + \sum_{m \ge 1} 10^{-m^2}$ (where $k_n \equiv \lfloor \sqrt n \rfloor \pmod 3$ holds for every $n \ge 0$, equidistributed mod 3) are exact.
- **Theorem 6.2 (dilation boundary $[1/m_0, 1]$):** Both necessity and the cubic positive-coefficient construction are sound. Independently tested the actual cubic schedule of Theorem 6.2(b) (rather than the linear simulation in `geometry-periods-check.py` §6) in exact rational arithmetic for $(b, m, m_0, \theta) \in \{(2,3,3,0), (2,3,3,1/2), (2,6,3,1/2), (3,4,4,0), (2,4,1,0)\}$, confirming $c_k \in (0,1]$, $\den(c_k) \mid m_0$, and convergence of $D_N(x)$ and $D_N(mx)$.
- **Proposition 6.3 & Remark 6.4 (Moser–de Bruijn product; star and box counterexamples):** All exact fractions ($D_3^*(1/4) = 1/2$, $D_3^*(63/256) = 61/192$, $D_3^*(-1/256) = 63/64$, change $35/192 = 1/6 + 1/64 > 1/64$; 2D box discrepancy $8/9$ vs. $1, 1$) are independently confirmed.

### 3. Bibliography Verification Against Primary Sources

Every entry in `references.bib` was verified against Crossref API records, Numdam, arXiv (`abs` and HTML of `2506.12929v1`), or repository companion metadata:

| Key | Primary source checked | Status | Notes |
| --- | --- | --- | --- |
| `KN` | Kuipers & Niederreiter (Wiley, 1974) | Verified | Ch. 1 Thm 8.1 (p. 70) and Ch. 2 Thm 1.1 (p. 89) confirmed. |
| `Rauzy76` | Crossref `10.4064/aa-29-3-211-225` | Verified | Acta Arith. 29(3), 211–225, 1976. Exact match. |
| `BD25` | arXiv `2506.12929` & HTML `2506.12929v1` | Mostly verified; **2 issues** | Defs. 3.5, 3.10, Thm 3.12, Prop. 4.9, Cor. 4.10(1), §4.3, Prop. 4.25 all verified verbatim. **Issues:** Section 8 mischaracterized in `paper.tex` L848–851 (Finding 1); doubled `2025, 2025` in rendered PDF (Finding 3). |
| `Sigmund74` | Crossref `10.1090/S0002-9947-1974-0352411-X` | Verified | Trans. AMS 190, 285–299, 1974. Exact match. |
| `Levy39` | Numdam `BSMF_1939__67__1_0` & Crossref `10.24033/bsmf.1288` | **Missing volume** | Primary Numdam record confirms **Tome 67** (1939), pp. 1–41; `references.bib` omits `volume = {67}` (Finding 3). |
| `Kuiper60` | Crossref `10.1016/S1385-7258(60)50006-0` | Verified | Matches ScienceDirect/Crossref `Indagationes Mathematicae (Proceedings), 63:38–47, 1960` (= Proc. KNAW A 63 = Indag. Math. 22; Finding 3). |
| `Fan43` | Crossref `10.1007/BF01174225` & EuDML | Verified | Math. Z. 49 (1943), 681–683. Exact match. |
| `Prokhorov56` | Crossref `10.1137/1101016` | Verified | Theory Probab. Appl. 1(2) (1956), 157–214. Exact match. |
| `Dudley02` | Crossref `10.1017/CBO9780511755347` | Verified | CSAM vol. 74, 2nd ed., CUP, 2002; §11.3 covers Prohorov metric. |
| `CompanionC` | `papers/07-synthetic-expansions/metadata.toml` & `paper.tex` | Verified | Title, version 1.0, Cor. 2.5 and Lemma 5.1 match. URL dropped by `plain.bst` (Finding 3). |
| `CompanionLambert` | `papers/06-multiplicative-lambert/metadata.toml` | Verified | Title and version 1.0 match. URL dropped by `plain.bst` (Finding 3). |
| `Lean4` | Crossref `10.1007/978-3-030-79876-5_37` | Verified | CADE 28, LNCS 12699, pp. 625–635, Springer, 2021. Exact match. |
| `Mathlib` | Crossref `10.1145/3372885.3373824` | Verified | CPP 2020, pp. 367–381, ACM, 2020. Exact match. |

Note: Bugeaud (2012) is not cited in `paper.tex` or `references.bib` (it appears only in `notes/phase19/literature.md`).

### 4. Build, Presentation, and Submission Package

- **Build:** `wsl -d Ubuntu -- bash papers/wsl-build.sh 10-discrepancy-arithmetic` succeeded with exit code 0, producing 16 pages (467,283 bytes, identical to the committed `paper.pdf` with clean `git status`), 0 errors, 0 undefined references/citations, and 0 overfull `\hbox` warnings (4 underfull `\hbox` warnings in the body/bibliography; see Finding 6).
- **Presentation and framing:** Theorems A–D are stated concisely up front in Section 1 with self-contained notation. Repository-internal jargon ("Phase 18/19", "Track B") is absent from Sections 1–7, appearing only as literal Lean module / script names in Section 8 as allowed by `WAVE2-CONTRACT.md`. The paper explicitly states (`paper.tex` L126–127) that `d_N` is **not** a new probability metric and credits Kuiper, Lévy, Ky Fan, Prokhorov, and Bergelson–Downarowicz transparently.
- **Submission package:** Checked all files in `papers/10-discrepancy-arithmetic/submission/` and `metadata.toml`; compliant with `WAVE2-CONTRACT.md` apart from the minor pre-release items in Finding 7.
