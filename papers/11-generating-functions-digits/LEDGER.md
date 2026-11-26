# Claim-to-source novelty ledger: Digit Distribution of Arithmetic Generating Functions (v1.0, candidate draft)

Ledger date: 26 November 2026. **No new literature search was performed for this draft.** The search record below is the one made on 25 November 2026 for the Phase 20 notes ([notes/phase20/literature.md](../../notes/phase20/literature.md)) and the Phase 21 audit ([notes/phase21/phase20-audit-and-paper-plans.md](../../notes/phase21/phase20-audit-and-paper-plans.md), §2.2), which used a web search tool in standard mode, the arXiv API, ar5iv and read-only GitHub queries. MathSciNet, zbMATH, Google Scholar and Crossref were **not** searched. **A failed search does not establish novelty.** "Not located" below means only that the statement was not found in the sources listed; it is not a priority claim.

Reading labels (as in the source notes): **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[U]** unverified.

The written proofs have been checked only by AI models from several providers, including one cross-provider review of this manuscript (`notes/phase22/reviews/paper-xi-review.md`, verdict REVISE; all findings repaired on 26 November 2026, post-repair re-check outstanding). None of the repairs changed a priority comparison below. Cross-model review is not independent human peer review.

## Sources compared

| Source | What it gives | Read | Used in |
| --- | --- | --- | --- |
| L. Euler, E244 (1760) and E541 (1783); proof communicated to Goldbach in 1750 | Pentagonal number theorem | [S] via J. Bell, arXiv:math/0510054 [R: ar5iv text]; originals not read | Theorem 4.1 |
| C. G. J. Jacobi, *Fundamenta nova* (1829) | Cube identity `∏(1−q^k)^3 = Σ(−1)^k(2k+1)q^{k(k+1)/2}` | [S] (page 185 from one secondary summary; book not read); the identity itself [R] as quoted by Serre 1985 | Theorem 4.1 |
| E. Landau (1908) | `#{n ≤ x: n = a²+b²} ∼ K x/√log x` | [S] via Brink–Moree–Osburn 2011 [R] | Theorems 5.1, 5.6 |
| P. Bernays (1912) | Same for every primitive positive definite binary form | [S] via Brink–Moree–Osburn 2011 [R] | Theorem 5.1, Prop 5.11, Thm 5.14 |
| J.-P. Serre (1981), Publ. IHÉS 54 | Chebotarev density of trace-zero primes, Théorème 18 (weight one), Théorème 17 (CM support) | [R] §6, §7.7, Introduction | Theorems 6.6, 9.9 |
| J.-P. Serre (1985), Glasgow Math. J. 27 | Lacunary powers `η^r`, CM decompositions of `η(12z)^{2k}` | [R] Introduction, §1.1, Theorem 1′; §2 as summarized | Theorems 4.9, 9.9 |
| P. Deligne and J.-P. Serre (1974) | Weight-one newforms ↔ odd Artin representations | [S] via Serre 1981 | Theorems 4.10, 6.6 |
| Yu. V. Nesterenko (1996) | Algebraic independence of `q, P(q), Q(q), R(q)` | [S] (as used by Duverney et al. and BBCP) | Prop 6.5 (transcendence, no novelty) |
| A. Hamieh and M. R. Murty (2016) | Transcendence of `L_q(k,χ)` (Thm 1.1, primitive χ) and of values of modular forms (Thm 3.1) | [R] for Paper VI (author PDF with journal pagination) | Prop 6.5 |
| Duverney–Nishioka–Nishioka–Shiokawa (1996); Bertrand (1997) | Transcendence of theta values | [A/S] | Prop 6.5 |
| Bailey, Borwein, Crandall, Pomerance (2004), J. Théor. Nombres Bordeaux 16, §9 | One-bit count of `Θ_3(1/2)^2`: `∼ C_0 M/√log M`, `C_0 ≈ 0.7996` (Theorem 9.4, p. 509); expectation that `Θ_3(1/2)^3` is 2-normal | [R] pp. 505–512 (Numdam scan) | Theorem D, §1.3 |
| V. Bergelson and T. Downarowicz (2025), arXiv:2506.12929 | Preservation of normality and determinism under arithmetic operations | [A] | §1.3 |
| G. Rauzy (1976) | Characterization of normality-preserving translations | [A] (IMPAN and EuDML records) | §1.3 |
| D. D. Wall (1949) | Rational multiples preserve normality | [S] | §1.3 |
| C. Anderson, Paper VI v1.0 (papers/06-multiplicative-lambert, registry CC-48) | Binary multiplicative Lambert series: `1 − D_N ≍ (log log N)/(log N)^{1−δ}`, disjunctive, nonnormal | own work, cited | Theorem D(i), (iv) |
| C. Anderson, Paper X v1.0 (papers/10-discrepancy-arithmetic) | Sharp translation identity; `K_b = (b−1)^{−1}ℤ + {M_N → 0}`; rational criterion; residue-density test | own work, cited | §§2, 4.6, 9 |
| J. M. Campbell (2026), arXiv:2605.24160 | The word 11 occurs infinitely often in the binary expansion of the Erdős–Borwein constant | [A] | §1.3 (context only) |
| V. Becher and S. Lew Deveali (2026), arXiv:2607.06773 | Numbers deterministic in base 2 and normal in every odd base | [A] | §1.3 (context only) |
| Public repositories `Mira-Cult/math` (commit `cf9e57f`) and `CaptainSude/*` | Erdős–Borwein density and disjunctivity notes; generalized Lambert disjunctivity | file listings and keyword scans only; contents not read | see below |

## Theorem A: sparse coefficient transfer (Theorems 3.4–3.15)

- **Statement and hypotheses:** integer coefficients with `Σ|a(m)|b^{−m} < ∞`; finite all-prefix bound `2ε + L(1+S(N−1))/N + Â(N+L)/((b−1)b^Lε N)`; rate with sharp constant 2 under linear mass; membership under linear, polynomial and logarithmic mass with the corresponding sparsity; displaced width inequality; sub-threshold width law.
- **Evidence:** Lean-supported paper proof. Kernel-verified: Theorem 3.5 (lookahead form and qualitative limits), Lemmas 2.2, 2.5, 3.10. Paper proof: the sharp shadow count, the explicit rates, Proposition 3.7, Theorems 3.12 and 3.15.
- **Earliest relevant literature:** the deficit and concentration identities are elementary consequences of the definition of extreme discrepancy (Kuipers–Niederreiter).
- **Closest published results:** none located that states a coefficient-to-discrepancy transfer for integer coefficient series with an explicit constant. BBCP 2004 isolate supported coefficients whose digits survive carries, a mechanism close to Lemma 3.13–3.14, for the one-bit count only.
- **Closest preprints and repositories:** none located.
- **Relation:** apparently new in the sources examined. It builds on the repository's sharp translation identity (registry SY-04, Paper X) and on the sparse-digit counting lemma `Phase18Synthetic.sparse_farCount_le`, which it generalizes from bounded to signed coefficients of controlled mass.
- **Outstanding review:** whether the sub-threshold width law (Theorem 3.15) appears elsewhere in a different language (for example for lacunary series in uniform distribution theory). Not searched.

## Theorem B: Euler's product (Theorems 4.3–4.6)

- **Statement:** exact base-`b` digit blocks; all-prefix word frequencies of `0^L`, `(b−1)^L`; non-disjunctivity; `1 − D_N(E_b; b) = √(2/3) log_b N/√N + O_b(N^{−1/2})`.
- **Evidence:** Lean-supported paper proof (series only; Euler's identity external).
- **Earliest relevant literature:** Euler (1750 letter; E244, E541). The digit blocks are an immediate consequence of the pentagonal theorem once written in base `b`.
- **Closest published results:** none located on digits or discrepancy of `∏(1 − b^{−k})`. Phase 20 search: query "base-b digits of Euler's pentagonal number product ∏(1−b^{−k}) normal number" returned Bell's survey and general normal-number pages only.
- **Relation:** the digit formula is elementary and may well be folklore; we claim only that we did not find it stated. The sharp deficit and the word bounds were not located.

## Theorem C: cube, square and scalings (Theorems 4.7–4.12, 8.6)

- **Statement:** `E_b^3` disjunctive with deficit constant `√2`; `E_b^2` coefficients `c(12n+1)` of `η(12τ)^2`, support `∼ C_η N/(log N)^{3/4}`; `(a/d)E_b^r ∈ K_b ⇔ a/d ∈ ℤ[1/b]` for r = 1, 2, 3.
- **Evidence:** paper proofs from Jacobi's identity and, for `E_b^2`, the external CM identification (Serre 1985, Martin 1996). The uniform pair sieve (Theorem 8.1) is proved in full, including Selberg's upper bound.
- **Earliest relevant literature:** Jacobi (1829); Serre (1985) for the CM decomposition of `η(12z)^2`; Martin (1996) for multiplicative η-quotients.
- **Closest published results:** Serre 1985 gives lacunarity (density-zero support) of `η^2`; the support exponent 3/4 follows from his Théorème 18 with the Klein-four image. No digit result located. The sign rule `c(p) = +2 ⇔ p = x² + 36y²` is a standard ring-class-field statement (Cox, Theorem 9.4); we did not search for it specifically.
- **Relation:** the constant `C_η`, the disjunctivity of `E_b^3` and the scaling criterion were not located. Multiplication by rationals preserves normality (Wall 1949); our scaling criterion concerns non-normal numbers in `K_b`, a different question.
- **Outstanding review:** the CM identification is cited, not reproved; the Martin (1996) record is unverified.

## Theorem D: exact constants in every radix (Theorems 5.6–5.14)

- **Statement:** `L_χ(b)` constants `C_χ/(2 log b)` (radix `2^k`) and `C_χ(1+log 2)/(2 log b)` (other radices); `K/(2 log 2)` for `χ_{−4}` in base 2 and for `Θ_3(1/2)^2`; `E_b^2` constants; theta values of primitive forms of fundamental discriminant in every radix; thresholds `δ*_b = β_b/(β_b + log 2)` for the prime-density class.
- **Evidence:** Lean-supported paper proofs (finite core in `RadixWidthLaw.lean`; analytic inputs external).
- **Earliest relevant literature:** Landau (1908) and Bernays (1912) for the support constants `K`, `C_Q`; Selberg–Delange for `C_χ`, `C_η`.
- **Closest published results:** **BBCP 2004, Theorem 9.4**: the number of ones among the first `M` binary digits of `Θ_3(1/2)^2` is `∼ C_0 M/√log M`, `C_0 ≈ 0.7996`, and their proof keeps isolated coefficients. This is a one-bit asymptotic with a constant that is not `K`; they do not consider discrepancy. **Paper VI v1.0 (CC-48)** proved `1 − D_N(L; 2) ≍ (log log N)/(log N)^{1−δ}` for the binary multiplicative Lambert class with unspecified constants. Theorem D upgrades that order to an exact constant and extends it to every radix; it is an upgrade of a cited result of the same author, not a second claim of it.
- **Closest preprints and repositories:** `CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality` concerns `Σ (b^{m^r} − 1)^{−1}`, a different (positive-density-word) regime; only its name and description were read. The Phase 21 audit recorded the action "read that repository's statement before any priority statement about other radices"; **this action has not been carried out**, so no priority statement about radix dependence is made beyond "not located".
- **Relation:** not located in the sources examined: the exact constants, the radix-`2^k` discontinuity, the even-composite thresholds and the class-group constants. The Landau–Bernays constants themselves are classical inputs.
- **Outstanding review:** Theorem 5.14 is condensed in the manuscript; its full proof (Proposition 2.10 and Lemmas 2.4–2.9 of [radix-thresholds-and-class-groups.md](../../notes/phase22/radix-thresholds-and-class-groups.md)) should be read by a specialist. The relative error `O(log log log N/log log N)` means finite data cannot test any constant.

## Theorem E: theta values, weight one and periodic weights (Theorems 6.3–6.10, Prop 6.11)

- **Statement:** `Θ_Q(1/b) ∈ K_b` with rate `LL/√log N`; integer-coefficient weight-one forms in `K_b` with exponent `α_f`; even-order characters; odd periodic weights; q-digamma reflections; residue-class Lambert sums.
- **Evidence:** Lean-supported paper proofs (transfer core, q-digamma identity and odd-periodic cancellation in Lean; Deligne–Serre, Chebotarev, Wirsing, Shiu external).
- **Earliest relevant literature:** Deligne–Serre (1974) and Serre (1981) for the structure and lacunarity of weight-one forms; Jackson and Gasper–Rahman for `ψ_q`.
- **Closest published results:** lacunarity of weight-one forms (Serre 1981) is the essential input; no digit or discrepancy statement located. Phase 20 search for "q-digamma function value q = 1/2 binary expansion normality digits Lambert series" returned only the Lambert-series identity (Wolfram `QPolyGamma`, Berg–Petersen arXiv:1111.0250).
- **Transcendence:** Nesterenko (1996), Duverney–Nishioka–Nishioka–Shiokawa (1996), Bertrand (1997), Hamieh–Murty (2016). **No novelty is claimed.** Transcendence of `L_χ(b)` for even `χ` is not claimed (open).
- **Relation:** not located in the sources examined.

## Theorem F: digit frequencies in the kernel (Theorems 7.3–7.16)

- **Statement:** dichotomy and classification of digit and word frequencies inside `K_b`; no element of `K_b` simply normal for `b ≥ 3`; nonnegative sparse series have digit 0 of frequency 1; `D^jE_b`, `D^jE_b^3`, `E_b^2DE_b` simply normal in base 2 and disjunctive (except `E_b`); `E_b^2` not simply normal for `b ≥ 3`, both constant words of positive lower frequency; exact automaton word laws for `(a/d)E_b`, `(a/d)E_b^3`; binary simple normality when `ord_d(2)` is odd.
- **Evidence:** paper proofs; the Lean support is Proposition 7.7 (derivatives of the series) and the purely periodic `E_b` automaton.
- **Earliest relevant literature:** the characterization of `K_b` through fixed points is Paper X. That a number concentrated at 0 has digits dominated by runs of `0` and `b−1` is elementary.
- **Closest published results:** none located. Bergelson–Downarowicz and Rauzy concern normal inputs and deterministic numbers, not digit frequencies of kernel elements.
- **Relation:** not located in the sources examined. The statement "no element of `K_b` is simply normal for `b ≥ 3`" is short and may be known in other language; no specific search was made.
- **Outstanding review:** the converse of Theorem 7.15 (only conjectured) and the simple normality of `E_2^2` are open and are stated as open.

## Theorem G: limits of the method (Theorems 9.5–9.10, Props 9.1–9.4)

- **Statement:** completeness of sparse bounded signed representations for `K_b`; entropy–multiplicity lower bound for signed digit widths of `D(Θ_3^2)`, `D(E_b^2)`, `E_b^4`, `E_b^6`, `E_b^8`; non-closure of `K_b` under squaring; theta powers modulo `K_b`; wash-out of congruences.
- **Evidence:** paper proofs; net transfer rests on the Lean transfer theorems.
- **Earliest relevant literature:** Reitwiesner (1960) for minimal signed binary representations (non-adjacent form); Moser–de Bruijn for the sumset decomposition; Serre (1985) for which `η^r` are lacunary; Ribet (1977) for CM forms.
- **Closest published results:** Bergelson–Downarowicz construct numerical-kernel elements whose product is normal (binary), which is consistent with Proposition 9.2 and is cited as context. BBCP 2004 (p. 509) expect `Θ_3(1/2)^3` and `Θ_3(1/2)^4` to be 2-normal; we prove nothing about them.
- **Relation:** the completeness theorem is a short consequence of Paper X's decomposition of `K_b`; the wall is a statement about a method, and we draw no distributional conclusion for `E_b^r`, `r ≥ 4`.

## Public repositories and preprints

- `Mira-Cult/math` at commit `cf9e57f` (25 November 2026): the tree listing and a keyword scan of the 24 files in `notes/number-theory/normal-numbers/` found no file concerning theta values, Euler's product, partitions or modular forms. The files were not read in full.
- `CaptainSude` (20 public repositories as of 25 November 2026): names and descriptions only; none concerns theta functions, `E_b`, partitions or sums of two squares. `generalized-Lambert-disjunctivity-and-nonnormality` concerns a different regime (see Theorem D).
- Campbell, arXiv:2605.24160: concerns the Erdős–Borwein constant; nothing here is proved about that constant, `E_odd` or `E_even` individually.
- Manai, arXiv:2609.24665 and arXiv:2508.09319 [A]: normality-preserving operations and transcendentally normal numbers; relevant to normal numbers, not to `K_b`. Not cited in the manuscript.

## Search record (25 November 2026; reproduced from the Phase 21 audit)

Queries: "Mira-Cult math github normal numbers notes"; "CaptainSude github generalized Lambert disjunctivity nonnormality"; "discrepancy of binary expansion of Lambert series Σ χ(m)/(2^m−1) non-normal digit distribution"; "q-digamma function value q=1/2 binary expansion normality digits Lambert series"; "base-b digits of Euler's pentagonal number product ∏(1−b^{−k}) normal number"; "Bergelson Downarowicz On preservation of normality and determinism under arithmetic operations"; "Bell Euler and the pentagonal number theorem arXiv math/0510054"; "Jacobi Fundamenta nova theoriae functionum ellipticarum 1829 Königsberg cube of product identity"; "Campbell binary digits of the Erdős–Borwein constant 11 occurs infinitely often Crandall problem"; "Rauzy Nombres normaux et processus déterministes Acta Arithmetica 29 1976 211–225"; "normal numbers theta function value Θ_3(1/2) binary digits discrepancy sum of two squares 2026 arXiv"; "Hardy Wright Theorem 357 Jacobi (1−x^n)^3 = Σ (−1)^n (2n+1) x^{n(n+1)/2}"; "partition generating function Σ p(n) 2^{−n} binary expansion digits normal number"; "Dayan Ganguly Weiss normality preserving multiplication rationals probabilistic proof"; arXiv API records for 2605.24160, 2506.12929, math/0510054, 2609.24665, 2607.06773, 2603.04396, 2508.09319; ar5iv text of math/0510054; GitHub tree and keyword scans as above.

None of these returned a statement of the main theorems. This is a record of a failed search, not evidence of novelty.

## Open actions before release

- Read the statement of `CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality` and compare it with Theorem D.
- Search MathSciNet and zbMATH for digit or discrepancy results on `∏(1 − b^{−k})`, theta values and weight-one forms, and for the sub-threshold width law.
- Verify the bibliographic records marked unverified in `references.bib` (Euler E244/E541, Jacobi, Landau, Bernays, Martin, Wirsing 1967, Strassmann, Reitwiesner, Ribet, Becher–Lew Deveali, Duverney–Nishioka–Nishioka–Shiokawa, Bertrand) against the originals.
