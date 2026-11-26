# Paper V v2.0 review 1: Denominator Growth and Rational Shadowing for Classical Constants

Reviewer model: Claude Sonnet 5.5 (`claude-sonnet-5-5`)
Date: 25 November 2026
Reviewed commit: `e0c222a17ed7b44bdbd726e56022b1534a4935ec` (`git rev-parse HEAD` at the start of the review; manuscript in `papers/05-classical-denominators-v2/`)
Manuscript author model: OpenAI GPT-6.2 Sol

**AI model review; not independent human peer review.**

All line numbers below refer to `papers/05-classical-denominators-v2/paper.tex` unless another file is named.

## Verdict

**Accept after major revision. No critical finding.**

I found no mathematical error in any statement I rederived (list below). The central scope requirement is met: nowhere does the paper imply normality, a limiting digit distribution or a discrepancy bound below one for ln 2, π, e, √2 or φ. It says so in the abstract (line 23), the introduction (line 40) and a dedicated remark (lines 348–350).

The revision needed is about framing, attribution and form rather than correctness.

1. The Legendre–Bézout "shadowing windows" and the "smaller denominator exponents" are, as approximation statements, equivalent to nearest-point rounding on a grid, which holds for every real number. The paper concedes this only in a remark. The abstract and §5 read as if the windows were a result about ln 2 and π (finding 1).
2. At least two closely related primary antecedents are missing from the manuscript's bibliography and the ledger (finding 2).
3. At 22 pages and about 13,800 words, the paper is overloaded. Several of its proofs are compressed to the point of being hard to check, and its second half is a separate paper (finding 3).

## What I did

- **Read** paper.tex in full, plus `references.bib`, VERIFICATION.md, LEDGER.md, CHANGES.md, metadata.toml, all six submission files, WAVE2-CONTRACT.md, and the Lean sources at the pinned commits.
- **Rederived.** I rederived these results by hand against the source text:
  - the prime-band formula (Prop. 2.1);
  - the valuation system and descent (Thm 2.2), including the arithmetic 7/18 + 1/36 = 5/12 and 73/180 + 1/36 = 13/30, and the constants C = 34, 16;
  - the Galois step and the 2-adic twist at 16 | M and 8 ‖ M in Thm 3.1 (lines 132–140);
  - the CRT cell values (c+2)/4, (c+5)/8 and the limit 4/15 (lines 193–195);
  - Bézout rounding;
  - the Chebyshev integration by parts, including h′(0) = g(1) and h′(π) = −g(−1);
  - the even-Legendre π kernel and its first crossing;
  - the barrier inequality, and ρ and the rates 0.39322 and 0.26316 for the examples (lines 319–323);
  - the factorial obstruction;
  - the Taylor delay (Thm 8.1);
  - the exact completion index including the p = 3 case {3, 12} → 683/2¹⁴, and the Dias da Silva–Hamidoune use with K = ⌈3√(4p−3)⌉ ≤ p−1 for p ≥ 41;
  - the exponent arithmetic in the mean-loss proof: the 3/7 exponent comes out from X^{−1/3}·(X^{4/7})^{4/3};
  - the divisor-function argument in the period bound;
  - the signed-transform threshold;
  - the sparse-obstruction proof;
  - the d = 3 and d = 5 cycle calculations.
- **Read for plausibility only.** The shell and Fourier argument for joint uniformity of ray components (lines 446–452), the continued-fraction facts about e, and the finer points of the horizontal-row discrepancy proof (lines 562–578).
- **Lean at the pinned commits.**
  - All 14 declaration pins in the paper resolve to the named declarations at `e4809cf` (lines 55, 66, 85, 122; 1158, 1210, 1220; 73, 94; 32; 207; 190; and `optimal_rate`, `denominator_rate` in VERIFICATION.md).
  - I also checked that the Lean cell rows `srcA` and `srcG` (cutoffs ⌊v/2k⌋ and ⌊v/(2t−1)⌋, coefficient 2Re((1+i)^j)/(j·2^{tj})) agree with the paper's A_k and G_t at x = v/2.
  - I checked by hand that the minimizer expressions in Thm 2.2 equal B − 5(G₃ + 2A₂ − 2A₄ − B) and B − 2(⋯), that their limits are log 2, and that G₁(∞) = log 2.
- **Reproduction scripts rerun** (all pass):
  - `phase16_adaptive_log.py`: 730 nodes at 13/30, 484 at 5/12, two surviving points 73/180 and 7/18; thresholds 1/528, 1/562, 1/839, 1/862 as quoted.
  - `phase18_classical.py`: 518 π enclosures; Machin D = 91 and Størmer D = 76 at shift 600.
  - `phase19_classical.py` (from the working tree, identical to c2c9da): all checks pass.
  - `phase19_horizontal.py`: row 3 gives 2/3 and 2/3; row 5 gives 1/5 and 8/15.
- **Independent computations** (my own scripts):
  - The BBP prefix at N = 4M has log q/N = 1.463, 1.503, 1.495 for M = 200, 400, 800, against the claimed 3/2.
  - The Bellard prefix at N = 10M gives 0.9989, 0.9970, 0.9997, against the claimed 1.
  - For every odd n with 7 ≤ n < 1500, both Aurifeuillian factors H_n^± have a prime divisor of exact order 4n. The check removes all primes of order dividing 4d for d | n, d < n, by repeated gcd, and the cofactor exceeds 1. The only failures are H_n^− for n = 1, 3, 5, exactly the exceptions the paper treats. This supports Grechkoseeva's Theorem 2 as used at line 93.
- **PDF.** `wsl -d Ubuntu -- bash papers/wsl-build.sh 05-classical-denominators-v2` builds. The PDF has 22 pages, no undefined references or citations after the final pass, and only four harmless underfull boxes (abstract and lines 132–141). I inspected rendered pages; the mathematics typesets correctly. The working tree is unchanged.

## 1. Scope requirement (explicit audit)

The requirement is satisfied. The relevant sentences are:

- Abstract, line 23: "Lower denominator exponents and longer rational shadowing windows do not establish limiting digit distribution. The paper proves neither normality nor a limiting discrepancy bound below one for log 2, π, e, √2 or the golden ratio."
- Introduction, line 40: the same statement, plus the reason ("one needs estimates across the relevant shifts and denominators, with control of the actual numerators").
- Remark `rem:digits` (lines 348–350): the dedicated remark. It defines D_N and limsup D_N, and notes that every real target has a nearest point on any rational grid.
- Lines 346, 399 and 455: the limits of the grid, golden-ratio and ray results are each stated at the point of use. In particular line 399 correctly records that the Lean criterion for φ leaves the density question open.
- Submission files: abstract.txt, alphaxiv.md, summary.md and metadata.toml repeat the sentence; announcement.md says "leave limiting digit distribution open"; reviewer-packet.md says "leave limiting digit distribution open".

I found no sentence that implies otherwise. Three small risks remain, listed as findings 4, 13 and 14: "shadowing windows" as a phrase, the undefended Theorem rays statement, and the absence of a conclusion section.

## Findings

### Major

**1. Major (framing and content). The window and denominator-exponent claims are vacuous as approximation statements and are compared with an incomparable class.**
- **Location:** abstract line 23 ("Chebyshev and Legendre kernels give rational approximants with smaller denominator exponents. Legendre moment rounding gives linear shadowing windows…"); Thm 5.3, lines 260–273; Prop. 5.4, lines 301–317; examples, lines 319–323; Remark, line 349.
- **Problem.** Thm 5.3 gives q_N | L_D and error ≤ (2L_D)^{−1} + O(ρ^{−D}). Since ρ^{−D} = o(1/L_D), this is the error of the nearest point of (1/L_D)ℤ to 2^N ξ for any real ξ, with L_D = lcm(1,…,D). Indeed Prop. 5.4 says Y_N is that nearest point under the separation test.
  - Consequently T_N = log₂ q_N + O(1) is the free benchmark available for every real number and every denominator. Any "rate" r = log q/N and window slope are only the choice of D.
  - The floor of 5/12 in §§2–4 concerns truncation of fixed identities without rounding. Chebyshev and Legendre use coefficient rounding, which is a different class. Saying the latter has "smaller denominator exponents" invites the reading that the 5/12 floor is beaten.
  - The paper does not use the window–denominator inequality (Thm 6.1) to say what a nontrivial window would be. That inequality only shows that windows exceeding log₂ q_N by more than (μ−1)(N + log₂ q_N) are impossible. This is consistent with the benchmark but does not engage it.
  - Substantive content: an explicit integer-polynomial (Padé-type) realization of the nearest grid point by rational arithmetic with D = O(N), the Chebyshev analytic floor D^{−2}, and the Legendre separation test. The reader has to find this out for themselves.
- **Fix.**
  1. In the abstract, replace "smaller denominator exponents" with a sentence such as "Rounding polynomial moments on the grid (1/lcm(1,…,D))ℤ realizes the nearest grid point to 2^N log 2 and 2^N π by rational arithmetic; the resulting windows equal log₂ of the denominator up to O(1), which is the benchmark for any real number."
  2. After Thm 5.3 add a remark stating the benchmark and defining the *excess window* G_N = T_N − log₂ q_N. Say that the paper proves G_N = O(1) for these models and nothing about larger G_N.
  3. Move the sentence at line 349 ("every real target has a nearest point…") into this remark.
  4. Label §5 as a construction of explicit moments, not an approximation theorem.
  5. Rename "rational shadowing" or define it at first use (T_N in line 219) so that the title does not promise more than the content.

**2. Major (attribution). Primary antecedents are missing.**
- **Location:** paper.tex lines 28, 42, 93, 510; LEDGER.md entry A (lines 5–15), "Relation" line.
- **Problem.** I found these by searching and could read only abstracts, snippets and keyword lists, not the full texts. They need a specialist's check before the ledger's priority statements stand.
  1. **Borwein–Borwein–Galway, "Finding and excluding b-ary Machin-type individual digit formulae", Canad. J. Math. 56 (2004).** According to its published keywords it uses Zsigmondy's theorem and primitive prime factors, together with prime factorization in ℤ[i] and ℤ, both to find Machin-type formulae and to exclude them. It also shows that π has no BBP arctangent formula in bases b ≠ 2. This is the closest method I found for the descent by a largest primitive prime in Thm 2.2, and for the Gaussian norm factors H_n^±. The ledger's claim that "the specific all-cutoff reduction and two extremal rates were not located" should be revised to say how this paper differs. Its "Closest published results" line cites Bang–Zsigmondy, Grechkoseeva and Shiu only.
  2. **Størmer 1896 and Todd 1949 (Amer. Math. Monthly 56).** The classical primitive-prime-factor argument for Machin-type arctangent relations. Mention it as the origin of the descent.
  3. **Harmonic-number p-adic literature.**
     - Sources: Boyd 1994 and Eswarathasan–Levine 1991 for the band structure at p^a ≤ n < p^{a+1}; Shiu (arXiv 1607.02863, Thm 2); Rogers (arXiv 0708.2439).
     - LEDGER.md already lists Shiu and Rogers but neither appears in references.bib or the body. The internal review notes/phase19/reviews/classical-final.md, line 37, says Rogers "already studies the very same weighted zero set J_p(y), including y = 1/2". Yet line 510 of the paper calls the lag count "the weighted counterpart of Sanna's short-range bound". The prime-band mechanism of Prop. 2.1 is the weighted analogue of the harmonic-number mechanism and should be credited as such.
  4. **Rivoal 2007 (cited at line 42, but understated).**
     - He proves irrationality measures for logarithms with denominators of the form d_m^s B^m (d_m = lcm(1,…,m)), from the Padé table of log(1−x).
     - His abstract draws consequences for nonzero digits in the B-ary expansion and for the denominators of convergents of log r.
     - That is exactly the denominator shape 2^w L_D of Thm 5.2 and 5.3. The paper's sentence "Here the binary multiplier is prescribed and the rational polynomial moment is rounded" is a fair description of the difference. It should be accompanied by a precise statement of Rivoal's theorem and a comparison of the denominators.
  5. **Brisebarre 2001 (Experimental Mathematics 10) on Legendre-type polynomials for log 2 and π/√3, and Alladi–Robinson 1980,** as the sources of the Legendre kernel with pole values in the denominator.
- **Answer to the author's open questions.** For the balanced-trace reduction, I found no antecedent for the all-cutoff reduction of balanced cyclotomic traces to A_k and G_t. The closest are the Machin-type classification literature above and the Bailey–Borwein–Plouffe "compendium of BBP-type formulas". For the prescribed-shift Padé moment grid, I found no exact statement. The closest are Rivoal (denominators d_m^s B^m with B a base) and the Legendre-type Padé tradition (Alladi–Robinson, Rukhadze, Brisebarre, Hata, Marcovecchio). My searches were limited to open web search; I could not reach MathSciNet or most journal full texts.
- **Fix.** Add the missing references (Borwein–Borwein–Galway, Størmer or Todd, Boyd, Shiu, Rogers, Brisebarre). Rewrite the "Relation" line of ledger entry A and add a sentence to the introduction describing the primitive-divisor method as classical.

**3. Major (exposition). The paper is overloaded, and its proofs are too compressed to check in the text.**
- **Location:** whole paper; §§7–9 in particular.
- **Problem.** Ten sections and 23 numbered statements at 22 pages and about 13,800 words cover heterogeneous topics:
  - least denominator rates;
  - adaptive heights;
  - Chebyshev and Legendre moments;
  - window barriers;
  - arctangent, BBP and Bellard denominators;
  - factorial grouping;
  - geometric rays;
  - sparse functional identities;
  - one-prime completion, mean loss and periods of Taylor rows;
  - discrepancy of horizontal rows.
  - The title and abstract do not prepare a reader for the last four. The reader meets undefined repository vocabulary (finding 9).
  - Several proofs are sketches: Thm 3.1 lines 136–140; Thm 8.2 lines 446–452; Prop. 7.2 lines 372–384; Thm 9.5 lines 562–578. In Thm 3.1, the claim "an involution because it preserves the class modulo 8" is right, but a reader must reconstruct why u + M/2 stays a unit and preserves the odd-prime residues. I did so, and it works.
- **Fix.** Split.
  - **Paper A (about 12 pages):** §§1–4 and the barrier from §6, plus the scope remark. Title: denominator rates for balanced traces.
  - **Paper B:** §5 and the window–denominator inequality, framed as in finding 1.
  - **Note C:** §§7 (BBP, Bellard, arctangent, e, √2, φ) and 8–9 (rays, functional obstruction, completion, mean loss, periods, horizontal rows).
  
  If a single paper is kept, move the proofs of Thm 3.1, Thm 8.2, Prop. 9.1 and Thm 9.5 to an appendix with the missing steps, drop the e, √2 and φ continued-fraction material (lines 397–408), which is not used elsewhere, and add a roadmap paragraph to the introduction.

### Minor

**4. Minor (scope wording). "Shadowing windows" and "shadowing" are not defined where they first appear.**
- **Location:** title; abstract line 23; the definition appears only at line 219.
- **Problem.** An expert reading the abstract may take "shadowing" to mean tracking of the actual digit orbit. Line 219 clarifies that a window is the number of bits to which a *rational* model agrees with 2^N ξ. This is the rational analogue of shadowing, but it provides no information on digits beyond the window.
- **Fix.** Define "window" in the introduction as "the number of binary digits after position N that the model reproduces", and keep the scope sentence adjacent to it.

**5. Minor (evidence label). Thm 4.1 (`th:adaptive`) is labelled "Lean-supported paper proof" although the linear thresholds N/528, N/562, N/839, N/862 rest on Python only.**
- **Location:** lines 159–175 and 179–181.
- **Problem.** Lean supports only the finite comparison (lines 177 and 181 say so). The thresholds come from a branch-and-bound enumeration in `phase16_adaptive_log.py`, which I reran and which reproduces them. The paper marks them "separate exact rational enumeration", but the theorem carries a single label.
- **Fix.** Add `\evidence{Finite certificate}` to the threshold table, or split the theorem into the Lean-supported rate statement and a separately labelled threshold proposition.

**6. Minor (evidence label). Thm 8.2 (`th:rays`) is labelled "Lean-supported paper proof" although the Lean declarations support different statements.**
- **Location:** lines 431–452.
- **Problem.** `hasSum_prime_rays_logTwo` (OrderedComponents, line 32) concerns the fixed-prime partition m = rp^j with p ∤ r, which is *not* the partition in the theorem (a distinct fresh prime for each ray). `fixed_support_orbit_estimate` (SmoothOrbit, line 207) is a qualitative modular estimate for a single fixed modulus c. VERIFICATION.md states correctly that "the fresh-prime and BBP partitions and all their joint distribution conclusions are paper deductions."
- **Fix.** Label the theorem "Paper proof" and list the Lean estimate under External inputs, or say in the label which steps are Lean.

**7. Minor (citation accuracy). Several citations could not be checked or look misplaced.**
- **Location:** lines 68, 382 (Hadamard, "p. 219, modulus 4"); lines 320 and 362 (Takahashi); bib entry `bang`; bib entry `mira`; line 448 (`bc02` Cor. 4.9(i)).
- **Problem.**
  1. Hadamard 1896 is cited for the prime number theorem in progressions modulo 4. I could not read the scanned article (Numdam serves page images only). The standard primary source for progressions is de la Vallée Poussin 1896. Please verify and cite both if both are correct. Hadamard for modulus 1 (ϑ(x) ~ x) is not in doubt.
  2. Takahashi (Ramanujan J. 51 (2020), 177–186; bibliographic data confirmed) is a BBP-type paper. It is cited for the Machin and Størmer identities and for "Eqs. (11)–(19)" of the tangent-addition formula. I could not check the equation numbers. The identities themselves are classical (Machin 1706, Størmer 1896); cite the classical sources or Borwein–Borwein–Galway.
  3. The `bang` entry's page range 70–80, 130–137 matches the standard citation, and VERIFICATION.md admits that the scan could not be read. The contract requires `note = {unverified}` for entries that cannot be checked. Add it, or state the input as "Bang's theorem as cited in Zsigmondy and in Grechkoseeva".
  4. The `mira` entry is dated "24 November 2026" in the bib, but the page I fetched carries only a commit hash and no date. Its Theorem 1 does state joint uniformity of ({bⁿ L_{p_i,s_i}(b)}) for distinct pairs (p_i, s_i), as paper.tex line 448 says. The note itself says OpenAI models assisted and that it makes "no historical priority claim and is not a formal verification." Cite it as an unrefereed AI-assisted note, with the commit as identifier.
  5. I could not retrieve Bailey–Crandall 2002 (the EMIS server returned 503), so Cor. 4.9(i) is unchecked by me.
- **Fix.** As above. Items 1 and 5 need a human with access to the original text.

**8. Minor (proof detail). Thm 2.2, lines 117–118: the positivity check on 8 ≤ v < 18 is not what the argument needs.**
- **Problem.** The 1/36 beyond the certificate is Σ_{v ≥ 72} 2/(v(v+1)), so only S_θ(x) ≠ 0 for x ≥ 36 is used. That follows directly from |S(x) − log 2| ≤ 4C·2^{−x} and 4·34·2^{−9} = 0.27 < log 2. The direct summation on 8 ≤ v < 18 is redundant. As written it suggests that cells 8–71 are needed for something else, which a reader could mistake for a gap.
- **Fix.** Delete the sentence or say that it is not used, and state the actual requirement (x ≥ 36).

**9. Minor (jargon). Repository vocabulary in the body.**
- **Location:** "prefix function" (lines 37, 83, 122, never defined; it means the map x ↦ S(x)); "cells", "half-cell", "M₇₁", "pays its mass" (lines 111–115, 179, 193, 364, 585); "the verification material" (line 181); "the repository checkpoint", "companion verification map" (line 585).
- **Fix.** Define "cell v" once, as the prime band 2N/(v+1) < p ≤ 2N/v with weight m_v. Replace "prefix function" by "the function x ↦ S(x)". Replace "the verification material" by a reference to a specific file or appendix. Describe the pinned commit by its SHA and purpose.

**10. Minor (submission file). The X post in `submission/announcement.md` is slightly misleading.**
- **Problem.** "proves balanced trace denominator rates of 5/12 and 13/30 for ln 2" reads as a property of ln 2. The theorem is about the *least* growth rates of reduced denominators among fixed finite rational identities truncated at a common binary scale. At 253 characters it fits the 280-character limit.
- **Fix.** "…shows that, among fixed truncated rational identities for ln 2, the reduced denominators grow at rates at least 5/12 (and 13/30 next)…".

**11. Minor (verification file). Corrupted characters in `VERIFICATION.md`.**
- **Location:** lines 33, 40, 41, 42, 77, 79.
- **Problem.** The symbols ≤, −, 2^{−k}, √ and exponents have been replaced by "?". Examples: "1 ? v ? 71", "(0, 0, 0, ?5)", "primitive prime of 2? ? 1", "errors at most 2???? and 2????". These include the two precision claims for π at shift 600 (2^{−261}, 2^{−213}). Line 64 of LEDGER.md may be affected too.
- **Fix.** Restore the symbols; re-save as UTF-8.

**12. Minor (evidence labels). Thm 5.2 (`th:cheb`) is labelled "Lean-supported" although its Lean content is elementary.**
- **Problem.** `shifted_poly_integral_den_dvd` and `rounding_integral_error` check only the divisibility of a polynomial moment and the rounding bound. All of the substantive content (first crossing, ρ, the D^{−2} residual, PNT) is paper proof. VERIFICATION.md states this honestly. The label is permitted by the contract ("named steps are Lean declarations").
- **Fix.** Optional. Say "Lean checks the moment-denominator and rounding-error lemmas only" in the theorem's label line.

**13. Minor (scope). Thm 8.2 proves joint normality of finitely many ray components, and the introduction never says so.**
- **Location:** lines 431–455 versus lines 40 and 348–350.
- **Problem.** This is a real normality-type result (joint Haar uniformity of binary orbits of components whose sum is log 2 or π). A reader who sees "do not establish limiting digit distribution" in the abstract may wonder how the components can be uniform while the sum is not covered. Lines 455–456 explain it well (finite uniformity does not transfer; an explicit rational example shows why). That explanation is far from the scope remark.
- **Fix.** Add one sentence to Remark `rem:digits` and to the introduction: "The ray components in §8 are jointly uniform; their sum, log 2, is not covered, and §8 shows by an explicit example that such uniformity does not pass to infinite sums."

**14. Minor (structure). There is no conclusion section.**
- **Problem.** The paper ends with verification and AI-use sections. The scope remark sits mid-paper (§6), and the open questions (author's antecedent questions, simultaneous optimality at line 498, density at line 399) are scattered.
- **Fix.** Add a one-page "Scope and open questions" section before the verification section. Repeat the scope sentence there.

**15. Minor (consistency). The abstract in paper.tex differs from `submission/abstract.txt` and `metadata.toml`.**
- **Problem.** The paper says "exhibit failure of the rate floor at larger heights"; the submission text says "construct large-height identities that fall below the denominator floor with growing error". Both are accurate (Prop. 4.2, lines 184–196), but release files should carry the same text. abstract.txt has 226 words, within the 250-word contract limit.
- **Fix.** Use one abstract everywhere.

### Editorial

**16. Editorial. Line 346.** "A modular estimate with fixed prime support and windows of length at least q^δ requires both hypotheses. The grid divisibilities do not supply them [vandehey]" is not parseable without Vandehey's statement. Name the two hypotheses.

**17. Editorial. Line 399.** "with a bounded accuracy window if the shift is rounded to effective precision" is unclear; say what is bounded and by what.

**18. Editorial. Section titles.** §7 "Scope for individual constants" mixes a proposition on arctangents, BBP digit series, factorial grouping and continued fractions. Retitle, or split as in finding 3.

**19. Editorial. Intro ordering.** The first mention of "balanced sources" (line 33) comes before motivation. One sentence on why balanced sources (the unbalanced remark, 146–152) would orient the reader.

**20. Editorial. Prop. 7.1, line 358.** State that a, c > 0 is used for positivity of aB₂ + cB₃ (lines 363–364). It is easy to miss that mixed signs can cancel.

## Evidence labels against Lean

- **Consistent with the pins:** Main Theorem, Prop. 2.1, Thm 2.2 and Thm 3.1. The Lean content is exactly as described in lines 52–53, 64, 102–103 and 112–114: the coefficient and cutoff lemmas, the Gaussian Frobenius congruence, the valuation system, and the 71-cell comparison with the two exact masses.
- **Overstated by label, accurate in text:** findings 5, 6 and 12.
- **Scope of the Lean certificate.** It is a branch-and-bound over ℚ⁴ on cells 1 ≤ v ≤ 71. The passage to reduced-denominator rates is a paper argument, which §10 (lines 585–587) and VERIFICATION.md say clearly. I found no place where the paper calls a paper theorem "verified".
- **Finite certificates.** The Legendre and π counts in lines 587 (ten log rows, 518 checks, D = 91 and 76 at shift 600) match the scripts' output.

## Submission files

- `abstract.txt`, `alphaxiv.md`, `summary.md`, `reviewer-packet.md`: accurate and not promotional. The scope sentence is present. The reviewer packet asks specific questions (the 2-adic twist, the same-height descent, a Padé antecedent), which are the right ones, and my review addresses them.
- Theorem numbers in the packet and the inquiries match the paper's counters: Theorem 2.2, Theorem 5.3, Proposition 5.4.
- `reviewer-inquiry.md`: two concrete theorem-specific inquiries with `[Name]` placeholders and no addresses. Add a third for the denominator-form antecedents (a Rivoal-style question) once finding 1 is addressed.
- `announcement.md`: see finding 10.
- `alphaxiv.md`: the author-field placeholder is as the contract requires.

## What I did not verify

- The shell and Fourier argument (lines 450–452) beyond checking that the Lean statement `fixed_support_orbit_estimate` has the quantifier structure (fixed prime support, length T with den ≤ T^d) that the paper uses.
- The elementary but long claims of Thm 9.5 beyond the d = 3, 5 cycle values (script) and the supporting logic.
- Any publisher full text of Bang, Hadamard and Bailey–Crandall 2002 (scans unreadable or server error).
- The truth of any priority statement; see finding 2.
- Whether the literature entries beyond those listed are free of subtle bibliographic errors. I confirmed the following against web records: Bang (volume, pages), Zsigmondy (volume, pages), Takahashi, Rivoal, Marcovecchio (and its bound 3.5745…), Zeilberger–Zudilin, Rukhadze (3.8914), Alladi–Robinson (Crelle 318, 137–155), Beukers (BLMS 11), BBP (Math. Comp. 66), Bailey–Crandall 2001 and 2002, Dias da Silva–Hamidoune, Sanna, and Grechkoseeva (arXiv 2504.04729v1, corrected version). I did not check Chudnovsky LNM 925, pp. 299–322, Hata's 8.016 bound, or Bellard's note beyond their existence.
