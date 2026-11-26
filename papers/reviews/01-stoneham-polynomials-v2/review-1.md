# Review 1 of Paper I v2.0, *Polynomial Images of Stoneham Numbers*

- **Reviewer model:** Claude Opus 5.5 (Anthropic)
- **Date:** 25 November 2026
- **Reviewed commit:** `0a19fe4` (branch `publication/wave-2`; manuscript `papers/01-stoneham-polynomials-v2/`)
- **Lean baseline:** `e4809cf561573aef588e6ffc491a35cdb79fd9ec`
- **Status:** AI model review; not independent human peer review.

The manuscript was written by a different model (OpenAI GPT-6.2 Astra). I did not rely on its own assessment. Line numbers refer to `paper.tex` at `0a19fe4`.

## Verdict

**Major revision.** I found no mathematical error, and no claim needs to be withheld. The kernel-verified statements match their Lean declarations. The parameter-two scope is stated honestly. The finite certificates reproduce exactly.

Three things need revision before release:

- **Credit placement (M1).** The credit to Mira Cult's S08 is accurate, but it is not placed where readers look for it: the theorem headings and the opening sentence.
- **Vandehey input (M2).** Vandehey's Theorem 5.1 is used in a repaired form, but the step is labelled as a black-box external input.
- **Exposition (M3).** The writing is too compressed and uses too many undefined project terms for a specialist to check the proofs without the repository notes.

## What I checked and how

1. **Lean statements at e4809cf.** I read every pinned declaration with `git show e4809cf:<path>`. All 27 pinned line references in `paper.tex`, `VERIFICATION.md`, `LEDGER.md` and `submission/` point at the named declaration. For the kernel-verified results I also checked the definitions they use:
   - `NormalIn` in `Basic.lean:23`: half-open digit cylinders of `Int.fract (b^n x)`.
   - The positive-index series `StonehamPolynomial.alpha`, `StonehamStatements.stoneham` and `ParameterTwoSquare.term`.
   - `rectangleFrequency` (positions 0 to N−1 in every coordinate).
   - `ParameterTwoQuadratic.prefix`, `pre`, `linearPrefix` and `quadZ`.

   I did not rerun `check.lean`, because there is no prepared checkpoint build in this worktree and the contract forbids a full build.
2. **Independent exact computations** (my own scripts, using `fractions` only):
   - **Theorem 5.1.** The formula F(d) = Σ⌊log₂ k⌋ holds by brute force for d ≤ 14. Using my own derivation of the mass recurrence, the minimum valuation v₂(d!)+F(d) and its location J_d hold for 2 ≤ d ≤ 8, scanning every 10-bit dyadic cut. This includes the j = 0 cases d = 3 and d = 7. M₂ vanishes on [3/2, 2).
   - **Quartic losses.** The losses are 8, 7 and 8 on the three quartic intervals (12-bit scan).
   - **Theorem 3.1.** The exact profile holds for b ∈ {3, 5, 7, 9, 15, 17} and k ≤ 7.
   - **Binary square, §2.** The α₂,₃² profile 2k−2, 2k−3, 2k−1, 2k holds for k = 4 and 5, and the dip at n = 30 is from 81 to 9.
   - **X² − 2X.** The formula q_k = 2^max(0, 2k−1−v₂(Z_k)) holds for b ∈ {3, 5, 7, 11} and k ≤ 8. The b = 3, n = 12 example is 7315/4 − 2·249399/8 = −60521.
   - **Nonresonant test.** The formula q_k = 2^max(0, k−v₂(2A+B)) holds in 278 random cases that satisfy (2).
   - **c = 35 example.** S = ω/36, and the mass 1295/1296 is divisible by 5.
   - **Theorem 6.1 exponents.** I checked the exponents and the claim η > δ_d for d ≤ 25.
3. **Certificates rerun:**
   - `python -B scripts/phase16_dyadic_stoneham.py --quick --max-degree 120` took 10 min 39 s. All assertions passed. It reported 41992 nodes; d = 120 with largest loss 835 first at 2157/2048, least loss 716 and 336 leaves; losses 6, 8 and 64 for d = 3, 4 and 15; and seven good pairs.
   - `python -B scripts/phase17_dyadic_stoneham.py --degree-128` took 69 s. All assertions passed. It reported 689 nodes, 345 leaves and precision 907; extremal losses 776 and 906, the latter at 138241/131072; nine further pairs, including an orbit of 338544 vectors for (5, 524287); and a reduced (3, 31) orbit of 57 vectors in rank 5.

   Every number quoted at lines 402–419 and in `VERIFICATION.md` matches.
4. **Primary sources read:**
   - **Mira Cult's gist 79be9a5, revision 41b5a78.** Its only revision was committed 2026-10-07T16:31:31Z. I read S08 in full.
   - **Mira Cult's September gist and November note.** I only partly read the September gist; S07 and S09 were checked through the archive's own synthesis and through the November note.
   - **Vandehey, arXiv:1606.07911v1.** I read the PDF text: Theorem 5.1 on pp. 13–14, Proposition 4.1 with (12)–(13), and Corollary 1.2.
   - **Bailey–Crandall.** I read the PDF of the journal version: Theorem 2.2(9) on pp. 529–530, Theorem 4.8 and the rate on p. 535, and Corollary 4.9 on p. 536.
   - **Bailey–Borwein** (author PDF), Theorem 2.
   - **Coons, arXiv:1212.3449v2**, Corollary A.3.
   - **Kano–Shiokawa**, institutional scan: Theorem 4 with conditions (15)–(16), and Wagner's conditions as quoted on p. 11.
   - **Crossref records** for the DOIs.
5. **PDF build.** `wsl -d Ubuntu -- bash papers/wsl-build.sh 01-stoneham-polynomials-v2` gave 11 pages, no undefined references or citations, and no overfull boxes. There is one amsmath warning (`\atopwithdelims`, line 387). The rebuilt `paper.pdf` is byte-identical to the committed one, and `git status` stayed clean.

## Assessment by topic

### 1. Theorem statements and scope

- **Theorem A** (lines 37–40) matches `coprime_polynomial_normal` (`PeriodicPolynomialNormal.lean:145`) exactly: 2 ≤ b, 2 < c, `b.Coprime c`, P ∈ ℚ[X] with `0 < natDegree`, and α indexed from j = 1. The interface equality `StonehamStatements.stoneham = alpha` is `rfl` in `check.lean`.
- **Theorem B** (lines 41–49) matches `coprime_joint_powers` (line 170): distinct positive rᵢ, 0 ≤ uᵢ ≤ vᵢ ≤ 1, half-open boxes, and a common starting digit.
- **Proposition 2.1** (lines 126–130) is a special case of `periodic_upper_mass_nonzero`. The Lean version is more general: it allows any complete normed field with ‖c‖ < 1.
- **Theorems 3.1, 3.2 and 4.1.** Their statements match `ExactDenominatorProfile`/`SquareNormality`, `normal_iff_upper_denominator` (with formal index j = k−1, as the map says), `odd_prime_power_degree_polynomial_normal` and `quartic_polynomial_normal`.
- **Rational-polynomial scope.** It is correct throughout.
- **Odd radix at c = 2.** The standing assumption b ≥ 3 odd is set once at line 231 and inherited by §§4–5 (see m1).

### 2. Proof steps

- **Periodic-unit nonvanishing (lines 131–153).** The argument is correct:
  - In every embedding, |σS| ≤ (c^h − 1)/((c − 1)(c^h − 1)) = 1/(c − 1) < 1, and the top term c^(h−1) exceeds the sum of the earlier terms, so σS ≠ 0. The norm therefore lies in (0, 1), and S is not an algebraic integer.
  - Inclusion–exclusion over the Dickson minimal vertices gives a polynomial of degree d with coefficients in the integral closure and leading coefficient 1 − (1 − 1)^s = 1.
  - Integrality over 𝒪_K implies integrality over ℤ.
  - Compactness of the upper sets containing the anchor, and continuity of the mass mod p^L, give a uniform loss bound.
- **Reflection congruence (lines 109–124).** It is correct, including p = 2: (1 + 2x)² ≡ 1 mod 8.
- **Joint uniformity of distinct powers (lines 195–203).** This is the standard Weyl argument and is correct.
- **Parameter-two square and quadratic test.** I rederived A_k ≡ 2^k − 1 mod 2^(k+2), the valuations k and 1 of A_k ± 1, and the expression −2^(−k)(2A + B + 2A(Σδ_j + δ_k)) for the numerator modulo ℤ₂. All are correct, and v₂(δ_j) = s exactly for every j.
- **Quantitative rate (lines 574–675).** The Vandehey input is discussed separately below. The rest is correct:
  - the length moment bound (6.1);
  - the harmonic gcd average;
  - the phase-error accounting;
  - the margin recursion: s₀ = 2, t_i = s_i − 4 + 2^(1−i), s_(i+1) = s_i + 1 − a_i t_i, Σ a_i t_i < 1/2, s_k > k + 3/2;
  - the conclusion η > a_k/2 = δ_d.

  The refined exponents (1/2, 2), (1/6, 3/2) and (1/14, 5/4) are correct, as are both values 5/6 at (d, λ) = (2, 1).
- **Vandehey's Theorem 5.1.** The paraphrase at lines 600–609 is faithful. Theorem 5.1 (pp. 13–14) holds for P a finite set of primes, m ∈ ℕ_P, gcd(a, m) = 1, k ≥ 0 and *all* N ∈ ℕ, with sum Σ_(n=1)^N, α_k = 1/(2^(k+2) − 2) and log factor (1 + log m)^(2^(−k)). The coprimality of b to P is a standing assumption in §2.1. The constants are explicit recursions in Q = ∏P, M(P) and C_(P,·), so they are effective. Starting at index 0 by replacing a with ab⁻¹ is fine.

  The authors also correctly identify a defect in the preprint's proof. Equation (12) sets m′ = Q·∏p_i^⌊xℓ_i⌋ with Q the product of *all* primes in P, so m′ ∤ m whenever some p ∈ P does not divide m. This happens inside Vandehey's own induction, not only after Fourier reduction: the inner moduli a(b^(iτ) − 1)/m in (11) can lose primes. The repair at lines 611–618 is valid: use Q_S = rad(m) at each step, so that m^x ≤ m′ ≤ 2 rad(m) m^x, and take the maximum of the constants over the finitely many S ⊆ P at each depth. Because the step uses a repaired proof rather than the stated theorem, its evidence label must change (M2).
- **Least orbit order F(d) (lines 509–550).** The proof is correct:
  - The identity Φ − G = Σ_D [min(d − N_D, 2^(D+1) − 1 − N_D) − S_D] follows from the three counting identities.
  - Legendre's formula needs c_i < 2^(i+1), which K(c) < 2 ensures.
  - Nonnegativity follows from A_D + S_D ≤ 2^D K(c) < 2^(D+1).
  - The equality classification forces c_i = 0 below I − 1.
  - The two minimizers enter at 2 − 2^(1−r) and 2 − 2^(−r) (one minimizer when j = 0).
  - The interval statement follows by parity.

  The paper's j = 0 case, with J_d = [2 − 2^(1−r), 2), is correct and corrects registry entry ST-33 (see m10).
- **Cyclic descent (lines 437–450).** It is correct:
  - fixed points of the simultaneous block rotation are the blockwise-constant tuples;
  - Σ_U z^|v| ≡ Σ_(U′) z^(p^r|w|) in 𝔽_p[[z]];
  - (1 − z)^(ep^r) ≡ (1 − z^(p^r))^e;
  - evaluation at 2 with 2^(p^r) ≡ 2 (mod p);
  - M_e(x) = 2^e M_e(2x) for x < 1.
- **Truncation after the d-th one (lines 395–397).** It is correct: if t′ < s ≤ t, then s has more than d binary ones.
- **Limit cuts (lines 333–343).** The argument is correct.
- **Echelon corollary (lines 453–473).** The proof is correct (see m4).

### 3. Parameter-two scope

The paper never claims that every degree or every quadratic is resolved:

- Lines 553–554 state that nonvanishing of M_d for every d ≥ 3 is open.
- Lines 309–313 state that growth of q_k for X² − 2X is open for every fixed odd radix and that a single computed upper half proves nothing. The abstract and CHANGES.md say the same.
- Proposition 4.2 carries the label *Finite certificate*.
- Theorem 4.3 and Corollary 4.4 are labelled *Lean-supported paper proof* and kept separate from the kernel-verified Theorems 3.1, 3.2 and 4.1.
- Lines 420–423 disclose that only the reduced (3, 31) automaton is checked by the Lean kernel, and that the identification of the automaton with the mass relies on the script.

I reran both certificates (see above). The abstract's verb "give" (line 24) is vague; see m3.

### 4. Evidence labels

Every *Kernel-verified* label in the body is the complete statement of a declaration at e4809cf under matching definitions. This covers Theorems A, B, 3.1, 3.2 and 4.1, Proposition 2.1, and the inline claims at lines 86, 216, 226 and 308. The base-48 claim, the one-axis sum and the binary-square profile are not in `check.lean`'s axiom audit (see m5). The label for the Vandehey step at line 600 is inaccurate (M2).

### 5. Overlap with Mira Cult's S08, and comparisons with the literature

**What S08 states.** Revision 41b5a78 is the only revision of the gist, committed 2026-10-07 16:31:31 UTC.

- **Theorem 1.1(a).** For x = Σ_(k≥1) q^(−k) b^(−c^k), with q > 2 and a prime p such that p | c, p | q and p ∤ b, every nonconstant P ∈ ℚ[T] gives a base-b normal P(x).
- **Theorem 1.1(b).** For each m there are effective κ > 0 and C with D*_N(x, …, x^m) ≤ C N^(−κ) for every N ≥ 2.
- **Corollary 1.2.** It states the ordinary case explicitly: if c ≥ 3 and (b, c) = 1, then (α, …, α^m) is jointly normal for every m.
- **Corollary 1.3.** Under Theorem 1.1, polynomial vectors are jointly normal exactly when the polynomials are linearly independent modulo constants.
- **Proof.** It uses Vandehey's Corollary 1.2, the nonintegrality of a cyclotomic tail, monic polynomials F_(d,n), a high/low index split with guard intervals [h, h + m c^(K−R)], and Erdős–Turán–Koksma.
- **Status.** "Conventional proofs; not formally verified or externally refereed." S08 says nothing about Lean, and its hypothesis excludes q = 2.

**Accuracy of the credit.** The paper's description (lines 70–81) is accurate:

- q = c gives Theorem A.
- Projection gives Theorem B. The projection is from Corollary 1.2, which is the cleaner source.
- "Both arguments evaluate at a nonintegral algebraic tail" is fair.
- The contrast at lines 75–77 (guard intervals in S08 versus inclusion–exclusion on every reflected upper set here) is fair and not overstated.
- The claimed remaining differences are fair: a complete Lean proof, the variant mass argument with compactness, and the parameter-two material (§§3–5), which S08 does not cover.
- LEDGER.md correctly records S08's Corollaries 1.2–1.3, its use of Vandehey's Corollary 1.2, and its exclusion of q = 2.

**Prominence of the credit.** The abstract credits S08 in its second sentence (lines 15–17), which is good. In the body, however, Theorems A and B are stated (lines 37–49) as unattributed main theorems. The credit appears only in the "Antecedents" paragraph that follows them. S08 Theorem 1.1(b) already gives an effective power saving. The abstract (line 20) and §6 present the effective rate without saying this. The intro (lines 72–73) does mention it. See M1.

**Other comparisons:**

- **Bailey–Crandall.** Corollary 4.9(i) (p. 536) covers coprime b, c > 1, *including c = 2*. Theorem 2.2(9) is the Erdős–Turán inequality on pp. 529–530. The rate D_N < C log² N/√N appears after Theorem 4.8 on p. 535, for the generator's PRNG sequence. The paper's statements at lines 60 and 87–89, and the use at line 630, are accurate. On "unnormalized" see e5.
- **Bailey–Borwein.** Theorem 2 gives nonnormality in radices B = b^p c^q r. "Certain other radices" (lines 82–83) is accurate.
- **Coons.** Corollary A.3 of v2 (28 November 2013) gives transcendence for all b, c ≥ 2. Accurate.
- **Kano–Shiokawa.** Condition (15) is λ_n/μ_(n−1) → ∞ and (16) is (log μ_n)/λ_n → ∞ (preprint p. 12). For λ_j = j and μ_j = c^j, the ratios are j/c^(j−1) and log c, so both conditions fail. Lines 63–65 are accurate. Wagner's conditions, as quoted by Kano–Shiokawa on p. 11, differ but also require divergence.
- **Vandehey.** Accurate, apart from M2.
- **Mira's earlier work.** The September archive (S07: the single series Σ D^(−j) b^(−C^j); S09: joint normality of L_(p,s)) and the November note (linear only; it has an explicit section "No nonlinear or absolute normality claim") contain no polynomial-image result. The description at lines 78–80 is fair.

### 6. Bibliography

I checked 12 entries against Crossref, the publisher or repository record, or the primary PDF:

| Key | Result |
| --- | --- |
| `stoneham` | Correct. Crossref gives issue print date 1972 and online date 1973. The usual citation "22 (1973)" is acceptable. |
| `korobov` (A. N.) | Correct (Math. Notes 47(2), 128–132). |
| `kano` | Correct. The DOI 10.18910/10356 resolves via handle 11094/10356 to Osaka J. Math. 30(4), 909–919. |
| `bc` | Correct; content checked in the PDF. |
| `wagner` | Correct. |
| `ks` | Correct; conditions checked in the scan. |
| `vandehey` | Correct. arXiv has only v1, with no journal reference, so the preprint numbering is the right choice; the journal record matches. |
| `bb` | Correct; Theorem 2 checked. |
| `coons` | Correct; Corollary A.3 checked in v2. |
| `ns` | Correct. |
| `bugeaud` | Correct (CUP, Cambridge Tracts 193, 2012). I could not check the content of §5.1. |
| `jointkorobov` | Not verified: mathnet.ru refused connections. The metadata look plausible. |
| `mira`, `mira2` | Revisions and dates confirmed (October gist). |
| `archive` | The repository's own v1.1. It has no `author` field (see m7). |

### 7. Exposition and PDF

The PDF builds cleanly and looks professional. The body avoids phase or track names; file names appear only inside link targets. The exposition, however, is far too dense, and it uses many project-coined terms without definition (M3).

### 8. Submission files

The abstract (146 words), alphaxiv.md, summary.md and reviewer-packet.md are accurate and do not overclaim. The reviewer packet states plainly that "the contribution here is its formal verification". The AI-use disclosure in `paper.tex` and alphaxiv.md is the standard wording verbatim. The X post is 245 characters.

Given the S08 overlap, the announcement is broadly appropriate: both texts call the result a Lean proof of Mira Cult's ordinary case. Its opening clauses, however, still headline the theorem itself, it uses a rhetorical hook, and it does not mention AI assistance (m8).

## Numbered findings

### Major

**M1. The theorem headings and opening sentences do not attribute Theorems A and B (and the effectiveness in Theorem 6.1) to S08.**

- **Location:** lines 13–17 (abstract), 37–49, 70–81; line 20 and §6, lines 556–572; `metadata.toml` abstract and `submission/abstract.txt`.
- **Problem:** The credit is accurate, but a reader of the theorem statements sees two unattributed main theorems. S08 Corollary 1.2 states the ordinary case, joint powers included, verbatim. S08 Theorem 1.1(b) already gives an effective power saving for (α, …, α^m), from which a scalar power saving for P(α) follows. The paper's effectiveness claim is new only in its explicit exponent δ_d.
- **Fix:**
  - Head the theorems as "Theorem A (Mira Cult [S08, Thm 1.1(a)], case q = c)" and "Theorem B ([S08, Cor. 1.2])".
  - Open §1 with one sentence stating that A and B are known (S08, unrefereed), and that the contributions here are the kernel-checked proof, the inclusion–exclusion mass argument, and §§3–6.
  - Rephrase the abstract's first sentence, e.g. "Mira Cult (2026) showed that …; we give a kernel-verified proof …".
  - In the abstract and at the start of §6, write "an explicit exponent δ_d (S08 Thm 1.1(b) gives an unspecified effective saving)".

**M2. The Vandehey step is labelled *External input*, but it uses a repaired version of the preprint's proof.**

- **Location:** lines 600–618; `VERIFICATION.md` row 6.1 and "External analytic dependencies"; `submission/reviewer-packet.md`.
- **Problem:** As written, Theorem 5.1 takes Q to be the product of the whole prime set P in (12). Its proof needs m′ | m, which fails whenever P contains a prime not dividing m. Such moduli arise inside Vandehey's own induction step (11), not only after Fourier reduction. The paper correctly replaces Q by rad(m) and takes the maximum of the constants over the subsets of P. That makes the step a modification of the cited proof, not a black-box use of the stated theorem. The contract reserves *External input* for black-box use.
- **Fix:**
  - State the estimate as a lemma: "for every finite S coprime to b there are effective A_k(S), B_k(S) such that the bound holds for all m with supp(m) ⊆ S, all a coprime to m and all L ≥ 1".
  - Give its short proof: Vandehey's induction with Q replaced by rad(m), then (13) with 2 rad(m), then the maximum over supports.
  - Label it *Paper proof (modifying [Vandehey, proof of Thm 5.1, (12)–(13)])* and update VERIFICATION.md.
  - Check whether the J. Anal. Math. version already corrects (12), and cite it if so.

**M3. The exposition is too compressed and depends on undefined project terminology.**

- **Location:** throughout, especially lines 92–124, 155–194, 381–423, 431–451, 479–490 and 574–675.
- **Problem:** The contract requires all notation to be defined and the proofs to be complete. A specialist cannot follow the paper without the repository notes:
  - **Undefined terms:** "shifted prefix" (92), "shell" and "late shell" (99, 160), "insertion" (100, 179), "cut", "weak/strict cut" (208, 336), "loss" (160), "anchor" (156), "phase" (161), "deficit" (382, 446, 480), "live transition" and "absorbed constant" (390–391), "Hilbert series" (441), "resonant" (305), "orbit order" (479).
  - **Overloaded symbols:**
    - a: v_p(c) at line 110, the exponent in α^a at 174, the minimal vertices a_i at 141, the numerator and a_k in Vandehey at 602–607.
    - s: s(j) at 95, the vertex count at 141, v₂(b² − 1) − 1 at 289, s_i at 649.
    - L: the precision, L_N, the piece lengths L_i and Vandehey's length.
    - h: the period and the frequency.
    - c_i: multiplicities, clashing with the parameter c (482).
  - **Compressed proofs:** The proof of Theorem A packs the pole comparison, the radix-prime removal, the block decomposition and the Weyl argument into one 40-line paragraph. The certificate interpretation (381–423) is a sketch.
- **Fix:**
  - Add a short notation subsection after line 36 defining the shell k = ⌊log_c n⌋, insertion points, the shifted prefix R_P(n), cuts U_t, the mass and the loss.
  - Rename the clashing symbols (e.g. ν = v_p(c), multiplicities m_i, the period π, the frequency h).
  - Define "deficit" as the reflected coordinate vᵢ, and "Hilbert series" as Σ_(v∈U) z^|v|, before using them.
  - Split the proof of Theorem A into numbered lemmas: (i) reflection congruence; (ii) uniform loss bound; (iii) denominator growth; (iv) block equidistribution.
  - Give the branch-and-bound certificate as a stated algorithm with its correctness lemma.

### Minor

**m1. The theorem statements in §§4–5 rely on a standing assumption set in §3.**

- **Location:** lines 231, 345–349, 361–366, 426–429, 453–460, 492–507.
- **Problem:** The phrase "at α in base b" depends on "b ≥ 3 odd, α = α_(b,2)", which is fixed at line 231.
- **Fix:** Restate the hypothesis in every statement.

**m2. The nonresonant quadratic test is an unnumbered result.**

- **Location:** lines 288–304.
- **Problem:** Corollary 4.4 and Theorem 6.1 both depend on inequality (2), but the test that proves it has no number and no row in VERIFICATION.md.
- **Fix:** Make it Proposition 3.3 with the label *Lean-supported paper proof*, name the Lean steps (`normal_iff_upper_denominator`), and add a VERIFICATION row.

**m3. The labels and the abstract do not say that the extended degrees depend on a computer certificate.**

- **Location:** line 24 (abstract, "give all polynomial degrees"); lines 429 and 460.
- **Problem:** The labels on Theorem 4.3 and Corollary 4.4 do not mention the Python certificate. "Give" is vague.
- **Fix:**
  - Write "[Lean-supported paper proof; uses the finite certificate of Proposition 4.2]".
  - In the abstract, write "prove normality of all rational polynomials of degrees 3–120 and 128, and of degrees ep^r for sixteen pairs, by a written transfer from exact finite certificates".

**m4. Corollary 4.4 excludes constants only implicitly.**

- **Location:** lines 454–456.
- **Problem:** A constant in the span would violate the conclusion. It is excluded only because degree 0 is not on any list.
- **Fix:** Add "and the span contains no nonzero constant (equivalently, every pivot degree is positive)".

**m5. The body gives no declaration names, and the inline kernel claims are not audited.**

- **Location:** lines 50–51, 152, 259, 262, 285, 307, 357–358, 420–421, 468; lines 86, 216, 226; `check.lean`.
- **Problem:** The contract asks for the declaration name with each *Kernel-verified* label, but printed copies show only link text. The inline kernel claims at lines 86, 216 and 226 (`square_nonnormal_48`, `same_prime_sum_normal`, `StonehamSquare.exact_profile`) are not in `check.lean`'s axiom audit.
- **Fix:** Add a short table of declaration names to the "Formal verification" section, and add the three declarations to the `check.lean` audit list.

**m6. The companion manuscript is cited by title only.**

- **Location:** lines 314–316.
- **Fix:** Cite it as "in preparation", with its repository path and version, or drop the reference.

**m7. The bibliography has three gaps.**

- **Location:** `references.bib`.
- **Problem:**
  - `archive` has no author.
  - `jointkorobov` could not be verified by this reviewer.
  - `mira`/`mira2` give the author as "Mira Cult (Mira-acc)", which is fine but should be consistent across manuscripts.
- **Fix:**
  - Add `author = {Anderson, Christopher}` to `archive`, as required by the authorship rule.
  - Recheck `jointkorobov` on mathnet.ru or zbMATH, and record the result in the ledger.

**m8. The submission texts do not mention AI assistance.**

- **Location:** `submission/announcement.md`, `reviewer-inquiry.md`, `alphaxiv.md`.
- **Problem:**
  - Neither announcement text nor the inquiry drafts mention that the work is AI-assisted.
  - The forum paragraph opens with a rhetorical hook, and both texts headline the theorem before the attribution.
  - alphaxiv.md links `../VERIFICATION.md` without a pinned commit.
- **Fix:**
  - Begin the X post with "Lean 4 formalization of Mira Cult's theorem (S08): …", and add "AI-assisted; not peer reviewed" (still under 280 characters).
  - Replace the forum paragraph's opening question with a statement.
  - Add one sentence of AI disclosure to each inquiry.
  - Pin the VERIFICATION link once the release commit exists.

**m9. The priority search is thin.**

- **Location:** `LEDGER.md`, search record.
- **Problem:** zbMATH Open returned a challenge, Google Scholar a rate limit, and MathSciNet was not consulted. The "apparently new" status of Theorems 3.1, 3.2 and 5.1 rests on this limited search. For Theorem 5.1, the prefix-code and Kraft-budget literature was explicitly not searched.
- **Fix:** Repeat the zbMATH and MathSciNet searches, including Kraft-inequality and optimal prefix-code formulations for Theorem 5.1, before release.

**m10. Registry entry ST-33 is inconsistent with Theorem 5.1.** This finding concerns the registry, not the manuscript.

- **Location:** `docs/registry/ST.toml`, ST-33.
- **Problem:** ST-33 states J_d = [2 − 2^(1−r), 2 − 2^(−r)) for every d. The paper (lines 501–505) correctly gives [2 − 2^(1−r), 2) when d = 2^r − 1, and my computations for d = 3 and 7 confirm the paper.
- **Fix:** Correct ST-33 when the registry is next edited.

### Editorial

- **e1.** Line 387: replace `{a\choose m}` with `\binom{a}{m}`, which removes the only build warning.
- **e2.** Line 289: "with v₂(0) = ∞" belongs to v₂(2A + B) in (2) (resonance at 2A + B = 0), not to s; b² − 1 ≠ 0.
- **e3.** Lines 200–202: replace the remark on the "empty box convention in dimension zero" with "for m = 0 the statement is trivial".
- **e4.** Lines 126–130: state that H(U) is defined as a convergent series in ℚ_p (or in ℤ_p after embedding).
- **e5.** Line 629: Bailey–Crandall state the *normalized* Erdős–Turán inequality. Write "Erdős–Turán [Thm 2.2(9)], multiplied by T".
- **e6.** Line 53: write "Coons's Mahler-method argument [Cor. A.3 of the 2013 preprint]". The bracketed "preprint" currently reads oddly before the corollary number.
- **e7.** Lines 205–210: the c = 35 example would read better directly after Proposition 2.1, as an illustration of why only a *bounded* loss can be expected.
- **e8.** Line 92: define R_d(n) in words, "the rational number obtained from b^n α^d by keeping the tuples with s(j) ≤ n", before the display.

## Summary for the editor

Theorems A, B, 3.1, 3.2 and 4.1 and Proposition 2.1 are kernel-verified as stated. The parameter-two finite certificates reproduce. The written proofs I rederived (cyclic descent, F(d), the quadratic test and the rate margins) are correct. Theorems A and B are Mira Cult's S08 results specialized to q = c. The paper credits this accurately, but the attribution must also appear in the theorem headings and the abstract's first sentence. The Vandehey step must be presented as a repaired lemma. The exposition needs a notation section and lemma-level structure. Once these are done, I expect minor revision at most. Independent human specialist review is still outstanding.
