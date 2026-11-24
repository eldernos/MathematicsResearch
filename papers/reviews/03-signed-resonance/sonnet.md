# Independent review of Paper III, *Resonance and Discrepancy in Signed Stoneham Expansions*

- **Reviewer:** Claude Sonnet 5.5 (`claude-sonnet-5-5`), working as a model reviewer. This is an internal AI-assisted check, not external peer review.
- **Date:** 2026-11-24
- **Input revision:** `43bbe0e4edefc489582a759aadb3c26caf2328b0`, directory `papers/03-signed-resonance` (`paper.tex`, `paper.pdf`, `references.bib`, `CORRESPONDENCE.md`, `check.lean`, `figures/`). The manuscript and `NormalityChecker/` are byte-identical at `af93394` (the checkout where this report is committed).
- **Not read:** any other review of this paper, including `REVIEW.md` in the paper directory. Only `papers/reviews/README.md` was read, for the scope of the review.

## Verdict

I found **no mathematical error** in any stated theorem, and every proof step I re-derived held. The main weaknesses are in exposition, in how the manuscript positions itself against its sources, and in a few places where a published fact is attributed imprecisely.

Readiness: **ready for human mathematical reading after the Priority 1 and 2 edits below.** I would not circulate it externally before the unrefereed-source issue (F2), the de Bruijn attribution (F3) and the internal-project artefacts (F10) are fixed. All of these are small edits.

## What I checked, and how

1. **Lean.** The Lean tree at the input revision was built from a clean copy: `lake build` of the four modules that `check.lean` imports, with the package cache copied from the project checkout. `lake env lean papers/03-signed-resonance/check.lean` then ran cleanly. All 18 audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
   - I resolved all 12 `\source{…}{line}` links against `a09e011…`: each line is the stated `theorem` or `lemma`. Between `a09e011` and `43bbe0e`, `NormalityChecker/` changed only by two added files (`StonehamJoint.lean`, `StonehamStatements.lean`), so the cited declarations are unchanged.
   - I read the definitions: `radixDiscrepancy`, `frequency`, `shift`, `zeroDensity`, `regularPositions`, `jump`, `value`, `SuffixMaximal`, `historyValue`, and the statements of `cyclotomic_normal_iff`, `translated_limsup`, `attainable_discrepancy_iff`, `severe_normal_summands`, `irrational_iff_frequently_nonzero`. They match the manuscript, including position 0 being regular, the half-open intervals, the `Nat.log p (u/m)` form of `j_m(u)`, and ties at p = 2.
2. **Proofs.** I re-derived Lemmas 2, 4 and 5, Theorems 1, 3, 7, 10 and 11, and Propositions 6 and 9 line by line (details under "Verified" below).
3. **Numerics** (exact rational arithmetic, throwaway scripts, not committed):
   - b=2, p=3, phases (1,0): D_N(X) against Z(N)/N is 0.7022/0.7407 at N=81, 0.7386/0.7490 at N=729 and 0.2468/0.2497 at N=2187. For X+1/3: 0.4935 against 2/3·0.7490 = 0.4993 at N=729.
   - b=2, p=7, M={1,2,3}, v_m=m, U=6F: D_N(U) is 0.2148 at N=1029 (prediction Z_R(N)/N = 0.2216), 0.6610 at N=2401 (0.6664) and 0.6654 at N=16807 (0.6666). The limit 2/3 at N=7^{k+1} and the mass 2/9 at N=3·7^k are confirmed.
   - Table 1 values, the de Bruijn factors 2/5 and 229/1020, and D(Y+3^{-k}) = 1/(2·3^{k−1}) were recomputed by hand.
4. **Primary sources read** (not recalled from memory):
   - Kano, Osaka J. Math. 30 (1993), Introduction, Theorems 1–2, Remark 1.
   - Baiocchi–Komornik, arXiv:0710.3001, Theorem 2.5.
   - Kaneko–Steiner, arXiv:2310.05454, Theorem 1 and §4.1.
   - Carminati–Tiozzo, arXiv:1410.5761, the "bifurcation set" section and Lemma 5.
   - Allouche, arXiv:math/0612816, Introduction.
   - Vandehey, arXiv:1606.07911, §7.2.
   - The two-sum manuscript at the pinned `f4d3d1f`.
   - Search snippets only (not full texts) for Bailey–Borwein and for the de Bruijn/Good history.
5. **PDF.** I read all 11 pages as text and rendered pages 1, 6, 7 and 10 as images.

## Findings, ranked

### Priority 1 (affects how a mathematician will read or trust the paper)

**F1. The relation between the two families is stated in one vague sentence.** This is the question the paper turns on, and it is answered only by:
> "In \eqref{eq:F}, cancellations occur among completed insertions of different components. In \eqref{eq:X}, the successive jumps prescribe the residual numerator on each shell. These mechanisms give different tests for vanishing. Both leave a rational radix orbit on the remaining positions." (§1, after (4))

The proofs make the difference precise, and the paper should say so in about five sentences.

| | Finite family F (Thm 3) | Signed expansion X (Thm 1) |
|---|---|---|
| Residual numerator on a cell or shell | W_u = D·p^E·P_u(w) ∈ ℤ_p, with w the Teichmüller lift of b⁻¹ (eq. (5)) | c_j/p^j · b^{n−p^j} (Lemma 4) |
| Resonant when | Φ_d divides P_u, d = ord_p(b): a ℚ-linear cancellation across components that depends on b | c_j = 0 (no cancellation is possible with the single multiplier m = 1; b does not enter) |
| Non-resonant | W_u ≠ 0 has fixed finite valuation, so denominator ≍ p^k | c_j ≠ 0 forces denominator ≥ p^j/C, so a bounded loss even when p ∣ c_j |
| Pattern of resonant cells | finite, so ρ = \|R\|/((p−1)S) is rational | arbitrary bounded sequence, whence the whole spectrum 𝒮_p |

A constant-phase X is itself a rational translate of one Stoneham-type component: c_j ≡ 1 gives X = p/b − (p−1)T_{b,p,1}. This is a useful consistency check for readers.

*Suggested replacement for the quoted sentences:*
> "Both families leave, on each shell or cell, a rational radix orbit whose denominator is comparable to the shell length, unless the residual numerator vanishes, in which case the completed part is integral and the shifted values accumulate at 0. In (4) the numerator is p-adic and its vanishing is a cyclotomic condition on a polynomial in w = b⁻¹; it depends on ord_p(b). In (1) it is the single integer c_j, and vanishing means c_j = 0 whatever b is."

The title says "signed Stoneham expansions", but the finite family (4) is not of the form (1) (its weights v_m are signed rationals, not integer jumps with a shell structure). One sentence in §1 saying that the paper has two parts sharing one lemma would help.

**F2. The two-sum manuscript is cited without saying that it answers the question affirmatively, and without flagging that it is unrefereed.** The §1 text, "Bailey and Borwein … asked about the sum of two standard Stoneham constants with the same construction base. The 2026 two-sum manuscript treats that question", never states the result. At the pinned `f4d3d1f`, that manuscript proves: for coprime c, d, the sum α_{b,c}+α_{b,d} **is normal in base b** (Theorem 1). A reader who then meets the abstract's "two positive normal summands whose irrational sum … nonnormal" may think there is a conflict.

There is none. In the appendix x = mT_{b,c,m} = b^{−m}+α_{b^m,c} and y = ℓT_{b,c,ℓ} = b^{−ℓ}+α_{b^ℓ,c}. They have different construction bases b^m and b^ℓ and the same c, so they are outside the question. Please:
- state this explicitly (one sentence in §1 and one in the appendix opening);
- mark the two-sum source "unrefereed manuscript" in the bibliography entry;
- remove or soften "treats that question" to "proves an affirmative answer".

The `howpublished` "Manuscript with Lean formalization, 9 September" with year 2026 should also give the author or repository name that the cited URL shows.

Related: **Theorem 11 is nearly a corollary of Theorem 3 when c is prime.** In the notation of §3, with v_m=m and v_ℓ=ℓ, P_u(Y) = Y^m/p^{j_m(u)} + Y^ℓ/p^{j_ℓ(u)}. For u ∈ [ℓ, c) the exponents agree and Φ_d ∣ Y^m(1+Y^{ℓ−m}) ⇔ b^{ℓ−m} ≡ −1 (mod p), which is exactly the hypothesis of Theorem 11. So Theorem 3 gives non-normality of the sum, and normality of each summand (|M| = 1), for prime c. What Theorem 11 adds is (i) composite odd c, (ii) a block frequency for the sum itself rather than for the integer-cleared U = (p−1)D·F, and (iii) the explicit threshold. A remark saying this would also answer why the appendix is not simply a corollary: Theorem 3 only controls U, and the passage from U back to F loses the numerical frequency (the manuscript says this in §4, but not here).

**F3. de Bruijn attribution is wrong for general radix.** Proposition 9 invokes an Euler circuit "including the one-vertex case h=1 \cite{debruijn}" for an arbitrary base b. N. G. de Bruijn's 1946 note (*Proc. Kon. Ned. Akad. Wet.* 49, 758–764) treats the binary count. The general-alphabet existence by Euler circuits is I. J. Good, "Normal recurring decimals", *J. London Math. Soc.* 21 (1946), 167–169, and the general count is van Aardenne-Ehrenfest and de Bruijn (1951). (This attribution comes from search-result summaries, not from the papers; please check the references.)

This is not only a citation repair. Good's title names the object the proposition uses: a rational whose periodic expansion contains every h-block once is a "normal recurring decimal". Cite Good as the antecedent of r = A/(b^L−1), and cite Good and the 1951 paper for the circuit.

**F4. "Invariance of base-b normality under nonzero integer multiplication" (end of Theorem 3's proof) is the wrong statement.** The proof must pass from U = (p−1)D·F to F, that is, **division** by an integer. Wall's theorem (the cited thesis) is for multiplication by a nonzero **rational**. Replace "nonzero integer" by "nonzero rational". Lean uses `normal_mul_nat_iff`, an iff, so the formal side is fine.

The introduction also asserts "x is normal in base b if and only if D_∞(x)=0" with a two-line argument. The standard references (Bailey–Crandall Theorem 2.2, as used in Vandehey §7.2; Kuipers–Niederreiter) should be cited. The Berkeley catalogue link for Wall's thesis is a weak locator; a textbook source for Wall's theorem would be better.

### Priority 2 (accuracy of attributions and of what is claimed as new)

**F5. Attributions that are accurate but imprecise, and one unstated overlap.**
- *Kano.* Verified: Theorem 1 gives x = ΣA_n/(a^{λ_n}b^{μ_n}) normal to base b under λ_{n+1}>λ_n, μ_{n+1}>μ_n, a^{λ_n} ≪ μ_n, |A_n| ≪ a^{λ_n} and a^{λ_n−λ_{n−1}} ∤ A_n. With λ_j=j, μ_j=p^j, A_j=a_j the last condition reads p ∤ c_j, as the paper says. **Theorem 2** (same hypotheses plus liminf μ_{n+1}/μ_n > 1 and limsup < ∞) also gives non-Liouville and transcendental, via a Ridout-type lemma. So for p ∤ c_j eventually, transcendence of X is already Kano's. Theorem 10 should say that it extends this to phases divisible by p and to arbitrary bounded phases. The current sentence "Kano also uses lacunary partial sums and restricted denominators" understates the overlap.
- *Stoneham 1970.* "unit numerators Z_j" is imprecise. Per Kano's summary, Stoneham's Theorem 1 takes positive integers Z_n < a^{α_n} with (Z_n, a) = 1 and positions determined by S(n,a) = Σα_iτ_b(a^i) (τ_b is the multiplicative order). Say "numerators Z_j prime to p" and "multiplicative periods τ_b(p^i)". By Kano's Lemma 1, τ_b(a^n) = C·a^n eventually, which is why p^j insertions here are the same scale but not the same numbers.
- *Vandehey.* "relates incomplete modular orbits to sufficient normality conditions in [§7]" is vague. §7.2, Theorem 7.4, is a Bailey–Crandall-type theorem for Σ 1/(c_k b^{m_k}) with c_k ∣ c_{k+1}, prime support in a finite set coprime to b, and a growth condition on the gaps. That is the closest published relative of Lemma 2, and it should be named as such.
- *Roth.* Theorem 10's proof invokes Roth for p > 2 and Ridout for all p ≥ 2. Ridout's theorem (exponent μ > 1 for denominators with prime support in a fixed finite set) already covers every p, since 1 < μ < p is allowed. Roth is redundant; drop it and "Roth and Ridout are external inputs" becomes "Ridout's theorem is an external input".
- *Hot spots.* My recollection, which I have **not** verified, is that Bailey and Misiurewicz ("A strong hot spot theorem", *Proc. AMS* 134 (2006)) prove an atomic hot spot at 0 for α_{2,3} in base 6, the same phenomenon as the atom at 0 on resonant cells. If correct, it is the natural precedent for "resonance ⇒ atom at 0" and should be cited.

**F6. Equation (7) is the weakest-supported statement, though numerically correct.** It is labelled "a paper deduction", and its proof is three sentences: "(5) gives an integral comparison on resonant cells and a denominator comparable to p^k on every other cell … There are only finitely many cell types." I confirmed the statement numerically (above), and the ingredients exist: non-resonant orbit denominators lie between p^k/C′ and p^k by the same argument as Theorem 1 with q_0 and m, and Lemma 2 plus Lemma 5 close the argument. But it is used for the headline example D_∞(6F) = 2/3. Promote it to a proposition with a short proof, or at least write the two-line denominator bound. The sentence "Recovering a numerical discrepancy after division requires the residues of the integral comparison points modulo the divisor." is opaque; say plainly that D_∞(F) itself is not obtained, because dividing U by (p−1)D reduces the cell orbits modulo that divisor, and cite what extra data would be needed.

**F7. Hypotheses that are used but not explained.**
- Theorem 3 assumes p **odd**. The proof does not visibly use oddness (Lemma 2 handles 2; d = 1 for p = 2). If it is a formalization artefact, say so; if it is mathematical, say where it is used. This matters for the abstract's "one odd prime parameter".
- Theorem 1 needs p **prime**, and Lemma 4 depends on it: Euler's φ(p^j) divides p^j(p−1) only for prime p. For p = 15, b = 2, one has 2^{15·14} ≢ 1 (mod 15), since the order of 2 mod 15 is 4 and 4 ∤ 210. So the remark that irrationality and transcendence hold for composite p (Theorem 10) is the only composite-p statement; the paper should say that the discrepancy results do not extend by this argument.
- "For each admissible b,p" (Theorem 7) uses "admissible" without a definition. Define it once in §1 (b ≥ 2, p prime, p ∤ b).
- The spectrum 𝒮_p is independent of b; the abstract and Theorem 7 should say so in words.

**F8. Eventually periodic case (end of the proof of Proposition 6).** "The same proof applies when only the zero pattern is eventually periodic, since a finite change of bits changes Z(N) by a bounded amount." True, but the formula has M_r and A computed from index 0. Either state the eventually periodic version (tail data M, A, r relative to the preperiod) or delete the sentence. It is used in the manuscript's own correspondence file as "derived in the manuscript".

### Priority 3 (notation, small errors of presentation)

**F9. Notation is overloaded in ways that cost the reader.**
- `D`: the discrepancy 𝒟(μ), D_N(x), D_∞(x), and the integer D = ∏den(v_m/m) in Theorem 3.
- `M`: the set of multipliers (§1, §3) and the integer M_j = Z(p^j) (§5).
- `R`: the resonant set (§3), the partial sums R_j (§4) and ℝ.
- `d`: ord_p(b) (§3), the interval end in 𝒟, the order k+1 in the appendix (ℓ = 2d+1).
- `S`: the cell-range integer (§3) and the spectrum 𝒮_p.
- `t`: ord_q(b) in Lemma 2's proof, then the integer t ≥ 2 in "(b,t)=1 and t≥2" (§6).
- `Y`: used in §6 ("the same binary alternating example Y", "X′ = 9Y + 3/8", "Y+3^{−k}") without ever being defined. It is the Table 1 row (1,0). Define it.

Suggested renames: D → Q (denominator clearing), M_j → Z_j (zero count; note z_j already exists), R_j → B_j, ord order d → h, t (ord in Lemma 2) → τ.

**F10. Internal project artefacts appear in a manuscript meant for readers outside the project.**
- The verification table prints registry labels: "Theorem 3 (CR-01)", "(DS-01, DS-03)", "(DS-02)", "(DS-04)". These are meaningless to anyone but the repository's authors.
- "Checkpoint 11, revision `a09e011720bc`", and URLs naming the repository owner: fine for the repository, awkward in a paper.
- "From the manuscript directory, run `python3 figures/generate.py` and `latexmk -pdf paper.tex`. The figure data, Lean correspondence checks and literature search record accompany the source." This belongs in the repository README, not the paper.
- "paper deduction" (in §4 and in the table) is project jargon; say "proved in this paper and not formalized".
- The **AI assistance** paragraph says an AI assistant "drafted the exposition, checked it against the cited declarations, and prepared the figures. Authorship and submission decisions rest with the project owner", yet `\author{}` is empty. A manuscript needs a named, accountable author. Keep the disclosure, but move it to an acknowledgement and name the author.
- The Lean evidence is pinned to `a09e011`, an older commit than the manuscript's own revision. I confirmed the cited declarations are unchanged to `43bbe0e`. A sentence in the paper or the correspondence note saying so would remove an obvious reader question.

**F11. Smaller mathematical or presentational points.**
- Lemma 2 is stated for interval counts, but Theorem 3 uses "Lemma 2 gives character sums o(p^k)". The proof establishes `|S(hA)| = o(q)` before deducing counts, so state the character-sum bound as part (a) of the lemma, intervals as (b). (The relation also needs the case where hA is not a unit mod q; the proof handles it, by distinctness of hAb^j via q > |h|b^H, but a reader will want it said.)
- In Theorem 3's proof, the displayed claim b^{p^j}w ≡ 1 (mod p^j) is correct, and in fact the stronger mod p^{j+1} holds (since w^{p^j} = w). No change is needed; the stronger statement is a free remark if desired.
- Theorem 7: "At p = 2, one suffix-maximal representation suffices at a dyadic endpoint." This sentence is cryptic. My reading: at p = 2, V_2 is not injective (0111… and 1000… have the same value), and only the terminating-in-zeros representative is suffix-maximal (a word ending in 1^∞ is suffix-maximal only if it is 1^∞ itself). If so, say exactly that, or delete.
- Corollary 8's proof, second paragraph. "In comparing a shifted truncation with the unshifted one, an earlier first difference retains its sign, and past the shifted cut the remaining digits on that side are zero." is correct but compressed to the point of being a puzzle. Rewrite with the two cases: let s^{(n)} = s_0…s_{n−1}0^∞ and let σ^h s^{(n)} = s_h…s_{n−1}0^∞. Either the first difference between σ^h s and s lies inside the first n−h digits, in which case σ^h s^{(n)} < s^{(n)}, or s_h…s_{n−1} = s_0…s_{n−h−1}, and then σ^h s^{(n)} = s_0…s_{n−h−1}0^∞ ≤ s^{(n)}. The following sentences ("At the block end the periodic history contains all its ones and further ones in the periodic tail. Its value is strictly greater while the error tends to zero.") should be unpacked in the same way; they carry the claim "zero is the only isolated point".
- Figure 2's caption says the gap above 0 is "at least 1−1/p in each row; Corollary 8 gives its exact length". Corollary 8 says the smallest positive element is **exactly** 1−1/p, so "at least" is wrong or at best circular. Write "The smallest positive value is exactly 1−1/p (Corollary 8)".
- §6: "Thus for each fixed signed expansion X with D_∞(X) > 0, the translates … have strictly positive upper discrepancies tending to zero." The abstract claims *transcendental* examples. That holds only if X has infinitely many nonzero phases (an X with eventually zero phases is rational, and so are all its translates). Say it in the proposition or the sentence after.
- The citation "Carminati and Tiozzo [§2]": the identity is correct and I verified it (their characterization U = {t∈[0,1] : g^k(t) ∉ (0,t) for all k ≥ 0}, Lemma 5), but in arXiv v2 the section is headed "The bifurcation set" and has no number. Cite "the bifurcation set U and Lemma 5".
- The Kaneko–Steiner citation is accurate: Theorem 1 gives L_≤ = M_≤ = closure of periodic sup-words, and §4.1 gives 10^∞ = min M \ {0^∞}. Note that Theorem 7's first half (the limit-word argument) is a reverse-history analogue of their L_≤ = M_≤. Say so, for it is the exact point on which the "limsup over all prefixes" equals a "sup over suffixes".
- "Baiocchi and Komornik's Theorem 2.5(a) identifies the infinite expansions of one … as the quasi-greedy expansions of one in varying bases": verified. **"Allouche's univoque condition also constrains the complemented word"** is not clear and, from the paper I read, inexact: Allouche's set is Γ = {u : u ≤ S^k u ≤ ū} (kneading sequences of unimodal maps, Cosnard), with the complement ū as the upper bound. This sentence should be deleted or replaced by that exact statement. Parry + Baiocchi–Komornik + Allouche + Kaneko–Steiner in one paragraph is four citations for one fact (suffix-maximal words are quasi-greedy expansions of 1); Kaneko–Steiner §4.1 already states it with Parry's attribution.

## Verified (no change needed)

- **Definitions and basic facts.** D_N includes n = 0; normality ⇔ D_∞ = 0; Lemma 4 (telescoped residue c_j b^{n−p^j}/p^j mod 1, error bound (p+1)C/((b−1)p^{j+1}), denominator p^j/gcd(p^j, c_j)); Lemma 5 (including the wrapping-arc complement argument and ε ↓ δ).
- **Lemma 2.** Lifting the exponent (with g ≡ 1 mod 4 at 2), q ∣ (g−1)t, orthogonality Σ|S|² = qU, the distinct-residue choice via q > |h|b^H, and the window shift by ≤ 2j terms. The interval step is standard.
- **Theorem 1.** The comparison points, the denominator bounds p^j/(C|m|q_0) ≤ q ≤ q_0p^j, the mixture identity (the discrepancy of (1−θ)λ+θν is exactly θ·𝒟(ν)), and the product statement. The apparent conflict for eventually-zero phases (X rational but D_∞ = 1) resolves correctly: c_{J+1} = 0 makes b^nX integral eventually, so d_b(X) = 1.
- **Theorem 3.** The cell computation B_n ≡ −b^nW_u, W_u = Dp^E P_u(w); tail ≤ p^{−k}Σ|g_m|; the resonant count |R|(p^k−1)/(p−1); both examples (exceptional weights {2, 2/3}; p = 7, R = {3,4,5,6}, ρ = 2/9 at N = 3·7^k and 2/3 at N = 7^{k+1}); the Y^d−1 implementation remark.
- **Section 5.** The H_j recurrence; Proposition 6 in both closed forms; all six rational entries of Table 1; the d_2(1/3) = 2/3 argument; Theorem 7 both directions (including that V_p is continuous and monotone, with a tie only at p = 2); compactness and the minimum 1−1/p; the truncation-preserves-admissibility argument.
- **Section 6.** Proposition 9 and its oscillation formula (the maximum of the right limits minus the minimum of the left values, using ×b^h as a permutation of the orbit); the numbers 2/5, 229/1020, 229/1360; D_∞(Y+3^{−k}) = 1/(2·3^{k−1}) via ord_{3^k}(2) = 2·3^{k−1}; the 9Y + 3/8 example; Theorem 10 (irrationality, the tail bound, Ridout).
- **Appendix.** The hypothesis c ∣ b^{ℓ−m}+1 gives (b,c) = 1; c^{j+1} ∣ B^{c^j}+1 by induction (c odd); the tail interval (0, 2/((c−1)c^k)]; the limit (c−ℓ)/(c−1); the choice m = 1, ℓ = 2d+1, c the odd part of b^{2d}+1 (odd or even b); positivity of the tail giving irrationality.
- **Claims about the literature that checked out.** Kano's Theorems 1–2 as described; Wagner's and Kano–Shiokawa's rings (nonzero elements normal to base b and nonnormal to base ab, with arithmetic conditions on generators); Baiocchi–Komornik Theorem 2.5(a); Kaneko–Steiner Theorem 1 and §4.1; Carminati–Tiozzo characterization of U.

## Scope of what the Lean evidence supports

- Formally verified and correctly matched: Theorem 1 (both parts, and the product), Theorem 3 and its criterion for rational weights, Proposition 6 and Table 1, Theorem 7, Corollary 8, the bounds in Proposition 9 and the eight-cell example, Theorem 10's irrationality for prime p coprime to b, and Theorem 11.
- Paper-only (flagged correctly in `CORRESPONDENCE.md`): equation (7); the exact de Bruijn equality and strict bound; Theorem 10's composite-p extension and transcendence; the binary reflection to Carminati–Tiozzo; the eventually periodic case of Proposition 6; the numerical inverse-power factor in §6. Roth/Ridout are external. The paper's own table says the same, but F10 and F6 apply.

## PDF and figures

- 11 pages, letter size, standard Latin Modern, no unresolved references (`??` absent), numbered equations (1)–(8) used consistently, shared counter for theorems, readable at normal zoom. The pdf trailer id is neutralised for reproducibility. No author and no date, which F10 raises.
- **Figure 1** (page 6) is clean: solid blue and dashed ochre differ by line style as well as colour, so it works in greyscale; the shading marks zero shells; the right-hand labels avoid a legend box. Two improvements: (i) the y-axis has no label, and it plots Z(N)/N and (2/3)Z(N)/N, which are the **main terms of Theorem 1, not D_N itself**. A reader might think the picture shows discrepancies. My exact computation shows D_N is within about 0.01 of these curves already at N = 729 (see above), so overlaying exact D_N would turn the figure from an illustration into evidence. (ii) The caption's "The curves join sampled values" is fine but belongs before the claim "The peaks tend to 3/4 and 1/2".
- **Figure 2** (page 7) is too small to read: the ticks are 1–2 pt marks and the right-hand clusters merge. The labels 0, 1/4, 1/2, 3/4, 1 are adequate, but nothing marks the gap or the first tick (1−1/p), which is the one feature the text discusses. Annotate the first tick and the gap, enlarge the row height, or show only p = 2 with the p = 3 row as an inset. See also the caption error under F11.
- There is no illustration for Theorem 3's flagship example (p = 7, R = {3,4,5,6}). A short strip showing which of the cells u ∈ [3,21) are resonant would make the cyclotomic condition visible; it is a three-line extension of `figures/generate.py`.
- Hyperlinks (blue, colourlinks) are legible. The verification table at the end is clear; its link labels are descriptive. F10 applies to its first column.
- I could not rebuild the PDF (no TeX Live in this environment), so I confirmed only that the text of `paper.pdf` corresponds to `paper.tex` by reading both; I did not test that `figures/generate.py` reproduces `prefix.tex` and `spectrum.tex` byte for byte.

## Exposition: where the prose should be cut or rewritten

Overall the prose is compact and mathematical. The manuscript has no promotional language and few connectives to prune (Thus ×10, Indeed ×5, Hence ×3). The problems are concentrated in a handful of sentences that gesture at an argument without giving it, which is what reads as machine-written.

| Location | Quoted text | Problem | Suggested edit |
|---|---|---|---|
| Abstract, last sentence | "We also give, in each radix, two positive normal summands whose irrational sum has arbitrarily high upper frequencies of zero blocks." | Reads as an afterthought; "upper frequencies of zero blocks" is ambiguous, and nothing says these summands are of different construction bases. | "For every radix b and every η < 1 we exhibit two positive normal numbers of Stoneham type whose irrational sum has, for every h, upper frequency greater than η of the block 0^h." |
| §1 after (4) | "These mechanisms give different tests for vanishing. Both leave a rational radix orbit on the remaining positions." | Vague (F1). | See F1. |
| §1 | "Here bounded nonzero phases may be divisible by p, and recurring zero phases give a quantitative obstruction." | "Here" is ambiguous (this paper? Theorem 1?) and "quantitative obstruction" is undefined at this point. | "Theorem 1 allows nonzero phases divisible by p, and shows that recurring zero phases force D_∞(X) ≥ (p−1)/p." |
| §4 before Lemma 5 | "A small signed error at a rational atom can change the frequency of an interval ending there. Extreme discrepancy nevertheless admits the following estimate." | "nevertheless" is conversational. | Put the sentence into a remark after the lemma, or write: "Interval counts are unstable under perturbation at an atom, but discrepancy is not." |
| §4 after Thm 1 | "The upper bound arising from the count of uncontrolled positions alone would prove only D_N(X) ≤ θ_N + o(1). Equality here uses their concentration at one circle point. In a sufficient normality test without such information, failure of a denominator condition supplies neither a lower bound nor a proof of nonnormality." | The last sentence is cryptic and defensive. | Cut the third sentence. Keep: "Without the concentration of the zero-shell points at a single point, the same method would give only D_N(X) ≤ θ_N + o(1)." |
| §4 | "The same argument identifies the quantitative connection with Theorem 3 … the following is a paper deduction:" | "identifies the quantitative connection" is empty; "paper deduction" is jargon (F10). | "The same method gives an all-cutoff formula for the integer-cleared sum U of Theorem 3; we prove it here without formalization:" |
| §4 end | "Recovering a numerical discrepancy after division requires the residues of the integral comparison points modulo the divisor." | Opaque (F6). | "We do not obtain D_∞(F) itself from this, only D_∞(mU + r)." |
| Thm 7 | "At p = 2, one suffix-maximal representation suffices at a dyadic endpoint." | Cryptic (F11). | Rewrite or delete. |
| §5 proof of Thm 7 | "At the first differing digit the gain from a 1 dominates the entire possible later loss, with a tie possible at p = 2." | Correct; slightly awkward. | "At the first index where two words differ, the digit 1 gains (p−1)p^{−(k+1)}; the remaining digits can lose at most p^{−(k+1)}, with equality only for p = 2." |
| Cor 8 proof | "In comparing a shifted truncation …" | F11. | Use the two cases above. |
| §5 closing | "Parry characterized admissible β-expansions … Allouche's univoque condition also constrains the complemented word." | Citation list without content (F5, F11). | One sentence with Kaneko–Steiner §4.1 (which cites Parry), and the Carminati–Tiozzo identification. |
| §6 | "Altering c_0 by one adds 1/2−1/8 = 3/8 when b=2, p=3. Hence X′=9Y+3/8 is a signed expansion …" | Good example, but Y undefined (F9). | Define Y at the start of the paragraph. |
| §6 | "De Bruijn blocks also appear in constructions of infinite normal words and estimates for their discrepancy \cite{bcarton}. Here one finite cycle supplies the factor of a positive upper discrepancy." | Fine. | Add Good 1946 here (F3). |
| Appendix | "For large h it exceeds the normal frequency b^{−h}." | Obvious; fine but trivial. | Keep or cut. |
| End matter | "From the manuscript directory, run `python3 figures/generate.py` …"; "literature search record accompany the source"; CR-/DS- codes | F10. | Move to the repository README. |

## Limits of this review

- I did not rebuild the PDF or test the figure generator (no TeX toolchain available); I did not read Stoneham 1970, Wagner 1995, Kano–Shiokawa 1993 or Becher–Carton 2019 in full. For Stoneham I relied on Kano's own summary of his Theorem 1; for Wagner and Kano–Shiokawa on Kano's introduction; for Bailey–Borwein on abstract-level search results; for the de Bruijn/Good history on search summaries (F3 should be confirmed against the papers).
- I did not verify the Bailey–Misiurewicz recollection in F5, nor the exact page ranges of bibliography entries beyond the DOIs.
- I did not independently re-run `lake build` for the full library at `43bbe0e`; I built the modules `check.lean` imports (7,719 jobs), which is sufficient for the audit of the 18 declarations but not a replacement for the project's own verification script.
- I did not assess the other manuscripts or the second half of the repository's documentation. The "novelty" assessment is limited to the sources named above; I found no earlier paper that determines D_N at all prefixes for these expansions, but I did not do an exhaustive literature search.
- This is a model review. It does not replace refereeing, and the decisions on F1–F11 belong to the author.
