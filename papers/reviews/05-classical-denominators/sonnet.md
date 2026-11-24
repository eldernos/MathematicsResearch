# Paper V review: Reduced denominators of binary logarithm and arctangent series

Reviewer: Claude Sonnet 5.5 (`claude-sonnet-5-5`)
Reviewed revision: `28186f0e08ea889827b489f03f1c213456581c91`, `papers/05-classical-denominators`
Date: 24 November 2026

## Verdict

I found no mathematical error in the statements I checked. The main results are correct as stated: the half-length denominator theorem, the band formula, the Bang optimality theorem, the beta-integral corrections, the uniform diagonal estimates and the 18-changes example. The paper is suitable for review by a human number theorist after the exposition changes below. It reads as an unfocused miscellany, and its prose has several conversational and vague passages. Sections 1–3 are the publishable core. Sections 4–8 should be trimmed, split or clearly labelled secondary before submission.

Severity key: **S1** a mathematical error (none found). **S2** a scope, attribution or framing problem that could mislead an expert. **S3** exposition, notation or presentation.

## What I checked

### Read
- `paper.tex` (923 lines), the compiled `paper.pdf`, `CORRESPONDENCE.md`, `references.bib`, `figures/generate.py` and all figure and table data.
- The committed PDF has the same text as a fresh build from `paper.tex` with the portable TinyTeX. There are 14 pages, no undefined references and only two harmless underfull boxes.
- I did not read `REVIEW.md` in the paper directory, in case it is a review of this paper. I read no other review of Paper V.

### Independent computation
I wrote my own exact-arithmetic code for these checks. It does not import the authors' scripts.

| Claim | Check | Result |
| --- | --- | --- |
| Thm 1.1 | Exact `Y_N` for all `N<200` and `N=400,777`: `0 ≤ 2^N log2 − Y_N ≤ 4/(N+1)`, `den(Y_N) | L_{⌊N/2⌋}`. Same for `R_N` with bound `1/(N+1)`. | passes |
| Thm 1.1 | Grouped weights `(0,4,3,4,0,1)` reproduce `Y_N`. `Y_10=10646/15` and `R_10=44711/63`. | passes |
| Prop 2.1 | Prime-power criterion for every odd prime and `3 ≤ N < 600`. | no failures |
| Prop 2.1 | Bound `log(L_N/q_N) ≤ 116 N^{2/3}`, `8 ≤ N < 1500`. | holds; observed maximum of the ratio is 0.79 |
| Thm 2.4 | Re-derived the valuation argument by hand: `2^k−1` = 1, 3, 7, 3·5, 31, 3²·7 for `k=1..6`. Obtain `b_5=b_4=0`, `b_3=−b_6`, `b_2=−2b_6`, `m=b_6−b_1`, `W=−b_1+b_6 w`. `P_v(w) ≥ 1/2` for `v ≥ 2`. | correct |
| Thm 3.1 | Exact `Z`, `η`, `K`, `M` for `N<70`, `0≤r,s≤6`. Verified `|2^N log2 − Z| ≤ η` and `den(Z) | K L_M`. | no failures |
| Cor 3.2 / Table 1 | Computed the thresholds for `F(1/2,ρ,3)`, `F(1/3,σ,9) ≥ α log2`. | the printed `ρ,σ` are the thresholds rounded up |
| Cor 3.2 / Table 1 | Computed `C` for the three rows, and re-ran the six integer comparisons `(b+j)^{b+j} d^j > 2^h b^b j^j`. | `C = 0.746089, 1.095662, 1.962602`, below the printed caps; all comparisons hold |
| Thm 4.2 | Exact `δ_n=(3/2)(−1)^n B(n,n)`, the recurrence for `U_n`, and `den(y_n) | L_{2n}` for `n<40`. Re-derived the polynomial-root argument, including the evaluation points `X=−h−1/2` and `X=−1`. | correct |
| Prop 5.1 | Local residue formula `L y_n ≡ (L/p) Σ a_{pi}/i (mod p)` for `n=7,12,20,33` and all `p>√(2n)`. `log H/√M ≈ 2` (2.05 at `n=1000`). | correct |
| Table 2 | Recomputed from scratch the four two-stride rows (`n=128..1024`) and the diagonal rows `n=64..512`: orders, bits, word counts, survivors. | all identical to the table; I did not re-run the diagonal row `n=1024` |
| Overlap example | Own enumeration over all `h=3,888,000` grid points. | `h=3,888,000`, `k=3,048,192`, `g=31,104` pairs, narrowness holds, 31,232 distinct words, minimum 18 changes with one word at 18, histogram identical to `overlap_words.csv` |
| Overlap example | Actual bits 514–577 of `log 2`. | the word lies in the admitted set and has **38** changes |
| Thm 6.3 | Exact Gaussian sums for `(a,c)=(1,1),(8,4),(2,3)`, `N ≤ 299`: error bound and `den | L_{M_2}`. Identities `tan(A+C)=1/2`, `tan(2A+C)=1`. | pass |
| Prop 6.2 | Decomposition `pV_m = G_m + pZ_m` and pair counts at gap `h ≤ 5` for `p ∈ {5,…,31}`, `k ∈ {1,3}` and `arctan(1/2)`. | counts `≤ h` (log), `≤ 2h` (arctan) |
| Prop 6.4 | Error bound `4/(15·60^n)` for `n<25`. Prime band `4n+3<p≤8n+1`, `p≡1,5 mod 8`, divides `den(V_n)`. | pass |
| Thm 7.1 | `A_{n+q} ≡ A_n (mod q)` for `q<60`. Least period equals `q` for nine tested `q`. Paired-zero bound `≤ h−1` for `p ≤ 31`, all `h`. | pass |

I also re-derived by hand, with no error found: the proofs of Thm 2.3 and Cor 2.2, the identity `2I_4−I_{−8}=log 2` and eq. (beta), `Prop 4.1`, the entropy count in `Prop 5.2`, `Prop 5.3`, the series for `b_t(v)` in Thm 6.3, the error integral in `Prop 6.4`, the Legendre-charge argument in Thm 7.1, and the discrepancy argument of `Prop 8.1`.

### Lean
- `NormalityChecker/` in the input tree is identical to the main checkout.
- All declarations linked in `CORRESPONDENCE.md` exist at exactly the cited line numbers. This covers every row, but I only spot-checked each statement against the paper.
- Statements read in full: `StrideDenominatorRate.log_denominator_rate`, `LogarithmBands.denominator_rate` (finite zero set, as stated), `DyadicRelations.coefficients_of_valuations` and `optimal_rate` (primitive divisors above 6 as a hypothesis, `R=1/2 ↔ a 1=0`), `CorrectedStrides.model`, `model_den` and `model_error` (matching `λ_2`, `λ_3`, `K`, `M`, `η`), `DiagonalNumerator.paired_residues` (hypotheses `3<p`, `0<h`, `2h<p`), `ResidueWindows.compatible_grid_differences` (narrowness `2η·lcm<1`) and `FactorialNumerators.paired_zeros`.
- `#print axioms` on 18 key declarations, run against the cached oleans, gives only `propext`, `Classical.choice` and `Quot.sound`.
- I did **not** run `lake build`, and I did not check how fresh the cache is.
- The manuscript links to `eldernos/MathematicsResearch@a09e011…`, an external tree. I could not examine it. Matching line numbers against the local source strongly suggests the same files, but the identity of that checkpoint is unconfirmed.

### References
- Web search confirms the bibliographic data for Takahashi (Ramanujan J. 51 (2020) 177–186), Adegoke–Lafont–Layeni (NNTDM 17(4) (2011) 18–32) and Berndt–Kim–Zaharescu (MRL 20(3) (2013) 429–448). The first author's name is "Sun Kim", which the bib writes correctly.
- **Not verified**, because I could not read the full texts:
  - Takahashi eqs (11)–(19).
  - Adegoke et al. eqs (28)–(29), and the "modulus `1/√2`" description.
  - BKZ `[Thm 1.6 and end of §4]`.
  - Shiu Thm 2.
  - Sondow–Schalm Prop A.5 and §3.
- These theorem-number citations must be checked against the sources by a human before release.

## Findings

### S2: scope, attribution and framing

1. **The binary-word exclusions give no information beyond direct computation of the digits.** The rational `Z` is known exactly, so the sieve discards information on purpose.
   - Table 2 ("Exact exclusions for `log 2`"), the abstract ("finite exclusions of binary words") and the 18-changes example read as results about `log 2`.
   - The actual 64-bit word has 38 changes. The conclusion "at least 18 changes" is weaker than the known digits.
   - The scope sentences (l. 464–465, 536–539, 596) are accurate. The distinction between the actual numerator and the possible lifted numerators is handled correctly: "passing only certifies compatibility", "every unresolved lift allowed", and Prop 5.2 averages over candidate residues.
   - Missing: one plain sentence in the abstract and at Table 2 saying the tests calibrate a method that uses only residues above a cutoff `y`, not that they establish new facts about the digits.
   - Rename the Table 2 caption "Exact exclusions for `log 2`" to something like "Binary words with few changes excluded by residues above `y`".

2. **Table 1 has no baseline, so its significance cannot be assessed.** The rates `C = 0.746, 1.096, 1.963` for `α = 1/2, 1, 2` are compared with nothing. A natural comparison is `2^{−αN} Y_{(1+α)N}`, with denominator dividing `2^{αN} L_{(1+α)N/2}` and rate `(1+α)/2 + α log 2 = 1.097, 1.693, 2.886`. The corrected form is better by more than 0.35 in every row. State a baseline column, with its definition, or drop the claim of an improvement.

3. **Theorem 7.1's density conclusion is subsumed by the paper's own remark.** Lines 778–794 deduce it from Berndt–Kim–Zaharescu with "a stronger exception count".
   - The abstract still lists "denominator estimates in moving windows for Taylor sums of `e`" as a result.
   - Recommend demoting Section 7 to a remark that derives the statement from BKZ, after the theorem numbers are verified. Keep only the elementary congruence lemma if something else uses it.
   - If the elementary route is kept, say why in one sentence: it is self-contained, and BKZ's methods differ.

4. **Prop 8.1 is stated only for `π` but the argument works for every irrational with a finite irrationality measure.** The `π` input `μ(π)<8` affects only the constant `8`. State it for any `x` with `μ(x)<∞`, with `π` as an instance, or the result looks more specific than it is. The deduction is short and probably folklore-level. Its novelty is low.

5. **The `log 2` finite-prefix estimate quoted in Section 8 contains a non-explicit constant.** "for some `K` and all `N ≥ 2`" is imprecise: say whether `K` is absolute and effective. The statement "the proposed bound 0.9999 for `log 2` remains open" refers to a proposal the paper never introduces.

6. **Prop 6.2 ("Two digits at one prime") is unmotivated and not used later.** I verified it, but nothing in the paper uses it, the title is opaque (it means two consecutive residues mod `p²`), and the function of the section is unclear. Either state its purpose or move it out.

7. **The introduction needs the context it currently omits.** The reader is never told why denominators of shifted series matter (the connection to digit extraction and normality of the shifts). All motivation lives in the project, so the paper cannot be read alone.

8. **Priority and antecedents** (Novelty status below). The sentence "Priority for the exact rates … remains undetermined" (l. 93–95) should be replaced by a statement of what was searched.

### S3: exposition and presentation (details in the next section)

9. **Overall structure.** Eight topics in 14 pages: half-length theorem, band formula, optimality, corrections, numerator residues, binary words, arctangents and `π`, `e`, discrepancy. The title mentions only logarithms and arctangents.

10. **Notation clashes.**
    - `B` is the beta function, a radix (Prop 6.2, Thm 6.3), and in `B_0` a numerator.
    - `H` is the lift count `L/P`, the bin width in Thm 4.2 and Thm 7.1, and a height `H(t_n)`.
    - `K` is `3^{max(r,2s)}`, `⌈N^{1/3}⌉`, and "some `K`" in Section 8.
    - `L` is `L_N`, a generic common denominator, and the count `L` in Prop 8.1.
    - `A` is the numerator sequence `A_n`, the polynomial `A_j` in Thm 4.2, and `arctan(1/3)` in Thm 6.3.
    - `C` is the constant in Cor 3.2, the correction `C_a`, and `arctan(1/7)`.
    - `F` is the function in Cor 3.2 and, as `𝔽_p`, the field.
    - `h` is the grid size, the gap, and the entropy `h(ρ)`.
    - `t` is `N−km`, the Gaussian index, an integration variable, and the target in Prop 6.2.
    - Theorem 6.3 uses `A`, `C` for the two angles and `a`, `c` for coefficients, which is hard to read.

11. **Internal identifiers in a journal manuscript.** "CC-01", "Checkpoint 11", "paper deduction", "reviewer guide" and "full declaration list" are repository vocabulary. Table 3 (l. 858–903) duplicates `CORRESPONDENCE.md`.

12. **Theorem 2.4's phrase "least possible limiting rate (eq:bands)"** defines the rate by the formula. Say that Theorem 2.3 shows the limit exists and equals the right side. In the proof, add that the primitive prime of the largest occupied `k` divides no other occupied `2^i−1` (the ones below `k` by primitivity, none above by maximality).

13. **The constant 116 in Prop 2.1** is correct but about 150 times larger than the largest observed ratio (0.79 for `N<1500`). Only the order `N^{2/3}` is used. Say that the constant is not optimised.

## Specific passages to cut, clarify or rewrite

Line numbers refer to `paper.tex` at the reviewed revision.

| Lines | Text | Action |
| --- | --- | --- |
| 33–46 | Abstract: eight claims in one paragraph; "Integral corrections give explicit common denominators for approximations valid over a linear number of further shifts"; "specified binary series"; "remains open here" | **Rewrite.** Open with Theorem 1.1 (`N/2`), then the class and optimality, then one sentence for the rest. Replace "specified binary series" with the actual series, and "remains open here" with "is not addressed". |
| 55–57 | "A multiplicative identity between three rational numbers yields a second approximation." | **Cut** or replace by the identity `(1+2^{−3})/(1−2^{−2})² = 2`. |
| 73–77 | "The prime divisors determining the limits can be read from much shorter prefixes. In particular, the first omitted prime band for `Y_N` carries half the logarithmic weight of `L_N`." | **Rewrite**: "The primes in `N/2 < p ≤ N` do not divide `den(Y_N)`; they carry half of `log L_N`." Delete "much shorter prefixes". |
| 79–95 | Literature paragraph | **Rewrite.** "Here the dyadic factor interacts with reduction at each prime, and primes of order `N` govern the first-order term" and "Such estimates quantify proximity of the real number to prescribed grids" say nothing checkable. State what each cited paper proves and how this paper's statement differs. |
| 93–95 | "are antecedents. Priority … remains undetermined" | **Rewrite**: "We did not find the exact rates in the literature; the search was not exhaustive." Say which results are known (BBP congruences, Takahashi's formulas, Sondow–Schalm periodicity). |
| 246–253 | "The quantifiers allow …", "changes the problem", "Another larger class arises" | **Tighten.** State the three excluded variants (`N`-dependent coefficients, other cutoffs, rational corrections) in one sentence with a reference to Adegoke et al. |
| 376 | "The following estimate counts returns to `\emph{each}` field element." | **Rewrite** as a statement: "`p`-adic residues of `U_n` do not cluster at any value." Drop the emphasis. |
| 420–422 | "This also explains why large diagonal denominators persist in moving windows. We record a proof, since the quantifier over the starting position differs from ordinary density one." | **Rewrite**: "Corollary 4.3 extends this to windows beginning at any `x`; the exceptional proportion is uniform in `x`." |
| 536–539 | "The logarithm supplies one particular `r` there." | **Rewrite**: "For `log 2` the residue `r` is a single value, not an average over residues." |
| 596 | "This lower bound concerns that single word." | **Keep the content**; add that the true word has 38 changes (see finding 1). |
| 793–794 | "The prime-by-prime proof above exhibits which numerator recurrences force the weaker density conclusion." | **Cut.** |
| 841–844 | "The gaps in these finite-prefix bounds tend to zero. … the proposed bound 0.9999 …" | **Rewrite**: drop "proposed", or state who proposed it. |
| 846–856 | Section "Formal verification and reproducibility" and Table 3 | **Shorten.** Keep a pinned reference, the statement of which results are formal, and the Bang and finite-zero-set caveats. Move Table 3 and the CC identifiers to `CORRESPONDENCE.md`. |
| 905–912 | "full declaration list and reviewer guide … alone uses floating-point logarithms" | **Rewrite** in neutral terms: list the files and what `generate.py` regenerates. |
| 914–918 | Authorship disclosure | **Keep**, but align the wording with the venue's policy and the owner's decision. |

Clarify before expert review:
- Define "observation" (Prop 5.3), "shadow" if retained, and "lift" (Section 5).
- Define the model `Z` once as "the two-stride model".
- Replace "paper deduction" by "proved in this paper".

## Limits of this review

- I did not run `lake build`.
- I could not read the full text of Takahashi, Adegoke–Lafont–Layeni, Berndt–Kim–Zaharescu, Shiu or Sondow–Schalm.
- I did not examine the external GitHub checkpoint.
- I did not regenerate the figure or run `generate.py`; I only compared its data with my own computations. The Table 2 diagonal row `n=1024` was not re-run.
- Numerical checks are finite and support the statements. They are not proofs of the asymptotic limits.
- I did not read `REVIEW.md`.

## Novelty status

- **Elementary or known inputs.** Beta-integral corrections are a classical technique. The prime-band congruences resemble the literature on `p`-adic valuations of harmonic numbers (Sanna, Shiu). BBP congruences are classical, and Sondow–Schalm already use gap polynomials for `e`.
- **Plausibly new, unverified.** The exact rate `N/2` for the two-argument representation, the band formula and the Bang-based optimality in the dyadic class, and the uniform Banach-density estimate for the diagonal residues. My search found no direct prior work on reduced denominators of shifted binary logarithm truncations. That is not a priority search.
- **Likely not new.** Section 7's density conclusion (BKZ), Prop 8.1 in its present form (finite irrationality measure), and the arctangent and `π` binary series, which follow Takahashi's identities.

## Suitability for human expert review

- Sections 1–3 are ready for an expert in elementary number theory or Diophantine approximation. I found no gap in their proofs.
- Sections 4–8 should not go to a reviewer until the S2 items are addressed. Otherwise a referee will reasonably ask what the sieve tables prove, why the `e` section remains and why the discrepancy result is specific to `π`.
- A reviewer should be asked in particular to check:
  - the BKZ and Takahashi citations;
  - whether the exact-rate and optimality statements are new;
  - whether the overlap proposition and the diagonal density corollary are worth keeping.
