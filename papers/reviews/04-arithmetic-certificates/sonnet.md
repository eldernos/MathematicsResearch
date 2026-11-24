# Independent review of Paper IV (arithmetic certificates for normality and their limitations)

- **Reviewer model:** Claude Sonnet 5.5 (`claude-sonnet-5-5`)
- **Input SHA:** `74ece558e91dc248420752ec0e63cfb03387251a` ("Write Paper IV on arithmetic certificates and overlap rigidity"). `papers/04-arithmetic-certificates/` is byte-identical at this SHA and at the working `HEAD` (`c4d4a95`).
- **Material examined:** `paper.tex`, the rendered `paper.pdf` (full text extraction checked for unresolved references and symbols; pages 1, 3, 6, 7, 9 viewed as images; page 10 as text), `references.bib`, `Check.lean`, `figures/` (`joint_density.py`, `joint_density.csv`, `curves.tex`), `CORRESPONDENCE.md`, the author's `REVIEW.md` and `notes/arithmetic-certificates.md` (as statements of intended scope, not as reviews). The Lean modules the paper links, at the pinned revision `a09e0117`. The cited sources Vandehey (arXiv:1606.07911), Bailey–Crandall (author-hosted PDF), the localized-logarithm manuscript at revision `06961817`, and Crossref records for the six DOIs.
- **Independence:** I read no other review of this paper. I did not edit the paper. I did not read Papers I–III or V beyond the abstract of Paper II.
- **Line numbers** refer to `paper.tex` at the input SHA.

## Verdict

**Mathematics: I found no error in any theorem.** I re-derived every proof by hand (Theorems 1, 2, 5, 6, 8; Propositions 3, 4; Corollary 7; the examples in §§3–5) and reproduced the finite computations independently. Both the stated constants and the claimed Lean correspondences hold. Quantifiers are correct as printed, but several are stated informally enough that a reader must reconstruct them (F9, F10).

**Formal correspondence: sound.** `Check.lean` compiles and its axiom audit of 26 declarations passes. The linked line numbers all land on the named declarations. Lean statements match the paper's, with the three scope differences recorded in F12.

**Positioning and attribution: two moderate problems.** Theorem 2 is a corollary of a published result and is presented as a result of the paper (F1). The joint-failure machinery of §4 is, for the unsigned localized family, superseded by the companion Paper II, and the paper never says so (F2). The Bailey–Crandall pin-cites are wrong (F5).

**Exposition: below the register the owner asked for, but not badly.** The text is terse and mostly precise. The problems are (i) an accounting metaphor ("cost", "charge", "pays") that carries mathematical content in the abstract, (ii) several sentences whose subject or quantifier is missing, (iii) several statements whose role in the paper is never explained (the toy examples after Proposition 4, the logarithmic-density paragraph, the first-precision bound), and (iv) heavy symbol reuse (F13). There is no chatty or promotional prose in the usual sense. §E gives 24 quote-and-replace edits.

**Suitability for specialist circulation: yes, with a cover note, after one short edit pass.** The mathematics is ready for experts in normal numbers and exponential sums, and for Lean-formalization reviewers. Before it goes out, apply F1–F6 and the §E edits to the abstract. That is a small amount of editing and needs no new mathematics. It is **not** ready for journal submission as it stands, because the novelty statement is missing (F1, F2, F7) and the Section 4 example is a weak illustration (F2, F4).

## Independent checks performed

| # | Check | Method | Result |
| --- | --- | --- | --- |
| C1 | Lean statements and axiom audit | `lake env lean Check.lean` from the project checkout (cached build at `d6acfcb`). I first confirmed that 14 relevant source files (ArithmeticCertificate, SmoothOrbit, QualityCoverage, PartialUniformity, IntervalCoverage, DiscrepancyChecker, JointFiveThirteen, OrbitRigidity, ModelCounting, StonehamOrder, LocalizedCertificate, SupportDiscrepancy, Basic, BinaryDiscrepancy) are identical to `a09e0117`. | Passes: "Checked the axiom dependencies of 26 declarations." I did not run a full `lake build`. |
| C2 | Linked line numbers | Script over all `\src{…}{line}{…}` links against `a09e0117`. | All 18 theorem links hit the named declaration. `SignedShellDiscrepancy` L144 is `discrepancy_sub_zeroDensity_tendsto`, whose statement is asymptotic (F6). |
| C3 | Statement-level Lean read | Read in full: `normal_of_approximate_arithmetic_certificate`, `phase_model_sum_bound`, `approximate_prefix_bound`, `fixed_support_orbit_estimate`, `smooth_overlap_separation`, `smooth_overlap_rigidity`, `overlap_chain_denominator`, `few_symbol_words`, `discrepancy_of_joint_failures`, the `failedCells` and `discrepancyCertificate` definitions, `joint_five_thirteen_count`. | Correspond to Theorems 1, 2, 6, Corollary 7, the word inequality, Theorem 5 and the example. Scope differences in F12. |
| C4 | Figure reproduction | Ran `joint_density.py` in a scratch copy of the repository layout. | `joint_density.csv` and `curves.tex` byte-identical to the committed files. |
| C5 | Independent exact recomputation of §4 | Own code (no repository imports). Computed the residues `U_p(t)` from definition (5), the failed regions `Z_5=[2,4)`, `Z_13=[10,13)`, the precision-two residues, and the anchored piecewise-affine maxima at τ=10⁻¹⁰ with breakpoints including clipping crossings. | All as printed: residues 3,0,0,4 mod 5 and 7,12,12,11,8,8,8,10,10,0,0,0 mod 13; precision two residues 13,23,10,15,20,14 mod 25 and minimum 7 mod 169 (no zeros). The two anchored maxima equal the printed fractions exactly. Both ends of [m_τ, m_τ+τ] = [0.2332417550079, 0.2332417551079] round to 0.233241755. |
| C6 | Brute-force sanity of the enclosure | Exact integer counts of the joint failure set `{n: n/5^k∈[2,4), n/13^i∈[10,13)}` at `N=13^{5994}`, where the relative scale of the 5-family is 0.384616 (≈5/13), truncated to the 14 newest shells per family. | f(N)=0.23324006, within 2×10⁻⁶ of m_τ, as the cusp at 5/13 predicts. Confirms the scaling and the claim that the maximum occurs at 5/13. |
| C7 | Lean count bound | `1000·count(N) ≤ 234N + 2197000` at ≈31,000 values of N (≈400 band endpoints up to ≈10²²⁰, 2,000 random N ≤ 10³⁰, and every seventh N<2·10⁵: ≈31,000 values in all). | No violation. Largest ratio count/N at large N: 0.23214. |
| C8 | Number-theory ingredients of Theorem 2 | Tested, for 100+ pairs (b,c) including even c and c=4,10,30: the valuation formula `v_p(b^{rm}−1)=v_p(C)+v_p(m)`, `Q | C·v_Q`, `Q ≤ C·v_Q`, and `|S(a)| ≤ √Q` for all unit a, for all c-supported Q ≤ 3000. | 0 failures. |
| C9 | Hand proofs | Re-derived each proof line by line, checking every displayed inequality, constant and quantifier (details in the "Soundness" section). | No error. |
| C10 | Sources | Downloaded Vandehey (arXiv v1), Bailey–Crandall (author site PDF), the localized manuscript; queried Crossref for the six DOIs. | Vandehey Cor. 1.2 and Thm 7.4 as described. Bibliographic data of all six journal items agree with Crossref. Bailey–Crandall pin-cites wrong (F5). Localized manuscript Thms 1.1, 4.1 as described; its §5 is closely related to §4 and uncited (F5). |

**Not done.** I did not compile the TeX (no TeX Live in this sandbox) and judged the PDF as committed. I did not check journal pagination of the Bailey–Crandall or Vandehey journal versions. I did not read the proofs in Papers I–III.

## Soundness and completeness of the proofs

**Theorem 1 (mean approximation), Eq. (3) and the prefix argument — correct.** The block `[uA, (u+1)A)` is a union of `m` consecutive blocks of length `T`, and cells `u=1,…,LB−1` tile `[A,LB·A)`. Theorem 2 applies to `hy` because `den(hy)=Q/gcd(Q,h)∈[Q/|h|,Q]` is supported on `c` and `Q>|h|` ensures it is not 1. Eq. (3) holds as printed. The conversion to a bound `o(A)` on every cut inside a cell uses `L≥2`, and the geometric summation over earlier shells gives `ρ·LB·A`. The thresholds for `M` and `η` are chosen in the right order. The hypothesis quantifies over all pairs `(M,η)`, which is what the proof uses (see F9). The Lean theorem is exactly this statement, with Theorem 2 as an argument.

**Theorem 2 (fixed-support estimate) — correct.** I checked the lifting-the-exponent formula (including the case `2∣c` with `4∣C`), `Q∣Cv_Q`, the Gauss-sum bound `|S(a)|≤√Q`, and (2) `≤ C/√Q + Q/T`. In the induction, `D∣g`, `g ≤ C(l−j)v ≤ CHcK` and `K^{s−1}/(CHc) < Q/g ≤ K^s` are correct. The Cauchy–Schwarz step, the `2Hv/T` translation error, the order of limits (first `K→∞`, then `H→∞`) and the final choice `K=⌊T^{1/3}⌋` (with `T^d ≤ K^{4d}` once `K≥3`) are correct. The statement "uniform convergence when K,Q→∞" is informal. It should be stated as: for every `s≥2` and `ε>0` there are `K₀, M` such that the bound holds when `K≥K₀, M≤Q≤K^s, T≥K³`. This is a presentation issue, not a gap (F10).

**Proposition 3 and the fixed-resolution remark — correct.** `D_N ≤ δG/N + (N−G)/N`. The `2/q` bound is right (inscribed and circumscribed unions of mesh cells differ from `[u,v)` by less than `2/q` in total). Note that "by at most `2/q` on each side" (l. 138) can be read as "at each endpoint". It should read "in total".

**Proposition 4 and the shortest-path remark — correct.** The restriction step (backward left, full edge, backward right) and the claim `min(t, w+l+r)` are right. The sharpness statement is correct: with `d(j)` the shortest-path distance from 0 on the graph that contains the given edges plus unit edges, `f_i=d(i+1)−d(i)` has `|f_i|≤1`, satisfies every given edge bound by the 1-Lipschitz property of `d`, and attains `S(N)=d(N)`. Both small examples are correct (zero sums on `[0,8),[2,8),[2,10)` force `[0,10)` via vertices `0,8,2,10`).

**Theorem 5 (joint failures) — correct, and the proof is complete modulo routine facts.** I verified the residue formula (5) against the definition (rows `i` with `is<L`, factor `p^{is}`, cofactor cutoff `r ≤ p^i t`, `w_p^p=w_p`, `k≥2(L−1)` so every row has `k−i≥L−1`). The valuation consequence `v_p(den R_n) ≥ ks−L+1` is right. The block-discard count (at most three blocks per index, `(1+log₂(N+T))^{|S|}` indices, hence `o(N)`) is right. On a retained block `R_{a+i}=b^iR_a`. The denominator bound `den R_a ∣ c^{sH}` follows from `m^s ∣ (bc)^{sH}` and `a−m>T≥sH`, and `c^{sH} ≤ T^d` for a fixed `d` because `T=⌊√N⌋` and `H≈log₂N`. Transferring vanishing Fourier means to vanishing block discrepancy (the sequence-of-violating-blocks argument) is standard and is stated tersely but correctly. Applying Proposition 3 to the retained blocks that contain a passing position gives the bound; blocks with no passing position consist entirely of joint failures. The Lean theorem has the same statement in cell form (the jumps of `U_p` occur at `t=r/p^i` with `i≤L−1`, so failure sets are unions of cells of width `p^{−(L−1)}`).

**§4 two-prime logarithmic density — correct.** The equidistribution of `(z/log p, z/log q)` on the torus, the product measure, and the comparison of `∫ dy/y` with `Σ 1/n` are right, but the error paragraph is muddled (F11). The conclusions "ordinary density does not exist" (the count is constant on `[13^k, 10·13^k]`, so a positive density is impossible, while the positive logarithmic density excludes zero) and `a_p·a_q ≈ 0.0441` are right. The bound `|Z_p| ≤ p(log p)a_p` and `d̄(B_p) ≤ p|Z_p|/(p−1)` are right.

**Worked example and Figure 1 — correct.** All printed residues, bands, densities, the rational pair, the rounding and the caption (peak at `5/13`, newest left endpoints coincide at `10/13`; curves start at `1/13` and `1/5`) were reproduced independently (C4–C7). The reduction to anchored right endpoints is sound: local maxima of the accumulated fraction occur only at right endpoints of components of the intersection, which are right endpoints of one of the two families. Between crossings each intersection length is affine in the phase, so the maximum is at a breakpoint, and Kronecker density of the phases gives `m_τ ≤ D_fail ≤ m_τ+τ`.

**Theorem 6 and Corollary 7 — correct.** `Q ∣ den(y)den(z)` gives support and `Q≤T^{2d}`. The case split at `M` is right, with `γ=min(1/M, 1/(4π))` (for `1<Q<M`, `1/Q ≥ 1/M`). Corollary 7's content is the Lean theorem `overlap_chain_denominator`. Its printed statement is not a well-formed theorem (F3). The three examples in the final paragraph are correct: `0,1/b` (mean `1/(bT)`), `0,c^{−T²}` (mean ≤ `b^Tc^{−T²}`), and `0, 1/(b^m−1)` with `T=m(b^m−1)` (mean `≤ 1/((b−1)m)`, first character mean →1, `Q_m ≤ C·v_{Q_m} ≤ Cm` impossible for a fixed support).

**Theorem 8 and the Borel–Cantelli step — correct.** I re-derived each constant. `{b^{n+i}x−b^iy}={b^iz}` with `z` uniform. A base-`a` digit 1 at position `j+1` puts `{b^{2j}z}` in `[1/a,2/a)`, at distance ≥`1/a` from an integer because `a≥4`. The number of such `j<J=⌊T/2⌋` is at most `K=⌊aη_bT⌋`. The weighted word count gives `2^K(1−1/(2a))^J`. With `T≤3J` the inequality `K log 2 ≤ J/(4a)` holds (the actual margin is a factor ≈2). The count of rationals is at most `T^{2d}`. The sum over `k` is summable, and Borel–Cantelli needs no independence. The deduction that the hypotheses of Theorem 1 hold only on a null set is correct: the certificate supplies at least `(1−η)L^k>0` good starts per cell, and `b^jx−P_j=o(1)` converts the certificate into a model for `x` itself.

## Findings, ranked

Severity: **Major** = fix before sending to experts. **Moderate** = fix in the same pass. **Minor** = polish. I found no Major finding; F1–F6 are Moderate.

### F1 (Moderate): Theorem 2 is a corollary of Vandehey's Corollary 1.2, and the paper does not say so where a reader would look

*Where:* abstract (l. 33), Theorem 2 (l. 66–71), l. 72.

Vandehey's Corollary 1.2 states, for finite `P`, `m∈ℕ_P`, `gcd(a,m)=1`, `gcd(m,b)=1` and each `ε>0`: `|Σ_{n=1}^N e(ab^n/m)| ≤ C m^{−δ}N(1+log m)` for `N≥m^ε`, with `δ=δ(ε)>0` and `C=C(ε,b,P)`. Taking `ε=1/d` gives Theorem 2 immediately. The paper acknowledges this in one sentence after the statement (l. 72). The abstract, however, lists the cancellation as the first result, and the theorem environment carries no attribution. The stated reason for the new proof, "to exhibit the uses of fixed support", is not a reason. The apparent reason is that the formal development needs a self-contained argument; the Lean docstring calls the proof an "elementary differencing proof" of the "qualitative consequence" that "does not give Vandehey's quantitative savings".

*Action.* Title the theorem "Fixed-support estimate (qualitative form of [Vandehey, Cor. 1.2])", and give the real reason in one sentence (replacement E10). In the abstract, say "we reprove a qualitative form of Vandehey's estimate". State in the introduction which results are new: Theorem 1 as a transfer principle, Proposition 3 (elementary), Theorem 5, Theorem 6 and Corollary 7, Theorem 8. Add that the author has found no prior statement of Theorem 6 or 8 in this form. This is what `REVIEW.md` already says. The paper itself should carry it.

### F2 (Moderate): §4 is, for its own example, superseded by Paper II, and the paper does not say so

*Where:* l. 154–235, abstract sentences 5–6.

Paper II proves (abstract) that for `Σ_{m∈M(S)} m^{−s}b^{−m}` the discrepancy tends to zero iff some `p∈S` does not divide `b`, and that at each cutoff the discrepancy differs by `o(1)` from the proportion of simultaneous persistent failures. Normality of `X` for `b=2, S={2,5,13}` therefore follows from Paper II directly, and Theorem 5 is a fixed-precision upper-bound version of Paper II's exact joint formula. Two consequences a reader cannot see from Paper IV:

1. The conclusion `D_∞^{(2)}(X)=0` (l. 235) is not new information. The example's value is that it illustrates the method.
2. The alternative on l. 192 ("Along nested refinements with positive limiting masses at both primes, that cost stays positive") describes a case that, by Paper II's persistence theorem, does not occur for this family. The sentence "In this case the single-prime test suffices in the limit" is, for this family, the general situation. A specialist reading §4 will ask what the joint test is for, since a single off-radix prime at high precision already suffices.

The paper does say that the two-prime calculation "gives no lower bound on the discrepancy of X" (good). The `REVIEW.md` says the example is "superseded for normality by the second-precision certificate, and in general by the unsigned classification in Paper II". The paper itself should say this once, next to Theorem 5 (replacement E24).

I did not review Paper II's proof; this finding rests on its abstract and on `REVIEW.md`.

### F3 (Moderate): Corollary 7 is not a well-formed statement

*Where:* l. 253–258.

The corollary mixes two statements. (i) For a sequence of pairs of models satisfying the hypotheses of Theorem 6 eventually, with positive lengths `T_j` and combined mean error tending to zero, `y_j−z_j∈ℤ` eventually. (ii) For a chain in which block `j+1` starts `r_j≥0` shifts after block `j`, the aligned pair `(b^{r_j}y_j, y_{j+1})` satisfies the hypotheses of (i) and the reduced denominators are eventually constant. In (ii) the observations, the block lengths, the lengths of the overlaps, and which quantities must be small are not stated. "Starting phases" is not defined. The size hypothesis must hold for the *overlap length* `T_j`, not the block length, and this appears only in the paragraph after the proof. The Lean theorem `overlap_chain_denominator` does not take the error hypothesis at all. It takes eventual agreement modulo one as a hypothesis, and the deduction from small error is the content of (i).

*Action.* Split into Corollary 7(a) and 7(b). In (b), name the blocks `[n_j, n_j+ℓ_j)`, the models `y_j` and the observations `f`, state `n_{j+1}=n_j+r_j` and `T_j=n_j+ℓ_j−n_{j+1}`, require `den y_j ≤ T_j^d` and `den y_{j+1} ≤ T_j^d`, and require the combined mean error of `b^{r_j}y_j, y_{j+1}` on the overlap to tend to zero (replacement E19).

### F4 (Moderate): two sentences say more than the paper supports

*Where:* l. 235 and l. 63.

(a) l. 235: "The positive density in Figure 1 measures the loss at precision one." The figure shows the length of the joint failure set, which is an upper bound for `D_∞` at precision one (Theorem 5). The paper says on l. 192 that this "gives no lower bound on the discrepancy". Nothing in the paper shows that any loss occurs at precision one. Replacement E14.

(b) l. 63: "For signed Stoneham expansions the uncovered positions can themselves be localized near zero on the circle. In that case a matching lower bound gives an exact prefix discrepancy formula." The terms "uncovered positions" and "localized near zero" are not defined at this point. The linked declaration `discrepancy_sub_zeroDensity_tendsto` states `radixDiscrepancy − zeroDensity → 0`, which is an asymptotic equivalence, not an exact formula. The result belongs to Paper III, which the sentence does not cite. The sentence also interrupts the discussion of Paper I/II. Replacement E9, or delete.

### F5 (Moderate): citations — Bailey–Crandall pin-cites; omitted close antecedent

*Where:* l. 61, l. 63, `references.bib`.

(a) "Bailey and Crandall relate radix recurrences with convergent perturbations to normality and use them in lacunary constructions \[Thms. 3.1, 4.8, 4.11\]." In the author-hosted PDF of Bailey–Crandall, there is no Theorem 3.1. The radix-recurrence theorem is Theorem 3.2 (a perturbed recurrence `x_n=(bx_{n−1}+r_n) mod 1`; the recurrence is equidistributed iff `Σ r_n/b^n` is `b`-normal), together with Theorem 2.2(10) (a convergent perturbation preserves equidistribution). The PDF's own proof of Theorem 4.8 refers to "Theorem 3.1", which looks like an internal cross-reference slip. Theorem 4.8 is correct (growth conditions on `μ_k, ν_k`). **Remark** 4.11 is a remark about transcendence (Theorem 4.10), not a theorem about normal constructions. The relevant statements are probably Theorems 3.2, 4.8 and 4.12. I could not compare with the journal pagination, so the author should check against the printed version.

(b) The localized-logarithm manuscript (revision `06961817`) has a §5, "Finite-prime extensions", whose Theorem 5.1 proves normality of `Σ_{m∈M(P)} 1/(m b^m)` when all primes of `P` are coprime to `b`, or `b=2` and `3∈P`. Its proof uses the same device as Theorem 5 of Paper IV: discard blocks around the indices in `M(P)`, observe `R_{a+i}=b^iR_a` on the rest, bound the denominator by a power of the length, and apply Vandehey's Corollary 1.2. Paper IV cites only that manuscript's Theorems 1.1 and 4.1, in the context of power-of-three denominators. The block decomposition in Theorem 5 should be credited to §5 of that manuscript, and Theorem 5.1 should be mentioned as a precedent whose scope (order one; either all primes off-radix or `b=2, 3∈P`) the example `b=2, S={2,5,13}` falls outside.

(c) `references.bib` entry `localized` has no author, and the PDF itself carries none. It is sorted as reference [2] under "Binary normality…", and its provenance is a GitHub handle. A specialist cannot attribute priority. The paper cannot fix this, but should say "manuscript without stated authorship".

I confirmed that Vandehey's Corollary 1.2 and Theorem 7.4 are described correctly, and that all six journal references match Crossref metadata.

### F6 (Moderate): the term "certificate" in the title is never defined

The title says "arithmetic certificates". The word occurs nowhere in the body. The hypotheses of Theorem 1 constitute the certificate, but the reader must infer this. `Check.lean`, the registry and `CORRESPONDENCE.md` use "certificate" throughout. Add one sentence after Theorem 1: "We call the data `(y_n)` satisfying (1) an arithmetic certificate for `x` at schedule `(L,B,d)`."

### F7 (Minor): Propositions 3 and 4 are classical in form, and Proposition 4 has no application

*Where:* l. 128–152, abstract.

Proposition 3 is the weighted version of the concatenation inequality `D_N ≤ Σ(N_i/N)D_{N_i}` (Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Ch. 2, Thm 2.6, quoted as Lemma 4.2 in Bailey–Crandall) with uncovered positions charged at 1. Proposition 4 is the triangle inequality along a path. Neither is cited as classical. `REVIEW.md` says "no claim of priority for AC-03" but is silent on these. The abstract promises "An endpoint estimate permits overlapping tests", but nothing in the paper applies Proposition 4. The only examples are toy sequences. A reader will ask where overlapping coverage is used (Paper V, or §5?).

*Action.* Cite the concatenation lemma. State in one sentence where Proposition 4 is applied in this series, or say it is recorded for use in future work.

### F8 (Minor): Theorem 8 is stated for geometric `T_k=B^k`, but the argument holds for every `T`

*Where:* l. 272, 283.

The union bound gives `Σ_T C·T^{A+2d}·exp(−⌊T/2⌋/(4a)) < ∞` over all integers `T≥2`. The restriction to `T_k=B^k` is unnecessary. Dropping it extends the limitation to the schedule actually used in Theorem 5 (`T=⌊√N⌋`, with `≈T` starts per `T`), which currently is not covered by the stated obstruction, and removes the awkward need to treat "countably many schedules". The symbol `A` also collides with `A=(LB)^k` in Theorem 1 (F13).

### F9 (Minor): quantifier structure of Theorem 1 is implicit

*Where:* l. 51–55.

"suppose that for all sufficiently large `k` the following holds. Of the `m` starts … at most `ηm` are exceptional. At every other start …" The exceptional set is determined by `(u,M,η,k)`. State: "for each `(u,M,η)` there is `k₀` such that for every `k≥k₀` there exists `E⊆{0,…,m−1}` with `|E|≤ηm` such that for every `j∉E` there is `y`…". The Lean statement is already in this form (`∀ᶠ k, ∃ E, … ∀ j<L^k, j∉E → ∃ y`).

### F10 (Minor): informal limit statement in the proof of Theorem 2

*Where:* l. 91 ("We prove uniform convergence to zero when `K,Q→∞`, `T≥K³`, `Q≤K^s`").

State as: for every integer `s≥2` and `ε>0` there exist `K₀` and `M` such that `|(1/T)Σ_{i<T}e(b^iy)|≤ε` whenever `K≥K₀`, `T≥K³`, `M≤Q≤K^s`, `Q` supported on `c`, `y=a/Q`. Then say that the induction hypothesis is applied at `Q/g≥K^{s−1}/(CHc)`, which exceeds the threshold `M` for `K` large once `H` is fixed.

### F11 (Minor): the error paragraph in the logarithmic-density argument

*Where:* l. 190 ("Within each unit interval free of jumps the error is `O(1/n²)`. Near a jump it is `O(1/n)`, summable along the finitely many geometric endpoint sequences.")

Once the shell index is at least `L_p+L_q` (so `p^{k}` exceeds the denominators `p^i` of the jump points `r/p^i`), every endpoint of a band of `B_p∩B_q` is an integer, and the indicator is constant on each `[n,n+1)`. The error between `∫_{[1,N)∩R}dy/y` and `Σ_{n∈B_p∩B_q,n<N}1/n` is then at most `Σ n^{−2}+O(1)=O(1)`. The early shells with non-integer endpoints contribute `O(1)`. Replacement E22.

### F12 (Minor): scope differences between the paper and Lean are not stated in §7

*Where:* l. 286–319 and `CORRESPONDENCE.md`.

1. Propositions 3 and 4 are proved on paper for arbitrary observations `x_i∈[0,1)`. The Lean declarations `Coverage.fixed_quality_cover`, `discrepancy_of_paths` etc. are for radix orbits `{b^ix}` only. `CORRESPONDENCE.md` says so. §7 does not.
2. The Lean proof of Theorem 2 uses `K=2^{⌊log₈T⌋}`, whereas the printed proof uses `K=⌊T^{1/3}⌋`. The correspondence is of statements, not of proofs. Say "the formal proof follows the same differencing argument with `K` a power of two".
3. Lean's `five_thirteen_binary_normal` uses only the single prime 5 at precision two (`failedCells`, `{2,13}`), not the joint formulation.
4. The ten-digit enclosure, the logarithmic density, the sharpness remark for scalar data and the Borel–Cantelli step are paper-only. §7 states this for all of them (good).

`Check.lean` checks statements for only three results (Theorem 1 via `normal_of_approximate_arithmetic_certificate`, Proposition 3 and Theorem 6). The other 23 declarations are covered by the axiom audit only. The text on l. 325 ("these commands check the statements and their allowed axioms") should say "the statements of three results".

### F13 (Minor): symbol collisions

A paper this short should not use each of these letters for two or three things. Collisions I found (first use → second use):

| Symbol | Meanings in the paper |
| --- | --- |
| `A` | cell length `(LB)^k` (Thm 1) · exponent in "`O(T_k^A)` starts" (Thm 8) |
| `a` | numerator of `y=a/Q` (Thm 2) · `a=b²` (Thm 8) · start of a band `[a,e)` (§4) · block start `[a,a+T)` (proof of Thm 5) · `a_p` logarithmic mass |
| `B` | block factor `T=B^k` (Thm 1, Thm 8) · `B_p` failure set (§4) |
| `c` | support integer (Thms 1, 2, 6) · `c=∏p` in proof of Thm 5 (consistent role, different object) |
| `D` | discrepancy `D_N, D(F), D_fail` · divisor `D∣Q` (Thm 2 proof) · "cost at most `DN`" (Prop 4) |
| `d` | polynomial exponent · shortest-path distance `d(j)` (§3) · upper density `d̄` |
| `E` | exceptional block set (Eq. 3) · arbitrary set in `d̄(E)` · `E_{n,T}` (Thm 8) · `e` as band end and as `e(t)` |
| `G` | subgroup generated by `b` (Thm 2) · number of covered positions (Prop 3) |
| `H` | number of translates (Thm 2) · `⌈log₂(N+T)⌉` (Thm 5 proof) |
| `J` | subset of primes (Thm 5) · `⌊T/2⌋` (Thm 8) |
| `K` | scale (Thm 2) · count `⌊aη_bT⌋` (Thm 8) |
| `L` | block multiplier (Thm 1) · precision `L_p`, written `L` in the proof of Thm 5 |
| `M` | denominator floor · `M(b,c,d,ε)` · `𝓜(S)` |
| `m` | `L^k` (Thm 1) · multiples of period `rm` (Thm 2) · elements of `𝓜(S)` |
| `S` | prime set (§4) · Fourier sum `S(a)` (Thm 2) · partial sum `S(n)` (Prop 4) |
| `s` | exponent of series (§4) · induction index `s≥2` (Thm 2) · `s,t∈ℝ` (l. 108) |
| `T` | segment length · `T=⌊√N⌋` (Thm 5 proof) |
| `t` | real in `[1,p)` (§4) · cut `t` in Eq. (3) · `t∈G` (Thm 2) |
| `u` | cell index (Thm 1) · interval endpoint (`D_N`) · relative scale (§4) |
| `v` | interval endpoint `v` (`D_N`) · order `v_Q`, `v=v_D` (Thm 2) · valuation `v_p` |
| `w` | edge cost (Prop 4) · `w=y−z` (Thm 6) · `w_p` (§4) |
| `r` | `φ(c²)` (Thm 2) · word length (§1) · cofactor `r∈𝓜(S∖{p})` (§4) · shift `r_j` (Cor 7) |
| `b'` | an edge endpoint in Prop 4 (primed copy of the radix `b`) |

Minimum repairs: rename the Theorem 8 exponent `A→\alpha` and `a→\lambda`; the band endpoints `[a,e)→[\alpha,\beta)` and the other family `[\alpha',\beta')`; the Prop. 4 vertices `b'→j`; `G`(subgroup)`→\Gamma`; Thm 5's `T→T_N`. Give the proof of Theorem 5 its own letters (`H→h_N`, `L→\ell`).

## Formal correspondence: assessment

- Every theorem the paper says is kernel-checked is kernel-checked as stated: Theorem 1 (with Theorem 2 as a hypothesis, discharged by `fixed_support_orbit_estimate`; see the first `example` in `Check.lean`), Theorem 2, Proposition 3 (radix orbit version), Proposition 4 (path inequalities), Theorem 5 (cell form), the first-precision count, Theorem 6, Corollary 7, the word inequality.
- The Lean statement of Theorem 1 matches the printed one: `u∈Ico 1 (L*B)`, `∀M,∀η>0`, eventually in `k`, an exceptional `Finset` of cardinality `≤ηL^k`, a model with `M≤y.den`, `y.den∣c^v`, `y.den≤(B^k)^d`, and `∑turnDistance ≤ ηB^k`.
- Lean's `smooth_overlap_separation` matches Theorem 6 (it takes `δ=min(1/(M+1),1/(4π))` rather than `min(1/M,1/(4π))`; both are valid).
- Paper-only items are correctly labelled in §7 and `CORRESPONDENCE.md`: the measure estimate and Borel–Cantelli step, the logarithmic density, the sharpness statement, the rational enclosure.
- Remaining gaps: F12 (scope of Props. 3–4 in Lean; proof vs statement; `Check.lean` coverage).

## Stated limitations: assessment

**Stated and accurate:** Theorem 1's qualitative (not quantitative) nature; order of quantifiers (floor chosen before scale); `B=1` or `d=0` vacuous; Theorem 5 gives only an upper bound and "no lower bound on the discrepancy of `X`"; Theorem 6 requires coprime support, a polynomial size bound and the overlap length (three examples); Theorem 8 concerns prescribed schedules and "no verdict for a specified constant".

**Not stated, and should be:**
1. Theorem 2 is not a new estimate (F1).
2. For the unsigned localized family, Theorem 5 and the example are superseded by Paper II (F2).
3. Proposition 4 has no application in this paper (F7).
4. The Lean statements of Props. 3–4 cover radix orbits only (F12).
5. Theorem 8's schedules are geometric and prescribed. It does not touch the `T=⌊√N⌋` schedule of Theorem 5 as stated (F8).
6. The enclosure of `D_fail` is a floating-free but unformalized rational computation. It is not kernel-checked. The kernel result is `0.234`. (The paper says this on l. 208 and §7. Good.)
7. The bound `D_∞ ≤ D_fail` at precision one does not claim `D_∞>0` anywhere (F4a).

## Attribution and historical claims

- **Correct:** Korobov 1972 (digits of periodic fractions); Weyl 1916 (criterion); Borel 1909 (almost-every normality); Hoeffding 1963 ("compare" — the paper's elementary bound has exponent `J/(4a)`, in fact stronger than Hoeffding's `~J/a²`); Vandehey Cor. 1.2 and Thm 7.4 (statements match); Bailey–Crandall Thm 4.8 (statement matches Vandehey's restatement); localized manuscript Thms 1.1, 4.1.
- **Incorrect or imprecise:** Bailey–Crandall "Thms. 3.1, 4.8, 4.11" (F5a). "lacunary constructions" is loose but acceptable.
- **Missing:** the classical concatenation lemma (F7); the localized manuscript's §5 as the source of the block decomposition (F5b); Paper III for the signed claim (F4b); the superseding relation with Paper II (F2); the equivalence "normal ⇔ equidistribution of `{b^nx}`" is used with only Weyl cited (standard references: Wall's 1949 thesis and Kuipers–Niederreiter, Ch. 1, §8; Bailey–Crandall Thm 2.2(12) is the discrepancy form, as quoted by Vandehey).
- The AI-assistance sentence (l. 336) states that AI tools assisted "the mathematical development, Lean proofs and exposition". That is accurate but does not tell the reader what was machine-derived. That is a project-level decision, which I note without recommending a change here.

## Exposition: passage-specific replacements

Targets: remove metaphor ("cost", "charge", "pays", "escapes", "verdict"), give every sentence a subject and a quantifier, delete restatement. Line numbers refer to `paper.tex`.

**E1 (l. 33).**
> "A counting estimate shows that almost every real number escapes all such approximations on prescribed geometric schedules, even with unrestricted denominator primes."

→ "For Lebesgue-almost every `x`, no such approximation exists at all large scales of a prescribed geometric schedule, even if the denominators are not restricted to a fixed finite set of primes."

**E2 (l. 33).**
> "For a localized series, tests at different primes charge only simultaneous failures."

→ "For a localized series, we test the same shifted prefix modulo several primes and bound the discrepancy by the upper density of the positions at which every test fails."

**E3 (l. 33).**
> "Two accurate rational models on a common segment must agree modulo one under the polynomial bound in the overlap length."

→ "Two rational models whose denominators are supported on a fixed finite set of primes coprime to the radix and bounded by a fixed power of the segment length `T` cannot both approximate the same `T` observations within a fixed mean circle distance `γ`, unless their starting values differ by an integer."

**E4 (l. 33).**
> "We give sufficient conditions for normality with small mean approximation error and exceptional segments."

→ "Theorem 1 gives a sufficient condition for normality: at each scale, all but a vanishing proportion of blocks admit a rational model whose orbit is within small mean circle distance of the shifted prefix." (Then define "arithmetic certificate" here; F6.)

**E5 (l. 33).**
> "An endpoint estimate permits overlapping tests."

→ "A path inequality for partial sums bounds the discrepancy by test intervals that overlap (Proposition 4)." (And say where it is used; F7.)

**E6 (l. 59).**
> "The role of the real tail hypothesis is to pass from the rational observations P_j to the actual radix shifts. Errors within a block are measured modulo one."

→ Delete both sentences. The first is repeated in the proof (l. 117); the second is clear from `‖·‖_𝕋` in (1).

**E7 (l. 61).**
> "In Theorem 1 the denominator belongs to a model of a shifted prefix, where the sum of many coefficients may have undergone cancellation. The spacing condition is replaced by an estimate of the proportion of usable blocks."

→ "In Theorem 1, `Q` is the reduced denominator of a model for a block of the shifted prefix `P`, not of an individual coefficient; the reduced denominator of a sum can be much smaller than those of its terms. Vandehey's spacing condition on `m_j−m_{j−1}` is replaced by the requirement that all but `ηm` blocks at each scale admit a model."

**E8 (l. 63).**
> "For example, the Stoneham polynomial theorem uses growing denominators on blocks between insertions."

→ "The argument of Paper I for Stoneham polynomial images is of this form: the reduced denominators grow on the blocks between consecutive insertions." (Confirm that Paper I's proof is of this form; as written, "for example" has no antecedent.)

**E9 (l. 63).**
> "For signed Stoneham expansions the uncovered positions can themselves be localized near zero on the circle. In that case a matching lower bound gives an exact prefix discrepancy formula."

→ "For the signed expansions of Paper III, the positions not covered by good blocks are those at which the shifted prefix lies in a shell near zero on the circle. The prefix discrepancy then differs from the density of such positions by `o(1)` \[Lean: `discrepancy_sub_zeroDensity_tendsto`\]." Or delete.

**E10 (l. 72).**
> "We give a qualitative differencing proof to exhibit the uses of fixed support."

→ "Theorem 2 is the qualitative content of this corollary. We include a self-contained proof, by differencing, because the formal development requires one."

**E11 (l. 138).**
> "A fixed digit resolution has a different effect. … Inscribing and circumscribing an arbitrary interval by grid intervals changes its length by at most `2/q` on each side. … In particular a test at one resolution gives a discrepancy bound even when finer resolutions have yet to be controlled."

→ "Fixed resolution. Suppose the `q` mesh cells `[j/q,(j+1)/q)` each have limiting frequency `1/q`. Then every union of consecutive cells has its correct limiting frequency. An arbitrary interval lies between two such unions whose total lengths differ from its length by less than `2/q` each. Hence `D_∞≤2/q`." (Delete the last sentence.)

**E12 (l. 152).**
> "There is an exact interpretation of the shortest path when only scalar edge bounds are known."

→ "The path bound is sharp for scalar data. Let `W` be a set of edges `{a,b'}` with costs `w`, and let `d(j)` be the shortest-path distance from 0 in the graph with the edges of `W` and a unit-cost edge between consecutive integers. Put `f_i=d(i+1)−d(i)`. Then `|f_i|≤1`, every edge bound holds, and `S(N)=d(N)`." (State as a proposition.)

**E13 (l. 150).**
> "For example, three consecutive runs +1, −1, +1 of the same length T give zero sums on both adjoining intervals of length 2T. Their union has sum T. In the opposite direction, zero sums on [0,8),[2,8),[2,10) force the sum on [0,10) to vanish by the path with vertices 0,8,2,10."

→ "Overlap alone does not suffice: with `f=+1,−1,+1` on `[0,T),[T,2T),[2T,3T)` the sums over `[0,2T)` and `[T,3T)` vanish, but the sum over `[0,3T)` is `T`. If, however, the sums over `[0,8)`, `[2,8)` and `[2,10)` vanish, the path `0→8→2→10` shows that the sum over `[0,10)` vanishes."

**E14 (l. 235).**
> "The positive density in Figure 1 measures the loss at precision one."

→ "At precision one, Theorem 5 gives only `D_∞≤D_fail≈0.2332`; this is an upper bound and not a lower bound for `D_∞`." (Cf. F4a.)

**E15 (l. 192).**
> "Thus the product of logarithmic masses supplies a *lower* bound on the cost on the right of (6)."

→ "Hence the right side of (6) is at least `a_pa_q` for `J={p,q}`: no choice of precisions with `a_pa_q>0` can give a bound below `a_pa_q`."

**E16 (l. 265).**
> "The orbit of a Lebesgue-typical point has little chance of following any low-denominator rational for a whole prescribed block in mean circle distance. The obstruction does not require fixed prime support."

→ "Theorem 8 bounds the Lebesgue measure of the set of `x` whose orbit segment of length `T` is within mean circle distance `η_b` of the orbit of some rational of denominator at most `T^d`. No condition is imposed on the primes dividing the denominator."

**E17 (l. 283).**
> "The estimate concerns prescribed search ranges and gives no verdict for a specified constant."

→ "Theorem 8 holds for almost every `x`; it gives no information about any particular constant."

**E18 (l. 260).**
> "Small mean error on a longer block can concentrate on its short shared part. A size bound polynomial in the original length suffices if that length is bounded by a fixed power of T."

→ "A model with small mean error on a block of length `T'≫T` can have error of order one on an overlap of length `T`, so the hypotheses of Theorem 6 must be imposed on the overlap. If `T'≤T^e` for a fixed `e`, a bound `Q≤T'^d` implies `Q≤T^{de}`; the mean error on the overlap is, however, at most `(T'/T)` times that on the block, which is small only if the latter is `o(T/T')`."

(The original sentence addresses only the size bound and could be misread as covering the error.)

**E19 (l. 253–255), Corollary 7.** Replace with:

> **Corollary 7.** Fix `b,c,d` as in Theorem 6. (a) Let `y_j,z_j∈ℚ` have denominators supported on `c` and at most `T_j^d`, and let `f^{(j)}` be real observations with `T_j^{-1}Σ_{i<T_j}(‖f^{(j)}_i−b^iy_j‖+‖f^{(j)}_i−b^iz_j‖)→0`. Then `y_j−z_j∈ℤ` for all large `j`. (b) Let block `j` have model `y_j` for observations starting at `n_j`, let `n_{j+1}=n_j+r_j` and let `T_j` be the length of the overlap of blocks `j` and `j+1`. If `den y_j,den y_{j+1}≤T_j^d` and the mean error of `b^{r_j}y_j` and `y_{j+1}` on the overlap tends to zero, then `den y_j` is eventually constant.

**E20 (l. 286).**
> "In Theorem 1 the Lean statement takes the short-orbit estimate as an argument. Theorem 2 supplies it for the b, c in the printed statement."

→ "The Lean statement of Theorem 1 takes the conclusion of Theorem 2 as a hypothesis (`SmoothOrbitEstimate b c`). The declaration `fixed_support_orbit_estimate` discharges it for all coprime `b,c≥2` (first example in `Check.lean`)."

**E21 (l. 283).**
> "Borel's theorem gives normality for almost every x \[3\]. The numbers admitting these certificates form a null set."

→ "By Borel's theorem \[3\], almost every `x` is normal. Nevertheless, by Theorem 8 the set of `x` satisfying the hypotheses of Theorem 1, for some `(b,B,L,d)`, is Lebesgue-null. Theorem 1 therefore cannot certify a typical normal number."

**E22 (l. 190).** Replace the last two sentences of the paragraph by: "Once the shell index is at least `L_p+L_q`, every endpoint of a band of `B_p∩B_q` is an integer, so the indicator is constant on each `[n,n+1)` and replacing the integral by the sum changes it by `O(Σn^{-2})`. The finitely many earlier shells contribute `O(1)`."

**E23 (l. 113–115, 182, 136).** The metaphor of "cost" in proofs: "each exceptional full block and the unfinished last block cost at most `T`" → "each exceptional full block and the unfinished last block contributes at most `T` to the modulus"; "Proposition 3 now gives a prefix cost at most the number of joint failures plus `o(N)`" → "Proposition 3 now bounds `N·D_N` by the number of joint failures in `[1,N)` plus `o(N)`"; "An uncovered position costs at most one" → "An uncovered position changes `C_I` by at most one."

**E24 (after Theorem 5, new remark).**

> "For the unsigned localized series treated in Paper II, normality of `X` already follows from that paper's classification, which also gives the discrepancy exactly in terms of persistent joint failures. Theorem 5 is the finite-precision upper-bound form of that statement. We use it to illustrate how partial information from several primes combines and to give an explicit enclosure at precision one."

**Other local edits (no replacement needed).**
- l. 154 section title "Several tests for the same denominator" → "Joint tests at several primes".
- l. 155 "supported on S" for a prime set and "supported on c" for an integer: say once "supported on a set of primes".
- l. 164, "(\mod p^{L_p}), i≥0": the clause `i≥0` is the index range of the row; write the sum as `Σ_{i≥0, is<L_p}`.
- l. 195 "gives residues in `{7,…,168}` on every cell": write "gives a nonzero residue on every cell (the smallest is 7)".
- l. 195 "the same finite check on `t=j/13`, `13≤j<169`": the jumps are at `t=j/13` with `j∈𝓜({2,5})`; the check over all `j` is a superset, harmless but not what the sentence says.
- l. 203–207: the two displayed fractions are the maxima for anchors 5 and 13, but only the second is labelled `m_τ`. Write `m_τ^{(5)}=…`, `m_τ^{(13)}=…`, `m_τ=max=m_τ^{(13)}`.
- Figure 1 caption: say what `u` is ("the scale of the other prime's bands relative to the anchored endpoint").
- l. 150 and l. 141: the symbol `b'` collides with the radix.
- l. 262 "Its denominators escape every fixed coprime support": replace "escape" by "are not supported on any fixed finite set of primes".

## Recommended order of editing

1. Abstract: E1–E5. Add the novelty statement of F1 and the clarification of F2 as one paragraph at the end of §1.
2. Add the definition of "arithmetic certificate" (F6). Fix pin-cites and add the missing references (F5, F7).
3. Restructure Corollary 7 (F3, E19). Restate Theorem 1's quantifiers (F9).
4. Remove F4's two sentences or replace them (E9, E14). Apply E10–E18, E20–E24.
5. Rename the colliding symbols (F13).

## Summary for the owner

- No mathematical error found; formal correspondence holds; numerical claims reproduced exactly.
- Two honest-positioning gaps (F1, F2), one citation error (F5), one ill-formed corollary (F3), two over-statements (F4).
- The register is mostly professional but uses an accounting metaphor in the abstract and a few unanchored sentences. Twenty-four concrete replacements are above.
- Suitable for specialist circulation after one short pass, with a cover note saying that Theorem 2 is qualitative Vandehey and §4 illustrates a method superseded for its own family by Paper II.
