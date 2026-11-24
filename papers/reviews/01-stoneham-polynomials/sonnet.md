# Independent review of Paper I — *Polynomial images of Stoneham numbers*

| | |
|---|---|
| **Input SHA** | `a9d9166e40aab0b9b85af0fdc9b967f87cd3b606` (`papers/01-stoneham-polynomials`: `paper.tex`, `paper.pdf`, `references.bib`, `check.lean`, `figures/`). The worktree HEAD `6fd1442` is a merge of that commit and leaves this directory unchanged (`git diff a9d9166 HEAD -- papers/01-stoneham-polynomials` is empty). |
| **Reviewer model** | Claude Sonnet 5.5 (`claude-sonnet-5-5`) |
| **Review date** | 2026-11-24 |
| **Scope** | Full read of `paper.tex` (576 lines) and the 10-page PDF, including rendered pages. Theorem-to-Lean mapping checked against the pinned commits `a09e011` and `afc3549`. External sources downloaded and read: Vandehey (arXiv 1606.07911), the Kano–Shiokawa preprint (KSTS/RR-91/006), Coons (arXiv 1212.3449), Bailey–Borwein (author PDF) and the two-sum manuscript. No other model's review was read. |
| **Not done** | `lake build` and `check.lean` were **not run**. The worktree has no `.lake` build and no mathlib cache. Lean correspondence below is by reading statements and declaration lines, not by kernel check. The published Kano–Shiokawa (Israel J. Math.), Korobov 1990 and Bailey–Crandall texts were not accessible. |

## Verdict

**Mathematically sound as far as I could check. Not ready to circulate or submit as it stands.** I found no false statement and no gap in the arguments for Theorems 1, 2, 7 and 8, Corollaries 6, 9 and 10, or Proposition 11. The defects are:

1. Internal workflow text left in the body, and a bibliography entry with no author.
2. A missing citation for a standard fact used in the proof.
3. An under-stated scope.
4. A positive novelty statement that is missing.
5. A fair amount of notation overload, non-standard terminology and repository-documentation prose.

The writing is terse and mostly free of chatty transitions, and there is no promotional rhetoric. The prose problems are of the kind "reads like a README or lab notebook", not "reads like marketing". All of it is fixable in one editing pass without touching the mathematics. The statement-by-statement Lean mapping is accurate (see Part A). Corollary numbering in this report follows the PDF: Theorem 1, Theorem 2, Lemmas 3–5, Corollary 6, Theorems 7–8, Corollaries 9–10, Proposition 11.

---

## Part A. What I verified

| Item | Method | Result |
|---|---|---|
| Prime-power convention: `α_{b,c}=Σ_{j≥1} c^{-j}b^{-c^j}`, `c=p^e`, `p` odd, `p∤b`, `b≥2` | Compared the abstract, Theorem 1, Theorem 2 and eq. (1) with Lean `StonehamStatements.stoneham` (`∑' j, 1/(c^(j+1) b^(c^(j+1)))`), `PolynomialNormality` and `prime_power_polynomial_normal`. | Consistent. Lean takes `e : ℕ+` and `3 ≤ p`, `b.Coprime p`. Index `j≥1` matches. |
| `NormalIn` | Lean `Basic.lean`: frequency of `shift b x n = fract(b^n x)` in `[m/b^k,(m+1)/b^k)` over `0≤n<N`, `k>0`. | Matches the definition in §1, including overlapping words and leading zeros. |
| Theorem 2 / strict top degree | `same_prime_sum_normal` (`StonehamPolynomial.lean:70`) takes a top monomial with a nonzero rational coefficient and finitely many monomials of strictly lower degree. `prime_power_product_normal` (87) is the pure product. | Matches. Degree-zero monomials are allowed in Lean, as in the paper. |
| Orthant numerator, uniform precision, retained denominator | `weighted_upper_set_numerator` (`…Orthant:114`, requires only `2≤p` and gives `K≡1 mod p−1`), `weighted_uniform_precision` (158, requires `3≤p`), `retained_denominator` (`…Prefix:189`). | Match Lemmas 3–5. The paper's remark that `p=2` gives no information is consistent with Lean's `3≤p` in the precision lemma. |
| All anchors in Table 2 | Checked every link at its pinned commit: 112, 87, 70, Orthant 114/158, Prefix 189, `SmoothOrbit` 207, `StonehamJoint` 196, Square 251/310, ProductThreeFive 77/93, `StonehamStatements` 13. | All land on the named declaration. `rectangleFrequency` is actually at line 17 of `StonehamStatements`. Line 13 is the series, which the link text "statement module" covers. |
| Lean `asymptoticDiscrepancy` | `BinaryDiscrepancy.lean:10–17`: `limsup` over `N` of `sSup` over `0≤a<c≤1` of `|freq−(c−a)|`. | Matches `D_∞` in §6, endpoints included. |
| Lemma 5 index algebra | Re-derived by hand: `h_i, r_i, A`, `dk−Σ(e_i−1)≤A≤dk`, the reflection `v_i=h_i−j_i`, the set `U`, the anchor `(J,…,J)` using `e_i≥1` and `r_i≥0`, `φ(p^L) \| p^{s+1}−p^s` giving the constant `u_L`, and the congruence (4). | Correct. `C=Σ(e_i−1)+L−1` suffices. |
| Lemma 3 worked example (`d=2`, `p=3`, cut 10/9) | Recomputed. | Minimal vectors `(0,2),(1,1),(2,0)`, `K_U=3z²−2z³`, `K_U(3)=−27`, `v_3(H_U(3))=3`. Correct. |
| Theorem 7 (square profile) | Exact `Fraction` computation of `R_n`, `n<3^7`. | The four-interval profile holds for `k=4,5,6`. The 81-position table is exact. `R_30=16952434/9`, `R_35=542477888/9`, `R_36=29293805954/243` are exact. `n²<243q_n` and `q_n≤n²` hold for `81≤n<2187`. The mod-9 residue argument (`3+3·4≡6`) is right. `k=3` really is exceptional. |
| Theorem 8 constants | Brute-forced the isolation claim for `k=3…39` with the paper's `Q∈[P/3,5P/3)`, `B=⌊4P/15⌋`. Re-derived the margins (`4Q/5, 2P/3, 2P−Q, 4Q−P`, all `≥4P/15`). Checked `s+B≤44P/15<3P`, the four shells `3R,9R,27R,81R` (windows `[3R,8.8R]`, `[9R,26.4R]`, `[27R,79.2R]`, `[81R,237.6R]`, disjoint, below `238R`), total length `32R−4`, and `32R−4≥2N/45` for `N<714R`. | Everything checks. `43/45=1−2/45` follows. |
| Table 1 (joint two-bit words, 4096 positions) | Recomputed with exact rationals for `(α_{2,3}, α_{2,3}²)`. | All 16 entries match; the entries sum to 4096. |
| Ridout step | `q≤2^s s²`, error `O(2^{−s−4P/15})`, `s≤8P/3`, so the exponent is `≥1.1·s`. | The threshold `1<μ<11/10` is right. The restricted-denominator form of Ridout is correctly invoked. |
| Corollary 10 (compact, countable gap set) | Re-derived. Normalised locations are sums of at most `d` elements of `{m_i p^{−v}: v≥−1}∪{0}`, which is compact and countable. The truncation error and `μ<v/u` are as claimed. | Sound. The "adjoin zero" step handles degrees below `d`. |
| Proposition 11 | Re-derived the window `(1/(d−1),c−1)` and the nonemptiness condition `(c−1)(d−1)>1`. Rotation by `log_d c` requires multiplicative independence. `π`-adic pole at least `k·v_π(c)`. | Sound, but sketched. See M5. |
| Vandehey Corollary 1.2 | Read the source. | The paper uses it correctly: for finite `P`, `gcd(a,m)=gcd(m,b)=1` and `N≥m^ε`, the sum is `≤C m^{−δ}N(1+log m)`. Equation (5) follows with `ε=1/D`. The shift of start by `b` is a unit change of `a`. |
| Vandehey Theorem 7.4 description | Read the source. | Accurate: unit numerators, `c_k \| c_{k+1}` with primes in `P`, a gap condition on `μ_k`. Strictly increasing `c_k` is also in the hypothesis. |
| Kano–Shiokawa Theorems 4–5 and conditions (15)–(16) (1991 preprint) | Read the pages (scanned). | Accurately described: (15) `λ_n/μ_{n−1}→∞` and (16) `(log μ_n)/λ_n→∞`, for the ring generated by `Σ ε_n a^{−λ_n}b^{−μ_n}`, `ε_n∈{0,1}`. For `λ_n=n`, `μ_n=a^n` the paper's computation (`j/c^{j−1}→0`, `log c`) is right, so the standard generator fails both. The numbering is the preprint's; the published Israel J. Math. numbering is unverified. |
| Wagner's hypotheses | KS reproduces them: `λ_n/(nμ_{n−1})→∞`, `(log μ_n)/λ_n→∞`. | Consistent with the paper's statement that the standard generator fails them. |
| Coons Appendix A | Read the arXiv version. Appendix A proves transcendence of `α_{b,c}` for all integers `b,c≥2` by Mahler's method. | The use is correct. Whether the published JAMS version retains "Appendix A" with that title is unverified. |
| Bailey–Borwein §4 | Read. | §4 states it is "not known" whether `α_{b,c1}+α_{b,c2}` is `b`-normal. The paper's "posed … a different question" is acceptable. The two-sum manuscript cites §§4 and 6, not only §4. |
| Two-sum manuscript | Downloaded the fixed PDF. | Theorem 1 there is `α_{b,c}+α_{b,d}` normal for all `c,d≥2` coprime to `b`, including dependent parameters. The paper's description is accurate. The PDF names no author. |

Not independently confirmed: the Lean kernel checks, `check.lean`'s axiom filter, and whether Bailey–Crandall Corollary 4.9 is the stated corollary for `α_{b,c}`. Vandehey cites "Theorem 4.8 in [1]" and describes the `α_{b,c}` application. The paper pairs "Theorem 4.8 and Corollary 4.9", which I could not check.

---

## Part B. Findings by severity

### Major (fix before circulation)

**M1. Internal review note left in the text.** `paper.tex:120–121`: "Historical priority for polynomial images of the classical generators under the full hypotheses of Theorem 1 remains open for review." This is a workflow remark, not mathematics, and a referee will read it as a retraction of the paper's own contribution.
*Fix:* delete it and state the claim, scoped to what was searched. For example: "We have not found normality of `α_{2,3}²`, of `α_{b,c}^k` for `k≥2`, or of a mixed product such as `α_{2,3}α_{2,9}` in the literature on Stoneham-type constants. Normality of an individual generator, and of rational affine images of it, is classical [Stoneham, Korobov, Bailey–Crandall]." If priority has not been established to your satisfaction, say "to the authors' knowledge" in one place only.

**M2. Bibliography entry `twosum` has no author.** `references.bib` (`@misc{twosum, key={Normality of sums}, …}`) and the rendered reference [8], "Normality of sums of two Stoneham constants. Manuscript and Lean development, 9 September, 2026." The fixed PDF itself is anonymous, and a public search for it finds only a MathWorld list that says independent review has not been reported.
*Fix:* name the author(s) and repository owner, give the arXiv or DOI identifier if one exists, and mark it "unrefereed" in the sentence at `paper.tex:116`. Cite §§4 and 6 of Bailey–Borwein, or drop the section number. Because the paper's context depends on the status of that manuscript, state in one clause that it is unrefereed.

**M3. The proof uses an unreferenced fact.** `paper.tex:96`: "Thus degree one in Theorem 1 also follows by invariance under nonzero rational affine maps." Wall's theorem that `x` normal in base `b` implies `qx+r` normal for rational `q≠0`, `r`, is cited nowhere. The proof of Theorem 2 later proves only the direction needed there ("Normality of `Dx` implies normality of `x`", lines 278–287). Nothing proves the converse (`x` normal ⇒ `Dx` normal), which the "affine maps" sentence silently relies on. Severity is borderline: the sentence is context, and no proof in the paper depends on the missing direction.
*Fix:* cite D. D. Wall (1949 thesis) or Kuipers–Niederreiter for both directions, then either delete the lines 279–287 argument or turn it into a short stand-alone lemma ("Lemma 2.1 (rational scaling)") that the proof invokes.

**M4. Scope is under-stated.** The title and the first sentence of the abstract are about "Stoneham numbers" and "the standard Stoneham constant `α_{b,c}`", but the proof needs `c=p^e` for an odd prime `p`. That excludes the standard examples `c=2` (`b` odd), `c=6`, `c=10`, `c=15`, and all `c` with two distinct prime factors. Lemma 3 uses `p−1>1` and the whole frozen-congruence argument uses one prime. Nothing in the paper says whether `p=2` or composite `c` is open, false, or merely out of reach.
*Fix:* (a) title: "Polynomial images of Stoneham numbers with prime-power parameter" or similar. (b) A remark after Theorem 1: normality of `α_{b,c}` itself is known for every coprime `b,c≥2` (Bailey–Crandall), and the polynomial statement for composite `c` and for `p=2` is not proved here. Say which step fails (the integer `K_U(p)` can vanish when `p=2`; for composite `c` the denominators carry several primes and there is no single dominant valuation). If it is unknown whether the statement fails, say so in one line.

**M5. Novelty is stated only by negation and the comparison paragraph is incoherent in two places.** The positive claim sits in the abstract ("a rational combination of products … is normal") but the "Relation to earlier results" subsection never says what is new relative to Kano–Shiokawa and Wagner, whose rings do contain polynomials in their lacunary generators. The correct and sufficient statement is already derivable from the paper's own numbers: KS Theorem 4 and Wagner require (15)–(16), the standard generator violates both, so those theorems do not cover `α_{b,c}²`. That sentence is present (lines 99–105) but is surrounded by loose text:
- Line 106: "The older results establish polynomial normality for explicit families."
- Lines 107–108: "Here the coordinates are powers of the specified values in (1)."
- Lines 112–115: "Even in a square, two ordered pairs may contribute at one location, and their combined coefficients can cancel a denominator layer."
- Lines 118–119: "Its two linear terms have equal degree. The mixed product studied in Section 6 requires estimates at the locations `3^i+5^j`."

The first three do not say what they are contrasting. The last two are non sequiturs about the two-sum paper. See Part C for rewrites.

**M6. Priority of Korobov's criterion is not verified.** `paper.tex:91–93` attributes to A. N. Korobov a criterion for `Σ a^{−λ_j}b^{−μ_j}` "with increasing exponents and `μ_j≥a^{λ_j}`", citing [korobov, kano]. In the KS preprint I read, the hypothesis `μ_n≥a^{λ_n}` appears in Theorem 3 (with integer numerators `|A_n|<a^{λ_n−λ_{n−1}}`), and Theorem 1/Corollary 1 give normality under `λ_n²√(a^{λ_n})/μ_n→0`; Example 1 gives normality of `Σ 1/(a^n b^{c^n})` for integers `c>√a`, which contains every `α_{b,c}` with `gcd(b,c)=1` as the case `a=c`. I could not read Korobov 1990 and cannot confirm the attribution.
*Fix:* cite Kano–Shiokawa Example 1 (or Theorem 1/Corollary 1) directly for degree one, and name Korobov only for what you have verified. It is the sharper antecedent.

**M7. Proposition 11 is proved as a sketch, though it is a headline-level generalisation.** The proof says "take the negative logarithm arc for the rotation", "Decrease `η` so the two adjacent windows lie in `[P,cP)`", and "by the same argument as for 3, 5", all inside a statement that Section 6 treats separately. It also makes Theorem 8 and the second claim of Corollary 9 qualitative special cases of itself. A reader will ask why `3,5` gets a full proof and constants and the general case a paragraph.
*Fix:* either (a) present Proposition 11 first with a complete proof and derive `3,5`/`43/45` as an instance with explicit constants, or (b) say in one sentence that the proposition generalises Theorem 8's qualitative conclusion and its proof is a sketch of the same argument. Spell out the rotation step: with `θ=log_d c` irrational, the set `{kθ mod 1}` meets a fixed open arc with bounded gaps, so there are infinitely many `(k,ℓ)` with `d^ℓ/c^k` in the allowed interval.

### Moderate

**R1. Equation (5) is stated imprecisely.** `paper.tex:240–245`: "Uniformly for reduced `a/q`, with `q` supported on `S` and `q≤B^D`, (1/B)Σ e(ab^i/q) → 0 as `q→∞`." The quantifier is hidden. Precisely: for every `ε>0` there is `Q` such that every `B` and every reduced `a/q` with `Q≤q≤B^D` and `q` supported on `S` has `|(1/B)Σ_{i<B}e(ab^i/q)|<ε`. State it as a lemma, with that quantifier, and attribute it. It is the only analytic input.

**R2. Lemma 3 proof compresses the one step that needs an argument.** Lines 154–156: "The alternating binomial sum at one equals 1. Since `p≡1 mod (p−1)`, the ordinary integer `K_U(p)` is nonzero when `p−1>1`." Say it: "`z−1` divides `K_U(z)−K_U(1)` in `Z[z]`, and `p−1` divides `p−1`, so `K_U(p)≡K_U(1)=1 mod (p−1)`; as `p−1≥2`, `K_U(p)≠0`." Also note explicitly that `K_U(p)` may be divisible by `p` (the worked example has `K_U(3)=−27`) and that this does not matter because `1−p^{e_i}` is a `p`-adic unit.

**R3. "Theorem 7" statement carries an artifact constant.** `In particular n² < 243 q_n and q_n ≤ n² for n≥81` (line 351). `243=3^5` is the loss between `3^{2k−3}` and `n²<3^{2k+2}`. A reader wants the order of magnitude.
*Fix:* "In particular `n²/243<q_n≤n²` for `n≥81`, so `q_n` has order `n²`."

**R4. Section 8 reads like repository documentation.** It contains the checkpoint hashes, two separate pinned commits (`a09e011` and `afc3549`), `lake build` commands, an ST-ID table whose rows are out of order (ST-01, 02, 04, 05, 03, 06), the sentence "Internally the product proof uses a series indexed from zero, `A(b,c,m)=…`" and a description of what `check.lean` does. The line-number permalinks into an external repository are fragile for an archival paper.
*Fix:* keep one paragraph in the paper (what was formalised, where it lives, which results are Lean-checked and which are paper deductions). Move the build commands, ST-IDs and indexing remark to the repository's README or to ancillary files. If the table stays, order it by theorem number and reduce it to theorem → declaration name, with commit given once.

**R5. No author, affiliation or contact.** The header says "Research manuscript · 24 November 2026" and `\hypersetup{pdfauthor={}}`. The last paragraph says "Human review and responsibility for authorship and submission rest with the project owner." A mathematics journal needs a named author who takes responsibility for the proofs. "The project owner" is not a name, and "AI assistance was used for the formalization, exposition, source comparison and figures" is a disclosure to be made in the form the target journal requires, in an acknowledgements or statement section, not as `\paragraph{Preparation.}`.

**R6. Corollary 9's first claim is not a corollary of this paper.** "Every value in Theorem 1 is transcendental" follows from Coons plus two lines of field theory; it does not use normality. Calling it a corollary of the theorem misleads, and it should not look like a result of the paper. Put the observation in a remark ("Since `α_{b,p^e}` is transcendental [Coons, Appendix A], so is `P(α_{b,p^e})` for every nonconstant `P` with algebraic coefficients"), and keep the real new content: Corollary 10 (products of different generators) and the `3,5` product. Also note, here or in the next remark, that `α·(1/α)` shows why transcendence of factors does not give transcendence of products — which is what `paper.tex:464–466` is trying to say.

**R7. The statement and proof of the joint corollary have two small gaps in form.** (i) `d=0` is allowed by the statement ("distinct positive integers `r_1,…,r_d`") and then dealt with by "The empty product gives the same formula in dimension zero." That is noise; assume `d≥1`. (ii) The statement uses `c_i` for interval endpoints, while `c` is the Stoneham parameter everywhere else. Rename the endpoints `u_i,v_i`.

### Minor / notation and terminology

**N1. Symbol collisions.** Each of these is a reader tax; a mathematician will stumble at least once.

| Symbol | Uses |
|---|---|
| `P` | polynomial (Thm 1); `P=3^k` shell scale (§6, Prop 11) |
| `d` | degree of a monomial; second Stoneham parameter in Prop 11 (`c,d`); the exponent `D` in (5) |
| `D` | integer clearing denominators (§3); exponent in (5); `D_∞` discrepancy |
| `c` | Stoneham parameter; interval endpoint in Cor 6 and §6 (`[a,c)`) |
| `e` | prime-power exponent; `e(u)=exp(2πiu)`, written `\ee` in the source |
| `s` | number of lower monomials in Thm 2; location function `s(j)`; location `s=P+Q` in §6 |
| `T` | `T_b` the shift; `\T=R/Z` the torus |
| `R` | `R_n(M)`; `R=3^h` in §6 |
| `a` | Korobov's `a^{−λ_j}`; interval endpoint; numerator in `a/q` |
| `k` | block length in §1; shell index `k=⌊log_p n⌋` |

Cheapest repairs: shell scale `P→P_k`, Prop 11 parameters `c,d→c_1,c_2`, endpoints `a,c→u,v`, torus `\T→\mathbb T` with the shift `T_b` kept, `R=3^h→M=3^h`.

**N2. "Pole" for a p-adic denominator.** The proof of Theorems 1–2 (lines 259–260, and again at line 505 in Proposition 11) says "its pole is strictly larger than every lower pole" and "its pole order persists". A pole is a complex-analytic notion. Write "`−v_p` of the leading term exceeds `−v_p` of every lower term".

**N3. "Insertion", "location", "shell", "reflected".** These are good working words but not standard. Define "insertion at `n`" once (when `n=s(j)` for some index tuple `j`) and "shell `k`" once (the range `p^k≤n<p^{k+1}`), then use them uniformly. The source label `eq:frozen` (line 230) is invisible to readers, so no change is needed there.

**N4. Table 1 and Figure 2 are illustrations with no stated role.** Table 1 lacks the positions `0≤n<4096` and the identification of "word in `α`" with the first two binary digits of `{2^nα}`. The sentence "No finite digit count is used to deduce a limit" (line 566) defends against a charge nobody has made. Cut the sentence. Keep Table 1 only if the caption says what it illustrates, or drop it: the corollary needs no illustration. The column header "Word in `α²`" should say "of `{2^nα²}`".

---

## Part C. Editorial pass: quotes, locations, rewrites

Line numbers are `paper.tex`. The paper's prose is terse and almost never chatty. The hits below are the places where phrasing is stock, hedged, defensive, or unclear, listed in document order. Items I would keep unchanged are not listed.

| Line | Quote | Problem | Proposed text |
|---|---|---|---|
| 40–42 | "The proof identifies a nonvanishing inclusion–exclusion numerator for each upper set of reflected exponents. Compactness bounds the loss in the reduced prefix denominator uniformly across all insertion patterns." | The abstract narrates technique in undefined vocabulary. | Cut both sentences. Optional replacement: "The proof shows that the reduced denominators of the shifted partial sums keep all but a bounded number of the expected `p`-adic digits." |
| 45–46 | "we obtain an upper bound of 43/45 for the limiting upper binary interval discrepancy" | Awkward chain of modifiers. | "the binary interval discrepancy of `α_{2,3}α_{2,5}` has limit superior at most 43/45 (so it is not 1)" |
| 69 | "The square and cube of `α_{2,3}` and the value … are examples." | Stock "are examples"; the bases are not stated. | "For instance, `α_{2,3}²`, `α_{2,3}³` are normal in base 2, and `−(5/2)α_{10,9}^7+α_{10,9}²+1/3` is normal in base 10." |
| 70–72 | "For products we count degree with multiplicity. Choose positive integers `m_i,e_i` independently in each factor and put" | Imperative "Choose" is fine; "independently in each factor" is vague. | "A *monomial* is a product (2) of `d` generators `α_{b^{m_i},p^{e_i}}` with arbitrary positive integers `m_i,e_i`; its degree is `d`." |
| 84 | "give the binary-normal number `α_{2,3}α_{2,9}`" | Non-standard "binary-normal". | "give `α_{2,3}α_{2,9}`, which is normal in base 2." |
| 84–88 | "The strict degree inequality … controls cancellation after the monomials have been evaluated. In a general multivariate polynomial several terms of maximal degree can contribute at the same denominator order." | Vague, and promises a phenomenon that is neither exhibited nor claimed to be sharp. | "We do not know whether the strict inequality can be dropped; when two top-degree monomials have denominators of the same `p`-adic order, their sum can have a smaller one, and the argument no longer applies." (Or give an example, or cut.) |
| 90–92 | "Stoneham established normality for specific constants including `α_{2,3}` by studying digits in periodic fractions" | "studying digits in periodic fractions" is a gloss, not a description. | "Stoneham proved normality of `α_{2,3}`, and of `α_{b,c}` for odd primes `c` and `b` a primitive root of `c²`, by analysing the digits of the rational approximants [stoneham]." (Check the hypothesis against the 1973 paper before using this wording.) |
| 96–97 | "Thus degree one in Theorem 1 also follows by invariance under nonzero rational affine maps." | See M3. | "Normality is preserved by `x↦qx+r` for rational `q≠0` and `r` [Wall], so the case `deg P=1` of Theorem 1 is already known." |
| 99–105 | The KS/Wagner computation. | Correct, but "taking `a=c`", "Both quantities must diverge" are compressed. | "In [ks, Theorems 4–5] the generators `Σ a^{−λ_j}b^{−μ_j}` must satisfy `λ_j/μ_{j−1}→∞` and `(log μ_j)/λ_j→∞` (conditions (15), (16) there). For `λ_j=j`, `μ_j=c^j` the first ratio tends to 0 and the second equals `log c`, so neither Kano–Shiokawa nor Wagner's rings contain `α_{b,c}` or its powers. Their results concern much sparser series." |
| 106–108 | "The older results establish polynomial normality for explicit families. Joint normality also occurs in N. M. Korobov's work on conjunctly normal numbers. Here the coordinates are powers of the specified values in (1)." | Three unconnected sentences; the last has no verb that links it to what precedes. "Older results" is vague. | "N. M. Korobov's conjunctly normal numbers [jointkorobov] give simultaneous normality of tuples of series of a different shape. Corollary 6 concerns the coordinates `(α,α²,…)` of one explicit series." Delete the sentence if Korobov's relevance cannot be stated exactly. |
| 110–114 | "Vandehey's fixed-prime-support estimate supplies the analytic implication from reduced denominators to uniformity. His Theorem 7.4 treats … Even in a square, two ordered pairs may contribute at one location, and their combined coefficients can cancel a denominator layer." | The relevance of "even in a square" is never stated; this is the paper's real reason Thm 7.4 does not apply. | "Theorem 7.4 of [vandehey] treats series `Σ c_k^{-1}b^{-m_k}` with one term per location. In `α²` the coefficient of `b^{−s}` is a sum over all ordered pairs `(i,j)` with `p^i+p^j=s`, and these sums can have smaller `p`-adic denominators than any single term. Theorem 7.4 therefore does not apply to `α²`; the new input is the lower bound on denominators in Lemma 5." |
| 116–119 | "The 2026 manuscript [twosum] proves normality of `α_{b,c}+α_{b,d}` … Its two linear terms have equal degree. The mixed product studied in Section 6 requires estimates at the locations `3^i+5^j`." | The last two sentences do not connect to anything. | "The unrefereed manuscript [twosum] proves that `α_{b,c}+α_{b,d}` is normal in base `b` for every `c,d` coprime to `b`. Sums of this kind need not be controlled by one denominator, and none of its methods is used here." Cut the sentences about "equal degree" and "locations `3^i+5^j`". |
| 120 | "Historical priority … remains open for review." | See M1. | Delete; replace as in M1. |
| 142–144 | "Dickson's lemma gives finitely many minimal vectors … Indeed, every infinite sequence in `N` has an infinite nondecreasing subsequence." | "Indeed" explains a lemma by re-proving it in three sentences. | "By Dickson's lemma, `U` has finitely many minimal elements `v_1,…,v_s`, and every element of `U` lies above one of them." |
| 154–156 | "The alternating binomial sum at one equals 1. … This proves the assertion even when `p` divides `K_U(p)`." | See R2. | Expand per R2. |
| 240 | "We use the following consequence of the short-orbit estimate." | Stock; the estimate should be a numbered statement. | "**Lemma 5′** ([vandehey, Cor. 1.2]). For a finite set `S` of primes not dividing `b` and `D>0`: for every `ε>0` there is `Q` such that …" |
| 249–252 | "The formal proof uses an internal qualitative estimate by differencing at multiples of orders modulo divisors of `q`; the formal orbit estimate has no external analytic hypothesis." | Lean-specific; garbled sentence ("differencing at multiples of orders modulo divisors of `q`"). | Move to §8 as: "The Lean development proves a qualitative version of this estimate (`SmoothOrbit.fixed_support_orbit_estimate`) by an elementary differencing argument and does not use [vandehey]." |
| 279 | "For completeness, every subsequential weak limit …" | "For completeness" is a tell; this is a proof of a standard fact embedded in the main proof. | Separate lemma citing Wall; keep the argument only if you cannot cite it. |
| 313 | "The empty product gives the same formula in dimension zero." | Pointless edge case. | Delete; assume `d≥1`. |
| 330–332 | "These are shifted prefixes of the *square*: truncating the generator and then squaring it would select a different set of ordered pairs." | Emphasis in italics; the point is right but oblique. | "Note that `R_n` is not the square of a truncation of `α`: it sums over all ordered pairs `(i,j)` with `3^i+3^j≤n`." |
| 351 | "In particular `n²<243q_n`" | See R3. | See R3. |
| 437–438 | "The estimate leaves full binary normality of this product open. It also gives no positive lower bound for `D_∞(x)`." | Fine as content; slightly defensive. | "Whether `α_{2,3}α_{2,5}` is normal in base 2 is left open, as is any positive lower bound for `D_∞`." |
| 464–466 | "We record the details because transcendence of the individual factors alone would not imply transcendence of their product." | Justifies including a corollary; the mathematics needs no such defence. | "Transcendence of the factors does not by itself imply transcendence of their product." |
| 521–531 | "The established results use checkpoint `a09e011720bc`. … Internally the product proof uses …" | Repository documentation (R4). | Shorten per R4. |
| 566 | "No finite digit count is used to deduce a limit." | Defends against a charge nobody made. | Delete. |
| 570–572 | "AI assistance was used for the formalization, exposition, source comparison and figures. Human review and responsibility for authorship and submission rest with the project owner." | See R5. | Replace with an acknowledgements-style disclosure under a named author in the format the target journal requires. |

**Stock transition density.** "Thus", "Hence" or "Consequently" occurs on 12 lines and "Indeed" three times (lines 143, 227, 460). None is wrong. At lines 143 and 227 "Indeed" introduces a one-line justification that is better folded into the previous sentence (line 143 is deleted by the Dickson rewrite above). Lines 234–235, "Thus `v_p(p^A R_n(M))<L`. Reduction loses at most `L−1` powers from the denominator `p^A`, as required.", form one step and can be one sentence.

**Cuteness / promotion.** I found none. The only expressions with a faintly rhetorical air are "Compactness bounds the loss … uniformly across all insertion patterns" (abstract) and the italic *square* (line 330). No sentence inflates the result.

---

## Part D. Specific questions asked

**Exact ranges and prime-power convention.** Correct and matched to Lean. `p` odd prime, `p∤b`, `b≥2`, `e≥1`, the positive-index series, and the shell offset `k+4` in Lean for the paper's `k≥4`. Theorem 2 permits `b^m`-dilations and different `p^{e_i}` per factor. The word "classical" in the introduction covers only `c=p^e` (see M4).

**All-degree orthant and nonvanishing proof.** Correct. The inclusion–exclusion formula, `K_U(1)=1`, and the worked `10/9` example (where `p` does divide `K_U(p)`) all check, and the Lean statement requires only `K≡1 mod p−1`. The compactness step (Lemma 4) correctly requires a fixed anchor; I see no gap in that argument. Weaknesses are expository (R2).

**Joint uniformity.** Corollary 6 is correctly derived from Theorem 1 via the one-dimensional Weyl criterion applied to `Σ h_i X^{r_i}`, Stone–Weierstrass, and the collar argument for boxes. The Lean theorem `joint_uniform_powers` has the same hypotheses (`r` injective and positive, `0≤a_i≤c_i≤1`, any `d`). The scope is only distinct positive powers of a single generator, as the abstract says. It is not joint normality of different generators.

**Square versus 3/5.** Distinct and correctly separated. The square (Theorem 7) has an exact denominator profile on one prime axis and normality follows from Theorem 2. The `3,5` product (Theorem 8) lives on two prime axes where denominators are not controlled by one valuation, so only a discrepancy bound `≤43/45` and irrationality are obtained, not normality. The text says so (lines 437–438). The abstract lists the two results sensibly.

**Transcendence including paper-only Corollary 10.** Arguments are correct. Corollary 9 reduces to Coons plus Ridout in the restricted-denominator form, with `1<μ<11/10` verified. Corollary 10 (all values in Theorem 2) is the genuinely new transcendence statement and is proved by a compact-countable gap argument. I checked it step by step and found no gap. The transcendence results are outside the Lean development, which Table 2 and the last paragraph of §8 state. Proposition 11 is sound but sketchy (M7). The only issue there is labelling (R6).

**Novelty and antecedents.** (a) Kano–Shiokawa and Wagner: described accurately, with their numbering from the preprint (M5, M6). (b) Stoneham, Bailey–Crandall: accurately cited for the degree-one case. (c) Vandehey: correctly used. Theorem 7.4 is for linear series with one term per location, so it does not give powers. (d) Coons: the transcendence of one generator, correct. (e) Two-sum manuscript: accurate but unauthored and unrefereed (M2). (f) Bailey–Borwein: §4 states the sum question as unknown, as the paper says. Gap: no sentence states the paper's positive contribution relative to these (M1, M5). Missing citation: Wall for rational affine invariance (M3).

---

## Part E. Readiness assessment

- **Mathematical content:** no errors found; arguments are complete except for the Proposition 11 sketch (M7). Numerical claims (square profile, `43/45`, Table 1) are exactly confirmed by independent computation.
- **Lean correspondence:** statement-level match confirmed for every cited declaration; kernel checks not run in this review.
- **Fixes required before circulation:** M1 (delete the in-text priority note), M2 (author and status of `twosum`), M3 (Wall), M4 (scope and title), M5/M6 (novelty paragraph and the Korobov/KS attribution), M7 (Proposition 11).
- **Fixes recommended in the same pass:** R1–R7, N1–N4, and the Part C edits. Roughly a day's editing; none touches a proof.
- **Not ready for journal submission** until an author is named, the comparison paragraph is rewritten, and §8 is reduced to what a paper needs.
