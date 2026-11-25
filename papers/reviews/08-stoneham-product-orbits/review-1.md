# Referee report: *Exceptional Orbits and Discrepancy of Stoneham Products* (Manuscript D, v1.0)

| | |
|---|---|
| **Reviewer model** | Claude Sonnet 5.5 (`claude-sonnet-5-5`) |
| **Date** | 2026-11-25 |
| **Reviewed commit** | `a7ad257` (branch `publication/wave-2`, includes the completed Phase 19 research) |
| **Status of this report** | **AI model review; not independent human peer review.** |
| **Author model of the manuscript** | Gemini 4 Neon, resuming an OpenAI draft (reviewed independently; the manuscript's self-assessment in `VERIFICATION.md` and `LEDGER.md` was not relied on) |

Materials read: `paper.tex` (405 lines), `references.bib`, `VERIFICATION.md`, `LEDGER.md`, `metadata.toml`, all six `submission/` files, `papers/wave2-audits/paper-III-audit.md`, `papers/WAVE2-CONTRACT.md`; sources `notes/phase14` to `phase17` and `notes/phase19` (README, handoff, literature, verification, the dyadic and mixed-prime scope section of `nonlinear.md`); Lean declarations at `e4809cf` (read from `git show`, not rebuilt); `scripts/phase16_mixed_product.py`, `scripts/phase17_mixed_product_orbits.py`, `scripts/phase17_dyadic_stoneham.py`, `scripts/test_mixed_interpolation.py`, `scripts/test_resonant_radices.py`. I built the PDF (15 pages, no undefined references or citations) and looked at pages 1 and 8.

## Verdict

**Mathematically sound; accept after revision.** I rederived every step listed in the brief and found **no critical error and no false statement**. The headline claims (mixture law, `D⁺ ≤ 4/11 + 2.85·10⁻¹⁰`, the zero-slack equivalence, `D⁻ = 0`, logarithmic equidistribution, the `O_ε(log* T)` sparsity) follow from the stated proofs together with the Lean pieces and the finite certificate. Ordinary normality of `α(2,3)α(2,5)` is stated plainly as open. The two major findings are about scope wording (abstract and submission texts) and one proof step that the text invokes but never states. The remaining findings are minor or editorial.

Counts: critical 0, major 2, minor 14, editorial 5.

---

## What I independently checked and confirmed

These checks are by hand or by my own scripts (kept in my scratchpad, not committed), not by trusting the manuscript.

* **Theorem 2.1 (l. 56–99).** Plateau structure (`R_n = B^{n−U}R_U` on a plateau; `den R_U | PQ ≤ n²`; coprime to `B`). Block argument: boundary blocks cost `O(N^{-1/2}(1+log²N))`; `m_I ≤ N² ≤ L_N⁵`; incomplete-cycle error `≤ M` per clean block, `O(M/√N)` in total. Tail `|σ(w)(J) − σ_M(J)| ≤ sup_{m_c>M} Δ(ν_c)` (the cruder constant `Σw_c ≤ 1` suffices). Real-shift remainder `0 ≤ Bⁿx − R_n ≤ 2(p+q)/((p−1)(q−1)n)` (I recomputed the two geometric tails). The arc-enlargement transfer `|D_N(x) − Δ(μ̃_N)| ≤ 2t + K/N` handles atoms at arc endpoints correctly: `J⁺` is built from the *closed* distance bound, and the argument is symmetric. Lean's `SmoothOrbitEstimate` (`SmoothOrbit.lean:16`) is stated exactly as used: uniform in the numerator and in `T` with `den ≤ T^d`, denominators dividing a power of `c`.
* **Propositions 3.1–3.2.** The loss formula `min(K, v_p(G_{a,d}(L)))`, including the telescoping `(p−1)Σp^{K−i} = p^K − p^{K−I_j}`, the fibre weights `1, p, p^d`, and the edge cases `a = L`, `d = K`. The expansion `x_{i+uz} = x_i A^{−z} exp(−qⁱℓ(A^z−1))`, the bound `v_p(∇^k g(0)) ≥ k+1` (the `h = 0` term uses `v_p(S_u) = 1`; for `h ≥ 1`, `v_p(ℓ^h/h!) ≥ (h+1)/2 ≥ 1` since `p ≥ 3`), the Vandermonde increment `F(z+y) − F(z) ≡ yS_u (mod p^{t+2})` (`k+1−⌊log_p(k+1)⌋ ≥ 2` for `k ≥ 1`, `p ≥ 3`), the isometry/surjectivity argument, and `ζ_{p,0,0} = 0`. The CRT existence of admissible radices (both cases `q ≢ 1` and `q ≡ 1 mod p`; `p` odd is used for `S_p ≡ p mod p²`). In Proposition 3.2: the periods and block sums `S₂ ≡ 6 (mod 9)`, `S₄ ≡ 15 (mod 25)` (the scripts print `(2,6)` and `(4,15)`); the Teichmüller bookkeeping `ω^{q^{u(−z)}} = ω`; `x_{−h} = q^h θ_h` with `θ_h^{q^h} = 1/2` and uniqueness of `q`-th roots (`gcd(q, p(p−1)) = 1` in both cases); compatibility `θ_{h+1}^q = θ_h`; coefficient of the lowest negative index (`p−1`, or `p^d−1` when `a = 1`); Eisenstein irreducibility of `X^{q^H} − 2` for `θ⁻¹`; the positivity argument for `z ≥ 0`. The loss formula itself is also tested exactly at every switch boundary up to `3^12` in `verify_prefixes` (`assert gcd(numerator, p^H) == gcd(g, p^H)`).
* **Theorem 3.3.** Residue-class reduction to `L mod up^{h−1}`, `K mod vq^{k−1}`; torus flow equidistribution (irrationality of `log p/log q`); overlap window `−log q < L log q − K log p < log p`; forced strict increase of both indices between distinct bounded-denominator plateaus of one shape; the tower bound `s_{j+1} ≥ c·e^{s_j}` giving `O(log* T)` bins; the boundary-strip density `pη/(p−1)` (peak at `t = 1−η`, matches `boundary_strip_piecewise_le`); `q^{a−1} < 1/η` outside the strips; summation by parts for logarithmic equidistribution.
* **Section 4.** Plateau endpoints `U, V`; `M_{p,q} = (p−1)(q−1)/(2pq−p−q)` attained uniquely at `r_* = q(p−1)/(p(q−1))`; inactivity of shell clipping at `r_*`; `a ≥ 2` and `d ≥ 2` bounds `(q−1)/q²`, `(p−1)/p²`; `M_{p,q}^{-1} ≤ 11/4` hence `M ≥ 4/11 > 2/9`. All four numerical bounds in Corollary 4.3 recomputed: `4/11 + 2.85·10⁻¹⁰`, `11250083/30000000`, `720004991/1860000000`, `720004379/1740000000` are correct values of `M + (p/(p−1)+q/(q−1))η + δ`. The grid sizes `(A, D)` and radii `(R_K, R_L)` follow from the stated rules (`η`, `δ` thresholds). The periods `(u, v)` match, including the torsion adjustments `v = 6` for `(2,3,13)` (needs `ω^{3^j}` period) and `(u,v) = (4,6)` for `(36,5,7)`.
* **Section 5.** `ord_{3^r}(2) = φ(3^r)`, `ord_{5^s}(2) = φ(5^s)`, `ord_m(2) = φ(m)/2` for `r,s ≥ 1`; each cycle is the full set of lifts of its numerator coset mod `m_0`; `Δ(ν_c) = 2/3, 2/5, 11/20` (I recomputed `F` at every atom; the script `verify_cycles` asserts it for `r ≤ 4`, `s ≤ 3`); the scaling by `m_0/m`; the equal-weight `15`-cycle mixture value `7/60`; period `≥ 4m/15`; atom counts `⌈mt⌉−1 < mt`, `m−⌈mt⌉ ≤ m(1−t)`; the dominance step: `w' < 3γ`, `w_0 > s_* − 2γ ≥ (11/4)w'`, hence `F_σ ∈ [0, w_0]` and `Δ(σ) = w_0`; `max_𝒲 w_0 = C_0` by diagonal extraction; the equivalence and `D⁺ = C_0` when either side fails (a short case check).
* **Theorem 6.1** (the 43/45 argument: gaps `≥ 4P/15`, `s+H ≤ 44P/15`, windows `3R…243R`, `32R−4 ≥ 2N/45`) and **Theorem 6.3** (see finding 3 for Ridout). The sets of exponents `k` with bounded gaps from the irrational rotation; the `π`-adic pole order argument works equally for `gcd(c,d) > 1` because the denominator support is the prime set of `Bcd`.
* **Section 7.** `y_k = {−Z_k b^{2^{k−1}}/2^{2k−1}}` and `h_k = [2k−1−v₂(Z_k)]_+`: I computed `R_{n_k}` exactly for `b ∈ {3,5,7,9,11}`, `C ∈ {0,1,2}`, `k ≤ 8` and compared (all match; plateau constancy on `[n_k, 2^{k+1})` also checked). Resonant classes: at `k = 11`, `s₀ = 2`, `H = 0` the radices `< 2000` with integral upper prefix are exactly `b ≡ 93, 163 (mod 256)`. Dyadic cycle discrepancies: the grid argument (i), the two-grid range `g·max(θ, 1−θ)` (iii), the singleton criterion (ii). Corollary 7.4: for `b ∈ {5,11,17,23,29,35}` the exact maximum of `Δ` over all admissible cycles equals `1 − 1/(3·2^{v₂(b+1)})` (so the bound is sharp for these); for `b = 5`, `D = 9`, `C = 0` the maxima over `h = 0,…,7` are `2/9, 2/9, 2/9, 5/18, 5/36, 5/72, 5/144, 5/288`, as stated.
* **Scripts** (all pass): `phase17_mixed_product_orbits.py` (5 s) reproduces the prefix scan (minimum `15` through `3^12` for `(2,3,5)`; `21`, `39`, `35` for the other rows), the three certificate lines with the exact fractions, and the block sums; `phase16_mixed_product.py` (11 s) prints the nano tier "depths (9,7), moduli (13122, 62500), `4/11 + 2.850e-10`"; `phase17_dyadic_stoneham.py` (35 s), `test_mixed_interpolation.py`, `test_resonant_radices.py` pass.
* **Lean pins at `e4809cf`.** Every distinct `\lean{File}{line}` pin lands on the declaration named in the text (checked by printing the lines). Statements match the paper: `quadratic_exact_limsup` (limsup equals `¼ limsup` of the cycle factor), `upper_denominator_valuation` (the `κ` formula, with `j = k−1`), `normal_iff_upper_denominator`, `normal_of_algebraic_kappa`, `quadratic_discrepancy_limits`, `quadratic_log_equidistribution`; `kappa b A B = −(2A+B+2A·intercept)/(2A·slope)` agrees with the paper's `κ`; `ProductThreeFive.discrepancy/irrational`, `column_discrepancy` (27/40), the two `mixed_product_discrepancy` (143881/250000, 4631/12500), `rectangle_denominator_growth`, `general_single_shape_one_one_max/attained`, `single_shape_one_one_max`. Proposition 7.2 is assembled from `target_valuation_of_hit` (first bullet) and `resonant_residue` (second bullet, with `¬(r ≡ −r)`), which together do state the full proposition; `radix_isometry` supports the radix map.

---

## Findings

Severity scale: **critical** (a false or unsupported headline claim), **major** (a defect that should be repaired before release, with no known mathematical error), **minor**, **editorial**.

### Major

**1. Scope and evidence conflation in the abstract and all submission texts** (`paper.tex` l. 13; `submission/abstract.txt`, `summary.md`, `alphaxiv.md` abstract, `announcement.md` forum post; `metadata.toml` abstract)

*Problem.* (a) The paper abstract says that for "rational quadratics in a parameter-two Stoneham number" the argument gives "unconditional upper bounds strictly below one quarter". This is proved only for explicit families: Proposition 7.3(i) and (iii) are conditional on `H = liminf h_k`; Corollary 7.4 covers `D = 3`, `b ≡ 2 (mod 3)` odd, `C ≢ 1 (mod 3)` and `(b, D, C) = (5, 9, 0)`. The scripts show the bound genuinely fails for other cases (for example `C ≡ 1 mod 3` gives `sup Δ = 1`, and `b = 7`, `D = 3` gives `1`), and the registry (`ST-21`) records that existence of a rational quadratic attaining `1/4` is open. A reader of the abstract would take the statement to hold for every rational quadratic. (b) `abstract.txt`, `summary.md`, `alphaxiv.md` and the announcement say "the kernel-verified plateau-cycle law, resonant-radix classification, **and unconditional sub-quarter discrepancy bounds**". Grammatically the adjective covers all three, but the sub-quarter bounds are a Lean-supported paper proof plus a finite exact enumeration (Proposition 7.3, Corollary 7.4), not kernel-verified.

*Fix.* Paper abstract: "…to obtain unconditional upper bounds strictly below one quarter for explicit families, such as `(α²−2α+C)/3` for odd radices `b ≡ 2 (mod 3)`". In every submission text, split the sentence: "the kernel-verified plateau-cycle law and resonant-radix classification, together with Lean-supported sub-quarter bounds for explicit families".

**2. The uniform-in-N consequence of Theorem 2.1 is used but never stated** (l. 204 in the proof of Theorem 3.3(ii); l. 263 in Corollary 4.3)

*Problem.* Theorem 2.1 as stated is a subsequential limit theorem. Theorem 3.3(ii) needs, and Corollary 4.3 implicitly needs, the *uniform* statement "given `ε > 0` there are `M` and `N₀` such that for every `N ≥ N₀`, `D_N(x) ≤ ε + #{n<N : den R_n ≤ M}/N`". The text says only "the block proof of Theorem 2.1 yields `M` such that `D_N(x) > ε` eventually requires `#{n<N : den(R_n) ≤ M} > εN/2`". I checked that this is true and does follow from the proof (the block estimate `sup_J |μ̃_N(J) − σ_{N,M}(J)| ≤ ε' + O((M+log²N)/√N)` is uniform in `N`, `Δ(σ_{N,M}) ≤ Σ_{m_c≤M} w_{c,N}`, and `D_N − Δ(μ̃_N) → 0`), so there is no mathematical gap. But a headline theorem (sparsity of exceptional scales, hence `D⁻ = 0` and logarithmic equidistribution) rests on a sentence that points back into a proof rather than into a numbered statement.

*Fix.* Add a lemma after Theorem 2.1: "**Lemma 2.2.** For every `ε > 0` there are `M` and `N₀` with `D_N(x) ≤ ε + N^{-1}#{n<N : den(R_n) ≤ M}` for all `N ≥ N₀`," with the two-line derivation above, and cite it in Theorem 3.3(ii) and Corollary 4.3.

### Minor

**3. Ridout's theorem: hypotheses used are standard but the citation is not pinned to a verifiable statement** (l. 317; `VERIFICATION.md` row "Theorem 6.3"; `LEDGER.md` "Theorems 6.1 and 6.3")

*Problem.* I could not retrieve the text of Ridout (1957) or (1958). From secondary sources (Waldschmidt, Bugeaud, Fraenkel's reference list) the result as used is: for a real algebraic `α`, a finite set `S` of primes and `ε > 0`, only finitely many rationals `u/t` with `t` an `S`-integer satisfy `|α − u/t| < t^{-1−ε}`. That is what the proof needs, and the application is valid: `y` is real, positive and irrational; `S` = primes of `Bcd` (so `gcd(c,d) > 1` is irrelevant); the approximants have `t ≤ B^s s²` and error `O(B^{-s−ηP})`, and `s/P ≤ 1 + r₂` is bounded, so `ε < η/(2(1+r₂))` works. The manuscript, however, says "[Theorem, p. 125] (taking `μ = 1, ν = 0`; see also [ridout])". I cannot confirm that the 1957 theorem is parametrized by `μ, ν` in this way (some secondary sources attribute the `p`-adic statement to the 1958 paper). A mis-citation of an external input is the one kind of error a specialist would catch immediately.

*Fix.* State in the proof the exact corollary used (finiteness of `u/t` with `S`-integer `t` and `|α − u/t| < t^{-1−ε}`), name it "Ridout's theorem", and cite the two Mathematika papers without the `μ, ν` parametrization unless a human has checked p. 125. Record in `LEDGER.md` that the page-level claim is unverified by AI review.

**4. `Lean-supported paper proof` labels are thin for Theorem A, Proposition 3.1, Theorem 3.3 and Corollary 4.3** (l. 28, 122, 167, 255; `VERIFICATION.md` l. 33)

*Problem.* The label satisfies the contract ("named steps are Lean declarations") and `VERIFICATION.md` states plainly what Lean does not prove. But the in-paper headings give a reader no hint of how little is formalized for general `(B, p, q)`: the Lean items are the binary ternary/quinary endpoint congruences and shape identity, the binary `simultaneous_ultrametric_spacing` (which is elementary divisibility), the real inequalities, and `SmoothOrbit`/`CircleDiscrepancy`. The Mahler–Newton isometry, the flow equidistribution, the tower-sparsity argument, the certificate-to-bound logic and the `4/11` dominance step are paper-only. The proof of Corollary 4.3 (l. 263) links no Lean step at all, though it is labelled Lean-supported.

*Fix.* Add after each such heading one sentence of the form "Formalized: …. Not formalized: …", or for Corollary 4.3 name the inherited steps (`boundary_strip_piecewise_le` via Theorem 3.3, `single_shape_one_one_max` via Proposition 4.1). Consider "Paper proof with Lean-checked components" for Theorem A.

**5. Proposition 3.2: a vacuous case and one confusing sentence** (l. 164)

*Problem.* "In the remaining case `m = a−1 ≥ 0`…" cannot occur: `m ≡ a (mod u)` with `u ∈ {2, 4}` and `m < a` forces `m ≤ a − u ≤ a − 2`. The paragraph is harmless but distracts from the real case analysis, and the claim "(the smallest negative index) … with nonzero coefficient `p − 1` when `a > 1`" is stated for `m ≤ a − 2` without saying that for `m ≥ 1` one needs `a ≥ 3` (automatic).

*Fix.* Delete the "remaining case" sentence and state that `u ≥ 2` excludes `m = a − 1`.

**6. Proposition 4.1, last sentence: a sketch carries a claim** (l. 228, 235)

*Problem.* "Every fixed joint-depth failure set has ordinary upper density at least `M_{p,q}`" is stated without defining the set. The proof (l. 235) is correct in outline (density of `{iA₀ log p/(D₀ log q)}`; residue conditions imposed on shape `(1,1)` through Proposition 3.1; cutoffs at `N = PV`) but compresses the requirement that *both* residue classes (`K mod vq^{k−1}`, `L mod up^{h−1}`) and the approach `r → r_*` be achieved simultaneously along infinitely many shells. It is used only for the sharpness remark at l. 43, not for any upper bound.

*Fix.* Define "joint-depth failure set" `{n : ≥ h layers lost at p and ≥ k at q}` and expand the last paragraph by two sentences, or move it to a remark. Also make clear in l. 43 that sharpness concerns the *method* (the bounded-denominator density), not `D⁺`.

**7. Section 7, l. 321: `R_n` is not fully defined** 

*Problem.* "retaining ordered pairs `2^i + 2^j ≤ n` in the square, terms `2^j ≤ n` in the linear sum, and `Cb^n`" omits the coefficients `A`, `E`. The Lean `«prefix» b n A B C₀ = A·pre + B·linearPrefix + C₀bⁿ` makes it clear, but the paper does not.

*Fix.* Write `R_n = A Σ_{2^i+2^j≤n} b^{n−2^i−2^j}/2^{i+j} + E Σ_{2^j≤n} b^{n−2^j}/2^j + Cbⁿ`.

**8. Unlabelled assertions at l. 395** 

*Problem.* (a) "`κ₀(λ) = −C_int(λ)/λ` is transcendental as a function of `λ` over `ℂ(λ, e^{λ/2^m})`" is a paper proof in `notes/phase16/dyadic-stoneham.md` (A.2, function-field, "trace and pole arguments"), unlabelled and uncited in the manuscript; the paper itself concedes it is irrelevant for fixed integer `b`. (b) "reducing any cycle-supremum bound to finitely many small dyadic levels" for general `D = 2^e D₁` is asserted without proof or label.

*Fix.* Either drop (a), or label it "Paper proof (see notes), not used below"; mark (b) explicitly as an unproved remark.

**9. Notation clashes** (throughout)

*Problem.* `λ` is Lebesgue measure (l. 22) and the 2-adic limit `lim δ_j` (l. 330); `K` is the shell index (l. 48) and a threshold index (l. 93); `c` is a cycle (l. 50) and an integer parameter (l. 18, 310); `D` is the discrepancy (`D_N`), the grid dimension in `(A, D)` (l. 239) and the denominator in `y = (Aα²+Eα+C)/D`; `A` is the coefficient, `q^u`, `PQR_n` and a grid size; `M` is the denominator cap and `M_{p,q}`; `d` is both the shape coordinate and an integer parameter (Section 6).

*Fix.* Rename the 2-adic `λ` (say `λ₂` or `ϖ`), the threshold `K` (say `n₀`), and either the Section 7 denominator or the Section 4 grid size; write cycles as `\mathfrak c`.

**10. Logarithmic equidistribution is used before it is defined** (l. 35, 169, 182, 212)

*Problem.* Theorem A and Theorem 3.3 assert it; the definition appears only inside the proof (harmonic weights `1/(n+1)`, "in the sense of Tsuji").

*Fix.* Define in Section 1: `{xₙ}` is logarithmically equidistributed if `H_X^{-1} Σ_{n<X} 1_J(xₙ)/(n+1) → |J|` for every arc `J`.

**11. Antecedents for the short-orbit estimate** (l. 67; `LEDGER.md` Theorem 2.1; bibliography)

*Problem.* The text calls `SmoothOrbit` "a qualitative counterpart of Vandehey's short-orbit bound". `notes/phase19/literature.md` (now in the branch) records that general-modulus short-orbit estimates are classical: Korobov (1970 Lemma 1; 1972 Lemma 2: square-root bound for `N` up to the order), Bourgain (2005, 2008, Thm 8.28, under divisor-order hypotheses), Konyagin–Shparlinski (1999), and that Vandehey's bounds are for a fixed finite prime set (the case used here). None is cited. This is not a priority claim, but readers will ask why the fixed-support case was needed.

*Fix.* Add one sentence after l. 67 citing Korobov and Bourgain, noting that their hypotheses (order, divisor-order conditions) are not available for the shifted prefixes whose denominators are arbitrary `{p,q}`-smooth numbers, and that Vandehey's fixed-prime-support bound is the relevant input. Add the entries to `references.bib` and `LEDGER.md` (Phase 19 literature has full details and DOIs; each must still be checked against the primary source per the contract).

**12. Bibliography: attributions and citation detail** (l. 45, 145, 317; `references.bib`; `LEDGER.md`)

*Problem.* (a) "Stoneham … proved normality for primitive-root radices" is vague. The usual summary is that Stoneham (1973) proved `b`-normality of `α(b,c)` for `c` an odd prime and `b` a primitive root modulo `c²`; I could not open the paper to confirm. (b) "additive normality preservers are characterized by zero entropy [kamae, rauzy, weiss]": Kamae (1973) concerns normality-preserving *subsequence selection*; the additive characterization is Rauzy (1976) (with Weiss's CBMS notes as exposition). (c) The `\cite{mahler,robert}` at l. 145 gives no theorem or page, although the contract requires them for external inputs (`VERIFICATION.md` supplies "Thm 1, p. 25" and "Ch. 4 §2, pp. 173–179", which I could not confirm). (d) `bd`: the `LEDGER` cites "Thm. 8.1 and Cor. 8.14" of Bergelson–Downarowicz; an earlier internal review (`notes/phase18/reviews/translation-summation.md`, "Untested") lists exactly these numbers as unverified, and `notes/phase19/literature.md` does not re-verify them. I confirmed only the paper's existence and abstract. (e) The Wall (1949) entry points to a Berkeley department listing (it confirms the thesis exists but is not a stable link to it). (f) `twosum` and `mira` are repositories at pinned commits that I could not independently access; the entries are labelled as repositories, which is appropriate.

*Fix.* Rephrase (a) with the precise hypotheses or cite them in `LEDGER.md` as "to be confirmed"; re-attribute (b) ("normality-preserving selections: Kamae; additive preservers: Rauzy, Weiss"); add theorem/page to (c) or soften; mark (d) `unverified` in the ledger; mark (e) `note = {unverified}` per the contract.

**13. `LEDGER.md` search record is generic** 

*Problem.* The contract asks for "formulations searched … databases … reference trails". The records list databases (arXiv, zbMATH Open, Google Scholar) and a few phrasings, but not dates, queries per theorem, or negative results; the entries for Proposition 3.2 and Theorem 3.3 reuse one line. Priority language is properly qualified ("apparently new in the sources examined"), and no unqualified priority claim appears anywhere in the manuscript or submission files.

*Fix.* Add the actual query strings and dates per ledger entry.

**14. Phase 19 consistency: no statement changes, but the open-problem discussion should record the obstruction** (l. 43, 292, 395)

*Problem.* `notes/phase19/nonlinear.md` ("Scope of the jump argument") and `README.md` state: the curvature/second-moment argument that resolves the flagship square does not apply to the degree-two resonant combination of `α(b,2)` or to "the simultaneous exceptional shell indices of the unmodified mixed-prime product", because the relevant variables are coupled integer shell indices and real-shell nullity does not control their visits to growing-depth residue classes; for the dyadic leading mass the complementary open plateaus carry all Lebesgue measure, so nonvanishing on plateaus is a sufficient test, while "determining the open plateau values in unresolved degrees remains necessary." I compared these with the manuscript. Everything the paper states about open problems (ordinary normality of `α(2,3)α(2,5)`; `q_k → ∞` for `α²−2α`; whether `C₀ = 0`) is consistent with Phase 19, and nothing in Phase 19 strengthens or contradicts a theorem here. The Phase 19 handoff correction (the prime-5 valuation paragraph in the Phase 18 translation/summation review) concerns a different argument and does not touch this manuscript (the prime 5 in Proposition 3.2 is a `5`-adic Teichmüller computation unrelated to multiplicative orders). Metadata correctly keeps `lean_commit = e4809cf…` since no Phase 19 Lean declaration is used.

*Fix.* In `LEDGER.md`, add a Phase 19 cross-reference under Theorem A and Theorem 7.1 (pin `c2c9da6…`). In the body, add one plain-language sentence to the Remark at l. 292 and to the final paragraph (l. 395): the method that settles joint normality for a real-parameter shell schedule does not apply here because the exceptional shell indices `(K, L)` are coupled integers. No phase vocabulary in the body; the contract allows phase notes only in `VERIFICATION.md` and `LEDGER.md`.

**15. Abstract wording "exact bound 4/11"; `metadata.toml` "sharp bound 4/11"** (l. 13; `metadata.toml`)

*Problem.* `4/11` is the threshold produced by the bounded-denominator method (`M_{3,5}`), not a proven sharp bound for `D⁺`; "exact" and "sharp" can be read as `D⁺ = 4/11`. The theorem (l. 37–40) is correct and precise.

*Fix.* Use "the threshold `4/11`" in both places.

**16. Abstract omits the standing coprimality hypothesis** (l. 13)

*Problem.* "distinct odd prime parameters" omits `gcd(B, pq) = 1` (Theorem 2.1 requires it; `abstract.txt` includes it).

*Fix.* Add "coprime to the radix `B`".

### Editorial

**17. Repository process language in the body.** l. 296: "These results were previously placed in the first version of the companion Stoneham-polynomial manuscript and are consolidated here." Cite Paper I (v1.1) as a reference and say the results are proved here for completeness. The contract also asks that phase names not appear in the body; the body is clean except in the Data availability section (script file names `phase16_…`, `phase17_…`), which is permitted.

**18. Undefined coined terms** in the body: "zero-slack" (l. 43), "primary `(1,1)` plateau" (l. 224), "joint-depth failure set" (l. 228), "bulk shape" (l. 202), "lifted loss residues" (l. 239), "shape" (defined, fine). Define on first use or paraphrase.

**19. Organization.** The kernel-verified `43/45` theorem (Section 6) and the intermediate Lean bounds (Remark 6.2) appear after the strictly stronger Theorem A, and Section 6's opening sentence ("Before applying higher-precision `p`-adic lifting…") reads as a leftover from a chronological draft. A short roadmap at the end of Section 1 would help (it exists in compressed form at l. 45).

**20. Density.** Sections 2–3 compress several independent arguments per paragraph (e.g. l. 93, 193, 202). Display the two-case argument for "distinct late shells of one shape force both indices to increase" as a numbered claim, and the Teichmüller computation in Proposition 3.2 as a lemma.

**21. Submission templates** (`reviewer-inquiry.md`). The contract asks that each inquiry pose *one* specific question. Template 1 asks two (soundness of Theorem 2.1 plus Section 5; prior results for products); Template 2 combines the mixed-product `p`-adic roots with the dyadic `κ₀` problem. Each template should name one theorem, the closest prior work, and one question. Neither contains real email addresses (checked), and each uses `[Name]`.

## Scope and exposition checks (brief items 2 and 6)

* **Open status of normality.** Stated plainly: abstract (l. 13: "Ordinary binary normality remains open"), l. 43, Remark l. 292 (also: "whether any nonempty integer prefix exists beyond `3^12`, whether `C₀ = 0`, and whether `α(2,3)α(2,5)` is binary normal all remain open"), and for `α²−2α` at l. 395.
* **Finite vs asymptotic.** The `3^12` scan and the four certificates are labelled `Finite certificate` (Proposition 4.2) and kept separate; the remark at l. 292 says the scan "is independent of the asymptotic equivalence". The only potential for confusion is that Corollary 4.3 (asymptotic) consumes the finite certificate; the proof says so explicitly (l. 263).
* **Build and layout.** `wsl -d Ubuntu -- bash papers/wsl-build.sh 08-stoneham-product-orbits` succeeds (15 pages, no undefined references or citations); the rebuilt PDF is byte-identical in tracked content (no `git status` change). Page 1 and the table page (p. 8) are clean; no clipping seen. Theorem numbering (2.1, 3.1–3.3, 4.1–4.3, 6.1–6.3, 7.1–7.4, and Theorem A) matches `VERIFICATION.md` and `LEDGER.md`.
* **Style.** Professional register; no hype or conversational transitions; evidence labels and AI-use disclosure present in the contract wording; byline and contact route as decided by the owner. Issues are the undefined terms (18), notation clashes (9) and density (20).

## Literature (brief item 5)

Checked against primary sources or authoritative catalogue records (publisher, EuDML, IMPAN, Project Euclid, arXiv, Cambridge/Springer DOI landing data as returned by search): Stoneham 1973 (Acta Arith. 22, 277–286; DOI matches), Bailey–Crandall 2002 (Exp. Math. 11, 527–546; DOI matches; the theorem number and page `Cor. 4.9(i), p. 536` not confirmed), Bailey–Borwein 2012 (Ramanujan J. 29, 409–422), Ridout 1957 (Mathematika 4, 125–131) and 1958 (Mathematika 5, 40–48), Mahler 1958 (Crelle 199, 23–34), Kamae 1973 (Israel J. Math. 16, 121–149), Rauzy 1976 (Acta Arith. 29, 211–225), Tsuji 1952 (J. Math. Soc. Japan 4, 313–322), Bugeaud–Laurent 1996 (J. Number Theory 61, 311–342), Bergelson–Downarowicz (arXiv:2506.12929; abstract confirms the multiplication counterexamples), Vandehey (arXiv:1606.07911 exists; the journal reference was not independently confirmed), Wall's 1949 Berkeley thesis (listed; no full text). I did not independently confirm Weiss (CBMS 95), Robert (GTM 198), Nishioka (LNM 1631) or Bugeaud (CTM 193) beyond their bibliographic data, nor the two repository citations. Antecedent credit is adequate (Stoneham, Bailey–Crandall, Bailey–Borwein, Wall, Kamae/Rauzy/Weiss, Bergelson–Downarowicz, Captain Sude, Mira Cult); gaps are in finding 11 and 12.

## Submission files and the Paper III audit (brief item 7)

* `abstract.txt` is 222 words (limit 250). `announcement.md`: the X post is 260 characters (limit 280, matches its own count). `metadata.toml`: required keys present; `registry_ids` `ST-06 … ST-35` all exist in `docs/registry/ST.toml` and match the topics. `alphaxiv.md`: author, contact route, MSC codes, AI-use disclosure (contract wording), and the *Verification scope* paragraph are accurate and carefully labelled ("Three headline results are completely kernel-verified…"); the only defect is the shared abstract sentence of finding 1. `reviewer-packet.md`: statements, evidence labels and "review requested on" steps match the paper; it is the most precise of the submission files (it flags the `gcd(c,d) > 1` Ridout application, the endpoint counts, and the Teichmüller and empty-fibre steps, which are the right steps to ask a specialist about).
* **Paper III audit** (`papers/wave2-audits/paper-III-audit.md`). Factual claims I could check are correct: `CR.toml` has 7 and `DS.toml` 11 entries; the last commit touching `CR.toml`, `DS.toml` or `papers/03-signed-resonance/` is `3545d5f`; `papers/manifest.toml` has `superseded_by = ""` for the paper. No overclaiming in the text. **Limitation (minor):** the audit is explicitly based on `e4809cf` and Phases 13–18, but the Wave 2 contract was updated the same day to merge Phase 19, and Phase 19 touches Paper III's territory: `notes/phase19/literature.md` cites `TranslatedShells.lean` (Paper III, `DS-03`) as an internal benchmark, and `geometry.md` (sharp translation formula, kernel `ℤ[1/b]`, scalar-dilation test, anchored/multidimensional counterexamples) overlaps the translation and dilation results. I read the relevant passages and see no conflict with Paper III's `D_∞(mX + r) = D_∞(X)·D(r)` (the Phase 19 counterexamples concern anchored or two-dimensional versions, which Paper III does not state), and the audit's item 2 (Rauzy converse for signed phases) rests on Paper III's uniformity and concentration theorems, not on the invalid prime-5 paragraph in the Phase 18 review that the Phase 19 handoff retracts. So the recommendation (retain v1.1 unchanged) appears right, but the audit should say so itself. **Fix:** add a short section "Phase 19 (merged at `c2c9da6`)" recording that geometry/addition/signed-transform material was compared with `CR`/`DS`, that the handoff correction does not affect the audit's item 2, and re-affirming the recommendation. I did not exhaustively verify its claim that no Phase 13–18 review found an error in Paper III, nor the statement about Mira Cult's note being "already tracked" in Manuscripts B and E.

## Recommendation to the owner

Release is reasonable once findings 1 and 2 are repaired and the evidence/scope wording in findings 3, 4, 14 and 15 is tightened; the remaining items can be handled in the same editing pass. Human specialist review is still outstanding, and the steps on which it would be most useful are those the reviewer packet already lists, plus the page-level Ridout citation (finding 3) and the antecedent search for Korobov-type short-orbit estimates in the discrepancy-of-products literature (finding 11).
