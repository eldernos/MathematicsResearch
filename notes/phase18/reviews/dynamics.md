# Independent review: Phase 18 dynamical claims

Scope: `translations.md` (sharp worst-case translation equality, fixed-point classification, sparse sums, determinism), `programming.md` (cubic programming, B1–B4, invariant-measure cluster sets), `liouville-realization.md`, `certificate.md`, reviewed at the parent working tree `MathematicsResearch-phase18/notes/phase18` on 25 Nov 2026, including `NormalityChecker/SharpTranslation.lean` as linked. No subagents were used. Evidence types: **H** = re-derived by hand, **N** = exact-rational numerical test (scripts kept in the reviewer scratchpad, not committed), **S** = repository script rerun, **U** = not independently verified.

## Verdict

All mathematical claims reviewed are correct as stated. Two objections require edits (one broken dependency, one overstated wording); minor clarity items follow. No counterexample was found to any claim.

## Results

### R1. Finite comparison, `|D_N(u)-D_N(v)| ≤ min(1, E/N+2ε)` — correct (H, N)
Enlarging each test arc by ε (+h for atoms) and complementing for deficits is valid, including atoms and arcs across zero. N: 20 000 random paired samples on grids of denominator 2–12, with atoms, ties and ε on the grid: 0 violations. The exact discrepancy formula (max post-jump minus min pre-jump of F−t) was cross-checked against brute-force closed/open arc enumeration on 300 random multisets.

### R2. Sharp equality `sup_x |D_N(x+z)-D_N(x)| = 1-D_N(z)` — correct (H, N, Lean text)
- Upper bound: for a closed arc J of length l, centre c, with T^n z∈J for a fraction 1−e, ‖T^n(x+z) − (T^n x + c)‖ ≤ l/2 on good positions, so the finite comparison gives e+l. The infimum over J is 1−sup(μ(J)−l) = 1−D_N(z): closed-arc positive excess equals the half-open discrepancy (limit h↓0, then complementation). Atoms are handled.
- Attainment: D_N(0)=1 for all N>0 (arcs [0,h), h↓0), so x=0 gives exactly 1−D_N(z).
- N: 4 000 random cases (b∈{2,3,4,10}, N≤30, z with denominators up to 63 and mixed radix/non-radix parts, 25 random rational x each, denominators up to 127): 0 violations of ≤, and equality at x=0 in every case.
- Edge cases N=1 and z∈ℤ (both sides 0) are consistent.
- Lean: `sharp_translation`, `sharp_translation_zero`, `sharp_translation_isGreatest` contain no `sorry`/axiom text; the statement (inequality plus IsGreatest attainment) is exactly the claimed equality. I did not run `lake build` (the parent owns it), so kernel acceptance is **U**.
- Equivalences (D_N(z)→1 ⇔ pointwise ⇔ uniform ⇔ preservation of lower/upper asymptotic discrepancy; lower discrepancy at x=0 suffices because liminf D_N(z)=1 with D_N≤1 forces lim=1): correct.

### R3. Fixed-point classification `z = c+w`, `(b−1)c∈ℤ`, `M_N(w)→0` — correct (H)
Nearly maximal positive arcs have length →0 and mass →1; weak limits are point masses; invariance by telescoping; the cluster set of empirical measures is connected because successive BL-distances are ≤2/(N+1); a connected subset of the b−1 point masses δ_c is one point; M_N(z−c)→0 since T^n(z−c)=T^n z−c. Converse by concentration near c. All steps valid. The class includes nonzero fixed points c=j/(b−1) for b>2 (z=c has D_N=1 but M_N(z)↛0); the note states this correctly and the later determinism bullet correctly says "if M_N(z)→0" (c=0).

### R4. Sparse signed integers — correct (H)
Charging/uncharged-shift bound; the ε choice `Ab^{-L}/(b−1)`; the charge window `[m_j−w_j+1−L, m_j)`; the O(log(2N)/√N) rate for m_k=k(k+1) (L=⌈log₂(N+1)⌉); irrationality; Liouville/transcendence for k!; the normal-number counterexample (digit blocks at m_j=2^j). The Markov bound `2√(2M_N)` is right (ε=√(M/2): M/ε+2ε=2√(2M)).

### R5. Determinism and arithmetic examples — correct modulo external citations (H, U)
- Base 2, z=1/3: limiting discrepancy 2/3 (arc [1/3,2/3] has mass 1, length 1/3). Correct.
- Tightness bullet (concentration on a countable union of cycles ⇒ entropy 0): correct.
- Density-zero-of-ones ⇒ window frequency→0 ⇒ M_N→0 and determinism, including disjunctive expansions: correct.
- Entropy transfer symbol→circle (fibres ≤2, conditional entropy of the name given its image ≤log 2, hence zero per digit): correct.
- Paper III mixture test: "nonzero-shell share ≥(p−1)/p at the end of a nonzero shell" is immediate from shell geometry; entropy (1−θ)log b by affinity. Correct given the cited Paper III theorems.
- **U**: Rauzy (Acta Arith. 29), Bergelson–Downarowicz Definitions 3.5/3.10, Theorem 3.12, Theorem 8.1, Corollary 8.14 were not re-checked against the sources.

### R6. Cubic programming theorem, B1–B3, estimate (3) — correct (H, N, S)
- B1 recurrence, positive representative, reduced-denominator formula, dense geometric group: re-derived.
- Period lemma (the input): ord_{p^e}(b)=t·p^{max(e−v,0)} for odd p∤b (lifting the exponent); the orbit of a unit is t classes mod p^v, each an equally spaced grid of p^{e−v} points, discrepancy ≤p^{v−e}; P≤p^e since t≤p−1. True, but not proved in the repository (Objection 1).
- Eqs. (1), (2), the tail estimate `B_0 b^{−(n_{k+1}−n)}`, `k<q_k≤pk`, `h_k≤7tk²`, the summation by parts (≤2Ch_{K−1}) and the constants in (3): re-derived line by line.
- N: with exact Fractions I built the true series (truncated three blocks past the cutoff, tail error included) for (b,p,δ) = (2,3,2/5), (10,3,1/3), (2,7,7/10), (3,5,0), (2,3,1), and compared |D_N−δ| with the right-hand side of (3) at **every** N up to 300–900: 0 violations; worst ratio actual/bound 0.11. So (3) holds with the stated constants.
- Worked example (b=2, p=3, δ=2/5): masks 0,0,1,0,1; exponents 2,16,54,128,250; targets 1/3,1/3,0,1/9,0; coefficients 1/3,1,2/3,1/9,5/9. All re-derived. `scripts/phase18_programming.py` passes, including the N=400 interval.
- Unfinished-interval counterexample (n_{k+1}=n_k+q_k², u_k=1/q_k): the first ⌊½log_b q_k⌋ positions have model ≤q_k^{−1/2} and outnumber the n_k earlier positions (½log_b q_k = ½n_k² log_b p ≫ n_k), so D_N→1 at those cutoffs. Correct, and it genuinely shows the need for the W/E_N unfinished-block control.
- Floors/computability: rational δ exact; computable irrational δ has kδ irrational so floors are decidable by enclosure; the uniform variant S_k=Σd_i, a_k=⌊S_k⌋−⌊S_{k−1}⌋ gives |Σa_i−kδ|<2, so C=2 in (3). The remark that no uniform exact floor test exists at rational boundaries is correct.
- Irrationality: δ=1 by isolated ones with unbounded gaps; δ<1 because the limit has a Lebesgue part while rational orbits have finitely supported limits. Limit measure (1−δ)λ+δδ_0 has entropy (1−δ)log b. Correct.
- Transcendental realizations: freedom at k=2^j costs ≤(28t/3)K² (Σ4^j≤(4/3)K²); distinctness since 2B_0b^{−h_k}<1/q_k eventually; countably many algebraic numbers; computable diagonalization via the farther of {0,1/q_k} (≥1/(2q_k)−1/(16q_k) from the approximant). Correct. Distinctness is guaranteed only for mask sequences differing at some index ≥k_0; the continuum claim is unaffected.

### R7. B4: mixtures, all pairs (α,β), weak-limit sets — correct (H)
- Deficit-maximizing scheduler: overcounts ≤1 and ≥−(m−1). Correct.
- (liminf, limsup)=(α,β) with K_{j+1}=K_j²: earlier-stage weight ≤K_j^{-3} of N at stage ends, weighted rounding error ≤t+3h_K, intermediate values by step ≤1/(N+1). Correct.
- Weak-limit sets: necessity (invariance, BL step ≤2/(N+1), connectedness) and sufficiency (periodic digit-word approximation with error b^{−r}+2r/L; chains in a connected compact set; stage construction) are valid. Scalar continuity of D under weak convergence (grid with endpoints off the atoms of μ, 2η enlargement) is correct, including atoms; the closing caveat about arc endpoints moving through an atom is the right one. The cycle laws use denominators dividing b^M−1 (not p-powers), as the note says.

### R8. Liouville realization — correct (H)
- Words: V_k (all b^k words, length kb^k), W_k = a_k zero blocks + (k−a_k) copies of V_k, P_k=k²b^k, |a_k/k−δ|≤2/k. Window uniformity of V_k at every internal offset is exact; union-of-depth-l-cells error ≤(l+1)/k. Ambiguity with all-(b−1) tails is excluded (V_k contains 0^k).
- Insertion at n_k=b^{(k+2)!}: P_k=o(n_k), ΣP_i=o(n_K); unfinished plateau costs ≤P_K≪n_K≤N; early plateaus (k<l) cost O(1); later ones ≤(l+1)/k·ℓ_k. Interval squeeze δ(1−b^{−l})−o(1) ≤ D_N ≤ δ+2b^{−l}+o(1): correct. Real-tail error b^{−H}/(b−1) off the last H places before an insertion: correct.
- Liouville: x_k has denominator ≤b^{n_k}(b^{P_k}−1), tail ≤b^{1−n_{k+1}}/(b−1), n_{k+1}/(n_k+P_k)→∞, x_k strictly increasing so q_k→∞ and x_k≠x. Correct. Full D_N→δ for all N (not a subsequence); no rate is claimed, and none is proved.

### R9. Certificate and bounded-denominator necessity — correct (H)
Upper certificate `(U+E+Σ|B_i|Δ_i)/N+2ε`; period block error `|B|d+min(P,|B|)`; necessary bound `D_N ≥ (H_Q−E)/(N|F_Q|)−2ε` (pigeonhole over the |F_Q| centres, arc of length ≤2ε+2h about the heaviest, using the circle at 0); the converse `H_Q/N+5η` (U=H_Q+ηN, E≤ηN, Σ|B_i|Δ_i≤ηN, ε=η). Counterexamples: states 0 and 1/3 in base 2 (limits 1 and 2/3); raw-truncation pairs (+2^{−k}/3 at k, −2^{−k}/3 at 2k): unfinished shifted sum (2^{⌈n/2⌉}−1)/3 has circle distance 1/3 exactly when ⌈n/2⌉ is odd, i.e. n≡1,2 (mod 4). Verified.

## Objections and corrections

1. **Broken dependency (must fix).** `[principal family](principal.md)` and `[prime-power period lemma](principal.md)` occur five times in `notes/phase18/` (`programming.md` lines 11 and 81, `certificate.md` line 25, others); no `principal.md` exists in `notes/`, `notes/phase18/` or at HEAD. `programming.md` calls this lemma "the only arithmetic input", so the central cubic theorem currently rests on an unreachable proof. Supply the target or inline the proof: for odd p∤b, lifting the exponent gives ord_{p^e}(b)=t·p^{max(e−v,0)}; the orbit of a unit mod p^e is t classes mod p^v, each an equally spaced grid of p^{e−v} points, so every arc misses its expected count by ≤1 per grid, i.e. discrepancy ≤p^{v−e}; and P≤p^e because t≤p−1.
2. **Overstated wording.** `translations.md` calls the Phase 17 estimate "the sharp uniform translation rate". Phase 17 proves 1−D_N(L_χ) ≍_χ log log N/√(log N), with χ-dependent constants. The supported statement is: sup_x|D_N(x+L_χ)−D_N(x)| equals 1−D_N(L_χ) exactly, hence has exact order log log N/√(log N) in that range.
3. **Minor clarity.**
   (a) `translations.md`, determinism bullet 3: the digit-change test is stated for b=2 only; add that for b>2 a long constant digit block c lies near the fixed point c/(b−1), which is nonzero unless c∈{0,b−1}, so the test does not extend.
   (b) `certificate.md`, "Why the hypotheses matter", first sentence: state the pointwise model 1/p^{⌊log_p(n+2)⌋} and which orbit relation fails when numerators change independently.
   (c) `programming.md`, "All pairs": say which of α, β is used on each [K_j,K_{j+1}).
   (d) `programming.md`, weak-limit sufficiency: the N^{-1/3} rate is for bounded-Lipschitz distance of the measures, not for D_N.
4. **Unverified external items** (cannot be certified from this checkout): Rauzy 1976 characterisation, Bergelson–Downarowicz numbering, Sigmund 1974, and Lean kernel acceptance of `SharpTranslation.lean`.
