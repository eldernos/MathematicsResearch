# Cross-provider verification check: Candidate Paper XIII

- **Target:** `papers/13-reciprocals-and-kernel-tower/` (`paper.tex`, `references.bib`, `VERIFICATION.md`, `LEDGER.md`), candidate draft v1.0, untracked in the Phase 23 working tree.
- **Reviewer:** Claude Opus 5.5 (Anthropic), auditing a draft assembled by Gemini 4. Check date 2026-11-27.
- **Cross-checked against:**
  - the notes `notes/phase23/euler-square-and-higher-order-tower.md` (Track A2) and `notes/phase23/convergent-reciprocals-and-schedules.md` (Tracks D1, D2, D4);
  - the reviews `notes/phase23/reviews/phase22-analytic-audit-shortorbits-reciprocals.md` (Audit 2, GF-26) and `notes/phase23/reviews/track-d124-review.md` (M1–M5, m1–m18);
  - the Lean files `NormalityChecker/HigherOrderTower.lean` (working tree), `RadixPowerTower.lean` at `8ca4309`, and `NormalReciprocalCore.lean` at `347ec3f`;
  - `docs/registry/GF.toml` (`GF-16`, `GF-23`, `GF-26`, `GF-29`, `GF-34`).
- **Scope of this check:** I wrote only this file and modified no other file. I made no commits. I ran no Lean build and no LaTeX build. The Lean evidence below comes from reading statements, resolving names and checking pinned line anchors. The kernel replay on `hail` is the one recorded in `notes/phase23/verification.md`; I did not re-run it.

**Cross-model review is not independent human peer review.**

## 1. Archived release integrity — PASS

`git status --short` lists no change to `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml` or `docs/registry/papers.toml`. It also lists no change to any directory that `papers/manifest.toml` marks as archived:
- `01`–`06`;
- `01-…-v2`, `02-…-v2`, `04-…-v2`, `05-…-v2`;
- `03-…-v1.2`;
- `07-synthetic-expansions`, `08`, `09`, `10`.

The modified paper directories are `papers/07-synthetic-expansions-v2/` and `papers/11-generating-functions-digits/`. Neither has a manifest entry, so both are candidate drafts and fall outside the immutability rule. Paper XIII is untracked and has no manifest, SHA or registry entry, as its VERIFICATION.md says.

## 2. LaTeX structural integrity — PASS

I ran a Python check (scratchpad script, not committed) on `paper.tex`, with comments stripped, and on `references.bib`:

| Check | Result |
| --- | --- |
| Braces (`paper.tex`, `references.bib`) | Balanced; depth never negative |
| `\begin`/`\end` | 125 environments, properly nested, none unclosed |
| `\[` / `\]` | 45 / 45. A raw count gives 46 because `\\[3pt]` in the title line matches the pattern; it is not display math. |
| Inline `$` | Even count overall, and even in every paragraph |
| Labels | 67, with 0 duplicates |
| `\ref`/`\eqref`/`\cref`/`\Cref` | 55 distinct targets, 0 undefined. Twelve labels are never referenced, which is harmless: `eq:Pk-def`, `eq:deBruijn-envelope`, `thm:C`/`D`/`E`, `q:*`, `rem:Q1-motivation`, `sec:intro`, `sec:ai`. |
| `\cite` | 11 distinct keys, all defined. 11 bib entries, 0 uncited, 0 duplicate keys. |
| Macros | `\e`, `\den`, `\leanat`, `\evidence`, `remark` and `question` are defined in `papers/common/preamble.tex`. Theorem-like environments share the per-section counter, so the numbering 2.1–7.5 in VERIFICATION.md matches the source order. |

These counts agree with the structural-check paragraph in VERIFICATION.md.

## 3. Mathematical accuracy and repair fidelity

### 3.1 Lean declaration names and anchors — PASS

Every Lean identifier cited in `paper.tex`, `VERIFICATION.md` and `LEDGER.md` resolves to a declaration in the cited module. The modules are `HigherOrderTower`, `RadixPowerTower`, `NormalReciprocalCore` and `SimpleNormalityKernel` (`not_simply_normal_of_mem_kernel`, `not_two_normal_of_mem_binary_kernel`). No cited name is missing.

There are 19 pinned `\leanT`/`\leanR` links. Each one resolves, via `git show <commit>:<file>`, to the line that opens the named declaration:
- `RadixPowerTower` at `8ca4309`: L106, 307, 347, 467, 531, 553, 694, 817, 828, 846, 896, 928, 1012, 1069, 1209, 1247, 1272;
- `NormalReciprocalCore` at `347ec3f`: L74, 139, 255.

The working-tree line numbers in VERIFICATION.md for `HigherOrderTower` are also correct: L331, 522, 548, 715, 2065, 2228, 2779, 2854, 2983. `HigherOrderTower.lean` contains no `sorry`, `admit` or `axiom`. It is imported in `NormalityChecker.lean` and listed in `Audit.lean`.

### 3.2 Theorem A / §2 against `HigherOrderTower.lean` — PASS, one labelling nit

The Lean statements match the paper:
- `tower_iff`: (∃ x ∈ K_{b^k} \ K_b, L-normal) ↔ b^L ∣ k, for b, k ≥ 2 and L ≥ 1.
- `tower_irrational_exact_iff`: adds irrationality and ¬(L+1)-normality.
- `all_kernel_pow_iff`: ↔ b^L ∣ k ∨ (b = 2 ∧ L = 1).
- `radixDiscrepancy_le_grid_add`: holds for b ≥ 1 and every L, matching "b ≥ 1, L ≥ 0" in Theorem 2.5.
- `eventually_radixDiscrepancy_le_of_orderNormal`: this is the substantive eventual form, so the `limsup` form is not vacuous.
- `mem_pow_kernel_decomp`: unique r < b^k − 1 and u ∈ M_b, with x ∈ K_b ↔ (b^k − 1) ∣ (b − 1)r.

`Kernel` is defined as `Tendsto (radixDiscrepancy b x) atTop (𝓝 1)`, which is the repository's strong K_b.

Part (iv) is the exact real spectrum [0, 2/b^L] and (0, 2/b^L], the finite tour formula and tower density. It is labelled **Paper proof** throughout: in the abstract, the Theorem A label, Propositions 2.6–2.7, Theorem 2.8, §9 and VERIFICATION.md. Nothing here is overclaimed as kernel-verified.

I checked the proofs of Propositions 2.6 and 2.7 and Theorem 2.8:
- In the de Bruijn envelope, the bounds 2/(M+1) and (2/M)(1 − 1/(bM − 1)) follow from x, z ≥ 1/(bM − 1) and (M + 1)(x + z) ≤ 2.
- The mixture construction gives D_N → 2t/M.
- f_{0^{L+1}} → (1 − t)/(bM) + t/M gives exact order L for t > 0.

**Nit A1.** Theorem 2.1(i) asserts that the constant (b^k − 1)/(k(b − 1)) is sharp, attained at u = b^{−k}. The proof then says "every statement is kernel-verified". `RadixPowerTower.lean` proves only the upper bounds. Its module docstring says "sharp constant", but no declaration proves attainment. The attainment is true: at u = b^{−k} the ratio is exactly (b^k − 1)/(k(b − 1)). Fix: mark the sharpness clause as a one-line Paper proof.

### 3.3 Theorem B / §3 against `RadixPowerTower.lean`, Hull–Dobell and Bang–Zsigmondy — PASS, one labelling nit

- `orderOf_mul_pow_sub_one` and `orderOf_mul_pow_add_one` have hypothesis `D ∣ b^m − 1`. The paper says exactly this in the abstract, in Theorem B(i) ("Under D ∣ (b^m − 1), both order formulas are kernel-verified") and in Theorem 3.1's proof. It gives the wider rad*(D) Hull–Dobell lifting a separate written LTE proof, including the 2∥D parity case. This carries repair **M3** correctly: there is no miscitation.
- Lemma 3.5 (Bang–Zsigmondy rigidity) and Theorem 3.6 are labelled **Paper proof using External input**, with `Bang1886` and `Zsigmondy1892` cited. Both are listed under External inputs in VERIFICATION.md (repair **M4**). I checked the three exceptional cases in Lemma 3.5: m = 1; m = 2 with b + 1 = 2^t, where 4 ∣ rad*(b² − 1); and (2, 6), where rad*(63) = 21 forces 6 ∣ n.
- Line 451 states that (HD1)–(HD2) are only *sufficient* conditions forcing tetration. It does not exclude slower Hull–Dobell products, and Question 8.4 leaves them open (repair **M5(b)**).

**Nit B1.** Theorem B(ii) carries one label, **Lean-supported paper proof**, but it bundles normality (Theorem 3.3, Lean-supported) with the balanced rate and the Koksma barrier. Theorem 3.4 and VERIFICATION row 3.4 label those two **Paper proof**. The §9 sentence "Theorem B(i)–(ii) are Lean-supported paper proofs" repeats the bundling. Fix: label B(ii) as "Lean-supported paper proof (normality); Paper proof (rate and barrier)", or split it.

### 3.4 Theorem C / §4 against the Audit 2 repairs to GF-26 — PASS

I traced every GF-26 item in Audit 2 into the draft:

| Audit 2 item | Where it appears in the draft |
| --- | --- |
| Hull–Dobell normality, elementary (Major 1) | Theorem 3.6(ii), using d′ ∣ S_i ⇔ d′ ∣ (i+1) and an O(T_{K−1}/m_K) incomplete-cycle error |
| Bang–Zsigmondy barrier (Major 2) | Theorem 3.6(iii): S_i ≡ i+1 (mod b^{m_{K−1}} − 1) is exact at h = D_{K−2}; labelled External input |
| Uniform geometric higher-tail bound | Proposition 4.2(iii): z_{v+1} ≥ z_v + m_v, edge cut z_{u+1} ≤ 2m_u + 6, total tail ≤ 8b^{−2m_u−6} uniformly in the number of levels |
| Fixed-cutoff argument for eventually-plus sequences, reset-tail buffer r > m_K − √m_K | Theorem 4.4 proof |
| Prefix-independent "strictly from above" (Minor) | Theorem 4.4: lim_L limsup_N μ_N([1 − b^{−L}, 1)) = 0 |
| Half-open arcs; midpoint transport for W₁ (Minor) | Lemma 3.2(iii) |
| Ideal B_j versus empirical O(J^{−1/4}) bias kept distinct | Theorem 4.6(i) uses the empirical O(J^{−1/4}) and the stratum recursion B^{(j)} = (2B^{(j−1)}+1)/(2k_j+3) |
| Fixed or partial outer band: bound the whole product by M_s before applying the outer multiplier; absolute count of discarded periods | Theorem 4.6 Step 2 |
| Signed lift in (−1/2, 1/2]; depth-shifted melting β_{u,d} | Theorem 4.6 Step 3 |
| γ_N not monotone; use both shell endpoints and the one-step bound | Step 2 states a range, not monotonicity. Step 4 uses \|D_{N+1} − D_N\| ≤ 1/(N+1). |

I found no false L¹/L²-type claim or broken sign inequality. Specifically:
- ⅓ < R_k(ε) < 4 holds, since ∏(1 + 2^{−j})^{−1} > 0.41 and ∏(1 − 2^{−j})^{−1} < 3.47.
- Lemma 4.1(ii), \|D(μ) − D(ν)\| ≤ 2√(2W₁), is correct: minimising W₁/η + 2η gives the constant.
- The 0⁺ collapse ("simple normality ⇔ full normality within y(ε), even for b = 2") is stated with the repaired observable.
- The P_k(q) counts are correct: positive bands 2(k+2)(2k+1), negative bands 2k(2k+1), zero-band density 1/(2k+3), and tail q^d/P_k.

The VERIFICATION.md source table lists these repairs accurately.

**Nit C1.** Step 3 asserts D_{K−1} ≥ b^{(4k_{t_s}+2)m^{(t_s)}} without the "previous denominator ≥ 2, P_k(b^{−m}) > 1/2" justification that Audit 2 asked for. Add half a sentence.

### 3.5 Theorems D and E / §§5–7 against the Track D post-repair statements — PASS, one terminology issue

| Track D item | Draft |
| --- | --- |
| **M1** Strong K_b and M_b; all-N proofs | Introduction definitions. Equation (all-minus-Mb) proves m_N(x) → 0 along all N for any m_{j+1}/m_j → ∞; it is reused in Theorems 3.6, 7.1 and 7.4. Theorems 5.2 and 5.4 give the all-N argument for x. |
| **M2** Lemma 6.2 digit-label hypothesis | Lemma 6.2 requires labels "neither identically 0 nor identically b − 1" and includes the G_{3,6} self-loop remark. I checked that Δ_n ∈ (0, 1) under this hypothesis. |
| **M3** Citation of `orderOf_mul_pow_sub_one` | See §3.3 above |
| **M4** Evidence vocabulary; External input for Bang–Zsigmondy | Only repository labels appear. "Finite certificate" is used for exact scripts and "finite measurements" for floating-point values (§9). |
| **M5** Heuristics not stated as theorems | Remark 5.6 is explicitly heuristic, and its 1,050-divisor search (m15) is labelled Finite certificate. The (HD2) growth remark is at line 451, and Rung 4 is marked **Open** in Table 1. |
| m1 Connected support for word laws | Theorem 6.3(i) |
| m2 Δ′_k = ⌊√m_k⌋ | Proposition 5.4 |
| D_max(b, L) = 2b^{−L} | Theorem 6.1 gives exact attainment via G*_{b,L}, with the upper bound from Theorem 2.5. |
| G_{b,M}, M = lcm(1, …, b−1)·b^L | Lemma 6.2 and Theorem 6.3(ii). The common interval I_R gives D ≥ 2/(bM) − 2k_R/(RbM) − 2b/R > 0 for every convex combination of the μ(sr). |
| Anchored coprime O_{b,A}((ln N)^{−A}) | Theorem 7.1. I checked s_b, ord_{M^k}(b) = sM^{k−1}, q_k ≡ 1 (mod sM∏_{j<k} q_j) and the Erdős–Turán cutoff H = M^{K−2}. |
| Fully coprime base-2 CRT convolution | Lemma 7.2: the 01-window argument with x ∈ [¼, ½) is sound. Theorem 7.4: E_k = E_{k−1}·e_k with e_k ≤ E_{k−1} + error. Monotonicity then gives the decay even when ω_k grows slowly. |
| R_k^{(E)} exponential complete-period equidistribution | Theorem 7.5. I checked the anchor table, v_p(T′_k) ≤ ⌊log_p k⌋ and the 2-adic case b ≡ 3 (mod 4). |

**Minor D1: "exact L-normal" collides with "exact order L".** The introduction defines "of exact order L" as L-normal and not (L+1)-normal. The abstract, Theorem D(iii) and Theorem 6.3(ii) then say that 1/x is "exact L-normal … along all N", meaning that every cyclic L-word count is exact. A reader will take this to mean exact order L. That reading is **false** for the G_{b,M} construction.

The strict-interiority recursion Δ_{n+1} = bΔ_n − d_n puts x_n in the interior of cell b·u_n + d_n at resolution bM = Q·b^{L+1}. The walk traverses each edge exactly R times, so every multiple sr (s ∣ Q) is equidistributed over (L+1)-cylinders. So 1/x is in fact **(L+1)-normal**, never of exact order L. For b = 2, L = 1, the four edges 00, 01, 10 and 11 each occur R times.

The theorem as intended (L-normal and nonnormal) remains true. Its bounds are consistent with this observation, because 2/(bM) ≤ 2b^{−L−1}. Fix: write "L-normal (with exact cyclic L-word counts in the seed)" or define "exact L-normal" locally. The paper could also record the free strengthening to (L+1)-normality and D⁺ ≤ 2b^{−L−1}. The same wording appears in LEDGER.md under Theorem D and in the GF-34 title (registry outside this draft).

**Minor D2.** The Theorem D(iii) summary says the multiples sr share "a common empty interval". They do not: (0, η_R) contains the 0-loop points. The proof uses a common interval I_R with a uniform deficit. Reword to match.

**Nit D3.** Theorem D(ii) requires "positive mass to both digits", which is correct for all L. Theorem 6.3(i) requires positive mass on "words containing both 0 and 1", which is vacuous at L = 1: no length-1 word contains both digits. Use the Theorem D wording in both places.

**Nit D4.** The proof of Proposition 6.5 cites "mass 1 on the closure". For a liminf the portmanteau direction needs the *open* arc (1 − b^{−L}, b^{−L}) ∋ 0 on 𝕋. Its ν-mass is the same, so the conclusion stands.

**Nit D5.** The proof of Theorem 7.4(iii) writes "monotonicity and L ≤ L² force E_k(h) → 0". Here L is the undefined limit from the source note, and it collides with the word length L. Write ℓ := lim E_k(h) ∈ [0, E_{j₁}(h)] ⊂ [0, 1), so ℓ ≤ ℓ² forces ℓ = 0, and argue the same way for \|Ĉ_k(h)\|.

## 4. Evidence-label discipline and hygiene — PASS, with stale registry text

- **Label separation.** Kernel-verified, Lean-supported paper proof, Paper proof, Finite certificate, External input and Open are used consistently in the paper, VERIFICATION.md and LEDGER.md. The exceptions are Nits A1 and B1 above. The §9 scope paragraph keeps finite certificates, floating-point finite measurements and proofs apart.
- **pdflatex/bibtex.** Marked pending before release in §10 of the paper, in VERIFICATION.md (bold, under Status and Pending items 1) and in LEDGER.md (Outstanding check 3).
- **Human review disclaimer.** "Cross-model review is not independent human peer review" appears verbatim in paper §10, VERIFICATION.md and LEDGER.md. §10 also states that the assembled manuscript has not been reviewed as a whole.
- **No fake commit hash.** `HigherOrderTower.lean` is cited only as "built and verified … in the Phase 23 working tree, pending commit pinning". No hash is given for it in the paper (lines 68 and 920) or in VERIFICATION.md ("W (working tree …)"). The two pinned hashes, `347ec3f…` and `8ca4309…`, are real commits, and the anchored declarations exist there. Phase 23 scripts are described as untracked.
- **Minor H1: stale registry correspondence.** VERIFICATION.md says "Track A2 … and Track D1–D2–D4 additions do not yet have registry entries", and Pending item 3 and LEDGER Outstanding check 4 say the same. The working-tree `docs/registry/GF.toml` now has **GF-29** (HigherOrderTower tower and the 2/b^L spectrum) and **GF-34** (Track D). Both are uncommitted. Add GF-29 and GF-34 to the registry-correspondence line and turn the item into "commit the registry entries".

## Findings summary

| ID | Severity | Location | Issue |
| --- | --- | --- | --- |
| D1 | Minor | Abstract; Theorem D(iii); Lemma 6.2; Theorems 6.1, 6.3; LEDGER | "Exact L-normal" collides with "exact order L". The G_{b,M} reciprocal is actually (L+1)-normal. |
| D2 | Minor | Theorem D(iii) | "Common empty interval" should say "common deficit interval I_R". |
| H1 | Minor | VERIFICATION.md registry line and Pending 3; LEDGER Outstanding 4 | GF-29 and GF-34 now exist in the working-tree registry. |
| A1 | Nit | Theorem 2.1(i) | Sharpness attainment is labelled Kernel-verified, but there is no Lean declaration for it. |
| B1 | Nit | Theorem B(ii); §9 | One Lean-supported label covers the Paper-proof rate and barrier. |
| C1 | Nit | Theorem 4.6 Step 3 | Add the previous-denominator justification Audit 2 asked for. |
| D3 | Nit | Theorem 6.3(i) | The "both digits" hypothesis is vacuous at L = 1. |
| D4 | Nit | Proposition 6.5 proof | Use the open arc, not the closure. |
| D5 | Nit | Theorem 7.4(iii) proof | Undefined L in "L ≤ L²"; rename it ℓ. |

There are no Critical or Major findings. Every flagship statement checked survives: Theorems A–E, the Lean claims, and the Audit 2 and Track D repairs.

## Verdict

**ACCEPT WITH MINOR POLISH.** The archive is untouched, the LaTeX structure is clean, and every cited Lean name and pinned anchor resolves. The Audit 2 (GF-26) and Track D (M1–M5) repairs are faithfully carried into the draft, and the evidence labels are disciplined.

Before the PDF build, fix D1 and D2 (wording) and H1 (stale registry text). The nits A1–D5 can be fixed in the same pass. The pending release items remain:
- typeset with `pdflatex`/`bibtex` and inspect the PDF;
- commit and pin `HigherOrderTower.lean` and the Phase 23 scripts;
- commit the GF-29 and GF-34 registry entries;
- run a targeted literature search.

**Cross-model review is not independent human peer review.** This check was carried out by an AI model (Claude Opus 5.5) and has not been read by a human specialist.
