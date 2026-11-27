# Verification map: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v2.0, candidate draft)

This file maps every numbered statement of version 2.0 to one evidence label: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **Finite certificate** or **External input**. Two further labels qualify statements: **Conditional** (a proved implication whose hypothesis is open) and **Open**. A Lean-supported label means only that the named finite step is a Lean declaration. Every exponential-sum estimate, every measure-theoretic step, every normality conclusion, every rate and every Diophantine statement in this paper is a written proof. Finite computations quoted as illustrations are finite measurements, not evidence for asymptotic statements.

**Cross-model review is not independent human peer review.** The written proofs of this version, and the arguments in the repository notes they come from, have been checked only by AI models from different providers. No human specialist has read them.

Version 1.0 is archived unchanged in [`papers/07-synthetic-expansions/`](../07-synthetic-expansions/), with its own [verification map](../07-synthetic-expansions/VERIFICATION.md). The changes are listed in [CHANGES.md](CHANGES.md) and the literature comparison is in [LEDGER.md](LEDGER.md).

**Split (27 November 2026).** The former §9 (all-prime polynomial normality and irrationality exponents) is now the companion candidate draft [Paper XII](../12-all-prime-normality-exponents/), whose own [verification map](../12-all-prime-normality-exponents/VERIFICATION.md) covers it. The boundary section is now §9, the questions §10, formal verification §11 and the AI disclosure §12. **PDF compilation with `pdflatex` and `bibtex` is pending before release.** Neither tool is installed on the local Windows host or on the Linux build server `hail`, so the current draft has not been typeset. The statement numbers below come from a structural count of `paper.tex`.

## Pinned commits

Lean links in the manuscript use three commits:

- **E** = `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (research checkpoint 18): `RetirementDenominator`, `Phase18Synthetic`, `SharpTranslation`, `SmoothOrbit`, `PositiveSummation`.
- **P** = `c2c9da683666b3b9368e5d4b5cb858caccf528f5` (Phase 19): `SurvivingGrid`, `PrimePowerGrid`.
- **R** = `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8` (Phase 21): `PowerSumPeeling`. After the split, `ProtectedPole` (also at R) is cited only by Paper XII. The line numbers below were read from the files at R on 26 November 2026; each is the declaration line of the named theorem.

Build records at the pinned commits:

- E and P: as in the [v1.0 map](../07-synthetic-expansions/VERIFICATION.md).
- R: as in [`notes/phase21/verification.md`](../../notes/phase21/verification.md). Lean 4.36.0; `lake build` of 8,776 jobs with zero warnings and zero `sorry`; an axiom audit of 1,873 public declarations accepting only `propext`, `Classical.choice` and `Quot.sound`; a `leanchecker` replay of `ProtectedPole` and `PowerSumPeeling`.

This draft did not rerun `lake build` and adds no Lean declaration.

## Exact scope of `PowerSumPeeling.lean` (at R)

| Declaration | Line | What it states | Used in |
| --- | --- | --- | --- |
| `card_pow_diff_eq_le_divisors` | 79 | For $d\ge2$, $M>0$: the pairs $(a,c)$ with $c<a$ and $a^d-c^d=M$ number at most the number of divisors of $M$. | Lemma 7.16 (rows with $B=0$), Theorem 7.20 and Lemma 7.23 (peeling) |
| `phiPoly_natDegree`, `phiPoly_leadingCoeff`, `phiPoly_ne_zero` | 232, 242, 222 | $\Phi_q\in(\mathbb Z[B])[X]$ has $X$-degree $q-2$ and leading coefficient $(-1)^q\prod_{j=1}^{q-2}(d+j)\ne0$. | Lemma 7.14 |
| `dominant_loss_unique_top_coord` | 372 | For equal sums of $d$-th powers of rationals with a unique top loss $h_{\rm top}\ge1$, a unit top numerator and $\sum g_i<2h_{\rm top}$, exactly one $w_i$ has loss $h_{\rm top}$. | Lemma 7.16, Theorem 7.20, Lemma 7.23 (peeling steps) |
| `truncMass_sub`, `truncMass_jump_of_isolated` | 446, 483 | The truncated mass jumps by exactly $r!\,p^{sH}$ across an isolated centre with distinct coordinates. | Lemma 7.12 (one order only; the weighted jump of Lemma 7.23 is written) |

`SurvivingGrid.stride_order` (P L43) and `PrimePowerGrid.crt_period_count` (P L337) are used in Lemma 2.4. The following are **not** in Lean: the derivative identity for $f_B^{(q)}$ (checked exactly by `scripts/phase20_normality.py`), Titchmarsh's test, the Erdős–Turán inequality, the isolation counts, the small-ball recursions, the measure theory, every rate, and everything in §9 beyond the sharp translation identity.

## Statement map

| No. | Statement (short) | Evidence | Lean declarations | External inputs | Reproduction / finite checks |
| --- | --- | --- | --- | --- | --- |
| A | Normality switch on schedules $n_k\ge k^2$ | Kernel-verified (= 4.5) | see 4.5 | — | `lake build` at E |
| B | Rate for $d\ge s+2$; $D_N(\xi)\le200N^{-1/3}$ | Lean-supported paper proof (= 4.7, 3.1) | see 4.2 | — | v1.0 `checks/xi_discrepancy.py` |
| C | Prescribed limits, pairs, limit sets | Lean-supported paper proof (= 5.3, 6.1, 6.4) | see 5.1 | Colebrook, Sigmund (comparison only) | `scripts/phase18_programming.py` at E |
| D | Total degree $r<d$ in distinct orders normal, with rate $(\log\log N)^{-d/(d-1)}$; $N^{-\eta}$ for a single linear maximizer; $\xi^2$ rate $(\log\log N)^{-3/2}$ | Lean-supported paper proof (= 7.1, 7.19, 7.20; rates 7.21, 7.22, 7.24 are paper proofs) | see 7.12, 7.14, 7.16, 7.23 | see 7.13, 7.16 | see 7.16–7.24 |
| E | All-odd-prime normal Liouville sum; finite joint normality; rational totals | Lean-supported paper proof (= 8.2–8.4) | see 2.4, 8.4 | KN Ch. 1 Thms 2.1, 6.2 | `scripts/phase19_grids.py` at P |
| F | Boundary $d=r$: depth tight; barrier; retirement at $d=2$; cubic conditional; (v) irrational squares; (vi) innovation law; (vii) packet barrier | Paper proof, with External inputs (= 9.1–9.18) | (sharp translation via 9.8) | Landau, Hooley, Bambah–Chowla, Selberg–Delange, Wooley, DHL, **DEKKM Thm 1**, Ghidelli | `scripts/phase22_nonlinear_boundary.py`, `scripts/phase23_nonlinear_short_orbits.py` |
| 2.1–2.6 | Arcs; finite comparison; block certificate; grids; prime-power orbits; sharp translation (quoted) | as in the 26 Nov map: 2.1–2.3, 2.5 Paper proof; 2.4 Lean-supported; 2.6 Kernel-verified (proved in manuscript H) | `discrepancy_transfer` (E L583); `stride_order` (P L43); `crt_period_count` (P L337); `sharp_translation` (E L343), `sharp_translation_isGreatest` (E L386) | Manuscript H, Thm 3.1 | `phase19_grids.py`, `phase18_programming.py` |
| 2.7 | Uniform short orbits; sharpness $\lvert S\rvert/M\ge\sin(\pi/10)/(\pi/10)>0.983$ (**Audit 2 repair**) | Paper proof | — | — | `scripts/phase22_short_orbits.py`: LTE (31,840 cases); complete-orbit vanishing (41); stride identity; sharpness example. The complex sums and the sine bound are floating-point checks. |
| 2.8 | Splitting off a coprime modulus; standing bound via $\ord_{M'}b\le M'$ (**weak** inequality, Audit 2) | Paper proof | — | — | same script: CRT factorization on 53 prefixes; identity on all 243 divisors |
| 3.1 | $D_N(\xi;2)\le200N^{-1/3}$ | Paper proof | — | — | v1.0 finite certificate |
| 4.1–4.7, 4.8 (Remark) | as in v1.0; Remark 4.8 points to 7.21 | as in v1.0 | as in v1.0 | as in v1.0 | as in v1.0 |
| 5.1–5.3, 6.1–6.5 | as in v1.0 | as in v1.0 | as in v1.0 | as in v1.0 | `phase18_programming.py` |
| 7.1–7.9 | Quadratic images (model case) | as in v1.0 (Paper proof; 7.9 Remark) | none | GK91; KN | `phase19_nonlinear.py` at P |
| 7.10–7.11 | Freezing in degree $r$; reduction to the mass | Paper proof; Lean-supported paper proof (via 4.3) | as 4.3 | — | `phase21_nonlinear.py` |
| 7.12–7.16 | Jumps; $q$-th derivative test; derivatives of $f_B$; margins; averaged isolation | 7.12, 7.14, 7.16 Lean-supported; 7.13 External input; 7.15 Paper proof | see the table above | Titchmarsh Thm 5.13; Erdős–Turán | `phase20_normality.py`, `phase21_nonlinear.py` |
| 7.17 | Uniform isolation fails ($p=3$, $d=4$, $r=3$, $H\ge6$) | Paper proof; **finite certificate** | — | — | `phase21_nonlinear.py` ($H\in\{6,10,100,1000,4000\}$) |
| 7.18 | Small balls | Lean-supported paper proof (via 7.12, 7.16) | as 7.12, 7.16 | — | — |
| 7.19 | One order, every degree $r<d$ | Lean-supported paper proof | via 7.12, 7.14, 7.16, 4.3 | as 7.16 | — |
| 7.20 | Several orders; freezing threshold $J_1(L)=\max(L,\lceil L/s_1\rceil+\lceil L/d\rceil)$ (**Phase 23 fix**) | Lean-supported paper proof | `dominant_loss_unique_top_coord`, `card_pow_diff_eq_le_divisors` | as 7.16; Lebesgue differentiation | `phase21_nonlinear.py`; `phase23_nonlinear_short_orbits.py`: weight-gap fixture $L=2$, $J=1$, $u=1$; full freezing window |
| 7.21 | Effective rates for every $d\ge r+1$ (one order); run conventions as repaired in Audit 2 | Paper proof | — | Erdős–Turán | `phase22_short_orbits.py` ($\delta$ table) |
| 7.22 | $D_N(\xi^2)\ll(\log\log N)^{-3/2}$; $C(2,3,1,4)^{1,2,3}$ | Paper proof | — | — | — |
| 7.23 | **New.** Weighted averaged isolation for several orders, explicit parameter order | Lean-supported paper proof (peeling and divisor-bound steps only) | `dominant_loss_unique_top_coord` (R L372), `card_pow_diff_eq_le_divisors` (R L79) | Titchmarsh Thm 5.13 and the margins of 7.15 (via 7.16); divisor bound | `phase23_nonlinear_short_orbits.py`: tied-order residues $2,41,15,15,60\bmod81$; 5,042 regular-row bounds (illustrations only) |
| 7.24 | **New.** Rates for several orders: $(\log\log N)^{-d/(d-1)}$; $N^{-\eta}$ for a single linear maximizer | Paper proof | — | Erdős–Turán | — |
| 8.1–8.5 | Infinite sums | as in v1.0 | as in v1.0 | as in v1.0 | `phase19_grids.py` at P |
| 9.1–9.10 | Former 10.1–10.10 (depth tight; barrier; no uniform cancellation; level filtration; sparse integer series; absorption; integer dilation; fixed-depth retirement; runs; fractional jumps) | unchanged from the 26 Nov map: Paper proofs, with External inputs Landau (9.6, 9.9), Hooley and Bambah–Chowla (9.9), Selberg–Delange (9.10); 9.8 Lean-supported (step 2.6) | as 2.6 for 9.8 | as listed | `phase21_nonlinear.py`, `phase22_nonlinear_boundary.py` |
| 9.11 | **New.** Long gaps between sums of two squares, $\limsup(\sigma_{n+1}-\sigma_n)/\log\sigma_n\ge390/449$ | **External input** | — | Dietmann–Elsholtz–Kalmynin–Konyagin–Maynard, **Theorem 1** (accepted manuscript; typeset numbering to be confirmed) | — |
| 9.12 | **New.** $C(b,p,s,2)^2$ irrational for $s<(390/449)t\log b$, including every $s=1$ | Paper proof using an **External input** (9.11) | — | 9.11 | — |
| 9.13 | **New.** Innovation law, both residue classes of $p$ modulo 4 | Paper proof using an **External input** | — | Selberg–Delange (Tenenbaum II.5); Landau | `phase23_nonlinear_short_orbits.py`: innovation counts for $n\le400$, $H=1$ (finite measurement, far from the limit law, **not** evidence for it); independent recount of ordered representations including retired levels |
| 9.14 | **New.** Aggregate denominator law | Paper proof | — | Landau; 7.18 | same script: 643 / 479 / 164 arrivals; 1,871 / 1,200 / 427 packets with surviving pole, exact recurrence and denominators (finite measurement) |
| 9.15 | **New.** Packet lemma | Paper proof | — | — | same script: $q=81$, $b=2$ realizes all 32 words of length 5 (**finite certificate** of the example) |
| 9.16 | **New.** Eligible packets at density one, $d=r\ge2$ | Paper proof | — | — | — |
| 9.17 | **New.** The cube modulo 9 | Paper proof | — | — | same script (cubic residues) |
| 9.18 | **New.** Conditional cubic irrationality criterion (threshold $2/(3\log2)$) | Paper proof; **Conditional** (the hypothesis is open) | — | Ghidelli Thm 1.1 (shown insufficient) | — |
| 9.19 (Remark) | Finite measurements | Finite measurement (not a claim) | — | — | `phase22_nonlinear_boundary.py`, `phase23_nonlinear_short_orbits.py` |
| §9.6 text | Cubic boundary: absorption conditional on density zero of sums of three cubes | Conditional; no claim | — | Wooley (2015); DHL (2006) | `phase22_nonlinear_boundary.py` |
| 10.1–10.4 | Questions | **Open** | — | — | — |

**Moved to Paper XII:** former Theorem F and statements 2.9 and 9.1–9.12 of the 26 November draft. See the [Paper XII map](../12-all-prime-normality-exponents/VERIFICATION.md) and the correspondence in [CHANGES.md](CHANGES.md).

**Registry correspondence.**

- Theorems A–C, E and Sections 2–8 carry the v1.0 identifiers [SY-01](../../docs/results.md#sy-01), [SY-02](../../docs/results.md#sy-02), [SY-03](../../docs/results.md#sy-03), SY-06, SY-07, SY-11, SY-13, SY-16, SY-19, [OP-08](../../docs/results.md#op-08), [OP-09](../../docs/results.md#op-09) and [OP-14](../../docs/results.md#op-14).
- [GF-11](../../docs/results.md#gf-11) is Theorem 7.19. [GF-14](../../docs/results.md#gf-14) covers Proposition 7.17, Lemma 7.16, Theorems 7.18 and 7.20, Proposition 9.1 and Lemma 9.2. [GF-25](../../docs/results.md#gf-25) covers Lemma 2.7, Corollary 2.8 and Theorem 7.21. [GF-24](../../docs/results.md#gf-24) covers 9.3–9.10.
- The Phase 23 material (Lemma 7.23, Theorem 7.24, Theorems 9.11–9.13, Propositions 9.14, 9.16–9.18, Lemma 9.15) comes from [`notes/phase23/nonlinear-multivariate-and-denser-mu.md`](../../notes/phase23/nonlinear-multivariate-and-denser-mu.md), which has **no registry entry yet**.

**Untracked or uncommitted files.**

- `NormalityChecker/Phase22Cores.lean` is now tracked (commit `8ca4309`). The manuscript still does not link it, so Lemma 9.7 and Proposition 9.4 keep the label *Paper proof*.
- `scripts/phase23_nonlinear_short_orbits.py` is untracked.
- `scripts/phase22_short_orbits.py` has its Audit 2 repair (`even_support_orders()`) as an uncommitted working-tree change; that check concerns Paper XII.
- Both scripts must be committed before release.

## Sources and model reviews

| Material | Source note | Model review (not human peer review) |
| --- | --- | --- |
| 7.10–7.19 | Phase 20 `cubic-power-schedule.md`, Phase 21 `nonlinear-boundary.md` §§1–4 | Phase 20 and Phase 21 Track C reviews (repaired; post-repair ACCEPT) |
| 7.20 | Phase 21 `multivariate-and-dense-allprime.md` §§1–3; freezing fix from Phase 23 Track C3 | Phase 21 Track C; [Phase 23 Track C](../../notes/phase23/reviews/track-c-review.md) (m6 erratum, closed) |
| 2.7–2.8, 7.21 | [`short-orbits-and-irrationality.md`](../../notes/phase22/short-orbits-and-irrationality.md) | [Phase 22 Track C3–C4](../../notes/phase22/reviews/track-c34-review.md); [Phase 23 Audit 2](../../notes/phase23/reviews/phase22-analytic-audit-shortorbits-reciprocals.md), **SOUND / ACCEPT** after repair (sharpness constant, weak inequality, run conventions) |
| 7.23–7.24 | [`nonlinear-multivariate-and-denser-mu.md`](../../notes/phase23/nonlinear-multivariate-and-denser-mu.md) §§3–4 | Phase 23 Track C: C3 **ACCEPT**. The review's m7 asked for a standalone multivariate Lemma I with explicit parameters, which Lemma 7.23 supplies. The Titchmarsh 5.13 row exponents are imported from Lemmas 7.15–7.16 and were not re-derived by that review. |
| 9.1–9.10 | Phase 21 `nonlinear-boundary.md` §7; Phase 22 `nonlinear-equality-boundary.md` | Phase 21 Track C; [Phase 22 Track C1–C2](../../notes/phase22/reviews/track-c12-review.md) |
| 9.11–9.18 | [`nonlinear-multivariate-and-denser-mu.md`](../../notes/phase23/nonlinear-multivariate-and-denser-mu.md) §§1–2 | Phase 23 Track C: C1 and C2 **ACCEPT** after repair. Major M1 (wrong DEKKM theorem number) is closed: the manuscript cites **Theorem 1**. |

Changes made in writing the manuscript, relative to the sources:

1. Lemma 7.23 packages the weighted isolation estimate of Track C3 as a standalone lemma, with the parameter order in its statement. Its free-loss boxes use the concrete scale $\beta_j=\lambda H(24s_m)^{j-1}$ in place of the note's unspecified boxes.
2. Proposition 9.16 is stated for every $d=r\ge2$; the note uses $d\in\{2,3\}$, and its counting argument is general.
3. Proposition 9.17(iv) is stated for every $s\ge1$; the note states $s=1$, and the same argument gives $9\mid3^{1+s(3a-\ell)}$.
4. The conditional packet-discrepancy statement of the note appears as a sentence, not as a numbered result.

No statement was strengthened in its hypotheses or conclusions beyond what the source proves.

## Exact checks run for this draft (27 November 2026)

From the repository root, native Windows Python 3.13 with bytecode disabled:

| Command | Exit | Notes |
| --- | --- | --- |
| `python -B scripts/phase23_nonlinear_short_orbits.py` | 0 | about 1 s; "All exact checks passed."; every number quoted in Remark 9.19 and above matches the output |
| `python -B scripts/phase22_short_orbits.py` | 0 | "All Phase 22 C3-C4 checks passed." |

The checks of 26 November 2026 (`phase20_normality.py`, `phase21_nonlinear.py`, `phase22_nonlinear_boundary.py`, all exit 0) were not rerun. The supplementary check for Proposition 7.17 ($4\le H\le12$) stands as recorded in the previous version of this file.

## Manuscript checks run for this draft

- **Structural check** (scratch Python script, 27 November 2026) of `paper.tex` against `references.bib`. **PASS.**
  - `\begin`/`\end` environments match; braces are balanced in both files; inline `$` is balanced in every paragraph.
  - All 107 labels are distinct. Every one of the 96 distinct `\ref`/`\cref`/`\Cref`/`\eqref` targets is defined.
  - Every one of the 36 `\cite` keys is in `references.bib`. All 36 entries are cited, and there are no duplicate keys.
  - **Zero** occurrences remain of the 18 labels removed with the split: `sec:allprime`, `eq:gridcount`, `lem:poledom`, `thm:allprime`, `thm:protected`, `lem:Ax`, `cor:dense`, `rem:algebras`, `thm:hybrid`, `lem:truncation`, `eq:separation`, `prop:ratioone`, `thm:geometric`, `thm:stoneham`, `rem:quasipoly`, `thm:F`, `thm:G`, `lem:largestprime`.
  - Every control sequence used is standard LaTeX/AMS or is defined in `../common/preamble.tex` or the paper preamble.
- **Pending before release:**
  - three `pdflatex` passes and `bibtex`, with inspection of numbering, overfull boxes and the new statements;
  - `python3 scripts/portal.py check` after any registry update;
  - committing the two scripts.

  The 26 November scratch build (48 pages, TinyTeX) predates the split and the Phase 23 additions, and does not describe this draft.
