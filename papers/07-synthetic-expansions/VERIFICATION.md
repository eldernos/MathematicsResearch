# Verification map: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v1.0)

Lean links use one of two commits:

- Checkpoint-18 modules are pinned to `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (research-checkpoint-18). Base: `E = https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker`.
- Phase 19 modules (SurvivingGrid, PrimePowerGrid) are pinned to `c2c9da683666b3b9368e5d4b5cb858caccf528f5`. Base: `P = https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker`.

All 22 Lean URLs embedded in the built `paper.pdf` were extracted with `pdfinfo -url` and checked with `git show <commit>:<path>` on 25 November 2026, after the revision in response to the two referee reports (`papers/reviews/07-synthetic-expansions/`): each anchored line is the declaration line of the named theorem or definition (22 of 22). The four script links (two at each commit) resolve to existing files.

The numbering is that of the built `paper.pdf` (24 pages). The revision added Remark 6.5 and no other numbered statement, so all earlier numbers are unchanged. Theorems A–E in the introduction restate theorems from later sections, as listed in the last column.

**Split of 25 November 2026.** The sharp translation identity, the preserver classification, the discrepancy pseudometric, the addition spectrum and the sparse-translation theorems moved to manuscript H (`papers/10-discrepancy-arithmetic`). This paper quotes only the identity, once, as Theorem 2.6. The quadratic-image theorems of Section 7 are new in this version of the manuscript. See `ARRANGEMENT.md`.

| No. | Statement (short) | Evidence | Lean declarations | External inputs | Reproduction |
| --- | --- | --- | --- | --- | --- |
| A | Normality switch: $D_N(X_0)\to1$ and $D_N(X_s)\to0$ for $s\ge1$ | Kernel-verified (= Thm 4.5) | see 4.5 | — | `lake build` (see Reproduce) |
| B | Rate for $d\ge s+2$, and $D_N(\xi)\le200N^{-1/3}$ | Lean-supported paper proof (= Thm 4.7 and Thm 3.1) | see 4.2 | — | `python -B scripts/phase18_principal.py` (finite enclosures) |
| C | Every $\delta$ at rate $N^{-1/3}$ with denominators dividing $q_k\le pk$; all pairs; all limit sets with state period $\le k$ (qualitative existence is classical, Remark 6.5) | Lean-supported paper proof (= Thms 5.3, 6.1, 6.4) | see 5.1 | Colebrook, Sigmund (only for the qualitative comparison in Remark 6.5) | `python -B scripts/phase18_programming.py` |
| D | Quadratic images: total degree $\le2$ in $X_a$ normal; $\xi^2$ normal; $(\xi,\xi^2)$ jointly normal | Paper proof (= Thm 7.1, Cor 7.2) | none (not formalized); uses 4.3 through 4.4 | GK91 Lemma 2.5, Thm 2.2; KN Ch. 2 Thm 2.5 | `python3 -B scripts/phase19_nonlinear.py` at `c2c9da6` |
| E | All-odd-prime normal Liouville sum, finite joint normality, rational totals | Lean-supported paper proof (= Thms 8.2–8.4) | see 8.2, 8.4 | KN Ch. 1 Thms 2.1, 6.2 | `python3 -B scripts/phase19_grids.py` at `c2c9da6` |
| 2.1 | Half-open arcs; $D$ = sup of positive excess; rotation invariance | Paper proof | — | — | — |
| 2.2 | Finite comparison $\lvert D(u)-D(v)\rvert\le E/N+2\epsilon$ | Paper proof (orbit case kernel-verified as `discrepancy_transfer`) | [E/Phase18Synthetic.lean#L583](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L583) | — | — |
| 2.3 | Block certificate | Paper proof | — | — | — |
| 2.4 | Grids for $q=p^eQ$, numerator prime to $p$; count error $Lp^{c-e}+\tau p^{e-c}$ along one chosen admissible stride $\tau$ (the count needed for Thm 8.2; the exact period and the maximal grid of the Phase 19 note are not stated) | Lean-supported paper proof: order and one-stretch count are Lean (`crt_period_count` assumes only $p\nmid a'$) | [`stride_order` P/SurvivingGrid.lean#L43](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/SurvivingGrid.lean#L43), [`crt_period_count` P/PrimePowerGrid.lean#L337](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean#L337) | — | `phase19_grids.py` (240 full-orbit cases) |
| 2.5 | Prime-power orbits: error $\le p^vL/p^e+p^e$ | Paper proof (full-period case is `primePower_period_count`, [P/PrimePowerGrid.lean#L313](https://github.com/eldernos/MathematicsResearch/blob/c2c9da683666b3b9368e5d4b5cb858caccf528f5/NormalityChecker/PrimePowerGrid.lean#L313), not linked in the paper) | — | — | `phase18_programming.py` (B2: 66 orbits) |
| 2.6 | Sharp translation identity, **quoted** from manuscript H (Theorem 3.1 there) | Kernel-verified (proved in manuscript H; not reproved here) | [`sharp_translation` E/SharpTranslation.lean#L343](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L343), [`sharp_translation_isGreatest` L386](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SharpTranslation.lean#L386) | Manuscript H, *The Arithmetic of Extreme Discrepancy*, Thm 3.1 | `lake build` |
| 3.1 | $D_N(\xi;2)\le200N^{-1/3}$; $D_N(\sum2^{-2k^3})\to1$ | Paper proof | (Step 1 is an instance of Thm 4.2) | — | `phase18_principal.py` prints $D_{1024}\in[0.593424,0.593425]$; the enclosures of $N^{1/3}D_N(\xi)$ quoted after the theorem are a finite certificate, `python -B papers/07-synthetic-expansions/checks/xi_discrepancy.py` (see the last section) |
| 4.1 | Geometric grouping; absolute convergence for bounded real multipliers; if every $M$ divides some gap, every prime $\nmid b$ divides some gap repunit $\rho_{n_k-n_{k-1}}$, and infinitely many primes do | Kernel-verified (exactly the stated repunit divisibility). The passage after the proof to reduced raw coefficients, for multipliers $1/m_k$, is a written step outside the labelled statement; for general multipliers it fails | [`geometric_retirement_weight` L76](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L76), [`grouped_retirement_hasSum` L146](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L146), [`raw_prime_support_infinite` L290](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L290) | — | `lake build` |
| 4.2 | Exact reduced denominator $p^{s\lfloor\log_pK\rfloor}$ | Kernel-verified | [`shiftedPrefix_den` L110](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L110), [`fullPrefix_den` L157](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L157), [`maximalLayer_card` L67](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L67) | — | `phase18_principal.py` (12,987 prefix shifts) |
| 4.3 | Fixed-support short-orbit estimate | Kernel-verified | [`fixed_support_orbit_estimate` L207](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean#L207), [`SmoothOrbitEstimate` L16](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/SmoothOrbit.lean#L16) | Related, not used: Vandehey, arXiv:1606.07911, Cor. 1.2 | `lake build` |
| 4.4 | All-prefix criterion (sparse insertions, fixed-support polynomially bounded denominators, small denominators of density zero ⇒ normal) | Lean-supported paper proof (step: Lemma 4.3) | as 4.3 | KN Ch. 1 Thm 2.1 (p. 7), Thm 8.1 (p. 70) | — |
| 4.5 | Normality switch on schedules $n_k\ge k^2$, $t\mid n_k$ | Kernel-verified | [`discrepancy_switch` L436](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L436), [`normal_iff_pos` L444](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L444), [`polynomial_discrepancy_switch` L456](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/RetirementDenominator.lean#L456) | Weyl's criterion is used only in the written outline (via 4.4) | `lake build` |
| 4.6 | $\sum p^{-sv_p(k)}b^{-t(k+1)!}$ is normal and Liouville | Lean-supported paper proof (normality is Thm 4.5; the hypotheses $n_k\ge k^2$ and $t\mid n_k$ for this schedule are not formalized; Liouville part is written) | as 4.5 | Liouville's theorem (classical) | — |
| 4.7 | Complete-period rate for $d\ge s+2$ | Lean-supported paper proof (denominator step = Thm 4.2) | as 4.2 | — | `phase18_principal.py` |
| 5.1 | Positive state programming; $p$-power coefficients | Kernel-verified | [`programState_fract` L383](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L383), [`programState_eq_prefix` L438](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L438), [`programmed_prefix_fract` L459](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L459), [`programCoeff_mem` L364](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L364), [`programCoeffs_prime_power` L426](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/Phase18Synthetic.lean#L426) | — | `phase18_programming.py` (12,288 transitions) |
| 5.2 | Modelled discrepancy $\lvert D_N-Z/N\rvert\le(H+(K+1)W)/N+\ldots$ | Paper proof | — | — | `phase18_programming.py` (G1, 291 windows) |
| 5.3 | Every $\delta\in[0,1]$ at rate $C_{b,p}N^{-1/3}$, uniform in $\delta$; $\mathrm{den}(c_k)\mid q_k\le pk$; weak limit; irrationality | Lean-supported paper proof (Lemma 5.1) | as 5.1 | — | `phase18_programming.py` ($b=2,p=3,\delta=2/5$, $N=400$: $D_N\in[0.549027,0.549028]$) |
| 6.1 | Every pair $(\alpha,\beta)$ of lower and upper limits, with $\mathrm{den}(c_k)\mid q_k\le pk$ and $D_N=\Lambda_N/N+O(N^{-1/3})$ | Lean-supported paper proof (Lemma 5.1) | as 5.1 | — | — |
| 6.2 | Limit sets are nonempty, compact, connected and invariant | Paper proof | — | — | — |
| 6.3 | Weak continuity of $D$ | Paper proof | — | — | — |
| 6.4 | Exactly the nonempty compact connected sets of invariant measures; realized on $tk^3$ for every $t\ge1$ with state period $\le k$ | Lean-supported paper proof (Lemma 5.1) | as 5.1 | Riesz representation (standard). Parthasarathy (1961) is a precedent for periodic density; it is not used as a black box | — |
| 6.5 (Remark) | Every radix orbit is, after $m$ shifts, the orbit of $\sum c_kb^{-n_k}$ with $c_k\in(0,1)$ of $p$-power denominator on any schedule; hence the existence statements of 5.3, 6.1, 6.4 follow from classical realization | Remark with a written proof of the encoding; the realization is an external input | — | Colebrook (1970); Sigmund (1974), Thm 4, pp. 293–295; DGS (1976); Lemma 6.3 | — |
| 7.1 | Quadratic images in distinct orders $X_a=C(b,p,a,d)$, $d\ge3$: normality, joint normality of monomials, degree $\ge3$ if algebraic | Paper proof | none | Prop 4.4 (Lean-supported), Thm 4.2 (Lean); GK91 Lemma 2.5 and Thm 2.2 (via 7.6); KN Ch. 2 Thm 2.5 (Erdős–Turán, p. 112); KN Ch. 1 Thm 6.2 (p. 49); Lebesgue density theorem | `phase19_nonlinear.py`; `python -B notes/phase19/reviews/nonlinear-check.py` |
| 7.2 | $\xi^2$ normal; $(\xi,\xi^2)$ jointly normal | Paper proof (special case of 7.1) | none | as 7.1 | as 7.1 |
| 7.3 (Remark) | Historical finite bound $\limsup D_N(\xi^2)<2.94\cdot10^{-10}$, superseded | Remark (finite certificate, not a claim) | — | — | `python -B scripts/phase18_principal.py --square-layers 21` at `e4809cf` |
| 7.4 | Freezing: normalized prefixes agree with $M_{a,c}(u)$, $M^{\rm lin}_D(u)$ modulo $p^L$ for $J\ge L(1+1/d)$ | Paper proof | — | lifting of exponents (§2) | `nonlinear-check.py` (230,784 cutoffs in shells $J=4,5$) |
| 7.5 | Primitive jumps at $c/p^H$ of valuation $a_*H+g$; classification of jumps modulo $p^{P_H}$ | Paper proof | — | — | `phase19_nonlinear.py` (isolated jumps, tied weights) |
| 7.6 | Third-derivative estimate $\ll M\lambda^{1/6}+M^{1/2}\lambda^{-1/6}$ | Paper proof | — | GK91 Lemma 2.5 and (2.3.2) (Weyl–van der Corput inequality, p. 10), Thm 2.2 (second-derivative test, p. 8) | — |
| 7.7 | Positive proportion of isolated primitive centres | Paper proof | — | KN Ch. 2 Thm 2.5 (Erdős–Turán) | `nonlinear-check.py` (collision main term within 1%; isolated fraction 0.80–0.86) |
| 7.8 | Level sets of the limiting mass are Lebesgue-null | Paper proof | — | Lebesgue density theorem; Cauchy–Schwarz | `nonlinear-check.py` ($\lvert E_L\rvert$ table) |
| 7.9 (Remark) | Scope: no rate; cubes open | Remark | — | — | — |
| 8.1 | Exact denominators of prefixes of $\sum r_\ell Y_\ell$ | Paper proof | — | — | `phase19_grids.py` (325 insertion denominators) |
| 8.2 | $Y$ is normal and Liouville; $D_N(Y)\ll1/\log(2N)$ | Lean-supported paper proof (Lemma 2.4 steps) | as 2.4 | — | `phase19_grids.py` certifies $D_N(Y)<1/8$ at prefixes near $16^{11}$ |
| 8.3 | Finite rational combinations of the $Y_\ell$; joint normality | Lean-supported paper proof (Lemma 2.4 steps) | as 2.4 | KN Ch. 1 Thm 2.1 (p. 7) and Thm 6.2 (p. 49) | — |
| 8.4 | Positive rationals with $\sum c_\ell Y_\ell=R$ | Lean-supported paper proof (existence of multipliers is kernel-verified) | [`hasSum_positive_rational_multiples` L15](https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker/PositiveSummation.lean#L15) | — | — |
| 8.5 | Consecutive tails: $\overline M(E_k)+\overline M(E_{k+1})\ge1/4$ and $\limsup(D_N(E_k)+D_N(E_{k+1}))\le1$ | Lean-supported paper proof (step: Thm 2.6) | as 2.6 | KN Ch. 1 Cor. 1.1 (p. 3); manuscript H Thm 3.3 (only for the closing sentence) | — |

KN = L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Wiley, 1974. Chapter 1, Corollary 1.1 (p. 3), Theorem 2.1 (p. 7), Theorem 6.2 (p. 49), Theorem 8.1 (p. 70) and Chapter 2, Theorem 1.1 (p. 89) were checked against a text copy. Chapter 2, Theorem 2.5 (Erdős–Turán, p. 112) is the standard citation and was not re-checked against the text in this worktree. GK91 = S. W. Graham and G. Kolesnik, *Van der Corput's Method of Exponential Sums*, LMS Lecture Note Series 126, Cambridge University Press, 1991. Theorem 2.2 (second-derivative test: $\lambda\le|f''|\le\alpha\lambda$ on $I$ gives $\sum_{n\in I}e(f(n))\ll\alpha|I|\lambda^{1/2}+\lambda^{-1/2}$, p. 8) and Lemma 2.5 with its consequence (2.3.2) (Weyl–van der Corput inequality, p. 10) were read in the publisher's open-access Chapter 2 excerpt, <https://assets.cambridge.org/97805213/39278/excerpt/9780521339278_excerpt.pdf>, on 25 November 2026.

## What is completely kernel-verified

The complete statements of Proposition 4.1, Theorem 4.2, Lemma 4.3, Theorem 4.5 (= Theorem A) and Lemma 5.1 are Lean declarations, and Theorem 2.6 is a kernel-verified declaration quoted from manuscript H. They use the paper's definitions of extreme discrepancy (`radixDiscrepancy`: supremum over $0\le a<c\le1$ of $\lvert\text{frequency in }[a,c)-(c-a)\rvert$) and normality (`NormalIn`: block frequencies with the terminating convention).

These were checked in Lean 4.36.0 with the pinned Mathlib manifest:

- At `e4809cf`: 8,746 Lake jobs. The axiom audit of 1,593 public declarations accepted only `propext`, `Classical.choice` and `Quot.sound`, and an independent kernel replay covered all 248 module files (`notes/phase18/verification.md`).
- At `c2c9da6`: 8,754 jobs. The axiom audit covered 1,719 declarations with the same three axioms, and the replay covered all 252 modules (`notes/phase19/verification.md`).

This manuscript worktree did not rerun `lake build`, following the wave-2 contract. The statements were matched against the source text at the pinned commits.

Not kernel-verified:

- every rate (Theorems 3.1, 4.7, 5.3, 8.2);
- the passage from repunit divisibility to reduced raw coefficients after Proposition 4.1;
- the encoding in Remark 6.5;
- the all-prefix criterion beyond the short-orbit estimate (4.4);
- the limit-set theorems (6.1, 6.4);
- **all of Section 7**, including Theorem 7.1 and Corollary 7.2 (paper proofs);
- Section 8 beyond the cited grid steps and the multiplier existence.

## Audit of the quadratic-image proof (Section 7)

The proof follows `notes/phase19/nonlinear.md` (§1 and "Quadratic forms in distinct orders") and its independent audit `notes/phase19/reviews/nonlinear.md` at `c2c9da6`. For this manuscript every step was rechecked and written out in full; the points rechecked and the changes made are:

1. **Localized endpoint counting (Lemma 7.7).** The removal costs ($O(H^2p^{4H/5})$ small rows, $O(\eta Hp^H)$ near-degenerate rows, $O(\eta p^v+1)$ per row near $z=0$ and near the zero of the cubic factor) and the row sums were rederived. The polynomial $\Pi$ in $f_y''''$ was computed: its leading coefficient is $(d+1)(d+2)$, so it is nonzero and the monotonicity intervals are $O_d(1)$. The lattice count of the slab and the factor $2$ for both orders are written explicitly. All error terms are uniform in $I\subseteq\mathcal K$, as audit objection O1 requested; only $H_0(I)$ depends on $I$.
2. **Van der Corput estimate (Lemma 7.6).** Rather than citing a third-derivative theorem by number, the paper derives the bound from the Weyl–van der Corput inequality and the second-derivative test, including the trivial cases $\lambda\ge1$ and short pieces $M\le\lambda^{-1/3}$ (audit objection O3). In the application $lp^H\Lambda\ge1$ for large $H$ because $\Lambda\ge H^{-O(1)}$.
3. **Second moment (Proposition 7.8).** The bounds $\lvert I\cap G_n\cap G_m\rvert\le12\lvert I\rvert(\epsilon^2/(nm)+\epsilon p^{n-m}/m)$ and $\lvert I\cap G_H\rvert\ge c_0\epsilon\lvert I\rvert/H$ were rederived; the constant $c_0^2/12$ is independent of $I$ and $L$ because the union decreases in $L$ (audit objection O2).
4. **Null level sets.** The flank argument and measurability were rechecked; the passage $x\mapsto u=1+x^d$ preserves null sets.
5. **Transfer.** The freezing threshold $J\ge L(1+1/d)$ was rederived from $v_p(b^{tm}-1)=v_0+v_p(m)$; the failed-cell count gives upper density at most $p^d\lvert E_L\rvert/(p^d-1)$.
6. **Distinct orders.** The precision $P_H=a_*H+g+1$ and the three jump types were rederived; linear endpoints are only $x=(z^d-1)^{1/d}$ with $z>1$ (audit objection O4). The case where the only top-weight term is linear is handled by the exact denominator (Theorem 4.2).

**No gap was found.** One simplification was made: the transfer in Case 2 needs only precision $L$ (the earlier draft carried an unnecessary shift by $v_p(A)$). The claim is stated exactly as in the source: total degree at most two, $p$ odd, $p\nmid b$, $d\ge3$, distinct orders on the common schedule $ti^d$. The rapidly varying schedules, separated pole growth and distinct-prime algebras of the same note are **not** included (see `COMPANION-ASSESSMENT.md`).

## External analytic dependencies

- **Kuipers–Niederreiter (1974):** Weyl's criterion (Ch. 1 Thm 2.1, p. 7), multidimensional Weyl (Ch. 1 Thm 6.2, p. 49), Riemann-integrable test functions (Ch. 1 Cor. 1.1, p. 3), normality ⇔ uniform distribution (Ch. 1 Thm 8.1, p. 70), uniform distribution ⇔ $D_N\to0$ (Ch. 2 Thm 1.1, p. 89), Erdős–Turán inequality (Ch. 2 Thm 2.5, p. 112).
- **Graham–Kolesnik (1991):** Weyl–van der Corput inequality (Lemma 2.5 and (2.3.2), p. 10) and second-derivative test (Theorem 2.2, p. 8), in Lemma 7.6.
- **Lebesgue density theorem; Riesz representation and diagonal compactness** of $\mathcal P(\mathbb T)$. Standard.
- **Liouville's theorem** (Liouville numbers are transcendental). Classical.
- **Manuscript H** (`papers/10-discrepancy-arithmetic`, same release): the sharp translation identity (Theorem 2.6, kernel-verified), used only in Proposition 8.5, and its Theorem 3.3, mentioned after Proposition 8.5.
- **Not used as inputs:** Vandehey's Corollary 1.2, cited as the quantitative source of the qualitative Lemma 4.3 (itself kernel-verified).

## Reproduce

From the repository root:

```sh
# Lean (long; uses the pinned toolchain). Checkpoint 18:
git checkout e4809cf561573aef588e6ffc491a35cdb79fd9ec && bash scripts/verify.sh
# Phase 19 modules:
git checkout c2c9da683666b3b9368e5d4b5cb858caccf528f5 && bash scripts/verify.sh
# Exact finite checks (standard library only)
python -B scripts/phase18_principal.py          # at e4809cf
python -B scripts/phase18_programming.py        # at e4809cf
python3 -B scripts/phase19_grids.py             # at c2c9da6
python3 -B scripts/phase19_nonlinear.py         # at c2c9da6
python -B notes/phase19/reviews/nonlinear-check.py   # at c2c9da6
python -B papers/07-synthetic-expansions/checks/xi_discrepancy.py   # revision branch; about 2 s
# Manuscript
wsl -d Ubuntu -- bash papers/wsl-build.sh 07-synthetic-expansions
```

After the referee revision of 25 November 2026 the manuscript build passed with no undefined references or citations (24 pages; PDF Author metadata `Christopher Anderson`), and `checks/xi_discrepancy.py` produced the table below. Before the revision the build gave 22 pages, and `phase19_grids.py`, `phase19_nonlinear.py` and `nonlinear-check.py` were rerun in this worktree and exited with status 0 (`nonlinear-check.py` reported agreement at 22,998 and 207,786 breakpoints in shells $J=4,5$). The two Phase 18 scripts passed on the same day in the earlier preparation of this manuscript and were not rerun after the split.

## Finite certificate: enclosures of $N^{1/3}D_N(\xi)$ (added in revision)

`checks/xi_discrepancy.py` (standard library only) computes the binary expansion of $\xi$ exactly to $2^{18}+192$ bits, encloses each orbit point $\{2^n\xi\}$ by its 64-bit window to within $2^{-63}$, computes the extreme discrepancy of the windows exactly from the sorted values ($D_N=\max_i(i/N-x_{(i)})+\max_i(x_{(i)}-(i-1)/N)$), and transfers it to the real orbit by Lemma 2.2 with error at most $2^{-62}$. Output on 25 November 2026 (rounded):

| $N$ | $2^{10}$ | $2^{11}$ | $2^{12}$ | $2^{13}$ | $2^{14}$ | $2^{15}$ | $2^{16}$ | $2^{17}$ | $2^{18}$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $D_N$ | 0.593424 | 0.435221 | 0.217339 | 0.214288 | 0.217523 | 0.219476 | 0.131982 | 0.073586 | 0.073785 |
| $N^{1/3}D_N$ | 5.9813 | 5.5270 | 3.4774 | 4.3198 | 5.5247 | 7.0232 | 5.3212 | 3.7379 | 4.7223 |

The value at $N=2^{10}$ agrees with the enclosure printed by `phase18_principal.py`, and the value at $N=2^{15}$ agrees with the independent estimate in referee report 1 (finding 3). The v1.0 sentence "between 3 and 6" was false (the value exceeds 7 at $N=2^{15}$) and has been replaced. The constant 200 of Theorem 3.1 is unaffected.
