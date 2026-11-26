# Verification map: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v2.0, candidate draft)

This file maps every numbered statement of version 2.0 to one evidence label: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **Finite certificate** or **External input**. A Lean-supported label means only that the named finite step is a Lean declaration; every exponential-sum estimate, every measure-theoretic step, every normality conclusion, every rate and every Diophantine statement in this paper is a written proof. Finite computations quoted as illustrations are measurements, not evidence for asymptotic statements.

**Cross-model review is not independent human peer review.** The written proofs of this version, and the arguments in the repository notes they come from, have been checked only by AI models from different providers. No human specialist has read them.

Version 1.0 is archived unchanged in [`papers/07-synthetic-expansions/`](../07-synthetic-expansions/), with its own [verification map](../07-synthetic-expansions/VERIFICATION.md). The changes are listed in [CHANGES.md](CHANGES.md) and the literature comparison in [LEDGER.md](LEDGER.md).

## Pinned commits

Lean links in the manuscript use three commits:

- **E** = `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (research checkpoint 18): `RetirementDenominator`, `Phase18Synthetic`, `SharpTranslation`, `SmoothOrbit`, `PositiveSummation`. Base `https://github.com/eldernos/MathematicsResearch/blob/e4809cf561573aef588e6ffc491a35cdb79fd9ec/NormalityChecker`.
- **P** = `c2c9da683666b3b9368e5d4b5cb858caccf528f5` (Phase 19): `SurvivingGrid`, `PrimePowerGrid`.
- **R** = `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8` (Phase 21 commit, the tip of this branch when the draft was written): `ProtectedPole`, `PowerSumPeeling`. Neither file is modified in the working tree. The line numbers below were read from the files at this commit on 26 November 2026; each is the declaration line of the named theorem.

Build records at the pinned commits: E and P as in the [v1.0 map](../07-synthetic-expansions/VERIFICATION.md); R as in [`notes/phase21/verification.md`](../../notes/phase21/verification.md) (Lean 4.36.0, `lake build` 8,776 jobs with zero warnings and zero `sorry`, axiom audit of 1,873 public declarations accepting only `propext`, `Classical.choice`, `Quot.sound`, and `leanchecker` replay of `ProtectedPole` and `PowerSumPeeling`). This draft did not rerun `lake build`.

## Exact scope of the two new Lean modules

### `ProtectedPole.lean` (at R)

| Declaration | Line | What it states | What it does **not** state |
| --- | --- | --- | --- |
| `shifted_prefix_protected_prime_pow_dvd_den` | 245 | For the prefix $U_k=\sum_{j\le k}1/(p^{e_j}\ell_jb^{n_j})$, if $p$ is prime, $p\nmid b$, $p\nmid\ell_j$, $e_j<e_k$ for $j<k$ and $n_j\le N$: $p^{e_k}$ divides the reduced denominator of $b^NU_k$ and $p^{e_k+1}$ does not. | Nothing about polynomials in $W$; $p$ need not be odd. |
| `shifted_prefix_aux_prime_dvd_den` | 143 | If $\ell_k$ is prime, $\ell_k\nmid b$, $\ell_k\nmid p$, $\ell_k\nmid\ell_j$ for $j<k$ and $n_j\le N$: $\ell_k$ divides the reduced denominator of $b^NU_k$. | **Only the newest prime** $\ell_k$ at its own truncation. Persistence of earlier $\ell_i$ in later prefixes and the exact formula $p^{k^2}\ell_1\cdots\ell_k$ (Theorem 9.2(i)) are written. |
| `truncated_poly_pole_dvd_den` | 347 | For $U=u/(p^{e_1}Q_1)$, $V=v/(p^{e_2}Q_2)$ with $p\nmid uvQ_1Q_2$, an integer polynomial with $a_r\ne0$, $1\le l\le r$ and $g=v_p(\lvert a_r\rvert\binom rl)<\min(e_1,e_2-e_1)$: $p^{le_2+(r-l)e_1-g}$ divides the denominator of the truncated expansion $F_l(U,V)$. | A **lower bound** on the depth of a rational expression, not the exact valuation of Lemma 9.1, and not a statement about the shifted prefixes of $P(W)$. The bridge $b^{-n}R_n=F_l(U_{k-1},V_k)$ (window rule) is written. |
| `SurvivingGrid.stride_order` (at P) | 43 | The order of $g$ modulo $p^eQ$ is $p^{e-v_p(g-1)}$ when $p$ is odd, $p\nmid Q$, $p\mid g-1$, $Q\mid g-1$. | The arc count (2.4)/(4) for arbitrary lengths is written. |

### `PowerSumPeeling.lean` (at R)

| Declaration | Line | What it states | Used in |
| --- | --- | --- | --- |
| `card_pow_diff_eq_le_divisors` | 79 | For $d\ge2$, $M>0$: the pairs $(a,c)$ with $c<a$ and $a^d-c^d=M$ number at most the number of divisors of $M$. | Lemma 7.16 (rows with $B=0$), Theorem 7.20 (bounded numerators, peeling) |
| `phiPoly_natDegree`, `phiPoly_leadingCoeff`, `phiPoly_ne_zero` | 232, 242, 222 | The recurrence polynomial $\Phi_q\in(\mathbb Z[B])[X]$ has $X$-degree $q-2$ and leading coefficient $(-1)^q\prod_{j=1}^{q-2}(d+j)\ne0$ ($d\ge1$). | Lemma 7.14 |
| `dominant_loss_unique_top_coord` | 372 | If $\sum y_i^d=\sum w_i^d$ (rationals $a_i/p^{h_i}$, $c_i/p^{g_i}$), the $y$ have a unique top loss $h_{\rm top}\ge1$ with $p\nmid a_{\rm top}$, and $\sum g_i<2h_{\rm top}$, then exactly one $w_i$ has loss $h_{\rm top}$ and the others have smaller loss. | Lemma 7.16, Theorem 7.20 (peeling steps) |
| `truncMass_sub`, `truncMass_jump_of_isolated` | 446, 483 | For a finite coordinate set and a centre $c$ with pairwise distinct coordinates, total loss $H\le\Lambda$, such that every tuple of loss $\le\Lambda$ within $\delta$ of $\sum c_i^d$ is a permutation of $c$: the truncated mass jumps by exactly $r!\,p^{sH}$ across $(\sum c_i^d-\delta/2,\sum c_i^d+\delta/2]$. | Lemma 7.12 |

Not in Lean: the derivative identity for $f_B^{(q)}$ (Lemma 7.14; checked exactly against Taylor coefficients for $4\le d\le7$, $2\le q\le6$ by `scripts/phase20_normality.py`), the homogeneity of $\Phi_q$, Titchmarsh's test, the Erdős–Turán inequality, the isolation counts, the small-ball recursion, the measure theory, and every rate.

## Statement map

Numbering is that of a scratch build of this candidate draft (48 pages after the revision below, built with the repository's TinyTeX toolchain in WSL on 26 November 2026 from `paper.tex` and `references.bib` with `../common/`; no undefined references or citations, no overfull boxes). No `paper.pdf` is committed in this directory yet. Introduction theorems restate later results as listed.

| No. | Statement (short) | Evidence | Lean declarations | External inputs | Reproduction / finite checks |
| --- | --- | --- | --- | --- | --- |
| A | Normality switch on schedules $n_k\ge k^2$ | Kernel-verified (= 4.5) | see 4.5 | — | `lake build` at E |
| B | Rate for $d\ge s+2$; $D_N(\xi)\le200N^{-1/3}$ | Lean-supported paper proof (= 4.7, 3.1) | see 4.2 | — | v1.0 `checks/xi_discrepancy.py` |
| C | Prescribed limits, pairs, limit sets | Lean-supported paper proof (= 5.3, 6.1, 6.4) | see 5.1 | Colebrook, Sigmund (comparison only, Remark 6.5) | `scripts/phase18_programming.py` at E |
| D | Total degree $r<d$ in distinct orders normal; one order: $(\log\log N)^{-d/(d-1)}$ ($r\ge2$), $N^{-\eta}$ ($r=1$); $\xi^2$ rate $(\log\log N)^{-3/2}$ | Lean-supported paper proof (= 7.1, 7.19, 7.20, 7.21, 7.22) | see 7.12, 7.14, 7.16 | see 7.13, 7.16 | see 7.16–7.21 |
| E | All-odd-prime normal Liouville sum; finite joint normality; rational totals | Lean-supported paper proof (= 8.2–8.4) | see 2.4, 8.4 | KN Ch. 1 Thms 2.1, 6.2 | `scripts/phase19_grids.py` at P |
| F | All-prime polynomial normality: (i) Liouville $W$; (ii) polynomial schedules; (iii) $\mu=\lambda$, degree $\le r$; (iv) $\mu=p$, all degrees. Finiteness of $\mu(W_H)$ **open** | (i) Lean-supported paper proof (= 9.2); (ii)–(iv) Paper proof (= 9.7, 9.10, 9.11) | see 9.1, 9.2 | see 9.2, 9.11 | see 9.2–9.11 |
| G | Boundary $d=r$: depth tight; barrier; retirement at $d=2$; cubic conditional | Paper proof, with External inputs (= 10.1–10.10) | (sharp translation via 10.8) | Landau, Hooley, Bambah–Chowla, Selberg–Delange, Wooley, DHL | `scripts/phase22_nonlinear_boundary.py` |
| 2.1 | Arcs; $D=\sup$ excess | Paper proof | — | — | — |
| 2.2 | Finite comparison | Paper proof (orbit case kernel-verified as `discrepancy_transfer`, E/Phase18Synthetic.lean L583) | `Phase18Synthetic.discrepancy_transfer` | — | — |
| 2.3 | Block certificate | Paper proof | — | — | — |
| 2.4 | Grids for $q=p^eQ$ | Lean-supported paper proof | `SurvivingGrid.stride_order` (P L43), `PrimePowerGrid.crt_period_count` (P L337) | — | `phase19_grids.py` |
| 2.5 | Prime-power orbits | Paper proof | — | — | `phase18_programming.py` |
| 2.6 | Sharp translation identity, quoted from manuscript H | Kernel-verified (proved there) | `SharpTranslation.sharp_translation` (E L343), `sharp_translation_isGreatest` (E L386) | Manuscript H, Thm 3.1 | `lake build` at E |
| 2.7 | **New.** Uniform short orbits: $\lvert S(G,e,c;M)\rvert\le9M_0^{1-\delta}$ for principal units, uniform in $G$ with $A(G)\le\frac3{16}\log_pM_0-1$ | Paper proof | — | — | `scripts/phase22_short_orbits.py`: LTE (31,840 cases), complete-orbit vanishing (41), stride van der Corput identity, sharpness example $\lvert S\rvert/M>0.98$ for $(p,a)=(3,6),(5,4),(7,3)$ |
| 2.8 | **New.** Splitting off a coprime modulus; $A(b^\tau)=a_0+v_p(\operatorname{ord}_Qb)$ | Paper proof | — | — | same script: CRT factorization on 53 prefixes, identity on all 243 divisors |
| 2.9 | **New.** Largest auxiliary prime via $A_b(x)$ | Paper proof | — | divisor bound (Hardy–Wright Thm 317); prime number theorem | — |
| 3.1 | $D_N(\xi;2)\le200N^{-1/3}$ | Paper proof | — | — | v1.0 finite certificate (unchanged) |
| 4.1 | Geometric grouping and repunit primes | Kernel-verified | as v1.0 | — | `lake build` at E |
| 4.2 | Exact reduced denominators | Kernel-verified | `RetirementDenominator.shiftedPrefix_den` (E L110), `fullPrefix_den` (E L157), `maximalLayer_card` (E L67) | — | `phase18_principal.py` |
| 4.3 | Fixed-support short orbits | Kernel-verified | `SmoothOrbit.fixed_support_orbit_estimate` (E L207) | — | `lake build` at E |
| 4.4 | All-prefix criterion | Lean-supported paper proof (step 4.3) | as 4.3 | KN Ch. 1 Thms 2.1, 8.1 | — |
| 4.5 | Normality switch | Kernel-verified | `discrepancy_switch` (E L436), `normal_iff_pos` (E L444), `polynomial_discrepancy_switch` (E L456) | — | `lake build` at E |
| 4.6 | Normal Liouville family on $t(k+1)!$ | Lean-supported paper proof | as 4.5 | Liouville's theorem | — |
| 4.7 | Complete-period rate, $d\ge s+2$ | Lean-supported paper proof (step 4.2) | as 4.2 | — | `phase18_principal.py` |
| 4.8 (Remark) | **Revised.** Power saving for every $d\ge2$ is the case $r=1$ of 7.21 | Remark | — | — | — |
| 5.1–5.3 | Programming, modelled discrepancy, every $\delta$ | as v1.0 (5.1 Kernel-verified; 5.2 Paper proof; 5.3 Lean-supported) | as v1.0 | — | `phase18_programming.py` |
| 6.1–6.5 | Pairs, necessity, weak continuity, limit sets, qualitative remark | as v1.0 (6.1, 6.4 Lean-supported; 6.2, 6.3 Paper proof; 6.5 Remark with External input) | as v1.0 | Colebrook, Sigmund, DGS, Riesz | — |
| 7.1–7.9 | Quadratic images (model case), freezing, primitive jumps, third derivatives, isolated centres, null level sets | as v1.0 (Paper proof; 7.3 historical finite bound; 7.9 Remark, **revised**) | none | GK91 Lemma 2.5, Thm 2.2; KN Ch. 2 Thm 2.5 | `phase19_nonlinear.py` at P |
| 7.10 | **New.** Freezing in degree $r$ | Paper proof | — | — | `phase21_nonlinear.py`: actual prefix of $C(2,3,1,4)^3$ vs $M_3\bmod27$ at $J=4$, six shifts |
| 7.11 | **New.** Reduction to the mass ($d\ge r+1$) | Lean-supported paper proof (step 4.3 via 4.4) | as 4.3 | — | — |
| 7.12 | **New.** Jumps at isolated centres, $r!p^{sH}$ | Lean-supported paper proof | `PowerSumPeeling.truncMass_jump_of_isolated` (R L483), `truncMass_sub` (R L446) | — | `phase20_normality.py` (flank residues) |
| 7.13 | **New.** $q$-th derivative test | External input | — | Titchmarsh, Thm 5.13 | — |
| 7.14 | **New.** Derivatives of $f_B$; $\Phi_q$ degree and leading coefficient | Lean-supported paper proof | `phiPoly_natDegree` (R L232), `phiPoly_leadingCoeff` (R L242), `phiPoly_ne_zero` (R L222) | — | `phase20_normality.py` (exact Taylor check, $4\le d\le7$, $2\le q\le6$) |
| 7.15 | **New.** Exponent margins $\sigma_2=1/12$, $\sigma_r=1/(r(2^{r+1}-2))$ | Paper proof | — | — | `phase20_normality.py` asserts $\sigma_r$ for $r=3,\dots,8$; `phase21_nonlinear.py` asserts $1/12$ and capped cases |
| 7.16 | **New.** Averaged isolation on unions of intervals | Lean-supported paper proof | `dominant_loss_unique_top_coord` (R L372), `card_pow_diff_eq_le_divisors` (R L79) | Titchmarsh 5.13; Erdős–Turán (KN Ch. 2 Thm 2.5); divisor bound | `phase20_normality.py`, `phase21_nonlinear.py` (illustrations only) |
| 7.17 | **New.** Uniform isolation fails ($p=3$, $d=4$, $r=3$) | Paper proof; **finite certificate** (stated for $H\ge6$; analytic argument for $H\ge5$) | — | — | `phase21_nonlinear.py` certifies the net for $H\in\{6,10,100,1000,4000\}$ and $R_{4000}^{126}<3^{4000}$; a scratch exact check also confirmed the net for $4\le H\le12$ (see below) |
| 7.18 | **New.** Small balls: $\lvert\{M_r\equiv w\bmod p^L\}\rvert\le C_*(\log L)^{-d/(d-1)}$, all $r,d\ge2$ | Lean-supported paper proof (via 7.12 and 7.16) | as 7.12, 7.16 | Lebesgue density (implicit in "null") | — |
| 7.19 | **New.** One order, every degree $r<d$ (GF-11) | Lean-supported paper proof | via 7.12, 7.14, 7.16 and 4.3 | as 7.16 | — |
| 7.20 | **New.** Several orders (Theorem M of the source) | Lean-supported paper proof | `dominant_loss_unique_top_coord`, `card_pow_diff_eq_le_divisors`, via 7.14 | as 7.16; Lebesgue differentiation; reverse Fatou | `phase21_nonlinear.py`: exact jumps at eight tied centres, loss-0 cancellation example |
| 7.21 | **New.** Effective rates for every $d\ge r+1$ | Paper proof | — | Erdős–Turán | `phase22_short_orbits.py` ($\delta$ table) |
| 7.22 | **New.** $D_N(\xi^2)\ll(\log\log N)^{-3/2}$; $C(2,3,1,4)^{1,2,3}$ jointly normal; rate for the cube | Paper proof | — | — | — |
| 8.1–8.5 | Infinite sums | as v1.0 | as v1.0 | as v1.0 | `phase19_grids.py` at P |
| 9.1 | **New.** Pole dominance in a truncated Taylor expansion | Lean-supported paper proof | `ProtectedPole.truncated_poly_pole_dvd_den` (R L347) — lower bound only | — | `phase20_normality.py` (exact pole formula at 222 prefixes) |
| 9.2 | **New.** Universal all-prime $W$: exact denominators, every $P(W)$ normal and Liouville, rate $\exp(-c(\log N)^{2/3})$ | Lean-supported paper proof | `shifted_prefix_protected_prime_pow_dvd_den` (R L245), `shifted_prefix_aux_prime_dvd_den` (R L143, newest prime only), `truncated_poly_pole_dvd_den` (R L347), `SurvivingGrid.stride_order` (P L43) | Chebyshev's bound; $\prod_{\ell\le x}\ell<4^x$ (proved in §8) | `phase20_normality.py` (270 prefixes, five radix/prime pairs, $q_n=p^{k^2}\ell_1\cdots\ell_k$) |
| 9.3 | **New.** General protected poles (one generator) | Lean-supported paper proof | as 9.1 | — | `phase20_normality.py` |
| 9.4 | **New.** $\log\operatorname{lcm}_{\ell\le x}(\ell-1)\ll x\log\log x/\log x$ | Paper proof using an **External input** | — | Selberg upper-bound sieve (Halberstam–Richert) | `phase21_nonlinear.py` (primorial vs lcm table, illustration) |
| 9.5 | **New.** Denser all-prime schedules (GF-15 part 1) | Paper proof | — | prime number theorem; 9.4 | — |
| 9.6 (Remark) | Several generators (not used) | Remark | — | — | `phase20_normality.py` (Variant 1 and 2 checks) |
| 9.7 | **New.** All-prime polynomial schedules for every $d\ge r+1$ (Theorem H′ of the source) | Paper proof | — | as 7.21; 2.9 | `phase21_nonlinear.py` (exact denominators, residue pollution at $k=27$); `phase22_short_orbits.py` (CRT split on prefixes) |
| 9.8 | **New.** Truncation separation | Paper proof | — | — | — |
| 9.9 | **New.** Ratio-one schedules: only $\lvert W_H-A/Q\rvert\ge Q^{-\psi(Q)}$, $\psi\to\infty$; **finiteness of $\mu(W_H)$ and non-Liouville status open** | Paper proof | — | — | `phase22_short_orbits.py` ($\rho_k$ table) |
| 9.10 | **New.** Geometric schedules: degree $\le r$, $D_N\ll N^{-\eta}$, $\mu(W_G)=\lambda$ ($\lambda\ge3$) | Paper proof | — | Roth's theorem (transcendence only) | `phase22_short_orbits.py`: exact valuation at 145 insertion positions, exact $\operatorname{den}U_k$, convergent exponents (finite evidence only) |
| 9.11 | **New.** Stoneham schedule: all degrees, $\mu(W_S)=p$ | Paper proof using an **External input** | — | Pole retention for $\alpha_{b,p}$: Paper I v2.0, Lemmas 2.2–2.4 (Paper proofs there; only Lemma 2.5 and Theorem A of that paper are Lean-supported or kernel-verified) | `phase22_short_orbits.py`: bounded depth defects $d=2,\dots,5$; congruence with $\alpha_{2,3}$ modulo $3^l$ at 42 and 121 positions |
| 9.12 (Remark) | Quasi-polynomial schedule: all-degree normality recorded **without proof**; finiteness of the exponent and non-Liouville status **open** | Remark (not a claim of this paper) | — | Phase 19 plateau estimate (not reproduced) | `phase21_nonlinear.py` (budget table) |
| 10.1 | **New.** Depth tight in density at $d\le r$ | Paper proof | — | — | `phase21_nonlinear.py` (exact 3-adic depth up to $4\cdot10^5$, illustration) |
| 10.2 | **New.** Denominators do not determine digits | Paper proof | — | — | `phase21_nonlinear.py` ($q=3^e$, $e\le9$) |
| 10.3 | **New.** No uniform cancellation below $\log_b(\epsilon q)$ | Paper proof | — | — | `phase22_nonlinear_boundary.py` ($q=3^{20},3^{40},3^{80}$) |
| 10.4 | **New.** Level filtration $p^{sH}C^r=X_H+Z_H$, mass bound, prefix identity | Paper proof | — | — | `phase22_nonlinear_boundary.py` (coefficientwise identity, $m\le2\cdot10^4$ and $3\cdot10^4$) |
| 10.5 | **New.** Sparse integer series transfer (self-contained, non-sharp constant) | Paper proof | — | — | — |
| 10.6 | **New.** Absorption of the integer part at $d=r=2$, uniform in $H$ | Paper proof using an **External input** | — | Landau's theorem | — |
| 10.7 | **New.** Integer dilation inequalities (and the normality converse in the text) | Paper proof | — | ergodicity of Lebesgue measure under $T$ (standard) | `phase22_nonlinear_boundary.py` (1,200 point sets) |
| 10.8 | **New.** Fixed-depth retirement: $C^2$ normal iff $Z_H$ normal | Lean-supported paper proof (step 2.6) | as 2.6 | — | `phase22_nonlinear_boundary.py` ((2.1) on actual orbits, illustration) |
| 10.9 | **New.** Runs after retirement (support runs) | Paper proof using **External inputs** | — | Landau; Hooley (1971) gap moments; Bambah–Chowla | `phase22_nonlinear_boundary.py` (coverage table, finite only) |
| 10.10 | **New.** Fractional jumps for $p\equiv3\pmod4$ | Paper proof using an **External input** | — | Selberg–Delange (Tenenbaum II.5) | `phase22_nonlinear_boundary.py` ($9^{k_H}\mathcal F_3\subseteq\mathcal P_H^{\rm frac}$ for $H\le3$) |
| 10.11 (Remark) | Finite digit statistics of $C(2,3,1,2)^2$, $C(2,3,2,2)^2$, $\xi^3$ | Finite measurement (not a claim) | — | — | `phase22_nonlinear_boundary.py` |
| §10.4 text | Cubic boundary: absorption conditional on density zero of sums of three cubes | External input / conditional; no claim | — | Wooley (2015); DHL (2006) model | `phase22_nonlinear_boundary.py` (counts to $10^6$) |

Registry correspondence: Theorems A–C, E and Sections 2–8 carry the v1.0 identifiers [SY-01](../../docs/results.md#sy-01), [SY-02](../../docs/results.md#sy-02), [SY-03](../../docs/results.md#sy-03), SY-06, SY-07, SY-11, SY-13, SY-16, SY-19, [OP-08](../../docs/results.md#op-08), [OP-09](../../docs/results.md#op-09) and [OP-14](../../docs/results.md#op-14). The new material corresponds to [GF-10](../../docs/results.md#gf-10) (Theorems 9.2–9.3, Remark 9.6), [GF-11](../../docs/results.md#gf-11) (Theorem 7.19), [GF-14](../../docs/results.md#gf-14) (Proposition 7.17, Lemma 7.16, Theorems 7.18, 7.20, Proposition 10.1, Lemma 10.2) and [GF-15](../../docs/results.md#gf-15) (Corollary 9.5, Theorem 9.7 in its $d>r(s+1)$ form, Remark 9.12). Lemma 2.7–2.9, Theorem 7.21 in the range $r+1\le d\le r(s+1)$, Theorem 9.7 in that range, Lemma 9.8, Proposition 9.9, Theorems 9.10–9.11 and Section 10 beyond Proposition 10.1 and Lemma 10.2 come from the notes [`short-orbits-and-irrationality.md`](../../notes/phase22/short-orbits-and-irrationality.md) and [`nonlinear-equality-boundary.md`](../../notes/phase22/nonlinear-equality-boundary.md), which are now registered as [GF-25](../../docs/results.md#gf-25) (short orbits, rates for every $d\ge r+1$, Theorems H′, G, S of the source) and [GF-24](../../docs/results.md#gf-24) (the equality boundary). The registry text of GF-25 calls Theorems 9.10–9.11 "the first explicit non-Liouville all-prime polynomial normal numbers"; the manuscript does **not** adopt that priority claim (see [LEDGER.md](LEDGER.md)).

**Untracked Lean module.** GF-24 lists declarations of `NormalityChecker/Phase22Cores.lean`: `one_sub_radixDiscrepancy_natMul_le` and `one_sub_radixDiscrepancy_intMul_le` (the orbit form of the second inequality of Lemma 10.7), `fixed_depth_transfer_deficit_le` (the inequality of Corollary 10.8 combined with the sharp translation identity) and `total_depth_split_sum`, `total_depth_split_sum_zpow` (the finite form of the split in Proposition 10.4). The module is untracked in this worktree, so it has no pinned commit and the manuscript does not link it; Lemma 10.7 and Proposition 10.4 keep the label *Paper proof*. Once the module is committed and kernel-replayed, those statements can be relabelled *Lean-supported paper proof* with links at that commit.

## Sources and model reviews

| Material | Source note | Model review (not human peer review) |
| --- | --- | --- |
| 7.10–7.19 (one order) | [`cubic-power-schedule.md`](../../notes/phase20/cubic-power-schedule.md), [`nonlinear-boundary.md`](../../notes/phase21/nonlinear-boundary.md) §§1–4 | [Phase 20 Track C](../../notes/phase20/reviews/track-c-review.md) (three Major findings, repaired); [Phase 21 Track C](../../notes/phase21/reviews/track-c-review.md) (re-audit, findings repaired, post-repair ACCEPT) |
| 7.20 (several orders) | [`multivariate-and-dense-allprime.md`](../../notes/phase21/multivariate-and-dense-allprime.md) §§1–3 | Phase 21 Track C (two Critical findings on localization, repaired by the $L^1$ argument; post-repair ACCEPT) |
| 7.21, 2.7–2.9, 9.7–9.11 | [`short-orbits-and-irrationality.md`](../../notes/phase22/short-orbits-and-irrationality.md) | [Phase 22 Track C3–C4](../../notes/phase22/reviews/track-c34-review.md) (five Major findings, including the freezing constraint in 7.21 and the bound on $A(G)$, repaired; post-repair Accept) |
| 9.1–9.6 | [`all-prime-polynomials.md`](../../notes/phase20/all-prime-polynomials.md), [`multivariate-and-dense-allprime.md`](../../notes/phase21/multivariate-and-dense-allprime.md) §5 | Phase 20 Track C (ACCEPT for C1; one Major quantifier fix in C2b); Phase 21 Track C (Proposition 5.1 part 3 needed (S), repaired) |
| 10.1–10.2 | [`nonlinear-boundary.md`](../../notes/phase21/nonlinear-boundary.md) §7 | Phase 21 Track C (Major quantifier swap in Proposition D, repaired to tightness in density) |
| 10.3–10.11, §10.4 | [`nonlinear-equality-boundary.md`](../../notes/phase22/nonlinear-equality-boundary.md) | [Phase 22 Track C1–C2](../../notes/phase22/reviews/track-c12-review.md) (three Major findings, repaired; post-repair ACCEPT) |

Changes made in writing the manuscript, relative to the source notes: (1) the qualitative Theorem 7.19 is deduced from the small-ball Theorem 7.18 instead of from the constant-measure route of the Phase 20 note; the anchor family of Lemma 7.16 uses $h_2\ge\max(2h_1+1,\lambda H)$ throughout. (2) The $K_b$-absorption Theorem 10.6 is proved from the self-contained Lemma 10.5 (Markov averaging of the tail) instead of citing the sharp coefficient transfer of the generating-function notes; the constant is worse and the order is the same. (3) Process language of the notes was removed. No statement was strengthened beyond its source.

## Exact checks run for this draft (26 November 2026)

From the repository root, in this worktree (standard library Python):

| Command | Exit | Time |
| --- | --- | --- |
| `python -B scripts/phase20_normality.py` | 0 | 70 s |
| `python -B scripts/phase21_nonlinear.py` | 0 | 3 s |
| `python -B scripts/phase22_short_orbits.py` | 0 | 7 s |
| `python -B scripts/phase22_nonlinear_boundary.py` | 0 | 5 s |

The two Phase 22 scripts are untracked in this worktree at the time of writing; **they must be committed before this version is released** (§12 of the manuscript says they accompany this version). The Phase 18–19 scripts and the v1.0 certificate `checks/xi_discrepancy.py` were not rerun; their v1.0 records stand.

**Supplementary check for Proposition 7.17.** After review the proposition is stated for $H\ge6$, where the target interval is nonempty ($\rho_H>2\delta_H$) and which is consistent with the repository certificate for $H\in\{6,10,100,1000,4000\}$; for $H=4,5$ the net property holds but the interval $(2+\rho_H+\delta_H,2+2\rho_H-\delta_H)$ is empty. For this draft a direct exact computation with Python `fractions` verified, for each $4\le H\le12$, that consecutive points $(a/3^H)^4$ with $3\nmid a$ covering $(\rho_H,2\rho_H]$ are at most $2\delta_H$ apart and that the first lies below $\rho_H$ (so $(2+\rho_H,2+2\rho_H]$ is covered); all nine cases passed ($R_4=8193,\ldots,R_{12}=153362$). This scratch file is not in the repository and is not cited by the manuscript; the referee independently confirmed the net for $4\le H\le14$.

## Revision after cross-model review (26 November 2026)

An independent model review from a different provider, [`paper-vii-v2-review.md`](../../notes/phase22/reviews/paper-vii-v2-review.md) (verdict ACCEPT AFTER REVISION; 0 Critical, 6 Major, 12 Minor), was answered in full. Cross-model review is not independent human peer review. The resulting label changes in this map: Theorem 7.18 is now *Lean-supported paper proof* (via Lemmas 7.12 and 7.16); Proposition 7.17 carries *Paper proof; finite certificate* and is stated for $H\ge6$; the input to Theorem 9.11 from Paper I v2.0 is recorded as paper proofs there; §12 of the manuscript now separates the paper proofs (7.1, 7.2, 7.21, 7.22) from the Lean-supported paper proofs (7.18–7.20). The full list of repairs is in [CHANGES.md](CHANGES.md).

## Manuscript checks run for this draft

- Python check of `paper.tex` and `references.bib` (26 November 2026): all `\begin`/`\end` environments matched; braces balanced in both files; inline `$` balanced in every paragraph; every `\cite` key present in `references.bib`, every bibliography entry cited, no duplicate keys; every referenced label defined, no duplicate labels; no process language from the source notes. Rerun after the revision below.
- Scratch LaTeX build (three `pdflatex` passes and `bibtex`, TinyTeX in WSL, outside the repository): exit 0, no errors, no undefined references or citations, no overfull boxes, 48 pages, PDF author metadata `Christopher Anderson`, statement numbering unchanged by the revision. Pages 1, 4, 26, 27 and 34 were rendered and inspected. No `paper.pdf` was written into the repository.
- `PYTHONUTF8=1 python scripts/portal.py check --strict --skip-figures`: **passed** ("198 registered results, 252 Markdown files, links, anchors, identifiers, topics and figures"), so every link, anchor and registry identifier in these three Markdown files resolves. Without `--skip-figures` the strict check reports one unrelated pre-existing error, a stale `assets/figures/data/proof-dependency-map.json`, which this draft does not touch.
