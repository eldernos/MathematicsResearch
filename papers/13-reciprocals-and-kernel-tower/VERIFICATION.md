# Verification map: The Radix-Power Discrepancy Kernel Tower and Reciprocals of Extreme-Discrepancy Numbers (v1.0, candidate draft)

This file maps every numbered statement of the candidate draft to one evidence label: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **External input**, **Finite certificate**, or **Open**. Finite computations quoted as illustrations are finite measurements, not evidence for asymptotic statements.

**Cross-model review is not independent human peer review.** The written proofs, and the repository notes they come from, have been checked only by AI models from different providers. No human specialist has read them, and the assembled manuscript has not been reviewed as a whole.

**Status.** This is an unreleased candidate draft. It has no entry in `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml`, or `docs/registry/papers.toml`, and no `paper.pdf`, `metadata.toml`, or `submission/` directory. **`pdflatex`/`bibtex` compilation is pending before release.** Neither tool is installed on the local Windows host or on `hail`, so the draft has not been typeset; only the structural check below has been run.

## Pinned and working-tree Lean commits

- **R** = `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8` (Phase 21): `NormalReciprocalCore`.
- **T** = `8ca43095887858bf9697b6a8332c6a6dd0b0cda3` (Phase 22): `RadixPowerTower`, `SimpleNormalityKernel`.
- **W (working tree, pending commit pinning before release)**: `NormalityChecker/HigherOrderTower.lean` (built and verified on `hail` in the Phase 23 working tree with Lean 4.36.0, zero warnings, zero `sorry`, standard axioms `propext`, `Classical.choice`, `Quot.sound`).

## Exact scope of the Lean declarations used

| Declaration | Module / Commit, line | What it states | What it does **not** state |
| --- | --- | --- | --- |
| `NormalReciprocalCore.band_identity` | R L74 | Exact rational band identity $b^{im+r}R\frac{b^m}{b^m-1}\equiv(i+1)b^rR+\frac{b^rR}{b^m-1}\pmod 1$ when $\ord_{\den(R)}(b)\mid m$. | Does not state Weyl bounds, Erd\H{o}s--Tur\'an rates, or normality. |
| `NormalReciprocalCore.signed_band_identity` | R L139 | Exact alternating-sign band identity for $1/(1+b^{-m})$ showing odd-band multiplier vanishing. | Does not state $W_1$ contractions or sign-classification limit sets. |
| `NormalReciprocalCore.sum_residues_cexp_eq_zero` | R L255 | $\sum_{c\in\Z/D\Z}e(cku/D)=0$ for $\gcd(u,D)=1$ and $D\nmid k$. | Finite character sum only; does not state all-prefix equidistribution. |
| `RadixPowerTower.strict_kernel_inclusion` | T L347 | $K_b\subsetneq K_{b^k}$ for $b,k\ge2$ (via $1/(b^k-1)$). | Full quotient $K_{b^k}/K_b\cong\Z/R\Z$ requires `HigherOrderTower.mem_pow_kernel_decomp`. |
| `RadixPowerTower.zeroOrbitSubgroup_pow_eq` | T L694 | $M_{b^k}=M_b$ (with sharp bounds `circMean_pow_le` L467, `circMean_le_circMean_pow` L531, `circMean_le_circMean_pow_add` L553). | Full-kernel decomposition $K_b=F_b+M_b$ is in `HigherOrderTower.lean`. |
| `RadixPowerTower.fixedPoint_quotient_equiv_gen`, `fixedPoint_quotient_card`, `fixedPointSubgroup_inter_zeroOrbitSubgroup` | T L828, L846, L896 | $F_{b^k}/F_b\cong\Z/R\Z$ (generator $1/(b^k-1)$) and $F_{b^k}\cap M_b=\Z$. | Only the fixed-point quotient; `HigherOrderTower.mem_pow_kernel_decomp` upgrades to $K_{b^k}$. |
| `RadixPowerTower.coprime_rat_cylinder_margin`, `coprime_rat_cylinder_stable` | T L928, L1012 | Strict $1/(db^L)$ margin from $b$-adic grid points and cylinder stability for coprime rationals $r/d$. | Finite perturbation lemma only. |
| `RadixPowerTower.orderOf_mul_pow_sub_one`, `orderOf_mul_pow_add_one` | T L1247, L1272 | $\ord_{D(b^m-1)}(b)=mD$ and $\ord_{D(b^m+1)}(b)=2m$ under **full divisibility** $D\mid(b^m-1)$. | Does **not** cover the weaker Hull--Dobell hypothesis $\rad^*(D)\mid(b^m-1)$ (which is a written proof). |
| `HigherOrderTower.kernel_eq_fixedPoint_add_zeroOrbit`, `mem_pow_kernel_decomp` | W L522, L548 | $K_b=F_b+M_b$ and unique decomposition $x=r/(b^k-1)+u$ ($0\le r<b^k-1$, $u\in M_b$) with $x\in K_b\iff(b^k-1)\mid(b-1)r$. | Uncommitted working-tree module; must be committed and pinned before release. |
| `HigherOrderTower.wordFreq_tower_limit` | W L715 | Asymptotic length-$L$ word frequency $\mathrm{cyclicCount}(b,k,L,r,v)/k$ for $r/(b^k-1)+u$ ($u\in M_b$). | Does not state the exact finite-level discrepancy spectrum (Proposition 2.7). |
| `HigherOrderTower.tower_iff`, `tower_irrational_exact_iff`, `all_kernel_pow_iff` | W L2228, L2065, L2779 | Complete higher-order normality classification in $K_{b^k}\setminus K_b$ (including exact-order-$L$ irrationals) and in $K_{b^k}$. | Does not state the full real discrepancy spectrum $[0,2/b^L]$ or tower density (Theorem 2.8). |
| `HigherOrderTower.radixDiscrepancy_le_grid_add`, `limsup_radixDiscrepancy_le_of_orderNormal` | W L2854, L2983 | Finite grid bound and universal ceiling $D^+(x;b)\le 2/b^L$ for every $L$-normal real. | Does not formalize attainment of $2/b^L$ (Theorem 2.8 / Theorem 6.1). |

## Statement map

Statement numbers come from a structural count of `paper.tex` (shared counter per section) and will be confirmed upon `pdflatex` compilation.

| No. | Statement (short) | Evidence | Lean | External inputs | Source note and finite checks |
| --- | --- | --- | --- | --- | --- |
| A | (i)--(iii) Tower $K_{b^k}/K_b$, $M_b=M_{b^k}$, $b^L\mid k$ classification, $D^+\le 2/b^L$; (iv) real spectrum $[0,2/b^L]$ and tower density | (i)--(iii) **Kernel-verified**; (iv) **Paper proof** | `RadixPowerTower`, `HigherOrderTower` (see 2.1--2.5) | — | [`euler-square-and-higher-order-tower.md`](../../notes/phase23/euler-square-and-higher-order-tower.md) §§3--5; [`odd-characters-and-kernel-quotient.md`](../../notes/phase22/odd-characters-and-kernel-quotient.md) §§7--10 |
| B | (i)--(ii) Reciprocal period lifting, balanced-multiplier rate, Koksma lower barrier; (iii) Bang--Zsigmondy rigidity & relaxed Hull--Dobell normality/barrier | (i) and normality in (ii) **Lean-supported paper proof**; rate & barrier in (ii) **Paper proof**; (iii) **Paper proof** + **External input** | `orderOf_mul_pow_sub_one`, `orderOf_mul_pow_add_one`, `band_identity`, `sum_residues_cexp_eq_zero` | Bang (1886); Zsigmondy (1892); Wigert divisor bound; Erd\H{o}s--Tur\'an | [`normal-reciprocals-and-signs.md`](../../notes/phase22/normal-reciprocals-and-signs.md) §§1--3; [`convergent-reciprocals-and-schedules.md`](../../notes/phase23/convergent-reciprocals-and-schedules.md) §3 |
| C | (i) Complete sign classification & oriented $0^+$ collapse; (ii) cyclotomic $P_k$ realizations; (iii) $+1$-inversion dense $\mathcal A_{\mathrm{conv}}(2)$ & all-base repunit localization | **Paper proof** (quoting `signed_band_identity`, `coprime_rat_cylinder_margin`) | see 4.2, 5.2 | Erd\H{o}s--Tur\'an | `normal-reciprocals-and-signs.md` §§4--5; `convergent-reciprocals-and-schedules.md` §1 |
| D | (i) Sharp $D_{\max}(b,L)=2b^{-L}$; (ii) base-$2$ dense $L$-normal reciprocals & prescribed word laws; (iii) all-base $L$-normal nonnormal reciprocals via $\mathcal G_{b,M}$ | **Paper proof** | see 6.3 (`coprime_rat_cylinder_margin`) | — | `convergent-reciprocals-and-schedules.md` §2 |
| E | (i) Anchored coprime non-tetration $O((\ln N)^{-A})$; (ii) fully coprime base-$2$ CRT convolution, prime product, sub-exponential $D(\mu(R_k;2))$; (iii) exponential equidistribution of $R_k^{(E)}$ | **Paper proof** | — | Erd\H{o}s--Tur\'an; divergence of $\sum 1/p$ | `convergent-reciprocals-and-schedules.md` §§4--5 |
| 2.1 | Zero-orbit invariance $M_{b^k}=M_b$, $F_{b^k}/F_b\cong\Z/R\Z$, $K_b\subsetneq K_{b^k}$ | **Kernel-verified** (sharpness attainment remark in (i): **Paper proof**) | `RadixPowerTower` T L106--L896 | — | `odd-characters-and-kernel-quotient.md` §§7--8; `scripts/phase22_characters_quotient.py` |
| 2.2 | Kernel decomposition $K_b=F_b+M_b$ and unique $K_{b^k}$ representation | **Kernel-verified** | `HigherOrderTower` W L331, L522, L548 | — | `euler-square-and-higher-order-tower.md` §3 |
| 2.3 | Coprime-rational cylinder word-frequency transfer | **Kernel-verified** | `HigherOrderTower.wordFreq_tower_limit` W L715; `RadixPowerTower` T L928, L1012 | — | `euler-square-and-higher-order-tower.md` §3 |
| 2.4 | Higher-order tower classification ($K_{b^k}\setminus K_b$ and $K_{b^k}$) | **Kernel-verified** | `HigherOrderTower.tower_iff`, `tower_irrational_exact_iff`, `all_kernel_pow_iff` W L2065--L2779 | — | `euler-square-and-higher-order-tower.md` §3 |
| 2.5 | Universal $L$-normal discrepancy bound $D^+(x;b)\le 2/b^L$ | **Kernel-verified** | `HigherOrderTower.radixDiscrepancy_le_grid_add`, `limsup_radixDiscrepancy_le_of_orderNormal` W L2854, L2983 | — | `euler-square-and-higher-order-tower.md` §5 |
| 2.6 | De Bruijn cycle discrepancy envelope | **Paper proof** | — | — | `euler-square-and-higher-order-tower.md` §4; `scripts/phase23_euler_tower.py` |
| 2.7 | Exact finite-level tower spectrum $\mathcal S_{b,L,k}$ | **Paper proof** | — | — | `euler-square-and-higher-order-tower.md` §4; **Finite certificate**: `scripts/phase23_euler_tower.py` (5 rows + brute enumeration) |
| 2.8 | Full real spectrum $[0,2/b^L]$, exact-order $(0,2/b^L]$, tower density | **Paper proof** | — | — | `euler-square-and-higher-order-tower.md` §5 |
| 3.1 | Exact period identities & Hull--Dobell bijection | **Lean-supported paper proof** | `RadixPowerTower.orderOf_mul_pow_sub_one` T L1247, `orderOf_mul_pow_add_one` T L1272 (for $D\mid b^m-1$) | — | `normal-reciprocals-and-signs.md` §1; **Finite certificate**: `scripts/phase22_reciprocals.py` (590 Hull--Dobell + 448 plus-sign + 72 signed-triple checks) |
| 3.2 | Four finite inequalities (partial-band, divisor-sum, shifted grid, Koksma) | **Paper proof** | — | — | `normal-reciprocals-and-signs.md` §2.1; **Finite certificate**: `phase22_reciprocals.py` (14,040 partial-band tuples) |
| 3.3 | Sharpened all-prefix Weyl, Erd\H{o}s--Tur\'an, grid, and Koksma bounds | **Lean-supported paper proof** | `NormalReciprocalCore.band_identity` R L74, `sum_residues_cexp_eq_zero` R L255 | Erd\H{o}s--Tur\'an; Wigert divisor bound | `normal-reciprocals-and-signs.md` §2.2; `phase22_reciprocals.py` (exact grid checks + float samples) |
| 3.4 | Balanced-multiplier rate and universal Koksma lower barrier | **Paper proof** | — | — | `normal-reciprocals-and-signs.md` §3.1--3.2 |
| 3.5 | Bang--Zsigmondy rigidity $\rad^*(b^m-1)\mid(b^n-1)\iff m\mid n$ | **Paper proof** + **External input** | — | Bang (1886); Zsigmondy (1892) | `convergent-reciprocals-and-schedules.md` §3.1; **Finite certificate**: `scripts/phase23_reciprocals_v2.py` §4 (1,666 triples) |
| 3.6 | Relaxed Hull--Dobell characterization, normality, barrier, forced growth | **Paper proof** + **External input** | — | Bang (1886); Zsigmondy (1892) (for (i) and (iii)) | `normal-reciprocals-and-signs.md` §3.2 (Audit 2); `convergent-reciprocals-and-schedules.md` §3.2; `phase23_reciprocals_v2.py` §4 (2,343 exact checks) |
| 4.1 | Perturbation and $W_1$-continuity of discrepancy | **Paper proof** | — | — | `normal-reciprocals-and-signs.md` §4.1 |
| 4.2 | Complete-period $W_1$ recursion and shell trajectories (incl.\ Kronecker melting) | **Lean-supported paper proof** | `NormalReciprocalCore.signed_band_identity` R L139 | Erd\H{o}s--Tur\'an | `normal-reciprocals-and-signs.md` §4.2--4.3 (Audit 2 uniform tail bound) |
| 4.3 | Complete sign classification of $y(\varepsilon)$ | **Paper proof** | — | — | `normal-reciprocals-and-signs.md` §4.4 |
| 4.4 | Oriented $0^+$ digit frequencies and simple-normality collapse | **Paper proof** | — | — | `normal-reciprocals-and-signs.md` §4.4 |
| 4.5 | Closed-form band structure and band identity of $P_k(q)$ | **Paper proof** | — | — | `normal-reciprocals-and-signs.md` §5.1--5.2; **Finite certificate**: `phase22_reciprocals.py` §5 ($k=1\dots25$ in exact $\Z[q]$) |
| 4.6 | Cyclotomic $K_2$ simple normality and prescribed $D^+=\alpha\in[0,1]$ | **Paper proof** | — | Erd\H{o}s--Tur\'an | `normal-reciprocals-and-signs.md` §5.3--5.4 (Audit 2 outer-band and signed-lift repairs) |
| 5.1 | Interior $W_\infty$-perturbation discrepancy stability | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §1.1 |
| 5.2 | Rational-orbit $+1$-inversion ($x\in M_b\subset K_b$, $1/x\to\mu(r;b)$) | **Paper proof** | `RadixPowerTower.coprime_rat_cylinder_margin` T L928 | — | `convergent-reciprocals-and-schedules.md` §1.2; **Finite certificate**: `phase23_reciprocals_v2.py` §1 |
| 5.3 | Density of $\mathcal A_{\mathrm{conv}}(2)$ in $[0,1]$ | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §1.3 |
| 5.4 | All-base universal repunit inversion $Q_b(q)$ and localization | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §1.3; **Finite certificate**: `phase23_reciprocals_v2.py` §1 (incl.\ $A>1$ seeds) |
| 5.5 | $Q(1)=1$ coefficient excess identity (plus Remark 5.6 heuristic) | **Paper proof** (Remark 5.6: heuristic + **Finite certificate** for $L\le50$) | — | — | `convergent-reciprocals-and-schedules.md` §1.4; `phase23_reciprocals_v2.py` §1e (1,050 divisors) |
| 6.1 | Sharp ceiling $D_{\max}(b,L)=2b^{-L}$ and $G_{b,L}^*$ attainment | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §2.1; **Finite certificate**: `phase23_reciprocals_v2.py` §2 (125 exact checks) |
| 6.2 | Strict cell interiority and simultaneous $L$-normality on $\mathcal G_{b,M}$ | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §2.2 (repaired digit-label hypothesis); `phase23_reciprocals_v2.py` §3 |
| 6.3 | Unconditional $L$-normal nonnormal reciprocals in all bases $b\ge2$ | **Paper proof** | `RadixPowerTower.coprime_rat_cylinder_margin` T L928 | — | `convergent-reciprocals-and-schedules.md` §2.2; **Finite certificate**: `phase23_reciprocals_v2.py` §3 (3,732 exact checks) |
| 6.4 | Primitive-root $2/p$ realization and quadratic-reciprocity obstruction | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §2.2; `phase23_reciprocals_v2.py` §3 |
| 6.5 | $R_0=1$ obstruction for $(b,L)\neq(2,1)$ | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §2.2 |
| 7.1 | Anchored coprime non-tetration normal reciprocals ($O((\ln N)^{-A})$) | **Paper proof** | — | Erd\H{o}s--Tur\'an | `convergent-reciprocals-and-schedules.md` §4; **Finite certificate**: `phase23_reciprocals_v2.py` §5 (4,431 exact checks) |
| 7.2 | Universal $01$-transition Fourier bound $|S(u,m)|\le 1-(2-\sqrt2)/m$ | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §5.1 |
| 7.3 | Prime-exponent product $D(\mu(R_k^{(\mathrm{prime})};2))\to0$ | **Paper proof** | — | Divergence of $\sum 1/p$ | `convergent-reciprocals-and-schedules.md` §5.1 |
| 7.4 | Fully coprime base-$2$ normality and $O(\exp(-c_0(\ln T_k)^{1/4}))$ | **Paper proof** | — | Erd\H{o}s--Tur\'an | `convergent-reciprocals-and-schedules.md` §5.2--5.3; `phase23_reciprocals_v2.py` §6 |
| 7.5 | Exponential complete-period equidistribution of $R_k^{(E)}$ in all bases | **Paper proof** | — | — | `convergent-reciprocals-and-schedules.md` §5.4; **Finite certificate**: `phase23_reciprocals_v2.py` §6 (80 exact checks) |
| 8.1--8.4 | Questions | **Open** | — | — | — |

Registry correspondence: [GF-16](../../docs/results.md#gf-16) (Phase 21 reciprocal band framework), [GF-23](../../docs/results.md#gf-23) (Theorem 2.1, Theorem 2.2), [GF-26](../../docs/results.md#gf-26) (Theorems 3.1, 3.3, 3.4, 4.3, 4.4, 4.6), [GF-29](../../docs/results.md#gf-29) (Phase 23 Track A2, `HigherOrderTower.lean`, Theorems 2.2--2.8; in working-tree `docs/registry/GF.toml`), and [GF-34](../../docs/results.md#gf-34) (Phase 23 Track D1--D2--D4, Theorems 3.5--3.6, 5.2--5.5, 6.1--6.5, 7.1--7.5; in working-tree `docs/registry/GF.toml`).

## Sources and cross-provider model reviews (not human peer review)

| Material | Source note | Cross-provider model review (not human peer review) |
| --- | --- | --- |
| §§2.1--2.3 | `notes/phase22/odd-characters-and-kernel-quotient.md` §§7--10 | Phase 22 Track B3--B4 review (`notes/phase22/reviews/track-b34-review.md`): post-repair ACCEPT |
| §§2.2--2.3 (order $L$, spectra) | `notes/phase23/euler-square-and-higher-order-tower.md` §§3--5 | Phase 23 Track A1--A2 review (`notes/phase23/reviews/track-a12-review.md`): 0 Critical, 0 Major, 6 Minor on A2; post-repair ACCEPT |
| §§3.1--3.3, §4 | `notes/phase22/normal-reciprocals-and-signs.md` (GF-26) | Phase 22 Track D1--D2 review (`notes/phase22/reviews/track-d12-review.md`) + Phase 23 Audit 2 (`notes/phase23/reviews/phase22-analytic-audit-shortorbits-reciprocals.md`): 0 Critical, post-repair ACCEPT (repairs carried in: Hull--Dobell normality & Bang--Zsigmondy barrier, uniform geometric higher-tail bound in Kronecker melting, prefix-independent $0^+$ formulation, fixed/partial outer-band uniformity and signed lift in Theorem 4.6) |
| §3.3 (Bang--Zsigmondy), §§5--7 | `notes/phase23/convergent-reciprocals-and-schedules.md` (Track D1, D2, D4) | Phase 23 Track D review (`notes/phase23/reviews/track-d124-review.md`): 0 Critical, 5 Major (all repaired: standing full-limit $K_b$/$M_b$ definitions & all-prefix proof \eqref{eq:all-minus-Mb}, repaired digit-label hypothesis in Lemma 6.2, accurate citation of `orderOf_mul_pow_sub_one` vs written Hull--Dobell proof, `External input` label for Bang--Zsigmondy, heuristic framing of Remark 5.6 and (HD1)--(HD2) growth) |

## Repository state and pending release items

- **Uncommitted / untracked working-tree files:** `NormalityChecker/HigherOrderTower.lean`, `scripts/phase23_euler_tower.py`, `scripts/phase23_reciprocals_v2.py`, and the Audit 2 repair in `scripts/phase22_reciprocals.py`. All must be committed and pinned before any release.
- **Manuscript structural check (PASS, 27 November 2026):** Python check of `papers/13-reciprocals-and-kernel-tower/paper.tex` against `references.bib`:
  - Balanced braces in both `paper.tex` and `references.bib`; all `125` `\begin`/`\end` pairs balanced; `45`/`45` display-math `\[`/`\]` delimiters balanced; inline `$` balanced in all `177` paragraphs.
  - `67` labels, all distinct (`0` duplicates); `140` `\ref`/`\cref`/`\Cref`/`\eqref` calls across `55` distinct targets (`0` undefined).
  - `11` bibliography entries (`0` duplicates); `17` `\cite` calls covering all `11` distinct keys (`0` undefined, `0` uncited).
- **Pending before release:**
  1. Three `pdflatex` passes and `bibtex`, plus visual PDF inspection for numbering, layout, and overfull boxes.
  2. Commit and pin `HigherOrderTower.lean`, the Phase 23 scripts, and the working-tree `GF-29`/`GF-34` registry entries, and update the working-tree citations in §9.
  3. Owner release steps (`metadata.toml`, `papers/manifest.toml`, `papers/SHA256SUMS`, `docs/registry/papers.toml`).
