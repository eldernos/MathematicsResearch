# Verification map: All-Prime Polynomial Normality and Optimal Irrationality Exponents (v1.0, candidate draft)

This file maps every numbered statement of the candidate draft to one evidence label: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **External input** or **Finite certificate**. Nothing in this paper is kernel-verified as a whole. A Lean-supported label means only that the named finite step is a Lean declaration. Every exponential-sum estimate, every normality conclusion, every rate and every Diophantine statement here is a written proof. Finite computations quoted as illustrations are finite measurements, not evidence for asymptotic statements.

**Cross-model review is not independent human peer review.** The written proofs, and the repository notes they come from, have been checked only by AI models from different providers. No human specialist has read them, and the assembled manuscript has not been reviewed as a whole.

**Status.** This is an unreleased candidate draft. It has no entry in `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml` or `docs/registry/papers.toml`, and no `paper.pdf`, `metadata.toml` or `submission/` directory. **PDF compilation with `pdflatex` and `bibtex` is still pending before release.** Neither tool is installed on the local Windows host or on the Linux build server `hail`, so the draft has not been typeset. Only the structural check below has been run. The companion is Paper VII v2.0 ([`../07-synthetic-expansions-v2/`](../07-synthetic-expansions-v2/)), also a candidate draft. Section 9 of that draft was moved here.

## Pinned commits

- **P** = `c2c9da683666b3b9368e5d4b5cb858caccf528f5` (Phase 19): `SurvivingGrid`, `PrimePowerGrid`.
- **R** = `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8` (Phase 21): `ProtectedPole`.

Build records at these commits are as in the [Paper VII v2.0 map](../07-synthetic-expansions-v2/VERIFICATION.md): Lean 4.36.0, `lake build` with zero warnings and zero `sorry`, an axiom audit accepting only `propext`, `Classical.choice` and `Quot.sound`, and a `leanchecker` replay of `ProtectedPole`. This draft did not rerun `lake build`, and it states no new Lean declaration.

## Exact scope of the Lean declarations used

| Declaration | Commit, line | What it states | What it does **not** state |
| --- | --- | --- | --- |
| `SurvivingGrid.stride_order` | P L43 | The order of $g$ modulo $p^eQ$ is $p^{e-v_p(g-1)}$ when $p$ is odd, $p\nmid Q$, $p\mid g-1$, $Q\mid g-1$. | The arc count for arbitrary lengths (Lemma 2.3) is written. |
| `PrimePowerGrid.crt_period_count` | P L337 | The count over one stretch of length $\tau p^{e-c}$. | The passage to arbitrary $L$ is written. |
| `ProtectedPole.shifted_prefix_protected_prime_pow_dvd_den` | R L245 | For $U_k=\sum_{j\le k}1/(p^{e_j}\ell_jb^{n_j})$ with $e_j<e_k$ ($j<k$) and $n_j\le N$: $p^{e_k}$ exactly divides the reduced denominator of $b^NU_k$. | Nothing about polynomials in $W$. |
| `ProtectedPole.shifted_prefix_aux_prime_dvd_den` | R L143 | The newest prime $\ell_k$ divides the reduced denominator of $b^NU_k$. | Only the newest prime. Persistence of the earlier $\ell_i$ and the exact formula $p^{k^2}\ell_1\cdots\ell_k$ are written. |
| `ProtectedPole.truncated_poly_pole_dvd_den` | R L347 | A lower bound $p^{le_2+(r-l)e_1-g}\mid\den F_l(U,V)$. | Not the exact valuation of Lemma 4.1, and not a statement about the shifted prefixes of $P(W)$; the window rule is written. |

## Statement map

Statement numbers come from a structural count of `paper.tex`: sections, and the shared theorem counter per section. They will be confirmed when the PDF is compiled.

| No. | Statement (short) | Evidence | Lean | External inputs | Source note and finite checks |
| --- | --- | --- | --- | --- | --- |
| A | Universal Liouville $W$: exact denominators, every $P(W)$ normal and Liouville, rate $\exp(-c(\log N)^{2/3})$ | Lean-supported paper proof (= 4.2) | see 4.1, 4.2 | Chebyshev; $\prod_{\ell\le x}\ell<4^x$ | see 4.2 |
| B | Polynomial schedules with growing auxiliary support, several orders | Paper proof (= 5.3), quoting 5.1–5.2 | — | see 5.2, 3.3 | see 5.3 |
| C | (i) $\mu(W_G)=\lambda$, degree $\le r$; (ii) $\mu(W_S)=p$, all degrees | Paper proof (= 6.2, 6.4) | — | see 6.2, 6.4 | see 6.2, 6.4 |
| D | Limit of truncation separation; $(3+\sqrt5)/2$ ceiling | Paper proof (= 6.1) | — | — | see 6.1 |
| E | Exponent two in all degrees: $W$, $W'$, $V$ | Paper proof (= 7.3, 7.4) | — | Dirichlet's theorem | see 7.3, 7.4 |
| 2.1 | Arcs and finite comparison | Paper proof | — | — | — |
| 2.2 | Block certificate | Paper proof | — | — | — |
| 2.3 | Grids | Lean-supported paper proof | `stride_order` (P L43), `crt_period_count` (P L337) | — | — |
| 3.1 | Uniform short orbits (Lemma A of GF-25), with the sharpness example $\lvert S\rvert/M>0.983$ | Paper proof | — | — | [`short-orbits-and-irrationality.md`](../../notes/phase22/short-orbits-and-irrationality.md) §1; `scripts/phase22_short_orbits.py`: LTE in 31,840 cases, complete-orbit vanishing in 41 cases, the stride identity, and the sharpness example (the complex sums and the sine bound are floating-point checks) |
| 3.2 | Splitting off a coprime modulus (Corollary B); standing bound $v_p(\ord_{M'}b)\le\log_pM'$ via the weak inequality $\ord_{M'}b\le M'$ | Paper proof | — | — | same note §2; same script: CRT factorization on 53 Theorem H prefixes, identity on all 243 divisors |
| 3.3 | Largest auxiliary prime (Lemma D), with $1+\omega(b)$ excluded primes | Paper proof | — | divisor bound (Hardy–Wright Thm 317); prime number theorem | same note §2 (as repaired in Audit 2) |
| 3.4 | $\log\lcm_{\ell\le x}(\ell-1)\ll x\log\log x/\log x$ | Paper proof using an **External input** | — | Selberg upper-bound sieve (Halberstam–Richert) | same note §4 |
| 3.5 | Exact auxiliary orders: $\lcm(O_\Lambda,E)$ for odd $\Lambda$; exact 2-adic order $2^{e_2(b,r)}$ for even $\Lambda$; $\ord_{16}(7)=2$ | Paper proof | — | — | [`nonlinear-multivariate-and-denser-mu.md`](../../notes/phase23/nonlinear-multivariate-and-denser-mu.md) §4 (odd case); GF-25 note §4 as repaired in Audit 2 (even case); `phase22_short_orbits.py` `even_support_orders()`: 2,985 local order comparisons and 1,112 mixed-support cases; `scripts/phase23_nonlinear_short_orbits.py` checks the order factorization with overlapping factors, including the prime 2 |
| 4.1 | Pole dominance | Lean-supported paper proof | `truncated_poly_pole_dvd_den` (R L347), a lower bound only | — | [`all-prime-polynomials.md`](../../notes/phase20/all-prime-polynomials.md); `scripts/phase20_normality.py` (exact pole formula at 222 prefixes) |
| 4.2 | Universal all-prime $W$ (GF-10) | Lean-supported paper proof | R L245, R L143 (newest prime only), R L347, P L43 | Chebyshev; prime product bound | `phase20_normality.py` (270 prefixes, five radix/prime pairs, $q_n=p^{k^2}\ell_1\cdots\ell_k$) |
| 4.3 | General protected poles | Lean-supported paper proof | as 4.1 | — | `phase20_normality.py` |
| 4.4 | Denser all-prime schedules (GF-15 part 1) | Paper proof | — | prime number theorem; 3.4 | — |
| 4.5 (Remark) | Several generators (not used) | Remark | — | — | `phase20_normality.py` |
| 5.1 | Freezing with $J\ge\max(L,\lceil L/s_1\rceil+\lceil L/d\rceil)$ | Paper proof, quoted from Paper VII v2.0 (Lemma 7.10 and the proof of Theorem 7.20) | — | — | Phase 23 Track C3 fixture $L=2$, $J=1$, $u=1$ in `phase23_nonlinear_short_orbits.py` |
| 5.2 | Weighted small balls | Paper proof, quoted from Paper VII v2.0 (Theorem 7.18 is a Lean-supported paper proof there for one order; the several-order estimate lies inside the proof of Theorem 7.24, through Lemma 7.23) | — | Titchmarsh Thm 5.13; Erdős–Turán (both inside Paper VII) | Phase 23 Track C3, note §3 |
| 5.3 | All-prime polynomial schedules in several orders under the order budget of Theorem B; one order is Theorem H′ of GF-25 | Paper proof | — | Erdős–Turán (KN Ch. 2 Thm 2.5); 3.3 | GF-25 note §4 (H′); Phase 23 note §4 (hybrid extension); `phase21_nonlinear.py` (exact denominators); `phase22_short_orbits.py` (CRT split on prefixes) |
| 5.4 | Truncation separation | Paper proof | — | — | GF-25 note §5 |
| 5.5 | Ratio-one schedules: only $Q^{-\psi(Q)}$; **finiteness of the exponent is Open** | Paper proof (the open question is Question 8.1) | — | — | `phase22_short_orbits.py` ($\rho_k$ table) |
| 5.6 (Remark) | Quasi-polynomial schedule, recorded **without proof** | Remark (not a claim of this paper) | — | Phase 19 plateau estimate (not reproduced) | — |
| 6.1 | Truncation certificates: the gap criterion and the $(3+\sqrt5)/2$ ceiling (Proposition 4 of Track C4) | Paper proof | — | — | Phase 23 note §5 |
| 6.2 | Geometric schedules, $\mu(W_G)=\lambda$ (Theorem G of GF-25, with $p>(r+1)!$, $\lambda\ge r+1$, $(\mathrm P_G)$) | Paper proof | — | Roth's theorem (transcendence only) | `phase22_short_orbits.py`: exact valuation at 145 insertion positions, exact $\den U_k$, 724 convergents (finite measurement) |
| 6.3 (Remark) | Real ratios $\lambda$ | Remark | — | — | GF-25 note §6 remark (a) |
| 6.4 | Stoneham schedule, $\mu(W_S)=p$ (Theorem S of GF-25) | Paper proof using an **External input** | — | Paper I v2.0, Lemmas 2.2–2.4, which are paper proofs there | `phase22_short_orbits.py`: depth defects for $d=2,\dots,5$; congruence with $\alpha_{2,3}$ modulo $3^l$ at 42 and 121 positions |
| 7.1 | Determinant estimate (Lemma 5 of Track C4) | Paper proof | — | — | Phase 23 note §6; `phase23_nonlinear_short_orbits.py`: 1,960 signed corrections, including $q=1$, against complete minimization; **finite certificate** of the inequality on that range only |
| 7.2 | Anchored upper sets | Paper proof | — | Dickson's lemma | Phase 23 note §7; same script: 251 antichains at $p=3,5$ |
| 7.3 | Doubling and clustered series $W$, $W'$: all-prime, $\mu=2$, all degrees normal (Theorem 6) | Paper proof | — | Dirichlet's theorem | Phase 23 note §7; same script: exact prefix denominators, explicit $z_k$ height bounds, maximum partial quotients, direct convolutions against reflected residues |
| 7.4 | Positive series $V$, $n_j\asymp j\sqrt{\log j}$, $\mu(V)=2$ (Theorem 7) | Paper proof | — | Dirichlet's theorem | Phase 23 note §8; same script: regrouping, normalized units, $z_k$ heights, convolutions $\widetilde V^2$ and $\widetilde V^3$, every displayed prefix denominator through shift 1023 in three radices |
| 8.1–8.4 | Questions | **Open** | — | — | — |

Registry correspondence: [GF-10](../../docs/results.md#gf-10) (Theorem 4.2, Remark 4.5); [GF-15](../../docs/results.md#gf-15) (Corollary 4.4; Theorem 5.3 for one order in the range $d>r(s+1)$); [GF-25](../../docs/results.md#gf-25) (Lemma 3.1, Corollary 3.2, Lemma 3.3, Theorem 5.3 for one order, Lemma 5.4, Proposition 5.5, Theorems 6.2 and 6.4). The Phase 23 Track C3–C4 material (Lemma 3.5 for odd $\Lambda$, Theorem 5.3 in several orders, Proposition 6.1, Lemmas 7.1–7.2, Theorems 7.3–7.4) comes from [`notes/phase23/nonlinear-multivariate-and-denser-mu.md`](../../notes/phase23/nonlinear-multivariate-and-denser-mu.md). That note has **no registry entry yet**. The GF-25 registry title calls Theorems 6.2 and 6.4 the first explicit non-Liouville all-prime polynomial normal numbers; this manuscript does **not** adopt that priority claim (see [LEDGER.md](LEDGER.md)).

## Sources and model reviews

| Material | Source note | Model review (not human peer review) |
| --- | --- | --- |
| 3.1–3.4, 5.3 (one order), 5.4–5.5, 6.2–6.4, 3.5 (even case) | [`notes/phase22/short-orbits-and-irrationality.md`](../../notes/phase22/short-orbits-and-irrationality.md) (GF-25) | [Phase 22 Track C3–C4](../../notes/phase22/reviews/track-c34-review.md), then [Phase 23 Audit 2](../../notes/phase23/reviews/phase22-analytic-audit-shortorbits-reciprocals.md): **SOUND / ACCEPT** after repair. The repairs carried into this draft are the sharpness constant $0.983$ from the exact geometric sum, $1+\omega(b)$ in Lemma 3.3, the weak inequality $\ord_{M'}b\le M'$, the run conventions (split at $\lceil\sqrt N\rceil$, trim $\lceil2\log_bN\rceil$), and the exact 2-adic order replacing the false bound $\frac12\Lambda^{r-1}$. |
| 3.5 (odd case), 5.1–5.3 (several orders), 6.1, 7.1–7.4 | [`notes/phase23/nonlinear-multivariate-and-denser-mu.md`](../../notes/phase23/nonlinear-multivariate-and-denser-mu.md) §§3–8 | [Phase 23 Track C](../../notes/phase23/reviews/track-c-review.md): 0 Critical, 1 Major (on C1, not used here), 13 Minor; post-repair **ACCEPT** for C3 and C4 |
| 4.1–4.5 | [`notes/phase20/all-prime-polynomials.md`](../../notes/phase20/all-prime-polynomials.md), [`notes/phase21/multivariate-and-dense-allprime.md`](../../notes/phase21/multivariate-and-dense-allprime.md) §5 | Phase 20 and Phase 21 Track C reviews (as recorded in the Paper VII v2.0 map) |

Changes made in writing the manuscript, relative to the sources:

1. Theorem 5.3 combines Theorem H′ of GF-25 with the several-order hybrid extension of Track C3 into one statement.
2. Lemma 3.5 combines the odd-support order formula of Track C3 with the corrected even-support formula of Audit 2.
3. Remark 5.6 (quasi-polynomial schedule) says "is expected to give". It records an argument that is not reproduced here and is not claimed.
4. Process language was removed.

No statement was strengthened beyond its source.

## Exact checks run for this draft (27 November 2026)

From the repository root, native Windows Python 3.13 with bytecode disabled (the `hail` build server was not needed for these pure-Python checks):

| Command | Exit | Output summary |
| --- | --- | --- |
| `python -B scripts/phase22_short_orbits.py` | 0 | "All Phase 22 C3-C4 checks passed." 31,840 LTE cases; 41 complete orbits; 243 divisors; even-support orders (1,112 mixed cases, smallest ratio $1/8$); 145 G insertion positions; 724 convergents; 42 and 121 Stoneham congruences |
| `python -B scripts/phase23_nonlinear_short_orbits.py` | 0 | "All exact checks passed." 1,960 determinant-lemma corrections; 251 antichains; doubling and clustered endpoint denominators; dense-schedule regrouping in 3 radices |

**Repository state of the scripts.** `scripts/phase22_short_orbits.py` is tracked, but its Audit 2 repair (`even_support_orders()`) is an uncommitted working-tree change. `scripts/phase23_nonlinear_short_orbits.py` is untracked. **Both must be committed before release**; the manuscript names them without pinned links for this reason. `scripts/phase20_normality.py` and `scripts/phase21_nonlinear.py` are linked at commit R and were not rerun; their earlier records stand.

## Manuscript checks run for this draft

- **Structural check** (scratch Python script, 27 November 2026) of `paper.tex` against `references.bib`. **PASS.**
  - `\begin`/`\end` environments match; braces are balanced in both files; inline `$` is balanced in every paragraph.
  - All 46 labels are distinct. Every one of the 35 distinct `\ref`/`\cref`/`\Cref`/`\eqref` targets is defined.
  - Every one of the 21 `\cite` keys is in `references.bib`. All 21 bibliography entries are cited, and there are no duplicate keys.
  - Every control sequence used is standard LaTeX/AMS or is defined in `../common/preamble.tex` or the paper preamble.
- **Pending before release.**
  - Three `pdflatex` passes and `bibtex`, then visual inspection of the PDF: numbering, overfull boxes, and resolution of the cross-references to Paper VII v2.0 (Lemma 7.10, Theorems 7.18, 7.20, 7.24, Lemma 7.23).
  - Commit the two scripts.
  - Register the Phase 23 Track C material.
  - Add metadata, manifest and release entries. These are owner steps.
