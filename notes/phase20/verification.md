# Phase 20 evidence, cross-provider reviews, and reproducibility

Branch `research/phase-20-generating-functions`, starting from commit `22e40fe` (PR #3, recording the four alphaXiv preprints of `manuscripts-v2.0.0`). Every Phase 20 result is labeled strictly by its actual evidence: **Kernel-verified**, **Lean-supported paper proof**, **Paper proof**, **Exact finite certificate**, or **Open**. Cross-provider AI referee audits are internal mathematical quality checks, not external human peer review.

## Independent cross-provider mathematical reviews

All Phase 20 notes, Lean modules, and verification scripts were authored on Claude models (Opus 5.5 / Sonnet 5.5) and audited independently by Gemini 4 models (Argon / Neon):

- **Tracks A1–A4, B5, D1–D4, E1–E3 ([track-ade-review.md](reviews/track-ade-review.md), Gemini 4 Argon):** Verdict **ACCEPT ALL** — 0 Critical, 0 Major, 2 Minor. Both minor items (prose antecedent typo on line 258 of `euler-product.md`; clarifying the schematic Lean signature remark in `theta-and-modular.md`) were fixed directly in the notes.
- **Tracks B1–B4 ([track-b-review.md](reviews/track-b-review.md), Gemini 4 Argon):** Verdict **ACCEPT ALL** — 0 Critical, 0 Major, 8 Minor. All 8 minor polish items (adding factor $e$ in the sufficient condition of Theorem 1.7; clarifying Markov on non-shadowed shifts in Theorem 2.2; clarifying $m_k \ge b^{1/\gamma}$ in counterexample (c); strengthening width control on excluded subsets and replacing $\widehat A_C(2N)$ by $\widehat A_C(N+\lambda_N)$ in Theorem 3.4; adding the $O_B(\lambda_N/N)$ boundary-source term in Theorem 3.6; applying Shiu directly to $2^{V(n)}\mathbf 1_{c(n)>0}$ for the general Phase 17 class in `lambert-leading-constant.md`; syncing Lean status sections with `CoefficientTransfer.lean`; and noting the base-2 vs. odd-radix width distinction) were applied directly to `coefficient-transfer.md` and `lambert-leading-constant.md`.
- **Tracks C1–C3 ([track-c-review.md](reviews/track-c-review.md), Gemini 4 Neon xhigh):** Verdict **ACCEPT** for C1 (`all-prime-polynomials.md` §§1–6), `ProtectedPole.lean`, and `phase20_normality.py`; **REVISE (no fatal obstruction)** for C2b (1 Major quantifier fix: fixed-$r$ period hypothesis only implies degree-$\le r$ nonvanishing and degree-$\le r$ monomial joint UD; full algebraic independence requires the period condition for every $r$) and C3 (`cubic-power-schedule.md`: verified sound analytic core, 3 fixable Major gaps — `C3-M1` $B=0$ rational separation $x=z \implies v'=v \implies k'=k+(H'-H)$ handling $p \le r$ with $H' > H$, `C3-M2` self-contained 6-line all-$r$/all-$\beta \le 1$ proof of exact uniform margin $\sigma_r = \frac{1}{r(2^{r+1}-2)}$, and `C3-M3` explicit dropping of $p \nmid m'$, Titchmarsh 5.13 short-piece/$T=1$/harmonic summation, and 4-line $r$-dimensional box-packing lattice-counting error). All 4 Major findings and all Minor polish items across `all-prime-polynomials.md`, `cubic-power-schedule.md`, and `scripts/phase20_normality.py` were repaired and re-verified (`phase20_normality.py` asserts exact $\sigma_r = 1/(r(2^{r+1}-2))$ for $r=3,\dots,8$).

## Lean 4 formalization & kernel verification

Four new Lean 4 modules were added to `NormalityChecker` (55 new named public theorems and lemmas):

1. [`NormalityChecker/CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean) — linear-mass sparse coefficient transfer (`finite_sparse_mass_transfer`, `finite_sparse_mass_translation`, `linear_mass_sparse_tendsto_one`, `linear_mass_sparse_preserves_discrepancy`), composite-radix displaced factorization (`radixVal`, `radixUnit`, `radixVal_mul_radixUnit`, `not_dvd_radixUnit`, `displaced_term_eq`), and two-sided circle separation (`one_sub_discrepancy_ge_of_bulk_and_far`).
2. [`NormalityChecker/EulerPentagonal.lean`](../../NormalityChecker/EulerPentagonal.lean) — pentagonal and triangular support/mass bounds (`pentagonal_supportCount_le`, `jacobiCube_supportCount_le`, `jacobiCube_absMass_le`, `cauchyConv_absMass_le`), finite gap upper bound (`eulerPentagonal_finite_gap_upper`), and kernel membership & discrepancy preservation for $E_b$ and $E_b^3$ (`eulerPentagonal_discrepancy_tendsto_one`, `eulerPentagonal_preserves_discrepancy`, `eulerCube_discrepancy_tendsto_one`, `eulerCube_preserves_discrepancy`).
3. [`NormalityChecker/CharacterLambertTransfer.lean`](../../NormalityChecker/CharacterLambertTransfer.lean) — radix-power linear discrepancy transfer (`radixDiscrepancy_mul_pow_sub_le`, `radix_pow_linear_transfer`), exact mod-8 character identities (`mod8_character_identities`), finite bounds (`mod8_odd_discrepancy_diff`, `mod8_class_discrepancy_diff`), and asymptotic equivalence (`mod8_asymptotic_equivalence`).
4. [`NormalityChecker/ProtectedPole.lean`](../../NormalityChecker/ProtectedPole.lean) — denominator valuation lemmas (`prime_pow_dvd_rat_den_of_repr`, `not_prime_pow_succ_dvd_rat_den_of_repr`), shifted-prefix auxiliary-prime and protected-prime-power survival (`shifted_prefix_aux_prime_dvd_den`, `shifted_prefix_protected_prime_pow_dvd_den`), and truncated polynomial pole survival (`truncated_poly_pole_dvd_den`).

Verification evidence (executed on Lean 4.36.0 against pinned Mathlib):

- `lake build`: **8,762 jobs succeeded**, zero warnings.
- `lake env lean Audit.lean`: **1,778 public theorem declarations audited**, using only `[propext, Classical.choice, Quot.sound]`.
- `scripts/readme_theorems.lean`: **1,387 named public theorems and lemmas** indexed in `docs/data/declarations.json` and `README.md`.
- `lake env lean scripts/test_localized_joint.lean` and all manuscript `Check.lean` / `check.sh` scripts: **all passed**.
- Independent kernel replay: `lake env leanchecker` passed on all four new modules, and `#eval replayFromImports \`NormalityChecker` passed on the root module.

## Exact-arithmetic scripts, portal, and publication checks

- `python -B scripts/phase20_transfer.py` — exit 0 (~15 s): checks 520 exact `Fraction` inequalities (B1/B2), 1,612 prefix checks for Theorem 1.5, Proposition 1.6 sharpness tables, 1,875 composite-radix reindexing shifts, counterexamples (a)–(c), certified 40-bit discrepancies & Lemma 3.3 lower bounds (B3), and $N = 2^{18}$ measurements for $L_{\chi_4}$, $\Theta_3(1/2)^2$, and $L_{\chi_{-3}}$ (B4).
- `python -B scripts/phase20_euler_theta.py` — exit 0 (~157 s): 534,917 exact assertions covering $E_b, E_b^2, E_b^3$, word counts, rational scalings, $\eta(12\tau)^2$ through $1.57 \times 10^6$, binary theta forms $\Theta_Q(1/b)$, weight-1 forms, and $\eta^{2r}$ overlap diagnostics.
- `python -B scripts/phase20_dense_classical.py` — exit 0 (~2 s): exact checks for carry-window transfers, $P_b = 1/E_b$ diagnostics, $\Theta^4$/$\Theta^3$ transfers, squaring/reciprocal counterexamples, mod-8/mod-24 identities, and Möbius collapse.
- `python -B scripts/phase20_normality.py` — exit 0 (~70 s): exact checks for Track C1–C3 denominator profiles, protected-pole dominance, and level-set diagnostics.
- Portal, site, citation, and release integrity checks: `scripts/figures/build.py`, `scripts/portal.py check --strict`, `scripts/check_citation.py`, `scripts/site.py bib --check`, `scripts/site.py build --strict`, `papers/check_release.py --require-all --verify-history`, and `unittest` suite (114 tests).

## Reproduce

```sh
bash scripts/verify.sh
python3 -B scripts/phase20_transfer.py
python3 -B scripts/phase20_euler_theta.py
python3 -B scripts/phase20_dense_classical.py
python3 -B scripts/phase20_normality.py
python3 -B papers/check_release.py --require-all --verify-history
```

Finite computations certify only the stated finite runs and never establish asymptotic normality, non-normality, or historical priority.
