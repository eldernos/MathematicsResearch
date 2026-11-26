# Phase 17 Independent Review and Verification Record

All six Phase 17 research tracks (authored using non-Gemini models: Claude Opus 5.5, Claude Sonnet 5.5, Codex `gpt-6.2-sol`, and Codex `gpt-6.2-astra`) underwent three independent mathematical and computational audits by **Gemini 4 Neon (`xhigh`)**, followed by full remediation, script re-execution, and Lean 4.36.0 kernel verification on Hail.

## 1. Independent audit verdicts and dispositions

| Review batch | Tracks audited | Initial verdict | Dispositions applied |
| --- | --- | --- | --- |
| **Review 1** | Track E ([classical-approximants.md](classical-approximants.md)), Track F ([limitations-and-undecidability.md](limitations-and-undecidability.md), [ComputableNormalityUndecidability.lean](../../NormalityChecker/ComputableNormalityUndecidability.lean)) | Track E: **MINOR REVISIONS**; Track F: **MINOR REVISIONS** | **Track E (all 7 items fixed & script re-verified in 2.0s):** corrected sign error in $e$ run ceiling ($\le N + \log_2 N - \log_2 \log N + O(1)$); fixed 3-part Euler CF bug (pairing $q_n$ with $a_{n+1}$, exact tail enclosure $\alpha_{n+1} + q_{n-1}/q_n$, exact $\ln q_n$, global min $0.386249$ at $n=19$, $q>2^{40}$ min $0.387300$ at $n=31$); moved unproved $T^*/N \to \rho^*/\ln 2$ out of rigorous Thm 7(b) into heuristic Thm 7(c)(iii) and changed `< 0.601` to `< 0.6012`; corrected Vandehey window exponent $\delta = 1/3, 1/4$ (separating from Stoneham discrepancy exponents $1/12, 1/28$); fixed finite-rate $0.3759 < 0.3932$ explanation to accidental gcd cancellation; corrected Bugeaud (2007/2008), Bugeaud–Evertse (2008), Davis (1978/1979 both directions), and Marcovecchio (2009 confirmed) citations; fixed all minor nits ($T_D(\sigma_{i^*} z)$, $14.09$, exact telescoping formula, sheared parallelepiped hypotheses, `log q_odd/N`). **Track F (both items fixed & rebuilt cleanly):** synced note §Lean 4 with [ComputableNormalityUndecidability.lean](../../NormalityChecker/ComputableNormalityUndecidability.lean) and upgraded the Lean module with the full universal s-m-n `Names` digit-oracle theorems (`exists_switchedDigit_index_map`, `no_computable_normality_decider_on_names`, `no_re_normality_recognizer_on_names`, `no_re_nonnormality_recognizer_on_names`). |
| **Review 2** | Track B ([multiplicative-lambert.md](multiplicative-lambert.md)), Track D ([mixed-product-orbits.md](mixed-product-orbits.md)) | Track B: **PASS**; Track D: **PASS** | Zero blocking issues. Applied both minor non-blocking editorial clarifications: tightened $q_0 \ge 2$ to $q_0 \ge 3$ in [multiplicative-lambert.md](multiplicative-lambert.md), and noted the short-block Fourier tolerance $\epsilon(M)$ alongside $\sup_{m_c > M}\Delta_B(\nu_c)$ in the finite-$N$ single-plateau reduction of [mixed-product-orbits.md](mixed-product-orbits.md). |
| **Review 3** | Track A ([dyadic-stoneham-classification.md](dyadic-stoneham-classification.md)), Track C ([erdos-borwein-bias.md](erdos-borwein-bias.md)) | Track A: **MINOR REVISIONS**; Track C: **MINOR REVISIONS** | **Track A (all 7 items fixed):** added missing "linearly independent over $\mathbb Q$" hypothesis to Theorem 8; corrected §A1.8 swap-involution 2-adic explanation; restricted the $2^{-2-[H-s]_+}$ dichotomy lower bound to $b \equiv 1 \pmod 4$ and gave the sharp $2^{-3-[H-s-1]_+}$ bound for $b \equiv 3 \pmod 4, H \ge 2$; fixed odd $y = 2(d - 2^{I+a-1}) + 1$ in Theorem 3 proof so $x \ge 0$ at $d = 2^{I+a} - 1$; synced §A3.1–A3.3 with `jointUniform_of_echelon_degrees` and `descent31_all_words_nonzero` in [Phase17DiscrepancyBounds.lean](../../NormalityChecker/Phase17DiscrepancyBounds.lean) and clarified `--emit-lean` output; fixed all 4 nits. **Track C (all 4 items fixed & script re-verified):** added missing `- flip` to lower bound `term = Iv(prob - flip, prob + errK)` in Theorem 3; added exact outward-rounding `dec_lo`/`dec_hi` formatters and outward-rounded every certified printed bound in Tables 1.2, 3, 4.2, $\mu \le 2.0763285$, and $1/2 - p_* \in [0.0075391, 0.0075498]$; added exact assertions for even $r \le 10$ at $L = 50{,}000$ plus the general analytic positivity proof in Theorem 4; clarified the auxiliary $2^{22}$ block-residual correlation check; fixed all 6 minor wording/notation slips (`556` cells, $|m|$ in Vaaler coefficients, $4.3 \times 10^{-13}$, $\int |f|\,d\rho_1 \approx 5.91$, $k^* = 389$ remark, `carry_sign` comment). |

## 2. Script verification

All six Phase 17 Python verification scripts exit with code `0` under `python -B` (standard library only):

- `scripts/phase17_dyadic_stoneham.py` (default run 36.3 s; `--emit-lean` verified against Lean; `--degree-128` independently verified in 62.4 s: precision 907, 345 leaves, 689 nodes, witness `138241/131072`)
- `scripts/phase17_multiplicative_lambert.py` (0.64 s, 132,096 certified digits each for $\chi_4$ and $p \equiv 1 \pmod 5$)
- `scripts/phase17_erdos_borwein_bias.py` (~13 s after review fixes, all exact rational & interval assertions pass)
- `scripts/phase17_mixed_product_orbits.py` (exact checker passes for $(2,3,5)$, $(2,3,7)$, $(2,3,13)$, $(36,5,7)$, and failing triples)
- `scripts/phase17_classical_approximants.py` (2.0 s after review fixes, all 40 E1/E2 rows, E3 lattice scans, and E4 exact comparisons pass)
- `scripts/phase17_limitations.py` (0.38 s, all digit oracles, switches, and Pairs A & B pass)

## 3. Lean 4.36.0 & repository verification

Verified on Hail against Lean 4.36.0 (`NormalityChecker` root + both new Phase 17 modules):

- `lake build` (zero errors, zero warnings)
- `lake env lean Audit.lean` (1,508 public theorem declarations audited; only `propext`, `Classical.choice`, `Quot.sound`)
- `lake env lean scripts/test_localized_joint.lean` (passed)
- All five paper verification scripts (`papers/01-stoneham-polynomials` through `papers/05-classical-denominators`, unchanged and passing)
- `lake env leanchecker NormalityChecker.Phase17DiscrepancyBounds` and `lake env leanchecker NormalityChecker.ComputableNormalityUndecidability` (replayed cleanly)
- `replayFromImports NormalityChecker` at trust level 0 (replayed cleanly)
- `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean` & `NORMALITY_UPDATE_THEOREM_INDEX=0` check
- `python -B scripts/figures/build.py`, `python -B scripts/portal.py build`, `python -B scripts/portal.py check --strict` (zero errors, zero warnings)
- `python -B -m unittest discover -s scripts -p 'test_*.py'` (all unit tests pass)
