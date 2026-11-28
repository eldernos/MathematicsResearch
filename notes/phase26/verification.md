# Phase 26 Verification Record

This file records the reproducible Lean 4 (executed on remote Linux build host `hail`, never WSL), exact-arithmetic Python, LaTeX (`~/.TinyTeX` on `hail`), documentation-portal, benchmark, and release-integrity checks executed on branch `research/phase-26-arithmetic-amplification`. **Cross-model review is not independent human peer review; finite digit statistics are finite measurements only; conditional results (including external Dirichlet GRH deductions) never change a benchmark status.**

## 1. Lean 4 kernel verification (`v4.36.0` on remote Linux server `hail`)

Two new flagship Lean 4 modules (+147 named public theorems and lemmas; +163 audited public declarations) were added, wired into [`NormalityChecker.lean`](../../NormalityChecker.lean), [`Audit.lean`](../../Audit.lean), and [`docs/data/topics.toml`](../../docs/data/topics.toml), and verified on `hail` (`~/math-research-build`):

- [`NormalityChecker/HankelDeterminants.lean`](../../NormalityChecker/HankelDeterminants.lean) — **1,088 lines, 36 audited flagship declarations** (`NormalityChecker.HankelLogTwo`: `bbpHankel_det_ne_zero`, `bbpHankel_det_padicValRat`, `int_pow_dvd_det_of_rank_le`, `ratMatrix_det_padicValRat_ge_neg_rank`, `bbpHankel_nonEntering_padicValRat_ge_neg_depth`, `two_pow_mul_log_two_eq_logPrefix_add_bbpTail`, `det_le_det_of_quadForm_le`, `tailMatrix_det_bounds`, `bbpHankel_clean_decomposition`, `cleanWindow_det`).
- [`NormalityChecker/ToeplitzDeterminants.lean`](../../NormalityChecker/ToeplitzDeterminants.lean) — **1,810 lines, 43 audited flagship declarations** (`NormalityChecker.ToeplitzDeterminants`: `orbitGram_det_le_pow`, `orbitGram_det_eq_pow_iff`, `orbitGram_two_det`, `posSemidef_det_fromBlocks_le`, `orbitGram_det_le_pow_div`, `orbitGram_det_pow_antitone`, `oneSubAlphaI_add_alphaJ_det`, `det_mul_eq_sum_powersetCard`, `orbitGram_det_eq_cauchy_binet`, `orbitGram_det_pos_of_irrational`, `orbitGram_regularized_posDef`).

Commands verified on `hail` (all exit `0`, 0 errors, 0 warnings, 0 `sorry`s):

- `lake build` — **8,796** jobs succeeded cleanly.
- `lake env lean Audit.lean` — audited **2,470** public theorem declarations (+163 over Phase 25); every declaration uses only `[propext, Classical.choice, Quot.sound]`.
- `lake env lean scripts/test_localized_joint.lean` — passed.
- `lake env leanchecker NormalityChecker.HankelDeterminants` — independent kernel replay exited `0`.
- `lake env leanchecker NormalityChecker.ToeplitzDeterminants` — independent kernel replay exited `0`.
- `import LeanChecker; #eval replayFromImports \`NormalityChecker` — root kernel replay exited `0`.
- `NORMALITY_UPDATE_THEOREM_INDEX=1` and `=0 lake env lean scripts/readme_theorems.lean` — updated `README.md` and `docs/data/declarations.json` to **2,008** named public theorems and lemmas (+147 over Phase 25).

## 2. Exact-arithmetic Python verification scripts

All seven Phase 26 research scripts and all unit tests ran cleanly on Windows (never WSL) with `exit 0` and zero floats in exact assertions:

| Script | Checks / Scope | Notes |
| --- | --- | --- |
| [`scripts/test_phase26_corrections.py`](../../scripts/test_phase26_corrections.py) | Unit test lock for Stage 0.1 corrections | Passes in full `unittest discover` suite |
| [`scripts/phase26_toeplitz_uniformity.py`](../../scripts/phase26_toeplitz_uniformity.py) | 77,250 assertions (`77,052 [exact]` + `198 [finite]`) | Track A (`GF-49`), AST-verified zero floats in exact, post-repair ACCEPT (`0/0/0`) |
| [`scripts/phase26_hankel_ln2.py`](../../scripts/phase26_hankel_ln2.py) | 67,877 assertions (`67,593 [exact]` + `284 [encl]`) | Track B (`GF-50`), zero floats before `[finite]`, ACCEPT (+`358,608` reviewer checks) |
| [`scripts/phase26_mesoscopic_carries.py`](../../scripts/phase26_mesoscopic_carries.py) | 27,325 zero-float checks (`24,497 [exact]` + `2,828 [encl]`, +`3 [finite]`) | Track C (`GF-51`, `GF-52`), AST + runtime type-trap zero-float verified, post-repair ACCEPT (`0` Crit, `0` Maj) |
| [`scripts/phase26_euler_modular.py`](../../scripts/phase26_euler_modular.py) | 44,890 exact assertions | Track D (`GF-53`), zero floats in `check`, post-repair ACCEPT |
| [`scripts/phase26_constructive_spectra.py`](../../scripts/phase26_constructive_spectra.py) | All 39 exact certificate counters | Track E (`GF-54`), zero floats in exact certificates, post-repair ACCEPT (`0/0/0`) |
| [`scripts/phase26_classical_nonlinear.py`](../../scripts/phase26_classical_nonlinear.py) | 179,335 exact assertions (`F1` 109,874; `F2` 8,295; `F3` 22,951; `F4` 38,215) | Track F (`GF-55`), AST-verified zero float literals, post-repair ACCEPT |
| [`scripts/phase26_grh_windows.py`](../../scripts/phase26_grh_windows.py) | 19,101 checks (`18,955 [exact]` + `127` consistency + `19 [finite]`) | Track G (`GF-56`), post-repair ACCEPT |

## 3. Reproducible LaTeX manuscript builds (`~/.TinyTeX` on `hail`)

All three unreleased candidate manuscripts compiled cleanly in two independent clean builds (`SOURCE_DATE_EPOCH=1700000000`, `pdflatex` + `bibtex` + `pdflatex` × 2) with zero errors, zero warnings, zero overfull/underfull boxes, byte-identical two-build PDF SHA-256 digests, and zero `paper.pdf` committed to the repository:

- **Candidate Paper XIV v1.1** ([`papers/14-dense-digit-mass-lambert/`](../../papers/14-dense-digit-mass-lambert/)): 30 pp., 639,991 bytes, `179/179` Lean citations verified (`76` `\leanW` at `04969b91` + `86` `\leanX` at `c06c97dd`), SHA-256 `819fedf564cbed01ef4b29effdef6f79bed7eefbe6ce43305c4df9a5edf1d5f2`.
- **Proposed Paper XV v1.0** ([`papers/15-reciprocal-discrepancy-spectra/`](../../papers/15-reciprocal-discrepancy-spectra/)): 28 pp., SHA-256 `4b4cfeeed99f47464d4de934376878e1460d972663f2b4aabcf0d63a9e5c9c16`.
- **Proposed Paper XVI v1.0** ([`papers/16-computable-badly-approx-normality/`](../../papers/16-computable-badly-approx-normality/)): 25 pp., 694,361 bytes, SHA-256 `cab8dff9c9392fe672c61e9991bf5b55bce8fefbd24d3fa887d30bc5b60d207e`.

## 4. Portal, benchmark, site, citation & release-integrity verification

All repository-wide mechanical validators passed with exit code `0`:
- `python -B scripts/figures/build.py` and `python -B scripts/figures/build.py --check`
- `python -B scripts/portal.py build` and `python -B scripts/portal.py check --strict`
- `python -B scripts/check_citation.py`
- `python -B scripts/site.py bib --check` and `python -B scripts/site.py build --strict`
- `python -B papers/check_release.py --require-all --verify-history`
- `python -B -m unittest discover -s scripts -p "test_*.py"`
- `NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean` on `hail` (confirmed `2,008` named public theorems after `portal.py build`).
