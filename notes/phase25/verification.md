# Phase 25 Verification Record

This file records the reproducible Lean 4 (executed on remote Linux build host `hail`, never WSL), exact-arithmetic Python, documentation-portal, benchmark, and release-integrity checks executed on branch `research/phase-25-carry-correlations`. **Cross-model review is not independent human peer review; finite digit statistics are finite measurements only; conditional results never change a benchmark status.**

## 1. Lean 4 kernel verification (`v4.36.0` on remote Linux server `hail`)

One new flagship Lean 4 module (+110 named public theorems and lemmas; +121 audited public declarations) was added, wired into [`NormalityChecker.lean`](../../NormalityChecker.lean), [`Audit.lean`](../../Audit.lean), and [`docs/data/topics.toml`](../../docs/data/topics.toml), and verified on `hail` (`~/math-research-build`):

- [`NormalityChecker/NafGeometricTransfer.lean`](../../NormalityChecker/NafGeometricTransfer.lean) — **2,034 lines, 39 audited flagship declarations** (`exists_naf`, `nafWeight_eq_signedWeight`, `nafWeight_le_card_support`, `signedWeight_natAbs_le_card_of_signed_sum`, `abs_nafLow_div_lt`, `naf_dyadic_count_le`, `naf_orbit_count_le`, `binary_radixDiscrepancy_eventually_ge_of_nafDensity`, `not_orderNormal_two_four_of_nafDensity`, `not_orderNormal_four_two_of_nafDensity`, `nafDensityLE_of_series`, `erdosBorweinPlusPow_eq_signed_series`, `ePlusMean_le` (`≤ 93694/100000`), `erdosBorweinPlus_two_pow_radixDiscrepancy_eventually_ge`, `erdosBorweinPlus_two_pow_lowerDiscrepancy_pos` (explicit `21/500 = 0.042` eventually for `k ≥ 3`), `erdosBorweinPlus_two_pow_not_orderNormal_four`, `erdosBorweinPlus_two_pow_not_orderNormal_base4_two`, `erdosBorweinPlus_eight_not_orderNormal_four`, `erdosBorweinPlus_eight_not_orderNormal_base4_two`).

Commands verified on `hail` (all exit `0`, 0 errors, 0 warnings, 0 `sorry`s):

- `lake build` — **8,792** jobs succeeded cleanly.
- `lake env lean Audit.lean` — audited **2,307** public theorem declarations (+121 over Phase 24); every declaration uses only `[propext, Classical.choice, Quot.sound]`.
- `lake env lean scripts/test_localized_joint.lean` — passed.
- `lake env leanchecker NormalityChecker.NafGeometricTransfer` — independent kernel replay exited `0`.
- `import LeanChecker; #eval replayFromImports \`NormalityChecker` — exited `0`.
- `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean` followed by `NORMALITY_UPDATE_THEOREM_INDEX=0` check — updated `README.md` and `docs/data/declarations.json` to **1,861** named public theorems and lemmas (+110 over Phase 24).

## 2. Exact-arithmetic Python verification scripts

All nine Phase 25 research/addendum scripts, the refreshed Phase 24 scripts, and the regression/benchmark unit tests ran cleanly (`exit 0`):

| Script | Checks / Scope | Notes |
| --- | --- | --- |
| [`scripts/test_phase24_corrections.py`](../../scripts/test_phase24_corrections.py) | 6 unit tests | Regression lock for the 8 Phase 24 consolidation corrections + `GF-22` additive cyclotomic projection |
| [`scripts/phase24_digit_mass.py`](../../scripts/phase24_digit_mass.py) | 3,095,908 checks | Re-run after Audit A rational endpoint assertions |
| [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py) | 50,284 exact checks | Re-run after Audit A `254305/10000` assertion |
| [`scripts/phase24_partitions_reciprocals.py`](../../scripts/phase24_partitions_reciprocals.py) | 30,586 exact + 136 float | Re-run after Audit B comment/note polishes |
| [`scripts/phase25_e4_carries.py`](../../scripts/phase25_e4_carries.py) | 2,513,921 exact (+ 3 float heuristic) | Track A (`GF-41`), post-repair ACCEPT |
| [`scripts/phase25_lambert_eplus.py`](../../scripts/phase25_lambert_eplus.py) | 186,311 exact, 2,428 encl, 27 finite (188,766 total) | Track B (`GF-42`), zero-float certificates, post-repair ACCEPT |
| [`scripts/phase25_euler_theta.py`](../../scripts/phase25_euler_theta.py) | Pure `int`/`Fraction` certificates | Track C (`GF-43`), Windows & Hail exit 0, ACCEPT WITH MINOR POLISH (applied) |
| [`scripts/phase25_digit_complexity.py`](../../scripts/phase25_digit_complexity.py) | 844 checks (incl. 33,108 rational boundary/periodic cases) | Track D (`GF-44`), post-repair ACCEPT |
| [`scripts/phase25_partitions_reciprocals.py`](../../scripts/phase25_partitions_reciprocals.py) | Pure `int`/`Fraction` certificates | Track E (`GF-45`), Windows & Hail exit 0, ACCEPT WITH MINOR POLISH (applied) |
| [`scripts/phase25_nonlinear_approx.py`](../../scripts/phase25_nonlinear_approx.py) | 810 lifts, 2,322 gap-iff configs, 123 pole-depth & F2 certificates | Track F (`GF-46`), post-repair ACCEPT |
| [`scripts/phase25_classical.py`](../../scripts/phase25_classical.py) | 6,049,844 assertions | Track G (`GF-47`), post-repair ACCEPT |
| [`scripts/phase25_naf_transfer.py`](../../scripts/phase25_naf_transfer.py) | 417,978 exact, 104 encl, 9 finite (418,091 total) | Addendum Track I (`GF-44`), zero floats before §6b, post-repair ACCEPT |
| [`scripts/phase25_grh_windows.py`](../../scripts/phase25_grh_windows.py) | 77,438 exact, 72 cert, 9,044 num (86,554 total) | Addendum Track J (`GF-48`), Windows & Hail exit 0, ACCEPT WITH MINOR POLISH (applied) |

## 3. Portal, benchmark, site, citation & release-integrity verification

All repository-wide mechanical validators passed with exit code `0`:
- `python -B scripts/figures/build.py --check`
- `python -B scripts/portal.py build` and `python -B scripts/portal.py check --strict`
- `python -B scripts/check_citation.py`
- `python -B scripts/site.py bib --check` and `python -B scripts/site.py build --strict`
- `python -B papers/check_release.py --require-all --verify-history`
- `python -B -m unittest discover -s scripts -p "test_*.py"` (including `test_benchmarks.py` and `test_phase24_corrections.py`)
- Candidate Paper XIV structural check (`20/20` bib keys cited, `75/75` `\leanW` links matched to pinned commit `04969b91f0c897ce55d21cb62c6b2c5aa3affe97`; `pdflatex`/`bibtex` unavailable on Windows and `hail`, so PDF compilation remains pending before release).
