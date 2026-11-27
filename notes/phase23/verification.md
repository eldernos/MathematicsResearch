# Phase 23 Verification Record

This file records the reproducible Lean 4 (executed on remote Linux build host `hail`, never WSL), exact-arithmetic Python, documentation-portal, benchmark, and release-integrity checks executed on branch `research/phase-23-higher-order-dense`. **Cross-model review is not independent human peer review; finite digit statistics are finite measurements only.**

## 1. Lean 4 kernel verification (`v4.36.0` on remote Linux server `hail`)

Two new Lean 4 modules (+63 exported theorems) were added, wired into [`NormalityChecker.lean`](../../NormalityChecker.lean), [`Audit.lean`](../../Audit.lean), and [`docs/data/topics.toml`](../../docs/data/topics.toml), and verified on `hail` (`~/math-research-build`):

- [`NormalityChecker/HigherOrderTower.lean`](../../NormalityChecker/HigherOrderTower.lean) — **24 exported theorems** covering the kernel decomposition `K_b = Fix_b + M_b`, de Bruijn Eulerian circuit existence (`exists_euler_circuit`, `exists_balanced_block`), exact higher-order tower characterizations (`tower_iff`, `tower_irrational_exact_iff`, `all_kernel_pow_iff` — `K_{b^k} \ K_b` contains a base-`b` `L`-normal and exact-order-`L` irrational real iff `b^L ∣ k`), the alternating-runs witness `altRuns_orderNormal_one`, and the universal discrepancy upper bound `D^+(x; b) ≤ 2/b^L` (`eventually_radixDiscrepancy_le_of_orderNormal`, `limsup_radixDiscrepancy_le_of_orderNormal`).
- [`NormalityChecker/Phase23Cores.lean`](../../NormalityChecker/Phase23Cores.lean) — **39 exported theorems** covering: (1) Track C4 rational determinant folding (`rat_det_folding_step`, `ratBadness_folding_step`); (2) Track B1 even-radix digit-cylinder identity `1/4 − 1/(2b)` and split-prime local-factor upper bound; (3) Track D3 Mahler binary partition recurrence (`binPart_even`), finite Mahler functional equation (`binPart_mahler_finite`), and signed Thue–Morse product identity (`prod_one_sub_pow_two_pow`); (4) Track B3 carry-cancellation gauge telescoping and exact zero-kernel characterization (`carry_gauge_telescoping`, `carry_kernel_iff`, `carry_kernel_eq_zero_of_tendsto`); (5) Track E `E_+` odd-shift nonpositivity (`erdosBorweinPlusCoeff_mul_add_odd_nonpos`), four-consecutive-zero (`erdosBorweinPlusCoeff_four_consec_eq_zero`), and `j = 1` peeling (`erdosBorweinPlusCoeff_peel_one`); (6) Track A3 `3 ∣ D^j E^3` divisibility (`three_dvd_triNum_pow_mul_odd`) and Track E `ln 2` Glaisher–Wieferich congruence (`glaisher_wieferich_zmod`, `ln2Prefix_num_dvd_iff_wieferich`).

Commands verified on `hail` (all exit `0`, 0 errors, 0 warnings, 0 `sorry`s):

- `lake build` — **8,786** jobs succeeded cleanly.
- `lake env lean Audit.lean` — audited **2,073** public theorem declarations; every declaration uses only `[propext, Classical.choice, Quot.sound]`.
- `lake env lean scripts/test_localized_joint.lean` — passed.
- `lake env leanchecker NormalityChecker.HigherOrderTower` and `NormalityChecker.Phase23Cores` — both independent kernel replays exited `0`.
- `import LeanChecker; #eval replayFromImports \`NormalityChecker` — exited `0`.
- `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean` followed by `NORMALITY_UPDATE_THEOREM_INDEX=0` check — updated `README.md` and `docs/data/declarations.json` to **1,657** named public theorems and lemmas (+63 over Phase 22).

## 2. Exact-arithmetic Python verification scripts

All Phase 23 scripts, the repaired Phase 22 audit scripts, and the regression/benchmark test suites ran cleanly (`exit 0`):

| Script | Checks / Scope | Notes |
| --- | --- | --- |
| [`scripts/test_phase22_corrections.py`](../../scripts/test_phase22_corrections.py) | 4 unit tests | Regression lock for the 4 Phase 22 consolidation corrections |
| [`scripts/test_benchmarks.py`](../../scripts/test_benchmarks.py) | 59 unit tests | Schema v2 permanence, `control_provenance`, cohort/radix consistency |
| [`scripts/phase22_radix_classgroups.py`](../../scripts/phase22_radix_classgroups.py) | 3,151,094 checks | Re-run on `hail` after Audit 1 repairs (exit 0) |
| [`scripts/phase22_partitions_carry.py`](../../scripts/phase22_partitions_carry.py) | 1,256,966 checks | Re-run on `hail` after Audit 1 repairs (exit 0) |
| [`scripts/phase22_short_orbits.py`](../../scripts/phase22_short_orbits.py) | All assertions + 4,097 new even-support checks | Re-run on `hail` after Audit 2 repairs (exit 0) |
| [`scripts/phase22_reciprocals.py`](../../scripts/phase22_reciprocals.py) | 21,443 checks | Re-run on `hail` after Audit 2 repairs (exit 0; exact vs numerical separated) |
| [`scripts/phase23_euler_tower.py`](../../scripts/phase23_euler_tower.py) | All assertions pass | `E_2^2` `1/40000` constants & finite higher-order tower spectra |
| [`scripts/phase23_rational_signed.py`](../../scripts/phase23_rational_signed.py) | 214,603 exact checks | Rational-scaling symmetry, Conjecture 5.5 (`d ≤ 20,000`/`3,000`), `(a/113)E_{10}`, `Θ_3`, `q`-digamma |
| [`scripts/phase23_dense_forms.py`](../../scripts/phase23_dense_forms.py) | All assertions pass | Certified cubic `C_odd` bounds (`4/5`, `21/25`), displaced orbit, 11 non-fundamental discriminants |
| [`scripts/phase23_binary_partition.py`](../../scripts/phase23_binary_partition.py) | 609,971 checks | Mahler `X_b`, Cartier `2`-automaticity mod `2^L`, signed Thue–Morse `Y_b`, gauge/3-state automaton |
| [`scripts/phase23_nonlinear_short_orbits.py`](../../scripts/phase23_nonlinear_short_orbits.py) | All exact checks (1,960 folding cases) | `C_s(2)^2` jumps, multivariate freezing/rows, `μ = 2` height bounds & direct convolutions |
| [`scripts/phase23_reciprocals_v2.py`](../../scripts/phase23_reciprocals_v2.py) | 12,193 exact + 510 float measurements | `+1`-inversion, `D_max = 2/b^L`, `G_{b,M}`, Zsigmondy exceptions, 9 recursive anchored schedules, CRT |
| [`scripts/phase23_classical.py`](../../scripts/phase23_classical.py) | 4,580,653 checks | `E`/`E_+` correlations, Lemma 3.2 (1,038 pairs), `ln 2` BBP band law (661,864 pairs) & Wieferich |

## 3. Repository portal, benchmarks, figures, site and release integrity

Verified after final Phase 23 consolidation (all exit `0`):

- `python -B scripts/figures/build.py` and `python -B scripts/figures/build.py --check`
- `python -B scripts/portal.py build` and `python -B scripts/portal.py check --strict`
- `python -B scripts/check_citation.py`
- `python -B scripts/site.py bib --check` and `python -B scripts/site.py build --strict`
- `python -B papers/check_release.py --require-all --verify-history` (confirming zero modifications to archived releases `manuscripts-v1.0.0`, `manuscripts-v1.1.0`, `manuscripts-v2.0.0`, `papers/manifest.toml`, `papers/SHA256SUMS`, `papers/alphaxiv-records.toml`, or `docs/registry/papers.toml`)
- `python -B -m unittest discover -s scripts -p "test_*.py"` (185+ tests, 0 warnings)
- `NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean` on `hail`

## 4. Cross-provider review status

All Phase 22 deep audits (`GF-21`, `GF-25`, `GF-26`, `GF-27 Theorem S`), all eight Phase 23 tracks (`F-Bench`, `A1–A2`, `A3–A4`, `B1–B2`, `B3+D3`, `C1–C4`, `D1–D2–D4`, `E1–E2`), and the refreshed/new candidate manuscripts passed cross-provider review with **0 Critical** and **0 Major** issues remaining after repairs. **Cross-model review is not independent human peer review.**
