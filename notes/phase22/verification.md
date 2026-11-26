# Phase 22 Verification Record

This file records the reproducible Lean 4, exact-arithmetic Python, documentation-portal, and release-integrity checks executed on branch `research/phase-22-digit-frequencies`. **Cross-model review is not independent human peer review; finite digit statistics are finite measurements only.**

## 1. Lean 4 kernel verification (`v4.36.0`)

Three new Lean 4 modules were added, wired into [`NormalityChecker.lean`](../../NormalityChecker.lean), [`Audit.lean`](../../Audit.lean), and [`docs/data/topics.toml`](../../docs/data/topics.toml), and verified in WSL (`~/phase20-build`):

- [`NormalityChecker/SimpleNormalityKernel.lean`](../../NormalityChecker/SimpleNormalityKernel.lean) — 48 public theorems covering finite localization, finite digit dichotomy, non-simple-normality of $K_b$ ($b \ge 3$), non-2-normality of $K_2$, exact oriented-tail transfer, nonnegative sparse simple nonnormality, and the Beatty odd-weight identity.
- [`NormalityChecker/RadixPowerTower.lean`](../../NormalityChecker/RadixPowerTower.lean) — 38 public theorems covering strict kernel inclusion $K_b \subsetneq K_{b^k}$, zero-orbit invariance $M_b = M_{b^k}$, fixed-point quotient isomorphism $\mathrm{Fix}_{b^k}/\mathrm{Fix}_b \cong \mathbb Z/((b^k-1)/(b-1))\mathbb Z$, trivial intersection $\mathrm{Fix}_{b^k} \cap M_b = \mathbb Z$, coprime-rational cylinder stability, and exact multiplicative-order period theorems for both $D(b^m - 1)$ and $D(b^m + 1)$.
- [`NormalityChecker/Phase22Cores.lean`](../../NormalityChecker/Phase22Cores.lean) — 35 public theorems covering real-character divisor-sum nonnegativity, the $\chi_{12}$ square-difference sign law, pentagonal gap balance, nonzero-atom interiority and odd-order Euler automaton complement symmetry, multiplier discrepancy deficit inequalities and total-depth retirement splits, and exact arithmetic coefficient and series identities for $E_+(b) = E(b) - 2E(b^2)$.

Commands verified (all exit `0`, 0 errors, 0 warnings, 0 `sorry`s):

- `lake build` — 8,782 jobs succeeded cleanly.
- `lake env lean Audit.lean` — audited **2,001** public theorem declarations; every declaration uses only `[propext, Classical.choice, Quot.sound]`.
- `lake env lean scripts/test_localized_joint.lean` — passed.
- `lake env leanchecker NormalityChecker.SimpleNormalityKernel`, `NormalityChecker.RadixPowerTower`, `NormalityChecker.Phase22Cores` — all three independent kernel replays exited `0`.
- `import LeanChecker; #eval replayFromImports \`NormalityChecker` — exited `0`.
- `NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean` — updated `README.md` and `docs/data/declarations.json` to **1,594** named public theorems and lemmas (+123 over Phase 21).

## 2. Exact-arithmetic Python verification scripts

All nine Phase 22 scripts and the Phase 21 corrections regression test ran cleanly (`exit 0`, deterministic exact integer/rational arithmetic):

| Script | Exact Assertions / Checks | Runtime | Scope |
| --- | ---: | ---: | --- |
| [`scripts/test_phase21_corrections.py`](../../scripts/test_phase21_corrections.py) | 2 unit tests | < 0.1 s | Regression lock for $K_b \subsetneq K_{b^k}$ and Theorem U scope |
| [`scripts/phase22_simple_normality.py`](../../scripts/phase22_simple_normality.py) | 3,344,335 | ~19.6 s | Finite localization, dichotomy, oriented-tail transfer, prescribed limits |
| [`scripts/phase22_flagship_digits.py`](../../scripts/phase22_flagship_digits.py) | 5,817,206 | ~16.6 s | Flagship word laws, $M \mid 24$, $E_b^2$ sign rule, odd-order signed automata |
| [`scripts/phase22_radix_classgroups.py`](../../scripts/phase22_radix_classgroups.py) | 3,141,166 | ~8.5 s | Even-composite thresholds $\delta_b^*$, Strassmann constants ($\Delta = -23 \dots -327$), $(V_q)$ |
| [`scripts/phase22_characters_quotient.py`](../../scripts/phase22_characters_quotient.py) | 273,017 | ~10.7 s | Cubic mod-7 character densities & splits, $K_{b^k}/K_b$ quotient & $b \mid k$ |
| [`scripts/phase22_nonlinear_boundary.py`](../../scripts/phase22_nonlinear_boundary.py) | All assertions pass | ~5.1 s | $p^{sH} C^r = X_H + Z_H$ split, two-squares jumps, three-cubes density |
| [`scripts/phase22_short_orbits.py`](../../scripts/phase22_short_orbits.py) | All assertions pass | ~6.2 s | Uniform short-orbit constant 9, $A(G)$, exact $\mu = \lambda$ and $\mu = p$ |
| [`scripts/phase22_reciprocals.py`](../../scripts/phase22_reciprocals.py) | 21,443 | ~1.5 s | Exact periods, partial-band Weyl bounds, cyclotomic realizations |
| [`scripts/phase22_partitions_carry.py`](../../scripts/phase22_partitions_carry.py) | 1,256,966 | ~4.9 s | Selberg uniform sieve checks, $P_b(M)$ periods, Mahler carry window, NAF wall |
| [`scripts/phase22_classical.py`](../../scripts/phase22_classical.py) | 301,593 | ~4.3 s | Scale-$2^{64}$ order-6 certificate ($f(1) \ge 0.518826$), $E_+$, Kempner, 5-constant recon |

## 3. Repository portal, benchmarks, figures, site and release integrity

Verified after final Phase 22 consolidation (all exit `0`):

- `python -B scripts/figures/build.py` and `python -B scripts/figures/build.py --check`
- `python -B scripts/portal.py build` and `python -B scripts/portal.py check --strict`
- `python -B scripts/check_citation.py`
- `python -B scripts/site.py bib --check` and `python -B scripts/site.py build --strict`
- `python -B papers/check_release.py --require-all --verify-history` (confirming zero modifications to archived releases `manuscripts-v1.0.0`, `manuscripts-v1.1.0`, `manuscripts-v2.0.0`, `papers/manifest.toml`, `papers/SHA256SUMS`, or `papers/alphaxiv-records.toml`)
- `python -B -m unittest discover -s scripts -p "test_*.py"`
- `NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean`

## 4. Cross-provider review status

All ten research/infrastructure tracks (`F`, `A1–A2`, `A3–A4`, `B1–B2`, `B3–B4`, `C1–C2`, `C3–C4`, `D1–D2`, `D3–D4 + Thm S`, `E1–E3`) passed post-repair cross-provider review with verdict **ACCEPT** (0 Critical flaws across all tracks). Candidate manuscripts **Paper XI** ([`paper-xi-review.md`](reviews/paper-xi-review.md)) and **Paper VII v2.0** ([`paper-vii-v2-review.md`](reviews/paper-vii-v2-review.md)) completed independent cross-provider audits, repairs, and post-repair verification.
