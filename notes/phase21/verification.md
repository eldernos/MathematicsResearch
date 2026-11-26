# Phase 21 Verification Record

This file records the exact verification commands, outcomes, and evidence separation for Phase 21 on branch `research/phase-21-radix-boundaries` (based on Phase 20 commit `be4a1608910b5ece343b0e529b79a712742c2b64`).

## 1. Lean 4 kernel verification (Lean 4.36.0 + Mathlib snapshot in WSL)

All seven new Phase 21 modules (`RadixWidthLaw`, `GeneralMassTransfer`, `AntisymmetricLambert`, `ClassicalBarriers`, `PowerSumPeeling`, `DerivativeTransfer`, `NormalReciprocalCore`) and both audited/repaired Phase 20 modules (`EulerPentagonal`, `ProtectedPole`) were built and verified with:

- `lake build` — **PASS** (8,776 jobs, zero warnings, zero `sorry`s).
- `lake env lean Audit.lean` — **PASS** (1,873 public theorem declarations audited; all use only `[propext, Classical.choice, Quot.sound]`).
- `lake env lean scripts/test_localized_joint.lean` — **PASS**.
- `lake env leanchecker` on every new and modified module (`EulerPentagonal`, `ProtectedPole`, `PowerSumPeeling`, `GeneralMassTransfer`, `AntisymmetricLambert`, `ClassicalBarriers`, `RadixWidthLaw`, `DerivativeTransfer`, `NormalReciprocalCore`) + `#eval replayFromImports \`NormalityChecker` — **PASS**.
- `NORMALITY_UPDATE_THEOREM_INDEX=0 lake env lean scripts/readme_theorems.lean` — **PASS** (**1,471** named public theorems and lemmas synchronized across `README.md` and `docs/data/declarations.json`).

## 2. Exact-arithmetic Python verification scripts

| Script | Tracks | Checks / assertions | Runtime | Status |
| --- | --- | ---: | ---: | --- |
| `python -B scripts/phase21_radix.py` | A1–A4 | 124,989 | ~26–40 s | **EXIT 0** |
| `python -B scripts/phase21_characters_classical.py` | B1–B4, E1–E3 | 374,840 | ~22–33 s | **EXIT 0** |
| `python -B scripts/phase21_nonlinear.py` | C1–C4 | exact assertions | ~6 s | **EXIT 0** |
| `python -B scripts/phase21_euler_reciprocals.py` | D1–D2 | 13,086 | ~6.9 s | **EXIT 0** |
| `python -B scripts/phase21_partitions_modular.py` | D3–D4 | 125,884 | ~5.1 s | **EXIT 0** |

All finite computations test finite identities, inequalities, and small-scale mechanisms; asymptotic theorems rest on the Lean declarations and written proofs cited in each registry entry.

## 3. Independent cross-provider mathematical referee reviews

Every Phase 21 research track (authored by Claude Opus 5.5) was independently audited by Gemini 4 Neon (`thought_level: xhigh`). **Cross-model review is not independent human peer review.**

| Review report | Tracks audited | Initial findings | Post-repair status |
| --- | --- | --- | --- |
| [track-a-review.md](reviews/track-a-review.md) | A1–A4 + `RadixWidthLaw.lean` | 1 Critical, 4 Major, 16 Minor | All repaired; post-repair **ACCEPT** (`A1–A4`) |
| [track-be-review.md](reviews/track-be-review.md) | B1–B4, E1–E3 | 0 Critical, 4 Major, 16 Minor | All repaired; post-repair **ACCEPT** (`B1–B4, E1–E3`) |
| [track-c-review.md](reviews/track-c-review.md) | C1–C4 + GF-11 + `PowerSumPeeling.lean` | 2 Critical, 4 Major, 20 Minor | All repaired; post-repair **ACCEPT** (`C1–C4`) |
| [track-d12-review.md](reviews/track-d12-review.md) | D1–D2 + `NormalReciprocalCore.lean` | 1 Critical, 2 Major, 7 Minor | All repaired; post-repair **ACCEPT** (`D1–D2`) |
| [track-d34-review.md](reviews/track-d34-review.md) | D3–D4 + `DerivativeTransfer.lean` | 0 Critical, 6 Major, 10 Minor | All repaired; post-repair **ACCEPT** (`D3–D4`) |

## 4. Portal, citation, release-integrity, and research-site checks

- `python -B scripts/figures/build.py` — figures up to date.
- `python -B scripts/portal.py build` & `python -B scripts/portal.py check --strict` — **PASS**.
- `python -B scripts/check_citation.py` — **PASS**.
- `python -B scripts/site.py bib --check` & `python -B scripts/site.py build --strict` — **PASS** (26 files including same-directory `paper.pdf` copies, `sitemap.xml`, `robots.txt`, `404.html`).
- `python -B -m unittest discover -s scripts -p 'test_*.py'` — **PASS** (including all 20 tests in `scripts/test_site.py`).
- `python -B papers/check_release.py --require-all --verify-history` — **PASS** (zero modifications to archived manuscripts, `papers/SHA256SUMS`, or `papers/alphaxiv-records.toml`).
- `python -B scripts/check_live.py` — verified all 4 live alphaXiv records match titles and PDF SHA-256 digests; Paper VII CC-BY-4.0 licence warning remains recorded as owner action `O1` in [site-and-alphaxiv-audit.md](site-and-alphaxiv-audit.md).
