# Wave 2 Audit: Paper III (`papers/03-signed-resonance`, v1.1)

**Date:** 25 November 2026  
**Baseline:** `e4809cf561573aef588e6ffc491a35cdb79fd9ec` (`research-checkpoint-18`)  
**Recommendation:** **Retain `papers/03-signed-resonance` (v1.1) unchanged** in Publication Wave 2.

## 1. Registry and Git History Audit (`CR.toml`, `DS.toml`)

A complete check of `docs/registry/CR.toml` (`CR-01`–`CR-07`), `docs/registry/DS.toml` (`DS-01`–`DS-11`), and the repository history through commit `e4809cf` confirms that **zero new `CR` or `DS` theorems were added during Phases 13–18**. The last commit touching `CR.toml`, `DS.toml`, or `papers/03-signed-resonance/` was `3545d5f` (the `manuscripts-v1.1.0` release itself). Every principal result of Paper III—the cyclotomic classification (`CR-01`), the all-cutoff signed-shell and rational-translation discrepancy laws (`DS-01`, `DS-03`), periodic evaluations (`DS-02`), the suffix-maximal spectrum (`DS-04`, `DS-05`), de Bruijn small-discrepancy translations (`DS-08`), transcendence via Roth/Ridout (`DS-07`), and the every-radix nonnormal sum of two positive normal summands (`CR-03`)—remains mathematically intact and unchanged since v1.1. No errors or scope retractions in Paper III were found in any Phase 13–18 review.

## 2. Assessment of Phase 13–18 Touchpoints

Across `notes/phase13/`–`notes/phase18/`, four items interact with Paper III's topics, all as comparisons or downstream extensions belonging to other Wave 2 manuscripts rather than gaps in Paper III:

1. **Synthetic programmable expansions (Phase 18, `notes/phase18/programming.md`, `SY.toml`).** Cubic rational-prefix programming realizes the full interval $[0,1]$ of ordinary discrepancy limits (at rate $O(N^{-1/3})$) and every nonempty compact connected set of $T_b$-invariant circle measures, contrasting with Paper III's nowhere-dense geometric-shell spectrum $\mathcal{S}_p$. This material forms its own standalone Wave 2 manuscript, Manuscript C (`papers/07-synthetic-expansions/`).
2. **Rauzy determinism converse for signed phases (Phase 18, `notes/phase18/translations.md`, §4).** Combining Paper III's nonzero-shell uniformity and zero-shell concentration yields a short corollary: among Paper III's bounded-phase signed expansions, the Rauzy-deterministic members are precisely the rational ones (eventually zero phases), since any irrational member has subsequential circle limits with entropy $(1-\theta)\log b > 0$ along nonzero-shell endpoints. This observation is naturally housed in Manuscript C's determinism classification rather than requiring a Paper III v2.
3. **Contemporary 2026 Stoneham-sum literature (Phase 18, `notes/phase18/sources.md`).** Captain Sude's `Stoneham-sum-normal` (Sept 2026) is already cited in Paper III v1.1 (`\cite{twosum}`). Mira Cult's 24 Nov 2026 note `stoneham-joint-normality.md` proves joint normality of $L_{p,s}(b)$ across distinct primes $p$ and orders $s \ge 1$; this is orthogonal to Paper III's fixed-prime dilated-component cyclotomic resonance test (`CR-01`) and is already tracked in Manuscript B (`01-stoneham-polynomials-v2`) and Manuscript E (`02-localized-normality-v2`).
4. **Pre-existing non-included items (`DS-11`, `CR-07`).** The paper-only Hausdorff dimension $\dim_H(\mathcal{S}_p) = \log 2 / \log p$ (`DS-11`) and the ordered partial sums of $\ln 2$ (`CR-07`) both predate Phase 13 and were intentionally left out of Paper III v1.1; Phases 13–18 added nothing new to either.

## 3. Conclusion

Retaining `papers/03-signed-resonance` (v1.1) unchanged matches `papers/manifest.toml` (`superseded_by = ""`) and avoids churning an already reviewed, self-contained manuscript. Should the owner later prepare a formatting update for external posting (e.g., applying the standard Wave 2 byline `Christopher Anderson, Independent Researcher` and adding the `metadata.toml`/`VERIFICATION.md`/`LEDGER.md`/`submission/` companion files), that would be a packaging release rather than a mathematical revision driven by Phases 13–18.
