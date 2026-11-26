# Changes relative to version 1.1

Version 2.0 supersedes `papers/02-localized-normality` (version 1.1, immutable archive, Lean pinned at `a09e011720bc`). This version pins Lean at `e4809cf561573aef588e6ffc491a35cdb79fd9ec`.

## Revision after referee report 1 (25 November 2026)

Response to `papers/reviews/02-localized-normality-v2/review-1.md` (AI model review; not independent human peer review); the item-by-item account is in `papers/reviews/02-localized-normality-v2/resolution.md`. The version number remains 2.0 (the manuscript has not been released). Changes to `paper.tex`:

- **Abstract and public abstracts** (also `metadata.toml`, `submission/abstract.txt`, `alphaxiv.md`, `summary.md`, `announcement.md`): the hypotheses are restored (an off-radix prime for the joint statement and for the dichotomy, "over all of M(S)" for the polynomial classification, the pole and the retained-power windows for the window bound, a selected prime in J for the common depth), and the public work of Captain Sude, Mira and Mira Cult is credited with the scope of the extension.
- **Section 1.1:** Theorem B is split into parts (i)-(iii) with the integral clause parenthesized and the quantifier over the restriction placed before the integer `L`; Theorem D carries the cancellation identity (displayed equation (2)); Theorem E and Theorem F state their exact Lean declarations; Theorem F is stated for the sum over the integers `q^a p^j`.
- **Section 1.2 (related work):** rewritten to separate what the sources state from what follows from their proofs (least prime off the radix, binary with 3 at all orders, two generators at higher orders, singleton supports with polynomial numerators, periodic common masks on the axis, Kano and Vandehey on the axis); the "do not state" list is replaced by a list of the remaining contribution. Corrections of detail: Sude's Stoneham criterion for arbitrary `c`; the functional equation; the xi-family Theorem 2 and Lemma 4.
- **Section 5:** the proof of the lower bound is split into the cases `r >= s` and `J` empty (in the latter the weight need not be integral, and old radix shifts clear the denominators), and gives `L = D_0` independently of the restriction.
- **Section 6:** Remark 6.2 relabelled as a Lean-supported paper proof; evidence of Theorem D made precise.
- **Section 7:** wording of the step from uniform distribution to box frequencies corrected.
- **Section 9 (rate):** the outline now states the correct unique-maximum argument (the inserted term with the largest layer), the Dirichlet and integer-separation mesh with depth `M q^2 p^M`, the block structure on the `K^6` scale and the passage to `1/log log N`; the separate "Paper proof" label is removed.
- **Section 10:** the unsupported reference to repository notes is removed (moved to `VERIFICATION.md`).
- **Section 11 (new numbering):** the former Appendix A is now an ordinary section before the formal-verification and AI-use sections, so that those two end the paper. Theorem A.1 is now Theorem 11.1 and Example A.2 is now Example 11.2 (with the four kernel facts separated from the remaining arithmetic, now in `check_order_two.py`); the former Section 11 is Section 12. Pointers to the proofs in version 1.1 are explicit.
- **Section 12:** the verification paragraph states exactly what `Statements.lean` and `Check.lean` restate, that these files are run from the release (the bare checkpoint omits them), and the new behaviour of `AuditDeclarations.lean`.
- **Bibliography:** the pinned URLs of the public sources are printed (notes), and the Vandehey entry gives arXiv:1606.07911v1 for the numbering used.
- **Other files:** `AuditDeclarations.lean` fails on a missing declaration or an unexpected axiom and now also audits `value_eq_series` and `series_normal`; `check_order_two.py` is new; `VERIFICATION.md`, `LEDGER.md` and the submission packet are updated to match.

## Mathematical content

| Version 1.1 | Version 2.0 | Change |
| --- | --- | --- |
| Theorem 1.1 (unsigned) | Theorem A | Unchanged statement. Declaration lines updated (`UnsignedNormality.lean` lines 191 and 198 at the new pin; `unsigned_certificate_tendsTo_zero` at line 169). |
| Theorem 1.2 (rational polynomial weights) | Theorem B | Statement made to match the kernel statement: the lower bound is `liminf D_N >= 1/L` for an integer `L` coprime to `b`, with the identification `L = D_0` kept as a written remark. Added the integral case `D_N -> 1` on every restriction as a stated part. |
| Corollary 1.3 (distinct orders on one support), a written deduction | Theorem C(i) | **Promoted to a kernel-verified theorem** (`joint_full_polynomial_orders`, unsigned case `joint_full_orders`, `distinct_orders_checked`) and extended to rational numerators with `P_i(0) != 0`. Mathlib-only statement of the polynomial version added to `Statements.lean`/`Check.lean`. |
| (not present) | Theorem C(ii),(iii) | New: joint uniformity on one prime-power axis iff the common mask is unbounded; joint uniformity for odd radix with all late powers of 2 retained. Kernel-verified. |
| Theorem 5.1 (retained prime powers) and Corollary 5.2 (window densities) | Theorem D, Corollary 6.1, Remark 6.2 | Restated with the Lean forms (`rational_window_bound`, `rational_pole_bound`, `bounded_gap_discrepancy`, `late_powers_discrepancy`, `normal_of_late_twos`, `axis_normal_iff`). The window-density formula is now credited to `exact_window_density`/`periodic_mask_price`. The remark on quotient weights is kept as a remark with its Lean reference. |
| (not present) | Theorem E | New: a computable common certificate depth for a positive tolerance and finitely many orders (kernel-verified), with a finite example. Stated as concerning certificates only; Proposition 7.2 shows that no cutoff in `N` is uniform over masks. |
| (not present) | Theorem F | New: rate `A/log log N` for two-generator supports `q | b`, `p` odd prime not dividing `b` (kernel-verified; proof outline only). |
| (not present) | Proposition 6.3 | New: order-one signed periodic weights on one prime-power axis, cycle test (kernel-verified). It overlaps a public archive of Mira (see below). |
| Lemma 2.1, Theorem 4.1 (nullity), Section 6 and Proposition 6.1 (finite termination) | Lemma 2.1, Theorem 4.1, Section 10 and Proposition 10.1 | Proofs kept, minor edits. Rechecked line by line in the preparation of this version. The statement of Lemma 3.1 now separates the kernel-supported inequality from the written valuation step. The phrase "on one support the powers `p^s, q^s` cannot lie in one divisibility chain" was replaced by a method note on equal-valuation separation. |
| Appendix A (exact joint failure and prefix discrepancy; Lemma on the integral principal-unit expansion; Corollary on attainable logarithmic phases) | Appendix A, Theorem A.1, Example A.2 | The statements of the exact formula, the second limit and the logarithmic-flow maximum are kept as one kernel-verified theorem. **The written proofs and the principal-unit identity lemma are no longer reproduced** (they remain in the archived version 1.1); the order-two example is kept. |
| Appendix B (formal statements and reproducibility) | Section 11 | Rewritten with the new evidence labels, a table at the new pin, and the new `Statements.lean`/`Check.lean`/`AuditDeclarations.lean`. |

## Evidence labels
Every theorem now carries one of the contract labels. Version 1.1's statement that Corollary 1.3 is "a paper deduction from the verified polynomial classification" is replaced by the kernel statement.

## Credit and priority corrections
- Added, with precise scope: Sude's `xi-family` (10-11 September 2026), whose Theorem 1 already gives order-one normality on every two-prime support with an off-radix prime. Version 1.1 stated that Theorem 1.1 "also covers mixed supports" without citing this; the introduction now says so and limits the new content to the cases listed in Section 1.2(a)-(f).
- Added Sude's `stoneham-prime-support` (axis criterion for composite `c`), Mira Cult's note of 24 November 2026 (Theorems 1-3), Mira's note S07/T29 (full-axis criterion) and Mira's second archive (7 October 2026; periodic arrays on one axis, rank conditions for joint normality), and Bourgain's estimate as a context citation.
- Version 1.1 cited Mira's notes as "Mira" with a pinned gist; Mira Cult's later note says it consolidates the same arguments. Both are credited, and the relation between the two accounts is reported only as the note states it.
- Version 1.1's description of Sude's Theorem 5.1 is kept (it was accurate at the pinned revision), together with the new statement that `xi-normality` Theorem 4.1 has a stronger rate for `{2,3}`.
- Priority language throughout is "we have not located"; the introduction now states that no specialist has reviewed the comparisons.

## Withheld or not carried over
- LS-05 (rational polynomial weights on two-generator supports with composite generators), MW-04, MW-05, MW-06 (dense and periodic weights on power intervals): not part of the prime-support classification; not reviewed for this version.
- LS-06, LS-07 (finite termination on two-prime supports and at large order): written arguments with a `p`-adic Subspace Theorem as external input. Not rechecked for this manuscript; mentioned in Section 10 as not included.
- MW-09 (finite sets of denominator primes of rational weights): a statement about coefficient denominators with no normality conclusion.
- `notes/phase13/quantitative-normality.md` and `independent-axes.md`: concern Stoneham polynomials and products (Paper I). Their rates and denominator transfer do not apply to localized sums of more than one prime, because the localized denominators can lose layers on sets of positive but vanishing measure. The introduction records this as a limitation; Theorem F and the cited rates for singleton supports are the only rates stated.
- `notes/logarithm-correlations.md`, `log-shadow-primes.md`, `strided-logarithm.md`: concern `ln 2` itself, not finite supports.
- Phase 19 material (`classical.md`, `literature.md` at `c2c9da683666`): read only on the owner's instruction; the Bourgain citation was taken from `literature.md` and rechecked against Crossref and Vandehey's Theorem 2.5. Nothing from `classical.md` bears on localized sums (the paragraph on `p^{as} | Q_n` concerns truncations of classical polylogarithm constants). Lean is not pinned to the Phase 19 commit because no Phase 19 declaration is used.

## Moved to another manuscript
Nothing was moved.

## Housekeeping
Preamble and byline are the shared `papers/common` files; author information is the placeholder macro. `metadata.toml` records the author name and affiliation approved by the owner. Figure unchanged (copied).
