# Independent Cross-Provider Audit: Phase 23 Track F-Bench (Benchmark Schema v2)

- **Reviewer**: Independent cross-provider audit sub-agent (Gemini 4 Neon)
- **Date**: 2026-11-27
- **Active worktree**: `C:\Users\chaos\.t3\worktrees\MathematicsResearch\research-phase-20-gener-b08235755636abff`
- **Files audited (read-only)**:
  1. [docs/benchmarks/SCHEMA.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md)
  2. [docs/benchmarks/classical-constants.toml](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml)
  3. [docs/benchmarks/arithmetic-families.toml](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml)
  4. [docs/benchmarks/progress.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md)
  5. [scripts/portal.py](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py) (benchmark validation & generation code, lines 601–1169)
  6. [scripts/test_benchmarks.py](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/test_benchmarks.py)
- **Cross-checked against**: `HEAD` (`0342f1f`) via `git show`, `docs/registry/ST.toml`, `docs/registry/GF.toml`, `docs/registry/CC.toml`, `docs/research-objectives.md`, `notes/phase22/reviews/track-f-review.md`, and published literature (Bailey–Borwein–Crandall–Pomerance 2004, Theorem 9.4).
- **Notice on review status**: **Cross-model review is not independent human peer review.** This report records an automated cross-provider audit and does not substitute for refereeing by independent human mathematicians.

---

## Overall Verdict: **ACCEPT AFTER REVISION**

The data migration to Benchmark Schema v2 is disciplined, conservative, and mathematically sound: strict permanence holds across all 50 constants (`BC-01`–`BC-50`) and 25 families (`BF-01`–`BF-25`) with zero v1 status changes, the 8-vs-42 cohort partition is well-founded and objective, every `digit_frequency_status` value (including `BC-50`, `BC-37`, `BC-29`, `BF-12`, and `BF-16`) matches its cited theorems without inflation, and both verification suites (`portal.py check --strict` and 163 unit tests) currently pass with exit code `0` and zero warnings.

However, the audit uncovered **0 Critical**, **4 Major**, and **6 Minor** findings—all four Major findings are concrete, reproducible defects in Schema v2's mechanical validation rules (`scripts/portal.py`, `docs/benchmarks/SCHEMA.md`) and per-radix evidence semantics (`docs/benchmarks/progress.md`):

- **M1**: Unvalidated loophole allowing `"all integer bases b ≥ 2"` constants to claim `digit_frequency_status = "nontrivial_bound"` with `evidence = "open"`, `registry_ids = []`, and `radix_results = []`, which `bench_cohort_counts` then silently credits to `"Unresolved: external input"`.
- **M2**: Mutual contradiction in Rule 8 for families (`portal.py:1113` vs `portal.py:1126`) making it impossible for any family with all four main status fields `"open"` to carry `digit_frequency_status ∈ {nontrivial_bound, partial}` under *any* `evidence` value.
- **M3**: Cohort Rule 12 (`portal.py:1161`, `SCHEMA.md:238`) accepts `simple_normality = "proved_simply_normal"` as a pre-2026 basis-(a) control witness, even though positive simple normality does not decide `full_normality`.
- **M4**: Semantic conflation in `radix_results` and `bench_property_evidence` on reproved control constants (`BC-34`, `BC-40`, `BC-49`), causing `progress.md` to display contradictory evidence labels (`Kernel-verified` vs `External input` on `BC-49`, `Lean-supported paper proof` vs `External input` on `BC-34`/`BC-40`), making `bench_property_evidence` return `"external"` for in-repo proved properties, and blocking repository per-property records for those `(radix, property)` pairs.

All four Major findings have direct, self-contained fixes.

---

## Verification Commands Run

Both required checks were executed directly in the active worktree:

1. `python -B scripts/portal.py check --strict`
   - **Exit code**: `0`, **Warnings**: `0`
   - **Output**: `Portal verified: 208 registered results, 252 Markdown files, links, anchors, identifiers, topics and figures.`
2. `python -B -m unittest discover -s scripts -p "test_*.py"`
   - **Exit code**: `0`, **Warnings**: `0`
   - **Output**: `Ran 163 tests in 22.438s — OK`

---

## Checklist Audit Summary

### 1. Strict Permanence — **PASS**

A field-by-field programmatic diff of `docs/benchmarks/classical-constants.toml` and `docs/benchmarks/arithmetic-families.toml` against `HEAD` (`0342f1f`) confirmed:
- **Roster preservation**: Exactly 50 constants (`BC-01`–`BC-50`) and 25 families (`BF-01`–`BF-25`) in identical order, with identical `id` and `name` on all 75 entries.
- **Zero v1 status changes**: Every v1 distributional/evidence field (`radices_scope`, `full_normality`, `simple_normality`, `disjunctivity`, `discrepancy_status`, `barrier_status`, `evidence`, `registry_ids`) is byte-for-byte unchanged across all 50 constants and 25 families.
- **Controlled text refinements only**:
  - `BC-34.external_sources`, `BC-40.external_sources`: added Bailey–Borwein–Crandall–Pomerance 2004 Theorem 9.4 (supporting basis-(a) control classification).
  - `BC-37.notes`: appended explicit refusal to promote `CC-21` to `digit_frequency_status` prior to independent verification.
  - `BC-39.discrepancy_summary`: fixed pre-existing Phase 22 formula typo `c_+(n) = (1 − 2 v_2(n)) τ_odd(n)` → `a_+(n) = (1 − v_2(n)) τ_odd(n)` (verified: for $n = 2^k m$ with $m$ odd, $\tau(n) - 2\tau(n/2) = (1 - k)\tau(m)$, matching `GF-28`).
  - `BC-50.notes`: appended explanation of the written deduction from `ST-32` ($D^+ < 1/2 \implies \liminf f_N(d) \ge 0.136$).
  - `BF-11.summary`, `BF-16.summary`: narrowed overbroad `"in any radix"` / `"in every base"` wording to `"in its construction radix b"` / `"in base b"`.
  - `BF-20.summary`: tightened hypotheses on non-Liouville all-prime constructions to match `GF-25`.

### 2. Cohort Rule (`control` = 8 vs `unresolved` = 42) — **DATA PASS / ENFORCEMENT NEEDS REVISION (M3, M4)**

- **Mathematical & historical soundness of the 8-vs-42 split**: **Sound and objective.**
  - **Basis (a) — 5 constants (`BC-34`, `BC-40`, `BC-47`, `BC-48`, `BC-49`)**:
    - `BC-34` ($\Theta_3(1/2)^2$) and `BC-40` ($L_{\chi_4}(2) = (\Theta_3(1/2)^2 - 1)/4$): Bailey–Borwein–Crandall–Pomerance (2004, *J. Théor. Nombres Bordeaux* 16, Theorem 9.4 and the paragraph following it) prove that the binary 1-bits of $z^2$ (with $z = \sum_{n \ge 0} 2^{-n^2} = (1 + \Theta_3(1/2))/2$, differing from $\Theta_3(1/2)^2$ after scaling by $O(\sqrt{N})$ sparse bits) have asymptotic count $C_0 N/\sqrt{\log N}$ ($C_0 \approx 0.7996$), hence $f(1) = 0$ and simple nonnormality in base 2.
    - `BC-47` (Champernowne 1933, base 10), `BC-48` (Copeland–Erdős 1946, base 10), `BC-49` (Stoneham 1973 and Bailey–Crandall 2002, base 2): classical pre-2026 normality theorems.
  - **Basis (b) — 3 constants (`BC-33`, `BC-45`, `BC-46`)**:
    - `BC-33` ($\Theta_3(1/2) = 2 + \sum_{n \ge 2} 2^{-(n^2 - 1)}$, gaps $2n + 1 \to \infty$), `BC-45` ($\sum_{k \ge 0} 2^{-2^k}$, gaps $2^k \to \infty$), `BC-46` ($\sum_{k \ge 1} 10^{-k!}$, gaps $k \cdot k! \to \infty$): each is an explicit lacunary 0–1 expansion in its scope radix.
  - **Unresolved cohort — 42 constants**:
    - The 5 newly decided targets (`BC-27` $E_2$, `BC-28` $E_3$, `BC-29` $E_2^2$, `BC-30` $E_2^3$, `BC-41` $L_{\chi_{-3}}(2)$) all rightly fail basis (b) (signed/alternating or non-0–1 coefficients, with $E_2$ and $E_2^3$ actually simply normal in base 2) and have no cited pre-2026 theorem deciding their scope-radix normality.
    - `BC-37` (Erdős–Borwein $E$) is rightly `unresolved`: its disjunctivity release is dated 2026 and leaves normality open.
    - `BC-50` ($\alpha(2,3)\alpha(2,5)$) and the remaining 35 open targets are rightly `unresolved`.
- **Mechanical enforcement issues**: See **M3** (Rule 12 accepts `proved_simply_normal` as a basis-(a) witness), **M4** (basis-(a) `external` record collides with repository per-property evidence on reproved controls), and **m1** (hardcoded `"Registry entries"` source string on `progress.md:39`).

### 3. `digit_frequency_status` — **DATA PASS / RULE 8 NEEDS REVISION (M1, M2)**

Every constant and family assignment was independently checked against its cited registry statements:
- **`BC-50` (`nontrivial_bound`)**: **Mathematically sound.** Since $\{2^n x\} \in [1/2, 1) \iff d_{n+1} = 1$, extreme interval discrepancy directly gives $|f_N(1) - 1/2| \le D_N(x; 2)$, hence $\limsup |f_N(1) - 1/2| \le D^+(x; 2)$. From `ST-32`, $D^+ \le 4/11 + 2.85 \times 10^{-10} = 0.36363636392\dots < 1/2$, giving
  $$\liminf_{N\to\infty} f_N(d) \ge \frac{1}{2} - \left(\frac{4}{11} + 2.85 \times 10^{-10}\right) = 0.13636363607\dots > 0.136$$
  and $\limsup f_N(d) \le 0.86363636392\dots < 0.864$ for both $d \in \{0, 1\}$. Recording `evidence = "paper"` for this written step from `ST-32` follows `SCHEMA.md:190` faithfully. (See also **m3** regarding `ST-29`'s Lean bound `4631/12500 < 1/2` and `ST-27` for $D^- = 0$.)
- **`BC-37` (`open`)**: **Rigorous and conservative.** Captain Sude (2026) yields only density-zero word counts $N \exp(-70000(\log\log N)^3) = o(N)$; `CC-21` (Mira Cult, Nov 2026) is deliberately withheld pending independent verification of its analytic inputs (matching `discrepancy_status = "open"` and `GF-18`); `CC-49` and `GF-28` are correlation-order barriers, not asymptotic digit bounds.
- **`BC-29` (`nontrivial_bound`)**: **Mathematically sound.** `GF-20` part (4), with the completed uniform Selberg sieve of `GF-27`, proves strictly positive lower asymptotic frequencies for both $0^L$ and $1^L$ in base 2 ($L = 1 \implies \liminf f_N(0) > 0, \liminf f_N(1) > 0$, hence $\limsup f_N(d) < 1$ for both digits). Recording `evidence = "paper"` in `radix_results` accurately reflects the weakest cited entry (`GF-27` is `paper`, and `GF-20` part (4) is a written proof).
- **`BF-12` (`partial`)**: **Mathematically exact.** Every integer-coefficient weight-1 modular form $f(1/b)$ lies in $K_b$ (`GF-06`). By `GF-19`, for every construction radix $b \ge 3$ no element of $K_b$ is simply normal and some digit has asymptotic frequency $0$ (a nontrivial bound), whereas for general signed weight-1 forms at $b = 2$ only 2-normality fails and single-digit frequencies remain open.
- **`BF-16` (`partial`)**: **Mathematically exact.** Every member lies in $K_b$ (`GF-13`), so `GF-19` excludes simple normality (and forces a zero-frequency digit) for all $b \ge 3$; moreover `GF-20` gives $f_{0^L} \to 1$ (`exact_law`) in every construction radix $b \ge 2$ for $q$-digamma reflections with $r = 1$ and $M \mid 24$, while signed cases at $b = 2$ (e.g. $M \nmid 24$) stay open.
- **All remaining 47 constants and 23 families**: Verified consistent with their registry entries (`BF-03` has a minor summary-clarity note in **m4**).
- **Mechanical validation defects**: See **M1** and **M2**.

### 4. `radix_results` Schema, Mechanical Checks, and Rendered Tables in `progress.md` — **COUNTS PASS / SCHEMA & RENDERING NEED REVISION (M1–M4, m1–m6)**

- **Independent count recomputation**: Every single number in `docs/benchmarks/progress.md` was recomputed independently from the two TOML files and matches verbatim:
  - Summary by objective: Obj 1 = `5`, Obj 2 = `10`, Obj 3 (discrepancy) = `14`, Obj 3 (digit frequencies) = `14`, Obj 4 = `16`, All four open = `35`.
  - Cohort breakdown (Control / 8 vs Unresolved / 42, Repo vs External): Obj 1 = `3 | 2 | 2 | 0`; Obj 2 = `5 | 5 | 5 | 0`; Obj 3 disc = `8 | 6 | 6 | 0`; Obj 3 df = `8 | 6 | 6 | 0`; Obj 4 = `0 | 16 | 16 | 0`. (Note: `BC-37` has `disjunctivity = proved_disjunctive` with `evidence = external`, which falls outside the 4 objective criteria above and explains why `50 - 35 = 15` constants have a non-open distributional field while Obj 3 counts `14`.)
  - Counts by category: exact match on all 8 rows × 8 numeric columns.
  - Per-radix table: 12 rows matching all 12 `radix_results` inline tables across `BC-29` (3), `BC-34` (1), `BC-37` (1), `BC-40` (1), `BC-47` (1), `BC-48` (1), `BC-49` (1), `BC-50` (3).
- **Defects found in `portal.py`, `SCHEMA.md`, and `progress.md`**: Detailed in **M1–M4** and **m1–m6** below.

---

## Detailed Findings

### Critical Findings

*None.*

---

### Major Findings

#### M1 — Rule 8 / Rule 11 Loophole Accepts Unbacked `digit_frequency_status = "nontrivial_bound"` on All-Bases Constants and Miscredits It to External Input
- **Files & Lines**:
  - [scripts/portal.py:1113-1114](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1113-L1114), [scripts/portal.py:1126-1127](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1126-L1127), [scripts/portal.py:1140-1143](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1140-L1143), [scripts/portal.py:792-794](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L792-L794), [scripts/portal.py:861](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L861)
  - [docs/benchmarks/SCHEMA.md:136](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L136), [docs/benchmarks/SCHEMA.md:190](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L190), [docs/benchmarks/SCHEMA.md:224-228](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L224-L228), [docs/benchmarks/SCHEMA.md:236](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L236)
- **Finding**: For a constant with `radices_scope = "all integer bases b ≥ 2"` (28 of the 50 constants, e.g., `BC-01`–`BC-26`, `BC-42`, `BC-44`), `single` is `False` at `portal.py:1140`. Therefore:
  1. `portal.py:1141` (`if single and df == "nontrivial_bound" ...`) is skipped, requiring no `radix_results` record.
  2. `portal.py:1113` checks only the 4 `BENCH_STATUS_FIELDS`, allowing `evidence = "open"`.
  3. `portal.py:1126` (`if not is_const and df != "open" and ev == "open":`) applies only to families.
  - **Reproduced**: Mutating `BC-01` (`radices_scope = "all integer bases b ≥ 2"`) to `digit_frequency_status = "nontrivial_bound"` with `evidence = "open"` and `radix_results = []` passes `portal.check_benchmarks` with **`0` errors** (`errs = []`), even though no evidence for the bound is recorded anywhere. Worse, `bench_cohort_counts` then returns `(8, 7, 6)` for `Objective 3 (digit-frequency law or bound)` because `bench_property_evidence(BC-01, "digit_frequency_status")` returns `"open" ∉ BENCH_REPOSITORY_EVIDENCE`, causing `progress.md` (`portal.py:861`) to silently credit an `"open"`-evidence entry to `"Unresolved: external input"`.
- **Actionable Fix**: Because a `radix_results` record only accepts a single base `"base B"`, an all-bases `digit_frequency_status = "nontrivial_bound"` must carry its evidence in the entry-level `evidence` field. Include `digit_frequency_status` in the `evidence == "open"` equivalence whenever the entry does not use a single-base scope (i.e., for families and for `"all integer bases b ≥ 2"` constants; see **M2**), update `SCHEMA.md:190,198,224,228`, and add a regression test in `scripts/test_benchmarks.py`.

#### M2 — Rule 8 Self-Contradiction Makes `digit_frequency_status ∈ {nontrivial_bound, partial}` Unsatisfiable for Families When the Four Main Status Fields Are `open`
- **Files & Lines**:
  - [scripts/portal.py:1113-1114](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1113-L1114), [scripts/portal.py:1126-1127](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1126-L1127)
  - [docs/benchmarks/SCHEMA.md:190](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L190), [docs/benchmarks/SCHEMA.md:198](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L198), [docs/benchmarks/SCHEMA.md:224](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L224), [docs/benchmarks/SCHEMA.md:228](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L228)
  - [scripts/test_benchmarks.py:181-184](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/test_benchmarks.py#L181-L184)
- **Finding**: For families (`not is_const`), `portal.py:1113` requires:
  ```python
  if (ev == "open") != all(e[k] == "open" for k in BENCH_STATUS_FIELDS):
  ```
  while `portal.py:1126` requires:
  ```python
  if not is_const and df != "open" and ev == "open":
  ```
  Whenever a family has all four fields in `BENCH_STATUS_FIELDS` equal to `"open"` and gains a digit-frequency bound (`digit_frequency_status = "nontrivial_bound"` or `"partial"`), line 1113 **forces `ev == "open"`** while line 1126 **forbids `ev == "open"`**.
  - **Reproduced**: On `BF-13` with `digit_frequency_status = "partial"`, **every** valid `evidence` value (`"open"`, `"paper"`, `"external"`, `"lean"`, `"lean+paper"`) is rejected by `portal.check_benchmarks`. Note that `test_benchmarks.py:181-184` (`test_family_bound_requires_evidence`) only checked that `evidence = "open"` is rejected and never tested that setting `evidence = "paper"` makes the entry pass!
- **Actionable Fix**: Unify **M1** and **M2** cleanly in `scripts/portal.py:1113` and `docs/benchmarks/SCHEMA.md:190,198,224,228`:
  - For families (`not is_const`) and for all-bases constants (`is_const and not single`), check `(ev == "open") != all(e[k] == "open" for k in BENCH_RR_PROPERTIES)` (all five distributional fields including `digit_frequency_status`), and remove the now-redundant line 1126.
  - For single-base constants (`is_const and single`), keep `(ev == "open") != all(e[k] == "open" for k in BENCH_STATUS_FIELDS)` (since `digit_frequency_status = nontrivial_bound` carries its evidence in the mandatory scope-radix `radix_results` record, as tested in `test_benchmarks.py:192-198`).
  - Extend `test_family_bound_requires_evidence` in `scripts/test_benchmarks.py` to assert that setting `evidence = "paper"` on `BF-13` (with `digit_frequency_status = "partial"`) succeeds, and add a test rejecting an all-bases constant with `digit_frequency_status = "nontrivial_bound"` and `evidence = "open"`.

#### M3 — Cohort Rule 12 Accepts Positive `simple_normality = "proved_simply_normal"` as a Basis-(a) Control Witness
- **Files & Lines**:
  - [scripts/portal.py:1158-1165](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1158-L1165)
  - [docs/benchmarks/SCHEMA.md:79](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L79), [docs/benchmarks/SCHEMA.md:238](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L238)
- **Finding**: `SCHEMA.md:79` correctly states the mathematical rule: a pre-2026 published theorem decides `full_normality`, *"or decides simple normality **negatively** and hence the question."* Positive simple normality (`proved_simply_normal`) does **not** decide `full_normality` (witness `BC-27` $E_2$ and `BC-30` $E_2^3$). However, `portal.py:1161` checks only:
  ```python
  and r["property"] in ("full_normality", "simple_normality")
  ```
  without checking `r["status"] == "proved_not_simply_normal"` when `r["property"] == "simple_normality"`.
  - **Reproduced**: Replacing `BC-49`'s `radix_results` with `{radix = "base 2", property = "simple_normality", status = "proved_simply_normal", evidence = "external", source = "Someone 1990: proved simply normal only"}` passes `portal.check_benchmarks` with **`0` errors**.
- **Actionable Fix**: Replace `portal.py:1161` with:
  ```python
  and (r["property"] == "full_normality"
       or (r["property"] == "simple_normality" and r["status"] == "proved_not_simply_normal"))
  ```
  update `SCHEMA.md:79` and `SCHEMA.md:238` to state `full_normality` or `simple_normality = proved_not_simply_normal`, and add a unit test in `scripts/test_benchmarks.py` (`CohortTests`) confirming that a `proved_simply_normal` external record is rejected as a basis-(a) control witness.

#### M4 — Semantic Conflation in `radix_results` and `bench_property_evidence` on Reproved Control Constants (`BC-34`, `BC-40`, `BC-49`)
- **Files & Lines**:
  - [docs/benchmarks/classical-constants.toml:808,815-817](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L808-L817) (`BC-34`), [docs/benchmarks/classical-constants.toml:955,964-966](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L955-L966) (`BC-40`), [docs/benchmarks/classical-constants.toml:1173,1181-1183](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L1173-L1183) (`BC-49`)
  - [docs/benchmarks/progress.md:91,97,106,111,118,120,123](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md#L106-L123)
  - [docs/benchmarks/SCHEMA.md:134,190](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L134)
  - [scripts/portal.py:723-732](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L723-L732)
- **Finding**: `radix_results` is overloaded for two conflicting purposes in the scope radix:
  1. Recording the **per-property best/actual evidence** when a single property has stronger or weaker evidence than the entry-level weakest label (e.g., `BC-50` `discrepancy_status` = `lean` vs entry `paper`; `BC-29` `digit_frequency_status` = `paper` vs entry `lean+paper`).
  2. Storing the **pre-2026 external theorem** (`evidence = "external"`) that places a basis-(a) constant in `cohort = "control"`.
  - For the three basis-(a) controls that are **also proved in the repository** (`BC-34`, `BC-40`, `BC-49`), this overloading creates three concrete inconsistencies:
    1. **Contradictory tables in `progress.md`**: Table 4 (`progress.md:106`) labels `BC-49` **Kernel-verified** (`lean`), whereas Table 5 (`progress.md:123`)—whose header (`progress.md:111`) promises *"the evidence label of that property alone"*—labels `BC-49 | base 2 | normality` as **External input** (`external`), with no indication that `BC-49` is kernel-verified in Lean (`ST-01`, `ST-11`) and that the row merely records pre-2026 control provenance. The exact same contradiction appears for `BC-34` (`progress.md:91` vs `:118`) and `BC-40` (`progress.md:97` vs `:120`), both labeled **Lean-supported paper proof** in Table 4 (`CC-46`, `CC-48`) yet **External input** for `simple normality` in Table 5.
    2. **Wrong return value in `bench_property_evidence`**: Calling `portal.bench_property_evidence` returns `"external"` for `BC-49.full_normality` (entry `evidence = "lean"`), `BC-34.simple_normality` (entry `evidence = "lean+paper"`), and `BC-40.simple_normality` (entry `evidence = "lean+paper"`). It happens not to distort `bench_cohort_counts` only because `bench_cohort_counts` skips `bench_property_evidence` on `cohort == "control"` entries.
    3. **Uniqueness collision**: Because `(radix, property)` must be unique in `radix_results`, storing the historical `external` record on `BC-49` makes it impossible to record a per-property `lean` record for `BC-49`'s `full_normality` (or `lean+paper` for `BC-34`/`BC-40`'s `simple_normality`).
- **Actionable Fix** (choose one):
  - **Recommended (cleanest separation)**: Do not overload `radix_results` with historical control provenance on reproved controls. Keep `radix_results` strictly for current per-property evidence (where an `external` record means the property currently rests *only* on external input, as on `BC-37`, `BC-47`, `BC-48`), and validate basis-(a) pre-2026 provenance directly against `external_sources` (e.g., requiring a pre-2026 dated theorem in `external_sources`, or an explicit pre-program source entry). On `BC-49`, `BC-34`, `BC-40`, either omit the redundant scope-radix record or record the repository's actual per-property evidence (`lean` / `lean+paper`).
  - **Alternative (if keeping pre-2026 `external` rows in `radix_results`)**: Explicitly distinguish historical control rows in `progress.md:111` and in the rendered `Evidence` or `Source` text (e.g., `"External input (pre-program control; also proved in repository)"`), document in `SCHEMA.md:134` that on reproved control constants an `external` scope-radix record documents historical provenance rather than downgrading the entry-level repository proof, and guard `bench_property_evidence` so an `external` control-provenance record never downgrades a stronger repository `e["evidence"]`.

---

### Minor Findings

#### m1 — Hardcoded `"Registry entries"` Attribution in `progress.md` Cohort Summary Table
- **Files & Lines**: [scripts/portal.py:871-873](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L871-L873), [docs/benchmarks/progress.md:39](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md#L39)
- **Finding**: `portal.py:871-873` filters `unres_decided = [e for e in unresolved if e["full_normality"] != "open"]` and unconditionally prints `"| Registry entries (see the constant table) |"`. While accurate today (`BC-27`, `BC-28`, `BC-29`, `BC-30`, `BC-41`), if an initially unresolved constant's `full_normality` is ever decided by an external theorem (as modeled in `test_benchmarks.py:351-359`), this row will falsely credit it to repository registry entries.
- **Fix**: Split `unres_decided` by `bench_property_evidence(e, "full_normality") in BENCH_REPOSITORY_EVIDENCE` (rendering a separate external-input row if nonempty, or displaying the actual source dynamically).

#### m2 — `BC-29.radix_results[1]` Cites Only `GF-04` Under `evidence = "lean+paper"` Although `GF-04` Formalizes Nothing About $E_b^2$
- **Files & Lines**: [docs/benchmarks/classical-constants.toml:695](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L695), [docs/benchmarks/progress.md:115](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md#L115), [docs/registry/GF.toml:60](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/registry/GF.toml#L60)
- **Finding**: `BC-29.radix_results[1]` records `full_normality = proved_nonnormal`, `evidence = "lean+paper"`, `source = "GF-04: E_2² ∈ K_2"`. While `GF-04` has bundle status `lean+paper` (so it passes mechanical validation), `GF-04`'s Scope explicitly warns: *"Nothing about $E_b^2$ (coefficients, support or $K_b$-membership) is formalized."* Its Lean theorems cover only $E_b^3$. The generic Lean transfer cores that actually enter $E_2^2 \in K_2$ are in `GF-01` (`CoefficientTransfer`) and `GF-12` (`RadixWidthLaw.lean`).
- **Fix**: Cite `GF-04` together with `GF-12` in `BC-29.radix_results[1].source` (e.g., `"GF-04 and GF-12: E_2² ∈ K_2 (Lean width-law core in GF-12; E_2²-specific steps are paper proofs)"`), or label `GF-04` alone as `paper`.

#### m3 — Minor Citation Precision on `BC-50.radix_results[1..2]` (`ST-27` for $D^- = 0$; `ST-29` Lean Bound `4631/12500`)
- **Files & Lines**: [docs/benchmarks/classical-constants.toml:1202,1208-1209](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L1202-L1210), [docs/benchmarks/progress.md:124-125](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md#L124-L125), [docs/registry/ST.toml:667,717,787](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/registry/ST.toml#L717)
- **Finding**:
  1. `BC-50.radix_results[1]` (`:1208`) cites `ST-32` for `D⁻ = 0`; `ST-32` proves $\sum_{D_N > \varepsilon} 1/(N\log N) < \infty$ (which implies $D^- = 0$), whereas `ST-27` (not listed in `BC-50.registry_ids`) first explicitly states $\liminf D_N(x) = 0$.
  2. `BC-50.radix_results[2]` (`:1209`) states `"ST-06 (D⁺ ≤ 43/45), sharpened in Lean by ST-14 (27/40) and ST-25 (143881/250000)"`, omitting that `ST-29` also proves `4631/12500 = 0.37048 < 1/2` in Lean (`NormalityChecker.ProductThreeFive.NonrectangularOrdinary.mixed_product_discrepancy`)—presumably omitted because `ST-29` has bundle status `lean+paper`, which Rule 11 rejects inside an `evidence = "lean"` record.
- **Fix**: Either add `ST-27` to `BC-50.registry_ids` and cite `ST-27`/`ST-32` on line 1208 (or write `"D⁻ = 0 (implied by ST-32)"`), and note `ST-29`'s Lean bound `4631/12500` in `BC-50.notes` so the Lean baseline is not understated.

#### m4 — `BF-03.summary` Does Not Explicitly Name the Digit-Frequency Subfamily Required by `SCHEMA.md:109`
- **Files & Lines**: [docs/benchmarks/arithmetic-families.toml:56,61](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml#L56-L61), [docs/benchmarks/SCHEMA.md:109](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L109)
- **Finding**: `SCHEMA.md:109` defines `digit_frequency_status = "partial"` for families as *"an explicit subfamily stated in `summary` has an exact law or a nontrivial bound, other members are open."* `BF-03.summary` states $D^+ \le 4/11 + 2.85 \times 10^{-10}$ for $\alpha(2, 3)\alpha(2, 5)$ (and explicit $D^+ < 1$ in `ST-35`), which implies a nontrivial digit-frequency bound whenever $D^+ < 1 - 1/B$, but does not explicitly mention digit frequencies in `summary`.
- **Fix**: Add a brief clause to `BF-03.summary` (e.g., `"; the explicit bounds D⁺ < 1 − 1/B (in particular for α(2, 3) α(2, 5)) give nontrivial digit-frequency bounds"`).

#### m5 — `"All open"` Column in `Counts by category` Ignores `digit_frequency_status`
- **Files & Lines**: [scripts/portal.py:827,886](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L827-L886), [docs/benchmarks/progress.md:20,43](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md#L43)
- **Finding**: `all_open` (`portal.py:827`) and `n_open` (`portal.py:886`) check only the four v1 `BENCH_STATUS_FIELDS`. Currently the counts coincide (`35`), but if a constant ever has a `digit_frequency_status = "nontrivial_bound"` with the other four fields `"open"` (explicitly allowed by `test_benchmarks.py:192`), `Counts by category` (`progress.md:43`) would count the same constant under both `"Digit law or bound"` and `"All open"`.
- **Fix**: Check `BENCH_RR_PROPERTIES` (all five distributional fields) in `n_open` (and update the Summary table label accordingly), or rename the category column to make its 4-field scope explicit.

#### m6 — Small Code-Hygiene & Edge-Case Items in `scripts/portal.py`
- **Files & Lines**: [scripts/portal.py:702-703,720,735-756,863](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L702-L756)
- **Findings**:
  1. `bench_years` (`:720`) duplicates `BENCH_YEAR_RE` (`:702`) instead of calling `BENCH_YEAR_RE.finditer(text)`; moreover, `any(y < 2026 ...)` in `:1162` could match a non-year 4-digit integer in `1500..2025` (e.g., a prime `1801` or `1729`) inside a 2026 citation.
  2. `bench_radix_consistency` (`:735-756`) omits checking `df == "exact_law"` against `simple_normality` in a non-scope radix (unlike entry-level Rule 7); either mirror Rule 7 or note in `SCHEMA.md:235` that recording `exact_law` without `simple_normality` in a non-scope radix is intentional.
  3. `reproved` (`:863`) checks entry-level `e["evidence"] in BENCH_REPOSITORY_EVIDENCE`, which would undercount a control constant whose `full_normality` is reproved in-repo if another property rested only on external input; once **M4** is resolved, `bench_property_evidence(e, "full_normality") in BENCH_REPOSITORY_EVIDENCE` is more exact.
  4. `BENCH_ID_RE` (`:703`) uses `\d{2}` rather than `\d{2,}` (relevant only if `BF-` families ever reach `BF-100`).

---

## Reminder on Review Scope

**Cross-model review is not independent human peer review.** This audit verifies mechanical consistency, mathematical deductions from cited registry entries, historical attributions, and test coverage, and should be followed by targeted fixes for **M1–M4** (and optionally **m1–m6**) before committing Track F-Bench.

---

## Post-Repair Verification

- **Reviewer**: Independent cross-provider audit sub-agent (Gemini 4 Neon)
- **Date**: 2026-11-27
- **Final Verdict**: **ACCEPT**
- **Notice on review status**: **Cross-model review is not independent human peer review.**

### Verification of Major Findings (M1–M4)

| ID | Status | Verification summary |
| --- | --- | --- |
| **M1** | **Closed** | `bench_evidence_covers` ([scripts/portal.py:742-757](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L742-L757)) covers `digit_frequency_status` for families and all-bases constants (and `exact_law`), and Rule 8 ([scripts/portal.py:1241-1247](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1241-L1247)) rejects unbacked all-bases `nontrivial_bound` with `evidence = "open"`. `bench_cohort_counts` ([scripts/portal.py:836-845](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L836-L845)) raises `ValueError` instead of silently crediting missing evidence to external input. Reproduced and confirmed blocked. |
| **M2** | **Closed** | Rule 8 ([scripts/portal.py:1241-1247](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1241-L1247), [docs/benchmarks/SCHEMA.md:208,242](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L242)) now unifies all five distributional fields for families (and all-bases constants), removing the contradictory check. Verified on `BF-13` with `digit_frequency_status = "partial"`: `evidence = "open"` is rejected while `evidence = "paper"` / `"external"` passes. |
| **M3** | **Closed** | Rule 12 ([scripts/portal.py:1140-1145](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1140-L1145), [docs/benchmarks/SCHEMA.md:80,111,256](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L256)) accepts only `full_normality ∈ {proved_normal, proved_nonnormal}` or `simple_normality = proved_not_simply_normal` in `control_provenance`, explicitly rejecting `proved_simply_normal` and non-normality properties. |
| **M4** | **Closed** | Clean separation via the new required `control_provenance` inline table (`basis`, `property`, `status`, `source`; `{}` for `unresolved`), validated by Rules 1, 5, 11, and 12 ([scripts/portal.py:1103-1107,1117-1157](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L1103-L1157)). Rule 11 rejects scope-radix `radix_results` records weaker than entry-level `evidence` for covered properties. Across all tables in [docs/benchmarks/progress.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md), `BC-34` and `BC-40` are consistently **Lean-supported paper proof** (`CC-46`) and `BC-49` is consistently **Kernel-verified** (`ST-01`, `ST-11`), with their pre-2026 external classifications displayed in the separate *Pre-program classification of the control constants* table (`progress.md:41-54`). `bench_property_evidence` returns `"lean+paper"` for `BC-34`/`BC-40` `simple_normality` and `"lean"` for `BC-49` `full_normality`. |

### Verification of Minor Findings (m1–m6)

- **m1 (Closed)**: `portal.py:926-934` dynamically partitions `unres_decided` into repository vs external-input rows (`test_externally_decided_target_listed_separately`).
- **m2 (Closed)**: `BC-29.radix_results[1]` ([classical-constants.toml:724](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L724)) cites both `GF-04` and `GF-12`, explicitly distinguishing the Lean width-law core in `GF-12` from the `E_2²`-specific paper steps in `GF-04`.
- **m3 (Closed)**: `ST-27` was added to `BC-50.registry_ids` (no status change) and cited alongside `ST-32` for `D⁻ = 0` in `BC-50.radix_results[1]`; `BC-50.radix_results[2]` and `BC-50.notes` ([classical-constants.toml:1258-1262](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/classical-constants.toml#L1258-L1262)) document `ST-29`'s Lean bound `4631/12500 = 0.37048 < 1/2`.
- **m4 (Closed)**: `BF-03.summary` ([arithmetic-families.toml:61](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/arithmetic-families.toml#L61)) explicitly names the digit-frequency subfamily (`α(2, 3) α(2, 5)`, lower frequency ≥ `0.136`, upper frequency ≤ `0.864`) recorded by `digit_frequency_status = partial`.
- **m5 (Closed)**: Both `all_open` (`portal.py:879`) and `n_open` (`portal.py:964`) check all five distributional fields (`BENCH_RR_PROPERTIES`), with labels updated to `"All five distributional fields open"` / `"All five fields open"` in `progress.md` and `SCHEMA.md`.
- **m6 (Closed)**: All four sub-items fixed: `bench_years` calls `BENCH_YEAR_RE.finditer` and `bench_is_pre_program` requires *every* 4-digit year in both `control_provenance.source` and matched `external_sources` entries to precede `2026` (blocking incidental numbers such as `1729` inside a 2026 citation); `bench_radix_consistency` enforces `exact_law` requiring a `simple_normality` record in the same radix (`SCHEMA.md:253`); `reproved` (`portal.py:917-918`) uses `bench_property_evidence(e, "full_normality")`; `BENCH_ID_RE` uses `\d{2,}`.

### Strict Permanence Against `HEAD` (`0342f1f`) — **PASS**

A programmatic diff against `0342f1f` confirmed:
- Exact same 50 constants (`BC-01`–`BC-50`) and 25 families (`BF-01`–`BF-25`) in identical order with identical `id` and `name`.
- **Zero status or evidence inflations**: every v1 status/evidence field (`radices_scope`, `full_normality`, `simple_normality`, `disjunctivity`, `discrepancy_status`, `barrier_status`, `evidence`) is byte-for-byte unchanged on all 75 entries.
- The only `registry_ids` diff is adding `"ST-27"` to `BC-50.registry_ids` (supporting **m3** with no status change); all other diffs to v1 fields are the controlled text refinements already audited (`BC-34`/`BC-40` `external_sources`, `BC-37`/`BC-50` `notes`, `BC-39` `discrepancy_summary`, `BF-03`/`BF-11`/`BF-16`/`BF-20` `summary`).

### Verification Command Results

1. `python -B -m unittest discover -s scripts -p "test_*.py"`
   - **Exit code**: `0`, **Warnings**: `0`
   - **Output**: `Ran 185 tests in 14.107s — OK` (22 new benchmark regression tests added in [scripts/test_benchmarks.py](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/test_benchmarks.py)).
2. `python -B scripts/portal.py check --strict`
   - **Exit code**: `1`, **Warnings**: `0`
   - **Observed error (unrelated to Track F-Bench)**: `error: figures: stale or missing: assets\figures\data\proof-dependency-map.json`. Diffing the generated JSON against the committed file confirmed the sole difference is `"modules_parsed": 266` → `267`, caused by an untracked Lean file (`NormalityChecker/HigherOrderTower.lean`) present in the shared worktree from another Phase 23 track.
3. `python -B scripts/portal.py check --strict --skip-figures`
   - **Exit code**: `0`, **Warnings**: `0`
   - **Output**: `Portal verified: 208 registered results, 252 Markdown files, links, anchors, identifiers, topics and figures.` (including byte-for-byte freshness of `docs/benchmarks/progress.md` and all Track F-Bench rules).

### Non-Blocking Note

- Minor prose nit only: the intro paragraph of *Per-radix and per-property results* ([scripts/portal.py:980-981](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/portal.py#L980-L981), rendered at [docs/benchmarks/progress.md:126](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/progress.md#L126)) states *"never weaker than the entry-level label"* without the *"for a covered property"* qualifier that [docs/benchmarks/SCHEMA.md:152,154](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/docs/benchmarks/SCHEMA.md#L152-L154) states accurately (for `BC-29`, the uncovered `digit_frequency_status = nontrivial_bound` row is `Paper proof` while entry-level evidence is `Lean-supported paper proof`). Does not affect schema enforcement or counts.

All Major findings (**M1–M4**) and Minor findings (**m1–m6**) are cleanly closed. Track F-Bench is **ACCEPTED**. Cross-model review is not independent human peer review.
