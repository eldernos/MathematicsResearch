# Benchmark format

The benchmark suite measures progress on the four [research objectives](../research-objectives.md) against a fixed list of targets. It has two TOML files in this directory:

| File | Table | Identifiers | Content |
| --- | --- | --- | --- |
| [classical-constants.toml](classical-constants.toml) | `[[constant]]` | `BC-01` … `BC-50` | Exactly 50 prominent constants, each with a published or kernel-verified proof of irrationality |
| [arithmetic-families.toml](arithmetic-families.toml) | `[[family]]` | `BF-01`, `BF-02`, … | Structured arithmetic families studied in the repository and in the literature |

The progress table [progress.md](progress.md) is generated from both files by `python3 scripts/portal.py build`. Do not edit it by hand.

## Permanence

- The constant roster is fixed at 50 entries. A constant is never added, removed, replaced or renumbered, so the counts in the progress table compare like with like over time.
- Family identifiers are permanent. New families take the next free number. A family is never deleted; if its definition proves defective, the entry keeps its identifier and its `notes` or `open_frontier` field says so.
- The `cohort` of a constant (see [Cohorts](#cohorts)) is fixed when it is assigned and never changes, even after an initially unresolved target is resolved.
- A status changes only when a result establishes it: a registry entry (listed in `registry_ids`) or a named published theorem (listed in `external_sources`). If an error is found, the status reverts and the entry records the correction.
- Finite computations, conditional theorems, heuristics and cross-model reviews never change a status. They may be mentioned in `notes`, `summary` or `open_frontier` with their scope. Cross-model review is not independent human peer review.

## Top-level `[meta]` table

Both files begin with a `[meta]` table.

| Key | File | Value |
| --- | --- | --- |
| `schema_version` | both | The integer `2`. |
| `status_as_of` | both | The research phase whose verified results the statuses reflect, for example `"Phase 22"`. |
| `roster_size` | constants | The integer `50`. |

Schema version 2 added `cohort`, `control_provenance`, `digit_frequency_status` and `radix_results` to constants and `digit_frequency_status` to families. No status value of version 1 changed in the migration.

## Fields of a `[[constant]]` table

Every field is required and no other field is allowed.

| Field | Type | Meaning |
| --- | --- | --- |
| `id` | string | `BC-01` … `BC-50`, in file order, each exactly once. |
| `name` | string | Human-readable name, unique in the file. Plain Unicode, for example `"π"`, `"ln 2"`, `"Euler's product E_2"`. |
| `formula` | string | A definition in plain Unicode. |
| `category` | enum | One of the category keys below. |
| `cohort` | enum | `control` or `unresolved`; see [Cohorts](#cohorts). Fixed. |
| `arithmetic_nature` | string | The proved arithmetic status with its source, for example `"transcendental (Lindemann 1882)"` or `"irrational (Apéry 1978); transcendence open"`. Every constant is proved irrational. |
| `radices_scope` | string | `"base B"` for one integer *B* ≥ 2, or `"all integer bases b ≥ 2"`. The status fields refer to this scope (see below). |
| `full_normality` | enum | `proved_normal`, `proved_nonnormal` or `open`. |
| `simple_normality` | enum | `proved_simply_normal`, `proved_not_simply_normal`, `radix_dependent` or `open`. |
| `disjunctivity` | enum | `proved_disjunctive`, `proved_non_disjunctive` or `open`. |
| `discrepancy_status` | enum | `zero_normal`, `exact_positive`, `strict_upper_bound`, `maximal_K_b` or `open`. |
| `digit_frequency_status` | enum | `exact_law`, `nontrivial_bound` or `open`; see [Digit frequencies](#digit-frequencies). |
| `barrier_status` | enum | `resolved`, `barrier_proved` or `no_barrier_recorded`. |
| `evidence` | enum | `lean`, `lean+paper`, `paper`, `external` or `open`. |
| `discrepancy_summary` | string | What is proved about *D*<sub>*N*</sub>, *D*⁺, *D*⁻ and digit frequencies, and what is open. |
| `registry_ids` | list of strings | Registry identifiers (`docs/registry/*.toml`) that prove a status, a barrier or a structural reduction for this constant. May be empty. Comparative cross-references mentioned only in `notes`, `summary` or `open_frontier` need not be listed here. |
| `external_sources` | list of strings | Published or released theorems used, each naming the author(s), the year (a four-digit year, with a release date or commit for software releases) and the statement. At least one entry, which supports `arithmetic_nature`. |
| `control_provenance` | inline table | The pre-program classification of a `control` constant, with the string keys `basis`, `property`, `status` and `source`; see [Cohorts](#cohorts). `{}` for an `unresolved` constant. |
| `radix_results` | list of inline tables | Per-radix and per-property records of current evidence; see [Per-radix records](#per-radix-records). `[]` when nothing beyond the entry-level fields is recorded. |
| `notes` | string | Exact scope, the main open question and the key barrier. |

**Scope of the status fields.** With `radices_scope = "base B"` a status refers to base *B* only. With `"all integer bases b ≥ 2"`, `proved_normal` means normal in every integer base (absolutely normal), `proved_nonnormal` means nonnormal in every integer base, and `open` means that the property is not settled in every integer base at once. A base in which the property is settled is listed in `radix_results`; with `radix_results = []`, `open` means that the property is not settled in any integer base.

### Category keys

| Key | Displayed as |
| --- | --- |
| `algebraic` | Algebraic irrationals |
| `logarithmic_and_pi` | Logarithms, π and Gelfond–Schneider values |
| `exponential_and_bessel` | Exponential, Gamma and Bessel values |
| `zeta_and_l_values` | Zeta and Dirichlet L-values |
| `q_series_and_modular` | q-series, theta and modular values |
| `lambert_and_divisor` | Lambert and divisor series |
| `continued_fraction_and_mahler` | Continued-fraction and Mahler-type numbers |
| `synthetic_classical` | Classical normal-number constructions |

## Cohorts

The roster mixes two populations, which the progress table counts separately.

**Rule.** A constant is `control` exactly when, before this research program began (2026), its normality or nonnormality in the scope radix (`full_normality` in `radices_scope`) was already settled on one of two bases:

- **(a) Published theorem.** A named theorem published before 2026 decides the question, or decides simple normality negatively and hence the question. Positive simple normality does not decide the question (Euler's product *E*<sub>2</sub> is simply normal and nonnormal in base 2) and never qualifies. The theorem is listed in `external_sources` and recorded in `control_provenance` with `basis = "published_theorem"`.
- **(b) Explicit digits.** The defining series is an explicit lacunary 0–1 expansion in the scope radix, a sum of distinct powers *b*<sup>−*n*<sub>*k*</sub></sup> with gaps *n*<sub>*k*+1</sub> − *n*<sub>*k*</sub> → ∞ (after removing an integer part). The digits are then read off the definition and the digit 1 has frequency 0. The reading is recorded in `control_provenance` with `basis = "explicit_digits"`.

Every other constant is `unresolved`: an initially unresolved research target whose scope-radix normality was open when the roster was fixed. A result that later settles such a target records progress and does not change its cohort. A theorem that establishes only a weaker property (for example a lower bound for the number of ones, density zero) does not make a constant `control`.

The control cohort is fixed as follows. `scripts/portal.py` rejects any other assignment.

| ID | Constant | Basis | Pre-program classification |
| --- | --- | --- | --- |
| `BC-33` | Θ_3(1/2) | (b) | Binary digit 1 exactly at positions *n*² − 1; nonnormal. |
| `BC-34` | Θ_3(1/2)² | (a) | Bailey–Borwein–Crandall–Pomerance 2004, Theorem 9.4 and the paragraph after it: the ones-count is asymptotic to *C*<sub>0</sub>*N*/√(log *N*), so the digit 1 has frequency 0; not simply normal in base 2. |
| `BC-40` | *L*<sub>χ<sub>4</sub></sub>(2) | (a) | The same theorem, since Θ_3(1/2)² = 1 + 4*L*<sub>χ<sub>4</sub></sub>(2) and the binary digits differ by a shift of two places. |
| `BC-45` | Kempner–Fredholm number | (b) | Binary digit 1 exactly at positions 2<sup>*k*</sup>; nonnormal. |
| `BC-46` | Liouville's constant | (b) | Decimal digit 1 exactly at positions *k*!; nonnormal. |
| `BC-47` | Champernowne's constant | (a) | Champernowne 1933: normal in base 10. |
| `BC-48` | Copeland–Erdős constant | (a) | Copeland–Erdős 1946: normal in base 10. |
| `BC-49` | Stoneham α(2, 3) | (a) | Stoneham 1973 and Bailey–Crandall 2002: normal in base 2. |

Constants whose scope-radix classification is due to this repository (for example `BC-27`–`BC-30`, `BC-41`) or to a release dated 2026 (the disjunctivity of `BC-37`, which leaves normality open) are `unresolved`. The repository also reproves several control classifications with registry entries; this does not change their cohort, and the progress table shows it separately.

### Control provenance

`control_provenance` keeps the pre-program classification apart from the current evidence, so that a control constant reproved in the repository (`BC-34`, `BC-40`, `BC-49`) carries both its historical source and its repository label without contradiction:

```toml
control_provenance = { basis = "published_theorem", property = "full_normality", status = "proved_normal", source = "Stoneham 1973 and Bailey–Crandall 2002: normality of α(2, 3) in base 2" }
```

| Key | Value |
| --- | --- |
| `basis` | `published_theorem` (basis (a)) or `explicit_digits` (basis (b)), as fixed in the table above. |
| `property` | `full_normality`, with the entry-level value `proved_normal` or `proved_nonnormal`, or `simple_normality`, with the entry-level value `proved_not_simply_normal`. |
| `status` | The entry-level value of `property`. |
| `source` | For `published_theorem`: the named theorem with its year. Every four-digit year in it precedes 2026 and belongs to an entry of `external_sources` whose years all precede 2026, and it names no registry entry. For `explicit_digits`: the digit positions read off the defining series. |

The record describes history and has no evidence label. The current evidence of the same property is the entry-level `evidence`, or a scope-radix `radix_results` record; for `BC-49`, for example, the provenance names Stoneham 1973 and Bailey–Crandall 2002 while the scope-radix record gives the kernel-verified proof (`ST-01`, `ST-11`).

## Digit frequencies

`digit_frequency_status` tracks what is proved about the asymptotic frequencies *f*<sub>*N*</sub>(*d*) of the individual digits *d* among the first *N* digits in the scope radix, separately from simple normality, discrepancy and full normality.

| Value | Displayed as | Meaning |
| --- | --- | --- |
| `exact_law` | exact law | For every digit *d* the limit of *f*<sub>*N*</sub>(*d*) exists and its value is proved, for example 1/*b* for every digit, or 1/2, 0, 1/2 for *E*<sub>3</sub> in base 3. |
| `nontrivial_bound` | nontrivial bound | The exact law is not proved, but some digit *d* has a proved asymptotic bound that 0 ≤ *f*<sub>*N*</sub>(*d*) ≤ 1 does not give: lim inf *f*<sub>*N*</sub>(*d*) > 0, lim sup *f*<sub>*N*</sub>(*d*) < 1, or a proved separation of lim inf *f*<sub>*N*</sub>(*d*) or lim sup *f*<sub>*N*</sub>(*d*) from 1/*b*. The last case is what a proof of `proved_not_simply_normal` without an exact law gives. |
| `open` | open | Neither of the above. |

For families, `exact_law` and `nontrivial_bound` assert the property for every member, and the qualifiers `classified` (every member has an exact law or a nontrivial bound, with an explicit criterion stated in `summary` deciding which) and `partial` (an explicit subfamily stated in `summary` has an exact law or a nontrivial bound, other members are open) are also allowed.

A density-zero lower bound for the count of a digit, such as at least a constant times √*N* ones among the first *N* binary digits of √2, is not a nontrivial bound. A bound *D*⁺ < δ on the extreme discrepancy gives |*f*<sub>*N*</sub>(*d*) − 1/*b*| ≤ δ + *o*(1) for every digit, so it yields a nontrivial bound when δ < 1 − 1/*b* (then lim sup *f*<sub>*N*</sub>(*d*) < 1 for every digit; in base 2 this means δ < 1/2). A qualitative bound *D*⁺ < 1 without a value gives none.

## Per-radix records

`radix_results` is a list of inline tables, one per property and radix:

```toml
radix_results = [
  { radix = "base 2", property = "digit_frequency_status", status = "nontrivial_bound", evidence = "paper", source = "GF-20 part (4) with GF-27: …" },
]
```

| Key | Value |
| --- | --- |
| `radix` | `"base B"` for one integer *B* ≥ 2. |
| `property` | One of `full_normality`, `simple_normality`, `disjunctivity`, `discrepancy_status`, `digit_frequency_status`. |
| `status` | A constant value of that property other than `open` and `radix_dependent`. A record states a settled property; open properties are not recorded. |
| `evidence` | `lean`, `lean+paper`, `paper` or `external`: the label of the result named in `source`, for this property in this radix alone. |
| `source` | The result: registry identifiers from `registry_ids` with the statement used, and any written step, or a named published theorem with its year. |

A record serves one of two purposes.

- **Another radix.** A property settled in a radix outside the scope, or in one base of an `"all integer bases b ≥ 2"` scope, without overclaiming the scope. For example, simple nonnormality in base 3 while bases 2 and 10 stay open is a base-3 record, and `simple_normality` stays `open` at entry level. Such a record never changes an entry-level value.
- **Per-property evidence in the scope radix.** The entry-level `evidence` is the weakest label among the needed results. A record in the scope radix repeats the entry-level status and gives the current evidence of that property alone. For a property that the entry-level `evidence` covers (see [Evidence values](#evidence-values)) the record is never weaker than the entry-level label. An `external` record therefore means that the property currently rests on external input only (as for `BC-37`, `BC-47`, `BC-48`); the pre-program source of a control classification belongs in `control_provenance`, not here.

Every constant with `digit_frequency_status = nontrivial_bound` and a single-base scope has a scope-radix record for `digit_frequency_status`, since no entry-level field carries the evidence for that bound. This record may be weaker than the entry-level label, which does not cover it (for example `BC-29`).

## Fields of a `[[family]]` table

Every field is required and no other field is allowed.

| Field | Type | Meaning |
| --- | --- | --- |
| `id` | string | `BF-01`, `BF-02`, … in file order, consecutive from `BF-01`. |
| `name` | string | Human-readable name, unique in the file. |
| `definition` | string | The members of the family, with every parameter and hypothesis. |
| `radices_scope` | string | `"construction radix b"` (each member is studied in the radix that appears in its definition), `"base B"` for one integer *B* ≥ 2, or `"all integer bases b ≥ 2"`. |
| `full_normality` | enum | `proved_normal`, `proved_nonnormal`, `classified`, `partial` or `open`. |
| `simple_normality` | enum | `proved_simply_normal`, `proved_not_simply_normal`, `radix_dependent`, `classified`, `partial` or `open`. |
| `disjunctivity` | enum | `proved_disjunctive`, `proved_non_disjunctive`, `classified`, `partial` or `open`. |
| `discrepancy_status` | enum | `zero_normal`, `exact_positive`, `strict_upper_bound`, `maximal_K_b`, `classified`, `partial` or `open`. |
| `digit_frequency_status` | enum | `exact_law`, `nontrivial_bound`, `classified`, `partial` or `open`. |
| `barrier_status` | enum | `resolved`, `barrier_proved` or `no_barrier_recorded`. |
| `evidence` | enum | `lean`, `lean+paper`, `paper`, `external` or `open`. |
| `registry_ids` | list of strings | As for constants. May be empty. |
| `external_sources` | list of strings | As for constants. May be empty. |
| `summary` | string | What is proved, with registry identifiers inline. |
| `open_frontier` | string | The precise open questions. |

Families have no `radix_results` field; radix dependence inside a family is expressed by `classified` or `partial` and stated in `summary`.

## Status values

A family value without the `classified` or `partial` qualifier asserts the property for every member.

| Value | Displayed as | Meaning |
| --- | --- | --- |
| `proved_normal` | normal | *D*<sub>*N*</sub> → 0 along all prefix lengths *N*. |
| `proved_nonnormal` | nonnormal | Not normal. |
| `proved_simply_normal` | simply normal | Every digit has limiting frequency 1/*b*. |
| `proved_not_simply_normal` | not simply normal | Some digit has no limiting frequency 1/*b*. |
| `radix_dependent` | depends on radix | Simple normality is proved in some radices of the scope and disproved in the others. |
| `proved_disjunctive` | disjunctive | Every finite word over the digit alphabet occurs. |
| `proved_non_disjunctive` | not disjunctive | Some finite word never occurs. |
| `zero_normal` | *D*<sub>*N*</sub> → 0 | Equivalent to normality. |
| `exact_positive` | exact *D*<sub>∞</sub> ∈ (0, 1) | lim *D*<sub>*N*</sub> exists and is computed exactly. |
| `strict_upper_bound` | *D*⁺ < 1 | An explicit or qualitative bound *D*⁺ < 1 is proved and normality is not. |
| `maximal_K_b` | *D*<sub>*N*</sub> → 1 (in *K*<sub>*b*</sub>) | Membership in the numerical translation kernel. |
| `exact_law` | exact law | See [Digit frequencies](#digit-frequencies). |
| `nontrivial_bound` | nontrivial bound | See [Digit frequencies](#digit-frequencies). |
| `classified` | classified | The property is decided for every member by an explicit criterion stated in `summary`. |
| `partial` | partial | The property is decided for an explicit subfamily stated in `summary` and open for other members. |
| `open` | open | Not settled. |
| `resolved` | resolved | Full normality is decided (`proved_normal`, `proved_nonnormal` or `classified`) and `discrepancy_status` is neither `open` nor `partial`. |
| `barrier_proved` | barrier proved | A registry entry proves a rigorous limitation of a method for an unsettled property. |
| `no_barrier_recorded` | none recorded | Neither of the above. |

## Evidence values

`evidence` is the label of the **weakest** result needed for the non-`open` values among the fields it covers. It always covers `full_normality`, `simple_normality`, `disjunctivity` and `discrepancy_status`. It also covers `digit_frequency_status` for every family and for every constant with scope `"all integer bases b ≥ 2"`, since no single-radix record can carry an all-bases or family-wide digit-frequency result. For a constant with a single-base scope, `digit_frequency_status = exact_law` is proved together with the `simple_normality` value it decides and is covered by `evidence`, while the evidence of a `nontrivial_bound` is recorded in a scope-radix `radix_results` record. Barriers do not enter `evidence`; their evidence is that of the registry entries listed. The order from strongest to weakest is `lean`, `lean+paper`, `paper`, `external`. Instantiating the parameters of a registry statement, and passing between *x* and *b*<sup>*k*</sup>*x* + *m* for integers *k* and *m* (which only shifts the digit sequence), are not separate steps. Any other written derivation, even a short one such as reading digit positions off a series or deducing disjunctivity from *D*⁻ = 0, counts as a paper step: an entry that needs such a derivation has evidence at most `paper` unless a listed registry entry contains it.

| Value | Evidence label | Meaning |
| --- | --- | --- |
| `lean` | Kernel-verified | Every needed result is a registry entry with status `lean` that states the conclusion for this entry. |
| `lean+paper` | Lean-supported paper proof | The weakest needed result is a listed registry entry with status `lean+paper`. |
| `paper` | Paper proof | The weakest needed result is a listed registry entry with status `paper`, or a written step not recorded as a separate entry. |
| `external` | External input | A status itself is a published or released theorem cited as a black box and not proved in the repository, named in `external_sources`. |
| `open` | Open | Every covered field is `open`: all five distributional fields for families and all-bases constants, the four status fields for single-base constants. |

Published theorems used as ingredients inside a registry proof (the registry `inputs` field) do not make the evidence `external`; they are named in `external_sources` and keep the label of the registry proof that uses them. `external_sources` also records the sources of `arithmetic_nature` and the classical literature on the entry. Registry status `computation` (Finite certificate) never supports a benchmark status.

## Mechanical checks

`python3 scripts/portal.py check` rejects a benchmark file unless all of the following hold.

1. The file parses as TOML, `[meta]` has exactly the keys listed above with the stated values (`schema_version = 2`), and every entry has exactly the required fields with the stated types.
2. Identifiers are consecutive in file order: `BC-01` … `BC-50` with exactly 50 constants, and `BF-01` … `BF-NN` for families. Names are unique within each file.
3. Every enum field takes one of the values allowed for its file. `category` is a listed key. `radices_scope` matches one of the allowed patterns.
4. Every identifier in `registry_ids` exists in `docs/registry/*.toml` and does not have status `withdrawn` or `computation`.
5. No string field, including every `radix_results` and `control_provenance` string, contains a backslash, `$`, `*`, a backtick or `|`. These keep TeX out of the data and keep the generated Markdown tables intact. Use ∗ (U+2217) for Dirichlet convolution, ∣ (U+2223) for divisibility and ‖·‖ for distances.
6. Implications between status values:
   - `full_normality = proved_normal` if and only if `discrepancy_status = zero_normal`, and then `simple_normality = proved_simply_normal` and `disjunctivity = proved_disjunctive`.
   - `discrepancy_status` ∈ {`exact_positive`, `maximal_K_b`} implies `full_normality = proved_nonnormal`.
   - `simple_normality = proved_not_simply_normal` or `disjunctivity = proved_non_disjunctive` implies `full_normality = proved_nonnormal`.
   - For constants, `simple_normality = radix_dependent` requires `radices_scope = "all integer bases b ≥ 2"`.
   - `barrier_status = resolved` requires `full_normality` ∈ {`proved_normal`, `proved_nonnormal`, `classified`} and `discrepancy_status` ∉ {`open`, `partial`}.
7. Digit-frequency consistency:
   - `simple_normality = proved_simply_normal` implies `digit_frequency_status = exact_law`.
   - `simple_normality = proved_not_simply_normal` implies `digit_frequency_status` ∈ {`exact_law`, `nontrivial_bound`} (for families also `classified`).
   - `simple_normality` ∈ {`radix_dependent`, `classified`} implies `digit_frequency_status` ∈ {`exact_law`, `nontrivial_bound`, `classified`}, and `simple_normality = partial` implies `digit_frequency_status ≠ open`.
   - `digit_frequency_status = exact_law` implies `simple_normality` ∉ {`open`, `partial`}.
   - Together with rule 6, `full_normality = proved_normal` implies `digit_frequency_status = exact_law`, and `digit_frequency_status = open` implies `simple_normality = open`.
8. Evidence consistency:
   - `evidence = open` if and only if every field covered by `evidence` is `open`: for families and for constants with scope `"all integer bases b ≥ 2"` the five distributional fields including `digit_frequency_status`, for single-base constants the four status fields (a single-base `nontrivial_bound` carries its evidence in a record, rule 11). In particular a family or an all-bases constant with a digit-frequency result and four `open` status fields has a non-`open` `evidence`, and an all-bases `nontrivial_bound` is never left without evidence.
   - `evidence` ∈ {`lean`, `lean+paper`, `paper`} requires a nonempty `registry_ids`; `evidence = lean` requires a listed entry of registry status `lean`, and `evidence = lean+paper` a listed entry of registry status `lean+paper`.
   - `evidence = external` requires a nonempty `external_sources`.
   - `barrier_status = barrier_proved` requires a nonempty `registry_ids`.
9. Every constant has a nonempty `external_sources`, and every `external_sources` string, in both files, contains a four-digit year.
10. Every registry identifier mentioned in any string field (a token such as `CC-49` with one of the registry prefixes) exists in `docs/registry/*.toml`, and every benchmark identifier mentioned (`BC-…` or `BF-…`) exists in the benchmark files.
11. Per-radix records (`radix_results`, constants only):
    - Each record has exactly the keys `radix`, `property`, `status`, `evidence`, `source`, all strings; `radix` is `"base B"`; `status` is allowed for `property` and is neither `open` nor `radix_dependent`; `evidence` is not `open`; `source` is nonempty; no (`radix`, `property`) pair repeats.
    - Every registry identifier in `source` is listed in the entry's `registry_ids`. `evidence` ∈ {`lean`, `lean+paper`, `paper`} requires at least one such identifier; `evidence = lean` requires every named entry to have registry status `lean`; `evidence = lean+paper` requires named entries of status `lean` or `lean+paper`, at least one `lean+paper`. `evidence = external` requires a four-digit year in `source`.
    - A record in the scope radix has the entry-level value of its property. With scope `"all integer bases b ≥ 2"`, a record agrees with any entry-level value other than `open` and `radix_dependent`.
    - A record in the scope radix for a property covered by the entry-level `evidence` has an evidence label at least as strong as the entry-level one (order `lean`, `lean+paper`, `paper`, `external`).
    - The records for one radix outside the scope satisfy the implications of rules 6 and 7 among themselves: a negative simple normality, disjunctivity or discrepancy value (`exact_positive`, `maximal_K_b`) requires a `full_normality = proved_nonnormal` record for that radix; `proved_normal` excludes conflicting values; `zero_normal` requires `proved_normal`; `proved_simply_normal` excludes a `digit_frequency_status` other than `exact_law`; `digit_frequency_status = exact_law` requires a `simple_normality` record for that radix.
    - `digit_frequency_status = nontrivial_bound` with a single-base scope requires a scope-radix record for `digit_frequency_status`.
    - `simple_normality = radix_dependent` requires records proving simple normality in one base and disproving it in another.
12. Cohorts (constants only): `cohort = control` exactly for the eight identifiers listed under [Cohorts](#cohorts). A control constant has a single-base scope and `full_normality` ∈ {`proved_normal`, `proved_nonnormal`}. `control_provenance` is `{}` for an unresolved constant; for a control constant it has exactly the four string keys of [Control provenance](#control-provenance), its `basis` is the fixed basis of that constant, it records `full_normality` (`proved_normal` or `proved_nonnormal`) or `simple_normality = proved_not_simply_normal` (never `proved_simply_normal`) with the entry-level value, and its `source` is nonempty. On basis (a) the `source` names no registry entry, contains a four-digit year, every year in it precedes 2026 (so an incidental number such as 1729 inside a 2026 citation does not qualify), and every year in it belongs to an entry of `external_sources` whose years all precede 2026.

`python3 -m unittest scripts/test_benchmarks.py` exercises each of these checks on modified copies of the data. The progress-table generator also refuses to count an unresolved target whose qualifying property has no recorded evidence, so such a property is never credited to external input.

## Generated progress table

`docs/benchmarks/progress.md` contains, in this order:

1. The `status_as_of` value and the evidence-label legend.
2. One summary table for the 50 constants with one row per objective: the number of constants with `full_normality` or `simple_normality` proved positive (Objective 1); with `proved_nonnormal`, `proved_not_simply_normal`, `proved_non_disjunctive` or `maximal_K_b` (Objective 2); with `discrepancy_status` other than `open` (Objective 3); with `digit_frequency_status` other than `open` (Objective 3, digit frequencies); and with `barrier_status = barrier_proved` (Objective 4). A count of constants with all five distributional fields (the four status fields and `digit_frequency_status`) `open` follows. The objective rows overlap and do not sum to 50: Euler's product *E*<sub>2</sub> (`BC-27`), for example, is proved simply normal (Objective 1), proved nonnormal (Objective 2) and in *K*<sub>2</sub> (Objective 3).
3. The cohort breakdown: the same objective rows counted separately for the 8 control/reference constants and the 42 initially unresolved targets. A target's count is split into results credited to repository registry entries (some qualifying property has evidence `lean`, `lean+paper` or `paper`, using a scope-radix `radix_results` record where one exists and the entry-level `evidence` where it covers the property) and results resting on external input only (every qualifying property has evidence `external`). Objective 4 counts are always registry results. A second table lists the control constants by basis, the control constants whose normality is also proved in the repository, and the unresolved targets whose scope-radix normality is now decided, split by whether that decision has repository or external evidence. A third table lists each control constant's `control_provenance` (basis, property, status, pre-program source) beside the current repository evidence for the same property.
4. A per-category count table, including the number of control constants, of constants with a digit-frequency law or bound, and of constants with all five distributional fields `open`.
5. The constant table, one row per constant, with columns ID, name, cohort, scope, normality, simple normality, disjunctivity, discrepancy, digit frequencies, barrier, evidence and registry links, using the display labels above.
6. The per-radix table, one row per `radix_results` record, with columns ID, name, radix, property, status, evidence and source. Pre-program control classifications do not appear in it.
7. The family table with the same status columns, `name` in place of the constant name, and `open_frontier` as the last column.

Every registry identifier in the generated tables links to its anchor in [docs/results.md](../results.md).
