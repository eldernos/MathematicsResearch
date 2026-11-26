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
- A status changes only when a result establishes it: a registry entry (listed in `registry_ids`) or a named published theorem (listed in `external_sources`). If an error is found, the status reverts and the entry records the correction.
- Finite computations, conditional theorems, heuristics and cross-model reviews never change a status. They may be mentioned in `notes`, `summary` or `open_frontier` with their scope.

## Top-level `[meta]` table

Both files begin with a `[meta]` table.

| Key | File | Value |
| --- | --- | --- |
| `schema_version` | both | The integer `1`. |
| `status_as_of` | both | The research phase whose verified results the statuses reflect, for example `"Phase 21"`. |
| `roster_size` | constants | The integer `50`. |

## Fields of a `[[constant]]` table

Every field is required and no other field is allowed.

| Field | Type | Meaning |
| --- | --- | --- |
| `id` | string | `BC-01` … `BC-50`, in file order, each exactly once. |
| `name` | string | Human-readable name, unique in the file. Plain Unicode, for example `"π"`, `"ln 2"`, `"Euler's product E_2"`. |
| `formula` | string | A definition in plain Unicode. |
| `category` | enum | One of the category keys below. |
| `arithmetic_nature` | string | The proved arithmetic status with its source, for example `"transcendental (Lindemann 1882)"` or `"irrational (Apéry 1978); transcendence open"`. Every constant is proved irrational. |
| `radices_scope` | string | `"base B"` for one integer *B* ≥ 2, or `"all integer bases b ≥ 2"`. The four status fields refer to this scope (see below). |
| `full_normality` | enum | `proved_normal`, `proved_nonnormal` or `open`. |
| `simple_normality` | enum | `proved_simply_normal`, `proved_not_simply_normal`, `radix_dependent` or `open`. |
| `disjunctivity` | enum | `proved_disjunctive`, `proved_non_disjunctive` or `open`. |
| `discrepancy_status` | enum | `zero_normal`, `exact_positive`, `strict_upper_bound`, `maximal_K_b` or `open`. |
| `barrier_status` | enum | `resolved`, `barrier_proved` or `no_barrier_recorded`. |
| `evidence` | enum | `lean`, `lean+paper`, `paper`, `external` or `open`. |
| `discrepancy_summary` | string | What is proved about *D*<sub>*N*</sub>, *D*⁺, *D*⁻ and digit frequencies, and what is open. |
| `registry_ids` | list of strings | Registry identifiers (`docs/registry/*.toml`) that prove a status, a barrier or a structural reduction for this constant. May be empty. Comparative cross-references mentioned only in `notes`, `summary` or `open_frontier` need not be listed here. |
| `external_sources` | list of strings | Published or released theorems used, each naming the author(s), the year (a four-digit year, with a release date or commit for software releases) and the statement. At least one entry, which supports `arithmetic_nature`. |
| `notes` | string | Exact scope, the main open question and the key barrier. |

**Scope of the status fields.** With `radices_scope = "base B"` a status refers to base *B* only. With `"all integer bases b ≥ 2"`, `proved_normal` means normal in every integer base (absolutely normal), `proved_nonnormal` means nonnormal in every integer base, and `open` means that the property is not settled in any integer base.

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
| `barrier_status` | enum | `resolved`, `barrier_proved` or `no_barrier_recorded`. |
| `evidence` | enum | `lean`, `lean+paper`, `paper`, `external` or `open`. |
| `registry_ids` | list of strings | As for constants. May be empty. |
| `external_sources` | list of strings | As for constants. May be empty. |
| `summary` | string | What is proved, with registry identifiers inline. |
| `open_frontier` | string | The precise open questions. |

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
| `classified` | classified | The property is decided for every member by an explicit criterion stated in `summary`. |
| `partial` | partial | The property is decided for an explicit subfamily stated in `summary` and open for other members. |
| `open` | open | Not settled. |
| `resolved` | resolved | Full normality is decided (`proved_normal`, `proved_nonnormal` or `classified`) and `discrepancy_status` is neither `open` nor `partial`. |
| `barrier_proved` | barrier proved | A registry entry proves a rigorous limitation of a method for an unsettled property. |
| `no_barrier_recorded` | none recorded | Neither of the above. |

## Evidence values

`evidence` is the label of the **weakest** result needed for the non-`open` values among `full_normality`, `simple_normality`, `disjunctivity` and `discrepancy_status`. Barriers do not enter it; their evidence is that of the registry entries listed. The order from strongest to weakest is `lean`, `lean+paper`, `paper`, `external`. Instantiating the parameters of a registry statement, and passing between *x* and *b*<sup>*k*</sup>*x* + *m* for integers *k* and *m* (which only shifts the digit sequence), are not separate steps. Any other written derivation, even a short one such as reading digit positions off a series or deducing disjunctivity from *D*⁻ = 0, counts as a paper step: an entry that needs such a derivation has evidence at most `paper` unless a listed registry entry contains it.

| Value | Evidence label | Meaning |
| --- | --- | --- |
| `lean` | Kernel-verified | Every needed result is a registry entry with status `lean` that states the conclusion for this entry. |
| `lean+paper` | Lean-supported paper proof | The weakest needed result is a listed registry entry with status `lean+paper`. |
| `paper` | Paper proof | The weakest needed result is a listed registry entry with status `paper`, or a written step not recorded as a separate entry. |
| `external` | External input | A status itself is a published or released theorem cited as a black box and not proved in the repository, named in `external_sources`. |
| `open` | Open | All four status fields are `open`. |

Published theorems used as ingredients inside a registry proof (the registry `inputs` field) do not make the evidence `external`; they are named in `external_sources` and keep the label of the registry proof that uses them. `external_sources` also records the sources of `arithmetic_nature` and the classical literature on the entry. Registry status `computation` (Finite certificate) never supports a benchmark status.

## Mechanical checks

`python3 scripts/portal.py check` rejects a benchmark file unless all of the following hold.

1. The file parses as TOML, `[meta]` has exactly the keys listed above with the stated values, and every entry has exactly the required fields with the stated types.
2. Identifiers are consecutive in file order: `BC-01` … `BC-50` with exactly 50 constants, and `BF-01` … `BF-NN` for families. Names are unique within each file.
3. Every enum field takes one of the values allowed for its file. `category` is a listed key. `radices_scope` matches one of the allowed patterns.
4. Every identifier in `registry_ids` exists in `docs/registry/*.toml` and does not have status `withdrawn` or `computation`.
5. No string field contains a backslash, `$`, `*`, a backtick or `|`. These keep TeX out of the data and keep the generated Markdown tables intact. Use ∗ (U+2217) for Dirichlet convolution, ∣ (U+2223) for divisibility and ‖·‖ for distances.
6. Implications between status values:
   - `full_normality = proved_normal` if and only if `discrepancy_status = zero_normal`, and then `simple_normality = proved_simply_normal` and `disjunctivity = proved_disjunctive`.
   - `discrepancy_status` ∈ {`exact_positive`, `maximal_K_b`} implies `full_normality = proved_nonnormal`.
   - `simple_normality = proved_not_simply_normal` or `disjunctivity = proved_non_disjunctive` implies `full_normality = proved_nonnormal`.
   - For constants, `simple_normality = radix_dependent` requires `radices_scope = "all integer bases b ≥ 2"`.
   - `barrier_status = resolved` requires `full_normality` ∈ {`proved_normal`, `proved_nonnormal`, `classified`} and `discrepancy_status` ∉ {`open`, `partial`}.
7. Evidence consistency:
   - `evidence = open` if and only if the four status fields are all `open`.
   - `evidence` ∈ {`lean`, `lean+paper`, `paper`} requires a nonempty `registry_ids`; `evidence = lean` requires a listed entry of registry status `lean`, and `evidence = lean+paper` a listed entry of registry status `lean+paper`.
   - `evidence = external` requires a nonempty `external_sources`.
   - `barrier_status = barrier_proved` requires a nonempty `registry_ids`.
8. Every constant has a nonempty `external_sources`, and every `external_sources` string, in both files, contains a four-digit year.
9. Every registry identifier mentioned in any string field (a token such as `CC-49` with one of the registry prefixes) exists in `docs/registry/*.toml`, and every benchmark identifier mentioned (`BC-…` or `BF-…`) exists in the benchmark files.

## Generated progress table

`docs/benchmarks/progress.md` contains, in this order:

1. The `status_as_of` value and the evidence-label legend.
2. One summary table for the 50 constants with one row per objective: the number of constants with `full_normality` or `simple_normality` proved positive (Objective 1); with `proved_nonnormal`, `proved_not_simply_normal`, `proved_non_disjunctive` or `maximal_K_b` (Objective 2); with `discrepancy_status` other than `open` (Objective 3); and with `barrier_status = barrier_proved` (Objective 4). A count of constants with all four status fields `open` follows. The objective rows overlap and do not sum to 50: Euler's product *E*<sub>2</sub> (`BC-27`), for example, is proved simply normal (Objective 1), proved nonnormal (Objective 2) and in *K*<sub>2</sub> (Objective 3).
3. A per-category count table.
4. The constant table, one row per constant, with columns ID, name, scope, normality, simple normality, disjunctivity, discrepancy, barrier, evidence and registry links, using the display labels above.
5. The family table with the same columns, `name` in place of the constant name, and `open_frontier` as the last column.

Every registry identifier in the generated tables links to its anchor in [docs/results.md](../results.md).
