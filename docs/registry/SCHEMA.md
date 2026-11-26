# Result registry format

The curated result index [docs/results.md](../results.md) is generated from the TOML files in this directory by `python3 scripts/portal.py build`. Do not edit `docs/results.md` by hand.

Identifiers are editorial and permanent. They stay attached to a mathematical statement when its Lean declaration moves or is renamed. A withdrawn identifier is kept with `status = "withdrawn"` and is never reassigned.

| Prefix | Family | Manuscript |
| --- | --- | --- |
| ST | Stoneham polynomial images and products | [papers/01-stoneham-polynomials](../../papers/01-stoneham-polynomials) |
| LS | Localized logarithms and polylogarithms | [papers/02-localized-normality](../../papers/02-localized-normality) |
| MW | Polynomial weights and masked supports | [papers/02-localized-normality](../../papers/02-localized-normality) |
| CR | Cyclotomic resonance and finite combinations | [papers/03-signed-resonance](../../papers/03-signed-resonance) |
| DS | Exact discrepancy and symbolic spectra | [papers/03-signed-resonance](../../papers/03-signed-resonance) |
| AC | Rational-orbit certificates, coverage and rigidity | [papers/04-arithmetic-certificates](../../papers/04-arithmetic-certificates) |
| CC | Classical constant arithmetic | [papers/05-classical-denominators](../../papers/05-classical-denominators) |
| SY | Synthetic expansions and translations | [papers/07-synthetic-expansions](../../papers/07-synthetic-expansions) (candidate; research record in [Phase 18](../../notes/phase18/README.md)) |
| OP | Arithmetic of discrepancy and unrestricted prime support | [Phase 19 research](../../notes/phase19/README.md) |
| GF | Arithmetic generating functions and transfer | [Phase 20 research](../../notes/phase20/README.md) |

## Fields of a `[[result]]` table

| Field | Required | Meaning |
| --- | --- | --- |
| `id` | yes | Identifier such as `ST-01`. The prefix fixes the family. SY, OP and GF record research preceding a manuscript release. |
| `title` | yes | A short name of the result, readable without notation. |
| `topic` | yes | One of the topic keys listed below. |
| `principal` | no | `true` for results featured in the README. |
| `status` | yes | `lean`, `lean+paper`, `paper`, `computation`, `pending` or `withdrawn`. |
| `statement` | yes | Precise statement in GitHub Markdown. Italic variables, Unicode relations and fenced `math` blocks with elementary TeX only. |
| `scope` | yes | Exact hypotheses, conventions and what the result does not claim. |
| `lean` | if Lean | Fully qualified declaration names. The first is the main declaration. Each must exist in `docs/data/declarations.json` or in a module source. |
| `proof` | yes | Repository paths, optionally with anchors, to human-readable proofs. |
| `inputs` | if any | External theorems used on paper, with the name of the source. |
| `computation` | if any | Scripts or Lean evaluations that perform a finite computation. |
| `supersedes` | no | Declarations or identifiers of weaker earlier results that this one implies. |
| `related` | no | Other identifiers. |
| `figures` | no | Figure slugs from `assets/figures/figures.json`. |

### Status values

- `lean`: the statement is a kernel-checked Lean theorem whose axioms are among `propext`, `Classical.choice` and `Quot.sound`.
- `lean+paper`: the core is kernel-checked and the stated conclusion follows by a short written deduction, possibly from a named external theorem in `inputs`.
- `paper`: a written proof in the repository; no corresponding Lean theorem.
- `computation`: an exact finite computation; it establishes only the finite statement given.
- `pending`: a formal proof is in progress; the entry names the intended declaration.

### Topic keys

`stoneham`, `localized`, `weights`, `resonance`, `discrepancy`, `certificates`, `coverage`, `classical`, `counterexamples`.

A result has one topic. Counterexamples and impossibility results keep the identifier of their family and use the `counterexamples` topic.

## `[[paper]]` tables (`papers.toml`)

Required: `number`, `dir`, `title`, `status`, `principal` (identifiers), `families` and, for every entry, `version`, `release` and `tags`.

| Field | Meaning |
| --- | --- |
| `number` | Roman numeral. A revision keeps the numeral of the paper it replaces; new papers continue the sequence. |
| `version`, `release`, `tags` | Manuscript version; the release tag that carries this text; every release tag that contains the directory. The v1.1 entries have `release = "manuscripts-v1.1.0"`; the candidate entries have `release = "manuscripts-v2.0.0"`. |
| `supersedes` | Directory of the version this entry replaces, or `""`. The superseded entry stays as the historical record and its files are never edited. An entry that nothing supersedes is *current*. |
| `families`, `results` | Registry prefixes mapped to the manuscript, and extra identifiers that map to it regardless of family. Only current manuscripts are shown as the "Paper" of a result. |
| `abstract`, `summary` | `abstract` for released manuscripts. `summary` is a one-sentence description used only until the manuscript's `metadata.toml` exists. |
| `keywords`, `msc_primary`, `msc_secondary` | Classification of a released manuscript that has no `metadata.toml`. |

Each wave-2 manuscript directory also holds a `metadata.toml` with the keys `id`, `title`, `short_title`, `version`, `status` (`"preprint draft"`), `abstract`, `keywords`, `msc_primary`, `msc_secondary` (MSC2020), `supersedes`, `lean_commit` and `registry_ids`. When the file is present it overrides the title, abstract, keywords and results of the registry entry, and `python3 scripts/portal.py check` validates it: all keys, the version, the pinned Lean commit, MSC code syntax, registry identifiers and the absence of any claim of peer review. `python3 scripts/portal.py check --strict` also requires the files listed by the contract (`paper.pdf`, `VERIFICATION.md`, `LEDGER.md`, `submission/`). The README table, `docs/results.md`, `papers/BIBLIOGRAPHY.bib` and the research site ([docs/site.md](../site.md)) are built from these files.

The `status` of a registry entry is one of `planned`, `draft`, `internally reviewed`, `external review` or `published`. The canonical publication status is [papers/README.md](../../papers/README.md). The registry copy must not claim peer review or acceptance.
