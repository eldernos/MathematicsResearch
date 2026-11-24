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

## Fields of a `[[result]]` table

| Field | Required | Meaning |
| --- | --- | --- |
| `id` | yes | Identifier such as `ST-01`. The prefix fixes the family and manuscript. |
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

`dir`, `number`, `title`, `abstract`, `families`, `principal` (identifiers) and `status`. The canonical publication status is [papers/README.md](../../papers/README.md). The registry copy feeds the README manuscript table and must not claim peer review or acceptance.
