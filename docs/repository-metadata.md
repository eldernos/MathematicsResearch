# Repository metadata proposal

**Status: proposal for owner approval. The commands below have not been run.** They change the public GitHub repository settings (description, homepage, topics), which are outward-facing, so the owner runs them after approval.

## Current values

Read-only query on 2026-11-25:

```sh
gh repo view eldernos/MathematicsResearch --json description,homepageUrl,repositoryTopics
```

```json
{
  "description": "AI-assisted mathematical research on normal numbers, digit discrepancy, Stoneham constants, and arithmetic expansions, with Lean 4 proofs and reproducible preprints.",
  "homepageUrl": "",
  "repositoryTopics": null
}
```

The description already matches the proposed text. No homepage and no topics are set.

## Proposed values

**Description** (unchanged):

> AI-assisted mathematical research on normal numbers, digit discrepancy, Stoneham constants, and arithmetic expansions, with Lean 4 proofs and reproducible preprints.

**Homepage:** `https://eldernos.github.io/MathematicsResearch/`. Set it only after GitHub Pages is enabled and the first deployment has succeeded ([site.md](site.md)); until then the address does not resolve.

**Topics** (17, lowercase, within GitHub's limit of 20):

`mathematics`, `number-theory`, `analytic-number-theory`, `normal-numbers`, `uniform-distribution`, `discrepancy-theory`, `stoneham-numbers`, `lambert-series`, `transcendental-numbers`, `diophantine-approximation`, `p-adic-numbers`, `ergodic-theory`, `lean4`, `mathlib`, `formal-verification`, `formalized-mathematics`, `ai-assisted-research`.

## Commands for the owner

Run from any directory with the GitHub CLI authenticated as the repository owner. Review the output of `gh repo view` afterwards.

```sh
gh repo edit eldernos/MathematicsResearch \
  --description "AI-assisted mathematical research on normal numbers, digit discrepancy, Stoneham constants, and arithmetic expansions, with Lean 4 proofs and reproducible preprints." \
  --homepage "https://eldernos.github.io/MathematicsResearch/" \
  --add-topic mathematics \
  --add-topic number-theory \
  --add-topic analytic-number-theory \
  --add-topic normal-numbers \
  --add-topic uniform-distribution \
  --add-topic discrepancy-theory \
  --add-topic stoneham-numbers \
  --add-topic lambert-series \
  --add-topic transcendental-numbers \
  --add-topic diophantine-approximation \
  --add-topic p-adic-numbers \
  --add-topic ergodic-theory \
  --add-topic lean4 \
  --add-topic mathlib \
  --add-topic formal-verification \
  --add-topic formalized-mathematics \
  --add-topic ai-assisted-research
```

To set only the topics and description now, and the homepage later, drop the `--homepage` line and run `gh repo edit eldernos/MathematicsResearch --homepage "https://eldernos.github.io/MathematicsResearch/"` after the site is live.

To check the result:

```sh
gh repo view eldernos/MathematicsResearch --json description,homepageUrl,repositoryTopics
```

## Related owner actions

- Enable GitHub Pages with the Actions source ([site.md](site.md)).
- Decide the manuscript licence ([licensing-proposal.md](licensing-proposal.md)).
- Publish the release `manuscripts-v2.0.0` only after the manuscripts, checksums and `CITATION.cff` are approved ([papers/ARCHIVING.md](../papers/ARCHIVING.md)).
