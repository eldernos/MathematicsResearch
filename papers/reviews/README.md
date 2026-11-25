# Manuscript review record

This directory records independent AI-assisted checks of the five manuscripts. Each pair of reviewers received the same identified manuscript revision and the underlying mathematical sources. Gemini 4 Neon and Claude Sonnet 5.5 were each asked to check:

- Exact theorem statements, proof steps, correspondence to Lean and the scope of external inputs.
- Specific antecedents, bibliography details and evidence supporting any priority claim.
- Professional mathematical exposition, including redundant summaries, conversational transitions, imprecise language and distracting stylistic devices.
- Consistency of the PDF, figures, notation and theorem references.

The reports identify source locations for findings. The resolution record lists the changes made after review and any questions reserved for a human mathematician. Internal model review is recorded separately from external peer review. [Manuscript index](../README.md)

| Manuscript | Reviewed author revision | Gemini 4 Neon | Sonnet 5.5 | Release changes |
| --- | --- | --- | --- | --- |
| I · Stoneham polynomials | [a9d9166](https://github.com/eldernos/MathematicsResearch/commit/a9d9166e40aab0b9b85af0fdc9b967f87cd3b606) | [Report](01-stoneham-polynomials/gemini.md) | [Report](01-stoneham-polynomials/sonnet.md) | [Disposition](01-stoneham-polynomials/resolution.md) |
| II · Localized normality | [9796812](https://github.com/eldernos/MathematicsResearch/commit/9796812804e0e22f6adb49436a8ff98cb8814c07) | [Report](02-localized-normality/gemini.md) | [Report](02-localized-normality/sonnet.md) | [Disposition](02-localized-normality/resolution.md) |
| III · Signed resonance | [43bbe0e](https://github.com/eldernos/MathematicsResearch/commit/43bbe0e4edefc489582a759aadb3c26caf2328b0) | [Report](03-signed-resonance/gemini.md) | [Report](03-signed-resonance/sonnet.md) | [Disposition](03-signed-resonance/resolution.md) |
| IV · Arithmetic certificates | [74ece55](https://github.com/eldernos/MathematicsResearch/commit/74ece558e91dc248420752ec0e63cfb03387251a) | [Report](04-arithmetic-certificates/gemini.md) | [Report](04-arithmetic-certificates/sonnet.md) | [Disposition](04-arithmetic-certificates/resolution.md) |
| V · Classical denominators | [28186f0](https://github.com/eldernos/MathematicsResearch/commit/28186f0e08ea889827b489f03f1c213456581c91) | [Report](05-classical-denominators/gemini.md) | [Report](05-classical-denominators/sonnet.md) | [Disposition](05-classical-denominators/resolution.md) |

## manuscripts-v2.0.0 review record

Each manuscript was reviewed by AI models from a different provider than its writer, using the same identified revision and the underlying sources. The report header gives the reviewed commit. Each resolution records every finding as accepted, partly accepted or declined, with the change made, and ends with the questions reserved for a human specialist. First-batch manuscripts received two reviews. **These are AI model reviews, not independent human peer review.**

| Manuscript | Writer | Review 1 | Review 2 | Resolution |
| --- | --- | --- | --- | --- |
| VI · Multiplicative Lambert series | Claude Opus 5.5 | [GPT-6.2 Astra](06-multiplicative-lambert/review-1.md) | [Gemini 4 Argon](06-multiplicative-lambert/review-2.md) | [Claude Opus 5.5](06-multiplicative-lambert/resolution.md) |
| I · Stoneham polynomials v2.0 | GPT-6.2 Astra | [Claude Opus 5.5](01-stoneham-polynomials-v2/review-1.md) | [Gemini 4 Argon](01-stoneham-polynomials-v2/review-2.md) | [GPT-6.2 Astra](01-stoneham-polynomials-v2/resolution.md) |
| VII · Synthetic expansions | Claude Opus 5.5 | [GPT-6.2 Astra](07-synthetic-expansions/review-1.md) | [Gemini 4 Argon](07-synthetic-expansions/review-2.md) | [Claude Opus 5.5](07-synthetic-expansions/resolution.md) |
| X · Arithmetic of extreme discrepancy | Claude Opus 5.5 | [Gemini 4 Argon](10-discrepancy-arithmetic/review-1.md) | [Gemini 4 Neon](10-discrepancy-arithmetic/review-2.md) | [Claude Sonnet 5.5](10-discrepancy-arithmetic/resolution.md) |
| VIII · Stoneham product orbits | GPT-6.2 Astra, Gemini 4 Neon | [Claude Sonnet 5.5](08-stoneham-product-orbits/review-1.md) | — | [Gemini 4 Neon](08-stoneham-product-orbits/resolution.md) |
| II · Localized normality v2.0 | Claude Sonnet 5.5 | [GPT-6.2 Sol](02-localized-normality-v2/review-1.md) | — | [Claude Sonnet 5.5](02-localized-normality-v2/resolution.md) |
| V · Classical denominators v2.0 | GPT-6.2 Sol | [Claude Sonnet 5.5](05-classical-denominators-v2/review-1.md) | — | [Claude Sonnet 5.5](05-classical-denominators-v2/resolution.md) |
| IV · Arithmetic certificates v2.0 | GPT-6.2 Sol, Gemini 4 Neon | [GPT-6.2 Sol](04-arithmetic-certificates-v2/review-1.md) | — | [Gemini 4 Neon](04-arithmetic-certificates-v2/resolution.md) |
| IX · Erdős–Borwein note | Claude Sonnet 5.5 | [Gemini 4 Neon](09-erdos-borwein-note/review-1.md) | — | [Claude Sonnet 5.5](09-erdos-borwein-note/resolution.md) |
| III · Signed resonance v1.2 | named-author edition, mathematics unchanged | [Gemini 4 Neon (v1.1)](03-signed-resonance/gemini.md) | [Sonnet 5.5 (v1.1)](03-signed-resonance/sonnet.md) | [v1.1 disposition](03-signed-resonance/resolution.md) |
