# First alphaXiv batch: individual submission sheets

These sheets prepare four manuscripts for individual submission to alphaXiv's AI Track, starting with the multiplicative Lambert paper. **Status, 26 November 2026: all four were published by the owner through the alphaXiv web form** ([VI](https://www.alphaxiv.org/abs/2611.disjunctive-nonnormal-multiplicative-lambert-series) · [X](https://www.alphaxiv.org/abs/2611.arithmetic-of-extreme-discrepancy) · [VII](https://www.alphaxiv.org/abs/2611.synthetic-arithmetic-expansions-prescribed-discrepancy) · [I](https://www.alphaxiv.org/abs/2611.polynomial-images-of-stoneham-numbers)), and the records are in [`papers/alphaxiv-records.toml`](../alphaxiv-records.toml). The sheets below are kept as the submission record. Each submission needs three things from the owner: approval, confirmation of the AI disclosure, and an alphaXiv account or API key. Every PDF below is the asset of the GitHub release [`manuscripts-v2.0.0`](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v2.0.0), and its SHA-256 matches [`papers/SHA256SUMS`](../SHA256SUMS). alphaXiv screens every submission, and screening is not peer review.

## Common steps for each manuscript

1. Read the paper's `submission/alphaxiv.toml`. Check the five stage ratings and the tool records against the development record in `papers/reviews/<dir>/`, then set `owner_confirmed = true` in a commit to `main`. The release tag does not need to move: the pipeline reads confirmations and records from `main`. The pipeline refuses to publish until this is done.
2. Dry run: `python3 -B scripts/alphaxiv_publish.py papers/<dir>` locally, or the *Publish to alphaXiv* workflow with `publish` unchecked and `release = manuscripts-v2.0.0`. Compare the printed title, abstract, author and disclosure with the sheet below.
3. Submit, either by uploading the release PDF in the alphaXiv web form or by running the workflow with `publish` checked (protected `alphaxiv` environment). Choose **CC BY 4.0** and the subject **Mathematics > Number Theory (math.NT)** in the web form, because they are not API fields.
4. Record the returned alphaXiv URL under the manuscript's `id` in `papers/alphaxiv-records.toml`, so that later versions are posted with `new_version_of`. Wait for screening to finish before the next submission: alphaXiv allows one in-progress submission per account.
5. Only after acceptance, post the announcement draft in `submission/announcement.md` if desired. The reviewer inquiries in `submission/reviewer-inquiry.md` are drafts and are sent only with the owner's approval.

## 1. Disjunctive but Nonnormal Multiplicative Lambert Series (manuscript VI, version 1.0)

Submit first. Cites manuscript X for the translation identity; that citation resolves to the GitHub release, so it does not require X to be on alphaXiv first.

| Field | Value |
| --- | --- |
| PDF (release asset) | [06-multiplicative-lambert.pdf](https://github.com/eldernos/MathematicsResearch/releases/download/manuscripts-v2.0.0/06-multiplicative-lambert.pdf) |
| SHA-256 | `69f911638d29c2f2ad90e74c84a603945a7ba767fe49c8a1515202d03d4ff7b5` |
| Source at the tag | <https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/06-multiplicative-lambert> |
| Authors | Christopher Anderson (Independent Researcher) |
| Subject | Mathematics > Number Theory (math.NT); MSC2020 11K16 (primary), 11N36, 11N37, 11J81, 11N25, 11K38 |
| Keywords | disjunctive numbers, normal numbers, Lambert series, binary expansion, discrepancy, multiplicative functions, sums of two squares, Selberg sieve, transcendence, Lean 4 |
| Licence | CC BY 4.0 |
| URL slug | `disjunctive-nonnormal-multiplicative-lambert-series` |
| AI disclosure stages | idea: mixed, literature: ai, experiments: ai, analysis: ai, writing: ai |
| AI tools recorded | 4: Claude, GPT and Gemini models (several versions) (Conjectures, proofs, Lean 4 formalization and exact computations in the underlying research phases (Phases 1-19)); Claude Opus 5.5 (Drafted the manuscript and proofs, checked primary sources, and revised it in response to both reviews); GPT-6.2 Astra (Independent referee report (analytic number theory)); Gemini 4 Argon (Independent referee report (primary sources and novelty)) |
| Pipeline flag `owner_confirmed` | false (published through the web form; the API pipeline was not used) |
| Verification scope | [`VERIFICATION.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/06-multiplicative-lambert/VERIFICATION.md) · [ledger](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/06-multiplicative-lambert/LEDGER.md) · [reviews](https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/reviews/06-multiplicative-lambert) |
| Prepared text | [`submission/alphaxiv.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/06-multiplicative-lambert/submission/alphaxiv.md) (abstract, categories, disclosure, verification scope) |

**Abstract**

Let c be a nonnegative integer-valued multiplicative function with c(p^e) <= e+1. Suppose that c(p) = 2 for the primes of a set S that contains a reduced residue class and satisfies sum_{p <= x, p in S} 1/p = delta log log x + O(1) with 0 < delta < 1, that c(p) = 0 at the other primes not dividing a fixed modulus, and that c(p_0^{2u}) = 2u+1 for one p_0 in S and all u >= 0. Examples are c = chi*1 for a nonprincipal real Dirichlet character chi (delta = 1/2; for chi_4 this is r_2(n)/4) and an analogue with c(p) = 2 exactly at the primes p = 1 (mod 5) (delta = 1/4). For L = sum c(n) 2^{-n} = sum (c*mu)(m)/(2^m - 1) and every fixed a > 7/12, each fixed binary word containing a one occurs between constant multiples of H/(log N)^{1-delta} times among the shifts in [N, N+H), uniformly for N^a <= H <= N, and the all-zero word occurs H - Theta(H/(log N)^{1-delta}) times. Hence L is disjunctive in base two, while the digit one has frequency zero. For 1 + 4 L_{chi_4} = theta_3(1/2)^2, Bailey, Borwein, Crandall and Pomerance (2004) had already proved that the number of ones among the first M digits is asymptotic to C_0 M/sqrt(log M); the new content is the short windows, all words, the discrepancy order and the general class. The extreme discrepancy satisfies 1 - D_N(L) of exact order (log log N)/(log N)^{1-delta}, which by the translation identity of a companion paper is the exact worst-case change of discrepancy under translation by L. For odd characters L is transcendental by a theorem of Hamieh and Murty, extended here to imprimitive characters. The finite discrepancy inequalities are verified in Lean 4; the analytic estimates are written proofs using Shiu's theorem, a Selberg sieve and the Perelli-Pintz-Salerno short-interval prime number theorem.

## 2. The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations (manuscript X, version 1.0)

Submit second, so that the two papers citing it (VI and VII) can be updated with its alphaXiv URL in a later version if desired.

| Field | Value |
| --- | --- |
| PDF (release asset) | [10-discrepancy-arithmetic.pdf](https://github.com/eldernos/MathematicsResearch/releases/download/manuscripts-v2.0.0/10-discrepancy-arithmetic.pdf) |
| SHA-256 | `79c045a43c3cbfea27906d89f6cd9c8ef1e505b16b01b7c2610cb8750adb4f74` |
| Source at the tag | <https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/10-discrepancy-arithmetic> |
| Authors | Christopher Anderson (Independent Researcher) |
| Subject | Mathematics > Number Theory (math.NT); MSC2020 11K38 (primary), 11K16, 11A63, 37A44, 60B10 |
| Keywords | extreme discrepancy, radix expansions, normal numbers, translation, addition spectrum, Kuiper statistic, concentration function, Ky Fan metric, rational dilation, Lean 4 formalization |
| Licence | CC BY 4.0 |
| URL slug | `arithmetic-of-extreme-discrepancy` |
| AI disclosure stages | idea: mixed, literature: ai, experiments: ai, analysis: ai, writing: ai |
| AI tools recorded | 5: Claude, GPT and Gemini models (several versions) (Conjectures, proofs, Lean 4 formalization and exact computations in the underlying research phases (Phases 1-19)); Claude Opus 5.5 (Drafted the manuscript and proofs); Gemini 4 Argon (Independent referee report); Gemini 4 Neon (Independent referee report (Lean correspondence and bibliography)); Claude Sonnet 5.5 (Revised the manuscript in response to both reviews) |
| Pipeline flag `owner_confirmed` | false (published through the web form; the API pipeline was not used) |
| Verification scope | [`VERIFICATION.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/10-discrepancy-arithmetic/VERIFICATION.md) · [ledger](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/10-discrepancy-arithmetic/LEDGER.md) · [reviews](https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/reviews/10-discrepancy-arithmetic) |
| Prepared text | [`submission/alphaxiv.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/10-discrepancy-arithmetic/submission/alphaxiv.md) (abstract, categories, disclosure, verification scope) |

**Abstract**

For an integer base b >= 2 let D_N(x) be the extreme discrepancy of x, bx, ..., b^(N-1) x modulo one. We prove the finite identity sup_x |D_N(x+z) - D_N(x)| = 1 - D_N(z), attained at x = 0, and classify the translations that preserve both limiting discrepancies of every real number: they are the numbers c + w with (b-1)c an integer and (1/N) sum_{n<N} ||b^n w|| -> 0. The limits of D_N(x), D_N(y) and D_N(x+y) are exactly the triples in [0,1]^3 with max(0, alpha+beta-1) <= gamma <= 1 - |alpha-beta|. Every such triple is realized by positive rational expansions on a cubic schedule with simultaneous error O(N^(-1/3)), uniformly in the triple, by computable and algebraically independent witnesses; the analogous deficit polytope for d summands is determined. The translation deficit 1 - D_N(x-y) is a pseudometric, an exact form of Levy's concentration function comparable to the Ky Fan distance to constants. The rational scalars preserving its asymptotic kernel are exactly Z[1/b], an individual rational scaling is decided by a residue-density test, and on the boundary D_N(mx) -> 1 the attainable limits of D_N(x) form [1/m_0, 1], where m_0 is the part of m prime to b. The finite identity, the pseudometric axioms and the qualitative addition spectrum are verified by the Lean 4 kernel.

## 3. Synthetic Arithmetic Expansions and Prescribed Discrepancy (manuscript VII, version 1.0)

Submit third. Cites manuscript X.

| Field | Value |
| --- | --- |
| PDF (release asset) | [07-synthetic-expansions.pdf](https://github.com/eldernos/MathematicsResearch/releases/download/manuscripts-v2.0.0/07-synthetic-expansions.pdf) |
| SHA-256 | `703fb39ae7b6df50901faa2e757723c25e17b11479d269861d12ac417c8ccb5b` |
| Source at the tag | <https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/07-synthetic-expansions> |
| Authors | Christopher Anderson (Independent Researcher) |
| Subject | Mathematics > Number Theory (math.NT); MSC2020 11K16 (primary), 11K38, 11L07, 11J81, 37A44, 11A63 |
| Keywords | normal numbers, extreme discrepancy, radix expansions, Stoneham numbers, Korobov numbers, polynomial images, joint normality, invariant measures, Liouville numbers, Lean 4 formalization |
| Licence | CC BY 4.0 |
| URL slug | `synthetic-arithmetic-expansions-prescribed-discrepancy` |
| AI disclosure stages | idea: mixed, literature: ai, experiments: ai, analysis: ai, writing: ai |
| AI tools recorded | 4: Claude, GPT and Gemini models (several versions) (Conjectures, proofs, Lean 4 formalization and exact computations in the underlying research phases (Phases 1-19)); Claude Opus 5.5 (Drafted, restructured (split of manuscript X) and revised the manuscript and proofs); GPT-6.2 Astra (Independent referee report); Gemini 4 Argon (Independent referee report (primary sources and novelty)) |
| Pipeline flag `owner_confirmed` | false (published through the web form; the API pipeline was not used) |
| Verification scope | [`VERIFICATION.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/07-synthetic-expansions/VERIFICATION.md) · [ledger](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/07-synthetic-expansions/LEDGER.md) · [reviews](https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/reviews/07-synthetic-expansions) |
| Prepared text | [`submission/alphaxiv.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/07-synthetic-expansions/submission/alphaxiv.md) (abstract, categories, disclosure, verification scope) |

**Abstract**

Fix an integer base b >= 2, a prime p not dividing b, and let t be the order of b modulo p. For an integer d >= 2, insert the coefficient p^(-s v_p(k)) at base-b position t k^d for every k >= 1. For s = 0 the extreme discrepancy tends to one, while for every integer s >= 1 the number is normal to base b; this switch holds on every strictly increasing schedule of multiples of t dominating k^2, and it has been checked by the Lean 4 kernel together with the exact reduced denominator of every shifted prefix. For odd p and d >= s+2 complete periods give an explicit power rate, and for xi = sum_k 3^(-v_3(k)) 2^(-2k^3) a short self-contained proof gives D_N <= 200 N^(-1/3). Every radix orbit is, after a finite shift, the orbit of a positive expansion of this kind, so qualitative realization of discrepancy limits and limit sets follows from classical results. Choosing the rational state after each cubic insertion from two explicit targets, with coefficient denominators at most pk, realizes every limiting discrepancy in [0,1] with error O(N^(-1/3)) uniformly in the limit, and gives explicit arithmetic realizations of every pair of lower and upper limits and of every nonempty compact connected set of invariant measures. For odd p, s >= 1 and an integer d >= 3, every nonconstant rational polynomial of total degree at most two in the numbers of this family with distinct orders s on a common schedule is normal; in particular xi^2 is normal and (xi, xi^2) is jointly normal. The proof shows that the limiting p-adic mass of the shifted prefixes has Lebesgue-null level sets, by counting isolated jumps with van der Corput's method and a second-moment argument. Finally a positive binary series using every odd prime as a denominator prime is normal and Liouville with D_N = O(1/log N), while positive rational multiples of its jointly normal components can sum to any positive rational.

## 4. Polynomial Images of Stoneham Numbers (manuscript I, version 2.0)

Submit fourth. Version 2.0 revises the GitHub-released version 1.1, which has no alphaXiv record, so this is a first alphaXiv version. Its headline Theorems A and B are credited to Mira Cult's public S08 notes; the announcement must not present them as new.

| Field | Value |
| --- | --- |
| PDF (release asset) | [01-stoneham-polynomials-v2.pdf](https://github.com/eldernos/MathematicsResearch/releases/download/manuscripts-v2.0.0/01-stoneham-polynomials-v2.pdf) |
| SHA-256 | `51a6769cda364b1d517fb5512db2e91635ce9ff78651ac573c78178ce6624f2d` |
| Source at the tag | <https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/01-stoneham-polynomials-v2> |
| Authors | Christopher Anderson (Independent Researcher) |
| Subject | Mathematics > Number Theory (math.NT); MSC2020 11K16 (primary), 11J81, 11A63 |
| Keywords | Stoneham numbers, normal numbers, uniform distribution, discrepancy, p-adic valuation, Lean 4 |
| Licence | CC BY 4.0 |
| URL slug | `polynomial-images-of-stoneham-numbers` |
| AI disclosure stages | idea: mixed, literature: ai, experiments: ai, analysis: ai, writing: ai |
| AI tools recorded | 4: Claude, GPT and Gemini models (several versions) (Conjectures, proofs, Lean 4 formalization and exact computations in the underlying research phases (Phases 1-19)); GPT-6.2 Astra (Drafted the version 2.0 manuscript and began the revision in response to both reviews); Claude Opus 5.5 (Independent referee report; after the GPT revision was interrupted, completed the revision and resolution record); Gemini 4 Argon (Independent referee report (primary sources and Lean correspondence)) |
| Pipeline flag `owner_confirmed` | false (published through the web form; the API pipeline was not used) |
| Verification scope | [`VERIFICATION.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/01-stoneham-polynomials-v2/VERIFICATION.md) · [ledger](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/01-stoneham-polynomials-v2/LEDGER.md) · [reviews](https://github.com/eldernos/MathematicsResearch/tree/manuscripts-v2.0.0/papers/reviews/01-stoneham-polynomials-v2) |
| Prepared text | [`submission/alphaxiv.md`](https://github.com/eldernos/MathematicsResearch/blob/manuscripts-v2.0.0/papers/01-stoneham-polynomials-v2/submission/alphaxiv.md) (abstract, categories, disclosure, verification scope) |

**Abstract**

For coprime integers b ≥ 2 and c ≥ 2 let α(b,c) = Σ c^(−j) b^(−c^j), summed over j ≥ 1. Mira Cult’s public, unrefereed notes S08 (2026, Theorem 1.1 and Corollaries 1.2–1.3) show that for c > 2 every nonconstant rational polynomial in α(b,c) is normal in base b and that the distinct powers of α(b,c) are jointly normal. We give a complete kernel-verified Lean 4 proof of this ordinary case; its arithmetic step is an inclusion–exclusion argument showing that the leading prefix denominators lose only a bounded power of each prime of c. S08, Theorem 1.1(b), already gives an effective power saving with an unspecified exponent; we give the explicit scalar exponent δ_d = 1/(2(2^(d+1) − 2)) in degree d. At c = 2 and odd b ≥ 3 we determine the prefix denominators of α(b,2)^2, prove its normality, and give a denominator criterion for quadratics. A written transfer from exact finite certificates proves normality of every rational polynomial of degree 3 through 120, of degree 128, or of degree ep^r for sixteen pairs (e,p) and r ≥ 0. We determine the least 2-adic valuation of the leading mass in every degree, and show that nonvanishing of this mass on a family of open intervals of full measure would suffice in each degree. Normality of the resonant quadratic α(b,2)^2 − 2α(b,2) remains open for every odd radix b ≥ 3.
