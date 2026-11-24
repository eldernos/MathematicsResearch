# Paper IV review disposition

The reviewers examined [the same author revision](https://github.com/eldernos/MathematicsResearch/tree/74ece558e91dc248420752ec0e63cfb03387251a/papers/04-arithmetic-certificates). Both checked the 26-declaration axiom audit and independently reproduced the finite enclosure. [Gemini report](gemini.md) · [Sonnet report](sonnet.md)

| Finding | Change in the release manuscript |
| --- | --- |
| Source of the fixed-support estimate | The abstract and Theorem 2 identify the estimate as a qualitative consequence of Vandehey. The text credits the block decomposition of the localized-logarithm preprint and removes unreliable theorem numbers for Bailey and Crandall. |
| Scope of the joint test | Section 4 explains that the qualitative normality conclusion for this unsigned family already follows from Paper II. The computation encloses the upper density of failures at one particular precision. The upper density supplies an upper bound for discrepancy. The separate comparison for signed expansions is explicitly asymptotic. |
| Quantifiers and overlap | Section 1 defines an arithmetic certificate, including the quantification over exceptional sets and individual reduced denominators. Corollary 7 now states the assumptions on each pair, the common observations and the overlap length, and distinguishes equality modulo one from eventual equality of reduced denominators in a chain. |
| Endpoints and finite checks | The monotonicity on a band and on the subsequent gap explains why the enumeration of right endpoints suffices. Checking all grid boundaries modulo 169 gives residues with minimum 7 and maximum 167. The mesh argument, the indexing of rows, and the restriction on the period example have been made explicit. |
| Exposition, figure and formal scope | The abstract gives the hypotheses of rigidity. Several informal accounting metaphors have been replaced with bounds for counts and sums. Figure 1 separates its axis title from the ticks and defines the relative scale. The correspondence table and its companion file now use the finer registry identifiers and explain the scope of the formal partial-coverage theorem. |

The degree of originality of the overlap-rigidity formulation remains a question for specialists. The source records no claim of historical priority for the short exponential sum estimate. [Revised PDF](../../04-arithmetic-certificates/paper.pdf) · [Formal correspondence](../../04-arithmetic-certificates/CORRESPONDENCE.md)
