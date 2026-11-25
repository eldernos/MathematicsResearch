# Manuscript releases

Every manuscript release is a Git tag. A tag is never moved and earlier files are never replaced:
a revision appears in a new directory with a new version number. The table lists the release
candidate manuscripts-v2.0.0. Its Lean links point to the immutable commit
[`e4809cf56157`](https://github.com/eldernos/MathematicsResearch/tree/e4809cf561573aef588e6ffc491a35cdb79fd9ec) (research-checkpoint-18).
The SHA-256 digests identify the PDFs committed at the source commit of this record.

| Paper | Version | Title | Status | PDF | SHA-256 |
| --- | --- | --- | --- | --- | --- |
| I | 1.1 | Polynomial Images of Stoneham Numbers with an Odd Prime-Power Parameter | archived (unchanged since manuscripts-v1.1.0) | [01-stoneham-polynomials.pdf](01-stoneham-polynomials/paper.pdf) | `a1eb39ba1d70344d1b0452b1b8e6445ff9824983841bc048f204c2512a5982e8` |
| II | 1.1 | Normality of Localized Logarithms and Polylogarithms on Finite Prime Supports | archived (unchanged since manuscripts-v1.1.0) | [02-localized-normality.pdf](02-localized-normality/paper.pdf) | `7ef10be884b1d55ac49ebf669707e2fedb715121c5e85099a871b8dba6824c03` |
| III | 1.1 | Resonance and Discrepancy in Signed Stoneham Expansions | archived (unchanged since manuscripts-v1.1.0) | [03-signed-resonance.pdf](03-signed-resonance/paper.pdf) | `d68e430fb75cb6ffa67eb13adc6553160b8a8ae1de095ed29fed1f3ebcc1f598` |
| IV | 1.1 | Arithmetic Certificates for Normality and Their Limitations | archived (unchanged since manuscripts-v1.1.0) | [04-arithmetic-certificates.pdf](04-arithmetic-certificates/paper.pdf) | `dea4c4afd1330f80bd295a96aeb9cb8e1abe7a6a86d60e4a87a51903c1618f2a` |
| V | 1.1 | Reduced Denominators of Binary Logarithm and Arctangent Series | archived (unchanged since manuscripts-v1.1.0) | [05-classical-denominators.pdf](05-classical-denominators/paper.pdf) | `9433bc84c6a615115b957e508e8d340559f7ebd9861686dee3d0f766d3c996dc` |
| A | 1.0 | Disjunctive but Nonnormal Multiplicative Lambert Series | preprint draft | [06-multiplicative-lambert.pdf](06-multiplicative-lambert/paper.pdf) | `7f746c12c84c13dded72f7f0bcaca51927f50efd45c3429fce0f747b54123024` |
| B | 2.0 | Polynomial Images of Stoneham Numbers | preprint draft | [01-stoneham-polynomials-v2.pdf](01-stoneham-polynomials-v2/paper.pdf) | `163a44972f20da57117f2fe0ec7044e36d17e0e009b6decd6bc888a2eb061e92` |
| C | 1.0 | Synthetic Arithmetic Expansions and Prescribed Discrepancy | preprint draft | [07-synthetic-expansions.pdf](07-synthetic-expansions/paper.pdf) | `9b2ca2bc67d3ded64267d8c3692a3b0f185612fff82de44dfb00c03f21768cb3` |
| H | 1.0 | The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations | preprint draft | [10-discrepancy-arithmetic.pdf](10-discrepancy-arithmetic/paper.pdf) | `e6779d5374fc5874f9b894d7043ae65cad48498ef0d6e1c715e00045e40774be` |
| D | 1.0 | Exceptional Orbits and Discrepancy of Stoneham Products | preprint draft | [08-stoneham-product-orbits.pdf](08-stoneham-product-orbits/paper.pdf) | `581870460109cf3b7d31220944249763d596173c7419732ffded2cd8da55a195` |
| E | 2.0 | Normality of localized logarithms and polylogarithms on finite prime supports | preprint draft | [02-localized-normality-v2.pdf](02-localized-normality-v2/paper.pdf) | `c48634fec0c49fa36e8290286f111fe656c05f1799939656c87dbd97632a60d3` |
| F | 2.0 | Denominator Growth and Rational Shadowing for Classical Constants | preprint draft | [05-classical-denominators-v2.pdf](05-classical-denominators-v2/paper.pdf) | `148b31a6cd54672edb8ff81a69ee5c0767a38280b6fa8d3903ef8c91a90a058e` |
| G | 2.0 | Arithmetic Certificates for Normality and Mathematical Limitations | preprint draft | [04-arithmetic-certificates-v2.pdf](04-arithmetic-certificates-v2/paper.pdf) | `9ab48a203203d4cb7b053e6f41ffebabf2eee4f5242830684d98c83f8f3ed5c8` |
| III | 1.2 | Resonance and Discrepancy in Signed Stoneham Expansions | preprint draft | [03-signed-resonance-v1.2.pdf](03-signed-resonance-v1.2/paper.pdf) | `7ade8cbeea29021594e48dc34c998fd47aa4c30916e3ba813e89a8824d610d8f` |
| EB | 1.0 | Finite-statistic thresholds and statistical obstructions for the binary digits of the Erdős–Borwein constant | preprint draft | [09-erdos-borwein-note.pdf](09-erdos-borwein-note/paper.pdf) | `e44e04c8f445fda587fad09d81bcbcb5ad9770c10d2fb3c7c0f6cbe50056af1d` |

## Earlier releases

These tags remain valid. `python3 -B papers/check_release.py --verify-history` checks that
each still names its commit and the recorded bytes of every PDF.

### manuscripts-v1.0.0

Commit [`a29515ba5469a9626dfdfb699f5899aa70ad632f`](https://github.com/eldernos/MathematicsResearch/tree/a29515ba5469a9626dfdfb699f5899aa70ad632f) · [GitHub release](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.0.0)

| PDF | SHA-256 |
| --- | --- |
| papers/01-stoneham-polynomials/paper.pdf | `809c4ca940e6cf68ca0bc8d3355159049b8ebced48ce67561e994bdd5ea7b812` |
| papers/02-localized-normality/paper.pdf | `f15a4e09bbfa072e5188117dbf4bc5d9aa194ebb4293ae0b2730fb6a23ed48df` |
| papers/03-signed-resonance/paper.pdf | `42bab14725e2ffa4bbdc7808a7181445779856bf1100a14da2d0324487f4d207` |
| papers/04-arithmetic-certificates/paper.pdf | `a6ca286b03bc5d880bde8d483ac272172b1197e4b7d125282be907110e6b81f9` |
| papers/05-classical-denominators/paper.pdf | `46b4e55040d7c2e2e413d6e6ffb17fac3146bde7f58f4eeea60b112a5ed64b7f` |

### manuscripts-v1.1.0

Commit [`944e0c466978dc636f348552058a4ef65c9ed8be`](https://github.com/eldernos/MathematicsResearch/tree/944e0c466978dc636f348552058a4ef65c9ed8be) · [GitHub release](https://github.com/eldernos/MathematicsResearch/releases/tag/manuscripts-v1.1.0)

| PDF | SHA-256 |
| --- | --- |
| papers/01-stoneham-polynomials/paper.pdf | `a1eb39ba1d70344d1b0452b1b8e6445ff9824983841bc048f204c2512a5982e8` |
| papers/02-localized-normality/paper.pdf | `7ef10be884b1d55ac49ebf669707e2fedb715121c5e85099a871b8dba6824c03` |
| papers/03-signed-resonance/paper.pdf | `d68e430fb75cb6ffa67eb13adc6553160b8a8ae1de095ed29fed1f3ebcc1f598` |
| papers/04-arithmetic-certificates/paper.pdf | `dea4c4afd1330f80bd295a96aeb9cb8e1abe7a6a86d60e4a87a51903c1618f2a` |
| papers/05-classical-denominators/paper.pdf | `9433bc84c6a615115b957e508e8d340559f7ebd9861686dee3d0f766d3c996dc` |

## Review status

All manuscripts are preprint drafts. Their written proofs and literature comparisons have been
reviewed only by AI models from several providers. Cross-model review is not independent human
peer review, and no manuscript has been submitted to or accepted by a journal.
