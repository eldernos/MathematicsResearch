# Paper V reviewer guide

[Manuscript](paper.pdf) · [LaTeX source](paper.tex) · [Bibliography](references.bib) · [Statement correspondence](CORRESPONDENCE.md) · [Figure and table generator](figures/generate.py)

The principal result is Theorems 1.1, 2.3 and 2.4. For a fixed, nonzero integer multiple of log 2, the binary-exponent truncations of finite integer combinations of real dyadic logarithms have least possible reduced-denominator rate 1/2. Equality characterizes the grouped coefficient sequence, after normalization. The general band formula and the corrected approximations answer different questions. In particular the values in Table 1 are upper bounds for the logarithmic costs of specified common denominators.

## Questions for mathematical review

- In the prime-band formula, fix the number of bands before excluding numerator primes. Only after taking the limit in the binary position may one discard the remaining first powers and higher powers. The checkpoint states this limit for a finite zero set. Convergence to a nonzero sum supplies this condition for the optimality theorem. The proof on paper also handles an infinite zero set.
- In the equality classification, rewriting a plus logarithm preserves every grouped coefficient. Exponentiating the real identity yields a balance at every odd prime. Bang supplies the primitive prime at a hypothetical largest occupied index greater than six. These inputs identify the full class covered by the optimality conclusion. [Checkpoint valuation proof](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/NormalityChecker/DyadicRelations.lean#L14)
- Check the sign of the multiplier on the negative radix, especially at an incomplete stride. The finite error covers independently chosen correction orders including zero. At the endpoint of linear coverage the factor from Stirling is of order 1/√*N*. Table 1 concerns this particular beta estimate and denominator. The exact reduced rates of these linearly corrected models remain undetermined.
- The large-prime sieve operates before rational reduction. A vanished pole still contributes a zero congruence. The extra power of three is recovered separately from the ordinary 3-part. The exponential estimate on low-transition words averages over all possible residues at a single position. The word count for log 2 instead uses its specified residue and all admissible lifts. [Exact common denominators, residues and rational errors](figures/sieves.csv)
- For the joint test at 513, advance the model at 512 by one bit, including its error and the reduction in its grid size. The common kernel acts by simultaneous translation, so there are 31,104 distinct compatible pairs. Intersect the two real error intervals before counting closed binary cylinders. The union has 31,232 words. Exactly one has 18 changes and all others have more. Independent dyadic enclosure of log 2 gives 38 changes in the actual word. [Two grid sizes, common interval and enclosed word](figures/overlap.csv) · [Exact histogram](figures/overlap_words.csv)
- In Theorem 6.3 the Gaussian prime test must be applied to the sum of both truncated series. Its short rational has positive value because both coefficients are positive. The two cutoff indices vary monotonically with the tested prime. Thus there are only linearly many short index pairs in the proof of the error term for the denominator.
- Proposition 7.1 is for ordinary Taylor sums of *e*. The proof by modular short returns gives a local arithmetic explanation of a density conclusion already implied by Berndt, Kim and Zaharescu. The arguments for π in base ten and base sixteen give a finite-prefix discrepancy gap tending to zero. Neither the finite experiments nor the denominator theorems prove strict limiting discrepancy below one for the classical constants in the manuscript.

## Literature and priority

Searches on 24 November 2026 included “denominators of partial sums harmonic logarithm log(2) binary BBP series denominator cancellation”, “binary degree one BBP formulas log 2 classification all identities”, “Takahashi arctan(1/3) arctan(1/7) BBP”, “Sondow Schalm denominator density almost all hypergeometric denominators Taylor partial sums e”, and “primitive divisors Bang 1886 Zsigmondy 1892”. The following comparisons concern the mathematical statements and their hypotheses.

| Earlier result | Relation to the manuscript |
| --- | --- |
| Shiu, Theorem 2, and Sanna on harmonic numbers | Shiu gives the complete prime-power interval criterion for loss in the unweighted harmonic denominator. Sanna estimates numerator divisibility for fixed primes. Proposition 2.1 uses the same most-divisible terms, with an extra Fermat congruence for dyadic weights. [Shiu, revised manuscript](https://arxiv.org/abs/1607.02863v2) · [Sanna](https://doi.org/10.1016/j.jnt.2016.02.020) |
| Bailey–Borwein–Plouffe, Adegoke–Lafont–Layeni, and Takahashi | The digit-extraction method, various binary series for log 2 and arctangents of rational numbers, and the two component arctangents used for π all have precedents. Adegoke et al., equations (28)–(29), give a log 2 identity using complex arguments. Compare Takahashi's equations (11)–(19) with Theorem 6.3. The latter estimates the reduced denominator at a common binary cutoff. [Original BBP manuscript](https://www.davidhbailey.com/dhbpapers/digits.pdf) · [Adegoke et al.](https://nntdm.net/papers/nntdm-17/NNTDM-17-4-18-32.pdf) · [Takahashi's manuscript](https://tsukuba.repo.nii.ac.jp/record/2001720/files/RJ_51-1-177.pdf) |
| Bang, 1886 | For every index above six, the Mersenne number has a prime divisor dividing none of the earlier Mersenne numbers. This is the external hypothesis used in Theorem 2.4. [Original volume and both installments](https://www.jstor.org/stable/i24539913) · [Modern account, §1](https://doi.org/10.1017/S1446788715000269) |
| Rivoal, 2007 | The allowed denominators in his irrationality measures may involve both a radix power and an lcm. His estimates apply to the distance of a logarithm from a rational grid. Sections 2 and 3 study specific rational truncations and integral corrections. [Article](https://doi.org/10.4171/RMI/519) |
| Sondow–Schalm and Berndt–Kim–Zaharescu | Sondow–Schalm's Proposition A.5 gives exact least period *q*, and their §3 treats gap polynomials. Berndt–Kim–Zaharescu, *Math. Res. Lett.* **20** (2013), Theorem 1.6 and end of §4, already bound the number of sufficiently good hypergeometric partial sums on proportional windows. Section 7 specializes their result to obtain the denominator conclusion, including upper Banach density zero. Their separate *Advances* paper settles the continued-fraction question. [Sondow–Schalm](https://arxiv.org/abs/0709.0671) · [Hypergeometric theorem](https://doi.org/10.4310/MRL.2013.v20.n3.a2) · [Full proof, §4](https://citeseerx.ist.psu.edu/document?doi=cea69a53ec649d2a78e38b364cddccde6d714ed0&repid=rep1&type=pdf) · [Convergents to e](https://doi.org/10.1016/j.aim.2013.08.010) |
| Zeilberger–Zudilin, 2020 | Their published upper bound on the irrationality measure of π is less than eight, sufficient for Proposition 8.1. The arc argument applies at every fixed integer radix. [Article](https://doi.org/10.2140/moscow.2020.9.407) |

Independent specialist review is still needed for priority of the dyadic rate classification and the prescribed-numerator bounds. The half-rate representation is an elementary logarithmic identity. The claims requiring comparison are its exact reduced-denominator asymptotics and its extremality under the stated cutoff and class restrictions. The paper is a lower-priority research draft for mathematical review. Authorship and submission remain with the project owner.

## Reproduction

Run the following from the repository root. Rebuilding the manuscript uses the archived vector figure. Regenerating it also requires Python 3, Pycairo and DejaVu Sans.

```sh
python3 -B papers/05-classical-denominators/figures/generate.py
papers/build.sh 05-classical-denominators
```

Figure 1 uses exact integers for the reduced denominators at every fourth binary position from 32 through 1024. The rational budget computation uses six integer power comparisons and a rational upper bound for log 3. [Figure](figures/denominators.pdf) · [Exact denominators](figures/denominators.csv) · [Budget inputs and rational bounds](figures/budgets.csv)

The following commands apply to a checkout of the [formal checkpoint](https://github.com/eldernos/MathematicsResearch/tree/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035). Its Lean toolchain is v4.36.0. The checkpoint build and axiom audit passed. The 43 declaration names in the correspondence table were also checked individually. Their axiom sets are subsets of `propext`, `Classical.choice` and `Quot.sound`.

```sh
lake build
lake env lean Audit.lean
cd scripts
python3 -B -m unittest \
  test_strided_logarithm.StridedLogarithmTests.test_exact_numerator_congruences \
  test_strided_logarithm.StridedLogarithmTests.test_low_transition_sieve \
  test_phase_eleven.PhaseElevenArithmeticTests.test_corrected_numerators \
  test_phase_eleven.PhaseElevenArithmeticTests.test_linear_coverage_costs \
  test_phase_eleven.PhaseElevenArithmeticTests.test_adjacent_lifts \
  test_phase_eleven.PhaseElevenArithmeticTests.test_corrected_window_sieve \
  test_phase_eleven.PhaseElevenArithmeticTests.test_gaussian_shadows
```

The independent full enumeration for the overlap calculation scanned each of the 3,888,000 points of the first advanced grid. For each point it selected the nearest point on the second grid and tested the intersection of the two rational error intervals. This recovered every bin of the archived histogram. The generator uses the faster gcd calculation in Proposition 5.3.
