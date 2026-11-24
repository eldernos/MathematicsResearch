# Reviewing Polynomial Images of Stoneham Numbers

[Manuscript](paper.pdf) · [LaTeX](paper.tex) · [References](references.bib) · [Declaration correspondence](CORRESPONDENCE.md)

Theorem 1 concerns the classical positive-index series. The second parameter may be any positive power of an odd prime coprime to the integer radix *b* ≥ 2. The conclusion concerns normality in that radix. Theorem 2 allows separate positive radix dilations and prime exponents in every factor, with exactly one nonzero term of highest positive degree.

## Mathematical checks

1. In Lemma 3, evaluate the integral polynomial numerator at one before reducing its value at *p* modulo *p* − 1. This proves nonvanishing as an integer. The lattice at the cut 10/9 gives a numerator divisible by 27, so a unit conclusion would be false. The congruence supplies no information for *p* = 2.
2. In Lemma 4, all upper sets under consideration contain a common anchor. This persists under coordinatewise limits and excludes an empty limiting set. In Lemma 5, the condition $v_i<h_i$ enforces the omitted zeroth term. At fixed precision, it holds on all contributing tuples when the shell is large.
3. In Theorem 2, the finite list of strictly lower degrees gives a denominator order at most $(d-1)k$ after clearing rational coefficients. Different maximal monomials can have equal pole orders. Expanding a hypothetical unrestricted multivariate theorem would lose the step that proves survival in the sum.
4. Corollary 6 tests half-open boxes in all dimensions and uses the same starting position in every coordinate. Repeated exponents would put the distribution on a diagonal. Exponent zero gives a constant coordinate. Zero-width intervals and the empty collection are included in the checked statement.
5. In Theorem 7, index zero would introduce extra terms at the third scale. The dip from 81 to 9 at position 30 and the rise to 243 at 36 follow from the actual ordered-pair recurrence. In Theorem 8, either side of the isolated jump may carry the growing pole. The four completed windows cover at least 2/45 of every sufficiently long prefix.
6. Corollaries 9–10 and Proposition 11 use external transcendence results. For Corollary 10 the normalized locations form a subset of a fixed compact countable set, giving a gap of positive relative length on every shell. For Proposition 11 the two parameters may share prime factors. One prime dividing the first parameter suffices for a growing pole. The stated conclusions give no rate or value of the limiting discrepancy for general independent parameters.

## Reproduce the formal check

At the repository root, with the pinned toolchain and mathlib available, run

```sh
lake build NormalityChecker.StonehamJoint NormalityChecker.StonehamSquare NormalityChecker.ProductThreeFive
lake env lean papers/01-stoneham-polynomials/check.lean
```

The [statement module](../../NormalityChecker/StonehamStatements.lean) imports the definition of normality and polynomial evaluation. It introduces no research theorem. The [proof module](../../NormalityChecker/StonehamJoint.lean) identifies the two public propositions with the proved conclusions. The [independent check](check.lean) also identifies the definitions used by the general, square and mixed-product proofs and checks transitive axiom dependencies. Each of the nine audited declarations passed with exactly `propext`, `Classical.choice` and `Quot.sound`.

## Figures and compilation

From this directory run

```sh
python3 figures/generate.py
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

The generator uses Python's standard library. The [lattice data](figures/lattice.csv) record exact membership on the displayed grid. The [square data](figures/square.csv) come from an independent recurrence over rational numbers. The [joint-word counts](figures/joint.csv) use rational upper and lower bounds for the generator and its square. At *N* = 4096 the two bounds agree after multiplication by $2^{N+1}$ and taking the floor, which determines every tested two-bit word. The counts illustrate a proved limit. Their values play no role in the proof.

## Literature and scope of priority review

The searches on 24 November 2026 included “Stoneham numbers powers squares polynomials normal numbers”, “Stoneham polynomial normality Korobov”, “Wagner rings of normal numbers Kano Shiokawa”, “Stoneham numbers Coons transcendence appendix”, “Korobov conjunctly normal numbers powers” and “Stoneham sums normality 2026”. We compared the sources below and checked bibliographic identifiers against publisher, institutional or Math-Net records.

| Comparison | Source and scope |
| --- | --- |
| The individual generator | Stoneham's original result includes the binary example. A. N. Korobov's 1990 criterion already gives individual normality for the standard schedule. Bailey–Crandall explicitly treat the whole coprime family. [Stoneham](https://doi.org/10.4064/aa-22-3-277-286) · [A. N. Korobov](https://doi.org/10.1007/BF01156821) · [Kano's account of the hypotheses](https://doi.org/10.18910/10356) · [Bailey–Crandall](https://doi.org/10.1080/10586458.2002.10504704) |
| Joint normality | N. M. Korobov studied jointly normal numbers in 1956. Classical multidimensional Weyl approximation is the analytic step in Corollary 6. The arithmetic input here concerns the particular coordinates consisting of powers of one standard generator. [N. M. Korobov](https://www.mathnet.ru/eng/im3836) · [Weyl](https://doi.org/10.1007/BF01475864) |
| Polynomial normality and normal-number rings | Wagner's publisher abstract describes an explicit ring. Kano–Shiokawa's Theorems 4–5 and hypotheses (15)–(16) concern specially separated generators. The ordinary positive-index schedule fails both growth limits. Kano–Shiokawa's Remarks 2 also identify the irrational members of the rings discussed there as Liouville. For the binary example, a direct rational-separation argument gives irrationality exponent 3. [Wagner](https://doi.org/10.1006/jnth.1995.1114) · [Kano–Shiokawa, institutional text](https://www.math.keio.ac.jp/wp-content/uploads/2022/03/91006.pdf) · [Binary exponent calculation](https://github.com/eldernos/MathematicsResearch/blob/a09e011720bc74396a27f4cb3ce2d8a5b3ce5035/notes/stoneham-powers-products.md#prior-normal-rings-and-a-change-of-radix) |
| Short orbits | Vandehey's Corollary 1.2 is quantitatively stronger than the qualitative analytic input here. Theorem 7.4 requires an increasing coefficient-denominator divisibility chain with unit numerators and a gap condition. In the square, even the two consecutive insertions at positions 18 and 30 have the same reduced coefficient denominator 81. [Vandehey, preprint §§1 and 7.2](https://arxiv.org/abs/1606.07911) |
| Sums and products | Bailey–Borwein pose the two-sum problem. The 2026 two-sum manuscript covers two positive unit coefficients with different parameters in a common base. The present product estimate concerns a different value and gives a strict bound short of the conclusion of full normality. [Bailey–Borwein](https://doi.org/10.1007/s11139-012-9417-3) · [September 2026 manuscript, fixed source](https://github.com/CaptainSude/Stoneham-sum-normal/blob/f4d3d1f01d00c57425c684409849053e58e42261/paper/stoneham-two-sum-normality.pdf) |
| Transcendence | Coons gives the standard generators' transcendence in Appendix A. Ridout's theorem gives the needed restricted-denominator approximation threshold for the products. Their uses in the paper are outside the kernel audit. [Coons](https://doi.org/10.1017/S1446788713000682) · [Ridout](https://doi.org/10.1112/S0025579300001339) |

The unresolved priority question is whether earlier work proves polynomial normality for these specified generators, including through a different representation or a more general criterion. The failure of one choice of generator hypotheses establishes no historical exclusion. The paper is prepared for mathematical review. Project-owner authorship and submission decisions remain pending.

The repository preprint on two Stoneham summands gives a title and date without a personal byline; the bibliography identifies its source repository and revision. Vandehey’s theorem numbers in the text refer to the linked arXiv version. The independent model reports and subsequent changes are recorded in the [release review log](../reviews/README.md).
