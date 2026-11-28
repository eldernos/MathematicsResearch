# Research objectives

The repository pursues four permanent objectives about the radix expansions of explicit real numbers. This page defines the distributional properties they refer to, states each objective and what counts as progress on it, fixes the evidence labels used everywhere in the repository, and describes the benchmark suite that measures progress.

1. **Establish normality**: full normality, simple normality, exact digit and word frequencies, joint uniformity and effective rates.
2. **Establish nonnormality**: simple nonnormality, disjunctive nonnormality, membership in the numerical translation kernel *K*<sub>*b*</sub> and exact digit-frequency bias.
3. **Quantify digit distributions**: exact asymptotic discrepancy, sharp discrepancy gaps, exact frequency laws, limit measures, prescribed discrepancy spectra and explicit bounds *D*⁺ < 1 and *D*⁻ > 0.
4. **Establish rigorous mathematical limitations**: where certificates, denominator rates, finite statistics, carry-window widths, complementary coverage, Diophantine exponents and computable recognition provably stop.

## Definitions

Fix an integer radix *b* ≥ 2 and a real number *x*. Write {*t*} for the fractional part of *t* and

```math
x = \lfloor x \rfloor + \sum_{n \ge 1} d_n b^{-n}, \qquad d_n \in \{0, 1, \ldots, b - 1\},
```

for the base-*b* expansion that does not end in an infinite run of the digit *b* − 1. The **orbit** of *x* is the sequence {*b*ⁿ*x*}, *n* ≥ 0. A word *w* = *w*<sub>1</sub> ⋯ *w*<sub>*L*</sub> over the digits **occurs at position** *n* when *d*<sub>*n*+1</sub> ⋯ *d*<sub>*n*+*L*</sub> = *w*, which happens exactly when {*b*ⁿ*x*} lies in the *b*-adic interval *I*<sub>*w*</sub> of length *b*<sup>−*L*</sup> whose expansion begins with *w*.

**Frequencies.** Let *f*<sub>*N*</sub>(*w*) be the proportion of positions 0 ≤ *n* < *N* at which *w* occurs. The word *w* has **limiting frequency** *c* if *f*<sub>*N*</sub>(*w*) → *c* as *N* → ∞ along all integers *N*.

**Discrepancy.** The extreme interval discrepancy of the first *N* orbit points is

```math
D_N(x; b) = \sup_{0 \le u < v \le 1} \left| \frac{\#\{0 \le n < N : \{b^n x\} \in [u, v)\}}{N} - (v - u) \right| .
```

Write *D*⁺ = lim sup *D*<sub>*N*</sub> and *D*⁻ = lim inf *D*<sub>*N*</sub>. When the two agree, their common value is the **exact asymptotic discrepancy** *D*<sub>∞</sub>. The **discrepancy gap** is 1 − *D*<sub>*N*</sub>.

**Distributional properties.** In base *b* the number *x* is

- **simply normal** if every digit has limiting frequency 1/*b*;
- **L-normal** if every word of length *L* has limiting frequency *b*<sup>−*L*</sup>;
- **normal** (fully normal) if it is *L*-normal for every *L* ≥ 1, equivalently *D*<sub>*N*</sub> → 0;
- **disjunctive** if every finite word over the digits occurs at least once (equivalently, infinitely often);
- **simply nonnormal** if it is not simply normal, and **disjunctively nonnormal** if it is disjunctive and not normal;
- a member of the **numerical translation kernel** *K*<sub>*b*</sub> if *D*<sub>*N*</sub> → 1.

The kernel has a second description. For every *z* and every *N* ≥ 1,

```math
\sup_{y \in \mathbb{R}} \left| D_N(y + z; b) - D_N(y; b) \right| = 1 - D_N(z; b),
```

a kernel-verified identity ([GF-05](results.md#gf-05)). So *z* ∈ *K*<sub>*b*</sub> exactly when translation by *z* changes no discrepancy asymptotically, uniformly in the translated number.

**Limit measures.** The orbit measures of *x* are the averages of the point masses at {*b*ⁿ*x*}, 0 ≤ *n* < *N*. Their weak limits along subsequences are the **limit measures** of *x*; *x* is normal exactly when Lebesgue measure is the only one.

Every statement is about one radix, and the radix is always named. Normality in base *b* is equivalent to normality in every base *b*<sup>*k*</sup> (Maxfield 1953). Between multiplicatively independent bases no general implication holds (Schmidt 1960), and no classical constant studied here is known to be normal in two multiplicatively independent bases (computable synthetic constructions normal — together with all their nonconstant rational polynomials — in every integer base are established in [GF-39](results.md#gf-39)).

## Logical hierarchy

The positive properties form two chains:

- normal ⇒ *L*-normal ⇒ *ℓ*-normal for every *ℓ* ≤ *L* ⇒ simply normal;
- normal ⇔ *D*⁺ = 0 ⇒ *D*⁺ < 1 ⇒ *D*⁻ < 1 ⇔ *x* ∉ *K*<sub>*b*</sub>.

Normality also implies disjunctivity. Each one-way arrow is strict, and the following properties are logically independent of one another.

| Relation | Witness |
| --- | --- |
| Simple normality does not imply 2-normality | Euler's product *E*<sub>2</sub> = ∏(1 − 2<sup>−*k*</sup>) is simply normal in base 2, while the word 00 has frequency 1/2 ([GF-03](results.md#gf-03)) |
| *D*⁺ < 1 does not imply normality | *E*<sub>2</sub>/3 has *D*<sub>*N*</sub> → 1/2 in base 2 ([GF-04](results.md#gf-04)) |
| *x* ∉ *K*<sub>*b*</sub> does not imply *D*⁺ < 1 | A signed Stoneham expansion whose zero-phase shells form blocks of increasing length, separated by longer nonzero blocks, has *D*⁻ = 0 and *D*⁺ = 1, since *D*<sub>*N*</sub> follows the proportion of positions in zero-phase shells ([DS-01](results.md#ds-01)) |
| Disjunctive and in *K*<sub>*b*</sub> | The multiplicative Lambert series *L*<sub>χ₄</sub> = Σ χ<sub>4</sub>(*m*)/(2<sup>*m*</sup> − 1) ([CC-48](results.md#cc-48)) and Euler's cube *E*<sub>*b*</sub><sup>3</sup> ([GF-04](results.md#gf-04)) |
| Not disjunctive and in *K*<sub>*b*</sub> | *E*<sub>*b*</sub> for every *b* ≥ 2 ([GF-03](results.md#gf-03)) |
| Disjunctive and not in *K*<sub>*b*</sub> | Every normal number, for example Champernowne's constant in base 10 |
| Not disjunctive and not in *K*<sub>*b*</sub> | 1/3 in base 2, with *D*<sub>∞</sub> = 2/3 ([CC-04](results.md#cc-04)) |
| Not simply normal, not disjunctive, not in *K*<sub>*b*</sub> | 1/7 = 0.001001…₂ in base 2: the digit 1 has frequency 1/3, the word 11 never occurs, and the orbit {1/7, 2/7, 4/7} has *D*<sub>∞</sub> = 4/7 |
| Simply normal, not disjunctive, in *K*<sub>*b*</sub> | *E*<sub>2</sub> in base 2 ([GF-03](results.md#gf-03)) |
| Disjunctive, not simply normal | *L*<sub>χ₄</sub> in base 2, whose digit 1 has frequency 0 ([CC-46](results.md#cc-46)) |

So disjunctivity is independent of membership in *K*<sub>*b*</sub>, and simple normality is independent of both disjunctivity and membership in *K*<sub>*b*</sub>.

## Objective 1: establish normality

Progress is a proof, along all prefix lengths *N*, of one of the following for an explicit number or family in a named radix:

- full normality, *D*<sub>*N*</sub> → 0;
- simple normality or *L*-normality, or an exact limiting frequency for a specified word;
- joint uniformity: the orbits of several numbers, or of several powers of one number, are jointly uniformly distributed in the unit cube;
- an effective rate, an explicit function *ε*(*N*) → 0 with *D*<sub>*N*</sub> ≤ *ε*(*N*).

Normality along a subsequence of prefix lengths, logarithmic equidistribution and *D*⁻ = 0 are recorded under Objective 3; they do not establish normality. Normality of a series restricted to a finite set of primes ([LS-01](results.md#ls-01)) does not establish normality of the unrestricted series.

## Objective 2: establish nonnormality

Progress is a proof that an explicit number is not normal in a named radix, together with the strongest available description of how it fails:

- **simple nonnormality**: some digit has no limiting frequency 1/*b*;
- **disjunctive nonnormality**: every word occurs, yet the number is not normal;
- **membership in *K*<sub>*b*</sub>**: *D*<sub>*N*</sub> → 1;
- **exact digit-frequency bias**: an exact limiting frequency different from *b*<sup>−*L*</sup> for a specified word, such as the base-3 digit 1 of *E*<sub>3</sub>, whose frequency is 0 ([GF-03](results.md#gf-03)).

A statement that the first *N* digits are biased, for any finite *N*, is not nonnormality.

## Objective 3: quantify digit distributions

Progress is an exact or explicitly bounded description of the asymptotic distribution:

- the exact asymptotic discrepancy *D*<sub>∞</sub>, or exact values of *D*⁺ and *D*⁻;
- a sharp asymptotic for the gap 1 − *D*<sub>*N*</sub>, with its leading constant when possible;
- exact limiting frequencies of digits and finite words;
- the set of limit measures;
- prescribed discrepancy spectra: which values of *D*<sub>∞</sub> a family attains;
- explicit bounds *D*⁺ < 1 or *D*⁻ > 0, with the constant stated.

An upper bound *D*⁺ < 1 for a constant whose normality is open is progress under this objective even when it is far from 0.

## Objective 4: establish rigorous mathematical limitations

Progress is a theorem showing that a specific method, or a specific kind of information, cannot settle a distributional property. Examples in the repository:

- **rational-orbit certificates** need models of polynomial denominator size, and for almost every *x* such accurate models exist on only finitely many blocks of a fixed schedule ([AC-10](results.md#ac-10));
- **denominator rates**: the rate 1/2 is optimal among finite dyadic identities for ln 2 ([CC-02](results.md#cc-02)), and every balanced algebraic trace source has rate at least 5/12 ([CC-42](results.md#cc-42), [CC-43](results.md#cc-43));
- **finite statistics**: for the Erdős–Borwein constant, sixteen columns is the sharp minimal truncation and low-order moment and trigonometric certificates cannot certify a digit bias ([CC-49](results.md#cc-49));
- **carry-window widths**: windows for the partition constant are sharp and its recurrence admits both extreme behaviours ([GF-17](results.md#gf-17));
- **complementary coverage** blocks additive cancellation into *K*<sub>*b*</sub> ([GF-18](results.md#gf-18));
- **Diophantine exponents**: if *x* has finite irrationality exponent *μ*, then for every *μ*′ > *μ* every rational shadowing window is bounded by (*μ*′ − 1)*N* + *μ*′ log₂ *q*<sub>*N*</sub> + *O*<sub>*μ*′</sub>(1), which excludes the incomplete-orbit hypothesis at every positive denominator rate ([CC-50](results.md#cc-50)), and irrationality-exponent run bounds admit witnesses with *D* = 0 and with *D* = 1 ([AC-11](results.md#ac-11));
- **computable recognition**: recognizing binary normality of digit-oracle program codes is neither computable, nor computably enumerable, nor co-computably enumerable ([AC-11](results.md#ac-11)).

A limitation theorem names the method and the property, and proves that the method cannot reach the property. A failed attempt is not a limitation theorem.

## Evidence labels

Every result proved in the repository carries exactly one **proof label**: Kernel-verified, Lean-supported paper proof, Paper proof or Finite certificate. Three further labels describe statements that the repository does not prove: Conditional, External input and Open. The labels, and the rules below them, are permanent.

| Label | Registry status | Benchmark value | Meaning |
| --- | --- | --- | --- |
| Kernel-verified | `lean` | `lean` | The complete stated theorem is a Lean declaration that passed the kernel replay and the axiom audit (axioms among `propext`, `Classical.choice`, `Quot.sound`). |
| Lean-supported paper proof | `lean+paper` | `lean+paper` | A written proof whose named steps are Lean declarations. |
| Paper proof | `paper` | `paper` | A written argument only. |
| Finite certificate | `computation` | none | An exact computation of a finite statement. |
| Conditional | none | none | Depends on an unproved hypothesis, which is named. |
| External input | none | `external` | The statement itself is a published or released theorem, cited as a black box and not proved in the repository. |
| Open | none | `open` | Not settled. |

Rules:

1. **Finite digit statistics are never asymptotic evidence.** No computation of finitely many digits, frequencies or discrepancies establishes or supports a limiting property. Finite certificates prove only the finite statements they state.
2. **Cross-model review is not independent human peer review.** Reviews of a proof by AI models from other providers are recorded as such. A result or manuscript is called peer reviewed only after review by a journal or by referees outside the project.
3. Conditional results never change a benchmark status. They are recorded with the hypothesis named.
4. Published theorems used as ingredients inside a proof written in the repository are named with their source in the registry `inputs` field (and in a benchmark entry's `external_sources`). They do not replace the proof label of that result, but a result that uses one is never labeled Kernel-verified: it is at most a Lean-supported paper proof. The External input label is reserved for a statement that the repository cites rather than proves.
5. Priority is provisional: a literature search that finds nothing does not establish novelty.

## Benchmark suite

Progress is measured against a fixed suite in [docs/benchmarks](benchmarks/):

- [classical-constants.toml](benchmarks/classical-constants.toml): a fixed roster of 50 prominent constants, `BC-01` to `BC-50`, each with a published or kernel-verified proof of irrationality. They cover algebraic irrationals, logarithms and π, exponential, Gamma and Bessel values, zeta and L-values, q-series and modular values, Lambert and divisor series, continued-fraction and Mahler-type numbers, and the classical normal-number constructions. The roster never changes, so counts are comparable over time.
- [arithmetic-families.toml](benchmarks/arithmetic-families.toml): the structured families studied here and in the literature, `BF-01` onward, from Stoneham numbers and localized logarithms to Euler products, theta values, Lambert series, protected-pole algebras and BBP-type constants.
- [SCHEMA.md](benchmarks/SCHEMA.md): the exact format, the allowed status values and the mechanical consistency checks.
- [progress.md](benchmarks/progress.md): the progress table generated from the two data files, with one count per objective.

For each entry the suite records full normality, simple normality, disjunctivity, discrepancy status, barrier status, the evidence label, and the registry identifiers and published theorems that support them. A status changes only when a registry entry or a named published theorem establishes the new status; an error reverts it. The suite records verified results only.
