# A guided tour

This page explains, without prerequisites beyond calculus, what the main theorems say and why they are interesting.

## Normal numbers

Write a real number in base 10. If every digit appears one tenth of the time, every pair of digits one hundredth of the time, and so on for blocks of every length, the number is *normal in base 10*. Normality in base *b* is defined the same way with *b* digits.

Almost every real number is normal in every base; this was proved by Émile Borel in 1909. Yet for the familiar constants √2, π, *e* and ln 2 normality is unknown in every base. Explicit normal numbers exist, but most are constructed for the purpose, such as Champernowne's 0.123456789101112…, whose digits are the integers written in order.

One way to measure how far a number is from normal is its *discrepancy*. Shift the decimal point *n* places and look at the fractional part; for *n* = 0, 1, …, *N* − 1 this gives *N* points in [0, 1). Their discrepancy *D*<sub>*N*</sub> is the worst difference, over all intervals, between the share of points in the interval and its length. A number is normal exactly when *D*<sub>*N*</sub> tends to 0, and *D*<sub>*N*</sub> close to 1 means the points crowd into a tiny region.

## Stoneham numbers

In 1973 Richard Stoneham studied numbers such as

```math
\alpha = \sum_{j=1}^{\infty} \frac{1}{3^j \, 2^{3^j}} = \frac{1}{3 \cdot 2^{3}} + \frac{1}{9 \cdot 2^{9}} + \frac{1}{27 \cdot 2^{27}} + \cdots
```

and showed that this one is normal in base 2. The reason is arithmetic. Multiply by 2ⁿ and drop the tiny later terms: what remains is a fraction whose denominator is a power of 3. As *n* grows, that power grows, and multiplying a fraction with denominator 3ᵏ by 2 again and again visits its multiples almost uniformly. So the binary digits of α look uniformly distributed.

## What is new here

**Polynomials of Stoneham numbers.** Normality is not preserved by multiplication in general. Theorem I shows that α², α³, and indeed every polynomial in α with rational coefficients that is not constant, is normal in base 2. The difficulty is that α² has many more terms: one for each *pair* of terms of α. The figure shows them.

<!-- BEGIN FIGURE stoneham-square-lattice -->
<p align="center">
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="../assets/figures/stoneham-square-lattice-dark.svg">
  <img src="../assets/figures/stoneham-square-lattice-light.svg" alt="A 6 by 6 grid of cells indexed by i from 1 to 6 left to right and j from 1 to 6 bottom to top. Each cell shows the insertion position 3 to the i plus 3 to the j and the coefficient 3 to the minus (i + j); the grid is symmetric about the diagonal. Positions range from 6 in the corner (1, 1) to 1458 in the corner (6, 6). Twenty-two cells are shaded blue: all pairs with both indices at most 4, plus (5, 1), (5, 2), (5, 3) and their transposes, the pairs whose position is at most 270. Cells (4, 4), (5, 3) and (3, 5) on the anti-diagonal i + j = 8 have an orange outline. Below, a logarithmic number line from about 2 to 1600 shows the 6 insertion positions 3 to the j of alpha in one row and the 21 distinct positions of alpha squared in a second row, clustered just after each power of 3, with a vertical marker at n = 270; positions up to 270 are blue." width="640">
</picture>
</p>

<sub>Figure 1. Squaring the binary Stoneham number creates a two-dimensional lattice of insertions; the pairs kept at one digit position form the upward-closed set used in the proof of ST-01. [Caption, data and generator](../docs/figures.md#stoneham-square-lattice)</sub>
<!-- END FIGURE stoneham-square-lattice -->

The proof shows that, however the terms of a power are arranged, a power of 3 always survives in the denominator, by a short counting argument modulo *p* − 1. The digits of α, α², α³, … are even independent of each other in the limit.

**A complete classification.** Theorem II looks at the series Σ 1/(*m*ˢ *b*ᵐ) where *m* runs over the integers built from a fixed finite set of primes. Every such series is either normal or as far from normal as possible, and which one happens depends only on whether some prime in the set fails to divide *b*.

**Exact discrepancy.** Most numbers that are not normal are hard to analyze precisely. Theorem III builds a family of signed series for which the discrepancy can be computed exactly, as the proportion of positions that fall in certain "resonant" ranges. It also determines exactly which values are possible.

<!-- BEGIN FIGURE signed-shell-regions -->
<p align="center">
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="../assets/figures/signed-shell-regions-dark.svg">
  <img src="../assets/figures/signed-shell-regions-light.svg" alt="Three stacked panels, one per phase word 1110, 10 and 100, sharing a logarithmic horizontal axis of prefix length N from 1 to 3 to the 10th. Above each panel a band of ten equal-width shells is coloured aqua for nonzero phase and orange for zero phase: every fourth shell for 1110, every second shell for 10, and two of every three shells for 100. Below, a solid curve shows the exact fraction Z(N)/N of zero-shell positions, rising across orange shells and falling across aqua ones. Its peaks approach dashed lines at 27/40, 3/4 and 12/13 respectively." width="640">
</picture>
</p>

<sub>Figure 4. The exact zero-shell fraction *Z*(*N*)/*N*, which DS-01 identifies with the discrepancy, for three periodic phase words. [Caption, data and generator](../docs/figures.md#signed-shell-regions)</sub>
<!-- END FIGURE signed-shell-regions -->

## What is not done

These methods need the denominators of the rational approximations to have a fixed, finite set of prime factors. The natural series for ln 2 and π produce denominators with ever more prime factors, growing exponentially. The project proves several facts about those denominators, but nothing about the normality of ln 2, π or *e*. [Open problems](open-problems.md)

## How the results are checked

The proofs are written out in [research notes](../notes/results.md) and in five draft [manuscripts](../papers/README.md). The main theorems are also proved in the proof assistant Lean, which checks every logical step mechanically. That guarantees the formal statements follow from their definitions; it does not guarantee that the definitions mean what the prose says, or that the results are new. [What verification covers](attribution.md#what-lean-verification-establishes)

## Where to go next

- The [README](../README.md) states the theorems precisely.
- The [figures](figures.md) illustrate the structures in the proofs.
- The [guide for mathematicians](guide-mathematicians.md) explains how to check a proof.
