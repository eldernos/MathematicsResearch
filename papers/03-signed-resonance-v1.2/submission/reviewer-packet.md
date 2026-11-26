# Reviewer packet: Paper III, version 1.2

## Exact statements

**Theorem 1 (DS-01, DS-03).** Let *b* ≥ 2, let *p* be a prime with *p* ∤ *b*, and let (*c*<sub>*j*</sub>)<sub>*j*≥0</sub> be bounded integers. For the signed expansion with jumps *c*<sub>*j*</sub> − *p c*<sub>*j*−1</sub> at *p*<sup>*j*</sup>, the difference between *D*<sub>*N*</sub> and the proportion of positions below *N* in shells with *c*<sub>*j*</sub> = 0 tends to zero. For every nonzero integer *m* and rational *r*, the translate *mY* + *r* has main term multiplied by the upper discrepancy of the rational orbit of *r*. Evidence: kernel-verified.

**Theorem 3 (CR-01).** For an odd prime *p* ∤ *b* and finitely many rational weights on radix-dilated components with parameter *p*, the sum is normal in base *b* exactly when the cyclotomic polynomial of order ord<sub>*p*</sub>(*b*) divides no cell polynomial. Evidence: kernel-verified.

**Theorem 7 (DS-04).** A number δ is the upper discrepancy of some bounded-phase expansion exactly when δ is the base-*p* value, with digits 0 and *p* − 1, of a binary word that is at least each of its suffixes in lexicographic order. Evidence: kernel-verified.

## Proof outline

On each shell [*p*<sup>*j*</sup>, *p*<sup>*j*+1</sup>), the shifted value equals a rational number *c*<sub>*j*</sub>/*p*<sup>*j*</sup> modulo one, up to a tail that tends to zero (Lemma 4). Lemma 2 gives uniform interval counts for incomplete rational orbits whose denominators grow on a fixed finite set of primes. Lemma 5 transfers the extreme discrepancy across endpoints carrying atoms. Zero shells therefore contribute concentrated mass and nonzero shells contribute uniform mass, which proves Theorem 1. Reading the zero pattern backwards in time and maximizing over prefixes gives the suffix-maximal condition in Theorem 7. For Theorem 3, clear denominators by (*p* − 1)·*D*, where *D* is the common denominator. The cell polynomial then records the residue at each scale, and its divisibility by the cyclotomic polynomial detects persistent cancellation.

## Where review is wanted

- The clearing factor in Theorem 3 for coincident insertions and signed weights.
- Uniformity in Lemma 2 over every partial length.
- The transfer across atoms in Lemma 5.
- The transcendence step in Theorem 10, which uses Roth and Ridout.

## Reproduction

`lake env lean papers/03-signed-resonance-v1.2/check.lean`, using a build of the repository at `e4809cf561573aef588e6ffc491a35cdb79fd9ec` or later. The declaration-level map is in `CORRESPONDENCE.md`.
