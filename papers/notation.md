# Notation across the manuscripts

| Symbol | Convention |
| --- | --- |
| *b* | Integer radix, at least two. |
| { *y* } | Fractional part of a real number, taken in [0,1). |
| *N* | Length of an observed prefix. The radix orbit uses the exponents 0 through *N* − 1. |
| *I* | A half-open test interval [*u*, *v*) in [0,1). Boxes in several dimensions are Cartesian products of such intervals. |
| *D*ₙ, *D*∞ | Extreme interval discrepancy at a finite cutoff and its upper limit. A subscript *N* denotes a sample of length *N*. |
| *p*, *s* | In the localized expansions, *p* denotes a selected prime and *s* the positive denominator order. In the Stoneham papers, *p* denotes the prime parameter. |
| *v*ₚ | Additive prime valuation, normalized by *v*ₚ(*p*) = 1. |
| *α*(*b*, *c*) | The standard Stoneham series, starting at index 1. Signed shell constructions in Paper III have a separate coefficient sequence, with its own initial index. |

For a finite prefix, discrepancy is the supremum of the absolute differences between interval frequency and interval length. Normality in radix *b* means that each word of length *h* in that radix has limiting frequency 1/*b*ʰ. The terminating convention applies at ambiguous digit expansions. Normality is equivalent to uniform distribution of the radix orbit.

The primary papers state the indexing, quantifiers and test sets in their own notation. Their correspondence tables identify the definitions used in Lean. A paper deduction that uses an external theorem, an exact finite computation, and a kernel-checked universal statement each carry their own evidence.
