# The square of the parameter-two Stoneham number

**Theorem.** Let *b* ≥ 3 be odd. Write *α* for the positive-index Stoneham number in base *b*. For each integer *n* ≥ 0, let *Pₙ* be the shifted rational prefix of its square and *qₙ* the positive denominator of *Pₙ* in lowest terms. Explicitly,

```math
\alpha=\sum_{j=1}^{\infty}\frac{1}{2^j b^{2^j}},
\qquad
P_n=\sum_{2^i+2^j\le n}\frac{b^{n-2^i-2^j}}{2^{i+j}},
```

where the second sum runs over **ordered** pairs of positive integers. Then *α*² is normal in base *b*. The following intervals give *qₙ* at every cutoff. Each left endpoint is included.

| Cutoff | Reduced denominator |
| --- | --- |
| 0 ≤ *n* < 4 | 1 |
| 2ᵏ ≤ *n* < 3 · 2ᵏ⁻¹, for *k* ≥ 2 | 2²ᵏ⁻² |
| 3 · 2ᵏ⁻¹ ≤ *n* < 2ᵏ⁺¹, for *k* ≥ 2 | 2ᵏ⁻¹ |

Both conclusions are kernel-verified. The public statements define the prefix directly from the finite ordered sum. In Lean, index zero denotes the term with positive index one. [Statements](../../NormalityChecker/ParameterTwoSquareStatements.lean) · [Denominator proof](../../NormalityChecker/ParameterTwoSquareProfile.lean) · [Normality proof](../../NormalityChecker/ParameterTwoSquare.lean)

## The single-axis congruence

Let *Tₖ* be the sum of the first *k* terms of *α*, and put *Sₖ* = 2ᵏ *Tₖ*. The integer *Aₖ* clears its odd denominator.

```math
S_k=\sum_{j=1}^k\frac{2^{k-j}}{b^{2^j}},
\qquad A_k=b^{2^k}S_k.
```

Indeed, clearing the denominator term by term gives the recurrence

```math
A_0=0,\qquad A_{k+1}=1+2b^{2^k}A_k.
```

In particular *Aₖ* is odd for *k* ≥ 1. For every *j* ≥ 1, the odd square identity *b*² ≡ 1 (mod 8) and repeated squaring give

```math
b^{2^j}\equiv 1\pmod{2^{j+2}}.
```

The inverse has the same residue, since *b* is odd. Multiplying by 2ᵏ⁻ʲ makes the error in each summand of *Sₖ* divisible by 2ᵏ⁺² in the rationals with odd denominator. Summing the geometric progression gives the congruence and its integer form

```math
S_k\equiv 2^k-1\pmod{2^{k+2}},
\qquad
A_k\equiv (2^k-1)b^{2^k}\pmod{2^{k+2}}.
```

For *k* ≥ 1 the radix factor is itself one modulo 2ᵏ⁺². Thus *Aₖ* + 1 = 2ᵏ *a* for an odd integer *a* congruent to one modulo four. If *k* ≥ 2, the factorization

```math
A_k^2-1=2^{k+1}a\bigl(2^{k-1}a-1\bigr)
```

exhibits an odd quotient. Clearing the rational difference now gives its exact valuation

```math
S_k^2-\frac{1}{b^{2^{k+1}}}
=\frac{A_k^2-1}{b^{2^{k+1}}},
\qquad
v_2\!\left(S_k^2-\frac{1}{b^{2^{k+1}}}\right)=k+1.
```

The lower bound *k* ≥ 2 matters. At *k* = 1, *A₁* = 1 and the difference vanishes. Lean proves the integer congruence, the odd-quotient identity and the rational valuation in `weighted_congruence`, `diagonal_numerator` and `diagonal_valuation`. [Arithmetic proof](../../NormalityChecker/ParameterTwoSquareArithmetic.lean)

## Which pairs have entered the prefix?

Before digit four the sum is empty. Fix *k* ≥ 2 and 2ᵏ ≤ *n* < 2ᵏ⁺¹. All pairs through index *k* − 1 are present since their largest insertion is 2ᵏ. An index above *k* cannot occur. The new diagonal (*k*, *k*) enters at the next shell boundary, 2ᵏ⁺¹. Hence the only further contributions come from the two equal arms (*k*, *j*) and (*j*, *k*) with 2ᵏ + 2ʲ ≤ *n*.

**Before the midpoint.** Each active arm index satisfies *j* ≤ *k* − 2, including the case of an empty arm. Let *J* be the set of these positive indices. Multiplying the old square and the two truncated arms by their common denominator gives the integer

```math
2^{2k-2}P_n =
 b^{n-2^k} A_{k-1}^2
 + 2\sum_{j\in J} b^{n-2^k-2^j} 2^{k-2-j}.
```

The old square gives an odd integer. The two arms together give an even integer. The displayed fraction therefore has reduced denominator 2²ᵏ⁻², including at *n* = 2ᵏ.

**From the midpoint onward.** At *n* = 3 · 2ᵏ⁻¹ the two pairs with indices *k* and *k* − 1 enter. Now the full *k*-by-*k* square is present except for the newest diagonal. Subtracting that term from *Tₖ*² and clearing the radix gives

```math
b^{2^{k+1}-n}P_n
 =\frac{A_k^2-1}{2^{2k}}
 =\frac{u_k}{2^{k-1}},
\qquad u_k=\frac{A_k^2-1}{2^{k+1}}.
```

The preceding factorization makes *uₖ* odd. Every summand in the definition of *Pₙ* has a power-of-two denominator, so the odd multiplier on the left preserves its reduced denominator. It also follows that the radix power on the left divides *uₖ*. Their quotient is the odd reduced numerator of *Pₙ*. The Lean theorems `first_half_reduction` and `second_half_reduction` give the numerator and denominator together. [Prefix proof](../../NormalityChecker/ParameterTwoSquareProfile.lean)

## From the prefix to normality

Taking two axes of stride one and dilation two in the existing Stoneham product expansion gives the real product (2*α*)² and the shifted prefix 4*Pₙ*. Dividing by four gives the actual shifted-tail limit

```math
b^n\alpha^2-P_n\longrightarrow 0.
```

On a block beginning at *n* with no new insertion through *n* + *i*, the same expansion gives *Pₙ₊ᵢ* = *bⁱ Pₙ*. [Identification and clean-block identity](../../NormalityChecker/ParameterTwoSquareExpansion.lean) · [Product expansion](../../NormalityChecker/StonehamPolynomialExpansion.lean)

Take blocks of length *B* = 2ʳ in the shell from 4ʳ to 4ʳ⁺¹. An insertion below 4ʳ⁺¹ has two indices each bounded by 2(*r* + 1), hence there are at most 4(*r* + 1)² candidate positions. The clean-block construction marks at most two blocks per candidate. The exceptional fraction in each group of *B* blocks tends to zero because *r*²/2ʳ tends to zero.

On every remaining block, write *qₙ* = 2ᵉ at its start and let *k* be the integer with 2ᵏ ≤ *n* < 2ᵏ⁺¹. The exact profile gives *k* − 1 ≤ *e* ≤ 2*k*. Since 2*r* ≤ *k* < 2(*r* + 1), the starting denominators tend uniformly to infinity and are at most *B*⁶ for *r* ≥ 2. Their only possible prime divisor is two, which is coprime to *b*. The fixed-support orbit estimate and the arithmetic certificate now give the frequency *b*⁻ᵐ for each length-*m* digit word of *α*². [Orbit estimate](../../NormalityChecker/SmoothOrbit.lean) · [Arithmetic certificate](../../NormalityChecker/ArithmeticCertificate.lean) · [Application](../../NormalityChecker/ParameterTwoSquare.lean)

## Checks

For *b* = 3, the first two midpoint transitions give the following reduced fractions directly from the ordered-pair sum.

| *n* | 4 | 5 | 6 | 7 | 8 | 10 | 11 | 12 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| *Pₙ* | 1/4 | 3/4 | 5/2 | 15/2 | 361/16 | 3251/16 | 9753/16 | 7315/4 |

At *k* = 3 one finds *A₃* = 3079 and (*A₃*² − 1)/16 = 592515. At *n* = 12 the remaining radix factor is 3⁴, giving 592515/81 = 7315 for the reduced numerator. At *n* = 10 only the two new pairs with positive indices 3 and 1 have entered. Those two terms add 2/16 to the shifted old square 3249/16.

An independent exact-fraction calculation checked all 1,024 cutoffs from 0 through 1023 in each odd base from 3 through 31. It used the recurrence below, starting with *P₀* = 0 and summing both orders at each insertion.

```math
P_n=bP_{n-1}+\sum_{2^i+2^j=n}\frac{1}{2^{i+j}}.
```

All 15,360 denominators agreed. Direct summation of *Sₖ* in the same bases checked all 150 congruences for 1 ≤ *k* ≤ 10 and all 135 valuations for 2 ≤ *k* ≤ 10. The universal Lean proofs build with `lake build NormalityChecker.ParameterTwoSquare`.
