# Exact discrepancy of a rational quadratic

Let *b* ≥ 3 be odd and let α be the sum of $2^{-j}b^{-2^j}$ over the positive integers *j*. Fix integers *A* ≠ 0, *B*, *C* and a positive integer *D*. Put $x=(Aα^2+Bα+C)/D$. Write $D_N(x)$ for the supremum, over half-open intervals in [0, 1), of the absolute difference between the observed frequency among the first *N* shifts of *x* and the interval length.

At position *n*, let $P_n$ be the shifted rational prefix of the numerator polynomial. Expand the linear and square terms as sums and retain exactly the terms whose radix exponent is at most *n*, including both orders of each off-diagonal pair. Multiply by $b^n$ and include the constant term $Cb^n$. For *r* ≥ 0 put $a_r=3·2^r$ and $u_r=4·2^r$. Let *s* be the least nonnegative integer for which the denominator of $b^s/D$ is coprime to *b*. The cycle point $y_r$ is the fractional part of $b^sP_{a_r}/D$. Write $Δ_b(y_r)$ for the extreme interval discrepancy of the uniform probability on its radix cycle. [Rational prefix and shift law](../../NormalityChecker/QuadraticOrbitModel.lean) · [Cycle point and finite-period discrepancy](../../NormalityChecker/QuadraticPlateauCycle.lean)

For every choice of these coefficients, Lean verifies the exact law

```math
\limsup_{N\to\infty} D_N(x)
= \frac14 \limsup_{r\to\infty} \Delta_b(y_r).
```

It also verifies an approximation at every prefix length. For *N* ≥ 1 let $w_{r,N}$ be the number of integers in the intersection of $[0,N)$ and $[a_r,u_r)$, divided by *N*. Then

```math
D_N(x)-\max_{r\ge0} w_{r,N}\,\Delta_b(y_r) \longrightarrow 0.
```

At a given cutoff only finitely many weights are positive. The review numbers the same shell by *k* = *r* + 1. Omitting *r* = 0 changes the maximum by at most 1/*N*. Both statements allow primes dividing the radix to divide *D*. [Exact limsup](../../NormalityChecker/QuadraticPlateauSpectrum.lean#L167) · [All-prefix theorem](../../NormalityChecker/QuadraticPlateauSpectrum.lean#L116) · [Independent review](reviews/quadratic-orbits.md)

## Proof

1. **Count a partial plateau.** On $[a_r,u_r)$ the rational prefix advances by multiplication by *b*. After *s* shifts, its denominator has fixed prime support coprime to *b*. For bounded denominators the incomplete preperiod and the last incomplete cycle cost a bounded number of observations. For large denominators the fixed-support orbit estimate gives small discrepancy both on sufficiently long partial plateaus and on the full cycle. Short partial plateaus have small length relative to $2^r$. Together these give a uniform error of $o(2^r)$ in the count relative to the included length times the cycle mass of the interval. [Partial-plateau count](../../NormalityChecker/QuadraticPlateauCycle.lean#L242) · [Decay of the full-cycle factor](../../NormalityChecker/QuadraticPlateauCycle.lean#L217)
2. **Sum through an arbitrary cutoff.** Use the true lifts on the lower halves and the rational prefix lifts on the upper halves. Subtract interval length at each lower position and the corresponding cycle mass at each upper position. The lower-half estimate and the partial-plateau count bound the residual uniformly on every partial half-shell. Summing the geometric shell lengths gives an error of $o(N)$ through the cutoff. The resulting sequence of lifts differs from the true lifts by a quantity tending to zero. Circle discrepancy therefore transfers the conclusion to the real orbit, even when a limiting cycle has an atom at an interval endpoint. [Lower-half estimate](../../NormalityChecker/QuadraticOrbitShells.lean#L172) · [Circle perturbation](../../NormalityChecker/CircleDiscrepancy.lean#L137)
3. **Isolate one cycle.** Given ε > 0, discard an initial segment of at most ε*N* positions. Every plateau meeting the rest lies in a fixed-length window of recent shell indices. Eventually at most one index *j* in this window has denominator below the cutoff for cycle discrepancy ε. All other cycle contributions together have absolute centered mass at most ε on the retained positions. Thus the empirical discrepancy differs from $w_{j,N}Δ_b(y_j)$ by a quantity tending to zero as ε tends to zero. The same bound controls how much the maximum over all indices can exceed this term. [Denominator separation](../../NormalityChecker/ParameterTwoQuadraticHeight.lean#L153) · [Isolation at arbitrary cutoffs](../../NormalityChecker/PlateauEnvelope.lean#L89) · [Discrepancy of the mixture](../../NormalityChecker/CircleDiscrepancy.lean#L35)
4. **Take the limsup.** Each individual weight is at most 1/4 and equals 1/4 at *N* = $u_r$, where exactly $2^r$ plateau positions have been observed. The weights of any finite set of early plateaus tend to zero. These two facts give the exact limsup of the maximum for every sequence of factors in [0, 1]. Attainment by a particular rational quadratic remains an arithmetic question. [Limsup of the weighted maximum](../../NormalityChecker/PlateauEnvelope.lean#L52) · [Attainment discussion](reviews/quadratic-orbits.md#when-the-factor-is-attained)
