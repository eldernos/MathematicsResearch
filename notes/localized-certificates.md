# Finite certificates for prime-restricted logarithms

The decimal logarithmic series supported on the primes 2, 3 and 5 is normal. In particular, the three exponents below are independent.

```math
X=\sum_{a,j,c\ge0}\frac{1}{2^a3^j5^c\,10^{2^a3^j5^c}}.
```

The Lean theorem `decimal_series_normal` states this formula directly. The same proof applies to the decimal supports $`\{2,5,7\}`$ and $`\{2,5,11\}`$, and to $`\{2,3,5,7\}`$ in base 30. [Formal examples](../NormalityChecker/LocalizedExamples.lean)

## The five decimal residues

Write $`P_n=\sum_{m\le n}10^{n-m}/m`$, summing over supported positive integers. On $`3^k\le n<3^{k+1}`$, set $`t=n/3^k`$. The rational $`3^k10^{-n}P_n`$ has a denominator coprime to 3, so it reduces modulo 9. For $`k\ge1`$, the top layer contributes $`r^{-1}`$ for $`r\le t`$, and the next contributes $`3r^{-1}`$ for $`r\le3t`$. Here $`r`$ ranges over products of powers of 2 and 5. Lower layers vanish. The decimal power contributes 1 modulo 9.

| Range of $`t`$ | Terms newly present at the left endpoint | Accumulated residue modulo 9 |
| --- | --- | ---: |
| $`[1,4/3)`$ | Top cofactor 1 and second-layer cofactors 1, 2 | 1 |
| $`[4/3,5/3)`$ | Second-layer cofactor 4 | 4 |
| $`[5/3,2)`$ | Second-layer cofactor 5 | 1 |
| $`[2,8/3)`$ | Top cofactor 2 | 6 |
| $`[8/3,3)`$ | Second-layer cofactor 8 | 3 |

Thus $`3^{k-1}`$ divides the reduced denominator of $`P_n`$ at **every** cutoff on these scales. Two factors of 3 can cancel in the *difference* of two prefixes, as the earlier collision example shows. The accumulated residues in the last column decide what survives in the full prefix. At $`k=0`$, the top layer alone gives residues 1 and 6 at $`n=1,2`$. [Denominator and table theorems](../NormalityChecker/LocalizedExamples.lean) · [Earlier collision](mixed-localized-logarithms.md)

## General certificate

Fix a base $`b\ge2`$, an odd prime $`p\nmid b`$, and a finite set $`S`$ of other primes. Every supported index has a unique expression $`m=p^j r`$ with $`r`$ supported on $`S`$. At precision $`L=\ell+1`$, use $`w=(b^{-1})^{p^s}\bmod p^L`$. The checker verifies $`w^p=w`$. The seed $`s=\ell`$ always works by Euler's theorem. A smaller seed can make the certificate valid on earlier scales. [Unique layer decomposition](../NormalityChecker/LocalizedSupport.lean) · [Lift and certificate proofs](../NormalityChecker/LocalizedCertificate.lean)

For $`p^k\le n<p^{k+1}`$ and $`k\ge s+\ell`$, set $`u=\lfloor n/p^{k-\ell}\rfloor`$. In the normalized unshifted prefix, layer $`j=k-i`$ contributes the following residue.

```math
\sum_{0\le i\le\ell}p^i
\sum_{\substack{r\text{ supported on }S\\r p^{\ell-i}\le u}} r^{-1}w^r\pmod{p^L}.
```

Each omitted layer contains a factor $`p^L`$. The inverse radix power in a retained summand is $`w^r`$, since $`j\ge s`$. To evaluate every cutoff it suffices to test the left endpoint $`p^\ell`$ and all thresholds $`r p^{\ell-i}`$ in $`[p^\ell,p^{\ell+1})`$. At every integer grid point the included terms coincide with those at the greatest preceding threshold, including the threshold itself. If all tested values are nonzero, $`p^{k-\ell}`$ divides the reduced shifted denominator. Zero cells can still yield a quantitative bound at the same precision. [Partial discrepancy certificates](finite-support-discrepancy.md) [Soundness for every cutoff](../NormalityChecker/LocalizedCertificate.lean)

```lean
import NormalityChecker
open NormalityChecker.LocalizedSupport
-- base, selected prime, precision minus one, seed, other support primes
#eval passes 10 3 1 0 {2, 5}  -- true
#eval passes 10 3 0 0 {2, 5}  -- false
```

The independent Python implementation accepts the **precision** and the **whole support**. `python3 scripts/localized_certificate.py 10 3 2 2 3 5` prints the five left endpoints and their residues. It uses exact rational thresholds and modular inverses. [Command-line implementation](../scripts/localized_certificate.py)

| Base | Full support | Selected prime | Modulus | Cells | Lean conclusion |
| ---: | --- | ---: | ---: | ---: | --- |
| 10 | 2, 3, 5 | 3 | 9 | 5 | Normality |
| 10 | 2, 5, 7 | 7 | 343 | 22 | Normality |
| 10 | 2, 5, 11 | 11 | 11 | 6 | Normality |
| 30 | 2, 3, 5, 7 | 7 | 7 | 6 | Normality |
| 2 | 2, 5, 7 | 7 | 7 | 4 | Normality |
| 2 | 2, 5, 11 | 11 | 11 | 6 | Normality |
| 2 | 2, 5, 7, 11, 13 | 13 | 13 | 8 | Normality |

## From a denominator to digits

Assume every prime of $`S`$ divides $`b`$. Through position $`2^D`$ there are at most $`(D+1)^{|S|+1}`$ insertions, by counting exponent vectors. Each cofactor $`r\le2^D`$ divides $`b^D`$. Once the latest insertion is at least $`D`$ digits old, the entire shifted denominator divides $`p^k`$. The certificate supplies the lower bound $`p^{k-\ell}`$. [Counting and clearing lemmas](../NormalityChecker/LocalizedClearing.lean)

On scales of size $`K^6`$, partition into blocks of length $`K^5`$. Charge at most two blocks per insertion and one final partial block. On every other block the prefix evolves by multiplication by $`b`$. After multiplication by a fixed nonzero Fourier frequency $`h`$, its reduced denominator $`Q`$ is still comparable to $`K^6`$, with constants depending on the certificate and $`h`$. Its multiplicative period is at least $`Q/(b^{p-1}-1)`$. The incomplete-orbit estimate saves a factor $`K`$ on each such block. The charged proportion is $`O((1+\log K)^{|S|+1}/K)`$. This proves cancellation for arbitrary final cutoffs. The shifted tail is at most $`1/(n+1)`$, so the actual radix orbit satisfies Weyl's criterion. [Kernel-checked normality theorem](../NormalityChecker/LocalizedCertifiedNormal.lean)

## Several surviving denominator primes

On clean blocks all remaining prime divisors belong to a fixed support coprime to the base. Their product $`c`$ is fixed, although their exponents vary. After clearing base factors the denominator divides a power of $`c`$ and is polynomially bounded in the block length. One passing prime test forces the reduced denominator to grow on every clean block. The qualitative fixed-support estimate proves uniform cancellation and yields binary normality for all three supports in the table. The theorem `normal_of_smooth_estimate` exposes the analytic input and `normal_of_certificate` supplies its proof. [Fixed-support estimate](../NormalityChecker/SmoothOrbit.lean) · [Unconditional binary results](../NormalityChecker/SmoothCertificates.lean) · [Comparison with Vandehey](arithmetic-certificates.md#the-fixed-prime-set-estimate)

## Higher orders

For coefficients $`m^{-s}`$, $`s\ge1`$, use `passesPower s b p ell seed S`. Each contribution changes from $`p^i r^{-1}w^r`$ to $`(p^i r^{-1})^s w^r`$. The formal checker uses the same complete grid as the order-one test. The Python version omits layers with $`is\ge L`$, whose contributions vanish identically, so it can print fewer intervals with the same residue function. A successful test implies $`p^{sk-L+1}`$ divides every sufficiently late shifted denominator and gives base-$`b`$ normality. The mixed two-generator theorem also covers cases where no passing finite table has been found. [Modular proof](../NormalityChecker/LocalizedCertificate.lean) · [Normality from the higher-order test](../NormalityChecker/SmoothCertificates.lean) · [Mixed generator proof](../NormalityChecker/MixedPowers.lean)

```lean
import NormalityChecker
open NormalityChecker.LocalizedSupport
#eval passesPower 2 10 3 0 0 {2, 5}  -- true, order 2 at modulus 3
example : passesPower 2 10 3 0 0 {2, 5} = true := by decide +kernel
```

`python3 scripts/localized_certificate.py 10 3 1 2 3 5 --order 2` gives residues 1 and 2 on the two cells beginning at 1 and 2. [Independent exact-prefix check](../scripts/test_localized_certificate.py)

## Scope for the full logarithm

All counting constants above are for a fixed support. For the binary logarithm, if $`p_*`$ is the first omitted prime, the single omitted term gives $`2^N(\ln 2-X_{2,P})\ge 2^{N-p_*}/p_*`$. The dense sequence of insertions still prevents this block argument from supplying the four-position miss estimate. The quantitative discrepancy estimate for the checkpoint-6 two-generator family is now kernel-verified. [Four-position target](transition-discrepancy.md) · [Two-generator rate](mixed-localized-logarithms.md#quantitative-interval-discrepancy)
