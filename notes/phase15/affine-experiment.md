# An exact affine-lift experiment for the shifted prefixes of ln 2

**Result (finite computation, exact arithmetic).** At three common shifts, integer affine combinations of a Taylor, a Gaussian and a beta approximant of 2<sup>*N*</sup> ln 2 can delete explicit divisors from the Taylor denominator at a certified price in precision. At shift 48 one Taylor–beta mixture reduces the odd denominator from 67.37 to 65.71 bits relative to beta alone, retains four future shifts, and adds 35 bits of dyadic denominator. The descending-prime searches miss this choice of divisor. For the Taylor family alone no lift removes anything from a band of primes: that is the obstruction checked at the end. These are exact computations in [`scripts/phase15_affine.py`](../../scripts/phase15_affine.py) (about 5 seconds, standard library only) for the listed shifts. The uniform theorem for Taylor cutoffs has a separate paper proof. [Taylor theorem](nearby-taylor.md)

## 1. Setting

Fix a shift *N* and a precision exponent *L*. Let *X* = 2<sup>*N*</sup> ln 2. Three rational approximants of *X* are used.

| Name | Approximant | Series for ln 2 |
| --- | --- | --- |
| T (Taylor) | Σ<sub>*j*≤*J*</sub> 2<sup>*N*−*j*</sup>/*j* | −log(1 − 1/2) |
| G (Gaussian) | Σ<sub>*j*≤*J*</sub> 2<sup>*N*</sup> Tr((1+*i*)<sup>*j*</sup>)/(*j* 2<sup>*j*</sup>) | −log\|1 − (1+*i*)/2\|² |
| B (beta) | 2<sup>*N*−*n*</sup> *y*<sub>*n*</sub>, *y*<sub>*n*</sub> = Σ<sub>*r*≤*n*</sub> 2<sup>*n*−*r*</sup>/*r* + Σ<sub>*h*&lt;*n*</sub> (−1)<sup>*h*</sup> *n*! *h*!/(*n*+*h*+1)! | Paper V diagonal beta model |

The depth of each (the cutoffs *J* and *n*) is the least one whose certified error is at most 2<sup>−*L*</sup>. The three are different rational numbers with different denominators and different errors. The companion note evaluates Padé rows separately. [Arithmetic atlas](arithmetic-lifts.md)

**Certified error.** The script computes integers lo ≤ hi with lo/2<sup>*P*</sup> ≤ ln 2 ≤ hi/2<sup>*P*</sup> (*P* = *N* + *L* + 90). It sums the independent series ln 2 = 2 artanh(1/3), rounds each term down for lo and up for hi, and adds a geometric tail bound. For a rational *R* the exact rational ε = max(\|*R* − 2<sup>*N*</sup>lo/2<sup>*P*</sup>\|, \|*R* − 2<sup>*N*</sup>hi/2<sup>*P*</sup>\|) bounds \|*R* − *X*\|. For integers *c*<sub>*i*</sub> with Σ*c*<sub>*i*</sub> = 1 the triangle inequality gives the certified combined error

```math
\Big|\sum_i c_iR_i - X\Big| \le \sum_i |c_i|\,\varepsilon_i ,
```

which is the Lean theorem `combined_error`. The script asserts that the measured error from the enclosure never exceeds this sum. **Future shifts at tolerance 2<sup>−8</sup>** means the largest *W* ≥ 0 with 2<sup>*W*</sup> times the certified error at most 2<sup>−8</sup>. It is then certified that 2<sup>*W*</sup>Σ*c*<sub>*i*</sub>*R*<sub>*i*</sub> lies within 2<sup>−8</sup> of 2<sup>*N*+*W*</sup> ln 2.

## 2. The affine lattice and its index

Write *R*<sub>*i*</sub> = *A*<sub>*i*</sub>/*M* with a common denominator *M* and let *D* be an odd divisor of *M*. The power of two in the denominator is a unit in the congruence modulo *D* and contributes separately to the full denominator. Put *d*<sub>*i*</sub> = *A*<sub>*i*</sub> − *A*<sub>0</sub> for *i* = 1, …, *k* − 1. The Lean theorem `feasible_iff_gcd` says that some integer vector *c* with Σ*c*<sub>*i*</sub> = 1 has *D* | Σ*c*<sub>*i*</sub>*A*<sub>*i*</sub> if and only if

```math
g = \gcd(D, d_1, \dots, d_{k-1}) \ \text{divides}\ A_0 .
```

The solutions form the set *c*₀ + Λ where Λ is a sublattice of the sum-zero lattice ℤ<sup>*k*−1</sup>. The map *x* ↦ Σ*x*<sub>*i*</sub>*d*<sub>*i*</sub> mod *D* has cyclic image of order *D*/*g*, so **Λ has index *D*/*g* in ℤ<sup>*k*−1</sup> and the quotient is cyclic**. Only one direction of mixing carries the congruence. The other *k* − 2 directions lie in the kernel of this residue map and are used to shorten the vector.

The degenerate cases are as follows.

* If every *d*<sub>*i*</sub> ≡ 0 (mod *D*), then *g* = *D*, the index is 1, Λ is the whole sum-zero lattice, the image has dimension 0, and every affine combination has the residue *A*<sub>0</sub>. Removal is possible only if *D* | *A*<sub>0</sub>. This is the Taylor situation of §5.
* For *k* = 1 there is no mixing, and the condition is *D* | *A*<sub>0</sub>.
* A prime *p* carried by only one approximant gives a rank-one condition: *c*<sub>*i*</sub> ≡ 0 (mod *p*). If that row is used, the absolute value of its coefficient is at least *p*.

The script builds Λ exactly (unimodular column reduction to (*g*₁, 0, …, 0), then a particular solution) and LLL-reduces it in the weighted metric. The **centre** of the search is obtained by solving the weighted real least-squares problem (the point of the real span of Λ nearest to the negative of the particular solution), writing that real minimizer in the reduced basis and rounding each coordinate. The enumeration takes ±3 around the rounded coordinates. A coefficient vector is a *genuine mixture* if at least two coordinates are nonzero. The search uses **integer weights** ⌈ε<sub>*i*</sub>2<sup>*L*+40</sup>⌉ for the error and the unit weights for the ℓ₁ norm; the exact rational error is recomputed afterwards. It is a bounded search that gives an upper bound for the true minimum. It is not a global minimization over ℤ<sup>*k*</sup>, and the weights are rounded. The only global statements below are the exhaustive box searches of §3a, which are global inside the stated box only. On 111 random feasible instances with *k* = 3 it matched or beat exhaustive search over \|*c*<sub>*i*</sub>\| ≤ 14.

## 3. Results at three shifts

Reduced odd denominators are in bits. "Support" counts odd primes. The best single approximant is B in every case.

| *N*, *L* | depths *J*<sub>T</sub>, *J*<sub>G</sub>, *n* | T bits (support) | G bits (support) | B bits (support) |
| --- | --- | ---: | ---: | ---: |
| 32, 24 | 51, 92, 18 | 64.1 (14, max 47) | 120.8 (23, max 89) | 33.0 (8, max 31) |
| 48, 40 | 82, 152, 29 | 110.2 (21, max 79) | 211.8 (35, max 151) | 67.4 (14, max 53) |
| 64, 56 | 114, 212, 39 | 163.4 (29, max 113) | 298.1 (46, max 211) | 94.8 (19, max 73) |

In these three runs the Gaussian depth is about twice the Taylor depth, admitting odd denominator primes up to the Gaussian cutoff. The beta approximant is shortest.

For each family the script removes *D*<sub>*t*</sub>, the product of the full powers of the *t* largest individually removable primes of the family's common denominator, and keeps a genuine mixture from its bounded error search at each divisor. The rows below minimize odd denominator size among those candidates with at least four certified future shifts.

| *N* | family | *D* bits | ‖*c*‖₁ | *W* | odd denominator bits | best single bits |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 48 | T, G | 21.6 | 6254721 | 10 | 188.7 | 110.2 |
| 48 | T, B | 24.7 | 54867237 | 7 | 76.9 | 67.4 |
| 48 | G, B | 28.7 | 856896913 | 4 | 183.2 | 67.4 |
| 48 | T, G, B | 120.5 | 54867237 | 7 | 76.9 | 67.4 |

At *N* = 32 and 64 the T, B row is again the best mixture, with odd denominators 48.2 bits (best single 33.0) and 123.1 bits (best single 94.8). The full table for all three shifts is the script output.

**The smallest odd denominator on the tested ladders at *N* = 48, *L* = 40.** The coefficient vector is *c* = (27433619, −27433618) on (T, B), with ‖*c*‖₁ = 54867237. The required divisor is *D* = 27433619 = 67·71·73·79. The valuations of the Taylor denominator drop by 10561943315 = 5·7·11·67·71·73·79 (33.3 bits; 5 and 7 stay with a lower exponent, 11 and the other four primes disappear), and nothing is added. The certified error is 2<sup>−15.3</sup>, and the future shifts are *W* = 7 at tolerance 2<sup>−8</sup>. The lattice index is 24.7 bits with *g* = 1. The reduced odd denominator has 76.9 bits and the support is {3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}. It is larger than B alone (67.4 bits, 14 primes, error 2<sup>−42.2</sup>).

**What determines the cost**

1. *Rank-one cost.* The primes 67, 71, 73, 79 occur in T but not in B. Removing them in the T, B family forces *c*<sub>T</sub> ≡ 0 modulo their product, and the cheapest vector has ‖*c*‖₁ = 2*D* − 1 exactly (4041, 54867237 and 2659800403257 at the three shifts). Precision is spent one-for-one with the divisor removed. The script prints this equality and does not assert it in general.
2. *A cheap Taylor–Gaussian cancellation.* For primes *p* with *J*<sub>G</sub>/3 < *p* ≤ *J*<sub>T</sub> only the first term of each series matters (the second Gaussian trace vanishes), and the Gaussian first term is exactly twice the Taylor one. So *c* = (2, −1, 0) has ‖*c*‖₁ = 3 and removes the Taylor primes 53, 59, 61, 67, 71, 73, 79 at *N* = 48 and the primes from 71 to 113 at *N* = 64 (plus 17 by coincidence), with *W* = 31 and 47. The Gaussian poles then return: the odd denominator is 166.4 bits at *N* = 48 against 110.2 for T. At *N* = 48 the three-row vector (−2, 1, 2) removes 59, 61, 67, 71, 73 and 79, with certified *W* = 30. It retains 53 from the beta row. The vector (−104, 52, 53) removes all seven and certifies *W* = 25.
3. In the candidates enumerated at all three shifts, the additional prime factors and coefficient cost leave the beta row with the smallest odd denominator. The search does not give a lower bound for unexamined mixtures.

**Outside the descending-prime ladders.** At shift 48 the Taylor–beta vector (204883990, −204883989) has coefficient norm 409767979. Its certified weighted error is approximately 2<sup>−12.42</sup>, giving four further shifts. Its odd denominator is 60452009000818733925, smaller than the single beta denominator 190103424450275260925. Its full denominator is the former integer times 2<sup>35</sup> (100.71 bits); the beta denominator is odd. The Taylor–beta ladder candidates at shifts 32, 48 and 64 have full log₂ denominators of 68.2, 112.9 and 175.1 respectively. Another off-ladder vector (893, −892) at shift 32 attains 43.85 odd bits and five further shifts. All displayed logarithms are rounded. The script prints the exact combined denominators and verifies both off-ladder witnesses.

## 3a. Two replayable examples with exhaustive box optimality

At *N* = 32, *L* = 24 the approximants are (the script prints all three exactly)

```
R_T = 60463469751752266423149615992581549 / 20309898063026564015063040
R_B = 26187609579251769344 / 8796512725
R_G = 219115580860227835658840079166871201991338473509197 / 73601715706418120223177959123463710146560
```

with certified errors ε<sub>T</sub> = 2<sup>−24.73</sup>, ε<sub>G</sub> = 2<sup>−26.09</sup>, ε<sub>B</sub> = 2<sup>−24.87</sup>. Take *D* = 43·47 = 2021, the product of the two largest primes of the Taylor denominator. Both searches below run over **every** integer vector in the stated box, so each minimum is global inside the box and says nothing about vectors outside it.

**(A) Two families, genuine mixing, minimum ℓ₁ norm.** Over all (*c*<sub>T</sub>, *c*<sub>B</sub>) with *c*<sub>T</sub> + *c*<sub>B</sub> = 1, both nonzero, \|*c*<sub>*i*</sub>\| ≤ 4142 and 2021 dividing the numerator, the minimum of ‖*c*‖₁ is 4041, attained by *c* = (2021, −2020). Its exact value and denominator are

```
2021 R_T − 2020 R_B = 1031641381899573911365189308113 / 346532069529023938560
346532069529023938560 = 2^20 · 3^3 · 5 · 7^2 · 11 · 13 · 17 · 19 · 23 · 31 · 37 · 41
```

The odd part has 48.2 bits and the power of two is 2<sup>20</sup>. The certified error is 2<sup>−12.82</sup> (measured at most 2<sup>−17.15</sup>), so *W* = 4 future shifts at tolerance 2<sup>−8</sup>. The Taylor primes 43 and 47 are gone and so is 29. The lattice search of §2 returns the same vector.

**(B) Three nonzero coefficients, exact weighted real error.** Over all *c* ∈ ℤ³ with Σ*c*<sub>*i*</sub> = 1, all three coordinates nonzero, \|*c*<sub>*i*</sub>\| ≤ 60 and 2021 dividing the numerator, the minimum of the exact weighted error bound Σ\|*c*<sub>*i*</sub>\|ε<sub>*i*</sub> (rational weights, no rounding) is attained by *c* = (−2, 1, 2) on (T, G, B). Its exact value and denominator are

```
−2 R_T + R_G + 2 R_B = 816795456204915106357409746137235243285120681 / 274364546427379714143513856455475200
274364546427379714143513856455475200 = 2^19 · 3^4 · 5^2 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 · 53 · 59 · 61 · 67 · 71 · 73 · 79 · 83 · 89
```

The certified error is 2<sup>−22.66</sup> (measured at most 2<sup>−25.52</sup>), so *W* = 14 future shifts at tolerance 2<sup>−8</sup>. The exhaustive search with the rounded integer weights and the lattice search with those weights return the same vector. For contrast, the best vector in the same box with only two nonzero coefficients is (2, −1, 0), with certified error 2<sup>−23.47</sup>. The Gaussian primes 53 to 89 return, which is why the denominator (about 2<sup>19</sup> times a 98.7-bit odd part) is larger than the one in (A).

## 4. What the experiment does and does not show

* It shows exact removal of explicit divisors, with the certified price. In the two-row examples where an entire divisor is carried by one used row, the necessary coefficient size consumes about one bit of precision per bit of divisor. Where two approximants share a prime with different residues (the Taylor–Gaussian band above) the price is far lower. It does not show a path to low-denominator lifts of ln 2 with many future shifts, since these calculations cover only three starting positions.
* The three depths are chosen for equal certified precision. Other depth rules or other approximants (Hermite–Padé, arithmetically normalized forms) are not tested.
* Outside §3a the enumeration around the rounded least-squares centre is bounded, uses rounded error weights, and is not exhaustive; the minima reported are upper bounds for the true minima. The shifts are *N* = 32, 48, 64.

## 5. The Taylor obstruction: an exact small check

**Statement checked.** Let *T*<sub>*J*</sub> = Σ<sub>*j*≤*J*</sub> 2<sup>*N*−*j*</sup>/*j*. Fix an integer *v* ≥ 1, integers *K* and *h* ≥ 0, and an odd prime *p* with

```math
\frac{K+h}{v+1} < p \le \frac{K}{v}, \qquad p^2 > K+h .
```

For every *J* in [*K*, *K* + *h*] one has ⌊*J*/*p*⌋ = *v*. So *T*<sub>*J*</sub> − *T*<sub>*K*</sub> is *p*-integral and the *p*-polar part of *T*<sub>*J*</sub> is the same for all *J* in the window. It is 2<sup>*N*</sup>*u*<sub>*v*</sub>/(*pw*<sub>*v*</sub>) modulo ℤ<sub>(*p*)</sub> with *u*<sub>*v*</sub>/*w*<sub>*v*</sub> = Σ<sub>*m*≤*v*</sub> 1/(*m* 2<sup>*m*</sup>), by Fermat. Any integer affine combination Σ*c*<sub>*J*</sub>*T*<sub>*J*</sub>, Σ*c*<sub>*J*</sub> = 1, therefore keeps *p* exactly once in its denominator unless *p* divides the fixed integer *u*<sub>*v*</sub>. By the gcd criterion of §2, *D* = ∏ of the surviving band primes has *g* = *D* and is not removable. The bands for *v* = 1, …, *V* are disjoint, with logarithmic mass about (1 − 1/(*V*+1))*K* for *h* = *o*(*K*). So the odd denominator of every such combination has logarithm at least (1 − 1/(*V*+1))*K* − *o*(*K*) for each fixed *V*, giving limiting lower rate one. The limit first fixes $V$ and then lets $V$ grow. [Paper proof and linear-width limit](nearby-taylor.md)

**Exact checks** (all passed). For each (*N*, *K*, *h*) below, with the band primes for *v* ≤ 4:

* ⌊*J*/*p*⌋ = *v* for every *J* in the window and every band prime, and *T*<sub>*J*</sub> − *T*<sub>*K*</sub> is *p*-integral for each;
* the denominator of *T*<sub>*K*</sub> contains *p* exactly once if and only if *p* does not divide *u*<sub>*v*</sub> (numerators *u*<sub>1</sub>, …, *u*<sub>6</sub> = 1, 5, 2, 131, 661, 1327);
* every integer affine combination keeps all surviving band primes in its denominator: all vectors with coefficients in {−1, 0, 1} on the *h* free coordinates, plus random vectors with coefficients up to 10<sup>9</sup>;
* *g* = *D* for the product *D* of the surviving band primes, so the lattice is the whole sum-zero lattice (index 1, mixing dimension 0) and `feasible_iff_gcd` fails.

| *N* | *K* | *h* | band primes kept | combinations checked | lost to *u*<sub>*v*</sub> |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 60 | 150 | 4 | 25 | 121 | 0 |
| 200 | 400 | 6 | 55 | 769 | 0 |
| 96 | 720 | 8 | 92 | 6601 | 0 |

The preserved logarithmic mass, divided by *K*, for *h* = ⌊√*K*⌋ and the bands *v* ≤ *V* (formula, no denominators computed):

| *K* | *V* = 2 | *V* = 4 | *V* = 6 |
| ---: | ---: | ---: | ---: |
| 10<sup>3</sup> | 0.632 | 0.738 | 0.795 |
| 10<sup>4</sup> | 0.656 | 0.783 | 0.838 |
| 10<sup>5</sup> | 0.663 | 0.794 | 0.851 |
| 10<sup>6</sup> | 0.665 | 0.798 | 0.854 |
| limit 1 − 1/(*V*+1) | 0.667 | 0.800 | 0.857 |

## 6. Reproduction

```sh
python3 -B scripts/phase15_affine.py          # about 5 seconds
python3 -B scripts/phase15_affine.py --quick  # shift 32 only, smaller obstruction table
```

The script prints each table above and ends with `All Phase 15 affine checks passed.` The sources match the [arithmetic atlas](arithmetic-lifts.md); here each depth is selected by its certified error. The script cross-checks the beta model against `corrected_model(n, n)` and the leading 64 bits of ln 2 against `log_bits(64)` from [`discrepancy_experiments.py`](../../scripts/discrepancy_experiments.py). The two examples of §3a are printed first (function `replay_examples`). The Lean statements are in [`AffineDenominator.lean`](../../NormalityChecker/AffineDenominator.lean).
