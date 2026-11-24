# The discrepancy spectrum of signed Stoneham phases

**Theorem (Lean).** Fix an integer *b* ≥ 2 and a prime *p* coprime to *b*. As the bounded integer phases *c* vary, the possible upper interval discrepancies of the signed Stoneham expansions are exactly the radix-*p* values of binary words that dominate all their suffixes. The spectrum is independent of *b*. Each value already occurs with phases in {0, 1}. [Formal equivalence](../NormalityChecker/ShellHistories.lean#L388) · [Original signed expansion and all-prefix theorem](signed-shell-discrepancy.md)

In detail, put *a*₀ = *c*₀ and *a*ⱼ₊₁ = *c*ⱼ₊₁ − *pc*ⱼ. In the first *N* fractional parts of *b*ⁿ*X*, starting at *n* = 0, take the supremum over half-open intervals in [0,1) of the absolute difference between frequency and length. Denote the limsup of these discrepancies by *D*∞(*X*). The signed series is

```math
X=\sum_{j=0}^{\infty}\frac{a_j}{p^j b^{p^j}}.
```

For a binary word *s* starting at index zero, let σ delete its first digit and define

```math
V_p(s)=(p-1)\sum_{i=0}^{\infty}\frac{s_i}{p^{i+1}}.
```

The spectrum *S*ₚ consists of the values *V*ₚ(*s*) for which σʰ*s* ≤ *s* in lexicographic order for every *h* ≥ 1. At a first difference the word having 0 is smaller. Equality of whole words is allowed. In radix two the criterion asks for **one** qualifying expansion. For example, 1000… qualifies for 1/2 and 0111… fails. The series defining *V*ₚ and the symbolic results below also make sense for each integer *p* ≥ 2. The discrepancy theorem uses primality and coprimality.

## Why the largest history gives the discrepancy

Let *z*ⱼ be 1 when *c*ⱼ = 0 and 0 otherwise. At the boundary *p*ʲ, the history *h*ⱼ is the word formed by reading the preceding *j* bits backwards and then padding with zeros. The zero-shell density before that boundary is *H*ⱼ = *V*ₚ(*h*ⱼ). Indeed *H*₀ = 0 and

```math
H_{j+1}=\frac{(p-1)z_j+H_j}{p}.
```

The zero-shell density is monotone between successive boundaries, since each additional position there contributes the same bit. Every sufficiently late intermediate density is bounded above by the larger of its two boundary densities. Thus its all-prefix limsup equals the boundary limsup. The all-prefix discrepancy theorem identifies this with *D*∞(*X*). [Boundary recurrence and all-cutoff reduction](../NormalityChecker/SignedShellDiscrepancy.lean#L515) · [Identification with reverse histories](../NormalityChecker/ShellHistories.lean#L366)

Take the cluster set of the words *h*ⱼ in the compact product {0,1}ᴺ. If *h*ⱼ converges along a subsequence to *s*, then *h*ⱼ₋ₕ along the same indices converges to σʰ*s*. Thus the cluster set contains all suffixes of each of its words. Two words agreeing on *k* digits have values within *p*⁻ᵏ. At a first difference, the contribution of a 1 dominates the entire remaining tail of the smaller word, strictly so for *p* > 2. In Lean we therefore maximize the **ternary** value over the cluster set to select its largest word. This resolves all binary ties. For every *p*, continuity and compactness give a limiting word whose value is the numerical limsup. Its value is bounded above by the value of the largest word, which itself is a cluster value. This proves necessity simultaneously in every radix. [Maximal limiting history](../NormalityChecker/ShellHistories.lean#L148)

For sufficiency, use the same chronological pattern for every *p*. On indices [*n*², (*n*+1)²), write *n* zeros and then the reversal of the first *n*+1 digits of *s*. At the end the history agrees with *s* for *n*+1 digits. A nonzero admissible *s* begins with 1. During padding, a history beginning with 0 is already smaller. Within the reversed part, its first *k* digits, for *k* ≤ *n*, agree with part of a suffix of *s*, followed when necessary by zeros from the padding. Truncate the history after *k* digits. Its value is bounded by that suffix value, hence by *V*ₚ(*s*). The untruncated history exceeds this bound by at most *p*⁻ᵏ. Letting *k* grow proves the converse. For the zero word take the constantly zero bit pattern. Set *c*ⱼ = 1 − *z*ⱼ. The padding gives infinitely many nonzero phases, so these particular realizations are transcendental by the paper application of Ridout's theorem. [Verified construction](../NormalityChecker/ShellHistories.lean#L237) · [Transcendence argument](signed-shell-discrepancy.md#irrationality-lean-and-transcendence-paper-corollaries)

## Periodic approximation and isolated points

**Lean** gives an explicit rational approximation. For *k* ≥ 1, repeat the block of *k* zero bits followed by the reversal of the first *k* bits of *s*. Its period divides 2*k*. Let *M*ₖ be the largest of the 2*k* limiting boundary densities. The same prefix and padding estimates give

```math
|M_k-V_p(s)|\le p^{-k}.
```

For a purely periodic bit pattern of length *L*, the limiting histories are its reversed cyclic rotations repeated forever. Read each rotation as an *L*-digit base-*p* integer using digits 0 and *p*−1. The largest such integer divided by *p*ᴸ−1 gives the rational maximum, including the all-zero and all-one patterns. This agrees with the executable `cycleMaximum`. For example, the word 1000… is approached from above by periodic words having a single 1 per period *L*. Their maxima are (*p*−1)*p*ᴸ⁻¹/(*p*ᴸ−1). [Periodic error bound](../NormalityChecker/ShellHistories.lean#L299) · [Rational maximum for the signed expansion](../NormalityChecker/ShellHistories.lean#L406)

**Zero is the only isolated point.** The smallest positive value is (*p*−1)/*p*, attained by 1000…. Every nonzero admissible word begins with 1. For such a word *s*, its *k*-digit truncation followed by zeros remains admissible. A comparison with a shifted truncation either encounters a difference among the retained digits or runs into the zeros of the shorter shifted prefix. If *s* has a 1 beyond the cut, the truncated value is strictly smaller and within *p*⁻ᵏ. Otherwise the padded periodic approximation above has a strictly larger maximum. At every sufficiently late block end its history contains all the 1s of *s* and an additional 1 at index 2*k* from the preceding block. This proof gives a distinct attainable value within *p*⁻ᵏ for every *k*. The suffix inequalities define a closed set in the compact word space, so *S*ₚ is compact. Its positive part is a nonempty perfect compact set. [Kernel proof of the gap](../NormalityChecker/ShellHistories.lean#L339) · [Compactness](../NormalityChecker/ShellHistories.lean#L418) · [Kernel accumulation theorem](../NormalityChecker/ShellHistories.lean#L491)

## Hausdorff dimension and measure (paper proof)

For every integer *p* ≥ 2 the dimension equals that of the full set of radix-*p* values with digits 0 and *p*−1. Write this dimension as

```math
d=\frac{\log 2}{\log p}.
```

There are at most 2ⁿ depth-*n* cylinders, each of diameter at most *p*⁻ⁿ. This gives the upper bound. For the lower bound fix *m* ≥ 2 and start with *m* ones followed by a zero. Continue with arbitrary blocks of length *m*, each ending in zero. Every proper suffix starts with fewer than *m* consecutive ones, so all these words are admissible. After removing the fixed prefix by a similarity, put equal independent weights on the $`2^{m-1}`$ blocks. A cylinder of *k* complete blocks has mass $`2^{-(m-1)k}`$. An interval of length at most $`p^{-mk}`$ meets at most three closed cells of the full depth-*mk* radix grid. Grid endpoints have zero mass because the mass of each nested cylinder tends to zero and each endpoint has at most two codings. At lengths between $`p^{-m(k+1)}`$ and $`p^{-mk}`$, the interval mass is consequently at most a constant depending on *m* times its length to the power (*m*−1)*d*/*m*. The mass distribution bound follows by summing over any interval cover. Let *m* tend to infinity.

The *d*-dimensional Hausdorff measure is nevertheless zero. Apart from the all-ones word, every nonzero admissible word starts with some finite run of *m* ones and avoids a run of *m*+1 ones everywhere. At depth (*m*+1)*k* there are at most $`(2^{m+1}-1)^k`$ choices for such a prefix, since each disjoint block omits the all-ones possibility. The sum of the *d*-th powers of the cylinder diameters tends to zero for each fixed *m*. Take the countable union and add the two constant words. In particular *S*₂ has full dimension and zero Lebesgue measure. Each *S*ₚ is closed and nowhere dense.

## Rational translations (paper deductions)

For rational *r*, let *d*ᵦ(*r*) be the interval discrepancy of the uniform measure on the eventual finite orbit of *r* under multiplication by *b* modulo one. For any fixed nonzero integer *m*, the signed-shell product theorem gives *D*∞(*mX*+*r*) = *d*ᵦ(*r*)*D*∞(*X*). The factor is positive because a finite orbit leaves an interval of positive length empty. Thus the spectrum at fixed *r* is exactly *d*ᵦ(*r*)*S*ₚ. Its dimension, isolation pattern, and the scaled periodic approximation bounds follow by similarity. In base 2, translation by 1/3 has factor 2/3, from the two points 1/3 and 2/3. It sends the least positive discrepancy for *p* = 3 to 4/9. [Product theorem](../NormalityChecker/TranslatedShells.lean#L221) · [Rational orbit computations and proof](translated-shells.md)

Allowing **all** rational translations yields a countable union of these copies. It has dimension *d* because the copy at *r* = 0 is included, and its *d*-dimensional Hausdorff measure is zero. Its closure is [0,1], so it has no isolated points. Here is a direct proof of density, including the rational translation factors themselves.

Fix *h* ≥ 1 and *B* = *b*ʰ. A cyclic de Bruijn word of order *h* has length *B* and contains every *h*-digit block exactly once cyclically. An Euler circuit on the graph of (*h*−1)-digit words constructs it. Make a periodic digit word of length *T* = *K* + *L* by following *K* zeros with copies of that word of total length *L*, a positive multiple of *B*. The resulting repeating rational has a nonconstant period. Counting the *T* starts gives its orbit measure even if the least period is shorter. In the long de Bruijn segment all except at most *h* starts have the same *h*-digit cell as in the cyclic word. Counting whole cells and bounding the two partial endpoint cells gives error at most 2*L*/*B* + *h* relative to *L* times the length of any interval. The *K* other starts have absolute error at most *K*. Conversely, [0,1/*B*) contains at least *K*−*h* of the zero starts. Its discrepancy is at least (*K*−*h*)/*T*−1/*B*. Altogether the factor differs from *K*/*T* by at most 2/*B* + *h*/*T*. Approximate any target by *K*/*T* with *T* large at fixed *h*, then send *h* to infinity. Since 1 belongs to *S*ₚ, every such rational factor belongs to the translated spectrum. [De Bruijn orbit construction](translated-shells.md#de-bruijn-translations)

## Changing the geometric schedule

For increasing integer boundaries *Q*₀ = 1, *Q*₁, …, set *r*ⱼ = *Q*ⱼ₊₁/*Q*ⱼ. Let *H*ⱼ be the zero density before group *j*. Counting positions gives the exact recurrence

```math
H_{j+1}=\frac{H_j+(r_j-1)z_j}{r_j}.
```

These counting identities hold for arbitrary boundaries. To realize the following examples by signed expansions, take $`Q_j=p^{e_j}`$ with *e*₀ = 0 and bounded positive steps *e*ⱼ₊₁−*e*ⱼ. Specify bounded integer phases *u*ⱼ at the chosen boundaries. For each 0 ≤ *i* < *e*ⱼ₊₁−*e*ⱼ, set the original phase *c* at index *e*ⱼ+*i* to *p*ⁱ*u*ⱼ. All these phases are bounded. Every interior insertion vanishes by the jump definition, and the zero pattern is constant throughout each group. The original arithmetic theorem therefore identifies the discrepancy with the limsup of the grouped boundary densities, including for aperiodic steps. This supplies the arithmetic justification for the examples. [Signed coefficients](../NormalityChecker/SignedPhases.lean#L14) · [All-prefix asymptotic](../NormalityChecker/SignedShellDiscrepancy.lean#L144)

* **Constant step.** With *e*ⱼ = *gj* for an integer *g* ≥ 1, every grouped bit pattern occurs and the spectrum is exactly *S* with symbolic radix *q* = *p*ᵍ. The recurrence uses *q* and the word theorem holds for every integer *q* ≥ 2. Consequently its dimension is log 2/(*g* log *p*) and its first positive value is 1−*p*⁻ᵍ.
* **Alternating ratios.** Repeat a zero group of ratio *r* followed by a regular group of ratio *t*, using admissible powers of *p*. If *P* is the limiting peak just after the zero group then *P* = 1−1/*r* + *P*/(*rt*), hence *P* = *t*(*r*−1)/(*rt*−1). With *b* = 2 and *p* = 3, the ratios (3, 9) give **9/13**, and (9, 3) give **12/13**. Both grouped indicator words are 1010…. Their refined periodic integer phases are (0, 1, 3) and (0, 0, 1) respectively. Lean checks the omitted insertion in each period and both discrepancies. [Formal examples](../NormalityChecker/ChangingShellSchedules.lean#L19)
* **Aperiodic ratios.** Use regular groups of fixed ratio *p* and zero groups of ratio *p*² at cycle indices 1, 2, 4, 8, …, of ratio *p* elsewhere. From peak to peak, an ordinary cycle applies the contraction *F*(*x*) = 1−1/*p*+*x*/*p*², with fixed point *A* = *p*/(*p*+1). The gaps between exceptional cycles tend to infinity. Thus the peaks immediately before them tend to *A*, and the exceptional peaks tend to 1−1/*p*²+*A*/*p*³ = **1−1/(*p*(*p*+1))**. All intervening peaks lie between the preceding exceptional peak and *A* because *F* contracts toward *A* without crossing it. All troughs are at most the preceding peak. This proves the asserted limsup, **11/12** for *b* = 2 and *p* = 3. The grouped bit word is still 1010…. The proof uses only steps of size one or two.

The coarsening argument proves discrepancy statements for the indicated arithmetic schedules. For arbitrary increasing boundaries the counting recurrence by itself gives the zero densities. A discrepancy identity there still requires an arithmetic estimate on the nonzero groups.

## Relation to symbolic dynamics

Parry's characterization of admissible expansions uses lexicographic comparison with the expansion of one. Baiocchi and Komornik's Theorem 2.5(a) identifies sequences with infinitely many nonzero digits that dominate all their suffixes as the quasi-greedy expansions of one in variable real bases. For our nonterminating binary words the associated base β in (1,2] solves the equation with digits *s* summing to 1 in base β. Here the value is instead evaluated in the prescribed integer radix *p*, and terminating words such as 1000… enter the discrepancy spectrum as well. Allouche studies stricter extremal conditions involving both the sequence and its digitwise complement in the univoque setting. For example, (10) repeated qualifies here and is a periodic boundary history. The weak one-sided condition imposes no uniqueness of a β-expansion. [Parry, *On the β-expansions of real numbers*](https://doi.org/10.1007/BF02020954) · [Baiocchi and Komornik, Theorem 2.5](https://arxiv.org/pdf/0710.3001) · [Allouche, `3](https://arxiv.org/pdf/math/0612816)

There is an exact comparison for *p* = 2. On [0,1], the reflected spectrum 1−*S*₂ equals the set of parameters *t* whose entire doubling orbit avoids (0,*t*), with 0 and 1 included. Indeed, complementing the bits of a suffix-maximal word reverses lexicographic order and sends its value to *t* = 1−*V*₂(*s*). A nonzero binary expansion of *t* is taken with infinitely many ones, so each shift codes its doubling iterate, using 1 for a positive iterate that reaches the circle point 0. On these expansions numerical and lexicographic order agree. An eventually-one maximal word must be all ones, since one of its suffixes is all ones. Thus every other maximal word has infinitely many zeros, exactly as this complement convention requires. The two endpoints follow directly. Carminati and Tiozzo characterize this same parameter set in `2 and describe its complementary intervals by finite Lyndon words in Proposition 4. For example, their component (1/4,1/3) reflects to the gap (2/3,3/4) of *S*₂. This identifies an existing symbolic parameter set underlying the binary discrepancy theorem. [Carminati and Tiozzo, `2](https://arxiv.org/pdf/1410.5761)

The kernel proofs here cover the discrepancy characterization, compactness, periodic error, positive gap, accumulation, and the two numerical alternating schedules. The dimension and Hausdorff-measure calculations, the varying-translation union, the general coarsening argument and the aperiodic numerical example have the paper proofs above.
