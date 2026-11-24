# Binary transitions and the discrepancy of ln 2

Let $`y_n=\{2^n x\}`$. Write $`D_N`$ for the supremum of the absolute frequency error over all half-open intervals $`[a,c)\subseteq[0,1]`$ in the first $`N`$ shifts. Write $`\tau_N`$ for the number of starts $`n\lt N`$ at which the next two binary digits differ, divided by $`N`$. The two transition cylinders form exactly $`[1/4,3/4)`$, with the terminating convention at dyadic rationals.

## The general theorem

Put $`D_\infty=\limsup_N D_N`$ and $`t=\liminf_N\tau_N`$. Lean proves

```math
D_\infty < 1 \quad\Longleftrightarrow\quad t>0,
\qquad
D_\infty\le\max\left(\frac23,1-t\right).
```

The constant $`2/3`$ is sharp for a bound of this form. The orbit of $`1/3`$ alternates between $`1/3`$ and $`2/3`$. Every position is a transition. Intervals of length arbitrarily close to $`1/3`$ contain the entire orbit. At the other end of the scale, $`D_\infty=0`$ is equivalent to binary normality. In the forward direction from normality, convergence on a finite grid of anchored intervals and monotonicity control the supremum over all endpoints. [Definitions and equivalences](../NormalityChecker/BinaryDiscrepancy.lean) · [Sharp estimate and extremal orbit](../NormalityChecker/SharpDiscrepancy.lean)

**Why sparse transitions give maximal discrepancy.** Fix $`k\ge0`$ and put $`r=2^{-(k+2)}`$. Any start in $`[r,1-r)`$ has a transition within its next $`k+1`$ starts. Otherwise its first $`k+2`$ bits would all agree. Each transition accounts for at most $`k+1`$ starts, and the last $`k`$ positions may look beyond the prefix. Thus the frequency of the central interval is at most $`(k+1)\tau_N+k/N`$. Along a subsequence with $`\tau_N\to0`$, this interval has frequency tending to zero even though its length is $`1-2r`$. Taking $`k`$ arbitrarily large forces $`D_\infty=1`$.

**Why the upper bound holds.** The counts of upward and downward transitions differ by at most one, since their signed difference telescopes to the last bit minus the first bit. Each direction therefore accounts for $`\tau_N/2`$ up to $`1/(2N)`$. Write $`\ell=c-a`$.

- For excess visits, $`\ell\ge1/3`$ gives an excess of at most $`2/3`$. An interval disjoint from the transition region has frequency at most $`1-\tau_N`$. Among the remaining intervals of width below $`1/3`$, those spanning $`1/2`$, and those of width below $`1/6`$, cannot hold three consecutive shifts. This follows by substituting the two branches $`2y`$ and $`2y-1`$ for two successive steps. Their frequency is at most $`2/3+2/(3N)`$. Every other interval lies in one half and has width at least $`1/6`$, so it misses one whole transition direction.
- For a deficit, only $`\ell>2/3`$ needs attention. Such an interval either contains the entire transition region or contains one complete transition direction and has width at most $`3/4`$. These cases use the same balance of the two direction counts.

Together these estimates give $`D_N\le\max(2/3,1-\tau_N)+1/N`$ for every $`N>0`$. The proposed finite bound $`D_N\le\max(7/8,1-\tau_N)`$ is also checked for $`N\ge2`$.

## What this proves for ln 2

Define $`R_0=0`$, $`R_{n+1}=2R_n+1/(n+1)`$, and let $`H_N`$ be the fraction of $`n\lt N`$ for which $`\{R_n\}\in[1/3,2/3]`$. The project proves

```math
\liminf_N H_N \le t(\ln 2) \le 3\liminf_N H_N.
```

In particular, positive lower density in that closed middle third is **necessary and sufficient** for $`D_\infty(\ln 2)\lt 1`$. A lower density of at least $`1/1000`$ would imply $`D_\infty(\ln 2)\le999/1000`$. Establishing any positive constant remains open here. [Rational-prefix transfer and bounds](../NormalityChecker/LogTwoTransitions.lean)

For $`n\ge12`$ the positive shift error $`2^n\ln2-R_n`$ is less than $`1/12`$. A middle-third hit then gives a true transition at the same position. Conversely, a true transition rules out wraparound of that small error and puts the rational residue above $`1/6`$ and below $`3/4`$. A residue above $`2/3`$ enters the middle third at the next step. A residue below $`1/3`$ either enters at the next step or just overshoots $`2/3`$ and enters one step later. Counting with these offsets gives the finite inequalities $`H_N\le\tau_N+12/N`$ and $`\tau_N\le3H_N+14/N`$.

**Unconditional count.** Every sufficiently late interval of integer positions $`[n,34n)`$ contains a middle-third hit which is also a binary digit transition of $`\ln 2`$. Consequently, for a fixed constant $`C`$, both counts in the first $`N`$ starts are at least $`\lfloor\log_{34}N\rfloor-C`$. The proof establishes the existence of the starting cutoff. It gives a finite-prefix discrepancy bound with a gap of order at least $`(\log N)/N`$ for sufficiently large $`N`$. This lower bound on the gap vanishes as $`N`$ grows. [Window theorem and cumulative count](../NormalityChecker/LogTwoTransitions.lean)

### Arithmetic behind the count

The development includes its own coarse dyadic approximation estimate. For every sufficiently large $`n`$ and every integer $`z`$ it proves $`|2^n\ln 2-z|\ge 2^{-32n}`$. Here is the proof.

1. Set $`g(y)=(y-1)(2-y)/y`$ and integrate $`g(y)^m/y`$ from 1 to 2 to obtain $`I_m`$. On this interval $`0\le g\le1/4`$. On $`[4/3,5/3]`$, $`g\ge1/18`$ and $`1/y\ge1/2`$. Thus $`18^{-m}/6\le I_m\le4^{-m}`$.
2. Let $`L`$ be the least common multiple through $`m`$. There are integers $`A,B`$ with $`L I_m=L A\ln 2+B`$ and $`|A|\le10^m`$. To verify this, multiply the integrand by $`y^i(2/y)^j`$ and use $`g=3-y-2/y`$ to lower the power of $`g`$. At power zero the diagonal integral is $`2^i\ln2`$. Off the diagonal the integral is $`(2^i-2^j)/(i-j)`$, with $`0\lt |i-j|\le m`$ at the leaves. Multiplying by $`L`$ clears these denominators. The recurrence increases the absolute coefficient bound by at most a factor of five per step.
3. Take $`q=2^n`$ and $`m=4n`$. Mathlib's prime number theorem for the lcm implies $`L\le3^m`$ eventually, so $`0\lt qLI_m\le q(3/4)^m\lt 1/2`$ eventually. Its distance to every integer is at least $`qLI_m`$. Subtract the integer $`qB+LAz`$ and divide by $`L`$ to get $`qI_m\le |A|\,|q\ln2-z|`$. The lower bound on $`I_m`$ and the upper bound on $`|A|`$ yield the stated dyadic separation.
4. Apply the separation to both integers adjacent to $`2^n\ln2`$. The shift is far enough from both endpoints that there must be a transition by position $`n+32n`$. The rational recurrence visits the middle third within two more steps. The disjoint intervals between successive powers of 34 give the count.

The integral method belongs to classical irrationality-measure theory. Stronger published bounds for $`\ln2`$ imply stronger restrictions on individual runs. The contribution here is a kernel-checked deduction for the rational middle-third counts and discrepancy, with all arithmetic inputs proved in Lean or Mathlib. [Linear forms and separation proof](../NormalityChecker/LogTwoLinearForms.lean) · [Alladi and Robinson (1980)](https://doi.org/10.1515/crll.1980.318.137) · [Marcovecchio (2009)](https://doi.org/10.4064/aa139-2-5)

## Where the density argument stops

For the Kempner number $`K=\sum_{j\ge0}2^{-2^j}`$, Lean proves the stronger dyadic separation $`|2^nK-z|\ge2^{-n}`$ for all $`n\ge2`$ and integers $`z`$, together with $`D_\infty(K)=1`$. If $`s`$ is the first power of two greater than $`n\ge1`$, the shifted tail lies between $`2^{n-s}`$ and $`(4/3)2^{n-s}`$. A transition start must be within two positions before $`s`$. There are at most $`2k+1`$ transition starts before $`2^k`$.

This example tests the precise dyadic estimate used above. A positive-density proof for $`\ln2`$ needs information about the *total number* of long gaps. One concrete target is a fixed block length $`B`$ for which a positive lower proportion of disjoint length-$`B`$ blocks contain a middle-third hit. The multiplicative-window theorem alone allows most such fixed-length blocks to be empty. [Verified sparse obstruction](../NormalityChecker/SparseTransitions.lean)

## First-frequency escape

Put $`f(v)=1-\cos(2\pi v)`$ and let $`E_N`$ be the average of $`f(R_n)`$ for $`0\le n\lt N`$. With $`t`$ the lower limiting density of true binary transitions in ln 2, Lean proves

```math
t\le\liminf_N E_N\le 4t.
```

In particular, a positive lower limit of $`E_N`$ is necessary and sufficient for discrepancy strictly below one. The proof works for every real $`x`$ and every sequence approximating $`2^n x`$ with error tending to zero. [Finite and limiting inequalities](../NormalityChecker/FirstFrequency.lean)

For the exact orbit, let $`I(v)`$ indicate the half-open transition region $`[1/4,3/4)`$ modulo one. Then $`I(v)\le f(v)`$. Outside that region $`f(v)\le1`$ and inside it $`f(v)\le2`$. The double-angle identity gives $`2f(v)-f(2v)=2f(v)(f(v)-1)\le4I(v)`$. Summing over consecutive shifts telescopes, leaving an endpoint error at most $`2/N`$ in the upper bound. This proof includes the point $`3/4`$, where the indicator is zero and $`f=1`$. The Lipschitz bound for cosine and Cesàro averaging transfer the inequalities to the rational recurrence.

At each closed middle-third hit, $`f(R_n)\ge3/2`$. The verified hit count therefore gives an unconditional lower bound $`(3/2)(\lfloor\log_{34} N\rfloor-C)`$ for the **sum**, for sufficiently large $`N`$. After division by $`N`$ this lower bound tends to zero. The unresolved estimate is a positive lower bound for the **average**.

## Total time between middle-third hits

For a set of hit positions, define $`A_0=0`$. Set $`A_{n+1}=0`$ after a hit at $`n`$, and $`A_{n+1}=A_n+1`$ after a miss. Let $`H`$ be the number of hits before $`N`$, and let $`W_N=\sum_{i=0}^N A_i`$. Lean proves the finite inequality

```math
(N+1)^2\le(H+1)(N+1+2W_N).
```

Split the $`N+1`$ positions at the hits, retaining the last segment even when the prefix ends in a long gap. A segment of length $`d`$ contributes $`d(d-1)/2`$ to $`W_N`$. Thus the segment lengths sum to $`N+1`$, and their squares sum to $`N+1+2W_N`$. Cauchy–Schwarz gives the displayed inequality. In particular, for the rational middle-third visits of ln 2, any eventual bound $`W_N\le C(N+1)`$ would give lower hit density at least $`1/(1+2C)`$ and discrepancy at most $`\max(2/3,1-1/(1+2C))`$. An eventual mean age of at most $`499.5`$ would suffice for the one-in-a-thousand target. Even an $`O(N^{3/2})`$ total-age bound would imply a square-root hit count by the finite inequality. The project has yet to derive either estimate for ln 2. [Gap counts and conditional discrepancy theorem](../NormalityChecker/AggregateGaps.lean)

An exact-integer computation gives the following finite checks. The final column includes the unfinished last gap in the prefix.

| Starts $`N`$ | Middle-third hits | Total age $`W_N`$ |
| ---: | ---: | ---: |
| 4,096 | 1,404 | 5,069 |
| 16,384 | 5,448 | 21,874 |
| 65,536 | 21,792 | 87,703 |

These rows can be reproduced with `python3 scripts/middle_gap_counts.py 16`. At precision $`M`$ the program encloses $`2^{M-n} R_n`$ by summing integer floors of $`2^{M-j}/j`$ with at most $`n`$ grid units of accumulated error. For an enclosure meeting an endpoint, it evaluates the recurrence with exact fractions. At the last cutoff the mean age is $`87703/65537`$. The rows are computational observations. The Lean density theorem requires a bound at every sufficiently large cutoff. [Computation](../scripts/middle_gap_counts.py)

## One fixed window length suffices

Fix $`r\ge1`$. Let $`M_r(N)`$ count starts $`n\lt N`$ for which the rational residues $`R_n,\ldots,R_{n+r-1}`$ all miss the closed middle third, and let $`H_N`$ count hits before $`N`$. Each hit covers at most $`r`$ starts. At most $`r-1`$ further starts can use a hit beyond the cutoff. Thus

```math
N\le M_r(N)+(r-1)+rH_N.
```

An eventual bound $`M_r(N)\le\rho N`$ with $`\rho\lt1`$ would give lower hit density at least $`(1-\rho)/r`$ and asymptotic discrepancy at most $`\max(2/3,1-(1-\rho)/r)`$. For example, showing that at least four in a thousand length-four windows contain a hit at every sufficiently large cutoff would imply the one-in-a-thousand density target. Lean proves this implication. Establishing its hypothesis for the logarithmic recurrence remains open. [Fixed-window counts and discrepancy](../NormalityChecker/FixedGap.lean)

For the exact doubling orbit from a uniformly chosen $`x\in[0,1)`$, $`r`$ consecutive misses have probability $`(4/3)2^{-r}`$. On the left of the middle third the next point is $`2x`$, and on the right it is $`2x-1`$. Induction gives exactly $`[0,c)\cup(1-c,1)`$ for the initial points that miss all $`r`$ times, where $`c=1/(3\cdot2^{r-1})`$. The interval boundaries and their combined Lebesgue measure are kernel-checked. Summing the probabilities gives the stationary mean-age benchmark $`4/3`$. The observed $`87703/65537`$ is a finite-prefix mean for the rational recurrence. A bound at one fixed window length suffices for the density implication above, even when longer misses have uncontrolled lengths. [Exact binary-orbit intervals and volume](../NormalityChecker/FixedGap.lean)
