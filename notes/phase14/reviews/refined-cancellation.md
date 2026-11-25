# Review of the nonrectangular density and the resonant radix classes

For the binary shifts of the mixed Stoneham product, an independent rational calculation confirms that the ordinary upper density of nonrectangular first-precision failures lies strictly between **0.37047223953692** and **0.37047223953703**. The upper endpoint bounds the product's upper interval discrepancy. For the polynomial *X*² − 2*X*, the two opposite radix classes have the claimed counts at each admissible shell. Their infinitely recurring 2-adic parameters form a dense set of Haar measure zero in each stratum. The fixed-integer conclusion is sparsity in shell index. [Mixed-product refinement, `a80f2c6`](../nonrectangular-coverage.md) · [Radix refinement, `2050382`](../resonant-radices.md)

## Which positions can be charged

Write $P=3^K$ and $Q=5^L$ for the largest powers of each prime at most the integer position $n$. The rational prefix $R_n$ of the shifted product includes the term with indices $i,j\ge1$ exactly when $3^i+5^j\le n$. The top corner $(K,L)$ has the largest insertion time in its rectangle, so the rectangle is full at equality $n=P+Q$. In the normalized coordinate $z$, active powers $p=3^i$ and $q=r5^j$ give precisely the half-open missing-corner interval
$$
[\max(p,q),\ \min(3p,5q,p+q)).
$$
Either shell may end before the corner enters. For $a\le r\le b$, writing $v=5^j$, the interval with left endpoint $\max(p,av)$ and right endpoint $\min(3p,5bv,p+bv)$ contains the true interval for every phase. Intersecting the three outer covers (row failure, column failure and missing corner) preserves inclusion, even if their enlarged pieces use different phases. At one fixed phase, retaining only actual pieces from all three families gives a lower bound.

At depth $d$, the smallest retained row and column starts are $p_0=81^{-d}$ and $r v_0=r25^{-d}$. A shell below the grid ends by $p_0$ or $rv_0$, so the initial strip through $\max(p_0,bv_0)$ covers every omitted missing-corner interval. Missing row-failure offsets $r25^m$, $m<-d$, have right edge at most $r v_0/5$ relative to their shell start. Missing column-failure offsets $81^h$, $h<-d$, end by $p_0/27$. The source uses the larger strips of widths $bv_0$ and $p_0$ and allows the column shell start to move throughout the bracket. The retained top exponents already reach $z=81$. This accounts for offsets near the start of a large shell as well as shells near zero. [Interval construction](../../../scripts/phase14_mixed_flow.py)

On the physical unit cell $[n,n+1)$ for $n\ge1$, the shell powers are fixed and the corner threshold is integral. The two offset tests are constant there except possibly at a cell starting a shell. At such a start the discrete empty offset charges the corresponding axis, and the continuous mass can only be smaller. Thus the total count-to-integral error is $O(1+\log N)$ for every integer cutoff $N$. I compared both depth-four covers with direct integer comparisons on all cells through $531440$. Both masses equal the discrete charge on all 531,420 ordinary cells. On the other 21 cells, including the initial cell, the outer mass is bounded above by the discrete charge. The source's refined checker skips these 21 cells. [Integer cell check](../../../scripts/phase14_nonrectangular.py)

With $A=81^k\le N<81A$, take $r=25^{\lceil k\log_{25}81\rceil}/A$ and $T=N/A$. The exponent shifts preserve both failure residues. The score is the common covered length through $T$ divided by $T$. At a fixed phase the shell edges, translated offset boundaries and corner thresholds make a countable exceptional set of $z$. At every other positive $z$ the active tests are locally constant as $r$ varies. Dominated convergence on $[0,81]$, excluding the cutoff point as well, gives joint continuity. Unique factorization implies that $\log_{25}81$ is irrational, so every phase is approached at arbitrarily late scales. For any specified $1\le T\le81$, the integer cutoffs $\min(81A-1,\lfloor AT\rfloor)$ realize it in the limit. This identifies the ordinary upper density with the maximum on the closed phase and cutoff rectangle. [Coupled flow](../mixed-flow.md)

## Independent rational enclosure

For the upper certificate I removed intervals guaranteed to be usable throughout a phase bracket. An interval with its right edge at or below its left edge contributes zero. In the table $a\le r\le b$, $p=3^i$ and $v=5^j$.

| Reason to remove an interval | Indices | Left edge | Right edge |
| --- | --- | --- | --- |
| Row passes | $j$ even | $p+5bv$ | $\min(3p,p+25av)$ |
| Column passes | $4\mid i$ | $bv+3p$ | $\min(5av,av+81p)$ |
| Full rectangle | All | $p+bv$ | $\min(3p,5av)$ |

For example, the last interval starts at or beyond $p+rv$ for every phase and still belongs to both shells. Omitting any usable interval can only increase the upper bound. For the lower certificate at $r=25/2$, I counted points belonging to a retained failure band of each axis and a retained missing-corner interval. These three families are each internally disjoint at a single phase.

The following standalone Python calculation uses three-way phase subdivision. It counts uncovered length for the upper sweep and triply covered length for the lower sweep. The cumulative length includes all mass below the minimum cutoff 1. Between consecutive endpoints the ratio to the cutoff is monotone or constant, so testing the endpoints, including 1 and 81, suffices.

<details>
<summary>Exact rational sweep</summary>

```python
from fractions import Fraction
from math import lcm

def score(a, b, *, lower=False):
    assert not lower or a == b
    unit = lcm(a.denominator, b.denominator) * 3**52 * 5**32
    stop = 81 * unit
    events = {0: 0, unit: 0, stop: 0}

    def span(left, right):
        right = min(right, stop)
        if left < right:
            events[left] = events.get(left, 0) + 1
            events[right] = events.get(right, 0) - 1

    for j in range(-32, 4):
        v = unit * 5**(j + 32) // 5**32
        lo = v * a.numerator // a.denominator
        hi = v * b.numerator // b.denominator
        for i in range(-52, 5):
            p = unit * 3**(i + 52) // 3**52
            if lower:
                span(max(p, lo), min(3*p, 5*lo, p+lo))
                if j % 2 == 0:
                    span(p+lo, min(3*p, p+5*lo))
                if i % 4 == 0:
                    span(lo+p, min(5*lo, lo+3*p))
            else:
                span(p+hi, min(3*p, 5*lo))
                if j % 2 == 0:
                    span(p+5*hi, min(3*p, p+25*lo))
                if i % 4 == 0:
                    span(hi+3*p, min(5*lo, lo+81*p))

    active = previous = mass = best_mass = 0
    best_cutoff = unit
    for t, delta in sorted(events.items()):
        if active == (3 if lower else 0):
            mass += t - previous
        if t >= unit and mass * best_cutoff > best_mass * t:
            best_mass, best_cutoff = mass, t
        active += delta
        previous = t
    return Fraction(best_mass, best_cutoff), Fraction(best_cutoff, unit)

r = Fraction(25, 2)
low, cutoff = score(r, r, lower=True)
assert cutoff == Fraction(11, 2) and Fraction("0.37047223953692") < low
pending = [(Fraction(1), Fraction(25))]
leaves = length = high = 0
while pending:
    a, b = pending.pop()
    cap, _ = score(a, b)
    if cap < Fraction("0.37047223953703"):
        leaves += 1
        length += b - a
        high = max(high, cap)
    else:
        step = (b-a)/3
        pending.extend([(a, a+step), (a+step, b-step), (b-step, b)])
assert leaves == 1405 and length == 24
print(low, high)
```

</details>

The lower witness at $(r,T)=(25/2,11/2)$ gave the exact fraction
```
1634791881508260275560272742041323102136750001 / 4412724374575751913603063113987445831298828125
```
and the largest upper bound over the 1,405 closed brackets was
```
51087246297178684516977023026106149653275500009 / 137897636705577404234837349504232406616210937500
```
The original depth-12 checker also reproduced its 1,117 brackets and both strict comparisons. The lower witness bounds the density of the charged set. Its precise optimality is open. [Source certificate](../../../scripts/phase14_nonrectangular.py)

## Transfer to the actual product at every cutoff

On a full rectangle the prefix factors as $2^n$ times the product of the two truncated axis sums. The ternary axis has valuation $-K$ by its unique last term of least valuation. For the opposite sum $S_L=\sum_{j=1}^L5^{-j}2^{-5^j}$, the residues alternate modulo three, and $S_2\equiv6\pmod9$. In the cited lifting proof, a block of length $m=2\cdot3^h$ and its two shifts give $S_{3m}\equiv3S_m\pmod{3^{h+3}}$ once $v_3(S_m)=h+1$. The first-order corrections have multiplier $0+1+2$, divisible by three. Repeating a block a number of times prime to three preserves its valuation. This gives zero loss for odd $L$ and exactly $1+v_3(L/2)$ for even positive $L$. Consequently at least $K-1-\lfloor\log_3 L\rfloor$ ternary denominator layers survive on late full rectangles, uniformly tending to infinity. [Rectangle lifting proof](../../phase13/independent-axes.md#exact-loss-on-full-rectangles)

Let $E$ consist of positions where both first tests fail and the top corner is missing. Use complete blocks of length $B=2^{\lfloor\log_4 N\rfloor}$. Discarding the first block, the unfinished block and blocks containing insertions costs $O(B(1+\log N)^2)=o(N)$ positions. On a remaining block the prefix doubles with a fixed odd denominator $d$ supported on 3 and 5, with $d\le N^2\le B^6$ eventually. One sample outside $E$ forces $d$ to grow uniformly, by either a surviving top power or the rectangle estimate. The fixed-support orbit estimate and the vanishing shifted tail then bound the centered interval-count error by $o(B)$ uniformly over these blocks and test intervals. Every other complete block lies wholly in $E$ and costs at most its length. Thus $D_N\le |E\cap[0,N)|/N+o(1)$ for arbitrary cutoffs, and $\limsup D_N\le0.37047223953703$. This refinement uses the paper rectangle deduction and rational certificate. [Short-orbit block transfer](../../../NormalityChecker/ProductThreeFiveCoverage.lean) · [Shifted tail](../../../NormalityChecker/ProductThreeFivePrefix.lean)

## The dyadic coordinate and its residue counts

For an odd integer $b\ge3$, take $u\in\{b,-b\}$ congruent to 1 modulo 4 and $\lambda=\log(u^{-1})$. Write $v=v_2$ and $s=v(\lambda)=v(b^2-1)-1$. Expanding $(b^{-2^j}-1)/2^j$ and removing its linear term gives, after division by $\lambda$, terms $2^{jm}\lambda^m/(m+1)!$ with $j,m\ge1$. Their valuations are
$$
(j-1)m+sm+d_2(m+1)-1\ \ge\ j-1+2m,
$$
where $d_2$ is binary digit sum. Only finitely many pairs contribute at each precision. Summing in $j$ first gives $2^m/(1-2^m)$, and negating the correction to obtain $\kappa+1$ gives $F(\lambda)$ with coefficient $a_m=2^m/((2^m-1)(m+1)!)$. Independently, the coefficient identity $2x(F(2x)-F(x))=\exp(2x)-1-2x$ telescopes over dyadic scales to the same intercept and sign. At $u=1$ the series extends with $F(0)=0$.

Legendre's formula gives $v(a_m)=d_2(m+1)-1\ge0$ and $a_1=1$. On $4\mathbb Z_2$, division of $x^m-y^m$ by $x-y$ for distinct $x,y$ leaves a sum in $4^{m-1}\mathbb Z_2$. Thus $F-\mathrm{id}$ is $1/4$-Lipschitz and solving $x=z-(F(x)-x)$ proves surjectivity by contraction. The linear term proves exact preservation of distances. The corresponding exponential tail has Lipschitz constant at most $1/2$ since $v(m!)\le m-1$. The same argument makes exp a bijective isometry onto $1+4\mathbb Z_2$. Its inverse log preserves distances there, as does inversion since $|u|_2=1$. Hence $u\mapsto F(\log(u^{-1}))$ takes residue balls bijectively to balls of the same precision and sends $1$ to zero. [Series and isometry](../../../NormalityChecker/ResonantRadixSeries.lean) · [Arithmetic identification](../../../NormalityChecker/ResonantRadix.lean)

On $3\cdot2^{k-1}\le n<2^{k+1}$, the upper denominator formula for *X*² − 2*X* is $q_k=\max(1,2^{k-1-s}|k-\kappa|_2)$. For $H\ge0$ and $t=k-1-s-H>s$, the required ball is centered at $k+1$ modulo $2^t$ in the shifted phase. It meets the valuation-$s$ stratum precisely when $v(k+1)=s$, and then lies wholly in it. Its preimage gives one normalized class and its negative gives the other, distinct modulo 4. The normalized stratum is $u\equiv1+2^s\pmod{2^{s+1}}$. Conditional Haar mass is therefore $2^{s+1-t}$, with natural density $2^{1-t}$ among all integers and $2^{2-t}$ among odds for the two signed classes together. At $t\le s$ the test admits the whole stratum exactly when $v(k+1)\ge t$, including automatic acceptance for $t\le0$. [Exact denominator](../../../NormalityChecker/ParameterTwoQuadratic.lean) · [Two-class theorem](../../../NormalityChecker/ResonantRadixClasses.lean)

For an arithmetic check independent of the phase series, set $U_0=0$, $U_m=2b^{2^{m-1}}U_{m-1}+1$. The first $m$ terms of the Stoneham series sum to $U_m/(2^m b^{2^m})$. At the first upper-shell position put $z=b^{2^{k-1}}$ and $U=U_{k-1}$. Expanding the square and omitting its last diagonal gives the shifted prefix times $2^{2k-2}$ as the integer
$$
zU^2+U-2^kz^2U-2^{k-1}z.
$$
Divisibility by $2^{\max(0,2k-2-H)}$ tests the requested threshold. I checked the recurrence against the rational prefix at every upper position for $b=3,5,7,9,11$ and $1\le k\le6$, then enumerated two consecutive complete periods of odd radices for each row below.

| Shell $k$ | Stratum $s$ | Threshold exponent $H$ | Modulus tested | Accepted residues |
| ---: | ---: | ---: | ---: | --- |
| 11 | 2 | 0 | 256 | 93, 163 |
| 11 | 2 | 1 | 128 | 35, 93 |
| 19 | 2 | 4 | 4096 | 1429, 2667 |
| 23 | 3 | 6 | 8192 | 137, 8055 |
| 31 | 4 | 9 | 131072 | None |
| 47 | 4 | 25 | 131072 | 11857, 119215 |
| 15 | 4 | 6 | 32 | 15, 17 (whole stratum at $t=s$) |

## Infinitely many shells and fixed integers

For fixed $s,H$, after finitely many shells the event masses are at most $2^{s+1-t}$ with $t=k-1-s-H$. The geometric series converges. Borel–Cantelli applies without independence, and intersecting over integer $H\ge0$ gives $q_k\to\infty$ almost surely. In phase coordinates every residue ball within the stratum contains arbitrarily large positive integers $k+1$ of its prescribed residue. For some such $k$ beyond any specified lower cutoff, the entire target ball at precision $t$ lies inside it. The union of late targets is open and dense. The stratum is a complete residue ball, so their countable intersection is a dense $G_\delta$ of measure zero. The isometry transports both statements to normalized radices.

For each fixed odd integer radix, two hits $k<\ell$ with $t_k>0$ give $2^{t_k}\mid\ell-k$. Equivalently, for each $d$ all sufficiently late hits lie in one shell-index class modulo $2^d$. Their upper index density is at most $2^{-d}$ for every $d$, hence zero. Individual finiteness, or membership of a specified integer radix in the exceptional set, needs further arithmetic information. Neither the Haar measure nor the Baire-category calculation resolves it. [Quantifiers in the radix proof](../resonant-radices.md#fixing-a-radix-and-varying-the-shell)

I re-elaborated the three reviewed radix modules with Lean 4.36.0 against cached dependencies matching the radix commit. The declarations `phase_bijOn`, `radix_parameter`, `target_valuation_of_hit` and `resonant_residue` reported only `propext`, `Classical.choice` and `Quot.sound`. All five tests in the source radix suite passed. The Haar and category conclusions are paper deductions. [Finite radix tests](../../../scripts/test_resonant_radices.py)
