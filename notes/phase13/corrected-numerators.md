# Actual residues of corrected binary shifts of ln 2

Let $y_n$ be the diagonal beta approximation to $2^n\log 2$ in Paper V. Fix $n$, integers $0<h<k$, and primes $n+k<p\le 2n$, $p>3$. At **all but $O(k)$** of these primes, the three values $p y_{n+j}\bmod p$, for $j=0,h,k$, cannot equal $c+d2^j$ for any $c,d\in\mathbb F_p$. The constant is absolute. For $h=1,k=2$ the exceptional primes are exactly those dividing $5n+7$, so there is at most one. This is a simultaneous restriction on the actual residues at one specified triple of starts. It allows different coefficients at every prime.

A corresponding result holds for the second prime-adic digit of the two-stride beta approximation. Both estimates below apply on arbitrarily late growing windows. There is also a finite lower bound for the first Fourier deficit of the real logarithm on each of four complete dyadic shells. The asymptotic lower deficit for the real orbit remains open.

## Diagonal model without the changing normalization

Write $B(m,r)=m!r!/(m+r+1)!$. Paper V defines

```math
y_n=\sum_{i=1}^n\frac{2^{n-i}}i+\sum_{j=0}^{n-1}(-1)^j B(n,j),
\qquad
\delta_n=y_{n+1}-2y_n=\frac32(-1)^n B(n,n).
```

The reduced denominator of $y_n$ divides $L_{2n}$, where $L_M$ is the least common multiple through $M$. In the stated prime band each $p y_{n+j}$ is integral at $p$, whether or not $p$ survives reduction. If $y=a/q$ is reduced and $p\mid q$, then $p y=a/(q/p)$. Equivalently one can take a single common denominator $L=L_{2(n+k)}$ throughout the triple. It has $v_p(L)=1$, so $Ly_{n+j}=(L/p)(p y_{n+j})$ differs by the **same unit** at all three positions. Paper V's return estimate concerns $3y_n/\delta_n$. The present estimates allow us to use the numerator at a common denominator, or $p y_n$, directly. [Paper V, section on prescribed numerators](../../papers/05-classical-denominators/paper.tex#L335) · [Prior normalized recurrence](../../NormalityChecker/DiagonalNumerator.lean)

Put $q_0(X)=1$. For $j\ge1$ and $h\ge1$ set

```math
q_j(X)=\prod_{i=1}^j\frac{-(X+i)}{2(2X+2i+1)},
\qquad F_h(X)=\sum_{j=0}^{h-1}2^{h-1-j}q_j(X).
```

The factorial formula gives $\delta_{n+1}/\delta_n=-(n+1)/(4n+6)$ and hence $y_{n+h}-2^hy_n=\delta_n F_h(n)$. For $n+k<p\le2n$ every displayed denominator at $n$ is a unit modulo $p$. Moreover $p\delta_n$ is a unit. Indeed $(2n)!$ contains exactly one factor $p$, $n!$ contains none, and $p<2n+1<2p$. [Lean proof of the step ratio](../../NormalityChecker/CorrectedNumeratorIncidence.lean)

**A single prime.** Fix $p>3$ and $0<h<k$ with $2k<p$. For any three prescribed field elements $w_0,w_h,w_k$, at most $k-1$ starts $n$ in the band satisfy $p y_{n+j}=w_j\bmod p$ at all three positions. The same bound holds after subtracting $d2^{n+j}$ from each tested value for any fixed $d\in\mathbb F_p$.

To prove it put $u=w_h-2^h w_0$ and $v=w_k-2^k w_0$. The increments force $u=(p\delta_n)F_h(n)$ and $v=(p\delta_n)F_k(n)$ modulo $p$. The geometric term cancels. If $(u,v)\ne(0,0)$, then $uF_k-vF_h$ vanishes at $n$. The functions $F_h,F_k$ are linearly independent over $\mathbb F_p$. For $a\ge2$, $F_a$ has a simple pole at $X=-a+1/2$ from its final summand. The earlier summands are regular there, and the final numerator has only nonzero half-integer factors since $2k<p$. The pole of $F_k$ is absent from $F_h$, and $F_1=1$. If $u=v=0$, use $F_h(n)=0$ instead. Clearing the $k-1$ distinct linear denominator factors gives a nonzero polynomial of degree at most $k-1$. The admissible starts are distinct modulo $p$.

Consequently, in any $T$ consecutive indices of the upper band $n<p\le2n$, a specified curve $c+d2^n$ contains $O(T^{3/4})$ observations $p y_n\bmod p$. In bins of at most $H+1$ indices, allow the first two hits and charge each further hit to a triple within its bin. For each gap pair $1\le h<k\le H$ there are at most $k-1$ possible starts throughout the window. The bound is $2\lceil T/(H+1)\rceil+\sum_{k=2}^H(k-1)^2$. Take $H$ of order $T^{1/4}$ with $2H<p$. This trades some power in the exponent for removal of the changing normalization.

**Higher prime powers.** On any interval of at most $p$ consecutive indices, choose $v\ge0$ with $p^v y_i$ integral at $p$ throughout. For $p>3$ and $2k<p$, any prescribed triple of residues of $p^v y_i\bmod p^{v+1}$ has at most $2(k-1)$ starts at gaps $h,k$. This includes intervals past $p^2$. The preceding $O(T^{3/4})$ consequence for a prescribed curve holds at this precision as well.

Discard the at most $k-1$ residue classes where a denominator factor of $F_k$ vanishes. For every remaining start put $S=p^v\delta_n$. Its valuation lies between zero and $v$. The lower bound follows by subtracting the adjacent scaled models. The upper bound follows from $\delta_n=3(-1)^n/[2(2n+1)\binom{2n}{n}]$. For prescribed increments $u,v'$ modulo $p^{v+1}$ one has $u=SF_h(n)$ and $v'=SF_k(n)$ at that precision. If both vanish then $F_h(n)=0\bmod p$. Otherwise divide the congruence $uF_k-v'F_h=0$ by the largest common power of $p$ in $u,v'$ and reduce modulo $p$. At least one coefficient is a unit, so the same polynomial argument bounds the regular starts by $k-1$. As before these statements apply to the integer numerator at a fixed common denominator with exact $p$-part $p^v$.

**All primes at a given triple.** An affine fit at $0,h,k$ forces $p$ to divide the numerator of

```math
W=(2^k-1)F_h(n)-(2^h-1)F_k(n).
```

In characteristic zero $W>0$ at **every** $n$. In fact $F_h(n)/(2^h-1)$ is a weighted mean of $q_0(n),\ldots,q_{h-1}(n)$. Its numerator divided by $2^h$ is an alternating sum starting at $1/2$ and its second term in absolute value is at most $1/16$. Its value is at least $7/16$, also when $h=1$. Every new $q_h(n)$ has absolute value at most $4^{-h}$. The successive weighted means therefore decrease strictly. Multiplication by $D=2^{k-1}\prod_{i=1}^{k-1}(2n+2i+1)$ clears $W$, and $0<DW\le 2^{2k+1}D$. The product of the exceptional primes divides this positive integer. Dividing its logarithm by $\log(n+k)$ bounds their number by $O(k)$, since the band is empty unless $k<n$. For $h=1,k=2$ the rational is $(5n+7)/(4n+6)$. In this case the determinant condition is sufficient as well, since the first two abscissas $1,2$ differ by a unit. Two eligible primes would have product at least $(n+3)^2>5n+7$. At $n=10$ the prime $19$ realizes the exception. [Exact rational identity](../../NormalityChecker/CorrectedNumeratorIncidence.lean) · [Independent modular checks](../../scripts/phase13_corrected_numerators.py)

## Two-stride beta corrections and the next prime-adic digit

For $a=4,-8$ let $C_a(u,r)$ be the sum of $\sum_{j=1}^u a^{u-j}/j$ and the $r$ corrections $\sum_{j=0}^{r-1}(-1)^j B(u,j)/(a-1)^{j+1}$. Use binary starts $N=6m$ and hold the orders $r,s$ fixed over the window of starts. Set $Z_m=2C_4(3m,r)-C_{-8}(2m,s)$. This is the actual two-stride approximation to $2^{6m}\log2$. The orders may change between windows. The exact recurrence is

```math
C_a(u+1,r)-aC_a(u,r)=\frac{(-1)^r B(u,r)}{(a-1)^r}.
```

It follows by induction on $r$ using $B(u,r)-B(u+1,r)=B(u,r+1)$. For $a=4$ take three steps, and for $a=-8$ take two. The combined increment $f(m)=Z_{m+1}-64Z_m$ is

```math
f(m)=\frac{2(-1)^r}{3^r}\bigl(16B(3m,r)+4B(3m+1,r)+B(3m+2,r)\bigr)
 +\frac{7B(2m,s)+B(2m,s+1)}{9^s}.
```

The final numerator equals $8B(2m,s)-B(2m+1,s)$. For even $r$ each term of the displayed expression is positive and strictly decreasing in $m$, for every $s\ge0$. [Lean identities and strict decrease](../../NormalityChecker/CorrectedNumeratorIncidence.lean) · [Paper V's two-stride model and error](../corrected-strides.md)

**Uniform local return bound, including higher powers.** Fix $h\ge1$ and a prime $p>\max(3h+r,3(2h+s),3)$. On any interval of at most $p$ phase indices, let $v\ge0$ be such that $p^v Z_m$ is integral at $p$ throughout. An ordered pair of prescribed values of $p^v Z_m\bmod p^{v+1}$ at gap $h$ has at most $2(5h+r+s)$ starts with both endpoints in the interval. Subtracting $d64^m$ modulo $p^{v+1}$ with fixed $d$ gives the same estimate. In particular this applies to $L Z_m$ at a common denominator $L$ with $p^v\Vert L$, after scaling by the fixed unit $L/p^v$.

For the proof, $J_h(m)=Z_{m+h}-64^h Z_m$ is a rational function of $m$ alone. It is the sum over $i=0,\ldots,3h-1$ of
$2(-1)^r 4^{3h-1-i}B(3m+i,r)/3^r$ and over $i=0,\ldots,2h-1$ of
$-(-8)^{2h-1-i}B(2m+i,s)/9^s$.
A common denominator polynomial up to constant units is

```math
D_h(X)=\prod_{i=1}^{3h+r}(3X+i)\prod_{i=1}^{2h+s}(2X+i).
```

This uses $B(u,r)=r!/\prod_{j=1}^{r+1}(u+j)$. At $X=-1/3$ only the $i=0$ term of the first sum has a pole, and its coefficient is a unit. Indeed the other factors of that term evaluate to $1,\ldots,r$, and none of $3i-2$ for $1\le i\le2h+s$ vanishes modulo $p$. Thus $D_h(J_h-t)$ is a nonzero polynomial of degree at most $5h+r+s$ for every field element $t$. The roots of $D_h$ themselves cost at most that many starts. At a regular start an ordered pair $w,z$ requires $p^v J_h(m)=z-64^h w\bmod p^{v+1}$. This requires $p^v\mid z-64^h w$, and then prescribes $t=(z-64^h w)/p^v\bmod p$. This proves the claim. At precision $p^v$ the regular displacement $p^v J_h$ vanishes identically.

In the one-pole band
$2(m+h)+s<p\le3m$ and $3(m+h)+r<2p$, the only pole is the prefix term $G_{p,m}/p$, where $G_{p,m}=2\cdot4^{3m-p}$. In particular $p$ survives. Define the actual residual digit $E_{p,m}=(Z_m-G_{p,m}/p)\bmod p$. Then $pZ_m=G_{p,m}+pE_{p,m}\bmod p^2$. Since $G_{p,m+h}=64^hG_{p,m}$, the increment of $E$ is $J_h$ modulo $p$. There are no denominator roots at these starts, so each ordered pair for $E_{p,m}-d64^m$ occurs at most $5h+r+s$ times, subject to the same distinct-start and prime-size conditions. This removes the known geometric leading contribution. Paper V's two-digit return theorem treats the uncorrected single-stride Taylor prefixes. [Paper V, Taylor-prefix comparison](../dyadic-prefix-residues.md)

For a $T$-position interval in a common one-pole band and $p>\max(3H+r,3(2H+s),3)$, a prescribed $c+d64^m$ contains at most
$\lceil T/(H+1)\rceil+5H(H+1)/2+(r+s)H$ residual digits. Charge each occurrence after the first in its bin to an earlier one. With $H$ of order $\min(T^{1/3},\sqrt{T/(1+r+s)})$, this gives $O(T^{2/3}+\sqrt{T(1+r+s)})$ when $r+s=o(T)$ and $p\gg T$. The same order of magnitude holds for the higher-power bound with its extra factor two.

**Cross-prime estimate for the residual digit.** For even $r$, $0<h<k$, consider the common one-pole band for the triple, with the preceding inequalities at $k$. At all but $O(k+r+s+1)$ of its primes the three residual digits $E_{p,m+j}$ cannot fit $c+d64^j$ for any $c,d\in\mathbb F_p$. The same exceptional-prime bound holds for the three values $pZ_{m+j}\bmod p^2$ and affine fits modulo $p^2$. The residual digit formulation permits the leading geometric term to be removed separately at each prime.

Indeed every such fit requires divisibility by $p$ of the numerator of

```math
V=(64^k-1)J_h(m)-(64^h-1)J_k(m).
```

For the $p^2$ assertion the corresponding determinant is $pV\bmod p^2$. Over the rationals $63 J_h(m)/(64^h-1)$ is the weighted mean of $f(m),\ldots,f(m+h-1)$ with weights $64^{h-1-i}$. Strict decrease of $f$ implies $V>0$. The integer $3^{\max(r,2s)}D_k(m)$ clears $V$. Since $|f(m)|\le 52$ for even $r$, $V$ is bounded by $104\cdot64^{2k}$. The common band implies $p>2m$, $k,r,s=O(m)$, so the logarithm of the positive cleared integer is $O((k+r+s+1)\log(2m+2))$. Its prime divisors in the band give the estimate. The constant is absolute. [Rational checks against independently summed actual prefixes](../../scripts/phase13_corrected_numerators.py)

## A uniform estimate across growing windows and across primes

Take $T$ consecutive starts beginning at $A$, with $T\to\infty$ and $T\le A^{1-\epsilon}$ for fixed $0<\epsilon<1$. For diagonal indices use all primes in $(A+T,2A]$. For beta phase indices use $(5A/2,3A]$, with $r$ even and $r+s=O(T)$. In either case these are common admissible bands for all sufficiently large $A$ and their sizes $P$ are of order $A/\log A$. Independently for each prime choose **any** $c_p,d_p\in\mathbb F_p$. Let $t_p$ count the starts matching $c_p+d_p b^m$, with $b=2$ for the diagonal residue or $b=64$ for the residual beta digit. There is an absolute $C$ such that, with $R=CT$ for the diagonal case or $R=C(T+r+s+1)$ for beta,

```math
\frac1{TP}\sum_p t_p\le\frac2T+\left(\frac RP\right)^{1/3}.
```

For each triple of starts at most $R$ primes can agree, even allowing the affine fit to be chosen after seeing the triple. Thus $\sum_p\binom{t_p}{3}\le R\binom T3$. Apply $(t-2)_+^3\le6\binom t3$ and the power-mean inequality. The right side of the display tends to zero uniformly in the profiles. For example, the fraction of starts agreeing with their profile at a fixed positive fraction of primes tends to zero. This counts joint incidences of the **prescribed models** and uses no independence hypothesis.

When $T=o((A/\log A)^{1/4})$ the same argument gives a statement about **every triple in the whole window at once**. The number of primes for which any three points $(b^m,p y_m)$ for the diagonal model, or $(b^m,E_{p,m})$ for beta, are collinear over $\mathbb F_p$ is $O(T^4)=o(P)$. Indeed collinearity forces exactly the vanishing determinant used above, including for a vertical line. Sum the exceptional-prime bound over all triples. At the remaining primes every line contains at most two observations, even if the line is selected after computing the entire window.

These beta windows can simultaneously follow $T$ further binary shifts of each start with vanishing error. For $T=\lfloor A^\delta\rfloor$, $0<\delta<1$, take both orders at least $cT/\log(A/T)$, rounded up (to even for $r$), with $c>\log2$ and rounding error at most two. The beta bound $B(u,r)\le(r/(u+1))^r/(u+1)$ and $u\asymp A$ give $2^T\eta=o(1)$ uniformly. The orders are $o(T)$, so both the local and the cross-prime results apply. [Earlier growing-window error and entropy bounds](../sublinear-residue-windows.md)

## What overlapping CRT grids determine

Suppose the computed numerator residues leave $H_i$ equally spaced lifts at starts $n_i$. Advance them to the same binary position $N\ge n_i$ and multiply the error bounds by $2^{N-n_i}$. The new grid sizes are $h_i=H_i/\gcd(H_i,2^{N-n_i})$. Translations by every multiple of $1/g$, $g=\gcd_i h_i$, preserve **all** the aligned partial congruences and common error enclosures. At least one phase satisfies them, namely the true phase. Consequently, if $2^T\le g$, every half-open $T$-bit cylinder contains a compatible phase even after arbitrarily many observations. These alternate lifts need not be the actual corrected numerators.

**Exact displacements and arbitrarily many extra prime-adic digits.** Suppose $L_i y_i$ is integral at each start and its actual residue is specified modulo any $Q_i\ge1$, which may exceed $L_i$. Also supply every exact rational displacement $y_j-2^{n_j-n_i}y_i$ for consecutive starts. Allow the integer parts of alternative model lifts to vary. Then the permissible translations of the final phase modulo one form **exactly** the subgroup of order

```math
g=\gcd_i b_i,\qquad
b_i=\frac{L_i}{\gcd(L_i,2^{N-n_i}Q_i)}.
```

Indeed, by the exact displacements an unwrapped final translation $u$ must give the model lift $y_i+u/2^{N-n_i}$ at each start. This preserves every numerator residue precisely when $u$ lies in each lattice $(2^{N-n_i}Q_i/L_i)\mathbb Z$. Write their positive generators $a_i/b_i$ in lowest terms. Their intersection is generated by $\operatorname{lcm}_i(a_i)/\gcd_i(b_i)$, as is seen from the largest valuation at each prime. This fraction is reduced. Its integer multiples project to the entire subgroup of order $g$, and shifting the true phase together with the models preserves each error. Increasing the exponent of any prime in $Q_i$ beyond its exponent in $L_i$ leaves every $b_i$ unchanged. In particular, although the next digit provides new information about the actual unwrapped numerators as the start varies, by itself it cannot refine these fractional-phase lifts, even given all exact inter-start displacements. An independent bound on the integer parts could restrict these alternatives.

For Paper V's common cutoff $p\le y_i=M_i^\gamma$, $0<\gamma<1$, take $M_* = \min_i M_i\to\infty$. All omitted ordinary odd prime powers through that cutoff for $M_*$ are still shared by the $b_i$. Their product $G$ satisfies $\log G=(\lfloor1/\gamma\rfloor+o(1))M_*^\gamma$, by the earlier prime-power count with the $O(\log M_*)$ contribution of two removed. Thus repeated observations with this cutoff convention cannot exclude even one word when $T\log2\le\log G$. Both $T$ and the number of starts may grow. [Two-grid rigidity](../../NormalityChecker/ResidueWindows.lean) · [Ordinary prime-power cutoff](../sublinear-residue-windows.md)

Complementary prime selections behave differently. For two aligned observations consisting of $[a,b]+\mathbb Z/h$ and $[c,d]+\mathbb Z/k$ modulo one, put $l=\operatorname{lcm}(h,k)$. The possible differences $i/h-j/k$ are multiples of $1/l$. If $l[(b-a)+(d-c)]<1$, at most one lies in $[c-b,d-a]$, and the true phase guarantees one. Solve the resulting integer equation, intersect the corresponding two intervals, and translate by multiples of $1/\gcd(h,k)$. This representation of the exact intersection can be merged with the next observation by the same rule. Narrowness is checked again at each merge.

The following computations use the three consecutive starts $N-2,N-1,N$. They omit respectively the ordinary primes $\{2,3,5,7\}$, $\{2,3,5,11\}$ and $\{2,3,7,11\}$ and retain the extra power of three from the correction in each. At advance $e=2,1,0$ use the earlier least-orders rule for $T+e$ bits. The minimum ranges over all words whose closed cylinders meet the final intervals. The last column checks the actual word independently with the positive Taylor series for $\log2$.

| Binary start | Bits | Joint intervals | Admitted words | Minimum changes | Actual changes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 64 | 2,592 | 2,592 | 22 | 29 |
| 1,024 | 128 | 31,104 | 31,104 | 45 | 56 |
| 4,096 | 256 | 373,248 | 373,248 | 101 | 129 |

For a complete shell $[A,2A)$ we also apply this test to every block in its disjoint partition into length-$T$ words. We charge only the $T-1$ internal gaps of each word. Each forced change gives a shift $x=\{2^j\log2\}\in[1/4,3/4)$ and contributes at least one to $1-\cos(2\pi x)$. Dividing the certified shell count by $A$ therefore bounds the mean first Fourier deficit from below on the **entire finite shell**.

| Shell start | Word length | Blocks | Least certified changes in a block | Certified changes in shell | Actual internal changes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 64 | 4 | 15 | 76 | 139 |
| 512 | 64 | 8 | 16 | 143 | 254 |
| 1,024 | 128 | 8 | 42 | 354 | 515 |
| 2,048 | 128 | 16 | 38 | 680 | 1,049 |

Each shell has mean deficit at least $143/512$. Together the 36 disjoint blocks certify 1,253 internal changes in 3,840 bits. Paper V's two observations at 512 and 513 gave 18 forced changes in one 64-bit word. The present minima use different prime selections and charge disjoint intervals. The reproduction checks both possible merge orders, enumerates every admissible cylinder by integer ceilings and floors, and verifies inclusion of the Taylor-series word. [Exact computation](../../scripts/phase13_corrected_numerators.py) · [Paper V's original pair and word count](../../papers/05-classical-denominators/paper.tex#L574)

## Remaining obstacle

For a low-transition $T$-bit word, the allowed integers at full common denominator $L$ occupy an interval of width approximately $L2^{-T}$. On the sublinear windows above this width greatly exceeds a single prime or its square. Projecting that interval to such a prime gives every residue. The cross-prime incidence bound excludes concentration on a prescribed affine-geometric profile in each field. To use it for the real logarithm one would need to constrain the simultaneous CRT residues of the low-transition cylinders by sufficiently few such profiles, or bound directly how often the actual least numerator residue lands in those cylinders. The entropy estimate of Paper V counts possible residues at one position, while the finite shell checks cover only the four shells displayed. Neither supplies the missing estimate on arbitrarily late shells. [Fourier-to-transition implication](../intermittent-coverage.md) · [Paper V's counting estimate and its quantifiers](../sublinear-residue-windows.md)

From the repository root, run `lake env lean NormalityChecker/CorrectedNumeratorIncidence.lean` and `python3 -B scripts/phase13_corrected_numerators.py`. The Lean file verifies the rational recurrence, six-step formula, strict positivity of the beta determinant, and the diagonal step identities. The prime counts, their window consequences and the shared-divisor obstruction have the proofs above. The two tables use exact arithmetic.
