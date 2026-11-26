# Overlapping transition windows for ln 2

Let $b_n(x)$ be the first bit of the fractional part of $2^n x$, using the terminating expansion at dyadic rationals. A transition at $t$ means $b_t(x)\ne b_{t+1}(x)$, equivalently $\{2^t x\}\in[1/4,3/4)$. Write $t(x)$ for the lower limiting frequency of transitions at $0\le t<M$, and $D(x)$ for the upper limit of their interval discrepancy. At cutoff $M$ this discrepancy is the supremum, over half-open intervals in $[0,1]$, of the absolute difference between the observed frequency of the first $M$ shifts and the interval length. At start $n$ let $C_x(n,T)$ count the transitions internal to the $T$ bits $b_n,\ldots,b_{n+T-1}$.

**Conditional theorem (Lean).** Fix $0<\delta\le1$ and $\eta,\rho>0$. At each sufficiently large dyadic $N$, put $T=\lfloor N^\delta\rfloor$. Suppose at least $\eta N$ starts $N\le n<2N$ satisfy $C_x(n,T)\ge\rho T$. Then
```math
t(x)\ge\frac{\eta\rho}{6},
\qquad D(x)\le\max\left(\frac{2}{3},1-\frac{\eta\rho}{6}\right)<1.
```
The proof applies more generally to any $1\le T=T(N)\le N$ with $\sum_{N\le n<2N}C_x(n,T)\ge\alpha NT$, replacing $\eta\rho$ by $\alpha>0$. For $x=\ln2$ we prove a weaker one-change estimate on arbitrarily late shells and certify the proportional threshold at seven finite scales. Whether fixed positive $\eta,\rho$ work on arbitrarily late dyadic shells of the actual logarithm remains open here. [Lean statements and proofs](../../NormalityChecker/TransitionWindows.lean) · [Binary discrepancy inequality](../../NormalityChecker/SharpDiscrepancy.lean)

## Counting overlaps and arbitrary cutoffs

The internal offsets are $0\le j<T-1$. For fixed $j$ the map $n\mapsto n+j$ is injective. Thus the total incidence count is at most $T-1$ times the number of transitions in $[N,2N+T-2)$ for $T\ge2$. The final gap starts at $2N+T-3$ and its right bit is at $2N+T-2$. A one-bit word contributes zero. In particular, extrapolating the word starting at $2N-1$ is allowed even for $T=N$. The richness hypothesis gives total incidence at least $\eta\rho NT$ by summing over the qualifying starts.

Given a sufficiently large integer cutoff $M$, choose the largest dyadic $N\le\lfloor M/3\rfloor$. Then $3N\le M<6N$. All charged transition starts lie before $M$, so there are at least $\alpha N$ transitions in the prefix. Take the lower limit and apply the sharp binary discrepancy inequality. For the power-length specialization $1\le\lfloor N^\delta\rfloor\le N$ and $T\to\infty$. [Finite multiplicity, all-cutoff frequency and logarithm specialization](../../NormalityChecker/TransitionWindows.lean)

At an isolated good scale the same count gives frequency at least $\alpha/3$ at cutoff $3N$. Infinitely many such scales bound the **upper** transition frequency. For instance, take dyadic integers $A_1=4$, $A_{j+1}=A_j^3$, alternate bits on $[A_j,3A_j)$, and use zeros elsewhere. Every start on the shell $N=A_j$ has $T-1$ changes for $2\le T\le N$. Up to the next $A_{j+1}$ there are only $O(A_j)$ changes, including the joins. This irrational has lower transition density zero and limiting upper discrepancy one. [Equivalence between positive lower density and strict discrepancy](../../NormalityChecker/BinaryDiscrepancy.lean)

## An unconditional bound on late windows of the actual logarithm

For every sufficiently large integer $B$ and every $2\le T\le B$, there are $T-1$ consecutive starts in $[B,68B)$ whose $T$-bit words all contain a transition. The logarithm integral gives a true transition $2B\le t<68B$. Use exactly the starts $t+2-T,\ldots,t$, all of which contain both bits of this transition. This statement, including both endpoints, is kernel-checked. [Window theorem](../../NormalityChecker/TransitionWindows.lean) · [Arithmetic input](../../NormalityChecker/LogTwoTransitions.lean)

For dyadic $B$ the block has length less than $B$, so it meets at most two of the dyadic shells with left endpoints $B,2B,\ldots,64B$. On at least one such shell $[N,2N)$ there are at least $\lceil(T-1)/2\rceil$ qualifying starts. Set $T=\lfloor B^\delta\rfloor$. Increasing word length to $\lfloor N^\delta\rfloor$ retains the change. This proves a bound of order $N^\delta$ starts with **one** change on arbitrarily late dyadic scales, with gaps of at most seven shell indices between successes. For $\delta=1$ this gives a positive fraction of starts. The number of changes guaranteed per word is still one.

There is a stronger **paper consequence** for $T=N$ using the exponent-two theorem for $\ln2$ attributed to Liu–Jiang–Zhang in phase 13. For any fixed $0<c<1/3$ and all sufficiently large $N$, at least $cN$ starts in $[N,2N)$ have a change in their $N$-bit word. To see this, take $c<c'<1/3$ and choose $b>2$ with $b(1+c')<3-c'$. Dyadic separation from exponent two gives a transition in $[m,bm)$ at every sufficiently large $m$. Indeed, an uninterrupted run there would approximate the logarithm by a rational with denominator $2^m$ to within $2^{-bm+O(1)}$. Apply the window at $m=\lceil(1+c')N\rceil$. Its transition $t$ lies between $(1+c')N$ and $(3-c')N$ for large $N$. The eligible starts are the integers in $[N,2N)\cap[t-N+2,t]$, numbering at least $c'N-2\ge cN$. The arithmetic input for this all-large-$N$ deduction is the cited preprint. [Phase 13 deduction from irrationality exponents](../phase13/logarithm-transitions.md) · [Liu–Jiang–Zhang, Theorem 1 for r = 2](https://arxiv.org/abs/2610.10192v3)

## A joint arithmetic estimate with a fixed set of cells

The diagonal beta-corrected rational for $2^N\ln2$ is
```math
y_N=\sum_{r=1}^{N}\frac{2^{N-r}}{r}
+\sum_{h=0}^{N-1}(-1)^h\frac{N!h!}{(N+h+1)!}.
```
Let $L_m$ be the least common multiple through $m$, $L=L_{2N}$, and $v$ the least residue of $L y_N$ modulo $L$. The factorial quotient is the integral of $t^N(1-t)^h$ over $[0,1]$. Expanding the binomial expresses it as a sum of integer multiples of $1/(N+i+1)$ with $0\le i\le h<N$, so $L$ clears every denominator. Split $L=AB$, where $A$ is the product of primes $N<p\le2N$ and $B=L/A$. For $N\ge2$ these factors are coprime. Form the two least residues
```math
a=v B^{-1}\pmod A,\qquad b=v A^{-1}\pmod B.
```
The fractional part of $y_N$ equals that of $a/A+b/B$. This uses the actual numerator, including its complementary factor $B$. For each offset $j$ form the two four-bit cell indices
```math
i_j=\left\lfloor16\{2^j a/A\}\right\rfloor,\qquad
k_j=\left\lfloor16\{2^j b/B\}\right\rfloor .
```
Mark $j$ when $(i_j+k_j)\bmod16$ belongs to $\{5,6,7,8,9\}$. On a mark the fractional part of $2^j y_N$ lies in $[5/16,11/16)$. The two unknown within-cell remainders add less than $2/16$, including when the cell sum wraps around one. The diagonal integral bounds the absolute unwrapped error at $0\le j\le2N$ by $1/\sqrt{N+1}$. For $N\ge256$ this is strictly less than $1/16$. Each marked offset therefore certifies a true transition at $N+j$. Lean checks the two-cell implication from the CRT fractional-part identity through the actual half-open transition test. [Diagonal integral](../../NormalityChecker/LogShadowIntegral.lean) · [Two-cell transfer](../../NormalityChecker/TransitionWindows.lean) · [Diagonal numerator and upper-band residues](../phase13/corrected-numerators.md)

A sufficient extra estimate is a constant $c>0$ with at least $cN$ marks among $0\le j<N$ at every large dyadic $N$. This tests a fixed union of 80 of the 256 pairs of four-bit cells, independently of the growing word length. Two exactly uniform four-bit marginals can place all their mass at the pairs $(i,15-i)$, which give zero marks.

Here is the count from this estimate to the requested windows. Write $H$ for the number of marks in the first shell, and $m=T-1$ for $2\le T\le N$. The mark at offset $j$ contributes exactly $\min(j+1,m)$ times to the full sum of internal changes. The smallest possible sum of these contributions comes from the earliest $H$ indices. Since $\min(r,m)\ge rm/N$ for $1\le r\le N$,
```math
\sum_{N\le n<2N} C_{\ln2}(n,T)
\ge \sum_{r=1}^{H}\min(r,m)
\ge \frac{m H(H+1)}{2N}.
```
If $H\ge cN$, the total is at least $c^2NT/4$. A word has at most $T$ changes, so at least $(c^2/8)N$ words must have at least $(c^2/8)T$ changes. This also treats $T=N$ and permits all the shell marks to lie near its left endpoint. The implication in this paragraph is a paper deduction. The lower bound on the joint cell count at unbounded scales is the missing arithmetic input.

The same cell estimate at every large dyadic scale would give the sharper direct bound $t(\ln2)\ge c/(2-c)$. For $N\le M<2N$, the completed dyadic shells contribute at least $cN-O(1)$ marks. The current one contributes at least $\max(0,cN-(2N-M))$ before cutoff $M$. The resulting ratio is smallest at $M=(2-c)N$, up to the vanishing initial error. In particular, a uniform quarter of marked positions would yield $t(\ln2)\ge1/7$ and $D(\ln2)\le6/7$.

## Exact finite checks

The calculation uses one actual diagonal numerator per shell. It doubles the two CRT residues through the last required offset $2N-3$, and counts marked gaps for **every** overlapping start. Independently, integer lower and upper bounds for $\sum_{k\ge1}2^{-k}/k$ determine the true bits through index $3N-2$. Each mark is checked against those bits. In the table a rich word has at least $T/4$ internal changes. The minimum columns for $T=N$ range over all $N$ starts.

| Shell start | Marks in shell | Square-root length | Certified rich starts | Actual rich starts | Least certified changes at length N | Least actual changes at length N |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 79 | 16 | 242 | 256 | 78 | 130 |
| 512 | 164 | 22 | 460 | 507 | 148 | 237 |
| 1,024 | 335 | 32 | 975 | 1,024 | 325 | 519 |
| 2,048 | 657 | 45 | 1,938 | 2,048 | 626 | 1,011 |
| 4,096 | 1,287 | 64 | 4,037 | 4,096 | 1,258 | 1,967 |
| 8,192 | 2,519 | 90 | 8,086 | 8,192 | 2,509 | 3,987 |
| 16,384 | 5,110 | 128 | 16,327 | 16,384 | 5,046 | 8,040 |

All seven mark counts exceed $N/4$. The preceding incidence inequality therefore certifies at least $N/128$ starts with at least $T/128$ changes for every integer $2\le T\le N$ on each listed shell. At length $N$ every start passes the stronger quarter threshold using the CRT cells alone. For example, the smaller length at $N=512$ has five actual failures. The overlap count never treats the successful words as disjoint. Run `python3 -B scripts/phase14_transition_windows.py` to reproduce the table and both minima for both lengths. [Exact calculation](../../scripts/phase14_transition_windows.py) · [Independent binary enclosure](../../scripts/discrepancy_experiments.py)

## What simultaneous upper-band incidences leave undetermined

Fix a dyadic shell start $N$ and let $M$ be the odd part of $L_N$. The prime number theorem gives $\log M=N+o(N)$, since the removed power of two costs $O(\log N)$. For $s$ modulo $M$, define the following translates for the real number and its diagonal models at positions $u\ge N$.
```math
x_s=\ln2+\frac{s}{2^N M},\qquad
y_{u,s}=y_u+2^{u-N}\frac{s}{M}.
```
This preserves every exact rational displacement $y_{v,s}-2^{v-u}y_{u,s}$ for $v\ge u\ge N$, every unwrapped error $2^u x_s-y_{u,s}$, and integrality at the natural common denominator $L_{2u}$. For **every** upper-band prime $u<p\le2u$, the actual value $p y_{u,s}\bmod p$ equals $p y_u\bmod p$, because $M$ is a unit there. All simultaneous incidence tests on these observed field values therefore agree, including choices of profiles made after observing the entire window. The error identities are exact, while the translated models need only satisfy the diagonal recurrence on the observed tail. The fixed Taylor initial condition selects the actual model. [Phase 13 upper-band estimates and exact-displacement grids](../phase13/corrected-numerators.md)

In fact the whole family with the prescribed first upper-band digits, natural denominators and exact displacements can be described. A rational translation $q=d/L$ at $N$ preserves $p y_N\bmod p$ precisely when $p\mid d$, for each $p\mid A$, since $p q=d/(L/p)$ and $L/p$ is a unit at $p$. Thus $A\mid d$ and $q\in B^{-1}\mathbb Z$. The displacements force the subsequent translations to be $2^{u-N}q$. Every prime divisor of $B$ is at most $N$, so these translations meet all later upper-band tests and denominator conditions automatically. Modulo one there are exactly $B$ choices at the anchor. They split into cosets of the $M$-point grid above.

There is an explicit bad completion for $0<\delta<1$. Take $s=-\lfloor M\{2^N\ln2\}\rfloor$. The first $N$ bits remain those of $\ln2$, and $0\le\{2^Nx_s\}<1/M$. For all large $N$, $2^{N+T-1}\le M$ since $(N+T-1)\log2=(\log2+o(1))N<N+o(N)$. All $N+T-1$ bits used by the overlapping shell words are zero. The countermodel varies with $N$. If any finite list of additional digits is specified at primes $p>N$, multiply the translation by the product of sufficiently high powers of those primes. This multiplier is a unit modulo $M$, so the same fractional grid and zero-word choice remain available. At these higher precisions the choice may change the integer parts and the initial $N$ bits. At $N=64$ and $T=8$ the script verifies a translated completion with 83 zero bits, identical adjacent displacements, and all 1,139 upper-band observations unchanged at the 64 shell starts. [Exact countermodel check](../../scripts/phase14_transition_windows.py)

**An exponential estimate conditional on the actual upper-band data.** For dyadic $N\ge256$, let $H_s$ be the number of marks in $0\le j<N$ for the translated numerator $L y_{N,s}$. On the $M$-point grid, on any of its cosets, and hence among all $B$ choices, the fraction that fail to produce $N/4$ marks is at most
```math
4\left(\frac{59}{64}\left(\frac{4}{3}\right)^{1/4}\right)^{N/4}
+\frac{2^{N+3}}{M}.
```
Both terms decay exponentially in $N$. Indeed $M\mid B$, so the actual upper-band indices $i_j$ stay fixed. The complementary phase starts at $b/B+s/M$ modulo one. Temporarily give it uniform Lebesgue measure. For each fixed class $j\bmod4$, the four bits that define $k_j$ are disjoint from those at every other offset of that class, hence independent. Each mark has probability $5/16$ for every fixed $i_j$. If the total falls below $N/4$, at least one class of $m=N/4$ offsets has a mark count $X<m/4$. On this event $(3/4)^X>(3/4)^{m/4}$, whereas its expectation is $(11/16+(5/16)(3/4))^m=(59/64)^m$. Markov's inequality and the four classes give the first term, whose base is less than one since $4\cdot59^4<3\cdot64^4$. To recover the grid count, express the event as a union of half-open cylinders of length $2^{-(N+3)}$, each with at most $M2^{-(N+3)}+1$ grid points. Summing the extra point per cylinder gives the second term. Translating the grid by a coset representative preserves this bound. The prime number theorem gives $2^{N+3}/M=\exp(-(1-\log2+o(1))N)$. This argument assumes no independence among primes or among the actual orbit positions.

Thus, except for an exponentially small fraction of these compatible completions, the preceding shell-count inequality gives at least $N/128$ starts with $T/128$ changes **simultaneously for every** $2\le T\le N$ (take $c=1/4$). The bad completion has zero marks in the first shell, even though it preserves the same upper-band values and exact displacements.

For a fixed power length one can also require **all** words to be rich. Fix $0<\rho<1/2$ and $0<\delta\le1$. For each start $u\ge N$, the phases from each $M$-element coset form a grid of mesh $1/M$ because $M$ is odd. Every half-open $T$-bit cylinder contains at most $M2^{-T}+1$ grid points. The number $W$ of words with fewer than $\rho T$ changes is $2\sum_{0\le h<\rho T}\binom{T-1}{h}$, by choosing the initial bit and its change offsets. A union bound over all $N$ overlapping starts shows that the fraction of completions with even one failing word is at most
```math
N W\left(2^{-T}+\frac{1}{M}\right).
```
This tends to zero. With $H_2(r)=-r\log_2 r-(1-r)\log_2(1-r)$, the binomial entropy estimate gives $W\le 2^{(H_2(\rho)+o(1))T}$ with $H_2(\rho)<1$, while $T\gg\log N$, $T\le N$ and $M\ge2^N$ eventually. This is an unconditional count in the family of lifts of actual arithmetic data. For $\delta<1$ that family simultaneously contains the all-zero shell above. The count does not locate the fixed lift $s=0$.

Two variants clarify the linear endpoint.

- **Keep exact displacements and the affine incidence bounds.** For $T=N$ replace $M$ by the odd part of $L_{2N}$. Its logarithm is $2N+o(N)$, so the same construction can prescribe $2N-1$ zero bits and retain the initial $N$ bits. Now some individual upper-band values change. For each such $p$ the change in $p y_{u,s}\bmod p$ is a fixed multiple of $2^{u-N}$, since $v_p(M)\le1$ for $p>N$. Every cross-prime determinant and every bound uniform over profiles $c_p+d_p2^u$ is preserved by relabeling $d_p$.
- **Keep the exact upper-band values at every index.** Put $z_u=y_u-\lfloor L_u y_u\rfloor/L_u$. Then $L_{2u}z_u$ is integral, $p z_u=p y_u\bmod p$ for every $u<p\le2u$, and $0\le z_u<1/L_u$. These rational phases shadow the zero orbit through $u$ further shifts with error at most $2^u/L_u\to0$. Here the unwrapped displacements can change. This is a single sequence exhibiting the failure of an inference from the full moving upper-band values alone.

Build the standalone module with `lake build NormalityChecker.TransitionWindows` and replay it with `lake env leanchecker NormalityChecker.TransitionWindows`. The countermodels and the count over completions are paper arguments. They explain why the fixed arithmetic correlation between the upper and complementary factors is part of the cell test. The numerical bounds in the table concern the actual lift. A proof of the proposed joint estimate on arbitrarily late shells, or of the uniform estimate needed for strict discrepancy, is still missing.
