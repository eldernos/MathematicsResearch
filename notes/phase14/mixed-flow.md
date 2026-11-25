# Ordinary simultaneous failures for the two-prime Stoneham product

Let $x=\alpha(2,3)\alpha(2,5)$, where
$\alpha(2,c)=\sum_{j\ge1}2^{-c^j}/c^j$. For $n\ge5$, let $P$ and $Q$ be
the largest powers of three and five at most $n$. For the shifted rational
prefix take

$$
R_n=\sum_{3^i+5^j\le n}\frac{2^{n-3^i-5^j}}{3^i5^j},
\qquad i,j\ge1.
$$

A top power fails when it does not divide the reduced denominator of
$R_n$. Let $J$ count positive
powers of five at most $n-P$ and $I$ count positive powers of three at most
$n-Q$. The ternary top power fails exactly when $J$ is even, and the quinary
top power fails exactly when $4\mid I$. Let $F(N)$ count simultaneous
failures for $0\le n<N$, extending the two counts to the initial positions
by the same empty-count convention as Lean. Changing these finitely many
positions gives the same upper density. [Residue and reduced-denominator tests](../../NormalityChecker/ProductThreeFiveResidues.lean)

**Theorem.** The ordinary upper density $\rho=\limsup_{N\to\infty}F(N)/N$ satisfies

$$
0.575523806608492 < \rho < 0.575523806608494.
$$

Write $D_N(x)$ for the supremum over half-open intervals in $[0,1)$ of the
absolute error between interval length and the observed frequency among
the fractional parts $\{2^n x\}$, $0\le n<N$. Then $\limsup_N D_N(x)\le\rho$. The enclosure
above is a paper deduction with an exact rational certificate. Lean separately
proves $250000F(N)\le143881N$ for every $N\ge81^5$, and hence
$\limsup_N D_N(x)\le143881/250000=0.575524$. Both conclusions improve the
earlier discrepancy bound $27/40$. The lower endpoint of the enclosure
concerns the frequency of simultaneous failures. The harmonic density of
these failures is $1/8$. [Exact rational certificate](../../scripts/phase14_mixed_flow.py) ·
[Kernel finite-prefix and discrepancy theorems](../../NormalityChecker/ProductThreeFiveOrdinary.lean) ·
[Earlier bound and proof of logarithmic density](../phase13/independent-axes.md)

## From integer positions to ordinary flow

Extend both power grids to all integer exponents on the positive real axis.
In a shell $[P,3P)$ the row fails on the translates by $P$ of the intervals
$[25^j,5\cdot25^j)$, $j\in\mathbb Z$. In a shell $[Q,5Q)$ the column
fails on translates by $Q$ of $[81^h,3\cdot81^h)$, $h\in\mathbb Z$.
Intersect each translate with its own shell. Let $f$ be the indicator that
both tests fail. At zero or at a shell start a value on a single point is
immaterial to the integral.

On every physical unit cell $[n,n+1)$ with $n\ge1$ away from a shell start,
both offsets are at least one. Every threshold that can change either test
there is an integer. The value throughout the cell is therefore the discrete
joint charge at $n$. Within a cell starting at a shell boundary, the
corresponding discrete empty count charges that test, while the extension
to negative powers can only reduce its charge. This gives, for $N\ge1$,

$$
0\le F(N)-\int_0^N f(y)\,dy
\le 1+\#\{i\ge0:3^i<N\}+\#\{j\ge0:5^j<N\}.
$$

The first term covers $[0,1)$. At a common insertion such as $81+25=106$,
both tests use the new endpoint on the same unit cell. No independence
assumption enters the count. [Worked prefix at 105 and 106](../phase13/independent-axes.md#exact-residues-of-a-prefix)

Choose $A=81^k\le N<81A$ and the least $25^l\ge A$. Put $T=N/A$ and
$r=25^l/A$, so $1\le T\le81$ and $1\le r\le25$. After the change of variable
$y=Az$, the row shell starts are $3^i$ and the column shell starts are
$r5^j$. The exponent shifts are multiples of four and two, preserving both
residue tests. Thus, with all the indices below in $\mathbb Z$, the failing
sets in normalized coordinates are

$$
\begin{aligned}
R_r &= \bigcup_{i,j}
  [3^i,3^{i+1})\cap[3^i+r25^j,3^i+5r25^j),\\
C_r &= \bigcup_{j,h}
  [r5^j,r5^{j+1})\cap[r5^j+81^h,r5^j+3\cdot81^h).
\end{aligned}
$$

Define $M(r,T)=|[0,T)\cap R_r\cap C_r|/T$, with $|\cdot|$ denoting length.
The physical prefix integral divided by $N$ is exactly $M(r,T)$. In
logarithmic time the **ordinary** prefix has the exponential weight

$$
M(r,T)=\int_0^\infty e^{-s}\,\mathbf 1_{R_r\cap C_r}(T e^{-s})\,ds.
$$

The harmonic count instead averages the indicator uniformly in logarithmic
time. Equidistribution of the eight residue sheets gives the harmonic density
$1/8$ in Phase 13. Here the ordinary upper density is the **maximum**

$$
\rho=\max_{1\le r\le25,\ 1\le T\le81} M(r,T).
$$

Indeed $\log81/\log25$ is irrational by unique factorization. The fractional
parts of $k\log81/\log25$ are dense on every tail, so the phases
$25^{\lceil k\log81/\log25\rceil}/81^k$ approach any prescribed $r$ along
arbitrarily late scales. For each such $k$, choose the integer cutoff
$\min(81A-1,\lfloor AT\rfloor)$, which realizes the required limit even at
$T=81$. The continuity of $M$ proved below gives the lower bound at every
phase and cutoff. Compactness and the unit-cell estimate give the reverse
bound. This argument realizes the maximum as an ordinary subsequential
density for the original, unshifted integer grids. [Kernel power-alignment lemma](../../NormalityChecker/ProductThreeFiveFlow.lean) · [Phase 13 irrational-flow argument](../phase13/independent-axes.md#the-logarithmic-distribution-of-the-coupled-endpoints)

## An exact formula using finite rational maxima

At depth $d\ge1$ retain ternary powers $3^i$ for $-4d\le i\le4$ and
quinary powers $r5^j$ for $-2d\le j\le3$. Use the retained powers both as
shell starts and, at the appropriate multiples of four or two, as opposite
offsets. Let $M_d$ be the resulting intersection length divided by $T$.
The upper exponent limits cover $[0,81]$ for every admissible $r$.
The omitted ternary and quinary shells occupy at most $81^{-d}$ and
$25^{1-d}$ in length. In each retained row shell the omitted quinary
offsets lie within $25^{1-d}$ of its start. In each retained column shell
the omitted ternary offsets lie within $81^{-d}$ of its start. Since
$T\ge1$, uniformly in both coordinates,

$$
0\le M-M_d\le (4d+6)25^{1-d}+(2d+5)81^{-d}.
$$

For a retained row and band, write $p=3^i$, $v=25^j$. For a retained
column and band, write $q=5^s$, $u=81^h$. Their contribution to $TM_d$ is

$$
\big[\min(T,3p,p+5rv,5rq,rq+3u)-\max(p+rv,rq+u)\big]_+,
\qquad [z]_+=\max(0,z).
$$

Each positive-length piece occurs once. This expression clips *both* full
shell edges and the last partial shell at $T$, including when the active
shell is different on the two axes. The finite sum is continuous, so its
uniform limit after division by $T$ is continuous as asserted.

There is an exact rational sequence for the constant. In the rectangle
$[1,25]\times[1,81]$, cut along the lines where two of the affine
endpoint expressions in the finite sum agree. Include the sides of the
rectangle. Let $V_d$ be the vertices of the resulting finite subdivision.
All vertices are rational. On each polygon $TM_d$ is affine. The ratio of
an affine numerator to $T>0$ at a convex combination of vertices is the
average of their ratios with weights proportional to the vertex weights
times their $T$ coordinates. Consequently

$$
m_d=\max_{(r,T)\in V_d} M_d(r,T),\qquad
\rho=\lim_{d\to\infty}m_d.
$$

The sequence increases and the uniform error above bounds $\rho-m_d$.
The following enclosure computes the maximum more efficiently.

## Rational enclosure of the maximum

For a closed phase bracket $a\le r\le b$ the script takes an outer union
for **each** axis. A retained row stripe starts no earlier than $p+av$ and
ends no later than $\min(3p,p+5bv)$. In a column the corresponding bounds
are $aq+u$ and $\min(5bq,bq+3u)$. The additional outer intervals are the
omitted starting shells and the initial strips in each retained shell
described above, using $b25^{-d}$ for the quinary cutoff. Intersecting
the two outer unions bounds every joint failure throughout the bracket.
At a single phase, simply omitting the tails gives an inner union.

For either union merge overlapping intervals, intersect the two axes, and
sweep the resulting disjoint intervals in increasing order. If the covered
length through $T$ is $L(T)$, $L(T)/T$ increases weakly inside a covered
interval and decreases weakly in a gap. Its maximum on $[1,81]$ is found
by testing $1$ and every right endpoint clipped at $81$. The sweep carries
forward the entire mass below $1$. This checks cutoffs inside covered
pieces, cutoffs in gaps, and both ends of the normalization range.

Run `python3 scripts/phase14_mixed_flow.py`. At depth 16 the inner sweep
at $r=1250/81$ gives $T=493/81$ and a ratio strictly above the lower
decimal in the theorem. Here $T=r/5+3$ ends a column band. Bisecting
$[1,25]$ and checking the outer sweep on each of the 1,304 terminal
brackets gives an upper bound strictly below the upper decimal.
All powers, lengths, comparisons and rounding checks use integers or
exact fractions. The program prints both rational bounds. The witness
establishes the lower bound. Its exact optimality remains open. A separate
pass compares the normalization against the two integer-log tests in every
unit cell through position 531440, including every shell and stripe edge
in that range. [Reproduce the certificate](../../scripts/phase14_mixed_flow.py)

## Kernel bound for the actual product

The Lean proof uses the same two survival tests directly on integers.
For $N\ge H=81^5$ choose $B=81^k$ so $HB\le N<81HB$, and choose a
power $Q=25^l$ between $B$ and $25B$. Bracket $Q/B$ between $a/D$ and
$b/D$, with $D=2^{30}$. For $q=5^j$ put
$L(q)=\lfloor aq/D\rfloor$ and $U(q)=1+\lfloor bq/D\rfloor$.
Then $B L(q)\le Qq\le B U(q)$. With $p=3^i$, each of the following
half-open windows is guaranteed to have zero joint charge. The endpoints
in the table are in units of $B$ and are clipped at $81H$.

| Surviving test | Exponent condition | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| Ternary row | *j* odd | *p* + *U*(*q*) | min(3*p*, *p* + *L*(5*q*)) |
| Quinary column | 4 ∤ *i* | *p* + *U*(*q*) | min(*L*(5*q*), *L*(*q*) + 3*p*) |

For instance the first window stays in the row shell starting at $Bp$.
Its offset ranges from at least $Qq$ to strictly below $5Qq$, so $J=2l+j$
is odd. The second stays in the column shell starting at $Qq$ with offset
in $[Bp,3Bp)$, so $I=4k+i$ certifies the column. Empty windows contribute
nothing.

A finite search covers the phase range with 660 brackets and supplies a list of exponent pairs for each.
The kernel checks the windows and the uncovered prefix length for each
list. Before a zero-cost window the count can grow by at most the length
of the gap, and inside the window it is constant. The check at the gap's
right edge and at the minimum cutoff $HB$ bounds every integer cutoff,
including one partway through a gap or window. A final check covers the
last gap through $81HB$. Adjacent brackets share their endpoint. Thus all
integer prefixes from $81^5$ onward satisfy the claimed finite bound.
The certificate uses proof by kernel reduction on each leaf.

Finally the Phase 13 transfer supplies $D_N(x)\le F(N)/N+o(1)$ uniformly
over the interval used in the discrepancy. Applying it to the finite
kernel bound gives $0.575524$, and applying it to the ordinary upper
density gives the sharper paper bound. Binary normality of $x$ remains
open. [Kernel window certificate and discrepancy proof](../../NormalityChecker/ProductThreeFiveOrdinary.lean) ·
[Uniform transfer to the binary shifts of the product](../../NormalityChecker/ProductThreeFiveCoverage.lean)
