# The two-prime product and tied leading monomials

Let $\alpha(b,c)=\sum_{j\ge1}c^{-j}b^{-c^j}$ and $x=\alpha(2,3)\alpha(2,5)$.
The upper extreme interval discrepancy of the binary shifts of $x$ is at most
**27/40**. Here discrepancy means the upper limit, over prefix lengths $N$, of
the largest absolute difference between the observed frequency of a half-open
subinterval of $[0,1)$ and its length. Paper I proved the bound $43/45$ by
choosing one of the two sides of an isolated insertion. The new bound uses
every interval on which the highest power of five survives. It includes every
cutoff inside the last interval. Binary normality of $x$ remains open.
[Independent statement](../../NormalityChecker/ProductThreeFiveStatements.lean) ·
[Kernel proof](../../NormalityChecker/ProductThreeFiveCoverage.lean) ·
[Paper I, “A product on two prime axes”](../../papers/01-stoneham-polynomials/paper.pdf)

## Exact residues of a prefix

At position $n\ge5$, set $K=\lfloor\log_3 n\rfloor$, $L=\lfloor\log_5 n\rfloor$,
$P=3^K$ and $Q=5^L$. Define $R_n$ by summing
$2^{n-3^i-5^j}/(3^i5^j)$ over all $i,j\ge1$ with $3^i+5^j\le n$.
Write $A_n=PQR_n$, an integer. Let $J$ count the positive powers of five at
most $n-P$ and let $I$ count the positive powers of three at most $n-Q$.
These counts are zero when their sets are empty. For $r=0,1,2,3$ respectively,
let $w(r)$ be $0,4,1,2$. Then

$$
 A_n\equiv 2^{n-P}5^L(J\bmod 2)\pmod 3,\qquad
 A_n\equiv 2^{n-Q}3^K w(I\bmod 4)\pmod 5.
$$

Modulo three, only the row $i=K$ remains. After the common unit is removed,
its summands $5^{-j}2^{-5^j}$ alternate between $1$ and $2$. Modulo five only
the column $j=L$ remains. Its summands $3^{-i}2^{-3^i}$ repeat the four
values $4,2,1,3$. Their partial sums give $w$. Thus $P$ divides the reduced
denominator exactly when $J$ is odd, and $Q$ divides it exactly when
$4\nmid I$. Each equivalence accounts for rational reduction and for
simultaneous insertions. [Kernel residue identities and denominator tests](../../NormalityChecker/ProductThreeFiveResidues.lean)

At precision $3^h$, retain exactly the active summands with $K-i<h$.
Their integer coefficients in $A_n$ are
$2^{n-3^i-5^j}3^{K-i}5^{L-j}$. Every omitted row is divisible by $3^h$.
At precision $5^h$ retain the columns with $L-j<h$. Thus the full local
residue at any depth is an explicit truncated sum even outside rectangles.
The opposite endpoint for each retained row is computed separately.

For example, at $n=105$ the active lengths are $J=1$ and $I=3$. The fractional
part of $R_{105}$ is $1702/2025$. At $n=106=81+25$, both lengths advance, to
$2$ and $4$. The new fractional part is $92/135$. Both full powers disappear
throughout $106\le n<125$, while a factor of each prime remains.

The periods two and four govern the lengths $J$ and $I$. As functions of $n$,
the lengths use different subtractions from the same cutoff. For instance,
both residues change at 106. Assigning independent uniform distributions to
their residue classes would require a separate theorem. The proof below
counts one of the two tests exactly.

## Counting all surviving columns

In the quinary shell $Q\le n<5Q$ write $y=n-Q$. The column fails at $y=0$
and on the disjoint integer intervals $[81^j,3\cdot81^j)$ for $j\ge0$.
Every interval $[3\cdot81^j,81^{j+1})$ inside the shell certifies $Q$.
Let $C(t)$ count failures with $0\le y<t$. For $B=81^j$, summing the
preceding bad intervals gives $C(B)=(B+39)/40$. Between $B$ and $3B$ the
count increases by one at every step, and between $3B$ and $81B$ it is
constant. Hence $40C(t)\le27t+39$ for every $t$, with equality at $t=3B$.
Summing the completed shells and the last partial shell gives the finite bound

$$
 40\sum_{n<N} c(n)\le27N+39\lfloor\log_5 N\rfloor+52,
$$

where $c(n)$ is one on failures and zero elsewhere, with the same integer-log
convention at the initial positions. [Kernel count including partial shells](../../NormalityChecker/ProductThreeFiveCount.lean)

To transfer the count to $x$, put $k=\lfloor\log_4 N\rfloor$ and partition
the prefix into blocks of length $B=2^k$. Discard the initial block, the last
partial block, and blocks containing a location $3^i+5^j$. Their total length
is $O(B(1+k)^2)=o(N)$. In any remaining block the rational prefixes follow
exact doubling. If one position certifies its full power of five, the starting
denominator is at least that power, since the later denominator divides the
earlier one. Such powers tend uniformly to infinity after the initial block.
Every starting denominator has prime support in $\{3,5\}$ and is at most
$N^2\le B^6$ for large $B$. The fixed-support short-orbit estimate and the
vanishing real tail give interval-count error $o(B)$ uniformly over these
blocks and test intervals. Every position in a remaining uncertified block
costs one and has $c(n)=1$. Dividing the resulting inequality by $N$ proves
the bound. Paper I attributes the fixed-support short-orbit estimate to
Vandehey. The Lean proof uses the repository's verified version.
[Shifted tail and smooth denominator](../../NormalityChecker/ProductThreeFivePrefix.lean) ·
[Short-orbit transfer](../../NormalityChecker/SupportDiscrepancy.lean) ·
[Discrepancy proof](../../NormalityChecker/ProductThreeFiveCoverage.lean) ·
[Vandehey, Corollary 1.2 of the preprint](https://arxiv.org/abs/1606.07911)

## The logarithmic distribution of the coupled endpoints

Under logarithmic weighting every one of the eight pairs $(I\bmod4,J\bmod2)$
has density $1/8$. In particular the harmonic weight of the positions where
both top powers fail, divided by $\log N$, tends to $1/8$. This is a paper
deduction about sampling time. The uniform bound $27/40$ above concerns
ordinary prefixes.

To prove the assertion, use continuous time $t=\log n$ and write
$\log_3 n=K+u$, $\log_5 n=L+v$, with $u,v\in[0,1)$. The pair
$(t/\log 3\bmod4,t/\log5\bmod2)$ is uniformly distributed on the rectangle
of side lengths four and two with opposite edges identified. Indeed, the
average of every nonconstant Fourier character over $0\le t\le T$ tends to
zero by direct integration, since $\log 3/\log 5$ is irrational. Away from
the beginnings of shells the active lengths are

$$
 I=K+\lfloor u+\log_3(1-5^{-v})\rfloor,\qquad
 J=L+\lfloor v+\log_5(1-3^{-u})\rfloor.
$$

For fixed fractional coordinates $(u,v)$, the eight sheets of the rectangle
have all eight possible pairs $(K\bmod4,L\bmod2)$. The displayed floor
terms translate these labels by amounts depending only on $(u,v)$, permuting
the eight pairs. The cell indicators are Riemann integrable. Their boundaries
lie on the axes and countably many continuous level curves, locally finite
away from the axes. Haar measure therefore gives $1/8$ to each cell.
In passing back to the integers, omit $[P,P+1)$ and $[Q,Q+1)$ at the start
of each shell. Their total logarithmic measure is finite. Elsewhere all
thresholds are integers, so the memberships are constant on each $[n,n+1)$.
Replacing $\log(1+1/n)$ by $1/n$ costs a bounded total error.

There is also an ordinary subsequence consequence. Let $F(N)$ count the
positions below $N$ where both powers fail. A clean block with either surviving power has a denominator growing uniformly
at late positions. Both powers use the same smooth denominator bound, so
only simultaneous failures need to be charged.
The kernel theorem gives $D_N(x)\le F(N)/N+o(1)$. Partial summation expresses the
logarithmic failure density as the logarithmic average of $F(N)/N$, up to a
vanishing error. Thus $\liminf D_N(x)\le1/8$. The upper limit still requires control of every ordinary cutoff. [Kernel bound in terms of simultaneous failures](../../NormalityChecker/ProductThreeFiveCoverage.lean)

## Persistent simultaneous cancellation

For every $h\ge1$ and every starting scale there are later $K,L$ with
$P<Q<5P/4$ such that, at **every** position $P+Q\le n<3P$,

$$
 \operatorname{den}(R_n)\mid 3^{K-h}5^{L-h}.
$$

The interval has length $2P-Q>3P/4$. Both axes therefore lose any prescribed
fixed number of denominator layers for a macroscopic time. To see why, define

$$
 U_a(J)=\sum_{j=1}^{J} a^{J-j}2^{a^J-a^j}.
$$

Throughout the stated interval all pairs with $i\le K$, $j\le L$ are active
and there are no others. Consequently $A_n=2^{n-P-Q}U_3(K)U_5(L)$.
For modulus $m=p^h$, take $T=\varphi(m)\varphi(\varphi(m))$.
For the two pairs $(p,a)=(3,5),(5,3)$, the base $a$ is a unit modulo both
$m$ and $\varphi(m)$, and two is a unit modulo $m$. Euler's congruence gives
$a^T\equiv1$ in both moduli. In the sum defining $U_a(J)$, the terms at
$j$ and $j+T$ agree modulo $m$ whenever both are present. The first factor
loses $a^T$, and the difference in the binary exponents is a multiple of
$\varphi(m)$. If $mT\mid J$ this gives a multiple of $m$ identical blocks,
so $m\mid U_a(J)$.

Choose $H$ divisible by both block requirements. The forward rotation for
$\log 3/\log 5$ supplies arbitrarily late powers $P<Q<5P/4$ with both
exponents divisible by $H$. Indeed, for any $A$, approximate a ratio in the
open interval $(3^A,3^A(5/4)^{1/H})$ by $5^j/3^i$, then set $K=H(i+A)$
and $L=Hj$. Irrationality of the log ratio follows from unique prime
factorization. This use of the rotation selects actual simultaneous phases.
[Logarithmic alignment](../../NormalityChecker/ProductThreeFiveFlow.lean) ·
[Kernel proof at arbitrary fixed depth](../../NormalityChecker/ProductThreeFiveRectangles.lean)

## Exact loss on full rectangles

The following arithmetic deduction gives the depth of cancellation. Its
lifting argument is supplied here as a paper proof. The kernel result above
already proves unbounded fixed-depth loss independently.

Take $(p,a,u)=(3,5,2)$ or $(5,3,4)$. For $J\ge1$ put
$S_J=\sum_{i=1}^J a^{-i}2^{-a^i}$, viewed in the rationals with denominator
coprime to $p$. The multiplier from $S_J$ to $U_a(J)$ is a $p$-adic unit.
Then

$$
 v_p(U_a(J)) =
 \begin{cases}
 0 & u\nmid J,\\
 1+v_p(J/u) & u\mid J.
 \end{cases}
$$

The nonmultiples follow from the two residue tables. For the multiples,
$S_2\equiv6\pmod9$ and $S_4\equiv15\pmod{25}$ in the respective cases.
We prove the lifting step for $s=up^t$. Write $x_i=a^{-i}2^{-a^i}$.
The integer $d=a^s-1$ is divisible by both $p-1$ and $p^{t+1}$. The latter
follows by starting from $p\mid a^u-1$ and raising to the $p$th power $t$
times. For $r\ge0$, expansion of $(1+d)^r$ gives
$a^{rs}-1\equiv rd\pmod{(p-1)p^{t+2}}$.
Set $D_i=2^{-a^i d}$. Euler's congruence gives
$D_i\equiv1\pmod{p^{t+2}}$ and
$2^{-a^i(a^{rs}-1)}\equiv D_i^r\pmod{p^{t+3}}$.
Since $a^{-rs}\equiv1\pmod p$, expansion yields

$$
 x_{i+rs}\equiv a^{-rs}x_i + r x_i(D_i-1)\pmod{p^{t+3}}.
$$

Sum over $1\le i\le s$ and $0\le r<p$. The second term vanishes modulo
$p^{t+3}$ because $p$ is odd and $p\mid\sum_{r<p}r$.
Moreover $\sum_{r<p}a^{-rs}\equiv p\pmod{p^2}$ by the same linear
expansion about one. If $v_p(S_s)=t+1$, this proves
$S_{ps}\equiv pS_s\pmod{p^{t+3}}$ and hence $v_p(S_{ps})=t+2$.
For $v$ coprime to $p$, summing $v$ blocks in the displayed congruence
modulo $p^{t+2}$ gives $S_{vs}\equiv vS_s\pmod{p^{t+2}}$. This completes
the induction for all lengths.

In a full rectangle $U_3(K)\equiv1\pmod3$ and $U_5(L)\equiv1\pmod5$ by
their final summands. Thus the exact reduced denominator exponents are
$\max(0,K-v_3(U_5(L)))$ and $\max(0,L-v_5(U_3(K)))$. In particular the
losses are at most logarithmic in the opposite exponents, even along the
macroscopic intervals above. Nonrectangular prefixes omit corners of the
product and require additional cancellation estimates.

## Tied highest-degree monomials

Fix an odd prime $p\nmid b$ and a distinguished monomial $M$ of positive
degree $d$ in the standard generators $\alpha(b^m,p^e)$, with $m,e\ge1$.
Fix a finite list $M_i$ of degree at most $d$. There exists $H$ such that
for every list of integers $a_i$ the number

$$
 M+p^H\sum_i a_i M_i
$$

is normal in base $b$. In particular the list can contain distinct monomials
of degree exactly $d$. For example, some $H$ works in base two for
$\alpha(2,3)^2+3^H a\alpha(4,3)^2$ simultaneously for all integers $a$.
[Independent statement](../../NormalityChecker/StonehamTiedStatements.lean) ·
[Kernel proof](../../NormalityChecker/StonehamTiedCoefficients.lean)

In the index-zero normalization, Paper I’s retained-denominator theorem gives
a loss $C$ for $M$ at every large cutoff in shell $k$, so its prefix denominator
is divisible by $p^{dk-C}$. The integral combination of the other prefixes
has denominator dividing $p^{dk}$. Multiplying it by $p^{C+1}$ leaves at most
$dk-C-1$ powers of $p$, so it cannot cancel the distinguished pole. The same
sparse-block proof gives normality. Passing to the index-one standard series
costs a fixed power depending on the strides in the given family. This explains
the order of quantifiers in the theorem. [Retained single-monomial pole](../../NormalityChecker/StonehamPolynomialPrefix.lean) ·
[Transfer for a surviving combination](../../NormalityChecker/StonehamPolynomialNormal.lean)

For unrestricted coefficients, two distinct degree-one generators can already
give a rational number. Reindexing the defining absolutely convergent series
gives $\alpha(b^c,c)=c\alpha(b,c)-b^{-c}$. For example
$\alpha(8,3)-3\alpha(2,3)=-1/8$. The kernel proves this identity for all
$b,c\ge2$. It also explains examples where equal quadratic terms cancel to
a normal linear term after substitution. [Radix-stride identity](../../NormalityChecker/StonehamTiedCoefficients.lean)

## Reproducible finite checks

Run `python3 scripts/check_independent_axes.py`. The script updates the
exact rational fractional prefix by doubling and adding all insertions at
each digit. It checks the scaled residues, both reduced-denominator tests and
the finite coverage bound at positions 0 through 100,000. It checks the
truncated formulas through depth four at insertions and their two neighbors. Among those
positions with both nominal prime exponents positive, 14,310 lose both full
powers. It also checks the rectangular valuation formula at all lengths
1 through 10,000 for each prime, using arithmetic modulo its ninth power.
[Exact test script](../../scripts/check_independent_axes.py)
