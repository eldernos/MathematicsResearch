# Denominator losses in the mixed Stoneham product

Let $x=\alpha(2,3)\alpha(2,5)$, where $\alpha(2,q)=\sum_{j\ge1}q^{-j}2^{-q^j}$. At digit position $n\ge5$, write $K=\lfloor\log_3 n\rfloor$, $L=\lfloor\log_5 n\rfloor$, $P=3^K$ and $Q=5^L$. The rational prefix after shifting $n$ binary places is

$$
 R_n=\sum_{3^i+5^j\le n,\ i,j\ge1}\frac{2^{n-3^i-5^j}}{3^i5^j}.
$$

Write $A_n=PQR_n$. Losing at least $h$ of the $K$ ternary layers means $3^h\mid A_n$ with $K\ge h$. Use the same convention at five.

**Theorem.** For any fixed $h,k\ge1$, the logarithmic density of positions losing at least $h$ ternary and $k$ quinary layers is

$$
 d_{h,k}=\frac{1}{8\,3^{h-1}5^{k-1}}.
$$

The same probability holds conditionally on any fixed pair of endpoint deficits of positive logarithmic density. The ordinary upper density of joint failures, even restricted to prefixes missing exactly one corner, is at least $4/11$ for **every** $h,k$. The binary interval discrepancy of $x$ tends to zero in logarithmic mean over ordinary cutoffs. In particular its ordinary lower limit is zero. Binary normality and pointwise sublinear loss on all nonrectangular prefixes remain open here.

The full-precision reduction and the first lift on every nonrectangular shape have Lean proofs. The general lift, Haar measure, logarithmic density and ordinary-cutoff deductions below are paper proofs. [Lean module](../../NormalityChecker/ProductThreeFiveInterpolation.lean) · [Exact tests](../../scripts/test_mixed_interpolation.py) · [Previous results for rectangles and first precision](../phase13/independent-axes.md)

## Full-precision reduction to two endpoint deficits

Take $(p,q)=(3,5)$ or $(5,3)$, and put $H=\lfloor\log_p n\rfloor$, $m=\lfloor\log_q n\rfloor$. Let $I_j$ count the positive powers of $p$ at most $n-q^j$, and $J$ the positive powers of $q$ at most $n-p^H$. Empty endpoints have count zero. Set $a=m-J$ and $b=H-I_m$. A full rectangle has $a=b=0$. Otherwise $a,b\ge1$. Every pair strictly below both top indices is present since $P/3+Q/5\le8n/15$. Hence in a nonrectangle $H-I_j$ is zero for $j\le m-a$, one for $m-a<j<m$, and $b$ for $j=m$. This includes $a=m$ or $b=H$.

Let $x_j=q^{-j}2^{-q^j}$ in $\mathbb Z_p$ and $S_m=\sum_{j=1}^m x_j$, with $S_0=0$. Define

$$
 G_{0,0}(m)=S_m,\qquad
 G_{a,b}(m)=S_{m-a}+p(S_{m-1}-S_{m-a})+p^b x_m
 \quad(a,b\ge1).
$$

At every $n$ the number of lost $p$-layers is exactly $\min(H,v_p(G_{a,b}(m)))$. Indeed,

$$
 (p-1)2^{p^H}A_n+2^n q^m G_{a,b}(m)\equiv0\pmod {p^H}.
$$

In the $i$-th own-axis layer, Euler's theorem gives $2^{p^H-p^i}\equiv1\pmod{p^i}$ because $p^{i-1}(p-1)$ divides $p^i(p^{H-i}-1)$. The weight $p^{H-i}$ brings the precision to $p^H$. Sum each remaining fibre using $(p-1)\sum_{i=1}^{I_j}p^{H-i}=p^H-p^{H-I_j}$. The surviving sum is $\sum_j p^{H-I_j}x_j$. Both outside multipliers are units. The Lean theorems **ternary_endpoint_num** and **quinary_endpoint_num** prove this congruence with the opposite-axis sum cleared of denominators. **endpoint_num_shape** proves the three fibre weights from the original cutoff. [Kernel proof](../../NormalityChecker/ProductThreeFiveInterpolation.lean)

## One zero class at every precision

Take $(p,q,u)=(3,5,2)$ or $(5,3,4)$. The summands modulo $p$ repeat $(1,2)$ or $(4,2,1,3)$ respectively. Hence $S_J\equiv0\pmod p$ precisely for $u\mid J$. The first block $S_u$ is $6\bmod9$ or $15\bmod25$. In particular $v_p(S_u)=1$. [First-precision Lean proof](../../NormalityChecker/ProductThreeFiveResidues.lean)

For $t\ge0$, put $s=up^t$ and $d=q^s-1$. Then $(p-1)p^{t+1}\mid d$ because $q^u\equiv1$ modulo both $p-1$ and $p$, and taking a $p$th power gains a $p$-layer. For $r\ge0$, binomial expansion gives $(1+d)^r-1\equiv rd\pmod{(p-1)p^{t+2}}$. Put $D_i=2^{-q^id}$. Euler's theorem gives $D_i\equiv1\pmod{p^{t+2}}$ and

$$
 x_{i+rs}\equiv q^{-rs}x_i + r x_i(D_i-1)\pmod{p^{t+3}}.
$$

Indeed the binary factor agrees with $D_i^r$ modulo $p^{t+3}$, and $q^{-rs}\equiv1\pmod p$. Sum over $1\le i\le s$ and $0\le r<p$. The linear correction vanishes since $p\mid\sum r$. Also $\sum_r q^{-rs}\equiv p\pmod{p^2}$ by expansion about one. Starting with $v_p(S_u)=1$, induction gives $S_{ps}\equiv pS_s\pmod{p^{t+3}}$ and $S_s\equiv p^tS_u\pmod{p^{t+2}}$.

For **any** starting index $J\ge0$, telescope the difference between the shifted and initial blocks. The single-shift congruence gives

$$
 S_{J+s}-S_J-S_s
 =\sum_{i=1}^{J}(x_{i+s}-x_i)
 \equiv(q^{-s}-1)S_J\pmod{p^{t+2}}.
$$

Every increment $S_{J+s}-S_J$ is divisible by $p^{t+1}$. When $u\mid J$, it equals $p^tS_u\bmod p^{t+2}$. Also $x_{m+s}-x_m\equiv0\pmod{p^{t+1}}$. The terms multiplied by $p$ and $p^b$ in $G$ therefore contribute zero to its increment modulo $p^{t+2}$. On the sheet $m\equiv a\pmod u$ this gives

$$
 G_{a,b}(m+up^t)-G_{a,b}(m)\equiv p^t S_u\pmod{p^{t+2}}.
$$

On the other sheets $G$ is a unit. For a rectangle use the same shifted-block identity with $a=b=0$. At precision two the Lean theorems **ternary_corner_lift_two** and **quinary_corner_lift_two** verify the affine formula for every pair of positive deficits and every nonnegative shell-index argument. [Kernel proof](../../NormalityChecker/ProductThreeFiveInterpolation.lean)

Write $m=a+uz$ on the failure sheet. The last congruence shows that exactly one of the $p$ lifts of a failing $z\bmod p^t$ fails at the next precision. Changing $z$ by a unit multiple of $p^t$ changes $G/p$ by an element of valuation exactly $t$. The map $z\mapsto G_{a,b}(a+uz)/p$ extends to a bijective isometry of $\mathbb Z_p$: it induces an injection, hence a bijection, on every finite quotient. There is a unique zero $\zeta_{p,a,b}$ and

$$
 v_p(G_{a,b}(a+uz))=1+v_p(z-\zeta_{p,a,b}).
$$

For rectangles the zero is $0$. For positive deficits the lift gives compatible, exactly computable residues. At depth $h$ exactly one class of $m$ modulo $up^{h-1}$ fails.

## Analytic interpolation and zero-set measure

The shell-index variable $z\in\mathbb Z_p$ is separate from the two **real** fractional logarithms that determine the shape. The isometry proves that the zero set has Haar measure zero and that $v_p(G)\ge h$ has measure $p^{1-h}$ on its failure sheet. The following series also establishes analyticity.

For $1\le i\le u$, put $A=q^u$, let $\omega$ be the Teichmüller part of $2$ and write $U=2/\omega$. On nonnegative integers $z$ the summand $x_{i+uz}$ equals

$$
 q^{-i}\exp(-z\log A)\,\omega^{-q^i}
 \exp\!\bigl(-q^i\exp(z\log A)\log U\bigr).
$$

The torsion exponent is constant because $A\equiv1\pmod{p-1}$. Both logarithms belong to $p\mathbb Z_p$. The exponential convergence radius $p^{-1/(p-1)}$ exceeds $p^{-1}$, so the displayed series converge on a common closed disc $|z|_p\le R$ with $R>1$ sufficiently close to one.

Summing over $i$ gives the analytic block increment $g(z)=S_{u(z+1)}-S_{uz}$. Its discrete primitive with value zero at zero is the Newton series $\sum_{k\ge0}\Delta^k g(0)\binom{z}{k+1}$, where $\Delta g(z)=g(z+1)-g(z)$. Indeed, if $g(z)=\sum b_jz^j$ with $|b_j|_p R^j\le C$, then $|\Delta^k g(0)/k!|_p\le C R^{-k}$ by the integer Stirling-number formula for differences of monomials. At radius $1<r<R$ the $k$th term has Gauss norm at most $C R^{-k}r^{k+1}|1/(k+1)|_p$, which tends to zero. The primitive is analytic and at ordinary integers agrees with $S_{uz}$ by the finite Newton formula and telescoping. Adding the finitely many extra summands interpolates $S_{uz+i}$ on each sheet. Fixed integral shifts preserve the disc, so this also interpolates $G$ for every fixed shape.

## Logarithmic sampling and the actual binary orbit

Let $t=\log n$, and put $v=\{t/\log3\}$, $w=\{t/\log5\}$. The deficit on the top ternary row is $-\lfloor w+\log_5(1-3^{-v})\rfloor$, and the other deficit is $-\lfloor v+\log_3(1-5^{-w})\rfloor$. Endpoints below one need clipping to zero. Discarding intervals of absolute width one following each power handles these exceptions at bounded total logarithmic cost.

Use the real torus with coordinates $t/\log3$ modulo $4\cdot5^{k-1}$ and $t/\log5$ modulo $2\cdot3^{h-1}$. Integration of characters and the irrationality of $\log3/\log5$ give equidistribution of the continuous linear flow. At fixed fractional coordinates $(v,w)$ all sheets have equal weight. The ternary test selects one residue of **$L$** and the quinary test selects one residue of **$K$**, with the deficits reversed for the other prime. Counting sheets gives $d_{h,k}$ even after conditioning on a fixed shape. Outside the axes the floor boundaries form locally finite unions of level curves of area zero. The discrete memberships agree on $[n,n+1)$, since every change is at a power or a sum of powers. Replacing $\log(1+1/n)$ by $1/n$ costs bounded total error. The marginal densities obtained in the same way are $1/(2\cdot3^{h-1})$ and $1/(4\cdot5^{k-1})$.

Write $F_{h,k}(N)$ for the joint failures below $N$ and $D_N(x)$ for binary extreme interval discrepancy. For fixed depths and $\epsilon>0$, every sufficiently large **ordinary** cutoff satisfies

$$
 D_N(x)\le\epsilon+F_{h,k}(N)/N.
$$

Apply the clean-block proof for first precision with $B=2^{\lfloor\log_4 N\rfloor}$. The initial, unfinished and insertion-containing blocks cost $o(N)$. On a clean block the odd denominator is constant under doubling. If one position passes either test, its denominator is at least $3^{K-h+1}$ or $5^{L-k+1}$, which tends uniformly to infinity past the initial block. The fixed-support short-orbit estimate applies since the denominator is 15-smooth and at most $N^2$. Charge every other clean position to $F_{h,k}$. [Shifted tail](../../NormalityChecker/ProductThreeFivePrefix.lean) · [Short-orbit bound](../../NormalityChecker/SupportDiscrepancy.lean) · [First-precision block accounting](../../NormalityChecker/ProductThreeFiveCoverage.lean)

Partial summation gives $\sum_{N\le X}F_{h,k}(N)/N^2=d_{h,k}\log X+o(\log X)$. Let the fixed depths increase **after** taking the upper limit in $X$. Then $\sum_{N\le X}D_N(x)/N=o(\log X)$. Thus $\liminf D_N(x)=0$, and for every $\epsilon>0$ the cutoffs with $D_N(x)>\epsilon$ have logarithmic density zero. The marginal laws likewise show that a loss threshold tending to infinity is exceeded at either prime on a set of logarithmic density zero. In particular the losses are sublinear in the respective exponents in logarithmic density.

## Ordinary cutoffs and the remaining obstruction

Take $P,Q$ at a ratio arbitrarily close to $Q/P=5/6$. Precisely the top corner is absent on

$$
 \max(P+Q/5,P/3+Q)\le n<P+Q.
$$

For large such shells the interval ends before $3P$ and $5Q$. Its length divided by $P+Q$ approaches $4/11$. Impose the failing class for $L$ modulo $2\cdot3^{h-1}$ and the failing class for $K$ modulo $4\cdot5^{k-1}$. Arbitrarily late $P,Q$ still attain ratios in any open neighborhood of $5/6$. Indeed, after writing $K=K_0+Ai$ and $L=L_0+Bj$, the forward rotation by $A\log3/(B\log5)$ modulo one is dense, and the required $j$ tends to infinity. At $N=P+Q$ the whole interval counts. For example $P=243$, $Q=125$ gives joint first-layer loss on $268\le n<368$. This proves the uniform-in-depth $4/11$ ordinary lower bound. The fixed-depth failure sets consequently have no natural density. One can prescribe the losses **exactly** by choosing a passing child of each failing class at the next precision. For a deeper worked example, take $(K,L)=(49,33)$. At depths two, three and four, the one-corner ternary classes for $L$ are $3,9,27$ modulo $6,18,54$. The corresponding quinary classes for $K$ are $9,49,349$ modulo $20,100,500$. Hence exactly two ternary layers and three quinary layers are lost throughout the displayed interval, giving reduced denominator $3^{47}5^{30}$. The full rectangle at these exponents retains both top powers. The exact tests also compute the large one-corner denominator directly.

There is a sparse-exception estimate for every fixed shape. In any integer index band $T\le m\le2T$ with $T\ge1$, choose the least positive $h$ with $up^{h-1}>T$. At most one integer $m$ belongs to the failing progression. At all other indices the loss is at most $h-1=O(\log(2T))$, simultaneously at every position of that shape with that index. For finitely many shapes discard one index per shape and prime. Restricting both top powers to at most $(1-\eta)n$ bounds both deficits in terms of $\eta>0$, so the estimate is uniform on that part of the shells. One exceptional shell can still occupy a positive proportion of an ordinary prefix.

More precisely, along **any** sequence of ordinary cutoffs $N\to\infty$, the convergence $D_N(x)\to0$ is equivalent to

$$
 \frac1N\#\{n<N:\operatorname{den}(R_n)\le M\}\longrightarrow0
 \qquad\text{for every fixed }M.
$$

For sufficiency apply the same clean-block estimate, taking $M$ large enough for its target error. For necessity, fractional parts of rationals with denominator at most $M$ form a finite set. The vanishing shifted tail puts the counted shifts, apart from finitely many, in an arbitrarily small neighborhood of this set on the circle. Discrepancy bounds the mass of this finite union of intervals by its length plus a fixed multiple of $D_N(x)$. Shrinking the neighborhood proves necessity. Since the denominator divides $3^K5^L$, bounded denominators require simultaneous losses of $K-O_M(1)$ and $L-O_M(1)$.

The lift gives no Archimedean height bound for the two nonrectangular zeros. For example the analytic isometry $f(z)=z-\sum_{j\ge1}p^{b_j}$ with $b_1=1$ and $b_{j+1}=p^{2b_j}$ has a zero extremely close to ordinary integers. Its truncated sums $z_j$ satisfy $v_p(f(z_j))=b_{j+1}\gg z_j$. This example tests the inference from analyticity. For the specific mixed product, controlling simultaneous approximation of its two zeros by actual shell pairs at growing precision, or establishing the bounded-denominator criterion directly, remains the ordinary-cutoff problem.

## Reproduction

~~~sh
lake build NormalityChecker.ProductThreeFiveInterpolation
python3 -B scripts/test_mixed_interpolation.py
~~~

The exact tests compare both full-precision congruences with a rational doubling-and-insertion recurrence through position 2,400. A separate direct sum checks all power and insertion boundaries and their neighbors through $3^{24}$. For each prime the tests exhaust two complete index periods at depths one through five, on the rectangle and on all 36 shapes with deficits from one through six. They check the one-corner example, period, root count and next digit of the increment. [Lean proofs](../../NormalityChecker/ProductThreeFiveInterpolation.lean) · [Exact finite checks](../../scripts/test_mixed_interpolation.py)
