# Overlapping certificates for radix shifts

## An interval as a bound between endpoints

Write $S(v)=\sum_{n<v} f(n)$. For Fourier estimates take $f(n)=\exp(2\pi i h x_n)$ with fixed integer frequency $h$. For an interval $I\subset[0,1)$ take $f(n)=\mathbf1_I(x_n)-|I|$. Both observables have norm at most one. A certificate on $[u,v)$ supplies an edge of cost $c$ if $\|S(v)-S(u)\|\le c$. Either orientation has the same cost. For every walk from $a$ to $b$ the triangle inequality bounds $\|S(b)-S(a)\|$ by the sum of the edge costs. Thus the cheapest available path gives a bound, including paths that overshoot the target endpoint. For discrepancy the paths can depend on the test interval, provided the cost bound holds for every interval. [Kernel proofs](../NormalityChecker/IntervalCoverage.lean)

For a subinterval of length $t$ obtained by deleting lengths $l,r$ from a certified interval of cost $c$, the cost is at most $\min(t,c+l+r)$. This handles the last partial block. Disjoint certified pieces cost the sum of their individual bounds plus the number of uncovered positions. Clipping an interval has a real cost. For instance the consecutive constant runs $+1,-1,+1$, each of length $T$, have zero sums on both adjoining intervals of length $2T$ and sum $T$ on their union. Counting their lengths twice would give an incorrect bound. Conversely, zero-cost edges on $[0,8)$, $[2,8)$ and $[2,10)$ give a zero-cost path $0,8,2,10$ and certify the whole interval. The middle edge is traversed backwards. [Restriction and disjoint coverage](../NormalityChecker/IntervalCoverage.lean)

## Combining several denominator primes

Fix a finite prime support $P$, order $s\ge1$ and radix $b\ge2$. Choose any nonempty finite subset of primes of $P$ coprime to $b$, with a separate precision for each. Write $B_p$ for the digit positions whose normalized coordinate fails the test for $p$. Then

$$
D_\infty^{(b)}(X_{b,P,s})\le
\limsup_{N\to\infty}\frac{\#([0,N)\cap\bigcap_p B_p)}{N}.
$$

A passing test gives an arbitrarily large lower bound on the **same reduced prefix denominator**. Finiteness lets us take a common starting threshold even though each prime uses its own scale. The fixed-support orbit estimate on clean blocks and the original tail bound then apply. Lean states the conclusion for any upper bound on the eventual fractions, with arbitrarily small slack. This avoids any hypothesis about independence of the tests. [Joint soundness](../NormalityChecker/DiscrepancyChecker.lean) · [Clean-block proof](../NormalityChecker/SupportDiscrepancy.lean)

## Binary logarithmic support {2, 5, 13}

At precision one the two failure patterns are $[2\cdot5^j,4\cdot5^j)$ and $[10\cdot13^k,13^{k+1})$. Their individual upper densities are $5/8$ and $1/4$. **Lean proves a joint first-precision discrepancy bound of $234/1000$.** At precision two either prime proves normality by itself. The first-precision calculation measures what combining partial information achieves. [Cell evaluations and normality](../NormalityChecker/DiscrepancyChecker.lean) · [First-precision geometric proof](../NormalityChecker/JointFiveThirteen.lean)

Here is the finite accounting behind the Lean bound. It suffices to consider a prefix ending just after a joint failure at $n=N-1$; appending a passing position leaves the failed count constant. For $n\ge2197$ use $A=5^{\lfloor\log_5 n\rfloor-3}$ and $B=13^{\lfloor\log_{13}n\rfloor-2}$. Then $250A\le n<500A$ and $1690B\le n<2197B$. Every previous joint failure lies in one of the following intervals. An interval with reversed endpoints is empty.

| Part of the prefix | Cover |
| --- | --- |
| Early positions | $[0,B)$ |
| Third most recent 13-scale | $[\max(2A,10B),\min(4A,13B))$ |
| Preceding 13-scale | $[\max(10A,130B),\min(20A,169B))$ |
| Current 13-scale | $[\max(250A,1690B),N)$ |

The neighboring 5-scales miss each of the displayed 13-windows by the inequalities on $A,B,n$. Adding the four lengths gives at most $234N/1000$ by piecewise linear arithmetic. Induction over passing positions and a constant allowance for the initial positions give the stated limsup bound.

### Sharper joint upper density

**Paper deduction with exact rational computation.** Truncating at $\delta=10^{-10}$ encloses the upper density of the joint failures between

$$
\frac{24154414499397933}{103559564189453125}
\quad\text{and}\quad
\frac{4946824091597596553}{21208998746000000000}.
$$

The endpoints are $10^{-10}$ apart. Both round to $0.233241755$ at nine decimal places. Thus $0.2344161$ is a valid, conservative discrepancy bound. The sharp value here concerns the density lost by the first-precision test. The number itself has discrepancy zero. [Exact solver](../scripts/overlap_certificate.py) · [Regression tests](../scripts/test_overlap.py)

To see why the calculation covers all prefixes, extend the bands to all integer exponents on the positive real axis. The extension changes length before a large cutoff by at most one, and the positive-exponent bands have integer endpoints. Within a failed interval the accumulated fraction increases and within a gap it decreases. It therefore suffices to consider right endpoints of either family's bands. Normalize each such endpoint to 1. That fixes one pattern. The other has intervals $u[a,b)$ and their shrunk copies, for $1/q\le u\le1$ with $q$ its scale ratio. Discard $[0,\delta)$ at cost at most $\delta$. On the remaining finite interval the overlap length is affine between successive values where a moving boundary equals a fixed boundary (including clipped endpoints). Evaluate the endpoints of the phase range and all these rational ratios for each choice of fixed band end. The largest result bounds the truncated fraction from above. It is also approached along actual endpoints because $\log5/\log13$ is irrational and multiples of an irrational are dense modulo one. Taking both endpoint families covers every possible peak. The implementation also gives a conservative upper bound for any number of primes by covering each phase with rational intervals and enclosing all its moving bands before taking intersections.

The **logarithmic density** is $(\log 2/\log5)(\log(13/10)/\log13)\simeq0.04405317$. With the change of variable $x=e^t$, logarithmic averaging becomes ordinary averaging in $t$. The flow $(t/\log5,t/\log13)\bmod1$ is equidistributed on the two-torus by the continuous Weyl criterion, since every nonzero integer character has nonzero frequency. Rectangle boundaries have zero Haar measure. Replacing the integral by the harmonic sum over integer positions costs $O(1)$ across geometric band boundaries. **Ordinary density does not exist.** A positive ordinary density would persist along both $13^k$ and $10\cdot13^k$, whereas the count is constant between them. Density zero is excluded by the positive upper density above. The product calculation applies to logarithmic weighting only. For three or more selected primes the phase-box upper bound needs no joint equidistribution theorem.

**A limitation on combining two primes (paper deduction).** This log-density calculation works for *every* pair of distinct primes and every pair of finite-precision failed cell unions. The logarithmic failure mass of a union $Z_p$ in one scale is $a_p=(\log p)^{-1}\int_{Z_p}dt/t$. The joint upper ordinary density is at least $a_p a_q$, since a logarithmic density is bounded by the upper ordinary density by partial summation. Consequently, along nested refinements of two tests, the joint upper density can tend to zero only if at least one test's logarithmic mass tends to zero. On $[1,p]$ logarithmic mass and length bound one another up to fixed constants, so the single-prime shrinking-cell theorem already proves normality in that case. The converse follows by inclusion. Two primes can strictly improve a quantitative bound, but joint failure counts alone cannot prove normality at the limit of refinement while both individual tests retain positive limiting mass. The conclusion concerns this method of charging failures; arithmetic behavior inside those cells is a separate question.

```sh
python3 -B scripts/overlap_certificate.py 2 5 13 2 5 13
python3 -B scripts/overlap_certificate.py 2 5 13 2 3 5 13 --extra 3 1 --divisions 16
```

## Rigidity on shared samples

Fix $b,c>1$ coprime and an integer $d\ge0$. There exists $\delta>0$ depending only on these data. If $x,y$ are rational models at the **start of the overlap**, their reduced denominators divide powers of $c$ and are at most $T^d$, and $x-y$ is nonintegral, then for any $T>0$ and any observations $f_i$,

$$
\frac1T\sum_{i<T}\left(\|f_i-b^ix\|_{\mathbb R/\mathbb Z}+
\|f_i-b^iy\|_{\mathbb R/\mathbb Z}\right)\ge\delta.
$$

Indeed the denominator $Q$ of $x-y$ divides a power of $c$ and is at most $T^{2d}$. For $Q$ above the fixed-support threshold, the normalized sum of the first Fourier character has modulus at most $1/2$. Its Lipschitz bound forces mean circle distance from zero at least $1/(4\pi)$. For bounded $Q>1$, coprimality preserves $Q$ at every shift and the distance is at least $1/Q$. The circle triangle inequality gives the displayed conclusion. If the two mean errors vanish, the models eventually agree modulo one. Along a chain where this holds at successive overlaps, the reduced denominators are eventually constant. Such a chain cannot supply the growing denominators of the normality certificate. Short overlaps and a positive total share in disjoint blocks remain possible. [Uniform separation and chain theorem](../NormalityChecker/OrbitRigidity.lean) · [Internal fixed-support orbit estimate](../NormalityChecker/SmoothOrbit.lean)

Both restrictions matter. The models $0$ and $1/b$ agree after the first shift and have mean separation tending to zero. With smooth denominators coprime to the base but without the polynomial size restriction, $0$ and $1/c^{T^2}$ have vanishing separation throughout the common block. A bound polynomial in the *original* block length suffices only when it gives a polynomial bound in the actual overlap length.
