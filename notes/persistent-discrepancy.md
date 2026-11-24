# When failed modular cells determine discrepancy exactly

Let $P$ be a finite set of primes, $b\ge2$, and $s\ge1$. Write $X_{b,P,s}$ for the sum of $1/(m^s b^m)$ over positive integers with prime support contained in $P$, including $m=1$. The discrepancy $D_N$ takes the supremum over all half-open subintervals of $[0,1)$ of the absolute empirical frequency error among the first $N$ radix shifts. Write $D_\infty=\limsup_N D_N$. Its unit is a difference in frequencies. [Finite-support proof guide](finite-support-discrepancy.md)

## The exact formula

Suppose $s=1$ and precisely one prime $p\in P$ is coprime to $b$. At precision $L=k+1$, take every failing cell $u$ from the executable test, and put its half-open interval $[u/p^k,(u+1)/p^k)$ in $Z_L\subseteq[1,p)$. These regions decrease with $L$. Put $Z=\bigcap_{L\ge1}Z_L$ and write $|E|$ for Lebesgue measure. Lean proves

```math
D_\infty(X_{b,P,1})=\max_{1\le t\le p}
\frac{|Z|/(p-1)+|Z\cap[1,t)|}{t}.
```

In particular, $X_{b,P,1}$ is normal in base $b$ **if and only if $|Z|=0$**. Each finite computation gives a rational upper bound $C_L$. These bounds converge to the exact answer even when no finite test settles normality. Convergence by itself supplies no stopping rule for a prescribed absolute error. [Exact rational limit](../NormalityChecker/ExactProfile.lean) · [Lebesgue maximum and null-set equivalence](../NormalityChecker/PersistentRegion.lean)

**Upper bound.** On any fixed passing cell, the reduced denominator retains a growing power of $p$. Remove positions near an insertion, divide the remainder into blocks and use short-orbit cancellation there. Charge every uncontrolled position its full possible frequency error. At a prefix ending at normalized coordinate $t$, previous complete scales contribute $|Z_L|/(p-1)$, and the current scale contributes $|Z_L\cap[1,t)|$. Division by $t$ normalizes by the prefix length. Within a mesh cell the numerator is affine, so a maximum occurs at a mesh endpoint. This upper bound works for all positive orders and allows several off-base primes. [Soundness at finite precision](../NormalityChecker/DiscrepancyChecker.lean)

**Matching lower bound.** On the scale $p^k\le n<p^{k+1}$, use precision $k+1$ at the actual integer position $n$. A failed residue clears the entire off-base part of the shifted rational prefix. Away from recent insertions, multiplication by the radix has already cleared the other prime factors. The shifted prefix is then integral. The omitted tail is positive and at most $1/(n+1)$, so the actual shift belongs to $[0,\delta)$ for every fixed $\delta>0$ once $n$ is large enough. The number of positions lost to clearing on a prefix of length $N$ is $O((1+\log N)^{|P|+1})$. [Growing-precision residue](../NormalityChecker/LocalizedCertificate.lean) · [Deep cancellation and observed visits](../NormalityChecker/DeepCancellation.lean)

Every failed child has a failed parent. If $F_k$ is the count of actual deep failures before $p^k$, this gives $\#\mathrm{failed}(k)/(p-1)\le F_k+1$ by induction. Adding the truncated current scale supplies the lower estimate at **the endpoint maximizing the finite certificate**, with an error of one position plus the clearing cost. Count visits to $[0,\delta)$ there, take the large-scale limit and then let $\delta$ decrease. This proves $C_L\to D_\infty$. For the real-set formula, continuity of finite measure from above gives $|Z_L|\to|Z|$. The prefix numerators differ uniformly in $t$ by at most $p|Z_L\setminus Z|/(p-1)$. The score is continuous on $[1,p]$ since $t\mapsto |Z\cap[1,t)|$ is 1-Lipschitz. The maximizing endpoint accounts for possible variation across geometric scales. Tracking the endpoint also explains which empirical distributions can occur. [Prefix accounting](../NormalityChecker/ExactProfile.lean) · [Real-set proof](../NormalityChecker/PersistentRegion.lean)

## Empirical distributions at a prescribed endpoint (paper proof)

Under the same order-one, single-off-base-prime assumptions, put $\rho(t)=(|Z|/(p-1)+|Z\cap[1,t)|)/t$. For a sequence $N_k$ with $p^k\le N_k\le p^{k+1}$ and $N_k/p^k\to t$, the empirical measures of the first $N_k$ shifts have the following weak limit.

```math
(1-\rho(t))\,dx + \rho(t)\,\delta_0.
```

The exact discrepancy and null-set equivalence above have Lean proofs. The endpoint-dependent weak convergence in this section is a paper deduction. It also specifies the side from which the exceptional shifts approach zero.

1. **Count the positions.** At fixed precision $L$, the failed fraction through $N_k$ tends to $\rho_L(t)$, the same formula with $Z_L$ in place of $Z$. On each sufficiently late complete scale $j$ its failed count is $p^j|Z_L|$. The final scale uses the truncated length. On scale $j$, the *deep* failed positions use $Z_{j+1}$ at mesh width $p^{-j}$. Their count divided by $p^j$ equals $|Z_{j+1}|$ for the whole scale and $|Z_{j+1}\cap[1,N_k/p^k)|$ for the truncated scale $j=k$. These are exact mesh counts at integer cutoffs. The anchored errors are bounded uniformly by $|Z_{j+1}\setminus Z|\to0$. In the sum over earlier scales, the weights $p^{j-k}$ form a geometric series. Discard a fixed initial segment, bound all remaining errors by their supremum and let that initial segment grow. The deep fraction therefore tends to $\rho(t)$.
2. **Evaluate the passing positions.** Fix $L$ and any test interval $I\subseteq[0,1)$. Divide the prefix into blocks of length $B=2^{\lfloor\log_4 N_k\rfloor}$. Discard the incomplete block, the early or recent-insertion blocks from the short-orbit proof, and blocks crossing fixed-precision cell boundaries. There are $O_L(1+\log N_k)$ such boundaries, so their total cost is $o(N_k)$. Every remaining passing block has the fixed prime support, polynomial upper denominator bound and growing lower denominator required by the uniform interval estimate. Its count differs from $B|I|$ by at most $\eta B$ for every sufficiently late clean block, for any fixed $\eta>0$. Thus the passing positions contribute $(1-\rho_L(t))|I|$ in the limit. [Clean-block estimates](../NormalityChecker/SupportDiscrepancy.lean)
3. **Evaluate the exceptional positions.** Except for $o(N_k)$ recent or early insertions, every deeply failed shift approaches zero from the right. Its contribution to a fixed half-open interval $I=[a,c)$ with $0\le a<c\le1$ tends in aggregate, after normalization by $N_k$, to $\rho(t)\mathbf1_{a=0}$. The fixed-precision failures left over after removing these deep failures have limiting proportion $\rho_L(t)-\rho(t)$ by nesting. Let $L\to\infty$ to remove them. This proves convergence of the frequencies of all such intervals and hence weak convergence by approximation of continuous functions by step functions. [Integral prefixes on deep cells](../NormalityChecker/DeepCancellation.lean)

The first normalized cell $[1,2)$ always passes. Consequently $\rho(2)=\rho(1)/2$. If $|Z|>0$, the prefixes ending at $p^k$ and $2p^k$ have different limiting atom sizes. If $|Z|=0$, every endpoint has the uniform limit. This distinguishes an exact limsup discrepancy from convergence to a single biased distribution. Determining whether a given support has positive persistent measure can still require an infinite-precision argument.

## Reproducing the precision table

Each row gives the exact rational upper bounds for $L=1,2,3,4$, at order one. The row with two off-base primes shows the bounds from one selected prime. Intersecting the failure sets of every off-base prime gives the exact order-one limit. [Joint formula and higher-order obstruction](joint-persistent.md) A zero certificate proves normality in all four examples. [Tests against exact rational arithmetic](../scripts/test_localized_certificate.py)

| Base | Support | Selected prime | $C_1$ | $C_2$ | $C_3$ | $C_4$ |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 2 | 2, 5 | 5 | 5/8 | 0 | 0 | 0 |
| 10 | 2, 5, 7 | 7 | 7/12 | 7/30 | 0 | 0 |
| 2 | 2, 5, 7 | 5 | 5/8 | 1/4 | 0 | 0 |
| 210 | 2, 3, 5, 7, 11 | 11 | 13/40 | 17/420 | 11/1890 | 0 |

```sh
python3 scripts/localized_certificate.py 210 11 3 2 3 5 7 11
```

## A finite classification for signed periodic weights

For a rational sequence $A$ of any positive period $d$, a prime $p\nmid b$, and denominator order one, consider the dense expansion

```math
Y=\sum_{n\ge1}\frac{A(n)}{p^{\lfloor\log_p n\rfloor}b^n}.
```

Compute the periodic solution $H(n)=\sum_{i=0}^{d-1} A(n+i)b^{-i}/(1-b^{-d})$ of $H(n)-H(n+1)/b=A(n)$. The sequence $p^j\bmod d$ has a finite preperiod followed by a cycle. Write $\alpha_k$ for the values of $H$ around that cycle, of length $L$. Then $Y$ is normal in base $b$ precisely when $W_k\ne0$ at every phase, where

```math
W_k=\sum_{i=0}^{L-1}p^i\alpha_{(k-i)\bmod L},\qquad 0\le k<L.
```

Telescoping between successive powers of $p$ reduces $Y$ to the sparse boundary series up to rational translation and nonzero rational scaling. The cyclic sums obey $W_k-pW_{k-1}=(1-p^L)\alpha_k$. Clearing their denominators produces bounded signed integers $c_j$. More generally, for any bounded integer sequence $c_j$, put $a_0=c_0$ and $a_j=c_j-pc_{j-1}$ for $j\ge1$. At the boundary $p^k$, the shifted prefix of $\sum_j a_j/(p^j b^{p^j})$ equals an integer plus $c_k/p^k$ by Euler's congruence. Nonzero bounded $c_k$ give growing reduced denominators. Infinitely many zero $c_k$ yield long intervals concentrating near integers, which contradict normality. This proves the classification and permits aperiodic signed coefficients in the boundary theorem. Rational changes of scale preserve the normality conclusion. Numerical discrepancies require their own analysis after scaling. [Signed boundary theorem](../NormalityChecker/SignedPhases.lean) · [Arbitrary periods](../NormalityChecker/PeriodicClassification.lean)

For $b=2,p=3$ and $A(0),\ldots,A(3)=(-1/2,1,3/2,-3)$, the residues $3^j\bmod4$ alternate between 1 and 3. The cyclic tests give $-8$ and 0. Lean proves binary nonnormality of the original dense expansion. The executable test also handles a period divisible by $p$, for which the initial residues can lie outside the eventual cycle.

```sh
python3 scripts/discrepancy_experiments.py periodic 2 3 -- -1/2 1 3/2 -3
```
