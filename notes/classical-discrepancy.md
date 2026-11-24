# Quantitative targets for classical constants

The target for $\ln 2$ is an unconditional upper bound $D_\infty<1$ in base two. Two sufficient estimates concern the aggregate size of logarithmic spikes and the first Fourier frequency on dyadic blocks. Both remain open for the full logarithm. The prime-survival theorem establishes a structural obstacle for one family of models. [Corrected-model arithmetic](log-shadow-primes.md) · [Binary transition theorem](transition-discrepancy.md)

## A fixed percentage has a finite interpretation

If every binary word of a fixed length $k$ has limiting frequency $2^{-k}$, the anchored empirical distribution converges to the correct value at every endpoint of the mesh $2^{-k}$. Monotonicity sandwiches an arbitrary endpoint between its two neighbors, costing at most one mesh width. Subtract the two anchored estimates to get $D_\infty\le2^{1-k}$. For $k=8$, the bound is $1/128$, or $0.78125\%$. A separate way to get partial information is to prove uniform distribution on a selected fraction $g$ of every sufficiently long prefix. Unselected observations contribute at most $1-g$ to the asymptotic discrepancy. A bound tending to zero over successively finer tests implies full normality. For $\ln 2$, even a positive lower density of transitions would already give $D_\infty<1$. [Fixed cells and uniform shares](../NormalityChecker/PartialUniformity.lean) · [Transition and normality equivalences](../NormalityChecker/BinaryDiscrepancy.lean)

## Logarithmic spikes and digit transitions

For any irrational $x$, put $v_n=-\log|\cos(\pi 2^n x)|$ and $\lambda=(\log 2)/2$. Irrationality excludes the zeros of sine and cosine on these shifts. Multiplying the double-angle identities gives

```math
\sum_{n<N}v_n=N\log2+\log|\sin(\pi x)|-\log|\sin(\pi2^N x)|.
```

The last term is nonnegative. A nontransition places $\{2^nx\}$ outside $[1/4,3/4)$ and gives $v_n\le\lambda$. If the prefix second moments have finite limsup at most $C>0$, the lower transition density $t(x)$ and binary discrepancy satisfy

```math
t(x)\ge\frac{(\log2)^2}{4C},\qquad D_\infty(x)\le\max\!\left(\frac23,1-\frac{(\log2)^2}{4C}\right).
```

Lean sums the pointwise quadratic inequality $v_n\le\lambda+a v_n^2+\mathbf1_{\rm transition}/(4a)$, then optimizes at $a=\log 2/(4C)$. Hypothetically, $C=100$ would give $t(x)\ge0.00120113\ldots$. A weaker first-moment criterion needs just one cutoff $M>\lambda$. If the upper limiting mean of $(v_n-M)_+$ is at most $L<\lambda$, then $t(x)\ge(\lambda-L)/(M-\lambda)>0$. This follows from the same identity and $v_n\le\lambda+(M-\lambda)\mathbf1_{\rm transition}+(v_n-M)_+$. [Conservation, moments and truncation](../NormalityChecker/TrigonometricMoments.lean)

The script computes a certified binary cylinder for $\log 2$ by rounding every term of $\sum 2^{-j}/j$ down with integer arithmetic and bounding the rounding and truncation errors. On a transition, let $r$ be the distance to the next transition. The distance of the current shift from $1/2$ is at least $2^{-r-2}$. Concavity of sine gives $|\cos(\pi2^nx)|\ge2\,\mathrm{dist}(\{2^nx\},1/2)$, hence $v_n\le(r+1)\log2$. The program reads beyond the end of a shell until it can certify the next transition for its last contributing run. The last column bounds the shell mean of $v_i^2$ in units of $(\log2)^2$. [Reproduction script](../scripts/discrepancy_experiments.py)

| Shell $[n,2n)$ | Transition fraction | Upper bound in units of $(\log2)^2$ |
| ---: | ---: | ---: |
| 256 | 141/256 | 1413/256 |
| 1,024 | 65/128 | 2995/512 |
| 4,096 | 525/1024 | 24251/4096 |
| 16,384 | 8209/16384 | 98509/16384 |

Rivoal obtains irrationality measures for restricted denominators and digit-count consequences for logarithms at certain rational arguments. Individual approximation bounds limit successive run lengths. For example, even a hypothetical bound $\|2^n\log2\|\ge n^{-C}$ gives a logarithmic maximum run length, compatible with only $O(N/\log N)$ transitions. A uniform bound on the aggregate contribution of long runs would give additional information. [Rivoal, *Convergents and irrationality measures of logarithms*](https://ems.press/journals/rmi/articles/4766)

## One Fourier frequency on dyadic blocks

For $n=2^k$, let $B_k=n^{-1}\sum_{i<n}\exp(2\pi i2^i C_n(n))$. If $1-\Re B_k\ge\varepsilon>0$ on every sufficiently late **complete** shell, then $D_\infty(\ln2)\le\max(2/3,1-\varepsilon/8)$. The Lipschitz bound on the cosine transfers the estimate to the true orbit. Its nonnegative deficit allows incomplete shells to be dropped, and the preceding shells still cover at least asymptotically half the prefix. The first-frequency transition theorem supplies the remaining factor four. A deficit of $0.008$ would prove $D_\infty\le0.999$. [Dyadic transfer](../NormalityChecker/DyadicEscape.lean)

For a numerator restricted to $0\le A<Q$, the number whose first $T\ge1$ binary digits make at most $K$ transitions is bounded by $(Q2^{-T}+1)2\sum_{j\le K}\binom{T-1}{j}$. Choose the first bit and the transition locations, then count the rational grid points in each half-open cylinder. The prime-survival results identify factors of the actual $Q$. Excluding the specific $A$ from these cylinders is an additional arithmetic problem. The earlier four-position discrepancy target and this one-frequency estimate both remain open. [Four-position target](transition-discrepancy.md#one-fixed-window-length-suffices) · [Growth on typical correction indices](log-shadow-primes.md)

The same denominators admit an explicit obstruction to any estimate uniform over reduced numerators. For numerator one, summing $1-\cos(2\pi u)\le2\pi u$ at $u=2^i/Q$ gives a mean deficit of at most $2\pi(2^n-1)/(nQ)$. At every start $n\ge1$ there is a $j\in\{n,n+1\}$ at whose actual denominator this deficit over $j$ positions is at most $4\pi/n$. This follows from $Q_{j,j}\ge2^n$. Thus a positive deficit on all long blocks for **every** reduced numerator at the actual moduli is impossible. The dyadic criterion concerns the specific corrected numerator. [Kernel-verified numerator obstruction](../NormalityChecker/NumeratorEscape.lean)

For the actual numerator the table uses integer doubling modulo the reduced $Q_{n,n}$. Each visit to $[1/4,3/4)$ contributes at least one unit of first-frequency deficit. This gives a rational lower bound without evaluating a trigonometric function. At these starts the visit counts also match the true-orbit transition counts obtained independently from the logarithm series above.

| Start $n$ | Bits in $Q_{n,n}$ | Lower bound on $1-\Re B_{\log_2 n}$ |
| ---: | ---: | ---: |
| 256 | 716 | 141/256 |
| 1,024 | 2,925 | 65/128 |
| 4,096 | 11,793 | 525/1,024 |
| 16,384 | 47,203 | 8,209/16,384 |

```sh
python3 scripts/discrepancy_experiments.py model 256 1024 4096 16384
```

## Hexadecimal shifts of π

For the Bailey–Borwein–Plouffe coefficient $r_k$, set $P(t)=4-2t^3-t^4-t^5$. Then $r_k=\int_0^1t^{8k}P(t)\,dt$. The integral of $16P(t)/(16-t^8)$ is $\pi$ on $[0,1]$, as can be seen from the antiderivative $2\log(2-t^2)-2\log((t-1)^2+1)+4\arctan(t-1)$. Lean verifies the identity for the actual real number $\pi$. Starting from the shifted BBP prefix, the rational corrections use finite differences of $r_k$ and successive powers of $15^{-1}$. The exact residual after order $r$ is

```math
16^n\pi-y_{r,n}=15^{-r}\int_0^1\frac{(t^8)^{n+1}(t^8-1)^rP(t)}{16-t^8}\,dt.
```

In particular $|16^{n+i}\pi-16^i y_{n,n}|\le4\cdot16^i/(15\cdot60^n)$, which tends uniformly to zero for $0\le i\le\alpha n$ at any fixed $\alpha<\log_{16}60$. For the **uncorrected** prefix through coefficient $n$, each prime $4n+3<p\le8n+1$ with $p\equiv1,5\pmod8$ survives. Exactly one summand has denominator divisible by $p$, with numerator a unit. This identifies a family of actual denominator factors. Statistical control of the numerator and a strict discrepancy bound for $\pi$ remain open. [Verified integral and corrections](../NormalityChecker/BBPShadow.lean) · [Prime survival](../NormalityChecker/BBPDenominator.lean) · [Original BBP paper](https://www.cecm.sfu.ca/~pborwein/PAPERS/P123.pdf)

## Quadratic irrationals and Fibonacci indices

Let $\varphi=(1+\sqrt5)/2$ and $\psi=-1/\varphi$. For the canonical Zeckendorf expansion of any positive integer $M$, write $k(M)$ for its smallest occupied Fibonacci index, starting with $F_2=1,F_3=2$. Summing $F_{j+1}-\varphi F_j=\psi^j$ gives the exact error made when replacing $\varphi M$ by the corresponding sum of successor Fibonacci numbers. Since index $k+1$ cannot be occupied, and the remaining geometric tail is bounded on both sides, the error after taking distance to the nearest integer satisfies

```math
\varphi^{-k(M)-1}\le\|M\varphi\|\le\varphi^{1-k(M)}.
```

The proof includes the possibility of rounding to the other adjacent integer at $k=2$. Taking $M=2^n$ gives an equivalence. $D_\infty(\varphi)<1$ in base two precisely when there is a finite $K$ such that $k(2^n)\le K$ on a set of positive lower density. In the reverse direction those indices place the shifts in a fixed interior interval. A bounded number of subsequent shifts must then include a digit transition. The existence of such a $K$ remains open. In each integer base the normality of $\varphi,\sqrt5,1/\sqrt5$ is equivalent by rational scaling and translation. This equivalence concerns normality and gives no numerical identity between their discrepancies. [Fibonacci bounds, discrepancy criterion and affine equivalences](../NormalityChecker/GoldenOrbit.lean)

Barnoff, Bright and Shallit compute a base-$b$ digit of $\varphi$ using a finite automaton on the Zeckendorf representation of $b^n$. The input distribution along powers of the base is a separate arithmetic question. Bailey, Borwein, Crandall and Pomerance prove a lower bound of order $N^{1/d}$ on the number of ones for irrational algebraic numbers of degree $d$. Complementation also gives a bound for zeros. Bugeaud and Evertse give bounds on digit changes through the Subspace Theorem. Kaneko obtains square-root growth for the number of binary digit changes for $1/\sqrt5$. These results provide comparisons for the quadratic track. Positive lower density is a stronger target. [Barnoff–Bright–Shallit](https://arxiv.org/abs/2405.02727) · [Bailey–Borwein–Crandall–Pomerance](https://www.numdam.org/articles/10.5802/jtnb.457/) · [Bugeaud–Evertse](https://arxiv.org/abs/0709.1560) · [Kaneko, pp. 148–149](https://pcwww.liv.ac.uk/~karpenk/JournalUDT/vol07/no2/07Kaneko35-11.pdf)

There is also a direct bit calculation on occupied Fibonacci indices. If $S$ represents $M>0$ and $k=\min S$, then $\lfloor M\varphi\rfloor=\sum_{j\in S}F_{j+1}-\mathbf1_{k\text{ even}}$. The conjugate error has absolute value below one and sign $(-1)^k$, as follows by writing it as $\psi^k u$ with $\varphi^{-1}\le u\le\varphi$. Since $F_{j+1}$ is odd exactly when $j\not\equiv2\pmod3$, one can read the Zeckendorf bits from least to most significant, track the index modulo six, toggle an output bit on each occupied index outside class 2 modulo 3, and toggle once more if the first occupied index is even. Applied to $M=2^{n+1}$ this returns fractional bit $n$, counted from zero. Lean checks the formula for every $n$. This is an alternative implementation of the published finite-state phenomenon. The frequency of the resulting bits on powers of two remains open. [Verified parity readout](../NormalityChecker/GoldenDigits.lean) · [Barnoff–Bright–Shallit, §3](https://arxiv.org/html/2405.02727v1)

The table counts starts $0\le n<N$. Integer square roots determine each binary prefix exactly. Greedy decomposition of the powers of two independently checks each bit of $\varphi$ via the parity formula and supplies the least-index counts. These finite counts place no lower bound on an infinite lower density.

| $N$ | $\varphi$ transitions | $\sqrt2$ transitions | $1/\sqrt5$ transitions | $k(2^n)\le4$ |
| ---: | ---: | ---: | ---: | ---: |
| 256 | 117 | 137 | 133 | 190 |
| 1,024 | 476 | 516 | 532 | 765 |
| 4,096 | 2,065 | 1,988 | 2,067 | 3,175 |

```sh
python3 scripts/discrepancy_experiments.py shell 256 1024 4096 16384
python3 scripts/discrepancy_experiments.py quadratic 256 1024 4096 --cutoff 4
```
