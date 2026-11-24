# Designing rational models for classical constants

## A polynomial moment identity

Suppose $b^n x-R_n=\int_0^1g(t)^n w(t)\,dt$ with rational $R_n$ and integrable moments. For a rational polynomial $F(X)=\sum_j f_j X^j$ with $F(b)=1$, put $Y_F(n)=\sum_j f_j R_{n+j}$. Then

$$
b^n x-Y_F(n)=\int_0^1 g(t)^n F(g(t))w(t)\,dt.
$$

Expand the finite polynomial and use $\sum_j f_j b^{n+j}=b^n$. Lean proves the identity for the abstract moments and for the actual constants $\log 2$ and $\pi$. For the logarithm, $b=2$, $g(t)=t$, $w(t)=1/(2-t)$, and $R_{n+1}=2R_n+1/(n+1)$ with $R_0=0$. At $n=0$, $Y_F(0)$ is exactly the integral of $(1-F(t))/(2-t)$. For hexadecimal shifts of $\pi$, take $g(t)=t^8$, $w(t)=t^8(4-2t^3-t^4-t^5)/(16-t^8)$ and use the BBP prefix through index $n$. The weights and integration limits follow from the established BBP identity. [Polynomial model theorems](../NormalityChecker/LogPolynomialKernel.lean) · [BBP identity](../NormalityChecker/BBPShadow.lean) · [Bailey, Borwein and Plouffe](https://www.cecm.sfu.ca/~pborwein/PAPERS/P123.pdf)

For the logarithm, replacing $F(t)$ by $F(t)+h(t-2)$ changes the rational model by exactly $h/(n+1)$. With rational $h$ every rational target is attainable even from the constant polynomial. This is an intrinsic limitation of unrestricted coefficient optimization. An independent enclosure of the error and control of the resulting rational orbit supply the arithmetic information. Normalized affine combinations of several kernels obey the same moment identity. Their approximation errors are signed, so separate absolute error bounds must be charged with the absolute weights. [Normalization and exact adjustment](../NormalityChecker/LogPolynomialKernel.lean)

## Chebyshev kernels and exact constraints

Use the shifted degree-two Chebyshev polynomial $8t^2-8t+1=T_2(2t-1)$. Its absolute value is at most one on $[0,1]$ and its value at two is 17. For $K_d=((8t^2-8t+1)/17)^d$, Lean proves the rational enclosure

$$
|2^n\log2-Y_{K_d}(n)|\le\frac{17^{-d}}{n+1}.
$$

This uses $2-t\ge1$ and $\int_0^1 t^n\,dt=1/(n+1)$. The Chebyshev polynomial is classical. The enclosure here is used to select admissible numerators and verify individual blocks. The general BBP identity permits the same polynomial in $t^8$, normalized by its value $1921$ at sixteen. [Verified enclosure](../NormalityChecker/LogPolynomialKernel.lean) · [Classical Chebyshev identity, DLMF §18.5](https://dlmf.nist.gov/18.5)

For an **integer coefficient constraint**, consider $F_h(t)=K_d(t)(1+h(t-2))$. Its model is $y+hJ$, where $y=Y_{K_d}(n)$ and $J=\int_0^1 t^nK_d(t)\,dt$ is rational. Express $y=A/D$ and $J=B/D$ over their least common denominator. To remove a prescribed factor $m\mid D$ from the common denominator, solve $Bh\equiv-A\pmod m$. To remove a prime entirely include its full power in $D$. Coprime prime-power requirements combine by the Chinese remainder theorem. Solutions exist exactly when $\gcd(B,m)\mid A$ and then form one class modulo $m/\gcd(B,m)$. Among them the minimizer of the maximum possible unwrapped error for an enclosure $[l,u]$ is obtained by rounding to the nearest admissible $h$ to $((l+u)/2-y)/J$, provided $J\ne0$. This optimizes the stated worst-case loss exactly. [Rational optimizer and experiment](../scripts/kernel_coverage.py) · [Reproduction tests](../scripts/test_overlap.py)

At $n=12,d=4$, imposing $m=35$ selects $h=-9$. The original reduced denominator is $4860766850940$ and the adjusted denominator is $138879052884$, coprime to 35. The error bound is $39002/12274663765$, small enough to give unwrapped error below $1/32$ at every additional shift $0\le i\le13$. Other primes still divide the denominator. This is an exact finite calculation.

## How many additional positions are certified?

The search uses a separate constrained family to evaluate finite uniform coverage. For each start $0\le n\le1012$ the fourth-power kernel supplies a rational interval $[l,u]$ for $2^n\log2$. Enumerate all reduced $a/q$ in the admissible range, with $1<q\le12^2$ supported on the primes indicated below. Each is realized by the linear adjustment above. Its maximum error over all 12 shifts is bounded by $e=2^{11}\max(|l-a/q|,|u-a/q|)$. Require $e\le1/32$. Compute the extreme interval discrepancy $d$ of its twelve modular iterates exactly, and accept if $d+2e\le1/3$.

To check the last step, thicken any test arc by $e$ on either side. Its length increases by at most $2e$; the complementary arc gives the other inequality. A wrapping arc has the same absolute error as its complement. Boundary ties can be handled by taking a decreasing sequence of slightly larger radii. For sorted model points $z_0\le\cdots\le z_{T-1}$, the extreme discrepancy is $\max_i((i+1)/T-z_i)+\max_i(z_i-i/T)$. The numerator enumeration and these finite inequalities use rational arithmetic. [Experiment](../scripts/kernel_coverage.py)

| Allowed denominator primes | Qualifying starts | Positions in their union | New positions beyond earlier rows | Positions in a largest disjoint packing of all rows so far |
| --- | ---: | ---: | ---: | ---: |
| 3 | 7 | 18 | 18 | 12 |
| 5 | 0 | 0 | 0 | 12 |
| 13 | 2 | 13 | 13 | 24 |
| 3, 5, 13 | 11 | 55 | 24 | 48 |

Thus 48 distinct observations can be charged to four disjoint blocks. The seven additional positions in the union require a restriction bound before they can be charged separately. Using unit edges for uncovered samples and the actual certified costs for all passing blocks, the shortest endpoint path gives $D_{1024}^{(2)}(\log2)\le0.964294$ (rounded up). The table concerns one finite prefix, fixed block length and fixed discrepancy budget. Proving a positive lower share in every sufficiently long prefix with vanishing distribution error, or a persistent escape estimate for a fixed frequency of the logarithm, remains open. [General overlap bounds](overlapping-certificates.md) · [Existing logarithm targets](classical-discrepancy.md)

## A modular obstruction for the golden ratio

Write $k(M)$ for the least occupied Zeckendorf index of $M>0$. Lean proves that for any modulus $m\ge1$, residue $r$, cutoff $K$, and length $T$, there exists a positive $M\equiv r\pmod m$ such that **all** $k(2^iM)>K$ for $0\le i\le T$. This tests the information in the integer residues of an entire finite doubling block.

Indeed, the Fibonacci pair update $(x,y)\mapsto(y,x+y)$ is a permutation modulo $m$. There are arbitrarily large $j$ with $F_j\equiv1\pmod m$. Set $M=(r+m)F_j$ using the nonnegative representative $r$. Since $F_{j+1}-\varphi F_j=(-1/\varphi)^j$, all $2^iM\varphi$ for $i\le T$ can be made closer to integers than $\varphi^{-K-1}$. The lower bound $\|z\varphi\|\ge\varphi^{-k(z)-1}$ forces the assertion. The witnesses $M$ are general integers. The distribution of the automaton's inputs along the particular integers $2^n$ remains an additional arithmetic question. [Kernel proof](../NormalityChecker/GoldenCongruence.lean) · [Least-index bound](../NormalityChecker/GoldenOrbit.lean) · [Barnoff, Bright and Shallit](https://arxiv.org/abs/2405.02727)

For the **actual powers of two**, exact greedy Zeckendorf decomposition produced both outcomes $k(2^n)\le4$ and $k(2^n)>4$ in every reachable residue class of every odd modulus from 3 through 101. There are 1,189 pairs (modulus, residue), and all first witnesses occur by $n=2667$. These finite counterexamples exclude any rule on those residues that must classify every power correctly. An eventual rule, a bias within a class, and positive lower density remain separate questions. [Reproduction script](../scripts/discrepancy_experiments.py)

```sh
python3 -B scripts/kernel_coverage.py
python3 -B scripts/discrepancy_experiments.py quadratic-moduli --limit 4096
python3 -B -m unittest discover -s scripts -p 'test_*.py'
```
