# A Gaussian logarithm prefix with denominator exponent 5/12

**Theorem.** There are explicit rational numbers $Y_N$ with $2^N\log 2-Y_N=O(1/(N+1))$ whose reduced denominators $q_N$ satisfy
```math
\lim_{N\to\infty}\frac{\log q_N}{N}=\frac5{12}.
```
The real dyadic logarithm construction has optimal exponent $1/2$ for finite integer combinations of $\log(1\pm 2^{-k})$ truncated at a common binary exponent. The improvement uses the real part of a Gaussian logarithm. The standalone Lean file verifies the four-series identity, the common denominator, prime removal throughout the specified band, and the eventual upper bound for every exponent above $5/12$. The proof of the matching lower bound and of the approximation error is given below. [Lean checks](../../NormalityChecker/GaussianLogarithmCharacters.lean) · [Real dyadic optimality theorem](../strided-logarithm.md#why-half-is-optimal-in-this-class)

There is also a uniform first-frequency deficit for the **modulo $p^2$ joint character** of the two original rational prefixes. Its proof uses the one-step additive term and Weil's Kloosterman bound. The real first-frequency deficit for $\log 2$ remains open.

## The logarithmic identity and the truncation

Set $z=(1+i)/8$. Then $|1-z|^2=25/32$ and $(25/32)(9/8)=(15/16)^2$. Add $k$ times the logarithm of this last identity to $\log 2=-2\log(3/4)+\log(9/8)$. For real $x\ge0$ set
```math
S_k(x)=
2\sum_{j\le x/2}\frac{(1/4)^j}{j}
-(1+k)\sum_{j\le x/3}\frac{(-1/8)^j}{j}
+2k\sum_{j\le x/4}\frac{(1/16)^j}{j}
-2k\sum_{j\le 2x/5}\frac{\Re(z^j)}{j}.
```
All sums start at one. The Taylor series for $-\log(1-u)$ on $|u|<1$ and $2\Re\log(1-z)=\log(25/32)$ give $S_k(x)\to\log 2$. Take $Y_N(k)=2^N S_k(N)$, with $k=5$ for the theorem. The case $k=0$ recovers the two original strides. Imaginary parts of the same Gaussian logarithms occur in Takahashi's binary BBP formulas for arctangents. The real part here supplies a vanishing prime band. [Takahashi, equations (11)–(19)](https://tsukuba.repo.nii.ac.jp/record/2001720/files/RJ_51-1-177.pdf) · [Gaussian arctangent denominators](../gaussian-arctangent-denominators.md)

Put $e_j=\lceil 5j/2\rceil$. The integers $2^{e_j}\Re(z^j)$ repeat the eight values $1,0,-1,-1,-1,0,1,1$, beginning at $j=1$. This follows by squaring $1+i$ and using $(1+i)^8=16$. For integer $N$, $j\le 2N/5$ is equivalent to $e_j\le N$. Hence every shifted term has an integer numerator over $j$ for integral $k$, and the reduced denominator divides $D_{\lfloor N/2\rfloor}$, where $D_m=\mathrm{lcm}(1,\ldots,m)$ and $D_0=1$. The Lean definition uses the integer matrix $G$ for multiplication by $2+2i$. Its trace after raising to the power $j$ equals $2\Re((2+2i)^j)$, so division by $16^j$ gives exactly $2\Re(z^j)$. For the error let $(m_2,m_3,m_4,m_G)$ be the four cutoffs in order. Within each series the omitted binary exponents are distinct integers exceeding $N$. Summing $2^{N-e}$ over these exponents gives at most one, so
```math
|2^N\log2-Y_N(k)|\le
\frac{2}{m_2+1}+\frac{|1+k|}{m_3+1}
+\frac{2|k|}{m_4+1}+\frac{2|k|}{m_G+1}.
```

## Prime residues and the exact rate

For any odd prime $p$ with $p^2>N/2$, the rational $pY_N(k)$ has denominator prime to $p$ when $k$ is integral. Its residue is
```math
pY_N(k)\equiv 2^N S_k(N/p)\pmod p.
```
After multiplication by $p$, the terms that survive have $j=p\ell$. The four cutoffs on $\ell$ are precisely those defining $S_k(N/p)$. Fermat's theorem treats the real powers. In the Gaussian ring modulo $p$, Frobenius fixes $i$ or sends it to $-i$, according as $p$ is $1$ or $3$ modulo four. Both maps preserve the real coefficient. Thus $\Re(z^{p\ell})\equiv\Re(z^\ell)$ for both prime classes. It matters that the last cutoff is $\lfloor 2N/(5p)\rfloor$ at this stage. Rounding $N/p$ to an integer first can change the residue.

The following are the exact short sums at the top of the denominator.

| Reciprocal scale $x=N/p$ | $S_2(x)$ | $S_5(x)$ |
| --- | ---: | ---: |
| $0\le x<2$ | 0 | 0 |
| $2\le x<5/2$ | $1/2$ | $1/2$ |
| $5/2\le x<3$ | 0 | $-3/4$ |
| $3\le x<4$ | $3/8$ | 0 |
| $4\le x$ | positive | positive |

For the last row the first sum is at least $1/2$, the second at least $(1+k)(1/8-1/128)$ by alternating-series bounds, and the third at least $2k/16$. The sum of the real parts in the fourth, before its coefficient, is at most $1/8+1/48$. Indeed $|z|^2=1/32$, $|z|<1/4$, and the terms after the first cost at most $|z|^2/[2(1-|z|)]$. Substituting either $k=2$ or $k=5$ gives a strictly positive lower bound. The pole therefore vanishes throughout $N/3<p\le 2N/5$ for $k=2$ and throughout $N/4<p\le N/3$ for $k=5$. The Lean proof applies to every odd prime in the respective band, including the small cases.

Here is a quantitative bound for all other cancellations. Set $m=\lfloor N/2\rfloor$ and let $I_k(N)$ be the corresponding vanished band. Then for $k=2,5$,
```math
\log q_N(k)=\log D_m-\sum_{p\in I_k(N)}\log p+O(N^{2/3}),
```
where the sum is over primes. For large $N$, put $K=\lceil N^{1/3}\rceil$. All first powers $p\le K^2$ cost $O(K^2)$ by Chebyshev's upper bound. All prime powers after the first in $D_m$ cost $O(\sqrt N\log N)$ by charging at most $\log N$ to each prime at most $\sqrt m$. For $K^2<p\le m$, only the first power occurs. As $p$ varies, the four short cutoffs decrease coordinatewise and are at most $K$. There are at most $4K+1$ distinct tuples. Each nonzero short sum is bounded absolutely by a fixed constant and has denominator dividing $16^K D_K$. Its reduced numerator has logarithm of absolute value $O(K)$. Every further canceled prime divides one of these nonzero numerators. Their product costs $O(K^2)$, as required. The prime number theorem now gives rates $1/2-(2/5-1/3)=13/30$ and $1/2-(1/3-1/4)=5/12$, respectively.

**Optimization within this one-parameter family.** Among all fixed rational $k$, the unique minimum is $5/12$ at $k=5$. Fixed coefficient denominators have bounded logarithmic cost. For $x\ge2$, $S_0(x)>0$ by the positive first sum and the alternating second sum. On each interval $v/2\le x<(v+1)/2$, $S_k$ is affine in $k$. An interval with nonzero slope vanishes for just the rational $-S_0/(S_1-S_0)$ and has prime mass $2/[v(v+1)]$. For zero slope it never vanishes. For each fixed $k$ the zeros stop eventually since $S_k(x)\to\log2>0$. The preceding prime argument consequently gives the rate as $1/2$ less the total mass of the vanishing intervals with $v\ge4$. Exact enumeration for $4\le v<200$ gives mass $1/12$ for $k=5$ and a maximum of $1/15$ over all other parameters. The entire unexamined tail has mass $1/100$, and $1/15+1/100<1/12$. The preceding positivity proof determines the full mass at $k=5$. This last optimality comparison uses finite rational arithmetic. [Enumeration and reproduction](complementary_characters.py)

## A uniform modular joint character deficit

Let $U_N=2^N\sum_{2j\le N}4^{-j}/j$ and $V_N=-2^N\sum_{3j\le N}(-1/8)^j/j$. Their real targets are the shifted $\alpha=\log(4/3)$ and $\beta=\log(9/8)$. For a prime $p>3$ and integers $a,b$ with at least one nonzero modulo $p$, put
```math
z_n=e_{p^2}\big(p(aU_n+bV_n)\big),\qquad
e_m(r)=\exp(2\pi i r/m).
```
A rational argument in this definition is reduced modulo $m$ by inverting its denominator. Work on consecutive $I=\{L,\ldots,L+T-1\}$, with $0\le L$, $1\le T\le p$ and $L+T<p^2$, so the multiplied prefixes are $p$-integral. The weights at the six residue classes $r=0,1,\ldots,5$ are
```math
(w_0,w_1,w_2,w_3,w_4,w_5)=(2a-3b,0,2a,3b,2a,0).
```
Let $d$ be the number of these weights nonzero modulo $p$. Uniformly in the interval and the primitive joint character,
```math
1-\left|\frac1T\sum_{n\in I}z_n\right|
\ \ge\ \frac{d}{54}-O\!\left(\frac{\sqrt p\log p}{T}\right).
```
In particular $d=4$ for the character $(a,b)=(2,1)$ of the original combined numerator. Its limiting lower deficit is at least $2/27$ on any sequence with $T/(\sqrt p\log p)\to\infty$, including the full band $2p\le n<3p$. Every primitive direction has $d\ge2$.

**Proof.** Write $f_n=z_{n+1}/z_n^2$. Outside the at most one index with $p\mid n+1$, the exact recurrence gives $f_n=e_p(w_r/(n+1))$ with $r=(n+1)\bmod6$. The exceptional term costs $O(1)$. On a zero-weight class the character equals one. On each other class the sum costs $O(\sqrt p\log p)$. Indeed write the denominators as $6t+r$ in a consecutive interval of length at most $p$. Completing the indicator of the interval modulo $p$ introduces Fourier coefficients of total absolute value $O(p\log p)$ for the unnormalized Fourier transform. This follows by summing the geometric progression bound $\min(T,p/(2|h|))$ over centered frequencies. Substituting $x=6t+r$ in each complete sum gives a Kloosterman sum $\sum_{x\ne0}e_p(w_r/x+h'x)$ up to a constant phase. The zero Fourier mode has sum $-1$, and every other mode has absolute value at most $2\sqrt p$ by Weil. Inverting the Fourier transform divides by $p$. Thus $|T^{-1}\sum f_n|\le1-d/6+O(\sqrt p\log p/T)$. [Weil, *On some exponential sums*](https://doi.org/10.1073/pnas.34.5.204)

Choose a unit $c$ in the direction of $\sum_{n\in I}z_n$, taking $c=1$ for zero sum. For unit $u,c$,
```math
|vc-u^2|^2\le 3|v-c|^2+6|u-c|^2.
```
Factor $vc-u^2=(v-c)c+(c-u)(c+u)$ and square the bound $|v-c|+2|u-c|$. With $u=z_n$, $v=z_{n+1}$ the left side is $2(1-\Re(c f_n))$. Summing the right side costs at most $9\sum|z_n-c|^2+12$ by shifting the endpoint, and $\sum|z_n-c|^2=2T(1-|T^{-1}\sum z_n|)$. This proves the estimate. Lean verifies the pointwise inequality and its finite sum with endpoint cost 12. [Lean proof](../../NormalityChecker/GaussianLogarithmCharacters.lean) · [Earlier single-residue counting bound](../dyadic-prefix-residues.md)

**Short initial subintervals of the band.** At $L=2p$, the direction $(2,1)$ retains a deficit of at least $1/54-o(1)$ even when $T=\lfloor p^\eta\rfloor$ for any fixed $0<\eta<1/2$. In fact this holds for $T<p$ as soon as $\log T/[(\log p)^{2/3}(\log\log p)^2]\to\infty$. Restrict the forcing sum to $n+1=2p+6j$ with $1\le j\le T/6$. The weight is 4 since $2p$ is even and prime to 3. The forcing equals $e_p((4/6)/j)$. Bourgain and Garaev bound the absolute value of this initial reciprocal sum of length $M=\lfloor T/6\rfloor$ by a constant times $M(\log\log p)^3\log p/(\log M)^{3/2}$, uniformly in the nonzero numerator. This is $o(T)$ under the displayed condition. Bounding all remaining forcing terms by one gives $|T^{-1}\sum f_n|\le5/6+o(1)$. The same squared-distance inequality gives the claim. The alignment at $2p$ is needed for this application of the initial-sum theorem. [Bourgain and Garaev, Theorem 16](https://arxiv.org/pdf/1211.4184)

## Obstructions at the real place

For a reduced rational $y=A/q$ the real character $e(y)$ factors over $p^s\parallel q$. The $p$-factor is $e_{p^s}(A(q/p^s)^{-1})$, with inverse taken modulo $p^s$. The Chinese remainder theorem proves the identity by multiplying the sum of the local arguments by $q$ and reducing modulo each $p^s$. When $s=1$ this real factor uses $py$ only modulo $p$. The second digit used in the modular deficit theorem does not enter that factor.

**The real character contributed by one prime.** On $2p\le n<3p$ the actual $p$-factor of $e(Y_n(0))$ is $e_p(2^{n-1})$, by the short-sum congruence with $k=0$. For a relative-density-one set of primes its mean tends to zero on every subinterval of this band of length at least $c p$, uniformly for each fixed $c>0$. Indeed, apart from $O(X^{2/3})$ primes $p\le X$, the group $H=\langle 2\rangle\subset\mathbb F_p^\times$ has size $D>p^{1/3}$. Every exception divides the product of $2^j-1$ for $1\le j\le X^{1/3}$, whose logarithm is $O(X^{2/3})$. The Bourgain–Glibichuk–Konyagin subgroup estimate gives some $\delta>0$ such that $|\sum_{x\in H}e_p(bx)|\ll D p^{-\delta}$ for every nonzero $b$. For any multiplicative character $\chi$ of $H$, squaring the corresponding twisted sum gives
```math
\left|\sum_{x\in H}\chi(x)e_p(bx)\right|^2
=\sum_{h\in H}\chi(h)\sum_{x\in H}e_p(b(h-1)x)
\ll D+D^2p^{-\delta}.
```
Thus every Fourier coefficient of the length-$D$ periodic sequence $e_p(b2^j)$ is $O(D p^{-\delta'})$ for some $\delta'>0$. Completing an interval modulo $D$ costs at most $O(\log(2D))$ as above. Splitting a length-$T$ interval into periods and one remainder gives an absolute bound $O((T+D\log(2D))p^{-\delta'})$, which is $o(T)$ for $T\ge cp$. This treats a genuine factor of the real character. The real character also contains all other prime factors at the same time. [Bourgain, Glibichuk and Konyagin, exponential sums over multiplicative subgroups](https://doi.org/10.1112/S0024610706022721)

The order hypothesis matters even for finite behavior. If $p=2^d-1$ is prime, the first-frequency deficit of its factor over a whole period is at most $2\pi^2(4^d-1)/(3d p^2)$, by $1-\cos(2\pi t)\le 2\pi^2 t^2$ evaluated at $t=2^j/p$, $0\le j<d$. At the known prime $2^{127}-1$ this bound is below $0.052$. Infinitely many such primes would prevent a uniform positive deficit for this first digit at every prime.

There is a finite-interval obstruction that also preserves the recurrence. On any interval $[L,H]$ and for any finite set of odd primes, choose a dyadic rational $A$ divisible at each prime by an arbitrarily prescribed power and satisfying $|A-\log2|<\epsilon 2^{-H}$. Such dyadic rationals are dense, by taking multiples of the product of the prime powers on finer binary grids. Replace the original combined prefix $Y_n(0)$ by $Y_n(0)-2^n A$. The new sequence obeys exactly the same inhomogeneous recurrence and agrees at all the prescribed modular precisions, yet every new real phase on the interval is within $4/(L+1)+\epsilon$ of zero by the original tail bound. This example changes the initial value. It identifies the additional information required of an argument using local data on one interval. [Two-stride tail bound](../../NormalityChecker/StridedLogarithm.lean)

Even individually normal real components and rational independence of $1,\alpha,\beta$ would be insufficient. Let $K=\sum_{j\ge0}2^{-2^j}$. For almost every $x$, both $x$ and $y=K-2x$ are base-two normal, since $x\mapsto K-2x$ preserves Lebesgue measure modulo one. Also $1,x,y$ are rationally independent outside a countable set. Substitution gives an equation in $x$ and $K$. If the coefficient of $x$ vanishes, irrationality of $K$ forces the remaining coefficients to vanish. Nevertheless $2x+y=K$, whose first-frequency deficit tends to zero. Its first $N$ bits have only $O(\log(N+2))$ transitions, and the finite escape inequality bounds the deficit by four times the transition frequency plus $2/N$. The actual logarithms likewise give rational independence: an integer relation with a nonzero constant would make the exponential of a nonzero rational algebraic, contrary to Lindemann's theorem. If the constant vanishes, the valuations at 2 and 3 of $4/3$ and $9/8$ have determinant one. [Sparse orbit and finite escape bounds](../transition-discrepancy.md#first-frequency-escape)

A precise possible real input is a mismatch of the two marginal character averages. Write $A_N(t)=N^{-1}\sum_{n<N}e(2^nt)$, where $e(t)=\exp(2\pi it)$. Cauchy–Schwarz and $|e(ht)-1|\le |h|\,|e(t)-1|$ give, for every nonzero integer $h$,
```math
1-\Re A_N(\log2)\ \ge\
\frac{|A_N(2h\alpha)-\overline{A_N(h\beta)}|^2}{2h^2}.
```
Subtract the two phases inside the averages. Their squared distance is $|e(h2^n(2\alpha+\beta))-1|^2$. Also $|A_N(2h\alpha)-A_N(h\alpha)|\le 2/N$ by shifting the index. Thus a persistent mismatch for one fixed $h$ would suffice, even without either marginal having a limit. The normal-marginal example shows why a mismatch cannot be inferred from separate equidistribution. Rivoal's estimates give lower bounds for distances from specified rational grids, including a grid with denominator $2^m D_m$ for $\log 2$. They constrain individual approximations. A persistent mismatch or a positive mean deficit for the actual real joint phase still requires an estimate over many positions. [Rivoal, Theorem 4(ii) and remark 2](https://rivoal.perso.math.cnrs.fr/articles/logconvergents.pdf) · [First-frequency discrepancy criterion](../classical-discrepancy.md)

## Direct binary digit extraction

For a starting position $N$ and word length $T$, choose a precision $q>T$ and put $s=N+q$. Each retained term in $Y_s(5)$ is $w2^{s-e}/j$ with an integer $w$. Compute the power of two modulo $j2^q$, multiply by $w$, divide by $j$ and round down. Each replacement changes the rounded term by a multiple of $2^q$. The discarded fractions have total between zero and the number of terms. The signed tail has absolute value at most 28 by the four-term bound above. These give integer lower and upper endpoints modulo $2^q$, retaining an unwrapped interval before the final reduction. When the endpoints divided by $2^{q-T}$ have the same floor, this floor modulo $2^T$ gives the word. Otherwise increase $q$. The interval width after rescaling tends to zero and $2^{N+T}\log2$ is irrational, so the test terminates. This is the modular exponentiation method of Bailey, Borwein and Plouffe applied to the new coefficients with certified rounding. [Bailey, Borwein and Plouffe, *On the rapid computation of various polylogarithmic constants*](https://doi.org/10.1090/S0025-5718-97-00856-9)

| Binary shift $N$ | Next 64 bits, written in hexadecimal |
| ---: | --- |
| 0 | B17217F7D1CF79AB |
| 1,000 | 3FD5C607F4CA11FB |
| 10,000 | 5B60899D52247F4C |
| 100,000 | 4B3FD4B99B9FBC82 |

The independent series $\sum_{j\ge1}2^{-j}/j$ certifies the same four words. At $N=256,1024,4096$ the reduced denominator bit lengths for $k=5$ are $150,623,2458$. Direct rational summation checks the short-sum congruence at every odd prime $\sqrt{N/2}<p\le N/2$ in each case for $k=2,5$. These are finite checks. [Exact arithmetic program](complementary_characters.py)

```sh
lake env lean NormalityChecker/GaussianLogarithmCharacters.lean
python3 notes/phase13/complementary_characters.py
```
