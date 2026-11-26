# Sparse binary words in multiplicative Lambert series

**Theorem (paper proof).** Let χ be a nonprincipal real Dirichlet character, let $L_\chi=\sum_{m\ge1}\chi(m)/(2^m-1)$, and count binary words by their starting shifts in $[N,N+H)$. For every fixed word $w$ of length $k\ge1$ containing a `1` and every fixed $7/12<a\le1$, uniformly for integers $N^a\le H\le N$,

```math
\#_w(N,H)\asymp_{w,\chi,a}\frac{H}{\sqrt{\log N}},
\qquad
H-\#_{0^k}(N,H)\asymp_{k,\chi,a}\frac{H}{\sqrt{\log N}}.
```

The ordinary interval discrepancy of its first $N$ doubling-orbit points satisfies

```math
1-D_N(L_\chi)\asymp_\chi\frac{\log\log N}{\sqrt{\log N}}.
```

Thus $L_\chi$ is irrational, contains every finite binary word infinitely often, and has one-digit frequency zero. The proof applies to the class below with $\sqrt{\log N}$ replaced throughout by $(\log N)^{1-\delta}$, where δ is the density parameter for the primes with a nonzero first-power coefficient. For $\chi_4$, the coefficients are $r_2(n)/4$, with $r_2(n)$ counting ordered, signed representations by two squares. The transcendence of this example also follows from a published modular-form theorem (Section 7).

## 1. Hypotheses and conventions

Let $q_0\ge3$ be fixed and let $S$ be a set of primes coprime to $q_0$ containing all primes in at least one reduced class $a_0$ modulo $q_0$. Assume that for some $0<\delta<1$,

```math
\sum_{p\le x,\ p\in S}\frac1p=\delta\log\log x+O(1).
```

Let $c$ be an integer-valued multiplicative function with $c(1)=1$ and the following local conditions.

- For all prime powers $p^e$, $0\le c(p^e)\le e+1$.
- At the primes in $S$ we have $c(p)=2$, and at the other primes coprime to $q_0$ we have $c(p)=0$.
- At one fixed prime $p_0\in S$ we have $c(p_0^{2u})=2u+1$ for every integer $u\ge0$.

Put $\kappa=1-\delta$ and $f=c*\mu$, where μ is the Möbius function and $*$ is Dirichlet convolution. Thus $c=f*1$ and $f(p^e)=c(p^e)-c(p^{e-1})$. In particular $|f(n)|\le\tau(n)$ and $c(n)\le\tau(n)\le n$, where τ counts divisors. Absolute convergence justifies the geometric expansions and rearrangement

```math
L_f=\sum_{m\ge1}\frac{f(m)}{2^m-1}=\sum_{n\ge1}c(n)2^{-n}.
```

Write $x_n=\{2^n L_f\}$ for $n\ge0$. We use the binary digits given by floors, so that the first digit of $x_n$ is digit $n+1$ of the fractional part of $L_f$. A word $w$ of length $k$ with integer value $u$ occurs at shift $n$ exactly when $x_n\in[u2^{-k},(u+1)2^{-k})$. We count starts, allowing a word to extend past the last shift in the window. For words wholly contained in the $H$ digits beginning at position $N+1$, restrict starts to $[N,N+H-k+1)$. The difference in each count is at most $k-1$. The discrepancy normalization is

```math
D_M(L_f)=\sup_{0\le s<t\le1}
\left|\frac{\#\{0\le n<M:s\le x_n<t\}}{M}-(t-s)\right|.
```

All logarithms are natural unless a base is indicated. Constants may depend on the fixed data $c,S,q_0,p_0,\delta$ and on indicated parameters. The threshold in every moving-window assertion is independent of $H$.

For a real nonprincipal character modulo $q_0$, take $S=\{p:\chi(p)=1\}$. For an imprimitive character use its actual modulus, which includes the primes at which the character vanishes. The kernel of χ has index two in the group of units. The fixed-modulus PNT and partial summation give the displayed harmonic sum with $\delta=1/2$. At primes with $\chi(p)=1,-1,0$, respectively, $c_\chi(p^e)$ is $e+1$, the indicator that $e$ is even, or $1$. In particular the support requires an even exponent at each prime with $\chi(p)=-1$, with no additional restrictions. Jacobi's two-square formula gives the identification for $\chi_4$. [Diamond and Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005, Exercise 4.8.7(c)][diamond]

More generally $S$ can be any nonempty proper union of reduced classes modulo $q_0$. A subgroup of index $m$ gives $\delta=1/m$. A canonical example takes $f$ completely multiplicative with prime values $1$ on $S$, $-1$ off $S$ at primes coprime to $q_0$, and $0$ at the prime divisors of $q_0$. Take $q_0=5$ and $S=\{p:p\equiv1\pmod 5\}$ for the example with $\delta=1/4$ used below.

The harmonic hypothesis also permits every real $\delta\in(0,1)$. Choose a prime modulus $q_0$ with $d_0=1/\varphi(q_0)\le\delta$. Retain the whole class $1$ and, among the other unramified primes in increasing order, retain the $j$th when $\lfloor rj\rfloor-\lfloor r(j-1)\rfloor=1$, where $r=(\delta-d_0)/(1-d_0)$. The order of selection gives a counting error of at most one relative to $r$ times the number of eligible primes. Partial summation gives $O(1)$ error for their reciprocal sum, and the fixed-modulus PNT gives the required exponent. The local hypotheses matter. For example, the indicator of integers whose prime factors all lie in $1\pmod 4$ has prime-support density $1/2$ and is itself the digit sequence of its dyadic series. All its supported indices are $1\pmod 4$, so the word `11` is absent.

## 2. Odd parts and displaced sources

Write $c(m)=2^{V(m)}U(m)$ on its support, with $U(m)$ odd. At zeros put $U(m)=V(m)=0$. The odd part $U$ is nonnegative and multiplicative, since valuations add on products of coprime arguments with positive coefficients and a zero factor makes both sides zero. We have $U(p)=1$ on $S$, $U(p)=0$ off $S$ for $p\nmid q_0$, and $U(p^e)\le e+1$ everywhere. In particular $U(p^e)\le2^e$ and $U(m)\le\tau(m)\ll_\epsilon m^\epsilon$ for each $\epsilon>0$. The last estimate follows by using $e+1\le2^e\le p^{e\epsilon}$ for large primes and absorbing the finitely many suprema of $(e+1)p^{-e\epsilon}$ at the small primes.

**Short sums.** For each fixed $0<\sigma\le1$, uniformly for $x^\sigma\le y\le x$ and large $x$,

```math
\sum_{x-y<m\le x} U(m)\ll_{\sigma}\frac{y}{(\log x)^\kappa}.\tag{1}
```

Shiu's Theorem 1 requires a nonnegative multiplicative function $g$ satisfying $g(p^e)\le A_1^e$ and $g(n)\le A_2(\epsilon)n^\epsilon$ for every $\epsilon>0$. Its bound for a reduced progression $a'\pmod k'$ is $y/(\varphi(k')\log x)$ times $\exp(\sum_{p\le x,\ p\nmid k'}g(p)/p)$, with $k'<y^{1-\alpha}$ and $x^\beta<y\le x$ for fixed $0<\alpha,\beta<1/2$. The printed convention uses $0<a'<k'$. To use it literally, write $m=2^e v$ with $v$ odd. For $2^e\le x^{\sigma/2}$ apply it to $1\pmod2$ with right endpoint $x/2^e$, length $y/2^e$, $\alpha=1/4$ and $\beta=\sigma/4$. All length and modulus inequalities hold for large $x$, and $\log(x/2^e)\asymp\log x$. The harmonic hypothesis bounds the exponential factor by $O((\log x)^\delta)$. Summing with $U(2^e)\le e+1$ costs $\sum_e(e+1)2^{-e}<\infty$. The remaining terms contribute $O(x^\epsilon(yx^{-\sigma/2}+\log x))$ by counting multiples of $2^e$ and bounding $U(m)$ pointwise. Taking $\epsilon=\sigma/8$ absorbs this error in (1). In particular (1) with $y=x$ gives the required global odd-part bound. [Shiu, J. Reine Angew. Math. **313** (1980), 161–170, Theorem 1, pp. 162–163][shiu] · [Original theorem scan][shiu-scan]

**Support and higher powers.** For characters, both the support indicator and $U$ satisfy Wirsing's nonnegative mean-value theorem. In its PNT form, if $g(p^e)\le A B^e$ at higher powers for some $B<2$ and $\sum_{p\le x}g(p)\sim\delta x/\log x$, then

```math
\sum_{m\le x}g(m)\sim\frac{e^{-\gamma\delta}}{\Gamma(\delta)}\frac{x}{\log x}
\prod_{p\le x}\left(1+\sum_{e\ge1}\frac{g(p^e)}{p^e}\right).
```

Use $B=3/2$ and the fixed-modulus PNT. Each local factor is $1+g(p)/p+O(p^{-2})$ uniformly, including the possible higher odd parts $U(p^e)=(e+1)/2^{v_2(e+1)}$ at split primes. Partial summation of the fixed-modulus PNT with its classical error gives $\sum_{p\le x} g(p)/p=\tfrac12\log\log x+C_g+o(1)$. Both sums are therefore asymptotic to positive constants times $x/\sqrt{\log x}$. For $\chi_4$ the support assertion is the Landau–Ramanujan theorem, with support constant $2^{-1/2}\prod_{p\equiv3\ (4)}(1-p^{-2})^{-1/2}$. This constant counts representable integers, while the odd-part sum uses the full higher-power local factors. [Wirsing, Math. Ann. **143** (1961), 75–102, Satz 1, p. 76][wirsing] · [Original theorem scan][wirsing-scan] · [Berndt and Moree, *Sums of two squares and the tau-function*, §§4, 7][berndt-moree]

The squarefull argument sketched in Phase 16 can also be completed directly. Write $m=sr$ with $s$ the product of the primes of exponent exactly one and $r$ the product of the remaining prime powers. Then $s$ is squarefree, $r$ is squarefull and $\gcd(s,r)=1$. The contribution of $s$ is bounded by the count of squarefree integers composed of $S$ and the finitely many primes dividing $q_0$, bounded by $O(t/(\log t)^\kappa)$ up to $t$ by the same Shiu argument applied to their indicator. Drop coprimality for an upper bound and use $U(r)\le\tau(r)$. For $r\le\sqrt x$, use $t=x/r$ and $\sum_{r\,\mathrm{squarefull}}\tau(r)/r<\infty$. For $r>\sqrt x$, bound the $s$ count by $x/r$. Since $\sum_{r\,\mathrm{squarefull}}\tau(r)r^{-3/4}<\infty$, this contributes $O(x^{7/8})$. Both Euler products converge because their first nontrivial prime-power terms have $e\ge2$ and their local remainders are $O(p^{-2})$ and $O(p^{-3/2})$, respectively.

**Exact reindexing.** Set $t(m)=m-V(m)$ on the support. From $c(m)\le m$ we have $V(m)\le\log_2 m$ and $m/2\le t(m)\le m$. The lower bound follows from $\log_2 m\le m/2$ for integers $m\ge4$, with $m=1,2,3$ checked using integer valuations. Define $C(t)=\sum_{m:t(m)=t}U(m)$ over supported $m$. Each such sum is finite. All terms with $t(m)\le n$ contribute integers to $2^n L_f$, including those displaced across $n$ from the right. Thus

```math
x_n=\{A(n)\},\qquad A(n)=\sum_{d\ge1}2^{-d}C(n+d)\ge0.
```

For each fixed $d$, summing $C(n+d)$ over integer $n\in[N,N+H)$ gives exactly $\sum_{m:t(m)\in[N+d,N+H+d)}U(m)$. This is the finite `arrival_sum` identity applied to the finitely many eligible sources, or follows by interchanging the finite sums. Summing levels uses nonnegativity. No source with $m<N$ can contribute to the window. For $1\le d\le N$, any eligible source satisfies $N+d\le m\le6N$ and $m<N+H+d+B$, where $B=\lceil\log_2(6N)\rceil$. This enlarged interval includes sources beyond the right boundary. Equation (1), applied with any fixed $0<\sigma<a$, bounds the mass by $O_a((H+B)/(\log N)^\kappa)=O_a(H/(\log N)^\kappa)$. Half-open endpoints are handled by writing the integer range as $(N+d-1,N+H+d+B-1]$. The same estimate holds for a fixed translation of the window to the right by applying (1) with the same exponent margin. For $d>N$, use $m\le2(n+d)$ and $U(m)\le m$ to get $C(n+d)\ll(n+d)^2$. Its geometric tail contributes $O(HN^2 2^{-N})$. Consequently,

```math
\sum_{N\le n<N+H} A(n)\ll_a H(\log N)^{-\kappa},\qquad
\sum_{0\le n<M} A(n)\ll M(\log M)^{-\kappa}.\tag{2}
```

For the second bound, use the global sum (1) up to $4M$ when $d\le M$, and the same distant-tail argument when $d>M$. A first digit `1` implies $x_n\ge1/2$ and hence $A(n)\ge1/2$. Thus the number of ones is bounded by twice the corresponding sum in (2). Requiring a `1` at one specified position of $w$ proves the moving-window upper bound, since the associated shifted window satisfies the same estimate. For $0^k$, a union bound over its $k$ positions makes the number of rejected starts $O_{k,a}(H(\log N)^{-\kappa})$. The same estimates hold in prefixes using $M+k$ in (2). [Lean `arrival_sum`][arrivals-lean] · [Lean `nonneg_one_bit_count_le`][weighted-lean]

## 3. Uniform prime input and the reciprocal sum

**Short-interval Bombieri–Vinogradov.** Perelli, Pintz and Salerno's 1985 theorem on p. 2 of *Inventiones Mathematicae* **79**, 1–9, gives equation (1.1) of their paper for $y=x^\nu$, fixed $7/12<\nu\le1$, and $Q=x^{1/40}$. With $\psi(x;q,v)=\sum_{n\le x,\ n\equiv v\ (q)}\Lambda(n)$, its form is

```math
\sum_{q\le x^{1/40}}\max_{(v,q)=1}\sup_{0\le h\le x^\nu}\sup_{x/2<z\le x}
\left|\psi(z+h;q,v)-\psi(z;q,v)-\frac{h}{\varphi(q)}\right|
\ll_{A,\nu} x^\nu(\log x)^{-A}\qquad(A>0).\tag{3}
```

This contains the fixed-modulus progression PNT needed below, with a strict exponent margin. Huxley's 1972 paper obtains the $7/12$ threshold from a zero-density bound for the Riemann zeta function. Here the progression version follows directly by retaining $q=q_0$ in (3), once $q_0\le x^{1/40}$. The maxima give uniformity in the residue, initial point and length. [Perelli, Pintz and Salerno, *Bombieri's theorem in short intervals. II*][pps85] · [Original theorem scan][pps85-scan] · [Huxley, Invent. Math. **15** (1972), 164–170][huxley]

Write $\theta$ for the cutoff exponent on the small factor in the plant. Fix

```math
0<\theta<\min(a-7/12,a-1/2,1/2),\qquad
7/12<\nu<a-\theta.
```

All subsequent prime intervals will have starting point $X\asymp N/b$ and length $Y=H/b<X$, where $b\ll_w N^\theta$ and $b\ge1$. Thus $Y\gg_w N^{a-\theta}$, $\log X\asymp_\theta\log N$, and $Y/(X+Y)^\nu\to\infty$ uniformly. Use $x=X+Y$ in (3) and split $(X,X+Y]$ into at most $1+Y/x^\nu$ pieces of length at most $x^\nu$. Every piece starts strictly above $x/2$. The error from all pieces is $O_{A,\nu}(Y/(\log X)^A)$. Removing prime powers costs $O(X^{1/2+1/40}(\log X)^2)$ in total over $q\le x^{1/40}$, since there are $O(X^{1/2}\log X)$ higher prime powers up to $2X$. This is absorbed in the logarithmic error since $1/2+1/40<\nu$. Writing $\vartheta(X,Y;q,v)$ for the sum of $\log p$ on $(X,X+Y]$ in class $v$, we therefore have

```math
\sum_{q\le (X+Y)^{1/40}}\max_{(v,q)=1}
\left|\vartheta(X,Y;q,v)-\frac{Y}{\varphi(q)}\right|
\ll_{A,a,\theta,w}Y(\log X)^{-A}.\tag{4}
```

The fixed class $a_0\pmod{q_0}$ has $(1+o(1))Y/(\varphi(q_0)\log X)$ primes, by (4) and $\log p=\log X+O(1)$. For a character one can sum over all split classes to obtain $(1+o(1))Y/(2\log X)$. We use just one class for the general lower bound. The CRT modulus $q_0d$ is covered whenever $d\le (X+Y)^{1/40}/q_0$. In terms of $Y$, the guaranteed range includes $d\le Y^{1/40}/q_0$. We take $d\le Y^{1/80}$, which lies in that range once $Y^{1/80}\ge q_0$.

**Small factors.** Let $\mathcal M$ be the squarefree $m\le N^\theta$ built from primes of $S$ other than $p_0$, with $\ell=\omega(m)\le2\log\log N$. Then

```math
\sum_{m\in\mathcal M}\frac1m\asymp_{\theta,S}(\log N)^\delta.\tag{5}
```

For the upper bound use the Euler product over $S$ up to $N^\theta$. For the lower bound, restrict the product to primes at most $z=N^{\lambda\theta}$ for a sufficiently small fixed $\lambda>0$. Under normalized reciprocal weights on its squarefree products, the expected $\log m$ is $\sum_{p\le z,\ p\in S\setminus\{p_0\}}(\log p)/(p+1)\ll\log z$ by Chebyshev's estimate and partial summation. Markov's inequality therefore leaves at least half the product mass on $m\le N^\theta$ for small enough $\lambda$. The product is $\asymp(\log N)^\delta$ by the harmonic hypothesis. Finally the discarded large-$\ell$ mass is bounded by Rankin's inequality

```math
2^{-2\log\log N}\prod_{p\le N^\theta,\ p\in S}(1+2/p)
\ll(\log N)^{2\delta-2\log 2}=o((\log N)^\delta),
```

as $\delta<1<2\log 2$. This uses a bounded-error harmonic sum, as furnished by fixed classes. A statement about prime density alone need not supply it.

## 4. Planting and isolating a coefficient

Fix the word $w$ of length $k$ and integer value $u$. For $m\in\mathcal M$, set $b=p_0^{2u}m$ and $j_0=k+2+\omega(m)$. The eligible primes $p\equiv a_0\pmod{q_0}$ lie in $(X,X+Y]$ with $X=(N+j_0-1)/b$ and $Y=H/b$. These endpoints give $n=bp-j_0\in[N,N+H)$ exactly, since $n$ is an integer. For large $N$, $p>X\gg_w N^{1-\theta}$ exceeds $b$ and $2\sqrt N$. Hence $p$ is coprime to $b$, and

```math
c(bp)2^{-j_0}=(2u+1)2^{-k-1}.\tag{6}
```

Set $J=\lceil10\log\log N\rceil$ and let $R$ be any nonnegative integer with $R=O(\log\log N)$ with a fixed implied constant. We will require $c(n+j)=0$ for $1-R\le j\le J$, $j\ne j_0$. The left extension will be used to control the discrepancy. The fixed-word count uses $R=0$. For large $N$, $j_0<J$ and all $n+j$ in the strip are positive.

**Sieve for one shifted coefficient.** Fix $h=j-j_0\ne0$ in this strip. Let $z_0=(\log N)^2$, $z=Y^{1/160}$, $D=z^2$, and use the primes $z_0<q\le z$ with $q\nmid q_0$ and $q\notin S$. For every such $q$, $c(q)=0$, so $q\parallel(bp+h)$ implies $c(bp+h)=0$. Because all prime factors of $b$ are in $S$, $\gcd(q,q_0 b)=1$. Also $q>z_0>|h|$, so $p\equiv-hb^{-1}\pmod q$ is a reduced class. Together with $p\equiv a_0\pmod{q_0}$ it defines one reduced class modulo $q_0 q$. The same reasoning by the Chinese remainder theorem applies to every squarefree product $d$ of sieve primes, giving one reduced class modulo $q_0d$ for $d\mid(bp+h)$. The event that some $q^2\mid(bp+h)$ has at most

```math
\sum_{z_0<q\le z}(Y/q^2+1)\ll Y/z_0+z\ll Y/(\log N)^2
```

integer candidates, since $b$ is invertible modulo $q^2$ and $Y\gg_w N^{a-\theta}$. Any remaining prime with $c(bp+h)>0$ avoids all the forbidden classes.

For the sifted primes use weight $\log p$. The sum on $d\mid(bp+h)$ in the progression $a_0\pmod{q_0}$ is $W g(d)+r_d$, where $W=Y/\varphi(q_0)$, $g$ is multiplicative with $g(q)=1/(q-1)$, and $d$ runs over squarefree products of the sieve primes. Equation (4) gives $\sum_{d\le D}|r_d|\ll_A Y/(\log X)^A$ after restricting to these products, since $q_0D\le (X+Y)^{1/40}$. The dependence on $h$ is uniform through the maximum over reduced classes. The elementary estimate on all integers in a single class modulo $d$, together with $D<Y$, gives $|r_d|\ll Y\log X/\varphi(d)$, including $d=1$.

Here are the Selberg weights and the denominator estimate used with these remainders. Let $P$ be the product of the sieve primes. For squarefree $d\mid P$ define $v(d)=\prod_{q\mid d}g(q)/(1-g(q))$ and

```math
G(z)=\sum_{d\le z,\ d\mid P}v(d).
```

Majorize the sifted indicator by $(\sum_{d\mid(bp+h)}\lambda_d)^2$ with $\lambda_1=1$ and support on $d\le z$, $d\mid P$. Write $[d,e]$ for the least common multiple and put $w_r=\sum_{r\mid d}g(d)\lambda_d$. Expanding $g([d,e])=g(d)g(e)\sum_{r\mid(d,e)}1/v(r)$ gives the quadratic form $\sum_r w_r^2/v(r)$. The choice $w_r=\mu(r)v(r)/G(z)$ gives $\lambda_1=1$ by inversion and main term $W/G(z)$. Inversion also gives

```math
|\lambda_d|=\frac{\prod_{q\mid d}(1+v(q))}{G(z)}
\sum_{r\le z/d,\ r\mid P,\ (r,d)=1}v(r)\le1.
```

Indeed, expand the product over divisors $l\mid d$. All resulting $lr$ are distinct, divide $P$ and are at most $z$. Each least common multiple in the error is at most $D=z^2$ and receives at most $3^{\omega(d)}$ terms. Cauchy–Schwarz gives a bound by $(\sum|r_d|)^{1/2}(\sum9^{\omega(d)}|r_d|)^{1/2}$. The crude estimate and the Euler product give $\sum 9^{\omega(d)}|r_d|\ll Y\log X(\log(2D))^9$, since $\prod_{q\le D}(1+9/(q-1))\ll(\log(2D))^9$. Taking $A$ sufficiently large thus gives $O_B(Y/(\log X)^B)$ for any fixed $B>0$ in the weighted sieve error. [Selberg, *The general sieve-method and its place in prime number theory*, Proc. ICM 1950, vol. I, 286–292][selberg-original] · [Modern derivation][selberg]

For the denominator, form the product of $(1+v(q))$ over sieve primes up to $z^\lambda$ for a small fixed $\lambda>0$. The expected log of the selected divisor under normalized weights $v(d)$ is $\sum_{q\le z^\lambda}g(q)\log q\ll\lambda\log z$. At least half its weight belongs to divisors at most $z$ by Markov. The complement of $S$ away from $q_0$ has reciprocal sum $\kappa\log\log x+O(1)$ by the all-prime Mertens estimate. Since $g(q)=1/q+O(q^{-2})$, the product is therefore $\asymp(\log z/\log z_0)^\kappa$. This verifies sieve dimension $\kappa$ and the Mertens factor with the lower cutoff, even when the complement of $S$ is specified by its bounded-error harmonic sum. The weighted sieve bound is $O(Y(\log z_0/\log z)^\kappa+Y/(\log X)^B)$. Divide by $\log X$ to bound the number of primes, then add the square-divisibility error. A sum over the $O(\log\log N)$ offsets shows that violations of the zero conditions remove at most

```math
\ll \frac{Y}{\log N}\left(
\frac{(\log\log N)^{1+\kappa}}{(\log N)^\kappa}
+\frac{\log\log N}{\log N}\right)=o(Y/\log N).\tag{7}
```

**Far tail on the planted progression.** It remains to bound $E(p)=\sum_{j>J}c(n+j)2^{-j}$. For $J<j\le N$, let $h=j-j_0>0$. Then $n+j<3N$ and divisor pairing yields $\tau(bp+h)\le2\sum_{d\le2\sqrt N}\mathbf1_{d\mid(bp+h)}$. Put $g=\gcd(d,b)$. A solution requires $g\mid h$, and for such $g$ the reduced congruence is

```math
(b/g)p\equiv-h/g\pmod{d'},\qquad d'=d/g,\qquad (b/g,d')=1.
```

If its residue is a nonunit, any prime solution divides $d'$, which is impossible since $p>X>2\sqrt N$. For a unit residue use Montgomery–Vaughan's Brun–Titchmarsh inequality, which bounds the number of primes of a reduced class modulo $d'$ in an interval of length $Y>d'$ by $2Y/(\varphi(d')\log(Y/d'))$. For $d'=1$ the ordinary prime bound in the same theorem applies. We may count all primes, since we only need an upper bound for primes in the planted class. Choose $0<\eta<1-1/(2(a-\theta))$, possible by the choice of $\theta$. Then $2\sqrt N\le Y^{1-\eta}$ for large $N$, because $(a-\theta)(1-\eta)>1/2$ absorbs the fixed factor in $Y\gg_w N^{a-\theta}$ and the factor $2$. Thus $Y>d'$ and $\log(Y/d')\ge\eta\log Y\gg_{a,\theta}\log N$. This is the constraint for the divisor sum, and it follows from $\theta<a-1/2$. The earlier choice $1-\eta=6/7$ also works for fixed $a,\theta$ because $a-\theta>7/12$. [Montgomery and Vaughan, *The large sieve*, Mathematika **20** (1973), 119–134, Theorem 2, (1.10)][mv]

Summing over $g\mid h$ and then $d'$ gives

```math
\sum_{X<p\le X+Y}\tau(bp+h)\ll_{a,\theta} \tau(h)\frac{Y}{\log N}
\sum_{d'\le2\sqrt N}\frac1{\varphi(d')}\ll_{a,\theta}\tau(h)Y.
```

Here $\sum_{d\le t}1/\varphi(d)\ll\log(2t)$ follows from $d/\varphi(d)=\sum_{l\mid d}\mu(l)^2/\varphi(l)$ and convergence of $\sum_l\mu(l)^2/(l\varphi(l))$. For $j>N$, use $c(n+j)\le2N+j$ and at most $Y+1$ integer candidates for $p$. Since $\tau(j-j_0)\le j$ for $j>J$, the full tail over the planted primes is bounded by $O(Y(J+1)2^{-J}+YN2^{-N})$. Markov at threshold $2^{-k-2}$ discards $O_w(Y(\log\log N)(\log N)^{-10\log 2})=o(Y/\log N)$ primes. This bound and (7) are uniform in $m,H,j_0$.

**Counting distinct starts.** For each $m\in\mathcal M$ there remain $\gg Y/\log N$ good primes. At a good start, the head of $2^nL_f$ through index $n$ is integral. The raw tail is the midpoint in (6) plus $0\le E(p)<2^{-k-2}$. Since the midpoint is at distance $2^{-k-1}$ from either endpoint, the result lies inside the correct dyadic interval. At $u=2^k-1$ its value is less than $1-2^{-k-2}$, so there is no wrap around 1. The least positive raw offset with nonzero coefficient is $j_0$, which is determined by $n$ alone. This identifies $bp=n+j_0$. Its unique largest prime factor is $p>b$, so it also identifies $b$ and $m$. This proves injectivity of the good pairs even when the offsets vary. Summing over $m$ and using (5) gives $\#_w(N,H)\gg_{a,w}H(\log N)^{-\kappa}$ for every fixed word, including $0^k$.

## 5. Word frequencies and finite discrepancy

Combine Sections 2 and 4 for every fixed word containing a `1`. For $0^k$, the upper bound on the number of rejected starts came from the union bound in Section 2. At least all starts with first digit `1` are rejected, giving the matching lower bound. Thus

```math
\#_w(N,H)\asymp_{w,a}H(\log N)^{-\kappa}\quad(w\ne0^k),\qquad
\#_{0^k}(N,H)=H-\Theta_{k,a}(H(\log N)^{-\kappa}).
```

For prefix lower bounds use the window with $N=H=\lfloor M/2\rfloor$ inside $[0,M)$. The prefix upper bounds follow from (2), with an extra fixed number of shifts when necessary. In particular the one-frequency tends to zero. Every word occurs in each sufficiently late dyadic window, giving infinitely many occurrences and disjunctivity. A rational binary expansion is eventually periodic and cannot contain every finite word infinitely often, proving irrationality. Indeed, an eventual period of length $r$ gives at most $r$ distinct length-$k$ words from the periodic tail, whereas $2^k>r$ for large $k$.

**The finite transition bound.** Write $T_M=\#_{01}(0,M)+\#_{10}(0,M)$, including the transition starting at shift $M-1$, which uses digit $M+1$. This is exactly the count in $[1/4,3/4)$, so the sharp Lean inequality with the same half-open interval convention is

```math
D_M(L_f)\le\max(2/3,1-T_M/M)+1/M.\tag{8}
```

Thus $1-D_M\ge\min(1/3,T_M/M)-1/M$. We have $T_M\ll M(\log M)^{-\kappa}$, since each transition uses a 1 among the first $M+1$ digits and each such digit is used at most twice. The fixed word `01` gives $T_M\gg M(\log M)^{-\kappa}$. Consequently the eventual lower bound from (8) is $\gg(\log M)^{-\kappa}$, with $1/M$ absorbed. For the alternative finite inequality used by `logTwo_finite_discrepancy_gap`, the bound is $D_M\le\max(7/8,1-T_M/M)$ for $M\ge2$. Its eventual transition branch is the same and has no $1/M$ term. [Lean `sharp_finite_discrepancy`][sharp-lean] · [Lean `logTwo_finite_discrepancy_gap`][log-two-lean] · [Lean `discrepancy_le_transitions`][disc-lean]

**Upper bound on the gap.** Let $B_M$ be the number of ones in the first $M$ digits. For any positive integer $L$ the count outside $[0,2^{-L})$ is at most $L B_{M+L-1}$. This includes all right endpoints needed by the last start. Hence

```math
1-D_M(L_f)\le 2^{-L}+L B_{M+L-1}/M.\tag{9}
```

Taking $L=\lceil\kappa\log_2\log M\rceil$ gives $1-D_M\ll(\log\log M)(\log M)^{-\kappa}$ by (2), and in particular $D_M\to1$. This $L$ also balances the rate in the first term against the marginal cost $O((\log M)^{-\kappa})$ of increasing the length by one in (9).

**Matching lower bound on the gap.** We prove that the logarithmic factor in (9) is necessary for this class, even when all intervals are allowed. Set $N=H=\lfloor M/2\rfloor$ and $R=\lfloor(\kappa/2)\log_2\log M\rfloor$. Apply Section 4 with $w=1$ and the left extension $R$. This gives $\gg M(\log M)^{-\kappa}$ distinct good starts $t\in[N,N+H)$ whose planted midpoint is $3/4$ and whose tail satisfies $E(t)<1/8$. All raw coefficients at offsets $1-R\le j\le0$ from $t$ vanish. Hence at $t-r$ for $1\le r\le R$, shifting the raw tail multiplies it by $2^{-r}$ and only adds an integral head. Since the resulting value is in $[0,1)$, we have the exact relations

```math
x_t=3/4+E(t),\qquad
x_{t-r}=2^{-r}(3/4+E(t))\in[(3/4)2^{-R},1/2).
```

Every such $t$ has a first digit `1` and each of its preceding $R$ starts has a first digit `0`. Thus the sets of preceding starts for distinct $t$ are disjoint. They all lie in $[0,M)$ for large $M$. With $\varepsilon=2^{-R}/4$, they contribute at least a proportion $\Delta\gg R(\log M)^{-\kappa}$ in $[3\varepsilon,1/2)$. Here and below one can take $\Delta$ to be exactly the proportion of these marked starts. We have $\varepsilon\asymp(\log M)^{-\kappa/2}$ and also $\Delta=O(R(\log M)^{-\kappa})$, since each good $t$ has digit `1` and (2) bounds their number. In particular $\Delta=o(\varepsilon)$. By $x_n\le A(n)$ and (2), the set $[0,\varepsilon]$ contains at least a proportion $1-O((\log M)^{-\kappa}/\varepsilon)>1/2$ for large $M$.

For an arbitrary interval $I=[s,t)$ write $m(I)$ for its empirical proportion and $|I|$ for its length. The positive deviation $m(I)-|I|$ is at most $1-\Delta$ if $|I|\ge\varepsilon$. If $|I|<\varepsilon$, it cannot meet both $[0,\varepsilon]$ and $[3\varepsilon,1/2)$, so $m(I)\le1-\Delta$ again. For the negative deviation $|I|-m(I)$ the same bound holds if $|I|\le1-\varepsilon$. Otherwise $s<\varepsilon$ and $t>1-\varepsilon$, so $I$ contains $[3\varepsilon,1/2)$ and $m(I)\ge\Delta$. Taking the supremum proves the matching lower gap and yields

```math
1-D_M(L_f)\asymp\frac{\log\log M}{(\log M)^\kappa}.\tag{10}
```

In particular the best all-zero cylinder gives the same order. Its deficiency $2^{-L}+1-m([0,2^{-L}))$ is at least $\Delta$ for every $L$ by the positive-deviation argument, and (9) supplies the matching upper bound on the minimum. The resulting order comes with implicit multiplicative constants.

## 6. Audit of Phase 16, Theorems 3.2 and 3.3

Sections 2–5 give independent proofs with the following checks and corrections to the earlier note. [Phase 16, §3][phase16] · [Phase 13 audit of the Erdős–Borwein proof][phase13]

- **Theorem 3.2.** The support description follows directly from the local factors. The support and odd-part sums have distinct Euler products, with the constants obtained from Wirsing. The squarefull decomposition needs the large-squarefull-factor bound and the multiplicity estimate given in Section 2. The finite arrival identity needs a bound on the right extension of the source range before it can be used with Shiu. The polynomial bound on each distant column ensures summability, and nonnegativity justifies the exchange over levels. Markov gives the claimed digit upper bound and its extension to all the moving windows.
- **Prime input in Theorem 3.3.** The 1985 paper is *Invent. Math.* **79**, 1–9. The theorem is on p. 2 and uses $Q=x^{1/40}$ for $y=x^\nu$, $7/12<\nu\le1$. The 1984 paper reviewed in Phase 13 is a separate article, with the older lower-end range quoted there. The start and length maxima in (3), splitting with slack, and prime-power removal give (4). The fixed modulus is included in the range and the CRT applications use the full modulus $q_0d$. The overall word-count threshold depends on $a,\theta,w,q_0$ and the fixed arithmetic data. [Perelli, Pintz and Salerno, *Bombieri's theorem in short intervals*, Ann. Scuola Norm. Sup. Pisa (4) **11** (1984), 529–539, pp. 529–530][pps84]
- **Plant and sieve.** Equation (5) uses the harmonic sum with bounded error and verifies the reciprocal mass cutoff. The fixed factor $p_0^{2u}$ affects the constants in the lower bound for $p$. The sieve argument needs coprimality with both $q_0$ and $b$, exclusion of the primes dividing $h$, a separate square-divisibility count and a weighted remainder estimate. These are established in Section 4, which also shows why one saves a power of $\log N$ for every fixed $\kappa>0$.
- **Tail and endpoints.** The earlier exponent $6/7$ follows from the strict inequality $(a-\theta)6/7>1/2$. Section 4 verifies this step with the more general condition $(a-\theta)(1-\eta)>1/2$. The reduced modulus can have a nonunit residue, and the planted prime size rules out that case. Choosing $X$ with the offset $j_0-1$ gives the desired half-open set of integer starts. The integrality of the head, the two dyadic endpoints, the geometric tail and the largest-prime recovery then give distinct occurrences, including for the final cylinder abutting 1.
- **Zero word.** The planted-prime lower bound for a fixed $0^k$ holds, and its actual count is $H-\Theta(H(\log N)^{-\kappa})$. The order $\Theta(H(\log N)^{-\kappa})$ refers to words containing a `1` and to the zero-word deficit.

## 7. Transcendence and verification status

**Published transcendence input.** For a primitive odd character χ and $0<|q|<1$ algebraic, Hamieh and Murty's Theorem 1.1 at $k=1$ gives transcendence of $\sum_{n\ge1}(\sum_{d\mid n}\chi(d))q^n$. Taking $q=1/2$ proves transcendence of $L_\chi$, including $L_{\chi_4}$. In the latter case one also has the direct identity $1+4L_{\chi_4}=(\sum_{j\in\mathbb Z}2^{-j^2})^2$. The odd imprimitive case follows from the same authors' higher-level modular-form theorem. In detail, if χ is induced by χ* of conductor $q_*$ and $P$ is the product of primes dividing $q_0$ but not $q_*$, inclusion–exclusion gives

```math
\sum_{m\ge1}\frac{\chi(m)q^m}{1-q^m}
=\sum_{d\mid P}\mu(d)\chi^*(d)\sum_{m\ge1}\frac{\chi^*(m)q^{dm}}{1-q^{dm}}.
```

At $q=e^{2\pi i z}$ the right side, after adding its algebraic Eisenstein constant term, is a weight-one modular form on $\Gamma_1(q_*P)$ with algebraic Fourier coefficients. This follows from the primitive weight-one Eisenstein series with constant term $L(0,\chi^*)/2$ and the oldform maps $z\mapsto dz$, since $q_*d\mid q_*P$. Its first positive Fourier coefficient is 1, so the modular form is nonzero. Theorem 3.1 applied at $q=1/2$ gives a transcendental value, and subtraction of an algebraic constant preserves transcendence. For even characters the weight-one parity condition fails. The digit-count argument establishes irrationality for those characters and the general class, including the index-four example. Transcendence for those remaining cases is outside the conclusions established here. [Hamieh and Murty, *A note on q-analogues of Dirichlet L-functions*, Int. J. Number Theory **12** (2016), 765–773, Theorems 1.1 and 3.1][hamieh-murty] · [Diamond and Shurman, Theorem 4.8.1][diamond]

**Kernel-verified components.** The existing Lean library proves the finite displaced-source identity and the finite one-bit Markov transfer. It also proves both finite transition bounds quoted in Section 5. Natural finite extensions include the union bound with right endpoint $M+L-1$, the interval estimate for two separated subsets used in (10), the injectivity criterion from the first nonzero raw offset, and the backward carry certificate. These extensions and the infinite limit transfers are paper arguments here. Shiu, Wirsing, short-interval prime distribution and modular-form transcendence are external inputs. All estimates in the classification concern the actual prime and divisor sums. [Lean arrivals][arrivals-lean] · [Lean weighted Lambert identities][weighted-lean] · [Lean sharp discrepancy][sharp-lean]

**Finite computation.** Run the standard-library verifier from the repository root.

```sh
python -B scripts/phase17_multiplicative_lambert.py
```

It checks convolution and prime-power formulas, the two-square formula through 4,096, and the exact finite arrival reindexing against a separate raw-coefficient sum. For each example it certifies 132,096 digits by integer carries. At coefficient cutoff $K$, the omitted tail scaled by $2^K$ is between 0 and $K+2$ since $c(n)\le n$. The two endpoint carries agree by the last digit requested. The script evaluates several windows of length $\lceil N^{3/5}\rceil$, checks the finite transition and all-zero cylinder bounds, and reports both discrepancy scalings. Some short words have zero occurrences on these finite samples, which lie below the unspecified asymptotic threshold.

The discrepancy calculation replaces each $x_n$ with its certified 24-bit truncation. If $y_i$ are the sorted points of a sample of size $M$ with ranks $1\le i\le M$, the discrepancy is the range of the values $0$, $i/M-y_i$ and $(i-1)/M-y_i$, by taking values and one-sided limits of the empirical distribution function minus the identity. This also handles ties. Each sorted orbit point moves by a number in $[0,2^{-24})$ relative to the corresponding grid point. All these differences enter the range with the same sign before subtraction, so the discrepancy changes by at most $2^{-24}$. At $M=131{,}072$ the resulting gaps are approximately $0.594759$ for $\chi_4$ and $0.280708$ for the index-four example. These are finite measurements. [Verification script][script]

[phase16]: ../phase16/weighted-lambert.md#3-classification-of-integer-valued-signed-multiplicative-lambert-series
[phase13]: ../phase13/reviews/erdos-local-limit.md
[arrivals-lean]: ../../NormalityChecker/ErdosBorweinArrivals.lean
[weighted-lean]: ../../NormalityChecker/WeightedLambertIdentities.lean
[sharp-lean]: ../../NormalityChecker/SharpDiscrepancy.lean
[log-two-lean]: ../../NormalityChecker/LogTwoTransitions.lean
[disc-lean]: ../../NormalityChecker/BinaryDiscrepancy.lean
[script]: ../../scripts/phase17_multiplicative_lambert.py
[diamond]: https://doi.org/10.1007/978-0-387-27226-9
[wirsing]: https://doi.org/10.1007/BF01351892
[wirsing-scan]: https://manifests.sub.uni-goettingen.de/iiif/image/gdz:PPN235181684_0143:00000082/full/1100,/0/default.jpg
[berndt-moree]: https://archive.mpim-bonn.mpg.de/id/eprint/5134/1/mpim-preprint_2024-22.pdf
[shiu]: https://doi.org/10.1515/crll.1980.313.161
[shiu-scan]: https://manifests.sub.uni-goettingen.de/iiif/image/gdz:PPN243919689_0313:00000167/full/1100,/0/default.jpg
[huxley]: https://doi.org/10.1007/BF01418933
[pps84]: https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
[pps85]: https://doi.org/10.1007/BF01388653
[pps85-scan]: https://manifests.sub.uni-goettingen.de/iiif/image/gdz:PPN356556735_0079:00000008/full/1100,/0/default.jpg
[selberg-original]: https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1950.1/ICM1950.1.ocr.pdf
[selberg]: https://kskedlaya.org/ant/chap-selberg.html
[mv]: https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf
[hamieh-murty]: https://doi.org/10.1142/S1793042116500494
