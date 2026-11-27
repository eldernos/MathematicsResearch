# Dense character carries and theta series of quadratic orders

Fix an integer construction radix $b\ge2$. Write $F_b(a)=\sum_{n\ge1}a(n)b^{-n}$ and let $D_N(x;b)$ be the supremum of the absolute discrepancy of the first $N$ points $\{b^n x\}$, $0\le n<N$, over half-open subintervals of $[0,1)$. Write $D^-,D^+$ for its liminf and limsup, and $K_b=\{x:D_N(x;b)\to1\}$. All logarithms without a subscript are natural.

**Paper proof; numerical constants by Finite certificate (`scripts/phase23_dense_forms.py`). For cubic characters modulo seven, nine and thirteen, $L_+(2^k)$ is simply nonnormal in its construction radix $2^k$ for every $k\ge4$, and $L_-(2^k)$ for every $k\ge3$.** Both have strictly positive lower extreme discrepancy in those ranges. More generally (**Paper proof**), every nonzero integer projection of any cubic character divisor sum is simply nonnormal in all sufficiently large power-of-two construction radices, and its lower discrepancy tends to one as the radix exponent tends to infinity. Theorem 4A proves this by moving powers of the radix out of the coefficients *before* estimating the orbit.

**Paper proof.** For every nonzero integer projection of an odd-order $h>1$ character divisor sum, the *undisplaced signed tail* at a typical position has magnitude $(\log N)^{(\log2)/h+o(1)}$ in every fixed construction radix $b\ge2$. The absolute tail has the same normal order. Every fixed zero block of the coefficients has positive density, but a bounded nonzero coefficient followed by such a block has density zero.

**Paper proof.** For every positive definite integral binary quadratic form, primitive or imprimitive, §§4–5 give the leading constant of $1-D_N(\Theta_Q(1/b);b)$ in every construction radix $b\ge2$. At the primes dividing the conductor, an exact lattice identity reduces the problem to coefficients prime to the conductor of a lower order. In dyadic radices these lower orders can have different width laws. The discriminants $-92$ and $-108$ give explicit examples.

**Open.** Membership of the original $L_\pm(b)$ in $K_b$, the upper bound $D^+<1$, and positive lower frequency for every prescribed word remain unresolved. For the cubic characters modulo seven, nine and thirteen, simple normality of $L_+(b)$ for $b\in\{2,4,8\}$, of $L_-(b)$ for $b\in\{2,4\}$, and of $L_\pm(b)$ in every construction radix that is not a power of two remains open. The $k$-ranges above are those of the method; even with the exact constants $C_{\rm odd}$ the method does not reach $L_+$ at $k=3$ or $L_-$ at $k=2$. A bounded transformation of the coefficients has an exact digit law in §3.

## 1. Moments and normal order of the coefficients

Let $\chi$ be a Dirichlet character of odd order $h>1$ modulo $M$, extended by zero off the units. Set $c=1*\chi$. For $h=3$ use $\omega=e^{2\pi i/3}$ and write $c=x+y\omega$. The two integer sequences are $c_+=2x-y$ and $c_-=y$. Thus $F_b(c_\pm)=L_\pm(b)$ in construction radix $b$. For modulus seven we take $\chi(3)=\omega$, as in [GF-22, §§1–3](../phase22/odd-characters-and-kernel-quotient.md). The arguments also cover cubic characters modulo nine and thirteen.

### Absolute moments, including the leading factors

**Proposition 1 (Paper proof).** For $r>0$ define

```math
\kappa_h(r)=\frac1h\sum_{j=0}^{h-1}|1+e^{2\pi i j/h}|^r,\qquad
C_{\chi,r}=\frac1{\Gamma(\kappa_h(r))}
\prod_p\left[(1-p^{-1})^{\kappa_h(r)}
\sum_{e\ge0}\frac{|c(p^e)|^r}{p^e}\right].
```

In the product each prime contributes both factors, with primes in increasing order. Then $\sum_{n\le X}|c(n)|^r\sim C_{\chi,r}X(\log X)^{\kappa_h(r)-1}$. For $h=3$ the corresponding sums for $c_+$ and $c_-$ are asymptotic to the same expression multiplied respectively by $(2^r+2)/3$ and $2/3$. In particular their first absolute moments have exponent $1/3$, their second moments have exponent $1$, and the ratio of the $c_+$ sum to the $c_-$ sum tends to $2$ for $r=1$ and to $3$ for $r=2$. The signed first moments instead satisfy $\sum_{n\le X}c(n)=L(1,\chi)X+O_M(\sqrt X)$, by the hyperbola decomposition and bounded character partial sums.

*Proof.* Away from $M$ the value at $p$ is $1+\chi(p)$, and $|c(p^e)|\le e+1$. At primes dividing $M$ the local coefficients are all one. The Euler factors from prime powers of exponent at least two are absolutely summable near $s=1$. Expanding the function of $p\bmod M$ at the primes in Dirichlet characters factors the Dirichlet series into powers of their $L$-functions times a factor regular near one. The principal exponent is $\kappa_h(r)>0$. Selberg–Delange gives the displayed positive constant, with convergence of the ordered product by the prime number theorem in fixed progressions.

For a cubic character each nonzero local factor at a prime with $\chi(p)\ne0,1$ is $1$ or $e^{\pm i\pi/3}$. Hence on its support $c(n)=A(n)e^{i\pi t(n)/3}$ with $A(n)=\prod_{\chi(p)=1}(v_p(n)+1)$ and $t(n)\bmod6$ additive on coprime arguments. Fourier-expand the function of the phase in $|c_\pm|^r$. The $j$-th twist of $|c|^r$ has principal exponent $(2^r+2\cos(\pi j/3))/3$. For $1\le j\le5$ its real part is strictly below $\kappa_3(r)$. The same Selberg–Delange bound makes these twists lower order, including when the leading reciprocal gamma factor vanishes. The six values of $c_+/A$ are $(2,1,-1,-2,-1,1)$ and those of $c_-/A$ are $(0,1,1,0,-1,-1)$. Their averaged absolute powers give the two factors. This supplies the asymptotics behind the order bounds in GF-22. ∎

For general odd $h$, summing the cosines with their signs gives $\kappa_h(1)=2/(h\sin(\pi/(2h)))>1$, and summing $2+2\cos(2\pi j/h)$ gives $\kappa_h(2)=2$. Also $\prod_{j=0}^{h-1}(1+e^{2\pi i j/h})=2$, by evaluating $z^h-1$ at $-1$. Hence the typical exponent $(\log 2)/h$ and the first-mean exponent $\kappa_h(1)-1$ differ for every odd $h>1$ (including $h=3$ and the quintic character modulo eleven).

**Proposition 2 (Paper proof).** Put $\gamma_h=(\log2)/h$. On the support of $c$,

```math
\frac{\log|c(n)|}{\log\log X}\longrightarrow\gamma_h
\qquad\text{in probability for }n\text{ sampled uniformly up to }X.
```

For every nonzero additive $\Phi:\mathbb Z[\zeta_h]\to\mathbb Z$, its projection $a=\Phi(c)$ has positive lower support density, the same normal order on that support, and

```math
\sum_{n\le X}|a(n)|^r\asymp_{\chi,\Phi,r} X(\log X)^{\kappa_h(r)-1}\quad(r>0).
```

*Proof.* Apply Turán–Kubilius to the strongly additive function with weights $\log|1+\chi(p)|$ at $p\nmid M$. Its mean is $\gamma_h\log\log X+O(1)$ by the product identity, and its variance is $O_h(\log\log X)$. Higher prime powers change the logarithm on the support by a quantity bounded in probability. Indeed for $\chi(p)\ne0,1$ the nonzero geometric sums take only finitely many values, and for $\chi(p)=1$ the error is $O(\log(e+1))$ at $p^e\parallel n$, $e\ge2$. Their expected absolute total is bounded by a convergent sum over $p^e$. All squarefree integers belong to the support, so restriction to it preserves exceptional sets of relative size $o(1)$.

Every embedding of $\mathbb Q(\zeta_h)$ obeys the same upper normal-order and moment bounds. An additive $\Phi$ extends to a rational linear functional and is bounded by a constant times the maximum of the embedding magnitudes. Conversely $a(n)$ is divisible by $2^{m(n)}$, where $m(n)=\#\{p\parallel n:\chi(p)=1\}$. Another application of Turán–Kubilius gives $m(n)/\log\log X\to1/h$ in probability. On $a(n)\ne0$ this supplies the matching lower normal order.

For the support and moment lower bounds choose finitely many $d_i$, each $1$ or a prime, such that $c(d_i)$ span $\mathbb Q(\zeta_h)$ over $\mathbb Q$. This is possible since the values $1$ and $1+\zeta_h^j$ span, and Dirichlet's theorem supplies the primes. The functionals $z\mapsto\Phi(c(d_i)z)$ separate points: multiplication by a nonzero $z$ is invertible. Norm equivalence gives $|z|^r\ll\sum_i|\Phi(c(d_i)z)|^r$. Restrict to $n\le X/\max d_i$ coprime to all $d_i$. Then the terms on the right occur at $d_i n\le X$, with bounded multiplicity. Removing these finitely many primes in Proposition 1 preserves the exponent and a positive constant. Restricting instead to squarefree $n$ in this coprime set gives positive lower density for the support. ∎

The bounded-value obstruction also holds for a finite integer combination of periodic divisor weights $a(n)=\sum_{d\mid n}w(d)$, after taking a common period $M$. For $p\equiv1\bmod M$, $p\parallel n$, the two choices of $p$ in $d$ give equal summands. Thus $2^{\#\{p\parallel n:p\equiv1\bmod M\}}\mid a(n)$. This exponent tends to infinity in probability. For every fixed $A$, the density of $0<|a(n)|\le A$ is zero. Any such sequence with positive lower support density has divergent first absolute mean. Subtracting another periodic weight cannot give bounded absolute mean while retaining positive lower support density.

## 2. Cubic zero patterns and signed carries

### Exact joint densities of support indicators

For a cubic character put $\mathcal P=\{p:\chi(p)=\omega\text{ or }\omega^2\}$ and $n^\circ=n/\prod_{p\mid M}p^{v_p(n)}$. Let $s_\pm(n)=\mathbf1_{c_\pm(n)\ne0}$. At $p\in\mathcal P$ the forbidden exponents are $2\bmod3$. On the remaining support the phase satisfies $e^{2\pi i t(n)/3}=\chi(n^\circ)$ by the prime-power factors. Thus $s_+$ imposes just the forbidden-exponent conditions, and $s_-$ imposes in addition $\chi(n^\circ)\ne1$.

**Proposition 3 (Paper proof).** For a finite set $J$ of offsets the density that $s_\pm(n+j)=1$ for all $j\in J$ equals

```math
A_\pm(J)=R_\pm(J)\prod_{p\in\mathcal P}
\int_{\mathbb Z_p}\prod_{j\in J}
\mathbf1_{v_p(z+j)\not\equiv2\bmod3}\,dz .
```

Here $dz$ is Haar probability, $R_+(J)=1$, and $R_-(J)$ is the Haar probability on $\prod_{p\mid M}\mathbb Z_p$ that $\chi((z+j)^\circ)\ne1$ for all $j$. The latter uses the unit residue modulo $M$ after stripping all its prime divisors. Values at a zero local coordinate are immaterial. For disjoint sets $J,Z$ prescribing ones and zeros respectively, the density is $\sum_{T\subseteq Z}(-1)^{|T|}A_\pm(J\cup T)$.

*Proof.* Truncate the primes at $P$ and the valuations at $E$. All remaining conditions, including the unit residue, can be evaluated in a finite residue ring (allow the extra prime powers in $M$ when stripping). The Chinese remainder theorem gives the product. Errors for large $p$ have upper density at most $|J|\sum_{p>P}p^{-2}$, by counting $p^2\mid n+j$ for each fixed shift. The finitely many remaining valuation tails have upper density at most $|J|\sum_{p\le P\text{ or }p\mid M}p^{-E}$. Taking the limits proves the formula and inclusion–exclusion. ∎

In particular $\delta=A_+(\{0\})=\prod_{p\in\mathcal P}(1-1/(p^2+p+1))$ and $A_-(\{0\})=2\delta/3$. For the cubic character modulo seven, letting $P_2=\prod_{p\in\mathcal P}(1-2/(p^2+p+1))$, the consecutive-one densities are $P_2$ and $3P_2/7$ respectively. At a bad prime two consecutive integers cannot both be divisible by $p^2$. At seven, the allowed consecutive unit pairs start at residues $2,3,4$; if either entry is divisible by seven its neighbor is $\pm1\bmod7$ and fails.

Every fixed string of $R$ zeros has positive density. Choose distinct $p_j\in\mathcal P$ larger than $R$ and impose $n+j\equiv p_j^2\bmod p_j^3$ for $1\le j\le R$. One can also require a one at $n$: these conditions make $n$ a unit at each $p_j$, the unprescribed primes leave a positive convergent product, and the modulus primes allow a unit residue with $\chi(n)\ne1$. Either choice of $s_\pm$ works. Requiring in addition $0<|c_\pm(n)|\le A$ changes the density to **zero** for each fixed $A$.

The density $q_R$ of an all-zero block tends to zero as $R\to\infty$. Indeed Proposition 3 realizes the block laws by translation $z\mapsto z+1$ on the profinite integers with Haar probability. This translation is ergodic (the integers are dense, or use Fourier characters). The set where $s_\pm=1$ has positive Haar measure, so almost every forward orbit hits it. Continuity of probability from above proves the assertion. In particular a block length tending arbitrarily slowly to infinity gives zero upper density, by comparison with each fixed $R$.

### A normal order for the actual signed carry

**Theorem 4 (Paper proof).** Fix a cubic character, either $a=c_+$ or $a=c_-$, and an integer construction radix $b\ge2$. With $n$ uniform on $1,\ldots,X$, write

```math
T_n=\sum_{j\ge1}a(n+j)b^{-j},\qquad B_n=\sum_{j\ge1}|a(n+j)|b^{-j},\qquad
\gamma=\frac{\log 2}{3}.
```

Then $\log(1+|T_n|)/\log\log X$ and $\log(1+B_n)/\log\log X$ both converge in probability to $\gamma$. The same holds for $|\lfloor T_n\rfloor|$ in place of $|T_n|$. In particular, for fixed $A,L$, indices with $|T_{n+L}|\le A$ have density zero, even if one also prescribes a preceding zero block. This improves the heuristic on small signed tails in [GF-22, §6](../phase22/odd-characters-and-kernel-quotient.md).

*Upper bound.* For $0<r\le1$, $B_n^r\le\sum_{j\ge1}|a(n+j)|^r b^{-jr}$. The average over $n\le X$ is $O_{r,b}((\log X)^{(2^r-1)/3})$ by Proposition 1 (bound $j\le X$ by the moment up to $2X$ and the rest by the divisor bound). As $r\downarrow0$, $(2^r-1)/(3r)\to\gamma$. Markov therefore excludes $B_n>(\log X)^{\gamma+\varepsilon}$ outside $o(X)$ indices. At $r=1$ the mean of the absolute tail beyond a fixed $L$ is in fact asymptotic to $b^{-L}/(b-1)$ times the first absolute coefficient mean. This follows first for finite shift sums, then by a uniform geometric-tail bound from the same argument.

*Separation of valuations in a fixed window.* Write $\omega_1(n)=\sum_{\chi(p)=1,\ p\mid n}1$. On $a(n)\ne0$, $v_2(a(n))=\omega_1(n)+O_{\mathbb P}(1)$: the phase contributes at most one and the corrections from $p^e$, $e\ge2$, have bounded expected absolute sum. For any distinct fixed shifts $i,j$,

```math
\frac{\omega_1(n+i)-\omega_1(n+j)}{\sqrt{(2/3)\log\log X}}\ \Longrightarrow\ {\cal N}(0,1).
```

Here is a proof that avoids any independence assumption about neighboring integers. Truncate at $y=X^{1/\log\log X}$. At $p\le y$, $\chi(p)=1$, $p\nmid i-j$, residues $-i,-j$ contribute $+1,-1$ respectively, each with probability $1/p$ in the uniform residue model. Ignore the finitely many divisors of $i-j$. For every fixed moment degree $k$, expanding the truncated sum and counting residue intersections by CRT differs from the independent-prime model in the unnormalized moment by $O_k((2y)^k/X)=o(1)$. The model has variance $2\sum_{p\le y,\chi(p)=1}1/p\sim(2/3)\log\log X$. Its bounded centered summands have Gaussian normalized moments: paired terms give the Gaussian moments, blocks of multiplicity at least three contribute lower powers of the variance. The expected omitted prime count is $O(\log\log\log X+1)=o(\sqrt{\log\log X})$ by Mertens in progressions (the floor errors are $O(1)$). This proves the claim by moments and Markov. Consequently the probability that two *nonzero* coefficients in any fixed window have valuations within any fixed distance is $o(1)$. Each nonzero coefficient there also has valuation at least $(1/3-\eta)\log\log X$ off $o(X)$ indices, by Proposition 2's prime-count argument.

*Lower bound with signs.* Fix $0<\varepsilon<\gamma$ and call a position small if $|T_n|\le(\log X)^{\gamma-\varepsilon}$. For fixed $H$ the exact recurrence gives, for $1\le d\le H$,

```math
b^d T_n-T_{n+d}=\sum_{i=1}^d b^{d-i}a(n+i).
```

Outside $o(X)$ starting positions, all nonzero terms on the right have distinct $2$-adic valuations (allow the fixed offsets up to $Hv_2(b)$). If any term is nonzero the sum has the unique minimum valuation. Its absolute value is at least $2^{(1/3-\eta)\log\log X}$, which exceeds $(b^H+1)(\log X)^{\gamma-\varepsilon}$ for $\eta\log2<\varepsilon$ and large $X$. Hence two small endpoints in this window force *every* intervening coefficient to vanish.

Fix $R<H$ and exclude starting positions with no nonzero coefficient in the next $R$ places, of density $q_R$. In each block of $H$ positions, any two remaining small, nonexceptional positions differ by less than $R$: otherwise the earlier one has a nonzero intervening coefficient. Their upper density is at most $R/H$. The full small-set upper density is at most $q_R+R/H$. First let $H\to\infty$, then $R\to\infty$. This proves the lower bound. Since $|T_n|\le B_n$ and $|\lfloor T_n\rfloor-T_n|<1$, all three assertions follow. ∎

The integer head gives $\{b^n L_\pm(b)\}=\{T_n\}$ in its construction radix $b$. Theorem 4 controls size on the real line. Estimating these fractional parts requires information at unit scale. In particular, even a positive density of one specified interior digit would be compatible with concentration at its corresponding fixed point $j/(b-1)$; to bound $D^+$ away from one it suffices to exhibit positive lower mass in two intervals at positive distance on $\mathbb R/\mathbb Z$ (not merely separated in $[0,1)$, since $[0,\varepsilon)$ and $[1-\varepsilon,1)$ are adjacent on the circle and compatible with concentration at $\mathbb Z$).

### Simple nonnormality in dyadic construction radices

**Theorem 4A (Paper proof; numerical upper bounds on $C_{\rm odd}$ by Finite certificate).** Let $\chi$ be any cubic character, $a(n)=\Phi(c(n))$ with $\Phi:\mathbb Z[\omega]\to\mathbb Z$ nonzero and additive, and $b=2^k$, $k\ge1$. Define $\operatorname{odd}(m)$ as the positive odd part of $|m|$ for $m\ne0$, and set $\operatorname{odd}(0)=0$. Put

```math
C_{\rm odd}=\delta\prod_{\chi(p)=1}
\left[(1-p^{-1})\sum_{e\ge0}\frac{\operatorname{odd}(e+1)}{p^e}\right],
\qquad
C_\Phi=C_{\rm odd}\frac16\sum_{s=0}^5\operatorname{odd}\bigl(\Phi(e^{i\pi s/3})\bigr).
```

Writing $\|x\|$ for distance to the nearest integer, the original value $z=F_{2^k}(a)$ satisfies

```math
\limsup_{N\to\infty}\frac1N\sum_{j=0}^{N-1}\|b^j z\|
\le\frac{C_\Phi}{k},\qquad
D^-(z;b)\ge\max\{0,\,1-2\sqrt{C_\Phi/k}\}.
```

If $C_\Phi/k<1/4-1/(2b)$, $z$ is simply nonnormal in its construction radix $b$. More precisely, if $f_{d,N}$ is the frequency of digit $d$ among the first $N$ digits, then

```math
\limsup_{N\to\infty}\sum_{d=0}^{b-1}\frac{\min(d,b-1-d)}b f_{d,N}
\le C_\Phi/k .
```

For $a=c_+,c_-$ respectively, $C_\Phi=C_{\rm odd},2C_{\rm odd}/3$. By the finite certificate of §6, modulo seven $C_{\rm odd}<4/5$, and modulo nine and thirteen $C_{\rm odd}<21/25$. For *every* fixed cubic character and nonzero projection (**Paper proof**), $\lim_{k\to\infty}D^-(F_{2^k}(a);2^k)=1$. Each term in this last limit has its own constructed value and radix.

*Weighted residue law.* On the support of $c$, let $A$ and $t$ be as in Proposition 1, and write $\nu=v_2(A)$. Give $n$ weight $w(n)=\mathbf1_{c(n)\ne0}\operatorname{odd}(A(n))$. This is nonnegative and multiplicative. Its mean tends to $C_{\rm odd}$, since $w(p)=1$ for every prime and the higher powers have summable excess. Under these weights, $(\nu\bmod k,t\bmod6)$ is asymptotically uniform on the product of the two cyclic groups. Indeed the twist by $e^{2\pi i u\nu/k+i\pi jt/3}$ has principal prime exponent

```math
\frac{e^{2\pi i u/k}+2\cos(\pi j/3)}3 .
```

Only the trivial twist has real part one. As in Proposition 1, Selberg–Delange and finite Fourier inversion give limiting weight $C_{\rm odd}/(6k)$ per pair. Define the radix-reduced $U(n)=a(n)b^{-\lfloor v_2(a(n))/k\rfloor}$ when $a(n)\ne0$, and put $U(n)=0$ otherwise. On a nonzero phase $s$, its absolute value is $w(n)\operatorname{odd}(\Phi(e^{i\pi s/3}))$ times $2^{(\nu+v_2(\Phi(e^{i\pi s/3})))\bmod k}$. A fixed phase offset permutes the residues, and $\sum_{r=0}^{k-1}2^r=b-1$. Consequently the ordinary first absolute mean of the *reduced* coefficients converges exactly to $(b-1)C_\Phi/k$.

*Orbit bound.* A nonzero reduced coefficient contributes at position $l(n)=n-\lfloor v_2(a(n))/k\rfloor$, where $a(n)b^{-n}=U(n)b^{-l(n)}$. For each $j$, arrivals with $l(n)\le j$ are integral after multiplication by $b^j$. Others give

```math
\|b^jz\|\le\sum_{l(n)>j}|U(n)|b^{j-l(n)}.
```

Average over $0\le j<N$. A single arrival costs at most $|U(n)|/(b-1)$ in the sum, irrespective of collisions or sign. Take $n\le N+H$, $H=\lceil3\log_b(2N)\rceil$; the added $H$ terms in the first absolute mean cost $o(N)$ since $|U(n)|\le|a(n)|\ll_\Phi\tau(n)$. For $n>N+H$ the contribution, summed over $j<N$, is at most $\sum_{n>N+H}|a(n)|b^{N-n}/(b-1)=o(1)$ by the same bound. Dividing by $N$ yields $C_\Phi/k$.

*Discrepancy and digits.* For the empirical orbit measure $\mu_N$, the identity $\int\|x\|d\mu_N=\int_0^{1/2}\mu_N([t,1-t))dt$ and the definition of $D_N$ give

```math
\int\|x\|d\mu_N\ \ge\int_0^{1/2}(1-2t-D_N)_+\,dt=(1-D_N)^2/4 .
```

On the cylinder with first digit $d$, the distance to an integer is at least $\min(d,b-1-d)/b$. Uniform digit frequencies would therefore force limiting lower mean distance at least $1/4-1/(2b)$, by summing these minima for the even radix $b$. For all three moduli, the plus component at $k=4$ satisfies $C_\Phi/k<(21/25)/4<1/4-1/32$, and the minus component at $k=3$ satisfies $C_\Phi/k<(14/25)/3<1/4-1/16$. The left sides decrease and the thresholds increase thereafter. This proves the claims. ∎

**Rate across construction radices (Paper proof).** For $k\ge3$ one also has

```math
1-D^-(F_{2^k}(a);2^k)\ \le\ \frac2k+\frac{e C_\Phi\log k}{k\log2}.
```

Indeed replace the odd-part weight by its $s$-th power, $0<s\le1$. Its values at primes and all the Fourier exponents in the weighted residue law stay the same. If $C_\Phi(s)$ is the limiting average of $\operatorname{odd}(a)^s$, then $C_\Phi(s)\le C_\Phi$. The average of $|U|^s$ tends to $C_\Phi(s)(b^s-1)/(k(2^s-1))$ by summing $2^{rs}$ over the residues. Subadditivity of the $s$-th power and the geometric sum over arrival positions give an orbit $s$-moment limsup at most $C_\Phi(s)/(k(2^s-1))$. The truncation argument is the same with $H=\lceil(3/s)\log_b(2N)\rceil$. Choose $s=1/\log k$ for this fixed $k$. The limsup mass of $[1/k,1-1/k)$ is at most $k^s C_\Phi/(k(2^s-1))\le e C_\Phi\log k/(k\log2)$. Subtract from the length of that interval. The prefix limit is taken first for each radix, so no uniform Selberg–Delange error is required.

The odd-part mechanism uses a specific property of cubic characters: at a nontrivial prime value, $|1+\chi(p)|=1$. For odd $h\ge5$ these $h-1$ moduli have product one but are unequal, so their arithmetic mean is strictly greater than one. Removing only the scalar factor $2$ from first-power primes with $\chi(p)=1$ leaves an archimedean absolute first-moment exponent $\kappa_h(1)-1-1/h>0$ (apply the Euler-product argument to $|c(n)|/2^{\#\{p\parallel n:\chi(p)=1\}}$). This calculation does not decide the dyadic digit law of higher-order projections.

### Higher odd orders, including the quintic character modulo eleven

**Proposition 4B (Paper proof).** For odd $h>1$ and any nonzero additive projection $a=\Phi(c)$, all finite zero/nonzero coefficient patterns have natural densities. Put $o_p=\operatorname{ord}\chi(p)$ at $p\nmid M$ and

```math
\delta_h=\prod_{p\nmid M,\ o_p>1}\left(1-\frac{p-1}{p^{o_p}-1}\right).
```

The density of $a\ne0$ is either $\delta_h$ or $(1-1/h)\delta_h$. Which one occurs is determined by the trace test below. For every fixed construction radix $b\ge2$, Theorem 4's signed-tail and absolute-tail normal orders hold for $a$ with exponent $\gamma_h=(\log2)/h$. Every bounded nonzero coefficient pattern has density zero if it requires even one bounded nonzero entry.

*Proof.* Put $E=\mathbb Q(\zeta_h)$ and $E^+=E\cap\mathbb R$. Write $\Phi(z)=\operatorname{Tr}_{E/\mathbb Q}(\beta z)$ by nondegeneracy of the trace pairing. The nonzero $\beta\in E$ incorporates the chosen integral functional. Pairing complementary divisors in each local geometric sum gives $\overline c=\overline{\chi(n^\circ)}c$. There is a unique $u\in\mu_h$ with $u^2=\chi(n^\circ)$ since $h$ is odd. Then $y=c/u\in E^+$, and

```math
a(n)=\operatorname{Tr}_{E^+/\mathbb Q}(A_u y),
\qquad A_u=\beta u+\overline{\beta u}.
```

At most one phase $u$ has $A_u=0$, since it must satisfy $u^2=-\bar\beta/\beta$. Call a site admissible if no nontrivial $o_p$ divides $v_p(n)+1$ and $A_u\ne0$. Outside these sites $a(n)=0$ exactly. At admissible sites each of the real embeddings in the trace has a nonzero multiplier from a fixed finite set.

To control possible trace cancellation, for each embedding of $E^+$ choose a lift $\sigma$ to $E$. Define $g_\sigma(p)=\log|1+\sigma\chi(p)|$ for $p\nmid M$ and zero for other primes. At each fixed shift $i$ on the complex support, $\log|\sigma c(n+i)|$ differs from $\sum_{p\mid n+i}g_\sigma(p)$ by $O_{\mathbb P}(1)$ as in Proposition 2. For different pairs $(i,\sigma),(j,\tau)$ the difference of the two prime sums, divided by $\sqrt{\log\log X}$, has a centered Gaussian limit of positive variance. To verify this, repeat the truncated-prime moment argument of Theorem 4 with bounded real prime weights. The mean difference is $O(1)$ by the progression prime sums. For different shifts the two residues are disjoint at $p\nmid i-j$, giving variance contribution $(g_\sigma(p)^2+g_\tau(p)^2)/p+O_h(p^{-2})$, positive in aggregate already at $\chi(p)=1$. For equal shifts the contribution is $(g_\sigma(p)-g_\tau(p))^2(1/p-1/p^2)$. At primes with $\chi(p)=\zeta_h$ the two absolute cosines differ: the two lifts are distinct modulo complex conjugation. In both cases Mertens in progressions gives a positive variance constant. The bounded centered summands and CRT moment error give the Gaussian limit exactly as above.

It follows that in any fixed window the logarithmic magnitudes belonging to admissible sites and their individual real embeddings are pairwise separated by more than any prescribed *fixed* constant, off $o(X)$ starting indices. Their sizes are all at least $(\log X)^{\gamma_h-\varepsilon}$ there, with an exceptional set of size $o(X)$, by Proposition 2 applied to every embedding. Choose the separation constant large enough to absorb the finitely many nonzero factors $\sigma(A_u)$, the weights $b^{d-i}$ for $d\le H$, and twice the number of terms. In the sum for $b^dT_n-T_{n+d}$, if there is any admissible site, the largest real term then exceeds twice the sum of the absolute values of all the others (the one-term case is immediate). In particular the absolute sum is bounded below by a fixed positive multiple of $(\log X)^{\gamma_h-\varepsilon}$. Taking a single site also shows that accidental trace zeros have density zero among admissible sites.

Consequently the indicator of $a\ne0$ agrees up to a density-zero set with the admissibility indicator. Proposition 3's CRT formula applies with forbidden exponents $-1\bmod o_p$ and with the conductor factor requiring $A_u\ne0$. For one site the probability of a forbidden exponent is $(p-1)/(p^{o_p}-1)$, and the stripped unit is uniform modulo $M$ (condition on the valuations at $p\mid M$). This gives the claimed two support densities and all finite patterns by inclusion–exclusion. Fixed zero blocks have positive density by prescribing $v_{p_j}(n+j)=o_{p_j}-1$ at distinct primes, while their densities tend to zero with the length by the same ergodic argument. The block packing in Theorem 4 now gives the signed-tail lower normal order (use $\varepsilon/2$ for the individual terms). For the upper bound use Proposition 2 and $\kappa_h'(0)=\gamma_h$ in the fractional-moment argument. ∎

## 3. A bounded transformation with exact digit statistics

**Corollary 5 (Paper proof).** Form $Z_\pm(b)=F_b(s_\pm)$ from the support indicators, for each fixed construction radix $b\ge2$. Every base-$b$ word has a frequency in $Z_\pm(b)$. For words using digits zero and one it is the inclusion–exclusion formula of Proposition 3, with the positions of the ones and zeros as specified. Words containing other digits have frequency zero. The digit one has frequency $\delta$ or $2\delta/3$. In modulus seven both transformations are simply nonnormal in every construction radix, and

```math
0< D^-(Z_\pm(b);b)=D^+(Z_\pm(b);b)<1 .
```

*Proof.* No digit carry occurs; the positive densities of zeros and ones exclude ambiguous terminating expansions. The digit frequencies give $D^-\ge|A_\pm(\{0\})-1/b|$. For modulus seven the exact product bounds in §6 give $\delta>3/4$, so either frequency exceeds $1/2$. To obtain convergence, push the ergodic Haar coding of §2 to one-sided digit sequences. Its shift-invariant measure has no atoms: an atom under an invariant ergodic measure forces a finite periodic orbit, incompatible with positive one frequency and positive frequencies of arbitrarily long zero blocks. The radix evaluation has fibers of size at most two, so its measure on $[0,1]$ is also nonatomic. The cylinder frequencies imply weak convergence of the empirical orbit measures, hence uniform convergence of their interval distribution functions to this continuous limit. The extreme discrepancy therefore converges. A nonatomic probability has limiting discrepancy strictly less than one: an interval of vanishing length has uniformly vanishing mass, and the complementary-interval statement follows likewise. ∎

This law concerns a new real number in each radix. Applying the nonlinear support indicator changes the coefficients of $L_\pm(b)$.

## 4. The conductor in the theta discrepancy constant

Let $K$ be imaginary quadratic of fundamental discriminant $D$, let $\mathcal O_f=\mathbb Z+f\mathcal O_K$ and let $G_f=\operatorname{Pic}(\mathcal O_f)$ be its proper invertible ideal class group. For a primitive positive definite integral form $Q$ of discriminant $f^2D$ put $r_Q(n)=\#\{(x,y)\in\mathbb Z^2:Q(x,y)=n\}$ and $\Theta_Q(z)=\sum_{n\ge0}r_Q(n)z^n$. Write $C_K$ for the support constant of the total ideal-norm count $1*\chi_D$ in the maximal order ($v_p(n)$ even at inert primes). The constant $C_Q$ counts distinct represented integers: $S_Q(X)\sim C_Q X/\sqrt{\log X}$.

### Exact descent of representation numbers

**Lemma 6 (Paper proof).** For $g\mid f$ let $Q_g$ be the form in the class obtained by extension from $\mathcal O_f$ to $\mathcal O_g$, so $Q_f=Q$ up to proper equivalence. For $p^a\parallel f$, a represented $n$ must have $e=v_p(n)$ either even below $2a$, or at least $2a$. More precisely, set

```math
d=\prod_{p^a\parallel f}p^{\min(a,\lfloor v_p(n)/2\rfloor)},\qquad
g=f/d,\qquad m=n/d^2 .
```

If $(m,g)>1$, then $r_Q(n)=0$. Otherwise $r_Q(n)=r_{Q_g}(m)$. The supported indices are consequently the disjoint union over $d\mid f$ of $n=d^2m$ with $(m,f/d)=1$ and $r_{Q_{f/d}}(m)>0$. This is equality of lattice counts, with all unit multiples included.

*Proof.* Represent $Q$ by $N_{K/\mathbb Q}(\alpha)/N(I)$ on an integral proper invertible $\mathcal O_f$-ideal $I$ prime to $f$. The ideal–form correspondence permits this representative in every class. Write $I_g=I\mathcal O_g$; its index relative to $\mathcal O_g$ equals $N(I)$, by localization. At $p^a\parallel f$ the lattice $I_p$ is $R_a=\mathbb Z_p+p^a\mathcal O_{K,p}$. If $\alpha\in R_a$ has maximal-order $p$-content $t<a$, then $\alpha/p^t$ is a scalar unit modulo $p$ and has unit norm, also when $p$ splits or ramifies. Thus $v_p(N\alpha)=2t$. For $0\le t\le a$ the sublattice in $R_a$ with norm divisible by $p^{2t}$ is exactly $p^tR_{a-t}$: elements of content below $t$ have just been excluded, and $R_a\cap p^t\mathcal O_{K,p}=p^tR_{a-t}$. Away from $p$, division by $p^t$ is a lattice automorphism. Combining the local identities, $\alpha\mapsto\alpha/d$ identifies the vectors of norm $nN(I)$ in $I$ with those of norm $mN(I_g)$ in $I_g$ when the residual exponents at $p\mid g$ vanish. A residual exponent one at such a prime is impossible by the unit-norm observation. Conversely a coprime residual index determines its unique $d$. ∎

For comparison the exact **class-summed ideal Euler factor** at $p^a\parallel f$, with $\xi=\chi_D(p)$ and variable $z$ marking the norm exponent, is

```math
\sum_{t=0}^{a-1}p^t z^{2t}
 +p^{a-1}(p-\xi)\frac{z^{2a}}{(1-z)(1-\xi z)} .
```

Indeed invertible integral local ideals are generated by integral non-zero-divisors modulo $R_a^\times$. In the part of content $t<a$, the index $[R_{a-t}^\times:R_a^\times]=p^t$ counts the unit choices. In content at least $a$, divide by $p^a$, choose an integral maximal-order ideal and lift a generator in $[\mathcal O_{K,p}^\times:R_a^\times]=p^{a-1}(p-\xi)$ ways. These indices follow by reducing units modulo $p^a$: in the split, inert and ramified cases the unit proportions in $\mathcal O_{K,p}$ are $(1-1/p)^2$, $1-1/p^2$, and $1-1/p$. The maximal-order ideal factor is the displayed denominator. Equivalently the coefficient at $z^e$ is $\sum_{[Q]}r_Q(p^e)/|\mathcal O_f^\times|$. Using this scalar factor for an individual class would discard the class change in Lemma 6.

### Prime-to-conductor input

Put $e_g=|G_g/G_g^2|$ and define

```math
B_g=\frac{C_K}{e_g}\prod_{p\mid g}u_p,\qquad
u_p=\begin{cases}1-p^{-2}&\chi_D(p)=-1,\\1-p^{-1}&\chi_D(p)=0,1.\end{cases}
```

For each split prime $p\nmid g$ let $c_p$ be the odd component of the class of one of the two primes over $p$ in $G_g$. Independently take $E_p$ with $\mathbb P(E_p=j)=(1-1/p)p^{-j}$, $j\ge0$. Start with all characters $\psi$ of the odd part of $G_g$. At $p$ discard $\psi$ if $\psi(c_p)\ne1$ and $\operatorname{ord}(\psi(c_p))$ divides $E_p+1$. Write $d_g^*$ for the largest order left and put $\eta_g=\mathbb E[1-1/d_g^*]$. The trivial character always remains. Orientation of $c_p$ is immaterial, and discarding requires $E_p\ge2$.

**Lemma 7 (Paper proof).** On $(m,g)=1$, the support count for $Q_g$ is asymptotic to $B_g X/\sqrt{\log X}$. On this support $\log r_{Q_g}(m)/\log\log X\to(\log2)/2$ in probability, each odd prime valuation $v_q(r_{Q_g}(m))$ is tight, and $v_2(r_{Q_g}(m))/\log\log X$ has limiting law $1/(2d_g^*)$. The normalized logarithms of the coefficients are uniformly integrable.

*Proof.* Here is how the [GF-21 class-group argument, §§2.1–2.5](../phase22/radix-thresholds-and-class-groups.md) applies. Invertible ideals prime to $g$ correspond under extension and contraction to maximal-order ideals prime to $g$, with their classes recorded in $G_g$. Thus at $m$ coprime to $g$ we have $r_{Q_g}=|\mathcal O_g^\times|[C]X_m$ (use the inverse class if that is the ideal–form convention). The coefficient is unchanged by inversion. At split $p^j$ the local group-ring factor is $\sum_{i=0}^j[c_p']^{2i-j}$ with $c_p'\in G_g$ the full prime class; at ramified primes it is the $j$-th power of the ramified class, and at inert primes it is $\mathbf1_{2\mid j}$. This is the precise range where the unmodified group-ring identity holds.

The character $L$-functions on these ideals are finite-order Hecke $L$-functions of $K$ (ring class characters of conductor dividing $g$), with the Euler factors at $p\mid g$ omitted. Ring class field Chebotarev gives density $|A|/(2|G_g|)$ for split rational primes in an inverse-stable set $A\subseteq G_g$. In particular all class pairs have positive prime density. To track their multiplicities modulo any fixed integer, twist the split prime factors by roots of unity $z_{\{c,c^{-1}\}}$. The principal exponent of the resulting Dirichlet series is $\sum_{c\in G_g}z_{\{c,c^{-1}\}}/(2|G_g|)$, by character expansion on $G_g$. The other factors are powers of these Hecke $L$-functions, regular and nonzero at one for nontrivial characters, times the regular prime-power correction. The real exponent drops below $1/2$ unless every twist is one. Selberg–Delange and finite Fourier inversion therefore give the multiplicity equidistribution of GF-21 Lemma 2.7, after fixing a local pattern at the primes $\le P_0$ with $P_0\ge\max\{p:p\mid D\}$ (so that every ramified prime of $K$ not dividing $g$ is recorded in the pattern; conductor primes are excluded by $(m,g)=1$) and excluding large split squares as there. With all ramified primes thus fixed by the pattern, conditioning on the genus imposes precisely the compatible parity coset. Removing the finitely many conductor primes throughout changes no singular exponent.

The total coprime norm support has constant $C_K\prod_{p\mid g}u_p$ by deleting its Euler factors. The genus is asymptotically uniform, also under fixed local conditions, by the preceding twists. Almost all integers in a given genus hit every class there: for each non-genus character $\psi$ the ratio of its eigenvalue to the total coefficient is bounded by $\theta^{\nu}$ with $\theta<1$, where $\nu$ counts exactly dividing split primes on which $\psi^2$ is nontrivial. Such primes have positive density, and the usual multiplicative Rankin bound on this support makes $\nu\gg\log\log X$ outside a set of relative density $o(1)$. Thus Fourier inversion gives the total ideal coefficient divided by $|G_g^2|$ with relative error $o(1)$ in that genus. This proves the support constant and the logarithmic size assertion, since the number of split prime divisors is $(1/2+o(1))\log\log X$ on the norm support and higher split powers give a tight correction. These last bounds follow by multiplying split prime factors by $z^{\mathbf1_{p\mid m}}$ near $z=1$ and by truncation of the square divisors, just as in GF-21.

For clarity, the valuation steps use two further consequences of this same prime-input verification. Characters nontrivial on the square of the $2$-part are annihilated with relative probability tending to one by an exactly dividing split prime with character value $\pm i$. For the remaining odd characters, a nontrivial $p$-value is killed just at the exponents in the definition of $d_g^*$. The finite-dimensional laws of the exponents at split $p\nmid g$ are the independent geometric laws above, even within a genus, by the local factors in the twisted series. Truncating large square divisors costs $o_{P\to\infty}(1)$ on the norm support: for $P<p\le X^{1/4}$ use $S_K(X/p^2)\ll X/(p^2\sqrt{\log X})$, and for $p>X^{1/4}$ use the trivial bound $X/p^2$. This also controls the genus-restricted exceptional set.

GF-21 Proposition 2.10 now applies with $G=G_g$: after the finite pattern (with $P_0\ge\max\{p:p\mid D\}$) is fixed, the $2$-valuation differs by a tight error from the minimum count of exactly dividing split primes in a surviving odd character's kernel. Its inputs are the group-ring factors, the multiplicity equidistribution just verified, and the finite-group Strassmann Lemmas 2.8–2.9, combined only through the common finite modulus of GF-21 Lemma 2.8′ (no conditioning on exact counts). Each kernel of index $d$ contributes $(1/(2d)+o_{\mathbb P}(1))\log\log X$ by its prime density. The minimum has the stated law. For an odd prime $q$, all first-power eigenvalues on the odd group are $2$ or global units. The separating direction and Strassmann argument of GF-21 §2.5 (again via Lemma 2.8′) therefore give tightness, including $q\mid |G_g|$; multiplication by the fixed unit count changes a valuation by a constant. All equidistribution used here is modulo fixed moduli before passing to larger cutoffs.

Finally $r_{Q_g}\le|\mathcal O_g^\times|\prod_{p^j\parallel m,\ p\ {\rm split}}(j+1)$ on this coprime support. The nonnegative multiplicative upper-mean estimate used in GF-21 Theorem 2.3 gives a bounded support average of $r_{Q_g}^{1/\log\log X}$: the exponent change at split primes is $(2^{1/\log\log X}-1)/2=O(1/\log\log X)$ and the higher-power contribution is bounded uniformly. The inequality $y^2\le2e^y$ for $y\ge0$ gives a bounded second moment of the normalized logarithm, proving uniform integrability. ∎

### The full constant

**Theorem 8 (Paper proof).** Define

```math
C_Q=\sum_{d\mid f}\frac{B_{f/d}}{d^2},\qquad
\eta(Q)=\frac1{C_Q}\sum_{d\mid f}\frac{B_{f/d}}{d^2}\eta_{f/d}.
```

For every primitive $Q$ of discriminant $f^2D$ and each construction radix $b\ge2$,

```math
1-D_N(\Theta_Q(1/b);b)\sim
\frac{C_Q\log\log N}{2\log b\sqrt{\log N}}
\begin{cases}
1+\eta(Q)\log2 & b=2^j,\ j\ge1,\\
1+\log2 & b\text{ has an odd prime divisor}.
\end{cases}
```

These constants are identical for all primitive classes of the discriminant. In particular $(V_q)$ is unconditional for every odd prime $q$, also on the *full* represented support, even when $q\mid f$.

*Proof.* The disjoint union in Lemma 6 and Lemma 7 give the stated expression for $C_Q$ and component probabilities $B_{f/d}/(d^2C_Q)$. On each component the scale $\log\log(N/d^2)$ differs from $\log\log N$ by $o(1)$. The finite mixture preserves tightness of odd valuations and uniform integrability. Put $\rho=S_Q(N)/N$ and $\lambda=\log_b(1/\rho)\sim(\log\log N)/(2\log b)$. For a supported coefficient $r$ its width $u$ is the number of digits after stripping its maximal power of $b$. If an odd prime divides $b$, then $u=\log_b r+O_{\mathbb P}(1)$, hence $u/\lambda\to\log2$. For $b=2^j$ the width is $(\log r-v_2(r)\log2)/\log b+O(1)$, so its limiting law on component $g$ is $(1-1/d_g^*)\log2$. Both width laws are supported below one and their first moments converge by uniform integrability.

Apply the mixture width law in [Phase 21, Theorem 1 and Remark 5](../phase21/radix-lambert.md) to the entire coefficient sequence. The mass is $O_Q(N)$ by lattice-point counting, and $r_Q(n)=n^{o(1)}$ by the coprime ideal bound and Lemma 6. The required two-sided isolation for the union, including pairs from *different* components, is [Phase 21, Proposition 2.1, step 2](../phase21/euler-square-and-forms.md): both indices must have even valuation at all inert primes away from $f$, giving $o(S_Q(N))$ close sources at distances $O(\log\log N)$ by the pair sieve. The width law yields $(1+\mathbb E[u/\lambda]_{\rm lim})\rho\lambda$ for the deficit. This proves the formula without assuming additivity of discrepancy for a sum of theta series. ∎

The class group of each order supplies its genera, possible character orders and kernel indices. The survival probabilities also depend on **which rational primes** lie in each class. The conductor determines which primes to omit and how to weight the lower orders. Even a conductor with trivial kernel on class groups can change $\eta(Q)$, as for $-92$. The alternative factor $1+\log2$ uses the odd-prime valuation bound, including in even radices with an odd factor. The split-prime density here is $1/2$ and all normalized widths are at most $\log2<1$ in the limit. **Conditional** estimates involving $(R_b)$ above the general multiplicative threshold $\delta_b^*$ concern other coefficient families in [GF-21, §1](../phase22/radix-thresholds-and-class-groups.md); Theorem 8 uses no digit-run condition.

## 5. Examples and imprimitive forms

For an order with odd class group of order three, put $P_g=\prod_p(1-1/(p^2+p+1))$, over nonprincipal split primes $p\nmid g$ of that order. Here $P_g$ refers to the field $K$ in its row (independent of the consecutive-pair product in §2). All nontrivial characters survive together, giving $\eta_g=2P_g/3$. For a $2$-group $\eta_g=0$. The table gives the coefficient of $\log2$ in the dyadic multiplier and the support constant relative to the field norm constant. The other-radix multiplier is $1+\log2$ throughout.

| Discriminant | Field discriminant | Conductor | Ring class number | $C_Q/C_K$ | $\eta(Q)$ |
|---:|---:|---:|---:|---:|---:|
| −12 | −3 | 2 | 1 | 1 | 0 |
| −16 | −4 | 2 | 1 | 3/4 | 0 |
| −27 | −3 | 3 | 1 | 7/9 | 0 |
| −28 | −7 | 2 | 1 | 3/4 | 0 |
| −32 | −8 | 2 | 2 | 1/2 | 0 |
| −36 | −4 | 3 | 2 | 5/9 | 0 |
| −44 | −11 | 2 | 3 | 1 | $P_2/2$ |
| −64 | −4 | 4 | 2 | 7/16 | 0 |
| −75 | −3 | 5 | 2 | 13/25 | 0 |
| −92 | −23 | 2 | 3 | 3/4 | $20P_1/27$ |
| −108 | −3 | 6 | 3 | 7/9 | $3P_6/7$ |

**Paper proof of the entries.** Enumerate reduced primitive forms $[a,b',c]$ with $|b'|\le a\le c$, $a\le\sqrt{|\Delta|/3}$, and $b'\ge0$ on ties. The resulting orders all have class number one, two or three, hence $e_g=\gcd(2,|G_g|)$. Insert the split/inert/ramified factors in Theorem 8. For instance:

* At $-12$ the form $x^2+3y^2$ has no representation at $v_2(n)=1$. Its counts at $4m$ equal those of $x^2+xy+y^2$ at $m$. In particular the unit count changes from two to six on descent; a constant multiplier attached to the upper order would miss this.
* At $-92$, for $x^2+23y^2$, the two coprime support contributions in units of $C_K$ are $1/2$ and $1/4$. Extension onto the maximal class group is an isomorphism (surjectivity follows from ideals prime to the conductor, and both groups have order three). The prime $2$ splits into nonprincipal ideals in the maximal order: $[2,1,3]$ represents two and $[1,1,6]$ does not. Thus $P_2=P_1/(1-1/7)=7P_1/6$ here. Weighting $2P_2/3$ and $2P_1/3$ in proportions $2/3,1/3$ gives $20P_1/27$.
* At $-108$, for $x^2+27y^2$, the conductors $6,3,2,1$ contribute respectively $1/2,1/6,1/12,1/36$ in units of $C_K$. Only the first has nontrivial odd characters; its conditional weight $9/14$ gives $\eta(Q)=3P_6/7$. At $-44$ the analogous weight of the cubic order is $3/4$.

**Corollary 9 (Paper proof, imprimitive forms).** For an integer $k\ge1$, put $Q'=kQ$. In construction radix $b\ge2$ the deficit for $\Theta_{Q'}(1/b)$ has the formula of Theorem 8 with $C_{Q'}=C_Q/k$ and $\eta(Q')=\eta(Q)$. More precisely,

```math
1-D_N(\Theta_{kQ}(1/b);b)
\ \sim\ 1-D_{\lfloor N/k\rfloor}(\Theta_Q(1/b^k);b^k).
```

*Proof.* $r_{kQ}(n)=\mathbf1_{k\mid n}r_Q(n/k)$, whence $\Theta_{kQ}(1/b)=\Theta_Q(1/b^k)$. For the left orbit use width and valuation in radix $b$ at source positions $km$. Dilating the source set by fixed $k$ divides its density by $k$ to leading order and adds $\log_b k+o(1)$ to $\lambda$ relative to the scale at $N/k$. The normalized width law is unchanged and the isolation estimate persists, since a gap bounded by $H$ after dilation came from one bounded by $H/k$. This gives the left-hand constant. For the right orbit apply Theorem 8 with radix $b^k$, whose dyadic type is the same and whose logarithm is $k\log b$. The leading equivalents agree. The identity of real numbers alone gives the tower relation between the orbits, not equality of their finite discrepancies. ∎

## 6. Finite evidence and proof dependencies

**Finite measurement.** For $1\le n\le8192$ the triples (support count, absolute mass, square mass) for the cubic character modulo seven are $(6154,12176,34416)$ for $c_+$ and $(4081,5662,9324)$ for $c_-$. These are coefficient statistics.

**Finite certificate.** The [exact verifier](../../scripts/phase23_dense_forms.py) independently convolves divisor weights and multiplies prime-power factors in the cyclotomic integer ring. It checks the other three example characters through $2048$, the quintic trace pairing and its phase-zero test, the cubic phase averages, the consecutive-support local factors and the finite signed-tail recurrence in construction radices $2,3,10$. Rounding each product endpoint outwards on a rational grid through $p\le4096$, then multiplying the lower endpoint by $1-1/4096$ for the omitted primes, certifies $3/4<\delta<751/1000$ in modulus seven. The analytic tail bound uses $\sum_{n>Y}n^{-2}\le1/Y$.

For the bounds on $C_{\rm odd}$ in Theorem 4A, write $x=1/p$. The split local factor is at most $1+(1-x)\sum_{e\ge2}e x^e=1+(2p-1)/(p^2(p-1))\le1+3/p^2$. The verifier rounds the product of these upper bounds upwards through $Y=4096$ and multiplies it by the upper bound for the corresponding $\delta$ and by $(1-3/Y)^{-1}\ge\exp(3/Y)$ for the remaining primes. This certifies $4/5$ as a strict upper bound modulo seven and $21/25$ modulo nine and thirteen. Conjugating a cubic character leaves these upper bounds unchanged. The verifier also checks the deterministic displaced signed polynomial identity and its pointwise orbit-distance inequality on the first 80 coefficients in dyadic construction radices, and sums the exact digit-cylinder minima.

For each of the eleven discriminants the verifier enumerates reduced forms and counts *all* lattice vectors through norm $4096$ by completing the square. It compares single-prime descent for every class, simultaneous descent for the principal class, class-summed conductor Euler factors, and the coefficient identity for dilations by two and three. It recomputes the rational factors in the table from the formulas of Lemma 7 and Theorem 8, and separately checks the arithmetic facts used for $-92$ ($2$ split; $[1,1,6]$ misses $2$; $[2,1,3]$ represents $2$). Support constants and $\eta(Q)$ are not measured here, and at this range could not be. These checks establish finite identities in the stated ranges. The infinite products $P_g$ in the theta constants are left exact.

**External input and status.** The paper proofs use the prime number theorem in fixed progressions, Turán–Kubilius and Selberg–Delange (Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, chapters II.5 and III.3), the ideal–form correspondence and ring class fields (Cox, *Primes of the Form $x^2+ny^2$*, chapters 2–3), and the sieve and Strassmann inputs of GF-21. The paper proofs above have no new Lean declaration. For the original $L_\pm(b)$, GF-22 gives disjunctivity and Theorem 4A gives simple nonnormality and $D^->0$ in the stated dyadic construction radices. Whether the orbit can concentrate completely, or every prescribed word has positive lower frequency, is open here. The [complementary-coverage barrier](../phase21/classical-barriers.md) applies to aligned source decompositions; Theorem 4A uses displaced sources.
