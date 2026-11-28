# Euler’s square and the binary digits of higher theta powers

**Paper proof.** Each constant binary word in Euler’s square has lower frequency at least $1/(3\pi)>1/10$. This improves the earlier $1/26$. The proof selects the sign at the right endpoint of each gap before sieving for a predecessor. For the cube and fourth power of Jacobi’s theta series, the mean minimum signed binary weight of the coefficients tends to infinity. Each fixed set of low coefficient bits nevertheless gives a series with binary one-frequency zero. The full theta values at a fixed stretch remain open.

## 1. The signed gaps in Euler’s square

Put $E(q)=\prod_{j\ge1}(1-q^j)$, $E_b=E(1/b)$, $a(n)=[q^n]E(q)^2$, $s(n)=\mathrm{sgn}\,a(n)$, and list its support as $0=m_0<m_1<\cdots$. Write $g(m_i)=m_i-m_{i-1}$. For a binary word $w$, let $f_w(N;x)$ count occurrences beginning at the first $N$ positions in the canonical binary expansion of the fractional part of $x$, divided by $N$. Logs without a subscript are natural. Write $\delta=3/4$, $\rho=C_\eta/(\log N)^\delta$, $S=\#\{0<m_i\le N\}$. The normalization of $C_\eta$ is $S\sim N\rho$. Binary simple normality means $f_1\to1/2$. Normality of order $L$ means $f_w\to2^{-L}$ for all words of length $L$, and binary normality requires this for every $L$. For the binary orbit $y_n=\{2^nx\}$ write

$$
 D_N(x;2)=\sup_{0\le a<b\le1}\left|N^{-1}\#\{0\le n<N:y_n\in[a,b)\}-(b-a)\right|,\qquad
 K_2=\{x:D_N(x;2)\to1\}.
$$

**Prior results and external inputs.** In the arithmetic index $l=12m+1$, $a(m)=c(l)$ for the weight-one CM form $\eta(12\tau)^2$. Write $\mathcal P$ for the primes $5,7,11\bmod12$. A supported $l$ has unique decomposition $v^2 u$, with $v$ composed of primes of $\mathcal P$ and all prime factors of $u$ equal to $1\bmod12$. Conversely every such integer occurs. The sign is multiplicative in these two factors and completely multiplicative on the latter semigroup. Its prime sign is positive for $p=x^2+36y^2$, negative for $p=4x^2+9y^2$. The identity and the element of order two of the cyclic subgroup of order four in the dihedral Galois group of the ring class field over $\mathbb Q$ give these two sign classes, each of prime density $1/8$. Serre’s CM identification, the class-field description, and a Halász–Wirsing / Hall–Tenenbaum comparison theorem for real multiplicative functions dominated by $1_{\mathcal N}$ (since $\sum_{p:\,s(p)=-1} 1/p = \infty$; also reproved independently by Corollary 1.1 below at $q=1, \Phi\equiv 1$) give $S_\sigma\sim S/2$ for each sign. The external short-interval input is Matomäki–Radziwiłł, Corollary 1.2(ii), on the exact multiplicative support. Its primes are the progression $1\bmod12$, of density $1/4$, satisfying their prime-sum condition by the prime number theorem in progressions. For $1<\gamma<3/2$, it gives $\sum g^\gamma\ll N\rho^{1-\gamma}$. The carry argument in GF-29 then gives, for every fixed $L\ge1$,

$$
 f_{0^L}(N;E_2^2)-f_{1^L}(N;E_2^2)
 = N^{-1}\sum_{0<m_i\le N}s(m_i)g(m_i)+o(1),\qquad
 f_{0^L}+f_{1^L}=1+o(1).
$$

The uncompleted last gap costs $O(\sqrt N)$ since $12(3j^2+j)+1=(6j+1)^2$ is supported. With $W_\sigma=\sum_{s(m_i)=\sigma,\,0<m_i\le N}g(m_i)$ the two frequencies thus equal $W_+/N+o(1)$ and $W_-/N+o(1)$ respectively. [GF-29, §§1–2](../phase23/euler-square-and-higher-order-tower.md) · [Prime signs and ring class field](../phase22/flagship-digit-laws.md#4-eulers-square) · [Matomäki–Radziwiłł](https://arxiv.org/abs/2007.04290)

**Reproduction of the earlier bound (Paper proof).** Summing the layers of $\min(g,H)$ gives $W_\sigma\ge HS_\sigma-H-\sum_{h<H}(H-h)P_h$, where $P_h$ counts all supported pairs a positive distance $h$ apart. Phase 24 §2.2 bounds the weighted pair sum by $(K_*+o(1))H^2N\rho^2/2$ when $H=\lfloor t/\rho\rfloor$, with

$$
 K_*=\frac{3\sqrt{2\pi}}{32}\Gamma(1/4)^2
 \prod_{p\in\mathcal P}\left(1+\frac{2}{(p-1)(p^2+1)}\right).
$$

Maximizing $t/2-K_*t^2/2$ gives $1/(8K_*)$. [Phase 24, Theorem 2.3](../phase24/simple-normality-and-word-laws.md)

**Finite certificate.** The verifier independently encloses $\pi$ by the alternating series in Machin’s formula, and bounds $\Gamma(1/4)$ by integrating the upper Taylor polynomial of degree 80 for $e^{-x}$ on $[0,16]$ against $x^{-3/4}$, with remaining integral below $2^{-16}$. For the product after 100 the log-tail is at most $\sum_{j\ge50}1/(4j^3)<1/19208$, so the product tail is at most $19208/19207$. The rational comparisons give $8K_*<25.431<26$.

### Theorem 1. A lower frequency greater than one tenth

**Paper proof, objective 3.** For every fixed $L\ge1$ and $d=0,1$,

$$
 \frac1{3\pi}\ \le\ \liminf_N f_{d^L}(N;E_2^2)
 \ \le\ \limsup_N f_{d^L}(N;E_2^2)\ \le\ 1-\frac1{3\pi}.
$$

In particular the limsup of the absolute normalized signed gap sum is at most $1-2/(3\pi)$. The proof below uses equidistribution only for a selected set of *single endpoints*, followed by a one-sided upper sieve for an earlier support point.

**Selecting endpoints.** Put $X=12N+1$. Fix $V$ and $0<e<b<1/4$. Retain right endpoints with $v\le V$, $l>X^{1-b}$, and a prime factor in $I=(X^e,X^b]$ congruent to $1\bmod12$. Give them weight as follows. For $u=pm$ count each distinct $p\in I$ with weight $1/(1+\omega_I(m))$, where $\omega_I$ counts distinct such primes. Partition by the sign of $v^2pm$. The sum of the weights at one endpoint is at most one and equals one when all its factors in $I$ are simple and at least one occurs. A repeated prime in $I$ costs $O(\sum_{j>X^e}X/j^2)=o(S)$ endpoints.

The lost proportion of $S$ can be made arbitrarily small. The count with $v>V$ is $\ll S/V+O(X^{3/4})$, by summing the support upper bound at $X/v^2$ up to $v=X^{1/4}$ and the trivial bound thereafter. In arithmetic indices let $S_0(Y)$ count the full multiplicative support up to $Y$, so $S_0(X)=S+1$. For a good prime $p$, the support count divisible by $p$ equals $S_0(X/p)$, including repeated powers. The same holds for two distinct good primes. Set $J=\sum_{p\in I,\,p\equiv1(12)}1/p\to\frac14\log(b/e)$. Under uniform counting on the support the first moment of $\omega_I$ lies between $(1-o(1))J$ and $((1-b)^{-\delta}+o(1))J$. Its second factorial moment is at most $((1-2b)^{-\delta}+o(1))J^2$. Indeed $S_0(X/d)/S_0(X)=(1+o(1))(\log X/\log(X/d))^\delta/d$ uniformly for $d\le X^{2b}$. Bounding the probability of zero by the mean of $(\omega_I-J)^2/J^2$ gives an upper limit at most $(1-b)^{-\delta}/(\frac14\log(b/e))+(1-2b)^{-\delta}-1$. First choose $b$ small, then $e$ small, and take $N\to\infty$ with these fixed. The cut $l\le X^{1-b}$ costs $o(S)$. Thus for either sign the selected mass is at least $(1/2-\eta)N\rho$ up to $o(N\rho)$, with $\eta$ arbitrarily small.

**Equidistribution of the selected factors.** For fixed $v$ and sign, view the selected measure in $u$ as a sum of two nonnegative convolutions. One factor is the indicator of primes in $I$ with a specified sign, the other is the indicator of allowed cofactors $m$ with the required complementary sign, weighted by $1/(1+\omega_I(m))$. All factors are units modulo every integer composed of primes of $\mathcal P$. We may enlarge the region $X^{1-b}<v^2pm\le X$ to a disjoint union of rectangles in $p,m$ of multiplicative mesh $1+(\log X)^{-D}$, taking all intersecting boxes, with the prime interval clipped at its ends. The extra endpoint mass is $O_V(1+X/(\log X)^D)$ since each $u$ has weight at most one. There are $O((\log X)^{2D+2})$ boxes. Denote this enlarged measure by $B_v$ and its mass by $M_v$. In particular $\sum_{v\le V}M_v\le(1/2+o(1))N\rho$ for each sign. We use enlarged measures only for upper bounds. Take $D>4$ fixed.

For every $\kappa>0$, every $A>0$, and $Q\le X^{1/2-\kappa}$, these measures satisfy

$$
 \sum_{\substack{q\le Q\\p\mid q\Rightarrow p\in\mathcal P}}
 \max_{(a,q)=1}\left|B_v(u\equiv a\bmod q)-M_v/\varphi(q)\right|
 \ll_{A,e,b,V,\kappa} X/(\log X)^A. \tag{1}
$$

Here are details of the analytic inputs and the level. **External input.** Murty–Petersen (*Trans. Amer. Math. Soc.* **365** (2013), 4987–5007, Theorem 0.2) give a Bombieri–Vinogradov estimate for a Frobenius class, with arbitrary logarithmic saving and a positive power level over cyclotomic fields disjoint from the ring class field. Here the two classes are singletons in the cyclic subgroup of index two. The field ramifies only at $2,3$, so its intersection with $\mathbb Q(\zeta_q)$ for our moduli is unramified at every finite prime, hence is $\mathbb Q$ by Minkowski. Their parameter $\theta = \max\{[E:\mathbb Q]-2, 2\}$ is 2, where $E = \mathbb Q(i)$ is the fixed field of the cyclic subgroup of order four (an abelian subgroup meeting the class). We only need the small-modulus consequence: for a nonprincipal primitive character of conductor $r\le(\log X)^F$ composed of these primes, its sum over either sign class in any subinterval of $[P,2P]$, $P\gg X^e$, is $\ll_{F,A,e} P/(\log X)^A$. Partial summation removes the log weight, prime powers are negligible, and expansion over the at most $r$ reduced classes absorbs a fixed logarithmic power. [Murty–Petersen, Theorem 0.2](https://www.math.fsu.edu/~aluffi/archive/paper443.pdf)

For completeness, on a box $p\asymp P,m\asymp M$ write the character sums of the two factors as $A_\chi,B_\chi$. Here $PM\ll_V X$ and both lengths have polynomially large scales, $P\gg X^e$, $M\gg_V X^{1-2b}$. By character orthogonality the error summed over moduli is bounded by the sum of $|A_\chi B_\chi|/\varphi(q)$ for nonprincipal characters. An induced character equals its primitive character on every operand. Summing $1/\varphi(q)$ over multiples of a conductor $r$ costs $\ll(\log X)^2/\varphi(r)$, since $\varphi(rs)\ge\varphi(r)\varphi(s)$ and $\sum_{s\le X}1/\varphi(s)\ll(\log X)^2$. The small conductors are handled by the preceding prime bound and $|B_\chi|\ll M$. For $R<r\le2R$ the multiplicative large sieve and Cauchy–Schwarz give

$$
 \sum_{r\asymp R}\frac1{\varphi(r)}\sum_{\chi\bmod r}^{*}|A_\chi B_\chi|
 \ll \frac{\sqrt{PM}}{R}\sqrt{(P+R^2)(M+R^2)}
 \ll \frac{PM}{R}+\frac{PM}{\sqrt P}+\frac{PM}{\sqrt M}+R\sqrt{PM}.
$$

The large sieve here is the classical inequality $\sum_{r\le Z}(r/\varphi(r))\sum_\chi^*|\sum_{n\le Y}a_n\chi(n)|^2\le (Y+O(Z^2))\sum|a_n|^2$, applied to bounded sequences supported in $[1,2P]$ and $[1,2M]$. Summing the dyadic ranges $R\ge(\log X)^F$ and the boxes proves (1) by choosing $F$ large. It also holds with a factor $3^{\omega(q)}$ on the left, with arbitrary saving. Indeed the individual discrepancy is $\ll_V X\tau(q)/q$ since $B_v(u)\le1$ and $q\le Q$, and Cauchy–Schwarz with (1) absorbs the divisor weights via $\sum_{q\le X}9^{\omega(q)}\tau(q)/q\ll(\log X)^{O(1)}$ by an Euler product. [Kedlaya, multiplicative large sieve](https://kskedlaya.org/ant/chap-largesieve2.html)

**Sieving the predecessor.** Fix an integer $T\ge V$, a positive $J_0$, and put $M_0=\prod_{\ell\in\mathcal P,\,\ell\le T}\ell^{2J_0}$. For $l=v^2u$, a predecessor a distance $h$ away has arithmetic index $l-12h$. At $\ell\le T$ admit residues of even valuation below $2J_0$ and the zero residue modulo $\ell^{2J_0}$. Let $b_v(h)$ be the fraction of units $u\bmod M_0$ passing these tests. It is periodic in $h$ and has mean

$$
 b_*=\prod_{\ell\le T,\,\ell\in\mathcal P}
 \left(\frac{\ell}{\ell+1}+\frac1{(\ell+1)\ell^{2J_0}}\right).
$$

In fact for each fixed unit, $v^2u-12h$ runs through all residues as $h$ varies. A genuine predecessor whose square part is $\le V$ has no prime factor from $\mathcal P$ above $T$. For $T<\ell<\xi=N^\beta$, $\beta<1/4$, sieve one unit class of $u$ modulo $\ell$ if $\ell\nmid h$, and none otherwise. Here $\ell\nmid12v$. Relative to units the first local density is $1/(\ell-1)$.

The Selberg upper square, applied on each admitted class modulo $M_0$, bounds the count with weight $B_v$ by

$$
 M_v b_v(h)G_T(\xi)^{-1} R_T(h)+O_{A,T,J_0,V}(X/(\log X)^A),
 \quad R_T(h)=\prod_{\ell\in\mathcal P,\,\ell>T,\,\ell\mid h}
 \left(1+\frac1{\ell-2}\right).
$$

Here $G_T(\xi)=\sum_{d<\xi}\mu(d)^2\prod_{\ell\mid d}1/(\ell-2)$ is restricted to $\mathcal P$ above $T$. The quadratic form in Selberg’s argument depends only on the multiplicative main density, so the optimum has $|\lambda_d|\le1$ and main term $1/G$ for the actually used primes. Removing $\ell\mid h$ reduces $G_T$ by at most the factor $1+1/(\ell-2)$ at each removal, by splitting divisors according to divisibility by $\ell$. Each lcm in the remainder occurs at most $3^{\omega(d)}$ times. Apply weighted (1) at $q=M_0d$, since $M_0\xi^2<X^{1/2-\kappa}$ for some fixed $\kappa>0$. This error is uniform in $h$. [Selberg diagonalization and bounded weights](../phase22/partitions-carry-and-lemma-s.md#12-selbergs-upper-bound-with-proof)

For $H=\lfloor t/\rho\rfloor$, the triangular mean $(2/H^2)\sum_{1\le h<H}(H-h)b_v(h)R_T(h)$ tends to
$b_*\prod_{\ell\in\mathcal P,\,\ell>T}(1+1/[\ell(\ell-2)])$. Expand $R_T$ over squarefree divisors with weights $r(d)=\prod_{\ell\mid d}1/(\ell-2)$. Each fixed $d$ is coprime to $M_0$, giving mean $b_*/d$. The triangular mean restricted to $d\mid h$ is bounded by $1/d$, and $\sum r(d)/d<\infty$, justifying the limit.

**Normalization.** Wirsing and partial summation give

$$
 G_T(\xi)^{-1}\sim e^{\gamma_E\delta}\Gamma(1+\delta)
 \prod_{T<\ell<\xi,\,\ell\in\mathcal P}(1-1/(\ell-1)).
$$

Apply Wirsing to the nonnegative squarefree-supported multiplicative function with prime value $\ell/(\ell-2)$ on the indicated primes and zero elsewhere. Its prime values are bounded, have weighted prime mean $\delta$ by the progression prime theorem, and higher prime powers vanish. Partial summation divides the leading constant in $G_T$ by $\delta$, as in Phase 24. The support normalization is $\rho\sim \mathcal W\prod_{\ell\le N,\ell\in\mathcal P}(1-1/\ell)$ where $\mathcal W=4e^{\gamma_E\delta}\prod_{\ell\in\mathcal P}(1-\ell^{-2})^{-1}/\Gamma(1/4)$. The factor 4 comes from the progression index 12 and removing 2 and 3. [GF-29, normalization of the support](../phase23/euler-square-and-higher-order-tower.md)

At every large prime the exact cancellation is $(1-1/(\ell-1))(1+1/[\ell(\ell-2)])=1-1/\ell$. Taking $J_0\to\infty$ after the $N$ limit gives the small-prime factors $\ell/(\ell+1)=(1-1/\ell)/(1-\ell^{-2})$. Thus the upper cost per selected endpoint per unit of triangular shift mass, divided by $\rho$, tends to

$$
 \frac{\Gamma(1+\delta)\Gamma(1/4)}4\,\beta^{-\delta}
 \prod_{\ell>T,\,\ell\in\mathcal P}(1-\ell^{-2}).
$$

Here the Mertens product at $N^\beta$ divided by that at $N$ tends to $\beta^{-\delta}$. (Note that for finite $T$ the factor $\prod_{\ell>T}(1-\ell^{-2}) < 1$ is strictly smaller than $1$ only because predecessors with square part $>V \le T$ are excluded from the sieve and charged separately at cost $O(tN/V)$ below; hence only the limit $T \ge V \to \infty$ gives the true constant $K$.) Let $T\to\infty$ and $\beta\uparrow1/4$. The gamma recurrence and reflection formula give $\Gamma(7/4)\Gamma(1/4)4^{3/4}/4=3\pi/4=:K$. The factor $1/2$ for the selected sign remains in its endpoint mass.

**From pairs to gap lengths.** Each selected end contributes at least $H$ minus its deficit $(H-g)_+$. If its immediate predecessor has square part $>V$, charge at most $H$ to that predecessor. Each predecessor is charged at most once, costing $O(HS/V)+o(HS)$ in total. For every other deficit count the preceding pair with weight $H-h$. All additional pairs counted in the sieve only increase the deduction. The initial point costs at most $H$. Using $\sum M_v\le(1/2+o(1))N\rho$ gives, for each fixed $t>0$, after taking the preceding limits and making the discarded endpoint proportion tend to zero,

$$
 \liminf_N W_\sigma/N\ \ge\ t/2-Kt^2/4 .
$$

All parameters can be fixed before $N$ for any prescribed loss: choose large $V,T$, the small-prime precision $J_0$, $\beta<1/4$, and the band parameters $b,e$. The estimates need no uniformity in those choices. At $t=1/K$ the bound is $1/(4K)=1/(3\pi)$. Complementation and the GF-29 identity prove the theorem.

### Corollary 1.1. Signed survival tests with a small common modulus

**Paper proof, objectives 1 and 4.** For any fixed $D'>0$, uniformly over $\mathcal P$-supported moduli $q\le(\log N)^{D'}$ and functions $|\Phi|\le1$ on $\mathbb Z/q\mathbb Z$,

$$
 \sum_{0<m_i\le N}s(m_i)\Phi(m_i\bmod q)=o(S).
$$

For each fixed $v$ the total masses of the two enlarged signed classes differ by $O_A(X/(\log X)^A)$ for arbitrary $A$. In each box and for each cofactor sign, their difference replaces the prime indicator by the difference of the two prime indicators. Chebotarev at modulus one gives equal main terms and arbitrary log saving, as both classes have size one; sum over the boxes. For each sign use (1), sum its errors over the $\varphi(q)$ unit classes, and evaluate $\Phi((v^2u-1)/12\bmod q)$ on those classes. Here 12 is invertible even if $v$ is not. Principal terms cancel to the stated saving for the enlarged measures. The boundary enlargement costs $o(S)$ and the unsigned discarded mass is at most $(\eta+o(1))S$. Let $\eta\to0$. In particular at $H=\lfloor t/\rho\rfloor$, replacing the first $H$ survival layers by arbitrary bounded periodic tests of the preceding offsets, each with such a common modulus within its own layer, gives total signed sum $o(N)$, uniformly over the tests. Excluding $m_i\le j$ in layer $j$ costs at most $O(H^2)=o(N)$.

**Prior Paper proof (GF-29) & Conditional reduction (objectives 1 and 4).** For $H/\rho^{-1}\to\infty$, the true signed survival sum $\sum_{m_i\le N,\ i>0}s(m_i)\min(g(m_i),H)$ is $o(N)$ if and only if $E_2^2$ is simply normal (unconditional equivalence from GF-29 (5) together with the gap-moment bound $O(N(\rho H)^{1-\gamma})$ on the discarded mass). Indeed each term counts layers $0\le j<H$ with $m_i>j$ and no support at $m_i-h$, $1\le h\le j$. Conditionally on a missing approximation estimate — namely, that for every fixed $t$ these true layers up to $H=\lfloor t/\rho\rfloor$ can be approximated by tests in Corollary 1.1 with total absolute error $o(N)$ summed over supported endpoints and layers — taking $N\to\infty$ followed by $t\to\infty$ (with normalized remainder $O(t^{1-\gamma})$) would establish binary simple normality of $E_2^2$.

**Open.** The small-modulus cancellation leaves the approximation error and binary simple normality unresolved. The dilation $m\mapsto13m+1$ reverses every nonzero sign, including repeated factors, but maps the gap from 0 to 1 to the interval from 1 to 14, which already contains the supported index 2 ($12\cdot2+1=25$). It preserves emptiness only within the image progression.

## 2. The cube and fourth power of Jacobi’s theta value

Write $\Theta_3(q)=\sum_{m\in\mathbb Z}q^{m^2}$ and $r_j(n)=\#\{\mathbf m\in\mathbb Z^j:\sum m_i^2=n\}$, counting order and signs. Then $x_{j,k}=\Theta_3(2^{-k})^j=\sum_{n\ge0}r_j(n)2^{-kn}$, for integers $k\ge1$. Write $s_2(c)$ for binary digit sum and $w(c)$ for minimum weight (number of nonzeros) among binary expansions with digits $-1,0,1$. Put both weights equal to zero at zero. The nonadjacent form attains $w$ (Reitwiesner 1960). In particular $w(c)\le s_2(|c|)$ and $w(2c)=w(c)$.

**External input and attribution.** Bailey, Borwein, Crandall and Pomerance use both $z=\sum_{m\ge0}2^{-m^2}$ and $z'=2z-1=\Theta_3(1/2)$. Their Theorem 9.4 states a one-count asymptotic $C_0N/\sqrt{\log N}$ for $z^2$, with $C_0$ about $0.7996$; immediately afterwards they extend the asymptotic to $(z')^2$. On p. 509 they suggest binary normality for higher powers, naming $z^3,z^4$, and point to the positive density of three-square representations and the resulting interference of carries. This is a conjectural observation about their named powers. [BBCP, §9, pp. 505–511](https://www.numdam.org/item/JTNB_2004__16_3_487_0.pdf)

For the cube one can connect the two notations at full normality level. Define $M_2$ by $N^{-1}\sum_{n<N}\|2^n y\|\to0$, where $\|\,\cdot\,\|$ is distance to an integer. It is an additive group. A number with binary one-frequency zero belongs to $M_2$, by inspecting a fixed number of future bits and then increasing that number. Thus $z,z^2\in M_2$ by square support and BBCP. The difference $(z')^3-8z^3=-12z^2+6z-1$ lies in $M_2$. Addition of an element of $M_2$ preserves equidistribution of a doubling orbit in both directions, by uniform continuity of each continuous periodic test function. Shifting three bits preserves binary normality. Hence $z^3$ is binary normal if and only if $(z')^3$ is. For the fourth power the expansion also contains $-32z^3$, whose orbit is unresolved. **Paper proof, objectives 1 and 4.**

### Theorem 2. Raw digit mass and signed weight at fixed stretch

**Paper proof, objective 4.** As $X\to\infty$,

$$
 X^{-1}\sum_{n\le X}w(r_3(n))\longrightarrow\infty,\qquad
 \sum_{n\le X}w(r_4(n))\asymp X\log X .
$$

The same conclusions hold for $s_2$. In particular, neither coefficient list has bounded mean raw digit mass or bounded mean minimum signed weight at any fixed stretch. Multiplying the number of digit positions per coefficient by a fixed $k$ merely divides these means by $k$. These conclusions do not require a model of independent bits in the coefficients.

**Four squares.** Jacobi’s formula gives $r_4(n)=8\sum_{d\mid n,4\nmid d}d$. For $n=2^a u$ with $u$ odd it is $8\sigma(u)$ if $a=0$, and $24\sigma(u)$ otherwise. Here $\sigma(u)=\sum_{d\mid u}d$. Take $n=mp\le X$ odd with $\sqrt X<p\le X^{3/4}$ prime. Each occurs once and contributes $8\sigma(m)(p+1)$. There are $\gg X$ such $n$ by summing $X/(2p)+O(1)$ over these primes (Mertens), and each output value has at most $\sqrt X$ preimages, one possible $p$ per $m$. All outputs are at most $8X^2$. For some absolute $c>0$ there are $O(X^{1/4})$ values of that size with $w\le c\log X$. Indeed a representation of weight $r$ and highest exponent $j$ has magnitude at least $2^{j-r+1}$, so uses $O(\log X)$ available positions for $r\le c\log X$. Sum $\binom{O(\log X)}r2^r$ and use $\binom{a}{r}\le(ea/r)^r$, choosing $c$ sufficiently small. Thus $O(X^{3/4})$ elements of the selected set have small weight. The upper bound follows from $w\le s_2\ll\log(2X)$. [Phase 22 entropy bound with explicit constants](../phase22/partitions-carry-and-lemma-s.md#35-three-counting-lemmas)

**Three squares.** The three-square theorem (Legendre 1798; Gauss 1801) gives $r_3(n)=0$ exactly on the disjoint sets $4^a(8b+7)$, of total density $\sum_{a\ge0}1/(8\cdot4^a)=1/6$ (the omitted tail lies among multiples of $4^A$). The identity $r_3(4n)=r_3(n)$ follows because all three coordinates must be even. We prove divergence on the positive-density subset of squarefree $n\equiv1\bmod8$ alone. For $n>1$ there, $D=-4n$ is fundamental, with just two units in its imaginary quadratic order. Gauss’s formula and Dirichlet’s class number formula give

$$
 r_3(n)=12h(D)=\frac{24}{\pi}\sqrt n\,L(1,\chi_D).
$$

Here $h(D)$ is the class number of discriminant $D$ and $\chi_D$ is its primitive quadratic character. The following details show how the factor $\sqrt n$ yields a digit-weight obstruction in this particular formula. Magnitude bounds alone would permit powers of two. [Gauss’s representation formula, Voight, Thm. 30.1.3](https://link.springer.com/chapter/10.1007/978-3-030-56694-4_30) · [Pollack, Prop. 3](https://www.pollack-math.net/cho.pdf)

Let $\mathcal A_X$ denote these squarefree integers in $[X,2X]$, and $L_n=L(1,\chi_{-4n})$. They have a positive asymptotic density by the squarefree sieve (truncate the square divisors and use CRT). For fixed $T$ put $P_T(n)=\sum_{m\le T}(-4n/m)/m$, using the Kronecker symbol. This is periodic in $n$. We claim

$$
 \lim_{T\to\infty}\limsup_{X\to\infty}\frac1X
 \sum_{n\in\mathcal A_X}|L_n-P_T(n)|^2=0. \tag{2}
$$

Truncate the primitive series first at $Y=\lceil\sqrt X(\log X)^3\rceil$. Pólya–Vinogradov and partial summation give uniform error $O(1/(\log X)^2)$ for this truncation. For the squared sum over $T<m\le Y$ enlarge the $n$-set to every integer of $[X,2X]$. The terms at even $m$ vanish. In the expansion, pairs $i,j$ with $ij$ square contribute after division by $X$ at most $(1+O(1/X))\sum_{i,j>T,\,ij=\square}1/(ij)$, which tends to zero. Indeed $i=da^2,j=db^2$ with the same squarefree $d$, and the full sum converges. For nonsquare odd $l=ij$, the Jacobi symbol $(n/l)$ is nonprincipal. Removing the extra imprimitive coprimality conditions by Möbius inversion and applying Pólya–Vinogradov to its primitive inducer bounds its interval sum by $O(\tau(l)\sqrt l\log(2l))$. The combined normalized error is $O(Y^{1+o(1)}/X)=o(1)$. This proves (2).

The normalized first moment $X^{-1}\sum_{\mathcal A_X} L_n$ has positive lower limit and the second moment is bounded. For the first claim, each fixed nonsquare odd $m$ has zero mean character over $\mathcal A_X$: for a prime with odd exponent in $m$, the nonzero classes of $n$ at that prime are equally represented under the squarefree condition and their Legendre symbols sum to zero. This follows by truncating square divisors in the squarefree sieve, or by CRT prime by prime. The square terms are nonnegative and $m=1$ contributes the density. Pass from $P_T$ to $L_n$ by (2). The second-moment bound follows from (2) and boundedness of a fixed $P_T$. Consequently there exist $0<c<C$ and $\alpha>0$ such that at least $\alpha X$ of these $n$ have $c\le L_n\le C$ for every sufficiently large $X$. For example, delete the portion $L_n<c$ from the first moment at cost $O(c)$ and $L_n>C$ at cost $O(1/C)$, then use $L_n\le C$ on the remainder.

Set $j_X=\lfloor\log_2\sqrt X\rfloor$. On that portion $r_3(n)2^{-j_X}$ lies in a fixed compact interval $[a,b]\subset(0,\infty)$. For fixed $W$, the normalized values having $w\le W$ lie in a compact countable set $F_W$: take all sums of at most $W$ signed powers $2^i$ with $i\le\lceil\log_2 b\rceil+W$, allowing zero summands. The highest exponent bound follows from the same weight inequality as for four squares. The set is compact as a finite sum of compact countable sets and has Lebesgue measure zero.

To justify anti-concentration despite the moving scale, cover $F_W\cap[a,b]$ by a finite union $O$ of open intervals inside $[a/2,2b]$, of arbitrarily small total length and with positive margin around that compact set. Approximate $r_3(n)2^{-j_X}$ by $(24/\pi)(\sqrt X/2^{j_X})\sqrt{n/X}\,P_T(n)$. For fixed margin the proportion of errors larger than the margin can be made arbitrarily small by (2). For fixed $T$ on each of the finitely many residue classes of the period, the approximating function has the form $B\sqrt{n/X}$. In $1\le n/X\le2$, wherever this function hits $[a/2,2b]$, its derivative with respect to $n/X$ is at least $a/8$. The preimage of $O$ consequently has length $\le8|O|/a$, uniformly in $B$, including the scale depending on $X$. Counting the finite union of intervals in each progression gives proportion $\le8|O|/a+o_T(1)$ even if the restriction to $\mathcal A_X$ is dropped. Shrinking the cover proves that only $o_W(X)$ of the selected $\alpha X$ points have $w\le W$. Thus on $[X,2X]$ the mean weight has lower limit at least $\alpha W$ for every $W$. Applying this to the last half of each prefix proves the first assertion of Theorem 2.

### Theorem 3. Low binary coefficient bits and the remaining carries

**Paper proof, objectives 2–4 (objective 1: reduction only).** For $j=3,4$, each fixed $t,k\ge1$, the series

$$
 L_{j,k,t}=\sum_{n\ge1}(r_j(n)\bmod 2^t)\,2^{-kn}
$$

has binary one-frequency zero. In particular it belongs to $M_2$ and to $K_2$, the set on which the extreme interval discrepancy of the doubling orbit tends to one. Moreover $x_{j,k}$ has the same weak subsequential empirical measures on the circle as $2^t\sum_{n\ge1}\lfloor r_j(n)/2^t\rfloor\,2^{-kn}$, along the very same subsequences. Binary normality of the two is equivalent.

For four squares, each odd prime $p\parallel n$ contributes the even factor $1+p$ to $\sigma(u)$. For three squares put $d$ equal to the squarefree part (the unique squarefree integer with $n/d$ square). We have $r_3(n)$ an integer multiple of $r_3(d)$ in the sense $r_3(n)=A\,r_3(d)$ with $A\in\mathbb Z$. Remove factors of four and use the prime-square formula for odd $p$, $p^2\nmid m$,

$$
 r_3(p^{2a}m)=
 \left(\sum_{i=0}^a p^i-\left(\frac{-m}{p}\right)\sum_{i=0}^{a-1}p^i\right)r_3(m).
$$

For $d>3$ squarefree and represented, Gauss gives $12h(-4d)$ for $d\equiv1,2\bmod4$ and $24h(-d)$ for $d\equiv3\bmod8$. These are fundamental discriminants. Gauss genus theory gives a quotient of the class group of order $2^{s-1}$ for $s$ distinct prime discriminant factors. Each odd prime of $d$ occurs among them. Consequently $2^{\max(0,\omega_{\rm odd}(d)-1)}\mid r_3(n)$, also valid trivially for the exceptions $d=1,2,3$ and the forbidden class. [Hirschhorn–Sellers, equations (2), (4), and attribution to Pall](https://www.d.umn.edu/~jsellers/p8.pdf) · [Gauss’s class-number formulas](https://www.pollack-math.net/cho.pdf)

For any fixed finite list of odd primes, the events $p\parallel n$ have independent natural densities $(p-1)/p^2$ by CRT modulo the product of their squares. Their mean count tends to infinity as the list grows and the variance is at most that mean. Chebyshev shows that all but density zero of $n$ have at least any prescribed number of such primes. Thus the nonzero residues in each displayed series have density zero. Their coefficients are bounded by $2^t-1$. In a prefix with $M$ blocks, subadditivity of binary digit sum bounds the number of ones by $t\,o(M)+O_t(1)$, since the rescaled tail is bounded by $(2^t-1)/(2^k-1)$. This also covers partial blocks. Arbitrarily long fixed zero words then have limiting frequency one, giving $M_2$ and discrepancy tending to one. Subtracting the quotient series multiplied by $2^t$ leaves $1+L_{j,k,t}$ in $M_2$. Uniform continuity on the circle gives the assertion about empirical measures as for the BBCP cube. A point mass at a binary cylinder boundary requires care for individual digits; the measure assertion uses continuous periodic tests.

**Exact displacements (Paper proof, objective 4).** For odd $p$ and $e\ge0$ put $b_p(e)=0$ for even $e$, and $b_p(e)=v_2(p+1)+v_2(e+1)-1$ for odd $e$. This is $v_2(1+p+\cdots+p^e)$, by parity for even $e$ and the difference-of-powers factorization for odd $e$. Thus

$$
 v_2(r_4(n))=3+\sum_{p\mid n,\,p\ {\rm odd}}b_p(v_p(n)).
$$

For $r_3(n)>0$, the prime-square factor in the preceding formula is odd whenever $p\nmid d$, since $\sum_{i=0}^a1-\sum_{i=0}^{a-1}1=1\bmod2$. For $p\mid d$ the Legendre symbol vanishes. Hence

$$
 v_2(r_3(n))=v_2(r_3(d))+
 \sum_{p\mid d,\,p\ {\rm odd}} b_p(\lfloor v_p(n)/2\rfloor).
$$

The least significant source bit of a nonzero coefficient lands at fractional position $kn-v_2(r_j(n))$ (positions at or below zero are integral). This identity locates that bit before different coefficients are added.

**Exact column identity (Paper proof, objectives 3 and 4).** Put $B=2^k$, $c_n=r_j(n)$ and $C_M=\lfloor\sum_{h\ge1}c_{M+h}B^{-h}\rfloor$. The integer $P_M=\lfloor B^M x_{j,k}\rfloor$ is exactly $\sum_{n=0}^M c_n B^{M-n}+C_M$. Expand all these summands in binary and let $K_M$ be the sum of the outgoing carry amounts over all columns, including final propagation. If $d_i$ is the number of input ones in column $i$, and $b_i$ is the output bit, $d_i+u_{i-1}=b_i+2u_i$, $u_{-1}=0$. Summation gives the exact identity

$$
 kM f_1(kM;x_{j,k}) =
 \sum_{n=0}^M s_2(c_n)+s_2(C_M)-K_M-s_2(\lfloor x_{j,k}\rfloor).
$$

The lattice count gives $c_n\le (2\lfloor\sqrt n\rfloor+1)^j\le81(n+1)^2$. Thus $s_2(C_M)=O(\log(M+2))$ and for fixed $k$ simple normality is equivalent to
$\sum_{n=0}^M s_2(c_n)-K_M=kM/2+o(M)$. Partial blocks change the digit count by at most $k$. By Theorem 2 together with the column identity (since the left-hand side is at most $kM$), both raw input mass per block and total carry per block tend to infinity. Subtracting them to accuracy $o(M)$ is necessary here.

For varying $k$ there is a different, unconditional conclusion. If $B>11\cdot81(M+1)^2$, each of the first $M$ positive-index coefficients fits in one block and $C_M=0$. Indeed $\sum_{h\ge1}(h+1)^2 B^{-h}\le 4/(B-4)<11/B$ for $B\ge8$. The first $kM$ fractional bits then contain exactly $\sum_{n=1}^M s_2(c_n)$ ones. In particular the proportion tends to zero when $k=k(M)\gg\log M$ with $k/\log M\to\infty$. This describes prefixes of a varying family. **Open.** For each full cube and fourth power at fixed $k$, including $k=1$, determine the binary one-frequency, transition density and normality. Neither an asymptotic $s_2(r_3(n))\sim\frac14\log_2 n$ nor its four-square analogue is used or established here.

## 3. Higher Euler powers, derivatives and prime coefficients

Let $D=q\,d/dq$ act on the series before evaluation. **Prior result (GF-27, Corollary D4.15) and restated criterion (Paper proof, objective 4; following GF-27 Corollary D4.9′).** For coefficients $c_n$ of $E^4,E^6,E^8,D(\Theta_3^2)$ the local minimum signed weight through $M$ is $\asymp M\sqrt{\log M}$; for $D(E^2)$ it is $\asymp M(\log M)^{1/4}$ (inherited from GF-27, Corollary D4.15, via the CM prime-coefficient multiplicity bound for the eta powers and divisor/support asymptotics for the derivatives). Thus they still diverge per binary digit after division by any fixed $kM$, including for $E_{2^k}^4$. The exact remaining signed criterion for each of these full values is

$$
 \sum_{n\ge0}c_n2^{-kn}\in K_2
 \quad\Longleftrightarrow\quad
 w\left(\sum_{n=0}^M c_n2^{k(M-n)}\right)=o(M).
$$

Indeed all five sequences grow polynomially, so the integral part of the rescaled tail has signed weight $O(\log M)$. Signed weight is subadditive and symmetric under negation, so removing the tail changes weight by at most that amount. Removing the integer part of the real times $2^{kM}$ costs $O(1)$. For the resulting nonnegative binary prefix, each run of ones has a representation as a difference of two powers of two. Conversely, adding or subtracting a power of two changes the transition count of the two’s-complement bits by at most two, since the carry or borrow flips a run and the neighboring bit, preserving the interior transitions up to its two boundaries. Thus prefix signed weight is sublinear exactly when adjacent unequal bits have density zero. The binary characterization of $K_2$ identifies the latter condition; partial blocks of fixed length cost $O(k)$. **Open.** For these five full sequences it remains to control the weight after summing across indices. [GF-27, §§3.2–3.7](../phase22/partitions-carry-and-lemma-s.md#3-d4-signed-digits-and-carry-cancellation) · [Phase 24, signed transfer theorem](../phase24/dense-digit-mass-and-lambert.md)

### Theorem 4. Nonnormal prime subseries

**Paper proof, objectives 2 and 3.** Write $a_f(p)$ for the (integer) Fourier coefficient at a rational prime of the normalized eigenform ($a_f(1) = 1$) $f=\eta(6\tau)^4,\eta(4\tau)^6,\eta(3\tau)^8$, respectively, of weights $w_f=2,3,4$. In the eigenform’s Fourier index define $y_{f,k}=\sum_p a_f(p)2^{-kp}$. Then

$$
 \limsup_N(f_{01}+f_{10})(N;y_{f,k})\le \frac{w_f-1}{4k\log2}.
$$

Consequently the prime subseries fail binary normality of order two for $k\ge1,2,3$, respectively. Their lower extreme interval discrepancy $D^-(y_{f,k}; 2) = \liminf_N D_N(y_{f,k}; 2)$ is at least $1/2-(w_f-1)/(4k\log2)$ when positive. The two transition cylinders form the single interval $[1/4,3/4)$.

**Proof and external inputs.** The three forms have CM by $\mathbb Q(\sqrt{-3}),\mathbb Q(i),\mathbb Q(\sqrt{-3})$, respectively. Away from the level, inert prime coefficients vanish and split coefficients have $|a_f(p)|\le2p^{(w_f-1)/2}$ by the Hecke character formula. These are the same identifications used in GF-17 and GF-27. The split primes are one reduced class modulo 3 or 4 and their count is asymptotic to $X/(2\log X)$. A binary NAF for a nonzero integer of magnitude $A$ has at most $\frac12\log_2 A+O(1)$ nonzeros: if its highest position is $j$, the lower positions have magnitude at most $2^{j-2}+2^{j-4}+\cdots\le2^j/3$, and adjacent positions cannot both occur. Hence the sum of signed weights is at most $((w_f-1)/(8\log2)+o(1))X$. Two transitions per signed digit and the $O(\log N)$ tail prove the bound. It concerns a prime Fourier subseries; in the original Euler index the exponent corresponding to $p$ would be $(p-1)/6,(p-1)/4,(p-1)/3$, respectively. [CM forms and coefficient formulas](../phase21/partitions-and-higher-modular.md#24-serres-lacunary-eta-powers)

In those original Euler indices the same proof multiplies the transition ceiling by $6,4,3$, respectively, since the prime index reaches $6M+1,4M+1,3M+1$ in $M$ coefficient positions. This proves failure of order-two normality in the prime components of the original stretched Euler powers for $k\ge5,6,7$, respectively. The analogous prime component of $D(E^2)$ uses $m=(p-1)/12$ and coefficient $\pm2m$ for $p\equiv1\bmod12$. There are $(3+o(1))M/\log M$ of these through $m=M$. Since $w(2m)=w(m)\le\frac12\log_2 M+O(1)$, the transition ceiling is $3/(k\log2)$, strictly below $1/2$ for $k\ge9$.

There is a stronger single-digit conclusion for the prime part of the theta derivative, in its original index. For every $k\ge1$,

$$
 \limsup_N f_1\left(N;\sum_p p\,r_2(p)2^{-kp}\right)
 \le\frac{1}{4k\log 2}<\frac12 .
$$

Indeed $r_2(p)=8$ for $p\equiv1\bmod4$ and zero for $p\equiv3\bmod4$. The prime 2 costs a bounded number of bits. Among integers with at most $J$ bits, those with more than $(1/2+\epsilon)J$ ones number $O_\epsilon(2^{(1-c_\epsilon)J})$ by the binomial theorem (apply a weight $t^r$ with $t>1$ sufficiently close to 1). At $J=\lceil\log_2(X+1)\rceil$ their contribution even among all integers is $o(X)$ bits. The other eligible primes contribute at most $(1/2+\epsilon)J$ each. The progression prime theorem and nonnegative digit subadditivity now give the bound as $\epsilon\downarrow0$. The lower discrepancy $D^- = \liminf_N D_N$ is at least $1/2-1/(4k\log2)$ by the single-digit interval. This conclusion is about simple nonnormality.

## 4. Reproduction and evidence

Run the standard-library verifier from the repository root.

~~~sh
python -B scripts/phase25_euler_theta.py
~~~

**Finite certificate.** The script uses integers and exact fractions. It checks the two outward bounds $106103/10^6<1/(3\pi)<106104/10^6$, the old $8K_*<25.431$, the large-prime sieve factor cancellation, and the finite valuation factor. It compares the CM coefficient formula with the pentagonal convolution through 6,000, checks both signs of the prime dilation, the layer count, the marked divisor weights, and a toy instance of the charging inequality. For $1\le n\le2200$ it compares theta convolution with three-square support, scaling, genus divisibility, reduced quadratic forms for squarefree $n\equiv1\bmod8$, Jacobi’s four-square formula, and minimum signed weight by independent dynamic programming. Binary column addition is checked against the head-plus-tail integer at stretches $1,2,4,30$. Sixty-four guard blocks and the polynomial lattice bound enclose the carry between rational endpoints with identical floors. It also expands the three eta products through Fourier index 400, checks inert-prime vanishing and the size bounds there, and certifies the stated stretch thresholds using a rational lower bound on log 2. The verifier is [phase25_euler_theta.py](../../scripts/phase25_euler_theta.py).

**Finite measurement.** The complete signed gap sum through 6,000 divided by 6,000 is $61/6000$. At the first 1,024 binary places the full theta cube has 515 ones and the fourth power has 527. At $k=30$ the respective first 30,720 bits have 2,249 and 4,110 ones. These are individual prefixes. All limiting claims in §§1–3 have separate paper arguments.

**Evidence scope.** The verifier passed on Windows and on Hail with exit code zero. The new results carry the label **Paper proof**. The named analytic and arithmetic theorems used above are **External input**. The stated equivalences identify the **Conditional** steps needed for further digit laws. The fixed-stretch full theta and higher Euler cases and the gap-weighted sign limit are **Open**. The objective numbers refer to the [standing research objectives](../../docs/research-objectives.md). The paper arguments have no Lean certificate here. Cross-model review is not independent human peer review.
