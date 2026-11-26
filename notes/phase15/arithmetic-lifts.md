# Arithmetic lifts of dyadic logarithm prefixes: Bézout lattices, balanced traces and a height–denominator obstruction

**Theorem A (completeness of the Gaussian alphabet; paper proof, exact checks).** Let $u=2^{-1/2}$. Call a monic integer polynomial $f$ with all roots $\alpha$ of the form $\alpha=2^{t}\zeta u^{n}$, with $\zeta$ a root of unity, $t\ge1$ and $n\ge1$ integers, a **flat trace source** $(f,t,n)$ (the same $t,n$ for every root). Put $p_j=\sum_\alpha\alpha^j$ and, for a real cutoff $x$,

```math
S_{f,t,n}(x)=\sum_{1\le j\le 2x/n}\frac{p_j}{j\,2^{tj}} .
```

At every real cutoff $x$, $S_{f,t,n}$ equals an explicit integer combination of the real sources $A_k=-\log(1-2^{-k})$ and Gaussian sources $G_t=-\log|1-(1+i)2^{-t}|^2$ at their Phase 14 cutoffs. For fixed finite rational formulas for $\ln2$ in this flat class, the least two distinct denominator rates are therefore $5/12$ and $13/30$. For instance, the degree-four source with roots $\sqrt2\,\zeta_{24}^{k}$, $k\in\{1,7,17,23\}$, satisfies $N_1=A_2-A_4+G_1+G_2$ at every cutoff.

**Theorem B (height–denominator obstruction; paper proof).** Let $S$ be a fixed finite combination $S=\sum_k a_kA_k+\sum_t b_tG_t$ with integer or rational coefficients with $S(\infty)=\log2$, and put $C=\sum|a_k|+2\sum|b_t|$. Let $X(C)$ be the least positive integer with $2^{X(C)}>4C/0.69$. Then $S(x)>0$ for every $x\ge X(C)$. Hence the denominator rate satisfies $\rho(S)\ge 1/X(C)$, and a cell on which $S$ vanishes with left endpoint $x_0$ costs height $C\ge(\log2/4)\,2^{x_0}$. Saving a band of primes costs an exponentially large weighted height.

**Theorem C (balance and the exponent gap; paper proof, exact examples).** Let $f$ be monic with integer coefficients, $f(0)\ne0$, and $d=\deg f\ge1$. Write $2^A$ for the largest complex root modulus and $\mu$ for the least root valuation over $\mathbb Q_2$, normalized by $v(2)=1$. Then $\mu\le A$, with equality precisely when all roots have the common form $2^{a/d}\zeta$ for a fixed nonnegative integer $a$ and roots of unity $\zeta$. If $\mu<A<t$, the cutoff $J=\lfloor N/(t-\mu)\rfloor$ gives unshifted precision exponent $(t-A)/(t-\mu)<1$ by the absolute tail estimate. Choosing $J=\lceil N/(t-A)\rceil$ gives shifted error $O(1/N)$ at a guaranteed cost of at most $N(A-\mu)/(t-A)+O(\log N)$ bits in the dyadic denominator. Section 4 measures both quantities for $\alpha=1+\sqrt{-7}$.

**Proposition D (Bézout).** For integers $a_1,\dots,a_k$, an integer solution of $\sum x_ia_i=c$ exists if and only if $\gcd(a_i)\mid c$. In the alphabet of a finite set of sources this gives the exact set of multiples $m\log2$ that an integer combination can reach: $m$ must be divisible by an explicitly computable $g$, equal to $1$ for the Phase 14 alphabet and equal to $2$ or $3$ for the sub-alphabets $\{G_2,G_{1,-}\}$ and $\{G_3,G_{1,-}\}$.

These are paper results about rational prefix functions. The affine feasibility and error lemmas have separate Lean proofs. [Arithmetic computations](../../scripts/phase15_arithmetic.py) · [Lean statements](../../NormalityChecker/AffineDenominator.lean)

## 0. Contents of the result

| Result | Status | Evidence |
| --- | --- | --- |
| Bézout lemma and target lattice (Proposition D, §2) | Paper proof, exact computation | Integer kernel by unimodular column reduction; brute-force box search; certificates verified in the script |
| Prefix-level relations equal multiplicative relations of root multisets (Theorem 2, §3) | Paper proof | Power-series argument; 24 elementary sources checked independent |
| Completeness of $\{A_k,G_t\}$ for flat sources (Theorem A, §3) | Paper proof | 1008 orbit sources decomposed and compared as multisets; $N_1$ identity at 400 cutoffs |
| Exponent gap and balance (Theorem C, §4) | Paper proof and finite example | Newton-polygon data for seven sources; measured loss for $1+\sqrt{-7}$ to $N=300$ |
| Frobenius congruence for arbitrary traces and correct truncation (§5) | Paper proof | 1800 polynomial triples; 577 support occurrences across six source families, mismatches 0 |
| Support and future-window tests (§5, §7) | Definition plus exact computation | Table in §7 |
| Height–denominator obstruction (Theorem B, §6) | Paper proof | Tail bound at every cutoff through $x=30$ for eight sources; 3993 formulas enumerated |
| Atlas of Taylor, Gaussian, algebraic, beta, Padé and Hermite–Padé sources (§7) | Finite computation | Table in §7 |

The enlarged Phase 14 optimality (Theorem A) rests on the Phase 14 theorem as an input, which in turn uses Grechkoseeva's primitive-divisor theorem. [Phase 14 optimal rate](../phase14/gaussian-relations.md) · [Phase 14 checkpoint](../phase14/README.md)

## 1. Setting and notation

A **source** is a triple $(f,t,n)$: a monic integer polynomial $f$ of degree $d$ with roots $\alpha$, an integer $t$ with $|\alpha|<2^t$, and an integer $n\ge1$. Its prefix at the real cutoff $x$ is the displayed $S_{f,t,n}(x)$ above. The infinite value is

```math
S_{f,t,n}(\infty)=-\sum_\alpha\log(1-\alpha 2^{-t})=dt\log2-\log|f(2^t)| ,
```

because $\prod_\alpha(2^t-\alpha)=f(2^t)$. The real source $A_k$ is $f=X-1$, $t=k$, $n=2k$. The Gaussian source $G_t$ is $f=X^2-2X+2$ with roots $1\pm i$, $n=2t-1$. Its terms are $2\,\mathrm{Re}((1+i)^j)/(j2^{tj})$, as in Phase 14. The sign twins $A_{k,-}$ and $G_{t,-}$ use $f=X+1$ and $f=X^2+2X+2$.

The **shifted prefix** at the integer cutoff $N$ is $Y_N=2^NS(N)$, and its **rate** is $\rho=\lim(\log q_N)/N$ where $q_N$ is the reduced denominator. Cutoffs are always **homogeneous**: the condition for index $j$ is the integer inequality $n j\le 2N$, applied to each source before multiplication by its coefficient, and at a prime $p$ the condition becomes $njp\le 2N$ with no rounding of $N/p$. A cutoff rule is *correct* if it has this form. §5 shows why. The notation $\log$ is natural. For the rate formula of Phase 14,

```math
\rho(S)=\int_{\{x>0:\,S(x)\ne0\}}\frac{dx}{x^2},
```

which holds for fixed finite rational combinations of $A_k,G_t$ and, by Theorem A, for fixed finite combinations of all flat sources. [Phase 14 prime bands](../phase14/gaussian-relations.md#rational-prefixes-and-their-prime-bands)

## 2. The Bézout lemma and what it decides

**Lemma (Bézout).** The set $\{\sum x_ia_i:x_i\in\mathbb Z\}$ is the ideal $g\mathbb Z$ with $g=\gcd(a_1,\dots,a_k)$. Therefore $\sum x_ia_i=c$ is solvable in integers exactly when $g\mid c$, and an iterated extended Euclidean algorithm produces a certificate.

*Proof.* The set is an ideal of $\mathbb Z$, hence principal. It contains each $a_i$, so $g$ divides every element. Induction on $k$ with $g_2=\gcd(g_1,a_k)=ug_1+va_k$ shows $g$ itself is attained. $\square$

**Target lattice.** Let sources $s_1,\dots,s_k$ have infinite values $V_i=\sum_p e_{ip}\log p$, with exponent vectors read from the factorization of $f(2^t)$ together with $dt\log 2$. Let $E$ be the matrix of odd-prime exponents and $c_i=e_{i,2}$. An integer relation $\sum x_iV_i=m\log2$ holds if and only if $Ex=0$ and $c\cdot x=m$, by unique factorization. Let $K$ be an integer basis of $\ker E$. By the Lemma applied to the numbers $c\cdot\kappa$, $\kappa\in K$, **$m$ is reachable exactly when $g\mid m$ with $g=\gcd_{\kappa\in K}(c\cdot\kappa)$**. If $K$ is empty then only $m=0$ is reachable.

| Alphabet | Rank of $\ker E$ | Reachable $m\log2$ |
| --- | ---: | --- |
| $A_1,A_2,A_3,A_4,A_6,G_1,G_2,G_3$ (Phase 14) | 5 | all integers $m$ ($g=1$); the relations with $m=0$ have rank 4 |
| $G_2,G_{1,-}$ | 1 | $m$ even: $G_2-G_{1,-}=2\log2$ |
| $G_3,G_{1,-}$ | 1 | $m$ divisible by 3: $G_3-2G_{1,-}=3\log2$ |

Here $G_{1,-}=\log2-\log5$, $G_2=3\log2-\log5$ and $G_3=5\log2-2\log5$. The script finds these sub-alphabets by enumerating pairs of signed sources, verifies every certificate exactly, and confirms by brute force over $|x_i|\le9$ that nothing outside the multiples of $g$ occurs. A gcd greater than one excludes an integer formula for the unscaled target in that alphabet.

**Cell lattice and denominator lattice.** The same Lemma describes the values taken by integer combinations at a fixed cutoff cell. At $v=12$ the eight Phase 14 cell values have common denominator $443520$, their numerators have gcd $1$, and every nonzero integer combination is therefore at least $1/443520$ in absolute value, attained by a Bézout certificate. For two reduced fractions with denominators $q_1,q_2$ the set $\mathbb Zq_1^{-1}+\mathbb Zq_2^{-1}$ equals $\mathrm{lcm}(q_1,q_2)^{-1}\mathbb Z$. This is the CRT bookkeeping behind the two-factor splits $a/A+b/B$ of [the transition-window experiment](../phase14/transition-windows.md).

**Prefix level versus value level.** A relation among infinite values ($\ker E$) is much weaker than a relation among prefix functions. Whether a candidate source is *nonredundant* depends on the second, which §3 classifies completely for flat sources.

## 3. Prefix-level relations and the completeness theorem

Write $e(\theta)=e^{2\pi i\theta}$ for $\theta\in\mathbb Q/\mathbb Z$ and let $\mathbb Z[\mathbb Q/\mathbb Z]$ be the group ring of finite multisets. For a flat source put $\alpha/2^{t}=e(\theta_\alpha)u^{n}$ and let $\Theta=\sum_\alpha[\theta_\alpha]$. Let $\nu_n$ be the **distribution operator** that replaces each $[\theta]$ by the $n$ elements $[(\theta+m)/n]$, $0\le m<n$, the $n$th roots of $e(\theta)$.

**Theorem 2.** For flat sources $s_i$ with root multisets $\Theta_i$ and integer coefficients $c_i$, one has $\sum c_iS_i(x)=0$ for **all real $x$** if and only if $\sum c_i\nu_{n_i}(\Theta_i)=0$ in $\mathbb Z[\mathbb Q/\mathbb Z]$.

*Proof.* Since $p_j/2^{tj}=\sum_\alpha e(j\theta_\alpha)u^{nj}$, the prefix is the truncation at $u$-degree $2x$ of the formal series

```math
-\sum_\alpha\log\bigl(1-e(\theta_\alpha)u^n\bigr)=-\sum_{\xi}\log\bigl(1-e(\xi)u\bigr),
```

where $\xi$ runs over $\nu_n(\Theta)$. This uses $\prod_{\xi^n=c}(1-\xi w)=1-cw^n$. The coefficient of $u^m$ is $m^{-1}\sum_\xi e(m\xi)$, evaluated at $u=2^{-1/2}$. A combination vanishes at every cutoff if and only if each jump at $x=m/2$ vanishes, that is, if and only if all power sums $\sum_\xi c_\xi e(m\xi)$ vanish for $m\ge1$. For a finite signed multiset of roots of unity this is equivalent to the multiset being zero (Newton's identities, or the linear independence of characters). $\square$

The elementary sources have $\nu_{2k}[0]=Z_{2k}$, the set of $2k$th roots of unity (for $A_k$), and $\nu_{2t-1}(g)$ with $g=[1/8]+[7/8]$ (for $G_t$). The script confirms that $A_1,\dots,A_{12}$ and $G_1,\dots,G_{12}$ are linearly independent as functions of the cutoff (rank 24), recovering and extending the independence argument of Phase 14.

**Theorem A (completeness).** Let $\alpha=\sqrt2^{\,a}\zeta_M$ be an algebraic integer with $a\ge0$, $\zeta_M$ a primitive $M$th root of unity, and $f$ its minimal polynomial. For every $t$ with $2^t>|\alpha|$, the flat source $(f,t,n)$, $n=2t-a$, is an integer combination of $A_k$ and $G_t$ at every cutoff.

*Proof.* Compute the Galois orbit $\Theta$ of $\sqrt2^{\,a}\zeta_M$ as a set of points of $\mathbb Q/\mathbb Z$ and write $P_c=\sum_{\zeta\ \text{primitive }c\text{th}}[\zeta]$ and $Z_c=\sum_{\xi^c=1}[\xi]$. Möbius inversion gives $P_c=\sum_{d\mid c}\mu(c/d)Z_d$, and $\nu_nZ_d=Z_{nd}$, which is $A_{nd/2}$ when $nd$ is even.

* *$a$ even.* The orbit is $P_M$ and the source is $\sum_{d\mid M}\mu(M/d)A_{nd/2}$ with $n$ even.
* *$a$ odd, $8\nmid M$.* The real quadratic character of $\mathbb Q(\sqrt2)$ has conductor 8. Thus $\sqrt2\notin\mathbb Q(\zeta_M)$ and the orbit contains both signs: $\Theta=P_M\cup(P_M+\tfrac12)$ as a set, which is a sum of at most two sets $P_c$. If $M$ is odd the union is $P_M+P_{2M}$, and if $M=2m$ with $m$ odd it is $P_m+P_{2m}$. In either case $\sum_{d\mid m}\mu(m/d)Z_{2d}$ (with $m=M$ in the first case) gives only even indices. If $4\mid M$ the orbit is $P_M$ and $\mu(M/d)$ vanishes for odd $d$.
* *$a$ odd, $16\mid M$.* Here $\sqrt2\in\mathbb Q(\zeta_M)$ and $\sigma(\sqrt2)=\chi(\sigma)\sqrt2$ with $\chi(\sigma)=+1$ if and only if $\sigma\equiv\pm1\pmod 8$. The orbit is $\{\zeta_M^{\sigma+(M/2)[\sigma\equiv\pm3\,(8)]}\}$. Since $M/2$ is divisible by 8 and by every prime divisor of $M$, the map $\sigma\mapsto\sigma+(M/2)[\sigma\equiv\pm3]$ is an involution on a subset of the units, hence a bijection of $(\mathbb Z/M)^*$. The orbit is $P_M$ and the source is real.
* *$a$ odd, $M=8M'$ with $M'$ odd.* The same twist maps the 2-part of the orbit to $\{\zeta_8^{\pm1}\}$ or to $\{\zeta_8^{\pm3}\}$. Indeed, write the chosen primitive phase in its coprime CRT parts as $\zeta_8^b\omega$ with $b$ odd and $\omega$ primitive of order $M^\prime$. The twisted 8-exponents are $b\sigma+4[\sigma\equiv\pm3\bmod8]$, whose values are $\pm b\bmod8$ as $\sigma$ ranges over units. The CRT lets the odd component vary independently. Changing the chosen primitive phase can interchange these two orbits at the same conductor. So the orbit is $g*P_{M'}$ or $g'*P_{M'}$ with $g'=[3/8]+[5/8]=P_8-g$. For odd $d$ the $d$th roots of $\zeta_8^{\pm1}$ are $\zeta_8^{\pm c}\omega$ with $cd\equiv1\pmod 8$ and $\omega^d=1$. Hence $g*Z_d=\nu_d(g)$ if $d\equiv\pm1\pmod 8$ and $g*Z_d=\nu_d(g')$ otherwise, and symmetrically for $g'$. Then $\nu_m(g)=G_{(m+1)/2}$ and $\nu_m(g')=Z_{8m}-Z_{4m}-\nu_m(g)=A_{4m}-A_{2m}-G_{(m+1)/2}$. Summing over $d\mid M'$ with Möbius weights gives the combination. $\square$

The script implements all four cases, builds the explicit combination, and compares it with the directly computed multiset for **1008 sources** ($M\le240$ with $M\le48$ or $8\mid M$, $a\in\{0,1,2,3\}$, $t\le4$). Each multiset equality implies the prefix identity by Theorem 2. For conductor exactly divisible by 8, the script checks the opposite sign orbit as well. A reducible polynomial contributes the sum over its irreducible factors, counted with multiplicity.

**Corollary (Phase 14 optimality is alphabet-robust).** Let $S$ be any finite rational combination of flat sources (each a sum over minimal polynomials, since power sums are additive) with $S(\infty)=\log 2$. By Theorem A it equals, at every cutoff, a rational combination of $A_k$ and $G_t$ with the same reduced denominators $q_N$. The classification theorem of Phase 14 therefore applies: $\rho(S)\ge5/12$, with equality only for the prefix $2A_2+6A_3+10A_4-6A_6-5G_3$, and the next value is $13/30$. No enlargement by flat trace sources of any degree or phase changes these constants. [Phase 14 theorem](../phase14/gaussian-relations.md)

**The new degree-4 source.** Let $f_{24}=X^4-2X^3+2X^2-4X+4$. Its power sums are $p_j=2,0,8,8,-8,0,16,-32,\dots$ (all zero or signed powers of two), its roots are $\sqrt2\zeta_{24}^k$ for $k\in\{1,7,17,23\}$, and $f_{24}(2)=4$ gives $N_1(\infty)=4\log2-\log4=2\log2$. Valuation counting alone suggests an independent free parameter, because the target has no odd prime. The root multisets of $\{A_2,-A_4,G_1,G_2\}$ combine to $\{1,7,17,23\}/24$:

```math
Z_4-Z_8+\nu_1(g)+\nu_3(g)=\{1,7,17,23\}/24 .
```

So $N_1=A_2-A_4+G_1+G_2$ at all cutoffs. The script checks this identity in exact rational arithmetic at 400 half-integer cutoffs, directly from the power sums of $f_{24}$. Valuation-level admissibility does not imply prefix-level novelty. By Theorem A every flat source is an integer combination of the $A_k$ and $G_t$, with $G_t$ accounting for the complex-conjugate pairs.

**Other radii.** The flat-source theorem permits arbitrary algebraic degree but requires the common radius after normalization to be an integral power of $2^{-1/2}$. Roots of radius $2^{a/e}$ with reduced $e>2$ lie outside this classification.

## 4. Balance and the exponent gap

**Theorem C.** Let $f$ be monic integer with $f(0)=c_0\ne0$, largest root modulus $2^A$, and $\mu$ the smallest valuation of a root in an extension of $\mathbb Q_2$. Then

```math
\mu\ \le\ \frac{v_2(c_0)}{d}\ \le\ \frac{\log_2|c_0|}{d}\ \le\ A .
```

Equality $\mu=A$ holds if and only if $c_0=\pm2^a$ and every root equals $2^{a/d}\zeta$ with $\zeta$ a root of unity.

*Proof.* The chain is $\sum_\alpha v(\alpha)=v_2(c_0)\le\log_2|c_0|=\sum\log_2|\alpha|$ together with $\min\le$ average $\le\max$. If $\mu=A$ then $v(\alpha)\ge A$ and $|\alpha|\le2^A$ for every root, while $v_2(c_0)=\sum v(\alpha)\ge dA$ and $|c_0|=\prod|\alpha|\le2^{dA}$. Since $|c_0|\ge2^{v_2(c_0)}$ all inequalities are equalities: $|c_0|=2^{dA}=2^{v_2(c_0)}$, so $c_0=\pm2^a$ with $a=dA$, every $|\alpha|=2^A$ and every $v(\alpha)=A$. For a root $\alpha$ the number $\beta=\alpha^d/2^a$ is a $2$-adic unit at every place above 2 (valuation $dA-a=0$), integral at every odd prime since $\alpha$ is an algebraic integer and the denominator is a power of two, and has all conjugates of modulus 1. By Kronecker's theorem $\beta$ is a root of unity. The converse is immediate. $\square$

**Consequences for truncation.** Let $B=2^t>2^A$, $\mu\le A<t$, and take the prefix with $J$ terms, shifted by $2^N$. Since $v_2(p_j)\ge\mu j$, the term $2^Np_j/(jB^j)$ has 2-adic valuation at least $N-j(t-\mu)-\log_2j$. The omitted tail is bounded by $d\,2^{-(J+1)(t-A)}/\bigl((J+1)(1-2^{A-t})\bigr)$. Hence:

* the *guaranteed* 2-adic denominator exponent is at most $\max(0,J(t-\mu)-N)+\log_2J$;
* the *guaranteed* error of $2^N\cdot$value is at most $2^{N-(J+1)(t-A)}$ up to a constant.

At $J=\lfloor N/(t-\mu)\rfloor$ the guaranteed 2-adic excess is $O(\log N)$. Before multiplication by $2^N$ the geometric error has precision exponent $\kappa=(t-A)/(t-\mu)$. At $J=\lceil N/(t-A)\rceil$ the shifted error is $O(1/N)$ and the guaranteed denominator excess is at most $N(A-\mu)/(t-A)+O(\log N)$. For intermediate $J$, the two leading exponents in these upper estimates are $E=J(t-\mu)-N$ and $S=N-J(t-A)$, so $(t-A)E+(t-\mu)S=(A-\mu)N$. Additional cancellation can improve an actual prefix.

**Flat-source denominators.** With $r=t-n/2$, every root has valuation $r$ at every place over 2. For $nj\le2N$, the shifted summand has valuation at least $N-nj/2-v_2(j)\ge-v_2(j)$. Its odd denominator divides $j$. Thus the full prefix denominator divides $\mathrm{lcm}(1,\dots,\lfloor2N/n\rfloor)$, and the geometric estimate gives shifted error $O(1/N)$.

| Source (root description) | $t$ | $\mu$ | $A$ | Balanced | Largest odd part of $p_j$, $j\le80$ | $\kappa$ |
| --- | ---: | ---: | ---: | --- | ---: | ---: |
| $1+i$ | 2 | 1/2 | 0.5000 | yes | 1 | 1 |
| $\sqrt2\zeta_{24}$ (degree 4) | 2 | 1/2 | 0.5000 | yes | 1 | 1 |
| $2\zeta_6$ | 2 | 1 | 1.0000 | yes | 1 | 1 |
| $\sqrt2$ | 2 | 1/2 | 0.5000 | yes | 1 | 1 |
| $1+\sqrt{-7}$ | 3 | 1 | 1.5000 | no | $1.8\times10^{12}$ | 0.7500 |
| $1+\sqrt2$ | 2 | 0 | 1.2716 | no | $2.1\times10^{30}$ | 0.3642 |
| $1+\zeta_8$ | 3 | 1/4 | 0.8858 | no | $1.0\times10^{15}$ | 0.7688 |

**An exact unbalanced example.** For $\alpha=1+\sqrt{-7}=2\omega$ with $\omega^2-\omega+2=0$, one has $p_j=2^j\,\mathrm{Tr}(\omega^j)$ and $\mathrm{Tr}(\omega^j)$ odd for all $j\ge1$ (Newton's identity $p'_j=p'_{j-1}-2p'_{j-2}$ gives $p'_j\equiv1\pmod 2$). The script confirms this through $j=399$. So the exact dyadic exponent is $e(j)=2j$, $\mu=1$, $A=3/2$, and at $t=3$ the infinite value is $3\log 2-\log 7$, the same as $A_3$. With $J=N/2$ (exact exponent) the measured loss is $S=\log_2|2^N\text{value}-Y|$; with $J=2N/3$ (full precision) the measured 2-adic denominator is $E$ bits. The guaranteed values are $N/4$ and $N/3$.

Here $S=\log_2|2^N\,\mathrm{value}-Y|$ and $E$ is the 2-adic exponent of the reduced denominator of $Y$.

| $N$ | $S$ at $J=N/2$ (predicted $N/4$) | $E$ at $J=2N/3$ (predicted $N/3$) |
| ---: | ---: | ---: |
| 40 | 4.92 | 14 |
| 90 | 16.33 | 32 |
| 150 | 29.50 | 52 |
| 300 | 66.88 | 103 |

In these four cases the script compares the measured values with $N/4$ and $N/3$ to logarithmic tolerance. The denominator exponent is exact. The logarithmic error uses a high-precision numerical evaluation. The general proof supplies upper bounds.

## 5. Frobenius congruences, correct truncation, support and future window

**Lemma (trace Frobenius).** For every monic integer polynomial $f$, every prime $p$ and every $\ell\ge1$,

```math
p_{p\ell}\equiv p_\ell\pmod p .
```

*Proof.* In $\mathbb Z[e_1,\dots,e_d]$ the power sum $p_p$ in the roots $\beta_i=\alpha_i^\ell$ satisfies $p_p(\beta)\equiv e_1(\beta)^p\pmod p$, because $(\sum\beta_i)^p\equiv\sum\beta_i^p$ modulo $p$ in the polynomial ring. The elementary symmetric functions of the $\beta_i$ are integers, and Fermat gives $e_1^p\equiv e_1$. $\square$

No splitting or inertia hypothesis occurs; the case of $\mathbb F_p[i]$ in Phase 14 is the case $f=X^2-2X+2$. [Phase 14 Frobenius step](../phase14/gaussian-relations.md#rational-prefixes-and-their-prime-bands)

**Proposition (shadow).** Let $S$ be a fixed finite combination $S=\sum c_iS_{f_i,t_i,n_i}$ with rational $c_i$, let $J=\max\lfloor2N/n_i\rfloor$, and let $p$ be an odd prime with $p^2>J$ and $p$ prime to the denominators of the $c_i$. At the homogeneous cutoffs $n_ij\le2N$,

```math
pY_N\equiv 2^N\sum_ic_i\sum_{\ell\le2N/(n_ip)}\frac{p_\ell}{\ell\,2^{t_i\ell}}\pmod p ,
```

where the right side is $p$-integral and **the cutoff on $\ell$ is the integer inequality $n_ip\ell\le2N$**. In particular $p$ divides the reduced denominator of $Y_N$ exactly once if the right side is nonzero modulo $p$, and not at all if it is zero. This holds for *any* integer $n_i$, balanced or not.

*Proof.* Multiplying by $p$ leaves modulo $p$ only the indices $j=p\ell$ with $\ell<p$, since $p^2>J$. The Lemma and Fermat give $p_{p\ell}/2^{tp\ell}\equiv p_\ell/2^{t\ell}$. The index condition $nj\le2N$ for $j=p\ell$ is the stated inequality. $\square$

**Why the truncation must be homogeneous.** The script checks the Proposition at every eligible odd prime $p\le J$, for $N\in\{61,100,157,233\}$, and reports the following (mismatches between the predicted and the actual presence of $p$ in the denominator: 0 everywhere).

| Source | Support primes tested | Mismatches | Mismatches if $N/p$ is rounded down first |
| --- | ---: | ---: | ---: |
| $A_1$ | 112 | 0 | 0 |
| $G_3$ | 49 | 0 | 8 |
| $N_1$ (degree 4, $t=1$) | 204 | 0 | 100 |
| $N_2-3G_2$ (mixed degrees and strides) | 74 | 0 | 18 |
| $1+\sqrt{-7}$, analytic cutoff $n=3$ | 77 | 0 | 19 |
| $1+\sqrt{-7}$, exact-exponent cutoff $n=4$ | 61 | 0 | 0 |

The worked case is $G_3$ at $N=13$, $p=5$: the homogeneous test $5\cdot1\cdot5\le26$ retains the index $\ell=1$, whereas rounding $13/5$ down to 2 gives $5\ell\le4$ and loses it, as in Phase 14. A second incorrect rule is the crude cutoff $tj\le N$, which ignores that $v_2(p_j)\ge j/2$ for $G_t$. It satisfies the Frobenius identity but loses precision: for $G_3$ the error of $2^N\cdot$value is $9.6\times10^{-3}$ and $4.9\times10^{-3}$ at $N=60$ and $120$ with the correct rule $nj\le2N$, but $11.7$ and $6150$ with $tj\le N$.

**Construction of a new algebraic trace source.** Given a monic integer $f$, a base exponent $t$ and the integer $n$:

1. compute $p_j$ from the Newton identities (equivalently, the trace of the $j$th power of the companion matrix);
2. test balance (Theorem C). If flat, use the homogeneous cutoff $nj\le2N$, with $n=2(t-r)$ for $2^r=|\alpha|$;
3. multiply by the coefficient *after* cutting each source;
4. at a prime $p$ use $n j p\le2N$ and the congruence above.

The half-integral cutoff applies to flat sources. For a balanced source of another radius, choose $J$ directly from Theorem C. The odd-prime congruence above applies to any specified integer stride; the geometric and 2-adic estimates retain their separate hypotheses.

**Support and future window.** For each odd support prime $p$ at shift $N$, let $W_p$ count the consecutive future shifts (capped at $N$ here) at which the $p$-primary component agrees with that of the shifted original prefix. The exact test at shift $j$ is that $Y_{N+j}-2^jY_N$ has denominator prime to $p$. It also covers primes whose square occurs. Define $m(w)=\sum_{W_p\ge w}\log p/\sum_{p\mid\mathrm{den}(Y_N),\,p>2}\log p$. The separate precision window is the largest $j\ge0$ with $2^j|2^Nx-Y_N|\le 2^{-8}$, with an empty window when the initial error exceeds the tolerance. [Phase 14 future windows](../phase14/transition-windows.md)

## 6. The weighted height–denominator obstruction

**Weights.** Give $A_k$ weight 1 and $G_t$ weight 2 (the number of conjugates), and put $C(S)=\sum w|{\rm coefficient}|$. This is the weighted height used in the Phase 14 optimization.

**Theorem B.** Let $S$ be a fixed finite combination $S=\sum a_kA_k+\sum b_tG_t$ with $S(\infty)=\log2$.
1. $|S(x)-\log2|\le4C\,2^{-x}$ for all $x\ge0$.
2. $S(x)>0$ for $x\ge X(C)$, where $X(C)$ is the least integer with $2^{X}>4C/0.69$.
3. $\rho(S)\ge1/X(C)$.
4. If $S$ vanishes on a half-integer cell $[v/2,(v+1)/2)$, then $2^{v/2}\le4C/\log2$.

*Proof.* (1) For $A_k$, with $m=\lfloor x/k\rfloor$, the omitted tail $\sum_{j>m}2^{-kj}/j\le 2\cdot2^{-k(m+1)}\le2\cdot2^{-x}$. For $G_t$ with $|z|=2^{-n/2}\le2^{-1/2}$ and $m=\lfloor2x/n\rfloor$, the tail is at most $2|z|^{m+1}/(1-|z|)\le2\cdot2^{-x}/(1-2^{-1/2})\le 6.83\cdot2^{-x}\le8\cdot2^{-x}$ since $n(m+1)>2x$. Summing with weights gives (1); the script checks both per-source bounds at every half-integer cutoff through $x=30$. (2) $\log2>0.69$. (3) By the Phase 14 rate formula, $\rho(S)=\int_{S\ne0}x^{-2}dx\ge\int_{X}^\infty x^{-2}dx=1/X$. (4) $S=0$ at $x=v/2$ forces $\log2\le4C2^{-v/2}$. $\square$

The same geometric bound applies directly to a flat source of degree $d$ with weight $d$, since each normalized root has modulus at most $2^{-1/2}$. The fixed finite formula must be chosen before the limit in the rate integral. Formulas with coefficients varying with $N$ require uniform estimates of their own. By Theorem B a nonzero cell at large $x$ cannot be avoided: *killing a band of primes with $N/p\ge x_0$ requires height exponential in $x_0$*.

**Exact enumeration.** The script enumerates the integer formulas for $\log2$ in the Phase 14 alphabet (the parameters $(a,u,b,c)$ solve the valuation system, which determines each vector), with $|a|,|b|,|c|\le5$ and $|u|\le1$ — **3993 formulas** — computing each rate exactly from its cells below $X(C)$ and the certified tail. The lowest rate at each height forms the frontier below. It reproduces $13/30$ and $29/60$ at the vectors listed in Phase 14 and finds nothing below $5/12$.

| Weighted height $C$ | Least rate found | Parameters $(a,u,b,c)$ | Lower bound $1/X(C)$ |
| ---: | --- | --- | --- |
| 1 | 1 | $(1,0,0,0)$ | 1/3 |
| 4 | 1/2 | $(0,0,0,0)$ | 1/5 |
| 16 | 13/30 | $(0,0,0,-2)$ | 1/7 |
| 34 | 5/12 | $(0,0,0,-5)$ | 1/8 |

Every enumerated vector satisfies $\rho\ge1/X(C)$, and every vanishing cell satisfies item 4; with $u\ne0$ the rate is at least 1, as in Phase 14. The obstruction is far from sharp in this alphabet: it gives $1/8$ where the truth at $C=34$ is $5/12$. The gap plausibly reflects the rank limit of the alphabet rather than height, though that is not proved here. Theorem B is a *necessary* cost on any improvement. Theorem A shows that flat trace sources do not add independent sources.

## 7. Candidate sources and actual tests

The script reports for each candidate at shift $N$ the exact prefix $Y\approx2^N x$, the quantity $\log q/N$ (natural logarithm of the full reduced denominator), the 2-adic exponent of the denominator, the number of odd primes up to $4N$ (or $3N$) dividing it, the base-2 logarithm of $|2^Nx-Y|$, the precision window, and for homogeneous sources the minimal prime window and the masses $m(N/16)$, $m(N/4)$. For the homogeneous sources the Frobenius prediction of the support agrees with the actual denominator at every eligible prime.

| Source | $N$ | $\log q/N$ | 2-adic bits | Support | $\log_2$ error | Precision window | $\min W_p$ | $m(N/16)$ | $m(N/4)$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Taylor $A_1$ | 96 | 0.9248 | 5 | 23 | −6.6 | empty | 1 | 0.87 | 0.57 |
| Taylor $A_1$ | 192 | 0.9728 | 6 | 41 | −7.6 | empty | 1 | 0.84 | 0.46 |
| Gaussian minimizer (rate 5/12) | 96 | 0.3775 | 4 | 12 | −5.6 | empty | 1 | 0.63 | 0.09 |
| Gaussian minimizer (rate 5/12) | 192 | 0.3658 | 5 | 19 | −3.4 | empty | 0 | 0.71 | 0.18 |
| $N_1=G_1+G_2+A_2-A_4$ (target $2\log2$) | 96 | 1.9607 | 4 | 42 | −6.6 | empty | 1 | 0.90 | 0.64 |
| $N_1$ | 192 | 1.9802 | 5 | 74 | −7.6 | empty | 0 | 0.88 | 0.65 |
| Diagonal beta model (Paper V) | 96 | 1.8677 | 7 | 40 | −196.1 | 188 | – | – | – |
| Diagonal beta model | 192 | 1.9437 | 8 | 73 | −388.6 | 380 | – | – | – |
| Beukers–Padé, $n=13$ | 60 | 0.5114 | 0 | 6 | −6.0 | empty | – | – | – |
| Beukers–Padé, $n=26$ | 125 | 0.5014 | 0 | 7 | −7.1 | empty | – | – | – |
| Padé of the Gaussian trace, $n=14$ | 29 | 4.0987 | 0 | 5 | −5.3 | empty | – | – | – |
| Padé of the Gaussian trace, $n=28$ | 67 | 6.6029 | 0 | 8 | −6.3 | empty | – | – | – |

The denominators and precision windows are certified. The program encloses $\ln2$ in a dyadic interval, scales its endpoints by $2^N$ (and by 2 for $N_1$), then compares the smallest and largest possible errors with $2^{-8-j}$. The displayed logarithms and mass fractions are rounded. Support counts for Padé rows include only odd primes through $3N$.

At $N=192$, about 18% of the Gaussian minimizer's odd-prime log mass and 46% of the Taylor row's persist for $N/4$ shifts. Neither tested row meets the initial real-error tolerance. Their $O(1/N)$ bound eventually gives nonempty precision windows. The degree-four row targets $2\ln2$.

The diagonal beta correction supports 188 and 380 further shifts at the two displayed cutoffs. Its shifted error is at most $(N!)^2/(2N+1)!$ by the beta-integral remainder. [Paper V](../../papers/05-classical-denominators/paper.tex)

For the real Padé rows, expand $(y-1)^n(2-y)^n$ at $y=1+x$ to evaluate $I_n=\int_0^1 x^n(1-x)^n(1+x)^{-n-1}dx=c_n\ln2-r_n$. The rational is $r_n/c_n$ and the unshifted error is $I_n/|c_n|\le 4^{-n}/|c_n|$. The table evaluates the full reduced denominator after shifting. For the Gaussian Padé rows the linear system enforces order $2n+1$ at the origin. Evaluation at $1/2$ targets $-\ln2$, allowing the same rigorous dyadic error test. The two finite rates in either family do not determine a limiting rate.

* **Hermite–Padé.** Type I forms $Q_0+Q_1\log(1-z)+Q_2\log(1-z/2)=O(z^{3n+2})$ evaluated at $z=1/2$ give integer vectors $(a_0,a_L,a_3)$ with $a_0+a_L\log2+a_3\log3$ small. The script solves the linear system exactly and reduces the content:

| $n$ | $\log_2H$ | $-\log_2\|\text{form}\|$ | $P/\log_2 H$ |
| ---: | ---: | ---: | ---: |
| 1 | 3.9 | 8.5 | 2.18 |
| 2 | 8.6 | 13.7 | 1.59 |
| 3 | 12.0 | 18.7 | 1.56 |
| 4 | 16.4 | 23.8 | 1.45 |
| 5 | 23.6 | 25.4 | 1.08 |
| 6 | 27.8 | 30.4 | 1.09 |
| 7 | 34.6 | 32.5 | 0.94 |
| 8 | 38.8 | 37.5 | 0.97 |
| 9 | 42.7 | 42.6 | 1.00 |
| 10 | 49.6 | 44.7 | 0.90 |
| 11 | 57.2 | 46.2 | 0.81 |
| 12 | 61.4 | 51.1 | 0.83 |

In all twelve forms $a_3\ne0$. Here $H=\max(|a_0|,|a_L|,|a_3|)$ and $P=-\log_2|a_0+a_L\log2+a_3\log3|$. The displayed logarithmic heights and errors are numerical. A direct remainder bound is also available before numerical evaluation. For $Q_i(z)=\sum_{j=0}^n b_{ij}z^j$ normalized in the defining identity and $m=3n+2$, the coefficient at $z^k$, $k\ge m$, has magnitude at most $\sum_{i=1}^2\sum_j |b_{ij}|/(m-n)$ by the logarithm series. At $z=1/2$ the remainder is therefore at most $2^{1-m}\sum |b_{ij}|/(m-n)$. Scale this bound by the same factor used to clear denominators and divide out content. These are joint linear forms for two logarithms.

## 8. Prior art and attribution

* **BBP-type and Gaussian formulas.** Rational-prefix series for logarithms and arctangents in dyadic bases are the BBP family. Bailey's compendium collects them including Harley's real-part construction, and Phase 14 and Paper V develop the prime-band denominators. [Bailey, *A compendium of BBP-type formulas*](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf) · [Phase 14](../phase14/gaussian-relations.md)
* The trace and balance arguments use the ordinary cyclotomic distribution relation, Möbius inversion, and Kronecker's theorem for algebraic integers on the unit circle. The half-integral classification here compares the entire cutoff functions. The rate optimization is inherited from the Phase 14 result.
* The integral belongs to the classical logarithmic linear-form method of Alladi and Robinson. Rivoal's restricted-denominator lower bounds concern prescribed grids, including $2^m\mathrm{lcm}(1,\ldots,m)$ for $\ln2$. Neither result provides a lower mean cosine deficit on the binary orbit. [Alladi–Robinson](https://doi.org/10.1515/crll.1980.318.137) · [Rivoal, Theorem 4(ii)](https://rivoal.perso.math.cnrs.fr/articles/logconvergents.pdf)

## 9. Residual limits

* **Rates are not normality.** A denominator rate controls prime-band structure of a prefix. It supplies no equidistribution of the real orbit. Phase 14 records the obstruction that odd-primary data cannot see the equal-frequency 2-adic direction. [Primary components](../phase14/primary-components.md)
* **Unbalanced sources.** For $\alpha=1+\sqrt{-7}$ the phases are genuinely different from roots of unity. If $\alpha/|\alpha|$ were a root of unity, $\alpha^2/8$ would be an algebraic integer. At a place above 2 with $v_2(\alpha)=1$ it has valuation $-1$. The optimal rate after adjoining this source is open, as is the extension of the cutoff classification to balanced radii with reduced exponent denominator greater than two.
* **Finite tests.** The height search covers a specified coefficient box, and the stability and precision measurements cover the shifts in §7. The proof of the global minimum for the flat class uses Phase 14; the finite tests alone do not supply it.

## 10. Reproduction

```sh
python3 -B scripts/phase15_arithmetic.py          # about 20 seconds
python3 -B scripts/phase15_arithmetic.py --quick  # about 4 seconds
python3 -B scripts/phase15_arithmetic.py --only=roots,height
```

The program is dependency-free (standard library only). The root estimates, quadrature and logarithmic summaries include numerical diagnostics. The identities between root multisets, the rational denominators and the atlas precision windows use exact arithmetic. It prints each section's evidence and ends with `All Phase 15 arithmetic checks passed.` The two figures $5/12$ and $13/30$ and the vector $(0,0,-2,-3)$ with rate $29/60$ are reproduced by an implementation independent of `notes/phase14/gaussian_relations.py`.
