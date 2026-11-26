# The optimal denominator rate for real parts of dyadic Gaussian logarithms

**Theorem.** Represent $\log 2$ by a fixed finite rational linear combination of the Taylor series for $-\log(1-z)$, taking real parts, with arguments of the form

$$
z=\pm 2^{-k},\qquad z=(\pm1\pm i)/2^t,\qquad k,t\ge1.
$$

Include a Taylor term when its binary scale $-j\log_2|z|$ is at most the integer $N$. Multiply the resulting prefix by $2^N$ and call its reduced denominator $q_N$. The error in approximating $2^N\log 2$ is $O(1/(N+1))$. The limit of $(\log q_N)/N$ exists. Its **least value is $5/12$ and its second least value is $13/30$**. Each occurs at a unique prefix sequence. The classification allows arbitrarily large strides and rational coefficients of either sign. All logarithms in rates are natural.

Both minimizers already occur in Phase 13. The additional conclusions are the classification of all norm relations in this alphabet and the exclusion of every other prefix at these rates. The proof applies Grechkoseeva’s theorem on the two factors of $2^{2n}+1$ and compares affine linear forms exactly. The rate formula, descent and global optimization are paper deductions. Lean verifies the real coefficients, integer cutoff, sign pairing, real Frobenius congruence, small primitive-prime witnesses and the final valuation system. A Python certificate checks the finite band comparison. [Phase 13 construction and rates](../phase13/complementary-characters.md) · [Lean statements](../../NormalityChecker/GaussianLogarithmRelations.lean) · [Exact certificates](gaussian_relations.py)

## Rational prefixes and their prime bands

For a real scale $x\ge0$, let $A_{k,s}(x)$ be the sum of $(s2^{-k})^j/j$ over $1\le j\le x/k$, for $s=\pm1$. Put $z_t=(1+i)/2^t$, $n=2t-1$, and define

$$
G_{t,s}(x)=2\sum_{1\le j\le 2x/n}\frac{\Re((s z_t)^j)}{j}.
$$

The factor two makes the infinite value $-\log|1-s z_t|^2$. Conjugation covers the other two Gaussian phases. Write $A_k=A_{k,+}$ and $G_t=G_{t,+}$. Use the value at infinity for the sum of the whole series.

For $j$ starting at zero let $w_j$ repeat $(1,1,0,-1,-1,-1,0,1)$. Since $(1+i)^2=2i$ and $(1+i)^8=16$,

$$
\Re((s z_t)^j)=s^j w_j 2^{-e_t(j)},\qquad
e_t(j)=tj-\lfloor j/2\rfloor=\lceil nj/2\rceil.
$$

This is the exact dyadic exponent whenever the coefficient is nonzero. The integer insertion rule $e_t(j)\le N$ is equivalent to $nj\le2N$. The homogeneous cutoff $nj\le2x$ defines the short sum at nonintegral $x$. For instance at $t=3$, $N=13$, $p=5$, the term $j=p$ is retained and the short sum includes $j=1$ at $x=13/5$. Rounding $13/5$ down first loses it. The cutoff is applied to each phase before multiplication by its fixed coefficient.

Let $S(x)$ combine these prefixes, $Y_N=2^NS(N)$, $D$ clear the rational coefficients, and $M$ be the largest Taylor index allowed by any of the cutoffs at $N$. Then $M\le2N$ and $q_N\mid D\,\mathrm{lcm}(1,\ldots,M)$. In a phase of modulus $r$ with cutoff $m=\lfloor N/(-\log_2 r)\rfloor$, the unshifted omitted terms have total absolute value at most $r^{m+1}/((m+1)(1-r))$ before the fixed coefficient. Here $2^Nr^{m+1}\le1$, which proves the shifted error bound even for $t=1$.

For an odd prime $p\nmid D$ with $p^2>M$, multiplication by $p$ leaves only $j=p\ell$ in the residue modulo $p$. The new index bounds on $\ell$ are the bounds at $x=N/p$. In $\mathbb F_p[i]=\mathbb F_p[X]/(X^2+1)$, Frobenius sends $i$ to $i$ for $p\equiv1\pmod4$ and to $-i$ for $p\equiv3\pmod4$. The latter conjugation fixes the real coefficient. In the split case the same calculation holds in the quotient ring. Both prime classes therefore satisfy

$$
pY_N\equiv 2^N S(N/p)\pmod p.
$$

The right side is $p$-integral. Its residue is nonzero exactly when $p\mid q_N$. On a fixed half-open interval $[v/2,(v+1)/2)$, $S$ is constant and the corresponding primes satisfy $2N/(v+1)<p\le2N/v$. The logarithmic prime mass divided by $N$ tends to $2/(v(v+1))$ by the prime number theorem. The exact rate is

$$
\rho(S)=\sum_{\substack{v\ge1\\ S(v/2)\ne0}}\frac{2}{v(v+1)}.
$$

Indeed a nonzero rational short sum can lose primes dividing its numerator. With $K=\lceil N^{1/3}\rceil$, all first powers at $p\le K^2$ cost $O(K^2)$ and all higher powers in the common denominator cost $O(\sqrt N\log N)$. The fixed factor $D$ adds $O(1)$. For $p>K^2$ the short sums take $O(K)$ values, bounded in absolute value, with denominators dividing $D2^{K+1}\mathrm{lcm}(1,\ldots,2K)$. The product of their nonzero absolute numerators has logarithm $O(K^2)$. This bounds the total exceptional weight even before dividing by $N$. Since $S(x)\to\log2>0$, only finitely many cells vanish. This is the prime-band argument of Paper V with half-integer breakpoints. [Paper V, §§2 and 6](../../papers/05-classical-denominators/paper.tex) · [Phase 13 band audit](../phase13/reviews/classical-bands.md)

## Which identities preserve the prefix?

At **every real cutoff**, pairing opposite signs gives

$$
A_{k,+}+A_{k,-}=A_{2k},\qquad
G_{t,+}+G_{t,-}=A_{2n,-},\qquad n=2t-1.
$$

In the first identity only even powers remain. In the second only $j=4h$ remain, since $z_t^2=i2^{-n}$. The two terms at $j=4h$ combine to $(-2^{-2n})^h/h$, and $nj/2=2nh$ is exactly its real scale. Thus all signs may be reduced to $A_k,G_t$ without changing any truncation. The norm numerators for the two Gaussian signs are

$$
H_n^- = 2^n-2^{(n+1)/2}+1,\qquad H_n^+ = 2^n+2^{(n+1)/2}+1.
$$

They are coprime odd integers with product $2^{2n}+1$. The retained $G_t(\infty)=n\log2-\log H_n^-$ uses the smaller one. The real-part norm formula also appears in Harley's construction in Bailey's compendium. [Bailey, §§1–3](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf)

## A primitive prime in each norm factor

**Lemma (Grechkoseeva).** For every odd $n\ge7$, each of $H_n^-$ and $H_n^+$ has a prime divisor $p$ at which $2$ has multiplicative order exactly $4n$. This is the Suzuki case of Theorem 2 of Grechkoseeva, with parameters $(v,n,m)=(2,4,n)$ in her notation. The proof below specializes the cyclotomic argument to the Gaussian integer $1+i$. [Grechkoseeva, Theorem 2, corrected version](https://arxiv.org/html/2504.04729v1) · [Published paper](https://doi.org/10.1007/s10469-023-09722-1)

**Proof.** Write $\pi=1+i$ and fix $s=\pm1$. For odd $e$ let $U_e=|1-(s\pi)^e|^2$. As $s$ varies these are $H_e^-$ and $H_e^+$, possibly interchanged. Keep the sign of $s\pi$ fixed as $e$ varies. Let $C_n=|\Phi_n(s\pi)|^2$, where $\Phi_n$ is the cyclotomic polynomial. It is a positive rational integer and $U_n=\prod_{e\mid n} C_e$.

If $p\mid U_n$ then $2^{2n}\equiv-1\pmod p$. Its order is $4d$ for an odd $d\mid n$ and $p\equiv1\pmod4$. Choose the square root of $-1$ in $\mathbb F_p$ at which $1-(s\pi)^n$ vanishes. Such a root exists because the norm is the product of the two evaluations. The reduction of $s\pi$ has odd order dividing $n$. Its fourth power is $-4$, of order $d$ since $-4\equiv 2^{2d+2}$ and $\gcd(4d,2d+2)=4$. Thus $s\pi$ itself has order $d$ at this root. For divisors $e\mid n$ this gives $p\mid U_e$ when $d\mid e$. Conversely $p\mid U_e$ implies $2^{2e}\equiv-1$ and hence $d\mid e$.

When $d\mid e\mid n$, coprimality of the two factors gives $v_p(U_e)=v_p(2^{2e}+1)$. For odd $h=e/d$, the ordinary odd-prime lifting formula gives $v_p(2^{2e}+1)=v_p(2^{2d}+1)+v_p(h)$. This also follows by binomial expansion at $2^{2d}\equiv-1\pmod p$, factoring $h$ into a part prime to $p$ and powers of $p$. Möbius inversion in the product for $U_n$ now shows, when $d<n$, that $v_p(C_n)=1$ if $n/d$ is a positive power of $p$, and is zero otherwise. Indeed the constant valuations cancel and $v_p(h)=\sum_{a\ge1,\,p^a\mid h}1$. Consequently the product of all nonprimitive prime powers in $C_n$ divides $\prod_{p\mid n}p\le n$.

To force $C_n>n$, the cyclotomic product and $|\pi|=\sqrt2$ give

$$
|\Phi_n(s\pi)|\ \ge\ 2^{\varphi(n)/2}\prod_{e\ \mathrm{odd},\ e\ge1}(1-2^{-e/2})\ >\ 2^{\varphi(n)/2}/16.
$$

A factor entering with exponent $-1$ has relative modulus at least $1/(1+2^{-e/2})\ge1-2^{-e/2}$. For the product bound, $2^{-1/2}<3/4$, $2^{-3/2}<3/8$, and the sum over odd $e\ge5$ is less than $3/8$. The product therefore exceeds $(1/4)(5/8)^2>1/16$. For odd $n$, $\varphi(n)^2\ge n$ by the formula on prime powers. For integers $h\ge16$, $2^h\ge256h^2$, by induction from equality at 16. Thus $C_n>2^{\varphi(n)}/256\ge n$ whenever $\varphi(n)\ge16$.

The remaining odd $n\ge7$ have $\varphi(n)<16$, hence $n<256$. Counting coprime residues gives precisely the six rows below. For each displayed divisor, direct modular powering verifies that the first positive exponent giving one is $4n$. This proves the lemma for both norm factors. [Finite certificate](gaussian_relations.py) · [Kernel-checked witnesses](../../NormalityChecker/GaussianLogarithmRelations.lean)

| Odd index | Prime in the smaller factor | Prime in the larger factor |
| ---: | ---: | ---: |
| 7 | 113 | 29 |
| 9 | 37 | 109 |
| 11 | 397 | 2113 |
| 13 | 1613 | 53 |
| 15 | 61 | 1321 |
| 21 | 14449 | 1429 |

## All rational norm relations

Clear coefficient denominators in an identity for $m\log2$, then exponentiate and compare prime valuations. The real factor $A_k(\infty)=k\log2-\log(2^k-1)$ contains only odd primes at which the order of 2 divides $k$. An odd prime in $G_t$ has order dividing $4n$. The small indices $n=1,3,5$ have smaller norm numerators $1,5,25$ and contribute only the odd prime 5, of order four.

Take the largest of the occupied real indices $k>6$ and the indices $4n$ of occupied Gaussian terms with $n\ge7$. Call it $h$. If there is a Gaussian term at $h=4n$, the prime of order $h$ in $H_n^+$ can occur only in the real factor $2^h-1$ at this height. Its valuation forces that real coefficient to vanish if present. The prime of order $h$ in $H_n^-$ then forces the Gaussian coefficient to vanish. If there is only a real term at $h$, Bang's primitive-divisor theorem for $2^h-1$ gives a prime of order $h$ since $h>6$, again forcing a zero coefficient. Descent removes every such index. At $k=5$ the valuation at 31 removes $A_5$. [Bang's theorem in Paper V, §2](../../papers/05-classical-denominators/paper.tex) · [Zsigmondy's primitive-divisor theorem](https://doi.org/10.1007/BF01692444)

The surviving factors have the following values. Write $L=\log2$.

| Prefix | Infinite value | Prefix | Infinite value |
| --- | --- | --- | --- |
| $A_1$ | $L$ | $G_1$ | $L$ |
| $A_2$ | $2L-\log3$ | $G_2$ | $3L-\log5$ |
| $A_3$ | $3L-\log7$ | $G_3$ | $5L-2\log5$ |
| $A_4$ | $4L-\log3-\log5$ | $A_6$ | $6L-2\log3-\log7$ |

Put $B=2A_2+A_3-A_6$. The five prefixes $B,A_1,G_1,G_2+A_2-A_4,G_3+2A_2-2A_4$ all tend to $L$. **Every representation** of $L$ has the unique form, after the coefficientwise identifications,

$$
S=B+a(A_1-B)+u(G_1-B)+b(G_2+A_2-A_4-B)+c(G_3+2A_2-2A_4-B).
$$

In fact let $a,a_2,a_3,a_4,a_6,u,b,c$ be the coefficients in stride order for a target $mL$. Valuations at $2,3,5,7$ give $a_6=a+u+b+c-m$, $a_4=-b-2c$, $a_3=-a_6$, $a_2=-a_4-2a_6$. Conversely these equations suffice by unique factorization. Taking $m=0$ gives all exact zero relations, including those obtained by undoing the conjugation and two sign identities. The four displayed differences from $B$ form a basis of the remaining zero relations.

They are independent as functions of the cutoff. In a combination with zero limit that vanishes identically, the first cell at $x=1/2$ forces $u=0$, the cell at $1$ then forces $a=0$, and the cell at $3/2$ forces $b=0$. At $5/2$ the remaining $c$ contributes $c/4$ and hence vanishes. Equality at every integer cutoff already implies equality on every half-cell by the prime test applied to arbitrarily large primes and integers $N$ with $N/p$ inside the cell. A fixed nonzero short sum cannot vanish modulo all those primes. Thus the prefix-preserving relations have also been exhausted.

## Exact optimization

For a fixed coefficient vector the rate is rational and computable. Let $C$ be the sum of the absolute real coefficients plus twice the sum of the absolute Gaussian coefficients. Every phase has modulus less than $3/4$, and after its cutoff at $x$ the first omitted power has modulus at most $2^{-x}$. Thus $|S(x)-L|\le4C2^{-x}$. If $2^X>8C$ then $S(x)>0$ for $x\ge X$ since $L>1/2$. One can sum the nonzero cells below the integer $X$ and add $1/X$ for the tail. This computes the rate for arbitrary fixed inputs, including arbitrarily large coefficients.

For an example using two Gaussian strides, take $(a,u,b,c)=(0,0,-2,-3)$. The prefix is $4A_2+6A_3+8A_4-6A_6-2G_2-3G_3$. Between $3/2$ and 4 its successive values are $-1,0,-3/4,0$ on the intervals cut at $2,5/2,3$. It deletes both $(2N/5,N/2]$ and $(N/4,N/3]$. On the half-cells from 4 up to 9 the minimum is $5/8$. Beyond 9 the tail bound applies with $C=34$. Its exact rate is $2/3-1/10-1/12=29/60$. The cost of the earlier start at $3/2$ exceeds the saving from the extra deleted band.

If $u\ne0$, the single cell $[1/2,1)$ contributes one. It remains to compare all triples $(a,b,c)$ at $u=0$. On each half-cell $S$ is an affine linear form in these three unknowns. The following finite certificate uses only cells with $1\le x<36$.

1. Start with no equations and accumulated prime mass zero. For $v=2,\ldots,71$ reduce the row for $S(v/2)$ by the accumulated zero equations, using rational Gaussian elimination.
2. A zero row costs nothing. A nonzero constant costs $2/(v(v+1))$. For a nonconstant row take two branches. In the zero branch adjoin the normalized row using its first nonzero variable as pivot. In the nonzero branch add its mass to the amount spent. The latter branch may forget the inequation, which only enlarges the set of possibilities being tested.
3. Discard a branch once the amount spent reaches $13/30$. Every actual vector following that branch has additional positive mass arbitrarily far out. On its truthful path a vector of rate at most $13/30$ therefore survives through the final cell.

Exactly two leaves survive. The pivot equations at both leaves are diagonal. The middle column gives the accumulated mass at the end of the search. Adding the surviving tail beyond 36 gives the last column.

| Parameters $(a,u,b,c)$ | Mass below 36 | Full rate |
| --- | ---: | ---: |
| $(0,0,0,-5)$ | $7/18$ | $5/12$ |
| $(0,0,0,-2)$ | $73/180$ | $13/30$ |

For example the first prefix is $2A_2+6A_3+10A_4-6A_6-5G_3$. Its short sum on $[2,5/2)$ is $1/2$, on $[5/2,3)$ it is $-3/4$, and on $[3,4)$ it is zero. For the second prefix the corresponding values are $1/2,0,3/8$. Both vanish below 2 and are positive from 4 onward. The latter fact follows from the Phase 13 bounds and is also certified by exact summation up to the positive-tail threshold above. The respective missing prime bands are $(N/4,N/3]$ and $(N/3,2N/5]$. This proves both extremal rates and their uniqueness in the stated alphabet. [Executable elimination and tail certificate](gaussian_relations.py) · [Analytic positivity bounds](../phase13/reviews/classical-bands.md)

The class prescribes the phases, fixed coefficients and common binary cutoff. The theorem leaves different Gaussian numerators, imaginary parts and position-dependent corrections open. Completely unrestricted rational approximants can achieve rate zero. Rounding $(N+1)2^N\log 2$ to an integer and dividing by $N+1$ gives the required error and a denominator at most $N+1$.

## Reproduction

```sh
python3 notes/phase14/gaussian_relations.py
lake build NormalityChecker.GaussianLogarithmRelations
```

The Python program also checks both coefficientwise identities at 81 half-integer cutoffs for ten strides. It compares directly reduced rational prefixes with the Frobenius test at 73 split and 80 inert prime/position pairs, using signed phases and a rational coefficient.
