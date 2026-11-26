# Review of the two smallest Gaussian logarithm denominator rates

Among all fixed finite rational representations of $\log 2$ in the Phase 14E alphabet, the least reduced-denominator rate is $5/12$ and the next distinct rate is $13/30$. Each belongs to one sequence of prefixes. I checked commit `4ca5456cf5ffe14f8af3a18d75b13b33437ef1b7` against Grechkoseeva’s theorem and obtained both rates from an independent enumeration of 33 lines. The classification and the global optimum are paper results. The finite computation below uses exact rational arithmetic. [Independent verifier](check_gaussian_optimality.py) · [Phase 13 construction](../../phase13/complementary-characters.md)

## Cutoff and rate

The allowed terms are real parts of the Taylor series for $-\log(1-z)$, with $z=\pm 2^{-k}$ or $z=(\pm1\pm i)/2^t$ and positive integer $k,t$. The strides and rational coefficients may be arbitrarily large. Each representation fixes finitely many of them before $N$ tends to infinity. Write $S(x)$ for the combined prefix retaining precisely $j(-\log_2|z|)\le x$ in each series. Write $q_N$ for the positive reduced denominator of $2^N S(N)$. The rate is $\lim_{N\to\infty}(\log q_N)/N$, with natural logarithms.

Every modulus $r$ satisfies $r\le1/\sqrt2$, including the two conjugate pairs with $t=1$. At $m=\lfloor N/(-\log_2 r)\rfloor$, the absolute shifted tail of one series is bounded by $2^N r^{m+1}/((m+1)(1-r))$. The numerator is at most one and $m+1$ grows linearly with $N$ for that fixed stride. This proves the claimed shifted error $O(1/(N+1))$ and absolute convergence at $t=1$. For a Gaussian term put $n=2t-1$. Its nonzero real powers have dyadic exponent $\lceil nj/2\rceil$, since $(1+i)^2=2i$. Thus $q_N$ divides $D\,\mathrm{lcm}(1,\ldots,2N)$ for a common coefficient denominator $D$.

For odd $p\nmid D$ with $p^2>2N$, the residue of $p\,2^N S(N)$ is $2^N S(N/p)$ modulo $p$. Only $j=p\ell$ contribute and the cutoff on $\ell$ is exactly the original one at $N/p$. Frobenius on $\mathbb F_p[i]$ fixes or conjugates the argument, preserving the real trace in either case. In particular, $p$ occurs in the denominator precisely when the short rational sum is nonzero **modulo $p$**.

One can take the limit using only finitely many bands at a time. On $[v/2,(v+1)/2)$, $v\ge1$, the short sum is one fixed rational. If it is nonzero, its numerator has finitely many prime divisors, and the prime number theorem gives weight $2/(v(v+1))$ after division by $N$. If it is zero the weight vanishes. Beyond $x=V/2$ the first-power primes have $p\le2N/V$, of limiting upper weight at most $2/V$. Higher powers cost $O(\sqrt{N}\log N)$ in total before division, and $D$ costs $O(1)$. Taking $N\to\infty$ first and then $V\to\infty$ proves the band formula. Since $S(x)\to\log2$, the tail past any finite endpoint has strictly positive mass. [Earlier prime-band analysis](../../phase13/reviews/classical-bands.md)

## Primitive factors and the four free coefficients

Write $A_{k,s}$ for the real prefix with sign $s$, and $G_{t,s}$ for twice the Gaussian real prefix with argument $s(1+i)/2^t$. Conjugation is coefficientwise equality. Pairing opposite real signs leaves the even indices and gives $A_{2k,+}$. Pairing opposite Gaussian signs leaves $j=4h$ and gives $A_{2n,-}$ at exactly the same cutoff $2nh$. Hence positive-sign $A_k,G_t$ suffice at every real cutoff. Their logarithms at infinity have odd numerators $2^k-1$ and $H_n^-=2^n-2^{(n+1)/2}+1$, respectively, in the factors $1-2^{-k}$ and $|1-(1+i)/2^t|^2$.

Grechkoseeva’s equation (1) gives $\Psi_4(x)=x^2+\sqrt2\,x+1$. Substitution of $x=\pm\sqrt{2^n}$ gives exactly the **two** integers $H_n^\pm=2^n\pm2^{(n+1)/2}+1$. Theorem 2 with her $(v,n,m)=(2,4,n)$ supplies a prime of order $4n$ for 2 in each factor for odd $n\ge7$. The exceptions $m=3,5$ lie outside this range, and $m=1$ is outside the theorem’s hypotheses. The factors are odd and their difference is a power of two, so the two witness primes are distinct. [Grechkoseeva, equation (1) and Theorem 2](https://arxiv.org/html/2504.04729v1#Thmtheorem2)

The independent cyclotomic proof in the audited commit also works. Fix $\alpha=\pm(1+i)$ throughout the divisor calculation and put $U_e=|1-\alpha^e|^2$, $C_e=|\Phi_e(\alpha)|^2$. The sign of the middle term in $U_e$ can change with $e$. If $p\mid U_n$, then $2^{2n}=-1\bmod p$, so 2 has order $4d$ with $d\mid n$. Thus $p\equiv1\pmod4$, and $U_n$ is the product of the two evaluations of $1-\alpha^n$ at square roots of $-1$ modulo $p$. At a root where this vanishes, the reduction of $\alpha$ has odd order. Its fourth power is $-4=2^{2d+2}\bmod p$, of order exactly $d$ since $\gcd(4d,2d+2)=4$. Consequently $p\mid U_e$ for $d\mid e\mid n$. Conversely $p\mid U_e$ implies $2^{2e}=-1\bmod p$ and hence $d\mid e$.

For these multiples $e$ of $d$, coprimality of $H_e^\pm$ and odd-prime lifting give $v_p(U_e)=v_p(2^{2d}+1)+v_p(e/d)$. Inverting $U_n=\prod_{e\mid n}C_e$ now gives a nonprimitive $p$ in $C_n$ only when $n/d$ is a positive power of $p$, with exponent one. All such factors together divide $n$. The cyclotomic product gives $C_n>2^{\varphi(n)}/256$. Indeed, after the leading power, the lower bounds for the modulus of the factors at exponents $1$, $3$ and all odd exponents $\ge5$ together are $1/4$, $5/8$ and $5/8$, respectively. Their product exceeds $1/16$. For $\varphi(n)\ge16$, $2^{\varphi(n)}/256\ge\varphi(n)^2\ge n$ for odd $n$.

As a separate finite check, count coprime residues for odd $7\le n<256$ and retain $\varphi(n)<16$. For these six indices the recursion $C_n=U_n/\prod_{e\mid n,\,e<n} C_e$ gives the following integers. Each entry exceeds its index, which suffices by the nonprimitive bound.

| Odd index | $C_n$ for $1+i$ | $C_n$ for $-1-i$ |
| ---: | ---: | ---: |
| 7 | 113 | 29 |
| 9 | 37 | 109 |
| 11 | 2113 | 397 |
| 13 | 8321 | 1613 |
| 15 | 61 | 1321 |
| 21 | 1429 | 14449 |

After clearing rational coefficients and exponentiating, choose the largest occupied height among $k>6$ and $4n$ for odd $n\ge7$. At height $4n$ with a Gaussian term, the witness in $H_n^+$ can only see $A_{4n}$, so its coefficient vanishes. The witness in $H_n^-$ then isolates $G_t$. At a real-only height $k>6$, Bang–Zsigmondy gives a prime of order $k$. All smaller high factors have strictly smaller possible order and the three low Gaussian numerators $1,5,25$ have only the prime 5 of order four. Finite support therefore completes descent even with no prescribed maximum stride. The prime 31 then removes $A_5$. [Zsigmondy, *Zur Theorie der Potenzreste*](https://doi.org/10.1007/BF01692444)

For the target $m\log2$, write $a,u,b,c$ for the coefficients of $A_1,G_1,G_2,G_3$. Valuations at 5, 7 and 3 give $a_4=-b-2c$, $a_3=-a_6$, $a_2=-a_4-2a_6$. The valuation at 2 gives $a_6=a+u+b+c-m$. Conversely these equations determine every prime valuation, so every rational choice of the four free variables works. The case $m=0$ describes all zero relations after sign pairing and conjugation. Distinct choices give distinct integer prefix sequences. For $m=1$ the matrix of coefficients of $(a,u,b,c)$ in $S(1),S(2),S(3),S(4)$ has determinant $67/215040$. This checks uniqueness directly at integer cutoffs.

## Independent global certificate

Take $m=1$. If $u\ne0$, $[1/2,1)$ alone costs one. Set $u=0$. If $a\ne0$, $[1,3/2)$ costs $1/3$. The next two cells have values $(a+b)/2$ and $(4+a+2b)/8$ and weights $1/6$ and $1/10$. Both must vanish to reach full rate at most $13/30$, since even equality in a finite lower bound leaves a positive tail. Thus $a=4,b=-4$. The cells $[5/2,3)$ and $[3,4)$ then have values $c/4$ and $7/24+c/8$, so at least one contributes, at a cost of at least $1/15$. Both halves of $[4,5)$ contribute, with values $13/24$ and $5/8$. This gives at least $1/3+1/15+1/20=9/20$. Consequently $a=u=0$ for every contender.

On the remaining $(b,c)$-plane, construct the short sums for $1\le v<60$ by the power-sum recurrence for the two roots of $X^2-2X+2$. Each nonconstant short sum has a line of zeros. Combine weights of coincident lines. A point can be off all lines, on exactly one line, or at the intersection of two distinct nonparallel lines. This covers unbounded rational parameters and also tests the positive-dimensional sets between intersection points.

The verifier finds 33 lines and 509 distinct intersections. Off the lines the mass below $x=30$ is $19/30$. On just one line its minimum is $7/15$. The table includes every intersection whose mass up to that cutoff is at most $13/30$. Each mass subtracts the weights of **all** incident lines, counting coincident lines once with their combined weight. [Exact line and intersection calculation](check_gaussian_optimality.py)

| $b$ | $c$ | Mass below 30 |
| ---: | ---: | ---: |
| 0 | −5 | 23/60 |
| 0 | −2 | 2/5 |
| 0 | −265/3 | 13/30 |

The last point exceeds the threshold in the full sum because its tail has positive mass. For the other two points, the early cells and their prime endpoints are as follows.

| Range of $x=N/p$ | Prime range | $c=-5$ | $c=-2$ |
| --- | --- | ---: | ---: |
| $[0,2)$ | $p>N/2$ | 0 | 0 |
| $[2,5/2)$ | $2N/5<p\le N/2$ | 1/2 | 1/2 |
| $[5/2,3)$ | $N/3<p\le2N/5$ | −3/4 | 0 |
| $[3,4)$ | $N/4<p\le N/3$ | 0 | 3/8 |
| $[4,\infty)$ | $p\le N/4$ | positive | positive |

On the ten half-cells $4\le x<9$ the respective minima are $125/192$ and $259/384$. For $x\ge9$ the unshifted tail is at most $4C2^{-x}$, where $C$ is the sum of absolute real coefficients plus twice the sum of absolute Gaussian coefficients. Here $C=34,16$, respectively, so the bound is less than $1/2<\log2$. This proves positivity on every later band. Hence the rates are $1/2-(1/3-1/4)=5/12$ and $1/2-(2/5-1/3)=13/30$. Adding $1/30-1/36$ to the first two finite masses also recovers the audited certificate’s $7/18$ and $73/180$ at $x=36$.

The negative $-3/4$ band counts toward the first rate. Direct reduction at $N=13$ gives denominators $(15,6)$ in table order, so only the first contains $p=5$. At $N=18$ the pair is $(63,90)$, reversing this test. At $N=44$ both short sums at $N/11=4$ equal $11/16$, and neither reduced denominator contains 11. Thus the distinction between a rational zero and an exceptional prime in a nonzero numerator matters even for the two extremizers.

Run `python3 notes/phase14/reviews/check_gaussian_optimality.py` from the repository root. The standalone Lean source from the reviewed commit also passed a fresh Lean check. Its declarations cover Gaussian coefficients and cutoffs, sign pairing, Frobenius on real parts, the six small primitive-witness pairs and the residual valuation equations. The global line comparison above is independently executable in Python.
