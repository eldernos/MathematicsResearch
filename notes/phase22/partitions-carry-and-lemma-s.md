# Lemma S, intermediate Euler products, and signed-digit transfer

Phase 22, Track D (sub-tracks D3 and D4) and Track G1, Correction C. Fix an integer radix $b\ge2$. Notation follows [Phase 21, partitions-and-higher-modular](../phase21/partitions-and-higher-modular.md) and [Phase 21, euler-scalings-and-reciprocals](../phase21/euler-scalings-and-reciprocals.md): $x_n=\{b^nx\}$, $D_N(x)$ is the extreme (interval) discrepancy of $x_0,\dots,x_{N-1}$, $\|\cdot\|$ is the distance to the nearest integer, $K_b=\{z:D_N(z)\to1\}$, $F_b=\{c:(b-1)c\in\mathbb Z\}$, and $M_N(w)=N^{-1}\sum_{n<N}\|b^nw\|$. By [Phase 19](../phase19/geometry.md#asymptotic-kernel-and-arithmetic-operations), $K_b=F_b+\{w:M_N(w)\to0\}$. For an integer sequence $a$ we write $F_b(a)=\sum_{m\ge0}a(m)b^{-m}$, $S_a(X)=\#\{1\le m\le X:a(m)\neq0\}$, and $A_a(X)=\sum_{1\le m\le X}|a(m)|$. $E(q)=\prod_{k\ge1}(1-q^k)$, $E_b=E(1/b)$, $E(q)^2=\sum_na_2(n)q^n$, and $\varphi$ is Euler's function.

**Scope and evidence.** "Paper proof" means proved here from the cited published inputs. The only non-elementary input in §1 is Phase 20 Theorem 6(a), which rests on the cited identification of $\eta(12\tau)^2$ as a CM eigenform (see [euler-product §5](../phase20/euler-product.md#5-the-square-of-eulers-product)). The other inputs to §1 are classical: Mertens, Dirichlet–Mertens in progressions (Apostol, Thm. 7.3), and Wirsing. All finite statements are checked by [`scripts/phase22_partitions_carry.py`](../../scripts/phase22_partitions_carry.py) (standard library, about 6 s, 1,256,966 checks, exit 0; §4). The Selberg instances of §1.6 are compared as exact rationals; the Rankin, Mertens and average-factor experiments are floating-point **numerical samples** at finitely many checkpoints, which neither verify a universal constant nor test an asymptotic estimate (the proofs bound those quantities independently). Every discrepancy, frequency, density and ratio quoted from it is a **finite measurement** and is not evidence for any asymptotic statement.

| § | Result | Status |
| --- | --- | --- |
| 1 | **Theorem S** (Lemma S, complete): $\sum_{h\le H}\#\{n\le N:a_2(n)a_2(n+h)\ne0\}\le C_0HN/(\log N)^{3/2}$, uniformly for $1\le H\le N$ | Paper proof (Selberg sieve proved in full; inputs: Phase 20 Thm 6(a), Apostol Thm 7.3, Mertens) |
| 1.7 | Theorem D1.5 for odd prime factors of the denominator: $\tfrac adE_b^2\in K_b\iff a/d\in\mathbb Z[1/b]$ | Paper proof; the gap of Phase 21 (sketched Lemma S) is closed |
| 2.1 | Proposition D3.8: for infinite $M$ with $\gcd M=1$, $p_M$ has cofinite support and $p_M(n)\to\infty$; finite $M$: $P_b(M)\in K_b\iff M=\{1\}$ | Paper proof |
| 2.2 | Proposition D3.9: $T_K\ge\max(\operatorname{lcm}m_j,\sum m_j-2)$; $T_K=m_KD_{K-1}$ under $T_{K-1}\mid m_K$, and for divisibility chains when $b$ is even, $b\equiv1\pmod4$ or $m_K$ is even (for odd chains with $b\equiv3\pmod4$, $T_K=m_KD_{K-1}/2^{\min(K-2,\,v_2(b+1)-1)}$); $T_K=\prod m_j$ for coprime schedules in base 2 | Paper proof; exact orders checked |
| 2.4 | Theorem D3.11 and Corollary D3.12: $\liminf_ND_N(P_b(M))=0$ along any subsequence of tetration steps, even when $M$ has upper density 1 | Paper proof |
| 2.5 | Tracking/period phase diagram across polynomial, chain, coprime and admissible schedules | Paper proof; table finite |
| 2.6 | Proposition D3.13: Mahler's binary partition constant, functional equation, window $\log_b\beta(N)+O(\log N)$, chain period | Paper proof (asymptotic of $\beta$ cited) |
| 2.7 | Proposition D3.14: progression splits, $P_b=Q_bP_{b^2}$, $1/Q_b=\sum(-1)^n\mathrm{sc}(n)b^{-n}$ | Paper proof; identities checked |
| 3.2 | Theorem D4.8: net signed-digit transfer | Paper proof (from Lean transfer theorems) |
| 3.3 | Theorem D4.9: completeness, $K_b=F_b+\{\text{sparse bounded signed series}\}+\mathbb Z$; in base 2, $x\in K_2$ iff the binary digits change $o(N)$ times | Paper proof |
| 3.4 | Examples in $K_b$ with raw width $\asymp N\log N$ and $\asymp N^2$ (the maximal order) | Paper proof |
| 3.6 | Theorem D4.13 (entropy–multiplicity wall) and Corollary D4.15: local signed-digit width $\asymp N\sqrt{\log N}$ for $D(\Theta_3^2)$, $E_b^4,E_b^6,E_b^8$; $\asymp N(\log N)^{1/4}$ for $D(E_b^2)$ | Paper proof (CM structure and Thm 6(b) cited) |
| 2.9, 3.7, 5 | $P_b$, $P_b(\{2^k\})$, $P_b(\{k^2\})$, $E_b^r$ ($r\ge4$): membership in $K_b$ and normality | **Open** |

## 1. Lemma S (Track G1, Correction C)

### 1.1 Statement

Let $\mathcal P_0$ be the set of primes $p\ge5$ with $p\not\equiv1\pmod{12}$. Since $12n+1$ is prime to $6$, every prime factor of $12n+1$ is at least $5$.

**Input (Phase 20, Theorem 6(a)).** $a_2(n)\neq0$ if and only if $v_p(12n+1)$ is even for every $p\in\mathcal P_0$; then $|a_2(n)|=\prod_{p\equiv1\,(12)}(v_p(12n+1)+1)$.

Lemma S uses only the direction "$a_2(n)\neq0\Rightarrow$ even exponents". For $a_2(n)\neq0$ define

```math
v(n)=\prod_{p\in\mathcal P_0}p^{v_p(12n+1)/2},\qquad u(n)=\frac{12n+1}{v(n)^2}.
```

Then $u(n)$ is a product of primes $\equiv1\pmod{12}$ only, and $\gcd(v(n),6)=1$.

**Theorem S.** There is an absolute constant $C_0$ such that for all $N\ge2$ and all $1\le H\le N$,

```math
\sum_{h=1}^{H}\#\{1\le n\le N:\ a_2(n)\,a_2(n+h)\neq0\}\ \le\ C_0\,\frac{HN}{(\log N)^{3/2}} .
```

Phase 21 needed this only for $H\le(\log N)^2$. Theorem S follows from a bound for each shift, with an explicit arithmetic factor.

**Proposition S′.** Let $N_1=\lceil e^{200}\rceil$. Let $B$ be the constant of Lemma S.3 and

```math
C_5=\Bigl(\sum_{g\ge1}\frac{(g/\varphi(g))^4}{g^2}\Bigr)\Bigl(\sum_{w\ge1}\frac{(w/\varphi(w))^2}{w^2}\Bigr)^{2}<\infty,\qquad C_1=4000\,e^{2B}C_5+1 .
```

Then for $N\ge N_1$ and $1\le h\le N$, the count $P_h(N)=\#\{1\le n\le N:a_2(n)a_2(n+h)\ne0\}$ satisfies

```math
P_h(N)\ \le\ C_1\,\frac{h}{\varphi(h)}\,\frac{N}{(\log N)^{3/2}} .
```

The constants are absolute and are not optimized. The two series in $C_5$ converge: $(w/\varphi(w))^2=\sum_{d\mid w}f_2(d)$ with $f_2$ supported on squarefree $d$ and $f_2(p)=(2p-1)/(p-1)^2$, so $\sum_w(w/\varphi(w))^2w^{-2}=\zeta(2)\prod_p(1+f_2(p)p^{-2})$; likewise with $f_4(p)=(p/(p-1))^4-1=O(1/p)$. Numerically the two series are $12.31$ and $3.39$, so $C_5\approx141.5$.

### 1.2 Selberg's upper bound, with proof

**Lemma S.1 (Selberg).** Let $F\in\mathbb Z[m]$, let $I$ be a set of $X$ consecutive integers, let $\mathcal Q$ be a finite set of primes and $P=\prod_{p\in\mathcal Q}p$. For squarefree $d\mid P$ let $\rho(d)=\#\{m\bmod d:F(m)\equiv0\bmod d\}$, and assume $1\le\rho(p)<p$ for $p\in\mathcal Q$. Put $g(d)=\prod_{p\mid d}\rho(p)/(p-\rho(p))$, $G(\xi)=\sum_{d<\xi,\,d\mid P}g(d)$, and $r_d=\#\{m\in I:d\mid F(m)\}-X\rho(d)/d$. Then $|r_d|\le\rho(d)$, and for every $\xi>1$

```math
S:=\#\{m\in I:\gcd(F(m),P)=1\}\ \le\ \frac{X}{G(\xi)}+\sum_{\substack{d_1,d_2<\xi\\ d_1,d_2\mid P}}|r_{[d_1,d_2]}| .
```

*Proof.* By the Chinese remainder theorem $\rho$ is multiplicative on divisors of $P$, and $\{m:d\mid F(m)\}$ is a union of $\rho(d)$ classes modulo $d$. Each class meets $I$ in $\lfloor X/d\rfloor$ or $\lceil X/d\rceil$ points, so $|r_d|\le\rho(d)$.

Let $\lambda_d$ ($d\mid P$, $d<\xi$) be real with $\lambda_1=1$. Then $\mathbf 1[\gcd(F(m),P)=1]\le(\sum_{d\mid\gcd(F(m),P)}\lambda_d)^2$ for every $m$, so

```math
S\le\sum_{d_1,d_2}\lambda_{d_1}\lambda_{d_2}\,\#\{m\in I:[d_1,d_2]\mid F(m)\}=X\,Q(\lambda)+\sum_{d_1,d_2}\lambda_{d_1}\lambda_{d_2}r_{[d_1,d_2]},\qquad Q(\lambda)=\sum_{d_1,d_2}\lambda_{d_1}\lambda_{d_2}f([d_1,d_2]),
```

with $f(d)=\rho(d)/d$. On squarefree numbers $f([d_1,d_2])=f(d_1)f(d_2)/f((d_1,d_2))$. Put $h(p)=1/f(p)-1=(p-\rho(p))/\rho(p)>0$, extended multiplicatively, so that $1/f(e)=\sum_{t\mid e}h(t)$. Then

```math
Q(\lambda)=\sum_{t}h(t)\,y_t^2,\qquad y_t=\sum_{t\mid d}\lambda_df(d).
```

Möbius inversion gives $\lambda_df(d)=\sum_{d\mid t}\mu(t/d)y_t$, and in particular $1=\lambda_1=\sum_t\mu(t)y_t$. By Cauchy–Schwarz, $1\le Q(\lambda)\sum_{t<\xi,\,t\mid P}1/h(t)=Q(\lambda)G(\xi)$, since $1/h=g$. Equality holds for $y_t=\mu(t)g(t)/G(\xi)$. For this choice, write $t=dk$ with $(k,d)=1$:

```math
\lambda_d=\frac{\mu(d)}{f(d)G(\xi)}\sum_{\substack{k<\xi/d,\ k\mid P\\ (k,d)=1}}\mu(k)^2g(dk)=\mu(d)\,\frac{g(d)}{f(d)}\,\frac{G_d(\xi/d)}{G(\xi)},\qquad G_d(y)=\sum_{\substack{k<y,\ k\mid P\\(k,d)=1}}g(k).
```

Now $g(d)/f(d)=\prod_{p\mid d}p/(p-\rho(p))=\prod_{p\mid d}(1+g(p))=\sum_{s\mid d}g(s)$. For $s\mid d$ and $k<\xi/d$ coprime to $d$, the products $sk<\xi$ are distinct divisors of $P$. Hence $G(\xi)\ge\sum_{s\mid d}g(s)\,G_d(\xi/d)$, which gives $|\lambda_d|\le1$. So $Q(\lambda)=1/G(\xi)$ and the error sum is at most $\sum|r_{[d_1,d_2]}|$. $\square$

**Lemma S.2 (lower bound for $G$).** In Lemma S.1 assume also $\rho(p)\in\{1,2\}$ and $5\le p\le z$ for every $p\in\mathcal Q$, with $\log z\ge2$. If $\xi\ge z^{17}$, then

```math
G(\xi)\ \ge\ \tfrac12\prod_{p\in\mathcal Q}\Bigl(1-\frac1p\Bigr)^{-\rho(p)} .
```

*Proof.* Let $\kappa$ be multiplicative with $\kappa(p^k)=\binom{k+\rho(p)-1}{\rho(p)-1}$, that is, $1$ if $\rho(p)=1$ and $k+1$ if $\rho(p)=2$. Then $\kappa(p^k)\le\rho(p)^k$, since $k+1\le2^k$. For squarefree $e\mid P$,

```math
g(e)=\prod_{p\mid e}\sum_{k\ge1}\Bigl(\frac{\rho(p)}p\Bigr)^k\ \ge\ \prod_{p\mid e}\sum_{k\ge1}\frac{\kappa(p^k)}{p^k}=\sum_{\operatorname{rad}n=e}\frac{\kappa(n)}n .
```

Since $n<\xi$ implies $\operatorname{rad}n<\xi$, $G(\xi)\ge\sum_{n<\xi,\ \operatorname{rad}n\mid P}\kappa(n)/n=\Pi-T$, where

```math
\Pi=\sum_{\operatorname{rad}n\mid P}\frac{\kappa(n)}n=\prod_{p\in\mathcal Q}\Bigl(1-\frac1p\Bigr)^{-\rho(p)},\qquad T=\sum_{\substack{n\ge\xi\\ \operatorname{rad}n\mid P}}\frac{\kappa(n)}n .
```

Here we used $\sum_k\binom{k+\rho-1}{\rho-1}y^k=(1-y)^{-\rho}$. Let $\delta=1/\log z$. Rankin's trick gives

```math
T\le\xi^{-\delta}\sum_{\operatorname{rad}n\mid P}\kappa(n)n^{\delta-1}=\xi^{-\delta}\prod_{p\in\mathcal Q}(1-p^{\delta-1})^{-\rho(p)} .
```

For $p\le z$ we have $t:=\delta\log p\le1$, so $p^\delta-1=e^t-1\le(e-1)t$, and $1-p^{\delta-1}\ge1-e/5$. Hence

```math
\log\frac{(1-p^{\delta-1})^{-1}}{(1-p^{-1})^{-1}}=\log\Bigl(1+\frac{p^{\delta-1}-p^{-1}}{1-p^{\delta-1}}\Bigr)\le\frac{(e-1)\log p}{(1-e/5)\,p\log z}.
```

Mertens' bound $\sum_{p\le z}(\log p)/p\le\log z+2$ and $\rho\le2$ give $T\le\xi^{-\delta}\,\Pi\,\exp\bigl(2\tfrac{e-1}{1-e/5}(1+\tfrac2{\log z})\bigr)\le\xi^{-\delta}\Pi\,e^{15.07}$, using $\log z\ge2$. For $\xi\ge z^{17}$, $\xi^{-\delta}\le e^{-17}$, so $T\le e^{-1.93}\Pi<\Pi/2$. $\square$

**Lemma S.3 (Mertens product over $\mathcal P_0$).** There is an absolute constant $B$ such that for $z\ge5$

```math
\sum_{p\le z,\ p\in\mathcal P_0}\frac1p\ \ge\ \frac34\log\log z-B,\qquad\text{hence}\qquad\prod_{p\le z,\ p\in\mathcal P_0}\Bigl(1-\frac1p\Bigr)^2\le e^{2B}(\log z)^{-3/2}.
```

*Proof.* For $a\in\{5,7,11\}$, Apostol (*Introduction to Analytic Number Theory*, Thm. 7.3) gives $\sum_{p\le x,\,p\equiv a\,(12)}(\log p)/p=\frac14\log x+O(1)$. Partial summation turns this into $\sum_{p\le x,\,p\equiv a\,(12)}1/p=\frac14\log\log x+O(1)$; sum over the three classes. Finally use $(1-1/p)^2\le e^{-2/p}$. $\square$

The script measures $\frac34\log\log z-\sum_{p\le z,\,p\in\mathcal P_0}1/p$ at $0.320,0.312,0.314,0.314,0.314$ for $z=10^2,10^3,10^4,10^5,6\cdot10^5$ (finite data; the proof needs only that $B$ exists).

### 1.3 The structure of supported pairs

**Lemma S.4.** Let $h\ge1$ and $n\ge1$ with $a_2(n)a_2(n+h)\ne0$. Put $v=v(n)$, $v'=v(n+h)$ and $g=\gcd(v,v')$.

(a) $g^2\mid h$.

(b) Let $v,v'\ge1$ be prime to $6$ with $g=\gcd(v,v')$ and $g^2\mid h$. The integers $n\ge0$ with $v^2\mid12n+1$ and $v'^2\mid12(n+h)+1$ form exactly one residue class $n\equiv n_0\pmod L$, where $L=\operatorname{lcm}(v^2,v'^2)=v^2v'^2/g^2$.

(c) In (b), write $n=n_0+mL$. Then

```math
\frac{12n+1}{v^2}=A_1m+B_1,\qquad\frac{12(n+h)+1}{v'^2}=A_2m+B_2,\qquad A_1=\frac{12v'^2}{g^2},\quad A_2=\frac{12v^2}{g^2},
```

with integers $B_1=(12n_0+1)/v^2$, $B_2=(12n_0+12h+1)/v'^2$, and

```math
A_1B_2-A_2B_1=\frac{144\,h}{g^2}.
```

(d) Let $p\in\mathcal P_0$ with $p\nmid vv'$, and let $\rho(p)$ be the number of roots of $(A_1m+B_1)(A_2m+B_2)$ modulo $p$. Then $\rho(p)=2$ if $p\nmid h$ and $\rho(p)=1$ if $p\mid h$.

(e) If $n$ is as in the hypothesis and $(v(n),v(n+h))=(v,v')$, then $A_1m+B_1=u(n)$ and $A_2m+B_2=u(n+h)$, so neither has a prime factor in $\mathcal P_0$.

*Proof.* (a) $g^2$ divides $12n+1$ and $12n+12h+1$, hence divides $12h$. Since $g\mid12n+1$, $\gcd(g,6)=1$, so $g^2\mid h$. (b) Since $12$ is invertible modulo $v^2$ and $v'^2$, the conditions read $n\equiv\alpha\pmod{v^2}$ and $n\equiv\beta\pmod{v'^2}$, with $12\alpha\equiv-1$ and $12\beta\equiv-1-12h$. This system is solvable if and only if $\alpha\equiv\beta\pmod{g^2}$, i.e. $12h\equiv0\pmod{g^2}$, i.e. $g^2\mid h$. The solution is then unique modulo $L$. (c) $12L/v^2=12v'^2/g^2$ and $12L/v'^2=12v^2/g^2$. Next, $v^2(A_1m+B_1)+12h=v'^2(A_2m+B_2)$ gives $v'^2B_2-v^2B_1=12h$, so $A_1B_2-A_2B_1=(12/g^2)(v'^2B_2-v^2B_1)=144h/g^2$. (d) $p\nmid12vv'$, so $p\nmid A_1A_2$ and each factor has exactly one root modulo $p$. The two roots coincide if and only if $p\mid A_1B_2-A_2B_1=144h/g^2$. Since $p\nmid6g$, this happens exactly when $p\mid h$. (e) is the definition of $u$. $\square$

The script verifies (a) on all $326{,}704$ supported pairs with $n\le50{,}000$, $h\le50$ (1,000 of them have $g>1$; pairs with $g=5$ occur at $h=25,50$). It verifies (b)–(c) and $u=A_1m+B_1$, $u'=A_2m+B_2$ on all $10{,}719$ classes $(v,v',h)$ that occur, and (d) in 2,083 (class, prime) cases.

### 1.4 Proof of Proposition S′

Fix $N\ge N_1$ and $1\le h\le N$. Put

```math
V=(\log N)^3,\qquad z=N^{1/100},\qquad\xi=z^{17}=N^{0.17}.
```

Then $\log z\ge2$ and $V^4=(\log N)^{12}\le N$. Split the supported pairs $n\in[1,N]$ into class (i), where $v(n)>V$ or $v(n+h)>V$, and class (ii), where both are at most $V$.

*Class (i).* If $v(n)=v>V$, then $v^2\mid12n+1\le12N+1$, so $v\le\sqrt{12N+1}$. For each $v$ prime to $6$ the condition is one class modulo $v^2$, which meets $[1,N]$ in at most $N/v^2+1$ points. Summing over $V<v\le\sqrt{12N+1}$ with $\gcd(v,6)=1$ gives at most $N/V+\sqrt{12N+1}$. Here we used $\sum_{v>V,\ \gcd(v,6)=1}v^{-2}\le1/V$ for real $V\ge3$: each interval $[V+6j,V+6j+6)$ contains at most two integers prime to $6$, so the sum is at most $2\sum_{j\ge0}(V+6j)^{-2}\le2V^{-2}+1/(3V)\le1/V$. The same argument for $v(n+h)$, with $12(n+h)+1\le24N+1$, gives

```math
\#\text{class (i)}\le\frac{2N}{V}+\sqrt{12N+1}+\sqrt{24N+1}\le\frac{2N}{(\log N)^3}+9\sqrt N .
```

*Class (ii).* By Lemma S.4(a), only pairs $(v,v')$ with $v,v'\le V$, both prime to $6$, and $g^2\mid h$ occur. Fix one. By S.4(b), the relevant $n$ are $n=n_0+mL\in[1,N]$ with $m$ in a set $I$ of $X\le N/L+1\le2N/L$ consecutive integers. By S.4(e), each such $n$ in class (ii) has $\gcd(F(m),P)=1$, where $F(m)=(A_1m+B_1)(A_2m+B_2)$ and $P$ is the product of

```math
\mathcal Q=\{p\in\mathcal P_0:\ p\le z,\ p\nmid vv'\}.
```

By S.4(d), $\rho(p)\in\{1,2\}<p$ on $\mathcal Q$. Lemmas S.1 and S.2 apply. Since $|r_e|\le\rho(e)\le2^{\omega(e)}=\tau(e)$ for squarefree $e$, $\tau([d_1,d_2])\le\tau(d_1)\tau(d_2)$ and $\sum_{d<\xi}\tau(d)\le\xi(1+\log\xi)$, we get

```math
\#\{\text{class (ii) with this }(v,v')\}\ \le\ 2X\prod_{p\in\mathcal Q}\Bigl(1-\frac1p\Bigr)^{\rho(p)}+\xi^2(1+\log\xi)^2 .
```

Split the product according to whether $p\mid vv'$ or $p\mid h$:

```math
\prod_{p\in\mathcal Q}\Bigl(1-\frac1p\Bigr)^{\rho(p)}=\prod_{\substack{p\in\mathcal P_0\\p\le z}}\Bigl(1-\frac1p\Bigr)^{2}\prod_{\substack{p\in\mathcal P_0,\ p\le z\\ p\mid vv'}}\Bigl(1-\frac1p\Bigr)^{-2}\prod_{\substack{p\in\mathcal Q\\ p\mid h}}\Bigl(1-\frac1p\Bigr)^{-1}\le e^{2B}(\log z)^{-3/2}\Bigl(\frac v{\varphi(v)}\Bigr)^2\Bigl(\frac{v'}{\varphi(v')}\Bigr)^2\frac h{\varphi(h)} .
```

The inequality uses Lemma S.3 and $\prod_{p\mid vv'}(1-1/p)^{-1}\le(v/\varphi(v))(v'/\varphi(v'))$. With $X\le2N/L$ and $(\log z)^{-3/2}=1000(\log N)^{-3/2}$, the main term for $(v,v')$ is at most

```math
4000\,e^{2B}\,\frac h{\varphi(h)}\,\frac N{(\log N)^{3/2}}\cdot\frac{(v/\varphi(v))^2(v'/\varphi(v'))^2}{L}.
```

*Summing over $(v,v')$.* Write $v=gw$ and $v'=gw'$ with $\gcd(w,w')=1$. Then $L=v^2v'^2/g^2=g^2w^2w'^2$, the map $(v,v')\mapsto(g,w,w')$ is injective, and $v/\varphi(v)\le(g/\varphi(g))(w/\varphi(w))$. Hence, **uniformly in $h$**,

```math
\sum_{\substack{v,v'\le V\\ g^2\mid h}}\frac{(v/\varphi(v))^2(v'/\varphi(v'))^2}{L}\ \le\ \sum_{g\ge1}\frac{(g/\varphi(g))^4}{g^2}\Bigl(\sum_{w\ge1}\frac{(w/\varphi(w))^2}{w^2}\Bigr)^2=C_5 .
```

Here $1/L=g^2/(v^2v'^2)=1/(g^2w^2w'^2)$: the surviving factor $g^{-2}$ makes the $g$-sum converge, and no condition beyond $g^2\mid h$ is used. There are at most $V^2$ pairs, so the remainders total at most $V^2\xi^2(1+\log\xi)^2$.

*Conclusion.* $P_h(N)\le4000e^{2B}C_5\,(h/\varphi(h))\,N(\log N)^{-3/2}+R(N)$ with

```math
R(N)=\frac{2N}{(\log N)^3}+9\sqrt N+(\log N)^6N^{0.34}(1+0.17\log N)^2 .
```

For $\log N\ge200$, each term of $R(N)(\log N)^{3/2}/N$ is decreasing in $N$, and at $\log N=200$ their sum is below $10^{-3}$ (the first term is $2/200^{3/2}\approx7.1\cdot10^{-4}$; the others are below $10^{-36}$). So $R(N)\le N(\log N)^{-3/2}\le(h/\varphi(h))N(\log N)^{-3/2}$, and Proposition S′ follows with $C_1=4000e^{2B}C_5+1$. $\square$

### 1.5 Proof of Theorem S

The identity $h/\varphi(h)=\sum_{d\mid h}\mu(d)^2/\varphi(d)$ holds because both sides are multiplicative and equal $p/(p-1)$ at every $p^k$. Hence

```math
\sum_{h\le H}\frac h{\varphi(h)}=\sum_d\frac{\mu(d)^2}{\varphi(d)}\Bigl\lfloor\frac Hd\Bigr\rfloor\le H\sum_d\frac{\mu(d)^2}{d\,\varphi(d)}=H\prod_p\Bigl(1+\frac1{p(p-1)}\Bigr)=\frac{\zeta(2)\zeta(3)}{\zeta(6)}H\le1.9436\,H .
```

For $N\ge N_1$, Proposition S′ gives Theorem S with constant $1.9436\,C_1$. For $2\le N<N_1$ the trivial bound $HN\le(\log N_1)^{3/2}HN/(\log N)^{3/2}$ applies. Take $C_0=\max(1.9436\,C_1,(\log N_1)^{3/2})$. $\square$

The script samples $\sum_{h\le H}h/\varphi(h)\le1.94360\,H$ numerically (floating point) for every $H\le10^4$; the proof above does not use this sample.

### 1.6 Comparison with the Phase 21 sketch

- **Determinant.** The sketch did not compute it. The two cofactors are tied by $v^2(A_1m+B_1)+12h=v'^2(A_2m+B_2)$. So $v'^2B_2-v^2B_1=+12h$ and $A_1B_2-A_2B_1=144h/g^2$.
- **Compatibility.** The sketch required $\gcd(v,v')\mid h$. The exact condition is $g^2\mid h$, which is stronger. It follows from $g^2\mid12h$ and $\gcd(g,6)=1$.
- **Singular series.** The proof produces the factor $\prod_{p\mid h,\,p\in\mathcal Q}(1-1/p)^{-1}\le h/\varphi(h)$. The sketch's $\prod_{p\mid h}(1+2/p)$ is also an upper bound, since $(1-1/p)^{-1}\le1+2/p$ for $p\ge2$, but $h/\varphi(h)$ has the exact average $\zeta(2)\zeta(3)/\zeta(6)$. At $H=50$ the two averages are $1.898$ and $2.096$.
- **Sieve parameters.** The sketch sifted up to $N^{1/10}$; the proof takes $z=N^{1/100}$ and $\xi=z^{17}$. The exponent 17 is what Rankin's trick needs for $G(\xi)\ge\Pi/2$ with explicit constants (Lemma S.2), and $\xi^2=N^{0.34}$ keeps the remainder negligible. The sketch cited Halberstam–Richert, Thm. 5.1; that citation is replaced by the self-contained Lemmas S.1–S.2.
- **Range of $H$.** The sketch assumed $H\le(\log N)^2$; no upper bound beyond $H\le N$ is needed.
- **$V$.** As in the sketch, $V=(\log N)^3$; this leaves room in the comparison $2N/V\le N/(\log N)^{3/2}$.

**Finite data.** At $N=50{,}000$ and $H=50$,

```math
\sum_{h\le50}P_h(50000)=326{,}704,\qquad \frac{326704\,(\log N)^{3/2}}{HN}=4.651 .
```

The per-shift ratio $P_h(N)(\log N)^{3/2}/((h/\varphi(h))N)$ lies in $[1.356,4.390]$, with mean $2.846$ and maximum at $h=1$. The Selberg inequality of Lemma S.1 holds, with $|\lambda_d|\le1$, in three exact instances (the script compares the rational quantities directly, with no tolerance; the decimals below are roundings); for $h=6$, $X=3000$, sifting primes in $\mathcal P_0\cap[5,31]$ and $\xi=60$, the values are $S=662\le\sum_m(\sum_{d\mid F(m)}\lambda_d)^2=939.9\le939.6+21.0$. Here $21.0$ is the $\lambda$-weighted remainder $\sum|\lambda_{d_1}\lambda_{d_2}r_{[d_1,d_2]}|$ from the proof of Lemma S.1; the unweighted remainder $\sum|r_{[d_1,d_2]}|$ displayed in Lemma S.1 is $77.1$ (and $67.7$, $81.1$ for $h=25,35$), and the script checks $|r_d|\le\rho(d)$ exactly. The Rankin chain $G(\xi)\ge\sum_{n<\xi}\kappa(n)/n\ge\Pi-\xi^{-\delta}\Pi_\delta$ of Lemma S.2 is sampled numerically (floating point) at $z=60$ for $\xi=10^3,10^4,10^5$. These are finite checks of the inequalities used, not estimates of $C_0$.

### 1.7 Completion of Theorem D1.5

**Theorem D1.5 (complete).** For reduced $a/d$, $\tfrac adE_b^2\in K_b$ if and only if $a/d\in\mathbb Z[1/b]$.

The inputs are Phase 20 Theorem 6(a) (cited eigenform identification), Wirsing's theorem, and Theorem S. Phase 21 proved the cases "if" and "$b$-coprime part $d_1$ even". For an odd prime $\ell\mid d_1$, Phase 21 reduced to $\tfrac1\ell E_b^2\in K_b$. Assume this. The argument below is the Phase 21 argument with every step stated.

*(i) Atoms.* Write $I_n=\sum_{m\le n}a_2(m)b^{n-m}$ and $\tau_n=b^nE_b^2-I_n$. Coefficient transfer (Phase 20) gives $\#\{n<N:|\tau_n|>\varepsilon\}=o(N)$ for each $\varepsilon>0$. Membership gives $c'\in F_b$ with $M_N(\tfrac1\ell E_b^2-c')\to0$. Since $b^nc'\equiv c'\pmod1$, $\|I_n/\ell-c'\|\to0$ along a density-one set of $n$. As $I_n/\ell\in\tfrac1\ell\mathbb Z$, this forces $c'=c/\ell$ for an integer $c$ with $bc\equiv c\pmod\ell$, and $I_n\equiv c\pmod\ell$ for density-one $n$.

*(ii) Runs.* Let $S_\ell=\{n:\ell\nmid a_2(n)\}$, with elements $n_1<n_2<\cdots$. For $n\notin S_\ell$, $I_n\equiv bI_{n-1}\pmod\ell$, and $b$ is invertible modulo $\ell$ with $bc\equiv c$. So on each run $[n_i,n_{i+1})$, $I_n\equiv c$ either everywhere or nowhere. Two consecutive runs cannot both sit at $c$: $I_{n_{i+1}}\equiv bc+a_2(n_{i+1})\not\equiv c$.

*(iii) Counting.* Let $S'$ be the set of $n$ with $12n+1=uv^2$, $u$ squarefree and composed of primes $\equiv1\pmod{12}$, and $v$ composed of primes in $\mathcal P_0$. By Theorem 6(a), $|a_2(n)|=2^{\omega(u)}$ on $S'$, so $S'\subseteq S_\ell$. The indicator of $\{uv^2\}$ is multiplicative, equals $1$ at primes $\equiv1\pmod{12}$ (prime density $\tfrac14$) and $0$ at the other primes, and is bounded on prime powers. Every such $m=uv^2$ is $\equiv1\pmod{12}$. Wirsing's theorem gives $\#\{m\le x\}\sim c\,x(\log x)^{-3/4}$ with $c>0$, hence $|S'\cap(N/2,N]|\ge\kappa N(\log N)^{-3/4}$ for $N\ge N_2$, with some $\kappa>0$.

By Theorem S applied twice (to $n$ and to $n-h$), at most $2C_0HN(\log N)^{-3/2}$ supported elements of $(N/2,N]$ (elements of $\operatorname{supp}a_2$) have another point of $\operatorname{supp}a_2\supseteq S_\ell$ within distance $H$. Take $H=\lfloor\kappa(\log N)^{3/4}/(4C_0)\rfloor$, so this is at most $\tfrac12\kappa N(\log N)^{-3/4}$. Then at least $\tfrac12\kappa N(\log N)^{-3/4}$ points $n_i\in S_\ell\cap(N/2,N]$ have both neighbouring gaps at least $H$. At each of them, by (ii), $[n_i-H,n_i)$ or $[n_i,n_i+H)$ lies in a run that avoids $c$. The left stretches are pairwise disjoint, and so are the right ones, so each $n$ lies in at most two stretches. Hence

```math
\#\{n<N+H:\ I_n\not\equiv c\pmod\ell\}\ \ge\ \frac H2\cdot\frac{\kappa N}{2(\log N)^{3/4}}\ \ge\ \frac{\kappa^2}{20\,C_0}\,N
```

for large $N$, using $H\ge\kappa(\log N)^{3/4}/(5C_0)$. Since $H=o(N)$, this contradicts (i). $\square$

So Theorem D1.5 now holds for every denominator, under the same single cited input (the eigenform identification behind Theorem 6(a)) that Phase 21 used for the rate of $E_b^2$. The limit law of $\tfrac adE_b^2$ for odd $d>1$ remains open.

## 2. D3: intermediate Euler products

For a nonempty set $M=\{m_1<m_2<\cdots\}$ of positive integers put

```math
P_b(M)=\prod_{m\in M}\bigl(1-b^{-m}\bigr)^{-1}=\sum_{n\ge0}p_M(n)\,b^{-n},\qquad R_K=\prod_{j\le K}\frac{b^{m_j}}{b^{m_j}-1},\qquad D_K=\prod_{j\le K}(b^{m_j}-1),\qquad T_K=\operatorname{ord}_{D_K}(b),
```

where $p_M(n)$ is the number of partitions of $n$ into parts from $M$. The fraction $R_K=b^{\sum_{j\le K}m_j}/D_K$ is reduced, since $\gcd(b,D_K)=1$. The extremes are $M=\mathbb Z_{\ge1}$, giving $P_b$ (open), and admissible schedules (Phase 21, Theorem D2), giving normal numbers.

### 2.1 Support: transfer methods never apply

**Proposition D3.8.** Let $g=\gcd(M)$.

(a) $P_b(M)=P_{b^g}(M/g)$. So assume $g=1$.

(b) If $g=1$, then $p_M(n)>0$ for all $n\ge n_0(M)$, so $S(X)=X-O_M(1)$.

(c) If $M$ is infinite and $g=1$, then $p_M(n)\to\infty$.

(d) If $M$ is finite, $P_b(M)$ is rational with reduced denominator $D_{|M|}$, and $P_b(M)\in K_b$ if and only if $M=\{1\}$.

*Proof.* (a) Substitute $q=b^{-g}$. (b) A finite subset with gcd 1 represents every large integer as a nonnegative combination (Frobenius). (c) Fix a finite $F_0\subseteq M$ with $\gcd F_0=1$. For every $k\ge\max(2,|F_0|)$ choose a finite $F\supseteq F_0$ in $M$ with $|F|=k$ (possible since $M$ is infinite); then $\gcd F=1$ and $p_M(n)\ge p_F(n)\sim n^{k-1}/((k-1)!\prod F)$ by Schur's theorem, so $\liminf p_M(n)=\infty$. (d) A rational number lies in $K_b$ exactly when its reduced denominator divides $b^j(b-1)$ for some $j$ (Phase 19). Here that means $\prod_{m\in M}(b^m-1)\mid b-1$, which holds only for $M=\{1\}$, where $P_b(\{1\})=b/(b-1)\in F_b$. $\square$

So for infinite $M$ the support has density one. Every coefficient-transfer theorem in the repository needs $S(X)=o(X)$ and is vacuous. The question is entirely one of carries.

### 2.2 Periods of the rational approximants

**Proposition D3.9.** Let $K\ge1$.

(a) $\operatorname{lcm}(m_1,\dots,m_K)\mid T_K$, $T_{K-1}\mid T_K$, and $T_K>\sum_{j\le K}m_j-2$.

(b) If $K\ge2$ and $T_{K-1}\mid m_K$, then $T_K=m_K\,D_{K-1}$.

(c) If $m_1\mid m_2\mid\cdots\mid m_K$, and $b$ is even, or $b\equiv1\pmod4$, or $m_K$ is even, then $T_K=m_KD_{K-1}$.

(c′) If $K\ge2$, $m_1\mid m_2\mid\cdots\mid m_K$ are all odd and $b\equiv3\pmod4$, then $T_K=m_KD_{K-1}/2^{\min(K-2,\,v_2(b+1)-1)}$. So the chain formula of (c) fails only by a power of 2 bounded by $2^{v_2(b+1)-1}$.

(d) If $b=2$ and $m_1,\dots,m_K$ are pairwise coprime, then $T_K=m_1\cdots m_K$. Moreover the full-period law of $R_K$ is the convolution $\mu_1*\cdots*\mu_K$, where $\mu_j$ is the uniform law on the orbit of $c_j/(2^{m_j}-1)$ and $R_K\equiv\sum_jc_j/(2^{m_j}-1)\pmod1$ is the partial-fraction decomposition.

*Proof.* (a) $\operatorname{ord}_{b^m-1}(b)=m$, since $b^j-1<b^m-1$ for $0<j<m$, and $b^{m_j}-1\mid D_K$. Next, $D_{K-1}\mid D_K$. Finally $b^{T_K}>D_K\ge b^{\sum m_j}\prod_{k\ge1}(1-b^{-k})\ge b^{\sum m_j}E_2>b^{\sum m_j-2}$, since $E_2=0.2887\ldots>\tfrac14$.

(b) $D_K\mid b^T-1$ forces $m_K\mid T$. Write $T=m_Kt$ and $b^{m_Kt}-1=(b^{m_K}-1)\Phi$ with $\Phi=\sum_{i<t}b^{m_Ki}$. Since $b^{m_K}\equiv1\pmod{D_{K-1}}$, $\Phi\equiv t\pmod{D_{K-1}}$. Because $D_K=D_{K-1}(b^{m_K}-1)$, $D_K\mid b^T-1$ if and only if $D_{K-1}\mid\Phi$, if and only if $D_{K-1}\mid t$.

(c) Every prime $q\mid D_K$ divides $x-1$ with $x=b^{m_K}$, since the chain gives $b^{m_j}-1\mid x-1$. Again $T=m_Kt$. By lifting the exponent, $v_q(x^t-1)=v_q(x-1)+v_q(t)$ for odd $q$. For $q=2$ the same holds when $4\mid x-1$, which the parity hypothesis guarantees ($b^2\equiv1\pmod8$ for odd $b$). So $D_K\mid x^t-1$ if and only if $v_q(t)\ge v_q(D_K)-v_q(x-1)=v_q(D_{K-1})$ for all $q$, i.e. $D_{K-1}\mid t$.

(c′) Odd primes $q$ behave as in (c). Now $x=b^{m_K}\equiv3\pmod4$ and every $b^{m_j}-1\equiv2\pmod4$, so $v_2(D_K)=K$ and $v_2(D_{K-1})=K-1$. For odd $t$, $v_2(x^t-1)=1$. For even $t$, $v_2(x^t-1)=v_2(x-1)+v_2(x+1)+v_2(t)-1=v_2(b+1)+v_2(t)$, since $b^{m_K}+1=(b+1)(b^{m_K-1}-\cdots+1)$ with an odd second factor. As $K\ge2$, $t$ must be even with $v_2(t)\ge\max(1,K-v_2(b+1))$. Hence $T_K/m_K$ is the odd part of $D_{K-1}$ times $2^{\max(1,K-v_2(b+1))}$, and $m_KD_{K-1}/T_K=2^{K-1-\max(1,K-v_2(b+1))}=2^{\min(K-2,\,v_2(b+1)-1)}$.

(d) $\gcd(2^a-1,2^c-1)=2^{\gcd(a,c)}-1=1$, so the order is $\operatorname{lcm}(m_j)=\prod m_j$. Also $2^n\bmod(2^{m_j}-1)$ depends only on $n\bmod m_j$, and over $n<\prod m_j$ the tuple $(n\bmod m_j)_j$ runs uniformly over $\prod\mathbb Z/m_j$ by the Chinese remainder theorem. $\square$

For the admissible example $m=(2,4,48,43200)$ of Phase 21, (b) gives $T=(2,12,2160,43200\cdot D_3)$. The script verifies (b)–(d) by exact order tests, $b^T\equiv1$ and $b^{T/q}\not\equiv1$ for every prime $q\mid T$, for the schedules in the table of §2.5. It verifies (d)'s convolution identity exactly for $M=\{2,3,5\}$, and (c′) by exact order tests for the odd chains $\{3,9,27,81\}$ and $\{1,3,15,45\}$ in bases $3,7,11$ (18 cases; for $b=3$, $M=\{3,9,27\}$ the factor is $2$).

### 2.3 Tracking

**Lemma D3.10.** For $K\ge1$, $b^{-m_{K+1}}\le P_b(M)-R_K\le32\,b^{-m_{K+1}}$. Hence $\|b^nP_b(M)-b^nR_K\|\le32\,b^{n-m_{K+1}}$. If moreover $b^{m_{K+1}}\ge64$ and $P_b(M)$ and $R_K$ agree in their first $A\ge1$ fractional digits, then $A<m_{K+1}$.

*Proof.* $P_b(M)-R_K=R_K(\prod_{k>K}(1-b^{-m_k})^{-1}-1)$ with $1\le R_K<4$. The bracket is at least $b^{-m_{K+1}}$. Since $s=\sum_{k>K}b^{-m_k}\le2b^{-m_{K+1}}$, it is at most $e^{2s}-1\le4s$. For the digit statement, $0<P_b(M)-R_K\le32b^{-m_{K+1}}\le\tfrac12$. If the integer parts differed, the fractional parts would differ by $1-(P_b(M)-R_K)\ge\tfrac12\ge1/b$, so they could not lie in the same digit cell $[i/b,(i+1)/b)$ and the first fractional digits would differ. So the integer parts agree, $|P_b(M)-R_K|<b^{-A}$, and $b^{-m_{K+1}}<b^{-A}$. $\square$

The hypothesis $b^{m_{K+1}}\ge64$ cannot be dropped: for $b=2$, $M=\{1,2,4,5,6,8,9\}$ and $K=1$, $R_1=2$ while $P_2(M)=3.00036\ldots$, and the fractional parts agree in 11 binary digits although $m_2=2$ (script).

So on $[0,m_{K+1}-O(\log m_{K+1}))$ the orbit of $P_b(M)$ tracks the orbit of $R_K$: the two orbits are close, with $\|b^nP_b(M)-b^nR_K\|\le32\,b^{n-m_{K+1}}$, but they are not identical. The orbit of $R_K$ is purely periodic with period $T_K$.

### 2.4 Distribution along tetration steps, with arbitrary filling

**Theorem D3.11.** Let $K\ge2$ with $T_{K-1}\mid m_K$. For every $N$ with $T_K\le N\le m_{K+1}$ and every integer $L\ge1$,

```math
D_N\bigl(P_b(M)\bigr)\ \le\ \frac6{D_{K-1}}+\frac{T_K}N+\frac LN+64\,b^{-L},\qquad T_K=m_KD_{K-1}.
```

Consequently, if infinitely many $K$ satisfy $T_{K-1}\mid m_K$ and $m_{K+1}/(m_KD_{K-1})\to\infty$ along them, then $\liminf_ND_N(P_b(M))=0$. In particular $P_b(M)\notin K_b$. Nothing is assumed about the other elements of $M$.

*Proof.* Phase 21, Lemma D2.2, uses only $T_{K-1}\mid m_K$, $\gcd(b,D_{K-1})=1$ and reducedness of $R_{K-1}$. It gives that the cycle Fourier coefficients $\widehat C_K(h)$ of $R_K$ vanish unless $D_{K-1}\mid h$. The Erdős–Turán inequality with $H=D_{K-1}-1$ bounds the full-period discrepancy by $6/D_{K-1}$. (If $D_{K-1}=1$, which happens only for $b=2$, $K=2$, $m_1=1$, the bound $6/D_{K-1}\ge1$ is trivial and Erdős–Turán with cutoff zero is not needed.) Writing $N=qT_K+r$ gives $ND_N(R_K)\le qT_KD_{T_K}(R_K)+r$, so $D_N(R_K)\le6/D_{K-1}+T_K/N$.

By Lemma D3.10, for $n<\min(N,m_{K+1}-L)$ we have $\|b^nP_b(M)-b^nR_K\|\le32b^{-L}$, and at most $L$ indices $n<N$ remain. If $\|y_n-x_n\|\le\eta$ off a set of $B$ indices, then for every arc $J$, $\#\{x_n\in J\}\le\#\{y_n\in J^\eta\}+B$ and $\#\{x_n\in J\}\ge\#\{y_n\in J^{-\eta}\}-B$, so $|D_N(x)-D_N(y)|\le2\eta+B/N$. This gives the bound. For the consequence, take $N=m_{K+1}$ and $L=\lceil\log_bm_{K+1}\rceil$, and use $D_{K-1}\ge b^{m_{K-1}}-1\to\infty$ and Proposition D3.9(b). $\square$

**Corollary D3.12 (upper density one).** There is $M\subseteq\mathbb Z_{\ge1}$ of upper density 1, containing arbitrarily long blocks of consecutive integers, with $\liminf_ND_N(P_b(M))=0$.

*Construction.* Start from any nonempty finite set. Given $m_1<\dots<m_{K-1}$, let $m_K$ be the least multiple of $T_{K-1}$ above $m_{K-1}$, let $m_{K+1}=K\,m_KD_{K-1}$, and append the block $m_{K+1}+1,\dots,(K+1)m_{K+1}$. Then repeat from the end of the block. At the marked indices, $T_{K-1}\mid m_K$ and $m_{K+1}/(m_KD_{K-1})=K\to\infty$. At $X=(K+1)m_{K+1}$, $\#(M\cap[1,X])\ge Km_{K+1}=\frac K{K+1}X$. $\square$

So locally partition-like behaviour, even on most of $[1,X]$ for infinitely many $X$, does not prevent near-uniform stretches. What the corollary does not give: normality (the windows between marked indices are uncontrolled) or any statement about $M=\mathbb Z_{\ge1}$.

The script illustrates the mechanism with $M=\{1,2,3,6,252\}$ ($T_3=6\mid m_4$, $T_4=126\mid m_5$). It finds $T_5=252\cdot D_4=333{,}396$. The full-period discrepancy of $R_5$ is $0.00073\le6/D_4=0.00454$, $|\widehat C_5(h)|<10^{-6}$ for $h=1,2,3$, and $|\widehat C_5(D_4)|=0.987$. Any $m_6\ge\omega T_5$ makes $P_2(M)$ follow this law on $[0,m_6)$.

### 2.5 The tracking/period phase diagram

The reciprocal mechanism of Phases 20–21 needs **(R1)**: the tracked prefix, of length at most $m_{K+1}$ by Lemma D3.10, contains many full periods $T_K$. It also needs **(R2)**: the full-period law is known.

| schedule $M$ | period $T_K$ | (R1): $m_{K+1}/T_K$ | (R2) | carry window at $N$ |
| --- | --- | --- | --- | --- |
| polynomial $\{k^d\}$ ($d=1$: $P_b$) | $\ge\operatorname{lcm}(1,\dots,K)^d=e^{dK(1+o(1))}$ | $\to0$ exponentially | — | $\asymp N^{1/(d+1)}$ |
| chains: $\{c^k\}$, $\{k!\}$, $\{2^{k^2}\}$, $\{2^{2^k}\}$ ($k\ge1$) | $=m_KD_{K-1}$ under the parity condition of D3.9(c); always $\ge m_KD_{K-1}/2^{\max(0,\,v_2(b+1)-1)}$ (D3.9(c′)) | $=2^{\epsilon_K}m_{K+1}/(m_KD_{K-1})$ with $\epsilon_K=0$ under D3.9(c) and $\epsilon_K=\min(K-2,\,v_2(b+1)-1)$ under D3.9(c′); $\to0$ for the four named chains | — | $\{2^k:k\ge0\}$: $\log_b\beta(N)+O(\log N)$ |
| pairwise coprime, $b=2$ | $=\prod_{j\le K}m_j$ | $\to\infty$ iff $m_{K+1}/\prod_{j\le K}m_j\to\infty$ | convolution law, **unknown** | — |
| admissible (A1)–(A2) | $=m_KD_{K-1}$, $T_K\mid m_{K+1}$ | $=\omega_K\to\infty$ | Fourier vanishing (Lemma D2.2) | normal (Phase 21 D2) |
| tetration steps along a subsequence | $=m_KD_{K-1}$ at those $K$ | $\to\infty$ along them | Fourier vanishing | $\liminf D_N=0$ (Thm D3.11) |

The window column for $\{k^d\}$ uses $\log p_M(n)\asymp n^{1/(d+1)}$ (Hardy–Ramanujan for $d=1$; Wright, Acta Math. 63 (1934), for $d\ge2$) and the window transfer of Phase 20, Lemma D1.1. Here $\operatorname{lcm}(k^d:k\le K)=\operatorname{lcm}(1,\dots,K)^d$, and the prime number theorem gives the exponential growth.

**Conclusion.** Polynomial growth, geometric growth, and the named super-exponential *divisibility chains* ($k!$, $2^{k^2}$, $2^{2^k}$) fall far below the tetration threshold: their periods are $m_KD_{K-1}$ under the parity condition of Proposition D3.9(c), and in every case at least $m_KD_{K-1}/2^{\max(0,\,v_2(b+1)-1)}$ by (c′), so $m_{K+1}/T_K\to0$ for all of them. Among the schedules in the table, the only regime below tetration where (R1) holds is the coprime one, where the period is a product rather than a tower. For a general chain the exact ratio in the table can be unbounded along one subsequence and tend to $0$ along another, so no dichotomy is claimed beyond the named schedules. Outside the table, (R1) can hold without pairwise coprimality. In base 2 take $m_j=2p_j$ with distinct primes $p_j>3$ in $[\exp(3^j),2\exp(3^j)]$. The numbers $(4^{p_j}-1)/3$ are pairwise coprime and prime to $3$, the order of $2$ modulo each divides $2p_j$, and the remaining factor of $D_K$ is $3^K$. So $T_K\mid2\cdot3^{K-1}\prod_{j\le K}p_j$ and $m_{K+1}/T_K\to\infty$. This side observation plays no role in Theorem S or Theorem D1.5. There (R2) fails, because the component numerators $c_j^{(K)}$ depend on every earlier $m_i$ and no vanishing is forced. For $M=\{2^k:k\ge1\}$, the case $K=2$ of Proposition D3.9(c) gives $T_2=4(b^2-1)$ in every base.

Finite table (base 2, exact orders; the script prints it):

| schedule | $K$ | $m_K$ | $m_{K+1}$ | $\log_2T_K$ | formula | $m_{K+1}/T_K$ |
| --- | --- | --- | --- | --- | --- | --- |
| $\mathbb Z_{\ge1}$ | 10 | 10 | 11 | 23.8 | exact | $7.5\cdot10^{-7}$ |
| $k^2$ | 5 | 25 | 36 | 11.8 | exact | $0.010$ |
| $2^k$, $k\ge1$ | 8 | 256 | 512 | 261.5 | $m_KD_{K-1}$ | $9.9\cdot10^{-77}$ |
| $3^k$, $k\ge1$ | 5 | 243 | 729 | 127.7 | $m_KD_{K-1}$ | $2.6\cdot10^{-36}$ |
| $k!$, $k\ge1$ | 6 | 720 | 5040 | 161.1 | $m_KD_{K-1}$ | $1.7\cdot10^{-45}$ |
| $2^{k^2}$, $k\ge1$ | 2 / 3 | 16 / 512 | 512 / 65536 | 5.6 / 26.6 | $m_KD_{K-1}$ | 10.7 / $6.5\cdot10^{-4}$ |
| primes (coprime) | 6 | 13 | 17 | 14.9 | $\prod m_j$ | $5.7\cdot10^{-4}$ |
| admissible | 3 | 48 | 43200 | 11.1 | $m_KD_{K-1}$ | 20 |

The ratio $10.7$ for $2^{k^2}$ at $K=2$ is a small-number effect, since $D_1=3$. At $K=3$ the ratio is already $6.5\cdot10^{-4}$; in general it equals $2^{2K+1}/D_{K-1}$.

### 2.6 Mahler's binary partition constant

Let $\beta(n)$ be the number of partitions of $n$ into powers of 2 (with part 1), and $X_b=\sum_n\beta(n)b^{-n}=P_b(\{2^k:k\ge0\})$. (In §2.5 the chain $\{2^k\}$ starts at $k=1$, and $P_b(\{2^k:k\ge1\})=X_{b^2}$.)

**Proposition D3.13.**

(a) *Functional equation.* $(b-1)X_b=bX_{b^2}$, and $\prod_{j<r}(1-b^{-2^j})\,X_b=X_{b^{2^r}}$. In finite form, for every $M\ge0$,

```math
(b-1)\sum_{n\le M}\beta(n)\,b^{M-n}=b\sum_{2k\le M}\beta(k)\,b^{M-2k}-\beta(M).
```

(b) *Growth.* $\beta(2n)=\sum_{j\le n}\beta(j)\le(n+1)\beta(n)$, and for $n\ge2$, with $K=\lceil\log_2n\rceil$,

```math
\beta(n)\le4.7685\cdot2^{K(K-1)/2}.
```

Also $\log\beta(n)\sim(\log n)^2/(2\log2)$ (Mahler, J. London Math. Soc. 15 (1940); de Bruijn, Indag. Math. 10 (1948)).

(c) *Window.* There is $j_0(b)$ such that for $N\ge j_0(b)$, $n<N$ and $L<N$,

```math
\beta(N)\,b^{-L-1}\ \le\ T(N-1,L)\quad\text{and}\quad T(n,L)\le\frac{(N+1)\beta(N)}{(b-1)b^L}+2b^{-N/2},\qquad T(n,L)=\sum_{j>L}\beta(n+j)b^{-j}.
```

So the certified window to precision $N^{-A}$ is $L(N)=\log_b\beta(N)+O_{A,b}(\log N)=\frac{(\log N)^2}{2\log2\,\log b}(1+o(1))$. This is polylogarithmic, against $\asymp\sqrt N$ for $P_b$.

(d) *Period.* $\{2^k:k\ge1\}$ is a chain with $m_K=2^K$ even, so Proposition D3.9(c) gives $T_K=2^KD_{K-1}$ in every base. The tracked prefix, of length at most $2^{K+1}$, is a vanishing fraction of one period.

(e) *Transcendence.* $X_b$ is transcendental. $f(z)=\prod_{k\ge0}(1-z^{2^k})^{-1}$ satisfies $f(z^2)=(1-z)f(z)$ and is transcendental over $\mathbb C(z)$. Indeed, let $\zeta^{2^r}=1$ and $0<\rho<1$. Iterating the functional equation $r$ times gives $|f(\rho\zeta)|=f(\rho^{2^r})/\prod_{j<r}|1-(\rho\zeta)^{2^j}|$; as $\rho\to1^-$ the numerator tends to $\infty$ and the denominator stays bounded. So every root of unity of 2-power order is a singularity of $f$, the unit circle is a natural boundary, and $f$ is not algebraic. Mahler's theorem (Math. Ann. 101 (1929); see Nishioka, *Mahler Functions and Transcendence*, LNM 1631, Ch. 1) applies at $z=1/b$.

(f) *What (a) gives.* Rational multiples preserve normality (Wall 1949), and normality in base $b$ is equivalent to normality in base $b^k$. So $X_b$ is normal in base $b$ if and only if $X_{b^{2^r}}$ is normal in base $b$, for any $r$. For $b=2$, $X_2=2X_4$, and $\mathbb Z[1/2]$ acts on $K_2$, so $X_2\in K_2$ if and only if $X_4\in K_2$. These are equivalences between open problems. The functional equation transports the question to another base and decides nothing.

*Proof.* (a) $(1-q)f(q)=f(q^2)$ coefficientwise reads $\beta(n)-\beta(n-1)=[2\mid n]\beta(n/2)$. Multiply the truncated series by $(1-q)$ and evaluate at $q=1/b$. (b) Telescoping the recurrence $\beta(2n)=\beta(2n-1)+\beta(n)$, $\beta(2n+1)=\beta(2n)$ gives $\beta(2n)=\sum_{j\le n}\beta(j)$. Since $\beta$ is nondecreasing, $\beta(2^k)\le\prod_{i<k}(2^i+1)=2^{k(k-1)/2}\prod_{i<k}(1+2^{-i})\le2\cdot2.38424\cdot2^{k(k-1)/2}$, since $\prod_{i\ge1}(1+2^{-i})=2.384231\ldots$. (c) For $j\le N$, $\beta(n+j)\le\beta(2N)\le(N+1)\beta(N)$. For $j>N$, $\beta(n+j)\le\beta(2j)\le4.7685\cdot2^{(\log_2j+2)(\log_2j+1)/2}\le\tfrac12b^{j/2}$ once $j\ge j_0(b)$, so $\sum_{j>N}\beta(n+j)b^{-j}\le\tfrac12b^{-N/2}/(\sqrt b-1)\le\tfrac12(1+\sqrt2)\,b^{-N/2}<2b^{-N/2}$. The lower bound is the first omitted term. $\square$

The script checks $\beta(2n)=\sum_{j\le n}\beta(j)$ for $n\le2000$, the bound in (b) for $n\le4096$, the parity $2\mid\beta(n)$ for $2\le n\le4800$ (Churchhouse), and the finite identity in (a) exactly for $b\in\{2,3,10\}$ and $M\in\{50,301,1000\}$. The exact windows ($b=2$, $\tau=N^{-2}$) are $L=44,52,70$ at $N=500,1000,4000$. Compare $\log_2\beta(N)+2\log_2N=42.6,50.8,69.8$ and, for $P_2$, $L=251$ at $N=4000$ (Phase 21). The normalized growth $\log\beta(n)/((\log n)^2/2\log2)$ is $0.606,0.622,0.641$ at $n=2^8,2^{10},2^{12}$; Mahler's asymptotic converges slowly.

### 2.7 Progression splits and Euler's identities

**Proposition D3.14.**

(a) For $d\ge1$, $P_b=\prod_{r=0}^{d-1}P_{b,r,d}$ with $P_{b,r,d}=\prod_{m\equiv r\,(d)}(1-b^{-m})^{-1}$, and $P_{b,0,d}=P_{b^d}$.

(b) $P_b=Q_b\,P_{b^2}$, where $Q_b=\prod_{m\ge1}(1+b^{-m})=\sum_nq(n)b^{-n}$ counts partitions into distinct parts.

(c) $1/Q_b=E_b/E_{b^2}=\prod_{k\ge1}(1-b^{-(2k-1)})=\sum_n(-1)^n\,\mathrm{sc}(n)\,b^{-n}$, where $\mathrm{sc}(n)$ is the number of partitions of $n$ into distinct odd parts, equivalently the number of self-conjugate partitions. There is no cancellation, and $\log\mathrm{sc}(n)\sim\pi\sqrt{n/6}$.

*Proof.* All identities hold as formal power series in $q$ and, by absolute convergence, at $q=1/b$. (a) Group the factors by residue. (b) Euler's identity (the even factors cancel) $\prod(1+q^m)=\prod_{m\text{ odd}}(1-q^m)^{-1}$, and $\prod_{m\text{ even}}(1-q^m)^{-1}=P(q^2)$. (c) $\prod(1+q^m)^{-1}=\prod(1-q^m)/\prod(1-q^{2m})$. In $\prod_{k}(1-q^{2k-1})$, a partition of $n$ into $j$ distinct odd parts contributes $(-1)^j$, and $j\equiv n\pmod2$. The asymptotic is the standard Meinardus-type estimate for $\prod(1+q^{2k-1})$. $\square$

Each factor in (a)–(c) is again a dense-coefficient constant with sub-exponential growth. Its support has density one after rescaling. In the common series variable $q=1/b$, a factor $P_{b,r,d}$ with $g=\gcd(r,d)>1$ (including $r=0$, where $g=d$) is supported on multiples of $g$; for example $P_{b^2}=P(q^2)$ has support of density $\tfrac12$. After the substitution of Proposition D3.8(a) its support is cofinite. The factors with $\gcd(r,d)=1$, and $Q_b$ and $1/Q_b$, have cofinite support directly. Neither $K_b$ nor the set of normal numbers is closed under multiplication (Phase 20, §4.2), so these splittings replace one open problem by products of others. The script verifies (b) and (c) through $q^{800}$ ($\mathrm{sc}(200)=312{,}928$).

### 2.8 Finite measurements (not evidence)

Base 2, first 4000 digits, from exact coefficient sums with a 700-term margin:

| constant | $D_{1000}$ | $D_{2000}$ | $D_{4000}$ | freq. of 1 | max dev. of 2-words | digit-change density |
| --- | --- | --- | --- | --- | --- | --- |
| $P_2$ | 0.0247 | 0.0186 | 0.0253 | 0.4893 | 0.0184 | 0.5158 |
| $P_2(\{k^2\})$ | 0.0368 | 0.0393 | 0.0175 | 0.5070 | 0.0103 | 0.4935 |
| $P_2(\{2^k:k\ge0\})=X_2$ | 0.0301 | 0.0228 | 0.0220 | 0.5042 | 0.0082 | 0.5080 |

The $P_2$ row agrees with Phase 21, §1.6. All three look like typical binary expansions at this length. By Corollary D4.9′ the last column would tend to $0$ if the constant were in $K_2$. A value near $\tfrac12$ at $N=4000$ decides nothing.

### 2.9 What remains open in D3

1. Normality, $D^+<1$, or $K_b$ membership of $P_b$, $P_b(\{k^2\})$, $P_b(\{2^k\})$, for any $b$.
2. Whether $P_b(M)\in K_b$ is possible for some infinite $M$. Finite $M\neq\{1\}$ never works (Proposition D3.8(d)).
3. A normal $P_b(M)$ with $M$ of positive lower density.
4. The full-period law for coprime schedules (R2 below tetration).

## 3. D4: signed digits and carry cancellation

### 3.1 Definitions

For an integer $x\ne0$ let $w_b^\pm(x)$ be the least $r$ such that $x=\sum_{i=1}^ru_ib^{e_i}$ with distinct $e_i\ge0$ and $u_i\in\{\pm1,\dots,\pm(b-1)\}$. Let $w_1(x)$ be the least $s$ with $x=\sum_{i=1}^s\pm b^{f_i}$, repetitions allowed. For $b=2$, $w_2^\pm$ is the weight of the non-adjacent form (Reitwiesner 1960), and the script confirms $w_2^\pm(x)=\operatorname{popcount}(3x\oplus x)$ for $x<2^{16}$.

A **local decomposition** of $a$ assigns to each $m$ a finite multiset $\mathcal D_m$ of pairs $(u,e)$, $u\in\mathbb Z\setminus\{0\}$, $e\ge0$, with $\sum_{\mathcal D_m}ub^e=a(m)$ and $\sum_m\sum_{\mathcal D_m}|u|b^{e-m}<\infty$. Its **net displaced sequence** is $A_{\rm net}(t)=\sum_m\sum_{(u,e)\in\mathcal D_m,\,m-e=t}u$, and its **local count** is $r(m)=|\mathcal D_m|$. Absolute convergence and $|u|\ge1$ give finitely many pairs at each $t$, so $A_{\rm net}(t)\in\mathbb Z$.

### 3.2 Net transfer

**Theorem D4.8.** Let $\mathcal D$ be a local decomposition of $a$ with $m-e\ge-E_0$ for all pairs. Then $F_b(a)=c_0+\sum_{t\ge1}A_{\rm net}(t)b^{-t}$ with $c_0=\sum_{-E_0\le t\le0}A_{\rm net}(t)b^{-t}\in\mathbb Z$. Consequently $F_b(a)\in K_b$ whenever, for some $c\in\mathbb Z$, the sequence $A'(t)=A_{\rm net}(t)-c$ ($t\ge1$) satisfies one of:

- (i) $\sum_{t\le X}|A'(t)|\le CX$ and $S_{A'}(X)=o(X)$;
- (ii) $\sum_{t\le X}|A'(t)|\le C(X+1)^k$ and $S_{A'}(X)\log X=o(X)$;
- (iii) $\sum_{t\le X}|A'(t)|\le CX\log^\gamma(X+2)$ and $S_{A'}(X)\log\log X=o(X)$.

*Proof.* Absolute convergence permits the rearrangement. The terms with $t\le0$ are integers. Then $F_b(a)=c_0+c/(b-1)+F_b(A')$ with $c/(b-1)\in F_b$, and $K_b+F_b=K_b$ (Phase 19). Conditions (i), (ii), (iii) are the hypotheses of the kernel-verified `linear_mass_sparse_tendsto_one` ([`CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean)), `poly_mass_sparse_tendsto_one` and `log_mass_sparse_tendsto_one` ([`GeneralMassTransfer.lean`](../../NormalityChecker/GeneralMassTransfer.lean)) applied to $A'$. $\square$

The *local* sufficient condition is $S_{A_{\rm net}}(X)\le\#\{\text{pairs with }1\le m-e\le X\}=o(X)$, with bounded $|u|$. It counts signed digits before any cancellation between different indices $m$.

### 3.3 Completeness: net cancellation is the whole problem

**Theorem D4.9.** $x\in K_b$ if and only if there are $c\in F_b$ and integers $A(t)$, $t\ge1$, with $|A(t)|\le\lfloor b/2\rfloor$, $S_A(N)=o(N)$ and $x-c-\sum_{t\ge1}A(t)b^{-t}\in\mathbb Z$. One may take $A(t)=I_t-bI_{t-1}$ with $I_t=\lfloor b^t(x-c)+\tfrac12\rfloor$, and then

```math
S_A(N)\le\#\{0\le n<N:\ \|b^n(x-c)\|\ge1/(2b)\}.
```

*Proof.* "If" is Theorem D4.8(i). "Only if": by Phase 19, $x=c+w$ with $M_N(w)\to0$. With $I_t$ as stated, $\sum_{t=1}^TA(t)b^{-t}=b^{-T}I_T-I_0\to w-I_0$. Put $\varepsilon_t=I_t-b^tw\in(-\tfrac12,\tfrac12]$. Then $A(t)=\varepsilon_t-b\varepsilon_{t-1}$ lies strictly between $-(b+1)/2$ and $(b+1)/2$, so $|A(t)|\le\lfloor b/2\rfloor$. If $\|b^{t-1}w\|<1/(2b)$, then $|b^tw-bI_{t-1}|<\tfrac12$, so $I_t=bI_{t-1}$ and $A(t)=0$. Markov's inequality gives $S_A(N)\le2bN\,M_N(w)=o(N)$. $\square$

**Corollary D4.9′ (base 2).** Let $d_1d_2\cdots$ be the binary digits of $x$ (not ending in all 1s). Then $x\in K_2$ if and only if $\#\{1\le n\le N:d_n\ne d_{n+1}\}=o(N)$. The canonical sequence is $A(n)=d_{n+1}-d_n$.

*Proof.* $F_2=\mathbb Z$. If $d_{n+1}\ne d_{n+2}$, then $\{2^nx\}\in[\tfrac14,\tfrac34)$, so $\|2^nx\|\ge\tfrac14$. Conversely, if the digits $n+1,\dots,n+L$ are constant, then $\|2^nx\|\le2^{-L}$, and at most $L\cdot\#\{\text{changes up to }N+L\}$ indices $n<N$ fail this. $I_n=\lfloor2^nx\rfloor+d_{n+1}$ gives $A(n)=d_{n+1}-d_n$. $\square$

For general $b$ the same argument shows: $x\in K_b$ if and only if either (i) for some $1\le j\le b-2$, $\#\{n\le N:d_n\ne j\}=o(N)$; or (ii) $\#\{n\le N:(d_n,d_{n+1})\notin\{(0,0),(b-1,b-1)\}\}=o(N)$.

**Consequence.** The net displaced measure is a *complete* invariant: every element of $K_b$ has a net representation with bounded coefficients and density-zero support, and that representation is computed from the digits of $x$ itself. Hence no theorem can block "signed-digit transfer with arbitrary cross-index cancellation": such transfer is equivalent to membership. A barrier can only address decompositions specified in advance, such as per-coefficient (local) ones. §3.5 proves that barrier.

### 3.4 Examples beyond the raw width wall

**(E1) Phase 21, Proposition D4.6.** $F=\sum_m(2^{w(m)}-1)2^{-m}$ with $w(m)$ the binary length. The decomposition $+2^{w(m)}-2^0$ has $r(m)=2$, so the local count $\sum_{m\le N}r(m)=2N$ is not $o(N)$. Yet

```math
A_{\rm net}(t)=[t=0]+[t\in\{2^s-s-1\}],
```

because the $-1$ placed at $t=m$ by index $m$ cancels the $+1$ placed at $t$ by the index $m'$ with $m'-w(m')=t$. So $S_{A_{\rm net}}(X)=O(\log X)$ and Theorem D4.8(i) applies. The script verifies this through $t\le4083$. The cancellation is between different indices.

**(E2) Quadratic width, the maximal order.** If $F_b(a)$ converges, then $|a(m)|<b^m$ for large $m$, so the raw width satisfies $W(N)\le N^2/2+O(N)$; super-quadratic raw width ($W(N)/N^2\to\infty$) is impossible. This order is attained inside $K_b$. Let

```math
a(m)=b^{\lfloor m/2\rfloor}-1+[m\in\{2^s:s\ge0\}].
```

Then $W_U(N)\sim N^2/4$ (the script measures $0.2498\,N^2$ at $N=3000$). Each $t\ge1$ receives $+1$ from $m=2t-1$ and $m=2t$ and $-1$ from $m=t$, so $A_{\rm net}(t)=1+[t\in\{2^s:s\ge0\}]$ and

```math
F_b(a)=\frac1{b-1}+\Lambda_b,\qquad\Lambda_b=\sum_{s\ge0}b^{-2^s}.
```

This is an irrational element of $F_b+K_b=K_b$ (Theorem D4.8(i) with $c=1$).

### 3.5 Three counting lemmas

**Lemma D4.10 (exponents).** If $x=\sum_{i=1}^ru_ib^{e_i}$ with $e_1>\dots>e_r\ge0$ and $1\le|u_i|\le b-1$, then $|x|\ge b^{e_1-r+1}$.

*Proof.* $|x|\ge b^{e_1}-(b-1)(b^{e_1-1}+\dots+b^{e_1-r+1})=b^{e_1-r+1}$. $\square$

**Lemma D4.11 (carry normalization).** If $x=\sum_ec_eb^e$ (finite), then $w_b^\pm(x)\le\sum_e|c_e|$. In particular $w_b^\pm\le w_1$, and a decomposition $x=\sum_{i\le r}u_ib^{e_i}$ with $|u_i|\le B$ has $r\ge w_b^\pm(x)/B$.

*Proof.* Proceed upward from the lowest position. If $|c_e|\ge b$, write $c_e=qb+s$ with $s$ of the sign of $c_e$ and $|s|<b$, replace $c_e$ by $s$, and add $q$ to $c_{e+1}$. The potential $\sum|c_e|$ changes by at most $|s|+|q|-|c_e|=-(b-1)|q|<0$. The process terminates with all $|c_e|\le b-1$ and at most the initial potential of nonzero digits. $\square$

**Lemma D4.12 (entropy count).** For $X\ge b$ and $k\ge0$,

```math
\#\{x:\ 0<|x|\le X,\ w_b^\pm(x)\le k\}\ \le\ \sum_{r=0}^{k}\binom Er(2b-2)^r-1,\qquad E=\lfloor\log_bX\rfloor+k .
```

If $N\ge b^2$, $A\ge1$, $\theta\in[2^{-20},1]$, $X=N^A$ and $k\le\frac\theta{40A}\log_bN$, then the count is at most $N^\theta$.

*Proof.* By Lemma D4.10 all exponents of a representation of weight $r\le k$ are at most $\log_bX+k-1$, which leaves $E$ positions; then choose $r$ positions and signed digits. For the second claim, let $\ell=\log_bN$ and $c=k/\ell\le c^*=\theta/(40A)$. Since $E\le A\ell+k$, $k\le E/2$, and $y\mapsto yH(k/y)$ increases, we get $\sum_{r\le k}\binom Er\le2^{(A+c)\ell H(c/(A+c))}$, where $H$ is the binary entropy. Using $H(p)\le p\log_2(e/p)$, the base-2 logarithm of the count is at most $c\ell[\log_2(2b-2)+\log_2(e(1+A/c))]$. This expression increases in $c$. At $c=c^*$, with $\log_2(2b-2)\le2\log_2b$ and $\log_2(e(1+40A^2/\theta))\le26.8+2\log_2A\le(26.8+2\log_2A)\log_2b$, it is at most $\theta\ell\log_2b\,(28.8+2\log_2A)/(40A)\le\theta\ell\log_2b$. $\square$

The script checks Lemma D4.12's first bound exactly for $b=2$ ($X=2^{14}$) and $b=3$ ($X=3^9$) with $k\le5$. It checks Lemma D4.10 exhaustively for $b=2,3$, $r\le3$, exponents $\le10$, and Lemma D4.11 on 9,000 random multisets.

### 3.6 The entropy–multiplicity wall

**Theorem D4.13.** Let $b\ge2$, $A\ge1$, $\theta\in[2^{-20},1]$ and $c=\theta/(40A)$. Let $N\ge b^2$, let $\mathcal T\subseteq[1,N]$ with $0<|a(n)|\le N^A$ on $\mathcal T$, and let $\mu=\max_y\#\{n\in\mathcal T:a(n)=y\}$. Then

```math
\#\{n\in\mathcal T:\ w_b^\pm(a(n))\le c\log_bN\}\le\mu N^\theta,\qquad\sum_{n\in\mathcal T}w_b^\pm(a(n))\ \ge\ c\log_bN\,\bigl(|\mathcal T|-\mu N^\theta\bigr).
```

Every local decomposition with $|u|\le B$ has $\sum_{n\in\mathcal T}r(n)\ge(c/B)\log_bN\,(|\mathcal T|-\mu N^\theta)$.

*Proof.* Each value $y$ with $w^\pm(y)\le c\log_bN$ and $|y|\le N^A$ is taken at most $\mu$ times, and there are at most $N^\theta$ such $y$ (Lemma D4.12). The last claim follows from Lemma D4.11. $\square$

**Lemma D4.14 (values at primes for CM forms).** Let $g$ be one of $\eta(6\tau)^4$, $\eta(4\tau)^6$, $\eta(3\tau)^8$, of weight $k\in\{2,3,4\}$, with CM by $F=\mathbb Q(\sqrt{-3})$, $\mathbb Q(i)$, $\mathbb Q(\sqrt{-3})$. There is $C_g$ such that $\#\{p\le Y:\ a(p)=t\}\le C_g\sqrt Y$ for every integer $t\ne0$ and every $Y\ge1$.

*Proof.* We use the standard description of a CM newform by a Hecke character (Hecke; Ribet, LNM 601 (1977)), as in Phase 21, Lemma W.2. $\mathcal O_F=\mathbb Z[\omega]$ has class number one. For a split prime $p\nmid$ level, $p=\alpha\bar\alpha$ with $a(p)=2\operatorname{Re}(\chi(\alpha)\alpha^{k-1})$, where $\chi$ takes values in a finite set $Z$ of roots of unity. Inert primes have $a(p)=0\ne t$, and finitely many primes divide the level.

For $\zeta\in Z$, $Q_\zeta(x,y)=2\operatorname{Re}(\zeta(x+y\omega)^{k-1})-t$ is a nonzero real polynomial of degree $k-1$: its top-degree part is the real part of a nonzero homogeneous polynomial in $z=x+y\omega\in\mathbb C$. If $N(\alpha)\le Y$, then $|x|,|y|\le2\sqrt Y$. A nonzero polynomial $Q=\sum_jc_j(x)y^j$ of degree $\delta$ has at most $2\delta(2R+1)$ zeros in $\{-R,\dots,R\}^2$. Indeed, at most $\delta$ values of $y$ for each $x$ with $c_{j^*}(x)\ne0$ ($j^*$ the top index), plus $2R+1$ values for each of the at most $\delta$ roots of $c_{j^*}$. Each prime has a generator $\alpha$ in the box. Hence the count is at most $|Z|\cdot2(k-1)(4\sqrt Y+1)$ plus the primes dividing the level. $\square$

**Corollary D4.15.** In every radix $b\ge2$, with $W_\pm(N)=\sum_{n\le N,\ a(n)\ne0}w_b^\pm(a(n))$:

(a) $D(\Theta_3(1/b)^2)=\sum_nn\,r_2(n)b^{-n}$: $W_\pm(N)\asymp N\sqrt{\log N}$;

(b) $D(E_b^2)=\sum_nn\,a_2(n)b^{-n}$: $W_\pm(N)\asymp N(\log N)^{1/4}$;

(c) $E_b^4$, $E_b^6$, $E_b^8$: $W_\pm(N)\asymp N\sqrt{\log N}$.

The same lower bounds hold, divided by $B$, for the local count $\sum_{n\le N}r(n)$ of every local decomposition with $|u|\le B$.

*Proof.* The upper bounds are $W_\pm\le\sum_{a(n)\ne0}(1+\log_b|a(n)|)$, together with the support sizes ($\ll N/\sqrt{\log N}$, $\ll N/(\log N)^{3/4}$, $\ll N/\sqrt{\log N}$) and $|a(n)|\le N^{O(1)}$.

(a) Take $\mathcal T=\{n\le N:r_2(n)>0\}$; $|\mathcal T|\sim K_{\rm LR}N/\sqrt{\log N}$ (Landau–Ramanujan). Next, $nr_2(n)\le4n\tau(n)\le8N^{3/2}\le N^2$ for $N\ge64$, so $A=2$. If $nr_2(n)=y$, then $n=y/r_2(n)$ with $r_2(n)=4j$, $1\le j\le\max_{n\le N}\tau(n)$, so $\mu\le\max_{n\le N}\tau(n)=N^{o(1)}$ (Wigert). With $\theta=\tfrac14$, Theorem D4.13 gives $W_\pm(N)\ge(\tfrac1{320}-o(1))\log_bN\cdot K_{\rm LR}N/\sqrt{\log N}$.

(b) Take $\mathcal T=\operatorname{supp}a_2\cap[1,N]$; $|\mathcal T|\gg N(\log N)^{-3/4}$ by Phase 20, Theorem 6(b). Here $n|a_2(n)|\le n\,\tau(12n+1)\le N^2$, and $\mu\le2\max_{m\le12N+1}\tau(m)=N^{o(1)}$.

(c) Work in the index of $f_r=\eta(24\tau/g_r)^r$, $r\in\{4,6,8\}$, for which $c_r(n)=a_{f_r}((24n+r)/g_r)$, and every supported index lies in the progression $r/g_r\bmod24/g_r$. Let $\mathcal T_f$ be the set built in Phase 21, Theorem D4.4: $n=pm\le Y$ with $p\in\mathcal P\cap(Y^{1/2},Y^{3/4}]$ and $a(m)\ne0$. Then $|\mathcal T_f|\gg Y/\sqrt{\log Y}$ and $a(n)=a(p)a(m)\ne0$. For $y\ne0$, Lemma D4.14 gives

```math
\#\{n\in\mathcal T_f:a(n)=y\}\le\sum_{m\le Y^{1/2}}\#\{p\le Y^{3/4}:a(p)=y/a(m)\}\le C_gY^{1/2}\cdot Y^{3/8}=C_gY^{7/8}.
```

With $A=k$ (Deligne: $|a(n)|\le\tau(n)n^{(k-1)/2}\le Y^k$) and $\theta=\tfrac1{16}$, $\mu Y^\theta\le C_gY^{15/16}=o(|\mathcal T_f|)$. Pull back along the linear change of index. $\square$

### 3.7 What the wall says

- **Signed digits separate what raw width confused.** Raw width ranks $F$ (about $N\log_2N$) *above* the CM forms (about $N\sqrt{\log N}$). Signed width ranks $F$ at $\sim2N$ and the CM forms, $D(\Theta_3^2)$ and $D(E_b^2)$ strictly above linear. So the NAF picture explains why $F$ is cheap: each coefficient is two signed digits.
- **But linear signed width is not $o(N)$.** $F$ still enters $K_2$ only through cross-index cancellation (E1). For the CM forms, Corollary D4.15 says that every local decomposition with bounded digits places $\gg N\sqrt{\log N}$ signed digits from the sources $n\le N$. Any proof of membership by net cancellation must cancel all but $o(N)$ of them. By Theorem D4.9 that is exactly the membership question, so the wall is a theorem about the method, not about $E_b^4$.
- **The exponent range matters.** A binary-entropy count over $\log_bX$ positions alone is incomplete, because a signed representation may use exponents above $\log_b|x|$. Lemma D4.10 bounds them by $\log_b|x|+r-1$, and the entropy computation of Lemma D4.12 uses $E=\lfloor\log_bX\rfloor+k$ positions. The constant $c=\theta/(40A)$ is admissible; it is not optimized.
- **Multiplicity for CM forms.** The values $a(p)$ do not have bounded multiplicity. In weight 2, $|a(p)|\le2\sqrt p$ takes at most $4\sqrt Y+1$ values on the $\asymp Y/\log Y$ primes $p\le Y$, so some value is attained $\gg\sqrt Y/\log Y$ times. Lemma D4.14 gives the matching upper bound $O(\sqrt Y)$. The argument runs on the structured set $\mathcal T_f$, where the resulting bound $Y^{7/8}$ suffices.
- **Width order.** Super-quadratic width ($W_U(N)/N^2\to\infty$) is impossible for a convergent series; $W_U(N)\asymp N^2$ is attained (E2).

### 3.8 Finite measurements (base 2, $N=50{,}000$; not evidence)

| series | $S\sqrt{\log N}/N$ | $W/N$ (raw) | $W_\pm/N$ | mean $w^\pm$/bits | max multiplicity | digit-change density |
| --- | --- | --- | --- | --- | --- | --- |
| $E_2^2$ | 1.191 | 0.80 | 0.37 | — | 6949 | 0.4003 |
| $E_2^4$ | 1.789 | 4.87 | 1.67 | 0.342 | 179 | 0.5023 |
| $E_2^6$ | 1.475 | 7.46 | 2.75 | 0.369 | 21 | 0.4995 |
| $E_2^8$ | 1.257 | 9.18 | 2.98 | 0.325 | 6 | 0.5009 |
| $D(\Theta_3(1/2)^2)$ | 0.820 | 4.51 | 1.40 | 0.311 | 1 | 0.4986 |
| $D(E_2^2)$ | 1.191 | 5.72 | 2.04 | 0.357 | 3 | 0.5005 |
| $F$ | 3.289 | 14.69 | 2.00 | 0.138 | 17233 | 0.0005 |

"Mean $w^\pm$/bits" is over coefficients with at least 8 bits; it sits near the classical $\tfrac13$ for random integers. "Digit-change density" is the density of the canonical net representation of Corollary D4.9′. $E_2^2\in K_2$, yet its change density is $0.40$ at $N=50{,}000$: kernel convergence for $E_2^2$ is slow ($1-D_{2^{20}}=0.79$ in Phase 20). For the base-3 canonical representation of $E_3^4$ the nonzero density is $0.668$ at $N=20{,}000$, with $|A|\le1=\lfloor3/2\rfloor$ as Theorem D4.9 requires. In the $D(\Theta_3^2)$ row all nonzero values $nr_2(n)$ below $50{,}000$ are distinct. The entropy-count inequality $\#\{w^\pm\le3\}\le\mu\cdot(\text{Lemma D4.12 bound})$ holds in every row.

## 4. Verification record

```sh
python -B scripts/phase22_partitions_carry.py
```

Standard library only. The run takes about 6 s, performs 1,256,966 checks and exits 0. It checks the following.

- **Lemma S.** Theorem 6(a) and the $uv^2$ split for every $n\le50{,}250$; exact pair counts for $h\le50$, $n\le50{,}000$; $g^2\mid h$ on all 326,704 pairs; the CRT class, the determinant $144h/g^2$ and $u=A_1m+B_1$ on 10,719 classes; $\rho(p)\in\{1,2\}$ as in S.4(d); three exact Selberg instances ($\lambda_1=1$, $|\lambda_d|\le1$, $|r_d|\le\rho(d)$, $S\le\sum(\sum\lambda)^2\le X/G+R_\lambda\le X/G+R$, with $R_\lambda$ the weighted and $R$ the unweighted remainder; exact rational comparisons with no tolerance); as floating-point numerical samples only, the Rankin chain of S.2, the Mertens constant of S.3, the constants in $C_5$ and $\sum_{h\le H}h/\varphi(h)\le1.9436H$ for $H\le10^4$; the class (i) bound.
- **D3.** Binary partitions: recurrence, product form, the sum identity, the upper bound and the parity; the finite Mahler identity; exact windows; Euler's identities through $q^{800}$; exact periods by order tests in base 2 for $\mathbb Z_{\ge1}$, squares, the chains $2^k,3^k,k!,2^{k^2}$ ($k\ge1$), the coprime primes and the admissible schedule, including $T_K=m_KD_{K-1}$ wherever $T_{K-1}\mid m_K$ and on every base-2 chain tested; the odd-chain formula (c′) in bases 3, 7, 11; the digit bound of Lemma D3.10 under $b^{m_{K+1}}\ge64$ and the $K=1$ counterexample without it; the coprime convolution law; full-period discrepancy and Fourier vanishing for $M=\{1,2,3,6,252\}$; the finite discrepancy table.
- **D4.** The NAF formula, NAF minimality and the base-$b$ minimal-weight dynamic program; Lemmas D4.10–D4.12; multiplicities; the width table; the net sequences of (E1) and (E2); the canonical representation in bases 2 and 3.

## 5. Open problems

1. $P_b$, Mahler's $X_b$, and $P_b(\{k^2\})$: any distributional statement in any base.
2. Is there an infinite $M$ with $P_b(M)\in K_b$? Is there one with $\limsup D_N(P_b(M))=1$?
3. The full-period law of $R_K$ for coprime schedules (among the schedules in the table of §2.5, the only sub-tetration regime satisfying (R1)).
4. A decomposition-free lower bound for the canonical net density of $E_b^4$; by Theorem D4.9, this is equivalent to $E_b^4\notin K_b$.
5. The limit law of $\tfrac adE_b^2$ for odd $d>1$ (Phase 21, open problem 1). Lemma S now holds, but it gives non-membership, not the law.

## References

- T. M. Apostol, *Introduction to Analytic Number Theory*, Springer 1976, Thm. 7.3.
- F. Mertens, Ein Beitrag zur analytischen Zahlentheorie, J. reine angew. Math. 78 (1874).
- A. Selberg, On an elementary method in the theory of primes, Norske Vid. Selsk. Forh. 19 (1947); H. Halberstam and H.-E. Richert, *Sieve Methods*, Academic Press 1974, Ch. 3.
- R. A. Rankin, The difference between consecutive prime numbers, J. London Math. Soc. 13 (1938).
- E. Wirsing, Das asymptotische Verhalten von Summen über multiplikative Funktionen, Math. Ann. 143 (1961).
- K. Mahler, On a special functional equation, J. London Math. Soc. 15 (1940); Arithmetische Eigenschaften der Lösungen einer Klasse von Funktionalgleichungen, Math. Ann. 101 (1929).
- N. G. de Bruijn, On Mahler's partition problem, Indag. Math. 10 (1948).
- K. Nishioka, *Mahler Functions and Transcendence*, LNM 1631, Springer 1996.
- R. F. Churchhouse, Congruence properties of the binary partition function, Proc. Cambridge Philos. Soc. 66 (1969).
- E. M. Wright, Asymptotic partition formulae III, Acta Math. 63 (1934).
- D. D. Wall, *Normal Numbers*, PhD thesis, Berkeley 1949.
- G. W. Reitwiesner, Binary arithmetic, Advances in Computers 1 (1960).
- K. A. Ribet, Galois representations attached to eigenforms with Nebentypus, LNM 601 (1977).
- J.-P. Serre, Sur la lacunarité des puissances de η, Glasgow Math. J. 27 (1985); Y. Martin, Multiplicative η-quotients, Trans. AMS 348 (1996).
