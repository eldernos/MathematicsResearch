# Euler's product, its powers and sparse quadratic polynomials

Phase 20, Tracks A1, A2 and B5. Fix an integer radix $b\ge2$ and put

```math
E_b=\prod_{k\ge1}\left(1-b^{-k}\right).
```

**Theorem A (Euler's product).** For every $b\ge2$:

1. The base-$b$ digits of $E_b$ are explicit (Theorem 1). Apart from its first four digits, the expansion consists of blocks $1\,0^{2j}\,(b-1)^{4j}\,(b-2)\,(b-1)^{2j+1}\,0^{4j+2}$, $j=1,2,\ldots$.
2. For every $L\ge1$ the words $0^L$ and $(b-1)^L$ each have frequency $1/2$, with error at most $\bigl((2L+3)\sqrt{N/6}+3L^2+5L+7\bigr)/N$ at **every** prefix $N$. Every other word of length $L$ occurs at most $(4L-2)\sqrt{N/6}+2L^2+12L+4$ times. Thus $E_2$ is simply normal in base 2, while $E_b$ is not simply normal for $b\ge3$. The number $E_b$ is never disjunctive.
3. With $D_N$ the extreme discrepancy of $\{b^nE_b\}$, $0\le n<N$,

```math
\left|\,1-D_N(E_b;b)-\sqrt{\tfrac23}\,\frac{\log_b N}{\sqrt N}\,\right|\le\frac{C_b}{\sqrt N}\qquad(N\ge2).
```

4. Consequently $E_b\in K_b$. The worst translation error $\max_x|D_N(x+E_b)-D_N(x)|$ equals $1-D_N(E_b)$ and has the same asymptotic.

**Theorem B (cube).** $E_b^3$ has explicit digits, the words $0^L$ and $(b-1)^L$ each have frequency $1/2$, and $E_b^3$ is **disjunctive**. Moreover

```math
\left|\,1-D_N(E_b^3;b)-\sqrt2\,\frac{\log_b N}{\sqrt N}\,\right|\le\frac{C_b}{\sqrt N}.
```

**Theorem C (square).** $E_b^2=\sum_n a_2(n)b^{-n}$, where $a_2(n)$ is the coefficient of $q^{12n+1}$ in the weight-one CM form $\eta(12\tau)^2$. Its support is described by an exact prime-factorization criterion and has counting function $\asymp X/(\log X)^{3/4}$. One has $E_b^2\in K_b$ with $1-D_N=O(\log\log N/(\log N)^{3/4})$, and a matching lower bound holds.

**Theorem D (polynomials).** Every $P\in\mathbb Z[1/b][x]$ of degree at most 3 has $P(E_b)\in K_b$. For reduced $a/d$, $(a/d)E_b\in K_b$ exactly when $a/d\in\mathbb Z[1/b]$. For example $\tfrac13E_2$ has limiting discrepancy $1/2$ in base 2, and $\tfrac12E_3$ has limiting discrepancy $2/3$ in base 3.

**Theorem E (Track B5).** Fix finitely many series with bounded integer coefficients supported on values of unary quadratic polynomials, for example $E_b$, $\sum b^{-k^2}$, $\sum b^{-k(k+1)}$ and Rogers' false theta series. Every polynomial of total degree at most 2 in them with coefficients in $\mathbb Z[1/b]$ lies in $K_b$ with $1-D_N=O(\log\log N/\sqrt{\log N})$. Degree 3 is out of reach of this method: three squares already have positive density.

Scope. The finite upper bound in A.3 is a direct instance of kernel-checked Lean theorems (§3). The digit formulas, the separation lemma, the lower bounds and Theorems B, D and E are paper proofs given in full below. Theorem C(a)–(b) uses the cited fact that $\eta(12\tau)^2$ is a Hecke eigenform, which the script also verifies through $1.57\cdot10^6$. Theorem C(c) is a paper proof that uses the same published analytic inputs as the Phase 17 lower bound. All numerical statements come from the [verification script](../../scripts/phase20_euler_theta.py).

## 0. Conventions and two finite tools

Write $x_n=\{b^nz\}$ and let $D_N(z)=D_N(z;b)$ be the extreme discrepancy of $x_0,\ldots,x_{N-1}$ over half-open subintervals of $[0,1)$. This is the Lean `radixDiscrepancy`. Let $\|t\|$ denote the distance to the nearest integer, and let $K_b=\{z:D_N(z)\to1\}$ (Phase 19). For $t\ge0$ put

```math
F_z(t)=\#\{0\le n<N:\ \|b^nz\|>t\}.
```

Extreme discrepancy over intervals equals the supremum over half-open circle arcs. By complementation (`SharpTranslation.arc_le` and `interval_eq_arc_excess`) this gives the **concentration identity**

```math
1-D_N(z)=\inf_{J}\Bigl(\tfrac1N\#\{n<N:x_n\notin J\}+|J|\Bigr),
```

where $J$ runs over half-open arcs. [Geometry note](../phase19/geometry.md#finite-distance-including-its-zero-set)

**Lemma 0.** For every $\varepsilon\ge0$ and $N\ge1$:

```math
\text{(a)}\quad 1-D_N(z)\le 2\varepsilon+F_z(\varepsilon)/N;
```

```math
\text{(b)}\quad 1-D_N(z)\ge\min\Bigl\{\,1-\frac{F_z(\varepsilon)}N,\ \inf_{\ell\ge0}\Bigl(\ell+\frac{F_z(\ell+\varepsilon)}N\Bigr)\Bigr\}.
```

Part (a) is the Lean theorem `Phase18Synthetic.discrepancy_deficit_le`. For (b), the **separation lemma**, let $J$ be a half-open arc of length $\ell$. If $J$ misses the closed ball $\{\|t\|\le\varepsilon\}$, then each sample in $J$ has $\|x_n\|>\varepsilon$, so the cost of $J$ is at least $1-F_z(\varepsilon)/N$. Otherwise $J$ contains a point $y$ with $\|y\|\le\varepsilon$, and every $t\in J$ has $\|t\|<\|y\|+\ell\le\ell+\varepsilon$. The samples with $\|x_n\|>\ell+\varepsilon$ then lie outside $J$, so the cost is at least $\ell+F_z(\ell+\varepsilon)/N$. Take the infimum over $J$. $\square$

The script checks (b) and the symmetric-arc upper bound $1-D_N\le\inf_d\,(2d+F(d)/N)$ against the exact discrepancy at every reported cutoff.

## 1. The pentagonal expansion and the exact digits

By Euler's pentagonal number theorem, with $P_k^-=k(3k-1)/2$ and $P_k^+=k(3k+1)/2$,

```math
E_b=1+\sum_{k\ge1}(-1)^k\left(b^{-P_k^-}+b^{-P_k^+}\right).
```

The two members of the pair $k$ share the sign $(-1)^k$, and

```math
P_k^+-P_k^-=k,\qquad P_{k+1}^--P_k^+=2k+1 .
```

Thus the gaps alternate between $k$ inside a pair and $2k+1$ between pairs. The two signs of a pair agree, and they alternate from pair to pair. The script checks the identity through $q^{1500}$ and the gaps for $k\le 20000$. It also checks that $P(M)=\#\{1\le p<M\}$, the number of generalized pentagonal numbers below $M$, satisfies

```math
\frac{\sqrt{24M+1}}3-2\ \le\ P(M)\ \le\ \frac{\sqrt{24M+1}}3 .
```

Indeed $k(3k\mp1)/2<M$ is equivalent to $k<(\pm1+\sqrt{24M+1})/6$.

**Theorem 1 (digits).** For $j\ge1$ put $a_j=j(6j-1)=P_{2j}^-$. Then

```math
E_b=0.(b-2)(b-1)\,0\,0\,B_1B_2B_3\cdots,\qquad
B_j=1\,0^{2j}\,(b-1)^{4j}\,(b-2)\,(b-1)^{2j+1}\,0^{4j+2},
```

where block $B_j$ occupies positions $a_j,\ldots,a_{j+1}-1$ and has length $12j+5$.

*Proof.* Group the positive pair $2j$ with the negative pair $2j+1$. Let $a=P_{2j}^-$, $c=P_{2j}^+$, $d=P_{2j+1}^-$ and $e=P_{2j+1}^+$, so that $c-a=2j$, $d-c=4j+1$ and $e-d=2j+1$. For $1\le m<n$,

```math
1-b^{-m}-b^{-n}=\sum_{i=1}^{m-1}(b-1)b^{-i}+(b-2)b^{-m}+\sum_{i=m+1}^{n}(b-1)b^{-i},
```

since the first two terms sum to $1-2b^{-m}$ and the last to $b^{-m}-b^{-n}$. Hence $G_j=b^{-a}+b^{-c}(1-b^{-(d-c)}-b^{-(e-c)})$ has digit $1$ at $a$, zeros on $(a,c]$, $b-1$ on $(c,d)$, $b-2$ at $d$, $b-1$ on $(d,e]$, and zeros elsewhere. The head $1-b^{-1}-b^{-2}$ is the case $c=0$, $m=1$, $n=2$; its digits are $(b-2)(b-1)$. The digit supports are disjoint and every digit lies in $[0,b-1]$, so the sum has no carries. The expansion does not end in $(b-1)^\infty$, so it is the standard one. The block lengths follow from the gaps, and $a_{j+1}-a_j=12j+5$. $\square$

The script certifies $2^{20}+60$ digits in bases 2, 3 and 10 by exact integer arithmetic and compares them with the block formula. For example $E_{10}=0.8900100999989990000001000099999999899999\ldots$.

**Corollary 1 (missing words).** The interior maximal zero runs have lengths $2j$ and $4j+2$, plus the isolated zero at $P_{2j+1}^-$ when $b=2$. The maximal $(b-1)$-runs have lengths $4j$ and $2j+1$. Consequently:

- in base 2 every zero run has length 1 or even, so $1\,0^m\,1$ never occurs for odd $m\ge3$;
- for $b\ge3$ the word $11$ never occurs, and for $b\ge5$ the digits $2,\ldots,b-3$ never occur.

Hence $E_b$ is not disjunctive. In the first $2^{18}$ binary digits there are only 13, 45, 90 and 148 distinct words of lengths 4, 8, 12 and 16.

## 2. Word frequencies

Let $Z_w(N)$ be the number of starts $0\le n<N$ with $d_{n+1}\cdots d_{n+L}=w$.

**Theorem 2.** For $L,N\ge1$ and $w\in\{0^L,(b-1)^L\}$,

```math
\left|Z_w(N)-\frac N2\right|\le(2L+3)\sqrt{N/6}+3L^2+5L+7 .
```

Every other word $w$ of length $L$ has $Z_w(N)\le(4L-2)\sqrt{N/6}+2L^2+12L+4$. In particular every nonconstant word has frequency 0, with count $O_L(\sqrt N)$.

*Proof for $0^L$.* A valid start reads a window inside a single zero run, and runs never merge across blocks because each block begins with the digit 1. Block $j$ contributes $g_j=(2j-L+1)^++(4j+3-L)^+$ valid starts, plus one more when $b=2$ and $L=1$, among its $12j+5$ starts. Write $\Delta(N)=Z(N)-N/2$. For $j\ge(L-1)/2$ the block increment is $1.5-2L$ (or $2.5-2L$), at most $2L$ in absolute value. Each smaller block changes $\Delta$ by at most half its length, so these blocks contribute at most $\tfrac34L^2+\tfrac{11}4L$ in total. The first four digits contribute at most 2.

Inside a block, $\Delta$ first drops by $1/2$. It then rises over the first run to at most $J$, falls to $-2J-L-\tfrac12$, rises over the last run and ends at $1.5-2L$. Hence the excursion inside block $J$ is bounded by $2J+L+\tfrac12$. If $N$ lies in block $J$, then $6J^2-J-1\le N$, so $J\le\sqrt{N/6}+\tfrac12$. Collecting terms gives $|\Delta(N)|\le(2L+2)\sqrt{N/6}+0.75L^2+6.75L+5.5$, which is smaller than the stated bound.

The word $(b-1)^L$ is handled identically. Its block gain is $(4j-L+1)^++(2j+2-L)^+$, its increment is $0.5-2L$, and its excursion lies in $[-J-\tfrac12,2J+1]$.

Nonconstant words start at the remaining $(12j+5)-(12j+7-4L)=4L-2$ starts of each block with $j\ge L/2$, and at most $12j+5$ starts of each smaller block. $\square$

The script evaluates $\Delta$ at every breakpoint of this piecewise linear function. This checks the bound at **every** prefix $N\le2^{20}$ for $L\in\{1,2,3,4,6,8\}$ in bases 2, 3 and 10. The largest observed value of $|Z-N/2|/((L+1)\sqrt N)$ is $0.746$. At $N=2^{20}$ the binary frequencies of $0^L$ and $1^L$ are $0.50051/0.49949$ for $L=1$ and $0.49455/0.49353$ for $L=8$.

**Simple normality.** In base 2, $(b-1)^1=1$, so both binary digits have frequency $1/2$; the observed one-digit frequency at $2^{20}$ is $0.499491$. Yet $D_N(E_2;2)\to1$ (§3), so the number is simply normal and as far from normal as the numerical kernel allows. For $b\ge3$, the digits $1,\ldots,b-2$ occur only twice per block. Their frequency is $O(1/\sqrt N)$ ($0.000797$ at $2^{20}$), so $E_b$ is not simply normal.

## 3. The sharp discrepancy asymptotic

**Theorem 3.** For $b\ge2$ and $N\ge2$, $\ 1-D_N(E_b)=\sqrt{2/3}\,\log_b N/\sqrt N+O_b(1/\sqrt N)$.

*Upper bound.* $E_b-1$ is the Lean `sparseValue b m A` with $m$ enumerating the generalized pentagonal numbers $p\ge1$ and $|A_k|=1$. Integer translation does not change $D_N$ (`discrepancy_add_int`). Combine `discrepancy_deficit_le` with `sparse_farCount_le`, taking $B=1$ and $\varepsilon=2b^{-w}$. For every $w\ge1$ this gives the kernel-checked finite inequality

```math
1-D_N(E_b)\le 4b^{-w}+\frac{w\,P(N+w)}N,\qquad P(M)\le\frac{\sqrt{24M+1}}3 .
```

With $w=\lceil\log_b\sqrt N\rceil+1$, the first term is at most $2/\sqrt N$. The second is $\bigl(\tfrac12\log_bN+O(1)\bigr)\cdot2\sqrt{2/3}\,N^{-1/2}\bigl(1+O(\log N/N)\bigr)$.

*Lower bound.* Fix $n$. Let $p>n$ be the next generalized pentagonal number, $r=p-n$, $s=\pm1$ its sign, and $g$ the gap after $p$. All later exponents are distinct and at least $r+g$, so

```math
b^nE_b\equiv s\,b^{-r}+\theta\,\tfrac{b}{b-1}\,b^{-r-g}\pmod 1,\qquad|\theta|\le1 .
```

If $r,g\ge2$, then $b^{-r}(1+2b^{-g})\le3/8$, so $\|x_n\|\ge b^{-r}(1-2b^{-g})\ge b^{-r}/2$. Fix $t\in(0,1/8]$ and let $R$ be the largest integer with $b^{-R}/2>t$, so $R\ge\log_b(1/(2t))-1$. A pentagonal number $p\le N$ whose pair index is at least $R$ has both neighbouring gaps at least $R$; all but at most $2R$ of the $P(N+1)$ pentagonal numbers $p\le N$ qualify. For such $p$ the shifts $n=p-r$ with $2\le r\le R$ are distinct and lie in $[0,N)$. Hence

```math
F(t)\ \ge\ \bigl(P(N+1)-2R\bigr)\bigl(\log_b\tfrac1{2t}-2\bigr).
```

Apply Lemma 0(b) with $\varepsilon=1/N$. The upper-bound count with $w=\lceil\log_b2N\rceil$ gives $F(1/N)\le wP(N+w)=O(\sqrt N\log N)$, so the first branch is $1-o(1)$. In the second branch put $M=P(N+1)-2\log_bN=2\sqrt{2N/3}+O(\log N)$. Then

```math
\ell+\frac{F(\ell+1/N)}N\ \ge\ h(\ell)=\ell+\frac MN\Bigl(\log_b\frac1{2(\ell+1/N)}-2\Bigr).
```

The convex function $h$ is minimized at $\ell+1/N=M/(N\ln b)$, with value at least $\frac MN\bigl(\log_b\frac{N\ln b}{2M}-2\bigr)-\frac1N$. This equals $\sqrt{2/3}\,\log_bN/\sqrt N-O_b(1/\sqrt N)$. Arcs with $\ell+1/N>1/8$ cost at least $1/8-1/N$. $\square$

**Remarks.** (i) The optimal concentration arc has half-length $\delta\asymp1/\sqrt N$, precisely $\delta^*\approx\sqrt{2/3}/(\sqrt N\ln b)$. The choice $\delta=c/(\sqrt N\log N)$ also gives the leading term but adds a second-order loss of $(\log_b\log N)P(N)/N$. (ii) Both signs matter. Positive pairs place samples just above 0 and negative pairs just below 1, and asymmetric arcs are never better. (iii) The bounded second-order term $c_N=(1-D_N)N/P_N-\tfrac12\log_bN$ oscillates because only integer distances $r$ occur. The heuristic value for $b=2$ is $\log_2(2\ln2\sqrt{3/8})-1+1/\ln2\approx0.207$.

**Numerical check.** The table gives exact discrepancies from certified digits. The ratio column is $(1-D_N)/(\sqrt{2/3}\log_bN/\sqrt N)$.

| $b$ | $N$ | $1-D_N$ | ratio | $c_N$ | separation lower bound | symmetric arc | Lean bound |
|---|---|---|---|---|---|---|---|
| 2 | $2^{14}$ | 0.090607 | 1.0146 | 0.137 | 0.078369 | 0.090637 | 0.117188 |
| 2 | $2^{20}$ | 0.016247 | 1.0188 | 0.195 | 0.014666 | 0.016248 | 0.019483 |
| 3 | $2^{20}$ | 0.010456 | 1.0392 | 0.252 | 0.009327 | 0.010456 | 0.012984 |
| 10 | $2^{20}$ | 0.004976 | 1.0366 | 0.112 | 0.004186 | 0.004976 | 0.006774 |

For $N\ge2^{14}$ the ratio stays in $[0.957,1.044]$ and $|c_N|<0.26$.

**Corollary 4.** By `SharpTranslation.sharp_translation_isGreatest`, $\max_x|D_N(x+E_b)-D_N(x)|=1-D_N(E_b)$, attained at $x=0$. The same asymptotic holds, so adding $E_b$ to an arbitrary input changes its discrepancy by $\sim\sqrt{2/3}\log_bN/\sqrt N$ in the worst case.

## 4. Transcendence (established; no novelty claimed)

Nesterenko (1996) proved that for $0<|q|<1$ at least three of $q$, $P(q)$, $Q(q)$ and $R(q)$ are algebraically independent; here $P,Q,R$ are Ramanujan's normalized $E_2,E_4,E_6$. For algebraic $q=1/b$, the values $P,Q,R$ are therefore algebraically independent. Since $\Delta=(Q^3-R^2)/1728=q\prod_n(1-q^n)^{24}$, algebraicity of $E_b$ would make $Q(1/b)^3-R(1/b)^2=1728\,b^{-1}E_b^{24}$ algebraic, a nontrivial algebraic relation between $Q$ and $R$. Hence $E_b$ is transcendental, and so are $E_b^r$ for all $r\ge1$ and every nonconstant polynomial in $E_b$ with algebraic coefficients. This is a standard consequence of Nesterenko's theorem, used for theta values by Duverney, Ke. Nishioka, Ku. Nishioka and Shiokawa and by Bertrand. Irrationality also follows elementarily from Theorem 1, since the expansion is not eventually periodic. [Nesterenko, C. R. Acad. Sci. Paris **322** (1996), 909–914; Mat. Sb. **187** (1996)][nesterenko] · [Duverney–Nishioka–Nishioka–Shiokawa, Proc. Japan Acad. **72A** (1996), 202–203][dnns] · [Bertrand, Ramanujan J. **1** (1997), 339–350][bertrand]

## 5. The square of Euler's product

By Euler's identity $24P_k^\mp+1=(6k\mp1)^2$, one has $\eta(24\tau)=\sum_{m\ge1}\chi_{12}(m)q^{m^2}$. Here $\chi_{12}(m)=1$ for $m\equiv\pm1$ and $-1$ for $m\equiv\pm5\pmod{12}$, and the sign $(-1)^k$ equals $\chi_{12}(|6k-1|)$. Therefore

```math
E(q)^2=\sum_{n\ge0}a_2(n)q^n,\qquad
\eta(12\tau)^2=\sum_{n\ge0}a_2(n)q^{12n+1}=:\sum_{m\ge1}c(m)q^m,
```

```math
c(m)=\sum_{\substack{m_1,m_2\ge1\\ m_1^2+m_2^2=2m}}\chi_{12}(m_1)\chi_{12}(m_2).
```

In particular $24n+2=m_1^2+m_2^2$ and $12n+1=u^2+v^2$ with $u=(m_1+m_2)/2$ and $v=(m_1-m_2)/2$.

**Proposition 5 (elementary).** If $a_2(n)\ne0$ then $12n+1$ is a sum of two squares. The trivial pair count gives $A_2(X)=\sum_{n\le X}|a_2(n)|\le(P(X+1)+1)^2\le(2\sqrt{2X/3}+2)^2$. Landau's bound for sums of two squares (a Halberstam–Richert bound for a multiplicative indicator) gives $S_2(X)=\#\{n\le X:a_2(n)\ne0\}\ll X/\sqrt{\log X}$. By the coefficient-transfer lemma (Lemma 1 in the [theta note](theta-and-modular.md#1-coefficient-transfer)), $1-D_N(E_b^2)=O_b(\log\log N/\sqrt{\log N})$.

**Cited input.** $\eta(12\tau)^2\in S_1(144,\chi_{-4})$ is a normalized Hecke eigenform of CM type. Serre (1985, §2) writes $\eta(12z)^{2k}$, $k\in\{1,2,3,4,5,7,13\}$, as combinations of CM forms attached to Hecke characters of $\mathbb Q(\sqrt{-1})$ and $\mathbb Q(\sqrt{-3})$; for $k=1$ the form is a single eigenform with CM by both fields. Martin (1996) lists the multiplicative η-quotients. Its projective Galois image is therefore the Klein four group $D_2$. In the notation of Serre (1981, Théorème 18), the proportion of involutions in the projective image is $\lambda=3/4$, the most lacunary weight-one type.

**Theorem 6.** Granting this input:

(a) $c$ is multiplicative. One has $|c(p)|=2$ for $p\equiv1\pmod{12}$ and $c(p)=0$ for all other primes $p\ge5$, with $c(2^e)=c(3^e)=0$. Moreover $c(p^e)=(e+1)\epsilon_p^e$ ($\epsilon_p=\pm1$) for $p\equiv1\pmod{12}$, and otherwise $c(p^{2e+1})=0$ and $c(p^{2e})=(-\chi_{-4}(p))^e$. Hence **$a_2(n)\ne0$ if and only if every prime $p\not\equiv1\pmod{12}$ divides $12n+1$ to an even power**, and then $|a_2(n)|=\prod_{p\equiv1\,(12)}(v_p(12n+1)+1)$.

(b) $S_2(X)\asymp X/(\log X)^{3/4}$ and $A_2(X)\asymp X/(\log X)^{1/2}$.

(c) $1-D_N(E_b^2;b)\asymp_b\log\log N/(\log N)^{3/4}$.

The script verifies (a) for every $n\le2^{17}$ with no exception. It also checks the Hecke relations at $p^2$ and $p^3$ for all 202 primes $5\le p\le1254$ and multiplicativity on 54,486 coprime pairs. Cancellation does occur on representable indices: $85=2^2+9^2=6^2+7^2$ but $a_2(7)=0$, and $145=1^2+12^2$ but $a_2(12)=0$, because $5$ and $29$ are $\equiv5\pmod{12}$ and occur to odd powers. Through $2^{17}$ there are 44,855 nonzero coefficients but 71,329 indices with $12n+1$ a sum of two squares. The brief's bound $S(X)=O(X/\sqrt{\log X})$ is thus true but not sharp; the support exponent is $3/4$.

*Proof.* (a) A Hecke eigenform of weight one has $c(p)=\operatorname{tr}\rho(\mathrm{Frob}_p)$ for an odd representation with projective image $V_4$. The three nontrivial elements of $V_4$ lift to trace-zero matrices. Frobenius is central exactly when $p$ splits completely in $\mathbb Q(i,\sqrt3)$, that is, $p\equiv1\pmod{12}$, and then $c(p)=\pm2$. The prime-power values follow from $c(p^{e+1})=c(p)c(p^e)-\chi_{-4}(p)c(p^{e-1})$. The support of $c$ is automatically $\equiv1\pmod{12}$, since $p^2\equiv1\pmod{24}$ for $p\nmid6$.

(b) The support indicator is multiplicative with value 1 exactly at primes $\equiv1\pmod{12}$ (prime density $1/4$) and at all $p^2$ with $p\ge5$. Wirsing's theorem gives $\asymp x/(\log x)^{3/4}$, and $n\mapsto12n+1$ is affine. For $|c|$ one has $\sum_{p\le x}|c(p)|/p=\tfrac12\log\log x+O(1)$ and $|c(p^e)|\le e+1$, so Wirsing and Shiu give $\asymp x/(\log x)^{1/2}$.

(c) *Upper bound.* Apply the coefficient-transfer corollary with $\kappa=3/4$ and $\beta=0$.

*Lower bound* (paper proof using the Phase 17 inputs). Fix $J=\lceil C\log_b\log N\rceil$ and call $n\le N$ *good* if

- $a_2(n)\ne0$;
- $a_2(n+h)=0$ for $0<|h|\le J$;
- $|a_2(n)|\le(\log N)^{1/3}$;
- the tail $\tau_n=\sum_{h>J}|a_2(n+h)|b^{-h}\le1/4$.

The support count is $\gg N/(\log N)^{3/4}$ by (b). For fixed $h$, an upper-bound sieve gives $\#\{n\le N:a_2(n)a_2(n+h)\ne0\}\ll_h N(\log N)^{-3/2}(\log\log N)^{3/2}$. It sifts both $12n+1$ and $12n+12h+1$ by the primes $\not\equiv1\pmod{12}$ in $((\log N)^2,N^{c}]$, with dimension $2\cdot\tfrac34$, after discarding the $O(N/(\log N)^2)$ indices divisible by $p^2$ for such $p$. This is the sieve of [Phase 17, §4](../phase17/multiplicative-lambert.md#4-planting-and-isolating-a-coefficient), and its dependence on $h\le J$ is polynomial. Summing over $|h|\le J$ removes $o(N/(\log N)^{3/4})$ indices. Markov's inequality with (b) removes $\ll A_2(N)/(\log N)^{1/3}=o(N/(\log N)^{3/4})$ indices of large coefficient and $\ll b^{-J}A_2^*(N)=o(N/(\log N)^{3/4})$ indices of large tail. Hence there are $G\gg N/(\log N)^{3/4}$ good $n$. At a good $n$ and for $r\le J$,

```math
\{b^{n-r}E_b^2\}\equiv b^{-r}\bigl(a_2(n)+\theta\tau_n\bigr),\qquad|\theta|\le1,
```

so $\|x_{n-r}\|\ge b^{-r}/2$ whenever $\log_b(4(\log N)^{1/3})\le r\le\log_b(1/(2t))$. The neighbourhoods $\{n-r:r\le J\}$ of distinct good $n$ are disjoint, so $F(t)\ge G\,(\log_b(1/t)-\tfrac13\log_b\log N-O(1))$. The bulk satisfies $F(1/\log N)/N=o(1)$ by the upper-bound argument. Lemma 0(b) with $\varepsilon=1/\log N$, optimized at $\ell\asymp G/N$, gives $1-D_N\gg(G/N)\bigl(\tfrac34-\tfrac13\bigr)\log_b\log N\gg\log\log N/(\log N)^{3/4}$. $\square$

**Numerical record.** For $X\in[2^{12},2^{20}]$, $S_2(X)(\log X)^{3/4}/X$ increases from $2.107$ to $2.206$, and $A_2(X)(\log X)^{1/2}/X$ from $2.889$ to $3.037$. At $N=2^{20}$ in base 2, $1-D_N=0.78861$. The ratio $(1-D_N)/(\log\log N/(\log N)^{3/4})$ stays within $2.11$–$2.16$ for $N\in[2^{10},2^{20}]$ in base 2 and within $1.98$–$2.03$ in base 3. The exponent-$\tfrac12$ normalization drifts down by about 14% over the same range. The finite transfer inequality is valid but still vacuous at these cutoffs; its value is $1.82$ at $2^{20}$. About 11% of the support below $2^{20}$ is isolated at distance 3.

## 6. The cube of Euler's product

Jacobi's identity $E(q)^3=\sum_{k\ge0}(-1)^k(2k+1)q^{T_k}$, $T_k=k(k+1)/2$, is checked through $q^{20000}$.

**Theorem 7.** For every $b\ge2$:

(a) *Digits.* For $j\ge2$ the positions $(T_{2j-1},T_{2j+1}]$ read the $2j$-digit zero-padded expansion of $4j$, followed by the $(2j+1)$-digit expansion of $b^{2j+1}-4j-3$. The latter is $(b-1)^{2j+1-w'}$ followed by the last $w'$ digits of $b^{w'}-1-(4j+2)$, where $w'$ is the length of $4j+2$. Digits beyond position 6 are determined by these blocks.

(b) *Frequencies.* $Z_w(N)=N/2+O((L+\log N)\sqrt N)$ for $w\in\{0^L,(b-1)^L\}$, and every other word has frequency 0. In base 2, $E_2^3$ is simply normal. For $b\ge3$, the digits $1,\ldots,b-2$ occur only in the $O(\log j)$ "junk" digits per block, so $E_b^3$ is not simply normal.

(c) *Disjunctivity.* $E_b^3$ contains every finite word infinitely often.

(d) *Sharp asymptotic.* $1-D_N(E_b^3)=\sqrt2\,\log_bN/\sqrt N+O_b(1/\sqrt N)$.

*Proof.* (a) $(4j+1)b^{-T_{2j}}-(4j+3)b^{-T_{2j+1}}=4j\,b^{-T_{2j}}+(b^{2j+1}-4j-3)b^{-T_{2j+1}}$, and the left side is less than $b^{-T_{2j-1}}$ because $4j+1<b^{2j}$ for $j\ge2$. The terms with $j\le1$ sum to a nonnegative multiple of $b^{-6}$. The script verifies all 722 blocks within $2^{20}+60$ certified digits in bases 2 and 3.

(b) Per block, the zero run has length $2j-O(\log j)$, the $(b-1)$-run has length $2j+1-O(\log j)$, and the junk has length $O(\log j)$. The proof of Theorem 2 applies with an extra $O(\log j)$ per block. The script checks $|Z-N/2|\le2(L+\log_b(N+1)+2)\sqrt{2N+1}+4L^2+20$ at every prefix $N\le2^{20}$. The largest observed value of $|Z-N/2|/((L+\log_bN)\sqrt N)$ is $0.494$.

(c) Given a word $w$, let $W$ be the integer with digits $1w$. For $b^t\ge4$ the interval $[Wb^t,(W+1)b^t)$ contains a multiple $4j$ of 4, whose expansion begins with $1w$, and (a) places it verbatim in the expansion. Letting $t\to\infty$ gives infinitely many occurrences. Every binary word of length at most 10 already occurs in the first $2^{20}$ digits of $E_2^3$ (in contrast to $E_2$, whose first $2^{20}$ digits contain only 90 distinct words of length 12).

(d) *Upper bound.* For $n\in[T_{k-1},T_k)$ let $r=T_k-n\in[1,k]$. Then $|b^nE_b^3-(\text{integer})|\le(2k+1)b^{-r}\bigl(1+\sum_{i\ge1}(1+i)b^{-i(k+1)}\bigr)\le2(2k+1)b^{-r}$, so

```math
F(\varepsilon)\le\sum_{k:\,T_k-\min(R_k,k)<N}\min(R_k,k),\qquad R_k=\Bigl\lceil\log_b\frac{2(2k+1)}\varepsilon\Bigr\rceil .
```

With $\varepsilon=1/\sqrt N$ there are $\sqrt{2N}+O(\log N)$ such $k$, each with $R_k=\log_bN+O(1)$. Lemma 0(a) gives $1-D_N\le\sqrt2\log_bN/\sqrt N+O(1/\sqrt N)$.

*Lower bound.* Let $w_k$ be the length of $2k+1$. For $w_k+2\le r\le k$ one has $\|x_{T_k-r}\|\ge(2k+1)b^{-r}/2$. For $r\le w_k+1$ the sample lies within $\eta_k=4(2k+1)b^{-k-2}$ of $\pm(2k+1)/b^r\bmod1$. These shifts are far from 0 unless $(2k+1)\bmod b^r$ falls in a set of at most $2\tau b^r+2$ residues, where $\tau=t+\eta_k$. As $k$ runs over $K$ consecutive integers, each residue class modulo $b^r$ contains at most $K/b^r+1$ of the odd numbers $2k+1$. Summing over $r\le w_K+1$ bounds the number of exceptional pairs $(k,r)$ by $O(K(1+t\log K))$. For odd $b$ this count includes the exact zeros $b^r\mid2k+1$, on average $1/(b-1)$ per $k$. With $K'=\max\{k:T_k\le N\}=\sqrt{2N}+O(1)$ and $\sum_{k\le K'}\log_b(2k+1)=K'\log_b(2K')-K'/\ln b+O(\log K')$, this gives

```math
F(t)\ \ge\ K'\Bigl(\log_b(2K')+\log_b\tfrac1t-C\Bigr)-O\bigl(K'(t\log K'+1)\bigr).
```

Lemma 0(b) with $\varepsilon=1/N$ gives $1-D_N\ge\min_\ell\bigl(\ell/2+\frac{K'}N(\log_b(2K')+\log_b\frac1{\ell+1/N}-C)\bigr)-\frac1N$. The negative $t\log K'$ term is absorbed by $\ell/2$. The minimum, at $\ell\asymp K'/N$, is $\frac{K'}N(\log_bN-O(1))$. $\square$

The leading constant is $\sqrt2=C(1-\sigma+\gamma)$ with $C=\sqrt2$ (insertions $T_k\le N$ number $\sim\sqrt{2N}$), $\sigma=1/2$, and $\gamma=1/2$ (coefficient size $2k+1\approx N^{1/2}$). The shifts that see the digits of $2k+1$ themselves account for the $\gamma$ part: they are spread around the circle rather than near 0, so each counts as a full far position. The heuristic centre of $c_N=(1-D_N)N/K_N-\log_bN$ is $\log_b(4\ln b)-\tfrac12-[b\text{ odd}]/(b-1)$, which is $0.971$ for $b=2$ and $0.347$ for $b=3$.

| $b$ | $N$ | $1-D_N$ | ratio to $\sqrt2\log_bN/\sqrt N$ | $c_N$ | separation lower | symmetric arc | paper upper |
|---|---|---|---|---|---|---|---|
| 2 | $2^{14}$ | 0.162018 | 1.0474 | 0.747 | 0.151123 | 0.162170 | 0.183228 |
| 2 | $2^{20}$ | 0.028902 | 1.0463 | 0.944 | 0.027529 | 0.028904 | 0.031646 |
| 3 | $2^{14}$ | 0.099629 | 1.0209 | 0.235 | 0.093468 | 0.099677 | 0.122061 |
| 3 | $2^{20}$ | 0.017749 | 1.0185 | 0.243 | 0.016976 | 0.017749 | 0.020793 |

Thus $E_b^3$ has $\sqrt3$ times the deficit of $E_b$ asymptotically. It has fewer insertions ($\sqrt{2N}$ against $2\sqrt{2N/3}$), but each one spoils about $\log_bN$ shifts instead of $\tfrac12\log_bN$.

## 7. Polynomials and rational scalars

**Theorem 8.** (a) If $P\in\mathbb Z[1/b][x]$ has degree at most 3, then $P(E_b)\in K_b$. Writing $P=b^{-j}Q$ with $Q=\sum q_ix^i\in\mathbb Z[x]$,

```math
1-D_N(P(E_b))\le\sum_{i=1}^3|q_i|\bigl(1-D_N(E_b^i)\bigr)+\frac jN .
```

The rate is therefore $O(\log\log N/(\log N)^{3/4})$ when $q_2\ne0$ and $O(\log N/\sqrt N)$ otherwise.

(b) For reduced $a/d$, $(a/d)E_b\in K_b$ if and only if $a/d\in\mathbb Z[1/b]$.

(c) The limiting laws are $\{2^nE_2/3\}\Rightarrow\frac16\delta_0+\frac5{12}(\delta_{1/3}+\delta_{2/3})$, so $D_N(\tfrac13E_2;2)\to\tfrac12$, and $\{3^nE_3/2\}\Rightarrow\frac13\delta_0+\frac23\delta_{1/2}$, so $D_N(\tfrac12E_3;3)\to\tfrac23$.

*Proof.* (a) $d_N(x,y)=1-D_N(x-y)$ is a pseudometric (Phase 19), so $d_N(mx,0)\le|m|\,d_N(x,0)$ and deficits add. Integer constants do not matter, and $|D_N(b^{-j}y)-D_N(y)|\le j/N$. Use Theorems 3, 6 and 7.

(b) By Phase 19, $(a/d)z\in K_b$ iff $z/d_0\in K_b$, where $d_0$ is the part of $d$ coprime to $b$. For $z=E_b$ the limiting fixed point is 0. Let $k_n$ be the nearest integer to $b^nE_b$, and let $I_n=\sum_{p\le n}s_pb^{n-p}$ be the integral head. Away from the $O(\sqrt N)$ shifts at distance at most 1 before an insertion, $k_n=I_n$. Inside a run, $I_{n+1}=bI_n$, and across an insertion, $I_p=bI_{p-1}+s_p$.

By the Phase 19 test, $E_b/d_0\in K_b$ iff some residue $r\bmod d_0$ carries density one among the $k_n$ and $(b-1)r\equiv0\pmod{d_0}$. Multiplication by $b$ permutes $\mathbb Z/d_0$, so a long run either stays in a fixed residue $r$ or meets $r$ in at most half of its positions. Two adjacent long runs cannot both stay in $r$: if $I_{p-2}\equiv I_{p-1}\equiv r$, then $I_p\equiv r+s_p\not\equiv r$, since $s_p=\pm1$ and $d_0>1$. The runs alternate in length between $k$ (after $P_k^-$) and $2k+1$ (after $P_k^+$), with total weights $1/3$ and $2/3$. A set of pairwise nonadjacent runs therefore has density at most $2/3$, so no residue carries density one.

(c) For $b=2$, $d=3$: $k_n\equiv(-1)^n\Sigma(n)\pmod 3$ with $\Sigma(n)=\sum_{p\le n}s_p(-1)^p$. The parities of $P_k^\mp$ have period 4 in $k$. Starting from $\Sigma=1$ at $p=0$, $\Sigma$ equals $2,0,-2,0$ after $P_k^-$ for $k\equiv1,2,3,0\pmod4$, and $1,-1,-1,1$ after $P_k^+$. Thus $k_n\equiv0$ exactly on the runs after $P_k^-$ with $k$ even (weight $1/6$), and $k_n$ alternates between the two nonzero residues elsewhere. The law of a three-point measure gives $D\to\max(5/12,\,10/12-1/3,\ldots)=1/2$. For $b=3$, $d=2$: $k_n\equiv\#\{p\le n\}\pmod2$, which is even after $P_k^-$ and odd after $P_k^+$, giving weights $1/3$ and $2/3$ on the two fixed points $0$ and $1/2$ and $D\to2/3$. $\square$

At $N=2^{16},2^{18},2^{20}$, $D_N(\tfrac13E_2;2)=0.4819$, $0.4893$, $0.4941$, and the masses within $0.01$ of $0,\tfrac13,\tfrac23$ are $0.1649$, $0.4136$, $0.4136$. Also $D_N(\tfrac12E_3;3)=0.6497$, $0.6572$, $0.6613$, with masses $0.3311$ and $0.6641$.

The same argument (sketched here) shows $E_b^3/d\notin K_b$ for $d>1$ coprime to $b$. Adjacent stable runs across $T_k$ require $d\mid2k+1$, which happens for at most a $1/d$ proportion of $k$, while consecutive runs have comparable lengths. For $E_b^2/d$ the coefficients are not sparse, and the residue test remains open.

Positive controls with $\mathbb Z[1/2]$ coefficients behave as predicted. For $P=\tfrac58+3x-2x^3$, $1-D_N(8P(E_2))=0.2296$, $0.1359$, $0.0780$ at $N=2^{14},2^{16},2^{18}$. For $P=3-5x+\tfrac14x^2-7x^3$ the values are $0.9066$, $0.8609$, $0.8247$, since the slow $E_2^2$ rate dominates.

## 8. Track B5: sparse quadratic polynomials

Call $F=\sum_{t\in T}\epsilon(t)b^{-f(t)}$ a *unary quadratic series* if $T\subseteq\mathbb Z$, the integers satisfy $|\epsilon(t)|\le B$, and $f(t)=(\alpha t^2+\beta t+\gamma)/\delta$ is a positive integer for $t\in T$, with integers $\alpha>0$ and $\delta\ge1$. Each value $m$ has at most two preimages, so $F=\sum_ma(m)b^{-m}$ with $|a(m)|\le2B$ and $S(X)\le2\sqrt{\delta X/\alpha}+2$. Examples are

- $E_b-1$ ($f=(3t^2-t)/2$);
- $\Theta_3(1/b)=\sum_{t\in\mathbb Z}b^{-t^2}$;
- $\sum_{t\ge0}b^{-t(t+1)}$, the $\Theta_2$-type series;
- Rogers' false theta series $\sum_{t\ge0}(-1)^tb^{-t(t+1)/2}$.

The Rogers–Ramanujan functions $G$ and $H$ are not of this kind, since they have positive partition-type coefficients. Neither is $E_b^3$, whose coefficients are unbounded.

**Theorem 9.** For unary quadratic series $F_1,\ldots,F_s$, every polynomial of total degree at most 2 in them with coefficients in $\mathbb Z[1/b]$ lies in $K_b$, with $1-D_N=O(\log\log N/\sqrt{\log N})$.

*Proof.* Linear terms have $S(X)=O(\sqrt X)$ and bounded coefficients, so the rate is $O(\log N/\sqrt N)$. For a product $F_iF_j$ the coefficient of $b^{-m}$ is $\sum_{f_i(t)+f_j(u)=m}\epsilon_i(t)\epsilon_j(u)$. With $D=\delta_i\delta_j$,

```math
Dm=\delta_j(\alpha_it^2+\beta_it+\gamma_i)+\delta_i(\alpha_ju^2+\beta_ju+\gamma_j)=:g(t,u),
```

an integral binary quadratic polynomial whose quadratic part $\delta_j\alpha_it^2+\delta_i\alpha_ju^2$ is positive definite. By the shifted-lattice reduction of the [theta note](theta-and-modular.md#22-extensions), the support has counting function at most that of the integers $\le DX$ represented by $g$, which is $\ll X/\sqrt{\log X}$. The coefficient sum satisfies $A(X)\le B^2\#\{(t,u):g(t,u)\le DX\}=O(X)$ by the area of an ellipse. The coefficient-transfer corollary with $\kappa=1/2$ and $\beta=0$ gives the rate, and Theorem 8(a) handles the $\mathbb Z[1/b]$-linear combinations. $\square$

For $\Theta_3(1/2)E_2$ the script confirms that every supported $m\le2^{18}$ has $24m+1=t^2+24k^2$ with $\gcd(t,6)=1$. It also records $S(X)\sqrt{\log X}/X=1.2043$, $A(X)/X=0.9708$ and $1-D_{2^{18}}=0.8227$.

**Why degree 3 fails in general.** A product of three unary quadratic series is supported on values of a ternary quadratic polynomial, typically a set of positive density. For $\Theta_3(1/b)^3=\sum r_3(n)b^{-n}$, Legendre's theorem gives support $\{n\ne4^a(8k+7)\}$ of density $5/6$; the script verifies it for $n\le2^{14}$ ($0.8334$). The coefficients have size $n^{1/2\pm\epsilon}$, so the transfer lemma has nothing to work with, and numerically $D_{2^{14}}(\Theta_3(1/2)^3)=0.012$ shows no concentration. $E_b^3$ is the exception: Jacobi's identity collapses the triple convolution of pentagonal series onto the triangular numbers. Positive density of the generic support is the obstruction; the cubic degree alone is not.

## 9. Lean status and recommended statements

**Already kernel-checked.** The Phase 18 declarations `discrepancy_deficit_le`, `sparse_farCount_le` and `sharp_translation_isGreatest` give the finite upper bound of Theorem 3 and Corollary 4. In this worktree the companion module [`EulerPentagonal.lean`](../../NormalityChecker/EulerPentagonal.lean), from the Track A Lean work, proves `eulerPentagonal_discrepancy_tendsto_one`, `eulerCube_discrepancy_tendsto_one` and the finite bound `eulerPentagonal_finite_gap_upper` through the Track B1 transfer `CoefficientTransfer.finite_sparse_mass_transfer`. [`CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean) also contains `one_sub_discrepancy_ge_of_bulk_and_far`:

```math
\min\Bigl(\delta-\varepsilon_0,\ \frac{F(\delta)}N,\ \frac{\#\text{bulk}}N\Bigr)\le1-D_N .
```

Taking $\delta\approx\sqrt{2/3}\log_bN/\sqrt N$ there already gives the **leading** constant of Theorem 3, with relative error $O(\log\log N/\log N)$. The $O(1/\sqrt N)$ error term needs the sharper Lemma 0(b), with its optimization over the arc length $\ell$.

**Recommended additions** (names follow the existing modules):

```lean
namespace NormalityChecker.EulerPentagonal
open CoefficientTransfer Phase18Synthetic

/-- Gaps: `k` inside the pair, `2k+1` between pairs. -/
theorem pentPlus_sub_pentMinus (k : ℕ) : pentPlus k - pentMinus k = k
theorem pentMinus_succ_sub_pentPlus (k : ℕ) : pentMinus (k+1) - pentPlus k = 2*k + 1

/-- Two-sided pentagonal count: `#{1 ≤ p < M}` lies in `[√(24M+1)/3 - 2, √(24M+1)/3]`. -/
theorem pentagonal_supportCount_ge (M : ℕ) :
    Nat.sqrt (24*M+1) / 3 ≤ supportCount pentCoeff M + 2

/-- Theorem 1: the digit at position `j(6j-1)+i`, `0 ≤ i < 12j+5`, of `E_b`. -/
theorem euler_digit_block {b : ℕ} (hb : 2 ≤ b) {j i : ℕ} (hj : 1 ≤ j) (hi : i < 12*j+5) :
    Int.toNat (⌊(b : ℝ) ^ (j*(6*j-1) + i) * eulerPentagonalSum b⌋ % b) =
      if i = 0 then 1 else if i ≤ 2*j then 0 else if i ≤ 6*j then b-1
      else if i = 6*j+1 then b-2 else if i ≤ 8*j+2 then b-1 else 0

/-- Lemma 0(b), the sharp separation lemma, for each fixed arc length `l`. -/
theorem deficit_ge_of_separation (b : ℕ) (x : ℝ) {N : ℕ} (hN : 0 < N) {ε c : ℝ} (hε : 0 ≤ ε)
    (hbulk : c ≤ 1 - (farCount b x ε N : ℝ) / N)
    (harc : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → c ≤ l + (farCount b x (l + ε) N : ℝ) / N) :
    c ≤ 1 - radixDiscrepancy b x N

/-- Local size `‖b^n E_b‖ ≥ b^{-r}/2` at distance `r ≥ 2` before an insertion whose
following gap is at least two. -/
theorem euler_shift_far {b : ℕ} (hb : 2 ≤ b) {n r : ℕ} (hr : 2 ≤ r)
    (hins : pentCoeff (n + r) ≠ 0) (hfree : ∀ i, 0 < i → i < r → pentCoeff (n + i) = 0)
    (hgap : pentCoeff (n + r + 1) = 0) :
    ¬ Near ((b : ℝ) ^ n * eulerPentagonalSum b) (((b : ℝ)⁻¹) ^ r / 2 - 1e-300)

/-- The count `F(t) ≥ (P(N+1) - 2R)(R - 1)` used in the lower bound. -/
theorem euler_farCount_ge {b : ℕ} (hb : 2 ≤ b) (N R : ℕ) {t : ℝ} (ht : 2 * t * (b : ℝ) ^ R < 1) :
    (((supportCount pentCoeff N - 2*R) * (R - 1) : ℕ) : ℝ) ≤ farCount b (eulerPentagonalSum b) t N

theorem euler_deficit_asymp {b : ℕ} (hb : 2 ≤ b) :
    (fun N : ℕ => 1 - radixDiscrepancy b (eulerPentagonalSum b) N
        - Real.sqrt (2/3) * Real.logb b N / Real.sqrt N) =O[Filter.atTop]
      (fun N : ℕ => 1 / Real.sqrt N)

/-- Theorem 8(b) for `E_b`: no off-radix denominator. -/
theorem euler_div_not_mem {b d : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d) (hcop : Nat.Coprime d b) :
    ¬ Tendsto (fun N => radixDiscrepancy b (eulerPentagonalSum b / d) N) atTop (𝓝 1)
```

The cube needs the analogue `eulerCube_shift_far`, with weight $2(2k+1)$ in place of $2$. Its lower bound uses a residue-counting lemma: among $K$ consecutive odd integers, at most $K/b^r+1$ lie in each class modulo $b^r$. In `euler_shift_far` the constant `1e-300` is a placeholder for any strict slack; the clean form states `b^{-r}/2 < ‖b^n E_b‖` with a distance-to-integer function. Theorem 8(b) is purely finite once stated with the run structure. It needs `I_{n+1} = b I_n` inside a run and `I_p = b I_{p-1} ± 1` at an insertion.

## 10. Verification record and open problems

```sh
python -B scripts/phase20_euler_theta.py
```

The run certifies about $2^{20}$ digits for each example by exact integer arithmetic. It checks 534,917 assertions in about 170 s and exits 0. Every discrepancy is computed exactly from sorted samples with error below $10^{-12}$. The rational-scalar limits use exact floors of $b^KE_b/d$.

Open problems:

1. Exact second-order terms $c_N$ for $E_b$ and $E_b^3$, which oscillate with $\{\log_b N\}$.
2. Whether $E_b^2$ is disjunctive. The Phase 17 planting argument applies to its multiplicative coefficients with values $\pm2(2u+1)$, but the sign of $c(p)$ on primes $\equiv1\pmod{12}$ must be controlled.
3. The residue test for $E_b^2/d$.
4. Whether $\Theta_3(1/b)^3$ and $E_b^r$ for $r\ge4$ are normal. Both look equidistributed at accessible scales; see the [theta note](theta-and-modular.md#4-serres-lacunary-eta-powers-and-the-failure-at-weight-two).

[nesterenko]: https://doi.org/10.1070/SM1996v187n09ABEH000158
[dnns]: https://projecteuclid.org/journals/proceedings-of-the-japan-academy-series-a-mathematical-sciences/volume-72/issue-9/Transcendence-of-Jacobis-theta-series/10.3792/pjaa.72.202.full
[bertrand]: https://doi.org/10.1023/a:1009749608672
