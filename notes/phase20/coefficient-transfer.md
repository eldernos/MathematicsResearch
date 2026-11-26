# Coefficient transfer, displaced sources and isolated-source constants

**Theorem (paper proof).** Let $b\ge2$ be an integer and let $a(m)\in\mathbb Z$ $(m\ge1)$ satisfy $\sum_m|a(m)|b^{-m}<\infty$. Put $F=\sum_{m\ge1}a(m)b^{-m}$, $S(X)=\#\{1\le m\le X:a(m)\ne0\}$ and $A(X)=\sum_{m\le X}|a(m)|$. If $A(X)\le CX$ for all $X\ge1$, then for **every** $N\ge1$, with $\rho_N=(1+S(N-1))/N$,

```math
1-D_N(F;b)\;\le\;\rho_N\Bigl(2\log_b\frac1{\rho_N}+\log_b^+\frac{4C}{b-1}+3\Bigr).
```

Consequently $A(X)=O(X)$ and $S(X)=o(X)$ imply $F\in K_b$. The left side equals $\sup_x|D_N(x+F;b)-D_N(x;b)|$, so the same bound controls the worst change of discrepancy under translation by $F$. The constant $2$ cannot be lowered. When the normalized coefficients have bounded mean (after removing powers of $b$, Section 2) the constant becomes $1$. For isolated sources this constant is attained, and it gives the exact leading terms in Section 3. Here $D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $0\le n<N$, over half-open subintervals of $[0,1]$; $K_b=\{z:D_N(z;b)\to1\}$ is the numerical translation kernel of [Phase 19](../phase19/geometry.md).

Section 1 proves the finite transfer inequality (B1). Section 2 removes radix powers from coefficients and gives the counterexamples (B2). Section 3 computes leading constants for isolated, growing-width and clustered sources (B3). Section 4 lists the finite statements recommended for Lean. Section 5 records the exact checks in [`scripts/phase20_transfer.py`](../../scripts/phase20_transfer.py). The multiplicative Lambert application (B4) is in [lambert-leading-constant.md](lambert-leading-constant.md).

## 0. Conventions

Write $x_n=\{b^nF\}$ and let $\|y\|$ be the distance from $y$ to the nearest integer. For $\varepsilon\ge0$ let

```math
E_N(\varepsilon)=\#\{0\le n<N:\ \|b^nF\|>\varepsilon\}.
```

Two finite facts from the Lean library are used throughout.

- **Deficit bound.** For every $\varepsilon\ge0$, $1-D_N(F)\le2\varepsilon+E_N(\varepsilon)/N$. [Lean `discrepancy_deficit_le`](../../NormalityChecker/Phase18Synthetic.lean)
- **Sharp translation.** $\sup_x|D_N(x+F)-D_N(x)|=1-D_N(F)$, attained at $x=0$. [Lean `sharp_translation_isGreatest`](../../NormalityChecker/SharpTranslation.lean)

The concentration form $1-D_N=\inf_I\,(1-\mu_N(I)+|I|)$ over half-open circle arcs $I$, with $\mu_N$ the empirical law, follows from the Lean lemmas `arc_le` and `interval_eq_arc_excess`. All logarithms are natural unless a base is shown, and $\log_b^+y=\max(0,\log_by)$.

## 1. Finite transfer (B1)

### 1.1 Integral head, shadows and the exact mean tail

**Lemma 1.1 (integral terms drop out).** Fix $n\ge0$. Let $I$ be any set of indices $m>n$ for which $b^{m-n}\mid a(m)$. Then

```math
\|b^nF\|\le\sum_{m>n,\ m\notin I}|a(m)|\,b^{n-m}.
```

*Proof.* Every term with $m\le n$ or $m\in I$ contributes an integer to $b^nF$. A summable family of integers has only finitely many nonzero terms, so its sum is an integer. ∎

With $I=\emptyset$ and a window $a(n+1)=\dots=a(n+L)=0$ this gives $\|b^nF\|\le\tau_L(n)$, where

```math
\tau_L(n)=\sum_{j>L}|a(n+j)|\,b^{-j}.
```

**Lemma 1.2 (shadow count).** Let $W_L(N)$ be the number of $0\le n<N$ whose next occupied index lies in $(n,n+L]$. Then

```math
W_L(N)\le L+\sum_{m<N,\ a(m)\ne0}\min(L,\,m-m^-)\le L\,(1+S(N-1)),
```

where $m^-$ is the previous occupied index, or $0$ if none exists.

*Proof.* The shifts whose next occupied index is $m$ form the interval $[\max(m-L,m^-),m-1]$. For $m\ge N$ these intervals meet $[0,N)$ inside $[N-L,N-1]$, giving at most $L$ shifts in total. ∎

So $S(N+L)$ and $S(2N)$ are not needed. Occupied indices beyond $N-1$ shadow at most $L$ shifts, which is the "$1+$" in $\rho_N$.

**Lemma 1.3 (exact mean tail and the far tail).** For $N\ge1$ and $L\ge0$,

```math
\sum_{n<N}\tau_L(n)=\sum_{j>L}b^{-j}\bigl(A(N-1+j)-A(j-1)\bigr)\le\frac{\widehat A(N+L)}{(b-1)\,b^L},
```

where

```math
\widehat A(X)=\sum_{m\ge1}|a(m)|\min(1,b^{X-m})=\Bigl(1-\frac1b\Bigr)\sum_{i\ge0}b^{-i}A(X+i).
```

*Proof.* Exchanging the order of summation gives the identity, since $n+j$ runs over $[j,N-1+j]$. For the inequality, coefficient $a(m)$ is paired with the shifts $0\le n\le\min(N-1,m-L-1)$. The geometric sum of $b^{n-m}$ over these is at most $b^{-\max(L,m-N)}/(b-1)$. The second formula for $\widehat A$ is Abel summation. ∎

Every term with $m>N+L$, the far tail, is weighted by $b^{N+L-m}$. If $A(X)\le CX$ for all $X$, then $\widehat A(X)\le C(X+1/(b-1))$.

### 1.2 The finite transfer inequality

**Theorem 1.4 (finite all-prefix transfer).** For all $N\ge1$, integers $L\ge0$ and $\varepsilon>0$,

```math
E_N(\varepsilon)\le L\,(1+S(N-1))+\frac{\widehat A(N+L)}{(b-1)\,b^L\,\varepsilon},
```

```math
\sup_x|D_N(x+F)-D_N(x)|=1-D_N(F)\le2\varepsilon+\frac{L(1+S(N-1))}{N}+\frac{\widehat A(N+L)}{(b-1)\,b^L\,\varepsilon N}.
```

*Proof.* Shadowed shifts are counted by Lemma 1.2. Every other shift satisfies $\|b^nF\|\le\tau_L(n)$ by Lemma 1.1. By Markov's inequality, $\#\{n<N:\tau_L(n)>\varepsilon\}\le\varepsilon^{-1}\sum_{n<N}\tau_L(n)$, and Lemma 1.3 bounds that sum. Finish with the deficit bound and sharp translation. ∎

The bounded-coefficient case $|a|\le B$ is Lean's `sparse_farCount_le`, which charges $w\cdot\#\{m_k<N+w\}$ with $2Bb^{-w}\le\varepsilon$. Theorem 1.4 handles signed coefficients of any size through their mass.

**Window form (nonuniform local estimate).** For $N_0\ge0$ and $H\ge1$, the same proof applied to shifts in $[N_0,N_0+H)$ gives

```math
\#\{N_0\le n<N_0+H:\|b^nF\|>\varepsilon\}\le L\bigl(1+S(N_0+H-1)-S(N_0)\bigr)+\frac{\widehat A_{N_0,H}(L)}{(b-1)\,b^L\,\varepsilon},
```

where

```math
\widehat A_{N_0,H}(L)=\sum_{m>N_0+L}|a(m)|\min(1,b^{N_0+H+L-m}).
```

Thus local support density and local mass control the local proportion of far shifts. Summing over dyadic windows recovers the prefix statement. There is also a pointwise estimate, $\|b^nF\|\le b^{-(\nu-n)}(|a(\nu)|+\tau_0(\nu))$ with $\nu$ the next occupied index after $n$.

### 1.3 Linear mass: the rate and its constant

**Theorem 1.5.** If $A(X)\le CX$ for every $X\ge1$, the bound in the opening theorem holds for every $N\ge1$.

*Proof.* We have $\rho=\rho_N\in(0,1]$. If $\rho=1$, the right side is at least $3$. Otherwise put $\varepsilon=\rho/2$ and $L=\max\bigl(0,\lceil\log_b(4C/((b-1)\rho^2))\rceil\bigr)$.

- If $L+1/(b-1)\le N$, then $\widehat A(N+L)\le2CN$, so the last term of Theorem 1.4 is at most $4Cb^{-L}/((b-1)\rho)\le\rho$. Hence $1-D_N\le\rho+L\rho+\rho=(L+2)\rho$.
- Otherwise $L\ge N$, so $(L+2)\rho>1$ and the bound is trivial.

Finally $L+2$ is at most the bracket in the opening theorem: use the ceiling when $L\ge1$ and $\rho<1$ when $L=0$. ∎

The implicit constant enters only additively, through $\log_b^+(4C/(b-1))$. Thus $1-D_N\le(2+o(1))\rho_N\log_b(1/\rho_N)$ whenever $C=\rho_N^{-o(1)}$.

**Proposition 1.6 (the constant 2 is sharp).** Let $K$ have base-$b$ digits $1,0,1,\dots,0,1$, with $K\asymp q$. Put $z=K/(b^q-1)=\sum_{k\ge1}Kb^{-qk}$ and $N=q$. Then $A(X)\le(K/q)X$, $\rho_N=1/q$, and

```math
(1-D_q(z))\,q=2\log_bq+O_b(\log\log q).
```

*Proof.* The orbit has period $q$. Let $w$ be the number of digits of $K$. For $1\le j<w$, the point $x_{q-j}=\{Kb^{-j}(1+(b^q-1)^{-1})\}$ is a digit suffix of $K$. Since the digits alternate, it lies at circle distance at least $c_b>0$ from $0$. For $j\ge w$ the point is $Kb^{-j}(1+O(b^{-q}))$. Its distance from $0$ is at least $\eta$ for $j\le w+\log_b(1/\eta)-O(1)$ and at most $\zeta$ for $j\ge w+\log_b(1/\zeta)+O(1)$.

Take $\zeta=1/q$ and $\eta=3(2\log_bq)/q$ in Lemma 3.3 below. This gives the lower bound $(w+\log_b(1/\eta)-O(1))/q=(2\log_bq-O(\log\log q))/q$. Theorem 1.5 gives the upper bound. ∎

To obtain a single number with $\rho_N\to0$, concatenate such periodic blocks on rapidly growing ranges with $q_k\to\infty$. The script computes the exact ratio $(1-D_q)/(\rho\log_2(1/\rho))$ for $b=2$:

| $q$ | 16 | 64 | 256 | 1024 | 4096 |
|---|---|---|---|---|---|
| ratio | 1.562 | 1.719 | 1.791 | 1.833 | 1.861 |

This is consistent with $2-O(\log\log q/\log q)$.

### 1.4 Larger mass

**Theorem 1.7.** For every $N\ge1$, with $\rho=\rho_N$ and $\mu_N=\max(1,\widehat A(2N)/N)$,

```math
1-D_N(F)\le\rho\Bigl(2\log_b\frac1\rho+\log_b\mu_N+\log_b^+\frac{2}{b-1}+3\Bigr).
```

*Proof.* As for Theorem 1.5, with $L=\max(0,\lceil\log_b(2\mu_N/((b-1)\rho^2))\rceil)$ and $\widehat A(N+L)\le\widehat A(2N)\le\mu_NN$ when $L\le N$. ∎

So $L$ grows by $\log_b\mu_N$. Suppose $A(X)\le XM(X)$ with $M\ge1$ nondecreasing and of polynomial growth. Then $\mu_N\le3M(4N)$ for large $N$, and

```math
S(N)\log\frac{e\,N\,M(4N)}{1+S(N)}=o(N)\ \Longrightarrow\ F\in K_b.
```

For doubling $M$ one may write $M(N)$. In particular:

- $M=X^\alpha$ requires $S(N)=o(N/\log N)$;
- $M=(\log X)^\alpha$ requires $S(N)=o(N/\log\log N)$.

Counterexample (c) in Section 2.4 has $M(X)=X^{\gamma}$, $S(N)\asymp N/\log N$ and a normal sum. Thus $o(N)$ cannot be weakened to $O(N)$.

The width form of the transfer inequality is Theorem 2.2. Its main term is the radix-digit width sum $\sum_{m\le N,\ a(m)\ne0}(1+\lfloor\log_b|a(m)|\rfloor)$, plus $L$ per source. By concavity of the logarithm, $\sum(1+\log_b|a|)\le S(1+\log_b(A/S))$, so the width form is never worse than Theorem 1.7 to leading order. It is strictly better when the coefficients carry radix powers or have bounded mean.

## 2. Displaced sources (B2)

### 2.1 Exact reindexing in every radix

For $a(m)\ne0$ write $a(m)=b^{V(m)}U(m)$ with $V(m)=v_b(a(m))$ the largest $v$ with $b^v\mid a(m)$, so that $b\nmid U(m)$ and $U(m)$ carries the sign. Put $t(m)=m-V(m)\in\mathbb Z$, let $u(m)$ be the number of base-$b$ digits of $|U(m)|$, and put $\tilde t(m)=t(m)-u(m)=m-(\text{number of digits of }|a(m)|)$. The radix $b$ may be composite. Then $U$ may still be divisible by a prime factor of $b$, as with $U=2$ for $b=6$, but its last base-$b$ digit is nonzero.

**Theorem 2.1 (displaced reindexing).** Each fiber $\{m:t(m)=t\}$ is finite, and only finitely many $m$ have $t(m)\le0$. With $C(t)=\sum_{t(m)=t}U(m)\in\mathbb Z$ we have $\sum_t|C(t)|b^{-t}<\infty$ and

```math
F=\sum_{t\in\mathbb Z}C(t)\,b^{-t},\qquad
\{b^nF\}=\Bigl\{\sum_{d\ge1}C(n+d)\,b^{-d}\Bigr\}\quad(n\ge0).
```

In particular $F\equiv\sum_{t\ge1}C(t)b^{-t}\pmod 1$, and $D_N(F)$ is unchanged by discarding $t\le0$.

*Proof.* Since $|U|\ge1$, the size of a fiber times $b^{-t}$ is at most $\sum|a(m)|b^{-m}$. A term with $t(m)\le0$ has $|a(m)|b^{-m}\ge1$, so there are finitely many. Absolute convergence permits the rearrangement. At shift $n$, terms with $t\le n$, including the finitely many with $t\le0$, contribute the integers $C(t)b^{n-t}$. ∎

$C(t)$ may vanish (signed cancellation) or be divisible by $b$ (a collision). The identity needs neither condition. The script checks it exactly in radices 2, 3, 6, 10 and 12, including sources with $t\le0$, for 1,875 shifts.

### 2.2 The displaced width inequality

**Theorem 2.2.** For $N\ge1$, $L\ge0$ and $\varepsilon>0$,

```math
E_N(\varepsilon)\le\Bigl|\bigcup_{a(m)\ne0}[\tilde t(m)-L,\ t(m)-1]\cap[0,N)\Bigr|
+\frac{\widehat P(N+L)}{(b-1)\,b^L\,\varepsilon},
```

where

```math
\widehat P(X)=\sum_{a(m)\ne0}|U(m)|\,b^{-u(m)}\min\bigl(1,b^{X-\tilde t(m)}\bigr).
```

The union has size at most $W_U(N)+L\,(1+P(N))+\Lambda_N$, where

- $P(N)=\#\{m:1\le t(m)\le N\}$;
- $W_U(N)=\sum_{1\le t(m)\le N}u(m)$;
- $\Lambda_N=\max_{t(m)>N}(u(m)-t(m)+N)^+$.

*Proof.* At shift $n$, a source with $t(m)\le n$ contributes the integer $U(m)b^{n-t(m)}$ (Lemma 1.1 with $I$ the indices where $b^{m-n}\mid a(m)$). If $n$ lies in no interval of the union, every source with $t(m)>n$ has $\tilde t(m)>n+L$. Its contribution is then $|U|b^{n-t}<b^{n-\tilde t}\le b^{-L-1}$, so $\|b^nF\|\le\sum_{\tilde t(m)>n+L}|U(m)|b^{n-t(m)}$. Markov's inequality is applied on the non-shadowed shifts $n<N$ to this truncated tail $\sum_{\tilde t(m)>n+L}|U(m)|b^{n-t(m)}$, whose sum over $n<N$ is at most $\widehat P(N+L)/((b-1)b^L)$, as in Lemma 1.3.

Intervals of sources with $t(m)>N$ all end at $N-1$, so their union inside $[0,N)$ is the longest of them, of length at most $L+\Lambda_N$. ∎

Taking $V'=0$, $U'=a$ instead of the full valuation gives the raw width bound with intervals $[\tilde t(m)-L,m-1]$. The digit arrival $\tilde t$ is the same in both versions. Removing the radix power only cuts off the $V(m)$ trailing positions, at which the source is an integer. The theorem is source by source and needs no merging. Applying Theorem 1.4 to the merged sequence $C$ gives a second bound, with $S_{\rm eff}(X)=\#\{1\le t\le X:C(t)\ne0\}\le P(X)$ and $A_{\rm eff}(X)=\sum_{t\le X}|C(t)|\le\sum_{1\le t(m)\le X}|U(m)|$.

### 2.3 Criteria for membership in $K_b$

Each of the following implies $F\in K_b$, with the rate stated.

- **(K1) Displaced linear mass.** $\widehat A_C(2N)=O(N)$ and $S_{\rm eff}(N)=o(N)$. Then Theorem 1.7 applied to $C$ gives $1-D_N\le(2+o(1))\rho\log_b(1/\rho)$ with $\rho=(1+S_{\rm eff}(N-1))/N$.
- **(K2) Width density zero.** $W_U(N)=o(N)$, together with the regularity conditions $\Lambda_N=o(N)$ and $\widehat P(2N)=O(N)$. Since $u\ge1$, this already forces $P(N)=o(N)$. Take $\varepsilon=\pi_N=P(N)/N$ and $L=\lceil\log_b(\widehat P(2N)/(\pi_N^2N))\rceil$ in Theorem 2.2. Both regularity conditions hold when $\log|a(m)|=o(m)$ and $m\mapsto\tilde t(m)$ is boundedly many-to-one.
- **(K3) Bounded mean of $|U|$.** If $\sum_{1\le t(m)\le X}|U(m)|\le K_0P(X)$, then Jensen's inequality gives $W_U\le P(1+\log_bK_0)$. Under the regularity of (K2) with $\widehat P(N+L)\le P(N)\pi_N^{-o(1)}$, we get $1-D_N\le(1+o(1))\,\pi_N\log_b(1/\pi_N)$, with **constant 1**. Section 3 shows that $1$ is attained.
- **(K4) Large exceptional coefficients** enter only through their widths. A set $E$ of sources with $\sum_{m\in E,\,t(m)\le N}u(m)=o(N)$ (respectively $o(P\log(N/P))$) does not affect (K2) (respectively the constant in (K3)).
- **Signed cancellation and local separation.** Cancellation only lowers $S_{\rm eff}$ and $A_{\rm eff}$, so it never hurts an upper bound. Separation, and positivity or two-sided isolation, matter only for lower bounds and constants (Section 3).

In general the leading term is $(W+S\lambda)/N$, with $\lambda=\log_b(N/S)$. The constant is therefore $1+(\text{mean radix width})/\lambda$: it is $1$ for bounded widths and at most $2$ for linear mass. In the script, a radix-10 series with coefficients $\pm10^{\min(30,\lfloor m/40\rfloor)}(1+k\bmod9)$ at $m=\lfloor k^{1.6}\rfloor$ has $1-D_{1000}=0.1630$. The best displaced-width bound over the tested parameters is $0.2126$, while the raw-mass bound is $2.4020$, which is vacuous.

### 2.4 Density-zero support without coefficient control

Each construction below is verified exactly in the script.

**(a) Logarithmic support, rational sum outside $K_b$.** Let $0=m_0<m_1<m_2<\cdots$ be any infinite sequence of even integers, and put

```math
a(m_k)=\frac{b^{m_k-m_{k-1}}-1}{b^2-1}=\sum_{m_{k-1}<2i\le m_k}b^{m_k-2i},
```

with $a=0$ elsewhere. Then $F=\sum_{i\ge1}b^{-2i}=1/(b^2-1)$. Since $a(m_k)\equiv1\pmod b$, $V\equiv0$. With $m_k=2^k$ we get $S(X)=\lfloor\log_2X\rfloor$. The orbit alternates between $1/(b^2-1)$ and $b/(b^2-1)$, so $D_N=b/(b+1)$ for every even $N$ and $1-D_N\to1/(b+1)$. The reduced denominator $b^2-1$ does not divide $b^j(b-1)$, so $F\notin K_b$. Multiplying $a$ by $b-1$ gives $1/(b+1)$. The coefficient widths $m_k-m_{k-1}-1$ fill the gaps, so $W(X)\sim X$.

**(b) Logarithmic support, normal sum.** Let $\xi=\sum\xi_ib^{-i}$ be $b$-normal, for instance Champernowne's number in base $b$. For any $0=m_0<m_1<\cdots$ put $a(m_k)=\sum_{m_{k-1}<i\le m_k}\xi_ib^{m_k-i}$. Then $F=\xi$, $|a(m_k)|b^{-m_k}<b^{-m_{k-1}}$, and $S$ may grow as slowly as desired. Since $D_N(\xi)\to0$, we get $\sup_x|D_N(x+F)-D_N(x)|\to1$, the largest possible value. In the script $b=2$, $m_k=2^k$, and $13$ coefficients reproduce 8,192 Champernowne digits.

**(c) Polynomial coefficients, normal sum.** Fix $0<\gamma\le1$, put $\ell_k=\max(1,\lfloor\gamma\log_b(m_{k-1}+1)\rfloor)$ and $m_k=m_{k-1}+\ell_k$, and use the same digit blocks. Then

```math
|a(m_k)|<b^{\ell_k}\le\max(b,m_k^{\gamma})\le b\,m_k^{\gamma},\qquad S(X)\sim\frac{X}{\gamma\log_bX}=o(X),\qquad A(X)\ll X^{1+\gamma},\qquad F=\xi ,
```

with $|a(m_k)|<b^{\ell_k}\le m_k^\gamma$ for all $m_k\ge b^{1/\gamma}$.

Taking $\ell_k\approx\log_b\log m_k$ instead gives $|a(m)|\le\log m$, $S(X)\asymp X/\log\log X$ and again a normal sum. In both cases $S(N)\log(NM/S)\asymp N$ for $M(X)=X^\gamma$ (respectively $\log X$): the conditions in Theorem 1.7 just fail. The script checks $|a(m_k)|\le\sqrt{bm_k}$ for $\gamma=1/2$.

Thus density-zero support, raw or displaced, says nothing by itself. All three examples have width density one, which is exactly the hypothesis that fails in (K2).

## 3. Exact leading constants (B3)

### 3.1 Source decomposition and a two-sided sandwich

By Theorem 2.1 we may assume $F\equiv\sum_{t\ge1}C(t)b^{-t}$. Let $\mathcal T=\{t\ge1:C(t)\ne0\}$, assumed infinite, and put $S_{\rm eff}(N)=\#\mathcal T\cap[1,N]$, $\rho_N=S_{\rm eff}(N)/N$ and $\lambda_N=\log_b(1/\rho_N)$. For $t\in\mathcal T$ define:

- $t^-$, the previous source, or $0$ if none;
- $g_t=t-t^-$, the gap before $t$;
- $u(t)$, the number of base-$b$ digits of $|C(t)|$;
- $A(t)=\sum_{d\ge1}C(t+d)b^{-d}$ and $Y(t)=C(t)+A(t)$.

**Lemma 3.1 (exact source decomposition).** The map $n\mapsto(t,j)$, with $t$ the first source after $n$ and $j=t-n$, is a bijection from $\mathbb N$ onto $\{(t,j):t\in\mathcal T,\ 1\le j\le g_t\}$, and

```math
x_n=\{b^{-j}\,Y(t)\}.
```

If $(t,t+h]\cap\mathcal T=\emptyset$, then $A(t)=b^{-h}A(t+h)$.

*Proof.* At shift $n=t-j$, all sources $\le n$ (including $t^-$ when $j=g_t$) are integral. The others are $t$ and its successors. ∎

Hence, exactly,

```math
E_N(r)=\sum_{t\in\mathcal T}\#\{1\le j\le g_t:\ t-j<N,\ \|b^{-j}Y(t)\|>r\}.
```

The orbit of $F$ is completely described by the gap before each source and that source's local value.

**Lemma 3.2 (one source).** Suppose $|A(t)|\le1/2$ and write $u=u(t)$.

1. If $b\nmid C(t)$, then $\|b^{-j}Y(t)\|\ge b^{-j}/2$ for every $j\ge1$. Indeed $C(t)\not\equiv0\pmod{b^j}$, so $C(t)+A(t)$ is at distance at least $1/2$ from $b^j\mathbb Z$.
2. If $j\ge u+1$, then $\|b^{-j}Y(t)\|=b^{-j}|Y(t)|\in[b^{-j}(b^{u-1}-\tfrac12),\ b^{-j}(b^u-\tfrac12)]$.

Consequently, for $0<r,\eta<1/2$ and $g=g_t$, put $\lambda'_\eta=\lfloor\log_b(1/(2\eta))\rfloor$ and let

```math
Z_t(\eta)=\#\{\lambda'_\eta<j\le u:\ \|b^{-j}Y(t)\|<\eta\}
```

count the internal near-zero suffixes. Then

```math
\min(g,\,u+\lambda'_\eta-1)-1-Z_t(\eta)\ \le\ \#\{j\le g:\|b^{-j}Y\|\ge\eta\},\qquad
\#\{j\le g:\|b^{-j}Y\|>r\}\le\min\bigl(g,\,u+\lceil\log_b(1/r)\rceil\bigr).
```

$Z_t(\eta)=0$ whenever $u\le\lambda'_\eta$.

**Lemma 3.3 (separated mass on the circle).** Let $0<\zeta$, $\Delta\ge0$, $\zeta+\Delta<\eta\le1/2$. Suppose at least $\Delta N$ of the points satisfy $\|x_n\|\le\zeta$ (the bulk) and at least $\Delta N$ satisfy $\|x_n\|\ge\eta$ (the marked points). Then $1-D_N\ge\Delta$.

*Proof.* Let $I=[s,t)\subseteq[0,1]$.

- For the positive excess $\mu(I)-|I|$: if $|I|\ge\Delta$ the excess is at most $1-\Delta$. If $|I|<\Delta$ and $I$ meets the bulk, then $I\subseteq[0,\zeta+\Delta)$ or $I\subseteq(1-\zeta-\Delta,1)$, so $I$ misses every marked point. Otherwise $I$ misses the bulk. In both cases $\mu(I)\le1-\Delta$.
- For the negative excess $|I|-\mu(I)$: if $|I|>1-\Delta$, then $s<\Delta<\eta$ and $t>1-\eta$, so $I$ contains every marked point and $\mu(I)\ge\Delta$. ∎

This is the circle version of Lean's `one_sub_discrepancy_ge_of_separated_mass`, which handles the one-sided binary case. It covers sources of both signs and arcs that wrap around $0$. It also shows that an arc of optimal concentration has length at most $1-D_N$.

### 3.2 The isolated-source law

**Theorem 3.4.** Assume $\rho_N\to0$ and the following.

- **(I1) Upper regularity.**
  - $\widehat P_C(N+3\lambda_N)\le S_{\rm eff}(N)\rho_N^{-o(1)}$;
  - $\Lambda_N=o(S_{\rm eff}\lambda_N)$;
  - $W(N)=\sum_{t\in\mathcal T\cap[1,N]}u(t)=O(S_{\rm eff}(N)\lambda_N)$;
  - every subset of $o(S_{\rm eff}(N))$ sources in $\mathcal T\cap[1,N]$ has total width $o(W+S_{\rm eff}\lambda_N)$ (in particular, this holds for the sources excluded by (I2), right-isolation, or $|A(t)|>1/2$).
- **(I2) Isolation.** All but $o(S_{\rm eff}(N))$ sources $t\le N$ satisfy $b\nmid C(t)$ and $g_t\ge u(t)+\lambda_N$.
- **(I3) Mass.** $\widehat A_C(N+\lambda_N)=O(S_{\rm eff}(N)\rho_N^{-1/3})$.
- **(I4) Digits.** $\sum_tZ_t(\eta_N)=o(W(N)+S_{\rm eff}(N)\lambda_N)$ for $\eta_N=\rho_N\lambda_N^2$.

Then

```math
1-D_N(F)=(1+o(1))\,\frac{W(N)+S_{\rm eff}(N)\,\lambda_N}{N}.
```

If $|C(t)|\le B$, conditions (I1), (I3) and (I4) hold automatically, $b\nmid C(t)$ may be dropped from (I2), and the law reads

```math
1-D_N(F)\sim\rho_N\log_b\frac1{\rho_N}.
```

*Proof.*

*Upper bound.* Apply Theorem 2.2 to $C$ with $\varepsilon=\rho_N$ and $L=\lambda_N+o(\lambda_N)$ chosen so that the Markov term is at most $\rho_NN$. This gives $1-D_N\le2\rho_N+(W+S_{\rm eff}\lambda_N(1+o(1))+\Lambda_N)/N$.

*Lower bound.* Left isolation of almost all sources at radius $h_N=\lfloor\lambda_N/2\rfloor$ implies right isolation of almost all sources at the same radius, because $t\mapsto$ (next source) is injective. For right-isolated $t\le N$, Lemma 3.1 gives $A(t)=b^{-h}A(t+h)$ with $t+h<N+\lambda_N$, and $t\mapsto t+h$ is injective. Lemma 1.3 with $L=0$ bounds $\sum_{s<N+\lambda_N}|A(s)|$ by $\widehat A_C(N+\lambda_N)/(b-1)$, so Markov's inequality gives

```math
\#\{t\le N:|A(t)|>1/2\}\le2b^{-h}\widehat A_C(N+\lambda_N)/(b-1)=o(S_{\rm eff}).
```

On the remaining good set $G$, Lemma 3.2 marks at least $u(t)+\lambda'_\eta-2-Z_t(\eta)$ positions per source. These positions lie in disjoint gaps.

Take $\zeta=\rho_N$ and $\eta=\zeta+2(W+S_{\rm eff}\lambda_N)/N+\rho_N$. Then $\lambda'_\eta=\lambda_N-O(\log\lambda_N)$, the bulk has proportion $1-o(1)$ by the upper bound, and Lemma 3.3 applies. ∎

**Case 1 (power-law support).** If $S_{\rm eff}(N)\sim cN^\sigma$ with $0<\sigma<1$ and the coefficients are bounded, under (I2) at radius $\lambda_N\sim(1-\sigma)\log_bN$,

```math
1-D_N(F)\sim\frac{c\,(1-\sigma)}{\log b}\,N^{\sigma-1}\log N.
```

The disjoint preceding neighborhoods have length $(1-\sigma)\log_bN-O(\log\log N)$. Examples:

- **Squares.** $\sum_{j\ge1}b^{-j^2}$ has $1-D_N\sim N^{-1/2}\log_bN/2$. So does $\Theta_3(1/b)$ after displacing $2b^{-j^2}=b^{-(j^2-1)}$ when $b=2$.
- **Cubes.** $\sum_kb^{-k^3}$ has $1-D_N\sim\tfrac23N^{-2/3}\log_bN$.

**Case 2 (logarithmic support).** If $S_{\rm eff}(N)\sim cN/(\log N)^\kappa$, under (I2) at radius $\lambda_N\sim\kappa\log_b\log N$,

```math
1-D_N(F)\sim\frac{c\,\kappa}{\log b}\,\frac{\log\log N}{(\log N)^\kappa}.
```

The neighborhoods now have length $\kappa\log_b\log N-O(\log\log\log N)$.

**Corollary 3.5 (the prime constant).** For every $b\ge2$,

```math
1-D_N\Bigl(\sum_pb^{-p};b\Bigr)=\sup_x\Bigl|D_N\Bigl(x+\sum_pb^{-p}\Bigr)-D_N(x)\Bigr|\sim\frac{\log\log N}{\log b\cdot\log N}.
```

*Proof.* Use Case 2 with $c=\kappa=1$. The Selberg upper-bound sieve gives $\#\{p\le x:p+h\text{ prime}\}\ll\mathfrak S(h)x/(\log x)^2$ uniformly in $h$, with $\sum_{h\le H}\mathfrak S(h)\ll H$. Hence all but $O(x\log\log x/(\log x)^2)$ primes have no other prime within $H=2\log_b\log x$. The coefficients are $1$. ∎

The isolation is asymptotic only: at $N=2^{18}$, 67% of primes have another prime within distance 6.

### 3.3 Growing widths (Case 3)

Let $S_{\rm eff}(N)\sim cN^\sigma$, let $u(t)=\gamma\log_bt+O(1)$ with $\gamma>0$, and assume isolation at radius $(1-\sigma+\gamma)\log_bN$. Then

```math
W(N)=\gamma S_{\rm eff}(N)\log_bN\,(1+O(1/\log N)).
```

By Theorem 3.4, under (I4),

```math
1-D_N(F)\sim\frac{c\,(1-\sigma+\gamma)}{\log b}\,N^{\sigma-1}\log N .
```

**When does the digit condition hold?** Lemma 3.2(1) shows that internal positions $j<\lambda'_\eta=\lambda_N-O(\log\lambda_N)$ are always marked. Hence:

- **$\gamma\le1-\sigma$:** $Z_t=0$, or $O(\log\lambda)=o(\lambda)$ per source at equality. The constant $c(1-\sigma+\gamma)/\log b$ is unconditional.
- **$\gamma>1-\sigma$:** an internal position $j\in(\lambda',u]$ is near zero exactly when the digits of $C(t)$ at positions $j,j-1,\dots$ begin with a run of about $\lambda_N$ zeros or about $\lambda_N$ copies of $b-1$. The constant depends on the digits in the following way.
  - **Generic digits give the full constant.** Let $\pm C(t_k)=n_k$ run through the positive integers not divisible by $b$; for $b=2$, $C(t_k)=\pm(2k+1)$. Each residue class modulo $b^j$ not divisible by $b$ occurs once per period. Hence

    ```math
    \#\{k\le K:\|b^{-j}(n_k+A)\|<\eta\}\le(2K/b^j+1)(\eta b^j+3),
    ```

    and summing over $\lambda'<j\le\log_b(2K)$ gives $\sum_kZ_k=O(K\eta\log K+Kb^{-\lambda'}+\log K)=o(K\lambda)$. So (I4) holds.
  - **Pure powers** $C=b^{w}$ displace to $U=1$ (Case 1): the constant is $c(1-\sigma)/\log b$.
  - **All-$(b-1)$ coefficients** $b^w-1$: here $Y\equiv-(1-A)$ modulo $b^w$, so the source acts like two unit sources, at $t-w$ and at $t$. The constant is $2c(1-\sigma)/\log b$.

In general the constant lies between $c(1-\sigma)/\log b$ and $c(1-\sigma+\gamma)/\log b$. The internal positions inside the coefficient width fall in the tiny arc near $0$ only along long runs of $0$ or $b-1$.

The script uses $m_k=\lfloor k^{3/2}\rfloor$, so $\sigma=\gamma=2/3$ and $c=1$. At $N=2^{18}$ the ratio of $1-D_N$ to $(W+S\lambda)/N$ is:

| coefficients | ratio | prediction |
|---|---|---|
| $(-1)^k(2k+1)$ | 1.039 | 1 |
| $2^w$ | 0.333 | $(1-\sigma)/(1-\sigma+\gamma)=1/3$ |
| $2^w-1$ | 0.663 | $2/3$ |

The boundary case $\sigma=\gamma=1/2$ is unconditional: $\sum_j(2j+1)b^{-j^2}$ has $1-D_N\sim N^{-1/2}\log_bN$. At $N=2^{18}$, $b=2$, this predicts $0.03516$, and the measured value is $0.03506$.

### 3.4 Clustered sources

**Theorem 3.6 (shadow law).** If $1\le C(t)\le B$ on $\mathcal T$ and $\rho_N\to0$, then

```math
1-D_N(F)=\frac1N\sum_{t\in\mathcal T\cap[1,N]}\min(g_t,\lambda_N)\;+\;O_B\Bigl(\rho_N\log(2+\lambda_N)+\frac{\lambda_N}{N}\Bigr).
```

(The boundary term $O_B(\lambda_N/N)$ accounts for the first source $t_*=\min(\mathcal T\cap(N,\infty))$ after $N$, which can shadow at most $\lambda_N+O_B(1)$ shifts in $[0,N)$; it is absorbed into $O_B(\rho_N\log(2+\lambda_N))$ whenever $S_{\rm eff}(N)\log(2+\lambda_N)\gg\lambda_N$.)

*Proof.* Positivity gives $Y(t)\in[1,Bb/(b-1)]$, so for $j\ge\log_b(2Bb/(b-1))$ the distance is exactly $b^{-j}Y(t)$. No tail or isolation hypothesis is needed. The upper count per source is at most $\min(g_t,\lambda_N+O_B(1))$ at $r=\rho_N$. The lower count is at least $\min(g_t,\lambda_N-\log_b(4\lambda_N))-O_B(1)$ at $\eta\le4\rho_N\lambda_N$. Apply Lemma 3.3. ∎

The law has an asymptotic form when $S_{\rm eff}\log\lambda_N=o(\sum\min(g_t,\lambda_N))$. For isolated sources $\sum\min=S_{\rm eff}\lambda_N(1-o(1))$, which recovers Cases 1 and 2. Clustering lowers the sum and can change the power of $\log N$. For the Phase 19 missing-digit supports, $\sum_t\min(g_t,L)\asymp N^\sigma L^{1-\sigma}$, which gives $(\log N/N)^{1-\sigma}$ in place of $N^{\sigma-1}\log N$, in agreement with [Phase 19](../phase19/products-of-remainders.md#sharp-rates-from-missing-digits-in-the-insertion-indices). Signed clusters can also cancel $Y(t)$, so two-sided isolation (Theorem 3.4) is needed when signs vary.

## 4. Recommended Lean core statements

These finite statements build on `Phase18Synthetic.farCount`, `Near`, `discrepancy_deficit_le` and `SharpTranslation.sampleDisc`. Indices start at $0$; a term $a(0)$ is integral and harmless.

```lean
namespace NormalityChecker.Phase20Transfer
open Finset

noncomputable def coeffValue (b : ℕ) (a : ℕ → ℤ) : ℝ := ∑' m, (a m : ℝ) / (b : ℝ) ^ m
def CoeffSummable (b : ℕ) (a : ℕ → ℤ) : Prop := Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m
def suppCount (a : ℕ → ℤ) (X : ℕ) : ℕ := ((Icc 1 X).filter fun m => a m ≠ 0).card
def massCount (a : ℕ → ℤ) (X : ℕ) : ℕ := ∑ m ∈ Icc 1 X, (a m).natAbs
noncomputable def tailWeight (b : ℕ) (a : ℕ → ℤ) (L n : ℕ) : ℝ :=
  ∑' i, |(a (n + L + 1 + i) : ℝ)| / (b : ℝ) ^ (L + 1 + i)
noncomputable def weightedMass (b : ℕ) (a : ℕ → ℤ) (X : ℕ) : ℝ :=
  ∑' m, |(a m : ℝ)| * min 1 ((b : ℝ) ^ X / (b : ℝ) ^ m)

/-- Lemma 1.1: terms that are integral at shift `n` drop out. -/
theorem near_of_dvd_terms {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (ha : CoeffSummable b a)
    (n : ℕ) (I : Set ℕ) (hI : ∀ m ∈ I, n < m → (b : ℤ) ^ (m - n) ∣ a m) :
    Phase18Synthetic.Near ((b : ℝ) ^ n * coeffValue b a)
      (∑' m, (Iᶜ ∩ Set.Ioi n).indicator (fun m => |(a m : ℝ)| * (b : ℝ) ^ n / (b : ℝ) ^ m) m)

theorem near_of_window_clear {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (ha : CoeffSummable b a)
    {n L : ℕ} (hclear : ∀ j ∈ Icc 1 L, a (n + j) = 0) :
    Phase18Synthetic.Near ((b : ℝ) ^ n * coeffValue b a) (tailWeight b a L n)

/-- Lemma 1.2. -/
theorem card_shadow_le (a : ℕ → ℤ) (N L : ℕ) :
    ((range N).filter fun n => ∃ j ∈ Icc 1 L, a (n + j) ≠ 0).card ≤
      L * (1 + suppCount a (N - 1))

/-- Lemma 1.3 (inequality form; the exact identity is a `Finset` exchange). -/
theorem sum_tailWeight_le {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (ha : CoeffSummable b a)
    (N L : ℕ) :
    ∑ n ∈ range N, tailWeight b a L n ≤
      weightedMass b a (N + L) / (((b : ℝ) - 1) * (b : ℝ) ^ L)

/-- Markov on a finite set. -/
theorem card_lt_le_sum_div {s : Finset ℕ} {τ : ℕ → ℝ} (hτ : ∀ n ∈ s, 0 ≤ τ n)
    {ε : ℝ} (hε : 0 < ε) :
    ((s.filter fun n => ε < τ n).card : ℝ) ≤ (∑ n ∈ s, τ n) / ε

/-- Theorem 1.4. -/
theorem coefficient_transfer {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (ha : CoeffSummable b a)
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) (L : ℕ) :
    |radixDiscrepancy b (x + coeffValue b a) N - radixDiscrepancy b x N| ≤
      2 * ε + ((L * (1 + suppCount a (N - 1)) : ℕ) : ℝ) / N +
        weightedMass b a (N + L) / (((b : ℝ) - 1) * (b : ℝ) ^ L * ε * N)

theorem weightedMass_le_of_linear {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (h0 : a 0 = 0)
    {C : ℝ} (hA : ∀ X, (massCount a X : ℝ) ≤ C * X) (X : ℕ) :
    weightedMass b a X ≤ C * (X + 1 / ((b : ℝ) - 1))

/-- Theorem 1.5. -/
theorem linear_mass_rate {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (h0 : a 0 = 0) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ X, (massCount a X : ℝ) ≤ C * X) {N : ℕ} (hN : 0 < N) :
    let ρ : ℝ := (1 + suppCount a (N - 1)) / N
    1 - radixDiscrepancy b (coeffValue b a) N ≤
      ρ * (2 * Real.logb b (1 / ρ) + max 0 (Real.logb b (4 * C / ((b : ℝ) - 1))) + 3)

/-- Corollary: linear mass and density-zero support give the kernel. -/
theorem tendsto_one_of_linear_mass {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (h0 : a 0 = 0)
    {C : ℝ} (hA : ∀ X, (massCount a X : ℝ) ≤ C * X)
    (hS : Filter.Tendsto (fun X => (suppCount a X : ℝ) / X) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => radixDiscrepancy b (coeffValue b a) N) Filter.atTop (nhds 1)

/-- Theorem 2.1 in the form used analytically: positions below `m - V m` are integral. -/
theorem near_displaced {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} (ha : CoeffSummable b a)
    (V : ℕ → ℕ) (hV : ∀ m, (b : ℤ) ^ V m ∣ a m) (n : ℕ) :
    Phase18Synthetic.Near ((b : ℝ) ^ n * coeffValue b a)
      (∑' m, if n + V m < m then |(a m : ℝ)| * (b : ℝ) ^ n / (b : ℝ) ^ m else 0)

/-- Lemma 3.1, local orbit before a source (`tailValue b C t = ∑_{d ≥ 1} C (t+d) b^{-d}`). -/
theorem shift_eq_before_source {b : ℕ} (hb : 2 ≤ b) {C : ℕ → ℤ} (hC : CoeffSummable b C)
    {t g j : ℕ} (hgap : ∀ s, t - g < s → s < t → C s = 0) (hj : 1 ≤ j) (hjg : j ≤ g)
    (hjt : j ≤ t) :
    shift b (coeffValue b C) (t - j) = Int.fract ((C t + tailValue b C t) / (b : ℝ) ^ j)

/-- Lemma 3.3. -/
theorem one_sub_sampleDisc_ge_of_marked {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n ∧ u n < 1)
    {N : ℕ} (hN : 0 < N) {ζ η Δ : ℝ} (hgap : ζ + Δ < η) (hη : η ≤ 1 / 2)
    (hbulk : Δ * N ≤ ((range N).filter fun n => min (u n) (1 - u n) ≤ ζ).card)
    (hmark : Δ * N ≤ ((range N).filter fun n => η ≤ min (u n) (1 - u n)).card) :
    Δ ≤ 1 - SharpTranslation.sampleDisc u N
```

Theorem 2.2 is `near_displaced` plus the shadow count and Markov's inequality, with the integer exponent $\tilde t(m)=m-V(m)-w(m)$ handled by `zpow`. For $|a(m)|<b^{V(m)+w(m)}$, only finitely many $m$ have $\tilde t(m)<X$, by summability. The asymptotic Theorems 3.4 and 3.6 combine these finite lemmas with counting hypotheses and are paper arguments.

## 5. Exact verification

```sh
python -B scripts/phase20_transfer.py
```

The script uses only the standard library, finishes in about 10 s, and exits 0.

- **B1.** Five test sequences use radices 2, 3, 10, 6 and 12. They include signed, clustered and random sequences and coefficients carrying radix powers. With exact `Fraction` orbits at $N=1200$, the script checks 520 inequalities: the shadow count, the exact mean-tail identity, Abel's identity for $\widehat A$, Theorem 1.4, Theorem 2.2 and the window form. Theorem 1.5 is checked at 1,612 prefixes, including every $N\le400$; the largest ratio of $1-D_N$ to the bound is $0.724$. The sharpness table of Proposition 1.6 is also produced.
- **B2.** The reindexing identity is checked exactly. Counterexample (a) is checked exactly, including $D_N=b/(b+1)$ for $b=2,3,6,10$. For (b) and (c), the digit strings are compared exactly with Champernowne's digits, and $D_{4096}=0.0861$ for $b=2$.
- **B3.** Digits are certified by two integer carries, and each reported discrepancy is within $b^{-P}$ of the true value, with $P=40$ (or $P=14$ for $b=10$). For each example the script also computes a certified lower bound from Lemma 3.3 (`lemma LB`) and asserts it is at most $1-D_N$. It computes the centered-arc upper bound $\min_r(2r+E_N(r)/N)$ and asserts that $1-D_N$ does not exceed it. At $N=2^{18}$:

| example | $1-D_N$ | model | ratio |
|---|---|---|---|
| $\sum2^{-j^2}$ | 0.01752 | 0.01758 | 0.997 |
| $\sum2^{-k^3}$ | 0.00288 | 0.00293 | 0.982 |
| $\sum_p2^{-p}$ | 0.32043 | 0.30802 | 1.040 |
| $\sum(2j+1)2^{-j^2}$ | 0.03506 | 0.03520 | 0.996 |

For the prime constant the model is $(\pi(N)/N)\log_2(N/\pi(N))$. The ratio of $1-D_N$ to the asymptotic expression $\log\log N/(\log2\log N)$ is $1.098$. For $\sum(2j+1)2^{-j^2}$ the model is $(W+S\lambda)/N$. The Case 3 contrasts are tabulated in Section 3.3. All ratios are finite measurements.

## 6. Scope, Lean formalization, and inputs

- **Kernel-verified in [`NormalityChecker/CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean)** (namespace `NormalityChecker.CoefficientTransfer`):
  - **B1 finite transfer & kernel membership:** `summable_abs_of_linear_mass`, `near_of_no_local_support`, `nearSupport_card_le`, `farCount_le_local_add_tail`, `markov_tail_card_le`, `sum_shiftedTail_le_of_linear_mass`, `finite_sparse_mass_transfer`, `finite_sparse_mass_translation`, `linear_mass_sparse_tendsto_one`, and `linear_mass_sparse_preserves_discrepancy`. (The Lean formalization uses the lookahead shadow bound $L\cdot S(N+L)$ and linear-mass tail $C(N+L+2)/b^L$, which suffices unconditionally for $A(X)=O(X), S(X)=o(X)\implies F\in K_b$ and exact translation preservation; the sharper non-lookahead bound $L(1+S(N-1))$ of Lemma 1.2, the weighted far tail $\widehat A(N+L)/((b-1)b^L)$ of Lemma 1.3, and the explicit rate Theorem 1.5 remain paper proofs.)
  - **B2 composite-radix factorization:** `radixVal`, `radixUnit`, `radixVal_pow_dvd`, `radixVal_mul_radixUnit`, `not_dvd_radixUnit`, and `displaced_term_eq` for every integer radix $b\ge2$ (prime or composite).
  - **B3/B4 circle separation (Lemma 3.3):** `one_sub_discrepancy_ge_of_bulk_and_far`.
- **Paper proofs with explicit constants:** Theorems 1.4 (sharp non-lookahead form), 1.5, 1.7, 2.1, 2.2, Proposition 1.6, Lemmas 3.1–3.2, and Theorems 3.4 and 3.6. Section 4 above also lists refined Lean signatures for future formalization of the sharper non-lookahead rate.
- **External inputs:** Corollary 3.5 uses the prime number theorem and the Selberg upper-bound sieve for prime pairs (Halberstam and Richert, *Sieve Methods*, Academic Press, 1974, Ch. 3). Counterexample (b) uses the normality of the base-$b$ Champernowne number; any established $b$-normal number serves.
