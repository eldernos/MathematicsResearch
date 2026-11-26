# Exact digit and word laws of the flagship kernel families

Phase 22, Track A, sub-tracks A3 and A4. Fix an integer radix $b\ge2$. For real $z$ write $d_j(z)=\lfloor b^jz\rfloor-b\lfloor b^{j-1}z\rfloor$ for the base-$b$ digits of the fractional part $\{z\}$. For a word $w\in\{0,\dots,b-1\}^L$ put

```math
Z_w(N)=\#\{0\le n<N:\ d_{n+1}(z)\cdots d_{n+L}(z)=w\},\qquad f_w(N)=\frac{Z_w(N)}N .
```

The word read at shift $n$ is the first $L$ digits of $\{b^nz\}$, so $Z_w(N)$ counts the $n<N$ with $\{b^nz\}$ in the cylinder $[u_w,u_w+b^{-L})$. A number is *simply normal in base $b$* if $f_c(N)\to1/b$ for every digit $c$, and *$L$-normal* if $f_w(N)\to b^{-L}$ for all $w$ of length $L$. As in Phases 19–21, $K_b=\{z:D_N(z;b)\to1\}$. For an integer sequence $a$ write $F_b(a)=\sum_{m\ge0}a(m)b^{-m}$, with support count $S(X)=\#\{1\le m\le X:a(m)\ne0\}$ and mass $A(X)=\sum_{m\le X}|a(m)|$. Write $E_b=\prod_{k\ge1}(1-b^{-k})$ and $D=q\,d/dq$, so that $D^jE_b$ means $(D^jE)(1/b)$. Throughout, $P_k^\mp=k(3k\mp1)/2$ and $T_k=k(k+1)/2$.

## Summary

| Result | Status |
| --- | --- |
| Lemma 0.1 (oriented tail), Lemma 0.2 (tail-sign reduction $f_{0^L}=\rho_+ +o(1)$) and Lemma 0.4 (signed Markov tail bound) | Paper proofs, self-contained; certified digits agree with the predictions at every non-exceptional shift (script) |
| Theorem 1: every nonnegative integer series covered by the coefficient transfer has $f_{0^L}(N)\to1$ in **every** base, including $b=2$, with explicit rates. Covers $\Theta_Q(1/b)$ for every positive definite binary $Q$, $\Theta_3(1/b)$, all $D^j\Theta_3(1/b)$, and $L_\chi(b)$ for every real nonprincipal $\chi$. None of them is simply normal in any base | Paper proof; $(1*\chi)\ge0$ proved and checked for all 50 real characters mod $q\le30$; explicit $\Theta_3$ bound checked on certified digits |
| Theorem 2: for every $j\ge0$ and $b\ge2$, $D^jE_b$, $D^jE_b^3$ and $E_b^2\,DE_b$ have $f_{0^L}\to\frac12$, $f_{(b-1)^L}\to\frac12$ and all other $f_w\to0$, with error $O_{b,j}((L+\log N)/\sqrt N)$. They are simply normal in base 2, not 2-normal, and not simply normal in base $b\ge3$ or in base $2^k$ for $k\ge2$ | Paper proof; mechanism checked shift by shift on certified digits ($b=2,3,10$; $j=0,1,2$) |
| Theorem 2.4: $D^jE_b$ ($j\ge1$), $D^jE_b^3$ and $E_b^2DE_b$ are disjunctive in every base. ($E_b$ is not.) | Paper proof; planted windows checked |
| Theorem 3.2: $\tau_{1,M}-\tau_{M-1,M}\ge0$ for all $n$ **iff** $\lambda(M)=2$, i.e. $M\mid24$; explicit negative values otherwise | Paper proof; checked for $M\le60$ |
| Theorem 3.5: digit law of the signed reflection series reduces exactly to an oriented gap-weighted sign proportion. Not simply normal in base $b\ge3$; in base 2 simply normal iff that proportion tends to $\tfrac12$ | Paper proof |
| Proposition 3.6: for $(M,r)=(8,3)$ the **unweighted** sign proportion tends to $K_{-8}/(K_{-4}+K_{-8})=0.53319$ | Paper proof from Wirsing/Selberg–Delange |
| Gap-weighted limits for signed Lambert series; base-2 simple normality of $A_{r,M}(2)-A_{M-r,M}(2)$ | **Open**; reduced exactly; numerics and a conditional prediction |
| Proposition 4.1: $c(p)=+2$ iff $p=x^2+36y^2$, $c(p)=-2$ iff $p=4x^2+9y^2$ ($p\equiv1\pmod{12}$); not a congruence condition (Proposition 4.2) | Elementary proof; Bauer/ring class fields for 4.2; sign rule checked for all 205,753 primes $\le12\cdot2^{20}+1$ |
| Theorem 4.3: $E_b^2$ is not simply normal for $b\ge3$; for all $b$, $f_{0^L}=\rho_+(N;b)+o(1)$ | Paper proof |
| Theorem 4.4: both $0^L$ and $(b-1)^L$ have positive lower frequency in $E_b^2$ | Paper proof granting the Phase 20 eigenform input; the sieve input is Theorem S of [`partitions-carry-and-lemma-s.md`](partitions-carry-and-lemma-s.md) (paper proof) |
| Simple normality of $E_2^2$ in base 2 | **Open**; equivalent to an oriented gap-weighted sign average tending to $\tfrac12$; measured $0.5007$ at $2^{20}$ |
| Theorem 5.2: the sign-augmented automaton gives the exact limit frequency of every word of every length for $\tfrac adE_b$ and $\tfrac adE_b^3$, at rates $O(1/\sqrt N)$ and $O(\log N/\sqrt N)$ | Paper proof; automaton predictions agree with certified digits at every non-exceptional shift |
| Theorem 5.3: if $\operatorname{ord}_d(b)$ is odd (and $d$ is odd, for $E_b^3$), the limit word law is invariant under digit complement; in base 2 such scalings are simply normal | Paper proof; antisymmetry checked for 82 pairs $(b,d)$ |
| Proposition 5.4: no rational scaling is $L$-normal once $b^L>d+1$ | Paper proof |
| Converse of 5.3 in base 2, and existence of a simply normal scaling for $b\ge3$ | **Open**; base-2 equivalence holds for all 2,492 laws with $d<64$ ($E_2$) and $d<46$ ($E_2^3$); no simply normal law $\tfrac adE_b$ for $b\in\{3,4,5,6,7,10\}$, $d\le40$ |

All finite statements come from [`scripts/phase22_flagship_digits.py`](../../scripts/phase22_flagship_digits.py) (§7). No new Lean declaration is claimed here. §6 lists the existing kernel-verified declarations used and recommends new finite cores.

## 0. Oriented tails

Let $z=F_b(a)$ with $a(m)\in\mathbb Z$ and $\sum|a(m)|b^{-m}<\infty$. The integral head and the tail at shift $n$ are

```math
I_n=\sum_{m\le n}a(m)\,b^{n-m}\in\mathbb Z,\qquad \tau_n=b^nz-I_n=\sum_{m>n}a(m)\,b^{n-m}.
```

**Lemma 0.1 (oriented tail).** Let $L\ge1$. If $0\le\tau_n<b^{-L}$, the word at shift $n$ is $0^L$. If $-b^{-L}<\tau_n<0$, the word is $(b-1)^L$.

*Proof.* The word is $\lfloor b^L\{b^nz\}\rfloor$ written with $L$ digits, because $\lfloor b^L\{b^nz\}\rfloor=\lfloor b^{n+L}z\rfloor-b^L\lfloor b^nz\rfloor=\sum_{i=1}^Ld_{n+i}b^{L-i}$ for every real $z$. In the first case $\{b^nz\}=\tau_n\in[0,b^{-L})$. In the second, $\{b^nz\}=1+\tau_n\in(1-b^{-L},1)$. $\square$

The companion note [`simple-normality-and-signed-transfer.md`](simple-normality-and-signed-transfer.md) develops signed coefficient transfer in general. This note uses only Lemmas 0.1–0.4, which are proved here in full.

**Lemma 0.2 (tail-sign reduction).** Put $\rho_+(N)=\frac1N\#\{n<N:\tau_n\ge0\}$ and $B_L(N)=\#\{n<N:|\tau_n|\ge b^{-L}\}$. Then

```math
\bigl|Z_{0^L}(N)-N\rho_+(N)\bigr|\le B_L(N),\qquad \bigl|Z_{(b-1)^L}(N)-N(1-\rho_+(N))\bigr|\le B_L(N),
```

and every other word $w$ has $Z_w(N)\le B_L(N)$. In particular, if $B_L(N)=o(N)$ for each $L$ (the orbit concentrates at $0$), then for every $L$: $f_{0^L}(N)-\rho_+(N)\to0$, $f_{(b-1)^L}(N)-(1-\rho_+(N))\to0$ and $f_w(N)\to0$ for every other $w$. Such a number is not simply normal in any base $b\ge3$, and it is simply normal in base 2 iff $\rho_+(N)\to\frac12$.

*Proof.* Apply Lemma 0.1 at every $n$ with $|\tau_n|<b^{-L}$. The remaining $B_L(N)$ shifts change each count by at most one. $\square$

**Lemma 0.3 (gap decomposition).** Let $0=m_0<m_1<\cdots$ contain the support of $a$ in $[1,\infty)$, with every $m_k$, $k\ge1$, in the support. For $n\in[m_k,m_{k+1})$,

```math
\tau_n=b^{\,n-m_{k+1}}\,V_{k+1},\qquad V_{k+1}=\sum_{m\ge m_{k+1}}a(m)\,b^{\,m_{k+1}-m}=a(m_{k+1})+\tau_{m_{k+1}} .
```

Hence $N\rho_+(N)=\sum_k\bigl|[m_k,m_{k+1})\cap[0,N)\bigr|\cdot\mathbf 1[V_{k+1}\ge0]$, the gap-weighted proportion of nonnegative **oriented values** $V$. If $|\tau_{m_{k+1}}|<1$, then $\operatorname{sgn}V_{k+1}=\operatorname{sgn}a(m_{k+1})$.

*Proof.* The first identity is the definition of $\tau_n$, since there is no support in $(n,m_{k+1})$. For the last claim, $|a(m_{k+1})|\ge1>|\tau_{m_{k+1}}|$. $\square$

The sign of $V_{k+1}$ can differ from the sign of the next coefficient when later terms cluster ("carry flips"). The flip rate is $2.0\%$ of the support of $E_2^2$ below $2^{20}$ in base 2 and $0.3\%$ in base 3 (§4). The exact criterion therefore uses $V$, not $a$.

**Lemma 0.4 (signed Markov tail bound).** For every integer sequence $a$ and all $N,R,L\ge1$,

```math
B_L(N)\le R\,S(N+R-1)+\frac{b^{\,L-R}}{b-1}\,A^*_{|a|}(N,R),\qquad A^*_{|a|}(N,R)=\sum_{m>R}|a(m)|\,b^{-(m-R-N)_+}.
```

If $S(X)\le C_1X(\log X)^{-\kappa}$ and $A(X)\le C_2X(\log X)^\beta$ for $X\ge3$, with $\kappa>0$ and $\beta\ge0$, then $B_L(N)=O_{a,b,L}\bigl(N\log\log N/(\log N)^\kappa\bigr)$; in particular $B_L(N)=o(N)$.

*Proof.* Shifts whose window $(n,n+R]$ meets the support number at most $RS(N+R-1)$. At every other shift $|\tau_n|\le T_n:=\sum_{m>n+R}|a(m)|b^{n-m}$, and exchanging the sums gives $\sum_{n<N}T_n\le b^{-R}A^*_{|a|}(N,R)/(b-1)$ (Lemma 1 of the [theta note](../phase20/theta-and-modular.md#1-coefficient-transfer), applied to $|a|$). Markov's inequality bounds $\#\{n<N:T_n\ge b^{-L}\}$ by $b^L\sum_nT_n$. For the second claim, split $A^*_{|a|}(N,R)\le A(N+R)+\sum_{k\ge1}|a(N+R+k)|b^{-k}$; summation by parts gives $\sum_{k\ge1}|a(N+R+k)|b^{-k}\le(1-b^{-1})\sum_{k\ge1}A(N+R+k)b^{-k}\ll(N+R)\log^\beta(N+R)$. Take $R=L+\lceil(\kappa+\beta)\log_b\log N\rceil$. $\square$

Concentration of $\|b^nz\|$ at $0$ alone does not give $B_L(N)=o(N)$, since $\tau_n$ may sit near a nonzero integer: for $a(m)=-(b-1)$, $m\ge1$, one has $\tau_n=-1$ for all $n$. The proofs below therefore bound $|\tau_n|$ through Lemma 0.4.

## 1. Nonnegative sparse series

**Theorem 1.** Let $a(m)\ge0$ be integers, infinitely many nonzero, and $z=F_b(a)$. For all $N,R,L\ge1$,

```math
N-Z_{0^L}(N)\ \le\ R\,S(N+R-1)+\frac{b^{\,L-R}}{b-1}A^*(N,R),\qquad A^*(N,R)=\sum_{m>R}a(m)\,b^{-(m-R-N)_+}.
```

Consequently:

1. if $S(X)\ll X(\log X)^{-\kappa}$ and $A(X)\ll X(\log X)^\beta$ with $\kappa>0$, $\beta\ge0$, then $1-f_{0^L}(N)=O_{L}\bigl(\log\log N/(\log N)^\kappa\bigr)$;
2. if $a(m)\le2m^{\gamma}$ with $\gamma\ge0$ and the support is contained in $\{t^2\}$, then $1-f_{0^L}(N)\le R(\sqrt{N+R}+1)/N$ for every integer $R$ with $R\ge L+\lceil\log_b(2C_{b,\gamma}(N+R)^{\gamma})\rceil+1$, where $C_{b,\gamma}=\sum_{k\ge1}(1+k)^\gamma b^{-k}$. (Such $R$ exist, since the right side grows like $\gamma\log_bR$.)

In either case $f_{0^L}(N)\to1$ and $f_w(N)\to0$ for every $w\ne0^L$, in every base $b\ge2$. In particular $z$ is not simply normal in any base, and in base 2 its digit 0 has frequency 1.

*Proof.* Shifts whose window $(n,n+R]$ meets the support number at most $RS(N+R-1)$. At every other shift $\tau_n=T_n:=\sum_{m>n+R}a(m)b^{n-m}\ge0$. If $T_n<b^{-L}$, Lemma 0.1 gives the word $0^L$. By Markov's inequality, $\#\{n<N:T_n\ge b^{-L}\}\le b^L\sum_{n<N}T_n\le b^{L-R}A^*(N,R)/(b-1)$, exchanging the sums as in Lemma 1 of the [theta note](../phase20/theta-and-modular.md#1-coefficient-transfer).

For part 1, summation by parts as in Lemma 0.4 (here $|a|=a$) gives $A^*(N,R)\ll N(\log N)^\beta$, with no growth hypothesis on individual coefficients. Take $R=L+\lceil(\kappa+\beta)\log_b\log N\rceil$. The first term is then $\ll N(L+\log\log N)/(\log N)^\kappa$ and the second is $\ll N(\log N)^{-\kappa}$.

For part 2, let $n<N$ have no square in $(n,n+R]$. The squares beyond $n$ are distinct and at distance greater than $R$, and $N+R+k\le(N+R)(1+k)$. Hence

```math
T_n\le2\sum_{i>R}(N+i)^\gamma b^{-i}\le2(N+R)^\gamma C_{b,\gamma}\,b^{-R}<b^{-L}.
```

The exceptional shifts number at most $R(\sqrt{N+R}+1)$. $\square$

**Proposition 1.1 (real characters).** Let $\chi$ be a real character modulo $q$ (values in $\{0,\pm1\}$). Then $(1*\chi)(n)=\sum_{d\mid n}\chi(d)\ge0$ for all $n\ge1$. Explicitly, $(1*\chi)(p^e)$ equals $1$ if $p\mid q$, $e+1$ if $\chi(p)=1$, and $\frac{1+(-1)^e}2$ if $\chi(p)=-1$.

*Proof.* $1*\chi$ is multiplicative, and $(1*\chi)(p^e)=\sum_{i=0}^e\chi(p)^i$ is one of the three listed values, each $\ge0$. A product of nonnegative numbers is nonnegative. $\square$

**Corollary 1.2.** In every base $b\ge2$, including $b=2$, the following satisfy $f_{0^L}(N)\to1$ for every $L$, and so none is simply normal in any base:

| number | rate of $1-f_{0^L}(N)$ | inputs |
| --- | --- | --- |
| $\Theta_Q(1/b)$, every positive definite integral binary $Q$ | $O_{Q,b,L}(\log\log N/\sqrt{\log N})$ | Bernays/Landau support bound, lattice-point mass ([Phase 20, Theorem 5](../phase20/theta-and-modular.md)) |
| $L_\chi(b)=\sum_n(1*\chi)(n)b^{-n}$, every real nonprincipal $\chi$ | $O_{\chi,b,L}(\log\log N/\sqrt{\log N})$ | Proposition 1.1; support exponent $\tfrac12$ ([Phase 21, Theorem 1.3](../phase21/character-q-digamma.md)); $A(X)=L(1,\chi)X+O(\sqrt X)$ |
| $\Theta_3(1/b)$ | $\le(L+2)(\sqrt{N+L+2}+1)/N$ | Theorem 1(2), $\gamma=0$; $2C_{b,0}=2/(b-1)\le2$ allows $R=L+2$ |
| $D^j\Theta_3(1/b)$, $j\ge1$ | $O_{b,j}((L+j\log N)/\sqrt N)$, explicit | Theorem 1(2), $\gamma=j$ |
| $A_{r,M}(b)-A_{M-r,M}(b)$ with $r\mid M$, $M/r\in\{3,4,6,8,12,24\}$ | $O(\log\log N/\sqrt{\log N})$ | Theorem 3.2 |

For $L_\chi$ the mass is linear by the hyperbola method, $\sum_{n\le X}(1*\chi)(n)=\sum_{d\le\sqrt X}\chi(d)\lfloor X/d\rfloor+O(q\sqrt X)$. Class-number-one theta values are special cases, since $r_Q=w\,(1*\chi_\Delta)$.

*Finite data.* The explicit bound of Theorem 1(2) holds on certified digits for $\Theta_3$ and $D^j\Theta_3$, $j=0,1,2$, in bases 2, 3 and 10 at three cutoffs each. For example $f_{0}(32760)=0.99451,0.96978,0.94521$ for $j=0,1,2$ in base 2. For the log-sparse members convergence is slow, as the rate predicts. In base 2, $f_0=0.7527$ for $\Theta_{m^2+n^2}(1/2)$ and $0.8054$ for $\Theta_{m^2+5n^2}(1/2)$ at $N\approx2^{15}$. At the same $N$, $f_0=0.7527$, $0.7865$, $0.8295$, $0.7772$ for $L_{\chi_{-4}}(2)$, $L_{\chi_{-3}}(2)$, $L_{\chi_5}(2)$, $L_{\chi_8}(2)$.

*Where the theorem stops.* $D^j\Theta_Q$ and $D^jL_\chi$ for $j\ge1$ have support $\asymp X/\sqrt{\log X}$ and polynomial mass $X^{1+j}$. The window needed to suppress the tail is $\asymp j\log_bN$, far longer than the typical gap $\asymp\sqrt{\log N}$. This is the width–density wall of [Phase 21, §2.3](../phase21/partitions-and-higher-modular.md). Their digit laws are not claimed.

## 2. Signed quadratic-support families

### 2.1 Coefficients and signs

For $j=0$ the series are $E_b$ and $E_b^3$ themselves; their constant term $1$ at $m=0$ enters only the integral head, so the statements below about $\tau_n$, $n\ge0$, include $j=0$. By Euler and Jacobi, for $j\ge1$,

```math
D^jE_b=\sum_{k\ge1}(-1)^k\Bigl((P_k^-)^j\,b^{-P_k^-}+(P_k^+)^j\,b^{-P_k^+}\Bigr),\qquad
D^jE_b^3=\sum_{k\ge1}(-1)^k(2k+1)T_k^j\,b^{-T_k},
```

and $E_b^2\,DE_b=\tfrac13D(E_b^3)=\sum_{k\ge1}(-1)^k\,\frac{k(k+1)(2k+1)}6\,b^{-T_k}$. The coefficient here is the integer $\sum_{i\le k}i^2$ (this identity is the kernel-verified `DerivativeTransfer.three_mul_eulerSqDerivCoeff`). Since $m^j>0$ for $m\ge1$, every nonzero coefficient has the sign of its pair: $(-1)^k$ at $P_k^\pm$ and $(-1)^k$ at $T_k$. Write the support as $m_1<m_2<\cdots$ with coefficients $c_i$, signs $\sigma_i$ and remainders

```math
R_i=\sum_{l>i}|c_l|\,b^{\,m_i-m_l}.
```

**Lemma 2.1 (dominance).** For each family above, $R_i\to0$. Explicitly, for the pentagonal families with $m_i=P_K^\pm$,

```math
R_i\le\sum_{\Delta\ge K}(m_i+\Delta)^j b^{-\Delta}\le(m_i+K)^j\,(1+C_{b,j})\,b^{-K},\qquad m_i\le2K^2,
```

and similarly for the triangular families with $|c_l|\le(2l+1)T_l^{j}$ (or $T_l^{3/2}$) and gaps $\ge K+1$. Let $i_0(b,j)$ be the least index with $R_i\le\frac12$ for all $i\ge i_0$.

*Proof.* The exponents beyond $m_i$ are distinct and at distance at least the next gap, which is $\ge K$. Also $(m_i+\Delta)\le(m_i+K)(1+\Delta-K)$, and the term $\Delta=K$ contributes the summand $1$ of $1+C_{b,j}=\sum_{r\ge0}(1+r)^jb^{-r}$. The right side is $\ll K^{2j}b^{-K}\to0$. $\square$

**Proposition 2.2 (single-term dominance on each gap).** Let $i\ge i_0$, $n\in[m_{i-1},m_i)$, $r=m_i-n$, and

```math
\ell_i=L+\bigl\lceil\log_b(|c_i|+\tfrac12)\bigr\rceil+1 .
```

If $r\ge\ell_i$, the word at shift $n$ is $0^L$ when $\sigma_i=+1$ and $(b-1)^L$ when $\sigma_i=-1$.

*Proof.* By Lemma 0.3, $\tau_n=b^{-r}(c_i+\theta R_i)$ with $|\theta|\le1$. Since $R_i\le\frac12<|c_i|$, the sign is $\sigma_i$ and $|\tau_n|\le b^{-r}(|c_i|+\frac12)<b^{-L}$. Apply Lemma 0.1. $\square$

So the window of exceptional shifts before $m_i$ has length $\ell_i\le L+j\log_bm_i+O(1)$ for $D^jE_b$, $\le L+(j+\frac12)\log_bm_i+O(1)$ for $D^jE_b^3$, and $\le L+\frac32\log_bm_i+O(1)$ for $E_b^2DE_b$. All of these are at most $L+(j+2)\log_bm_i+O(1)$.

### 2.2 Frequencies

**Theorem 2.** Let $z$ be $D^jE_b$, $D^jE_b^3$ ($j\ge0$) or $E_b^2DE_b$. For every $L\ge1$ and $N\ge2$,

```math
\Bigl|f_{0^L}(N)-\tfrac12\Bigr|+\Bigl|f_{(b-1)^L}(N)-\tfrac12\Bigr|+\sum_{w\ne0^L,(b-1)^L}f_w(N)\ \le\ C_{b,j}\,\frac{L+\log N}{\sqrt N}.
```

Consequently all of them are simply normal in base 2 and not 2-normal ($f_{01},f_{10}\to0$). For $b\ge3$ they are not simply normal: the digits $1,\dots,b-2$ have frequency $O_{b,j}(\log N/\sqrt N)$, and every nonconstant word of length $L$ has frequency $O_{b,j}((L+\log N)/\sqrt N)$.

*Proof.* Let $\Pi_\pm(N)$ count the shifts $n<N$ whose next support point has sign $\pm$. By Proposition 2.2, $|Z_{0^L}(N)-\Pi_+(N)|$ and $|Z_{(b-1)^L}(N)-\Pi_-(N)|$ are at most the number of exceptional shifts, $\sum_{i:\,m_{i-1}<N}\ell_i+m_{i_0}$. This sum includes at most one support point $m_i>N$, and that point is $N+O(\sqrt N)$. The number of support points up to $X$ is $\le\sqrt{24X+1}/3$ (pentagonal) or $\le\sqrt{2X}+1$ (triangular), so this is $O_{b,j}(\sqrt N(L+\log N))$. For $L\ge\sqrt N$ the claim is trivial, since the left side is at most 2.

It remains to show $|\Pi_+(N)-\Pi_-(N)|=O(\sqrt N)$. Pentagonal case: the gaps preceding $P_K^-$ and $P_K^+$ are $2K-1$ and $K$, both with sign $(-1)^K$. So pair $K$ contributes $(-1)^K(3K-1)$, and $|\sum_{K\le K_0}(-1)^K(3K-1)|\le(3K_0+2)/2$; a partial pair adds at most $3K_0+2$. Triangular case: the gap before $T_k$ is $k$ with sign $(-1)^k$, and $|\sum_{k\le k_0}(-1)^kk|\le k_0/2+1$. In both cases $K_0\asymp\sqrt N$. $\square$

For $E_b$ ($j=0$) the coefficients are bounded, $\ell_i=L+O(1)$, and the rate improves to $O(L/\sqrt N)$, recovering Phase 20, Theorem 2. For $E_b^3$ ($j=0$) the coefficients $2k+1$ already grow like $\sqrt{T_k}$, and Theorem 2 recovers Phase 20, Theorem 7(b) with rate $O((L+\log N)/\sqrt N)$.

**Corollary 2.3 (other powers of the radix).** For the same $z$ and every $k\ge2$, the base-$b^k$ digits $0$ and $b^k-1$ each have frequency $\frac12$, and all other digits frequency 0. In particular $D^jE_2$, $D^jE_2^3$ and $E_2^2DE_2$ are simply normal in base 2 but not in base $4,8,16,\dots$.

*Proof.* The base-$b^k$ digit at place $n+1$ is the base-$b$ word of length $k$ at shift $kn$. The positions $\equiv0\pmod k$ in a gap of length $g$ number $g/k+O(1)$. The balance argument of Theorem 2 then applies with an extra $O(1)$ per gap. $\square$

### 2.3 Disjunctivity

**Theorem 2.4.** For every $b\ge2$ and $j\ge1$, $D^jE_b$ is disjunctive: every finite base-$b$ word occurs infinitely often. The same holds for $D^jE_b^3$ ($j\ge0$) and $E_b^2DE_b$. By contrast $E_b$ is not disjunctive (Phase 20, Corollary 1).

*Proof.* **Planted windows.** Let $m=m_i$ with $i\ge i_0$. Suppose the gap $g$ before $m$ satisfies $g\ge\ell$, where $\ell$ is the number of base-$b$ digits of $|c_i|$, and that $|\tau_m|<1$. Then $\lfloor b^mz\rfloor=b^gI_{m_{i-1}}+c_i+\lfloor\tau_m\rfloor$. So the digits at places $m-\ell+1,\dots,m$ form the $\ell$-digit expansion of $(c_i+\epsilon)\bmod b^\ell$, where $\epsilon=0$ if $\tau_m>0$ and $\epsilon=-1$ if $\tau_m<0$. For large $i$ both conditions hold, since $\ell=O(\log m)$ while $g\asymp\sqrt m$, and $\tau_m=b^{-g'}(c_{i+1}+\theta R_{i+1})$ with next gap $g'\gg\log|c_{i+1}|$. The sign of $\tau_m$ is $\sigma_{i+1}$.

**Leading digits.** For $D^jE_b$ take $m=P_K^-$ with $K$ even. Then $\sigma_i=\sigma_{i+1}=+1$, so the window reads $v_K=(P_K^-)^j$ itself. For $D^jE_b^3$ and $E_b^2DE_b$ take $m=T_k$ with $k$ even. Then $\sigma_i=+1$, $\sigma_{i+1}=-1$, and the window reads $v_k=c_k-1>0$. In each case $v_K$ is strictly increasing along the chosen indices, $v_{K+2}/v_K\to1$ and $v_K\to\infty$. The window starts at place $m-\ell+1\ge m_{i-1}+1\ge1$, so it lies among the fractional digits. When $c_k=b^{\ell-1}$ exactly, the window for $v_k=c_k-1$ is the standard expansion of $v_k$ with one leading $0$ prepended, which still contains every subword of that expansion.

Given a word $w$, let $W$ be the integer with base-$b$ digits $1w$. For large $s$, let $v_K$ be the last term below $Wb^s$. Then $Wb^s\le v_{K+2}<Wb^s\,v_{K+2}/v_K<(W+1)b^s$. So $v_{K+2}$ begins with the digits $1w$, and $w$ occurs inside its window. Letting $s\to\infty$ gives infinitely many occurrences. $\square$

*Finite data.* In the first $2^{16}$ binary digits:

| | $E_2$ | $DE_2$ | $D^2E_2$ | $E_2^3$ | $DE_2^3$ | $E_2^2DE_2$ |
| --- | --- | --- | --- | --- | --- | --- |
| distinct words of length 8 (of 256) | 45 | 256 | 256 | 256 | 256 | 256 |
| distinct words of length 10 (of 1024) | 67 | 1016 | 1024 | 896 | 1023 | 1023 |

The script checks every planted window that satisfies the explicit hypotheses: 388 for $DE_2$ and 348 for $D^2E_2$ in base 2, with corresponding counts in bases 3 and 10. It also checks that for $j=1,2$ and every binary word of length $\le6$, some even $K$ has $(P_K^-)^j$ beginning with $1w$.

*Mechanism check.* For all 21 series ($b=2,3,10$; $D^jE$ and $D^jE^3$ with $j=0,1,2$; $E^2DE$) and $L=1,2,3$, every shift outside the windows of Proposition 2.2 reads the predicted constant word on certified digits, and $|Z_{0^L}-N/2|\le\#\text{exceptional}+\frac12|\Pi_+-\Pi_-|$. For instance $DE_2$ has $f_0=0.4982$, $f_1=0.5018$ at $N=65532$, with exceptional share $0.105$ for $L=3$. The finite frequencies of nonconstant words are visibly the $O(\log N/\sqrt N)$ windows, not a limit.

## 3. Signed periodic Lambert series and $q$-digamma reflections

For $M\ge3$ and $1\le r<M/2$ put $w_{r,M}=\mathbf 1_{r\bmod M}-\mathbf 1_{-r\bmod M}$ and $a_{r,M}=1*w_{r,M}=\tau_{r,M}-\tau_{M-r,M}$. By [Phase 21, Theorem 4.1](../phase21/character-q-digamma.md) (kernel-verified as `AntisymmetricLambert.qDigamma_reflection_eq_dirichletSeries`),

```math
\frac{\psi_q(r/M)-\psi_q(1-r/M)}{\log q}=A_{r,M}(b)-A_{M-r,M}(b)=F_b(a_{r,M})\qquad(q=b^{-M}),
```

and $F_b(a_{r,M})\in K_b$, with the orbit concentrating at $0$ ([Phase 21, Theorem 3.2](../phase21/character-q-digamma.md)).

### 3.1 Sign structure

**Proposition 3.1.** Let $g=\gcd(r,M)$, $M'=M/g$ and $r'=r/g$. Then $a_{r,M}(n)=a_{r',M'}(n/g)$ if $g\mid n$, and $a_{r,M}(n)=0$ otherwise. For $\gcd(r,M)=1$,

```math
a_{r,M}(n)=\frac2{\varphi(M)}\sum_{\chi\ \text{odd}}\overline{\chi(r)}\,(1*\chi)(n),
```

the sum running over the odd characters modulo $M$.

*Proof.* $d\equiv\pm r\pmod M$ forces $g\mid d$; write $d=ge$, so $d\equiv\pm r\pmod M$ iff $e\equiv\pm r'\pmod{M'}$. For the character formula, orthogonality gives $\mathbf 1_r(d)-\mathbf 1_{-r}(d)=\frac1{\varphi(M)}\sum_\chi\overline{\chi(r)}(1-\chi(-1))\chi(d)$. This holds for all $d$, both sides vanishing when $\gcd(d,M)>1$. Sum over $d\mid n$. $\square$

**Theorem 3.2 ($r=1$).** $a_{1,M}(n)\ge0$ for all $n$ if and only if the Carmichael exponent $\lambda(M)$ equals 2, that is, $M\in\{3,4,6,8,12,24\}$.

*Proof.* If $\lambda(M)=2$, every character modulo $M$ is real, and Proposition 3.1 with Proposition 1.1 gives $a_{1,M}\ge0$. Suppose $\lambda(M)>2$ and let $u\in G=(\mathbb Z/M)^\times$ have order $h\ge3$. For distinct primes $p_1,\dots,p_s$ with given residues, the divisors of $n=\prod p_i$ correspond to subsets $S$, with residue $\prod_{i\in S}p_i$, so $a_{1,M}(n)=\#\{S:\prod_S p_i\equiv1\}-\#\{S:\prod_S p_i\equiv-1\}$. Dirichlet's theorem supplies primes in any unit class.

*Case A: some $u$ of order $2t\ge4$ has $u^t=-1$.* Take $t+1$ primes $\equiv u$. A subset of size $i$ has residue $u^i$. Since $i\le t+1<2t$, $u^i=1$ only for $i=0$ and $u^i=-1$ only for $i=t$. So $a_{1,M}(n)=1-(t+1)=-t<0$.

*Case B: otherwise.* If $-1\in\langle u\rangle$ for some $u$ of order $h\ge3$, then $-1$ is the unique involution of the cyclic group $\langle u\rangle$, which forces Case A. So $-1\notin\langle u\rangle$ for every $u$ of order $h\ge3$. Fix such a $u$, put $v=-u^{-2}$, and take one prime $q\equiv v$ and three primes $p_1,p_2,p_3\equiv u$. These are distinct primes: $v\equiv u$ would give $-1=u^3\in\langle u\rangle$. A divisor has residue $v^\epsilon u^i=(-1)^\epsilon u^{i-2\epsilon}$ with $\epsilon\in\{0,1\}$ and $0\le i\le3$. It is $1$ iff $\epsilon=0$ and $h\mid i$, giving $i=0$, plus $i=3$ when $h=3$. It is $-1$ iff $\epsilon=1$ and $h\mid i-2$, giving $i=2$ ($\binom32=3$ subsets). So $a_{1,M}(n)=1+[h=3]-3<0$. $\square$

The script constructs these $n$ for every $M\le60$ with $\lambda(M)>2$ and verifies $a_{1,M}(n)<0$. Case B occurs, for example, for $M=15$ ($G\cong C_2\times C_4$, with $n=q\,p_1p_2p_3$ and $q\equiv11$, $p_i\equiv7$). The smallest negative values are $a_{1,5}(28)=-1$ (divisors $\equiv1,2,4,2,4,3$), $a_{1,7}(54)$ and $a_{1,9}(88)$.

**Proposition 3.3 ($r\not\equiv\pm1$).** If $\gcd(r,M)=1$ and $r\not\equiv\pm1$, then $a_{r,M}(p)=+1$ for primes $p\equiv r$ and $-1$ for $p\equiv-r$. So both signs occur on sets of primes of density $1/\varphi(M)$.

**Proposition 3.4 (mass law).** $\sum_{n\le X}a_{r,M}(n)=\frac\pi M\cot\frac{\pi r}M\,X+O(\sqrt X)$.

*Proof.* By the hyperbola method with $W(t)=\sum_{d\le t}w_{r,M}(d)\in\{0,1\}$, the sum is $X\sum_{d\le\sqrt X}w(d)/d+O(\sqrt X)$. Also $\sum_dw(d)/d=\frac1M(\psi(1-\frac rM)-\psi(\frac rM))=\frac\pi M\cot\frac{\pi r}M$. $\square$

The mean is positive for $r<M/2$, but the support has density zero, so this bias says nothing about the frequency of each sign. The script checks the law within $3\sqrt X+3$ at $X=2^{16}$ for all 30 pairs with $M\le12$.

**Classification for $3\le M\le12$, $1\le r<M/2$.**

- *Nonnegative* ($r'=1$, $M'\mid24$): $(3,1),(4,1),(6,1),(6,2),(8,1),(8,2),(9,3),(12,1),(12,2),(12,3),(12,4)$. Theorem 1 applies: $f_{0^L}\to1$ in every base.
- *Signed, $r'=1$, $\lambda(M')>2$*: $(5,1),(7,1),(9,1),(10,1),(10,2),(11,1)$. Negative values are rare at accessible scales (5–11% of the support at $2^{16}$).
- *Signed, real type* ($\lambda(M')=2$, $r'\not\equiv\pm1$): $(8,3)$ and $(12,5)$. Here $2a_{3,8}=1*\chi_{-8}-1*\chi_{-4}$ and $2a_{5,12}=1*\chi'_{-4}-1*\chi'_{-3}$, with the primes 2 and 3 free in the imprimitive characters $\chi'$.
- *Signed, complex type* ($\lambda(M')>2$, $r'\not\equiv\pm1$): all remaining pairs, for example $a_{2,5}=\operatorname{Im}(1*\chi)$ with $\chi(2)=i$. In the same notation $a_{1,5}=\operatorname{Re}(1*\chi)$, which belongs to the previous class.

### 3.2 Digit laws

**Theorem 3.5.** For every $(r,M)$ and every $b\ge2$, with $\rho_+$ and $V$ as in Lemmas 0.2–0.3 for $z=F_b(a_{r,M})$: $f_{0^L}(N)=\rho_+(N)+o(1)$, $f_{(b-1)^L}(N)=1-\rho_+(N)+o(1)$, and $f_w(N)\to0$ for every other $w$ of every length $L$. Hence:

1. $F_b(a_{r,M})$ is not simply normal in any base $b\ge3$;
2. in base 2 it is simply normal iff the oriented gap-weighted proportion $\rho_+(N)$ tends to $\frac12$;
3. in the nonnegative cases $\rho_+\equiv1$, so $f_0\to1$, also in base 2.

*Proof.* By Proposition 3.1, $S_{a_{r,M}}(X)=S_{a_{r',M'}}(X/g)\ll X(\log X)^{-1/\lambda(M')}$ (the support exponent of [Phase 21, Theorem 3.2](../phase21/character-q-digamma.md)), and $|a_{r,M}(n)|\le\tau(n)$ gives $A(X)\ll X\log X$. Lemma 0.4 with $\kappa=1/\lambda(M')$ and $\beta=1$ gives $B_L(N)=O(N\log\log N/(\log N)^{1/\lambda(M')})=o(N)$, and Lemma 0.2 applies. $\square$

**Proposition 3.6 (unweighted sign proportion, real type).** For $(M,r)=(8,3)$,

```math
\frac{\#\{n\le X:a_{3,8}(n)>0\}}{\#\{n\le X:a_{3,8}(n)\ne0\}}\ \longrightarrow\ \frac{K_{-8}}{K_{-4}+K_{-8}}=0.53319\ldots,
```

where $K_\Delta=\lim S_{1*\chi_\Delta}(X)\sqrt{\log X}/X$, so that $K_{-4}=0.7642236\ldots$ (Landau–Ramanujan) and $K_{-8}=0.8728875\ldots$ (integers $x^2+2y^2$). For $(12,5)$ the limit is $K'_{-4}/(K'_{-4}+K'_{-3})=0.51532$, where $K'_{-4}=1.01896$ and $K'_{-3}=0.95836$ are the Wirsing constants of the supports of $1*\chi'$.

*Proof.* The supports of $1*\chi_{-4}$ and $1*\chi_{-8}$ are multiplicative sets of prime density $\frac12$. Their intersection kills the classes $3,5,7\pmod 8$ at odd exponents, so it has prime density $\frac14$ and count $\ll X/(\log X)^{3/4}$ (Halberstam–Richert). Off the intersection, $a_{3,8}=\frac12(1*\chi_{-8})>0$ or $a_{3,8}=-\frac12(1*\chi_{-4})<0$, and $|a_{3,8}|\ge\frac12$ there (in fact $\ge1$, since $a_{3,8}\in\mathbb Z$). By Wirsing's theorem (Selberg–Delange), $S_{1*\chi}(X)\sim K_\chi X/\sqrt{\log X}$ with

```math
K_\chi=\frac1{\sqrt\pi}\Bigl(L(1,\chi)\prod_p c_p\Bigr)^{1/2},\qquad c_p=\begin{cases}(1-p^{-2})^{-1},&\chi(p)=-1,\\(1-p^{-1})^{-1},&\chi(p)=0,\\1,&\chi(p)=1.\end{cases}
```

This follows from $F(s)^2=\zeta(s)L(s,\chi)\prod_pc_p(s)$ for $F(s)=\sum\mathbf 1_{\text{supp}}(n)n^{-s}$. Here $L(1,\chi_{-4})=\pi/4$, $L(1,\chi_{-8})=\pi/(2\sqrt2)$, $L(1,\chi'_{-4})=\pi/3$ and $L(1,\chi'_{-3})=\pi/(2\sqrt3)$. $\square$

The script evaluates the products over $p<2\cdot10^5$ and recovers the Landau–Ramanujan constant to $10^{-5}$.

**What is open, and the exact obstruction.** Theorem 3.5 reduces simple normality in base 2 to the gap-weighted oriented proportion $\rho_+$. Proposition 3.6 controls only the unweighted proportion. The gap weighting asks whether the sign of $a(m)$ correlates with the backward gap to the previous support point. Expanding the gap indicator gives correlations $\sum_m\operatorname{sgn}a(m)\prod_{i\in T}\mathbf 1_{\rm supp}(m-i)$ for sets $T$ of shifts up to the typical gap $(\log N)^{1/\lambda}$. These are multi-point correlations of a sign function with a sparse multiplicative set, beyond current sieve and Matomäki–Radziwiłł technology at this sparsity. Under the decorrelation hypothesis

> **(H$_{\rm gap}$)** the gap-weighted and unweighted sign proportions have the same limit, and carry flips do not change it,

$A_{3,8}(2)-A_{5,8}(2)$ would have binary $f_0\to0.5332$ and would **not** be simply normal in base 2, and $A_{5,12}(2)-A_{7,12}(2)$ would have $f_0\to0.5153$. For the complex types the argument of $(1*\chi)(n)$ is $\frac\pi4(\omega_2(n)-\omega_3(n))$ plus prime-power corrections (for $M=5$). Its expected equidistribution modulo $2\pi$ (Delange) gives the unweighted limit $\frac12$, at a $\log\log$ rate that is invisible at accessible scales. That limit is not proved here.

*Finite data* ($X=2^{16}$; $\rho_+$ from oriented tails in base 2; $f_0$ from certified binary digits):

| $(M,r)$ | type | support/$X$ | negative/support | unweighted $+$ | $\rho_+$ | $f_0$ |
| --- | --- | --- | --- | --- | --- | --- |
| (3,1), (4,1), (8,1), (12,1) | nonneg | 0.21–0.53 | 0 | 1 | 1 | 0.79, 0.76, 0.61, 0.56 |
| (5,1) | $r'=1$ signed | 0.494 | 0.107 | 0.893 | 0.913 | 0.565 |
| (7,1) | $r'=1$ signed | 0.579 | 0.081 | 0.919 | 0.943 | 0.520 |
| (5,2) | complex | 0.457 | 0.405 | 0.595 | 0.655 | 0.563 |
| (7,3) | complex | 0.501 | 0.405 | 0.595 | 0.600 | 0.532 |
| (11,5) | complex | 0.537 | 0.458 | 0.542 | 0.561 | 0.529 |
| (8,3) | real | 0.377 | 0.443 | 0.557 | 0.596 | 0.528 |
| (12,5) | real | 0.420 | 0.472 | 0.529 | 0.547 | 0.512 |

At this scale the support still has density $0.2$–$0.7$, so most shifts have large tails. That is why the measured $f_0$ is far from $\rho_+$ even in the nonnegative cases ($f_0(L_{\chi_{-3}})=0.79$, not $1$). These values neither support nor refute any limit statement.

**General odd periodic weights.** Let $w\not\equiv0$ be an odd $M$-periodic integer weight. Primes $p\equiv-1\pmod M$ kill $1*w$ at odd exponents ([Phase 21, Theorem 3.2](../phase21/character-q-digamma.md)), so $S_{1*w}(X)\ll X(\log X)^{-1/\varphi(M)}$, and $|1*w|\le\max|w|\cdot\tau$ gives $A(X)\ll X\log X$. Lemma 0.4 therefore applies, and Theorem 3.5(1)–(2) hold verbatim for $F_b(1*w)$. The sign structure follows from Proposition 3.1 applied on each gcd stratum: the part of $w$ supported on $\gcd(d,M)=g$ is an odd weight modulo $M/g$ in $d/g$, with its own character expansion.

## 4. Euler's square

Write $E(q)^2=\sum a_2(n)q^n$ and $\eta(12\tau)^2=\sum_mc(m)q^m$, so that $a_2(n)=c(12n+1)$ and ([Phase 20, §5](../phase20/euler-product.md#5-the-square-of-eulers-product))

```math
c(m)=\sum_{\substack{m_1,m_2\ge1\\ m_1^2+m_2^2=2m}}\chi_{12}(m_1)\chi_{12}(m_2).
```

**Proposition 4.1 (sign rule, elementary).** Let $p\equiv1\pmod{12}$ be prime and write $p=u^2+v^2$ with $u$ odd and $v$ even. Exactly one of $u,v$ is divisible by 3, and

```math
c(p)=\begin{cases}+2,&3\mid v\quad(p=x^2+36y^2),\\-2,&3\mid u\quad(p=4x^2+9y^2).\end{cases}
```

*Proof.* $p\equiv1\pmod3$ forces exactly one of $u,v$ to be $\equiv0\pmod3$. The representations $2p=m_1^2+m_2^2$ with $m_i\ge1$ are $(u+v,|u-v|)$ and its swap, from $2p=(u+v)^2+(u-v)^2$ and the uniqueness of $p=u^2+v^2$. Since $\chi_{12}$ is even and completely multiplicative, $c(p)=2\chi_{12}(u^2-v^2)$, and $\chi_{12}=\chi_{-4}\chi_{-3}$. Now $u^2-v^2\equiv1\pmod4$, so $\chi_{-4}=1$. Modulo 3, $u^2-v^2\equiv1$ if $3\mid v$ and $\equiv-1$ if $3\mid u$. $\square$

Combined with Phase 20, Theorem 6(a), the sign of $a_2(n)$ is

```math
\operatorname{sgn}a_2(n)=\prod_{p\equiv1\,(12)}\epsilon_p^{\,v_p(12n+1)}\prod_{p\equiv5\,(12)}(-1)^{v_p(12n+1)/2}\qquad(a_2(n)\ne0),
```

with $\epsilon_p=+1$ iff $p=x^2+36y^2$. The squares of primes $\equiv5\pmod{12}$ flip the sign; for example $a_2(2)=c(25)=-1$. The script checks Proposition 4.1 for all 205,753 primes $p\equiv1\pmod{12}$ up to $12\cdot2^{20}+1$ (49.95% have $c(p)=+2$), and the full multiplicative formula for every $n\le2^{16}$.

**Proposition 4.2 (not a congruence condition).** There is no modulus $Q$ such that $\epsilon_p$ depends only on $p\bmod Q$ for all large $p\equiv1\pmod{12}$.

*Proof.* The reduced forms of discriminant $-144$ are $x^2+36y^2$, $4x^2+9y^2$ and $5x^2\pm4xy+8y^2$. The last two are inverse and distinct, so $\mathrm{Cl}(-144)\cong C_4$. By Cox, *Primes of the form $x^2+ny^2$*, Theorem 9.4, $p=x^2+36y^2$ iff $p$ splits completely in the ring class field $H$ of $\mathbb Z[6i]$, and $\mathrm{Gal}(H/\mathbb Q)\cong C_4\rtimes C_2=D_4$ is nonabelian (Cox, Lemma 9.3). Since $H\supseteq\mathbb Q(i,\sqrt3)$, every prime splitting completely in $H$ is $\equiv1\pmod{12}$. Suppose $\epsilon_p$ depended only on $p\bmod Q$ for large $p\equiv1\pmod{12}$, and put $Q'=\operatorname{lcm}(12,Q)$. Then there is a set $S\subseteq(\mathbb Z/Q'\mathbb Z)^\times$ such that, for all large primes $p$, $p$ splits completely in $H$ iff $p\bmod Q'\in S$. The compositum $H\,\mathbb Q(\zeta_{Q'})$ is a finite Galois extension of $\mathbb Q$, so infinitely many primes split completely in it. Each such prime splits completely in $H$ and is $\equiv1\pmod{Q'}$, so $1\in S$. Hence every large prime $p\equiv1\pmod{Q'}$ splits completely in $H$; that is, up to finitely many primes, $\operatorname{Spl}(\mathbb Q(\zeta_{Q'}))\subseteq\operatorname{Spl}(H)$. By Bauer's theorem (Neukirch, *Algebraic Number Theory*, VII.13.9–13.10), $H\subseteq\mathbb Q(\zeta_{Q'})$. This is impossible: $\mathrm{Gal}(H/\mathbb Q)\cong D_4$ is nonabelian, while every subfield of $\mathbb Q(\zeta_{Q'})$ is abelian over $\mathbb Q$. $\square$

The script confirms that, for each $Q\in\{24,48,72,144,288,432,720,1440,5040,10080\}$, every class $p\equiv1\pmod{12}$ modulo $Q$ contains primes of both signs.

**Theorem 4.3.** For every $b\ge2$ and $L\ge1$, $f_{0^L}(N;E_b^2)=\rho_+(N;b)+o(1)$, $f_{(b-1)^L}(N;E_b^2)=1-\rho_+(N;b)+o(1)$, and all other words have frequency $o(1)$. Hence $E_b^2$ is **not simply normal in any base $b\ge3$**. In base 2 it is simply normal iff $\rho_+(N;2)\to\frac12$, where by Lemma 0.3

```math
\rho_+(N;2)=\frac1N\sum_{m\in\mathrm{supp}\,a_2,\ m\ge1}\bigl|[m-G_-(m),m)\cap[0,N)\bigr|\cdot\mathbf 1\Bigl[\sum_{m'\ge m}a_2(m')\,2^{\,m-m'}>0\Bigr]
```

and $G_-(m)$ is the backward gap at $m$. The strict inequality agrees with the $\ge0$ of Lemma 0.3 because $E_2^2$ is irrational (indeed transcendental, Phase 20, §4), so no oriented value vanishes.

*Proof.* Elementarily, $S(X)\ll X/\sqrt{\log X}$ (Landau) and $A_2(X)=O(X)$ (pair count), by Phase 20, Proposition 5. Lemma 0.4 with $\kappa=\frac12$, $\beta=0$ gives $B_L(N)=O(N\log\log N/\sqrt{\log N})$. Apply Lemmas 0.2–0.3. $\square$

**Theorem 4.4 (both constant words have positive lower frequency).** Grant Phase 20, Theorem 6(a). Use the uniform sieve bound Lemma S of [Phase 21, §4.2](../phase21/euler-scalings-and-reciprocals.md#42-non-membership-for-every-denominator) in the form of Theorem S of [`partitions-carry-and-lemma-s.md`](partitions-carry-and-lemma-s.md) (§1, a complete paper proof): $\sum_{h\le H}\#\{n\le N:a_2(n)a_2(n+h)\ne0\}\le C_0HN/(\log N)^{3/2}$ for $1\le H\le N$. Then there is $c>0$ such that for every $b\ge2$ and $L\ge1$,

```math
c\le\liminf_{N\to\infty}f_{0^L}(N;E_b^2)\le\limsup_{N\to\infty}f_{0^L}(N;E_b^2)\le1-c .
```

*Proof.* Let $U=\mathrm{supp}\,a_2$ and $s=\operatorname{sgn}a_2$ on $U$. The function $f(m)=\operatorname{sgn}c(m)$ ($f=0$ off the support) is real multiplicative with $|f|\le g$, where $g$ is the multiplicative indicator of $\{12n+1:n\in U\}$. Here $\sum_{p\le x}g(p)\log p\sim x/4$, and $\sum_p(g(p)-f(p))/p=\sum_{p\equiv1\,(12),\ \epsilon_p=-1}2/p=\infty$, since the primes with $\epsilon_p=-1$ have density $\frac18$ (Chebotarev in $H$). By Wirsing's mean-value theorem for real multiplicative $|f|\le g$ with $\sum_{p\le x}g(p)\log p\sim\tau x$, $\tau>0$ (Wirsing, *Acta Math. Acad. Sci. Hungar.* 18 (1967)), $\sum_{n\le N,\,n\in U}s(n)=o(S(N))$, so

```math
\#\{n\in U\cap(N/2,N]:s(n)=+1\}=(\tfrac12+o(1))\,(S(N)-S(N/2))\ \ge\ \kappa'\frac N{(\log N)^{3/4}}
```

for large $N$, using $S(N)\sim C_\eta N/(\log N)^{3/4}$.

Let $H=\lfloor\eta(\log N)^{3/4}\rfloor$. By Theorem S, at most $2C_0HN/(\log N)^{3/2}\le\frac18\kappa'N/(\log N)^{3/4}$ points of $U\cap(N/2,N]$ have another support point within distance $H$, once $\eta\le\kappa'/(16C_0)$. By Markov's inequality, $o(N/(\log N)^{3/4})$ points have $|a_2(n)|>(\log N)^{1/3}$, and $O(Nb^{-H})$ isolated points $m\le N$ have $|\tau_m|\ge1$: for isolated $m$, $\tau_m=\sum_{k>H}a_2(m+k)b^{-k}$, and Markov's inequality applies to $\sum_{m\le N}\sum_{k>H}|a_2(m+k)|b^{-k}\le\sum_{k>H}A_2(N+k)b^{-k}\ll Nb^{-H}$. Each remaining positive point $m$ has $\operatorname{sgn}V(m)=+1$ (Lemma 0.3). By Lemma 0.1 it makes the word $0^L$ at the shifts $n\in[m-H,m-r_0]$, where $r_0=L+\log_b(2(\log N)^{1/3})+1$. These sets of shifts are disjoint, so

```math
Z_{0^L}(N)\ \ge\ (H-r_0)\cdot\tfrac14\kappa'\frac N{(\log N)^{3/4}}\ \ge\ \frac{\eta\kappa'}5\,N
```

for large $N$. The same argument with $s=-1$ bounds $Z_{(b-1)^L}(N)$, and $Z_{0^L}+Z_{(b-1)^L}\le N$. $\square$

**Simple normality of $E_2^2$ in base 2 is open.** By Theorem 4.3 it is equivalent to $\rho_+(N;2)\to\frac12$, which is a statement about the correlation of the non-congruence sign $s(m)$ with the gap structure of $U$. The unweighted analogue holds by Wirsing. The weighted version needs correlations $\sum_ms(m)\prod_{i\in T}\mathbf 1_U(m-i)$ for $|T|$ up to $(\log N)^{3/4}$; this is the obstruction described in §3.2. Heuristically, $s(m)$ is driven by Chebotarev classes of the primes $\equiv1\pmod{12}$ in $H$, while membership of $m-i$ in $U$ is driven by the parity of exponents of the primes $\not\equiv1\pmod{12}$. No interaction is expected, and (H$_{\rm gap}$) predicts the limit $\frac12$.

*Finite data* (support of $a_2$ computed by exact convolution to $2^{20}$):

| $N$ | base | $\rho_+$ (oriented) | gap-weighted $\operatorname{sgn}a_2$ | unweighted $+$ | carry flips |
| --- | --- | --- | --- | --- | --- |
| $2^{14}$ | 2 | 0.50507 | 0.50146 | 0.50031 | 1.93% |
| $2^{16}$ | 2 | 0.50249 | 0.50038 | 0.50006 | 2.07% |
| $2^{18}$ | 2 | 0.50179 | 0.50174 | 0.50009 | 2.04% |
| $2^{20}-4000$ | 2 | 0.50068 | 0.50088 | 0.50002 | 1.95% |
| $2^{20}-4000$ | 3 | 0.50113 | 0.50088 | 0.50002 | 0.31% |

The certified binary digits give $f_0(2^{18})=0.50170$, against $\rho_+=0.50179$. The data are consistent with $\frac12$. At $2^{20}$ the support still has density $0.307$, and only $0.35\%$ of support points are isolated by $8$ on both sides, so the asymptotic regime of Theorem 4.4 is far away.

## 5. Rational scalings $\tfrac adE_b$ and $\tfrac adE_b^3$

Let $d\ge2$ with $\gcd(d,b)=1$, $\gcd(a,d)=1$, $a\ne0$, and $t=\operatorname{ord}_d(b)$. Let $z\in\{E_b,E_b^3\}$ with insertion positions $p_j$ and coefficients $c_j$ ($p_0=0$, $c_0=1$). Then $b^n\frac adz=\frac a dI_n+\frac a d\tau_n$, and the **atom** at shift $n$ is $\alpha_n=aI_n\bmod d$. This is the automaton of [Phase 21, Theorem D1.1](../phase21/euler-scalings-and-reciprocals.md), on states $(k\bmod\operatorname{lcm}(2,t),u)$ for $E_b$ and $(k\bmod\operatorname{lcm}(t,2,d),v)$ for $E_b^3$. Its pure periodicity is kernel-verified as `NormalReciprocalCore.eulerAutomaton_purely_periodic`.

**Lemma 5.1 (nonzero atoms are interior).** For $1\le c\le d-1$ and $L\ge1$, $c/d$ is at distance $\ge1/(db^L)$ from $b^{-L}\mathbb Z$. So $c/d$ lies in the interior of a unique length-$L$ cylinder, labelled by $\pi_L(c/d)$, the first $L$ digits of the purely periodic expansion of $c/d$. Only the atom $0$ lies on a cylinder boundary.

*Proof.* $|c/d-k/b^L|=|cb^L-kd|/(db^L)$, and $cb^L-kd\ne0$ because $d\nmid cb^L$, as $\gcd(d,b)=1$ and $d\nmid c$. $\square$

**Theorem 5.2 (signed automaton).** Augment each run of the automaton with the sign $\sigma\in\{\pm1\}$ of the insertion that ends it. For $E_b$: the run after $P_k^-$ (length $k$, weight class $\frac13$) has $\sigma=(-1)^k$, and the run after $P_k^+$ (length $2k+1$, weight $\frac23$) has $\sigma=(-1)^{k+1}$. For $E_b^3$: the run after $T_k$ (length $k+1$) has $\sigma=(-1)^{k+1}$. Let $P$ be the period, $\nu(u)$ the uniform law on the orbit $\{ub^i\}$, and let a run class with start residue $u$ and sign $\sigma$ carry weight $\omega(u,\sigma)$: the limiting share of its runs. Define, for every word $w$ of length $L$,

```math
f_w=\sum_{(u,\sigma)}\omega(u,\sigma)\,\frac1{|O(u)|}\sum_{x\in O(u)}\mathbf 1\bigl[\mathrm{word}(ax\bmod d,\ \sigma\operatorname{sgn}a)=w\bigr],
```

where $\mathrm{word}(c,\cdot)=\pi_L(c/d)$ for $c\ne0$, $\mathrm{word}(0,+)=0^L$ and $\mathrm{word}(0,-)=(b-1)^L$. Then

```math
\max_{|w|=L}\bigl|f_w(N)-f_w\bigr|=\begin{cases}O_{b,d,a,L}(1/\sqrt N),&z=E_b,\\ O_{b,d,a,L}(\log N/\sqrt N),&z=E_b^3.\end{cases}
```

The limits $f_w$ are rational and computable for every $w$ of every length.

*Proof.* Let $n$ lie in the run ending at the insertion $p$ with coefficient $c$, at distance $r=p-n$, and assume the remainder after $p$ is $\le\frac12$ (all but finitely many insertions). Then $a\tau_n=ab^{-r}(c+\theta/2)$ has sign $\sigma\operatorname{sgn}a$ and modulus $<b^{-L}$ as soon as $r\ge\ell:=L+\lceil\log_b(|a|(|c|+\frac12))\rceil+1$. If $\alpha_n\ne0$, then $|x_n-\alpha_n/d|=|a\tau_n|/d<1/(db^L)$, and Lemma 5.1 puts $x_n$ in the cylinder $\pi_L(\alpha_n/d)$. If $\alpha_n=0$, then $x_n=\{a\tau_n/d\}$ lies in $[0,b^{-L})$ or $(1-b^{-L},1)$ according to the sign, which is Lemma 0.1.

The exceptional shifts number $\sum_p\ell=O(\sqrt N(L+\log|a|))$ for $E_b$. For $E_b^3$, $|c|\le2\sqrt{2N}+3$, so the count is $O(\sqrt N(L+\log(|a|N)))$. On the good shifts, the word is determined by the pair $(\alpha_n,\sigma)$. Inside a run $\alpha_n$ moves along $u\mapsto ub$, while $\sigma$ is constant; by Lemma 1.2 of Phase 21 the visit counts of each run differ from its length times $\nu$ by at most $t$. Runs of one type have lengths $k$, $2k+1$ or $k+1$, the same linear function of $k$ for every class, so every class $k\bmod P$ receives its share up to $O(P/\sqrt N)$ (Phase 21, proof of Theorem D1.1). $\square$

**Corollary 5.2.1 (digit law).** With $w_c$ the limit mass of the nonzero atom $c/d$ and $w_0^\pm$ the masses of zero-atom runs with $\sigma\operatorname{sgn}a=\pm1$,

```math
f_e=\sum_{c\ne0:\ \lfloor bc/d\rfloor=e}w_c\;+\;w_0^+\,[e=0]\;+\;w_0^-\,[e=b-1]\qquad(0\le e<b),
```

and $\tfrac adz$ is simply normal in base $b$ iff $f_e=1/b$ for all $e$. Moreover the mean digit satisfies $\sum_e e\,f_e=(b-1)\bigl(w_0^-+\sum_{c\ne0}w_c\,c/d\bigr)$. In base 2 this means $f_1$ is the barycentre of the limit law with the negative half of the zero atom placed at $1$.

*Proof.* Only the last claim needs proof. The atomic law restricted to the nonzero atoms is $\times b$-invariant ($0$ is fixed), so $\sum_cw_c\lfloor bc/d\rfloor=\sum_cw_c(bc/d-\{bc/d\})=(b-1)\sum_cw_cc/d$. The zero atom contributes $(b-1)w_0^-$. $\square$

**Theorem 5.3 (odd order: complement symmetry).** Suppose $t=\operatorname{ord}_d(b)$ is odd. Then for $\tfrac adE_b$, and for $\tfrac adE_b^3$ when moreover $d$ is odd, the limit word law is invariant under the complement $w\mapsto\bar w$, $\bar w_i=b-1-w_i$. In particular, **in base 2, $\tfrac adE_2$ and $\tfrac adE_2^3$ are simply normal whenever $\operatorname{ord}_d(2)$ is odd**, for every nonzero numerator $a$ coprime to $d$.

*Proof.* *Euler.* Write $P(j)=j(3j-1)/2$ for $j\in\mathbb Z$, so that the generalized pentagonal numbers $\le P_k^+=P(-k)$ are the $P(j)$, $-k\le j\le k$. Then

```math
u_k^+\equiv I_{P_k^+}\equiv b^{P_k^+}A(k),\qquad A(k)=\sum_{j=-k}^{k}\mathrm{tm}(j),\qquad \mathrm{tm}(j)=(-1)^jb^{-P(j)}\pmod d .
```

Since $t$ is odd, $P(j+t)-P(j)=t\,(6j+3t-1)/2\equiv0\pmod t$, so $\mathrm{tm}(j+t)=-\mathrm{tm}(j)$. Any $2t$ consecutive terms therefore sum to $0$, and

```math
A(k+t)=\sum_{j=-k-t}^{k-t}\mathrm{tm}(j)+\sum_{j=k-t+1}^{k+t}\mathrm{tm}(j)=\sum_{i=-k}^{k}\mathrm{tm}(i-t)+0=-A(k).
```

Also $b^{P_{k+t}^+}=b^{P_k^+}$. Hence $u_{k+t}^+=-u_k^+$, and likewise $u_{k+t}^-=-u_k^-$ (sum over $-(k-1)\le j\le k$). The run signs $(-1)^k$ and $(-1)^{k+1}$ flip under $k\mapsto k+t$. So the class $k+t$ carries the negated atoms and the flipped zero-split. The map $x\mapsto-x$ sends $\pi_L(c/d)$ to $\overline{\pi_L(c/d)}$ (the expansion of $(d-c)/d$ is the digitwise complement), and it swaps $0^L$ with $(b-1)^L$. Classes $k$ and $k+t$ have asymptotically equal weight.

*Cube.* Let $T=\operatorname{lcm}(t,d)$, which is odd, and $\mathrm{tm}(i)=(-1)^i(2i+1)b^{-T_i}\bmod d$, so $v_k=b^{T_k}\sum_{i=0}^k\mathrm{tm}(i)$. We have $T_{i+T}-T_i=T(2i+T+1)/2\equiv0\pmod t$, $2(i+T)+1\equiv2i+1\pmod d$ and $(-1)^T=-1$, so $\mathrm{tm}(i+T)=-\mathrm{tm}(i)$. The involution $i\mapsto T-1-i$ has $T_{T-1-i}-T_i=T(T-2i-1)/2\equiv0\pmod t$, coefficient $2T-2i-1\equiv-(2i+1)\pmod d$ and the same sign, so $\mathrm{tm}(T-1-i)=-\mathrm{tm}(i)$. Hence $\sum_{i<T}\mathrm{tm}(i)$ equals its own negative, and is $0$ since $d$ is odd. Then $\sum_{i\le k+T}\mathrm{tm}(i)=0+\sum_{i\le k}\mathrm{tm}(i+T)=-\sum_{i\le k}\mathrm{tm}(i)$, so $v_{k+T}=-v_k$ with flipped sign $(-1)^{k+T+1}$. Conclude as before. In base 2 the complement of the word $0$ is $1$, so $f_0=f_1=\frac12$. $\square$

The script verifies $u_{k+t}=-u_k$ over a full period, $v_{k+T}=-v_k$, and complement symmetry for $L=1,2,3$ and several $a$, for all 82 pairs $(b,d)$ with $b\in\{2,3,4,5,7,10\}$, $d<80$ and $t$ odd.

**Proposition 5.4 (no higher normality).** At most $d+1$ words of length $L$ have positive limit frequency: the words $\pi_L(c/d)$, $c\ne0$, together with $0^L$ and $(b-1)^L$. Hence $\tfrac adE_b$ and $\tfrac adE_b^3$ are not $L$-normal for any $L>\log_b(d+1)$, and never normal. For $b\ge3$, simple normality forces each cylinder $[e/b,(e+1)/b)$, $1\le e\le b-2$, to contain nonzero atoms of total mass exactly $1/b$.

**Worked cases (exact laws).** In particular $\tfrac12E_3$ and $\tfrac12E_3^3$ are not simply normal in base 3.

| number | atoms (mass) | $w_0^+,w_0^-$ | $f_0,f_1,\dots$ | simply normal |
| --- | --- | --- | --- | --- |
| $\tfrac13E_2$ | $0(\tfrac16)$, $\tfrac13(\tfrac5{12})$, $\tfrac23(\tfrac5{12})$ | $\tfrac16,0$ (zero runs follow $P_k^-$, $k$ even, next sign $+$) | $\tfrac7{12},\tfrac5{12}$ | no |
| $\tfrac17E_2$ | $0(\tfrac19)$, each unit $\tfrac4{27}$ | $\tfrac1{18},\tfrac1{18}$ | $\tfrac12,\tfrac12$; $f_{00}=f_{11}=\tfrac{11}{54}$, $f_{01}=f_{10}=\tfrac8{27}$ | **yes** (not 2-normal) |
| $\tfrac17E_2^3$ | uniform | $\tfrac1{14},\tfrac1{14}$ | $\tfrac12,\tfrac12$; $f_{00}=\tfrac3{14}$, $f_{01}=\tfrac27$ | **yes** |
| $\tfrac1{23}E_2$ | — | $\tfrac1{22},\tfrac1{22}$ | $\tfrac12,\tfrac12$; $f_{00}=\tfrac{61}{242}$, $f_{01}=\tfrac{30}{121}$ | **yes** |
| $\tfrac12E_3$ | $0(\tfrac13)$, $\tfrac12(\tfrac23)$ | $\tfrac16,\tfrac16$ | $\tfrac16,\tfrac23,\tfrac16$ | no |
| $\tfrac12E_3^3$ | $0(\tfrac12)$, $\tfrac12(\tfrac12)$ | $\tfrac12,0$ (parity flips at each odd coefficient; zero runs follow odd $k$, next sign $+$) | $\tfrac12,\tfrac12,0$ | no |
| $\tfrac14E_3$ | $\tfrac16,\tfrac13,\tfrac16,\tfrac13$ | $\tfrac16,0$ | $\tfrac12,\tfrac16,\tfrac13$ | no |
| $\tfrac13E_{10}$ | uniform | $\tfrac16,\tfrac16$ | $f_0=f_9=\tfrac16$, $f_3=f_6=\tfrac13$ | no |

For $\tfrac12E_3$ the order $t=\operatorname{ord}_2(3)=1$ is odd, and the law is complement-symmetric as Theorem 5.3 predicts. Its middle digit has mass $\tfrac23$ because $\tfrac12=0.111\ldots_3$. For $\tfrac12E_3^3$ ($d$ even) the symmetry fails: every zero run is followed by a positive insertion.

**Catalogue in base 2 and the converse.** For all 2,492 laws $\tfrac adE_2$ with odd $d<64$ and $\tfrac adE_2^3$ with odd $d<46$ (all $a$, both signs), simple normality in base 2 holds **iff** $\operatorname{ord}_d(2)$ is odd. In that range the simply normal denominators are $d\in\{7,23,31,47,49\}$ for $E_2$ and $d\in\{7,23,31\}$ for $E_2^3$. None of these laws is 2-normal. Theorem 5.3 proves "if". **Conjecture 5.5.** "Only if" holds for all odd $d$. In every even-order case of the catalogue the zero-atom split is unbalanced, $w_0^+\ne w_0^-$, in various ways: $(w_0^+,w_0^-)=(\tfrac16,0)$ for $\tfrac13E_2$, $(\tfrac1{36},\tfrac1{18})$ for $\tfrac1{13}E_2$ and $(\tfrac1{140},\tfrac1{70})$ for $\tfrac1{35}E_2^3$. Replacing $a$ by $-a$ swaps $w_0^+$ and $w_0^-$. No proof is offered.

**Other radices.** Among 3,974 laws of $\tfrac adE_b$ with $b\in\{3,4,5,6,7,10\}$, $d\le40$, none is simply normal in base $b$. Whether some rational scaling of $E_b$ or $E_b^3$ is simply normal in a base $b\ge3$ is **open**.

**Certified agreement.** In 12 cases, $\tfrac adz$ was compared with the prediction on certified digits for $L=1,2,3$ at $N=2^{16}$ (base 2) or $2^{14}$. The cases are $z=E_b$ with $(b,d,a)=(2,3,1),(2,7,1),(2,7,3),(2,5,-2),(3,2,1),(3,4,1),(10,3,1)$, and $z=E_b^3$ with $(2,3,1),(2,7,1),(3,2,\pm1),(3,4,5)$. Every shift outside the windows of Theorem 5.2 reads exactly the word predicted from $(\alpha_n,\sigma)$. The largest $|f_w(N)-f_w|$ is $0.0008$ ($L=1$) and $0.0071$ ($L=3$) for $\tfrac13E_2$. Over all twelve cases it ranges from $0.00004$ ($L=1$, $\tfrac37E_2$) to $0.035$ ($L=3$, $\tfrac54E_3^3$), always within the explicit bound.

## 6. Lean status and recommended finite cores

**Kernel-verified declarations used here** (existing modules):

- `Phase18Synthetic.discrepancy_deficit_le` and `CoefficientTransfer.finite_sparse_mass_transfer`: the transfer bound behind Theorems 1 and 3.5;
- `DerivativeTransfer.derivCoeff_supportCount_le` and `three_mul_eulerSqDerivCoeff`: derivative coefficients and $3\,\mathrm{coeff}(E^2DE)=\mathrm{coeff}(D E^3)$;
- `AntisymmetricLambert.residueLambert_sub_eq_coeffSeries` and `qDigamma_reflection_eq_dirichletSeries`: the identification of the reflection value with $F_b(a_{r,M})$;
- `AntisymmetricLambert.dirichletOneConv_eq_zero_of_odd_padicVal`: the sparsity input;
- `NormalReciprocalCore.eulerAutomatonStep_bijective` and `eulerAutomaton_purely_periodic`: periodicity of the automaton in §5.

**Recommended new targets** (statements only; not written or checked):

```lean
namespace NormalityChecker.FlagshipDigits

/-- Lemma 0.1: a small nonnegative fractional part forces `L` zero digits. -/
theorem digits_eq_zero_of_fract_lt {b L : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (h : Int.fract x < ((b : ℝ) ^ L)⁻¹) :
    ⌊(b : ℝ) ^ L * Int.fract x⌋ = 0

/-- Lemma 0.1, negative side: the word is `(b-1)^L`. -/
theorem digits_eq_top_of_fract_gt {b L : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (h : 1 - ((b : ℝ) ^ L)⁻¹ < Int.fract x) :
    ⌊(b : ℝ) ^ L * Int.fract x⌋ = (b : ℤ) ^ L - 1

/-- Proposition 1.1. -/
theorem sum_divisors_realChar_nonneg {q : ℕ} (χ : DirichletCharacter ℤ q)
    (hχ : ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1) (n : ℕ) :
    0 ≤ ∑ d ∈ n.divisors, χ d

/-- Lemma 5.1: nonzero atoms are strictly inside `b`-adic cylinders. -/
theorem atom_ne_grid {b d c L : ℕ} (hcop : Nat.Coprime d b) (hc0 : 0 < c) (hcd : c < d)
    (k : ℤ) : (c : ℤ) * b ^ L ≠ k * d

/-- Theorem 5.3, Euler part: antisymmetry of the pentagonal head sum for odd order. -/
theorem pentHeadSum_add_order {b d : ℕ} [NeZero d] (hcop : Nat.Coprime b d)
    (hodd : Odd (orderOf (b : ZMod d))) (k : ℕ) :
    pentHeadSum b d (k + orderOf (b : ZMod d)) = - pentHeadSum b d k

/-- Proposition 4.1, finite core: `χ₁₂(u² - v²)` for `u` odd, `v` even, exactly one divisible by 3. -/
theorem chi12_sq_sub_sq (u v : ZMod 12) (hu : u.val % 2 = 1) (hv : v.val % 2 = 0)
    (h3 : Xor' (u.val % 3 = 0) (v.val % 3 = 0)) :
    chi12 (u ^ 2 - v ^ 2) = if v.val % 3 = 0 then 1 else -1

/-- Theorem 2, sign balance of the pentagonal gaps. -/
theorem abs_sum_alt_pent_gaps_le (K : ℕ) :
    |∑ k ∈ Finset.Icc 1 K, (-1 : ℤ) ^ k * (3 * k - 1)| ≤ (3 * K + 2) / 2
```

`pentHeadSum b d k` denotes $\sum_{-k\le j\le k}(-1)^jb^{-P(j)}$ in `ZMod d`, and `chi12` is the Kronecker symbol $(12/\cdot)$ on `ZMod 12`; both are to be defined. The last three are decidable finite statements. Theorem 3.2 also has a finite core: the subset-count identities of Cases A and B in a finite abelian group.

## 7. Verification record

```sh
python -B scripts/phase22_flagship_digits.py
```

Standard library only. The run takes about 20 s, performs 5,817,206 checks and exits 0. It verifies:

- **A3.1.** All 50 real nonprincipal characters modulo $q\le30$ are constructed, with $(1*\chi)(n)\ge0$ for $n\le3000$ and the local values. The explicit bound of Theorem 1(2) holds on certified digits for $D^j\Theta_3$, $j\le2$, $b\in\{2,3,10\}$. Measured $f_{0^L}$ for three binary theta values and four real-character Lambert series.
- **A3.2.** Certified digits for 21 series. Every non-exceptional shift reads the predicted constant word ($L=1,2,3$), and the count inequality of Theorem 2 holds. Every eligible planted window holds; the planting search succeeds; word counts as listed.
- **A3.3.** The gcd reduction for all 30 pairs $(M,r)$ with $M\le12$. Nonnegativity for $\lambda(M)=2$ and explicit negative values (Cases A and B) for all $M\le60$, cross-checked by direct divisor sums when $n<10^8$. The character identities for $(8,3)$, $(12,5)$ and $M=5$, and the mass law. Sign and oriented-tail proportions, certified binary $f_0$, and the Wirsing constants.
- **A3.4.** $a_2(n)$ by exact convolution for $n\le2^{20}$. The sign rule for all 205,753 primes $p\equiv1\pmod{12}$ up to $12\cdot2^{20}+1$ (Cornacchia). The multiplicative sign formula for $n\le2^{16}$. Both signs in every class modulo the tested $Q$. Oriented-tail proportions in bases 2 and 3, and certified binary digits to $2^{18}$.
- **A4.** Strict interiority for $b\le10$, $d<60$, $L\le6$. Exact limit laws for 13 pairs $(b,d)$, both signs $a=\pm1$ and both series (52 laws), including the zero-split masses of the worked cases. Automaton predictions agree with certified digits off the exceptional windows (12 cases, $L=1,2,3$). The odd-order antisymmetry and complement symmetry. The base-2 catalogue (with $w_0^+\ne w_0^-$ at every even order), the $b\ge3$ search, and the bound of $d+1$ on words with positive frequency.

Digits are certified by bracketing $\lfloor b^Mz\rfloor$ between two integers with an explicit tail bound and checking that both give the same leading $N$ digits; the margin $M-N=4\sqrt N+300$ exceeds every constant run. All finite frequencies are measurements at accessible scales. They test the stated identities and finite inequalities; they are not evidence for limits except where a theorem supplies the limit.

## 8. Open problems

1. Simple normality of $E_2^2$ in base 2, equivalently $\rho_+(N;2)\to\frac12$ (Theorem 4.3), or even the existence of $\lim f_0(N;E_2^2)$.
2. The gap-weighted sign limits for the signed reflection series. In particular, prove or refute (H$_{\rm gap}$) for $(M,r)=(8,3)$, which would make $A_{3,8}(2)-A_{5,8}(2)$ simply nonnormal in base 2 with $f_0\to0.5332$.
3. Conjecture 5.5: in base 2, $\tfrac adE_2$ (or $\tfrac adE_2^3$) is simply normal only if $\operatorname{ord}_d(2)$ is odd.
4. A rational scaling of $E_b$ or $E_b^3$ that is simply normal in a base $b\ge3$, or a proof that none exists.
5. The digit laws of $D^j\Theta_Q$ and $D^jL_\chi$ ($j\ge1$) behind the width–density wall.
6. The unweighted sign limit $\frac12$ for the complex-type reflection series (a Delange-type equidistribution of $\arg(1*\chi)(n)$ on the support).
