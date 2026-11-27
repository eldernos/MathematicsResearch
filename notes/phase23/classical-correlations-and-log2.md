# Classical constants: signed divisor correlations, the 2-adic peeling of $E_+$, numerator laws for $\ln 2$, and a missing-estimate map

Phase 23, Track E (E1, E2). This note continues [classical-targets-and-recon.md](../phase22/classical-targets-and-recon.md) (cited below as *P22*). Notation: $D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $0\le n<N$, on half-open intervals. $D^+(x;b)=\limsup_N D_N(x;b)$ and $K_b=\{x:D_N(x;b)\to1\}$. Further,

```math
E=\sum_{n\ge1}\tau(n)2^{-n},\qquad E_+=\sum_{n\ge1}\frac1{2^n+1}=\sum_{n\ge1}a_+(n)2^{-n},\qquad a_+(n)=\sum_{d\mid n}(-1)^{d-1}=(1-v_2(n))\,\tau_{\rm odd}(n),
```

the last identity being `erdosBorweinPlusCoeff_eq` in `NormalityChecker/Phase22Cores.lean`. Write $n=2^em$ with $m$ odd, $\lambda$ for the Liouville function, $L(Y)=\sum_{k\le Y}\lambda(k)$, $\chi_4$ for the nonprincipal character modulo 4, and $\sigma_{-1}(h)=\sum_{d\mid h}1/d$.

**Evidence labels** (repository conventions):

- *Paper proof*: written proof in this note.
- *External input*: a published theorem that is cited, not re-proved.
- *Conditional*: proved here under a stated, unproved hypothesis.
- *Finite certificate*: exact integer or rational computation, or a rigorous rational enclosure of an infinite product, in `scripts/phase23_classical.py`.
- *Finite measurement*: finite data, which bears on no limit.
- *Numerical*: floating-point evaluation of an exact formula; not a certificate.
- *Open*.

No cross-model review was used for these results. Any later cross-model review would not be independent human peer review.

**Nothing in this note proves normality, simple normality, simple nonnormality, $D^+<1$ or (non)membership in $K_2$ for $E$, $E_+$, $\ln2$ or any other benchmark constant. No benchmark status changes.**

## Summary of conclusions

| Result | Evidence |
| --- | --- |
| E1.1 $a_+(n)\equiv\mathbf 1_\square(n)\pmod 2$ and $a_+(k^2)\equiv\tau(k^2)\equiv\lambda(k)\pmod 4$. Hence $\sum_{n\le X}\chi_4(a_+(n))=L(\sqrt X)$: equidistribution of $a_+$ mod 4 on squares is equivalent to the PNT, and square-root cancellation in it is equivalent to RH (Prop. 1.1) | Paper proof; finite certificate to $2^{20}$ |
| E1.1 $\#\{n\le X:a_+(n)\equiv2\ (4)\}\sim\frac{\pi^2}6\frac X{\log X}$, split $7\!:\!3$ between residues $2$ and $6$ mod 8 ($\frac{7\pi^2}{60}$, $\frac{\pi^2}{20}$) (Prop. 1.2) | Paper proof (PNT); structure exact to $2^{20}$ |
| E1.1 $N_j(X)=\#\{n\le X:2^j\nmid a_+(n)\}$: $N_1=\lfloor\sqrt X\rfloor$; $N_j\asymp_jX(\log\log X)^{j-2}/\log X$ for $j\ge2$. So $a_+(n)\equiv0\pmod{2^j}$ for 100% of $n$, for every $j$ (Prop. 1.3) | Paper proof + external (Hardy–Ramanujan) |
| E1.1 **2-adic peeling.** For every $j\ge1$, $\lvert D_N(E_+;2)-D_N(B_j;2)\rvert\le 1-D_N(y_j;2)+j/N\to0$, with $B_j=\sum\lfloor a_+(n)/2^j\rfloor2^{-n}$, $y_j\in K_2$; for $j=1$, $E_+=\sum_{k\ge1}2^{-k^2}+2B_1$. The same holds for $E$, $E_{\rm odd}$ and $\sum\sigma(n)2^{-n}$. All fixed-depth 2-adic information in the coefficients is invisible to $D^\pm$ (Thm. 1.5) | Paper proof (uses SY-04, Lean) |
| E1.1 The peel does not reduce the problem: $B_j$ has coefficients of mean $2^{-j}\ln2$ and mean square $\sim4^{-j}\frac{\log^3X}{3\pi^2}$. At $N=2^{14}$ the discarded part still has $D_N(y_2)=0.398$ | Paper proof; finite measurement |
| E1.2 Exact 2-adic local factors $\mathbb E_2[(1-v)(1-v')]=2-3\cdot2^{-k}$ and $\mathbb E_2[(1+v)(1+v')]=6-3\cdot2^{-k}$ ($k=v_2(h)$). Ratio $\rho(h)=\frac{2^{k+1}-3}{3(2^{k+1}-1)}$, so $\rho=-\frac13$ for every odd $h$ (Prop. 2.1) | Paper proof; finite certificate |
| E1.2 $C_+(h;X)=\frac1X\sum_{n\le X}a_+(n)a_+(n+h)=(c_+(h)+o(1))\log^2X$ with $c_+(h)=\rho(h)\frac6{\pi^2}\sigma_{-1}(h)$. For odd $h$, $a_+(n)a_+(n+h)\le0$ for every $n$ and $c_+(h)=-\frac2{\pi^2}\sigma_{-1}(h)$ (Thm. 2.2) | Asymptotic: Conditional on (H2). Sign and $\lvert C_+\rvert\ll_h\log^2X$: paper proof + Ingham |
| E1.2 $r$-point products: exact 2-adic ratios $\rho(\mathbf h)$ (e.g. $-\frac1{11}$ at $(0,1,2)$, $\frac1{24}$ at $(0,2,4)$, $\frac3{19}$ at $(0,1,4,5)$). The product vanishes identically when $\{h_j\bmod 4\}$ meets $2-n$ for every $n$ (e.g. four consecutive shifts) (§2.3) | Exact; leading constants conditional on the shifted-divisor conjecture |
| E1.2 The reduced mean ($\ln2$) is not reduced fluctuation: the independent model with mean $\ln2$ predicts $(\ln2)^r$, the arithmetic gives $\asymp\log^rX$ whenever $\rho(\mathbf h)\ne0$ (§2.4) | Conditional ($r\ge3$); $r=2$ conditional on (H2) |
| E1.2 **Raw-tail second moments.** $T_n^+=\sum_{k\ge1}a_+(n+k)2^{-k}$ has $\frac1X\sum_{n\le X}(T_n^+)^2\asymp\log^3X$ unconditionally, and $=(\frac1{9\pi^2}+o(1))\log^3X$. The tail $T_n$ of $E$ has variance $(\frac1{3\pi^2}+o(1))\log^3X$. The diagonal forces $\log^3X$; the off-diagonal terms are $O(\log^2X)$ by an elementary two-point bound uniform in the shift (Lemma 3.2) and cannot cancel it. Ratio of variances $\to\frac13$ (Thm. 3.1) | Paper proof (inputs: $\sum_{n\le X}\tau(n)^2\sim X\log^3X/\pi^2$, classical, and P22 Prop. 1.2(b)) |
| E1.2 Off-diagonal constants (Thm. 3.1(3)): $+0.503389\log^2X$ for $E$, $-0.066965\log^2X$ for $E_+$. Observed $-12.98$ against $-12.87$ predicted for $E_+$ at $X=2^{20}$ | For $E$: paper proof + Ingham (external) + Lemma 3.2; for $E_+$: conditional on (H2). Values numerical; finite measurement |
| E1.3 Singular series of the divisor lattice (independent-shift model $=1$): $S(0,1)=6/\pi^2$, then $0.394$, $0.225$, $0.146$, $0.0735$, $0.0491$ for $r=3,\dots,7$ consecutive shifts. Raw divisor correlations differ from independence by $O(1)$ factors from $r=2$ on (§4.1) | Finite certificate (enclosures); $r=2$ Ingham, $r\ge3$ conditional |
| E1.3 Marks $U=\operatorname{odd}(\tau)$ mod 4 at $r$ consecutive shifts: exact local-product law. Total variation from i.i.d. marks is $0.0272$, $0.0559$, $0.0755$, $0.0882$, $0.1065$, $0.1232$ for $r=2,\dots,7$, dominated by $p=2,3$ (§4.2) | Paper proof (formula); numerical (values); finite check |
| E1.3 Column-level correlations average these deviations over the displacement law; heuristically the residual decays only at a doubly logarithmic rate (§4.3) | Open (heuristic) |
| E2.1 $D^+(x;2)=1\iff\limsup_N\lvert\frac1N\sum_{n<N}e(2^nx)\rvert=1$. Quantitatively, $\limsup\lvert S_N(1)\rvert\le0.9997$ implies $D^+\le0.9999$. A degree-2 minorant bounds the transition density below by $\frac14-\frac12\mathrm{Re}\,S_N(1)+\frac14\mathrm{Re}\,S_N(2)$ (Prop. 5.1, 5.2) | Paper proof; constants exact |
| E2.1 **Band law for $\ln2$.** With $s_N=\sum_{k\le N}2^{N-k}/k=A_N/Q_N$, every odd prime $p$ with $\sqrt N<p\le N$ and $m=\lfloor N/p\rfloor$ satisfies $v_p(Q_N)=1-[p\mid A_m]$ and $p\,s_N\equiv2^{N-m}s_m\pmod p$. The large-prime part of the BBP state is explicit in the numerators $A_m$, $m<\sqrt N$ (Thm. 5.3) | Paper proof; finite certificate ($661{,}864$ pairs) |
| E2.1 Glaisher–Wieferich law: $s_{p-1-j}\equiv2^{p-1-j}\bigl(q_p(2)+\sum_{i\le j}2^{i-1}/i\bigr)\pmod p$; $p\mid A_{p-1}\iff p$ is a Wieferich prime (Prop. 5.4) | Paper proof; finite certificate |
| E2.2 Gap: needed, $\lvert\sum_{n<N}e(x_n)\rvert\le0.9997N$; known, $\mathrm{Re}\sum\le N-(1+o(1))\log N/\log\mu$, with $\mu=3.5746$. Subgroup exponential-sum methods need $\ge q^\delta$ terms, while the BBP orbit evolves by pure doubling only for $\approx\log_2n$ steps against $\log Q_n\sim n$ (§5.4) | Paper proof + external; **$D^+(\ln2;2)\le0.9999$ open** |
| E2.3 Missing-estimate map for the 35 open benchmark constants (§6) | Open everywhere |

## 1. E1.1 The 2-adic structure of $a_+$ and the peeling of $E_+$

### 1.1 Parity, residues mod 4 and the Liouville function

**Proposition 1.1.** For all $n,k\ge1$:

1. $a_+(n)\equiv\mathbf 1_\square(n)\pmod2$.
2. $a_+(k^2)\equiv\tau(k^2)\equiv\lambda(k)\pmod4$.
3. $\sum_{n\le X}\chi_4(a_+(n))=L(\lfloor\sqrt X\rfloor)$.

Hence $\#\{k\le Y:a_+(k^2)\equiv1\ (4)\}-\#\{k\le Y:a_+(k^2)\equiv3\ (4)\}=L(Y)$. By Landau, $L(Y)=o(Y)$ is equivalent to the prime number theorem, and $L(Y)\ll Y^{1/2+\varepsilon}$ for all $\varepsilon>0$ is equivalent to the Riemann hypothesis (external, classical).

*Proof.* (1) is P22 Proposition 1.1 (Lean: `erdosBorweinPlusCoeff_odd_iff`). (2) Let $k=2^v\prod_{p>2}p^{\beta_p}$. Then $a_+(k^2)=(1-2v)\prod(2\beta_p+1)$ and $\tau(k^2)=(1+2v)\prod(2\beta_p+1)$. Since $2\beta+1\equiv(-1)^\beta$ and $1\pm2v\equiv(-1)^v\pmod 4$, both are $\equiv(-1)^{v+\sum\beta_p}=\lambda(k)\pmod4$. (3) $\chi_4$ vanishes on even values, and by (1) $a_+(n)$ is odd exactly on squares. ∎

The script checks (1)–(2) for all $n\le2^{20}$ and (3) at $X=10^3,\dots,10^6,2^{20}$, where $L(1024)=-20$.

### 1.2 The residue class $2\bmod4$ and the $7:3$ split mod 8

**Proposition 1.2.** As $X\to\infty$,

```math
\#\{n\le X:a_+(n)\equiv2\ (4)\}\sim\frac{\pi^2}6\,\frac X{\log X},\qquad
\#\{\equiv2\ (8)\}\sim\frac{7\pi^2}{60}\,\frac X{\log X},\qquad \#\{\equiv6\ (8)\}\sim\frac{\pi^2}{20}\,\frac X{\log X}.
```

*Proof.* If $a_+(n)\ne0$ then $e\ne1$, and $v_2(a_+(n))=v_2(1-e)+v_2(\tau(m))$ (with $v_2(1)=0$). Now $v_2(\tau(m))=\sum_pv_2(\alpha_p+1)$. So $v_2(a_+(n))=1$ exactly when either

- (i) $e\in\{0,2,4,\dots\}$ and $m=p^\alpha s^2$ with $\alpha\equiv1\ (4)$, $p\nmid s$, $s$ odd; or
- (ii) $e\equiv3\ (4)$ and $m$ is a square.

Case (ii) and the terms $\alpha\ge5$ contribute $O(\sqrt X)$. For $\alpha=1$ the count is $\sum_{e\ge0\ \rm even}\sum_{s\ \rm odd}\#\{p\le Y_{e,s}\text{ odd prime}:p\nmid s\}$ with $Y_{e,s}=X/(2^es^2)$. Truncate jointly in $e$ and $s$:

- Pairs with $2^es^2>X^{1/2}$ contribute at most $\sum Y_{e,s}\ll X^{3/4}$. For $s\le X^{1/4}$ the sum over $e$ is geometric with largest term $<X^{1/2}$; the $s>X^{1/4}$ contribute at most $\sum_{s>X^{1/4}}2X/s^2$.
- Pairs with $2^es^2\le X^{1/2}$ have $Y_{e,s}\ge X^{1/2}$, so $\frac12\log X\le\log Y_{e,s}\le\log X$ and, by the PNT, $\pi(Y_{e,s})=(1+o(1))Y_{e,s}/\log Y_{e,s}$ uniformly in such pairs. The condition $p\nmid s$ removes at most $\omega(s)\ll\log X$ primes per pair, $O(X^{1/4}\log^2X)$ in total. Divided by $X/\log X$, the term of $(e,s)$ tends to $2^{-e}s^{-2}$, and by Chebyshev's bound it is $\ll2^{-e}s^{-2}$ uniformly. Dominated convergence gives $(1+o(1))\bigl(\sum_{e\ge0\ \rm even}2^{-e}\bigr)\bigl(\sum_{s\ \rm odd}s^{-2}\bigr)\frac X{\log X}$.

Since $\sum_{e\ge0\ \rm even}2^{-e}=\frac43$ and $\sum_{s\ \rm odd}s^{-2}=\frac{\pi^2}8$, the total is $\frac{\pi^2}6\frac X{\log X}$.

For the split, in case (i) with $\alpha=1$: $a_+(n)/2=(1-e)\tau(s^2)\equiv(1-e)\lambda(s)\pmod 4$ by Proposition 1.1, and $1-e\equiv1$ or $-1$ according as $e\equiv0$ or $2\pmod4$. With the same joint truncation and dominated convergence (the weights $\pm\lambda(s)$ are bounded), the signed count is

```math
\Bigl(\sum_{s\ \rm odd}\frac{\lambda(s)}{s^2}\Bigr)\Bigl(1+\sum_{e\equiv0\,(4),\,e\ge4}2^{-e}-\sum_{e\equiv2\,(4)}2^{-e}\Bigr)\frac X{\log X}=\frac{\pi^2}{12}\cdot\frac45\cdot\frac X{\log X}=\frac{\pi^2}{15}\frac X{\log X},
```

using $\sum_{s\ \rm odd}\lambda(s)s^{-2}=\frac54\,\zeta(4)/\zeta(2)=\pi^2/12$. Half the sum and half the difference of $\frac{\pi^2}6$ and $\frac{\pi^2}{15}$ give the two counts. ∎

The general rule, including $\alpha\ge5$, is $a_+(n)/2\equiv(1-e)\,\frac{\alpha+1}2\,\lambda(s)\pmod 4$. The script verifies the characterization (i)/(ii) and this rule for every $n\le2^{20}$; exponent tally $\alpha=1,5,9$: $152985,68,5$. It also verifies that the $\alpha=1$ part equals $\sum_{e,s}\#\{p\le X/(2^es^2)\text{ odd prime},\ p\nmid s\}$ exactly.

*Finite measurement* at $X=2^{20}$: residues mod 8 are $(587268,282,101348,293,306985,220,51951,229)$ for $a_+\equiv0,\dots,7$. Further:

- $\#\{\equiv2\ (4)\}=153299$, which is $2.0267\,X/\log X$ against the limit $1.6449$. It is $1.0917$ times $\sum_{e,s}Y/\log Y$ with $Y=X/(2^es^2)$, the usual $\pi(Y)/(Y/\log Y)$ excess.
- The $2:6$ ratio is $1.9508$ against $7/3$; the signed share is $0.3222$ against the main-term value $0.3274$ and the limit $2/5$.

Convergence is logarithmic.

### 1.3 Divisibility by $2^j$ on 100% of integers

**Proposition 1.3.** $N_1(X)=\lfloor\sqrt X\rfloor$. For $j\ge2$, $N_j(X)\asymp_j X(\log\log X)^{j-2}/\log X$. In particular $\{n:2^j\nmid a_+(n)\}$ has density $0$ for every fixed $j$.

*Proof.* $N_1$: $a_+(n)$ is odd exactly on squares (Proposition 1.1(1)). Let $j\ge2$. If $a_+(n)\ne0$ and $2^j\nmid a_+(n)$ then $v_2(\tau(m))\le j-1$. Each prime with odd exponent in $m$ contributes at least $1$ to $v_2(\tau(m))$, so $m=s\,r^2$ with $s$ squarefree, odd and $\omega(s)\le j-1$. Hence $N_j(X)\le\sum_{e,r}\#\{s\le Y_{e,r}:\omega(s)\le j-1\}$ with $Y_{e,r}=X/(2^er^2)$. Truncate jointly, as in Proposition 1.2. Pairs with $2^er^2>X^{1/2}$ contribute at most $\sum Y_{e,r}\ll X^{3/4}$. Pairs with $2^er^2\le X^{1/2}$ have $\frac12\log X\le\log Y_{e,r}\le\log X$. For them the Hardy–Ramanujan inequality $\#\{s\le Y:\omega(s)=k\}\ll_kY(\log\log Y+O(1))^{k-1}/\log Y$ (external, 1917; uniform in $Y\ge3$), applied for each $k\le j-1$, gives $\ll_jY_{e,r}(\log\log X)^{j-2}/\log X$. Since $\sum_{e,r}Y_{e,r}\ll X$, this is the upper bound. For the lower bound, odd squarefree $n$ with $\omega(n)=j-1$ have $a_+(n)=2^{j-1}$; Landau's asymptotic for such $n$ is external. ∎

*Finite measurement:* $N_j(2^{20})=1024,154323,461308,688238,769968$ for $j=1,\dots,5$, densities $0.0010,0.1472,0.4399,0.6564,0.7343$. At accessible scales the "density zero" of Proposition 1.3 is invisible for $j\ge3$.

### 1.4 The peeling theorem

**Lemma 1.4 (sparse bounded coefficients).** Let $c(n)\in\{0,\dots,M\}$ be supported on a set $Z$ with $Z(X)=\#(Z\cap[1,X])$, and let $y=\sum c(n)2^{-n}$. For every $L$ with $M2^{-L}<1$,

```math
1-D_N(y;2)\le\frac{L\,Z(N+L)}N+M2^{-L}.
```

*Proof.* If $c(n+1)=\dots=c(n+L)=0$ then $\{2^ny\}=\sum_{k>L}c(n+k)2^{-k}\in[0,M2^{-L}]$. At most $L\,Z(N+L)$ indices $n<N$ fail this. For $0<\varepsilon\le1-M2^{-L}$ the half-open interval $J=[0,M2^{-L}+\varepsilon)$ therefore holds at least $N-L\,Z(N+L)$ points, so $D_N(y;2)\ge1-L\,Z(N+L)/N-M2^{-L}-\varepsilon$. Let $\varepsilon\to0^+$. ∎

**Theorem 1.5 (2-adic peeling).** For $j\ge1$ put $y_j=\sum_n(a_+(n)\bmod2^j)2^{-n}$ and $B_j=\sum_n\lfloor a_+(n)/2^j\rfloor2^{-n}$, so that $E_+=y_j+2^jB_j$. Then $y_j\in K_2$ and

```math
\bigl|D_N(E_+;2)-D_N(B_j;2)\bigr|\le1-D_N(y_j;2)+\frac jN,\qquad
1-D_N(y_j;2)\ll_j\begin{cases}\log N/\sqrt N,& j=1,\\ (\log\log N)^{j-1}/\log N,& j\ge2.\end{cases}
```

Hence $D^+(E_+;2)=D^+(B_j;2)$ and $D^-(E_+;2)=D^-(B_j;2)$ for every $j$. For $j=1$, $y_1=\sum_{k\ge1}2^{-k^2}=\frac12(\Theta_3(\frac12)-1)$, which gives the **theta peeling identity**

```math
E_+=\sum_{k\ge1}2^{-k^2}+2\sum_{n\ge1}\Bigl\lfloor\frac{a_+(n)}2\Bigr\rfloor2^{-n}.
```

*Proof.* $y_j$ has coefficients in $[0,2^j)$ supported on $\{n:2^j\nmid a_+(n)\}$. Lemma 1.4 with Proposition 1.3 gives the bound: for $j=1$ take $L=\lceil\frac12\log_2N\rceil$, and for $j\ge2$ take $L=\lceil\log_2\log N\rceil+j$. SY-04 (`sharp_translation`, Lean) gives $\lvert D_N(x+z)-D_N(x)\rvert\le1-D_N(z)$ for $x=2^jB_j$, $z=y_j$. P22 Proposition 1.3(1), applied $j$ times, gives $\lvert D_N(2^jB_j)-D_N(B_j)\rvert\le j/N$. For $j=1$, $a_+\bmod2=\mathbf 1_\square$ by Proposition 1.1(1). ∎

**Corollary 1.6.** Let $c(n)\in\mathbb Z$ with $\sum_n\lvert c(n)\rvert2^{-n}<\infty$, put $x=\sum_nc(n)2^{-n}$, and define $y_j=\sum_n(c(n)\bmod2^j)2^{-n}$ and $B_j=\sum_n\lfloor c(n)/2^j\rfloor2^{-n}$. Suppose that $Z_j=\{n:2^j\nmid c(n)\}$ has density $0$ for each $j$. Then for every $j$, $y_j\in K_2$, $\lvert D_N(x;2)-D_N(B_j;2)\rvert\le1-D_N(y_j;2)+j/N\to0$, and $D^\pm(x;2)=D^\pm(B_j;2)$. If moreover $Z_1(X)\ll\sqrt X$ and $Z_j(X)\ll_jX(\log\log X)^{j-2}/\log X$ for $j\ge2$, the rate of Theorem 1.5 holds.

*Proof.* $B_j$ converges because $\lvert\lfloor c/2^j\rfloor\rvert\le\lvert c\rvert+1$. The proof of Theorem 1.5 applies, except that for the qualitative statement one fixes $L$ in Lemma 1.4 and lets $N\to\infty$: $\limsup_N(1-D_N(y_j;2))\le(2^j-1)2^{-L}$, and then $L\to\infty$. ∎

This covers, with the rate:

- $\tau$ (constant $E$). $\tau(n)$ is odd exactly on squares, so $y_1(\tau)=\sum_{k\ge1}2^{-k^2}$. Also $v_2(\tau(n))\ge\#\{p:v_p(n)\text{ odd}\}$.
- $\tau_{\rm odd}$ (constant $E_{\rm odd}=\sum_{n\ \rm odd}1/(2^n-1)=\sum_n\tau_{\rm odd}(n)2^{-n}$). $\tau_{\rm odd}(n)$ is odd exactly when $n=k^2$ or $n=2k^2$, so $y_1(\tau_{\rm odd})=\sum_k2^{-k^2}+\sum_k2^{-2k^2}$. Also $v_2(\tau_{\rm odd}(n))\ge\#\{p>2:v_p(n)\text{ odd}\}$.
- $\sigma$ (constant $\sum\sigma(n)2^{-n}$). $\sigma(n)$ is odd exactly when $n=k^2$ or $n=2k^2$. Also $v_2(\sigma(n))\ge\#\{p>2:v_p(n)\text{ odd}\}$, since for odd $p$ and odd $v$, $\sigma(p^v)=1+p+\dots+p^v$ is a sum of an even number of odd terms.

In each case write the odd part of $n$ as $s\,r^2$ with $s$ squarefree. Then $2^j\nmid c(n)$ forces $\omega(s)\le j-1$, and the count in the proof of Proposition 1.3 applies verbatim. The theta form $y_1=\sum2^{-k^2}$ is specific to $a_+$ and $\tau$.

Moreover $\lfloor\tau(n)/2\rfloor-\lfloor a_+(n)/2\rfloor=\tau(n/2)[2\mid n]$, so $B_1(\tau)-B_1(a_+)=E(4)$, consistent with $E-E_+=2E(4)$ (checked for $n\le20000$).

**What the peel does and does not do.** Theorem 1.5 is an exact $K_2$-equivalence. The limiting discrepancies of $E_+$ do not see the parity of the coefficients (the squares), nor the Liouville-signed residues mod 4 (Proposition 1.1), nor any fixed number of further 2-adic digits. It is not a reduction. $B_j$ is a constant of exactly the same type: its coefficients $\lfloor a_+/2^j\rfloor$ are dense and signed, have mean $2^{-j}\ln2+o(1)$ (the discarded remainders have density-zero support and bounded size), and have mean square $\sim4^{-j}\log^3X/(3\pi^2)$. Iterating with $j\to\infty$ is not available, because the error $1-D_N(y_j)$ is controlled only for fixed $j$. The peel also does not commute with the comparison model of P22 §1.5: the marks of $B_j$ are the odd parts of $\lfloor a_+/2^j\rfloor$, which are not those of $a_+$.

*Finite measurement* ($2^{14}+64$ certified digits; extreme discrepancies from 53-bit points):

| $N$ | $E_+$ | $\sum2^{-k^2}$ | $2B_1$ | $B_1$ | $y_2$ | $4B_2$ |
| --- | --- | --- | --- | --- | --- | --- |
| $2^{10}$ | 0.05679 | 0.84741 | 0.04257 | 0.04355 | 0.21606 | 0.07657 |
| $2^{12}$ | 0.02054 | 0.90768 | 0.02241 | 0.02266 | 0.31564 | 0.04763 |
| $2^{14}$ | 0.01402 | 0.94585 | 0.01625 | 0.01625 | 0.39756 | 0.03673 |

The SY-04 inequalities $\lvert D_N(E_+)-D_N(2B_1)\rvert\le1-D_N(\sum2^{-k^2})$ and $\lvert D_N(E_+)-D_N(4B_2)\rvert\le1-D_N(y_2)$ hold in every row. The Lemma 1.4 bound at $N=2^{14}$, $L=7$ is $0.0625$. The theta part is already close to $K_2$ behaviour ($D_N=0.946$), but $y_2$ is far from it ($0.398$), as Proposition 1.3 predicts.

## 2. E1.2 Signed correlations of $a_+$

### 2.1 Local factors

For a function $g=1*f$ write $g_p(v)$ for its value on $p^v$ when it is determined locally. Then $g_p(v)=1+v$ for $\tau$ at every $p$, while for $a_+$ one has $g_p(v)=1+v$ at odd $p$ and $g_2(v)=1-v$. Let $\mathbb E_p$ denote Haar expectation over $n\in\mathbb Z_p$, and $v=v_p(n)$, $v'=v_p(n+h)$.

**Proposition 2.1.** Let $k=v_2(h)$, $h\ne0$. Then

```math
\mathbb E_2[(1-v)(1-v')]=2-\frac3{2^k},\qquad \mathbb E_2[(1+v)(1+v')]=6-\frac3{2^k},\qquad
\rho(h):=\frac{\mathbb E_2[(1-v)(1-v')]}{\mathbb E_2[(1+v)(1+v')]}=\frac{2^{k+1}-3}{3(2^{k+1}-1)}.
```

Also $\mathbb E_2[1-v]=0$ and $\mathbb E_2[(1-v)^2]/\mathbb E_2[(1+v)^2]=2/6=1/3$, the $h=0$ ratio of P22 Proposition 1.2(b).

*Proof.* Split by $v(n)$. If $v(n)=j<k$ then $v(n+h)=j$; if $j>k$ then $v(n+h)=k$; if $j=k$ then $v(n+h)=k+i$ with conditional probability $2^{-i}$, $i\ge1$. For $\varphi(v)=1\mp v$ the second and third contributions are equal, so

```math
\mathbb E_2[\varphi(v)\varphi(v')]=\sum_{j<k}\frac{\varphi(j)^2}{2^{j+1}}+2\varphi(k)\,2^{-k-1}\sum_{i\ge1}2^{-i}\varphi(k+i).
```

With a geometric variable $G$ ($\mathbb EG=1$, $\mathbb EG^2=3$): for $\varphi=1-v$ the first sum is $2-2^{-k}\mathbb E(1-k-G)^2=2-2^{-k}(k^2+2)$, and the second term is $2^{-k}(1-k)(-1-k)$. The total is $2-3\cdot2^{-k}$. The case $\varphi=1+v$ is identical, giving $6-2^{-k}(k^2+4k+6)+2^{-k}(k+1)(k+3)=6-3\cdot2^{-k}$. ∎

The denominator reproduces Ingham's 2-adic factor $(1-\frac14)\sum_{j\le k}2^{-j}=\frac14(6-3\cdot2^{-k})$. The script implements a general exact recursion for $\mathbb E_p[\prod_jg(v_p(n+h_j))]$. It checks Ingham's factors $(1-p^{-2})\sum_{j\le v_p(h)}p^{-j}$ for $p\le7$, $h\le40$, and the closed forms for $k\le20$. Values: $\rho(1)=\rho(3)=\dots=-\frac13$, $\rho(2)=\frac19$, $\rho(4)=\frac5{21}$, $\rho(8)=\frac{13}{45}$, $\rho(16)=\frac{29}{93}$, and $\rho\to\frac13$ as $k\to\infty$.

### 2.2 Two-point correlations

**Hypothesis (H2).** For fixed $h\ge1$, $K\ge0$ and $a\bmod2^K$,

```math
\sum_{n\le X,\ n\equiv a\,(2^K)}\tau(n)\tau(n+h)=\bigl(c_{a,K}(h)+o(1)\bigr)X\log^2X,
```

where $c_{a,K}(h)=\frac14\,\mathbb E_2\bigl[(1+v)(1+v')\mathbf 1_{n\equiv a\,(2^K)}\bigr]\prod_{p>2}(1-\frac1p)^2\mathbb E_p[(1+v)(1+v')]$ is the singular series localized at 2. For $K=0$ this is Ingham's theorem (1927, external). For $K\ge1$ we believe it follows from the standard treatments of the binary additive divisor problem for linear forms (Estermann's method with Weil's bound), but we have not pinned a reference. It is used here as a hypothesis.

**Theorem 2.2.** Let $h\ge1$.

1. *(Paper proof.)* For odd $h$, $a_+(n)a_+(n+h)\le0$ for every $n$. For every $h$, $\lvert C_+(h;X)\rvert\le\frac1X\sum_{n\le X}\tau(n)\tau(n+h)\sim\frac6{\pi^2}\sigma_{-1}(h)\log^2X$ (Ingham).
2. *(Conditional on (H2).)* $C_+(h;X)=(c_+(h)+o(1))\log^2X$ with

```math
c_+(h)=\rho(h)\,\frac6{\pi^2}\,\sigma_{-1}(h),\qquad c_+(h)=-\frac2{\pi^2}\sigma_{-1}(h)\ \ (h\ \text{odd}).
```

*Proof.* (1) $\operatorname{sign}a_+(n)$ depends only on $n\bmod4$ (positive, zero, positive, negative for $n\equiv1,2,3,0$). For odd $h$ one of $n,n+h$ is odd and the other even, so one factor is $>0$ and the other $\le0$. Also $\lvert a_+\rvert\le\tau$. (2) $a_+(n)a_+(n+h)=w(e,e')\tau(n)\tau(n+h)$ with $w=\frac{(1-e)(1-e')}{(1+e)(1+e')}$, $e=v_2(n)$, $e'=v_2(n+h)$, and $\lvert w\rvert\le1$. For $e,e'<K$, $w$ is constant on classes mod $2^K$. Apply (H2) to each class. The classes with $e\ge K$ or $e'\ge K$ have total (H2)-coefficient $\ll K^22^{-K}$ times the odd-prime product. Let $X\to\infty$ and then $K\to\infty$. The 2-adic factor becomes $\frac14\mathbb E_2[w(1+v)(1+v')]=\frac14\mathbb E_2[(1-v)(1-v')]$, and the odd-prime factors are those of $\tau$. ∎

Leading coefficients ($6/\pi^2$ in floating point): $c_+(1),\dots,c_+(8)=-0.202642,\ +0.101321,\ -0.270190,\ +0.253303,\ -0.243171,\ +0.135095,\ -0.231591,\ +0.329294$.

*Finite measurement.* $\sum_{n\le X}a_+(n)a_+(n+h)/\sum_{n\le X}\tau(n)\tau(n+h)$, which tends to $\rho(h)$ under (H2):

| $h$ | $X=2^{14}$ | $2^{17}$ | $2^{20}$ | $\rho(h)$ |
| --- | --- | --- | --- | --- |
| 1 | $-0.3023$ | $-0.3078$ | $-0.3115$ | $-0.3333$ |
| 2 | $+0.1432$ | $+0.1375$ | $+0.1335$ | $+0.1111$ |
| 4 | $+0.2554$ | $+0.2521$ | $+0.2499$ | $+0.2381$ |
| 8 | $+0.2917$ | $+0.2910$ | $+0.2905$ | $+0.2889$ |

Odd $h=3,5,7$ give $-0.3108,-0.3108,-0.3109$ at $2^{20}$, and $h=6$ gives $+0.1343$. Every row moves monotonically toward $\rho(h)$.

### 2.3 $r$-point products and their 2-adic factorization

Under the shifted-divisor conjecture for $\tau$, $\sum_{n\le X}\prod_{j=1}^r\tau(n+h_j)\sim S(\mathbf h)X\log^rX$ for distinct shifts with $S(\mathbf h)=\prod_p(1-\frac1p)^r\mathbb E_p[\prod_j(1+v_p(n+h_j))]$; this is a standard conjecture, open for $r\ge3$. The argument of Theorem 2.2(2), with (H2) replaced by its $r$-point analogue in classes mod $2^K$, gives

```math
M_+^{(r)}(\mathbf h;X)=\frac1X\sum_{n\le X}\prod_{j}a_+(n+h_j)=\bigl(\rho(\mathbf h)S(\mathbf h)+o(1)\bigr)\log^rX,\qquad \rho(\mathbf h)=\frac{\mathbb E_2[\prod_j(1-v(n+h_j))]}{\mathbb E_2[\prod_j(1+v(n+h_j))]}.
```

This is the exact 2-adic factorization (Conditional). The ratios $\rho(\mathbf h)$ are exact rationals, and $S(\mathbf h)$ is enclosed rigorously (§4.1). Unconditionally:

- The product vanishes identically if for every $n$ some $n+h_j\equiv2\pmod4$, for instance any four consecutive shifts. Then $\rho(\mathbf h)=0$ (script: exact, and the product is checked to vanish for $n\le4096$).
- $\operatorname{sign}\prod_ja_+(n+h_j)$ depends only on $n\bmod4$.
- $\lvert M_+^{(r)}\rvert\ll_{\mathbf h}\log^rX$ by the Nair–Tenenbaum bound for $\prod\tau(n+h_j)$ (external).

| pattern $\mathbf h$ | $r$ | $S(\mathbf h)$ (enclosure) | $\rho(\mathbf h)$ | $\rho S$ |
| --- | --- | --- | --- | --- |
| $(0,1)$ | 2 | $[0.607924,0.607927]$ | $-1/3$ | $-0.20264$ |
| $(0,1,2)$ | 3 | $[0.394270,0.394278]$ | $-1/11$ | $-0.03584$ |
| $(0,1,2,3)$ | 4 | $[0.224653,0.224663]$ | $0$ | $0$ |
| $(0,4)$ | 2 | $[1.063868,1.063873]$ | $5/21$ | $+0.25330$ |
| $(0,4,8)$ | 3 | $[1.227614,1.227639]$ | $-7/137$ | $-0.06273$ |
| $(0,4,8,12)$ | 4 | $[1.642772,1.642846]$ | $5/117$ | $+0.07020$ |
| $(0,4,\dots,24)$ | 7 | $[3.687709,3.688373]$ | $-79/24938$ | $-0.01168$ |
| $(0,2,4)$ | 3 | $[0.860226,0.860243]$ | $1/24$ | $+0.03584$ |
| $(0,2,\dots,12)$ | 7 | $[0.788470,0.788612]$ | $1/1333$ | $+0.00059$ |
| $(0,1,4,5)$ | 4 | $[0.306791,0.306805]$ | $3/19$ | $+0.04844$ |
| $(0,1,4,5,8,9,12)$ | 7 | $[0.116129,0.116150]$ | $5/597$ | $+0.00097$ |

The script prints the full family (step 1, 2, 4 and $\{0,1\}\bmod4$, $r\le7$). *Finite measurement* of the three-point ratios at $X=2^{14},2^{17},2^{20}$:

- $(0,1,2)$: $-0.0898,-0.0902,-0.0904$ against $\rho=-0.0909$.
- $(0,2,4)$: $+0.0620,+0.0582,+0.0557$ against $+0.0417$.
- $(0,4,8)$: $-0.0220,-0.0276,-0.0314$ against $-0.0511$.

All three move toward $\rho$, slowly for the last two.

### 2.4 Reduced mean is not reduced fluctuation

The independent model with the correct mean predicts $M_+^{(r)}\approx(\ln2)^r$. The arithmetic gives $\asymp\log^rX$ whenever $\rho(\mathbf h)\ne0$, which is conditional for $r\ge3$ and conditional on (H2) at $r=2$. The cancellation $\mathbb E_2[1-v]=0$ kills the logarithm in the first moment only. In every higher mixed moment the 2-adic factor is a nonzero rational for generic patterns, and the odd primes contribute exactly as for $\tau$. Quantitatively, P22's advice "do not confuse reduced coefficient mean with controlled digit distribution" is the statement $\rho(\mathbf h)\ne0$.

### 2.5 Parity and column indicators

- *Parity.* By Proposition 1.1(1), $\sum_{n\le X}\prod_j(a_+(n+h_j)\bmod2)$ counts $n$ with all $n+h_j$ square. For distinct shifts this is bounded, since $w^2-u^2=h_2-h_1$ has finitely many solutions (paper proof).
- *Nonzero indicator.* $\mathbf 1[a_+(n)\ne0]=\mathbf 1[n\not\equiv2\ (4)]$ is 4-periodic, so all its correlations are exact rationals.
- *Indivisibility indicator.* $\mathbf 1[4\nmid a_+(n)]$ has two-point correlation $\ll_hX/\log^2X$ by a Brun–Selberg upper-bound sieve (paper proof sketch, external sieve). A matching lower bound would need Hardy–Littlewood-type input (Open).

In the signed model of P22 §1.5 the source sign is drawn independently with probability $2/3$. In the arithmetic, the sign is a deterministic function of the source index mod 4, and the column sign is random only through the displacement $V_+$.

## 3. E1.2 Raw-tail second moments of $E$ and $E_+$

Let $T_n=\sum_{k\ge1}\tau(n+k)2^{-k}$ and $T_n^+=\sum_{k\ge1}a_+(n+k)2^{-k}$, and write $\mathbb E_X$ for $\frac1X\sum_{n\le X}$.

For $c\in\{\tau,a_+\}$ write $T_n(c)=\sum_{k\ge1}c(n+k)2^{-k}$ (so $T_n=T_n(\tau)$, $T_n^+=T_n(a_+)$) and $C_c(h;X)=\frac1X\sum_{n\le X}c(n)c(n+h)$, so $C_+=C_{a_+}$. Split $\mathbb E_XT_n(c)^2=\mathrm{Diag}_X(c)+\mathrm{Off}_X(c)$ with $\mathrm{Diag}_X(c)=\sum_{k\ge1}4^{-k}\mathbb E_Xc(n+k)^2$.

**Theorem 3.1.**

1. *(Paper proof, using only $\sum_{n\le X}\tau(n)^2\sim X\log^3X/\pi^2$ and P22 Proposition 1.2(b).)* $(\frac1{10}-o(1))\frac{\log^3X}{3\pi^2}\le\mathbb E_X(T_n^+)^2\le(1+o(1))\frac{\log^3X}{3\pi^2}$, and the same with $\frac1{\pi^2}$ for $T_n$.
2. *(Paper proof, same inputs and Lemma 3.2.)* $\mathbb E_X(T_n^+)^2=(\frac1{9\pi^2}+o(1))\log^3X$ and $\mathrm{Var}_X(T_n)=(\frac1{3\pi^2}+o(1))\log^3X$. Since $\mathbb E_XT_n^+=\ln2+o(1)$ and $\mathbb E_XT_n=\log X+O(1)$, $\mathrm{Var}_X(T^+_n)/\mathrm{Var}_X(T_n)\to\frac13$.
3. *(Off-diagonal.)* $\mathrm{Off}_X(\tau)$ and $\mathrm{Off}_X(a_+)$ are $O(\log^2X)$ (paper proof, Lemma 3.2). Moreover $\mathrm{Off}_X(\tau)=(\kappa_\tau+o(1))\log^2X$ with $\kappa_\tau=\frac4{\pi^2}\sum_{h\ge1}2^{-h}\sigma_{-1}(h)=\frac4{\pi^2}\sum_{d\ge1}\frac1{d(2^d-1)}=0.503389$ (paper proof with Ingham's theorem as external input). Conditionally on (H2), $\mathrm{Off}_X(a_+)=(\kappa_++o(1))\log^2X$ with $\kappa_+=\frac23\sum_{h\ge1}2^{-h}c_+(h)=-0.066965$.

So the signed cancellation leaves the order $\log^3X$ of the tail variance unchanged and lowers the leading constant by exactly the 2-adic factor $\frac13$.

**Lemma 3.2 (uniform two-point bound, paper proof).** For $X\ge2$ and every integer $1\le h\le X$,

```math
\sum_{n\le X}\tau(n)\tau(n+h)\le4\,\sigma_{-1}(h)\,X\Bigl(1+\frac12\log(2X)\Bigr)^2+8X .
```

In particular $C_\tau(h;X)\ll\sigma_{-1}(h)\log^2X\le\frac h{\varphi(h)}\log^2X$ uniformly in $1\le h\le X$.

*Proof.* Each $m$ has $\tau(m)\le2\#\{d\mid m:d\le\sqrt m\}$. For $n\le X$ and $h\le X$ we have $n+h\le2X$; put $Y=\sqrt{2X}$. Then $\tau(n)\tau(n+h)\le4\sum_{d,e\le Y}\mathbf 1[d\mid n]\,\mathbf 1[e\mid n+h]$. The congruences $d\mid n$, $e\mid n+h$ are solvable only if $g=\gcd(d,e)$ divides $h$, and then they fix $n$ modulo $de/g$, so at most $Xg/(de)+1$ values $n\le X$ satisfy both. Write $d=gd'$, $e=ge'$. Summing,

```math
\sum_{n\le X}\tau(n)\tau(n+h)\le4X\sum_{g\mid h}\frac1g\Bigl(\sum_{d'\le Y/g}\frac1{d'}\Bigr)^2+4Y^2\le4X\,\sigma_{-1}(h)\,(1+\log Y)^2+8X .
```

Finally $\sigma_{-1}(h)=\sigma(h)/h\le h/\varphi(h)$, because $\sigma(p^a)\varphi(p^a)=p^{a-1}(p^{a+1}-1)<p^{2a}$. ∎

*Finite check:* the script verifies the inequality for $X=2^{10}$ and all $h\le X$, and for $X=2^{18}$ with $h\le12$ and $h=2^{17},2^{18}$ ($1038$ pairs; the largest ratio of the two sides is $0.4777$).

*Proof.* (1) Upper bound: by Cauchy–Schwarz with weights $2^{-k}$, $(T_n^+)^2\le\sum_k2^{-k}a_+(n+k)^2$; average over $n$. Lower bound: $T^+_{n-1}=\frac12a_+(n)+\frac12T^+_n$, so $a_+(n)=2T^+_{n-1}-T^+_n$ and $a_+(n)^2\le8(T^+_{n-1})^2+2(T^+_n)^2$; average over $n$.

(2), (3) Let $c\in\{\tau,a_+\}$, so $\lvert c\rvert\le\tau$. For $k\ge1$, $h\ge0$ put $M_{k,h}(X)=\frac1X\sum_{n\le X}c(n+k)c(n+k+h)$. Expanding the absolutely convergent square, with $k'=k+h$,

```math
\mathbb E_XT_n(c)^2=\sum_{k\ge1}4^{-k}M_{k,0}(X)+2\sum_{k\ge1}\sum_{h\ge1}2^{-2k-h}M_{k,h}(X)=\mathrm{Diag}_X(c)+\mathrm{Off}_X(c).
```

*Bounds.* If $k+h\le X$, then $X'=X+k\in[X,2X]$ and $h\le X'$, so Lemma 3.2 at $X'$ gives $\lvert M_{k,h}(X)\rvert\le\frac1X\sum_{m\le X'}\tau(m)\tau(m+h)\le C\,\sigma_{-1}(h)\log^2X$ for $h\ge1$, with an absolute constant $C$. If $k+h>X$, Cauchy–Schwarz gives $\lvert M_{k,h}(X)\rvert\le\frac1X\sum_{m\le X+k+h}\tau(m)^2\ll\frac{X+k+h}X\log^3(X+k+h)\ll(k+h)^4$. For $h=0$ the same argument, with $\sum_{m\le Y}\tau(m)^2\ll Y\log^3Y$ in place of Lemma 3.2, gives $M_{k,0}(X)\ll\log^3X$ for $k\le X$ and $M_{k,0}(X)\ll k^4$ for $k>X$.

*Off-diagonal bound.* Hence $\lvert\mathrm{Off}_X(c)\rvert\le2C\log^2X\sum_{k,h\ge1}2^{-2k-h}\sigma_{-1}(h)+O\bigl(\sum_{s>X}s^5\,2^{-s}\bigr)$. The double sum is $\frac13\sum_h2^{-h}\sigma_{-1}(h)=\frac13\sum_d\frac1{d(2^d-1)}<\infty$, and the remainder is $o(1)$. This is the first claim of (3).

*Diagonal.* For fixed $k$, $M_{k,0}(X)=\mathbb E_Xc^2+O_{k,\varepsilon}(X^{\varepsilon-1})$ since $\tau(m)\ll_\varepsilon m^\varepsilon$. Here $\mathbb E_X\tau^2\sim\frac{\log^3X}{\pi^2}$ and $\mathbb E_Xa_+^2\sim\frac{\log^3X}{3\pi^2}$ (P22 Proposition 1.2(b)). The bounds above dominate $4^{-k}M_{k,0}(X)/\log^3X$ by a summable sequence independent of $X$ (namely $\ll4^{-k}k^4$). Tannery's theorem gives $\mathrm{Diag}_X(c)=(\frac13+o(1))\mathbb E_Xc^2$. That is $(\frac1{9\pi^2}+o(1))\log^3X$ for $a_+$ and $(\frac1{3\pi^2}+o(1))\log^3X$ for $\tau$. With the off-diagonal bound this proves (2) for $\mathbb E_X(T_n^+)^2$. For $T_n$ subtract $(\mathbb E_XT_n)^2=O(\log^2X)$, and for $T_n^+$ subtract $(\ln2+o(1))^2$.

*Off-diagonal constant.* For fixed $k,h$, $M_{k,h}(X)-C_c(h;X)=O_{k,h,\varepsilon}(X^{\varepsilon-1})$. So $M_{k,h}(X)/\log^2X\to c(h)$ whenever $C_c(h;X)=(c(h)+o(1))\log^2X$. Ingham's theorem gives this for $c=\tau$ with $c(h)=\frac6{\pi^2}\sigma_{-1}(h)$. Theorem 2.2(2) gives it for $c=a_+$ with $c(h)=c_+(h)$, under (H2). On $k+h\le X$ the terms $2^{-2k-h}M_{k,h}(X)/\log^2X$ are dominated by $C\,2^{-2k-h}\sigma_{-1}(h)$, which is summable and independent of $X$. The terms with $k+h>X$ contribute $o(1)$ in total. By Tannery's theorem, $\mathrm{Off}_X(c)/\log^2X\to2\sum_{k,h\ge1}2^{-2k-h}c(h)=\frac23\sum_h2^{-h}c(h)$. ∎

The uniformity in $h$ of Lemma 3.2 is what justifies exchanging $X\to\infty$ with the sum over shifts at scale $\log^2X$; Ingham's theorem and (H2) are used only at fixed $h$. The constant $\kappa_+$ is **negative**, because the odd shifts dominate and are pointwise non-positive. Both constants are floating-point evaluations of the exact series (*numerical*).

*Finite measurement* (fixed point at scale $2^{-64}$, $T_n$ by the stable backward recursion):

| $c$ | $X$ | $\mathbb ET$ | $\mathbb ET^2$ | $\mathrm{Var}\,T$ | $\mathbb Ec^2$ | diagonal | off-diagonal | off/diag |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $\tau$ | $2^{14}$ | 9.8611 | 113.310 | 16.068 | 171.286 | 57.097 | $+56.213$ | $+0.9845$ |
| $\tau$ | $2^{20}$ | 14.0174 | 251.162 | 54.674 | 424.872 | 141.624 | $+109.538$ | $+0.7734$ |
| $a_+$ | $2^{14}$ | 0.6924 | 11.291 | 10.812 | 52.724 | 17.576 | $-6.285$ | $-0.3576$ |
| $a_+$ | $2^{20}$ | 0.6931 | 31.221 | 30.741 | 132.592 | 44.197 | $-12.976$ | $-0.2936$ |

At $X=2^{20}$ the predicted off-diagonal $\kappa_+\log^2X=-12.87$ matches the observed $-12.98$. For $\tau$ the prediction $+96.74$ is below the observed $+109.54$, because of Ingham's lower-order terms. The ratio off/diag shrinks like $1/\log X$ in both cases. $\mathrm{Var}(T^+)/\mathrm{Var}(T)=0.6729,0.6092,0.5623$ at $2^{14},2^{17},2^{20}$, approaching $\frac13$ slowly.

These are raw tails. The *displaced* tail $Y_D$ of P22 §1.5 is bounded on average; its variance is a different and open question.

## 4. E1.3 Arithmetic correlations of $E$ against the independent model

### 4.1 The divisor lattice

*CRT densities (paper proof, standard).* $\operatorname{dens}\{n:d_j\mid n+h_j\ \forall j\}=1/\operatorname{lcm}(d_1,\dots,d_r)$ if $\gcd(d_i,d_j)\mid h_j-h_i$ for all $i<j$, and $0$ otherwise. The independent-shift model replaces this by $\prod_j1/d_j$. The script checks the formula by enumeration for $d_j\le12$ and shifts $(0,1,2)$. Summing these densities against the divisor weights yields the singular series $S(\mathbf h)=\prod_p\sigma_p(\mathbf h)$, normalized so that the independent model gives $1$. If the shifts are distinct mod $p$,

```math
\sigma_p=\Bigl(1-\frac1p\Bigr)^{r-1}\Bigl(1+\frac{r-1}p\Bigr)\in\Bigl[1-\frac{(r-1)^2}{p^2},\,1\Bigr],
```

so $\prod_{p>P}\sigma_p\in[1-(r-1)^2/P,1]$. The enclosures of §2.3 use exact rationals for $p<60$, outward-rounded integers at scale $2^{96}$ for $61\le p\le2\cdot10^5$, and this tail bound. They contain $S(0,1)=6/\pi^2$.

For consecutive shifts, $S=0.6079,0.3943,0.2247,0.1460,0.0735,0.0491$ for $r=2,\dots,7$: **at the level of raw divisor values the arithmetic correlations differ from the independent model by $O(1)$ factors from $r=2$ on.** The deviation comes only from primes dividing a difference ($p<r$ for consecutive shifts), plus the universal factor $\prod_p(1-O(r^2/p^2))$. At $r=2$ this is Ingham's theorem; for $r\ge3$ the identification of $S$ with the actual leading coefficient is conditional.

### 4.2 Marks: the joint law of $U=\operatorname{odd}(\tau)\bmod4$

The comparison model of CC-49 uses the marks $U(m)$ (odd part of $\tau(m)$), not $\tau$. Write $\chi_4(U(m))=\prod_p\psi(v_p(m))$ with $\psi(v)=\chi_4(\operatorname{odd}(v+1))$. Then $\psi(0)=\psi(1)=1$, and $\psi(v)=-1$ requires $v\ge2$.

**Proposition 4.1 (paper proof).** For distinct shifts $\mathbf h$, the vector $(\chi_4(U(n+h_j)))_j$ has a limiting joint law. Its Fourier coefficients are

```math
\lim_{X\to\infty}\mathbb E_X\prod_{j\in A}\chi_4(U(n+h_j))=\prod_p\mathbb E_p\Bigl[\prod_{j\in A}\psi(v_p(n+h_j))\Bigr],\qquad A\subseteq\{1,\dots,r\}.
```

If $p^2\nmid h_i-h_j$ for all $i\ne j$, the local factor is $1-2\lvert A\rvert q_p$ with $q_p=\Pr(\psi(v_p)=-1)\le p^{-2}$. The i.i.d.-mark model replaces it by $(1-2q_p)^{\lvert A\rvert}$.

*Proof.* The function depends on $n$ only through the squarefull parts of the $n+h_j$. Fix $P$. Outside a set of upper density $\le r\sum_{p>P}p^{-2}$, no $p>P$ has $p^2\mid n+h_j$, and the event is then periodic mod $\prod_{p\le P}p^{K}$ up to density $O(r\sum_{p\le P}p^{-K})$. CRT gives the product over $p\le P$; let $K\to\infty$, then $P\to\infty$. At $p$ with $p^2\nmid h_i-h_j$, at most one $j$ has $v_p(n+h_j)\ge2$, so $\prod_{j\in A}\psi-1=\sum_{j\in A}(\psi(v_j)-1)$. ∎

For consecutive shifts and $r\le7$, only $p=2$ has $p^2$ dividing a difference (the difference 4). The script computes the 2-adic joint law exactly by enumeration mod $2^{16}$. *Numerical* (exact formula, odd primes $\le20000$): the total-variation distance between the true limiting joint law and i.i.d. marks with the same marginal is

| $r$ | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- |
| TV | 0.02724 | 0.05594 | 0.07550 | 0.08820 | 0.10648 | 0.12319 |

Here $\Pr(U\equiv1\bmod4)=0.752252$, inside P22's certified interval $[0.752169,0.752294]$. A rigorous but crude upper bound $\sum_p\mathrm{TV}_p$ (with $\mathrm{TV}_p=rq_p(1-(1-q_p)^{r-1})$ at odd $p$) is $0.0598$ at $r=2$ and $0.741$ at $r=7$ (script: $\le0.05973$ and $\le0.74033$, rounded up). *Finite check* ($n\le2^{20}$): $\mathbb E\chi_4(U(n))=0.50449$ (limit $0.50450$). $\mathbb E\chi_4(U(n))\chi_4(U(n+1))=0.20010$ against the limit $0.20005$ and the i.i.d. value $0.25452$.

**Conclusion.** At fixed adjacent arguments the marks are measurably correlated, by TV about $0.03$ at $r=2$ rising to $0.12$ at $r=7$. The deviation is dominated by $p=2$ (adjacent integers cannot both be even) and $p=3$. The i.i.d.-mark ingredient of the comparison model is therefore false at fixed shifts, already at $r=2$.

### 4.3 Where the column model can still be right (heuristic)

Column $t$ of CC-49 receives the sources $m$ with $m-V(m)=t$, $V=v_2(\tau)$. Since $V(m)=\sum_pv_2(v_p(m)+1)\ge\#\{p\parallel m\}$ has typical size $\log\log m$, two sources in nearby columns differ by $h=\Delta t+V(m')-V(m)$. That difference is spread over a range of width about $\sqrt{\log\log m}$. Column-level correlations are averages of the fixed-shift correlations of §4.1–4.2 over this law of $h$. The $p$-adic deviations average to zero when $h$ is equidistributed modulo $p^k$, because uniform averaging over $h$ makes $n$ and $n+h$ independent $p$-adically. So the column-level deviation is governed by how fast $V(m+h)-V(m)$ equidistributes modulo small prime powers. Heuristically, through a local limit theorem for $\omega$-type functions at shifted arguments, that is at a rate no better than $(\log\log X)^{-1/2}$.

This is the scale at which arithmetic correlations and the model separate: never at any fixed polynomial or logarithmic scale, but at a doubly logarithmic one. Two consequences, both heuristic and labelled *Open*:

- The real columns of $E$ do not have the exact $Q_\infty$ moments that define $\mathcal I_{D,r}$ at any finite $X$.
- A proof through $\mathcal I_{D,r}$ (P22 Theorem 2.2, $r_{\min}\ge7$) would need an approximate-moment version with explicit $(\log\log X)^{-c}$ errors, together with a joint local limit theorem for $(V,U)$ at $\ge7$ shifted arguments.

Neither is available.

## 5. E2 $\ln2$: the Weyl-sum form of $D^+<1$ and exact numerator laws

The denominator-only routes CC-43, CC-50, OP-11, GF-09 and GF-28 are not repeated. Write $s_N=\sum_{k\le N}2^{N-k}/k=A_N/Q_N$ in lowest terms, $x_N=\{s_N\}$ and $r_N=\sum_{k\ge1}((N+k)2^k)^{-1}$. Then $\{2^N\ln2\}=\{x_N+r_N\}$, $r_N\sim1/N$, and $s_{N+1}=2s_N+1/(N+1)$, so $x_{N+1}=\{2x_N+1/(N+1)\}$ (the BBP map). The script checks $\{2^N\ln2\}=x_N+r_N$ to 38 bits for $N\le300$ against $2^{16}+96$ certified binary digits.

### 5.1 $D^+<1$ is a single Weyl-sum condition

Let $S_N(h)=\frac1N\sum_{n<N}e(h\,2^nx)$.

**Proposition 5.1 (paper proof).** For every real $x$:

1. If $D_N(x;2)\ge1-\varepsilon$ with $\varepsilon\in[0,1]$, then for every $\delta'>0$ a proportion $\ge1-\varepsilon-\delta'$ of the points lies in an arc of length $\le\varepsilon+\delta'$, and $\lvert S_N(1)\rvert\ge(1-\varepsilon)\cos(\pi\varepsilon)-\varepsilon$.
2. If $\lvert S_N(1)\rvert\ge1-\eta$, then $D_N\ge1-2\delta-\eta/(1-\cos2\pi\delta)$ for every $\delta\in(0,\frac12)$.
3. Hence $D^+(x;2)=1\iff\limsup_N\lvert S_N(1)\rvert=1$. In particular, $\limsup\lvert S_N(1)\rvert\le0.9997$ implies $D^+(x;2)\le0.9999$, since $(1-\varepsilon)(1-(22\varepsilon/7)^2/2)-\varepsilon=0.9997999506\ldots>0.9997$ at $\varepsilon=10^{-4}$ (exact rational).

*Proof.* (1) Let $\delta'>0$ with $\varepsilon'=\varepsilon+\delta'\le1$. Since $D_N$ is a supremum over half-open intervals, which need not be attained, some half-open $J$ has $\lvert A_N(J)/N-\lvert J\rvert\rvert\ge1-\varepsilon'$. Such $J$ is either short ($\le\varepsilon'$) with mass $\ge1-\varepsilon'$, or long ($\ge1-\varepsilon'$) with mass $\le\varepsilon'$; in the second case its complement is an arc around 0. Points in an arc of length $\varepsilon'$ centred at $c$ satisfy $\mathrm{Re}\,e(x-c)\ge\cos\pi\varepsilon'$, as $\cos$ decreases on $[0,\pi]$. So $\lvert S_N(1)\rvert\ge(1-\varepsilon')\cos(\pi\varepsilon')-\varepsilon'$; let $\delta'\to0^+$. (2) Choose $c$ with $\lvert S_N(1)\rvert=\frac1N\sum\cos2\pi(x_n-c)$. Then $\frac1N\sum(1-\cos2\pi(x_n-c))\le\eta$, so the mass outside the arc $\lvert x-c\rvert<\delta$ is $\le\eta/(1-\cos2\pi\delta)$. Take $J=[c-\delta,c+\delta)$ if this arc avoids 0, and otherwise the half-open complement $[c+\delta,1+c-\delta)$ (mod 1). (3) Use $\cos t\ge1-t^2/2$ and $\pi<22/7$. ∎

**Proposition 5.2 (transition minorant, paper proof).** $\mathbf 1_{[1/4,3/4]}(x)\ge\frac14-\frac12\cos2\pi x+\frac14\cos4\pi x=\frac{c^2-c}2$, where $c=\cos2\pi x$. For $x$ not dyadic, digits $n+1$ and $n+2$ differ exactly when $\{2^nx\}\in[1/4,3/4)$. So the transition density is at least $\frac14-\frac12\mathrm{Re}\,S_N(1)+\frac14\mathrm{Re}\,S_N(2)$. For $x=\ln2$ one may use $x_n$ in place of $2^n\ln2$, since $\sum_{n<N}r_n=O(\log N)$. The minorant is optimal among $\alpha+\beta c+\gamma c^2$: maximize $\alpha+\gamma/2$ subject to $p\le0$ on $(0,1]$ and $p\le1$ on $[-1,0]$, which gives mean $\frac14$.

*Proof.* $(c^2-c)/2\in[0,1]$ for $c\in[-1,0]$ and $\le0$ for $c\in(0,1]$. The script checks the identity and the bounds exactly on a rational grid. ∎

### 5.2 The band law: exact $p$-adic structure of the BBP state

**Theorem 5.3 (paper proof).** Let $N\ge2$ and let $p$ be an odd prime with $\sqrt N<p\le N$ (that is, $p^2>N$ and $p\le N$); put $m=\lfloor N/p\rfloor$, so $1\le m<p$. Then

```math
v_p(Q_N)=\begin{cases}1,& p\nmid A_m,\\ 0,& p\mid A_m,\end{cases}\qquad\qquad p\,s_N\equiv2^{N-m}\,s_m\pmod p .
```

So the $p$-component of $x_N$ (its CRT summand with denominator $p$) is $\langle2^{N-m}A_mQ_m^{-1}\bmod p\rangle/p$.

*Proof.* The multiples of $p$ up to $N$ are $ip$, $i\le m<p$, each with $v_p(ip)=1$; all other terms of $s_N$ are $p$-integral. So $p\,s_N\equiv\sum_{i\le m}2^{N-ip}/i\pmod p$. Since $2^{p-1}\equiv1$, $2^{-ip}\equiv2^{-i}$, so the sum is $\equiv2^N\sum_{i\le m}2^{-i}/i=2^{N-m}s_m$. Every prime factor of $Q_m$ is $\le m<p$, so $s_m$ is a $p$-adic unit times $A_m$. ∎

- $m=1$ is the top band $(N/2,N]$ of OP-11. There $A_1=1$, so every top-band prime survives with component $\langle2^{N-1}\rangle/p=\langle2^{N-p}\rangle/p$.
- $A_1,\dots,A_6=1,5,16,131,661,1327$. So $p=5$ drops out in band $m=2$ (for $10\le N<15$), $p=131$ in band $4$, and so on.

The large primes ($\sqrt N<p\le N$) carry $\sum\log p/N=0.9302,0.9514,0.9625$ at $N=1000,2000,3000$, against $\log Q_N/N=0.9884,0.9951,0.9968$. The dropped share is $0.00438,0,0.00180$. Up to $N=3000$ there are 21 dropped pairs $(p,m)$, e.g. $(5,2),(17,11),(19,15),(29,13)$, and 1735 dropped events $(N,p)$. The script verifies Theorem 5.3 for all $661{,}864$ pairs with $N\le3000$.

**Single-prime behaviour along a band window.** Fix $p$ and $1\le m<p$ with $p\nmid A_m$, and let $N$ run through the band window $[mp,(m+1)p)$. Then $\lfloor N/p\rfloor=m$ and $p^2>N$, and by Theorem 5.3 the $p$-component is $u_N/p$ with $u_N\equiv c\,2^{N-mp}\pmod p$, where $c=u_{mp}\ne0$. Let $t=\operatorname{ord}_p(2)$, a divisor of $p-1$. The window has $p=(p-1)+1$ terms, so $u_N$ runs through the coset $c\langle2\rangle\subseteq\mathbb F_p^\times$ of size $t$. Each element is visited exactly $(p-1)/t$ times, except $c$, which is visited once more.

- If 2 is a primitive root mod $p$ ($t=p-1$), every nonzero residue occurs once and $c$ twice. The window average of $e(u_N/p)$ is $\frac1p(-1+e(c/p))$, of modulus $\le2/p$. This is equidistribution on $\mathbb F_p^\times$ up to $O(1/p)$, not exact equidistribution.
- If $t<p-1$, only a coset of a proper subgroup is visited. For small $t$ there is no cancellation. For $m=1$ the window averages have modulus $0.4926$ at $p=7$ ($t=3$) and $0.5467$ at $p=31$ ($t=5$); a Mersenne prime $p=2^q-1$ has $t=q$. In general the Gauss-period bound $\lvert\sum_{u\in c\langle2\rangle}e(u/p)\rvert\le((k-1)\sqrt p+1)/k<\sqrt p$, with $k=(p-1)/t$ (external, classical, via Gauss sums), gives cancellation along the window only when $t$ is large compared with $\sqrt p$. That holds for almost all primes, since $\operatorname{ord}_p(2)>p^{1/2}$ for all but $o(\pi(x))$ primes $p\le x$ (Erdős–Murty 1999, external).

The script checks the coset structure and the multiplicities exactly for all $333$ pairs with $m\in\{1,2\}$, odd $p\le1000$ and $p\nmid A_m$; $133$ of them have 2 as a primitive root and $200$ do not. It checks the $2/p$ bound at every primitive-root pair and the Gauss-period bound at every pair in floating point. So each large-prime phase is explicit, and individually it is only as well distributed as $\langle2\rangle\bmod p$ allows. Everything difficult lies in the *joint* behaviour of the $\asymp N/\log N$ simultaneous components.

**Proposition 5.4 (Glaisher–Wieferich numerator law, paper proof).** For an odd prime $p$ and $0\le j<p-1$, with $q_p(2)=(2^{p-1}-1)/p$:

```math
s_{p-1-j}\equiv2^{p-1-j}\Bigl(q_p(2)+\sum_{i=1}^{j}\frac{2^{i-1}}i\Bigr)\pmod p .
```

In particular $p\mid A_{p-1}$ if and only if $p$ is a Wieferich prime ($1093$ and $3511$ below $10^5$).

*Proof.* In $\mathbb Z_{(p)}[x]$, $\sum_{k=1}^{p-1}x^k/k\equiv(1-x^p-(1-x)^p)/p\pmod p$, because $\binom pk/p\equiv(-1)^{k-1}/k$. At $x=\frac12$ this gives $\sum_{k<p}2^{-k}/k\equiv(1-2^{1-p})/p\equiv q_p(2)$. Removing $k=p-i$, $i\le j$, removes $2^{-(p-i)}/(p-i)\equiv-2^{i-1}/i$. Finally $s_N=2^N\sum_{k\le N}2^{-k}/k$. ∎

Script: verified for $11\le p\le3000$, $j\le5$, against exact $s_N$. The primes dividing $A_{p-1-j}$ are $j=0$: $1093$; $j=3$: $19,149$; $j=5$: $17,173,233,401$; none for $j=1,2,4$.

### 5.3 What would suffice, in numerator form

For $n\ge2$ let $P_n$ be the set of odd primes $p$ with $\sqrt n<p\le n$ and $p\nmid A_{m_p}$, where $m_p=\lfloor n/p\rfloor$ (so $m_p<\sqrt n$). By Theorem 5.3, $Q_n=\bigl(\prod_{p\in P_n}p\bigr)Q_n'$, where every prime factor of $Q_n'$ is $2$ or at most $\sqrt n$. The partial-fraction (CRT) decomposition of $x_n$ is therefore

```math
x_n\equiv R_n+\sum_{p\in P_n}\frac{u_{n,p}}p\pmod 1,\qquad u_{n,p}\equiv2^{n-m_p}A_{m_p}\,\overline{Q_{m_p}}\pmod p,
```

where $\overline{Q}$ is the inverse of $Q$ mod $p$ and $R_n$, with denominator dividing $Q_n'$, is the summand supported on $2$ and on the primes $q\le\sqrt n$. No prime is counted twice. The boundary band $m=\lfloor\sqrt n\rfloor$ contributes only its primes $p>\sqrt n$; a prime $q\le\sqrt n$ in its interval $(n/(m+1),n/m]$ (e.g. $q=3$ at $n=10$, $q=5$ at $n=26$), for which $v_q(Q_n)$ may exceed $1$, belongs to $R_n$. The script checks the factorization of $Q_n$ for every $2\le n\le3000$. Since $\{2^n\ln2\}=\{x_n+r_n\}$ and $\sum_{n<N}r_n=O(\log N)$, $\bigl\lvert S_N(1)-\frac1N\sum_{n<N}e(x_n)\bigr\rvert\le\frac{2\pi}N\sum_{n<N}r_n\to0$. Proposition 5.1 then gives (the terms $n<2$ do not affect the limsup)

```math
D^+(\ln2;2)<1\iff\limsup_{N}\Bigl|\frac1N\sum_{2\le n<N}e(R_n)\prod_{p\in P_n}e\Bigl(\frac{u_{n,p}}p\Bigr)\Bigr|<1.
```

So the required "cancellation bound on the numerator recurrence" is an $\eta$-saving, for some fixed $\eta>0$, in this average of products of large-prime phases. The phases are explicit in the numerators $A_m$, $m<\sqrt n$. Individually, each runs through a coset of $\langle2\rangle\bmod p$ along its band window (§5.2); this is equidistribution on $\mathbb F_p^\times$ up to $O(1/p)$ only when 2 is a primitive root mod $p$. Only a bounded loss is allowed: $\lvert\cdot\rvert\le0.9997$ suffices for $D^+\le0.9999$. This is an exact reformulation, not a new estimate.

### 5.4 The quantitative gap (Bailey–Crandall versus what is needed)

- *Needed* (Proposition 5.1): $\lvert\sum_{n<N}e(2^n\ln2)\rvert\le0.9997N$ for all large $N$. By Proposition 5.2, $2\,\mathrm{Re}\,S_N(1)-\mathrm{Re}\,S_N(2)\le1-\eta$ already gives positive transition density.
- *Bailey–Crandall Hypothesis A* (Experimental Math. 10 (2001), external): roughly, a BBP-type sequence either has a finite attractor or is equidistributed. Equidistribution of $(x_n)$ is equivalent to normality of $\ln2$ in base 2, and gives $S_N(h)\to0$ for every $h\ne0$. This is vastly more than needed: one frequency, and only a bounded loss.
- *Known* (paper proof from external input): $\mu(\ln2)\le3.5746$ (Marcovecchio 2009) bounds each run by $(\mu-1+\varepsilon)n$, so transitions up to $N$ number at least $\log N/\log(\mu+\varepsilon)-O(1)$. Each one puts some $\{2^n\ln2\}$ in $[1/4,3/4)$, which gives $\mathrm{Re}\,S_N(1)\le1-(1+o(1))\frac{\log N}{N\log\mu}$. The gap between this and the needed $1-\eta$ is a factor $N/\log N$ in the saving. By P22 Corollary 3.2 no improvement of $\mu$ alone can close it.
- *Exponential-sum technology* (external: Korobov; Bourgain–Glibichuk–Konyagin 2006; Bourgain 2005 for general moduli) gives $o(H)$ for $\sum_{t<H}e(a2^t/q)$ only when $H\ge q^\delta$. Along the BBP orbit, $x_{n+t}=\{2^tx_n+O(2^t/n)\}$ is pure doubling of $A_n/Q_n$ only for $t\le(1-\delta)\log_2n$, while $\log Q_n=(1+o(1))n$ (finite: $0.9968$ at $n=3000$). The available windows have length $\asymp\log\log Q_n$ against the required $Q_n^\delta$, a doubly exponential gap. This is the BBP-map form of the CC-50 window–denominator barrier.

*Finite measurement* (exact transition counts from $2^{16}$ certified digits; $\lvert S_N(1)\rvert$ from 53-bit points):

| $N$ | $2^{10}$ | $2^{12}$ | $2^{14}$ | $2^{16}$ |
| --- | --- | --- | --- | --- |
| transitions | 529 | 2107 | 8209 | 32824 |
| per digit | 0.5166 | 0.5144 | 0.5010 | 0.5009 |
| $\lvert S_N(1)\rvert$ | 0.0337 | 0.0248 | 0.0030 | 0.0013 |
| $\log N/\log\mu$ | 5.4 | 6.5 | 7.6 | 8.7 |

The data sit far inside the sufficient region. **$D^+(\ln2;2)\le0.9999$ remains open.**

## 6. E2.3 Missing-estimate map for the 35 open benchmark constants

By Proposition 5.1, for every constant the target $D^+<1$ in base 2 is equivalent to $\limsup\lvert S_N(1)\rvert<1$. The table names, per cluster, the sharpest arithmetic input that would feed that saving and that is missing. These are research targets, not claimed reductions. The 35 IDs are exactly those with `full_normality = "open"` and `evidence = "open"` in `docs/benchmarks/classical-constants.toml` (script section B). BC-37 ($E$) is excluded because its evidence is `external` (pinned external $D^+<1$, independent verification open). BC-50 ($\alpha(2,3)\alpha(2,5)$) is excluded because its evidence is `paper`: there $D^+\le4/11+2.85\times10^{-10}<1$ is already proved (ST-32), although full normality is open. The other 13 excluded constants have a proved normality or nonnormality status.

| cluster | IDs | known input | single sharpest missing estimate |
| --- | --- | --- | --- |
| algebraic irrationals | BC-01–BC-07 | BBCP: $\gg N^{1/d}$ ones; Adamczewski–Bugeaud superlinear complexity (external) | A positive-proportion version of BBCP. For $\sqrt2$, with $a_n=\lfloor2^n\sqrt2\rfloor$ and $\varepsilon_n=2^{2n+1}-a_n^2=\{2^n\sqrt2\}(2^{n+1}\sqrt2-\{2^n\sqrt2\})$: a positive lower density of $n$ with $\{2^n\sqrt2\}$ in a fixed closed subinterval of $(0,1)$, e.g. $[\frac14,\frac34]$; up to $O(2^{-n})$ this is $\varepsilon_n/2^{n+1}\in[\frac{\sqrt2}4,\frac{3\sqrt2}4]$ (the norm-form residue in degree $d$). The subinterval must avoid $0$ and $1$: by the doubling map an arc of length $\eta$ carrying almost all points lies within $2\eta$ of $0$, so mass near $0$ is compatible with $D^+=1$ |
| $\ln2,\ln3,\ln10,\pi,\pi^2,\arctan\frac12$ | BC-08–BC-13 | BBP-type series in base $2^k$ (external for $\pi,\pi^2$); band law, Thm. 5.3 | An $\eta$-saving in the BBP-orbit Weyl sum, i.e. joint equidistribution of the large-prime phases of §5.3 along $n$. Beyond subgroup-sum methods by the gap of §5.4 |
| $e^\pi$, $2^{\sqrt2}$ | BC-14, BC-15 | transcendence (Gelfond–Schneider) | Any radix-compatible rational approximation scheme at all (no BBP-type series is known); approximation quality alone is insufficient (P22 Cor. 3.2) |
| $e,1/e,e^2,C_1$ | BC-16–BC-18, BC-21 | factorial series, $\mu=2$ (external); for $C_1=I_1(2)/I_0(2)=[0;1,2,3,\dots]$, convergents $p_K/q_K$ with $K!\le q_K\le(K+1)!$ | For $e,1/e,e^2$: equidistribution of $2^n\sum_{k\le K}1/k!$ modulo 1 for $n\asymp K\log K$, i.e. of the residues $2^n\,(K!\,e_K)\bmod K!$ on windows short against their periods. For $C_1$: the same for $2^np_K\bmod q_K$. $\mu=2$ cannot help (P22 Cor. 3.2) |
| $\Gamma(\frac14),\Gamma(\frac13)$ | BC-19, BC-20 | Chudnovsky transcendence; AGM/elliptic formulas (external) | A radix-adapted series with integer structure in base 2 (none known), before any distribution estimate |
| $\zeta(3)$ | BC-22 | top band to power 3 (P22 Prop. 4.4); binary BBP-type ladder (external) | The $\ln2$ estimate with cubed top-band denominators |
| Dirichlet $L(1,\chi)$ | BC-23–BC-26 | $L(1,\chi_4)=\pi/4$ (digits of $\pi$ shifted); the others are $\pi/(3\sqrt3)$, $\ln(1+\sqrt2)/\sqrt2$, $\ln(2+\sqrt3)/\sqrt3$ | For BC-23, as for $\pi$. For BC-24–BC-26, the BBP or logarithmic saving for a product with an algebraic irrational multiplier, which the rational-operation results of Paper X do not cover |
| dense Lambert/divisor | BC-38 $E_{\rm odd}$, BC-39 $E_+$, BC-43 $\sum\sigma(n)2^{-n}$ | unconditional tail means; peeling (Thm. 1.5, Cor. 1.6); $r_{\min}\ge7$ (P22) | A column-level joint local limit theorem for $(v_2(c),\operatorname{odd}(c)\bmod2^K)$ at $\ge7$ shifted arguments, with explicit $(\log\log X)^{-c}$ error (§4.3). For BC-39 add the sign-periodic structure (§2.5) and the 2-adic factor $\rho$ |
| dense modular | BC-31 $E_2^4$, BC-35 $\Theta_3^3$, BC-36 $E_4(\frac12)$, BC-32 $P_2$ | coefficient formulas (GF-08, GF-17); carry windows $O(\log n)$ ($\sigma_3$, $r_3$) or $O(\sqrt n)$ ($p(n)$) | The same column-level correlation estimate for signed modular coefficients ($\eta^4$, $r_3$, $\sigma_3$). For $P_2$ the carry window $\asymp\sqrt n$ first needs a fractional-part law for $\sum_kp(n+k)2^{-k}$ |
| $\psi=\sum1/F_n$ | BC-42 | $E_{\rm odd}$-type in radix $\varphi^2$ (P22 Prop. 4.2) | An Erdős–Borwein theory in radix $\varphi^2$, then a transfer between multiplicatively independent radices |
| Cahen | BC-44 | $\mu=3$; exact reduced denominators (P22 Prop. 4.1) | Equidistribution of $2^n$ modulo products of Sylvester numbers on windows short against $\operatorname{ord}_{s_j}(2)$ |

## 7. Lean 4 blueprint

Statements only; not compiled here. Names follow `NormalityChecker/Phase22Cores.lean` (`erdosBorweinPlusCoeff`) and `NormalityChecker/ClassicalBarriers.lean` (`tauOdd`).

```lean
-- B1. Parity peel (from erdosBorweinPlusCoeff_odd_iff).
theorem erdosBorweinPlusCoeff_emod_two {n : ℕ} (hn : 0 < n) :
    erdosBorweinPlusCoeff n % 2 = if IsSquare n then 1 else 0

-- B2. Mod-4 value on squares: a_+(k^2) ≡ λ(k) (mod 4), λ(k) = (-1)^Ω(k).
theorem erdosBorweinPlusCoeff_sq_mod_four {k : ℕ} (hk : 0 < k) :
    (erdosBorweinPlusCoeff (k ^ 2) : ZMod 4) = (((-1 : ℤ) ^ (ArithmeticFunction.cardFactors k) : ℤ) : ZMod 4)

-- B3. Theta peeling identity (b = 2), termwise from B1 and summability of a_+(n) 2^{-n}.
--     (`/` on ℤ is Euclidean division, which is floor division for the divisor 2.)
theorem erdosBorweinPlus_theta_peel :
    (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) + 1)) =
      (∑' k : ℕ, (2 : ℝ) ^ (-(((k + 1) ^ 2 : ℕ) : ℤ))) +
        2 * ∑' n : ℕ, ((erdosBorweinPlusCoeff (n + 1) / 2 : ℤ) : ℝ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))

-- B4. Peel difference: ⌊τ/2⌋ − ⌊a_+/2⌋ = τ(n/2)·[2 ∣ n].
theorem floor_half_tau_sub_floor_half_plus {n : ℕ} (hn : 0 < n) :
    (n.divisors.card : ℤ) / 2 - erdosBorweinPlusCoeff n / 2 =
      if 2 ∣ n then ((n / 2).divisors.card : ℤ) else 0

-- B5. Sparse bounded coefficients give K_2 (Lemma 1.4), finite form; combine with
--     NormalityChecker.SharpTranslation.sharp_translation for Theorem 1.5.

-- B6. Transition minorant (Prop. 5.2).
theorem transition_minorant (x : ℝ) :
    1/4 - Real.cos (2 * Real.pi * x) / 2 + Real.cos (4 * Real.pi * x) / 4 =
      (Real.cos (2 * Real.pi * x) ^ 2 - Real.cos (2 * Real.pi * x)) / 2

-- B7. Glaisher congruence (Prop. 5.4, j = 0), in ZMod p.
theorem glaisher_half {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (∑ k ∈ Finset.Ico 1 p, (2 : ZMod p) ^ (p - 1 - k) * (k : ZMod p)⁻¹) =
      (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod p)

-- B8. Band law (Thm 5.3), valuation part, for odd p with N < p^2.
theorem ln2_prefix_band_law {N p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hN : N < p ^ 2) (h1 : p ≤ N) :
    padicValNat p (ln2Prefix N).den = if p ∣ (ln2Prefix (N / p)).num.natAbs then 0 else 1
```

B1, B3 and B4 are short consequences of existing Phase 22 lemmas. B2 needs the multiplicative description of $\tau(k^2)$ mod 4. B7 is the polynomial congruence $\binom pk/p\equiv(-1)^{k-1}/k$. B8 needs a definition `ln2Prefix N : ℚ` $=\sum_{k\le N}2^{N-k}/k$.

## 8. Verification

`python -B scripts/phase23_classical.py` (standard library; about 10–20 s; $4{,}580{,}653$ assertions; exits 0) checks every displayed number:

- **P.** The alternating divisor sum for $n\le3000$. Parity and mod-4 laws for all $n\le2^{20}$. $\sum\chi_4(a_+)=L(\sqrt X)$ at five $X$. The characterization of $v_2(a_+)=1$ and the mod-8 sign rule for all $n\le2^{20}$, the exact $\alpha=1$ count identity, residue counts mod 8, and $N_j(2^{20})$. The truncated theta peeling identity, exactly. $B_1(\tau)-B_1(a_+)=E(4)$ coefficientwise. Certified digits, $D_N$ and the SY-04 inequalities.
- **C.** The exact local recursion against Ingham's factors; the closed forms of Proposition 2.1 for $k\le20$; $\rho(h)$; pointwise signs; the $r$-point ratios; singular-series enclosures; CRT densities by enumeration; finite two- and three-point ratios.
- **T.** Fixed-point tails, the unconditional sandwich, the diagonal/off-diagonal split, the predicted off-diagonal terms, the closed form of $\kappa_\tau$, and Lemma 3.2 at $1038$ pairs $(X,h)$.
- **M.** The 2-adic joint mark law by enumeration mod $2^{16}$, TV bounds and values, and finite mark moments.
- **L.** Exact $s_N$ for $N\le3000$, the band law for $661{,}864$ pairs, the factorization $Q_N=\prod_{p\in P_N}p\cdot Q_N'$ of §5.3 for $2\le N\le3000$, the band-window coset structure for $333$ pairs, Glaisher–Wieferich for $p\le3000$, Wieferich primes below $10^5$, the exact $0.9997$ threshold, the minorant identity, the BBP state against certified digits, and transitions.
- **B.** The 35-constant map against the fixed roster.

Values labelled *numerical* (TV values, $c_+(h)$, $\kappa_\tau$, $\kappa_+$, predicted off-diagonal terms, window phase averages) are floating-point evaluations of exact formulas and are not certified. Values labelled *finite measurement* bear on no limit.

## 9. Open questions

1. Prove (H2), or locate a reference, so that Theorem 2.2(2) becomes unconditional; the asymptotic $C_+(1;X)\sim-\frac2{\pi^2}\log^2X$ is the first case.
2. A joint local limit theorem for $(V,U)$ at shifted arguments, with explicit error. Does the column-level deviation from $Q_\infty$ decay like $(\log\log X)^{-1/2}$? Can P22's $\mathcal I_{D,r}$ be replaced by an approximate-moment class robust to such errors?
3. The displaced-tail variance of $E_+$ (as opposed to the raw tail, Theorem 3.1).
4. For $\ln2$: any $\eta>0$ with $\limsup\lvert S_N(1)\rvert\le1-\eta$, equivalently an $\eta$-saving in the band-phase average of §5.3. Even a saving restricted to the top band ($m=1$) is open.
5. Do the dropped band primes ($p\mid A_m$ in band $m$) have any structure beyond Proposition 5.4? Up to $N=3000$ they carry less than $0.5\%$ of the large-prime mass.
