# Mahler's binary partition constant and net carry complexity

Phase 23, Track D3 (Mahler's constant $X_b$) and Track B3 (carry cancellation beyond raw signed-digit width). Fix an integer radix $b\ge2$. Notation follows [Phase 22, partitions-carry-and-lemma-s](../phase22/partitions-carry-and-lemma-s.md) and [Phase 22, odd-characters-and-kernel-quotient](../phase22/odd-characters-and-kernel-quotient.md). Write $x_n=\{b^nx\}$, let $D_N(x;b)$ be the extreme discrepancy of $x_0,\dots,x_{N-1}$ over intervals $[\alpha,\beta)\subseteq[0,1)$, and let $\|t\|$ be the distance from $t$ to the nearest integer. As in Phase 22:

```math
K_b=\{x: D_N(x;b)\to1\},\qquad F_b=\tfrac1{b-1}\mathbb Z,\qquad M_N(w;b)=\frac1N\sum_{n<N}\|b^nw\|,\qquad M_b=\{w: M_N(w;b)\to0\},
```

and $K_b=F_b+M_b$ (Phase 19). For an integer sequence $a$ put $F_b(a)=\sum_{m\ge1}a(m)b^{-m}$. The base-$b$ digits of $x$ are $d_n(x)=\lfloor b\{b^{n-1}x\}\rfloor$, with the convention that an expansion never ends in $(b-1)^\infty$. For $m\ge2$ let $b_m(n)$ be the number of partitions of $n$ into powers of $m$, write $\beta=b_2$, and put

```math
X_{b,m}=\prod_{j\ge0}\bigl(1-b^{-m^j}\bigr)^{-1}=\sum_{n\ge0}b_m(n)\,b^{-n},\qquad X_b=X_{b,2}.
```

Thue–Morse is $t_n=s_2(n)\bmod2$, with $s_2$ the binary digit sum, and the Thue–Morse–Mahler number is $\xi_b=\sum_{n\ge0}t_nb^{-n}$.

**Scope and evidence.** "Paper proof" means proved here, from elementary arguments and the cited results of Phases 19–22. Published theorems used as black boxes are marked **External input**. Exact identities and the inequalities in the theorems below were checked by [`scripts/phase23_binary_partition.py`](../../scripts/phase23_binary_partition.py). It uses the standard library only, with exact `int` and `Fraction` arithmetic for every identity, order, window and inequality certificate. The two exceptions are the comparisons in Corollary 2.2 and the power form $2N^{\log_m2}$ in Theorem 3.4, which involve the irrational numbers $\log_mn$ and are made in floating point with tolerance $10^{-9}$ (§8). The run takes about 6–9 s, performs 609,971 checks and exits 0. These checks are **Finite certificates** of the stated finite instances. Every discrepancy, frequency, density or ratio quoted from the script is a **Finite measurement**. Finite measurements are not evidence for any asymptotic statement. Never read a coefficient congruence, such as $\beta(n)\equiv0\pmod2$, as a digit frequency of $X_b$: the binary digit 1 of $X_2$ has finite frequency $0.5042$ (§6). One cross-model referee audit has been run on this note ([review](reviews/track-b3d3-review.md)), and its findings C1, M1–M4 and m1–m10 are repaired here. Cross-model review is not independent human peer review.

| § | Result | Status |
| --- | --- | --- |
| 1.2 | Theorem 1.1 (tower transfer): $\mathbb Z[1/b]$ acts on every $K_{b^k}$. Hence $X_b\in K_{b^k}\Rightarrow X_{b^{2^r}}\in K_{b^k}$ and $X_{b^{2^r}}\in K_{b^k}\iff D'_rX_b\in K_{b^k}$. Also $X_b\in K_b\Rightarrow X_{b^{2^r}}\in M_b$ for $r\ge1$. For $b=2$, $X_2\in K_{2^k}\iff X_4\in K_{2^k}$ for every $k$ | Paper proof |
| 1.3 | Proposition 1.2 (rate transfer): $M_N(X_{b^{2^r}};b^{2^r})\le\frac1{2N}+2^rD'_rM_{2^rN}(X_b-c;b)$. For $b=2$, $\tfrac13M_{2N}(X_2;2)\le M_N(X_4;4)\le2M_{2N}(X_2;2)+\tfrac1{2N}$ | Paper proof |
| 1.4 | Theorem 1.3 (coset transport): if $X_b\in K_{b^2}$ has class $r\in\mathbb Z/(b+1)$, then $X_{b^2}$ has class $2r$. Also $X_2\in K_4\Rightarrow$ the binary change density of $X_2$ tends to $0$ or to $1$ | Paper proof; class map checked for $b\le24$ |
| 1.5 | $X_b$ is transcendental and has irrationality exponent $2$ | External input (Mahler 1929; Bugeaud 2011) + paper proof |
| 2 | Theorem 2.1 and Corollary 2.2: elementary two-sided bounds $\log_mb_m(n)=\frac12(\log_mn)^2+O(\log n\log\log n)$. The exact certified carry window is $L_\tau(N)=\frac{(\log_2N)^2}{2\log_2b}+O_b(\log N\log\log N)$ for $\tau=N^{-A}$ | Paper proof; windows exact |
| 3.1 | Theorem 3.1: $1/X_{b,m}=Y_{b,m}=\sum_n\varepsilon_m(n)b^{-n}$. For $m=2$, $1/X_b=\frac b{b-1}-2\xi_b$ and $X_2=1/(2-4\tau_{\rm TM})$. Each product truncation is the reciprocal of a truncation of $Y_{b,m}$ | Paper proof; identities exact |
| 3.2 | Theorem 3.3: the base-$b$ digits of $Y_b$ are a 2-block code of Thue–Morse. $Y_b\notin K_b$, $Y_b$ is not normal, and $Y_2$ and $Y_3$ are simply normal. For all $N$, $D_N(Y_b;b)\ge2b^{-2}$ ($b\ge3$) or $\ge\frac14$ ($b=2$). Also $\limsup_ND_N(Y_b;b)\le1-\frac4{15b^2}$ | Paper proof (elementary Thue–Morse counts) |
| 3.3 | Theorem 3.4 (dichotomy): for $m\ge3$, $Y_{b,m}\in M_b\subseteq K_b$ with $M_N\le2N^{\log_m2-1}$. So $X_{b,m}$ is the reciprocal of a kernel element exactly when $m\ge3$ | Paper proof |
| 4 | Theorem 4.1: $T_J=\operatorname{ord}_{D_J}(b)=2^JD_{J-1}$ for $J\ge1$, in every base. This is a power of 2 only for $J=1$ with $b-1$ a power of 2, or for $(J,b)=(2,3)$. The tracked prefix is less than $2/D_{J-1}$ of one period. The analogous m-ary chain orders were checked in 43 cases | Paper proof; exact order tests |
| 4 | Proposition 4.5: $\beta\bmod2^L$ is 2-automatic for every $L\ge1$ (Cartier-operator closure). This does not give an automaton for the digits of $X_2$ | Paper proof; closure identities exact |
| 5.1 | Theorem 5.2 (gauge identity): every sequence radix-equivalent to $a$ is $d+b\delta-S\delta$, where $d$ is the digit sequence of $x$, for a unique integer $\delta$ with $\delta_m=o(b^m)$; without this growth condition $\delta$ is determined only up to $c\,b^{m-1}$ | Paper proof |
| 5.2 | Lemma 5.3 (quantitative Phase 19): $\frac25\mu_N-\frac1N\le1-D_N\le2\sqrt{2\mu_N}$. Theorems 5.4–5.5: the minimal net support $\sigma_N$ satisfies $\frac13\chi_{N-2}\le\sigma\le\chi_N+1$ and is bounded above and below by $\mu_N$ and $1-D_N$ with explicit constants | Paper proof; exact checks on 500 rationals |
| 5.3 | Proposition 5.7: elements of $K_b$ whose coefficient sequences have **signed-digit** width $\asymp N\sqrt{\log N}$ (the wall order of Phase 22) and $\asymp N^2$ (the maximal order) | Paper proof |
| 5.4 | Proposition 5.9: $K_b$ membership of $E_b^4$, $E_b^6$, $E_b^8$, $D(\Theta_3^2)$ and $D(E_b^2)$ is equivalent to concentration of the carry residues $R_{n,L(n)}/b^{L(n)}$ with $L(n)\asymp\log n$ | Paper proof (reformulation) |
| 6 | Discrepancy and support table, base 2, $N=4000$ | Finite measurement |
| 9 | $K_b$ membership, normality, $D^+<1$ and $D^->0$ for $X_b$, $X_{b,m}$ and $E_b^4$ | **Open** |

**Corrections to working hypotheses.** Three hypotheses suggested for this track are false. (i) $\operatorname{ord}_{D_J}(b)$ is not a power of 2: lifting the exponent adds the odd part of $D_{J-1}$ (Theorem 4.1; for example $T_2=12$ in base 2). (ii) Multiplication by $(b-1)/b$ *preserves* $K_b$, because $\mathbb Z[1/b]$ acts on $K_b$. The obstruction runs the other way: recovering $X_b=\frac b{b-1}X_{b^2}$ needs division by $b-1$, which does not preserve $K_b$. (iii) $\beta$ is not a 2-regular sequence over $\mathbb Z$, because 2-regular sequences grow at most polynomially (Allouche–Shallit, *Automatic Sequences*, Thm. 16.3.1) and $\beta$ does not. This does not prevent automaticity modulo a fixed integer. For every fixed $L\ge1$, $\beta\bmod2^L$ *is* 2-automatic (Proposition 4.5). That automaton still gives none for the digits of $X_2$. By Proposition 2.3, certifying the orbit points $x_n$, $n<N$, from the coefficients needs a window $L_\tau(N)\ge\log_2\beta(N)+\log_2(1/\tau)-1$, of order $(\log N)^2$, so no single modulus $2^L$ suffices. For moduli with an odd prime factor, such as $\beta\bmod3$, the argument of Proposition 4.5 fails, and automaticity is not settled here (§9, Problem 4).

## 1. The radix-power tower of Mahler constants

### 1.1 Functional equations

Substituting $z\mapsto z^m$ in $F_m(z)=\prod_{j\ge0}(1-z^{m^j})^{-1}$ gives $(1-z)F_m(z)=F_m(z^m)$. Evaluated at $z=1/b$:

```math
X_{b^m,m}=\Bigl(1-\frac1b\Bigr)X_{b,m},\qquad X_{b^{2^r}}=c_r\,X_b,\qquad c_r=\prod_{j<r}\bigl(1-b^{-2^j}\bigr)=\frac{D'_r}{b^{2^r-1}},\qquad D'_r=\prod_{j<r}\bigl(b^{2^j}-1\bigr).
```

Coefficientwise, $b_m(n)-b_m(n-1)=[m\mid n]\,b_m(n/m)$. So $b_m(mn+i)=b_m(mn)=\sum_{k\le n}b_m(k)$ for $0\le i<m$. The script checks the recurrence and the product form for $m=2,3,4,5$, and the parity $2\mid\beta(n)$ for $2\le n\le17{,}000$.

### 1.2 Tower transfer

**Theorem 1.1.** Let $b\ge2$, $k\ge1$ and $r\ge0$.

(a) $K_{b^k}$ is a $\mathbb Z[1/b]$-module, and so is $M_b=M_{b^k}$.

(b) If $X_b\in K_{b^k}$, then $X_{b^{2^r}}\in K_{b^k}$. More precisely, $X_{b^{2^r}}\in K_{b^k}\iff D'_rX_b\in K_{b^k}$.

(c) If $X_b\in K_b$ and $r\ge1$, then $X_{b^{2^r}}\in M_b$. In particular $X_{b^{2^r}}\in K_{b^{2^r}}$, with zero class in $K_{b^{2^r}}/K_b$. Contrapositively, $X_{b^{2^r}}\notin K_{b^{2^r}}$ implies $X_b\notin K_b$.

(d) For $b=2$, $X_4=\frac12X_2$, so $X_2\in K_{2^k}\iff X_4\in K_{2^k}$ for every $k$. More generally $X_{2^m,m}=\frac12X_{2,m}$, so $X_{2,m}\in K_{2^k}\iff X_{2^m,m}\in K_{2^k}$.

*Proof.* (a) Phase 19's universal scalar ring theorem, applied in radix $b^k$, says that a reduced rational $u/v$ acts on $K_{b^k}$ exactly when every prime of $v$ divides $b^k$, that is, divides $b$. The statement for $M_b$ follows from $\|nt\|\le|n|\|t\|$ and from $\|b^{n}(w/b)\|=\|b^{n-1}w\|$ for $n\ge1$; Phase 22 Theorem 7.1 gives $M_b=M_{b^k}$. (b) $c_r\in\mathbb Z[1/b]$, and $D'_rX_b=b^{2^r-1}X_{b^{2^r}}$. (c) Write $X_b=c+w$ with $c=j/(b-1)$ and $w\in M_b$. For $r\ge1$, the factor $j=0$ of $D'_r$ is $b-1$, so $c_rc\in\mathbb Z[1/b]\subseteq M_b$. Also $c_rw\in M_b$ by (a). So $X_{b^{2^r}}=c_rc+c_rw\in M_b=M_{b^{2^r}}\subseteq K_{b^{2^r}}$. (d) $D'_1=b-1=1$. $\square$

The converse of (b) needs division by $D'_r$, which is not available: for $b\ge3$, $\frac1{(b-1)^2}\notin K_b$ (script). The tower is therefore *monotone*. Membership propagates up from $X_b$ in base $b$ to $X_{b^{2^r}}$ in base $b^{2^r}$, and non-membership propagates down. For $b=2$ the first step is an equivalence.

### 1.3 Rate transfer

**Proposition 1.2.** Let $B=b^{2^r}$ with $r\ge1$ and $s=2^r$. For every $c\in F_b$ and $N\ge1$,

```math
M_N(X_B;B)\ \le\ \frac1{2N}+s\,D'_r\,M_{sN}(X_b-c;b).
```

For $b=2$ and every $N\ge1$,

```math
\tfrac13\,M_{2N}(X_2;2)\ \le\ M_N(X_4;4)\ \le\ 2M_{2N}(X_2;2)+\frac1{2N}.
```

*Proof.* Put $w=X_b-c$. Then $X_B=c_rc+c_rw$ with $c_rc=u/b^{s-1}$, $u\in\mathbb Z$, so $\|B^nc_rc\|=0$ for $n\ge1$. For $n\ge1$, $B^nc_rw=D'_rb^{s(n-1)+1}w$, so $\|B^nc_rw\|\le D'_r\|b^{s(n-1)+1}w\|$. The indices $s(n-1)+1$ with $1\le n<N$ are distinct and less than $sN$. The $n=0$ term is bounded directly, $\|B^0X_B\|\le\frac12$, without splitting it into its two parts. This gives the first bound. For $b=2$, the upper bound is the case $s=2$, $D'_1=1$, $c=0$. For the lower bound, $\|2t\|\le2\|t\|$ and Phase 22 Theorem 7.1(ii) with $k=2$ give $M_{2N}(X_2;2)=M_{2N}(2X_4;2)\le2M_{2N}(X_4;2)\le2\cdot\frac32M_N(X_4;4)$. $\square$

Combined with Lemma 5.3 below, Proposition 1.2 becomes a transfer between discrepancies:

```math
1-D_N(X_B;B)\ \le\ 2\sqrt{2\Bigl(\frac1{2N}+\tfrac52\,s\,D'_r\bigl(1-D_{sN}(X_b;b)+\tfrac1{sN}\bigr)\Bigr)} .
```

To obtain it, choose $c\in F_b$ attaining $\mu_{sN}(X_b)$. All of this is conditional on rates for $X_b$, and none is known.

### 1.4 The quotient $K_{b^2}/K_b\cong\mathbb Z/(b+1)$ and $X_b$

**Theorem 1.3.** Suppose $X_b\in K_{b^2}$. By Phase 22 Theorem 8.1, $X_b=\frac r{b^2-1}+w$ with a unique $r\in\{0,\dots,b^2-2\}$ and $w\in M_b$. Its class is $[r]\in\mathbb Z/(b+1)$.

(a) $X_{b^2}\in K_{b^2}$, with class $[2r]$.

(b) If $b$ is even, $X_{b^2}\in K_b\iff X_b\in K_b$. If $b$ is odd, $X_{b^2}\in K_b\iff r\equiv0\pmod{\frac{b+1}2}$.

(c) If $r\not\equiv0\pmod{b+1}$, then every base-$b$ word frequency of $X_b$ exists and equals the corresponding frequency of the period-2 expansion of $\frac r{b^2-1}$. Hence $D_N(X_b;b)\to D(\mu_{r/(b^2-1)})<1$.

(d) For $b=2$: if $X_2\in K_4$, then the binary digit-change density of $X_2$ tends to $0$ (class $0$, i.e. $X_2\in K_2$) or to $1$ (class $\pm1$, with limit measure that of $\frac13$ and $D_N(X_2;2)\to\frac23$).

*Proof.* (a) $X_{b^2}=\frac{b-1}bX_b=\frac r{b(b+1)}+\frac{b-1}bw$. For $A\in\mathbb Z$ and $B'$ prime to $b$, $\frac A{bB'}\equiv\frac{Ab'}{B'}\pmod{\mathbb Z[1/b]}$ whenever $bb'\equiv1\pmod{B'}$. Take $B'=b^2-1$ and $b'=b$, and write $\frac r{b(b+1)}=\frac{r(b-1)}{b(b^2-1)}$. This gives

```math
\frac r{b(b+1)}\equiv\frac s{b^2-1}\pmod{\mathbb Z[1/b]},\qquad s\equiv r(1-b)\equiv2r\pmod{b+1}.
```

Since $\mathbb Z[1/b]\subseteq M_b$, the class of $X_{b^2}$ is $[2r]$. (b) $X_{b^2}\in K_b$ iff $2r\equiv0\pmod{b+1}$. (c) is Phase 22 Theorem 9.2(3)–(4) with $k=2$; the period is $d=2$ when $R=b+1\nmid r$. (d) If $r=0$, use Phase 22 Corollary D4.9′. Otherwise $r\in\{1,2\}$, the block is $01$ or $10$, and Phase 22 Theorem 9.2 and its table give $D(\mu_{1/3})=\frac23$. $\square$

The script verifies the class map $r\mapsto2r$ for all $r<b^2-1$, $b\le24$, through the Phase 19 rational membership test. Finite measurement: the binary change density of $X_2$ is $0.5080$ at $N=4000$. That value decides nothing.

Wall's theorem (rational multiples preserve normality) and the equivalence of normality in bases $b$ and $b^k$ show that $X_b$, $X_{b^2}$, $X_{b^4},\dots$ are all normal in base $b$ or none is (Phase 22, D3.13(f)).

### 1.5 Arithmetic nature

$X_b=1/(\frac b{b-1}-2\xi_b)$ by Theorem 3.1, a rational Möbius image of $\xi_b$. **External input:** $\xi_b$ is transcendental (Mahler, Math. Ann. 101 (1929)), and its irrationality exponent equals 2 for every $b\ge2$ (Y. Bugeaud, *On the rational approximation to the Thue–Morse–Mahler numbers*, Ann. Inst. Fourier 61 (2011) 2065–2076). Transcendence and the irrationality exponent are invariant under $t\mapsto(\alpha t+\beta)/(\gamma t+\delta)$ with rational $\alpha\delta-\beta\gamma\ne0$. So $X_b$ is transcendental with irrationality exponent 2, which agrees with Phase 22 D3.13(e). By Phase 20 §2.5(2), irrationality-exponent information does not decide $K_b$ membership.

## 2. Growth and the carry window

### 2.1 Elementary two-sided bounds

**Theorem 2.1.** For $m\ge2$ and $k\ge1$,

```math
\prod_{i=1}^{k-1}\Bigl(\Bigl\lfloor\frac{m^{k-i}}k\Bigr\rfloor+1\Bigr)\ \le\ b_m(m^k)\ \le\ \prod_{i=0}^{k-1}(m^i+1).
```

In particular $\frac{k(k-1)}2-(k-1)\log_mk\le\log_mb_m(m^k)\le\frac{k(k-1)}2+\log_mC_m$, where $C_m=\prod_{i\ge0}(1+m^{-i})$. Numerically $C_2=4.768462$, $C_3=3.129868$, $C_4=2.711819$ and $C_5=2.521002$.

*Proof.* Upper: $b_m$ is nondecreasing, so $b_m(mn)=\sum_{j\le n}b_m(j)\le(n+1)b_m(n)$; iterate from $b_m(1)=1$. Lower: a partition of $m^k$ into powers of $m$ is a vector of multiplicities $(c_0,\dots,c_k)$ with $\sum c_im^i=m^k$. For $1\le i\le k-1$ choose $c_i\in\{0,\dots,\lfloor m^{k-i}/k\rfloor\}$ freely and put $c_k=0$. Then $\sum_{i\ge1}c_im^i\le\frac{k-1}km^k<m^k$, so $c_0=m^k-\sum_{i\ge1}c_im^i\ge1$ completes a partition. Distinct choices give distinct partitions, and $\lfloor y\rfloor+1\ge y$. $\square$

**Corollary 2.2.** For $n\ge m$ and $\ell=\log_mn$,

```math
\frac{\ell^2}2-\frac{3\ell}2+1-\ell\log_m\ell\ \le\ \log_mb_m(n)\ \le\ \frac{\ell^2}2+\frac\ell2+\log_mC_m .
```

Hence $\log b_m(n)=\frac{(\log n)^2}{2\log m}+O(\log n\log\log n)$, which is Mahler's leading term (J. London Math. Soc. 15 (1940); de Bruijn, Indag. Math. 10 (1948) for the full expansion), here proved elementarily.

*Proof.* Let $k=\lfloor\ell\rfloor\ge1$ and use monotonicity, $b_m(m^k)\le b_m(n)\le b_m(m^{k+1})$. Lower: $k(k-1)/2\ge(\ell-1)(\ell-2)/2$ (for $\ell\ge2$ because $k\ge\ell-1\ge1$; on $1\le\ell<2$ the left side is $0$ and the right side is at most $0$), and $(k-1)\log_mk\le\ell\log_m\ell$. Upper: by Theorem 2.1,

```math
b_m(m^{k+1})\ \le\ \prod_{i=0}^{k}(m^i+1)\ =\ m^{k(k+1)/2}\prod_{i=0}^{k}\bigl(1+m^{-i}\bigr)\ \le\ m^{k(k+1)/2}\,C_m ,
```

and $k(k+1)/2\le\ell(\ell+1)/2$. $\square$

The factor $i=0$, equal to $2$, is already part of $C_m$, so it cannot be divided out. Indeed the constant $\log_m(C_m/2)$ fails already at $k=1$ for every $m\ge3$: $b_m(m^2)=m+2$, and $m+2>mC_m/2$ (for example $\log_35=1.465>1+\log_3(C_3/2)=1.408$). The script checks this exactly for $3\le m\le10$.

The script checks Theorem 2.1 for $m^k\le20{,}000$, and the integer form $L_{\lfloor\ell\rfloor}\le b_m(n)\le U_{\lfloor\ell\rfloor+1}$ and Corollary 2.2 for every $n<17{,}000$ ($m=2$) and every $n<20{,}000$ ($m=3,4,5$), in floating point with tolerance $10^{-9}$. The smallest slacks in Corollary 2.2 are $1.000$ (lower) and $2.254$ (upper) for $m=2$.

Finite table (exact integers):

| $m$ | $k$ | $\log_mL_k$ | $\log_mb_m(m^k)$ | $k(k-1)/2$ | $\log_mU_k$ |
| --- | --- | --- | --- | --- | --- |
| 2 | 13 | 39.784 | 54.933 | 78.0 | 80.253 |
| 2 | 14 | 48.485 | 64.597 | 91.0 | 93.253 |
| 3 | 9 | 22.038 | 27.798 | 36.0 | 37.039 |
| 4 | 7 | 13.255 | 16.877 | 21.0 | 21.720 |
| 5 | 6 | 9.670 | 12.374 | 15.0 | 15.574 |

The normalized growth $\log_2\beta(2^k)/(k^2/2)$ is $0.6063$, $0.6222$, $0.6408$ and $0.6591$ at $k=8,10,12,14$; the first three agree with Phase 22. The convergence to 1 is slow, because the correction term $\ell\log_m\ell$ is large.

### 2.2 The certified window

Put $T(n,L)=\sum_{j>L}\beta(n+j)b^{-j}$, so that $x_n\equiv R_{n,L}/b^L+T(n,L)\pmod1$. The window to precision $\tau$ at $N$ is the least $L$ with $\max_{n<N}T(n,L)<\tau$. Since $\beta$ is nondecreasing, the maximum is $T(N-1,L)$.

**Proposition 2.3.** For $0<\tau<1$,

```math
L_\tau(N)\ \ge\ \log_b\beta(N)+\log_b(1/\tau)-1 .
```

There is $j_0(b)$ such that for $N\ge j_0(b)$ and $2b^{-N/2}\le\tau/2$,

```math
L_\tau(N)\ \le\ \log_b\beta(N)+\log_b(1/\tau)+\log_b(N+1)+\log_b\frac2{b-1}+1 .
```

The last two terms add to at most $1$ for $b\ge3$, and to $2$ for $b=2$.

So for $\tau=N^{-A}$,

```math
L_\tau(N)=\frac{(\log_2N)^2}{2\log_2b}+O_{A,b}(\log N\log\log N).
```

*Proof.* Lower: $T(N-1,L)\ge\beta(N+L)b^{-L-1}\ge\beta(N)b^{-L-1}$. Upper: put

```math
\Omega=\log_b\beta(N)+\log_b(1/\tau)+\log_b(N+1)+\log_b\frac2{b-1},
```

and let $L^*$ be the least integer with $\frac{(N+1)\beta(N)}{(b-1)b^{L^*}}<\frac\tau2$, that is, the least integer $L^*>\Omega$. Then $L^*\le\Omega+1$. Phase 22 Proposition D3.13(c) requires $N\ge j_0(b)$ and $L<N$. To check $L^*<N$, note that $2b^{-N/2}\le\tau/2$ gives $\log_b(1/\tau)\le\frac N2-\log_b4$. So $L^*\le\frac N2+\log_b\beta(N)+\log_b(N+1)+1$, which is $\frac N2+O_b((\log N)^2)$ by Corollary 2.2, and this is less than $N$ once $N$ is large. Enlarge $j_0(b)$ so that this holds for $N\ge j_0(b)$. Then D3.13(c) with $n=N-1$ and $L=L^*$ gives $T(N-1,L^*)\le\frac{(N+1)\beta(N)}{(b-1)b^{L^*}}+2b^{-N/2}<\frac\tau2+\frac\tau2=\tau$, so $L_\tau(N)\le L^*\le\Omega+1$. For $b=2$ the term $\log_2\frac2{b-1}=1$ is needed: with only $+1$ in place of $\log_b\frac2{b-1}+1$, an $L$ allowed by the bound could leave the D3.13(c) majorant as large as $2^{-0.01}\tau+\frac\tau2>\tau$. Asymptotic: apply Corollary 2.2 with $m=2$ and divide by $\log_2b$. $\square$

The same proof applies to $X_{b,m}$, with leading term $(\ln N)^2/(2\ln m\ln b)$.

Exact windows from the script, with $\tau=N^{-2}$. $L_{\rm nec}$ is the least $L$ with $\beta(N+L)b^{-L-1}<\tau$, a lower bound for the window.

| $b$ | $N$ | $L_{\rm exact}$ | $L_{\rm nec}$ | $\log_b\beta(N)+\log_b(1/\tau)$ | $\frac{(\log_2N)^2}{2\log_2b}$ |
| --- | --- | --- | --- | --- | --- |
| 2 | 500 | 44 | 43 | 42.58 | 40.19 |
| 2 | 1000 | 52 | 51 | 50.82 | 49.66 |
| 2 | 4000 | 70 | 69 | 69.78 | 71.59 |
| 3 | 4000 | 44 | 44 | 44.03 | 45.17 |
| 10 | 4000 | 21 | 21 | 21.01 | 21.55 |

The base-2 values $44,52,70$ reproduce Phase 22. The window exceeds the first-omitted-term bound by at most one digit in all twelve cases computed ($b=2,3,10$, $N=500,1000,2000,4000$). For each case the script also computes $L^*$ of the proof exactly and checks, by integer comparisons, $L_{\rm exact}\le L^*\le\Omega+1$, $L^*<N$, $2b^{-N/2}\le\tau/2$ and the lower bound. For $b=2$, $L^*=53,62,72,83$ at $N=500,1000,2000,4000$.

## 3. Reciprocals: Thue–Morse and the $m$-ary dichotomy

### 3.1 The reciprocal identity

Let $\varepsilon_m(n)=(-1)^{s_m(n)}$ if every base-$m$ digit of $n$ is $0$ or $1$, and $\varepsilon_m(n)=0$ otherwise. Here $s_m$ is the base-$m$ digit sum. In particular $\varepsilon_2(n)=(-1)^{t_n}$.

**Theorem 3.1.** For every $J\ge0$, in $\mathbb Z[z]$,

```math
\prod_{j=0}^{J}\bigl(1-z^{m^j}\bigr)=\sum_{n<m^{J+1}}\varepsilon_m(n)\,z^n .
```

Hence $1/X_{b,m}=Y_{b,m}=\sum_{n\ge0}\varepsilon_m(n)b^{-n}$. The product truncation $X^{(J)}_{b,m}=\prod_{j\le J}(1-b^{-m^j})^{-1}$ equals $1/Y^{[m^{J+1}]}_{b,m}$, where $Y^{[M]}$ denotes the sum of the first $M$ terms. For $m=2$,

```math
\frac1{X_b}=Y_b=\sum_{n\ge0}(-1)^{t_n}b^{-n}=\frac b{b-1}-2\xi_b,\qquad X_2=\frac1{2-4\tau_{\rm TM}},
```

where $\tau_{\rm TM}=\sum_nt_n2^{-n-1}=0.412454033640108\ldots$ is the Prouhet–Thue–Morse constant and $X_2=2.855642702854817\ldots$.

*Proof.* Expanding the product, $z^n$ appears once for each $S\subseteq\{0,\dots,J\}$ with $\sum_{j\in S}m^j=n$, with sign $(-1)^{|S|}$. By uniqueness of base-$m$ expansions there is at most one such $S$, and it exists iff the digits of $n$ lie in $\{0,1\}$. The degree is $\sum_{j\le J}m^j<m^{J+1}$. Let $J\to\infty$ (absolute convergence for $|z|<1$), and use $\sum_nb^{-n}=\frac b{b-1}$ with $(-1)^{t}=1-2t$. $\square$

The script checks the truncated identity for $m=2$ ($J\le11$), $m=3$ ($J\le6$) and $m=4,5,7$; the coefficientwise identity $F_m\cdot Y_m=1$ through $z^{1200}$ for $m=2,3$; $X^{(J)}_bY_b^{[2^{J+1}]}=1$ exactly for $b=2,3,10$ and $J\le6$; and $X_2(2-4\tau_{\rm TM})=1$ to $2^{-150}$.

This is the exact analogue of $P_b=1/E_b$, with one difference. Euler's $E_b$ has support of size about $\sqrt N$ and lies in $K_b$. The Thue–Morse reciprocal $Y_b$ has full support with coefficients $\pm1$, and §3.2 shows that it is not in $K_b$.

### 3.2 The digits of $Y_b$

**Lemma 3.2 (Thue–Morse 2-blocks).** Let $C(N)=\#\{0\le n<N:t_n\ne t_{n+1}\}$. Then $|C(N)-\frac{2N}3|\le\frac{\lfloor\log_2N\rfloor+1}3$ for every $N\ge1$. Consequently the 2-blocks $00,01,10,11$ of $(t_n)$ have frequencies $\frac16,\frac13,\frac13,\frac16$, each with error $O(\log N)$ in the count.

*Proof.* Put $p_n=t_n\oplus t_{n+1}$. From $t_{2k}=t_k$ and $t_{2k+1}=1-t_k$ we get $p_{2k}=1$ and $p_{2k+1}=1-p_k$. So $C(2N)=2N-C(N)$ and $C(2N+1)=C(2N)+1$. Then $E(N)=C(N)-\frac{2N}3$ satisfies $E(2N)=-E(N)$ and $E(2N+1)=\frac13-E(N)$, with $E(1)=\frac13$. Induct on the bit length. Changes $01$ and $10$ alternate, so their counts differ by at most 1. Since $t_{2k}+t_{2k+1}=1$, $\#\{n<N:t_n=1\}=\frac N2+O(1)$. Finally $\#11=\#\{t_n=1\}-\#10$ and $\#00=N-C(N)-\#11$. $\square$

**Theorem 3.3.** (a) *Digit code.* For $b\ge3$ and $n\ge1$,

```math
d_n(Y_b)=\begin{cases}1,&(t_n,t_{n+1})=(0,0),\\ 0,&(t_n,t_{n+1})=(0,1),\\ b-1,&(t_n,t_{n+1})=(1,0),\\ b-2,&(t_n,t_{n+1})=(1,1).\end{cases}
```

For $b=2$, $d_n(Y_2)=1-t_{n+1}$.

(b) *Frequencies.* For $b\ge4$ the digits $1,0,b-1,b-2$ have frequencies $\frac16,\frac13,\frac13,\frac16$. For $b=3$ each digit has frequency $\frac13$. For $b=2$ each digit has frequency $\frac12$. So $Y_2$ and $Y_3$ are simply normal in their bases.

(c) *Not normal.* For $b\ge3$, neither $00$ nor $(b-1)(b-1)$ ever occurs in the digits of $Y_b$. For $b=2$, neither $000$ nor $111$ occurs, because Thue–Morse is cube-free (Thue 1912). Hence, for every $N\ge1$, $D_N(Y_b;b)\ge2b^{-2}$ for $b\ge3$ and $D_N(Y_2;2)\ge\frac14$.

(d) *Not in the kernel, quantitatively.* $Y_b\notin K_b$, and $\limsup_ND_N(Y_b;b)\le1-\frac4{15b^2}$.

*Proof.* (a) Let $e_k=(-1)^{t_k}$. For $b\ge3$ put $\rho_{n+1}=\sum_{k>n}e_kb^{n-k}$. Since $\frac1b>\sum_{k\ge n+2}b^{n-k}=\frac1{b(b-1)}$ for $b\ge3$, $\rho_{n+1}$ has the sign of $e_{n+1}$ and $|\rho_{n+1}|\ge\frac1b-\frac1{b(b-1)}>0$. Also $|\rho_{n+1}|<\sum_{k>n}b^{n-k}=\frac1{b-1}\le\frac12$, strictly, because $(t_k)$ is not eventually constant. So $0<|\rho_{n+1}|<\frac12$, and neither $1+\rho_{n+1}$ nor $b-1+\rho_{n+1}$ is an integer. Now $\{b^{n-1}Y_b\}=\{(e_n+\rho_{n+1})/b\}$. If $e_n=1$, the digit is $\lfloor1+\rho_{n+1}\rfloor$. If $e_n=-1$, it is $\lfloor b-1+\rho_{n+1}\rfloor$. This gives the four cases. For $b=2$, $Y_2=2-2\xi_2$ and $\xi_2=0.t_1t_2t_3\cdots$ in binary, with $t_0=0$ and $t_1=1$. So $Y_2=1-0.t_2t_3\cdots=0.\bar t_2\bar t_3\cdots$, since Thue–Morse is not eventually constant. (b) follows from (a) and Lemma 3.2. (c) A digit $0$ needs $t_{n+1}=1$, and a following digit $0$ would need $t_{n+1}=0$. A digit $b-1$ needs $t_{n+1}=0$, and a following digit $b-1$ would need $t_{n+1}=1$. The points with first two digits $00$ fill $[0,b^{-2})$, and those with first two digits $(b-1)(b-1)$ fill $[1-b^{-2},1)$. Both intervals are empty, so all $N$ points lie in $[b^{-2},1-b^{-2})$, of length $1-2b^{-2}$, and $D_N(Y_b;b)\ge2b^{-2}$. For $b=2$, avoiding $000$ and $111$ puts every point in $[\frac18,\frac78]$, and since $Y_2$ is irrational no point equals $\frac18$ or $\frac78$. So all $N$ points lie in $(\frac18,\frac78)\subseteq[\frac18,\frac78)$, an interval of length $\frac34$, and $D_N(Y_2;2)\ge\frac14$. (d) If $x=c+w\in K_b$ with $c=j/(b-1)$ and $w\in M_b$, Markov's inequality gives $\|b^nw\|$ small for a density-one set of $n$. When $1\le j\le b-2$, $c$ is interior to the cylinder of digit $j$, so digit $j$ has density 1. When $j=0$, the 2-blocks lie in $\{00,(b-1)(b-1)\}$ for a density-one set. Both fail by (b) and (c). For the rate, take $c=j/(b-1)$ with $1\le j\le b-2$. Every point outside the digit-$j$ cylinder is at circle distance at least $\frac1{b(b-1)}$ from $c$, so $M_N(Y_b-c)\ge\frac{1-f_N(j)}{b(b-1)}$, where $f_N(j)\le\frac13+o(1)$ is the frequency of digit $j$. For $c=0$, every point whose 2-block is outside the allowed set has $\|b^nY_b\|\ge b^{-2}$. Such 2-blocks have density 1 ($b\ge3$) or $\frac23$ ($b=2$). Hence $\liminf_N\mu_N(Y_b)\ge\frac2{3b^2}$. Lemma 5.3 gives $1-D_N\ge\frac25\mu_N-\frac1N$. $\square$

**External input.** The Thue–Morse subshift is uniquely ergodic and has no atoms (Keane 1968). So all word frequencies of $Y_b$ exist, and $D_N(Y_b;b)$ converges to the discrepancy of an atomless limit measure. This is not used above.

Finite measurements: $D_N(Y_2;2)=0.3502$ at $N=1000,2000,4000$. For base $3,4,5$ with $N=3970$, $(D_N,\mu_N)=(0.3901,0.2131)$, $(0.4007,0.2250)$ and $(0.5335,0.1844)$. The base-3 digit frequencies of $Y_3$ at $N=4000$ are $0.3332,0.3335,0.3332$. The script verifies the digit code on 4000 certified digits for $b=2,3,4,5,10$, the absence of the forbidden pairs, the 2-block counts up to $70{,}000$ with the error bound of Lemma 3.2, and cube-freeness for factors of length at most 6 in the first $20{,}000$ terms.

### 3.3 The dichotomy $m=2$ versus $m\ge3$

**Theorem 3.4.** Let $m\ge3$ and $S_m(N)=\#\{1\le n\le N:\varepsilon_m(n)\ne0\}\le2N^{\log_m2}-1$. Then

```math
M_N(Y_{b,m};b)\ \le\ \frac{S_m(N)+1}N\ \le\ 2N^{\log_m2-1},\qquad 1-D_N(Y_{b,m};b)\ \le\ 4N^{(\log_m2-1)/2}.
```

So $Y_{b,m}\in M_b\subseteq K_b$ with an explicit power rate.

*Proof.* If $N<m^K$, then $S_m(N)\le2^K-1$. Taking $K=\lfloor\log_mN\rfloor+1$ gives $2^K\le2N^{\log_m2}$. The rest is Phase 22 Proposition 9.3: $\|b^nY\|\le\sum_{k\ge1}|\varepsilon_m(n+k)|b^{-k}$. Summing over $n<N$, each supported $m'\le N$ contributes at most $\frac1{b-1}\le1$, and all $m'>N$ together contribute at most 1. Then apply Lemma 5.3. $\square$

**Corollary 3.5.** $X_{b,m}$ is the reciprocal of an element of $K_b$ if $m\ge3$ (with support exponent $\log_m2$; compare $\frac12$ for $E_b$). It is the reciprocal of the non-kernel Thue–Morse number $Y_b$ if $m=2$. Neither case decides membership, because reciprocals do not preserve $K_b$: $1+\frac1b\in\mathbb Z[1/b]\subseteq K_b$, but $\frac b{b+1}\notin K_b$ by the Phase 19 denominator test.

Finite measurements ($M_N$ from certified digits, against the proved bound):

| $b$ | $m$ | $N$ | $M_N(Y_{b,m};b)$ | $(S_m(N)+1)/N$ | $2N^{\log_m2-1}$ |
| --- | --- | --- | --- | --- | --- |
| 2 | 3 | 4000 | 0.027754 | 0.064000 | 0.093674 |
| 2 | 4 | 4000 | 0.007382 | 0.016000 | 0.031623 |
| 3 | 3 | 4000 | 0.020844 | 0.064000 | 0.093674 |
| 3 | 4 | 4000 | 0.005218 | 0.016000 | 0.031623 |

## 4. Rational approximants: periods against tracking

Let $D_J=\prod_{j=0}^J(b^{2^j}-1)$. Then $X^{(J)}_b=b^{2^{J+1}-1}/D_J$ is in lowest terms, and its base-$b$ period is $T_J=\operatorname{ord}_{D_J}(b)$, with the convention $T_J=1$ when $D_J=1$.

**Theorem 4.1.** $T_0=1$, and $T_J=2^JD_{J-1}$ for $J\ge1$, in every base $b\ge2$. For $J\ge1$, $T_J$ is a power of 2 exactly when either $J=1$ and $b-1$ is a power of 2, or $J=2$ and $b=3$.

*Proof.* The exponents $1\mid2\mid\cdots\mid2^J$ form a divisibility chain with even last term, so Phase 22 Proposition D3.9(c) applies. In outline: every prime $p\mid D_J$ divides $x-1$ with $x=b^{2^J}$, and $T_J=2^Jt$. By lifting the exponent, $v_p(x^t-1)=v_p(x-1)+v_p(t)$. For $p=2$ this needs $4\mid x-1$, which holds since $J\ge1$. So $D_J\mid x^t-1$ iff $D_{J-1}\mid t$. For an odd prime $p\mid b-1$, $v_p(D_J)=(J+1)v_p(b-1)$ grows linearly in $J$. These odd prime powers enter $T_J$, so $T_J$ is not a pure power of 2. Power-of-two cases: $D_0=b-1$ and $D_1=(b-1)^2(b+1)$, which is a power of 2 only for $b=3$. For $J\ge3$, $D_{J-1}$ is divisible by $b^2+1$, whose odd part exceeds 1. $\square$

The script verifies $T_J$ by exact order tests for $b\in\{2,3,5,7,10\}$ and $J\le6$: $b^{T_J}\equiv1$, and $b^{T_J/q}\not\equiv1$ for every prime $q\mid T_J$. The primes come from complete factorizations of $b-1$ and of $b^{2^i}+1$ for $i\le4$. It also checks the power-of-two classification for $b\le40$ and $J\le5$.

| $b$ | $J$ | $T_J$ | $2^{J+1}/T_J$ |
| --- | --- | --- | --- |
| 2 | 2 | 12 | $6.7\cdot10^{-1}$ |
| 2 | 3 | 360 | $4.4\cdot10^{-2}$ |
| 2 | 4 | 183,600 | $1.7\cdot10^{-4}$ |
| 2 | 5 | 24,064,452,000 | $2.7\cdot10^{-9}$ |
| 2 | 6 | $\approx2.07\cdot10^{20}$ | $6.2\cdot10^{-19}$ |
| 3 | 2 | 64 | $1.3\cdot10^{-1}$ |
| 3 | 3 | 10,240 | $1.6\cdot10^{-3}$ |
| 10 | 3 | 71,272,872 | $2.2\cdot10^{-7}$ |
| 10 | 6 | $\approx5.7\cdot10^{64}$ | $2.2\cdot10^{-63}$ |

**Lemma 4.2 (tracking).** Let $A_J$ be the number of leading fractional digits shared by $X_b$ and $X^{(J)}_b$. If $J\ge0$ and $b^{2^{J+1}}\ge64$, then $A_J<2^{J+1}$. If moreover $J\ge1$ (so that $D_{J-1}$ is defined and Theorem 4.1 gives $T_J$), then $A_J/T_J<2^{J+1}/T_J=2/D_{J-1}$, which tends to 0 doubly exponentially.

*Proof.* Phase 22 Lemma D3.10 applies with $m_{K+1}=2^{J+1}$ (when $A_J=0$ there is nothing to prove). For $J\ge1$, divide by $T_J=2^JD_{J-1}$. $\square$

Exact $A_J$ for $J=0,\dots,6$: $0,1,6,14,27,59,126$ ($b=2$), $0,2,6,15,30,63,127$ ($b=3$) and $1,3,7,13,31,63,127$ ($b=10$).

**Theorem 4.3 ($m$-ary chains).** For the chain $1,m,\dots,m^J$ with $J\ge1$, let $D_{J,m}=\prod_{j\le J}(b^{m^j}-1)$. If $b$ is even, $b\equiv1\pmod4$ or $m$ is even, then $\operatorname{ord}_{D_{J,m}}(b)=m^JD_{J-1,m}$. Otherwise it is $m^JD_{J-1,m}/2^{\min(J-1,\,v_2(b+1)-1)}$.

*Proof.* Phase 22 Proposition D3.9(c) and (c′). $\square$

The script verifies Theorem 4.3 by exact order tests in 43 cases ($b\in\{2,3,5,7,10\}$, $m\in\{3,4,5\}$, $J\le3$). For example, $(b,m,J)=(3,3,2)$ has $\operatorname{ord}=m^JD_{1,3}/2$ and tracking ratio $m^{J+1}/T=0.115$.

**Consequence 4.4 (barrier for one method).** The approximant mechanism of Phases 20–22 needs (R1): the tracked prefix must contain many full periods. Let $m\ge2$, $J\ge1$ and $b^{m^{J+1}}\ge64$. Let $A_{J,m}$ be the number of leading fractional digits shared by $X_{b,m}$ and its product truncation $X^{(J)}_{b,m}=b^{\sum_{j\le J}m^j}/D_{J,m}$, and let $T_{J,m}=\operatorname{ord}_{D_{J,m}}(b)$. Put $e=0$ in the first case of Theorem 4.3 and $e=\min(J-1,\,v_2(b+1)-1)$ otherwise. In every case

```math
0\ \le\ e\ \le\ \max\bigl(0,\ \min(J-1,\ v_2(b+1)-1)\bigr),\qquad \frac{A_{J,m}}{T_{J,m}}\ <\ \frac{2^e\,m}{D_{J-1,m}}\ \le\ \frac{2^{\max(0,\,\min(J-1,\,v_2(b+1)-1))}\,m}{D_{J-1,m}} .
```

*Proof.* Phase 22 Lemma D3.10, for the chain $1,m,\dots,m^J,m^{J+1},\dots$, gives $A_{J,m}<m^{J+1}$. Theorem 4.3 gives $T_{J,m}=m^JD_{J-1,m}/2^e$. In the second case of Theorem 4.3, $b\equiv3\pmod4$, so $v_2(b+1)\ge2$ and $e\ge0$. $\square$

The clamp at $0$ matters. For even $b$, $v_2(b+1)=0$ and $\min(J-1,v_2(b+1)-1)=-1$, and the bound with exponent $-1$ is false. At $b=2$, $m=2$, $J=2$ one has $A_2=6$, $T_2=12$ and $D_1=3$, so $A_2/T_2=\frac12$, which exceeds $2^{-1}\cdot\frac23=\frac13$ but is below $\frac23$. For $m=2$ the case $e=0$ always applies, and the bound is $2/D_{J-1}$, as in Lemma 4.2. The script checks the bound exactly in 24 m-ary cases ($m\in\{3,4\}$, $b\in\{2,3,5,7\}$, $J\le3$, $m^{J+1}\le256$), including $e=1$ at $(b,m,J)=(3,3,2),(3,3,3),(7,3,2)$ and $e=2$ at $(7,3,3)$. For example, $(b,m,J)=(3,3,2)$ has $A_{2,3}=26$ and $A/T=0.1111<0.1154$.

By Theorem 3.1, these truncations are exactly the reciprocals of the truncations of $Y_{b,m}$. So no argument that runs through the truncations of either $X_{b,m}$ or $Y_{b,m}$ can see a full period. This is a theorem about a method, not about $X_b$.

The carry window of §2 grows like $(\log N)^2$. So no fixed window of coefficients $\beta(n+1),\dots,\beta(n+L)$, and no fixed residue $\beta\bmod b^L$, certifies the orbit points of $X_b$ (Proposition 2.3). This rules out one construction of an automaton, namely a local carry transducer with a bounded window reading the coefficients. It does not rule out a finite automaton computing $d_n(X_b)$ by other means. For comparison, the 2-automatic number $\Lambda_2$ has radix-equivalent coefficient series of unbounded signed width (Proposition 5.7). Whether the digit sequence of $X_b$ is automatic is **open**. Adamczewski–Bugeaud (Ann. of Math. 165 (2007)) shows that an automatic irrational number is transcendental, which is consistent with either answer.

**Proposition 4.5 ($\beta$ modulo powers of 2).** For every $L\ge1$, the sequence $(\beta(n)\bmod2^L)_{n\ge0}$ is 2-automatic. Its 2-kernel has at most $2^{L(L+1)}$ elements.

*Proof.* Let $F(z)=\sum_n\beta(n)z^n$, so $(1-z)F(z)=F(z^2)$, and put $F_k=(1-z)^{-k}F\in\mathbb Z[[z]]$ for $k\ge0$. Define the Cartier operators $\Phi_0,\Phi_1$ by $A(z)=(\Phi_0A)(z^2)+z\,(\Phi_1A)(z^2)$, so that $\Phi_iA$ has coefficients $A_{2n+i}$. From the functional equation,

```math
F_k(z)=\frac{F(z^2)}{(1-z)^{k+1}}=(1+z)^{k+1}\,\frac{F(z^2)}{(1-z^2)^{k+1}}=(1+z)^{k+1}\,F_{k+1}(z^2).
```

Write $(1+z)^s=U_s(z^2)+z\,V_s(z^2)$ and expand $U_s(1-w)=\sum_ju_{s,j}w^j$ and $V_s(1-w)=\sum_jv_{s,j}w^j$, with integer coefficients and $j\le s/2$. Since $(1-y)^jF_{k+1}(y)=F_{k+1-j}(y)$,

```math
\Phi_0F_k=\sum_{j}u_{k+1,j}\,F_{k+1-j},\qquad \Phi_1F_k=\sum_{j}v_{k+1,j}\,F_{k+1-j}.
```

The leading coefficients are $u_{s,0}=U_s(1)$ and $v_{s,0}=V_s(1)$, the sums of the even and of the odd binomial coefficients, both equal to $2^{s-1}$. So for $k\le L-1$ the right-hand sides lie in the $\mathbb Z$-span of $F_0,\dots,F_L$. For $k=L$ the only term outside it is $2^LF_{L+1}\equiv0\pmod{2^L}$. Hence the $(\mathbb Z/2^L)$-module $S_L$ spanned by $F_0,\dots,F_L$ modulo $2^L$ contains $F$ and is closed under $\Phi_0$ and $\Phi_1$. It has at most $(2^L)^{L+1}$ elements. Every element of the 2-kernel of $(\beta(n)\bmod2^L)$ is some $\Phi_{i_1}\cdots\Phi_{i_r}F\bmod2^L$, so it lies in $S_L$. A sequence over a finite alphabet with a finite $k$-kernel is $k$-automatic (Eilenberg; Allouche–Shallit, Thm. 6.6.2). $\square$

*Literature.* Congruences for $\beta$ modulo powers of 2 go back to Churchhouse (1969) and Rødseth (1970). The proof above is self-contained, and we have not checked whether automaticity modulo $2^L$ is stated in exactly this form in the literature. For a modulus $q$ with an odd prime factor $p$, the argument fails because $u_{s,0}=v_{s,0}=2^{s-1}$ is a unit modulo $p$, so the index never drops out. Whether $\beta\bmod3$ is 2-automatic is not settled here (§9, Problem 4). The script checks the two displayed identities exactly in $\mathbb Z[[y]]$ through $y^{3000}$ for $k\le7$, together with $u_{s,0}=v_{s,0}=2^{s-1}$. As a **finite measurement**, the numbers of distinct 2-kernel prefixes (depth at most 6, length 200) are $3,5,6,13$ for $q=2,4,8,16$, below $2^{L(L+1)}$, and $51$ for $q=3$.

## 5. Net carry complexity

### 5.1 Radix equivalence and the gauge identity

Call two integer sequences with absolutely convergent $F_b$ **radix-equivalent**, $a\sim a'$, if $F_b(a)-F_b(a')\in\mathbb Z$. Let $(S\Delta)(m)=\Delta(m+1)$.

**Lemma 5.1 (telescoping).** If $\Delta$ is an integer sequence with $\sum|\Delta(m)|b^{-m}<\infty$, then $F_b(a+b\Delta-S\Delta)=F_b(a)+\Delta(1)$. In finite form, for every $M\ge1$,

```math
\sum_{m=1}^{M}\bigl(b\Delta(m)-\Delta(m+1)\bigr)b^{M-m}=\Delta(1)\,b^M-\Delta(M+1).
```

**Theorem 5.2 (gauge identity).** Let $x=F_b(a)$, and let $d=(d_m)_{m\ge1}$ be the digits of $\{x\}$.

(a) *Existence and uniqueness under a growth condition.* Every $a'\sim a$ has the form $a'=d+b\delta-S\delta$ for exactly one integer sequence $\delta$ with $\delta_m=o(b^m)$, that is, $\delta_mb^{-m}\to0$. It is the canonical carry

```math
\delta_m=\sum_{j\ge0}\bigl(a'(m+j)-d_{m+j}\bigr)\,b^{-1-j},\qquad \delta_1=F_b(a')-F_b(d)\in\mathbb Z ,
```

and it satisfies

```math
|\delta_m|\,b^{-m}\ \le\ \frac1b\sum_{k\ge m}\bigl|a'(k)-d_k\bigr|\,b^{-k}\ \longrightarrow\ 0\qquad(m\to\infty).
```

So the growth condition holds automatically for the canonical carry, because $F_b(a')$ converges absolutely by the definition of $\sim$ and $d$ is bounded.

(b) *The kernel.* Without the growth condition $\delta$ is not unique. The integer solutions of $a'=d+b\delta-S\delta$ are exactly the sequences $\tilde\delta_m=\delta_m+c\,b^{m-1}$ with $c\in\mathbb Z$, because $\ker(b-S)=\{(c\,b^{m-1})_{m\ge1}:c\in\mathbb Z\}$. For $c\ne0$, $\tilde\delta_mb^{-m}\to c/b\ne0$. So $\delta_m=o(b^m)$ is necessary and sufficient to single out $\delta$.

(c) *Converse.* If $\delta$ is an integer sequence with $\delta_m=o(b^m)$ and $a'=d+b\delta-S\delta$ has absolutely convergent $F_b(a')$, then $F_b(a')=F_b(d)+\delta_1$, so $a'\sim a$. This applies to every bounded $\delta$.

(d) *Small coefficients.* If $|a'|\le B$ with $1\le B\le b-1$, then $\delta_m\in\{-1,0,1\}$ for every $m$.

*Proof.* (a) Existence: $b\delta_m=a'(m)-d_m+\delta_{m+1}$, by splitting off the $j=0$ term. The number $b^{m-1}(F_b(a')-F_b(d))$ minus the integer $\sum_{k<m}(a'(k)-d_k)b^{m-1-k}$ equals $\delta_m$, and $F_b(a')-F_b(d)=F_b(a')-\{x\}\in\mathbb Z$, so every $\delta_m$ is an integer. The growth bound follows from $\delta_mb^{-m}=\sum_{k\ge m}(a'(k)-d_k)b^{-1-k}$. Uniqueness follows from (b). (b) If $\delta$ and $\delta'$ both solve the equation, then $\eta=\delta-\delta'$ satisfies $b\eta_m-\eta_{m+1}=0$ for all $m\ge1$, so $\eta_m=b^{m-1}\eta_1$. Conversely each such $\eta$ solves the homogeneous equation. If both $\delta$ and $\delta'$ are $o(b^m)$, then $\eta_1/b=\eta_mb^{-m}\to0$, so $\eta_1=0$ and $\eta\equiv0$. (c) By the finite form of Lemma 5.1, $\sum_{m\le M}a'(m)b^{-m}=\sum_{m\le M}d_mb^{-m}+\delta_1-\delta_{M+1}b^{-M}$, and $\delta_{M+1}b^{-M}\to0$. (d) $a'-d\in[-B-(b-1),B]$ gives $\delta_m\in[-\frac{B+b-1}{b-1},\frac B{b-1}]\subseteq[-2,1]$. The endpoint $-2$ (reached only when $B=b-1$) would need $d_k=b-1$ for all $k\ge m$, which the digit convention excludes. $\square$

The summability hypothesis $\sum_m|\delta_m|b^{-m}<\infty$ of Lemma 5.1 is stronger than $\delta_m=o(b^m)$, and it can fail for the canonical carry. For example, $a'(k)=\lfloor b^k/k^2\rfloor$ has absolutely convergent $F_b(a')$, but $\delta_m\asymp b^{m-1}/m$, so $\sum_m|\delta_m|b^{-m}=\infty$. That is why (c) uses the finite telescoping identity rather than Lemma 5.1. In Theorem 5.5, $\delta_m\in\{-1,0,1\}$, so the growth condition holds and the uniqueness of (a) applies. The script checks the growth bound of (a) and the kernel shift of (b) exactly on the 300 random instances of §8 E, with $c\in\{\pm1,\pm2,\pm3\}$.

So a radix-equivalence class is $d+\{b\delta-S\delta:\ \delta\text{ integer},\ \delta_m=o(b^m)\}$, restricted to sequences with absolutely convergent $F_b$, and each element has exactly one such $\delta$. Any quantity minimized over the class, such as the support or the signed width of the "net carried expansion", is a function of the digits of $x$ alone. It does not depend on how the coefficients $a(m)$ were written.

### 5.2 Minimal net support

For $w\in\mathbb R$, $N\ge1$ and $B\ge1$, let

```math
\sigma_B(w;N)=\min\bigl\{\#\{1\le m\le N:a'(m)\ne0\}:\ |a'|\le B,\ w-F_b(a')\in\mathbb Z\bigr\}.
```

Put $\sigma_N(x)=\min_{c\in F_b}\sigma_{\lfloor b/2\rfloor}(x-c;N)$ and $\mu_N(x)=\min_{c\in F_b}M_N(x-c;b)$. Both minima are over $c\bmod1$, a finite set. Let

```math
\chi_N(w)=\#\{1\le m\le N:(d_m,d_{m+1})\notin\{(0,0),(b-1,b-1)\}\}.
```

**Lemma 5.3 (quantitative Phase 19).** For every real $x$ and $N\ge1$,

```math
\tfrac25\,\mu_N(x)-\frac1N\ \le\ 1-D_N(x;b)\ \le\ 2\sqrt{2\,\mu_N(x)} .
```

*Proof.* Upper: $D_N$ is invariant under translation of the circle: a wrapped arc is the complement of an interval, with discrepancy of the same size. Also $b^nc\equiv c$ for $c\in F_b$. So $D_N(x)=D_N(x-c)$. Take $c$ attaining $\mu_N(x)$ and put $w=x-c$ and $M_N=M_N(w;b)=\mu_N(x)$. If $M_N=0$, every point $\{b^nw\}$ is $0$, so $D_N=1$ and the bound holds. If $M_N\ge\frac18$, then $2\sqrt{2M_N}\ge1\ge1-D_N$. Otherwise $0<M_N<\frac18$ and $\varepsilon=\sqrt{M_N/2}\in(0,\frac14)$. Markov's inequality puts at most $NM_N/\varepsilon$ points in $[\varepsilon,1-\varepsilon)$, so $D_N\ge1-2\varepsilon-M_N/\varepsilon=1-2\sqrt{2M_N}$. Lower: let $\delta=1-D_N$. Some interval has discrepancy above $1-\delta'$ for every $\delta'>\delta$. Hence at least $(1-\delta')N$ of the points lie in an arc of length at most $\delta'$, with center $z$. If $N(1-2\delta')>1$, some consecutive pair $x_n,x_{n+1}$ lies in the arc. Then $\|(b-1)z\|\le\|bx_n-bz\|+\|x_{n+1}-z\|\le\frac{(b+1)\delta'}2$. So $z$ is within $\frac{(b+1)\delta'}{2(b-1)}\le\frac32\delta'$ of some $c\in F_b$. Points in the arc are within $\frac{\delta'}2+\frac32\delta'$ of $c$, and the at most $\delta'N$ others contribute at most $\frac12$ each, so $M_N(x-c)\le2\delta'+\frac{\delta'}2=\frac52\delta'$. Otherwise $\delta'\ge\frac12-\frac1{2N}$, and $\mu_N\le\frac12\le\frac52(\delta'+\frac1N)$. Let $\delta'\to\delta$. $\square$

The square root cannot be removed. Put a fraction $\sqrt\mu$ of the points at distance $\sqrt\mu$ from 0 and the rest at 0. Then $M_N=\mu$ while $1-D_N\asymp\sqrt\mu$.

**Theorem 5.4 (support against kernel deficit).** Let $b\ge2$ and $\lfloor b/2\rfloor\le B\le b-1$. For every real $w$ and $N\ge1$,

```math
\frac{b-1}B\,N\,M_N(w;b)-\frac1{b-1}\ \le\ \sigma_B(w;N)\ \le\ \#\Bigl\{0\le n<N:\|b^nw\|\ge\frac1{2b}\Bigr\}\ \le\ 2b\,N\,M_N(w;b).
```

Consequently, with $B_0=\lfloor b/2\rfloor$,

```math
\frac{b-1}{8B_0}\bigl(1-D_N(x;b)\bigr)^2-\frac1{(b-1)N}\ \le\ \frac{\sigma_N(x)}N\ \le\ 5b\Bigl(1-D_N(x;b)+\frac1N\Bigr).
```

So $\sigma_N(x)=o(N)\iff D_N(x)\to1\iff x\in K_b$, with the rates tied as shown.

*Proof.* Upper: this is the canonical representation of Phase 22 Theorem D4.9, $a'(t)=I_t-bI_{t-1}$ with $I_t=\lfloor b^tw+\frac12\rfloor$. Then $|a'|\le\lfloor b/2\rfloor\le B$, and $a'(t)=0$ whenever $\|b^{t-1}w\|<\frac1{2b}$. The last inequality is Markov's. Lower: for any admissible $a'$, $\|b^nw\|\le\sum_{k\ge1}|a'(n+k)|b^{-k}$. Summing over $n<N$, each $t\le N$ with $a'(t)\ne0$ contributes at most $\frac B{b-1}$, and the terms $t>N$ contribute at most $\frac B{(b-1)^2}$. So $NM_N\le\frac B{b-1}(S_{a'}(N)+\frac1{b-1})$. The consequence takes the minimum over $c$ and applies Lemma 5.3. $\square$

**Theorem 5.5 (a three-state transducer).** Let $\lfloor b/2\rfloor\le B\le b-1$ and $N\ge3$.

(a) By Theorem 5.2(a),(d), $\sigma_B(w;N)$ is the minimum, over paths $\delta_1,\dots,\delta_{N+1}\in\{-1,0,1\}$, of $\#\{m\le N:d_m+b\delta_m-\delta_{m+1}\ne0\}$. The constraints are $|d_m+b\delta_m-\delta_{m+1}|\le B$ and $|\delta_{N+1}+\{b^Nw\}|\le\frac B{b-1}$.

(b) The cost-free transitions $d_m+b\delta_m-\delta_{m+1}=0$ are exactly $0\xrightarrow{0}0$, $0\xrightarrow{1}1$ and $-1\xrightarrow{b-1}-1$.

(c) $\frac13\chi_{N-2}(w)\le\sigma_B(w;N)\le\chi_N(w)+1$.

*Proof.* (a) Admissible tails from state $\delta_{N+1}$ exist iff $\tau=\delta_{N+1}+\{b^Nw\}$ is a sum $\sum_{j\ge0}a'(N+1+j)b^{-1-j}$ with $|a'|\le B$. Since $2B+1\ge b$, those sums fill $[-\frac B{b-1},\frac B{b-1}]$. Feasibility at earlier states follows from the transitions. (b) $d=\delta'-b\delta\in[0,b-1]$ with $\delta,\delta'\in\{-1,0,1\}$; enumerate. (c) Suppose $(d_m,d_{m+1})$ is not an allowed pair and positions $m$, $m+1$ are both cost-free. By (b) the path must be $0\xrightarrow{0}0\xrightarrow{1}1$, and state $1$ has no cost-free exit, so position $m+2$ costs. Each costly position serves at most three windows $\{m,m+1,m+2\}$. Upper: if $(d_t,d_{t+1})$ is allowed, then $\{b^{t-1}w\}\in[0,b^{-2})\cup[1-b^{-2},1)$, and $\|b^{t-1}w\|<\frac1{2b}$ except for the value $\{b^{t-1}w\}=\frac34$ when $b=2$. That value occurs for at most one index $t$: its forward orbit under $y\mapsto\{2y\}$ is $\frac34\to\frac12\to0\to0\to\cdots$, so $\frac34$ is never revisited. Apply the upper bound of Theorem 5.4. $\square$

This gives the general-$b$ form of Phase 22 Corollary D4.9′ with explicit constants: $x\in K_b\iff\min_c\chi_N(x-c)=o(N)\iff\sigma_N(x)=o(N)$. "Carry-cancellation complexity" is thus the output of a three-state min-plus automaton reading the digits of $x$.

The script runs the dynamic program of (a) and compares it with brute force over all prefixes $a'\in[-B,B]^N$ on 70 rational instances, with $(b,B,N)$ from $(2,1,7)$ to $(6,3,4)$. It checks Lemma 5.3, Theorem 5.4 (each inequality) and Theorem 5.5(c) exactly on 500 random rationals in bases $2,3,4,5,10$. It also checks the discrepancy formula $D_N=\frac1N+\max z-\min z$ against brute force on 150 orbits with ties. The gauge identity is checked on 300 random finite sequences, and the transition table of (b) for $b\le16$.

### 5.3 Signed widths inside $K_b$

Phase 22 Corollary D4.15 proved that every *local* decomposition of the coefficients of $E_b^4,E_b^6,E_b^8,D(\Theta_3^2)$ has signed-digit (NAF) width $\gg N\sqrt{\log N}$, or $\gg N(\log N)^{1/4}$ for $D(E_b^2)$. The Phase 22 examples inside $K_b$ had large *raw* width but signed width only $\sim2N$. The construction below reaches the wall order, and the maximal order, in *signed* width.

**Lemma 5.6.** Let $R_k=\sum_{i<k}b^{2i}$, with base-$b$ digits $1010\cdots01$. Then $w_b^\pm(R_k)=k$ for every $b\ge2$ and $k\ge0$.

*Proof.* For $b=2$, $R_k$ is in non-adjacent form, and the NAF has minimal weight (Reitwiesner). Let $b\ge3$, and let $v$ be a signed digit vector with $|v_e|\le b-1$ and $\sum v_eb^e=R_k$. Write $d$ for the digits of $R_k$. Put $\kappa_e=b^{-(e+1)}\sum_{i\le e}(v_i-d_i)b^i$, which is an integer, with $\kappa_{-1}=0$. Then $v_e=d_e+b\kappa_e-\kappa_{e-1}$ and $|\kappa_e|<\frac b{b-1}\le\frac32$, so $\kappa_e\in\{-1,0,1\}$. If $v_e=0$, then $b\kappa_e=\kappa_{e-1}-d_e\in\{-2,\dots,1\}$, which forces $\kappa_e=0$ and $\kappa_{e-1}=d_e$. At a position $e$ with $d_e=1$ and $v_e=0$ this gives $\kappa_{e-1}=1$. Then $v_{e-1}=b-\kappa_{e-2}\ne0$. At $e=0$ this case cannot occur, since $\kappa_{-1}=0$, so $v_0\ne0$. Each of the $k$ sets $\{0\}$ and $\{e-1,e\}$ for $e=2,4,\dots,2k-2$ therefore contains a nonzero entry of $v$. These sets are pairwise disjoint, so $v$ has at least $k$ nonzero entries, and the digit vector of $R_k$ has exactly $k$. $\square$

**Proposition 5.7 (wall-order and maximal signed width in $K_b$).** Let $k(m)$ be nondecreasing with $k(m)\equiv0\pmod{b-1}$, $k(1)=0$ and $\sum_mb^{2k(m)-m}<\infty$. Put $\Delta(m)=R_{k(m)}/(b-1)$, which is an integer since $R_k\equiv k\pmod{b-1}$. Let $c=\mathbf 1_{\{2^s:s\ge0\}}$ and

```math
\tilde a(m)=c(m)+\Delta(m+1)-b\,\Delta(m).
```

Then $F_b(\tilde a)=\Lambda_b=\sum_{s\ge0}b^{-2^s}$, an irrational element of $M_b\subseteq K_b$. At every non-jump index ($\Delta(m+1)=\Delta(m)$), $\tilde a(m)=c(m)-R_{k(m)}$ and $w_b^\pm(\tilde a(m))\ge k(m)-c(m)$.

- With $k(m)=(b-1)\lfloor\sqrt{\log_bm}\rfloor$, the signed width is $W_\pm(N)\asymp N\sqrt{\log N}$, the order of the entropy–multiplicity wall, and the support has density 1.
- With $k(m)=(b-1)\lfloor m/(4(b-1))\rfloor$, $W_\pm(N)\asymp N^2$. This is the maximal order, since $|a(m)|<b^m$ forces $W_\pm\le W\le N^2/2+O(N)$ (Phase 22 §3.4).

*Proof.* Lemma 5.1 with $-\Delta$ gives $F_b(\tilde a)=F_b(c)-\Delta(1)=\Lambda_b$. Convergence follows from $\Delta(m)\le b^{2k(m)}$. At non-jump $m$, Lemma 5.6 and $w^\pm(y\pm1)\ge w^\pm(y)-1$ give the weight bound. In the first family, jumps occur only at $m=b^{s^2}-1$, which is $O(\sqrt{\log N})$ indices. So $W_\pm(N)\ge\sum_{m\le N}(k(m)-1)-O(\sqrt{\log N}\cdot\sqrt{\log N})\gg N\sqrt{\log N}$. The upper bound is $W_\pm\le\sum(1+\log_b|\tilde a(m)|)\ll\sum(k(m)+1)$. In the second family the jump indices have density $\frac1{4(b-1)}$, and the non-jump indices alone give $W_\pm(N)\ge(1-\frac1{4(b-1)})\frac{N^2}8(1+o(1))$. $\square$

**Corollary 5.8.** Signed-digit width $\asymp N\sqrt{\log N}$, with support of density 1, is compatible with membership in $K_b$. The entropy–multiplicity wall (GF-27) limits local decompositions. It cannot decide $K_b$ membership of $E_b^4$, and by Theorem 5.2 no width statement about the coefficients can.

Finite measurements (signed widths are exact minimal weights; base 2 uses the NAF formula, checked against the dynamic program below $2^{14}$):

| $b$ | family | $N$ | $W_\pm/N$ | $W_\pm/N^2$ | $W_{\rm raw}/N$ | support density |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | $\sqrt{\log}$ | 3000 | 2.822 | 0.00094 | 4.649 | 0.9990 |
| 2 | maximal | 360 | 44.986 | 0.12496 | 88.761 | 0.9972 |
| 3 | $\sqrt{\log}$ | 3000 | 3.943 | 0.00131 | 6.893 | 1.0000 |
| 3 | maximal | 360 | 44.492 | 0.12359 | 87.900 | 0.9917 |

The value of every one of these series is $\Lambda_b$. Its digit statistics at $N=4000$ ($b=2$) are $\chi_N/N=0.0053$ and $\sigma_N/N=0.0027$ (§6).

### 5.4 What would decide $E_b^4$

**Proposition 5.9 (carry-residue criterion).** Let $A\ge0$, $C>0$ and $|a(m)|\le Cm^A$ for $m\ge1$, and put $T(n,L)=\sum_{j>L}a(n+j)b^{-j}$. There is an integer $\kappa=\kappa(b,A,C)\ge0$ such that, with $L(n)=\lceil(A+2)\log_b(n+2)\rceil+\kappa\ge1$, we have $|T(n,L(n))|\le(n+2)^{-2}$ for every $n\ge0$. Then, for every $c\in F_b$,

```math
\Bigl|M_N(x-c;b)-\frac1N\sum_{n<N}\Bigl\|\frac{\rho_n}{b^{L(n)}}-c\Bigr\|\Bigr|\le\frac1N,\qquad \rho_n=\sum_{j=1}^{L(n)}a(n+j)\,b^{L(n)-j}\bmod b^{L(n)} .
```

So $F_b(a)\in K_b$ iff the carry residues $\rho_n/b^{L(n)}$ concentrate, in mean, at one point of $F_b$.

*Proof.* Tail: put $L=L(n)$ and let $r\ge1$. Since $L\le(A+2)\log_b(n+2)+1+\kappa$, $\log_b(n+2)\le n+2$ and $n+2\ge1$,

```math
n+L+r\ \le\ (n+2)(A+3)+(1+\kappa+r)\ \le\ (n+2)(A+4+\kappa+r)\ \le\ (n+2)(1+\kappa)(A+4+r).
```

As $A\ge0$, raising to the power $A$ preserves these inequalities. With $b^{-L}\le b^{-\kappa}(n+2)^{-(A+2)}$,

```math
|T(n,L)|\ \le\ C\,b^{-L}\sum_{r\ge1}(n+L+r)^Ab^{-r}\ \le\ (n+2)^{-2}\cdot C\,(1+\kappa)^A\,b^{-\kappa}\,S_A,\qquad S_A=\sum_{r\ge1}(A+4+r)^Ab^{-r}<\infty .
```

Since $b^{-\kappa}$ decays exponentially and $(1+\kappa)^A$ grows polynomially, $C(1+\kappa)^Ab^{-\kappa}S_A\le1$ for all large $\kappa$. Fix such a $\kappa$. Criterion: $x_n\equiv\rho_n/b^{L(n)}+T(n,L(n))\pmod1$ (Phase 20 Lemma D1.1), and $b^nc\equiv c\pmod1$ for $c\in F_b$. Since $t\mapsto\|t\|$ is 1-Lipschitz, each term of $M_N(x-c;b)$ differs from $\|\rho_n/b^{L(n)}-c\|$ by at most $(n+2)^{-2}$, and $\sum_{n\ge0}(n+2)^{-2}=\frac{\pi^2}6-1<1$. $\square$

For $E_b^4$, $E_b^6$, $E_b^8$, $D(\Theta_3^2)$ and $D(E_b^2)$, $A$ is fixed and $L(n)\asymp\log n$. The exact arithmetic quantity is therefore the joint law of the triangular residues $(a(n+j)\bmod b^j)_{j\le L(n)}$, as in Phase 20 Lemma D1.4. "Irreversible carry mixing" means that $\rho_n/b^{L(n)}$ equidistributes. "Collapse" means that it concentrates at a point of $F_b$, which by Theorem 5.5 is the same as $\chi_N=o(N)$. Neither has been proved for any of these series. The finite data of §6 put all five next to $X_2$ and $\Lambda$-type behaviour far away.

## 6. Finite measurements (base 2, $N=4000$; not evidence)

Digits are certified from exact coefficient sums with an adaptive guard and an explicit tail bound. Orbit points use 64-bit windows, and $D_N$ is computed by the exact formula $\frac1N+\max z-\min z$. $\sigma_N$ is the exact dynamic program of Theorem 5.5 with $B=1$.

| constant | $D_{1000}$ | $D_{2000}$ | $D_{4000}$ | $\mu_{4000}$ | $\chi_N/N$ | $\sigma_N/N$ | freq. of 1 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $X_2$ | 0.0301 | 0.0228 | 0.0220 | 0.25141 | 0.5080 | 0.3357 | 0.5042 |
| $Y_2=1/X_2$ | 0.3502 | 0.3502 | 0.3502 | 0.30623 | 0.6665 | 0.5000 | 0.5000 |
| $X_{2,3}$ | 0.0349 | 0.0366 | 0.0304 | 0.25207 | 0.5098 | 0.3375 | 0.5180 |
| $Y_{2,3}=1/X_{2,3}$ | 0.7640 | 0.8467 | 0.8457 | 0.02775 | 0.0428 | 0.0320 | 0.7265 |
| $\Lambda_2$ | 0.9482 | 0.9676 | 0.9801 | 0.00255 | 0.0053 | 0.0027 | 0.0030 |
| $E_2^2$ | 0.0442 | 0.0572 | 0.0674 | 0.23375 | 0.4560 | 0.3045 | 0.4823 |
| $E_2^4$ | 0.0397 | 0.0178 | 0.0152 | 0.25197 | 0.5050 | 0.3387 | 0.4938 |
| $E_2^6$ | 0.0347 | 0.0232 | 0.0205 | 0.25286 | 0.5165 | 0.3367 | 0.4963 |
| $E_2^8$ | 0.0277 | 0.0173 | 0.0158 | 0.25136 | 0.5075 | 0.3360 | 0.4950 |
| $D(\Theta_3(1/2)^2)$ | 0.0251 | 0.0208 | 0.0140 | 0.25147 | 0.5068 | 0.3357 | 0.5042 |
| $D(E_2^2)$ | 0.0507 | 0.0372 | 0.0204 | 0.24860 | 0.4965 | 0.3317 | 0.5112 |

Remarks on the table.

- The $X_2$ row reproduces Phase 22 §2.8: $D_{1000}$, $D_{2000}$, $D_{4000}$, the frequency of 1 and the change density $0.5080$, which equals $\chi_N/N$ in base 2. Even though $\beta(n)$ is even for every $n\ge2$, the frequency of the binary digit 1 in $X_2$ is $0.5042$.
- The values $\sigma_N/N\approx0.336$ for the typical-looking constants are close to $\frac13$, the classical NAF density of random integers. $E_2^2\in K_2$ still has $\chi_N/N=0.456$ at $N=4000$, because its kernel convergence is slow (Phase 22 measured $0.40$ at $N=50{,}000$).
- $Y_{2,3}\in K_2$ and $\Lambda_2\in K_2$ (Theorem 3.4, Proposition 5.7) show small $\mu,\chi,\sigma$. At this length nothing separates $E_2^4,\dots,D(E_2^2)$ from $X_2$.
- Every row satisfies Lemma 5.3 and Theorem 5.5(c), checked by the script.

## 7. Lean 4 blueprint for `NormalityChecker/Phase23Cores.lean`

These statements are a blueprint. **None has been compiled or kernel-checked**, and none is cited as `Kernel-verified`. Each is finite or elementary, and the script checks every instance listed. Builds go through `hail` (AGENTS.md).

```lean
namespace Phase23Cores
open Finset Polynomial

/-- m-ary partition numbers via (1 - z) F(z) = F(z^m). -/
def maryPart (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => maryPart m n + if m ∣ n + 1 then maryPart m ((n + 1) / m) else 0
-- (termination: (n+1)/m < n+1 for m ≥ 2; add `decreasing_by`)

theorem maryPart_mul_add (m n i : ℕ) (hm : 2 ≤ m) (hi : i < m) :
    maryPart m (m * n + i) = ∑ k ∈ range (n + 1), maryPart m k
theorem binaryPart_even {n : ℕ} (hn : 2 ≤ n) : Even (maryPart 2 n)
theorem maryPart_pow_le (m k : ℕ) (hm : 2 ≤ m) :
    maryPart m (m ^ k) ≤ ∏ i ∈ range k, (m ^ i + 1)
theorem prod_le_maryPart_pow (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    ∏ i ∈ Ico 1 k, (m ^ (k - i) / k + 1) ≤ maryPart m (m ^ k)

/-- Finite Mahler identity (Phase 22 D3.13(a)) for X_{b^2} = (1 - 1/b) X_b.
    All arithmetic is in ℤ; the exponents M - n (n ≤ M) and M - 2 * k
    (k ≤ M / 2) are natural-number subtractions that never truncate. -/
theorem mahler_finite (b M : ℕ) :
    ((b : ℤ) - 1) * ∑ n ∈ range (M + 1), (maryPart 2 n : ℤ) * (b : ℤ) ^ (M - n)
      = (b : ℤ) * ∑ k ∈ range (M / 2 + 1), (maryPart 2 k : ℤ) * (b : ℤ) ^ (M - 2 * k)
        - (maryPart 2 M : ℤ)

/-- Truncated Thue–Morse product (Theorem 3.1, m = 2). -/
theorem prod_one_sub_X_two_pow (J : ℕ) :
    ∏ j ∈ range (J + 1), (1 - (X : ℤ[X]) ^ (2 ^ j))
      = ∑ n ∈ range (2 ^ (J + 1)), C ((-1 : ℤ) ^ (Nat.digits 2 n).sum) * X ^ n

/-- Radix telescoping (Lemma 5.1, finite form). -/
theorem radix_coboundary_sum (b M : ℕ) (Δ : ℕ → ℤ) :
    ∑ m ∈ Icc 1 M, ((b : ℤ) * Δ m - Δ (m + 1)) * (b : ℤ) ^ (M - m)
      = Δ 1 * (b : ℤ) ^ M - Δ (M + 1)

/-- Zero transitions of the carry transducer (Theorem 5.5(b)). -/
theorem zero_transition (b : ℕ) (hb : 2 ≤ b) (δ δ' : ℤ) (d : ℕ)
    (hδ : δ ∈ ({-1, 0, 1} : Finset ℤ)) (hδ' : δ' ∈ ({-1, 0, 1} : Finset ℤ)) (hd : d < b) :
    (d : ℤ) + b * δ - δ' = 0 ↔
      (δ = 0 ∧ δ' = 0 ∧ d = 0) ∨ (δ = 0 ∧ δ' = 1 ∧ d = 1) ∨ (δ = -1 ∧ δ' = -1 ∧ d = b - 1)

/-- Coset transport (Theorem 1.3(a)), arithmetic core. -/
theorem coset_transport (b r : ℤ) : r * (1 - b) ≡ 2 * r [ZMOD (b + 1)]

/-- Thue–Morse change count recursion (Lemma 3.2). -/
theorem tm_change_even (k : ℕ) : (Nat.digits 2 (2*k)).sum % 2 ≠ (Nat.digits 2 (2*k+1)).sum % 2

/-- Order instances (Theorem 4.1), by `decide`/`norm_num`. -/
example : orderOf (2 : ZMod 45) = 12 := by decide
example : orderOf (2 : ZMod (3 * 15 * 255)) = 360 := by decide
end Phase23Cores
```

Two further targets need more work. The first is the carry argument of Lemma 5.6, $w_b^\pm(R_k)\ge k$, for all $b\ge3$. The second is the three-window lemma of Theorem 5.5(c), which is a finite case check over $\{-1,0,1\}^4\times[0,b-1]^3$ for each fixed $b$.

## 8. Verification record

```sh
python -B scripts/phase23_binary_partition.py
```

The script uses the standard library only. Every identity, order, window and inequality certificate uses exact `int`/`Fraction` arithmetic, except the comparisons in Corollary 2.2 and the power form $2N^{\log_m2}$ in Theorem 3.4, which involve $\log_mn$ and are made in floating point with tolerance $10^{-9}$. The integer form $S_m(N)\le2^K-1$ behind the latter is checked exactly. It takes about 6–9 s, performs 609,971 checks and exits 0. Check labels follow the numbering of this note.

- **A.** Recurrences and product forms of $b_m$ ($m=2,3,4,5$). The finite Mahler identity of Phase 22 D3.13(a) for $b=2,3,10$ (the `mahler_finite` target of §7). Parity of $\beta$ for $2\le n\le17{,}000$. Theorem 2.1 for $m^k\le20{,}000$, and its integer form and Corollary 2.2 for every $n<17{,}000$ ($m=2$) and $n<20{,}000$ ($m=3,4,5$). The failure of the former constant $\log_m(C_m/2)$ at $k=1$ and the corrected constant, exactly for $3\le m\le10$. The constants $C_m$. Exact windows with $\tau=N^{-2}$ for $b=2,3,10$ and $N\le4000$, reproducing Phase 22's $44,52,70$. Both bounds of Proposition 2.3 by integer comparison, with $L^*$, $L^*<N$ and $2b^{-N/2}\le\tau/2$.
- **B.** The truncated identity of Theorem 3.1 for $m\in\{2,3,4,5,7\}$. Coefficientwise reciprocity through $z^{1200}$. The exact identities $X^{(J)}_bY^{[2^{J+1}]}_b=1$. Lemma 3.2 up to $70{,}000$, and cube-freeness for factors of length at most 6. The digit code of $Y_b$ on 4000 certified digits ($b=2,3,4,5,10$). $X_2=1/(2-4\tau_{\rm TM})$. The support bound $S_m(N)$ and $M_N(Y_{b,m})\le(S_m(N)+1)/N$.
- **C.** $T_J=2^JD_{J-1}$ for $b\in\{2,3,5,7,10\}$, $J\le6$, by exact order tests with complete factorizations (deterministic Miller–Rabin below $3.3\cdot10^{24}$, Pollard–Brent). The power-of-two classification. Theorem 4.3 in 43 cases. Tracking lengths $A_J$ and Lemma 4.2 for $J\ge1$. Consequence 4.4 in 24 m-ary cases, and the counterexample $b=m=J=2$ to the unclamped exponent. The Cartier identities of Proposition 4.5 through $y^{3000}$ for $k\le7$, and the 2-kernel prefix counts (finite measurement).
- **D.** The rational $\mathbb Z[1/b]$-module tests for $K_{b^k}$ and $\frac1{(b-1)^2}\notin K_b$. The class map $r\mapsto2r$ for $b\le24$. $X_{b^2}=\frac{b-1}bX_b$ on 600 certified digits for $b=2,3,10$, which for $b=2$ is the exact one-place binary shift.
- **E.** Lemma 5.1. Theorem 5.2 on 300 random sequences: the gauge identity, integrality, $\delta_1=F_b(a')-F_b(d)$, the growth bound of (a), and the kernel shift $\delta+c\,b^{m-1}$ of (b). Theorem 5.5(b) for $b\le16$ and the three-window lemma for $b\le7$. The dynamic program against brute force (70 instances). Lemma 5.3, Theorem 5.4 and Theorem 5.5(c) on 500 exact rationals. The discrepancy formula with ties against brute force (150 orbits). The NAF formula below $2^{14}$ and $w_b^\pm(R_k)=k$ for $b\le7$, $k\le15$. The finite telescoping and the width bounds of Proposition 5.7, with raw widths from exact base-$b$ digit counts.
- **F.** Certified digits and the §6 table. $D_N(Y_2)\ge\frac14$, $D_N(Y_b)\ge2b^{-2}$ (no orbit point in $[0,b^{-2})$ or $[1-b^{-2},1)$) and $D_N(Y_b)\le1-\frac4{15b^2}$ at $N=3970$ ($b=3,4,5$). Coefficient majorants $|a(n)|\le2^{n/8}$ for the tail clause of the digit certification. These are checked exactly on finite grids: $n\le17{,}000$ for $\beta$ (via $U_K$), $2000\le n\le20{,}000$ for $b_3,b_4,b_5$, and $2000\le n\le9000$ for the series of §6. Beyond these grids the majorant rests on analytic growth bounds (Theorem 2.1 for $b_m$, polynomial growth for the eta and theta series, boundedness for $Y_b$, $Y_{2,3}$ and $\Lambda_2$), not on the script.

## 9. Open problems

1. $K_b$ membership, normality, $D^+<1$ or $D^->0$ for $X_b$, in any base. By Theorem 1.1, a proof of $X_{b^{2^r}}\notin K_{b^{2^r}}$ for one $r$ would give $X_b\notin K_b$.
2. For $b=2$: is $X_2\in K_4\setminus K_2$ possible? By Theorem 1.3(d) this would force binary change density $\to1$ and $D_N(X_2;2)\to\frac23$.
3. $m\ge3$: $X_{b,m}=1/Y_{b,m}$ with $Y_{b,m}\in M_b$. Decide whether $X_{b,m}\in K_b$. This is the polylogarithmic-window analogue of $P_b=1/E_b$.
4. Whether the base-$b$ digit sequence of $X_b$ is automatic. Separately, whether $\beta\bmod q$ is 2-automatic for some modulus $q$ with an odd prime factor, for example $q=3$. For $q=2^L$ it is, for every $L\ge1$ (Proposition 4.5), and that does not settle the digits of $X_2$, because the carry window is unbounded (Proposition 2.3).
5. A decomposition-free lower bound $\chi_N(E_b^4-c)\gg N$ for every $c\in F_b$. By Theorem 5.5 this is equivalent to $E_b^4\notin K_b$, and by Proposition 5.9 to non-concentration of the carry residues.
6. The exact limit discrepancy $D(\mu_{Y_b})$ of the Thue–Morse reciprocal.

## References

- J.-P. Allouche and J. Shallit, *Automatic Sequences*, Cambridge 2003 (Thm. 6.6.2: finite $k$-kernel characterization of $k$-automatic sequences; Thm. 16.3.1: polynomial growth of $k$-regular sequences).
- R. F. Churchhouse, Congruence properties of the binary partition function, Proc. Cambridge Philos. Soc. 66 (1969) (context for Proposition 4.5; not used in the proof).
- Ø. J. Rødseth, Some arithmetical properties of $m$-ary partitions, Proc. Cambridge Philos. Soc. 68 (1970) (context for Proposition 4.5; not used in the proof).
- B. Adamczewski and Y. Bugeaud, On the complexity of algebraic numbers I, Ann. of Math. 165 (2007).
- Y. Bugeaud, On the rational approximation to the Thue–Morse–Mahler numbers, Ann. Inst. Fourier 61 (2011) 2065–2076.
- N. G. de Bruijn, On Mahler's partition problem, Indag. Math. 10 (1948).
- M. Keane, Generalized Morse sequences, Z. Wahrscheinlichkeitstheorie verw. Geb. 10 (1968).
- K. Mahler, Arithmetische Eigenschaften der Lösungen einer Klasse von Funktionalgleichungen, Math. Ann. 101 (1929); On a special functional equation, J. London Math. Soc. 15 (1940).
- K. Nishioka, *Mahler Functions and Transcendence*, LNM 1631, Springer 1996.
- G. W. Reitwiesner, Binary arithmetic, Advances in Computers 1 (1960).
- A. Thue, Über die gegenseitige Lage gleicher Teile gewisser Zeichenreihen, Norske Vid. Selsk. Skr. I (1912).
- D. D. Wall, *Normal Numbers*, PhD thesis, Berkeley 1949.
- Phase 19 [geometry](../phase19/geometry.md); Phase 20 [dense-and-partitions](../phase20/dense-and-partitions.md); Phase 22 [partitions-carry-and-lemma-s](../phase22/partitions-carry-and-lemma-s.md) and [odd-characters-and-kernel-quotient](../phase22/odd-characters-and-kernel-quotient.md).
