# Dense coefficient series, the partition constant and products in the discrepancy kernel

Phase 20, Tracks D1–D4. Fix an integer radix $b\ge2$ and write $x_n=\{b^nx\}$, $D_N(x)$ for the extreme interval discrepancy of $x_0,\dots,x_{N-1}$, and $\|\cdot\|$ for distance to the nearest integer. As in Phase 19,

```math
K_b=\{z:\ D_N(z)\to1\}=F_b+\{w:\ M_N(w)\to0\},\qquad F_b=\{c:\ (b-1)c\in\mathbb Z\},\qquad M_N(w)=\frac1N\sum_{n<N}\|b^nw\|.
```

For an integer sequence $a$ put $F_b(a)=\sum_{m\ge0}a(m)b^{-m}$, $S_a(X)=\#\{1\le m\le X:\ a(m)\ne0\}$ and $A_a(X)=\sum_{1\le m\le X}|a(m)|$. The Euler value is $E_b=\prod_{k\ge1}(1-b^{-k})$ and the partition constant is $P_b=\sum_{n\ge0}p(n)b^{-n}=1/E_b$. Eisenstein series are always written with their argument, $E_2(q),E_4(q),E_6(q)$, to avoid a clash with $E_b$.

**Summary of conclusions.**

| Result | Status |
| --- | --- |
| D1. Exact carry-window transfer, explicit certified windows $L(N)$ for polynomial and $e^{\alpha\sqrt m}$ growth, triangular reduction and coordinate freedom, concrete criteria (i)–(iv) | Paper proofs (§1) |
| D2. $p(n)\le e^{\pi\sqrt{2n/3}}$ and window $L(N)=(\pi\sqrt{2/3}/\log b)\sqrt N+O(\log N)$, sharp to first order | Paper proof (§2.1) |
| D2. Pentagonal recurrence on the circle; a rate-conditional exclusion of nonzero fixed points | Paper proof (§2.2) |
| D2. Congruence wash-out: congruences on $p(m)$ alone carry no digit information; the exact surviving trace | Paper proof (§2.3) |
| D2. $P_b$ transcendental; $E_b$, $E_2(1/b)$, $E_4(1/b)$ algebraically independent | From Nesterenko (§2.4) |
| D2. Normality, simple normality, $D^+(P_b)<1$, $P_b\notin K_b$ | **Open** (§2.5) |
| D3. $\Theta_3(1/b)$, $\Theta_3(1/b)^2$, every binary theta $\Theta_Q(1/b)$, every $L_\chi(b)$ for real nonprincipal $\chi$, $E_b$ and $E_b^3$ lie in $K_b$ in **every** base | Paper proof from Track B1; $E_b,E_b^3$ also in Lean (§3.1) |
| D3. $\Theta^3$, $\Theta^4$, $E_{2,4,6}(1/b)$, $\Delta(1/b)$, $E_b^{4},E_b^6$: distributional status | **Open**; exact transfers $\Theta^4\equiv16L_{\chi_4}^2$, $\Theta^3\equiv4\Theta L_{\chi_4}$ mod $K_b$ (§3.2) |
| D4. Sumset criterion for $xy\in K_b$; both outcomes occur on the critical line | Paper proof (§4.1) |
| D4. $K_b$ is not closed under squaring | Paper proof (§4.2) |
| D4. Exact reciprocal test for radix-primary rationals | Paper proof (§4.3) |
| D4. Sparse $z$ with $1-z\in K_2$ and $\liminf D_N(1/(1-z))=0$, with any prescribed lacunarity | Paper proof (§4.4) |

The finite computations are in [`scripts/phase20_dense_classical.py`](../../scripts/phase20_dense_classical.py) (§5). Lean declarations cited from [`CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean), [`EulerPentagonal.lean`](../../NormalityChecker/EulerPentagonal.lean), and [`CharacterLambertTransfer.lean`](../../NormalityChecker/CharacterLambertTransfer.lean) are built and kernel-verified.

## 1. D1 — the carry-window transfer framework

### 1.1 Exact transfer

Let $a$ be integer-valued with $\sum|a(m)|b^{-m}<\infty$ and $x=F_b(a)$. For $n\ge0$ and $L\ge1$ define

```math
R_{n,L}=\Big(\sum_{j=1}^{L}a(n+j)\,b^{L-j}\Big)\bmod b^L\in\{0,\dots,b^L-1\},\qquad
T(n,L)=\Big|\sum_{j>L}a(n+j)\,b^{-j}\Big|.
```

**Lemma D1.1.** $\big\|x_n-R_{n,L}/b^L\big\|\le T(n,L)$. If $a\ge0$, then $x_n\equiv R_{n,L}/b^L+\tau$ (mod 1) with $0\le\tau=T(n,L)$. Consequently, for $y_n=R_{n,L}/b^L$ and any choice $L=L(N)$,

```math
|D_N(x)-D_N(y_0,\dots,y_{N-1})|\le 2\max_{n<N}T(n,L(N)).
```

*Proof.* $b^nx=\sum_{m\le n}a(m)b^{n-m}+\sum_{j\ge1}a(n+j)b^{-j}$, and the first sum is an integer. The sum over $1\le j\le L$ equals $b^{-L}\sum_ja(n+j)b^{L-j}\equiv R_{n,L}/b^L$ (mod 1). The discrepancy statement is the Phase 18 finite comparison with no bad samples. ∎

### 1.2 Certified windows

**Lemma D1.2 (polynomial growth).** Suppose $|a(m)|\le Cm^k$ for $m\ge1$, with $C\ge1$ and $k\ge0$. For $2\le L+1\le N$ with $L+1\ge 2k/\log b$ and all $0\le n<N$,

```math
T(n,L)\le C\,2^{k}\,b^{-L}\Big(\frac{N^k}{b-1}+\frac{(L+1)^k}{b(1-b^{-1/2})}\Big)\le \frac{2^{k+1}C}{1-b^{-1/2}}\,N^kb^{-L}.
```

Hence $L(N)=\lceil (A+k)\log_bN+\log_b(2^{k+1}C/(1-b^{-1/2}))\rceil=(A+k)\log_bN+O_{b,k,C}(1)$ gives $T(n,L(N))\le N^{-A}$ uniformly for $n<N$.

*Proof.* $(n+j)^k\le2^k(N^k+j^k)$. The ratio of consecutive terms of $\sum_{j>L}j^kb^{-j}$ is $(1+1/j)^kb^{-1}\le e^{k/j}/b\le b^{-1/2}$ once $j\ge2k/\log b$, so that sum is at most $(L+1)^kb^{-L-1}/(1-b^{-1/2})$. ∎

**Lemma D1.3 (subexponential growth).** Suppose $|a(m)|\le Ce^{\alpha\sqrt m}$ with $C\ge1$, $\alpha>0$. If $N\ge(\alpha/\log b)^2$ then for all $L\ge1$ and $0\le n<N$,

```math
T(n,L)\le \frac{C}{\sqrt b-1}\exp\Big(\alpha\sqrt N-L\big(\log b-\tfrac{\alpha}{2\sqrt N}\big)\Big).
```

Put

```math
L(N)=\Big\lceil\frac{\alpha\sqrt N+A\log N+\log\big(C/(\sqrt b-1)\big)+\alpha^2/\log b}{\log b}\Big\rceil .
```

Whenever $L(N)\le2\alpha\sqrt N/\log b$ (true for all large $N$), $T(n,L(N))\le N^{-A}$ for every $n<N$, and $L(N)=(\alpha/\log b)\sqrt N+(A/\log b)\log N+O_{\alpha,b,C}(1)$.

*Proof.* For $n<N$, $\sqrt{n+j}\le\sqrt{N+j}\le\sqrt N+j/(2\sqrt N)$ by concavity. With $\lambda=\log b-\alpha/(2\sqrt N)\ge\tfrac12\log b$ we get $T\le Ce^{\alpha\sqrt N}\sum_{j>L}e^{-\lambda j}=Ce^{\alpha\sqrt N}e^{-\lambda L}/(e^\lambda-1)$ and $e^\lambda\ge\sqrt b$. For the window, $\alpha L/(2\sqrt N)\le\alpha^2/\log b$, so the exponent is at most $-A\log N-\log(C/(\sqrt b-1))$. ∎

### 1.3 Triangular reduction and coordinate freedom

Because $a(n+j)b^{L-j}$ modulo $b^L$ depends only on $a(n+j)$ modulo $b^j$,

```math
\frac{R_{n,L}}{b^L}\equiv\sum_{j=1}^{L}\frac{v_j(n)}{b^{j}}\pmod 1,\qquad v_j(n)=a(n+j)\bmod b^j .
```

Thus $y_n$ is a function of the **triangular residue vector** $V_n=(v_1(n),\dots,v_L(n))\in\prod_{j\le L}\mathbb Z/b^j$, through the surjective homomorphism $V\mapsto\sum_jv_jb^{L-j}$ onto $\mathbb Z/b^L$.

**Lemma D1.4 (coordinate freedom).** For any $S\subseteq\{1,\dots,L-1\}$, any prescribed values of $v_j$ for $j\in S$, and any target $t\in b^{-L}\mathbb Z/\mathbb Z$, some choice of the coordinates outside $S$ gives $y_n=t$. In particular every base-$b$ digit of $y_n$ (hence of $x_n$, up to the boundary set of Lemma D1.1) is a surjective function of the free coordinates.

*Proof.* $v_L$ alone moves $y_n$ through the whole grid $b^{-L}\mathbb Z/\mathbb Z$. ∎

This is the structural reason why **residue information on a proper subset of coordinates cannot force any digit statistic**: one needs the joint law of all coordinates up to the cutoff (or a growth/sparsity property making the late coordinates predictable, as in the sparse case below). For the partition function Lemma D1.3 makes $L(N)\asymp\sqrt N$, so the relevant object is the joint distribution of $(p(n+j)\bmod b^j)_{j\lesssim3.7\sqrt N}$.

### 1.4 Concrete sufficient conditions

Fix $A\ge2$ and a certified window $L=L(N)$ with $\max_{n<N}T(n,L)\le N^{-A}$. Write $y_n=R_{n,L(N)}/b^{L(N)}$; it depends on $N$ through $L(N)$.

**(i) Full normality.** By Wall's theorem $x$ is normal in base $b$ iff $(x_n)$ is equidistributed. Lemma D1.1 and $|e(hx_n)-e(hy_n)|\le2\pi|h|N^{-A}$ give: $x$ is normal iff for every integer $h\ne0$,

```math
\frac1N\sum_{n<N}\ \prod_{j=1}^{L(N)} e\Big(\frac{h\,v_j(n)}{b^j}\Big)\longrightarrow0 .
```

Quantitatively, by the Erdős–Turán inequality with absolute constants $c_1,c_2$ (Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Ch. 2, Thm. 2.5), for every $H\ge1$,

```math
D_N(x)\le 2N^{-A}+\frac{c_1}{H+1}+c_2\sum_{h=1}^{H}\frac1h\Big|\frac1N\sum_{n<N}e\big(hR_{n,L(N)}/b^{L(N)}\big)\Big| .
```

The content beyond Wall's theorem is that the Weyl sums are finite sums over a fixed residue vector of length $L(N)$, and that the factors with $b^j\mid h$ drop out.

**(ii) Simple nonnormality.** Assume $a\ge0$. Then the first digit of $x_n$ equals the top digit $\lfloor R_{n,L}/b^{L-1}\rfloor$ unless $R_{n,L}\bmod b^{L-1}\ge b^{L-1}-\lceil b^{L}N^{-A}\rceil$ (the one-sided tail can only carry upward). Let $E_N$ count these boundary shifts. If $E_N=o(N)$ and for some digit $d$

```math
\limsup_{N}\Big|\frac{\#\{n<N:\lfloor R_{n,L(N)}/b^{L(N)-1}\rfloor=d\}}{N}-\frac1b\Big|>0,
```

then $x$ is not simply normal. For signed coefficients use a two-sided boundary zone.

**(iii) Positive coverage, $D^+<1$.** Let $U_b\subset[0,1)$ be the set of points whose first two base-$b$ digits differ (in base 2 this is exactly $[1/4,3/4)$).

**Lemma D1.5.** For every real $x$ and $N\ge2$, with $\theta_N=\#\{n<N:x_n\in U_b\}/N$,

```math
1-D_N(x)\ \ge\ \min\Big(\theta_N,\ \frac12-\frac1{2N},\ \frac1{b^3}\Big).
```

*Proof.* The circle distance from $U_b$ to $F_b$ is at least $g_b=1/(b^2(b-1))$: the fixed point $c/(b-1)=0.ccc\ldots$ lies in the equal-digit cylinder $[cc]$ at distances $c/(b^2(b-1))$ and $(b-1-c)/(b^2(b-1))$ from its ends, and $0$ is flanked on the circle by $[00]$ and $[(b-1)(b-1)]$. By the concentration formula (Phase 19), $1-D_N=\inf_J\{1-\mu_N(J)+|J|\}$ over half-open arcs. Take an arc $J$ of length $l<g_b(b-1)/b=b^{-3}$ with $\mu_N(J)>\tfrac12+\tfrac1{2N}$. Then more than $(N+1)/2$ of the indices have $x_n\in J$, so some $n\le N-2$ has $x_n,x_{n+1}=bx_n\in J$. With $c$ the centre, $\|(b-1)c\|\le\|bc-bx_n\|+\|bx_n-c\|\le(b+1)l/2$, so $c$ lies within $(b+1)l/(2(b-1))$ of some $f\in F_b$ and $J$ lies in the ball of radius $bl/(b-1)<g_b$ about $f$. Hence $J\cap U_b=\emptyset$ and $1-\mu_N(J)\ge\theta_N$. Arcs with $l\ge b^{-3}$ or $\mu_N(J)\le\frac12+\frac1{2N}$ satisfy the bound trivially. ∎

In binary the Lean bound `sharp_finite_discrepancy`, $D_N\le\max(2/3,1-T_N/N)+1/N$, has better constants. Transfer to the window: for $a\ge0$, $x_n\in U_b$ whenever $y_n\in U_b$ and $R_{n,L}\bmod b^{L-2}<b^{L-2}-\lceil b^LN^{-A}\rceil$. So **a positive lower density of shifts whose packed residue has two distinct top digits away from the $N^{-A}$-boundary implies $D^+(x)<1$**, uniformly in the base.

**(iv) Maximal discrepancy.** The sparse-support criterion of Track B1 (Lean: `CoefficientTransfer.finite_sparse_mass_transfer`, `linear_mass_sparse_tendsto_one`) states: if $A_a(X)\le CX$ for all $X$, then for all $N,L\ge1$, $\varepsilon>0$,

```math
1-D_N(x)\le2\varepsilon+\frac{L\,S_a(N+L)}{N}+\frac{C(N+L+2)}{N\varepsilon b^L},
```

so $S_a(X)=o(X)$ and $A_a(X)=O(X)$ imply $x\in K_b$ with limiting fixed point $0$. In window language the vector $V_n$ vanishes on $(n,n+L]$ for most $n$.

*Digit-width refinement.* Let $w(m)=1+\lfloor\log_b|a(m)|\rfloor$ for $a(m)\ne0$ and $W_a(X)=\sum_{m\le X,\,a(m)\ne0}w(m)$. If $|a(m)|\le Cm^k$ and $W_a(X)=o(X)$, then $x\in K_b$. Expand each $|a(m)|$ in base $b$ and charge only the shifts within $L$ of an occupied *digit* position; the number of charged shifts is at most $W_a(2N+2L)+(L-1)S_a(2N+2L)$, and Markov's inequality applied to the digit tails bounds the rest by $b^{-L}\varepsilon^{-1}(W_a(2N+2L)+O(\log N))$. By Jensen, $W_a\le S_a(1+\log_b(A_a/S_a))$, so this condition is implied by $S_a=o(X)$, $A_a=O(X)$, and it also allows a superlinear mass with very sparse support.

**What arithmetic input would trigger (ii) or (iii).** By Lemma D1.4 no statistic of a proper subset of the coordinates $v_j(n)$ suffices. For a dense, growing $a$ the minimal input is the law of the top one or two digits of $\sum_{j\le L(N)}v_j(n)b^{-j}$, that is, of the real carry $\{\sum_{j\ge1}a(n+j)b^{-j}\}$. This is a distribution-mod-one statement of the same strength as the conclusion. For $a(m)=m^k$ the number $x$ is rational, so the problem is genuinely about nonpolynomial sequences. Current number theory supplies:

- for sparse $a$ with linear mass, criterion (iv) (Phase 17, Track B1);
- for sparse multiplicative $a$, planted-pattern counts giving (iii) together with (iv) (Phase 17);
- for dense $a$ such as $p(n)$, $\tau(n)$ or $\sigma_k(n)$, nothing at the required strength. Even the one-coordinate statistic $p(n)\bmod2$ is open: Parkin–Shanks predicts density $1/2$ for each parity, while the best lower bounds for the counts are of order $\sqrt X$ up to logarithmic factors (Bellaïche–Nicolas, Ramanujan J. 2016; Bellaïche–Green–Soundararajan; Q.-Y. Zheng, arXiv:2509.09553). By Lemma D1.4, even a solution of Parkin–Shanks would not by itself give (ii) or (iii).

## 2. D2 — the partition constant $P_b=1/E_b$

### 2.1 Growth and the certified window

**Elementary bound.** For all $n\ge0$, $p(n)\le e^{\pi\sqrt{2n/3}}$. For $0<q<1$, $p(n)q^n\le P(q)=\prod(1-q^k)^{-1}$ and

```math
\log P(q)=\sum_{j\ge1}\frac1j\frac{q^j}{1-q^j}\le\frac{q}{1-q}\sum_j\frac1{j^2}=\frac{\pi^2}{6}\frac{q}{1-q},
```

using $q^j/(1-q^j)\le q/(j(1-q))$, which follows from $1+q+\dots+q^{j-1}\ge jq^{j-1}$. Put $q=e^{-t}$, so $q/(1-q)\le1/t$, and choose $t=\pi/\sqrt{6n}$.

**Window.** Lemma D1.3 with $C=1$ and $\alpha=\pi\sqrt{2/3}\approx2.5651$ gives the certified window

```math
L(N)=\frac{\pi\sqrt{2/3}}{\log b}\sqrt N+\frac{A}{\log b}\log N+O_b(1).
```

**It is sharp to first order.** Since $p$ is positive and increasing, $T(N-1,L)\ge p(N+L)b^{-L-1}$. By Hardy–Ramanujan, $p(n)\sim e^{\pi\sqrt{2n/3}}/(4\sqrt3\,n)$, so any $L$ with $T(N-1,L)<1$ satisfies $L\ge(\pi\sqrt{2/3}/\log b)\sqrt N-O(\log N)$. The certified windows computed in §5 (for example $L=251$ against $L(N)=273$ for $b=2$, $N=4000$) agree with this.

### 2.2 The pentagonal recurrence on the circle

Let $g_k=k(3k-1)/2$ for $k\in\mathbb Z\setminus\{0\}$ (generalized pentagonal numbers $1,2,5,7,12,15,\dots$) and $\varepsilon_k=(-1)^{k+1}$. Euler's theorem gives $E_b=1-z$ with $z=\sum_{k\ne0}\varepsilon_kb^{-g_k}$, and $P_b=1+zP_b$. Multiplying by $b^n$:

**Proposition D2.1.** With $x_n=\{b^nP_b\}$,

```math
x_n\equiv\sum_{0<g_k\le n}\varepsilon_k\,x_{n-g_k}+\rho_n\pmod 1,\qquad \rho_n=\sum_{g_k>n}\varepsilon_k\,b^{n-g_k}P_b,
```

with $|\rho_n|\le\frac{b}{b-1}P_b\,b^{-(g^+(n)-n)}$, where $g^+(n)$ is the least generalized pentagonal number exceeding $n$. On integers this is Euler's recurrence for $p(n)$. On the circle it couples $x_n$ to about $2\sqrt{2n/3}$ earlier shifts with signs $++--++--\cdots$.

**Proposition D2.2 (rate-conditional).** Let $b\ge3$. If $P_b\in K_b$ with limiting fixed point $c$ and $M_N(P_b-c)=o(N^{-1/2})$, then $c\equiv0$.

*Proof.* Let $s_n=\sum_{0<g_k\le n}\varepsilon_k$. Its values follow the partial sums $1,2,1,0,\dots$ of the sign pattern. Since $[g_{-k},g_{k+1})$ has length $2k+1$ and $[g_k,g_{-k})$ has length $k$, the set $\{n:s_n=0\}$ has density $1/3$. Write $x_m=c+\delta_m$ on the circle. Proposition D2.1 gives $\|(1-s_n)c\|\le|\delta_n|+\sum_{g_k\le n}|\delta_{n-g_k}|+|\rho_n|$. Average over $n<N$ with $s_n=0$. The right side is at most $(1+2\sqrt{2N/3})M_N+O(N^{-1/2})$, because $\sum_n|\rho_n|=O(\#\{g_k\le N\})$. The left side is $(1/3+o(1))\|c\|$. ∎

In base 2 the statement is vacuous ($F_2=\{0\}$). The recurrence cannot exclude $c=0$: the identically small orbit is consistent with it, and its large kicks $\rho_n\approx\pm P_b b^{-1}$ occur only for the $O(\sqrt N)$ shifts just before pentagonal numbers.

### 2.3 Ramanujan congruences leave no forced trace

**Proposition D2.3 (wash-out).** Let $Z\subset\mathbb Z_{\ge1}$ contain no two consecutive integers. Every real number $u$ has an integer representation $u=\sum_m a^*(m)b^{-m}$ with $a^*(m)=0$ for $m\in Z$ and $0\le a^*(m)\le b^2-1$.

*Proof.* Take the base-$b$ digits $d_m$ of $u$ and move each digit at $m\in Z$ to $m+1\notin Z$, using $d_mb^{-m}=(bd_m)b^{-(m+1)}$. ∎

Consequently a congruence $b\mid a(m)$ on a set $Z$, which allows an exact integral reindexing that empties $Z$, places **no restriction whatever** on the digits of $F_b(a)$. For $p(5k+4)\equiv0\pmod5$ in base 5 or 10, the reindexing is $a'(5k+3)=p(5k+3)+p(5k+4)/5$, $a'(5k+4)=0$. Any digit consequence must come from sizes and joint residues, as Lemma D1.4 says.

**The exact surviving trace.** Put $T_m=\sum_{j\ge1}p(m+j)b^{-j}$. Then $bT_n=p(n+1)+T_{n+1}$ and

```math
d_1(x_n)\equiv p(n+1)+\lfloor T_{n+1}\rfloor\pmod b .
```

In base 5 on $n\equiv3\pmod5$ this reduces to $d_1(x_n)\equiv\lfloor T_{n+1}\rfloor$. That is the full content of the congruence. The carry $\lfloor T_{n+1}\rfloor\approx p(n+1)/(b-1)$ is a huge integer whose residue modulo $b$ depends on $p(n+2)\bmod b^2$, $p(n+3)\bmod b^3$, and so on. In triangular coordinates the congruence fixes $v_1=0$ at those shifts, and Lemma D1.4 shows that this constrains no digit. Higher congruences $p(5^kn+\delta_k)\equiv0\pmod{5^k}$ fix $v_j(m-j)=0$ for $j\le k$ at the corresponding offsets. Again the top digit is free through $v_{k+1},v_{k+2},\dots$.

Finite check (§5): over $n<4000$ the first digits of $x_n$ on the congruence classes give $\chi^2=4.9$ ($b=5$, 4 d.f.), $4.3$ ($b=7$, 6 d.f.), $11.8$ ($b=10$, 9 d.f.) and $8.9$ ($b=11$, 10 d.f.). No bias is visible.

### 2.4 Transcendence and algebraic independence

Nesterenko (Sb. Math. 187 (1996)) proved that for algebraic $q$ with $0<|q|<1$ the Ramanujan values $E_2(q),E_4(q),E_6(q)$ are algebraically independent. Since $1728\,q\prod(1-q^n)^{24}=E_4(q)^3-E_6(q)^2$, an algebraic $E_b$ would give an algebraic relation between $E_4(1/b)$ and $E_6(1/b)$. Hence $E_b$ and $P_b=1/E_b$ are transcendental. Moreover $E_6(1/b)$ is algebraic over $\mathbb Q(E_4(1/b),E_b)$, so $E_2(1/b),E_4(1/b),E_b$ are algebraically independent.

### 2.5 What is and is not known for $P_b$

- **Known:** transcendence; the exact identities above; certified digits (§5).
- **Open:** normality, simple normality, $D^+(P_b)<1$, and even $P_b\notin K_b$. We found no argument for any of them, and none is in the literature we checked.

Why the natural routes fail:

1. **Reciprocals.** $E_b\in K_b$ (Phase 18 sparse signed digits; Lean `EulerPentagonal.eulerPentagonal_discrepancy_tendsto_one`). But $K_b$ is neither closed nor anti-closed under inversion. §4.4 gives sparse $x\in K_2$ with $\liminf D_N(1/x)=0$, while Theorem D4.3 gives $x,1/x\in K_b$ for every $x=d/b^j$ with $d\mid b-1$. In the irrational binary setting, Bergelson–Downarowicz (arXiv:2506.12929, Thm. 8.11 and Prop. 8.13) construct numerical-kernel elements $xy$ and $1/y$ whose product $x$ is normal. So $E_b\in K_b$ says nothing about $1/E_b$.
2. **Diophantine information.** $P_b\in K_b$ only forces, for density-one $n$, runs of length $r_n\to\infty$ at an arbitrary slow rate. These give approximations $|P_b-k/((b-1)b^n)|\ll b^{-n-r_n}$, of quality $q^{-1-o(1)}$, which are weaker than Dirichlet's. No irrationality measure, finite or Liouville, can therefore decide $K_b$ membership. Both $K_b$ (Phase 18, $\sum b^{-k!}$) and the normal numbers (Phase 19) contain Liouville numbers.
3. **The convolution identity.** $E_bP_b=1$ is equivalent to Proposition D2.1. Its constraint is the rate-conditional Proposition D2.2.
4. **Congruences.** These are washed out by Proposition D2.3 and Lemma D1.4.

Finite evidence (§5) shows normal-looking orbits: $D_{4000}(P_b)=0.025,0.022,0.014,0.019,0.022,0.020$ for $b=2,3,5,7,10,11$.

## 3. D3 — theta powers, Eisenstein values and eta powers

### 3.1 The sparse rungs, in every base

**Theorem D3.1.** For every radix $b\ge2$ the following lie in $K_b$ with limiting fixed point $0$:

1. $\Theta_3(1/b)=1+2\sum_{n\ge1}b^{-n^2}$, $E_b$ and $E_b^3=\sum_{k\ge0}(-1)^k(2k+1)b^{-k(k+1)/2}$ (Jacobi), with $1-D_N\ll_b\log N/\sqrt N$;
2. $L_\chi(b)=\sum_{m\ge1}\chi(m)/(b^m-1)$ for every real nonprincipal Dirichlet character $\chi$, and in particular $\Theta_3(1/b)^2=1+4L_{\chi_4}(b)$;
3. $\Theta_Q(1/b)=\sum_{v\in\mathbb Z^2}b^{-Q(v)}$ for every positive definite integral binary quadratic form $Q$.

In cases 2 and 3, $1-D_N\ll_{b,\chi,Q}\log\log N/\sqrt{\log N}$.

*Proof.* Each is $F_b(c)$ with polynomially bounded $c$. Apply the Track B1 bound of §1.4(iv).

1. Squares, generalized pentagonal and triangular numbers have $S(X)\ll\sqrt X$. The masses are $O(\sqrt X)$, $O(\sqrt X)$ and at most $4X$ (Lean `jacobiCube_absMass_le`). Take $\varepsilon=N^{-1/2}$ and $L=\lceil\log_bN\rceil$.
2. $c=1*\chi\ge0$ is multiplicative with local factors $1+\chi(p)+\dots+\chi(p)^e\in\{0,1,e+1\}$. Its mass is $A(X)=\sum_{d\le X}\chi(d)\lfloor X/d\rfloor\le X|\sum_{d\le X}\chi(d)/d|+X=O(X)$. If $c(n)\ne0$, then every prime $p$ with $\chi(p)=-1$ divides $n$ to an even power. For a finite set of such primes, this forces upper density at most $\prod_p(1-1/p+1/p^2)$, which tends to $0$ because $\sum_{\chi(p)=-1}1/p=\infty$. So $S(X)=o(X)$. The quantitative bound $S(X)\ll X/\sqrt{\log X}$ is the Wirsing/Shiu estimate used in Phase 17, §2. Then take $\varepsilon=(\log N)^{-1/2}$ and $L=\lceil\log_b((\log N)^{3/2})\rceil$.
3. If $Q$ has discriminant $\Delta<0$ and $p\nmid2\Delta$ with $(\Delta/p)=-1$, then $Q$ is anisotropic modulo $p$. So $p\mid Q(v)$ forces $p\mid v$, and by iteration $v_p(Q(v))$ is even. The support is therefore sparse as in case 2. The mass is $\#\{v:Q(v)\le X\}=(2\pi/\sqrt{|\Delta|})X+O(\sqrt X)$. ∎

This extends to every radix the qualitative $K_2$ membership that Phase 17 proved for the characters, there with matching binary rates. Here the rate is an upper bound only. Finite values are in §5: $1-D_{4000}(L_{\chi_4}(b))=0.657,0.633,0.474$ for $b=2,3,5$. They decay as slowly as the rate predicts.

### 3.2 The dense rungs and the exact transfers

- **$\Theta^3$.** By Gauss–Legendre, $r_3(n)>0$ unless $n=4^a(8k+7)$. The support has density $5/6$, so (iv) is inapplicable, and $r_3(n)\ll n^{1/2+\epsilon}$ makes the window $O(\log N)$.
- **$\Theta^4$.** Jacobi gives $r_4(n)=8\sum_{d\mid n,\,4\nmid d}d$, so $\Theta_3(1/b)^4=1+8\sum_{4\nmid m}m/(b^m-1)=\tfrac13\big(4E_2(b^{-4})-E_2(b^{-1})\big)$. The support is everything.
- **Eisenstein values and $\Delta$.** $E_{2k}(1/b)$ have coefficients $\sigma_{2k-1}(n)$ and windows $O(k\log N)$. $\Delta(1/b)=b^{-1}E_b^{24}$ has coefficients $\tau(n)$. By Serre (Glasgow Math. J. 27 (1985)), $\eta^r$ for even $r$ is lacunary exactly for $r\in\{2,4,6,8,10,14,26\}$, so $\eta^{24}$ is not lacunary.
- **Lacunary but too wide.** $E_b^4$ and $E_b^6$ have density-zero support (Serre), but their coefficients have size about $n^{(r-2)/4}$. Each nonzero coefficient occupies about $\frac{r-2}{4}\log_bn$ digit positions while the support gaps average about $\sqrt{\log n}$. Both the B1 hypothesis $A=O(X)$ and the width condition $W=o(X)$ fail. The finite measurements look normal: $1-D_{4000}=0.985$ and $0.980$ in binary. This is the precise boundary of the sparse method.

Membership, nonmembership and normality are **open** for every dense rung. What is provable are exact transfers modulo the kernel. Since $\Theta^2=1+4L$ with $L=L_{\chi_4}(b)\in K_b$,

```math
\Theta_3(1/b)^4=1+8L+16L^2\equiv16L^2,\qquad \Theta_3(1/b)^3=\Theta+4\Theta L\equiv4\,\Theta L\pmod{K_b}.
```

Hence $D_N(\Theta^4)-D_N(16L^2)\to0$ in every base. In binary, using $|D_N(2^jy)-D_N(y)|\le j/N$,

```math
|D_N(\Theta_3(1/2)^4)-D_N(L_{\chi_4}^2)|\le 1-D_N(L_{\chi_4})+7/N\ll\frac{\log\log N}{\sqrt{\log N}} .
```

Equivalently, $L_{\chi_4}^2\equiv\frac12\sum_{4\nmid m}m/(2^m-1)$ in $\mathbb R/K_2$. These statements identify discrepancy behaviour and decide none of it. At $N\le4000$ both sides are near $0$, so the observed agreement (difference $0.0001$) is not evidence for the transfer.

**Transcendence.** $\Theta_3(1/b)$ is transcendental (Duverney–Ke. Nishioka–Ku. Nishioka–Shiokawa, Proc. Japan Acad. 72A (1996), from Nesterenko; Bertrand, Ramanujan J. 1 (1997)), hence so are all its powers. The Eisenstein values are covered by §2.4.

## 4. D4 — multiplication and inversion in the discrepancy geometry

### 4.1 A sumset criterion for products

**Theorem D4.1.** Let $x=F_b(a)$ and $y=F_b(c)$ with absolutely convergent integer coefficient series. Then $xy=F_b(a*c)$ with Cauchy convolution $a*c$. If

```math
\#\big((\operatorname{supp}a\cap[0,X])+(\operatorname{supp}c\cap[0,X])\big)=o(X)\quad\text{and}\quad \bar A_a(X)\,\bar A_c(X)=O(X),
```

where $\bar A_a(X)=\sum_{0\le m\le X}|a(m)|$, then $xy\in K_b$. In particular $(S_a(X)+1)(S_c(X)+1)=o(X)$ together with $\bar A_a\bar A_c=O(X)$ suffices.

*Proof.* $\operatorname{supp}(a*c)\subseteq\operatorname{supp}a+\operatorname{supp}c$ and $\sum_{m\le X}|(a*c)(m)|\le\bar A_a(X)\bar A_c(X)$ (compare Lean `EulerPentagonal.cauchyConv_absMass_le`). The index-zero term contributes an integer. Apply Track B1. ∎

**Corollary.** Missing-digit series of index dimensions $\sigma,\tau$ (Phase 19, products-of-remainders) with $\sigma+\tau<1$ have product in $K_b$.

**On the critical line $S_aS_c\asymp X$, both outcomes occur.**

- **Negative:** the Moser–de Bruijn factors $U,V$ ($\sigma=\tau=1/2$) have sumset all of $\mathbb N$ and $UV=b^r/(b^r-1)\notin K_b$ (Phase 19).
- **Positive:** $\Theta_3(1/b)\cdot\Theta_3(1/b)$ also has $\sigma=\tau=1/2$, but the sumset of the squares has counting function $\asymp X/\sqrt{\log X}$ (Landau). Hence $\Theta^2\in K_b$ (Theorem D3.1).

So the product-of-counts criterion is sharp, and the true invariant is the density of the sumset together with the mass.

### 4.2 $K_b$ is not closed under squaring

**Proposition D4.2.** Let $U,V$ be the Moser–de Bruijn factors with $r\ge2$ and $x=U+V$. Then $x\in K_b$, $x^2\equiv2b^r/(b^r-1)\pmod{K_b}$, and $x^2\notin K_b$. Moreover $D_N(x^2)$ converges to the discrepancy of the finite cycle of $2/(b^r-1)$.

*Proof.* Elements of $A$ have base-4 digits in $\{0,1\}$. Adding two of them produces no carries, so $A+A$ is the set of integers with base-4 digits in $\{0,1,2\}$, of counting function $\asymp X^{\log3/\log4}=o(X)$. The masses are at most $\#(A\cap[0,X])^2=O(X)$. Theorem D4.1 gives $U^2\in K_b$, and likewise $V^2\in K_b$ since $2A+2A=2(A+A)$. Then $x^2=U^2+V^2+2UV$. The rational $2UV=2b^r/(b^r-1)$ has reduced denominator $(b^r-1)/\gcd(2,b^r-1)>b-1$, coprime to $b$, so it is not in $K_b$ (Phase 19 rational test). Translations by $K_b$ preserve all limits. ∎

For $b=r=2$ the limit is $2/3$. The finite values $D_N(x^2)=0.27,0.32,0.35$ at $N=1000,2000,4000$ approach it slowly, because $1-D_{4000}(U^2)\approx0.36$ is still large. The algebraic relation $y=x^2$ thus imposes no constraint of the form "$x\in K_b\Rightarrow y\in K_b$".

### 4.3 Reciprocals of radix-primary rationals

**Theorem D4.3.** Let $x=A/b^j$ with $A\in\mathbb Z\setminus\{0\}$, and write $|A|=uv$ where every prime of $u$ divides $b$ and $\gcd(v,b)=1$. Then $x\in K_b$ always, and

```math
1/x\in K_b\iff v\mid b-1 .
```

*Proof.* By Phase 19 a rational lies in $K_b$ iff its reduced denominator divides $b^i(b-1)$ for some $i$, that is, iff the $b$-coprime part of the reduced denominator divides $b-1$. Since $b$ and $b-1$ are coprime, every divisor of $b^i(b-1)$ is a divisor of $b^i$ times a divisor of $b-1$. The $b$-coprime part of the reduced denominator of $b^j/A$ is exactly $v$. ∎

**Corollary (finite sparse $z$).** Let $z=\sum_{m\in M}b^{-m}$ with $M$ finite, $m_K=\max M$, and $Q=b^{m_K}(1-z)\equiv-1\pmod b$. Then $1/(1-z)\in K_b$ iff $Q\mid b-1$. For $b\ge3$ this holds iff $M=\{1\}$, because $Q\ge((b-2)b^{m_K}+1)/(b-1)>b-1$ when $m_K\ge2$, by $b(b-1)(b-2)>0$. For $b=2$ it holds iff $M=\{1,\dots,m_K\}$, since $Q=1+\sum_{m\notin M,\,m<m_K}2^{m_K-m}$. Example: $1-b^{-2}\in K_b$, but $b^2/(b^2-1)\notin K_b$, with limiting discrepancy $2/3$, $3/4$, $10/11$ for $b=2,3,10$. The script checks the criterion exhaustively for $M\subseteq\{1,\dots,7\}$, $|M|\le4$, $b\in\{2,3,5\}$.

**The geometric-series heuristic is not a proof.** For infinite $z=b^{-m_1}+\cdots$ one has $1/(1-z)=\sum_rz^r$. Its difference from $1/(1-b^{-m_1})$ is $\sum_r(z^r-b^{-rm_1})$, which is neither sparse nor in $K_b$ in general, so "$1/(1-z)$ contains the periodic part $1/(1-b^{-m_1})$" yields no conclusion about the orbit. The correct infinite statement follows.

### 4.4 Sparse $z$ whose reciprocal is far from the kernel

**Theorem D4.4.** There are integers $2=m_1<m_2<\cdots$, which may be required to grow faster than any prescribed function, such that $z=\sum_k2^{-m_k}$ satisfies $1-z\in K_2$ but

```math
\liminf_{N\to\infty}D_N\Big(\frac1{1-z}\Big)=0 ,
```

in particular $1/(1-z)\notin K_2$.

*Construction.* Put $z_k=\sum_{i\le k}2^{-m_i}$, $Q_k=2^{m_k}(1-z_k)$ (odd and greater than 1) and $r_k=1/(1-z_k)=2^{m_k}/Q_k<2$. Given $m_1,\dots,m_{k-1}$, write $Q=Q_{k-1}$ and $J=J_k=kQ$. Choose $m_k$ divisible by $\operatorname{ord}_{Q^{J}}(2)$, with $m_k\ge k\,J\,Q^{J+1}$ and $m_k\ge(J_{k-1}+2)m_{k-1}$, and as large as desired.

*Proof.* The binary digits of $1-z$ are all ones except zeros at the $m_k$, so $\|2^n(1-z)\|$ is small off neighbourhoods of the $m_k$ and $1-z\in K_2$. Fix $k$ and write $m=m_k$, $r=r_{k-1}$, $y=1/(1-z)$, $y'=1/(1-z_{k-1}-2^{-m})$, $N_k=Jm$.

*Approximation.* $|y-y'|\le4\cdot2^{1-m_{k+1}}$. If $|u-u'|\le b^{-N-L}$ then $|D_N(u)-D_N(u')|\le2b^{-L}$, by the finite comparison with $\varepsilon=b^{-L}$. Since $m_{k+1}\gg N_k$, we may replace $y$ by $y'$.

*Bands.* $y'=\sum_{i\ge0}r^{i+1}2^{-im}$. Fix $L=L_k=3J$. For $j<J$ and $n\in I_j=[jm,(j+1)m-L)$,

```math
2^ny'\equiv\sum_{i\le j}2^{n-im}r^{i+1}+e_n,\qquad 0\le e_n\le 2^{j+3-L}.
```

Each term is $2^{n-im+(i+1)m_{k-1}}/Q^{i+1}$ with a nonnegative exponent. Because $2^m\equiv1\pmod{Q^{J}}$ and $i+1\le J$, it is congruent mod 1 to $2^{n+(i+1)m_{k-1}}/Q^{i+1}$. Hence $x_n=2^nS_j+e_n$ (mod 1), where

```math
S_j=\frac{u_j}{Q^{j+1}},\qquad u_j=\sum_{i\le j}2^{(i+1)m_{k-1}}Q^{j-i}\equiv2^{(j+1)m_{k-1}}\pmod Q .
```

So $u_j$ is a unit modulo $Q^{j+1}$ and $x_n$ follows the purely periodic orbit of $S_j$, of period $p_j=\operatorname{ord}_{Q^{j+1}}(2)\le Q^{j+1}$.

*Equidistribution of the cycles.* Let $h=2^{\operatorname{ord}_Q(2)}$, $s_p=v_p(h-1)$ and $M=\prod_{p\mid Q}p^{s_p}$. Then $M\mid h-1<2^Q$, so $\log_QM<Q$. For odd $p$ the group $(1+p^{s}\mathbb Z)/(1+p^{e}\mathbb Z)$ is cyclic and generated by any element of exact valuation $s$. By the Chinese remainder theorem (the factors have coprime orders), $\langle h\rangle\supseteq\{v\equiv1\pmod M\}$ in $(\mathbb Z/Q^e)^\times$ for every $e$ with $M\mid Q^e$. So each coset $u_j\langle2\rangle$ is a union of full residue classes modulo $M$. Each class, divided by $Q^{j+1}$, is an arithmetic progression of step $M/Q^{j+1}$ on the circle. The cycle measure $\nu_j$ therefore satisfies $D(\nu_j)\le\min(1,M/Q^{j+1})$.

*Assembly.* On $I_j$ the empirical law is within $2p_j/(m-L)$ of $\nu_j$ (one partial period) and within $2\cdot2^{j+3-L}$ by the finite comparison. Discrepancy is subadditive under mixtures. The shifts outside $\bigcup I_j$ have proportion at most $L/m$. Hence

```math
D_{N_k}(y)\le\frac1J\sum_{j<J}\min\Big(1,\frac{M}{Q^{j+1}}\Big)+\frac{2Q^{J}}{m-L}+2^{4-2J}+\frac Lm+o(1)\le\frac{\log_QM+2}{J}+o(1)\le\frac{2}{k}+o(1). \quad ∎
```

The same proof works in any base $b$ with $m_1\ge2$, using $Q_k\equiv-1\pmod b$. Finite check, stage $k=2$ ($m_2=1080$, divisible by $\operatorname{ord}_{81}(2)=54$): $D_N(y)=0.661,0.330,0.220,0.165$ at $N=1080j$, $j=1,\dots,4$. The predicted band cycle discrepancies are $2/3$ and those of the units modulo $3^{j+1}$ ($0.222,0.074,0.025$).

So even arbitrarily lacunary $z$ cannot keep $1/(1-z)$ in $K_b$, and §2.5(1) has a rigorous basis: reciprocals carry no kernel information in either direction.

### 4.5 Algebraic relations: summary for (c)

- **Additive relations** $x+y=r$: $|D_N(y)-D_N(x)|\le1-D_N(r)$, using $D_N(-x)=D_N(x)$. The Phase 19 addition spectrum is the complete answer for $\liminf/\limsup$ triples.
- **Integer dilations** $y=mx$: the Phase 19 bounds and boundary spectrum $[1/m_0,1]$ apply.
- **Multiplicative and higher-degree relations** admit no Lipschitz control. Multiplication by a non-integer is not Lipschitz for $d_N$: $d_N(1,0)=0$, while $d_N(1/3,0)=1-D_N(1/3)\to1/3$ in base 2. Moreover:
  - $x,y\in K_b$ but $xy\notin K_b$ (Moser–de Bruijn);
  - $x\in K_b$ but $x^2\notin K_b$ (Proposition D4.2);
  - $x\in K_2$ with $\liminf D_N(1/x)=0$ (Theorem D4.4);
  - $x,1/x$ both in $K_b$ (Theorem D4.3, $x=d/b^j$ with $d\mid b-1$);
  - two binary numerical-kernel elements with a normal product (Bergelson–Downarowicz).

  The only general constraints valid for $xy=r$ or $y=x^2$ are those inherited from the pseudometric through additive decompositions that one can actually exhibit, as in Theorem D4.1 and Proposition D4.2.

## 5. Finite verification

`python -B scripts/phase20_dense_classical.py` exits 0 in about two seconds. Exact checks:

- $p(n)\le e^{\pi\sqrt{2n/3}}$ for $n\le7000$ (least log-margin $2.565$), and the certified inequality $T(N-1,L(N))\le N^{-2}$ for $b\in\{2,3,5,7,11\}$, $N\in\{1000,4000\}$;
- agreement of 4000+ certified digits of $P_b$ computed from $p(n)$ and from $1/E_b$ (pentagonal theorem), $b\in\{2,3,5,7,10,11\}$;
- Ramanujan congruences modulo $5,7,11,25,49,121$, the first-digit carry identity, and the circle recurrence of Proposition D2.1;
- the Jacobi four-square and cube identities, $\Theta^4=(4E_2(q^4)-E_2(q))/3$, the Legendre criterion, and $\Delta=(E_4^3-E_6^2)/1728=q\prod(1-q^n)^{24}$;
- the reciprocal criterion, the band predictions of Theorem D4.4, and $UV=4/3$.

Orbit points use 40-bit truncations, so each discrepancy is within $2^{-40}$ of the exact finite value. Selected values ($N=4000$, binary unless noted):

| Number | $D_{4000}$ | | Number | $1-D_{4000}$ |
| --- | --- | --- | --- | --- |
| $P_2$ | 0.0253 | | $\Theta_3(1/2)$ | 0.0927 |
| $P_{11}$ (base 11) | 0.0202 | | $\Theta_3(1/2)^2$ | 0.656 |
| $\Theta^3$ | 0.0191 | | $E_2$ (Euler value) | 0.156 |
| $\Theta^4$ | 0.0163 | | $E_2^3$ | 0.278 |
| $E_2(1/2)$, $E_4(1/2)$, $E_6(1/2)$ | 0.017, 0.022, 0.022 | | $E_2^4$, $E_2^6$ | 0.985, 0.980 |

These are finite measurements below any asymptotic threshold and decide none of the open questions.

## 6. Open questions

1. Prove $D^+(P_b)<1$ for some base, or even $P_b\notin K_b$. By §2.5 this needs genuinely new input on the joint distribution of $(p(n+j)\bmod b^j)_{j\lesssim\sqrt n}$, or on $\{\sum_jp(n+j)b^{-j}\}$.
2. Is $E_b^4\in K_b$? It is the simplest series with density-zero support where both the mass and the width hypotheses fail.
3. Is $1/(1-z)\notin K_b$ for **every** infinite sparse $z$ with $m_1\ge2$? Theorem D4.4 gives existence only.
4. Give a lower bound of matching order for $1-D_N(L_\chi(b))$ when $b\ne2$; Phase 17 has it only in binary.
