# The partition constant, derivative transfer and the width–density wall

Phase 21, Track D, sub-tracks D3 and D4. Fix an integer radix $b\ge2$. Notation follows [Phase 20, dense-and-partitions](../phase20/dense-and-partitions.md): $x_n=\{b^nx\}$, $D_N(x)=D_N(x;b)$ is the extreme discrepancy of $x_0,\dots,x_{N-1}$, $K_b=\{z:D_N(z)\to1\}$, and for an integer sequence $a$

```math
F_b(a)=\sum_{m\ge0}a(m)b^{-m},\qquad S(X)=\#\{1\le m\le X:\ a(m)\ne0\},\qquad A(X)=\sum_{1\le m\le X}|a(m)|,\qquad \rho_N=\frac{1+S(N-1)}{N}.
```

$E_b=\prod_{k\ge1}(1-b^{-k})$ is the Euler value and $P_b=1/E_b=\sum_{n\ge0}p(n)b^{-n}$ the partition constant. The generalized pentagonal numbers in increasing order are $m_1<m_2<\cdots$ $(1,2,5,7,12,15,\dots)$, with Euler signs $\varepsilon(m_i)\in\{\pm1\}$ (pattern $++--$), so that $E_b=1-z$, $z=\sum_i\varepsilon(m_i)b^{-m_i}$. We write $K=\pi\sqrt{2/3}=2.5651\ldots$ and $D=q\,\frac{d}{dq}$, so $D^jF$ has coefficients $m^ja(m)$.

**Scope and evidence.** Everything marked "paper proof" is proved here from the cited published inputs. Lean citations refer to declarations already built and kernel-replayed on this branch: [`GeneralMassTransfer.lean`](../../NormalityChecker/GeneralMassTransfer.lean) (`poly_mass_sparse_tendsto_one`, `finite_poly_mass_transfer`), [`EulerPentagonal.lean`](../../NormalityChecker/EulerPentagonal.lean), and [`DerivativeTransfer.lean`](../../NormalityChecker/DerivativeTransfer.lean) (`deriv_eulerPentagonal_discrepancy_tendsto_one`, `deriv_eulerCube_discrepancy_tendsto_one`, `deriv_thetaThree_discrepancy_tendsto_one`, `eulerSqDeriv_discrepancy_tendsto_one`, `coprimePart_le_natAbs_radixUnit_mul`, `carryWindow_succ_modEq`). Finite statements are checked by [`scripts/phase21_partitions_modular.py`](../../scripts/phase21_partitions_modular.py) (standard library, about 5 s, 125,884 assertions, exit 0). Every discrepancy, word frequency and width density quoted from it is a **finite measurement**. None of them is evidence for or against normality.

**Summary of conclusions.**

| Item | Result | Status |
| --- | --- | --- |
| §1.1 | Propositions D3.1–D3.2: $p(n)<e^{K\sqrt n}$ and $\eta$-refinement $p(n)\le(1+2e^{-4\pi\sqrt{6n}})(24n)^{-1/4}e^{K\sqrt n}$ for all $n\ge1$ | Paper proof |
| §1.2 | Theorem D3.3 & Corollary D3.4: all-$N$ certified carry windows for $P_b$ in closed form; sharp to $\log_b(N+L_{\rm el})+O(1)$ digits ($\tfrac34\log_b(N+L_{\rm el})+O(1)$ with the refinement) | Paper proof; table |
| §1.3 | Proposition D3.5: exact carry recurrences (shift register, pentagonal window identity, solved tail formula $T_n=\sum_{m\le n}p(n-m)\beta_m$) | Shift register kernel-verified in `DerivativeTransfer.lean`; rest paper proof |
| §1.4 | Theorem D3.6: the pentagonal circle recurrence with admissible kicks has both an equidistributed solution and the zero solution, so it cannot decide normality or $K_b$ membership | Paper proof |
| §1.5 | Theorem D3.7: $P_b$ vs $1/E_b^{(K)}$ — exact error, agreement $\le m_{K+1}$ digits, excess precision $\Theta(\sqrt{m_K})$ over denominator scale, period $\ge m_K-O(1)$; why this blocks the reciprocal mechanism | Paper proof; orders checked for $6\le K\le34$ |
| §1.7 | Normality, simple normality, $D^+(P_b)<1$, $P_b\notin K_b$ | **Open** for every $b\ge2$ |
| §2.1 | Theorem D4.1: polynomial-mass rate $1-D_N\le\rho_N\bigl(2\log_b\frac1{\rho_N}+(\kappa-1)\log_bN+O(1)\bigr)$ under $A(X)\le CX^\kappa$, all $N$ | Paper proof |
| §2.2 | Theorem D4.2 & Corollary D4.3: $D^jE_b$, $D^jE_b^3$, $D^j\Theta_3(1/b)$, $E_b^2\,DE_b\in K_b$ for all $j\ge0,b\ge2$; every sparse $\mathbb Z[1/b]$-polynomial in them lies in $K_b$ | Series theorems kernel-verified in `DerivativeTransfer.lean` (product IDs external); general polynomials paper proof |
| §2.3 | Lemma W.1, Theorem D4.4, Lemma W.2, Corollary D4.5: width–density wall $W_U(N)\asymp N\sqrt{\log N}$ for weight $k\ge2$ CM newforms ($\eta^4,\eta^6,\eta^8$); $b$-adic valuations cannot cancel it | Lemma W.1 kernel-verified in `DerivativeTransfer.lean`; wall paper proof from Hecke, Chebotarev & Serre |
| §2.3 | Proposition D4.6: $W(N)=o(N)$ is sufficient for $K_b$ but **not necessary** | Paper proof |
| §2.4 | $\eta^{10},\eta^{14}$: same wall, conditional on a twisted Hecke relation verified numerically. $\eta^{14}$ has CM by $\mathbb Q(\sqrt{-3})$. $\eta^{26}$ mixes $\mathbb Q(i)$ and $\mathbb Q(\sqrt{-3})$ | Numerically verified structure |
| §2.5 | Proposition D4.7: derivatives cross the wall between unary and binary objects ($D^j(\Theta_3^2)$, $D^j(E_b^2)$, $j\ge1$, $E_b\,DE_b$ lie beyond every transfer hypothesis) | Paper proof |
| §2.6 | $\Theta^3,\Theta^4,E_2(1/b),E_4(1/b),E_6(1/b),\Delta(1/b)$, $E_b^r$ for $r\ge4$: membership in $K_b$ and normality | **Open** |

## 1. D3 — the partition constant

### 1.1 Two all-$n$ bounds for $p(n)$

**Proposition D3.1 (elementary).** For every $n\ge1$, $p(n)<e^{K\sqrt n}$.

This is [Apostol, *Introduction to Analytic Number Theory*, Thm. 14.5]. *Proof.* For $0<q<1$, $p(n)q^n<P(q)=\prod_k(1-q^k)^{-1}$ (the other terms are positive), and

```math
\log P(q)=\sum_{j\ge1}\frac1j\,\frac{q^j}{1-q^j}\le\frac{q}{1-q}\sum_{j\ge1}\frac1{j^2}=\frac{\pi^2}{6}\,\frac q{1-q},
```

since $1+q+\dots+q^{j-1}\ge jq^{j-1}$. With $q=e^{-t}$ we have $q/(1-q)\le1/t$, so $p(n)<\exp(nt+\pi^2/(6t))$. Take $t=\pi/\sqrt{6n}$; then $nt+\pi^2/(6t)=K\sqrt n$. ∎

**Proposition D3.2 (η-refinement).** For every $n\ge1$,

```math
p(n)\le\bigl(1+2e^{-4\pi\sqrt{6n}}\bigr)\,(24n)^{-1/4}\,e^{K\sqrt n}.
```

*Proof.* Dedekind's transformation $\eta(-1/\tau)=\sqrt{-i\tau}\,\eta(\tau)$ [Apostol, *Modular Functions and Dirichlet Series*, Thm. 3.1] at $\tau=it/2\pi$ gives, with $q'=e^{-4\pi^2/t}$,

```math
P(e^{-t})=\Bigl(\frac{t}{2\pi}\Bigr)^{1/2}\exp\Bigl(\frac{\pi^2}{6t}-\frac t{24}\Bigr)P(q').
```

Again $p(n)\le e^{nt}P(e^{-t})$. At $t=\pi/\sqrt{6n}$ we get $(t/2\pi)^{1/2}=(24n)^{-1/4}$, $e^{-t/24}<1$, and $q'=e^{-4\pi\sqrt{6n}}\le e^{-30.7}$, so $P(q')\le\exp(\tfrac{\pi^2}{6}\tfrac{q'}{1-q'})\le1+2q'$. ∎

By Hardy–Ramanujan, $p(n)\sim e^{K\sqrt n}/(4\sqrt3\,n)$, so D3.1 loses a factor $\asymp n$ and D3.2 a factor $\asymp n^{3/4}$. The script checks D3.1 and D3.2 (with prefactor $1.0000001\ge 1+2e^{-4\pi\sqrt{6n}}$; all 12 table rows are identical under either prefactor) for $1\le n\le4700$. The least log-margins are $2.565$ and $1.771$.

### 1.2 Certified all-$N$ windows

Put $T(n,L)=\sum_{j>L}p(n+j)b^{-j}$. By [Phase 20 Lemma D1.1](../phase20/dense-and-partitions.md#11-exact-transfer), $x_n\equiv R_{n,L}/b^L+T(n,L)\pmod 1$ with $T(n,L)>0$, where (with $R_{n,0}=0$ when $L=0$)

```math
R_{n,L}=\Bigl(\sum_{j=1}^{L}p(n+j)\,b^{L-j}\Bigr)\bmod b^L .
```

**Theorem D3.3 (all-$N$ window bound).** Let $N\ge1$ and $L\ge0$, and suppose that $\lambda=\log b-K/(2\sqrt{N+L})>0$ (true whenever $N+L\ge4$). Then

```math
\max_{0\le n<N}T(n,L)=T(N-1,L)\le B_{\rm el}(N,L):=\frac{e^{K\sqrt{N+L}}\,b^{-(L+1)}}{1-e^{-\lambda}},
```

and also $T(N-1,L)\le B_{\rm mod}(N,L):=(1+2e^{-4\pi\sqrt{6(N+L)}})\,(24(N+L))^{-1/4}\,B_{\rm el}(N,L)$.

*Proof.* $p$ is nondecreasing, so $p(n+j)\le p(N-1+j)$ termwise for $n<N$. For $j\ge L+1$, concavity of the square root at $N+L$ gives $\sqrt{N-1+j}\le\sqrt{N+L}+(j-L-1)/(2\sqrt{N+L})$. Insert D3.1 and sum the geometric series of ratio $e^{-\lambda}$. For $B_{\rm mod}$ use D3.2 and observe that $(24m)^{-1/4}$ decreases in $m$. ∎

**Corollary D3.4 (explicit windows and their sharpness).** Let $0<\tau<1$ with $\log_b(1/\tau)=O(N)$, and let $L_{\rm el}(N,\tau)$ be the least nonnegative integer $L$ with $B_{\rm el}(N,L)<\tau$. For large $N$ the equation $B_{\rm el}(N,L^*)=\tau$ has a unique real root $L^*(N,\tau)\ge0$ satisfying

```math
L^*(N,\tau)=\frac{K\sqrt N}{\log b}+\frac{K^2}{2\log^2b}+\log_b\frac1\tau-\log_b(b-1)+O_b\Bigl(\frac{1+\log^2(1/\tau)/N+\log(1/\tau)}{\sqrt N}\Bigr),
```

and $L_{\rm el}(N,\tau)=\lfloor L^*(N,\tau)\rfloor+1=L^*(N,\tau)+\theta$ with $\theta\in(0,1]$ (in particular, when $\log(1/\tau)=O(\sqrt N)$, $L^*(N,\tau)$ has error $O_b((1+\log(1/\tau))/\sqrt N)$ and $L_{\rm el}(N,\tau)$ differs from $L^*(N,\tau)$ by the integer rounding term $\theta\in(0,1]$).

Conversely, for every $0<\tau<1$ (without restricting $\tau$), every $L$ with $T(N-1,L)<\tau$ satisfies $T(N-1,L)\ge p(N+L)b^{-L-1}$. Hence, by Hardy–Ramanujan, $L\ge L_{\rm el}(N,\tau)-\log_b(4\sqrt3\,(N+L_{\rm el}(N,\tau)))-O_b(1)$. In particular, whenever $\log_b(1/\tau)=O(N)$ (such as $\tau=N^{-A}$), the elementary window is sharp to within $\log_bN+O(1)$ digits, and the η-refined window to within $\tfrac34\log_bN+O(1)$ (and unconditionally to within $\log_b(N+\log_b(1/\tau))+O(1)$, resp. $\tfrac34\log_b(N+\log_b(1/\tau))+O(1)$).

*Proof.* For $N+L\ge4$, $\partial_L\log B_{\rm el}(N,L)=-\lambda-\frac{e^{-\lambda}}{1-e^{-\lambda}}\frac{K}{4(N+L)^{3/2}}<0$, so $B_{\rm el}(N,L)$ is strictly decreasing in $L$ and $L_{\rm el}(N,\tau)=\lfloor L^*(N,\tau)\rfloor+1$. Take logarithms in $B_{\rm el}(N,L^*)=\tau$, expand $\sqrt{N+L^*}=\sqrt N+L^*/(2\sqrt N)+O((L^*)^2N^{-3/2})$ (using $L^*=O(N)$ from $\log_b(1/\tau)=O(N)$) and $1-e^{-\lambda}=(1-b^{-1})(1+O(N^{-1/2}))$, and solve for $L^*$. For the converse, Hardy–Ramanujan gives $p(N+L)\sim e^{K\sqrt{N+L}}/(4\sqrt3\,(N+L))$. ∎

Compared with Phase 20 (Lemma D1.3, $L=273$ for $b=2$, $N=4000$), the closed form saves 7 digits, the η-refinement 11. The table gives, for $\tau=N^{-2}$: $L_{\rm nec}$, the least $L$ with $p(N+L)b^{-L-1}<\tau$ (a necessary condition); $L_{\rm exact}$, certified from the exact values of $p$, with a far tail bounded by $B_{\rm mod}$; $L_{\rm mod}$ and $L_{\rm el}$, the closed forms; and $L_{\rm asym}$, the main terms of D3.4. The script asserts $L_{\rm nec}\le L_{\rm exact}\le L_{\rm mod}\le L_{\rm el}$ in every row, and that $|L_{\rm el}-L_{\rm asym}|\le3$ for $N\ge1000$.

| $b$ | $N$ | $L_{\rm nec}$ | $L_{\rm exact}$ | $L_{\rm mod}$ | $L_{\rm el}$ | $L_{\rm asym}$ |
|---|---|---|---|---|---|---|
| 2 | 100 | 48 | 49 | 57 | 61 | 57.1 |
| 2 | 1000 | 131 | 132 | 142 | 146 | 143.8 |
| 2 | 4000 | 250 | 251 | 262 | 266 | 264.8 |
| 3 | 4000 | 156 | 156 | 163 | 166 | 164.9 |
| 5 | 4000 | 106 | 106 | 110 | 112 | 111.5 |
| 10 | 4000 | 73 | 73 | 77 | 78 | 77.3 |

The exact window is one digit above the necessary one, because $p$ grows so smoothly that the first omitted term dominates the tail. The gap $L_{\rm el}-L_{\rm nec}=16$ for $b=2$, $N=4000$ matches $\log_2(4\sqrt3\cdot4000)\approx14.8$.

### 1.3 Exact carry recurrences

**Proposition D3.5.** For all $n\ge0$ and $L\ge1$:

1. *(shift register)* $R_{n+1,L}\equiv b\,R_{n,L}+p(n+L+1)\pmod{b^L}$;
2. *(pentagonal window identity)* with $\widehat R_{n,L}=\sum_{j=1}^Lp(n+j)b^{L-j}$ (not reduced),

```math
\widehat R_{n,L}=\sum_{0<m_i\le n}\varepsilon(m_i)\,\widehat R_{n-m_i,L}\;+\sum_{n<m_i\le n+L}\varepsilon(m_i)\sum_{j=m_i-n}^{L}p(n+j-m_i)\,b^{L-j};
```

3. *(real tails)* with $T_n=\sum_{j\ge1}p(n+j)b^{-j}$, so that $x_n=\{T_n\}$,

```math
T_n=\sum_{0<m_i\le n}\varepsilon(m_i)\,T_{n-m_i}+\beta_n,\qquad \beta_n=P_b\sum_{m_i>n}\varepsilon(m_i)\,b^{n-m_i},\qquad\text{equivalently}\qquad T_n=\sum_{m=0}^{n}p(n-m)\,\beta_m .
```

*Proof.* (1) is the definition of $R_{n,L}$ shifted by one place. For (2) and (3), substitute Euler's recurrence $p(r)=\sum_i\varepsilon(m_i)p(r-m_i)$ ($r\ge1$, $p(<0)=0$) into each $p(n+j)$. Terms with $m_i\le n$ reassemble into $\widehat R_{n-m_i,L}$, respectively $T_{n-m_i}$. Terms with $m_i>n$ start at $j=m_i-n$; in (3) they sum to $b^{n-m_i}P_b$. The solved form follows from $E(t)\sum_nT_nt^n=\sum_n\beta_nt^n$ with $E(t)=\prod(1-t^k)$ and $1/E(t)=\sum p(n)t^n$. ∎

The script checks (1) for $n<399$ and (2) for $1\le n<400$ exactly at $L=30$, $b\in\{2,3,10\}$ (while (2) at $n=0$ is Euler's recurrence directly), and checks (3) for $n\le40$ in binary at working precision $2^{-4044}$ (agreement within $2^{-4004}$ at $n=40$). Note $\beta_0=zP_b=P_b-1=T_0$. Phase 20 Proposition D2.1 is (3) read modulo 1, with $\rho_n=\beta_n$.

### 1.4 What the pentagonal recurrence constrains, and what it cannot

Let $B_n=\frac{b}{b-1}P_b\,b^{-(g^+(n)-n)}$, where $g^+(n)$ is the least pentagonal number exceeding $n$; by Phase 20, $|\beta_n|\le B_n$. Call a sequence $(\xi_n)_{n\ge0}$ in $\mathbb R/\mathbb Z$ *admissible* if

```math
\xi_n\equiv\sum_{0<m_i\le n}\varepsilon(m_i)\,\xi_{n-m_i}+\rho'_n\pmod1\quad\text{for some reals }|\rho'_n|\le B_n .
```

**Theorem D3.6 (the recurrence is statistically empty).**

1. Every admissible sequence has the form $\xi_n=\{\sum_{m\le n}p(n-m)\rho'_m\}$, and every choice of kicks $|\rho'_m|\le B_m$ gives one. The orbit of $P_b$ is the admissible sequence with $\rho'=\beta$.
2. $\xi\equiv0$ is admissible ($\rho'=0$). Its discrepancy is $D_N=1$, the $K_b$ scenario with fixed point $0$.
3. For Lebesgue-almost every $\theta\in(0,B_0)$, with $B_0=P_b/(b-1)$, the sequence $\xi_n=\{\theta p(n)\}$ is admissible ($\rho'_0=\theta$, $\rho'_n=0$ for $n\ge1$) and equidistributed modulo 1.

Consequently no argument that uses only the pentagonal recurrence, together with size bounds on its kicks, can prove or refute normality, simple normality, $D^+(P_b)<1$ or $P_b\in K_b$. Admissibility drops both the shift coupling $\xi_{n+1}=\{b\xi_n\}$ (satisfied by $x_n$ and $\xi\equiv0$, but not by $\{\theta p(n)\}$) and the exact arithmetic of $\beta_m=P_b\sum_{m_i>m}\varepsilon(m_i)b^{m-m_i}$, which involves the digits of $P_b$ itself.

*Proof.* (1) is the solved form of Proposition D3.5(3) applied to arbitrary kicks; the identity holds over $\mathbb R$ and hence modulo 1. (2) is immediate. For (3), $\theta p(n)=\sum_i\varepsilon(m_i)\theta p(n-m_i)$ for $n\ge1$, and $p(1)<p(2)<\cdots$ are distinct integers. Weyl's theorem (Math. Ann. 77 (1916)) states that $\{\theta u_n\}$ is equidistributed for almost every $\theta$ when the $u_n$ are distinct integers. ∎

The same statement holds modulo $b^L$. Proposition D3.5(2) expresses $\widehat R_{n,L}$ through earlier windows and boundary data. By [Phase 20 Lemma D1.4](../phase20/dense-and-partitions.md#13-triangular-reduction-and-coordinate-freedom), however, any digit statistic needs the joint law of the triangular residues $(p(n+j)\bmod b^j)_{j\le L(N)}$ with $L(N)\asymp\sqrt N$, and nothing is known about it. Even the one-coordinate law $p(n)\bmod2$ (Parkin–Shanks) is open. The script illustrates Theorem D3.6(3): with $\theta=(\sqrt5-1)/2^{11}$ it verifies the homogeneous recurrence exactly and measures $D_{4000}(\{\theta p(n)\})=0.0217$, against $D_N=1$ for the zero solution.

### 1.5 $P_bE_b=1$, the block structure of $E_b$, and rational approximants

The signs $\varepsilon(m_i)$ come in pairs $++--$. As a result, the base-$b$ expansion of $E_b=1-z$ consists of constant blocks of $0$s and $(b-1)$s, whose ends lie at pentagonal numbers and whose lengths are $\Theta(\sqrt N)$ near position $N$. Truncate at the $K$-th pentagonal number:

```math
E_b^{(K)}=1-\sum_{i\le K}\varepsilon(m_i)b^{-m_i},\qquad Q_K=b^{m_K}E_b^{(K)}\in\mathbb Z,\qquad r_K=\frac1{E_b^{(K)}}=\frac{b^{m_K}}{Q_K}.
```

**Theorem D3.7.** For every $K\ge3$:

1. $Q_K\equiv-\varepsilon(m_K)\pmod b$, so $\gcd(Q_K,b)=1$, and $\log_bQ_K=m_K+\log_bE_b+o(1)$.
2. $P_b-r_K=\varepsilon(m_{K+1})\,P_b\,r_K\,b^{-m_{K+1}}(1+\vartheta_K)$ with $|\vartheta_K|\le b^{-(m_{K+2}-m_{K+1})}\frac b{b-1}\le\frac1{b(b-1)}$.
3. If $r_K$ and $P_b$ agree in their first $A$ fractional digits, then $A\le m_{K+1}$. For all $n$, the circle distance satisfies $\|b^nP_b-b^nr_K\|\le2P_b^2\,b^{\,n-m_{K+1}}$.
4. The excess precision over the denominator scale is $m_{K+1}-m_K\in\{k,2k+1\}$ with $k\approx\sqrt{2m_K/3}$. In Diophantine form, $|P_b-b^{m_K}/Q_K|=Q_K^{-1-\theta_K}$ with $\theta_K\asymp m_K^{-1/2}\to0$.
5. The orbit of $r_K$ is purely periodic, with period $\operatorname{ord}_{Q_K}(b)\ge\log_b(Q_K+1)\ge m_K-O_b(1)$.

*Proof.* (1) Every term of $Q_K=b^{m_K}-\sum_{i\le K}\varepsilon(m_i)b^{m_K-m_i}$ except $i=K$ is divisible by $b$. (2) $P_b-r_K=(E_b^{(K)}-E_b)/(E_bE_b^{(K)})$ and $E_b^{(K)}-E_b=\sum_{i>K}\varepsilon(m_i)b^{-m_i}$; for $K\ge3$ consecutive gaps are at least 2. (3) $P_b,r_K\ge1$ and (2) give $|P_b-r_K|\ge\frac12b^{-m_{K+1}}$. Moreover, for all $K\ge3$ and $b\ge2$, $E_b^{(K)}\ge E_2-2^{-6}>0.272$, so $r_K/P_b<1.063$, $r_K(1+|\vartheta_K|)<1.6\,P_b\le2P_b$, and $|P_b-r_K|<\min(\{P_b\},1-\{P_b\})$, which forces $\lfloor r_K\rfloor=\lfloor P_b\rfloor$; hence agreement in the first $A$ fractional digits implies $|P_b-r_K|<b^{-A}$ and therefore $A\le m_{K+1}$. Multiplying (2) by $b^n$ and using $r_K(1+|\vartheta_K|)\le2P_b$ gives the orbit estimate. (4) follows from (1) and (2). (5) $b^{\rm ord}\equiv1\pmod{Q_K}$ forces $b^{\rm ord}>Q_K$. ∎

The script checks (1) and (3) for $3\le K\le34$ in base 2 and $3\le K\le28$ in bases 3, 5 and 10. Typical rows (base 2): $K=20$ has $m_K=155$, $m_{K+1}=176$ and 172 agreeing digits; $K=30$ has $345$, $376$ and $370$. The shortfall $m_{K+1}-A_K$ is about $\log_b(P_b^2)$ plus a carry run.

**Why this is an obstruction (contrast with the reciprocal mechanism).** Phase 20 [Theorem D4.4](../phase20/dense-and-partitions.md#44-sparse-z-whose-reciprocal-is-far-from-the-kernel) controls $1/(1-z)$ for sparse $z$. There the orbit on a band of length $\approx m_k$ follows a rational $S_j=u_j/Q^{j+1}$ whose denominator comes from an *earlier* stage ($Q=Q_{k-1}$ is fixed). Its period is at most $Q^J$, and the gap is chosen with $m_k\ge kJQ^{J+1}$. Two facts make that mechanism work:

- **(R1)** band length ÷ period $\to\infty$, so each band contains many full periods;
- **(R2)** the full-period law of $S_j$ is computable (cosets of $\langle b\rangle$ in $(\mathbb Z/Q^{j+1})^\times$).

For $P_b$ both fail.

- **(R1) fails structurally.** The new information contributed by $r_K$ is the band $[m_K,m_{K+1})$ of length $\le2\sqrt{2m_K/3}+1$. By Theorem D3.7(5), every period of $r_K$ has length at least $m_K-O(1)$, so the ratio is $O(m_K^{-1/2})\to0$. Even the whole tracked prefix $[0,m_{K+1})$ is at most $1+o(1)$ times the *trivial lower bound* for the period. In fact the script certifies $\operatorname{ord}_{Q_K}(b)>20\,m_{K+1}$ for every $6\le K\le34$ ($b=2$) and $6\le K\le28$ ($b=3,5,10$). The only small orders are at $K\le5$, e.g. $\operatorname{ord}_9(2)=6$. So the prefix tracked by $r_K$ covers less than $1/20$ of a single period.
- **(R2) fails.** The law of a full period of $r_K$ is the digit statistics of $1/Q_K$ for a modulus $Q_K\approx E_bb^{m_K}$ with no exploitable multiplicative structure. That is a problem of the same kind as the original. Even in the most favourable case, a full period inside $[0,m_{K+1})$ would only reproduce statistics of finitely many digits of $P_b$ already in hand. It would not give an asymptotic statement.

In short, the reciprocal mechanism needs the approximation window to dwarf the period. For $P_b=1/E_b$ the window is $\Theta(\sqrt N)$ and the period is at least of order $N$. The rational approximants are of quality $Q^{-1-o(1)}$, weaker than Dirichlet's $Q^{-2}$. This is consistent with Phase 20 §2.5(2), which shows that no irrationality-measure information decides $K_b$ membership.

### 1.6 Finite measurements (not evidence of normality)

Certified digits are computed in two independent ways that agree: from the window enclosure of §1.2 (4044, 4030, 4022 and 4017 digits for $b=2,3,5,10$) and from $1/E_b$. Orbit points use 40-bit truncations.

| $b$ | $D_{1000}$ | $D_{2000}$ | $D_{4000}$ | words, $\ell=1$: max dev., $\chi^2$/d.f. | words, $\ell=2$: max dev., $\chi^2$/d.f. |
|---|---|---|---|---|---|
| 2 | 0.0247 | 0.0186 | 0.0253 | 0.0108, 1.8/1 | 0.0184, 7.5/3 |
| 3 | 0.0396 | 0.0309 | 0.0218 | 0.0139, 3.5/2 | 0.0139, 11.0/8 |
| 5 | 0.0327 | 0.0217 | 0.0138 | 0.0040, 0.7/4 | 0.0063, 24.2/24 |
| 10 | 0.0425 | 0.0289 | 0.0220 | 0.0090, 7.0/9 | 0.0045, 101.1/99 |

In base 2, words of lengths 3 and 4 give $\chi^2=13.5/7$ and $26.1/15$. The counts are of overlapping words over the first 4000 digits, so the $\chi^2$ values are descriptive and not test statistics. The values agree with Phase 20 §5.

### 1.7 Status of $P_b$

- **Proved:** transcendence (Phase 20 §2.4, from Nesterenko); D3.1–D3.7 above; certified digits.
- **Open, for every $b\ge2$:** normality, simple normality, $D^+(P_b)<1$, $P_b\notin K_b$, and also $P_b\in K_b$. §1.4 shows that the pentagonal recurrence is compatible with both extremes. §1.5 shows that $P_bE_b=1$ with the block structure of $E_b$ gives only $\Theta(\sqrt N)$-digit rational tracking, far below one period. Phase 20 §2.3 shows that congruences wash out.

## 2. D4 — polynomial mass, derivatives, and the width–density wall

### 2.1 The polynomial-mass rate

**Theorem D4.1 (paper proof).** Let $a$ be an integer sequence, and suppose $A(X)\le CX^\kappa$ for all $X\ge1$, with real $\kappa\ge0$ and $C>0$. Put

```math
M_\kappa(b)=\Bigl(1-\frac1b\Bigr)\sum_{i\ge0}(1+i)^\kappa b^{-i},\qquad c_\kappa=\frac{2^{\kappa+1}C\,M_\kappa(b)}{b-1}.
```

Then for **every** $N\ge1$, with $\rho=\rho_N$,

```math
1-D_N(F_b(a))=\sup_x\bigl|D_N(x+F_b(a))-D_N(x)\bigr|\le\rho\cdot\max\Bigl\{2,\ 2\log_b\frac1\rho+(\kappa-1)\log_bN+\log_b^+c_\kappa+3\Bigr\}.
```

*Proof.* We use [Phase 20 Theorem 1.4](../phase20/coefficient-transfer.md#12-the-finite-transfer-inequality) (non-lookahead shadow count $L(1+S(N-1))$, exact mean tail $\widehat A$). By Abel summation, $\widehat A(X)=(1-b^{-1})\sum_ib^{-i}A(X+i)\le CM_\kappa(b)X^\kappa$ for $X\ge1$, since $X+i\le X(1+i)$. Take $\varepsilon=\rho/2$ and $L=\max(0,\lceil\log_b(c_\kappa N^{\kappa-1}/\rho^2)\rceil)$. If $L\le N$, then $\widehat A(N+L)\le CM_\kappa(2N)^\kappa$, and the Markov term is

```math
\frac{\widehat A(N+L)}{(b-1)b^L\varepsilon N}\le\frac{c_\kappa N^{\kappa-1}}{\rho\,b^L}\le\rho,
```

so $1-D_N\le2\varepsilon+L\rho+\rho=(L+2)\rho$. If $L>N$, then $(L+2)\rho>1$ and the bound is trivial. Finally, $L+2\le\max\{2,\log_b(c_\kappa N^{\kappa-1}/\rho^2)+3\}$, which is at most the bracket. ∎

**The leading constant.** For $N\ge2$, write $\lambda_N=\log(1+S(N-1))/\log N\in[0,1]$, so $2\log_b(1/\rho)=2(1-\lambda_N)\log_bN$. Then

```math
1-D_N(F_b(a))\le\bigl(\kappa+1-2\lambda_N+o(1)\bigr)\,\rho_N\log_bN .
```

The answer to "is it $(k+1)/\log b$ or $k/\log b$?" is therefore that it depends on the support. In units of $\rho_N\log N$ the constant is $(\kappa+1-2\lambda_N)/\log b$. For $\kappa\ge1$, it ranges from $(\kappa+1)/\log b$ for bounded support down to $(\kappa-1)/\log b$ for support of density $N^{1-o(1)}$; for $0\le\kappa<1$, integrality of $a(m)$ forces $S(X)\le A(X)\le CX^\kappa$ and hence $\lambda_N\le\kappa+o(1)$, so the range is $[1-\kappa,1+\kappa]/\log b$. For $\kappa=1$ this is Phase 20 Theorem 1.5, whose constant 2 in front of $\log_b(1/\rho)$ is sharp (Phase 20 Proposition 1.6). In Lean's integer form $A(X)\le C(X+1)^k$, take $\kappa=k$. For a series with $S(X)\asymp X^\sigma$ and coefficients of regular size $m^{\kappa-\sigma}$, the width form ([Phase 20 Theorem 2.2](../phase20/coefficient-transfer.md#22-the-displaced-width-inequality), with $L=\log_b(1/\rho)+O(1)$) gives $\rho(\bar w_N+\log_b(1/\rho)+O(1))$, where $\bar w_N=(\kappa-\sigma)\log_bN+O(1)$ is the mean width. That is the same leading constant $\kappa+1-2\sigma$: the mass form and the width form agree.

**Relation to Lean.** `finite_poly_mass_transfer` is the lookahead version, with $L\cdot S(N+L)$ and $C\,2^k((N+L+2)^k+\mathrm{const})/b^L$ in place of $L(1+S(N-1))$ and $\widehat A(N+L)/((b-1)b^L)$. It suffices for `poly_mass_sparse_tendsto_one` ($S(X)=o(X/\log X)\Rightarrow F_b(a)\in K_b$) but does not give the constant. Theorem D4.1 is the sharp non-lookahead rate, and it remains a paper proof.

### 2.2 Derivatives of unary series lie in $K_b$

**Theorem D4.2 (kernel-verified in `DerivativeTransfer.lean` for the coefficient series).** Let $k\in\mathbb N$, $C\ge0$, and let $a$ have $A_a(X)\le C(X+1)^k$ and $S_a(X)\log X/X\to0$. Then for every $j\ge0$, the sequence $m^ja(m)$ satisfies the hypotheses of `GeneralMassTransfer.poly_mass_sparse_tendsto_one` with $(C,k+j)$, so $F_b(D^ja)=(q\frac d{dq})^jF(q)|_{q=1/b}\in K_b$ for every $b\ge2$ (with limiting fixed point $0$). In particular, for every $j\ge0$ and every $b\ge2$ (with $0^0=1$ at $k=0$ in the middle formula),

```math
D^jE_b=\delta_{j,0}-\sum_{i\ge1}\varepsilon(m_i)\,m_i^j\,b^{-m_i},\qquad D^j(E_b^3)=\sum_{k\ge0}(-1)^k(2k+1)T_k^{\,j}\,b^{-T_k},\qquad D^j\Theta_3(1/b)=\delta_{j,0}+2\sum_{n\ge1}n^{2j}b^{-n^2}
```

lie in $K_b$, with $T_k=k(k+1)/2$. Here $E_b=F_b(\texttt{pentCoeff})$ and $E_b^3=F_b(\texttt{jacobiCubeCoeff})$ in Lean (identifying the series with the infinite products via Euler's pentagonal theorem and Jacobi's triple-product identity, which are external to Lean).

*Proof.* The support is unchanged, and $A_{m^ja}(X)\le X^jA_a(X)\le C(X+1)^{k+j}$. For the three examples: `pentagonal_supportCount_le` and `pentCoeff_absMass_le` give $S\le2(\sqrt{2X}+1)$ and $A\le X$; `jacobiCube_supportCount_le` and `jacobiCube_absMass_le` give $S\le\sqrt{2X}$, $A\le4X$; for $\Theta_3$, $S\le\sqrt X$ and $A\le2X$. In each case $S\log X/X\to0$. All four theorems are proved in [`NormalityChecker/DerivativeTransfer.lean`](../../NormalityChecker/DerivativeTransfer.lean). ∎

**Rates (Theorem D4.1).** With $(\kappa,\lambda)$ equal to $(j+\tfrac12,\tfrac12)$ for $D^jE_b$ and $D^j\Theta_3$, and $(j+1,\tfrac12)$ for $D^jE_b^3$:

```math
1-D_N(D^jE_b)\le\Bigl(j+\tfrac12+o(1)\Bigr)\rho_N\log_bN,\qquad 1-D_N(D^jE_b^3)\le(j+1+o(1))\,\rho_N\log_bN,
```

and $D^j\Theta_3$ has the same constant as $D^jE_b$. Here $\rho_N\log_bN\asymp\log N/\sqrt N$ in all three cases.

**Polynomials.** Each of these series is $F_b(c)$ with polynomial mass. Cauchy products multiply masses ($A_{a*c}\le\bar A_a\bar A_c$, Lean `cauchyConv_absMass_le`), and a factor $u/b^s$ with $u\in\mathbb Z$ shifts indices. So:

**Corollary D4.3.** For each radix $b\ge2$, let $\mathcal P$ be any polynomial with $\mathbb Z[1/b]$ coefficients in the variables $D^jE_b$, $D^j\Theta_3(1/b)$ ($j\ge0$). If its coefficient sequence $c$ has $S_c(X)=o(X/\log X)$, then $\mathcal P(\dots)\in K_b$. This covers every degree-one polynomial, where $S_c=O(\sqrt X)$. It also covers some higher-degree ones, through cancellation. For example,

```math
E_b^2\cdot DE_b=\tfrac13D(E_b^3)=\sum_{k\ge0}(-1)^k\frac{k(k+1)(2k+1)}6\,b^{-k(k+1)/2}\in K_b,
```

using $T_k(2k+1)=3\sum_{i\le k}i^2$ (the series theorem is kernel-verified in `DerivativeTransfer.eulerSqDeriv_discrepancy_tendsto_one`, with Jacobi's identity identifying it with $E_b^2\cdot DE_b$). By §2.5, by contrast, $E_b\cdot DE_b=\frac12D(E_b^2)$ lies beyond every available transfer hypothesis. The script checks both identities through $q^{6000}$.

**Finite check of Theorem D4.1** (base 2, $N=4000$; the full table in the script also covers $N=1000$ and bases 3 and 10, and every row satisfies the bound):

| series | $j=0$ | $j=1$ | $j=2$ | $j=3$ |
|---|---|---|---|---|
| $D^jE_2$: $1-D_N$ / bound / ratio | 0.156 / 0.286 / 0.51 | 0.362 / 0.653 / 1.18 | 0.538 / 1.035 / 1.75 | 0.680 / 1.429 / 2.21 |
| $D^jE_2^3$ | 0.278 / 0.422 / 1.05 | 0.448 / 0.746 / 1.68 | 0.593 / 1.082 / 2.23 | 0.734 / 1.426 / 2.75 |
| $D^j\Theta_3(1/2)$ | 0.093 / 0.199 / 0.48 | 0.211 / 0.428 / 1.10 | 0.318 / 0.665 / 1.66 | 0.430 / 0.910 / 2.24 |

The "ratio" is $(1-D_N)/(\rho_N\log_bN)$. At $j=0$ it is close to the predicted constants $\tfrac12,1,\tfrac12$. For $j\ge1$ it lies below $j+\tfrac12$ (resp. $j+1$) and is still rising with $N$ (for example $1.68\to2.21$ for $D^3E_2$ between $N=1000$ and $4000$). These are finite measurements; Theorem D4.1 is an upper bound and we do not claim that it is attained. At $N=4000$ the bound exceeds 1 for $j\ge2$ in base 2, so it is vacuous there.

### 2.3 The width–density wall

Recall the displaced data of Phase 20 §2: $a(m)=b^{V(m)}U(m)$ with $b\nmid U(m)$, displaced index $t(m)=m-V(m)$, and $u(m)$ the number of base-$b$ digits of $|U(m)|$. In this section we define the raw-index unit width $W_U(N)=\sum_{1\le m\le N,\,a(m)\ne0}u(m)$ and the raw width $W(N)=\sum_{1\le m\le N,\,a(m)\ne0}(1+\lfloor\log_b|a(m)|\rfloor)\ge W_U(N)$. Whenever $|a(m)|\le m^{O(1)}$, we have $0\le V(m)\le O(\log m)$, so $t(m)=m-O(\log m)$ and Phase 20 Theorem 2.2's displaced-index width $W_U^{\rm disp}(N)=\sum_{1\le t(m)\le N}u(m)$ satisfies $W_U^{\rm disp}(N)=W_U(N)+O((\log N)^2)$. Thus every asymptotic lower bound on $W_U(N)$ below transfers verbatim to $W_U^{\rm disp}(N)$. The transfer theorems used in this note need $W_U^{\rm disp}(N)=o(N)$ or something stronger: Theorem 2.2 directly; Theorem 1.7, D4.1 and the Lean polynomial-mass theorem through $S\log N=o(N)$; the Lean log-mass theorem through $A=O(N\log^\gamma N)$.

**Lemma W.1 ($b$-coprime parts survive).** Let $x,y$ be nonzero integers, and let $x'$ be the largest divisor of $x$ coprime to $b$. Then $|U(xy)|\ge|x'|$.

*Proof.* Write $xy=b^VU$ and $x=x_bx'$, where every prime of $x_b$ divides $b$. Since $\gcd(b^V,x')=1$ and $b^V\mid x_bx'y$, we get $b^V\mid x_by$, so $b^V\le|x_by|$ and $|U|=|x'|\,|x_by|/b^V\ge|x'|$. ∎

**Theorem D4.4 (abstract wall).** Let $c$ be an integer sequence, $k\ge2$ an integer, and suppose:

- **(H1)** $s_0Y/\sqrt{\log Y}\le S_c(Y)\le s_1Y/\sqrt{\log Y}$ and $|c(n)|\le n^{(k-1)/2+o(1)}$;
- **(H2)** there is a set of primes $\mathcal P$ of relative natural density $\delta>0$ and integers $\lambda(p)$ such that $c(pm)=\lambda(p)c(m)$ whenever $p\in\mathcal P$ and $p\nmid m$;
- **(H3)** for $p\in\mathcal P$: $|\lambda(p)|\ge p^{(k-1)/2}$, and $v_q(\lambda(p))\le e_0$ for every prime $q\mid b$.

Then, as $Y\to\infty$,

```math
\Bigl(\frac{(k-1)\,\delta\,s_0\log\frac32}{4\log b}+o(1)\Bigr)Y\sqrt{\log Y}\ \le\ W_U(Y)\ \le\ W(Y)\ \le\Bigl(\frac{(k-1)s_1}{2\log b}+o(1)\Bigr)Y\sqrt{\log Y}.
```

*Proof.* *Lower bound.* Count $n=pm\le Y$ with $p\in\mathcal P\cap(Y^{1/2},Y^{3/4}]$ and $c(m)\ne0$. Since $m\le Y/p<p$, we have $p\nmid m$, and $p$ is the unique prime factor of $n$ above $\sqrt Y$, so distinct pairs give distinct $n$. By (H2), $c(n)=\lambda(p)c(m)\ne0$. By (H1), the number of such $n$ is

```math
\sum_{p}S_c(Y/p)\ \ge\ \frac{s_0Y}{\sqrt{\log Y}}\sum_{p\in\mathcal P\cap(Y^{1/2},Y^{3/4}]}\frac1p=(\delta\log\tfrac32+o(1))\frac{s_0Y}{\sqrt{\log Y}}
```

by partial summation, using $Y/p\ge Y^{1/4}$. By Lemma W.1 and (H3), $|U(c(n))|\ge|\lambda(p)'|\ge p^{(k-1)/2}\prod_{q\mid b}q^{-e_0}\ge p^{(k-1)/2}b^{-e_0}$. Hence $u(n)\ge\frac{k-1}4\log_bY-e_0$. *Upper bound.* $W(Y)\le\sum_{c(n)\ne0}(1+\log_b|c(n)|)\le S_c(Y)(\frac{k-1}2+o(1))\log_bY$. ∎

**Lemma W.2 (CM newforms satisfy H1–H3).** Let $g=\sum a(n)q^n$ be a newform of weight $k\ge2$ and level $M_g$, with rational integer coefficients and CM by the imaginary quadratic field $F$. Let $M$ be a multiple of $M_g\cdot|d_F|$ and of the conductor of the nebentypus, and let $\mathcal P_0=\{p\equiv1\pmod M\}$. Then (H1)–(H3) hold for $c=a$ with $\mathcal P\subseteq\mathcal P_0$ of relative density $\delta\ge\frac1{\varphi(M)}(\frac23-\eta)$ for every $\eta>0$, provided $e_0$ is large enough in terms of $\eta$.

*Proof sketch from published inputs.*

- **(H1)** is Serre's asymptotic $S(Y)\sim\alpha Y/\sqrt{\log Y}$ for CM forms of weight $\ge2$ (Serre, Publ. Math. IHÉS 54 (1981), §7, Théorème 17, as cited in Phase 20), together with Deligne's bound.
- **(H2)** is Hecke multiplicativity.
- **(H3), angle part.** A prime $p\in\mathcal P_0$ splits as $\mathfrak p\bar{\mathfrak p}$ in $F$, and $\chi(p)=1$. So $a(p)=\psi(\mathfrak p)+\overline{\psi(\mathfrak p)}=2p^{(k-1)/2}\cos\theta_{\mathfrak p}$, where $\psi$ is the Grössencharacter of $g$, of infinity type $k-1\ge1$. By Hecke's equidistribution theorem (Math. Z. 6 (1920)), the angles $\theta_{\mathfrak p}$ are equidistributed in every ray class, up to a fixed rotation. Hence $|a(p)|\ge p^{(k-1)/2}$, i.e. $|\cos\theta_{\mathfrak p}|\ge\frac12$, holds on relative density $\frac23$ of $\mathcal P_0$.
- **(H3), valuation part.** By Chebotarev's theorem for the $q$-adic representation (Serre 1981), for each prime $q\mid b$, the relative density inside $\mathcal P_0$ of $p\in\mathcal P_0$ with $q^{e+1}\mid a(p)$ is the Haar measure of $\{t\in G:\operatorname{tr}t\equiv0\bmod q^{e+1}\}$, where $G=\rho_q(\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q(\zeta_M)))$. Because $k-1\ge1$, $G$ is an open subgroup of the $2$-dimensional $q$-adic Lie group $(\mathcal O_F\otimes\mathbb Z_q)^\times$, and as $e\to\infty$ the measure decreases to that of $\{t\in G:\operatorname{tr}t=0\}=\{t\in G:t+\bar t=0\}$, a $1$-dimensional closed subset of Haar measure $0$. Taking a union bound over the finitely many primes $q\mid b$ makes the exceptional relative density inside $\mathcal P_0$ arbitrarily small for large $e_0$; moreover, the finite extension cut out by $\mathbb Q(\zeta_M)$ and the representations $\rho_q\bmod q^{e_0+1}$ ($q\mid b$) is abelian over $F$ (hence lies in a ray class field of $F$), so Hecke's equidistribution of $\theta_{\mathfrak p}$ holds inside each Frobenius class and $\mathcal P$ has a natural density $\delta\ge\frac1{\varphi(M)}(\frac23-\eta)$. ∎

**Corollary D4.5 (the wall for CM newforms).** For every CM newform of weight $k\ge2$ with rational integer coefficients, and every radix $b\ge2$, $W_U^{\rm disp}(N)=W_U(N)+O((\log N)^2)\asymp W(N)\asymp N\sqrt{\log N}$. Consequently, in every radix:

- the Lean hypothesis of `poly_mass_sparse_tendsto_one` fails, since $S(N)\log N/N\asymp\sqrt{\log N}\to\infty$;
- the hypothesis of `log_mass_sparse_tendsto_one` fails, since $A(N)\gg N^{1+(k-1)/4}/\sqrt{\log N}$ on the constructed set;
- Theorem 1.7 and Theorem D4.1 are vacuous for large $N$;
- the union bound of Theorem 2.2, $W_U^{\rm disp}(N)+L(1+P(N))+\Lambda_N$, exceeds $N$ for large $N$.

The $b$-adic valuations cannot rescue any of these: by Lemma W.1, on a set of $\gg N/\sqrt{\log N}$ sources the unit part keeps at least $\frac{k-1}4\log_bN-e_0$ digits. The same conclusion holds for the restriction of such a form to any residue class $\equiv m_0\pmod M$ that contains at least one supported index $n_0$ with $a(n_0)\ne0$ (then (H2) holds for $p\equiv1\pmod M$ with $\lambda(p)=a(p)$, and multiplying $n_0$ by integers $r\equiv1\pmod M$ coprime to $Mn_0$ with $a(r)\ne0$ yields $S(Y)\gg Y/\sqrt{\log Y}$ in the class by character orthogonality and Halász's theorem).

**This is a wall for the method, not a theorem about membership.**

**Proposition D4.6 ($W=o(N)$ is not necessary for $K_b$).** Let $w(m)$ be the binary length of $m$ and $F=\sum_{m\ge1}(2^{w(m)}-1)2^{-m}$. Then $A(X)\ll X^2$ and $W(N)=W_U(N)=\sum_{m\le N}w(m)\sim N\log_2N$, yet $F\in K_2$.

*Proof.* $2^{w}-1$ has exactly $w$ binary digits and is odd, so $u(m)=w(m)$. Put $\tilde t(m)=m-w(m)$; its steps are $0$ or $1$, and a step is $0$ exactly when $m+1$ is a power of 2. Hence

```math
F=\sum_m2^{-\tilde t(m)}-1=1+\sum_{s\ge1}2^{-(2^s-s-1)}=2+\sum_{s\ge2}2^{-(2^s-s-1)},
```

which is $2$ plus a lacunary binary number with digit-$1$ positions $2^s-s-1$ of exponential growth. Its support has $O(\log X)$ elements up to $X$ and its coefficients are bounded, so it lies in $K_2$ by Lean `linear_mass_sparse_tendsto_one`, and adding the integer $2$ changes no orbit point. ∎

The script checks the telescoped identity exactly and measures $W(N)/N=8.99,10.98$ and $D_N=0.952,0.981$ at $N=1000,4000$. So $W_U(N)\gg N$ alone proves nothing. For the CM forms the obstruction is that no available argument controls the overlapping footprints. Membership of $E_b^r$ ($r\ge4$) in $K_b$ is **open**, and so is its normality.

The footprint picture is a finite measurement. In binary, the union of the source footprints $[m-\text{digits}(a(m)),\,m-V(m)-1]$ already covers $98.7\%$ of the positions up to $16384$ for $\eta^4$, and $100.0\%$ for $\eta^6,\dots,\eta^{26}$. For the weight-one $\eta^2$ it covers $36.9\%$ (§2.4 table).

### 2.4 Serre's lacunary eta powers

Write $E_b^r=\sum_nc_r(n)b^{-n}$. Then $c_r(n)=a_{f_r}((24n+r)/g_r)$, where $g_r=\gcd(24,r)$ and $f_r=\eta(24\tau/g_r)^r$ has weight $r/2$. By Serre (Glasgow Math. J. 27 (1985)), $\eta^r$ for even $r$ is lacunary exactly when $r\in\{2,4,6,8,10,14,26\}$. (This is the brief's list $\eta^{2r}$, $2r\in\{4,\dots,26\}$, in Serre's indexing.) The script decides the CM field of each $f_r$ from its support. A form with CM by $F$ vanishes at every index containing an odd power of a prime inert in $F$. Through index $12\cdot16384$:

| $r$ | weight | form | structure (checked) | support exponent $\alpha$ | $S\sqrt{\log X}/X$ | $W_2/X$ | $W_U$ (b=2) $/X$ | $W_U$ (b=10) $/X$ | footprint cover (b=2) |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 1 | $\eta(12\tau)^2$ | CM by $\mathbb Q(i)$ and $\mathbb Q(\sqrt{-3})$; $a(p)=\pm2$ iff $p\equiv1\ (12)$ | $3/4$ | 1.21 | 0.85 | 0.39 | 0.39 | 0.369 |
| 4 | 2 | $\eta(6\tau)^4$ | newform, level 36, CM $\mathbb Q(\sqrt{-3})$ | $1/2$ | 1.78 | 4.67 | 3.04 | 1.43 | 0.987 |
| 6 | 3 | $\eta(4\tau)^6$ | newform, level 16, character $\chi_{-4}$, CM $\mathbb Q(i)$ | $1/2$ | 1.47 | 7.09 | 6.40 | 1.93 | 1.000 |
| 8 | 4 | $\eta(3\tau)^8$ | newform, level 9, CM $\mathbb Q(\sqrt{-3})$ | $1/2$ | 1.26 | 8.70 | 7.16 | 2.37 | 1.000 |
| 10 | 5 | $\eta(12\tau)^{10}$ | CM $\mathbb Q(i)$; twisted Hecke relation holds | $1/2$ | 1.84 | 16.18 | 15.25 | 4.68 | 1.000 |
| 14 | 7 | $\eta(12\tau)^{14}$ | CM $\mathbb Q(\sqrt{-3})$; twisted Hecke relation holds | $1/2$ | 1.72 | 21.86 | 21.07 | 6.67 | 1.000 |
| 26 | 13 | $\eta(12\tau)^{26}$ | **mixed**: support splits between $\mathbb Q(i)$ and $\mathbb Q(\sqrt{-3})$ | $1/2$ | 2.35 | 55.41 | 54.05 | 16.17 | 1.000 |

($X=16384$ in the radix index $n$. The widths and $S\sqrt{\log X}/X$ are finite measurements, and the asymptotic $\alpha$ is never read off a finite count.)

**Answers to the specific questions.**

- **Newforms, $r=4,6,8$.** The three forms are multiplicative eta-quotients that are newforms with integer coefficients (Martin, Trans. AMS 348 (1996)). The script checks $a(mn)=a(m)a(n)$ on more than 10,000 coprime pairs each, the Hecke relation $a(p^2)=a(p)^2-\chi(p)p^{k-1}$, the bound $|a(p)|\le2p^{(k-1)/2}$, and the inert-prime vanishing. By Lemma W.2 and Corollary D4.5 they hit the wall: **$W_U(N)\asymp N\sqrt{\log N}$ in every radix**, for $E_b^4$, $E_b^6$, $E_b^8$ (paper proof, given the cited identifications). In the radix index the support is that of $f_r$ along a linear change of variable, so the constants change but the orders do not.
- **$r=10,14$.** Each index is $\equiv5$, resp. $7\pmod{12}$. An index $\equiv2\pmod3$ contains some prime $\equiv2\pmod3$ (inert in $\mathbb Q(\sqrt{-3})$) to an odd power, so CM by $\mathbb Q(\sqrt{-3})$ would kill every coefficient of $\eta^{10}$. Likewise an index $\equiv3\pmod4$ rules out $\mathbb Q(i)$ for $\eta^{14}$. The script confirms CM by $\mathbb Q(i)$ for $\eta^{10}$ and by $\mathbb Q(\sqrt{-3})$ for $\eta^{14}$, **not** $\mathbb Q(\sqrt{-7})$. It also checks the twisted Hecke relation $a(pm)=a(pm_0)\,a(m)$, with $m_0=5$ resp. $7$, for all primes $p\equiv1\pmod{12}$ below 600 and coprime $m$ in the class, on 1,213 and 1,215 instances, with no failures. This is the relation of a CM newform restricted to one residue class. Given that structure, Theorem D4.4 applies with $\lambda(p)=a(pm_0)$, and the good-prime proportion is measured at $0.66$ resp. $0.65$ with $e_0=3$. We did not identify the underlying newforms, so for $r=10,14$ the wall is **conditional** on the class-restriction structure (and on (H1)).
- **$r=26$.** The twisted relation fails (140 hold, 1,058 fail). The support contains indices that violate the $\mathbb Q(i)$ condition and indices that violate the $\mathbb Q(\sqrt{-3})$ condition, but none that violate both. This is consistent with $\eta(12\tau)^{26}=f_{\mathbb Q(i)}+f_{\mathbb Q(\sqrt{-3})}$ for two CM forms. If that decomposition holds, the support is contained in a union of two Landau-type sets, so $S\ll X/\sqrt{\log X}$ ($\alpha=\frac12$). Off the $\mathbb Q(\sqrt{-3})$-support, $c=f_{\mathbb Q(i)}$, so the lower bound of Theorem D4.4 would apply to that component. We have not proved the decomposition, so for $r=26$ the wall is a **finite measurement** ($W_U/X=54.05$ in binary at $X=16384$).
- **Can a weight-$\ge2$ newform have $\alpha>1$?** No. A CM newform has $\alpha=\frac12$ exactly: the inert primes have density $\frac12$, and split primes with $a(p)=0$ have density $0$ by Hecke equidistribution. A non-CM newform of weight $\ge2$ has support of positive density (Serre 1981, §7), so $\alpha=0$. For arbitrary linear combinations we prove nothing beyond the upper bound for CM combinations.
- **The weight-one form $\eta^2$** has $a(p)=\pm2$ for every prime $p\equiv1\pmod{12}$ (checked on all 4,394 such primes up to $196{,}608$) and $a(p)=0$ for the other primes, which are inert in $\mathbb Q(i)$ or $\mathbb Q(\sqrt{-3})$. So $\alpha=\frac34$ (Wirsing), and $E_b^2\in K_b$ (Phase 20).

### 2.5 Where derivatives meet the wall

**Proposition D4.7 (paper proof).** Let $f$ be $\Theta_3(1/b)^2=1+4L_{\chi_4}(b)$ or $E_b^2$, with support exponent $\alpha=\frac12$ (Landau) or $\alpha=\frac34$ (§2.4). Then $f\in K_b$ (Phase 20). For every $j\ge1$, however, $D^jf$ satisfies

```math
\frac{S(X)\log X}X\asymp(\log X)^{1-\alpha}\to\infty,\qquad W_U(X)\gg j\,X(\log X)^{1-\alpha},
```

in every radix. So every transfer hypothesis of §2.3 fails. The same holds for $E_b\cdot DE_b=\frac12D(E_b^2)$ and $\Theta_3\cdot D\Theta_3=\frac12D(\Theta_3^2)$.

*Proof.* $D^j$ does not change the support. For $m\in(X/2,X]$ in the support, Lemma W.1 with $x=m^j$ gives $u(m)\ge j\log_b(m')$, where $m'$ is the $b$-coprime part of $m$ (for $E_b\cdot DE_b=\frac12D(E_b^2)$ and $\Theta_3\cdot D\Theta_3=\frac12D(\Theta_3^2)$, halving the integer coefficients $mc_2(m)$ or $mr_2(m)$ reduces $|U|$ by at most a factor of $2$, costing at most $1$ digit). The number of $m\le X$ whose $b$-smooth part exceeds $\sqrt{X/2}$ is at most $\sum_{s>\sqrt{X/2},\ s\ b\text{-smooth}}X/s\ll X^{1/2+o(1)}$. So all but $X^{1/2+o(1)}$ of the $\gg X/(\log X)^\alpha$ supported $m\in(X/2,X]$ have $u(m)\ge\frac j2\log_b(X/2)-1$. ∎

So the boundary is sharp in the derivative order. Unary objects such as $E_b$, $E_b^3$ and $\Theta_3$ have $S\asymp\sqrt X$ and stay inside $K_b$ under every $D^j$ (Theorem D4.2). Binary objects such as $\Theta_3^2$, $L_\chi$ and $E_b^2$ are inside at $j=0$ and beyond the wall at every $j\ge1$. Weight $k\ge2$ CM forms are beyond the wall already at $j=0$: their coefficients behave like a built-in derivative of order $\frac{k-1}2$.

| series | $j$ | $S\log X/X$ | $W_2(X)/X$ |
|---|---|---|---|
| $D^j\Theta_3$ | 0 / 1 / 2 | 0.112 | 0.026 / 0.145 / 0.270 |
| $D^jE_b$ | 0 / 1 / 2 | 0.183 | 0.021 / 0.216 / 0.422 |
| $D^j\Theta_3^2$ | 0 / 1 / 2 | 2.475 | 1.220 / 4.220 / 7.332 |
| $D^jE_b^2$ | 0 / 1 / 2 | 3.636 | 0.897 / 5.292 / 9.866 |

($X=6000$, finite measurements.)

### 2.6 Dense classical constants

The script checks the following identities exactly through $q^{6000}$ ($\Delta$ through $q^{400}$): Jacobi's $r_4(n)=8\sum_{d\mid n,\,4\nmid d}d$; $\Theta_3^4=\frac13(4E_2(q^4)-E_2(q))$; Legendre's criterion $r_3(n)=0\iff n=4^a(8k+7)$; and $\Delta=(E_4^3-E_6^2)/1728=q\prod(1-q^n)^{24}$. The only exact reductions modulo $K_b$ known to us are those of Phase 20 §3.2. With $L=L_{\chi_4}(b)\in K_b$,

```math
\Theta_3(1/b)^4\equiv16L^2,\qquad\Theta_3(1/b)^3\equiv4\,\Theta_3(1/b)\,L,\qquad E_2(1/b)\equiv4E_2(b^{-4})-48L^2\pmod{K_b},
```

The last follows from $E_2(q)=4E_2(q^4)-3\Theta_3(q)^4$ (checked) and the fact that $K_b$ is an additive group. These identify discrepancy behaviour; they decide none of it.

| constant | $W_2(N)/N$ | $W_{10}(N)/N$ | $D_{4000}$, $b=2$ | $D_{4000}$, $b=10$ |
|---|---|---|---|---|
| $\Theta_3^3$ | 7.01 | 2.38 | 0.0191 | 0.0203 |
| $\Theta_3^4$ | 14.09 | 4.62 | 0.0163 | 0.0155 |
| $E_2(1/b)$ | 16.26 | 5.23 | 0.0168 | 0.0244 |
| $E_4(1/b)$ | 40.08 | 12.43 | 0.0221 | 0.0193 |
| $E_6(1/b)$ | 62.12 | 19.06 | 0.0221 | 0.0240 |
| $\Delta(1/b)$ | 56.61 | 17.40 | 0.0241 | 0.0276 |

($N=4000$.) The width densities grow like $(k-1)\log_bN$ for the weight-$k$ Eisenstein series $E_2,E_4,E_6$ and $\Theta_3^4$, like $\frac5{12}\log_bN$ for $\Theta_3^3$ (weight $\frac32$, support density $\frac56$), and at most like $\frac{k-1}2\log_bN=\frac{11}2\log_bN$ for the weight-$12$ cusp form $\Delta$ (by Deligne's bound). The supports have positive density, so these series are far beyond the wall. In base 2, $D_{4000}(E_2^r)=0.844,0.067,0.722$ for $r=1,2,3$, and lies between $0.015$ and $0.026$ (max $0.0253$ at $r=14$) for $r\in\{4,6,8,10,14,26\}$. **Normality and $K_b$ membership of every constant in this subsection are open**, as are those of $E_b^r$ for $r\ge4$.

## 3. Verification

`python -B scripts/phase21_partitions_modular.py` exits 0 in about 5 seconds with 125,884 assertions. It checks:

- **D3:** both bounds for $p(n)$, $n\le4700$; the window ordering and the asymptotic formula (12 rows); agreement of certified digits of $P_b$ computed from the window enclosure and from $1/E_b$, $b\in\{2,3,5,10\}$; the shift register and the pentagonal window identity (exact integers); the window transfer (first 30 binary digits of $x_n$ against $R_{n,L}$ up to one final carry); the solved tail formula; the homogeneous solution $\theta p(n)$; $Q_K\equiv\pm1\pmod b$, $A_K\le m_{K+1}$, and $\operatorname{ord}_{Q_K}(b)>20m_{K+1}$ for $K\ge6$.
- **D4:** the mass hypotheses $A(X)\le CX^\kappa$ and $A(X)\le C(X+1)^{\lceil\kappa\rceil}$ for the derivative families; Theorem D4.1 against exact finite discrepancies (72 cases, bases 2, 3 and 10); monotone decrease of $S\log N/N$ for the unary supports; the counterexample identity; the CM-field support conditions for all seven eta powers; multiplicativity, the Hecke $p^2$ relation and the Hecke bound for $r=4,6,8$; the twisted Hecke relation for $r=10,14$ and its failure for $r=26$; Lemma W.1 on $1\le x,y<120$ in radices $2,6,10,12$; the factorization $c(pm)=\lambda(p)c(m)$ and the surviving width $u>\frac{k-1}2\log_{10}p-3$ on every constructed source; $\eta^2$ at primes $\equiv1\pmod{12}$; the two product identities of §2.2; and the classical identities of §2.6.

## 4. Scope and open problems

1. **$P_b$.** Prove $D^+(P_b)<1$ in some base, or decide $P_b\in K_b$. By Theorem D3.6 this needs input beyond the pentagonal recurrence. By Theorem D3.7 it needs input beyond rational approximation by $1/E_b^{(K)}$.
2. **Sharpness of Theorem D4.1 for $\kappa>1$.** Is $\kappa+1-2\lambda$ attained, as $2$ is for $\kappa=1$? The finite ratios for $D^jE_b$ are still increasing at $N=4000$.
3. **$\eta^{10},\eta^{14},\eta^{26}$.** Identify the CM newforms. For $r=10,14$, prove the class-restriction structure; for $r=26$, prove the two-field decomposition. Either would make the wall unconditional for that $r$.
4. **Beyond the wall.** Decide $E_b^4\in K_b$, or $E_b\cdot DE_b\in K_b$, the simplest series whose width is $\gg N$ but whose support has density zero. Proposition D4.6 shows that large width alone is no obstruction to membership.
5. Do the footprint unions for the weight-$\ge2$ CM forms have density 1, as the finite coverage $0.987$–$1.000$ suggests? That would need short-interval information about the support at scale $\log n$, in the spirit of Hooley and Plaksin for sums of two squares.

## 5. Lean finite cores (items 1–4 kernel-verified; items 5–8 remaining targets)

Items 1–4 are now formalized, compiled with zero warnings, and kernel-replayed in [`NormalityChecker/DerivativeTransfer.lean`](../../NormalityChecker/DerivativeTransfer.lean). Items 5–8 remain recommended future Lean targets.

1. **Derivative transfer (kernel-verified in `DerivativeTransfer.lean`).** `derivCoeff_absMass_le`, `derivCoeff_supportCount_le`, `derivCoeff_tendsto_one`, `derivCoeff_preserves_discrepancy`, and the instantiations `deriv_eulerPentagonal_discrepancy_tendsto_one` (using `pentCoeff_absMass_le`, $C=1$), `deriv_eulerCube_discrepancy_tendsto_one` ($C=4$, from `jacobiCube_absMass_le`), and `deriv_thetaThree_discrepancy_tendsto_one` ($C=2$) for all $j\ge0$ and $b\ge2$.
2. **$E_b^2DE_b$ (kernel-verified for the triangular series in `DerivativeTransfer.lean`).** The exact integer identity `three_mul_eulerSqDerivCoeff` ($3\cdot c(m) = m\cdot$`jacobiCubeCoeff m`) and `eulerSqDeriv_discrepancy_tendsto_one` for all $b\ge2$ (identifying the series with $E_b^2DE_b$ uses Jacobi's triple-product identity, external to Lean as in `EulerPentagonal.lean`).
3. **Lemma W.1 (kernel-verified in `DerivativeTransfer.lean`).** `coprimePart_le_natAbs_radixUnit_mul`: for nonzero `x y : ℤ` and `d ∣ x.natAbs` with `Nat.Coprime d b`, `d ≤ (radixUnit b (x * y)).natAbs`.
4. **Shift register (kernel-verified in `DerivativeTransfer.lean`).** `carryWindow_succ_eq` and `carryWindow_succ_modEq`: `carryWindow b a (n + 1) L ≡ b * carryWindow b a n L + a (n + L + 1) [ZMOD b^L]`.
5. **Pentagonal window identity and homogeneous solutions (open Lean target),** stated for any sequence satisfying Euler's recurrence (taken as a hypothesis, since Mathlib lacks the pentagonal theorem): the identity of Proposition D3.5(2), and that $\theta\cdot p$ satisfies the homogeneous recurrence.
6. **$Q_K\equiv-\varepsilon(m_K)\pmod b$ (open Lean target).** Pure ring arithmetic.
7. **Theorem D4.1 non-lookahead (open Lean target).** This needs the paper-only shadow count $L(1+S(N-1))$ (Phase 20 Lemma 1.2) and the weighted far tail $\widehat A$ (Lemma 1.3). It is the main missing finite core for sharp rates.
8. **Proposition D4.6 (open Lean target).** The telescoping $\sum_m(2^{w(m)}-1)2^{-m}=2+\sum_{s\ge2}2^{-(2^s-s-1)}$, together with the Phase 18 bounded-coefficient sparse transfer. This yields a kernel-checked element of $K_2$ with $W(N)\gg N\log N$.

## References

- T. M. Apostol, *Introduction to Analytic Number Theory*, Springer 1976, Thm. 14.5; *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., Springer 1990, Thm. 3.1.
- G. H. Hardy and S. Ramanujan, Asymptotic formulae in combinatory analysis, Proc. London Math. Soc. (2) 17 (1918).
- H. Weyl, Über die Gleichverteilung von Zahlen mod. Eins, Math. Ann. 77 (1916).
- E. Hecke, Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen II, Math. Z. 6 (1920).
- J.-P. Serre, Quelques applications du théorème de densité de Chebotarev, Publ. Math. IHÉS 54 (1981).
- J.-P. Serre, Sur la lacunarité des puissances de η, Glasgow Math. J. 27 (1985).
- Y. Martin, Multiplicative η-quotients, Trans. Amer. Math. Soc. 348 (1996).
- E. Landau, Über die Einteilung der positiven ganzen Zahlen in vier Klassen …, Arch. Math. Phys. (3) 13 (1908).
