# The $E(4)$ and $E^*(4)$ carry-correlation frontier

Phase 25, Track A. Companion script: `scripts/phase25_e4_carries.py`. `python -B scripts/phase25_e4_carries.py` runs 2,513,921 exact checks in about 10–15 s and exits with code 0. Every certificate uses exact integers, `fractions.Fraction`, or integer arithmetic at scale $2^{-100}$ with directed rounding, and no check counted as exact uses floating-point arithmetic. Floating point appears only in the display of finite measurements (§9) and in the heuristic model of §10 (Section 8 of the script). The model's three loose sanity assertions are counted separately from the exact checks. Every certified decimal interval quoted here is the outward rounding of an exact `Fraction` enclosure: the lower endpoint is rounded down, the upper endpoint up, and the script asserts each quoted endpoint. Finite digit statistics (§9) are **finite measurements only** and are never used as evidence for limits. This revision addresses every finding of one cross-provider model review (`notes/phase25/reviews/track-a-review.md`). Cross-model review is not independent human peer review.

## Results at a glance

| Item | Statement | Evidence | Objectives |
| --- | --- | --- | --- |
| A1.1 | **True-carry identity.** $S(N)=R(N)-K(N)+c_N$. Here $K(N)$ is a prefix sum of the single sequence $c_j=\lfloor\sum_{i>j}r_i2^{j-i}\rfloor$, the true carries of the infinite column sum (Thm 1.2) | Paper proof; Finite certificate for every $N\le2^{17}$ | 3 |
| A1.2 | **Integer tail correction.** Phase 24's $\kappa$, which includes $\lfloor\tau_N\rfloor$, equals $K(N)+O(\log^2N)$. The head-only count misses exactly the carry chain that $\lfloor\tau_N\rfloor$ launches, and this chain is bounded by $\ell(T_N)+Z(N)$, where $Z(N)$ is a zero run of $E(4)$. Certified worst case: a gap of 9 at $N=490$ with $T_N<4$ (Thm 1.4) | Paper proof; Finite certificate | 3, 4 |
| A1.3 | **Window approximation.** $0\le K-K^{(W)}\le\#\{j:\ d_{j+1}=\dots=d_{j+W-\ell}=0\}$ (Thm 1.5) | Paper proof | 3, 4 |
| A1.4 | Simple normality of $E(4)$ in base 2 holds if and only if $K(N)/N\to\theta=(C_{\rm true}-1)/2$, in five equivalent forms (Cor 1.6) | Paper proof | 1, 2 |
| A2.1 | **Stationarity bound** (unconditional): $\limsup f_1\le\limsup\frac1N\sum_{j<N}\{R_W(j)/2^W\}+2^{-W}\mu/2$ for every $W$ (Thm 2.2) | Paper proof | 2, 3 |
| A2.2 | **Locality barrier.** Fixed-shift collisions have density 0. Every carry witness that uses boundedly many consecutive coefficients has asymptotic density 0, so it cannot improve $\limsup f_1\le C_{\rm true}/2$ (Thm 2.3) | Paper proof with External input (bivariate Erdős–Kac) | 4 |
| A2.3 | **Three-column criterion.** If the residue law of 3 consecutive columns matches the compound-Poisson comparison law (hypothesis $H_3$), then $\limsup f_1(E(4);2)\le0.452881$, so $E(4)$ is not simply normal and $D^-\ge0.047119$. On this route two columns cannot suffice, since $B_2>\frac12$ (Thm 2.4) | Conditional; Finite certificate | 2, 3 |
| A2.4 | **$E(2)$:** the same route needs 8 columns: under $H_8^{(1)}$, $B_8\le0.497108$. The CC-49 statistic uses 16 columns, and our hypothesis is implied by CC-49's distributional 16-column hypothesis (Rem 2.5) | Conditional; Finite certificate | 2, 4 |
| A2.5 | $\mu=\lim\frac1X\sum_{n\le X}\mathrm{odd}(\tau(n))\in[2.07632553,\,2.07632693]$, 50 times narrower than Phase 17 (CC-49) (Thm 2.6) | Finite certificate | 3 |
| A3.1 | $s_4(m)+s_4(2m)=3s_2(m)$. The mean of $s_4(\tau(n))$ is $\frac32C_{\rm true}$. Even and odd columns receive equal arrival densities (Thm 3.2) | Paper proof with External input (Wirsing) | 3 |
| A3.2 | Exact base-4 identities. Base-4 carries are the even binary carries, and $f_{\rm even}-f_{\rm odd}=3(E_M-O_M)/M+o(1)$, where $E_M$ and $O_M$ are the even- and odd-column carry totals (Thm 3.3) | Paper proof; Finite certificate; asymptotic part with External input (Wirsing) | 1, 2, 3 |
| A3.3 | The brief's "low-bit asymmetry" from $\tau(n)$ being odd only at squares is **refuted at first order** (Prop 3.5) | Paper proof with External input (Wirsing) | 4 |
| A4.1 | $E^*(4)$ is normal in base 2 if and only if it is simply normal and $\mathbf 1_Q$ is normal, where $Q=\{2n-\omega(n)\}$. Base-4 simple normality forces $\#\{m\le M:2m-1,2m\in Q\}\sim M/4$ (Thm 4.1) | Paper proof; Finite certificate; the conditional-density clause of (d) with External input (Wirsing) | 1, 2 |
| A4.2 | Collisions occur only between equal $\omega$-parities. A second-moment criterion, from local lower bounds at shifts $d\asymp\sqrt{\log\log n}$, would prove simple nonnormality (Thms 4.2–4.3) | Paper proof; Conditional | 2, 4 |
| A5.1 | Exact countermodels. Neither the proved column mean nor the first two factorial moments determine $f_1$ relative to $\frac12$. For $E^*(4)$ the threshold is one-sided (Thms 5.1–5.3) | Finite certificate (exact rationals) | 4 |
| A5.2 | Comparison-law predictions: $f_1(E(4))\to0.4047$ with base-4 law $(0.357,0.238,0.238,0.166)$, and $f_1(E^*(4))\to0.3635$. The expected truth is that **neither is simply normal** (§10) | Heuristic; floating-point | — |

### Status of the brief's proposals

| Brief item | Outcome |
| --- | --- |
| A1: include $\lfloor\tau_N\rfloor$ and do not assume an $O(\log N)$ popcount effect | **Confirmed and made exact.** Phase 24's $\kappa$ already contains the tail and equals the true $K(N)$ up to $O(\log^2N)$ (Thm 1.4a). The head-only count can differ by a zero run of unbounded length (Thm 1.4b, c); the certified example is a gap of 9 from $T_{490}<4$. The clean statistic is $K(N)$ (Thm 1.2) |
| A1: $f_1=C_{\rm true}/2-\kappa_2/N+o(1)$, threshold $[0.169551,0.169558]$ | **Proved** with the true carries, in five equivalent forms (Cor 1.6) |
| A2: reset-block lower bound | **Proved valid** for column windows, column blocks and coefficient groups (Thm 2.1). Coefficient-local versions have density 0 (Thm 2.3). Column-window versions are not computable from present theorems |
| A2: prove $\liminf\kappa_2/N>\theta$ | **Not proved unconditionally.** It is proved under the 3-column hypothesis $H_3$, with bit-carry density at least $0.216670>\theta$ (Thm 2.4). The comparison law predicts $0.2649$. The unconditional interval $\limsup f_1\le C_{\rm true}/2$ is **not improved**, and Thm 2.3 shows why |
| A3: huge parity asymmetry from $\tau(n)$ odd only at squares | **False at first order.** The low bits come from $\mathrm{bit}_{2t}(\tau(m+t))$, and their mean equals that of the high bits, because $(-1)^{v(n)}$ has mean 0 (Prop 3.5). The real even/odd question is $E_M$ versus $O_M$, the even- and odd-column carry totals (Thm 3.3). The prefix shows $f_{\rm e}=0.448$, $f_{\rm o}=0.541$; this is a finite measurement only, and the comparison law predicts symmetry |
| A4: positive-density collision set for $E^*(4)$ | **Open.** We prove reformulations, a parity constraint and a conditional second-moment theorem (LLB+PUB). We identify the blocking ingredient: a lattice-resolution local law at growing shifts, which contains a two-point sign problem for $(-1)^\omega$ |
| A5: barriers and countermodels extending CC-49/GF-28 | **Done** (Thms 2.3, 5.1–5.3, minimality in Thm 2.4) |

## 0. Definitions

**Digits.** For $x\in[0,1)$ let $d_j$ be the binary digits of the expansion not ending in $1^\infty$. Put $S(N)=\sum_{j\le N}d_j$ and $f_1(N)=S(N)/N$. Let $F_N(I)$ be the proportion of $0\le j<N$ with $\{2^jx\}\in I$.

**Arithmetic.** Write $\tau(n)=2^{v(n)}o(n)$ with $o(n)$ odd. Then $v(n)=\sum_{p^e\parallel n}v_2(e+1)$ and $o(n)=\prod_{p^e\parallel n}\mathrm{odd}(e+1)$, where $\mathrm{odd}(m)=m/2^{v_2(m)}$. The function $o$ is multiplicative with $o(p)=1$. Let $s(n)$ be the squarefull part of $n$. Let $B(m)$ be the set of bit positions of $m$, and $\ell(T)$ the bit length of $T$.

**Constants.** $C_{\rm true}=\lim\frac1X\sum_{n\le X}s_2(\tau(n))\in[1.339103,1.339116]$ (Phase 24 Thm 4.1), and $\theta=(C_{\rm true}-1)/2\in[0.169551,0.169558]$. Further $\mu=\lim\frac1X\sum_{n\le X}o(n)=\prod_p(1-\frac1p)\sum_{e\ge0}\mathrm{odd}(e+1)p^{-e}$. The limit exists by Phase 24 Lemma 3.1, since $o(p)=1$ and $o(p^e)\le e+1$.

**Columns of $E(4)=\sum_{n\ge1}\tau(n)4^{-n}$.** Column $j\ge1$ has weight $2^{-j}$. It receives the

- *bit arrivals* $r_j=\#\{(n,i):i\in B(\tau(n)),\ 2n-i=j\}$, and the
- *mark arrivals* $J_j=\sum_{n:\,2n-v(n)=j}o(n)$, where the whole odd part sits at the column of the lowest bit.

Then $x=\sum_jr_j2^{-j}=\sum_jJ_j2^{-j}$. For $E(2^k)$ replace $2n$ by $kn$.

**True carries.** For integers $a_j\in\mathbb Z_{\ge0}$ with $\sum a_j2^{-j}<\infty$ put $c_j(a)=\lfloor\sum_{i>j}a_i2^{j-i}\rfloor$ for $j\ge0$. Write $c_j=c_j(r)$ and $K(N)=\sum_{j=1}^{N-1}c_j$, and analogously $c^J_j$ and $K^J(N)$. Put $R(N)=\sum_{j\le N}r_j$. The window carry is $c^{(W)}_j(a)=\lfloor\sum_{j<i\le j+W}a_i2^{j-i}\rfloor$, and $K^{(W)}(N)=\sum_{j=1}^{N-1}c^{(W)}_j(r)$. The residue window is

```math
R_W(j)=\Bigl(\sum_{i=1}^WJ_{j+i}2^{W-i}\Bigr)\bmod 2^W .
```

**Head and tail (Phase 24 §2).** Let $M=\lfloor N/2\rfloor$, $A_N=\sum_{n\le M}\tau(n)2^{N-2n}$, $\tau_N=\sum_{n>M}\tau(n)2^{N-2n}$ and $T_N=\lfloor\tau_N\rfloor$. Define

```math
\kappa_{24}(N)=\sum_{n\le M}s_2(\tau(n))+s_2(T_N)-s_2(A_N+T_N),\qquad \kappa_{\rm head}(N)=\sum_{n\le M}s_2(\tau(n))-s_2(A_N).
```

$Z(N)$ is the length of the run of zero digits of $x$ that ends at position $N-\ell(T_N)$, read backwards and counted only over positive indices. So $Z(N)$ is the largest $z$ with $0\le z\le N-\ell(T_N)$ and $d_{N-\ell(T_N)-z+1}=\dots=d_{N-\ell(T_N)}=0$, and $Z(N)=0$ if $\ell(T_N)\ge N$. In particular $Z(N)\le N$ is always finite.

**Comparison law (heuristic object, used only in Conditional statements).** Let $\nu$ be the law of $\prod_p\mathrm{odd}(\varepsilon_p+1)$ with independent $\mathbb P(\varepsilon_p=e)=(1-\frac1p)p^{-e}$; this is the density law of $o(n)$ (Phase 24 Lemma 3.2). $\mathrm{CP}(\lambda,\nu)$ is the law of $U_1+\dots+U_K$ with $K\sim\mathrm{Poisson}(\lambda)$ and $U_i\sim\nu$ i.i.d. $Q_W^{(\lambda)}$ is the law of $\sum_{i\le W}J_i2^{W-i}\bmod2^W$ for i.i.d. $J_i\sim\mathrm{CP}(\lambda,\nu)$. Take $\lambda=1/k$ for $E(2^k)$; for $\lambda=1$ this is the law $Q_D$ of Phase 17 (CC-49).

**$E^*(4)=\sum_n2^{\omega(n)}4^{-n}=\sum_n2^{-q(n)}$** with $q(n)=2n-\omega(n)$. Put $r^*_j=\#\{n:q(n)=j\}$ and $Q=q(\mathbb N)$, and define $c^*_j$ and $K^*(N)$ as above.

## 1. A1: many-summand Kummer framework with the true tail

**Lemma 1.1 (true carries; Paper proof).** Let $x=\sum_{j\ge1}a_j2^{-j}$ with integers $a_j\in\mathbb Z_{\ge0}$. (Integrality is what makes $2^jx-Y_j$ an integer in the proof.)

- (a) $c_0=\lfloor x\rfloor$.
- (b) $a_j+c_j=d_j+2c_{j-1}$ for $j\ge1$.
- (c) $c_{j-1}=\lfloor(a_j+c_j)/2\rfloor$.
- (d) If $a\le a'$ coordinatewise, then $c(a)\le c(a')$.
- (e) $c^{(W)}_j\le c_j$. If $c_{j+W}\le B$ with $B+1\le2^W$, then $c_j-c^{(W)}_j\in\{0,1\}$. Moreover $c_j>c^{(W)}_j$ forces $d_{j+1}=\dots=d_{j+W-\ell}=0$ for every $\ell$ with $2^\ell\ge B+1$.

*Proof.* Put $Y_j=\sum_{i>j}a_i2^{j-i}$. Then $2^jx-Y_j\in\mathbb Z$, so $\{Y_j\}=\{2^jx\}=0.d_{j+1}d_{j+2}\ldots$ and $c_j=\lfloor Y_j\rfloor$.

(b) Taking integer parts in $2Y_{j-1}=a_j+Y_j$ gives $2c_{j-1}+\lfloor2\{2^{j-1}x\}\rfloor=a_j+c_j$, and $\lfloor2\{2^{j-1}x\}\rfloor=d_j$. Then (c) follows because $d_j\in\{0,1\}$, and (d) because the floor is monotone.

(e) Write $Y_j=P+2^{-W}Y_{j+W}$, where $P=\sum_{j<i\le j+W}a_i2^{j-i}$ and $0\le2^{-W}Y_{j+W}<2^{-W}(B+1)\le1$. So $c_j\in\{\lfloor P\rfloor,\lfloor P\rfloor+1\}$. In the second case $\{2^jx\}=\{P\}+2^{-W}Y_{j+W}-1<2^{\ell-W}$. ∎

**Theorem 1.2 (exact digit identity; Paper proof; Finite certificate).** For $E(4)$ and every $N\ge1$,

```math
S(N)=R(N)-K(N)+c_N=\sum_{j\le N}J_j-K^J(N)+c^J_N .
```

Here $R(N)=\sum_{n\le M}s_2(\tau(n))+\varepsilon_N$ with $0\le\varepsilon_N=O(\log^2N)$, and

```math
c_N\le\frac32+\frac14\log_2N+\frac1{2N\ln2}.
```

The last term is below $0.001$ for $N\ge722$. Also $\sum_{j\le N}J_j=\sum_{n\le M}o(n)+O(\sqrt N\log N)$ and $c^J_N\le3\sqrt N$. Hence, with an explicit error term for the finite sum,

```math
f_1(N;E(4),2)=\frac1N\sum_{n\le M}s_2(\tau(n))-\frac{K(N)}N+O\Bigl(\frac{\log^2N}N\Bigr).
```

Replacing the finite mean by its limit gives only an error $o(1)$:

```math
f_1(N;E(4),2)=\frac{C_{\rm true}}2-\frac{K(N)}N+o(1)=\frac\mu2-\frac{K^J(N)}N+o(1).
```

No rate is claimed for the passage from the finite mean to $C_{\rm true}/2$. A rate of $O(\log^2N/N)$ there would be false. Since $\zeta(\frac12)<0$ while $\mathbb E_s[s_2(o(r))]\to\infty$ as $s\to\frac12^+$ (squarefull $r$ weighted by $r^{-s}$), the error $\sum_{n\le X}(s_2(\tau(n))-C_{\rm true})$ is not $O(X^\vartheta)$ for any $\vartheta<\frac12$; see the review, finding M1. For $E(2^k)$ the right-hand sides are $C_{\rm true}/k-K_k(N)/N+o(1)$ and $\mu/k-K^J_k(N)/N+o(1)$.

*Proof.* Sum Lemma 1.1(b) over $j=1,\dots,N$ and use $c_0=\lfloor E(4)\rfloor=0$.

*Bound on $r_i$.* If $n$ contributes to column $i$, then $i\le2n\le i+\ell(\tau(n))-1$, and $\ell(\tau(n))\le2+\frac12\log_2n$ because $\tau(n)\le2\sqrt n$. This forces $n\le i$, so at most $(\ell+1)/2$ values of $n$ occur. Hence $r_i\le\frac32+\frac14\log_2i$ for every $i\ge1$. Since $c_N\le\sum_{m\ge1}r_{N+m}2^{-m}$ and $\log_2(1+m/N)\le m/(N\ln2)$,

```math
c_N\le\frac32+\frac14\log_2N+\frac14\sum_{m\ge1}\frac{\log_2(1+m/N)}{2^m}\le\frac32+\frac14\log_2N+\frac1{2N\ln2},
```

using $\sum_{m\ge1}m2^{-m}=2$. The term $1/(2N\ln2)$ is below $0.001$ only for $N\ge722$. For $N\le2^{17}$ the certificate below gives $c_N\le2$ directly.

*Bound on $\varepsilon_N$.* $\varepsilon_N$ counts the bits of $\tau(M+m)$, $m\ge1$, that land in columns $\le N$. There are at most $(\ell_{\max}-2m+1)^+$ of them for each $m$, so $\varepsilon_N=O(\log^2N)$.

*$J$-boundary.* At most $O(\log N)$ integers $n$ satisfy $2n-v(n)\le N<2n$, and each has $o(n)\le2\sqrt n$. Also $\sum_{i>N}J_i2^{N-i}\le\sum_{n>N/2}\tau(n)2^{N-2n}$.

*Means.* Dividing the exact identity by $N$ gives the first display with error $O(\log^2N/N)$, from $\varepsilon_N$ and $c_N$. The second display uses only $\frac1M\sum_{n\le M}s_2(\tau(n))\to C_{\rm true}$ and $\frac1M\sum_{n\le M}o(n)\to\mu$ (Phase 24 Lemmas 3.1–3.2), which give $o(1)$ and no rate. ∎

*Certificate.* For $N\le2^{17}$ the script verifies both identities and every column equation. The true carries are exact: the chains started at column $J_0=2^{17}+64$ from $0$ and from the a priori bound $B=5$ coalesce before column $2^{17}+1$, and (d) sandwiches the truth between them. The bound $c_{J_0}\le5$ follows from the display above, and the script checks it exactly in integers as $J_0^{16}\le2^{16\cdot18-1}$. The largest true carry in this range is $2$.

*Remark 1.3.* $K(N)$ is a prefix sum of **one** sequence $(c_j)$, which is independent of $N$. By contrast, $\kappa_{24}(N)$ and $\kappa_{\rm head}(N)$ are recomputed for each $N$ from a truncated addition. This is the precise sense in which the infinite tail is handled.

**Theorem 1.4 (integer tail correction; Paper proof; Finite certificate).** For every $N$:

- (a) $\kappa_{24}(N)=K(N)-c_N+s_2(T_N)-\varepsilon_N$. Hence $\kappa_{24}=K+O(\log^2N)$, so Phase 24's Theorem 9.1 is correct as stated: its $\kappa$ includes the tail.
- (b) $0\le\kappa_{24}(N)-\kappa_{\rm head}(N)=s_2(A_N)+s_2(T_N)-s_2(A_N+T_N)\le\ell(T_N)+Z(N)$.
- (c) The gap in (b) is the Kummer carry count of $A_N+T_N$. Beyond bit $\ell(T_N)-1$ it equals the length of the run of 1-bits of $A_N$ that starts at bit $\ell(T_N)$ when a carry enters bit $\ell(T_N)$, and $0$ otherwise. That run becomes a zero run of $x$, so a tail of size $O(\sqrt N)$ can shift the popcount by an amount that is not $O(\log N)$ in general. **Certificate:** over $N\le2^{17}$ the maximal gap is $9$, attained at $N=490$ with $\ell(T_{490})=2$ (so $T_{490}\le3$) and $Z=8$. Gaps $\ge8$ occur at 22 values of $N$.
- (d) If $f_1(N)\to\alpha>0$, then $Z(N)=o(N)$, and so $\kappa_{\rm head}=K+o(N)$.

*Proof.* (a) Compare Theorem 1.2 with Phase 24's identity $S(N)=\sum_{n\le M}s_2(\tau(n))+s_2(T_N)-\kappa_{24}(N)$; here $s_2(\lfloor x\rfloor)=0$.

(b, c) Add $T<2^\ell$ to $A$ in binary. At most $\ell$ carries leave bits $0,\dots,\ell-1$. If no carry enters bit $\ell$, there are no further carries. A carry entering bit $\ell$ propagates exactly through the maximal run of ones of $A$ that starts there, and turns it into zeros of $A+T=\lfloor2^Nx\rfloor$. Bit $\ell+i$ of $\lfloor2^Nx\rfloor$ is $d_{N-\ell-i}$. Since $A+T<2^N$, the carry leaving that run lands at a bit below $N$. So the zeroed bits correspond to digits of positive index, and the run has length at most $Z(N)$ as defined in §0.

(d) The digits $d_{N-\ell-Z+1},\dots,d_{N-\ell}$ vanish. So $S(N-\ell)=S(N-\ell-Z)$, which forces $\alpha Z=o(N)$. ∎

**Theorem 1.5 (window approximation; Paper proof; Finite certificate).** Let $B=\max_{j\le N+W}c_j$; by Theorem 1.2, $B\le\max_{j\le N+W}\bigl(\frac32+\frac14\log_2j+\frac1{2j\ln2}\bigr)$. Suppose $2^\ell\ge B+1$ and $W>\ell$. Then

```math
0\le K(N)-K^{(W)}(N)\le\#\{1\le j<N:\ d_{j+1}=\dots=d_{j+W-\ell}=0\}=N\,F_N\bigl([0,2^{\ell-W})\bigr)+O(1).
```

Take $W=W(N)$ with $W(N)-\ell(N)\to\infty$, where $\ell(N)$ is the least $\ell$ with $2^\ell\ge B+1$; this $\ell(N)$ grows like $\log_2\log_2N$ at most, so $W$ must grow too. Then $K^{(W)}/N$ approximates $K/N$ to $o(1)$ whenever $\lim_{m\to\infty}\limsup_NF_N([0,2^{-m}))=0$. That is, no weak limit, on $[0,1]$, of the empirical measures of $(\{2^jx\})_{j<N}$ charges the point $0$. On $\mathbb R/\mathbb Z$ one would also have to exclude mass escaping to $1^-$, which does not affect $F_N([0,2^{-m}))$. The condition holds in particular if $E(4)$ is normal.

*Proof.* Lemma 1.1(e) for each $j$. ∎

*Certificate.* With $B=5$ and $\ell=3$, the script counts the $j$ with $c_j\ne c_j^{(W)}$ for $j<2^{17}-W$: $346$ for $W=4$, $5$ for $W=8$, and $0$ for $W=16$. Every error comes with the predicted zero window.

**Corollary 1.6 (simple-normality equivalences; Paper proof).** The following are equivalent:

- (i) $E(4)$ is simply normal in base 2;
- (ii) $K(N)/N\to\theta$;
- (iii) $K^J(N)/N\to\mu/2-1/2$;
- (iv) $\kappa_{24}(N)/N\to\theta$;
- (v) $\kappa_{\rm head}(N)/N\to\theta$ and $Z(N)=o(N)$.

Moreover $\limsup f_1=C_{\rm true}/2-\liminf K/N$ exactly. So $\limsup f_1<\frac12$ holds if and only if $\liminf K(N)/N>\theta\in[0.169551,0.169558]$.

*Proof.* (i)⇔(ii)⇔(iii) is Theorem 1.2, and (iv) follows from Theorem 1.4(a). For (v): (i) implies $Z=o(N)$ by Theorem 1.4(d), and then Theorem 1.4(b) applies. Conversely, (v) and Theorem 1.4(b) give (iv). ∎

## 2. A2: lower bounds, the locality barrier and the three-column criterion

**Theorem 2.1 (reset witnesses; Paper proof).**

- (a) $K(N)\ge K^{(W)}(N)$. If the columns are cut into blocks $[a,a+W)$ and the carry entering each block from the right is reset to $0$, the summed block carries are at most $K(N)$; averaging over offsets keeps this.
- (b) For any partition of $\{1,\dots,M\}$ into groups $G$, put $\kappa_G=\sum_{n\in G}s_2(\tau(n))-s_2\bigl(\sum_{n\in G}\tau(n)4^{\max G-n}\bigr)$. Then $\sum_G\kappa_G\le\kappa_{\rm head}(N)\le K(N)+O(\log^2N)$.

*Proof.* (a) Block carries are at most window carries, which are at most true carries, by Lemma 1.1(d)–(e).

(b) The many-summand Kummer count is additive along any addition tree: the carries of the total equal the sum of the group carries plus the carries of adding the group sums. Then apply Theorem 1.4. ∎

**Theorem 2.2 (stationarity bound; Paper proof).** For every $W\ge1$,

```math
\limsup_{N\to\infty}f_1(N;E(4),2)\ \le\ \limsup_{N\to\infty}\frac1N\sum_{j<N}\Bigl\{\frac{R_W(j)}{2^W}\Bigr\}+\frac{\mu}{2^{W+1}} .
```

The same holds for $E(2^k)$ with $\mu/k$ in place of $\mu/2$, and on any sequence of dyadic windows $[N,2N)$.

*Proof.* There are three steps.

(i) Digit $d_m$ contributes $1-2^{-m}$ to $\sum_{j<N}\{2^jx\}$ if $m\le N$, and less than $2^{N-m}$ otherwise. So $\frac1N\sum_{j<N}\{2^jx\}=f_1(N)+O(1/N)$.

(ii) Put $Y_s=\sum_{i>s}J_i2^{s-i}$. Then $\{2^jx\}=\{\sum_{i\le W}J_{j+i}2^{-i}+2^{-W}Y_{j+W}\}\le\{R_W(j)/2^W\}+2^{-W}Y_{j+W}$, since $\{a+t\}\le\{a\}+t$ for $t\ge0$.

(iii) $\frac1N\sum_{j<N}Y_{j+W}=\sum_{m\ge1}2^{-m}\frac1N\sum_{j<N}J_{j+W+m}\to\mu/2$, by the mean of $J$ (Theorem 1.2) and dominated convergence, using $\frac1N\sum_{j<N}J_{j+s}\le C(1+s)$. ∎

Step (i) is where shift invariance enters: every digit of the window has the same Cesàro frequency. In carry language, Theorem 2.2 is the identity $c^{(W)}_j(J)=\sum_{i\le W}J_{j+i}2^{-i}-\{R_W(j)/2^W\}$ averaged over $j$.

The criterion "the right-hand side is below $\frac12$" requires $\limsup\overline{\{R_W/2^W\}}<\frac12-\mu2^{-W-1}$. The second column gives a certified **sufficient** threshold $t_W$, the outward rounding (down) of $\frac12-\mu_{\rm hi}2^{-W-1}$, so any bound below $t_W$ suffices. The third column gives a certified interval for $\mathbb E_{Q_W^{(1/2)}}[R/2^W]$. Both are outward-rounded and asserted by the script.

| $W$ | sufficient: $\limsup\overline{\{R_W/2^W\}}<t_W$ | $\mathbb E_{Q_W^{(1/2)}}[R/2^W]$ (certified) | measured at $N=2^{17}$ (finite only) |
| --- | --- | --- | --- |
| 1 | $<-0.019082$ (impossible) | $[0.158029,0.158031]$ | $0.18930$ |
| 2 | $<0.240459$ | $[0.261075,0.261076]$ | $0.31604$ |
| 3 | $<0.370229$ | $[0.323108,0.323111]$ | $0.39399$ |
| 4 | $<0.435114$ | $[0.359675,0.359678]$ | $0.43903$ |

**Theorem 2.3 (locality barrier; Paper proof with External input EK2).** Assume EK2 (§7): for fixed $d$, $(\omega(n)-L,\ \omega(n+d)-L)/\sqrt L$ converges to a standard bivariate normal distribution for $n\le x$ uniform, where $L=\log\log x$.

- (a) For each fixed $d\ge1$ the collision set $\mathcal C_d=\{n:\tau(n)\mathbin{\&}\lfloor\tau(n+d)/4^d\rfloor\ne0\}$ has density 0. These are the $n$ for which $\tau(n)4^{-n}$ and $\tau(n+d)4^{-n-d}$ share a column.
- (b) For each fixed $D$, the group carries of Theorem 2.1(b) for groups of $D+1$ consecutive coefficients satisfy $\sum_G\kappa_G=o(N)$. Hence every *coefficient-local* witness, meaning one that uses the bits of at most $D+1$ consecutive coefficients and no incoming carry, yields only $\limsup f_1\le C_{\rm true}/2$, the Phase-24 bound.
- (c) Interpretation, not a theorem: any unconditional improvement of $\limsup f_1(E(4);2)\le C_{\rm true}/2$ must control $(v(n),v(n+d))$ at lattice resolution for unboundedly many shifts $d$. No present theorem does this.

*Proof.* (a) A collision means $v(n+d)=v(n)+2d+\beta-\beta'$ with $\beta\in B(o(n))$ and $\beta'\in B(o(n+d))$. Given $\varepsilon>0$, choose $T$ with the upper density of $\{o(n)>T\}$ below $\varepsilon$; then $\{o(n+d)>T\}$ also has upper density below $\varepsilon$. This is possible because $o(n)\le\tau(s(n))\le2\sqrt{s(n)}$ and the density of $\{s(n)>S\}$ is at most $\sum_{s>S\ \rm squarefull}1/s\to0$. Off the union $\{o(n)>T\}\cup\{o(n+d)>T\}$, which has upper density below $2\varepsilon$, both $\beta,\beta'<\log_2T$, so $|v(n+d)-v(n)-2d|\le\log_2T$. Next, $v(n)-\omega(n)=\sum_{p^2\mid n}(v_2(e_p+1)-1)$ is bounded in probability, so by EK2, $(v(n+d)-v(n))/\sqrt{2L}$ is asymptotically $N(0,1)$. A bounded window therefore has density $0$.

(b) Numbers with disjoint binary supports add without carries. So $\kappa_G=0$ unless two members of $G$ collide, and always $\kappa_G\le\sum_Gs_2(\tau)$. Thus $\sum_G\kappa_G\le\sum_{d\le D}\sum_{n\in\mathcal C_d,\,n\le M}\sum_{|m-n|\le D}s_2(\tau(m))=o(M)$, by (a) and uniform integrability. The latter holds because $s_2(\tau(m))\le g(m)$ (Phase 24 Cor 3.3) and $\sum_{m\le Y}g(m)\mathbf 1[s(m)>S]\le Y\sum_{s>S,\ s\ \rm squarefull}\tau(s)/s$. ∎

*The barrier is invisible to finite computation.* The fraction of $n$ in $\mathcal C_1$ is $0.2090$, $0.2117$ and $0.2111$ on $[2^9,2^{10})$, $[2^{12},2^{13})$ and $[2^{15},2^{16})$. The expected decay $\asymp(\log\log n)^{-1/2}$ is flat here, since $\log\log2^{16}\approx2.4$. The $D$-local carries per column at $N=2^{17}$ are $0.112$ ($D=1$), $0.149$ ($D=4$) and $0.172$ ($D=32$), against a true value of $0.174$. These are finite measurements only.

**Theorem 2.4 (three-column criterion; Conditional; Finite certificate).** For $\lambda>0$ let $H_W^{(\lambda)}$ be the hypothesis

```math
\limsup_{N}\frac1N\sum_{j<N}\Bigl\{\frac{R_W(j)}{2^W}\Bigr\}\le\mathbb E_{Q_W^{(\lambda)}}\Bigl[\frac R{2^W}\Bigr],
```

which is implied by weak convergence of the column-empirical law of $R_W(j)$ to $Q_W^{(\lambda)}$. For $E(4)$ we use $\lambda=\frac12$ and write $H_W=H_W^{(1/2)}$. Put $B_W=\mathbb E_{Q_W^{(1/2)}}[R/2^W]+\mu2^{-W-1}$. Then, with every interval outward-rounded from the exact certificate:

| $W$ | $B_W$ (certified) | consequence under $H_W$ |
| --- | --- | --- |
| 1 | $[0.677111,0.677112]$ | none |
| 2 | $[0.520615,0.520617]$ | none, since $B_2>\frac12$ |
| **3** | $[0.452879,0.452881]$ | $\limsup f_1\le0.452881$, so $D^-(E(4);2)\ge0.047119$ |
| 4 | $[0.424560,0.424563]$ | $\limsup f_1\le0.424563$, so $D^-(E(4);2)\ge0.075437$ |

Under $H_3$, then, **$E(4)$ is not simply normal in base 2**, nor in any base $2^j$ (Phase 24 Prop 2.4(5)). In carry language (Cor 1.6), $\liminf K(N)/N\ge C_{\rm true}/2-B_3\ge0.216670>\theta$, and $\liminf K^J/N\ge\mu/2-B_3\ge0.585282$, which exceeds $\mu/2-\frac12\in[0.538162,0.538164]$. This answers the brief's question of a carry density above the threshold, conditionally. Since $B_2>\frac12$, no hypothesis of type $H_2$ consistent with the comparison law can decide $E(4)$ through Theorem 2.2. Three columns is minimal for this route.

*Proof.* Theorem 2.2 with $W=3$ (respectively 4). ∎

*Certificate method.*

1. Bounds for $\mu$ (Theorem 2.6).
2. Lower-bound probabilities for $\nu$ modulo $2^8$, at scale $2^{-100}$ with rounding down. Primes $p\le3000$ are convolved exactly. Primes in $(3000,10^6]$ enter as one combined factor that allows no factor or a single factor 3, bounded below by the Weierstrass inequality. Primes $>10^6$ are charged $\sum_{n>10^6}n^{-2}$.
3. Poisson weights: $e^{-\lambda}$ is bounded below by the alternating series truncated after a negative term, for $k\le30$.
4. The law of $J\bmod2^W$, and then of $R_W$, by convolution with rounding down. The missing mass (at most $2.1\cdot10^{-6}$ for $E(4)$ and $8.1\cdot10^{-6}$ for $E(2)$, both asserted) is charged at the maximal value $1-2^{-W}$.
6. Decimal output by exact floor (lower endpoints) and ceiling (upper endpoints) of the `Fraction` bounds. The script asserts every endpoint quoted in this note.
5. Cross-check by a closed form. $U$ is odd, so $(-1)^J=(-1)^K$, and therefore $B_1=(1-e^{-1})/4+\mu/4$.

**Remark 2.5 ($E(2)$; Conditional; Finite certificate).** For $E(2)$ ($\lambda=1$, mean $\mu$) put $B_W^{(1)}=\mathbb E_{Q_W^{(1)}}[R/2^W]+\mu2^{-W}$. The same computation gives $B_7^{(1)}\in[0.502089,0.502097]$ and $B_8^{(1)}\in[0.497099,0.497108]$. So the 8-column hypothesis $H_8^{(1)}$, which uses $Q_8^{(1)}$ rather than the $E(4)$ law $Q_8^{(1/2)}$, implies $\limsup f_1(E(2);2)\le0.497108$, and then $E(2)$ is not simply normal.

CC-49 proves that witnesses built from the residue law $R_D\sim Q_D$ of $D$ columns plus the tail mean need $D\ge16$. Its $R_D(n)$ (`notes/phase17/erdos-borwein-bias.md`, opening section) is our $R_W(j)$. Consider CC-49's *distributional* 16-column hypothesis: the column-empirical law of $R_{16}$ converges to $Q_{16}=Q_{16}^{(1)}$. This is stronger than the single scalar inequality on $\Psi_{16}$. Since $R_8(n+8)\equiv R_{16}(n)\pmod{2^8}$, the image of $Q_{16}$ under reduction modulo $2^8$ is $Q_8^{(1)}$, and a shift by 8 columns does not change Cesàro averages. So the distributional hypothesis **implies** $H_8^{(1)}$. There is no contradiction. CC-49's countermodels specify the law of one window and control only its top digit. They violate the shift-invariance identity, step (i) of Theorem 2.2, which every actual digit sequence satisfies. The margins are measured differently: CC-49's certificate has margin $2.6\cdot10^{-4}$ in its statistic $\Psi_{16}$, and ours has $\frac12-B_8^{(1)}\ge2.89\cdot10^{-3}$ in $f_1$ (certified; the exact enclosure gives $\frac12-B_8^{(1)}\ge0.0028923$).

**Theorem 2.6 ($\mu$; Finite certificate).** $\mu\in[2.07632553,\,2.07632693]$. This is the outward rounding of the exact enclosure, whose width is at most $1.3843\cdot10^{-6}$.

*Method.* Each local factor $\sum_e\mathrm{odd}(e+1)(p-1)p^{-e-1}$ is computed for $p\le10^6$ at scale $2^{-100}$ with outward rounding. The truncation tail is at most $(e+2)p^{-e}$. For $p>10^6$ we use $1\le\ell(p)\le1+2p^{-2}+5p^{-3}$, and for primes $p\equiv\pm1\pmod6$ we bound $\sum_{p>P}p^{-2}\le\frac1{3(P-6)}$. The interval lies inside the certified enclosure $[2.0762592,2.0763285]$ of Phase 17 (CC-49, `notes/phase17/erdos-borwein-bias.md`) and is at least 50 times narrower; both facts are asserted. Phase 14 proved only $\mu\le5/2$.

**Unconditional status (2.7).** The sharpest unconditional statements remain $\limsup f_1(E(4);2)\le C_{\rm true}/2\le0.669558$ (Phase 24). Nothing nontrivial is known for $\liminf f_1$ or $D^-(E(4);2)$. This note does not improve either. Theorem 2.3 shows that coefficient-local arguments cannot, and Theorem 2.2 identifies the statistic that would suffice.

## 3. A3: base 4

**Lemma 3.1 (Paper proof; Finite certificate for $m<2^{16}$).** $s_4(m)+s_4(2m)=3s_2(m)$.

*Proof.* We have $s_4(m)=s_2(m)+\#\{\text{ones of }m\text{ at odd positions}\}$ and $s_4(2m)=s_2(m)+\#\{\text{ones at even positions}\}$. ∎

**Theorem 3.2 (parity equidistribution; Paper proof with External input: Wirsing).** Let $F$ be a function on odd integers with $\sum_{s\ \rm squarefull}|F(o(s))|/s<\infty$. Then $\frac1X\sum_{n\le X}(-1)^{v(n)}F(o(n))\to0$. Consequently:

- (a) The mean number of ones of $\tau(n)$ at even positions equals the mean at odd positions, namely $C_{\rm true}/2$. So the even and the odd columns of $E(4)$ each receive arrival density $C_{\rm true}/2$.
- (b) $\frac1X\sum_{n\le X}s_4(\tau(n))\to\frac32C_{\rm true}\in[2.008654,2.008674]$.
- (c) For $E^*(4)$, the even and odd columns each receive density $\frac12$, and the base-4 digit mass is $\frac32$ per position.

*Proof.* Write $n=st$ with $s$ squarefull, $t$ squarefree and $(s,t)=1$. Then $v(n)=v(s)+\omega(t)$ and $o(n)=o(s)$, so

```math
\sum_{n\le X}(-1)^{v(n)}F(o(n))=\sum_{s}(-1)^{v(s)}F(o(s))\sum_{t\le X/s,\ (t,s)=1}\mu(t).
```

By Wirsing's theorem applied to $\mu\cdot\mathbf 1_{(\cdot,s)=1}$ (value $-1$ at every $p\nmid s$, so $\sum_p(1-f(p))/p=\infty$), the inner sum is $o(X/s)$ for each $s$, and it is at most $X/s$ in absolute value. Dominated convergence finishes the proof.

(a) Use the exact identity $\#\mathrm{even}-\#\mathrm{odd}=(-1)^{v(n)}\varphi(o(n))$, where $\varphi(m)=\sum_i(-1)^im_i$ satisfies $|\varphi|\le s_2\le\tau$ (verified for $n\le2^{16}$).

(b) $s_4(2^vo)$ equals $s_4(o)$ if $v$ is even and $s_4(2o)$ if $v$ is odd. Apply Lemma 3.1 with $F=s_4(o)-s_4(2o)$.

(c) $(-1)^{\omega}$ is multiplicative with value $-1$ at prime powers, so Wirsing applies directly. ∎

**Theorem 3.3 (exact base-4 identities; Paper proof; Finite certificate; the asymptotic consequences with External input: Wirsing, via Theorem 3.2(a)).** Base-4 position $m$ consists of binary columns $2m-1$ and $2m$. Put $a_m=2r_{2m-1}+r_{2m}$. The true base-4 carries satisfy $C_m=\lfloor\sum_{m'>m}a_{m'}4^{m-m'}\rfloor=c_{2m}$ and $C_{m-1}=\lfloor(a_m+C_m)/4\rfloor$. With $E_M=\sum_{m\le M}c_{2m}$, $O_M=\sum_{m\le M}c_{2m-1}$, and $R_{\rm e},R_{\rm o},S_{\rm e},S_{\rm o}$ the arrival and digit totals over even and odd columns up to $2M$:

```math
S_{\rm e}-S_{\rm o}=(R_{\rm e}-R_{\rm o})+3(E_M-O_M)-2c_{2M},\qquad \sum_{m\le M}D_m=2R_{\rm o}+R_{\rm e}-3E_M+4c_{2M}.
```

Here $D_m$ is the base-4 digit. These two identities are exact and unconditional. Hence, using Theorem 3.2(a) (Wirsing), $f_{\rm even}-f_{\rm odd}=3(E_M-O_M)/M+o(1)$, and the mean base-4 digit is $\frac32C_{\rm true}-3E_M/M+o(1)$.

*Proof.* Sum Lemma 1.1(b) over even and over odd columns separately, and use $c_0=0$; this gives the exact identities. For the asymptotic consequences use Theorem 3.2(a), so $R_{\rm e}-R_{\rm o}=o(M)$ and $R_{\rm e},R_{\rm o}\sim\frac12C_{\rm true}M$. ∎

**Corollary 3.4 (inherits the Wirsing input of Theorem 3.3).** Simple normality of $E(4)$ in base 4 forces $E_M/M\to\theta$ **and** $O_M/M\to\theta$, whereas simple normality in base 2 constrains only the average. Every proof of $f_{\rm even}\ne f_{\rm odd}$ is a proof that the even-column and odd-column carry densities differ, which is a carry-correlation statement. Under base-4 simple normality the aligned XOR frequency $f_{01}+f_{10}$ (base-4 digits $\{1,2\}$) equals $\frac12$; nothing unconditional is known about it. Under $H_3$, base-4 simple nonnormality already follows from Theorem 2.4 by radix descent.

**Proposition 3.5 (the low-bit observation, corrected; Paper proof with External input: Wirsing, via Theorem 3.2(a); Finite certificate for the exact decomposition).** We have

```math
r_{2m}=\mathbf 1[m=\square]+\sum_{t\ge1}\mathrm{bit}_{2t}\bigl(\tau(m+t)\bigr),\qquad r_{2m-1}=\sum_{t\ge0}\mathrm{bit}_{2t+1}\bigl(\tau(m+t)\bigr),
```

verified for $m\le2^{16}$. The square term has density 0. By Theorem 3.2(a) both sums have asymptotic mean $C_{\rm true}/2$. Example: a squarefree $n$ has $\tau(n)=2^{\omega(n)}$ at column $2n-\omega(n)$, whose parity is that of $\omega(n)$. So there is **no** first-order deficit of low bits. The parity of $\tau$ at squares affects only a density-zero set of columns.

*Finite measurement.* At $N=2^{17}$, $f_{\rm even}=0.44836$ and $f_{\rm odd}=0.54144$. Theorem 3.3 explains this exactly: the arrivals are $0.66632$ and $0.67189$, the carries $0.15964$ and $0.18880$, and $-0.00557+3(-0.02916)=-0.0931$. The base-4 prefix law is $(0.2062,0.2524,0.3454,0.1960)$. The comparison law predicts even/odd symmetry and the law $(0.3569,0.2383,0.2383,0.1660)$ (§10). Neither is evidence.

## 4. A4: the unitary boundary $E^*(4)$

**Theorem 4.1 (Paper proof; Finite certificate; the final clause of (d) with External input: Wirsing, via Theorem 3.2(c)).**

- (a) $S^*(N)=R^*(N)-K^*(N)+c^*_N$ with $R^*(N)=N/2+O(\log N)$. Hence $f_1=\frac12-K^*(N)/N+O(\log N/N)$, and simple normality holds if and only if $K^*(N)=o(N)$.
- (b) $\#\{1\le j\le N:d^*_j\ne\mathbf 1_Q(j)\}\le2K^*(N)+\mathbf 1[c^*_N\ge1]\le2K^*(N)+c^*_N$.
- (c) $E^*(4)$ is normal in base 2 if and only if it is simply normal and $\mathbf 1_Q$ is a normal sequence. If it is simply normal, its digits and $\mathbf 1_Q$ have identical word frequencies.
- (d) $E^*(4)$ is simply normal in base 4 if and only if it is simply normal in base 2 and the four aligned patterns $(\mathbf 1_Q(2m-1),\mathbf 1_Q(2m))$ each have frequency $\frac14$. In particular $\#\{m\le M:2m-1,2m\in Q\}\sim M/4$. With Theorem 3.2(c), among the $n$ with $q(n)$ even, the conditional density of $q(n)-1\in Q$ must then be $\frac12$.
- (e) Every base-4 digit 3 comes from an adjacent pair $q(n')=q(n)-1$ or from a carry.

*Proof.* (a) Lemma 1.1, with one arrival per $n$.

(b) If $c^*_j=0$ and $r^*_j\le1$, then $c^*_{j-1}=0$ and $d^*_j=r^*_j=\mathbf 1[r^*_j\ge1]$. If $r^*_j\ge2$, then $c^*_{j-1}\ge1$. So a mismatch at $j$ forces $c^*_j\ge1$ or $c^*_{j-1}\ge1$. Now $\#\{1\le j\le N:c^*_j\ge1\}\le\sum_{j=1}^{N-1}c^*_j+\mathbf 1[c^*_N\ge1]=K^*(N)+\mathbf 1[c^*_N\ge1]$, and $\#\{0\le j<N:c^*_j\ge1\}\le c^*_0+K^*(N)=K^*(N)$.

(c) A density-zero modification preserves all word frequencies.

(d) For the forward direction use radix descent (Phase 24 Prop 2.4(5)) and then (b); the converse follows from (b). For the final clause: simple normality gives $K^*(N)=o(N)$ by (a). Since $c^*_{j-1}=\lfloor(r^*_j+c^*_j)/2\rfloor\ge\lfloor r^*_j/2\rfloor\ge\frac12(r^*_j-1)^+$, we get $\sum_{j\le N}(r^*_j-1)^+\le2\sum_{j\le N}c^*_{j-1}=2K^*(N)=o(N)$. So $n\mapsto q(n)$ is injective off $o(M)$ exceptions among $n$ with $q(n)\le2M$. Hence $\#\{m\le M:2m-1,2m\in Q\}=\#\{n:q(n)=2m\le2M,\ q(n)-1\in Q\}+o(M)$. By Theorem 3.2(c), $\#\{n:q(n)\text{ even},\ q(n)\le2M\}\sim M/2$, and $(M/4)/(M/2)=\frac12$.

(e) Digit 3 needs both bits of a base-4 position, and without a carry each bit is an arrival. ∎

*Certificate.* At $N=2^{17}$: $15679$ mismatches, below the bound $2K^*+c^*_N=15966$ (here $K^*=7983$ and $c^*_N=0$), and $3886$ digit-3 positions, of which $3834$ are pure adjacency and $52$ involve a carry.

**Theorem 4.2 (parity; Paper proof; External input for (c)).**

- (a) $q(n)\equiv\omega(n)\pmod2$. A collision at shift $d$ means $\omega(n+d)-\omega(n)=2d$, so $(-1)^{\omega(n)+\omega(n+d)}=+1$: every collision lies in the "equal sign" pattern at shift $d$.
- (b) Even and odd columns each carry density $\frac12$ (Theorem 3.2(c)).
- (c) Assuming EK2, each fixed-shift collision set has density 0. A positive-density collision set must therefore come from shifts $d\to\infty$, and in fact $d\le\frac12\omega(n+d)$.

*Certificate.* All $7709$ collision columns $q(n)$ from $n\le65{,}594$ have partners of equal $\omega$-parity. Of these, $7701$ have $q\le2^{17}$; the other 8 lie in the guard region.

**Theorem 4.3 (Conditional; Paper proof).** For a dyadic block $I=(x/2,x]$ put $L=\log\log x$, and suppose that for all large $x$:

- **LLB($c$):** $\#\{n\in I:\omega(n+d)-\omega(n)=2d\}\ge c|I|/\sqrt L$ for $1\le d\le\sqrt L$;
- **PUB($C$):** $\#\{n\in I:\omega(n+d)-\omega(n)=2d,\ \omega(n+d')-\omega(n)=2d'\}\le C|I|/L$ for $1\le d<d'\le\sqrt L$.

Then the collision set $\mathcal C=\{n:\exists n'>n,\ q(n')=q(n)\}$ has lower density at least $\delta_0=c^2/(2c+4C)$. So $E^*(4)$ is not simply normal in base 2, and $D^-(E^*(4);2)\ge\delta_0/4$ by Phase 24 Prop 10.2.

*Proof.* Let $Z(n)=\sum_{d\le\sqrt L}\mathbf 1[\omega(n+d)-\omega(n)=2d]$ on $I$. Then $\mathbb EZ\ge c/2$ and $\mathbb EZ^2\le\mathbb EZ+C$. Cauchy–Schwarz gives $\mathbb P(Z\ge1)\ge(\mathbb EZ)^2/(\mathbb EZ+C)\ge\delta_0$, since $t\mapsto t^2/(t+C)$ is increasing. Summing over dyadic blocks gives the lower density. ∎

*What blocks LLB.* LLB is a lattice-resolution local law for $\omega(n+d)-\omega(n)$, uniform in $d\asymp\sqrt L$. Through characteristic functions it needs $\mathbb E\,e^{i\vartheta(\omega(n+d)-\omega(n))}$ for all $\vartheta\in[-\pi,\pi]$. Its value at $\vartheta=\pi$ is the two-point correlation of $(-1)^\omega$ at shift $d$, a Chowla-type quantity. If the signs at $n$ and $n+d$ were anti-correlated on the relevant set, no collision would exist (Thm 4.2(a)). Fixed-shift sign-pattern theorems are known for the Liouville function (context only, not used: Matomäki–Radziwiłł–Tao, 2015). Uniformity in $d\asymp\sqrt{\log\log n}$ at local resolution is not available. PUB is a three-point sieve upper bound and is plausible, but it is not verified here. *Heuristic:* model $\omega(n),\omega(n+d),\omega(n+d')$ as independent Gaussians of mean and variance $L$. Then the increments $\omega(n+d)-\omega(n)$ and $\omega(n+d')-\omega(n)$ have covariance matrix $\begin{pmatrix}2L&L\\L&2L\end{pmatrix}$ with determinant $3L^2$; they are correlated through $\omega(n)$. In this model LLB holds with $c\approx e^{-1}/(2\sqrt\pi)$ and PUB with $C\approx1/(2\sqrt3\,\pi)$. In the comparison law the collision-column density is $1-\frac32e^{-1/2}\approx0.0902$.

## 5. A5: barriers and countermodels

**Theorem 5.1 (the proved column mean cannot decide; Finite certificate, exact).** Take i.i.d. bit-column models $r_j$ on $\{0,1,2\}$ with $\mathbb P=(1-\lambda+t,\ \lambda-2t,\ t)$. The stationary carry lies in $\{0,1\}$, with $\pi_1=t/(1-\lambda+2t)$, and $f_1=\lambda-t/(1-\lambda+2t)$. For both rational endpoints $\lambda=1339103/2\cdot10^6$ and $1339116/2\cdot10^6$ of $C_{\rm true}/2$:

- $t=0$ gives $f_1=\lambda>\frac12$;
- $t^*=(2\lambda-1)/4$ gives $f_1=\frac12$ exactly;
- $t=\lambda/2$ gives $f_1=\lambda/2<\frac12$.

All three models have the proved column mean and, being i.i.d., the proved even/odd split. At the threshold the collision density $\mathbb E\binom r2=t^*=(C_{\rm true}-1)/4$ is fine-tuned.

*Proof.* The carry moves from 0 to 1 with probability $t$ and stays at 1 with probability $\lambda-t$. Then $f_1=\mathbb Er-\mathbb Ec$, which is Lemma 1.1(b) in stationary expectation. The script solves the chains exactly in rationals. ∎

**Theorem 5.2 (two factorial moments cannot decide; exact).** Take $\lambda=1339103/2000000$ and $m_2=\lambda-\frac12$. The threshold law A of Theorem 5.1 and the law B on $\{0,1,2,3\}$ with $p_3=1/200$ have the same mass, mean and second factorial moment. Law A has $f_1=\frac12$, while law B has $f_1=92307439724609/179643056000000\in[0.513838,0.513839]$. For $s\in[0,\frac1{200}]$ let law $B_s$ have $p_3=s$, with $p_2,p_1,p_0$ fixed by the mass, mean and second-moment constraints. These are probability laws, being linear in $s$ and nonnegative at both ends, and $B_0$ is law A. On the carry space $\{0,1,2\}$ each chain is unichain: state $0$ is reachable from every state, since $r=0$ has positive probability. At $s=0$ state $2$ is transient, so the chain is not irreducible there. A unichain finite chain has a unique stationary law, which depends continuously on the transition matrix. Hence $f_1(B_s)$ is continuous in $s$, and every value between them is attained.

**Theorem 5.3 ($E^*(4)$ count models; exact).** For i.i.d. start counts $N_j$ with $\mathbb EN=\frac12$, $f_1=\frac12$ holds if and only if $\mathbb P(N\ge2)=0$.

*Proof.* If $\mathbb P(N\ge2)>0$, then $\pi(0)>0$, because runs of $N=0$ halve the carry. So $\pi(c\ge1)\ge\pi(0)\mathbb P(N\ge2)>0$, and $f_1=\frac12-\mathbb Ec<\frac12$. ∎

Exact examples: $(\frac58,\frac14,\frac18)$, $(\frac34,0,\frac14)$ and $(\frac{21}{36},\frac{13}{36},\frac1{36},\frac1{36})$. For $E^*(4)$ the obstruction is therefore *existence*, a lower bound for collisions. For $E(4)$ it is *precision*: the carry density must equal $\theta$ exactly.

**Barrier map (extends CC-49 and GF-28).**

| Information | Status | Decides $E(4)$? |
| --- | --- | --- |
| Column means $C_{\rm true}/2$ and $\mu/2$; even/odd split; mean of $s_4(\tau)$ | proved (Thms 1.2, 3.2) | no (Thm 5.1) |
| First two factorial moments of column counts | unknown | no (Thm 5.2) |
| Any coefficient-local statistic (fixed $D$) | proved asymptotically trivial (Thm 2.3) | no |
| Residue law of 2 consecutive columns $=Q_2$ | unknown | no ($B_2>\frac12$) |
| Residue law of 3 consecutive columns $=Q_3$ | unknown | **yes**, $\limsup f_1\le0.452881$ (Thm 2.4) |

## 6. Prior art and attribution

- Kummer's carry theorem (1852) and its many-summand form are classical. Phase 24 (Lemma 1.1, Thms 2.2 and 9.1) set up the truncated version. The closed form $c_j=\lfloor\sum_{i>j}a_i2^{j-i}\rfloor$ for an infinite column sum is elementary; we found no specific source and claim no novelty for it.
- The comparison law, i.e. compound-Poisson columns with mark law $\nu$, comes from Phases 14, 16 and 17 for $E(2)$ (CC-49, `notes/phase17/erdos-borwein-bias.md`). The Poisson heuristic for $E^*(4)$ is Phase 24 §10. The extensions here are the case $\lambda=\frac12$ for $E(4)$, the stationarity bound (Thm 2.2) and the window minimality.
- Irrationality of $E(2)$ is due to Erdős (1948) and of $\sum1/(q^n-1)$ to P. Borwein (1991). Neither is used.
- Wirsing's mean-value theorem (1967) is External input. The Erdős–Kac theorem (1940) and its bivariate form for shifted arguments are External input as in Phase 24 §10. The bivariate form goes back to LeVeque (*Trans. Amer. Math. Soc.* 66 (1949), 440–463); see also the method of moments in the Kubilius model in Elliott, *Probabilistic Number Theory II* (1980).
- Matomäki–Radziwiłł–Tao (2015) on sign patterns of $\lambda$ is cited for context only.

## 7. External inputs and hypotheses

| Input | Statement used | Where | Hypotheses checked |
| --- | --- | --- | --- |
| Wirsing (1967) | A real multiplicative $f$ with $\lvert f\rvert\le1$ and $\sum_p(1-f(p))/p=\infty$ has mean $0$ | Thm 3.2; via Thm 3.2: asymptotic parts of Thm 3.3 and Cor 3.4, Prop 3.5, final clause of Thm 4.1(d), Thm 4.2(b) | $f=\mu\mathbf 1_{(\cdot,s)=1}$ and $f=(-1)^\omega$: values $-1$ at all but finitely many primes ✓ |
| EK2 | For fixed $d$, $(\omega(n)-L,\omega(n+d)-L)/\sqrt L\Rightarrow N(0,I_2)$ | Thm 2.3, 4.2(c) | $d$ fixed ✓. Not re-derived here; Phase 24 §10 uses the same input |
| Phase 24 | $C_{\rm true}$ certificate, Lemmas 3.1–3.2, Cor 3.3, Prop 2.4(5), Prop 10.2 | throughout | proved there |
| $H_W^{(\lambda)}$ | Residue-window average bounded by the comparison law $Q_W^{(\lambda)}$ ($\lambda=\frac12$ for $E(4)$, $\lambda=1$ for $E(2)$) | Thm 2.4, Rem 2.5 | **Conditional**; open |
| LLB, PUB | Uniform local lower bound and pair upper bound at shifts $\le\sqrt L$ | Thm 4.3 | **Conditional**; open |

## 8. Exact finite tests and reproduction

Run `python -B scripts/phase25_e4_carries.py`. It needs Python $\ge3.10.7$ (for `int.bit_count` and `sys.set_int_max_str_digits`) and the standard library only. It takes about 10–15 s and exits with code 0, printing `ALL CHECKS PASSED: 2513921 exact checks (plus 3 floating-point sanity checks of the heuristic model)`. Exact checks (`check()`) use only integers and `Fraction`. The three floating-point sanity assertions on the §10 model use a separate counter (`float_sanity()`). It was run with CPython 3.13 on Windows; it is pure Python, so the Hail server, which AGENTS.md prescribes for Lean, LaTeX and `verify.sh`, is not needed.

| Script section | Exact tests |
| --- | --- |
| 1 | Closed form equals recursion, Kummer identity and value preservation for all $r\in\{0..3\}^L$, $L\le6$ (5460 vectors). Monotonicity, the window lemma and superadditivity on 300 pseudo-random instances. $\{a+t\}\le\{a\}+t$ in 2000 rational cases |
| 2 | $\lfloor2^{2^{17}}E(4)\rfloor$ with guard bits. The arrival bound and the a priori carry bound $B=5$, in exact integer form. Coalescence of the true carries. Every column equation; both digit identities for every $N\le2^{17}$. Thm 1.4(a, b) for every $N$, and the maximal gap of 9 at $N=490$ ($\ell=2$, $Z=8$; 22 values with gap $\ge8$). The window lemma for $W=4,8,16$ (error counts $346,5,0$) |
| 3 | Lemma 3.1 for $m<2^{16}$; Prop 3.5 for $m\le2^{16}$; base-4 carries $=c_{2m}$; Thm 3.3 identities; the parity identity for $n\le2^{16}$ |
| 4 | $E^*(4)$ prefix and carries; Thm 4.1(b) in the sharp form $2K^*+\mathbf 1[c^*_N\ge1]$, and (e); the parity of all collisions; the counts $15679$, $7709/7701$, $3886=3834+52$ |
| 5 | Thm 2.1 inequalities for $D\in\{0,\dots,32\}$ and $W\in\{2,\dots,32\}$, in integers; $\kappa_{\rm head}\le K-c_N+s_2(T_N)$ |
| 6 | Exact stationary laws: Thms 5.1–5.3, including the exact rational $f_1$ of law B |
| 7 | $\mu$ interval; $B_W$ intervals; the closed form of $B_1$; $B_3<\frac12<B_2$ for $E(4)$ and $B_8<\frac12<B_7$ for $E(2)$. Every decimal endpoint, threshold and margin quoted in §2 equals the exact floor or ceiling of the `Fraction` bound |

## 9. Finite measurements only ($N=2^{17}$; no asymptotic meaning)

| Quantity | $E(4)$ | $E^*(4)$ |
| --- | --- | --- |
| $f_1$ | 0.49490 | 0.43910 |
| carry density $K/N$ (bits) | 0.17421 (threshold $\theta\approx0.16955$) | 0.06091 (threshold 0) |
| $R(N)/N$; $\sum J/N$ | 0.66911 (limit 0.66956); 1.03032 (limit 1.03816) | — |
| $f_{\rm even}$, $f_{\rm odd}$ | 0.44836, 0.54144 | — |
| base-4 digits 0,1,2,3 | 0.2062, 0.2524, 0.3454, 0.1960 | digit 3: 0.0593 |
| $\overline{\{R_W/2^W\}}$, $W=1..4$ | 0.18930, 0.31604, 0.39399, 0.43903 | — |

## 10. Floating-point exploration (heuristic comparison law; not evidence)

The predicted limits are the stationary values under $\mathrm{CP}(\lambda,\nu)$ columns, computed with marks truncated at 127 and column counts at 320. Because of this truncation the model base-4 laws sum to slightly less than 1: $0.999$ for $E(2)$ and $0.9995$ for $E(4)$ at four decimals. The last column gives the window carries $c^{J,(W)}$ of the **mark** arrivals $J$, not the bit carries. For $E^*(4)$ and $E^*(8)$ the two coincide, because every mark is $1$. The bit-carry density of $E(4)$ in this model is the $0.2649$ quoted below.

| Constant ($\lambda$) | model $f_1$ | model base-4 law | $\mathbb Ec^{J,(W)}$ (mark carries) for $W=1,2,3,8$ |
| --- | --- | --- | --- |
| $E(2)$ (1) | 0.4925 (Phase 17: $p_*=0.49245$) | 0.254, 0.253, 0.253, 0.239 | 0.820, 1.214, 1.403, 1.576 |
| $E(4)$ ($\frac12$) | **0.4047** | **0.357, 0.238, 0.238, 0.166** | 0.360, 0.516, 0.584, 0.631 |
| $E(8)$ ($\frac13$) | 0.3213 | 0.473, 0.206, 0.206, 0.115 | 0.224, 0.314, 0.349, 0.370 |
| $E^*(4)$ ($\frac12$, $\nu=\delta_1$) | 0.3635 (Phase 24) | 0.396, 0.241, 0.241, 0.123 | 0.092, 0.122, 0.132, 0.137 |
| $E^*(8)$ ($\frac13$, $\nu=\delta_1$) | 0.2734 (Phase 24) | 0.523, 0.203, 0.203, 0.070 | 0.045, 0.056, 0.059, 0.060 |

Under the comparison law, the bit-carry density of $E(4)$ is about $0.66956-0.4047=0.2649$, far above $\theta=0.1696$. **The expected truth is therefore that $E(4)$ is not simply normal**, with margin about $0.095$, much larger than $E(2)$'s $0.0075$. The approach rate is presumably of order $(\log\log N)^{-1/2}$, which explains why the prefix value $0.4949$ is still near $\frac12$.

## 11. Open questions

1. Prove $H_3$ for $E(4)$, or any bound $\limsup_N\frac1N\sum_{j<N}\{R_3(j)/8\}<0.370229$; this certified threshold is at most $\frac12-\mu/16$. This statistic involves the parities and residues of the counts $\#\{n:2n-v(n)=j\}$ over three consecutive columns.
2. Improve $\limsup f_1(E(4);2)\le C_{\rm true}/2$ unconditionally, or prove $\liminf f_1(E(4);2)>0$ (equivalently a step towards $D^+<1$). By Theorem 2.3 this needs growing-shift information.
3. Prove LLB at shifts $d\asymp\sqrt{\log\log n}$, or any positive-density lower bound for $\{n:\exists d,\ \omega(n+d)-\omega(n)=2d\}$. Prove PUB by a sieve.
4. Are the even-column and odd-column carry densities of $E(4)$ asymptotically equal? (The comparison law says yes.)
5. Give a quantitative local version of EK2: is $\mathrm{dens}(\mathcal C_1\cap[x,2x])\asymp(\log\log x)^{-1/2}$?
6. Find the minimal factorial-moment order (CC-49 style) that suffices on 3 or 4 columns for $E(4)$.
7. Formalize Lemma 1.1, Theorem 1.2, Theorem 1.4(b) and Theorem 2.2 in Lean. All are finite combinatorics plus one averaging step.
8. Register Remark 2.5, the 8-column criterion for $E(2)$, as a strengthening of CC-49's conditional criterion.

## 12. Standing objectives advanced

- **Objective 1 (normality):** exact equivalences for simple normality and normality of $E(4)$ and $E^*(4)$ (Cor 1.6, Thms 3.3, 4.1).
- **Objective 2 (nonnormality):** conditional simple nonnormality of $E(4)$ from 3 columns and of $E(2)$ from 8 columns (Thm 2.4, Rem 2.5), and the conditional theorem for $E^*(4)$ (Thm 4.3).
- **Objective 3 (quantification):** $\mu$ to 50 times higher precision; the exact base-4 laws $3C_{\rm true}/2$ and the even/odd split; certified $B_W$; the conditional $D^-$ bounds.
- **Objective 4 (limitations):** the tail-chain analysis (Thm 1.4), the locality barrier (Thm 2.3), the moment and window countermodels (Thms 5.1–5.3, $B_2>\frac12$), and the refutation of the low-bit asymmetry (Prop 3.5).

## 13. Proposed registry text (not edited here)

> **Phase 25 Track A — carry correlations for $E(4)$ and $E^*(4)$.** (1) The exact identity $f_1(E(4);2)=C_{\rm true}/2-K(N)/N+o(1)$ with true infinite-tail carries. Phase 24's $\kappa$ equals $K+O(\log^2N)$. The head-only count misses a zero-run-length chain, with a certified gap of 9 at $N=490$. (2) The stationarity bound $\limsup f_1\le\limsup\overline{\{R_W/2^W\}}+\mu2^{-W-1}$. Under the 3-column residue hypothesis $H_3$, $E(4)$ is not simply normal, with $\limsup f_1\le0.452881$; $W=2$ provably cannot suffice. For $E(2)$, 8 columns suffice: under $H_8^{(1)}$, $B_8^{(1)}\le0.497108$. This hypothesis is implied by CC-49's distributional 16-column hypothesis. (3) Locality barrier: coefficient-local carry witnesses have density 0 (bivariate Erdős–Kac). (4) Base 4: $s_4(m)+s_4(2m)=3s_2(m)$, mean $s_4(\tau)=\frac32C_{\rm true}$, equal even/odd arrivals (Wirsing), and $f_{\rm e}-f_{\rm o}=3(E_M-O_M)/M+o(1)$, where $E_M$ and $O_M$ are the even- and odd-column carry totals. (5) $E^*(4)$: normal if and only if simply normal and $\mathbf 1_{\{2n-\omega(n)\}}$ is normal; a conditional second-moment criterion. (6) $\mu\in[2.07632553,2.07632693]$ (outward-rounded). Evidence: Paper proofs; Finite certificates in `scripts/phase25_e4_carries.py`; External inputs Wirsing and bivariate Erdős–Kac; Conditional $H_W$, LLB and PUB.
