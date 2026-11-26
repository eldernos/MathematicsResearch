# Classical constants: the $2^k$ decomposition of $E_{\rm odd}$, the $E$–$E_{\rm odd}$–$E(b^2)$ triangle, and logarithm synthesis

Phase 21, Tracks E1–E3. Notation follows [character-q-digamma.md](character-q-digamma.md): $D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $0\le n<N$; $K_b=\{z:D_N(z;b)\to1\}$; $F_b(a)=\sum_{n\ge1}a(n)b^{-n}$; $S_a$ and $A_a$ are the support count and absolute mass. For the Erdős–Borwein family write

```math
E(b)=\sum_{m\ge1}\frac1{b^m-1}=\sum_{n\ge1}\tau(n)b^{-n},\qquad
E_{\rm odd}(b)=\sum_{m\ \rm odd}\frac1{b^m-1}=\sum_{n\ge1}\tau_{\rm odd}(n)b^{-n},
```

and $E_{\rm even}(b)=E(b^2)$. In base 2 we drop $b$. For $k\ge2$ and odd $r$, let $A_{r,2^k}=\sum_{m\equiv r\,(2^k)}1/(2^m-1)$, $\tau_{r,2^k}(n)=\#\{d\mid n:d\equiv r\ (2^k)\}$ and

```math
a_{k,r}(n)=2^{k-1}\tau_{r,2^k}(n)-\tau_{\rm odd}(n),\qquad Z_{k,r}=2^{k-1}A_{r,2^k}-E_{\rm odd}=F_2(a_{k,r}).
```

**Summary of conclusions.**

| Result | Evidence |
| --- | --- |
| E1. For each fixed $k$, all $2^{k-1}$ classes $A_{r,2^k}$ share $D^\pm$ and limit sets with $E_{\rm odd}$ in base 2 (Track B2, Theorem 2.3) | Paper proof |
| E1. $A_{2^k-1,2^k}$ is trivially concentrated only on $N<2^k$: $1-D_N\le2^{N-2^k}(1+2^{3-2^k})$; the brief's "$1-O(N/2^{2^k})$" is corrected to this (Lemma 1.1) | Paper proof; exact check |
| E1. **Complementary supports**: every $n$ lies in $\operatorname{supp}\tau_{r,2^k}\cup\operatorname{supp}a_{k,r}$, so no raw-support argument certifies both pieces; for every growth rate $k(N)$ the derived lower bound for $D_N(E_{\rm odd})$ is $\le0$ (Theorem 1.2, Corollary 1.3) | Paper proof; exact check to $2\cdot10^5$ |
| E1. For $k-1\ge\alpha\ln\ln N$ ($\alpha>1$), $\operatorname{supp}a_{k,r}$ has density $1-O((\ln N)^{-Q(\alpha)})$ in $[1,N]$ (Proposition 1.5) | Paper proof (Shiu) |
| E1. A nontrivial transfer bound needs $k\lesssim\log_2\ln\ln N$, and there $A_{r,2^k}$ has support density $\to1$; the sufficient condition $2^k\gg\ln N$ for certified concentration of $A_{r,2^k}$ lies where $Z_{k,r}$ is dense (Proposition 1.6) | Paper proof, part under hypothesis (U) |
| E2. The only constraints implied by $E(b)=E_{\rm odd}(b)+E(b^2)$ are the pseudometric triangle inequalities (sharp by OP-01) | Paper proof |
| E2. $1-D_N(x;b^k)\le k\,(1-D_{kN}(x;b))$, so $K_b\subsetneq K_{b^k}$; hence $E(b)\equiv E_{\rm odd}(b)\pmod{K_b}$ would force $E(b^2)\in K_{b^2}$ (Propositions 2.2–2.3) | Paper proof; finite check |
| E2. Dyadic truncation: $\lvert D_N(E)-D_N(E-E(2^{2^I}))\rvert\ll2^{-I}(I+\log\log N)$ (Proposition 2.4) | Paper proof; finite data |
| E3. Kernel decompositions are equivalences; splitting off a normal Stoneham number leaves a remainder $Z_c$ with the same top-band prime denominators (OP-11 applies verbatim) | Paper proof; exact check |
| E3. Every $q$-generic identity for $-\log(1-q)$ has chronological prefixes equal to the Taylor prefixes (Lemma 3.3) | Paper proof |
| E3. $\ln2,\pi,e,\sqrt2,\varphi,E$ (and $E_{\rm odd}$, $E_{\rm even}$) | **Open.** No new unconditional digit estimate |

## 1. E1 — the $2^k$ decomposition of $E_{\rm odd}$

### 1.1 The fixed-$k$ theorem

Track B2 (Theorem 2.3 of [character-q-digamma.md](character-q-digamma.md#23-kernel-membership-and-the-binary-transfer)) gives, for every $k\ge2$, odd $r$ and $N\ge1$,

```math
\bigl|D_N(A_{r,2^k})-D_N(E_{\rm odd})\bigr|\le\frac{k-1}N+\delta_{k,r}(N),\qquad
\delta_{k,r}(N)=1-D_N(Z_{k,r})\ll_k\frac{\log\log N}{(\log N)^{1/H_k}},
```

with $H_2=H_3=2$ and $H_k=2^{k-2}$. For each fixed $k$ the $2^{k-1}$ classes and $E_{\rm odd}$ therefore have the same $D^-$, the same $D^+$ and the same limit set. This is an equivalence. It transfers whatever holds for one member to the others, and it decides nothing.

### 1.2 What a growing $k$ would need

The classes become tiny as $r$ grows: $A_{r,2^k}=1/(2^r-1)+O(2^{-r-2^k})$. A lower bound for $D_N(E_{\rm odd})$ could come from $D_N(E_{\rm odd})\ge D_N(A_{r,2^k})-(k-1)/N-\delta_{k,r}(N)$ if some $A_{r,2^k}$ were provably concentrated while $\delta_{k,r}(N)$ was provably small.

**Lemma 1.1 (trivial concentration).** For $k\ge2$ and $1\le N\le2^k$,

```math
1-D_N(A_{2^k-1,2^k})\le2^{N-2^k}\bigl(1+2^{3-2^k}\bigr).
```

*Proof.* $A=\sum_{j\ge1}1/(2^{j2^k-1}-1)\le2^{1-2^k}(1+2^{3-2^k})$. For $N<2^k$ all $N$ points $2^nA$, $n<N$, lie in $[0,2^{N-1}A]\subset[0,1)$, and an interval containing all of them has length at most $2^{N-1}A$. For $N=2^k$ the right side exceeds 1. ∎

This corrects the brief's guess $1-O(N/2^{2^k})$: the deficit is $2^{N-2^k}$. It is exponentially small for $N\le2^k-\omega(1)$ and gives nothing once $N\ge2^k$. Beyond that range the support of $\tau_{r,2^k}$ in $[1,N]$ has density

```math
\sigma_N(r,k)\le\frac1r+\frac{1+\ln N}{2^k},
```

so Phase 20's sparse transfer certifies concentration of $A_{r,2^k}$ once $2^k\gg\ln N\cdot\log\log N$ and $r\gg1$, that is for $k\ge\log_2\ln N+O(\log\log\log N)\approx1.4427\ln\ln N$. This is a sufficient condition. The true threshold for sparse support of $\tau_{r,2^k}$ is presumably near $2^k\approx(\ln N)^{\ln2}$, the typical size of $\tau_{\rm odd}(n)$, that is $k\approx\ln\ln N$. That is exactly where Proposition 1.5 below makes $Z_{k,r}$ dense. The script shows the decay: $1-D_N(A_{127,128})$ is $0.000$, $0.055$, $0.070$, $0.106$ at $N=64,128,512,2048$.

### 1.3 The complementary-support barrier

**Theorem 1.2.** For every $k\ge2$ and every odd $r$, every $n\ge1$ lies in $\operatorname{supp}\tau_{r,2^k}\cup\operatorname{supp}a_{k,r}$.

*Proof.* If $\tau_{r,2^k}(n)=0$, then $a_{k,r}(n)=-\tau_{\rm odd}(n)\le-1$, because $1$ is an odd divisor. ∎

Two consequences follow:

1. No shift $n$ can be raw-certified for both pieces. A raw certificate is a support-free window $(n,n+L]$ with $L\ge1$ (Lemma 1.1 of the Phase 20 [coefficient-transfer note](../phase20/coefficient-transfer.md#11-integral-head-shadows-and-the-exact-mean-tail)), and $n+1$ lies in one of the two supports.
2. $S_{\tau_r}(N-1)+S_{a_{k,r}}(N-1)\ge N-1$ for every $N$.

**Corollary 1.3 (no growth rate helps).** Work in base 2. Let $U_A(N)$ and $U_Z(N)$ be upper bounds for $1-D_N(A_{r,2^k})$ and $1-D_N(Z_{k,r})$ produced by any of Theorems 1.4, 1.5 or 1.7 of the Phase 20 coefficient-transfer note, or by the kernel-checked `CoefficientTransfer.finite_sparse_mass_transfer`. Then for every $N$, every $k=k(N)\ge2$ and every odd $r=r(N)$,

```math
1-U_A(N)-\frac{k-1}N-U_Z(N)\le\frac{2-k}N\le0 .
```

So the lower bound $D_N(E_{\rm odd})\ge D_N(A_{r,2^k})-(k-1)/N-\delta_{k,r}(N)$, with both unknown quantities estimated by raw-support bounds, never yields $D^-(E_{\rm odd})>0$, however $k(N)$ is chosen.

*Proof.* Each listed bound is at least $S(N-1)/N$ for its sequence:

- Theorem 1.4 with $L\ge1$ contains $L(1+S(N-1))/N$.
- Theorem 1.4 with $L=0$ is at least $2\sqrt{2\widehat A(N)/N}\ge2\sqrt{S(N)/N}\ge S(N)/N$ in base 2, by AM–GM and $\widehat A\ge A/2\ge S/2$.
- Theorems 1.5 and 1.7 are at least $3\rho_N$.
- The Lean bound contains $L\,S(N+L)/N$ for $L\ge1$, and for $L=0$ it is at least $2\sqrt{2C}\ge S(N)/N$ since $C\ge A(N)/N$.

Then use consequence 2. ∎

**Scope.** The corollary concerns *raw* supports. Phase 20's displaced (valuation-aware) Theorem 2.2 counts effective sources $t(m)=m-v_2(a(m))$ instead and is not covered. Heuristically it does not help. For $n$ with squarefree odd part, $\tau_{\rm odd}(n)=2^{\omega_{\rm odd}(n)}$ is a power of 2, so in base 2 one has $E_{\rm odd}\approx\sum_n2^{-(n-\omega_{\rm odd}(n))}$: unit sources at the displaced positions $n-\omega_{\rm odd}(n)$, whose multiplicities have mean 1, a dense displaced support. We do not prove a displaced version.

The same argument shows more generally: if $c\,a_x=a_y+a_z$ coefficientwise and $a_x$ never vanishes (as for $\tau$ or $\tau_{\rm odd}$), then $\operatorname{supp}a_y\cup\operatorname{supp}a_z=\mathbb Z_{\ge1}$. Aligned integer decompositions of the Erdős–Borwein constants always have complementary supports.

### 1.4 The support of $a_{k,r}$ becomes dense

**Proposition 1.5.** Let $\alpha>1$ and $Q(\alpha)=\alpha\ln\alpha-\alpha+1>0$. If $k-1\ge\alpha\ln\ln N$, then

```math
N-S_{a_{k,r}}(N)\ll_\alpha N(\ln N)^{-Q(\alpha)} .
```

*Proof.* A zero of $a_{k,r}$ needs $\tau_{r,2^k}(n)\ge1$ and then $\tau(n)\ge\tau_{\rm odd}(n)=2^{k-1}\tau_{r,2^k}(n)\ge2^{k-1}$. With $s=\log_2\alpha>0$, Markov's inequality and Shiu's theorem for the multiplicative function $\tau^s$ (where $\tau(p^e)^s\le A^e$ and $\tau^s\ll n^\varepsilon$) give

```math
\#\{n\le N:\tau(n)\ge2^{k-1}\}\le2^{-s(k-1)}\sum_{n\le N}\tau(n)^s\ll N(\ln N)^{2^s-1}(\ln N)^{-\alpha s\ln2}=N(\ln N)^{\alpha-1-\alpha\ln\alpha}.
```

∎

The concentration range of §1.2, $k\ge\log_2\ln N+1$, has $k-1\ge(\ln\ln N)/\ln2$, i.e., $\alpha=1/\ln2$ and $Q=0.0861$ (and for $k\ge\log_2\ln N$ the $-1$ offset changes the bound only by the constant factor $\alpha$). So it lies inside the range where $\operatorname{supp}a_{k,r}$ has density tending to 1. This statement is about the true supports, not about upper bounds for them.

### 1.5 The quantitative trade-off

**Proposition 1.6.**

1. For fixed $k$, $\delta_{k,r}(N)\ll_k(\log\log N)/(\log N)^{1/H_k}$. The dependence on $k$ is explicit in Proposition 2.4 of the B note: $k-2$ support sets independent of $k$, the exponent $2^{-(k-2)}$, and an additive $k\log_22$. There is no factor $2^{k-1}$ from the character count.
2. Under the uniformity hypothesis (U) of the B note, $\delta_{k,r}(N)\ll k(\log N)^{-2^{2-k}}(k+\log_2\log N)$. This is below 1 only for $k\le\log_2\ln\ln N-\log_2\ln\ln\ln N+O(1)$. In that range Theorem 1.2 forces $\sigma_N(r,k)\ge1-S_{a_{k,r}}(N)/N\to1$, so every raw certificate for $A_{r,2^k}$ is vacuous.
3. Conversely, the sufficient condition of §1.2 for certified concentration of $A_{r,2^k}$, namely $2^k\gg\ln N$, lies inside the range of Proposition 1.5, where $Z_{k,r}$ is dense. For every $k$, Theorem 1.2 already excludes certifying both pieces at once.

Model thresholds, the largest $k$ with $k(\log N)^{-2^{2-k}}(k+\log_2\log N)<1$ (unit constants):

| $\ln\ln N$ | 5 | 10 | 20 | 50 | 100 | 1000 | 10000 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $k^*$ | 2 | 3 | 4 | 5 | 5 | 8 | 11 |
| $\log_2\ln\ln N-\log_2\ln\ln\ln N$ | 1.64 | 2.12 | 2.74 | 3.68 | 4.44 | 7.18 | 10.08 |

Even at $\ln\ln N=10^4$ only $k\le11$ gives a nontrivial transfer, while concentration of $A_{r,2^k}$ would need $2^k\gtrsim\ln N=e^{10^4}$.

### 1.6 The upper side, and the order of limits

Sparse-support methods only bound $1-D_N$ from above, that is, they prove concentration. A bound $D^+(E_{\rm odd})<1$ through the decomposition would need an anti-concentration estimate $D_N(A_{r,2^k})\le1-c-\delta_{k,r}(N)$ for some member of the family. For fixed $k$ that is equivalent to the same estimate for $E_{\rm odd}$ (§1.1). For growing $k$ it would be a new equidistribution theorem for a Lambert series with dense coefficients. No such estimate is known for any member, and the decomposition cannot create one.

**Limits.** For each fixed $k$, $\lim_N|D_N(A_{r,2^k})-D_N(E_{\rm odd})|=0$. For each fixed $N$, $\lim_{k\to\infty}D_N(A_{2^k-1,2^k})=1$ by Lemma 1.1; at $N=50$ the script finds $0.3127$, $0.6663$, $0.8888$, $0.9999$, $1.0000$ for $k=3,\dots,7$. If the first convergence were uniform in $k$, $E_{\rm odd}\in K_2$ would follow. That is not known, and $E_{\rm odd}$ is expected to be normal. The two limits are never interchanged in this note.

### 1.7 Finite data

Base 2, $N=2\cdot10^5$, exact:

| $k$ | $r$ | $S_{a_{k,r}}(N)/N$ | $S_{\tau_r}(N)/N$ | sum |
| --- | --- | --- | --- | --- |
| 2 | 3 | 0.2323 | 0.8070 | 1.0392 |
| 3 | 7 | 0.5524 | 0.6233 | 1.1758 |
| 4 | 15 | 0.8684 | 0.4118 | 1.2802 |
| 5 | 31 | 0.9755 | 0.2395 | 1.2150 |
| 6 | 63 | 0.9980 | 0.1203 | 1.1184 |
| 8 | 255 | 1.0000 | 0.0265 | 1.0265 |
| 12 | 4095 | 1.0000 | 0.0010 | 1.0010 |

For $r=1$ the second column is 1, since every $n$ has the divisor 1. Every $n\le2\cdot10^5$ lies in one of the two supports, and every zero of $a_{k,r}$ has $\tau_{\rm odd}(n)\ge2^{k-1}$, for all listed $(k,r)$, $k\le12$. The sparse regime of $Z_{k,r}$ (small $k$) and the sparse regime of $A_{r,2^k}$ (large $k$) are visibly complementary.

## 2. E2 — $E(b)$, $E_{\rm odd}(b)$ and $E(b^2)$

### 2.1 Identities

```math
E(b)=E_{\rm odd}(b)+E(b^2),\qquad E(b)=\sum_{i\ge0}E_{\rm odd}\bigl(b^{2^i}\bigr),\qquad
E_{\rm odd}(b)=\sum_{n\ge1}\tau_{\rm odd}(n)b^{-n}=\sum_{j\ge1}\frac{b^j}{b^{2j}-1}.
```

Coefficientwise, $\tau(m)=\tau_{\rm odd}(m)+[2\mid m]\,\tau(m/2)$ and $\tau(m)=\sum_{2^i\mid m}\tau_{\rm odd}(m/2^i)$, since the divisors with $v_2=i$ are $2^i$ times the odd divisors of $m/2^i$. The last formula for $E_{\rm odd}$ is Lambert duality, $\sum_{m\ \rm odd}\sum_jq^{mj}=\sum_jq^j/(1-q^{2j})$. The script checks the coefficient identities for $m\le10^5$ and the real identities to 50 digits for $b=2,3,10$.

### 2.2 Constraints from addition

**Proposition 2.1.** Let $u_N=1-D_N(E(b);b)$, $v_N=1-D_N(E_{\rm odd}(b);b)$ and $w_N=1-D_N(E(b^2);b)$. Then for every $N$,

```math
u_N\le v_N+w_N,\qquad v_N\le u_N+w_N,\qquad w_N\le u_N+v_N .
```

Consequently, for every labelling $(x,y,z)$ of the three numbers:

- $D^-(x)\ge D^-(y)+D^-(z)-1$;
- $D^+(x)\ge D^+(y)+D^-(z)-1$;
- $D^+(x)\le1-\liminf_N|D_N(y)-D_N(z)|$.

No further constraint follows from the identity alone.

*Proof.* $d_N(s,t)=1-D_N(s-t)$ is a pseudometric (Phase 19; its triangle inequality is the sharp translation bound), $D_N(-s)=D_N(s)$, and the three numbers are $0$, $E_{\rm odd}$, $E$ with differences $E_{\rm odd}$, $E(b^2)$, $E$. By the exact addition spectrum [OP-01](../phase19/addition.md), every triple $(\alpha,\beta,\gamma)$ with $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$ is realized by some $(x,y,x+y)$. So any additional constraint must use arithmetic input about these specific numbers. ∎

If one of the three numbers is normal, the constraints reduce to $D_N(y)+D_N(z)\le1+o(1)$ for the other two. If two are normal, they say nothing about the third. The finite values at $N=500,1000,2000,4000$ are $D_N(E)=0.0517,0.0332,0.0338,0.0353$, $D_N(E_{\rm odd})=0.1072,0.1088,0.1147,0.1049$ and $D_N(E(4))=0.0739,0.0694,0.0638,0.0634$; they satisfy the inequalities, as they must.

### 2.3 Changing the radix

**Proposition 2.2.** For every real $x$ and all integers $b\ge2$, $k\ge1$, $N\ge1$,

```math
1-D_N(x;b^k)\le k\,\bigl(1-D_{kN}(x;b)\bigr).
```

Hence $K_b\subseteq K_{b^k}$, and for every $k\ge2$ the inclusion is strict: $1/(b^k-1)\in K_{b^k}\setminus K_b$ (and for $k=2$, also $1/(b+1)\in K_{b^2}\setminus K_b$).

*Proof.* The empirical measure of $\{b^mx\}$, $m<kN$, is $\mu=\frac1k\sum_{j<k}\mu_j$, where $\mu_j$ is the empirical measure of $\{(b^k)^n(b^jx)\}$, $n<N$. For a half-open circle arc $I$, $\mu_0(I)\ge k\mu(I)-(k-1)$, so $\mu_0(I)-|I|\ge k(\mu(I)-|I|)-(k-1)$. Take the supremum over arcs and use $D_N=\sup_I(\mu_N(I)-|I|)$, the arc form behind Lean `arc_le` and `interval_eq_arc_excess`. (Equivalently, `ClassicalBarriers.one_sub_radixDiscrepancy_pow_le` proves this directly on intervals in Lean 4.) For strictness when $k\ge2$, $x=1/(b^k-1)$ is fixed by multiplication by $b^k$ modulo 1 (so $D_N(x;b^k)=1$ and $x\in K_{b^k}$), whereas its base-$b$ orbit cycles periodically through the $k\ge2$ distinct points $\{b^j/(b^k-1):0\le j<k\}$, keeping $\limsup_N D_N(x;b)<1$ so $x\notin K_b$. For $k=2$, $1/(b+1)$ is likewise fixed modulo 1 by $b^2$ while multiplication by $b$ swaps it with $b/(b+1)$, giving $D_N(1/(b+1);b)=\max\bigl(\frac{2}{b+1},\frac{b-1}{b+1}\bigr)<1$ for even $N$ (equal to $2/3$ at $b=2$ and $(b-1)/(b+1)$ for $b\ge3$). ∎

**Proposition 2.3.** If $E(b)-E_{\rm odd}(b)\in K_b$, then $E(b^2)\in K_{b^2}$.

*Proof.* $E(b)-E_{\rm odd}(b)=E(b^2)$; apply Proposition 2.2 with $k=2$. ∎

So relating $E$ and $E_{\rm odd}$ modulo $K_b$ is at least as hard as a kernel-membership question for the Erdős–Borwein constant $E(B)$ in its own radix $B=b^2$. That statement is expected to be false, since $E(B)$ is expected to be normal in base $B$. In base $b$, the coefficient sequence of $E(b^2)$ vanishes at odd positions but has support density $1/2$, so the sparse method does not apply. The script confirms Proposition 2.2 for $x=E,E_{\rm odd},L_{\chi_4}$ with $b=2$, $k=2$, $N=250,\dots,2000$.

### 2.4 Dyadic truncation of the divisor function

**Proposition 2.4.** For $I\ge1$ let $E^{(I)}(b)=E(b)-E(b^{2^I})=\sum_{i<I}E_{\rm odd}(b^{2^i})=\sum_n\#\{d\mid n:v_2(d)<I\}\,b^{-n}$. Then

```math
\bigl|D_N(E(b))-D_N(E^{(I)}(b))\bigr|\le1-D_N\bigl(E(b^{2^I})\bigr)\le\rho_I\Bigl(2\min(I\log_b2,\log_b N)+\log_b\bigl(\log(4N)+1\bigr)+4\Bigr),\qquad\rho_I\le2^{-I}+\frac1N .
```

In particular, for every sequence $I=I(N)\ge1$ with $2^{-I(N)}\log\log N\to0$, we have $D_N(E(b))-D_N(E^{(I(N))}(b))\to0$.

*Proof.* In base $b$, $E(b^{2^I})$ has coefficient $\tau(n)$ at position $2^In$ and zero elsewhere. Its support count up to $N-1$ is $\lfloor (N-1)/2^I\rfloor$, so $\rho=(1+\lfloor(N-1)/2^I\rfloor)/N$ satisfies $\max(2^{-I},1/N)\le\rho\le 2^{-I}+1/N$, whence $\log_b(1/\rho)\le\min(I\log_b2,\log_b N)$. Its mass is at most $(N/2^I)(\log N+1)$. Apply sharp translation and Theorem 1.7 of the coefficient-transfer note. ∎

The deep dyadic layers of the divisor function are negligible in discrepancy, but the main part $E^{(I)}$ is a sum of $I$ numbers of the same unknown type. The script finds $|D_{2000}(E)-D_{2000}(E^{(I)})|=0.081,0.061,0.024,0.0075,0.0019,0.0060$ for $I=1,\dots,6$, against the true deficits $1-D_{2000}(E(2^{2^I}))=0.936,0.723,0.460,0.292,0.174,0.102$.

### 2.5 What remains open

- The digit statistics of $E(b)$, $E_{\rm odd}(b)$, $E(b^2)$ in any radix: $D^\pm$, normality, and even membership or non-membership in $K_b$.
- Whether $E(b^2)\in K_b$, equivalently whether $E\equiv E_{\rm odd}\pmod{K_b}$. Proposition 2.3 shows this is at least as hard as $E(b^2)\in K_{b^2}$.
- Any constraint between the three numbers beyond Proposition 2.1.

## 3. E3 — logarithm synthesis

### 3.1 Kernel decompositions are equivalences

**Proposition 3.1.** If $x-y\in K_b$, then $D^\pm(x)=D^\pm(y)$ and $(D_N(x))$, $(D_N(y))$ have the same limit points.

*Proof.* $|D_N(x)-D_N(y)|\le1-D_N(x-y)\to0$. ∎

Every classical question about $D^\pm$ is therefore a question about the class of the constant in $\mathbb R/K_b$. A decomposition $x=y+z$ with $z\in K_b$ makes progress only if $y$ has known statistics, and no such representative is known for $\ln2$.

### 3.2 Splitting off a normal summand

**Proposition 3.2.** If $\alpha$ is normal in base $b$, then for every $x$ and $Z$,

```math
D^+(\alpha+Z)\le1-D^-(Z),\qquad D^-(x-\alpha)\le1-D^+(x).
```

*Proof.* $D_N(\alpha+Z)\le D_N(\alpha)+1-D_N(Z)$ by sharp translation, and $D_N(\alpha)\to0$. ∎

**The Stoneham splitting.** For odd $c\ge3$ the Stoneham number $\alpha_{2,c}=\sum_{k\ge1}c^{-k}2^{-c^k}$ is normal in base 2 (Bailey–Crandall, Experiment. Math. **11** (2002)). It consists exactly of the Taylor terms of $\ln2$ at $K\in\{c^k\}$, so

```math
\ln2=\alpha_{2,c}+Z_c,\qquad Z_c=\sum_{K\ge1,\ K\notin\{c,c^2,\dots\}}\frac{2^{-K}}K ,
```

verified to 50 digits for $c=3,5,7$. Hence $D^+(\ln2)\le1-D^-(Z_c)$. The route stalls for three reasons:

1. $|D_N(\ln2)-D_N(Z_c)|\le1-D_N(\alpha_{2,c})\to1$, so no statistic transfers between $\ln2$ and $Z_c$ in either direction.
2. The odd part of the reduced denominator of $2^N$ times the chronological prefix of $Z_c$ is divisible by every prime $p\in(N/2,N]$ with $p\ne c$ (exact for $N=60,120,240$). [OP-11](../phase19/taylor-periods.md) therefore applies to $Z_c$ verbatim: it holds "after deleting any one prime-power axis".
3. $D^-(Z_c)>0$ is a statement about a Taylor-type series of exactly the same kind as $\ln2$, and neither implies nor is implied by anything known.

Splitting off several Stoneham numbers changes nothing: sums of normal numbers need not be normal, and the remainder keeps all but finitely many top-band primes. At $N=2000$ the script finds $D_N(\ln2)=0.0331$, $D_N(\alpha_{2,3})=0.0130$ and $D_N(Z_3)=0.0192$, which satisfy Proposition 3.2 and say nothing.

### 3.3 Generating-function identities collapse to the Taylor prefixes

**Lemma 3.3.** Let $G_j(q)=\sum_{K\ge1}g_j(K)q^K$ with $\sum_j\sum_K|g_j(K)|\rho^K<\infty$ for some $1/2<\rho\le1$, and suppose $\sum_jG_j(q)=-\log(1-q)$ for all $q\in(0,\rho)$. Then $\sum_jg_j(K)=1/K$ for every $K$. In particular, collecting all terms with exponent $K\le N$ at $q=1/2$ gives exactly the Taylor prefix $\sum_{K\le N}2^{-K}/K$.

*Proof.* Both sides are analytic in $|q|<\rho$ and agree on an interval, so their coefficients agree; absolute convergence permits the regrouping. ∎

This covers every "$q$-generic" construction: the Möbius–Lambert identity $-\log(1-q)=\sum_m\mu(m)F(q^m)$ (Phase 20 E2.1), the Euler-product form $\ln2=-\sum_m\mu(m)\ln E_{2^m}$ (checked to 55 digits), residue splitting (§3.4), dilations, and any finite or absolutely convergent combination of Lambert series. Every such route returns the Taylor prefixes and hence the OP-11 barrier exactly. To escape one needs an identity special to the point $q=1/2$. The known ones either live in a multiplicatively independent radix, for example $\ln2=\frac23\sum_k9^{-k}/(2k+1)$ in base 9, which meets the same denominator barrier there, or are not radix power series at all, such as $\sum(-1)^{n+1}/n$.

In the Euler-product form each $E_{2^m}=\prod_k(1-2^{-mk})$ lies in $K_2$ (Phase 20, sparse pentagonal coefficients). But $K_2$ is not closed under products (Phase 20 dense-and-partitions), let alone logarithms, so membership of the factors gives nothing.

### 3.4 Residue-class splitting

Write $B_{r,M}=\sum_{K\equiv r\,(M)}2^{-K}/K$. Then $B_{1,2}=\frac12\ln3$, $B_{0,2}=\frac12\ln\frac43$ and $B_{1,4}-B_{3,4}=\arctan\frac12$; the script checks these to 50 digits, computing $\pi$ by Machin's formula. For $\gcd(r,M)=1$, the prefix denominators of $B_{r,M}$ contain every prime $p\equiv r\pmod M$ in $(N/2,N]$ (exact for $(M,r)\in\{(4,1),(4,3),(6,1),(6,5),(5,2)\}$, $N=60,120,240$). That is a positive proportion $1/\varphi(M)$ of the top band, so OP-11 holds for each piece separately ("retaining a positive proportion of the top-band primes"). For $\gcd(r,M)=g>1$ the piece is a Taylor-type series in the radix $2^g$ and meets the same barrier on the dilated scale. Splitting by residues decomposes the obstruction without removing it.

### 3.5 Why the Track B machinery cannot reach logarithms

Every membership in $K_b$ proved in Track B and in Phase 20 comes from an **integer** coefficient sequence: divisor sums, representation numbers, pentagonal signs. Integrality makes every head $\sum_{n\le N}a(n)b^{N-n}$ an integer, so the orbit is governed by the tails, and sparse tails force concentration. Logarithmic series have coefficients $u(K)/K$. Their heads are rationals whose odd denominators contain almost all top-band primes, and the order of $2$ modulo those denominators is superpolynomial (OP-11). A sparse integer-coefficient representation of $\ln2$ plus a rational would put $\ln2$ in $K_2$. None is known, and none is expected, since $\ln2$ is expected to be normal.

The Erdős–Borwein constants have integer coefficients, but nowhere-vanishing ones, and Theorem 1.2 shows that every aligned decomposition then has complementary supports.

These are two structural reasons, one for each family, why a method that decides kernel membership of sparse integer-coefficient constants in every radix leaves the classical constants untouched.

### 3.6 Verdict

No new unconditional estimate yields $D^+(\ln2)<1$ or $D^-(\ln2)>0$. Not even $\ln2\notin K_2$ is established here. The same holds for $\pi$, $e$, $\sqrt2$, $\varphi$ and the Erdős–Borwein constants $E$, $E_{\rm odd}$, $E_{\rm even}$: their digit distribution in every radix **remains open**.

- $\pi$: its BBP prefixes fall under the OP-11 scope.
- $e$: its factorial denominators have no radix structure.
- $\sqrt2$, $\varphi$: algebraic; the Phase 18 functional obstruction stands.

## 4. Verification

The Track E part of `python -B scripts/phase21_characters_classical.py` (standard library; 374,840 assertions in total with Track B; exits 0) checks:

- **E1.** Theorem 1.2 and the zero criterion of Proposition 1.5 for all $n\le2\cdot10^5$ and $k\le12$; the table of §1.7; Lemma 1.1 at every $N\le2^k$ for $k=5,6,7$, with certified digits; the fixed-$N$ limit; the model thresholds. The transfer inequality of §1.1 is checked at $N=2000$ for 14 pairs $(k,r)$ in the B2 section.
- **E2.** The coefficient identities for $m\le10^5$; the real identities to 50 digits; the triangle inequalities at four values of $N$; Proposition 2.2 at four values of $N$ for three numbers; $D(1/3;2)=2/3$ and $D(1/3;4)=1$; Proposition 2.4 for $I\le6$.
- **E3.** The Stoneham splitting for $c=3,5,7$; the top-band prime divisibility for $Z_c$ and for five residue pieces; the residue closed forms; the Euler-product logarithm; the translation inequality at $N=2000$.

All discrepancies come from certified enclosures accurate to $10^{-9}$. All densities and discrepancies are finite data.

## 5. Recommended Lean finite cores

Schematic signatures (names to be fixed against the library), complementing those in [character-q-digamma.md §6](character-q-digamma.md#6-recommended-lean-finite-cores):

```lean
/-- Theorem 1.2: complementary supports. -/
theorem complementary_cover (k r n : ℕ) (hn : 0 < n) :
    (n.divisors.filter fun d => d % 2 ^ k = r).card ≠ 0 ∨
      (2 ^ (k - 1) : ℤ) * (n.divisors.filter fun d => d % 2 ^ k = r).card
        - (n.divisors.filter Odd).card ≠ 0

/-- Lemma 1.1 core: all points of a small positive number lie in a short initial interval. -/
theorem one_sub_radixDiscrepancy_le_of_small {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx0 : 0 ≤ x)
    {N : ℕ} (hN : 0 < N) (hx : (b : ℝ) ^ (N - 1) * x < 1) :
    1 - radixDiscrepancy b x N ≤ (b : ℝ) ^ (N - 1) * x

/-- Proposition 2.2: changing the radix to a power. -/
theorem one_sub_radixDiscrepancy_pow_le (b k : ℕ) (hk : 0 < k) (x : ℝ) {N : ℕ} (hN : 0 < N) :
    1 - radixDiscrepancy (b ^ k) x N ≤ k * (1 - radixDiscrepancy b x (k * N))
```

The analytic inputs (Shiu's moment bound, Bailey–Crandall normality, the PNT) would enter as hypotheses.

## 6. Open questions

1. A displaced, valuation-aware version of Corollary 1.3. Does the 2-adic structure $\tau_{\rm odd}(n)=2^{\omega_{\rm odd}(n)}$ allow any concentration statement for $E_{\rm odd}$ in base 2?
2. Is $E_{\rm odd}\notin K_2$, or $E\notin K_2$? Even this is not established.
3. An anti-concentration estimate $D^+(x)<1$ for a single member of $\{E_{\rm odd},A_{r,2^k}\}$, or for $Z_c$.
4. An identity specific to $q=1/2$ that supplies rational approximants of $\ln2$ whose denominators avoid a positive proportion of the top-band primes at accuracy $2^{-N-\omega(1)}$ (Phase 20 open question 3, unchanged).
