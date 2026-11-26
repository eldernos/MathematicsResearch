# Radix thresholds and class groups

Phase 22, Tracks B1 and B2. Notation follows [radix-lambert.md](../phase21/radix-lambert.md) and [euler-square-and-forms.md](../phase21/euler-square-and-forms.md): $D_N(z;b)$ is the extreme discrepancy of $\{b^nz\}$, $0\le n<N$, $LL=\log\log N$, $\ell_N=\log_b\log N$, $\rho_N=S(N)/N$, $\lambda_N=\log_b(1/\rho_N)$, and "Theorem 1" is the sub-threshold width law of Phase 21. A source $n$ has coefficient $a(n)=b^{V(n)}U(n)$ with $b\nmid U(n)$, width $u(n)$ (the number of base-$b$ digits of $|U(n)|$), arrival $t(n)=n-V(n)$ and local value $Y(t)=U(n)+A(t)$.

For a radix $b$ write $b=2^sb'$ with $b'$ odd and put

```math
\beta_b=\frac{\log b}{\log b'}\in[1,\infty],\qquad
g_\beta(y)=\sum_{i\ge0}\Bigl(\frac{y\,\gamma^i}{\beta}-1\Bigr)_+,\qquad \gamma=1-\frac1\beta .
```

So $\beta_b=1$ for odd $b$, $\beta_b=\infty$ for $b=2^k$, and $1<\beta_b<\infty$ exactly for the **even composite radices** that are not powers of $2$ ($b=6,10,12,14,18,20,24,\ldots$). Note that $\gamma=\log_b2^s$. For $\beta=1$ we have $\gamma=0$, and with the convention $0^0=1$ the definition gives $g_1(y)=(y-1)_+$.

**Theorem B1 (even composite radices; paper proof).** Let $c$ satisfy the hypotheses of Phase 21 Theorem A2 (multiplicative, $c(p)=2$ on a prime set of density $\delta$, $\kappa=1-\delta$, $\Phi_N=C_f\log\log N/(\log b\,(\log N)^\kappa)$, $\omega=\delta\log2/\kappa$). Let $b=2^sb'$ with $s\ge1$ and $b'>1$ odd. Then, unconditionally,

```math
\kappa\bigl(1+\omega-g_{\beta_b}(\omega)\bigr)\ \le\ \liminf_{N\to\infty}\frac{1-D_N(L_f(b);b)}{\Phi_N}\ \le\ \limsup_{N\to\infty}\frac{1-D_N(L_f(b);b)}{\Phi_N}\ \le\ \kappa+\delta\log2 .
```

In particular $1-D_N\sim(\kappa+\delta\log2)\Phi_N$ for every

```math
\delta\ \le\ \delta^*_b=\frac{\beta_b}{\beta_b+\log2},
```

which strictly exceeds the odd-radix threshold $\delta^*=1/(1+\log2)=0.590616\ldots$ of Phase 21. For $b=6,10,12$ the thresholds are $0.701754$, $0.673632$ and $0.765433$. For odd $b$ the formula reduces to the Phase 21 value $\kappa(1+\min(\omega,1))$, since $g_1(\omega)=(\omega-1)_+$; above the threshold ($\omega\ge1$) this is $2\kappa$.

The source of the gain is a $2$-adic barrier. The coefficient $U=M\cdot2^m$ carries a large power of $2$, and in an even radix the low base-$b$ digits of a large power of $2$ cannot contain long runs of $0$s or of $(b-1)$s (Lemma 1.2). This corrects the last bullet of [radix-lambert.md §4.3](../phase21/radix-lambert.md#43-what-the-classical-tools-give), which asserts that no known tool separates odd from even radices.

**Theorem B1′ (what the digit hypothesis is; paper proof).** Under (W0)–(W3) of Theorem 1, in any radix and for any $\omega>0$, the deficit is pinned between two values of an explicit run functional $\mathcal E_N(\theta)$ of the coefficients (§1.5). The limit $1-D_N\sim(1+\omega)\rho_N\lambda_N$ holds if $\mathcal E_N(\theta)\to0$ for some $\theta<1$, and it implies $\mathcal E_N(\theta)\to0$ for every $\theta>1$. Phase 21's hypothesis $(\mathrm R_b)$ is a sufficient condition of the first kind.

**Theorem B2 (class groups in radix $2^k$; paper proof).** Let $\Delta<0$ be a fundamental discriminant, $G=\mathrm{Cl}(\Delta)=G_2\times G_{\rm odd}$, $h_0=|G^2|$, $Q$ a form in any class $C$, and $\Psi_N=C_Q\log\log N/(2\log b\sqrt{\log N})$. Then, unconditionally, for $b=2^k$,

```math
1-D_N(\Theta_Q(1/b);b)\ \sim\ \Bigl(1+\log2\cdot\mathbb E_\Delta\Bigl[1-\frac1{d}\Bigr]\Bigr)\Psi_N ,
```

where $d=d(n)\in\{1\}\cup\{\text{orders of characters of }G_{\rm odd}\}$ is the largest order of a character of $G_{\rm odd}$ that is not annihilated by a prime power exactly dividing $n$, and $\mathbb E_\Delta$ is its limiting law, an explicit Euler product (§2.4). The constant does not depend on the class $C$. In particular:

- **$G$ a $2$-group** ($G_{\rm odd}=1$: $\mathbb Z/4$ for $\Delta=-39$, $\mathbb Z/8$ for $\Delta=-95$, $\mathbb Z/2\times\mathbb Z/4$ for $\Delta=-260$, and every $h_0=1$ discriminant). The constant is $1$, as for class number one. Moreover $r_Q(n)=w\,(1*\chi_\Delta)(n)/h_0$ for almost all $n$ in the genus of $Q$.
- **$G_{\rm odd}\cong\mathbb Z/\ell$, $\ell$ prime.** The constant is $1+(1-\frac1\ell)(1-\pi_{J,\ell})\log2$, with

```math
1-\pi_{J,\ell}=\prod_{\substack{p\ \text{split}\\ [\mathfrak p]\notin G_2}}\Bigl(1-\frac{(1-1/p)\,p^{1-\ell}}{1-p^{-\ell}}\Bigr).
```

| $\Delta$ | $\mathrm{Cl}(\Delta)$ | $h_0$ | $1-\pi_J$ | radix-$2^k$ factor |
|---|---|---|---|---|
| $-39$, $-95$, $-260$ | $\mathbb Z/4$, $\mathbb Z/8$, $\mathbb Z/2\times\mathbb Z/4$ | 2, 4, 2 | — | $1$ |
| $-23$ | $\mathbb Z/3$ | 3 | 0.783638 | 1.362117 (Phase 21) |
| $-87$ | $\mathbb Z/6$ | 3 | 0.827283 | 1.382286 |
| $-47$ | $\mathbb Z/5$ | 5 | 0.959390 | 1.531999 |
| $-71$ | $\mathbb Z/7$ | 7 | 0.991168 | 1.588879 |

(The Euler products are truncated at $p\le2\cdot10^5$; the tail is below $10^{-6}$ for $\ell=3$ and smaller for $\ell\ge5$.)

**Theorem B2′ ($(\mathrm V_q)$ holds; paper proof).** For every fundamental $\Delta<0$, every class $C$ and every odd prime $q$, $v_q(r_Q(n))$ is tight on the support of $r_Q$. Consequently $1-D_N(\Theta_Q(1/b);b)\sim(1+\log2)\Psi_N$ for every radix $b$ that is not a power of $2$. This removes the hypothesis $(\mathrm V_q)$ from Phase 21 Theorem A4(4).

Together, Theorems B2 and B2′ give the exact constant of $\Theta_Q(1/b)$ in every radix for every primitive form of fundamental discriminant.

**Scope and evidence.** All results are paper proofs from Phase 21 Theorem 1 and its finite lemmas (kernel-verified in `NormalityChecker/RadixWidthLaw.lean` and `CoefficientTransfer`), Phase 20 Theorem 2.2, and published inputs: Shiu and Halberstam–Richert upper bounds; Brun's sieve; Selberg–Delange for products of Hecke $L$-functions of class-group characters (Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, II.5), including the multiplicity statement of Lemma 2.7; Bernays and genus theory; and Strassmann's theorem on zeros of $p$-adic power series. [`scripts/phase22_radix_classgroups.py`](../../scripts/phase22_radix_classgroups.py) (standard library, about 10 s, exit 0, about $3.1\cdot10^6$ exact checks) verifies every finite identity used. Its averages at $N\le5\cdot10^4$ are finite measurements: $LL<2.4$ there, so they do not test the constants.

## 1. Thresholds in composite radices (Track B1)

### 1.1 What is already settled, and what is not

Three points of Phase 21 are recorded here because they determine where the remaining difficulty lies.

1. **Isolation holds for every $\delta<1$.** Distinct sources do not overlap, at any density.
2. **The critical case is exact.** At $\delta=\delta^*$ (that is, $\omega=1$) both bounds of Theorem 1 equal $2\rho_N\lambda_N$, so $1-D_N\sim2\kappa\Phi_N$ unconditionally ([radix-lambert.md §3](../phase21/radix-lambert.md#3-the-prime-density-family-track-a2)).
3. **The upper bound is unconditional in every regime.** $\limsup(1-D_N)/\Phi_N\le\kappa+\delta\log2$ for every $\delta$ and every $b$ that is not a power of $2$. This is the upper half of Theorem 1; its finite core is the kernel-verified `RadixWidthLaw.width_law_upper`, whose analytic inputs are the first moment $W(N)\le(\omega+o(1))S\lambda_N$ and the Markov tail.

**Proposition 1.1 (isolation at every density).** In the setting of Theorem A2, for $1\le H\le(\log N)^{\kappa}/(LL)^{2\kappa+1}$,

```math
\#\{n\in\mathcal A\cap[1,N]:\ \exists\,n'\in\mathcal A,\ 0<|n'-n|\le H\}\ \ll\ S(N)\,\frac{H\,(LL)^{2\kappa}}{(\log N)^{\kappa}}=o(S(N)) .
```

*Proof.* The pair sieve of [radix-lambert.md §3](../phase21/radix-lambert.md#3-the-prime-density-family-track-a2) gives $\ll N(LL)^{2\kappa}/(\log N)^{2\kappa}$ pairs at each shift, uniformly for $1\le|h|\le\sqrt N$. Sum over $|h|\le H$ and divide by $S(N)\asymp N/(\log N)^\kappa$. ∎

The shadow of a source has length $u+\lambda_N\asymp LL$, while sources are isolated at all scales up to $(\log N)^{\kappa-o(1)}$. So **no overlap between distinct sources occurs for any $\delta<1$**. Above the threshold the only obstruction is internal: inside the single block of $u\approx\omega\lambda_N>\lambda_N$ digits of one coefficient $U$, an extremal run (of $0$s or of $(b-1)$s) of length about $\lambda_N$ brings a shift within $\rho_N$ of $0$ (Phase 21 §4.1). Every result below is a statement about such runs.

### 1.2 The 2-adic run barrier

**Lemma 1.2 (run barrier).** Let $b=2^sb'$ with $s\ge1$ and $b'>1$ odd, and let $U\ge1$ with $b\nmid U$.

1. For $1\le j\le v_2(U)/s$, $\ \|U/b^j\|\ge b'^{-j}$.
2. Suppose that $\ell\ge1$ and that the base-$b$ digits of $U$ in positions $s_0,\ldots,s_0+\ell-1$ (position $0$ is the units digit) are all $0$ or all $b-1$, with $s_0+\ell\le v_2(U)/s$. Then $s_0\ge1$ and $2^{s(s_0+\ell)}<b^{s_0}$; equivalently

```math
\ell\ <\ \frac{s_0}{\beta_b-1}.
```

*Proof.* Put $J=s_0+\ell$ in (2), or $J=j$ in (1), and $r=U\bmod b^J$. Since $sJ\le v_2(U)$, both $U$ and $b^J$ are divisible by $2^{sJ}$, so $r$ and $b^J-r$ are multiples of $2^{sJ}$. They are positive, because $b\nmid U$ forces $b^J\nmid U$. Hence $\min(r,b^J-r)\ge2^{sJ}$, which is (1) since $2^{sJ}/b^J=b'^{-J}$.

For (2) with $0$-digits, $r=U\bmod b^{s_0}<b^{s_0}$, so $2^{sJ}\le r<b^{s_0}$. With $(b-1)$-digits, $b^J-r=b^{s_0}-(U\bmod b^{s_0})$. This is $\le b^{s_0}$, with equality only if $b^{s_0}\mid U$, which is impossible for $s_0\ge1$. If $s_0=0$, then $b^J-r=1<2^{sJ}$, a contradiction; so $s_0\ge1$, and again $2^{sJ}<b^{s_0}$. Taking logarithms, $s(s_0+\ell)\log2<s_0\log b$, that is, $\ell s\log2<s_0\log b'$, and $s\log2/\log b'=\beta_b-1$. ∎

For $b=6$ and $U=2^m$, part (1) reads $\{6^{-j}2^m\}=\{2^{m-j}/3^j\}\ge3^{-j}$ for $j\le m$: the fractional part is a nonzero multiple of $3^{-j}$, much larger than the generic bound $6^{-j}/2$ of Phase 20 Lemma 3.2(1). For an odd radix, $\gcd(M2^m,b^J)$ is bounded and Lemma 1.2 has no analogue. Among $M2^m$ with $M\le7$, $m\le400$, the script finds base-$3$ extremal runs whose length is $7$ times their starting position.

### 1.3 Run packing

**Lemma 1.3 (packing).** Let $\beta>1$, $\kappa_0>0$ and $x>0$. Let $[s_i,s_i+\ell_i)$, $\ell_i>0$, be pairwise disjoint intervals in $[0,x]$ with $\ell_i<s_i/(\beta-1)$. (Empty intervals contribute nothing and are discarded.) Then

```math
\sum_i(\ell_i-\kappa_0)_+\ \le\ \kappa_0\,g_\beta(x/\kappa_0),
```

and the bound is sharp: the supremum over admissible families equals $\kappa_0g_\beta(x/\kappa_0)$.

*Proof.* The constraint is invariant under scaling, so take $\kappa_0=1$. The function $g=g_\beta$ is continuous, piecewise linear and nondecreasing, and it satisfies

```math
g(y)=\Bigl(\frac y\beta-1\Bigr)_++g(\gamma y),\qquad 0\le g'(y)\le\sum_{i\ge0}\frac{\gamma^i}{\beta}=\frac1{\beta(1-\gamma)}=1 .
```

Induct on the number of intervals. Let $[s,s+\ell)$ be the interval with the largest left endpoint, so that all other intervals lie in $[0,s]$. By induction they contribute at most $g(s)$. Since $s+\ell\le x$, we get $\ell<s/(\beta-1)\le(x-\ell)/(\beta-1)$, so $\ell<x/\beta$. If $\ell\le1$, the total is at most $g(s)\le g(x)$. If $1<\ell<x/\beta$, then $\ell-1+g(x-\ell)$ is nondecreasing in $\ell$ (because $g'\le1$), so the total is at most $(\ell-1)+g(x-\ell)\le x/\beta-1+g(\gamma x)=g(x)$. For sharpness, take tops $x_i=\gamma^ix$ and lengths $(1-\epsilon)x_i/\beta$ while $x_i>\beta$. ∎

The script checks the recursion, the Lipschitz bound, random admissible families and the geometric extremal family.

### 1.4 Proof of Theorem B1

Run the lower-bound argument of Theorem 1 with $\varepsilon\in(0,1)$, the radius $R_N$ and the exclusions (E1)–(E5) of Phase 21, plus one more condition:

- **(G7)** $v_2(U(n))\ge s\,u(n)$.

*(G7) fails for $o(S(N))$ indices.* On the support, $c(n)=M(n)2^{\omega_{\mathcal S,1}(n)}$ with $M(n)=\prod_{p^e\|n,\ e\ge2\text{ or }p\mid q_0}c(p^e)$. Then $v_2(U)\ge\omega_{\mathcal S,1}-sV$ and $u\le(\omega_{\mathcal S,1}\log2+\log M)/\log b-V+1$, so (G7) holds whenever

```math
\omega_{\mathcal S,1}(n)\,\frac{\log b'}{\log b}\ \ge\ s\bigl(\log_bM(n)+1\bigr).
```

$M$ is tight on the support (Phase 21 §4.1), so $\#\{\log_bM>\eta LL\}=o(S)$ for each $\eta>0$. The Rankin lower tail gives $\omega_{\mathcal S,1}\ge(\delta-\eta)LL$ outside $o(S)$ indices. Take $\eta$ small.

*Marking.* Let $n$ be good, with $t=t(n)$, $u=u(n)$, $Y=U+A$, $|A|\le\frac12$, and let $\eta$ and $\lambda'=\lfloor\log_b(1/(2\eta))\rfloor$ be as in Theorem 1. All shifts $t-j$ with $1\le j\le u+\lambda'-1$ lie in the arrival-free interval $[t-R,t)$. Positions $j\le\lambda'$ and $u<j\le u+\lambda'-1$ are $\eta$-far by Phase 20 Lemma 3.2. Let $\lambda'<j\le u$ be an internal position with $\|Y/b^j\|<\eta$. Then $\|U/b^j\|<\eta+b^{-j}/2<2\eta\le b^{-\lambda'}$, so the $\lambda'$ digits of $U$ in positions $j-1,\ldots,j-\lambda'$ are all $0$ or all $b-1$. A maximal extremal run of length $\ell$ produces at most $\ell-\lambda'+1$ such $j$. By (G7) every run lies below $v_2(U)/s$, so Lemma 1.2(2) applies, and Lemma 1.3 with $\kappa_0=\lambda'-1$ and $x=u$ bounds the number of near internal positions by $(\lambda'-1)g_\beta(u/(\lambda'-1))$. Hence each good source marks at least

```math
u+\lambda'-1-(\lambda'-1)\,g_\beta\!\Bigl(\frac u{\lambda'-1}\Bigr)\ \ge\ \bigl(1+\omega-g_\beta(\omega+\varepsilon)-2\varepsilon-o(1)\bigr)\lambda_N
```

far shifts. This uses (G5)–(G6), $\lambda'/\lambda_N\to1$, and both the monotonicity and the $1$-Lipschitz continuity of $g$: (G6) gives only $u/(\lambda'-1)\le(\omega+\varepsilon)(1+o(1))$, and $g((\omega+\varepsilon)(1+o(1)))\le g(\omega+\varepsilon)+o(1)$. The marked sets of distinct good sources are disjoint. Lemma 3.3 then gives $1-D_N\ge(1+\omega-g_\beta(\omega+\varepsilon)-3\varepsilon-o(1))\rho_N\lambda_N$, exactly as in Theorem 1. Let $\varepsilon\to0$ and use the continuity of $g$ and $\rho_N\lambda_N\sim\kappa\Phi_N$. The upper bound is Theorem 1's. Finally, $g_\beta(\omega)=0$ if and only if $\omega\le\beta$, that is, $\delta\le\delta^*_b$. ∎

Lemma 1.2(1) alone (the bottom band $j\le\lambda'\beta_b$) gives the weaker value $\kappa(1+\min(\omega,\beta_b))$. Lemma 1.3 improves it: $g_\beta(\beta)=0$ and $g_\beta'<1$ just above $\beta$, so $g_\beta(\omega)<\omega-\beta$ for every $\omega>\beta$. Unconditional lower constants, with the upper value $\kappa+\delta\log2$:

| $\delta$ | $\kappa$ | $\omega$ | $b$ odd | $b=6$ | $b=10$ | $b=12$ | upper (all $b\ne2^k$) |
|---|---|---|---|---|---|---|---|
| 0.60 | 0.40 | 1.0397 | 0.8000 | **0.8159** | **0.8159** | **0.8159** | 0.8159 |
| 0.65 | 0.35 | 1.2873 | 0.7000 | **0.8005** | **0.8005** | **0.8005** | 0.8005 |
| 0.70 | 0.30 | 1.6173 | 0.6000 | **0.7852** | 0.7461 | **0.7852** | 0.7852 |
| 0.75 | 0.25 | 2.0794 | 0.5000 | 0.7011 | 0.6565 | **0.7699** | 0.7699 |
| 0.80 | 0.20 | 2.7726 | 0.4000 | 0.6145 | 0.5669 | 0.7094 | 0.7545 |
| 0.90 | 0.10 | 6.2383 | 0.2000 | 0.3934 | 0.3565 | 0.4942 | 0.7238 |

Bold entries are exact constants (lower value equal to upper value). For odd radices (primes, odd prime powers and odd composites such as $15$) Phase 21's lower value $2\kappa$ is the best unconditional value known. Baker–Matveev at the top of the expansion and Yu's $q$-adic theorem at the bottom exclude only $o(\lambda_N)$ internal positions ([radix-lambert.md §4.3](../phase21/radix-lambert.md#43-what-the-classical-tools-give)).

**Sub-threshold composite radices.** For $\delta\le\delta^*$ the bottom band $[1,u]$ is already entirely far in every radix, so Lemma 1.2 adds nothing there. The constant is $\kappa+\delta\log2$ for **every** $b$ that is not a power of $2$, whether prime, prime power, odd composite or even composite. In particular $L_{\chi}(6)$ has the same constant as $L_\chi(3)$ after normalization by $\log b$: $1-D_N\sim C_\chi(1+\log2)LL/(2\log b\sqrt{\log N})$ (Phase 21 Theorem A1). At $N=2^{16}$ the script asserts the barrier $\min(r,6^j-r)\ge2^j$ for every source of $L_{\chi_4}(6)$ and every $j\le v_2(U)$ (and the analogues for $10$ and $12$). It also records the mean displacement $\mathbb E[V_b]$: $1.41$ for $b=2$, and $0.06$, $0.002$, $0.05$, $0.001$, $0.006$ for $b=3,5,6,10,12$.

### 1.5 The exact run functional

For an integer $U\ge1$ and $k\ge1$ let

```math
E_k(U)=\sum_{\text{maximal runs of }0\text{s or }(b-1)\text{s in }U}(\ell-k+1)_+ ,
```

where $\ell$ is the run length in the base-$b$ expansion of $U$. $E_k$ is nonincreasing in $k$ and $E_k(U)\le u$. For $\theta>0$ put

```math
\mathcal E_N(\theta)=\frac1{S(N)\lambda_N}\sum_{n\in\mathcal A\cap[1,N]}E_{\lceil\theta\lambda_N\rceil}\bigl(|U(n)|\bigr),
```

which is nonincreasing in $\theta$.

**Theorem 1.4 (run sandwich).** Assume (W0)–(W3) of Theorem 1 with $\omega>0$, in any radix. For all $0<\theta_1<1<\theta_2$,

```math
1+\omega-\mathcal E_N(\theta_1)-o(1)\ \le\ \frac{1-D_N(F;b)}{\rho_N\lambda_N}\ \le\ 1+\omega-\mathcal E_N(\theta_2)+o(1).
```

*Proof.* **Lower bound.** In the marking step of §1.4 (without (G7)), the near internal positions of a good source number at most $E_{\lambda'}(|U|)\le E_{\lceil\theta_1\lambda_N\rceil}(|U|)$, since $\lambda'=\lambda_N-O(\log\lambda_N)\ge\theta_1\lambda_N$. So each good source marks at least $u+\lambda'-1-E_{\lceil\theta_1\lambda_N\rceil}$ shifts. Summing over $G$, $\sum_Gu\ge(\omega-o(1))S\lambda_N$ by the $L^1$ convergence $u/\lambda_N\to\omega$ (Phase 21 (E5)), and $\sum_GE\le\sum_{\mathcal A}E$.

**Upper bound.** Phase 20 Theorem 2.2 bounds the number of $\varepsilon$-far shifts by the size of the union of the windows $[t(m)-u(m)-L,\,t(m)-1]$ plus the Markov term. Take $\varepsilon=\rho_N$ and $L=\lceil\lambda_N\rceil+2$. Inside the window of a good source, $x_{t-j}=\{b^{-j}Y\}$. Let $k_+=\lceil\log_b(2/\varepsilon)\rceil=\lambda_N+O(1)$. If the $k_+$ digits of $|U|$ below position $j$ are all extremal, then $\|U/b^j\|\le b^{-k_+}\le\varepsilon/2$, and $j\ge k_+$ gives $|A|b^{-j}\le\varepsilon/2$; so $\|x_{t-j}\|\le\varepsilon$ and the shift is not far. A run of length $\ell\ge k_+$ yields the $\ell-k_++1$ positions $j\in[s_0+k_+,s_0+\ell]$, and distinct runs yield disjoint ranges. Windows of good sources are disjoint. Let $Z$ be the set of these non-far shifts over all $n\in G$, and let $\mathcal U_{\rm good}$, $\mathcal U_{\rm bad}$ be the unions of the windows of good and of bad sources. Windows of bad sources may overlap good windows, but a shift in $Z$ is not far whatever windows contain it, so the far shifts inside the union number at most $|(\mathcal U_{\rm good}\cup\mathcal U_{\rm bad})\setminus Z|\le|\mathcal U_{\rm good}|-|Z|+|\mathcal U_{\rm bad}|$. So

```math
E_N(\rho_N)\le W(N)+S(N)\bigl(\lambda_N+O(1)\bigr)-\sum_{n\in G}E_{k_+}(|U(n)|)+o(S\lambda_N).
```

Since $k_+\le\theta_2\lambda_N$ for large $N$, $E_{k_+}\ge E_{\lceil\theta_2\lambda_N\rceil}$. The bad sources contribute at most $\sum_{\mathcal A\setminus G}u=o(S\lambda_N)$ by uniform integrability. With $W(N)\le(\omega+o(1))S\lambda_N$ and $1-D_N\le2\varepsilon+E_N(\varepsilon)/N$ the bound follows. ∎

**Corollary 1.5 (the exact content of the digit hypothesis).**

1. If $\mathcal E_N(\theta)\to0$ for some $\theta<1$, then $1-D_N\sim(1+\omega)\rho_N\lambda_N$.
2. If $1-D_N\sim(1+\omega)\rho_N\lambda_N$, then $\mathcal E_N(\theta)\to0$ for every $\theta>1$.
3. If $\mathcal E(\theta)=\lim\mathcal E_N(\theta)$ exists near $\theta=1$ and is continuous at $1$, then $1-D_N\sim(1+\omega-\mathcal E(1))\rho_N\lambda_N$.

Phase 21's $(\mathrm R_b)$ implies (1) (Phase 21 Proposition 4.1). The extremal-run statistics of $U(n)$ at relative length $1/\omega$ determine the constant, up to the boundary $\theta=1$ itself. Lemmas 1.2–1.3 give, unconditionally, $\limsup\mathcal E_N(\theta)\le\theta g_{\beta_b}(\omega/\theta)$ in even composite radices; this is Theorem B1. For odd $b$ only the trivial $\limsup\mathcal E_N(\theta)\le(\omega-\theta)_+$ is known.

### 1.6 Averaging over the exponent: what it gives and what it cannot give

Write $r=\omega_{\mathcal S,1}(n)$, so $U(n)=M(n)2^r/b^{V(n)}$ with $M,V$ tight and $r$ spread over a window of width $\asymp\sqrt{LL}$ around $\delta LL$.

**Proposition 1.6 (equidistribution at small moduli).** Let $\mathcal S$ be a union of reduced residue classes modulo $q_0$, so that Selberg–Delange applies. Uniformly for $2\le D\le\sqrt{LL}/\psi_N$ with any $\psi_N\to\infty$ and every residue $a\bmod D$,

```math
\frac{\#\{n\le N:\ c(n)>0,\ r(n)\equiv a\ (\mathrm{mod}\ D)\}}{S(N)}=\frac1D\bigl(1+o(1)\bigr).
```

In particular, for $L\le\log_{b'}(\sqrt{LL}/\psi_N)$ the residue $2^{r(n)}\bmod b'^L$ is asymptotically uniform on the cyclic group $\langle2\rangle\subset(\mathbb Z/b'^L)^\times$.

*Proof.* The Dirichlet series $\sum_{c(n)>0}z^{r(n)}n^{-s}$ equals $\zeta(s)^{\delta z}H(s,z)$ with $H(s,z)=(\zeta_{\mathcal S}(s)/\zeta(s)^\delta)^z\tilde H(s,z)$. Here $\zeta_{\mathcal S}(s)/\zeta(s)^\delta$ is a product of Dirichlet $L$-functions to powers, holomorphic and nonvanishing near $s=1$, and $\tilde H$ is holomorphic and bounded for $\Re s>\frac34$, $|z|\le1$. So $H$ is holomorphic near $s=1$ and bounded uniformly in $|z|\le1$; its value $H(1,z)$ includes the constant factor $(\zeta_{\mathcal S}/\zeta^\delta)(1)^z$. Tenenbaum's Theorem II.5.2, uniformly for $|z|\le1$, gives

```math
\mathbb E\bigl[z^{r}\mid c>0\bigr]=(\log N)^{\delta(z-1)}\,\frac{\Gamma(\delta)H(1,z)}{\Gamma(\delta z)H(1,1)}+O\Bigl(\frac1{\log N}\Bigr).
```

For $z=e(h/D)$ we have $|(\log N)^{\delta(z-1)}|=\exp(-\delta LL(1-\cos2\pi h/D))\le\exp(-8\delta LL\|h/D\|^2)$. Orthogonality gives a relative error $\ll\sum_{h=1}^{D-1}\exp(-8\delta LL\|h/D\|^2)+D/\log N\ll D/\sqrt{LL}+D/\log N=o(1)$. The order of $2$ modulo $b'^L$ is at most $\phi(b'^L)<b'^L$. ∎

**Why this cannot decide the runs.** A near-zero internal position needs an extremal run of length $\ge\lambda'\asymp LL$, and whether such a run ends below position $j>\lambda'$ depends on $U\bmod b^j$. Its modulus is at least $b^{\lambda'}=(\log N)^{\kappa+o(1)}$. Once $j\ge(\frac12+\epsilon)\log_{b'}LL$, the order of $2$ modulo $b'^j$ is $\gg_bb'^j$, and this exceeds the length $O(\sqrt{LL})$ of the window that carries all but $\epsilon$ of the law of $r$. So $r\mapsto2^r\bmod b'^j$ is injective on that window. The law of $2^r\bmod b'^j$ is a set of $\asymp\sqrt{LL}$ atoms of mass $\asymp1/\sqrt{LL}$ at distinct residues. No equidistribution statement at those moduli is true, and whether the atoms meet the near-zero set is a question about the specific integers $M2^m$. Proposition 1.6 therefore reaches only digit positions $j\le(\frac12-\epsilon)\log_{b'}LL=o(\lambda_N)$.

### 1.7 Necessary versus sufficient isolation

Theorem 1 isolates sources at the radius $H_N=R_N+H_V\ge(2+\omega)\lambda_N+2(B+2)\ell_N$. The following example shows that this radius is sufficient but not necessary, and that the true scale is the shadow length.

**Proposition 1.7 (pairs at gap $\theta\lambda_N$).** Fix $b\ge3$, $\kappa\in(0,1)$ and $\theta>0$. Let $t_i=\lfloor i(\log(i+3))^\kappa\rfloor$, let $d(t)=\max(1,\lfloor\theta\kappa\log_b\log t\rfloor)$, and let $a$ be the indicator of $\mathcal A=\{t_i\}\cup\{t_i+d(t_i)\}$. Then

```math
1-D_N\Bigl(\sum_{n\in\mathcal A}b^{-n};b\Bigr)\ \sim\ \frac{1+\min(\theta,1)}2\,\rho_N\lambda_N .
```

*Proof.* The gaps $t_{i+1}-t_i\gg(\log t_i)^\kappa$ exceed $d$ and $\lambda_N$ by far. So $\#\mathcal A\cap[1,N]\sim2N/(\log N)^\kappa$, $\lambda_N=\kappa\ell_N+O(1)$ and $d=\theta\lambda_N+O(1)$ for $t\in[N/\log N,N]$. Smaller $t$ number $o(S)$. All coefficients equal $1$, so $u=1$ and $V=0$.

*Upper.* In Phase 20 Theorem 2.2 with $\varepsilon=\rho_N$ and $L=\lceil\lambda_N\rceil+2$, the two windows of a pair $\{t,t+d\}$ have union of length $L+1+\min(d,L+1)$. The Markov term is $O(S/b^2)$, so $1-D_N\le\frac12(1+\min(\theta,1)+o(1))\rho_N\lambda_N$.

*Lower.* For $1\le j\le\min(d,\lambda')$, $x_{t+d-j}=b^{-j}(1+A)$ with $0\le A\ll b^{-(t_{i+1}-t-d)}$, so $\|x\|\ge b^{-j}/2\ge\eta$. For $1\le j\le\lambda'$, $x_{t-j}=b^{-j}(1+b^{-d}+\cdots)$ also has $\|x\|\ge\eta$. These $\min(d,\lambda')+\lambda'$ shifts lie strictly between consecutive pairs, so Lemma 3.3 applies as in Theorem 1. ∎

For $1\le\theta<2+4/\kappa$ the pairs violate (W2), yet the law $1-D_N\sim\rho_N\lambda_N$ holds, with $S(N)$ counting every nonzero coefficient. For $\theta<1$ the constant drops to $(1+\theta)/2$, and as $\theta\to0$ each pair acts as one source of width $2$. A positive proportion $p$ of paired sources gives $1-\frac p2(1-\min(\theta,1))$ by the same count. The script checks the finite identity behind the proof: the far count of the cluster $b^d+1$ at threshold $b^{-k}$ equals $\min(d,k)+k$ for $b\in\{3,5,10\}$, $2\le k\le14$, $1\le d\le29$. The same argument shows that for sources of width $u$, isolation at gap $u+\lambda_N+\psi_N$ with $\psi_N\to\infty$ suffices whenever the tails satisfy (G4).

## 2. Class groups in every radix (Track B2)

### 2.1 Set-up

Let $\Delta<0$ be fundamental, $K=\mathbb Q(\sqrt\Delta)$, $G=\mathrm{Cl}(\Delta)$ of order $h$ with $g=|G/G^2|$ genera, $h_0=h/g=|G^2|$, and $w=2$ (for $\Delta<-4$). Write $G=G_2\times G_{\rm odd}$, $c=(c_2,c_{\rm o})$, and $E=G/G^2=G_2/G_2^2$, an elementary abelian $2$-group. As in Phase 21 §2.1, for $n\in\operatorname{supp}a$, $a=1*\chi_\Delta$, the numbers $a_C(n)$ of ideals of norm $n$ in class $C$ are the coefficients of

```math
X_n=\prod_{p^e\|n\ \text{split}}\ \sum_{i=0}^e[\mathfrak p]^{2i-e}\ \prod_{p^e\|n\ \text{ramified}}[\mathfrak p]^e\ \in\mathbb Z[G],
\qquad r_Q=w\,a_C ,
```

with inert primes contributing $\mathbf 1_{2\mid e}$. For $\chi\in\widehat G$, $\chi(X_n)=\prod\lambda_\chi(p^e)$, where $\lambda_\chi(p^e)=\sum_{i=0}^e\chi(\mathfrak p)^{2i-e}$ at split $p$, and $a_C=\frac1h\sum_\chi\bar\chi(C)\chi(X_n)$. The script checks $r_Q=w\,a_C$ for every $n\le5\cdot10^4$ and every reduced form of $\Delta=-39,-47,-71,-84,-87,-95,-260$, with class groups $\mathbb Z/4,\mathbb Z/5,\mathbb Z/7,(\mathbb Z/2)^2,\mathbb Z/6,\mathbb Z/8,\mathbb Z/2\times\mathbb Z/4$, computed by Gauss composition.

### 2.2 Order-4 annihilation

**Lemma 2.1.** Let $\mathcal X_4=\{\chi\in\widehat G:4\mid\operatorname{ord}\chi\}$.

1. $\chi\in\mathcal X_4$ if and only if $\chi$ is nontrivial on $G_2^2$. Every $\chi\in\mathcal X_4$ takes the value $i$ on some class.
2. Suppose that for every $\chi\in\mathcal X_4$ some split $p\|n$ has $\chi(\mathfrak p)^2=-1$. Then for every class $C$,

```math
|G_2^2|\cdot a_C(n)=\sum_{C'\in CG_2^2}a_{C'}(n)=\mathbf 1\bigl[n\in\operatorname{genus}(C)\bigr]\cdot b_{C_{\rm o}}(n),
```

where $b_c(n)$ is the coefficient of $c$ in $Y_n=\pi_{\rm o}(X_n)\in\mathbb Z[G_{\rm odd}]$ and $\pi_{\rm o}:G\to G_{\rm odd}$ is the projection.

*Proof.* (1) $\operatorname{ord}\chi$ is the lcm of the orders of $\chi|_{G_2}$ and $\chi|_{G_{\rm odd}}$, and $\chi|_{G_2}$ kills $G_2^2$ if and only if its order is at most $2$. Since $\chi(G)=\mu_{\operatorname{ord}\chi}$, it contains $i$ when $4\mid\operatorname{ord}\chi$.

(2) If $\chi(\mathfrak p)=\pm i$ and $p\|n$, then $\lambda_\chi(p)=\chi(\mathfrak p)+\chi(\mathfrak p)^{-1}=0$, so $\chi(X_n)=0$ for every $\chi\in\mathcal X_4$. The remaining characters are those of $\bar G=G/G_2^2\cong E\times G_{\rm odd}$, and orthogonality on $\bar G$ gives $a_C=\frac{|\bar G|}h\cdot[\bar C]\bar X_n=[\bar C]\bar X_n/|G_2^2|$. In $\bar G$ the image of a split prime is $(\bar e,c_{\rm o})$ with $\bar e^{-1}=\bar e$, so each local factor maps to $[\bar e^{\,e}]\otimes\sum_i[c_{\rm o}]^{2i-e}$, and ramified and inert factors map likewise. Hence $\bar X_n=[\bar e_n]\otimes Y_n$, where $\bar e_n\in E$ is the genus of the ideals of norm $n$. ∎

**Lemma 2.2.** The hypothesis of Lemma 2.1(2) fails for $\ll S_\Delta(N)(\log N)^{-c}$ integers $n\le N$ in $\operatorname{supp}a$, with $c=c(\Delta)>0$.

*Proof.* For $\chi\in\mathcal X_4$, the split primes with $\chi(\mathfrak p)=\pm i$ form a union of ideal classes and so have Chebotarev density $\delta_\chi>0$. The integers in $\operatorname{supp}a$ divisible exactly by none of them are the support of a multiplicative function that vanishes at those $p$. Shiu's bound gives $\ll N(\log N)^{-1/2-\delta_\chi}$. There are finitely many $\chi$. ∎

**Theorem 2.3 ($2$-groups).** If $G$ is a $2$-group, then for all but $O(S_Q(N)(\log N)^{-c})$ integers $n\le N$,

```math
r_Q(n)=\frac{w}{h_0}\,(1*\chi_\Delta)(n)\,\mathbf 1\bigl[n\in\operatorname{genus}(Q)\bigr],
```

and $1-D_N(\Theta_Q(1/b);b)\sim\Psi_N$ for $b=2^k$, $\sim(1+\log2)\Psi_N$ for every other $b$, unconditionally.

*Proof.* With $G_{\rm odd}=1$, $Y_n=a(n)$ and $|G_2^2|=h_0$, so Lemmas 2.1 and 2.2 give the identity. Off the exceptional set $\mathcal E_N$, $r_Q$ equals the $h_0=1$ coefficient times the power of two $1/h_0$. Hence $V_b,U_b$ change by $O(1)$, and the proof of Phase 21 Theorem A4(3) applies verbatim, including the genus-restricted first moment and Bernays' $S_Q\sim S_\Delta/g$. The widths on $\mathcal E_N$ are negligible. Take the Rankin exponent $s=1/LL$. By (F2) and Shiu applied to $(2^{\omega_{\rm split}}\sigma_2)^{s}$, $\sum_{n\in\operatorname{supp}r_Q,\,n\le N}r_Q(n)^{1/LL}\ll S$, because the factor $(\log N)^{(2^s-1)/2}$ stays bounded. With $y^2\le2e^y$ for $y=\log r_Q(n)/LL$ this gives $\sum(\log_br_Q)^2\ll S(LL)^2$. By Cauchy–Schwarz,

```math
\sum_{n\in\mathcal E_N}u(n)\le|\mathcal E_N|+\Bigl(|\mathcal E_N|\sum_{n\in\operatorname{supp}r_Q,\,n\le N}(\log_br_Q(n))^2\Bigr)^{1/2}\ll S\,LL\,(\log N)^{-c/2}=o(S\lambda_N).
```

For odd $q\mid b$, $v_q(r_Q)=v_q(a)+O(1)$ off $\mathcal E_N$, which is tight by Phase 21 Lemma 2.3(2). ∎

The script checks the identity $h_0a_C\in\{0,a\}$ for every $n\le5\cdot10^4$ satisfying the annihilation hypothesis: $12{,}538$ of $17{,}219$ supported $n$ for $\Delta=-39$, $3{,}158$ of $17{,}575$ for $\Delta=-95$, and $13{,}865$ of $19{,}988$ for $\Delta=-260$. (For $\Delta=-84$ the hypothesis is empty.) For $\mathbb Z/8$ the annihilation is necessary: $([1]+[7])^r$ has principal coefficient $2^{r-2}+2^{r/2-1}$, whose odd part is about $2^{r/2}$; a single extra factor $[2]+[6]$ (the class on which the order-$8$ characters take the value $\pm i$) turns the product into $2^{r-1}$ times the sum over a coset of $2G$. The nilpotency of the augmentation ideal of $\mathbb F_2[G_2]$ (index $1+\sum(2^{a_i}-1)$, checked for $\mathbb Z/4,\mathbb Z/8,\mathbb Z/2\times\mathbb Z/4,\mathbb Z/4\times\mathbb Z/4$) gives only $v_2\gg r/t$. The exact statement is the annihilation, not the nilpotency.

### 2.3 The odd part

**Lemma 2.4 (local values).** Let $\psi\in\widehat{G_{\rm odd}}$, regarded as a character of $G$ trivial on $G_2$. Let $p$ be split, $\zeta=\psi(\mathfrak p)$ of odd order $o$, and $e\ge1$.

1. If $\zeta=1$, then $\lambda_\psi(p^e)=e+1$.
2. If $\zeta\ne1$, then $\lambda_\psi(p^e)=0$ if and only if $o\mid e+1$. Otherwise $\lambda_\psi(p^e)=\zeta^{-e}(\zeta^{2(e+1)}-1)/(\zeta^2-1)$ is a nonzero real algebraic integer and a $2$-adic unit.
3. For $\zeta\ne1$, $\zeta+\zeta^{-1}$ is a unit of $\mathbb Z[\zeta]$.

*Proof.* (1) and the formula in (2) are immediate. Since $o$ is odd, $\zeta^2$ has order $o$, so the numerator vanishes exactly when $o\mid e+1$. For a root of unity $\xi\ne1$ of odd order, $1-\xi$ has norm $1$ or an odd prime power, so it is a $2$-adic unit. (3) $\zeta+\zeta^{-1}=\zeta^{-1}(1-\zeta^4)/(1-\zeta^2)$, and $\zeta^2,\zeta^4$ have the same order, so the quotient is a cyclotomic unit. ∎

For $n\in\operatorname{supp}a$ define:

- the **survivors** $\mathsf S(n)=\{\psi\in\widehat{G_{\rm odd}}:\lambda_\psi(p^e)\ne0\text{ for all split }p^e\|n\}$, which contains $1$ and is stable under $\psi\mapsto\psi^j$ for $\gcd(j,\operatorname{ord}\psi)=1$;
- $d(n)=\max\{\operatorname{ord}\psi:\psi\in\mathsf S(n)\}$;
- $m_K(n)=\#\{\text{split }p\|n:[\mathfrak p]_{\rm o}\in K\}$ for subgroups $K\le G_{\rm odd}$.

Killing ($\psi\notin\mathsf S(n)$) needs $e\ge o-1\ge2$, so it is a local event at prime squares. This generalizes the J-type of Phase 21 §2.5.

**Lemma 2.5 (exact formula and lower bound).** Under the hypothesis of Lemma 2.1(2),

```math
h_0\,a_C(n)=\mathbf 1[n\in\operatorname{genus}(C)]\sum_{\psi\in\mathsf S(n)}\bar\psi(C_{\rm o})\,\psi(Y_n),
\qquad v_2\bigl(\psi(Y_n)\bigr)=m_{\ker\psi}(n)+\sum_{\substack{p^e\|n,\ e\ge2\\ \psi(\mathfrak p)=1}}v_2(e+1).
```

Hence $v_2(a_C(n))\ge\min_{\psi\in\mathsf S(n)}m_{\ker\psi}(n)-v_2(h_0)$ whenever $a_C(n)\ne0$.

*Proof.* Fourier inversion on $G_{\rm odd}$ applied to Lemma 2.1, with $h_0=|G_2^2|\,|G_{\rm odd}|$ and $|G_{\rm odd}|$ odd. The valuation follows from Lemma 2.4, since ramified factors contribute roots of unity. The last statement is the ultrametric inequality. ∎

**Lemma 2.6 (concentration).** For every subgroup $K$ and $\varepsilon>0$, $|m_K(n)-\frac{|K|}{2|G_{\rm odd}|}LL|\le\varepsilon LL$ outside $O(S(\log N)^{-c(\varepsilon)})$ integers of $\operatorname{supp}r_Q$.

*Proof.* The split primes with $[\mathfrak p]_{\rm o}\in K$ have Chebotarev density $\frac12|K||G_2|/h=|K|/(2|G_{\rm odd}|)$. Apply Rankin's two-sided argument of Phase 21 Lemma 2.2 to $z^{m_K}$; the genus restriction is handled by genus-character twists as in Phase 21 §2.3. ∎

**Lemma 2.7 (multiplicities modulo $M$).** Fix $P_0$, an admissible local pattern $\pi$ (the exponents at the primes $\le P_0$, even at inert primes) and $M\ge1$. Restrict to $n\in\operatorname{supp}a$ with pattern $\pi$ and no split $p>P_0$ with $p^2\mid n$. For each class pair $g=\{c,c^{-1}\}\subset G$ let $m_g(n)$ count the split $p>P_0$, $p\|n$, with $[\mathfrak p]\in g$. Then the vector $(m_g(n)\bmod M)_g$ is asymptotically uniform. Conditionally on the genus it is uniform on the compatible coset when $M$ is even, and uniform on all residue vectors when $M$ is odd.

*Proof.* With $z_g$ roots of unity of order dividing $M$, the Dirichlet series of $\prod_gz_g^{m_g(n)}$ over this set is $H(s,z)\prod_{\chi\in\widehat G}L(s,\chi)^{\alpha_\chi(z)}$, with Hecke $L$-functions of class-group characters and $\alpha_1(z)=\frac1{2h}\sum_{c\in G}z_{\{c,c^{-1}\}}$. Selberg–Delange (Tenenbaum II.5) gives a mean $\ll S\cdot(\log N)^{\Re\alpha_1(z)-1/2}$. This is an upper bound only: the leading coefficient carries $1/\Gamma(\alpha_1(z))$, which vanishes when $\alpha_1(z)=0$, for example at nontrivial genus characters. Moreover $\Re\alpha_1(z)<\frac12$ unless every $z_g=1$. The genus of $n$ is a linear function of $(m_g\bmod2)$ and of $\pi$. For even $M$, conditioning on it restricts the uniform law to a coset. For odd $M$, apply the unconditioned statement modulo $2M$: the residues modulo $M$ are then independent of the residues modulo $2$, hence of the genus. ∎

**Lemma 2.8 (Strassmann).** Let $\mathcal O$ be the ring of integers of a finite extension of $\mathbb Q_\ell$, let $\beta_1,\ldots,\beta_r\in\mathcal O^\times$ with no ratio $\beta_i/\beta_j$ ($i\ne j$) a root of unity, and let $\mathcal C\subset\mathcal O^r$ be compact with all coordinates nonzero at every point. For $A\in\mathcal C$ put $f_A(j)=\sum_iA_i\beta_i^j$ ($j\in\mathbb Z$). Then there is $T\ge1$ with the following property. For each $H$ there is $a(H)$ such that, for every $A$, whether $v(f_A(j))\ge H$ depends only on $j\bmod T\ell^{a(H)}$, and

```math
\sup_{A\in\mathcal C}\ \frac{\#\{j\bmod T\ell^{a(H)}:\ v(f_A(j))\ge H\}}{T\ell^{a(H)}}\ \longrightarrow\ 0\qquad(H\to\infty).
```

Equivalently, the Haar measure of $\{v(f_A)\ge H\}$ in $\mathbb Z/T\mathbb Z\times\mathbb Z_\ell$, into which $\mathbb Z$ embeds densely by $j\mapsto(j\bmod T,j)$, tends to $0$ uniformly in $A$. (Since $T$ has a factor prime to $\ell$, $j\bmod T$ is not a function of $j\in\mathbb Z_\ell$ alone.)

*Proof.* Choose $T$ with $\beta_i^T\in1+\mathfrak m^\nu$, where $\log:1+\mathfrak m^\nu\to\mathfrak m^\nu$ and $\exp$ are inverse isometries. On $j=j_0+Tk$, $f_A(j)=\sum_iA_i\beta_i^{j_0}\exp(kL_i)$ with $L_i=\log\beta_i^T\in\mathfrak m^\nu$ pairwise distinct ($\beta_i^T\ne\beta_j^T$ by hypothesis). This is an analytic function of $k\in\mathbb Z_\ell$, and modulo $\mathfrak m^H$ it depends only on $k\bmod\ell^{a(H)}$ for a suitable $a(H)$. The proportion in the statement is the average over $j_0\bmod T$ of the Haar measure of $\{k\in\mathbb Z_\ell:v(f_A(j_0+Tk))\ge H\}$. Its derivatives at $0$ are $\sum_iA_i\beta_i^{j_0}L_i^m$, which cannot all vanish (Vandermonde), so by Strassmann's theorem it has finitely many zeros. The sets $\{v(f_A)\ge H\}$ decrease to this finite zero set, so their measure $\phi_H(A)\downarrow0$. Each $\phi_H$ depends only on $A\bmod\mathfrak m^H$, so it is continuous, and Dini's theorem makes the convergence uniform on $\mathcal C$. ∎

**Lemma 2.9 (frequencies).** For $\psi\in\widehat{G_{\rm odd}}$ and $c\in G_{\rm odd}$ put $\psi(\eta_c)=\psi(c)+\psi(c)^{-1}$ (real). If $\{\psi,\bar\psi\}\ne\{\psi',\bar\psi'\}$, then for some $c$ the ratio $\psi(\eta_c)/\psi'(\eta_c)$ is not a root of unity. If $\psi$ has order $d$ and $\psi(c^*)$ is a primitive $d$-th root of unity, then the Galois conjugates $\tau(\psi(\eta_{c^*}))$, $\tau\in\mathrm{Gal}(\mathbb Q(\zeta_d)^+/\mathbb Q)$, have pairwise ratios that are not roots of unity.

*Proof.* A real root of unity is $\pm1$. If $\psi(\eta_c)^2=\psi'(\eta_c)^2$ for all $c$, then $\eta_c^2=\eta_{c^2}+2$ gives $\psi(\eta_{c^2})=\psi'(\eta_{c^2})$ for all $c$. Since squaring is a bijection of $G_{\rm odd}$, the class functions $\psi+\bar\psi$ and $\psi'+\bar\psi'$ coincide, and linear independence of characters gives $\{\psi,\bar\psi\}=\{\psi',\bar\psi'\}$. For the second claim, $\tau(\eta)^2=\tau'(\eta)^2$ with $\eta=\psi(\eta_{c^*})$ gives $\tau(\psi(\eta_{c^{*2}}))=\tau'(\psi(\eta_{c^{*2}}))$, and $\psi(\eta_{c^{*2}})$ generates $\mathbb Q(\zeta_d)^+$, so $\tau=\tau'$. ∎

**Proposition 2.10 ($2$-adic non-cancellation).** For every $\varepsilon>0$ there is $H$ such that, for large $N$, all but $\varepsilon S_Q(N)$ integers $n\in\operatorname{supp}r_Q$ satisfy

```math
\min_{\psi\in\mathsf S(n)}m_{\ker\psi}(n)-v_2(h_0)\ \le\ v_2(a_C(n))\ \le\ \min_{\psi\in\mathsf S(n)}m_{\ker\psi}(n)+H .
```

*Proof.* The lower inequality is Lemma 2.5, on the annihilated set of Lemma 2.2. For the upper one fix $\varepsilon>0$. All constants below are chosen in the order Step 0, Step 1, Step 2, Step 3; the minimizing kernel is selected only in Step 4.

*Step 0: patterns.* Choose $P_0$ and a finite set $\Pi$ of admissible patterns so that, outside probability $\varepsilon/4$, $n$ is annihilated, no split $p>P_0$ has $p^2\mid n$, and the pattern $\pi$ of $n$ at the primes $\le P_0$ (ramified primes included) lies in $\Pi$. Fix $\pi\in\Pi$ and work conditionally on $\pi$ and on the genus. Then $\mathsf S(n)=\mathsf S_\pi$. With $m_g$ as in Lemma 2.7 (primes $>P_0$ only), put $m^{\rm o}_c(n)=\sum_{g:\,g_{\rm o}\in\{c,c^{-1}\}}m_g(n)$ for $c\in G_{\rm odd}$, and for a subgroup $K$ let $m^>_K(n)$ count the split $p>P_0$, $p\|n$, with $[\mathfrak p]_{\rm o}\in K$, so that $m_K=m^>_K+m^{\le}_K$ with $m^{\le}_K$ fixed by $\pi$. For $\psi\in\mathsf S_\pi$,

```math
\psi(Y_n)=w_\psi(\pi)\prod_{c\in G_{\rm odd}/\pm}\psi(\eta_c)^{m^{\rm o}_c(n)},\qquad w_\psi(\pi)\ne0,
```

where $w_\psi(\pi)$ collects the primes $\le P_0$ and the ramified primes. Hence $v_2(\psi(Y_n))=m^>_{\ker\psi}(n)+v_2(w_\psi(\pi))$, and by Lemma 2.5, $0\le v_2(w_\psi(\pi))-m^{\le}_{\ker\psi}\le W(\pi)$ for a constant $W(\pi)$.

Characters with the same kernel $K$ are the faithful characters of the cyclic group $G_{\rm odd}/K$. They form one Galois orbit $O_K$, they survive together, and they share $v_K(\pi):=v_2(w_\psi(\pi))$. Let $\mathcal K(\pi)=\{\ker\psi:\psi\in\mathsf S_\pi\}$ and $\mathrm{val}_K=m^>_K+v_K(\pi)$. Then

```math
h_0\,a_C(n)=\mathbf 1_{\rm genus}\sum_{K\in\mathcal K(\pi)}T_K,\qquad T_K=\sum_{\psi\in O_K}\bar\psi(C_{\rm o})\,\psi(Y_n)=2^{m^>_K}F_K ,
```

where $F_{G_{\rm odd}}=w_1(\pi)$ (the orbit of the trivial character is a single character, $d=1$, and no factor $2$ arises), and for $d=[G_{\rm odd}:K]\ge3$ and any $\psi_K\in O_K$

```math
F_K=\mathrm{Tr}_{\mathbb Q(\zeta_d)^+/\mathbb Q}\Bigl(\psi_K(\eta_{C_{\rm o}})\,w_{\psi_K}(\pi)\prod_{c\notin K}\psi_K(\eta_c)^{m^{\rm o}_c}\Bigr),
```

using $\mathrm{Tr}_{\mathbb Q(\zeta_d)/\mathbb Q}(\bar\zeta^{C}x)=\mathrm{Tr}_{\mathbb Q(\zeta_d)^+/\mathbb Q}((\zeta^C+\zeta^{-C})x)$ for real $x$. Since $2$ is unramified in $\mathbb Q(\zeta_d)$, $v_2(T_K)\ge\mathrm{val}_K$ for every $K$.

*Step 1: each fixed kernel, unconditioned on minimality.* Let $K\in\mathcal K(\pi)$. If $K=G_{\rm odd}$, put $H'_K=v_K(\pi)+1$; then $v_2(F_K)<H'_K$ always. If $d\ge3$, pick $c^*\in G_{\rm odd}$ with $\psi_K(c^*)$ a primitive $d$-th root of unity, and vary only the coordinate $j=m_{g^*}$ of the class pair $g^*=\{(1,c^*),(1,c^{*-1})\}$ (trivial $2$-component), all other $m_g$ fixed. Then $F_K=\sum_\tau A_\tau\beta_\tau^j$ with $\beta_\tau=\tau(\psi_K(\eta_{c^*}))$, which are $2$-adic units (Lemma 2.4(3)) with no ratio a root of unity (Lemma 2.9). The coefficients are $A_\tau=\tau\bigl(\psi_K(\eta_{C_{\rm o}})w_{\psi_K}(\pi)\prod\cdots\bigr)$, where the product runs over $c\notin K$ with the coordinate $g^*$ removed and consists of $2$-adic units. So $A$ lies in the compact set $\prod_\tau\tau(\psi_K(\eta_{C_{\rm o}})w_{\psi_K}(\pi))\,\mathcal O^\times$ of vectors with nonzero coordinates ($\psi_K(C_{\rm o})\ne\pm i$ because its order is odd). Lemma 2.8 gives $H'_K$ and a modulus $M_K$ such that, for every value of the other coordinates, at most a proportion $\varepsilon/(8|\mathcal K(\pi)|)$ of the residues of $j$ modulo $M_K$ have $v_2(F_K)\ge H'_K$. The pair $g^*$ lies in $G^2$, so changing $m_{g^*}$ does not change the genus. Lemma 2.7, applied on the whole set with pattern $\pi$ in the given genus (with no condition on which kernel is minimal), gives $\mathbb P(v_2(F_K)\ge H'_K\mid\pi,\text{genus})\le\varepsilon/(4|\mathcal K(\pi)|)$ for large $N$.

*Step 2: constants.* Put $H''(\pi)=\max_{K\in\mathcal K(\pi)}(H'_K-v_K(\pi))$, $H_{\rm tie}=\max_{\pi\in\Pi}H''(\pi)$ and $H=\max_{\pi\in\Pi}(H''(\pi)+W(\pi))$. These depend only on $\varepsilon$.

*Step 3: ties.* Only now choose $M$. For $K\ne K'$ in $\mathcal K(\pi)$ some $c\in G_{\rm odd}$, $c\ne1$, lies in exactly one of them. Changing $m_{\{(1,c),(1,c^{-1})\}}$ by one changes $\mathrm{val}_K-\mathrm{val}_{K'}$ by $\pm1$ and does not change the genus. By Lemma 2.7, $\mathbb P(|\mathrm{val}_K-\mathrm{val}_{K'}|\le H_{\rm tie}\mid\pi,\text{genus})\le(2H_{\rm tie}+1)/M+o(1)$. For $M$ large the probability that some pair of kernels ties within $H_{\rm tie}$ is at most $\varepsilon/4$.

*Step 4: union bound.* Outside the events of Steps 0, 1 and 3, whose total probability is at most $3\varepsilon/4+o(1)$, there is a unique $K^*$ minimizing $\mathrm{val}_K$. Every other $K$ has $v_2(T_K)\ge\mathrm{val}_K>\mathrm{val}_{K^*}+H_{\rm tie}$, while $v_2(T_{K^*})=m^>_{K^*}+v_2(F_{K^*})<\mathrm{val}_{K^*}+H''(\pi)\le\mathrm{val}_{K^*}+H_{\rm tie}$. Hence $v_2(h_0a_C)=v_2(T_{K^*})<\mathrm{val}_{K^*}+H''(\pi)$ whenever $a_C\ne0$. Finally $\mathrm{val}_{K^*}\le\min_{\psi\in\mathsf S(n)}(m^>_{\ker\psi}+m^{\le}_{\ker\psi}+W(\pi))=\min_{\psi\in\mathsf S(n)}m_{\ker\psi}(n)+W(\pi)$, so $v_2(a_C)\le v_2(h_0a_C)<\min_{\psi\in\mathsf S(n)}m_{\ker\psi}(n)+H$. ∎

The script measures the excess $v_2(a_C)-\min_{\mathsf S(n)}(\cdots)+v_2|G_2^2|$ (with the $e\ge2$ terms of Lemma 2.5 included) on all supported $n\le3\cdot10^4$ that satisfy the annihilation hypothesis. Frequencies of the values $0,1,2,3$: for $\Delta=-47$, $0.710,0.249,0.038,0.003$; for $\Delta=-87$, $0.829,0.160,0.011,<10^{-3}$; for $\Delta=-71$, $0.698,0.260,0.040,0.002$; for $\Delta=-327$ ($\mathbb Z/12$, $|G_2^2|=2$), $0.869,0.124,0.008$ (maximum $2$); for $\Delta=-4027$ ($\mathbb Z/3\times\mathbb Z/3$, non-cyclic $G_{\rm odd}$), $0.963,0.037$ (maximum $1$). For $\mathbb Z/5$ and squarefree $n$ the excess is explicit: with $m_0,m_1,m_2$ the numbers of primes of class $0,\pm1,\pm2$ and $j=m_1-m_2$,

```math
5a_0=2^r+(-1)^{m_1}2^{m_0+1}L_j,\qquad 5a_{\pm1}=2^r-(-1)^{m_1}2^{m_0}L_{j+1},\qquad 5a_{\pm2}=2^r+(-1)^{m_1}2^{m_0}L_{j-1},
```

where $L_j$ are the Lucas numbers. Since $v_2(L_j)\in\{0,1,2\}$ (according as $3\nmid j$, $j\equiv0$ or $j\equiv3\pmod6$), the excess is at most $3$ whenever $m_1+m_2\ge4$, since the term $2^r$ then has valuation at least $m_0+4$. The bound persists for non-squarefree $n$ as long as at least four nonprincipal split primes divide $n$ exactly. A nonprincipal prime square with $5\nmid e+1$ contributes a unit $\pm\varphi^k$ to the $\psi$-components, and principal prime powers contribute the same factor $e+1$ to every component. With fewer nonprincipal exact divisors the excess can be larger: $m_0=0$, $m_1=1$, $m_2=2$ and four split primes of class $\pm1$ with exponent $2$ give $5a_0=2^3\cdot3^4-2L_3=640$, so $a_0=2^7$. Here $\psi(\eta_{\pm1})=\varphi^{-1}$ and $\psi(\eta_{\pm2})=-\varphi$ generate the units of $\mathbb Z[\varphi]$. For $\mathbb Z/3$ the units are $\pm1$, which is Phase 21 Lemma 2.3. In particular, contrary to the naive expectation, $v_2(a_C(n))$ is **not** bounded for $\mathbb Z/5$: it grows like $m_0\sim LL/10$, because every principal split prime contributes the factor $[1]+[1]=2$. What is bounded is the excess over $m_0$.

### 2.4 Proof of Theorem B2

Write $u=u_{2^k}(n)=\log_{2^k}\mathrm{odd}(r_Q(n))+O(1)$ and recall $\lambda_N=LL/(2k\log2)+O(1)$. On the support, $\log_2a(n)=\omega_{\rm split}(n)+O(\text{tight})$ and $\omega_{\rm split}=(\frac12+o(1))LL$ in probability. By Phase 21 Proposition 2.2, $\log_2a_C=\log_2a-\log_2h_0+o(1)$ for almost all $n$. Proposition 2.10 and Lemma 2.6, applied to the finitely many kernels, give

```math
\frac{u(n)}{\lambda_N}=\Bigl(1-\frac1{d(n)}\Bigr)\log2+o(1)\qquad\text{in probability on }\operatorname{supp}r_Q .
```

*Law of $d$.* $\mathsf S(n)$ is determined by the events $D_p(e)=\{\psi:\psi(\mathfrak p)\ne1,\ \operatorname{ord}\psi(\mathfrak p)\mid e+1\}$ at the split $p^e\|n$ with $e\ge2$. On $\operatorname{supp}r_Q$ the exponents at finitely many split primes are asymptotically independent with $\mathbb P(v_p=e)=(1-\frac1p)p^{-e}$ (Selberg–Delange with local conditions, and genus twists as in Phase 21 §2.5). Truncation at $P_0$ costs $O(1/P_0)$. So $\mathsf S(n)\to\mathsf S$ in law, where $\mathsf S=\widehat{G_{\rm odd}}\setminus\bigcup_pD_p(e_p)$ with independent geometric $e_p$, and $d$ converges in law to $\mu_\Delta$, the law of $\max_{\psi\in\mathsf S}\operatorname{ord}\psi$. For $G_{\rm odd}\cong\mathbb Z/\ell$, every nontrivial $\psi$ dies together, at $p$ with $[\mathfrak p]_{\rm o}\ne1$ and $\ell\mid e+1$. This gives $\mathbb P(d=\ell)=1-\pi_{J,\ell}$ with $\mathbb P_p(\ell\mid e+1)=(1-\frac1p)\sum_{k\ge1}p^{1-k\ell}=(1-\frac1p)p^{1-\ell}/(1-p^{-\ell})$, the stated product. For $\ell=3$, $G=\mathbb Z/3$ it is Phase 21's $\pi_J$.

*First moment.* By Lemmas 2.5 and 2.6, $v_2(a_C)\ge(\frac1{2d(n)}-\varepsilon)LL-O(1)$ outside $o(S)$ indices, and $v_2\ge0$ always. So

```math
W(N)\le\frac1k\sum_n\bigl(\log_2a(n)-v_2(a_C(n))\bigr)+O(S)\le\Bigl(\log2\,\mathbb E_{\mu_\Delta}\Bigl[1-\frac1d\Bigr]+2\varepsilon+o(1)\Bigr)S\lambda_N ,
```

using the genus-restricted first moment $\sum\log_2a=(\frac12+o(1))S_QLL$ (Phase 21 §2.3), the convergence of $\frac1S\sum1/d(n)$ to $\mathbb E_{\mu_\Delta}[1/d]$ ($1/d$ is bounded) and the exceptional-set estimate of Theorem 2.3. The limit law of $u/\lambda_N$ is supported in $[0,(1-\frac1{|G_{\rm odd}|})\log2]\subset[0,1)$. Theorem 1 in its mixture form ([radix-lambert.md, Remark 5](../phase21/radix-lambert.md#1-the-sub-threshold-width-law)) gives the theorem. ∎

**Remarks.**

1. **The $2$-adic growth rate.** On the event $d(n)=d$, $v_2(a_C(n))/\omega_{\rm split}(n)\to1/d$. This is $1$ for $2$-groups, $1/3$ for $\mathbb Z/3$ and $\mathbb Z/6$ (non-J types), $1/5$ for $\mathbb Z/5$ and $1/7$ for $\mathbb Z/7$. Only $G_{\rm odd}$ and the local killing law matter. The ambiguous classes $\mathrm{Cl}[2]$ and the fraction of primes in them, which Phase 21 Corollary 2.2(3) used for the upper value $1+(1-h_0^{-1})\log2$, do not enter. That value is superseded by $1+\log2\,\mathbb E[1-1/d]\le1+(1-|G_{\rm odd}|^{-1})\log2$.
2. **Group-ring structure modulo $2$.** $\mathbb Z_2[G]\cong\prod_{[\psi]}\mathcal O_\psi[G_2]$ over Frobenius orbits of $\widehat{G_{\rm odd}}$, with $\mathcal O_\psi$ unramified. A factor $[c]+[c^{-1}]$ is a unit in the $\psi$-component exactly when $c_{\rm o}\notin\ker\psi$, and it lies in the maximal ideal otherwise (always so in the trivial component). For $\mathbb Z/3$ the reduction $[1]+[2]$ is idempotent in $\mathbb F_2[\mathbb Z/3]\cong\mathbb F_2\times\mathbb F_4$, and the coefficients of $([1]+[2])^r$ are $(2^r+2(-1)^r)/3$ (even) and $(2^r-(-1)^r)/3$ (odd). For $\mathbb Z/5$, $\mathbb F_2[\mathbb Z/5]\cong\mathbb F_2\times\mathbb F_{16}$, and the principal coefficient of a product of nonprincipal factors is always even. These finite facts are consistent with Proposition 2.10 but do not by themselves fix the valuation; the cancellation question is $2$-adic (Lemma 2.8), not mod $2$.
3. **Several kernels.** For non-cyclic $G_{\rm odd}$ (for example $\mathbb Z/3\times\mathbb Z/3$) the minimum in Proposition 2.10 runs over several kernels of the same index. They tie only with probability $o(1)$, and the constant still depends only on $\mu_\Delta$.

### 2.5 Proof of Theorem B2′

Fix an odd prime $q$ and $\varepsilon>0$. Assume $G_{\rm odd}\ne1$ (the case $G_{\rm odd}=1$ is Theorem 2.3). Work on a fixed pattern $\pi\in\Pi$ and genus, as in Step 0 of Proposition 2.10, with all survivors at once. After pairing $\psi$ with $\bar\psi$ (their terms coincide because $\psi(Y_n)$ is real),

```math
h_0\,a_C(n)=\mathbf 1_{\rm genus}\sum_{\{\psi,\bar\psi\}\subset\mathsf S_\pi}\epsilon_\psi\,\psi(\eta_{C_{\rm o}})\,w_\psi(\pi)\prod_{c\in G_{\rm odd}/\pm}\psi(\eta_c)^{m^{\rm o}_c(n)},\qquad \epsilon_1=\tfrac12,\ \epsilon_\psi=1\ \text{otherwise}.
```

*Coordinates.* Split $m^{\rm o}_c=m_{(1,c)}+m^{\rm rest}_c$. Here $m_{(1,c)}$ counts the primes of the class pair $\{(1,c),(1,c^{-1})\}$ (trivial $2$-component, so inside $G^2$) and $m^{\rm rest}_c$ the primes with nontrivial $2$-component. Condition on all $m^{\rm rest}_c$. Their factors $\psi(\eta_c)^{m^{\rm rest}_c}$ are $q$-adic units, so they are absorbed into the coefficients, which then range over a compact set of vectors with nonzero coordinates. The free vector $\mathbf m=(m_{(1,c)})_{c\in G_{\rm odd}/\pm}$ has $k=(|G_{\rm odd}|+1)/2\ge2$ coordinates.

*Field.* Let $L$ be the completion of $\mathbb Q(\zeta_{|G_{\rm odd}|})^+$ at a prime above $q$ (ramified if $q\mid|G_{\rm odd}|$) and $\mathfrak m_L$ its maximal ideal. The bases $\psi(\eta_c)$ are $2$ or global units (Lemma 2.4(3)), hence units of $\mathcal O_L$. Choose $T$ with $\psi(\eta_c)^T\in1+\mathfrak m_L^\nu$ for all $\psi$ and $c$, where $\log:1+\mathfrak m_L^\nu\to\mathfrak m_L^\nu$ is an isometric isomorphism; the group $1+\mathfrak m_L^\nu$ is torsion-free.

*A separating direction.* For two distinct pairs, Lemma 2.9 gives $c$ with $\psi(\eta_c)^T\ne\psi'(\eta_c)^T$. So $\Lambda(\mathbf w)=\sum_cw_c\bigl(\log\psi(\eta_c)^T-\log\psi'(\eta_c)^T\bigr)$ is a nonzero homomorphism $\mathbb Z^k\to L$. Since $L$ is torsion-free, $\ker\Lambda$ has infinite index, and $\ker\Lambda\cap\{w_{c_1}=1\}$ is either empty or a coset of a subgroup of infinite index in $\{w_{c_1}=0\}\cong\mathbb Z^{k-1}$. Finitely many such sets do not cover $\{w_{c_1}=1\}$, so some $\mathbf w$ with $w_{c_1}=1$ avoids all of them. For this $\mathbf w$ the elements $B_\psi=\prod_c\psi(\eta_c)^{Tw_c}$ of $1+\mathfrak m_L^\nu$ are pairwise distinct. Hence no ratio $\prod_c\psi(\eta_c)^{w_c}/\prod_c\psi'(\eta_c)^{w_c}$ is a root of unity: its $T$-th power is $B_\psi/B_{\psi'}\ne1$, which lies in a torsion-free group.

*Conclusion.* Along the lines $\mathbf m=(0,\mathbf u)+j\mathbf w$ the sum is $f_A(j)$ of Lemma 2.8, with bases $\prod_c\psi(\eta_c)^{w_c}$ and compact nonzero coefficients. Since $w_{c_1}=1$, the map $(\mathbf u,j)\mapsto(0,\mathbf u)+j\mathbf w$ is a bijection of $(\mathbb Z/M)^{k-1}\times\mathbb Z/M$ onto $(\mathbb Z/M)^k$ for every $M$. The classes $(1,c)$ lie in $G^2$, so Lemma 2.7 makes $j\bmod M$ asymptotically uniform given $\mathbf u$, the conditioned coordinates, $\pi$ and the genus. Lemma 2.8 gives $\mathbb P(v_q(h_0a_C)\ge H\mid\pi,\text{genus})\le\varepsilon/2$ for $H\ge H(\varepsilon,\pi)$; take the maximum over $\Pi$. Hence $V_b\le v_q(r_Q)$ is tight for every $b$ divisible by $q$, which is $(\mathrm V_q)$, and Phase 21 §2.4 gives the constant $1+\log2$. ∎

For $\Delta=-23$ this recovers Phase 21's residue-class argument. The general case needs Lemma 2.8, because the units $\psi(\eta_c)$ have infinite order as soon as $\ell\ge5$.

### 2.6 Finite measurements at $N=5\cdot10^4$

Ratios below are measurements at $LL<2.4$; they illustrate the mechanisms and test no constant.

| $\Delta$ | $Q$ | $S_Q/N$ | mean $v_2(r_Q)$ | mean $\log_2U_2$ | fraction with $h_0a_C=a$ |
|---|---|---|---|---|---|
| $-39$ ($\mathbb Z/4$) | $x^2+xy+10y^2$ | 0.1464 | 2.304 | 0.241 | 0.635 |
| $-39$ | $2x^2+xy+5y^2$ | 0.1721 | 1.729 | 0.454 | 1.000 |
| $-95$ ($\mathbb Z/8$) | $x^2+xy+24y^2$ | 0.1146 | 2.180 | 0.142 | 0.292 |
| $-95$ | $4x^2+xy+6y^2$ | 0.1532 | 1.450 | 0.317 | 0.661 |
| $-260$ ($\mathbb Z/2\times\mathbb Z/4$) | $x^2+65y^2$ | 0.0767 | 2.139 | 0.082 | 0.554 |
| $-84$ ($(\mathbb Z/2)^2$) | $x^2+21y^2$ | 0.1057 | 2.396 | 0.123 | 1.000 |
| $-47$ ($\mathbb Z/5$) | $x^2+xy+12y^2$ | 0.1717 | 2.170 | 0.102 | 0.081 |
| $-47$ | $2x^2+xy+6y^2$ | 0.2241 | 1.432 | 0.319 | 0.062 |
| $-87$ ($\mathbb Z/6$) | $x^2+xy+22y^2$ | 0.1209 | 2.197 | 0.123 | 0.273 |
| $-71$ ($\mathbb Z/7$) | $x^2+xy+18y^2$ | 0.1513 | 2.121 | 0.070 | 0.023 |

For the non-ambiguous classes when $h_0=2$ (for example $2x^2\pm xy+5y^2$, of order $4$ in $\mathbb Z/4$ for $\Delta=-39$, and the four forms $3x^2\pm2xy+22y^2$, $6x^2\pm2xy+11y^2$, of order $4$ in $\mathbb Z/2\times\mathbb Z/4$ for $\Delta=-260$), the fraction is exactly $1$. Their genus is $\{C,C^{-1}\}$ and $a_C=a_{C^{-1}}$, so $a_C=a/2$ identically. This fails when $h_0>2$: for $\Delta=-95$ ($\mathbb Z/8$, $h_0=4$) the order-$4$ classes $4x^2\pm xy+6y^2$ lie in the principal genus of four classes, and their fraction is $0.661$. At this height the principal form misses many integers of its genus (Bernays' convergence is slow), which is why the principal rows have smaller support.

## 3. Verification

```sh
python -B scripts/phase22_radix_classgroups.py
```

The script (standard library, about 10 s, exit 0, about $3.1\cdot10^6$ checks) asserts:

- **B1.1** for $L_{\chi_4}(b)$, $n\le2^{16}$, $b\in\{2,3,5,6,10,12\}$: $b\nmid U$, the barrier $\min(r,b^j-r)\ge2^{sj}$ for every source and every $j\le v_2(U)/s$ in $b=6,10,12$, and base-$2$ widths below base-$3$ widths;
- **B1.2** for $U=M2^m/b^{V}$, $M\le27$, $m\le400$, $b\in\{6,10,12,14,18,20,24\}$: Lemma 1.2(2) for every extremal run below $v_2(U)/s$; every near position at threshold $b^{-k}$ lies above $k\beta_b$; near count $\le E_k(U)\le(k-1)g_\beta(u/(k-1))$; and the far-count bound used in §1.4 (it prints maximal run-to-start ratios in bases $3,5,7$ for contrast);
- **B1.3** the recursion, monotonicity and Lipschitz bound of $g_\beta$, random admissible families below $g_\beta$, and the geometric family attaining it;
- **B1.4** the thresholds $\delta^*_b$ and the constant table of §1.4;
- **B1.5** the pair far count $\min(d,k)+k$ of Proposition 1.7;
- **B2.1** the $\mathbb Z/3$ coefficient formulas and idempotence, $\mathbb Z/4$ pure powers of two, $(\mathbb Z/2)^2$, the $\mathbb Z/8$ atypical formula and its annihilated form, the $\mathbb Z/5$ Lucas formulas for 3,000 random products with excess $\le3$, $v_2(L_n)$ for $n<120$, and the nilpotency indices for four $2$-groups (all products of length $\le40$);
- **B2.2** for random products in $\mathbb Z/4,\mathbb Z/6,\mathbb Z/7,\mathbb Z/8,\mathbb Z/12,\mathbb Z/2\times\mathbb Z/4,\mathbb Z/2\times\mathbb Z/6,\mathbb Z/3\times\mathbb Z/3$: the identity of Lemma 2.1(2) whenever the annihilation hypothesis holds, and the lower bound of Lemma 2.5;
- **B2.3** Gauss composition with group axioms, the class-group structures, $r_Q=w\,a_C$ for every $n\le5\cdot10^4$, all reduced forms and seven discriminants, and Theorem 2.3's identity on the annihilated set for the $2$-groups;
- **B2.4** nonnegativity of the excess (Lemma 2.5) for $\Delta=-47,-87,-71$, for the cyclic $\mathbb Z/12$ discriminant $\Delta=-327$ found by search ($|G_2^2|=2$), and for $\Delta=-4027$ ($\mathbb Z/3\times\mathbb Z/3$, structure asserted), on all annihilated supported $n\le3\cdot10^4$. It also prints, as finite measurements, the means of $v_3(a_C)$ ($0.116$, $0.126$, $0.095$, $0.066$, $0.000$) and of $v_5(a_C)$ ($0.025$, $0.024$, $0.017$, $0.005$, $0.000$) for the five discriminants in that order; no supported $n\le3\cdot10^4$ has $v_3(a_C)\ge3$ or $v_5(a_C)\ge3$;
- **B2.5** $1-\pi_J$ and the radix-$2^k$ constants, reproducing Phase 21's $0.783638$ and $1.362117$ for $\Delta=-23$, and listing the $2$-group discriminants $-39,-84,-95,-260$ with constant $1$.

## 4. Status

- **Paper proofs (this note):** Proposition 1.1; Lemmas 1.2 and 1.3; Theorem B1 (§1.4); Theorem 1.4 and Corollary 1.5; Proposition 1.6; Proposition 1.7; Lemmas 2.1–2.9; Theorem 2.3; Proposition 2.10; Theorems B2 and B2′.
- **Corrections to Phase 21:** the claim in [radix-lambert.md §4.3](../phase21/radix-lambert.md#43-what-the-classical-tools-give) that no known tool separates odd from even radices (Lemma 1.2 does, and Theorem B1 improves $2\kappa$ in every even composite radix); the "conditional under $(\mathrm V_q)$" status of [euler-square-and-forms.md](../phase21/euler-square-and-forms.md) Theorem A4(4) (now unconditional, Theorem B2′); and the "open" radix-$2^k$ constant for class groups other than $\mathbb Z/3$ and $h_0=1$ (now Theorem B2, for every fundamental $\Delta<0$).
- **Open:** the exact constant above $\delta^*_b$ in even composite radices and above $\delta^*$ in odd radices; Corollary 1.5 identifies it with the extremal-run statistics of $M2^m$ at relative length $1/\omega$, and no available tool reaches runs of length $\asymp LL$ (§1.6). Also open are non-fundamental and imprimitive forms beyond the order and the lower value of Phase 21 Proposition 2.1.
- **External inputs:** Shiu and Halberstam–Richert; Brun's sieve; Selberg–Delange for Hecke $L$-functions of class-group characters (Tenenbaum II.5), including Lemma 2.7 and Proposition 1.6; Chebotarev in the Hilbert class field; Bernays and genus theory; Strassmann's theorem. Phase 21 inputs are listed there.
- **Finite core suitable for Lean:** Lemma 1.2 (integer statement), Lemma 1.3 (real inequality by induction) and the identity of Lemma 2.1(2) (orthogonality on a finite abelian group) are finite statements in the style of `NormalityChecker/RadixWidthLaw.lean`. They have not been formalized here.
- **Finite evidence:** [`scripts/phase22_radix_classgroups.py`](../../scripts/phase22_radix_classgroups.py).
