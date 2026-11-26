# The leading constant for the multiplicative Lambert series

**Theorem (paper proof).** Let $r_2(n)$ be the number of representations $n=x^2+y^2$ with $x,y\in\mathbb Z$, and let

```math
L_{\chi_4}=\sum_{m\ge1}\frac{\chi_4(m)}{2^m-1}=\sum_{n\ge1}\frac{r_2(n)}4\,2^{-n},
\qquad
K=\frac1{\sqrt2}\prod_{p\equiv3\ (4)}\Bigl(1-\frac1{p^2}\Bigr)^{-1/2}=0.76422365358922\ldots
```

Then, as $N\to\infty$,

```math
1-D_N(L_{\chi_4};2)\;=\;\sup_x\bigl|D_N(x+L_{\chi_4};2)-D_N(x;2)\bigr|\;\sim\;\frac{K}{2\log2}\,\frac{\log\log N}{\sqrt{\log N}}.
```

The same asymptotic holds for $\Theta_3(1/2)^2=\bigl(\sum_{j\in\mathbb Z}2^{-j^2}\bigr)^2=1+4L_{\chi_4}$. For every real nonprincipal character $\chi$ modulo $q$,

```math
1-D_N(L_\chi;2)\sim\frac{C_\chi}{2\log2}\frac{\log\log N}{\sqrt{\log N}},\qquad
C_\chi=\Bigl(\frac{L(1,\chi)}{\pi}\prod_{\chi(p)=-1}\Bigl(1-\frac1{p^2}\Bigr)^{-1}\prod_{p\mid q}\Bigl(1-\frac1p\Bigr)^{-1}\Bigr)^{1/2}.
```

Here $C_\chi$ is the constant in the count of the support of $r_\chi(n)=\sum_{d\mid n}\chi(d)$. For $\chi_4$, $C_\chi=K$. Phase 17 proved the order $\asymp$ with unspecified constants. [Phase 17 theorem](../phase17/multiplicative-lambert.md)

This answers the critical check of Track B4 affirmatively. Removing the powers of two does not lose a constant factor, collisions are negligible, and the arrival positions have the same counting function $\sim KN/\sqrt{\log N}$ as the sums of two squares. The factor $1/2$ comes from the precision $\log_2(1/\rho_N)=\tfrac12\log_2\log N+O(1)$ that each isolated source needs. Here $\rho_N\sim K/\sqrt{\log N}$ is the source density. The odd parts contribute only $O(1/\sqrt{\log N})$ to the deficit. The proof combines the general isolated-source law of [coefficient-transfer.md §3](coefficient-transfer.md#3-exact-leading-constants-b3) with five arithmetic estimates.

## 1. Arithmetic of the coefficients

Write $c(n)=r_2(n)/4=\sum_{d\mid n}\chi_4(d)$ and $n=2^a\prod p_i^{e_i}\prod q_j^{f_j}$, with $p_i\equiv1$ and $q_j\equiv3\pmod 4$. Then $c(n)=\prod(e_i+1)$ if every $f_j$ is even, and $c(n)=0$ otherwise. The support $\mathfrak B$ is the set of sums of two squares, and Landau's theorem gives $B(N)=\#\mathfrak B\cap[1,N]\sim KN/\sqrt{\log N}$.

On the support write $c(n)=2^{V(n)}U(n)$ with $U(n)$ odd, so that

```math
V(n)=\sum_iv_2(e_i+1),\qquad U(n)=\prod_i\mathrm{odd}(e_i+1),\qquad t(n)=n-V(n).
```

Displacing each source to $t(n)$ gives $\{2^nL_{\chi_4}\}=\{A(n)\}$ with $A(n)=\sum_{d\ge1}C(n+d)2^{-d}$ and $C(t)=\sum_{t(n)=t}U(n)\ge1$ on its support (coefficient-transfer Theorem 2.1). The bounds used below are:

- $V(n)\le\log_2c(n)\le\log_2\tau(n)=O(\log n/\log\log n)$, so $t(n)\ge1$;
- $V(n)\ge\#\{p\equiv1\ (4):p\,\|\,n\}$, whose typical size on $\mathfrak B$ is $\tfrac12\log\log n$;
- $U(n)>1$ only if $p^e\,\|\,n$ with $p\equiv1\ (4)$ and $e+1$ not a power of $2$, in particular $e\ge2$.

**External inputs.**

- (i) Landau's theorem, and Wirsing's theorem for general $\chi$.
- (ii) Shiu's bound $\sum_{n\le x}U(n)\ll x/\sqrt{\log x}$, Phase 17 eq. (1).
- (iii) The resulting mean tail $\sum_{s<M}A(s)\ll M/\sqrt{\log M}$, Phase 17 eq. (2). It also follows from coefficient-transfer Lemma 1.3 with $L=0$.
- (iv) Gauss's bound $\sum_{n\le x}c(n)=\pi x/4+O(\sqrt x)$.
- (v) Brun's upper-bound sieve: Halberstam and Richert, *Sieve Methods*, Theorem 2.2. In the form used here, $S(\mathcal A;\mathfrak P,z)\ll XW(z)$ for $z\le X$ in sieve dimension $\kappa$, with $|R_d|\le\omega(d)$.
- (vi) Mertens' theorem for the primes $\equiv3\pmod4$.

## 2. Upper bound

Apply coefficient-transfer Theorem 2.2 source by source, with sources $n\in\mathfrak B$, arrivals $t(n)$, widths $u(n)=$ the bit length of $U(n)$, and $b=2$. The quantities in that theorem satisfy:

- **Arrival count.** $P(N)=\#\{n:t(n)\le N\}\le B(N+O(\log N))=B(N)+O(\log N)$. Indeed $t(n)\le N$ forces $n\le2N$ and $V(n)=O(\log N)$.
- **Width sum.** $W_U(N)\le\sum_{n\le2N,\,t(n)\le N}U(n)\ll N/\sqrt{\log N}$, using $u\le U$ for odd $U\ge1$ and (ii).
- **Boundary term.** $\Lambda_N=O(\log N)$.
- **Markov term.** $\widehat P(N+L)\le B(N)+O(L+\log N)$, because $\tilde t(n)=n-(\text{bit length of }c(n))\ge n-O(\log n)$ and each value of $\tilde t$ has $O(\log N)$ preimages.

Put $\rho=(1+P(N))/N\sim K/\sqrt{\log N}$, $\varepsilon=\rho$ and $L=\lceil\log_2(1/\rho)\rceil+1$. Then the Markov term is at most $(\tfrac12+o(1))\rho N$ and

```math
1-D_N\le2\rho+\frac{E_N(\rho)}N\le\rho\log_2\frac1\rho+O\Bigl(\frac1{\sqrt{\log N}}\Bigr)
=\frac{K}{2\log2}\frac{\log\log N}{\sqrt{\log N}}\Bigl(1+O\Bigl(\frac1{\log\log N}\Bigr)\Bigr).
```

The $\sqrt{\log N}$ saving in (ii) and the Markov threshold cancel. Markov's inequality at $\varepsilon=\rho$ costs $2^{-L}P(N)/(\rho N)\approx2^{-L}$, so $L=\log_2(1/\rho)+O(1)=\tfrac12\log_2\log N+O(1)$ suffices. A larger $L$, such as the $\log_2\log N$ that a crude mass bound would suggest, is never needed. The Phase 17 one-bit bound (9) charges $L$ per one-digit rather than per source, so it gives a larger constant.

## 3. Lower bound

Fix $N$ large and put

```math
R=\lceil\log_2\log N\rceil,\qquad H_V=\lceil\log_2\log N\rceil,\qquad H=R+H_V.
```

Call $n\in\mathfrak B\cap(2H,N]$ **good** if all of the following hold:

- (G1) $V(n)\le H_V$;
- (G2) $U(n)\le\log\log N$;
- (G3) no $n'\in\mathfrak B$ has $0<|n'-n|\le H$;
- (G4) no $n'\in\mathfrak B$ with $V(n')>H_V$ has $|t(n')-t(n)|\le R$;
- (G5) $A(t(n))\le1/2$.

For good $n$, $t=t(n)$ is an isolated arrival with $C(t)=U(n)$ and no other arrival in $[t-R,t+R]$. Indeed, another $n'$ with $|t(n')-t|\le R$ would have $|n'-n|\le R+H_V$, which (G3) excludes, unless $V(n')>H_V$, which (G4) excludes. We now show that each condition excludes $o(N/\sqrt{\log N})$ elements of $\mathfrak B\cap[1,N]$.

**(E1) Large $V$.** Since $2^{V(n)}\le c(n)$, Gauss's bound gives

```math
\#\{n\le x:V(n)>H_V\}\le2^{-H_V}\sum_{n\le x}c(n)\le\Bigl(\frac\pi4+o(1)\Bigr)\frac{x}{\log x}.
```

**(E2) Large $U$.** By (ii) and Markov, $\#\{n\le N:U(n)>\log\log N\}\ll N/(\sqrt{\log N}\,\log\log N)$.

**(E3) Pairs.** Fix $1\le|h|\le\sqrt x$. If $n,n+h\in\mathfrak B$ and $q\equiv3\pmod4$ divides $n(n+h)$, then $q^2$ divides $n$ or $n+h$. Let $z_0=(\log x)^2$ and $z=\sqrt x$. The pairs with $q^2\mid n(n+h)$ for some $q>z_0$ number at most $2x/z_0+2z$.

The remaining $n$ avoid the classes $0$ and $-h$ modulo every prime $q\equiv3\ (4)$ with $z_0<q\le z$ and $q\nmid h$. This is a sieve problem with $\omega(q)=2$ and $|R_d|\le\omega(d)$, of dimension $1$, since these primes have density $\tfrac12$. Brun's bound and Mertens' theorem in progressions give

```math
\ll x\prod_{z_0<q\le z,\ q\equiv3\,(4),\ q\nmid h}\Bigl(1-\frac2q\Bigr)\ll x\,\frac{\log z_0}{\log z}\ll\frac{x\log\log x}{\log x}.
```

Dropping the primes $q\mid h$ changes the product by a factor at most $(1-2/z_0)^{-\log_2x}\to1$, so the bound is uniform in $h$. It agrees with the expected order $\mathfrak S(h)x/\log x$, with $\mathfrak S(h)\asymp\prod_{q\mid h,\,q\equiv3\,(4)}(1+1/q)$, up to the factor $\log\log x$ lost at the cutoff $z_0$. That factor is harmless. Summing over $|h|\le H$ gives

```math
O(Hx\log\log x/\log x)=O\bigl(x(\log\log x)^2/\log x\bigr)=o\bigl(x/\sqrt{\log x}\bigr).
```

**(E4) Distant arrivals with large $V$.** An exceptional $n'$ with $t(n')\le N+R$ satisfies $n'\le2(N+R)$, since $V(n')\le n'/2$. If $n$ satisfies (G1) and $|t(n)-t(n')|\le R$, then $n\in[t(n')-R,\,t(n')+R+H_V]$. So each exceptional $n'$ spoils at most $2R+H_V+1$ values of $n$, and by (E1) the total is $O(N\log\log N/\log N)$.

**(E5) Tails at isolated arrivals.** For $n$ satisfying (G1)–(G4), the arrival $t$ has no successor within $R$. By coefficient-transfer Lemma 3.1, $A(t)=2^{-R}A(t+R)$. The map $n\mapsto t(n)+R$ is injective, so by (iii)

```math
\#\{A(t(n))>1/2\}\le\#\{s\le N+R:A(s)>2^{R-1}\}\le2^{1-R}\sum_{s\le N+R}A(s)\ll\frac{N}{(\log N)^{3/2}}.
```

This transfers the tail at a source to the unconditional mean tail. That mean, as noted in the B4 brief, cannot be used directly when conditioning on $n\in\mathfrak B$.

Hence the good set $G$ has $|G|=B(N)(1-o(1))$.

**Marking.** For good $n$, $t=t(n)$ and $1\le j\le R$, coefficient-transfer Lemma 3.1 gives $x_{t-j}=\{2^{-j}Y\}$ with $Y=U(n)+A(t)\in[1,\log\log N+\tfrac12]$. Put $j_0=\lceil\log_2(2\log\log N+1)\rceil$. For $j\ge j_0$, $\|x_{t-j}\|=2^{-j}Y\ge2^{-j}$.

Set

```math
\zeta=\rho,\qquad\Delta^+=2\rho\log_2(1/\rho),\qquad\eta=2\Delta^+,\qquad\lambda_\eta=\lfloor\log_2(1/\eta)\rfloor=\log_2\frac1\rho-O(\log\log\log N).
```

By Section 2, at least $1-\Delta^+$ of the points lie within $\zeta$ of $0$. The marked shifts $t-j$, for $n\in G$ and $j_0\le j\le\lambda_\eta\ (\le R)$, lie in pairwise disjoint gaps inside $[0,N)$. Each is at circle distance at least $\eta$ from $0$. Their proportion is

```math
\Delta=\frac{|G|\,(\lambda_\eta-j_0+1)}N=(1-o(1))\,\rho\log_2\frac1\rho .
```

The conditions of coefficient-transfer Lemma 3.3 hold: $\zeta+\Delta\le\rho+\Delta^+<\eta\le\tfrac12$, the bulk has proportion at least $\Delta$, and the marked proportion is at least $\Delta$. So $1-D_N\ge(1-o(1))\rho\log_2(1/\rho)$. Together with Section 2 this proves the theorem. The relative error is $O(\log\log\log N/\log\log N)$.

## 4. Transfers and other characters

**Translation and $\Theta_3$.** The supremum identity is Lean's `sharp_translation_isGreatest`. Since $\Theta_3(1/2)^2-1=4L_{\chi_4}$, the first $N$ shifts of $\Theta_3(1/2)^2$ are $x_2,\dots,x_{N+1}$. Every interval count changes by at most $2$, so $|D_N(\Theta_3(1/2)^2)-D_N(L_{\chi_4})|\le2/N$. The single theta value $\Theta_3(1/2)=1+2\sum_{j\ge1}2^{-j^2}$ displaces to unit sources at $j^2-1$. By Case 1 of the isolated-source law, $1-D_N(\Theta_3(1/2);2)\sim\log_2N/(2\sqrt N)$.

**Real characters.** For nonprincipal real $\chi$, $c_\chi(n)=\sum_{d\mid n}\chi(d)\ge0$, and the support consists of the $n$ with an even exponent at every $p$ with $\chi(p)=-1$. Its Dirichlet series $F$ satisfies

```math
F(s)^2=\zeta(s)L(s,\chi)\prod_{\chi(p)=-1}(1-p^{-2s})^{-1}\prod_{p\mid q}(1-p^{-s})^{-1}.
```

The Selberg–Delange method, or Wirsing's theorem, then gives the support count $\sim C_\chi x/\sqrt{\log x}$ with $C_\chi$ as above. For $\chi_4$, $L(1,\chi_4)=\pi/4$ and $p=2$ give $K$.

Sections 2 and 3 apply verbatim, with the following substitutions:

- Dirichlet's hyperbola bound $\sum_{n\le x}c_\chi(n)=L(1,\chi)x+O_q(\sqrt x)$ replaces Gauss's bound;
- Shiu's bound for $U$ is Phase 17 eq. (1);
- the pair sieve uses the primes with $\chi(p)=-1$, which have harmonic density $\tfrac12$.

For $\chi_{-3}$ the script computes $C_\chi=0.638909$, the known constant for integers of the form $x^2+xy+y^2$.

**The general Phase 17 class.** Take the class of the Phase 17 note: multiplicative $c$ with $0\le c(p^e)\le e+1$, $c(p)=2$ on a prime set of harmonic density $\delta$ with bounded error, and $\kappa=1-\delta$. Assume in addition $S(N)\gg N/(\log N)^\kappa$. This holds by Wirsing's theorem when the prime set has a natural density. Then

```math
1-D_N(L_f;2)=(1+o(1))\,\frac{S(N)}N\log_2\frac N{S(N)}=(1+o(1))\,\frac{\kappa}{\log2}\,\frac{S(N)}N\log\log N .
```

With a Wirsing asymptotic $S(N)\sim C_fN/(\log N)^\kappa$ this becomes $(C_f\kappa/\log 2)(\log\log N)/(\log N)^\kappa$. The changes to the proof are:

- the pair sieve has dimension $2\kappa$ and gives $O(x(\log\log x)^{2\kappa+1}/(\log x)^{2\kappa})=o(x/(\log x)^\kappa)$;
- the Rankin bound uses $H_V=\delta\log_2\log x+2\log_2\log\log x$ applied directly to $2^{V(n)}\mathbf 1_{c(n)>0}$ via Shiu's theorem: on the support of $c$, $2^{V(n)}\le 2^{\omega_S(n)+\Omega_{\ge2}(n)}$ has Euler product $\prod_{p\in S,\,p\le x}(1+2/p)\ll(\log x)^{2\delta}$, giving $\sum_{n\le x,\,c(n)>0}2^{V(n)}\ll x(\log x)^{2\delta-1}$ and hence $\#\{n\le x:V(n)>H_V\}\ll x(\log x)^{\delta-1}(\log\log x)^{-2}=o(x/(\log x)^\kappa)$;
- the bounds (ii) and (iii) are Phase 17 eqs. (1) and (2).

If only the harmonic hypothesis is known, so that $S(N)$ is known only to order, the first form remains an asymptotic equivalence with the true counting function.

## 5. Finite measurements

The script [`scripts/phase20_transfer.py`](../../scripts/phase20_transfer.py) checks the two-square formula through 4,096. It recomputes $K$ from its Euler product to within $10^{-6}$ and certifies $2^{18}+104$ binary digits of $L_{\chi_4}$ and $\Theta_3(1/2)^2$ by integer carries. Each discrepancy is within $2^{-40}$ of the true value.

| $N$ | $1-D_N$ | ratio to $\rho\log_2(1/\rho)$ | ratio to the asymptotic | collisions | isolated at $H=3$ |
|---|---|---|---|---|---|
| $2^{12}$ | 0.65644 | 1.289 | 1.621 | 7.9% | 0.169 |
| $2^{14}$ | 0.63173 | 1.267 | 1.571 | 6.8% | 0.217 |
| $2^{16}$ | 0.60635 | 1.242 | 1.522 | 6.0% | 0.252 |
| $2^{18}$ | 0.58400 | 1.222 | 1.483 | 5.5% | 0.285 |

Here $\rho=S_{\rm eff}(N)/N$. At $N=2^{18}$:

- $B(N)=60{,}108$, which is $1.060$ times $KN/\sqrt{\log N}$, and $S_{\rm eff}(N)=56{,}788$;
- the mean of $V$ is $1.49$, and $V>\log_2\log N$ for 0.23% of the support;
- the mean of $U$ is $1.128$;
- the mean of $A(s)\sqrt{\log N}$ over $s<N$ is $0.913$;
- $|D_N(\Theta_3(1/2)^2)-D_N(L_{\chi_4})|=7.6\times10^{-6}\le2/N$.

For $\chi_{-3}$ at $N=2^{16}$ the ratio to its asymptotic is $1.650$.

The ratios decrease slowly. The proven relative error, $O(\log\log\log N/\log\log N)$, is not small at accessible $N$. The limiting mechanism is visible: only 28.5% of arrivals are isolated at radius $3$ at $N=2^{18}$. The pair count relative to the support is about $H(\log\log N)/\sqrt{\log N}$, which tends to zero only at astronomically large $N$. These are finite measurements, not evidence for the constant. The constant rests on the proof above.

## 6. Status and radix scope

The theorem is a **Lean-supported paper proof**: its circle-separation lower bound (Lemma 3.3, `one_sub_discrepancy_ge_of_bulk_and_far`), composite-radix displaced-source factorization (`radixVal`, `radixUnit`, `displaced_term_eq`), and general linear-mass sparse transfer (`linear_mass_sparse_tendsto_one`, `linear_mass_sparse_preserves_discrepancy`) are kernel-verified in [`NormalityChecker/CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean), alongside `sharp_translation_isGreatest` in [`NormalityChecker/SharpTranslation.lean`](../../NormalityChecker/SharpTranslation.lean). The displaced width bound (Theorem 2.2), source decomposition (Lemma 3.1), exceptional-set estimates (E1)–(E5), and asymptotic theorem remain paper proofs using the external analytic inputs (i)–(vi).

**Radix scope note.** The constant $K/(2\log 2)$ for $L_{\chi_4}$ and $\Theta_3(1/2)^2$ is proved here for base $2$, where $v_2(r_2(n)/4)$ absorbs the powers of $2$ in $c(n)$ so that the remaining odd part $U(n)$ has bounded mean. In an odd radix such as $b=3$, powers of $2$ in $r_2(n)/4$ are not absorbed by $v_3$, so typical digit widths grow like $\frac{1}{2}\log_3(2)\log\log m$; see [theta-and-modular.md](theta-and-modular.md) for the general-radix upper bound $O_b((\log\log N)/\sqrt{\log N})$ and the base-$b$ distinction.
