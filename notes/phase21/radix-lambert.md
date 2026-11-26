# Multiplicative Lambert series in every radix

Phase 21, Tracks A1 and A2. Fix an integer radix $b\ge2$. For a real nonprincipal Dirichlet character $\chi$ put $c(n)=(1*\chi)(n)=\sum_{d\mid n}\chi(d)$ and

```math
L_\chi(b)=\sum_{m\ge1}\frac{\chi(m)}{b^m-1}=\sum_{n\ge1}c(n)\,b^{-n}.
```

Let $S(N)=\#\{n\le N:c(n)>0\}$ and let $C_\chi$ be the Landau–Wirsing support constant, $S(N)\sim C_\chi N/\sqrt{\log N}$, given explicitly in [Phase 20](../phase20/lambert-leading-constant.md) ($C_{\chi_4}=K=0.764223653\ldots$). Write $D_N(z;b)$ for the extreme discrepancy of $\{b^nz\}$, $0\le n<N$.

**Theorem A1 (paper proof).** As $N\to\infty$,

```math
1-D_N(L_\chi(b);b)=\sup_x\bigl|D_N(x+L_\chi(b);b)-D_N(x;b)\bigr|\sim
\begin{cases}
\dfrac{C_\chi}{2\log b}\,\dfrac{\log\log N}{\sqrt{\log N}}, & b=2^k,\\[2ex]
\dfrac{C_\chi\,(1+\log 2)}{2\log b}\,\dfrac{\log\log N}{\sqrt{\log N}}, & b\ \text{not a power of }2.
\end{cases}
```

The factor $1+\log2$ is the sum of two costs per supported index: $\tfrac12\log_b\log N$ digits of precision that every isolated source needs, and $\tfrac{\log 2}{2}\log_b\log N$ digits that the coefficient $c(n)\approx2^{\omega_{\rm split}(n)}$ itself occupies when the radix cannot absorb its powers of $2$. In radix $2^k$ the second cost disappears.

**Theorem A2 (paper proof; the Phase 17 class).** Let $c$ be multiplicative with $0\le c(p^e)\le e+1$, $c(p)=2$ on a prime set $\mathcal S$ of natural density $\delta\in(0,1)$ with convergent Mertens constant $\sum_{p\le x,\,p\in\mathcal S}1/p=\delta\log\log x+M_{\mathcal S}+o(1)$, and $c(p)=0$ on the other primes coprime to a fixed modulus ([Phase 17 hypotheses](../phase17/multiplicative-lambert.md#1-hypotheses-and-conventions)). Put $\kappa=1-\delta$, $S(N)\sim C_fN/(\log N)^\kappa$ (Wirsing), $L_f(b)=\sum c(n)b^{-n}$, and

```math
\delta^*=\frac1{1+\log2}=0.590616\ldots,\qquad\text{so that}\qquad \delta\log2<\kappa\iff\delta<\delta^* .
```

Normalize by $\Phi_N=C_f\log\log N/(\log b\,(\log N)^\kappa)$ (or, if only the bounded-error harmonic hypothesis $+O(1)$ and $S(N)\asymp N/(\log N)^\kappa$ are assumed, normalize by $\rho_N\lambda_N$ in place of $\kappa\Phi_N$, with the ratio constants divided by $\kappa$).

1. If $b=2^k$, then $1-D_N(L_f(b);b)\sim\kappa\,\Phi_N$ for every $\delta\in(0,1)$.
2. If $b$ is not a power of $2$ and $\delta\le\delta^*$, then $1-D_N\sim(\kappa+\delta\log2)\,\Phi_N$.
3. If $b$ is not a power of $2$ and $\delta>\delta^*$, then unconditionally

```math
2\kappa\ \le\ \liminf_{N\to\infty}\frac{1-D_N}{\Phi_N}\ \le\ \limsup_{N\to\infty}\frac{1-D_N}{\Phi_N}\ \le\ \kappa+\delta\log2 ,
```

and the upper value is the limit under the digit hypothesis $(\mathrm R_b)$ of §4 on extremal base-$b$ runs in $M\cdot2^m$. Linear forms in logarithms (Baker, Matveev, Yu), Stewart's digit theorem and the periodicity of $2^m\bmod b^j$ do not improve the lower value $2\kappa$ (§4.3).

Part 1 normalized by the true support count ($1-D_N\sim\rho_N\lambda_N$) needs only the bounded-error harmonic hypothesis of Phase 17 together with $S(N)\asymp N/(\log N)^\kappa$; the asymptotic constant $C_f$ in $\Phi_N$ uses the convergent Mertens constant $+M_{\mathcal S}+o(1)$, and parts 2 and 3 use the natural density to compute the first moment of $\log c$.

**Scope and evidence.** Theorems A1 and A2 are paper proofs. They combine Phase 20's displaced width inequality, source decomposition and circle separation ([coefficient-transfer.md](../phase20/coefficient-transfer.md), Theorem 2.2 and Lemmas 3.1–3.3; Lemma 3.3 is kernel-verified as `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far`) with published analytic inputs listed in §2.0. Phase 20 Theorem 3.4 is **not** applied as stated: its mass hypothesis (I3) fails in every radix that is not a power of $2$. §1 proves a replacement, the sub-threshold width law, in which a longer isolation radius absorbs the mass and the digit hypothesis (I4) holds automatically. Finite checks are in [`scripts/phase21_radix.py`](../../scripts/phase21_radix.py) (standard library, about 40 s, exit 0). All ratios quoted from it are finite measurements, not evidence for the constants, since $\log\log N<2.6$ at every accessible $N$.

## 0. Conventions and reused finite facts

Logarithms are natural unless a base is shown, $\ell_N=\log_b\log N$ and $LL=\log\log N$. For an integer sequence $a$ with support $\mathcal A$ write $a(n)=b^{V(n)}U(n)$ with $b\nmid U(n)$ (Lean `radixVal`, `radixUnit`), let $u(n)$ be the number of base-$b$ digits of $|U(n)|$, and put $t(n)=n-V(n)$ (the arrival) and $\tilde t(n)=t(n)-u(n)$. Let $C(t)=\sum_{t(n)=t}U(n)$ and $A(t)=\sum_{d\ge1}C(t+d)b^{-d}$, so that $\{b^nF\}=\{A(n)\}$ for $F=\sum a(n)b^{-n}$ (Phase 20 Theorem 2.1). Put $S(N)=\#\mathcal A\cap[1,N]$, $\rho_N=S(N)/N$, $\lambda_N=\log_b(1/\rho_N)$, $W(N)=\sum_{n\in\mathcal A,\,n\le N}u(n)$, and $\mathsf A(X)=\sum_{n\le X}|a(n)|$.

From Phase 20 we use, for a single source with arrival $t$, previous gap $g_t$ and local value $Y(t)=C(t)+A(t)$, the exact formula $x_{t-j}=\{b^{-j}Y(t)\}$ for $1\le j\le g_t$ (Lemma 3.1), and Lemma 3.2: if $b\nmid C(t)$ and $|A(t)|\le\tfrac12$, then

- $\|b^{-j}Y(t)\|\ge b^{-j}/2$ for every $j\ge1$;
- $\|b^{-j}Y(t)\|=b^{-j}|Y(t)|\ge b^{-j}(b^{u-1}-\tfrac12)$ for $j\ge u+1$.

Both statements hold for either sign of $C(t)$. We also use the deficit bound $1-D_N\le2\varepsilon+E_N(\varepsilon)/N$, the displaced width inequality (Phase 20 Theorem 2.2), the sharp translation identity (Lean `sharp_translation_isGreatest`), and Lemma 3.3: if at least $\Delta N$ points satisfy $\|x_n\|\le\zeta$ and at least $\Delta N$ satisfy $\|x_n\|\ge\eta$, with $\zeta+\Delta<\eta\le\tfrac12$, then $1-D_N\ge\Delta$.

## 1. The sub-threshold width law

**Theorem 1.** Let $a:\mathbb N\to\mathbb Z$ and suppose that, for constants $B\ge0$, $0<\kappa<1$ and $\omega\ge0$:

- **(W0) Density.** $\rho_N=(\log N)^{-\kappa+o(1)}$ and $\rho_N\to0$.
- **(W1) Mass.** $\mathsf A(X)\le X(\log X)^B$ for large $X$, and $|a(n)|\le n^{o(1)}$.
- **(W2) Isolation.** With $H_V=\lceil(B+2)\ell_N\rceil$, $R_N=\lceil(2+\omega)\lambda_N+(B+2)\ell_N\rceil$ and $H_N=R_N+H_V$,

```math
\#\{n\in\mathcal A\cap[1,N]:\ \exists\,n'\in\mathcal A,\ 0<|n'-n|\le H_N\}=o(S(N)).
```

- **(W3) Widths.** $W(N)\le(\omega+o(1))\,S(N)\lambda_N$, and for each $\varepsilon>0$, $\#\{n\in\mathcal A\cap[1,N]:u(n)<(\omega-\varepsilon)\lambda_N\}=o(S(N))$.

Then

```math
\bigl(1+\min(\omega,1)-o(1)\bigr)\rho_N\lambda_N\ \le\ 1-D_N(F;b)\ \le\ (1+\omega+o(1))\,\rho_N\lambda_N .
```

In particular $1-D_N(F;b)\sim(1+\omega)\rho_N\lambda_N$ whenever $\omega\le1$. If $\omega>1$, the upper value is attained provided

- **(W4) Internal digits.** $\sum_{n\in G_0}Z_{t(n)}(\eta_N)=o(S(N)\lambda_N)$, where $G_0$ is the set of indices $n\in\mathcal A\cap(2H_N,N]$ satisfying (G1)–(G4) below together with $u(n)\le(\omega+1)\lambda_N$, $\eta_N=3(2+\omega)\rho_N\lambda_N$, and $Z_t(\eta)=\#\{\lambda'_\eta<j\le u:\|b^{-j}Y(t)\|<\eta\}$ counts the near-zero internal positions with $\lambda'_\eta=\lfloor\log_b(1/(2\eta))\rfloor$.

*Upper bound.* Apply Phase 20 Theorem 2.2 with $\varepsilon=\rho_N$ and $L=\lceil\lambda_N\rceil+2$. Since $b^{V(n)}\le|a(n)|=n^{o(1)}$, $V(n)=o(\log n)$ and $t(n)\ge n/2$ for large $n$. The four terms are bounded as follows.

- **Arrivals.** $P(N)=\#\{n:1\le t(n)\le N\}\le S(N)+O(\log N)$, since $t(n)\le N$ forces $n\le N+\max_{m\le2N}V(m)$.
- **Widths.** The arrivals $t\le N$ have total width $W_U(N)\le W(N)+O(\log^2N)$.
- **Right boundary.** $\Lambda_N\le\max_{n\le2N}(u(n)+V(n))=O(\log N)$.
- **Markov term.** Since $|U|b^{-u}<1$,

```math
\widehat P(N+L)\le\#\{n:\tilde t(n)\le N+L\}+\sum_{\tilde t(n)>N+L}b^{N+L-\tilde t(n)}\le S(N)+O(\log N)+b\sum_{i\ge1}|a(N+L+i)|b^{-i}=S(N)(1+o(1)).
```

As $b^{-L}\le\rho_N/b^2$, the Markov term counts at most $S(N)(1+o(1))/(b^2(b-1))$ shifts. Hence

```math
1-D_N\le2\rho_N+\frac{W(N)+S(N)\lambda_N+O(S(N))}{N}=(1+\omega+o(1))\rho_N\lambda_N .
```

*Lower bound.* Fix $\varepsilon\in(0,1)$ and write $R=R_N$, $H=H_N$. Call $n\in\mathcal A\cap(2H,N]$ **good** if

- (G1) $V(n)\le H_V$;
- (G2) no $n'\in\mathcal A$ has $0<|n'-n|\le H$;
- (G3) no $n'\in\mathcal A$ with $V(n')>H_V$ has $|t(n')-t(n)|\le R$;
- (G4) $|A(t(n))|\le\tfrac12$;
- (G5) $u(n)\ge(\omega-\varepsilon)\lambda_N$;
- (G6) $u(n)\le(\omega+\varepsilon)\lambda_N$.

The exclusions are counted as follows.

- **(E1)** Since $b^{V}\le|a|$, Markov's inequality and (W1) give $\#\{n\le3N:V(n)>H_V\}\le b^{-H_V}\mathsf A(3N)\ll N(\log N)^{-2}$. This is $o(S(N)/\ell_N)$ by (W0), because $\kappa<1$.
- **(E2)** (G2) fails for $o(S(N))$ indices, by (W2).
- **(E3)** An exceptional $n'$ with $t(n')\le N+R$ has $n'\le3N$. If $n$ satisfies (G1) and $|t(n)-t(n')|\le R$, then $n\in[t(n')-R,\,t(n')+R+H_V]$, so each exceptional $n'$ spoils at most $2R+H_V+1=O(\ell_N)$ indices. By (E1) the total is $o(S(N))$.
- **(E4)** For $n$ satisfying (G1)–(G3), $t=t(n)$ is the only arrival in $[t-R,t+R]$, and $C(t)=U(n)$. Indeed, any other $n'$ with $|t(n')-t|\le R$ either has $V(n')\le H_V$, and then $|n'-n|\le H$, or has $V(n')>H_V$; (G2) and (G3) exclude both. By Lemma 3.1, $A(t)=b^{-R}A(t+R)$. The map $n\mapsto t(n)+R$ is injective on these $n$. Lemma 1.3 of Phase 20 with $L=0$ gives $\sum_{s<M}|A(s)|\le\widehat{\mathsf A}_C(M)/(b-1)$, and $\widehat{\mathsf A}_C(M)\le\mathsf A(2M)+O(1)$ because for $n>2M$ we have $t(n)\ge n/2>M$ and $|U(n)|b^{M-t(n)}=|a(n)|b^{M-n}\le n^{o(1)}b^{-n/2}$ (whose tail sum is $O(1)$). With $M=N+R+1$ and $b^{-R}\le\rho_N^{2+\omega}(\log N)^{-B-2}\le\rho_N(\log N)^{-B-2}$,

```math
\#\{n:\ |A(t(n))|>\tfrac12\}\le2b^{-R}\,\frac{\mathsf A(3N)+O(1)}{b-1}\ll\frac{\rho_NN}{(\log N)^2}=o(S(N)).
```

  This step replaces hypothesis (I3) of Phase 20. The mass $\mathsf A(N)$ may be as large as $N(\log N)^B$; the radius $R-\lambda_N\ge(B+2)\ell_N$ absorbs it.
- **(E5)** (G5) fails for $o(S(N))$ indices by (W3). Together with the first-moment upper bound $W(N)\le(\omega+o(1))S(N)\lambda_N$ in (W3), this implies $u(n)/\lambda_N\to\omega$ in $L^1$ on $\mathcal A\cap[1,N]$: writing $X_n=u(n)/\lambda_N$, we have $\mathbb E[(X_n-\omega)_-]\to0$ and $\mathbb E[X_n-\omega]\le o(1)$, hence $\mathbb E[|X_n-\omega|]\to0$. In particular (G6) also fails for $o(S(N))$ indices.

Thus the good set $G$ has $|G|=(1-o(1))S(N)$.

*Marking.* Let $\Delta^+=(1+\omega+\varepsilon)\rho_N\lambda_N$ dominate the upper bound for large $N$. Put $\zeta=\rho_N$, $\eta=2\rho_N+2\Delta^+$ and $\lambda'=\lfloor\log_b(1/(2\eta))\rfloor=\lambda_N-\log_b\lambda_N-O(1)$. For $n\in G$ with $t=t(n)$ and $u=u(n)$, Lemma 3.2 applies, because $b\nmid U(n)=C(t)$ and $|A(t)|\le\frac12$. It marks the positions $1\le j\le\lambda'$ and $u+1\le j\le u+\lambda'-1$, at each of which $\|x_{t-j}\|\ge\eta$. Their union has at least $\min(u,\lambda')+\lambda'-1$ elements, and by (G6) every marked index satisfies $1\le j\le u+\lambda'-1\le(1+\omega+\varepsilon)\lambda_N\le R$ (since $R_N\ge(2+\omega)\lambda_N$). Therefore **all** these shifts $t-j$ lie in the arrival-free interval $[t-R,t)$, so the sets belonging to distinct good sources are pairwise disjoint, and $t-j\ge n-H>0$. By (G5),

```math
\frac{\#\text{marked}}N\ \ge\ \frac{|G|}N\Bigl(\min\bigl(\max(1,(\omega-\varepsilon)\lambda_N),\lambda'\bigr)+\lambda'-1\Bigr)=:\Delta\ \ge\ \bigl(1+\min(\omega,1)-2\varepsilon-o(1)\bigr)\rho_N\lambda_N .
```

The upper-bound count gives at least $N(1-\Delta^+)\ge\Delta N$ points with $\|x_n\|\le\zeta$, and $\zeta+\Delta<\eta\le\tfrac12$. Lemma 3.3 gives $1-D_N\ge\Delta$. Since $\varepsilon$ was arbitrary, the lower bound follows.

If $\omega>1$ and (W4) holds, note that $G\subseteq G_0$ for $\varepsilon<1$, and for each $n\in G$ Lemma 3.2 marks at least $u+\lambda'-1-Z_t(\eta_N)$ positions inside $[t-R,t)$ (since $\eta\le\eta_N$ for large $N$ and $u+\lambda'-1\le R$ by (G6)). Summing over $n\in G$ and using (W4) gives $(1+\omega-2\varepsilon-o(1))\rho_N\lambda_N$. ∎

**Remarks.**

1. **Why no internal-digit statistics are needed below the threshold.** When $\omega<1$, every source with $u\le\lambda'$ has $Z_t=0$, since the internal range $(\lambda',u]$ is empty. The bound uses $\min(u,\lambda')$, so the sources with $u>\lambda'$ need no control either. At $\omega=1$ the minimum still gives $(2-o(1))\rho\lambda$, which equals the upper value. The boundary case is unconditional, as in Phase 20 Case 3 at $\gamma=1-\sigma$.
2. **The radius.** The mass requires $R-\lambda_N\to\infty$ faster than $B\ell_N$, and marking the upper band $\{u+1,\dots,u+\lambda'-1\}$ requires $R\ge(1+\omega+\varepsilon)\lambda_N$ (because $u\approx\omega\lambda_N$ even when $\omega>1$). Any $R_N\ge(1+\omega+\varepsilon)\lambda_N+(B+2)\ell_N$ works, and Theorem 1's choice $R_N=\lceil(2+\omega)\lambda_N+(B+2)\ell_N\rceil$ gives a full $\lambda_N$ margin. For $L_\chi(b)$ ($B=0$, $\lambda_N=\frac12\ell_N+O(1)$, $\omega=\log2$) the theorem's choice is $R_N=\lceil(2+\log2)\lambda_N+2\ell_N\rceil=\lceil3.35\,\ell_N\rceil+O(1)$, while $(1+\log2+\varepsilon)\lambda_N+2\ell_N\approx2.85\,\ell_N$ already suffices. Phase 20's radius $\lambda_N/2$ is too short in radices other than $2^k$: there $\sum_{s<N}A(s)\asymp N$, not $O(S(N))$.
3. **All-prefix, collisions, exceptional coefficients and the boundary.** The theorem holds along all $N$, not a subsequence. Collisions of arrivals are excluded by (G2). A source with a huge coefficient enters the upper bound only through its width, which is part of the first moment $W(N)$. The lower bound discards it via (G6). Sources beyond $N$ contribute only $\Lambda_N=O(\log N)$.
4. **Signed coefficients.** Nothing in the proof uses $a\ge0$. Lemma 3.2, Lemma 3.3 and the Markov bounds are sign-blind. Cancellation inside a fiber $C(t)$ is excluded on $G$ by (G2).
5. **Mixture form.** The proof only uses (W3) through the upper bound $W(N)$ and the truncated lower sum $\sum_{n\in G}\min(u(n),\lambda')$. If $u(n)/\lambda_N$ converges in distribution to a probability law $\mu$ supported on $[0,1)$ and $W(N)\le(\int x\,d\mu+o(1))S(N)\lambda_N$, replacing (G5)–(G6) by $u(n)\le\lambda_N$ (which holds for $(1-o(1))S(N)$ sources and guarantees $u(n)+\lambda'-1<2\lambda_N\le R_N$) yields $1-D_N\sim(1+\int x\,d\mu)\rho_N\lambda_N$. This mixture form is used in [euler-square-and-forms.md](euler-square-and-forms.md) §2.5.

## 2. The arithmetic of $c=1*\chi$ (Track A1)

### 2.0 External inputs

- **(i) Support asymptotic.** Landau's theorem for $\chi_4$, and Wirsing's theorem or the Selberg–Delange method for general $\chi$, give $S(x)\sim C_\chi x/\sqrt{\log x}$. Halberstam–Richert also gives $S(x)\le B_\chi\,x/\sqrt{\log2x}$ for all $x\ge1$.
- **(ii) Upper mean values.** Halberstam–Richert and Shiu: for multiplicative $g\ge0$ with $g(p^e)\le A^e$ and $g(n)\ll_\epsilon n^\epsilon$,

```math
\sum_{n\le x}g(n)\ll\frac{x}{\log x}\exp\sum_{p\le x}\frac{g(p)}p .
```

  [Shiu, J. Reine Angew. Math. **313** (1980), Theorem 1; Phase 17 eq. (1)](../phase17/multiplicative-lambert.md#2-odd-parts-and-displaced-sources)
- **(iii) Dirichlet's hyperbola bound.** $\sum_{n\le x}c(n)=L(1,\chi)x+O_q(\sqrt x)$.
- **(iv) Mertens in progressions.** $\sum_{p\le x,\,\chi(p)=1}1/p=\tfrac12\log\log x+M_\chi+O(1/\log x)$.
- **(v) Brun's upper-bound sieve.** Halberstam–Richert, *Sieve Methods*, Theorem 2.2.

### 2.1 Lemma 2.1: the exact first moment (uniform integrability)

On the support, $\log c(n)=\sum_{p^e\| n,\ \chi(p)=1}\log(e+1)$. For a split prime $p$, $n=p^em$ with $p\nmid m$ is supported if and only if $m$ is. Hence, exactly,

```math
\sum_{\substack{n\le N\\ c(n)>0}}\log c(n)=\sum_{\chi(p)=1}\ \sum_{e\ge1}\log(e+1)\Bigl(S\bigl(\tfrac N{p^e}\bigr)-S\bigl(\tfrac N{p^{e+1}}\bigr)\Bigr),
\qquad
\sum_{\substack{n\le N\\ c(n)>0}}\omega_{\rm split}(n)=\sum_{\chi(p)=1}S\bigl(\tfrac Np\bigr).
```

**Lemma 2.1.** $\displaystyle\sum_{n\le N,\ c(n)>0}\log c(n)=\Bigl(\frac{\log2}2+o(1)\Bigr)S(N)\log\log N.$

*Proof of the upper bound.* Bound each bracket by $S(N/p^e)$ and fix $\theta\in(0,\frac12)$.

- **Small primes, $e=1$, $p\le N^{1-\theta}$.** With $\eta(y)=\sup_{x\ge y}|S(x)\sqrt{\log x}/x-C_\chi|\to0$,

```math
\log2\sum_{\substack{\chi(p)=1\\ p\le N^{1-\theta}}}S\bigl(\tfrac Np\bigr)\le\log2\,\bigl(C_\chi+\eta(N^\theta)\bigr)\frac N{\sqrt{\log N}}\sum_{\substack{\chi(p)=1\\ p\le N^{1-\theta}}}\frac1{p\sqrt{1-\log p/\log N}} .
```

  Partial summation with (iv) evaluates the last sum (separating $p=2$ as $O(1)$). The weight $f(y)=(1-\log y/\log N)^{-1/2}$ is monotone on $[3,N^{1-\theta}]$ and at most $\theta^{-1/2}$, so the error term of (iv) contributes $O_\theta(1)$. The main term is $\frac12\int_{\log3/\log N}^{1-\theta}\frac{du}{u\sqrt{1-u}}=\frac12\log\log N+O(1)$, uniformly in $\theta$. This range therefore contributes $(\frac{\log 2}2C_\chi+o(1))\frac{N}{\sqrt{\log N}}LL+O_\theta(N/\sqrt{\log N})$.
- **Large primes, $N^{1-\theta}<p\le N$.** Using (i) and Chebyshev,

```math
\sum\frac Np\,\frac{B_\chi}{\sqrt{\log(2N/p)}}\ll\frac N{\log N}\int_0^{\theta\log N}\frac{dv}{\sqrt{v+\log2}}\ll\sqrt\theta\,\frac N{\sqrt{\log N}} .
```

- **Prime powers, $e\ge2$.** For $p^e\le\sqrt N$ the contribution is $\ll\frac N{\sqrt{\log N}}\sum_{p,e\ge2}\frac{\log(e+1)}{p^e}=O(S(N))$. For $p^e>\sqrt N$ it is $\ll N^{3/4+o(1)}$.

Every error is $O(S(N))=o(S(N)LL)$. The lower bound follows from Lemma 2.2 (lower tail). ∎

The full sum of widths is controlled, not merely the typical width, so no separate uniform-integrability argument is needed: the upper bound in (W3) is exactly Lemma 2.1. The script checks both exact identities for $\chi_4$ at $N=2^{14},2^{17},2^{20}$.

### 2.2 Lemma 2.2: conditional concentration, both tails

**Lemma 2.2.** For each $\varepsilon>0$ there is $c(\varepsilon)>0$ such that

```math
\#\Bigl\{n\le N:\ c(n)>0,\ \Bigl|\log c(n)-\frac{\log2}2\log\log N\Bigr|>\varepsilon\log\log N\Bigr\}\ll_\varepsilon S(N)(\log N)^{-c(\varepsilon)} .
```

*Proof.* Use the multiplicative moments $g_t(n)=\mathbf 1_{c(n)>0}\,c(n)^t$. Their split-prime value is $2^t$ on a set of primes of density $\frac12$, inert primes contribute only through $p^{2e}$, and $g_t(p^e)\le(e+1)^{|t|}\le2^e$. By (ii) and Wirsing,

```math
\sum_{n\le N}g_t(n)\asymp_t N(\log N)^{\frac12 2^t-1}\qquad(|t|\le1),\qquad\text{so}\qquad
\mathbb E\bigl[c^t\mid c>0\bigr]\asymp(\log N)^{\frac12(2^t-1)} ;
```

the logarithmic exponent is $\frac12(2^t-1)$.

- **Upper tail.** For $0<t\le1$, $\#\{\log c>(\frac{\log2}2+\varepsilon)LL\}\le e^{-t(\frac{\log2}2+\varepsilon)LL}\sum g_t\ll S(N)(\log N)^{k(t)}$, where $k(t)=\frac12(2^t-1)-t(\frac{\log2}2+\varepsilon)$. Since $k(0)=0$ and $k'(0)=-\varepsilon$, a small $t>0$ makes $k(t)<0$.
- **Lower tail.** Since $c(n)\ge2^{\omega_{\rm split}(n)}$, use $z^{\omega_{\rm split}}$ with $0<z<1$. By (ii), $\sum_{c(n)>0,\,n\le N}z^{\omega_{\rm split}(n)}\ll N(\log N)^{z/2-1}$. Hence $\#\{\omega_{\rm split}\le(\frac12-\varepsilon')LL\}\ll S(N)(\log N)^{h(z)}$ with $h(z)=\frac{z-1}2-(\frac12-\varepsilon')\log z$. Since $h(1)=0$ and $h'(1)=\varepsilon'>0$, some $z<1$ gives $h(z)<0$. Take $\varepsilon'=\varepsilon/\log 2$. ∎

For $\chi_4$ the script finds $\mathbb E[c^t\mid c>0]$ increasing in $N$ for $t>0$ and decreasing for $t<0$ between $N=2^{14}$ and $2^{20}$. The mean of $\log c/LL$ is $0.437$ at $2^{20}$, against the limit $0.347$; the difference is the $O(1)$ term in Lemma 2.1 divided by $LL=2.63$.

### 2.3 Lemma 2.3: radix valuations

**Lemma 2.3.** Let $V_b(n)=v_b(c(n))$ and $U_b(n)=c(n)/b^{V_b(n)}$.

1. **$b=2^k$.** Then $V_b=\lfloor v_2(c)/k\rfloor$ absorbs the power $2^{v_2(c(n))}$ up to the remainder $U_b(n)=2^{v_2(c)-kV_b}\,\mathrm{odd}(c(n))\le2^{k-1}\mathrm{odd}(c(n))$. Since $\sum_{n\le x}\mathrm{odd}(c(n))\ll x/\sqrt{\log x}$ (Phase 17 eq. (1)), $u_b\le1+\log_bU_b$ has bounded conditional mean, and $W(N)=O(S(N))$.
2. **$b$ not a power of $2$.** Fix an odd prime $q\mid b$. Then $V_b(n)\le v_q(c(n))=\sum_{p^e\|n,\ \chi(p)=1}v_q(e+1)$, and $q\mid e+1$ forces $e\ge q-1\ge2$. By the exact decomposition,

```math
\sum_{\substack{n\le x\\ c(n)>0}}v_q(c(n))\le\sum_{\chi(p)=1}\ \sum_{e\ge q-1}v_q(e+1)\,S\bigl(\tfrac x{p^e}\bigr)\ll\frac x{\sqrt{\log x}} .
```

  So the radix displacement $V_b(n)\le v_q(c(n))$ has bounded conditional mean. The limiting conditional mean of $v_q(c(n))$ is the local law $\Lambda_q=\sum_{\chi(p)=1}(1-\frac1p)\sum_ev_q(e+1)p^{-e}$, which equals the limit of $\mathbb E[V_b\mid c>0]$ when $b=q$ is an odd prime and is an upper bound for composite $b$ (for $\chi_4$ and $q=3$, $\Lambda_3=0.0453$; at $N=2^{20}$ the script measures $0.0556$ for $b=3$ and $0.0507$ for $b=6$).
3. **Every $b$.** Since $b^{V_b}\le c$, $\#\{n\le x:V_b(n)>H\}\le b^{-H}\sum_{n\le x}c(n)\ll xb^{-H}$.

The script asserts, for every supported $n\le2^{20}$ and $q=3,5,7$, that $q\mid c(n)$ only when some split $p^e\|n$ has $e\ge q-1$.

### 2.4 Lemma 2.4: pairs

**Lemma 2.4.** Uniformly for $1\le|h|\le\sqrt x$, $\#\{n\le x:c(n)c(n+h)>0\}\ll x\log\log x/\log x$.

*Proof.* This is Phase 20 (E3). Discard the $n$ with $q^2\mid n(n+h)$ for some $q>z_0=(\log x)^2$ with $\chi(q)=-1$; there are at most $2x/z_0+2\sqrt x$ of them. The remaining $n$ avoid the classes $0$ and $-h$ modulo every inert $q\in(z_0,\sqrt x]$ with $q\nmid h$. Brun's sieve in dimension $1$ gives $\ll x\log z_0/\log x$, uniformly in $h$. ∎

### 2.5 Proof of Theorem A1

Apply Theorem 1 with $B=0$ and $\kappa=\frac12$.

- **(W0), (W1).** By (i) and (iii), with $c(n)\le\tau(n)=n^{o(1)}$. Here $\lambda_N=\frac12\ell_N-\log_bC_\chi+o(1)$.
- **(W2).** Sum Lemma 2.4 over $|h|\le H_N=O(\ell_N)$: the exceptions number $O(N\ell_NLL/\log N)=o(S(N))$.
- **(W3) for $b=2^k$.** $\omega=0$ by Lemma 2.3(1).
- **(W3) for other $b$.** Since $u(n)\in[\log_bc(n)-V_b(n),\ \log_bc(n)-V_b(n)+1]$, Lemma 2.1 gives $W(N)\le S(N)+\frac{1}{\log b}\sum\log c=(\log2+o(1))S(N)\lambda_N$. For the lower tail, $\#\{V_b>\varepsilon\lambda_N/2\}\ll S(N)/\lambda_N=o(S(N))$ by Lemma 2.3(2), and Lemma 2.2 controls $\log_b c$. Hence $\omega=\log2<1$: the series is **below the threshold**.

Theorem 1 gives $1-D_N\sim(1+\omega)\rho_N\lambda_N$, with $\rho_N\lambda_N\sim\frac{C_\chi}{2\log b}\frac{LL}{\sqrt{\log N}}$. Sharp translation gives the supremum form. ∎

For $\chi_4$ at $N=2^{17}$ the script certifies, to within $b^{-P}\approx2^{-40}$:

| $b$ | 2 | 3 | 4 | 5 | 6 | 10 |
|---|---|---|---|---|---|---|
| $1-D_N$ | 0.59476 | 0.59045 | 0.39883 | 0.43462 | 0.37387 | 0.30267 |
| ratio to $(W+S\lambda)/N$ | 0.799 | 0.913 | 0.808 | 0.916 | 0.846 | 0.781 |
| ratio to Theorem A1 | 1.501 | 1.395 | 2.014 | 1.505 | 1.441 | 1.499 |
| mean $u_b/\lambda_N$ | 0.512 | 1.082 | 1.005 | 1.238 | 1.320 | 1.614 |

Every value also satisfies the certified Lemma 3.3 lower bound and centred-arc upper bound. At $N=2^{17}$, $\lambda_N\le2.1$ and each width carries an additive $+1$, so the mean $u_b/\lambda_N$ is far from its limits ($0$ for $b=2^k$, $\log2$ otherwise). The data show the radix effect only qualitatively: base-$3$ widths exceed base-$2$ widths (asserted). They do not test the constants.

## 3. The prime-density family (Track A2)

Let $c$ satisfy the Phase 17 hypotheses with split set $\mathcal S$ ($c(p)=2$ on $\mathcal S$, $c(p)=0$ on the other primes coprime to $q_0$) and $\kappa=1-\delta$.

**Changes to §2.**

- **Mass.** By (ii), $\mathsf A(X)=\sum_{n\le X}c(n)\ll X(\log X)^{2\delta-1}$, so (W1) holds with $B=\max(0,2\delta-1)$.
- **Pairs.** The pair sieve uses the primes outside $\mathcal S$ (density $\kappa$) in dimension $2\kappa$. It gives $\ll x(\log\log x)^{2\kappa}/(\log x)^{2\kappa}$ per shift, uniformly in $h$, and $o(x/(\log x)^\kappa)$ after summing over $|h|\le H_N=O(\ell_N)$. Only a bounded-error harmonic sum for $\mathcal S$ is used, so (W2) holds under the Phase 17 hypotheses.
- **First moment.** On the support, $\log c(n)=\omega_{\mathcal S,1}(n)\log2+\sum_{p^e\|n,\ e\ge2\text{ or }p\mid q_0}\log c(p^e)$, where $\omega_{\mathcal S,1}$ counts the primes of $\mathcal S$ with exponent exactly $1$. Each exact count $\#\{n\le N:c(n)>0,\,p^e\|n\}$ is at most $S(N/p^e)$ (since $c(p^e)$ may vanish at higher powers). With natural density and the convergent Mertens constant $+M_{\mathcal S}+o(1)$ (so that Wirsing's Satz 1 gives $S(x)\sim C_fx/(\log x)^\kappa$ uniformly), the upper bound of Lemma 2.1 goes through with the weight $(1-\log p/\log N)^{-\kappa}$, which is integrable since $\kappa<1$, yielding $\sum\log c\le(\delta\log2+o(1))S(N)LL$; the lower bound follows from $c(n)\ge2^{\omega_{\mathcal S,1}(n)}$ and the lower tail below.
- **Concentration.** Lemma 2.2 holds with centre $\delta\log2$; the lower-tail exponent is $h(z)=\delta(z-1)-(\delta-\varepsilon')\log z$.
- **Valuations.** For odd $q$, $v_q(c(p))=0$ because $c(p)\in\{0,1,2\}$, and $v_q(c(p^e))\le\log_q(e+1)$. The bound of Lemma 2.3(2) holds verbatim. For $b=2^k$, Lemma 2.3(1) uses Phase 17 eq. (1) in the form $\sum_{n\le x}\mathrm{odd}(c(n))\ll x/(\log x)^\kappa$.

Hence (W3) holds with $\omega=0$ for $b=2^k$ and with

```math
\omega=\frac{\delta\log2}{\kappa}\qquad(b\ \text{not a power of }2).
```

Since $\lambda_N=\kappa\ell_N+O(1)$, Theorem 1 gives Theorem A2(1) and (2), and the unconditional bounds in (3). The threshold $\omega=1$ is exactly $\delta=\delta^*$, where both bounds equal $2\kappa$. In the radix-$2^k$ case only $S(N)\asymp N/(\log N)^\kappa$ and the harmonic hypothesis are used, and the conclusion reads $1-D_N=(1+o(1))\rho_N\lambda_N$ with the true support count.

| $\delta$ | $\kappa$ | $\omega=\delta\log2/\kappa$ | constant$\,\cdot\log b/C_f$ (other $b$) | radix $2^k$ |
|---|---|---|---|---|
| 1/4 | 3/4 | 0.2310 | 0.9233 (exact) | 0.75 |
| 1/2 | 1/2 | 0.6931 | 0.8466 (exact) | 0.5 |
| $\delta^*=0.5906$ | 0.4094 | 1 | 0.8188 (exact) | 0.4094 |
| 3/4 | 1/4 | 2.0794 | in $[0.5000,\,0.7699]$ | 0.25 |

Euler's square $E_b^2$ ($\delta=\frac14$) and every binary theta series ($\delta=\frac12$) lie strictly below the threshold ([euler-square-and-forms.md](euler-square-and-forms.md)).

## 4. Beyond the threshold: what decides the constant

### 4.1 The mechanism

Let $\delta>\delta^*$ and let $b$ not be a power of $2$. A typical good source has $u\approx\omega\lambda_N$ with $\omega>1$. For an internal position $\lambda'<j\le u$ we have $x_{t-j}=\{b^{-j}(U+A)\}$ with $0\le A\le\frac12$. This point lies within $\eta\approx b^{-\lambda'}$ of $0$ exactly when the base-$b$ digits of $U$ in positions $j-1,\ldots,j-\lambda'-O(1)$ are all $0$ or all $b-1$. Such points do not count as far, and the deficit loses one position each. Write

```math
c(n)=M(n)\cdot2^{\omega_{\mathcal S,1}(n)},\qquad M(n)=\prod_{p^e\|n,\ e\ge2\text{ or }p\mid q_0}c(p^e).
```

$M(n)$ is tight on the support: $\mathbb P(M(n)>M_0)\to0$ as $M_0\to\infty$, uniformly in $N$, because the local factors at $e\ge2$ are summable. The displacement $V_b$ is tight by Lemma 2.3. So the question is how often $M\cdot2^m$ contains an extremal run of length about $\theta\cdot(\text{its length})$, with $\theta=\lambda'/u\to1/\omega\in(0,1)$, as $m$ runs through a window of width $\asymp\sqrt{LL}$ around $\delta LL$. On the support, the uniform point-probability bound $\mathbb P(\omega_{\mathcal S,1}=m\mid c>0)\ll1/\sqrt{LL}$ holds unconditionally for every prime set $\mathcal S$ with $\sum_{p\le x,\,p\in\mathcal S}1/p=\delta\log\log x+O(1)$ and $S(N)\gg N/(\log N)^\kappa$ via Hardy–Ramanujan's elementary Chebyshev induction: factoring $n=p_1\cdots p_m\cdot r$ ($p_i\in\mathcal S$, $r$ supported on $q_0$ and prime powers $p^e$, $e\ge2$, so $\sum 1/r<\infty$) and weighting by $\log(p_1\cdots p_m)$ gives $\#\{p_1<\dots<p_m\in\mathcal S:p_1\cdots p_m\le x\}\ll\frac x{\log x}\frac{E(x)^{m-1}}{(m-1)!}\ll\frac x{\log x}\frac{e^{E(x)}}{\sqrt{E(x)}}\ll\frac x{(\log x)^\kappa\sqrt{LL}}$ uniformly in $m\ge1$, where $E(x)=\sum_{p\le x,\,p\in\mathcal S}1/p=\delta\log\log x+O(1)$, and summing over $r$ yields the claim without requiring analytic continuation.

### 4.2 A sufficient digit hypothesis

**Hypothesis $(\mathrm R_b)$.** For every integer $M\ge1$ and every $\theta\in(0,1)$,

```math
\#\bigl\{m\le X:\ M\cdot2^m\text{ has a base-}b\text{ run of }0\text{s or of }(b-1)\text{s of length}\ge\theta\log_b(M2^m)\bigr\}=o(\sqrt X).
```

**Proposition 4.1.** $(\mathrm R_b)$ implies (W4). Hence it implies $1-D_N\sim(\kappa+\delta\log2)\Phi_N$ for every $\delta\in(0,1)$.

*Proof.* Fix $\varepsilon>0$ and $M_0$ with $\mathbb P(M>M_0)<\varepsilon$, and partition $G_0$ into the discarded set $E=\{n\in G_0:M(n)>M_0\text{ or }V_b(n)>\varepsilon\lambda_N\}$ (which has $|E|\le(\varepsilon+o(1))S(N)$) and the remainder $G_0\setminus E$. Because (W3) gives $L^1$ convergence $u(n)/\lambda_N\to\omega$, uniform integrability gives $\sum_{n\in E}Z_{t(n)}\le\sum_{n\in E}u(n)\le(\omega+\varepsilon)\lambda_N|E|+o(S(N)\lambda_N)$. Dividing by $b^{V_b}$ removes trailing digits and does not change the runs. A source in $G_0\setminus E$ has $Z_t>0$ only if $M(n)2^{\omega_{\mathcal S,1}(n)}$ has an extremal run of length $\ge(1/\omega-\varepsilon)$ times its length, and on $G_0$ we have $Z_t\le u\le(\omega+1)\lambda_N$. By the uniform Hardy–Ramanujan upper bound above and $(\mathrm R_b)$ with $X=2\delta LL$, the proportion of such sources is at most $\sum_{M\le M_0}o(\sqrt{LL})/\sqrt{LL}+\mathbb P(\omega_{\mathcal S,1}>2\delta LL)=o(1)$. Hence $\sum_{n\in G_0}Z_t\le(\varepsilon+o(1))(\omega+\varepsilon)S\lambda_N$, and $\varepsilon$ is arbitrary. ∎

The expected number of $m\le X$ with such a run is $\sum_m m\,b^{-\theta m\log_b2}<\infty$ for random digits, so $(\mathrm R_b)$ is the weak form of the heuristic "finitely many exceptions". In the script, for $b\in\{3,5,6,10\}$, $M\in\{1,3,5\}$ and $100\le m\le2000$, the longest extremal run of $M2^m$ is at most $2.23\log_bm$ digits. It is never as long as $\frac15$ of the expansion, and it reaches $\frac1{10}$ only at $m\le159$ (base $5$). This is consistent with $(\mathrm R_b)$ and proves nothing about it.

### 4.3 What the classical tools give

Write $u=\lceil\log_b(M2^m)\rceil$, and suppose that position $j\in(\lambda',u]$ is near $0$.

- **Top positions: Baker, Matveev.** Let $A$ be the nearest integer to $M2^m/b^j$, so $A<b^{u-j+1}$. Then $0<|m\log2+\log M-j\log b-\log A|\le2b^{-\lambda'}/A$. Matveev's lower bound $\exp(-C_b\log(eA M)\log m)$ forces $(u-j)\gg\lambda'/\log m$. Only the top $O(\lambda_N/\log\lambda_N)=o(\lambda_N)$ internal positions are excluded.
- **Bottom positions: Yu's $q$-adic theorem.** A zero block ending at $j$ means $M2^m\equiv r\pmod{b^j}$ with $0\le r<b^{j-\lambda'}$. For an odd prime $q\mid b$, $v_q(M2^m-r)\ge j$, while Yu's bound gives $v_q(M2^m-r)\ll_{b}\log(r+M)\log m$. This excludes only $j\le\lambda'(1+O(1/\log m))$. A $(b-1)$-block is handled the same way with $-r$.
- **Stewart's theorem.** The number of nonzero base-$b$ digits of $M2^m$ is at least $\log m/(\log\log m+C)-1$. A run of length $(1-\epsilon)u$ is compatible with this, so it gives no bound on run length.
- **Periodicity.** If $b'>1$ is the odd part of $b$, then $2^m\bmod b'^j$ has period $\mathrm{ord}_{b'^j}(2)\gg_b b'^j$. This is far longer than the window of length $\sqrt{LL}$, and even than the whole range $m\le\delta LL$. Korobov's bounds for exponential sums over $2^m\bmod b^j$ require orbit segments of length $(b^j)^{\epsilon}$; here the length is about $(\log b^j)^{1/2}$.
- **Odd versus even $b$.** If $b=2^sb'$ with $b'>1$ odd and $m\ge sj$, then $M2^m\bmod b^j=2^{sj}\cdot(M2^{m-sj}\bmod b'^j)$ in the sense of the Chinese remainder theorem. The run question again concerns the $b'$-adic orbit of $2$, so no known tool separates odd from even radices. Only $b=2^k$ is special: there $2^m$ is $1$ followed by zeros, which is precisely why the width term vanishes.

Hence the unconditional constants in Theorem A2(3) are $2\kappa$ and $\kappa+\delta\log2$, and the exact constant is $(\kappa+\delta\log2-\kappa\zeta_b)/\log b\cdot C_f$, where $\zeta_b=\lim\,(S\lambda_N)^{-1}\sum_{G_0}Z_t$ if this limit exists (matching $2\kappa$ at the extremal value $\zeta_b=\omega-1$). It is determined by the extremal-run statistics of $\{M2^m\}$ in base $b$ at relative run length $\kappa/(\delta\log2)$. We know of no result that decides $\zeta_b=0$ for any $b$ that is not a power of $2$.

## 5. Finite verification

```sh
python -B scripts/phase21_radix.py
```

For this note the script:

- builds the least-prime-factor tables to $2^{20}$;
- checks $r_2=4(1*\chi_4)$, the Landau–Ramanujan constant, and both exact first-moment identities at three cutoffs;
- computes the moments and valuation means and the $e\ge q-1$ mechanism for every supported $n\le2^{20}$;
- certifies $2^{17}+P$ digits of $L_{\chi_4}(b)$ in six radices by two integer carries (tail $c(m)\le\tau(m)\le2\sqrt m$) and computes the exact discrepancy of the digit windows. Each reported value is within $b^{-P}\le2^{-40}$ of the truth and lies between the certified Lemma 3.3 bound and the centred-arc bound.

For A2 it checks $c=1*g$ for the index-four classes modulo $5$ ($\delta=\frac14,\frac34$), the first-moment identities and Rankin moments, the extremal runs of $M2^m$, and certified discrepancies in bases $2$ and $3$. At these $N$ the class with $\delta=\frac34$ has support density $0.66$, and $1-D_N\approx0.97$ is nowhere near its asymptotic regime.

## 6. Kernel-verified Lean finite core

The finite lemmas below have been formalized, compiled, and kernel-replayed in `NormalityChecker/RadixWidthLaw.lean` (extending `CoefficientTransfer`, `Phase18Synthetic`, and `SharpTranslation`). Note that `card_far_in_gap_ge` quantifies over `Icc 1 (u + lam - 1)` (when `u > lam`, the two guaranteed far bands `[1, lam]` and `[u + 1, u + lam - 1]` are disjoint inside `[1, u + lam - 1]`). All analytic inputs of §2.0 remain outside Lean.

```lean
namespace NormalityChecker.RadixWidthLaw
open Finset CoefficientTransfer SharpTranslation Phase18Synthetic

/-- Distance to the nearest integer. -/
noncomputable def dist0 (y : ℝ) : ℝ := |y - (round y : ℝ)|

/-- Lemma 3.2(1), any radix and either sign: a unit not divisible by `b`
stays at distance `≥ b^{-j}/2` from the integers after division by `b^j`. -/
theorem dist0_div_pow_ge {b : ℕ} (hb : 2 ≤ b) {C : ℤ} (hC : ¬ (b : ℤ) ∣ C)
    {A : ℝ} (hA : |A| ≤ 1 / 2) {j : ℕ} (hj : 1 ≤ j) :
    ((b : ℝ) ^ j)⁻¹ / 2 ≤ dist0 ((C + A) / (b : ℝ) ^ j)

/-- Lemma 3.2(2): beyond the digit length the distance is the exact value. -/
theorem dist0_div_pow_eq {b : ℕ} (hb : 2 ≤ b) {C : ℤ} {u j : ℕ}
    (hu : |(C : ℝ)| < (b : ℝ) ^ u) (hj : u + 1 ≤ j) {A : ℝ} (hA : |A| ≤ 1 / 2) :
    dist0 ((C + A) / (b : ℝ) ^ j) = |C + A| / (b : ℝ) ^ j

/-- Marks per isolated source: at least `min u lam + lam - 1` shifts in `Icc 1 (u + lam - 1)` are `η`-far. -/
theorem card_far_in_gap_ge {b : ℕ} (hb : 2 ≤ b) {C : ℤ} (hC : ¬ (b : ℤ) ∣ C) {u lam : ℕ}
    (hu1 : 1 ≤ u) (hlam1 : 1 ≤ lam)
    (hu : (b : ℝ) ^ (u - 1) ≤ |(C : ℝ)|) (hu' : |(C : ℝ)| < (b : ℝ) ^ u)
    {A η : ℝ} (hA : |A| ≤ 1 / 2) (hη : 2 * η * (b : ℝ) ^ lam ≤ 1) :
    min u lam + lam - 1 ≤
      ((Icc 1 (u + lam - 1)).filter
        (fun j => η ≤ dist0 ((C + A) / (b : ℝ) ^ j))).card

/-- Isolated tails (step E4): right-isolation at radius `R` scales the tail by `b^{-R}`,
so Markov bounds the large tails by the total tail mass. -/
theorem card_large_tail_le {b : ℕ} (hb : 2 ≤ b) (T : Finset ℕ) (R : ℕ)
    (A : ℕ → ℝ) (hscale : ∀ t ∈ T, A t = A (t + R) / (b : ℝ) ^ R) (M : ℕ)
    (hT : ∀ t ∈ T, t + R < M) :
    ((T.filter fun t => 1 / 2 < |A t|).card : ℝ) ≤
      2 / (b : ℝ) ^ R * ∑ s ∈ range M, |A s|

/-- Exact first-moment decomposition for a nonnegative multiplicative `c`
(Lemma 2.1 identity; `S y = #{m ≤ y : c m ≠ 0}`). -/
theorem sum_log_eq_sum_primePow (c : ℕ → ℕ) (h1 : c 1 = 1)
    (hmul : ∀ m n, Nat.Coprime m n → c (m * n) = c m * c n) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => c n ≠ 0), Real.log (c n) =
      ∑ q ∈ (Icc 2 N).filter (fun q => IsPrimePow q ∧ c q ≠ 0),
        Real.log (c q) * ((Icc 1 (N / q)).filter
          (fun m => c m ≠ 0 ∧ ¬ q.minFac ∣ m)).card

/-- The valuation mechanism of Lemma 2.3(2). -/
theorem padicVal_succ_pos_imp {q e : ℕ} (hq : q.Prime) (h : q ∣ e + 1) : q - 1 ≤ e

/-- Finite sub-threshold upper bound (Theorem 1, upper half), from Theorem 2.2. -/
theorem width_law_upper {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    {N L : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (W P Λ : ℕ) (Phat : ℝ)
    (hunion : (farCount b (coeffSeries b a) ε N : ℝ) ≤
      W + L * (1 + P) + Λ + Phat / (((b : ℝ) - 1) * (b : ℝ) ^ L * ε)) :
    1 - radixDiscrepancy b (coeffSeries b a) N ≤
      2 * ε + (W + L * (1 + P) + Λ : ℝ) / N + Phat / (((b : ℝ) - 1) * (b : ℝ) ^ L * ε * N)
end NormalityChecker.RadixWidthLaw
```

For the lower bound (Theorem 1, lower half), `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far` already supplies the finite separation with $\varepsilon_0=\zeta$ and $\delta=\eta$, after unfolding the $\min$. Strict versus non-strict `Near` at $\eta$ needs a small margin, as in Phase 20. `coeffSeries` and `farCount` are the existing definitions in `CoefficientTransfer` and `Phase18Synthetic`. The asymptotic Theorems 1, A1 and A2 then follow on paper from these lemmas and the hypotheses (W0)–(W3).

## 7. Status

- **Kernel-verified:** circle separation `one_sub_discrepancy_ge_of_bulk_and_far`, composite-radix displacement `radixVal`/`radixUnit`/`displaced_term_eq`, `sharp_translation_isGreatest`, and `RadixWidthLaw.*` (`dist0_div_pow_ge`, `dist0_div_pow_eq`, `card_far_in_gap_ge`, `card_large_tail_le`, `sum_log_eq_sum_primePow`, `padicVal_succ_pos_imp`, `width_law_upper`).
- **Paper proofs (this note):** Theorem 1; Lemmas 2.1–2.4 from the inputs (i)–(v); Theorems A1 and A2(1)–(3); Proposition 4.1.
- **Conditional:** the exact constant in Theorem A2(3) for $\delta>\delta^*$, under $(\mathrm R_b)$.
- **External inputs:** Landau, Wirsing and Selberg–Delange; Halberstam–Richert and Shiu; Dirichlet's hyperbola method; Mertens in progressions; Brun's sieve; Hardy–Ramanujan Chebyshev induction (in Proposition 4.1). §4.3 cites, without using, Matveev's and Yu's linear-forms bounds, Stewart (1980) and Korobov.
- **Finite evidence:** [`scripts/phase21_radix.py`](../../scripts/phase21_radix.py). Its ratios do not test the leading constants.

