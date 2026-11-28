# Dirichlet GRH and moving windows: Paper VI planting, GF-22 windows, and the exponent in Mira Cult's local-limit argument

Phase 25, Addendum Track J (Addendum sections D, E and F). Companion script: [`scripts/phase25_grh_windows.py`](../../scripts/phase25_grh_windows.py) (standard library only; exact integer and `fractions.Fraction` arithmetic, Miller–Rabin and Pollard–Brent factorization; exit code 0). Sources read for this note: [`papers/06-multiplicative-lambert/paper.tex`](../../papers/06-multiplicative-lambert/paper.tex) (cited as *Paper VI*; labels such as `prop:planting` refer to its LaTeX labels), [`notes/phase22/odd-characters-and-kernel-quotient.md`](../phase22/odd-characters-and-kernel-quotient.md) §5 (the proof of `GF-22`, cited as *GF-22*), and the Phase 13 audit of Mira Cult's claim 0002, [`notes/phase13/erdos-borwein.md`](../phase13/erdos-borwein.md) and [`notes/phase13/reviews/erdos-local-limit.md`](../phase13/reviews/erdos-local-limit.md) (cited as *P13* and *P13-R*).

**The hypothesis.** For an integer $q\ge1$, **GRH($q$)** is the statement that for every Dirichlet character $\chi$ modulo $q$, every nontrivial zero of $L(s,\chi^*)$ has real part $1/2$, where $\chi^*$ is the primitive character that induces $\chi$. For $q=1$ this is the Riemann hypothesis. GRH($q$) is equivalent to the Riemann hypothesis for the Dedekind zeta function of $\mathbb Q(\zeta_q)$. **Dirichlet GRH** is GRH($q$) for every $q$. Both are unproved conjectures. In this note they are explicit external analytic hypotheses. Nothing here proves them or tests them. Finite computations cannot test them (§8, S2 and S4).

**Evidence labels.** We use the repository labels of [`docs/research-objectives.md`](../../docs/research-objectives.md).

- *Conditional*: a written deduction from the named external hypothesis (GRH($q_0$), GRH for the moduli $q'$ of §2.5, or Dirichlet GRH). These deductions are written proofs only. None is kernel-verified, and none changes a benchmark status.
- *Paper proof*: a complete written argument in this note, with no unproved hypothesis.
- *Lean-supported paper proof*: a written proof whose finite steps are existing kernel-verified Lean declarations.
- *Finite certificate*: an exact computation of a finite statement in the script.
- *Numerical*: floating-point measurements, which are not evidence.
- *External input*: a published theorem used as a black box.
- *Repository input*: a result of an earlier phase used without reproof; its own label is stated.
- *Open*.

Finite digit statistics are never asymptotic evidence. Cross-model review is not independent human peer review. No result in this note has yet been reviewed by anyone.

**Scope.** No file other than this note and its script was created or edited. In particular Paper VI, `docs/registry/GF.toml` and the benchmark files are unchanged. Appendix A is a draft insert for a future revision of Paper VI that the owner would have to authorize. Conditional results never change a benchmark status. None of the 50 roster constants `BC-01`…`BC-50` changes status.

---

## Summary of results

| # | Result | Evidence |
| --- | --- | --- |
| A | **GRH short-interval estimate in a progression** (Theorem A, Corollaries A.2–A.3). Under GRH($q$), uniformly for $x\ge2$ and $(u,q)=1$, $\lvert\psi(x;q,u)-x/\varphi(q)\rvert\le C_0\sqrt x\log^2(qx)$ with an absolute constant $C_0$. Hence $\psi(X+H;q,u)-\psi(X;q,u)=H/\varphi(q)+O(\sqrt X\log^2(qX))$ for $1\le H\le X$, with the matching estimates for $\theta$ and $\pi$. In particular Paper VI's hypothesis $(\mathrm P_\nu)$ holds for **every** $1/2<\nu<1$, with $c_P=1/(2\varphi(q_0))$ | Conditional (GRH($q$); for $(\mathrm P_\nu)$ only GRH($q_0$)) |
| B | **Paper VI for every $a>1/2$** (Theorem B). Assume (H1)–(H4) and GRH($q_0$). Then `prop:planting` holds with $\nu_*=1/2$. For every fixed $1/2<a\le1$, uniformly for $N^a\le H\le N$: $\#_w(N,H)\asymp_{w,a}H/(\log N)^{\kappa}$ for every word $w$ containing a $1$, and $H-\#_{0^k}(N,H)\asymp_{k,a}H/(\log N)^\kappa$. Every word occurs in every window $[N,N+\lceil N^a\rceil)$ with $N\ge N_0(w,a)$. For $L_{\chi_4}$ only RH for $\zeta(s)$ and for $L(s,\chi_{-4})$ is used | Conditional (GRH($q_0$)) |
| C | **Window discrepancy gap** (Proposition C). Put $D_{N,H}(x)=D_H(\{2^Nx\})$. If $(\mathrm P_\nu)$ holds for every $\nu_*<\nu<1$, then for every fixed $\nu_*<a\le1$ we have $1-D_{N,H}(L)\asymp_a(\log\log N)/(\log N)^{\kappa}$ uniformly for $N^a\le H\le N$. The upper bound holds for every $a>0$. Corollary C.2 gives the window translation identity $\sup_x\lvert D_{N,H}(x+L)-D_{N,H}(x)\rvert=1-D_{N,H}(L)$ | Lean-supported paper proof for $a>0.53$ (Kumchev) and $a>7/12$ (PPS), new and unreviewed; Conditional (GRH($q_0$)) for $a>1/2$ |
| D | **GF-22 in moving windows** (Theorem D). Assume Dirichlet GRH. For every nonprincipal $\chi$, every nonzero additive $\Phi:\mathbb Z[\zeta_h]\to\mathbb Z$, every radix $b\ge2$, every word $w$ and every fixed $1/2<a\le1$: $\#_w(N,H)\ge H\exp(-C_w\log\log N\cdot\log\log\log N)$ uniformly for $N^a\le H\le N$. Every exceptional set of the GF-22 proof was rebuilt on the moving interval. None is a prefix estimate, and none needs Shiu, Brun–Titchmarsh or Rankin beyond the elementary Lemma E.2 | Conditional (GRH for the moduli $q'=qQ(N,w)$, which grow with $N$) |
| D.2 | **GF-22 in near-full windows, unconditionally** (Proposition D.2). The same lower bound holds for $N\exp(-c_3\sqrt{\log N})\le H\le N$. This uses Landau–Page with **three** disjoint kill families | Paper proof (repository input: GF-22's (E1)) |
| E | **Additivity of $\Phi$ is necessary** (Proposition E). For every nonprincipal $\chi$ the nonadditive $\Phi=\mathbf 1_{z\ne0}$, which has $\Phi(0)=0$, gives a number $F_b(\Phi\circ(1*\chi))$ that is **not** disjunctive in any base $b\ge2$. For $\chi_{-4}$ the word $1111$ never occurs, and for the cubic character mod 7 the word $1^8$ never occurs. The HEAD wording of `GF-22` ("every nonzero integer-valued function $\Phi$ … with $\Phi(0)=0$"), still displayed in the generated `docs/results.md`, is false as stated. The working-tree registry text (additive $\Phi$) matches the proof | Paper proof; finite certificate (first $10^5$ digits) |
| F | **Mira Cult's exponent $7/12$** (§3). The exponent enters her weighted local-limit argument only through a positive power level of distribution $Q=X^\rho$ with arbitrary log saving for the primes in the short interval. No step needs $\rho\ge\rho_0$; the unconditional argument already lets $\rho\to0$ as $a\downarrow7/12$. Under Dirichlet GRH the summed error is $\ll Q\sqrt X\log^2(QX)$, which gives the level $\rho<\vartheta-1/2$ with a power saving. The reviewed argument therefore extends to **every fixed $1/2<a\le1$** for the Erdős–Borwein constant $E$ | Conditional (Dirichlet GRH); dependency audit of Mira Cult's argument, which inherits the residual verification burden recorded in P13 |

**What is new.** Paper VI's own §10 (`subsec:range`, question Q2) already notes that apart from the prime input "the remaining steps need only $a>1/2$". Theorem B is therefore the expected conditional consequence. Its content is the line-by-line verification in §2.3. The new mathematical items are Proposition C, the moving-window reconstruction of GF-22 (Theorem D and Proposition D.2), Proposition E, and the dependency analysis in §3.

---

## 0. Definitions and notation

$p$ and $\ell$ denote primes and $\log$ is natural. For $(u,q)=1$,

```math
\psi(x;q,u)=\sum_{\substack{n\le x\\ n\equiv u\ (q)}}\Lambda(n),\qquad
\theta(x;q,u)=\sum_{\substack{p\le x\\ p\equiv u\ (q)}}\log p,\qquad
\pi(x;q,u)=\sum_{\substack{p\le x\\ p\equiv u\ (q)}}1 .
```

For a character $\chi$ we write $\psi(x,\chi)=\sum_{n\le x}\chi(n)\Lambda(n)$. Nontrivial zeros are written $\rho=\beta+i\gamma$.

**Paper VI data** (Paper VI §1.1). (H1)–(H4) fix $q_0$, a reduced class $a_0\bmod q_0$, a set $S$ of primes containing every $p\equiv a_0\pmod{q_0}$ with $\sum_{p\le x,\,p\in S}1/p=\delta\log\log x+O(1)$ and $0<\delta<1$, and a multiplicative $c\ge0$ with $c(p^e)\le e+1$, $c(p)=2$ on $S$, $c(p)=0$ at the other primes not dividing $q_0$, and $c(p_0^{2u})=2u+1$ for one $p_0\in S$. Put $\kappa=1-\delta$, $L=\sum_n c(n)2^{-n}$ and $x_n=\{2^nL\}$. For a binary word $w$ of length $k$ and value $u$, the cylinder is $I_w=[u2^{-k},(u+1)2^{-k})$ and

```math
\#_w(N,H)=\#\{N\le n<N+H:\ x_n\in I_w\}.
```

**$(\mathrm P_\nu)$** (Paper VI, display `eq:Pnu`). For $1/2<\nu<1$, $(\mathrm P_\nu)$ holds if there are $c_P>0$ and $X_P$ such that, for all real $X\ge X_P$ and $X>Y\ge(X+Y)^\nu$,

```math
\#\{X<p\le X+Y:\ p\equiv a_0\ (\mathrm{mod}\ q_0)\}\ \ge\ c_P\,\frac{Y}{\log X}.
```

**Window discrepancy.** $D_N(x)$ is the extreme discrepancy of $(\{2^nx\})_{0\le n<N}$ over intervals $[s,t)\subseteq[0,1)$, as in Paper VI. For $N\ge0$ and $H\ge1$ put

```math
D_{N,H}(x)=D_H(\{2^Nx\}),
```

the extreme discrepancy of $(\{2^nx\})_{N\le n<N+H}$, because $\{2^n\{2^Nx\}\}=\{2^{n+N}x\}$. Write $F_{N,H}(s,t)=\#\{N\le n<N+H:\ s\le\{2^nL\}<t\}/H$.

**GF-22 data** (GF-22 §5). $\chi$ is a nonprincipal character modulo $q$ of order $h$, $c_\chi=1*\chi$, and $\Phi:\mathbb Z[\zeta_h]\to\mathbb Z$ is nonzero and additive. Put $c_\Phi(n)=\Phi(c_\chi(n))$, so that $\lvert c_\Phi(n)\rvert\le C_\Phi\tau(n)$ with $C_\Phi=\max_j\lvert\Phi(\zeta_h^j)\rvert$, and put $x=F_b(c_\Phi)=\sum_n c_\Phi(n)b^{-n}$. The base-$b$ digits are $d_n(x)=\lfloor b\{b^{n-1}x\}\rfloor$. The word $w$ (length $W$) occurs at start $n$ if $d_{n+1}\cdots d_{n+W}=w$, and $\#_w(N,H)$ counts starts $N\le n<N+H$. $T_P=\sum_{k\ge1}c_\Phi(P+k)b^{-k}$, so $\{b^Px\}=\{T_P\}$.

**Level of distribution** (§3). A short-interval Bombieri–Vinogradov estimate has level $Q=x^\rho$ if, for intervals of length $y=x^\vartheta$,

```math
\sum_{q\le Q}\max_{(u,q)=1}\max_{h\le y}\max_{x/2<z\le x}\Bigl\lvert\psi(z+h;q,u)-\psi(z;q,u)-\frac h{\varphi(q)}\Bigr\rvert\ \ll_B\ \frac{y}{(\log x)^B}\qquad\text{for every }B .
```

---

## 1. Statements

**Theorem A (Conditional on GRH($q$)).** There is an absolute constant $C_0$ such that, if GRH($q$) holds, then for all real $x\ge2$ and $(u,q)=1$

```math
\Bigl\lvert\psi(x;q,u)-\frac{x}{\varphi(q)}\Bigr\rvert\le C_0\sqrt x\,\log^2(qx).
```

Consequently, for $X\ge2$ and $1\le H\le X$,

```math
\Bigl\lvert\psi(X+H;q,u)-\psi(X;q,u)-\frac H{\varphi(q)}\Bigr\rvert\le 2C_0\sqrt{2X}\,\log^2(2qX).
```

**Lemma A.1 (prime powers; elementary).** For $x\ge2$ let $P(x)=\#\{(p,k):\ k\ge2,\ p^k\le x\}$. Then $P(x)\le\lfloor\sqrt x\rfloor+\lfloor x^{1/3}\rfloor\lfloor\log_2x\rfloor$. The prime powers $p^k\in(X,X+H]$ with $k\ge2$ contribute at most $P(2X)\log(2X)\ll\sqrt X\log X$ to $\psi(X+H;q,u)-\psi(X;q,u)$ when $H\le X$.

**Corollary A.2 (Conditional on GRH($q$)).** With an absolute constant $C_2$, for $X\ge2$, $1\le H\le X$ and $(u,q)=1$:

```math
\Bigl\lvert\theta(X+H;q,u)-\theta(X;q,u)-\frac H{\varphi(q)}\Bigr\rvert\le C_2\sqrt X\log^2(2qX),
```

```math
\pi(X+H;q,u)-\pi(X;q,u)=\frac1{\varphi(q)}\int_X^{X+H}\frac{dt}{\log t}+O\Bigl(\frac{\sqrt X\log^2(2qX)}{\log X}\Bigr).
```

**Corollary A.3 (Conditional on GRH($q_0$)).** For every fixed $1/2<\nu<1$, $(\mathrm P_\nu)$ holds with $c_P=1/(2\varphi(q_0))$. Moreover the asymptotic formula of Paper VI `lem:shortprimes` holds for every $1/2<\nu\le1$:

```math
\#\{X<p\le X+Y:\ p\equiv a_0\ (\mathrm{mod}\ q_0)\}=(1+o(1))\frac{Y}{\varphi(q_0)\log X},
```

uniformly for real $X>Y\ge(X+Y)^\nu$ as $X\to\infty$.

**Theorem B (Conditional on GRH($q_0$)).** Assume (H1)–(H4) and GRH($q_0$). Then Paper VI `prop:planting` holds with $\nu_*=1/2$. Consequently, for every fixed $1/2<a\le1$ and every binary word $w$ of length $k$, there is $N_0(w,a)$ such that for all $N\ge N_0$ and $N^a\le H\le N$ the following hold.

1. If $w$ contains a $1$, then $\#_w(N,H)\asymp_{w,a}H/(\log N)^\kappa$.
2. $H-\#_{0^k}(N,H)\asymp_{k,a}H/(\log N)^\kappa$.
3. Every finite word occurs in every window $[N,N+\lceil N^a\rceil)$ with $N\ge N_0(w,a)$.

The upper bounds in 1 and 2 are unconditional for every $0<a\le1$ (Paper VI `prop:upper`).

**Proposition C (window discrepancy gap; parameterized).** Assume (H1)–(H4). Let $1/2\le\nu_*<1$ be such that $(\mathrm P_\nu)$ holds for every $\nu_*<\nu<1$. For every fixed $\nu_*<a\le1$ there are $N_0(a)$ and constants depending on $a$ and the data such that, for $N\ge N_0(a)$ and $N^a\le H\le N$,

```math
1-D_{N,H}(L)\asymp_a\frac{\log\log N}{(\log N)^{\kappa}} .
```

The upper bound $1-D_{N,H}(L)\ll_a(\log\log N)/(\log N)^\kappa$ holds for every fixed $0<a\le1$ under (H1)–(H3). There are three instances. With $\nu_*=7/12$ (PPS, Paper VI `lem:shortprimes`) and with $\nu_*=0.53$ (Kumchev, Paper VI `lem:kumchevfixed`) the statement is unconditional. With $\nu_*=1/2$ it is Conditional on GRH($q_0$) by Corollary A.3.

**Corollary C.2 (window translation identity).** For every $N\ge0$ and $H\ge1$,

```math
\sup_{x\in\mathbb R}\bigl\lvert D_{N,H}(x+L)-D_{N,H}(x)\bigr\rvert=1-D_{N,H}(L),
```

with the supremum attained at $x=0$.

**Theorem D (Conditional on Dirichlet GRH).** Let $\chi$, $\Phi$, $c_\Phi$, $b$ and $x=F_b(c_\Phi)$ be as in §0. Assume GRH($q'$) for the moduli $q'=qQ(N,w)$ constructed in §2.5; Dirichlet GRH suffices. For every word $w$ of length $W$ over $\{0,\dots,b-1\}$ there is $C_w$, depending on $w,b,\chi,\Phi$, and for every fixed $1/2<a\le1$ there is $N_0(w,a)$, such that for $N\ge N_0$ and $N^a\le H\le N$

```math
\#_w(N,H)\ \ge\ H\exp\bigl(-C_w\,\log\log N\cdot\log\log\log N\bigr).
```

In particular $w$ occurs in every window $[N,N+\lceil N^a\rceil)$ for $N\ge N_0(w,a)$.

**Proposition D.2 (unconditional near-full windows).** In the setting of Theorem D, without GRH, there is $c_3>0$ depending only on the constants of GF-22's input (E1) such that the bound of Theorem D holds for $N\ge N_0(w)$ and $N\exp(-c_3\sqrt{\log N})\le H\le N$.

**Proposition E (additivity cannot be dropped).** Let $\chi$ be any nonprincipal Dirichlet character and let $\Phi_{\rm ind}(z)=1$ for $z\ne0$ and $\Phi_{\rm ind}(0)=0$. Then $\Phi_{\rm ind}$ is nonzero on the range of $c_\chi$, satisfies $\Phi_{\rm ind}(0)=0$, and is not additive. For every $b\ge2$ the number $F_b(\Phi_{\rm ind}\circ c_\chi)$ is not disjunctive in base $b$. If $p\nmid q$ is a prime with $\chi(p)$ of exact order $d\ge2$, the word $1^{p^d}$ never occurs, and for $b\ge3$ the digit $2$ never occurs. For $\chi_{-4}$ already $1111$ never occurs. For the cubic character modulo 7 already $1^8$ never occurs.

**Audit conclusion F (Conditional on Dirichlet GRH; dependency audit).** §3 states it precisely.

---

## 2. Proofs

### 2.1 Proof of Theorem A, Lemma A.1 and Corollary A.2

We use two classical inputs, listed in §5.

- (X1) The truncated explicit formula for $\psi(x,\chi)$ with primitive $\chi$, together with the estimate of the constant $b(\chi)$: Davenport, Ch. 17 for $\zeta$ and Ch. 19 for $L(s,\chi)$; equivalently Montgomery–Vaughan I, Ch. 12.
- (X2) The zero count: for primitive $\chi$ modulo $q^*$ and real $t$, the number of zeros with $\lvert\gamma-t\rvert\le1$ is $\ll\log(q^*(\lvert t\rvert+2))$ (Davenport, Chs. 15–16).

*Step 1 (orthogonality).* $\psi(x;q,u)=\varphi(q)^{-1}\sum_{\chi\bmod q}\bar\chi(u)\psi(x,\chi)$. The principal character contributes $\varphi(q)^{-1}\psi(x,\chi_0)$.

*Step 2 (reduction to primitive characters).* If $\chi\bmod q$ is induced by $\chi^*\bmod q^*$, where $q^*=1$ and $\chi^*=1$ for $\chi=\chi_0$, then

```math
\lvert\psi(x,\chi)-\psi(x,\chi^*)\rvert\le\sum_{p\mid q}\sum_{k:\,p^k\le x}\log p\le\omega(q)\log x\le 2\log q\,\log x .
```

*Step 3 (explicit formula).* Let $\chi$ be primitive modulo $q^*$, let $x\ge4$ and let $2\le T\le x$. By (X1),

```math
\psi(x,\chi)=E(\chi)\,x-\sum_{\lvert\gamma\rvert<T}\frac{x^\rho}{\rho}+r(\chi,x)+O\Bigl(\frac xT\log^2(q^*xT)+\log x\Bigr),
```

where $E(\chi)=1$ if $q^*=1$ and $E(\chi)=0$ otherwise. For $q^*=1$, $r=O(1)$. For $q^*>1$ with parity $\mathfrak a\in\{0,1\}$,

```math
r(\chi,x)=-(1-\mathfrak a)\log x-b(\chi)+\sum_{m\ge1}\frac{x^{\mathfrak a-2m}}{2m-\mathfrak a},\qquad
b(\chi)=-\sum_{\lvert\gamma\rvert<1}\frac1\rho+O(\log q^*).
```

*Step 4 (use of GRH).* Assume every nontrivial zero has $\beta=1/2$. For $q^*>1$, group the zeros with $\lvert\gamma\rvert<1$ with $b(\chi)$:

```math
-\sum_{\lvert\gamma\rvert<T}\frac{x^\rho}{\rho}-b(\chi)=-\sum_{1\le\lvert\gamma\rvert<T}\frac{x^\rho}{\rho}-\sum_{\lvert\gamma\rvert<1}\frac{x^\rho-1}{\rho}+O(\log q^*).
```

Under GRH $\lvert\rho\rvert\ge1/2$, so $\lvert(x^\rho-1)/\rho\rvert\le2(\sqrt x+1)$. By (X2) there are $\ll\log 2q^*$ zeros with $\lvert\gamma\rvert<1$, so the middle sum is $\ll\sqrt x\log2q^*$. Without GRH a zero near $s=0$ could make this sum large; this is the only place where the location of low zeros matters. For the remaining zeros, $\lvert x^\rho/\rho\rvert\le\sqrt x/\lvert\gamma\rvert$. By (X2),

```math
\sum_{1\le\lvert\gamma\rvert<T}\frac1{\lvert\gamma\rvert}\le\sum_{k=1}^{\lceil T\rceil}\frac{\#\{k\le\lvert\gamma\rvert<k+1\}}{k}\ll\sum_{k\le T+1}\frac{\log(q^*(k+2))}{k}\ll\log(q^*(T+2))\,(1+\log T)\ll\log^2(q^*T).
```

The script (S2) checks this harmonic bookkeeping numerically. The trivial-zero series is at most $2$ for $x\ge2$, and $(1-\mathfrak a)\log x\le\log x$. For $q^*=1$ every zero has $\lvert\gamma\rvert>14$, so the first sum is bounded directly. Take $T=\sqrt x$. Then $\log(q^*xT)\le\frac32\log(q^*x)$ (S2, exact), so $(x/T)\log^2(q^*xT)\le\frac94\sqrt x\log^2(q^*x)$. Hence there is an absolute $C_1$ with

```math
\lvert\psi(x,\chi)-E(\chi)x\rvert\le C_1\sqrt x\log^2(q^*x)\qquad(x\ge2,\ \chi\ \text{primitive modulo}\ q^*\mid q).
```

For $2\le x<4$ this holds trivially.

*Step 5 (assembly).* By Steps 1, 2 and 4,

```math
\Bigl\lvert\psi(x;q,u)-\frac x{\varphi(q)}\Bigr\rvert\le\frac1{\varphi(q)}\sum_{\chi\bmod q}\bigl(C_1\sqrt x\log^2(qx)+2\log q\log x\bigr)\le C_0\sqrt x\log^2(qx).
```

The short-interval form follows by subtracting the estimates at $X+H\le2X$ and at $X$. ∎

All constants are absolute and effective in principle; we do not compute them. Davenport, Ch. 20 states the conclusion $\psi(x;q,a)=x/\varphi(q)+O(x^{1/2}\log^2x)$ under GRH for $q\le x$. We have not rechecked page or equation numbers of either book against the printed text in this session.

*Proof of Lemma A.1.* A pair with $k=2$ has $p\le\sqrt x$, which leaves at most $\lfloor\sqrt x\rfloor$ choices. A pair with $3\le k\le\log_2x$ has $p\le x^{1/3}$, which leaves at most $\lfloor x^{1/3}\rfloor$ choices for each of at most $\lfloor\log_2x\rfloor$ values of $k$. Each prime power $p^k\le2X$ contributes $\log p\le\log 2X$. S3 checks the count bound exhaustively at every jump point $x\le10^6$. ∎

*Proof of Corollary A.2.* By Theorem A and Lemma A.1, $\theta(X+H;q,u)-\theta(X;q,u)=H/\varphi(q)+O(\sqrt X\log^2(2qX))$, since $\sqrt X\log X\le\sqrt X\log^2(2qX)$. For the prime count, write $\Delta(t)=\theta(t;q,u)-\theta(X;q,u)-(t-X)/\varphi(q)$, so that $\lvert\Delta(t)\rvert\le C_2\sqrt X\log^2(2qX)$ for $X\le t\le X+H$. Partial summation gives

```math
\pi(X+H;q,u)-\pi(X;q,u)=\int_{X^+}^{X+H}\frac{d\theta(t;q,u)}{\log t}=\frac1{\varphi(q)}\int_X^{X+H}\frac{dt}{\log t}+\frac{\Delta(X+H)}{\log(X+H)}+\int_X^{X+H}\frac{\Delta(t)}{t\log^2t}\,dt .
```

The last two terms are $O(\sqrt X\log^2(2qX)/\log X)$, because $\int_X^{2X}dt/(t\log^2t)\le1/\log X$. ∎

### 2.2 Proof of Corollary A.3

Fix $1/2<\nu<1$ and let $X>Y\ge(X+Y)^\nu$, so $X^\nu\le Y\le X$. Corollary A.2 with $q=q_0$ and $H=Y$ gives

```math
\#\{X<p\le X+Y:\ p\equiv a_0\ (q_0)\}\ \ge\ \frac{\theta(X+Y;q_0,a_0)-\theta(X;q_0,a_0)}{\log(2X)}\ \ge\ \frac{Y/\varphi(q_0)-C_2\sqrt X\log^2(2q_0X)}{\log 2X}.
```

Since $X^{\nu-1/2}/\log^2(2q_0X)\to\infty$, there is $X_P(q_0,\nu)$ beyond which $C_2\sqrt X\log^2(2q_0X)\le Y/(4\varphi(q_0))$. For $X\ge4$ also $\log2X\le\frac32\log X$. Hence the count is at least $\frac34\cdot\frac23\,Y/(\varphi(q_0)\log X)=Y/(2\varphi(q_0)\log X)$. The asymptotic formula follows from the two-sided form in Corollary A.2, because $\int_X^{X+Y}dt/\log t=(1+O(1/\log X))\,Y/\log X$. Only the finitely many $L$-functions modulo $q_0$ enter, so the hypothesis is GRH($q_0$). For Paper VI's examples this means $\zeta(s)$ and $L(s,\chi_{-4})$ when $q_0=4$, and the four $L$-functions modulo 5 for `ex:quarter`. ∎

S2 shows that even with constant $1$ the error $\sqrt X\log^2X$ falls below $X^\nu$ only for $\log_{10}X\ge93.3$ at $\nu=0.55$, and only for $\log_{10}X\ge632.7$ at $\nu=0.51$. The conditional estimate says nothing about any computable range.

### 2.3 Proof of Theorem B: verification of every hypothesis of `prop:planting`

`prop:planting` assumes "$1/2\le\nu_*<1$ such that $(\mathrm P_\nu)$ holds for every $\nu_*<\nu<1$". Its proof sets

```math
\theta=\min\{1/4,(a-\nu_*)/2\},\qquad \nu=\tfrac12(\nu_*+a-\theta),\qquad \beta=\tfrac12+\frac1{4(a-\theta)},\qquad z_0=(\log N)^2 .
```

We take $\nu_*=1/2$, which the statement allows, and use Corollary A.3. The following table lists every place in the proof where the window length or the prime input enters, together with the status at $\nu_*=1/2$ and $1/2<a\le1$. S1 checks each parameter inequality exactly on a grid of 1001 exponents $a\in(1/2,1]$, and also for $\nu_*=0.53$ and $\nu_*=7/12$.

| Step of `prop:planting` | Requirement | Status at $\nu_*=1/2$ |
| --- | --- | --- |
| Parameter choice | $\nu_*<\nu<a-\theta$ and $1/(2(a-\theta))<\beta<1$, both equivalent to $a-\theta>1/2$ | $a-\theta\ge a-\frac{a-1/2}2=\frac a2+\frac14>\frac12$ ✓ |
| `lem:small` (small factors $m\le N^\theta$) | $0<\theta<1/2$ | $0<\theta\le1/4$ ✓ (constant $\asymp\theta^\delta$) |
| `eq:Pm`: $\lvert\mathcal P_m\rvert\ge c_PY/(2\log N)$ on $(X,X+Y]$, $X=(N+j_0-1)/b$, $Y=H/b$ | $(\mathrm P_\nu)$ with $Y\ge(X+Y)^\nu$ | $Y\gg_wN^{a-\theta}$, $X+Y\le3N$, $\nu<a-\theta$ ✓; $(\mathrm P_\nu)$ by Corollary A.3 (**Conditional**) |
| $p\in\mathcal P_m$ satisfies $p>X>b$ and $p>2\sqrt{3N}$ | $1-\theta>1/2$ | $\theta\le1/4$ ✓ |
| (I2) vanishing of the nearby coefficients: Selberg sieve `lem:selberg` on $(X,X+Y]$ with $z=Y^{1/4}$, $w=Y^{1/32}>z_0$; remainder $Y^{1/2}(1+\log Y)^2$ | $Y\ge N^{c}$ for some fixed $c>0$ | $Y\gg N^{a-\theta}$ with $a-\theta>1/2$ ✓ |
| (I2) integers with $q^2\mid bp+h$, $q\in\mathcal Q\cap(z_0,z]$ | at most $Y/z_0+z$ | ✓ (no condition) |
| (I3) far tail for $J<j\le N$: Brun–Titchmarsh `thm:mv` for moduli $d'\le2\sqrt N\le Y^\beta$ | $(a-\theta)\beta>1/2$ | $(a-\theta)\beta=\frac{a-\theta}2+\frac14>\frac12$ ✓ |
| (I3) far tail for $j>N$ | none | ✓ |
| Counting and injectivity of $(m,p)\mapsto n$ | none | ✓ |

Every exceptional set in the proof is bounded on the actual short interval $(X,X+Y]$ of primes $p$, with $Y=H/b$. These are the (I2) failures, $O(Y(\log\log N)^{1+\kappa}(\log N)^{-1-\kappa})$; the square-divisible $p$, $O(Y/z_0+z)$; and the (I3) failures, $O(Y\log\log N\,(\log N)^{-10\log2})$. Each is $o(Y/\log N)$ uniformly in $H\in[N^a,N]$. No prefix estimate occurs, so nothing has to be localized. Hence `prop:planting` holds with $\nu_*=1/2$, Conditional on GRH($q_0$).

The deduction in Paper VI §6 (`sec:words`) then applies verbatim.

1. The upper bound is `prop:upper`(b). Every 0-isolated $n\in[N,N+H)$ has $x_n\in I_w$ (`lem:isolated`), which gives the lower bound $c_*H/(\log N)^\kappa$.
2. The upper bound is `prop:upper`(c). For the lower bound, every start $n$ with $x_n\ge1/2$ begins with the digit $1$ and is rejected for $0^k$. There are $\#_1(N,H)\gg H/(\log N)^\kappa$ of them by item 1 with $w=1$.
3. For $w$ containing a $1$, item 1 gives $\#_w>0$. For $0^k$, item 2 gives $\#_{0^k}\ge H-CH/(\log N)^\kappa>0$. ∎

*Remark B.1.* As written, the proof of `prop:planting` needs $a>1/2$ also outside the prime input. The far tail needs $a-\theta>1/2$, and $\theta>0$ is needed. At $a=1/2$ one gets $\theta=0$ and $\beta=1$, so the construction degenerates (S1 boundary check). We do not claim that $1/2$ is a barrier for other methods.

### 2.4 Proof of Proposition C and Corollary C.2

The two finite inequalities below are kernel-verified Lean declarations **for every real number**, quoted in Paper VI §7:

- `Phase17DiscrepancyBounds.one_sub_discrepancy_le_one_bits`: for real $y$ and integers $\ell,H\ge1$, $1-D_H(y)\le2^{-\ell}+(\ell-1)/H+\ell F_H(y;1/2,1)$;
- `Phase17DiscrepancyBounds.one_sub_discrepancy_ge_of_separated_mass`: if $0<\varepsilon\le1/6$, $\Delta\le\varepsilon$, $F_H(y;0,\varepsilon)\ge\Delta$ and $F_H(y;3\varepsilon,1/2)\ge\Delta$, then $1-D_H(y)\ge\Delta$.

Here $F_H(y;s,t)=\#\{0\le n<H:\ s\le\{2^ny\}<t\}/H$. We apply both to $y=\{2^NL\}$. Since $\{2^ny\}=x_{N+n}$, we get $F_H(y;s,t)=F_{N,H}(s,t)$ and $D_H(y)=D_{N,H}(L)$.

*Upper bound (every $0<a\le1$, (H1)–(H3)).* By `prop:upper`(a) with $s=0$, $F_{N,H}(1/2,1)\le C(\log N)^{-\kappa}$ for $N^a\le H\le N$. Take $\ell=\lceil\kappa\log_2\log N\rceil$. Then $2^{-\ell}\le(\log N)^{-\kappa}$ and $(\ell-1)/H\le(\kappa/\log2)\log\log N/N^a\ll\log\log N/N^a$, so $1-D_{N,H}(L)\ll_a\log\log N/(\log N)^\kappa$.

*Lower bound ($a>\nu_*$).*

1. Fix $\nu_*<a'<a$ and put $R=\lfloor\frac\kappa2\log_2\log N\rfloor$, so $R\ge1$ and $R\le\log\log N$ for large $N$.
2. Apply `prop:planting` with exponent $a'$, the word $w=1$ ($k=1$, $u=1$), $C_R=1$, start $N'=N+R$ and length $H'=H-R$. Its range condition $N'^{a'}\le H'\le N'$ holds for large $N$, because $H-R\ge N^a-R\ge(N+R)^{a'}$.
3. The set $\mathcal G$ of $R$-isolated $n\in[N+R,N+H)$ therefore has $\lvert\mathcal G\rvert\ge c_*H'/(\log N')^\kappa\gg H/(\log N)^\kappa$.
4. By `lem:isolated`, each $n\in\mathcal G$ has $x_n\in[3/4,7/8)$ and $x_{n-r}=2^{-r}x_n\in[\frac342^{-R},\frac7{16})\subseteq[3\varepsilon,1/2)$ for $1\le r\le R$, where $\varepsilon=2^{-R}/4\le1/8$. All starts $n-r$ lie in $[N,N+H)$.
5. The blocks $\{n-1,\dots,n-R\}$ are pairwise disjoint (Paper VI §7). If $n<n'$ and $n-r=n'-r'$, then $x_n=2^{-(r'-r)}x_{n'}<1/2$, which contradicts $x_n\ge3/4$. So $F_{N,H}(3\varepsilon,1/2)\ge\Delta:=R\lvert\mathcal G\rvert/H$.
6. By `prop:upper`(a), $\lvert\mathcal G\rvert\le\#\{n:\ x_n\ge1/2\}\ll H/(\log N)^\kappa$. Hence $\Delta\ll\log\log N/(\log N)^\kappa\le\frac14(\log N)^{-\kappa/2}\le\varepsilon$ for large $N$.
7. By $x_n\le A(n)$ (`lem:oddpart`) and `lem:windows`, $\#\{n:\ x_n\ge\varepsilon\}\le\varepsilon^{-1}\sum_nA(n)\ll\varepsilon^{-1}H(\log N)^{-\kappa}$. So $F_{N,H}(0,\varepsilon)\ge1-O((\log N)^{-\kappa/2})\ge1/2\ge\Delta$.
8. The second Lean inequality gives $1-D_{N,H}(L)\ge\Delta\gg\log\log N/(\log N)^\kappa$. ∎

The analytic steps are Paper VI's propositions, which are themselves Lean-supported paper proofs. The finite steps are the two declarations. Hence the label: a Lean-supported paper proof for $\nu_*\in\{7/12,0.53\}$ and Conditional for $\nu_*=1/2$. The proposition is new in this note and unreviewed. S9 checks the window form of the first inequality on five windows of $L_{\chi_4}$ with exact enclosures. That is a finite instance of a kernel-verified theorem, not evidence for the asymptotic order.

*Proof of Corollary C.2.* `SharpTranslation.sharp_translation_isGreatest` (Paper VI `thm:sharp`, kernel-verified for every real) gives $\lvert D_H(y+z)-D_H(y)\rvert\le1-D_H(z)$, with equality at $y=0$ because $D_H(0)=1$. Put $y=2^Nx$ and $z=2^NL$; since $D_H$ depends only on fractional parts, $D_H(2^Nx+2^NL)=D_{N,H}(x+L)$. As $x$ ranges over $\mathbb R$, so does $y$. ∎

Combined with Proposition C, the supremum is $\asymp_a\log\log N/(\log N)^\kappa$ on windows $N^a\le H\le N$. This holds unconditionally for $a>0.53$ and under GRH($q_0$) for $a>1/2$.

### 2.5 Proof of Theorem D: GF-22 rebuilt on the moving interval

We follow GF-22 Steps 0–7 and mark every change. Steps 0, 1 and 4 do not depend on $N$ or $H$.

*Step 0 (fixed choices; unchanged).* Choose a class $g_0$ with $\chi(g_0)$ of exact order $d\ge2$. Then $c_\chi(p^{d-1})=0$ for every prime $p\equiv g_0\pmod q$. Choose a prime $\ell\equiv1\pmod q$, a class $r_0$ and an integer $A_0$ prime to $q\ell$ with $\kappa:=\Phi(c_\chi(A_0)(1+\chi(r_0)))\ne0$, and write $\kappa=b^f\kappa_1$ with $b\nmid\kappa_1$. **Additivity of $\Phi$ is used here**: $\Phi$ extends to a nonzero $\mathbb Q$-linear form, and $\{(1+\zeta)^j\}_{j<\varphi(h)}$ is a $\mathbb Q$-basis of $\mathbb Q(\zeta_h)$ (S7 checks the basis for $3\le h\le30$).

*Step 1 (the value; unchanged).* Choose $e$ with $b^e\ge\lvert\kappa_1\rvert$, put $W'=W+e$, choose $V_1=\tau\kappa_1$ with $\tau\equiv1\pmod b$ as in GF-22, and put $A=\ell^{\tau-1}A_0$. For every prime $u\equiv r_0\pmod q$ with $u>A$, $c_\Phi(Au)=\Phi(\tau c_\chi(A_0)(1+\chi(r_0)))=\tau\kappa=b^fV_1$. **Additivity is used again** here, through $\Phi(\tau z)=\tau\Phi(z)$.

*Step 2′ (parameters now depend on $N$).* Let $L=L(N)$ be the least integer with

```math
b^L\ \ge\ K_*\,C_\Phi\,\tau(A)\,\tau(q)\,\bigl(1+\log 6AN\bigr)^2,\qquad K_*=512 .
```

Thus $L=2\log_b\log N+O_w(1)$. Put $J=\{-(W'+f),\dots,-1\}\cup\{1,\dots,L\}$, $s=\lvert J\rvert=W'+f+L$, and $P_0=L+W'+f+\lceil2s\log_2(d+1)\rceil+A_0+\ell+q$. Take the $s$ smallest primes $p\equiv g_0\pmod q$ exceeding $P_0$. Under GRH one family suffices, because no exceptional modulus has to be avoided; for Proposition D.2 we take three. Assign them bijectively, $j\mapsto p_j$, and put $Q=\prod_jp_j^d$ and $q'=qQ$. By the prime number theorem modulo the fixed $q$ these primes are $\ll_q(P_0+s)\log(P_0+s)$, so

```math
\log q'\ \ll_{q,h}\ s\log s\ \ll_w\ \log\log N\cdot\log\log\log N,\qquad q'=N^{o(1)} .
```

*Step 4 (the class; unchanged).* By the Chinese remainder theorem choose $a_0\bmod q'$ with $a_0\equiv r_0\pmod q$ and $Aa_0\equiv p_j^{d-1}-j\pmod{p_j^d}$ for $j\in J$. Then $\gcd(a_0,q')=1$. For **every** integer $u\equiv a_0\pmod{q'}$ we have $v_{p_j}(Au+j)=d-1$ and hence $c_\Phi(Au+j)=\Phi(0)=0$ for all $j\in J$. **Additivity is used a third time** here, through $\Phi(0)=0$.

*Step 5′ (primes in the window; Conditional on GRH($q'$)).* Put $U=(N+W'+f+1)/A$ and $Y=H/A$. For an integer $u$, the start $n(u):=Au-W'-f-1$ lies in $[N,N+H)$ if and only if $U\le u<U+Y$. Let $\mathcal U$ be the set of primes $u\equiv a_0\pmod{q'}$ with $U\le u<U+Y$. Applying Corollary A.2's $\theta$-bound on $(U,U+Y-1]\subset[U,U+Y)$ with modulus $q'$ and dividing by $\log(2U)$,

```math
\lvert\mathcal U\rvert\ \ge\ \frac{Y-1}{\varphi(q')\log 2U}-C_2\frac{\sqrt U\log^2(2q'U)}{\log U}\ \ge\ \frac{Y}{2\varphi(q')\log2U}\qquad(N\ge N_0(w,a)).
```

The last inequality is check (a) of the brief. It holds because $Y/\varphi(q')\ge H/(Aq')\ge N^{a}\exp(-O_w(\log\log N\log\log\log N))$ while $\sqrt U\log^2(2q'U)\le\sqrt N\log^2N\,(1+o(1))$, and $a>1/2$. S6 computes $q'$ exactly for $L_+(2)$. The decimal-digit ratio $\operatorname{digits}(q')/\log_{10}N$ (closely tracking $\log q'/\log N$) is $22.1$ at $N=10^{10}$, $2.71$ at $10^{100}$ ($\log q'/\log N\approx2.701$), $0.34$ at $10^{1000}$ and $5.57\cdot10^{-4}$ at $10^{10^6}$ ($\log q'/\log N\approx5.564\cdot10^{-4}$). With constant $1$ in the GRH error, inequality (a) first holds for all four tested exponents $a\in\{0.55,0.6,0.75,0.9\}$ at $N=10^{10^4}$. The bound $q'=N^{o(1)}$ is purely asymptotic.

*Step 6′ (tail Markov on the moving interval; check (b) of the brief).* For $u\in\mathcal U$ put $R(u)=\sum_{k\ge1}\tau(Au+L+k)b^{-k}$, so that $\lvert T_{Au+L}\rvert\le C_\Phi R(u)$. Fix $k$. As $u$ runs over the integers of $[U,U+Y)$ in the class $a_0\bmod q'$, the number $m=Au+L+k$ runs injectively over integers of the class $Aa_0+L+k\bmod Aq'$ in an interval of length $H$ with right end

```math
X_k=N+W'+f+1+L+k+H\le3Nk .
```

Here we need a short-interval bound, not GF-22's prefix Lemma 5.2:

**Lemma E.2 (short-interval divisor sums in a progression).** For integers $D\ge1$ and $c$, reals $X_0\ge0$ and $Z\ge1$, $X_1=X_0+Z$ and $g=\gcd(c,D)$,

```math
\sum_{\substack{X_0<m\le X_1\\ m\equiv c\ (D)}}\tau(m)\ \le\ 2\sqrt{X_1}+\frac{2Z}{D}\,\tau(g)\Bigl(1+\tfrac12\log X_1\Bigr).
```

*Proof.* For $m\le X_1$, $\tau(m)\le2\#\{d\mid m:\ d\le\sqrt{X_1}\}$. For fixed $d\le\sqrt{X_1}$, the conditions $m\equiv c\ (D)$ and $d\mid m$ are compatible only if $e:=\gcd(d,D)$ divides $g$. They then define one class modulo $dD/e$, which has at most $Ze/(dD)+1$ members in $(X_0,X_1]$. The $+1$ terms contribute at most $2\sqrt{X_1}$. Writing $d=ed'$, the main terms contribute at most $\frac{2Z}D\sum_{e\mid g}\sum_{d'\le\sqrt{X_1}/e}\frac1{d'}\le\frac{2Z}D\tau(g)(1+\frac12\log X_1)$. ∎

S5 checks Lemma E.2 rigorously on 2556 instances, using a rational lower bound for the right side; the largest ratio of left to right side is $0.981$. The gcd $g_k=\gcd(Aa_0+L+k,Aq')$ satisfies $\tau(g_k)\le\tau(A)\tau(q)(d+1)^{E(L+k)}$, where $E(L+k)=0$ for $k<K_0:=P_0-L-W'-f$ and $E\le s$ always. This is GF-22 Step 5 verbatim, because it concerns only the residue class; S5 checks the gcd structure. Using $\sqrt{X_k}\le\sqrt{3N}\,k$, $1+\frac12\log X_k\le(1+\log3N)k$, and $(d+1)^s\le2^{k/2}$ for $k\ge K_0$, together with $\sum_kk2^{-k}=2$ and $\sum_kk2^{-k/2}<8.25$:

```math
\sum_{\substack{U\le u<U+Y\\ u\equiv a_0\,(q')}}R(u)\ \le\ 7\sqrt N+21\,\tau(A)\tau(q)\,\frac{Y}{q'}\,(1+\log3N).
```

The sum runs over all integers of the class, not only primes. This is legitimate by positivity. By Markov's inequality and the choice of $L$, the number of $u\in\mathcal U$ with $C_\Phi R(u)\ge b^L/2$ is at most

```math
\frac{2C_\Phi}{b^L}\Bigl(7\sqrt N+21\tau(A)\tau(q)\frac Yq'(1+\log3N)\Bigr)\ \le\ \sqrt N+\frac{42}{K_*}\cdot\frac{Y}{q'(1+\log6AN)}\ \le\ \frac{Y}{8\varphi(q')\log2U}+\frac{Y}{8q'\log2U}
```

for $N\ge N_0(w,a)$. The last step uses $\log2U\le1+\log6AN$, $K_*\ge336$, and once more $Y/\varphi(q')\ge N^{a-o(1)}\gg\sqrt N\log N$, which needs $a>1/2$.

*Step 7′ (conclusion).* At least $Y/(4\varphi(q')\log2U)$ primes $u\in\mathcal U$ have $\lvert T_{Au+L}\rvert<b^L/2$. For each of them $T_{Au}=b^{-L}T_{Au+L}$, because $c_\Phi(Au+j)=0$ for $1\le j\le L$, and therefore $\lvert T_{Au}\rvert<1/2$. GF-22 Lemma 5.1 applies with $W'$ in place of $W$, $P=Au$ and start $n(u)=Au-W'-f-1\in[N,N+H)$. The zeros at $n(u)+1,\dots,n(u)+W'+f$ are the offsets $-(W'+f),\dots,-1$ of $J$, and $c_\Phi(Au)=b^fV_1$. So digits $n(u)+1,\dots,n(u)+W'$ spell an expansion that begins with $w$. Distinct $u$ give distinct starts, so

```math
\#_w(N,H)\ \ge\ \frac{Y}{4\varphi(q')\log2U}\ \ge\ \frac{H}{4Aq'\log3N}\ \ge\ H\exp\bigl(-C_w\log\log N\cdot\log\log\log N\bigr).
```

Restricting to occurrences wholly inside the window changes the count by at most $W$. ∎

**Exceptional sets on the moving interval.** Item (b) of the brief asked whether any exceptional set of size $N/(\log N)^A$ could swallow a window of length $N^{1/2+\varepsilon}$. The table gives the answer.

| Set in the GF-22 proof | GF-22 prefix bound | Moving-window bound (this note) | Is it $o(Y/(\varphi(q')\log N))$? |
| --- | --- | --- | --- |
| Kill positions fail | empty (CRT forces $v_{p_j}=d-1$ for every $u$ in the class) | empty | ✓ |
| Value position fails | empty for prime $u\equiv r_0\ (q)$, $u>A$ | empty, since $u\ge U\asymp N/A$ | ✓ |
| Exceptional (Siegel) modulus | avoided by two families | not needed under GRH; three families for Proposition D.2 | ✓ |
| Tail Markov set $\{C_\Phi R(u)\ge b^L/2\}$ | $\frac{2C_\Phi}{b^L}\bigl(7\sqrt{AY}+330\tau(A)\tau(q)\frac Y{q'}(1+\log3AY)\bigr)$ | $\sqrt N+\frac{Y}{8q'\log2U}$ via Lemma E.2 | ✓ for $H\ge N^{1/2+\varepsilon}$ |
| Prime powers in $\psi(\cdot;q',a_0)$ | $\le2\sqrt x\log^2x$ | $\le P(2U)\log2U\ll\sqrt N\log N$ (Lemma A.1) | ✓ |
| Large-factor exclusion; nearby-support collisions | not used by GF-22 (kills are deterministic) | not used | — |

The only probabilistic condition, smallness of the tail, is handled by Markov's inequality on the **actual window sum**. The only additive error in that sum is the $2\sqrt{X_1}$ term of Lemma E.2. That term is $o(Y/q')$ exactly when $H\ge N^{1/2+\varepsilon}$, and $q'=N^{o(1)}$. So the step needs no Shiu, Brun–Titchmarsh or Rankin input, and its range coincides with the range where GRH gives primes, namely $a>1/2$. Below $1/2$, Lemma E.2 and Theorem A fail together.

S8 runs the moving-window construction in two prescribed windows, using the small kill primes $3,2,5,11$ of GF-22's table, so $q'=251559000$. It certifies, by factorization and an exact enclosure of the tail, an occurrence of $00$ in $L_+(2)$ at start $n=100000002495588146\in[10^{17},10^{17}+\lceil10^{17\cdot3/5}\rceil)$. It also certifies an occurrence of $01$ at $n=1000000495022262146\in[10^{18},10^{18}+\lceil10^{18\cdot7/10}\rceil)$. These are finite certificates of two finite statements. They say nothing about the count.

### 2.6 Proof of Proposition D.2 (unconditional, near-full windows)

Repeat §2.5 with **three** disjoint families $\mathcal P_1,\mathcal P_2,\mathcal P_3$ of $s$ primes $\equiv g_0\pmod q$ above $P_0$, with $Q_\nu=\prod_{p\in\mathcal P_\nu}p^d$. Apply GF-22's input (E1) at the two points $x=U$ and $x=U+Y$. It yields exceptional conductors $q_1(U)$ and $q_1(U+Y)$, if they exist. Each divides at most one of $qQ_1,qQ_2,qQ_3$; otherwise it would divide $q$, and the finitely many primitive real characters of conductor dividing $q$ are not exceptional for large $x$ (GF-22 Step 3). So some $\nu$ has $q_1(U)\nmid q':=qQ_\nu$ and $q_1(U+Y)\nmid q'$. Since $q'=\exp(O_w(\log\log N\log\log\log N))\le T(U)=\exp(c_0\sqrt{\log U})$, (E1) gives

```math
\psi(U+Y;q',a_0)-\psi(U;q',a_0)\ \ge\ \frac Y{\varphi(q')}-4C\,U\exp\bigl(-c_1\sqrt{\log U}\bigr)\ \ge\ \frac{3Y}{4\varphi(q')}
```

whenever $Y\ge16C\varphi(q')U\exp(-c_1\sqrt{\log U})$. That holds for $H=AY\ge N\exp(-c_3\sqrt{\log N})$ with $c_3=c_1/3$ and $N$ large, because $\varphi(q')=\exp(o(\sqrt{\log N}))$. Prime powers cost $O(\sqrt N\log N)$ (Lemma A.1) and the single possible prime at the right endpoint $U+Y$ costs at most $\log(2U)$, leaving $\lvert\mathcal U\rvert\ge Y/(2\varphi(q')\log 2U)$ literally for large $N$. Steps 6′ and 7′ then apply verbatim; they need only $H/q'\gg\sqrt N\log N$. ∎

This is a Paper proof from a repository input, namely GF-22's external input (E1), which is Landau–Page plus the prime number theorem for moduli up to $\exp(c\sqrt{\log x})$. It shows exactly what GRH adds to GF-22: unconditionally the windows reach $H\ge N\exp(-c_3\sqrt{\log N})$, and under GRH they reach $H\ge N^{1/2+\varepsilon}$.

### 2.7 Proof of Proposition E

Let $a(n)=\Phi_{\rm ind}(c_\chi(n))\in\{0,1\}$. Pick $r$ with $(r,q)=1$ and $\chi(r)\ne1$, which exists because $\chi$ is nonprincipal. By Dirichlet's theorem there is a prime $p\equiv r\pmod q$, so $p\nmid q$ and $\chi(p)\ne1$; let $d\ge2$ be the order of $\chi(p)$. If $n\equiv p^{d-1}\pmod{p^d}$, then $v_p(n)=d-1$. Hence $c_\chi(n)=c_\chi(p^{d-1})c_\chi(n/p^{d-1})=0$, because $c_\chi(p^{d-1})=\sum_{i<d}\chi(p)^i=0$ when $\chi(p)$ is a primitive $d$-th root of unity. S7 checks that $\Phi_d\mid1+x+\dots+x^{d-1}$ for $d\le12$. So $a(n)=0$ on a full residue class modulo $p^d$, and $a(n)=0$ infinitely often.

Since $0\le a(n)\le1$ and infinitely many $a(n)$ vanish, $\sum_{n>m}a(n)b^{m-n}<1$ for every $m$. For $b=2$ this is strict because of the zeros; for $b\ge3$ the sum is at most $1/(b-1)$. So the base-$b$ digit at position $n$ is exactly $a(n)$. Every block of $p^d$ consecutive positions contains a $0$, so $1^{p^d}$ never occurs, and for $b\ge3$ the digit $2$ never occurs.

For $\chi_{-4}$ the class $n\equiv3\pmod4$ already forces $a(n)=0$, so $1111$ is absent. For the cubic character modulo 7 the class $n\equiv4\pmod8$ forces $v_2(n)=2$ with $2\equiv2\pmod7$ in $\mathcal P'$, so $1^8$ is absent. Additivity fails: $\Phi_{\rm ind}(1)+\Phi_{\rm ind}(-1)=2\ne0=\Phi_{\rm ind}(0)$. S7 checks the vanishing classes and the absence of these words in the first $10^5$ digits, and the presence of $111$ and $1^7$ respectively. ∎

*Consequence for the registry (text only).* The proof of GF-22 uses additivity three times: in Step 0 ($\kappa\ne0$ via $\mathbb Q$-linearity), in Step 1 ($\Phi(\tau z)=\tau\Phi(z)$) and in Step 4 ($\Phi(0)=0$). The tail bound $\lvert c_\Phi\rvert\le C_\Phi\tau$ also comes from $c_\Phi(n)=\sum_{d\mid n}\Phi(\chi(d))$. The `GF-22` statement at HEAD (commit `04969b9`) said "every nonzero integer-valued function $\Phi$ on the range of $1*\chi$ with $\Phi(0)=0$". Proposition E refutes that wording. The uncommitted working-tree `docs/registry/GF.toml` already says "nonzero additive map $\Phi:\mathbb Z[\zeta_h]\to\mathbb Z$", which matches the proof. The generated `docs/results.md` still shows the old wording until `python3 scripts/portal.py build` is rerun. This note does not edit either file.

---

## 3. Addendum F: audit of Mira Cult's short-window exponent under Dirichlet GRH

**Attribution and scope.** The theorem and the proof are Mira Cult's: claim 0002 in the public repository `Mira-Cult/math`, theorem at commit `149831943806a656c9efaa14cacbd9c915b2a2ba`. P13 records that the paper credits GPT-6.2 Astra with developing and drafting the proof under Mira Cult's guidance. The theorem gives a positive lower density $c_{a,w}H$ of every fixed binary word in every window $N^a\le H\le N$, $7/12<a\le1$, of the Erdős–Borwein constant $E$. The repository's earlier audit (P13, P13-R) found the argument consistent. It recorded a residual burden: the uniform force-weighted multi-bank exact-atom induction was not independently reconstructed in every mixed Taylor remainder.

This section is a **dependency audit**. It locates every use of the exponent $7/12$ and asks what Dirichlet GRH changes. It relies on the description of the argument recorded in P13 and P13-R; Mira Cult's source files were not re-read in this session. No contact with Mira Cult or with anyone else was made. The conclusion is labelled Conditional and audit-level. It is not a theorem of the repository and not an independent verification of the induction.

### 3.1 Where $7/12$ enters

| # | Location (as recorded in P13/P13-R) | Role in the argument | Prime input used |
| --- | --- | --- | --- |
| U1 | Choice of $7/12<a'<a$ and $\theta$ with $(a'-\theta)/(1-\theta)>7/12$, $a'-\theta>1/2$, $\theta<a'/4$ | the prime interval for $p$ (scale $X\asymp N/b$, length $Y\asymp H/b$, $b\le N^\theta$) has length $\ge X^\vartheta$ with $\vartheta>7/12$ | PPS requires $\vartheta>7/12$ |
| U2 | Display (2) of Perelli–Pintz–Salerno (1984, *Ann. Pisa*, pp. 529–530; not the 1985 *Invent. Math.* paper used by Paper VI) with the Huxley–Iwaniec level $\nu\le3\vartheta-7/4-\epsilon$ for $7/12<\vartheta\le29/48$; level $\rho<\min(3\vartheta-7/4,\vartheta-1/2)$ | equidistribution of the normalized log-prime measure $P$ in classes modulo $d\le X^\rho$, with arbitrary log saving and the sum over moduli outside the maximum | PPS 1984 (Huxley–Iwaniec zero density) |
| U3 | Removing prime powers costs $O(X^{1/2+\rho}\log^2X)$ | $\psi\to\theta$ | elementary; needs $\rho<\vartheta-1/2$ |
| U4 | Normalization $S/Y=1+O((\log X)^{-B})$ | the modulus-one case of (2) | PPS at $q=1$ (Huxley) |
| U5 | Arithmetic error of the binomial (Bonferroni) brackets: moduli are least common multiples of $O_D(t)$ bank primes and a force of size $\le X^{\rho/4}$; the multiplicity $\exp(O_D(t))$ is absorbed by arbitrary log savings | joint factorial moments compared with the CRT model | (2) at level $X^\rho$ |
| U6 | Force-weighted marks $Z_j$: squares force at most two primes or powers of size $\le X^{2\eta}$, $\eta=\rho/16$; repeated powers $\ell^e\le X^\eta$ | angular cost of the true divisor terms | (2) at level $X^\rho$ |
| U7 | One-coordinate envelope, outer offsets, second moment $\mathbb EF^2\ll\mathbb EF$ | the same progression estimate | (2) at level $X^\rho$ |

The following steps do **not** use the exponent: the dimension-two upper-bound sieve for $\mathbb EF(F-1)$, which has trivial remainders; the divisor-pairing tail, which needs only $\sqrt N/H\to0$, i.e. $a>1/2$; the Gaussian and Bonferroni model computations; Fourier inversion; Markov's inequality; and Cauchy–Schwarz.

### 3.2 The GRH replacement

**Lemma F.1 (Conditional on GRH($q$) for every $q\le Q$).** Let $x\ge4$, $1/2<\vartheta\le1$, $0<\rho<\vartheta-1/2$, $y=x^\vartheta$ and $Q=x^\rho$. Then for every $B$

```math
\sum_{q\le Q}\max_{(u,q)=1}\max_{0\le h\le y}\max_{x/2<z\le x}\Bigl\lvert\psi(z+h;q,u)-\psi(z;q,u)-\frac h{\varphi(q)}\Bigr\rvert\le2C_0\,Q\sqrt{2x}\,\log^2(4Qx)\ll y\,x^{-(\vartheta-\frac12-\rho)}\log^2x\ll_B\frac{y}{(\log x)^B}.
```

*Proof.* Theorem A at $z+h\le2x$ and at $z$ bounds each term pointwise by $2C_0\sqrt{2x}\log^2(4Qx)$, uniformly in $u$, $h$ and $z$. Sum over $q\le Q$. ∎

This is display (2) of PPS 1984 at level $x^\rho$, for **every** $\vartheta>1/2$, with a power saving in place of an arbitrary log saving. The modulus-one case U4 is the Riemann hypothesis: $S=Y+O(\sqrt X\log^2X)$. The moduli $q\le X^\rho$ grow with $X$, so the hypothesis is Dirichlet GRH for all moduli up to $X^\rho$, not a single GRH($q_0$).

### 3.3 Does any step need a fixed level $\rho\ge\rho_0$?

No. There are four reasons.

1. **Internal evidence.** In the unconditional argument the admissible level satisfies $\rho<3\vartheta-7/4=3(\vartheta-7/12)$. This tends to $0$ as $a\downarrow7/12$ (S10, exact: $3\vartheta-\frac74=\frac1{4k}$ at $\vartheta=\frac7{12}+\frac1{12k}$). The theorem is asserted for every $a>7/12$, so the argument must run with every fixed $\rho>0$, with constants depending on $\rho$. The recorded parameter choices confirm that it does.
2. **Explicit $\rho$-dependence** (P13-R parameters).
   - The cutoff exponent is $c=\rho/[100D(R+1)]$. The later-bank modulus budget is $Dc\sum_h2^{-h}(R+h)=\rho/50<\rho/4$ for every $\rho$ (S10, exact). The first-bank term $Dc\,2^{-m}r_*$ is $O_D(c\,t^{-7})\to0$.
   - Forces have size $\le X^{\rho/4}$.
   - $\eta=\rho/16$, and $\eta/c=100D(R+1)/16$ does not depend on $\rho$ (S10). So the mean number $\log(\eta/(4c))+O(1)$ of supplementary primes in $(X^c,X^{\eta/4}]$ depends only on the strip width $W$.
   - Since $X\asymp N/b$ with $b\le N^\theta$ ($\theta<1/4$), the stripped form has size $L_j(p)\ll N\ll X^{1/(1-\theta)}$, so prime factors larger than $X^{\eta/4}$ have total multiplicity $\le\frac4{\eta(1-\theta)}(1+o(1))=\frac{64}{\rho(1-\theta)}(1+o(1))<\frac{256}{3\rho}(1+o(1))=O(1/\rho)$, deterministically. This enters only the constant $C_a$ in $Z_j$.
   - Omitted higher powers cost $O(X^{-\eta/2})$.
   - The first bank ends at $X^{c/t^8}$ and has reciprocal prime mass $t-8\log t-\log(1/c)+O(1)$. Since $\log(1/c)=O(\log(W/\rho))$ is fixed, the local-limit scale $\sqrt t$ and the Gaussian atoms are unaffected.
3. **Order of choices.** The strip width $W$ is chosen after $(k,a)$. As $a\downarrow1/2$ under GRH, $\rho\downarrow0$ and $C_a=O(1/\rho^2)$ grows (since $Z_j$ bounds the square of the $O(1/\rho+G+M_j+P_j)$ displacement). The conditional mean angular cost $O(C_a(1+\log^2(W/\rho))/W)$ still tends to $0$ as $W\to\infty$ for fixed $\rho$. So $W=W(k,\rho)$, followed by $L=e^{20W}$, $B_*=\lceil e^{50W}\rceil$ and $R=\lceil W^4\rceil$. All of these are fixed before $N\to\infty$.
4. **Error absorption.** Under GRH the progression error carries the power saving $X^{-(\vartheta-1/2-\rho)}$. This absorbs the $\exp(O_D(t))=(\log X)^{O_D(1)}$ modulus multiplicities and the fixed powers of $\log X$ that come from recovering primes.

### 3.4 Conclusion of the audit

Steps U3 and the divisor-pairing tail need $\vartheta>1/2$ and $a>1/2$ independently of GRH. Lemma F.1 gives every positive level below $\vartheta-1/2$, and §3.3 shows that every positive level suffices. S10 constructs admissible $(a',\theta,\vartheta,\rho)$ exactly for every $a$ on a grid of step $0.007$ in $(1/2,1]$.

**Audit conclusion F (Conditional on Dirichlet GRH for the moduli $q\le X^\rho$; dependency audit).** Grant the argument of Mira Cult as audited in P13, with the residual burden recorded there. Then Dirichlet GRH extends her window theorem for the Erdős–Borwein constant $E$ from $7/12<a\le1$ to every fixed $1/2<a\le1$. For each fixed nonempty binary word $w$ and each such $a$ there is $c_{a,w}>0$ such that every window of $N^a\le H\le N$ digits after digit $N$ contains at least $c_{a,w}H$ wholly contained occurrences of $w$, for $N\ge N_0(a,w)$. The constant $c_{a,w}$ may tend to $0$ as $a\downarrow1/2$; this is not quantified. Under the same conditional extension, the finite Lean Fourier transfer of P13 (`ErdosBorweinFourier.lean`) then gives, for each fixed odd frequency $h$ and $w=10^{k-1}$ with $2^k\ge2\pi\lvert h\rvert$, the window bound $\lvert\sum_{N\le n<N+H}e(h2^nE)\rvert/H\le1+1/H-c_{a,w}/2$ for $a>1/2$.

*What does not transfer.* Kumchev's exponent $0.53$ does not transfer to this argument. Kumchev supplies a minorant $\lambda$ of the primes with equidistributed weights. The local-limit comparison needs two-sided asymptotics for the prime measure itself, and $\lambda$ is not a nonnegative measure on the integers. Unconditionally the audited range therefore stays at $a>7/12$. Lowering it would need a short-interval Bombieri–Vinogradov estimate with a positive level for some $\vartheta\le7/12$; see Open question 4.

---

## 4. Prior art and attribution

- **GRH and primes in progressions.** The estimate $\psi(x;q,a)=x/\varphi(q)+O(x^{1/2}\log^2x)$ under GRH is classical. It appears in textbook form in Davenport, Ch. 20 and Montgomery–Vaughan I, Ch. 13. We make no claim of priority for Theorem A; §2.1 records the deduction so that every hypothesis is visible. The analogous classical consequence of RH for gaps between consecutive primes is due to Cramér (1920).
- **Paper VI.** Paper VI (version 1.0, 25 November 2026) proves the window counts for $a>7/12$ via Perelli–Pintz–Salerno (1985, *Invent. Math.*, with level $x^{1/40}$, of which only the single modulus $q_0$ is used) and Huxley (1972), and for $a>0.53$ via Kumchev (2002). Its §10 already observes that the steps other than the prime input need only $a>1/2$. Theorem B makes this explicit under GRH($q_0$), and its novelty is correspondingly small. Bailey, Borwein, Crandall and Pomerance (2004, §9) give the one-bit asymptotic for $\theta_3(1/2)^2$ in prefixes; Theorem B does not touch that.
- **Short-interval prime theorems.** Huxley (1972, exponent $7/12$); Huxley–Iwaniec, quoted in PPS; Baker–Harman–Pintz (exponent $0.525$ for primes in short intervals, without progressions, as recalled by Kumchev); Guth and Maynard (arXiv:2405.20552, 2024), who prove a zero-density estimate that gives the prime number theorem in intervals of length $x^{17/30+\varepsilon}$. That statement is recalled and was not checked against the source in this session. Selberg (1943) treats almost all short intervals under RH (Open question 2).
- **GF-22.** The construction, Lemma 5.1, the Landau–Page device with two families, and the prefix bound are from Phase 22 (`GF-22`). §2.5 transports them to moving windows; the three-family variant in §2.6 is a routine extension.
- **Erdős–Borwein windows.** The window theorem and its weighted local-limit method are Mira Cult's (claim 0002). The earlier prefix bounds are due to Captain Sude ($N\exp(-C(\log\log N)^3)$, elementary Lean release), Mira's gists ($N\exp(-C(\log\log N)^2\log\log\log N)$), and Campbell (the word $11$), as recorded in P13. §3 is only a dependency audit of Mira Cult's argument.
- **Search scope.** No literature search beyond the repository notes and the sources they cite was made in this session. Priority statements are provisional.

## 5. External inputs and exact hypothesis verification

| Input | Statement used | Where | Label | Hypotheses checked |
| --- | --- | --- | --- | --- |
| **GRH($q$), GRH($q_0$), Dirichlet GRH** | all nontrivial zeros of the relevant $L(s,\chi^*)$ on $\Re s=1/2$ | Theorem A and every result labelled Conditional | **Conditional hypothesis (unproved)** | named per result: GRH($q_0$) for Theorem B and Proposition C at $a>1/2$; GRH($q'$) for the growing $q'$ of §2.5 (Dirichlet GRH suffices) for Theorem D; GRH for all $q\le X^\rho$ for §3 |
| (X1) truncated explicit formula, estimate of $b(\chi)$ | Davenport Chs. 17, 19 (`Davenport` in Paper VI's bibliography); Montgomery–Vaughan I, Ch. 12 | Theorem A | External input | $\chi$ primitive, $2\le T\le x$: used with $T=\sqrt x$, $x\ge4$ |
| (X2) zero counting near height $t$ | Davenport Chs. 15–16 | Theorem A | External input | primitive $\chi$, all $t$ |
| Prime number theorem modulo a fixed $q$ | size of the kill primes $p_j\ll_q(P_0+s)\log(P_0+s)$ | Theorem D, Proposition D.2 | External input (unconditional) | fixed modulus $q$ |
| GF-22 (E1) | Landau–Page and PNT for $q'\le\exp(c_0\sqrt{\log x})$ with at most one exceptional modulus | Proposition D.2 | Repository input (GF-22, Paper proof with this external input) | applied at $x=U$ and $x=U+Y$; three families; $q'\le T(U)$ |
| GF-22 Lemma 5.1 and Steps 0, 1, 4 | digit window, value, CRT kills | Theorem D, Proposition D.2 | Repository input (Paper proof) | $\Phi$ additive and nonzero (Proposition E shows this cannot be dropped) |
| Paper VI `prop:planting`, `lem:isolated`, `prop:upper`, `lem:windows`, `lem:oddpart` | planting and upper bounds | Theorem B, Proposition C | Repository input (Lean-supported paper proof) | (H1)–(H4); $\nu_*=1/2$ is allowed by the statement of `prop:planting` |
| Paper VI `lem:shortprimes` (PPS 1985) and `lem:kumchevfixed` (Kumchev 2002) | $(\mathrm P_\nu)$ for $\nu>7/12$, resp. $\nu>0.53$ | unconditional instances of Proposition C | External inputs as in Paper VI | as checked in Paper VI (note Paper VI `paper.tex:1171-1173` records that Kumchev 2002 was checked against the author's posted text rather than the printed journal version) |
| Lean: `one_sub_discrepancy_le_one_bits`, `one_sub_discrepancy_ge_of_separated_mass`, `sharp_translation_isGreatest` | finite discrepancy inequalities **for every real** | Proposition C, Corollary C.2 | Kernel-verified (repository) | applied to $y=\{2^NL\}$ and $z=2^NL$, which are real numbers |
| Brun–Titchmarsh (Montgomery–Vaughan 1973), Selberg sieve, Shiu (1980) | inside Paper VI's proofs | Theorem B (via Paper VI) | External inputs of Paper VI | unchanged |
| Mira Cult, claim 0002; P13, P13-R | the audited argument | §3 | attribution; audited dependency | levels and parameters as recorded in P13-R |

## 6. Evidence ledger

- **Conditional (written deductions from an external GRH hypothesis; not kernel-verified):**
  - Theorem A and Corollary A.2 (GRH($q$));
  - Corollary A.3, Theorem B, and Proposition C for $a>1/2$ (GRH($q_0$));
  - Theorem D and its window-disjunctivity corollary (GRH for the moduli $q'=qQ(N,w)$; Dirichlet GRH suffices);
  - Lemma F.1 and Audit conclusion F (Dirichlet GRH up to $X^\rho$). F is also only an audit and inherits P13's residual burden.
- **Lean-supported paper proof (new, unreviewed):** Proposition C for $a>0.53$ and for $a>7/12$, and Corollary C.2. The finite steps are the cited kernel-verified declarations.
- **Paper proof (new, unreviewed):** Lemma A.1, Lemma E.2, Proposition D.2 (with the repository input (E1)), Proposition E.
- **Finite certificate:** S1 and S10 (exact parameter algebra); S3 (prime-power count at every jump point $\le10^6$); S5 (Lemma E.2 on 2556 instances, gcd structure); the exact parts of S6 ($q'(N)$ and digit counts); S7 (closed form to $n=3000$, Q-basis for $h\le30$, absent and present words in the first $10^5$ digits); S8 (two certified window occurrences in $L_+(2)$); S9 (window upper-gap inequality on five windows of $L_{\chi_4}$, with exact enclosures).
- **Numerical (not evidence):** S2 (the threshold where $X^\nu\ge\sqrt X\log^2X$); S4 ($\psi(x;q,u)$ for $x\le2\cdot10^6$ and the finite measurement of $(\mathrm P_{0.55})$); the illustrative constant $1$ in S6.
- **Open:** §9.

## 7. Reproduction

```sh
python -B scripts/phase25_grh_windows.py
```

Expected output: `ALL 86554 CHECKS PASSED` (77,438 exact, 72 cert, 9,044 num), exit code 0, about 2–5 s. This was checked on Windows (Python 3.13) and on the Linux build host `hail`. The script needs only the Python standard library. Random instances use the fixed seeds 25010 and 25011, and every random instance is verified exactly. The Pollard–Brent seeds affect only the speed of factorization, never a result. No Lean file, manuscript or registry entry depends on this script.

## 8. Exact finite tests (script sections)

1. **S1 [exact]** Paper VI parameters $\theta,\nu,\beta$ for $\nu_*\in\{1/2,\,0.53,\,7/12\}$ on grids of exponents $a$ (1001, 941 and 835 distinct values). The checks are every inequality in the table of §2.3 and the degeneration at $a=1/2$.
2. **S2 [exact]/[num]** The bound $\log(qxT)\le\frac32\log(qx)$ at $T=\sqrt x$ (exact), the harmonic bookkeeping for the zero sum (numerical), and the least $X$ with $X^\nu\ge\sqrt X\log^2X$: $\log_{10}X\ge632.7$, $93.3$, $49.3$, $39.1$, $11.3$ for $\nu=0.51$, $0.55$, $7/12$, $0.6$, $0.75$.
3. **S3 [exact]** Lemma A.1 at all 236 jump points $x\le10^6$.
4. **S4 [num]** $\max\lvert\psi(x;q,u)-x/\varphi(q)\rvert/(\sqrt x\log^2x)=0.0057$ for $q\in\{3,4,5,7,8,11,12,13\}$ and $x\le2\cdot10^6$. The ratio of the prime count in $(X,X+X^{0.55}]$, $p\equiv1\ (4)$, to $Y/(4\log X)$ is at least $1.579$ for $10^5\le X\le1.9\cdot10^6$. This is a finite measurement only.
5. **S5 [exact]** Lemma E.2 on 2556 seeded and edge-case instances, rigorous through a rational lower bound for the right side. The gcd structure of Step 6′ on 2,424 coprime pairs (out of 4,000 sampled).
6. **S6 [exact]/[num]** Exact $q'(N)$ for $L_+(2)$ ($W=2$, worst word value $M=3$), with admissible $L$ from rational upper bounds for the logarithms. The table below summarizes it. The numerical checks (illustrative GRH constant $1$) verify that the sufficient window inequality fails at $N=10^{100}$ and holds at $N=10^{10^6}$ for $a\in\{0.55,0.6,0.75,0.9\}$.

   | $\log_{10}N$ | $L$ | $s$ | largest kill prime | digits of $q'$ | $\operatorname{digits}(q')/\log_{10}N$ |
   | --- | --- | --- | --- | --- | --- |
   | $10$ | 25 | 27 | 1123 | 221 | 22.1 |
   | $10^2$ | 30 | 32 | 1319 | 271 | 2.71 |
   | $10^3$ | 37 | 39 | 1669 | 340 | 0.34 |
   | $10^4$ | 43 | 45 | 2131 | 405 | 0.0405 |
   | $10^6$ | 57 | 59 | 2971 | 557 | 0.000557 |

7. **S7 [exact]** Additivity of $\Phi_\pm$, $\Phi(\tau z)=\tau\Phi(z)$, $\kappa=\Phi_\pm(1+\omega)=1$, and the closed form of $c$ against the divisor sum for $n\le3000$. The value family $c_\pm(13^{V-1}u)=V$. The Q-basis $\{(1+\zeta_h)^j\}$ for $3\le h\le30$. The counterexamples of Proposition E: $1111$ absent for $\chi_{-4}$ and $1^8$ absent for the cubic character modulo 7 in the first $10^5$ digits, with $111$ and $1^7$ present. The identity $\Phi_d\mid1+\dots+x^{d-1}$ for $d\le12$.
8. **S8 [cert]** Moving-window instances of Theorem D's construction for $L_+(2)$ with kill primes $3,2,5,11$ ($q'=251559000$):
   - word $00$ in $[10^{17},10^{17}+15848931925)$, with 63 class members and 7 primes;
   - word $01$ in $[10^{18},10^{18}+3981071705535)$, with 93 class members and 12 primes.

   Each occurrence is certified by factoring the 64 following coefficients and enclosing the tail.
9. **S9 [cert]** At least 12,000 certified binary digits of $L_{\chi_4}$. Exact discrepancies of 32-bit truncations on five windows. The window upper-gap inequality for $\ell=1,\dots,11$, with truncation slack $2^{-31}$.
10. **S10 [exact]** Huxley–Iwaniec level $3\vartheta-7/4\to0$ as $\vartheta\to7/12$; GRH parameters $(a',\theta,\vartheta,\rho)$ for every grid point $a\in(1/2,1]$; bank budget $=\rho/50$; $\eta/c$ independent of $\rho$; multiplicity of large factors $\le\frac4{\eta(1-\theta)}<\frac{256}{3\rho}$ for $\theta<1/4$.

## 9. Open questions

1. **The endpoint $a=1/2$.** Under GRH, are there windows $H=\sqrt N(\log N)^C$ in which every word occurs? Theorem A gives primes in $(X,X+C\sqrt X\log^2X]$, but Paper VI's far tail ($a-\theta>1/2$) and the $2\sqrt{X_1}$ term of Lemma E.2 both fail there. A Shiu-type short-interval divisor bound in progressions to moduli $N^{o(1)}$ would be needed.
2. **Almost all windows below $1/2$.** Selberg's (1943) mean-square method under RH, and its GRH analogue for progressions, might give the conclusions of Theorems B and D for almost all $N$ with $H\ge N^\varepsilon$ or $H\ge(\log N)^C$. This was not attempted.
3. **Paper VI below $0.53$ unconditionally.** This is Paper VI's Q2, unchanged.
4. **Mira Cult's range below $7/12$ unconditionally.** It would need a short-interval Bombieri–Vinogradov estimate with a positive level for some $\vartheta\le7/12$. Whether a hybrid Dirichlet-character version of the Guth–Maynard large-value estimate provides one was not checked.
5. **Positive window density for GF-22.** The CRT kills cost $\exp(-C\log\log N\log\log\log N)$ even under GRH, because the loss comes from $q'$ itself. Is $\#_w(N,H)\gg H(\log N)^{-c}$, or even $\gg H$, provable, for example by replacing kills with a sieve as in Paper VI? For odd-order characters the support of $c_\chi$ has positive density, which changes the sieve.
6. **GF-22 unconditionally for $H\ge N^{1-\eta_0}$.** Log-free zero-density estimates near $\sigma=1$, with the three-family Landau–Page device, plausibly give such a range. This was not checked.
7. **Effective thresholds.** An explicit constant in Theorem A would make $N_0$ explicit. S6 shows that for GF-22 the thresholds are $N$ with thousands of digits.
8. **Window discrepancy constants.** Does $(1-D_{N,H}(L))(\log N)^\kappa/\log\log N$ converge along windows?

## 10. Standing objectives advanced

- **Objective 1 (normality):** none.
- **Objective 2 (nonnormality and disjunctivity):** window disjunctivity for every $a>1/2$, conditional on GRH($q_0$) for the Paper VI family and on Dirichlet GRH for the GF-22 family and, via the audit, for $E$. Unconditional near-full windows for GF-22 (Proposition D.2). Nonnormality statuses are unchanged.
- **Objective 3 (quantify digit distributions):**
  - two-sided window counts $\asymp H/(\log N)^\kappa$ for $a>1/2$ (Conditional);
  - the new window discrepancy order $1-D_{N,H}(L)\asymp(\log\log N)/(\log N)^\kappa$, unconditional for $a>0.53$ and Conditional for $a>1/2$ (Proposition C);
  - the window translation identity (Corollary C.2).
- **Objective 4 (limitations):**
  - exact location of the threshold $1/2$ in each method (Remark B.1, the moving-window table of §2.5, §3.4);
  - additivity in GF-22 is necessary (Proposition E);
  - the GRH estimates are vacuous below about $10^{93}$ at $\nu=0.55$, and the GF-22 moduli are not small before $N\approx10^{10^4}$ (S2, S6);
  - $7/12$ enters Mira Cult's argument only through the level of distribution, and Kumchev's $0.53$ does not transfer to it (§3).
- **Benchmarks.** No status changes. Conditional results never change a benchmark status. The unconditional Proposition C refines window statistics of families whose discrepancy status is already recorded in `docs/benchmarks/arithmetic-families.toml`; any update there needs the registry procedure and review.

---

## Appendix A. Draft revision insert for Paper VI (not applied)

The following LaTeX is a self-contained draft for a future revision of `papers/06-multiplicative-lambert/paper.tex` that the owner would have to authorize. It uses only the paper's existing macros (`\cref`, `\evidence`, `\ref{H1}` and so on) and existing bibliography keys (`Davenport`, `MontgomeryVaughanBook`). It keeps the unconditional theorems ($a>7/12$ in `thm:words`, checked against the printed PPS source, and $a>0.53$ in `thm:kumchev`) and the publication history unchanged. The paper has not been modified.

```latex
% === Insert A1: Section \ref{subsec:range}, after the proof of \cref{thm:kumchev} and
%     before the paragraph "\cref{thm:kumchev} is a \evidence{Paper proof} ..." ===

\begin{lemma}\label{lem:grhfixed}
Assume that for every Dirichlet character $\chi$ modulo $q_0$ all nontrivial zeros
($0<\Re s<1$) of $L(s,\chi^*)$ have real part $1/2$, where $\chi^*$ is the primitive
character inducing $\chi$ (equivalently, the Riemann hypothesis for the Dedekind zeta
function of $\mathbb{Q}(\zeta_{q_0})$). Then $\mathrm{(P}_\nu\mathrm{)}$ holds for
every fixed $1/2<\nu<1$, with $c_P=1/(2\varphi(q_0))$.
\end{lemma}

\begin{proof}
Under this hypothesis the truncated explicit formula with $T=\sqrt x$ and the
zero count give $\psi(x;q_0,a_0)=x/\varphi(q_0)+O(\sqrt x\log^2x)$ for $x\ge2$
\cite[Chs.~16, 17, 19 and~20]{Davenport}. Let $X>Y\ge(X+Y)^\nu$ with $X$ large.
Subtracting the estimates at $X+Y\le2X$ and at $X$ gives
$\psi(X+Y;q_0,a_0)-\psi(X;q_0,a_0)=Y/\varphi(q_0)+O(\sqrt X\log^2X)$, and prime
powers $p^e\le2X$ with $e\ge2$ contribute $O(\sqrt X\log X)$. Since $Y\ge X^\nu$
with $\nu>1/2$, both errors are at most $Y/(4\varphi(q_0))$ for large $X$, and
$\log p\le\log 2X\le\frac32\log X$ for $p\le X+Y$. Hence $(X,X+Y]$ contains at
least $Y/(2\varphi(q_0)\log X)$ primes $p\equiv a_0\pmod{q_0}$.
\end{proof}

\begin{theorem}[Lower bounds for $a>1/2$ under GRH]\label{thm:grh}
Assume \ref{H1}--\ref{H4} and the hypothesis of \cref{lem:grhfixed}. Then
\cref{prop:planting} holds with $\nu_*=1/2$. Consequently \cref{thm:words},
including its lower bounds, and the window statement of \cref{cor:disjunctive}
hold for every fixed $1/2<a\le1$.
\end{theorem}

\begin{proof}
By \cref{lem:grhfixed}, $\mathrm{(P}_\nu\mathrm{)}$ holds for every $1/2<\nu<1$.
This is the only hypothesis on $\nu_*$ in \cref{prop:planting}, whose statement
allows $\nu_*=1/2$. With $\nu_*=1/2$ the parameters of its proof satisfy
$a-\theta\ge a/2+1/4>1/2$, hence $\nu_*<\nu<a-\theta$,
$1/(2(a-\theta))<\beta<1$ and $(a-\theta)\beta>1/2$, as required there. The
deduction in \cref{sec:words} applies verbatim.
\end{proof}

\cref{thm:grh} is \evidence{Conditional} on the generalized Riemann hypothesis for
the finitely many Dirichlet $L$-functions modulo $q_0$; for $L_{\chi_4}$ these are
$\zeta(s)$ and $L(s,\chi_{-4})$. It is not used elsewhere in the paper, and the
unconditional ranges $a>7/12$ (\cref{thm:words}) and $a>0.53$ (\cref{thm:kumchev})
are unaffected. As written, the far-tail step of \cref{prop:planting} needs
$a-\theta>1/2$, so the exponent $1/2$ is also where that step stops.

% === Insert A2: replace question (Q2) in "Questions" ===
\item Can the range $a>0.53$ of \cref{thm:kumchev} be lowered unconditionally,
  either through better short-interval lower bounds for a fixed progression or by
  avoiding them? Under the generalized Riemann hypothesis modulo $q_0$ the range is
  $a>1/2$ (\cref{thm:grh}), where the far-tail step of \cref{prop:planting} also stops.

% === Insert A3: Section \ref{subsec:scope}, after the sentence on \cref{thm:kumchev} ===
\cref{thm:grh} is \evidence{Conditional} on the generalized Riemann hypothesis for
the Dirichlet $L$-functions modulo $q_0$.

% === Insert A4 (optional): introduction, after "the lower bounds extend to every
%     fixed $a>0.53$ (\cref{thm:kumchev})." ===
Under the generalized Riemann hypothesis for the characters modulo $q_0$ they
extend to every fixed $a>1/2$ (\cref{thm:grh}).

% === Insert A5 (optional, unconditional; needs its own review before inclusion):
%     after \cref{rem:transition} ===
\begin{proposition}[Window discrepancy]\label{prop:windisc}
Assume \ref{H1}--\ref{H4} and put $D_{N,H}(x)=D_H(\{2^Nx\})$. For every fixed
$0.53<a\le1$ (and under the hypothesis of \cref{lem:grhfixed}, for every fixed
$1/2<a\le1$), uniformly for $N^a\le H\le N$,
$1-D_{N,H}(L)\asymp_a(\log\log N)/(\log N)^{\kappa}$; the upper bound holds
unconditionally for every fixed $0<a\le1$.
\end{proposition}
% Proof: apply \cref{lem:upperlean,lem:lowerlean} to the real number $\{2^NL\}$,
% with \cref{prop:upper}(a), \cref{lem:windows} and \cref{prop:planting} (exponent
% $a'\in(0.53,a)$, $w=1$, $R=\lfloor\frac\kappa2\log_2\log N\rfloor$, window
% $[N+R,N+H)$), exactly as in notes/phase25/grh-lambert-windows.md, Proposition C.
```

If Insert A5 is adopted, Paper VI's verification map (`VERIFICATION.md`) and novelty ledger (`LEDGER.md`) would need matching entries. The evidence label would be Lean-supported paper proof for the unconditional range and Conditional for $a>1/2$.

## References

- H. Cramér, Some theorems concerning prime numbers, *Ark. Mat. Astr. Fys.* 15 (1920), no. 5.
- H. Davenport, *Multiplicative Number Theory*, 2nd ed., revised by H. L. Montgomery, Springer GTM 74, 1980 (Chs. 15–17, 19, 20; chapter numbering as in the 3rd edition).
- L. Guth, J. Maynard, New large value estimates for Dirichlet polynomials, arXiv:2405.20552 (2024) (recalled; not rechecked here).
- M. N. Huxley, On the difference between consecutive primes, *Invent. Math.* 15 (1972), 164–170.
- A. Kumchev, The difference between consecutive primes in an arithmetic progression, *Q. J. Math.* 53 (2002), 479–501.
- H. L. Montgomery, R. C. Vaughan, The large sieve, *Mathematika* 20 (1973), 119–134.
- H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, Cambridge University Press, 2007 (Chs. 12–13).
- A. Perelli, J. Pintz, S. Salerno, Bombieri's theorem in short intervals, *Ann. Sc. Norm. Super. Pisa Cl. Sci.* (4) 11 (1984), 529–539 (display (2) with the Huxley–Iwaniec range; used by Mira Cult and audited in P13; cited as PPS 1984).
- A. Perelli, J. Pintz, S. Salerno, Bombieri's theorem in short intervals. II, *Invent. Math.* 79 (1985), 1–9 (Paper VI's key `PPS1985`, level $x^{1/40}$, $7/12<\theta\le1$; cited as PPS or PPS 1985).
- A. Selberg, On the normal density of primes in small intervals, and the difference between consecutive primes, *Arch. Math. Naturvid.* 47 (1943), 87–105.
- P. Shiu, A Brun–Titchmarsh theorem for multiplicative functions, *J. reine angew. Math.* 313 (1980), 161–170.
- Mira Cult, claim 0002, `Mira-Cult/math` at commit `149831943806a656c9efaa14cacbd9c915b2a2ba` (as audited in P13).
- Repository: Paper VI; `GF-22` ([odd-characters-and-kernel-quotient.md](../phase22/odd-characters-and-kernel-quotient.md)); P13 ([erdos-borwein.md](../phase13/erdos-borwein.md)); P13-R ([erdos-local-limit.md](../phase13/reviews/erdos-local-limit.md)).
