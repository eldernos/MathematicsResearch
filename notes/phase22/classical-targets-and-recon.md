# Classical targets: the companion constant $E_+$, the minimal correlation order, the badly-approximable barrier, and five benchmark constants

Phase 22, Track E (E1–E3). Notation follows [classical-barriers.md](../phase21/classical-barriers.md): $D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $0\le n<N$; $K_b=\{x:D_N(x;b)\to1\}$; $F_b(a)=\sum_{n\ge1}a(n)b^{-n}$. For the Erdős–Borwein family

```math
E(b)=\sum_{m\ge1}\frac1{b^m-1},\qquad E_{\rm odd}(b)=\sum_{m\ \rm odd}\frac1{b^m-1},\qquad E_+(b)=\sum_{m\ge1}\frac1{b^m+1},
```

and $E=E(2)$, $E_+=E_+(2)$. The comparison law $Q_\infty$, the packed residue $R_D$, the information classes $\mathcal I_{D,r}$ and $r_{\min}(D)$ are those of the Erdős–Borwein note ([CC-49](../../docs/results.md#cc-49), `papers/09-erdos-borwein-note`).

**Evidence labels.** *Paper proof*; *exact* (integer or rational arithmetic, or a 50-digit identity check in `scripts/phase22_classical.py`); *model* (floating-point evaluation of a comparison model: numerical evidence, not a proof and not a statement about the constant); *finite* (finite digit data, which bears on no limit); *external* (a published or pinned result not re-derived here).

**Summary of conclusions.**

| Result | Evidence |
| --- | --- |
| E1. Scope for $E$: irrational, base-2 disjunctive, unconditional tail mean (known); positive lower word density on windows $H\ge N^{7/12+\varepsilon}$ and hence $D^+(E;2)<1$ (external pinned deduction, not independently verified); normality and simple (non)normality (open everywhere) | External / CC-49 |
| E1. $E_+(b)=E(b)-2E(b^2)=E_{\rm odd}(b)-E(b^2)$; coefficients $a_+(n)=\sum_{d\mid n}(-1)^{d-1}=(1-v_2(n))\tau_{\rm odd}(n)$, zero exactly on $n\equiv2\ (4)$, odd exactly on squares (Proposition 1.1) | Paper proof; exact to $10^5$ |
| E1. $\sum_{n\le X}a_+(n)=X\ln2+O(\sqrt X)$, but $\sum_{n\le X}a_+(n)^2\sim\frac13\sum_{n\le X}\tau(n)^2\asymp X\log^3X$: the logarithm cancels in the mean only (Proposition 1.2) | Paper proof; exact to $10^5$ |
| E1. $E\equiv E_+\pmod{K_2}$ would force $E(4)\in K_4$; the four numbers $E,E_+,E_{\rm odd},E(4)$ obey only triangle constraints from the identities (Proposition 1.3) | Paper proof |
| E1. Signed digit identity and unconditional tail means $\mu^{\rm pos}=\mu_{\rm odd}/2\approx0.7012$, $\mu^{\rm neg}=\mu_{\rm odd}E_2/4=\mu/4\approx0.5191$ for $E_+$ (Proposition 1.4); signed knapsack inequality (Lemma 1.5) | Paper proof |
| E1. Signed comparison model for $E_+$: source rate $3/4$, predicted first-digit frequency $p_+\approx0.47783$, bias $1/2-p_+\approx0.0222$, about $2.9$ times the bias of $E$ | Model |
| E1. Column threshold for $E_+$ is $14$ in the model ($f^{\sup}_{13}\approx0.5081>1/2>0.49986\approx f^{\sup}_{14}$), against $16$ for $E$ (§1.6) | Model |
| E1(a). **Test-function invariance**: no test function of any form (rational, piecewise linear, smoothed) lowers $r_{\min}(D)$; an expectation is determined by order-$\le r$ information iff the function is a polynomial of degree $\le r$ on the lattice (Theorem 2.1) | Paper proof |
| E1(a). **$7\le r_{\min}(D)$ for every $D\ge2$, and $7\le r_{\min}(D)\le92$ for every $D\ge16$**: exact rational two-column laws in $\mathcal I_{D,6}$ (resp. $\mathcal I_{D,5}$) with certified $f(1)\ge0.518826$ (resp. $0.528931$) (Theorem 2.2); $r_{\min}$ is non-increasing in $D$ by mark projection (Proposition 2.4). Previously $r_{\min}(D)\ge5$ for all $D$ ($\ge7$ at $D=17$, $\ge9$ at $D=16$), with an upper bound only at $D=16$ | Exact moments + finite certificate (outward-rounded enclosures of the five model inputs); Proposition 2.4: paper proof |
| E2. **Kempner–Shallit barrier**: $\kappa=\sum_{k\ge0}2^{-2^k}$ is badly approximable ($\lVert q\kappa\rVert\ge1/(8q)$) and transcendental, yet $1-D_N(\kappa;2)\le(\log_2N+2)^2/N$; so no hypothesis on Diophantine approximation quality alone can give $D^+<1$ or exclude $K_2$ (Proposition 3.1, Corollary 3.2) | Paper proof + external (Shallit 1979); exact for 2048 partial quotients |
| E2. $D^+(\ln2;2)\le0.9999$; any digit statement for $\ln2,\ln3,\arctan\frac12,\pi$ | **Open** |
| E3. Cahen's constant: reduced denominator of the $K$-th partial sum is $\prod_{j<K,\,K-j\ \rm odd}s_j=s_K^{2/3+o(1)}$, error $\sim1/(s_K(s_K-1))$, so the partial sums have approximation exponent exactly 3 (Proposition 4.1) | Paper proof; exact for $K\le12$ |
| E3. $\psi=\sum1/F_n=\sqrt5\bigl(\tfrac14\theta_2(q)^2+\sum_{m\ \rm odd}q^m/(1-q^m)\bigr)$, $q=\varphi^{-2}$: in the radix $\varphi^2$ it is an $E_{\rm odd}$-type value plus a sparse theta value (Proposition 4.2) | Paper proof (Landau); exact |
| E3. $C(1/b)=\sum C_nb^{-n}=(b-\sqrt{b^2-4b})/2$ and $\sum\binom{2n}nb^{-n}=\sqrt{b/(b-4)}$ ($b\ge5$); e.g. $\sqrt2=\sum\binom{2n}n8^{-n}$: positive integer coefficients with exponential mass give quadratic irrationals (Proposition 4.3) | Paper proof; exact |
| E3. Apéry's series: every prime $p\ge3$ in $(n/2,n]$ divides the reduced denominator of the $n$-th partial sum exactly to the third power (Proposition 4.4) | Paper proof; exact for $3\le n\le400$ |
| E3. $C_1=[0;1,2,3,\dots]=I_1(2)/I_0(2)$: $\lvert C_1-p_n/q_n\rvert\,q_nq_{n+1}\to1$, $q_{n+1}\sim(n+1)q_n$, $\mu=2$ (Proposition 4.5) | Paper proof (classical); exact |
| E3. Digit statistics of $C,\psi,C(1/b),\zeta(3),C_1$ | **Open** for each; finite data only |

Nothing in this note proves normality, simple normality, simple nonnormality or $D^+<1$ for $\ln2$, $\pi$, $e$, $\sqrt2$, $\varphi$, $E$, $E_+$, Cahen's constant, $\psi$, $\zeta(3)$ or $C_1$.

## 1. E1 — the Erdős–Borwein constant and its companion $E_+$

### 1.1 What is known about $E$, and from where

| Statement about $E=\sum1/(2^n-1)$ | Status | Source |
| --- | --- | --- |
| Irrational | Known | Erdős (1948); Vandehey completed the argument for negative bases |
| Base-2 disjunctive (every word occurs) | Known | Captain Sude (public work; see CC-49 §related) |
| $11$ occurs infinitely often | Known | Campbell (2026) |
| Mean of the displaced tail: $\mu\in[2.0762592,2.0763285]$; $\mathbb E_I Y_D=\mu+o(1)$ | Proved | CC-49, Proposition "one-source mean and tail mean" and Theorem "certified enclosures" |
| Positive lower density of every word on windows $H\ge N^{7/12+\varepsilon}$; consequently $D^+(E;2)<1$ | **External input, independent verification open** | Mira Cult, `Mira-Cult/math` commit `1498319`; the deduction holds *if* its analytic inputs are verified. Not claimed as proved here |
| Comparison-model frequency $p_*\in[0.492450290,0.492460864]$ | Model constant (certified enclosure of a model quantity) | CC-49, Theorem "certified enclosures" |
| Simple nonnormality ($f(1)<1/2$), simple normality, normality | **Open everywhere** | — |

The model value $p_*<1/2$ is a prediction about a random comparison law, not about $E$. CC-49 determines which finite statistics of the real columns would turn it into a theorem: a bounded statistic of $16$ columns suffices, $15$ do not, and order-$r$ moment information with $9\le r_{\min}(16)\le92$. Section 2 below improves the universal lower bound on $r_{\min}$.

### 1.2 The identities for $E_+(b)$

**Proposition 1.1.** For every integer $b\ge2$,

```math
E_+(b)=E(b)-2E(b^2)=E_{\rm odd}(b)-E(b^2),\qquad E(b)+E_+(b)=2E_{\rm odd}(b),\qquad E(b)-E_+(b)=2E(b^2),
```

and $E_+(b)=\sum_{n\ge1}a_+(n)b^{-n}$ with

```math
a_+(n)=\sum_{d\mid n}(-1)^{d-1}=\tau(n)-2[2\mid n]\,\tau(n/2)=(1-e)\,\tau(m)\qquad(n=2^em,\ m\ \text{odd}).
```

So $a_+(n)=\tau(m)>0$ for odd $n$, $a_+(n)=0$ exactly for $n\equiv2\pmod4$, and $a_+(n)=-(e-1)\tau(m)<0$ for $4\mid n$. Moreover $a_+(n)\equiv\tau(n)\pmod2$, so $a_+(n)$ is odd exactly when $n$ is a perfect square.

*Proof.* $1/(x-1)-2/(x^2-1)=(x+1-2)/(x^2-1)=1/(x+1)$ with $x=b^n$; sum over $n$ and use $E(b)=E_{\rm odd}(b)+E(b^2)$. Expanding $1/(b^n+1)=\sum_{k\ge1}(-1)^{k-1}b^{-kn}$ gives the coefficient $\sum_{kd=n}(-1)^{k-1}=\sum_{d\mid n}(-1)^{d-1}$ (exchange $d\leftrightarrow n/d$). With $n=2^em$, $\tau(n)=(e+1)\tau(m)$ and $\tau(n/2)=e\tau(m)$ for $e\ge1$. Finally $(1-e)\tau(m)\equiv(1+e)\tau(m)=\tau(n)\pmod 2$, and $\tau(n)$ is odd iff $n$ is a square. ∎

The real identities are checked to 50 digits for $b=2,3,10$ and the coefficient identities for $n\le10^5$. Numerically $E_+=0.76449978034844420919\ldots=0.11000011101101100100\ldots_2$. Its irrationality is a case of P. Borwein's theorem on $\sum1/(q^n+r)$ (J. Number Theory 37 (1991)), external input.

### 1.3 The mean cancels, the fluctuations do not

**Proposition 1.2.** (a) $\sum_{n\ge1}a_+(n)n^{-s}=(1-2^{1-s})\zeta(s)^2=\eta(s)\zeta(s)$, and

```math
\sum_{n\le X}a_+(n)=\sum_{d\le X}(-1)^{d-1}\Bigl\lfloor\frac Xd\Bigr\rfloor=X\ln2+O(\sqrt X).
```

(b) $\sum_{n\le X}a_+(n)^2\sim\frac13\sum_{n\le X}\tau(n)^2\sim\dfrac{X\log^3X}{3\pi^2}$.

*Proof.* (a) The Dirichlet series follows from $a_+=\tau-2\,\tau(\cdot/2)$. The hyperbola identity is the definition of $a_+$ summed over $n$. With $\Delta(X)=\sum_{n\le X}\tau(n)-X(\log X+2\gamma-1)=O(\sqrt X)$, $\sum_{n\le X}a_+(n)=\sum_{n\le X}\tau(n)-2\sum_{m\le X/2}\tau(m)=X\ln2+\Delta(X)-2\Delta(X/2)$. (b) $a_+^2$ and $\tau^2$ are multiplicative and agree at odd primes. At $p=2$ the local factors at $s=1$ are $\sum_e(1-e)^22^{-e}=4$ and $\sum_e(e+1)^22^{-e}=12$. Since $\sum\tau(n)^2n^{-s}=\zeta(s)^4/\zeta(2s)$ has a pole of order 4, the ratio of the two summatory functions tends to the ratio $1/3$ of the local factors. ∎

The finite values are $\sum_{n\le X}a_+(n)=689$, $6916$, $69300$ at $X=10^3,10^4,10^5$, against $X\ln2=693.15$, $6931.47$, $69314.72$. The ratio in (b) is $0.304$, $0.307$, $0.310$, approaching $1/3$ slowly.

**What this does and does not mean.** The $\log X$ terms cancel *in the mean*: the raw tail $T_n=\sum_{j\ge1}a_+(n+j)2^{-j}$ has window mean $\ln2+o(1)$, while the raw tail of $E$ has mean $\log n+O(1)$. This is not a reduction of randomness. By (b) the coefficients still have size $(\log n)^{3/2}$ in mean square, now with both signs. For the digits, what matters is the *displaced* tail of §1.4, and the displaced tail of $E$ is already bounded on average ($\mu\approx2.076$, CC-49). The cancellation therefore does not make $E_+$ more tractable. Its consequence for the comparison model is different and is computed in §1.5: a lower source rate, which raises the predicted bias.

### 1.4 Kernel relations among $E,E_+,E_{\rm odd},E(4)$

**Proposition 1.3.** Work in base 2 and let $u_N,v_N,w_N,z_N$ be $1-D_N$ of $E,E_+,E_{\rm odd},E(4)$ respectively.

1. $|D_N(2x;2)-D_N(x;2)|\le1/N$ for every real $x$. Hence $1-D_N(E-E_+)=z_N+O(1/N)$ and $1-D_N(E+E_+)=w_N+O(1/N)$.
2. Up to $O(1/N)$, the triples $(u_N,v_N,z_N)$ and $(u_N,v_N,w_N)$ satisfy the three triangle inequalities, as $(u_N,w_N,z_N)$ does by Phase 21 Proposition 2.1.
3. If $E-E_+\in K_2$, then $E(4)\in K_4$. If $E+E_+\in K_2$, then $E_{\rm odd}\in K_2$.

*Proof.* (1) The orbit of $2x$ under doubling is the orbit of $x$ shifted by one step, so one $N$-point set arises from the other by removing one point and adding one; every interval count changes by at most $1$. (2) $d_N(s,t)=1-D_N(s-t)$ is a pseudometric with $d_N(s,-t)=1-D_N(s+t)$; apply it to $0,E,E_+$ and to $0,E,-E_+$, and use (1). (3) $E-E_+=2E(4)$ and $E+E_+=2E_{\rm odd}$; use (1) and Phase 21 Proposition 2.2 ($K_2\subseteq K_4$). ∎

So $E$ and $E_+$ are the sum and the difference of the same two numbers $E_{\rm odd}$ and $E(4)$. A relation between $E$ and $E_+$ modulo $K_2$ is at least as hard as a kernel statement about $E(4)$ in its own radix $4$ (expected false), or about $E_{\rm odd}$ in base 2 (expected false). By the addition spectrum of [OP-01](../phase19/addition.md), nothing beyond these triangle constraints follows from the identities alone.

### 1.5 The signed digit identity, tail means and comparison model for $E_+$

Write $a_+(m)=\sigma(m)2^{V_+(m)}U_+(m)$ with $\sigma(m)=\pm1$ and $U_+(m)$ odd, for $a_+(m)\ne0$. With $m=2^em'$:

- for $e=0$: $\sigma=+1$, $U_+=U(m')$ (the odd part of $\tau(m')$);
- for $e\ge2$: $\sigma=-1$, $U_+=\operatorname{odd}(e-1)\,U(m')$.

The source $m$ deposits the signed odd mark $\sigma U_+$ at position $t(m)=m-V_+(m)$. Since $|a_+(m)|\le\tau(m)$, we have $V_+(m)\le\log_2m$.

**Lemma (signed digit identity).** The digit identity of CC-49 (Lemma "digit identity") holds verbatim with signed column totals $C(t)=\sum_{t(m)=t}\sigma(m)U_+(m)\in\mathbb Z$: the $(n{+}1)$-st binary digit of $E_+$ is the top bit of $(R_D(n)+\lfloor Y_D(n)\rfloor)\bmod2^D$, where now $\lfloor Y_D\rfloor$ may be negative. *Proof:* the proof of CC-49 Lemma "digit identity" uses only integrality of the column totals. ∎

**Proposition 1.4 (unconditional tail means).** Split $Y_D=Y_D^+-Y_D^-$ into the contributions of positive and negative sources, and let $I=[N,2N)$. For every fixed $D$,

```math
\mathbb E_IY_D^+=\mu^{\rm pos}+o(1),\quad \mathbb E_IY_D^-=\mu^{\rm neg}+o(1),\qquad
\mu^{\rm pos}=\frac{\mu_{\rm odd}}2,\quad \mu^{\rm neg}=\frac{\mu_{\rm odd}E_2}4,
```

where $\mu_{\rm odd}=\prod_{p>2}\mathbb E\operatorname{odd}(B_p+1)$ and $E_2=\sum_{k\ge1}\operatorname{odd}(k)2^{-k}=1.4804922\ldots$. Thus $\mu=E_2\mu_{\rm odd}$, so $\mu^{\rm neg}=\mu/4\in[0.5190648,0.5190822]$ inherits the certified CC-49 enclosure of $\mu$; $\mu^{\rm pos}\approx0.70123$, and the net mean is $\mu_{\rm odd}(1/2-E_2/4)\approx0.18215$.

*Proof.* As in CC-49 Proposition "one-source mean and tail mean": $U=1*a$ with $a$ supported on squarefull integers, so $\sum_{m'\le X,\ m'\ \rm odd}U(m')=X\mu_{\rm odd}/2+O(X^{1/2+\varepsilon})$. Summing over $e$ with weights $\operatorname{odd}(e-1)$ gives the negative mass $X\mu_{\rm odd}\sum_{e\ge2}\operatorname{odd}(e-1)2^{-e-1}=X\mu_{\rm odd}E_2/4$. The displacement strip is handled exactly as there, using $V_+(m)\le\log_2m$, and the columns $d>N$ by the bound $|C(t)|\le\sum_{m\le2t+3}\tau(m)$. ∎

**The signed comparison model $Q_+$.** Each column has an independent Poisson$(3/4)$ number of sources: $3/4$ is the density of nonzero $a_+$. A source is positive with probability $2/3$ and then carries a mark of law $\nu_{\rm odd}$ (the law of $\prod_{p>2}\operatorname{odd}(B_p+1)$). With probability $1/3$ it is negative and carries the mark $\operatorname{odd}(e-1)U$, where $\Pr(e)=2^{-(e-1)}$ for $e\ge2$ and $U\sim\nu_{\rm odd}$ is independent. Since marks are odd, the parity of column $1$ is that of a Poisson$(3/4)$ count, $\mathbb E(-1)^{C_1}=e^{-3/2}$. Exactly as in CC-49 Proposition "value of $p_*$",

```math
p_+=\frac12-\frac12e^{-3/2}\,\mathbb E(-1)^{c_1},\qquad c_1=\Bigl\lfloor\sum_{d\ge2}C_d2^{1-d}\Bigr\rfloor .
```

*Model values* (same code reproduces CC-49: $\mu=2.076317$, $\mathbb E(-1)^{c_1}=0.111490$, $p_*=0.492456$, inside the certified enclosures):

| | source rate | $\mathbb E(-1)^{c_1}$ | predicted $f(1)$ | bias $1/2-f(1)$ |
| --- | --- | --- | --- | --- |
| $E$ | $1$ | $0.111490$ | $0.492456$ | $0.007544$ |
| $E_+$ | $3/4$ | $0.198676$ | $0.477835$ | $0.022165$ |

Two effects combine. The column parity factor $e^{-3/2}=0.2231$ exceeds $e^{-2}=0.1353$ because the source rate drops to $3/4$, which is exactly the effect of the zeros at $n\equiv2\pmod 4$. The carry parity also nearly doubles, because the signed tail has small net mean and the carry concentrates on $\{0,-1\}$ (model law: $0.506$ on $0$, $0.259$ on $-1$, $0.113$ on $1$). This is a statement about the model, not about $E_+$.

### 1.6 A signed knapsack and the column threshold for $E_+$

**Lemma 1.5 (signed knapsack).** For integers $D\ge1$, $0\le r<2^D$, reals $y^\pm\ge0$, $c=\lfloor y^+-y^-\rfloor$ and $\lambda,\lambda'\ge0$,

```math
\mathbf 1\bigl[2^{D-1}\le(r+c)\bmod2^D\bigr]\le\mathbf 1[r\ge2^{D-1}]+\lambda y^++\lambda'y^-+\mathbf 1[r<2^{D-1}]\max\bigl((1-\lambda(2^{D-1}-r))^+,\ (1-\lambda'r)^+\bigr).
```

*Proof.* If $r\ge2^{D-1}$ the right side is at least 1. Let $r<2^{D-1}$. If $c\ge0$, the digit is 1 only if $c\ge2^{D-1}-r$, and then $y^+\ge c$. The Lean inequality `carry_knapsack_le` applied to $c$ gives the bound, since $\lambda c\le\lambda y^+$. If $c<0$, the digit is 1 only if $r+c<0$, that is $y^--y^+>r$, so $y^->r$, and $\lambda'y^-+(1-\lambda'r)^+\ge1$. ∎

Averaging over a window and using Proposition 1.4 turns this into a two-budget fractional knapsack. Cells $2^{D-1}-k$ move up at cost $k$ against the budget $\mu^{\rm pos}$. Cells $r=j$ move up (by wrapping) at cost $j$ against the budget $\mu^{\rm neg}$; in particular the cell $r=0$ moves for free. The primal construction is that of CC-49 Theorem "sharpness", with $Y^-=j+\varepsilon$ on moved low cells. As in CC-49, the class $\mathcal I^+_D$ consists of laws whose first $D$ columns are i.i.d. copies of the $Q_+$ column and whose later columns respect the two tail means; $f^{\sup}_D$ is the supremum of $f(1)$ over it.

*Model values* of $f^{\sup}_D$, floating point. The three $E$ entries reproduce the certified CC-49 table, which validates the code; that table gives $[.505523,.509093]$, $[.502823,.502828]$ and $[.499732,.499736]$ at $D=14,15,16$.

| $D$ | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $E$ | | | | | 0.507245 | 0.502826 | **0.499734** |
| $E_+$ | 0.557375 | 0.535373 | 0.519625 | 0.508114 | **0.499863** | | |

In this model **$14$ columns suffice for $E_+$** ($f^{\sup}_{14}\approx0.499863$, margin $1.4\times10^{-4}$) and $13$ do not ($f^{\sup}_{13}\approx0.508114$). For $E$ the threshold is $16$ (margin $2.7\times10^{-4}$). The saving of two columns comes from the larger bias; it is partly offset by the free wrap of the cell $r=0$ and by the second budget.

These are model computations of the same kind as the CC-49 table. They are not certified, and they concern the abstract class $\mathcal I_D^+$, not the real columns of $E_+$. `python -B scripts/phase22_classical.py --thresholds` (about six minutes) recomputes the entries $E$, $D=15,16$ (checked against the certified CC-49 intervals) and $E_+$, $D=12,13,14$ (checked for the threshold at $14$). The remaining entries come from the same code with other $D$. The default run omits this section.

### 1.7 Finite data

Exact binary digits ($2^{19}$ digits, 64 guard bits, all digits certain). These are finite observations only.

| shell $s$ (shifts $n\in[2^s,2^{s+1})$, digits $2^s+1..2^{s+1}$) | 12 | 13 | 14 | 15 | 16 | 17 | 18 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $E$: proportion of 1s | 0.514404 | 0.514038 | 0.507751 | 0.510254 | 0.509232 | 0.502670 | 0.500923 |
| $E_+$: proportion of 1s | 0.495117 | 0.489258 | 0.497864 | 0.492554 | 0.492523 | 0.488930 | 0.489449 |

$D_N(E;2)=0.0332,0.0223,0.0203$ and $D_N(E_+;2)=0.0641,0.0147,0.0103$ at $N=10^3,10^4,10^5$. The $E$ shells match CC-49 (which continues to $0.4937$ at $s=23$). The $E_+$ shells lie below $1/2$ at every shell in this range, but $\log\log N<2.6$ here, and the model limit $0.4778$ is a model value. **No limit statement follows.**

### 1.8 Open for $E_+$

Disjunctivity of $E_+$ is not established here. We did not examine whether Captain Sude's method for $E$ transfers to signed coefficients, and the signed columns allow cancellation between positive and negative sources. Normality, simple (non)normality, $D^+(E_+;2)<1$ and $E_+\notin K_2$ are open. The model suggests $E_+$ as a *better-conditioned* target for simple nonnormality than $E$: the predicted bias is about three times larger and the column threshold about two columns smaller. The arithmetic input needed is of the same kind, a joint law of $(v_2,\ \text{odd part})$ of $a_+$ at consecutive integers.

## 2. E1(a) — the minimal correlation order

### 2.1 The form of the test function is irrelevant

Let $\mathcal C$ be a class of laws of a random vector $\vec N\in\mathbb Z_{\ge0}^k$ (with any further coupled tail), defined by prescribing finitely many expectations: here, all mixed factorial moments of total order $\le r$ together with the tail means, as in $\mathcal I_{D,r}$.

**Theorem 2.1 (test-function invariance).**

1. *(Weak duality.)* If a conclusion "$f(1)<1/2$" is deduced from the information defining $\mathcal C$ alone, by any argument whatsoever (polynomial, rational or piecewise-linear majorants, characteristic-function smoothing, LP or SDP certificates), then every law in $\mathcal C$ satisfies $f(1)<1/2$. Hence a single law in $\mathcal C$ with $f(1)\ge1/2$ defeats every such argument, and $r_{\min}(D)$ is a property of the information, not of the test function.
2. *(Determinacy.)* For a function $\phi:\mathbb Z_{\ge0}^k\to\mathbb R$ with $\mathbb E_{Q_\infty}|\phi|<\infty$, the following are equivalent: (a) $\mathbb E\phi$ takes the same value on all finitely supported perturbations of $Q_\infty$ in $\mathcal C$ (the factorial moments of order $\le r$ being fixed); (b) $\phi$ agrees on $\mathbb Z^k_{\ge0}$ with a polynomial of total degree $\le r$.

*Proof.* (1) A valid deduction from the defining information is a statement true of every law having that information. (2) (b)⇒(a): a polynomial of degree $\le r$ is a fixed linear combination of the products $\prod_i\binom{n_i}{j_i}$ with $\sum j_i\le r$, whose expectations are prescribed. (a)⇒(b): suppose $\phi$ does not agree with a polynomial of degree $\le r$ on some finite box $S=\{0,\dots,M\}^k$ with $M\ge r$. Then $\phi|_S$ is not in the span of the restricted binomial products. So there is a signed measure $\sigma$ on $S$ annihilating every $\prod\binom{n_i}{j_i}$ with $\sum j_i\le r$ (including the constant) with $\sum\sigma\phi\ne0$. Since $Q_\infty$ gives positive mass to every point of $S$, $Q_\infty\pm\varepsilon\sigma$ are probability laws in $\mathcal C$ for small $\varepsilon$ (the tail is untouched), and $\mathbb E\phi$ differs between them. If $\phi$ agrees with a degree-$\le r$ polynomial $P_M$ on every box, the polynomials coincide (a polynomial of degree $\le r$ is determined by its values on $\{0,\dots,r\}^k$), so $\phi$ is a polynomial. ∎

**Consequences for the CC-49 programme.**

- Non-polynomial one-sided test functions on $\Psi_{16}$ (rational, piecewise linear, smoothed) cannot lower $r_{\min}(16)$, and their expectations are not even determined by order-$r$ information. What can shorten the *witness* is a better polynomial majorant of degree $r$: the interval $9\le r_{\min}(16)\le92$ is a gap between a countermodel bound and a particular polynomial witness (Bonferroni–Jordan truncation). Closing it is a multivariate moment LP on the $16$-column count vector, as CC-49 already notes.
- Characteristic-function and Fourier methods use $\mathbb E\,e(m\,2^nE)$, which are infinite-order statistics. They sit outside every $\mathcal I_{D,r}$. That is the CC-49 Fourier route (degree $116$ suffices numerically, degree $\le110$ does not), a different information axis.

### 2.2 Two columns already force order seven

CC-49's countermodels perturb only column 1, changing the parity $\mathbb E(-1)^{N_1}$ from $e^{-2}$ to the parity Bonferroni minimum $e_r$ ($e_5=1/15$, $e_7=41/315$, $e_9=383/2835$). On infinitely many columns that family fails from $r=5$ on, since $e_5>0$. The column-1 parity can instead be *correlated with the next column*. Under $Q_\infty$ the first digit is $(N_1+c_1)\bmod2$ with $c_1=\lfloor(C_2+c_2)/2\rfloor$, and $c_2$ is an independent stationary carry. Put

```math
h(n)=\mathbb E\bigl[(-1)^{c_1}\bigm|N_2=n\bigr]=\sum_{a,b\bmod4}\Pr(S_n\equiv a)\Pr(c_2\equiv b)\,g(a+b),\qquad g=(1,1,-1,-1),
```

where $S_n$ is a sum of $n$ independent marks (only $\Pr(U\equiv1\bmod4)$ enters). For any law of $(N_1,N_2)$ with i.i.d. marks given the counts, and all other columns as in $Q_\infty$,

```math
f(1)=\frac12-\frac12\,\mathbb E\bigl[(-1)^{N_1}h(N_2)\bigr].
```

Such a law lies in $\mathcal I_{D,r}$ for every $D\ge2$ exactly when $\mathbb E[(N_1)_i(N_2)_j]=1$ for all $i+j\le r$. Given the counts, the marked counts are multinomial, so all mixed marked factorial moments reduce to these. The tail and columns $\ge3$ are untouched, so the tail mean is $\mu$. Minimizing $\mathbb E[(-1)^{N_1}h(N_2)]$ is a linear programme.

**Theorem 2.2.** For $r=5$ and $r=6$ there are explicit laws $\rho_r$ on $\{0,\dots,12\}^2$ with rational weights ($17$ and $25$ atoms, listed in `scripts/phase22_classical.py`) such that:

1. *(exact)* $\mathbb E_{\rho_r}\binom{N_1}i\binom{N_2}j=1/(i!\,j!)$ for all $i+j\le r$ (exact rational arithmetic), so $\rho_r$ with i.i.d. marks and $Q_\infty$ elsewhere lies in $\mathcal I_{D,r}$ for every $D\ge2$;
2. *(finite certificate)* $f(1)\ge0.528931$ for $\rho_5$ and $f(1)\ge0.518826$ for $\rho_6$. The floating-point model values are $0.529672$ and $0.519371$.

*The five inputs, and their certificate.* Since every mark is odd, $S_n\bmod4$ moves by $\pm1$, so $\mathbb E\,i^{S_n}=(i\,t)^n$ with $t=2\Pr(U\equiv1\bmod4)-1$. With $g(x)=\mathrm{Re}\,i^x+\mathrm{Im}\,i^x$ this gives the closed form

```math
h(n)=t^n\sum_{b=0}^{3}\Pr(c_2\equiv b\bmod 4)\,g(n+b),
```

so $f(1)$ for $\rho_r$ is $\frac12-\frac12\bigl(A_0P_0(t)+A_1P_1(t)\bigr)$. Here $A_m=\sum_b\Pr(c_2\equiv b)g(m+b)$ and $P_0,P_1$ are explicit rational polynomials determined by $\rho_r$. The script encloses the five inputs with outward rounding: integer lower measures at scale $2^{64}$, every product and quotient floored.

- *Marks:* primes $p\le4000$ exactly, marks $\le511$. Primes $p>4000$ act trivially on the event $\{B_p\le1\ \forall p>4000\}$, of probability $\ge1-\sum_{n>4000,\ n\ \rm odd}n^{-2}\ge1-1/7998$.
- *Column law:* the Panjer recursion, monotone in the mark measure, from a rational lower bound for $e^{-1}$, with $J\le255$.
- *Carry:* $18$ carry steps. The depth truncation costs $\Pr(c\ne c^{(18)})\le\mathbb E\lfloor Y_{18}\rfloor\max_r\Pr(R_{18}=r)\le\mu\,p_0^{18}$, by CC-49 Lemma "depth truncation", with $\mu\le2.0763285$ (CC-49 certified enclosure) and $p_0<0.5677$.

The missing mass is charged to both sides. The certified intervals are $\Pr(U\equiv1\bmod4)\in[0.752169,0.752294]$ and carry residues $[0.353493,0.355913]$, $[0.342887,0.345306]$, $[0.200876,0.203295]$, $[0.100169,0.102589]$; the floating-point values lie inside. Interval evaluation of $A_0P_0(t)+A_1P_1(t)$ over these boxes (exact rational arithmetic; $t>0$, so each polynomial is split into its positive and negative parts) gives the two certified lower bounds of (2). The comparison law $Q_\infty$ and Lemma "depth truncation" are CC-49's; nothing here concerns the real columns of $E$.

Suppose each of the five inputs ($\Pr(U\equiv1\bmod4)$ and the four carry-residue probabilities) moves by at most $\delta$, keeping probability vectors. Then $|\Delta h(n)|\le\lVert\Delta L_n\rVert_1+\lVert\Delta c\rVert_1\le(2n+4)\delta$, where $L_n$ is the law of $S_n\bmod4$. Since $\mathbb E_{\rho_r}N_2=1$ exactly, the objective moves by at most $6\delta$, so the model conclusion $f(1)>1/2$ survives any error below $0.0098$ (resp. $0.0064$; radii rounded down) in those inputs. The certified enclosures above have half-widths at most $0.0013$. The model gives $\Pr(U\equiv1\bmod4)=0.752250$ and carry residues $(0.354292,0.343738,0.201435,0.100498)$; $\mathbb Eh(N_2)=0.111490$ reproduces CC-49's $\mathbb E(-1)^{c_1}$.

**Corollary 2.3.** $r_{\min}(D)\ge7$ for every $D\ge2$. With CC-49: $r_{\min}(D)=\infty$ for $D\le15$ (the countermodels of CC-49 Theorem "sharpness" have exact $D$-column laws), $9\le r_{\min}(16)\le92$, and, by Proposition 2.4, $7\le r_{\min}(D)\le92$ for every $D\ge17$. Theorem 2.2(1) is exact and Theorem 2.2(2) is a finite certificate, so the lower bound is certified within the comparison framework of CC-49.

**Proposition 2.4 (monotonicity in $D$).** For $1\le D<D'$ and $r\ge1$, $r_{\min}(D')\le r_{\min}(D)$. In particular $r_{\min}(D)\le r_{\min}(16)\le92$ for every $D\ge16$.

*Proof.* Take a law in $\mathcal I_{D',r}$ and replace every mark $u$ in each column $d\in\{D+1,\dots,D'\}$ by $u\bmod2^d\in\{1,3,\dots,2^d-1\}$. This changes $\sum_{d\ge2}C_d2^{1-d}$ by an even integer (a multiple of $2^d$ in column $d$ moves it by a multiple of $2$), so $c_1$ keeps its parity and the first digit is unchanged pointwise. Columns $1,\dots,D$ are untouched, so their mixed factorial moments of order $\le r$ still equal the $Q_\infty$ values. The order-$1$ moments of the class $\mathcal I_{D',r}$ give $\mathbb EN_{d,c}=\nu_d(c)$, so the projected column $d$ has mean $\sum_cc\,\nu_d(c)=\mathbb E[U_*\bmod2^d]\le\mu$, and columns $d>D'$ already have mean $\le\mu$. Hence the projected law lies in $\mathcal I_{D,r}$ and has the same $f(1)$. So if every law in $\mathcal I_{D,r}$ has $f(1)<1/2$, so does every law in $\mathcal I_{D',r}$. ∎

The sets themselves are not nested ($\mathcal I_{D',r}\not\subseteq\mathcal I_{D,r}$ in general, because residue counts do not bound mean mark totals); the projection is what makes the comparison work.

The previous universal bound was $r_{\min}(D)\ge5$ (CC-49 Theorem "low order fails"(a)); for $D\ge18$ nothing better was recorded, and no upper bound was recorded for $D\ge17$. In the correlation bookkeeping of CC-49 ("what the arithmetic would have to supply"), any argument through mixed moments of the column counts, on any number of columns, needs at least $7$-point correlations of $(V,U)$ at shifted arguments.

**Where two columns stop.** The same programme at $r=7$ (supports $\{0,\dots,10\}^2$ and $\{0,\dots,14\}^2$) gives maximal $f(1)\approx0.4987<1/2$, so on these supports the two-column family is exhausted at order $7$ (model; larger supports were not tried). Correlating column 1 with columns 2 and 3 jointly is the next step. The function $h$ then depends on $(N_2,N_3)$ through residues modulo 8. That programme is not solved here, and whether $r_{\min}(D)\ge8$ holds for all $D$ is open here.

## 3. E2 — $\ln2$: the badly-approximable barrier

Denominator-only and complete-period routes (CC-42, CC-43, CC-50, OP-11, GF-09) are not revisited. This section isolates what *any* method based on approximation quality can give.

### 3.1 Runs and approximation quality

A run of $L$ equal binary digits after position $n$ gives a dyadic rational $a/2^n$ with $|x-a/2^n|\le2^{-n-L}$, i.e. approximation exponent $1+L/n$ with denominator $2^n$. So $\mu(x)<\infty$ bounds each run, $L\le(\mu-1+\varepsilon)n$, and hence forces at least a constant times $\log N$ transitions. That is the classical mechanism behind the $\Omega(\log N)$ transition counts for $\ln2$, $\pi$, $e$ (CC-50 table). It constrains each run separately. It says nothing about the *sum* of run lengths, and nothing about runs of length $o(n)$, which are what decide $D^+<1$.

### 3.2 Kempner's number

**Proposition 3.1.** Let $\kappa=\sum_{k\ge0}2^{-2^k}=0.8164215090\ldots$.

1. *(External: Shallit, J. Number Theory 11 (1979) 209–217.)* The partial quotients of $\kappa$ are bounded; Shallit's explicit folding description gives $a_1=1$ and $a_n\in\{2,4,6\}$ for $n\ge2$. Hence $\lVert q\kappa\rVert\ge1/(8q)$ for all $q\ge1$, and $\mu(\kappa)=2$. *(Exact check: the first $2048$ partial quotients, certified by comparing the continued fractions of both ends of an enclosing interval, are $[0;1,4,2,4,4,6,4,2,4,6,2,4,6,\dots]$ with values in $\{2,4,6\}$ after $a_1$; Shallit's folding construction gives all $n$.)*
2. *(External: Kempner 1916.)* $\kappa$ is transcendental.
3. *(Paper proof.)* $1-D_N(\kappa;2)\le(\log_2N+2)^2/N$ for $N\ge2$; in particular $\kappa\in K_2$.

*Proof of 3.* Let $L=\lfloor\log_2N\rfloor$. A point $\{2^n\kappa\}$ with $n<N$ lies outside $[0,2^{-L}]$ only if one of the digits $n+1,\dots,n+L$ is $1$, that is $2^k\in(n,n+L]$ for some $k$. Each of the at most $\log_2(N+L)+1$ relevant $k$ excludes at most $L$ values of $n$. The remaining points have digits $n+1,\dots,n+L$ equal to $0$, so they lie in $[0,2^{-L}]$, an interval of length at most $2/N$. Hence $D_N\ge1-L(\log_2N+2)/N-2/N$, and $1-D_N\le(L(\log_2N+2)+2)/N\le(\log_2N+2)^2/N$. ∎

The exact values are $N(1-D_N)/(\log_2N)^2=0.563,0.580,0.604,0.622$ at $N=2^8,2^{10},2^{12},2^{14}$: the order $(\log N)^2/N$ is attained.

**Corollary 3.2 (barrier).** Let $\mathcal H$ be any hypothesis on a real number that is satisfied by every badly approximable number with partial quotients $\le6$: for instance "$\lVert qx\rVert\ge c/q$ for all $q$" with $c\le1/8$, "$\mu(x)\le\mu_0$" for any $\mu_0\ge2$, or "$x$ is transcendental with $\mu(x)=2$". Then $\mathcal H$ does not imply $D^+(x;2)<1$, nor $D^-(x;2)<1$, nor $x\notin K_2$.

By Dirichlet, $\lVert qx\rVert\le1/q$ infinitely often for every irrational $x$, so $c/q$ is the strongest possible lower bound and Kempner's number attains it up to the constant. **No improvement of $\mu(\ln2)\le3.5746$ (Marcovecchio 2009), even to $\mu=2$ or to bounded partial quotients, could by itself yield $D^+(\ln2;2)\le0.9999$.** The same holds for $\pi$, $\zeta(3)$, Cahen's constant and $C_1$ (§4), and makes sharp the CC-50 remark that $\mu(e)=2$ "only forces $O(\log N)$ transitions". Kempner's number also answers the multiple-run question. At $\mu=2$ its digits $2^k+1,\dots,2^{k+1}-1$ form a single run of zeros of length $2^k-1$, slightly less than its starting position $2^k+1$. For every $0<\varepsilon<1$, all but $O_\varepsilon(\log N)$ of the first $N$ digits lie in runs of the (infinite) binary expansion of $\kappa$ whose length is at least $\varepsilon$ times their starting position. No late run reaches length $(1+\varepsilon)$ times its starting position, consistent with $\mu(\kappa)=2$. Per-run bounds of the form $L\le(\mu-1)n$ are therefore attained simultaneously by essentially every run.

### 3.3 What distinguishes $\ln2$ from $\kappa$

The digit statistics of $x$ in base 2 are essentially its approximation behaviour with respect to the restricted denominators $2^n(2^m-1)$, $m$ bounded. Up to $O(m)$ digits at the ends, a run of a periodic word of period $m$ and length $L$ after position $n$ is the same as $|x-a/(2^n(2^m-1))|<2^{-n-L}$. The irrationality exponent takes a supremum over *all* denominators and is blind to this restriction. Kempner's number has superb unrestricted approximation behaviour and terrible restricted behaviour.

For $\ln2$ the only known approximants (Taylor, BBP, Legendre–Bezout, Rhin–Viola) have denominators built from $\operatorname{lcm}(1,\dots,n)$, whose odd parts carry the top-band primes with superpolynomial multiplicative orders of 2 (OP-11). The identity $e^{\ln2}=2$ and the integrality of $2^n$ are what make the binary Taylor series exist at all, but no currently known consequence of them reaches the restricted approximation profile beyond what the digits themselves are. Finite contrast: the first $2415$ certified partial quotients of $\ln2$ reach $3377$ (Kempner: $6$), while the first $8142$ binary digits of $\ln2$ have longest run $13$ and $\max L/n=0.318$ for $n\ge16$. Better unrestricted approximation is not better digit behaviour.

### 3.4 Logarithmic and Gregory constants

| constant | natural radix series | prefix denominators | status in this framework |
| --- | --- | --- | --- |
| $\ln2$ | $\sum2^{-k}/k$; $\frac23\sum9^{-k}/(2k+1)$ | top-band primes (OP-11) in base 2; same barrier in base 9 | open |
| $\ln3=2\sum_{k\ \rm odd}2^{-k}/k$ | base 2 residue piece $B_{1,2}$ | positive proportion of top-band primes (Phase 21 §3.4) | open |
| $\ln\frac32$, $\ln\frac43$ | $\sum3^{-k}/k$; $2B_{0,2}=\sum4^{-j}/j$ | Taylor type in base 3, base 4 | open |
| $\arctan\frac12=B_{1,4}-B_{3,4}$, $\arctan\frac13$ | base 4, base 9 alternating Taylor | positive proportion of top-band primes | open |
| $\pi/4=\arctan\frac12+\arctan\frac13=\sum(-1)^k/(2k+1)$ | Machin-type: radices 4 and 9; Gregory: no radix | Gregory prefixes: denominator of size $e^{(2+o(1))K}$, error about $1/(4K)$ | open |

Every rational combination $\sum_iq_ix_i$ of the base-2 periodic-coefficient series $\sum u(k)2^{-k}/k$ is again such a series, with $u$ rational and periodic modulo some $M$. Suppose $u\not\equiv0$. Let $g=\min\{\gcd(r,M):u(r)\ne0\}$ and fix $r_0$ with $\gcd(r_0,M)=g$ and $u(r_0)\ne0$. Consider a prime $p\in(N/(g+1),N/g]$ with $p\nmid M$, $p$ larger than the numerators and denominators of $u$, and $gp\equiv r_0\pmod M$; equivalently $p\equiv r_0/g\pmod{M/g}$, a reduced class. The multiples $mp\le N$ have $m\le g$. For $m<g$, $\gcd(mp,M)=\gcd(m,M)<g$, so $u(mp)=0$ by minimality of $g$. Hence $k=gp$ is the only multiple of $p$ in $[1,N]$ carrying a nonzero coefficient, and $p$ divides the reduced denominator of the prefix. By the prime number theorem in progressions this is a proportion $1/\varphi(M/g)$ of the primes in $(N/(g+1),N/g]$. For $g=1$ this is a positive proportion of the OP-11 top band. For $g>1$ it is the same structure at scale $N/g$ (example: $\ln2-\frac12\ln3=\frac12\ln\frac43$, $g=2$). The case of several primes in $M$ is included: for $M=6$ and $u=\mathbf 1_{\{2,3,4\}\bmod6}$ one has $g=2$, although the support is not contained in any single $g\mathbb Z$. That the OP-11 period bound then holds for every nonzero combination is a written deduction by the OP-11 argument, not a new theorem; in any case no relation modulo $K_2$ among these constants is available from their series. Gregory's series gives no digit window at all: the $K$-th prefix tracks about $\log_2(4K)$ digits against a denominator of about $2.9K$ bits. The verdict of Phase 21 stands: **$D^+(\ln2;2)\le0.9999$ is open, as is $\ln2\notin K_2$.**

### 3.5 Summary of E2

What is new here is a barrier and a reformulation. The barrier is Corollary 3.2: approximation-quality hypotheses of every strength are compatible with membership in $K_2$. The reformulation is that the relevant invariant is the restricted (radix-periodic) approximation profile. No new estimate for $\ln2$ is obtained.

## 4. E3 — five benchmark constants

### 4.1 Cahen's constant $C=\sum_{k\ge0}(-1)^k/(s_k-1)=0.64341054628833802618\ldots$

Here $s_0=2$, $s_{k+1}=s_k^2-s_k+1$ (Sylvester). Known: transcendental (Davison–Shallit, Monatsh. Math. 111 (1991)), $\mu(C)=3$ (Duverney–Shiokawa, Monatsh. Math. 191 (2020) 53–76), external inputs.

**Proposition 4.1.** (a) $s_k-1=\prod_{j<k}s_j$ and the $s_j$ are pairwise coprime. (b) The partial sum $C_K=\sum_{k\le K}(-1)^k/(s_k-1)$ has reduced denominator

```math
D_K=\prod_{0\le j<K,\ K-j\ \rm odd}s_j=s_{K-1}s_{K-3}s_{K-5}\cdots,
```

so $\log D_K=(\tfrac23+o(1))\log s_K$. (c) $|C-C_K|=(1+O(1/s_{K+1}))/(s_{K+1}-1)$, hence $|C-C_K|=D_K^{-3+o(1)}$.

*Proof.* (a) $s_{k+1}-1=s_k(s_k-1)$ and $s_0-1=1$; and $s_k\equiv1\pmod{s_j}$ for $j<k$. (b) Over the common denominator $Q_K=s_K-1=\prod_{j<K}s_j$ the numerator is $P_K=\sum_{k\le K}(-1)^k\prod_{k\le j<K}s_j$. Fix $i<K$. Terms with $k\le i$ contain the factor $s_i$. For $k>i$ every factor $s_j$ ($j\ge k>i$) is $\equiv1\pmod{s_i}$. Hence $P_K\equiv\sum_{k=i+1}^K(-1)^k\pmod{s_i}$, which is $0$ if $K-i$ is even and $\pm1$ if $K-i$ is odd. As the $s_j$ are pairwise coprime, $\gcd(P_K,Q_K)=\prod_{K-i\ \rm even}s_i$. (c) Alternating series with super-exponentially decreasing terms; and $\log s_{K-1-2i}\sim2^{-1-2i}\log s_K$ sums to $\frac23\log s_K$. ∎

Exact: $\log D_K/\log s_K=0.7017,0.6760,0.6690,0.6672,0.6668,0.6666$ for $K=3,5,7,9,11,12$. The normalized error $|C-C_K|D_K^3$ has no limit: it tends to $L\approx1.520221$ along odd $K$ and to $1/L\approx0.657799$ along even $K$. Indeed $D_KD_{K-1}=s_K-1$ gives, for $r_K=D_K^3/(s_{K+1}-1)$, the exact relation $r_Kr_{K-1}=1-1/s_K$ (checked for $3\le K\le12$). Since $\mu(C)=3$, the partial sums are essentially best possible approximations.

**Digits.** $C_K$ agrees with $C$ on about $2\log_bs_K\approx3\log_bD_K$ base-$b$ digits, while its period is $\operatorname{ord}_{D_K'}(b)$ ($D_K'$ the $b$-coprime part). The orders of $2$ modulo $s_j$ are $2,3,14,276,1087814,490854546,72928377053894166480$ for $j=1,\dots,7$. The factor $s_j$ first enters the reduced denominator $D_{j+1}$, and $C_{j+1}$ tracks about $2\log_2s_{j+1}\approx4\log_2s_j$ bits: $5.6,10.9,21.6,43.3,86.6,173.1,346.2$. So the tracked windows are vanishingly short pieces of their periods, the CC-50 window–denominator barrier applies with $\mu=3$, and no run or transition statement follows. **Radix misalignment:** in the base $B=s_K$, every $s_j$ with $j<K$ has $B\equiv1\pmod{s_j}$, order $1$. But in any *fixed* base only finitely many Sylvester factors are aligned. The terms $1/(s_k-1)$ are not radix powers, so sparse transfer (which needs integer coefficients on $b^{-n}$) does not apply, although the series is doubly-exponentially sparse. Finite: the first $16384$ bits have $49.976\%$ ones and $D_{10^4}=0.0127$. **Status: open; Diophantine-explicit, radix-blind.**

### 4.2 Reciprocal Fibonacci constant $\psi=\sum_{n\ge1}1/F_n=3.35988566624317755317\ldots$

*Known results.* $\psi$ is irrational (André-Jeannin, C. R. Acad. Sci. Paris 308 (1989)) and not in $\mathbb Q(\sqrt5)$ (Bundschuh–Väänänen). Transcendence results via Nesterenko's theorem (Duverney–Nishioka–Nishioka–Shiokawa 1997) concern $\sum1/F_n^{2s}$ and related even-index sums. We found no source establishing that $\psi$ itself is transcendental, so we record its transcendence as **not established here**.

**Proposition 4.2 (Landau; radix $\varphi^2$ form).** With $q=\varphi^{-2}=(3-\sqrt5)/2$ and $\theta_2(q)=\sum_{n\in\mathbb Z}q^{(n+1/2)^2}$,

```math
\sum_{n\ \rm odd}\frac1{F_n}=\frac{\sqrt5}4\,\theta_2(q)^2,\qquad \sum_{n\ \rm even}\frac1{F_n}=\sqrt5\sum_{m\ \rm odd}\frac{q^m}{1-q^m},\qquad
\frac{\psi}{\sqrt5}=\sum_{N\ge1}c(N)\varphi^{-N},
```

where $c(N)=r_2(N)/4=\sum_{d\mid N}\chi_4(d)$ for odd $N$ and $c(N)=\tau_{\rm odd}(N)$ for even $N$.

*Proof.* $1/F_n=\sqrt5\,\varphi^{-n}/(1-(-q)^n)=\sqrt5\sum_{k\ge0}(-1)^{nk}\varphi^{-n(2k+1)}$. Collect $N=n(2k+1)$: for odd $N$ the sign is $(-1)^k=\chi_4(2k+1)$; for even $N$ (so $n$ even) it is $+1$. Then $\theta_2(q)^2=\sum_{A,B\ \rm odd}q^{(A^2+B^2)/4}=\sum_{M\ \rm odd}r_2(M)\varphi^{-M}$, since $A^2+B^2=2M$ with $M$ odd forces $A,B$ odd and $r_2(2M)=r_2(M)$. ∎

So in its natural radix $\varphi^2$ (a Pisot unit, not an integer), $\psi/\sqrt5$ is the value of $E_{\rm odd}$-type Lambert coefficients $\tau_{\rm odd}$ on even indices plus the theta coefficients $r_2/4$ on odd indices. The second part has support density $0$, the analogue of $L_{\chi_4}(b)\in K_b$ (Phase 20); the first is dense and of Erdős–Borwein type, which is open even in integer radices. In an integer base $b$, $\log b/\log\varphi$ is irrational, so shifts $b^n\psi$ never align with powers of $q$. The Phase 20–21 coefficient transfer needs integer coefficients on $b^{-n}$ and has no purchase (radix–modulus misalignment).

The *sparse cousin* $y=\sum_{n\ge2}2^{-F_n}$ is in $K_2$ by the proof of Proposition 3.1(3): its support up to $N$ has $O(\log N)$ elements. Exact: $N(1-D_N)/(\log_2N)^2=0.740,0.736,0.786$ at $N=2^{10},2^{12},2^{14}$. Finite: $\psi$ has $49.62\%$ ones among its first $8192$ bits and $D_{4000}=0.0163$. **Status of $\psi$: open in every integer base.**

### 4.3 Catalan values and the exponential-mass wall

**Proposition 4.3.** For integers $b\ge5$,

```math
\sum_{n\ge0}C_nb^{-n}=\frac{b-\sqrt{b^2-4b}}2,\qquad \sum_{n\ge0}\binom{2n}nb^{-n}=\sqrt{\frac b{b-4}},
```

and at $b=4$ the first series converges to the rational number $2$. Examples: $C(1/5)=(5-\sqrt5)/2$, $C(1/6)=3-\sqrt3$, $C(1/8)=4-2\sqrt2$, $C(1/10)=5-\sqrt{15}$, and

```math
\sqrt2=\sum_{n\ge0}\binom{2n}n\,8^{-n},\qquad \sqrt5=\sum_{n\ge0}\binom{2n}n\,5^{-n}.
```

*Proof.* $C(x)=(1-\sqrt{1-4x})/(2x)$ and $\sum\binom{2n}nx^n=(1-4x)^{-1/2}$ for $|x|<1/4$, and by Abel's theorem at $x=1/4$. ∎

These are positive-integer-coefficient base-$b$ series whose values are quadratic irrationals. Their digit statistics are open (BBCP 2004 gives $\gg\sqrt N$ ones in binary, density zero). The obstruction is mass. The tail at shift $n$ is

```math
T_n=\sum_{j\ge1}C_{n+j}b^{-j}\asymp C_n\asymp4^nn^{-3/2},\qquad \log_bT_n=n\log_b4+O(\log n),
```

so the integer part of the tail absorbs a carry window of $n\log_b4=\Theta(n)$ digits (exact: $\log_8T_n/n=0.631,0.655,0.661$ at $n=100,400,1000$, tending to $2/3$). Integrality of the coefficients controls the digits only through the fractional part of tails of size $b^{\Theta(n)}$, which is no control. Every $K_b$ membership proved in Phases 20–21 used integer coefficients with sparse support or subexponential mass. Proposition 4.3 shows that the subexponential-mass hypothesis cannot be dropped: exponential mass with rate $4<b$ already produces algebraic irrationals, including $\sqrt2$. **Status: open (algebraic irrationals).**

### 4.4 Apéry's constant $\zeta(3)$

Known: irrational (Apéry 1978); $\mu(\zeta(3))\le5.513891$ (Rhin–Viola, Acta Arith. 97 (2001)), external. The accelerated series $\zeta(3)=\frac52\sum_{n\ge1}(-1)^{n-1}/(n^3\binom{2n}n)$ and the classical ladder $\zeta(3)=\frac87\bigl(\mathrm{Li}_3(\frac12)+\frac{\pi^2}{12}\ln2-\frac16\ln^32\bigr)$ agree to 50 digits in the script. The ladder is a binary BBP series plus products of $\pi^2$ and $\ln2$. BBP-type formulas for $\zeta(3)$ in a power-of-two radix exist via Broadhurst's polylogarithmic ladders (arXiv:math/9803067, external, not re-verified here).

**Proposition 4.4.** Let $A_n=\sum_{k\le n}(-1)^{k-1}/(k^3\binom{2k}k)$. For every prime $p\in(n/2,n]$ with $p\ge3$, $v_p(\operatorname{den}A_n)=3$.

*Proof.* By Kummer, $v_p\binom{2p}p=0$ for $p\ge3$ (no carry in $p+p$), so the term $k=p$ has $p$-adic valuation $-3$. For $k\le n<2p$, $k\ne p$, we have $p\nmid k$. If $k<p$, or if $p\ge5$ (write $k=p+r$ with $1\le r<p$: the base-$p$ digit sums of $k+k$ stay below $p$ in the top place), then $k+k$ has at most one carry in base $p$, so $v_p\binom{2k}k\le1$. The only remaining case is $p=3$, $k\in\{4,5\}$: $v_3\binom84=v_3(70)=0$ and $v_3\binom{10}5=v_3(252)=2$. So every term $k\ne p$ has valuation $\ge-2>-3$, and the unique minimum gives valuation $-3$ for the sum. ∎

Exact for every $3\le n\le400$. The partial sums have accuracy $4^{-n}$ (2 bits per term) against denominators of about $5.4$–$5.8$ bits per term at $n\le400$. The reduced denominator divides $\operatorname{lcm}(1..n)^2\operatorname{lcm}(1..2n)$ (checked for $n\le400$), whose size is $e^{(4+o(1))n}$, a cap of $4/\ln2\approx5.77$ bits per term; the cruder divisor $\operatorname{lcm}(1..n)^3\binom{2n}n$ gives $3/\ln2+2\approx6.33$. The tracking-to-denominator ratio is therefore about $0.35$. The CC-50 window–denominator barrier, which needs only $\mu<\infty$, applies verbatim with $\mu'=5.514$. Proposition 4.4 shows the prefixes keep *every* top-band prime $p\ge3$, to the third power. This is the property used in OP-11 (top band $(n/2,n]$ at term index $n\approx N/2$ for binary shift $N$), so the superpolynomial-period obstruction applies by the same argument; that is a written deduction, not a new theorem. **Status: open.**

### 4.5 The continued fraction constant $C_1=[0;1,2,3,\dots]=I_1(2)/I_0(2)=0.69777465796400798200\ldots$

Known: $[0;1,2,3,\dots]=I_1(2)/I_0(2)$, the Bessel-ratio continued fraction going back to Euler and Gauss, and the case $a=d=1$ of Lehmer's catalogue of arithmetic-progression continued fractions (Scripta Math. 29 (1973)); checked to 50 digits; transcendental by Siegel's theorem on $E$-functions (1929), external.

**Proposition 4.5.** With $p_n/q_n$ the convergents ($a_n=n$): $q_{n+1}=(n+1)q_n+q_{n-1}$, so $q_{n+1}/((n+1)q_n)\to1$, $\log q_n=n\log n-n+O(\log n)$, and

```math
\Bigl|C_1-\frac{p_n}{q_n}\Bigr|=\frac{1+o(1)}{q_nq_{n+1}}=q_n^{-2-(1+o(1))/n}.
```

Hence $\mu(C_1)=2$, and the partial quotients are unbounded.

*Proof.* Standard continued-fraction identities: $|x-p_n/q_n|=1/(q_n(q_{n+1}+q_n/x_{n+2}))$ with $x_{n+2}\ge n+2$. Then $\log(q_{n+1}/q_n)/\log q_n=\log(n+1)/(n\log n)\cdot(1+o(1))$. ∎

Exact: $q_{n+1}/((n+1)q_n)=1.008992,1.002375,1.000609,1.000273$ and $|C_1-p_n/q_n|q_nq_{n+1}=0.992595,0.997850,0.999420,0.999736$ at $n=10,20,40,60$. The Bessel series have factorial denominators, $I_\nu(2)=\sum_k1/(k!(k+\nu)!)$, so $C_1$ belongs to the same class as $e$ (whose continued fraction also has linearly growing partial quotients and $\mu=2$): factorial denominators with no radix structure, and an explicit continued fraction with $\mu=2$. By Corollary 3.2, $\mu=2$ cannot give $D^+<1$. Finite: $50.79\%$ ones in the first $16384$ bits, $D_{10^4}=0.0157$; decimal digit counts in the first $4000$ decimals are $395,406,384,404,396,433,383,405,405,389$. **Status: open.**

### 4.6 Status matrix

| constant | reachable by sparse transfer / $K_b$ tools? | proved barrier here | what would be needed |
| --- | --- | --- | --- |
| $E$ | no (dense $\tau$; complementary supports, GF-18) | CC-49 thresholds; $r_{\min}(D)\ge7$ for every $D$ (Cor. 2.3, finite certificate), $r_{\min}(D)\le92$ for $D\ge16$ (Prop. 2.4) | $\ge7$-point correlations of $(v_2,\text{odd part})$ of $\tau$; external $D^+<1$ awaiting independent verification |
| $E_+$ | no (dense signed coefficients) | signed knapsack; model bias $0.0222$ | the same correlations for $a_+$ (model threshold about two columns lower) |
| Cahen $C$ | no (non-radix denominators) | exponent-3 partial sums with periods $\gg$ windows | equidistribution of $b^n$ modulo products of Sylvester numbers on short windows |
| $\psi$ | no (radix $\varphi^2$ misaligned with $b$) | $E_{\rm odd}$-type in its own radix (Prop. 4.2) | an Erdős–Borwein theory in radix $\varphi^2$, then a transfer across multiplicatively independent radices |
| $C(1/b)$, $\sqrt{b/(b-4)}$ | no (exponential mass) | carry window $n\log_b4$ (Prop. 4.3) | the algebraic-irrational problem |
| $\zeta(3)$ | no (prime-lcm denominators) | top band to power 3 (Prop. 4.4); CC-50 with $\mu'=5.514$ | as for $\ln2$ |
| $C_1$, $e$ | no (factorial denominators) | $\mu=2$ insufficient (Cor. 3.2) | a digit-level arithmetic identity |
| $\sum b^{-F_n}$, $\kappa=\sum2^{-2^k}$ | **yes**: in $K_b$, rate $(\log N)^2/N$ | — | — |

## 5. Verification

`python -B scripts/phase22_classical.py` (standard library; about 5 s; 301,593 checks; exits 0) checks:

- **E1.** The identities of Proposition 1.1 to 50 digits for $b=2,3,10$. The three coefficient formulas, the zero set and the square-parity criterion for $n\le10^5$. The hyperbola identity and the partial sums at $X=10^3,10^4,10^5$. The second-moment ratio. The model constants: reproduction of CC-49's $\mu$, $\mathbb E(-1)^{c_1}$, $p_*$; $\mu^{\rm pos},\mu^{\rm neg}$; $p_+$. $2^{19}$ certified binary digits of $E$ and $E_+$, shell frequencies and $D_N$.
- **E1(a).** The parity Bonferroni values. The exact mixed factorial moments of the two embedded rational laws for every $i+j\le r$. The closed form of $h$. The outward-rounded integer enclosures of the five inputs, and the certified lower bounds for $f(1)$ by exact rational interval evaluation. The model objective and the downward-rounded robustness radius.
- **E2.** $2048$ certified partial quotients of $\kappa$ in $\{1,2,4,6\}$; $\lVert q_k\kappa\rVert\ge1/(8q_k)$ at the first 60 convergents; the $K_2$ bound at four values of $N$; the $\ln2$ continued fraction and runs from $8192$ certified bits.
- **E3.** Sylvester product and coprimality; the reduced denominators of $C_K$ for $K\le12$ against the formula; $D_KD_{K-1}=s_K-1$ and $r_Kr_{K-1}=1-1/s_K$; the error asymptotics and the two parity limits; factorizations and orders for $s_1,\dots,s_7$. Landau's two identities and the coefficient form of $\psi$ to 50 digits; the sparse cousin. Proposition 4.3 for $b=5,6,8,10$ and $\sqrt2=\sum\binom{2n}n8^{-n}$; the tail growth. Apéry's series against the $\mathrm{Li}_3$ ladder; Proposition 4.4 for every $3\le n\le400$ and the divisibility by $\operatorname{lcm}(1..n)^2\operatorname{lcm}(1..2n)$. The Bessel-ratio identity to 50 digits and the convergent asymptotics of Proposition 4.5. Finite digit statistics of $C$, $\psi$, $C_1$.

`--thresholds` additionally recomputes five entries of the knapsack table of §1.6 (model, about six minutes): it checks $E$ at $D=15,16$ against the certified CC-49 intervals and the $E_+$ threshold at $14$.

All model numbers are floating point and are labelled as such; all digit data are finite.

## 6. Open questions

1. Close $9\le r_{\min}(16)\le92$ and $7\le r_{\min}(D)\le92$ ($D\ge17$) by a genuinely multivariate moment LP. Theorem 2.1 shows the answer depends only on the information class.
2. Certify (interval arithmetic) the $E_+$ column table and the comparison constants of the signed model. Solve the three-column programme of §2.2: does $r_{\min}(D)\ge8$ hold for all $D$?
3. Is $E_+$ disjunctive in base 2? Is $f(1;E_+)<1/2$? Does a positive-word-density argument of the kind in the external pinned result transfer to signed coefficients?
4. An approximation property of $\ln2$ by the restricted denominators $2^n(2^m-1)$, $m$ bounded, that is not a restatement of its digits.
5. Transcendence of $\psi$ (not established in the sources we examined).
