# Euler's square, modular positivity, theta cubes and higher Euler powers

**Phase 26, Track D (D1–D4).** This note does not improve the unconditional lower frequency $1/(3\pi)$ for the constant binary words of Euler's square $E_2^2$ (`BC-29`). It proves that $1/(3\pi)$ is the exact limit of the inputs from which it was derived. Any further unconditional gain must come from the dimension-$3/4$ upper-sieve constant or from the level of distribution. Two conditional gains are recorded: Iwaniec's $\beta$-sieve would give about $0.1148$ and level one about $0.1784$. We also prove the following.

- Gram, Hankel and Toeplitz data of the coefficient signs cannot detect gap weights. Positivity combined with upper correlation bounds cannot beat the first-order bound.
- Legendre's zero set, the $4$-adic self-similarity of $r_3$, any fixed number of low coefficient bits and all leading-order size information leave the binary distribution of $\Theta_3(2^{-k})^3$ and $\Theta_3(2^{-k})^4$ completely undetermined.
- For large stretch the prime subseries of the CM newforms $\eta(6\tau)^4,\eta(4\tau)^6,\eta(3\tau)^8$ lie outside $K_2$, with explicit bounds $D^+<1$. Consequently, at most one of each full Euler power $E(2^{-k})^r$, $r=4,6,8$, and its composite-index complement can lie in $K_2$.

All new statements carry the labels below. Cross-model review is not independent human peer review.

| # | Statement | Label | Objective |
| --- | --- | --- | --- |
| D1.1 | Sign-conditioned gap law: for each sign, the proportion of supported endpoints with normalized gap $\rho g\le t$ has upper limit at most $(3\pi/4)t$ | Paper proof | 3 |
| D1.2 | First-order sign cancellation of small gaps: $\lvert\sum s\min(g,t/\rho)\rvert\le(3\pi/16)t^2N+o(N)$ | Paper proof | 3 |
| D1.3 | First-order method class $\mathfrak B(K)$: truncation is optimal, the output is exactly $1/(4K)$, and $K$ is given by an explicit transfer formula in the sieve constant and the level | Paper proof | 4 |
| D1.4 | Sharpness: a signed model satisfies every input of GF-43, Theorem 1, and has $W_+/N\to1/(4K)$. Hence $1/(3\pi)$ is the limit of those inputs | Paper proof | 4 |
| D1.5 | $\beta$-sieve constant gives $\approx0.1148$; level $\theta$ gives $(2\theta)^{3/4}/(3\pi)$ | Conditional | 3 |
| D1.6 | Unweighted sign balance (even in every residue class) does not imply weighted gap balance | Paper proof | 4 |
| D2.1 | Every multilinear (distinct-shift) correlation whose leftmost factor is a sign is blind to gap weights. Only predecessor-type correlations, including repeated-shift moments of the signed sequence, can see them | Paper proof | 4 |
| D2.2 | Gap-indexed Gram matrices collapse to unsigned data. Every $2\times2$ Gram bound for $\sum s\,g$ is at least the trivial bound $\sum g$ | Paper proof | 4 |
| D2.3 | Moment–positivity ceiling: valid inequalities for probability laws plus upper correlation bounds give at most the first-order bound, at every horizon | Paper proof | 4 |
| D3.1 | Exact identities: $r_3(n)=12(H(4n)-2H(n))$, the $4$-adic tower, $8q^3\psi(q^8)^3$, the Jacobi $2$-scaling | External input + Finite certificate | 3 |
| D3.2 | Inertness: the Legendre, $2$-adic, scaling and size data of $r_3$, $r_4$ are compatible with every value in an interval | Paper proof | 4 |
| D3.3 | $v_2(r_4(n))/\log\log n\to2$ in density | Paper proof | 3 |
| D3.4 | Carry volume of $\Theta_3(2^{-k})^4$ is $\asymp M\log M$ at every fixed $k$ | Paper proof | 4 |
| D4.0 | $K_2=M_2$ in base $2$; quantitatively $D^+\le1-\min(1/4,\tau/2)$ for lower transition density $\tau$ | Paper proof | 2 |
| D4.1 | Prime subseries of $\eta(6\tau)^4,\eta(4\tau)^6,\eta(3\tau)^8$ at stretch $k\ge47,93,139$ have positive lower transition density, hence $D^+<1$ explicitly | Paper proof | 2, 3 |
| D4.2 | Dichotomy: for Euler stretch $k\ge277,370,416$, at most one of $E(2^{-k})^r$ and its composite-index complement lies in $K_2$ | Paper proof | 2, 4 |
| D4.3 | The composite complement has support density zero and diverging mean weight. Neither fact decides membership in $K_2$ | Paper proof | 4 |

Notation follows [GF-43](../phase25/euler-square-and-theta-powers.md). The orbit is $y_n=\{2^nx\}$, and $D_N$, $D^\pm$, $K_2$ and $M_2$ are as in the [research objectives](../../docs/research-objectives.md) and GF-43. Logs without subscript are natural, $\delta=3/4$, and $\gamma_E$ is Euler's constant.

## 1. D1: Euler's square

Let $a(n)=[q^n]E(q)^2$, $s(n)=\mathrm{sgn}\,a(n)$, and let $0=m_0<m_1<\cdots$ list the support $U$, with gap $g(m_i)=m_i-m_{i-1}$ attached to the right endpoint. Put $S=\#\{0<m_i\le N\}\sim\rho N$ with $\rho=C_\eta(\log N)^{-3/4}$, $S_\sigma$ the number with sign $\sigma$, and $W_\sigma=\sum_{s(m_i)=\sigma}g(m_i)$. GF-29 and GF-43 give $f_{0^L}=W_+/N+o(1)$ and $f_{1^L}=W_-/N+o(1)$, and $S_\pm\sim S/2$. GF-43, Theorem 1, proves $\liminf W_\sigma/N\ge1/(3\pi)$ with the predecessor constant

$$
K=\frac{\Gamma(7/4)\Gamma(1/4)\,4^{3/4}}{4}=\frac{3\pi}{4}.
$$

**Checking the constant.** We rederived $K$ from first principles. Wirsing's theorem gives the count of integers composed of primes $\equiv1\bmod12$ up to $Y$ as $(e^{3\gamma_E/4}/(3\Gamma(1/4)))\,Y\,V(Y)$, where $V(Y)=\prod_{\ell\in\mathcal P,\ell\le Y}(1-1/\ell)$. Here $\mathcal P$ is the set of primes $\equiv5,7,11\bmod12$. Summing over square parts gives $\rho\sim\mathcal W V(N)$ with $\mathcal W=4e^{\gamma_E\delta}\prod_{\ell\in\mathcal P}(1-\ell^{-2})^{-1}/\Gamma(1/4)$. The factor $4$ is $12\cdot\frac12\cdot\frac23$: the shifted predecessor $l-12h$ is automatically $\equiv1\bmod12$. The Selberg main term for a predecessor is $e^{\gamma_E\delta}\Gamma(1+\delta)V(\xi)$ up to local factors. Those local factors match the true local densities exactly at every prime, by the identity $(1-\frac1{\ell-1})(1+\frac1{\ell(\ell-2)})=1-\frac1\ell$ and the limit $J_0\to\infty$ of GF-43. With $\xi=X^{1/4}$ the ratio is $\Gamma(7/4)\Gamma(1/4)4^{3/4}/4$. Reflection gives $\Gamma(1/4)\Gamma(3/4)=\pi\sqrt2$ and $4^{3/4}=2\sqrt2$, so the ratio is $3\pi/4$. Thus the loss over the truth (mean pair density $1$) factors exactly as

$$
\frac{3\pi}{4}=\underbrace{\frac{3\pi\sqrt2}{16}\,2^{3/4}}_{\text{Selberg constant at full level, }\approx1.401}\times\underbrace{2^{3/4}}_{\text{level }X^{1/2}\text{ instead of }X,\ \approx1.682}.
$$

There is no loss at any individual prime. "Exact small-prime refinement" therefore has nothing left to gain.

### Theorem D1.1. The sign-conditioned gap law near zero

**Paper proof, objective 3.** For each sign $\sigma$ and each fixed $t>0$,

$$
\limsup_{N\to\infty}\frac1{S_\sigma}\#\{0<m_i\le N:\ s(m_i)=\sigma,\ \rho\,g(m_i)\le t\}\le\frac{3\pi}{4}\,t .
$$

*Proof.* Use GF-43's selected endpoints. Their total enlarged mass satisfies $\sum_{v\le V}M_v\le(\frac12+o(1))N\rho$ per sign, and the unselected proportion is at most $\eta$, which is arbitrary. An endpoint with $g\le H$ has an immediate predecessor at some distance $h\le H$. If that predecessor has square part at most $V\le T$, it passes the predecessor sieve. Otherwise it is charged once, at total cost $O(S/V)+o(S)$, exactly as in GF-43. Summing the Selberg bound $M_vb_v(h)R_T(h)/G_T(\xi)$ over $1\le h\le H$ with uniform weights rather than triangular ones gives the same limiting mean $b_*\prod_{\ell>T}(1+1/[\ell(\ell-2)])$. Expand $R_T$ over squarefree $d$ with weights $\prod_{\ell\mid d}(\ell-2)^{-1}$. Each $d$ coprime to $M_0$ has uniform mean $b_*/d$ on $[1,H]$ as $H\to\infty$, and $\sum_d r(d)/d<\infty$. The normalization of GF-43 then gives at most $(\frac12+o(1))N\rho\cdot K\rho H$ endpoints. With $H=\lfloor t/\rho\rfloor$ this is $(Kt+o(1))S_\sigma$. The limits are taken as in GF-43. All parameters are fixed before $N\to\infty$, and no estimate needs uniformity in them. After $N\to\infty$, let the small-prime precision $J_0\to\infty$, the sieving exponent $\beta\uparrow1/4$ in $\xi=N^\beta$, the unselected proportion $\eta\to0$ (through the band parameters $b,e$), and $V,T\to\infty$ with $T\ge V$. $\square$

Since $\min(g,H)=\int_0^H\mathbf 1[g>u]\,du$, Theorem D1.1 together with monotonicity in $t$ gives

$$
\frac{W_\sigma}{N}\ \ge\ \frac{S_\sigma}{\rho N}\int_0^{t}\bigl(1-F_{\sigma,N}(\tau)\bigr)\,d\tau,
\qquad\text{hence}\qquad
\liminf_N\frac{W_\sigma}{N}\ \ge\ \frac12\int_0^{1/K}(1-K\tau)\,d\tau=\frac1{4K}=\frac1{3\pi},
$$

where $F_{\sigma,N}(\tau)$ is the proportion of sign-$\sigma$ endpoints with $\rho g\le\tau$, the quantity bounded in D1.1. This reproves GF-43, Theorem 1, in distributional form. Uniformity on $t\in[0,1/K]$ follows from the monotonicity of $F_{\sigma,N}$ and the continuity of $Kt$, by the usual Pólya argument.

### Corollary D1.2. First-order sign cancellation of small gaps

**Paper proof, objective 3.** For every fixed $t>0$,

$$
\Bigl|\sum_{0<m_i\le N}s(m_i)\min\bigl(g(m_i),t/\rho\bigr)\Bigr|\ \le\ \Bigl(\frac{3\pi}{16}t^2+o(1)\Bigr)N,\qquad
\sum_{0<m_i\le N}\min\bigl(g(m_i),t/\rho\bigr)\ \ge\ \Bigl(t-\frac{3\pi}{8}t^2-o(1)\Bigr)N .
$$

*Proof.* For each sign the count $\#\{\sigma:g>u\}$ lies between $S_\sigma(1-K\rho u)-o(S)$ and $S_\sigma$, uniformly for $u\le t/\rho$, by D1.1. Since $S_+-S_-=o(S)$, the two counts differ by at most $\frac S2K\rho u+o(S)$. Integrate over $u\le H=t/\rho$. $\square$

The signed truncated mass is of second order in $t$ while the unsigned one is of first order. This is genuine cancellation, but only at scales $t\to0$. Binary simple normality needs $\sum s\,g=o(N)$, the regime $t\to\infty$, and D1.2 says nothing there. The exact identity $\sum s\min(g,H)=H(S_+-S_-)-\sum s\,(H-g)_+$ is checked by the verifier.

### Theorem D1.3. The first-order class and its exact output

Call a lower-bound argument for $W_\sigma$ of **class $\mathfrak B(K)$** if it (i) chooses a test $\varphi$ with $\varphi(g)\le g$ and $\varphi\le\Phi:=\sup\varphi$, (ii) uses the pointwise inequality $\varphi(g(m))\ge\Phi-\sum_{h:\,m-h\in U}(\Phi-\varphi(h))$, valid because the nearest predecessor is among those counted, and (iii) replaces the predecessor counts by upper bounds $K\rho\,\varsigma(h)S_\sigma(1+o(1))$ with $\varsigma\ge0$ of mean one on long intervals. This is the form supplied by any upper-bound sieve.

**Paper proof, objective 4.** (a) For each $\Phi$ the truncation $\varphi=\min(\cdot,\Phi)$ maximizes the output. The best output of class $\mathfrak B(K)$ is

$$
\sup_{t>0}\Bigl(\frac t2-\frac{K t^2}{4}\Bigr)=\frac1{4K},\qquad\text{attained at }t=1/K .
$$

(b) Suppose the predecessor bound comes from an upper-bound sieve of dimension $\delta=3/4$ with weights bounded by one and upper function $F(s)=A s^{-\delta}$ for $0<s\le s_0$, for some $s_0\ge1$, whose remainders are controlled at level $X^\theta$ by GF-43's estimate (1). Selberg's sieve has $s_0=2$, and the $\beta$-sieve has $s_0=\beta_\delta+1$. Then

$$
K(A,\theta)=\frac{A\,\Gamma(1/4)}{4e^{\gamma_E\delta}}\,\theta^{-\delta},\qquad
\frac1{4K(A,\theta)}=\frac{e^{3\gamma_E/4}\theta^{3/4}}{A\,\Gamma(1/4)}=\frac{A_{\rm Sel}}{A}\cdot\frac{(2\theta)^{3/4}}{3\pi},
$$

where $A_{\rm Sel}=2^{3/4}e^{3\gamma_E/4}\Gamma(7/4)\approx2.3830$ is Selberg's constant. With $A=A_{\rm Sel}$ and $\theta=1/2$ this is GF-43's $1/(3\pi)$.

*Proof.* (a) The cost is $\sum_hK\rho\varsigma(h)(\Phi-\varphi(h))$. It decreases in each $\varphi(h)$, and $\varphi(h)\le\min(h,\Phi)$. With $\Phi=t/\rho$ and $\varsigma$ of mean one, the output per unit $N$ tends to $\frac\rho2[\Phi-K\rho\Phi^2/2]=t/2-Kt^2/4$. Moreover $1/(4K)-(t/2-Kt^2/4)=K(t-1/K)^2/4$. (b) Take $s=1$, that is $z=D\le X$. Any $s\in[\theta,s_0]$ would do, since $z=D^{1/s}\le X$ exactly when $s\ge\theta$. Then $V(z)F(s)\sim A\,V(D)$ because $V(D^{1/s})\sim s^\delta V(D)$, and $D=X^{\theta-o(1)}$. Divide by $\rho\sim\mathcal W V(N)$ and use $V(D)/V(N)\to\theta^{-\delta}$. The local factors cancel exactly as in GF-43. For the closed form use $\Gamma(1+\delta)\Gamma(1-\delta)=\frac{3}{4}\pi\sqrt2$ and $2^{-3/4}2^{-1/2}\frac43=2^{3/4}\cdot2^{-2}\cdot\frac43$. $\square$

### Theorem D1.4. Sharpness: $1/(4K)$ is the limit of the inputs

**Paper proof, objective 4.** Let $K>9/4$; this covers $K=3\pi/4\approx2.356$. Let $\rho(N)\to0$ be slowly varying with $N\rho(N)^3\to\infty$. The decay may be arbitrarily slow, and $\rho=C_\eta(\log N)^{-3/4}$ is allowed. There is a signed set $(U^*,s^*)$ of positive integers of density $\rho_N=\rho(N)$ with the following properties.

- **(a)** $S\sim\rho N$ and $S_\pm\sim S/2$.
- **(b)** For every fixed modulus $q$, both sign classes are asymptotically equidistributed over the residue classes modulo $q$.
- **(c)** For each sign, every $t>0$ and $H=\lfloor t/\rho\rfloor$, the triangular and uniform predecessor means are at most $K\rho(1+o(1))$:
  $$\frac2{H^2}\sum_{h<H}(H-h)P^\sigma_h\le K\rho\,S_\sigma(1+o(1)),\qquad \frac1H\sum_{h\le H}P^\sigma_h\le K\rho\,S_\sigma(1+o(1)),$$
  where $P^\sigma_h$ is the number of sign-$\sigma$ endpoints $m$ with $m-h\in U^*$.
- **(d)** $\sum g^\gamma\asymp N\rho^{1-\gamma}$ for each fixed $\gamma>1$.
- **(e)** $W_+/N\to1/(4K)$ and $W_-/N\to1-1/(4K)$.

Properties (a), (c) and (d) are the inputs of GF-43, Theorem 1, and of D1.1: support and sign asymptotics, the averaged predecessor sieve, and the Matomäki–Radziwiłł gap moment that makes the GF-29 carry identity valid. No argument that derives $\liminf_N\min_\sigma W_\sigma/N$ from (a)–(d), with or without (b), can exceed $1/(4K)$. With $K=3\pi/4$ this limit is GF-43's $1/(3\pi)$.

*Construction.* On each dyadic block of positions use constant parameters $\rho$ and $H_*=\lfloor1/(K\rho)\rfloor$, with $\rho$ the value of $\rho(\cdot)$ at the start of the block. Alternate signs. A $+$ endpoint has gap uniform on $\{1,\dots,H_*\}$, independent of the past. A $-$ endpoint has gap $L=\lfloor(2-\frac1{2K})/\rho\rfloor$. This forces $K\rho=1/H_*$ and mean gap $1/\rho$ up to rounding. The construction is random. We show that (a)–(e) hold almost surely, so some deterministic realization $(U^*,s^*)$ has them all.

(a): signs alternate. On each block the strong law for the independent gaps gives mean gap $(\mathbb Eg_++L)/2=(1+o(1))/\rho$.

(e): on each block the $+$ gaps occupy the proportion $\mathbb E g_+/(\mathbb E g_++L)=(1+1/H_*)/(4K)\to1/(4K)$ of the length. The limit does not depend on $\rho$, so $W_+/N\to1/(4K)$ and $W_-/N\to1-1/(4K)$.

(c) for $+$ endpoints. Let $D_1=g$, $D_2=g+L$, $D_3=g+L+g'$, and so on, be the distances to earlier points, so $D_{2i},D_{2i+1}\ge iL$.

- *Triangular sums.* For $H\le H_*+1$ the sum is exactly $H(H-1)/(2H_*)$. For $H_*<H\le L$ only $D_1$ counts, and $\mathbb E(H-g)=H-(H_*+1)/2\le H^2/(2H_*)$ since $(H-H_*)^2+H_*\ge0$. For $H>L$ the sum is at most $H+2\sum_{i\ge1}(H-iL)_+\le H+H^2/L$. With $m=\lfloor H/L\rfloor$ this follows from $H^2/L-\bigl(2mH-m(m+1)L\bigr)=(H-mL)^2/L+mL\ge0$. The bound is $\le K\rho H^2/2$ once $1/H+1/L\le K\rho/2$, and for $H>L$ it suffices that $L\ge4/(K\rho)$. Since $\rho L\to2-\frac1{2K}$, this holds on all large blocks when $K>9/4$.
- *Uniform counts.* For $H\le H_*$ the expected count is $\Pr(g\le H)=H/H_*=K\rho H$. For $H_*<H<L$ it is $1<H/H_*=K\rho H$. For $H\ge L$ it is at most $1+2\lfloor H/L\rfloor\le3H/L\le K\rho H$, which needs $\rho L\ge3/K$, true on large blocks when $K>7/4$. The count bound $1+2\lfloor H/L\rfloor$ is used only for $H\ge L$; for $H\le H_*$ it would fail, since then $K\rho H\le1$.

(c) for $-$ endpoints. The distances are $D^-_{2i-1}=iL+g_1+\dots+g_{i-1}$ and $D^-_{2i}=iL+g_1+\dots+g_i$, so $D^-_{2i-1},D^-_{2i}\ge iL$ and no predecessor is closer than $L$. For $H<L$ both sums vanish. For $H\ge L$ the triangular sum is at most $2\sum_{i\ge1}(H-iL)_+\le H^2/L\le K\rho H^2/2$, and the count is at most $2\lfloor H/L\rfloor\le2H/L\le K\rho H$. Both need only $\rho L\ge2/K$, true when $K>5/4$.

(c) globally. An endpoint $m\le2H$ contributes at most $H^2$ to a triangular sum, so these endpoints contribute $O(H^3)=O(\rho(N)^{-3})=o(N)$ in total. This is negligible against the bound $K\rho S_\sigma H^2/2\asymp t^2N$ because $N\rho(N)^3\to\infty$; the uniform means are handled the same way. For $2H<m\le N$ the window $[m-H,m]$ lies in $[m/2,m]$, where the block parameters differ from those at $m$ by a factor $1+o(1)$ because $\rho$ is slowly varying. So each such endpoint contributes at most $(1+o(1))K\rho(m)H^2/2$ in expectation, and the strong law turns these expectations into almost sure bounds. Endpoints near $m$ have density $\rho(m)$, so Karamata's theorem $\sum_{m\le N}\rho(m)^2\sim N\rho(N)^2$ gives (c) for the whole set, with $\rho=\rho(N)$ and $S_\sigma\sim\rho(N)N/2$. Property (c) is an averaged bound, which is all GF-43, Theorem 1, uses. The model has a pointwise spike $P^-_L=S_-$, so it does not satisfy a uniform bound $P^-_h\le K\rho S_-$ at $h=L$.

(b): given the past up to $m_{2i-2}$, the gap $g_+$ is uniform on $\{1,\dots,H_*\}$. So $m_{2i-1}$, and hence $m_{2i}=m_{2i-1}+L$, lies in each class modulo $q$ with conditional probability $1/q+O(1/H_*)$. The centred class indicators are bounded martingale differences. The martingale strong law therefore gives equidistribution of both sign classes almost surely, and the $O(1/H_*)$ errors sum to $o(S)$. This argument needs no stationarity, so the time-inhomogeneous, block-varying parameters are allowed.

(d): every gap is $O(1/\rho)$, and the $S/2$ gaps of length $L\asymp1/\rho$ give the matching lower bound. So $\sum g^\gamma\asymp N\rho^{1-\gamma}$ on each block. Summing the dyadic blocks preserves this because $\rho^{1-\gamma}$ is slowly varying. $\square$

The verifier checks the triangular and uniform predecessor inequalities exactly for $H_*=60$, $L=252$ (model constant $K=113/48\approx2.3542$), for both signs and both full predecessor chains. It covers every $H<180$, the grid $H=180,187,\dots,2014$, and $H=2016=8L$. Equality holds for $H\le H_*+1$, and $-$ endpoints have no predecessor below $L$, as claimed.

### D1.5. Conditional improvements of the constant

**Conditional (named hypotheses), objective 3.** By D1.3(b) and D1.4, an improvement can only come from $A$ or $\theta$.

1. **Level.** Suppose the sign-selected endpoint measures $B_v$ of GF-43 satisfy the fixed-residue estimate (1) with $3^{\omega(q)}$-weights at level $Q=X^{\theta-\kappa}$ for some $\theta\in(1/2,1]$. This is an Elliott–Halberstam-type hypothesis for the Frobenius class in the $D_4$ ring class field of discriminant $-144$. Then the lower frequency is at least $(2\theta)^{3/4}/(3\pi)$. At $\theta=1$ the bound is $2^{3/4}/(3\pi)\in(0.1784,0.1785)$, certified.
2. **$\beta$-sieve constant.** Grant (H1) that Iwaniec's Rosser $\beta$-sieve (Iwaniec, *Acta Arith.* 36 (1980) 171–202; Friedlander–Iwaniec, *Opera de Cribro*, Ch. 11) applies in dimension $3/4$ with $F(s)=A_{3/4}s^{-3/4}$ for $0<s\le\beta_{3/4}+1$. Grant also (H2) that $A_{3/4}\le2.21$. Its weights are bounded by one and its remainder is $\sum_{d<D}|r_d|$, so GF-43's estimate (1) at level $X^{1/2}$ applies. D1.3(b) then gives a lower frequency of at least $A_{\rm Sel}/(3\pi\cdot2.21)>0.1144$.
   - [Exploration, floats, not a certificate.] We solved the $\beta$-sieve delay-differential system on a grid aligned with the unit delay, so that every delayed value and every kink is a grid point. The scheme uses the trapezoid rule, bisection for $\beta$ and one Richardson step in the grid size. It gives $\beta_{3/4}\approx1.3981$, $A_{3/4}\approx2.2020$, ratio $A_{3/4}/A_{\rm Sel}\approx0.9240$, and an implied bound $\approx0.1148$. The same solver reproduces $\beta_1=2$ and $A_1=2e^{\gamma_E}$ to within $10^{-11}$ in dimension one. An earlier first-order midpoint discretization gave $1.399$, $2.205$ and $0.1146$; that third-decimal difference was discretization error. The independent Simpson solve in the cross-model Track D review agrees with the new values to the digits shown. For comparison, in dimension $1/2$ the semi-linear sieve beats Selberg by the factor $2\sqrt2/\pi\approx0.900$.
3. **Both.** Under both hypotheses the bound would be about $2^{3/4}\cdot0.1148\approx0.1931$.

Even with a perfect sieve, D1.3 caps class $\mathfrak B$ at $1/(4\kappa_2)$. Here $\kappa_2$ is the true normalized mean predecessor density, conjecturally $1$. The expected ceiling is therefore $1/4<1/2$. Simple normality lies outside every first-order method.

### Proposition D1.6. Unweighted sign balance does not give weighted balance

**Paper proof, objective 4.** Take gaps independent and uniform on $\{1,3\}$, and set $s_i=+1$ exactly when $g_i=3$. Almost surely $S_+\sim S_-$, and for every $q$ the two signs are equidistributed in every residue class modulo $q$. The position chain modulo $q$ has steps $1,3$. Its uniform law is stationary, and $\Pr(m_i\equiv a,s_i=+)=\frac12\Pr(m_{i-1}\equiv a-3)=\frac1{2q}=\Pr(m_i\equiv a,s_i=-)$. Yet $N^{-1}\sum s\,g\to\frac{3/2-1/2}{2}=\frac12$. The verifier checks the stationary law exactly for $q\le12$. **Warning, retained from GF-37 and GF-43.** No statement of the form "$S_\pm\sim S/2$" or "Corollary 1.1 of GF-43", that is, signed tests of small modulus, implies $\sum s\,g=o(N)$.

### 1.7. What remains open for D1

**Open.** Several questions remain.

- An asymptotic, or even a lower bound of the right order, for the predecessor counts $P^\sigma_h$. A lower bound needs a dimension-$3/4$ lower-bound sieve sifting to $X$ at level $X^{1/2}$, that is $s\le1/2$. This lies below the $\beta$-sieve sifting limit $\beta_{3/4}\approx1.4$ (numerical value). It also faces the parity barrier.
- Cancellation $\sum_m s(m)\mathbf 1_U(m-h)=o(S\rho)$ of signed predecessor counts for fixed $h$.
- Signed gap moments at scales $t\gtrsim1$.
- A limiting law of $\rho g$ conditioned on the sign.

By D1.4 and D2.3 each requires information outside (a)–(d), for example lower bounds on mixed correlations or Galois structure of the signs at shifted arguments. The `BC-29` benchmark status is unchanged.

## 2. D2: Positivity and determinant methods

Write $u(m)=\mathbf 1_U(m)$ and $a(m)=s(m)u(m)$. For finite sets $T_a,T_u$ of shifts, the **mixed correlation** is

$$
C(T_a,T_u)=\lim_N\frac1N\sum_{m\le N}\prod_{h\in T_a}a(m+h)\prod_{h\in T_u}u(m+h)
$$

whenever the limit exists. We always take $T_a\cap T_u=\varnothing$. The relations $a^2=u$, $au=a$ and $u^2=u$ reduce every monomial $\prod_t a(m+i_t)$, repeated shifts allowed, to one such $C(T_a,T_u)$. Here $T_a$ is the set of shifts of odd multiplicity and $T_u$ the set of shifts of positive even multiplicity. A correlation is **signed-leftmost** if $\min(T_a\cup T_u)\in T_a$. Gram, Hankel and Toeplitz matrices of $a$ have off-diagonal entries $C(\{i,j\},\varnothing)$ for $i\ne j$. Their diagonal entries are $\mathbb E[a(m+i)^2]=C(\varnothing,\{i\})$, a pure support correlation. Shifted convolution sums $\sum c(n)c(n+h)$ of the CM newform, their spectral expansions, and Hecke-character sign distributions in progressions (GF-43, Corollary 1.1) all have **signed leftmost factor**: the leftmost shift carries a sign, or every factor is signed. The gap functional has a different shape:

$$
\Phi=\frac1N\sum_{0<m_i\le N}s(m_i)g(m_i)=\frac1N\sum_{m}a(m)\sum_{j\ge0}\prod_{h=1}^{j}\bigl(1-u(m-h)\bigr).
$$

Expanding the products, $\Phi$ is a combination of **predecessor-type** correlations $C(\{0\},\{-h_1,\dots,-h_r\})$. In these the unique signed factor is the rightmost one.

### Theorem D2.1. Signed-leftmost data are blind to gap weights

**Paper proof, objective 4.** Consider two stationary signed point processes with independent gaps uniform on $\{1,3\}$. In model A, $s_i=+1$ exactly when $g_i=3$. In model B the signs are independent fair coins. Then:

- every signed-leftmost correlation vanishes in both models. In particular, every distinct-shift (multilinear) autocorrelation $\mathbb E\prod_{h\in T}a(m+h)$ with $T$ a nonempty finite set vanishes in both. The $2$-point Gram, Hankel and Toeplitz matrices of $a$ also agree, since their diagonal entries $C(\varnothing,\{i\})=1/2$ are pure support;
- all pure support correlations agree;
- all successor-type correlations agree;
- $\Phi_A=1/2$ while $\Phi_B=0$.

Hence any inequality $|\Phi|\le\mathcal F(\text{data})$, where the data are signed-leftmost and support correlations of any order in reduced form, must have $\mathcal F(\text{data}_B)\ge1/2$. Positive-semidefinite Gram, Hankel or Toeplitz constraints built from these data therefore cannot force $\Phi\to0$. The same holds for any bound on them, such as power savings for shifted convolution sums.

**Repeated shifts are not covered.** Squaring the leftmost factor strips its sign. So a monomial in $a$ whose leftmost shift has even multiplicity reduces to a correlation that is not signed-leftmost. It is either a pure support correlation, or it has a support factor to the left of a signed factor, as the predecessor-type correlations do. The claim already fails at order three:

$$
\mathbb E\bigl[a(m)^2a(m+1)\bigr]=\mathbb E\bigl[u(m)\,a(m+1)\bigr]=C(\{1\},\{0\})=
\begin{cases}-1/4&\text{in model A},\\ 0&\text{in model B}.\end{cases}
$$

In model A the point density is $1/2$, the next gap is $1$ with probability $1/2$, and that gap carries the sign $-1$. So D2.1 does not apply to higher moment tensors of $a$, or to Lasserre moment matrices of degree at least $2$ in $a$, through their repeated-shift entries. Those entries include predecessor-type correlations such as $C(\{1\},\{0\})$. By D2.3, upper bounds on them give nothing beyond class $\mathfrak B$; using them requires lower bounds, the open problem of §1.7.

*Proof.* Order the points $i_1<\dots<i_r$ of a pattern, with distinct positions. The sign $s_{i_1}$ is a function of $g_{i_1}$ alone. Every relative position $m_{i_j}-m_{i_1}$ and every other sign depends only on gaps with index $>i_1$. So $s_{i_1}$ is independent of the rest, and $\mathbb E s_{i_1}=0$. In model B every signed factor is an independent fair coin. The predecessor correlation $C(\{0\},\{-1\})=\mathbb E[s_j\mathbf 1(g_j=1)]\cdot(\text{density})\ne0$ in model A. The verifier enumerates all gap tuples of length up to $7$. It confirms the vanishing of the forward, pure-signed and three-point signed correlations and finds $24$ nonzero predecessor-type ones. It also evaluates the repeated-shift entry $\mathbb E[a(m)^2a(m+1)]$ exactly as $-1/4$ in model A and $0$ in model B. $\square$

For $\eta(12\tau)^2$ the finite sums through $6000$ are also measured: $\sum_m a(m)u(m-h)$ is $1,1,12,12,-9,34,15,15$ for $h=1,\dots,8$, and the forward sums are $-34,10,-24,25,-23,-25,-8,-15$ [finite]. The predecessor sums are the ones that enter $\Phi$.

### Lemma D2.2. Gap-indexed Gram matrices collapse; $2\times2$ Gram bounds are vacuous

**Paper proof, objective 4.** (a) Put $v_i=s_i\,e_{\psi(g_i)}$ for any gap labelling $\psi$. Then $\sum_iv_iv_i^{\mathsf T}=\sum_ie_{\psi(g_i)}e_{\psi(g_i)}^{\mathsf T}$ because $s_i^2=1$, so the matrix carries no sign information.

(b) Let $(x_i,y_i)$ be real numbers with $x_iy_i=s_ig_i$ for every endpoint $i$. Their Gram matrix

$$
\begin{pmatrix}\sum_i x_i^2&\sum_i s_ig_i\\ \sum_i s_ig_i&\sum_i y_i^2\end{pmatrix}
$$

is PSD and yields $|\sum s_ig_i|\le\sqrt{\sum x_i^2\sum y_i^2}$. By Cauchy–Schwarz,

$$
\sqrt{\sum_i x_i^2\,\sum_i y_i^2}\ \ge\ \sum_i|x_iy_i|=\sum_i g_i ,
$$

so every such bound is at least the trivial bound $\sum g$. The inequality is sharp. The choice $(x_i,y_i)=(s_i\sqrt{g_i},\sqrt{g_i})$ gives both diagonal entries equal to $\sum g$ and attains $\sum g$ exactly. The bordered matrix $\begin{pmatrix}S&\sum s g\\ \sum s g&\sum g^2\end{pmatrix}$ is the case $(x_i,y_i)=(s_i,g_i)$, and $(s_ig_i^e,g_i^{1-e})$ gives a different matrix for every real $e$. No single matrix is canonical; all are vacuous. The same holds for vectors $x_i,y_i\in\mathbb R^d$ with $\langle x_i,y_i\rangle=s_ig_i$, since $\sqrt{\sum\|x_i\|^2\sum\|y_i\|^2}\ge\sum\|x_i\|\|y_i\|\ge\sum|\langle x_i,y_i\rangle|$.

The verifier checks (a) and (b) on the $2508$ endpoints through $6000$. For (b) it tests the family $e=-1,0,2,3$ and the equality case. It also checks exactly that the $12\times12$ signed Toeplitz Gram matrix $G$ is PSD and invariant under $s\mapsto-s$. Next it checks that the $9\times9$ mixed Gram matrix $G_m$ of $(a(m),u(m-1),\dots,u(m-8))$ is PSD. $G_m$ is not invariant under $s\mapsto-s$. It becomes $JG_mJ$ with $J=\mathrm{diag}(-1,1,\dots,1)$, so its mixed entries $\sum_m a(m)u(m-h)=1,1,12,12,-9,34,15,15$ change sign while the diagonal and the support block stay fixed. Positivity is preserved by this congruence, and the verifier checks $G_m(-s)=JG_m(s)J$ exactly. $\square$

### Theorem D2.3. The moment–positivity ceiling

**Paper proof, objective 4.** Fix $H$. Let $\mu$ range over probability laws on predecessor patterns $\omega\in\{0,1\}^{H-1}$, where $\omega_h=1$ means $m-h\in U$. Suppose $\mu(\omega_h=1)\le u_h$ with $\sum_hu_h\le1$, and impose arbitrary upper bounds on higher moments. Then

$$
\min_\mu\ \mathbb E_\mu\min(g,H)=H-\sum_{h<H}(H-h)u_h,
$$

and the minimum is attained by the law with at most one predecessor, $\mu(\omega=e_h)=u_h$. Consequently the following, combined with upper correlation bounds of any order such as higher-order sieve weights or multi-endpoint upper sieves, cannot improve the first-order bound of class $\mathfrak B$: PSD moment matrices, Lasserre/SOS hierarchies, Bonferroni, Hunter, Kounias, de Caen, and every other inequality valid for all probability laws. In particular, at $t=1/K$ the optimum of D1.3 has $\sum_hu_h=1$ exactly. An improvement requires a **lower** bound on some correlation that has a support factor to the left of the signed endpoint.

**Arbitrary horizons.** Suppose instead $\sum_{h<H}u_h>1$, as happens for $H>1/(K\rho)$. Then

$$
\min_\mu\ \mathbb E_\mu\min(g,H)=\sum_{v=0}^{H-1}\Bigl(1-\sum_{h\le v}u_h\Bigr)_+ ,
$$

which agrees with the display above when $\sum_{h<H}u_h\le1$. Let $H_0$ be the first index with $\sum_{h\le H_0}u_h\ge1$. The minimum is attained by the greedy singleton law with $\mu(\omega=e_h)=u_h$ for $h<H_0$ and $\mu(\omega=e_{H_0})=1-\sum_{h<H_0}u_h$. It is a genuine probability law with $\mu(\omega_h=1)\le u_h$, and all its higher moments vanish. With $u_h=K\rho$ the value is $(1+o(1))/(2K\rho)$ per endpoint, which is again $1/(4K)$ per unit of $N$. No choice of horizon escapes the ceiling.

*Proof.* The lower bound is the pointwise inequality of D1.3. For general $H$, write $\min(g,H)=\sum_{v<H}\mathbf 1[g>v]$ and apply the union bound $\Pr(g>v)\ge1-\min\bigl(1,\sum_{h\le v}u_h\bigr)$; the greedy law attains it for every $v$. The extremal law is a genuine probability law, so it satisfies every constraint valid for probability laws, and all its higher moments vanish, so every upper bound holds. Global consistency with a single point set is supplied by D1.4. The verifier checks that the $7\times7$ moment matrix of the extremal law is PSD and that its mean equals the bound. It checks the layer-cake identity on all $4094$ patterns with $H\le12$. It also checks the greedy law, its PSD moment matrix and the displayed minimum for two rate vectors with $\sum u_h>1$, one of them with a fractional residual mass. $\square$

**Classification of the D2 candidates.**

| Method | Data type | Outcome |
| --- | --- | --- |
| Gram, Hankel or Toeplitz matrices of signs or coefficients | signed leftmost off the diagonal, pure support on it | blind (D2.1) |
| Higher moment tensors or Lasserre moment matrices of $a$ with repeated shifts | include predecessor-type entries such as $C(\{1\},\{0\})$ | not blind; upper bounds give the first-order ceiling (D2.3), lower bounds are **Open** (§1.7) |
| Gap-indexed Gram matrices | even in signs | collapse (D2.2a) |
| $2\times2$ Gram matrices containing $\sum s\,g$ | any factorization $x_iy_i=s_ig_i$ | vacuous, bound $\ge\sum g$ (D2.2b) |
| Shifted convolution sums and spectral expansions of $\eta(12\tau)^2$ | signed leftmost, or not involving $\mathbf 1_U$ | blind (D2.1) |
| Hecke-character signs and orthogonality in progressions | one-point signed | blind; already GF-43, Corollary 1.1 |
| Positive (upper) sieve weights, any order | upper bounds | first-order ceiling (D2.3, D1.4) |
| Lower bounds on predecessor-type correlations | the needed data | **Open**: beyond the sieving limit (§1.7) |

The support indicator $\mathbf 1_U=\mathbf 1[c\ne0]$ is not the coefficient sequence of a modular form. Spectral methods for $\sum c(l)c(l-12h)$ therefore do not reach $\sum c(l)\mathbf 1[c(l-12h)\ne0]$. Replacing $\mathbf 1_U$ by $c^2$ changes the functional, because $\sum s\,g$ depends only on the support.

## 3. D3: The theta cube and fourth power

Write $x_{j,k}=\Theta_3(2^{-k})^j=\sum_{n\ge0}r_j(n)2^{-kn}$.

### 3.1. Prior art, read from the source

The source is Bailey, Borwein, Crandall and Pomerance, *On the binary expansions of algebraic numbers*, **J. Théor. Nombres Bordeaux 16 (2004), no. 3, 487–518**, DOI 10.5802/jtnb.457. We read pp. 506–510 of the scan directly. It is not in *Experimental Mathematics* 13(3); that citation in the Track D brief is incorrect. Section 9 contains the following.

- **p. 506.** The identity $z'^2=4\sum_{d\text{ odd}}(-1)^{(d-1)/2}/(2^d-1)$ for $z'=\Theta_3(1/2)$, described as "reminiscent of the Erdős–Borwein number" $E=\sum1/(2^n-1)=\sum d(m)/2^m$. Erdős's irrationality proof of $E$ and P. Borwein's Padé proof are cited. The transcendence of $z,z'$ is quoted from the literature.
- **Theorem 9.1 and Corollary 9.2.** Long zero runs of $r_2$.
- **Theorem 9.3.** $z=\sum_{n\ge0}2^{-n^2}$ is not a quadratic irrational.
- **Theorem 9.4 (p. 509).** "Almost all bits of $z^2$ are 0's", with $\#(z^2,N)\sim C_0N/\sqrt{\log N}$ and $C_0\approx0.7996$. The text adds that "the asymptotic density also holds for $z'^2$".
- **Remark on p. 509.** "Higher powers such as $z^3,z^4$ are likely 2-normal. Indeed, all such higher powers will involve interfering carries. For example, it is known that $r_3(n)>0$ for a limiting fraction $5/6$ of all $n$ …, so the carry problem for $z^3$ is already formidable." This is a heuristic remark, not a theorem.

BBCP do not use the $4$-adic structure $r_3(4n)=r_3(n)$, Legendre's exceptional set $4^a(8b+7)$, or class numbers in §9; only the density $5/6$ appears. GF-43's attribution matches the source. GF-43 also proves $z^3$ normal if and only if $(z')^3$ is.

### Proposition D3.1. Exact identities

**External input (classical), checked by Finite certificate, objective 3.**

1. **Gauss, Kronecker and Hurwitz.** $r_3(n)=12\bigl(H(4n)-2H(n)\bigr)$ for all $n\ge0$, with Hurwitz class numbers $H$ and $H(0)=-1/12$. Equivalently $\Theta_3^3=12(U_4\mathcal H-2\mathcal H)$ for Zagier's weight-$3/2$ class-number series $\mathcal H$. The special cases in the brief, $r_3(n)=12H(4n)$ for $n\equiv1,2\bmod4$ and $r_3(n)=24H(n)$ for $n\equiv3\bmod8$, follow from $H(n)=0$ and $H(4n)=4H(n)$ respectively. With Hurwitz class numbers, which carry the automorphism weights, the second case includes $n=3$: $r_3(3)=8=24H(3)$ with $H(3)=1/3$. The restriction $n>3$ in the brief is needed only for the unweighted class number $h(-n)$. The case $n\equiv7\bmod8$ gives $H(4n)=2H(n)$, hence $r_3(n)=0$.
2. **The $4$-adic tower.** Let $\mathfrak F=\{m\ge1: m\bmod8\in\{1,2,3,5,6\}\}$ and $Y(q)=\sum_{n\in\mathfrak F}r_3(n)q^n$. Then $\Theta_3(q)^3=1+\sum_{i\ge0}Y(q^{4^i})$, so $x_{3,k}=1+\sum_{i\ge0}Y(2^{-4^ik})$. Indeed $r_3(4^im)=r_3(m)$, and $r_3$ vanishes on $4^a(8b+7)$, which has density $1/6$.
3. **Three odd coordinates.** $\sum_nr_3(8n+3)q^{8n+3}=8q^3\psi(q^8)^3$ with $\psi(q)=\sum_{j\ge0}q^{j(j+1)/2}$, so $8\mid r_3(n)$ for $n\equiv3\bmod8$.
4. **Jacobi.** $r_4(2^au)=24\sigma(u)$ for $a\ge1$ and $u$ odd, so $r_4(4n)=r_4(2n)$.

The verifier checks (1) and its three special cases, including $n=3$, for $n\le600$ with $H$ computed from weighted reduced forms, and (2)–(4) for $n\le2200$. It also checks Jacobi's identity for $E^3$ through $q^{3000}$ (prior input of GF-04).

### Theorem D3.2. Inertness of Legendre, 2-adic, scaling and size data

**Paper proof, objective 4.** Fix integers $k\ge1$ and $t\ge0$ and put $J=2^{3k+2}$. For every choice $(j_m)_{m\in\mathfrak F}\in\{0,\dots,J\}^{\mathfrak F}$ put $a_0=r_3(0)=1$ and, for $n\ge1$, $a_n=r_3(n)+2^tj_{\mathrm{rep}(n)}$. Here $\mathrm{rep}(n)=n/4^{\lfloor v_2(n)/2\rfloor}$, and $a_n=0$ if $\mathrm{rep}(n)\notin\mathfrak F$. The perturbation acts only on $n\ge1$. Each such sequence has the following properties:

- (a) the same zero set as $r_3$;
- (b) $a_{4n}=a_n$;
- (c) $a_n\equiv r_3(n)\bmod2^t$, hence $v_2(a_n)=v_2(r_3(n))$ whenever the latter is below $t$;
- (d) $0\le a_n-r_3(n)\le2^{t+3k+2}$. So $a_n/r_3(n)\to1$ in density on the support of $r_3$, which has density $5/6$ ($r_3$ vanishes on a set of density $1/6$). All size asymptotics (Gauss–Dirichlet, Siegel, limiting laws of $L(1,\chi)$) are unchanged, and $w(a_n)\ge w(r_3(n))-(t+3k+3)$. GF-43, Theorem 2 therefore holds verbatim.

With $w_m=\sum_{n\ge1:\ \mathrm{rep}(n)=m}2^{-kn}=\sum_{i\ge0}2^{-k4^im}$, the values $\sum_na_n2^{-kn}$ fill the whole interval

$$
\Bigl[x_{3,k},\ x_{3,k}+2^tJ\sum_{m\in\mathfrak F}w_m\Bigr].
$$

The same holds for $r_4$, with $a_0=r_4(0)=1$, $\mathfrak F=\{m\ge1:m\not\equiv0\bmod4\}$, $\mathrm{rep}$ dividing by $2$ while $4\mid n$, and (b) replaced by $a_{4n}=a_{2n}$. The weights are again $w_m=\sum_{\mathrm{rep}(n)=m}2^{-kn}$. Now this is $2^{-km}$ for odd $m$ and $\sum_{i\ge0}2^{-k2^im}$ for $m\equiv2\bmod4$, and the interval is $\bigl[x_{4,k},\,x_{4,k}+2^tJ\sum_{m\in\mathfrak F}w_m\bigr]$.

**Consequently no argument using only (a)–(d) can decide** any of the following for $\Theta_3(2^{-k})^3$ or $\Theta_3(2^{-k})^4$: normality, simple normality, disjunctivity, membership in $K_2$, or an explicit bound $D^+<1$ or $D^->0$. The interval contains normal numbers, dyadic rationals (in $K_2$, not disjunctive), and rationals with $D_\infty$ strictly between $0$ and $1$. In particular, Legendre's zero density $1/6$, $r_3(4n)=r_3(n)$, genus and $2$-adic data modulo any fixed $2^t$, class-number size bounds, carry conservation and localized low-bit analysis, all used **together**, are distributionally inert. A decisive argument must control the bits of $r_j(n)$ above every fixed position, jointly across neighbouring $n$.

*Proof.* (a)–(d) are immediate; nonvanishing holds because $r_3(m)>0$ on $\mathfrak F$ by Legendre. The value is $x_{3,k}+2^t\sum_mj_mw_m$ with $w_m=\sum_{i\ge0}2^{-k4^im}$. Consecutive elements of $\mathfrak F$ differ by at most $3$. Also $w_m\le2\cdot2^{-km}$ and $w_{m'}\ge2^{-k(m+3)}$ for the next element $m'$, so $w_m\le Jw_{m'}$. Run the greedy algorithm with digits $j_m=\min(J,\lfloor R_m/w_m\rfloor)$. By induction the remainder never exceeds the tail capacity $J\sum_{m''\ge m}w_{m''}$: either $j_m=J$, or the new remainder is below $w_m\le J\sum_{m''>m}w_{m''}$. The remainder is nonnegative and tends to $0$ (Kakeya's criterion for subsums). For $r_4$ the free set has gaps at most $2$, and again $w_m\le2\cdot2^{-km}\le Jw_{m'}$. $\square$

The verifier runs the construction exactly for $k=1$, $n\le240$: with $t=2$ for the cube and $t=3$ for the fourth power. For each it reaches two prescribed targets, one of them dyadic, up to a final remainder below one digit step. It checks (a)–(d) on every coefficient.

### Proposition D3.3. The 2-adic valuation law of $r_4$

**Paper proof, objective 3 (coefficient law, not a digit law).** For every $\epsilon>0$,

$$
\frac1X\#\Bigl\{n\le X:\ \bigl|v_2(r_4(n))-2\log\log X\bigr|>\epsilon\log\log X\Bigr\}\to0 .
$$

*Proof.* By GF-43, $f(n):=v_2(r_4(n))-3=\sum_{p^e\parallel n,\,p\text{ odd}}b_p(e)$ is additive with $f(p)=v_2(p+1)$. Layer-cake gives $\sum_{p\le X}v_2(p+1)/p=\sum_{j\ge1}\sum_{p\le X,\,p\equiv-1\bmod2^j}1/p$. For fixed $j$ this is $2^{1-j}\log\log X+O_j(1)$ by Dirichlet and Mertens in progressions. Brun–Titchmarsh bounds the range $j>J$ by $O((\log\log X+J)2^{-J})$. Hence $A(X)=(2+o(1))\log\log X$, using $\sum j2^{-j}=2$. Likewise $\sum_{p\le X}f(p)^2/p\le(6+o(1))\log\log X$, using $\sum j^22^{-j}=6$, and prime powers contribute $O(1)$. The Turán–Kubilius inequality gives $\sum_{n\le X}|f(n)-A(X)|^2\ll X\log\log X$. Apply Chebyshev. $\square$

So the lowest $\sim2\log\log n$ bits of $r_4(n)$ vanish. By D3.2 this has no consequence for the digits of $x_{4,k}$. [finite] For odd primes up to $2\cdot10^5$, the mean of $v_2(p+1)$ is $2.0022$.

### Corollary D3.4. Sharp carry order for the fourth power

**Paper proof, objective 4.** In GF-43's exact column identity at fixed $k\ge1$, the carry volume of $x_{4,k}$ satisfies $K_M\asymp M\log M$. For $x_{3,k}$ it satisfies $K_M/M\to\infty$ and $K_M\ll M\log M$. Thus normalizing the fourth power requires cancelling $\asymp\log M$ carries per digit.

*Proof.* The identity reads $K_M=\sum_{n\le M}s_2(c_n)+s_2(C_M)-kMf_1-s_2(\lfloor x\rfloor)$ with $0\le f_1\le1$ and $s_2(C_M)=O(\log M)$. For the upper bound use $s_2(c_n)\le\log_2c_n+1\ll\log M$. For the lower bound, $s_2\ge w$ and GF-43, Theorem 2 give $\sum w(r_4(n))\asymp M\log M$ and $M^{-1}\sum w(r_3(n))\to\infty$. $\square$

**Open (D3).** The binary one-frequency, the transition density, membership in $K_2$, and normality of $\Theta_3(2^{-k})^3$ and $\Theta_3(2^{-k})^4$ remain open for every fixed $k$, including $k=1$. So does a lower bound $\gg\log M$ for the mean of $s_2(r_3(n))$; it would need a multiplicity bound for class numbers in short ranges.

## 4. D4: Higher Euler powers and prime subseries

**Index conventions.** For $(r,c,w)=(4,6,2),(6,4,3),(8,3,4)$ put $f=\eta(c\tau)^r=qE(q^c)^r=\sum a_f(n)q^n$. This is a CM newform of weight $w$: CM by $\mathbb Q(\sqrt{-3})$ for $r=4,8$ and by $\mathbb Q(i)$ for $r=6$. The **Euler index** $j$ and the **modular index** $n=cj+1$ are related by $[q^j]E(q)^r=a_f(cj+1)$. The **full value** at stretch $k$ is $E(2^{-k})^r=\sum_ja_f(cj+1)2^{-kj}$. Its **prime part** is $P_{r,k}=\sum_{p\equiv1\bmod c}a_f(p)2^{-k(p-1)/c}$ and its **composite complement** is $C_{r,k}=E(2^{-k})^r-P_{r,k}$. The **prime subseries in modular index**, studied in GF-43 Theorem 4, is $y_{f,k}=\sum_pa_f(p)2^{-kp}$. These are four different numbers.

**External input (as in GF-17, GF-27 and GF-43).** These are the CM identifications, with $a_f(p)=\mathrm{Tr}(\zeta\pi^{w-1})$ for a generator $\pi$ of a prime above a split $p$ and a unit $\zeta$, and $a_f(p)=0$ for inert $p$. The verifier confirms on the computed ranges several consequences of these identifications: the support law ($a_f(n)\ne0$ exactly when every inert prime has even exponent in $n$), nonvanishing at split primes, $a_f(p)^2\le4p^{w-1}$, and $|a_f(p)|\in\{|2A|,|A\pm3B|\}$ (respectively $\{|2A|,|2B|\}$), where $\pi^{w-1}=A+B\sqrt{-3}$ (respectively $A+Bi$). The checked ranges are Fourier indices up to $20401$, $10001$ and $7501$.

### Lemma D4.0. $K_2=M_2$ in base 2

**Paper proof, objective 2.** First, $M_2\subset K_2$: the interval $[\epsilon,1-\epsilon)$ eventually receives $o(N)$ points. Conversely, suppose $D_N\to1$. Then either a fraction $1-\eta$ of the points lies in an interval of length $\le\eta$, or a fraction $\le\eta$ lies in an interval $[a,b)\supset[\eta,1-\eta)$. In the first case at least $(1-2\eta)N-1$ consecutive pairs $y_n,y_{n+1}=2y_n\bmod1$ lie in the short interval. Since $|\{2y\}-y|=\|y\|$ for every $y\in[0,1)$, this forces $\|y_n\|<\eta$. In both cases all but $O(\eta N)+1$ points are within $\eta$ of $0$ on the circle. $\square$

The same argument gives a quantitative form. Let $\tau$ be the lower density of positions $n$ with adjacent unequal binary digits; such a transition means exactly $y_n\in[1/4,3/4)$. Then

$$
D^+\ \le\ 1-\min\Bigl(\frac14,\frac\tau2\Bigr).
$$

Indeed, let $\eta\le1/4$ and $D_N>1-\eta$. In the first case all but at most $2\eta N+1$ indices $n<N$ have $\|y_n\|<\eta\le1/4$, so $y_n\notin[1/4,3/4)$. In the second case $[1/4,3/4)\subset[\eta,1-\eta)$ receives fewer than $\eta N$ points. Either way the proportion of transitions among the first $N$ positions is at most $2\eta+O(1/N)$. For every $\eta<\min(1/4,\tau/2)$ that proportion eventually exceeds $2\eta+O(1/N)$, so $D_N\le1-\eta$ for all large $N$. Let $\eta\uparrow\min(1/4,\tau/2)$.

The cap $1/4$ cannot be removed. Both steps use $\eta\le1/4$: for larger $\eta$ the set $\{\|y\|<\eta\}$ meets $[1/4,3/4)$. The point $x=1/3=0.\overline{01}_2$ has $\tau=1$, while its orbit $\{1/3,2/3\}$ gives $D^+=2/3>1/2=1-\tau/2$, witnessed by the intervals $[1/3,2/3+\epsilon)$. Every transition density in D4.1 is at most $c'_w/1024<1/2$, so there $\min(1/4,\tau/2)=\tau/2$. The verifier checks $D_\infty\le1-\min(1/4,\tau/2)$ exactly on all $121$ binary cycles $a/d$ with $d$ odd and $d\le99$. On such a cycle $D^+=D^-$ is the discrepancy of the uniform measure on the orbit. Only the cycle $\{1/3,2/3\}$ exceeds the uncapped $1-\tau/2$ in this range.

### Theorem D4.1. Large-stretch prime subseries are outside $K_2$

**Paper proof, objectives 2 and 3.** Let $\lambda=(w-1)/(2k\log2)$ and suppose $\lambda<1/64$, that is, $k\ge k_0(w)=47,93,139$ for $w=2,3,4$. Then adjacent unequal binary digits of $y_{f,k}$ have lower density at least

$$
\tau_{w,k}=\Bigl(\frac12-32\lambda\Bigr)\frac{c'_w(w-1)}{4k\log2},\qquad c'_2=\tfrac15,\ c'_3=\tfrac2{25},\ c'_4=\tfrac1{22}.
$$

Hence $y_{f,k}\notin K_2$ and $D^+(y_{f,k};2)\le1-\tau_{w,k}/2<1$ by Lemma D4.0. The cap there is inactive: since $(w-1)/(4k\log2)=\lambda/2$, we have $\tau_{w,k}=c'_w(\frac12-32\lambda)\frac\lambda2\le\frac{c'_w}{1024}\le\frac1{5120}$, by $\frac1{1024}-(\frac12-32\lambda)\frac\lambda2=16(\lambda-\frac1{128})^2$. Together with GF-43 Theorem 4 this gives

$$
\frac12-\frac{w-1}{4k\log2}\ \le\ D^-\ \le\ D^+\ \le\ 1-\frac{\tau_{w,k}}2 .
$$

The same holds for the Euler-index prime parts $P_{r,k}$ when $k\ge277,370,416$ for $r=4,6,8$, with $k$ replaced by $k/c$ throughout. In the Euler index the primes sit at positions $k(p-1)/c$, so the effective stretch per modular unit is $k/c$. The lower transition density of $P_{r,k}$ is therefore

$$
\tau_{w,k/c}=\Bigl(\frac12-32c\lambda\Bigr)\frac{c\,c'_w(w-1)}{4k\log2},
$$

so $\lambda$ becomes $c\lambda$ inside the bracket and the outer factor is multiplied by $c$. The condition $c\lambda<1/64$ gives the thresholds $277,370,416$, and again $\tau_{w,k/c}\le c'_w/1024$.

**Certified lower bounds.** Each value quoted here is the downward truncation to three significant digits of an exact rational lower bound for $\tau_{w,k}$. That rational uses $\log2$ from below inside $\lambda$ and from above in the outer factor. The verifier asserts every displayed inequality as an exact `Fraction` comparison and checks that it is the three-digit truncation. The bounds are $\tau_{2,47}>1.36\cdot10^{-5}$ and $\tau_{2,94}>1.95\cdot10^{-4}$; $\tau_{3,93}>2.22\cdot10^{-6}$ and $\tau_{3,186}>7.81\cdot10^{-5}$; $\tau_{4,139}>6.38\cdot10^{-7}$ and $\tau_{4,278}>4.43\cdot10^{-5}$. An earlier version printed $\tau_{3,93}>2.23\cdot10^{-6}$ and $\tau_{4,278}>4.44\cdot10^{-5}$ by round-to-nearest. Both were false, since $\tau_{3,93}=2.2269\ldots\cdot10^{-6}$ and $\tau_{4,278}=4.4389\ldots\cdot10^{-5}$. The transition density is $\asymp1/k$ for large $k$.

*Proof.* Write $L_p=\lfloor\log_2|a_f(p)|\rfloor\le1+\frac{w-1}2\log_2p$ and $H_p=(\frac{w-1}2\log_2(4p)+4)/k$.

*Isolation.* Call a split prime $p$ **isolated** if no other split prime lies within distance $H_p$ of it. For such $p$ write $2^{kp}y=I_p+a_f(p)+\tau_p$. Here $I_p$ is a multiple of $2^{k(p-p^-)}\equiv0\bmod2^{L_p+2}$, and $|\tau_p|\le\sum_{m\ge H_p}2(2p)^{(w-1)/2}2^{-km}+o(1)<1$. So the digits in the window of $L_p+2$ positions ending at $kp$ are the bits of $(a_f(p)+\varepsilon)\bmod2^{L_p+2}$ with $\varepsilon\in\{0,-1\}$. Put $A=|a_f(p)|<2^{L_p+1}$.

- If $a_f(p)>0$, the window is the $(L_p+2)$-bit string of $M=A+\varepsilon\in\{A-1,A\}$.
- If $a_f(p)<0$, the window is the bitwise complement of the string of $M=A-1-\varepsilon\in\{A-1,A\}$, and it has the same transitions.

In both cases $M<2^{L_p+1}$, so the top bit of the string of $M$ is $0$ and only the right edge of the window can cut a run of ones. If $M$ has $R$ runs of ones, at most one of them loses a transition at the edge, so there are at least $2R-1$ transitions. A run $2^b-2^a$ has signed weight at most $2$, so $w(M)\le2R$; and $w(A)\le w(A-1)+1$. Hence the window contains at least $w(M)-1\ge w(A)-2$ transitions. One unit of the $-2$ is lost at the right edge and one to $\varepsilon$. Windows of distinct isolated primes are disjoint.

*Counting isolated primes.* Selberg's upper bound for prime pairs gives $\#\{p\le2X:p+h\text{ prime}\}\le(8+o(1))\mathfrak S(h)\,2X/\log^2X$ uniformly for $1\le h\le\log^2X$ (Halberstam–Richert, *Sieve Methods*, Thm. 3.11). Moreover $\sum_{h\le H}\mathfrak S(h)\le H$ exactly, by the local identity $1+\frac1{p(p-2)}=(1-\frac1{(p-1)^2})^{-1}$. So at most $(32\lambda+o(1))X/\log X$ split primes in $(X,2X]$ have a prime within $\max H_p=\lambda\log X+O(1)$ on either side. There are $(\frac12+o(1))X/\log X$ split primes in $(X,2X]$.

*Entropy.* Fix $v$ and $y$. Write $\pi=x+y\sqrt{-3}$ or $x+yi$ for a generator with $x,y\in\mathbb Z$. Since $-1$ is a unit, $|a_f(p)|=v$ means $\mathrm{Tr}(\zeta\pi^{w-1})=v$ for one of at most $6$ units $\zeta$. As a polynomial in $x$ this relation has degree at most $w-1$, and it is nonconstant. Its $x^{w-1}$ coefficient is $\mathrm{Tr}(\zeta)\ne0$, except for $\zeta=\pm i$ in $\mathbb Q(i)$, where $w=3$. There $\mathrm{Tr}(\pm i(x+yi)^2)=\mp4xy$, and $y\ne0$ because $p=x^2+y^2$ is prime. So at most $6(w-1)(2\sqrt{2X}+1)$ primes $p\le2X$ have $|a_f(p)|=v$. The number of $v<2^B$ with $w(v)\le\alpha(B+1)$ is at most $\sum_{j\le\alpha(B+1)}\binom{B+1}j2^j\le2^{(B+1)(H(\alpha)+\alpha)}$ for $\alpha\le2/3$; take the weight $t^j$ with $t=\alpha/(2(1-\alpha))$. With $B+1\le\frac{w-1}2\log_2(2X)+3$ and $\alpha=c'_w$, the exact inequalities $(w-1)(H(c'_w)+c'_w)<1$ give an exception count $O(X^{1-\eta})$. Thus all but $o(X/\log X)$ split primes in $(X,2X]$ have $w(|a_f(p)|)\ge c'_w\frac{w-1}2\log_2X-1$.

*Conclusion.* The isolated large-weight primes in $(X,2X]$ contribute at least $(\frac12-32\lambda-o(1))\frac{c'_w(w-1)}{2\log2}X$ transitions among the first $2kX$ digits. Taking $X=P/(2k)$ for a prefix of length $P$ gives the lower density. Apply Lemma D4.0. In the Euler index, primes sit at positions $k(p-1)/c$, so all distances scale by $1/c$. $\square$

[finite] For $\eta(6\tau)^4$ at $k=24$, the first $480{,}000$ bits of $y_{f,24}$ have $4382$ transitions, density $0.00913$. The bits are certified by a guard tail. GF-43's ceiling is $0.01503$. In this range every split prime is isolated, since every coefficient fits in one block. The proved $\tau$ is far below the measured density, which is no evidence about limits.

### Theorem D4.2. A dichotomy for the full Euler powers

**Paper proof, objectives 2 and 4.** For $r=4,6,8$ and Euler stretch $k\ge277,370,416$ respectively, at most one of the full value $E(2^{-k})^r$ and its composite-index complement $C_{r,k}$ lies in $K_2$. Equivalently, $E(2^{-k})^r\in K_2$ implies $C_{r,k}\notin K_2$, and the reverse implication also holds.

*Proof.* $M_2$ is an additive group (GF-43) and equals $K_2$ (D4.0). By D4.1, $P_{r,k}\notin K_2$. If both $E(2^{-k})^r$ and $C_{r,k}$ were in $M_2$, so would be their difference $P_{r,k}$. $\square$

### Proposition D4.3. The composite complement: density zero, diverging weight, no decision

**Paper proof, objective 4.** In the Euler index, the support of $C_{r,k}$ has count $\asymp M/\sqrt{\log M}$ through $M$. That is the CM support law with half of the primes inert, by Wirsing's theorem, minus the $O(M/\log M)$ prime indices. Its density is therefore **zero**, not positive. The total minimum signed weight of its coefficients through $M$ is $\asymp M\sqrt{\log M}$. GF-27, Corollary D4.15 gives this for all of $E^r$, and the prime part has weight $O(M)$ by GF-43. The mean weight is therefore $\asymp\sqrt{\log M}$ per index $1\le j\le M$, zeros included, and $\asymp\log M$ per supported composite index. Both diverge. Neither property decides membership in $M_2=K_2$, for two reasons.

1. Positive density, or full support, together with diverging mean weight is compatible with membership in $M_2$. Put $d_n=(4^{b(n)}-1)/3$, where $b(n)$ is the bit length of $n$, and $c_n=2d_n-d_{n+1}\ne0$. Then $\sum_{n\ge1}c_n2^{-n}=d_1=1$, an integer, while the mean NAF weight of $c_n$ tends to infinity. The verifier checks the telescoping identity exactly, $c_n\ne0$ for all $n\le2^{14}$, and a mean weight of $13.00$ there.
2. Diverging mean weight only makes the sparse-transfer upper bound $w(\text{prefix})\le\sum w(c_n)+O(\log M)$ of GF-43 §3 useless. That is a barrier for the method, not a statement about $C_{r,k}$.

The correct new information is D4.2. **Do not** infer $C_{r,k}\notin M_2$ from support density or coefficient weight.

**Euler's cube.** $E_2^3$, and indeed $E_b^3$ for every radix $b$, is already settled by GF-04: it lies in $K_b$, is disjunctive, its constant words $0^L$ and $(b-1)^L$ have frequency $1/2$, and $1-D_N=\sqrt2(\log_bN)/\sqrt N+O_b(1/\sqrt N)$. Nothing here duplicates or extends it. Jacobi's identity is rechecked through $q^{3000}$.

[finite] The Euler-index counts are as follows; the mean NAF weight is taken per supported composite index. For $E^4$ through $3400$: support $2091$ (prime $1146$, composite $945$), mean weight $2.28$. For $E^6$ through $2500$: support $1306$ (prime $609$, composite $697$), mean weight $4.67$. For $E^8$ through $2500$: support $1120$ (prime $468$, composite $652$), mean weight $5.36$.

**Open (D4).** Several questions remain open: membership in $K_2$, normality, and digit frequencies of the full values $E(2^{-k})^r$ for $r\ge4$ at every stretch; which side of the dichotomy D4.2 holds; and D4.1 for small $k$, including $k=1$, where the prime coefficients overlap pervasively.

## 5. Reproduction and evidence

Run the standard-library verifier from the repository root:

~~~sh
python -B scripts/phase26_euler_modular.py
~~~

**Finite certificate.** The verifier [phase26_euler_modular.py](../../scripts/phase26_euler_modular.py) exits with code $0$ on Windows after **44,890** exact `int`/`Fraction` assertions; no `check(...)` predicate involves a float. It checks:

- **D1.**
  - Machin enclosures $106103/10^6<1/(3\pi)<106104/10^6$ and $2^{3/4}/(3\pi)\in(0.1784,0.1785)$.
  - The exponent and $\Gamma$-reflection bookkeeping behind $K=3\pi/4$ and the transfer formula.
  - The optimization identity.
  - The first-order inequality and the layer-cake identity on all $4094$ predecessor patterns with $H\le12$, and optimality of truncation on all small test functions.
  - The sharpness model with $K=113/48$: exact triangular and uniform predecessor sums for every $H<180$, the grid $180,187,\dots,2014$ and $H=2016$, the equality range, and $W_+/N$.
  - The warning model: stationary uniform signed residues for $q\le12$, and $\Phi=1/2$.
  - Model-pair correlations, enumerated exactly, including the repeated-shift entry $\mathbb E[a(m)^2a(m+1)]=-1/4$ (model A) against $0$ (model B).
  - The CM formula for $a(n)$ against pentagonal convolution through $n=2000$, and the signed-truncation identity.
- **D2.**
  - Exact PSD tests: the $12\times12$ signed Toeplitz matrix, the $9\times9$ mixed matrix and its sign-flipped version, the bordered matrix, the $2\times2$ Gram family, and the $7\times7$ extremal moment matrix.
  - Sign-flip invariance of the $12\times12$ matrix $G$, and the exact conjugation $G_m(-s)=JG_m(s)J$ with every mixed entry changing sign.
  - The collapse identity, the Cauchy–Schwarz inequality for the $2\times2$ family, and its equality case.
  - The greedy singleton law and the arbitrary-horizon minimum for two rate vectors with $\sum u_h>1$.
- **D3.**
  - Legendre's zero set and $r_3(4n)=r_3(n)$ for $n\le2200$.
  - $r_3=12(H(4n)-2H(n))$ and its special cases, including $r_3(3)=24H(3)=8$, for $n\le600$.
  - $8q^3\psi(q^8)^3$, the $4$-dissection, Jacobi's $r_4$ and $r_4(4n)=r_4(2n)$.
  - The partial sums $\sum j2^{-j}$ and $\sum j^22^{-j}$.
  - Both inertness constructions.
  - Jacobi's identity for $E^3$.
- **D4.**
  - The CM support law and magnitude forms over the stated ranges.
  - The entropy inequalities for $c'_w$, the exact integer thresholds $47,93,139$ and $277,370,416$ (with a rational enclosure of $\log2$), and the bound $\tau_{w,k}\le c'_w/1024$.
  - The six certified lower bounds on $\tau_{w,k}$. Each is asserted as an exact rational inequality and checked to be the downward three-digit truncation; no lower bound is printed by rounding.
  - The quantitative form of Lemma D4.0, $D_\infty\le1-\min(1/4,\tau/2)$, on all $121$ binary cycles with odd denominator at most $99$, and $D_\infty(1/3;2)=2/3>1-\tau/2$.
  - The singular-series local identity for $p<2000$ and $\sum_{h\le H}\mathfrak S(h)\le H$ for $H\le300$.
  - The guard-certified bit prefix and the telescoping identity.

**Finite measurement** (lines tagged `[finite]`): the $E_2^2$ signed sums through $6000$ ($S_+=1259$, $S_-=1249$, $\sum s\,g=61$), the predecessor and successor sums, the $v_2(p+1)$ statistics, the prime-subseries transition count, and the Euler-power support counts. These are individual finite prefixes. They are not evidence for any limit.

**Exploration** (the single float block): the $\beta$-sieve delay-differential solution behind D1.5, on a delay-aligned grid with Richardson extrapolation. It proves nothing and is not used in any assertion.

**Evidence scope.** The labels are as follows.

- **Paper proof:** D1.1–D1.4, D1.6, D2.1–D2.3, D3.2–D3.4, D4.0–D4.3. These are written arguments without Lean certificates.
- **Conditional:** D1.5, with hypotheses (H1)–(H2) and the level hypothesis named there. It changes no benchmark.
- **External input:** Serre's CM identification of $\eta(12\tau)^2$ and of the three higher-weight eta products; Matomäki–Radziwiłł Corollary 1.2(ii) and Murty–Petersen Theorem 0.2 (through GF-43); Wirsing's theorem; Selberg's prime-pair bound (Halberstam–Richert Thm. 3.11); Brun–Titchmarsh; Turán–Kubilius; the Gauss–Kronecker–Hurwitz and Jacobi formulas; Legendre's three-square theorem; and, for D1.5 only, the Rosser–Iwaniec $\beta$-sieve.
- **Open:** everything listed under §§1.7, 3 and 4.

The benchmark statuses of `BC-29` and of the theta and Euler-power families are unchanged. Cross-model review of this note, if any, is not independent human peer review. A literature search finding nothing does not establish novelty. Lemma D4.0 and Proposition D3.3 are elementary and may be folklore.
