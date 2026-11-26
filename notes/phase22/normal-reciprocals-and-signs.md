# Exact periods, sharpened discrepancy rates, sign classification, and base-2 simple normality for reciprocals of kernel elements

Fix an integer radix $b\ge2$. For a real number $z$ write $x_n=\{b^nz\}\in[0,1)$, let $d_1d_2\cdots$ be its base-$b$ digits ($d_{n+1}=\lfloor bx_n\rfloor$), let $\mu_N^{\mathrm{emp}}(z)=\frac1N\sum_{n=0}^{N-1}\delta_{x_n}$ be the empirical measure on $\mathbb T=\mathbb R/\mathbb Z$, let $D_N(z)=D_N(z;b)$ be the extreme interval discrepancy of $x_0,\dots,x_{N-1}$, and put $D^-(z;b)=\liminf_{N\to\infty}D_N(z;b)$ and $D^+(z;b)=\limsup_{N\to\infty}D_N(z;b)$. Write $\|t\|=\min_{k\in\mathbb Z}|t-k|$, $e(t)=e^{2\pi it}$, $\lambda$ for Lebesgue measure on $\mathbb T$, and $K_b=\{z\in\mathbb R:\ D_N(z;b)\to1\}$ for the numerical translation kernel. For a word $w=w_1\cdots w_L\in\{0,\dots,b-1\}^L$, let $f_w(N;z)=\frac1N\#\{0\le n<N:\ d_{n+1}\cdots d_{n+L}=w\}$.

Phase 21 ([`euler-scalings-and-reciprocals.md`](../phase21/euler-scalings-and-reciprocals.md), §5) proved that for an admissible exponent sequence $(m_k)$ with $T_k=\operatorname{ord}_{D_k}(b)\mid m_{k+1}$ and $\omega_k=m_{k+1}/T_k\to\infty$, the kernel element $x=\prod_{k\ge1}(1-b^{-m_k})\in K_b$ has a base-$b$ normal reciprocal $y=1/x=\prod_{k\ge1}(1-b^{-m_k})^{-1}$, whereas flipping the signs to $x'=\prod_{k\ge1}(1+b^{-m_k})$ forces $\limsup D_N(1/x';b)\ge\tfrac12$. This note resolves the exact arithmetic, quantitative, measure-theoretic, and digit-frequency structure of this reciprocal family and its cyclotomic generalizations.

## Main results

For a sign sequence $\varepsilon=(\varepsilon_1,\varepsilon_2,\dots)\in\{-1,+1\}^{\mathbb N}$ and strictly increasing positive integers $m_1<m_2<\cdots$, put

```math
x(\varepsilon)=\prod_{k\ge1}\bigl(1+\varepsilon_k b^{-m_k}\bigr),\qquad y(\varepsilon)=\frac1{x(\varepsilon)}=\lim_{k\to\infty}R_k(\varepsilon),\qquad R_k(\varepsilon)=\prod_{j=1}^k\frac{b^{m_j}}{b^{m_j}+\varepsilon_j},
```

with $R_0(\varepsilon)=1$, $D_0(\varepsilon)=1$, $D_k(\varepsilon)=\prod_{j=1}^k(b^{m_j}+\varepsilon_j)$, and $T_k(\varepsilon)=\operatorname{ord}_{D_k(\varepsilon)}(b)$ ($T_0(\varepsilon)=1$). Since $\gcd(b,b^{m_j}+\varepsilon_j)=1$ for every $j\ge1$, $D_k(\varepsilon)$ is the exact reduced denominator of $R_k(\varepsilon)$ and $\gcd(b,D_k(\varepsilon))=1$. Call $(m_k)$ **sign-admissible** for $\varepsilon$ if

```math
\text{(A1)}\quad T_{k-1}(\varepsilon)\mid m_k\quad(k\ge1),\qquad\qquad \text{(A2)}\quad \omega_k:=\frac{m_{k+1}}{T_k(\varepsilon)}\to\infty.
```

**Theorem 1 (exact period identity and Hull–Dobell lifting).** Let $b\ge2$, $m\ge1$, and $D\ge1$ be integers with $\gcd(b,D)=1$. Put $\operatorname{rad}^*(D)=2^{\mathbf 1[4\mid D]}\prod_{p\mid D}p$.

1. *(Minus sign, Hull–Dobell lifting.)* If $\operatorname{rad}^*(D)\mid(b^m-1)$ (in particular, whenever $D\mid(b^m-1)$, i.e., $\operatorname{ord}_D(b)\mid m$), then for every integer $s\ge1$,
   $$D\mid\frac{b^{sm}-1}{b^m-1}\iff D\mid s,$$
   and hence $\operatorname{ord}_{D(b^m-1)}(b)=mD$. Moreover, the partial geometric sums $S_i(b^m)=\sum_{j=0}^ib^{jm}\bmod D$ ($0\le i<D$) form a bijection onto $\mathbb Z/D\mathbb Z$.
2. *(Plus sign, linear period collapse.)* If $D\mid(b^m-1)$, then $\operatorname{ord}_{D(b^m+1)}(b)=2m$.
3. *(Exact signed periods.)* For every $b\ge2$, every $\varepsilon\in\{-1,+1\}^{\mathbb N}$, and every $k\ge1$ satisfying $T_{k-1}(\varepsilon)\mid m_k$,
   ```math
   T_k(\varepsilon)=\begin{cases} m_k\,D_{k-1}(\varepsilon) & \text{if }\varepsilon_k=-1,\\ 2m_k & \text{if }\varepsilon_k=+1. \end{cases}
   ```
   In particular, $T_k(\varepsilon)\ge m_k$ unconditionally, so (A1)–(A2) automatically imply $m_{k+1}/m_k\to\infty$.

**Theorem 2 (sharpened all-prefix discrepancy rates for all-minus reciprocals).** Suppose $\varepsilon\equiv-1$ and $(m_k)$ satisfies (A1)–(A2), with $y=\prod_{k\ge1}(1-b^{-m_k})^{-1}$. Let $K\ge3$, $m_K\le N\le m_{K+1}$, and $h\ge1$.

1. *(Sharpened Weyl bound.)* With $c_b(h)=2\log_b(64\pi h)+8$,
   ```math
   |W_h(N)|\le\frac{\gcd(h,D_{K-2})}{D_{K-2}}+\frac{T_{K-1}+3c_b(h)}{m_K}.
   ```
   (This drops the leading factor $3$ of Phase 21 Proposition D2.3 to $1$ via an exact partial-band inequality.)
2. *(Divisor-sum Erdős–Turán bound.)* Putting $H=\min(D_{K-2},\omega_{K-1})\ge1$ and $\tau(D)=\#\{d\ge1:d\mid D\}$,
   ```math
   D_N(y;b)\le\frac6{H+1}+\frac4\pi\,\frac{\tau(D_{K-2})(1+\ln H)}{D_{K-2}}+\frac4\pi\,\frac{1+\ln H}{\omega_{K-1}}+\frac{12}{\pi}\,\frac{c_b(H)(1+\ln H)}{m_K}.
   ```
   When $\omega_{K-1}\ge D_{K-2}$, this improves Phase 21's $D_{K-2}^{-1/2}$ bound to $D_{K-2}^{-1+o(1)}$, specifically
   $$D_N(y;b)\le D_{K-2}^{-1}\exp\biggl((1+o(1))\frac{\ln 2\cdot\ln D_{K-2}}{\ln\ln D_{K-2}}\biggr).$$
3. *(Exact grid bound at period multiples and matching Koksma lower bound.)* At every multiple $N=JT_K\le m_{K+1}$ ($J\ge1$), $D_N(y;b)\le D_{K-1}^{-1}+O_b(\frac{\ln N}{N})$ with no divisor-function loss. Conversely, $W_{D_{K-2}}(m_K)\to1$ and $D_{m_K}(y;b)\ge\frac{1-o(1)}{\pi D_{K-2}}$ as $K\to\infty$; hence the exponent $-1$ on $D_{K-2}$ in part 2 is sharp.

**Theorem 3 (balanced-multiplier rate in $N$ and universal barrier for admissible reciprocals).** Let $\varepsilon\equiv-1$ and $y=\prod_{k\ge1}(1-b^{-m_k})^{-1}$.

1. *(Balanced rate under $\omega_k=D_{k-1}$.)* Fix $m_1\ge2$, $m_2=\omega_1m_1$ ($\omega_1\ge2$), and set $\omega_k=D_{k-1}$, $m_{k+1}=\omega_kT_k=m_kD_{k-1}^2$ for $k\ge2$. Then for every fixed integer $r\ge1$ and every real $A>0$,
   ```math
   D_N(y;b)\le\frac1{\exp^{(r)}\bigl((\ln^{(r+1)}N)^A\bigr)}
   ```
   for all sufficiently large $N$. In particular, $D_N(y;b)=O_{b,A}((\ln N)^{-A})$ and $D_N(y;b)=O_{b,A}(\exp(-(\ln\ln N)^A))$ for every $A>0$.
2. *(Universal barrier across all admissible sequences.)* For **every** sequence $(m_k)$ satisfying (A1)–(A2) (regardless of $\omega_k$), every fixed integer $r\ge1$, and every $\varepsilon>0$,
   ```math
   D_N(y;b)>\frac1{\exp^{(r)}\bigl((\ln^{(r)}N)^\varepsilon\bigr)}
   ```
   holds for infinitely many $N$. In particular, neither $D_N(y;b)=O(N^{-c})$ nor $D_N(y;b)=O(\exp(-(\ln N)^c))$ can hold for any $c>0$ within the admissible family.

Parts 1 and 2 leave an explicit gap of one iterated logarithm between $\ln^{(r+1)}N$ and $\ln^{(r)}N$; whether $\omega_k=D_{k-1}$ is optimal inside the admissible family remains open (§8). Likewise, under the strictly wider Hull–Dobell divisibility condition $\operatorname{rad}^*(D_{k-1})\mid(b^{m_k}-1)$ with $m_{k+1}/T_k\to\infty$, Theorem 1(1) still yields $T_k=m_kD_{k-1}$ and the same growth lower bound $m_{k+1}\ge m_kD_{k-1}$, whereas both normality of $y$ and extending the Koksma barrier of part 2 to that relaxed family remain open (§3.2).

**Theorem 4 (complete sign classification of $y(\varepsilon)$).** Let $b\ge2$, $\varepsilon\in\{-1,+1\}^{\mathbb N}$, and let $(m_k)$ be sign-admissible for $\varepsilon$. Then $x(\varepsilon)\in K_b$ with $1-D_N(x(\varepsilon);b)\le N^{-1+o(1)}$, and the trailing $+1$-run lengths $r_k$ ($r_k=0$ if $\varepsilon_k=-1$, $r_k=r_{k-1}+1$ if $\varepsilon_k=+1$) with $R_{\max}(\varepsilon)=\limsup_{k\to\infty}r_k\in\{0,1,2,\dots,\infty\}$ completely classify $y(\varepsilon)$:

1. *(Eventually all $-1$, $R_{\max}(\varepsilon)=0$.)* $D_N(y(\varepsilon);b)\to0$ ($y(\varepsilon)$ is normal in base $b$), with unique weak\* limit measure $\{\lambda\}$.
2. *(Eventually all $+1$.)* $D_N(y(\varepsilon);b)\to1$, so **$y(\varepsilon)\in K_b$**, with unique weak\* limit measure $\{\delta_0\}$. For $\varepsilon\equiv+1$, sign-admissibility reduces to $2m_k\mid m_{k+1}$ and $m_{k+1}/(2m_k)\to\infty$ (e.g. $m_k=2^k k!$), requiring no tetration growth.
3. *(Infinitely many $-1$ and infinitely many $+1$, $1\le R_{\max}(\varepsilon)\le\infty$.)* With $2^{-\infty}=0$:
   - $D^-(y(\varepsilon);b)=0$ and $D^+(y(\varepsilon);b)=1-2^{-R_{\max}(\varepsilon)}$;
   - the exact set of limit points of $(D_N(y(\varepsilon);b))_{N\ge1}$ is the closed interval $[0,\,1-2^{-R_{\max}(\varepsilon)}]$;
   - the exact set of weak\* limit points of $(\mu_N^{\mathrm{emp}}(y(\varepsilon)))_{N\ge1}$ is $\{(1-\alpha)\lambda+\alpha\delta_0:\ 0\le\alpha\le1-2^{-R_{\max}(\varepsilon)}\}$.

**Theorem 5 (oriented digit frequencies and collapse of simple normality for $y(\varepsilon)$).** Under the hypotheses of Theorem 4, outside a set of indices of asymptotic density $0$, every concentration of $\mu_N^{\mathrm{emp}}(y(\varepsilon))$ near $0\in\mathbb T$ occurs strictly from above ($0^+$), including along all $-1$ transition shells. Consequently, for every length $L\ge1$:

- if $\varepsilon$ is eventually $+1$, then $f_{0^L}(N;y(\varepsilon))\to1$ and $f_w(N;y(\varepsilon))\to0$ for all $w\ne0^L$;
- if both $+1$ and $-1$ occur infinitely often, then
  ```math
  \liminf_{N\to\infty}f_0(N;y(\varepsilon))=\frac1b,\qquad \limsup_{N\to\infty}f_0(N;y(\varepsilon))=1-\frac{b-1}b\,2^{-R_{\max}(\varepsilon)}>\frac1b,
  ```
  and for every digit $d\ne0$, $\liminf f_d(N)=\frac1b 2^{-R_{\max}(\varepsilon)}$ and $\limsup f_d(N)=\frac1b$.

In particular, within the signed product family $y(\varepsilon)$, **simple normality in base $b$ is equivalent to full normality in base $b$** (even when $b=2$), and holds if and only if $\varepsilon_k=-1$ for all sufficiently large $k$.

**Theorem 6 (cyclotomic band family, base-2 simple normality of nonnormal reciprocals, and prescribed discrepancy spectrum).** For every integer $k\ge1$, define the palindromic cyclotomic polynomial

```math
P_k(q):=\frac{1+q^{2k+1}}{1+q}\cdot\frac{1+q^{2k+3}}{1+q}\in 1+q\mathbb Z[q]
```

of degree $4k+2$, and set $L_k=2(2k+1)(2k+3)$. Then $P_k(q)\mid\frac{1-q^{L_k}}{1-q}$, and the quotient $A_k(q)=\frac{1-q^{L_k}}{(1-q)P_k(q)}$ has zero internal zero coefficients, exactly $4k+2$ trailing zero-bands (exact density $\rho_k=\frac1{2k+3}$, all oriented $0^+$ with exact tail $\tau_{L_k-d}^{(k)}(q)=q^d/P_k(q)$), exactly $2(k+2)(2k+1)$ positive bands, exactly $2k(2k+1)$ negative bands (conditional sign expectation $\frac1{k+1}$), band values in $[-2k,2k+2]$, and series coefficients $1/P_k(q)=\sum_{s\ge0}c_s^{(k)}q^s$ with $|c_s^{(k)}|\le2$ uniformly in $k$. Using $P_k(b^{-m_k})$ yields:

1. *(Simply normal, maximally nonnormal reciprocal in base 2.)* For every base $b\ge2$, with $m_1=8$ and $m_{j+1}=b^{(j+1)^3}L_jm_j$, the irrational product $x=\prod_{j=1}^\infty P_j(b^{-m_j})$ satisfies $x\in K_b$ ($1-D_N(x;b)\le N^{-1+o(1)}$), and its reciprocal $y=1/x$ satisfies $y\in K_b$ ($D_N(y;b)\to1$) together with
   ```math
   \lim_{N\to\infty}f_{0^L}(N;y)=\lim_{N\to\infty}f_{(b-1)^L}(N;y)=\frac12,\qquad \lim_{N\to\infty}f_w(N;y)=0\quad(w\notin\{0^L,(b-1)^L\})
   ```
   for every $L\ge1$. In particular, for $b=2$, $y=1/x$ is **simply normal in base 2 yet maximally nonnormal ($y\in K_2$)**.
2. *(Every $\alpha\in[0,1]$ as prescribed upper discrepancy $D^+(1/x;b)=\alpha$, simultaneously simply normal in base 2.)* For every base $b\ge2$ and every real $\alpha\in[0,1]$, there is an explicit irrational $x\in K_b$ ($1-D_N(x;b)\le N^{-1+o(1)}$) whose reciprocal $y=1/x$ satisfies $D^-(y;b)=0$, $D^+(y;b)=\alpha$, exact discrepancy limit set $[0,\alpha]$, and exact weak\* limit measure set $\{(1-\gamma)\lambda+\gamma\delta_0:\ 0\le\gamma\le\alpha\}$. When $b=2$, this same $y=1/x$ is simultaneously **simply normal in base 2** ($f_0(N;y)\to\frac12$, $f_1(N;y)\to\frac12$ along all $N$).

| Result | Status |
|---|---|
| Theorem 1 (exact period identities $m_kD_{k-1}$ and $2m_k$, Hull–Dobell lifting) | **Kernel-verified** for $D\mid b^m-1$ and plus-sign $2m$ in [`RadixPowerTower.lean`](../../NormalityChecker/RadixPowerTower.lean) (`orderOf_mul_pow_sub_one`, `orderOf_mul_pow_add_one`); **Paper proof** for the wider Hull–Dobell $\operatorname{rad}^*(D)\mid b^m-1$ extension; 590 Hull–Dobell + 448 plus-sign + 72 signed-triple checks exact (`scripts/phase22_reciprocals.py`) |
| Theorem 2 (sharpened Weyl bound, divisor-sum Erdős–Turán, grid bound, Koksma lower bound) | **Paper proof** (self-contained); partial-band inequality, divisor-sum, grid, partial-band Weyl, and Koksma bounds checked (`scripts/phase22_reciprocals.py`) |
| Theorem 3 (balanced-multiplier rate $\exp^{(r)}((\ln^{(r+1)}N)^A)^{-1}$ and admissible-family barrier $\exp^{(r)}((\ln^{(r)}N)^\varepsilon)^{-1}$) | **Paper proof**; log-tower growth checked (`scripts/phase22_reciprocals.py`). Optimality of $\omega_k=D_{k-1}$ and barrier under relaxed Hull–Dobell are **Open** (§8) |
| Theorems 4–5 (complete sign classification of $y(\varepsilon)$, exact limit sets, oriented digit frequencies) | **Paper proof**; trajectories, sweeps, digit laws, and melting illustration checked across bases 2 and 3 (`scripts/phase22_reciprocals.py`) |
| Theorem 6 (closed form of $P_k$, base-2 simply normal reciprocal in $K_2$, prescribed $D^+=\alpha\in[0,1]$ with base-2 simple normality) | **Paper proof**; closed form checked for $k=1\dots25$, exact band and tail identities across bases $2,3,5,10$, $0^+/1^-$ mixing and prescribed $\alpha$ checked (`scripts/phase22_reciprocals.py`) |
| Convergent limit $\lim_{N\to\infty}D_N(1/x;b)=\alpha\in(0,1)$ for $x\in K_b$ | **Open** (§8) |
| Remaining Lean 4 finite cores (Hull–Dobell lifting, partial-band/divisor/grid bounds, cyclotomic band identity & sign counts) | Blueprints in §6; not yet kernel-checked |

---

## 1. Exact period identities and Hull–Dobell order lifting

We give a self-contained proof of Theorem 1, including the exact $p$-adic valuation lemma needed for lifting the exponent.

### 1.1 Self-contained LTE lemma

**Lemma 1.1 (Lifting the Exponent).** Let $p$ be a prime and let $q\ge2$ be an integer with $p\mid(q-1)$; if $p=2$, assume further that $4\mid(q-1)$. Then for every integer $s\ge1$,

```math
v_p\Bigl(\frac{q^s-1}{q-1}\Bigr)=v_p(s).
```

*Proof.* First, if $r\ge1$ satisfies $p\nmid r$, then since $q\equiv1\pmod p$,

```math
\frac{q^r-1}{q-1}=\sum_{j=0}^{r-1}q^j\equiv r\not\equiv0\pmod p,
```

so $v_p((q^r-1)/(q-1))=0$. Next, write $q=1+p^au$ with $a=v_p(q-1)\ge1$ (and $a\ge2$ when $p=2$) and $p\nmid u$. By the binomial theorem,

```math
\frac{q^p-1}{q-1}=\frac{(1+p^au)^p-1}{p^au}=p+\sum_{j=2}^{p-1}\binom pj p^{a(j-1)}u^{j-1}+p^{a(p-1)}u^{p-1}.
```

For $2\le j\le p-1$, $p\mid\binom pj$ and $a(j-1)\ge a\ge1$, so $p^2\mid\binom pj p^{a(j-1)}$. For the last term, if $p\ge3$ then $a(p-1)\ge2a\ge2$, while if $p=2$ then $a(p-1)=a\ge2$ by hypothesis. Hence $(q^p-1)/(q-1)\equiv p\pmod{p^2}$, giving $v_p((q^p-1)/(q-1))=1$ and $v_p(q^p-1)=a+1\ge2$ (preserving the hypothesis $4\mid(q^p-1)$ when $p=2$). Writing $s=p^tr$ with $p\nmid r$ and inducting on $t$ yields

```math
v_p\Bigl(\frac{q^{p^tr}-1}{q-1}\Bigr)=\sum_{i=0}^{t-1}v_p\Bigl(\frac{q^{p^{i+1}}-1}{q^{p^i}-1}\Bigr)+v_p\Bigl(\frac{(q^{p^t})^r-1}{q^{p^t}-1}\Bigr)=t+0=v_p(s).\qquad\square
```

### 1.2 Proof of Theorem 1

*Proof of Theorem 1(1).* Put $q=b^m\ge2$ and assume $\operatorname{rad}^*(D)\mid(q-1)$. First observe that for every integer $M\ge1$,

```math
(b^m-1)\mid(b^M-1)\iff m\mid M.
```

Indeed, writing $M=sm+r$ with $0\le r<m$ gives $b^M-1=b^r(b^{sm}-1)+(b^r-1)$. Since $(b^m-1)\mid(b^{sm}-1)$ and $0\le b^r-1<b^m-1$ (strictly, even in the boundary case $b=2,m=1$ where $r=0$ and $0<1$), divisibility holds iff $b^r-1=0$, i.e. $r=0$.

Now write $M=sm$ ($s\ge1$). Then $D(b^m-1)\mid(b^M-1)$ iff $D\mid\frac{q^s-1}{q-1}$. We check every prime power $p^e\parallel D$ ($e\ge1$):

- **Odd prime $p\mid D$:** $p\mid\operatorname{rad}^*(D)\mid(q-1)$, so Lemma 1.1 gives $v_p\bigl(\frac{q^s-1}{q-1}\bigr)=v_p(s)$, hence $p^e\mid\frac{q^s-1}{q-1}\iff p^e\mid s$.
- **$p=2$ and $e=1$ ($2\parallel D$):** $2\mid\operatorname{rad}^*(D)\mid(q-1)$, so $q$ is odd and $\frac{q^s-1}{q-1}=\sum_{j=0}^{s-1}q^j\equiv s\pmod2$, hence $2\mid\frac{q^s-1}{q-1}\iff 2\mid s$.
- **$p=2$ and $e\ge2$ ($4\mid D$):** $4\mid\operatorname{rad}^*(D)\mid(q-1)$, so Lemma 1.1 gives $v_2\bigl(\frac{q^s-1}{q-1}\bigr)=v_2(s)$, hence $2^e\mid\frac{q^s-1}{q-1}\iff 2^e\mid s$.

Multiplying over all prime powers $p^e\parallel D$ gives $D\mid\frac{q^s-1}{q-1}\iff D\mid s$. Thus for all $M\ge1$, $D(b^m-1)\mid(b^M-1)\iff mD\mid M$. Since $D(b^m-1)\ge1$ and $\gcd(b,D(b^m-1))=1$, the least positive such $M$ is $\operatorname{ord}_{D(b^m-1)}(b)=mD$. (When $D(b^m-1)=1$, i.e. $b=2,m=1,D=1$, $\operatorname{ord}_1(2)=1=mD$ holds as well.)

For the bijection claim, note $S_i(q)=\sum_{j=0}^iq^j=\frac{q^{i+1}-1}{q-1}$. For $0\le i_1<i_2<D$,

```math
S_{i_2}(q)-S_{i_1}(q)=q^{i_1+1}\,\frac{q^{i_2-i_1}-1}{q-1}.
```

Since $\gcd(q,D)=1$, $D\mid(S_{i_2}(q)-S_{i_1}(q))\iff D\mid\frac{q^{i_2-i_1}-1}{q-1}\iff D\mid(i_2-i_1)$, impossible for $0<i_2-i_1<D$. Hence $\{S_i(q)\bmod D:\ 0\le i<D\}$ consists of $D$ distinct residues, so it is a bijection onto $\mathbb Z/D\mathbb Z$. (This is the Hull–Dobell full-period theorem for the linear congruential generator $S_{i+1}\equiv qS_i+1\pmod D$.)

*Sharpness of the 2-adic condition.* If $4\mid D$ and $v_2(q-1)=1$ (so $q\equiv3\pmod4$), then $v_2(q^2-1)=v_2(q-1)+v_2(q+1)\ge1+2=3$, giving extra 2-adic divisibility and strictly smaller order: for $(b,m,D)=(3,1,4)$, $D(b^m-1)=8$ has $\operatorname{ord}_8(3)=2<4=mD$. Under the admissibility condition $D\mid(b^m-1)$, however, $4\mid D$ automatically forces $4\mid(b^m-1)$, so every prime-power case is covered automatically.

*Proof of Theorem 1(2).* Assume $D\mid(b^m-1)$. Since $b^{2m}-1=(b^m-1)(b^m+1)$, we immediately have $D(b^m+1)\mid(b^{2m}-1)$, so $\operatorname{ord}_{D(b^m+1)}(b)\mid2m$. Conversely, suppose $(b^m+1)\mid(b^M-1)$ with $M\ge1$, and write $M=2ms+r$ with $0\le r<2m$. Because $b^{2m}\equiv1\pmod{b^m+1}$, we have $(b^m+1)\mid(b^r-1)$.

- If $0<r<m$, then $0<b^r-1<b^m-1<b^m+1$, impossible.
- If $r=m$, then $b^m-1=(b^m+1)-2\equiv-2\pmod{b^m+1}$; since $b\ge2$ and $m\ge1$, $b^m+1\ge3>2$, so $(b^m+1)\nmid(-2)$.
- If $m<r<2m$, write $r=m+t$ with $1\le t<m$. Then $b^r-1=b^tb^m-1\equiv-(b^t+1)\pmod{b^m+1}$, and $0<b^t+1\le b^{m-1}+1<b^m+1$, impossible.

Hence $r=0$, so $2m\mid M$. Therefore $\operatorname{ord}_{D(b^m+1)}(b)=2m$.

*Proof of Theorem 1(3).* For $k\ge1$, $D_k(\varepsilon)=D_{k-1}(\varepsilon)(b^{m_k}+\varepsilon_k)$ is the exact reduced denominator of $R_k(\varepsilon)$ because $\gcd(b,b^{m_j}+\varepsilon_j)=1$ for all $j\le k$. Since $T_{k-1}(\varepsilon)\mid m_k$, we have $D_{k-1}(\varepsilon)\mid(b^{m_k}-1)$ (trivially at $k=1$ since $D_0(\varepsilon)=1$). Applying part 1 (when $\varepsilon_k=-1$) and part 2 (when $\varepsilon_k=+1$) with $D=D_{k-1}(\varepsilon)$ and $m=m_k$ gives the stated formula for $T_k(\varepsilon)$. Since $D_{k-1}(\varepsilon)\ge1$ and $2m_k>m_k$, we have $T_k(\varepsilon)\ge m_k$ in both cases, so $m_{k+1}/m_k=\omega_kT_k(\varepsilon)/m_k\ge\omega_k\to\infty$. $\square$

---

## 2. Sharpened Weyl, divisor-sum, and Koksma bounds

Throughout Sections 2 and 3, take $\varepsilon\equiv-1$, so $R_k=\prod_{j=1}^k(1-b^{-m_j})^{-1}$, $D_k=\prod_{j=1}^k(b^{m_j}-1)$, $T_k=m_kD_{k-1}$, and $y=\prod_{k\ge1}(1-b^{-m_k})^{-1}$. Since $m_1<m_2<\cdots$, we have $R_k<\prod_{j\ge1}(1-2^{-j})^{-1}<4$ for every $k\ge0$, and $|y-R_K|\le32b^{-m_{K+1}}$ for every $K\ge1$ (in fact $\le16b^{-m_{K+1}}$ whenever $m_{K+1}\ge3$).

### 2.1 Four finite lemmas

**Lemma 2.1 (exact partial-band inequality).** For all integers $d'\ge1$, $I\ge1$, $m\ge1$, and $0\le r_0<m$,

```math
m\left\lfloor\frac{I}{d'}\right\rfloor + r_0\,\mathbf 1\bigl[d'\mid(I+1)\bigr]\ \le\ \frac{Im+r_0}{d'}.
```

*Proof.* If $d'\nmid(I+1)$, the left side is $m\lfloor I/d'\rfloor\le Im/d'\le(Im+r_0)/d'$. If $d'\mid(I+1)$, write $I+1=qd'$ with $q\ge1$. Then $\lfloor I/d'\rfloor=q-1$, so

```math
d'\bigl(m(q-1)+r_0\bigr)-(Im+r_0)=d'\bigl(m(q-1)+r_0\bigr)-\bigl((qd'-1)m+r_0\bigr)=(d'-1)(r_0-m)\le0,
```

because $d'\ge1$ and $r_0<m$. $\square$

**Lemma 2.2 (divisor-sum bound).** For all integers $D\ge1$ and $H\ge1$, putting $\tau_{\le H}(D)=\#\{d\mid D:\ d\le H\}$ and $H_n=\sum_{j=1}^n\frac1j$,

```math
\sum_{h=1}^H\frac{\gcd(h,D)}{h}\ \le\ \sum_{\substack{d\mid D\\ d\le H}}H_{\lfloor H/d\rfloor}\ \le\ \tau_{\le H}(D)(1+\ln H)\ \le\ \tau(D)(1+\ln H).
```

*Proof.* Group $h\in\{1,\dots,H\}$ by $d=\gcd(h,D)$, writing $h=dj$ with $1\le j\le\lfloor H/d\rfloor$ and $\gcd(j,D/d)=1$. Dropping the coprimality condition gives

```math
\sum_{h=1}^H\frac{\gcd(h,D)}{h}=\sum_{\substack{d\mid D\\ d\le H}}\sum_{\substack{1\le j\le H/d\\ \gcd(j,D/d)=1}}\frac1j\ \le\ \sum_{\substack{d\mid D\\ d\le H}}H_{\lfloor H/d\rfloor}\ \le\ \sum_{\substack{d\mid D\\ d\le H}}(1+\ln(H/d))\ \le\ \tau_{\le H}(D)(1+\ln H).\qquad\square
```

**Lemma 2.3 (elementary Wigert bound on $\tau(D)$).** As $D\to\infty$,

```math
\tau(D)\le\exp\biggl(\frac{\ln 2\cdot\ln D}{\ln\ln D}\Bigl(1+O\Bigl(\frac{\ln\ln\ln D}{\ln\ln D}\Bigr)\Bigr)\biggr)=D^{o(1)}.
```

*Proof.* For all sufficiently large $D$ (for instance $D\ge e^{e^5}$, where $P\ge e^5/125>1$), set $P=\frac{\ln D}{(\ln\ln D)^3}>1$. Write $D=\prod_{p^a\parallel D}p^a$. For primes $p\le P$, there are at most $P$ such primes and each has $a+1\le1+\log_2D$, so $\ln\prod_{p\le P}(a+1)\le P\ln(1+\log_2D)=O\bigl(\frac{\ln D}{(\ln\ln D)^2}\bigr)$. For primes $p>P$, $a+1\le2^a=(P^a)^{\ln 2/\ln P}<(p^a)^{\ln 2/\ln P}$, so multiplying over $p>P$ gives $\prod_{p>P}(a+1)\le D^{\ln 2/\ln P}$. Since $\ln P=\ln\ln D-3\ln\ln\ln D$, combining the two factors gives the claim. $\square$

**Lemma 2.4 (shifted-grid discrepancy and elementary Koksma lower bound).**

1. For any integer $D\ge1$ and $\alpha\in\mathbb T$, let $U_D(\alpha)=\frac1D\sum_{j=0}^{D-1}\delta_{\{\alpha+j/D\}}$. Then $D(U_D(\alpha))=\frac1D$, and its circular Wasserstein-1 distance to $\lambda$ is $W_1(U_D(\alpha),\lambda)=\frac1{4D}$.
2. For any finite sequence $x_0,\dots,x_{N-1}\in[0,1)$ with extreme interval discrepancy $D_N$ and Weyl sums $W_h(N)=\frac1N\sum_{n=0}^{N-1}e(hx_n)$ ($h\ge1$),
   ```math
   |W_h(N)|\le\pi h\,D_N,\qquad\text{so}\qquad D_N\ge\frac{|W_h(N)|}{\pi h}.
   ```

*Proof.* (1) Every arc $J\subset\mathbb T$ of length $\ell$ contains either $\lfloor D\ell\rfloor$ or $\lceil D\ell\rceil$ points of $\alpha+\frac1D\mathbb Z/\mathbb Z$, so $|U_D(\alpha)(J)-\ell|\le\frac1D$ (attained on open arcs of length $1/D$ between adjacent grid points). Transporting each interval $[\alpha+\frac{j-1/2}D,\alpha+\frac{j+1/2}D]$ to its midpoint $\alpha+j/D$ moves mass at average circular distance $\frac1{4D}$.

(2) Put $F_N(t)=\frac1N\#\{n<N:\ x_n<t\}$. For any $x\in[0,1)$, integration by parts yields

```math
\int_0^1(\mathbf 1_{x<t}-t)\,2\pi ih\,e(ht)\,dt=(e(h)-e(hx))-\Bigl(\bigl[te(ht)\bigr]_0^1-\int_0^1e(ht)\,dt\Bigr)=-e(hx).
```

Averaging over $n=0,\dots,N-1$ gives $W_h(N)=-2\pi ih\int_0^1(F_N(t)-t-c)\,e(ht)\,dt$ for every constant $c\in\mathbb R$ (since $\int_0^1e(ht)\,dt=0$). With $M_+=\sup_{[0,1]}(F_N(t)-t)$ and $M_-=\inf_{[0,1]}(F_N(t)-t)$, we have $D_N=M_+-M_-$. Setting $c=(M_++M_-)/2$ gives $|F_N(t)-t-c|\le D_N/2$ everywhere on $[0,1]$, hence $|W_h(N)|\le2\pi h\cdot\frac12D_N=\pi hD_N$. $\square$

### 2.2 Proof of Theorem 2

*Proof of Theorem 2(1).* Write $N=Im_K+r_0$ with $I\ge1$ and $0\le r_0<m_K$, and follow steps (1)–(3) of Phase 21 Proposition D2.3. Passing from $y$ to $R_K$ costs at most $c_b(h)$. Summing over the $I$ complete bands and the partial band $i=I$ (using `band_identity` and $T_{K-1}\mid m_K$) gives

```math
\sum_{n=0}^{N-1}e(hb^ny)=\sum_{a=1}^I m_K\,\widehat C_{K-1}(ha)+\Bigl\lfloor\frac{r_0}{T_{K-1}}\Bigr\rfloor T_{K-1}\,\widehat C_{K-1}(h(I+1))+O^*\bigl(T_{K-1}+(I+2)c_b(h)\bigr).
```

By Lemma D2.2 at level $K-1\ge2$, $\widehat C_{K-1}(ha)=0$ unless $d'\mid a$, where $d'=D_{K-2}/g$ and $g=\gcd(h,D_{K-2})$. Since $|\widehat C_{K-1}|\le1$ and $\lfloor r_0/T_{K-1}\rfloor T_{K-1}\le r_0$, the surviving main terms have total modulus at most

```math
m_K\left\lfloor\frac{I}{d'}\right\rfloor + r_0\,\mathbf 1\bigl[d'\mid(I+1)\bigr]\ \le\ \frac{Im_K+r_0}{d'}=\frac{g}{D_{K-2}}\,N
```

by Lemma 2.1. Dividing by $N\ge Im_K$ and using $\frac{T_{K-1}+(I+2)c_b(h)}{Im_K}\le\frac{T_{K-1}+3c_b(h)}{m_K}$ (since $I\ge1$) yields Theorem 2(1).

*Proof of Theorem 2(2).* Apply the Erdős–Turán inequality $D_N(y)\le\frac6{H+1}+\frac4\pi\sum_{h=1}^H\frac{|W_h(N)|}{h}$ with $H=\min(D_{K-2},\omega_{K-1})\ge1$. Insert Theorem 2(1), apply Lemma 2.2 to the first sum, and use $\sum_{h=1}^H\frac1h\le1+\ln H$ together with $T_{K-1}/m_K=1/\omega_{K-1}$ and $c_b(h)\le c_b(H)$ on the remaining sums. This gives the displayed inequality. When $\omega_{K-1}\ge D_{K-2}$, we have $H=D_{K-2}$ and $m_K=\omega_{K-1}m_{K-1}D_{K-2}\ge m_{K-1}D_{K-2}^2$, so the last term is $O_b((\ln D_{K-2})^2/(m_{K-1}D_{K-2}^2))$, and Lemma 2.3 gives $D_N(y;b)\le D_{K-2}^{-1}\exp((1+o(1))\frac{\ln 2\cdot\ln D_{K-2}}{\ln\ln D_{K-2}})$.

*Proof of Theorem 2(3).* For the complete period $\mu_K$ of $R_K$ ($T_K=m_KD_{K-1}$ by Theorem 1), Lemma D2.1 gives $b^{im_K+r}R_K\equiv\frac{(i+1)b^rA_{K-1}}{D_{K-1}}+\eta_r^{(K)}\pmod1$ for $0\le i<D_{K-1}$ and $0\le r<m_K$, where $\gcd(b^rA_{K-1},D_{K-1})=1$. Hence for each fixed $r$, the $D_{K-1}$ points $\{b^{im_K+r}R_K\bmod1:\ 0\le i<D_{K-1}\}$ are **identically** the shifted uniform grid $\eta_r^{(K)}+\frac1{D_{K-1}}\mathbb Z/\mathbb Z$. Thus

```math
\mu_K=\frac1{m_K}\sum_{r=0}^{m_K-1}U_{D_{K-1}}\bigl(\eta_r^{(K)}\bigr),
```

and by convexity and Lemma 2.4(1), $D(\mu_K)\le\frac1{D_{K-1}}$ and $W_1(\mu_K,\lambda)\le\frac1{4D_{K-1}}$ with zero tail error. For any $N=JT_K\le m_{K+1}$, $|b^ny-b^nR_K|\le32b^{n-m_{K+1}}\le32b^{n-N}$. Setting $L=\lceil\log_b(64N)\rceil$, all $n<N-L$ move by at most $\eta=\frac1{2N}$, while the last $L$ indices form fraction $\beta=L/N$. By the pointwise perturbation bound $|D(\mu_x)-D(\mu_y)|\le\beta+2\eta$ (Lemma 4.1 below),

```math
D_{JT_K}(y;b)\le D(\mu_K)+\frac{L+1}{N}\le\frac1{D_{K-1}}+O_b\Bigl(\frac{\ln N}{N}\Bigr).
```

For the lower bound at $N=m_K$, note $|y-R_{K-1}|\le32b^{-m_K}$, so replacing $y$ by $R_{K-1}$ changes $W_{D_{K-2}}(m_K)$ by at most $c_b(D_{K-2})/m_K$. Since $T_{K-1}\mid m_K$, the average of $e(D_{K-2}b^nR_{K-1})$ over $n<m_K$ equals $\widehat C_{K-1}(D_{K-2})$. By Lemma D2.1 at level $K-1$ and $D_{K-2}R_{K-2}\in\mathbb Z$, $D_{K-2}b^{jm_{K-1}+s}R_{K-1}\equiv D_{K-2}\eta_s^{(K-1)}\pmod1$, with $0<\eta_s^{(K-1)}\le8b^{s-m_{K-1}}$. Thus

```math
\bigl|\widehat C_{K-1}(D_{K-2})-1\bigr|\le\frac1{m_{K-1}}\sum_{s=0}^{m_{K-1}-1}\min\bigl(2,\,16\pi D_{K-2}b^{s-m_{K-1}}\bigr)\le\frac{c_b(D_{K-2})}{m_{K-1}}.
```

Because $m_{j+1}/m_j\to\infty$, we have $\log_b D_{K-2}<\sum_{j=1}^{K-2}m_j=(1+o(1))m_{K-2}=o(m_{K-1})$, so $c_b(D_{K-2})/m_{K-1}\to0$. Hence $W_{D_{K-2}}(m_K)\to1$, and Lemma 2.4(2) gives $D_{m_K}(y;b)\ge\frac{1-o(1)}{\pi D_{K-2}}$. $\square$

Numerically, comparing the main $D_{K-2}$ and $\omega_{K-1}$ Erdős–Turán terms at $\omega_{K-1}=D_{K-2}$ (omitting the $c_b(H)/m_K=O_b((\ln D_{K-2})^2/(m_{K-1}D_{K-2}^2))$ term), replacing Phase 21's $H=\lfloor\sqrt{D_{K-2}}\rfloor$ by Theorem 2(2) with $H=D_{K-2}$ tightens the bound from $5.58\times10^{-6}$ to $1.41\times10^{-8}$ ($395.2\times$) at $D_3^{\mathrm{bal}}=45(2^{36}-1)=3{,}092{,}376{,}453{,}075$ ($\tau=1152$, from the balanced base-2 sequence starting $(2,4,36,\dots)$), and from $8.73\times10^{-8}$ to $7.35\times10^{-12}$ ($11{,}865.6\times$) at Phase 21's $D_3=45(2^{48}-1)=12{,}666{,}373{,}951{,}979{,}475$ ($\tau=1920$, from $(2,4,48,43200,\dots)$).

---

## 3. Exact growth, balanced-multiplier rate in $N$, and universal barrier

By Theorem 1, (A1)–(A2) force the exact two-step exponential recursion

```math
m_{k+1}=\omega_k T_k=\omega_k m_k D_{k-1}\ge\omega_k m_k\bigl(b^{m_{k-1}}-1\bigr)\qquad(k\ge2).
```

This recursion couples even and odd indices into two interleaved exponential towers, which governs both the achieved balanced-multiplier rate and the universal lower barrier.

### 3.1 Proof of Theorem 3(1): balanced $\omega_k=D_{k-1}$

Set $m_1\ge2$, $m_2=\omega_1m_1$ ($\omega_1\ge2$), and $\omega_k=D_{k-1}$, $m_{k+1}=m_kD_{k-1}^2$ for all $k\ge2$. Since $D_1=b^{m_1}-1\ge3$, we have $m_{k+1}\ge9m_k$ for all $k\ge2$ and $m_{k+1}/m_k=D_{k-1}^2\to\infty$. Consequently $\sum_{j=1}^km_j=(1+o(1))m_k$, and

```math
\log_b D_k=\sum_{j=1}^k\log_b(b^{m_j}-1)=(1+o(1))m_k.
```

Put $a_k=\log_b m_k$. Then $a_{k+1}=a_k+2\log_b D_{k-1}=a_k+(2+o(1))m_{k-1}$. Since $a_k=\log_b(m_{k-1}D_{k-2}^2)\le\log_b m_{k-1}+4m_{k-2}=o(m_{k-1})$, we obtain

```math
a_{k+1}=(2+o(1))m_{k-1},\qquad \frac{a_{k+1}}{a_k}=(1+o(1))\frac{m_{k-1}}{m_{k-2}}=(1+o(1))D_{k-3}^2\to\infty.
```

Switching to natural logarithms, for any sequence $u_k=(c+o(1))m_j$ with $c>0$ we have $\ln u_k=(\ln b)\,a_j+O(1)=(2\ln b+o(1))m_{j-2}$. Inducting on any fixed integer $r\ge1$ as $K\to\infty$ gives

```math
\ln D_{K-2}=(\ln b+o(1))m_{K-2},\qquad \ln^{(r)}D_{K-2}=(2\ln b+o(1))m_{K-2r}\quad(r\ge2),
```

while for every $N\in[m_K,m_{K+1}]$ we have $\ln N\le(\ln b)\,a_{K+1}=(2\ln b+o(1))m_{K-1}$, and hence by induction on $r\ge1$,

```math
\ln^{(r+1)}N\le\ln^{(r+1)}m_{K+1}=(2\ln b+o(1))m_{K-2r-1}\qquad(r\ge1).
```

Now compare $m_j$ with $m_{j-1}^A$ for any fixed $A>0$ as $j\to\infty$:

```math
\log_b\frac{m_j}{m_{j-1}^A}=a_j-Aa_{j-1}=(2+o(1))m_{j-2}-A(2+o(1))m_{j-3}\to+\infty,
```

because $m_{j-2}/m_{j-3}\to\infty$. Applying this at $j=K-2r$ shows that for every fixed $r\ge1$ and every $A>0$,

```math
\frac{\ln^{(r)}D_{K-2}}{\bigl(\ln^{(r+1)}N\bigr)^A}\to+\infty
```

uniformly over $N\in[m_K,m_{K+1}]$. By Theorem 2(2), $D_N(y;b)\le D_{K-2}^{-1+o(1)}$ on $[m_K,m_{K+1}]$, so $\ln(1/D_N(y;b))\ge(1-o(1))\ln D_{K-2}$ and $\ln^{(r)}(1/D_N(y;b))\ge\ln^{(r)}D_{K-2}-o(1)$ for $r\ge2$. Therefore $D_N(y;b)\le\bigl(\exp^{(r)}((\ln^{(r+1)}N)^A)\bigr)^{-1}$ for all sufficiently large $N$. $\square$

**Heuristic comparison of Erdős–Turán upper bounds across multiplier regimes.** Comparing only our Theorem 2(2) upper bound across different choices of $\omega_k$ (this is a comparison of upper bounds, not a proof of optimality):

- *Sub-balanced $\omega_k\ll D_{k-1}$:* the term $(1+\ln\omega_{K-1})/\omega_{K-1}$ dominates Theorem 2(2). For $\omega_k=k+1$, $1/\omega_{K-1}=1/K\asymp1/\log^*N$. For Phase 21's $\omega_k=(k+1)m_k$, at $N=m_{K+1}$ one has $\ln N\asymp m_{K-1}$ and $\omega_{K-1}=Km_{K-1}\asymp(\log^*N)\ln N$, yielding $O\bigl(\frac{\ln\ln N}{(\log^*N)\ln N}\bigr)$.
- *Balanced $\omega_k=D_{k-1}$:* equalizes the two main upper-bound terms $D_{K-2}^{-1+o(1)}$ and $\omega_{K-1}^{-1+o(1)}$, achieving Theorem 3(1)'s bound $O(\exp^{(r)}((\ln^{(r+1)}N)^A)^{-1})$ for every $r\ge1$ and $A>0$.
- *Super-balanced $\omega_k\gg D_{k-1}$:* enlarging $\omega_k$ beyond $D_{k-1}$ leaves the window-$K$ bound at $D_{K-2}^{-1+o(1)}$ while pushing $m_{K+1}$ higher; for single-step exponential growth $m_{k+1}\asymp b^{m_k}$, at $N=m_{K+1}$ one has $\ln^{(3)}N\approx m_{K-2}\approx\log_bD_{K-2}$, reducing the upper bound back to $(\ln\ln N)^{-1}$.

### 3.2 Proof of Theorem 3(2): universal lower barrier and remark on relaxing (A1)

Let $(m_k)$ be **any** sequence satisfying (A1)–(A2). For all large $K$, we have $D_{K-2}<b^{2m_{K-2}}$ and $m_{K-1}/m_{K-2}=\omega_{K-2}D_{K-3}\to\infty$, so

```math
I_K:=\left\lfloor\frac{b^{m_{K-1}/8}}{96\,D_{K-2}}\right\rfloor\ge b^{m_{K-1}/8-3m_{K-2}}\ge1,\qquad N_K:=I_Km_K.
```

Since $I_K\le b^{m_{K-1}/8}<b^{m_{K-1}}-1\le D_{K-1}$, we have $m_K\le N_K<m_KD_{K-1}=T_K\le m_{K+1}$. Because $N_K=I_Km_K$ consists of $I_K$ complete bands of $R_K$ with no partial band,

```math
W_{D_{K-2}}(N_K)=\frac1{I_K}\sum_{a=1}^{I_K}\widehat C_{K-1}(aD_{K-2})+O^*\!\Bigl(\frac{2c_b(D_{K-2})}{m_K}\Bigr).
```

For each $1\le a\le I_K$, Lemma D2.1 at level $K-1$ and $D_{K-2}R_{K-2}\in\mathbb Z$ give $aD_{K-2}b^{jm_{K-1}+s}R_{K-1}\equiv aD_{K-2}\eta_s^{(K-1)}\pmod1$ with $0<\eta_s^{(K-1)}\le8b^{s-m_{K-1}}$. Setting $L_a=\lceil\log_b(8\pi aD_{K-2})\rceil$, the $L_a$ terms with $m_{K-1}-s\le L_a$ contribute at most $2L_a$, and the remaining geometric tail contributes at most $\sum_{j\ge0}2b^{-j}\le4$. Since $8\pi I_KD_{K-2}\le\frac{8\pi}{96}b^{m_{K-1}/8}<b^{m_{K-1}/8}$, we have $2L_a<\frac14m_{K-1}+2$, so

```math
\bigl|\widehat C_{K-1}(aD_{K-2})-1\bigr|\le\frac{2L_a+4}{m_{K-1}}<\frac14+\frac6{m_{K-1}}<\frac13
```

for all large $K$, uniformly in $1\le a\le I_K$. Since $2c_b(D_{K-2})/m_K=O(m_{K-2}/m_K)\to0$, we obtain $|W_{D_{K-2}}(N_K)|>\frac12$, and Lemma 2.4(2) gives

```math
D_{N_K}(y;b)>\frac1{2\pi D_{K-2}}\ge b^{-2m_{K-2}}\qquad(\text{all large }K),
```

while $N_K\ge I_K\ge b^{m_{K-1}/9}$, so $\ln N_K\ge\frac{\ln b}9m_{K-1}$.

Now fix $r\ge1$ and $\varepsilon>0$, and suppose for contradiction that $D_N(y;b)\le\bigl(\exp^{(r)}((\ln^{(r)}N)^\varepsilon)\bigr)^{-1}$ for all large $N$. Evaluating at $N=N_K$ gives $\exp^{(r)}((\ln^{(r)}N_K)^\varepsilon)<b^{2m_{K-2}}$.

- If $r=1$: $(\frac{\ln b}9m_{K-1})^\varepsilon\le(\ln N_K)^\varepsilon<2m_{K-2}\ln b$, so $m_{K-1}\le Cm_{K-2}^{1/\varepsilon}$ for all large $K$. Iterating twice yields $m_K\le C^{1+1/\varepsilon}m_{K-2}^{1/\varepsilon^2}$, contradicting $m_K\ge m_{K-1}D_{K-2}\ge b^{m_{K-2}}-1$.
- If $r\ge2$: put $u_k=\ln^{(r-1)}(m_k)$. Taking $\ln$ $r$ times gives $(\ln^{(r)}N_K)^\varepsilon<\ln^{(r-1)}((2\ln b)m_{K-2})\le2u_{K-2}$, while $\ln N_K\ge\frac{\ln b}9m_{K-1}$ implies $\ln^{(r)}N_K\ge\frac12u_{K-1}$ for all large $K$. Thus $u_{K-1}\le2^{1+1/\varepsilon}u_{K-2}^{1/\varepsilon}$ for all large $K$, and iterating twice gives $u_K\le C_\varepsilon u_{K-2}^{1/\varepsilon^2}$. On the other hand, $m_K\ge b^{m_{K-2}}-1\ge\frac12b^{m_{K-2}}$ gives $\ln m_K\ge\frac{\ln b}2m_{K-2}$, and applying $\ln^{(r-2)}$ yields $u_K\ge\frac{\ln b}2e^{u_{K-2}}$ (for $r=2$) or $u_K\ge e^{u_{K-2}}-O(1)$ (for $r\ge3$), contradicting $u_K\le C_\varepsilon u_{K-2}^{1/\varepsilon^2}$ as $u_{K-2}\to\infty$. $\square$

**Remark (relaxing (A1) to Hull–Dobell divisibility).** Without any divisibility hypothesis, the geometric expansion of $R_K=R_{K-1}\frac{b^{m_K}}{b^{m_K}-1}$ gives the exact algebraic identity

```math
b^{im_K+r}R_K=S_i(b^{m_K})\,b^rR_{K-1}+\frac{b^rR_{K-1}}{b^{m_K}-1},\qquad S_i(q)=\sum_{j=0}^iq^j.
```

If some prime $p\mid D_{K-1}$ has $q=b^{m_K}\not\equiv1\pmod p$, then $S_i(q)\equiv\frac{q^{i+1}-1}{q-1}\pmod p$ omits the residue class $\frac{-1}{q-1}\pmod p$ for every $i\ge0$ (and if $4\mid D_{K-1}$ with $q\equiv3\pmod4$, then $S_i(q)\bmod4$ alternates $1,0$). Thus Hull–Dobell divisibility $\operatorname{rad}^*(D_{K-1})\mid(b^{m_K}-1)$ is the exact necessary-and-sufficient condition for $i\mapsto S_i(b^{m_K})\bmod D_{K-1}$ to be bijective on $\mathbb Z/D_{K-1}\mathbb Z$ (Theorem 1(1)). Under Hull–Dobell divisibility, Theorem 1(1) proves that $T_K=\operatorname{ord}_{D_K}(b)=m_KD_{K-1}$ **still** holds, so requiring $m_{K+1}/T_K\to\infty$ forces the exact same growth lower bound $m_{K+1}\ge m_KD_{K-1}$. However, extending either normality of $y$ or the Koksma lower-bound barrier of Theorem 3(2) to the strictly wider Hull–Dobell family (where $D_{K-1}\nmid(b^{m_K}-1)$) is **open**: when a prime power dividing $b^{m_{K-1}}-1$ fails to divide $b^{m_K}-1$, the band multiplier $S_i(b^{m_K})\bmod(b^{m_{K-1}}-1)$ need not equal $i+1$, so the small-$a$ control of $\widehat C_{K-1}(aD_{K-2})$ in the proof of Theorem 3(2) does not apply directly.

---

## 4. Complete sign classification for $y(\varepsilon)$

Now let $\varepsilon=(\varepsilon_1,\varepsilon_2,\dots)\in\{-1,+1\}^{\mathbb N}$ be arbitrary, and assume $(m_k)$ is sign-admissible for $\varepsilon$. Since $m_1<m_2<\cdots$, we have $\frac13<\prod_{j\ge1}(1+2^{-j})^{-1}\le R_k(\varepsilon)\le\prod_{j\ge1}(1-2^{-j})^{-1}<4$ for every $k\ge0$. Expanding $\prod_{k>K}(1+\varepsilon_kb^{-m_k})^{-1}$ term by term and comparing with the all-minus series gives

```math
\bigl|y(\varepsilon)-R_K(\varepsilon)\bigr|\le 16\,b^{-m_{K+1}} \qquad(m_{K+1}\ge3).
```

Also, the subset-sum proof of Phase 21 Theorem D2(a) depends only on $m_{k+1}/m_k\to\infty$ (automatic from Theorem 1(3)) and holds for every $\varepsilon$, giving $1-D_N(x(\varepsilon);b)\le N^{-1+o(1)}$ and $x(\varepsilon)\in K_b$.

### 4.1 Discrepancy and circular Wasserstein-1 perturbation

Let $W_1(\mu,\nu)$ be the Wasserstein-1 (optimal transport) distance on $\mathbb T$ with respect to the circle metric $\|\cdot\|$: $W_1(\mu,\nu)=\inf_{(X,Y)}\mathbb E[\|X-Y\|]$ over couplings $(X,Y)$ of $\mu,\nu$. Note that $W_1$ is convex in each argument: $W_1(t\mu_1+(1-t)\mu_2,\,t\nu_1+(1-t)\nu_2)\le tW_1(\mu_1,\nu_1)+(1-t)W_1(\mu_2,\nu_2)$.

**Lemma 4.1 (perturbation and $W_1$-continuity of discrepancy).**

1. *(Pointwise perturbation.)* Let $\mu_x=\frac1N\sum_{n<N}\delta_{x_n}$ and $\mu_y=\frac1N\sum_{n<N}\delta_{y_n}$ on $\mathbb T$. If $\|x_n-y_n\|\le\eta$ for all $n\in G\subseteq\{0,\dots,N-1\}$ with $|G|\ge(1-\beta)N$, then $|D(\mu_x)-D(\mu_y)|\le\beta+2\eta$.
2. *($W_1$-continuity of $D$.)* For any Borel probability measures $\mu,\nu$ on $\mathbb T$, $|D(\mu)-D(\nu)|\le 2\sqrt{2\,W_1(\mu,\nu)}$.
3. *(Convex combinations with $\delta_0$.)* For every $\alpha\in[0,1]$, $D((1-\alpha)\lambda+\alpha\delta_0)=\alpha$. More generally, for every probability measure $\sigma$ on $\mathbb T$, $\alpha\le D((1-\alpha)\sigma+\alpha\delta_0)\le\alpha+(1-\alpha)D(\sigma)$.

*Proof.* (1) Recall $D(\mu)=\sup_{J\text{ arc}}(\mu(J)-|J|)$. For any arc $J$ of length $\ell$: if $\ell+2\eta\ge1$, then $\mu_x(J)-\ell\le1-\ell\le2\eta\le D(\mu_y)+\beta+2\eta$; otherwise enlarging $J$ by $\eta$ on both sides yields an arc $J_\eta$ of length $\ell+2\eta<1$ with $\mu_x(J)-\ell\le\mu_y(J_\eta)+\beta-(|J_\eta|-2\eta)\le D(\mu_y)+\beta+2\eta$. Symmetry gives the reverse bound.

(2) Let $(X,Y)$ be a coupling with $\mathbb E[\|X-Y\|]=w=W_1(\mu,\nu)$. For any $\eta>0$, Markov's inequality gives $\mathbb P(\|X-Y\|>\eta)\le w/\eta$. Repeating the arc enlargement of (1) gives $|D(\mu)-D(\nu)|\le2\eta+w/\eta$; minimizing at $\eta=\sqrt{w/2}$ yields $2\sqrt{2w}$.

(3) Taking arcs $(-\varepsilon,\varepsilon)$ with $\varepsilon\downarrow0$ gives $D((1-\alpha)\sigma+\alpha\delta_0)\ge\alpha$. For any arc $J$, $((1-\alpha)\sigma+\alpha\delta_0)(J)-|J|=(1-\alpha)(\sigma(J)-|J|)+\alpha(\delta_0(J)-|J|)\le(1-\alpha)D(\sigma)+\alpha$. Setting $\sigma=\lambda$ ($D(\lambda)=0$) gives equality. $\square$

### 4.2 Exact complete-period measure recursion

Let $\mu_K=\frac1{T_K(\varepsilon)}\sum_{t=0}^{T_K(\varepsilon)-1}\delta_{\{b^tR_K(\varepsilon)\}}$ be the complete-period empirical measure of $R_K(\varepsilon)$.

**Proposition 4.2 ($W_1$ measure recursion).** For every $K\ge1$ under (A1):

1. If $\varepsilon_K=-1$, then $\mu_K=\frac1{m_K}\sum_{r=0}^{m_K-1}U_{D_{K-1}(\varepsilon)}(\eta_r^{(K)})$, hence
   ```math
   D(\mu_K)\le\frac1{D_{K-1}(\varepsilon)},\qquad W_1(\mu_K,\lambda)\le\frac1{4D_{K-1}(\varepsilon)}.
   ```
2. If $\varepsilon_K=+1$, then
   ```math
   W_1\Bigl(\mu_K,\ \tfrac12\mu_{K-1}+\tfrac12\delta_0\Bigr)\le\frac4{m_K}.
   ```
3. Let $r_K\ge0$ be the trailing $+1$-run length ending at $K$ and put $K_0=K-r_K$. If $K_0\ge1$ (so $\varepsilon_{K_0}=-1$), then
   ```math
   W_1\bigl(\mu_K,\ 2^{-r_K}\lambda+(1-2^{-r_K})\delta_0\bigr)\le\min\Bigl(\frac{2^{-r_K}}{4D_{K_0-1}(\varepsilon)},\,\frac{2^{-r_K}}2\Bigr)+\sum_{j=0}^{r_K-1}\frac{2^{-j}\cdot4}{m_{K-j}}.
   ```
   If $K_0=0$ (all $\varepsilon_1=\dots=\varepsilon_K=+1$), then $W_1(\mu_K,\delta_0)\le 2^{-K-1}+\sum_{j=0}^{K-1}\frac{2^{-j}\cdot4}{m_{K-j}}$.

*Proof.* (1) Identical to Theorem 2(3): $\gcd(b^rA_{K-1},D_{K-1}(\varepsilon))=1$ holds for every sign pattern $\varepsilon_1,\dots,\varepsilon_{K-1}$, so every $\varepsilon_K=-1$ completely resets $\mu_K$ to an average of shifted $D_{K-1}(\varepsilon)$-point uniform grids.

(2) When $\varepsilon_K=+1$, Theorem 1(3) gives $T_K(\varepsilon)=2m_K$. By `signed_band_identity` (Phase 21 Proposition D2.5), for $0\le r<m_K$:

```math
b^rR_K(\varepsilon)\equiv b^rR_{K-1}(\varepsilon)-\eta_r^+\pmod1,\qquad b^{m_K+r}R_K(\varepsilon)\equiv+\eta_r^+\pmod1,
```

where $0<\eta_r^+=\frac{b^rR_{K-1}(\varepsilon)}{b^{m_K}+1}\le4b^{r-m_K}$. Since $T_{K-1}(\varepsilon)\mid m_K$, the unperturbed points $\{b^rR_{K-1}(\varepsilon):\ 0\le r<m_K\}$ have empirical measure identically equal to $\mu_{K-1}$. Coupling $b^rR_K(\varepsilon)$ to $b^rR_{K-1}(\varepsilon)$ on band $0$ and $b^{m_K+r}R_K(\varepsilon)$ to $0$ on band $1$ has total average transport cost at most

```math
\frac1{m_K}\sum_{r=0}^{m_K-1}4b^{r-m_K}=\frac4{m_K}\sum_{l=1}^{m_K}b^{-l}\le\frac4{(b-1)m_K}\le\frac4{m_K}.
```

(3) Unroll the contraction in (2) by induction on $r_K$ using convexity of $W_1$ and the trivial bound $W_1(\mu,\nu)\le\frac12$ (diameter of $\mathbb T$). $\square$

Both limits follow directly from Proposition 4.2(3): if $K_0\to\infty$, the right side is at most $\frac1{4D_{K_0-1}(\varepsilon)}+\frac8{m_{K_0+1}}\to0$; if $K_0$ stays bounded (so $\varepsilon$ is eventually $+1$ and $r_K\to\infty$), splitting the sum at $J=\lfloor r_K/2\rfloor$ gives $W_1(\mu_K,\delta_0)\le2^{-r_K}+\frac8{m_{K-J}}+8\cdot2^{-J}\to0$.

### 4.3 Exact all-prefix trajectory on $+1$ shells and $-1$ transition shells

Fix $K\ge2$ and any $N\in[m_K,m_{K+1}]$, writing $N=Im_K+r_0$ with $I\ge1$ and $0\le r_0<m_K$. Since $|y(\varepsilon)-R_K(\varepsilon)|\le16b^{-m_{K+1}}$, passing from $y(\varepsilon)$ to $R_K(\varepsilon)$ on $0\le n<N\le m_{K+1}$ moves the empirical measure by

```math
W_1\bigl(\mu_N^{\mathrm{emp}}(y(\varepsilon)),\ \mu_N^{\mathrm{emp}}(R_K(\varepsilon))\bigr)\le\frac1N\sum_{l=1}^N16b^{-l}\le\frac{16}{m_K}.
```

We now evaluate $\mu_N^{\mathrm{emp}}(R_K(\varepsilon))$ on both shell types.

**Proposition 4.3 (exact trajectory on a $+1$ shell).** Suppose $\varepsilon_K=+1$, and let $\theta_K(N)=\frac1N\#\{0\le n<N:\ \lfloor n/m_K\rfloor\text{ is even}\}$. Then $\theta_K(N)\in[\frac12,1]$ for every $N\ge m_K$ (with $\theta_K(m_K)=1$, $\theta_K(2Jm_K)=\frac12$, and $\theta_K(N)=m_K/N$ sweeping $[\frac12,1]$ in steps $\le1/m_K$ on $[m_K,2m_K]$), and

```math
W_1\Bigl(\mu_N^{\mathrm{emp}}(y(\varepsilon)),\ \theta_K(N)\mu_{K-1}+\bigl(1-\theta_K(N)\bigr)\delta_0\Bigr)\le\frac{24}{m_K}+\frac1{2\omega_{K-1}}.
```

*Proof.* Every complete even band ($0\le i<I$, $i$ even) is within $W_1\le4/m_K$ of $\mu_{K-1}$, and every complete odd band is within $W_1\le4/m_K$ of $\delta_0$. In the partial band $i=I$ ($0\le r<r_0$), if $I$ is odd all points lie within $\eta_r^+$ of $\delta_0$ (total cost $\le4$); if $I$ is even, writing $r_0=qT_{K-1}(\varepsilon)+u$ with $0\le u<T_{K-1}(\varepsilon)$, the first $qT_{K-1}(\varepsilon)$ points couple to $\mu_{K-1}$ at total cost $\le4$ and the remaining $u$ points have weight $<T_{K-1}(\varepsilon)/m_K=1/\omega_{K-1}$ (contributing $\le\frac1{2\omega_{K-1}}$ to $W_1$). Combining with the $16/m_K$ approximation cost yields the bound. Finally, every complete pair of bands $(2j,2j+1)$ contributes equal weight to even and odd bands while any partial pair begins with an even band, so $\frac12\le\theta_K(N)\le1$. $\square$

**Proposition 4.4 (exact Kronecker melting on a $-1$ transition shell).** Suppose $\varepsilon_K=-1$, let $r=r_{K-1}\ge0$ be the trailing $+1$-run length before $K$, and suppose $K_0=K-1-r\ge2$ (so $\varepsilon_{K_0}=-1$ and $\varepsilon_{K_0+1}=\dots=\varepsilon_{K-1}=+1$). For $N=Im_K+r_0\in[m_K,m_{K+1}]$, put

```math
\beta_u(I):=\min\Bigl(1,\ \max\Bigl(0,\ \frac{\log_b I}{m_u}\Bigr)\Bigr),\qquad \alpha_K(N):=\sum_{u=K_0+1}^{K-1}2^{-(K-u)}\bigl(1-\beta_u(I)\bigr)\in\bigl[0,\,1-2^{-r}\bigr].
```

Then as $K_0\to\infty$, uniformly over all $N\in[m_K,m_{K+1}]$ (and even if $r$ varies),

```math
W_1\Bigl(\mu_N^{\mathrm{emp}}(y(\varepsilon)),\ \bigl(1-\alpha_K(N)\bigr)\lambda+\alpha_K(N)\delta_0\Bigr)\longrightarrow 0.
```

*Proof.* Dropping $\eta_r^{(K)}$ on all bands of $R_K(\varepsilon)$ and dropping the incomplete cycle $r_0\bmod T_{K-1}(\varepsilon)$ inside the partial band $i=I$ incurs $W_1$-error at most $\frac{24}{m_K}+\frac1{2\omega_{K-1}}\to0$. The remaining empirical measure $\widetilde\mu_N$ is the convex combination $\frac{m_K}M\sum_{a=1}^Ia_*\mu_{K-1}+\frac{r_0'}M(I+1)_*\mu_{K-1}$ where $r_0'=\lfloor r_0/T_{K-1}\rfloor T_{K-1}<m_K$ and $M=Im_K+r_0'$.

Since $T_u(\varepsilon)=2m_u\mid m_{u+1}$ for every $u\in\{K_0+1,\dots,K-1\}$, we partition $\{0,\dots,T_{K-1}(\varepsilon)-1\}$ into $r+1$ disjoint strata according to the **highest** level $u\in\{K_0+1,\dots,K-1\}$ at which $t$ lies in an odd band of $m_u$:

- $E_2=\{t:\ \lfloor t/m_u\rfloor\text{ is even for all }u\in\{K_0+1,\dots,K-1\}\}$, of exact density $2^{-r}$;
- $E^{(u)}=\{t:\ \lfloor t/m_u\rfloor\text{ is odd, and }\lfloor t/m_v\rfloor\text{ is even for all }v>u\}$ ($u=K_0+1,\dots,K-1$), of exact density $2^{-(K-u)}$.

This decomposes $\widetilde\mu_N=2^{-r}\sigma^{(2)}+\sum_{u=K_0+1}^{K-1}2^{-(K-u)}\sigma^{(u)}$, where each $\sigma^{(\cdot)}$ is the weighted average over $a$ of $a_*$ applied to the uniform measure on the corresponding stratum.

*Step 1: $W_1(\sigma^{(2)},\lambda)\to0$ uniformly in $I\ge1$.* For $t\in E_2$, iterating `signed_band_identity` down from $K-1$ to $K_0+1$ and noting that $T_{K_0}\mid m_{K_0+1}$ gives the exact telescoping identity

```math
b^tR_{K-1}(\varepsilon)\equiv b^tR_{K_0}(\varepsilon)-\sum_{u=K_0+1}^{K-1}\frac{b^{t\bmod m_u}R_{u-1}(\varepsilon)}{b^{m_u}+1}\pmod1. \tag{4.1}
```

Set $H=\min\bigl(D_{K_0-1}(\varepsilon),\,\lfloor m_{K_0+1}/m_{K_0}\rfloor\bigr)\to\infty$ (note $H<D_{K_0}(\varepsilon)$ for large $K_0$). Fix $1\le h\le H$ and split into two overlapping regimes of $I$:

- *Regime 1 ($I\le D_{K_0}(\varepsilon)^2$):* For every $1\le a\le I+1$, $ha\le D_{K_0}(\varepsilon)^3+D_{K_0}(\varepsilon)$, so $c_b(ha)=O(m_{K_0})$. On $E_2$, the condition for level $s\ge u$ depends only on $\lfloor t/m_u\rfloor$ while $t\bmod m_u$ varies over a subset of $[0,m_u)$ of density $2^{-(u-1-K_0)}$. Bounding each tail sum over all $v\in[0,m_u)$ gives
  ```math
  \frac1{|E_2|}\sum_{t\in E_2}\Bigl|e(hab^tR_{K-1})-e(hab^tR_{K_0})\Bigr|\le\sum_{u=K_0+1}^{K-1}\frac{2^{u-1-K_0}c_b(ha)}{m_u}\le\frac{2c_b(ha)}{m_{K_0+1}}=O_b\Bigl(\frac{m_{K_0}}{m_{K_0+1}}\Bigr),
  ```
  where the geometric sum collapses because $2m_u/m_{u+1}=1/\omega_u\le\frac12$ for all large $K_0$ (independent of $r$). Since $E_2$ is an exact union of complete periods of $R_{K_0}$ and $\varepsilon_{K_0}=-1$, Lemma D2.2 at level $K_0$ plus Lemma 2.1 gives
  ```math
  |\widehat\sigma^{(2)}(h)|\le\frac{\gcd(h,D_{K_0-1}(\varepsilon))}{D_{K_0-1}(\varepsilon)}+O_b\Bigl(\frac{m_{K_0}}{m_{K_0+1}}\Bigr).
  ```
- *Regime 2 ($I>D_{K_0}(\varepsilon)^2$):* Put $L_0=\lceil4m_{K_0}\rceil+6$ and $L_u=L_0+(u-K_0-1)$. Outside the exceptional subset of $t\in E_2$ where $t\bmod m_u\ge m_u-L_u$ for some $u>K_0$—whose proportion in $E_2$ is at most $\sum_{u>K_0}\frac{2^{u-1-K_0}L_u}{m_u}=O(m_{K_0}/m_{K_0+1})$—we have by (4.1) that $\|b^tR_{K-1}-b^tR_{K_0}\|\le\sum_{u>K_0}4b^{-L_u}\le8b^{-L_0}\le\frac1{4D_{K_0}(\varepsilon)^2}$. For every $t$, $y_t=\{b^tR_{K_0}\}=\frac{b^tA_{K_0}}{D_{K_0}}\bmod1$ has $\gcd(b^tA_{K_0},D_{K_0})=1$, and since $1\le h<D_{K_0}(\varepsilon)$, $\|hy_t\|\ge\frac1{D_{K_0}(\varepsilon)}$ holds for **every** $t$. Hence $\|hb^tR_{K-1}\|\ge\frac3{4D_{K_0}(\varepsilon)}$. Reversing the order of summation over $a=1,\dots,I$ and $t\in E_2$, the Kronecker geometric sum bound $|\frac1I\sum_{a=1}^Ie(a\theta)|\le\frac1{2I\|\theta\|}$ plus the partial-band weight $r_0'/M\le1/I$ gives
  ```math
  |\widehat\sigma^{(2)}(h)|\le\frac{2D_{K_0}(\varepsilon)}{3I}+\frac1I+O_b\Bigl(\frac{m_{K_0}}{m_{K_0+1}}\Bigr)\le\frac2{D_{K_0}(\varepsilon)}+O_b\Bigl(\frac{m_{K_0}}{m_{K_0+1}}\Bigr).
  ```

Applying Erdős–Turán with Lemma 2.2 over $1\le h\le H$ in both regimes shows $D(\sigma^{(2)})\to0$, hence $W_1(\sigma^{(2)},\lambda)\to0$ uniformly in $I\ge1$.

*Step 2: $W_1(\sigma^{(u)},\,\beta_u(I)\lambda+(1-\beta_u(I))\delta_0)\to0$ for each $u\in\{K_0+1,\dots,K-1\}$.* For $t\in E^{(u)}$, telescoping from $K-1$ down to $u$ gives

```math
b^tR_{K-1}(\varepsilon)\equiv+\frac{b^{r_u}R_{u-1}(\varepsilon)}{b^{m_u}+1}-\sum_{v=u+1}^{K-1}\frac{b^{r_v}R_{v-1}(\varepsilon)}{b^{m_v}+1}\pmod1, \tag{4.2}
```

where $r_s=t\bmod m_s$. Because $E^{(u)}$ constrains only $\lfloor t/m_v\rfloor$ for $v\ge u$ and $2m_u\mid m_v$ for all $v>u$, the residue $r_u$ is **exactly uniform** on $\{0,1,\dots,m_u-1\}$ over $E^{(u)}$. Excluding the edge set where $r_v\ge m_v-2m_u-6$ for some $v>u$ (proportion $\le\sum_{v>u}\frac{2^{v-u}(2m_u+6)}{m_v}=O(m_u/m_{u+1})=o(1)$), the higher-level sum is $\le8b^{-2m_u-6}\ll\frac14b^{-m_u}\le\frac{b^{r_u}R_{u-1}}{b^{m_u}+1}$, so $x_t=\{b^tR_{K-1}(\varepsilon)\}$ lies strictly in $(\frac14b^{r_u-m_u},\,4b^{r_u-m_u})$ for all $r_u<m_u-3$.

Set $\Delta_u=\lceil\sqrt{m_u}\rceil$ and $r_*=m_u-\lfloor\log_bI\rfloor$, and denote $\kappa_I(x)=\frac1I\sum_{a=1}^I\delta_{\{ax\}}$.

- For $0\le r_u<r_*-\Delta_u$ (proportion $1-\beta_u(I)-O(m_u^{-1/2})$): $Ix_t\le4Ib^{r_u-m_u}\le4b^{-\Delta_u}$, so every point of $\kappa_I(x_t)$ lies in $(0,4b^{-\Delta_u})$, giving $W_1(\kappa_I(x_t),\delta_0)\le4b^{-\Delta_u}$.
- For $r_*+\Delta_u<r_u<m_u-\Delta_u$ (proportion $\beta_u(I)-O(m_u^{-1/2})$): take $H_u=\lfloor b^{\Delta_u/2}/16\rfloor$. For every $1\le h\le H_u$, $hx_t\le4H_ub^{-\Delta_u}\le\frac14b^{-\Delta_u/2}<\frac12$, so $\|hx_t\|=hx_t\ge\frac14b^{r_u-m_u}$ and $|\widehat{\kappa_I(x_t)}(h)|\le\frac1{2I\|hx_t\|}\le2b^{-\Delta_u}$. By Erdős–Turán, $D(\kappa_I(x_t))=O(b^{-\Delta_u/2})\to0$, hence $W_1(\kappa_I(x_t),\lambda)\to0$.
- The remaining $r_u$ lie in buffer intervals of total proportion $\le(3\Delta_u+4)/m_u=O(m_u^{-1/2})$.

Finally, for the partial band $a=I+1$ (weight $r_0'/M\le1/I$): if $I\ge\sqrt{m_u}$, its total weight is $\le m_u^{-1/2}\to0$; if $I<\sqrt{m_u}$, then $\beta_u(I)=O(\frac{\log m_u}{m_u})\to0$ and $(I+1)x_t\le4\sqrt{m_u}b^{r_u-m_u}\to0^+$ for all $r_u<m_u-\Delta_u$, matching $\delta_0$. Combining Step 1 and Step 2 over all strata (whose weights $2^{-(K-u)}$ sum to $1-2^{-r}$) yields the proposition. $\square$

### 4.4 Proof of Theorems 4 and 5

*Proof of Theorem 4.* (1) Eventually all $-1$: for all $K$ at least two steps past the last $+1$, Proposition 4.4 with $r=0$ (or Phase 21 Proposition D2.5, converse) gives $W_1(\mu_N^{\mathrm{emp}}(y(\varepsilon)),\lambda)\to0$ and $D_N(y(\varepsilon);b)\to0$.

(2) Eventually all $+1$: if $\varepsilon_k=+1$ for all $k>K_0$, then Proposition 4.2(3) gives $W_1(\mu_{K-1},\delta_0)\to0$ as $K\to\infty$, and Proposition 4.3 then gives $W_1(\mu_N^{\mathrm{emp}}(y(\varepsilon)),\delta_0)\to0$ uniformly for $N\in[m_K,m_{K+1}]$. By Lemma 4.1(2), $D_N(y(\varepsilon);b)\to D(\delta_0)=1$, so $y(\varepsilon)\in K_b$.

(3) Infinitely many $-1$ and infinitely many $+1$: here the last $-1$ index $K_0(K)\to\infty$ as $K\to\infty$. By Propositions 4.2(3), 4.3, and 4.4, on every shell $[m_K,m_{K+1}]$ we have $W_1(\mu_N^{\mathrm{emp}}(y(\varepsilon)),\,(1-\alpha_N)\lambda+\alpha_N\delta_0)\to0$, where $\alpha_N=1-\theta_K(N)2^{-r_{K-1}}\in[1-2^{-r_{K-1}},\,1-2^{-r_K}]$ when $\varepsilon_K=+1$, and $\alpha_N=\alpha_K(N)\in[0,\,1-2^{-r_{K-1}}]$ when $\varepsilon_K=-1$. Therefore:

- Every weak\* limit point has the form $(1-\alpha)\lambda+\alpha\delta_0$ with $0\le\alpha\le\limsup_{K\to\infty}(1-2^{-r_K})=1-2^{-R_{\max}(\varepsilon)}$.
- For every finite $r\le R_{\max}(\varepsilon)$, infinitely many $+1$-runs reach length $r$; across the $r$ shells of each such run, Proposition 4.3 sweeps $\alpha_N$ in steps of $O(1/m_K)$ across every subinterval $[1-2^{-(j-1)},1-2^{-j}]$ ($1\le j\le r$), so every $\alpha\in[0,1-2^{-r}]$ is attained as a limit point. Taking the union over $r\le R_{\max}(\varepsilon)$ (and closure when $R_{\max}(\varepsilon)=\infty$) gives the exact weak\* limit set $\{(1-\alpha)\lambda+\alpha\delta_0:\ 0\le\alpha\le1-2^{-R_{\max}(\varepsilon)}\}$.
- By Lemma 4.1(2)–(3), $D_N(y(\varepsilon);b)=\alpha_N+o(1)$, giving $D^-=0$, $D^+=1-2^{-R_{\max}(\varepsilon)}$, and exact discrepancy limit set $[0,1-2^{-R_{\max}(\varepsilon)}]$. $\square$

*Proof of Theorem 5.* Track the sign of every point contributing to the $\delta_0$ mass of $\mu_N^{\mathrm{emp}}(y(\varepsilon))$:

1. *On a $+1$ shell $K$:* on odd bands of level $K$, $b^nR_K(\varepsilon)\equiv+\frac{b^rR_{K-1}}{b^{m_K}+1}\in(\frac14b^{r-m_K},4b^{r-m_K})$ is strictly positive ($0^+$). On even bands of level $K$, any point in stratum $E^{(u)}$ ($u<K$, where $u>K_0$) satisfies (4.2), which is strictly positive ($0^+$) of size $\ge\frac14b^{-m_u}$ outside an $o(1)$ edge set where higher-level tails $\le8b^{-2m_u-6}$ could compete. (When no $-1$ factor precedes a $+1$ run—for instance $\varepsilon\equiv+1$, so $K_0=0$ and $R_0=1$—the all-even stratum has weight $2^{-r_K}\to0$ and sits on the orbit of $R_1$, e.g. $1^-$ when $m_1$ is large; its total share has asymptotic density $0$.) Passing from $R_K(\varepsilon)$ to $y(\varepsilon)$ shifts by $|b^n(y(\varepsilon)-R_K(\varepsilon))|\le16b^{n-m_{K+1}}$, which is strictly smaller than $\frac14b^{-m_K}$ for all $n<m_{K+1}-m_K-10$ (fraction $1-o(1)$ of $[0,N)$).
2. *On a $-1$ transition shell $K$:* for $t\in E^{(u)}$ with $r_u<r_*-\Delta_u$, the unperturbed point $a x_t\in(0,4b^{-\Delta_u})$ is strictly positive, the band tail $+\eta_r^{(K)}=+\frac{b^rR_{K-1}}{b^{m_K}-1}>0$ is also strictly positive, and $|b^n(y(\varepsilon)-R_K(\varepsilon))|\le16b^{n-m_{K+1}}\ll\frac14b^{-m_K}\le\eta_r^{(K)}$ for all $n<m_{K+1}-m_K-10$.

Thus for every $L\ge1$, outside a set of indices of asymptotic density $0$, every point contributing to the $\delta_0$ mass lies in $(0,b^{-L})\subset C_{0^L}$, whereas the $(1-\alpha_N)\lambda$ component assigns mass $(1-\alpha_N)b^{-L}+o(1)$ to every cylinder $C_w$ ($w\in\{0,\dots,b-1\}^L$, since $\lambda(\partial C_w)=0$ and $W_1$-convergence implies convergence on $\lambda$-continuity sets). Hence

```math
f_{0^L}(N;y(\varepsilon))=\alpha_N+(1-\alpha_N)b^{-L}+o(1),\qquad f_w(N;y(\varepsilon))=(1-\alpha_N)b^{-L}+o(1)\quad(w\ne0^L).
```

Evaluating $\liminf$ and $\limsup$ over $\alpha_N$ via Theorem 4 gives all digit-frequency formulas. Since $\limsup f_0(N)=1-\frac{b-1}b2^{-R_{\max}(\varepsilon)}>\frac1b$ whenever $R_{\max}(\varepsilon)\ge1$ (and $f_0(N)\to1>\frac1b$ when $\varepsilon$ is eventually $+1$), simple normality forces $\varepsilon_k=-1$ eventually, which by Theorem 4(1) is equivalent to full normality. $\square$

---

## 5. Cyclotomic band family $P_k(q)$, base-2 simple normality, and prescribed discrepancy

Theorem 5 shows that simple normality and full normality coincide inside the two-term signed family $y(\varepsilon)=\prod(1+\varepsilon_kb^{-m_k})^{-1}$ because every zero-band tail is oriented $0^+$. To achieve asymptotic $\frac12/\frac12$ balance between $0^+$ and $1^-$ while keeping $x\in K_b$, we replace $(1+q)$ by a palindromic polynomial family $P_k(q)\in1+q\mathbb Z[q]$ whose exact mechanism is:

- all $4k+2$ zero-band tails of $P_k$ are still $0^+$ (indeed $\tau_{L_k-d}^{(k)}(q)=q^d/P_k(q)>0$ identically), with total density $\rho_k=\frac1{2k+3}\to0$;
- the nonzero bands are positively biased, with $\mathbb E[\operatorname{sgn}(S_i^{(k)})\mid S_i^{(k)}\ne0]=\frac1{k+1}$, **not** balanced at any single level;
- asymptotic $\frac12/\frac12$ balance emerges from composing levels: a $0^+$ point created at level $u$ has its sign multiplied across levels $v>u$ with conditional expectation $\prod_{v>u}\frac1{v+1}\to0$, driving the overall $0^+-1^-$ bias $B_J$ to $0$ at rate $B_J\sim1/J$.

### 5.1 Closed-form band theorem for $P_k(q)$

For every integer $k\ge1$, put $p=2k+1$, $r=2k+3=p+2$, $L_k=2pr=2(2k+1)(2k+3)$, and

```math
P_k(q):=\frac{1+q^p}{1+q}\cdot\frac{1+q^r}{1+q}=\biggl(\sum_{s=0}^{p-1}(-q)^s\biggr)\biggl(\sum_{t=0}^{r-1}(-q)^t\biggr)\in1+q\mathbb Z[q].
```

**Proposition 5.1 (exact structure of $P_k(q)$).** For every integer $k\ge1$:

1. $P_k(q)$ is palindromic of degree $p+r-2=2p=4k+2$, satisfies $P_k(1)=1$, and divides $\frac{1-q^{L_k}}{1-q}$ in $\mathbb Z[q]$.
2. Let $A_k(q)=\frac{1-q^{L_k}}{(1-q)P_k(q)}=\sum_{i=0}^{L_k-1}S_i^{(k)}q^i$ (setting $S_i^{(k)}=0$ for $i>\deg A_k$) and $\frac1{P_k(q)}=\sum_{s=0}^\infty c_s^{(k)}q^s$. Then $c_s^{(k)}$ and its partial sums $S_i^{(k)}=\sum_{s=0}^ic_s^{(k)}$ are purely periodic of period $L_k$, with:
   - **Zero internal zeros:** $S_i^{(k)}\ne0$ for every $0\le i<L_k-2p$, and $S_i^{(k)}=0$ for every $L_k-2p\le i<L_k$. In particular, the zero-band density is $\rho_k=\frac{2p}{L_k}=\frac1{2k+3}$, and every prefix $1\le I\le L_k$ has zero-band proportion at most $\frac1{2k+3}$.
   - **Exact sign counts:** among the $4(2k+1)(k+1)$ nonzero bands, exactly $2(k+2)(2k+1)$ satisfy $S_i^{(k)}>0$ and exactly $2k(2k+1)$ satisfy $S_i^{(k)}<0$. Hence
     ```math
     \mathbb E\bigl[\operatorname{sgn}(S_i^{(k)})\mid S_i^{(k)}\ne0\bigr]=\frac{2(k+2)(2k+1)-2k(2k+1)}{4(2k+1)(k+1)}=\frac1{k+1}.
     ```
   - **Exact range, uniform series bound, and exact zero-band tail:** $-2k\le S_i^{(k)}\le2k+2$ and $|c_s^{(k)}|\le2$ for all $i,s\ge0$ and all $k\ge1$. On every trailing zero-band $i=L_k-d$ ($1\le d\le2p$), the tail $\tau_i^{(k)}(q):=\sum_{u=1}^\infty c_{i+u}^{(k)}q^u$ equals $q^d/P_k(q)$ identically, begins with $+q^d$, and satisfies $\frac12q^d\le\tau_i^{(k)}(q)\le2q^d$ whenever $0<q\le\frac18$.

*Proof.* Since $p,r$ are odd and $\gcd(p,r)=1$, $\gcd(1+q^p,1+q^r)=1+q$, so $(1+q^p)(1+q^r)$ divides $(1+q)(1+q^{pr})$ in $\mathbb Z[q]$, and $P_k(1)=\frac22\cdot\frac22=1$. Define the polynomial

```math
G_k(q):=\frac{(1+q)(1+q^{pr})}{(1+q^p)(1+q^r)}=\sum_{n=0}^{p^2-1}g_nq^n\in\mathbb Z[q],
```

of degree $pr+1-p-r=p^2-1$, which is palindromic ($g_{p^2-1-n}=g_n$) because each defining factor is palindromic. Then

```math
A_k(q)=\frac{(1-q^{2pr})(1+q)^2}{(1-q)(1+q^p)(1+q^r)}=(1-q^{pr})\,\frac{1+q}{1-q}\,G_k(q)\in\mathbb Z[q],
```

proving (1). Next we determine $g_n$ explicitly. Setting $x=-q$ transforms $G_k(q)$ into $F_{p,r}(x)=\frac{(1-x)(1-x^{pr})}{(1-x^p)(1-x^r)}$. For $0\le n<pr$, the coefficient of $x^n$ in $\frac{1-x^{pr}}{(1-x^p)(1-x^r)}$ is $1$ if $n\in\mathcal S_{p,r}=\{ap+br:\ a,b\in\mathbb Z_{\ge0}\}$ and $0$ otherwise (representations with $a<r$ are unique since $\gcd(p,r)=1$). Hence $g_n=(-1)^n(\mathbf 1_{n\in\mathcal S_{p,r}}-\mathbf 1_{n-1\in\mathcal S_{p,r}})$. Writing $ap+b(p+2)=mp+2b$ with $m=a+b$ and $0\le b\le m$: for $0\le m\le k=\frac{p-1}2$, the values $\{mp,mp+2,\dots,mp+2m\}$ lie inside $[mp,(m+1)p-1]$ and consist of all integers in $[mp,mr]$ having parity $m\bmod2$. Therefore:

- for each $0\le m<k$: on $[mp,\,mr+1]$ (length $2m+2$), consecutive integers alternate membership in $\mathcal S_{p,r}$, giving $g_n=(-1)^m$; on $[mr+2,\,(m+1)p-1]$, neither $n$ nor $n-1$ lies in $\mathcal S_{p,r}$, giving $g_n=0$;
- for $m=k$ (the center block $[kp,\,kr]$, length $p$, centered at $\frac{p^2-1}2$): $g_n=(-1)^k$ (note $kr+1=(k+1)p$ has both $(k+1)p$ and $kr$ in $\mathcal S_{p,r}$, so $g_{(k+1)p}=0$);
- for $n>kr$: $g_n=g_{p^2-1-n}$ by palindromicity.

Now put $s_n=\sum_{j=0}^ng_j$ (with $s_{-1}=0$) and $t_n=s_n+s_{n-1}=2s_{n-1}+g_n$, the coefficient of $q^n$ in $\frac{1+q}{1-q}G_k(q)$. Since $G_k(1)=\frac{2\cdot2}{2\cdot2}=1$, we have $s_n=1$ and $t_n=2$ for all $n\ge p^2$. For $0\le m<k$, summing the block totals $+2,-4,+6,-8,\dots$ shows that after block $m$, $s_n=S_{\mathrm{after}}(m)$, where $S_{\mathrm{after}}(m)=m+2$ for even $m$ and $-(m+1)$ for odd $m$. In particular, $|S_{\mathrm{after}}(m)|\ge2$ for every $0\le m<k$, and on $[0,p^2/2)$:

- inside every nonzero block ($g_n=\pm1$), $t_n=2s_{n-1}+g_n$ is **odd** (hence neither $0$ nor $2$);
- inside every zero gap ($g_n=0$), $t_n=2S_{\mathrm{after}}(m)$ satisfies $|t_n|\ge4$ (hence neither $0$ nor $2$).

Palindromicity $g_{p^2-1-n}=g_n$ gives $s_{p^2-1-n}=1-s_{n-1}$ and therefore

```math
t_{p^2-1-n}=2-t_n\qquad(0\le n<p^2). \tag{5.1}
```

Since $t_j\notin\{0,2\}$ for all $0\le j<p^2/2$, (5.1) implies $t_n\ne0$ for **every** $0\le n<p^2$. For the exact range of $t_n$, observe that across blocks $m=0,\dots,k$, $s_n$ stays in $[-k,k+1]$ (reaching $+k+1$ at the end of block $k-1$ when $k$ is odd, or at the end of the center block $m=k$ when $k$ is even; and reaching $-k$ at the end of block $k-1$ when $k$ is even, or at the end of the center block $m=k$ when $k$ is odd). Whenever $s_{n-1}=k+1$, the preceding block had positive sign, so at step $n$ either $g_n=0$ (giving $t_n=2k+2$) or $g_n=-1$ (giving $t_n=2k+1$); symmetrically, whenever $s_{n-1}=-k$, $g_n\in\{0,+1\}$ gives $t_n\in\{-2k,-2k+1\}$. Thus $-2k\le t_n\le2k+2$ on $[0,p^2/2]$, and by (5.1), $t_{p^2-1-n}=2-t_n\in[-2k,2k+2]$ on all of $[0,p^2)$.

Now evaluate $S_i^{(k)}=t_i-t_{i-pr}$ using $pr=p^2+2p>p^2$:

1. For $0\le i<p^2$: $S_i^{(k)}=t_i\in[-2k,2k+2]\setminus\{0\}$.
2. For $p^2\le i<pr$ (length $2p$): $S_i^{(k)}=2-0=+2$.
3. For $pr\le i<pr+p^2=L_k-2p$: $S_i^{(k)}=2-t_{i-pr}=t_{p^2-1-(i-pr)}\in[-2k,2k+2]\setminus\{0\}$ (by (5.1)).
4. For $L_k-2p\le i<L_k$ (length $2p=4k+2$): $S_i^{(k)}=2-2=0$.

This proves zero internal zeros, the exact range $[-2k,2k+2]$, and the trailing zero-band block of length $2p=4k+2$. For the sign counts, in each pair $(t_n,2-t_n)$ on $[0,p^2)$, one entry is positive and one is negative unless $t_n=1$ (when both equal $+1$). Since $t_n=2s_{n-1}+g_n=1$ occurs iff $(s_{n-1},g_n)=(0,+1)$ or $(1,-1)$, and $s_n$ crosses between $\le0$ and $\ge1$ exactly once in each of the $2k+1=p$ nonzero blocks of $G_k$, $t_n=1$ occurs exactly $p$ times in $[0,p^2)$. Thus $[0,p^2)$ contains $\frac{p(p+1)}2$ positive and $\frac{p(p-1)}2$ negative terms. Doubling for $[pr,pr+p^2)$ and adding the $2p$ positive terms in $[p^2,pr)$ yields $p(p+3)=2(k+2)(2k+1)$ positive bands and $p(p-1)=2k(2k+1)$ negative bands.

Finally, $c_s^{(k)}=S_s^{(k)}-S_{s-1}^{(k)}=(g_s+g_{s-1})-(g_{s-pr}+g_{s-1-pr})$. Because $[0,p^2]$ and $[pr,pr+p^2]$ are disjoint and $|g_j|\le1$, we have $|c_s^{(k)}|\le2$ for all $s\ge0$. On a trailing zero-band $i=L_k-d$ ($1\le d\le2p$), $c_{i+1}^{(k)}=\dots=c_{L_k-1}^{(k)}=0$, and because $c^{(k)}$ has period $L_k$, $c_{i+d+u}^{(k)}=c_u^{(k)}$ for all $u\ge0$. Therefore $\tau_{L_k-d}^{(k)}(q)=\sum_{u=0}^\infty c_u^{(k)}q^{d+u}=q^d/P_k(q)$ identically, and since $c_0^{(k)}=1$ and $|c_u^{(k)}|\le2$, $\tau_{L_k-d}^{(k)}(q)\in[q^d(1-\frac{2q}{1-q}),\,q^d(1+\frac{2q}{1-q})]\subseteq[\frac12q^d,2q^d]$ for $0<q\le\frac18$. $\square$

### 5.2 Generalized band identity and period divisibility

**Lemma 5.2 (generalized band identity for $P_k$).** Let $b\ge2$, $k\ge1$, $m\ge1$, and $R\in\mathbb Q$ with $\gcd(b,\operatorname{den}(R))=1$ and $\operatorname{ord}_{\operatorname{den}(R)}(b)\mid m$. Put $R'=R/P_k(b^{-m})=R\cdot\frac{b^{2pm}}{P_k(b^m)}$.

1. $\gcd(b,P_k(b^m))=1$ and $P_k(b^m)\equiv P_k(1)=1\pmod{\operatorname{den}(R)}$ (so $\gcd(\operatorname{den}(R),P_k(b^m))=1$), and $\operatorname{ord}_{\operatorname{den}(R')}(b)\mid L_km$. If moreover $\gcd(\operatorname{num}(R),P_k(b^m))=1$ (in particular, whenever $\operatorname{num}(R)$ is a power of $b$), then $\operatorname{den}(R')=\operatorname{den}(R)P_k(b^m)$ in lowest terms.
2. For all $i\ge0$ and $0\le r<m$,
   ```math
   b^{im+r}R'\equiv S_{i\bmod L_k}^{(k)}\,b^rR+b^rR\,\tau_{i\bmod L_k}^{(k)}(b^{-m})\pmod1,
   ```
   where the exact rational tail is $\tau_i^{(k)}(q)=(1-q^{L_k})^{-1}\sum_{u=1}^{L_k}c_{(i+u)\bmod L_k}^{(k)}q^u$.

*Proof.* (1) Since $P_k(0)=1$, $P_k(b^m)\equiv1\pmod b$, so $\gcd(b,P_k(b^m))=1$. Since $\operatorname{ord}_{\operatorname{den}(R)}(b)\mid m$, we have $b^m\equiv1\pmod{\operatorname{den}(R)}$, hence $P_k(b^m)\equiv P_k(1)=1\pmod{\operatorname{den}(R)}$. By Proposition 5.1(1), $(X-1)P_k(X)\mid(X^{L_k}-1)$ in $\mathbb Z[X]$; evaluating at $X=b^m$ and using $\operatorname{den}(R)\mid(b^m-1)$ gives $\operatorname{den}(R')\mid\operatorname{den}(R)P_k(b^m)\mid(b^{L_km}-1)$, hence $\operatorname{ord}_{\operatorname{den}(R')}(b)\mid L_km$. When $\gcd(\operatorname{num}(R),P_k(b^m))=1$, no cancellation occurs between $\operatorname{num}(R)\,b^{2pm}$ and $\operatorname{den}(R)\,P_k(b^m)$, so $\operatorname{den}(R')=\operatorname{den}(R)P_k(b^m)$.

(2) Expanding $b^{im+r}R'=\sum_{s=0}^\infty c_s^{(k)}b^{(i-s)m+r}R$, every $0\le s\le i$ satisfies $b^{(i-s)m+r}R\equiv b^rR\pmod1$ because $b^m\equiv1\pmod{\operatorname{den}(R)}$. The terms $s\le i$ sum to $S_i^{(k)}b^rR\equiv S_{i\bmod L_k}^{(k)}b^rR\pmod1$, and the tail $s>i$ equals $b^rR\,\tau_{i\bmod L_k}^{(k)}(b^{-m})$, which sums by $L_k$-periodicity of $c^{(k)}$ to the displayed rational function. $\square$

### 5.3 Proof of Theorem 6(1): simply normal reciprocal in $K_2$

Fix $b\ge2$, set $m_1=8$ and $m_{j+1}=b^{(j+1)^3}L_jm_j$ for $j\ge1$, and put $x=\prod_{j=1}^\infty P_j(b^{-m_j})$, $R_J=\prod_{j=1}^J P_j(b^{-m_j})^{-1}$, and $y=1/x=\lim R_J$. Since $P_j(q)=1+\sum_{d=1}^{4j+2}a_{j,d}q^d$ has $\sum_{d\ge1}|a_{j,d}|<4(j+2)^2$, we have $\sum_{j\ge1}|P_j(b^{-m_j})-1|<\frac14$, so $R_J,x,y\in(\frac34,\frac43)$ and $|y-R_J|\le12(J+3)^2b^{-m_{J+1}}$.

*Step 1: $x\in K_b$.* For $m_J\le N<m_{J+1}$, $N\ge b^{J^3}$ gives $J\le(\log_bN)^{1/3}$. In the power-series expansion $x=\sum_{n\ge0}c_x(n)b^{-n}$, the support up to $N+w$ (with $w=O(\ln N)$) has cardinality at most $2\prod_{j=1}^J(4j+3)=\exp(O(J\ln J))=N^{o(1)}$, and every coefficient has magnitude at most $\prod_{j=1}^{J+1}(2j+1)(2j+3)=N^{o(1)}$. By `discrepancy_deficit_le` (Phase 20, Lemma 0(a)), $1-D_N(x;b)\le N^{-1+o(1)}\to0$, so $x\in K_b$.

*Step 2: Complete-period distribution of $R_J$.* By induction using Lemma 5.2(1) and $L_jm_j\mid m_{j+1}$, we have $T_j=\operatorname{ord}_{D_j}(b)\mid L_jm_j$ for every $j\ge1$. Consider a uniformly random $t\in\{0,1,\dots,L_Jm_J-1\}$. Its mixed-radix expansion

```math
t=\sum_{j=1}^J\bigl(i_j(t)m_j+q_j(t)L_{j-1}m_{j-1}\bigr)+r_1(t) \qquad(L_0m_0:=m_1,\, q_1:=0)
```

has coordinates $i_j(t)\in\{0,\dots,L_j-1\}$, $q_j(t)\in\{0,\dots,b^{j^3}-1\}$ ($j\ge2$), and $r_1(t)\in\{0,\dots,m_1-1\}$ that are **mutually independent and exactly uniform**. Put $U(t)=\max(\{0\}\cup\{1\le j\le J:\ S_{i_j(t)}^{(j)}=0\})$ and $u_0=\lfloor\sqrt J\rfloor$. Since $\mathbb P(S_{i_j}^{(j)}=0)=\frac1{2j+3}$,

```math
\mathbb P(U(t)\le u_0)=\prod_{j=u_0+1}^J\Bigl(1-\frac1{2j+3}\Bigr)\le\exp\Bigl(-\sum_{j=u_0+1}^J\frac1{2j+3}\Bigr)=O(J^{-1/4})\to0.
```

Whenever $U(t)=u\in(u_0,J]$, telescoping Lemma 5.2(2) from level $J$ down to level $u$ (where $S_{i_u}^{(u)}=0$ annihilates the $R_{u-1}$ term) gives the exact identity

```math
b^tR_J\equiv\underbrace{\biggl(\prod_{v=u+1}^J S_{i_v}^{(v)}\biggr)\,b^{r_u}R_{u-1}\,\tau_{i_u}^{(u)}(b^{-m_u})}_{\Lambda_u(t)}+\underbrace{\sum_{v=u+1}^J\biggl(\prod_{w=v+1}^J S_{i_w}^{(w)}\biggr)\,b^{r_v}R_{v-1}\,\tau_{i_v}^{(v)}(b^{-m_v})}_{E_u(t)}\pmod1,
```

with $r_v=t\bmod m_v$. Put $L_J^*=\lceil4J\log_bJ\rceil+J+L$. For $u>u_0$:

- $1\le|\prod_{v=u+1}^JS_{i_v}^{(v)}|\le(2J+2)^J\le b^{3J\log_bJ}$ (for large $J$);
- $r_u(t)$ is independent of $(i_u,\dots,i_J)$, so $\mathbb P(r_u\ge m_u-L_J^*\mid U=u)\le L_J^*/m_u\le L_J^*/b^{J^{3/2}}$;
- the event $\exists v\in(u,J]$ with $q_v(t)=b^{v^3}-1$ is **independent of all $i_j(t)$** and has probability $\le\sum_{v>u_0}b^{-v^3}\le2b^{-J^{3/2}}$. Outside it, every $v>u$ satisfies $r_v<m_v-L_{v-1}m_{v-1}<m_v-(4u+4)m_u-L_J^*$ (for large $J$, since $L_{v-1}m_{v-1}\ge L_um_u\ge8u^2m_u$).

Outside these two events (combined probability $O(J\log J\cdot b^{-J^{3/2}})$), we have $|\Lambda_u(t)|\in[\frac38b^{-(4u+2)m_u},\,3b^{-J-L}]$ and $|E_u(t)|\le b^{-J}b^{-(4u+2)m_u}\ll|\Lambda_u(t)|$. Therefore $\Lambda_u(t)+E_u(t)$ lies strictly in $(-b^{-L},b^{-L})\setminus\{0\}$ and has exact sign $\sigma_{u,J}(t)=\prod_{v=u+1}^J\operatorname{sgn}(S_{i_v}^{(v)})$.

Conditioned on $U(t)=u$, the indices $i_{u+1},\dots,i_J$ are independent and uniform over the nonzero bands of $P_v$, so Proposition 5.1(2) gives

```math
\mathbb E\bigl[\sigma_{u,J}(t)\mid U(t)=u\bigr]=\prod_{v=u+1}^J\frac1{v+1}=\frac{(u+1)!}{(J+1)!}\le\frac1{J+1}\qquad(u\le J-1),
```

while $\mathbb P(U(t)=J)=\frac1{2J+3}$. Hence the complete-period bias $\Delta_J:=f_{0^L}(L_Jm_J;R_J)-f_{(b-1)^L}(L_Jm_J;R_J)$ satisfies $|\Delta_J|\le\frac1{2J+3}+\frac1{J+1}+O(J^{-1/4})=O(J^{-1/4})$, and $f_{0^L}(L_Jm_J;R_J)+f_{(b-1)^L}(L_Jm_J;R_J)=1-O(J^{-1/4})$.

*Step 3: All prefixes $N\in[m_J,m_{J+1}]$ and irrationality.* Passing from $y$ to $R_J$ affects only $n\ge m_{J+1}-(4J+4)m_J-L_J^*$, which is either empty (if $N$ is below this threshold) or has proportion $O(J/b^{(J+1)^3})\to0$ of $[0,N)$. Write $N=Im_J+r_0$ ($I\ge1$, $0\le r_0<m_J$). In the partial band $i=I$, the incomplete cycle $r_0\bmod(L_{J-1}m_{J-1})$ has weight $<L_{J-1}m_{J-1}/m_J=b^{-J^3}\to0$. Among all complete bands $0\le i<I$ and the complete $L_{J-1}m_{J-1}$-cycles in the partial band:

- every band with $S_{i\bmod L_J}^{(J)}=0$ lies in the trailing $4J+2$ indices of an $L_J$-block, so their total proportion in $[0,N)$ is at most $\frac1{2J+3}$ (Proposition 5.1(2));
- every band with $S_{i\bmod L_J}^{(J)}\ne0$ maps $R_{J-1}$ by multiplication by $S_{i\bmod L_J}^{(J)}$ plus the band tail $b^rR_{J-1}\tau_{i\bmod L_J}^{(J)}(b^{-m_J})$; since $1\le|S_{i\bmod L_J}^{(J)}|\le2J+2\ll b^J$ cannot push points of size $\le3b^{-(J-1)-L}$ out of $(-b^{-L},b^{-L})$ and the band tail is $\le6b^{r-m_J}\ll\frac38b^{-(4J-2)m_{J-1}}$ outside the edge set $r\ge m_J-(4J+2)m_{J-1}-L_J^*$ (proportion $O(J/b^{J^3})$), multiplication preserves $\delta_0$ and multiplies the sign bias $\Delta_{J-1}$ by $\operatorname{sgn}(S_{i\bmod L_J}^{(J)})$, so on every single nonzero band both $0^L$ and $(b-1)^L$ have density $\frac12\pm\frac12|\Delta_{J-1}|+O(J^{-1/4})=\frac12+O(J^{-1/4})$.

Therefore, uniformly over $N\in[m_J,m_{J+1}]$, $f_{0^L}(N;y)=\frac12+O(J^{-1/4})$, $f_{(b-1)^L}(N;y)=\frac12+O(J^{-1/4})$, and $1-D_N(y;b)=O(J^{-1/4})\to0$. For $b=2$ and $L=1$, this yields $f_0(N;y)\to\frac12$ and $f_1(N;y)\to\frac12$ along all $N$ while $y\in K_2$. Finally, $y$ (and hence $x=1/y$) is irrational: no eventually periodic base-$b$ expansion can satisfy $f_{0^L}(N;y)\to\frac12$ for $L$ exceeding its period. (By Theorem A of [`simple-normality-and-signed-transfer.md`](simple-normality-and-signed-transfer.md), no element of $K_b$ can be simply normal in any base $b\ge3$, so $b=2$ is sharp for $y\in K_b$.) $\square$

### 5.4 Proof of Theorem 6(2): prescribed $D^+(1/x;b)=\alpha\in[0,1]$ and base-2 simple normality

For $\alpha=0$, Theorem 2 gives an irrational $x=\prod_{k\ge1}(1-b^{-m_k})\in K_b$ whose reciprocal $y=1/x$ is base-$b$ normal ($D^-=D^+=0$, limit set $\{0\}$, weak\* limit set $\{\lambda\}$, and in particular simply normal in base $b$).

Now fix any $\alpha\in(0,1]$ (handling $\alpha\in(0,1)$ and $\alpha=1$ uniformly). For each integer $s\ge1$, put $f_s(t)=\prod_{k=s}^{s+t-1}\bigl(1-\frac1{2k+3}\bigr)$ ($t\ge0$).

- If $\alpha\in(0,1)$: set $s_0=\lceil1/\alpha\rceil+1$. Since $f_s(0)=1>1-\alpha$, $f_s(t)\to0$, and $0<f_s(t)-f_s(t+1)\le\frac1{2s+3}$, putting $t_s:=\max\{t\ge0:\ f_s(t)\ge1-\alpha\}$ yields $1-\alpha\le f_s(t_s)<1-\alpha+\frac1{2s+3}$, so $\alpha_s:=1-f_s(t_s)\in(\alpha-\frac1{2s+3},\alpha]$.
- If $\alpha=1$: set $s_0=1$ and $t_s:=s^2$. Since $\sum_{k=s}^{s+s^2-1}\frac1{2k+3}=\frac12\ln s+O(1)\to\infty$, we have $f_s(t_s)=O(s^{-1/2})\to0$, so $\alpha_s:=1-f_s(t_s)=1-O(s^{-1/2})\to1=\alpha$ with $\alpha_s<1$.

In both cases, $0<\alpha_s\le\alpha$ for all $s\ge s_0$ and $\alpha_s\to\alpha$.

**Definition of the factor sequence and exponents.** Build the polynomial sequence $(Q_n)_{n\ge1}$ in rounds $s=s_0,s_0+1,\dots$, with round $s$ starting at $n_s$ ($n_{s_0}=1$, $n_{s+1}=n_s+2+t_s$):

- $Q_{n_s}(q)=1-q$ and $Q_{n_s+1}(q)=1-q$ (two minus-sign reset factors);
- $Q_{n_s+1+j}(q)=P_{s+j-1}(q)$ for $j=1,\dots,t_s$ (the $t_s$ cyclotomic factors of round $s$, with index $k_j=s+j-1$, $p_j=2k_j+1$, $L_j=2(2k_j+1)(2k_j+3)$, $\rho_j=\frac1{2k_j+3}$).

For **every** $n\ge1$, define explicitly the degree $d_n=\deg Q_n$, the number of nonzero terms $\#(Q_n)$, and the coefficient $\ell^1$-norm $\|Q_n\|_1$: for $Q_n(q)=1-q$ these are $(d_n,\#(Q_n),\|Q_n\|_1)=(1,2,2)$; for $Q_n(q)=P_k(q)$ they satisfy $d_n=4k+2$, $\#(Q_n)\le4k+3$, and $\|Q_n\|_1\le(2k+1)(2k+3)<4(k+2)^2$. Put

```math
C_n:=\prod_{j=1}^n\#(Q_j)\|Q_j\|_1,\qquad M_s:=\prod_{k=s}^{s+t_s-1}(2k+2),
```

and define the step period modulus $\widetilde T_0:=1$, $\widetilde T_n:=T_n=m_nD_{n-1}$ when $Q_n(q)=1-q$ (exact by Theorem 1(1)), and $\widetilde T_n:=L_nm_n$ when $Q_n(q)=P_{k_n}(q)$ (a multiple of $T_n$ by Lemma 5.2(1)). Because the entire sequence $(Q_n)_{n\ge1}$ is fixed in advance, we choose $(m_n)_{n\ge1}$ recursively as positive multiples of $\widetilde T_{n-1}$ satisfying $m_1\ge8$,

```math
m_n\ge b^{n^3}\,\widetilde T_{n-1}\,C_n^n\,(d_n+1)\qquad(n\ge1),\qquad\text{and}\qquad b^{m_{n_s}}-1\ge2^sM_s^2\quad(s\ge s_0).
```

Put $x=\prod_{n=1}^\infty Q_n(b^{-m_n})$, $R_n=\prod_{j=1}^n Q_j(b^{-m_j})^{-1}$, and $y=1/x=\lim R_n$. Since $\sum_{n\ge1}\|Q_n\|_1b^{-m_n}<\frac14$, we have $x,y,R_n\in(\frac34,\frac43)$ and $|y-R_n|\le4\|Q_{n+1}\|_1b^{-m_{n+1}}$ for all $n\ge1$.

**Proof that $x\in K_b$.** Fix $N\in[m_n,m_{n+1})$ and set $w=\lceil3\log_bN\rceil+10$. If $N+w<m_{n+1}$, only $Q_1,\dots,Q_n$ contribute to $[0,N+w]$, so $S(N+w)\le C_n\le m_n^{1/n}\le N^{1/n}=N^{o(1)}$ and $\max_{j\le N+w}|c_x(j)|\le C_n\le N^{1/n}=N^{o(1)}$. If $N+w\ge m_{n+1}$, then $N\ge\frac12m_{n+1}$ (for large $n$), and only $Q_1,\dots,Q_{n+1}$ contribute to $[0,N+w]$, giving $S(N+w)$ and $\max|c_x|$ both $\le C_{n+1}\le m_{n+1}^{1/(n+1)}\le(2N)^{1/(n+1)}=N^{o(1)}$. Hence `discrepancy_deficit_le` gives $1-D_N(x;b)\le N^{-1+o(1)}\to0$, so $x\in K_b$.

Now fix a round $s\ge s_0$, put $n_0:=n_s+1$ (the second $-1$ reset of round $s$), and abbreviate $m^{(j)}:=m_{n_0+j}$, $R^{(j)}:=R_{n_0+j}$, $\widetilde T^{(j)}:=\widetilde T_{n_0+j}$, and $Q_v:=m^{(v)}/\widetilde T^{(v-1)}\ge b^{(n_0+v)^3}$ for $1\le j,v\le t_s$ (with $R^{(0)}:=R_{n_0}$, $\widetilde T^{(0)}:=T_{n_0}=m_{n_0}D_{n_s}$). Note that $b^{m_{n_s}}-1\ge2^sM_s^2$ implies $D_{n_s}\ge2^sM_s^2$ and $m_{n_s}\ge\log_b(2^sM_s^2)$, hence $m^{(1)}\ge b^{n_0^3}m_{n_0}\gg(\log_bM_s)^2+s$.

**Step 1: Complete-period decomposition and bias recursion across round $s$.** For any $1\le j\le t_s$, a uniformly random $t\in\{0,\dots,\widetilde T^{(j)}-1\}$ has mixed-radix coordinates $i_v(t)=\lfloor t/m^{(v)}\rfloor\bmod L_v\in\{0,\dots,L_v-1\}$ ($1\le v\le j$), $q_v(t)=\lfloor(t\bmod m^{(v)})/\widetilde T^{(v-1)}\rfloor\in\{0,\dots,Q_v-1\}$ ($1\le v\le j$), and $t_0=t\bmod T_{n_0}\in\{0,\dots,T_{n_0}-1\}$, which are **mutually independent and exactly uniform**. Partition $\{0,\dots,\widetilde T^{(j)}-1\}$ into:

- $E_2^{(j)}=\{t:\ S_{i_v}^{(k_v)}\ne0\text{ for all }1\le v\le j\}$, of exact density $f_s(j)=\prod_{v=1}^j(1-\rho_v)$;
- depth-indexed zero-band strata $E_{u,d}^{(j)}=\{t:\ i_u(t)=L_u-d\text{ and }S_{i_v}^{(k_v)}\ne0\text{ for all }u<v\le j\}$ ($1\le u\le j$, $1\le d\le4k_u+2$), of exact density $w_{u,d}^{(j)}:=L_u^{-1}\prod_{v=u+1}^j(1-\rho_v)$, summing over $d$ to $\rho_u\prod_{v=u+1}^j(1-\rho_v)$ and over all $(u,d)$ to $1-f_s(j)$.

1. *On $E_2^{(j)}$:* telescoping Lemma 5.2(2) from $j$ down to $1$ gives
   ```math
   b^tR^{(j)}\equiv S_{\mathrm{tot}}(t)\,b^{t_0}R^{(0)}+\sum_{v=1}^j\biggl(\prod_{w=v+1}^j S_{i_w}^{(k_w)}\biggr)b^{r_v}R^{(v-1)}\tau_{i_v}^{(k_v)}(b^{-m^{(v)}})\pmod1, \tag{5.2}
   ```
   where $S_{\mathrm{tot}}(t)=\prod_{v=1}^jS_{i_v}^{(k_v)}$ satisfies $1\le|S_{\mathrm{tot}}(t)|\le M_s$ and $r_v=t\bmod m^{(v)}$. By Proposition 4.2(1), $\mu_{n_0}$ is a convex combination of shifted $D_{n_s}$-point uniform grids, so for each fixed $(i_1,\dots,i_j)\in E_2^{(j)}$, averaging over the independent variable $t_0$ produces $(S_{\mathrm{tot}})_*\mu_{n_0}$, which is a convex combination of shifted $(D_{n_s}/\gcd(|S_{\mathrm{tot}}|,D_{n_s}))$-point uniform grids and therefore satisfies
   ```math
   D\bigl((S_{\mathrm{tot}})_*\mu_{n_0}\bigr)\le\frac{\gcd(|S_{\mathrm{tot}}|,D_{n_s})}{D_{n_s}}\le\frac{M_s}{2^sM_s^2}=\frac1{2^sM_s},\qquad W_1\bigl((S_{\mathrm{tot}})_*\mu_{n_0},\lambda\bigr)\le\frac1{4\cdot2^sM_s}.
   ```
   For the tail sum in (5.2), whenever $q_v(t)\le Q_v-2$ for all $1\le v\le j$ (which fails with probability at most $\sum_{v=1}^jQ_v^{-1}\le2b^{-n_0^3}$, independent of $(i_1,\dots,i_j)$), we have $r_v<m^{(v)}-\widetilde T^{(v-1)}\le m^{(v)}-T_{n_0}$, so the entire tail sum has modulus at most $\sum_{v=1}^j6M_sb^{-T_{n_0}}\le b^{-2^s}$. Hence the empirical measure $\mu_{E_2}^{(j)}$ on $E_2^{(j)}$ satisfies $W_1(\mu_{E_2}^{(j)},\lambda)\le2^{-s}$.

2. *On $E_{u,d}^{(j)}$:* telescoping Lemma 5.2(2) from $j$ down to $u$ (where $S_{L_u-d}^{(k_u)}=0$) gives
   ```math
   b^tR^{(j)}\equiv\underbrace{\biggl(\prod_{v=u+1}^jS_{i_v}^{(k_v)}\biggr)b^{r_u}R^{(u-1)}\tau_{L_u-d}^{(k_u)}(b^{-m^{(u)}})}_{\Lambda_{u,d}(t)}+\underbrace{\sum_{v=u+1}^j\biggl(\prod_{w=v+1}^jS_{i_w}^{(k_w)}\biggr)b^{r_v}R^{(v-1)}\tau_{i_v}^{(k_v)}(b^{-m^{(v)}})}_{E_{u,d}(t)}\pmod1. \tag{5.3}
   ```
   Here $r_u=t\bmod m^{(u)}$ is **independent** of $(i_u,\dots,i_j)$ and **exactly uniform** on $\{0,\dots,m^{(u)}-1\}$. Put $L_s^*:=\lceil\log_b(16M_s)\rceil+s+2$. Outside the two independent edge events $\{r_u\ge m^{(u)}-L_s^*\}$ (conditional probability $\le L_s^*/m^{(u)}\le b^{-n_0^3/2}$) and $\bigcup_{v=u+1}^j\{q_v(t)=Q_v-1\}$ (probability $\le2b^{-n_0^3}$), Proposition 5.1(2) gives $\tau_{L_u-d}^{(k_u)}(b^{-m^{(u)}})\in[\frac12b^{-dm^{(u)}},2b^{-dm^{(u)}}]$, so
   ```math
   \frac38b^{r_u-dm^{(u)}}\le|\Lambda_{u,d}(t)|\le\frac83M_sb^{r_u-dm^{(u)}}\le\frac12b^{-s-2},
   ```
   while for every $v>u$, $r_v<m^{(v)}-\widetilde T^{(v-1)}\le m^{(v)}-L_um^{(u)}<m^{(v)}-(4k_u+4)m^{(u)}-L_s^*$, giving $|E_{u,d}(t)|\le b^{-s}b^{-(4k_u+2)m^{(u)}}\ll|\Lambda_{u,d}(t)|$. Hence $b^tR^{(j)}\bmod1$ lies strictly in $(-b^{-s-2},b^{-s-2})\setminus\{0\}$ with exact sign $\sigma_{u,j}(t):=\prod_{v=u+1}^j\operatorname{sgn}(S_{i_v}^{(k_v)})$, which is **independent of $(r_u,d)$** and has conditional expectation
   ```math
   \mathbb E\bigl[\sigma_{u,j}(t)\mid E_{u,d}^{(j)}\bigr]=\prod_{v=u+1}^j\frac1{k_v+1}=\frac{(s+u)!}{(s+j)!}\ge0. \tag{5.4}
   ```
   Summing over all strata $(u,d)$ defines the complete-period signed bias $B^{(j)}:=\sum_{u=1}^j\rho_u\bigl(\prod_{v=u+1}^j(1-\rho_v)\bigr)\frac{(s+u)!}{(s+j)!}$, which satisfies $B^{(0)}=0$ and the exact recursion
   ```math
   B^{(j)}=\frac{2B^{(j-1)}+1}{2k_j+3}\qquad(1\le j\le t_s). \tag{5.5}
   ```
   By induction ($0\le B^{(j-1)}\le1\implies0\le B^{(j)}\le\frac{2\cdot1+1}{2k_j+3}$), we have $0\le B^{(j)}\le\frac3{2k_j+3}\le\frac3{2s+3}$ for every $1\le j\le t_s$.

**Step 2: All prefixes $N\in[m^{(j)},m^{(j+1)}]$ inside cyclotomic shell $j$ ($1\le j\le t_s$).** Write $N=Im^{(j)}+r_0$ ($I\ge1$, $0\le r_0<m^{(j)}$). Passing from $y$ to $R^{(j)}$ affects only $n\ge m^{(j+1)}-(4k_j+4)m^{(j)}-L_s^*$ (proportion $O(b^{-n_0^3})\to0$), and the incomplete cycle $r_0\bmod\widetilde T^{(j-1)}$ in the partial band has weight $<\widetilde T^{(j-1)}/m^{(j)}\le b^{-n_0^3}\to0$. Let $\theta_j(N)$ be the fraction of indices in $[0,N)$ falling in trailing zero-bands of $P_{k_j}$; by Proposition 5.1(2), $0\le\theta_j(N)\le\rho_j=\frac1{2k_j+3}\le\frac1{2s+3}$ for every $N\ge m^{(j)}$.

On every nonzero band $i$ ($S_{i\bmod L_j}^{(k_j)}\ne0$), multiplying $R^{(j-1)}$ by $S_{i\bmod L_j}^{(k_j)}$ ($1\le|S|\le2k_j+2\le M_s$) preserves $\lambda$ on $E_2^{(j-1)}$ up to $W_1\le2^{-s}$, preserves $\delta_0$ on every $E_{u,d}^{(j-1)}$ (keeping points in $(-b^{-s-1},b^{-s-1})\setminus\{0\}$ outside the $O(b^{-n_0^3/2})$ edge set), and multiplies the inherited bias $B^{(j-1)}$ by $\operatorname{sgn}(S_{i\bmod L_j}^{(k_j)})\in\{-1,+1\}$. Thus:

- $W_1\bigl(\mu_N^{\mathrm{emp}}(y),\,(1-\gamma_N)\lambda+\gamma_N\delta_0\bigr)\to0$, where $\gamma_N:=1-(1-\theta_j(N))f_s(j-1)\in[1-f_s(j-1),\,1-f_s(j)]\subseteq[0,\alpha_s]$, increasing smoothly in steps $\le\frac1{2s+3}$ from $0$ to $\alpha_s$ across round $s$;
- in base $b=2$, even on a partly traversed $L_j$-block (where early bands are positive so the complete-period contraction factor $\frac1{k_j+1}$ does not apply), every nonzero band has signed $0^+-1^-$ bias of absolute value $B^{(j-1)}+o(1)$, while the trailing zero-bands contribute at most $\theta_j(N)\le\rho_j$, so
  ```math
  \bigl|f_0(N;y)-\tfrac12\bigr|\le\frac12\bigl(B^{(j-1)}+\theta_j(N)\bigr)+o(1)\le\frac12\Bigl(\frac3{2s+3}+\frac1{2s+3}\Bigr)+o(1)=\frac2{2s+3}+o(1).
  ```

**Step 3: Full Kronecker melting and base-2 digit-bias preservation on the first $-1$ reset shell $K:=n_{s+1}$.** Here $Q_K(q)=1-q$ follows $K-1=n_0+t_s$. Write $N=Im_K+r_0\in[m_K,m_{K+1}]$ ($I\ge1$, $0\le r_0<m_K$). Passing from $y$ to $R_K$, dropping the band tails $\eta_r^{(K)}$ in $W_1$ (cost $\le24/m_K$), and dropping the incomplete cycle $r_0\bmod\widetilde T^{(t_s)}$ (weight $\le b^{-K^3}$) leaves $\widetilde\mu_N=f_s(t_s)\sigma^{(2)}+\sum_{u=1}^{t_s}\sum_{d=1}^{4k_u+2}w_{u,d}^{(t_s)}\sigma_{u,d}$, where each $\sigma$ averages $a_*$ over $a=1,\dots,I$ (weight $m_K/M$) and $a=I+1$ (weight $r_0'/M$, $r_0'=\lfloor r_0/\widetilde T^{(t_s)}\rfloor\widetilde T^{(t_s)}<m_K$, $M=Im_K+r_0'$).

*Part A: $W_1(\sigma^{(2)},\lambda)\to0$ uniformly in $I\ge1$.* Choose the explicit Erdős–Turán cutoff

```math
H_s:=\min\Bigl(2^{\lfloor s/2\rfloor},\ \Bigl\lfloor\frac{m^{(1)}}{s\,m_{n_0}}\Bigr\rfloor\Bigr)\to\infty,
```

noting $H_sM_s<2^sM_s^2\le D_{n_s}<D_{n_0}$ for $s\ge2$. Fix $1\le h\le H_s$. In both regimes below, exclude the event $\bigcup_{v=1}^{t_s}\{q_v(t)=Q_v-1\}$ (independent of $E_2^{(t_s)}$, conditional probability $\le2b^{-n_0^3}$); outside it, every $r_v<m^{(v)}-T_{n_0}=m^{(v)}-m_{n_0}D_{n_s}$, and since $D_{n_0}<b^{2m_{n_0}}$, the tail sum in (5.2) has modulus at most $\sum_{v=1}^{t_s}6M_sb^{-m_{n_0}D_{n_s}}\le\frac1{4D_{n_0}^4}$.

- *Regime 1 ($I\le D_{n_0}^2$):* For every $1\le a\le I+1$, $ha\cdot\frac1{4D_{n_0}^4}\le D_{n_0}^{-1}$. Replacing $b^tR^{(t_s)}$ by $S_{\mathrm{tot}}(t)b^{t_0}R^{(0)}$ in $e(hab^tR^{(t_s)})$ therefore costs at most $2\pi D_{n_0}^{-1}+2b^{-n_0^3}$. For each fixed $(i_1,\dots,i_{t_s})\in E_2^{(t_s)}$ with $S=S_{\mathrm{tot}}(t)$ ($1\le|S|\le M_s$), averaging over the independent $t_0$ gives $\widehat C_{n_0}(haS)$, which by Lemma D2.2 at the $-1$ reset level $n_0$ vanishes unless $(D_{n_s}/\gcd(h|S|,D_{n_s}))\mid a$. By Lemma 2.1,
  ```math
  |\widehat\sigma^{(2)}(h)|\le\max_{1\le|S|\le M_s}\frac{\gcd(h|S|,D_{n_s})}{D_{n_s}}+2\pi D_{n_0}^{-1}+2b^{-n_0^3}\le\frac{H_sM_s}{2^sM_s^2}+O(D_{n_0}^{-1}+b^{-n_0^3})\le 2^{-s/2}+O(b^{-n_0^3}).
  ```
- *Regime 2 ($I>D_{n_0}^2$):* For every $t\in E_2^{(t_s)}$ outside the excluded $q_v$-event, $y_t=\{b^{t_0}R^{(0)}\}=\frac{b^{t_0}A_{n_0}}{D_{n_0}}\bmod1$ has $\gcd(b^{t_0}A_{n_0},D_{n_0})=1$. Since $1\le h|S_{\mathrm{tot}}(t)|\le H_sM_s<D_{n_0}$, we have $\|hS_{\mathrm{tot}}(t)y_t\|\ge\frac1{D_{n_0}}$, and adding the tail of size $\le\frac1{4D_{n_0}^4}$ leaves $\|hb^tR^{(t_s)}\|\ge\frac3{4D_{n_0}}$. Reversing summation over $a=1,\dots,I$ and $t\in E_2^{(t_s)}$, the Kronecker bound plus partial-band weight $r_0'/M\le1/I$ gives
  ```math
  |\widehat\sigma^{(2)}(h)|\le\frac{2D_{n_0}}{3I}+\frac1I+2b^{-n_0^3}\le\frac2{D_{n_0}}+2b^{-n_0^3}.
  ```

Applying Erdős–Turán over $1\le h\le H_s$ gives $D(\sigma^{(2)})\le\frac6{H_s+1}+\frac4\pi(1+\ln H_s)(2^{-s/2}+O(D_{n_0}^{-1}+b^{-n_0^3}))\to0$, hence $W_1(\sigma^{(2)},\lambda)\to0$ uniformly in $I\ge1$.

*Part B: Depth-indexed melting on $E_{u,d}^{(t_s)}$ and base-2 bias preservation.* For each $1\le u\le t_s$ and $1\le d\le4k_u+2$, define the depth-shifted melting fraction

```math
\beta_{u,d}(I):=\min\Bigl(1,\ \max\Bigl(0,\ \frac{\log_b I-(d-1)m^{(u)}}{m^{(u)}}\Bigr)\Bigr)\in[0,1].
```

For $t\in E_{u,d}^{(t_s)}$ outside $\bigcup_{v>u}\{q_v(t)=Q_v-1\}$ (probability $\le2b^{-n_0^3}$), (5.3) gives $x_t:=\{b^tR^{(t_s)}\}\equiv\sigma_{u,t_s}(t)|x_t|\pmod1$ with $|x_t|\in(\frac14b^{r_u-dm^{(u)}},\,4M_sb^{r_u-dm^{(u)}})$ for all $r_u<m^{(u)}-\log_b(16M_s)-2$, where $r_u$ is uniform on $\{0,\dots,m^{(u)}-1\}$ and **independent** of $\sigma_{u,t_s}(t)$. Put $\Delta_u:=\lceil\sqrt{m^{(u)}}\rceil+\lceil\log_b(16M_s)\rceil+1$ (so $\Delta_u/m^{(u)}\le2b^{-n_0^3/2}\to0$ uniformly in $u$) and $r_*:=dm^{(u)}-\lfloor\log_bI\rfloor$:

1. *Unmelted zone $0\le r_u<r_*-\Delta_u$* (proportion $1-\beta_{u,d}(I)+O(b^{-n_0^3/2})$): $I|x_t|\le4M_sIb^{r_u-dm^{(u)}}\le b^{-\sqrt{m^{(u)}}}$, so every $ax_t$ ($1\le a\le I$) stays in $(0,b^{-\sqrt{m^{(u)}}})$ when $\sigma_{u,t_s}(t)=+1$ and in $(1-b^{-\sqrt{m^{(u)}}},1)$ when $\sigma_{u,t_s}(t)=-1$, giving $W_1(\kappa_I(x_t),\delta_0)\le b^{-\sqrt{m^{(u)}}}$.
   *Edge-set check for $\eta_r^{(K)}$ on $1^-$ points:* when $\sigma_{u,t_s}(t)=-1$, adding $+\eta_r^{(K)}\in(0,8b^{r-m_K}]$ cannot flip $ax_t+\eta_r^{(K)}$ across $0$ to $0^+$ whenever $\eta_r^{(K)}<|x_t|\le a|x_t|$, which holds for all $r<m_K-(4k_u+2)m^{(u)}-6$. Since $m_K\ge b^{K^3}L_{t_s}m^{(t_s)}$, the excluded fraction of $r\in[0,m_K)$ is at most $\frac{(4k_{t_s}+2)m^{(t_s)}+6}{m_K}=O(b^{-K^3})\to0$ (and passing from $R_K$ to $y$ affects fraction $O(b^{-(K+1)^3})\to0$).
2. *Melted zone $r_*+\Delta_u<r_u<m^{(u)}-\Delta_u$* (proportion $\beta_{u,d}(I)+O(b^{-n_0^3/2})$): with $H_u=\lfloor b^{\sqrt{m^{(u)}}/2}/16\rfloor$, every $1\le h\le H_u$ satisfies $h|x_t|\le4M_sH_ub^{-\Delta_u}<\frac14b^{-\sqrt{m^{(u)}}/2}<\frac12$, hence $\|hx_t\|=h|x_t|\ge\frac14b^{r_u-dm^{(u)}}$ and $|\widehat{\kappa_I(x_t)}(h)|\le\frac1{2I\|hx_t\|}\le2b^{-\sqrt{m^{(u)}}}$. By Erdős–Turán, $D(\kappa_I(x_t))=O(b^{-\sqrt{m^{(u)}}/2})\to0$, so $W_1(\kappa_I(x_t),\lambda)\to0$ (contributing $f_0=f_1=\frac12+o(1)$ in base 2).
3. *Buffer zones* $[r_*-\Delta_u,r_*+\Delta_u]$ and $[m^{(u)}-\Delta_u,m^{(u)})$: total proportion $\le(3\Delta_u+2)/m^{(u)}=O(b^{-n_0^3/2})$.
4. *Partial band $a=I+1$:* if $I\ge2^s$, its weight $r_0'/M\le1/I\le2^{-s}\to0$; if $I<2^s$, then $\beta_{u,d}(I)=O(s/m^{(1)})\to0$ and $(I+1)|x_t|\le4\cdot2^sM_sb^{r_u-dm^{(u)}}\to0$ for $r_u<m^{(u)}-\Delta_u-s$, matching $\delta_0$ and preserving $\sigma_{u,t_s}(t)$.

Putting $\gamma_K(N):=\sum_{u=1}^{t_s}\sum_{d=1}^{4k_u+2}w_{u,d}^{(t_s)}(1-\beta_{u,d}(I))\in[0,\alpha_s]$, Parts A and B yield

```math
W_1\Bigl(\mu_N^{\mathrm{emp}}(y),\ \bigl(1-\gamma_K(N)\bigr)\lambda+\gamma_K(N)\delta_0\Bigr)\to0
```

uniformly over $N\in[m_K,m_{K+1}]$, with $\gamma_K(m_K)=\alpha_s$ and $\gamma_K(m_{K+1})=0$ (since $I=m_{K+1}/m_K\ge D_{K-1}\ge b^{(4k_{t_s}+2)m^{(t_s)}}$ forces $\beta_{u,d}(I)=1$ for all $u,d$). Moreover, in base $b=2$, because $\sigma_{u,t_s}(t)$ is **independent of $(r_u,d)$** on $E_{u,d}^{(t_s)}$, melting removes the exact same fraction $\beta_{u,d}(I)$ of $0^+$ and $1^-$ mass in stratum $(u,d)$. Since every stratum bias (5.4) is **nonnegative** and $1-\beta_{u,d}(I)\in[0,1]$,

```math
0\le f_0(N;y)-f_1(N;y)+o(1)=\sum_{u=1}^{t_s}\sum_{d=1}^{4k_u+2}w_{u,d}^{(t_s)}\bigl(1-\beta_{u,d}(I)\bigr)\frac{(s+u)!}{(s+t_s)!}\le B^{(t_s)}\le\frac3{2s+3},
```

so $|f_0(N;y)-\frac12|\le\frac2{2s+3}+o(1)\to0$ uniformly over all $N\in[m_K,m_{K+1}]$.

**Step 4: Second $-1$ reset shell $n=n_{s+1}+1$ and conclusion.** Because both $Q_{n_{s+1}}$ and $Q_{n_{s+1}+1}$ equal $1-q$, Phase 21 Proposition D2.5 (converse) / Theorem 2 gives $D_N(y;b)\to0$ (hence $\mu_N^{\mathrm{emp}}(y)\to\lambda$ and $f_0(N;y)\to\frac12$ in base 2) uniformly across $[m_{n_{s+1}+1},m_{n_{s+1}+2}]$. Combining Steps 1–4 across all rounds $s\ge s_0$ gives $D^-(y;b)=0$, $D^+(y;b)=\lim_{s\to\infty}\alpha_s=\alpha$, exact discrepancy limit set $[0,\alpha]$, exact weak\* limit set $\{(1-\gamma)\lambda+\gamma\delta_0:\ 0\le\gamma\le\alpha\}$, and (when $b=2$) $f_0(N;y)\to\frac12$, $f_1(N;y)\to\frac12$ along all $N$. Finally, since $D^-(y;b)=0<\alpha=D^+(y;b)$ whereas every rational number has convergent $D_N$, $y$ (and hence $x=1/y$) is irrational. $\square$

---

## 6. Lean 4 finite cores (kernel-verified results and remaining blueprints)

Two Lean modules already kernel-verify the algebraic core of Phase 21–22 reciprocals:

- [`NormalityChecker/NormalReciprocalCore.lean`](../../NormalityChecker/NormalReciprocalCore.lean): `band_identity` (Lemma D2.1), `signed_band_identity` (Proposition D2.5), `sum_residues_cexp_eq_zero` (Lemma D2.2), and `eulerAutomaton_purely_periodic`.
- [`NormalityChecker/RadixPowerTower.lean`](../../NormalityChecker/RadixPowerTower.lean): `mul_pow_sub_one_dvd_pow_sub_one_iff`, `orderOf_mul_pow_sub_one`, `orderOf_mul_pow_sub_one_of_orderOf`, `orderOf_mul_pow_add_one`, and `orderOf_mul_pow_add_one_of_orderOf` — which **kernel-verify** Theorem 1(1) under $D\mid b^m-1$, Theorem 1(2), and Theorem 1(3).

The remaining finite algebraic and analytic cores from this note are blueprint targets for future formalization:

```lean
namespace NormalityChecker.NormalReciprocalPeriods

/-- Hull-Dobell radical: product of distinct prime factors of `D`, times `2` if `4 ∣ D`. -/
def radStar (D : ℕ) : ℕ :=
  (if 4 ∣ D then 2 else 1) * ∏ p ∈ D.primeFactors, p

/-- **Theorem 1(1) (wider Hull-Dobell order lifting, minus sign).**
Extends `RadixPowerTower.orderOf_mul_pow_sub_one` from `D ∣ b^m - 1` to `radStar D ∣ b^m - 1`. -/
theorem orderOf_mul_pow_sub_one_radStar {b m D : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (hcop : Nat.Coprime b D) (hHD : radStar D ∣ b ^ m - 1) :
    orderOf (b : ZMod (D * (b ^ m - 1))) = m * D := by
  sorry

/-- **Lemma 2.1 (exact partial-band inequality, constant 3 → 1).** -/
theorem partial_band_count_le {d' I m r₀ : ℕ} (hd' : 1 ≤ d') (hr₀ : r₀ < m) :
    d' * (m * (I / d') + if d' ∣ I + 1 then r₀ else 0) ≤ I * m + r₀ := by
  sorry

/-- **Lemma 2.2 (divisor-sum bound for `∑ gcd(h, D) / h`).** -/
theorem sum_gcd_div_le (D H : ℕ) (hD : 1 ≤ D) :
    ∑ h ∈ Finset.Icc 1 H, ((Nat.gcd h D : ℝ) / h) ≤
      ∑ d ∈ D.divisors.filter (· ≤ H), ∑ j ∈ Finset.Icc 1 (H / d), (1 : ℝ) / j := by
  sorry

/-- **Lemma 2.4(1) (exact shifted-uniform-grid interval discrepancy).**
Every shifted `D`-point grid `α + j/D` has excess at most `1 / D` on every `[a, c) ⊆ [0, 1]`. -/
theorem shifted_grid_interval_excess_le (D : ℕ) (hD : 1 ≤ D) (α : ℝ) (a c : ℝ)
    (hac : 0 ≤ a ∧ a ≤ c ∧ c ≤ 1) :
    |((Finset.range D).filter (fun j => a ≤ Int.fract (α + (j : ℝ) / D) ∧
        Int.fract (α + (j : ℝ) / D) < c)).card / (D : ℝ) - (c - a)| ≤ 1 / (D : ℝ) := by
  sorry

/-- Exact rational tail `τ_i(q) = (1 - q^L)^{-1} ∑_{u=1}^L c_{(i+u) mod L} q^u` for a factor
`P * A = ∑_{j < L} X^j` with `deg A < L - 1` (so `c_j = A.coeff j - A.coeff (j - 1)` mod `L`). -/
def cyclotomicTail (L : ℕ) (A : Polynomial ℤ) (i : ℕ) (q : ℚ) : ℚ :=
  (∑ u ∈ Finset.Icc 1 L,
    (((A.coeff ((i + u) % L) - A.coeff ((i + u + L - 1) % L)) : ℤ) : ℚ) * q ^ u) /
    (1 - q ^ L)

/-- **Lemma 5.2(2) (generalized cyclotomic band identity with exact rational tail).** -/
theorem cyclotomic_band_identity {b m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hL : 2 ≤ L)
    (P A : Polynomial ℤ) (hPA : P * A = ∑ j ∈ Finset.range L, Polynomial.X ^ j)
    (hdeg : A.natDegree < L - 1)
    {R : ℚ} (hcop : Nat.Coprime b R.den) (hT : orderOf (b : ZMod R.den) ∣ m)
    (hPne : Polynomial.eval ((b : ℚ)⁻¹ ^ m) (P.map (Int.castRingHom ℚ)) ≠ 0) (i r : ℕ) :
    ∃ z : ℤ,
      (b : ℚ) ^ (i * m + r) * (R / Polynomial.eval ((b : ℚ)⁻¹ ^ m) (P.map (Int.castRingHom ℚ))) =
        (A.coeff (i % L) : ℚ) * (b : ℚ) ^ r * R +
          (b : ℚ) ^ r * R * cyclotomicTail L A i ((b : ℚ)⁻¹ ^ m) + (z : ℚ) := by
  sorry

/-- **Proposition 5.1 (exact positive, negative, and trailing-zero band counts for `P_k`).** -/
theorem cyclotomic_Pk_sign_counts (k : ℕ) (hk : 1 ≤ k) (A : Polynomial ℤ)
    (hPA :
      (∑ s ∈ Finset.range (2 * k + 1), (-Polynomial.X : Polynomial ℤ) ^ s) *
      (∑ t ∈ Finset.range (2 * k + 3), (-Polynomial.X : Polynomial ℤ) ^ t) * A =
        ∑ j ∈ Finset.range (2 * (2 * k + 1) * (2 * k + 3)), Polynomial.X ^ j) :
    let L := 2 * (2 * k + 1) * (2 * k + 3)
    ((Finset.range L).filter (fun i => 0 < A.coeff i)).card = 2 * (k + 2) * (2 * k + 1) ∧
    ((Finset.range L).filter (fun i => A.coeff i < 0)).card = 2 * k * (2 * k + 1) ∧
    (∀ i < L, A.coeff i = 0 ↔ L - (4 * k + 2) ≤ i) := by
  sorry

end NormalityChecker.NormalReciprocalPeriods
```

The `sorry` markers denote blueprint proof targets (not gaps in the paper proofs).

---

## 7. Verification record

```sh
python -B scripts/phase22_reciprocals.py
```

Pure Python standard library; runs in $1.38\text{ s}$, performs $21{,}443$ checks across five sections, and exits $0$. Per-section check counts:

| Section | Checks | Nature of checks |
|---|---|---|
| 1. Exact periods (minus) & Hull–Dobell | 2,693 | Exact integer/modular arithmetic |
| 2. Weyl, divisor-sum, grid & Koksma | 14,326 | Exact integer inequalities + 48-bit float Weyl/discrepancy measurements |
| 3. Signed periods | 2,456 | Exact integer/modular arithmetic |
| 4. Sign trajectories & digits | 92 | Exact order checks + 40-bit float orbit measurements |
| 5. Cyclotomic family $P_k$ | 1,876 | Exact $\mathbb Z[q]$/$\mathbb Q$ identities + 40-bit float orbit measurements |
| **Total** | **21,443** | |

Summary of verified identities and finite-scale measurements:

1. **Exact periods (minus) and Hull–Dobell lifting.** Verified $T_k=m_kD_{k-1}$ across 15 sequences in bases $b=2,\dots,10$, including the boundary case $b=2,m=(1,2,6)\to T=(1,2,18)$ and $b\equiv3\pmod4$ with odd exponents ($b=3,7$ with $m=(1,3,18)\to T=(1,6,936),(1,18,36936)$). Verified the full Hull–Dobell lifting theorem and bijectivity of $S_i(b^m)\bmod D$ on all $590$ valid triples $(b,m,D)$ with $2\le b\le10$, $1\le m\le6$, $1\le D\le100$ (including $196$ triples where $D\nmid(b^m-1)$), and confirmed the 2-adic sharpness counterexamples $(3,1,4)\to T=2<4$ and $(3,1,8)\to T=4<8$.
2. **Sharpened Weyl, divisor-sum, grid, and Koksma bounds.** Verified Lemma 2.1 on $14{,}040$ tuples and Lemma 2.2 on $11$ moduli up to $5040$. Comparing the main $D_{K-2}$ and $\omega_{K-1}$ Erdős–Turán terms at $\omega_{K-1}=D_{K-2}$ (omitting $c_b(H)/m_K$): at $D_3^{\mathrm{bal}}=45(2^{36}-1)=3{,}092{,}376{,}453{,}075$ ($\tau=1152$), Phase 22 gives $1.4130\times10^{-8}$ versus Phase 21's $5.5841\times10^{-6}$ ($395.2\times$); at Phase 21's $D_3=45(2^{48}-1)=12{,}666{,}373{,}951{,}979{,}475$ ($\tau=1920$), Phase 22 gives $7.3533\times10^{-12}$ versus $8.7251\times10^{-8}$ ($11{,}865.6\times$). Verified $D(\mu_K)\le1/D_{K-1}$ and exact circular $W_1(\mu_K,\lambda)\le1/(4D_{K-1})$ in bases $2,3,5$ (for $b=2,k=3,D_2=45$: $D(\mu_3)=0.019676\le0.022222$, $W_1=0.005097\le0.005556$). For $b=2,m=(2,4,48,43200)$, checked the sharpened constant-$1$ Weyl bound and Koksma lower bound across $7$ prefixes $N\in\{m_4,\,m_4+7T_3,\,2m_4-1,\,3m_4-1,\,3m_4,\,\frac72m_4,\,4m_4-1\}$ and $7$ frequencies $h\in\{1,2,3,5,9,15,45\}$ (48-bit truncation): the worst ratio $|W_h|/\text{bound}$ for $h<45$ is $0.8047$ at $N=3m_4-1=129{,}599$, $h=15$, where $|W_{15}|=0.3102\le0.3855$ (Phase 21's constant-$3$ bound is $1.0522$); at $N=m_4=43{,}200$, $|W_{45}(m_4)|=0.93071$ and Koksma gives $0.00658\le D_{m_4}=0.01970$. For balanced $\omega_k=D_{k-1}$ in base 2 at $K=6$, $\log_2D_4=72941.5$ against $\log_2\log_2m_7=100.14$ (ratio $728.4$).
3. **Exact signed periods.** Verified $T_k(\varepsilon)=m_kD_{k-1}(\varepsilon)$ ($\varepsilon_k=-1$) and $T_k(\varepsilon)=2m_k$ ($\varepsilon_k=+1$) across all $9$ bases $b=2,\dots,10$ and all $8$ sign triples ($72$ runs) plus $4$ edge-case runs at $b=2,m_1=1$, and verified $\operatorname{ord}_{D(b^m+1)}(b)=2m$ on $448$ triples $(b,m,D)$.
4. **Sign trajectories, melting illustration, and oriented digits (40-bit orbit measurements).** For pure $+1$ with the non-tetration sequence $m_k=2^k k!$ ($2,8,48,384,3840$), $D(\mu_k)$ climbs to $0.90161$ ($f_0=0.96875=31/32$, $1^-=0.0000$) at $k=5$ in base 2 and $0.84827$ ($f_0=0.93750$, $1^-=0.0000$) at $k=4$ in base 3. For $r$-runs ($r=1,2,3$) after a $-1$ reset: in base 2, $D=0.50496,0.75215,0.87591$ and $f_0=0.75331,0.87665,0.93833$ against $1-2^{-r}$ and $1-2^{-r-1}$; in base 3, $D=0.50422,0.75188,0.87582$ and $f_0=0.66875,0.83437,0.91719$ against $1-2^{-r}$ and $1-\frac232^{-r}$. The continuous sweep $D_N\approx1-\frac12\theta_K(N)$ across $[3024,6048]$ agrees to within $0.015$. At $m=(2,4,24)$ ($b=2$), a finite-scale illustration of the $-1$ melting transition after a $+1$ shell shows $D$ decreasing monotonically across $I=1,8,64,512$ ($0.5389\to0.5049\to0.4358\to0.3766$, within $0.08$ of the asymptotic $\frac12(1-\beta)$).
5. **Cyclotomic family $P_k(q)$.** Verified Proposition 5.1 completely in exact $\mathbb Z[q]$ arithmetic for all $k=1,\dots,25$ (zero internal zeros, exact counts $2(k+2)(2k+1)$ positive, $2k(2k+1)$ negative, $4k+2$ trailing zero-bands, exact range $[-2k,2k+2]$, $\max|c_s|\le2$, plus the exact closed form of $G_k$ and exact zero-band tail identity $\tau_{L_k-d}^{(k)}(q)=q^d/P_k(q)$ for $k=1,\dots,12$). Verified Lemma 5.2 in exact rational arithmetic (using `cyclotomicTail`) across bases $b=2,3,5,10$ on all $30$ bands of $P_1$, including $\frac12b^{-dm}R_0\le\tau\le2b^{-dm}R_0$ on all $6$ trailing $0^+$ zero-bands. For concrete $0^+/1^-$ mixing in base 2 (40-bit measurement), applying $P_4$ ($m=256$, $T=50{,}688$) to $R_{\mathrm{init}}=(1+2^{-32})^{-1}(1+2^{-128})^{-1}$ ($D=0.8906$, $f_0=0.7500$) kept $D=0.8829$ while collapsing $f_0$ to $0.5909$ (matching the exact recursion prediction $13/22=0.5909$, with $0^+=0.5187$, $1^-=0.3332$, $f_{00}=0.5772$, $f_{11}=0.3954$). Verified the consecutive-$k$ prescribed-$\alpha$ product on $\alpha\in\{1/\pi,\sqrt2/2,1/e,0.123456,0.9\}$.

All finite orbit values are finite-scale measurements (40-bit or 48-bit float truncations, not interval certificates); they test the stated identities and finite inequalities and are separate from the asymptotic proofs above.

---

## 8. Open problems

1. **Closing the one-iterated-logarithm gap in Theorem 3 and optimality of $\omega_k=D_{k-1}$.** Theorem 3(1) achieves $D_N(y;b)\le\bigl(\exp^{(r)}((\ln^{(r+1)}N)^A)\bigr)^{-1}$ for balanced $\omega_k=D_{k-1}$, whereas Theorem 3(2) rules out $\bigl(\exp^{(r)}((\ln^{(r)}N)^\varepsilon)\bigr)^{-1}$ across all admissible sequences. What is the exact optimal rate inside the admissible family (A1)–(A2), and does balanced $\omega_k=D_{k-1}$ attain it?
2. **Normality and discrepancy barrier under relaxed Hull–Dobell divisibility.** Under $\operatorname{rad}^*(D_{k-1})\mid(b^{m_k}-1)$ with $D_{k-1}\nmid(b^{m_k}-1)$ and $m_{k+1}/T_k\to\infty$, Theorem 1(1) preserves $T_k=m_kD_{k-1}$, but neither normality of $y$ nor the Koksma barrier of Theorem 3(2) is proved (§3.2).
3. **Convergent intermediate discrepancy for reciprocals of kernel elements.** Theorem 6(2) realizes every $\alpha\in[0,1]$ as $D^+(1/x;b)=\alpha$ with $D^-(1/x;b)=0$ for an irrational $x\in K_b$, and Theorems 2 and 4(2) realize the convergent endpoints $\lim D_N(1/x;b)\in\{0,1\}$. Does there exist, for every $\alpha\in(0,1)$, an irrational $x\in K_b$ whose reciprocal has a **convergent** discrepancy $\lim_{N\to\infty}D_N(1/x;b)=\alpha$ (with $D^-=D^+=\alpha$)? Our cyclotomic construction requires periodic $-1$ resets to push the $\lambda$-component grid denominator $D_{n_s}\to\infty$, which brings $D^-$ back to $0$.
4. **Faster rates outside the admissible family.** Theorem 3(2) rules out $D_N(1/x;b)=O(N^{-c})$ and even $O(\exp(-(\ln N)^c))$ across every admissible product $x=\prod(1-b^{-m_k})$. Does any irrational $x\in K_b$ (not necessarily an admissible product) satisfy $D_N(1/x;b)=O(N^{-c})$ for some $c>0$, or does $x\in K_b$ impose an intrinsic rate barrier on $1/x$?
5. **Simply normal, nonnormal reciprocals in base $b\ge3$.** Theorem 6(1)–(2) gives explicit base-$2$ simply normal reciprocals of $x\in K_2$ at every $D^+\in(0,1]$ (including $1/x\in K_2$). For $b\ge3$, no element of $K_b$ can be simply normal, and any measure $(1-\alpha)\lambda+\alpha\delta_0$ with $\alpha>0$ biases digit $0$ or digit $b-1$. Can a reciprocal $1/x$ of an $x\in K_b$ ($b\ge3$) be simply normal in base $b$ yet nonnormal?
6. **Normality of $P_b=1/E_b$.** As noted in Phase 21, the constructions here do not resolve whether the partition generating function $1/E_b=\prod_{k\ge1}(1-b^{-k})^{-1}$ is normal in base $b$.
