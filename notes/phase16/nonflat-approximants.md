# Non-flat approximants to ln 2: full balanced completeness, unbalanced trace bounds, and Padé / Chebyshev-pole integrals

**Theorem 1 (Universal balanced completeness; paper proof, exact checks).** Let $f \in \mathbb{Z}[X]$ be any monic balanced polynomial ($\mu = A$ in Phase 15 Theorem C), so every root has the form $\alpha = 2^{a/e}\zeta$ with $a \ge 0$, $e \ge 1$, $\gcd(a,e) = 1$, and $\zeta$ a root of unity. Put
```math
r = \begin{cases} e & \text{if } e \text{ is odd,} \\ e/2 & \text{if } e \text{ is even.} \end{cases}
```
Then there exists a monic **flat** balanced polynomial $g \in \mathbb{Z}[Y]$ (every root of radius $2^a$ if $e$ is odd, or $2^{a/2}$ if $e$ is even) such that $f(X) = g(X^r)$. Consequently $p_j(f) = 0$ whenever $r \nmid j$, $p_{rm}(f) = r\,p_m(g)$ for all $m \ge 1$, and for every integer base $t > a/e$ and every real cutoff $x > 0$,
```math
S_{f,t}(x) = \sum_{1 \le j \le \frac{x}{t - a/e}} \frac{p_j(f)}{j\,2^{tj}} = S_{g, rt, n}(x), \qquad n = 2r(t - a/e),
```
which by Phase 15 Theorem A equals an explicit integer combination of $\{A_k, G_t\}$ at every real cutoff $x > 0$. **Corollary (paper deduction from Phase 15):** For integer bases $t > a/e$ with homogeneous cutoffs, no finite rational combination of balanced algebraic trace sources of *any* degree or *any* radius $2^{a/e}$ can escape the Phase 14/15 real+Gaussian alphabet or lower the optimal denominator rate $5/12$ (or second rate $13/30$).

**Theorem 2 (Lagrange $2$-adic non-cancellation and unbalanced full-rate lower bound; paper proof).** Let $f \in \mathbb{Z}[X]$ be squarefree monic of degree $d$ with minimal $2$-adic root valuation $\mu$ and maximal complex root modulus $2^A$ ($\mu < A < t$). Then there is a constant $C_f \ge 0$ such that $\min_{J-d+1 \le j \le J} v_2(p_j) \le \mu J + C_f$ for every $J \ge d$. Hence for any fixed combination $S = c_0 S_{f,t} + S_{\mathrm{bal}}$ ($c_0 \neq 0$) with $S(\infty) = \log 2$ truncated at the analytic cutoff $J = \lceil N/(t-A) \rceil$ required for shifted error $O(1/N)$,
```math
\limsup_{N \to \infty} \frac{\log q_N}{N} \ge \frac{A - \mu}{t - A}\log 2 + \int_{\{x > 0 : S(x) \neq 0\}} \frac{dx}{x^2}.
```
When $\mu$ is attained by a unique root of minimal valuation in $\overline{\mathbb{Q}}_2$ (e.g. $1 + \sqrt{-7}$, $3 + \sqrt{-7}$), $\limsup$ sharpens to $\lim$. *(Finite search)*: Across $7{,}495$ irreducible unbalanced polynomials of degrees $2, 3, 4$ with $\{2,3,5,7\}$-smooth $|f(2^t)|$, the lowest combined rate found is $0.41885$ (for $X^4 + 2X + 4$, $t = 3$), still above $5/12 = 0.41667$.

**Theorem 3 (Shifted Padé relation vs. $\ln 2$-free rounded Chebyshev-pole integrals; paper proof + Lean core, exact checks).**
1. For any rational approximation $p_n/q_n$ to $\ln 2$ with $|\ln 2 - p_n/q_n| \asymp 2^{-N}$, $q_n = 2^{e_n} q_n^{\mathrm{odd}}$ ($e_n \le N$), and irrationality exponent $\tau = -\log|\ln 2 - p_n/q_n| / \log q_n$, the shifted reduced denominator satisfies
```math
\frac{\log q_N}{N} = \left(\frac{1}{\tau} - \frac{e_n}{N}\right)\log 2.
```
*(Finite experiments)*: All tested unrounded Alladi–Robinson Padé ($0.54318$ naive, $0.51193$ at $n=60$), asymmetric Legendre/beta integrals $I_n(a,b,c)$ (lowest observed $0.44463$), and simultaneous Type II Padé approximants at $z = 1/2$ (lowest observed $0.60093$) remain above $5/12$.
2. **Breaking $5/12$ with explicit $\ln 2$-free rounded Chebyshev-pole integrals (sparse in $N$, extending to all $N$ via a $2^{O(1)}$ scaling factor, with no persistent shift window).** For any pole decomposition $\ln 2 = \sum_i c_i \int_0^1 \frac{dx}{a_i - \sigma_i x}$ ($a_i \in \mathbb{Z}_{\ge 1}$, $\sigma_i \in \{\pm 1\}$, $a_i - \sigma_i x > 0$ on $[0,1]$), normalizing $T_D(2x-1)/T_D(\sigma_i a_i)$ at each pole and rounding the scaled quotient polynomial $R_{\mathrm{tot}}(x)$ coefficientwise to $Q_D(x) \in \mathbb{Z}[x]$ (a purely polynomial construction using **no knowledge of $\ln 2$**) produces an explicit rational $Y_N = -2^{-w}\int_0^1 Q_D(x)\,dx$ at $N = e(D) - w$ with $|2^N \ln 2 - Y_N| = O(1/N)$ ($w = \lceil \log_2(D(\ln D + 1)) \rceil + 2 = O(\log N)$) and $q_N \mid 2^w \mathrm{lcm}(1, \dots, D)$ (denominator divisibility and rounding-error master bound are kernel-verified in [ChebyshevPoleApproximation.lean](../../NormalityChecker/ChebyshevPoleApproximation.lean)). Along the sequence $N = N(D)$ (and for all large $N$ by adjusting $e$ within $O(1)$), this achieves:
   - **Single pole $1/(1+x)$:** $\limsup (\log q_N)/N \le \frac{\log 2}{2\log(1+\sqrt{2})} \approx \mathbf{0.393220} < 5/12$ (certified $0.40530$ at $D = 240, N = 596$);
   - **Two-stride poles $2/(4-x) + 1/(8+x)$:** $\limsup (\log q_N)/N \le \frac{\log 2}{2\log(2+\sqrt{3})} \approx \mathbf{0.263162} < 5/12$ (certified $0.26329$ at $D = 160, N = 594$);
   - **Telescoping $M$ poles $\sum_{a=M+1}^{2M} \frac{1}{a-x}$:** $\limsup (\log q_N)/N \le \frac{1}{\log_2(2M + 1 + 2\sqrt{M(M+1)})} \to \mathbf{0}$ as $M \to \infty$ (certified $0.19696$ at $M = 8, D = 120, N = 597$).

[Phase 15 arithmetic lifts](../phase15/arithmetic-lifts.md) · [Verification script](../../scripts/phase16_nonflat.py)

## 1. Complete classification of balanced algebraic trace sources

**Lemma 1 (Cyclotomic disjointness of $2^{1/e}$).** For every integer $e \ge 1$, $[\mathbb{Q}^{\mathrm{ab}}(2^{1/e}) : \mathbb{Q}^{\mathrm{ab}}] = r$, where $r = e$ if $e$ is odd and $r = e/2$ if $e$ is even. Equivalently, $\mathbb{Q}(2^{1/e}) \cap \mathbb{Q}^{\mathrm{ab}} = \mathbb{Q}$ ($e$ odd) or $\mathbb{Q}(\sqrt{2})$ ($e$ even).

*Proof.* Let $s = [\mathbb{Q}^{\mathrm{ab}}(2^{1/e}) : \mathbb{Q}^{\mathrm{ab}}] \mid e$. The minimal polynomial of $2^{1/e}$ over $\mathbb{Q}^{\mathrm{ab}}$ divides $X^e - 2$, so its constant term has the form $(-1)^s \xi (2^{1/e})^s \in \mathbb{Q}^{\mathrm{ab}}$ for some $\xi \in \mu_e \subset \mathbb{Q}^{\mathrm{ab}}$, giving $2^{1/m} \in \mathbb{Q}^{\mathrm{ab}}$ with $m = e/s \mid e$. Every subfield of $\mathbb{Q}^{\mathrm{ab}}$ is Galois over $\mathbb{Q}$, so $\mathbb{Q}(2^{1/m}) \subset \mathbb{R}$ is Galois over $\mathbb{Q}$. Since $X^m - 2$ is Eisenstein at $2$, it is irreducible over $\mathbb{Q}$, so all its roots $\zeta_m^k 2^{1/m}$ must lie in $\mathbb{R}$, forcing $m \in \{1, 2\}$. For odd $e$, $m = 1$ gives $s = e$. For even $e$, $\sqrt{2} = \zeta_8 + \zeta_8^{-1} \in \mathbb{Q}^{\mathrm{ab}}$ gives $s \le e/2$, while $m \le 2$ gives $s \ge e/2$, so $s = e/2$. $\square$

**Proof of Theorem 1.** Assume first that $f$ is monic irreducible and balanced with root $\alpha = 2^{a/e}\zeta_M$ ($\gcd(a,e)=1$, $\zeta_M$ primitive). Put $\beta = \alpha^r = 2^{ar/e}\zeta_M^r$, which has radius $2^a$ ($e$ odd) or $2^{a/2}$ ($e$ even), hence is a flat algebraic integer. Set $C = \mathbb{Q}(\zeta_{\mathrm{lcm}(e,M,8)}) \subset \mathbb{Q}^{\mathrm{ab}}$ and $E = C(2^{1/e})$. By Lemma 1, $[E:C] = r$, so there exists $\tau \in \operatorname{Gal}(E/C)$ with $\tau(2^{1/e}) = \zeta_r 2^{1/e}$ and $\tau|_C = \mathrm{id}$. Then $\tau(\alpha) = \zeta_r^a \alpha$ and $\tau(\beta) = \beta$. Because $\gcd(a, r) = 1$, the $r$ conjugates $\tau^k(\alpha) = \zeta_r^{ak}\alpha$ ($0 \le k < r$) are pairwise distinct over $\mathbb{Q}(\beta)$. Hence $[\mathbb{Q}(\alpha):\mathbb{Q}(\beta)] \ge r$; since $\alpha^r = \beta$, equality holds and $f(X) = g(X^r)$, where $g \in \mathbb{Z}[Y]$ is the minimal polynomial of $\beta$.

Summing $j$-th powers over the $r$ distinct $r$-th roots of each root of $g$ gives $p_j(f) = 0$ when $r \nmid j$ and $p_{rm}(f) = r\,p_m(g)$. Substituting $j = rm$ into $S_{f,t}(x)$ cancels the factor $r$ against $j = rm$ and turns the cutoff $rm \le x/(t - a/e)$ into $2r(t - a/e)m \le 2x$, which is the exact homogeneous cutoff for the flat source $(g, rt, 2r(t-a/e))$. Phase 15 Theorem A then decomposes $S_{g,rt,n}(x)$ into an explicit integer combination of $\{A_k, G_t\}$ at every real $x > 0$. If $f$ is reducible and balanced, every irreducible factor shares the same radius $2^{a/e}$ and collapses identically. $\square$

The script verifies all $44$ irreducible test cases across $e \in \{3, 4, 5, 6, 8, 12\}$ (with $42$ independently subset-certified irreducible) plus the reducible product $X^8 + 4 = (X^4 - 2X^2 + 2)(X^4 + 2X^2 + 2) \mapsto A_{12} - A_6$. Representative decompositions at $t = 1$:

| Source $(e, a, M, b)$ | $r$ | $\deg f$ | Exact cutoff-level collapse at $t = 1$ |
| --- | ---: | ---: | --- |
| $\sqrt{1+i}$ $(4, 1, 16, 1)$ | 2 | 4 | $G_2$ |
| $\sqrt{-1+i}$ $(4, 1, 16, 3)$ | 2 | 4 | $A_{12} - A_6 - G_2$ |
| $2^{1/4}\zeta_{32}$ $(4, 1, 32, 1)$ | 2 | 16 | $A_{24} - A_{12}$ |
| $2^{1/4}\zeta_{48}$ $(4, 1, 48, 1)$ | 2 | 8 | $A_6 - A_{12} + G_2 + G_5$ |
| $2^{3/4}\zeta_8$ $(4, 3, 8, 1)$ | 2 | 4 | $A_2 - A_1$ |
| $2^{1/3}\zeta_9$ $(3, 1, 9, 1)$ | 3 | 6 | $A_6 - A_2$ |
| $2^{2/5}\zeta_5$ $(5, 2, 5, 1)$ | 5 | 5 | $A_3$ |
| $2^{1/6}\zeta_{24}$ $(6, 1, 24, 1)$ | 3 | 6 | $G_3$ |
| $2^{1/8}\zeta_{32}$ $(8, 1, 32, 1)$ | 4 | 8 | $G_4$ |
| $2^{1/12}\zeta_{48}$ $(12, 1, 48, 1)$ | 6 | 12 | $G_6$ |

## 2. Unbalanced algebraic trace sources ($\mu < A < t$)

**Proof of Theorem 2.** Let $\alpha_1, \dots, \alpha_d$ be the distinct roots of squarefree $f \in \mathbb{Z}[X]$ in $\overline{\mathbb{Q}}_2$ with $v_2(\alpha_1) = \mu$. The Lagrange interpolation polynomial $L_1(X) = \frac{f(X)}{(X - \alpha_1)f'(\alpha_1)} = \sum_{r=0}^{d-1} c_r X^r$ satisfies $L_1(\alpha_1) = 1$ and $L_1(\alpha_i) = 0$ for $i > 1$, so for every $J \ge d$,
```math
\alpha_1^{J - d + 1} = \sum_{i=1}^{d} \alpha_i^{J - d + 1} L_1(\alpha_i) = \sum_{r=0}^{d-1} c_r p_{J - d + 1 + r}.
```
Putting $C_f = \max(0,\, -(d-1)\mu - \min_r v_2(c_r))$ gives $\min_{J-d+1 \le j \le J} v_2(p_j) \le \mu J + C_f$ (since $v_2(\alpha_1^{J-d+1}) = (J-d+1)\mu$). For each large $J$, choose $j^* \in [J-d+1, J]$ with $v_2(p_{j^*}) \le \mu J + C_f$, and let $N_{j^*} := \lfloor j^*(t - A) \rfloor$ (so the analytic cutoff $\lceil N/(t-A)\rceil$ jumps from $j^* - 1$ to $j^*$ across $N_{j^*}$ and $N_{j^*} - 1$, or between consecutive cutoffs within $O_f(1)$ of $N_{j^*}$). Writing the single term $T_{j^*} = c_0 p_{j^*} / (j^* 2^{t j^*})$ as the partial-sum difference $S_{f,t}(\text{cutoff } j^*) - S_{f,t}(\text{cutoff } j^*-1)$, at least one of the two consecutive partial sums $S(\text{cutoff } j^*)$ or $S(\text{cutoff } j^*-1)$ must satisfy $v_2 \le v_2(T_{j^*}) = v_2(c_0) + v_2(p_{j^*}) - t j^* - v_2(j^*)$ (since balanced terms have $2$-adic valuation $\ge -N - O(\log N)$ after shifting by $2^N$). Rescaling by $2^{N_{j^*} + O_f(1)}$ puts that partial sum back among the shifted prefixes $Y_N$, forcing $v_2(\operatorname{den}(Y_N)) \ge j^*(t - \mu) - N_{j^*} - O_f(\log N_{j^*}) = \frac{A - \mu}{t - A} N_{j^*} - O_f(\log N_{j^*})$ along a subsequence of cutoffs $N \to \infty$. For odd primes $p > J^{1/2}$ outside the fixed coefficient denominators, the homogeneous cutoff $p\ell \le N/(t - A) \iff \ell \le (N/p)/(t - A)$ preserves the Frobenius shadow $p Y_N \equiv 2^N S(N/p) \pmod p$ even when $t - A$ is irrational, adding $\int_{S \neq 0} x^{-2}\,dx$ to $\frac{\log q_N}{N}$. $\square$

Searching all monic irreducible unbalanced polynomials of degrees $2, 3, 4$ in the box of `scripts/phase16_nonflat.py` finds $7{,}495$ pairs $(f, t)$ with $\{2,3,5,7\}$-smooth $|f(2^t)|$. Combining the lowest-$\rho_2$ candidates with the Phase 14 alphabet yields:

| Polynomial $f(X)$ [low..high] | $d$ | $t$ | $\mu$ | $A$ | $\rho_2 = \frac{A-\mu}{t-A}\ln 2$ | Best $\rho_{\mathrm{odd}}$ found | Full rate $\rho_2 + \rho_{\mathrm{odd}}$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `[4, 2, 0, 0, 1]` ($X^4 + 2X + 4$) | 4 | 3 | $1/3$ | $0.6760$ | $0.1022$ | $0.3167$ | **$0.4189$** |
| `[1, 0, -1, 1]` ($X^3 - X^2 + 1$) | 3 | 2 | $0$ | $0.2028$ | $0.0782$ | $0.3898$ | $0.4680$ |
| `[5, 1, 0, 1]` ($X^3 + X + 5$) | 3 | 5 | $0$ | $0.8608$ | $0.1442$ | $0.3333$ | $0.4775$ |
| `[4, 1, 0, 1]` ($X^3 + X + 4$) | 3 | 4 | $0$ | $0.7683$ | $0.1648$ | $0.3167$ | $0.4815$ |
| `[-3, 3, -2, 1]` ($X^3 - 2X^2 + 3X - 3$) | 3 | 3 | $0$ | $0.5536$ | $0.1568$ | $0.3421$ | $0.4989$ |
| `[2, -2, 0, 0, 1]` ($X^4 - 2X + 2$) | 4 | 2 | $1/4$ | $0.5346$ | $0.1346$ | $0.4167$ | $0.5513$ |

None improves upon $5/12 \approx 0.41667$: the unavoidable $2$-adic penalty $\rho_2$ offsets the smaller odd-prime rate from larger strides $t - A$.

## 3. Padé, asymmetric Legendre integrals, simultaneous Padé, and Chebyshev-pole integrals

### 3.1 Shifted rates for unrounded Padé and Legendre families

For a rational approximant $p_n/q_n$ to $\ln 2$ with error $2^{-N}$ and $q_n = 2^{e_n} q_n^{\mathrm{odd}}$ ($e_n \le N$), shifting by $2^N$ erases all $2$-adic factors up to $2^N$, giving $(\log q_N)/N = (1/\tau - e_n/N)\log 2$, where $\tau = -\log|\ln 2 - p_n/q_n| / \log q_n$. For asymmetric Legendre integrals $I_n(a,b,c) = \int_0^1 \frac{x^{an}(1-x)^{bn}}{(1+x)^{cn+1}}\,dx = c_n\ln 2 - r_n$, Möbius substitution $x \mapsto (1-x)/(1+x)$ yields the exact symmetry $I_n(a,b,c) = 2^{(b-c)n} I_n(b,a,a+b-c)$, and $2^{(b-c)n} \mid c_n$ whenever $b > c$. Nevertheless, the saddle-point growth of the odd part of $c_n$ keeps every tested unrounded Legendre integral and simultaneous Type II Padé approximant above $5/12$:

| Family | Parameters | $N$ | Shifted $(\log q_N)/N$ | $v_2(q_N)$ |
| --- | --- | ---: | ---: | ---: |
| Alladi–Robinson / Beukers Padé | $(1,1,1)$, $n=60$ | 296 | $0.51193$ (naive $0.54318$) | 0 |
| Asymmetric Legendre | $(1,1,1)$, $n=28$ | 135 | $0.44463$ | 0 |
| Asymmetric Legendre | $(5,5,3)$, $n=12$ | 281 | $0.44827$ | 0 |
| Asymmetric Legendre | $(4,5,2)$, $n=13$ | 263 | $0.50576$ | 0 |
| Asymmetric Legendre | $(1,2,1)$, $n=28$ | 196 | $0.50756$ | 0 |
| Type II simultaneous Padé | $(\log(1-z),\log(1-z^2))$, $(6,6)$ | 33 | $0.60093$ | 0 |
| Type II simultaneous Padé | $(\log(1-z),\log(1-z^2))$, $(10,10)$ | 58 | $0.65891$ | 0 |
| Type II simultaneous Padé | $(\log(1-z^2),\log(1+z^3))$, $(8,8)$ | 30 | $1.08503$ | 0 |

### 3.2 Breaking $5/12$ with explicit $\ln 2$-free rounded Chebyshev-pole integrals

Let $\ln 2 = \sum_{i=1}^m c_i \int_0^1 \frac{dx}{a_i - \sigma_i x}$ ($c_i \in \mathbb{Z}$, $a_i \in \mathbb{Z}_{\ge 1}$, $\sigma_i \in \{\pm 1\}$, $a_i - \sigma_i x > 0$ on $[0,1]$). For degree $D \ge 1$, let $T(x) = T_D(2x - 1) \in \mathbb{Z}[x]$ be the shifted Chebyshev polynomial of the first kind ($|T(x)| \le 1$ on $[0, 1]$). At each pole $x_i = \sigma_i a_i$, $T(x) - T(x_i) = (a_i - \sigma_i x) P_i(x)$ with $P_i \in \mathbb{Z}[x]$ of degree $D - 1$, giving the exact identity
```math
\sum_{i=1}^m c_i \int_0^1 \frac{T(x)}{T(x_i)(a_i - \sigma_i x)}\,dx
= \ln 2 + \int_0^1 R_{\mathrm{tot}}(x)\,dx,
\qquad
R_{\mathrm{tot}}(x) := \sum_{i=1}^m \frac{c_i}{T(x_i)} P_i(x).
```
Put $e = \lfloor \log_2 \min_i |T(x_i)| \rfloor$, and round each rational coefficient of $2^e R_{\mathrm{tot}}(x)$ to its nearest integer to form $Q_D(x) \in \mathbb{Z}[x]$. This requires **no knowledge of $\ln 2$**. Since $|T(x)| \le 1$ on $[0,1]$ and each coefficient rounding error is at most $1/2$,
```math
\left|2^e \ln 2 + \int_0^1 Q_D(x)\,dx\right|
\le \sum_{i=1}^m |c_i| \frac{2^e}{|T(x_i)|} \int_0^1 \frac{dx}{a_i - \sigma_i x}
+ \frac{1}{2} \sum_{k=1}^{D} \frac{1}{k}
\le C_0 + \frac{1}{2} H_D = O(\log D).
```
Setting $w = \lceil \log_2(D(\ln D + 1)) \rceil + 2 = O(\log D)$, $N = e - w$, and $Y_N = -2^{-w} \int_0^1 Q_D(x)\,dx$ yields $|2^N \ln 2 - Y_N| = O(1/N)$ while $q_N \mid 2^w \mathrm{lcm}(1, \dots, D)$. By the prime number theorem ($\psi(D) = (1 + o(1)) D$), $\log q_N \le (1 + o(1)) D$ while $N \sim e \sim D \log_2 \rho_{\min}$, where $\rho_{\min} = \min_i \bigl(|2x_i - 1| + \sqrt{(2x_i - 1)^2 - 1}\bigr)$:
- Single pole $1/(1+x)$ ($x_1 = -1, |2x_1 - 1| = 3$): $\rho_{\min} = 3 + 2\sqrt{2} = (1+\sqrt{2})^2$, rate $\le \frac{\ln 2}{2\ln(1+\sqrt{2})} = 0.393220 < 5/12$.
- Two-stride poles $2/(4-x) + 1/(8+x)$ ($x_1 = 4, 2x_1 - 1 = 7$): $\rho_{\min} = 7 + 4\sqrt{3} = (2+\sqrt{3})^2$, rate $\le \frac{\ln 2}{2\ln(2+\sqrt{3})} = 0.263162$.
- Telescoping $M$ poles $\sum_{a=M+1}^{2M} \frac{1}{a-x}$ ($x_1 = M+1, 2x_1-1 = 2M+1$): $\rho_{\min} = 2M + 1 + 2\sqrt{M(M+1)}$, rate $\le 1/\log_2(\rho_{\min}) \to 0$ as $M \to \infty$.

Exact certified computations from `scripts/phase16_nonflat.py`:

| Chebyshev-pole family | $D$ | $N$ | $w$ | $(\log q_N)/N$ | Odd rate | $\log_2|\text{err}|$ | $2^{-8}$ window |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Single pole $1/(1+x)$ (limit $0.39322$) | 240 | 596 | 13 | **$0.40530$** | $0.38320$ | $-14.89$ | 6 |
| Single pole $1/(1+x)$ | 400 | 1002 | 14 | **$0.40563$** | $0.39041$ | $-15.62$ | 7 |
| Two-stride $2/(4-x)+1/(8+x)$ (limit $0.26316$) | 80 | 291 | 11 | **$0.27169$** | $0.23596$ | $-12.22$ | 4 |
| Two-stride $2/(4-x)+1/(8+x)$ | 160 | 594 | 12 | **$0.26329$** | $0.24112$ | $-13.39$ | 5 |
| Telescoping $M = 8$ (limit $0.19661$) | 120 | 597 | 12 | **$0.19696$** | $0.17606$ | $-14.05$ | 6 |

*Why this escapes Phase 15 Theorem B and Track 3:* The polynomial $Q_D(x)$ depends on $D$ (hence on $N$) and lies outside the balanced algebraic trace alphabet; by rounding $2^e R_{\mathrm{tot}}(x)$ directly to integer coefficients, it eliminates the exponential odd denominator factor $|T(x_i)|$ that burdens unrounded Padé/Legendre integrals. However, rounding destroys homogeneous prime-band persistence across consecutive shifts $N \mapsto N + 1$, and obtaining a linear precision window ($\ge N/2$ future shifts) incurs a linear $2$-adic shift cost ($w \approx N/2$, raising full rate to $\approx 0.765$ at $D = 120$ for two-stride poles while keeping the odd rate near $0.362$).

## 4. Reproduction

```sh
python3 -B scripts/phase16_nonflat.py
```
