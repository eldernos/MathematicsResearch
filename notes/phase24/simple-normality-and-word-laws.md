# Simple normality, higher-$m$ partition reciprocals $Y_{b,m}$, Euler's square $E_2^2$, rational-scaling Conjecture 5.5, and multi-radix finite-order normality

Phase 24, Track B (Sub-tracks B1–B4). Notation follows [`docs/research-objectives.md`](../../docs/research-objectives.md) and Phase 23 notes [`binary-partition-and-carry-complexity.md`](../phase23/binary-partition-and-carry-complexity.md) (`GF-32`), [`euler-square-and-higher-order-tower.md`](../phase23/euler-square-and-higher-order-tower.md) (`GF-29`), and [`rational-scalings-and-signed-special.md`](../phase23/rational-scalings-and-signed-special.md) (`GF-30`). Fix an integer radix $b \ge 2$. Write $\{t\}$ for the fractional part of $t$, $T_b x = \{b x\}$, and $x = \lfloor x \rfloor + \sum_{n \ge 1} d_n(x) b^{-n}$ for the canonical base-$b$ expansion (not ending in $(b-1)^\infty$), so $d_n(x) = \lfloor b \{b^{n-1} x\} \rfloor \in \{0, \dots, b-1\}$. For a length-$L$ word $w = w_1 \cdots w_L \in \{0, \dots, b-1\}^L$, let
```math
f_w(N; x, b) = \frac{1}{N} \#\bigl\{0 \le n < N : d_{n+1}(x) \cdots d_{n+L}(x) = w\bigr\}
```
be the overlapping word frequency among the first $N$ shifts, and write $D_N(x; b)$ for the extreme interval discrepancy of $\{b^n x\}_{0 \le n < N}$, $D^+(x; b) = \limsup_N D_N(x; b)$, $D^-(x; b) = \liminf_N D_N(x; b)$, $D_\infty(x; b)$ for the limit when it exists, $K_b = \{x \in \mathbb{R} : D_N(x; b) \to 1\}$, $F_b = \frac{1}{b-1}\mathbb{Z}$, and $M_b = \{u \in \mathbb{R} : N^{-1} \sum_{n < N} \|b^n u\| \to 0\}$.

**Scope and evidence.** Evidence labels follow [`docs/research-objectives.md`](../../docs/research-objectives.md) strictly:
- **Paper proof** denotes a complete, self-contained proof written here (noting any cited published theorem or Phase 19–23 result used as an ingredient).
- **External input** denotes a cited published theorem used as a black box.
- **Finite certificate** denotes an exact integer/rational verification in [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py) (standard library only, 100% exact `int`/`Fraction` arithmetic with zero floating-point checks, 50,283 exact checks, exit code `0`).
- **Finite measurement** denotes a finite-prefix statistic or floating-point sample; finite measurements are **never** evidence for asymptotic statements.
- **Open** denotes an unsettled question. No independent human peer review has been conducted on this note.

## Summary of results

| § | Sub-track | Result | Evidence label |
| --- | --- | --- | --- |
| 1.1–1.2 | B2 | Exact support bijection $u_i$ (binary-to-base-$m$), Thue–Morse sign $(-1)^{t_i}$, exact gap law $u_i - u_{i-1} = \frac{(m-2)m^{v_2(i)} + 1}{m-1}$, uniform zero-carry-flip tail bound $|R_i| < \frac{b^{-1}+b^{-m}}{1-b^{-m}} \le \frac{5}{7} < 1$, and exact base-$b$ digit law of $Y_{b,m}$ at every $n \ge 1$ ($b \ge 2, m \ge 3$), plus non-disjunctivity (`0101` forbidden in base $2$; no adjacent interior digits for $b \ge 3$) | Paper proof + Finite certificate |
| 1.3 | B2 | Exact finite-prefix counts at $N = m^k$ ($k \ge 2$): exact cancellation $\Delta(k) = g_{2^k} + g_{2^{k-1}}$, exact binary count $C_1(m^k; Y_{2,m}, 2) = \frac{m^{k-1}(m^2-m-1) - (m-2)}{m-1}$ (zero $2^k$ error term), proving Astra's subsequence law $\lim_{k\to\infty} f_1(m^k; Y_{2,m}, 2) = 1 - \frac{1}{m(m-1)}$ and its base-$b$ analogue for $f_{b-1}(m^k)$ and $f_0(m^k)$ | Paper proof + Finite certificate |
| 1.4 | B2 | Complete digit- and word-frequency limit set of $Y_{b,m}$ ($b \ge 2, m \ge 3$): self-similar Lipschitz cumulative limit $F_m(t)$ with uniform error $O_m((2/m)^k)$; for every $L \ge 1$, the cluster set of $f_{(b-1)^L}(N; Y_{b,m}, b)$ is the exact closed interval $[1 - \frac{1}{m},\ 1 - \frac{1}{m(m-1)}]$, that of $f_{0^L}(N; Y_{b,m}, b)$ is $[\frac{1}{m(m-1)},\ \frac{1}{m}]$, all other words have frequency $O(L N^{\log_m 2 - 1}) \to 0$, finite prefixes obey the strict-type upper bound $C_{b-1}(N) \le (1 - \frac{1}{m(m-1)})N$ while dipping slightly below $1 - 1/m$ infinitely often, and $Y_{2,m}$ is never simply normal ($\liminf f_1 = 1 - 1/m \ge 2/3 > 1/2$) | Paper proof + Finite certificate |
| 2.1 | B1 | Exact Gaussian-integer and binary-theta-difference identity $a_2(n) = R_+(12n+1) - R_-(12n+1) = \frac{1}{2}(r_{x^2+36y^2}(12n+1) - r_{4x^2+9y^2}(12n+1))$, $r_2(24n+2)/4 = r_2(12n+1)/4 = R_+ + R_-$, exact equality criterion for $n \in U$ ($|a_2(n)| = r_2(12n+1)/4 \iff$ no prime $p \equiv 5 \pmod{12}$ divides $12n+1$), and $a_2(n) \equiv r_2(12n+1)/4 \pmod 2$ | Paper proof + Finite certificate |
| 2.2 | B1 | Tightened unconditional lower bound for Euler's square $E_2^2$: prime-by-prime Selberg sieve inequality $G(\xi) \ge G_0(\xi) \prod_{p \mid ww'h'} \frac{p-2}{p-1}$, Wirsing asymptotic at $\xi = N^{1/2-\varepsilon}$, exact weighted-sum bound, and Euler product collapse $\mathcal{E}_0 = \prod_{p \in \mathcal{P}_0}(1 + \frac{2}{(p-1)(p^2+1)})$ with zero-float rational certificates yield $\mathcal{E}_0 < 1.028980$, $K_* < 3.178808$, $8 K_* < 25.431 < 26$, and $\frac{1}{26} \le \liminf f_{d^L}(N; E_2^2, 2) \le \limsup f_{d^L}(N; E_2^2, 2) \le \frac{25}{26}$ ($> 1{,}538\times$ sharper than Phase 23's $1/40000$) | Paper proof (using Serre; Wirsing; Matomäki–Radziwiłł Cor. 1.2(ii)) + Finite certificate |
| 2.3 | B1 | Binary simple normality of $E_2^2$ ($B_N(H_N) = o(N)$ for $H_N/A_N \to \infty$) and disjunctivity of $E_2^2$ | **Open** |
| 3.1–3.2 | B3 | Base-2 vs base-$b \ge 3$ complement-symmetry dichotomy; closed-form digit law for the universal odd-order family $\frac{1}{b^2+b+1} E_b$ ($t = 3$, balanced $w_0^\pm = \frac{1}{18}$, $f_0 = f_{b-1} = \frac{19}{54}$, $f_1 = f_{b-2} = \frac{4}{27}$, $f_e = 0$ for $2 \le e \le b-3$ when $b \ge 4$; simply normal at $b = 2$ only) | Paper proof + Finite certificate |
| 3.3 | B3 | Complete primitive-root impossibility theorem: for every base $b \ge 3$ and every odd prime $p \nmid 2b$ having $b$ as a primitive root mod $p$, neither $\frac{a}{p} E_b$ nor $\frac{a}{p} E_b^3$ is simply normal in base $b$ (no exceptions; tightest near-miss $\frac{a}{11} E_6$ has interior digits all $1/6$ but unbalanced $w_0^+ = 1/10 \ne 1/15 = w_0^-$ for $a > 0$, swapped for $a < 0$) | Paper proof + Finite certificate |
| 3.4 | B3 | First-principles derivation of $\frac{a}{113} E_{10}$ ($t = 112 \equiv 0 \pmod 4$), new balanced $b$-exceptional primes realizing $t \equiv 2 \pmod 4$ at $(b, p) = (4, 29)$, $(6, 59)$, $(6, 1613)$, infinite arithmetic progressions of bases refuting the radix-free converse, and extended verification of Conjecture 5.5 for $E_2$ through $p \le 40{,}000$ (0 exceptional primes among 2,989 even-order primes) | Paper proof + Finite certificate (full Conjecture 5.5 **Open**) |
| 4.1 | B4 | Exact cross-radix order implication ($L_2$-normal in base $b^k \implies (k(L_2 - 1) + 1)$-normal in base $b$) with all-$(b, k, L_2)$ sharpness via an explicit Markov chain, and reverse non-implication ($L_1$-normal in base $b$ for arbitrary $L_1$ yet not $1$-normal in base $b^k$) | Paper proof + Finite certificate |
| 4.2 | B4 | Simultaneous discrepancy ceilings: phase-stratified $D^+(x; b) \le \min(\frac{2}{b^{L_1}}, \frac{2(b^k-1)}{k(b-1)b^{k L_2}})$, coupling $D^+(x; b^k) \le \min(\frac{2}{b^{k L_2}}, \frac{2(k-1)}{k b^{k L_2}} + \frac{2}{b^{L_1}})$, quantitative kernel exclusion $D^+(x; b^k) \le 1 - \frac{1}{k} + \frac{2}{b^{L_1}}$ (strictly $< 1$ for $b^{L_1} > 2k$), diagonal spectrum when $L_1 \ge k L_2$, and explicit witnesses with $D_\infty(x; b) > 2/b^{k L_2}$ ($11/36 > 2/9$ for $(3,2,1)$ and $1865/6132 > 1/4$ for $(2,3,1)$) | Paper proof + Finite certificate |
| 4.3–4.5 | B4 | Kernel intersection law $K_{b^{k_1}} \cap K_{b^{k_2}} = K_{b^{\gcd(k_1, k_2)}}$; simultaneous $(L_1, L_2)$ tower existence via phased de Bruijn circuits $G_{\text{phased}}(b, k, L_*)$ and genuine parity obstruction at $(b, k, L_1, L_2) = (2, 2, 3, 1)$ in $K_{2^8}$; translation stability vs boundary-flipping instability under $M_b$ and $K_{b^k}$; independence of universal power-disjunctivity in $K_{b^k} \setminus K_b$ | Paper proof + Finite certificate |

---

## 1. Sub-track B2: Higher-$m$ partition reciprocals $Y_{b,m}$ ($b \ge 2, m \ge 3$)

For integers $b \ge 2$ and $m \ge 2$, Mahler's $m$-ary partition constant $X_{b,m} = \prod_{j \ge 0} (1 - b^{-m^j})^{-1}$ has reciprocal
```math
Y_{b,m} = \frac{1}{X_{b,m}} = \prod_{j \ge 0} \bigl(1 - b^{-m^j}\bigr) = \sum_{n \ge 0} \varepsilon_m(n)\, b^{-n},
```
where $\varepsilon_m(n) = (-1)^{s_m(n)}$ if every base-$m$ digit of $n$ lies in $\{0, 1\}$, and $\varepsilon_m(n) = 0$ otherwise (Phase 23 `GF-32`, Theorem 3.1). Here $s_r(n)$ denotes the sum of the base-$r$ digits of $n$, and $t_i = s_2(i) \bmod 2 \in \{0, 1\}$ is the Thue–Morse sequence.

Phase 23 (`GF-32`, Theorems 3.3–3.4) established a sharp dichotomy between $m = 2$ and $m \ge 3$: for $m = 2$, $Y_b = Y_{b,2} \notin K_b$ and $Y_2, Y_3$ are simply normal, whereas for $m \ge 3$, $Y_{b,m} \in M_b \subseteq K_b$ with $M_N(Y_{b,m}; b) \le 2 N^{\log_m 2 - 1}$. We now determine the **exact digit at every position $n \ge 1$**, the **exact finite-prefix count at $N = m^k$**, and the **complete digit- and word-frequency limit set** of $Y_{b,m}$ for every $b \ge 2$ and $m \ge 3$.

### 1.1 Exact support bijection, gap law, and zero-carry-flip tail bound

Write $U_m = \{n \ge 0 : \varepsilon_m(n) \ne 0\}$. For each integer $i = \sum_{j \ge 0} \beta_j(i) 2^j \ge 0$ with $\beta_j(i) \in \{0, 1\}$, define
```math
u_i = \sum_{j \ge 0} \beta_j(i)\, m^j.
```
Let $v_2(i)$ denote the 2-adic valuation of $i \ge 1$ (so $2^{v_2(i)} \parallel i$).

**Theorem 1.1 (support bijection and exact gap law).** *Let $m \ge 2$. The map $i \mapsto u_i$ is a strictly increasing bijection $\mathbb{Z}_{\ge 0} \to U_m$, with $\varepsilon_m(u_i) = (-1)^{t_i}$ for all $i \ge 0$. For every $i \ge 1$, the gap $g_i := u_i - u_{i-1}$ satisfies*
```math
g_i = u_i - u_{i-1} = \frac{(m - 2) m^{v_2(i)} + 1}{m - 1}.
```
*In particular, when $m \ge 3$, $g_i = 1$ if and only if $i$ is odd ($v_2(i) = 0$), and $g_i \ge m - 1 \ge 2$ if and only if $i$ is even ($v_2(i) \ge 1$).*

*Proof.* Uniqueness of base-$m$ expansions implies $i \mapsto u_i$ is a bijection $\mathbb{Z}_{\ge 0} \to U_m$ with $s_m(u_i) = \sum_j \beta_j(i) = s_2(i)$, hence $\varepsilon_m(u_i) = (-1)^{t_i}$. For $i \ge 1$, put $r = v_2(i)$. In binary, $i - 1$ agrees with $i$ in all bits $j > r$, has $\beta_r(i - 1) = 0$ and $\beta_j(i - 1) = 1$ for $0 \le j < r$, whereas $i$ has $\beta_r(i) = 1$ and $\beta_j(i) = 0$ for $0 \le j < r$. Therefore
```math
u_i - u_{i-1} = m^r - \sum_{j=0}^{r-1} m^j = m^r - \frac{m^r - 1}{m - 1} = \frac{(m - 2) m^r + 1}{m - 1} \ge 1.
```
Positivity of every consecutive difference $u_i - u_{i-1} \ge 1$ proves strict monotonicity. For $m \ge 3$, $r = 0$ gives $g_i = 1$, while $r \ge 1$ gives $g_i \ge \frac{(m-2)m + 1}{m-1} = m - 1 \ge 2$. $\square$

For every $n \ge 0$, define the rescaled tail $T_n := \sum_{k > n} \varepsilon_m(k) b^{n - k}$, and for $i \ge 0$ put $R_i := T_{u_i} = \sum_{j > i} (-1)^{t_j} b^{u_i - u_j}$.

**Lemma 1.2 (uniform zero-carry-flip tail bound).** *Let $b \ge 2$ and $m \ge 3$. For every $i \ge 0$, write $R_i = b^{-g_{i+1}}\bigl((-1)^{t_{i+1}} + \theta_{i+1}\bigr)$ where $\theta_{i+1} := \sum_{j \ge i+2} (-1)^{t_j} b^{u_{i+1} - u_j}$. Then*
```math
|\theta_{i+1}| < \begin{cases} \dfrac{b^{-1} + b^{-m}}{1 - b^{-m}} \le \dfrac{5}{7} < 1, & i + 1 \text{ even}, \\[10pt] \dfrac{b^{-(m-1)} + b^{-m}}{1 - b^{-m}} \le \dfrac{3}{7} < \dfrac{1}{2}, & i + 1 \text{ odd}. \end{cases}
```
*Consequently, for every $i \ge 0$, $\operatorname{sgn}(R_i) = (-1)^{t_{i+1}}$ (zero carry flips ever occur) and*
```math
0 < |R_i| < \begin{cases} \dfrac{b^{-1} + b^{-m}}{1 - b^{-m}} \le \dfrac{5}{7} < 1, & i \text{ even}, \\[10pt] \dfrac{b^{-(m-1)} + b^{-m}}{1 - b^{-m}} \le \dfrac{3}{7} < \dfrac{1}{2}, & i \text{ odd}. \end{cases}
```

*Proof.* By Theorem 1.1, consecutive gaps alternate between $g_{\text{odd}} = 1$ and $g_{\text{even}} \ge m - 1$, so every two consecutive indices advance $u_j$ by at least $1 + (m - 1) = m$, with strict inequality infinitely often (whenever $v_2(j) \ge 2$).

- If $i + 1$ is even, then $g_{i+2} = 1$, and by induction on $k \ge 0$, $u_{i+1+2k} - u_{i+1} \ge mk$ and $u_{i+2+2k} - u_{i+1} \ge mk + 1$, with strict inequality for all sufficiently large $k$. Hence
```math
|\theta_{i+1}| < b^{-1} + \sum_{k \ge 1} \bigl(b^{-mk} + b^{-mk-1}\bigr) = b^{-1} + (1 + b^{-1})\frac{b^{-m}}{1 - b^{-m}} = \frac{b^{-1} + b^{-m}}{1 - b^{-m}}.
```
- If $i + 1$ is odd, then $g_{i+2} \ge m - 1$, and by induction on $k \ge 0$, $u_{i+2+2k} - u_{i+1} \ge (m - 1) + mk$ and $u_{i+3+2k} - u_{i+1} \ge m + mk$, with strict inequality for all large $k$. Hence
```math
|\theta_{i+1}| < \sum_{k \ge 0} \bigl(b^{-(m-1)-mk} + b^{-m-mk}\bigr) = \frac{b^{-(m-1)} + b^{-m}}{1 - b^{-m}}.
```
Since both bounds decrease in $b \ge 2$ and $m \ge 3$, evaluating at $(b, m) = (2, 3)$ gives $(2^{-1} + 2^{-3})/(1 - 2^{-3}) = 5/7 < 1$ and $(2^{-2} + 2^{-3})/(1 - 2^{-3}) = 3/7 < 1/2$. Because $|\theta_{i+1}| < 1$, $(-1)^{t_{i+1}} + \theta_{i+1}$ is nonzero and strictly has sign $(-1)^{t_{i+1}}$.

Finally, for $i$ even ($i + 1$ odd, $g_{i+1} = 1$), $|R_i| = b^{-1}|(-1)^{t_{i+1}} + \theta_{i+1}| < b^{-1}\bigl(1 + \frac{b^{-(m-1)}+b^{-m}}{1-b^{-m}}\bigr) = \frac{b^{-1}+b^{-m}}{1-b^{-m}} \le \frac{5}{7}$. For $i$ odd ($i + 1$ even, $g_{i+1} \ge m - 1$), $|R_i| \le b^{-(m-1)}\bigl(1 + \frac{b^{-1}+b^{-m}}{1-b^{-m}}\bigr) = \frac{b^{-(m-1)}+b^{-m}}{1-b^{-m}} \le \frac{3}{7}$. $\square$

### 1.2 Exact base-$b$ digit law at every position and non-disjunctivity

**Theorem 1.3 (exact digit law of $Y_{b,m}$).** *Let $b \ge 2$ and $m \ge 3$. Then $Y_{b,m} \in (0, 1)$ (so $\lfloor Y_{b,m} \rfloor = 0$), and for every $i \ge 1$ the base-$b$ digits $d_n(Y_{b,m})$ on the half-open interval $(u_{i-1}, u_i]$ are given with no boundary exceptions by:*
1. *(Even $i \ge 2$, gap length $g_i \ge m - 1 \ge 2$): for EVERY $n \in (u_{i-1}, u_i]$ — including the right endpoint $n = u_i$ —*
```math
d_n(Y_{b,m}) = \begin{cases} 0, & t_i = 0, \\ b - 1, & t_i = 1. \end{cases}
```
2. *(Odd $i \ge 1$, singleton $(u_{i-1}, u_i] = \{u_i\}$):*
```math
d_{u_i}(Y_{b,m}) = \begin{cases} 1, & (t_i, t_{i+1}) = (0, 0), \\ 0, & (t_i, t_{i+1}) = (0, 1), \\ b - 1, & (t_i, t_{i+1}) = (1, 0), \\ b - 2, & (t_i, t_{i+1}) = (1, 1). \end{cases}
```
*In particular, for $b = 2$ and odd $i \ge 1$, $d_{u_i}(Y_{2,m}) = 1 - t_{i+1}$.*

*Proof.* Since $u_0 = 0$, $u_1 = 1$, $\varepsilon_m(0) = 1$, $\varepsilon_m(1) = -1$, we have $Y_{b,m} = 1 - b^{-1} + b^{-1} R_1$. By Lemma 1.2, $R_1 < 0$ (since $t_2 = 1$) and $|R_1| < 3/7 < 1$, so $Y_{b,m} \in (1 - 2/b, 1 - 1/b) \subset (0, 1)$ (for $b = 2$, $Y_{2,m} \in (0, 1/2)$).

For any $n \ge 1$,
```math
b^{n-1} Y_{b,m} = \sum_{k=0}^{n-1} \varepsilon_m(k) b^{n-1-k} + \frac{\varepsilon_m(n) + T_n}{b} \equiv \frac{\varepsilon_m(n) + T_n}{b} \pmod{1}.
```
First suppose $n = u_i$ ($i \ge 1$). Then $\varepsilon_m(n) = (-1)^{t_i}$ and $T_n = R_i$, with $0 < |R_i| < 1$ and $\operatorname{sgn}(R_i) = (-1)^{t_{i+1}}$ by Lemma 1.2. Examining the four pairs $(t_i, t_{i+1})$:
- $(0, 0)$: $\varepsilon_m(n) + R_i = 1 + R_i \in (1, 2)$, so $\frac{1 + R_i}{b} \in (\frac{1}{b}, \frac{2}{b}) \subseteq (0, 1)$ (using $b \ge 2$) and $d_{u_i} = 1$.
- $(0, 1)$: $1 + R_i \in (0, 1)$, so $\frac{1 + R_i}{b} \in (0, \frac{1}{b})$ and $d_{u_i} = 0$.
- $(1, 0)$: $-1 + R_i \in (-1, 0)$, so $\{\frac{-1 + R_i}{b}\} = \frac{b - 1 + R_i}{b} \in (\frac{b-1}{b}, 1)$ and $d_{u_i} = b - 1$.
- $(1, 1)$: $-1 + R_i \in (-2, -1)$, so $\{\frac{-1 + R_i}{b}\} = \frac{b - 1 + R_i}{b} \in (\frac{b-2}{b}, \frac{b-1}{b}) \subseteq (0, 1)$ and $d_{u_i} = b - 2$.

This proves (2), and also settles the endpoint $n = u_i$ of (1): when $i$ is even, $i + 1$ has binary digit sum $s_2(i + 1) = s_2(i) + 1$, so $t_{i+1} = 1 - t_i$; hence only $(t_i, t_{i+1}) \in \{(0, 1), (1, 0)\}$ occur, giving $d_{u_i} = 0$ if $t_i = 0$ and $d_{u_i} = b - 1$ if $t_i = 1$.

Now suppose $n \in (u_{i-1}, u_i)$ (so $u_{i-1} + 1 \le n \le u_i - 1$, which requires $g_i \ge 2$, hence $i$ even). Then $\varepsilon_m(n) = 0$ and $T_n = b^{-(u_i - n)}\bigl((-1)^{t_i} + R_i\bigr)$. Since $i$ is even, $t_{i+1} = 1 - t_i$, so $R_i$ has the opposite sign to $(-1)^{t_i}$; combined with $0 < |R_i| < 1$, this gives $(-1)^{t_i} + R_i$ strictly of sign $(-1)^{t_i}$ and magnitude $1 - |R_i| \in (0, 1)$. As $u_i - n \ge 1$, we have $0 < |T_n| < b^{-1} < 1$ and $\operatorname{sgn}(T_n) = (-1)^{t_i}$. Thus $0 < |\frac{T_n}{b}| < \frac{1}{b}$, yielding $d_n = 0$ when $t_i = 0$ and $d_n = b - 1$ when $t_i = 1$. Since $Y_{b,m}$ is not a terminating $b$-adic rational (its digits contain both $0$'s and $(b-1)$'s infinitely often, as $t_{2^k} = 1$ and $t_{3\cdot 2^k} = 0$), these are the canonical base-$b$ digits. $\square$

**Corollary 1.4 (non-disjunctivity).** *For every $b \ge 2$ and $m \ge 3$, $Y_{b,m}$ is not disjunctive in base $b$:*
- *For $b = 2$, neither `0101` nor `1010` ever occurs in the binary expansion of $Y_{2,m}$.*
- *For $b \ge 3$, no length-2 word in $\{1, \dots, b - 2\}^2$ ever occurs in the base-$b$ expansion of $Y_{b,m}$.*

*Proof.* By Theorem 1.3, every even gap $(u_{i-1}, u_i]$ is a constant run of length $g_i \ge m - 1 \ge 2$ of digit $0$ or $b - 1$, separated by singletons $\{u_j\}$ at odd $j$. Consecutive odd positions $u_{2r-1}, u_{2r+1}$ satisfy $u_{2r+1} - u_{2r-1} = g_{2r} + 1 \ge m \ge 3$. For $b \ge 3$, digits in $\{1, \dots, b-2\}$ occur only at odd $u_j$, so no two can be adjacent. For $b = 2$, if $d_n d_{n+1} d_{n+2} d_{n+3} = 0101$, then $d_{n+1} = 1$ is flanked by $0$'s, forcing $n + 1$ to be an odd $u_j$ (every position inside an even gap has at least one neighbor in the same constant run of length $\ge 2$); likewise $d_{n+2} = 0$ is flanked by $1$'s, forcing $n + 2$ to be an odd $u_{j'}$, contradicting $u_{2r+1} - u_{2r-1} \ge 3$. The same argument rules out `1010`. $\square$

### 1.3 Exact finite-prefix counts at $N = m^k$ and Astra's subsequence law

Let $C_d(N) := \#\{1 \le n \le N : d_n(Y_{b,m}) = d\}$. For $k \ge 1$, note that $u_{2^k} = m^k$, so the intervals $(u_{i-1}, u_i]$ for $1 \le i \le 2^k$ partition $\{1, \dots, m^k\}$. Define the even-gap counts
```math
W_1(k) := \sum_{\substack{1 \le i \le 2^k \\ i \text{ even},\, t_i = 1}} g_i, \qquad W_0(k) := \sum_{\substack{1 \le i \le 2^k \\ i \text{ even},\, t_i = 0}} g_i.
```

**Theorem 1.5 (exact counts at $N = m^k$ and Astra's subsequence law).** *Let $b \ge 2$, $m \ge 3$, and $k \ge 2$.*
1. *(Exact signed even-gap cancellation):*
```math
W_1(k) - W_0(k) = g_{2^k} + g_{2^{k-1}} = \frac{(m - 2)(m^k + m^{k-1}) + 2}{m - 1},
```
*and consequently*
```math
W_1(k) = \frac{m^{k-1}(m^2 - m - 1) + 1}{m - 1} - 2^{k-2}, \qquad W_0(k) = \frac{m^{k-1} - 1}{m - 1} - 2^{k-2}.
```
2. *(Exact binary prefix count with zero $2^k$ error term): for $b = 2$ and every $k \ge 2$,*
```math
C_1(m^k; Y_{2,m}, 2) = \frac{m^{k-1}(m^2 - m - 1) - (m - 2)}{m - 1}, \qquad C_0(m^k; Y_{2,m}, 2) = \frac{m^{k-1} + m - 2}{m - 1},
```
*so*
```math
f_1(m^k; Y_{2,m}, 2) = 1 - \frac{1}{m(m - 1)} - \frac{m - 2}{(m - 1) m^k}, \qquad \lim_{k \to \infty} f_1(m^k; Y_{2,m}, 2) = 1 - \frac{1}{m(m - 1)}.
```
3. *(General base $b \ge 3$): for every $k \ge 2$, $|C_{b-1}(m^k) - W_1(k)| \le 2^{k-1}$ and $|C_0(m^k) - W_0(k)| \le 2^{k-1}$ (more precisely, the odd-index counts are given by Thue–Morse 2-block counts on $0 \le r < 2^{k-1}$), yielding*
```math
\lim_{k \to \infty} f_{b-1}(m^k; Y_{b,m}, b) = 1 - \frac{1}{m(m - 1)}, \qquad \lim_{k \to \infty} f_0(m^k; Y_{b,m}, b) = \frac{1}{m(m - 1)},
```
*and $f_d(m^k; Y_{b,m}, b) = O((2/m)^k) \to 0$ for every $d \in \{1, \dots, b - 2\}$.*

*Proof.* (1) Group the $2^{k-1}$ even integers $i \in \{2, 4, \dots, 2^k\}$ by $r = v_2(i) \in \{1, \dots, k\}$. Since $g_i$ depends only on $r = v_2(i)$ (Theorem 1.1):
- For $r = k$, the unique index is $i = 2^k$, with $t_{2^k} = 1$, contributing $+g_{2^k}$ to $W_1(k) - W_0(k) = -\sum_{i \text{ even}} (-1)^{t_i} g_i$.
- For $r = k - 1$ (valid since $k \ge 2$), the unique index is $i = 2^{k-1}$, with $t_{2^{k-1}} = 1$, contributing $+g_{2^{k-1}}$.
- For every $1 \le r \le k - 2$, the indices with $v_2(i) = r$ are $i = (2a + 1) 2^r$ with $0 \le a < 2^{k - 1 - r}$. Here $t_{(2a+1)2^r} = 1 - t_a$ and $2^{k-1-r} \ge 2$ is even. Partitioning $a$ into pairs $(2c, 2c + 1)$ gives $(-1)^{t_{2c}} + (-1)^{t_{2c+1}} = 0$, so the sum over every $1 \le r \le k - 2$ vanishes identically!

Thus $W_1(k) - W_0(k) = g_{2^k} + g_{2^{k-1}}$. Since there are $2^{k-1}$ odd integers in $\{1, \dots, 2^k\}$ each of gap length $1$, we have $W_1(k) + W_0(k) = m^k - 2^{k-1}$. Solving the two linear equations yields the stated formulas for $W_1(k)$ and $W_0(k)$.

(2) For $b = 2$, Theorem 1.3 gives $d_{u_i}(Y_{2,m}) = 1 - t_{i+1}$ for each odd $i \in \{1, 3, \dots, 2^k - 1\}$. Writing $i + 1 = 2r$ with $1 \le r \le 2^{k-1}$, we have $t_{2r} = t_r$. Over $0 \le r \le 2^{k-1} - 1$, exactly $2^{k-2}$ values have $t_r = 0$ (including $r = 0$). Replacing $r = 0$ ($t_0 = 0$) by $r = 2^{k-1}$ ($t_{2^{k-1}} = 1$) leaves exactly $2^{k-2} - 1$ odd indices with $d_{u_i} = 1$. Adding $2^{k-2} - 1$ to $W_1(k)$ cancels the $-2^{k-2}$ term identically! Dividing by $m^k$ and letting $k \to \infty$ gives $1 - \frac{1}{m(m-1)}$.

(3) For $b \ge 3$, there are $2^{k-1}$ odd positions $u_i \le m^k$ (for $i = 2r + 1$, $0 \le r < 2^{k-1}$, where $(t_{2r+1}, t_{2r+2}) = (1 - t_r, t_{r+1})$), contributing at most $2^{k-1} = o(m^k)$ to any digit count. Dividing $W_1(k)$ and $W_0(k)$ by $m^k$ gives the limits. $\square$

### 1.4 The complete digit- and word-frequency limit set of $Y_{b,m}$

We now go far beyond the single subsequence $N = m^k$ and determine the **entire oscillation trajectory and cluster set** of $f_w(N; Y_{b,m}, b)$ across all $N \ge 1$ and all finite words $w$.

Define the self-similar Lipschitz function $F_m : [0, 1] \to [0, 1]$ as the unique bounded solution to the functional equation
```math
F_m(t) = \begin{cases} \dfrac{1}{m}\, F_m(m t), & t \in \bigl[0, \tfrac{1}{m}\bigr], \\[8pt] \dfrac{m^2 - m - 1}{m^2(m - 1)} + \bigl(t - \tfrac{1}{m}\bigr) - F_m\bigl(t - \tfrac{1}{m}\bigr), & t \in \bigl[\tfrac{1}{m}, \tfrac{1}{m - 1}\bigr], \\[8pt] t - \dfrac{1}{m(m - 1)}, & t \in \bigl[\tfrac{1}{m - 1}, 1\bigr]. \end{cases}
```
(Note that $F_m$ is **not** finite piecewise-linear: rescaling produces infinitely many affine segments and distinct values of $F_m(t)/t$ arbitrarily close to $0$.) Let us verify existence, regularity, and uniqueness via a Banach contraction on an explicit invariant complete metric space. Let $\mathcal{X}_m \subset C([0, 1])$ be the closed (hence complete under $\|\cdot\|_\infty$) subset of all nondecreasing $1$-Lipschitz functions $F : [0, 1] \to \mathbb{R}$ ($0 \le F(y) - F(x) \le y - x$ for $0 \le x \le y \le 1$) satisfying the three prescribed anchor values
```math
F(0) = 0, \qquad F\Bigl(\frac{1}{m - 1}\Bigr) = \frac{1}{m}, \qquad F(1) = 1 - \frac{1}{m(m - 1)}.
```
The space $\mathcal{X}_m$ is nonempty: linear interpolation through $(0, 0)$, $(\frac{1}{m-1}, \frac{1}{m})$, and $(1, 1 - \frac{1}{m(m-1)})$ has slopes $\frac{m-1}{m} \in (0, 1)$ and $1$, so it lies in $\mathcal{X}_m$. Define the operator $\mathcal{T}_m$ on $\mathcal{X}_m$ by substituting the first branch into the second:
- on $[0, \frac{1}{m}]$: $(\mathcal{T}_m F)(t) = \frac{1}{m} F(mt)$;
- on $[\frac{1}{m}, \frac{1}{m-1}]$: writing $s = t - \frac{1}{m} \in [0, \frac{1}{m(m-1)}] \subseteq [0, \frac{1}{m}]$, $(\mathcal{T}_m F)(t) = \frac{m^2 - m - 1}{m^2(m-1)} + s - \frac{1}{m} F(ms)$;
- on $[\frac{1}{m-1}, 1]$: $(\mathcal{T}_m F)(t) = t - \frac{1}{m(m-1)}$.

For every $F \in \mathcal{X}_m$, the two junctions match identically: at $t = \frac{1}{m}$, both pieces give $\frac{1}{m} F(1) = \frac{m^2 - m - 1}{m^2(m-1)} = \frac{m^2 - m - 1}{m^2(m-1)} - \frac{1}{m} F(0)$; at $t = \frac{1}{m-1}$ ($s = \frac{1}{m(m-1)}$, $ms = \frac{1}{m-1}$), the middle piece gives $\frac{m^2 - m - 1}{m^2(m-1)} + \frac{1}{m(m-1)} - \frac{1}{m} F(\frac{1}{m-1}) = \frac{m^2 - 1}{m^2(m-1)} - \frac{1}{m^2} = \frac{1}{m}$, matching the third piece. Moreover, $\mathcal{T}_m F$ preserves the three anchor values $(0, \frac{1}{m}, 1 - \frac{1}{m(m-1)})$ and the slope bounds $0 \le \Delta(\mathcal{T}_m F) \le \Delta t$ on all three intervals (on the middle interval, $0 \le \frac{1}{m} \Delta F(ms) \le \Delta s$ implies $s \mapsto s - \frac{1}{m} F(ms)$ is nondecreasing and $1$-Lipschitz), hence globally on $[0, 1]$ by continuity at the junctions. Thus $\mathcal{T}_m(\mathcal{X}_m) \subseteq \mathcal{X}_m$ with strict contraction factor $\|\mathcal{T}_m F - \mathcal{T}_m G\|_\infty \le \frac{1}{m}\|F - G\|_\infty$ ($\frac{1}{m} \le \frac{1}{3}$), so Banach's fixed-point theorem yields a unique fixed point $F_m \in \mathcal{X}_m$ (which automatically satisfies the original functional equation since $F_m(s) = \frac{1}{m} F_m(ms)$ on $[0, \frac{1}{m}]$). Conversely, any bounded solution $F : [0, 1] \to \mathbb{R}$ of the original functional equation must satisfy $F(0) = \frac{1}{m} F(0) \implies F(0) = 0$, $F(\frac{1}{m-1}) = \frac{1}{m}$, $F(1) = 1 - \frac{1}{m(m-1)}$, and $F = \mathcal{T}_m F$ on $[0, 1]$, whence $\|F - F_m\|_\infty = \|\mathcal{T}_m F - \mathcal{T}_m F_m\|_\infty \le \frac{1}{m}\|F - F_m\|_\infty$ forces $F = F_m$.

**Theorem 1.6 (complete digit- and word-frequency limit set of $Y_{b,m}$).** *Let $b \ge 2$ and $m \ge 3$.*
1. *(Uniform scaling law): for every $k \ge 2$ and $t \in [0, 1]$,*
```math
\sup_{t \in [0, 1]} \left| \frac{C_{b-1}(\lfloor t m^k \rfloor; Y_{b,m}, b)}{m^k} - F_m(t) \right| = O_m\left(\left(\frac{2}{m}\right)^k\right).
```
*Equivalently, writing any $N \ge m^2$ as $N = \lfloor t m^k \rfloor$ with $k = \lfloor \log_m N \rfloor + 1$ and $t = N / m^k \in [1/m, 1]$,*
```math
f_{b-1}(N; Y_{b,m}, b) = \frac{F_m(t)}{t} + O_m\bigl(N^{\log_m 2 - 1}\bigr).
```
2. *(Exact global extrema of $F_m(t)/t$):*
```math
\min_{t \in [1/m,\, 1]} \frac{F_m(t)}{t} = 1 - \frac{1}{m}, \qquad \max_{t \in [1/m,\, 1]} \frac{F_m(t)}{t} = 1 - \frac{1}{m(m - 1)}.
```
*On $[1/m, 1]$, the maximum is attained at both endpoints $t = 1/m$ and $t = 1$ (corresponding to $N = m^k$) and nowhere in $(1/m, 1)$. The minimum is attained at $t = \frac{1}{m - 1}$ ($N = u_{2^k - 1} = \frac{m^k - 1}{m - 1}$), at $t = \frac{1}{m} + \frac{1}{m^2}$ ($N = m^{k-1} + m^{k-2}$), and along the infinite sequence $t_r = \frac{1}{m} + \frac{1}{m^2} + \frac{1}{m^{r+1}(m - 1)}$ ($r \ge 1$).*
3. *(Complete cluster set for every finite word of every length $L \ge 1$):*
   - *The set of all subsequential limit points (cluster set) of $f_{(b-1)^L}(N; Y_{b,m}, b)$ as $N \to \infty$ is the exact closed interval*
```math
\left[1 - \frac{1}{m},\ 1 - \frac{1}{m(m - 1)}\right].
```
   - *The cluster set of $f_{0^L}(N; Y_{b,m}, b)$ as $N \to \infty$ is the exact complementary closed interval*
```math
\left[\frac{1}{m(m - 1)},\ \frac{1}{m}\right].
```
   - *Every word $w \in \{0, \dots, b - 1\}^L \setminus \{0^L, (b-1)^L\}$ other than the two extreme constant words satisfies $f_w(N; Y_{b,m}, b) = O(L N^{\log_m 2 - 1}) \to 0$.*
4. *(Finite-prefix bounds and consequences):*
   - *The interval $[1 - \frac{1}{m},\, 1 - \frac{1}{m(m-1)}]$ is the asymptotic **cluster set**: every subsequential limit lies in it, whereas finite prefixes dip slightly below the lower endpoint $1 - \frac{1}{m}$ infinitely often. Specifically, for $N = u_{2^k - 1} = \frac{m^k - 1}{m - 1}$ ($k \ge 2$),*
```math
C_1(N; Y_{2,m}, 2) = m^{k-1} - 1, \qquad f_1(N; Y_{2,m}, 2) = 1 - \frac{1}{m} - \frac{m - 1}{m N} < 1 - \frac{1}{m}
```
     *(e.g. $80/121 < 2/3$ at $m = 3, k = 5$), and for $b \ge 3$ the top-digit count satisfies $C_{b-1}(N; Y_{b,m}, b) \le C_1(N; Y_{2,m}, 2)$.*
   - *By contrast, the upper endpoint holds as an exact **finite-prefix upper bound** for every $N \ge 1$ and $L \ge 1$:*
```math
C_{b-1}(N; Y_{b,m}, b) \le \left(1 - \frac{1}{m(m - 1)}\right) N, \qquad f_{(b-1)^L}(N; Y_{b,m}, b) \le f_{b-1}(N; Y_{b,m}, b) \le 1 - \frac{1}{m(m - 1)}.
```
   - *For every $b \ge 2$ and $m \ge 3$, $Y_{b,m}$ is never simply normal in base $b$ (even for $b = 2$, $\liminf_N f_1(N; Y_{2,m}, 2) = 1 - \frac{1}{m} \ge \frac{2}{3} > \frac{1}{2}$), its digit frequencies $f_0(N)$ and $f_{b-1}(N)$ diverge while oscillating across an interval of width $\frac{m - 2}{m(m - 1)} > 0$, and the set of seam-resolved orbit limit measures of $\{b^n Y_{b,m}\}$ on $[0, 1]$ is exactly $\bigl\{(1 - p)\delta_{0^+} + p\delta_{1^-} : p \in [1 - \frac{1}{m},\, 1 - \frac{1}{m(m-1)}]\bigr\}$.*

*Proof.* (1) Define $E(N) := \#\{1 \le n \le N : n \in (u_{i-1}, u_i] \text{ for some even } i \ge 2 \text{ with } t_i = 1\}$ and $O(N) := \#\{1 \le n \le N : n = u_i \text{ for some odd } i \ge 1\}$. By Theorem 1.3, $|C_{b-1}(N) - E(N)| \le O(N) \le 2^{k-1}$ for all $N \le m^k$. Set $\varepsilon_k := \sup_{t \in [0, 1]} |E(\lfloor t m^k \rfloor)/m^k - F_m(t)|$. For $k \ge 3$:
- On $t \in [0, 1/m]$, $\lfloor t m^k \rfloor = \lfloor (mt) m^{k-1} \rfloor$, so $|E(\lfloor t m^k \rfloor)/m^k - F_m(t)| \le \varepsilon_{k-1}/m$.
- On $t \in [1/m, 1/(m-1)]$, write $s = t - 1/m \in [0, \frac{1}{m(m-1)}]$ and $r = \lfloor t m^k \rfloor - m^{k-1} = \lfloor s m^k \rfloor$. Since $\lfloor \frac{m^k}{m-1} \rfloor = \frac{m^k - 1}{m-1} = m^{k-1} + u_{2^{k-1}-1}$, we have $0 \le r \le u_{2^{k-1}-1}$. For every $1 \le j \le 2^{k-1} - 1$, $u_{2^{k-1}+j} = m^{k-1} + u_j$, $g_{2^{k-1}+j} = g_j$, and $t_{2^{k-1}+j} = 1 - t_j$. Hence every even gap in $(m^{k-1}, m^{k-1} + r]$ is the $+m^{k-1}$ shift of the corresponding even gap in $(0, r]$ with **opposite** Thue–Morse parity! Therefore $E(m^{k-1} + r) = E(m^{k-1}) + \bigl(r - E(r) - O(r)\bigr)$. By Theorem 1.5(1), $|E(m^{k-1})/m^k - F_m(1/m)| \le (2^{k-3} + 1)/m^k$; also $|r/m^k - s| \le 1/m^k$, $O(r)/m^k \le 2^{k-2}/m^k$, and $|E(r)/m^k - F_m(s)| \le \varepsilon_{k-1}/m$. Summing gives error $\le \varepsilon_{k-1}/m + (2^{k-1} + 2)/m^k$.
- On $t \in [1/(m-1), 1]$, $\lfloor t m^k \rfloor \ge u_{2^k - 1}$ and every $n \in (u_{2^k - 1}, m^k]$ lies in the even gap $(u_{2^k-1}, u_{2^k}]$ with $t_{2^k} = 1$, so $E(\lfloor t m^k \rfloor) = E(u_{2^k - 1}) + (\lfloor t m^k \rfloor - u_{2^k - 1}) = \lfloor t m^k \rfloor - \frac{m^{k-1}-1}{m-1} - 2^{k-2}$ by Theorem 1.5(1), giving error $\le (2^{k-2} + 2)/m^k$.

Thus $\varepsilon_k \le \frac{\varepsilon_{k-1}}{m} + \frac{2^{k-1} + 2}{m^k}$ for all $k \ge 3$. Unrolling the recurrence gives
```math
\varepsilon_k \le \frac{\varepsilon_2}{m^{k-2}} + \sum_{j=3}^k \frac{2^{j-1} + 2}{m^k} \le \frac{\varepsilon_2 m^2 + 2^k + 2k}{m^k} = O_m\left(\left(\frac{2}{m}\right)^k\right),
```
and adding $O(N)/m^k \le 2^{k-1}/m^k$ proves (1).

(2) *Lower bound ($\min = 1 - \frac{1}{m}$):* Let $\alpha := \min_{t \in [1/m,\, 1]} F_m(t)/t$, attained by continuity at some $t_* \in [1/m, 1]$. By scale invariance $F_m(t)/t = F_m(mt)/(mt)$ on $(0, 1/m]$, we have $F_m(z) \ge \alpha z$ for **every** $z \in [0, 1]$. Partition $[1/m, 1]$ into three intervals:
- *Piece I:* $t \in [\frac{1}{m-1}, 1]$. Here $F_m(t)/t = 1 - \frac{1}{m(m-1)t}$, which increases strictly from $1 - \frac{1}{m}$ (at $t = \frac{1}{m-1}$) to $1 - \frac{1}{m(m-1)}$ (at $t = 1$).
- *Piece II:* $t \in [\frac{1}{m}, \frac{1}{m} + \frac{1}{m^2}]$. Write $t = \frac{1 + y}{m}$ with $y \in [0, \frac{1}{m}]$, so $F_m(t) = \frac{1}{m}\bigl(1 - \frac{1}{m(m-1)} + y - F_m(y)\bigr)$. We claim $F_m(t) \ge (1 - \frac{1}{m}) t$, which upon multiplying by $m$ and rearranging is equivalent to
```math
F_m(y) \le \frac{y}{m} + \frac{m - 2}{m(m - 1)} \qquad \text{for all } y \in \bigl[0, \tfrac{1}{m}\bigr].
```
  For $y \in [\frac{1}{m(m-1)}, \frac{1}{m}]$, scaling Piece I gives $F_m(y) = y - \frac{1}{m^2(m-1)}$, so $\text{RHS} - F_m(y) = \frac{m-1}{m}(\frac{1}{m} - y) \ge 0$ (equality at $y = \frac{1}{m}$, i.e. $t = \frac{1}{m} + \frac{1}{m^2}$). For $y \in [0, \frac{1}{m(m-1)}]$, monotonicity gives $F_m(y) \le F_m(\frac{1}{m(m-1)}) = \frac{1}{m^2}$, whereas $\text{RHS} \ge \frac{m-2}{m(m-1)}$; and $\frac{m-2}{m(m-1)} - \frac{1}{m^2} = \frac{m^2 - 3m + 1}{m^2(m-1)} \ge \frac{1}{m^2(m-1)} > 0$ for every $m \ge 3$!
- *Piece III:* $t \in [\frac{1}{m} + \frac{1}{m^2}, \frac{1}{m-1}]$. Write $t = \frac{1 + \frac{1}{m} + z}{m}$ with $z \in [0, \frac{1}{m(m-1)}]$. Applying the functional equation twice (first at $t = \frac{1}{m} + \frac{1/m + z}{m}$, then at $\frac{1}{m} + z$):
```math
F_m(t) = \frac{1}{m}\left(1 - \frac{1}{m(m-1)} + \frac{1}{m} + z - F_m\bigl(\tfrac{1}{m} + z\bigr)\right) = \frac{1}{m}\left(1 - \frac{1}{m^2} + F_m(z)\right).
```
  Since $(1 - \frac{1}{m}) t = \frac{1}{m}\bigl(1 - \frac{1}{m^2} + (1 - \frac{1}{m}) z\bigr)$, we obtain the **exact self-similar deficit identity**
```math
F_m(t) - \left(1 - \frac{1}{m}\right) t = \frac{1}{m}\left(F_m(z) - \left(1 - \frac{1}{m}\right) z\right). \tag{1.1}
```

Now suppose for contradiction that $\alpha < 1 - \frac{1}{m}$. By Pieces I and II, the minimizer $t_*$ must lie in the interior of Piece III, so $t_* = \frac{1 + 1/m + z_*}{m}$ with $z_* \in (0, \frac{1}{m(m-1)})$. Applying (1.1) and $F_m(z_*) \ge \alpha z_*$:
```math
\Bigl(\alpha - \bigl(1 - \tfrac{1}{m}\bigr)\Bigr) t_* = \frac{1}{m}\left(F_m(z_*) - \bigl(1 - \tfrac{1}{m}\bigr) z_*\right) \ge \frac{1}{m}\Bigl(\alpha - \bigl(1 - \tfrac{1}{m}\bigr)\Bigr) z_*.
```
Dividing by the strictly negative number $\alpha - (1 - \frac{1}{m})$ gives $t_* \le z_*/m < z_* < \frac{1}{m(m-1)} < \frac{1}{m} < t_*$, a contradiction! Hence $\alpha = 1 - \frac{1}{m}$. Setting $z = \frac{1}{m^r(m-1)}$ ($r \ge 1$) in (1.1) gives $F_m(z) = (1 - \frac{1}{m}) z$, producing the infinite sequence of minimizers $t_r = \frac{1}{m} + \frac{1}{m^2} + \frac{1}{m^{r+1}(m-1)}$.

*Upper bound ($\max = 1 - \frac{1}{m(m-1)}$):* On Piece I, $F_m(t)/t \le 1 - \frac{1}{m(m-1)}$ with equality uniquely at $t = 1$. On Pieces II–III, $t = \frac{1+y}{m}$ with $y \in (0, \frac{1}{m-1}]$ has
```math
\frac{F_m(t)}{t} = 1 - \frac{\frac{1}{m(m-1)} + F_m(y)}{1 + y}.
```
Since we just proved $F_m(y) \ge (1 - \frac{1}{m}) y > \frac{1}{m(m-1)} y$ for all $y > 0$ (as $1 - \frac{1}{m} \ge \frac{2}{3} > \frac{1}{6} \ge \frac{1}{m(m-1)}$ for $m \ge 3$), we have $\frac{\frac{1}{m(m-1)} + F_m(y)}{1 + y} > \frac{1}{m(m-1)}$, hence $F_m(t)/t < 1 - \frac{1}{m(m-1)}$ strictly for all $t \in (1/m, 1)$.

(3) Since $t \mapsto F_m(t)/t$ is continuous on $[1/m, 1]$ with exact image $[1 - \frac{1}{m}, 1 - \frac{1}{m(m-1)}]$, every point of that closed interval is a limit point of $f_{b-1}(N; Y_{b,m}, b)$ (pick $N_k = \lfloor t m^k \rfloor$), and by (1) no point outside it can be a limit point. For any fixed word length $L \ge 1$, a shift $n \in [0, N)$ can read a word other than $0^L$ or $(b-1)^L$, or disagree with $d_{n+1}(Y_{b,m})^L$, only if $[n + 1, n + L]$ meets an odd support point $u_j$ or crosses a gap endpoint $u_i$. Since $\#\{i : u_i \le N + L\} \le 2 (N + L)^{\log_m 2}$, at most $L \cdot 2 (N + L)^{\log_m 2} = O(L N^{\log_m 2})$ shifts are affected. Thus $f_{(b-1)^L}(N) = f_{b-1}(N) + O(L N^{\log_m 2 - 1})$, $f_{0^L}(N) = 1 - f_{b-1}(N) + O(L N^{\log_m 2 - 1})$, and every word other than $0^L$ and $(b-1)^L$ satisfies $f_w(N) = O(L N^{\log_m 2 - 1}) \to 0$.

(4) For the finite-prefix lower crossing at $N = u_{2^k - 1} = \frac{m^k - 1}{m - 1}$ ($k \ge 2$), the final gap $(u_{2^k - 1}, m^k]$ has length $g_{2^k} = \frac{(m-2)m^k + 1}{m-1}$ and consists entirely of ones in base $2$ (Theorem 1.3). Subtracting $g_{2^k}$ from Theorem 1.5(2) gives $C_1(N; Y_{2,m}, 2) = m^{k-1} - 1$ and $f_1(N; Y_{2,m}, 2) = \frac{m^{k-1} - 1}{N} = 1 - \frac{1}{m} - \frac{m - 1}{m N} < 1 - \frac{1}{m}$. For any $b \ge 3$, Theorem 1.3 shows $d_n(Y_{b,m}) = b - 1 \implies d_n(Y_{2,m}) = 1$ at every $n \ge 1$, so $C_{b-1}(N; Y_{b,m}, b) \le C_1(N; Y_{2,m}, 2)$ for all $N \ge 1$.

For the finite-prefix upper bound, it therefore suffices to prove $C(N) \le (1 - d) N$ for $b = 2$, where $C(N) := C_1(N; Y_{2,m}, 2)$, $d := \frac{1}{m(m-1)}$, and $c := \frac{m - 2}{m - 1}$. By Theorem 1.3, $d_1(Y_{2,m}) = 0$ and $d_n(Y_{2,m}) = 1$ for $2 \le n \le m$, so $C(N) = N - 1 \le (1 - d)N$ for $1 \le N \le m$ (since $dN \le \frac{1}{m-1} < 1$). Moreover, $C(m^a) = (1 - d)m^a - c$ holds for every $a \ge 1$ ($a = 1$ directly; $a \ge 2$ by Theorem 1.5(2)). Now take any $a \ge 1$ and $N \in (m^a, m^{a+1}]$:
- *Reflected range* $N = m^a + r$ with $1 \le r \le u_{2^a - 1} = \frac{m^a - 1}{m - 1}$: for every $1 \le n < u_{2^a - 1}$, shifting by $+m^a$ flips $t_i$ (on even gaps) and $t_{i+1}$ (on odd singletons), giving exact complementation $d_{m^a + n} = 1 - d_n$; at the last singleton $n = u_{2^a - 1}$, both $d_{u_{2^a - 1}}$ and $d_{u_{2^{a+1} - 1}}$ equal $0$ (since $t_{2^a} = t_{2^{a+1}} = 1$). Hence $C(m^a + r) \le C(m^a) + r - C(r)$. For $1 \le r < m$, $C(r) = r - 1 \ge d r - c$ (since $(1 - d)r + c - 1 \ge \frac{m^2 - 2m - 1}{m(m-1)} > 0$ for $m \ge 3$). For $m^j \le r < m^{j+1}$ with $j \ge 1$, monotonicity gives $C(r) \ge C(m^j) \ge \frac{m^j}{m - 1} > d r > d r - c$ (checking $C(m) = m - 1 \ge \frac{m}{m-1}$ for $m \ge 3$, and $C(m^j) - \frac{m^j}{m-1} = \frac{m^{j-1}(m^2-2m-1)-(m-2)}{m-1} > 0$ for $j \ge 2$). Combining gives $C(m^a + r) \le (1 - d)m^a - c + r - (d r - c) = (1 - d)(m^a + r)$.
- *Final all-ones gap* $u_{2^{a+1} - 1} < N \le m^{a+1}$: since every digit in $(u_{2^{a+1}-1}, m^{a+1}]$ is $1$, $C(N)/N$ increases strictly with $N$ to $C(m^{a+1})/m^{a+1} = 1 - d - c/m^{a+1} < 1 - d$.

Thus $C_{b-1}(N; Y_{b,m}, b) \le C(N) \le (1 - d)N$ for all $N \ge 1$, and since every shift starting $(b-1)^L$ begins with $b - 1$, $f_{(b-1)^L}(N; Y_{b,m}, b) \le f_{b-1}(N; Y_{b,m}, b) \le 1 - d$. The remaining statements follow immediately from (3), $Y_{b,m} \in M_b$ (Phase 23 `GF-32`, Theorem 3.4), and the fact that $\{b^n Y_{b,m}\}$ lies in $[0, b^{-L})$ on $0^L$-shifts and in $[1 - b^{-L}, 1)$ on $(b-1)^L$-shifts. $\square$

### 1.5 Contrast with $m = 2$ (`GF-32`) and finite verification

| Property | $m = 2$ ($Y_b = 1/X_b$, Phase 23 `GF-32`) | $m \ge 3$ ($Y_{b,m} = 1/X_{b,m}$, Theorem 1.6) |
| --- | --- | --- |
| Support exponent | Full support ($S_2(N) = N$) | Cantor support $S_m(N) \asymp N^{\log_m 2}$ ($\log_m 2 < 1$) |
| Membership in $K_b$ | $Y_b \notin K_b$ ($D^+ \le 1 - \frac{4}{15 b^2}$) | $Y_{b,m} \in M_b \subseteq K_b$ ($1 - D_N \le 4 N^{(\log_m 2 - 1)/2}$) |
| Simple normality in base $2$ | **Simply normal** ($f_0, f_1 \to 1/2$) | **Never simply normal** ($\liminf f_1 = 1 - \frac{1}{m} \ge \frac{2}{3}$) |
| Simple normality in base $3$ | **Simply normal** ($f_0, f_1, f_2 \to 1/3$) | **Never simply normal** ($f_1 \to 0$; cluster set of $f_2$ is $[1 - \frac{1}{m}, 1 - \frac{1}{m(m-1)}]$) |
| Convergence of $f_d(N)$ | Converges for all $d$ (unique atomless limit measure) | Diverges for $d \in \{0, b-1\}$; oscillates across interval of width $\frac{m-2}{m(m-1)}$ |
| Disjunctivity | Not disjunctive (cube-free in $b=2$; no $00, (b-1)(b-1)$ in $b \ge 3$) | Not disjunctive (no `0101`/`1010` in $b=2$; no $\{1,\dots,b-2\}^2$ in $b \ge 3$) |

**Finite certificates and finite measurements** ([`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py)): exact integer checks confirm Theorem 1.1 through $i \le 512$ and Theorem 1.5(1) through $k \le 8$ for $m \in \{3, 4, 5, 6, 10\}$; exact certified digits match Theorem 1.3 at every single position across 15 pairs $(b, m) \in \{2, 3, 4\} \times \{3, 4, 5, 6, 10\}$ over prefixes $81 \le N = m^k \le 1000$, together with exact $C_1(m^k)$ (Theorem 1.5(2)), exact finite-prefix lower crossing $C_1(u_{2^k - 1}) = m^{k-1} - 1$ and upper bound $C_{b-1}(N) \le (1 - \frac{1}{m(m-1)})N$ at every prefix $1 \le N \le m^k$, forbidden words (Corollary 1.4), and exact evaluations of $F_m(t)/t$ on depth-$4$ $m$-adic grids, Cantor minimizers $t_r$, and periodic-orbit rationals (e.g. $F_3(1/8) = 23/240$). Separate finite extrema measurements on $[m^{k-1}, m^k]$ for $Y_{2,m}$ (not asymptotic evidence; note $\min f_1 < 1 - 1/m$, reflecting the finite-prefix lower crossing above):
- $m = 3, k = 6$ ($N = 729$): $\min f_1 = 0.664615$ (theory $\liminf = 2/3 \approx 0.666667$), $\max f_1 = 0.832647$ (theory $\limsup = 5/6 \approx 0.833333$).
- $m = 4, k = 5$ ($N = 1024$): $\min f_1 = 0.747664$ (theory $3/4 = 0.750000$), $\max f_1 = 0.916016$ (theory $11/12 \approx 0.916667$).
- $m = 5, k = 4$ ($N = 625$): $\min f_1 = 0.794702$ (theory $4/5 = 0.800000$), $\max f_1 = 0.948800$ (theory $19/20 = 0.950000$).

---

## 2. Sub-track B1: Euler's square $E_2^2 = \prod_{n \ge 1}(1 - 2^{-n})^2$

Let $E(q)^2 = \sum_{n \ge 0} a_2(n) q^n$, $U = \{n \ge 0 : a_2(n) \ne 0\}$, $s(n) = \operatorname{sgn} a_2(n)$, and $\mathcal{P}_0 = \{p \text{ prime} : p \ge 5,\ p \not\equiv 1 \pmod{12}\}$. Recall from Phase 23 `GF-29` (`euler-square-and-higher-order-tower.md`, §§1–2) that $a_2(n) = c(12n + 1)$ where $\eta(12\tau)^2 = \sum_{m \ge 1} c(m) q^m$, $S(N) = |U \cap [1, N]| \sim C_\eta N / A_N$ with $A_N = (\log N)^{3/4}$, $S_\pm(N) \sim C_\eta N / (2 A_N)$, and
```math
f_{0^L}(N; E_2^2, 2) - f_{1^L}(N; E_2^2, 2) = \frac{1}{N} \sum_{0 < m \le N,\, m \in U} s(m) g(m) + O_{L,\theta}\left(\left(\frac{\log A_N}{A_N}\right)^\theta\right) \qquad (0 < \theta < 1/3),
```
where $g(m_i) = m_i - m_{i-1}$ is the preceding gap in $U$. Phase 23 proved the unconditional lower bound $\frac{1}{40000} \le \liminf f_d(N; E_2^2, 2) \le \limsup f_d(N; E_2^2, 2) \le \frac{39999}{40000}$. Here we first record an exact Gaussian-integer / binary-theta-difference identity for $a_2(n)$, and then improve the unconditional lower frequency bound by a factor exceeding **$1{,}538\times$**, from $1/40000$ to **$1/26$**.

### 2.1 Exact Gaussian-integer and binary-theta-difference identity

For a binary quadratic form $Q(x, y)$, let $r_Q(m) := \#\{(x, y) \in \mathbb{Z}^2 : Q(x, y) = m\}$, and write $r_2(m) = r_{x^2 + y^2}(m)$.

**Theorem 2.1 (exact theta-difference and $r_2$ identities for $a_2(n)$).** *For every integer $n \ge 0$, define*
```math
R_+(m) := \#\bigl\{(x, y) \in \mathbb{Z}^2 : x^2 + y^2 = m,\ x \equiv 1 \pmod 6,\ y \equiv 0 \pmod 6\bigr\},
```
```math
R_-(m) := \#\bigl\{(x, y) \in \mathbb{Z}^2 : x^2 + y^2 = m,\ x \equiv 4 \pmod 6,\ y \equiv 3 \pmod 6\bigr\}.
```
*Then, identically for every $n \ge 0$:*
1. $a_2(n) = R_+(12n + 1) - R_-(12n + 1) = \dfrac{1}{2}\Bigl(r_{x^2 + 36y^2}(12n + 1) - r_{4x^2 + 9y^2}(12n + 1)\Bigr)$;
2. $\dfrac{r_2(24n + 2)}{4} = \dfrac{r_2(12n + 1)}{4} = R_+(12n + 1) + R_-(12n + 1)$;
3. $|a_2(n)| \le \dfrac{r_2(24n + 2)}{4}$, *with exact equality on $n \in U$ if and only if $12n + 1$ has no prime factor $p \equiv 5 \pmod{12}$;*
4. $a_2(n) \equiv \dfrac{r_2(12n + 1)}{4} \pmod 2$, *and consequently $a_2(n)$ is odd if and only if $12n + 1 = (6j + 1)^2$ is a perfect square, i.e., $n = 3j^2 + j = 2 P(-j)$ with $P(k) = k(3k - 1)/2$ ($j \in \mathbb{Z}$).*

*Proof.* By Euler's pentagonal number theorem, $E(q)^2 = \sum_{j, k \in \mathbb{Z}} (-1)^{j+k} q^{(3j^2 + j + 3k^2 + k)/2}$, so
```math
a_2(n) = \sum_{\substack{j, k \in \mathbb{Z} \\ (6j+1)^2 + (6k+1)^2 = 24n + 2}} (-1)^{j+k}.
```
Put $u = 6j + 1$, $v = 6k + 1$, and divide $u + iv \in \mathbb{Z}[i]$ by $1 + i$:
```math
x + iy := \frac{u + iv}{1 + i} = \bigl(3(j + k) + 1\bigr) + i \cdot 3(k - j).
```
Then $x^2 + y^2 = \frac{u^2 + v^2}{2} = 12n + 1$, $x \equiv 1 \pmod 3$, $y \equiv 0 \pmod 3$, and $x + y = 6k + 1$ is odd. Conversely, given any $(x, y) \in \mathbb{Z}^2$ with $x^2 + y^2 = 12n + 1$, $x \equiv 1 \pmod 3$, $y \equiv 0 \pmod 3$, reducing mod $4$ forces $x, y$ to have opposite parity, so $a = (x - 1)/3$ and $b = y/3$ satisfy $a \equiv b \pmod 2$, yielding unique integers $j = (a - b)/2$, $k = (a + b)/2$ with $(6j+1)^2 + (6k+1)^2 = 24n + 2$. Moreover, $(-1)^{j+k} = (-1)^{3(j+k)} = (-1)^{x - 1}$, which is $+1$ when $x \equiv 1 \pmod 6$, $y \equiv 0 \pmod 6$ (counted by $R_+$) and $-1$ when $x \equiv 4 \pmod 6$, $y \equiv 3 \pmod 6$ (counted by $R_-$). This proves $a_2(n) = R_+(12n+1) - R_-(12n+1)$.

For any solution $x^2 + 36y'^2 = 12n + 1$, $3 \nmid x$ and $x$ is odd, so $x \equiv \pm 1 \pmod 6$; replacing $x \mapsto -x$ pairs solutions in $\{x \equiv 1 \pmod 6\}$ bijectively with $\{x \equiv 5 \pmod 6\}$, giving $r_{x^2+36y^2}(12n+1) = 2 R_+(12n+1)$ (including when $y' = 0$). Likewise, in $4x'^2 + 9y'^2 = 12n + 1$, $y'$ is odd and $3 \nmid x'$, so $x' \mapsto -x'$ pairs $\{x' \equiv 2 \pmod 3\}$ (i.e. $2x' \equiv 4 \pmod 6$) bijectively with $\{x' \equiv 1 \pmod 3\}$, giving $r_{4x^2+9y^2}(12n+1) = 2 R_-(12n+1)$. This proves (1).

For (2), every $\alpha \in \mathbb{Z}[i]$ of norm $12n + 1 \equiv 1 \pmod 3$ has exactly one coordinate divisible by $3$, so among its four associates $\{\pm \alpha, \pm i\alpha\}$ **exactly one** satisfies $x \equiv 1 \pmod 3$, $y \equiv 0 \pmod 3$; hence $R_+(12n+1) + R_-(12n+1) = r_2(12n+1)/4$. Multiplication by $1 + i$ gives $r_2(24n+2) = r_2(12n+1)$.

For (3) and (4), $|R_+ - R_-| \le R_+ + R_-$ and $(R_+ - R_-) \equiv R_+ + R_- \pmod 2$ are immediate. On $n \in U$, Jacobi's two-square formula gives $r_2(12n+1)/4 = \prod_{p \equiv 1 \,(12)} (v_p + 1) \prod_{p \equiv 5 \,(12)} (v_p + 1)$, whereas $|a_2(n)| = \prod_{p \equiv 1 \,(12)} (v_p + 1)$ (Phase 20 Theorem 6(a)), so equality holds iff $v_p(12n+1) = 0$ for every $p \equiv 5 \pmod{12}$. Finally, $r_2(12n+1)/4$ is odd iff every prime factor of $12n + 1$ has even exponent, i.e. $12n + 1 = (6j + 1)^2$. $\square$

### 2.2 Tightened unconditional lower bound $\liminf f_{d^L}(N; E_2^2, 2) \ge 1/26$

Where did Phase 23 `GF-29` lose over three orders of magnitude in obtaining $1/40000$? Five compounding losses occurred: (i) Lemma S.2 used Rankin's trick at $\log z = 2$ with $\xi = z^{17}$, forcing $\beta < 1/34$ ($\beta^{-3/2} > 198$, rounded to $216$); (ii) omitting $p \mid vv'$ from the sieve $\mathcal{Q}$ instead of retaining $\rho(p) \in \{1, 2\}$; (iii) bounding the $(v, v')$ and $h$ sums over all integers coprime to $6$ (or all $h$) rather than only primes in $\mathcal{P}_0$, and discarding the $g^2 \mid h$ density saving ($g^{-4}$ vs $g^{-2}$); (iv) the crude lower bound $\mathcal{W} > 4/5$ (whereas $\mathcal{W} \approx 1.835$); and (v) separating the Euler products rather than canceling their local factors against $\mathcal{W}^{-2}$. We eliminate all five losses cleanly.

First, for any squarefree-supported multiplicative function $g_0$ on $\mathcal{P}_0$ defined by $g_0(p) := \frac{2}{p - 2}$ ($p \in \mathcal{P}_0$), put $G_0(\xi) := \sum_{d < \xi} \mu(d)^2 g_0(d)$ (summing over squarefree $d < \xi$ composed solely of primes in $\mathcal{P}_0$).

**Lemma 2.2 (exact prime-by-prime Selberg sieve lower bound).** *Let $\xi > 1$, let $S \subseteq \mathcal{P}_0$ be any finite set of primes, and define a multiplicative function $g$ on squarefree integers composed of primes in $\mathcal{P}_0$ by $g(p) = \frac{1}{p - 1}$ for $p \in S$ and $g(p) = \frac{2}{p - 2}$ for $p \in \mathcal{P}_0 \setminus S$. Put $G(\xi) := \sum_{d < \xi} \mu(d)^2 g(d)$. Then, uniformly in $\xi > 1$ and $S$,*
```math
G(\xi) \ge G_0(\xi) \prod_{p \in S} \frac{p - 2}{p - 1}.
```

*Proof.* Switch the primes of $S$ one at a time from $\alpha = \frac{2}{q - 2}$ to $\beta = \frac{1}{q - 1}$. At a single step for a prime $q \in S$, let $g_{\text{cur}}$ be the current multiplicative weight, and split the sum over $d < \xi$ into $q \nmid d$ and $q \mid d$:
```math
G_{\text{before}}(\xi) = A + \alpha B, \qquad G_{\text{after}}(\xi) = A + \beta B,
```
where $A = \sum_{d < \xi,\, q \nmid d} \mu(d)^2 g_{\text{cur}}(d)$ and $B = \sum_{d < \xi/q,\, q \nmid d} \mu(d)^2 g_{\text{cur}}(d)$. Since every summand is nonnegative and $\xi / q < \xi$, we have $0 \le B \le A$. Since $0 \le \beta < \alpha$,
```math
(A + \alpha B)(1 + \beta) - (A + \beta B)(1 + \alpha) = (\alpha - \beta)(B - A) \le 0,
```
so $G_{\text{after}}(\xi) \ge \frac{1 + \beta}{1 + \alpha} G_{\text{before}}(\xi) = \frac{q / (q - 1)}{q / (q - 2)} G_{\text{before}}(\xi) = \frac{q - 2}{q - 1} G_{\text{before}}(\xi)$. Iterating over all $q \in S$ proves the lemma. $\square$

**Theorem 2.3 (improved unconditional binary digit-frequency bound for $E_2^2$).** *Grant the same published inputs as Phase 23 `GF-29` (Serre 1985 for $\eta(12\tau)^2$; Wirsing's mean-value theorem; Matomäki–Radziwiłł Corollary 1.2(ii)). Define*
```math
\mathcal{E}_0 := \prod_{p \in \mathcal{P}_0} \left(1 + \frac{2}{(p - 1)(p^2 + 1)}\right), \qquad K_* := \frac{3\sqrt{2\pi}}{32}\, \Gamma(1/4)^2\, \mathcal{E}_0.
```
*Then for every fixed $L \ge 1$ and every $d \in \{0, 1\}$,*
```math
\frac{1}{8 K_*} \le \liminf_{N \to \infty} f_{d^L}(N; E_2^2, 2) \le \limsup_{N \to \infty} f_{d^L}(N; E_2^2, 2) \le 1 - \frac{1}{8 K_*}.
```
*Exact zero-float rational certificates yield $\mathcal{E}_0 < 1.028980$ and $K_* < 3.178808$, hence $8 K_* < 25.431 < 26$, which gives the unconditional bound*
```math
\frac{1}{26} \le \liminf_{N \to \infty} f_{d^L}(N; E_2^2, 2) \le \limsup_{N \to \infty} f_{d^L}(N; E_2^2, 2) \le \frac{25}{26}, \qquad \limsup_{N \to \infty} \bigl|f_{d^L}(N; E_2^2, 2) - \tfrac{1}{2}\bigr| \le \frac{6}{13}.
```

*Proof.* Set $A_N = (\log N)^{3/4}$, $V = (\log N)^3$, and $H = \lfloor t A_N \rfloor$ for a fixed constant $t > 0$. Fix any $\beta \in (0, 1/2)$ and put $\xi = N^\beta$. By Phase 23 `GF-29` (equations (4) and (6)), it suffices to show
```math
\limsup_{N \to \infty} \frac{A_N^2}{(H^2 / 2)\, N} \sum_{h = 1}^{H - 1} (H - h) P_h(N) \le K_* C_\eta^2, \tag{2.1}
```
where $P_h(N) = \#\{1 \le n \le N : a_2(n) a_2(n + h) \ne 0\}$: indeed, substituting (2.1) into $W_\sigma(N) \ge H S_\sigma(N) - H - \sum_{h=1}^{H-1} (H - h) P_h(N)$ (with $S_\sigma(N) \sim \frac{1}{2} C_\eta N / A_N$) yields $\liminf_{N \to \infty} W_\sigma(N)/N \ge \frac{1}{2} C_\eta t - \frac{1}{2} K_* C_\eta^2 t^2$, whose maximum at $t = (2 K_* C_\eta)^{-1}$ is $\frac{1}{8 K_*}$.

To prove (2.1), fix $1 \le h < H$ and split supported pairs $(n, n+h)$ with $1 \le n \le N$ into class (i) ($\max(v(n), v(n+h)) > V$) and class (ii) ($v(n), v(n+h) \le V$), where $v(n) = \prod_{p \in \mathcal{P}_0} p^{v_p(12n+1)/2}$. By Phase 22 `partitions-carry-and-lemma-s.md` §1.4, class (i) contributes at most $2N/(\log N)^3 + 9\sqrt{N} = o(N / A_N^2)$ uniformly in $h$.

For class (ii), fix $(v, v')$ composed of primes in $\mathcal{P}_0$ with $v, v' \le V$, and write $g = \gcd(v, v')$, $v = gw$, $v' = gw'$ with $\gcd(w, w') = 1$. By Lemma S.4(a), $g^2 \mid h$, so write $h = g^2 h'$. We first observe that **$\gcd(ww', h') = 1$** is necessary for any solution to exist: if $p \mid w$ (so $a := v_p(g) \ge 0$, $b := v_p(w) \ge 1$) and $p \mid h'$, then $p^{2a+2b} \mid (12n+1)$ and $p^{2a+1} \mid 12h$, whence $v_p(12(n+h)+1) \ge 2a + 1 > 2a = 2 v_p(v')$, forcing $p \mid u(n+h)$, contradiction; symmetrically $p \mid w'$ and $p \mid h'$ is impossible.

Now let $n = n_0 + m L$ ($L = g^2 w^2 w'^2 \le V^4 = (\log N)^{12}$) parametrize the unique admissible progression modulo $L$ (Lemma S.4(b)), with $X = N/L + O(1) = (1 + o(1)) N/L$ consecutive integers $m \in I$, and $F(m) = (A_1 m + B_1)(A_2 m + B_2)$ where $A_1 = 12 w'^2$, $A_2 = 12 w^2$, and $A_1 B_2 - A_2 B_1 = 144 h'$ (Lemma S.4(c)). Because $u(n) = A_1 m + B_1$ and $u(n+h) = A_2 m + B_2$ have **no** prime factors in $\mathcal{P}_0$ (even among primes dividing $vv'$), we sift by the **entire** prime set $\mathcal{Q} = \{p \in \mathcal{P}_0 : p < \xi\}$ without omitting $p \mid vv'$! Let us count the roots $\rho(p)$ of $F(m) \equiv 0 \pmod p$ for every $p \in \mathcal{Q}$:
- If $p \nmid ww'$ and $p \nmid h'$: $p \nmid A_1 A_2$ and $p \nmid (A_1 B_2 - A_2 B_1)$, so $\rho(p) = 2$ (even when $p \mid g$).
- If $p \nmid ww'$ and $p \mid h'$: $p \nmid A_1 A_2$ and $p \mid (A_1 B_2 - A_2 B_1)$, so $\rho(p) = 1$.
- If $p \mid w$ (hence $p \nmid w'$ and $p \nmid h'$): $p \mid A_2$, while $v_p(12n_0 + 1) \ge 2a + 2 > 2a = v_p(12h)$ forces $v_p(12(n_0+h)+1) = 2a$, so $p \nmid B_2$; thus $A_2 m + B_2 \equiv B_2 \not\equiv 0 \pmod p$ has no root and $A_1 m + B_1 \equiv 0 \pmod p$ has one root, giving $\rho(p) = 1$.
- If $p \mid w'$: symmetrically $\rho(p) = 1$.

In all cases $\rho(p) \in \{1, 2\} < p$ (since $p \ge 5$), with $\rho(p) = 1$ precisely when $p \mid ww'h'$, and $\rho(p) = 2$ otherwise. Applying Selberg's upper bound (Lemma S.1) and Lemma 2.2 with $S = \{p \in \mathcal{P}_0 : p \mid ww'h'\}$ gives
```math
\#\bigl\{\text{class (ii) for }(v, v')\bigr\} \le \frac{(1 + o(1)) N}{g^2 w^2 w'^2 \, G_0(\xi)} \left(\prod_{p \mid ww'} \frac{p - 1}{p - 2}\right) \left(\prod_{\substack{p \in \mathcal{P}_0 \\ p \mid h'}} \frac{p - 1}{p - 2}\right) + \xi^2 (1 + \log \xi)^2.
```
Since $\xi = N^\beta$ with $\beta < 1/2$, summing the remainder over at most $V^2 = (\log N)^6$ pairs $(v, v')$ yields $O((\log N)^8 N^{2\beta}) = o(N / A_N^2)$.

Next, evaluate $G_0(\xi)$ asymptotically via Wirsing's theorem (1961, Satz 1, already an input of Phase 23 §1). Put $f_0(d) := d \mu(d)^2 g_0(d)$, a nonnegative multiplicative function with $f_0(p) = \frac{2p}{p-2} \le \frac{10}{3}$ on $p \in \mathcal{P}_0$, $f_0(p) = 0$ outside $\mathcal{P}_0$, and $f_0(p^k) = 0$ for $k \ge 2$. By the prime number theorem in progressions mod $12$, $\sum_{p \le x} f_0(p) \frac{\log p}{p} \sim \frac{3}{2} \log x$ (sieve dimension $\kappa = 3/2$). Wirsing's theorem gives $M(x) := \sum_{d \le x} f_0(d) \sim \frac{e^{-3\gamma_E/2}}{\Gamma(3/2)} \frac{x}{\log x} \prod_{p \le x,\, p \in \mathcal{P}_0} (1 + \frac{2}{p-2})$, and partial summation with left limits $M(x^-) := \sum_{d < x} f_0(d)$ gives $G_0(\xi) = \frac{M(\xi^-)}{\xi} + \int_1^\xi \frac{M(u)}{u^2}\,du$ (dividing the leading constant by $\kappa = \frac{3}{2}$ without affecting the asymptotic), yielding
```math
G_0(\xi) \sim \frac{e^{-3\gamma_E/2}}{\Gamma(5/2)} \prod_{\substack{p < \xi \\ p \in \mathcal{P}_0}} \left(1 - \frac{2}{p}\right)^{-1} = \frac{4 e^{-3\gamma_E/2}}{3\sqrt{\pi}} \prod_{\substack{p < \xi \\ p \in \mathcal{P}_0}} \left(1 - \frac{2}{p}\right)^{-1}.
```
Writing $1 - \frac{2}{p} = (1 - \frac{1}{p})^2 \bigl(1 - \frac{1}{(p-1)^2}\bigr)$ and recalling from Phase 23 §2 that $\Pi_{\mathcal{P}_0}(N^\beta) \sim \beta^{-3/4} \frac{C_\eta}{\mathcal{W}} A_N^{-1}$ with $\mathcal{W} = \frac{4 e^{3\gamma_E/4}}{\Gamma(1/4)} \prod_{p \in \mathcal{P}_0} (1 - p^{-2})^{-1}$, the $e^{3\gamma_E/2}$ factors cancel identically:
```math
\frac{1}{G_0(N^\beta)} \sim \frac{3\sqrt{\pi}}{4} \beta^{-3/2} \frac{\Gamma(1/4)^2}{16} \left[\prod_{p \in \mathcal{P}_0} \left(1 - \frac{1}{(p - 1)^2}\right) \left(1 - \frac{1}{p^2}\right)^2\right] \frac{C_\eta^2}{A_N^2}. \tag{2.2}
```

Now sum the class (ii) main term over $1 \le h \le H - 1$ with weight $(H - h)$, keeping $h = g^2 h'$ and $\gcd(ww', h') = 1$. Expanding $\prod_{p \in \mathcal{P}_0,\, p \mid h'} \frac{p-1}{p-2} = \sum_{d \mid h',\, p \mid d \Rightarrow p \in \mathcal{P}_0} \frac{\mu(d)^2}{\prod_{p \mid d}(p-2)}$ (note $\gcd(d, ww') = 1$ automatically), and dropping $\gcd(m, ww') = 1$ after writing $h' = d m$:
```math
\sum_{\substack{1 \le h' < H/g^2 \\ \gcd(h', ww') = 1}} (H - g^2 h') \prod_{\substack{p \in \mathcal{P}_0 \\ p \mid h'}} \frac{p - 1}{p - 2} \le \sum_{\substack{d < H/g^2,\, \gcd(d, ww') = 1 \\ p \mid d \Rightarrow p \in \mathcal{P}_0}} \frac{\mu(d)^2}{\prod_{p \mid d}(p - 2)} \sum_{1 \le m < H/(g^2 d)} (H - g^2 d m).
```
For every real $M = H/(g^2 d) > 0$ and $K = \lceil M \rceil - 1 \ge 0$, $\sum_{m=1}^K (M - m) = KM - \frac{K(K+1)}{2} \le \frac{M^2}{2}$ (since $M^2 - 2KM + K^2 + K = (M - K)^2 + K \ge 0$). Hence the inner sum over $m$ is at most $\frac{H^2}{2 g^2 d}$, and the $h'$-sum is bounded by
```math
\frac{H^2}{2 g^2} \prod_{\substack{p \in \mathcal{P}_0 \\ p \nmid ww'}} \left(1 + \frac{1}{p(p - 2)}\right).
```
Substituting this into the $(g, w, w')$-sum (where $g, w, w'$ run over $\mathcal{P}_0$-smooth integers with $\gcd(w, w') = 1$) factors completely over $p \in \mathcal{P}_0$: at each prime $p \in \mathcal{P}_0$, the $(a, b, c) = (v_p(g), v_p(w), v_p(w'))$ contribution is
- $b = c = 0$ ($p \nmid ww'$): $\sum_{a \ge 0} p^{-4a} \bigl(1 + \frac{1}{p(p-2)}\bigr) = \frac{p^4}{p^4 - 1}\bigl(1 + \frac{1}{p(p-2)}\bigr)$;
- $\max(b, c) \ge 1, \min(b, c) = 0$ ($p \mid ww'$): $2 \frac{p^4}{p^4 - 1} \frac{1}{p^2 - 1} \frac{p - 1}{p - 2}$.

Multiplying this local factor by the bracketed local factor $\bigl(1 - \frac{1}{(p-1)^2}\bigr)\bigl(1 - \frac{1}{p^2}\bigr)^2$ in (2.2) yields the exact algebraic cancellation:
```math
\frac{p(p - 2)}{(p - 1)^2} \cdot \frac{(p^2 - 1)^2}{p^4} \cdot \frac{p^4}{p^4 - 1} \left(1 + \frac{1}{p(p - 2)} + \frac{2(p - 1)}{(p^2 - 1)(p - 2)}\right) = \frac{p^3 - p^2 + p + 1}{(p - 1)(p^2 + 1)} = 1 + \frac{2}{(p - 1)(p^2 + 1)}.
```
Multiplying over $p \in \mathcal{P}_0$ produces $\mathcal{E}_0$. Taking $\limsup_{N \to \infty}$ and then letting $\beta \uparrow \frac{1}{2}$ (so $\beta^{-3/2} \downarrow 2\sqrt{2}$ and $\frac{3\sqrt{\pi}}{4} \cdot 2\sqrt{2} \cdot \frac{\Gamma(1/4)^2}{16} = \frac{3\sqrt{2\pi}}{32} \Gamma(1/4)^2$) proves (2.1).

Finally, for the explicit zero-float numerical certificate:
- *Euler product $\mathcal{E}_0$:* Split at $p \le 100$ with $P := \prod_{p \in \mathcal{P}_0,\, p \le 100}\bigl(1 + \frac{2}{(p-1)(p^2+1)}\bigr)$. Every tail prime $p \ge 101$ is odd ($p = 2j + 1$, $j \ge 50$), so $(p - 1)(p^2 + 1) = 2j(4j^2 + 4j + 2) > 8 j^3$ and $\frac{2}{(p-1)(p^2+1)} < \frac{1}{4 j^3}$. Hence the log-tail is bounded by $\sum_{j \ge 50} \frac{1}{4 j^3} < \int_{49}^\infty \frac{dt}{4 t^3} = \frac{1}{8 \cdot 49^2} = \frac{1}{19208}$. Using $e^u < (1 - u)^{-1}$ for $0 < u < 1$ gives $\mathcal{E}_0 < \frac{19208}{19207} P < 1.028980$ (exact rational inequality).
- *$\pi$ and $\sqrt{2\pi}$:* By Machin's formula and alternating arctangent bounds, $\pi = 16 \arctan(\frac{1}{5}) - 4 \arctan(\frac{1}{239}) < 16 \sum_{j=0}^{4} \frac{(-1)^j}{(2j+1) 5^{2j+1}} - 4(\frac{1}{239} - \frac{1}{3 \cdot 239^3}) < 3.1416$, and squaring gives $2\pi < (25067/10000)^2$, hence $\sqrt{2\pi} < 2.5067$.
- *$\Gamma(1/4)$:* On $[0, 16]$, integrating the even-degree-$80$ Taylor upper polynomial $e^{-x} \le \sum_{j=0}^{80} \frac{(-x)^j}{j!}$ against $x^{-3/4}$ (using $\int_0^{16} x^{j-3/4}\,dx = \frac{8 \cdot 16^j}{4j+1}$) and bounding the tail on $[16, \infty)$ by $\int_{16}^\infty x^{-3/4} e^{-x}\,dx < e^{-16} < 2^{-16}$ yields $\Gamma(1/4) < 8 \sum_{j=0}^{80} \frac{(-16)^j}{j!(4j+1)} + 2^{-16} < 3.625626 < 3.6257$.

Combining these three exact `Fraction` certificates in [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py) (zero floating-point checks) gives $K_* < 3.178808$ and $8 K_* < 25.431 < 26$, so $\frac{1}{8 K_*} > \frac{1}{26}$. $\square$

### 2.3 What remains open for $E_2^2$

**Status: Open.** Binary simple normality of $E_2^2$ (equivalently $B_N(H_N) = o(N)$ for a cutoff $H_N$ with $H_N / A_N \to \infty$, e.g. $H_N = \lceil A_N \log\log N \rceil$, Phase 23 `GF-29` equation (5)) and disjunctivity of $E_2^2$ remain **open**. Although Theorem 2.1 expresses $a_2(n)$ directly via the difference of two theta functions of discriminant $-144$ and Theorem 2.3 tightens the unconditional lower density from $1/40000$ to $1/26$, the cited gap moment alone gives no vanishing truncation bound at $H_N \asymp A_N$, and proving $\frac{1}{N} \sum_{m \le N} s(m) g(m) \to 0$ runs into the obstacle of obtaining uniform cancellation in shifted correlations $\sum_{m \le N} s(m) \prod_{h \in T} \mathbf{1}_U(m - h)$ across logarithmic shift scales ($H_N \asymp A_N$ and beyond, $H_N / A_N \to \infty$). Because $s(m)$ is governed by the non-abelian $D_4$ ring class field of discriminant $-144$ (not a Dirichlet character; Phase 22 Proposition 4.2), such cancellation against sparse multiplicative survival indicators lies beyond current sieve and Matomäki–Radziwiłł methods.

---

## 3. Sub-track B3: Rational-scaling Conjecture 5.5, complement symmetry, and exceptional primes

Recall from Phase 23 `GF-30` (`rational-scalings-and-signed-special.md`) that for $z \in \{E_b, E_b^3\}$ and reduced $a/d$ with $\gcd(d, b) = 1$, $a \ne 0$, the limit law of the nonzero atoms of $\frac{a}{d} z$ in base $b$ is always invariant under $c \mapsto -c$ (Theorem 1.1 of `GF-30`), and for odd $d > 1$ with even $t = \operatorname{ord}_d(b)$ ($h = t/2$), $w_0^+ - w_0^- = \operatorname{sgn}(a)\, \Xi_b(d)/(3t)$ for $E_b$ (resp. $\operatorname{sgn}(a)\, \Xi_3(d)/L$ for $E_b^3$), where $p \mid d_-$ is **$b$-exceptional** if $A^-_p(t_p/2) \equiv 0 \pmod p$. Throughout this section, replacing $a \mapsto -a$ swaps the geometric boundary sides $(w_0^+, w_0^-)$ and reflects digits $e \mapsto b - 1 - e$, so nonnormality and boundary balance ($w_0^+ = w_0^-$) are invariant across all reduced numerators $a \ne 0$; all numerical boundary values $(w_0^+, w_0^-)$ and digit vectors below are stated in the positive-numerator orientation ($a > 0$), with the specific numerator coset noted whenever $t < p - 1$.

### 3.1 The base-$2$ vs base-$b \ge 3$ complement-symmetry dichotomy

**Theorem 3.1 (base-$2$ complement identity vs base-$b \ge 3$ interior obstructions).** *Let $b \ge 2$, $\gcd(d, b) = 1$, $\gcd(a, d) = 1$. For every $c \in \{1, \dots, d - 1\}$, the purely periodic base-$b$ expansion of $(d - c)/d$ is the digitwise $(b - 1)$-complement of that of $c/d$, so for every digit $e \in \{0, \dots, b - 1\}$,*
```math
f_e\bigl(\tfrac{c}{d}; b\bigr) + f_e\bigl(\tfrac{d - c}{d}; b\bigr) = f_e\bigl(\tfrac{c}{d}; b\bigr) + f_{b - 1 - e}\bigl(\tfrac{c}{d}; b\bigr).
```
1. *(Base $b = 2$):* $f_0(\frac{c}{d}; 2) + f_0(\frac{d-c}{d}; 2) = f_0(\frac{c}{d}; 2) + f_1(\frac{c}{d}; 2) = 1$ **identically** for every $c/d$ (even when $-1 \notin \langle 2 \rangle \pmod d$, e.g. $d = 7$ where $f_0(1/7; 2) = 2/3$ and $f_0(6/7; 2) = 1/3$ sum to $1$). Therefore, for any signed lacunary limit law with reflection-symmetric nonzero atoms ($m_c = m_{d-c}$), base-$2$ simple normality holds **if and only if** the single boundary balance equation $w_0^+ = w_0^-$ holds.
2. *(Every base $b \ge 3$):* complement symmetry ($m_c = m_{d-c}$ and $w_0^+ = w_0^-$) enforces only $f_e = f_{b-1-e}$ for all $e$, leaving $\lfloor (b - 1)/2 \rfloor \ge 1$ independent interior digit-pair equations $f_e + f_{b-1-e} = \frac{2}{b}$ (and $f_{(b-1)/2} = \frac{1}{b}$ for odd $b$) completely unconstrained.

*Proof.* For $c \in \{1, \dots, d - 1\}$, $\frac{c}{d} + \frac{d-c}{d} = 1 = \sum_{n \ge 1} (b - 1) b^{-n}$ with no carries because $c/d$ is not a terminating $b$-adic rational ($\gcd(d, b) = 1$), so $d_n((d-c)/d) = (b - 1) - d_n(c/d)$ for every $n \ge 1$. Averaging over the reflection-symmetric nonzero atoms and boundary split $(w_0^+, w_0^-)$ gives $f_e = f_{b-1-e}$ whenever $w_0^+ = w_0^-$. For $b = 2$, $f_0 + f_1 = 1$ forces $f_0 = f_1 = 1/2$. For $b \ge 3$, $f_0 = f_{b-1}$ does not fix $f_0$ unless every interior pair $(e, b - 1 - e)$ also carries mass $2/b$. $\square$

### 3.2 Universal odd-order family $\frac{1}{b^2 + b + 1} E_b$ across all bases $b \ge 2$

**Theorem 3.2 (universal family $\frac{1}{b^2 + b + 1} E_b$).** *For every integer radix $b \ge 2$, let $d = b^2 + b + 1$. Then $d$ is odd, $\gcd(d, b) = 1$, $\operatorname{ord}_d(b) = 3$ (odd), and the limit law of $\frac{1}{b^2 + b + 1} E_b$ in base $b$ has balanced zero split $w_0^+ = w_0^- = \frac{1}{18}$ and exact digit frequencies:*
- *For $b = 2$ ($d = 7$): $f_0 = f_1 = \frac{1}{2}$ (simply normal in base $2$).*
- *For $b = 3$ ($d = 13$): $(f_0, f_1, f_2) = (\frac{19}{54}, \frac{8}{27}, \frac{19}{54})$ (complement-symmetric, not simply normal).*
- *For every $b \ge 4$:*
```math
f_0 = f_{b-1} = \frac{19}{54}, \qquad f_1 = f_{b-2} = \frac{4}{27}, \qquad f_e = 0 \quad (2 \le e \le b - 3).
```
*In particular, for every base $b \ge 3$, $\frac{1}{b^2 + b + 1} E_b$ is complement-symmetric yet strictly non-simply-normal (and misses every digit $2 \le e \le b - 3$ asymptotically whenever $b \ge 5$).*

*Proof.* Since $b(b+1)$ is even, $d = b^2 + b + 1$ is odd and coprime to $b$. As $b^3 - 1 = (b - 1)d$ and $b \not\equiv 1 \pmod d$, we have $t = \operatorname{ord}_d(b) = 3$, with $q = b^{-1} \equiv b^2 \pmod d$ and $q^2 \equiv b \pmod d$. Computing $\mathrm{tm}(i) = (-1)^i q^{P(i)} \bmod d$ over one half-period ($P(0) = 0, P(1) = 1, P(-1) = 2, P(2) = 5 \equiv 2, P(-2) = 7 \equiv 1, P(3) = 12 \equiv 0 \pmod 3$) gives $\mathrm{tm}(0) = 1$, $\mathrm{tm}(1) = -b^2$, $\mathrm{tm}(-1) = -b$, $\mathrm{tm}(2) = b$, $\mathrm{tm}(-2) = b^2$, $\mathrm{tm}(3) = -1$. Using $b^2 \equiv -b - 1 \pmod d$, the exact head sums $A^-(k)$ and $A(k)$ for $k = 0, 1, 2$ are:
- $A(0) = 1$, $A(1) = 1 - b^2 - b \equiv 2$, $A(2) = 2 + b + b^2 \equiv 1$ (and by antiperiodicity $A(k + 3) = -A(k)$, the six $+$ run classes carry orbits of $\pm 1$ with weight $4/9$ and $\pm 2$ with weight $2/9$).
- $A^-(0) = 0$, $A^-(1) = 1 - b^2 \equiv b + 2$, $A^-(2) = A(1) + b = b + 2$ (and $A^-(k + 3) = -A^-(k)$, so the six $-$ run classes carry $0^\pm$ with $w_0^+ = w_0^- = 1/18$, and orbits of $\pm(b + 2)$ with weight $2/9$).

Now evaluate the base-$b$ period-3 expansions of the three nonzero orbits using $\frac{c}{d} = \frac{c(b - 1)}{b^3 - 1}$:
- $c = 1$: $1 \cdot (b - 1) = (0, 0, b - 1)_b$; averaging with its complement gives digits $0$ and $b - 1$ with weight $1/2$ each.
- $c = 2$ (for $b \ge 3$): $2(b - 1) = 0 \cdot b^2 + 1 \cdot b + (b - 2) = (0, 1, b - 2)_b$; averaging with its complement $(b - 1, b - 2, 1)_b$ gives $0, b - 1$ with weight $1/6$ each and $1, b - 2$ with weight $1/3$ each.
- $c = b + 2$ (for $b \ge 3$): $(b + 2)(b - 1) = b^2 + b - 2 = 1 \cdot b^2 + 0 \cdot b + (b - 2) = (1, 0, b - 2)_b$; averaging with its complement gives the same digit distribution ($0, b-1$ with weight $1/6$; $1, b-2$ with weight $1/3$).

Summing the weights for $b \ge 4$ (where $0, 1, b - 2, b - 1$ are distinct): $f_0 = f_{b-1} = \frac{4}{9}\cdot\frac{1}{2} + \frac{4}{9}\cdot\frac{1}{6} + \frac{1}{9}\cdot\frac{1}{2} = \frac{19}{54}$, $f_1 = f_{b-2} = \frac{4}{9}\cdot\frac{1}{3} = \frac{4}{27}$, and $f_e = 0$ otherwise. At $b = 3$, digits $1$ and $b - 2 = 1$ merge to $f_1 = 8/27$. At $b = 2$, $2(b-1) = 2 = (0, 1, 0)_2$ and $(b+2)(b-1) = 4 = (1, 0, 0)_2$ merge with $0$ and $1$, giving $f_0 = f_1 = 1/2$. $\square$

### 3.3 Complete primitive-root impossibility theorem in every base $b \ge 3$

Phase 23 `GF-30` (§4) tested 42,296 exact laws in bases $3 \le b \le 10$ and found zero simply normal rational scalings of $E_b$ or $E_b^3$, leaving the general question open. We now prove unconditionally that **no primitive-root prime denominator $p$ ever yields simple normality in any base $b \ge 3$**.

**Theorem 3.3 (primitive-root impossibility for $E_b$ and $E_b^3$ in bases $b \ge 3$).** *Let $b \ge 3$ and let $p \nmid 2b$ be an odd prime such that $b$ is a primitive root modulo $p$ (so $t = \operatorname{ord}_p(b) = p - 1$ is even). Then for every $a$ coprime to $p$, neither $\frac{a}{p} E_b$ nor $\frac{a}{p} E_b^3$ is simply normal in base $b$.*

*Proof.* Because $b$ is a primitive root mod $p$, all $p - 1$ nonzero residues $\{1, \dots, p - 1\}$ form a single $\times b$-orbit, so every nonzero atom $c/p$ receives equal limit mass $\frac{1 - w_0}{p - 1}$, where $w_0 = w_0^+ + w_0^-$. By Phase 23 `GF-30` §4, $w_0 > 0$ (since $A^-(0) = 0$ and $V(-1) = 0$). Also $w_0 < 1$ because $A^-(1) = 1 - q \not\equiv 0 \pmod p$ (as $b \not\equiv 1 \pmod p$) and $V(0) = 1 \not\equiv 0 \pmod p$.

Write $p = q_0 b + r$ with $q_0 \ge 0$ and $1 \le r \le b - 1$ (since $p \nmid b$), and put $N_e := \#\{1 \le c \le p - 1 : \lfloor b c / p \rfloor = e\}$. Clearly $N_0 = \lfloor p / b \rfloor = q_0$ and $N_{b-1} = q_0$, while every interior digit $e \in \{1, \dots, b - 2\}$ satisfies $N_e \in \{q_0, q_0 + 1\}$ with $\sum_{e=1}^{b-2} (N_e - q_0) = (p - 1) - b q_0 = r - 1$.
- If $r = 1$ ($p \equiv 1 \pmod b$): $N_e = q_0 = \frac{p - 1}{b}$ for every interior digit $1 \le e \le b - 2$, so $f_e = \frac{1 - w_0}{b} < \frac{1}{b}$ strictly (since $w_0 > 0$).
- If $2 \le r \le b - 2$: among the $b - 2$ interior digits, $r - 1 \ge 1$ have $N_e = q_0 + 1$ and $b - r - 1 \ge 1$ have $N_e = q_0$, so their frequencies differ by $\frac{1 - w_0}{p - 1} > 0$, precluding equality.
- If $r = b - 1$ ($p \equiv -1 \pmod b$): then $N_e = q_0 + 1 = \frac{p + 1}{b}$ for every $1 \le e \le b - 2$, so $f_e = \frac{p + 1}{b} \cdot \frac{1 - w_0}{p - 1}$. Setting $f_e = \frac{1}{b}$ forces
```math
w_0 = \frac{2}{p + 1}. \tag{3.1}
```
  We check the denominator of $w_0$ in (3.1):
  - For $\frac{a}{p} E_b$: by reflection symmetry ($k \mapsto -k$ on $-$ runs and $k \mapsto -1 - k$ on $+$ runs) and $A^-(k + t) = -A^-(k)$, $A(k + t) = -A(k)$, the zero counts on both run types are even (on $-$ runs $0$ and $t$ pair, and $h, t+h$ pair), so $w_0 = \frac{n_0}{3(p - 1)}$ for an integer $n_0$. Equation (3.1) then requires $(p + 1) \mid 6(p - 1) = 6(p + 1) - 12$, hence $(p + 1) \mid 12$, leaving only $p \in \{3, 5, 11\}$.
  - For $\frac{a}{p} E_b^3$: by Theorem 2.3 of `GF-30`, $w_0 = \frac{n_0}{p(p - 1)}$ for an integer $n_0$, so (3.1) requires $(p + 1) \mid 2p(p - 1) = 2(p + 1)(p - 2) + 4$, hence $(p + 1) \mid 4$, leaving only $p = 3$.

Finally, test the finite residue list $p \in \{3, 5, 11\}$ with $p \equiv -1 \pmod b$, $b \ge 3$, and $b$ a primitive root mod $p$:
- $p = 3$: $3 \equiv -1 \pmod b$ with $b \ge 3$ forces $b = 4 \equiv 1 \pmod 3$, which is not a primitive root mod $3$. (This already finishes $\frac{a}{p} E_b^3$ completely!)
- $p = 5$: $5 \equiv -1 \pmod b$ with $b \ge 3$ forces $b \in \{3, 6\}$; $b = 6 \equiv 1 \pmod 5$ is not a primitive root, and for $(b, p) = (3, 5)$, exact evaluation gives $w_0^+ = 1/4 \ne 1/6 = w_0^-$ for $a > 0$ (and $1/6 \ne 1/4$ for $a < 0$).
- $p = 11$: $11 \equiv -1 \pmod b$ with $b \ge 3$ forces $b \in \{3, 4, 6, 12\}$; $3, 4$ have order $5 < 10$ and $12 \equiv 1 \pmod{11}$, leaving only $(b, p) = (6, 11)$. Remarkably, for $\frac{a}{11} E_6$, $w_0 = \frac{1}{10} + \frac{1}{15} = \frac{1}{6} = \frac{2}{11 + 1}$ satisfies (3.1) **exactly**, so all four interior base-$6$ digits have exact frequency $\frac{1}{6}$, yet the boundary split is unbalanced: for $a > 0$, $w_0^+ = \frac{1}{10} \ne \frac{1}{15} = w_0^-$, giving $f_0 = \frac{11}{60}$ and $f_5 = \frac{3}{20}$ (swapped to $f_0 = \frac{3}{20}, f_5 = \frac{11}{60}$ for $a < 0$)! $\square$

### 3.4 Exact analysis of $\frac{a}{113} E_{10}$, new balanced $b$-exceptional primes, and Conjecture 5.5 to $40{,}000$

For $\frac{a}{113} E_{10}$ (Phase 23 `GF-30`, Example 3.4), $10$ is a primitive root mod $113$ ($t = 112 \equiv 0 \pmod 4$, $h = 56$) with $A^-_{113}(k) \equiv 0 \pmod{113}$ for $k \in \{29, 56, 83, 112\}$, giving $\Xi_{10}(113) = (-1)^{29} + (-1)^{56} + (-1)^{83} + (-1)^{112} = 0$ and balanced split $w_0^+ = w_0^- = \frac{1}{56}$ ($w_0 = \frac{1}{28}$). Since $113 = 11 \cdot 10 + 3 \equiv 3 \pmod{10}$, the mechanism of Theorem 3.3 explains the exact digit vector from first principles: $N_3 = N_6 = 12$ while $N_e = 11$ for all $e \notin \{3, 6\}$, and each nonzero atom carries mass $\frac{1 - 1/28}{112} = \frac{27}{3136}$, giving $f_3 = f_6 = 12 \cdot \frac{27}{3136} = \frac{81}{784}$, $f_1 = f_2 = f_4 = f_5 = f_7 = f_8 = 11 \cdot \frac{27}{3136} = \frac{297}{3136}$, and $f_0 = f_9 = \frac{297}{3136} + \frac{1}{56} = \frac{353}{3136}$.

Phase 23 §3.5 noted that a balanced $b$-exceptional prime can occur in **two** ways: $t_p \equiv 0 \pmod 4$ (requiring odd zeros to cancel $1 + (-1)^h = 2$, realized by $p = 113$ in base $10$) or $t_p \equiv 2 \pmod 4$ (where $1 + (-1)^h = 0$ already cancels, so a single half-period zero $k = h$ suffices!).

**Theorem 3.4 (new balanced $b$-exceptional primes and infinite base families).**
1. *(New $t \equiv 2 \pmod 4$ witnesses):* The pairs $(b, p) \in \{(4, 29),\ (6, 59),\ (6, 1613)\}$ are **balanced $b$-exceptional primes** with $t_p \equiv 2 \pmod 4$ and unique zero $k = h$ in $\{1, \dots, h\}$, giving a balanced zero split ($w_0^+ = w_0^-$) and complement-symmetric limit word law for every reduced numerator $a \ne 0$ despite even $\operatorname{ord}_p(b)$:
   - $(b, p) = (4, 29)$: $t = 14$, $h = 7$, $w_0^+ = w_0^- = \frac{1}{14}$ for all $29 \nmid a$; the exact base-$4$ digit vector depends on the multiplicative coset of $a \bmod 29$, giving $(\frac{29}{98}, \frac{10}{49}, \frac{10}{49}, \frac{29}{98})$ for $a = 1$ (i.e. $a \in \langle 4 \rangle \pmod{29}$) and $(\frac{27}{98}, \frac{11}{49}, \frac{11}{49}, \frac{27}{98})$ for $a = 2$ (the other coset).
   - $(b, p) = (6, 59)$: $t = 58$, $h = 29$, $w_0^+ = w_0^- = \frac{5}{174}$, exact base-$6$ digits $(\frac{883}{5046}, \frac{410}{2523}, \frac{410}{2523}, \frac{410}{2523}, \frac{410}{2523}, \frac{883}{5046})$ for every $59 \nmid a$ (here $59 \equiv -1 \pmod 6$ with $6$ a primitive root, so all four interior digits agree, yet $w_0 = \frac{5}{87} \ne \frac{2}{60}$).
   - $(b, p) = (6, 1613)$: $t = 806$, $h = 403$, unique zero $k = 403$ in $\{1, \dots, 403\}$, $\Xi_6(1613) = 0$.
2. *(Infinite arithmetic progressions of bases):* Because the modular orbit data, the zero set of $A^-_p(k) \pmod p$, and the balance invariant $\Xi_b(p)$ depend only on $b \bmod p$, every base $b \ge 3$ in any of the infinite arithmetic progressions
```math
b \equiv 4 \pmod{29}, \qquad b \equiv 6 \pmod{59}, \qquad b \equiv 10 \pmod{113} \qquad (\text{and } b \equiv 6 \pmod{1613})
```
*admits an even-order prime denominator $p$ for which $\frac{a}{p} E_b$ has a balanced zero split ($w_0^+ = w_0^-$) and complement-symmetric limit word law in base $b$ (refuting the radix-free converse "complement-symmetric $\iff$ odd order" in infinitely many bases; the numerical base-$b$ cylinder frequencies themselves depend on the actual radix $b$ and, when $t < p - 1$, on the coset of $a \bmod p$).*

*Proof.* Exact modular computation of $A^-_p(k) \pmod p$ in [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py) verifies the zero sets and $\Xi_b(p) = 0$ for each $(b_0, p)$. By Theorem 1.1 and Theorem 2.2 of `GF-30`, the modular orbit weights, zero sets, and boundary balance condition $w_0^+ = w_0^-$ (hence complement symmetry) depend solely on $b \bmod p$. $\square$

**Corollary 3.5 (extended base-$2$ verification of Conjecture 5.5).** *No prime $p \le 40{,}000$ is $2$-exceptional (exact check over all 2,989 primes $p \le 40{,}000$ with $\operatorname{ord}_p(2)$ even in [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py)). Consequently, by `GF-30` Theorem 3.2, for every odd denominator $d \ge 1$ (with the trivial-modulus convention $\operatorname{ord}_1(2) = 1$, which is odd and matches simple normality of $a E_2$ in base $2$) and reduced nonzero numerator $a$ such that either $d_- = 1$ or the negative-involution part $d_-$ has a prime factor $\le 40{,}000$ — and in particular for every odd $1 \le d \le 40{,}000$ — $\frac{a}{d} E_2$ is simply normal in base $2$ if and only if $\operatorname{ord}_d(2)$ is odd.* (This doubles Phase 23's bound of $20{,}000$. Conjecture 5.5 for all odd $d$ remains **Open**.)

---

## 4. Sub-track B4: Multi-radix finite-order normality and joint constraints

Building on the kernel-verified `NormalityChecker/HigherOrderTower.lean` (`GF-29`), we characterize the exact logical implications, discrepancy ceilings, multi-power tower existence criteria (and obstructions), translation behavior, and disjunctivity constraints for simultaneous finite-order normality across related radices $(b, b^k)$ and $(b^{k_1}, b^{k_2})$.

### 4.1 Exact cross-radix order implication and two-sided sharpness

**Theorem 4.1 (exact cross-radix order implication and sharpness).** *Let $b \ge 2$ and $k \ge 2$.*
1. *(Forced base-$b$ order):* For every $L_2 \ge 1$, if $x \in \mathbb{R}$ is $L_2$-normal in base $b^k$, then $x$ is **automatically** $\bigl(k(L_2 - 1) + 1\bigr)$-normal in base $b$.
2. *(Sharpness at the very next order $\ell_* := k(L_2 - 1) + 2$):* For every $b \ge 2$, $k \ge 2$, and $L_2 \ge 1$, there exists an explicit real number $x$ that is $L_2$-normal in base $b^k$ (hence $(k(L_2 - 1) + 1)$-normal in base $b$) yet **fails** to be $\ell_*$-normal in base $b$, with
```math
f_{0^{\ell_*}}(N; x, b) \longrightarrow b^{-\ell_*} \left(1 + \frac{b - 1}{2k}\right) > b^{-\ell_*}.
```
3. *(Reverse non-implication at every order $L_1$):* For every $b \ge 2$, $k \ge 2$, and arbitrarily large $L_1 \ge 1$, there exists an explicit real number $x$ that is $L_1$-normal in base $b$ yet **not even $1$-normal in base $b^k$**.

*Proof.* (1) Write a base-$b$ shift $n = k m + r$ with $0 \le r < k$. For any base-$b$ word $w$ of length $\ell \le k(L_2 - 1) + 1$, we have $r + \ell \le (k - 1) + k(L_2 - 1) + 1 = k L_2$. Thus the digits $d_{km + r + 1} \cdots d_{km + r + \ell}$ lie completely inside the length-$L_2$ base-$b^k$ block starting at shift $m$ (base-$b$ positions $km + 1, \dots, km + k L_2$), corresponding to a disjoint union of exactly $b^{k L_2 - \ell}$ base-$b^k$ length-$L_2$ cylinders. Since $x$ is $L_2$-normal in base $b^k$, the proportion of $0 \le m < M$ reading $w$ at phase $r$ tends to $b^{k L_2 - \ell} \cdot b^{-k L_2} = b^{-\ell}$ for each $r \in \{0, \dots, k - 1\}$. Averaging over $r = 0, \dots, k - 1$ (with at most $k$ incomplete shifts at the end of $[0, N)$) gives $f_w(N; x, b) \to b^{-\ell}$.

(2) Set $B = b^k$ and define a stationary order-$L_2$ Markov chain on the base-$B$ alphabet $\{0, \dots, B - 1\}$ with transition kernel $P_{\text{mix}} = \frac{1}{2} P_{\text{unif}} + \frac{1}{2} P_\Pi$, where $P_{\text{unif}}(D_{L_2} \mid D_0, \dots, D_{L_2-1}) = B^{-1}$ everywhere, and $P_\Pi$ is uniform at every state with nonzero middle suffix $(D_1, \dots, D_{L_2 - 1}) \ne (0, \dots, 0)$, while at suffix $(D_1, \dots, D_{L_2 - 1}) = (0, \dots, 0)$ (which is the empty middle suffix when $L_2 = 1$, so $P_\Pi$ acts at every state $D_0$) we set $P_\Pi(D_{L_2} \mid D_0, 0, \dots, 0) = \mathbf{1}[D_{L_2} = \Pi(D_0)]$ for any bijection $\Pi : \{0, \dots, B - 1\} \to \{0, \dots, B - 1\}$ mapping $S_{\text{in}} := \{D_0 : b \mid D_0\}$ (size $b^{k-1}$) bijectively onto $S_{\text{out}} := \{D_{L_2} < b^{k-1}\}$ (size $b^{k-1}$). Because $\Pi$ is a bijection, the uniform distribution on $\{0, \dots, B - 1\}^{L_2}$ is stationary for both $P_{\text{unif}}$ and $P_\Pi$, hence for $P_{\text{mix}}$. Moreover, every transition probability is an exact rational multiple of $\frac{1}{2 B}$ and is $\ge \frac{1}{2 B} > 0$, so the weighted multigraph on $\{0, \dots, B - 1\}^{L_2}$ (giving each transition $(w, D_{L_2})$ integer multiplicity $2 B \cdot P_{\text{mix}}(D_{L_2} \mid w) \in \{1, 2, B + 1\}$ — specifically $2$ at nonzero middle suffixes when $L_2 \ge 2$, and $B + 1$ or $1$ at the all-zero / empty middle suffix) is balanced with every row and column sum equal to $2B$, and is strongly connected because the uniform part gives multiplicity $\ge 1$ to every de Bruijn edge. By Hierholzer's theorem (`HigherOrderTower.exists_euler_circuit`), it admits a closed Euler tour $W$ of base-$B$ length $2 B^{L_2 + 1}$ whose cyclic length-$L_2$ and length-$(L_2 + 1)$ frequencies match $P_{\text{mix}}$ identically! Repeating $W$ periodically (or adding a sparse $u \in M_b$ to make it irrational) yields an explicit $x$ that is $L_2$-normal in base $b^k$. Now count $0^{\ell_*}$ in base $b$:
- At phases $r \in \{0, \dots, k - 2\}$, $r + \ell_* \le k L_2$, so each phase gives frequency $b^{-\ell_*}$.
- At phase $r = k - 1$, $0^{\ell_*}$ occurs precisely when $D_0 \in S_{\text{in}}$, the middle suffix $(D_1, \dots, D_{L_2 - 1})$ is $(0, \dots, 0)$ (vacuous/empty when $L_2 = 1$), and $D_{L_2} \in S_{\text{out}}$. Under $P_{\text{unif}}$ this has probability $\frac{b^{k-1}}{B^{L_2}} \cdot \frac{b^{k-1}}{B} = b^{-\ell_*}$; under $P_\Pi$ every $D_0 \in S_{\text{in}}$ transitions with probability $1$ into $S_{\text{out}}$, giving probability $\frac{b^{k-1}}{B^{L_2}} = b \cdot b^{-\ell_*}$. Hence phase $k - 1$ has frequency $\frac{1 + b}{2} b^{-\ell_*}$.

Averaging over all $k$ phases yields $f_{0^{\ell_*}}(N; x, b) \to \frac{(k - 1) + (1 + b)/2}{k} b^{-\ell_*} = b^{-\ell_*}(1 + \frac{b - 1}{2k}) > b^{-\ell_*}$. (For the minimal case $(b, k, L_2) = (2, 2, 1)$, the separate length-$8$ Gray-code periodic cycle `00 01 11 10` already achieves $1$-normality in bases $4$ and $2$ with $f_{00} = 3/8 \ne 1/4$.)

(3) Choose an integer $m \ge \max(2, \lceil L_1 / k \rceil)$ so $m k \ge L_1$, and let $u := 0^k 1^{(m - 1)k} \in \{0, \dots, b - 1\}^{mk}$ and $v := T_b u = 0^{k-1} 1^{(m-1)k} 0$. Construct an explicit digit sequence $x$ in stages $j = 1, 2, \dots$: at stage $j$, concatenate $w^{j}$ (length $j m k$, a multiple of $k$) for every $w \in \{0, \dots, b - 1\}^{mk}$ with multiplicity $0$ for $w = v$, multiplicity $2$ for $w = u$, and multiplicity $1$ for all other $w$ (in lexicographic order). Work on the symbolic shift space $\{0, \dots, b - 1\}^{\mathbb{N}}$ (so the two constant strings $0^\infty$ and $(b-1)^\infty$ are distinguished cleanly). Because every block has length divisible by $k$, the base-$b^k$ phase $0 \pmod k$ is preserved across all stages, and each block $w^j$ contributes its uniform $T_{b^k}$-invariant orbit measure $\mu_w^{(k)} := \frac{1}{m} \sum_{j=0}^{m-1} \delta_{T_b^{kj} w^\infty}$. Hence the limiting $T_{b^k}$-invariant symbolic measure of the base-$b^k$ shifts is
```math
\rho = \nu_{mk} + b^{-mk}\left(\frac{1}{m}\sum_{j=0}^{m-1} \delta_{T_b^{kj} u^\infty} - \frac{1}{m}\sum_{j=0}^{m-1} \delta_{T_b^{kj} v^\infty}\right), \qquad \nu_{mk} := b^{-mk} \sum_{w \in \{0,\dots,b-1\}^{mk}} \frac{1}{m}\sum_{j=0}^{m-1} \delta_{T_b^{kj} w^\infty}.
```
Averaging $\rho$ across all $k$ base-$b$ phases $T_b^r$ ($0 \le r < k$) converts both orbit averages into the identical full base-$b$ orbit measure $\frac{1}{mk}\sum_{s=0}^{mk-1} \delta_{T_b^s u^\infty} = \frac{1}{mk}\sum_{s=0}^{mk-1} \delta_{T_b^s v^\infty}$, so the correction cancels identically and the base-$b$ word frequencies of $x$ equal those of $\nu_{mk}$; since $mk \ge L_1$, every length-$L_1$ base-$b$ word has limiting frequency $b^{-L_1}$, making $x$ $L_1$-normal in base $b$. Under $\rho$ (base $b^k$), however, the $m$-point orbit $\{T_b^{kj} u^\infty\}_{0 \le j < m}$ visits the base-$b^k$ digit $0^k$ at proportion $1/m$ (at $j = 0$) whereas $\{T_b^{kj} v^\infty\}_{0 \le j < m}$ visits $0^k$ at proportion $0$, so the frequency of the base-$b^k$ digit $0^k$ increases by $\frac{1}{m b^{mk}}$: $f_{0^k}(N; x, b^k) \to b^{-k} + \frac{1}{m b^{mk}} > b^{-k}$! $\square$

### 4.2 Simultaneous discrepancy ceilings, quantitative kernel exclusion, and spectra

**Theorem 4.2 (simultaneous discrepancy ceilings and quantitative kernel exclusion).** *Let $b \ge 2$, $k \ge 2$, $L_1 \ge 1$, $L_2 \ge 1$.*
1. *(Phase-stratified base-$b$ ceiling):* Every $x \in \mathbb{R}$ that is $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$ satisfies
```math
D^+(x; b) \le \min\left(\frac{2}{b^{L_1}},\ \frac{2(b^k - 1)}{k(b - 1)\, b^{k L_2}}\right).
```
   *Whenever $L_1 \le k(L_2 - 1) + 1$, the second term is strictly smaller than the single-radix ceiling $2 / b^{k(L_2 - 1) + 1}$ (e.g., $3/4 < 1$ for $(b, k, L_1, L_2) = (2, 2, 1, 1)$).*
2. *(Cross-radix base-$b^k$ coupling ceiling):* Every $x \in \mathbb{R}$ that is $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$ satisfies
```math
D^+(x; b^k) \le \min\left(\frac{2}{b^{k L_2}},\ \frac{2(k - 1)}{k\, b^{k L_2}} + \frac{2}{b^{L_1}}\right).
```
   *Whenever $b^{L_1 - k L_2} > k$, $L_1$-normality in base $b$ strictly lowers the base-$b^k$ discrepancy ceiling below $2 / b^{k L_2}$.*
3. *(Quantitative kernel exclusion from base-$b$ $L_1$-normality alone):* Every $x \in \mathbb{R}$ that is $L_1$-normal in base $b$ (with no normality assumption in base $b^k$) satisfies
```math
D^+(x; b^k) \le \min\left(1,\ 1 - \frac{1}{k} + \frac{2}{b^{L_1}}\right).
```
   *In particular, whenever $b^{L_1} > 2k$, every base-$b$ $L_1$-normal real is uniformly separated from $K_{b^k}$ with $1 - D^+(x; b^k) \ge \frac{1}{k} - \frac{2}{b^{L_1}} > 0$.*
4. *(Diagonal spectrum when $L_1 \ge k L_2$, and strictly exceeding $2 / b^{k L_2}$ when $L_1 < k L_2$):*
   - *When $L_1 \ge k L_2$, for every $t \in [0, 1]$ there exists an explicit real $x_t$ that is simultaneously $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$ with $D_\infty(x_t; b) = D_\infty(x_t; b^k) = \frac{2t}{b^{L_1}}$ (realizing the full base-$b$ ceiling $[0, 2/b^{L_1}]$).*
   - *When $L_1 < k L_2$, $D_\infty(x; b)$ **can strictly exceed** $2 / b^{k L_2}$: there exist explicit $1$-normal reals in base $9$ with exact discrepancy $D_\infty(x; 3) = \frac{11}{36} > \frac{2}{9}$ and $1$-normal reals in base $8$ with exact discrepancy $D_\infty(x; 2) = \frac{1865}{6132} > \frac{1}{4}$.*

*Proof.* (1) For any $M \ge 1$, split the $k M$ points $\{b^n x\}_{0 \le n < k M}$ into the $k$ phases $n = km + r$ ($0 \le r < k$). For each fixed $r$, the phase-$r$ empirical measure $\mu_{M}^{(r)}$ assigns to every base-$b$ length-$(k L_2 - r)$ cylinder a mass converging to $b^{-(k L_2 - r)}$ (by the proof of Theorem 4.1(1)). Rounding any interval $[u, v)$ outwards/inwards to the $b^{k L_2 - r}$-grid (as in `HigherOrderTower.radixDiscrepancy_le_grid_add`) gives $\limsup_{M \to \infty} D(\mu_M^{(r)}) \le \frac{2}{b^{k L_2 - r}}$. By the triangle inequality for $D$ on $\frac{1}{k}\sum_{r=0}^{k-1} \mu_M^{(r)}$ (and $O(k/N)$ boundary error between $N$ and $k \lfloor N/k \rfloor$),
```math
D^+(x; b) \le \frac{1}{k} \sum_{r=0}^{k-1} \frac{2}{b^{k L_2 - r}} = \frac{2 (b^k - 1)}{k(b - 1)\, b^{k L_2}}.
```
Combining with `HigherOrderTower.limsup_radixDiscrepancy_le_of_orderNormal` ($D^+(x; b) \le 2/b^{L_1}$) yields (1).

(2)–(3) Put $M_1 = b^{L_1}$ and $M_2 = b^{k L_2}$. Let $\mu_M^{(0)}$ be the empirical measure of $\{b^{km} x\}_{0 \le m < M}$ and $\bar{\mu}_{kM}$ the empirical measure of $\{b^n x\}_{0 \le n < kM}$; trivially $\mu_M^{(0)}(A) \le k\, \bar{\mu}_{kM}(A)$ for every Borel set $A \subseteq [0, 1)$.
- For (3): let $I = [u, v) \subseteq [0, 1)$ have length $\alpha \in [0, 1]$, and let $\widetilde{I}$ be its outward rounding to the $M_1$-grid, so $|\widetilde{I}| \le \alpha + 2/M_1$ and $\bar{\mu}_{kM}(\widetilde{I}) = |\widetilde{I}| + \eta_M$ with $\eta_M \to 0$ uniformly in $I$. Then $\mu_M^{(0)}(I) - \alpha \le \min\bigl(1 - \alpha,\ k(\alpha + 2/M_1 + \eta_M) - \alpha\bigr) = \min\bigl(1 - \alpha,\ (k - 1)\alpha + 2k/M_1 + k\eta_M\bigr)$. Optimizing over $\alpha \in [0, 1]$ (setting $1 - \alpha = (k-1)\alpha + 2k/M_1$ when $2k < M_1$) yields $\mu_M^{(0)}(I) - \alpha \le \min(1,\, 1 - \frac{1}{k} + \frac{2}{M_1}) + k\eta_M$. Applying the identical argument to the wrapping arc $I^c$ (whose outward $M_1$-rounding also adds at most $2/M_1$) gives $|I| - \mu_M^{(0)}(I) = \mu_M^{(0)}(I^c) - |I^c| \le \min(1,\, 1 - \frac{1}{k} + \frac{2}{M_1}) + k\eta_M$. Letting $M \to \infty$ proves (3).
- For (2): when $L_1 \le k L_2$, $\frac{2(k-1)}{k M_2} + \frac{2}{M_1} \ge \frac{2}{M_2}$, so the bound reduces to `HigherOrderTower.limsup_radixDiscrepancy_le_of_orderNormal` in base $b^k$. Assume $L_1 > k L_2$, so every $M_2$-grid endpoint is also an $M_1$-grid endpoint. Decompose any interval $I = [u, v)$ as $I = I_{\text{full}} \sqcup J_1 \sqcup J_2$, where $I_{\text{full}}$ is a union of complete $M_2$-cells and $J_1, J_2$ are subintervals of at most two boundary $M_2$-cells $C_1, C_2$. On $I_{\text{full}}$, $|\mu_M^{(0)}(I_{\text{full}}) - |I_{\text{full}}|| \le \varepsilon_M \to 0$ uniformly. If $I$ meets at least two $M_2$-cells, each $J_i$ has one endpoint on the $M_2$-grid (hence on the $M_1$-grid), so its outward $M_1$-rounding $\widetilde{J}_i$ has $|\widetilde{J}_i| \le |J_i| + 1/M_1$. Writing $\alpha_i = |J_i| \in [0, 1/M_2]$, we obtain
```math
\mu_M^{(0)}(J_i) - \alpha_i \le \min\left(\frac{1}{M_2} - \alpha_i + \varepsilon_M,\ (k - 1)\alpha_i + \frac{k}{M_1} + k\eta_M\right) \le \frac{k - 1}{k M_2} + \frac{1}{M_1} + \varepsilon_M + k\eta_M.
```
  Summing over $i = 1, 2$ gives $\mu_M^{(0)}(I) - |I| \le \frac{2(k-1)}{k M_2} + \frac{2}{M_1} + o(1)$. If $I$ lies inside a single $M_2$-cell, $|\widetilde{I}| \le |I| + 2/M_1$ yields $\mu_M^{(0)}(I) - |I| \le \frac{k-1}{k M_2} + \frac{2}{M_1} + o(1) \le \frac{2(k-1)}{k M_2} + \frac{2}{M_1} + o(1)$. Applying the same argument to the complement $I^c$ (whose boundary pieces inside $M_2$-cells are again at most two half-aligned subintervals) and letting $M \to \infty$ proves (2).

(4) Put $M = b^{L_1}$. For $L_1 \ge k L_2$, handle the two endpoints explicitly: at $t = 0$, take any base-$b$ normal number $x_0$ (also normal in base $b^k$ by Maxfield's theorem, giving $D_\infty(x_0; b) = D_\infty(x_0; b^k) = 0$); at $t = 1$, use the periodic blocks $w^{k j}$ alone ($j = 1, 2, \dots$, over all $w \in \{0, \dots, b - 1\}^{L_1}$). For $t \in (0, 1)$, fix a single base-$b$ normal digit stream consumed continuously across stages; at stage $j = 1, 2, \dots$, concatenate $w^{k j}$ (length $k j L_1$, a multiple of $k$) for every $w \in \{0, \dots, b - 1\}^{L_1}$ (total periodic length $k j M L_1$), followed by the next $k \lfloor j M L_1 (1 - t)/t \rfloor$ digits of the fixed normal stream (also a multiple of $k$). The periodic length is $k j M L_1$ and the normal length is $k j M L_1 (1 - t)/t + O(k)$, so the periodic and normal proportions in stage $j$ are $t + O(1/j)$ and $(1 - t) + O(1/j)$, respectively; an incomplete stage has length $O(j)$ against cumulative length $\Theta(j^2)$, contributing $O(1/j) \to 0$. At every aligned offset $r \pmod{L_1}$ (including when $\gcd(k, L_1) > 1$), cyclic rotation permutes $\{0, \dots, b - 1\}^{L_1}$ bijectively, so the aligned base-$b^k$ symbolic law is the exact same $t$-periodic / $(1 - t)$-uniform mixture as in base $b$ (and the single continuous normal stream is normal in base $b^k$ by Maxfield's theorem). Since $k L_2 \le L_1$, $x_t$ is simultaneously $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$, and the grid argument of Phase 23 `GF-29` §5 yields $D_\infty(x_t; b) = D_\infty(x_t; b^k) = \frac{2t}{M} = \frac{2t}{b^{L_1}}$.

For $L_1 < k L_2$, explicit finite mixtures of $T_{b^k}$-periodic orbits exceed $2/b^{k L_2}$. Concatenating increasingly long aligned periodic pieces (lengths divisible by $k$) in the prescribed proportions yields a single explicit real $x$ whose base-$b^k$ orbit measure converges to the target mixture and whose base-$b$ orbit measure converges to the phase-averaged measure $\bar{\mu}$ (obtained by expanding every atom across all $k$ phases $\{y, T_b y, \dots, T_b^{k-1} y\}$ with multiplicities retained): at each fixed grid depth, discarding the bounded number of starts per join, passing to the limit on finite grids, and sending the mesh to zero (via two-cell rounding error) transfers the exact full-multiset discrepancy $D(\bar{\mu}) = \frac{1}{n} + \max_i z_i - \min_i z_i$ (where $y_0 \le \dots \le y_{n-1}$ are the $n$ equally weighted phase points and $z_i = y_i - i/n$) to $D_\infty(x; b) = D(\bar{\mu})$. Exact full-multiset checks via `disc_multiset` in [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py) certify:
- $(b, k, L_2) = (3, 2, 1)$ ($2/M_2 = 2/9 = 8/36$): mix the seven $T_9$-orbits $0^\infty$ (base-$9$ orbit at $0$), $\{1/8\}$, $\{3/8\}$, $\{1/2\}$, $\{5/8\}$, $\{7/8\}$ (weight $1/9$ each) and $\{30/91, 88/91, 64/91\}$ (weight $1/3$). Each of the nine base-$9$ cells $[j/9, (j+1)/9)$ receives exact mass $1/9$ ($1$-normal in base $9$). Expanding across both base-$3$ phases yields $18$ equally weighted points (weight $1/18$ each), with $\min_i z_i = -7/72$ at $i = 4, y_4 = 1/8$ and $\max_i z_i = 11/72$ at $i = 13, y_{13} = 7/8$, giving the exact discrepancy $D_\infty(x; 3) = \frac{1}{18} + \frac{11}{72} - (-\frac{7}{72}) = \frac{11}{36} > \frac{2}{9}$ (and $\le \frac{4}{9}$, the phase-stratified ceiling).
- $(b, k, L_2) = (2, 3, 1)$ ($2/M_2 = 1/4 = 1533/6132$): mix the three $T_8$-orbits $\{1/3, 2/3\}$ (weight $1/4$), $\{51/511, 408/511, 198/511\}$ (weight $3/8$), and $\{103/511, 313/511, 460/511\}$ (weight $3/8$). Every base-$8$ cell receives exact mass $1/8$ ($1$-normal in base $8$). Expanding across all three base-$2$ phases yields $24$ equally weighted points (weight $1/24$ each), with $\min_i z_i = -677/6132$ at $i = 22, y_{22} = 412/511$ and $\max_i z_i = 1865/12264$ at $i = 1, y_1 = 99/511$, giving the exact discrepancy $D_\infty(x; 2) = \frac{1}{24} + \frac{1865}{12264} - (-\frac{677}{6132}) = \frac{1865}{6132} > \frac{1}{4}$ (and $\le \frac{7}{12}$, the phase-stratified ceiling). $\square$

### 4.3 Kernel intersection law and multi-power tower existence (with parity obstruction)

**Theorem 4.3 (kernel intersection law and simultaneous tower existence).** *Fix $b \ge 2$.*
1. *(Kernel intersection law):* For all $k_1, k_2 \ge 1$,
```math
K_{b^{k_1}} \cap K_{b^{k_2}} = K_{b^{\gcd(k_1, k_2)}}.
```
   *Consequently, for $L \ge 1$, $(K_{b^{k_1}} \cap K_{b^{k_2}}) \setminus K_b$ contains a base-$b$ $L$-normal real (and an exact-order-$L$ irrational) if and only if $b^L \mid \gcd(k_1, k_2)$.*
2. *(Simultaneous $(L_1, L_2)$ existence in $K_{b^m}$):* Let $k \ge 2$, $L_1, L_2 \ge 1$, and $m \ge 2$ with $k \mid m$.
   - *Necessary condition:* If $K_{b^m}$ contains a real $x$ that is simultaneously $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$, then $\operatorname{lcm}\bigl(b^{L_1},\ k b^{k L_2}\bigr) \mid m$ (and $x \notin K_b \cup K_{b^k}$).
   - *Sufficient condition:* Whenever $k\, b^{\max(L_1,\, k L_2)} \mid m$, there exists an explicit irrational $x \in K_{b^m} \setminus (K_b \cup K_{b^k})$ that is simultaneously $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$. In particular, when $L_1 \le k L_2$ OR $\gcd(k, b) = 1$, necessity and sufficiency **coincide**: $\operatorname{lcm}(b^{L_1}, k b^{k L_2}) = k b^{\max(L_1, k L_2)}$.
   - *Genuine parity obstruction when $L_1 > k L_2$ and $\gcd(k, b) > 1$:* For $(b, k, L_1, L_2) = (2, 2, 3, 1)$, the necessary divisibility condition $\operatorname{lcm}(2^3, 2 \cdot 2^2) = 8 \mid m$ is satisfied at $m = 8$, yet **no element of $K_{2^8}$** is simultaneously $3$-normal in base $2$ and $1$-normal in base $4$; the least admissible level is $m = 16$.

*Proof.* (1) Put $g = \gcd(k_1, k_2)$ and $L = \operatorname{lcm}(k_1, k_2)$. Since $g \mid k_i$, $F_{b^g} \subseteq F_{b^{k_i}}$ and $M_{b^g} = M_b = M_{b^{k_i}}$, giving $K_{b^g} \subseteq K_{b^{k_1}} \cap K_{b^{k_2}}$. Conversely, if $x \in K_{b^{k_1}} \cap K_{b^{k_2}}$, then by `HigherOrderTower.kernel_eq_fixedPoint_add_zeroOrbit`, $x = \frac{m_1}{b^{k_1}-1} + u_1 = \frac{m_2}{b^{k_2}-1} + u_2$ with $m_i \in \mathbb{Z}$ and $u_i \in M_b$. Subtracting places $\frac{m_1}{b^{k_1}-1} - \frac{m_2}{b^{k_2}-1} = u_2 - u_1 \in F_{b^L} \cap M_b = \mathbb{Z}$ (`RadixPowerTower.fixedPoint_inter_zeroOrbit`). Thus the reduced denominator $q$ of $\frac{m_1}{b^{k_1}-1}$ divides both $b^{k_1} - 1$ and $b^{k_2} - 1$, hence divides $\gcd(b^{k_1} - 1, b^{k_2} - 1) = b^g - 1$, so $x \in F_{b^g} + M_b = K_{b^g}$. For the corollary: in the degenerate case $g = \gcd(k_1, k_2) = 1$, $(K_{b^{k_1}} \cap K_{b^{k_2}}) \setminus K_b = K_b \setminus K_b = \emptyset$ directly, matching $b^L \nmid 1$; for $g \ge 2$, applying `HigherOrderTower.tower_iff` and `tower_irrational_exact_iff` at level $g$ gives the equivalence.

(2) *Necessity:* Since $b^k \ge 4 > 2$, $K_{b^k}$ contains no $1$-normal real in base $b^k$ (`HigherOrderTower.all_kernel_pow_iff`), so $x \notin K_{b^k}$ (and hence $x \notin K_b$). In particular, the degenerate case $m = k$ is impossible immediately, so $m / k \ge 2$ (and $m \ge 2k \ge 4$). By `HigherOrderTower.mem_pow_kernel_decomp`, $x = r / (b^m - 1) + u$ with $u \in M_b$, and the exclusion $x \notin K_{b^k}$ (hence $x \notin K_b$) supplies the nonzero rational-part hypothesis ($x$ is not an integer-shifted fixed point of $T_b$ or $T_{b^k}$) required by `HigherOrderTower.wordFreq_tower_limit` in both bases $b$ and $b^k$. Hence the base-$b$ word frequencies of $x$ are rational with cyclic denominator $m$ (forcing $b^{L_1} \mid m$) and its base-$b^k$ word frequencies are rational with cyclic denominator $m / k$ (forcing $b^{k L_2} \mid (m / k)$, i.e. $k b^{k L_2} \mid m$).

*Sufficiency:* Put $L_* := \max(L_1, k L_2)$ and form the **phased de Bruijn directed graph** $G_{\text{phased}}(b, k, L_*)$ with vertex set $\{0, \dots, b - 1\}^{L_* - 1} \times (\mathbb{Z}/k\mathbb{Z})$ (just $\mathbb{Z}/k\mathbb{Z}$ when $L_* = 1$) and directed edges $(v, r) \xrightarrow{d} (\text{suffix}_{L_*-1}(vd),\ (r + 1) \bmod k)$ for every digit $d \in \{0, \dots, b - 1\}$. Every vertex has in-degree $b$ and out-degree $b$, and the graph is strongly connected: from $(v, r)$ to $(v', r')$, pick any $s \ge L_* - 1$ with $s \equiv r' - r \pmod k$ and append $0^{s - (L_* - 1)} v'$. By Hierholzer's theorem, $G_{\text{phased}}(b, k, L_*)$ admits a closed Euler circuit $W$ of length $k b^{L_*}$ in which, at **every** fixed phase $r \in \mathbb{Z}/k\mathbb{Z}$, every length-$L_*$ base-$b$ word occurs **exactly once**. Repeating $W$ exactly $m / (k b^{L_*})$ times gives $c = r / (b^m - 1)$ that is $L_*$-normal in base $b$ (hence $L_1$-normal) and, restricting to phase $r = 0$, $L_2$-normal in base $b^k$ (since $k L_2 \le L_*$). Adding any irrational $u \in M_b$ preserves all word frequencies (`wordFreq_tower_limit`).

*Obstruction at $(2, 2, 3, 1, m = 8)$:* Any $x \in K_{2^8}$ that is $1$-normal in base $4$ has base-$4$ block of length $4$ that must be a cyclic permutation of the four base-$4$ digits $\{00, 01, 10, 11\}$. Up to cyclic rotation there are $3! = 6$ such blocks (`00 01 10 11`, `00 01 11 10`, `00 10 01 11`, `00 10 11 01`, `00 11 01 10`, `00 11 10 01`), and direct inspection (certified in [`scripts/phase24_word_laws.py`](../../scripts/phase24_word_laws.py)) shows none contains all eight binary $3$-words! Thus no element of $K_{2^8}$ is simultaneously $3$-normal in base $2$ and $1$-normal in base $4$, whereas $G_{\text{phased}}(2, 2, 3)$ gives an explicit witness at $m = 16$. $\square$

### 4.4 Translation by $M_b$ and $K_{b^k}$, and universal disjunctivity in the tower

**Theorem 4.4 (translation stability vs boundary-flipping instability under $M_b$ and $K_{b^k}$).** *Let $b \ge 2$, $k \ge 2$, $L \ge 1$.*
1. *(Discrepancy invariance and full normality):* For every $x \in \mathbb{R}$, every $u \in M_b$, and every $m \ge 1$, $D^\pm(x + u; b^m) = D^\pm(x; b^m)$. For every $z \in K_{b^k}$, $D^\pm(x + z; b^k) = D^\pm(x; b^k)$; in particular, by Sharp Translation (`GF-05`) and Maxfield's theorem, translation by any $z \in K_{b^k}$ preserves **full normality** in base $b$.
2. *(Conditional $L$-normality stability under $M_b$):* If $x$ is $L$-normal in base $b^m$ and has no boundary concentration on $b^{-m L}\mathbb{Z}$ (i.e., $\lim_{\varepsilon \downarrow 0} \limsup_N \frac{1}{N} \#\{n < N : \operatorname{dist}(b^{mn} x, b^{-m L} \mathbb{Z}) < \varepsilon\} = 0$), then $x + u$ is $L$-normal in base $b^m$ for every $u \in M_b$.
3. *(Boundary-flipping instability of finite-order normality under $M_b$):* Without the no-boundary-concentration hypothesis, **$M_b$ does NOT preserve $L$-normality**: for every $b \ge 2$ and $L \ge 1$, there exist an $L$-normal real $x$ (with $D_\infty(x; b) = 2/b^L$) and $u \in M_b$ such that $f_{0^L}(N; x + u, b) \to 0$, $f_{(b-1)^L}(N; x + u, b) \to 2/b^L$, and for single digits $f_0(N; x + u, b) \to \frac{1}{b} - b^{-L}$ and $f_{b-1}(N; x + u, b) \to \frac{1}{b} + b^{-L}$ (so $x + u$ is not even $1$-normal for any $L \ge 1$!).
4. *(Non-invariance of base-$b$ finite-order normality under $K_{b^k} \setminus K_b$):* Whenever $b^L \mid k$, taking $z \in K_{b^k} \setminus K_b$ that is $L$-normal in base $b$ shows that translation by $z$ maps the non-normal $0 \in K_b$ to $L$-normal $z$, while translation by $-z$ maps $L$-normal $z$ to $0$.

*Proof.* (1) Immediate from Sharp Translation (`GF-05`, $|D_N(x + y; B) - D_N(x; B)| \le 1 - D_N(y; B)$) and $M_b = M_{b^m} \subseteq K_{b^m}$, plus Maxfield's equivalence of full normality in bases $b$ and $b^k$.

(2) For any $\varepsilon > 0$, outside the $\varepsilon$-neighborhood of $b^{-m L}\mathbb{Z}$ (which has upper density $\delta(\varepsilon) \to 0$) and the shifts where $\|b^{mn} u\| \ge \varepsilon$ (which have density $0$ by Markov's inequality, `HigherOrderTower.farCount_div_tendsto_zero_of_mem_zeroOrbit`), $T_{b^m}^n(x + u)$ and $T_{b^m}^n x$ lie in the exact same length-$L$ base-$b^m$ cylinder. Letting $N \to \infty$ and then $\varepsilon \downarrow 0$ yields identical word frequencies.

(3) Take the exact $t = 1$ stage construction $x$ of Phase 23 `GF-29` §5: at stage $j = 1, 2, \dots$, append $w^j$ (length $L j$) for each $w \in \{0, \dots, b - 1\}^L$ in lexicographic order. Then $x$ is $L$-normal in base $b$ along all $N$ (with $D_\infty(x; b) = 2/b^L$), cumulative length through stage $j$ is $N_j = \frac{1}{2} b^L L j(j + 1) \asymp j^2$, and the stage-$j$ $0$-run $[A_j, A_j + L j)$ has length $L j \asymp A_j^{1/2}$. Now set $n_s := \lfloor s^{4/3} \rfloor$ for $s \ge 2$ and define $u := -\sum_{s \ge 2} b^{-n_s}$. For $s \ge 2$, $(s + 1)^{4/3} - s^{4/3} > \frac{4}{3} \cdot 2^{1/3} > 1$, so $(n_s)$ is strictly increasing with $\#\{s \ge 2 : n_s \le N\} \le (N + 1)^{3/4} = o(N)$, whence $u \in M_b$; moreover, $n_{s+1} - n_s = (\frac{4}{3} + o(1)) n_s^{1/4}$. Throughout any stage-$j$ run $[A_j, A_j + L j)$, we have $n / A_j = 1 + O(1/j)$, so for all sufficiently large $j$ and every $n \in [A_j, A_j + L j)$ with $n_s \le n < n_{s+1}$, $n_{s+1} - n \le n_{s+1} - n_s \le 2 A_j^{1/4}$. Excluding the $O_L(N^{3/4}) = o(N)$ shifts within distance $L + 1$ of $\{n_s\}$ and trimming the last $\lceil 3 A_j^{1/4} \rceil$ starts of each stage-$j$ constant run (total cost $\sum_{A_j \le N} O(A_j^{1/4}) = O_{b,L}(N^{3/4}) = o(N)$):
- on every remaining stage-$j$ $0$-run shift $n \in [A_j, A_j + L j - 3 A_j^{1/4})$, $0 < T_b^n x < b^{-(A_j + L j - n)} \le b^{-3 A_j^{1/4}}$, while $b^n u \equiv -\beta_n \pmod 1$ with $b^{-2 A_j^{1/4}} \le b^{-(n_{s+1} - n)} < \beta_n < b^{-L - 1}$.

Hence $0 < T_b^n x < \beta_n < b^{-L - 1}$, so $T_b^n(x + u) = \{T_b^n x - \beta_n\} = 1 - (\beta_n - T_b^n x) \in (1 - b^{-L - 1}, 1) \subset (1 - b^{-L}, 1)$ (crossing the seam from $0^L$ into $(b-1)^L$). On every remaining $(b-1)$-run shift, $T_b^n x \in (1 - b^{-3 A_j^{1/4}}, 1)$ and $0 < \beta_n < b^{-L - 1}$ keep $T_b^n(x + u) = T_b^n x - \beta_n \in (1 - b^{-L}, 1)$ on its side of the seam. Finally, every periodic orbit $w^\infty$ other than the two extreme constant strings $0^L$ and $(b-1)^L$ — including constant interior-digit words $d^L$ ($1 \le d \le b - 2$) — stays at a fixed positive distance $\ge ((b^L - 1) b^L)^{-1}$ from $b^{-L}\mathbb{Z}$, so its length-$L$ word frequencies (and leading-digit frequencies) are unaffected by $u \in M_b$. Therefore $f_{0^L}(N; x + u, b) \to 0$ and $f_{(b-1)^L}(N; x + u, b) \to 2/b^L$ along all $N$. Moreover, for single digits (including $L > 1$), the exact same mass $b^{-L}$ transfers from digit $0$ to digit $b - 1$ while all other contributions remain unchanged, giving $f_0(N; x + u, b) \to \frac{1}{b} - b^{-L}$ and $f_{b-1}(N; x + u, b) \to \frac{1}{b} + b^{-L}$, so $x + u$ fails $1$-normality.

(4) Immediate from `HigherOrderTower.tower_iff`. $\square$

**Theorem 4.5 (complete independence of disjunctivity in the multi-radix tower).** *For every $b \ge 2$, $k \ge 2$, $L \ge 1$ with $b^L \mid k$, and every fixed-level exact-order-$L$ discrepancy value $\alpha \in \mathcal{S}_{b, L, k}^{\text{exact}}$ (Phase 23 `GF-29`, eq. (9)), there exist:*
1. *an explicit irrational $x \in K_{b^k} \setminus K_b$ of exact base-$b$ normality order $L$ with $D_\infty(x; b) = \alpha$ that is **universally power-disjunctive** (simultaneously disjunctive in every base $b^m$, $m \ge 1$);*
2. *an explicit irrational $x' \in K_{b^k} \setminus K_b$ of exact base-$b$ normality order $L$ with $D_\infty(x'; b) = \alpha$ that is **not disjunctive** in base $b$.*

*Proof.* Let $c = r / (b^k - 1)$ ($0 < r < b^k - 1$) be a rational witness realizing $\alpha \in \mathcal{S}_{b, L, k}^{\text{exact}}$.

(1) Form a **recurrent** enumeration $w_1, w_2, \dots$ of all finite nonempty base-$b$ words by concatenating, for $h = 1, 2, \dots$, the lexicographic list of all base-$b$ words of lengths $1, \dots, h$. Then every finite nonempty base-$b$ word occurs **infinitely often** in $(w_j)$, and since the $h$-th block has $\sum_{\ell=1}^h b^\ell \ge b^h$ words, any $w_j$ in block $h \ge 2$ satisfies $j \ge b^{h-1}$ and hence $\ell_j := |w_j| \le h \le \lfloor \log_b j \rfloor + 2 = O(\log j)$. Write $W_j \in \{0, \dots, b^{\ell_j} - 1\}$ for the base-$b$ integer value of $w_j$. Choose rapidly growing positions $N_j$ divisible by $j!$ (for example $N_j = j! \cdot b^{j^2}$), so $N_{j+1} - (N_j + \ell_j) \to \infty$ faster than any polynomial, $N_s + \ell_s \le N_j$ for all $s < j$ once $j$ is sufficiently large, and $N_j \equiv 0 \pmod m$ for all $j \ge m$. For each $j \ge 1$, let $C_j := \lfloor b^{\ell_j} \{b^{N_j} c\} \rfloor$ be the length-$\ell_j$ word of $c$ starting at shift $N_j$, put $v_j := (W_j - C_j) \bmod b^{\ell_j} \in \{0, \dots, b^{\ell_j} - 1\}$, and define
```math
u_{\text{disj}} := \sum_{j \ge 1} v_j\, b^{-(N_j + \ell_j)}.
```
For any fixed $J \ge 1$, the shifts $n < N$ with $\|b^n u_{\text{disj}}\| \ge b^{-J}$ must lie within $J$ of some block $[N_j, N_j + \ell_j)$, numbering $O_J(\sqrt{\log N} \log\log N) = o(N)$, so $u_{\text{disj}} \in M_b$. Hence $x := c + u_{\text{disj}} \in K_{b^k} \setminus K_b$ has exact base-$b$ normality order $L$ (`wordFreq_tower_limit`) and $D_\infty(x; b) = D_\infty(c; b) = \alpha$ (Sharp Translation). At every sufficiently large $j$ (so that $N_s + \ell_s \le N_j$ for all $s < j$):
```math
b^{N_j + \ell_j} x = I_j + (C_j + v_j) + \{b^{N_j + \ell_j} c\} + \sum_{s > j} v_s b^{N_j + \ell_j - N_s - \ell_s},
```
where $I_j := \lfloor b^{N_j} c \rfloor b^{\ell_j} + \sum_{s < j} v_s b^{N_j + \ell_j - N_s - \ell_s}$ is an integer **divisible by $b^{\ell_j}$** (since $N_j - (N_s + \ell_s) \ge 0$ for every $s < j$), $\{b^{N_j + \ell_j} c\} \le 1 - \frac{1}{b^k - 1}$ (as $0 < r < b^k - 1$ is purely periodic), and the $s > j$ tail is strictly positive and $< \frac{1}{b^k - 1}$. Hence the fractional tail lies strictly in $(0, 1)$, so no carry enters position $N_j + \ell_j$, and reducing $\lfloor b^{N_j + \ell_j} x \rfloor = I_j + C_j + v_j$ modulo $b^{\ell_j}$ (using $b^{\ell_j} \mid I_j$) gives $(C_j + v_j) \bmod b^{\ell_j} = W_j$, i.e. the digits of $x$ at shifts $N_j + 1, \dots, N_j + \ell_j$ are exactly $w_j$! Because every base-$b^m$ word $W$ of length $r$ is a base-$b$ word of length $m r$ occurring infinitely often among $\{w_j\}$, it occurs at some $j \ge m$ (hence $m \mid N_j$), so $W$ occurs in the base-$b^m$ expansion of $x$ at shift $N_j / m$. Thus $x$ is simultaneously disjunctive in every base $b^m$ ($m \ge 1$), and in particular irrational.

(2) Take $u = \sum_{j \ge 1} b^{-2^j} \in M_b$ (`sparseQuadPerturb` style; irrational since $c + u$ is not eventually periodic). Because $0 < r < b^k - 1$, the $k$-periodic expansion of $c$ cannot equal $(b-1)^\infty$, so it contains at least one digit $< b - 1$ in every period of length $k$ and therefore has no run of $k$ consecutive maximal digits $b - 1$. Consequently, an isolated $+1$ increment at position $2^j$ propagates carries to the left by at most $k$ places (affecting only the carry neighborhood $[2^j - k, 2^j]$). Because $2^{j+1} - 2^j = 2^j \to \infty$, these carry neighborhoods are eventually pairwise disjoint, and for any fixed $L_0 > k$ and all sufficiently large shifts $n$, at most one perturbation affects $[n + 1, n + L_0]$, yielding at most $k(L_0 + k + 2)$ distinct base-$b$ words of length $L_0$ that occur infinitely often in $x' = c + u$. Choosing $L_0$ with $k(L_0 + k + 2) < b^{L_0}$ produces a base-$b$ word $w_0$ of length $L_0$ with only finitely many occurrences in $x'$; taking a sufficiently long extension starting with $w_0$ then gives a base-$b$ word that never occurs in $x'$ at all, ruling out disjunctivity. $\square$

---

## 5. Uncompiled Lean 4 algebraic core blueprint for `Phase24Cores.lean`

> **Evidence status:** Uncompiled blueprint containing `sorry` placeholders. This section outlines candidate declarations for a future `NormalityChecker/Phase24Cores.lean` (extending `Phase23Cores.lean` and `HigherOrderTower.lean`) and **supplies no new kernel verification**.

```lean
namespace NormalityChecker.Phase24Cores

/-- Sub-track B2: binary-to-base-m support map `u_m(i)`. -/
def binToBaseM (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (i + 1) % 2 + m * binToBaseM m ((i + 1) / 2)

/-- Exact support-gap identity (Theorem 1.1):
`(m - 1) * (u_m (i + 1) - u_m i) = (m - 2) * m ^ (padicValNat 2 (i + 1)) + 1`. -/
theorem binToBaseM_gap {m : ℕ} (hm : 2 ≤ m) (i : ℕ) :
    (m - 1) * (binToBaseM m (i + 1) - binToBaseM m i) =
      (m - 2) * m ^ (padicValNat 2 (i + 1)) + 1 := by sorry

/-- Exact Thue-Morse signed even-gap sum identity (Theorem 1.5(1)):
for `m ≥ 3` and `k ≥ 2`, all `1 ≤ r ≤ k - 2` layers cancel identically. -/
theorem thueMorse_signed_even_gap_sum {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k) :
    ∑ j ∈ Finset.Icc 1 (2 ^ (k - 1)),
      ((-1 : ℤ) ^ (Nat.popcount (2 * j))) *
        ((binToBaseM m (2 * j) - binToBaseM m (2 * j - 1) : ℕ) : ℤ) =
      -(((m - 2) * (m ^ k + m ^ (k - 1)) + 2 : ℕ) / (m - 1) : ℤ) := by sorry

/-- Sub-track B1: exact prime-by-prime Selberg sieve switch inequality (Lemma 2.2). -/
theorem selberg_prime_switch_ineq {A B α β : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) (hβ : 0 ≤ β) (hβα : β ≤ α) :
    (A + α * B) * (1 + β) ≤ (A + β * B) * (1 + α) := by nlinarith

/-- Sub-track B1: exact local Euler-factor collapse (Theorem 2.3). -/
theorem eulerSq_local_factor_identity {p : ℚ} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hp2 : p ≠ 2) (hpm1 : p ≠ -1) (hp4 : p ^ 4 - 1 ≠ 0) :
    (1 - 1 / (p - 1) ^ 2) * (1 - 1 / p ^ 2) ^ 2 * (p ^ 4 / (p ^ 4 - 1)) *
      (1 + 1 / (p * (p - 2)) + 2 * (p - 1) / ((p ^ 2 - 1) * (p - 2))) =
      1 + 2 / ((p - 1) * (p ^ 2 + 1)) := by sorry

/-- Sub-track B1: exact weighted average sum inequality `2 * D * ∑ (H - D * m) ≤ H ^ 2`. -/
theorem weighted_linear_sum_le (H D K : ℕ) :
    2 * D * (K * H) ≤ H ^ 2 + D ^ 2 * K * (K + 1) := by sorry

/-- Sub-track B3: universal odd-order modulus `d = b^2 + b + 1` has `b^3 ≡ 1 (mod d)` and odd `d`. -/
theorem b2_add_b_add_one_odd_and_order (b : ℕ) :
    Odd (b ^ 2 + b + 1) ∧ (b ^ 2 + b + 1) ∣ (b ^ 3 - 1) := by sorry

/-- Sub-track B4: kernel intersection law `K_{b^{k1}} ∩ K_{b^{k2}} = K_{b^{gcd k1 k2}}`
(building directly on `HigherOrderTower.kernel_eq_fixedPoint_add_zeroOrbit`). -/
theorem kernel_pow_inter_eq_gcd {b k₁ k₂ : ℕ} (hb : 2 ≤ b) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    HigherOrderTower.Kernel (b ^ k₁) ∩ HigherOrderTower.Kernel (b ^ k₂) =
      HigherOrderTower.Kernel (b ^ (Nat.gcd k₁ k₂)) := by sorry

/-- Sub-track B4: cross-radix order implication (Theorem 4.1(1)). -/
theorem orderNormal_of_pow_orderNormal {b k L₂ : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) (hL₂ : 1 ≤ L₂)
    {x : ℝ} (hx : HigherOrderTower.OrderNormal (b ^ k) L₂ x) :
    HigherOrderTower.OrderNormal b (k * (L₂ - 1) + 1) x := by sorry

end NormalityChecker.Phase24Cores
```

---

## 6. Verification summary

Running `python -B scripts/phase24_word_laws.py` executes **50,283 exact `int`/`Fraction` checks (0 floating-point checks)** across all four sub-tracks with standard-library code only and exits with status `0`:
- **B2:** support-gap identity ($m \in \{3, 4, 5, 6, 10\}$, $i \le 512$), exact signed even-gap sums $\Delta(k)$ ($k \le 8$), rational tail majorant bounds, exact certified digit prefixes for 15 pairs $(b, m)$ over $81 \le N = m^k \le 1000$, exact binary counts $C_1(m^k)$, exact finite-prefix lower crossing $C_1(u_{2^k - 1}) = m^{k-1} - 1$ and finite upper bound $C_{b-1}(N) \le (1 - \frac{1}{m(m-1)})N$ at every prefix $1 \le N \le m^k$, forbidden words (`0101`/`1010` and $\{1,\dots,b-2\}^2$), bounds on words other than $0^L, (b-1)^L$ ($L \in \{2, 3\}$), and exact self-similar function $F_m(t)/t$ checks on depth-$4$ $m$-adic grids, Cantor minimizers $t_r$, and periodic-orbit cycles ($F_3(1/8) = 23/240$). (Separate finite extrema measurements up to $N = 1024$ are printed for illustration only.)
- **B1:** exact theta-difference identity $a_2(n) = \frac{1}{2}(r_{x^2+36y^2}(12n+1) - r_{4x^2+9y^2}(12n+1))$, $r_2(12n+1)/4$ sum and $n \in U$ equality criterion ($0 \le n \le 3{,}000$), local Euler-factor collapse ($p \le 500$), full-$G_0(\xi)$ instances of Lemma 2.2 using all primes $p \in \mathcal{P}_0$ below $\xi \in \{40, 100, 250\}$, weighted-sum inequality, and zero-float exact rational certificates for $\pi < 3.141593 < 3.1416$, $2\pi < (25067/10000)^2$, $\Gamma(1/4) < 3.625626 < 3.6257$, $\mathcal{E}_0 < 1.028980$, $K_* < 3.178808$, and $8 K_* < 25.4305 < 25.431 < 26$ ($\kappa > 1/26$).
- **B3:** base-$2$ complement identity ($d < 50$), $d = 1$ trivial-modulus check, universal family $\frac{1}{b^2+b+1} E_b$ ($2 \le b \le 12$), primitive-root edge cases $(3, 5)$ and $(6, 11)$ (both $a = \pm 1$), balanced $b$-exceptional primes $(4, 29)$ (both cosets $a = 1, 2$), $(6, 59)$, $(6, 1613)$, $(10, 113)$ and their arithmetic-progression base shifts, and exact verification of zero $2$-exceptional primes among all 2,989 even-order primes $p \le 40{,}000$.
- **B4:** Gray-code and Markov-chain sharpness formulas, reverse non-implication orbit-average check, exact full-multiset periodic-orbit witnesses via `disc_multiset` attaining $D_\infty(x; 3) = 11/36 > 2/9$ (18 phase points) and $D_\infty(x; 2) = 1865/6132 > 1/4$ (24 phase points), exhaustive proof of the parity obstruction at $(2, 2, 3, 1)$ in $K_{2^8}$, phased de Bruijn Euler circuits via Hierholzer's algorithm, $\gcd(b^{k_1}-1, b^{k_2}-1) = b^{\gcd(k_1, k_2)} - 1$, and exact carry-free word-planting checks for universal power-disjunctivity.
