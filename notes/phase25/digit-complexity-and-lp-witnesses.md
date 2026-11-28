# Digit complexity, middle-interval orbit formulas and optimal discrepancy witnesses

Phase 25, Track D (D1–D4). Companion script: [`scripts/phase25_digit_complexity.py`](../../scripts/phase25_digit_complexity.py) (pure Python, exact integer and `fractions.Fraction` arithmetic, every printed bound rounded outward with the rounding direction itself checked; 844 checks, exit code 0). This note continues the Phase 24 notes [classical-constants-and-joint-numerators.md](../phase24/classical-constants-and-joint-numerators.md) §3 (`GF-40`, cited as *P24-E*), [dense-digit-mass-and-lambert.md](../phase24/dense-digit-mass-and-lambert.md) §§2, 7–8 (`GF-36`, cited as *P24-A*) and [simple-normality-and-word-laws.md](../phase24/simple-normality-and-word-laws.md) §4 (`GF-37`, cited as *P24-B*), and Phase 23 [binary-partition-and-carry-complexity.md](../phase23/binary-partition-and-carry-complexity.md) §5 (`GF-32`, cited as *P23-B3*).

**Evidence labels** (repository conventions, [`docs/research-objectives.md`](../../docs/research-objectives.md)): *Paper proof* (complete written proof here); *Finite certificate* (exact integer/rational computation in the companion script); *External input* (published theorem cited without proof); *Repository input* (a result proved and registered in an earlier phase, used without re-proof; its own label is stated); *Conditional*; *Finite measurement* (finite digit statistics, bearing on no limit); *Numerical* (floating-point, not a certificate); *Open*. Cross-model review is not independent human peer review.

**Scope statement.** Nothing here changes the status of any constant in the fixed 50-constant roster (`BC-01`…`BC-50`). The nonnormality results concern $E_+(2^k)$ ($k \ge 3$) and the cubic Lambert series $L_\pm(2^k)$ ($k \ge 3$), which are outside the base-2 roster entries `BC-37`–`BC-39`. Simple normality of $E_+(8)$ in base 2 remains open, as do $E(2)$, $E_+(2)$, $E(4)$ and $E_+(4)$.

---

## Summary of results

| # | Result | Evidence |
| --- | --- | --- |
| 1 | **Middle-interval orbit formulas** (Thm. 1.2). For every radix $b \ge 2$, digit bound $\lfloor b/2\rfloor \le B \le b-2$, real $x$ and $N \ge 1$: $\sigma_B(x;N) = \#\{0 \le n < N : \lVert b^n x\rVert > B/(b(b-1))\}$ **exactly**. For $B = b-1$: $K_I(x;N) - 1 \le \sigma_{b-1}(x;N) \le K_I(x;N)$, where $K_I$ counts orbit points in $I = [\tfrac{1}{b+1}, \tfrac{b}{b+1})$. In base 2: $-2 \le 2\sigma_1(x;N) - \#\{n<N : \{2^n x\} \in [\tfrac16,\tfrac56)\} \le 1$, both ends attained | Paper proof; finite certificate (exact $\sigma_B$ by tail-constrained DP: 19,870 finite $b$-adic instances and 33,108 periodic/boundary rational instances, $b \le 7$) |
| 2 | **Exact signed-digit laws** (Cor. 1.3, Thm. 1.4). $A(b,B) = 1 - \tfrac{2B}{b(b-1)}$ ($B \le b-2$) and $A(b,b-1) = \tfrac{b-1}{b+1}$; every base-$b$ normal number has $\sigma_B(x;N)/N \to A(b,B)$ with the effective rate $\lvert\sigma_B/N - A\rvert \le D_N(x;b) + 1/N$; exact finite-window averages $A_L(b,B)$ in closed form | Paper proof; finite certificate (stationary laws $b \le 12$; $A_L$ by enumeration) |
| 3 | **Exact base-2 pattern formula and measure law** (Thm. 1.5, Cor. 1.6). $\sigma_{\rm free}(w) = \#_{10}(w) + \#\{00(10)^j11 \text{ in } 0w\}$; for every shift-invariant $\nu$, cost$(\nu) := \lim_N N^{-1}\int\sigma_1\,d\nu = \nu[\tfrac13,\tfrac23) = \nu[10] + \sum_j \nu[00(10)^j11]$. Bernoulli($p$): $\tfrac{pq}{1-pq}$; two-state Markov: $\tfrac{ac(2-a-c)}{(a+c)(1-ac)}$ for $(a,c) \ne (0,0), (1,1)$ | Paper proof; finite certificate (all 32,766 words of length $\le 14$; seven Markov laws) |
| 4 | **Sharp signed cost of $L$-normal numbers** (Thm. 1.7). With $\bar g_L = \tfrac13 - \tfrac13 4^{-\lfloor L/2\rfloor}$: every base-2 $L$-normal $x$ has $\bar g_L \le \liminf \sigma_1/N \le \limsup \sigma_1/N \le \bar g_L + 2^{-L}$. Both ends are attained by periodic $L$-normal numbers for $4 \le L \le 10$ (upper end for $2 \le L \le 10$); for $L \in \{2,3\}$ the lower end $1/4$ is a limit attained only non-periodically. Every de Bruijn word of order $L$ has cyclic cost $2^L\bar g_L$ or $2^L\bar g_L + 1$ | Paper proof (bounds, dichotomy); finite certificate (attainment, $L \le 10$); **all $L$: Open** |
| 5 | **Exact LP certificates** (Thms. 2.1–2.2). Primal/dual LP over shift-invariant word laws with grid-interval discrepancy and a type-augmented transducer cost. For every even $L$ a dual certificate is the single interval $[00(10)^{m-2}11,\ 11(01)^{m-1})$ with multiplier $2$ (optimal for $L \le 12$ by the numerical LP, and exactly at $L = 4$), giving $D_N(x;2) \ge 2\bar g_L - (2\sigma_1(x;N) + 5)/N$; exact Bellman–Ford potentials verified for $L = 4,\dots,12$ (oscillation 3); exact primal at $L = 4$ shows $\mathrm{LP}^*_4(\alpha) = 2(\tfrac{5}{16} - \alpha)$ on $[\tfrac{9}{32}, \tfrac{5}{16}]$ | Paper proof; finite certificate |
| 6 | **Universal discrepancy inequality** (Thm. 2.3). For every real $x$ and $N$: $D_N(x;2) \ge 2\,\lvert\sigma_1(x;N)/N - \tfrac13\rvert - 2/N$. Hence $D^-(x;2) \ge 2(\tfrac13 - \limsup_N \sigma_1(x;N)/N)$ | Paper proof |
| 7 | **$D^-(E_+(8);2) \ge 17431/300000 > 0.058103$** (Thm. 2.5), up from $2.34\times10^{-7}$ (`GF-40`), a factor $> 2.4\times10^5$; $\ge 0.061210$ with the sharper `GF-36` mean. $E_+(8)$ is **not 4-normal in base 2 and not 2-normal in base 8**. $D^-(E_+(16);2) \ge 0.2102$ ($\ge 0.2125$ with the `GF-36` mean; `GF-36` had $0.0459$). **New: $L_+(8)$ (cubic characters mod 7, 9, 13) is nonnormal in base 2**, $D^-(\cdot;2) \ge 0.1620, 0.1303, 0.1404$, and not 4-normal. For $L_-(8)$, simple nonnormality in base 8 with $D^-(\cdot;8) > 0$ is already `GF-31` Thm. 4A (via a Selberg–Delange weighted phase law); new here are an elementary proof, the same explicit base-2 bounds, and failure of 4-normality in base 2 | Paper proof + repository inputs (`GF-40` Thm 3.1, `GF-36` Thm 7.2 / Prop 8.1) |
| 8 | **Optimal-constant sandwich** (Thm. 2.6). The best lower bound for $D^-$ obtainable from "$\limsup\sigma_1/N \le \alpha$" alone lies in $[0.058102,\ 0.059108]$ for $\alpha = 0.304282$ and in $[0.058103,\ 0.059108]$ for the `GF-40` input $\alpha = 0.912845/3$: an explicit rational periodic $x$ with $\sigma_1$-density $4887/16076$ has exact orbit discrepancy $0.0591079541\ldots$ | Paper proof; finite certificate (16,076-bit witness) |
| 9 | **Carry-aware functionals** (Thm. 3.1, Props. 3.2–3.4). $\#_{10} \le \sigma_{\rm free} \le \min(\mathrm{tr}, \#_0, \#_1)$ exactly, both ends sharp; explicit separating families; hypothesis (H) is necessary for signed transfer; coefficient weights can be unbounded while $x = 1$ | Paper proof; finite certificate |
| 10 | **Multi-radix compatibility** (Props. 4.1–4.3, Table 4.4). Closure of the feasible level set under repetition and phased-Euler splicing; human parity proof of the `GF-37` obstruction $(2,2,3,1)$; new obstructions $(2,2,4,1)$ at $m=16$ and $(2,2,5,2)$ at $m=32$; complete feasible sets for seven small cases (e.g. $(2,2,3,1)$: $8\mathbb N\setminus\{8\}$; $(2,2,5,1)$: $32\mathbb N$) | Paper proof; finite certificate |

The main structural discovery is item 1: minimal signed-digit complexity is not merely bounded by an orbit statistic but **equals** one (exactly for $B \le b-2$, up to one unit for $B = b-1$). The LP of item 5 found it: its optimal dual certificate at every level is the dyadic inner approximation of $[\tfrac16, \tfrac56)$ with multiplier 2, and the limit of these certificates is Theorem 2.3.

---

## 0. Definitions

Fix a radix $b \ge 2$ and $x \in \mathbb R$ with base-$b$ digits $d_1 d_2 \cdots$ of $\{x\}$ (not ending in $(b-1)^\infty$). Write $t_n = \{b^n x\}$, $\lVert t\rVert$ for the distance to $\mathbb Z$, and for a set $J \subseteq [0,1)$

```math
K_J(x;N) = \#\{0 \le n < N : t_n \in J\}, \qquad F_N(J) = K_J(x;N)/N .
```

$D_N(x;b)$, $D^\pm(x;b)$, $L$-normality and $K_b$ are as in [`docs/research-objectives.md`](../../docs/research-objectives.md). The empirical word frequency $f_N(w)$ is the proportion of $0 \le n < N$ with $d_{n+1}\cdots d_{n+L} = w$, i.e. $t_n \in I_w$.

**Signed-digit complexity** (*P23-B3* §5). For $B \ge 1$, an **admissible representation** of $x$ is $a' : \mathbb Z_{\ge1} \to \{-B,\dots,B\}$ with $x - \sum_m a'_m b^{-m} \in \mathbb Z$. Its residuals are $r_n = \sum_{m > n} a'_m b^{n-m}$, so $r_n \equiv b^n x \pmod 1$ and $\lvert r_n\rvert \le \rho := B/(b-1)$. Define

```math
\sigma_B(x;N) = \min_{a' \text{ admissible}} \#\{1 \le m \le N : a'_m \ne 0\}.
```

In base 2, $\sigma_1(x;N)$ is the minimal number of nonzero signed binary digits ($\pm1$) on positions $1,\dots,N$.

**Free-boundary cost** (*P24-E* §3.2). For a word $w = w_1\cdots w_L$ over $\{0,\dots,b-1\}$, $\sigma^{(b,B)}_{\rm free}(w)$ is the minimum of $\#\{i : a_i \ne 0\}$ over carry paths $\delta_0,\dots,\delta_L \in C(b,B)$ with $a_i = w_i + b\delta_{i-1} - \delta_i \in [-B,B]$, where $C(b,b-1) = \{-1,0,1\}$ and $C(b,B) = \{-1,0\}$ for $B \le b-2$. $A_L(b,B) = (L b^L)^{-1}\sum_{\lvert w\rvert = L}\sigma_{\rm free}(w)$.

**Base-2 combinatorics.** $\#_{10}(w)$ counts adjacent pairs $10$; $\mathrm{tr}(w)$ counts adjacent unequal pairs. A *doubled pair* is an adjacent $00$ or $11$; the *type* at a position is the value of the most recent doubled pair (undefined before the first one). A *type change* $0 \to 1$ is an occurrence of $00(10)^j11$ ($j \ge 0$). The 4-state transducer $T_4$ of *P24-E* (states $A,B,C,D$, start $A$) is re-derived in the script. For $L \ge 1$ set

```math
g_L(w) = \min_{s \in \mathrm{Reach}(w_1\cdots w_{L-1})} \mathrm{cost}(s, w_L), \qquad \bar g_L = 2^{-L}\sum_{\lvert w\rvert = L} g_L(w),
```

where $\mathrm{Reach}(u)$ is the set of states $T_4$ can occupy after reading $u$ from any state. $w^*_L$ denotes the alternating word of length $L-1$ ending in $1$, followed by $1$.

**Invariant measures.** For a shift-invariant probability $\nu$ on $\{0,1\}^{\mathbb N}$ (equivalently a doubling-invariant measure on $[0,1)$; the coding is a bijection off the sequences ending in $1^\infty$, and the only invariant measure charging those is $\delta_{1^\infty}$, which codes $x = 0$), define

```math
\mathrm{cost}(\nu) = \lim_{N\to\infty} \frac1N \int \sigma_1(x;N)\, d\nu(x).
```

Corollary 1.6 shows that the limit exists and evaluates it for every $\nu$; when $\nu$ is ergodic it is also the $\nu$-a.e. limit of $\sigma_1(x;N)/N$ (Birkhoff's ergodic theorem).

---

## 1. D1: Signed-digit cost, exact laws and finite-order normality

### 1.1 Carry range

**Lemma 1.1 (Paper proof).** Let $a'$ be admissible for $x$ with digit bound $B$, $\lfloor b/2\rfloor \le B \le b-1$, and put $\delta_i = b^i\sum_{m>i}(a'_m - d_m)b^{-m}$. Then $\delta_i \in C(b,B)$, $a'_i = d_i + b\delta_{i-1} - \delta_i$, hence $\sigma_{\rm free}(d_1\cdots d_N) \le \sigma_B(x;N)$. If every reachable normalized DP vector has spread at most 1 (true for $2 \le b \le 12$, finite certificate), then also $\sigma_B(x;N) \le \sigma_{\rm free}(d_1\cdots d_N) + 1$.

*Proof.* $\delta_0 = \sum_m a'_m b^{-m} - \{x\} \in \mathbb Z$, and $\delta_i = b\delta_{i-1} - a'_i + d_i$ gives integrality and the digit relation. Since $a'_m - d_m \in [-B-(b-1), B]$, $\delta_i \in [-(B+b-1)/(b-1), B/(b-1)]$, the lower end attained only if $d_m = b-1$ for all $m > i$, which is excluded. For $B = b-1$ this leaves $\{-1,0,1\}$; for $B \le b-2$ it leaves $\{-1,0\}$ because $B/(b-1) < 1$ and $(B+b-1)/(b-1) < 2$. For the upper bound, $x - \sum_{i \le N} a_i b^{-i} \equiv b^{-N}(t_N + \delta_N)$, and $t_N + \delta_N \in [-\rho, \rho]$ is representable by digits in $[-B,B]$ (as $2B+1 \ge b$). For $B = b-1$ both $\delta_N \in \{-1,0\}$ qualify; for $B \le b-2$ one of $\delta_N = 0$ ($t_N \le \rho$) or $\delta_N = -1$ ($t_N \ge 1-\rho$) qualifies because $\rho \ge 1/2$. Restricting the final carry costs at most the spread. $\square$

### 1.2 The orbit formulas

**Theorem 1.2 (middle-interval orbit formulas; Paper proof, finite certificate).** Let $b \ge 2$, $x \in \mathbb R$, $N \ge 1$.

1. If $\lfloor b/2\rfloor \le B \le b-2$ and $\theta = \dfrac{B}{b(b-1)}$, then
```math
\sigma_B(x;N) = \#\{0 \le n < N : \lVert b^n x\rVert > \theta\}.
```
2. If $B = b-1$ and $I_b = [\tfrac{1}{b+1}, \tfrac{b}{b+1})$, then
```math
K_{I_b}(x;N) - 1 \le \sigma_{b-1}(x;N) \le K_{I_b}(x;N).
```
3. In base 2, with $J = [\tfrac16, \tfrac56)$: $\lvert K_J(x;N) - 2K_{I_2}(x;N)\rvert \le 1$ and
```math
-2 \le 2\sigma_1(x;N) - K_J(x;N) \le 1 .
```
Both ends are attained ($x = \tfrac14$, $N = 2$ gives $-2$; $x = \tfrac12$, $N = 2$ gives $+1$). More generally, in part (2), $\sigma_{b-1}(x;N) = K_{I_b}(x;N) - 1$ forces $t_N \notin I_b$.

*Proof.* (1) *Lower bound.* If $a'_{n+1} = 0$ then $r_n = r_{n+1}/b$, so $\lVert b^n x\rVert \le \lvert r_n\rvert \le \rho/b = \theta$. Hence every $n$ with $\lVert b^n x\rVert > \theta$ carries a nonzero digit $a'_{n+1}$.
*Upper bound.* Put $y_0 = x - \lfloor x + \tfrac12\rfloor$ and, recursively, $a_{n+1} = 0$ if $\lvert y_n\rvert \le \theta$, otherwise $a_{n+1}$ is the nearest integer to $by_n$ clipped to $[-B,B]$; $y_{n+1} = by_n - a_{n+1}$. Inductively $\lvert y_n\rvert \le \rho$: if $\lvert y_n\rvert \le \theta$ then $\lvert by_n\rvert \le \rho$; otherwise $\lvert by_n\rvert \le B + \rho$, and rounding leaves $\lvert y_{n+1}\rvert \le \tfrac12 \le \rho$ when $\lvert by_n\rvert \le B + \tfrac12$, while clipping leaves $\lvert y_{n+1}\rvert \le \rho$ otherwise. So $(a_m)$ is admissible (the remainder $b^{-n}y_n \to 0$), with zeros exactly where $\lvert y_n\rvert \le \theta$. Finally $\lvert y_n\rvert \le \theta \iff \lVert b^n x\rVert \le \theta$: if $\lvert y_n\rvert \le \tfrac12$ the two quantities agree, and if $\lvert y_n\rvert > \tfrac12$ then both exceed $\theta$, since $\lVert b^n x\rVert = 1 - \lvert y_n\rvert \ge (b-1-B)/(b-1) \ge 1/(b-1) > \theta$.

(2) *Lower bound (charging).* Here $\rho = 1$. Let $a'$ be optimal and call $n$ *counted* if $t_n \in I_b$. If $n$ is counted and $a'_{n+1} = 0$, then $\lvert r_n\rvert \le 1/b$, so $r_n = t_n \in [\tfrac{1}{b+1}, \tfrac1b]$ or $r_n = t_n - 1 \in [-\tfrac1b, -\tfrac{1}{b+1})$. Then $r_{n+1} = br_n$ lies in $[\tfrac{b}{b+1}, 1]$ or $[-1, -\tfrac{b}{b+1})$, so $t_{n+1} \notin I_b$, and $\lvert r_{n+1}\rvert \ge \tfrac{b}{b+1} > \tfrac1b$ forces $a'_{n+2} \ne 0$. Charge a counted $n$ to position $n+1$ if $a'_{n+1} \ne 0$ and to $n+2$ otherwise. A position $m$ charged from $n = m-2$ has $m-1$ uncounted, so it is not also charged from $m-1$: the charging is injective into nonzero positions in $[1, N+1]$, giving $K_{I_b} \le \sigma_{b-1}(x;N) + 1$.
*Upper bound.* Keep $y_n \in [-\tfrac{b}{b+1}, \tfrac{b}{b+1})$, $y_0 = x - \lfloor x + \tfrac12\rfloor$. If $y_n \in [-\tfrac{1}{b+1}, \tfrac{1}{b+1})$ set $a_{n+1} = 0$ (then $by_n$ stays in the domain). Otherwise the half-open window $(by_n - \tfrac{b}{b+1}, by_n + \tfrac{b}{b+1}]$ has length $> 1$, lies in $(-b, b)$ and excludes 0, so it contains an integer $a_{n+1} \in [-(b-1), b-1] \setminus \{0\}$ with $y_{n+1} = by_n - a_{n+1}$ in the domain. A case check over the six subintervals of the domain shows that $y_n \notin [-\tfrac{1}{b+1}, \tfrac{1}{b+1})$ exactly when $t_n \in I_b$ (the half-open conventions classify the boundary orbit $\{\tfrac{1}{b+1}, \tfrac{b}{b+1}\}$ consistently: $\tfrac{1}{b+1} \in I_b$ and $\tfrac{b}{b+1} \notin I_b$). So $\sigma_{b-1}(x;N) \le K_{I_b}(x;N)$.

*Defect forces exit.* Let $a'$ attain $\sigma_{b-1}(x;N)$. The charging map sends the $K_{I_b}(x;N)$ counted $n < N$ injectively to nonzero positions in $[1, N+1]$, of which at most $\sigma_{b-1}(x;N)$ lie in $[1,N]$. So $\sigma_{b-1} = K_{I_b} - 1$ requires position $N+1$ to be charged. Since $n = N$ is not counted, the charge comes from $n = N-1$ with $a'_N = 0$, and then, as shown above, $r_N \in [\tfrac{b}{b+1}, 1] \cup [-1, -\tfrac{b}{b+1})$, so $t_N \in [\tfrac{b}{b+1}, 1) \cup [0, \tfrac{1}{b+1})$, i.e. $t_N \notin I_b$.

(3) The doubling map sends $[\tfrac16,\tfrac13) \cup [\tfrac23,\tfrac56)$ onto $I_2 = [\tfrac13,\tfrac23)$ and is the full preimage of $I_2$ (at every endpoint as well). Hence $K_J(N) = K_{I_2}(N) + K_{I_2}(N+1) - [t_0 \in I_2] = 2K_{I_2}(N) + [t_N \in I_2] - [t_0 \in I_2]$, so $\lvert K_J - 2K_{I_2}\rvert \le 1$ and

```math
2\sigma_1(x;N) - K_J(x;N) = 2\bigl(\sigma_1(x;N) - K_{I_2}(x;N)\bigr) + [t_0 \in I_2] - [t_N \in I_2].
```

By (2), either $\sigma_1 = K_{I_2}$, and the right side lies in $\{-1, 0, 1\}$; or $\sigma_1 = K_{I_2} - 1$, in which case $t_N \notin I_2$ and the right side is $-2 + [t_0 \in I_2] \in \{-2, -1\}$. For $x = \tfrac14$: $t_0 = \tfrac14$ and $t_1 = \tfrac12$ both lie in $J$, and $\sigma_1(\tfrac14; 2) = 0$ (take $a'_1 = a'_2 = 0$ and the tail $0.0011\ldots_2 = \tfrac14$). For $x = \tfrac12$: $K_J = 1$ ($t_1 = 0$) and $\sigma_1(\tfrac12; 2) = 1$, since a zero prefix would need a tail $\equiv \tfrac12 \pmod 1$ of absolute value at most $\tfrac14$. $\square$

The script computes $\sigma_B(x;N)$ exactly (DP with the exact tail condition of Lemma 1.1) for 19,870 finite $b$-adic instances and, since finite $b$-adic rationals never land on the critical endpoints, for 33,108 instances at arbitrary rationals: every $p/q$ with $q \le 24$ together with $\theta$, $1-\theta$, $\theta/b$, $\tfrac12 \pm \theta$, $\tfrac{k}{b(b-1)}$, $\tfrac{1}{b+1}$, $\tfrac{b}{b+1}$, $\tfrac16$, $\tfrac56$, $\tfrac17$, $\tfrac37$, $\tfrac{1}{13}$, $\tfrac{5}{12}$, with $N \le 12$, $b = 2,\dots,7$ and all $B$. It confirms (1) with equality and (2)–(3) in every instance, as well as the implication $\sigma_{b-1} = K_{I_b} - 1 \Rightarrow t_N \notin I_b$. The observed extremes are $K_I - \sigma = 1$ and $2\sigma_1 - K_J \in \{-2, \dots, 1\}$ with both $-2$ and $+1$ attained, so all constants in (2)–(3) are sharp. (An earlier draft stated $\lvert 2\sigma_1 - K_J\rvert \le 3$ and claimed the value 3 was observed; the script never printed more than 2, and the value 3 is impossible by the proof above.)

### 1.3 Exact laws and effective rates

**Corollary 1.3 (Paper proof; finite certificate).** Put $A(b,B) = 1 - \tfrac{2B}{b(b-1)}$ for $\lfloor b/2\rfloor \le B \le b-2$ and $A(b,b-1) = \tfrac{b-1}{b+1}$. For every real $x$ and $N$,

```math
\Bigl\lvert \frac{\sigma_B(x;N)}{N} - A(b,B) \Bigr\rvert \le D_N(x;b) + \frac{[B = b-1]}{N}.
```

Every base-$b$ normal number satisfies $\sigma_B(x;N)/N \to A(b,B)$. For balanced digits ($B = \lfloor b/2\rfloor$, $b \ge 3$) this is $\tfrac{b-1}{b}$ for odd $b$ and $\tfrac{b-2}{b-1}$ for even $b$; for minimal-support digits ($B = b-1$) it is $\tfrac{b-1}{b+1}$ ($\tfrac13$ in base 2).

*Proof.* By Theorem 1.2, $\sigma_B/N$ is $F_N$ of an interval of length $A(b,B)$ (the open interval $(\theta, 1-\theta)$, or $I_b$, up to $1/N$). $\square$

The script independently computes $A(b,B)$ as the stationary mean increment of the determinized min-plus automaton (3 recurrent states for $B \le b-2$, $b \ge 4$; 6 states for $B = b-1$) for all $2 \le b \le 12$ and every $B$, and checks the closed forms exactly.

**Theorem 1.4 (exact finite windows; Paper proof, finite certificate).** For $b \ge 3$ and $L \ge 1$,

```math
A_L(b,B) = A(b,B) - \frac{2(b-1-B)\,(1 - b^{-L})}{(b-1)^2 L} \quad (\lfloor b/2\rfloor \le B \le b-2),
```

```math
A_L(b,b-1) = \frac{b-1}{b+1} - \frac{(b+3)\,(1 - (-1/b)^L)}{(b+1)^2 L},
```

and $A_L(2,1) = \tfrac13 - \tfrac{7 - (-1/2)^{L-1}}{18L}$ (*P24-E* Thm. 3.2).

*Proof.* For $B \le b-2$ the automaton from the all-zero vector $O$ has states $O, P, Q$ with $O \to P$ on digit 0, $O \to Q$ on $b-1$, $O \to O$ (cost 1) otherwise; $P, Q$ have expected step cost $(2b-3-B)/b$ and $O$ has $(b-2)/b$. The mass $s_t$ on $\{P,Q\}$ satisfies $s_{t+1} = 2/b + s_t/b$, $s_0 = 0$, so $s_t = \tfrac{2}{b-1}(1 - b^{-t})$; summing the expected costs $\tfrac{b-2}{b} + \tfrac{b-1-B}{b}s_t$ over $t < L$ gives the formula. For $B = b-1$ the six states lump into four ($X, Y, Z, W$) with symmetric masses $y_t = z_t = w_t = (1 - (-1/b)^t)/(b+1)$ and step cost $\tfrac{b-3}{b} + \tfrac{b+3}{b}y_t$; summing gives the second formula. Both are confirmed by exhaustive enumeration ($b = 3$: $L \le 7$; $b = 4$: $L \le 5$; $b = 5, 6$: $L \le 4$; $b = 7$: $L \le 3$). $\square$

### 1.4 Base 2: exact pattern formula and measure law

**Theorem 1.5 (Paper proof; finite certificate).** For every binary word $w$,

```math
\sigma_{\rm free}(w) = \#_{10}(w) + \#\{\text{occurrences of } 00(10)^j11,\ j \ge 0, \text{ in } 0w\},
```

the second term being the number of $0 \to 1$ type changes in $0w$.

*Proof.* In $T_4$ the costly steps are $B \xrightarrow{0}$, $D \xrightarrow{0}$ and $D \xrightarrow{1}$. After reading a 1 the state lies in $\{B, D\}$, so every $10$ costs exactly 1. State $D$ is entered only from $C$ on a 1, and $C$ is the state after reading $0$ from $A$, $C$ or $D$; tracing back, the state before a pair $11$ is $D$ exactly when the last doubled pair was $00$ (the alternation $C \xrightarrow{1} D \xrightarrow{0} C$ preserves this side, while $B \xrightarrow{0} A \xrightarrow{1} B$ preserves the other). The start state $A$ goes to $C$ on 0, which accounts for the virtual leading 0. $\square$

**Corollary 1.6 (measure law; Paper proof, finite certificate).** For every shift-invariant probability $\nu$,

```math
\mathrm{cost}(\nu) = \nu\bigl([\tfrac13,\tfrac23)\bigr) = \tfrac12\,\nu\bigl([\tfrac16,\tfrac56)\bigr) = \nu[10] + \sum_{j \ge 0} \nu[00(10)^j 11].
```

In particular the limit defining cost$(\nu)$ exists. For i.i.d. digits with $\Pr(1) = p$, $q = 1-p$: cost $= \dfrac{pq}{1-pq}$. For the stationary Markov chain with $\Pr(0\to1) = a$, $\Pr(1\to0) = c$ and $(a,c) \ne (0,0), (1,1)$ (so that $a + c > 0$ and $ac < 1$):

```math
\mathrm{cost} = \frac{ac\,(2-a-c)}{(a+c)(1-ac)} .
```

At the degenerate points: for $a = c = 1$ the chain is the alternating orbit $\tfrac12(\delta_{(01)^\infty} + \delta_{(10)^\infty})$, with cost $\tfrac12$ (the limit of the formula along $a = c \to 1$); for $a = c = 0$ every stationary law is a mixture of $\delta_{0^\infty}$ and $\delta_{1^\infty}$, with cost $0$.

*Proof.* By invariance $\int K_{I_2}(x;N)\,d\nu = N\nu(I_2)$ and $\int K_J(x;N)\,d\nu = N\nu(J)$. Since $\lvert\sigma_1 - K_{I_2}\rvert \le 1$ and $\lvert 2\sigma_1 - K_J\rvert \le 2$ pointwise (Theorem 1.2(2)–(3)), $N^{-1}\int\sigma_1\,d\nu$ converges to $\nu(I_2) = \tfrac12\nu(J)$; no ergodic decomposition is needed. For the last equality, $\sigma_{\rm free}(d_1\cdots d_N) \le \sigma_1(x;N) \le \sigma_{\rm free}(d_1\cdots d_N) + 1$ (Lemma 1.1, spread $\le 1$), and by Theorem 1.5 $\int\sigma_{\rm free}(d_1\cdots d_N)\,d\nu = (N-1)\nu[10] + \sum_{j \ge 0}(N-2j-3)^+\,\nu[00(10)^j11] + \varepsilon_N$, where $0 \le \varepsilon_N \le 1$ accounts for the at most one occurrence using the virtual leading 0. Each factor $(N-2j-3)^+/N$ is nondecreasing in $N$ with limit 1, so by monotone convergence $N^{-1}\int\sigma_{\rm free}\,d\nu \to \nu[10] + \sum_j \nu[00(10)^j11]$. (Equivalently, distinct type-change occurrences occupy disjoint windows, so those with $j > J$ number at most $N/(2J+6) + 1$; this is a uniform tail bound.) For Markov laws, $\nu[10] = \tfrac{ac}{a+c}$ and $\sum_j \nu[00(10)^j11] = \tfrac{c}{a+c}\cdot\tfrac{a(1-a)(1-c)}{1-ac}$; adding gives the formula, and $a = p$, $c = q$ gives the Bernoulli case. $\square$

At $p = \tfrac12$ both give $\tfrac13$; persistence $r = 1-a = 1-c$ gives $\tfrac{1-r}{2-r}$. The script checks the Markov formula, the Bernoulli specialization and the identity with $\nu[\tfrac13,\tfrac23)$ exactly for seven rational parameter pairs.

### 1.5 Sharp signed cost of $L$-normal numbers

**Theorem 1.7 (Paper proof; finite certificate for attainment).** Let $\bar g_L = \tfrac13 - \tfrac13\,4^{-\lfloor L/2\rfloor}$.

1. $g_L(w) = [w \text{ ends in } 10] + \#\{j : w \text{ ends in } 00(10)^j11\}$, and $\bar g_L$ has the stated closed form; also $\bar g_L = \tfrac12\lvert\mathrm{inner}_L(J)\rvert$ and $\bar g_L + 2^{-L} = \tfrac12\lvert\mathrm{outer}_L(J)\rvert$ for the inner and outer dyadic approximations of $J = [\tfrac16,\tfrac56)$ at level $L$.
2. Every base-2 $L$-normal real $x$ satisfies
```math
\bar g_L \le \liminf_{N} \frac{\sigma_1(x;N)}{N} \le \limsup_{N} \frac{\sigma_1(x;N)}{N} \le \bar g_L + 2^{-L}.
```
3. For $L \ge 2$ and every binary word, $\mathrm{cost}(S_t, d_{t+1}) = g_L(d_{t-L+2}\cdots d_{t+1}) + [d_{t-L+2}\cdots d_{t+1} = w^*_L][S_t = D]$ for $t \ge L-1$. Consequently every de Bruijn word of order $L$ has cyclic cost exactly $2^L\bar g_L$ or $2^L\bar g_L + 1$.
4. For $4 \le L \le 10$ both values occur, so both bounds in (2) are attained by rational (purely periodic) $L$-normal numbers; for $2 \le L \le 10$ the upper bound is attained. For $L \in \{2,3\}$ every exactly 2-normal periodic word of length $P$ has cost at least $P/4 + 1$, while $B_n = (0001)^n(1110)^n$ has cyclic cost exactly $2n$ (density $\tfrac14$) and cyclic 3-block counts $n \pm 1$ (deviation at most $\tfrac{1}{4n}$ in frequency). The concatenation $x = 0.B_1B_2B_3\cdots$, with $n = 1, 2, 3, \dots$ increasing by one at each step, is 3-normal and has $\sigma_1(x;N)/N \to \tfrac14 = \bar g_3$: the prefix $B_1\cdots B_n$ has length $4n(n+1)$, each block contributes an $O(1)$ boundary error to the 3-block counts and to the cost (Lemma 1.1, spread $\le 1$), and a partial block has length at most $8(n+1) = O(\sqrt N) = o(N)$. (Fast block growth, e.g. $n_k = 2^k$, would destroy normality along mid-block prefixes.) For $L = 1$ the infimum $0$ is attained in the same way by $0.\,0^11^1\,0^21^2\,0^31^3\cdots$. Hence for $L \le 3$ the lower bound in (2) is attained only by non-periodic numbers, and order-3 normality is compatible with every $\sigma_1$-density $\ge \tfrac14$.

*Proof.* (1) The explicit form of $g_L$ follows from the proof of Theorem 1.5: the only ambiguity in $\mathrm{Reach}$ is the side (A/B versus C/D) along an alternating context, which affects only a final $11$. Counting gives $\sum_w g_L(w) = 2^{L}(\tfrac14 + \sum_{4+2j \le L} 4^{-2-j})$. The approximation identities are elementary: for even $L$ the inner approximation is $[\tfrac{2^L+2}{6}, \tfrac{5\cdot2^L-2}{6})2^{-L}$, of length $\tfrac23 - \tfrac{2}{3\cdot2^L}$, and similarly for odd $L$ and for the outer one (checked exactly for $L \le 40$).
(2) By Theorem 1.2(3), $2\sigma_1(x;N) \ge K_J(x;N) - 2 \ge N\sum_{w \in \mathrm{inner}_L} f_N(w) - 3$, and $L$-normality sends the sum to $\lvert\mathrm{inner}_L(J)\rvert$. The upper bound uses $2\sigma_1 \le K_J + 1$ and $\mathrm{outer}_L(J)$.
(3) Along an alternating context the true state is $B$ or $D$ (context ending in 1) or $A$ or $C$ (ending in 0); only the pair ($D$, next bit 1) differs from the minimum. A de Bruijn word contains $w^*_L$ exactly once and every other window once, so the cyclic cost is $\sum_w g_L(w) + \varepsilon$ with $\varepsilon \in \{0,1\}$.
(4) The script finds, by seeded random Euler circuits and exact cyclic evaluation, de Bruijn words of each kind. For exact 2-normality, $\#_{10} = P/4$ and both $00$ and $11$ occur, so the cyclic type process changes from 0 to 1 at least once. The block family is checked exactly for $n \le 20$. $\square$

*Base $b \ge 3$ (Paper proof).* The same argument with Theorem 1.2 shows that every base-$b$ $L$-normal $x$ has $\lvert\mathrm{inner}_L(J_{b,B})\rvert \le \liminf \sigma_B/N \le \limsup \sigma_B/N \le \lvert\mathrm{outer}_L(J_{b,B})\rvert$, where $J_{b,B} = (\theta, 1-\theta)$ for $B \le b-2$ and $J_{b,b-1} = I_b$, and the approximations are by base-$b$ cylinders of length $L$. Whether these bounds are attained is open (Question 3).

*Comparison.* *P24-E* proved $\liminf \sigma_1/N \ge A_L = \tfrac13 - \tfrac{7 - (-1/2)^{L-1}}{18L}$ for $L$-normal $x$ (via $D^+$). Theorem 1.7 replaces the $O(1/L)$ deficit by the exact, exponentially small $\tfrac13 4^{-\lfloor L/2\rfloor}$ and shows it is sharp. Attainment for every $L \ge 4$ is **Open** (computational evidence through $L = 10$).

### 1.6 Prior art and attribution

Minimality of the non-adjacent form (NAF) for integers is due to Reitwiesner (1960); the mean NAF density $\tfrac13$ and the base-$b$ value $\tfrac{b-1}{b+1}$ for digits $\lvert a\rvert \le b-1$ are classical (Arno–Wheeler 1993; Clark–Liang 1973). The NAF of a real number, generated by the symmetric map $y \mapsto 2y - \varepsilon$ on $[-\tfrac23, \tfrac23]$ with nonzero digit exactly when $\lvert y\rvert \ge \tfrac13$, and its ergodic theory are studied by Dajani, Kraaikamp and Liardet (2006). The rounding representation and Theorem 5.4 of *P23-B3* give the one-sided comparison of $\sigma_B$ with $\lVert b^n x\rVert$. What we have not found in the literature, and claim here, is: the two-sided, all-$N$ identities of Theorem 1.2 for arbitrary admissible representations (exact equality for $B \le b-2$, one unit for $B = b-1$), the exact pattern formula of Theorem 1.5 for the free-boundary transducer, and the sharp $L$-normal interval of Theorem 1.7. The closed forms in Corollary 1.6 and Theorem 1.4 are routine once the automata are known; we claim no novelty for them. All priority claims here are provisional (rule 5 of [`docs/research-objectives.md`](../../docs/research-objectives.md)): a literature search that finds nothing does not establish novelty, and the search behind this note was limited.

---

## 2. D2: Optimal discrepancy witnesses via exact linear programming

### 2.1 The LP and the dual certificate theorem

Fix $L$ and $\alpha$. The **type-augmented LP** $\mathcal P_L(\alpha)$ has variables $\nu(\tau, w) \ge 0$ ($\tau \in \{0,1\}$ a type, $w \in \{0,1\}^L$), $\mu(w) = \nu(0,w) + \nu(1,w)$, and $D$:

- $\sum_{\tau,w} \nu(\tau,w) = 1$;
- stationarity on the type-augmented de Bruijn graph: for each $(\tau', u)$, $u \in \{0,1\}^{L-1}$, $\sum_{\tau,\beta : T(\tau,\beta,u_1) = \tau'} \nu(\tau, \beta u) = \sum_{a} \nu(\tau', ua)$, where $T(\tau, \beta_1, \beta_2) = \beta_2$ if $\beta_1 = \beta_2$ and $\tau$ otherwise;
- grid discrepancy: with $G_j = \sum_{w < j}\mu(w) - j2^{-L}$ ($0 \le j \le 2^L$), $\max_j G_j - \min_j G_j \le D$;
- cost: $\sum_{\tau,w}\nu(\tau,w)\,\kappa(\tau,w) \le \alpha$, where $\kappa(\tau,w) = [w_1w_2 = 10] + [w_1w_2 = 11][\tau = 0]$.

Minimize $D$. The **plain LP** drops $\tau$ and uses the cost $g_L$ instead of $\kappa$.

**Theorem 2.1 (dual certificate theorem; Paper proof).** Let $\rho = (\rho_j)_{0 \le j \le 2^L}$ have $\sum_j \rho_j = 0$ and $\sum_j\lvert\rho_j\rvert \le 2$, put $h(w) = \sum_{j > w}\rho_j$ and $K = 2^{-L}\sum_j j\rho_j$, and let $z \ge 0$, $c \in \mathbb Q$ and potentials $\psi(\tau,u)$ satisfy, for every edge $(\tau, w)$,

```math
h(w) + z\,\kappa(\tau,w) - c \ \ge\ \psi\bigl(T(\tau,w_1,w_2), w_2\cdots w_L\bigr) - \psi(\tau, w_1\cdots w_{L-1}).
```

Then for every real $x$ and every $N \ge 1$,

```math
D_N(x;2) \ \ge\ c - K - z\,\frac{\sigma_1(x;N) + 1}{N} - \frac{\max\psi - \min\psi}{N},
```

and consequently $D^-(x;2) \ge c - K - z\,\limsup_N \sigma_1(x;N)/N$.

*Proof.* (i) $G^{(N)}_j = F_N([0, j2^{-L})) - j2^{-L}$ satisfies $\lvert G^{(N)}_j - G^{(N)}_i\rvert \le D_N$; writing $\rho = \rho^+ - \rho^-$ with masses $\le 1$ gives $\sum_j \rho_j G^{(N)}_j \le D_N$, and $\sum_j\rho_jG^{(N)}_j = \sum_w f_N(w)h(w) - K$. (ii) Let $\tau_n$ be the type of the last doubled pair in $0d_1\cdots d_{n+1}$ (type 1 if none) and $W_n = d_{n+1}\cdots d_{n+L}$. The edges $(\tau_n, W_n)$ form a walk, so averaging the certificate inequality over $n < N$ telescopes the potentials to at most $\mathrm{osc}(\psi)/N$. (iii) $\sum_{n<N}\kappa(\tau_n, W_n) = \sigma_{\rm free}(d_1\cdots d_{N+1}) \le \sigma_1(x;N) + 1$ by Theorem 1.5 and Lemma 1.1. Combine; for the corollary take $N$ along a sequence with $D_N \to D^-$. $\square$

For the plain LP the same statement holds with $\kappa$ replaced by $g_L$, potentials on $\{0,1\}^{L-1}$, and $(\sigma_1 + 1)/N$ replaced by $(\sigma_1 + L - 1)/N$ (windows near the end are not covered by $\sigma_1(x;N)$).

### 2.2 Exact solution of the LP

**Theorem 2.2 (canonical certificates; Paper proof, finite certificate).** Let $L = 2m \ge 4$ and $I_L = [j_\beta, j_\gamma)2^{-L}$ with $j_\beta = \tfrac{2^L+2}{6}$, $j_\gamma = \tfrac{5\cdot2^L-2}{6}$, i.e. $j_\beta = 00(10)^{m-2}11$ and $j_\gamma = 11(01)^{m-1}$ in binary. Then $\rho = \delta_{j_\beta} - \delta_{j_\gamma}$, $z = 2$, $c = 0$ is a dual certificate for every even $L$: the integer weights $2\kappa(\tau,w) - [w \in I_L]$ admit potentials $\psi_L$. For $L = 4,6,8,10,12$ the script exhibits integer potentials with oscillation exactly 3 (exact Bellman–Ford). Since $c - K = \lvert I_L\rvert = 2\bar g_L$, every real $x$ satisfies

```math
D_N(x;2) \ \ge\ 2\bar g_L - \frac{2\sigma_1(x;N) + 2 + \mathrm{osc}(\psi_L)}{N} \qquad (\mathrm{osc}(\psi_L) = 3 \text{ for } L \le 12).
```

At $L = 4$ the exact primal solution $\nu_\alpha = \nu^{(0)} + \alpha\,\nu^{(1)}$ (21 nonzero entries, listed in the script) is feasible with cost $\alpha$ and grid discrepancy exactly $2(\tfrac{5}{16} - \alpha)$ for every $\alpha \in [\tfrac{9}{32}, \tfrac{5}{16}]$, so $\mathrm{LP}^*_4(\alpha) = 2(\tfrac{5}{16} - \alpha)$ on that range.

*Proof.* Potentials exist if and only if every cycle of the type-augmented graph has nonnegative weight. Following a doubled pair, the type label on a cycle is forced, so a cycle is a periodic word $W$ (of period $P$) with its true type process; the one exception, $(01)^\infty$, contains no $11$ and has the same weight under either label. The cycle weight is $2\,\mathrm{cost}(W) - \#\{\text{windows of } W \text{ in } I_L\}$. Since $I_L \subseteq J$, the number of windows in $I_L$ is at most $K_J$ over one period, and for a purely periodic point Theorem 1.2(2)–(3) give $K_{I_2} = \mathrm{cost}(W)$ and $K_J = 2\,\mathrm{cost}(W)$ per period (the bounded errors cannot accumulate over repeated periods). So every cycle has weight $\ge 0$. For $L \le 12$ the script checks the explicit potentials edge by edge. The primal claim is a finite exact check at $\alpha \in \{\tfrac{9}{32}, 0.304282, 0.302728, \tfrac{3}{10}, \tfrac{5}{16}\}$. Each entry of $\nu_\alpha$, the stationarity equations, the total mass and the cost are affine in $\alpha$, so feasibility and cost $= \alpha$ hold on the whole interval once they hold at its endpoints. The grid discrepancy $D_{\rm grid}(\alpha) = \max_j G_j - \min_j G_j$ is a maximum of affine functions minus a minimum of affine functions, hence **convex** in $\alpha$. Equality with $2(\tfrac5{16} - \alpha)$ at both endpoints gives $D_{\rm grid}(\alpha) \le 2(\tfrac5{16} - \alpha)$ on $[\tfrac9{32}, \tfrac5{16}]$, and the $L = 4$ dual certificate (Theorem 2.1 with $c - K = 2\bar g_4$, $z = 2$) gives $D_{\rm grid} \ge 2(\tfrac5{16} - \alpha)$ at every feasible point. $\square$

At $\alpha = 0.304282$ the floating LP solver (HiGHS via SciPy, *Numerical*, used only for discovery) returns:

| $L$ | 4 | 6 | 8 | 10 | 12 | limit |
| --- | --- | --- | --- | --- | --- | --- |
| plain LP optimum | 0.010957 | 0.031858 | 0.039711 | 0.045923 | 0.049049 | — |
| type-augmented LP optimum $= 2(\bar g_L - \alpha)$ | 0.016436 | 0.047686 | 0.0554985 | 0.0574516… | 0.0579399… | 0.0581026… |

The second row lists the exact rationals $2(\bar g_L - \alpha)$, truncated where marked (checked exactly in the script); HiGHS reproduces them to solver precision (it reports $0.055499$ for the exact $0.0554985$ at $L = 8$). The plain LP is weaker because its primal optima load mass on long alternating stretches that $g_L$ prices at zero; periodic words built from those optima have true signed density near $0.32$, far above $\alpha$. The plain value at $L = 4$ is itself certified exactly: $3D \ge 3G_3 - G_4 - G_{11} - G_{14} \ge \tfrac54 - 4\sum_w\mu(w)g_4(w)$, i.e. $D \ge \tfrac43(\tfrac{5}{16} - \alpha)$, with $g_4 = [w \text{ ends in } 10] + [w = 0011]$.

### 2.3 The limit theorem

**Theorem 2.3 (universal discrepancy inequality; Paper proof).** For every real $x$ and $N \ge 1$,

```math
D_N(x;2) \ \ge\ 2\,\Bigl\lvert \frac{\sigma_1(x;N)}{N} - \frac13 \Bigr\rvert - \frac{2}{N}.
```

Hence $D^-(x;2) \ge 2\bigl(\tfrac13 - \limsup_N \sigma_1(x;N)/N\bigr)$, $D^+(x;2) \ge 2\bigl(\tfrac13 - \liminf_N \sigma_1(x;N)/N\bigr)$ and $D^+(x;2) \ge 2\bigl(\limsup_N\sigma_1(x;N)/N - \tfrac13\bigr)$.

*Proof.* $J = [\tfrac16, \tfrac56)$ has length $\tfrac23$, so $\lvert K_J(x;N)/N - \tfrac23\rvert \le D_N$; insert $-2 \le 2\sigma_1 - K_J \le 1$ from Theorem 1.2(3), so $\lvert 2\sigma_1/N - K_J/N\rvert \le 2/N$. $\square$

The *P24-E* argument bounded each length-$L$ word frequency separately and paid a factor $2^L$; Theorem 2.3 uses one interval and loses nothing in the limit. In base $b \ge 3$, Corollary 1.3 gives the analogue with constant 1; whether a larger constant holds there is open (Question 4).

### 2.4 Signed-weight transfer

**Lemma 2.4 (Paper proof; adapts *P24-E* Thm. 3.1(c)).** Let $k \ge 1$, $a : \mathbb Z_{\ge1} \to \mathbb Z$ with $\lvert a(n)\rvert \le Cn^{A}$ for constants $C > 0$, $A \ge 0$, and $x = \sum_n a(n)2^{-kn}$. Then

```math
\limsup_{N\to\infty} \frac{\sigma_1(x;N)}{N} \ \le\ \frac1k\,\limsup_{X\to\infty}\frac1X\sum_{n \le X} w_\pm(a(n)),
```

where $w_\pm$ is the NAF weight.

*Proof.* For $N = kN_0$ take $M = N_0 + H$ with $2^{kH} > 3C'(M+1)^A$, where $\sum_{j\ge1}C(M+j)^A2^{-kj} \le C'(M+1)^A$; so $H = O(\log N_0)$. Write $S = \sum_{n \le M}a(n)2^{k(M-n)}$ in NAF, $S = S_{\rm hi} + S_{\rm lo}$ with $S_{\rm lo}$ the part below $2^{kH}$, $\lvert S_{\rm lo}\rvert < \tfrac23 2^{kH}$. Then $2^Nx = 2^{-kH}S_{\rm hi} + r$ with $\lvert r\rvert < \tfrac23 + \tfrac13 = 1$, so $r$ has a signed binary tail and $x$ has an admissible representation with at most $w_\pm(S) \le \sum_{n \le M}w_\pm(a(n))$ nonzero digits on $[1,N]$ (subadditivity of $w_\pm$). Since $w_\pm(a(n)) = O(\log n)$ and $H = O(\log N)$, the extra terms are $o(N)$; monotonicity in $N$ handles $N \not\equiv 0 \pmod k$. $\square$

### 2.5 Applications

**Theorem 2.5 (Paper proof; repository inputs).** Let $W_+ = \lim_X X^{-1}\sum_{n \le X}w_\pm(a_+(n))$, so that $W_+ \le 0.912845$ (`GF-40`, Thm. 3.1(a)) and $W_+ \in [0.908174, 0.908184]$ (`GF-36`, Thm. 7.2); and let $W_\chi$ be the cubic majorant means of `GF-36` Prop. 8.1, $W_7 \le 0.756905$, $W_9 \le 0.804516$, $W_{13} \le 0.789314$. By Lemma 2.4 (or *P24-E* Thm. 3.1(c)), $\limsup\sigma_1/N \le W/k$, and Theorem 2.3 gives $D^-(x;2) \ge 2(\tfrac13 - W/k)$. All decimals below are rounded outward from the exact rationals (upper bounds up, lower bounds down), and the script checks each rounding exactly:

| Constant | $\alpha \ge \limsup\sigma_1/N$ | $D^-(x;2) \ge$ | previous best | not 4-normal in base 2 |
| --- | --- | --- | --- | --- |
| $E_+(8)$ (`GF-40` input) | $0.912845/3 = 0.3042816\ldots$ | **$17431/300000 = 0.0581033\ldots$** | $2.34\times10^{-7}$ (`GF-40`) | yes |
| $E_+(8)$ (`GF-36` input) | 0.302728 | **0.061210** | — | yes |
| $E_+(16)$ (`GF-36` input) | 0.227046 | **0.212574** | 0.0459 (`GF-36`) | yes |
| $E_+(32)$ | 0.181637 | 0.303393 | 0.136726 | yes |
| $L_\pm(8)$, mod 7 | 0.252302 | **0.162063** | $L_+$: none (new); $L_-$: base 8 only, $D^-(\cdot;8) > 0$ (`GF-31`) | yes |
| $L_\pm(8)$, mod 9 | 0.268172 | **0.130322** | $L_+$: none (new); $L_-$: base 8 only (`GF-31`) | yes |
| $L_\pm(8)$, mod 13 | 0.263105 | **0.140457** | $L_+$: none (new); $L_-$: base 8 only (`GF-31`) | yes |
| $L_\pm(16)$, mod 7 / 9 / 13 | 0.189227 / 0.201129 / 0.197329 | 0.288214 / 0.264408 / 0.272009 | 0.1215 / 0.0977 / 0.1053 | yes |

Consequences: (a) $E_+(8)$ is nonnormal in base 2 with $D^- \ge 17431/300000 > 0.058103$, and in base 8 with $D^-(E_+(8);8) \ge \tfrac37\cdot0.058103 > 0.0249$ (radix descent, *P24-A* Prop. 2.4(5)). (b) Since $\alpha < \bar g_4 = \tfrac{5}{16}$, Theorem 1.7(2) shows $E_+(8)$, $E_+(16)$ and $L_\pm(8)$ are **not 4-normal in base 2**; by the cross-radix implication of `GF-37` (2-normal in base 8 implies 4-normal in base 2) they are **not 2-normal in base 8**. (c) The cubic series $L_\pm(8)$ were outside the transition method of `GF-36`, which needs $W_\chi/k < \tfrac14$; the signed route needs only $W_\chi/k < \tfrac13$. The two signs must be distinguished. **$L_+(8)$**: nonnormality (in base 2, hence in base 8 by Maxfield) is new here, with the explicit bounds above and failure of 4-normality in base 2; `GF-31` covers $L_+(2^k)$ only for $k \ge 4$, and simple normality of $L_+(8)$ in base 8 remains open. **$L_-(8)$**: `GF-31` Thm. 4A already proved simple nonnormality in base 8 with $D^-(L_-(8);8) > 0$, and hence nonnormality in base 2 by Maxfield. That proof uses the weighted phase law of `GF-31`, which rests on the Selberg–Delange method (External input); this is the factor $\tfrac23$ that, as `GF-36` Prop. 8.1 notes, brings $c_-$ to $k = 3$. What is new for $L_-(8)$ is an elementary proof that avoids Selberg–Delange, the explicit lower bounds $D^-(L_-(8);2) \ge 0.162063, 0.130322, 0.140457$, and failure of 4-normality in base 2 (and of 2-normality in base 8). (d) For large $k$ the transition bound of `GF-36` ($D^- \to 1$) eventually exceeds $2(\tfrac13 - W/k) \to \tfrac23$; at $k = 16$ ours is still larger (0.5531 vs 0.5344), and the two can be combined by taking the maximum.

### 2.6 Limitations

**Theorem 2.6 (optimal constant; Paper proof, finite certificate).** Let $\Delta(\alpha) = \inf\{D^-(x;2) : \limsup_N \sigma_1(x;N)/N \le \alpha\}$. Then $\Delta(\alpha) \ge 2(\tfrac13 - \alpha)$ for all $\alpha$, $\Delta$ is nonincreasing, and $\Delta(\alpha) \le D(W) = 0.0591079541\ldots \le 0.059108$ for every $\alpha \ge 4887/16076 = 0.3039935\ldots$. In particular

```math
0.058102 \le \Delta(0.304282) \le 0.059108, \qquad 0.058103 \le \Delta(0.912845/3) \le 0.059108 .
```

Here $2(\tfrac13 - 0.304282) = 43577/750000 = 0.0581026\ldots$, while $2(\tfrac13 - 0.912845/3) = 17431/300000 = 0.0581033\ldots$. The second $\alpha$ is the exact `GF-40` input for $E_+(8)$, and $0.304282$ is its upward rounding.

*Proof.* The lower bound is Theorem 2.3. For the upper bound, the script decodes an explicit binary word $W$ of length $P = 16076$ (from the $L = 12$ type-augmented primal, via an Euler circuit on integerized edge weights), and verifies exactly: cyclic signed cost 4887 (density $4887/16076 \le 0.303994 < 0.912845/3$; also $K_{[1/3,2/3)} = 4887$ and $K_J = 9774$ over one period), and the extreme discrepancy of the periodic orbit of $x_W = W/(2^P - 1)$, computed exactly by sorting the $P$ rotations, is $0.059107954113\ldots \le 0.059108$. For the purely periodic $x_W$, $\sigma_1(x_W;N)/N \to 4887/16076$ and $D_N(x_W;2) \to D(W)$. $\square$

So no argument whose only input about $E_+(8)$ is $\limsup\sigma_1/N \le 0.912845/3$ (or $\le 0.304282$) can prove $D^-(E_+(8);2) > 0.059108$; the bound $0.058103$ is within 1.8% of optimal for that input. Similarly, because $\bar g_3 = \tfrac14 < 0.304282$ is attained by the 3-normal number of Theorem 1.7(4), no such argument can rule out order-3 normality of $E_+(8)$ or $L_\pm(8)$ in base 2: "not 4-normal" is the strongest finite-order conclusion this input can give. The ratio $D(W)/(2(\tfrac13 - \text{density}))$ is $1.007299\ldots$ for this witness, against $1.024$ for a level-10 witness built the same way (*Numerical*, not embedded), which supports Conjecture 9.1 below.

Further limitations. (i) *Finite-level LP ceiling*: at level $L$ the type-augmented LP cannot exceed $2(\bar g_L - \alpha)$ (proved for $L = 4$, numerical for $L \le 12$), and the plain LP is strictly weaker. (ii) *$E_+(4)$ barrier*: the signed-transfer bound is $W_+/2 \ge 0.454087 > \tfrac13$, so this route proves nothing for $E_+(4)$ without a certified carry-cancellation deficit exceeding $W_+/2 - \tfrac13 \ge 0.120753$ in the limsup of $\sigma_1/N$ (compare *P24-E* §3.4, $0.1231$ from the upper enclosure). The same obstruction applies more strongly to $E_+(2)$ ($W_+ > \tfrac13$ by $0.5748$) and to $E(4)$ ($\mu_{\rm NAF}(\tau)/2 > \tfrac13$). (iii) For any input of the form $\limsup\sigma_1/N \le \alpha$ with $\alpha \ge \tfrac13$, every normal number is consistent with the input, so no nonnormality can follow.

---

## 3. D3: Carry-aware functionals

**Theorem 3.1 (Paper proof; finite certificate).** For every binary word $w$ (with $\#_0, \#_1$ the digit counts),

```math
\tfrac12(\mathrm{tr}(w) - 1) \ \le\ \#_{10}(w) \ \le\ \sigma_{\rm free}(w) \ \le\ \min\bigl(\mathrm{tr}(w),\ \#_0(w),\ \#_1(w)\bigr).
```

For densities: $\tfrac12\mathrm{tr} \le \sigma_1 \le \min(\mathrm{tr}, f_0, f_1)$ up to $O(1/N)$, and both ends are attained.

*Proof.* By Theorem 1.5, $\sigma_{\rm free} = \#_{10} + \#P$ with $P$ the type-change occurrences. Each occurrence of $00(10)^j11$ ends in $011$; distinct occurrences end at distinct positions, so $\#P \le \#_{01}$ and $\sigma_{\rm free} \le \mathrm{tr}$. Each occurrence's closing $11$ begins a run of ones of length $\ge 2$ that it is the only one to begin; each run of ones contributes at most one $10$; summing over runs gives $\sigma_{\rm free} \le \#_1$. Each occurrence's opening $00$ ends a run of zeros (followed by 1), at most one occurrence per run, and each run of zeros is preceded by at most one $10$; so $\sigma_{\rm free} \le \#_0$ (a leading run with the virtual 0 still has real length $\ge 1$). The left inequalities hold because $10$ and $01$ alternate. All words of length $\le 14$ are checked. $\square$

**Proposition 3.2 (separating families; Paper proof, finite certificate).** Exact cyclic densities:

| Periodic word | $\sigma_1$-density | transition density | ones | remark |
| --- | --- | --- | --- | --- |
| $(0001)$ | $1/4$ | $1/2$ | $1/4$ | $\sigma = \mathrm{tr}/2$ |
| $(0011)$ | $1/2$ | $1/2$ | $1/2$ | $\sigma = \mathrm{tr} = f_1 = f_0$ |
| $(01)$ | $1/2$ | $1$ | $1/2$ | $\sigma = \mathrm{tr}/2$, maximal $\sigma$ at $f_1 = \tfrac12$ |
| $(0^n1^n)$, $n \ge 2$ | $1/n$ | $1/n$ | $1/2$ | simply normal, $\sigma \to 0$ (at $n = 1$ this is $(01)$) |
| normal $x$ | $1/3$ | $1/2$ | $1/2$ | $\sigma/\mathrm{tr} = 2/3$ (Cor. 1.3) |

The ratio $\sigma_1/\mathrm{tr}$ ranges over $[\tfrac12, 1]$; a normal number sits at $\tfrac23$, which is why signed transfer (threshold $\tfrac13$) reaches $k = 3$ where transition transfer (threshold $\tfrac12$ for $\mathrm{tr}$, i.e. $W/k < \tfrac14$) does not.

**Proposition 3.3 ((H) is necessary for signed transfer; Paper proof).** Let $x \in (0,1)$ be any base-2 normal number with ones at positions $m_1 < m_2 < \cdots$, so $x = \sum_j 2^{-m_j}$. Since $m_j/j \to 2$, there is $s$ with $m_j \le 4(j+s)$ for all $j$; set $a(j+s) = 2^{4(j+s) - m_j}$ and $a(n) = 0$ for $n \le s$. Then $x = \sum_n a(n)2^{-4n}$, every nonzero coefficient has $w_\pm = 1$, so the right side of Lemma 2.4 would be $\tfrac14$, yet $\sigma_1(x;N)/N \to \tfrac13$ by Corollary 1.3. Here $\log a(n) \sim 2n\log 2$ violates polynomial growth.

**Proposition 3.4 (unbounded weights, trivial expansion; Paper proof, finite certificate).** For $k \ge 2$ and $a(n) = (2^k - 1)n - 1$, $\sum_{n \le M}a(n)2^{-kn} = 1 - (M+1)2^{-kM}$, so $x = 1$ and $\sigma_1(x;N) = 0$, while $w_\pm(a(n))$ is unbounded (choose $n$ with $a(n) \equiv (01)^r \pmod{2^{2r}}$, possible as $2^k - 1$ is odd) and its mean over $n \le 400$ already exceeds $k/3$ for $k = 3, 4, 8$. Transfer bounds are one-sided; the gap is the carry-cancellation deficit.

*Other functionals.* In base 2 the Phase 23 functional $\chi_N(x) = \mathrm{tr}(d_1\cdots d_{N+1})$ differs from $\mathrm{tr}_N(x) = \mathrm{tr}(d_1\cdots d_N)$ by $[d_N \ne d_{N+1}] \in \{0,1\}$, so the two have the same densities. Block entropy is independent of $\sigma_1$ on periodic words (zero entropy, any density in $[0, \tfrac12]$), but empirical entropy rate 1 forces normality and hence $\sigma_1/N \to \tfrac13$. The oriented borrow length and window carry losses of *P24-A* §2 bound coefficient-to-digit transfer from one side only (Prop. 3.4); Theorem 1.2 shows that, among these, $\sigma_B$ is the functional whose asymptotics are an exact linear statistic of the orbit.

---

## 4. D4: Multi-radix finite-order classification

Throughout §4, $b \ge 2$, $k \ge 2$, $L_1, L_2 \ge 1$, and $\mathbb N = \mathbb Z_{\ge1}$. Let $F(b,k,L_1,L_2)$ be the set of $m \in \mathbb N$ with $k \mid m$ such that $K_{b^m}$ contains a real number that is $L_1$-normal in base $b$ and $L_2$-normal in base $b^k$. Put $\ell = \mathrm{lcm}(b^{L_1}, kb^{kL_2})$, $L_* = \max(L_1, kL_2)$ and $s = kb^{L_*}$. `GF-37` (*P24-B* Thm. 4.3) proves $F \subseteq \ell\mathbb N$, $s\mathbb N \subseteq F$, and $F = \ell\mathbb N$ when $L_1 \le kL_2$ or $\gcd(k,b) = 1$.

**Proposition 4.1 (reduction; Paper proof).** $m \in F$ if and only if there is a cyclic word $W$ of length $m$ over $\{0,\dots,b-1\}$ in which every $L_1$-word occurs $m/b^{L_1}$ times among the $m$ cyclic positions and every $kL_2$-word occurs $m/(kb^{kL_2})$ times among the positions $\equiv 0 \pmod k$. Equivalently, there is a closed walk of length $m$ in the phased de Bruijn graph $G_{\rm phased}(b,k,L_*)$ with these marginals.

*Proof.* By `HigherOrderTower.mem_pow_kernel_decomp` and `wordFreq_tower_limit` (kernel-verified, `GF-29`/`GF-37`), $x = r/(b^m - 1) + u$ with $u \in M_b$ and the word frequencies of $x$ in bases $b$ and $b^k$ are the cyclic frequencies of the period $W$ of $r/(b^m-1)$ (at all positions, resp. at aligned positions). $\square$

**Proposition 4.2 (closure; Paper proof).** (a) $m \in F \Rightarrow jm \in F$ for all $j \ge 1$ (repeat $W$). (b) $m \in F \Rightarrow m + s \in F$: the phased Euler circuit $W_0$ of `GF-37` visits every vertex of $G_{\rm phased}(b,k,L_*)$, so it can be spliced into the closed walk of $W$ at a common vertex with a common phase; all marginal counts add. (c) Hence $F$ is a union of progressions $m_0 + s\mathbb Z_{\ge0}$ ($m_0 \in F$), closed under multiplication by positive integers, and if some $m_1 \in F$ has $\gcd(m_1/\ell, s/\ell) = 1$ then $F \supseteq \ell\mathbb N \cap [s m_1/\ell, \infty)$.

**Proposition 4.3 (parity proof of the `GF-37` obstruction; Paper proof).** $8 \notin F(2,2,3,1)$. *Proof.* A witness of length 8 is a de Bruijn word of order 3, whose runs have lengths 1 and 3 (one of each for zeros and for ones), all odd. Run starting positions therefore alternate in parity, so both runs of zeros start at positions of the same parity, and the two occurrences of $10$ (immediately before them) have the same parity. Uniform base-4 digits at even positions require exactly one $10$ at an even and one at an odd position. $\square$

**Table 4.4 (complete feasible sets; finite certificate + Props. 4.2–4.3).**

| $(b,k,L_1,L_2)$ | $\ell$ | $s$ | exhaustive at $m = \ell$ | witness | $F$ |
| --- | --- | --- | --- | --- | --- |
| $(2,2,3,1)$ | 8 | 16 | infeasible (0/2 de Bruijn words) | $m = 24$ | $8\mathbb N \setminus \{8\}$ |
| $(2,2,4,1)$ | 16 | 32 | infeasible (0/16) | $m = 48$ | $16\mathbb N \setminus \{16\}$ |
| $(2,2,5,1)$ | 32 | 64 | feasible (256/2048) | $m = 32$ | $32\mathbb N$ |
| $(2,2,5,2)$ | 32 | 64 | infeasible (0/2048) | $m = 96$ | $32\mathbb N \setminus \{32\}$ |
| $(2,4,5,1)$ | 64 | 128 | — | $m = 64$ | $64\mathbb N$ |
| $(2,2,6,1)$ | 64 | 128 | — | $m = 64$ | $64\mathbb N$ |
| $(2,4,6,1)$ | 64 | 256 | — | $m = 64$ | $64\mathbb N$ |

The `GF-37` sufficient level $s$ is not necessary: it fails to be the minimum in four of the seven cases, and the necessary level $\ell$ fails in three. The new obstruction $(2,2,4,1)$ shows the phenomenon is not confined to $L_1 = kL_2 + 1$, and $(2,2,5,2)$ shows it persists at larger $kL_2$; $(2,2,5,1)$ shows it disappears once $L_1 - kL_2 = 3$ in that family. For $(b^{k_1}, b^{k_2})$ with $k_1 \mid k_2$ the problem is the case $(b^{k_1}, k_2/k_1)$; in general the same circulation framework applies over base $b^{\gcd(k_1,k_2)}$ with phase group $\mathbb Z/\mathrm{lcm}(k_1,k_2)$ (not computed here). Overlapping word frequencies (all positions) and aligned radix blocks (positions $\equiv 0 \bmod k$) enter as separate marginals throughout; no statement above conflates them.

---

## 5. External and repository inputs; hypothesis verification

| Input | Used in | Label | Hypotheses checked |
| --- | --- | --- | --- |
| `GF-40` *P24-E* Thm. 3.1(a): $\mu_{\rm NAF}(a_+) \le 0.912845$; Thm. 3.1(c): $\limsup\sigma_1(E_+(2^k);N)/N \le \mu_{\rm NAF}(a_+)/k$ | Thm. 2.5 | Repository input (Paper proof + finite certificate) | same quantity $\sigma_1$ (*P23-B3* definition); same mean as $W_+$ |
| `GF-36` *P24-A* Thm. 7.2: $W_+ \in [0.908174, 0.908184]$ | Thm. 2.5, §2.6 | Repository input (Paper proof + finite certificate) | consistent with `GF-40` enclosure (intersection nonempty) |
| `GF-36` *P24-A* Prop. 8.1: $w_\pm(c_\pm(n)) \le G_\chi(n)$, means $W_7, W_9, W_{13}$ | Thm. 2.5 | Repository input (Paper proof + finite certificate) | $\lvert c_\pm(n)\rvert \le 3\tau(n)$ gives polynomial growth for Lemma 2.4 |
| `GF-37` cross-radix implication; kernel decomposition (`HigherOrderTower`) | Thm. 2.5(b), Prop. 4.1 | Repository input (kernel-verified Lean + paper proof) | $k \mid m$ assumed throughout §4 |
| Radix descent *P24-A* Prop. 2.4(5) | Thm. 2.5(a) | Repository input (Paper proof) | — |
| `GF-31` Thm. 4A ([dense-characters-and-nonfundamental-forms.md](../phase23/dense-characters-and-nonfundamental-forms.md)): $L_-(2^k)$ simply nonnormal in radix $2^k$ with $D^- > 0$ for $k \ge 3$, and $L_+(2^k)$ for $k \ge 4$ | Thm. 2.5(c) (priority only) | Repository input (Paper proof; Selberg–Delange as External input) | not used as a proof input; cited to delimit what is new for $L_-(8)$ |
| Birkhoff ergodic theorem | Cor. 1.6 (ergodic remark only) | External input | not needed for the formula, which uses only invariance |
| Maxfield (1953): normality in $b$ iff in $b^k$ | remarks | External input | — |
| Borel (1909): normal numbers exist | Prop. 3.3 | External input | — |
| Reitwiesner (1960), Clark–Liang (1973), Arno–Wheeler (1993), Dajani–Kraaikamp–Liardet (2006) | §1.6 | Attribution only (not used as proof inputs) | — |

No conditional hypothesis is used. LP duality is used only through the explicit certificate inequality of Theorem 2.1, which is verified directly; no duality theorem is invoked.

---

## 6. Evidence ledger

- *Paper proof*: Lemma 1.1, Theorem 1.2, Corollary 1.3, Theorem 1.4, Theorem 1.5, Corollary 1.6, Theorem 1.7(1)–(3), Theorem 2.1, Theorem 2.3, Lemma 2.4, Theorem 2.5 (given repository inputs), Theorem 2.6 lower bound, Theorem 3.1, Propositions 3.3–3.4, 4.1–4.3.
- *Finite certificate*: DP spread $\le 1$ for $b \le 12$; transducer and pattern identity on all words of length $\le 14$; orbit formulas on exact finite $b$-adic and periodic/boundary rational instances; outward rounding of every stated decimal; $A(b,B)$ for $b \le 12$; $A_L$ by enumeration; Markov identities; $\bar g_L$ for $L \le 16$; approximation identities for $L \le 40$; de Bruijn dichotomy samples and attainment ($L \le 10$); canonical dual certificates $L = 4,\dots,12$; plain $L = 4$ certificate; $L = 4$ primal; the 16,076-bit witness; exhaustive de Bruijn enumerations and multi-radix witnesses.
- *Numerical* (discovery only): HiGHS LP optima for $L = 6,\dots,12$ (plain) and the table in §2.2; the primal-to-periodic-word construction.
- *Finite measurement*: none of the conclusions depends on digit statistics of any constant.
- *Open*: attainment in Theorem 1.7 for $L > 10$; exact $\Delta(\alpha)$; base-$b$ optimal constants; Questions 9.x.

---

## 7. Reproduction

```
python -B scripts/phase25_digit_complexity.py
```

Expected: `ALL 844 CHECKS PASSED`, exit code 0, about 20–30 s on a laptop. The script needs only the standard library. Random searches use fixed seeds (25001–25004) and every result they return is re-verified exactly, so a different random implementation could change which witness is found but not the validity of a passing run. The LP solves that discovered the certificates are not part of the script (they need SciPy); the certificates themselves are embedded or regenerated combinatorially.

## 8. Exact finite tests (script sections)

1. **D1.1** 7 normalized DP vectors, spread $\le 1$; transducer $=$ DP and pattern formula on all 32,766 words of length $\le 14$; type-change count equals direct pattern count for length $\le 11$.
2. **D1.2** Orbit formulas on 19,870 exact finite $b$-adic $(x,N)$ instances and 33,108 exact rational instances (all $p/q$ with $q \le 24$ plus the critical boundary and periodic points), $b = 2,\dots,7$, every $B$; base 2: $\lvert K_J - 2K_{I_2}\rvert \le 1$ and $-2 \le 2\sigma_1 - K_J \le 1$ with both ends attained; $\sigma_{b-1} = K_{I_b} - 1 \Rightarrow t_N \notin I_b$; rational DP cross-checked against the finite-expansion DP.
3. **D1.3** Stationary $A(b,B)$ for $b \le 12$; $A_L(b,B)$ by enumeration; Markov and Bernoulli identities.
4. **D1.4** $\bar g_L$ ($L \le 16$); explicit $g_L$ ($L \le 12$); pointwise identity with $w^*_L$; inner/outer identities ($L \le 40$); de Bruijn dichotomy and attainment; exactly 2-normal cycles of length $\le 16$; the $(0001)^n(1110)^n$ family.
5. **D2.1–D2.3** Bellman–Ford potentials for the canonical dual at $L = 4,6,8,10,12$; plain $L = 4$ certificate; $L = 4$ primal at five values of $\alpha$; exact values $2(\bar g_L - \alpha)$ of Table 2.2.
6. **D2.4** Witness decoding, cyclic cost 4887, exact periodic discrepancy $D(W) = 0.059107954113\ldots \le 0.059108$, $K_{[1/3,2/3)}$ and $K_J$ counts; both versions of the Theorem 2.6 lower bound ($43577/750000$ and $17431/300000$).
7. **D2.5** Exact application bounds and comparisons, each stated decimal checked to be the outward rounding of the exact rational; $E_+(4)$ barrier.
8. **D3** Functional inequalities on all words of length $\le 14$; separating families; telescoping identities.
9. **D4** Parity check and enumeration for $(2,2,3,1)$; exhaustive order-4 and order-5 enumerations; six witnesses; repetition and splice closure.

## 9. Open questions

1. **Conjecture 9.1.** $\Delta(\alpha) = 2(\tfrac13 - \alpha)$ for all $\alpha$ in some interval $[\alpha_0, \tfrac13]$, i.e. the constant 2 in Theorem 2.3 is optimal. (Evidence: the LP values, and witnesses whose ratio $D(W)/(2(\tfrac13 - \text{density}))$ falls from $1.024$ at level 10 to $1.0073$ at level 12.)
2. Do periodic $L$-normal numbers attain $\bar g_L$ for every $L \ge 4$? Is there an explicit de Bruijn family?
3. Sharp signed cost of $L$-normal numbers in base $b \ge 3$: are the inner/outer approximations of the intervals in Theorem 1.2 attained?
4. Optimal constant $c_b$ in $D_N(x;b) \ge c_b\lvert\sigma_B/N - A(b,B)\rvert - O(1/N)$ for $b \ge 3$ (Corollary 1.3 gives $c_b \ge 1$; in base 2, $c_2 = 2$).
5. A certified upper bound $\limsup\sigma_1(E_+(4);N)/N < \tfrac13$ would make $E_+(4)$ nonnormal; it needs a carry-cancellation deficit $> 0.1207$ beyond the zero-carry transfer.
6. Simple nonnormality of $E_+(8)$ in base 2 (cost bounds give no information on single-digit frequencies: $\bar g_1 = 0$).
7. For multi-radix compatibility: is the exception set $\ell\mathbb N \setminus F$ always finite? Characterize it, e.g. for $b = 2$, $k = 2$, $L_2 = 1$ and all $L_1$.

## 10. Standing objectives advanced

- **Objective 1 (normality):** exact signed-digit law for normal numbers in every base with an effective rate (Cor. 1.3); sharp signed cost interval for $L$-normal numbers (Thm. 1.7).
- **Objective 2 (nonnormality):** $E_+(8)$ not 4-normal in base 2 and not 2-normal in base 8; new nonnormality of $L_+(8)$ (moduli 7, 9, 13); for $L_-(8)$, already simply nonnormal in base 8 by `GF-31`, an elementary Selberg–Delange-free proof, explicit base-2 $D^-$ bounds and failure of 4-normality in base 2; improved quantitative nonnormality for $E_+(2^k)$, $L_\pm(2^k)$.
- **Objective 3 (quantify):** $D^-(E_+(8);2) \ge 0.058103$ (a factor $> 2.4\times10^5$ over `GF-40`), $D^-(E_+(16);2) \ge 0.2125$, explicit $D^-$ for the cubic family; exact frequency laws for Bernoulli and Markov digit processes; Theorem 2.3.
- **Objective 4 (limitations):** optimal-constant sandwich (Thm. 2.6); finite-level LP ceilings; $E_+(4)$, $E_+(2)$, $E(4)$ barriers for the signed route; multi-radix obstructions (Props. 4.2–4.3, Table 4.4).

## 11. Registry and benchmark recommendations (text only; no registry or benchmark file is edited)

A new `GF` entry could record Theorems 1.2, 1.7, 2.3 and 2.5 and Table 4.4, citing this note and script. Benchmark statuses for `BC-37`–`BC-39` are unchanged. If `docs/benchmarks/arithmetic-families.toml` tracks $E_+(8)$, $E_+(16)$ or $L_\pm(2^k)$, the recorded $D^-$ lower bounds and finite-order statuses could be updated from Theorem 2.5 after independent review.

## References

Bibliographic details below were supplied from memory and then corrected after the cross-model referee check in `notes/phase25/reviews/track-d-review.md` (which is not independent human verification); verify them before any external use.

- S. Arno, F. S. Wheeler, Signed digit representations of minimal Hamming weight, *IEEE Trans. Computers* 42 (1993) 1007–1010.
- E. Borel, Les probabilités dénombrables et leurs applications arithmétiques, *Rend. Circ. Mat. Palermo* 27 (1909) 247–271.
- W. E. Clark, J. J. Liang, On arithmetic weight for a general radix representation of integers, *IEEE Trans. Inform. Theory* 19 (1973) 823–826.
- K. Dajani, C. Kraaikamp, P. Liardet, Ergodic properties of signed binary expansions, *Discrete Contin. Dyn. Syst.* 15 (2006) 87–112.
- N. G. de Bruijn, A combinatorial problem, *Proc. Kon. Ned. Akad. Wetensch.* 49 (1946) 758–764.
- J. E. Maxfield, Normal $k$-tuples, *Pacific J. Math.* 3 (1953) 189–196.
- G. W. Reitwiesner, Binary arithmetic, *Advances in Computers* 1 (1960) 231–308.
- Repository: `GF-29`, `GF-31`, `GF-32`, `GF-36`, `GF-37`, `GF-40` and the Phase 23–24 notes cited above.
