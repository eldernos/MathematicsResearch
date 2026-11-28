# Nonlinear Normality Boundaries, Computable Badly Approximable Polynomial-Normal Numbers, and Reduced-Loss Deterministic Series (Phase 25, Track F)

## 0. Setup, definitions, and summary

Fix an integer base $b \ge 2$, an odd prime $p \nmid b$, $t = \operatorname{ord}_p b$, $a_0 = v_p(b^t - 1) \ge 1$, $B = b^t$, and integers $d \ge 2$, $s \ge 1$. Write $v_p(n)$ for the $p$-adic valuation of $n \ne 0$, $e(u) = \exp(2\pi i u)$, $\{u\} = u - \lfloor u \rfloor$ for the fractional part, $\|u\| = \min(\{u\}, 1 - \{u\})$ for distance to the nearest integer, and $\tau(q) = \sum_{d \mid q} 1$ for the divisor function. Natural logarithms are written $\log$.

* **Equality-boundary powers.** Set
  $$
  C_s(d) = \sum_{i \ge 1} p^{-s v_p(i)} B^{-i^d}, \qquad X = C_s(d)^d = \sum_{m \ge d} c_m B^{-m},
  $$
  where $c_m = \sum_{x_1^d + \cdots + x_d^d = m,\, x_i \ge 1} p^{-s \sum_{i=1}^d v_p(x_i)}$ is the ordered positive $d$-fold convolution coefficient. For $M \ge 1$, write the shifted prefix $R_M = \sum_{m \le M} c_m B^{M - m}$, its reduced denominator $q_M = \operatorname{den}(R_M)$, its reduced fractional-part numerator modulo $q_M$ as $A_M \in [0, q_M)$ with $R_M \equiv A_M / q_M \pmod 1$, and its positive real tail $T_M = B^M X - R_M = \sum_{j \ge 1} c_{M+j} B^{-j} > 0$.
* **Digit distribution and local discrepancy.** For any $x \in \mathbb{R}$ and any integer $N \ge 1$, the extreme interval discrepancy in base $b$ of the first $N$ shifts of $x$ is
  $$
  D_N(x; b) = \sup_{0 \le u < v \le 1} \left| \frac{\#\{0 \le n < N : \{b^n x\} \in [u, v)\}}{N} - (v - u) \right|,
  $$
  with $D^+(x; b) = \limsup_{N \to \infty} D_N(x; b)$ and $D^-(x; b) = \liminf_{N \to \infty} D_N(x; b)$. For a shift $y \in \mathbb{R}$ and block length $L \ge 1$, the **local $L$-step discrepancy** is $D_L(y; b)$ (the same extreme interval discrepancy on the $L$-point sample $\{b^n y\}$, $0 \le n < L$). Note the universal floor $D_L(y; b) \ge 1/L$ for every $y \in \mathbb{R}$ and $L \ge 1$, obtained by shrinking a half-open interval onto a single sample point. A real number $x$ is **normal** in base $b$ if $D_N(x; b) \to 0$, and **absolutely normal** if it is normal in every integer base $b \ge 2$.
* **Continued fractions and Diophantine approximation.** For a finite or infinite regular continued fraction $x = [0; a_1, a_2, \ldots]$ ($a_j \in \mathbb{Z}_{\ge 1}$), write $p_n / q_n = [0; a_1, \ldots, a_n]$ for its convergents ($p_{-1} = 1, p_0 = 0, q_{-1} = 0, q_0 = 1$). For a finite word $\mathbf{a} = (a_1, \ldots, a_n)$, write
  $$
  M_{\mathbf{a}} = \begin{pmatrix} 0 & 1 \\ 1 & a_1 \end{pmatrix} \cdots \begin{pmatrix} 0 & 1 \\ 1 & a_n \end{pmatrix} = \begin{pmatrix} p_{n-1} & p_n \\ q_{n-1} & q_n \end{pmatrix}, \qquad T_{\mathbf{a}}(y) = \frac{p_n + p_{n-1} y}{q_n + q_{n-1} y}, \qquad I_{\mathbf{a}} = T_{\mathbf{a}}([0, 1]).
  $$
  For a rational $u \in (0, 1)$, let $A(u) = \max_{1 \le i \le n} a_i$ denote the maximum partial quotient of its canonical expansion ($a_n \ge 2$). For $M \ge 2$, let $F_M = \{[0; a_1, a_2, \ldots] : 1 \le a_n \le M \text{ for all } n \ge 1\}$. A real number $x$ is **badly approximable** if $\inf_{q \ge 1} q \|q x\| > 0$ (equivalently, its partial quotients are bounded). Its **irrationality exponent** is $\mu(x) = \sup\{\mu : \|qx\| < q^{1 - \mu} \text{ for infinitely many } q \ge 1\}$.
* **Kloosterman sums.** For integers $u, v$ and $q \ge 1$,
  $$
  S(u, v; q) = \sum_{\substack{x \bmod q \\ \gcd(x, q) = 1}} e\!\left(\frac{u x + v \bar{x}}{q}\right), \qquad x \bar{x} \equiv 1 \pmod q.
  $$
* **All-prime denominator support.** A specified series $\sum_{n \ge 1} \gamma_n b^{-n}$ has **all-prime denominator support** if every prime $\ell \nmid b$ eventually divides the reduced denominator of every shifted prefix $\sum_{n \le N} \gamma_n b^{N - n}$.

### Summary of results, evidence labels, and standing objectives

Per `docs/research-objectives.md` (rule 4), each proved result carries a single proof label (`Paper proof` or `Finite certificate`); published theorems used inside a proof are listed as **inputs**, unproved hypotheses are labeled `Conditional`, and open problems are labeled `Open`. Companion finite verification checks are recorded in §6.

| Item | Result | Evidence label & inputs | Objectives (`docs/research-objectives.md`) |
| --- | --- | --- | --- |
| **Theorem 1.1** | Low-residue-locked & aggregate-denominator-locked single-packet obstruction at $d \ge 2$: fixing all packet innovations, denominators, low residues mod $p^h$, scaled phases, aggregate difference denominators, and tails still realizes every base-$b$ word of length $L \le \min(tK, \lfloor (e - h) \log_b p \rfloor)$ at the packet start (local limitation; does not build a global multi-packet counter-model) | `Paper proof` | **Objective 4** (local single-packet limitation) |
| **Theorem 1.2** | (1) Scaled lag-$\delta$ difference equidistribution on full windows $[M, M+G)$ ($1 \le \delta \le G/2$) with discrepancy $O_{p,B}(p^{2w+\ell-h} + p^k/G)$; (2) flagship-cube consecutive selected-arrival $3$-adic extra cancellation ($[1, 2, 4, 11, 31]$ for $k = 3, \ldots, 7$) | (1) `Paper proof`; (2) `Finite certificate` | **Objective 3** (quantifying distributions) |
| **Theorem 1.3** | (1) Exact iff characterization of one-gap + low-residue certificates excluding $Q X \in \mathbb{Z}$ via $Q' = Q/\gcd(Q, B^M)$; (2) barrier on sublogarithmic gap envelopes under the depth hypothesis on the gap starts; (3) sufficient cubic gap thresholds for arbitrary ($\frac{s+1/3}{\log B}$), mild/abundant ($\frac{s}{\log B}$), and residue-boosted Ghidelli gaps | (1)–(2) `Paper proof` (conditional Ghidelli illustration uses input Ghidelli arXiv:1910.05076v1); (3) `Conditional` (third item uses input Ghidelli arXiv:1910.05076v1); irrationality of $C_1(3)^3$: `Open` | **Objective 3**, **Objective 4** |
| **Lemma 2.1** | Self-contained elementary fourth-moment Kloosterman bound $\lvert S(u,v;q)\rvert \le 2\tau(q)\gcd(u,v,q)^{1/4} q^{3/4}$ and log-free modular-hyperbola rectangle bound (plus Weil–Estermann $q^{1/2}$ refinement) | `Paper proof` (part 3 uses inputs Weil 1948, Estermann 1961) | Infrastructure for **Objectives 1, 3** |
| **Lemma 2.2** | Explicit computable block-i.i.d. Frostman measures on $F_M$: hand-checkable pure analytic $M = 100, L = 52$ ($s = 19/20$); exact integer certificates $M = 42, L = 4$ ($s = 18/19$), $M = 14, L = 4$ and $M = 30, L = 2$ ($s = 10/11$) | (1), (2), (4) `Paper proof`; (3) `Finite certificate` | Infrastructure for **Objectives 1, 3** |
| **Theorem 2.3** | Effective polynomial Fourier decay $\lvert \int e(\xi P(x))\,d\mu(x)\rvert \le \bar{C}(P)(1 + \lvert \xi \rvert)^{-\eta_{r, s, \rho}}$ for every nonconstant $P \in \mathbb{Q}[X]$ (and $X - S$) with explicit rational $\eta_{r, s, \rho} > 0$ and explicitly computable rational majorants $\bar{C}(P), \bar{\xi}_0(P)$ | `Paper proof` (Regime A, $s > 17/18$: no external inputs; Regime B, $s > 9/10$: inputs Weil 1948, Estermann 1961) | Infrastructure for **Objectives 1, 3** |
| **Theorem 2.4** | **Computable badly approximable polynomial-normal real numbers** $x \in F_M$ (every nonconstant $P(x) \in \mathbb{Q}[X]$ absolutely normal; $q\lVert qx\rVert > \frac{1}{M+2}$ for all $q \ge 1$): $M = 100$ pure paper, $M = 42$ via Lemma 2.2(3), $M = 14, 30$ via Lemma 2.2(3) and Weil–Estermann; plus computable badly approximable all-prime full-density series $Z = \sum_{n \ge 1}(d_n + 1/\ell_n) b^{-n}$ | `Paper proof` ($M = 100$: no external inputs or computer certificates; $M = 42$: uses Lemma 2.2(3) `Finite certificate`; $M = 14, 30$: uses Lemma 2.2(3) `Finite certificate` and inputs Weil 1948, Estermann 1961) | **Objective 1** (absolute normality), **Objective 3** (Diophantine optimality) |
| **Theorem 3.1** | Exact Continued-Fraction Folding Lemma: zero loss on prior partial quotients at $c = 1$ ($A(v) = \max(A(u), d_z - 1)$); factor-2-free bound $A(v) \le \max(\lfloor d_z/c \rfloor, c^2(A(u) + 2) - 1)$ for $c \ge 2$ | `Paper proof` | **Objective 3** |
| **Theorem 3.2** | Deterministic full-density all-prime polynomial-normal series $V(\mathbf{w})$ with genuinely local sub-shell coefficient variation ($2^{P_k}$ patterns per shell), complete monic-polynomial $p$-adic pole-depth proof, and arbitrarily slow folding loss $\lVert q V(\mathbf{w})\rVert \ge \frac{c}{q}\exp\{-C(\log\log(3q))\psi(\log\log(3q))\}$ | `Paper proof` | **Objective 1** (normality), **Objective 3** (uniform irrationality measure) |

Context: [Phase 23 note](../phase23/nonlinear-multivariate-and-denser-mu.md) · [Phase 24 note](../phase24/nonlinear-boundaries-and-approximation.md) · [Phase 22 short orbits](../phase22/short-orbits-and-irrationality.md) · [Exact verifier](../../scripts/phase25_nonlinear_approx.py).

---

## 1. Equality boundaries $d = r \in \{2, 3\}$: aggregate barriers and cubic irrationality thresholds (F1)

Phase 23 §2 proved that at density one of starts, fixing packet innovations, denominators, and future tails still realizes every logarithmic-length word as the incoming unit numerator varies freely modulo $p^e$. Phase 24 §2 then established an exact **low-residue law** $A_y \equiv B^{y-M} A_M \pmod{p^h}$ and scaled-phase equidistribution on $[M, M + G)$, raising the question whether locking the low residues, scaled phases, and aggregate consecutive-arrival difference denominators pins down local digit blocks at a packet start. Theorem 1.1 proves that it does **not**.

### Theorem 1.1 (Low-residue-locked and aggregate-denominator-locked single-packet obstruction — `Paper proof`)

Let $d \ge 2$, let $M \ge d$ be a shift with reduced prefix denominator $q_M = p^e$ ($e \ge 2$), and suppose that on the integer window $(M, M + K]$ every convolution coefficient $c_i$ has denominator dividing $p^{e - 1}$ (so $q_y = p^e$ identically for all $y \in [M, M + K]$). Fix any low-residue precision $1 \le h \le e - 1$. Keep all innovations $c_{M+1}, \ldots, c_{M+K}$ and all exact future real tails $T_{M+j}$ ($0 \le j \le K$) fixed, and replace $A_M$ by any of the $p^{e - h}$ high-digit lifts
$$
\widetilde{A}_M(u) = A_M + u p^h \pmod{p^e}, \qquad u \in \{0, 1, \ldots, p^{e - h} - 1\},
$$
propagating by $\widetilde{R}_y(u) = B^{y - M} \widetilde{R}_M(u) + \sum_{i = M+1}^y B^{y - i} c_i \pmod 1$ and $\widetilde{X}_y(u) = \widetilde{R}_y(u) + T_y \pmod 1$. Then for every $u \in \{0, \ldots, p^{e - h} - 1\}$:

1. **Exact denominator, low-residue, and scaled-phase invariance:** For every $y \in [M, M + K]$, $\operatorname{den}(\widetilde{R}_y(u)) = p^e = \operatorname{den}(R_y)$, $\widetilde{A}_y(u) \equiv A_y \pmod{p^h}$, and $\{p^{e - h} \widetilde{R}_y(u)\} = \{p^{e - h} R_y\}$.
2. **Exact aggregate-difference invariance:** For every pair $M \le u_1 < v_1 \le M + K$ such that the unperturbed propagated innovation $\sum_{i = u_1 + 1}^{v_1} B^{v_1 - i} c_i$ has $p$-adic denominator strictly smaller than $p^{e - v_p(B^{v_1 - u_1} - 1)}$ (which holds on all pairs in Phase 24's window $[M_a, M_a + G)$ with $v_p(B^{v_1 - u_1} - 1) < h$, and on a relative density $1 - o(1)$ of consecutive-arrival packets of Phase 23 §2 Theorem (A) for $d = 2$), the aggregate difference satisfies
   $$
   \operatorname{den}\bigl(\widetilde{R}_{v_1}(u) - \widetilde{R}_{u_1}(u)\bigr) = \operatorname{den}(R_{v_1} - R_{u_1}) = p^{e - v_p(B^{v_1 - u_1} - 1)},
   $$
   and its reduced numerator modulo $p^h$ is unchanged.
3. **Complete unconstrained single-packet word realization:** For every integer $L \ge 1$ with $b^L \le p^{e - h}$ and $L \le t K$, **every** base-$b$ word $w \in \{0, \ldots, b - 1\}^L$ occurs as the first $L$ base-$b$ digits of $\widetilde{X}_M(u)$ for at least one $u \in \{0, \ldots, p^{e - h} - 1\}$. In particular:
   * some lift $u$ produces the all-zero word $0^L$, which has zero digit transitions among its first $L$ digits and local $L$-step discrepancy satisfying
     $$
     D_L\bigl(\widetilde{X}_M(u); b\bigr) \ge \max_{1 \le m \le L}\!\left(\frac{L - m + 1}{L} - b^{-m}\right)
     $$
     (which is $\ge 1 - \frac{\lceil \log_b L \rceil}{L}$ for every $L \ge b$, tending to $1$ as $L \to \infty$; e.g., $\ge 47/72 \approx 0.6528$ for $b = 2, L = 9$ and $\ge 7/12 \approx 0.5833$ for $b = 2, L = 6$);
   * conversely, for any target point $x^* \in [0, 1)$ (subject to the universal floor $D_L(x^*; b) \ge 1/L$), some lift $u$ matches the first $L$ base-$b$ digits of $x^*$, and for $L \ge b$ its local $L$-step discrepancy satisfies $\bigl|D_L(\widetilde{X}_M(u); b) - D_L(x^*; b)\bigr| \le \frac{\lceil \log_b L \rceil + 1}{L}$.

**Proof.** Subtracting the recurrences gives, for every $y \in [M, M + K]$,
$$
\widetilde{R}_y(u) - R_y \equiv \frac{u B^{y - M}}{p^{e - h}} = \frac{u B^{y - M} p^h}{p^e} \pmod 1.
$$
Since $h \ge 1$ and $p \nmid A_y$, the numerator $\widetilde{A}_y(u) \equiv A_y + u B^{y - M} p^h \pmod{p^e}$ satisfies $\widetilde{A}_y(u) \equiv A_y \pmod{p^h}$, so $p \nmid \widetilde{A}_y(u)$ and $\operatorname{den}(\widetilde{R}_y(u)) = p^e$. Multiplying by $p^{e - h}$ kills $u B^{y - M} / p^{e - h}$ modulo $1$, giving $\{p^{e - h} \widetilde{R}_y(u)\} = \{p^{e - h} R_y\}$. This proves (1).

For (2), take $M \le u_1 < v_1 \le M + K$ and write $m = v_p(B^{v_1 - u_1} - 1) = w + v_p(v_1 - u_1)$ where $w = v_p(B - 1)$. By hypothesis, $R_{v_1} - R_{u_1} = (B^{v_1 - u_1} - 1) R_{u_1} + \sum_{i = u_1 + 1}^{v_1} B^{v_1 - i} c_i$ has exact reduced denominator $p^{e - m}$. Meanwhile, the perturbation
$$
\Delta_{u_1, v_1}(u) := \bigl(\widetilde{R}_{v_1}(u) - \widetilde{R}_{u_1}(u)\bigr) - (R_{v_1} - R_{u_1}) \equiv \frac{u B^{u_1 - M} (B^{v_1 - u_1} - 1)}{p^{e - h}} \pmod 1
$$
behaves in two cases:
* If $e - m < h$, then $m > e - h$, so $p^{e - h} \mid (B^{v_1 - u_1} - 1)$ and $\Delta_{u_1, v_1}(u) \equiv 0 \pmod 1$ is an integer; adding it leaves both the reduced denominator $p^{e - m}$ and the entire reduced numerator unchanged.
* If $e - m \ge h$, then $\Delta_{u_1, v_1}(u)$ has $p$-adic denominator dividing $p^{e - m - h}$, whose pole order is at least $h$ smaller than $e - m$; adding it shifts the reduced numerator over $p^{e - m}$ by a multiple of $p^h$, leaving both the exact reduced denominator $p^{e - m}$ and the reduced numerator modulo $p^h$ completely unchanged.

On Phase 24's window $[M_a, M_a + G)$, every innovation $c_i$ ($i > M_a$) satisfies $p^E c_i \equiv 0 \pmod{p^h}$, so the propagated innovation has pole order at most $E - h < E - m$ whenever $m < h$.

For (3), the exact tail recurrence $T_{y + 1} = B T_y - c_{y + 1}$ implies $\widetilde{X}_{M + j}(u) \equiv B^j (R_M + T_M + u / p^{e - h}) \pmod 1$. Because $h \ge 1$ already ensures coprimality to $p$ for **every** $u \in \{0, \ldots, p^{e - h} - 1\}$, the shifted phases $\{R_M + T_M + u / p^{e - h}\}$ form an exact uniform grid of spacing $p^{-(e - h)}$ on $[0, 1)$ (without the factor-of-$2$ unit-skipping loss of Phase 23's Packet Lemma). Every half-open base-$b$ cylinder $[k b^{-L}, (k + 1) b^{-L})$ of length $b^{-L} \ge p^{-(e - h)}$ therefore contains at least one grid point, realizing every word $w \in \{0, \ldots, b - 1\}^L$.

For the all-zero word $0^L$, if $y = \widetilde{X}_M(u)$ begins with $0^L$, then for every $1 \le m \le L$ and every $0 \le n \le L - m$ we have $\{b^n y\} \in [0, b^{-(L - n)}) \subseteq [0, b^{-m})$. Evaluating $D_L(y; b)$ on $[0, b^{-m})$ gives $D_L(y; b) \ge \frac{L - m + 1}{L} - b^{-m}$, and maximizing over $1 \le m \le L$ yields the stated bound (when $L \ge b$, choosing $m = \lceil \log_b L \rceil \in [1, L]$ gives $b^{-m} \le 1/L$ and hence $\ge 1 - \frac{\lceil \log_b L \rceil}{L}$). Finally, if $y, x^* \in [0, 1)$ share their first $L$ base-$b$ digits ($L \ge b$), set $m = \lceil \log_b L \rceil \in [1, L]$. For every $0 \le n \le L - m$, $\{b^n y\}$ and $\{b^n x^*\}$ lie in the same $b$-adic interval of length $b^{-(L - n)} \le 1/L$, so $|\{b^n y\} - \{b^n x^*\}| < 1/L$. For any $0 \le \alpha < \beta \le 1$, counting the $L - m + 1$ shifts $0 \le n \le L - m$ via the enlarged interval $[\max(0, \alpha - 1/L), \min(1, \beta + 1/L))$ and the shrunk interval $[\alpha + 1/L, \beta - 1/L)$ (when $\beta - \alpha > 2/L$; otherwise $(\beta - \alpha) - \text{count}/L \le 2/L \le (m + 1)/L$), together with the $m - 1$ remaining indices $n > L - m$, gives $|D_L(y; b) - D_L(x^*; b)| \le \frac{m + 1}{L}$. $\square$

**Local single-packet limitation (Objective 4) and scope.** On Phase 24's windows $[M_a, M_a + G)$ ($M_a = d p^{da}$, $E = sda$, $h = \lfloor \gamma a \rfloor$ with $0 < \gamma < s / (s + d)$), we have $h / E < \frac{1}{d(s + d)}$, leaving at least $\frac{5}{6} E$ ($d = 2, s = 1$) or $\frac{11}{12} E$ ($d = 3, s = 1$) free high base-$p$ digits, while $t(G - 1) \gg M_a^{1 - \gamma/s} \gg \log M_a \ge L$. Thus no **single-packet** deduction using only the packet innovations, denominators, low residues $A_y \bmod p^h$ ($h \le (1 - \epsilon) e_y$), scaled phases, aggregate difference denominators, and future tails can forbid **any** base-$b$ word of length $L = \lfloor (E - h) \log_b p \rfloor \gg \epsilon s \log_b M_a$ at the start of the packet, nor distinguish locally between a zero-transition block $0^L$ (of local discrepancy $\ge 1 - \lceil \log_b L \rceil / L$) and a low-discrepancy block. Pinning down digits at a packet start requires controlling the **top $O(1)$ base-$p$ digits** of $A_M$ (macroscopic real-circle phase information).

*Scope boundary:* Theorem 1.1 perturbs one packet at a time (changing the underlying real number globally across lifts) and does **not** construct a single real number simultaneously consistent with the listed invariants at all packets that attains $D^+ = 1$ or zero lower transition density. Because logarithmic-length blocks such as $0^L$ with $L \asymp \log M_a$ at shift $\asymp M_a$ are compatible with normal numbers, Theorem 1.1 is a rigorous **local single-packet limitation** (Objective 4) and does not by itself rule out multi-packet or global arguments for $D^+ < 1$ or positive lower transition density.

### Theorem 1.2 (Lag-$\delta$ scaled-phase equidistribution and flagship-cube selected-arrival cancellation)

Let $d \in \{2, 3\}$, $U = p^a$, $M = d U^d$, $E = s d a$, $v = \lceil h/s \rceil \le a + 1$, $G = p^{d(a - v + 1)}$, $w = v_p(B - 1)$, and $k = h - w > 0$. Fix any integer lag $1 \le \delta \le G / 2$ with $\ell = v_p(\delta)$ and suppose $k \ge w + \ell$ (equivalently $h \ge 2w + \ell$).

1. **Full-window lag-$\delta$ equidistribution (`Paper proof`):** Over all $y \in [M, M + G - \delta)$, the scaled lag-$\delta$ phase differences $\{p^{E - h}(R_{y + \delta} - R_y)\}$ are asymptotically uniformly distributed on $[0, 1)$ as $h \to \infty$ with $p^k / G \to 0$, with extreme interval discrepancy
   $$
   O_{p, B}\!\left(p^{2w + \ell - h} + \frac{p^k}{G}\right).
   $$
2. **Flagship-cube selected-arrival cancellation (`Finite certificate`):** On the selected fractional arrivals $m_j = 2 U^3 + (U + j)^3$ ($3 \nmid j$) of the flagship cube $(d, p, B) = (3, 3, 4)$ with $a \ge k$, consecutive unit indices $(j, j + 1)$ occur at $j = 1 + 3r$ with actual gap
   $$
   \Delta_j^{\mathrm{act}} := (U + j + 1)^3 - (U + j)^3 \equiv (j + 1)^3 - j^3 = 3 j^2 + 3 j + 1 = 7 + 27 r(r + 1) \pmod{3^k}
   $$
   (since $3^k \mid U$). Thus $\Delta_j^{\mathrm{act}} \equiv 1 \pmod 3$, so $v_3(4^{\Delta_j^{\mathrm{act}}} - 1) = w = 1$ has zero extra $3$-adic valuation loss. Nevertheless, the consecutive scaled-difference map $r \mapsto 4^{j^3}(4^{\Delta_j} - 1)/3 \pmod{3^k}$ ($0 \le r < 3^{k-1}$, where $\Delta_j = (j+1)^3 - j^3$) exhibits $3$-adic derivative damping: since $\Delta_j \equiv 7 \pmod{27}$ and $j^3 = 1 + 9r + 27(r^2 + r^3)$, modulo $3^4 = 81$ we have $4^{j^3}(4^{\Delta_j} - 1) \equiv 4(4^7 - 1) \pmod{81}$ identically in $r$ (collapsing all $9$ pairs to $1$ residue at $k = 3$), and modulo $3^5 = 243$ using $4^9 \equiv 1 - 54 \pmod{243}$, $4^{27} \equiv 1 + 81 \pmod{243}$, and $4^7 - 1 \equiv 102 \pmod{243}$ we obtain $4^{j^3}(4^{\Delta_j} - 1) \equiv 4(4^7 - 1) + 81(r^2 + 2r) \pmod{243}$, where $r^2 + 2r \bmod 3$ takes only $\{0, 2\}$ (collapsing all $27$ pairs to $2$ residues at $k = 4$). Across $k = 3, 4, 5, 6, 7$, the $3^{k-1} \in \{9, 27, 81, 243, 729\}$ consecutive pairs collapse to exactly $1, 2, 4, 11, 31$ distinct residues modulo $3^k$, respectively.

**Proof of (1).** By Phase 24 eq. (4), $A_{y + \delta} - A_y \equiv (B^\delta - 1) B^{y - M} A_M \pmod{p^h}$ throughout $[M, M + G - \delta)$. By lifting the exponent (LTE) for odd $p$, $B^\delta - 1 = p^{w + \ell} u_\delta$ with $p \nmid u_\delta$, while $B^{y - M}$ has exact period $p^k = p^{h - w}$ modulo $p^h$ and visits every element of $1 + p^w \mathbb{Z} / p^h \mathbb{Z}$ exactly once per period. Multiplying $1 + m p^w$ by $p^{w + \ell} A_M u_\delta$ yields
$$
A_{y + \delta} - A_y \equiv p^{w + \ell} A_M u_\delta + m (A_M u_\delta) p^{2w + \ell} \pmod{p^h}.
$$
Since $p \nmid A_M u_\delta$ and $h \ge 2w + \ell$, as $m$ runs over $0 \le m < p^{h - w}$ the product visits every lift modulo $p^h$ of its fixed residue modulo $p^{2w + \ell}$ with exact multiplicity $p^{w + \ell}$. Dividing by $p^h$ gives a uniform translated grid on $[0, 1)$ of spacing $p^{2w + \ell - h}$ on each complete period of length $p^k$, and the terminal incomplete period has relative weight at most $p^k / (G - \delta) \le 2 p^k / G$ (since $\delta \le G / 2$). $\square$

### Theorem 1.3 (Exact iff one-gap + low-residue certificate characterization and sufficient cubic gap thresholds)

For fixed shift $M \ge 1$, denominator $p^e$ ($e \ge 1$), low-residue congruence class $A_0 \bmod p^h$ ($0 \le h \le e$, with $p \nmid A_0$ when $h \ge 1$), and tail upper bound $T_{\max} > 0$, say that a real number $X'$ is **consistent with the information** $\mathcal{I} = (\operatorname{den}(R_M) = p^e,\; A_M \equiv A_0 \pmod{p^h},\; 0 < T_M \le T_{\max})$ if $B^M X' = N + \widetilde{A}_M / p^e + \widetilde{T}$ for some integer $N \in \mathbb{Z}$, some integer $\widetilde{A}_M \in [0, p^e)$ with $p \nmid \widetilde{A}_M$ and $\widetilde{A}_M \equiv A_0 \pmod{p^h}$, and some real $\widetilde{T} \in (0, T_{\max}]$. Say that $\mathcal{I}$ **excludes $Q X \in \mathbb{Z}$** if no real $X'$ consistent with $\mathcal{I}$ satisfies $Q X' \in \mathbb{Z}$.

1. **Exact characterization (`Paper proof`, Objective 4):** Fix $Q \ge 1$, and set
   $$
   Q' := \frac{Q}{\gcd(Q, B^M)}, \qquad g_0 := \gcd(Q', p^{e - h}) = \gcd(Q, p^{e - h})
   $$
   (the last equality holds because $p \nmid B$; note $Q' = Q$ if and only if $\gcd(Q, b) = 1$). Define
   $$
   r_{\min}(Q', A_0, h) := \begin{cases}
   g_0 & \text{if } h = 0, \\
   \text{the unique } r \in \{1, \ldots, g_0 p^h\} \text{ with } r \equiv -Q' A_0 \pmod{g_0 p^h} & \text{if } h \ge 1.
   \end{cases}
   $$
   Then the information $\mathcal{I} = (\operatorname{den}(R_M) = p^e,\; A_M \equiv A_0 \pmod{p^h},\; 0 < T_M \le T_{\max})$ excludes $Q X \in \mathbb{Z}$ **if and only if**
   $$
   Q' p^e T_{\max} < r_{\min}(Q', A_0, h). \tag{1.1}
   $$
   Specifically, if (1.1) holds, then no $X'$ consistent with $\mathcal{I}$ satisfies $Q X' \in \mathbb{Z}$; conversely, if $Q' p^e T_{\max} \ge r_{\min}(Q', A_0, h)$, there exist an integer $N \ge 0$, an integer lift $\widetilde{A}_M \equiv A_0 \pmod{p^h}$ with $p \nmid \widetilde{A}_M$, and a positive rational $\widetilde{T} = r_{\min}(Q', A_0, h) / (Q' p^e) \in (0, T_{\max}]$ such that $X' = (N + \widetilde{A}_M / p^e + \widetilde{T}) / B^M$ satisfies $Q X' \in \mathbb{Z}$. (For example, on $C_1(2)^2$ at $b = 2, B = 4, p = 3, s = 1, M = 10$, exact convolution gives $R_{10} = 202802/3$, $e = 1$, $T_{10} < 1/6$; at $h = 0, Q = 2, T_{\max} = 1/6$, one has $Q' = 2/\gcd(2, 4^{10}) = 1$, so $Q' p^e T_{\max} = 1/2 < 1 = r_{\min}$ genuinely excludes $2 X \in \mathbb{Z}$, whereas the unreduced product $Q p^e T_{\max} = 1$ would falsely fail.)
2. **Sublogarithmic-gap envelope barrier (`Paper proof`, Objective 4):** Let $(M_k)$ be any sequence of gap starts with gap lengths $g_k = o(\log M_k)$ such that the **depth hypothesis** $e_k \sim s \log_p M_k$ holds along $(M_k)$ and the low-residue precision satisfies $h_k \le (1 - \epsilon) e_k$ for a fixed $\epsilon > 0$. Then for every **gap-envelope tail bound** of the form $T_{\max, k} = H_{\mathrm{ub}, k} B^{-g_k}$ with $H_{\mathrm{ub}, k} \ge 1$, one has $r_{\min}(Q'_k, A_0, h_k) \le Q'_k p^{h_k}$ (where $Q'_k = Q / \gcd(Q, B^{M_k})$), so
   $$
   \frac{Q'_k p^{e_k} T_{\max, k}}{r_{\min}(Q'_k, A_0, h_k)} \ge p^{e_k - h_k} B^{-g_k} \ge p^{\epsilon e_k} B^{-g_k} = M_k^{\epsilon s - o(1)} \longrightarrow \infty.
   $$
   Hence no one-gap + low-residue certificate using such a gap envelope along $(M_k)$ can exclude even a single rational denominator $Q \ge 1$. In particular, for Ghidelli's unconditional mild-gap starts (input: Ghidelli arXiv:1910.05076v1, with $H_{\mathrm{ub}, k} = 60(\log T_k)^C \ge 1$ and $K_k \gg \sqrt{T_k}/(\log T_k)^2$), this barrier applies **conditionally on** both $K_k = o(\log M_k)$ and $e_k \sim s \log_p M_k$ holding on those starts.
3. **Sufficient cubic gap thresholds for $C_s(3)^3$ (Objective 3):**
   * *(Arbitrary three-cube gaps, `Conditional`):* If $\mathcal{S}_3^+ = \{x^3 + y^3 + z^3 : x, y, z \ge 1\}$ has infinitely many gaps $[M_k + 1, M_k + g_k]$ with $\limsup_{k \to \infty} g_k / \log M_k > \frac{s + 1/3}{\log B}$ (for flagship $b = 2, p = 3, s = 1$: $\frac{2}{3 \log 2} \approx 0.9618$), then $C_s(3)^3$ is irrational.
   * *(Mild or abundant three-cube gaps, `Conditional`):* If either (i) there are infinitely many gaps $[M_k + 1, M_k + g_k]$ with mild post-gap mass $H_{M_k} = M_k^{o(1)}$ and $\limsup_{k \to \infty} g_k / \log M_k > \frac{s}{\log B}$, or (ii) there exists $\varepsilon > 0$ such that for infinitely many dyadic scales $N$, $[N/2, N]$ contains at least $A_N \ge N^{1 - o(1)}$ pairwise disjoint maximal gaps $[M_k + 1, M_k + g_k]$, **each** of length $g_k > \left(\frac{s}{\log B} + \varepsilon\right) \log N$, then $C_s(3)^3$ is irrational (for flagship $b = 2, p = 3, s = 1$, the threshold is $\frac{1}{2 \log 2} \approx 0.7213$).
   * *(Residue-boosted criterion on Ghidelli's unconditional mild gaps, `Conditional`; input: Ghidelli arXiv:1910.05076v1):* Let $M_k = n_k - 1 < N_k$ be Ghidelli's unconditional mild-gap starts associated to parameters $T_k \to \infty$ ($\log N_k \asymp T_k$, gap length $K_k \gg \sqrt{T_k} / (\log T_k)^2$, and post-gap mass $H_{M_k} \le 60(\log T_k)^C$). If for every $Q \ge 1$,
     $$
     \limsup_{k \to \infty} \frac{\{-Q R_{M_k}\} B^{K_k}}{(\log T_k)^C} = \infty
     $$
     (in particular, if $\limsup_{k \to \infty} \{-Q R_{M_k}\} > 0$ for every $Q \ge 1$, since $B^{K_k} / (\log T_k)^C \to \infty$ unconditionally), then $C_s(3)^3$ is irrational for **every** $s \ge 1, p, b$.

**Proof.** For (1), write $G_B = \gcd(Q, B^M)$, $Q' = Q / G_B$, and $B_0 = B^M / G_B$, so $\gcd(Q', B_0) = 1$. For any $X'$ consistent with $\mathcal{I}$, write $B^M X' = N + \varphi$ with $N \in \mathbb{Z}$ and $\varphi = \widetilde{A}_M / p^e + \widetilde{T}$. Then $Q X' = Q'(N + \varphi) / B_0$. If $Q X' \in \mathbb{Z}$, then $Q'(N + \varphi) \in \mathbb{Z}$, forcing $Q' \varphi \in \mathbb{Z}$. Conversely, if $Q' \varphi = k \in \mathbb{Z}$, then since $\gcd(Q', B_0) = 1$ there exists a nonnegative integer $N \in [0, B_0)$ solving $Q' N \equiv -k \pmod{B_0}$, for which $Q X' = (Q' N + k)/B_0 \in \mathbb{Z}$. Thus $\mathcal{I}$ excludes $Q X \in \mathbb{Z}$ if and only if no valid pair $(\widetilde{A}_M, \widetilde{T})$ satisfies $Q'(\widetilde{A}_M / p^e + \widetilde{T}) \in \mathbb{Z}$.

As $u$ runs over $\{0, \ldots, p^{e - h} - 1\}$, the residues $-Q'(A_0 + u p^h) \pmod{p^e}$ traverse the exact coset $-Q' A_0 + g_0 p^h \mathbb{Z} / p^e \mathbb{Z}$. When $h \ge 1$, every lift $\widetilde{A}_M = A_0 + u p^h$ automatically satisfies $p \nmid \widetilde{A}_M$, and the smallest positive integer in this coset is precisely $r_{\min}(Q', A_0, h) \in \{1, \ldots, g_0 p^h\}$. When $h = 0$, write $Q' = p^v Q''$ with $p \nmid Q''$. If $v \ge e$, then $g_0 = p^e$, every unit $\widetilde{A}_M$ has $-Q' \widetilde{A}_M \equiv 0 \pmod{p^e}$, and the smallest positive lattice value is $p^e = g_0$. If $0 \le v < e$, then $g_0 = p^v$, and solving $-Q' \widetilde{A}_M \equiv p^v \pmod{p^e}$ reduces to $-Q'' \widetilde{A}_M \equiv 1 \pmod{p^{e - v}}$, whose unique solution automatically satisfies $p \nmid \widetilde{A}_M$. In all cases, $Q'(\widetilde{A}_M / p^e + \widetilde{T}) \in \mathbb{Z}$ with $\widetilde{T} > 0$ requires $Q' p^e \widetilde{T} \ge r_{\min}(Q', A_0, h)$, and equality is achieved at $\widetilde{T} = r_{\min}(Q', A_0, h) / (Q' p^e) \le T_{\max}$ precisely when $Q' p^e T_{\max} \ge r_{\min}(Q', A_0, h)$.

For (2), any gap envelope $T_{\max, k} = H_{\mathrm{ub}, k} B^{-g_k}$ with $H_{\mathrm{ub}, k} \ge 1$ satisfies $T_{\max, k} \ge B^{-g_k}$. Together with $r_{\min}(Q'_k, A_0, h_k) \le g_0 p^{h_k} \le Q'_k p^{h_k}$, the factor $Q'_k \ge 1$ cancels identically:
$$
\frac{Q'_k p^{e_k} T_{\max, k}}{r_{\min}(Q'_k, A_0, h_k)} \ge p^{e_k - h_k} B^{-g_k} \ge p^{\epsilon e_k} B^{-g_k} = M_k^{\epsilon s - o(1)} \longrightarrow \infty,
$$
so (1.1) fails for every fixed $Q \ge 1$ and all sufficiently large $k$.

For (3), the arbitrary-gap and mild-gap criteria follow from Phase 24 eq. (2) with $\alpha = 1/3$ and $\alpha = 0$ respectively. In the abundant-gap case (ii), every maximal gap $[M_k + 1, M_k + g_k]$ with $M_k \in [N/2, N]$ has right endpoint $r_k := M_k + g_k + 1 \le (\lfloor M_k^{1/3} \rfloor + 1)^3 + 2 \le 2N$ for all large $N$, and because the maximal gaps are pairwise disjoint, their right endpoints $r_k \le 2N$ are pairwise distinct. Split each post-gap mass $H_{M_k} = \sum_{j \ge 0} c_{r_k + j} B^{-j}$ into $r_k + j \le 3N$ and $r_k + j > 3N$. For $m = r_k + j \le 3N$, each integer $m$ appears at most once per fixed offset $j \ge 0$; for $r_k + j > 3N$, we have $j > N$ and trivially $c_{r_k + j} \le r_k + j \le 2N + j$. Therefore
$$
\sum_{k = 1}^{A_N} H_{M_k} \le \frac{B}{B - 1} \sum_{m \le 3N} c_m + \sum_{k = 1}^{A_N} \sum_{j > N} (2N + j) B^{-j} \le \frac{B}{B - 1} \sum_{x^3 + y^3 + z^3 \le 3N} 1 + O_B(N^2 B^{-N}) = O_B(N).
$$
By Markov's inequality, at least $A_N / 2$ of these gaps satisfy $H_{M_k} \ll_B N / A_N = N^{o(1)} = M_k^{o(1)}$, and every surviving gap still satisfies $g_k > (\frac{s}{\log B} + \varepsilon)\log N \ge (\frac{s}{\log B} + \varepsilon)\log M_k$, reducing to case (i). Finally, for the residue-boosted criterion, if $Q X \in \mathbb{Z}$, then $Q B^{M_k} X = Q R_{M_k} + Q T_{M_k} \in \mathbb{Z}$ forces $\{-Q R_{M_k}\} = Q T_{M_k} \le 60 Q (\log T_k)^C B^{-K_k}$ once the right-hand side is $< 1$, contradicting the limsup assumption. $\square$

**Remark (Honest status of $C_1(3)^3$ — `Open`).** Even for the unweighted cubic theta series $\theta_3(B^{-1}) = \sum_{i \ge 1} B^{-i^3}$ ($s = 0$, where $q_M \equiv 1$), irrationality of $\theta_3(B^{-1})^3$ was established by Ghidelli (arXiv:1910.05076v1, building on the cubic gap theorem in Ghidelli 2020, JLMS) via sublogarithmic mild gaps of length $\gg \sqrt{T} / (\log T)^2$. For $s \ge 1$, the prefix denominator satisfies $q_M \ge M^{s - o(1)}$ at density $1$ of all $M$ (Phase 21 Prop. D), though exact finite drops occur (such as $q_{1268} = 1$ in the flagship cube verified in §6); density-one growth does not by itself establish $e_k \sim s \log_p M_k$ on Ghidelli's sparse mild-gap starts, so the application of Theorem 1.3(2)'s barrier to those starts is conditional on the depth hypothesis (and $K_k = o(\log M_k)$) holding along them. Irrationality of $C_1(3)^3$ (and of $C_s(3)^3$ for all $s \ge 1$) remains **Open**.

---

## 2. Computable badly approximable polynomial-normal numbers (F2)

We resolve the open problem of Phase 24 §4 (whether one can **compute** a real number $x$ with **bounded partial quotients** such that every nonconstant $P(x) \in \mathbb{Q}[X]$ is absolutely normal). Our proof has four completely explicit components: (1) an elementary Kloosterman / modular-hyperbola rectangle bound (with a tighter Weil–Estermann variant); (2) computable block-i.i.d. Frostman measures $\mu$ on $F_M$; (3) effective polynomial Fourier decay for every nonlinear polynomial pushforward $P_* \mu$ with explicit rational exponents and computable rational majorants; and (4) a discontinuity-free $L^2$ potential-function nested-cylinder selection algorithm using only finite rational arithmetic.

### Lemma 2.1 (Explicit Kloosterman and modular-hyperbola rectangle bounds)

1. **Elementary Kloosterman bound (`Paper proof`, zero external inputs):** For every positive integer $q \ge 1$ and all integers $u, v$,
   $$
   |S(u, v; q)| \le 2 \, \tau(q) \, \gcd(u, v, q)^{1/4} \, q^{3/4}. \tag{2.1}
   $$
2. **Log-free modular-hyperbola rectangle bound (`Paper proof`):** For every integer $q \ge 1$ and any integer intervals $I, J \subseteq [1, q]$ of cardinalities $L_1, L_2 \ge 1$,
   $$
   \#\bigl\{(p, q') \in I \times J : p q' \equiv -1 \pmod q\bigr\} \le \frac{16 L_1 L_2}{q} + 120 \, \tau(q) \, q^{3/4}. \tag{2.2}
   $$
3. **Weil–Estermann refinement (`Paper proof`; inputs: Weil 1948, Estermann 1961):** Substituting Estermann's bound $|S(u, v; q)| \le \tau(q) \gcd(u, v, q)^{1/2} q^{1/2}$ replaces (2.2) by
   $$
   \#\bigl\{(p, q') \in I \times J : p q' \equiv -1 \pmod q\bigr\} \le \frac{16 L_1 L_2}{q} + 90 \, \tau(q) \, q^{1/2}. \tag{2.3}
   $$

**Proof.**
*Step 1: Prime moduli $q = p$ in (2.1).* If $p \mid \gcd(u, v)$, then $|S(u, v; p)| = p - 1 < p = \gcd(u, v, p)^{1/4} p^{3/4}$. If $p$ divides exactly one of $u, v$, then $S(u, v; p)$ is a Ramanujan sum of modulus $1 \le 2 p^{3/4}$. Suppose $p \nmid u$ and $p \nmid v$. For $p = 2$, $|S(1, 1; 2)| = 1 \le 2 \cdot 2^{3/4}$. For odd $p \ge 3$, orthogonality gives
$$
\sum_{a, b \in \mathbb{F}_p} |S(a, b; p)|^4 = p^2 \cdot \#\Bigl\{(x_1, x_2, x_3, x_4) \in (\mathbb{F}_p^\times)^4 : x_1 + x_2 = x_3 + x_4,\; x_1^{-1} + x_2^{-1} = x_3^{-1} + x_4^{-1}\Bigr\}.
$$
Write $s = x_1 + x_2 = x_3 + x_4$. If $s = 0$, then $x_2 = -x_1$ and $x_4 = -x_3$ automatically solve the second equation, giving $(p - 1)^2$ solutions. If $s \ne 0$, then $s / (x_1 x_2) = s / (x_3 x_4)$ forces $x_1 x_2 = x_3 x_4$, so $\{x_3, x_4\} = \{x_1, x_2\}$: the diagonal $x_1 = x_2$ contributes $p - 1$ solutions and $x_1 \ne x_2$ ($x_2 \ne -x_1$) contributes $2(p - 1)(p - 3)$ solutions. The exact solution count is $(p - 1)^2 + (p - 1) + 2(p - 1)(p - 3) = 3(p - 1)(p - 2)$. As $t$ varies over $\mathbb{F}_p^\times$, the $p - 1$ pairs $(t u, t^{-1} v)$ are pairwise distinct and satisfy $S(tu, t^{-1} v; p) = S(u, v; p)$. Therefore
$$
(p - 1) |S(u, v; p)|^4 \le 3 p^2 (p - 1)(p - 2) \implies |S(u, v; p)| \le 3^{1/4} p^{3/4} < 2 p^{3/4}.
$$

*Step 2: Prime powers $q = p^k$ ($k \ge 2$) and CRT.* Let $p^r = \gcd(u, v, p^k)$. If $r = k$, $|S(0, 0; p^k)| = \varphi(p^k) \le p^k = \gcd(u,v,p^k)^{1/4} p^{3k/4}$. If $1 \le r < k$, reducing modulo $p^{k - r}$ gives $S(u, v; p^k) = p^r S(u/p^r, v/p^r; p^{k - r})$, and $p^r (p^{k-r})^{3/4} = p^{r/4} p^{3k/4}$, reducing to $r = 0$. Now assume $\gcd(u, v, p) = 1$ and $k \ge 2$. Set $m = \lfloor k/2 \rfloor \ge 1$ and write $x = x_0 + p^{k - m} y$ ($x_0 \in (\mathbb{Z}/p^{k - m}\mathbb{Z})^\times$, $y \bmod p^m$). Since $2(k - m) \ge k$, $(x_0 + p^{k-m} y)^{-1} \equiv x_0^{-1} - x_0^{-2} p^{k-m} y \pmod{p^k}$, so
$$
S(u, v; p^k) = \sum_{x_0 \in (\mathbb{Z}/p^{k-m}\mathbb{Z})^\times} e\!\left(\frac{u x_0 + v x_0^{-1}}{p^k}\right) \sum_{y \bmod p^m} e\!\left(\frac{(u - v x_0^{-2}) y}{p^m}\right).
$$
The inner sum equals $p^m$ when $u x_0^2 \equiv v \pmod{p^m}$ and $0$ otherwise. If $p \mid u$ or $p \mid v$, no unit $x_0$ solves this congruence, so $S = 0$. Otherwise $x_0^2 \equiv v u^{-1} \pmod{p^m}$ has at most $2$ solutions modulo $p^m$ for odd $p$ (cyclicity of $(\mathbb{Z}/p^m\mathbb{Z})^\times$) and at most $4$ solutions modulo $2^m$ for $p = 2$. Each lifts to $p^{k - 2m}$ values modulo $p^{k - m}$, so
$$
|S(u, v; p^k)| \le c_p p^{k - m} \le c_p p^{(k + 1)/2} \le c_p p^{3k/4} \qquad (c_p = 2 \text{ for odd } p,\; c_2 = 4),
$$
using $(k + 1)/2 \le 3k/4$ for all $k \ge 2$. By CRT twisted multiplicativity $S(u, v; q_1 q_2) = S(u \bar{q}_2, v \bar{q}_2; q_1) S(u \bar{q}_1, v \bar{q}_1; q_2)$ ($\gcd(q_1, q_2) = 1$) and $2^{\omega(q)} \le \tau(q)$, multiplying over prime powers proves (2.1) (the extra factor $2$ at $p = 2$ supplies the leading $2$).

*Step 3: Log-free trapezoid majorant for (2.2) and (2.3).* For an integer interval $I = [a, a + L - 1]$ of length $L \in [1, q]$, define a majorant $B_I : \mathbb{Z}/q\mathbb{Z} \to [0, 1]$ with $B_I \ge \mathbf{1}_I$ as follows. If $L \ge q/4$, set $B_I \equiv 1$, whose discrete Fourier transform $\widehat{B_I}(u) = \sum_{x \bmod q} B_I(x) e(-ux/q)$ has $\widehat{B_I}(0) = q \le 4 L$ and $\widehat{B_I}(u) = 0$ for $u \not\equiv 0 \pmod q$. If $1 \le L < q/4$, define the trapezoid convolution
$$
B_I(x) = \frac{1}{L} \sum_{y = -L + 1}^0 \mathbf{1}_{[a, a + 2L - 1]}(x - y) \quad (\text{mod } q).
$$
Since $3L - 1 < q$, there is no wraparound: $0 \le B_I \le 1$, $B_I \equiv 1$ on $I$, $\widehat{B_I}(0) = 2 L \le 4 L$, and by Jordan's inequality $|\sin(\pi u / q)| \ge 2|u|/q$ for $1 \le |u| \le q/2$,
$$
|\widehat{B_I}(u)| = \frac{1}{L} \left|\frac{\sin(2\pi u L / q)}{\sin(\pi u / q)}\right| \left|\frac{\sin(\pi u L / q)}{\sin(\pi u / q)}\right| \le \min\!\left(2 L,\; \frac{q^2}{4 L u^2}\right).
$$
For any divisor $d \mid q$, writing $u = d u'$ and splitting at $U_0 = \lfloor q / (2 \sqrt{2} L d) \rfloor$ gives:
* if $U_0 \ge 1$, then $U_0 \ge q / (4 \sqrt{2} L d)$, so $\sum_{1 \le |u'| \le q/(2d)} |\widehat{B_I}(d u')| \le 4 L U_0 + \frac{q^2}{2 L d^2 U_0} \le 3\sqrt{2} \frac{q}{d} < \frac{5q}{d}$;
* if $U_0 = 0$, then $2 L d > q / \sqrt{2}$, so $\sum_{1 \le |u'| \le q/(2d)} |\widehat{B_I}(d u')| \le \frac{q^2}{2 L d^2} \frac{\pi^2}{6} < \frac{\sqrt{2}\pi^2}{6} \frac{q}{d} < \frac{5q}{d}$.

Now expand $\#\{(p, q') \in I \times J : p q' \equiv -1 \pmod q\} \le \sum_{x \in (\mathbb{Z}/q\mathbb{Z})^\times} B_I(x) B_J(-\bar{x})$ by discrete Fourier inversion:
$$
\frac{1}{q^2} \sum_{u, v \bmod q} \widehat{B_I}(u) \widehat{B_J}(v) S(u, -v; q).
$$
The $u = v = 0$ term is $\frac{\widehat{B_I}(0) \widehat{B_J}(0) \varphi(q)}{q^2} \le \frac{16 L_1 L_2}{q}$. The axis terms ($u = 0, v \ne 0$ and $v = 0, u \ne 0$) use the Ramanujan bound $|S(0, -v; q)| \le \gcd(v, q)$: summing over $d = \gcd(v, q) \mid q$ yields at most $20 \tau(q)$ combined. For $u, v \ne 0$ (which vanishes unless both $L_1, L_2 < q/4$), grouping by $d = \gcd(u, v, q) \mid q$ and applying (2.1) yields at most
$$
\frac{2 \tau(q) q^{3/4}}{q^2} \sum_{d \mid q} d^{1/4} \left(\frac{5 q}{d}\right)^2 = 50 \tau(q) q^{3/4} \sum_{d \mid q} d^{-7/4} \le 50 \zeta(7/4) \tau(q) q^{3/4} < 100 \tau(q) q^{3/4},
$$
since $\zeta(7/4) \le \sum_{n=1}^5 n^{-7/4} + \frac{4}{3} \cdot 5^{-3/4} < 2$. Adding the $\le 20 \tau(q)$ axis terms gives (2.2). For (2.3), Estermann's bound gives $25 \zeta(3/2) \tau(q) q^{1/2} + 20 \tau(q) < (25 \cdot 2.8 + 20) \tau(q) q^{1/2} = 90 \tau(q) q^{1/2}$, since $\zeta(3/2) \le \sum_{n=1}^{25} n^{-3/2} + 2 \cdot 25^{-1/2} < 2.8$. $\square$

### Lemma 2.2 (Computable block-i.i.d. Frostman measures on $F_M$)

Let $M \ge 2$, let $L \ge 2$ be an **even** integer, and let $s \in (0, 1)$ be rational. Define the block partition sum
$$
\Sigma(M, L, s) := \sum_{\mathbf{u} \in \{1, \ldots, M\}^L} \bigl(q_L(\mathbf{u}) + p_L(\mathbf{u})\bigr)^{-2s}.
$$
1. **Existence of explicit rational weights (`Paper proof`):** If $\Sigma(M, L, s) > 1$, there exist explicit positive rational weights $\{p_{\mathbf{u}} : \mathbf{u} \in \{1, \ldots, M\}^L\}$ with $\sum_{\mathbf{u}} p_{\mathbf{u}} = 1$ and $p_{\mathbf{u}} \le (q_L(\mathbf{u}) + p_L(\mathbf{u}))^{-2s}$ for every $\mathbf{u}$.
2. **Hand-checkable pure-analytic parameter existence (`Paper proof`):** Writing $\phi = (1 + \sqrt{5})/2$, one has $\Sigma(M, L, s) \ge 2^{-2s} \phi^{2(1-s)(L-1)} (1 - \frac{2}{M+2})^L$ for all $M, L, s$. In particular, for $s = 19/20$ ($2s = 19/10$), $M = 100$ and $L = 52$ satisfy $\Sigma(100, 52, 19/20) > 1$ purely analytically by hand (with zero computer certificates).
3. **Sharp finite integer certificates (`Finite certificate`):** Exact integer $Q$-th root arithmetic certifies:
   * $\Sigma(42, 4, 18/19) > 1.0185 > 1$ (for $s = 18/19 > 17/18$, zero-external-input regime);
   * $\Sigma(14, 4, 10/11) > 1.0147 > 1$ and $\Sigma(30, 2, 10/11) > 1.0257 > 1$ (for $s = 10/11 > 9/10$, Weil–Estermann regime).
4. **Exact structural and Frostman properties (`Paper proof`):** Let $\mu$ be the pushforward to $F_M$ of the i.i.d. product measure on $(\{1, \ldots, M\}^L)^{\mathbb{N}}$ with weights $p_{\mathbf{u}}$, and set $B_{M, L} = \max_{\mathbf{u}} (q_L(\mathbf{u}) + p_L(\mathbf{u})) \le 2(M + 1)^L$. Then:
   * Every block word $\mathbf{a} = \mathbf{u}_1 \cdots \mathbf{u}_m$ has **even** length $m L$, so $T_{\mathbf{a}}$ is strictly increasing, $\det(M_{\mathbf{a}}) = +1$ (hence $p(\mathbf{a}) q'(\mathbf{a}) \equiv -1 \pmod{q(\mathbf{a})}$), and the pair $(p(\mathbf{a}), q(\mathbf{a}))$ determines $\mathbf{a}$ **uniquely**.
   * Submultiplicativity $q(\mathbf{u}_1 \cdots \mathbf{u}_m) \le \prod_{j=1}^m (q_L(\mathbf{u}_j) + p_L(\mathbf{u}_j))$ yields $w(\mathbf{a}) := \mu(I_{\mathbf{a}}) \le q(\mathbf{a})^{-2s}$.
   * For every $R > 1$, the prefix stopping set $\mathcal{W}(R) = \{\mathbf{a} = \mathbf{u}_1 \cdots \mathbf{u}_m : q(\mathbf{a}) \ge R > q(\mathbf{u}_1 \cdots \mathbf{u}_{m-1})\}$ is a finite partition of $F_M$ satisfying $R \le q(\mathbf{a}) < B_{M, L} R$, $w(\mathbf{a}) \le R^{-2s}$, $|\mathcal{W}(R)| \le 2 B_{M, L}^2 R^2$, and exact independence of $\mathbf{a} \sim \mu|_{\mathcal{W}(R)}$ and $y \sim \mu$ in $x = T_{\mathbf{a}}(y)$.
   * For every interval $I \subset [0, 1]$, $\mu(I) \le C_F |I|^s$ with $C_F = 2 B_{M, L}^2 + 2$.

**Proof.** For (1), let $2s = P/Q$ in lowest terms, choose a large integer $D$ so that $a_N := \lfloor (D^Q / N^P)^{1/Q} \rfloor \ge 1$ for all $N = q_L(\mathbf{u}) + p_L(\mathbf{u})$ and $T := \sum_{\mathbf{u}} a_{N(\mathbf{u})} > D$, and set $p_{\mathbf{u}} = a_{N(\mathbf{u})} / T \in \mathbb{Q}_{>0}$; then $p_{\mathbf{u}} < a_{N(\mathbf{u})} / D \le N(\mathbf{u})^{-2s}$.

For (2), by induction on depth $L$ (as in Phase 24 §3), the retained Lebesgue measure of $\bigcup_{\mathbf{u} \in \{1, \ldots, M\}^L} I_{\mathbf{u}}$ is at least $(1 - \frac{2}{M+2})^L$ (at each step a parent with ratio $y = q'/q \in [0, 1]$ retains fraction $\frac{M}{M + 1 + y} \ge \frac{M}{M + 2} = 1 - \frac{2}{M+2}$). Since $q_L(\mathbf{u}) + p_L(\mathbf{u}) \le 2 q_L(\mathbf{u})$ and $|I_{\mathbf{u}}| = \frac{1}{q_L(\mathbf{u})(q_L(\mathbf{u}) + q_{L-1}(\mathbf{u}))} \le \min(q_L(\mathbf{u})^{-2}, \phi^{-2(L-1)})$, we obtain
$$
\bigl(q_L(\mathbf{u}) + p_L(\mathbf{u})\bigr)^{-2s} \ge 2^{-2s} |I_{\mathbf{u}}|^s = 2^{-2s} |I_{\mathbf{u}}|^{s - 1} |I_{\mathbf{u}}| \ge 2^{-2s} \phi^{2(1-s)(L-1)} |I_{\mathbf{u}}|.
$$
Summing over $\mathbf{u} \in \{1, \ldots, M\}^L$ gives the analytic lower bound. To verify $M = 100, L = 52, s = 19/20$ purely by hand, raise $2^{-19/10} \phi^{51/10} (50/51)^{52} > 1$ to the tenth power: we need $\phi^{51} > 2^{19} (51/50)^{520}$. First, $5 \cdot 5^2 = 125 > 121 = 11^2 \implies \phi = (1 + \sqrt{5})/2 > 8/5$, so $\phi^{51} > 2^{153} / 5^{51}$. Second,
$$
e = \sum_{k=0}^\infty \frac{1}{k!} < 1 + 1 + \frac{1}{2} + \frac{1}{6} + \frac{1}{24} \sum_{j=0}^\infty \frac{1}{5^j} = \frac{8}{3} + \frac{5}{96} = \frac{261}{96} < \frac{11}{4},
$$
whence $e^2 < \frac{121}{16} = \frac{242}{32} < \frac{243}{32} = (\frac{3}{2})^5$, giving $e^{2/5} < \frac{3}{2}$ (and also $e^2 < 8 = 2^3$, giving $\log 2 > \frac{2}{3}$, used in Theorem 2.4). Therefore $(1 + \frac{1}{50})^{520} < e^{52/5} = e^{10} e^{2/5} < (\frac{11}{4})^{10} \cdot \frac{3}{2}$, so $2^{19}(51/50)^{520} < 3 \cdot 11^{10} / 4$. It remains to check $2^{155} > 3 \cdot 11^{10} \cdot 5^{51}$, i.e., $2 \cdot (128/121)^5 (128/125)^{17} > 3$ (since $1 + 7 \cdot 5 + 7 \cdot 17 = 155$). By Bernoulli's inequality,
$$
\left(1 + \frac{7}{121}\right)^5 > 1 + \frac{35}{121} > \frac{5}{4} \quad (140 > 121), \qquad \left(1 + \frac{3}{125}\right)^{17} > 1 + \frac{51}{125} > \frac{6}{5} \quad (51 > 25),
$$
and $2 \cdot \frac{5}{4} \cdot \frac{6}{5} = 3$, establishing $\Sigma(100, 52, 19/20) > 1$ completely by hand.

For (4), every rational in $(0, 1)$ has exactly one even-length regular continued fraction, giving uniqueness of $(p(\mathbf{a}), q(\mathbf{a}))$. Writing $M_{\mathbf{w} \mathbf{u}} = M_{\mathbf{w}} M_{\mathbf{u}}$ gives $q(\mathbf{w} \mathbf{u}) = q(\mathbf{w}) q_L(\mathbf{u}) + q'(\mathbf{w}) p_L(\mathbf{u}) \le (q_L(\mathbf{u}) + p_L(\mathbf{u})) q(\mathbf{w})$ since $0 \le q'(\mathbf{w}) \le q(\mathbf{w})$. Induction gives $q(\mathbf{a}) \le \prod (q_L(\mathbf{u}_j) + p_L(\mathbf{u}_j))$; raising to the negative power $-2s$ reverses the inequality to $\prod p_{\mathbf{u}_j} \le q(\mathbf{a})^{-2s}$. For $R > 1$, the empty word has $q(\emptyset) = 1 < R$ while $q(\mathbf{u}_1 \cdots \mathbf{u}_m) \ge \phi^{mL - 1} \to \infty$, so $\mathcal{W}(R)$ is a finite partition of $F_M$; every $\mathbf{a} \in \mathcal{W}(R)$ has $|I_{\mathbf{a}}| \ge \frac{1}{2 q(\mathbf{a})^2} \ge \frac{1}{2 B_{M, L}^2 R^2}$, and pairwise disjoint interiors yield $|\mathcal{W}(R)| \le 2 B_{M, L}^2 R^2$. For any interval $I \subset [0, 1]$ with $|I| < 1$, taking $R = |I|^{-1/2} > 1$ shows that at most $2 B_{M, L}^2 + 2$ cylinders of $\mathcal{W}(R)$ intersect $I$, each of mass $\le R^{-2s} = |I|^s$; for $|I| = 1$, $\mu(I) = 1 \le C_F \cdot 1^s$ trivially. $\square$

### Theorem 2.3 (Effective nonlinear polynomial Fourier decay for $P_* \mu$)

Let $\mu$ be a block-i.i.d. measure on $F_M$ from Lemma 2.2 with rational Frostman exponent $s \in (0, 1)$ and parameters $(M, L)$. Suppose either:
* **(Regime A — `Paper proof`, zero external inputs):** $s > 17/18$ (e.g., $s = 19/20$ with $M = 100, L = 52$, or $s = 18/19$ with $M = 42, L = 4$), using Lemma 2.1(2) with $\rho_{\mathrm{Klo}} = 3/4$ and $C_{\mathrm{Klo}} = 120$; or
* **(Regime B — `Paper proof`; inputs: Weil 1948, Estermann 1961):** $s > 9/10$ (e.g., $s = 10/11$ with $M = 14, L = 4$ or $M = 30, L = 2$), using Lemma 2.1(3) with $\rho_{\mathrm{Klo}} = 1/2$ and $C_{\mathrm{Klo}} = 90$.

Then for every integer degree $r \ge 1$ there exist an explicit rational exponent $\eta_{r, s, \rho} > 0$ (depending on $r$, $s$, and $\rho_{\mathrm{Klo}}$) and an **explicit algorithm** that, given $(M, L, s, \rho_{\mathrm{Klo}})$ and the rational coefficients of any nonconstant polynomial $P(X) = \sum_{j=0}^r c_j X^j \in \mathbb{Q}[X]$ (or $P(X) = X - S$ with $r = 1, c_1 = 1, M_P = 1, L_P = 0$), computes in finite rational arithmetic an integer threshold $\bar{\xi}_0(P) \ge 16$ and a rational majorant $\bar{C}(P) \in \mathbb{Q}_{>0}$ such that for every real $\xi$,
$$
\left|\int_0^1 e\bigl(\xi P(x)\bigr)\,d\mu(x)\right| \le \bar{C}(P) (1 + |\xi|)^{-\eta_{r, s, \rho}}. \tag{2.4}
$$

**Proof.** Set $B_0 := B_{M, L} \le 2(M + 1)^L$, $C_F := 2 B_0^2 + 2$, $c_* := |c_r| \in \mathbb{Q}_{>0}$, $M_P := \sum_{j=1}^r j |c_j| \in \mathbb{Q}_{>0}$, $\bar{M}_P := \max(1, M_P)$, $L_P := \sum_{j=2}^r j(j-1) |c_j| \in \mathbb{Q}_{\ge 0}$, and $S_1 := 2(M + 1) B_0 L_P \in \mathbb{Q}_{\ge 0}$.

Choose rational parameters $(\alpha, \beta, \theta)$ (with $\alpha, \beta > 0$, $\theta = 0$ when $r = 1$, and $\theta > 0$ when $r \ge 2$) satisfying the five strict rational inequalities
$$
2\alpha + 4\beta > 1, \qquad 2\alpha + 2\beta + \frac{3}{2}\theta < s, \qquad 1 - s - \frac{1 - \rho_{\mathrm{Klo}}}{2}\alpha + \frac{1}{2}\theta < 0, \qquad 4\alpha + 2\beta > 1, \qquad 2\alpha > \theta. \tag{2.5}
$$
Eliminating $\beta$ and $\theta$ shows that (2.5) is feasible if and only if $\frac{2(1 - s)}{1 - \rho_{\mathrm{Klo}}} < s - \frac{1}{2}$, i.e., $s > 17/18$ for $\rho_{\mathrm{Klo}} = 3/4$ and $s > 9/10$ for $\rho_{\mathrm{Klo}} = 1/2$ (note that the admissible interval collapses as $s$ approaches the threshold, so $\eta_{r, s, \rho}$ depends on $s$ as well as $r$ and $\rho_{\mathrm{Klo}}$). For any rational $s$ above the threshold, an explicit rational solution is given by taking the midpoints
$$
\alpha = \frac{1}{2}\!\left(\frac{2(1 - s)}{1 - \rho_{\mathrm{Klo}}} + s - \frac{1}{2}\right), \qquad \beta = \frac{1 + 2s - 6\alpha}{8}, \qquad \theta = \begin{cases} 0 & (r = 1), \\ \frac{1}{2}\min\!\bigl(\frac{2}{3}(s - 2\alpha - 2\beta),\; (1 - \rho_{\mathrm{Klo}})\alpha - 2(1 - s)\bigr) & (r \ge 2), \end{cases}
$$
which automatically satisfies all five inequalities in (2.5) (since $s > 9/10 \implies 4\alpha + 2\beta = (1 + 2s + 10\alpha)/4 > 6/5 > 1$). For the certified triples of Lemma 2.2, concrete simplified rational choices (with $\theta = 0$ when $r = 1$) are:
* $s = 19/20, \rho_{\mathrm{Klo}} = 3/4$: $\alpha = 21/50,\; \beta = 9/200,\; \theta = 1/1000$ (margins $(m_{\mathrm{lin}}, m_A, m_B) = (1/50, 37/2000, 1/500)$);
* $s = 18/19, \rho_{\mathrm{Klo}} = 3/4$: $\alpha = 43/100,\; \beta = 37/1000,\; \theta = 1/2000$ (margins $(1/125, 959/76000, 33/38000)$);
* $s = 10/11, \rho_{\mathrm{Klo}} = 1/2$: $\alpha = 19/50,\; \beta = 13/200,\; \theta = 1/500$ (margins $(1/50, 177/11000, 17/5500)$).

Define the strictly positive rational margins
$$
m_{\mathrm{lin}} := 2\alpha + 4\beta - 1, \qquad m_A := s - 2\alpha - 2\beta - \frac{3}{2}\theta, \qquad m_B := \frac{1 - \rho_{\mathrm{Klo}}}{2}\alpha - (1 - s) - \frac{1}{2}\theta,
$$
and define the explicit rational decay exponent separately for $r = 1$ and $r \ge 2$:
$$
\eta_{r, s, \rho} := \begin{cases}
\min\!\left\{m_{\mathrm{lin}},\; \frac{m_A}{2},\; \frac{m_B}{4}\right\} & \text{if } r = 1, \\[4pt]
\min\!\left\{m_{\mathrm{lin}},\; 2\alpha s,\; \frac{s\theta}{r - 1},\; \frac{m_A}{2},\; \frac{m_B}{4}\right\} & \text{if } r \ge 2.
\end{cases}
$$
Notice that (2.5) also implies two auxiliary strict inequalities: $2\alpha + 2\beta + \theta < s < 1$ (from the second inequality) and $\theta < (1 - \rho_{\mathrm{Klo}})\alpha < (1 + \rho_{\mathrm{Klo}})\alpha$ (from the third inequality).

Let $|\xi| \ge \bar{\xi}_0(P)$, where the explicit computable integer $\bar{\xi}_0(P) \ge 16$ is defined in Step 5 below. Set $R_1 = |\xi|^\alpha > 1$, $R_2 = |\xi|^\beta > 1$, $\Delta = R_2^2 = |\xi|^{2\beta}$, and $\delta = |\xi|^{-\theta}$ for $r \ge 2$ (while for $r = 1$, set $\delta = c_* = |c_1|$ and $\theta = 0$).

*Step 1: Excising critical points.* When $r = 1$, $P'(x) = c_1$ is constant with $|P'(x)| = \delta$; set $\widetilde{B}_\delta = \emptyset$ and $\mathcal{W}_1^* = \mathcal{W}_1 := \mathcal{W}(R_1)$, so zero cylinders are excised ($A_1(P) := 0$). When $r \ge 2$, the product formula $|P'(x)| = r c_* \prod_{i=1}^{r-1} |x - \rho_i|$ shows that $\{x \in [0, 1] : |P'(x)| < \delta\}$ is covered by $\widetilde{B}_\delta = \bigcup_{i=1}^{r-1} (\operatorname{Re}\rho_i - \rho, \operatorname{Re}\rho_i + \rho)$ with $\rho = (\delta / (r c_*))^{1/(r-1)}$. By Lemma 2.2(4), $\mu(\widetilde{B}_\delta) \le (r - 1) C_F (2\rho)^s$. Let $\mathcal{W}_1^* \subseteq \mathcal{W}_1$ consist of those $\mathbf{a} \in \mathcal{W}_1$ with $I_{\mathbf{a}} \cap \widetilde{B}_\delta = \emptyset$. Each of the at most $2(r - 1)$ endpoints of $\widetilde{B}_\delta$ can lie in at most **two** closed cylinders of $\mathcal{W}_1$ (since distinct cylinders have disjoint interiors), so at most $4(r - 1)$ cylinders meet an endpoint of $\widetilde{B}_\delta$. Thus the total $\mu$-measure of $\mathcal{W}_1 \setminus \mathcal{W}_1^*$ is at most
$$
\mu(\widetilde{B}_\delta) + 4(r - 1) R_1^{-2s} \le (r - 1) C_F \left(2 \left(\frac{|\xi|^{-\theta}}{r c_*}\right)^{\!1/(r-1)}\right)^{\!s} + 4(r - 1) |\xi|^{-2\alpha s} \le A_1(P) |\xi|^{-\eta_{r, s, \rho}},
$$
where $A_1(P) := (r - 1)\bigl(2 C_F \max(1, \frac{1}{r c_*}) + 4\bigr) \in \mathbb{Q}_{>0}$ (using $0 < s < 1$ and $0 < s/(r-1) < 1$). On every $\mathbf{a} \in \mathcal{W}_1^*$, $|P'(x)| \ge \delta$ throughout $I_{\mathbf{a}}$ and $P'$ has constant sign on $I_{\mathbf{a}}$.

*Step 2: Two-block decomposition and linearization.* By exact independence in Lemma 2.2(4) (valid since $R_1, R_2 > 1$), decompose $x = T_{\mathbf{a}}(y)$ ($\mathbf{a} \in \mathcal{W}_1$) and partition $y$ over $\mathcal{W}_2 = \mathcal{W}(R_2)$:
$$
\left|\int_0^1 e(\xi P(x))\,d\mu(x)\right| \le A_1(P) |\xi|^{-\eta_{r, s, \rho}} + \left|\sum_{\mathbf{b} \in \mathcal{W}_2} \sum_{\mathbf{a} \in \mathcal{W}_1^*} w(\mathbf{a}) \int_{I_{\mathbf{b}}} e\bigl(\xi P(T_{\mathbf{a}}(y))\bigr)\,d\mu(y)\right|.
$$
For each $\mathbf{b} \in \mathcal{W}_2$, let $y_{\mathbf{b}} = p(\mathbf{b}) / q(\mathbf{b})$ be the left endpoint of $I_{\mathbf{b}}$; since $\mathbf{b}$ has even length $\ge 2$ and digits $\le M$, $y_{\mathbf{b}} \in [\frac{1}{M+1}, 1]$ and $|y - y_{\mathbf{b}}| \le q(\mathbf{b})^{-2} \le R_2^{-2}$ on $I_{\mathbf{b}}$. For $f_{\mathbf{a}}(y) = P(T_{\mathbf{a}}(y))$, $|T_{\mathbf{a}}'(y)| \le R_1^{-2}$ and $|T_{\mathbf{a}}''(y)| = \frac{2 q'(\mathbf{a})}{(q(\mathbf{a}) + q'(\mathbf{a}) y)^3} \le 2 R_1^{-2}$, so $|f_{\mathbf{a}}''(y)| \le (L_P + 2 M_P) R_1^{-2}$. Linearizing $\xi f_{\mathbf{a}}(y)$ around $y_{\mathbf{b}}$ incurs total phase error at most
$$
E_{\mathrm{lin}} := \pi (L_P + 2 M_P) |\xi| R_1^{-2} R_2^{-4} \le A_2(P) |\xi|^{-\eta_{r, s, \rho}}, \qquad A_2(P) := 4(L_P + 2 M_P) \in \mathbb{Q}_{>0}
$$
(using $\pi < 4$ and $m_{\mathrm{lin}} \ge \eta_{r, s, \rho}$), leaving $\sum_{\mathbf{b} \in \mathcal{W}_2} S_{\mathbf{b}}$, where
$$
S_{\mathbf{b}} := \sum_{\mathbf{a} \in \mathcal{W}_1^*} w(\mathbf{a}) \left|\int_{I_{\mathbf{b}}} e(\Lambda_{\mathbf{a}, \mathbf{b}} y)\,d\mu(y)\right|, \qquad \Lambda_{\mathbf{a}, \mathbf{b}} := \frac{\xi \, P'\bigl(T_{\mathbf{a}}(y_{\mathbf{b}})\bigr)}{\bigl(q(\mathbf{a}) + q'(\mathbf{a}) y_{\mathbf{b}}\bigr)^2}.
$$

*Step 3: Large sieve for Frostman measures.* Fix $\mathbf{b} \in \mathcal{W}_2$, write $\nu = \mu|_{I_{\mathbf{b}}}$ (total mass $w(\mathbf{b})$), let $x_0$ be the midpoint and $\rho_{\mathbf{b}} = \frac{1}{2}|I_{\mathbf{b}}| \le \frac{1}{2} R_2^{-2} = \frac{1}{2\Delta}$ the half-length of $I_{\mathbf{b}}$, and set $g(t) := \int_{I_{\mathbf{b}}} e(t(y - x_0))\,d\nu(y)$. Every $\Lambda_{\mathbf{a}, \mathbf{b}}$ lies in $[-U, U]$ with $U := M_P |\xi| R_1^{-2}$. Set $T := U + \Delta$ and
$$
N(\Delta) := \sup_{\mathbf{b} \in \mathcal{W}_2} \sup_{u \in \mathbb{R}} \sum_{\substack{\mathbf{a} \in \mathcal{W}_1^* \\ \Lambda_{\mathbf{a}, \mathbf{b}} \in [u, u + \Delta]}} w(\mathbf{a}).
$$
By Cauchy–Schwarz and binning $\mathbb{R}$ into intervals $[k\Delta, (k+1)\Delta)$ meeting $[-U, U]$,
$$
S_{\mathbf{b}}^2 \le \sum_{\mathbf{a} \in \mathcal{W}_1^*} w(\mathbf{a}) |g(\Lambda_{\mathbf{a}, \mathbf{b}})|^2 \le N(\Delta) \sum_{[k\Delta, (k+1)\Delta) \cap [-U, U] \ne \emptyset} \sup_{t \in [k\Delta, (k+1)\Delta]} |g(t)|^2.
$$
On each bin $[a_k, b_k] \subseteq [-T, T]$ of length $\Delta$, $|g(t_*)|^2 - |g(t_0)|^2 = \int_{t_0}^{t_*} 2 \operatorname{Re}(\overline{g} g')\,dt \le 2 \int_{a_k}^{b_k} |g| |g'|\,dt$; summing over $k$ and applying Cauchy–Schwarz gives Gallagher's Sobolev inequality:
$$
\sum_k \sup_{[a_k, b_k]} |g(t)|^2 \le \frac{1}{\Delta} \int_{-T}^T |g(t)|^2\,dt + 2 \left(\int_{-T}^T |g(t)|^2\,dt\right)^{1/2} \left(\int_{-T}^T |g'(t)|^2\,dt\right)^{1/2}.
$$
Using the Fejér majorant $H(u) = (\frac{\sin \pi u}{\pi u})^2 \ge \frac{4}{\pi^2}$ on $|u| \le \frac{1}{2}$ with $\int_{-\infty}^\infty H(\frac{t}{2T}) e(tz)\,dt = 2T \max(1 - 2T|z|, 0)$ and Lemma 2.2(4),
$$
\int_{-T}^T |g(t)|^2\,dt \le \frac{\pi^2}{2} T \iint_{I_{\mathbf{b}}^2} \max(1 - 2T|y - y'|, 0)\,d\nu(y)\,d\nu(y') \le \frac{\pi^2}{2} C_F T^{1 - s} w(\mathbf{b}).
$$
Since $|y - x_0| \le \rho_{\mathbf{b}} \le \frac{1}{2\Delta}$, the identical calculation for $g'(t) = 2\pi i \int (y - x_0) e(t(y - x_0))\,d\nu(y)$ gives $\int_{-T}^T |g'(t)|^2\,dt \le \frac{\pi^4}{2 \Delta^2} C_F T^{1 - s} w(\mathbf{b})$. Since $\sqrt{\pi^2/2 + \pi^3} < 6$, this gives $S_{\mathbf{b}} \le 6 \sqrt{C_F N(\Delta) \frac{T^{1-s}}{\Delta}} \sqrt{w(\mathbf{b})}$. Summing over $\mathbf{b} \in \mathcal{W}_2$ by Cauchy–Schwarz and using $|\mathcal{W}_2| \le 2 B_0^2 R_2^2 = 2 B_0^2 \Delta$ cancels $\Delta$ completely:
$$
\sum_{\mathbf{b} \in \mathcal{W}_2} S_{\mathbf{b}} \le 6 \sqrt{2 C_F} \, B_0 \sqrt{N(\Delta) \, T^{1 - s}}. \tag{2.6}
$$

*Step 4: Bounding $N(\Delta)$ via modular hyperbolas.* Split $\mathcal{W}_1^* = \mathcal{W}_1^+ \cup \mathcal{W}_1^-$ according to the sign of $\xi P'$ on $I_{\mathbf{a}}$; by symmetry we bound $\mathcal{W}_1^+$ and double the result. On $\mathcal{W}_1^+$, every $\Lambda_{\mathbf{a}, \mathbf{b}}$ lies in $[u_{\min}, u_{\max}]$ with $u_{\min} := \frac{\delta |\xi|}{4 B_0^2 R_1^2}$ and $u_{\max} := U$ (if $u_{\min} > u_{\max}$, then $\mathcal{W}_1^+ = \emptyset$ and the contribution is $0$). Replacing $T_{\mathbf{a}}(y_{\mathbf{b}})$ by the left endpoint $p/q = p(\mathbf{a}) / q(\mathbf{a}) \in I_{\mathbf{a}}$ changes $\Lambda_{\mathbf{a}, \mathbf{b}}$ by at most $\Delta' := L_P |\xi| R_1^{-4}$ (which is $0$ when $r = 1$). By the choice of $\bar{\xi}_0(P)$ in Step 5, for all $|\xi| \ge \bar{\xi}_0(P)$ we have $\Delta \le \frac{1}{2} u_{\min}$ and $\Delta' \le \min(\frac{1}{2}\Delta, \frac{1}{4} u_{\min})$. Thus any $[u, u + \Delta]$ meeting $[u_{\min}, u_{\max}]$ satisfies $u' := u - \Delta' \ge \frac{1}{4} u_{\min} > 0$, and every qualifying $\mathbf{a} \in \mathcal{W}_1^+$ satisfies $\frac{\xi P'(p/q)}{(q + q' y_{\mathbf{b}})^2} \in [u',\; u' + \Delta + 2\Delta'] \subseteq [u',\; u' + 2\Delta]$, hence
$$
\sqrt{\frac{\xi P'(p/q)}{u' + 2\Delta}} \le q + q' y_{\mathbf{b}} \le \sqrt{\frac{\xi P'(p/q)}{u'}}.
$$
By the elementary bound $\sqrt{A/u'} - \sqrt{A/(u'+2\Delta)} \le \sqrt{A} \Delta / (u')^{3/2}$ and $y_{\mathbf{b}} \ge \frac{1}{M+1}$, every such $(p, q')$ lies within vertical distance $W_0 := 64 (M + 1) B_0^3 M_P^{1/2} \delta^{-3/2} \frac{\Delta R_1^3}{|\xi|}$ of the curve $q' = F_q(p) := y_{\mathbf{b}}^{-1}(\sqrt{\xi P'(p/q) / u'} - q)$.

Fix $q \in [R_1, B_0 R_1]$. The set $\{t \in [0, 1] : \xi P'(t) \ge \delta |\xi|\}$ has at most $r$ connected components (since $P'(t) = \pm \delta$ has at most $r - 1$ real roots), on each of which $F_q$ is $C^1$ with
$$
|F_q'(x)| = \frac{|\xi| |P''(x/q)|}{2 y_{\mathbf{b}} q \sqrt{u'} \sqrt{\xi P'(x/q)}} \le 2 (M + 1) B_0 L_P \delta^{-1} = S_1 \delta^{-1} =: S_0.
$$
Set $K := \lceil (S_0 + 1)^{1/2} q^{(1 - \rho_{\mathrm{Klo}})/2} \rceil$. For $|\xi| \ge \bar{\xi}_0(P)$, Step 5 ensures $S_0 + 1 \le q^{1 + \rho_{\mathrm{Klo}}}$ for every $q \ge R_1$, so $1 \le K \le q$, whence $\lceil q/K \rceil \le 2 q / K$, $K + r \le (r + 1) K$, and $K \le 2(S_0 + 1)^{1/2} q^{(1 - \rho_{\mathrm{Klo}})/2}$. Partitioning $[1, q]$ into $K$ intervals of length $\le \lceil q/K \rceil$ and intersecting with the $\le r$ components yields at most $K + r$ subintervals $I_j$ of length $L_1 \le \lceil q/K \rceil \le 2q/K$, on each of which $q'$ lies in an interval $J_j \subseteq [1, q]$ of length $L_2 \le \min(q, W_0 + S_0 L_1 + 2)$. By Lemma 2.2(4), $(p, q)$ uniquely determines $\mathbf{a} \in \mathcal{W}_1^+$ and satisfies $p q' \equiv -1 \pmod q$. Applying Lemma 2.1(2)–(3) to each rectangle $I_j \times J_j$ and summing over $j$ gives at most
$$
32(r + 1) W_0 + 2(r + 1)(C_{\mathrm{Klo}} + 64)(S_0 + 1)^{1/2} \tau(q) q^{(1 + \rho_{\mathrm{Klo}})/2}
$$
solutions for fixed $q$ (using $2 + \frac{2 S_0 q}{K} \le 4(S_0 + 1)^{1/2} q^{(1 + \rho_{\mathrm{Klo}})/2}$ and $1 \le \tau(q)$). Doubling for $\mathcal{W}_1^\pm$, summing over $q \in [R_1, B_0 R_1]$ via $\sum_{q \le B_0 R_1} \tau(q) \le B_0 R_1 (\log(B_0 R_1) + 1) \le B_0 R_1 \log(3 B_0 |\xi|)$ and $q^{(1 + \rho_{\mathrm{Klo}})/2} \le B_0 R_1^{(1 + \rho_{\mathrm{Klo}})/2}$, and multiplying by $w(\mathbf{a}) \le R_1^{-2s}$ yields
$$
N(\Delta) \le 64(r + 1) B_0 R_1^{1 - 2s} W_0 + 4(r + 1)(C_{\mathrm{Klo}} + 64) B_0^2 (S_0 + 1)^{1/2} R_1^{\frac{3 + \rho_{\mathrm{Klo}}}{2} - 2s} \log(3 B_0 |\xi|).
$$

*Step 5: Explicit computable rational majorants $\bar{\xi}_0(P)$ and $\bar{C}(P)$.* Every threshold inequality $A |\xi|^{-\gamma} \le 1$ ($A \in \mathbb{Q}_{>0}, \gamma \in \mathbb{Q}_{>0}$) holds whenever $|\xi| \ge \max(1, \lceil A \rceil)^{\lceil 1/\gamma \rceil} \in \mathbb{Z}_{\ge 1}$. Define the positive rational exponents $\gamma_1 := 1 - 2\alpha - 2\beta - \theta$ and $\gamma_5 := 1 - 2\alpha - 2\beta$ (and, for $r \ge 2$, $\gamma_2 := 4\alpha + 2\beta - 1$, $\gamma_3 := 2\alpha - \theta$, $\gamma_4 := (1 + \rho_{\mathrm{Klo}})\alpha - \theta$), and define the explicit computable integers:
* For $r = 1$: $X_1 := \max(1, \lceil 8 B_0^2 / c_* \rceil)^{\lceil 1/\gamma_1 \rceil}$, $X_2 = X_3 = X_4 := 1$;
* For $r \ge 2$: $X_1 := (8 B_0^2)^{\lceil 1/\gamma_1 \rceil}$, $X_2 := \max(1, \lceil 2 L_P \rceil)^{\lceil 1/\gamma_2 \rceil}$, $X_3 := \max(1, \lceil 16 B_0^2 L_P \rceil)^{\lceil 1/\gamma_3 \rceil}$, $X_4 := \max(1, \lceil S_1 + 1 \rceil)^{\lceil 1/\gamma_4 \rceil}$;
* For all $r \ge 1$: $X_5 := \max(1, \lceil 1 / M_P \rceil)^{\lceil 1/\gamma_5 \rceil}$, and
  $$
  \bar{\xi}_0(P) := \max(16,\; X_1,\; X_2,\; X_3,\; X_4,\; X_5) \in \mathbb{Z}_{\ge 16}.
  $$
By construction, $|\xi| \ge \bar{\xi}_0(P)$ enforces $\Delta \le \frac{1}{2} u_{\min}$ (via $X_1$), $\Delta' \le \frac{1}{2}\Delta$ (via $X_2$), $\Delta' \le \frac{1}{4} u_{\min}$ (via $X_3$), $S_0 + 1 \le R_1^{1 + \rho_{\mathrm{Klo}}} \le q^{1 + \rho_{\mathrm{Klo}}}$ (hence $K \le q$, via $X_4$), and $\Delta \le U$ (hence $T = U + \Delta \le 2 M_P |\xi|^{1 - 2\alpha}$, via $X_5$).

Now bound each factor of $N(\Delta) T^{1 - s}$ rationally for $|\xi| \ge \bar{\xi}_0(P)$:
* $M_P^{1/2} \le \bar{M}_P$, $T^{1 - s} \le 2 \bar{M}_P |\xi|^{(1 - 2\alpha)(1 - s)}$, and $(S_0 + 1)^{1/2} \le (S_1 + 1) |\xi|^{\theta/2}$ (both for $r = 1$ where $S_0 = S_1 = \theta = 0$, and for $r \ge 2$ where $S_0 + 1 \le (S_1 + 1)|\xi|^\theta$);
* $\delta^{-3/2} = |\xi|^{3\theta/2}$ when $r \ge 2$ (put $D_{\delta, 1} := 1$) and $\delta^{-3/2} = c_*^{-3/2} \le \max(1, c_*^{-2}) =: D_{\delta, 1}$ when $r = 1$;
* By $\log x \le x^\varepsilon / \varepsilon$ ($x > 0, \varepsilon > 0$) applied with $x = 3 B_0 |\xi|$ and $\varepsilon = m_B / 2 \in (0, 1)$,
  $$
  \log(3 B_0 |\xi|) \le \frac{2}{m_B} (3 B_0)^{m_B / 2} |\xi|^{m_B / 2} \le \frac{6 B_0}{m_B} |\xi|^{m_B / 2}.
  $$
Multiplying $N(\Delta)$ by $T^{1 - s}$ cancels $2\alpha s$ in both exponents, leaving $-m_A$ and $-m_B + m_B/2 = -m_B/2$, both $\le -2\eta_{r, s, \rho}$:
$$
N(\Delta) T^{1 - s} \le 2 \bar{M}_P \bigl(K_A^{(0)}(P) + K_B^{(0)}(P)\bigr) |\xi|^{-2\eta_{r, s, \rho}},
$$
with explicit rationals $K_A^{(0)}(P) := 4096 (r + 1)(M + 1) B_0^4 \bar{M}_P D_{\delta, 1}$ and $K_B^{(0)}(P) := \frac{24(r + 1)(C_{\mathrm{Klo}} + 64) B_0^3 (S_1 + 1)}{m_B}$. Substituting into (2.6) and using $\sqrt{X} \le X$ for $X \ge 1$ gives
$$
\sum_{\mathbf{b} \in \mathcal{W}_2} S_{\mathbf{b}} \le 12 C_F B_0 \bar{M}_P \bigl(K_A^{(0)}(P) + K_B^{(0)}(P)\bigr) |\xi|^{-\eta_{r, s, \rho}} =: A_3(P) |\xi|^{-\eta_{r, s, \rho}}.
$$
Finally, for $|\xi| \ge \bar{\xi}_0(P) \ge 16$ we have $|\xi|^{-\eta} \le 2 (1 + |\xi|)^{-\eta}$, while for $|\xi| < \bar{\xi}_0(P)$ the trivial bound $1 \le (1 + \bar{\xi}_0(P)) (1 + |\xi|)^{-\eta}$ holds (since $0 < \eta < 1$). Setting the explicit computable rational majorant
$$
\bar{C}(P) := \max\!\Bigl(1 + \bar{\xi}_0(P),\; 2\bigl(A_1(P) + A_2(P) + A_3(P)\bigr)\Bigr) \in \mathbb{Q}_{>0}
$$
proves (2.4) for every real $\xi$. $\square$

### Theorem 2.4 (Computable badly approximable polynomial-normal numbers and all-prime series)

Let $(M, L, s)$ be any certified block-measure parameter triple of Lemma 2.2 satisfying the hypothesis of Theorem 2.3:
* $M = 100, L = 52, s = 19/20$ (**`Paper proof`**, zero external inputs, zero computer certificates);
* $M = 42, L = 4, s = 18/19$ (**`Paper proof`**, using Lemma 2.2(3) `Finite certificate`; zero external inputs);
* $M = 14, L = 4, s = 10/11$ or $M = 30, L = 2, s = 10/11$ (**`Paper proof`**, using Lemma 2.2(3) `Finite certificate` and inputs Weil 1948, Estermann 1961).

Then there is an explicit Turing machine that computes the continued-fraction partial quotients of a real number $x = [0; a_1, a_2, \ldots] \in F_M$ ($1 \le a_n \le M$ for all $n \ge 1$) such that:
1. $x$ is **badly approximable** with uniform constant $q \|q x\| > \frac{1}{M + 2}$ for every integer $q \ge 1$ (giving $> 1/102$ for $M = 100$, $> 1/44$ for $M = 42$, $> 1/16$ for $M = 14$, and $> 1/32$ for $M = 30$).
2. For **every** nonconstant rational polynomial $P \in \mathbb{Q}[X]$, $P(x)$ is **absolutely normal** (normal in every integer base $b \ge 2$).
3. **(Computable badly approximable all-prime full-density series):** Fixing any target radix $b \ge 2$ and letting $\ell_1 < \ell_2 < \cdots$ enumerate the primes not dividing $b$ and $S = \sum_{n \ge 1} \ell_n^{-1} b^{-n}$, the same algorithm (including $X - S$ among the tested maps) makes $x - S$ normal in base $b$ (hence irrational with computable base-$b$ digits $d_n$). The resulting full-density positive series
   $$
   Z = \sum_{n \ge 1} \left(d_n + \frac{1}{\ell_n}\right) b^{-n} = x - \lfloor x - S \rfloor
   $$
   is **computable**, has exact shifted prefix denominators $\prod_{n \le N} \ell_n$ (every off-radix prime enters at its own site and persists), has base-$b$ normal individual-site digits $d_n$, satisfies $q \|q Z\| > \frac{1}{M + 2}$ for all $q \ge 1$, and has $P(Z)$ absolutely normal for every nonconstant $P \in \mathbb{Q}[X]$.

**Proof.**
*Step 1: Effective $L^2$ Davenport–Erdős–LeVeque moment bound with rational majorant.* For any test triple $e = (P_e, b_e, h_e)$ consisting of a nonconstant $P_e \in \mathbb{Q}[X]$ (or $X - S$) of degree $r_e \ge 1$, an integer base $b_e \ge 2$, and a positive integer frequency $h_e \ge 1$, write $S_N(x; e) := \frac{1}{N} \sum_{n = 0}^{N - 1} e(h_e b_e^n P_e(x))$ and $\eta_e := \eta_{r_e, s, \rho} \in \mathbb{Q} \cap (0, 1)$. Expanding $|S_N|^2$ and using $h_e(b_e^n - b_e^m) \ge b_e^{n - 1} \ge 2^{n - 1}$ for $0 \le m < n < N$, Theorem 2.3 gives
$$
\int_0^1 |S_N(x; e)|^2\,d\mu(x) \le \frac{1}{N} + \frac{2 \bar{C}(P_e)}{N^2} \sum_{n = 1}^{N - 1} n \, 2^{-\eta_e (n - 1)} \le \frac{K(P_e)}{N}, \qquad K(P_e) := 1 + \frac{2 \bar{C}(P_e)}{(1 - 2^{-\eta_e})^2},
$$
uniformly in $b_e \ge 2$, $h_e \ge 1$, and $N \ge 1$. To avoid computing the irrational real $K(P_e)$, use $1 - e^{-x} \ge \frac{x}{1 + x}$ ($x > 0$) and $\log 2 > \frac{2}{3}$ (proved in Lemma 2.2(2) from $e < \frac{11}{4} \implies e^2 < 8$) to obtain $\frac{1}{1 - 2^{-\eta_e}} \le 1 + \frac{1}{\eta_e \log 2} < 1 + \frac{3}{2\eta_e}$. Thus the **explicit computable rational**
$$
\bar{K}_e := 1 + 2 \bar{C}(P_e) \left(1 + \frac{3}{2 \eta_e}\right)^2 \in \mathbb{Q}_{>1}
$$
strictly majorizes $K(P_e)$.

*Step 2: Continuous-partial-sum $L^2$ potential function with computable integer thresholds.* Fix a computable enumeration $e = 1, 2, \ldots$ of all triples $(P_e, b_e, h_e)$ (including $(X - S, b, h)$ for (3)). Compute the integer threshold directly by rational floor division:
$$
J_e := \lfloor 2^{e + 3} \bar{K}_e \rfloor + 1 \in \mathbb{Z}_{\ge 1},
$$
so $J_e > 2^{e + 3} \bar{K}_e > 2^{e + 3} K(P_e)$ (avoiding the uncomputable ceiling of an irrational). Define
$$
\Psi(x) := \sum_{e = 1}^\infty \sum_{j = J_e}^\infty \bigl|S_{j^2}(x; e)\bigr|^2 \in [0, \infty].
$$
Since $\sum_{j = J_e}^\infty j^{-2} \le 2 / J_e$, Tonelli's theorem gives
$$
\int_0^1 \Psi(x)\,d\mu(x) \le \sum_{e = 1}^\infty \frac{2 K(P_e)}{J_e} < \sum_{e = 1}^\infty \frac{2 \bar{K}_e}{J_e} < \sum_{e = 1}^\infty 2^{-e - 2} = \frac{1}{4}.
$$

*Step 3: Fully rational computability of conditional expectations and nested-cylinder selection.* First, compute the exact rational block weights $p_{\mathbf{u}}$ of Lemma 2.2(1) by searching $D = 1, 2, \ldots$ until $\sum_{\mathbf{u}} a_{N(\mathbf{u})} > D$ (which halts because $\Sigma(M, L, s) > 1$). For any block-cylinder $I_{\mathbf{a}}$ ($\mathbf{a} = \mathbf{u}_1 \cdots \mathbf{u}_m$) of exact positive rational mass $w(\mathbf{a}) = \prod_{i=1}^m p_{\mathbf{u}_i}$, we compute $\mathbb{E}[\Psi \mid I_{\mathbf{a}}] := w(\mathbf{a})^{-1} \int_{I_{\mathbf{a}}} \Psi\,d\mu$ to any prescribed rational tolerance $\delta > 0$ using only finite rational arithmetic:
1. **Rational tail truncation (budget $\delta/2$):** Choose explicit integers $E, J \ge 1$ by rational arithmetic so that $\frac{2^{-E - 2}}{w(\mathbf{a})} < \frac{\delta}{4}$ and $\frac{2}{J w(\mathbf{a})} \sum_{e=1}^E \bar{K}_e < \frac{\delta}{4}$ (e.g., $J = \lfloor \frac{8}{w(\mathbf{a})\delta} \sum_{e=1}^E \bar{K}_e \rfloor + 1$). Put $\mathcal{F} := \{(e, j) : 1 \le e \le E,\; J_e \le j < J\}$ and $N_{\mathcal{F}} := |\mathcal{F}|$. Because every term of $\Psi$ is nonnegative, the omitted tail of $\mathbb{E}[\Psi \mid I_{\mathbf{a}}]$ lies in $[0, \delta/2)$.
2. **Rational refinement, $S$-truncation, and trigonometric evaluation (budget $\delta/6 + \delta/6 + \delta/6 = \delta/2$):** For each $(e, j) \in \mathcal{F}$, $|S_{j^2}(x; e)|^2$ is $C^\infty$ on $[0, 1]$ with rational Lipschitz majorant $\bar{L}_{e, j} := 16 h_e b_e^{j^2} M_{P_e} \ge 4\pi h_e b_e^{j^2} M_{P_e}$ (using $\pi < 4$). Set $\bar{L}_{\mathrm{tot}} := \sum_{(e, j) \in \mathcal{F}} \bar{L}_{e, j} \in \mathbb{Q}_{>0}$.
   * *Sub-cylinder refinement ($\delta/6$):* Refining $I_{\mathbf{a}}$ by $d \ge 1$ additional block levels partitions $I_{\mathbf{a}}$ into sub-cylinders $I_{\mathbf{a}\mathbf{v}}$ of exact rational conditional weights $\prod_{i=1}^d p_{\mathbf{v}_i}$ and diameter $\le \phi^{-2(d L - 1)} < (5/8)^{2(d L - 1)}$ (using $\phi > 8/5$ from Lemma 2.2(2)). Increment $d = 1, 2, \ldots$ until the rational inequality $\bar{L}_{\mathrm{tot}} (5/8)^{2(d L - 1)} < \delta/6$ holds. Evaluating at one rational endpoint $x_{\mathbf{a}\mathbf{v}} \in I_{\mathbf{a}\mathbf{v}}$ incurs total discretization error $< \delta/6$ summed over all $(e, j) \in \mathcal{F}$.
   * *Partial sum of $S$ ($\delta/6$):* For any active term with $P_e = X - S$, replace $S$ by $S_{N_S} = \sum_{n=1}^{N_S} \ell_n^{-1} b^{-n}$, whose tail satisfies $|S - S_{N_S}| < b^{-N_S}$; choosing the least integer $N_S \ge 1$ with $\bar{L}_{\mathrm{tot}} b^{-N_S} < \delta/6$ keeps the total $S$-approximation error summed over all $(e, j) \in \mathcal{F}$ strictly $< \delta/6$.
   * *Rational trigonometric evaluation ($\delta/6$):* Set $\epsilon_{\mathrm{trig}} := \min(\frac{1}{2}, \frac{\delta}{36 \max(1, N_{\mathcal{F}})}) \in \mathbb{Q}_{>0}$. For each evaluation angle $\theta = \{h_e b_e^n \widetilde{P}_e(x_{\mathbf{a}\mathbf{v}})\} \in [0, 1) \cap \mathbb{Q}$, compute a rational approximation $\tilde{\pi}$ with $|\pi - \tilde{\pi}| < \epsilon_{\mathrm{trig}} / 4$ (via Machin's alternating arctangent series $\pi/4 = 4\arctan(1/5) - \arctan(1/239)$) and evaluate $\cos(2\tilde{\pi}\theta)$ and $\sin(2\tilde{\pi}\theta)$ by Taylor polynomials of degree $2 N_{\mathrm{Tay}}$ with $\frac{7^{2 N_{\mathrm{Tay}} + 1}}{(2 N_{\mathrm{Tay}} + 1)!} < \epsilon_{\mathrm{trig}} / 2$ (as $2\tilde{\pi}\theta < 7$). Each $\cos(2\pi\theta)$ and $\sin(2\pi\theta)$ is within $\epsilon_{\mathrm{trig}}$, so each $S_{j^2}$ is within $2\epsilon_{\mathrm{trig}}$ and each $|S_{j^2}|^2$ is within $(2 + 2\epsilon_{\mathrm{trig}}) \cdot 2\epsilon_{\mathrm{trig}} \le 6\epsilon_{\mathrm{trig}}$. Summing over all $(e, j) \in \mathcal{F}$ gives total evaluation error $< \delta/6$.

   Combining all four budgets yields a rational approximation $\widehat{E}(\mathbf{a}) \in \mathbb{Q}$ satisfying $|\widehat{E}(\mathbf{a}) - \mathbb{E}[\Psi \mid I_{\mathbf{a}}]| < \delta$.

Now set rational thresholds $B_m := 1 - 2^{-m - 1}$ ($m \ge 0$). At $m = 0$, $I_0 = [0, 1]$ satisfies $\mathbb{E}[\Psi \mid I_0] < \frac{1}{4} < \frac{1}{2} = B_0$. Inductively, given $I_m = I_{\mathbf{a}}$ with $\mathbb{E}[\Psi \mid I_m] < B_m$, compute $\widehat{E}(\mathbf{a} \mathbf{u})$ for every child block $\mathbf{u} \in \{1, \ldots, M\}^L$ to rational accuracy $\delta_m := \frac{B_{m+1} - B_m}{4} = 2^{-m - 4}$. Because $\sum_{\mathbf{u}} p_{\mathbf{u}} \mathbb{E}[\Psi \mid I_{\mathbf{a}\mathbf{u}}] = \mathbb{E}[\Psi \mid I_{\mathbf{a}}] < B_m$, at least one child satisfies $\mathbb{E}[\Psi \mid I_{\mathbf{a}\mathbf{u}}] < B_m$, hence $\widehat{E}(\mathbf{a}\mathbf{u}) < B_m + \delta_m < B_{m+1} - \delta_m$. Choosing the lexicographically first child satisfying the exact rational inequality $\widehat{E}(\mathbf{a}\mathbf{u}) < B_{m+1} - \delta_m$ halts deterministically, certifies $\mathbb{E}[\Psi \mid I_{\mathbf{a}\mathbf{u}}] < B_{m+1}$, and sets $I_{m+1} = I_{\mathbf{a}\mathbf{u}}$.

*Step 4: Verification of normality and Diophantine properties.* The nested closed cylinders $I_m$ shrink to a unique computable $x = [0; a_1, a_2, \ldots] \in F_M$. For every finite cutoff $T \ge 1$, the partial sum $\Psi_T(y) := \sum_{e=1}^T \sum_{j = J_e}^T |S_{j^2}(y; e)|^2$ is **continuous** on $[0, 1]$ and satisfies $0 \le \Psi_T \le \Psi$. Therefore, for all $m \ge 0$,
$$
\frac{1}{\mu(I_m)} \int_{I_m} \Psi_T(y)\,d\mu(y) \le \mathbb{E}[\Psi \mid I_m] < B_m < 1.
$$
Sending $m \to \infty$ gives $\Psi_T(x) \le 1$ by continuity of $\Psi_T$ at $x$; sending $T \to \infty$ gives $\Psi(x) \le 1 < \infty$. Thus for every triple $e = (P_e, b_e, h_e)$, $\sum_{j \ge J_e} |S_{j^2}(x; e)|^2 \le 1$, so $S_{j^2}(x; e) \to 0$. For $j^2 \le N < (j+1)^2$, $|S_N(x; e) - S_{j^2}(x; e)| \le \frac{2(N - j^2)}{N} \le \frac{4}{j} \to 0$, so $S_N(x; e) \to 0$. By Weyl's criterion (with conjugation for $h < 0$), $P(x)$ is absolutely normal for every nonconstant $P \in \mathbb{Q}[X]$ (and $x - S$ is normal in base $b$). Since $1 \le a_n \le M$ for all $n \ge 1$, the standard convergent inequality (Phase 24 §3) gives $q \|q x\| > \frac{1}{M + 2}$ for all $q \ge 1$. Part (3) follows identically to Phase 24 §3 eq. (6), since $Z = x - \lfloor x - S \rfloor$ differs from $x$ by an integer and $x - S$ is irrational (so base-$b$ digit extraction of $\{x - S\}$ never stalls at a $b$-adic rational). $\square$

---

## 3. Exact continued-fraction folding and slower-loss locally varying deterministic series (F3)

In Phase 24 §4, the deterministic full-density all-prime family $V(a)$ achieved $\mu(V(a)) = 2$ with uniform defect $\exp(-C (\log\log(3q))^2)$ (losing $O(k)$ per doubling step across $K \asymp \log\log q$ steps via Phase 23 Lemma 5) and required all sites in each shell $(2^k, 2^{k+1}]$ to carry the same constant filler $a_k$. We sharpen both the folding step and the deterministic construction.

### Theorem 3.1 (Exact Continued-Fraction Folding Lemma — `Paper proof`)

Let $u = p_n / q_n = [0; a_1, \ldots, a_n] \in (0, 1/2)$ be a reduced rational in canonical form ($a_n \ge 2$; note $a_1 \ge 3$ if $n = 1$ and $a_1 \ge 2$ if $n \ge 2$), with maximum partial quotient $A(u) = \max_{1 \le i \le n} a_i$. Let $z = \varepsilon c / d_z$ in lowest terms ($\varepsilon \in \{+1, -1\}$, $c, d_z \ge 1$, $\gcd(c, d_z) = 1$), and set $v = u + z / q_n^2$.
1. **Zero folding loss at $c = 1$:** For every $d_z \ge 2$ and either sign $\varepsilon \in \{\pm 1\}$, the canonical expansion of $v = u + \varepsilon / (d_z q_n^2)$ satisfies
   $$
   A(v) = \max\bigl(A(u), \; d_z - 1\bigr),
   $$
   with final partial quotient $a_{\mathrm{last}}(v) = a_1 - 1 \ge 2$ if $(n = 1, \varepsilon = -1)$ and $a_{\mathrm{last}}(v) = a_1 \ge 2$ in all other cases.
2. **Factor-2-free general partial-quotient bound ($c \ge 2$):** Whenever $d_z > 2c$,
   $$
   A(v) \le \max\!\left(\left\lfloor \frac{d_z}{c} \right\rfloor, \; c^2 \bigl(A(u) + 2\bigr) - 1\right).
   $$

**Proof.** Recall $T_{\mathbf{a}}(y) - \frac{p_n}{q_n} = \frac{(-1)^n y}{q_n(q_n + q_{n-1} y)}$ for $\mathbf{a} = (a_1, \ldots, a_n)$. If $\varepsilon = (-1)^n$, solving $T_{\mathbf{a}}(y) = v$ gives $\frac{1}{y} = \frac{d_z}{c} - \alpha$ with $\alpha = \frac{q_{n-1}}{q_n} = [0; a_n, a_{n-1}, \ldots, a_1] \in (0, 1)$. If $\varepsilon = -(-1)^n$, rewrite $u$ in its non-canonical length-$(n + 1)$ expansion $\mathbf{a}' = (a_1, \ldots, a_n - 1, 1)$ (whose convergents still satisfy $q(\mathbf{a}') = q_n$, with $q'(\mathbf{a}') = q_n - q_{n-1}$); solving $T_{\mathbf{a}'}(y) = v$ gives $\frac{1}{y} = \frac{d_z}{c} - \alpha'$ with $\alpha' = 1 - \alpha = [0; 1, a_n - 1, a_{n-1}, \ldots, a_1] \in (0, 1)$.

For (1) ($c = 1, d_z \ge 2$), $1 - \alpha = [0; 1, a_n - 1, a_{n-1}, \ldots, a_1]$ and $1 - \alpha' = \alpha = [0; a_n, a_{n-1}, \ldots, a_1]$, yielding the exact canonical expansions:
$$
v = \begin{cases}
[0; a_1, \ldots, a_n, \; d_z - 1, \; 1, \; a_n - 1, \; a_{n-1}, \ldots, a_1] & (\varepsilon = (-1)^n), \\
[0; a_1, \ldots, a_n - 1, \; 1, \; d_z - 1, \; a_n, \; a_{n-1}, \ldots, a_1] & (\varepsilon = -(-1)^n).
\end{cases}
$$
Every listed partial quotient is $\ge 1$, the final entry is $a_1 \ge 2$ when $n \ge 2$ or $\varepsilon = +1$ (and $a_1 - 1 \ge 2$ when $n = 1, \varepsilon = -1$, since $u < 1/2$ forces $a_1 \ge 3$), and the maximum over all entries is identically $\max(A(u), d_z - 1)$.

For (2) ($c \ge 2, d_z > 2c$), write $\beta = \frac{1}{y} = \frac{d_z}{c} - \tilde{\alpha}$ ($\tilde{\alpha} \in \{\alpha, \alpha'\}$) in canonical form $[b_1; b_2, \ldots, b_r]$ ($b_r \ge 2$ if $r \ge 2$). Since $d_z / c > 2$ and $\tilde{\alpha} \in (0, 1)$, $b_1 = \lfloor \beta \rfloor \in [1, \lfloor d_z / c \rfloor]$ (and if $r = 1$, $b_1 \ge 2$). Appending $b_1, \ldots, b_r$ to $\mathbf{a}$ (or $\mathbf{a}'$) gives a valid canonical expansion of $v$. For every $1 \le i \le r - 1$, let $h_i / l_i$ be the $i$-th convergent of $\beta$; then $|\beta - h_i / l_i| \le \frac{1}{b_{i+1} l_i^2}$. Meanwhile, since $H / L := (d_z l_i - c h_i) / (c l_i) \ne \tilde{\alpha}$, every rational $H / L \ne \alpha$ satisfies the strict best-approximation inequality $L |L \alpha - H| > \frac{1}{A(u) + 2}$ (for $L \ge q_n$, $L|L\alpha - H| \ge L/q_n \ge 1$; for $1 \le L < q_n$, the convergent $s_j / t_j$ of $\alpha$ with $t_j \le L < t_{j+1}$ satisfies $L|L\alpha - H| \ge t_j |t_j \alpha - s_j| > \frac{1}{A(u) + 2}$), and the same holds for $\alpha' = 1 - \alpha$. Substituting $L = c l_i$ gives
$$
\frac{1}{(A(u) + 2) c^2 l_i^2} < \left|\tilde{\alpha} - \frac{d_z l_i - c h_i}{c l_i}\right| = \left|\beta - \frac{h_i}{l_i}\right| \le \frac{1}{b_{i+1} l_i^2},
$$
hence $b_{i+1} \le c^2 (A(u) + 2) - 1$. $\square$

### Theorem 3.2 (Deterministic full-density locally varying all-prime series with arbitrarily slow folding loss — `Paper proof`)

Fix any integer base $b \ge 2$, any odd prime $p \nmid b$, and **any** computable strictly increasing integer sequence $\kappa_1 < \kappa_2 < \cdots$ with $\kappa_1 \ge 2$ and $\kappa_{m + 1} - \kappa_m \to \infty$ (for example, $\kappa_m = 2^m$). Define the slowly growing pole count $e_k := \#\{m \ge 1 : \kappa_m \le k\} \to \infty$. Let $\ell_1 < \ell_2 < \cdots$ enumerate the primes not dividing $bp$, and define the computable sparse auxiliary indices $m_j := 1 + \max\bigl(m_{j-1},\; 4 \lceil \log_2 \prod_{i=1}^j \ell_i \rceil\bigr)$ ($m_0 = 0$), so that $\Lambda_m := \prod_{m_j \le m} \ell_j \le 2^{m / 4}$ for every $m \ge 1$.

Define sparse coefficients $c_k$:
* At $k = \kappa_m$, set $\mu_m = \ell_j$ if $m = m_j$ and $\mu_m = 1$ otherwise, and put $c_{\kappa_m} = u_m / (p^m \mu_m)$, where $u_m$ is the least positive solution of $u_m \equiv \mu_m b^{2^{\kappa_m}} \pmod{p^m}$ and $u_m \equiv 1 \pmod{\operatorname{rad}(b) \mu_m}$.
* At $k \notin \{\kappa_m\}$, set $c_k = 2$.

Define nondecreasing power-of-two sub-shell periods $P_k := 2^{\lfloor \log_2(1 + e_k) \rfloor}$ when $2 \cdot 2^{\lfloor \log_2(1 + e_k) \rfloor} \le 2^k$ and $P_k := 1$ otherwise. For an **arbitrary** sequence of local sub-shell patterns $\mathbf{w} = (\mathbf{w}_k)_{k \ge 1}$ with $\mathbf{w}_k = (w_{k, 1}, \ldots, w_{k, P_k}) \in \{1, 2\}^{P_k}$, define the full-density positive series
$$
V(\mathbf{w}) := \sum_{k \ge 1} c_k b^{-2^k} + \sum_{k \ge 1} \sum_{j = 0}^{2^k / P_k - 1} \sum_{i = 1}^{P_k} w_{k, i} b^{-2^k - j P_k - i}. \tag{3.1}
$$
Let $\mathbf{w}^{\mathbf{1}}$ denote the **all-ones baseline** ($w_{k, i} = 1$ for all $k, i$), and for any $\mathbf{w}$ define its **expanded site-by-site binary difference sequence** $(\varepsilon_n(\mathbf{w}))_{n \ge 3} \in \{0, 1\}^{\mathbb{Z}_{\ge 3}}$ by $\varepsilon_{2^k + j P_k + i}(\mathbf{w}) := w_{k, i} - 1$ ($k \ge 1$, $0 \le j < 2^k / P_k$, $1 \le i \le P_k$). Then uniformly across all continuum-many pattern choices $\mathbf{w}$:
1. **Full occupancy, local variation, and all-prime support:** Every integer position $n \ge 2$ is occupied with positive coefficients in $(0, \operatorname{rad}(b) + 2]$, varying freely across $2^{P_k}$ site-by-site patterns in shell $k$, and every raw shifted prefix at $n \in [2^k, 2^{k+1})$ has exact denominator $D_k = p^{e_k} \Lambda_{e_k}$ (retaining every off-radix prime).
2. **Polynomial normality in every degree (pure complete-period proof):** For every nonconstant $P \in \mathbb{Q}[X]$ of degree $r \ge 1$, $P(V(\mathbf{w}))$ is normal in base $b$ with quantitative discrepancy bound
   $$
   D_N\bigl(P(V(\mathbf{w})); b\bigr) \ll_{P, b, p, \kappa} p^{-e_K / 4} + 2^{-(\kappa_{e_K} - \kappa_{e_K - 1})} \qquad (K = \lfloor \log_2 N \rfloor),
   $$
   where the displayed quantity is computable at each $N$ (and has an effective modulus of convergence to $0$ whenever $\kappa_{m+1} - \kappa_m$ admits a computable unbounded nondecreasing lower bound, e.g., $\kappa_m = 2^m$).
3. **Improved uniform irrationality measure ($\mu = 2$):** There exist constants $c, C > 0$ depending only on $b, p$ (and the initial prefix of $\kappa$) such that for every choice $\mathbf{w}$ and every integer $q \ge 1$,
   $$
   \|q V(\mathbf{w})\| \ge \frac{c}{q} \exp\!\Bigl\{-C (\log \log(3q)) \cdot \bigl(1 + e_{\lfloor \log_2 \log_b(3q) \rfloor + 4}\bigr)\Bigr\}. \tag{3.2}
   $$
   In particular, $\kappa_m = 2^m$ ($e_k = \lfloor \log_2 k \rfloor$) gives $\|q V(\mathbf{w})\| \ge \frac{c}{q} \exp\{-C (\log\log(3q)) \log\log\log(16q)\}$, and choosing $\kappa_m$ sparser attains $\exp\{-C(\log\log(3q)) \psi(\log\log(3q))\}$ for any prescribed computable unbounded nondecreasing $\psi \to \infty$.
4. **Injectivity and exact baseline-difference irrationality criterion:** Distinct pattern sequences $\mathbf{w} \ne \mathbf{w}'$ (differing at some $k$ with $2 P_k \le 2^k$) produce distinct real values $V(\mathbf{w}) \ne V(\mathbf{w}')$. Moreover, $V(\mathbf{w}) - V(\mathbf{w}^{\mathbf{1}})$ is irrational **if and only if** the expanded site-by-site difference sequence $(\varepsilon_n(\mathbf{w}))_{n \ge 3}$ is not eventually periodic (for example, $w_{k, 1} = 1 + (k \bmod 2)$ and $w_{k, i} = 1$ for $i \ge 2$).

**Proof.**
*Exact regrouping and denominators.* Set $\lambda_0 = 0$ and $\lambda_k = W(\mathbf{w}_k) / (b^{P_k} - 1)$ where $W(\mathbf{w}_k) = \sum_{i = 1}^{P_k} w_{k, i} b^{P_k - i}$. Finite geometric summation gives
$$
V(\mathbf{w}) = \sum_{k \ge 1} d_k b^{-2^k}, \qquad d_k = c_k + \lambda_k - \lambda_{k - 1}. \tag{3.3}
$$
Every filler coefficient in (3.1) is an integer, so the raw shifted prefix at $n \in [2^k, 2^{k+1})$ inherits the exact denominator $D_k = p^{e_k} \Lambda_{e_k}$ from the unique deepest $p$-pole and unique auxiliary prime occurrences. Since $w_{k, i} \in \{1, 2\}$, $\lambda_k \in [\frac{1}{b-1}, \frac{2}{b-1}]$ for every $k \ge 1$. At $k = 1$, $c_1 = 2$ and $\lambda_0 = 0$, so $d_1 = 2 + \lambda_1 > 2 > 1$; for every $k \ge 2$, $|\lambda_k - \lambda_{k-1}| \le \frac{1}{b-1} \le 1$, so for $k \notin \{\kappa_m\}$, $c_k = 2$ ensures $d_k \ge 1 > 0$ even for $b = 2$. Because $P_k$ is a power of $2$ and $p$ is odd, LTE gives $v_p(b^{P_k} - 1) \le a_0 = v_p(b^t - 1)$ (constant!), hence $p^{a_0}(\lambda_k - \lambda_{k-1}) \in \mathbb{Z}_p$ for every $k \ge 1$ and every $\mathbf{w}$. At each pole index $k = \kappa_m$, the CRT congruence $u_m \equiv \mu_m b^{2^{\kappa_m}} \pmod{p^m}$ with $p \nmid \mu_m b$ implies $b^{-2^{\kappa_m}} c_{\kappa_m} - p^{-m} \in \mathbb{Z}_p$. Writing $\alpha_m := b^{-2^{\kappa_m}} d_{\kappa_m}$, we therefore have uniformly in $\mathbf{w}$ and independently of $\mu_m$:
$$
\alpha_m = p^{-m} + \delta_m \quad \text{with } p^{a_0} \delta_m \in \mathbb{Z}_p \quad (m \ge 1), \qquad\text{and}\qquad p^{a_0} b^{-2^k} d_k \in \mathbb{Z}_p \quad (k \notin \{\kappa_m\}).
$$
In particular, at $k = \kappa_m$ ($m > a_0$), $d_{\kappa_m}$ has exact $p$-depth $m$, whereas every non-pole $d_k$ has $p$-depth $\le a_0$.

*Monic-polynomial $p$-adic pole retention.* Write $P(X) = \sum_{d=0}^r \gamma_d X^d \in \mathbb{Q}[X]$ with $\gamma_r \ne 0$, and clear denominators as $b^c P = Y / D_P$ with $Y \in \mathbb{Z}[X]$ and $\gcd(D_P, b) = 1$. At any shift $n$, since $p \nmid b$, the shifted prefix $R_n^{(P)}$ of $P(V(\mathbf{w}))$ has the same $p$-adic valuation as the unshifted prefix $S_n^{(P)} = \sum_{d=0}^r \gamma_d T_d(n)$, where $T_d(n) := \sum_{2^{i_1} + \cdots + 2^{i_d} \le n} \prod_{\ell=1}^d (d_{i_\ell} b^{-2^{i_\ell}})$.

Fix an epoch index $M$ large enough that $\kappa_M - \kappa_{M-1} > \log_2 r$ (so $r \cdot 2^{\kappa_{M-1}} < 2^{\kappa_M}$) and $M > a_0$, and consider any $1 \le j \le r$ and any shift $n$ in the $j$-th interval of epoch $M$: namely $[j \cdot 2^{\kappa_M} + (r - j) 2^{\kappa_{M-1}},\; (j + 1) 2^{\kappa_M})$ for $1 \le j \le r - 1$, or $[r \cdot 2^{\kappa_M},\; 2^{\kappa_{M+1}})$ for $j = r$. Set $\mathcal{P}_M := \{\kappa_1, \ldots, \kappa_M\}$. Because $n < 2^{\kappa_{M+1}}$, no tuple with $2^{i_1} + \cdots + 2^{i_d} \le n$ contains any pole $\ge \kappa_{M+1}$. For $d = r$, split $T_r(n) = T_r^{\mathrm{pole}}(n) + T_r^{\mathrm{mix}}(n)$ into pure-pole tuples in $\mathcal{P}_M^r$ and mixed tuples containing at least one non-pole index $k \notin \mathcal{P}_M$.
* **Exact pure-pole identity:** A pure-pole tuple in $\mathcal{P}_M^r$ with $i$ copies of $\kappa_M$ satisfies $2^{i_1} + \cdots + 2^{i_r} \le n$ if and only if $0 \le i \le j$: indeed, $i > j$ exceeds $(j+1)2^{\kappa_M} > n$ (when $j < r$), while for $i = j$ the sum is $\le j \cdot 2^{\kappa_M} + (r - j) 2^{\kappa_{M-1}} \le n$, and for $i \le j - 1$ it is $\le (j - 1) 2^{\kappa_M} + r \cdot 2^{\kappa_{M-1}} < j \cdot 2^{\kappa_M} \le n$. Hence
  $$
  T_r^{\mathrm{pole}}(n) = \sum_{i = 0}^j \binom{r}{i} \alpha_M^i S_{M-1}^{r - i}, \qquad S_{M-1} := \sum_{m = 1}^{M - 1} \alpha_m.
  $$
* **Congruence mod $p^{M - a_0} \mathbb{Z}_p$:** Multiplying by $p^{rM}$, we have $p^M \alpha_M = 1 + p^M \delta_M \equiv 1 \pmod{p^{M - a_0}\mathbb{Z}_p}$ and
  $$
  p^M S_{M-1} = \sum_{m=1}^{M-1} p^{M - m} + p^M \sum_{m=1}^{M-1} \delta_m = \frac{p - p^M}{1 - p} + p^{M - a_0} \sum_{m=1}^{M-1} (p^{a_0}\delta_m) \equiv t_p \pmod{p^{M - a_0}\mathbb{Z}_p},
  $$
  where $t_p := \frac{p}{1 - p} \in p \mathbb{Z}_p$ (as $1 - p \in \mathbb{Z}_p^\times$). Substituting into the integer polynomial $\sum_{i=0}^j \binom{r}{i} X^i Y^{r - i}$ gives
  $$
  p^{r M} T_r^{\mathrm{pole}}(n) \equiv \sum_{i = 0}^j \binom{r}{i} t_p^{r - i} = t_p^{r - j} f_{r, j}(t_p) \pmod{p^{M - a_0} \mathbb{Z}_p}, \qquad f_{r, j}(T) := \sum_{i = 0}^j \binom{r}{i} T^{j - i} \in \mathbb{Z}[T].
  $$
* **Nonvanishing via the rational root theorem:** The polynomial $f_{r, j}(T)$ is **monic** ($\binom{r}{0} = 1$) with integer coefficients. Because $p \ge 3$ is odd, $t_p = -p/(p - 1)$ is a non-integer rational (denominator $p - 1 \ge 2$), so by the rational root theorem $f_{r, j}(t_p) \ne 0$. Hence
  $$
  \nu_{r, j, p} := (r - j) + v_p\bigl(f_{r, j}(t_p)\bigr) = v_p\bigl(t_p^{r - j} f_{r, j}(t_p)\bigr) \in \mathbb{Z}_{\ge 0}
  $$
  is a finite constant depending only on $(r, j, p)$ (even when $p \mid \binom{r}{j}$, e.g., $\nu_{3, 1, 3} = 3$, $\nu_{3, 2, 3} = 2$, $\nu_{4, 2, 3} = 4$; and $\nu_{r, r, p} = 0$ since $f_{r, r}(t_p) = (1 - p)^{-r} \in \mathbb{Z}_p^\times$). Put $\nu_{r, p} := \max_{1 \le j \le r} \nu_{r, j, p}$.
* **Dominance over mixed and lower-degree terms:** Every mixed degree-$r$ tuple has at most $r - 1$ poles (each of valuation $\ge -M$) and at least one non-pole (valuation $\ge -a_0$), so $v_p(\gamma_r p^{rM} T_r^{\mathrm{mix}}(n)) \ge v_p(\gamma_r) + M - a_0$. Every lower-degree term $0 \le d \le r - 1$ has $v_p(\gamma_d p^{rM} T_d(n)) \ge v_{\min}(P) + M$, where $v_{\min}(P) := \min_{0 \le d \le r - 1} v_p(\gamma_d)$. Therefore, once $M \ge M_0(P, b, p)$ satisfies $\kappa_M - \kappa_{M-1} > \log_2 r$, $M - a_0 > \nu_{r, p}$, $M > v_p(\gamma_r) - v_{\min}(P) + \nu_{r, p}$, and $r M > v_p(\gamma_r) + \nu_{r, p}$, the strict ultrametric triangle inequality gives the **exact** $p$-depth
  $$
  e = -v_p\bigl(R_n^{(P)}\bigr) = r M - v_p(\gamma_r) - \nu_{r, j, p} = r M - O_{P, p}(1)
  $$
  uniformly across every pattern sequence $\mathbf{w}$ and every shift $n$ in the $j$-th interval of epoch $M$.

*Complete-period normality.* For large $N$, set $K = \lfloor \log_2 N \rfloor$ and $M = e_K$, so $2^{\kappa_M} \le 2^K \le N < 2^{\kappa_{M+1}}$. Discard the initial prefix $[1, \max(\sqrt{N}, r \cdot 2^{\kappa_{M-1}}))$ together with the $r - 1$ transition slivers $[j \cdot 2^{\kappa_M}, j \cdot 2^{\kappa_M} + (r - j) 2^{\kappa_{M-1}})$ ($1 \le j \le r - 1$) in $[2^{\kappa_M}, N]$; their combined proportion of $[1, N]$ is at most $N^{-1/2} + \bigl(r + \frac{r(r-1)}{2}\bigr) 2^{-(\kappa_M - \kappa_{M-1})}$. Every remaining shift lies either in $[r \cdot 2^{\kappa_{M-1}}, 2^{\kappa_M})$ (the saturated $j = r$ interval of epoch $M - 1$, with exact $p$-depth $r(M - 1) - v_p(\gamma_r) \ge M - 1 - O_P(1)$) or in one of the $j$-th intervals of epoch $M$ ($1 \le j \le r$, with exact $p$-depth $rM - v_p(\gamma_r) - \nu_{r, j, p} \ge M - O_{P, p}(1)$).

Through $N$, the regrouped convolution (3.3) has $O_r((1 + \log N)^r)$ insertion positions. Removing logarithmic tail buffers $C_P \log N$ before each insertion and before $N$ (keeping the real tail error $\ll_{P, b} N^{-2}$), together with any resulting sub-run shorter than $N^{1/3}$, discards a further proportion $O_{P, r}(N^{-2/3}(\log N)^r) \ll_{P, b, p} N^{-1/2}$. On each retained run of length $T' \ge N^{1/3}$, the complementary prime-to-$bp$ denominator $Q$ divides $D_P' (Q_0 \Lambda_M)^r$, where $Q_0$ is the prime-to-$bp$ part of $b^{P_K} - 1$. Since $\operatorname{ord}_{Q_0}(b) \mid P_K$ (a power of $2$) and $p \nmid Q_0$, lifting to $Q_0^r$ preserves $v_p(\operatorname{ord}_{Q_0^r}(b)) = 0$. Meanwhile $\Lambda_M \le 2^{M/4}$ gives $\operatorname{ord}_{\Lambda_M^r}(b) \le 2^{r M / 4}$ and $v_p(\operatorname{ord}_{\Lambda_M^r}(b)) \le \log_p(\Lambda_M) \le \frac{M}{4 \log_2 p} \le \frac{M}{6}$ (as $p \ge 3$). Hence the stride $\tau = \operatorname{lcm}(t, \operatorname{ord}_Q b)$ satisfies $\log_2 \tau = O_{P, b}(M)$ (using $P_K \le 1 + M$) and $A(b^\tau) = a_0 + v_p(\operatorname{ord}_Q b) \le \frac{M}{6} + O_P(1)$.

For every $1 \le h \le H_{\mathrm{ET}} := \lfloor p^{M/4} \rfloor$, the reduced pole exponent $e(h) = e - v_p(h)$ of $h R$ satisfies $e(h) \ge \frac{3}{4} M - O_{P, p}(1) > A(b^\tau)$ on both epoch $M - 1$ and epoch $M$. Crucially, because $\kappa_{m+1} - \kappa_m \to \infty$, Cesàro averaging implies $\kappa_m / m \to \infty$; since $\kappa_M \le K \le \log_2 N$, it follows that $M = e_K = o(K) = o(\log N)$ as $N \to \infty$. Therefore the complete period $\tau p^{e(h) - A(b^\tau)}$ satisfies $\log_2(\tau p^{e(h)}) = O_{P, b, p}(M) = o_{P, b, p}(\log N)$, so $\tau p^{e(h)} = N^{o(1)} \ll N^{1/3} \le T'$ for all large $N$ (and likewise $N^{-1/2} \le 2^{-K/2} \ll_{p, \kappa} p^{-M/4}$). Pure complete-period cancellation yields
$$
\frac{1}{T'} \left|\sum_{j < T'} e(h b^j R)\right| \le \frac{\tau p^{e(h)}}{T'} \le N^{-1/3 + o(1)},
$$
and the tail buffer contributes $O_{P, b}(h N^{-2}) = O_{P, b}(N^{-2 + o(1)})$. Erdős–Turán up to $H_{\mathrm{ET}} = \lfloor p^{M/4} \rfloor$ gives $D(\text{run}) \ll_{P, b, p, \kappa} p^{-M/4}$ (including the saturated epoch $M - 1$ runs, since $p^{-(M-1)/4} = p^{1/4} p^{-M/4}$), proving (2).

*Sharper uniform irrationality measure (3.2).* Put $U_k = \sum_{i \le k} d_i b^{-2^i}$, $q_k = \operatorname{den}(U_k)$, and $E_k = D_k (b^{P_k} - 1)$ (since $P_{k-1} \mid P_k$, $(b^{P_{k-1}} - 1) \mid (b^{P_k} - 1)$, so $E_k d_i \in \mathbb{Z}$ for all $i \le k$). Here $\log E_k = O_{b, p}(1 + e_k)$. As shown above, $0 < |E_k d_k| \ll_b E_k$ for all $k > k_0(a_0)$. Over $E_k b^{2^k}$ the numerator is congruent to $E_k d_k \pmod{b^{2^{k-1}}}$, so for large $k$ both numerator and denominator of $q_k / b^{2^k}$ in lowest terms are $\exp(O_{b, p}(1 + e_k))$. Thus $U_{k+1} = U_k + z_k / q_k^2$ with $z_k = d_{k+1} (q_k / b^{2^k})^2 \ne 0$ having both reduced heights $\exp(O_{b, p}(1 + e_{k+1}))$. Iterating Phase 23 Lemma 5 ($H_{k+1} \le \max(\log(1/|z_k|), H_k + \log 2 + 2 \log |c_k^*|)$) from a fixed $k_0$ yields
$$
-\log F(U_K) = H_K \le C_{b, p} \sum_{k = 1}^K (1 + e_{k + 1}) \le C_{b, p} K (1 + e_{K + 1}).
$$
For large $q$, choosing the first $K$ with $2^K \ge 4 \log_b q$ gives $K = \log_2 \log_b q + O(1)$, $q_K > q$, $|V(\mathbf{w}) - U_K| \ll_b q^{-8}$, and $\|q V(\mathbf{w})\| \ge F(U_K)/q - O_b(q^{-7})$, proving (3.2) uniformly for large $q$; compactness of $\prod_k \{1, 2\}^{P_k}$ and continuity handle small $q$ as in Phase 24 §4.

*Injectivity and exact baseline-difference irrationality criterion.* Suppose $\mathbf{w} \ne \mathbf{w}'$ first differ in shell $k$ (with $2 P_k \le 2^k$) at site $i_0 \in \{1, \ldots, P_k\}$. The jump at $2^k + i_0$ is $b^{-2^k - i_0}$, while the maximum tail difference after $2^k + i_0$ is $\sum_{m > 2^k + i_0} b^{-m} = \frac{1}{b - 1} b^{-2^k - i_0}$, strictly smaller for $b \ge 3$; for $b = 2$, equality would require $w_{k, i_0} = 2$ and all later sites $1$ (versus $1$ and all later sites $2$), impossible because $2 P_k \le 2^k$ repeats $w_{k, i_0}$ at $2^k + i_0 + P_k$. Thus $\mathbf{w} \mapsto V(\mathbf{w})$ is injective. Finally, subtracting the all-ones baseline $\mathbf{w}^{\mathbf{1}}$ gives
$$
V(\mathbf{w}) - V(\mathbf{w}^{\mathbf{1}}) = \sum_{n \ge 3} \varepsilon_n(\mathbf{w}) b^{-n}, \qquad \varepsilon_n(\mathbf{w}) \in \{0, 1\}.
$$
If $(\varepsilon_n(\mathbf{w}))_{n \ge 3}$ is eventually periodic, the series sums to a rational number. Conversely, if $(\varepsilon_n(\mathbf{w}))_{n \ge 3}$ is not eventually periodic, then in particular it cannot end in $1^\infty$ (or $(b - 1)^\infty$), so it is the unique canonical base-$b$ expansion of $V(\mathbf{w}) - V(\mathbf{w}^{\mathbf{1}})$ for every integer base $b \ge 2$, and therefore $V(\mathbf{w}) - V(\mathbf{w}^{\mathbf{1}})$ is irrational. $\square$

### Strict separation: representation properties vs intrinsic real properties

| Construction | Representation properties (expansion-dependent) | Intrinsic real-number properties |
| --- | --- | --- |
| **Theorem 3.2** ($V(\mathbf{w})$, closed-form deterministic) | Full density $n_j = j$, positive bounded locally varying coefficients ($2^{P_k}$ choices/shell), all-prime raw prefix denominators $D_k = p^{e_k} \Lambda_{e_k}$; second (signed) doubling form drives proofs | $\mu = 2$ with uniform defect $\exp(-C (\log\log 3q)\,\psi(\log\log 3q))$; polynomial normality in base $b$ for every degree $r \ge 1$ |
| **Theorem 2.4(3)** ($Z = x - \lfloor x - S \rfloor$, computable selection) | Full density $n_j = j$, distinct prime $\ell_n$ at every site $n$ with prefix denominator $\prod_{n \le N} \ell_n$, base-$b$ normal individual-site digits $d_n$ | **Badly approximable** ($q\lVert qZ\rVert > \frac{1}{M+2}$, zero $\log q$ loss); **absolute** polynomial normality in **every** integer base $b \ge 2$ |

---

## 4. Prior-art and attribution notes

* **Fourier decay on bounded partial quotients ($F_M$) and nonlinear pushforwards:** Kaufman (1980, *Continued fractions and Fourier transforms*, Mathematika 27, 262–267) introduced continued-fraction stopping-time measures and large-sieve Fourier decay on $F_M$ ($M \ge 3$, $\dim_H > 2/3$), establishing existence of normal numbers with bounded partial quotients via Davenport–Erdős–LeVeque (1963). Queffélec–Ramaré (2003, Enseign. Math. 49, 335–356) lowered the threshold to $\dim_H > 1/2$ (including $F_2$). Jordan–Sahlsten (2016, Math. Ann. 364) extended polynomial decay to Gauss-map Gibbs measures of $\dim_H > 1/2$. Hochman–Shmerkin (2015, Invent. Math. 202) proved pointwise absolute normality for self-conformal measures on $F_2$ and their $C^1$ diffeomorphism images (used in Phase 24 §3). Recent breakthroughs by Sahlsten–Stevens (2024, Amer. J. Math.), Algom–Rodriguez Hertz–Wang (2023/2026, arXiv:2306.01275), and Baker–Banaji (2025, Math. Ann.) established polynomial Fourier decay for nonlinear self-conformal measures and nonlinear pushforwards via Dolgopyat's method / renewal theory; our Theorem 2.3 instead uses an elementary Kaufman-style two-block large sieve that yields fully explicit rational constants and thresholds suitable for direct computable cylinder selection.
* **Computable normal numbers and Diophantine constraints:** Sierpiński (1917) gave an explicit analytic construction of an absolutely normal number, later given a computable reformulation by Becher–Figueira (2002); Turing (c. 1938, unpublished manuscript, *Collected Works* 1992) gave the first algorithm for a computable absolutely normal number; Becher–Heiber–Slaman (2013) and Lutz–Mayordomo (2021) brought the complexity down to polynomial and nearly linear time. Becher–Heiber–Slaman (2015, Math. Comp. 84, 2939–2952) constructed a computable absolutely normal Liouville number (while Becher–Bugeaud–Slaman 2016, Proc. AMS 144, 1509–1521 characterized irrationality exponents of computable reals without normality), and Scheerer (2017, arXiv:1701.07979) and Becher–Yuhjtman (2024) constructed computable numbers simultaneously absolutely normal and continued-fraction normal (which necessarily have **unbounded** partial quotients). Our literature search did not locate a published construction of a **computable badly approximable** real number whose nonconstant rational polynomial images are all absolutely normal; per repository rules, priority is provisional and a literature search finding nothing does not establish novelty.
* **Kloosterman sums and modular hyperbolas:** The elementary fourth-moment bound $|S(u, v; p)| \ll p^{3/4}$ originates with Kloosterman (1926); the prime-power stationary-phase argument originates with Salié (1931) and Estermann (1961); the optimal $q^{1/2}$ bound is due to Weil (1948) and Estermann (1961, Mathematika 8, 83–86).
* **Continued-fraction folding:** Exact reciprocal folding $u \pm 1/(m q^2)$ originates with Mendès France (1973), Shallit (1979), and van der Poorten–Shallit (1992).
* **Gaps between sums of powers:** Two-square gaps of order $\frac{390}{449} \log M$ are due to Dietmann–Elsholtz–Kalmynin–Konyagin–Maynard (2022, IMRN). Arbitrarily long sublogarithmic gaps between sums of three nonnegative cubes ($\gg \sqrt{\log N}/(\log\log N)^2$) are due to Ghidelli (2020, JLMS, doi:10.1112/jlms.12312), while the weighted mild-gap tail bound $\sum_{j \ge 0} r_3^{(0)}(n + K + j) 2^{-j} \le 60(\log T)^C$ ($\log N \asymp T$) used for cubic theta-series irrationality is established in Ghidelli (arXiv:1910.05076v1).

Cross-model review is not independent human peer review.

---

## 5. External inputs and internal Phase 21–24 dependencies

### External published/preprint inputs

Every theorem in this note except Regime B ($M = 14$ and $M = 30$) of Lemma 2.1(3) / Theorems 2.3–2.4 and the Ghidelli-based parts of Theorem 1.3(2)–(3) uses **zero external inputs**. The external inputs used in those specific items are:

1. **Estermann (1961, *On Kloosterman's sum*, Mathematika 8, 83–86) + Weil (1948)** — used **only** for Regime B of Lemma 2.1(3), Theorem 2.3, and Theorem 2.4 ($M = 14, L = 4$ and $M = 30, L = 2$):
   * *Statement:* For every integer $q \ge 1$ and all $u, v \in \mathbb{Z}$, $|S(u, v; q)| \le \tau(q) \gcd(u, v, q)^{1/2} q^{1/2}$.
   * *Hypothesis verification:* Applies unconditionally to every modulus $q \ge 1$ and all integer frequencies $u, v \in \mathbb{Z}$ appearing in the discrete Fourier expansion of $B_I(x) B_J(-\bar{x})$ in Lemma 2.1(3). (Not used in Regime A, where Lemma 2.1(1) proves $|S(u, v; q)| \le 2\tau(q)\gcd(u,v,q)^{1/4} q^{3/4}$ from scratch.)
2. **Ghidelli (arXiv:1910.05076v1, Definition 3.2, Lemma 7.1, §§8.1–8.2; building on the cubic gap theorem of Ghidelli 2020, JLMS, doi:10.1112/jlms.12312)** — used **only** for Theorem 1.3(2)–(3) (the conditional Ghidelli barrier illustration and the residue-boosted cubic criterion):
   * *Statement:* For arbitrarily large parameters $T$ (with $\log N \asymp T$), there exist mild-gap starts $n \in [1, N - K)$ with gap length $K \gg \sqrt{T} / (\log T)^2$ such that $r_3^{(0)}(n) = \cdots = r_3^{(0)}(n + K - 1) = 0$ and $\sum_{j \ge 0} r_3^{(0)}(n + K + j) 2^{-j} \le 60(\log T)^C$ for an absolute constant $C > 0$, where $r_3^{(0)}$ counts ordered nonnegative representations as sums of three cubes.
   * *Hypothesis verification:* Positive-coordinate representations satisfy $c_m \le r_3^{(0)}(m)$ and $B = b^t \ge 4 > 2$, so every nonnegative gap is also a gap of $C_s(3)^3$ and $H_{n - 1} \le 60(\log T)^C$ unconditionally for every $b \ge 2, p \nmid b, s \ge 1$. Because Ghidelli's theorem places $n < N$ without asserting $\log n \asymp \log N$, we state the residue-boosted criterion directly in terms of $(\log T_k)^C$ and state the sublogarithmic-gap barrier on Ghidelli's starts conditionally on both $K_k = o(\log M_k)$ and $e_k \sim s \log_p M_k$.

### Internal Phase 21–24 dependencies

Several proofs also invoke earlier in-repository `Paper proof` results from Phases 21–24 (each subject to its own repository review status, and not independently human peer-reviewed):
* **Phase 24 eq. (2)** (sufficient gap-only irrationality condition): used in Theorem 1.3(3);
* **Phase 24 eq. (4)** (exact low-residue recurrence on $[M, M + G)$): used in Theorems 1.1–1.2;
* **Phase 24 §3 eq. (6) and convergent inequality** ($q\|qx\| > 1/(M + 2)$): used in Theorem 2.4(1) and (3);
* **Phase 23 §2 Theorem (A)** (density-$1$ consecutive-arrival packets for $d = 2$): referenced in Theorem 1.1(2);
* **Phase 23 Lemma 5** (rational folding inequality $F(u + z/q^2) \ge \min(|z|, F(u)/(2 c^2))$): used in Theorem 3.2(3);
* **Phase 21 Prop. D** (density-$1$ prefix-denominator growth $q_M \ge M^{s - o(1)}$): referenced in the Remark after Theorem 1.3.

---

## 6. Reproduction instructions and exact finite verification

Run:
```bash
python -B scripts/phase25_nonlinear_approx.py
```
Exit code `0` certifies every check listed below. Exact integer and `Fraction` certificates are strictly separated from the floating-point sanity measurements.

### Exact finite certificates (exact integer / `Fraction` arithmetic)

* **F1 single-packet obstruction and local discrepancy bounds (Theorem 1.1):** On exact square ($d = 2, p = 3, s = 2, b = 2, a = 2, h = 2$: $M = 162, E = 8, L = 9, K = 12$) and cube ($d = 3, p = 3, s = 2, b = 2, a = 1, h = 2$: $M = 81, E = 6, L = 6, K = 12$) windows, all $729 + 81 = 810$ high-digit lifts $u \in \{0, \ldots, p^{E - h} - 1\}$ are tested across **every** site $y \in [M, M + K]$ ($10{,}530$ site checks) and **every** qualifying aggregate pair $M \le u_1 < v_1 \le M + K$ with $w_B + v_p(v_1 - u_1) < h$ ($45{,}360$ pair checks), preserving exact denominator $p^E$, low residue mod $p^h$, scaled phase $\{p^{E-h} R_y\}$, and every qualifying aggregate difference denominator and low residue. Using an exact positive rational tail $T_{M+K} = 1/(7 B^4)$ propagated backward by $T_m = (T_{m+1} + c_{m+1})/B$, the lifts realize all $512$ length-$9$ and all $64$ length-$6$ binary words, and the explicit all-zero witnesses $0^9$ and $0^6$ satisfy the exact local discrepancy lower bounds $\ge 47/72$ and $\ge 7/12$.
* **F1 lag-$\delta$ grids and flagship cube $3$-adic cancellation (Theorem 1.2):** $68$ exact translated uniform lag-$\delta$ grids (spacing $p^{2w + \ell}$, multiplicity $p^{w + \ell}$) verified across $(p, B) \in \{(3, 4), (3, 10), (5, 16)\}$; exact $3$-adic congruences $\Delta_j = 7 + 27r(r+1)$, $4^{j^3}(4^{\Delta_j} - 1) \equiv 4(4^7 - 1) \pmod{81}$, and $\equiv 4(4^7 - 1) + 81(r^2 + 2r) \pmod{243}$ verified for all $r \bmod 27$; flagship cube consecutive selected-arrival collapse verified for $k = 3, \ldots, 7$ with exact distinct counts $[1, 2, 4, 11, 31]$.
* **F1 one-gap + low-residue iff characterization and flagship cube drops (Theorem 1.3):** Real-data regression test on $C_1(2)^2$ ($b = 2, B = 4, p = 3, s = 1, M = 10$) certifies $R_{10} = 202802/3$, $T_{10} < 1/6$, $Q' = 2/\gcd(2, 4^{10}) = 1$, exclusion of $2X \in \mathbb{Z}$ at $T_{\max} = 1/6$, and an explicit rational witness $X' = 1/2$ at $T_{\max} = 1/3$. Systematic iff verification over $2{,}322$ configurations across $b \in \{2, 3, 5, 6, 10\}$, $p \in \{3, 5\}$ ($p \nmid b$), $M \in \{1, 10\}$, $e \in \{2, 3\}$, $0 \le h \le e$, $Q \in \{1, 2, 3, 4, 5, 6, 9, 10, 15\}$ (including all configurations with $\gcd(Q, B^M) > 1$) certifies (1.1), automatic coprimality at $h = 0$, strict exclusion below $r_{\min}/(Q' p^e)$, and explicit rational impostors $X' = (N + \widetilde{A}_M/p^e + \widetilde{T})/B^M$ with $Q X' \in \mathbb{Z}$. For the flagship cube $C_1(3)^3$ ($b = 2, p = 3, s = 1, B = 4$) through $M = 2200$, exact convolution certifies all $5$ prefix-denominator drops at $M \in \{783, 820, 953, 1161, 1268\}$ with $e(1268) = 0$, $e(2186) = 4$, and first $e = 6$ attained at $M = 2187$.
* **F2 elementary Kloosterman identities, trapezoid split sums, and zeta constants (Lemma 2.1):** Exact fourth-moment solution count $3(p - 1)(p - 2)$ (and $1$ at $p = 2$) verified for $p \in \{2, 3, 5, 7, 11, 13\}$; prime-power quadratic-congruence counts verified across $9$ prime powers $p^k \in \{4, 8, 16, 32, 9, 27, 81, 25, 125\}$; non-vacuous exact trapezoid majorant properties ($72$ interval pairs) and Fourier-tail split-sum bounds $< 5q/d$ ($367$ divisor/length checks across $q \in \{13, 16, 21, 25, 30, 37, 45, 60\}$, maximum achieved ratio $0.4952 < 1$); and exact integer-root certificates proving $\zeta(7/4) < 2$ ($50\zeta(7/4) + 20 < 120$) and $\zeta(3/2) < 14/5$ ($25\zeta(3/2) + 20 < 90$).
* **F2 block-measure certificates, Fourier exponents, computable rational majorants, and $L^2$ martingale step (Lemma 2.2, Theorems 2.3–2.4):**
  * All hand-checkable inequalities for $M = 100, L = 52, s = 19/20$ ($5 \cdot 5^2 > 11^2$, $261/96 < 11/4$, $(11/4)^2 < (3/2)^5$, $(11/4)^2 < 8$, Bernoulli factors, and $2^{155} > 3 \cdot 11^{10} \cdot 5^{51}$) as well as $809^{51} \cdot 100^{520} > 2^{19} \cdot 500^{51} \cdot 102^{520}$ certified in exact rational/integer arithmetic.
  * Exact integer $Q$-th root certificates ($D = 10^{18}$): $\Sigma(42, 4, 18/19) > 1.018523$ ($550{,}612$ distinct values of $q_4 + p_4$); $\Sigma(14, 4, 10/11) > 1.014769$ ($8{,}439$ distinct values); $\Sigma(30, 2, 10/11) > 1.025743$ ($337$ distinct values).
  * All $5$ strict rational exponent inequalities in (2.5), both derived inequalities ($2\alpha + 2\beta + \theta < 1$, $\theta < (1 + \rho_{\mathrm{Klo}})\alpha$), and exact margins $(m_{\mathrm{lin}}, m_A, m_B)$ certified in exact `Fraction` arithmetic for all $3$ parameter triples ($s \in \{19/20, 18/19, 10/11\}$); executable rational majorants $(\eta_{r,s,\rho}, \bar{\xi}_0(P), \bar{C}(P), \bar{K}_e, J_e)$ certified on sample polynomials of degrees $r = 1, 2, 3$ for the $M = 30, L = 2$ measure.
  * Exact submultiplicativity, $\det = +1$, uniqueness of $(p, q)$, and $w(\mathbf{a}) \le q(\mathbf{a})^{-2s}$ certified on the $10{,}000$ depth-$4$ block concatenations drawn from $\{1, \ldots, 10\}^2 \times \{1, \ldots, 10\}^2$ of the certified $M = 30, L = 2$ measure; exact Weyl square-subsequence bound $2(N - j^2)/N \le 4/j$ ($1 \le j < 30$) and exact rational child-selection averaging algebra verified on the actual $900$-child certified $M = 30, L = 2$ probability weights ($m = 0, \ldots, 5$).
* **F3 exact CF folding and locally varying series (Theorems 3.1–3.2):** Exhaustive verification of Theorem 3.1 across all canonical $u = p/q \in (0, 1/2)$ with $3 \le q \le 24$ over the tested parameter ranges: $1{,}780$ zero-loss $c = 1$ folds ($2 \le d_z \le 11$, $\varepsilon \in \{\pm 1\}$) and $4{,}272$ general folds ($2 \le c \le 5$, $2c < d_z \le 2c + 9$ with $\gcd(c, d_z) = 1$, $\varepsilon \in \{\pm 1\}$). Verification of Theorem 3.2 using the exact theorem schedules ($\kappa = (2, 4, 7, 11, 16, 22)$, exact $m_j = 1 + \max(m_{j-1}, 4 \lceil \log_2 \prod_{i \le j} \ell_i \rceil)$ through $j = 12$ with $m_1 = 5$ at $(b, p) = (3, 5)$, and exact $P_k$) across $(b, p) \in \{(2, 3), (3, 5), (6, 5)\}$: power-of-two order valuations $v_p(\operatorname{ord}_{Q_0^r}(b)) = 0$ ($r = 1, 2, 3$, $k \le 22$), auxiliary-prime CRT congruences at $m_1$, exact raw-vs-regrouped identity, strict positivity $d_k \ge 1$ at non-pole steps (including $k = 1$ and $b = 2$), exact raw shifted denominators $D_k$ at every site $n < 2^8$, injectivity across $3$ pattern choices, and exact monic-polynomial pole depths $r M - v_p(\gamma_r) - \nu_{r, j, p}$ verified via $6$ literal `Fraction` checks at $M = 4$ (including $p = 3 \mid \binom{r}{j}$ at $(r, j) = (3, 1), (3, 2), (4, 2)$) and $117$ exact $p$-adic modular checks at $M = 6$ across all $1 \le j \le r \le 4$, $3$ radices, $3$ locally varying patterns, and the non-monomial polynomial $p X^3 + 2 X^2 + X$.

### Clearly separated floating-point measurements (not proof certificates)

* **F2 complex Kloosterman and empirical rectangle-excess sanity checks:** Evaluating $|S(u, v; q)|$ in IEEE-754 floating point over all $u, v \bmod q$ for $q \in \{2, 3, 4, 5, 7, 8, 9, 12, 16, 25, 27\}$ gives maximum ratios $0.2611 \le 1$ against (2.1) and $0.8493 \le 1$ against Estermann's bound. Evaluating empirical modular-hyperbola rectangle excess $|\text{count} - L_1 L_2 (q - 1)/q^2| / \sqrt{q}$ across $48$ rectangles on primes $q \in \{101, 503, 2003\}$ gives maximum ratio $0.4162$. These are numerical sanity measurements only; the proofs of Lemma 2.1(1)–(3) are analytic.

---

## 7. Explicit open questions

1. **Irrationality of $C_1(3)^3$ (`Open`):** Is the flagship cube $C_1(3)^3$ (for $b = 2, p = 3, s = 1, B = 4$) — or $C_s(3)^3$ for any $s \ge 1$ — irrational? By Theorem 1.3(2)–(3), proving irrationality via gap envelopes under the depth hypothesis requires either logarithmic three-cube gaps ($\limsup g/\log M > \frac{s}{\log B}$ on mild/abundant gaps), or real-circle phase control $\limsup \{-Q R_{M_k}\} B^{K_k} / (\log T_k)^C = \infty$ along Ghidelli's mild gaps, or an entirely different non-gap method.
2. **Global distributional bounds at $d = r \in \{2, 3\}$ (`Open`):** Does $C_s(2)^2$ or $C_1(3)^3$ satisfy $D^+ < 1$ or positive lower digit-transition density? By Theorem 1.1, any **single-packet** argument pinning down logarithmic-length digit blocks at a packet start must reach the top $O(1)$ base-$p$ digits of $A_M$; whether multi-packet correlations or a global counter-model can settle $D^+ < 1$ remains open.
3. **Lowering the computable cap $M$ to $M = 2$ (`Open`):** Theorem 2.4 constructs computable badly approximable polynomial-normal numbers in $F_{42}$ (zero external inputs, via Lemma 2.2(3)) and $F_{14}$ (via Weil–Estermann). Can an effective version of Queffélec–Ramaré (2003), Jordan–Sahlsten (2016), or Baker–Banaji / Algom–Rodriguez Hertz–Wang lower the computable cap to $M = 2$ (yielding $q \|q x\| > 1/4$)?
4. **Polynomial-time complexity (`Open`):** Our $L^2$ potential selection algorithm in Theorem 2.4 is fully computable in finite rational arithmetic, but carries steep finite costs: even precomputing the rational block weights $p_{\mathbf{u}}$ at $M = 100, L = 52$ involves summing over $100^{52}$ blocks (finite and guaranteed to halt, though astronomically large; by contrast, $M = 42, L = 4$ has $3{,}111{,}696$ blocks and $M = 30, L = 2$ has only $900$ blocks), and refining sub-cylinders to match $\bar{L}_{e, j} \asymp b_e^{j^2}$ runs in super-exponential time. Can a badly approximable absolutely normal (or polynomial-normal) number be computed in polynomial time (analogous to Becher–Heiber–Slaman 2013)?
5. **Closed-form deterministic series with $(\log q)^{-o(1)}$ defect (`Open`):** Theorem 3.2 reduces the uniform irrationality defect of closed-form deterministic all-prime polynomial-normal series from $\exp(-C(\log\log 3q)^2)$ to $\exp(-C(\log\log 3q) \psi(\log\log 3q))$ for arbitrarily slow $\psi \to \infty$, while any doubling series with permanent off-radix denominator $D_k \ge 2$ incurs at least $\log_2 \log_b q$ folding steps. Can an explicit closed-form algebraic series (without measure selection) attain $\|q W\| \gg q^{-1} (\log 3q)^{-o(1)}$ or bounded partial quotients together with all-prime support and polynomial normality?

---

## 8. Standing research objectives advanced

* **Objective 1 (Establish normality):** Theorem 2.4 constructs computable badly approximable real numbers (and all-prime full-density series) whose nonconstant rational polynomial images are **all absolutely normal** (in every base $b \ge 2$); Theorem 3.2 gives a pure complete-period proof of base-$b$ polynomial normality in all degrees for locally varying full-density all-prime series.
* **Objective 3 (Quantify digit distributions and Diophantine quality):** Theorem 1.2 quantifies lag-$\delta$ scaled-phase discrepancy on $[M, M+G)$ and exhibits $3$-adic derivative cancellation in the flagship cube; Theorem 1.3 gives sufficient cubic irrationality gap thresholds (arbitrary, mild/abundant, and residue-boosted); Theorem 2.4 attains the optimal badly approximable Diophantine rate $q\|qx\| > \frac{1}{M+2}$ simultaneously with absolute polynomial normality; Theorems 3.1–3.2 eliminate folding losses at $c = 1$ and strictly tighten the uniform irrationality measure of deterministic full-density all-prime series.
* **Objective 4 (Establish rigorous mathematical limitations):** Theorem 1.1 establishes a **local single-packet limitation** showing that locking packet innovations, denominators, low residues mod $p^h$ ($h \le (1-\epsilon)e$), scaled phases, aggregate difference denominators, and tails leaves every base-$b$ word of length $L \le \min(tK, \lfloor (e - h)\log_b p \rfloor)$ unconstrained at the start of the packet; Theorem 1.3(1)–(2) gives an exact iff characterization via $Q' = Q / \gcd(Q, B^M)$ proving that one-gap + low-residue certificates using gap envelopes $T_{\max} = H_{\mathrm{ub}} B^{-g_k}$ ($H_{\mathrm{ub}} \ge 1$) cannot exclude even a single rational denominator along sublogarithmic gaps satisfying the depth hypothesis.
