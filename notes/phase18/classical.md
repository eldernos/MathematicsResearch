# Phase 18 Track F: Synthetic Representations of Classical Constants (F1–F5)

**Honest mathematical status.** None of the constructions, groupings, transformations or reductions in this note establishes normality or an asymptotic discrepancy bound $D_\infty < 1$ for $\ln 2$, $\pi$, $e$, $\mathrm{Li}_s(1/b)$ ($s \ge 1$), $\zeta(3)$, or any algebraic irrational such as $\sqrt{2}$, $\sqrt{3}$ or $\varphi = (1+\sqrt{5})/2$. What this note proves is the exact arithmetic structure of positive dyadic groupings of $\ln 2$ (F1), quantitative lower bounds showing why grouping and retirement reproduce the exponential denominator-growth obstruction (F2), a synthesis of nine genuinely different functional transformations (F3), structural obstructions to deterministic-remainder decompositions $\ln 2 = A + B$ (F4), and explicit exact-arithmetic evaluations across the six named classical targets (F5), including two new sharp results outside $\ln 2$: (i) a four-line proof that **no** finite nonempty subset of factorial terms $\sum_{k \in G} 1/k!$ with $\max G \ge 3$ can ever sum to a dyadic rational (Theorem F5.2), and (ii) explicit $\pi$-free rounded Chebyshev-pole integrals using even $T_{2D}(x)$ that cut the shifted binary denominator rate of $\pi$ below $2/3$ to $0.29975$ (Machin), $0.24965$ (Størmer) and arbitrarily close to $0$ (Theorem F5.1), though without shift persistence.

All finite assertions, exact rational sums, period checks, prime-delay counts, cross-ray counterexamples, Frobenius checks, Chebyshev-pole certificates, exhaustive factorial-subset checks and Padé/Apéry/Catalan evaluations are verified in exact arithmetic by [`scripts/phase18_classical.py`](../../scripts/phase18_classical.py). Throughout, $\log$ denotes the natural logarithm unless a base is written explicitly, and $v_p$ denotes the $p$-adic valuation.

## 0. Summary of established results and open boundaries

| Track | Main result | Evidence & status | What remains open |
| --- | --- | --- | --- |
| **F1** | Exact preperiod $a = v_2(\mathrm{ord}_d(2))$ and minimal eventual period $P_d = \mathrm{lcm}(\mathrm{ord}_d(2), \mathrm{ord}_{u_0}(2))$ of $r_d(j) = 2^{-(d 2^j + j)} \bmod d$; constructive partition of every odd ray $d \ge 3$ into finite dyadic-valued groups of size $\le d$; exact reduced denominator $2^{d 2^{j_{\max}} + j_{\max}}$ (no $2$-adic drop on single rays). | Paper proofs (Theorems F1.1–F1.3) + exact checks on all odd $d \in [3, 199]$. | Optimal minimal-span partition algorithms across arbitrary composite $d$. |
| **F2** | Universal prime delay ($m' \ge 2p$) for any positive grouping; superlinear worst-case single-ray retirement $R(G(p)) > p(\log_2(3p/2) - \log_2\log_2(3p/2))$, typical-prime delay $> p^{3/2}/\log p$, $1 - O(1/\log N)$ of all primes $\le N$ and $\ge \log 2 \approx 69.3\%$ of all odd rays $\le N$ open at cutoff $N$; cross-ray $2$-adic drop witness $G = \{5, 8, 10\}$ ($E_{\max} = 11$, $e_{\mathrm{red}} = 10$); Strategy A/B1/B2 persistence of the exponential obstruction. | Paper proofs (Theorems F2.1–F2.4, Proposition F2.3) + exact counts to $N = 5000$. | Whether non-positive (signed) non-Taylor groupings outside the balanced trace alphabet can keep both $q_N$ polynomial and shift persistence. |
| **F3** | Evaluation of 9 transformation classes (telescoping, geometric cancellation, logarithmic functional equations, Lambert series, polylogarithms, algebraic traces, Chebyshev poles, Padé/Hermite–Padé, Stoneham-ray sums); horizontal dyadic-ray sum $\ln 2 = \sum_{d\text{ odd}} L_d$ decomposes $\ln 2$ into Rauzy-deterministic summands. | Paper proofs (Theorem F3.1) + synthesis of Phases 10–16 + cross-reference to [`summation.md`](summation.md). | Any transformation of $\ln 2$ yielding a surviving fixed-support prime axis with controlled remainder. |
| **F4** | Complement denominator persistence: for any finite prime set $P$, $B_P = \ln 2 - A_P$ retains identical Frobenius residues at every $p > \max P$ ($p^2 > N$) and exact odd-denominator rate $1$. Uniqueness of deterministic remainders across any family with normal pairwise differences. | Paper proofs (Theorems F4.1–F4.2) + 0 Frobenius mismatches for $P = \{2,3\}, \{2,3,5\}$ through $N = 256$. | Any non-circular decomposition $\ln 2 = A + B$ with $A$ normal and $B$ provably normality-preserving. |
| **F5** | Exact shifted binary denominator rates and grouping obstructions for $\pi$ (BBP $3/2$, Bellard $1$, Gaussian Machin $2/3$, new $\pi$-free Chebyshev poles $\le 0.29975, 0.24965, \to 0$; the two original BBP slots with odd denominator part $p$ retain $p$), $e$ (complete impossibility of positive dyadic factorial groups with $\max G \ge 3$; Taylor rate $\ln 2$, Padé rate $(\ln 2)/2$), $\mathrm{Li}_s(1/b)$ (exact rate $s$), $\zeta(3)$ (Apéry series / convergents $\le 0.64149$, Broadhurst BBP), Erdős–Borwein $E$ (benchmark status), and algebraic irrationals (Catalan dyadic series with odd denominator $1$ vs. Pell optimal odd rate $(\ln 2)/2$). | Paper proofs (Theorems F5.1–F5.3) + exact checks in `phase18_classical.py`. | Normality or $D_\infty < 1$ for $\pi, e, \mathrm{Li}_s(1/b), \zeta(3), \sqrt{2}, \varphi$; limiting word law for $E$. |

---

## F1. Grouping Taylor terms of ln 2 into dyadic rationals

Write every positive integer uniquely as $m = d \cdot 2^j$ with $d \ge 1$ odd and $j \ge 0$. The standard binary Taylor series of $\ln 2$ splits into odd-$d$ rays:

```math
\ln 2 = \sum_{m=1}^{\infty} \frac{1}{m 2^m}
= \sum_{\substack{d \ge 1 \\ d \text{ odd}}} \sum_{j=0}^{\infty} \frac{1}{d \cdot 2^{e(d,j)}},
\qquad e(d, j) := d \cdot 2^j + j.
```

For $d = 1$, every term $2^{-(2^j + j)}$ is already a dyadic rational (odd denominator $1$), so each singleton $\{j\}$ is dyadic-valued. Fix an odd integer $d \ge 3$. For any finite nonempty subset $G \subset \mathbb{N} = \{0, 1, 2, \dots\}$ with $J = \max G$, set $E(G) := e(d, J) = d \cdot 2^J + J$ and

```math
S_d(G) := \sum_{j \in G} \frac{1}{d \cdot 2^{e(d, j)}} = \frac{M_d(G)}{d \cdot 2^{E(G)}},
\qquad M_d(G) := \sum_{j \in G} 2^{E(G) - e(d, j)}.
```

Because $\gcd(2, d) = 1$, the rational number $S_d(G)$ belongs to $\mathbb{Z}[1/2]$ (its odd denominator $d$ cancels completely) if and only if $d \mid M_d(G)$, equivalently

```math
\sum_{j \in G} r_d(j) \equiv 0 \pmod{d},
\qquad r_d(j) := 2^{-e(d, j)} \bmod d \in (\mathbb{Z}/d\mathbb{Z})^\times.
```

### Theorem F1.1 (Exact preperiod and minimal eventual period of the ray residues)

*Let $d \ge 3$ be odd, let $t = \mathrm{ord}_d(2)$, write $t = 2^a u$ with $a = v_2(t) \ge 0$ and $u$ odd, and put $u_0 = u / \gcd(u, d)$. Then the residue sequence $r_d(j) = 2^{-e(d,j)} \bmod d$ ($j \ge 0$) has:*
1. *exact preperiod length $a = v_2(\mathrm{ord}_d(2))$ (purely periodic from $j = 0$ if and only if $t$ is odd); and*
2. *exact minimal eventual period $P_d = \mathrm{lcm}(t, \mathrm{ord}_{u_0}(2)) \le t \cdot \varphi(u_0) \le \varphi(d)^2$.*

**Proof.** Since $2$ has exact order $t$ modulo $d$, we have $r_d(j + P) = r_d(j)$ if and only if $e(d, j + P) \equiv e(d, j) \pmod{t}$, that is,

```math
d \cdot 2^j (2^P - 1) + P \equiv 0 \pmod{t}.
```

*Periodicity from $j \ge a$ with period $P_d$:* By definition $t \mid P_d$, and $\mathrm{ord}_{u_0}(2) \mid P_d$ implies $u_0 \mid (2^{P_d} - 1)$, hence $u \mid d(2^{P_d} - 1)$ for every $j \ge 0$. Since $j \ge a$, we also have $2^a \mid 2^j$, so $t = 2^a u$ divides $d \cdot 2^j (2^{P_d} - 1) + P_d$.

*Minimality of $P_d$:* Suppose $e(d, j + P) \equiv e(d, j) \pmod{t}$ holds for all $j \ge j_0$ and some $P \ge 1$. Subtracting the congruence at $j$ from the congruence at $j + 1$ gives $d \cdot 2^j (2^P - 1) \equiv 0 \pmod{t}$ for all $j \ge j_0$. Modulo the odd part $u$, $2^j$ is a unit, so $u \mid d(2^P - 1)$, equivalently $u_0 \mid (2^P - 1)$, forcing $\mathrm{ord}_{u_0}(2) \mid P$. Substituting $d \cdot 2^j (2^P - 1) \equiv 0 \pmod{t}$ back into the original congruence forces $P \equiv 0 \pmod{t}$. Hence $P_d = \mathrm{lcm}(t, \mathrm{ord}_{u_0}(2)) \mid P$.

*Sharpness of preperiod $a$:* If $a \ge 1$, then $P_d \ge 1$ makes $2^{P_d} - 1$ odd, and $d$ is odd. At $j = a - 1$, $v_2(d \cdot 2^{a-1}(2^{P_d} - 1)) = a - 1 < a$, whereas $2^a \mid t \mid P_d$, so $e(d, a - 1 + P_d) - e(d, a - 1) \equiv 2^{a-1} \not\equiv 0 \pmod{2^a}$. Thus $r_d(a - 1 + P_d) \neq r_d(a - 1)$. $\square$

`scripts/phase18_classical.py` verifies both the exact preperiod $a$ and the exact minimal eventual period $P_d$ for all $99$ odd integers $d \in [3, 199]$.

### Theorem F1.2 (Existence and explicit bounds for single-ray dyadic partitions)

*For every odd integer $d \ge 3$, the entire index set $\mathbb{N}$ of the $d$-ray can be partitioned into finite nonempty dyadic-valued groups $G \subset \mathbb{N}$ ($S_d(G) \in \mathbb{Z}[1/2]$). Consequently, the entire Taylor series $\ln 2 = \sum_{m \ge 1} 1/(m 2^m)$ admits a partition into finite positive dyadic-valued groups. Specifically, the periodic-block construction gives:*
1. *Every preperiod index $j_0 \in \{0, \dots, a - 1\}$ lies in a group of size $|G| \le d$, span $\max G - j_0 \le a + a(d-1)P_d$ (and for $j_0 = 0$ alone, span $\le a + (d-1)P_d$).*
2. *Every remaining periodic index lies in a block of exact size $|G| = d$ and span $(d-1) P_d$ (or smaller whenever a shorter zero-sum combination of residue classes exists; e.g., for $d = 3$, the explicit partition $\{0, 2\}$ together with $\{2k - 1, 2k + 2\}$ for $k \ge 1$ uses size $|G| = 2$ and span $\le 3$ throughout).*

**Proof.** Partition $\{j \in \mathbb{N} : j \ge a\}$ into the $P_d$ disjoint infinite arithmetic progressions $C_r = \{a + r + k P_d : k \ge 0\}$ ($0 \le r < P_d$). By Theorem F1.1, $r_d(j) = \rho_r \in (\mathbb{Z}/d\mathbb{Z})^\times$ is constant on each $C_r$. For each preperiod index $j_0 \in \{0, \dots, a - 1\}$ in turn, since $\rho_0$ is a unit modulo $d$, there is a unique integer $m(j_0) \in \{1, \dots, d - 1\}$ with $r_d(j_0) + m(j_0) \rho_0 \equiv 0 \pmod{d}$; pair $j_0$ with the next $m(j_0)$ unused elements of $C_0$. Each resulting group has size $1 + m(j_0) \le d$ and residue sum $0 \pmod{d}$. After all $a$ preperiod indices are absorbed (removing at most $a(d-1)$ elements from $C_0$), every remaining progression $C_r'$ ($0 \le r < P_d$) is still an infinite arithmetic progression of constant residue $\rho_r$ and step $P_d$. Partition each $C_r'$ into consecutive blocks of $d$ elements; each block has residue sum $d \rho_r \equiv 0 \pmod{d}$, size $d$, and span $(d - 1) P_d$. For $d = 3$, $a = 1$, $P_3 = 2$, $r_3(0) = 2$, $r_3(2k-1) = 2$, $r_3(2k) = 1$ ($k \ge 1$), so $\{0, 2\}$ and $\{2k - 1, 2k + 2\}$ ($k \ge 1$) partition $\mathbb{N}$ into pairs with residue sum $2 + 1 \equiv 0 \pmod 3$. $\square$

### Theorem F1.3 (Exact reduced dyadic denominator and retirement position on a single ray)

*Let $d \ge 3$ be odd and let $G \subset \mathbb{N}$ be **any** finite nonempty subset with $S_d(G) \in \mathbb{Z}[1/2]$. Let $J = \max G$. Then:*
1. *$M_d(G)$ is an odd positive integer, so $A_d(G) := M_d(G) / d$ is an odd positive integer.*
2. *No $2$-adic cancellation occurs: the exact reduced dyadic denominator of $S_d(G)$ is $2^{e(d, J)} = 2^{d \cdot 2^J + J}$.*
3. *The exact retirement position (the least integer $N \ge 0$ with $2^N S_d(G) \in \mathbb{Z}$) is*

```math
R(G) = e_{\mathrm{red}}(G) = e(d, J) = d \cdot 2^J + J.
```

**Proof.** Because $e(d, j+1) - e(d, j) = d \cdot 2^j + 1 \ge 4$, the exponents $E(G) - e(d, j)$ for $j \in G \setminus \{J\}$ are all strictly positive, while the $j = J$ term contributes $2^0 = 1$. Hence $M_d(G) = 1 + \sum_{j \in G \setminus \{J\}} 2^{E(G) - e(d, j)}$ is odd. Since $d$ is odd and $d \mid M_d(G)$, the quotient $A_d(G) = M_d(G)/d$ is an odd integer. Therefore $S_d(G) = A_d(G) / 2^{E(G)}$ is already in lowest terms, so $v_2(\mathrm{den}(S_d(G))) = E(G)$ and $2^N S_d(G) \in \mathbb{Z} \iff N \ge E(G)$. $\square$

The table below (from `scripts/phase18_classical.py`) records the exact **minimal-span** single-ray dyadic group $G_{\min}(d)$ containing $j = 0$ for small odd $d$, together with its exact reduced dyadic denominator $2^{R}$:

| $d$ | $t = \mathrm{ord}_d(2)$ | $a$ | $P_d$ | $K_{\min} = \max G_{\min}$ | $|G_{\min}|$ | Minimal-span group $G_{\min}$ | Exact retirement $R = d 2^{K_{\min}} + K_{\min}$ |
| ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| 3 | 2 | 1 | 2 | 2 | 2 | $\{0, 2\}$ | 14 |
| 5 | 4 | 2 | 4 | 1 | 2 | $\{0, 1\}$ | 11 |
| 7 | 3 | 0 | 6 | 3 | 3 | $\{0, 1, 3\}$ | 59 |
| 9 | 6 | 1 | 6 | 4 | 4 | $\{0, 2, 3, 4\}$ | 148 |
| 11 | 10 | 1 | 20 | 2 | 2 | $\{0, 2\}$ | 46 |
| 13 | 12 | 2 | 12 | 3 | 4 | $\{0, 1, 2, 3\}$ | 107 |
| 15 | 4 | 2 | 4 | 5 | 4 | $\{0, 2, 4, 5\}$ | 485 |
| 17 | 8 | 3 | 8 | 5 | 2 | $\{0, 5\}$ | 549 |
| 19 | 18 | 1 | 18 | 4 | 4 | $\{0, 1, 2, 4\}$ | 308 |
| 21 | 6 | 1 | 6 | 5 | 3 | $\{0, 1, 5\}$ | 677 |
| 23 | 11 | 0 | 110 | 6 | 6 | $\{0, 1, 3, 4, 5, 6\}$ | 1478 |
| 25 | 20 | 2 | 20 | 5 | 6 | $\{0, 1, 2, 3, 4, 5\}$ | 805 |
| 27 | 18 | 1 | 18 | 5 | 3 | $\{0, 3, 5\}$ | 869 |
| 29 | 28 | 2 | 84 | 7 | 3 | $\{0, 1, 7\}$ | 3719 |
| 31 | 5 | 0 | 20 | 6 | 7 | $\{0, 1, 2, 3, 4, 5, 6\}$ | 1990 |
| 41 | 20 | 2 | 20 | 2 | 3 | $\{0, 1, 2\}$ | 166 |

Already at $d = 29$, the earliest possible single-ray retirement of $m = 29$ occurs at binary shift $R = 3719$.

---

## F2. The delayed-retirement obstruction

Existence of a dyadic partition (Theorem F1.2) does not yield efficiency. The theorems below quantify the unavoidable delay for both single-ray and arbitrary cross-ray positive groupings, distinguish the largest original insertion exponent from the reduced dyadic denominator exponent, and prove that arbitrary positive regrouping reproduces the exponential denominator-growth obstruction in another guise.

### Theorem F2.1 (Universal prime-delay theorem)

*Let $\mathcal{P}$ be **any** partition of $\mathbb{N}_{\ge 1}$ into finite nonempty sets $G_\alpha$ (allowing arbitrary cross-ray combinations) such that $S(G_\alpha) = \sum_{m \in G_\alpha} \frac{1}{m 2^m} \in \mathbb{Z}[1/2]$ for every $\alpha$. For every odd prime $p$, let $G(p) \in \mathcal{P}$ be the unique group containing $m = p$. Then:*
1. *$G(p)$ must contain at least one integer multiple $m' \ge 2p$ of $p$.*
2. *At every Taylor cutoff $N \ge 2$, every odd prime $p \in (N/2, N]$ belongs to an **open (unfinished)** group $G(p)$ satisfying $\min G(p) \le p \le N < 2p \le \max G(p)$.*

**Proof.** In $\mathbb{Q}_p$, $v_p(1/(p 2^p)) = -1$, while $v_p(1/(m 2^m)) = 0$ for every $m$ with $p \nmid m$. Since $S(G(p)) \in \mathbb{Z}[1/2] \subset \mathbb{Z}_p$ satisfies $v_p(S(G(p))) \ge 0$, the ultrametric triangle inequality forces a second term $m' \in G(p)$ with $p \mid m'$, hence $m' \ge 2p$. Item 2 follows immediately from $p \le N < 2p$. $\square$

### Theorem F2.2 (Superlinear worst-case and super-square-root typical delay on single rays)

*Let $p \ge 3$ be an odd prime and let $G \subset \mathbb{N}$ be **any** finite single-ray dyadic group containing $0$ (so $m = p \in \{p \cdot 2^j : j \in G\}$), with $K = \max G \ge 1$. Then:*
1. *(Exact Fermat criterion.) $p$ divides the $p$-independent positive integer*

```math
B(G) := \sum_{j \in G} 2^{2^K - 2^j + K - j},
```

*which satisfies $0 < B(G) < \frac{2}{3} \cdot 2^{2^K + K}$. In particular, $K = 1$ occurs if and only if $p = 5$; $K = 2$ occurs if and only if $p \in \{3, 11, 41\}$; and $K = 3$ occurs if and only if $p \in \{3, 5, 7, 13, 41, 61, 101, 151\}$.*
2. *(Worst-case lower bound for every prime $p \ge 5$.) $2^K + K > \log_2(3p/2)$, whence $2^K > \log_2(3p/2) - \log_2\log_2(3p/2)$, and both the largest Taylor index $m_{\max}(G) = p 2^K$ and the exact retirement position $R(G) = p 2^K + K$ satisfy*

```math
R(G) > m_{\max}(G) > p \left(\log_2\!\left(\frac{3p}{2}\right) - \log_2\log_2\!\left(\frac{3p}{2}\right)\right).
```

3. *(Typical-prime delay and density of open prime rays.) For every $K_0 \ge 1$, the total number of odd primes $p$ (of any size) admitting any single-ray dyadic group with $0 \in G$ and $\max G \le K_0$ is strictly less than $2^{2K_0 + 1}$. Consequently:*
   - *for a proportion $1 - O(1/\log X)$ of all primes $p \le X$, every single-ray dyadic group containing $p$ satisfies $R(G) > p\sqrt{X}/\log X$ (and $R(G) > p^{3/2}/\log p$ on a density-$1$ set of primes);*
   - *at cutoff $N$, a proportion $1 - O(1/\log N) \to 1$ of **all** odd primes $p \le N$ have their initial single-ray group still unfinished (open) at Taylor index $N$.*
4. *(Positive density of all odd rays open.) In any single-ray dyadic partition of $\ln 2$, at least a limiting proportion $\log 2 \approx 69.31\%$ of **all** odd rays $d \le N$ have their initial group $G(d)$ still unfinished at Taylor index $N$.*

**Proof.**
(1) For every $j \in G$, $e(p, K) - e(p, j) = p(2^K - 2^j) + (K - j)$. By Fermat's Little Theorem ($2^p \equiv 2 \pmod{p}$), $2^{e(p,K) - e(p,j)} \equiv 2^{2^K - 2^j + K - j} \pmod{p}$, so $M_p(G) \equiv B(G) \pmod{p}$. Thus $S_p(G) \in \mathbb{Z}[1/2] \iff p \mid B(G)$. The exponents $2^K - 2^j + K - j$ decrease by at least $2$ at the first step ($j = 0 \to 1$) and by at least $3$ at every subsequent step, so $B(G) \le 2^{2^K + K - 1}(1 + 2^{-2} + 2^{-5} + \dots) < \frac{4}{3} \cdot 2^{2^K + K - 1} = \frac{2}{3} \cdot 2^{2^K + K}$.

(2) Since $p \mid B(G)$ and $B(G) > 0$, we have $p < \frac{2}{3} \cdot 2^{2^K + K}$, so $2^K + K > \log_2(3p/2)$. For $p \ge 5$, if $2^K \le \log_2(3p/2) - \log_2\log_2(3p/2)$, then $K \le \log_2(2^K) < \log_2\log_2(3p/2)$, giving $2^K + K < \log_2(3p/2)$, a contradiction. Applying Theorem F1.3 gives the bound on $R(G) = p 2^K + K$.

(3) For a fixed $k \ge 1$, there are $2^{k-1}$ subsets $G \subseteq \{0, \dots, k\}$ containing $0$ and $k$, and each $B(G) < 2^{2^k + k}$ has strictly fewer than $2^k + k$ distinct odd prime divisors (since every odd prime is $\ge 3 > 2$). Summing over $1 \le k \le K_0$ gives at most $\sum_{k=1}^{K_0} 2^{k-1}(2^k + k) < 2^{2K_0 + 1}$ primes. Taking $K_0 = \lfloor \frac{1}{2}\log_2 X - \log_2\log X \rfloor$ excludes at most $2X / (\log X)^2 = O(\pi(X)/\log X)$ primes $p \le X$, leaving $2^K > \sqrt{X}/\log X$ on the remaining primes. For the cutoff-$N$ count, any prime $p \in [\sqrt{N}\log N, N]$ whose group finishes by Taylor index $N$ ($p 2^K \le N$) has $2^K \le \sqrt{N}/\log N$, so at most $2N/(\log N)^2$ such primes can finish, while $\pi(\sqrt{N}\log N) = O(\sqrt{N})$; dividing by $\pi(N) \sim N/\log N$ yields $O(1/\log N)$ finished primes.

(4) Consider all odd integers $d \le N$ whose largest prime factor satisfies $p = P^+(d) > \sqrt{N}\log N$. Write $d = q p$ with $q$ odd, $q < \sqrt{N}/\log N$, and $p \nmid q$. For $G \subset \mathbb{N}$ with $0, K \in G$ to cancel $d$ (hence $p$), Fermat's Little Theorem gives $p \mid B_q(G) := \sum_{j \in G} 2^{q(2^K - 2^j) + K - j} < 2^{q 2^K + K}$. If $d \cdot 2^K \le N$, then $2^K \le \sqrt{N}/(q \log N)$, so $K \le K_q := \lfloor \log_2(\sqrt{N}/(q\log N)) \rfloor$. For fixed $q$, the number of primes $p$ dividing some $B_q(G)$ with $1 \le k \le K_q$ is at most $\sum_{k=1}^{K_q} 2^{k-1}(q 2^k + k) \le 2 q \cdot 2^{2K_q} \le 2N / (q (\log N)^2)$. Summing over odd $q < \sqrt{N}/\log N$ bounds the total number of finished odd rays with $P^+(d) > \sqrt{N}\log N$ by $O(N/\log N) = o(N)$. Meanwhile, by the prime number theorem, the number of odd $d \le N$ with $P^+(d) > \sqrt{N}\log N$ is $\sum_{q \text{ odd} < \sqrt{N}/\log N} (\pi(N/q) - \pi(\sqrt{N}\log N)) \sim \frac{N}{2} \log 2$, which is a proportion $\log 2$ of the $\approx N/2$ odd integers $\le N$. $\square$

Exact checks in `scripts/phase18_classical.py` confirm the rapid convergence of the open prime-ray share toward $100\%$:

| Cutoff $N$ | Odd primes $p \le N$ | Minimal single-ray group finished ($p 2^{K_{\min}} \le N$) | Still open | Open fraction |
| ---: | ---: | ---: | ---: | ---: |
| 200 | 45 | 6 | 39 | 86.67% |
| 1000 | 167 | 10 | 157 | 94.01% |
| 5000 | 668 | 26 | 642 | 96.11% |

### Proposition F2.3 (Largest original insertion exponent vs. actual reduced dyadic denominator)

*For an arbitrary finite positive dyadic-valued group $G \subset \mathbb{N}_{\ge 1}$ (not restricted to a single ray), put $E_{\max}(G) := \max_{m \in G} (m + v_2(m))$ and $e_{\mathrm{red}}(G) := v_2(\mathrm{den}(S(G)))$.*
1. *If $G$ has a unique maximizer of $m \mapsto m + v_2(m)$ (in particular, for every single-ray group), then $e_{\mathrm{red}}(G) = E_{\max}(G)$.*
2. *For cross-ray groups, $e_{\mathrm{red}}(G) < E_{\max}(G)$ can occur because $m \mapsto m + v_2(m)$ is not injective across distinct rays (though at most $1 + \lfloor \log_2 m_{\max} \rfloor$ terms can share any given $E$). The smallest exact positive witness is the three-term cross-ray group $G = \{5, 8, 10\}$:*

```math
S(\{5, 8, 10\}) = \frac{1}{5 \cdot 2^5} + \frac{1}{8 \cdot 2^8} + \frac{1}{10 \cdot 2^{10}}
= \frac{13}{2^{11}} + \frac{1}{2^{11}} = \frac{14}{2^{11}} = \frac{7}{2^{10}},
```

*which has $E_{\max} = \max(5, 11, 11) = 11$ but $e_{\mathrm{red}} = 10$ (a $1$-bit drop). More generally, on any single-ray dyadic group $G_d$ with $K = \max G_d \ge 1$, $M_d(G_d) \equiv 1 \pmod{2^{d 2^{K-1} + 1}}$ implies $A_d(G_d) \equiv d^{-1} \pmod{2^{d 2^{K-1} + 1}}$; hence combining two colliding single-ray dyadic groups at $E = e(d_1, K_1) = e(d_2, K_2)$ always drops $e_{\mathrm{red}}$ by at least $1$ bit, and by at least $\min(v_2(d_1 + d_2), d_1 2^{K_1-1}+1, d_2 2^{K_2-1}+1)$ bits.*
3. *(Archimedean separation floor.) Even under arbitrary cross-ray $2$-adic cancellation, put $R = e_{\mathrm{red}}(G)$ and $G_{> R} = \{m \in G : m > R\}$. If $G_{> R} \neq \emptyset$ and $m^* = \min G_{> R}$, then*

```math
R \ge \frac{\log 2}{1 + \log 2} m^* - o(m^*) \approx 0.40938\, m^*.
```

**Proof.** Item 1 follows from the ultrametric triangle inequality in $\mathbb{Q}_2$. Item 2 is verified directly by exact rational addition. For item 3, $2^R S(G) = 2^R S(G_{\le R}) + 2^R S(G_{> R}) \in \mathbb{Z}$, while $0 < 2^R S(G_{> R}) < 2^{R - m^* + 1}/m^* < 1$. Hence $2^R S(G_{\le R}) \notin \mathbb{Z}$, and its reduced denominator divides $L_R=\mathrm{lcm}(1,\ldots,R)$ because $2^{R-m}$ is an integer for $m\le R$. Hence the positive tail is at least $1/L_R$. Taking logarithms gives $(m^*-R)\log 2\le\log L_R+\log 2-\log m^*$. Since $\log L_R=R+o(R)$ and $R<m^*$, the asserted leading coefficient follows. $\square$

### Theorem F2.4 (Persistence of the exponential denominator-growth obstruction)

*Let $\mathcal{P}$ be any partition of $\mathbb{N}_{\ge 1}$ into finite positive dyadic-valued groups, and at cutoff $N \ge 2$ write $R_N = 2^N \sum_{m=1}^N \frac{1}{m 2^m}$, $C_N = \sum_{\max G \le N} S(G) \in \mathbb{Z}[1/2]$ (completed groups), $U_N^{\le N} = \sum_{\min G \le N < \max G} \sum_{m \in G,\, m \le N} \frac{1}{m 2^m}$ (prefix terms of open groups), and $W_N = \sum_{\min G \le N} S(G) \in \mathbb{Z}[1/2]$ (closing every group meeting $[1, N]$). Then the following three ways of using the partition have the stated limitations:*
1. *(Strategy A: completed groups only.) By Theorem F2.1, every odd prime $p \in (N/2, N]$ is omitted from $C_N$, so by positivity and the prime number theorem,*

```math
2^N(\ln 2 - C_N) \ge \sum_{N/2 < p \le N} \frac{2^{N - p}}{p} \ge 2^{(1/2 - o(1)) N}.
```

*(Exact lower bounds from `scripts/phase18_classical.py`: $\ge 2^{11.22}$ at $N = 32$, $\ge 2^{21.89}$ at $N = 64$, $\ge 2^{55.04}$ at $N = 128$.)*
2. *(Strategy B1: retaining open-group prefixes.) Because $C_N \in \mathbb{Z}[1/2]$ has odd denominator $1$, the identity $R_N = 2^N C_N + 2^N U_N^{\le N}$ gives*

```math
\mathrm{den}_{\mathrm{odd}}(2^N U_N^{\le N}) = \mathrm{den}_{\mathrm{odd}}(R_N) = \exp(N + o(N)),
```

*reproducing the original exponential odd-denominator obstruction verbatim.*
3. *(Strategy B2: closing all open groups.) Closing all groups meeting $[1, N]$ pulls in tail indices up to $M_N \ge 2N - o(N)$ (and $M_N \gg N \log_2 N$ for single-ray partitions) and produces a pure dyadic rational $W_N = A_N / 2^{N + r_N} \in \mathbb{Z}[1/2]$ with odd denominator $1$ and $0 < 2^N(\ln 2 - W_N) < 1/(N+1)$. Because $W_N$ has no odd denominator at all, its doubling orbit $\{2^n W_N\}$ vanishes identically for $n \ge N + r_N$ and for $N \le n < N + r_N$ merely reads off the binary digits of $W_N$ itself: it provides zero incomplete-orbit Weyl cancellation, and proving equidistribution of those $r_N$ bits requires knowing the binary digits of $\ln 2$ directly.*

**Proof.** Items 1 and 2 follow immediately from Theorem F2.1 and the exact denominator growth $\log \mathrm{den}_{\mathrm{odd}}(R_N) = N + o(N)$ (Paper V, `NormalityChecker/DenominatorGrowth.lean`). For item 3, $W_N \in \mathbb{Z}[1/2]$ implies $\{2^n W_N\} = 0$ once $n \ge N + r_N$, and since $W_N$ contains all terms $m \le N$ plus a subset of $m > N$, $0 < \ln 2 - W_N < \sum_{m > N} \frac{1}{m 2^m} < \frac{1}{(N+1) 2^N}$. $\square$

---

## F3. Functional identity synthesis

Because finite positive regrouping of Taylor terms cannot escape Theorem F2.4, we evaluate nine genuinely different transformation families seeking either denominator retirement with a surviving prime axis or a controllable remainder:

| Transformation class | Representative identity for $\ln 2$ | Shifted denominator behavior | Verdict for digit distribution of $\ln 2$ |
| --- | --- | --- | --- |
| 1. Telescoping & Euler acceleration | $\sum \frac{(-1)^{k-1}}{k} \mapsto \sum \frac{1}{m 2^m}$; dyadic telescoping $A_{k,+} + A_{k,-} = A_{2k}$ | Rate $\ge 1/2$ in the real dyadic alphabet (Bang, Paper V / [`strided-logarithm.md`](../strided-logarithm.md)) | Reduces rate $1 \to 1/2$, still exponential; no $D_\infty < 1$. |
| 2. Geometric cancellation & horizontal dyadic rays | $\ln 2 = \sum_{d \text{ odd}} L_d$, $L_d = \frac{1}{d}\sum_{j \ge 0} 2^{-(d 2^j + j)}$ | Each finite sum $\sum_{d \in S} L_d$ has bounded denominator $\mid \mathrm{lcm}(S)$ between exponentially spaced jumps | **Theorem F3.1**: every finite sum is Rauzy-deterministic (zero entropy, $D_\infty > 0$), yet the infinite sum escapes determinism. |
| 3. Logarithmic functional equations | $\ln 2 = \sum c_i \ln(1 - z_i)$, $z_i \in \{\pm 2^{-k}, (\pm 1 \pm i)/2^t\}$ | Optimal rate $5/12$, runner-up $13/30$ (Phase 14 [`gaussian-relations.md`](../phase14/gaussian-relations.md)); adaptive obstruction persists for $\log H_N = o(N)$ and up to $N/528$ (Phase 16 [`adaptive-logarithms.md`](../phase16/adaptive-logarithms.md)) | Rate $0$ at linear height $H_N = e^{\varepsilon N}$ fails shifted error on the integer $c$-line and uses exponential heights; no $D_\infty < 1$. |
| 4. Lambert-series transformations | $\ln 2 = \sum_{m \ge 1} \frac{a_m}{2^m - 1}$, $a_m = \frac{1}{m}\prod_{p \mid m}(1 - p)$ | $P^+(m) \mid \mathrm{den}(a_m)$ for all $m \ge 2$; binary-level head equals Taylor prefix $H_N^{\mathrm{Lam}} = R_N$ identically (Phase 16 [`weighted-lambert.md`](../phase16/weighted-lambert.md)) | All three pillars of Mira Cult's local isolation fail completely for $\ln 2$. |
| 5. Polylogarithm identities | $\mathrm{Li}_2(1/2) = \frac{\pi^2}{12} - \frac{1}{2}(\ln 2)^2$; $\mathrm{Li}_3(1/2) = \frac{7}{8}\zeta(3) - \frac{\pi^2}{12}\ln 2 + \frac{1}{6}(\ln 2)^3$ | $\mathrm{Li}_s(1/2)$ has exact shifted rate $s$ (Theorem F5.3 below); mixes $\ln 2$ with $\pi^2, \zeta(3)$ | Increases denominator rate ($s \ge 2$) and couples distinct classical constants rather than retiring primes. |
| 6. Algebraic field norms & traces | $S_{f,t}(x) = \sum \frac{p_j(f)}{j 2^{tj}}$ for monic $f \in \mathbb{Z}[X]$ | Universal balanced completeness collapses every balanced radius $2^{a/e}$ into $\{A_k, G_t\}$ ($\ge 5/12$); unbalanced sources pay Lagrange $2$-adic penalty $\frac{A-\mu}{t-A}\ln 2$ (Phase 16 [`nonflat-approximants.md`](../phase16/nonflat-approximants.md)) | No balanced algebraic trace of any degree beats $5/12$; 7,495 searched unbalanced degree $2$–$4$ candidates stay $\ge 0.41885$. |
| 7. Chebyshev-pole & integral representations | $\ln 2 = \sum c_i \int_0^1 \frac{dx}{a_i - \sigma_i x}$ with rounded $T_D(2x-1)$ | Breaks $5/12$ with $\ln 2$-free polynomials: $0.39322$ (1 pole), $0.26316$ (2 poles), $\to 0$ ($M$ poles) with $O(1/N)$ error (Phase 16 [`nonflat-approximants.md`](../phase16/nonflat-approximants.md)) | Rounding destroys homogeneous prime-band shift persistence across $N \mapsto N+1$; no linear precision window without linear $2$-adic cost. |
| 8. Padé & simultaneous approximation | Alladi–Robinson/Beukers integrals, asymmetric Legendre, Type I/II Hermite–Padé, Rivoal | Shifted rate $= (1/\tau - e_n/N)\ln 2$; universal floor $\ge (\ln 2)/\mu(\ln 2) \ge 0.1939$ whenever $e_n = o(N)$; all tested unrounded Padé/Legendre $\ge 0.4446$ | Gives irrationality measures and grid exclusions (Rivoal), not binary equidistribution or positive transition density. |
| 9. Sums of Stoneham-type functions | $\ln 2 = \sum_{p \nmid r} T_{2,p,r}$ and fresh-prime geometric-ray partitions | Every finite sum is binary normal and finitely jointly normal (Track D1; see [`summation.md`](summation.md)) | Finite joint normality + convergence does **not** imply normality of the infinite sum (Track D3 counterexamples). |

### Theorem F3.1 (Horizontal dyadic-ray decomposition into deterministic summands)

*For each odd $d \ge 1$, put $L_d := \frac{1}{d} \sum_{j=0}^{\infty} 2^{-(d 2^j + j)}$. Then $\ln 2 = \sum_{d \ge 1,\, d \text{ odd}} L_d$ converges absolutely, and for every finite nonempty set $S$ of odd positive integers, the finite partial sum $L_S := \sum_{d \in S} L_d$ is **Rauzy-deterministic** (zero topological/point entropy in base $2$) and nonnormal in base $2$ (with $D_\infty(L_S; 2) \ge 1/(2 \mathrm{lcm}(S))$).*

**Proof.** Absolute convergence is immediate from $L_d \le 2^{-d+1}/d$, and regrouping $m = d 2^j$ yields $\ln 2 = \sum_{d \text{ odd}} L_d$ (checked to $1.02 \times 10^{-44}$ in `scripts/phase18_classical.py`). Fix finite $S$ and put $D = \mathrm{lcm}(S)$. The set of all insertion exponents $\{e(d, j) : d \in S,\, j \ge 0\}$ has at most $|S| \cdot (1 + \log_2 N)$ elements up to $N$. For every $n \in [0, N)$ at distance at least $L_N := \lceil 2 \log_2 N \rceil$ before the next insertion exponent, all completed terms of $2^n L_S$ have rational sum in $\frac{1}{D}\mathbb{Z}$, while the remaining tail is at most $2 |S| \cdot 2^{-L_N} \ll_S N^{-2}$. Consequently, outside a set of positions $n < N$ of cardinality $O_S((\log N)^2)$ (density $0$), $\{2^n L_S\}$ lies within $O_S(N^{-2})$ of the finite set $\frac{1}{D}\mathbb{Z}/\mathbb{Z}$ and agrees on $k$-digit blocks with a periodic sequence of period dividing $\mathrm{ord}_D(2)$. Thus every weak-* cluster point of the empirical measures of $\{2^n L_S\}$ is supported on $\frac{1}{D}\mathbb{Z}/\mathbb{Z}$ (forcing $D_\infty(L_S; 2) \ge 1/(2D)$ by taking an open interval of length $1/D$ avoiding $\frac{1}{D}\mathbb{Z}/\mathbb{Z}$), and the upper Rauzy noise / upper point entropy of $L_S$ in base $2$ vanishes identically. $\square$

Compare this with Track D1's vertical $p$-adic Stoneham-ray partition $\ln 2 = \sum_{p \nmid r} T_{2,p,r}$ (see [`summation.md`](summation.md)): $\ln 2$ can be written *both* as an infinite sum of individually normal numbers (vertical rays) *and* as an infinite sum of Rauzy-deterministic nonnormal numbers (horizontal rays). Neither decomposition by itself settles the digit distribution of the infinite sum.

---

## F4. Deterministic remainder synthesis

The target of Track F4 is a decomposition $\ln 2 = A + B$ in which $A$ belongs to a provably binary-normal arithmetic family and $B$ belongs to a provably normality-preserving remainder class (in particular, Rauzy's additive subgroup $\mathcal{B}^\perp(2)$ of $2$-deterministic numbers; see [`sources.md`](sources.md)). Two sharp obstructions govern this approach.

### Theorem F4.1 (Complement denominator persistence)

*Let $P$ be any finite set of primes (or more generally, let $M \subset \mathbb{N}_{\ge 1}$ be any set of Taylor indices containing at most $o(N/\log N)$ primes $\le N$ and avoiding all multiples $\ell p$ with $p > P_0$ and $\ell \le V_p$, or simply $M = \langle P \rangle$ the $P$-smooth integers). Put $A_P = \sum_{m \in \langle P \rangle} \frac{1}{m 2^m}$ (binary normal whenever $P$ contains an odd prime, by Paper II / `LS-01`) and $B_P = \ln 2 - A_P$. Then at every cutoff $N$ and every odd prime $p > \max P$ with $p^2 > N$, the shifted prefix $Y_N(B_P) = 2^N \sum_{m \le N,\, m \notin \langle P \rangle} \frac{1}{m 2^m}$ satisfies the **exact same Frobenius congruence** as $\ln 2$:*

```math
p \, Y_N(B_P) \equiv 2^N \sum_{\ell=1}^{\lfloor N/p \rfloor} \frac{1}{\ell 2^\ell} \pmod{p}.
```

*Consequently, $\lim_{N \to \infty} \frac{\log \mathrm{den}_{\mathrm{odd}}(Y_N(B_P))}{N} = 1$.*

**Proof.** For any prime $p > \max P$, every integer multiple $m = \ell p$ ($\ell \ge 1$) is divisible by $p \notin P$, hence $m \notin \langle P \rangle$. Therefore, removing $\langle P \rangle$ removes zero multiples of $p$ from $[1, N]$. Multiplying $Y_N(B_P)$ by $p$ and reducing modulo $p$ (using $p^2 > N$ and $2^p \equiv 2 \pmod p$) leaves the exact sum $2^N \sum_{\ell=1}^{\lfloor N/p \rfloor} 1/(\ell 2^\ell) \pmod p$. Because every partial sum $P_v = \sum_{\ell=1}^v 1/(\ell 2^\ell) > 0$ is strictly positive, the prime-band argument of Paper V yields $\lim (\log \mathrm{den}_{\mathrm{odd}}(Y_N(B_P)))/N = \sum_{v \ge 1} (1/v - 1/(v+1)) = 1$. $\square$

`scripts/phase18_classical.py` verifies Theorem F4.1 with zero Frobenius mismatches for $P = \{2, 3\}$ and $P = \{2, 3, 5\}$ at $N = 64, 128, 256$ (reaching $(\log q_{\mathrm{odd}})/N = 0.94157$ and $0.94586$ at $N = 256$). Removing any finite-support normal logarithm $A_P$ leaves $100\%$ of the asymptotic exponential odd-denominator mass untouched inside $B_P$.

### Theorem F4.2 (Uniqueness of deterministic remainders across compatible normal families)

*Let $\mathcal{F} \subset \mathbb{R}$ be any family of real numbers such that for all distinct $A_1, A_2 \in \mathcal{F}$, the difference $A_1 - A_2$ is normal in base $2$ (for example, any rational vector space of Stoneham components on distinct primes or distinct localized polylogarithm orders, minus $0$ in pairwise differences). Then **at most one** $A \in \mathcal{F}$ can make $B = \ln 2 - A$ belong to $\mathcal{B}^\perp(2)$ (equivalently, be $2$-deterministic by Rauzy's theorem).*

**Proof.** Suppose $B_1 = \ln 2 - A_1 \in \mathcal{B}^\perp(2)$ and $B_2 = \ln 2 - A_2 \in \mathcal{B}^\perp(2)$ with $A_1, A_2 \in \mathcal{F}$. Because $\mathcal{B}^\perp(2)$ is closed under addition and negation (Rauzy 1976; see [`sources.md`](sources.md)), we have $A_1 - A_2 = B_2 - B_1 \in \mathcal{B}^\perp(2)$. On the other hand, no base-$2$ normal number $x$ can lie in $\mathcal{B}^\perp(2)$: if $x \in \mathcal{B}(2) \cap \mathcal{B}^\perp(2)$, then $-x \in \mathcal{B}(2)$ (since negating flips digits outside dyadic rationals), so $0 = x + (-x) \in \mathcal{B}(2)$, a contradiction. Hence $A_1 - A_2$ cannot be normal, forcing $A_1 = A_2$. $\square$

**Scale-varying decompositions and the circularity check.** Allowing $A_N, B_N$ to vary with scale $N$ (for example, setting $B_N = W_N - A_N$ using closed dyadic groups from Theorem F2.4, or rounding $2^N \ln 2$) avoids Theorem F4.2 only by encoding the unknown binary digits of $\ln 2$ directly into $B_N$. For a scale-varying decomposition $\ln 2 = A_N + B_N + E_N$ to transfer positive uniform coverage to $\ln 2$, one needs **independently certified** orbit equidistribution of $A_N$ on a positive share of $[0, N)$, an independent bound on the circular displacement of $B_N$ on those same positions (Track C1), and $|2^n E_N| \to 0$ across the window—none of which is currently supplied by any known arithmetic expansion of $\ln 2$.

---

## F5. Other classical targets

We evaluate the six named targets in F5, comparing exact shifted binary denominator rates, grouping/retirement behavior, and actual digit-distribution status. (For BBP joint-ray decompositions of $\pi$ and $\ln 2$, we cross-reference the parent track's [`notes/phase18/summation.md`](summation.md) rather than re-deriving those ray theorems.)

### Comparative overview

| Target | Representation | Shifted binary rate $(\log q_N)/N$ | Grouping / retirement behavior | Honest digit-distribution status |
| --- | --- | --- | --- | --- |
| **$\pi$** | Standard BBP (1997) | **$3/2 = 1.50000$** (exact) | For every odd prime the two slots retain its pole; cancellation needs a larger odd multiple | Open ($D_\infty^{(b)}(\pi) \le 1 - c_b (\log N)/N$ via $\mu(\pi) < 8$) |
| **$\pi$** | Bellard (1997) | **$1 = 1.00000$** (exact) | All primes $p \equiv 1,3,7,9 \pmod{10}$ survive up to $N$ | Open |
| **$\pi$** | Gaussian Machin $8\arctan(1/3)+4\arctan(1/7)$ | **$2/3 \approx 0.66667$** (Phase 11) | Fixed Gaussian prime bands, no cancellation | Open |
| **$\pi$** | **New** $\pi$-free rounded Chebyshev poles (even $T_{2D}$) | **$\le 0.29975$** (Machin), **$\le 0.24965$** (Størmer), **$\to 0$** | Breaks $2/3$ without knowing $\pi$; rounding destroys shift persistence | Open |
| **$e$** | Taylor $\sum 1/k!$ | **$\ln 2 \approx 0.69315$** (density-1 cutoffs) | **Theorem F5.2**: **zero** finite positive dyadic groups with $\max G \ge 3$ exist | Open |
| **$e$** | Diagonal Padé $C_m / B_m$ | **$(\ln 2)/2 \approx 0.34657$** (exact; Roth/$\mu(e)=2$ floor) | Convergents of $[2; 1, 2, 1, 1, 4, \dots]$; unbounded prime support | Open |
| **$\mathrm{Li}_s(1/b)$** | Taylor $\sum 1/(m^s b^m)$ | **$s$** (exact, Theorem F5.3) | Same $p\log_2 p$ / $p^{3/2}/\log p$ single-ray delay; finite prime supports normal (Paper II) | Open for full support ($s \ge 1$) |
| **$\zeta(3)$** | Apéry binomial $\frac{5}{2}\sum \frac{(-1)^{k-1}}{k^3 \binom{2k}{k}}$ | $\le 2$ (measured $1.79$–$1.89$ at $N \le 256$) | $\binom{2k}{k}$ adds primes in $(M, 2M]$; $k^3$ gives $p^3$ up to $M$ | Open |
| **$\zeta(3)$** | Apéry convergents $a_n/b_n$ | $\le 0.64149$ (measured $0.554$ at $n=30$) | $Q_n \mid 2 d_n^3 b_n$; Broadhurst BBP (1998) uses $(24k+j)^3$ over $2^{12k}$ | Open |
| **$E$ (Erdős–Borwein)** | Lambert $\sum (2^m-1)^{-1} = \sum \tau(n) 2^{-n}$ | **$0$** (odd denominator $= 1$ automatically) | Integral head annihilation automatic; $2$-adic carries of $\tau(n)$ govern digits | Disjunctive (Sude, Lean); positive word density & $D_\infty < 1$ (Cult, audited); simple normality conditionally disproved under Hypothesis P (Phase 16) |
| **$\sqrt{2}, \sqrt{3}, \varphi$** | Catalan dyadic series (e.g. $\frac{3}{4}\sqrt{2} = 1 + \sum (-1)^{k-1} C_{k-1} 2^{-(5k-1)}$) | Odd den $= 1$; $2$-adic excess $\frac{2}{3}N$ ($\sqrt{2}$), $N$ ($\sqrt{3}, \varphi$) | Trades odd primes completely for unbalanced $2$-adic denominator | Open ($D_\infty < 1$ open; $\ge c N^{1/d}$ ones by BBCP 2004; $\Omega(\sqrt{N})$ changes for $1/\sqrt{5}$ by Kaneko) |
| **$\sqrt{2}$** | Pell convergents $p_m / q_m$ | **$(\ln 2)/2 \approx 0.34657$** (exact; Roth/$\mu=2$ floor) | Primitive prime divisors in every $q_m$ ($m \ge 3$) by Carmichael's theorem | Open |

### 1. $\pi$: BBP denominator rates, two-slot non-cancellation, and $\pi$-free Chebyshev poles

**BBP and Bellard rates.** In the hexadecimal BBP formula $\pi = \sum_{k=0}^\infty 16^{-k}(4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6))$, shifting by $16^M = 2^{4M}$ ($N = 4M$ binary digits) places odd primes $p \equiv 1, 5 \pmod 8$ in $8k+1$ or $8k+5$ up to $p \le 8M + 5 \approx 2N$, and primes $p \equiv 3, 7 \pmod 8$ in $4k+3$ up to $p \le 4M + 3 \approx N$. By the prime number theorem in arithmetic progressions ($\vartheta(x; 8, r) = x/4 + o(x)$), the top uncancelled bands contribute $\frac{1}{4}(2N + 2N + N + N) = \frac{3}{2} N + o(N)$, matching `scripts/phase18_classical.py` ($1.482, 1.463, 1.467, 1.503$ at $N = 64, 128, 256, 512$). In Bellard's formula (1997), shifting by $2^{10M}$ ($N = 10M$) puts all four coprime residue classes $p \equiv 1, 3, 7, 9 \pmod{10}$ up to $10M + 9 \approx N$, yielding rate $1$ ($1.001, 1.002, 1.008$ at $N = 120, 240, 480$).

**Signed two-slot non-cancellation in BBP.** Every odd prime $p$ occurs twice in BBP with denominator $p$: once in $-1/(2(2k+1))$ at binary exponent $2p - 2$, and once in its mod-$8$ slot at exponent $(p-1)/2$ ($p \equiv 1 \pmod 8$, coefficient $+4$), $(p-5)/2$ ($p \equiv 5 \pmod 8$, coefficient $-1$), or $p - 3$ ($p \equiv 3, 7 \pmod 8$, coefficient $-1/2$). By Euler's criterion $2^{(p-1)/2} \equiv (\frac{2}{p}) \pmod p$:
- for $p \equiv 1 \pmod 8$: numerator $\equiv 2^{3(p-1)/2 + 3} - 1 \equiv 7 \not\equiv 0 \pmod p$ (since $p \ge 17$);
- for $p \equiv 5 \pmod 8$: numerator $\equiv -(2^{3(p-1)/2 + 3} + 1) \equiv 7 \not\equiv 0 \pmod p$ (since $p \neq 7$);
- for $p \equiv 3, 7 \pmod 8$: numerator $\equiv -(2^{p+1} + 1) \equiv -5 \pmod p$, nonzero in these residue classes. Indeed $8k+6=2p$ here gives $4k=p-3$. At $p=3$ the two terms sum to $-17/96$.

Thus combining both $p$-slots in BBP retains every odd prime $p$, forcing any positive or signed BBP grouping to wait at least until a higher multiple ($\ge 3p$). For geometric-ray decompositions of BBP series preserving residue classes mod $8$ and their joint normality, see [`notes/phase18/summation.md`](summation.md).

**Theorem F5.1 ($\pi$-free rounded Chebyshev-pole integrals breaking $2/3$).** *Let $\pi = \sum_{i=1}^m c_i \arctan(1/a_i) = \sum_{i=1}^m c_i a_i \int_0^1 \frac{dx}{x^2 + a_i^2}$ with $c_i \in \mathbb{Z}$ and $a_i \in \mathbb{Z}_{\ge 1}$, and put $a_{\min} = \min_i a_i$. For degree $2D$ ($D \ge 1$), let $T_{2D}(x) \in \mathbb{Z}[x^2]$ be the even Chebyshev polynomial of the first kind ($|T_{2D}(x)| \le 1$ on $[0, 1]$). Then $T_{2D}(x) - T_{2D}(i a_i) = (x^2 + a_i^2) P_i(x^2)$ with $P_i \in \mathbb{Z}[y]$ of degree $D - 1$, and*

```math
\sum_{i=1}^m \frac{c_i a_i}{T_{2D}(i a_i)} \int_0^1 \frac{T_{2D}(x)}{x^2 + a_i^2}\,dx
= \pi + \int_0^1 R_{\mathrm{tot}}(x^2)\,dx,
\qquad R_{\mathrm{tot}}(y) := \sum_{i=1}^m \frac{c_i a_i}{T_{2D}(i a_i)} P_i(y).
```

*Put $e = \lfloor \log_2 \min_i |T_{2D}(i a_i)| \rfloor$, round $2^e R_{\mathrm{tot}}(y)$ coefficientwise to $Q_D(y) \in \mathbb{Z}[y]$ (using **no knowledge of $\pi$**), set $w = \lceil \log_2(D(\ln D + 1)) \rceil + 2$, $N = e - w$, and $Y_N = -2^{-w} \int_0^1 Q_D(x^2)\,dx$. Then $|2^N \pi - Y_N| = O(1/N)$, $q_N \mid 2^w \mathrm{lcm}(1, 3, \dots, 2D - 1)$, and*

```math
\limsup_{D \to \infty} \frac{\log q_N}{N} \le \frac{\ln 2}{\ln\bigl(a_{\min} + \sqrt{a_{\min}^2 + 1}\bigr)}.
```

**Proof.** Writing $i a = \frac{u + u^{-1}}{2}$ with $u = i(a + \sqrt{a^2 + 1})$ gives $|T_{2D}(i a)| = \frac{1}{2}\bigl((a + \sqrt{a^2 + 1})^{2D} + (a + \sqrt{a^2 + 1})^{-2D}\bigr)$, so $N = e - w = 2D \log_2(a_{\min} + \sqrt{a_{\min}^2 + 1}) - O(\log D)$. Because $|T_{2D}(x)| \le 1$ on $[0, 1]$ and each rounded coefficient differs from $2^e R_{\mathrm{tot}}[k]$ by at most $1/2$,

```math
\left|2^e \pi + \int_0^1 Q_D(x^2)\,dx\right|
\le \sum_{i=1}^m |c_i| \frac{2^e}{|T_{2D}(i a_i)|} \arctan\frac{1}{a_i} + \frac{1}{2} \sum_{k=0}^{D-1} \frac{1}{2k+1} = O(\log D).
```

Dividing by $2^w$ gives $|2^N \pi - Y_N| = O(1/N)$. Since $\int_0^1 x^{2k}\,dx = 1/(2k+1)$, $q_N \mid 2^w \mathrm{lcm}(1, 3, \dots, 2D-1)$, whose logarithm is $(2 + o(1)) D$ by the prime number theorem. Dividing by $N$ yields the stated bound. $\square$

The script computes the denominators exactly and certifies the error against a rational alternating-series enclosure for π. The table shows decimal renderings of the logarithms, including the logarithm of the certified error upper bound:

| $\pi$ Chebyshev-pole family | Limit rate | $D$ | $N$ | $w$ | $(\log q_N)/N$ | Odd rate | $\log_2|\text{err}|$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Single pole $4\arctan(1)$ | $0.78644$ | 120 | 292 | 12 | $0.82554$ | $0.79706$ | $-13.11$ |
| Machin $16\arctan(1/5) - 4\arctan(1/239)$ | **$0.29975$** | 120 | 787 | 12 | **$0.29730$** | $0.28850$ | $-15.46$ |
| Størmer $24\arctan(1/8) + 8\arctan(1/57) + 4\arctan(1/239)$ | **$0.24965$** | 120 | 948 | 12 | **$0.25398$** | $0.24667$ | $-13.75$ |

Just as in Phase 16's $\ln 2$-free Chebyshev-pole construction, rounding eliminates $|T_{2D}(i a_i)|$ from the denominator at the cost of destroying shift persistence across $N \mapsto N+1$, so this provides no binary discrepancy bound for $\pi$.

### 2. $e$: Complete impossibility of positive dyadic factorial groups

In sharp contrast to $\ln 2$ (where every odd ray admits a dyadic partition), positive dyadic grouping of $e = \sum_{k=0}^\infty 1/k!$ fails completely beyond $k = 2$:

**Theorem F5.2 (Impossibility of finite positive dyadic factorial groups for $e$).** *There exists **no** finite nonempty subset $G \subset \mathbb{N}$ with $M = \max G \ge 3$ such that $\sum_{k \in G} \frac{1}{k!} \in \mathbb{Z}[1/2]$.*

**Proof.** Let $M = \max G \ge 3$.
- *Case 1 ($M$ has an odd prime divisor $p$):* Then $v_p(M!) = v_p((M-1)!) + v_p(M) > v_p(k!)$ for every $k \in G \setminus \{M\}$. By the ultrametric triangle inequality in $\mathbb{Q}_p$, $v_p(\sum_{k \in G} 1/k!) = -v_p(M!) < 0$.
- *Case 2 ($M = 2^r$ with $r \ge 2$):* Then $M - 1 = 2^r - 1 \ge 3$ is odd, so it has an odd prime divisor $p \ge 3$. Since $p \mid (M - 1)$ and $p \nmid M$, we have $v_p(M!) = v_p((M-1)!) > v_p(k!)$ for all $k \le M - 2$. Thus the terms of minimal $p$-adic valuation in $G$ are either $\{M\}$ alone or $\{M - 1, M\}$. Multiplying by $M!$ gives numerator congruent modulo $p$ to $1$ (if $M - 1 \notin G$) or to $1 + M \equiv 2 \pmod p$ (if $M - 1 \in G$). Since $p \ge 3$, neither $1$ nor $2$ vanishes modulo $p$, so $v_p(\sum_{k \in G} 1/k!) = -v_p(M!) < 0$. $\square$

`scripts/phase18_classical.py` independently verifies all $65{,}528$ subsets of $\{0, \dots, 15\}$ with $\max G \ge 3$ by brute force. For shifted binary approximants to $e$: the Taylor truncation $2^N \sum_{k=0}^n 1/k!$ ($n! \approx 2^N$) clears $v_2(n!) = O(N/\log N)$ and retains $\log q_N = (1 - o(1))\log(n!) = (\ln 2 - o(1))N$ on a density-$1$ set of $n$ (by Phase 11's moving-window bound in [`classical-approximants.md`](../classical-approximants.md); measured $0.523, 0.546, 0.566$ at $N = 100, 250, 500$, approaching $\ln 2 \approx 0.69315$ slowly because of the $O(1/\log N)$ $2$-adic subtraction). The diagonal Padé approximants $C_m/B_m$ (convergents of $e$'s continued fraction) achieve $(\log q_{\mathrm{odd}})/N_{\mathrm{eff}} \to (\ln 2)/2 \approx 0.34657$ (measured $0.334, 0.340, 0.343$ at $m = 15, 30, 50$), which is the universal floor $(\ln 2)/\mu(e)$ for any rational sequence with $v_2(q) = o(N)$, since $\mu(e) = 2$.

### 3. $\mathrm{Li}_s(1/b)$: Exact shifted rate and finite-support boundary

**Theorem F5.3 (Exact shifted denominator rate for $\mathrm{Li}_s(1/b)$).** *For every integer $b \ge 2$ and every integer order $s \ge 1$, the shifted Taylor prefix $Y_N = b^N \sum_{m=1}^N \frac{1}{m^s b^m}$ of $\mathrm{Li}_s(1/b)$ has reduced denominator $q_N$ satisfying $\lim_{N \to \infty} (\log q_N)/N = s$.*

**Proof.** For any fixed $V \ge 1$ and any prime $p \nmid b$ in $(N/(v+1), N/v]$ ($1 \le v \le V$) with $p^2 > N$, multiplying $Y_N$ by $p^s$ retains only $m = \ell p$ ($1 \le \ell \le v$) and gives $p^s Y_N \equiv b^N \sum_{\ell=1}^v \frac{1}{\ell^s b^\ell} \pmod p$ by Fermat's Little Theorem. Every partial sum $\sum_{\ell=1}^v \ell^{-s} b^{-\ell} > 0$ is strictly positive, so outside finitely many numerator/denominator primes we have $p^s \parallel q_N$. Summing $s \log p$ over $1 \le v \le V$ gives $\liminf (\log q_N)/N \ge s(1 - 1/(V+1))$, while $q_N \mid \mathrm{lcm}(1, \dots, N)^s$ gives $\limsup (\log q_N)/N \le s$. Let $V \to \infty$. $\square$

`scripts/phase18_classical.py` checks $s = 2, 3$ at $b = 2$ ($1.983$ for $\mathrm{Li}_2(1/2)$ and $2.975$ for $\mathrm{Li}_3(1/2)$ at $N = 128$). On single odd rays $m = p 2^j$, the exact same Fermat bound $p \mid \sum_{j \in G} 2^{2^K - 2^j + s(K-j)}$ reproduces the $p \log_2 p$ worst-case and $p^{3/2}/\log p$ typical delay bounds of Theorem F2.2. While every finite-prime localized subseries $\mathrm{Li}_{s, P}(1/b)$ with an off-radix prime is $b$-normal (Paper II) and jointly normal across orders (Phase 13), passage to all primes remains open.

### 4. $\zeta(3)$: Apéry series, Apéry convergents, and Broadhurst BBP

- **Apéry binomial series** $\zeta(3) = \frac{5}{2}\sum_{k=1}^\infty \frac{(-1)^{k-1}}{k^3 \binom{2k}{k}}$: reaching binary shift $N$ requires $M = \lfloor N/2 \rfloor$ terms (since $\binom{2k}{k} \sim 4^k / \sqrt{\pi k}$). The unreduced common denominator $\mathrm{lcm}_{k \le M}(k^3 \binom{2k}{k})$ has log-size $\sim 3M + M = 2N$ (primes $\le M$ to power $3$ from $k^3$, plus primes in $(M, 2M]$ to power $1$ from $\binom{2k}{k}$); exact reduced shifted rates in `scripts/phase18_classical.py` are $1.794, 1.794, 1.893$ at $N = 64, 128, 256$.
- **Apéry recurrence convergents** $a_n / b_n$ (from $n^3 u_n - (34n^3 - 51n^2 + 27n - 5) u_{n-1} + (n-1)^3 u_{n-2} = 0$, $b_0=1, b_1=5, a_0=0, a_1=6$): since $b_n \in \mathbb{Z}$, $2 d_n^3 a_n \in \mathbb{Z}$, $\log(2 d_n^3 b_n) \sim (3 + 4\ln(1+\sqrt{2}))n$, and $|\zeta(3) - a_n/b_n| \asymp (1+\sqrt{2})^{-8n}$, the shifted odd denominator rate is bounded above by $\frac{(3 + 4\ln(1+\sqrt{2}))\ln 2}{8\ln(1+\sqrt{2})} \approx 0.64149$ (measured $0.464, 0.527, 0.554$ at $n = 10, 20, 30$ due to finite-$n$ gcd cancellation).
- **Broadhurst's binary BBP ladder** (1998, `arXiv:math/9803067`): expresses $\zeta(3)$ as a base-$2^{12}$ sum over $(24k + j)^{-3}$, which places cubes of primes $p \le 2N$ in the shifted denominator—analogous to $\mathrm{Li}_3(1/2)$ and standard BBP for $\pi$, with exponential odd-denominator growth.

### 5. Erdős–Borwein constant $E$

As detailed in [`notes/phase13/erdos-borwein.md`](../phase13/erdos-borwein.md), [`notes/phase16/erdos-borwein-correlations.md`](../phase16/erdos-borwein-correlations.md), and [`notes/phase16/weighted-lambert.md`](../phase16/weighted-lambert.md), $E = \sum_{m \ge 1}(2^m - 1)^{-1} = \sum_{n \ge 1} \tau(n) 2^{-n}$ automatically satisfies integral head annihilation (odd denominator $1$ at every shift $N$) because $\tau(n) \in \mathbb{Z}$. It is therefore the **only** named classical constant in F5 with an unconditional base-$2$ disjunctivity proof (Captain Sude, Sept 2026, Lean-verified) and an audited positive-word-density / strict-discrepancy proof on short windows (Mira Cult, Nov 2026). However, Phase 16's mesoscopic Poisson pair correlation and conditional disproof of simple normality (under Hypothesis P, limiting one-frequency $p_* \in [0.492230, 0.492685]$) indicate that zero odd denominator with $2$-adic carries can produce biased rather than normal digits, and weighted-Lambert transfer to $\ln 2$ fails at Pillar (i) because $P^+(m) \mid \mathrm{den}(a_m)$ for every $m \ge 2$.

### 6. Algebraic irrationals ($\sqrt{2}, \sqrt{3}, \varphi$)

Applying $\sqrt{1 + 4x} = 1 + 2\sum_{k=1}^\infty (-1)^{k-1} C_{k-1} x^k$ (where $C_{k-1} = \frac{1}{k}\binom{2k-2}{k-1} \in \mathbb{Z}$ is the $(k-1)$-th Catalan number) at $x = 2^{-5}, -2^{-4}, 2^{-4}$ gives exact **integer-coefficient dyadic expansions** (odd denominator $1$ identically):

```math
\frac{3}{4}\sqrt{2} = 1 + \sum_{k=1}^{\infty} (-1)^{k-1} \frac{C_{k-1}}{2^{5k-1}},
\qquad
\frac{\sqrt{3}}{2} = 1 - \sum_{k=1}^{\infty} \frac{C_{k-1}}{2^{4k-1}},
\qquad
\varphi = \frac{3}{2} + \sum_{k=1}^{\infty} (-1)^{k-1} \frac{C_{k-1}}{2^{4k-1}}.
```

Because $C_{k-1} \sim 4^{k-1}/(\sqrt{\pi} k^{3/2})$ while $v_2(C_{k-1}) = s_2(k) - 1 = O(\log k)$ by Kummer's theorem, these series are **unbalanced** (in the sense of Phase 15 Theorem C): reaching binary precision $2^{-N}$ requires $K \approx N/3$ (for $\frac{3}{4}\sqrt{2}$) or $K \approx N/2$ (for $\frac{\sqrt{3}}{2}, \varphi$), which leaves a pure $2$-adic denominator excess of $\frac{2}{3}N - O(\log N)$ or $N - O(\log N)$ bits in the shifted prefix $2^N S_K$ (verified in `scripts/phase18_classical.py`: $v_2/N = 0.6500$ vs. $2/3$, and $0.9667$ vs. $1$, at $N = 120$). Conversely, the Pell convergents $p_m / q_m$ to $\sqrt{2}$ achieve $v_2(q_m) = O(1)$ and odd-denominator rate $(\log q_{\mathrm{odd}})/N_{\mathrm{eff}} \to (\ln 2)/2 \approx 0.34657$ (measured $0.34151$ at step $40$), which is optimal among $v_2(q) = o(N)$ approximants by Roth's theorem ($\mu(\sqrt{2}) = 2$), yet $q_m$ acquires new primitive prime divisors at every $m \ge 3$ (Carmichael's theorem), excluding fixed-support orbit theorems. Best known unconditional binary digit bounds remain $\ge c N^{1/d}$ ones for degree-$d$ algebraic irrationals (Bailey–Borwein–Crandall–Pomerance 2004, DOI `10.5802/jtnb.457`) and $\ge (1-\varepsilon)\sqrt{N/2}$ binary transitions for $1/\sqrt{5}$ (Kaneko; see [`classical-approximants.md`](../classical-approximants.md)).

### Priority conclusion across F1–F5

The external word-density theorem gives the Erdős–Borwein constant a strict upper discrepancy below one. The character Lambert comparison family instead has discrepancy tending to one despite disjunctivity. Earlier work also supplies digit-count lower bounds for specific algebraic irrationals. Among the non-Lambert classical constants ($\ln 2, \pi, e, \mathrm{Li}_s(1/b), \zeta(3)$, algebraic irrationals), synthetic grouping and retirement do not yet yield $D_\infty < 1$ or normality for any target; the strongest rigorous arithmetic advances remain the prime-band rate classifications, the factorial grouping impossibility theorem for $e$ (Theorem F5.2), and the $\ln 2$-free / $\pi$-free Chebyshev-pole denominator reductions (Phase 16 and Theorem F5.1), with shift persistence and distribution of the resulting models still requiring estimates.

## Reproduction

```sh
python3 -B scripts/phase18_classical.py
```

The script uses only the Python standard library. It ends with `All Phase 18 classical synthesis checks passed.`
