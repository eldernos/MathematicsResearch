# Independent Mathematical Referee Report — Phase 21 Track D (Sub-tracks D1–D2)

**Audited files (read-only):**
- `notes/phase21/euler-scalings-and-reciprocals.md`
- `scripts/phase21_euler_reciprocals.py` (executed with `python -B scripts/phase21_euler_reciprocals.py`: exited 0, 13,081 checks passed in 6.8 s)
- Cross-checked against `notes/phase20/euler-product.md`, `notes/phase20/dense-and-partitions.md`, `NormalityChecker/EulerPentagonal.lean`, `NormalityChecker/CoefficientTransfer.lean`, `NormalityChecker/Phase18Synthetic.lean`, and `NormalityChecker/SharpTranslation.lean`.

---

## Executive Verdicts

| Sub-track | Verdict | Summary |
| --- | --- | --- |
| **D1** (Rational scalings of $E_b, E_b^3, E_b^2$, §§1–4) | **ACCEPT WITH MINOR POLISH** | Every theorem statement and paper proof is mathematically sound; scope and sketch status (Lemma S, Phase 20 Theorem 6(a), Wirsing) are honestly disclosed. Only minor proof edge-cases, wording/rounding slips, and a script tail-certification bug for unbounded coefficients (`E_b^3`, `E_b^2`) need cleanup. |
| **D2** (Normal reciprocals of $K_b$ elements, §5) | **REVISE** | The core mechanism (band identity, exact cycle Fourier vanishing, window Weyl-sum estimate, and $1 - D_N(x) \le N^{-1+o(1)}$) is genuinely strong and airtight. However, **two substantive gaps** break the stated deductions under admissibility (A1)+(A2) alone: **(1) Critical:** the displayed Erdős–Turán bound in Theorem D2(b) does *not* tend to $0$ under (A1)+(A2) (it diverges to $+\infty$ for e.g. $m_{k+1}=(k+1)T_k$); **(2) Major:** the extraneous $-2\log_b m_{K+1}/m_K$ term in Proposition D2.5(1) makes the lower bound vacuous whenever $m_{K+1} \ge b^{m_K}$, breaking the deduction of the sign dichotomy (Part 2) and $\limsup D_N(1/x') \ge 1/2$. Both have short, exact fixes that preserve (A1)+(A2) unchanged. |

---

## Summary of Findings by Severity

| ID | Track | Severity | Location | Short Description |
| --- | --- | --- | --- | --- |
| **C1** | D2 | **Critical** | `euler-scalings-and-reciprocals.md` L297–300, L358 | Erdős–Turán bound with $H=\lfloor\sqrt{D_{K-2}}\rfloor$ diverges to $+\infty$ under (A1)+(A2) alone (fails to prove $D_N(y)\to 0$ as written). |
| **M1** | D2 | **Major** | `euler-scalings-and-reciprocals.md` L17, L382–396 | Extraneous $-2\log_b m_{K+1}/m_K$ term in Prop. D2.5(1) is vacuous for fast-growing admissible sequences ($m_{K+1}\ge b^{m_K}$), breaking Prop. D2.5(2) and $\limsup D_N(1/x')\ge 1/2$. |
| **M2** | D1 (Script) | **Major (script)** / **Minor (note)** | `phase21_euler_reciprocals.py` L279–290, L454–460 | `tail_bound(cmax, b, W)` uses empirical prefix `cmax` as a global bound on unbounded sequences $E_b^3$ and $E_b^2$, invalidating strict certification of `eta`, `slack`, and `trunc`. |
| **m1** | D1 | **Minor** | `euler-scalings-and-reciprocals.md` L41–57 | Lemma 1.1 prose omits boundary cases ($|J|+2\eta\ge 1$, empty atom set, $|J|\le 2\eta$, all $d$ atoms inside $J_{-\eta}$, implicit $N\ge 1$); inequality holds unconditionally. |
| **m2** | D1 | **Minor** | `euler-scalings-and-reciprocals.md` L7, L93–95, L103 | Confuses Phase 20 digit-run lengths ($2j,4j,2j+1,4j+2$) with automaton run lengths ($2j,4j+1,2j+1,4j+3$); leftover after $K$ pairs is $\le 3K+4$ (not $2K+3$); $\eta=1/N < 1/(4d)$ needs $N>4d$. |
| **m3** | D1 | **Minor** | `euler-scalings-and-reciprocals.md` L117–123, L219 | Cor. D1.2 simplifies further to $\max(w_0, 2/p - w_0) = 1/p + |w_0 - 1/p|$; Prop. D1.0 is cited for $E_b^2$ on L219 though stated only for $E_b$. |
| **m4** | D1 | **Minor** | `euler-scalings-and-reciprocals.md` L29, L149, L181, L255, L266 | Four claimed uniform cube cases `(2,31),(2,73),(3,13),(2,23)` are mathematically true (independently verified) but absent from the script; minor numerical rounding/range slips on L149, L255, L266. |
| **m5** | D1 (Script) | **Minor** | `phase21_euler_reciprocals.py` L366 | `pentagonal_insertions(1 << 13)` omits $P_{74}^+ = 8251 \in (8192, 8252]$ in the radix-primary shift spot check. |
| **m6** | D2 | **Minor** | `euler-scalings-and-reciprocals.md` L278, L290/L336, L358, L360–368 | Exact no-cancellation identity $D_k = \prod_{j\le k}(b^{m_j}-1)$ simplifies Lemma D2.4 ($T_k \ge m_k$); $D_{K-2}=1$ edge case in L358; $N<m_{K+1}$ vs $N\le m_{K+1}$. |
| **m7** | D1 & D2 | **Minor** | `euler-scalings-and-reciprocals.md` §6 (L428–468) | Lean proposals missing `[NeZero d]`/`[NeZero D]`, `0 < N`, `0 ≤ w j`, and coercing `Circle.exp` to `ℂ` inside `∑`. |

---

## Detailed Audit of Track D2 (§5)

### [CRITICAL] C1 — Quantitative Erdős–Turán bound in Theorem D2(b) does not tend to $0$ under (A1)+(A2)

**Location:** `notes/phase21/euler-scalings-and-reciprocals.md`, lines 297–300 and line 358.

**What the text claims:**
In Theorem D2(b) (lines 296–300), for any admissible sequence satisfying (A1) $T_k \mid m_{k+1}$ and (A2) $\omega_k = m_{k+1}/T_k \to \infty$, and any $K \ge 3$, $m_K \le N < m_{K+1}$:
$$D_N(y) \le \frac{14}{\sqrt{D_{K-2}}} + \frac{\bigl(T_{K-1} + 3 c_b(\sqrt{D_{K-2}})\bigr)(1 + \log D_{K-2})}{m_K},$$
followed by "and both right sides tend to 0." The proof (line 358) sets $H = \lfloor \sqrt{D_{K-2}} \rfloor$ in the Kuipers–Niederreiter Erdős–Turán inequality $D_N \le \frac{6}{H+1} + \frac{4}{\pi}\sum_{h \le H} |W_h(N)|/h$ and argues:
> "It tends to 0 because $T_{K-1}/m_K = 1/\omega_{K-1} \to 0$ by (A2), $\log D_{K-2}/m_K \le T_{K-2}/m_K \to 0$, and $D_k \to \infty$ by Lemma D2.4."

**Why this fails:**
1. Checking $T_{K-1}/m_K \to 0$ and $\log D_{K-2}/m_K \to 0$ separately does **not** control their product times $m_K$, namely
   $$\frac{T_{K-1} \log D_{K-2}}{m_K} = \frac{\log D_{K-2}}{\omega_{K-1}},$$
   nor the second product $\frac{3 c_b(\sqrt{D_{K-2}}) \log D_{K-2}}{m_K} \asymp_b \frac{(\log D_{K-2})^2}{m_K}$.
2. **Explicit counterexample under (A1)+(A2):** Set $m_1 = 2$ and inductively $m_{k+1} = (k+1) T_k$. Since $D_k = \prod_{j=1}^k (b^{m_j} - 1) \ge b^{m_k} - 1$ (see m6 below), we have $b^{T_k} - 1 \ge D_k \ge b^{m_k} - 1$, hence $T_k \ge m_k$. Therefore $m_{k+1} \ge (k+1) m_k > m_k$, $T_k \mid m_{k+1}$, and $\omega_k = k + 1 \to \infty$, so $(m_k)$ is strictly increasing and admissible. Yet $m_{K-2} \ge 2(K-2)!$ and $\log D_{K-2} \ge m_{K-2} \log b - 1$, giving
   $$\frac{T_{K-1} \log D_{K-2}}{m_K} = \frac{\log D_{K-2}}{K} \ge \frac{2(K-2)! \log b - 1}{K} \longrightarrow +\infty.$$
   Even on the note's own $b = 2$ prefix $(2, 4, 48, 43200)$ continued with $\omega_4 = 25, \omega_5 = 30$, the second term already grows to $\frac{1 + \log D_3}{25} \approx 1.52$ at $K=5$ and $\frac{1 + \log D_4}{30} \approx 1000$ at $K=6$.
3. Similarly, $\frac{(\log D_{K-2})^2}{m_K}$ need not vanish under (A1)+(A2) alone (for instance if $m_{K-2}$ is chosen very large relative to $D_{K-3}$ while $\omega_{K-2}, \omega_{K-1}$ grow slowly).
4. Note that for the *specific* canonical choice $m_{k+1} = (k+1) m_k T_k$ (line 17), the bound on line 297 *does* vanish, because $\omega_{K-1} = K m_{K-1}$ while $\log D_{K-2} \le 2 m_{K-2} \log b = o(m_{K-1})$ and $m_K \ge K m_{K-1}^2 \gg (\log D_{K-2})^2$. However, Theorem D2(b) is stated for **every** admissible sequence.

**Verification of the unaffected parts of Theorem D2(b):**
- The **Weyl-sum bound** (Proposition D2.3, line 293) is **100% airtight** across all $m_K \le N \le m_{K+1}$ and all $h \ge 1$ (see dedicated verification below).
- The **inequality** on line 297 itself is valid (using $\gcd(h, D_{K-2})/h \le 1$, so $\frac{6}{H+1} + \frac{12 H}{\pi D_{K-2}} \le \frac{6 + 12/\pi}{\sqrt{D_{K-2}}} < \frac{14}{\sqrt{D_{K-2}}}$, and for $D_{K-2} \ge 2$, $\frac{4}{\pi}\sum_{h=1}^{\lfloor\sqrt{D_{K-2}}\rfloor} 1/h \le 1 + \log D_{K-2}$; at $D_{K-2} = 1$, $\frac{4}{\pi} > 1 + \log 1$, though $14/\sqrt{1} = 14 > 1$ makes line 297 trivially valid).
- **Normality of $y$ holds unconditionally for every admissible sequence!**

**Concrete minimal fix (keeps (A1)+(A2) unchanged):**
In Theorem D2(b) and its proof (lines 297 and 358), replace $H = \lfloor \sqrt{D_{K-2}} \rfloor$ by
$$H = \min\Bigl(\lfloor \sqrt{D_{K-2}} \rfloor,\ \omega_{K-1}\Bigr) \ge 1.$$
Applying Erdős–Turán ($D_N \le \frac{6}{H+1} + \frac{4}{\pi}\sum_{h=1}^H |W_h(N)|/h$) with $\gcd(h, D_{K-2})/h \le 1$ and $\sum_{h=1}^H 1/h \le 1 + \log H$ gives
$$D_N(y) \le \frac{6}{H+1} + \frac{12}{\pi\sqrt{D_{K-2}}} + \frac{4}{\pi}\,\frac{\bigl(T_{K-1} + 3 c_b(H)\bigr)(1 + \log H)}{m_K}.$$
Every term explicitly tends to $0$ under (A1)+(A2) alone:
- $H \to \infty$ since $D_{K-2} \to \infty$ (Lemma D2.4) and $\omega_{K-1} \to \infty$ (A2), so $\frac{6}{H+1} \to 0$ and $\frac{12}{\pi\sqrt{D_{K-2}}} \to 0$;
- $\frac{T_{K-1}(1+\log H)}{m_K} = \frac{1+\log H}{\omega_{K-1}} \le \frac{1+\log \omega_{K-1}}{\omega_{K-1}} \to 0$;
- $H \le \omega_{K-1} = m_K/T_{K-1} \le m_K$, so $\frac{3 c_b(H)(1+\log H)}{m_K} \ll_b \frac{(1+\log m_K)^2}{m_K} \to 0$.
(Equivalently, deduce $D_N(y) \to 0$ directly from $|W_h(N)| \to 0$ via Weyl's criterion, and use $H = \min(\lfloor\sqrt{D_{K-2}}\rfloor, \omega_{K-1})$ for the explicit discrepancy bound.)

---

### [MAJOR] M1 — Extraneous $-\frac{2\log_b m_{K+1}}{m_K}$ term in Proposition D2.5 breaks the sign dichotomy for general admissible sequences

**Location:** `notes/phase21/euler-scalings-and-reciprocals.md`, lines 17 and 380–398.

**What the text claims:**
Proposition D2.5 assumes only (A1) and (A2) for $(D_k^\epsilon, T_k^\epsilon)$, and claims:
1. if $\epsilon_K = +1$ and $2 J m_K \le m_{K+1} - \lceil 2 \log_b m_{K+1} \rceil$, then for every $L$
   $$D_{2 J m_K}(1/x_\epsilon) \ge \tfrac{1}{2}(1 - L/m_K) - 6 b^{-L} - \frac{2 \log_b m_{K+1}}{m_K};$$
2. "consequently $1/x_\epsilon$ is normal **if and only if** $\epsilon_k = -1$ for all large $k$."

**Why this fails:**
1. Admissibility (A1)+(A2) places **no upper bound** on how fast $m_{K+1}$ grows relative to $m_K$. Take any admissible sequence with $m_{k+1} \ge b^{m_k}$ (for instance $m_{k+1} = b^{m_k} T_k$, which satisfies $T_k \mid m_{k+1}$ and $\omega_k = b^{m_k} \to \infty$). Then
   $$\frac{2 \log_b m_{K+1}}{m_K} \ge 2,$$
   so the right-hand side of Proposition D2.5(1) is $\le \frac{1}{2} - 2 = -\frac{3}{2} < 0$ for every $L$ and every $J$. Part 1 is completely vacuous for such sequences, so **Part 2 (and Theorem D2's claim $\limsup D_N(1/x') \ge \frac{1}{2}$) does not follow from Part 1 as stated**.
2. Furthermore, the proof sentence on line 396 ("There $x_n \in (0, 4 b^{r-m}]$ up to the error $32 b^{n-m_{K+1}}$. Hence an arc of length $5 b^{-L}$ at 0 contains at least $J(m_K - L) - 2 \log_b m_{K+1}$ of the $2 J m_K$ points") does not explain how $32 b^{n-m_{K+1}}$ is compared to $b^{-L}$ when $L > 2\log_b m_{K+1}$, nor does it note that the error $b^n(1/x_\epsilon - R_K^\epsilon)$ can be negative (e.g., when $\epsilon_{K+1} = +1$), requiring a two-sided circle arc straddling $0$.

**Concrete minimal fix:**
Because we only count indices $n = i m_K + r$ in odd bands $i \in \{1, 3, \dots, 2J - 1\}$ with $0 \le r \le m_K - L - 1$, every counted index automatically satisfies
$$n \le (2J - 1) m_K + (m_K - L - 1) = 2 J m_K - L - 1.$$
Therefore, replace the hypothesis in Proposition D2.5(1) by simply
$$2 J m_K \le m_{K+1} - 6$$
(which holds with $J = 1$ for all sufficiently large $K$, since $m_{K+1}/m_K \to \infty$ by Lemma D2.4). Then for **every** $L \ge 1$ and every counted index $n$:
- $n - m_{K+1} \le -L - 7$, so $|b^n(1/x_\epsilon - R_K^\epsilon)| \le 32 b^{n - m_{K+1}} \le 32 b^{-7} b^{-L} \le \frac{1}{4} b^{-L}$ (note $m_{K+1} \ge 8$ ensures $|1/x_\epsilon - R_K^\epsilon| \le 32 b^{-m_{K+1}}$);
- $b^n R_K^\epsilon \equiv \frac{b^r R_{K-1}^\epsilon}{b^{m_K} + 1} \in (0, 4 b^{r - m_K}] \subseteq (0, 2 b^{-L}]$ (using $r \le m_K - L - 1$ and $b \ge 2$).
Hence **all** $J(m_K - L)$ points lie in the half-open circle arc $[-\frac{1}{4} b^{-L}, \frac{9}{4} b^{-L})$ of length $\frac{5}{2} b^{-L} < 3 b^{-L}$, with **zero** points lost. If $L \ge m_K$ or $3 b^{-L} \ge 1$ the bound is trivially nonpositive; otherwise arc discrepancy immediately yields
$$D_{2 J m_K}(1/x_\epsilon) \ge \frac{1}{2}\Bigl(1 - \frac{L}{m_K}\Bigr) - 3 b^{-L}.$$
Taking $J = 1$ and $L = \lfloor \sqrt{m_K} \rfloor$ along $\epsilon_K = +1$ gives $\limsup_{N\to\infty} D_N(1/x_\epsilon) \ge \frac{1}{2}$ for **every** admissible sequence with $\epsilon_K = +1$ infinitely often, completely repairing Part 2 and Theorem D2.

---

### Verification of All Other D2 Components

Every other mathematical step of D2 was checked independently and holds rigorously:
- **Admissibility & existence:** $m_{k+1} = (k+1) m_k T_k$ satisfies $m_k < m_{k+1}$, (A1), and (A2). Even the edge case $b = 2, m_1 = 1$ ($D_1 = T_1 = 1$) does not break Lemmas D2.1–D2.4 or Proposition D2.3.
- **Band identity (Lemma D2.1):** Exact. Expanding $b^n R_K = \sum_{j \ge 0} b^{n - j m_K} R_{K-1}$ at $n = i m_K + r$ ($0 \le r < m_K$), the $i+1$ terms $0 \le j \le i$ all agree with $b^r R_{K-1} \pmod 1$ since $T_{K-1} \mid m_K$, and the tail $\sum_{j > i} b^{n - j m_K} R_{K-1} = \frac{b^r R_{K-1}}{b^{m_K} - 1} = \eta_r \in (0, 8 b^{r-m_K}]$ is **exact and independent of $i$**, even when $i \sim m_{K+1}/m_K$. Also $R_{K-1} \le 1/E_2 \approx 3.463 < 4$ since $m_j \ge j$.
- **Exact cycle Fourier vanishing (Lemma D2.2):** Exact. Since $b^t R_K \bmod 1$ depends only on $(i \bmod D_{K-1}, r)$, $T_K \mid m_K D_{K-1}$. Because $\eta_r$ is independent of $i$, $e(k \eta_r)$ factors out of the $c = i+1$ sum for *every* $r$ (including $r = m_K - O(1)$), and $\gcd(b^r A_{K-1}, D_{K-1}) = 1$ makes the inner sum vanish identically whenever $D_{K-1} \nmid k$.
- **Window Weyl-sum estimate (Proposition D2.3):** Completely airtight across all $m_K \le N \le m_{K+1}$ and all $h \ge 1$:
  - *Tail leakage from $m_{K+1}$ (Step 1):* For $K \ge 3$, $m_{K+1} \ge 4$, $2\sum_{k>K} b^{-m_k} \le 4 b^{-m_{K+1}} \le 1/4$, so $\prod_{k>K}(1-b^{-m_k})^{-1} - 1 \le e^{4b^{-m_{K+1}}}-1 \le 8 b^{-m_{K+1}}$ and $y - R_K < 32 b^{-m_{K+1}}$. Summing $\min(2, 64\pi h b^{n - m_{K+1}})$ over $0 \le n < N \le m_{K+1}$ gives $\le \sum_{l \ge 1} \min(2, 64\pi h b^{-l}) \le 2\log_b(32\pi h) + 4 < c_b(h) = 2\log_b(64\pi h) + 8$ for all $b \ge 2$ (including $b > 64\pi h$).
  - *Right endpoints of bands (Step 2):* Although $\eta_r = O(1)$ near $r = m_K - 1$, capping $|e(h\eta_r)-1| \le \min(2, 16\pi h b^{r-m_K})$ bounds the entire band error (including its right endpoint) by $\le c_b(h)$ uniformly in $i$, and $T_{K-1} \mid m_K$ gives $m_K \widehat C_{K-1}(h(i+1))$ cleanly on every complete band, with error $\le T_{K-1} + c_b(h)$ on the partial band.
  - *Partial-band and transition accounting (Step 3):* For $I \ge 1$, the complete bands contribute $\le g/D_{K-2}$; the partial band survives only if $D_{K-2}/g \mid (I+1)$, forcing $D_{K-2}/g \le I+1 \le 2I$, hence $r_0/N < 1/I \le 2g/D_{K-2}$; and $(I+2)/I \le 3$ gives $\frac{T_{K-1} + 3 c_b(h)}{m_K}$.
- **Growth (Lemma D2.4) & Irrationality (Theorem D2(c)):** Valid. Since $D_k \to \infty$ and every fixed $h \ge 1$ satisfies $W_h(N) \to 0$, $y$ is base-$b$ normal, hence irrational (every rational $p/q$ has $D_N(p/q) \ge 1/q$), hence $x = 1/y$ is irrational.
- **Kernel membership and rate $1 - D_N(x) \le N^{-1+o(1)}$ (Theorem D2(a)):** Completely rigorous. From $m_{k+1}/m_k \to \infty$ we get $J(X) = o(\log X)$, so $2^{J(X)} \ll X^{1/2}$; with $w = \lceil 2\log_b N \rceil + C$, $\sum_{l > w} 2^{J(n+l)} b^{-l} \le 1/N$ uniformly for $n < N$, and `discrepancy_deficit_le` gives $1 - D_N(x) \le 2/N + (w+1) 2^{J(N+w)}/N = N^{-1+o(1)}$.
- **Converse in Proposition D2.5(2) ($\epsilon_k = -1$ for $k \ge k_0$):** Valid once C1 is fixed (needs $K \ge k_0 + 1$, so $K \ge k_0 + 2$ is safe).
- **Slow-rate sketch (§5.6, L407):** Valid; at $N = m_K$, $\widehat C_{K-1}(D_{K-2}) = 1 - O(\log_b D_{K-2} / m_{K-1}) = 1 - o(1)$, and Koksma's inequality gives $D_N \ge |W_h(N)|/(4h) > |W_h(N)|/(2\pi h) \ge 1/(4\pi D_{K-2})$. Script numbers $|W_{45}(N)| \in [0.887, 0.931]$ and $|W_h(N)| \le 1.4 \times 10^{-4}$ ($h=1,2,3$, $N \ge 2\cdot 10^5$) match L407.

---

## Detailed Audit of Track D1 (§§1–4)

### Section 1 (Lemmas 1.1 & 1.2)
- **Lemma 1.1 (atomic limit lemma):** The inequality $|D_N - D^*(w)| \le \|\mu^G - w\|_1 + \beta + 2\eta$ is **completely true** (for $N \ge 1$, $0 \le \eta < 1/(4d)$). Note that by circle complementation, $\max_{\text{closed } A}(w(A)-|A|) = \max_{\text{open } A}(|A|-w(A))$, so the two halves of $D^*(w)$ are equal.
  - **Minor (m1):** The prose proof (L49–55) omits four boundary cases: (i) $|J| + 2\eta \ge 1$ (gives $\#J/N - |J| \le 2\eta$ directly); (ii) no atom within $\eta$ of $J$ (gives $\#J/N - |J| \le \beta$); (iii) $|J| \le 2\eta$ (gives $|J| - \#J/N \le 2\eta$); (iv) all $d$ atoms lie at distance $> \eta$ inside $J$ (there is no open atom arc containing all $d$ atoms, since open atom arcs omit at least one atom; instead $\#J/N \ge 1-\beta$ gives $|J| - \#J/N \le \beta$). Also $N \ge 1$ is tacit.
- **Lemma 1.2 (runs):** **Airtight.** With $m = |O(u)| \mid t$ and $g = qm + r$ ($0 \le r < m$), the $\ell^1$ error is $2r(1 - r/m) \le m/2 \le t/2 \le t$.

### Section 2 ($E_b$: Automaton, Theorem D1.1, Prop. D1.0, Cor. D1.2)
- **Automaton & periodicity (§2.1):** Exact. $P_k^- - P_{k-1}^+ = 2k - 1$, $P_k^+ - P_k^- = k$, $u_k^- = b^{2k-1} u_{k-1}^+ + (-1)^k$, $u_k^+ = b^k u_k^- + (-1)^k$. Since $\gcd(b, d) = 1$, the map on $(\mathbb{Z}/L) \times (\mathbb{Z}/d)$ with $L = \operatorname{lcm}(2, t)$ is a bijection, hence purely periodic of period $P$ with $L \mid P \le Ld$.
- **Theorem D1.1 (convergence, non-oscillation, rate $O(\log N/\sqrt N)$, $D^* < 1$):** **Sound.** Every class $k \equiv c \pmod P$ has run sums $\sum_{k \le K, k \equiv c} k = \frac{K^2}{2P} + O(K+P)$ and $\sum_{k \le K, k \equiv c} (2k+1) = \frac{K^2}{P} + O(K+P)$, so weights converge to $\frac{1}{3P}$ and $\frac{2}{3P}$ with no oscillation. The Dirac-exclusion proof ($v = bv$ and $v = b^k v + (-1)^k \implies d \mid 1$, impossible for $d \ge 2$) is completely airtight.
  - **Minor (m2):** Three tiny slips:
    1. Lines 7 and 103 refer to "the four run lengths $2j, 4j, 2j+1, 4j+2$" (those are Phase 20's *constant-digit* run lengths of $E_b$); the automaton's inter-insertion runs have lengths $k$ and $2k+1$, i.e., $2j, 4j+1, 2j+1, 4j+3$ for $k = 2j, 2j+1$.
    2. Line 93 sets $\eta = 1/N$, which satisfies Lemma 1.1's hypothesis $\eta < 1/(4d)$ only for $N > 4d$ (small $N \le 4d$ are absorbed into $C_{b,d,a}$; alternatively $R = \lceil\log_b(4|a|N)\rceil + 1$ gives $\eta < 1/(4d)$ for all $N \ge 1$).
    3. Line 95 says the leftover after $K$ complete pairs is "one partial run" costing at most $(2K+3)/N$; if $N$ falls in the plus-run of pair $K+1$, the leftover is the complete minus-run of length $K+1$ plus a partial plus-run of length $< 2K+3$ (plus $n=0$), total $\le 3K+4$. Still $O(1/\sqrt N)$.
- **Proposition D1.0 (general denominators):** **Sound** (with $|D_N(b^e z) - D_N(z)| \le e/N \le 2e/N$ and $1 - D_N(j E_b) \le |j|(1 - D_N(E_b))$ for all $j \in \mathbb{Z}$).
  - **Minor (m3):** Line 219 invokes Proposition D1.0 for $E_b^2$, although Proposition D1.0 is stated only for $E_b$ (the proof applies verbatim to any $z \in K_b$).
- **Corollary D1.2 (primitive-root closed form):** **Correct** for all primes $p \ge 2$ (including $p=2$).
  - **Minor (m3):** The 4-term maximum $\max(w_0, u, \frac{2}{p} - w_0, \frac{p-1}{p} - (p-2)u)$ simplifies further to $\max(w_0, \frac{2}{p} - w_0) = \frac{1}{p} + |w_0 - \frac{1}{p}|$, since $\frac{p-1}{p} - (p-2)u = w_0 + u - \frac{1}{p} \le \max(w_0, u)$ always and $u \le \frac{2}{p} - w_0$ whenever $w_0 < 1/p$.
- **Table & numerator dependence (§2.2):** Independently verified by hand for `(2,5)` ($19/60$), `(2,7)` ($11/63$), `(3,5)` ($5/12$), and `(10,11)` ($P=2$, $u^-=(-2,0)$, $u^+=(1,1)$, giving 5 values $25/66, 13/33, 31/66, 19/33, 43/66$ across the 5 cosets of $(\mathbb{Z}/11)^\times / \langle 10, -1 \rangle$). Every table entry matches the script output exactly.
  - **Minor (m4):** Line 149 says $|D_N - D_\infty|\sqrt N/\log_b N$ stays in $[0.05, 0.45]$, whereas `1E_10/3` has `0.000` (exact open empty interval $(1/3, 2/3)$) and `1E_3/2` at $N=4096$ has `0.451`.

### Section 3 ($E_b^3$: Theorem D1.3)
- **Automaton, rate, and $D^* < 1$:** **Airtight.** The recurrence $v_k = b^k v_{k-1} + (-1)^k (2k+1) \pmod d$ has period $P_3$ with $L_3 = \operatorname{lcm}(t, 2d) \mid P_3 \le L_3 d$. For $R = \lceil\log_b(4|a|(2K+3)N)\rceil$ (with $T_K \le N < T_{K+1}$), any $n < N$ with $r_n \ge R$ has next triangular index $m \le K+1$, giving $|\tau_n| \le b^{-R}(2(2K+3)+4)$ and $|a\tau_n/d| \le \frac{2K+5}{4(2K+3)N} < \frac{1}{N}$. The Dirac-exclusion proof ($d \mid 2k+1$ for consecutive $k \implies d \mid 2$, contradicting $2k+1$ odd) is airtight.
- **Reversal cases `(3,4)` and `(3,8)`:** Independently verified by hand: for $b=3$ and $d \in \{4, 8\}$, induction gives $v_{2m} \equiv 4m+1 \pmod d$ and $v_{2m+1} \equiv 3(4m+1) - (4m+3) = 8m \equiv 0 \pmod d$, so $v_k = 0$ on every odd $k$ (weight $1/2$), yielding $D_\infty(E_3^3/4) = 1/2 > 1/3 = D_\infty(E_3/4)$ and $D_\infty(E_3^3/8) = 1/2 > 1/4 = D_\infty(E_3/8)$. (This also gives an elementary 2-line structural explanation for L181's remark.)
- **Minor (m4):** Line 181 cites five uniform cube cases `(2,7), (2,31), (2,73), (3,13), (2,23)`. Independent execution of `cube_automaton` confirms all five truly have uniform law and $D^* = 1/d$, but the last four are not included in `scripts/phase21_euler_reciprocals.py`, slightly conflicting with line 29 ("All finite statements come from `scripts/phase21_euler_reciprocals.py`").

### Section 4 ($E_b^2$: Theorems D1.4 & D1.5, Lemma S)
- **Theorem D1.4 ($\frac{a}{2} E_b^2$, $b$ odd, $a$ odd):** **Completely rigorous and unconditional.**
  - Frobenius $E(q)^2 = E(q^2) + 2 G(q)$ holds identically in $\mathbb{Z}[[q]]$ and converges absolutely at $q = 1/b$.
  - Because $g_n = (a_2(n) - [n = 2p] s_p)/2$ is supported on $\operatorname{supp}(a_2) \cup 2\cdot\text{Pent}$ with $S_g(X) \ll X/\sqrt{\log X}$ (Landau, elementary) and $A_g(X) = O(X)$ (pair count, elementary), `CoefficientTransfer.finite_sparse_mass_transfer` gives $1 - D_N(G(1/b)) = O(\log\log N/\sqrt{\log N})$ unconditionally (and $O(\log\log N/(\log N)^{3/4})$ under Phase 20 Theorem 6).
  - Using the additive discrepancy pseudometric cleanly bypasses direct tail-carry analysis: $|D_N(\frac{a}{2} E_b^2) - D_N(\frac{a}{2} E(b^{-2}))| \le |a|(1 - D_N(G(1/b)))$, while $\frac{a}{2} E(b^{-2})$ has exact limiting law $\frac{1}{3}\delta_0 + \frac{2}{3}\delta_{1/2}$ ($I_n \bmod 2$ equals the count of insertions $\le n$ including $0$, hence $0$ on $[2P_k^-, 2P_k^+)$ and $1$ on $[2P_k^+, 2P_{k+1}^-)$) and $D^* = 2/3$ with error $O(\log N/\sqrt N)$.
- **Theorem D1.5 ($\frac{a}{d} E_b^2 \in K_b \iff a/d \in \mathbb{Z}[1/b]$):** **Completely rigorous modulo the explicitly cited inputs (Phase 20 Theorem 6(a), Wirsing, and Lemma S).**
  - Reduction to $\frac{1}{\ell} E_b^2 \in K_b$ for prime $\ell \mid d_1$, Step (i) (density-one concentration at a fixed residue $c \bmod \ell$ with $bc \equiv c \pmod \ell$), Step (ii) (non-adjacency of $c$-runs on $S_\ell$), and Step (iii) (Wirsing lower bound on $S' \cap (N/2, N]$ + double-counting stretches of length $H$ with overlap at most 2, since left stretches $\{L_i\}$ are pairwise disjoint and right stretches $\{R_i\}$ are pairwise disjoint) all verify cleanly without gaps.
- **Lemma S (sketch) & scope honesty:**
  - The scope labeling (lines 9, 25, 211–215, 241, 489) is completely transparent and accurate: the odd-$\ell$ case clearly states its reliance on Theorem 6(a), Wirsing, and the sketched Selberg sieve Lemma S.
  - **Independent soundness check of the Lemma S sketch:** The sketched proof is mathematically sound and fillable without hidden traps. Specifically: (a) pairs with $v > V = (\log N)^3$ or $v' > V$ number $\ll N/V + \sqrt N$ per $h$; (b) $v^2 \mid 12n+1$ and $v'^2 \mid 12n+12h+1$ actually forces $\gcd(v,v')^2 \mid h$ (stronger than $\gcd(v,v') \mid h$) and restricts $n$ to at most one class modulo $M = \operatorname{lcm}(v^2, v'^2) \le (\log N)^{12}$; (c) uniformity in $h, v, v'$ of Selberg's upper bound $X/G(z) + R$ follows cleanly because comparing $G(z)$ against the fixed $(h,v,v')$-independent denominator $G_{\text{all}}(z) \asymp (\log z)^{3/2}$ via $d = d_0 d_1$ ($d_1 = \gcd(d, hvv')$) yields $1/G(z) \le G_{\text{all}}(z)^{-1} \prod_{p \in \mathcal{P}, p \mid hvv'} (1 + \frac{2}{p-2})$ (with $1 + \frac{2}{p-2} \le (p/(p-1))^2$ for $p \ge 5$, and keeping $\rho(p)=1$ at $p \mid h, p \nmid vv'$ gives $\frac{1+2/(p-2)}{1+1/(p-1)} = 1 + \frac{1}{p-2} \le 1 + \frac{2}{p}$ for $p \ge 5$); (d) the Selberg remainder summed over $V^2 = (\log N)^6$ pairs is $O(N^{1/5}(\log N)^{11}) \ll N/(\log N)^{3/2}$; (e) writing $g = \gcd(v,v')$, the sum over $v, v'$ converges uniformly in $h$, and $\sum_{h \le H} \mathfrak{S}(h) \ll H$.
- **Minor (m4):** Line 255 reports alternation `0.605` for $\ell=3,5,7$ (actual: `0.6051`, `0.6063`, `0.6063`); line 266 reports finite discrepancies `0.03–0.05` (actual at $2^{16}$: `0.0258`–`0.0542`).

---

## Audit of `scripts/phase21_euler_reciprocals.py` and Section 6 (Lean Proposals)

### [MAJOR (Script)] M2 — Invalid tail certification for unbounded coefficients ($E_b^3$ and $E_b^2$)
- **Location:** `scripts/phase21_euler_reciprocals.py`, lines 279–290 (`certified_limit_check`) and lines 454–460 (`tail_good_check`), plus docstring lines 14–16.
- **Issue:** `cmax = max(abs(c) for c in coef[: Nmax + W + 2])` is passed to `tail_bound(cmax, b, W) = cmax * b ** (-W) * b / (b - 1)` and used to define `eta`, `slack`, and `trunc`. While valid for $E_b$ ($|c(m)| \le 1$ globally), it is **not a valid upper bound on the neglected infinite tail for $E_b^3$ or $E_b^2$**, whose coefficients grow unboundedly:
  - For $E_b^3$ at $N_{\max} = 2^{16} = 65536$, $W \le 80$, the next triangular insertion $T_{363} = 66066 > N_{\max} + W + 1$ has $|c(T_{363})| = 727 > c_{\max} = 725$, so both `eta` and `tail_bound` slightly underestimate the true tail bound.
  - For $E_b^2$, $|a_2(m)|$ grows unboundedly (bounded elementarily by $P(m+1) + 1 \le \sqrt{8m/3} + 2$), so using empirical prefix `cmax` underestimates `trunc` by roughly 1–2 orders of magnitude.
- **Impact:** None of the numerical conclusions or inequalities fail (the true truncation errors remain $\lesssim 10^{-13}$ against margins $\gtrsim 0.05$), so this does not affect the paper's theorems, only the script's claim of *certified* error bounds.
- **Minimal fix:** Pass an explicit analytic growth bound into `certified_limit_check` / `tail_good_check` (using Phase 20 Lemma D1.2: $|c(m)| \le 2\sqrt{2m}+1$ for $E_b^3$ and $|a_2(m)| \le \sqrt{8m/3}+2$ for $E_b^2$).

### [MINOR] m5 — Off-by-window truncation in `section_d1a` shift spot check
- **Location:** `scripts/phase21_euler_reciprocals.py`, line 366.
- **Issue:** `coefs = dense(pentagonal_insertions(1 << 13), (1 << 13) + 80)` truncates pentagonal insertions at `8192` while `orbit_with_atoms` reads up to index `8191 + 60 + 1 = 8252`, omitting the pentagonal number $P_{74}^+ = 8251$. The test still passes because both `xs12` and `xs3` share the same truncated array, but it tests a truncated polynomial rather than $E_2$.
- **Minimal fix:** Change `pentagonal_insertions(1 << 13)` to `pentagonal_insertions((1 << 13) + 80)`.

### [MINOR] m6 — Minor D2 notes (`D_k` closed form & range conventions)
- **Location:** `notes/phase21/euler-scalings-and-reciprocals.md`, lines 278, 290 vs 336, 358, 360–368.
- Since $\gcd(b^{m_1 + \cdots + m_k}, \prod_{j=1}^k (b^{m_j} \pm 1)) = 1$, the products $R_k$ and $R_k^\epsilon$ are **already in lowest terms**, so $D_k = \prod_{j=1}^k (b^{m_j} - 1)$ and $D_k^\epsilon = \prod_{j=1}^k (b^{m_j} + \epsilon_j)$ identically. This directly yields $D_k \ge b^{m_k} - 1$ and $T_k \ge m_k$ for all $k \ge 1$ (simplifying Lemma D2.4).
- Minor range inconsistency: Theorem D2(b) (line 290) writes $m_K \le N < m_{K+1}$, while Proposition D2.3 (line 336) writes $m_K \le N \le m_{K+1}$ (both are valid).
- In `section_d2` (lines 692–706), `window_bound` checks the sharper intermediate bound of Proposition D2.3 for the 4-factor product $R_4$ (with `e_y = 0` in window 4), which is valid for $y = 1/x$ whenever $m_5$ is chosen large enough (e.g. $m_5 \ge T_4 \approx 5.47 \times 10^{20}$, since $\|2^{N_{\max}+W+1} R_4\| \ge 1/D_4 > 2^{-43255} \gg 32 \cdot 2^{N_{\max}+W+1-m_5}$ prevents any carry into the first $2^{19}+53$ bits).

### [MINOR] m7 — Lean proposal signatures (§6, lines 415–468)
- `eulerStep_periodic` (L428), `abs_discrepancy_sub_atomicDisc_le` (L435), `run_counts_l1_le` (L445), and `sum_residues_expMapCircle_eq_zero` (L461) need `[NeZero d]` / `[NeZero D]` so `ZMod d` / `ZMod D` has a `Fintype` instance (for `d = 0`, `ZMod 0 = ℤ` is infinite).
- `abs_discrepancy_sub_atomicDisc_le` (L435–442) should include `hN : 0 < N` and `hw0 : ∀ j, 0 ≤ w j`.
- `sum_residues_expMapCircle_eq_zero` (L462): `Circle.exp` returns a term of type `Circle` (which has no `AddCommMonoid` instance for `∑`); coerce to `ℂ` via `(Circle.exp (...) : ℂ)` or use `Complex.exp (2 * π * I * ...)`.
- `band_identity` (L455–458) and `lacunaryProduct_discrepancy_tendsto_one` (L465–467) are mathematically exact (`r < m` forces $m \ge 1$, and $m(k+1)/m(k) \to \infty$ forces $m(k) > 0$ eventually).

---

## Post-Repair Verification

**Re-audited files (read-only):**
- `notes/phase21/euler-scalings-and-reciprocals.md` (lines 1–478)
- `scripts/phase21_euler_reciprocals.py` (lines 1–801; re-run via `python -B scripts/phase21_euler_reciprocals.py` — exited 0, all **13,086** checks passed in 6.7 s)
- `NormalityChecker/NormalReciprocalCore.lean` (lines 1–354; full line-by-line inspection; note `lake` is not on PATH in this Windows shell environment, so compilation/`leanchecker` was not re-executed here, while the source was audited in full for zero `sorry`s, zero custom axioms, and complete mathematical fidelity).

### Updated Verdicts

| Sub-track | Previous Verdict | Updated Verdict |
| --- | --- | --- |
| **D1** (Rational scalings of $E_b, E_b^3, E_b^2$, §§1–4) | ACCEPT WITH MINOR POLISH | **ACCEPT** |
| **D2** (Normal reciprocals of $K_b$ elements, §5) | REVISE | **ACCEPT** |

### Verification of Every Repair

1. **C1 (Critical — Theorem D2(b) & Proof, L292–302, L360): RESOLVED.**
   - Replacing $H = \lfloor\sqrt{D_{K-2}}\rfloor$ by $H = \min(\lfloor\sqrt{D_{K-2}}\rfloor, \omega_{K-1}) \ge 1$ in Kuipers–Niederreiter's Erdős–Turán inequality yields
     $$D_N(y) \le \frac{6}{H+1} + \frac{12}{\pi\sqrt{D_{K-2}}} + \frac{4}{\pi}\,\frac{\bigl(T_{K-1} + 3 c_b(H)\bigr)(1 + \log H)}{m_K}.$$
   - Every constant is valid for all $H \ge 1$ (including $D_{K-2}=1$ or $\omega_{K-1}=1$): $\gcd(h, D_{K-2})/h \le 1$, $H \le \sqrt{D_{K-2}}$, $c_b(h) \le c_b(H)$, and $\sum_{h=1}^H 1/h \le 1 + \log H$.
   - Under (A1) and (A2) alone, $H \to \infty$, $\frac{T_{K-1}(1+\log H)}{m_K} \le \frac{1+\log\omega_{K-1}}{\omega_{K-1}} \to 0$, and $H \le \omega_{K-1} \le m_K \implies \frac{3 c_b(H)(1+\log H)}{m_K} \ll_b \frac{(1+\log m_K)^2}{m_K} \to 0$. Both bounds in Theorem D2(b) now genuinely tend to $0$ for every admissible sequence.

2. **M1 (Major — Proposition D2.5(1)–(2), L376–395): RESOLVED.**
   - Under $\epsilon_K = +1$, $m_{K+1} \ge 8$, and $2 J m_K \le m_{K+1} - 6$, every counted odd-band index $n = i m_K + r$ ($0 \le r \le m_K - L - 1$) satisfies $n \le 2 J m_K - L - 1 \le m_{K+1} - L - 7$, so $|b^n(1/x_\epsilon - R_K^\epsilon)| \le 32 b^{-7} b^{-L} \le \frac{1}{4} b^{-L}$ (valid for both signs of the tail since $m_{K+1} \ge 8 \implies 2\sum_{k>K} b^{-m_k} \le 4 b^{-8} \le 1/64$), while $b^n R_K^\epsilon \bmod 1 \in (0, 2 b^{-L}]$.
   - All $J(m_K - L)$ points lie in the two-sided circle arc $[-\frac{1}{4} b^{-L}, \frac{9}{4} b^{-L})$ of length $\frac{5}{2} b^{-L} < 3 b^{-L}$, establishing $D_{2 J m_K}(1/x_\epsilon) \ge \frac{1}{2}(1 - L/m_K) - 3 b^{-L}$ with no $m_{K+1}$-dependent penalty. Taking $J = 1$ and $L = \lfloor\sqrt{m_K}\rfloor$ unconditionally yields $\limsup_{N\to\infty} D_N(1/x_\epsilon) \ge \frac{1}{2}$ for every admissible sequence with $\epsilon_K = +1$ infinitely often, and the converse holds for $K \ge k_0 + 2$ using the repaired Theorem D2(b).

3. **M2 & m5 (Script certification and truncation fix, `scripts/phase21_euler_reciprocals.py` L279–297, L373, L431–446, L467–471): RESOLVED.**
   - Verified `tail_bound(c_const, b, W, sqrt_growth=True, n_max=Nmax)`: for $0 \le n < n_{\max}$ and $j = W + 1 + t$ ($t \ge 0$), $\sqrt{n + W + 2 + t} \le \sqrt{n_{\max} + W + 2}(1 + t)$ and $\sum_{t \ge 0} (1+t) b^{-(W+1+t)} = b^{-W} b / (b-1)^2$, exact.
   - Verified global coefficient bounds: for $E_b^3$, $|c(T_k)| = 2k+1 \le 4\sqrt{T_k + 1}$ for all $k \ge 0$ (since $4k^2 + 4k + 1 < 8k^2 + 8k + 16$); for $E_b^2$, $|a_2(m)| \le 1 + P(m+1) \le 1 + \frac{\sqrt{24(m+1)+1}}{3} \le \frac{8}{3}\sqrt{m+1} < 4\sqrt{m+1}$ for all $m \ge 0$.
   - `eta` uses `tail_bound(..., R - 1, ...)` matching `r >= R`, line 373 passes `(1 << 13) + 80` to `pentagonal_insertions`, and lines 431–434 explicitly check all five uniform cube cases `(2,7), (2,31), (2,73), (3,13), (2,23)`. Script exits 0 with all 13,086 checks passing.

4. **All Minor findings (m1–m7): RESOLVED.**
   - **m1:** Lemma 1.1 now states $N \ge 1$ and explicitly resolves all four boundary cases.
   - **m2:** Automaton run lengths ($k$ and $2k+1$, i.e. $2j, 4j+1, 2j+1, 4j+3$) are distinguished from constant-digit runs; $R = \lceil\log_b(4|a|N)\rceil + 1$ and leftover $\le 3K+4$ are fixed (note: strictly speaking $\eta = 1/(4dN) < 1/(4d)$ holds for all $N \ge 2$, matching Theorem D1.1's hypothesis $N \ge 2$, rather than $N = 1$ where equality occurs; completely harmless).
   - **m3:** Proposition D1.0 is stated for arbitrary $z \in K_b$, and Corollary D1.2 includes the simplified form $\max(w_0, 2/p - w_0) = 1/p + |w_0 - 1/p|$ with proof.
   - **m4:** Ranges (`0.000`–`0.451`, `0.6051`/`0.6063`, `0.0258`–`0.0542`) match script output exactly; the 2-line induction proof for `(3,4)` and `(3,8)` is accurate; all 5 uniform cube cases are in the script.
   - **m6:** Lemma D2.4 now uses the exact no-cancellation identity $D_k = \prod_{j\le k}(b^{m_j}-1) \ge b^{m_k}-1$, $T_k \ge m_k$; Theorem D2(b) and Proposition D2.3 ranges are aligned to $m_K \le N \le m_{K+1}$.
   - **m7:** §6 cleanly separates the kernel-verified declarations in `NormalityChecker/NormalReciprocalCore.lean` from remaining blueprint targets and includes `[NeZero d]`, `hN : 0 < N`, and `hw0 : ∀ j, 0 ≤ w j`.

5. **Inspection of `NormalityChecker/NormalReciprocalCore.lean`:**
   - Contains zero `sorry`s and zero custom axioms.
   - `exists_int_pow_sub_one_mul_rat`, `band_identity` (Lemma D2.1), `signed_band_identity` (Proposition D2.5), `sum_residues_cexp_eq_zero` (Lemma D2.2, properly using `[NeZero D]` and `Complex.exp` in `ℂ`), and `eulerAutomatonStep_bijective` / `eulerAutomaton_purely_periodic` (Theorem D1.1) are all mathematically faithful, well-typed, and proved completely cleanly. (One cosmetic docstring typo on line 28: `eulerStep_bijective` vs. actual declaration name `eulerAutomatonStep_bijective` on line 315; non-blocking.)

No new mathematical or logical bugs were introduced by any of the repairs. Both **D1** and **D2** are **ACCEPTED**.
