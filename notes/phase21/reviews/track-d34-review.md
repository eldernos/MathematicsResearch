# Independent Mathematical Referee Report: Phase 21, Track D (D3–D4)

**Audited documents (read-only):**
- [`notes/phase21/partitions-and-higher-modular.md`](../partitions-and-higher-modular.md) (Tracks D3–D4)
- [`scripts/phase21_partitions_modular.py`](../../scripts/phase21_partitions_modular.py) (executed via `python -B scripts/phase21_partitions_modular.py`: exit code 0, 125,884 assertions passed in 5.1 s)
- Cross-checked against [`NormalityChecker/GeneralMassTransfer.lean`](../../NormalityChecker/GeneralMassTransfer.lean), [`NormalityChecker/EulerPentagonal.lean`](../../NormalityChecker/EulerPentagonal.lean), [`NormalityChecker/CoefficientTransfer.lean`](../../NormalityChecker/CoefficientTransfer.lean), [`notes/phase20/dense-and-partitions.md`](../../phase20/dense-and-partitions.md), [`notes/phase20/theta-and-modular.md`](../../phase20/theta-and-modular.md), and [`notes/phase20/coefficient-transfer.md`](../../phase20/coefficient-transfer.md).

---

## Executive Summary & Verdicts

| Sub-track | Verdict | Critical | Major | Minor |
| :--- | :--- | :---: | :---: | :---: |
| **D3** (Partition constant $P_b = 1/E_b$) | **REVISE** | 0 | 2 | 4 |
| **D4** (Polynomial mass, derivatives, weight $\ge 2$ wall) | **REVISE** | 0 | 4 | 6 |

The mathematical backbone of both tracks is sound, well-motivated, and tightly corroborated by the verification script. No **Critical** (proof-destroying or theorem-invalidating) errors were found: Propositions D3.1–D3.2, Theorem D3.3, Proposition D3.5, Theorems D3.6–D3.7, Theorem D4.1 (including the exact leading constants $j + \frac{1}{2}$ and $j + 1$), Lemma W.1 (including for composite radices), Theorem D4.4, Lemma W.2, Proposition D4.6 (the exact binary telescoping counterexample), and Proposition D4.7 all hold mathematically.

However, both tracks contain concrete **Major** errors in stated formulas, hypotheses, or cross-referenced definitions that require revision before acceptance:
- In **D3**, **Corollary D3.4** omits the integer rounding error $\theta \in (0, 1]$ (making its claimed $o(1)$ error term literally false for integer $L_{\rm el}$) and states a converse sharpness bound $-\log_b(4\sqrt{3}\,N) - O_b(1)$ that fails for small $\tau$ without a $\log(1/\tau) \ll N$ restriction (or replacing $N$ by $N + L_{\rm el}$).
- In **D4**, **Theorem D4.2** displays $D^j E_b$ with the **wrong sign** for all $j \ge 1$ and omits the $j = 0$ constant term (and likewise at $j = 0$ for $D^j \Theta_3$); **Corollary D4.5** omits the non-vanishing hypothesis on residue-class restrictions; **§2.3** silently redefines $W_U(N)$ relative to Phase 20 Theorem 2.2 without supplying the index-shift comparison; and **§2.6** misstates the width-density growth rate of the weight-12 cusp form $\Delta(1/b)$ (and $\Theta_3^3$) as $(\mathrm{weight} - 1)\log_b N$.

Every Major finding below has a minimal, surgical fix.

---

## Part I: Detailed Audit of Track D3 (§1.1–§1.7)

### Item-by-item Verification Summary

- **§1.1 Propositions D3.1 & D3.2 (all-$n$ bounds on $p(n)$): VERIFIED.**
  - D3.1: $p(n) q^n < P(q)$ is strict for $n \ge 1$ (positive other terms including $p(0) = 1$); $1 + q + \dots + q^{j-1} \ge j q^{j-1}$ gives $q^j / (1-q^j) \le q / (j(1-q))$; $e^{-t}/(1-e^{-t}) \le 1/t$; optimizing at $t = \pi/\sqrt{6n}$ gives $K\sqrt{n}$ with $K = \pi\sqrt{2/3}$. Exact.
  - D3.2: From $\eta(\tau) = q^{1/24} P(q)^{-1}$ and $\eta(-1/\tau) = \sqrt{-i\tau}\,\eta(\tau)$ at $\tau = it/(2\pi)$, we have $q = e^{-t}$, $q' = e^{-4\pi^2/t}$, $\sqrt{-i\tau} = (t/(2\pi))^{1/2}$, yielding $P(e^{-t}) = (t/(2\pi))^{1/2} \exp(\frac{\pi^2}{6t} - \frac{t}{24}) P(q')$. At $t = \pi/\sqrt{6n}$: $(t/(2\pi))^{1/2} = (24n)^{-1/4}$, $e^{-t/24} < 1$, $q' = e^{-4\pi\sqrt{6n}} \le e^{-4\pi\sqrt{6}} < e^{-30.78} < 4.3 \times 10^{-14}$, and $\exp(\frac{\pi^2}{6} \frac{q'}{1-q'}) \le 1 + 2 q'$. Valid for all $n \ge 1$.
- **§1.2 Theorem D3.3 (all-$N$ window bound): VERIFIED.**
  - Since $p$ is nondecreasing on $\mathbb{Z}_{\ge 0}$, $\max_{0 \le n < N} T(n,L) = T(N-1,L)$. Every summand $p(N-1+j)$ for $j \ge L+1$ has index $m = N + L + i \ge N + L \ge 1$ (since $N \ge 1, L \ge 0$), so $n = 0$ and small $n$ are handled cleanly without invoking D3.1/D3.2 at $m = 0$.
  - $\lambda = \log b - K/(2\sqrt{N+L}) > 0$ holds whenever $N + L \ge 4$: for $b = 2$, $(K/(2\log 2))^2 \approx 3.4237 < 4$, so $N + L \ge 4$ is exact and sharp.
  - Concavity $\sqrt{N+L+i} \le \sqrt{N+L} + i/(2\sqrt{N+L})$ and monotonicity of both $(24m)^{-1/4}$ and $1 + 2e^{-4\pi\sqrt{6m}}$ yield $B_{\rm el}(N,L)$ and $B_{\rm mod}(N,L)$ cleanly.
- **§1.2 Corollary D3.4 (explicit windows & sharpness): TWO MAJOR ISSUES (D3-M1, D3-M2).**
- **§1.3 Proposition D3.5 (exact carry recurrences): VERIFIED.**
  - (1) Shift register $R_{n+1,L} \equiv b R_{n,L} + p(n+L+1) \pmod{b^L}$ holds for all $n \ge 0, L \ge 1$.
  - (2) Unreduced pentagonal window identity holds for all $n \ge 0, L \ge 1$, including $n = 0$ (where the first sum is empty and the second reassembles via Euler's recurrence at $j \ge 1$).
  - (3) Real tails $T_n = \sum_{j \ge 1} p(n+j) b^{-j}$: interchange of sums is justified by absolute convergence ($\sum_{j \ge 1} (2\sqrt{n+j}+1) e^{K\sqrt{n+j}} b^{-j} < \infty$); boundary sum gives $\beta_n = P_b \sum_{m_i > n} \varepsilon(m_i) b^{n - m_i}$ with $\beta_0 = z P_b = P_b - 1 = T_0$; formal power series inversion $E(t) \sum_{n \ge 0} T_n t^n = \sum_{n \ge 0} \beta_n t^n$ in $\mathbb{R}[[t]]$ gives $T_n = \sum_{m=0}^n p(n-m)\beta_m$ for all $n \ge 0$ with all signs and indices exact.
- **§1.4 Theorem D3.6 (recurrence non-separation): VERIFIED (with one Minor remark D3-m2).**
  - Over $(\mathbb{R}/\mathbb{Z})[[t]]$ as a $\mathbb{Z}[[t]]$-module, $E(t)^{-1} = P(t) \in \mathbb{Z}[[t]]$ gives the exact bijection between admissible sequences and kick sequences $|\rho'_m| \le B_m$.
  - $B_0 = \frac{b}{b-1} P_b b^{-(1-0)} = P_b / (b-1) > P_b - 1 = \beta_0 > 0$ (since $z < \frac{1}{b-1}$), so $P_b$'s actual kicks satisfy $|\beta_n| \le B_n$ for all $n \ge 0$.
  - For $\xi_n = \{\theta p(n)\}$ with $\theta \in (0, B_0)$, $\rho'_0 = \theta$ and $\rho'_n = 0$ ($n \ge 1$) satisfy $|\rho'_n| \le B_n$. Although $p(0) = p(1) = 1$ is a duplicate, $(p(n))_{n \ge 1}$ is strictly increasing, so Weyl's 1916 metric theorem yields equidistribution of $(\{\theta p(n)\})_{n \ge 1}$ for a.e. $\theta \in (0, B_0)$, and prepending the single term $n = 0$ changes $D_N$ by at most $1/N \to 0$.
  - Moreover, even if one requires matching $P_b$'s exact kicks $\rho'_n = \beta_n$ for all $n \ge 1$, the shifted family $\{x_n + \theta p(n)\}$ with $\theta \in (-B_0 - \beta_0, B_0 - \beta_0)$ (a nonempty interval since $B_0 - \beta_0 > P_b/(b^2(b-1)) > 0$) is admissible and equidistributed for a.e. $\theta$ by the same $L^2$ orthogonality proof.
- **§1.5 Theorem D3.7 ($P_b E_b = 1$ rational approximants): VERIFIED (with Minor proof omissions D3-m3).**
  - All 5 parts hold for all $K \ge 3$ and all $b \ge 2$: $Q_K \equiv -\varepsilon(m_K) \pmod b$, $\gcd(Q_K, b) = 1$; $P_b - r_K = \varepsilon(m_{K+1}) P_b r_K b^{-m_{K+1}}(1+\vartheta_K)$ with $|\vartheta_K| \le b^{-(m_{K+2}-m_{K+1})}\frac{b}{b-1} \le \frac{1}{b^2(b-1)} \le \frac{1}{b(b-1)}$; agreement $A \le m_{K+1}$ (noting $\frac{1}{2} b^{-m_{K+1}} \le |P_b - r_K| < b^{-A}$ implies $A < m_{K+1} + 1$, hence $A \le m_{K+1}$ even at $b = 2$); $\|b^n P_b - b^n r_K\| \le 2 P_b^2 b^{n - m_{K+1}}$; Diophantine exponent $1 + \theta_K$ with $\theta_K > 0$ and $\theta_K \asymp m_K^{-1/2}$; pure period $\operatorname{ord}_{Q_K}(b) \ge \log_b(Q_K + 1) \ge m_K - O_b(1)$.
  - Contrast with Phase 20 Theorem D4.4 (failure of R1 and R2) is accurate and illuminating.
- **§1.6 Finite measurements:** All tabulated values ($D_{1000}, D_{2000}, D_{4000}$, word deviations, $\chi^2$, certified digit counts 4044/4030/4022/4017) match the script output verbatim.

---

### Track D3 Findings

#### [Major] D3-M1 — Corollary D3.4 (§1.2, line 82): Missing integer rounding term makes the $o(1)$ error claim literally false
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 79–88.
- **Problem:** Corollary D3.4 defines $L_{\rm el}(N,\tau) \in \mathbb{Z}_{\ge 0}$ as the least integer $L$ with $B_{\rm el}(N,L) < \tau$, and states for all $0 < \tau < 1$:
  $$L_{\rm el}(N,\tau) = \frac{K\sqrt{N}}{\log b} + \frac{K^2}{2\log^2 b} + \log_b\frac{1}{\tau} - \log_b(b-1) + O_b\Bigl(\frac{1 + \log(1/\tau)}{\sqrt{N}}\Bigr).$$
  Whenever $\log(1/\tau) = o(\sqrt{N})$ (for example, fixed $\tau = 1/2$, or $\tau = N^{-2}$ as in the table), the stated error term $O_b((1+\log(1/\tau))/\sqrt{N})$ tends to $0$ as $N \to \infty$. However, $L_{\rm el}(N,\tau)$ is an **integer**, while the continuous main term has non-vanishing fractional part. Direct computation at $b = 2, \tau = 1/2, N = 10^6$ gives $L_{\rm el} - L_{\rm asym} \approx 0.4960$ against $(1+\log(1/\tau))/\sqrt{N} \approx 0.001693$; as $N \to \infty$, $(L_{\rm el} - L_{\rm asym}) / ((1+\log(1/\tau))/\sqrt{N})$ is unbounded.
  Because $\frac{\partial}{\partial L} \log B_{\rm el}(N,L) = -\lambda(N+L) - \frac{e^{-\lambda}}{1-e^{-\lambda}} \frac{K}{4(N+L)^{3/2}} < 0$ for $N+L \ge 4$, $B_{\rm el}(N,L)$ is strictly decreasing in $L$, so $L_{\rm el}(N,\tau) = \lfloor L^*(N,\tau) \rfloor + 1 = L^*(N,\tau) + \theta$ with $\theta \in (0, 1]$ (whenever the continuous root $L^*(N,\tau)$ of $B_{\rm el}(N,L^*) = \tau$ is $\ge \max(0, 4-N)$). The $O_b((1+\log(1/\tau))/\sqrt{N})$ error belongs to the real root $L^*(N,\tau)$, not to the integer $L_{\rm el}(N,\tau)$.
- **Minimal fix:** Either (a) state the asymptotic with error $O_b\bigl(\frac{1 + \log(1/\tau)}{\sqrt{N}}\bigr)$ for the unique real root $L^*(N,\tau)$ of $B_{\rm el}(N, L^*) = \tau$ (for $N$ large enough that $L^* \ge 0$) and record $L_{\rm el}(N,\tau) = \lfloor L^*(N,\tau) \rfloor + 1$, or (b) include the explicit rounding term $+\theta$ with $\theta \in [0, 1]$ (or $+O(1)$) in the formula for $L_{\rm el}(N,\tau)$. Also, in the proof (line 87), note that the Taylor expansion $\sqrt{N+L} = \sqrt{N} + L/(2\sqrt{N}) + O(L^2 N^{-3/2})$ assumes $L = O(N)$ (i.e., $\log(1/\tau) = O(N)$); for $L > N$, invoke the global concavity inequality $0 \le \sqrt{N+L} - \sqrt{N} \le L/(2\sqrt{N})$ directly, or restrict $\tau$ as in D3-M2.

#### [Major] D3-M2 — Corollary D3.4 (§1.2, line 85): Converse sharpness bound fails for very small $\tau$ without a $\tau$-regime hypothesis
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 85.
- **Problem:** Under the sole hypothesis $0 < \tau < 1$, Corollary D3.4 asserts that every $L$ with $T(N-1,L) < \tau$ satisfies $L \ge L_{\rm el}(N,\tau) - \log_b(4\sqrt{3}\,N) - O_b(1)$, and concludes that the elementary window is sharp to within $\log_b N + O(1)$ digits (and the $\eta$-refined window to within $\frac{3}{4}\log_b N + O(1)$).
  In fact, Hardy–Ramanujan gives $p(N+L) \sim e^{K\sqrt{N+L}} / (4\sqrt{3}(N+L))$, so the missing polynomial factor is $4\sqrt{3}(N+L)$, not $4\sqrt{3}\,N$. If $\tau$ is super-exponentially small in $N$ — e.g. $\tau = b^{-N^2}$, where $L \asymp N^2$ — then $L_{\rm el}(N,\tau) - L_{\rm nec}(N,\tau) = \log_b(4\sqrt{3}(N+L_{\rm el})) + O_b(1) \sim 2\log_b N$, violating $\log_b(4\sqrt{3}\,N) + O_b(1)$. (For $b=2, N=100, \tau=2^{-N^2}$, the gap is $17$ vs $\log_2(4\sqrt{3}\cdot 100) \approx 9.44$, matching $\log_2(4\sqrt{3}(N+L_{\rm el})) \approx 16.15$.) Tellingly, `scripts/phase21_partitions_modular.py` line 401 already uses `N + Le` rather than `N`.
- **Minimal fix:** Replace $4\sqrt{3}\,N$ by $4\sqrt{3}(N + L_{\rm el}(N,\tau))$ (and $\log_b N$ by $\log_b(N + \log_b(1/\tau))$), or add the explicit regime hypothesis $\log_b(1/\tau) = O(N)$ (which covers every practical choice such as $\tau = N^{-A}$).

#### [Minor] D3-m1 — §1.2 (line 63): Strict inequality `< T(n,L)` instead of equality `= T(n,L)` modulo 1
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 63.
- **Problem:** Writes "$0 \le x_n - R_{n,L}/b^L < T(n,L)$ modulo 1". By Phase 20 Lemma D1.1, since $p > 0$, $x_n \equiv R_{n,L}/b^L + T(n,L) \pmod 1$ holds with **equality** (not strict inequality $< T(n,L)$).
- **Fix:** Replace with "$x_n \equiv R_{n,L}/b^L + T(n,L) \pmod 1$ with $T(n,L) > 0$" (and note $R_{n,0} = 0$ when $L = 0$).

#### [Minor] D3-m2 — §1.4 (line 137): Remark after Theorem D3.6 omits the $\times b$-shift coupling
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 137.
- **Problem:** The remark states "What distinguishes the true orbit is the exact arithmetic of $\beta_m$". Admissibility also drops the shift coupling $\xi_{n+1} \equiv b \xi_n \pmod 1$, which $\{\theta p(n)\}$ does not satisfy (while both $x_n = \{b^n P_b\}$ and $\xi \equiv 0$ do). Theorem D3.6 itself is unaffected since its stated target is arguments using only the pentagonal recurrence and kick-size bounds (such as Phase 20 Proposition D2.2).
- **Fix:** Note explicitly that admissibility drops both the exact arithmetic of $\beta_m$ and the shift relation $\xi_{n+1} = \{b \xi_n\}$.

#### [Minor] D3-m3 — §1.5 (Theorem D3.7(3), lines 155 & 159): Two brief omitted justifications in the proof
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 155 and 159.
- **Problem:**
  1. Inferring $|P_b - r_K| < b^{-A}$ from agreement in the first $A$ fractional digits requires $\lfloor r_K \rfloor = \lfloor P_b \rfloor$ (true for all $K \ge 3, b \ge 2$ since $|P_b - r_K| < \min(\{P_b\}, 1 - \{P_b\})$, or can be stated as agreeing in integer part and first $A$ fractional digits).
  2. Inferring $\|b^n P_b - b^n r_K\| \le 2 P_b^2 b^{n - m_{K+1}}$ from Part 2 uses $r_K(1 + |\vartheta_K|) \le 2 P_b$, which is true for all $K \ge 3, b \ge 2$ (since $E_b^{(K)} \ge E_2 - 2^{-6} > 0.272 \implies r_K/P_b < 1.063$ and $1 + |\vartheta_K| \le 3/2$, giving $< 1.6 P_b$), but is left unstated.
- **Fix:** Add one sentence in the proof of (3) verifying $\lfloor r_K \rfloor = \lfloor P_b \rfloor$ and $r_K(1 + |\vartheta_K|) \le 2 P_b$.

#### [Minor] D3-m4 — Script/text minor discrepancies and summary-table numbering collision
- **Locations:**
  1. Summary table (lines 15–29): row labels `D3.1–D3.6` and `D4.1–D4.7` collide with different theorem labels in the body (e.g., Summary `D3.4` is Theorem D3.6; Summary `D3.6` is Open §1.7; Summary `D4.4` is Proposition D4.6).
  2. §1.1 (line 59) and `scripts/phase21_partitions_modular.py` (lines 333, 338, 374): `section_partition_bounds` and `mod_tail_bound` check with the looser constant `CMOD = 1.0000001` instead of $1 + 2e^{-4\pi\sqrt{6n}}$ (all 12 table rows are identical either way, as verified directly, since $2e^{-4\pi\sqrt{6}} < 10^{-13}$).
  3. §1.3 (line 121): says (2) is checked for "$n < 400$" whereas `scripts/phase21_partitions_modular.py` line 450 runs `range(1, 400)` (omitting $n = 0$); and says (3) is checked for $n \le 40$ "to precision $2^{-4044}$", whereas `tol = 2**n + 300 * sum(p[:n+1])` at scale $2^{-4044}$ certifies agreement to roughly $2^{-4004}$ at $n = 40$ (working precision $2^{-4044}$).

---

## Part II: Detailed Audit of Track D4 (§2.1–§2.6, §5)

### Item-by-item Verification Summary

- **§2.1 Theorem D4.1 (polynomial-mass transfer rate): VERIFIED (with one Minor remark D4-m1).**
  - Abel summation $\widehat{A}(X) = (1 - b^{-1})\sum_{i \ge 0} b^{-i} A(X+i)$ with $X + i \le X(1+i)$ ($X \ge 1$) and $\kappa \ge 0$ gives $\widehat{A}(X) \le C M_\kappa(b) X^\kappa$.
  - With $\varepsilon = \rho/2$ and $L = \max(0, \lceil \log_b(c_\kappa N^{\kappa-1}/\rho^2) \rceil)$: if $L \le N$, then $\widehat{A}(N+L) \le C M_\kappa(b) (2N)^\kappa$, so the Markov term of Phase 20 Theorem 1.4 is at most $c_\kappa N^{\kappa-1}/(\rho b^L) \le \rho$, yielding $1 - D_N \le (L+2)\rho$. If $L > N$, then $(L+2)\rho \ge (N+3)/N > 1$, so the bound is trivial. The $\max\{2, \dots\}$ properly covers $L = 0$ (critical when $0 \le \kappa < 1$). Works for all $N \ge 1$, all real $\kappa \ge 0$, all $C > 0$, and arbitrary $a(0) \in \mathbb{Z}$.
  - Leading constant: with $1/\rho_N = N^{1 - \lambda_N}$, $2\log_b(1/\rho_N) + (\kappa - 1)\log_b N = (\kappa + 1 - 2\lambda_N)\log_b N$.
  - Specialization to $D^j E_b$ and $D^j \Theta_3(1/b)$: $\kappa = j + \frac{1}{2}$ (since $S(X) \asymp X^{1/2}$ and $|m^j a(m)| \asymp m^j$, so $A(X) \asymp X^{j + 1/2}$) and $\lambda = \frac{1}{2}$, giving $\kappa + 1 - 2\lambda = (j + \frac{1}{2}) + 1 - 1 = j + \frac{1}{2}$. Independent check via Phase 20 §3.3 width formula: $1 - \sigma + \gamma = 1 - \frac{1}{2} + j = j + \frac{1}{2}$. Exact agreement!
  - Specialization to $D^j(E_b^3)$: $\kappa = j + 1$ ($A_0(X) \le 4X \implies A_j(X) \le 4X^{j+1}$) and $\lambda = \frac{1}{2}$, giving $(j+1) + 1 - 1 = j + 1$. Exact!
- **§2.2 Theorem D4.2 & Corollary D4.3 ($K_b$ closure under $D^j$ and sparse polynomials): ONE MAJOR SIGN ERROR (D4-M1) + Minor polish (D4-m4).**
  - The transfer deduction from `GeneralMassTransfer.poly_mass_sparse_tendsto_one` is valid (for $k \in \mathbb{N}$).
  - The identity $E_b^2 \cdot DE_b = \frac{1}{3} D(E_b^3) = \sum_{k \ge 0} (-1)^k \frac{k(k+1)(2k+1)}{6} b^{-k(k+1)/2} \in K_b$ is **100% exact** (coefficients are signed sums of squares $(-1)^k \sum_{i=1}^k i^2 \in \mathbb{Z}$, verified directly at $k = 0,1,2,3$ and by the script through $q^{6000}$).
  - All finite check table entries (lines 259–265) match the script output verbatim.
- **§2.3 Lemma W.1 ($b$-coprime parts survive): VERIFIED.**
  - Works for **every** integer $b \ge 2$, prime or composite (e.g. $b = 6, 12$). Writing $x = x_b x'$ with $\gcd(x', b) = 1$ and $xy = b^V U$, $\gcd(b^V, x') = 1$ forces $b^V \mid x_b y$, so $|U(xy)| = |x'| \cdot (|x_b y|/b^V) \ge |x'|$ (in fact $x' \mid U(xy)$). Even when $v_b(xy)$ jumps strictly above $v_b(x) + v_b(y)$ for composite $b$, the jump only cancels prime factors dividing $b$ and never affects $x'$.
- **§2.3 Theorem D4.4 (abstract wall): VERIFIED.**
  - Unique factorization of $n = pm$ for $p \in \mathcal{P} \cap (Y^{1/2}, Y^{3/4}]$, $1 \le m \le Y/p < Y^{1/2} < p$; $p \nmid m$; partial summation of $\sum_{p \in \mathcal{P} \cap (Y^{1/2}, Y^{3/4}]} 1/p = (\delta \log \frac{3}{2} + o(1))$; $|U(c(pm))| \ge |\lambda(p)'| \ge p^{(k-1)/2} \prod_{q \mid b} q^{-e_0} \ge p^{(k-1)/2} b^{-e_0} > Y^{(k-1)/4} b^{-e_0}$; $u(n) \ge \frac{k-1}{4}\log_b Y - e_0$. Every constant in $\frac{(k-1)\delta s_0 \log(3/2)}{4\log b}$ and $\frac{(k-1)s_1}{2\log b}$ checks out exactly.
- **§2.3 Lemma W.2 (CM newforms satisfy H1–H3): MATHEMATICALLY SOUND (with Minor proof-wording cleanup D4-m2).**
  - (H1) Serre (1981, §7, Thm. 17) + Deligne / direct Grössencharacter bound; (H2) Hecke multiplicativity; (H3) angle part: $p \equiv 1 \pmod M$ splits in $F$ (since $|d_F| \mid M$) and $\chi(p) = 1$, norm mod $M$ factors through $Cl_{M\mathcal{O}_F}(F)$, Hecke (1920) equidistribution gives $|\cos\theta_{\mathfrak{p}}| \ge \frac{1}{2}$ on relative density $\frac{2}{3}$ of $\mathcal{P}_0$; (H3) valuation part: $G = \rho_q(\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q}(\zeta_M)))$ is open in $(\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$ (using $k - 1 \ge 1$), and $\{\operatorname{tr} t = 0\}$ has Haar measure $0$.
- **§2.3 Corollary D4.5 (wall for CM newforms): TWO MAJOR ISSUES (D4-M2, D4-M3).**
  - The four failure bullets for a CM newform $g$ itself are verified (including $A(N) \gg N^{1+(k-1)/4}/\sqrt{\log N}$ on the constructed set, which breaks `log_mass_sparse_tendsto_one`).
  - However, the residue-class restriction sentence (line 311) omits a non-vanishing hypothesis (D4-M2), and the appeal to Phase 20 Theorem 2.2 uses a silently redefined $W_U(N)$ (D4-M3).
- **§2.3 Proposition D4.6 ($W(N) = o(N)$ is not necessary for $K_b$): VERIFIED (with Minor wording fix D4-m3).**
  - For $F = \sum_{m \ge 1}(2^{w(m)} - 1) 2^{-m}$ with $w(m) = \lfloor \log_2 m \rfloor + 1$: $0 < a(m) < 2m$ ensures absolute convergence and $A(X) \ll X^2$; $2^{w(m)}-1$ is odd of exact binary length $w(m)$, so $V(m) = 0$ and $W(N) = W_U(N) = \sum_{m=1}^N w(m) \sim N \log_2 N$ (under *both* raw and displaced index definitions).
  - Putting $\tilde{t}(m) = m - w(m)$, $\tilde{t}(1) = 0$, $\tilde{t}(m+1) - \tilde{t}(m) \in \{0, 1\}$, and $\tilde{t}(m+1) = \tilde{t}(m)$ iff $m = 2^s - 1$ ($s \ge 1$), where the common value is $2^s - s - 1$ (occurring twice, never three times since $2^{s+1} - 2^s \ge 2$). Hence $\sum_{m \ge 1} 2^{-\tilde{t}(m)} = \sum_{t \ge 0} 2^{-t} + \sum_{s \ge 1} 2^{-(2^s-s-1)} = 2 + \sum_{s \ge 1} 2^{-(2^s-s-1)}$, and subtracting $\sum_{m \ge 1} 2^{-m} = 1$ gives the **exact** identity $F = 1 + \sum_{s \ge 1} 2^{-(2^s-s-1)} = 2 + \sum_{s \ge 2} 2^{-(2^s-s-1)} \in K_2$.
- **§2.4 Serre's lacunary eta powers ($\eta^2, \eta^4, \eta^6, \eta^8, \eta^{10}, \eta^{14}, \eta^{26}$): VERIFIED.**
  - All CM fields ($\eta^4, \eta^8, \eta^{14}$: $\mathbb{Q}(\sqrt{-3})$; $\eta^6, \eta^{10}$: $\mathbb{Q}(i)$; $\eta^2$: both, weight 1, $\alpha = 3/4$; $\eta^{26}$: mixed $\mathbb{Q}(i) + \mathbb{Q}(\sqrt{-3})$), levels/characters for $r=4,6,8$, twisted Hecke relation $a(pm) = a(pm_0)a(m)$ for $r=10,14$ and its failure for $r=26$, and nonexistence of weight-$\ge 2$ newforms with $\alpha > 1/2$ (Serre 1981 §7) are all mathematically correct and accurately scoped (unconditional for $r=4,6,8$, conditional for $r=10,14$, finite measurement for $r=26$). All table numbers match the script output.
- **§2.5 Proposition D4.7 (derivatives meet the wall): VERIFIED (with Minor proof detail D4-m5).**
  - $\alpha = 1/2$ for $\Theta_3^2$ (Landau) and $\alpha = 3/4$ for $E_b^2$ (Serre 1981, Thm. 18 on $\eta(12\tau)^2$); both give $\gg X/(\log X)^\alpha$ supported $m \in (X/2, X]$.
  - The number of $m \le X$ with $b$-smooth part $s > \sqrt{X/2}$ is at most $\sum_{\sqrt{X/2} < s \le X,\, s\ b\text{-smooth}} X/s \ll_b \sqrt{X}(\log X)^{\omega(b)} = X^{1/2+o(1)} = o(X/(\log X)^\alpha)$.
  - For all remaining supported $m \in (X/2, X]$, Lemma W.1 gives $|U(m^j a(m))| \ge (m')^j > (X/2)^{j/2}$, hence $u(m) > \frac{j}{2}\log_b(X/2)$ and $W_U(X) \gg_{b,f} j\,X(\log X)^{1-\alpha}$ (and the same holds for $E_b \cdot DE_b = \frac{1}{2} D(E_b^2)$ and $\Theta_3 \cdot D\Theta_3 = \frac{1}{2} D(\Theta_3^2)$).
- **§2.6 Dense classical constants: ONE MAJOR ERROR (D4-M4) + Minor rounding typo (D4-m6).**
  - All algebraic identities ($r_4$, $\Theta_3^4 = \frac{1}{3}(4E_2(q^4)-E_2(q))$, Legendre $r_3$, $\Delta = (E_4^3 - E_6^2)/1728 = q\prod(1-q^n)^{24}$, and the mod-$K_b$ reductions) are exact, and all table values match the script output.
- **§5 Recommended Lean finite cores:** Cross-checked against `GeneralMassTransfer.lean`, `EulerPentagonal.lean`, and `CoefficientTransfer.lean`; all 8 items are genuinely feasible and accurately reflect what is and is not currently formalized (see Minor notes D4-m4).

---

### Track D4 Findings

#### [Major] D4-M1 — Theorem D4.2 (§2.2, line 232): Wrong sign for $D^j E_b$ (all $j \ge 1$) and missing $j = 0$ constant terms
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 231–235.
- **Problem:** Line 232 writes, for "all $j \ge 0$":
  $$D^j E_b = \sum_i \varepsilon(m_i)\,m_i^j\,b^{-m_i}, \qquad D^j(E_b^3) = \sum_{k \ge 0} (-1)^k (2k+1) T_k^j b^{-T_k}, \qquad D^j \Theta_3(1/b) = 2 \sum_{n \ge 1} n^{2j} b^{-n^2}.$$
  Because line 9 defines $E_b = 1 - \sum_{i \ge 1} \varepsilon(m_i) b^{-m_i}$, applying $D^j = (q\frac{d}{dq})^j$ at $q = 1/b$ gives:
  - for $j \ge 1$: $D^j E_b = \mathbf{-}\sum_{i \ge 1} \varepsilon(m_i) m_i^j b^{-m_i}$ (line 232 has the **opposite sign**, equaling $-D^j E_b$);
  - for $j = 0$: $D^0 E_b = 1 - \sum_{i \ge 1} \varepsilon(m_i) b^{-m_i}$ and $D^0 \Theta_3(1/b) = 1 + 2\sum_{n \ge 1} b^{-n^2}$ (both omit the leading constant term $1$; only $D^j(E_b^3)$ recovers $1$ at $j = 0$ via $T_0^0 = 0^0 = 1$).
  (Note that `EulerPentagonal.pentCoeff` in Lean has the correct sign `(-1)^k = -ε(m_i)` and `pentCoeff 0 = 1`, and the $K_b$-membership statement remains true since $K_b$ is a group containing $\mathbb{Z}$.)
- **Minimal fix:** Write the displayed identities as
  $$D^j E_b = \delta_{j,0} - \sum_{i \ge 1} \varepsilon(m_i)\,m_i^j\,b^{-m_i}, \qquad D^j(E_b^3) = \sum_{k \ge 0} (-1)^k (2k+1) T_k^j b^{-T_k}, \qquad D^j \Theta_3(1/b) = \delta_{j,0} + 2 \sum_{n \ge 1} n^{2j} b^{-n^2}$$
  (with $0^0 = 1$ at $k = 0$ in the middle formula), or restrict the displayed expansions to $j \ge 1$ with the minus sign on $D^j E_b$ and cite Phase 20 for $j = 0$.

#### [Major] D4-M2 — Corollary D4.5 (§2.3, line 311): Residue-class restriction claim lacks a non-vanishing hypothesis
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 311.
- **Problem:** States unconditionally: "The same conclusion holds for the restriction of such a form to the residue classes $\equiv m_0 \pmod M$, because (H2) then holds for $p \equiv 1 \pmod M$ with $\lambda(p) = a(p)$."
  This is **false** if the class $m_0 \pmod M$ contains no supported indices of $g$ — for example, $m_0 \equiv 2 \pmod 3$ for $\eta(6\tau)^4$ (CM by $\mathbb{Q}(\sqrt{-3})$), where the restriction is identically zero and $W_U \equiv 0$. Although (H2) holds automatically, Theorem D4.4 also requires the lower bound $S_{c_{\rm res}}(Y) \ge s_0 Y / \sqrt{\log Y}$ in (H1).
- **Minimal fix:** Qualify the sentence to any residue class $\equiv m_0 \pmod M$ that contains at least one supported index $n_0$ with $a(n_0) \ne 0$ (or explicitly satisfies $S(Y) \gg Y/\sqrt{\log Y}$). If one wants the clean justification from a single $n_0 \equiv m_0 \pmod M$ with $a(n_0) \ne 0$: multiplying $n_0$ by integers $r \equiv 1 \pmod M$ coprime to $M n_0$ with $a(r) \ne 0$ yields $\gg Y/\sqrt{\log Y}$ supported indices $\equiv m_0 \pmod M$ (by orthogonality of Dirichlet characters mod $M$, since $\chi_0$ and $\chi_F$ contribute $\sim c_0 X/\sqrt{\log X}$ while every other character mod $M$ contributes $o(X/\sqrt{\log X})$ by Halász's theorem).

#### [Major] D4-M3 — §2.3 (lines 269, 309) vs Phase 20 Theorem 2.2: Silent redefinition of $W_U(N)$ without the index-shift comparison
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 269, 284, 309, 361; compare `notes/phase20/coefficient-transfer.md`, line 197.
- **Problem:** Phase 20 Theorem 2.2 defines the displaced width over **displaced** indices $t(m) = m - V(m)$:
  $$W_U^{\rm disp}(N) = \sum_{1 \le t(m) \le N} u(m).$$
  Phase 21 line 269 writes "Recall the displaced data of Phase 20 §2 ... and the displaced width $W_U(N) = \sum_{m \le N,\, a(m)\ne 0} u(m)$", silently switching to raw indices $m \le N$, then asserts generally $W(N) \ge W_U(N)$ (which holds for raw indices, but can fail for $W_U^{\rm disp}$ when $V(m)$ shifts terms from $m > N$ into $t(m) \le N$) and invokes Phase 20 Theorem 2.2's union bound $W_U(N) + L(1+P(N)) + \Lambda_N$ in Corollary D4.5 (line 309) and Proposition D4.7 (line 361).
  For sequences with polynomial growth $|a(m)| \le m^{O(1)}$, $0 \le V(m) \le O(\log m)$, so $t(m) = m - O(\log m)$ and $|W_U^{\rm disp}(N) - W_U^{\rm raw}(N)| = O((\log N)^2)$. Thus the asymptotic walls in Theorem D4.4, Corollary D4.5, and Proposition D4.7 hold identically for Phase 20's $W_U^{\rm disp}(N)$ too — but the missing bridge leaves a definitional mismatch with Phase 20.
- **Minimal fix:** Explicitly note that $W_U(N)$ here sums over $1 \le m \le N$ (or write $W_U^{\rm raw}(N)$) and add one sentence showing that whenever $|a(m)| \le m^{O(1)}$, $V(m) = O(\log m)$ implies $W_U^{\rm disp}(N) = W_U(N) + O((\log N)^2)$, so every asymptotic lower bound transfers verbatim to Phase 20 Theorem 2.2's $W_U^{\rm disp}(N)$.

#### [Major] D4-M4 — §2.6 (line 395): False width-density growth law for cusp forms ($\Delta(1/b)$) and $\Theta_3^3$
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 395.
- **Problem:** Referring to the 6-row table ($\Theta_3^3, \Theta_3^4, E_2, E_4, E_6, \Delta$), line 395 claims:
  > The width densities grow like $(\text{weight} - 1)\log_b N$.
  This holds for the Eisenstein series $E_2, E_4, E_6$ and $\Theta_3^4$, where $|a(n)| \asymp n^{k-1}$. It is **false** for:
  1. **$\Delta(1/b)$ (weight $k = 12$, cusp form):** By Deligne's theorem, $|\tau(n)| \le d(n) n^{(k-1)/2} = n^{11/2 + o(1)}$, NOT $n^{k-1} = n^{11}$. Its width density grows at most like $\frac{k-1}{2}\log_b N = 5.5\log_b N$, half the stated slope — as already visible in the table itself, where at $N = 4000, b = 2$, $\Delta(1/2)$ has $W_2/N = 56.61 < 62.12$ for weight-6 $E_6(1/2)$!
  2. **$\Theta_3^3$ (weight $3/2$):** By Legendre's three-square theorem, the support has density $5/6$, so $W_b(N)/N \sim \frac{5}{6}(\frac{3}{2} - 1)\log_b N = \frac{5}{12}\log_b N$, not $\frac{1}{2}\log_b N$.
- **Minimal fix:** Replace the sentence on line 395 with: "The width densities grow like $(k-1)\log_b N$ for the weight-$k$ Eisenstein series $E_2, E_4, E_6$ and $\Theta_3^4$, like $\frac{5}{12}\log_b N$ for $\Theta_3^3$ (weight $\frac{3}{2}$, support density $\frac{5}{6}$), and at most like $\frac{k-1}{2}\log_b N = \frac{11}{2}\log_b N$ for the weight-$12$ cusp form $\Delta$."

#### [Minor] D4-m1 — §2.1 (lines 217, 223): Support-exponent range of $(\kappa + 1 - 2\lambda_N)/\log b$ when $\kappa < 1$
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 217 and 223.
- **Problem:** Line 223 states that $(\kappa + 1 - 2\lambda_N)/\log b$ "ranges from $(\kappa + 1)/\log b$ for bounded support down to $(\kappa - 1)/\log b$ for support of density $N^{1-o(1)}$." Since $a(m) \in \mathbb{Z}$, $S(X) \le A(X) \le C X^\kappa$, forcing $\lambda_N \le \min(1, \kappa) + o(1)$. For $0 \le \kappa < 1$ (such as $E_b$ and $\Theta_3$ at $j = 0$, where $\kappa = 1/2$), density $N^{1-o(1)}$ is impossible and the actual range is $[1 - \kappa, 1 + \kappa]/\log b$ (always nonnegative); the lower endpoint $(\kappa - 1)/\log b$ applies only for $\kappa \ge 1$. (Also $\lambda_N = \log(1+S(N-1))/\log N$ on line 217 requires $N \ge 2$.)
- **Fix:** State "for $\kappa \ge 1$, it ranges from $(\kappa+1)/\log b$ down to $(\kappa-1)/\log b$; for $0 \le \kappa < 1$, $S \le A$ forces $\lambda_N \le \kappa + o(1)$, so the range is $[1-\kappa, 1+\kappa]/\log b$."

#### [Minor] D4-m2 — §2.3 (Lemma W.2 proof sketch, line 302): Variable conflation in $\{\operatorname{tr} t = 0\}$ and natural density of $\mathcal{P}$
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 302.
- **Problem:**
  1. Line 302 defines $G = \rho_q(\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q}(\zeta_M)))$ as an open subgroup of the Cartan torus $(\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$, and then writes: "On each coset of the kernel of the finite part, that set [$\{\operatorname{tr} t = 0\}$] is $\{t : (t/\bar{t})^{k-1} = \text{const}\}$." This conflates an element $t \in G \subseteq (\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$ (where $\operatorname{tr} t = t + \bar{t} = 0$ is simply $t/\bar{t} = -1$, a 1-dimensional closed subset of the 2-dimensional $q$-adic Lie group $G$) with a local Artin preimage $\alpha \in (\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$ before raising to the $(k-1)$-st power. (The exponent $k - 1 \ge 1$ is already what guarantees that $G$ is open in $(\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$.)
  2. Minor omissions in the same paragraph: clarify "relative density inside $\mathcal{P}_0$", take a union bound over the finitely many primes $q \mid b$, and note that the finite extension cut out by $\rho_q \bmod q^{e_0+1}$ ($q \mid b$) and $\mathbb{Q}(\zeta_M)$ is abelian over $F$ (hence lies in a ray class field of $F$), so Hecke's theorem gives equidistribution of $\theta_{\mathfrak{p}}$ inside each Frobenius class — ensuring $\mathcal{P}$ genuinely has a natural density as required by (H2) (alternatively, observe that Theorem D4.4's partial summation only requires lower natural density $\ge \delta$).
- **Fix:** Replace the sentence describing $\{\operatorname{tr} t = 0\}$ with: "Because $k - 1 \ge 1$, $G$ is an open subgroup of the $2$-dimensional $q$-adic Lie group $(\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$, and $\{t \in G : \operatorname{tr} t = 0\} = \{t \in G : t + \bar{t} = 0\}$ is a $1$-dimensional closed subset, hence has Haar measure $0$." Add one clause for the union bound over $q \mid b$ and ray-class compatibility.

#### [Minor] D4-m3 — §2.3 (Proposition D4.6, lines 317–323): "super-exponential" should be "exponential", plus notation reuse
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 317–323.
- **Problem:**
  1. Line 323 describes the digit-$1$ positions $2^s - s - 1$ as "of super-exponential growth"; $2^s - s - 1 \sim 2^s$ is **exponential** growth in $s$, not super-exponential.
  2. Note $s = 1$ gives $2^1 - 1 - 1 = 0$ (contributing an integer $1$, so $F = 2 + \sum_{s \ge 2} 2^{-(2^s-s-1)}$).
  3. Line 317 reuses $t(m) = m - w(m)$ for what Phase 20 §2.1 called $\tilde{t}(m)$ (whereas $t(m) = m - V(m)$ is the displaced index elsewhere in §2.3).
- **Fix:** Change "super-exponential" to "exponential", optionally rename $t(m)$ to $\tilde{t}(m)$ in the proof, and write $2 + \sum_{s \ge 2} 2^{-(2^s-s-1)}$ if referring to fractional digit-$1$ positions.

#### [Minor] D4-m4 — §2.2 & §5 (Lean alignment & Corollary D4.3 wording)
- **Locations:** `notes/phase21/partitions-and-higher-modular.md`, lines 229, 237, 249, 416–417.
- **Items:**
  1. In Theorem D4.2 (line 229), state $k \in \mathbb{N}$ and $C \ge 0$ to match `GeneralMassTransfer.poly_mass_sparse_tendsto_one`.
  2. In line 237 and §5 item 1 (line 416), `EulerPentagonal.pentCoeff_absMass_le` already establishes `absMass pentCoeff X ≤ X` ($C = 1$), so deducing $C = 5$ from `pentagonal_supportCount_le` and `abs_pentCoeff_le_one` is unnecessary.
  3. In Corollary D4.3 (line 249), "any polynomial with $\mathbb{Z}[1/b]$ coefficients ... then $\mathcal{P}(\dots) \in K_b$ for every $b$" slightly mixes quantifiers on $b$; say "For each $b \ge 2$, let $\mathcal{P}$ be any polynomial with $\mathbb{Z}[1/b]$ coefficients ... then $\mathcal{P}(\dots) \in K_b$" (or "with $\mathbb{Z}$ coefficients ... for every $b \ge 2$").
  4. In §5 item 2 (line 417), note explicitly that identifying the triangular series $c(T_k) = (-1)^k k(k+1)(2k+1)/6$ with $E_b^2 DE_b$ still relies on Jacobi's triple-product identity (external to Lean, matching `EulerPentagonal.lean`'s documented convention).

#### [Minor] D4-m5 — §2.5 (Proposition D4.7, line 361): Factor of $1/2$ in $E_b \cdot DE_b$
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, lines 361–363.
- **Problem:** The proof of Proposition D4.7 applies Lemma W.1 to $m^j a(m)$, whereas $E_b \cdot DE_b = \frac{1}{2} D(E_b^2)$ has integer coefficients $\tilde{c}(m) = m c_2(m) / 2$. The claim is true (for $2 \mid b$, $m'$ is odd so $m' \mid \tilde{c}(m)$ gives $|U(\tilde{c}(m))| \ge m'$ with no loss; for $2 \nmid b$, $|U(\tilde{c}(m))| = \frac{1}{2}|U(m c_2(m))| \ge \frac{1}{2} m'$, losing at most $1$ digit; for $\Theta_3 \cdot D\Theta_3$, $2 \mid r_2(m)$ so $r_2(m)/2 \in \mathbb{Z}$ directly).
- **Fix:** Add one parenthetical sentence explaining that halving $m c_2(m)$ (or $r_2(m)$) reduces $|U|$ by at most a factor of $2$.

#### [Minor] D4-m6 — §2.6 (line 395): Upper endpoint of finite discrepancy range for $E_2^r$
- **Location:** `notes/phase21/partitions-and-higher-modular.md`, line 395.
- **Problem:** Writes "$D_{4000}(E_2^r)$ ... lies between $0.015$ and $0.025$ for $r \in \{4,6,8,10,14,26\}$", whereas `scripts/phase21_partitions_modular.py` prints `r=14: 0.0253` ($> 0.025$).
- **Fix:** Change "$0.025$" to "$0.026$" (or "$0.0253$").

---

## Summary of Required Revisions Before Acceptance

1. **D3-M1 & D3-M2 (Corollary D3.4):** Introduce the integer rounding term $\theta \in (0, 1]$ (or state the $O_b((1+\log(1/\tau))/\sqrt{N})$ asymptotic for the continuous root $L^*$) and either replace $N$ by $N + L_{\rm el}(N,\tau)$ in the converse sharpness bound or restrict to $\log_b(1/\tau) = O(N)$.
2. **D4-M1 (Theorem D4.2):** Correct the sign of $D^j E_b$ to $-\sum_{i \ge 1} \varepsilon(m_i) m_i^j b^{-m_i}$ and account for $\delta_{j,0}$ at $j = 0$ in both $D^j E_b$ and $D^j \Theta_3(1/b)$.
3. **D4-M2 (Corollary D4.5):** Add the non-vanishing hypothesis on the residue class $m_0 \pmod M$ (at least one supported index $n_0 \equiv m_0 \pmod M$ with $a(n_0) \ne 0$).
4. **D4-M3 (§2.3 $W_U(N)$ definition):** Reconcile the raw-index $W_U(N)$ with Phase 20 Theorem 2.2's displaced-index $W_U^{\rm disp}(N)$ via $W_U^{\rm disp}(N) = W_U(N) + O((\log N)^2)$ under $|a(m)| \le m^{O(1)}$.
5. **D4-M4 (§2.6 width densities):** Distinguish cusp-form growth ($\le \frac{k-1}{2}\log_b N = \frac{11}{2}\log_b N$ for $\Delta$) and $\Theta_3^3$ ($\frac{5}{12}\log_b N$) from Eisenstein growth ($(k-1)\log_b N$).
6. Apply the Minor clarifications (D3-m1–m4, D4-m1–m6), especially the summary-table numbering alignment and the Lemma W.2 trace-zero wording.

---

## Post-Repair Verification

**Updated Verdicts:**
- **Track D3:** **ACCEPT** (0 Critical, 0 Major, 0 Minor remaining)
- **Track D4:** **ACCEPT** (0 Critical, 0 Major, 0 Minor remaining)

### Verification of All Repairs in `notes/phase21/partitions-and-higher-modular.md`

Re-read the entire revised document [`notes/phase21/partitions-and-higher-modular.md`](../partitions-and-higher-modular.md) (lines 1–436). Every Major and Minor finding from the initial review has been cleanly resolved with no new mathematical or expositional bugs introduced:

- **D3-M1 & D3-M2 (Corollary D3.4, lines 79–90):** Verified fixed. The derivative $\partial_L \log B_{\rm el}(N,L) = -\lambda - \frac{e^{-\lambda}}{1-e^{-\lambda}}\frac{K}{4(N+L)^{3/2}} < 0$ ($N + L \ge 4$) establishes strict monotonicity and uniqueness of the continuous root $L^*(N,\tau) \ge 0$ for large $N$, separating the continuous asymptotic (with remainder $O_b((1 + \log^2(1/\tau)/N + \log(1/\tau))/\sqrt{N})$, which in fact holds with a $b$-only implied constant via the global bound $|\sqrt{N+x} - \sqrt{N} - x/(2\sqrt{N})| \le x^2/(8N^{3/2})$) from the integer rounding relation $L_{\rm el}(N,\tau) = \lfloor L^*(N,\tau) \rfloor + 1 = L^*(N,\tau) + \theta$, $\theta \in (0, 1]$. The converse bound is now stated unconditionally as $L \ge L_{\rm el}(N,\tau) - \log_b(4\sqrt{3}(N + L_{\rm el}(N,\tau))) - O_b(1)$, yielding $\log_b N + O(1)$ and $\frac{3}{4}\log_b N + O(1)$ whenever $\log_b(1/\tau) = O(N)$, and $\log_b(N + \log_b(1/\tau)) + O(1)$ unconditionally.
- **D3-m1–m4:** Verified fixed. Exact congruence $x_n \equiv R_{n,L}/b^L + T(n,L) \pmod 1$ with $T(n,L) > 0$ and $R_{n,0} = 0$ (line 63); shift-coupling remark added after Theorem D3.6 (line 139); Theorem D3.7(3) proof now verifies $E_b^{(K)} \ge E_2 - 2^{-6} > 0.272$, $r_K(1 + |\vartheta_K|) < 1.6 P_b \le 2 P_b$, and $|P_b - r_K| < \min(\{P_b\}, 1 - \{P_b\})$ forcing $\lfloor r_K \rfloor = \lfloor P_b \rfloor$ for all $K \ge 3, b \ge 2$ (line 161); Summary table rows (lines 15–29) are now indexed by section (`§1.1`–`§2.6`) with exact theorem references; script prefactor, $n$-range, and working-precision caveats are accurately stated (lines 59, 123).
- **D4-M1 (Theorem D4.2, lines 231–240):** Verified fixed. Added $k \in \mathbb{N}, C \ge 0$; corrected displayed expansions to $D^j E_b = \delta_{j,0} - \sum_{i \ge 1} \varepsilon(m_i) m_i^j b^{-m_i}$ and $D^j \Theta_3(1/b) = \delta_{j,0} + 2\sum_{n \ge 1} n^{2j} b^{-n^2}$ (with $0^0 = 1$ at $k = 0$ in $D^j(E_b^3)$), exact for all $j \ge 0$; explicitly noted external Euler/Jacobi product identifications; updated proof to use `pentCoeff_absMass_le` ($A \le X$).
- **D4-M2 (Corollary D4.5, line 313):** Verified fixed. Qualified the residue-class restriction to classes $\equiv m_0 \pmod M$ containing at least one supported index $n_0$ with $a(n_0) \ne 0$, with the concise character-orthogonality / Halász justification for $S(Y) \gg Y/\sqrt{\log Y}$.
- **D4-M3 (§2.3 $W_U(N)$ vs $W_U^{\rm disp}(N)$, lines 271, 306–311):** Verified fixed. Explicitly defined raw-index $W_U(N)$ over $1 \le m \le N$ and proved $W_U^{\rm disp}(N) = W_U(N) + O((\log N)^2)$ whenever $|a(m)| \le m^{O(1)}$, bridging cleanly to Phase 20 Theorem 2.2.
- **D4-M4 (§2.6 width densities, line 397):** Verified fixed. Accurately distinguishes $(k-1)\log_b N$ (Eisenstein $E_2, E_4, E_6$ and $\Theta_3^4$), $\frac{5}{12}\log_b N$ ($\Theta_3^3$, weight $\frac{3}{2}$, support density $\frac{5}{6}$), and $\le \frac{11}{2}\log_b N$ ($\Delta$, weight $12$, Deligne's bound).
- **D4-m1–m6:** Verified fixed. $\lambda_N$ restricted to $N \ge 2$ and $[1-\kappa, 1+\kappa]/\log b$ split for $0 \le \kappa < 1$ (lines 219, 225); Lemma W.2 valuation part rewritten cleanly in terms of the open subgroup $G \subseteq (\mathcal{O}_F \otimes \mathbb{Z}_q)^\times$, $1$-dimensional $\{t \in G : t + \bar{t} = 0\}$, union bound over $q \mid b$, and ray-class compatibility (line 304); Proposition D4.6 uses $\tilde{t}(m)$, $2 + \sum_{s \ge 2} 2^{-(2^s-s-1)}$, and "exponential growth" (lines 319–325); Corollary D4.3 quantifiers fixed (line 251); Proposition D4.7 halving remark added (line 365); finite range updated to `0.015`–`0.026` (`max 0.0253` at `r = 14`, line 397).

### Inspection of `NormalityChecker/DerivativeTransfer.lean`

Conducted a complete line-by-line read-only audit of [`NormalityChecker/DerivativeTransfer.lean`](../../NormalityChecker/DerivativeTransfer.lean) (485 lines; note that `lake` is not installed on the Windows PATH in this review environment, so verification here is a thorough static audit of every definition, theorem statement, and proof step, complementing the author's reported zero-warning `lake build` and `leanchecker` replay):

- **Soundness & completeness:** Zero `sorry`, `admit`, or custom `axiom`s anywhere in the file. Every declaration cited in `notes/phase21/partitions-and-higher-modular.md` (lines 11, 239, 257, 418–421) exists verbatim with the stated signature and semantics.
- **Part 1 (`derivCoeff`, lines 49–127):** `(m : ℤ)^j * a m` matches $D^j$ for all $j \ge 0$ (including $0^0 = 1$ at $j = 0, m = 0$). `derivCoeff_supportCount_le`, `derivCoeff_absMass_le`, `derivCoeff_poly_mass`, `derivCoeff_tendsto_one`, and `derivCoeff_preserves_discrepancy` cleanly compose with `GeneralMassTransfer.poly_mass_sparse_tendsto_one` / `preserves_discrepancy`.
- **Part 2 (Instantiations, lines 130–321):** `tendsto_sqrt_mul_log_div_self` and all six discrepancy/preservation theorems for `pentCoeff` ($C=1$), `jacobiCubeCoeff` ($C=4$), and `thetaThreeCoeff` ($C=2$) are mathematically sound, with the external-identity scope (Euler's pentagonal theorem and Jacobi's triple-product identity) explicitly documented in both the Lean docstring and the Markdown note.
- **Part 3 (`eulerSqDerivCoeff`, lines 322–403):** `six_dvd_sum_sq_num`, `three_mul_eulerSqDerivCoeff` (`3 * eulerSqDerivCoeff m = derivCoeff 1 jacobiCubeCoeff m`), and `eulerSqDeriv_discrepancy_tendsto_one` are exact and free of edge-case bugs (including at $m = 0$).
- **Part 4 (Lemma W.1, lines 404–429):** `coprimePart_le_natAbs_radixUnit_mul` uses `CoefficientTransfer.radixVal_mul_radixUnit` and `Nat.Coprime.pow_right` + `dvd_of_dvd_mul_left` to prove `d ≤ (radixUnit b (x * y)).natAbs` for all nonzero `x y : ℤ`, `d ∣ x.natAbs`, `Nat.Coprime d b` (valid for arbitrary composite $b \ge 2$ where `not_dvd_radixUnit` guarantees maximality of `radixVal`).
- **Part 5 (Shift register, lines 430–485):** `carryWindow_succ_eq` and `carryWindow_succ_modEq` prove the exact integer shift identity $\widehat{R}_{n+1,L} + a(n+1)b^L = b\widehat{R}_{n,L} + a(n+L+1)$ and its congruence modulo $b^L$ for all $b, n, L \in \mathbb{N}$ (handling $L = 0$ cleanly).

Both **D3** and **D4** are ready for acceptance.
