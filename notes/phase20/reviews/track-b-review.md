# Phase 20 Track B — Mathematical Referee Report

**Reviewer:** Gemini 4 Argon (independent cross-provider mathematical referee)  
**Target files audited:**
- `notes/phase20/coefficient-transfer.md` (Tracks B1, B2, B3)
- `notes/phase20/lambert-leading-constant.md` (Track B4)
- `scripts/phase20_transfer.py`
- `NormalityChecker/CoefficientTransfer.lean`

---

## Overall Verdicts

| Track | Subject | Verdict | Summary |
|---|---|---|---|
| **B1** | Finite all-prefix transfer, linear-mass rate & constant $2$, larger mass (`coefficient-transfer.md` §1) | **Accept (Valid; 1 Minor note)** | Theorems 1.4, 1.5, Proposition 1.6, and Theorem 1.7 are mathematically sound. Every index and radix edge case checks out. One minor edge case in the sufficient condition (148) when $M(X)\equiv 1$. |
| **B2** | Composite-radix displaced-source factorization, width transfer & counterexamples (`coefficient-transfer.md` §2) | **Accept (Valid; 2 Minor notes)** | Theorems 2.1 and 2.2 and counterexamples (a), (b), (c) are valid across all prime and composite radices $b \ge 2$. Minor wording clarification in the Markov step of Theorem 2.2 and small-$k$ threshold in counterexample (c). |
| **B3** | Exact source decomposition, circle separation, isolated-source law, prime constant, growing widths & shadow law (`coefficient-transfer.md` §3) | **Accept (Valid; 3 Minor notes)** | Lemmas 3.1–3.3, Theorem 3.4, Corollary 3.5, Case 3, and Theorem 3.6 are valid. Minor precision notes on hypotheses (I1)/(I3) of Theorem 3.4 and the single boundary source $t_* > N$ in Theorem 3.6. |
| **B4** | Leading constant for $L_{\chi_4}$, $\Theta_3(1/2)^2$, and $L_\chi$ (`lambert-leading-constant.md`) | **Accept (Valid; 1 Minor note)** | The asymptotic $1 - D_N(L_{\chi_4}; 2) \sim \frac{K}{2\log 2}\frac{\log\log N}{\sqrt{\log N}}$ and its generalization to $L_\chi$ are completely rigorous. Both the upper bound and all five exceptional-set estimates (E1)–(E5) in the lower bound are verified line by line. |
| **Lean & Script** | `NormalityChecker/CoefficientTransfer.lean` & `scripts/phase20_transfer.py` | **Accept (Valid; 1 Minor sync note)** | `scripts/phase20_transfer.py` runs in 14.9 s (exit 0) and reproduces all reported numbers. The notes' status sections (§6) should be updated to reflect that `CoefficientTransfer.lean` already kernel-verifies core B1–B3 theorems. |

**Severity tallies:** **0 Critical**, **0 Major**, **8 Minor**.

---

## 1. Detailed Audit of Track B1 (`coefficient-transfer.md` §1)

### 1.1 Verification of Lemmas 1.1–1.3 and Theorem 1.4
- **Lemma 1.1 (integral terms drop out):** For fixed $n \ge 0$ and $I \subseteq \{m > n : b^{m-n} \mid a(m)\}$, summability $\sum_{m\ge 1} |a(m)|b^{-m} < \infty$ forces $|a(m)|b^{-m} < b^{-n}$ for all sufficiently large $m$, so only finitely many $m \in I$ have $a(m) \ne 0$. Hence $\sum_{m\le n} a(m)b^{n-m} + \sum_{m\in I} a(m)b^{n-m} \in \mathbb Z$, and $\|b^n F\| \le \sum_{m>n, m\notin I} |a(m)|b^{n-m}$. With $I = \emptyset$ and $a(n+1) = \dots = a(n+L) = 0$, this yields $\|b^n F\| \le \tau_L(n)$. **Verified.**
- **Lemma 1.2 (shadow count) — edge-case audit:**
  - *Index $n = N - 1$ and $a(N) \ne 0$:* The shifts $n \in [0, N)$ whose *next* occupied index is $m$ form $J_m = [\max(m-L, m^-), m-1] \cap [0, N)$. For the $S(N-1)$ occupied indices $1 \le m \le N-1$, $|J_m| \le \min(L, m - m^-) \le L$. For any $n \in [0, N)$ whose next occupied index satisfies $m \ge N$, $m$ must be the *first* occupied index $\ge N$, and $n \ge m - L \ge N - L$, so $n \in [\max(0, N-L), N-1]$. There are at most $\min(N, L) \le L$ such shifts in total (even when $a(N) \ne 0$, and regardless of how many occupied indices exist at or above $N$).
  - *$L = 0$:* $(n, n+0] = \emptyset$ and $W_0(N) = 0 \le 0 \cdot (1 + S(N-1))$.
  - *$L > N$:* $W_L(N) \le N < L \le L(1 + S(N-1))$.
  - Thus $W_L(N) \le L(1 + S(N-1))$ holds unconditionally without looking ahead to $S(N+L)$ or $S(2N)$. **Verified.**
- **Lemma 1.3 (exact mean tail and far tail):**
  - Exchanging $\sum_{n=0}^{N-1}$ and $\sum_{j>L}$ gives $\sum_{n<N} \tau_L(n) = \sum_{j>L} b^{-j}(A(N-1+j) - A(j-1))$ since $j \ge L+1 \ge 1$.
  - Pairing each $m = n+j \ge L+1$ with $0 \le n \le \min(N-1, m-L-1)$ gives $\sum_{n=0}^{\min(N-1, m-L-1)} b^{n-m} \le \frac{b^{-\max(L, m-N)}}{b-1} = \frac{\min(1, b^{N+L-m})}{(b-1)b^L}$.
  - Abel summation gives $(1 - 1/b)\sum_{i\ge 0} b^{-i} A(X+i) = \sum_{m\ge 1} |a(m)|(1-1/b)\sum_{i\ge \max(0, m-X)} b^{-i} = \widehat A(X)$. Under $A(X) \le CX$, $\widehat A(X) \le C(X + 1/(b-1))$. **Verified.**
- **Theorem 1.4 & Window form:** Combining Lemma 1.2, Markov's inequality on $\{0 \le n < N : \tau_L(n) > \varepsilon\}$, Lemma 1.3, `discrepancy_deficit_le`, and `sharp_translation_isGreatest` yields Theorem 1.4 and the local window inequality on $[N_0, N_0+H)$. **Verified.**

### 1.2 Verification of Theorem 1.5 and Proposition 1.6
- **Theorem 1.5 (all-$N$ linear-mass rate):**
  - $\rho = \rho_N = (1 + S(N-1))/N \in [1/N, 1]$.
  - If $\rho = 1$, the right-hand side is $\ge 3 \ge 1 - D_N$.
  - If $\rho < 1$, set $\varepsilon = \rho/2$ and $L = \max\bigl(0, \lceil \log_b(4C/((b-1)\rho^2))\rceil\bigr)$.
    - *Case $L + 1/(b-1) \le N$:* $\widehat A(N+L) \le C(N + L + 1/(b-1)) \le 2CN$, so the Markov term in Theorem 1.4 is $\le \frac{4C}{(b-1)b^L \rho} \le \rho$, giving $1 - D_N \le (L+2)\rho$.
    - *Case $L + 1/(b-1) > N$:* Since $L, N \in \mathbb Z$ and $0 < 1/(b-1) \le 1$ for all $b \ge 2$ (specifically $1/(b-1) = 1$ for $b = 2$ and $1/(b-1) \le 1/2$ for $b \ge 3$), $L + 1/(b-1) > N$ is equivalent to $L \ge N$ for every $b \ge 2$. Since $\rho \ge 1/N$, $(L+2)\rho \ge (N+2)/N > 1 \ge 1 - D_N$.
    - In both cases $L + 2 \le 2\log_b(1/\rho) + \log_b^+(4C/(b-1)) + 3$. **Verified.**
- **Proposition 1.6 (sharpness of constant 2):** For $z = K/(b^q - 1)$ with $K \asymp q$ having alternating base-$b$ digits $1,0,1,\dots,0,1$ of length $w = \log_b q + O(1)$, the $w-1$ shifts $x_{q-j}$ ($1 \le j < w$) are bounded away from $0 \pmod 1$ by alternating digits, and the next $\log_b(1/\eta) - O(1)$ shifts ($w \le j \le w + \log_b(1/\eta) - O(1)$) stay in $[\eta, 1/2)$. Taking $\zeta = 1/q$ and $\eta = 3(2\log_b q)/q$ in Lemma 3.3 yields $(1 - D_q(z))q = 2\log_b q + O_b(\log\log q)$. **Verified.**

### 1.3 Verification of Theorem 1.7 and Finding B1-1
- **Theorem 1.7:** With $\mu_N = \max(1, \widehat A(2N)/N)$ and $L = \max\bigl(0, \lceil \log_b(2\mu_N/((b-1)\rho^2))\rceil\bigr)$, monotonicity of $X \mapsto \widehat A(X)$ gives $\widehat A(N+L) \le \widehat A(2N) \le \mu_N N$ whenever $L \le N$, while $L > N$ makes $(L+2)\rho > 1$. Under $A(X) \le X M(X)$ with $M \ge 1$ nondecreasing of polynomial growth, splitting $\widehat A(2N) = (1-1/b)\sum_{i\ge 0} b^{-i} A(2N+i)$ at $i \le 2N$ and $i > 2N$ gives $\mu_N \le (2 + \frac{1}{(b-1)N})M(4N) + o(1) \le 3M(4N)$ for large $N$. **Verified.**
- **[Minor B1-1] Sufficient condition (line 148) when $M(X) \equiv 1$:**
  Line 148 writes:
  $$S(N)\log\frac{N\,M(4N)}{1+S(N)} = o(N) \implies F \in K_b.$$
  If $S(N) = o(N)$ is not stated alongside this condition (or if $M(4N)$ inside the logarithm is not multiplied by $e$), then in the special case $M(X) \equiv 1$ and $S(N) = N$ (for example, $b = 3$ and $a(m) \in \{-1, 1\}$ for all $m \ge 1$ encoding a normal number, so $A(X) = X$), one has $S(N)\log\frac{N \cdot 1}{1 + N} = -1 + O(1/N) = o(N)$ even though $\rho_N = 1 \not\to 0$ and $F \notin K_b$ (because the $+3\rho$ term in Theorem 1.7 does not vanish). Writing $S(N)\log\frac{e\,N\,M(4N)}{1+S(N)} = o(N)$ (or stating $S(N) = o(N)$ explicitly) rules out this boundary case.

---

## 2. Detailed Audit of Track B2 (`coefficient-transfer.md` §2)

### 2.1 Verification of Composite-Radix Reindexing (Theorem 2.1) and Displaced Width Bound (Theorem 2.2)
- **Composite-radix factorization:** For any integer $b \ge 2$ (prime or composite) and $a(m) \ne 0$, $V(m) = \max\{v \ge 0 : b^v \mid a(m)\} \le \log_b|a(m)|$ is well-defined, $a(m) = b^{V(m)} U(m)$ with $b \nmid U(m)$, and the last base-$b$ digit of $|U(m)|$ is nonzero. Moreover, $|a(m)|$ has $V(m) + u(m)$ base-$b$ digits, so $\tilde t(m) = t(m) - u(m) = m - (V(m) + u(m))$.
- **Theorem 2.1 (displaced reindexing):** Since $|U(m)| \ge 1$, $|a(m)|b^{-m} = |U(m)|b^{-t(m)} \ge b^{-t(m)}$. Summability gives $\#\{m : t(m) = t\} \le b^t \sum_{m\ge 1} |a(m)|b^{-m} < \infty$ for every $t \in \mathbb Z$, and $\#\{m : t(m) \le 0\} \le \sum_{m\ge 1} |a(m)|b^{-m} < \infty$. Absolute convergence justifies $F = \sum_{t\in\mathbb Z} C(t)b^{-t}$, and at shift $n \ge 0$ the finitely many terms with $t \le n$ (including $t \le 0$) are integers $C(t)b^{n-t}$. **Verified.**
- **Theorem 2.2 (displaced width inequality):**
  - At shift $n \in [0, N)$, every source with $t(m) \le n$ satisfies $b^{m-n} \mid a(m)$ (if $m > n$) or $m \le n$, hence contributes an integer by Lemma 1.1.
  - If $n \notin \bigcup_{a(m)\ne 0} [\tilde t(m) - L, t(m) - 1]$, then every source with $t(m) > n$ satisfies $\tilde t(m) > n + L$.
  - Summing $\sum_{a(m)\ne 0,\, \tilde t(m) > n+L} |U(m)|b^{n-t(m)}$ over $0 \le n < N$ pairs each source with $0 \le n \le \min(N-1, \tilde t(m)-L-1)$, giving $\le \frac{\widehat P(N+L)}{(b-1)b^L}$.
  - The intervals with $1 \le t(m) \le N$ have total length $\sum_{1 \le t(m) \le N} (u(m) + L) = W_U(N) + L P(N)$, while all intervals with $t(m) > N$ meet $[0, N)$ in subintervals ending at $N-1$, so their union has size $\max_{t(m)>N} (N - \tilde t(m) + L)^+ \le L + \Lambda_N$. **Verified.**
- **[Minor B2-1] Wording in the proof of Theorem 2.2 (line 200):**
  Line 200 states: *"Markov's inequality is applied to $\sum_{t(m)>n}|U(m)|b^{n-t(m)}$, whose sum over $n<N$ is at most $\widehat P(N+L)/((b-1)b^L)$, as in Lemma 1.3."*
  To be completely precise, Markov's inequality is applied on the non-shadowed shifts $n < N$ (or equivalently to the truncated tail $\sum_{\tilde t(m) > n+L} |U(m)|b^{n-t(m)}$, which agrees with $\sum_{t(m)>n} |U(m)|b^{n-t(m)}$ when $n$ lies outside the shadow union). Summing $\sum_{t(m)>n} |U(m)|b^{n-t(m)}$ over *all* $n < N$ including shadowed shifts would not carry the $b^{-L-u(m)}$ factor.

### 2.2 Verification of Counterexamples (a), (b), (c) (§2.4)
- **(a) Logarithmic support, rational sum outside $K_b$:** For $0 = m_0 < m_1 < \dots$ even and $a(m_k) = \frac{b^{m_k - m_{k-1}} - 1}{b^2 - 1} = \sum_{m_{k-1} < 2i \le m_k} b^{m_k - 2i}$, the series telescopes to $\sum_{i\ge 1} b^{-2i} = \frac{1}{b^2-1}$. Its base-$b$ shift orbit alternates between $\frac{1}{b^2-1}$ and $\frac{b}{b^2-1}$, so at every even $N$, the interval $[\frac{1}{b^2-1}, \frac{b}{b^2-1}]$ of length $\frac{1}{b+1}$ contains all $N$ points, giving $D_N = \frac{b}{b+1}$ and $1 - D_N = \frac{1}{b+1} \not\to 0$. **Verified.**
- **(b) Logarithmic support, normal sum:** Grouping the base-$b$ digits of a $b$-normal number $\xi$ into blocks $(m_{k-1}, m_k]$ with $m_k = 2^k$ gives $F = \xi$, $S(X) = \lfloor \log_2 X \rfloor$, and $D_N(F) \to 0$. **Verified.**
- **(c) Polynomial coefficients, normal sum:** With $\ell_k = \max(1, \lfloor \gamma \log_b(m_{k-1}+1)\rfloor)$ and $m_k = m_{k-1} + \ell_k$, we have $S(X) \sim \frac{X}{\gamma \log_b X}$ and $F = \xi \notin K_b$, showing sharpness of the $o(N)$ condition in Theorem 1.7. **Verified.**
- **[Minor B2-2] Initial values of $k$ in line 235:**
  Line 235 writes $|a(m_k)| < b^{\ell_k} \le m_k^\gamma$. For the initial indices $k$ where $\lfloor \gamma \log_b(m_{k-1}+1)\rfloor = 0$ (e.g. $k=1$, where $m_0 = 0, \ell_1 = 1, m_1 = 1$), $\ell_k = 1$ gives $b^{\ell_k} = b > 1 = m_1^\gamma$. For all $k$ one has $b^{\ell_k} \le \max(b, m_k^\gamma) \le b m_k^\gamma$ (as correctly asserted in the script at line 426 and noted on line 238 for $\gamma = 1/2$), and $b^{\ell_k} \le m_k^\gamma$ holds for all $m_k \ge b^{1/\gamma}$.

---

## 3. Detailed Audit of Track B3 (`coefficient-transfer.md` §3)

### 3.1 Verification of Lemmas 3.1–3.3 and Theorem 3.4
- **Lemma 3.1 (exact source decomposition):** Every $n \in \mathbb N$ has a unique first successor $t \in \mathcal T$ ($t > n$), and $j = t - n$ satisfies $1 \le j \le t - t^- = g_t$. At shift $n = t - j$, all sources $\le t^- \le n$ are integers, so $x_n = \{b^{-j}(C(t) + A(t))\} = \{b^{-j} Y(t)\}$. When $(t, t+h] \cap \mathcal T = \emptyset$, $C(t+1) = \dots = C(t+h) = 0$, so $A(t) = b^{-h} A(t+h)$ holds identically. **Verified.**
- **Lemma 3.2 (one source):**
  1. When $|A(t)| \le 1/2$ and $b \nmid C(t)$, $C(t)$ is at distance $\ge 1$ from $b^j \mathbb Z$ for every $j \ge 1$, so $Y(t) = C(t) + A(t)$ is at distance $\ge 1/2$ from $b^j \mathbb Z$, giving $\|b^{-j} Y(t)\| \ge \frac{1}{2} b^{-j}$.
  2. When $j \ge u(t) + 1$, $b^{u-1} - 1/2 \le |Y(t)| \le b^u - 1/2 < \frac{1}{2} b^j$, so $\|b^{-j} Y(t)\| = b^{-j}|Y(t)|$.
  - This yields both the lower count $\min(g, u + \lambda'_\eta - 1) - 1 - Z_t(\eta)$ (under $b \nmid C(t)$) and the upper count $\min(g, u + \lceil \log_b(1/r)\rceil)$. **Verified.**
- **Lemma 3.3 (separated mass on the circle):** Checked for both positive excess $\mu(I) - |I|$ and negative excess $|I| - \mu(I)$, including wrapping intervals; also kernel-verified in `CoefficientTransfer.lean` (`one_sub_discrepancy_ge_of_bulk_and_far`). **Verified.**
- **Theorem 3.4 (isolated-source law):**
  - *Upper bound:* Follows from Theorem 2.2 applied to $C$ with $\varepsilon = \rho_N$ and $L = \lambda_N(1 + o(1))$.
  - *Lower bound:* Since $t \mapsto t^+$ is injective on $\mathcal T$ and at most one $t \le N$ has $t^+ > N$, left isolation of all but $o(S_{\rm eff}(N))$ sources at radius $h_N = \lfloor \lambda_N/2 \rfloor$ implies right isolation of all but $o(S_{\rm eff}(N))$ sources at radius $h_N$. For right-isolated $t$, $A(t) = b^{-h_N} A(t+h_N)$, and injectivity of $t \mapsto t + h_N$ together with Lemma 1.3 ($L=0$) and (I3) bounds $\#\{t : |A(t)| > 1/2\} \le \frac{2 b^{-h_N}}{b-1}\widehat A_C(2N) = O(S_{\rm eff}(N)\rho_N^{1/6}) = o(S_{\rm eff}(N))$. Since $t^- \ge 0$, every $t \in \mathcal T \cap [1, N]$ has $g_t = t - t^- \le t$, so all marked shifts $t - j$ ($1 \le j \le u(t) + \lambda'_\eta - 1 \le g_t$) satisfy $0 \le t - j < N$ and lie in disjoint gaps. Lemma 3.3 then gives the matching lower bound. **Verified.**
- **[Minor B3-1] Widths of sources excluded by right-isolation or $|A(t)| > 1/2$ in Theorem 3.4:**
  The fourth bullet of (I1) (line 308) assumes that the widths of the sources excluded in (I2) total $o(W + S_{\rm eff}\lambda_N)$. In the lower-bound proof (line 335), the good set $G$ also excludes the $o(S_{\rm eff}(N))$ sources that fail right-isolation at radius $h_N$ or have $|A(t)| > 1/2$. In all applications in the paper (Cases 1, 2, 3 and Track B4), $\max_{t\le N, t\in\text{(I2)}} u(t) = O(\lambda_N + W(N)/S_{\rm eff}(N))$, so any $o(S_{\rm eff}(N))$ subset of (I2)-sources automatically has width sum $o(W + S_{\rm eff}\lambda_N)$. In the abstract statement of Theorem 3.4, stating that any $o(S_{\rm eff}(N))$ subset of sources has total width $o(W + S_{\rm eff}\lambda_N)$ (or including right-isolation in (I2)) prevents a pathological case where a single source in (I2) with huge gap $g_{t_0} \ge u(t_0) + \lambda_N$ carries a positive fraction of $W(N)$ and fails right-isolation.
- **[Minor B3-2] Using $\widehat A_C(N + \lambda_N)$ instead of $\widehat A_C(2N)$ in (I3) (lines 310, 319, 330):**
  Line 319 states that if $|C(t)| \le B$, then (I1), (I3), and (I4) hold automatically. Note that for $t \le N$, the shifted index in line 330 satisfies $s = t + h_N \le N + \lfloor \lambda_N/2 \rfloor < N + \lambda_N$. Since $(N, N + 3\lambda_N]$ contains at most $3\lambda_N$ integers and $\lambda_N = \log_b(N/S_{\rm eff}(N)) \le \rho_N^{-o(1)} S_{\rm eff}(N)$ for every infinite support $\mathcal T$, the bound $\widehat A_C(N + \lambda_N) \le B(S_{\rm eff}(N) + \lambda_N + \frac{1}{b-1}) = O_B(S_{\rm eff}(N)\rho_N^{-1/3})$ holds *unconditionally* for every infinite $\mathcal T$ when $|C(t)| \le B$, whereas $\widehat A_C(2N)$ in (I3) would require $S_{\rm eff}(2N) = O(S_{\rm eff}(N)\rho_N^{-1/3})$. Replacing $\widehat A_C(2N)$ by $\widehat A_C(N + \lambda_N)$ in (I3) and line 332 makes the automatic satisfaction of (I3) for bounded coefficients completely unconditional.

### 3.2 Verification of Corollary 3.5, Case 3 (§3.3), and Theorem 3.6 (§3.4)
- **Corollary 3.5 (prime constant):** For $\sum_p b^{-p}$, $S_{\rm eff}(N) = \pi(N) \sim N/\log N$. For each $1 \le h \le H = \lceil 2\log_b \log N \rceil$, the Selberg upper-bound sieve (Halberstam–Richert, Ch. 3) gives $\#\{p \le N : p \pm h \text{ prime}\} \ll \mathfrak S(h) \frac{N}{(\log N)^2}$ uniformly in $h$, and $\sum_{1 \le h \le H} \mathfrak S(h) \ll H$ gives $O\bigl(\frac{N\log\log N}{(\log N)^2}\bigr) = o(\pi(N))$ non-isolated primes. Theorem 3.4 (Case 2, $c = \kappa = 1$) yields $1 - D_N(\sum_p b^{-p}; b) \sim \frac{\log\log N}{\log b \cdot \log N}$. **Verified.**
- **Case 3 (growing widths, §3.3):**
  - When $\gamma \le 1 - \sigma$, $u(t) \le \gamma \log_b N + O(1) \le \lambda_N + O(1) = \lambda'_\eta + O(\log\lambda_N)$, so $Z_t(\eta_N) = O(\log\lambda_N) = o(\lambda_N)$ unconditionally by Lemma 3.2(1).
  - When $\gamma > 1 - \sigma$:
    - For generic digits $\pm C(t_k) = n_k$ (the $k$-th positive integer not divisible by $b$), even though $A = A(t_k)$ in line 389 depends on $k$, every right-isolated source satisfies $|A(t_k)| \le 1/2$, so $\|b^{-j}(n_k + A(t_k))\| < \eta \implies \|b^{-j} n_k\| < \eta + \frac{1}{2}b^{-j}$. This confines $n_k \pmod{b^j}$ to at most $2\eta b^j + 1$ residue classes independent of $k$, so the equidistribution bound $(2K/b^j + 1)(\eta b^j + 3)$ and its sum over $\lambda' < j \le \log_b(2K)$ are completely valid.
    - Pure powers $C = b^w$ displace to unit sources (constant $c(1-\sigma)/\log b$), while $C = b^w - 1$ satisfies $Y(t) \equiv -(1 - A(t)) \pmod{b^w}$, acting as two unit sources at $t - w$ and $t$ (constant $2c(1-\sigma)/\log b$). **Verified.**
- **Theorem 3.6 (clustered sources / shadow law):** Positivity $1 \le C(t) \le B$ implies $Y(t) \in [1, \frac{Bb}{b-1}]$ for all $t \in \mathcal T$, eliminating any tail or isolation hypothesis.
- **[Minor B3-3] Boundary source $t_* > N$ in Theorem 3.6 (line 413):**
  For every $t \in \mathcal T \cap [1, N]$, $g_t = t - t^- \le t$, so all shifts $t - j$ ($1 \le j \le g_t$) lie inside $[0, N)$. However, the first source $t_* = \min(\mathcal T \cap (N, \infty))$ after $N$ can also shadow up to $\min(N - t_*^-, \lambda_N) \le \lambda_N$ shifts in $[0, N)$, contributing at most $O_B(\lambda_N/N)$ to $1 - D_N(F)$. When $S_{\rm eff}(N)\log(2+\lambda_N) \gg \lambda_N$ (which holds for all power-law, logarithmic, and missing-digit supports), $\lambda_N/N$ is absorbed into $O_B(\rho_N \log(2+\lambda_N))$; for ultra-sparse supports where $S_{\rm eff}(N) = o(\lambda_N/\log\lambda_N)$, one should either define $\rho_N = (1 + S_{\rm eff}(N))/N$ (as in §1) or write $+ O_B(\rho_N \log(2+\lambda_N) + \lambda_N/N)$.

---

## 4. Detailed Audit of Track B4 (`lambert-leading-constant.md`)

### 4.1 Arithmetic Setup and Upper Bound (§1–§2)
- **Coefficient factorization:** $c(n) = r_2(n)/4 = \sum_{d\mid n} \chi_4(d)$ is multiplicative, supported on $\mathfrak B$ (sums of two squares, $B(N) \sim K N/\sqrt{\log N}$). At $p = 2$, $\chi_4(2) = 0 \implies c(2^a) = 1$, so powers of $2$ in $n$ do not alter $V(n)$ or $U(n)$. Since $2^{V(n)} \le c(n) \le \tau(n) \le n$ with $V(n) \le n/2$ for all $n \ge 1$, every arrival satisfies $t(n) = n - V(n) \ge \lceil n/2 \rceil \ge 1$.
- **Upper bound via Theorem 2.2:**
  - $P(N) = \#\{n \in \mathfrak B : t(n) \le N\} = B(N) + O(\log N) \sim K N/\sqrt{\log N}$ since $t(n) \le N \implies n \le N + O(\log N)$.
  - $W_U(N) \le \sum_{n\le 2N} U(n) \ll N/\sqrt{\log N}$ via $u(n) \le U(n)$ (for odd $U(n) \ge 1$) and Shiu's bound (Phase 17 eq. (1)).
  - $\Lambda_N = O(\log N)$ and $\widehat P(N+L) \le B(N) + O(L + \log N)$ since $U(n)2^{-u(n)} < 1$ and each value $s = \tilde t(n)$ has $O(\log s)$ preimages.
  - Choosing $\rho = (1 + P(N))/N \sim K/\sqrt{\log N}$, $\varepsilon = \rho$, and $L = \lceil \log_2(1/\rho)\rceil + 1 = \frac{1}{2}\log_2\log N + O(1)$ makes the Markov term $\frac{\widehat P(N+L)}{2^L \rho N} \le \frac{1}{2} + o(1)$, because the $\sqrt{\log N}$ saving in $\widehat P(N+L) \sim K N/\sqrt{\log N}$ cancels $\varepsilon = \rho \sim K/\sqrt{\log N}$. This gives
    $$1 - D_N(L_{\chi_4}; 2) \le \rho \log_2\frac{1}{\rho} + O\Bigl(\frac{1}{\sqrt{\log N}}\Bigr) = \frac{K}{2\log 2}\frac{\log\log N}{\sqrt{\log N}}\Bigl(1 + O\Bigl(\frac{1}{\log\log N}\Bigr)\Bigr).$$
  **Verified.**

### 4.2 Audit of the Lower Bound and All Five Exceptional Sets (§3)
With $R = H_V = \lceil \log_2\log N \rceil$ and $H = R + H_V$:
- **Two-sided isolation of good arrivals (line 87):** Suppose $n \in \mathfrak B \cap (2H, N]$ satisfies (G1)–(G4), and $n' \in \mathfrak B$ ($n' \ne n$) satisfies $|t(n') - t(n)| \le R$. By (G4), we cannot have $V(n') > H_V$, so $0 \le V(n') \le H_V$. Since (G1) gives $0 \le V(n) \le H_V$, we have $|V(n') - V(n)| \le H_V$. Therefore, for *both* $n' > n$ and $n' < n$,
  $$0 < |n' - n| = |(t(n') - t(n)) + (V(n') - V(n))| \le R + H_V = H,$$
  which contradicts (G3). Thus $t = t(n)$ has singleton fiber $\{n\}$ (so $C(t) = U(n)$ is odd) and no other arrival in $[t - R, t + R]$. Moreover, $n > 2H \implies t = n - V(n) > 2H - H_V = 2R + H_V > R$, so $[t - R, t - 1] \subseteq [0, N)$. **Verified.**
- **(E1) Rankin bound on $V(n)$:** Since $c(n) = 2^{V(n)}U(n)$ with integer $U(n) \ge 1$ on $\mathfrak B$, $2^{V(n)} \le c(n) = r_2(n)/4$ holds everywhere without exception. By Gauss's circle bound $\sum_{n\le x} c(n) = \frac{\pi}{4}x + O(\sqrt x)$ and $2^{H_V} \ge \log x$,
  $$\#\{n \le x : V(n) > H_V\} \le 2^{-H_V}\sum_{n\le x} c(n) \le \Bigl(\frac{\pi}{4} + o(1)\Bigr)\frac{x}{\log x} = o\Bigl(\frac{x}{\sqrt{\log x}}\Bigr).$$
  **Verified.**
- **(E2) Markov bound on $U(n)$ via Shiu:** By Phase 17 eq. (1), $\sum_{n\le N} U(n) \ll N/\sqrt{\log N}$, so $\#\{n \le N : U(n) > \log\log N\} \ll \frac{N}{\sqrt{\log N}\log\log N} = o(N/\sqrt{\log N})$. **Verified.**
- **(E3) Pair sieve for $0 < |n' - n| \le H$:**
  - Fix $1 \le |h| \le H$. If $n, n+h \in \mathfrak B$ and $q \equiv 3 \pmod 4$ divides $n(n+h)$, then $v_q(n)$ and $v_q(n+h)$ must both be even, so $q^2 \mid n$ or $q^2 \mid (n+h)$.
  - For $q > z_0 = (\log x)^2$, the number of $n \le x$ with $q^2 \mid n$ or $q^2 \mid (n+h)$ is at most $\sum_{z_0 < q \le \sqrt{x+|h|}} 2(x/q^2 + 1) \le 2x/z_0 + 2\sqrt{x+|h|} = O(x/(\log x)^2)$.
  - The remaining $n \le x$ avoid $0$ and $-h \pmod q$ for all primes $q \equiv 3 \pmod 4$ with $z_0 < q \le z = \sqrt x$ and $q \nmid h$. Since $q > z_0 > |h|$ for large $x$, $0$ and $-h \pmod q$ are distinct residue classes, so $\omega(q) = 2$ and $|R_d| \le \omega(d)$.
  - Applying Halberstam–Richert Theorem 2.2 (which holds for all $z \le X$ in fixed dimension $\kappa = 1$ with $|R_d| \le \omega(d)$ via internal truncation at $z_1 = X^{c}$) and Mertens' theorem for $q \equiv 3 \pmod 4$ yields $\ll x \prod_{z_0 < q \le z,\, q\equiv 3\ (4),\, q\nmid h} (1 - 2/q) \ll x \frac{\log z_0}{\log z} \ll \frac{x\log\log x}{\log x}$.
  - Uniformity in $h$: at most $\log_2 x$ primes $q > z_0$ can divide $h$, so $\prod_{q\mid h, q>z_0} (1 - 2/q)^{-1} \le (1 - 2/z_0)^{-\log_2 x} = 1 + O(1/\log x) \to 1$.
  - Summing over $1 \le |h| \le H \asymp \log\log x$ gives $O\bigl(x(\log\log x)^2/\log x\bigr) = o(x/\sqrt{\log x})$. **Verified.**
- **(E4) Spoilage from distant $n'$ with $V(n') > H_V$:**
  - If $n \le N$ satisfies (G1) ($0 \le V(n) \le H_V$) and $|t(n') - t(n)| \le R$ for some $n' \in \mathfrak B$ with $V(n') > H_V$, then $t(n') \le t(n) + R \le N + R$.
  - Since $V(n') \le \log_2 n' \le n'/2$, we have $t(n') = n' - V(n') \ge n'/2$, so $n' \le 2(N + R)$.
  - For each such $n'$, $n = t(n) + V(n)$ must lie in $[t(n') - R, t(n') + R + H_V]$ (which holds for both $n' > n$ and $n' < n$), an interval of $2R + H_V + 1 = O(\log\log N)$ integers.
  - By (E1) at $x = 2(N + R)$, there are $O(N/\log N)$ such $n'$, spoiling at most $O(N\log\log N/\log N) = o(N/\sqrt{\log N})$ values of $n$. **Verified.**
- **(E5) Conditioned tail $A(t(n))$ via shift by $R$:**
  - For $n \in \mathfrak B \cap (2H, N]$ satisfying (G1)–(G4), there are no arrivals in $(t(n), t(n) + R]$, so $C(t(n)+1) = \dots = C(t(n)+R) = 0$ and Lemma 3.1 gives the *exact* equality $A(t(n)) = 2^{-R} A(t(n) + R)$.
  - Because $n$ is the unique element of $\mathfrak B$ in the fiber over $t(n)$, the map $n \mapsto s = t(n) + R$ is injective on the set of $n$ satisfying (G1)–(G4), and maps into $[1, N + R]$ (properly covering the boundary region $t(n) \in (N - R, N]$ where $t(n) + R \in (N, N + R]$).
  - By Phase 17 eq. (2) (or Lemma 1.3 with $L=0$ and Shiu's bound), $\sum_{s \le N+R} A(s) \ll (N+R)/\sqrt{\log(N+R)} \ll N/\sqrt{\log N}$, so
    $$\#\{n : \text{(G1)--(G4) and } A(t(n)) > 1/2\} \le \#\{s \le N + R : A(s) > 2^{R-1}\} \le 2^{1-R}\sum_{s\le N+R} A(s) \ll \frac{N}{(\log N)^{3/2}} = o\Bigl(\frac{N}{\sqrt{\log N}}\Bigr).$$
  **Verified.**
- **Marking and Lemma 3.3:** For $n \in G$, $Y(t) = U(n) + A(t) \in [1, \log\log N + 1/2]$, so for $j_0 = \lceil \log_2(2\log\log N + 1)\rceil \le j \le \lambda_\eta \le R$, $\|x_{t-j}\| = 2^{-j}Y(t) \ge 2^{-j} \ge \eta$. The intervals $[t - \lambda_\eta, t - j_0] \subseteq [0, N)$ are pairwise disjoint and mark $\Delta N = |G|(\lambda_\eta - j_0 + 1) = (1 - o(1))\rho N \log_2(1/\rho)$ shifts, matching the upper bound via Lemma 3.3. **Verified.**

### 4.3 Audit of Transfers and General Real Characters (§4)
- **Transfer to $\Theta_3(1/2)^2 = 1 + 4L_{\chi_4}$:** Multiplying by $4$ shifts the binary orbit by $2$ indices ($x_2, \dots, x_{N+1}$ vs $x_0, \dots, x_{N-1}$), changing any interval count by at most $2/N$. **Verified.**
- **Euler product for $C_\chi$ (lines 21 and 146):** For any real nonprincipal Dirichlet character $\chi \pmod q$, $c_\chi(n) = (1 * \chi)(n) \ge 0$ is supported on $n$ with even valuation at all primes with $\chi(p) = -1$ and unrestricted valuation at primes with $\chi(p) = 1$ or $p \mid q$ ($\chi(p) = 0$). Comparing local factors at $\chi(p) = 1$, $\chi(p) = -1$, and $p \mid q$ confirms the exact identity
  $$F(s)^2 = \zeta(s)L(s,\chi)\prod_{\chi(p)=-1}(1 - p^{-2s})^{-1}\prod_{p\mid q}(1 - p^{-s})^{-1}$$
  and the Wirsing / Selberg–Delange constant $C_\chi = \bigl(\frac{L(1,\chi)}{\pi}\prod_{\chi(p)=-1}(1 - p^{-2})^{-1}\prod_{p\mid q}(1 - p^{-1})^{-1}\bigr)^{1/2}$. Evaluated at $\chi_4$ ($q=4, p=2$) and $\chi_{-3}$ ($q=3, p=3$, with $p=2$ in the $\chi(p)=-1$ product), this gives $K = 0.76422365\ldots$ and $C_{\chi_{-3}} = 0.638909\ldots$. **Verified.**
- **[Minor B4-1] Minor exposition note on the general Phase 17 class (line 168):**
  Line 168 states that for the general Phase 17 class with harmonic density $\delta$, *"the Rankin bound uses $H_V = \delta \log_2\log x + 2\log_2\log\log x$ against $\sum c \ll x(\log x)^{2\delta - 1}$."* Since $2^{-H_V} x(\log x)^{2\delta - 1} = x(\log x)^{\delta - 1}(\log\log x)^{-2} = o(x/(\log x)^{1-\delta})$ only when $2\delta - 1 - \delta = \delta - 1 = -\kappa$, note that $c(n) \le \tau(n)$ does not always satisfy $\sum_{n\le x} c(n) \ll x(\log x)^{2\delta - 1}$ unless $c(p^e)$ is suitably controlled; however, on the support of $c$, $2^{V(n)} \le 2^{\omega_S(n) + \Omega_{\ge 2}(n)}$ has Euler product $\prod_{p\in S, p\le x}(1 + 2/p) \ll (\log x)^{2\delta}$, so Shiu's theorem applied directly to $2^{V(n)}\mathbf 1_{c(n)>0}$ always satisfies $\sum_{n\le x, c(n)>0} 2^{V(n)} \ll x(\log x)^{2\delta - 1}$, making the Rankin bound on $V(n)$ valid for the entire Phase 17 class.

---

## 5. Audit of `NormalityChecker/CoefficientTransfer.lean` & `scripts/phase20_transfer.py`

### 5.1 Verification of `scripts/phase20_transfer.py`
- Executed `python -B scripts/phase20_transfer.py`: completes in 14.9 s with exit code 0.
- All 520 exact `Fraction` inequalities in B1, 1,612 prefix checks for Theorem 1.5, Proposition 1.6 sharpness tables for $b=2,3$, 1,875 exact shift checks for composite-radix reindexing in B2, counterexamples (a)–(c), certified 40-bit discrepancy measurements and Lemma 3.3 lower bounds in B3, and the $N = 2^{18}$ calculations for $L_{\chi_4}$, $\Theta_3(1/2)^2$, and $L_{\chi_{-3}}$ in B4 match the prose and tables of both markdown notes.

### 5.2 Correspondence with `NormalityChecker/CoefficientTransfer.lean`
- **[Minor Lean-1] Synchronization between `coefficient-transfer.md` (§4, §6), `lambert-leading-constant.md` (§6), and `NormalityChecker/CoefficientTransfer.lean`:**
  - `coefficient-transfer.md` §6 (line 532) and `lambert-leading-constant.md` §6 (line 198) state that *"No statement in this note is kernel-verified yet"*, and `coefficient-transfer.md` §4 proposes signatures in namespace `NormalityChecker.Phase20Transfer`.
  - Meanwhile, `NormalityChecker/CoefficientTransfer.lean` (namespace `NormalityChecker.CoefficientTransfer`) already exists in the codebase and kernel-verifies:
    1. **Track B1:** `summable_abs_of_linear_mass`, `near_of_no_local_support`, `nearSupport_card_le`, `farCount_le_local_add_tail`, `markov_tail_card_le`, `sum_shiftedTail_le_of_linear_mass`, `finite_sparse_mass_transfer`, `finite_sparse_mass_translation`, `linear_mass_sparse_tendsto_one`, and `linear_mass_sparse_preserves_discrepancy`. (Note that `CoefficientTransfer.lean` uses the lookahead shadow bound $L \cdot S(N+L)$ and linear-mass tail $C(N+L+2)/b^L$, which suffices for $F \in K_b$, whereas Lemma 1.2's $L(1 + S(N-1))$, Lemma 1.3's $\widehat A(N+L)/((b-1)b^L)$, and the explicit rate Theorem 1.5 remain paper proofs.)
    2. **Track B2:** `radixVal`, `radixUnit`, `radixVal_pow_dvd`, `radixVal_mul_radixUnit`, `not_dvd_radixUnit`, and `displaced_term_eq` for arbitrary prime or composite radices $b \ge 2$.
    3. **Track B3/B4:** `one_sub_discrepancy_ge_of_bulk_and_far`, the two-sided circular concentration lower bound (Lemma 3.3).
  - Updating §4 and §6 of `coefficient-transfer.md` and §6 of `lambert-leading-constant.md` to cite the kernel-verified theorems in `NormalityChecker/CoefficientTransfer.lean` and distinguish them from the remaining paper-only statements (Theorems 1.5, 1.7, 2.2, 3.4, 3.6, and B4) will bring the notes into full alignment with the Lean library.
