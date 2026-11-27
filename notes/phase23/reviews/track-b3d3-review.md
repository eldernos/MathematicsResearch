# Independent Referee Report — Phase 23, Tracks B3 + D3

- **Audited files (read-only):**
  - `notes/phase23/binary-partition-and-carry-complexity.md` (551 lines)
  - `scripts/phase23_binary_partition.py` (1,226 lines)
- **Execution environment:** Local Windows host (`python -B scripts/phase23_binary_partition.py`: exited 0, 534,930 checks passed in 6.7 s; independent counterexample and 2-kernel verification run locally via `python -B`).
- **Disclaimer:** Cross-model review is not independent human peer review.

## Verdict: **ACCEPT AFTER REVISION**

The mathematical architecture of Phase 23 Tracks B3+D3 is strong and largely sound: the radix-power tower transfer and coset transport (§1), the elementary partition bounds of Theorem 2.1 (§2.1), the Thue–Morse reciprocal identity, 2-block digit code, simple normality of $Y_2, Y_3$, quantitative non-kernel bounds, and $m \ge 3$ dichotomy (§3), the multiplicative order formulas of Theorems 4.1 and 4.3 (§4), the quantitative Phase 19 sandwich (Lemma 5.3), the minimal-support inequalities and three-state transducer (Theorems 5.4–5.5), and the wall-order / maximal signed-width constructions inside $K_b$ (Lemma 5.6, Proposition 5.7) all withstand line-by-line verification.

However, the audit identified **1 Critical** error (unrestricted uniqueness in Theorem 5.2 is false), **4 Major** errors (a false open-problem claim for $\beta \bmod 2^L$, an invalid upper-bound proof in Corollary 2.2, an off-by-one constant in Proposition 2.3 for $b=2$, and a sign/clamping error in Consequence 4.4's tracking-ratio formula together with a contradictory automaton remark), and **10 Minor** issues. Every issue has a localized, concrete repair.

---

## 1. Summary of Findings

| ID | Severity | Location | Issue |
| --- | --- | --- | --- |
| **C1** | **Critical** | Note lines 318–326 (Thm 5.2) | Uniqueness of the gauge sequence $\delta$ is **false** without a growth condition ($\tilde\delta_m = \delta_m + c b^{m-1}$ gives the same $a'$ for any $c \in \mathbb{Z}$). |
| **M1** | **Major** | Note lines 37, 535 (Open Problem 4) | Automaticity of $\beta \bmod 2^L$ is **settled (true)** for every fixed $L \ge 1$, both classically and by an elementary Cartier-operator proof; only moduli with odd prime factors (e.g. $\beta \bmod 3$) remain distinct/open. |
| **M2** | **Major** | Note lines 136, 141 (Cor 2.2) | Upper-bound proof erroneously divides $C_m$ by $2$; the intermediate inequality $\log_m b_m(m^{k+1}) \le \frac{k(k+1)}{2} + \log_m(C_m/2)$ is **false** for $k=1$ and every $m \ge 3$. |
| **M3** | **Major** | Note lines 167–179 (Prop 2.3) | Upper-bound constant $+1$ fails the proof when $b=2$ (requires $+2$, which the script actually checks on line 391); also $L < N$ for applying Phase 22 Prop. D3.13(c) is unverified. |
| **M4** | **Major** | Note line 304 (Cons 4.4) | Bound $2^{\min(J-1, v_2(b+1)-1)} m / D_{J-1,m}$ is **false** for every even $b$ (gives $2^{-1}$ factor; fails at $b=2, m=2, J=2$ where $A_2/T_2 = 1/2 > 1/3$). Also self-contradiction in the automaton remark. |
| **m1** | **Minor** | Note lines 237, 241 (Thm 3.3(a),(c)) | $b \ge 3$ immediately gives $D_N(Y_b;b) \ge 2b^{-2}$ (stated $b^{-2}$ is valid but loose by $2$); $b=2$ should cite $(\frac18, \frac78) \subset [\frac18, \frac78)$; Thm 3.3(a) should explicitly note $0 < |\rho_{n+1}| < \frac12$. |
| **m2** | **Minor** | Note line 223 (Lem 3.2) | Missing explicit condition $N \ge 1$ for $\log_2 N$. |
| **m3** | **Minor** | Note line 292 (Lem 4.2) | $A_J/T_J < 2/D_{J-1}$ requires $J \ge 1$ (for $J=0, b\ge 8$, $b^2 \ge 64$ holds but $D_{-1}$ is undefined). |
| **m4** | **Minor** | Note line 350 (Lem 5.3) | Upper bound sets $\varepsilon = \sqrt{M_N/2} \in (0, \frac14)$, which requires $0 < M_N < \frac18$; edge cases $M_N = 0$ and $M_N \ge \frac18$ should be noted. |
| **m5** | **Minor** | Note line 378 (Thm 5.5(c)) | Briefly justify why $\{2^{t-1} w\} = \frac34$ occurs at most once (orbit $\frac34 \to \frac12 \to 0 \to 0\cdots$). |
| **m6** | **Minor** | Note line 390 (Lem 5.6) | For $e = 0$ the disjoint set is $\{0\}$, not $\{e-1, e\} = \{-1, 0\}$. |
| **m7** | **Minor** | Note lines 420–428 (Prop 5.9) | State $A \ge 0$ explicitly and verify how $b^{-\kappa}$ beats the $\kappa$-dependence of $n + L(n) + r$. |
| **m8** | **Minor** | Note line 81 (Prop 1.2) | Direct bound $\|X_B\| \le \frac12$ yields $\frac{1}{2N}$ instead of $\frac1N$ for the $n=0$ term. |
| **m9** | **Minor** | Script lines 6, 22, 327–331, 554, 966–998, 1070, 1143–1146, 1179–1180 | Theorem-number drift (`Lemma Q`, `Theorem 5.3/5.4` vs Note `Lemma 5.3`, `Theorem 5.4/5.5`); comment typo `2^{n/4}` vs code `2**(n//8)`; minor floating-point `math.log` checks vs "exact `int`/`Fraction` throughout"; tail majorant beyond $n=9000$ is analytical, not script-checked. |
| **m10** | **Minor** | Note lines 480–483 (§7 Lean blueprint) | `mahler_finite` omits explicit `(b : ℤ)` and `(maryPart 2 M : ℤ)` casts on the RHS. |

---

## 2. Detailed Findings & Concrete Repairs

### Critical Finding

#### [C1] Theorem 5.2 (Gauge identity): Uniqueness of $\delta$ is false without a growth hypothesis (`notes/phase23/binary-partition-and-carry-complexity.md`, lines 318–326)
- **Text:** "Every $a' \sim a$ has the form $a' = d + b\delta - S\delta$ for a unique integer sequence $\delta$, namely $\delta_m = \sum_{j \ge 0}(a'(m+j) - d_{m+j})b^{-1-j}$."
- **Defect:** The linear operator $\Delta \mapsto b\Delta - S\Delta$ on $\mathbb{Z}^{\mathbb{Z}_{\ge 1}}$ has a nontrivial kernel:
  $$\ker(b - S) = \bigl\{(c\,b^{m-1})_{m \ge 1} : c \in \mathbb{Z}\bigr\}.$$
  Indeed, for any $c \in \mathbb{Z} \setminus \{0\}$, setting $\tilde\delta_m = \delta_m + c b^{m-1}$ gives a distinct integer sequence satisfying
  $$d_m + b\tilde\delta_m - \tilde\delta_{m+1} = d_m + b\delta_m - \delta_{m+1} + c b^m - c b^m = a'(m) \quad \forall m \ge 1.$$
  Notice also that the proof on line 326 never even proves uniqueness; it only verifies existence for the displayed $\delta_m$.
- **Sharpness of the required hypothesis:**
  - The necessary and sufficient condition eliminating $\ker(b - S)$ is **$\delta_m b^{-m} \to 0$** (i.e. $\delta_m = o(b^m)$), since $c b^{m-1} b^{-m} = c/b \not\to 0$ for $c \ne 0$.
  - This condition holds **automatically** for the canonical $\delta_m$ of line 321 whenever $F_b(a')$ converges absolutely:
    $$|\delta_m| b^{-m} \le \frac{1}{b} \sum_{k \ge m} |a'(k) - d_k| b^{-k} \longrightarrow 0 \quad (m \to \infty).$$
  - By contrast, the stronger summability condition $\sum_{m \ge 1} |\delta_m| b^{-m} < \infty$ of Lemma 5.1 does *not* hold for every $a' \sim a$: e.g., $a'(k) = \lfloor b^k / k^2 \rfloor$ has absolutely convergent $F_b(a')$, yet $\delta_m \asymp b^{m-1}/m$, so $\sum_{m \ge 1} |\delta_m| b^{-m} = \infty$.
- **Downstream impact:** Theorem 5.5(a) imposes $|a'| \le B \le b-1$ and restricts $\delta_m \in \{-1, 0, 1\}$, which automatically satisfies $\delta_m = o(b^m)$, so Theorems 5.4–5.5 remain completely valid once Theorem 5.2 is amended.
- **Concrete repair:** Restate Theorem 5.2 as: *"Every $a' \sim a$ has the form $a' = d + b\delta - S\delta$ for a unique integer sequence $\delta$ satisfying $\delta_m = o(b^m)$, namely ..."* and add the two-line proof of uniqueness: if $b\eta_m - \eta_{m+1} = 0$ for all $m \ge 1$, then $\eta_m = b^{m-1} \eta_1$, so $\eta_m = o(b^m)$ forces $\eta_1 = 0$ and $\eta \equiv 0$, while the displayed $\delta_m$ satisfies $|\delta_m| b^{-m} \le b^{-1} \sum_{k \ge m} |a'(k) - d_k| b^{-k} \to 0$.

---

### Major Findings

#### [M1] Open Problem 4 & Working Hypothesis (iii): $\beta \bmod 2^L$ is *not* open — it is 2-automatic for every fixed $L \ge 1$ (`notes/phase23/binary-partition-and-carry-complexity.md`, lines 37, 535)
- **Text:**
  - Line 535 (Open Problem 4): *"Whether the digit sequence of $X_b$ is automatic, and whether $\beta \bmod b^L$ is 2-automatic for fixed $L$."*
  - Line 37 (Correction (iii)): *"$\beta$ is not a 2-regular sequence, because 2-regular sequences grow at most polynomially (Allouche–Shallit, Automatic Sequences, Thm. 16.3.1) and $\beta$ does not. So 2-regularity gives no automaton for $\beta \bmod b^L$, and none is claimed here."*
- **Defect:** For $b = 2$ (and any power of $2$), the sequence $(\beta(n) \bmod 2^L)_{n \ge 0}$ is **known to be 2-automatic** for every fixed $L \ge 1$. This connects classically to the Churchhouse (1969) / Rødseth (1970) congruence structure for binary and $m$-ary partitions modulo prime powers, and is stated explicitly in modern automatic-sequence literature (e.g., Sobolewski–Ulas for binary/colored binary partition functions modulo $2^p$). Moreover, there is a completely self-contained proof directly from $(1-z)F(z) = F(z^2)$:
  1. Put $F_k(z) = (1-z)^{-k} F(z) \in (\mathbb{Z}/2^L\mathbb{Z})[[z]]$. Then
     $$F_k(z) = \frac{F(z^2)}{(1-z)^{k+1}} = \frac{(1+z)^{k+1}}{(1-z^2)^{k+1}} F(z^2).$$
  2. Write $w = 1 - z^2$ and $(1+z)^s = u_s(w) + z\,v_s(w)$ with $u_s, v_s \in \mathbb{Z}[w]$. Since $(1+z)^2 = 2(1+z) - w$ and $w$ is even in $z$, both sequences satisfy the same linear recurrence
     $$u_s = 2u_{s-1} - w\,u_{s-2}\quad (u_0=1, u_1=1), \qquad v_s = 2v_{s-1} - w\,v_{s-2}\quad (v_0=0, v_1=1).$$
  3. By induction on $s \ge 1$, $2^{\max(0, s-1-2j)}$ divides $[w^j] u_s$ and $[w^j] v_s$ for all $j \ge 0$; in particular $[w^0] u_{L+1} = [w^0] v_{L+1} = 2^L \equiv 0 \pmod{2^L}$.
  4. Applying the Cartier operators $\Lambda_0, \Lambda_1$ (defined by $A(z) = \Lambda_0(A)(z^2) + z\Lambda_1(A)(z^2)$) to $F_k$ for $0 \le k \le L$ expresses $\Lambda_i(F_k)$ as a $\mathbb{Z}$-linear combination of $F_{k+1-j}$ with coefficients $[w^j] u_{k+1}$ or $[w^j] v_{k+1}$. For $k = L$, the $j = 0$ coefficient on $F_{L+1}$ is $2^L \equiv 0 \pmod{2^L}$.
  5. Therefore the finite $\mathbb{Z}/2^L\mathbb{Z}$-module $S_L = \operatorname{span}_{\mathbb{Z}/2^L\mathbb{Z}}\{F_0, F_1, \dots, F_L\}$ (cardinality $\le 2^{L(L+1)}$) contains $F \bmod 2^L$ and is closed under $\Lambda_0$ and $\Lambda_1$. Hence the 2-kernel of $(\beta(n) \bmod 2^L)_{n \ge 0}$ is finite, so $(\beta(n) \bmod 2^L)_{n \ge 0}$ is **2-automatic** for every $L \ge 1$.
  - Independent computational confirmation: verified directly on power series to degree $256$ that $S_L$ is closed under $\Lambda_0, \Lambda_1 \pmod{2^L}$ for $L = 1, 2, 3, 4$.
- **Distinction for odd moduli:** By contrast, for bases $b$ with an odd prime factor (e.g. $b = 3$, $\beta \bmod 3$), the proof above breaks down because $[w^0] u_s = 2^{s-1}$ is invertible mod $3$ (computationally, the 2-kernel mod 3 already has $1, 2, 4, 7, 13, 23$ distinct subsequences at depths $e = 1, \dots, 6$ on prefixes of length $64$). Note also that even though $\beta \bmod 2^L$ *is* 2-automatic for every fixed $L$, this does **not** settle automaticity of the base-2 digits of $X_2$, because the carry window $L(N) \asymp (\log N)^2$ grows with $N$.
- **Concrete repair:**
  1. Remove the $b = 2^k$ case from Open Problem 4 (line 535); restrict the coefficient-automaticity question to moduli not dividing a power of $2$ (e.g., *"whether $\beta \bmod m$ is 2-automatic for any $m$ not a power of $2$, such as $m = 3$"*), and note explicitly that $\beta \bmod 2^L$ *is* 2-automatic for every fixed $L$ (with the short Cartier-operator proof or citation to Churchhouse/Rødseth/Sobolewski–Ulas).
  2. Refine line 37 (iii) so it does not imply no automaton exists for $\beta \bmod 2^L$: $2$-regularity fails for $\beta$ over $\mathbb{Z}$ by Allouche–Shallit Thm. 16.3.1, whereas modulo fixed $2^L$ a finite automaton *does* exist, yet still does not yield an automaton for $X_2$ because the required carry depth $L(N) \asymp (\log N)^2$ is unbounded.

#### [M2] Corollary 2.2: Invalid upper-bound proof and false intermediate step (`notes/phase23/binary-partition-and-carry-complexity.md`, lines 136, 141)
- **Text:**
  - Line 136: $\log_m b_m(n) \le \frac{\ell^2}{2} + \frac{\ell}{2} + \log_m \frac{C_m}{2}$, where $C_m = \prod_{i \ge 0}(1 + m^{-i})$.
  - Line 141: *"Let $k = \lfloor \ell \rfloor \ge 1$ and use monotonicity, $b_m(m^k) \le b_m(n) \le b_m(m^{k+1})$. ... and $k(k+1)/2 \le \ell(\ell+1)/2$. The factor $i=0$ of $\prod(m^i+1)$ is $2$."*
- **Defect:** By Theorem 2.1,
  $$b_m(m^{k+1}) \le \prod_{i=0}^{k}(m^i + 1) = m^{k(k+1)/2} \prod_{i=0}^{k}(1 + m^{-i}) \le m^{k(k+1)/2} C_m.$$
  The factor $i=0$ is $m^0 + 1 = 2$, which is **already included** in $C_m = \prod_{i \ge 0}(1 + m^{-i}) = 2 \prod_{i \ge 1}(1 + m^{-i})$. Dividing $C_m$ by $2$ drops that factor in the wrong direction. In fact, the intermediate inequality $\log_m b_m(m^{k+1}) \le \frac{k(k+1)}{2} + \log_m(C_m/2)$ is **false** at $k = 1$ for every $m \ge 3$ (since $b_m(m^2) = m + 2$):
  - $m = 3$: $\log_3 5 = 1.46497 > 1.40764 = 1 + \log_3(C_3/2)$;
  - $m = 4$: $\log_4 6 = 1.29248 > 1.21963 = 1 + \log_4(C_4/2)$;
  - $m = 5$: $\log_5 7 = 1.20906 > 1.14384 = 1 + \log_5(C_5/2)$;
  - $m = 10$: $\log_{10} 12 = 1.07918 > 1.04620 = 1 + \log_{10}(C_{10}/2)$.
  (The final inequality of Corollary 2.2 still passed the script's checks up to $20{,}000$ only because monotonicity $b_m(n) \le b_m(m^{k+1})$ has large slack when $n < m^{k+1}$; the written proof does not establish the $C_m/2$ constant.)
- **Concrete repair:** Replace $\log_m \frac{C_m}{2}$ with $\log_m C_m$ in Corollary 2.2 (line 136), delete *"The factor $i=0$ of $\prod(m^i+1)$ is $2$"* from line 141, and update line 143 / script line 330 accordingly. (The lower bound of Corollary 2.2 is completely valid, including on $1 \le \ell < 2$ where $k(k-1)/2 = 0 \ge (\ell-1)(\ell-2)/2$.)

#### [M3] Proposition 2.3: Upper-bound constant off by $+1$ when $b = 2$ (`notes/phase23/binary-partition-and-carry-complexity.md`, lines 167–179)
- **Text:** *"There is $j_0(b)$ such that for $N \ge j_0(b)$ and $2 b^{-N/2} \le \tau/2$, $L_\tau(N) \le \log_b \beta(N) + \log_b(1/\tau) + \log_b(N+1) + 1$."*
- **Defect:** Phase 22 Proposition D3.13(c) gives $T(n, L) \le \frac{(N+1)\beta(N)}{(b-1)b^L} + 2 b^{-N/2}$ under $N \ge j_0(b)$ and $L < N$. With $2 b^{-N/2} \le \tau/2$, ensuring $T(N-1, L) < \tau$ via this bound requires
  $$\frac{(N+1)\beta(N)}{(b-1)b^L} < \frac{\tau}{2} \iff L > \log_b \beta(N) + \log_b(1/\tau) + \log_b(N+1) + \log_b\frac{2}{b-1}.$$
  Since $L$ must be an integer, the least such integer satisfies
  $$L \le \log_b \beta(N) + \log_b(1/\tau) + \log_b(N+1) + \log_b\frac{2}{b-1} + 1.$$
  For $b \ge 3$, $\log_b \frac{2}{b-1} \le 0$, so $+1$ works. For **$b = 2$**, $\log_2 \frac{2}{2-1} = 1$, so the proof yields **$+2$**, not $+1$. For instance, if $\log_2\beta(N) + \log_2(1/\tau) + \log_2(N+1) = M + 0.99$, then $L = M + 1$ satisfies the stated bound $M + 1.99$, yet $\frac{(N+1)\beta(N)}{(2-1)2^L} + 2\cdot 2^{-N/2}$ can reach $2^{-0.01}\tau + 0.5\tau \approx 1.493\tau > \tau$. Notably, `scripts/phase23_binary_partition.py` line 391 already checks `+ 2` rather than `+ 1`.
  Additionally, the proof omits checking the hypothesis $L < N$ required by Phase 22 Proposition D3.13(c). Because $2b^{-N/2} \le \tau/2$ implies $\log_b(1/\tau) \le N/2 - \log_b 4$, one has $L \le N/2 + \log_b\beta(N) + \log_b(N+1) + 2 < N$ for all $N \ge j_0'(b)$ sufficiently large, so enlarging $j_0(b)$ closes this gap cleanly.
- **Concrete repair:** Replace $+ 1$ by $+ 2$ (or $+ 1 + \log_b\frac{2}{b-1}$ for $b=2$ vs $b\ge 3$) on line 170, and add one sentence in line 179 verifying $L < N$ for $N \ge j_0(b)$ sufficiently large.

#### [M4] Consequence 4.4: Tracking-ratio bound false for even $b$, plus contradictory automaton remark (`notes/phase23/binary-partition-and-carry-complexity.md`, line 304)
- **Text:** *"For every $m \ge 2$, the tracked prefix of the product truncations is less than $2^{\min(J-1,\,v_2(b+1)-1)}\,m/D_{J-1,m}$ of one period. ... Because the window of §2 grows like $(\log N)^2$, any finite-automaton description of the digits of $X_b$ would need a growing number of states. Whether the digit sequence of $X_b$ is automatic is **open**."*
- **Defect 1 (false bound for even $b$):** Whenever $b$ is even, $b+1$ is odd so $v_2(b+1) = 0$ and $\min(J-1, v_2(b+1)-1) = -1$. Thus the stated factor is $2^{-1} = \frac12$, claiming $A_{J,m}/T_{J,m} < \frac{m}{2 D_{J-1,m}}$, which is half the true ratio $m^{J+1}/(m^J D_{J-1,m}) = m/D_{J-1,m}$.
  - **Explicit counterexample:** $b = 2, m = 2, J = 2$ (where $b^{2^{J+1}} = 2^8 = 256 \ge 64$): $A_2 = 6$, $T_2 = 12$, $D_1 = 3$, so the actual tracked fraction is $A_2/T_2 = 6/12 = 0.5000$, violating the stated bound $2^{-1} \cdot 2 / 3 = 1/3 \approx 0.3333$.
  - (Compare Phase 22 `partitions-carry-and-lemma-s.md` line 359, which correctly used $2^{\max(0,\,v_2(b+1)-1)}$ / separate cases for D3.9(c) vs (c′).)
- **Defect 2 (logical tension):** Asserting that *"any finite-automaton description of the digits of $X_b$ would need a growing number of states"* directly contradicts *"Whether the digit sequence of $X_b$ is automatic is **open**."* A growing carry window from the series coefficients $\beta(n)$ blocks a *bounded-window local transducer reading $\beta(n)$*, not an arbitrary finite automaton computing $d_n(X_b)$ (indeed, Proposition 5.7 constructs gauge-equivalent series for the 2-automatic number $\Lambda_2$ with unbounded coefficient widths).
- **Concrete repair:**
  1. Replace $2^{\min(J-1,\,v_2(b+1)-1)}$ by $2^{\max(0,\,\min(J-1,\,v_2(b+1)-1))}$ (and state $J \ge 1$, $b^{m^{J+1}} \ge 64$).
  2. Rephrase the automaton sentence to state that the growing carry window rules out obtaining a finite automaton *directly by a bounded-window local carry transducer on the coefficients $\beta(n)$*, leaving general automaticity of the digit sequence of $X_b$ open.

---

### Minor Findings

- **[m1] Theorem 3.3(a),(c) (lines 237, 241):**
  - In (a), line 241 writes $|\rho_{n+1}| \le \frac{1}{b-1} \le \frac12$; it is worth noting explicitly that $0 < |\rho_{n+1}| < \frac{1}{b-1} \le \frac12$ strictly (since $\frac1b > \frac{1}{b(b-1)}$ for $b \ge 3$ and $t_n$ is not eventually constant), so $\lfloor 1 + \rho_{n+1}\rfloor$ and $\lfloor b - 1 + \rho_{n+1}\rfloor$ never hit an integer boundary.
  - In (c), for $b \ge 3$, avoiding both $00$ and $(b-1)(b-1)$ confines all $\{b^n Y_b\}$ to $[b^{-2}, 1 - b^{-2})$, an interval of length $1 - 2b^{-2}$ containing all $N$ points, giving $D_N(Y_b; b) \ge 2b^{-2}$ directly (the stated $b^{-2}$ is valid, just a factor of $2$ weaker).
  - For $b = 2$ (line 241), note that since $Y_2$ is irrational, all points $\{2^n Y_2\}$ lie in $(\frac18, \frac78) \subset [\frac18, \frac78)$ (excluding the right endpoint $\frac78$), so the half-open interval $[\frac18, \frac78)$ of length $\frac34$ contains all $N$ points and yields $D_N(Y_2; 2) \ge 1 - \frac34 = \frac14$.
- **[m2] Lemma 3.2 (line 223):** Specify $N \ge 1$ so $\log_2 N$ is defined.
- **[m3] Lemma 4.2 (line 292):** Specify $J \ge 1$ for $A_J / T_J < 2^{J+1}/T_J = 2/D_{J-1}$ (for $J = 0$ and $b \ge 8$, $b^{2^1} \ge 64$ holds while $D_{-1}$ is undefined).
- **[m4] Lemma 5.3 proof (line 350):** In the upper bound, $\varepsilon = \sqrt{M_N/2}$ lies in $(0, \frac14)$ iff $0 < M_N < \frac18$. Add one phrase disposing of the trivial cases $M_N = 0$ (all orbit points are $0$, $D_N = 1$) and $M_N \ge \frac18$ ($2\sqrt{2 M_N} \ge 1 \ge 1 - D_N$).
- **[m5] Theorem 5.5(c) proof (line 378):** Add one phrase justifying why $\{2^{t-1} w\} = \frac34$ occurs for at most one index $t$: its forward orbit under $x \mapsto \{2x\}$ is $\frac34 \to \frac12 \to 0 \to 0 \cdots$, so $\frac34$ is never revisited.
- **[m6] Lemma 5.6 proof (line 390):** Write *"The sets $\{0\}$ and $\{e-1, e\}$ for $e = 2, 4, \dots, 2k-2$ are pairwise disjoint"* (for $e = 0$, $e-1 = -1$ is not a digit position, and the proof already showed $v_0 \ne 0$).
- **[m7] Proposition 5.9 (lines 420–428):** State $A \ge 0$ explicitly (so $L(n) \ge 1$) and include the one-line check $n + L(n) + r \le (n+2)(A + 4 + \kappa + r)$ showing that $b^{-\kappa}$ dominates the polynomial $\kappa$-dependence in the tail sum.
- **[m8] Proposition 1.2 proof (line 81):** $\|B^0 X_B\| \le \frac12$ holds directly without splitting $\|c_r c\| + \|c_r w\| \le \frac12 + \frac12 = 1$, giving the slightly sharper $\frac{1}{2N}$ instead of $\frac1N$ (matching the $b=2$ inequality).
- **[m9] `scripts/phase23_binary_partition.py` consistency & exact-vs-numerical separation:**
  - Lines 22, 966, 977–978, 988, 994, 996, 998, 1179–1180 still use older labels (`Lemma Q`, `Theorem 5.3`, `Theorem 5.4`) instead of the note's numbering (`Lemma 5.3`, `Theorem 5.4`, `Theorem 5.5`).
  - Line 1143 comment says `|a(n)| <= 2^{n/4}` while line 1146 checks `2 ** (n // 8)`.
  - Lines 327–331, 554, and 1070 use floating-point `math.log` (with tolerances `1e-9` / `1e-12`), slightly qualifying the header/note claim of *"exact `int`/`Fraction` arithmetic throughout"*. In particular, `Wraw` on line 1070 can be computed by exact integer base-$b$ length rather than `math.log`. Also note explicitly that `certified_floor`'s tail majorant $|a(n)| \le 2^{n/8}$ for $n > 9000$ rests on the analytical growth bounds for the series in §F, while lines 1144–1146 check it on a finite grid $2000 \le n \le 9000$.
- **[m10] Section 7 Lean 4 blueprint (lines 480–483):** In `mahler_finite`, add explicit `(b : ℤ)` and `(maryPart 2 M : ℤ)` casts on the RHS and in `b ^ (M - n)` so the equality is well-typed in `ℤ` without `ℕ` subtraction issues when formalized.

---

## 3. Verification Checklist (Independent Line-by-Line Audit)

### 3.1 Mathematical Statements & Proofs
- **§1.1 Functional equations:** Verified. $(1-z)F_m(z) = F_m(z^m)$, $c_r = D'_r / b^{2^r-1}$, and $b_m(mn+i) = \sum_{k \le n} b_m(k)$ are exact.
- **§1.2 Theorem 1.1 (Tower transfer):** Verified in full. $\mathbb{Z}[1/b]$-module action on $K_{b^k}$ and $M_b = M_{b^k}$, equivalence $X_{b^{2^r}} \in K_{b^k} \iff D'_r X_b \in K_{b^k}$, $X_b \in K_b \implies X_{b^{2^r}} \in M_b$ for $r \ge 1$, and $X_2 \in K_{2^k} \iff X_4 \in K_{2^k}$ (and $X_{2,m} \iff X_{2^m,m}$) are all airtight.
- **§1.3 Proposition 1.2 (Rate transfer):** Verified in full (with minor note [m8]); discrepancy transfer on line 86 follows cleanly from Lemma 5.3.
- **§1.4 Theorem 1.3 (Coset transport):** Verified in full. Check $\frac{r}{b(b+1)} - \frac{r(1-b)}{b^2-1} = \frac{r}{b} \in \mathbb{Z}[1/b] \subseteq M_b$ and $r(1-b) \equiv 2r \pmod{b+1}$; parity split (b), Phase 22 Theorem 9.2 application (c), and base-2 dichotomy (d) are exact.
- **§1.5 Arithmetic nature:** Verified; transcendence and irrationality exponent $2$ follow from Mahler (1929), Bugeaud (2011), and Möbius invariance.
- **§2.1 Theorem 2.1 & Corollary 2.2:** Theorem 2.1 is completely verified and very clean. Corollary 2.2 lower bound is verified; upper-bound proof has **Major finding [M2]**.
- **§2.2 Proposition 2.3 (Carry window):** Lower bound verified; upper bound has **Major finding [M3]** for $b = 2$.
- **§3.1 Theorem 3.1 (Reciprocal identity):** Verified in full. Truncated polynomial identity, $1/X_{b,m} = Y_{b,m}$, $Y_b = \frac{b}{b-1} - 2\xi_b$, and $X_2 = 1/(2 - 4\tau_{\mathrm{TM}})$ are exact.
- **§3.2 Lemma 3.2 & Theorem 3.3 (Digits of $Y_b$):** Verified in full (with minor polish [m1], [m2]). Recurrence $C(2N) = 2N - C(N)$, $C(2N+1) = C(2N) + 1$, 2-block frequencies $(\frac16, \frac13, \frac13, \frac16)$, digit code for all $b \ge 2$ (carefully checked for borrows/carries), simple normality of $Y_2$ and $Y_3$, nonnormality, $Y_b \notin K_b$, and $\limsup D_N(Y_b;b) \le 1 - \frac{4}{15b^2}$ via $\liminf \mu_N \ge \frac{2}{3b^2}$ and Lemma 5.3 are all sound.
- **§3.3 Theorem 3.4 & Corollary 3.5 ($m \ge 3$ dichotomy):** Verified in full. $S_m(N) \le 2 N^{\log_m 2} - 1$, $M_N(Y_{b,m}; b) \le \frac{S_m(N)+1}{N} \le 2 N^{\log_m 2 - 1}$, and $1 - D_N \le 4 N^{(\log_m 2 - 1)/2}$ via Lemma 5.3 are exact.
- **§4 Theorems 4.1, 4.3, Lemma 4.2, Consequence 4.4:** Theorems 4.1 (including power-of-two classification) and 4.3 (matching Phase 22 Prop. D3.9(c),(c′) with $K = J+1$) and Lemma 4.2 (with [m3]) are verified. Consequence 4.4 has **Major finding [M4]**.
- **§5.1 Lemma 5.1 & Theorem 5.2 (Gauge identity):** Lemma 5.1 is verified. Theorem 5.2 has **Critical finding [C1]** (uniqueness requires $\delta_m = o(b^m)$); existence, integrality, bounded converse, and $\delta_m \in \{-1,0,1\}$ for $|a'| \le B \le b-1$ are verified.
- **§5.2 Lemma 5.3, Theorems 5.4–5.5 (Three-state transducer):** Verified in full (with minor notes [m4], [m5]). Both sides of Lemma 5.3, both sides of Theorem 5.4, optimality and tail feasibility $|\delta_{N+1} + \{b^N w\}| \le \frac{B}{b-1}$ of the 3-state min-plus automaton in Theorem 5.5(a)–(b), and the factor-3 sandwich $\frac13 \chi_{N-2} \le \sigma_B \le \chi_N + 1$ in Theorem 5.5(c) are sound.
- **§5.3 Lemma 5.6, Proposition 5.7, Corollary 5.8 ($\Lambda_b$ signed widths):** Verified in full (with minor note [m6]). The carry proof of $w_b^\pm(R_k) = k$ for $b \ge 3$, integrality of $\Delta(m) = R_{k(m)}/(b-1)$, convergence, and both $W_\pm(N) \asymp N\sqrt{\log N}$ and $W_\pm(N) \asymp N^2$ constructions are sound.
- **§5.4 Proposition 5.9 (Carry-residue criterion):** Verified (with minor note [m7]).
- **§9 Open problems:** Open Problem 4 has **Major finding [M1]**; Problems 1–3, 5–6 are appropriately stated as open.

### 3.2 External Citations
- **Bugeaud (2011),** *On the rational approximation to the Thue–Morse–Mahler numbers*, Ann. Inst. Fourier 61 (2011), 2065–2076: **Verified** (exact title, volume, year, pages, and theorem: $\mu(\xi_b) = 2$ for every $b \ge 2$).
- **Keane (1968),** *Generalized Morse sequences*, Z. Wahrscheinlichkeitstheorie verw. Geb. 10 (1968): **Verified** (unique ergodicity and minimality of generalized Morse / Thue–Morse subshifts; an invariant probability measure on an infinite minimal subshift is automatically atomless).
- **Allouche–Shallit (2003),** *Automatic Sequences*, Thm. 16.3.1: **Verified** (polynomial growth $O(n^d)$ of $k$-regular sequences).
- **Mahler (1929, 1940), de Bruijn (1948), Thue (1912), Wall (1949), Reitwiesner (1960), Adamczewski–Bugeaud (2007), Nishioka (1996):** All standard and accurately invoked.

### 3.3 Script Execution & Evidence Separation
- Ran `python -B scripts/phase23_binary_partition.py` locally: exited `0`, `All 534930 checks passed in 6.7 s.`
- Every tabulated figure in §§2.1, 2.2, 3.2, 3.3, 4, 5.3, and 6 matches the script output to all reported digits.
- Exact finite certificates vs. finite measurements are clearly separated throughout the note (with the minor qualifications in [m9] regarding floating-point `math.log` checks and the analytical tail majorant above $n = 9000$).
- No finite measurement is used to claim an asymptotic conclusion, and the Lean 4 blueprint in §7 is explicitly marked uncompiled and not `Kernel-verified`.

---

## Post-Repair Verification

- **Audited files (read-only):**
  - `notes/phase23/binary-partition-and-carry-complexity.md` (630 lines)
  - `scripts/phase23_binary_partition.py` (1,434 lines)
- **Script execution:** Ran `python -B scripts/phase23_binary_partition.py` locally; exited `0` (`All 609971 checks passed in 5.9 s.`). Every quoted table entry, slack, window, order, tracking ratio, 2-kernel prefix count, and finite measurement in §§1–6 and §8 matches the script output to all reported digits.
- **Disclaimer:** Cross-model review is not independent human peer review.

### Verdict: **ACCEPT**

All findings from the initial audit (**C1**, **M1–M4**, **m1–m10**) are cleanly and rigorously closed, with no regressions introduced.

### Finding-by-Finding Closure

- **C1 (Critical — Closed):** Theorem 5.2(a)–(d) now states the exact necessary and sufficient uniqueness condition $\delta_m = o(b^m)$, proves $|\delta_m|b^{-m} \le b^{-1}\sum_{k \ge m}|a'(k)-d_k|b^{-k} \to 0$ automatically for the canonical carry, identifies $\ker(b-S) = \{(c\,b^{m-1})_{m \ge 1} : c \in \mathbb{Z}\}$ explicitly, proves the converse (c) from the finite telescoping identity of Lemma 5.1 (noting why $\sum |\delta_m|b^{-m} < \infty$ can fail via $a'(k) = \lfloor b^k/k^2 \rfloor$), and verifies (d) with $\delta_m \in \{-1,0,1\}$. Script §E2 checks both the growth bound and kernel shifts on 300 random instances.
- **M1 (Major — Closed):** Brand-new **Proposition 4.5** gives a self-contained, airtight proof that $(\beta(n) \bmod 2^L)_{n \ge 0}$ is 2-automatic with 2-kernel size $\le 2^{L(L+1)}$: writing $F_k = (1-z)^{-k} F$, $(1+z)^{k+1} = U_{k+1}(z^2) + z V_{k+1}(z^2)$ and expanding $U_s(1-w), V_s(1-w)$ yields exact Cartier identities $\Phi_0 F_k = \sum_j u_{k+1,j} F_{k+1-j}$ and $\Phi_1 F_k = \sum_j v_{k+1,j} F_{k+1-j}$ with $k+1-j \ge 1$ and $u_{s,0} = v_{s,0} = 2^{s-1}$, so $2^L F_{L+1} \equiv 0 \pmod{2^L}$ closes $\operatorname{span}_{\mathbb{Z}/2^L\mathbb{Z}}\{F_0,\dots,F_L\}$ under $\Phi_0, \Phi_1$. Script §C checks the exact identities in $\mathbb{Z}[[y]]$ through $y^{3000}$ for $k \le 7$. Correction (iii) and Open Problem 4 now cleanly separate fixed $2^L$ (settled) from moduli with odd prime factors (open) and from automaticity of $X_2$'s digits (open; unbounded window).
- **M2 (Major — Closed):** Corollary 2.2 replaces $\log_m(C_m/2)$ with $\log_m C_m$, removes the erroneous halving step from the proof, explicitly documents why $i=0$ is already in $C_m$, and verifies in exact `Fraction` arithmetic (script §A4) that $b_m(m^2) = m+2$ violates the old constant and satisfies the corrected constant for $3 \le m \le 10$.
- **M3 (Major — Closed):** Proposition 2.3 updates the upper bound to $\log_b \beta(N) + \log_b(1/\tau) + \log_b(N+1) + \log_b \frac{2}{b-1} + 1$ (at most $+1$ for $b \ge 3$, $+2$ for $b = 2$), defines $\Omega$ and $L^*$, and explicitly verifies $L^* < N$ for $N \ge j_0(b)$ before applying Phase 22 Prop. D3.13(c). Script §A5 verifies $L^*$, $L^* \le \Omega+1$, $L^* < N$, $2b^{-N/2} \le \tau/2$, and $L_{\mathrm{exact}} \le L^*$ by exact integer comparisons.
- **M4 (Major — Closed):** Consequence 4.4 states $m \ge 2$, $J \ge 1$, $b^{m^{J+1}} \ge 64$, and proves $0 \le e \le \max(0, \min(J-1, v_2(b+1)-1))$ with $A_{J,m}/T_{J,m} < 2^e m / D_{J-1,m}$ (checked in 24 exact m-ary cases plus the $b=m=J=2$ counterexample to the unclamped exponent). The automaton remark is now logically consistent, ruling out only bounded-window local carry transducers on $\beta(n)$ while leaving general automaticity of $d_n(X_b)$ open.
- **m1–m10 (Minor — All Closed):**
  - **m1:** Theorem 3.3(a) proves strict $0 < |\rho_{n+1}| < \frac12$; Theorem 3.3(c) tightens $b \ge 3$ to $D_N(Y_b;b) \ge 2b^{-2}$ and justifies $(\frac18,\frac78) \subseteq [\frac18,\frac78)$ for $b=2$ via irrationality of $Y_2$.
  - **m2:** Lemma 3.2 explicitly states $N \ge 1$.
  - **m3:** Lemma 4.2 separates $J \ge 0$ ($A_J < 2^{J+1}$) from $J \ge 1$ ($A_J/T_J < 2/D_{J-1}$).
  - **m4:** Lemma 5.3 disposes explicitly of $M_N = 0$ and $M_N \ge \frac18$ before setting $\varepsilon = \sqrt{M_N/2} \in (0,\frac14)$.
  - **m5:** Theorem 5.5(c) justifies uniqueness of $\{2^{t-1}w\} = \frac34$ via the forward orbit $\frac34 \to \frac12 \to 0 \to 0 \to \cdots$.
  - **m6:** Lemma 5.6 partitions positions into the $k$ pairwise disjoint sets $\{0\}$ and $\{e-1,e\}$ for $e = 2, 4, \dots, 2k-2$.
  - **m7:** Proposition 5.9 states $A \ge 0$ ($L(n) \ge 1$) and proves $n+L+r \le (n+2)(1+\kappa)(A+4+r)$, isolating $C(1+\kappa)^A b^{-\kappa} S_A \le 1$.
  - **m8:** Proposition 1.2 bounds $\|B^0 X_B\| \le \frac12$ directly, tightening $\frac1N$ to $\frac1{2N}$ in the theorem, proof, summary table, and discrepancy transfer.
  - **m9:** Script labels align throughout with `Lemma 5.3`, `Theorem 5.4`, `Theorem 5.5`; `2^{n/8}` comment typo fixed; `Wraw` uses exact integer `int_len`; floating-point tolerances (`Corollary 2.2`, power form of `Theorem 3.4`) and analytic tail majorants beyond finite grids are explicitly separated in both the script and note §§0, 8.
  - **m10:** Section 7 Lean 4 blueprint `mahler_finite` adds explicit `(b : ℤ)` and `(maryPart 2 M : ℤ)` casts across both sides.

