# Cross-Provider Referee Review — Phase 24 Track A

- **Reviewer:** Gemini 4 (auditing Claude Opus 5.5)
- **Files audited:**
  - `notes/phase24/dense-digit-mass-and-lambert.md` (547 lines)
  - `scripts/phase24_digit_mass.py` (991 lines)
- **Independent script execution:** `python -B scripts/phase24_digit_mass.py` exited with code `0` (`All 3095901 checks passed in 91.9 s`).
- **Scope notice:** This is an automated cross-model audit, **not** independent human peer review.
- **Verdict:** **ACCEPT AFTER REVISION**

---

## Executive Summary

Track A is mathematically strong, original in its unified framing, and exceptionally clean in both its elementary proofs and its outward-rounded finite certificates. Every flagship theorem—the exact multi-operand Kummer prefix identity and $O(\log N)$ carry-tail transfer (Theorems 2.1–2.2, Corollary 2.3), the frequency/discrepancy criteria and radix descent (Proposition 2.4), the elementary squarefull-convolution and independent-exponent mean-value framework with zero Tauberian input (Lemmas 3.1–3.2, Corollary 3.3), the base-2 and base-$2^j$ simple nonnormality and explicit $D^-$ bounds for $E(2^k)$ ($k \ge 3$, Theorem 4.1), the Senge–Straus non-power-of-2 barrier and $\tau_r$ multiplicative-dependence dichotomy (Theorems 5.1, 6.2), the working base-$b$ families (Theorem 5.2, including composite $b$), the signed transition-count/NAF transfer for $E_+(2^k)$ ($k \ge 4$, optimal for the method) and cubic-character $L_\pm(2^k)$ ($k \ge 4$ in base 2, Theorems 7.1–7.2, Proposition 8.1), and the exact carry-density boundary characterizations for $E(4)$ and $E^*(4)$ (Theorems 9.1, 10.1, Proposition 10.2)—withstood line-by-line verification.

The companion script `scripts/phase24_digit_mass.py` is rigorously outward-rounded throughout Section 4–5 (`SB = 192`, `Fraction`, explicit geometric/telescoping tail bounds), has **zero inward-rounding bugs**, and reproduces every certified interval, threshold, and finite measurement reported in the note.

There are **0 Critical**, **4 Major**, and **12 Minor** findings. None invalidates a flagship theorem or certified numerical constant, but all four Major items are genuine mathematical/numerical inaccuracies in supporting characterizations, remarks, or the Lean blueprint that must be repaired before promoting Track A to Paper XIV and `NormalityChecker/DigitMassTransfer.lean`.

---

## Section-by-Section Audit

### 1. General Digit-Mass Transfer & Truncation/Carry-Tail Theorem (§§0–2)

- **Lemma 1.1 (multi-operand Kummer):** Verified. Finiteness of the carry sequence follows since $a_i$ are finite and $c_j = \lfloor c_{j-1}/b \rfloor$ decreases to $0$ once columns exceed the highest operand digit. Telescoping $\sum_j r_j b^j = \sum_i a_i$ and summing column equations gives $\sum_i s_b(a_i) - s_b(\sum_i a_i) = (b-1)\sum_{j\ge 0} c_j \ge 0$, with $c_j \in \{0,1\}$ for $m=2$.
- **Lemma 1.2 ($s_b$, $w_b$, $w_\pm$):**
  - $s_b(a+c) \le s_b(a)+s_b(c)$, $s_b(ab^t) = s_b(a)$, and $s_b(ac) \le s_b(a)s_b(c)$ are completely rigorous.
  - The carry-run injection proof of $w_b(a+c) \le w_b(a)+w_b(c)$ (line 83) is airtight: for $i \in Z = \{i \notin S_a \cup S_c : \varepsilon_i = 1\}$, no carry leaves $i$ ($\varepsilon_{i+1} = 0$), so for $i_1 < i_2$ in $Z$ we have $i_1 + 1 < i_2$ and therefore the maximal carry-run start $j_2 < i_2$ satisfies $j_2 \ge i_1 + 1 > i_1 > j_1$, proving strict monotonicity and injectivity into $S_a \cap S_c$.
  - $w_b(ac) \le \min\{s_b(a)w_b(c), 2w_b(a)w_b(c)\}$ and the counterexample $w_b((b-1)^2) = 2 > 1 = w_b(b-1)^2$ for every $b \ge 3$ (since $(b-1)^2 = (b-2)b + 1$ with $1 \le b-2 \le b-1$) are verified, including $w_3(\tau(pq)) = w_3(4) = 2 > 1$.
  - Subadditivity, submultiplicativity, $w_\pm(-c) = w_\pm(c) = w_\pm(2c)$, $w_\pm(c) \le s_2(|c|) \le \lfloor\log_2|c|\rfloor + 1$, and the defining recursion for $w_\pm$ are verified.
- **Theorem 2.1 & Theorem 2.2 (exact prefix decomposition and carry tail):**
  - For arbitrary $N \ge 0$ (not just multiples of $k$) and $M = \lfloor N/k \rfloor$, $\lfloor b^N x \rfloor = A_N + \lfloor \tau_N \rfloor$ and $|\tau_N| \le b^{k-1}\Theta_M$ hold exactly, and the exponent bound $N - k(M+m) \le -1 - k(m-1) \le -m$ justifies both $\tau_N \le 4\sqrt{M+1}$ for $a = \tau$ (line 142) and `coeff_bound_tail` in `scripts/phase24_digit_mass.py` (lines 359–365).
  - The unsigned identities (lines 114 and 120) are exact because $\lfloor b^N x \rfloor = \lfloor x \rfloor b^N + \sum_{j=1}^N d_j b^{N-j}$ has disjoint base-$b$ digit supports for $\lfloor x \rfloor \ge 0$ and the fractional prefix.
  - Hand verification confirms the "+1" counterexample at $E(8)$, $N=35$, $M=11$: $\tau_{35} = 6/2 + 2/16 + 4/128 + \cdots \in [3,4)$, $\lfloor \tau_{35} \rfloor = 3$, and the shifted summands of $A_{35}$ plus $3$ occupy strictly distinct bit positions $\{32, 30, 27, 24, 23, 21, 19, 15, 13, 9, 8, 7, 3, 1, 0\}$, giving $\kappa(35) = 0$ and excess $s_2(3) = 2$.
  - **Defect found (Major M1):** Line 123 (and line 33) falsely asserts that the carry tail contributes at most $+1$ "exactly when $\lfloor \tau_N \rfloor \le 1$". In fact $s_b(b^r) = w_b(b^r) = 1$ for every $r \ge 0$.
- **Corollary 2.3 & counterexample for (H):**
  - Under (H), $\ell_b(\tau_N) = o(N)$ (and $O(\log N)$ under polynomial growth), and $(1/N)\sum_{n\le M} s_b(a(n)) \le (1/k)\cdot (1/M)\sum_{n\le M} s_b(a(n))$ yields both asymptotic bounds.
  - **Defect found (Major M2):** In the Example on line 144 ("Take $k \ge 2$ and $a(n) = b^{\lfloor kn/2 \rfloor}$"), the case $(b, k) = (2, 2)$ fails because $x = \sum_{n\ge 1} 2^{-n} = 1$, whose §0 expansion not ending in $1^\infty$ has $d_j = 0$ for all $j$, giving $f_1 = 0$, not $2/k = 1$.
- **Proposition 2.4 (frequency criteria & radix descent):**
  - All five items are proved cleanly and rigorously. Note that in item (5), $D_{kN}(x;b) \le \frac{b^k-1}{k(b-1)}D_N(x;b^k)$ even holds at $N = 0$ (under the Lean convention `radixDiscrepancy b x 0 = 1`), and simple normality descent from base $b^k$ to base $b$ is airtight.

### 2. Elementary Mean-Value Proof & Certified Constants for $E(2^k)$ ($k \ge 3$) (§§3–4, §13)

- **Lemma 3.1 (squarefull convolution):** Verified. Standard Wintner-type argument ($\sum_{d\le X}|h(d)| \le \sqrt{X}H + X\sum_{d>\sqrt{X}}|h(d)|/d = o(X)$) uses zero Tauberian input. Absolute convergence $\sum_{e\ge 1}|h(p^e)|p^{-e} < \infty$ implies $\sum_{e\ge 0}|G(p^e)|p^{-e} < \infty$, validating the local Euler factor $(1-p^{-1})\sum_{e\ge 0} G(p^e)p^{-e}$.
- **Lemma 3.2 (independent-exponent model):** Audited in full detail.
  - Under Lemma 3.1 for $G$, $G(p^e) = 1 + \sum_{k=2}^e h(p^k)$ for $p > p_0$, which forces $\varepsilon_y = \sum_{p>y}\sum_{e\ge 2} G(p^e)p^{-e} \le \sum_{p>y}\frac{1}{p(p-1)} + 2\sum_{p>y}\sum_{k\ge 2}|h(p^k)|p^{-k} \to 0$ with no unstated hypothesis.
  - The truncation of $e_p(m) \le E$ for $p \le y$, the indicator $\rho$ (which satisfies Lemma 3.1), the Borel–Cantelli + dominated-convergence identification with $\mathbb E\,F(U)$ (using $\mathbb E[\prod_p F(u_p(\varepsilon_p))] \le \prod_p \mathbb E[F(u_p(\varepsilon_p))] < \infty$ by Fatou), and both displayed bounds (lower via good event + independence, upper via submultiplicativity + independence + Fatou) are all completely rigorous, including when $u_p(e) = 0$ is allowed (as for $E_+$ at $p=2$).
- **Corollary 3.3:** $s_2(m) - s_2(m-1) = 1 - v_2(m)$, $|h(p^e)| \le \log_2(e+1)$ for all $e \ge 1$, the power-series identity $(1-x)\sum_{e\ge 0} s_2(e+1)x^e = \sum_{j\ge 0} x^{2^j-1}/(1+x^{2^j})$, and $H \in [1.903838, 1.903848] < 1.90385$ are all verified. Independent floating-point evaluation through $p \le 50000$ gave $H \approx 1.903844$.
- **Theorem 4.1 ($E(2^k)$ for $k \ge 3$):**
  - Certified intervals $C \in [1.4035953, 1.4035958] < 29/20$ and $C_{\rm true} \in [1.339103, 1.339116]$ are rigorously verified by auditing `EulerProduct`, `tail_bound`, `tail_A`, `inv_sq_above`, and `model_dp` (see Section 6 below). Independent evaluation through $p \le 50000$ gave $C \approx 1.4035933$ (plus tail $\approx 2.5\times 10^{-6} \approx 1.4035958$).
  - Transfer to base $2$ ($\limsup f_1 \le C_{\rm true}/k \le 0.44638$ at $k=3$), descent to every base $2^j$ ($j \ge 1$), explicit $D^-(E(2^k); 2) > 0$, $1 - D^-(E(2^k); 2) \le (C_{\rm true}\lceil\log_2 k\rceil + 1)/k \to 0$, and the base-$2^k$ popcount-run bound $D^-(E(2^k); 2^k) \ge (1 - C_{\rm true}/2 - (k+1)/2^k)/(k-1)$ for $k \ge 4$ (verified: the $k+1$ digits of popcount $\le 1$ form $k-1$ intervals $\{0,1,2\}, \{4\}, \dots, \{2^{k-1}\}$ of total length $(k+1)/2^k$) are all sound. Every table entry on lines 227–236 matches the script and rounds toward the weaker side.
- **Closed-form $C < 3/2$ via $15/\pi^2$ route (§13, line 543):**
  - The identity $L(p) - 1 = \frac{p-1}{(p+1)(p^2+1)} + \sum_{j\ge 2}\frac{p}{p^{2^j}+1}$ is exact, $L(p) \le 1 + p^{-2}$ holds for every $p \ge 3$ (e.g., $L(3)-1 \approx 0.08704 < 1/9$, and analytically $\frac{1}{p^2} - \frac{p-1}{(p+1)(p^2+1)} > \frac{2}{(p+1)(p^2+1)} \ge \frac{54}{40 p^3} > \frac{55}{54 p^3} \ge \sum_{j\ge 2}\frac{p}{p^{2^j}+1}$), $\prod_p(1+p^{-2}) = \zeta(2)/\zeta(4) = 15/\pi^2$, and $L(2) \approx 1.1921263 < 1.1922$.
  - **Defect found (Major M3):** The final chain $\frac{4}{5}\cdot 1.1922 \cdot 1.5199 < 1.4496$ on line 543 is **arithmetically false**: $\frac{4}{5}\cdot 1.1922 \cdot 1.5199 = 1.449619824 > 1.4496$ (even though the unrounded product $\frac{4}{5}L(2)\cdot\frac{15}{\pi^2} \approx 1.4494518 < 1.4496$).

### 3. Senge–Straus Barrier, $\tau_r$ Dichotomy & Base-$b$ Families (§§5–6)

- **Theorem 5.1 (base-$b$ barrier):** Verified. $\log 2 / \log b \notin \mathbb Q$ iff $b$ is not a power of $2$. Applying Senge–Straus (1973, explicitly labeled `External input`) to $s_2(2^r)=1$ gives $s_b(2^r) \to \infty$, hence $w_b(2^r) \ge s_b(2^r)/(b-1) \to \infty$. Combining with squarefree density $6/\pi^2$ (and $4/\pi^2$ for odd squarefree $n$ in $E_{\rm odd}$) and $\#\{n \le X : \omega(n) < r_0\} = o(X)$ proves $\frac{1}{X}\sum_{n\le X} w_b(\tau(n)) \to \infty$. (See Minor m5 regarding a helpful one-sentence note that direct base-4 mass also fails at $k=1$.)
- **Theorem 5.2 (working base-$b$ families):**
  - Unitary identity $\sum_{m\ge 1} \mu^2(m)(b-1)^{\omega(m)}/(b^{km}-1) = \sum_{n\ge 1} b^{\omega(n)}b^{-kn}$ and growth $b^{\omega(n)} \le n^{\log_2 b}$ (satisfying **(H)**) are exact; thresholds $k \ge 1$ ($b\ge 4$), $k \ge 2$ ($b=3$), $k \ge 3$ ($b=2$) are verified.
  - $\tau_b$-family identity $\sum_n \tau_b(n)b^{-kn} = \sum_m \tau_{b-1}(m)/(b^{km}-1)$ and Lemma 3.2 application are verified **including for composite $b \in \{4,6,8,9,10\}$**: because `b_free` strips only complete factors of $b$ (not individual prime factors), $\tau_b(n) = b^{\sum_p k_p} \prod_p u_b(e_p(n))$ holds identically, $s_b(\tau_b(n)) = s_b(\prod_p u_b(e_p(n)))$ is exact, $u_b(0)=u_b(1)=1$, and $s_b(\binom{e+b-1}{b-1}) \le (b-1)(e+b-1) \le b^2(e+1)$ validates `cd = (b*b, 1)` in the script.
  - The square-divisor identity $\sum_n \tau(n^2)3^{-kn} = \sum_m 2^{\omega(m)}/(3^{km}-1)$ (line 265) is exact since $\sum_{j=0}^e 2^{\omega(p^j)} = 2e+1 = \tau(p^{2e})$.
- **Theorems 6.1–6.3 ($E_{\rm odd}$, $\tau_r$ dichotomy, $E^*$):**
  - Multiplicative dependence $r^a = b^c \iff (r = t^v,\, b = t^u)$ for integer $t \ge 2$, the bound $s_b(m) \le (b-1)w_b(m) \le (b-1)w_t(m) \le (b-1)s_t(m)$, the Senge–Straus divergence for independent $(r,b)$, the refutation of the brief's $w_b$ refinement $r = db^m$, and all certified intervals/thresholds for $E_{\rm odd}$, $\tau_4$, $\tau_8$, $\tau_{16}$, and $E^*$ are completely verified.

### 4. Signed Transition-Count / NAF Transfer ($E_+(2^k)$ and Cubic $L_\pm(2^k)$) (§1, §§7–8)

- **Lemma 1.3 ($|T(A \pm 2^m) - T(A)| \le 2$):** Statement is true and exact (also verified in `trans(A)` using `~A = -A - 1` for $A < 0$, which complements every two's-complement bit and preserves transitions). See Minor m1 for a small gap in the proof text when $j = m$.
- **Theorem 7.1 (signed transfer):** Verified for every real $x$ (positive or negative): $\lfloor 2^N x \rfloor = 2^N \lfloor x \rfloor + \lfloor 2^N \{x\} \rfloor \equiv \sum_{j=1}^N d_j 2^{N-j} \pmod{2^N}$, so the low $N$ two's-complement bits are always $d_N, \dots, d_1$, giving $\mathrm{tr}_N(x) \le T(\lfloor 2^N x \rfloor) \le 2\sum_{n\le N/k} w_\pm(a(n)) + 2w_\pm(\lfloor \tau_N \rfloor)$ and $\limsup (f_{01}+f_{10}) \le 2W/k$.
- **Theorem 7.2 ($E_+(2^k)$, $k \ge 4$):**
  - Applying Lemma 3.2 with $F = w_\pm$, $p_0 = 2$, $u_2(1)=0$, $u_2(e) = \operatorname{odd}(|1-e|)$ ($e \ne 1$) is valid.
  - Certified $W_+ \in [0.908174, 0.908184]$, $W_+^{\rm maj} \in [0.936414, 0.936415]$, $D^-(E_+(16);2) \ge 0.04590$, and all table values match the script.
  - **Sharpness at $k = 4$:** Airtight. Since $a_+(n) = 0 \iff n \equiv 2 \pmod 4$, $a_+(n) \ne 0$ has density $3/4$, forcing $W_+ \ge 3/4$ and $2W_+/3 \ge 1/2$, so no signed-weight bound can reach $k = 3$.
- **Proposition 8.1 (cubic characters $L_\pm(2^k)$, $k \ge 4$ in base 2):**
  - Verified: $c_\pm(n)/A(n) \in \{0, \pm 1, \pm 2\}$, $G_\chi(p) = 1$ for all $p$, cube subgroups for $M \in \{7, 9, 13\}$ are exact ($\{1,6\}$, $\{1,8\}$, $\{1,5,8,12\}$), certified $W_\chi$ intervals match independent evaluation, and $D^-(L_\pm(16); 2) \ge 0.1215, 0.0977, 0.1053$ follow from Theorem 7.1.
  - The external-input remark that GF-31's weighted phase law multiplies the $c_-$ majorant by $2/3$ (reaching $k=3$) is valid (for all three moduli $7, 9, 13$, since $\frac{2}{3} \cdot 0.804516 < 3/4$).
  - **Defect found (Major M4):** The quartic-character remark on line 339 claims "the same proof" gives non-2-normality for $k > 4K_\Phi W$ with $W$ the analogous Euler product. At primes with $\chi(p) = -1$ (density $1/4$), $c(p) = 0$, so $G(p) = 0 \ne 1$: Lemma 3.1 does not apply directly to $G$, and the full Euler product $W$ actually equals $0$ (in fact, truncating the $\chi(p)=-1$ factors at $p \le P$ and applying Lemma 3.1 gives mean $0$ and $D^-(L_\Phi(2^k); 2) = 1$ for **every** $k \ge 1$).

### 5. $E(4)$ & $E^*(4)$ Boundary Analysis & Lean-Ready §13 Blueprint (§§9–13)

- **Theorem 9.1 ($E(4)$ boundary):** The exact identity $f_1(N; E(2^k), 2) = C_{\rm true}/k - \kappa_k(N)/N + o(1)$, the equivalence of simple normality of $E(4)$ with $\kappa_2(N)/N \to (C_{\rm true}-1)/2 \in [0.169551, 0.169558]$, and the obstruction for any $\mu \ge 1$ are verified. (See Minor m6 for a small precision fix on line 352.)
- **Theorem 10.1 & Proposition 10.2 ($E^*(4)$ boundary):**
  - All three parts of Theorem 10.1 are rigorously verified: $q(n) = 2n - \omega(n) \le 2n \le N$ for $n \le \lfloor N/2 \rfloor$, any collision partner satisfies $n' - n \le \frac{1}{2}\log_2 n'$ (giving $O(\log N)$ boundary losses across $M = \lfloor N/2 \rfloor$), and $\lfloor r/2 \rfloor \ge (r-1)/2$ for all $r \ge 1$ yields $\kappa^*(N) \ge \frac{1}{2}\#(\mathcal C \cap [1, N/2]) - O(\log N)$.
  - Proposition 10.2 (`Conditional`) correctly derives $\liminf f_1 \le \frac{1}{2} - \delta^+/4$ and $\limsup f_1 \le \frac{1}{2} - \delta^-/4$, $D^-(E^*(4); 2) \ge \delta^-/4$.
  - Evidence separation in §§10–11 is exemplary: `External input`, `Conditional`, `Open`, `Heuristic (not evidence)`, and `Finite measurements only` are cleanly distinguished. (Independent check of the Poisson stationary carry chain confirms the heuristic figures $0.36353$ for $E^*(4)$ and $0.27337$ for $E^*(8)$.)
- **§13 Lean-ready statements (L1–L15):**
  - Every mathematical statement L1–L15 was checked across all boundary cases (`0`, `1`, `N=0`, `m=0`, `k=0`, negative `A`, `c`), and **all 15 theorem statements are mathematically true as stated** (including L7's index alignment, L8/L9 at $k=0$, L11 at $N=0$, L12 at $m=0$, L14 for arbitrary integer $p \ge 2$, and L15).
  - See Major M3 (arithmetic slip on line 543) and Minor m8–m9 (two Lean 4 typing/coercion fixes in `nonzeroDigits` and L13).

### 6. Script Verification (`scripts/phase24_digit_mass.py`)

- Ran `python -B scripts/phase24_digit_mass.py`: exit code `0`, `3,095,901` checks passed in `91.9 s`. Every single numerical interval, threshold, and finite measurement in `notes/phase24/dense-digit-mass-and-lambert.md` matches the script output with outward/conservative rounding.
- Audited every arithmetic bound in Section 4 (`tail_bound`, `local_bounds`, `tail_A`, `inv_sq_above`, `EulerProduct`, `model_dp`, `two_tail`, cubic-character loop, `fmt_dn`, `fmt_up`, `cdiv`):
  - `tail_bound`: $((e+1)/(E+2))^d \le \exp(d(e-E-1)/(E+2)) \le (3/2)^{e-E-1}$ holds whenever $E \ge 3d$ (since $e^{1/3} = 1.3956\dots < 3/2$).
  - `cd = (c, d)` dominance $0 \le g(e) \le c(e+1)^d$ verified at every call site: `s_2(e+1) ≤ e+1`, `Gcum(e) ≤ 2e ≤ (e+1)^2` (since $\sum_{m=1}^{e+1} v_2(m) = e+1 - s_2(e+1) \le e$), `w_pm(e+1) ≤ e+1`, `s_2(C(e+r-1, r-1)) ≤ e+r ≤ r(e+1)`, `s_b(C(e+b-1, b-1)) ≤ (b-1)(e+b-1) ≤ b^2(e+1)`.
  - `inv_sq_above`: telescoping over $n \equiv \pm 1 \pmod 6$, $n > Y_2 = 4\cdot 10^6$, yields $< \frac{1}{6(Y_2-5)} + \frac{1}{6(Y_2-3)} < \frac{1}{3(Y_2-6)}$; prime reciprocals $q^{-2}$ rounded up via `cdiv(ONE, q*q)`.
  - `model_dp`: lower-bound probabilities rounded down (`//`) and multiplied by $1 - \text{inv\_sq\_above}(y)$; upper-bound frozen and live states rounded up (`cdiv`) and multiplied by `R_after(p)` / `R_after(last)`. Zero inward-rounding bugs.
  - `prefix_int` (Section 3 & 6): guard-digit certification (`lo == hi`) verified for both unsigned and signed series, with $\tau_3(n) \le \tau(n)^2 \le 4n$ and $3^{\omega(n)} \le \frac{3}{2} n \le 4n$ justifying `growth="linear"`.

---

## Classified Findings & Repair Recommendations

### Critical Findings

*None.*

### Major Findings

#### M1. False "exactly when" characterization of the $+1$ carry tail
- **Locations:** `notes/phase24/dense-digit-mass-and-lambert.md` line 123 (Theorem 2.2) and line 33 (summary table).
- **Issue:** Line 123 states: *"It contributes at most $+1$ to both sums **exactly when** $\lfloor \tau_N \rfloor \le 1$, for instance when $\tau_N < 2$."* This is false: $s_b(T) \le 1$ and $w_b(T) \le 1$ hold **if and only if** $T = 0$ or $T = b^r$ for some integer $r \ge 0$ (e.g., $\lfloor \tau_N \rfloor = 2$ in base $2$ has $s_2(2) = w_2(2) = 1$). Similarly, line 33 states *"The correct bound is $(b-1)(1+\log_b(1+\tau_N)) = O(\log N)$, and it equals $+1$ only when $\tau_N < 2$"*, which conflates the bound with the carry tail itself and repeats the false necessity claim.
- **Repair:**
  - On line 123, change *"exactly when $\lfloor \tau_N \rfloor \le 1$, for instance when $\tau_N < 2$"* to *"exactly when $\lfloor \tau_N \rfloor = 0$ or $\lfloor \tau_N \rfloor = b^r$ for some $r \ge 0$, and in particular whenever $\tau_N < 2$"*.
  - On line 33, revise to *"The correct bound is $(b-1)\ell_b(\tau_N) \le (b-1)(1+\log_b(1+\tau_N)) = O(\log N)$; the carry tail itself is guaranteed to be at most $+1$ when $\tau_N < 2$ (Theorem 2.2)."*

#### M2. Counterexample to dropping **(H)** fails at $(b, k) = (2, 2)$
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 144 (*Example (H cannot be dropped)*).
- **Issue:** The example begins *"Take $k \ge 2$ and $a(n) = b^{\lfloor kn/2 \rfloor}$"* and concludes $x = \sum_n b^{-\lceil kn/2 \rceil}$ has digit $1$ at positions $\lceil kn/2 \rceil$ and $f_1 \to 2/k$. When $b = 2$ and $k = 2$, $x = \sum_{n\ge 1} 2^{-n} = 1$, whose base-$2$ expansion under the §0 convention (not ending in $(b-1)^\infty = 1^\infty$) has $d_j = 0$ for all $j \ge 1$, giving $f_1 = 0$, not $2/k = 1$.
- **Repair:** Change *"Take $k \ge 2$"* to *"Take $k \ge 3$ (or $k = 2$ with $b \ge 3$)"* and note in one clause that the expansion does not end in $(b-1)^\infty$ (missing infinitely many positions for $k \ge 3$, and having all digits $1 < b-1$ for $k = 2, b \ge 3$).

#### M3. False rounded inequality in the §13 closed-form $C < 3/2$ route for Lean 4
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 543.
- **Issue:** Line 543 writes:
  $$C \le \frac{4}{5} L(2)\prod_p (1 + p^{-2}) = \frac{4}{5} L(2)\cdot \frac{15}{\pi^2} \le \frac{4}{5}\cdot 1.1922 \cdot 1.5199 < 1.4496.$$
  In fact $\frac{4}{5}\cdot 1.1922 \cdot 1.5199 = 1.449619824 > 1.4496$, so the last inequality is **false** (even though the unrounded quantity is $\approx 1.4494518 < 1.4496$).
- **Repair:** Replace the final chain with either $\frac{4}{5}\cdot 1.1922 \cdot 1.5199 < 1.4497 < 3/2$ or $\frac{4}{5}\cdot 1.19213 \cdot 1.51982 < 1.4495 < 3/2$ (both intermediate bounds are valid since $L(2) = 1.19212634\dots$ and $15/\pi^2 = 1.51981775\dots$).

#### M4. Quartic-character remark in §8 misapplies Lemma 3.1 when $\chi(p) = -1$ (and misses a stronger $D^- = 1$ conclusion)
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 339.
- **Issue:** The remark states that for a quartic character $\chi$, *"The same proof then gives non-2-normality in base 2 for all $k > 4K_\Phi W$, with $W$ the analogous Euler product."* However, at primes with $\chi(p) = -1$ (density $1/4$), $c(p) = 1 + \chi(p) = 0$, so the support majorant has $G(p) = 0 \ne 1$. Thus Lemma 3.1 does not apply directly to $G$ (since $\sum |h(p)|/p = \infty$), and the full Euler product $W$ vanishes ($\prod_{\chi(p)=-1}(1+1/p)^{-1} = 0$).
- **Repair:** Either (a) explicitly state that one drops the $\chi(p) = -1$ factor (setting $G_1(p^e) = 1$ at $\chi(p) = -1$) to apply Lemma 3.1 directly with a positive constant $W_1$, or (b) better, note that keeping $G_P(p^e) = \mathbf 1[2 \mid e]$ for $p \le P$ with $\chi(p) = -1$ and setting $G_P(p^e) = 1$ for $p > P$ lets Lemma 3.1 apply elementarily for every $P$; letting $P \to \infty$ gives $\lim \frac{1}{X}\sum_{n\le X} w_\pm(\Phi(c(n))) = 0$, proving $\lim(f_{01}+f_{10}) = 0$ and $D^-(L_\Phi(2^k); 2) = 1$ for **every** $k \ge 1$ with zero Tauberian input!

---

### Minor Findings

#### m1. Proof of Lemma 1.3 omits the $j = m$ case
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 93.
- **Issue:** When $j = m$ (i.e. $A_m = 0$), bits $m, \dots, j-1$ are empty, and $(j-1, j)$ coincides with $(m-1, m)$ and can change its transition status (e.g. $(0,0) \to (0,1)$), contradicting *"the pair $(j-1,j)$ is a transition both before and after"*. The conclusion $|T(A\pm 2^m) - T(A)| \le 2$ still holds.
- **Repair:** Separate $j = m$ (only bit $m$ flips, affecting at most $(m-1, m)$ and $(m, m+1)$) from $j > m$ (where $(j-1, j)$ flips $(1,0) \to (0,1)$ and stays a transition). Also note that $(m-1, m)$ is absent when $m = 0$.

#### m2. Domain of exponents $m_i$ in the definition of $w_\pm$
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 50.
- **Issue:** $w_\pm(c)$ is defined via $c = \sum \varepsilon_i 2^{m_i}$ without stating $m_i \in \mathbb Z_{\ge 0}$.
- **Repair:** Add $m_i \in \mathbb Z_{\ge 0}$.

#### m3. $\log |a(n)| = o(n)$ when $a(n) = 0$
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 135 (Corollary 2.3).
- **Issue:** Sequences with zeros (such as $a_+$ and $c_\pm$ in §§7–8) have $\log |a(n)| = -\infty$ at zeros.
- **Repair:** Write $\log(1 + |a(n)|) = o(n)$.

#### m4. Domain of $F$ in Lemma 3.2 vs $s_b$
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 176.
- **Issue:** Lemma 3.2 states $F : \mathbb Z \to [0, \infty)$ with example $s_b$, whereas §0 defines $s_b$ only on $\mathbb Z_{\ge 0}$.
- **Repair:** Either note $s_b(c) := s_b(|c|)$ on $\mathbb Z$, or state $F : \mathbb Z_{\ge 0} \to [0,\infty)$ (or $\mathbb Z \to [0,\infty)$) matching the codomain of $u_p$.

#### m5. Clarify direct base-4 mass failure in Theorem 5.1
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 244.
- **Issue:** Theorem 5.1 states $k_0(4) = 2$ is the method's threshold for $E(4^k)$ in base $4$, proved via base-$2$ transfer + radix descent. A reader may wonder whether direct base-$4$ transfer ($s_4$ or $w_4$) reaches $E(4)$ ($k=1$).
- **Repair:** Add a brief parenthetical remark that direct base-$4$ mass also fails at $k = 1$: $w_4(\tau(n)) \ge 1 > 3/4$, and even on squarefree $n$ the average of $s_4(2^{\omega(n)}) \in \{1, 2\}$ is $3/2$ (with full mean $\approx 2.01 > 3/2$).

#### m6. Slightly imprecise phrasing in Theorem 9.1(2)
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 352.
- **Issue:** *"A proof must exhibit carry density at least $0.1695$"* only applies to proving $\limsup f_1 < 1/2$ (simple nonnormality could logically also arise if $\kappa_2(N)/N$ stays below $(C_{\rm true}-1)/2$ or fails to converge).
- **Repair:** Write *"A proof of $\limsup f_1 < \frac{1}{2}$ must exhibit $\liminf \kappa_2(N)/N > (C_{\rm true}-1)/2 > 0.169551$."*

#### m7. Two-variable equation for a three-fold collision in §10
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 375.
- **Issue:** *"carries need three-fold collisions $\omega(n') - \omega(n) = n' - n$"* writes a two-index equation for a three-fold collision.
- **Repair:** Write *"three-fold collisions $n_1 - \omega(n_1) = n_2 - \omega(n_2) = n_3 - \omega(n_3)$ (absent incoming carries)"*.

#### m8. Lean 4 type error in `nonzeroDigits` (§13 blueprint)
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 426.
- **Issue:** `((Nat.digits b n).filter (· ≠ 0)).length` passes a `Prop` predicate `(· ≠ 0)` to `List.filter`, which expects `α → Bool`.
- **Repair:** Use `((Nat.digits b n).filter (· != 0)).length` or `(Nat.digits b n).countP (· != 0)`.

#### m9. Lean 4 coercion and unused hypothesis in L13 (§13 blueprint)
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` lines 522–526.
- **Issue:** `(ArithmeticFunction.moebius : ArithmeticFunction ℝ)` may require an explicit ring-hom cast (e.g., `(ArithmeticFunction.moebius : ArithmeticFunction ℤ).map Int.cast` / `Int.castRingHom ℝ`) depending on the Mathlib version's `Coe` instances. Also, `hG : G.IsMultiplicative` is not needed for the mean-value identity $\frac{1}{X}\sum_{n\le X} G(n) \to \sum' (G*\mu)(n)/n$ (only for the Euler product).
- **Repair:** Note the `ℤ → ℝ` cast for `moebius`, and either drop `hG` from L13 or keep it explicitly only if bundling the Euler-product form.

#### m10. Informal phrasing in the §8 odd-$h \ge 5$ remark
- **Location:** `notes/phase24/dense-digit-mass-and-lambert.md` line 339.
- **Issue:** *"The majorant then grows like $2^{\#\{p\parallel n\}}$ over a positive proportion of primes"* is slightly imprecise because $1 + \zeta_h^j \in \mathbb Z[\zeta_h]$ is not an integer and does not directly carry a $w_\pm$ value.
- **Repair:** Clarify that expanding products of $(1 + \zeta_h^j)$ in an integral basis and bounding signed weights naively yields a multiplicative majorant growing at least like $2^{\#\{p\parallel n : \chi(p) \ne 0, 1\}}$, whose mean diverges.

#### m11. Tautological check in `scripts/phase24_digit_mass.py` Section 3
- **Location:** `scripts/phase24_digit_mass.py` lines 449–450.
- **Issue:** `dsum = sb(PN, 2) - sb(intpart, 2)` followed by `check(dsum + sb(intpart, 2) == sb(PN, 2), "digit sum of prefix")` is a tautology (`(a - b) + b == a`).
- **Repair:** Compute `dsum = sb(PN & ((1 << N) - 1), 2)` so the assertion genuinely checks the digit-sum split between the integer and fractional parts.

#### m12. Dead code & explicit domain guards in `scripts/phase24_digit_mass.py` Section 4
- **Location:** `scripts/phase24_digit_mass.py` lines 592, 608, 720, 809–810.
- **Issue:**
  - `sumsq_tail=None` (line 608) and `absdiff = lambda e: ...` (line 720) are unused.
  - Line 592 checks `Ap < Y and Am < Y` instead of directly asserting `Ap * S2 < 1 and Am * S2 < 1`, and lines 809–810 (cubic characters) omit the domain assertion `A * S2 < 1 and (1 + Am) * S2 < 1` (all hold by $\ge 4$ orders of magnitude at the script's $Y$, so no result is affected).
- **Repair:** Remove the two unused symbols and add explicit assertions `check(Ap * S2 < 1 and Am * S2 < 1)` in `EulerProduct.__init__` and `check(A * S2 < 1 and (1 + Am) * S2 < 1)` in the cubic-character block.

---

## Final Verdict

**ACCEPT AFTER REVISION.**

All core theorems, proof architectures, barrier arguments, carry-boundary equivalences, and outward-rounded finite certificates in Track A are mathematically sound and computationally verified (`3,095,901` checks passed, zero inward-rounding bugs). Fixing Major items **M1–M4** (and optionally Minor items **m1–m12**) will make `notes/phase24/dense-digit-mass-and-lambert.md` and `scripts/phase24_digit_mass.py` ready to serve as the backbone for Candidate Paper XIV and `NormalityChecker/DigitMassTransfer.lean`.

*Note: This cross-model review (Gemini 4 auditing Claude Opus 5.5) is **not** independent human peer review.*

---

## Post-Repair Verification

- **Reviewer:** Gemini 4 (post-repair audit of Track A)
- **Files re-audited:**
  - `notes/phase24/dense-digit-mass-and-lambert.md` (552 lines)
  - `scripts/phase24_digit_mass.py` (991 lines)
- **Independent script execution:** `python -B scripts/phase24_digit_mass.py` exited with code `0` (`All 3095904 checks passed in 91.8 s`; +3 checks from the new cubic-character tail-domain assertions).
- **Scope notice:** This cross-model review is **not** independent human peer review.
- **Post-repair verdict:** **ACCEPT**

### Major Findings (M1–M4)

| ID | Status | Verification |
| --- | --- | --- |
| **M1** | **Closed** | Line 123 (Theorem 2.2) now states the exact characterization: the carry tail contributes at most $+1$ to both sums iff $\lfloor\tau_N\rfloor \in \{0\} \cup \{b^r : r \ge 0\}$, noting that $\tau_N < 2$ is sufficient (not necessary, e.g. $s_b(b)=w_b(b)=1$). Line 33 (status table) accurately separates the bound $(b-1)\ell_b(\tau_N) \le (b-1)(1+\log_b(1+\tau_N)) = O(\log N)$ from the sufficient condition $\tau_N < 2$. |
| **M2** | **Closed** | Line 144 (*Example (H cannot be dropped)*) restricts to $k \ge 3$ or ($k = 2, b \ge 3$), verifies that the expansion does not end in $(b-1)^\infty$ in both regimes, and explicitly excludes $(b, k) = (2, 2)$ with the exact explanation ($x = \sum_n 2^{-n} = 1$, fractional digits all $0$). |
| **M3** | **Closed** | Line 548 defines $L(p) = \sum_{j \ge 0} p/(p^{2^j}+1)$ before use and replaces the false rounded inequality with $\frac{4}{5}\cdot 1.19213 \cdot 1.51982 < 1.4495 < \frac{3}{2}$ (verified: $L(2) \approx 1.192126 < 1.19213$, $15/\pi^2 \approx 1.519818 < 1.51982$, and $0.8 \times 1.19213 \times 1.51982 = 1.44945841328 < 1.4495$). |
| **M4** | **Closed** | Line 340 rewrites the quartic-character remark cleanly: notes why $G(p) = 0$ at $\chi(p) = -1$ (density $1/4$, $\sum 1/p = \infty$) prevents direct application of Lemma 3.1, introduces the truncated multiplicative majorant $G_P$ (keeping $\mathbf 1[2 \mid e]$ for $p \le P$ with $\chi(p) = -1$ and $1$ for $p > P$), applies Lemma 3.1 to obtain $\limsup \le K_\Phi W_0 \prod_{p \le P,\, \chi(p)=-1} \frac{p}{p+1} \to 0$ as $P \to \infty$, and deduces $(f_{01}+f_{10})(N) \to 0$ and $D^-(L_\Phi(2^k); 2) = 1$ for every $k \ge 1$ via Theorem 7.1 and Proposition 2.4(4). Properly labeled *Paper proof sketch; no Tauberian input and no constants needed*. |

### Minor Findings (m1–m12)

| ID | Status | Verification |
| --- | --- | --- |
| **m1** | **Closed** | Line 93 (Lemma 1.3 proof) explicitly separates $j = m$ from $j > m$ and notes that $(m-1, m)$ is absent when $m = 0$. |
| **m2** | **Closed** | Line 50 specifies $m_i \in \mathbb Z_{\ge 0}$ in the definition of $w_\pm$. |
| **m3** | **Closed** | Lines 135 and 142 (Corollary 2.3) use $\log(1 + \lvert a(n) \rvert) = o(n)$. |
| **m4** | **Closed** | Line 176 (Lemma 3.2) explicitly extends $s_b$ to $\mathbb Z$ via $s_b(c) := s_b(\lvert c \rvert)$. |
| **m5** | **Closed** | Line 246 adds a rigorous direct base-4 transfer remark for $E(4)$ ($k = 1$): $w_4(\tau(n)) \ge 1 > 3/4$ rules out Proposition 2.4(2); $s_4(\tau(n)) \ge 2$ unless $\tau(n)$ is a power of $4$; the multiplicative indicator $\mathbf 1[\tau(n) = 2^t]$ has value $1$ at every prime and hence density $\delta_2 = \prod_p(1-p^{-1})\sum_{i\ge 0} p^{1-2^i} \le \frac{1}{2}\sum_{i\ge 0} 2^{1-2^i} \approx 0.81642 < 0.8165$ by Lemma 3.1; extending $(-1)^{t(n)}$ by $0$ gives a real multiplicative function with $|f| \le 1$ and $f(p) = -1$ at every prime, whose mean is $0$ by Wirsing's theorem (properly labeled `External input`), yielding power-of-4 density $\delta_2/2 < 0.4083$ and $\liminf \frac{1}{X}\sum_{n\le X} s_4(\tau(n)) \ge 2 - \delta_2/2 > 1.59 > 3/2$. *(Cosmetic note only, non-blocking: line 246 ends with a stray literal `\n` after `(§9).`.)* |
| **m6** | **Closed** | Line 353 (Theorem 9.1(2)) clarifies that a proof of $\limsup f_1 < \frac{1}{2}$ must exhibit $\liminf \kappa_2(N)/N > (C_{\rm true}-1)/2 \ge 0.169551$, while simple nonnormality could also arise from non-convergence of $\kappa_2(N)/N$. |
| **m7** | **Closed** | Line 376 writes the three-fold collision condition explicitly as $n_1 - \omega(n_1) = n_2 - \omega(n_2) = n_3 - \omega(n_3)$ with $n_1 < n_2 < n_3$, absent incoming carries. |
| **m8** | **Closed** | Line 427 (`nonzeroDigits`) uses `(· != 0)` for `List.filter`. |
| **m9** | **Closed** | Lines 522–531 (L13) add `moebiusReal` with the `ℤ → ℝ` coercion and drop the unused `hG` hypothesis from `tendsto_average_of_summable_conv_mobius`. |
| **m10** | **Closed** | Line 340 clarifies the odd-$h \ge 5$ remark via integral-basis coordinates and subadditivity, yielding a majorant growing like $2^{\#\{p \parallel n : \chi(p) \ne 0, 1\}}$, while noting this does not prove the true mean is infinite. |
| **m11** | **Closed** | `scripts/phase24_digit_mass.py` lines 449–450 compute `dsum = sb(PN & ((1 << N) - 1), 2)` independently and assert `dsum + sb(intpart, 2) == sb(PN, 2)` (non-tautological). |
| **m12** | **Closed** | `scripts/phase24_digit_mass.py` removes unused `sumsq_tail=None` (line 608) and `absdiff` (line 721), and adds explicit domain checks `Ap * S2 < 1 and Am * S2 < 1` (line 593) and `A * S2 < 1 and (1 + Am) * S2 < 1` (line 808). |

### Final Post-Repair Verdict

**ACCEPT.** All 4 Major findings (**M1–M4**) and all 12 Minor findings (**m1–m12**) are closed, and `python -B scripts/phase24_digit_mass.py` exits with code `0` (`3,095,904` checks passed).

*Note: Cross-model review is **not** independent human peer review.*
