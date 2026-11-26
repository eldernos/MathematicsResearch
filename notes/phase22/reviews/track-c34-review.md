# Independent Cross-Provider Referee Review: Phase 22 Track C (C3–C4)

**Audited files:**
- `notes/phase22/short-orbits-and-irrationality.md` (lines 1–275)
- `scripts/phase22_short_orbits.py` (lines 1–635)

**Scope note:** This is an automated cross-provider mathematical referee audit. Cross-model review is **not** independent human peer review and does not substitute for human refereeing or formal kernel verification.

---

## Executive Summary & Sub-Track Verdicts

- **Script verification:** `python -B scripts/phase22_short_orbits.py` ran cleanly from the worktree root with **exit code 0** in **9.52 seconds** (`All Phase 22 C3-C4 checks passed.`). Almost all reported numbers match the script output exactly; two reporting discrepancies were found (line 234 convergent count `736` vs. `736 partial quotients`; line 254 Theorem S $d=5$ defect `10` vs. `[8, 10, 10, 10, 12, 10]`).
- **Core mathematics:** Every headline theorem (**Lemma A**, **Corollary B**, **Theorem E**, **Theorem H′**, **Proposition 5.1**, **Theorem G**, **Theorem S**) is **true** as stated (up to the missing word "strictly increasing" in Theorem S, line 240). In particular:
  - **Lemma A** and **Corollary B** are completely sound, self-contained, and elementary, with all constants (`9`, `18`, $\delta = 2^{-\lceil 2/\theta \rceil - 3}$, $M_* = p^{n_\theta+8}$) verified line-by-line including $p = 3$.
  - **Theorem G**'s exact $p$-adic depth mechanism (lexicographic initial segment, $\le r+1$ candidate ties, $(r+1)!$ multiplicity cap, non-cancellation, lower-degree domination) is airtight.
  - **Theorem S**'s verbatim transfer of Phase 13/14 periodic pole retention modulo $p^l$ under auxiliary units $u_{k_j}/\ell_j \equiv 1 \pmod{p^j}$ and its exact irrationality exponent $\mu(W_S) = p$ are airtight.
- **Defects found:** **0 Critical**, **5 Major** (all cleanly repairable proof gaps or false auxiliary asymptotics), **6 Minor** (parameter caps, notation collisions, script-description accuracy, and self-containedness).

| Sub-track | Verdict | Summary |
|---|---|---|
| **C3** (Lemma A, Corollary B, Theorem E, Theorem H′) | **Revise (Major)** | Lemma A and Corollary B are sound. Theorem E omits Corollary Q1's freezing constraint $c_0(1+d/s)\log p < 1/2$ (breaks freezing for $r \ge 5$). Theorem H′ asserts $A(G) = O(\log\log N)$ via §2's $\Lambda \le N^{O(1)}$ bound, which fails for $r=1$ (where $\Lambda_K \gg N^C$) and is unproved for $r \ge 2$ without controlling Wieferich primes; an elementary 4-line divisor-bound proof repairs it. Summary line 13 states a false $\asymp$ asymptotic for $\log A_b(\ell_j)$. |
| **C4** (Prop 5.1, Theorem G, Theorem S, §8) | **Revise (Major)** | Prop 5.1 and Theorem S are sound (Minor clarifications and script-description fix only). Theorem G repeats the unjustified $A(G) = O(\log\log N)$ step at $r=1$ (line 230) and falsely claims $\log D_k = O(k)$ (line 232, false for the note's own $r=1$ schedule), both cleanly repairable. §8 item 2 (line 259) relies on the mathematically false asymptotic $\log A(\ell_k) \asymp k\log\log k\log\log\log k$. |

---

## 1. Script Execution & Table/Number Audit

Command executed from worktree root: `python -B scripts/phase22_short_orbits.py`
- **Exit code:** `0`
- **Measured runtime:** `9.52 s` (note line 267 says "about 8 seconds" — consistent within machine variance).

| Note line(s) | Claimed value / statement | Script output | Match? |
|---|---|---|---|
| 9, 79, 269 | LTE `31840` cases; vanishing `41` cases; sharpness `|S|/M > 0.98` for `(3,6),(5,4),(7,3)` | `31840 cases`; `41 cases`; `|S|/M > 0.98 (3 cases)` | **Match** |
| 141 | $\delta = 2^{-19}$ at $(r,s,d)=(2,2,3)$ | `r=2 s=2 d=3 ... theta=0.1250 n_theta=17 delta=2^-19` | **Match** |
| 10, 113, 270 | `53` shifts of $W^2$ ($d=3,4,5,6$), `243` divisors of $\prod \ell^2$, $v_3(T_Q)\in\{0,1,2\}$, $T=1500$, tol $10^{-8}T$ | `12+16+12+13 = 53` shifts; `243 divisors`; `[0, 1, 2]`; `T=1500`, `1e-8 * T` | **Match** |
| 197 | $\rho_{10^4}\approx 2000$ (H, $d=5$), $\approx 515$ (U) | `k=10000: rho=2000.4 ... rho=515.4` | **Match** |
| 217 | $r=1$, $b=2$, $\lambda=3$, max ratio over $20<j\le 3000$ is `0.595` | `max ratio ... over 20<j<=3000 = 0.595` | **Match** |
| 15, 228, 271 | `145` insertion positions across $(1,3,3),(2,7,3),(3,29,4)$ with $4x+1$, $5x^2+2x+3$, $29x^3+3x^2+1$ | `11 + 49 + 85 = 145` positions; polynomials `(1,4)`, `(3,2,5)`, `(1,0,3,29)` | **Match** |
| 234 | $-\log|W-U_k|/\log\operatorname{den}U_k$ rises to `2.9962` ($\lambda=3,k=8$) and `3.9971` ($\lambda=4,k=5$); max convergent exponent `2.9894`; $U_4,\dots,U_7$ are convergents | `2.9962..2.9962`; `3.9971..3.9971`; `2.9894`; `U_4..U_7 are convergents` | **Match** |
| 234 | "all **736** continued-fraction convergents of $U_8$ with $2^{30}\le q\le 2\operatorname{den}U_7$" | `736 partial quotients` (includes skipped $q < 2^{30}$ and the stopping step $q > 2\operatorname{den}U_7$) | **Mismatch (Minor #10)** |
| 236 | $r=2, p=3, \lambda=3$, $X=n_8+n_6$, top `(7,7),(8,6)`, count 3, valuation `-13` vs `-14` | `v_3(S_2) = -13 > -w* = -14 (the pole cancels by 1)` | **Match** |
| 254 | Theorem S ($p=3,b=2$, aux `5,7,11` at `2,4,6`): "maximal depth defect ... stabilizes. It is `3, 4, 8, 10` for $d=2,3,4,5$" | `d=2:[3..3]`, `d=3:[4..4]`, `d=4:[8..8]`, **`d=5: modified [8, 10, 10, 10, 12, 10]`** | **Mismatch (Minor #9)** |
| 258 | $K=10, r=2$: $\log_2 p^{re_K}\approx 1.9\times 10^5$ vs $\log_2 \lambda^K = 20$ | `1.87e+05` vs `20` | **Match** |
| 259 | $b=2$: $\log\operatorname{lcm}\operatorname{ord}_{\ell_j} 2 > k\log 3$ for $36 < k \le 3000$; `1565` vs `1099` at $k=1000$ | `k=1000: 1565 vs 1099`; `36 < k <= 3000` | **Match** |

---

## 2. Detailed Line-by-Line Analytic Audit

### 2.1 Lemma A (`lines 31–81`) — **Sound**
All steps were independently re-derived and checked at edge cases:
- **LTE (line 37):** For any odd prime $p \ge 3$ (including $p=3$) and any integer $G \equiv 1 \pmod p$, $G \ne 1$ (even $G < 0$), writing $G = 1 + u p^A$ with $p \nmid u$ and $A \ge 1$ gives $v_p((1+up^A)^p - 1) = A + 1$ since $\binom{p}{2}p^{2A}$ has valuation $\ge 1 + 2A \ge A + 2$ and $p^{kA}$ ($k \ge 3$) has valuation $\ge 3A \ge A + 2$. Hence $v_p(G^n - 1) = A + v_p(n)$ for all $n \ge 1$.
- **Complete periods (lines 37–43):** $\operatorname{ord}_{p^e}(G) = p^{e-A} = p^X$, so $\langle G \rangle = 1 + p^A \mathbb Z / p^e \mathbb Z$, the complete period sum vanishes for $X \ge 1$ and $p \nmid c$, and reducing $M \bmod p^X$ yields $|S| \le (M \bmod p^X) < p^X$ for all $M \ge 0$.
- **Stride van der Corput (lines 43–49):** Extending $a_m = 0$ outside $[0, M)$, the support of $n \mapsto \sum_{i < H} a_{n+iw}$ is contained in $[-(H-1)w, M-1]$ (length $M + (H-1)w$). Cauchy–Schwarz gives
  $$ H^2 |S|^2 \le (M + (H-1)w)\Big(HM + 2\sum_{h=1}^{H-1}(H-h)\operatorname{Re} C_h\Big) \le H(M + (H-1)w)\Big(M + 2\sum_{h=1}^{H-1}|C_h|\Big), $$
  matching line 46 exactly. For $C_h$, $c(G^{hw}-1) = c_h p^{A + v_p(hw)}$ with $p \nmid c_h$ by LTE, preserving the base $G$ and reducing the exponent to $e_h = e - A - k - j$ (note $M - hw$ should be written $\max(0, M - hw)$ when $M < hw$; Minor #6).
- **Induction constants & bounds (lines 51–77):**
  - Since $\theta \in (0, 1]$, $n_\theta = \lceil 2/\theta \rceil + 1 \ge 3$, so $L_0 = \log_p M_0 \ge n_\theta + 8 \ge 11 \ge 8$.
  - $A \le \frac{3}{16} L_0 - 1 < \frac{3}{16} L_0 - \frac{1}{4} < W/4$, where $W = \lfloor \frac{3}{4} L_0 \rfloor$.
  - The 3-case choice of $k \in [0, \kappa]$ ($\kappa = \lfloor \frac{1}{2} L_0 \rfloor$) guarantees $\frac{3}{4} W \le X_1 = X - A - k \le W + n\kappa$ in all three cases (Case 1 uses $X > W$ and $A \le W/4$; Case 2 gives $X_1 = W$; Case 3 uses $X \le W + (n+1)\kappa$ and $A \ge 1$).
  - For $1 \le h < H = \lfloor M_0^{1/4} \rfloor$, $j = v_p(h) < \frac{1}{4} L_0$, so $X_h = X_1 - j \ge \frac{3}{4} W - \frac{1}{4} L_0 \ge \frac{5}{16} L_0 - \frac{3}{4} \ge \frac{7}{4} \ge 1$, ensuring $e_h > A$ and $(G, e_h, c_h) \in \mathcal F$ with $X_h \le W + n\kappa$.
  - Since $M_0^{1/4} \ge 3^{11/4} > 20$, $H \ge \frac{1}{2} M_0^{1/4}$, and $(H-1)w < M_0^{3/4} \le M_0$, giving $\frac{M+(H-1)w}{H} \le 4 M_0^{3/4}$.
  - Thus $|S|^2 \le 4 M_0^{3/4}(M_0 + 2 H C_n M_0^{1-\delta_n}) \le (4 + 8 C_n) M_0^{2 - \delta_n}$ (since $\delta_n = 2^{-2-n} \le 1/4$), yielding $C_{n+1} = \sqrt{4 + 8 C_n}$ and $\delta_{n+1} = \delta_n / 2 = 2^{-3-n}$.
  - The fixed point of $x = \sqrt{4 + 8x}$ is $4 + 2\sqrt{5} \approx 8.4721 < 9$, so $C_n < 9$ for all $n \ge 0$, completely independent of $G$, $p$, and $\theta$.
  - Conclusion (line 77): $W + n_\theta \kappa \ge (\frac{3}{4} L_0 - 1) + (\frac{2}{\theta} + 1)(\frac{L_0}{2} - 1) \ge \frac{L_0}{\theta} + \frac{5}{4} L_0 - n_\theta - 1 > \frac{L_0}{\theta} \ge e > e - A$ using $L_0 \ge n_\theta + 8$. Every inequality holds.
- **Sharpness (line 79):** $G = 1 + p^a$, $e = 2a$, $c = 1$ gives $G^m \equiv 1 + m p^a \pmod{p^{2a}}$ and $|S|/M > 0.98$ for $M = \lfloor p^a/10 \rfloor$, confirming $A \ge \log_p M + O(1)$ kills cancellation.

### 2.2 Corollary B (`lines 85–113`) — **Sound**
- Since $t \mid p - 1$, $p \nmid t$, so $v_p(L/t) = v_p(\operatorname{lcm}(t, T_Q)/t) = v_p(T_Q)$. LTE for $b^t \equiv 1 \pmod p$ yields $A(b^L) = v_p(b^L - 1) = v_p(b^{t T_Q} - 1) = a_0 + v_p(T_Q)$.
- CRT decomposition $a/(p^e Q) \equiv a_1/p^e + a_2/Q \pmod 1$ with $p \nmid a_1$ and splitting $j = Lm + j_0$ ($0 \le j_0 < L$) is exact; $M_0 = \lceil T/L \rceil \le 2 T/L$ when $L \le T$, giving $9 L M_0^{1-\delta} \le 9 L (2 T/L)^{1-\delta} \le 18 T (L/T)^\delta$.
- For $Q \mid \Lambda^r M'$, $\ker((\mathbb Z/\ell^k)^\times \to (\mathbb Z/\ell)^\times)$ has order $\ell^{k-1}$ coprime to $p$ (including $\ell = 2$ since $p$ is odd), so $v_p(\operatorname{ord}_{\ell^k} b) = v_p(\operatorname{ord}_\ell b) \le v_p(\ell - 1) < \log_p \ell$. Thus $A(G) \le a_0 + v_p(\operatorname{ord}_{M'} b) + \max_{\ell \mid \Lambda} \log_p \ell$.
- **Caveat for later sections:** Line 113 correctly proves $A(G) = O(\log\log N)$ **under the hypothesis $\Lambda \le N^{O(1)}$**. Theorems H′ and G later invoke $A(G) = O(\log\log N)$ in regimes where $\Lambda$ is super-polynomial in $N$ (Findings #1 and #4).

### 2.3 Theorem E (`lines 117–141`) — **Major omission + Minor issues**
- **Major (Finding #2):** Line 125 chooses $L = \lfloor c_0 \log N \rfloor$ with only $c_0 \log p \le rs/(8d)$ and $(c_0 \log p)/s < r/d$, omitting Corollary Q1's third condition $c_0(1 + d/s)\log p < 1/2$ (`nonlinear-boundary.md:131`). Without it, freezing ($J \ge J_0(L) = \lceil L/s + L/d \rceil$) fails on $n \ge \sqrt{N}$ for $r \ge 5$, and for $(r,s,d)=(10,1,11)$ with $c_0 \log p = 5/44$, $p^{d J_0(L)} \approx N^{15/11} \gg N$ leaves no frozen shifts at all.
- **Minor (Findings #6, #7, #8):** $\theta = (d - r - 1/2)/(rs)$ can exceed $1$ when $d > r(s+1)$; $\eta_0 \le rs/(8d)$ needs $\eta_0 < 1$ (e.g. $\eta_0 \le \min(1/2, rs/(8d))$) when $rs \ge 8d$; the letter $L$ is overloaded in the same sentence on line 132; and $q_n \mid p^{rsJ} M'$ (line 125) omits $p^{O_P(1)}$ when $p$ divides the denominator of $P$.
- **Otherwise sound:** Once $c_0$ includes $c_0(1 + d/s)\log p < 1/2$, $\theta$ is capped at $1$, and $\eta_0 \le \min(1/2, rs/(8d))$, the short-run discard ($O(N^{1-\epsilon_1})$), buffer tail ($O_P(N^{(r-1)/d - 2}) \le N^{-1}$ since $r \le d - 1$), uniformity in $h \le H_{\rm ET}$ ($e \ge (\frac{rs}{2d} - \frac{rs}{8d} - \frac{rs}{8d})\log_p N - O(1) = \frac{rs}{4d}\log_p N - O(1)$), combination of Theorem Q with Lemma A, and the $\deg P = 1$ power-saving rate (where $A M_1(u) \equiv A \lfloor u^{1/d} \rfloor \not\equiv 0 \pmod{p^{v_p(A)+1}}$ has zero failed shifts) all hold.

### 2.4 Theorem H′ (`lines 145–174`) — **Two Major gaps + False Summary asymptotic**
- **Major (Finding #1):** Line 155 asserts $A(G) \le a_0 + O(1) + \log_p \ell_{\max} = O(\log\log N) \le \frac{3}{16}\log_p M_0 - 1$ without proving any upper bound on $\ell_{\max}$ from $(\mathrm P_H)$. Line 113 does **not** apply: for $r=1$ on the note's own schedule (lines 164, 171), $\Lambda_K$ is super-polynomial in $N$; for $r \ge 2$, $(\mathrm P_H)$ bounds $\operatorname{ord}_{\Lambda_K^r}(b)$, not $\Lambda_K$ (Wieferich primes are uncontrolled). See Finding #1 below for the elementary 4-line divisor-bound repair.
- **Major (Finding #2 inherited):** Line 153 runs Theorem E's proof and inherits the missing $c_0(1 + d/s)\log p < 1/2$ condition.
- **Major (Finding #3):** Summary line 13 states $\log A_b(\ell_j) \asymp j \log\log j \log\log\log j$, which is false (see Finding #3 below).
- **Otherwise sound:** The splitting mod $L = \operatorname{lcm}(t, \operatorname{ord}_{Q'} b) \le N^{1 - r/d - 4\epsilon_1}$, $M_0 \ge N^{\epsilon_1}$, $e \ge \frac{rs}{4d}\log_p N - O(1)$, and the prime-position thresholds in lines 161–172 (with $\ll$ as on line 171) are verified.

### 2.5 Section 5: Truncation Separation (`lines 178–197`) — **Sound**
- Lemma S: $0 < \xi - U_k \le C \frac{b}{b-1} b^{-n_{k+1}} \le 2 C b^{-n_{k+1}} \le \frac{1}{4 Q D_k b^{n_k}}$, giving $|\xi - A/Q| \ge \frac{3}{4 Q D_k b^{n_k}} \ge \frac{1}{2 Q D_k b^{n_k}}$ for $A/Q \ne U_k$.
- Inequality (5.1): With $Y_k = b^{n_{k+1}-n_k}/(8 C D_k)$ and minimal $k$ with $Q \le Y_k$ ($Y_{k-1} < Q \le Y_k$), $b^{n_k} = (8 C D_{k-1} Y_{k-1})^{\rho_k} < (8 C D_{k-1} Q)^{\rho_k}$ yields (5.1) verbatim.
- Proposition 5.1: Both $\operatorname{den} U_k \ge b^{n_k}$ (numerator mod $b$ is coprime to $b$) and the exact leading constants/asymptotics of $\psi(Q)$ for Theorem H ($\frac{1}{d}(\frac{\log_b Q}{td})^{1/(d-1)}$) and Theorem U ($\exp((1+o(1))\sqrt{\log\log Q})$) are exact.

### 2.6 Theorem G (`lines 201–236`) — **Exact depth sound; two Major proof gaps in digits & $\mu(W)$**
- **Part (1) & Exact depth in Part (2) (lines 219–228):** Completely airtight.
  - $r < \lambda$ implies $(r - c + 1) n_{i'_c - 1} \le r n_{i'_c - 1} < \lambda n_{i'_c - 1} = n_{i'_c}$, so lex order strictly equals position order, distinct $r$-multisets have distinct positions, and present $r$-multisets form $\{M \le_{\rm lex} g\}$.
  - Every $M <_{\rm lex} g$ with first difference at slot $c$ has $g_c \ge 2$ and $w(M) \le w(\mathrm{cand}_c)$ with equality iff $M = \mathrm{cand}_c$. Hence at most $r + 1$ multisets attain $w^*(n)$, contributing between $1$ and $(r+1)\cdot r! = (r+1)!$ ordered $r$-tuples.
  - Since $u_k/\mu_k \equiv 1 \pmod p$ and $b^{-n_i} = (b^t)^{-\lambda^i} \equiv 1 \pmod p$, the top tuples sum to $p^{-w^*} b^n \cdot (\text{count}) \not\equiv 0 \pmod{p^{-w^*+1}}$ because $p > (r+1)!$.
  - For $n \in [n_K, n_{K+1})$ ($K \ge 2$), $((K-1)^r)$ is present ($r n_{K-1} < n_K$), so $r(K-1) \le w^*(n) \le rK$. Lower degrees $a < r$ have weights $\le aK$, strictly dominated once $K > r + v_p(A_r)$.
  - Remark (a) ($\lambda > r$ real, $n_k = t\lceil \lambda^k \rceil$, $\lambda^{k_0}(\lambda - r) > 2r$) was also verified: $r n_{k-1} < rt(\lambda^{k-1}+1) < t\lambda^k \le n_k$ for all $k \ge k_0 + 1$.
- **Major (Finding #4):** Line 230 asserts $A(G) = O(\log\log N)$ without proof under $(\mathrm P_G)$ (fails line 113 at $r=1$ where $\Lambda_K$ is super-polynomial in $N$). Same elementary repair as Finding #1.
- **Major (Finding #5):** Line 232 asserts $\log D_k = O(k) = o(\lambda^k)$ for $D_k = p^k \Lambda_k$. The claim $\log D_k = O(k)$ is **false** for the note's own $r=1$ schedule $k_j = j\lceil(\log\log(j+16))^2\rceil$ (line 217), where $\log \Lambda_{k_j} \sim j\log j \gg k_j$. However, $\log D_k = o(\lambda^k)$ DOES follow in one line from $(\mathrm P_G)$ via $\log \Lambda_k < \operatorname{ord}_{\Lambda_k}(b)\log b \le (\log b)\lambda^{(1-\epsilon)k} = o(\lambda^k)$.
- **Exact $\mu(W)$ once Finding #5 is patched:** CRT on pairwise coprime $p, \operatorname{rad}(b), \ell_j$ gives $u_{k_j} \le p \operatorname{rad}(b) \ell_j$, so $0 < c_k \le \operatorname{rad}(b)$. Exact $\operatorname{den} U_k = D_k b^{n_k}$ holds. With $\log D_k = o(\lambda^k)$ and $\log(1/c_{k+1}) \le (k+1)\log p + \log \Lambda_{k+1} = o(\lambda^k)$, both the lower bound $\mu(W) \ge \lambda$ (via $U_k$) and the upper bound $\mu(W) \le \max(\lambda, \frac{2\lambda - 1}{\lambda - 1})$ (via Lemma S / (5.1)) are completely airtight, giving $\mu(W) = \lambda$ for $\lambda \ge 3$ and transcendence by Roth's theorem.

### 2.7 Theorem S (`lines 240–254`) — **Sound (Minor revisions only)**
- **Periodic pole retention transfer (line 250):** Checked directly against `notes/phase14/quantitative-composites.md` and `NormalityChecker/PeriodicPolynomialNormal.lean` (`periodic_power_retained_denominator`).
  - For $p$ odd ($c = p > 2$), Phase 13/14 gives a precision $l \ge 1$ such that $v_p(p^{dk} R_d^{\alpha_{b,p}}(n)) \le l - 1$ for all $p^k \le n < p^{k+1}$ and all $k \ge K_p(l)$.
  - In $p^{dk} R_d^{W_S}(n) = \sum_{\sum p^{j_i} \le n} (\prod \frac{u_{j_i}}{\mu_{j_i}}) p^{\sum(k - j_i)} b^{n - \sum p^{j_i}} \in \mathbb Z_{(p)}$, every tuple with $\sum(k - j_i) \ge l$ vanishes modulo $p^l$.
  - Every surviving tuple has $k - j_i \le l - 1$ for all $i$, so $j_i \ge k - l + 1$. Since $k_1 < k_2 < \cdots$ is strictly increasing (needs stating explicitly on line 240; Minor #9), once $k \ge k_{l-1} + l$, every auxiliary index $k_J \ge k - l + 1$ satisfies $J \ge l$, hence $u_{k_J}/\ell_J \equiv 1 \pmod{p^J}$, so $\equiv 1 \pmod{p^l}$ in $\mathbb Z_{(p)}$.
  - Thus $p^{dk} R_d^{W_S}(n) \equiv p^{dk} R_d^{\alpha_{b,p}}(n) \pmod{p^l}$ in $\mathbb Z_{(p)}$, transferring $v_p(p^{dk} R_d^{W_S}(n)) \le l - 1$ verbatim.
  - Lower degrees $a < d$ have $p^{ak} R_a^{W_S}(n) \in \mathbb Z_{(p)}$ (since $\gcd(\Lambda_k, p) = 1$), so they carry $p^{(d-a)k} \in p^k \mathbb Z_{(p)}$ in $p^{dk} R_Y^{W_S}(n)$ and cannot cancel $A_d p^{dk} R_d^{W_S}(n)$ once $k > l - 1 + v_p(A_d)$.
- **Exact $\mu(W_S) = p$ (line 248):** CRT gives $u_{k_j} \le p^j \operatorname{rad}(b) \ell_j$, hence $0 < c_{k_j} \le p^{j - k_j} \operatorname{rad}(b) \le \operatorname{rad}(b)$ since $k_j \ge j$. Here $\log \Lambda_k = o(k)$ genuinely implies $\log D_k = O(k) = o(p^k)$ and $\Lambda_k = N^{o(1)}$ (so §2's $A(G) = O(\log\log N)$ genuinely applies!). Since $p \ge 3$, $\frac{2p-1}{p-1} \le \frac{5}{2} < p$, so $\mu(W_S) = p$ is completely airtight.
- **Digits (line 252):** Works for all $d \ge 1$, including $d > p$, because even when tuples collide at a position $m$, multiplicity is at most $(\log_p m)^d$, which is crushed by $b^{-\lceil 2\log_b N \rceil} = N^{-2}$ off the buffers. (Worth one explicit sentence since Theorem G relied on distinct positions.)

---

## 3. Classified Findings and Actionable Repairs

### Critical Findings
None.

### Major Findings

1. **[Major — C3] Unjustified $A(G) = O(\log\log N)$ in Theorem H′ (`notes/phase22/short-orbits-and-irrationality.md:155`).**
   - **Problem:** Line 155 asserts $A(G) \le a_0 + O(1) + \log_p \ell_{\max} = O(\log\log N) \le \frac{3}{16}\log_p M_0 - 1$. The only bound on $\ell_{\max}$ in the note is §2 (line 113), which assumes $\Lambda \le N^{O(1)}$. Under $(\mathrm P_H)$, this hypothesis fails for $r = 1$ (in the note's own degree-1 schedule on lines 164 and 171, $\log \Lambda_K \sim j\log j$ while $\log N \ll j\log\log j$, so $\Lambda_K \gg N^C$ for every $C$) and is unproved for $r \ge 2$ because Wieferich primes are uncontrolled (line 174).
   - **Repair:** Add a 4-line elementary bound showing $\log_p \ell_{\max} = O(\frac{\log N}{\log\log N}) = o(\log_p M_0)$ directly from $M := \operatorname{ord}_{\Lambda_K}(b) = A_b(\ell_{\max}) \le N$:
     1. At most $\sum_{m \le x^{1/3}} \omega(b^m - 1) \le (\log_2 b) x^{2/3}$ primes $\ell \le x := \ell_{\max}$ satisfy $\operatorname{ord}_\ell(b) \le x^{1/3}$.
     2. Each remaining prime $\ell \le x$ ($\ell \nmid pb$) has $m = \operatorname{ord}_\ell(b) > x^{1/3}$ dividing $M$ and satisfies $\ell \equiv 1 \pmod m$ (at most $x/m < x^{2/3}$ such $\ell$ per $m$).
     3. Hence $\pi(x) - O_b(x^{2/3}) \le d(M) x^{2/3}$, so $d(M) \gg x^{1/3}/\log x$.
     4. The standard divisor bound $\log d(M) \ll \frac{\log M}{\log\log M}$ yields $\log x \ll \frac{\log M}{\log\log M} \le \frac{\log N}{\log\log N}$, giving $A(G) = O(\frac{\log N}{\log\log N}) = o(\log_p M_0) \le \frac{3}{16}\log_p M_0 - 1$ (and $A(G) < e$) for large $N$ with no new deep input. (Alternatively, Bombieri–Vinogradov/Goldfeld gives $\log A_b(x) \gg x^{0.55}$ and hence literally $A(G) = O(\log\log N)$.)

2. **[Major — C3] Missing freezing condition on $c_0$ in Theorem E (`notes/phase22/short-orbits-and-irrationality.md:125, 127`, inherited by Theorem H′ at `line 153`).**
   - **Problem:** Line 125 imposes only $c_0 \log p \le rs/(8d)$ and $(c_0 \log p)/s < r/d$, omitting Corollary Q1's third condition $c_0 (1 + d/s)\log p < 1/2$ (`notes/phase21/nonlinear-boundary.md:131`). Since freezing holds only for $J \ge J_0(L) = \lceil L/s + L/d \rceil$, shifts with $J < J_0(L)$ extend to $t p^{d J_0(L)} \asymp N^{c_0(1+d/s)\log p}$. For $(r, s, d) = (10, 1, 11)$, $c_0 \log p = 5/44$ satisfies line 125 yet gives $p^{d J_0(L)} \approx N^{15/11} \gg N$, so no shift in $[1, N]$ reaches the frozen regime (and already at $(5,1,6)$, $N^{35/48} \gg \sqrt{N}$).
   - **Repair:** Add $c_0(1 + d/s)\log p < 1/2$ to the parameter constraints for $c_0$ on line 125 (i.e. $c_0 \log p < \min(\frac{rs}{8d}, \frac{s}{2(d+s)})$).

3. **[Major — C3 & C4] Mathematically false two-sided asymptotic $\log A_b(\ell_j) \asymp j\log\log j\log\log\log j$ and $\log A(\ell_k) \asymp k\log\log k\log\log\log k$ (`notes/phase22/short-orbits-and-irrationality.md:13, 259`).**
   - **Problem:** Line 13 claims $\log A_b(\ell_j) \asymp j\log\log j\log\log\log j$, and line 259 claims that for $W = \sum 1/(p^k \ell_k b^{3^k})$, "the period bound $t p^k A(\ell_k)$ is not $o(3^k)$, because $\log A(\ell_k) \asymp k\log\log k\log\log\log k$." Both two-sided asymptotics are **false**: by Selberg's two-dimensional upper-bound sieve on $(q, mq+1)$ for even $m < \log x$ and $\sum_{m < \log x} 1/\phi(m) \ll \log\log x$,
     $$ \log A_b(x) \le \log A(x) \ll \frac{x}{\log x} + \sum_{2 \le m < \log x} \log x \cdot \frac{x}{\phi(m)(\log x)^2} \ll \frac{x \log\log x}{\log x}, $$
     so at $x = \ell_k \sim k\log k$, $\log A_b(\ell_k) \le \log A(\ell_k) \ll k\log\log k = o(k\log\log k\log\log\log k)$. The $\log\log\log$ factor in Phase 19 (`notes/phase19/grids.md:156`) came solely from replacing $\log\log(3m)$ by its worst case in an **upper bound** ($\ll$), never a lower bound. Additionally, on line 259, $t p^k A(\ell_k)$ already fails $o(3^k)$ trivially from $p^k \ge 3^k$ (for any odd prime $p \ge 3$), whereas the auxiliary-order failure $\log A_b(\ell_k) > k\log 3$ is only supported numerically in the script ($36 < k \le 3000$), not proved in the note.
   - **Repair:** On line 13, replace $\asymp$ by $\ll$ (matching line 171). On line 259, delete the false $\asymp k\log\log k\log\log\log k$; note that $t p^k A(\ell_k) \ge 3^k$ already fails $o(3^k)$ for every odd prime $p \ge 3$, and state accurately that for the auxiliary-only budget $L \le T^{1-\eta}$, the script numerically finds $\log A_2(\ell_k) > k\log 3$ for all $36 < k \le 3000$ (motivating the sparse condition $(\mathrm P_G)$).

4. **[Major — C4] Unjustified $A(G) = O(\log\log N)$ in Theorem G (`notes/phase22/short-orbits-and-irrationality.md:230`).**
   - **Problem:** Identical to Finding #1: line 230 asserts $A(G) = O(\log\log N)$ under $(\mathrm P_G)$, but at $r=1$ with $k_j = j\lceil(\log\log(j+16))^2\rceil$ (line 217), $\log \Lambda_{k_j} \sim j\log j$ while $\log N \asymp j(\log\log j)^2$, so $\Lambda_K$ is super-polynomial in $N$ and §2 (line 113) does not apply.
   - **Repair:** Invoke the same elementary 4-line divisor-bound lemma from Finding #1 to obtain $A(G) = O(\frac{\log N}{\log\log N}) = o(\log_p M_0)$ directly from $\operatorname{ord}_{\Lambda_K}(b) \le \operatorname{ord}_{\Lambda_K^r}(b) \le N$ (or cite Goldfeld/Bombieri–Vinogradov for $O(\log\log N)$).

5. **[Major — C4] False claim $\log D_k = O(k)$ in Theorem G(3) (`notes/phase22/short-orbits-and-irrationality.md:232`).**
   - **Problem:** Line 232 states $\log D_k = O(k) = o(\lambda^k)$ for $D_k = p^k \Lambda_k$. For $r = 1$ with the note's own schedule $k_j = j\lceil(\log\log(j+16))^2\rceil$ (line 217), $\log D_{k_j} \ge \log \Lambda_{k_j} \sim j\log j \asymp k_j \frac{\log k_j}{(\log\log k_j)^2} \neq O(k_j)$. Nor does $(\mathrm P_G)$ alone imply $\log \Lambda_k = O(k)$ for $r \ge 2$ without ruling out Wieferich primes.
   - **Repair:** Replace "$\log D_k = O(k) = o(\lambda^k)$" by the exact 1-line deduction from $(\mathrm P_G)$: since $\Lambda_k \mid b^{\operatorname{ord}_{\Lambda_k}(b)} - 1$,
     $$ \log \Lambda_k < \operatorname{ord}_{\Lambda_k}(b)\log b \le \operatorname{ord}_{\Lambda_k^r}(b)\log b \le (\log b)\lambda^{(1-\epsilon)k} = o(\lambda^k), $$
     hence $\log D_k = k\log p + \log \Lambda_k = o(\lambda^k)$ (and similarly $\log(1/c_{k+1}) \le (k+1)\log p + \log \Lambda_{k+1} = o(\lambda^k)$, justifying $|W - U_k| \ge c_{k+1} b^{-\lambda n_k} \ge Q^{-\lambda - o(1)}$).

### Minor Findings

6. **[Minor — C3] Parameter caps missing for Lemma A and Erdős–Turán (`notes/phase22/short-orbits-and-irrationality.md:128, 134, 156, 230`).**
   - Lemma A requires $\theta \in (0, 1]$ (line 31), but $\theta = \frac{d-r-1/2}{rs}$ (line 134) exceeds $1$ for $d > r(s+1) + 1/2$, $\theta = \frac{d\epsilon_1}{2rs}$ (line 156) can exceed $1$ for large $d$, and $\theta = \frac{\epsilon \log\lambda}{2r\log p}$ (line 230) needs $\epsilon$ small enough that $\theta \le 1$. Fix: cap $\theta = \min(1, \dots)$ in Theorems E and H′, and note $\epsilon$ is chosen small enough that $\theta \le 1$ in Theorem G.
   - In Theorem E (line 128), $\eta_0 \le rs/(8d)$ can exceed $1$ when $rs \ge 8d$, making $N^{\eta_0 - 1} \ge 1$ on line 137. Fix: require $0 < \eta_0 \le \min(1/2, rs/(8d))$.

7. **[Minor — C3] Notation collisions and tiny slips in §1–§4 (`notes/phase22/short-orbits-and-irrationality.md:9, 31, 49, 77, 125, 132, 153, 174`).**
   - **Line 9 (Summary):** Lemma A summary omits $M_0 \ge M_* = p^{n_\theta + 8}$ (and $p \nmid c$, $p$ odd).
   - **Line 31:** Explicitly state $e, c \in \mathbb Z$.
   - **Line 49:** Write $C_h = S(G, e_h, c_h; \max(0, M - hw))$ (empty sum $= 0$ if $M \le hw$) to match Claim($n$)'s $0 \le M \le M_0$.
   - **Line 77:** Typo `$W + n\kappa$` should be `$W + n_\theta \kappa$`.
   - **Line 125:** `$q_n \mid p^{rsJ} M'$` should be `$q_n \mid p^{rsJ + O_P(1)} M'$` if $p$ divides the denominator of $P$ (already accounted for by $+O(1)$ on line 132).
   - **Lines 132 & 153:** $L$ is simultaneously used for $p$-adic precision $\lfloor c_0 \log N \rfloor$ and Corollary B's stride $\operatorname{lcm}(t, \operatorname{ord}_{Q'} b)$ in the same sentence; rename the stride (e.g., $L_{\rm per}$).
   - **Line 174:** $\operatorname{ord}_{\Lambda^r}(b) \ge \Lambda^{r-1}$ (for non-Wieferich $\ell \mid \Lambda$) is off by a factor of $2$ when $b$ is odd, $2 \mid \Lambda$, and $r \ge 3$ (since $\operatorname{ord}_{2^r}(b) \le 2^{r-2}$); state $\ge \frac{1}{2}\Lambda^{r-1}$ or restrict to odd $\ell$.

8. **[Minor — C4] Technical tightening in Theorem G & §5 (`notes/phase22/short-orbits-and-irrationality.md:178, 221, 230, 232`).**
   - **Lines 178 vs. 240:** Both Lemma S (§5) and Theorem S (§7) use the letter `S`.
   - **Line 221:** Add one clause reducing $\deg P \le r$ to $\deg P = r$ (replacing $r$ by $\deg P$ preserves $p > (r+1)!$, $\lambda > r$, and $(\mathrm P_G)$).
   - **Line 230:** Write $Q' \mid \Lambda_K^r D'_0$ where $D'_0$ is the prime-to-$p$ part of $D_0$ (likewise line 252 in Theorem S); distinguish $K(N)$ from the run's shell index $K(n_0) \in [(1-\epsilon)\log_\lambda N - O(1), K(N)]$ (noting that cutting at shell boundaries $n_k$, or using the insertions $r n_k$, enforces $K(n_0) \ge (1-\epsilon)\log_\lambda N - O(1)$ on long runs); include the $\log N$ harmonic-sum factor on $N^{-\epsilon\delta}$ (absorbed into $N^{-\eta_P}$).
   - **Line 232:** Add the 1-line CRT justification for $0 < c_k \le \operatorname{rad}(b)$ ($u_{k_j} \le p \operatorname{rad}(b) \ell_j$ by CRT on pairwise coprime $p, \operatorname{rad}(b), \ell_j$).

9. **[Minor — C4] Theorem S statement omissions & script-check overstatement (`notes/phase22/short-orbits-and-irrationality.md:240, 250, 252, 254`; `scripts/phase22_short_orbits.py:572–618`).**
   - **Line 240:** State "**strictly increasing** indices $k_j \ge j$" (needed for $\mu_{k_j}$ to be well-defined and for $k_J \to \infty \implies J \to \infty$ on line 250). Also note $\log A_b(\ell_{j(K)}) = o(K)$ is redundant since $A_b(\ell_{j(K)}) \mid \phi(\Lambda_K) < \Lambda_K$ already gives $\log A_b(\ell_{j(K)}) < \log \Lambda_K = o(K)$.
   - **Lines 250 & 252:** Explicitly note (i) lower-degree terms $a < d$ satisfy $p^{ak} R_a^{W_S}(n) \in \mathbb Z_{(p)}$ and carry $p^{(d-a)k}$, hence cannot cancel the leading pole for $k > l - 1 + v_p(A_d)$, and (ii) for $d > p$, insertion multiplicity at $m$ is at most $(\log_p m)^d$, which is still crushed by $b^{-\lceil 2\log_b N \rceil} = N^{-2}$ off the buffers.
   - **Line 254 & `stoneham_all_prime()`:** For $d = 5$ ($k=3..8$), the script outputs `modified [8, 10, 10, 10, 12, 10]` — the maximum defect is **12** (at $k = 7$), not `10`, and returning to `10` at the single last shell $k = 8$ does not yet demonstrate stabilization. Moreover, because `aux = {2: 5, 4: 7, 6: 11}` has only 3 primes ($J \le 3 < l$ for all $d \in \{2,3,4,5\}$), the script never exercises an auxiliary prime inside the active reflected window $[k - l + 1, k]$ with $J \ge l$. Fix the prose on line 254 (and optionally extend the script with an auxiliary prime having $J \ge l$ inside $[k - l + 1, k]$ for $d=2, 3$ to directly test the congruence transfer).

10. **[Minor — C4] Continued-fraction count wording mismatch (`notes/phase22/short-orbits-and-irrationality.md:234`; `scripts/phase22_short_orbits.py:498–521`).**
    - **Problem:** Line 234 reads "all 736 continued-fraction convergents of $U_8$ with $2^{30} \le q \le 2\operatorname{den}U_7$ have exponent at most $2.9894$." In the script, `steps = 736` counts all partial quotients up to and including the stopping step `k1 > qlimit`, including those with `k1 < 2**30` skipped by `continue`.
    - **Repair:** Reword line 234 to match the script printout ("among the first 735 convergents of $U_8$, every convergent with $2^{30} \le q \le 2\operatorname{den}U_7$ has exponent at most $2.9894$"), or print the exact filtered count in the script.

11. **[Minor — Scope hygiene] Standalone phrasing of "proposed" items (`notes/phase22/short-orbits-and-irrationality.md:81, 174, 256, 261`).**
    - **Observation:** Neither audited file contains forbidden process language (`"the brief"`, `"prompt"`, `"agent"`, etc.). However, lines 81, 174, 256, and 261 refer to `"the proposed condition / budget / arguments / bound"` without naming where they were proposed.
    - **Repair:** For a mathematician reading the note standalone, rephrase `"the proposed ..."` as `"a naive ..."` / `"the candidate ..."` / `"obstacles to alternative constructions"`.

---

## Post-Repair Verification

Re-audited the revised `notes/phase22/short-orbits-and-irrationality.md` (285 lines) and `scripts/phase22_short_orbits.py` (678 lines), and re-ran `python -B scripts/phase22_short_orbits.py` from the worktree root.

### Script Re-run & Output Check
- **Command:** `python -B scripts/phase22_short_orbits.py`
- **Exit code:** `0` (`All Phase 22 C3-C4 checks passed.`)
- **Runtime:** `6.17 s` (matches line 277: "runs in under 10 seconds and exits 0").
- **Process-language grep** (`brief|prompt|subagent|agent|todo|fixme|proposed`): **0 matches** in both files.
- **Updated script outputs verified against prose:**
  - Continued fractions (`convergent_check`, lines 500–524): `724 convergents with 2^30 <= q <= 2 den(U_7) (from 736 partial quotients computed); U_4..U_7 are among them; largest exponent: 2.9894` — matches lines 244 and 281 verbatim.
  - Theorem S (`stoneham_all_prime`, lines 614–661):
    - Early-aux defects: `d=2:[3..3]`, `d=3:[4..4]`, `d=4:[8..8]`, `d=5: modified [8, 10, 10, 10, 12, 10]; alpha_(2,3) [8, 9, 11, 10, 10, 10]` — matches line 264 verbatim.
    - Direct active-window congruence transfer (`k_J = J+1`, $J = 1..8$, $u_{k_J} \equiv \ell_J \pmod{3^J}$): `d=2, l=4` matches `alpha_(2,3) mod 3^4` and is nonzero at all `42` positions of shells `k=8..11` (active auxiliary indices `[5, 6, 7, 8, 9]`, all satisfying $J \ge 4$); `d=3, l=5` matches `alpha_(2,3) mod 3^5` and is nonzero at all `121` positions of shells `k=10..11` (active auxiliary indices `[6, 7, 8, 9]`, all satisfying $J \ge 5$) — matches lines 16, 264, and 282 verbatim.

### Repair-by-Repair Verification

| Prior Finding | Status | Verification Notes |
|---|---|---|
| **Major #1** (Theorem H′ $A(G)$ gap) | **Resolved** | New **Lemma D** (lines 115–123) proves $\log x \ll_b \log A_b(x)/\log\log A_b(x)$ elementarily via $\sum_{m \le x^{1/3}} m\log_2 b \le x^{2/3}\log_2 b$, $\pi(x) - \omega(pb) - x^{2/3}\log_2 b \le d(M) x^{2/3}$, and the divisor bound; applied cleanly in Theorem H′ (line 165) using $\operatorname{ord}_{\Lambda_K} b \le \operatorname{ord}_{\Lambda_K^r} b \le N$ to get $A(G) = O(\log N/\log\log N) = o(\log_p M_0) \le \frac{3}{16}\log_p M_0 - 1$. *(See 1 trivial residual Minor note below on `- 2` vs `- \omega(pb)` at line 121.)* |
| **Major #2** (Theorem E freezing constraint on $c_0$) | **Resolved** | Line 135 restores $c_0(1+d/s)\log p < 1/2$ and notes it forces all unfrozen shells $J < J_0(L)$ below $\sqrt{N}$ for large $N$; inherited explicitly by Theorem H′ on line 163. |
| **Major #3** (False $\log A_b(\ell_j) \asymp j\log\log j\log\log\log j$ & §8 item 2) | **Resolved** | Line 171 proves the sharp Selberg upper-bound sieve estimate $\log A(x) \ll x\log\log x/\log x$ (verified step-by-step: $q^a$ with $a \ge 2$ contributes $\le \pi(\sqrt{x})\log x$, $q \le x/\log x$ contributes $\le \theta(x/\log x)$, $q > x/\log x$ gives $\ll \sum_{m<\log x} x/(\varphi(m)\log x) \ll x\log\log x/\log x$) and states explicitly that no matching lower bound is proved. Lines 13 and 181 now write $\ll j\log\log j$. §8 item 2 (line 269) separates $p^k \ge 3^k$ (complete periods) from the finite numerical violation of Corollary B's stride budget ($36 < k \le 3000$) and states the every-index version is neither covered nor disproved. |
| **Major #4** (Theorem G $A(G)$ gap) | **Resolved** | Line 240 applies Lemma D directly to obtain $A(G) = O(\log N/\log\log N) \le \frac{3}{16}\log_p M_0 - 1$. |
| **Major #5** (False $\log D_k = O(k)$ in Theorem G(3)) | **Resolved** | Line 242 replaces $\log D_k = O(k)$ with the airtight 1-line deduction $\Lambda_k \mid b^{\operatorname{ord}_{\Lambda_k} b} - 1 \implies \log \Lambda_k < \operatorname{ord}_{\Lambda_k}(b)\log b \le \operatorname{ord}_{\Lambda_k^r}(b)\log b \le \lambda^{(1-\epsilon)k}\log b$, yielding both $\log D_k = o(\lambda^k)$ and $\log(1/c_{k+1}) = o(\lambda^k)$ (and explicitly noting $\log D_k = O(k)$ is false for the degree-1 schedule). |
| **Minor #6** ($\theta \le 1$, $\eta_0 \le 1/2$ caps) | **Resolved** | Capped at lines 138 ($\eta_0 \le \min(\frac{1}{2}, \frac{rs}{8d})$), 144 ($\theta = \min(1, \frac{d-r-1/2}{rs})$), 166 ($\theta = \min(1, \frac{d\epsilon_1}{2rs})$), and 240 ($\theta \le 1$ for small $\epsilon$). |
| **Minor #7** (Lemma A & C3 notation/slips) | **Resolved** | Summary line 9 includes $p$ odd, $p \nmid c$, $M_0 \ge M_* = p^{\lceil 2/\theta\rceil + 9}$; line 31 states $e, c \in \mathbb Z$; line 49 uses $\max(0, M - hw)$; line 77 fixes $W + n_\theta \kappa$; line 135 writes $p^{rsJ+O_P(1)}M'$; stride renamed to $\tau$ throughout §§1–4, 6 (no clash with $L$); line 184 includes the $2 \mid \Lambda, r \ge 3$ factor-of-$2$ caveat. |
| **Minor #8** (Theorem G & §5 tightening) | **Resolved** | Lemma S renamed **Lemma T** (line 188); line 231 reduces $\deg P \le r$ to $\deg P = r$; line 240 explicitly discards shifts before the first degree-$r$ insertion $n_k + (r-1)n_1 > N^{1-\epsilon}$ (at most $\lambda N^{1-\epsilon} + O(1)$), separates $K_0 = K(n_0)$ from $K = K(N)$, uses $D'_0$, and includes the $\log N$ harmonic-sum factor; line 242 adds the 1-line CRT bound $u_{k_j} \le p\operatorname{rad}(b)\ell_j \implies c_k \le \operatorname{rad}(b)$. |
| **Minor #9** (Theorem S omissions & script check) | **Resolved** | Line 250 adds "strictly increasing" and notes $\log A_b(\ell_{j(K)}) = o(K)$ follows from $A_b \mid \varphi(\Lambda_K) < \Lambda_K$; line 260 states $k \ge k_{l-1} + l \implies J \ge l$ and lower-degree $p$-integrality; line 262 bounds $d > p$ collision multiplicity by $(\log_p m + 1)^d$ and uses $D'_0$; line 264 and `stoneham_all_prime()` report exact $d=5$ defects and add the direct active-window congruence test. |
| **Minor #10** (736 vs. 724 convergents) | **Resolved** | Script tracks `counted = 724` separately from `steps = 736`; lines 244 and 281 match verbatim. |
| **Minor #11** (Scope hygiene / "proposed") | **Resolved** | All four occurrences of "proposed" replaced cleanly (lines 81, 184, 266, 271); zero process language remains. |

### Residual Trivial Observations (Non-blocking)
- **Line 121 (Lemma D proof):** Writes `$\pi(x) - 2 - x^{2/3}\log_2 b \le d(M) x^{2/3}$`, subtracting `2` for the primes dividing $pb$; for composite $b$ the exact count is $\omega(pb) = 1 + \omega(b) \le 1 + \log_2 b$. Since $1 + \omega(b) = O_b(1)$, the subsequent deduction $d(M) \ge x^{1/3}/(2\log x)$ for $x \ge x_0(b)$ is completely unaffected. (Also in line 118, $\log\log\operatorname{ord}_\Lambda b$ implicitly assumes $\operatorname{ord}_\Lambda b \ge 3$, i.e. $\ell_{\max} \ge x_0(b)$.)
- **Line 280 (§9):** Writes `$v_3(2^L - 1) = v_3(2^{2T_Q} - 1) = 1 + v_3(T_Q)$` matching the script's print label (`L = lcm(t, TQ)`), whereas §2 now denotes the stride by $\tau$.

### Updated Sub-Track Verdicts

| Sub-track | Updated Verdict | Notes |
|---|---|---|
| **C3** (Lemma A, Corollary B, Lemma D, Theorem E, Theorem H′) | **Accept** | All 3 C3 Major findings and all C3 Minor findings are cleanly resolved. Lemma D and the Selberg sieve bound are verified and sound (modulo the trivial `- 2` vs `- \omega(pb)` constant in Lemma D line 121, which does not affect the conclusion). |
| **C4** (Lemma T, Prop 5.1, Theorem G, Theorem S, §8) | **Accept** | All 3 C4 Major findings (including shared Major #3) and all C4 Minor findings are cleanly resolved. Theorem G(2)–(3), Theorem S (pole retention transfer + $\mu(W_S) = p$), and all script assertions pass with exact matches. |

*Reminder: Cross-model review is not independent human peer review.*
