# Cross-Provider Adversarial Referee Review — Phase 25 Track D

- **Reviewer:** Gemini 4 Neon (auditing Claude `claude-opus-5-5`)
- **Branch / worktree:** `research/phase-25-carry-correlations`
- **Files audited (read-only):**
  - [`notes/phase25/digit-complexity-and-lp-witnesses.md`](../digit-complexity-and-lp-witnesses.md) (427 lines)
  - [`scripts/phase25_digit_complexity.py`](../../../scripts/phase25_digit_complexity.py) (1,033 lines)
- **Independent script execution:** `python -B scripts/phase25_digit_complexity.py` exited with code `0`, printing `ALL 709 CHECKS PASSED`. All certificate assertions in the script use exact `int` and `fractions.Fraction` arithmetic (pure Python standard library; floating point appears only in the `f6()` display formatter and in the random-generator weights of `D1.2` before exact verification).
- **Reviewer-side auxiliary stress tests** (run in memory via `python -B -c`; no repository files modified or added except this review):
  1. **Exact periodic- and boundary-rational verification of Theorem 1.2:** Built an independent tail-constrained exact DP (`sigma_exact_rational`) supporting arbitrary non-terminating rationals $p/q$, and tested Theorem 1.2(1) ($b = 3,\dots,7$, all $\lfloor b/2\rfloor \le B \le b-2$, $N \le 15$) on all critical boundary points $x \in \{0, \frac{1}{2}, \theta, 1-\theta, \rho, 1-\rho, \frac{1}{b-1}, \frac{1}{b+1}, \frac{b}{b+1}, \frac{k}{b(b-1)}, \frac{\theta}{b}, \frac{1}{7}, \frac{3}{7}, \frac{1}{13}, \frac{5}{12}\}$ — **0 errors**. Tested Theorem 1.2(2)–(3) ($b = 2,\dots,7$, $N \le 12$) on all rationals $p/q$ with $1 \le q \le 32$ (including $0, \frac{1}{2}, \frac{1}{3}, \frac{2}{3}, \frac{1}{6}, \frac{5}{6}, \frac{1}{b+1}, \frac{b}{b+1}, \frac{1}{7}, \frac{3}{7}, \frac{3}{8}, \frac{5}{8}, \frac{9}{16}$) — **0 errors** in $K_{I_b} - 1 \le \sigma_{b-1} \le K_{I_b}$, and exact observed base-2 range $2\sigma_1(x;N) - K_J(x;N) \in [-2, 1]$ (confirming our analytic proof that $|2\sigma_1 - K_J| = 3$ is impossible; **Major M1**).
  2. **Independent exact audit of Theorem 2.6 witness & Theorem 2.5 outward rounding:** Re-decoded the 16,076-bit witness $W$, verified zero ties across all 16,076 orbit points (minimal period $16076$, $0 < \min p < \max p < 2^P - 1$), verified exact $D(W) = 0.059107954113\ldots \le 0.059108$ and ratio $D(W)/(2(\frac{1}{3} - \frac{4887}{16076})) = 1.00729979\ldots$, and checked exact rational rounding directions for every claimed bound in Theorems 2.5–2.6, Summary items 7–8, §2.6, §9–§10, and `section_applications` (**Major M2**).
  3. **Independent SciPy/HiGHS verification of Table 2.2:** Rebuilt and solved both the plain LP and type-augmented LP at $\alpha = 0.304282$ for $L = 4, 6, 8, 10$ via `scipy.optimize.linprog(..., method="highs")`, reproducing `plain = 0.010957, 0.031858, 0.039711, 0.045923` and `aug = 0.016436, 0.047686, 0.055499, 0.057452` (exact $L=8$ value $0.0554985$). Verified the 21-entry affine $L = 4$ primal solution has constant $\arg\max G = \{2,3,4,5,9\}$ and $\arg\min G = \{0,7,11,12,13,14,16\}$ on $[\frac{9}{32}, \frac{5}{16}]$.
  4. **Independent checks of Theorem 1.4, Proposition 3.2, and Section 4 (D4):** Verified the 6-state automaton and step-cost recurrence $(b-3)/b + ((b+3)/b)(1 - (-1/b)^t)/(b+1)$ for $B = b - 1$, $b = 3,\dots,8$; confirmed $(b, B) = (3, 1)$ has 3 states with 2 recurrent states $\{P, Q\}$ ($O$ transient); verified $(0^n 1^n)$ at $n = 1$ gives $\sigma_1$-density $\frac{1}{2} \ne 1/n$; verified `all_debruijn(L)` returns all $2^{2^{L-1}-L} = 2, 16, 2048$ cyclically distinct de Bruijn words for $L = 3, 4, 5$, and verified `random_euler(L)` yields valid order-$L$ de Bruijn words for $L = 2,\dots,10$.
  5. **Prior-art & external-citation verification:** Checked `GF-31`, `GF-36`, `GF-37`, `GF-40` against [`notes/phase23/dense-characters-and-nonfundamental-forms.md`](../phase23/dense-characters-and-nonfundamental-forms.md), [`notes/phase24/dense-digit-mass-and-lambert.md`](../phase24/dense-digit-mass-and-lambert.md), [`notes/phase24/simple-normality-and-word-laws.md`](../phase24/simple-normality-and-word-laws.md), [`notes/phase24/classical-constants-and-joint-numerators.md`](../phase24/classical-constants-and-joint-numerators.md), and [`docs/registry/GF.toml`](../../../docs/registry/GF.toml) (**Major M3**); web-checked all seven external references (**Minor m6**).

> **Scope disclaimer: Cross-model review is not independent human peer review.** This report is an automated cross-provider audit by one AI model (Gemini 4 Neon) reviewing work drafted by another (Claude `claude-opus-5-5`). It does not substitute for refereeing by human mathematicians or formal verification in Lean, and none of its conclusions may be used to change a benchmark status.

## Verdict: **REVISE**

| Severity | Count |
| --- | --- |
| Critical | 0 |
| Major | 3 |
| Minor | 7 |

### Executive Assessment

The core mathematical discoveries of Phase 25 Track D are **genuinely strong and mathematically sound**, with **zero Critical flaws**:

- **Theorem 1.2 (middle-interval orbit formulas)** is true and its proof survives every adversarial boundary and periodic-rational check: exact equality $\sigma_B(x; N) = \#\{0 \le n < N : \|b^n x\| > \frac{B}{b(b-1)}\}$ for $\lfloor b/2\rfloor \le B \le b-2$, and $K_{I_b}(x; N) - 1 \le \sigma_{b-1}(x; N) \le K_{I_b}(x; N)$ for $B = b-1$ (and in fact base 2 satisfies the tighter two-sided bound $-2 \le 2\sigma_1(x; N) - K_J(x; N) \le 1$).
- **Theorem 1.5, Corollary 1.6, and Theorem 1.7** (pattern formula, measure law, sharp $L$-normal interval $[\bar g_L, \bar g_L + 2^{-L}]$ with $\bar g_L = \frac{1}{3} - \frac{1}{3}4^{-\lfloor L/2\rfloor}$, and the order-3 barrier $\bar g_3 = \frac{1}{4}$ attained non-periodically) are sound.
- **Theorems 2.1–2.3 and Lemma 2.4** (type-augmented LP dual certificate, canonical even-$L$ interval certificate, universal inequality $D_N(x; 2) \ge 2|\sigma_1(x; N)/N - \frac{1}{3}| - \frac{3}{N}$ [sharpenable to $-\frac{2}{N}$], and signed-weight transfer) are rigorously proved, improving $D^-(E_+(8); 2)$ from $2.34\times 10^{-7}$ (`GF-40`) to $\ge 0.058103$ ($> 2.48\times 10^5\times$).
- **The 16,076-bit periodic counterexample** in Theorem 2.6 genuinely has cyclic cost $4887$ (density $0.30399353\ldots \le 0.304282$), $K_3 = 4887$, $K_6 = 9774$, minimal period $16076$, and exact discrepancy $D(W) = 0.059107954\ldots \le 0.059108$.
- **Sections 3 and 4 (D3–D4)** — including the carry-aware functional inequalities, Hypothesis (H) counterexample, telescoping trivial-expansion example, 4-line run-parity proof of $(2,2,3,1)$, new obstructions $(2,2,4,1)$ at $m = 16$ and $(2,2,5,2)$ at $m = 32$, closure rules, and all seven complete feasible sets — are mathematically solid.

However, the manuscript requires a targeted revision (`REVISE`) before registration because of **three Major findings**:

1. **M1 (False attainment claim & script/note contradiction):** Line 92 asserts that $|2\sigma_1(x;N) - K_J(x;N)| = 3$ was observed in the script and *"so the constants are attained."* In reality, the script prints `max |2 sigma_1 - K_6| = 2`, and $|2\sigma_1(x;N) - K_J(x;N)| = 3$ is **mathematically impossible** for every $x \in \mathbb{R}$ and every $N \ge 1$ because $-2 \le 2\sigma_1 - K_J \le 1$ universally.
2. **M2 (Systematic wrong-direction rounding across Theorems 2.5–2.6 & Summary):** Using nearest-rounded `f6()` output inside certified inequality statements produces **nine** bounds rounded inward rather than outward — including the headline Theorem 2.6 lower bound $0.058103 \le \Delta(0.304282)$ (false for literal $\alpha = 0.304282$, where $2(\frac{1}{3} - \alpha) = 0.058102\overline{6}$), $D^-(E_+(16); 2) \ge 0.2126$ (exact $0.212574\overline{6}$), $D^-(E_+(8); 2) \ge 0.061211$ (`GF-36` input, exact $0.061210\overline{6}$), four cubic-table entries, and the necessary $E_+(4)$ carry deficit ($0.120753\overline{6}$ rounded up to $0.120754$ / $0.1208$).
3. **M3 (Priority overclaim on $L_-(8)$ omitting `GF-31`):** Summary item 7, Theorem 2.5 (`previous best: none (new)`), and §10 present nonnormality of both $L_+(8)$ and $L_-(8)$ (moduli 7, 9, 13) as entirely new. While **$L_+(8)$ is genuinely new**, **`GF-31` Theorem 4A** already proved $L_-(8)$ is simply nonnormal in base 8 with $D^-(L_-(8); 8) > 0$ (hence nonnormal in base 2 by Maxfield 1953) via Selberg–Delange; what is new for $L_-(8)$ here is the elementary Selberg–Delange-free proof, the explicit base-2 $D^-$ lower bounds, and base-2 4-nonnormality.

All three Major findings and the seven Minor polishes have direct, surgical fixes that leave the core theorems intact (and even strengthen Theorem 1.2(3) and Theorem 2.3).

---

## Section-by-Section Adversarial Audit

### 1. Script Execution and Exact-Arithmetic Discipline

Running `python -B scripts/phase25_digit_complexity.py` from the worktree root exited with status `0` and printed `ALL 709 CHECKS PASSED`. Every certificate assertion uses `int` or `fractions.Fraction`; floating point is restricted to `f6()` formatting and the random-trial generator weights in `D1.2` (`rng.random() ** 3`) prior to exact verification.

**Discrepancies between script output and note:**
- **D1.2 (`max |2 sigma_1 - K_6|`):** Script prints `2 (proved <= 3)`; note line 92 falsely reports `3` and claims attainment (**Major M1**).
- **D2.4 (`WITNESS_DMAX` vs `0.059108`):** Script asserts `D <= Fr(5911, 100000)` (`0.05911`) and prints `exact D(W) = 0.059108...`; note lines 22, 277 claim `<= 0.059108` while line 280 writes `0.059108... <= 0.05911`. Exact evaluation gives $D(W) = 0.059107954113\ldots \le 0.059108$, so the bound $0.059108$ is true, but the script does not assert it and `0.059108...` is misleading (**Major M2**, **Minor m7**).
- **D2.5 (`f6()` nearest rounding):** Nine printed/tabulated bounds round in the non-conservative direction (**Major M2**). Also line 793 asserts `> 2e5` while note lines 21, 409 cite `> 2.4e5` (true: $248{,}304.8$), and line 795 asserts `> 4 * 0.0459` while its message reads `> 4.5x GF-36` (true: $4.58\times$) (**Minor m7**).

### 2. D1: Carry Range, Orbit Formulas, Exact Laws, and Sharp $L$-Normal Bounds (§1, Lines 62–174)

- **Lemma 1.1 (lines 66–68) — Verified (Minor m1):**
  - The carry relation $a'_i = d_i + b\delta_{i-1} - \delta_i$ and tail relation $\{x\} - \sum_{i \le N} a_i b^{-i} \equiv b^{-N}(t_N + \delta_N) \pmod 1$ are sign-exact. Since $2B + 1 \ge b$, $[-\rho, \rho]$ with $\rho = B/(b-1) \ge 1/2$ is filled by $[-B, B]$-digit tails, and every $\delta_0 \in C(b, B)$ yields an admissible sequence mod $\mathbb{Z}$.
  - **Minor m1 (line 68):** Excluding $\delta_i = -2$ for $B \le b-2$ uses $(B+b-1)/(b-1) < 2$, not `> 1`.
- **Theorem 1.2 (lines 72–92) — Core proofs verified; Line 92 FALSE (Major M1, Minor m2):**
  - **Part (1) ($\lfloor b/2\rfloor \le B \le b-2$, $\theta = B/(b(b-1))$):** Completely airtight, including every boundary point $\|b^n x\| = \theta$ (e.g. $x = 1/6, 5/6$ at $b = 3, B = 1$). Because $\rho \ge 1/2$, whenever $|y_n| > \theta$ we have $|b y_n| > \rho \ge 1/2$, so the nearest integer to $b y_n$ clipped to $[-B, B]$ is **never zero** (regardless of half-integer tie-breaking). When $|y_n| > 1/2$, $\|b^n x\| = 1 - |y_n| \ge 1 - \rho = \frac{b-1-B}{b-1} \ge \frac{1}{b-1} > \theta$, so $|y_n| \le \theta \iff \|b^n x\| \le \theta$ holds unconditionally. Independently confirmed with 0 errors on all boundary/periodic rationals for $b = 3,\dots,7$.
  - **Part (2) ($B = b-1$, $I_b = [\frac{1}{b+1}, \frac{b}{b+1})$):** Both the charging lower bound and the half-open window upper bound are completely airtight, including $t_n = \frac{1}{2}$ in base 2 (where both $r_n = \pm\frac{1}{2}$ map to $r_{n+1} = \pm 1 \implies t_{n+1} = 0 \notin I_2$ and $|r_{n+1}| = 1 > \frac{1}{2} \implies a'_{n+2} \ne 0$) and the boundary orbit $\{\frac{1}{b+1}, \frac{b}{b+1}\}$. Independently confirmed on all $p/q$ ($q \le 32$, $b = 2,\dots,7$). See **Minor m2** on the phrasing *"exclude the boundary orbit"* (line 88).
  - **Part (3) (base 2, $J = [\frac{1}{6}, \frac{5}{6})$) & Major M1 (line 92):** The preimage identity $T_2^{-1}(I_2) = [\frac{1}{6}, \frac{1}{3}) \sqcup [\frac{2}{3}, \frac{5}{6}) = J \setminus I_2$ holds at every endpoint ($1/6, 1/3, 2/3, 5/6$), giving the exact identity
    $$2\sigma_1(x; N) - K_J(x; N) = 2\bigl(\sigma_1(x; N) - K_{I_2}(x; N)\bigr) + [t_0 \in I_2] - [t_N \in I_2].$$
    However, in the charging proof of Part (2), $\sigma_1(x; N) = K_{I_2}(x; N) - 1$ can occur **only** if the charging map hits position $N+1$, which requires $t_{N-1} \in I_2$ and $a'_N = 0$, which forces $r_N = 2r_{N-1} \in [\frac{2}{3}, 1] \cup [-1, -\frac{2}{3})$ and hence **$t_N \notin I_2$** (so $[t_N \in I_2] = 0$)! Therefore:
    - when $\sigma_1 = K_{I_2}$: $2\sigma_1 - K_J = [t_0 \in I_2] - [t_N \in I_2] \in \{-1, 0, +1\}$;
    - when $\sigma_1 = K_{I_2} - 1$: $2\sigma_1 - K_J = -2 + [t_0 \in I_2] \in \{-2, -1\}$.
    Thus **$-2 \le 2\sigma_1(x; N) - K_J(x; N) \le 1$ for every $x \in \mathbb{R}$ and every $N \ge 1$** (attained at $-2$ by $x = 1/4, N = 2$ and at $+1$ by $x = 1/2, N = 2$). Consequently, line 92's claim that $|2\sigma_1 - K_J| = 3$ was observed and attained is **mathematically false** and contradicts the script output (`max |2 sigma_1 - K_6| = 2`).
- **Corollary 1.3 & Theorem 1.4 (lines 96–120) — Verified:**
  - Open interval $(\theta, 1-\theta)$ vs half-open $D_N$: for any finite orbit $\{t_n : n < N\}$, taking $[\theta + \varepsilon, 1-\theta)$ and letting $\varepsilon \downarrow 0$ yields $|F_N((\theta, 1-\theta)) - (1 - 2\theta)| \le D_N(x; b)$ with no boundary loss.
  - Theorem 1.4: Checked the exact 3-state transitions for $B \le b-2$ (from $P$, digits $0, B, b-1$ map into $\{P, Q\}$, giving $\Pr(P \to \{P, Q\}) = 3/b$ and $s_{t+1} = (1 - s_t)\frac{2}{b} + s_t\frac{3}{b} = \frac{2}{b} + \frac{s_t}{b}$, with expected cost $(2b-3-B)/b$; note also $(b, B) = (3, 1)$ has $O$ transient and 2 recurrent states $\{P, Q\}$, validating line 106's "$b \ge 4$"). Independently confirmed the 6-state automaton and step-cost recurrence for $B = b - 1$ through $b = 8$.
- **Theorem 1.5 & Corollary 1.6 (lines 124–148) — Verified (Minor m3):**
  - Induced state invariant on $T_4$ (mapping $(w_k, \mathrm{type}(0w_1\cdots w_k)) \in \{0,1\} \times \{0, 1, \bot\}$ to $\{A, B, C, D\}$ with $\{1, \bot\}$ merged) rigorously proves Theorem 1.5.
  - Corollary 1.6 holds even on the atomic alternating orbit $\nu = \frac{1}{2}\delta_{1/3} + \frac{1}{2}\delta_{2/3}$ (all four expressions equal $\frac{1}{2}$). However, the Markov closed form $\frac{ac(2-a-c)}{(a+c)(1-ac)}$ hits $0/0$ at the ergodic point $(a, c) = (1, 1)$ (and divides by $0$ at $(0, 0)$), $\mathrm{cost}(\nu)$ is defined only for ergodic $\nu$ in §0, and line 146's appeal to $\nu[01] = \nu[10]$ should be replaced by the uniform tail bound $\frac{1}{N}\#\{j > J \text{ occurrences}\} \le \frac{1}{2J+2}$ (**Minor m3**).
- **Theorem 1.7 (lines 152–169) — Verified (Minor m4):**
  - Checked $g_L$, $\bar g_L = \frac{1}{3} - \frac{1}{3} 4^{-\lfloor L/2\rfloor}$, and $\frac{1}{2}|\mathrm{inner}_L(J)| = \bar g_L$, $\frac{1}{2}|\mathrm{outer}_L(J)| = \bar g_L + 2^{-L}$ for both even and odd $L \ge 1$ (including $L = 1$ where $\bar g_1 = 0$, $\bar g_1 + \frac{1}{2} = \frac{1}{2}$).
  - Checked the pointwise identity $\mathrm{cost}(S_t, d_{t+1}) = g_L(d_{t-L+2}\cdots d_{t+1}) + [d_{t-L+2}\cdots d_{t+1} = w^*_L][S_t = D]$ for $t \ge L-1$, $L \ge 2$: every word containing a doubled pair synchronizes $T_4$ to a singleton, leaving only the two alternating prefixes, and only the one ending in `1` followed by `1` ($w^*_L$) has cost ambiguity ($B \xrightarrow{1} 0$ vs $D \xrightarrow{1} 1$). Hence every order-$L$ de Bruijn word has cyclic cost in $\{2^L \bar g_L, 2^L \bar g_L + 1\}$.
  - Checked $L \in \{2, 3\}$: every 2-normal periodic word of length $P$ has $\#_{10}^{\rm cyc} = P/4$ and contains both `00` and `11`, forcing at least one cyclic $0 \to 1$ type change and cost $\ge P/4 + 1$. Meanwhile $B_n = (0001)^n(1110)^n$ has exact cyclic cost $2n$ (density $1/4$) and cyclic 3-block counts $n \pm 1$ (max deviation $\frac{1}{8n} \le \frac{1}{4n}$). Concatenating $B_1 B_2 B_3 \cdots$ ($n = 1, 2, 3, \dots$) has single-block length $8n = o(4n^2) = o(N)$, yielding an explicit **3-normal** real $x$ with $\sigma_1(x; N)/N \to \frac{1}{4} = \bar g_3$. This rigorously proves that **order-3 normality cannot be ruled out by $\limsup \sigma_1/N \le 0.304282$ alone**! (See **Minor m4** on specifying slow block growth $n = 1, 2, 3, \dots$ rather than arbitrary $n \to \infty$.)

### 3. D2: Exact LP Certificates, Universal Inequality, Applications, and 16,076-Bit Witness (§2, Lines 177–285)

- **Theorem 2.1 (lines 190–206) — Verified:** Every sign, index, and boundary term checks out: $\sum_j \rho_j G_j^{(N)} = \sum_w f_N(w) h(w) - K \le D_N(x; 2)$ (via $\rho = \rho^+ - \rho^-$ with mass $\le 1$), $\tau_{n+1} = T(\tau_n, d_{n+1}, d_{n+2})$ matches the last doubled pair in $0d_1\cdots d_{n+2}$ (with type $1$ if none), and $\sum_{n < N} \kappa(\tau_n, W_n) = \sigma_{\rm free}(d_1\cdots d_{N+1}) \le \sigma_1(x; N+1) \le \sigma_1(x; N) + 1$. The plain-LP remark (line 206) with $(\sigma_1 + L - 1)/N$ is also exact.
- **Theorem 2.2 (lines 210–228) — Verified (Minor m5):** For $\rho = \delta_{j_\beta} - \delta_{j_\gamma}$, $h(w) = -[w \in I_L]$, $K = -|I_L| = -2\bar g_L$, and every cycle in the type-augmented graph has weight $2\,\mathrm{cost}(W) - \#\{\text{windows in } I_L\} \ge 0$ (checked explicitly for the exceptional cycles $0^\infty, 1^\infty$, and $(01)^\infty$ under both $\tau = 0, 1$, where weight $= 2(1) - 2 = 0$). Our independent HiGHS run reproduced Table 2.2 verbatim for $L = 4, 6, 8, 10$ (noting $L = 8$ exact value is $0.0554985$). For $L = 4$, our exact check confirmed that the 21-entry primal attains $D_{\rm grid}(\alpha) = 2(\frac{5}{16} - \alpha)$ with constant argmax/argmin across $[\frac{9}{32}, \frac{5}{16}]$ (see **Minor m5** on stating convexity + dual lower bound).
- **Theorem 2.3 & Lemma 2.4 (lines 231–254) — Verified (Minor m5):** All three $\liminf$/$\limsup$ corollaries of Theorem 2.3 follow validly from $D_N(x; 2) \ge 2|\sigma_1(x; N)/N - \frac{1}{3}| - \frac{3}{N}$ (which improves to $-\frac{2}{N}$ under **M1**). Lemma 2.4's NAF tail split $|2^{-kH} S_{\rm lo}| < \frac{2}{3}$, series tail $< \frac{1}{3}$, and monotonicity for $N \not\equiv 0 \pmod k$ are completely rigorous (tiny typo `2/3 + 1/3 < 1` $\to$ `= 1`, and state $A \ge 0$; **Minor m5**).
- **Theorem 2.5 & Theorem 2.6 (lines 257–285) — Core logic verified; Major M2 (rounding) & Major M3 ($L_-(8)$ priority):**
  - Cross-radix descent (`GF-36` Prop. 2.4(5), $\frac{3}{7} \cdot 0.058103 > 0.0249$) and `GF-37` Thm. 4.1(1) (2-normal in base 8 $\implies$ 4-normal in base 2, so $\alpha < \frac{5}{16} = \bar g_4$ rules out 4-normality in base 2 and 2-normality in base 8) are valid.
  - The 16,076-bit witness $W$ was independently verified: no orbit ties, exact extreme discrepancy formula $D_P = \frac{1}{P} + \max_i(\frac{i}{P} - x_i) - \min_i(\frac{i}{P} - x_i)$ is exact (since $0 < x_1 < \dots < x_P < 1$ forces $\max(\frac{i}{P} - x_i) \ge 1 - x_P > 0$ and $\min(\frac{i-1}{P} - x_i) \le -x_1 < 0$), $D(W) = 0.059107954113\ldots \le 0.059108$, density $4887/16076 = 0.30399353\ldots \le 0.304282$, and $D_N(x_W; 2) \to D(W)$ along all $N$.
  - **Major M2** and **Major M3** affect the rounded decimals in Theorems 2.5–2.6 and the priority claim on $L_-(8)$ (itemized below).

### 4. D3: Carry-Aware Functionals (§3, Lines 288–317) — Verified (Minor m5)

- **Theorem 3.1:** Every inequality $(\mathrm{tr}-1)/2 \le \#_{10} \le \sigma_{\rm free} \le \min(\mathrm{tr}, \#_0, \#_1)$ is proved cleanly. Crucial edge check passed: when an occurrence of $00(10)^j 11$ in $0w$ uses the virtual leading `0`, its closing `011` (and hence `01`) still lies wholly inside $w$, and a leading `0`-run of length $z_1 \ge 1$ is not preceded by `10`, so it contributes at most $1 \le z_1$.
- **Proposition 3.2:** Verified all rows, except `$(0^n 1^n)$` requires **$n \ge 2$** because at $n = 1$, $(01)$ has $\sigma_1$-density $\frac{1}{2} \ne 1/n$ (**Minor m5**).
- **Proposition 3.3:** Completely sound (require $x \in (0, 1)$ so $x = \sum_j 2^{-m_j}$; **Minor m5**).
- **Proposition 3.4:** Telescoping sum $\sum_{n \le M}((2^k-1)n - 1)2^{-kn} = 1 - (M+1)2^{-kM} \to 1$ is exact. Crucial adversarial check on unboundedness: for $A = \frac{4^r - 1}{3} + Q \cdot 2^{2r}$, the bottom $2r$ NAF digits are $(+1, 0)^r$ for **every** $Q \in \mathbb{Z}$ (at bit $2r - 2$, $1 + 4Q \equiv 1 \pmod 4$ independent of $Q$), forcing $w_\pm(A) \ge r$. Airtight!
- **Line 316 remark:** In base 2, Phase 23's $\chi_N(x) = \mathrm{tr}(d_1\cdots d_{N+1})$ differs from $\mathrm{tr}_N(x)$ by $[d_N \ne d_{N+1}] \in \{0, 1\}$ (**Minor m5**).

### 5. D4: Multi-Radix Compatibility (§4, Lines 320–345) — Verified (Minor m5)

- **Proposition 4.1:** Both directions are rigorously justified by `HigherOrderTower.mem_pow_kernel_decomp` and `wordFreq_tower_limit` (`GF-29`/`GF-37`); $L_1, L_2 \ge 1$ automatically excludes $F_{b^k} \supseteq F_b$.
- **Proposition 4.2:** Repetition closure (a) and phased-Euler splicing (b) are exact (verified both analytically and via `section_multiradix`'s explicit splice at `m = 24 + 16 = 40`). In (c), Sylvester's Frobenius bound $(a-1)(d-1) < ad$ gives $F \supseteq \ell\mathbb{N} \cap [sm_1/\ell, \infty)$ whenever $\gcd(m_1/\ell, s/\ell) = 1$. Fix notation `$m_0 + s\mathbb{N}$` $\to$ `$m_0 + s\mathbb{Z}_{\ge 0}$` since $\mathbb{N} = \mathbb{Z}_{\ge 1}$ throughout §4 (**Minor m5**).
- **Proposition 4.3:** The 4-line run-parity proof of $8 \notin F(2, 2, 3, 1)$ is completely rigorous and self-contained (every order-3 de Bruijn word has unique `0`-runs of lengths 3 and 1 and `1`-runs of lengths 3 and 1, all odd, forcing both `0`-run starts and hence both `10` starts to share the same parity, contradicting base-4 uniformity at even positions).
- **Table 4.4:** All seven complete feasible sets follow rigorously from the exact exhaustive de Bruijn enumerations (`0/2`, `0/16`, `256/2048`, `0/2048`, independently verified to cover all $2^{2^{L-1}-L}$ cyclic de Bruijn sequences), the six exact witnesses (`24, 48, 96, 64, 64, 64`), and Proposition 4.2.

### 6. Research-Note Checklist (10 Standard Elements, Evidence Labels, Citations)

| # | Standard Element | Status | Audit Notes |
| --- | --- | --- | --- |
| 1 | Definitions & notation | Present (lines 30–58) | Clean; define $\mathrm{cost}(\nu)$ for non-ergodic $\nu$ (**m3**) and distinguish $\mathbb{N}$ vs $\mathbb{Z}_{\ge 0}$ in §4 (**m5**). |
| 2 | Summary of results, evidence labels, standing objectives | Present (lines 5, 11–26, 365–371, 405–410) | Disciplined label separation; fix rounded decimals (**M2**), $L_-(8)$ novelty claim (**M3**), and line 92 (**M1**). |
| 3 | Complete statements & self-contained proofs | Present (lines 62–345) | All main proofs sound; fix **M1**, **M2**, and localized slips **m1–m5**. |
| 4 | Prior-art & attribution notes | Present (lines 171–174, 416–427) | Fix `GF-31` omission on $L_-(8)$ (**M3**), `S. Arno`, Dajani–Kraaikamp–Liardet pages `87–112` (**m6**), and add Rule 5 provisional-priority note (**m7**). |
| 5 | External & repository inputs hypothesis-verified | Present (lines 348–361) | Thorough table; add Birkhoff / ergodic decomposition (Cor. 1.6) (**m3**, **m7**). |
| 6 | Conditional statements marked | Present (line 361) | Explicitly notes no conditional hypothesis is used (verified). |
| 7 | Reproduction instructions & finite certificate summary | Present (lines 375–393) | Exact command, exit 0, 709 checks; tighten script checks/formatter (**M2**, **m7**). |
| 8 | Strict separation of finite measurements / numerics | Present (lines 220, 369–370) | HiGHS LP values cleanly labeled *Numerical* (discovery only); no finite digit statistics used. |
| 9 | Explicit open questions & benchmark boundary | Present (lines 7, 395–403, 412–414) | Seven sharp open questions; confirms `BC-01`…`BC-50` unchanged and no registry/benchmark edits. |
| 10 | Cross-model review disclaimer | Present (line 5) | Explicitly states cross-model review is not independent human peer review. |

---

## Itemized Findings

### Critical

None.

### Major

1. **M1 — Mathematically false attainment claim and direct script/note contradiction on $|2\sigma_1(x; N) - K_J(x; N)| = 3$ ([`notes/phase25/digit-complexity-and-lp-witnesses.md:92`](../digit-complexity-and-lp-witnesses.md#L92), [`scripts/phase25_digit_complexity.py:275`](../../../scripts/phase25_digit_complexity.py#L275)):**
   - *Issue:* Line 92 states: *"the observed maxima are $K_I - \sigma = 1$ and $\lvert 2\sigma_1 - K_J\rvert = 3$, so the constants are attained."* First, the companion script actually prints `max |2 sigma_1 - K_6| = 2 (proved <= 3)`. Second, $|2\sigma_1(x; N) - K_J(x; N)| = 3$ is **mathematically impossible** for every $x \in \mathbb{R}$ and every $N \ge 1$: from $2\sigma_1 - K_J = 2(\sigma_1 - K_{I_2}) + [t_0 \in I_2] - [t_N \in I_2]$ and the charging proof of Theorem 1.2(2) (line 87), $\sigma_1(x; N) = K_{I_2}(x; N) - 1$ occurs only when $t_{N-1} \in I_2$ and $a'_N = 0$, which forces $t_N \notin I_2$ ($[t_N \in I_2] = 0$). Hence **$-2 \le 2\sigma_1(x; N) - K_J(x; N) \le 1$** always (with $-2$ attained e.g. at $x = 1/4, N = 2$ and $+1$ at $x = 1/2, N = 2$).
   - *Fix:* Add the 2-line proof of $-2 \le 2\sigma_1(x; N) - K_J(x; N) \le 1$ (hence $|2\sigma_1 - K_J| \le 2$) to Theorem 1.2(3) (and tighten Theorem 2.3's error term from $-3/N$ to $-2/N$, updating Summary items 1 and 6 and line 275 of the script), and update line 92 to report the actual observed maximum `2` (which IS attained!).

2. **M2 — Wrong-direction (nearest instead of outward) rounding invalidating nine stated certified inequalities ([`notes/phase25/digit-complexity-and-lp-witnesses.md:21-22,262-268,277,280,284,401,409`](../digit-complexity-and-lp-witnesses.md#L21-L22), [`scripts/phase25_digit_complexity.py:38-39,751,788-790,801-802,986`](../../../scripts/phase25_digit_complexity.py#L38-L39)):**
   - *Issue:* The script formats rational bounds via round-to-nearest `f6(q) = "%.6f" % float(q)`, and those values are stated as rigorous inequalities in the note, breaking outward rounding in nine places:
     - **Theorem 2.6 & Summary item 8 (lines 22, 277; script line 802):** For literal $\alpha = 0.304282$, $2(\frac{1}{3} - 0.304282) = \frac{43577}{750000} = 0.058102666\ldots < 0.058103$, so $0.058103 \le \Delta(0.304282)$ does not follow from Theorem 2.3 (unlike $E_+(8)$ with $W_+ \le 0.912845$, where $\alpha = W_+/3 = 0.304281\overline{6}$ gives $0.058103\overline{3} > 0.058103$). Also, while exact $D(W) = 0.059107954113\ldots \le 0.059108$ is true, the script only asserts `D <= Fr(5911, 100000)` (`0.05911`) and line 280 misleadingly writes `0.059108... <= 0.05911`.
     - **Theorem 2.5, Summary item 7, & §10 (lines 21, 262–268, 409; script lines 788–790):**
       - $E_+(8)$ (`GF-36`): exact $D^- \ge 0.061210\overline{6}$ (lines 21, 262 claim `0.061211` $\to$ `0.061210`).
       - $E_+(16)$ (`GF-36`): exact $D^- \ge 0.212574\overline{6}$ (line 263 claims `0.212575` $\to$ `0.212574`; lines 21, 409 claim `0.2126` $\to$ `0.2125`).
       - $E_+(16)$ (`GF-40`, script output): exact $\alpha = 0.22821125$ (script prints `<= 0.228211` $\to$ `0.228212`).
       - $L_\pm(8)$ mod 9: exact $D^- \ge 0.130322\overline{6}$ (line 266 claims `0.130323` $\to$ `0.130322`).
       - $L_\pm(16)$ mod 7: exact $\alpha = 0.18922625$ (line 268 claims `0.189226` $\to$ `0.189227`).
       - $L_\pm(16)$ mod 9: exact $D^- \ge 0.264408\overline{6}$ (line 268 claims `0.264409` $\to$ `0.264408`).
       - $L_\pm(16)$ mod 13: exact $\alpha = 0.1973285$ (line 268 claims `0.197328` $\to$ `0.197329`) and exact $D^- \ge 0.272009\overline{6}$ (line 268 claims `0.272010` $\to$ `0.272009`).
     - **$E_+(4)$ necessary carry-cancellation deficit (lines 284, 401; script line 801):** Exact $W_{\rm lo}/2 - \frac{1}{3} = 0.120753\overline{6}$; rounding up to `0.120754` / `0.1208` overstates the proved necessary deficit (must be `0.120753` / `0.1207`).
   - *Fix:* Replace `f6()` with exact outward-rounding helpers (floor for lower bounds / necessary deficits, ceiling for upper bounds) in `scripts/phase25_digit_complexity.py`, tighten `WITNESS_DMAX` to `Fr(59108, 10**6)` (writing `0.05910795... <= 0.059108` in line 280), fix all nine bounds above (and in Theorem 2.6 either write $0.058102 \le \Delta(0.304282) \le 0.059108$ or state Theorem 2.6 at $\alpha = 0.912845/3$ where $0.058103 \le \Delta(\alpha) \le 0.059108$ holds).

3. **M3 — Priority / novelty overclaim on $L_-(8)$ overlooking `GF-31` Theorem 4A ([`notes/phase25/digit-complexity-and-lp-witnesses.md:21,265-267,270,408`](../digit-complexity-and-lp-witnesses.md#L21)):**
   - *Issue:* Summary item 7 (line 21), Theorem 2.5 (lines 265–267: `"previous best: none (new)"`), and §10 (line 408: `"new nonnormality of L_±(8)"`) claim nonnormality of both $L_+(8)$ and $L_-(8)$ (moduli 7, 9, 13) in base 2 as new. In fact, **`GF-31` Theorem 4A** ([`notes/phase23/dense-characters-and-nonfundamental-forms.md:5,116-140`](../phase23/dense-characters-and-nonfundamental-forms.md#L5)) already established simple nonnormality and $D^-(L_-(8); 8) > 0$ for **$L_-(8)$** (moduli 7, 9, 13), which already implies base-2 nonnormality via Maxfield (1953) (and `GF-36` Prop. 8.1 noted that `GF-31`'s Selberg–Delange factor $2/3$ also brings $L_-(8)$ under the transition route). Only **$L_+(8)$** is newly proved nonnormal; for $L_-(8)$, the new contributions are the elementary proof without Selberg–Delange, explicit base-2 lower bounds $D^-(L_-(8); 2) \ge 0.162063, 0.130322, 0.140457$, and base-2 4-nonnormality.
   - *Fix:* Distinguish $L_+(8)$ (genuinely new nonnormality, $D^- > 0$, not 4-normal) from $L_-(8)$ (previously proved base-8 simply nonnormal with $D^-(\cdot; 8) > 0$ in `GF-31` using Selberg–Delange; here newly given an elementary proof, explicit base-2 $D^-$ bounds, and base-2 4-nonnormality) in Summary item 7, Theorem 2.5, §2.5(c), and §10, and add `GF-31` to the §5 table.

### Minor

1. **m1 — Wrong inequality in Lemma 1.1 carry-range proof ([`notes/phase25/digit-complexity-and-lp-witnesses.md:68`](../digit-complexity-and-lp-witnesses.md#L68)):**
   - *Issue:* Writes `$(B+b-1)/(b-1) > 1$` instead of `$(B+b-1)/(b-1) < 2$` to exclude $\delta_i = -2$ when $B \le b-2$.
   - *Fix:* Replace `$(B+b-1)/(b-1) > 1$` with `$(B+b-1)/(b-1) < 2$`.

2. **m2 — Boundary-orbit wording in Theorem 1.2(2) proof ([`notes/phase25/digit-complexity-and-lp-witnesses.md:88`](../digit-complexity-and-lp-witnesses.md#L88)):**
   - *Issue:* Writes *"(the half-open conventions exclude the boundary orbit $\{\tfrac{1}{b+1}, \tfrac{b}{b+1}\}$ consistently)"*, whereas $\frac{1}{b+1} \in I_b$ is included and $\frac{b}{b+1} \notin I_b$ is excluded.
   - *Fix:* Reword to *"(the half-open conventions classify the boundary orbit $\{\frac{1}{b+1}, \frac{b}{b+1}\}$ consistently: $\frac{1}{b+1} \in I_b$ and $\frac{b}{b+1} \notin I_b$)"*.

3. **m3 — Degenerate Markov endpoints, non-ergodic $\mathrm{cost}(\nu)$ definition, and proof wording in Corollary 1.6 ([`notes/phase25/digit-complexity-and-lp-witnesses.md:58,134-146`](../digit-complexity-and-lp-witnesses.md#L58)):**
   - *Issue:* The Markov formula $\frac{ac(2-a-c)}{(a+c)(1-ac)}$ is $0/0$ at the ergodic point $(a, c) = (1, 1)$ (where true cost $= \frac{1}{2}$) and undefined at $(a, c) = (0, 0)$. In §0 line 58, $\mathrm{cost}(\nu)$ is defined only for ergodic $\nu$. In line 146, *"and $\nu[01] = \nu[10]$"* is unnecessary and obscures the tail-truncation justification for summing over all $j \ge 0$.
   - *Fix:* Specify $0 < a + c < 2$ in the Markov formula (noting cost $= \frac{1}{2}$ at $a = c = 1$); define $\mathrm{cost}(\nu) = \lim_N N^{-1}\int \sigma_1(x; N)\, d\nu$ in §0; replace *"and $\nu[01] = \nu[10]$"* with the uniform tail bound $\frac{1}{N}\#\{j > J\text{ occurrences}\} \le \frac{1}{2J+2}$ (and note Birkhoff's ergodic theorem / ergodic decomposition in §5).

4. **m4 — Block-growth schedule in Theorem 1.7(4) and explicit order-3 barrier remark ([`notes/phase25/digit-complexity-and-lp-witnesses.md:160,284`](../digit-complexity-and-lp-witnesses.md#L160)):**
   - *Issue:* Line 160 writes *"concatenating these blocks with $n \to \infty$"*, which fails 3-normality (even 1-normality) along mid-block prefixes if $n$ grows exponentially (e.g. $n_k = 2^k$).
   - *Fix:* Specify concatenating $B_1 B_2 B_3 \cdots$ for $n = 1, 2, 3, \dots$ (so block length $8n = o(N)$, and similarly $0^1 1^1 0^2 1^2 \cdots$ for $L = 1$). Also add one sentence in §2.6 noting that since $\bar g_3 = \frac{1}{4} < 0.304282$ is attained by this 3-normal real, order-3 normality of $E_+(8)$ and $L_\pm(8)$ cannot be ruled out from $\limsup \sigma_1/N \le \alpha$ alone.

5. **m5 — Localized hypothesis/notation slips in Lemma 2.4, Theorem 2.2, Propositions 3.2–3.3, §3 remark, and Proposition 4.2(c) ([`notes/phase25/digit-complexity-and-lp-witnesses.md:218,245,253,307,312,316,322,328`](../digit-complexity-and-lp-witnesses.md#L218)):**
   - Line 218 (Thm. 2.2 proof): note that $D_{\rm grid}(\alpha)$ is *convex* in $\alpha$ (so endpoint equality + dual lower bound forces equality on $[\frac{9}{32}, \frac{5}{16}]$, or note constant argmax $j=3$ / argmin $j=0$).
   - Lines 245, 253 (Lemma 2.4): state $A \ge 0$ (and $C > 0$), and correct `$\lvert r\rvert < \tfrac23 + \tfrac13 < 1$` $\to$ `$\lvert r\rvert < \tfrac23 + \tfrac13 = 1$`.
   - Line 307 (Prop. 3.2): specify $n \ge 2$ for `$(0^n 1^n)$` (at $n = 1$, $\sigma_1$-density is $\frac{1}{2} \ne 1/n$).
   - Line 312 (Prop. 3.3): specify $x \in (0, 1)$ so $x = \sum_j 2^{-m_j}$.
   - Line 316 (§3 remark): clarify that Phase 23's $\chi_N(x) = \mathrm{tr}(d_1\cdots d_{N+1})$ equals $\mathrm{tr}_N(x)$ up to $[d_N \ne d_{N+1}] \in \{0, 1\}$.
   - Lines 322, 328 (§4 / Prop. 4.2(c)): explicitly state $b \ge 2, k \ge 2, L_1, L_2 \ge 1$, and write `$m_0 + s\mathbb{Z}_{\ge 0}$` instead of `$m_0 + s\mathbb{N}$` (since $\mathbb{N} = \mathbb{Z}_{\ge 1}$ in line 322 and Table 4.4).

6. **m6 — External bibliographic errors ([`notes/phase25/digit-complexity-and-lp-witnesses.md:420,423`](../digit-complexity-and-lp-witnesses.md#L420)):**
   - Line 420: `J. Arno, F. S. Wheeler` $\to$ **S. Arno, F. S. Wheeler** (Steven Arno and Ferrell S. Wheeler, *IEEE Trans. Computers* 42 (1993) 1007–1010).
   - Line 423: Dajani–Kraaikamp–Liardet, *Discrete Contin. Dyn. Syst.* 15 (2006): pages are **87–112**, not `87–119`.
   - (All five remaining external references — Borel 1909, Clark–Liang 1973, de Bruijn 1946, Maxfield 1953, Reitwiesner 1960 — checked accurate against published sources.)

7. **m7 — Script test coverage, assertion-message alignment, and Rule 5 disclosure ([`scripts/phase25_digit_complexity.py:229-277,793,795`](../../../scripts/phase25_digit_complexity.py#L229-L277), [`notes/phase25/digit-complexity-and-lp-witnesses.md:173,225`](../digit-complexity-and-lp-witnesses.md#L173)):**
   - In `D1.2` (`section_orbit_formulas`), add a deterministic test suite over exact periodic/boundary rationals ($x = \theta, 1-\theta, \frac{1}{b+1}, \frac{b}{b+1}, \frac{1}{3}, \frac{2}{3}, \frac{1}{6}, \frac{5}{6}, \frac{1}{2}$) and assert `-2 <= 2*s - K6 <= 1`, since finite $b$-adic rationals never hit those critical endpoints.
   - Align `section_applications` lines 793 (`> 24 * 10**4` to match `> 2.4e5`) and 795 (`> Fr(9, 2) * Fr(459, 10000)` to match `> 4.5x GF-36`).
   - Add an explicit provisional-priority sentence in §1.6 per [`docs/research-objectives.md`](../../../docs/research-objectives.md) Rule 5, and note in Table 2.2 (line 225) that the exact value at $L = 8$ is `0.0554985` (explaining the last-digit difference between round-half-to-even `0.055498` and HiGHS `0.055499`).

---

## Summary Verdict

**REVISE** (0 Critical, 3 Major, 7 Minor).

Every main theorem and proof in Phase 25 Track D — the middle-interval orbit formulas, the sharp $L$-normal cost law, the type-augmented LP dual certificates, the universal discrepancy inequality, the $> 2.4\times 10^5\times$ improvement on $D^-(E_+(8); 2)$, the 16,076-bit periodic optimality witness, the carry-aware functional bounds, and the multi-radix compatibility table and parity proof — is mathematically sound. Resolving **M1** (fixing line 92 and tightening $|2\sigma_1 - K_J| \le 2$), **M2** (enforcing outward rounding across Theorems 2.5–2.6, Summary, §2.6, §9–§10, and the script), **M3** (separating new $L_+(8)$ from `GF-31`'s $L_-(8)$), and the seven Minor items **m1–m7** will bring the note and companion script to full publication and registration standard.

**Cross-model review is not independent human peer review.**

---

## Post-Repair Verification

- **Reviewer:** Gemini 4 Neon (post-repair re-audit of [`notes/phase25/digit-complexity-and-lp-witnesses.md`](../digit-complexity-and-lp-witnesses.md) and [`scripts/phase25_digit_complexity.py`](../../../scripts/phase25_digit_complexity.py))
- **Independent script re-execution:** `python -B scripts/phase25_digit_complexity.py` exited with code `0`, printing `ALL 844 CHECKS PASSED` (up from 709 checks, with exact `int`/`fractions.Fraction` arithmetic and verified outward rounding throughout).

### Disposition of Findings

| ID | Status | Verification |
| --- | --- | --- |
| **M1** | **Closed** | Theorem 1.2(3) now proves $\sigma_{b-1} = K_{I_b} - 1 \Rightarrow t_N \notin I_b$ and the exact two-sided bound $-2 \le 2\sigma_1(x;N) - K_J(x;N) \le 1$, with explicit attainment at $x = \tfrac14, N = 2$ ($-2$) and $x = \tfrac12, N = 2$ ($+1$); Theorem 2.3 and Summary items 1 & 6 tighten $-3/N$ to $-2/N$; note line 110 and script lines 336–348, 393–407 agree on `[-2, 1]` attained. |
| **M2** | **Closed** | Replaced `f6()` with exact outward-rounding helpers `lo()` / `hi()` (`scripts/phase25_digit_complexity.py:40-79`) that check rounding direction on every printed decimal; tightened `WITNESS_DMAX = Fr(59108, 10**6)` and verified $D(W) = 0.059107954113\ldots \le 0.059108$; all nine previously misrounded bounds in Theorems 2.5–2.6, Summary items 7–8, §2.6, §9–§10, and `section_applications` are now rounded outward (including both $0.058102 \le \Delta(0.304282) \le 0.059108$ and $0.058103 \le \Delta(0.912845/3) \le 0.059108$, $0.061210$, $0.212574$ / $0.2125$, $0.228212$, $0.130322$, $0.189227$, $0.264408$, $0.197329$, $0.272009$, and $0.120753$ / $0.1207$). |
| **M3** | **Closed** | Summary item 7, Theorem 2.5 table and item (c), §5 inputs table, §10 Objective 2, and References cleanly separate $L_+(8)$ (genuinely new nonnormality in base 2/8) from $L_-(8)$ (previously proved simply nonnormal in base 8 with $D^-(\cdot;8) > 0$ in `GF-31` Thm. 4A via Selberg–Delange; newly given an elementary proof, explicit base-2 $D^-$ lower bounds, and base-2 4-nonnormality here). |
| **m1** | **Closed** | Lemma 1.1 proof (line 74) corrected to $(B+b-1)/(b-1) < 2$. |
| **m2** | **Closed** | Theorem 1.2(2) proof (line 98) reworded to state $\tfrac{1}{b+1} \in I_b$ and $\tfrac{b}{b+1} \notin I_b$ consistently. |
| **m3** | **Closed** | $\mathrm{cost}(\nu)$ defined for all shift-invariant $\nu$ in §0 (lines 58–64) with Birkhoff noted in §0 and §5; Corollary 1.6 restricts the Markov closed form to $(a,c) \ne (0,0), (1,1)$ and states both degenerate values ($\frac12$ and $0$); proof uses monotone convergence and the uniform disjoint-window tail bound $N/(2J+6) + 1$. |
| **m4** | **Closed** | Theorem 1.7(4) specifies $0.B_1B_2B_3\cdots$ ($n = 1, 2, 3, \dots$) with partial-block error $O(\sqrt{N}) = o(N)$ (and $0.0^11^10^21^2\cdots$ for $L=1$); §2.6 (line 304) explicitly states the resulting order-3 barrier for $E_+(8)$ and $L_\pm(8)$. |
| **m5** | **Closed** | All six localized slips fixed: convexity of $D_{\rm grid}(\alpha)$ in Thm. 2.2 proof (line 238); $C > 0, A \ge 0$ and $\frac23 + \frac13 = 1$ in Lemma 2.4 (lines 265, 273); $n \ge 2$ for $(0^n1^n)$ in Prop. 3.2 (line 329); $x \in (0,1)$ in Prop. 3.3 (line 334); $\chi_N - \mathrm{tr}_N = [d_N \ne d_{N+1}]$ in §3 (line 338); $b \ge 2, k \ge 2, L_1, L_2 \ge 1$, $\mathbb{N} = \mathbb{Z}_{\ge 1}$, and $m_0 + s\mathbb{Z}_{\ge 0}$ in §4 (lines 344, 350). |
| **m6** | **Closed** | References fixed to `S. Arno, F. S. Wheeler` (line 444) and `87–112` for Dajani–Kraaikamp–Liardet (line 447). |
| **m7** | **Closed** | Added `sigma_exact_rational` (cross-checked against `sigma_exact`) and 33,108 exact periodic/boundary rational instances in `D1.2`; aligned `section_applications` assertions (`> 24 * 10**4`, `> Fr(9, 2) * Fr(459, 10000)`); added Rule 5 provisional-priority disclosure in §1.6 (line 193) and exact Table 2.2 $L=8$ note (`0.0554985`) with script check. |

### Post-Repair Verdict: **ACCEPT**

All 3 Major findings (`M1`–`M3`) and all 7 Minor findings (`m1`–`m7`) are cleanly closed, `python -B scripts/phase25_digit_complexity.py` passes all 844 exact checks with exit code `0`, and no new mathematical, numerical, or attribution issues were introduced.

**Cross-model review is not independent human peer review.**
