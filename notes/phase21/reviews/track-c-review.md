# Independent Cross-Provider Referee Review — Phase 21 Track C (C1–C4)

**Worktree audited:** `C:\Users\chaos\.t3\worktrees\MathematicsResearch\research-phase-20-gener-b08235755636abff`  
**Files audited (read-only):**
- `notes/phase21/nonlinear-boundary.md` (Tracks C1–C2, §§1–8)
- `notes/phase21/multivariate-and-dense-allprime.md` (Tracks C3–C4, §§1–9)
- `scripts/phase21_nonlinear.py` (executed with `python -B scripts/phase21_nonlinear.py`, exit code `0`)
- `NormalityChecker/PowerSumPeeling.lean` (audited in full against §6 of `nonlinear-boundary.md`)
- Cross-checked against `notes/phase20/cubic-power-schedule.md` (GF-11), `notes/phase20/all-prime-polynomials.md`, `notes/phase20/reviews/track-c-review.md`, `notes/phase19/nonlinear.md`, `notes/phase19/grids.md`, and `notes/phase18/principal.md`.

---

## Executive Summary & Sub-Track Verdicts

| Sub-Track | Scope | Verdict | Findings Summary |
|---|---|---|---|
| **C1** | GF-11 audit, $d \ge 2$ isolation, refutation of uniform chain, Lemma I, Theorem Q, Corollary Q1, §6 Lean core & `PowerSumPeeling.lean` | **REVISE** | **0 Critical, 2 Major, 8 Minor.** The core breakthroughs (Proposition 2.1 refutation, averaged isolation via Lemma I, $(\log L)^{-d/(d-1)}$ small-ball rate in Theorem Q, $(\log\log N)^{-d/(d-1)}$ discrepancy rate in Corollary Q1, and all Lean statements) are **genuinely sound**. Two clean, easily fixable Major gaps exist in Lemma I: (i) the $|X^+| - |X| \le 2NC_d\delta_H$ boundary error blows up as $\tau \to 0^+$ without truncating $\tau$ at $p^{-\mu H}$; (ii) for $d < r+1$ with $2r > p^d$ or $2r > (9/2)^d$, $h_1 = 1$ admits zero anchors and the stated $(2/9)^{r-1} p^k$ anchor count fails. |
| **C2** | $d = r$ boundary, Proposition D, exact denominator barrier, real tail & strategy table (`nonlinear-boundary.md` §7) | **REVISE** | **0 Critical, 1 Major, 2 Minor.** Counts, the exact denominator-only barrier lemma, and the strategic obstruction diagnosis are **sound**. **Proposition D** (and the Summary table) has a Major quantifier-swap error claiming $v_p(q_n) - rsJ(n)$ is bounded on a set of shifts of density one, which does not follow from upper density $\le C(\log L)^{-d/(d-1)}$ and is contradicted by positive-measure zero cells of $M_2 \bmod 3^L$. |
| **C3** | Multivariate distinct orders $r < d$, Theorem M (`multivariate-and-dense-allprime.md` §§1–3) | **REVISE** | **2 Critical, 1 Major, 5 Minor.** Theorem M is **true and salvageable**, but the written proof breaks fatally whenever $m_* \ge 1$: **(1) Critical:** Lemma 2's uniform-$I$ localization fails completely for $m_* \ge 1$ because fixed higher-slot coordinates leave $n_* < d$ order-$s_*$ slots creating $H$-independent power-law singularities $(u - u_0)_+^{n_*/d - 1}$ (explicit verified counterexample: $P = X_1 X_2$ has $I \cap G_H = \emptyset$ on fixed $I = (1.0005, 1.001)$ for all $H \ge 4$). **(2) Critical:** $B = 0$ peeling at bounded coordinates relies on the **backwards** inequality $\sum_{i \le j} p^{-dg_i} < 2^d p^{-dg_j}$ (false for all $j \ge 2$), on unweighted $k' \le k + O(1)$ (which fails against $g_{m_*}$), and on maximizing degree before lex-min (which lets lower-degree competitors violate $k'_j < 2g_j$, e.g. $X_1 X_3^4 + X_1 X_2^2 X_4$). Concrete minimal fixes restore Theorem M completely. |
| **C4** | Refined protected pole (Prop. 5.1), polynomial hybrid (Theorem H), quasi-polynomial universal schedule (Theorem U), §8 thresholds | **REVISE** *(Theorems H & U: ACCEPT WITH MINOR POLISH; Prop. 5.1: REVISE)* | **0 Critical, 1 Major, 5 Minor.** **Theorem H** and **Theorem U** are **completely sound** (including the genuine discovery that $p \nmid k_j$ is required to avoid $p$-adic residue pollution). **Proposition 5.1 Part 3** has one Major omission: $\log n_k / (k \log k) \to \infty$ alone does **not** imply (S) ($n_{k+1}/n_k \to \infty$), failing for staircase schedules ($n_{2m+1} = n_{2m} + 1$). |

---

## Detailed Audit — Track C1 (`notes/phase21/nonlinear-boundary.md` §§1–6)

### C1.1 Audit of GF-11 & Extension of Isolation to All $r \ge 2, d \ge 2$ (§1)

1. **Seven pressure points of GF-11 (lines 29–39):** Independently re-verified against `notes/phase20/cubic-power-schedule.md` and `notes/phase20/reviews/track-c-review.md`. All seven pressure points hold for $r \ge 3, d \ge r+1$. In particular, the Weyl-differencing induction from van der Corput ($q=2$) confirms Titchmarsh Theorem 5.13 unconditionally for all piece lengths $T_i \ge 1$ and all $\lambda > 0$ (both trivial regimes $\lambda \ge 1$ and $\lambda < T_i^{-(K_q - 1)}$ are dominated by the first and second terms respectively, and $1 - 2/K_q \ge 0$ permits replacing $T_i$ by ambient $T = p^{v'}$).
2. **$q > d$ extension via $x \ge \eta = p^{-2\kappa H}$ cap (lines 46–48):**
   - For $f_B^{(q)}(x) = (d-1) B x^{d-q} (x^d + B)^{1/d - q} \Phi_q(x^d, B)$ on $x \in [\eta, p)$, $x^d + B \in [1/4, p^d+1]$, $|B| \in [p^{-cH}, r p^d]$, $|\Phi_q(x^d, B)| \ge \eta^{d(q-2)}$:
     - **Upper bound ($q > d$):** $x^{d-q} \le \eta^{d-q} = p^{2\kappa(q-d)H}$ and all other factors are $O_{p,r,d,q}(1)$, so $|f_B^{(q)}(x)| \ll p^{2\kappa(q-d)H}$. In Titchmarsh 5.13 this adds $2\kappa(q-d)H / (2K_q - 2)$ to $E_1$, absorbed for small $\kappa$.
     - **Lower bound ($q > d$):** $x^{d-q} > p^{d-q} \gg 1$, so $D_{\min} \gg p^{-\gamma H}$ with $\gamma = c + 2\kappa d(q-2)$ (see C1-m1 below: $\gamma$ is larger by $2\kappa(q-d)$ than GF-11's $c + 2\kappa(d(q-1)-q)$, still $c + O(\kappa)$ and absorbed for small $\kappa$).
     - **Dyadic pieces & non-constancy:** Raising $(f_B^{(q)})^d = D^d$ to a polynomial equation still has RHS degree minus LHS degree $= d^2 + dq - d > 0$ for all $d \ge 2, q \ge 2$ (including $q > d$), and $\Phi_{q+1}(x^d, B) = 0$ has $\le q - 1$ positive real roots, giving $O_{q,d}(H)$ monotonic dyadic pieces since $\log_2(D_{\max}/D_{\min}) = O_{q,d}(H)$.
     - **Slab volume for $d \le r$:** Since $u \le p^d$ forces $z_i^d \le p^d \implies z_i \le p$, $R_u = \{z \in (0,p)^r : \sum z_i^d \le u\}$ still has volume $c_{r,d} u^{r/d}$ with bounded derivative on $[1/2, p^d+1]$ for all $r \ge 2, d \ge 2$.
3. **$r = 2, q = 3$ edge cases:**
   - $K_3 = 4, 2K_3 - 2 = 6$: $E_1/H = \beta + (1 - 3\alpha)/6 \le \frac{1}{6} + \frac{3}{4}\beta \le \frac{11}{12}$ and $E_2/H = \beta - \frac{1}{6} \le \frac{5}{6}$ on $\beta/2 \le \alpha \le \beta \le 1$, confirming the exact margin $1/12$.
   - $B = 0$: Since $p$ is odd, $e_2 = v_p(2!) = 0$, so $H' \le H$ and $\delta' = C_d \epsilon H^{-1} p^{-H} < p^{-H} \le p^{-\max(v,v')}$ for $H > C_d$, forcing $x = z$ and hence $w_1^d = y_1^d \implies w_1 = y_1$. Also $h_1 \le \kappa H < H - h_1 = v$ ensures $y_1 \ne z$ and jump $2p^{sH} \not\equiv 0 \pmod{p^{sH+1}}$.
   - $d = 2, q = 3$: $\Phi_3(x^2, B) = -3 x^2$, which satisfies $|\Phi_3(x^2, B)| = 3x^2 \ge 3\eta^2 > \eta^2 = \rho$ on $x \ge \eta$; both upper and lower derivative bounds hold cleanly.
   - However, anchor existence for general $d < r+1$ has a genuine bug (see **C1-M2** below).

### C1.2 Proposition 2.1, Lemma I, Theorem Q, Corollary Q1 (§§2–5)

- **Proposition 2.1 (§2):** Sound for all $H \ge 4$ (and certified in exact integers at $H = 4000$, where $R_{4000}^{126} < 3^{4000}$). Every centre has three distinct positive losses, so it never belongs to the net $\{2 + (a/3^H)^4\}$. Minor boundary slip at $H = 1, 2, 3$ (see C1-m2).
- **Lemma I (§3):** The architecture — $h_2 \ge \lambda H$ with $\lambda = 3\kappa/6^{r-1}$, intersection of $N$ intervals with $O(qH)$ dyadic pieces giving $\le N + O(qH)$ pieces per row, Titchmarsh 5.13 concavity across pieces, row count $H^{O(r)} p^{(1-\kappa)H + O(1)}$, and the regular/irregular split at $\mu_0 = 1/(2r)$ (noting that positive numerators $a_m \ge 1$ eliminate any $+1$ rounding error on irregular tuples!) — is **genuinely strong and correct**, modulo two Major gaps (**C1-M1** and **C1-M2** below).
- **Theorem Q (§4):** **Sound** once Lemma I is patched. In particular:
  - Removing at most $p H_{j+1}^{r-1} p^{H_{j+1}}$ open flanks at step $j \to j+1$ increases the component count by at most $1$ per removed flank, so $N_{j+1} \le N_j + p H_{j+1}^{r-1} p^{H_{j+1}} \le A H_{j+1}^A p^{H_{j+1}} (j+2)$ holds inductively once $A \ge \max(p, r-1)$.
  - $\delta_H$-separation of distinct isolated centres implies at most one isolated centre lies within $\delta_H/2$ of each of the $\le 2N_j$ endpoints of $\partial X_j$, confirming the $-2N_j$ boundary deduction.
  - Generalized Bernoulli $(1 - c_1 x_j^a)^{-a} \ge 1 + a c_1 x_j^a$ (for $a = (d-1)/d \in [1/2, 1)$) and $m(L) \gg \log L$ are exact.
- **Corollary Q1 (§5):** **Sound.** Clearing denominators via $y = b^c P(C) = (b^c/M_b) P_1(C)/M'$, coefficient bound $O(m^{(r-1)/d})$ with $H = \lceil 2 \log_b N \rceil$ (using $(r-1)/d < 1/2$ from $d > r(s+1)$), freezing threshold $J_0(L) = \lceil L/s + L/d \rceil$ for general rational $P$ (lower degrees carry $p^{sJ}$ with $sJ \ge L$, retained degree-$r$ indices have $v_p(b^{ti^d} - 1) = a_0 + d(J-h) \ge L$, exact bijection with $M_r(u) \bmod p^L$), cell-rounding error $O(\log N \cdot L^{r-1} p^{L/s})$ including the final partial shell (since $t p^{d J_{\max}} \le N$), grid mesh $1/G_n \le p^{L+a_0+O(1)} n^{-rs/d}$, run count $O(N^{r/d} + \log N \cdot L^{r-1} p^{L/s})$, and buffer cost $O(N^{r/d} \log N)$ all verify cleanly (see C1-m6 on the exact condition for $c_0$).

---

### Major Findings — Track C1

#### C1-M1 [MAJOR]. Boundary term $|X^+| - |X| \le 2 N C_d \delta_H$ blows up as $\tau \to 0^+$ in Lemma I (`nonlinear-boundary.md`, lines 66, 87, 91)
- **Issue:** Lemma I is stated for arbitrary $0 < \tau \le 1$, claiming
  $$\#\{\text{non-isolated centres in } X\} \le A\epsilon(\tau^{1-d}|X| + \tau) H^{r-1} p^H + A N H^A p^{(1-\mu)H}.$$
  The proof bounds regular competitors on $X^+$ by $O(\tau^{1-d} |X^+| H^{r-1} p^H) + O(N H^{r-1} p^{(1-\mu_0)H})$, multiplies by $O(\epsilon)$, and concludes in one line: *"Finally $|X^+| \le |X| + 2 N C_d \delta_H$."*
  Substituting $|X^+| \le |X| + 2 N C_d \delta_H$ into $\epsilon \tau^{1-d} |X^+| H^{r-1} p^H$ yields an **unaccounted extra term**
  $$2 C_d \epsilon^2 N \tau^{1-d},$$
  which tends to $+\infty$ as $\tau \to 0^+$ and is **not** absorbed by $A N H^A p^{(1-\mu)H}$ when $\tau$ is arbitrarily small.
- **Concrete minimal fix:** Require $\mu < 1/d$ (in addition to the other smallness constraints on $\mu$). In the proof of Lemma I, handle $N = 0$ trivially ($X = \emptyset$), and for $N \ge 1$ apply the regular/irregular split with $\tilde\tau := \max(\tau, p^{-\mu H}) \in (0, 1]$ instead of $\tau$. Then:
  1. $\tilde\tau^{1-d} \le \tau^{1-d}$;
  2. the boundary-difference term satisfies $2 C_d \epsilon^2 N \tilde\tau^{1-d} \le 2 C_d N p^{(d-1)\mu H} \le 2 C_d N p^{(1-\mu)H}$ (since $d\mu < 1 \implies (d-1)\mu < 1-\mu$);
  3. the irregular-competitor term satisfies $\epsilon \tilde\tau H^{r-1} p^H \le \epsilon \tau H^{r-1} p^H + N H^{r-1} p^{(1-\mu)H}$.
  This makes Lemma I literally valid as stated for **all** $0 < \tau \le 1$ (alternatively, add the hypothesis $\tau \ge p^{-\mu H}$ to Lemma I, which Theorem Q already satisfies since $\tau = (x/p^d)^{1/d} \ge p^{-\mu H/(8d)}$).

#### C1-M2 [MAJOR]. Anchor existence and $(2/9)^{r-1} p^k$ count fail for $d < r+1$ (`nonlinear-boundary.md`, lines 48, 64, 76)
- **Issue:** In GF-11, $d \ge r+1$ guaranteed $\theta = (2r)^{-1/d} \ge 4^{-1/3} \approx 0.630$, so $\theta p^{h_1} \ge 1.89$ even at $h_1 = 1$, and each anchor coordinate had at least $(2/9) p^{h_i}$ choices. Lemma I and §1 claim isolation for **all** $r \ge 2, d \ge 2$, keeping $h_1 \ge 1$ and stating on line 76: *"There are at least $(2/9)^{r-1} p^k$ anchors per loss vector."*
  When $d < r+1$ and $2r > p^d$ (e.g. $p = 3, d = 2, r \ge 5$), $\theta p = (2r)^{-1/d} p < 1$, so loss vectors with $h_1 = 1$ have **zero** anchors! Even for large $h_i$, when $2r > (9/2)^d$ (e.g. $d = 2, r \ge 11$), $\theta < 2/9$, so there are at most $\theta p^{h_i} < (2/9) p^{h_i}$ anchors per coordinate.
- **Concrete minimal fix:** Require $h_1 \ge h_{\min}(p,r,d) := \lceil \log_p(6/\theta) \rceil$ (for $r \ge 3$, the box $h_j \in [a_j, 2a_j]$ with $a_1 \asymp \kappa H$ automatically satisfies $h_1 \ge h_{\min}$ for $H \ge H_*$; for $r = 2$, $\theta = 4^{-1/d} \ge 1/2$ already gives $\theta p \ge 3/2$). Then each anchor coordinate has at least $(1 - 1/p)\theta p^{h_i} - 2 \ge (\theta/3) p^{h_i}$ admissible numerators, so each loss vector in the box has at least $(\theta/3)^{r-1} p^k$ anchors (whose dependence on $r, d$ is absorbed into $A$).

---

### Minor Findings — Track C1

- **C1-m1 (`nonlinear-boundary.md` line 46):** When $q > d$, the lower-bound exponent for $D_{\min}$ changes from GF-11's $\gamma = c + 2\kappa(d(q-1)-q)$ to $\gamma = c + 2\kappa d(q-2)$ (larger by $2\kappa(q-d)$ since $x^{d-q} > p^{d-q}$ replaces $\eta^{d-q}$). Both are $c + O(\kappa)$ and absorbed for small $\kappa$ (and `scripts/phase21_nonlinear.py` line 250 uses $c + 2\kappa d(q-2)$), so state $\gamma = c + 2\kappa d(q-2)$ explicitly in §1.
- **C1-m2 (`nonlinear-boundary.md` lines 54–56):** Proposition 2.1 states *"the choice of $R_H$ makes this at most $2\delta_H$ for every $H$"*. Exact verification shows the gap condition **fails** for $H = 1, 2, 3$ (and at $H = 1$, $a_{\rm lo} = 0$, so no admissible $a \le \rho_1^{1/4} 3^1$ exists), while it holds for every $H \ge 4$ (and the analytic bound $8 a_{\rm hi}^3 \le 2\delta_H 3^{4H}$ holds for all $H \ge 5$). State $H \ge 4$ (or $H \ge 6$) explicitly.
- **C1-m3 (`nonlinear-boundary.md` line 82):** The bound $(N + O(qH))^{2/K_q} \le (2N)^{1/2}$ drops an $H^{1/2}$ factor when $N \ll qH$ (e.g. $N = 1$). Replace with $(N + O(qH))^{2/K_q} \ll_{q,d} N^{1/2} H^{1/2} \le N H^{O(1)}$, which is absorbed into $H^{O(r)}$. Also make explicit that $\mu := \frac{1}{2}\min(\mu_{\rm GF11}, \lambda/3, c/d - \kappa, \kappa, \mu_0, 1/d)$ is fixed prior to the hypothesis $\epsilon \ge p^{-\mu H/8}$ so there is no circularity.
- **C1-m4 (`nonlinear-boundary.md` line 83):** Since $\operatorname{Comp}'(X^+)$ already drops $p \nmid m'$ on $x$, the extra factor $\frac{p}{p-1}$ in $2\eta_0 \frac{p}{p-1} \operatorname{Comp}'(X^+)$ is redundant (harmless upper bound).
- **C1-m5 (`nonlinear-boundary.md` line 105):** In Theorem Q, the intermediate inequality *"one has $x\epsilon \ge (\log L)^{-3} \ge p^{-\mu H/8}$"* fails by the constant factor $8 p^2 A^2$ when $d = 2$ and $x$ is near $(\log L)^{-2}$ (since $x\epsilon = x^{3/2}/(8p^2A^2)$). What is actually needed is $\epsilon > (\log L)^{-1}/(8p^dA^2) \ge p^{-\mu H/8}$ and $x > (\log L)^{-2} \ge p^{-\mu H/8}$, both of which hold cleanly for large $L$ (or use $H = H_{j+1} \ge \Gamma H_0$). Also add one sentence justifying the inductive component bound $N_{j+1} \le N_j + p H_{j+1}^{r-1} p^{H_{j+1}} \le A H_{j+1}^A p^{H_{j+1}} (j+2)$.
- **C1-m6 (`nonlinear-boundary.md` line 132):** With $L = \lfloor c_0 \log N \rfloor$, $p^{L/s} = N^{(c_0 \log p)/s}$ is a small positive power of $N$, not $N^{o(1)}$. State explicitly that $c_0$ is chosen small enough that $(c_0 \log p)/s < r/d$ (along with $c_0 \log p < rs/(2d)$ and $c_0(1+d/s)\log p < 1/2$), so that $\log N \cdot L^{r-1} p^{L/s} = o(N^{r/d})$, the run count is $O(N^{r/d})$, and the residual cost is $O(N^{r(s+1)/d}) = O(N^{1-\eta'})$.
- **C1-m7 (`nonlinear-boundary.md` lines 139–143):** In the conditional remark `(LC)`, replacing $X$ by $X \setminus Z_H$ in Lemma I could inflate the interval component count $N$ unless $Z_H$ has controlled component complexity (note that the heuristic $Z_H$ of §2 has $\asymp H^{r-2} p^H$ components, which is too large to cut $X$ directly). Phrasing `(LC)` instead as $\operatorname{Comp}(X^+) \le C_0(|X| + H^{-a}) H^{r-1} p^H + N H^A p^{(1-\mu)H}$ avoids cutting $X$ by $Z_H$ and yields the exact same recursion $x_{j+1} \le (1-c) x_j + H_{j+1}^{-a}$.
- **C1-m8 (`nonlinear-boundary.md` line 33):** Under pressure point (i) of GF-11, the remark *"Competitors with a different number of coordinates cannot occur at $B=0$"* does not belong to GF-11 (where all tuples have length $r$) and anticipates C3, where peeling at bounded coordinates actually fails (see C3-C2).

---

## Detailed Audit — Track C2 (`notes/phase21/nonlinear-boundary.md` §7)

- **§7.1 Counts:** $\pi/4$ (squares) and $\Gamma(4/3)^3 \approx 0.712$ (cubes) for ordered tuples, Landau's $KX/\sqrt{\log X}$ for distinct sums of two positive squares (removing $a^2 + 0^2$ costs only $O(\sqrt{X})$), and $(\Gamma(4/3)^3/6 + o(1))X$ upper bound for distinct sums of three positive cubes all verify accurately against the script.
- **§7.3 Item 2 (Denominator-only barrier lemma, line 237):** **100% sound.** For any prime $p$ and $q = p^e$ with $b^T \le q/2$, admissible $a \in \{1, \dots, q-1\}$ ($p \nmid a$) start at $a = 1$ ($\lfloor b^T/q \rfloor = 0$), end at $a = q - 1$ ($\frac{(q-1)b^T}{q} \ge b^T - \frac{1}{2} > b^T - 1 \implies \lfloor (q-1)b^T/q \rfloor = b^T - 1$), and advance by at most $2$, so $a b^T / q$ advances by at most $2b^T/q \le 1$ and its floor advances by at most $1$, hitting all $b^T$ words.
- **§7.3 Item 4 & Strategy table:** Sound and clear.

### Major Finding — Track C2

#### C2-M1 [MAJOR]. False quantifier-swap conclusion in Proposition D (`nonlinear-boundary.md`, lines 22, 226)
- **Issue:** Proposition D states:
  > *"For every $L$, the shifts $n \le N$ with $v_p(q_n) < rsJ(n) - L$ have upper density at most $C(\log L)^{-d/(d-1)}$. **Hence $v_p(q_n) - rsJ(n)$ is bounded on a set of shifts of density one.**"*
  (And Summary line 22: *"At $d = r$ the prefixes of $P(C)$ have $p$-depth $rsJ - O(1)$ on a set of shifts of density one."*)
  This is a quantifier-swap error. Knowing $\overline{d}(\{n : v_p(q_n) < rsJ(n) - L\}) \le C(\log L)^{-d/(d-1)} \to 0$ as $L \to \infty$ does **not** produce a single constant $L_0$ such that $\{n : v_p(q_n) < rsJ(n) - L_0\}$ has density $0$. Indeed, exact computation for $C(2,3,1,2)^2$ shows that the zero cells $\{u \in [1, 9) : M_2(u) \equiv 0 \pmod{3^L}\}$ have strictly positive Lebesgue measure for $L = 1, 2, 3, 4$ (specifically $4$, $7/9$, $5/27$, and $38/729$ respectively; note also that the script's window $[2 \cdot 10^5, 4 \cdot 10^5]$ only sampled $u \in [1.69, 3.39]$ in shell $J = 5$, missing $[5, 8)$ where $M_2(u) \equiv 3 \equiv 0 \pmod 3$). Additionally, Proposition D should require $L \ge 3$ (since $\log 1 = 0$) and note $C = C(P)$ (to handle $L \le 2 + v_p(A_{\rm lead})$).
- **Concrete minimal fix:** Replace the second sentence of Proposition D (and Summary line 22) by:
  > *"For every $L \ge 3$, the shifts $n \le N$ with $v_p(q_n) < rsJ(n) - L$ have upper density at most $C_P (\log L)^{-d/(d-1)}$. Hence $v_p(q_n) - rsJ(n)$ is tight in density (for every $\varepsilon > 0$ there is $L$ such that $v_p(q_n) \ge rsJ(n) - L$ on a set of lower density $\ge 1 - \varepsilon$), and for every function $\omega(n) \to \infty$, $v_p(q_n) \ge rsJ(n) - \omega(n)$ on a set of shifts of density one."*

### Minor Findings — Track C2

- **C2-m1 (`nonlinear-boundary.md` line 238):** The real-tail lower bound $\frac{1}{N} \sum_{n < N} T_n \ge \frac{1}{N} \sum_{m \le N} c_m (1 - b^{-m})$ is missing the factor $\frac{1}{b - 1}$: since $\sum_{n=0}^{m-1} b^{n-m} = \frac{1 - b^{-m}}{b - 1}$, the true bound is $\frac{1}{(b-1)N} \sum_{m \le N} c_m (1 - b^{-m})$ (they coincide only at $b = 2$).
- **C2-m2 (`nonlinear-boundary.md` line 238):** For squares ($r = d = 2$), *"For squares, $T_n \to 0$ in density, because the insertion positions have density zero"* is slightly incomplete because $c_{2m} \le r_2(m)$ is unbounded. The conclusion is true, but its proof needs one extra line: split $T_n = \sum_{u \le H} c_{n+u} b^{-u} + \sum_{u > H} c_{n+u} b^{-u}$; the first sum vanishes off a set of density $0$ by Landau's bound, and the second has average $\frac{1}{N}\sum_{n < N} \sum_{u > H} c_{n+u} b^{-u} \ll b^{-H}$ (since $\sum_{m \le X} c_m = O(X)$), so Markov's inequality kills it as $H \to \infty$.

---

## Detailed Audit — Track C3 (`notes/phase21/multivariate-and-dense-allprime.md` §§1–3)

### Critical Findings — Track C3

#### C3-C1 [CRITICAL]. Uniform Lemma 2 and GF-11 main-term localization are FALSE whenever $m_* \ge 1$ (`multivariate-and-dense-allprime.md`, §3 lines 81–83)
- **Issue:** Section 3 line 81 claims:
  > *"Main term. The competitor count of §2 is $O(H^{n_* - 1} p^H)$ per unit length, plus the lattice error of GF-11."*
  and line 83 invokes Lemma 2 of GF-11, which requires $|I \cap G_H| \ge c |I|$ for every interval $I \subset K'$ with $c > 0$ independent of $I$ once $H \ge H_0(I)$.
  This is **false whenever $m_* \ge 1$** (i.e., whenever the target monomial involves any variable of order $> s_*$). Fix any higher-order coordinates $w_{\rm hi} = (w_1, \dots, w_{m_*})$ of bounded losses $e_1, \dots, e_{m_*}$ such that $u_0 = S(w_{\rm hi}) \in (1, p^d)$. In $\nu^*$, the remaining $n_*$ slots of order $s_*$ have total loss up to $H + C_g - \frac{1}{s_*} \sum o_j e_j$. On the fixed interval $I = (u_0, u_0 + \rho)$, the number of tuples $(w_{\rm hi}, x_1, \dots, x_{n_*})$ with $S \in I$ is
  $$\asymp \operatorname{Vol}\Big(\sum_{i=1}^{n_*} x_i^d \le \rho\Big) \cdot H^{n_* - 1} p^{H + C_g - \frac{1}{s_*}\sum o_j e_j} \asymp \rho^{n_*/d} H^{n_* - 1} p^H,$$
  against $\asymp \rho H^{n_* - 1} p^H$ centres in $I$. Because $n_* < r_* \le r < d$, we have $n_*/d < 1$, so the ratio scales as $\rho^{n_*/d - 1} \to \infty$ as $\rho \to 0$ **independently of $H$** (unlike GF-11 where $m_* = 0$ left an extra $H^{r-1} \to \infty$ margin). Equivalently, the limiting competitor density is an $L^1(K')$ function with integrable power-law poles $(u - u_0)_+^{n_*/d - 1}$ on a dense set of points, **not** bounded in $L^\infty(K')$.
- **Verified counterexample to Lemma 2:** Take $P(X_1, X_2) = X_1 X_2$ with $s_1 = 1, s_2 = 2, p = 3, d = 3$ ($n_* = 1, m_* = 1$), fixed $g_1 = 2$, $\epsilon = 1/4$, $\delta_H = \epsilon / 3^H$. The relevant competitors $(1, a / 3^{H + g_1})$ (weighted level $2 \cdot 0 + (H + g_1) < \pi = H + g_1 + 1$) have sums $1 + (a / 3^{H+2})^3$. On the **fixed** interval $I = (1.0005, 1.001)$, exact integer computation confirms that for every $H \ge 4$ the maximum gap between consecutive admissible competitor sums is $\le 0.0137 \cdot (2 \delta_H) \ll 2 \delta_H$, so **$I \cap G_H = \emptyset$ for every $H \ge 4$**. The same holds for ANY fixed $\epsilon > 0$ on a dense open union of fixed intervals $(u_0 + \rho_e/2, u_0 + \rho_e)$ near $u_0 = (b/3^e)^3 \in (1, 27)$, and identically for $n_* \ge 2, m_* \ge 1$ (e.g. $X_1^2 X_3 + 5 X_1 X_2^2$ on $(1, 1 + \rho)$ where $\rho^{2/4} \gg \rho$).
- **Concrete minimal fix ($L^1$ Lebesgue-point localization):** Replace Lemma 2's uniform-$I$ hypothesis as follows.
  1. For each interval $I \subset K'$, split competitors of $\nu' \in T$ by their higher-slot coordinates $w_{\rm hi}$ at a weighted cutoff $E_0 = E_0(|I|)$:
     - Tuples with $\nu'_{a_*} < n_*$ contribute $O(H^{n_*-2} p^H) = o(H^{n_*-1} p^H)$ (or $O(H^{r-1} p^{\frac{s_*}{s_*+1} H})$ when $\nu'_{a_*} = 0$).
     - Tuples with $\nu'_{a_*} = n_*$ and $\sum o_j e_j > E_0$ contribute $O(H^{n_*-1} p^H \cdot p^{-\eta_1 E_0})$ by convergence of $\prod \sum_{e_j} p^{e_j(1 - o_j/s_*)}$; choose $E_0$ so $p^{-\eta_1 E_0} \le |I|$.
     - For each of the finitely many remaining $w_{\rm hi}$ (with $\sum o_j e_j \le E_0$), apply GF-11's $n_*$-dimensional lattice count to $(x_1, \dots, x_{n_*})$ on the slab $I^+ - S(w_{\rm hi})$: when $n_* \ge 2$ the lattice error is $O_{E_0}(H^{n_*-2} p^H) = o(H^{n_*-1} p^H)$, and when $n_* = 1$ the 1D lattice error is $+1$ per $w_{\rm hi}$, totalling $O_{E_0}(1) = o(p^H)$.
  2. Hence for every interval $I \subset K'$,
     $$\limsup_{H \to \infty} \frac{\operatorname{Comp}'(I^+)}{H^{n_*-1} p^H} \le C_P \int_I f(u)\,du, \qquad f(u) := 1 + \sum_{\substack{\nu' \in T \\ \nu'_{a_*} = n_*}} \sum_{w_{\rm hi}} p^{-\frac{1}{s_*}\sum o_j e_j} \frac{d}{du} \operatorname{Vol}_{n_*}\!\Big(\sum_{i=1}^{n_*} x_i^d \le (u - S(w_{\rm hi}))_+\Big).$$
     Since $n_*/d > 0$ and $\prod_j \sum_{e_j \ge 0} p^{e_j(1 - o_j/s_*)} < \infty$, we have $f \in L^1(K')$.
  3. For each integer $M \ge 1$, set $\epsilon_M = \min(\epsilon_0, c_1/M)$ (with $\epsilon_0$ as in C3-M1 below). On every interval $I \subset K'$ with $\frac{1}{|I|}\int_I f \le M$, isolation holds for all $H \ge H_0(I, M)$ and reverse Fatou yields $|I \cap \limsup_H G_H(\epsilon_M)| \ge c_2 \epsilon_M |I|$.
  4. As in GF-11 Lemma 2, no point of $\limsup_H G_H(\epsilon_M)$ is a density point of a level set $E = \{M_P = w\}$, so $|E \cap \limsup_H G_H(\epsilon_M)| = 0$, hence $|I \cap E| \le (1 - c_2 \epsilon_M)|I|$ whenever $\frac{1}{|I|} \int_I f \le M$. If $|E| > 0$, choose $x_0 \in E$ that is simultaneously a Lebesgue density point of $E$ and a Lebesgue point of $f \in L^1(K')$, and put $M = \lceil f(x_0) \rceil + 1$: small intervals $I$ around $x_0$ satisfy $\frac{1}{|I|}\int_I f \le M$, forcing $|I \cap E|/|I| \le 1 - c_2 \epsilon_M < 1$, contradiction. Thus $|E| = 0$.

#### C3-C2 [CRITICAL]. Broken $B = 0$ peeling at bounded coordinates and incompatible target-monomial selection for mixed degrees (`multivariate-and-dense-allprime.md`, §2 lines 41–43 & §3 line 79)
- **Issues (three intertwined errors):**
  1. **Backwards inequality on line 79:** Line 79 claims *"At a bounded coordinate the remaining anchor sum is $\sum_{i \le j} p^{-dg_i} < 2^d p^{-dg_j}$. So the unique competitor coordinate of loss $g_j$ has numerator $c$ with $c^d < 2^d$, that is $c = 1$, and it peels."*
     Because $g_1 < g_2 < \dots < g_j$, $p^{-d g_j}$ is the **smallest** summand, not the largest: $\sum_{i \le j} p^{-dg_i} > p^{-dg_1} = p^{d(g_j - g_1)} p^{-dg_j} \gg 2^d p^{-dg_j}$ for every $j \ge 2$. Hence $c^d < 2^d$ and $c = 1$ do **not** follow.
  2. **Wrong target selection for mixed degrees (lines 41 vs. 43):** Line 41 selects $\nu^*$ by maximizing $n_* = \nu_{a_*}$, then **maximizing the degree $r_*$**, then taking lex-least $u(\nu)$. Line 43 falsely asserts this coincides with taking the lex-least sorted order tuple. When degrees differ, the two disagree — e.g. for $s = (1, 2, 5, 16), S^* = 21, d = 6$ and $P = X_1 X_3^4 + X_1 X_2^2 X_4$:
     - Line 41 (max degree first) picks $\nu^* = X_1 X_3^4$ with sorted orders $(1, 5, 5, 5, 5)$ and $w^* = v + 5(g_1 + g_2 + g_3 + g_4)$.
     - The lower-degree monomial $\nu' = X_1 X_2^2 X_4$ has sorted orders $(1, 2, 2, 16) <_{\rm lex} (1, 5, 5, 5, 5)$. Putting $x = z$ in slot $1$ leaves weighted budget $2 e_1 + 2 e_2 + 16 e_3 \le 5(g_1 + g_2 + g_3 + g_4) + O(1)$, which **allows two coordinates $e_1 = e_2 = g_4 + 1 > g_4$** (since $4g_4 + 4 < 5g_4$)! Thus the valuation peeling bound $\sum e_l < 2 g_4$ fails completely.
  3. **Unweighted $k' \le k + O(1)$ cannot peel bounded coordinates (line 79):** Even for a single monomial (e.g. $u_1(\nu^*) \ge 2 s_*$), the unweighted excess $H' - H$ can be as large as $\frac{u_1(\nu^*) - s_*}{s_*} g_{m_*} \ge g_{m_*}$, so $k'_{m_*} = \sum g_i + (H' - H) \ge 2 g_{m_*}$ violates $k'_j < 2 g_j$. Peeling bounded coordinates **requires** tracking the weighted inequality.
- **Concrete minimal fix:**
  1. **Target selection:** Drop *"fix the largest degree $r_*$"* in line 41; define $\nu^* \in T$ directly as the monomial whose sorted order tuple $(o_1 \le \dots \le o_{\deg \nu})$ is **lexicographically least**. (As line 43 already notes, this automatically maximizes $n_* = \nu_{a_*}$, and no member of $T$ can be a proper prefix of another since all have equal sum $S^*$.) Set $r_* = \deg(\nu^*)$ and $m_* = r_* - n_*$.
  2. **Weighted peeling of free coordinates:** For any $B = 0$ competitor $(w, x)$ from $\nu' \in T$ with $x = z$ ($v' = v$), $x$ must occupy an order-$s_*$ slot (else weight $\ge (s_*+1)v > \pi$). Cancelling $s_* v$ gives
     $$s_* \sum f_i + \sum o'_l e_l \le s_* (h_1 + \dots + h_{n_*-1}) + \sum_{i=1}^{m_*} u_i(\nu^*) g_{m_*+1-i} + e_{\rm prec}. \tag{$*$}$$
     Peeling $h_{n_*-1}, \dots, h_1$ downward: at $h_j \ge \lambda H$, dividing by $s_*$ gives total remaining loss $< 2 h_j$, forcing a unique coordinate of loss $h_j$; if it does not peel off, the divisor bound saves $p^{-h_j/3}$; if it peels off, it **must** sit in an order-$s_*$ slot (since $h_j \ge s_m(\sum g + \sum_{i<j} h_i) + G_0$ makes an order $\ge s_* + 1$ slot exceed the RHS of $(*)$). After all free coordinates peel off, we must have $\nu'_{a_*} = n_*$, and the remaining higher-slot losses satisfy
     $$\sum_{l=1}^{q'} u_l(\nu') e_l \le \sum_{i=1}^{m_*} u_i(\nu^*) g_{m_*+1-i} + e_{\rm prec}. \tag{$**$}$$
  3. **Inductive choice of bounded anchor coordinates $(g_1, a_1), \dots, (g_{m_*}, a_{m_*})$:** Instead of fixing numerator $1$, choose $(g_1, a_1), \dots, (g_{m_*}, a_{m_*})$ **sequentially** (fixed constants independent of $H$) with $y_i = a_i / p^{g_i} \le \theta = (2r_*)^{-1/d}$ and $p \nmid a_i$:
     - Having chosen $(g_1, a_1), \dots, (g_{j-1}, a_{j-1})$, put $B_{j-1} := \frac{s_m}{s_*} \sum_{i < j} g_i + e_{\rm prec}$. Choose $g_j > \max(2 B_{j-1} + C_0, s_m \sum_{i < j} g_i + G_0)$ large enough that the total number of $(q'-1)$-tuples $(w_l)$ of total loss $\le B_{j-1}$ times $2 \max_{|M| \le p^{d(g_j+1)}} \tau(|M|)$ (which is $\ll B_{j-1}^r p^{B_{j-1} + \epsilon' d g_j} \ll p^{(\frac{1}{2} + \epsilon' d) g_j}$) is strictly less than the number of admissible $a_j \in [1, \theta p^{g_j}]$ ($p \nmid a_j$, which is $\gg \theta p^{g_j}$). Pick an $a_j$ avoiding all solutions of $c^d - a_j^d = M \ne 0$ where $M = p^{d g_j}(\sum_{i < j} y_i^d - \sum w_l^d)$.
     - Now peel $(**)$ downward for $j = m_*, \dots, 1$: inductively $u_i(\nu') = u_i(\nu^*)$ for $i < m_* + 1 - j$, so by **pure lex-min** we have $u_{m_*+1-j}(\nu') \ge u_{m_*+1-j}(\nu^*)$ (the competitor cannot run out of slots while $\sum_{i \le j} y_i^d > 0$). Dividing the remaining $(**)$ by $u_{m_*+1-j}(\nu^*)$ gives $\sum e_l \le g_j + B_{j-1} < 2 g_j$, forcing a unique coordinate $w_j = c/p^{g_j}$ of loss $g_j$, which must sit in a slot of order $u_{m_*+1-j}(\nu^*)$ (so $u_{m_*+1-j}(\nu') = u_{m_*+1-j}(\nu^*)$). The remaining coordinates of $w$ then have total loss $\le B_{j-1}$; by our choice of $a_j$, $M = 0$ is forced, so $c = a_j$ ($w_j = y_j$ peels off!). After $j = 1$, any remaining competitor coordinates would sum to $0$, impossible, forcing $q' = m_*$, $\nu' = \nu^*$, and $w = y$ as multisets.

### Major Finding — Track C3

#### C3-M1 [MAJOR]. Unhandled edge cases: $n_* = 1$ rational separation, $r_* = 1$, and $r = 2$ (`multivariate-and-dense-allprime.md`, §§2–3 lines 73, 79–80)
- **Issues:**
  1. **$n_* = 1$ rational separation:** When $n_* = 1$, $\delta_H = \epsilon / p^H$ has **no** $H^{1 - n_*}$ decay factor, whereas a relevant competitor can have $v' \le H' < H + C_g$ with $C_g = \sum \frac{u_i - s_*}{s_*} g_{m_*+1-i} + (e_{\rm prec} + 1)/s_* > 0$. Thus $|x - z| \ge p^{-H - C_g}$ does not automatically beat $\delta' = C_d \epsilon p^{-H}$ for arbitrary fixed $\epsilon$!
  2. **$r_* = 1$ ($T = \{X_{a_*}\}$, so $n_* = 1, m_* = 0$):** When a single linear variable has uniquely maximal depth (e.g. $P = X_3 + X_1^2$ with $s_1 = 1, s_3 = 3$), the anchor is empty ($B_y = 0$) and GF-11 §5 does not apply.
  3. **$r = 2$:** Line 80 cites GF-11's margins $\sigma_r$ with $q \le r + 1 \le d$, whereas GF-11 only defines $\sigma_r$ for $r \ge 3$ ($q \in \{4, \dots, r+1\}$).
- **Concrete minimal fix:**
  1. Explicitly require $\epsilon \le \epsilon_0 := (2 C_d)^{-1} p^{-C_g}$ (a fixed constant depending only on $P$ and the chosen $g_i$; fully compatible with $\epsilon_M = \min(\epsilon_0, c_1/M)$ in C3-C1), which ensures $\delta' < p^{-H - C_g} \le p^{-\max(v,v')}$ and forces $x = z$ even when $n_* = 1$.
  2. Handle $r_* = 1$ in one sentence: $T = \{X_{a_*}\}$ gives $M_P(u) = A M_1(u)$, where every level-$H$ point $m/p^H$ is isolated at radius $p^{-H}$ (and $M_1(u) \equiv \lfloor u^{1/d} \rfloor \not\equiv 0 \pmod p$).
  3. For $r = 2$, either cite Phase 19 (already noted on line 37) or use $q = 3$ with margin $1/12$ from `nonlinear-boundary.md` §1. Also note that any degree-$1$ competitor $\nu' \in T$ when $r_* \ge 2$ has order $o_1 > s_*$ and contributes only $O(p^{\frac{s_*}{o_1} H}) = o(p^H)$ tuples directly.

### Minor Findings — Track C3

- **C3-m1 (`multivariate-and-dense-allprime.md` line 45):** The constant $G_0 > \max_\nu v_p(A_\nu r!) + 2\lfloor e \rfloor + 2$ contains an undefined symbol $e$. Replace with $G_0 > \max_{\nu \in T} v_p(A_\nu \prod_a \nu_a!) + 2$.
- **C3-m2 (`multivariate-and-dense-allprime.md` line 48):** Because the free-loss dominance uses $s_m$ in place of $2$ ($h_{j+1} \ge s_m(\sum g + h_1 + \dots + h_j) + G_0$), the lower threshold $\lambda$ must be chosen depending on $s_m$ (e.g. $\lambda \le \kappa / (3 s_m)^{n_*-1}$), not GF-11's $3\kappa / 6^{r-1}$. Also note $\kappa < 1/(s_m + 1)$ is required so that $v - s_m k \ge G_0$ holds in the non-minimal assignment check on line 63.
- **C3-m3 (`multivariate-and-dense-allprime.md` line 70):** The displayed bound $C H^{\nu'_{a_*} - 1} p^H \prod \sum p^{h(1 - o/s_*)}$ writes $H^{-1} p^H$ when $\nu'_{a_*} = 0$; in that case the actual count is $O(H^{r-1} p^{\frac{s_*}{s_*+1} H}) = o(p^H)$.
- **C3-m4 (`multivariate-and-dense-allprime.md` line 80):** Specify that the Erdős–Turán cutoff is $L_{\rm ET} = \lceil p^k H^{n_* + 1} \rceil$ so $\sum_y L_{\rm ET}^{-1} \operatorname{Comp}'(I^+) = O(H^{n_* - 3} p^H) = o(H^{n_* - 1} p^H)$.
- **C3-m5 (`multivariate-and-dense-allprime.md` line 10, Summary):** Update the Summary note on the proposed lex rule once line 41 is fixed to pure lex-min (and note that bounded numerators are chosen inductively rather than fixed to $1$).

---

## Detailed Audit — Track C4 (`notes/phase21/multivariate-and-dense-allprime.md` §§4–8)

### C4.1 Proposition 5.1 (§5)
- **Parts 1 & 2:** Sound. Using $\operatorname{ord}_{\ell^r} b \mid \ell^{r-1}(\ell - 1)$ and Phase 19's Ford–Luca–Pomerance bound $\log A(L) \ll L \log\log L \log\log\log L / \log L$ at $L = \ell_k \sim k \log k$ gives $\log A(\ell_k) \ll k \log\log k \log\log\log k = o(k(\log\log k)^2)$. Both (D) and (G) hold for $e_k = k\lceil \log\log(k+16)\rceil$, (S) holds for Parts 1 and 2, `(P'_r)` holds with $\log \Lambda_k = (1+o(1)) k \log k$, and $\log(p^{e_k} \Lambda_k) \sim k \log k = o(n_k)$ confirms the Liouville property.
- **Part 3:** Missing hypothesis (S) — see **C4-M1** below.

### C4.2 Theorem H (§6) — **SOUND (minor polish only)**
- **Part 1 (exact denominators):** Completely airtight. Each $\ell_j$ appears only at $k_j$ with $\ell_j$-unit numerator $b^{n - tk_j^d}$, so $\ell_j \parallel q_n$. For $p$: since $p \nmid k_j$, no top-$p$-valuation index $a p^J$ ($1 \le a \le \lfloor K/p^J \rfloor < p$, $J \ge 1$) is auxiliary, so $p^{sJ} R_n \equiv \lfloor K/p^J \rfloor b^n \not\equiv 0 \pmod p$, giving $q_n = p^{s\lfloor \log_p K \rfloor} \Lambda_K$ **exactly** at every shift $n \ge t$.
- **Part 2 ($p$-adic freezing invariance, grid, periods, rate):** Completely airtight.
  - Because $p \nmid k_j$, every auxiliary index has loss $J$, so any tuple containing one carries $p^{sJ}$ after normalization and vanishes mod $p^L$ for $J \ge J_0(L) = \lceil L/s + L/d \rceil$ (since $sJ \ge L$ and $\mu_k^{-1} \in \mathbb Z_p^\times$). The pollution remark & script check at $k = 27 = 3^3$ are spot-on.
  - Grid: $Q \mid \Lambda_K^r M' \implies \max_{\ell \mid Q} \ell \le \max(\Lambda_K, M') = N^{o(1)}$, so $G \ge p^{rsJ - L} N^{-o(1)}$ and the mesh sum is $p^L N^{-rs/d + o(1)} = O(N^{-rs/(2d)})$ for small $c_0$.
  - Periods: each period $\le t p^{rsJ} \Lambda_K^r \operatorname{ord}_{M'} b \le N^{rs/d + o(1)}$, and with $(c_0 \log p)/s < r/d$ the run count is $O(N^{r/d})$, giving residual cost $N^{r(s+1)/d + o(1)} = o(N)$ since $d > r(s+1)$.
  - $\deg P = 1$: fixed precision $L = v_p(A) + 1$ has zero failed shifts for $J \ge J_0(L)$ (since $M_1(u) \equiv \lfloor u^{1/d} \rfloor \not\equiv 0 \pmod p$ on $[1, p^d)$), so $D_N(P(W); b) \ll_{P,\eta} N^{-\eta}$ for any $\eta < \min(s/d, (d-s-1)/d)$.

### C4.3 Theorem U (§7) — **SOUND (minor polish only)**
- All three steps of Phase 19 §2 (`notes/phase19/nonlinear.md` §2) transfer verbatim because every auxiliary index has $v_p(k_j) = 0$: in the plateau estimate (3), both $J_m - v \to \infty$ (where top indices $a p^{J_m}$ have $J_m \ge 1$, hence $\mu_i = 1$) and bounded $J_m - v$ (where $v \to \infty$, so $v - h \ge 1$ eventually gives $\mu_i = 1$ on all retained terms, and lower-valuation terms vanish $p$-adically because $\mu_i^{-1} \in \mathbb Z_p^\times$) yield the identical limit $B(a)$; in sparsification, $v_p(k_j) = 0 < J - H$; and the last grid index $m$ has $v_p(m) \ge J - H \ge 1$, so $\mu_m = 1$.
- **Grid check:** Because $\Lambda_K = \prod_{j \le J(K)} \ell_j$ is a primorial, Chebyshev's bound gives $\max_{\ell \mid \Lambda_K} \ell \asymp \log \Lambda_K = o((\log K)^2)$, hence $w_n \le a_0 + \log_p(O((\log K)^2)) + O_P(1) \le 2 \log_p \log K + O_P(1)$, confirming $G \ge K^{rs - o(1)}$!
- **Transfer:** Discarding $n < \sqrt{N}$ (so $1/G_n \le \exp(-c \sqrt{\log N}) \to 0$ uniformly) plus the $o(N)$ discarded intervals of Phase 19 §2 leaves $O(K(N)^r) = N^{o(1)}$ runs of period $\le p^{rsJ} \Lambda_K^r M' = N^{o(1)}$ (since $\log N \sim (\log K)^2$), with $H = \lceil 2\log_b N \rceil$ controlling buffers and tail. Also the sketch estimate $w_m/n_m \asymp m^{-2p^{-H-1}}$ on line 179 is algebraically exact.

---

### Major Finding — Track C4

#### C4-M1 [MAJOR]. Missing growth-ratio hypothesis (S) in Proposition 5.1 Part 3 (`multivariate-and-dense-allprime.md`, lines 130, 132)
- **Issue:** Proposition 5.1 Part 3 states: *"If $\log n_k / (k \log k) \to \infty$, then the conclusion of part 2 holds for all nonconstant $P$,"* and line 132 asserts *"(S) holds in each case."*
  The condition $\log n_k / (k \log k) \to \infty$ alone does **not** imply (S) ($n_{k+1}/n_k \to \infty$). Counterexample: $n_{2m} = \lceil \exp(2m(\log(2m))^2) \rceil$, $n_{2m+1} = n_{2m} + 1$ (or long flat plateaus $n_k = 2^{m^2} + k$ on $k \in [m, 2m]$), which satisfies $\log n_k / (k \log k) \to \infty$ while $n_{k+1}/n_k \to 1$ along a positive-density subsequence, breaking the Phase 20 C2a window rule ($r n_{k-1} < n_k$).
- **Concrete minimal fix:** Add the explicit hypothesis $n_{k+1}/n_k \to \infty$ to Part 3 (or state $n_k = \lceil \exp(k \log k \, \psi(k)) \rceil$ with $\psi(k) \to \infty$ nondecreasing, matching Summary line 11, which does imply $(k+1)\log(k+1)\psi(k+1) - k\log k\,\psi(k) \ge \log(k+1)\psi(k) \to \infty$ and hence (S)).

### Minor Findings — Track C4

- **C4-m1 (`multivariate-and-dense-allprime.md` line 121):** The weakened period condition `(P'_r)` ($k p^{r e_k} \Lambda_k^{r-1} A(\ell_k) = o(n_k)$) holds for squarefree $\Lambda_k$ (as in $\mu_k = \ell_k$ in Proposition 5.1). For general non-squarefree $m_j$ in C2a, $\Lambda_k^{r-1}$ should be $\Lambda_k^r / \operatorname{rad}(\Lambda_k)$.
- **C4-m2 (`multivariate-and-dense-allprime.md` line 157):** As in C1-m6, state explicitly that $c_0$ is chosen with $(c_0 \log p)/s < r/d$ so $\log N \cdot L^{r-1} p^{L/s} = o(N^{r/d})$, and on line 159 clarify that for $\deg P = 1$ the rate is $O_{P,\eta}(N^{-\eta})$ for every $\eta < \min(s/d, (d-s-1)/d)$ (due to $\Lambda_K = N^{o(1)}$).
- **C4-m3 (`multivariate-and-dense-allprime.md` lines 165, 173–177):** In Theorem U, explicitly specify that $k_j$ is strictly increasing (implicit from $\mu_{k_j} = \ell_j$), and note that discarding $n < \sqrt{N}$ makes $1/G_n \to 0$ uniform across retained shifts in the prefix estimate.
- **C4-m4 (`multivariate-and-dense-allprime.md` line 191):** In §8's table, $\exp(j^2)$ is the prime position for the concrete example $k_j \approx e^j$ of Theorem U; under Theorem U's general hypothesis $\log \Lambda_K = o((\log K)^2)$ one can even place the $j$-th prime at $\exp(j \log j \, \psi(j))$ (taking $\log k_j = \sqrt{j \log j \, \psi(j)}$).
- **C4-m5 (`multivariate-and-dense-allprime.md` line 193):** Change *"and the period carries the factor $\prod_{i \le j} \ell_i^{r-1}$"* to *"and the period **bound** carries the factor $\prod_{i \le j} \ell_i^{r-1}$"* to remain consistent with §5 line 134 (unproved necessity due to possible older-prime cancellation in $P(W)$ and Wieferich primes).

---

## Audit of §6 Lean Core, `NormalityChecker/PowerSumPeeling.lean`, & `scripts/phase21_nonlinear.py`

### 1. Lean core in `nonlinear-boundary.md` §6 (9 `sorry` statements)
All nine statements (lines 155–208) were checked mathematically for edge cases and soundness:
- `unique_top_loss_of_eq_sum_pow`: **Sound.** Since $d > 0$ and `hloss` forces $h \ge 1$, `hval` forces $\sum y_i^d \ne 0$ (as `padicValRat p 0 = 0`), and `hw0` ensures `padicValRat p (w j ^ d) = d * padicValRat p (w j)`. The ultrametric argument forces a unique `j` with `padicValRat p (w j) = -h`.
- `le_of_pow_sub_pow_eq` & `card_pow_sub_pow_eq_le`: **Sound** (including edge case $M = 0$, where both sides are $0$).
- `phi`, `phi_three`, `phi_homogeneous`, `coeff_phi_X_pow`, `iteratedDeriv_rpow_root`: **Sound.** Recurrence, homogeneity of degree $q - 2$, leading coefficient $(-1)^q \prod_{i=1}^{q-2}(d+i)$, and real iterated derivative identity (using `zpow` on `x > 0` so $q > d$ is handled cleanly) all match GF-11 and §1 exactly.
- `truncMass`, `truncMass_sub`, `truncMass_jump_of_isolated`: **Sound.** Injectivity of `c : Fin r → ℚ` guarantees `σ ↦ c ∘ σ` is injective on `Equiv.Perm (Fin r)`, giving exact jump `r! * p^(s*H)`.

### 2. `NormalityChecker/PowerSumPeeling.lean` (435 lines)
- **Manual audit (note: `lake` is not on `PATH` in this review environment, so compilation was verified by complete line-by-line inspection and should be confirmed by `lake build` at integration):** Zero `sorry`, zero custom axioms.
  - `strictMono_add_pow_sub_pow`, `nat_sub_dvd_pow_sub_pow`, `card_pow_diff_eq_le_divisors` (lines 43–100): Clean and exact.
  - `phiPoly`, `phiLead`, `phiPoly_spec`, `phiPoly_ne_zero`, `phiPoly_natDegree`, `phiPoly_leadingCoeff` (lines 108–242): Exact match to GF-11's recurrence in `(ℤ[B])[X]` with $n = q - 2$.
  - `pow_dvd_den_and_not_succ_of_unique_max`, `den_dvd_pow_of_all_le`, `dominant_loss_unique_top_coord` (lines 259–433): Clean elementary `Rat.den` proof of the dominant-loss $p$-adic peeling lemma (`∑ g i < 2 * h j₀`).
  - Alignment with `nonlinear-boundary.md` §6 (line 213) is accurate: `PowerSumPeeling.lean` covers the divisor bound, `phiPoly` degree/leading coefficient, and peeling lemma, while support homogeneity, `iteratedDeriv_rpow_root`, and the two `truncMass` statements remain unproved targets.

### 3. `scripts/phase21_nonlinear.py`
- **Execution:** `python -B scripts/phase21_nonlinear.py` exited with code `0`; all assertions use exact integers/`Fraction`s and pass.
- **Two minor script discrepancies:**
  1. **Docstring typo (line 8):** States `certified at H = 3000`, whereas the code (lines 154, 171) certifies `H = 4000` (and independent check confirms `R**126 < 3**H` is `False` at $H = 3000$ and `True` at $H = 4000$).
  2. **Omitted perturbation term in `check_c1_margins` (line 250):** `e2 += kappa + (c + 2 * kappa * d * (q - 2)) / (2 * K - 2)` omits the `+ kappa / (2 * K - 2)` term from GF-11 line 109 ($+k/(2K_q - 2)$ in $E_2$). Independent exact check confirms all four tested cases `(3,3), (2,2), (4,3), (3,2)` still have strictly positive margins (`0.0232, 0.0827, 0.0078, 0.0232`) once `+ kappa / (2 * K - 2)` is restored.

---

## Post-Repair Verification

All modified sections of `notes/phase21/nonlinear-boundary.md`, `notes/phase21/multivariate-and-dense-allprime.md`, and `scripts/phase21_nonlinear.py` were re-audited line by line (read-only), and `python -B scripts/phase21_nonlinear.py` was re-executed (exit code `0`, all exact assertions pass).

### Item-by-Item Resolution Check

| Finding | Status | Verification Notes |
|---|---|---|
| **C1-M1** (`nonlinear-boundary.md` §§3–4) | **RESOLVED** | $\mu := \frac{1}{2}\min(\mu_{\rm GF11}, \lambda/3, c/d - \kappa, \kappa, \mu_0, 1/d) \in (0, 1/d)$ is fixed prior to $\epsilon \ge p^{-\mu H/8}$, $N=0$ is separated, and $\tilde\tau := \max(\tau, p^{-\mu H})$ yields $2C_d\epsilon^2 N\tilde\tau^{1-d} \le 2C_d N p^{(1-\mu)H}$ and $\epsilon\tilde\tau H^{r-1}p^H \le \epsilon\tau H^{r-1}p^H + N H^{r-1}p^{(1-\mu)H}$ cleanly. |
| **C1-M2** (`nonlinear-boundary.md` §§1, 3) | **RESOLVED** | $h_1 \ge h_{\min}(p,r,d) := \lceil\log_p(6/\theta)\rceil$ ensures $(1-1/p)\theta p^{h_i} - 2 \ge \frac{2}{3}\theta p^{h_i} - \frac{1}{3}\theta p^{h_i} = (\theta/3)p^{h_i}$ for every odd prime $p \ge 3$ and every $r \ge 2, d \ge 2$. |
| **C1-m1–m8** & script fixes | **RESOLVED** | $\gamma = c + 2\kappa d(q-2)$ stated; Prop. 2.1 restricted to $H \ge 4$; $(N + O(qH))^{2/K_q} \ll_{q,d} N^{1/2}H^{1/2}$ fixed; redundant $p/(p-1)$ removed; Theorem Q separates $\epsilon$ and $x$ lower bounds and proves $N_{j+1} \le N_j + pH^{r-1}p^H \le A H^A p^H(j+2)$ inductively; Corollary Q1 states explicit $c_0$ constraints; `(LC)` avoids cutting $X$ by $Z_H$; GF-11 (i) cleaned up; script docstring (`H = 4000`) and `+ kappa / (2 * K - 2)` term in `check_c1_margins` both fixed and pass. |
| **C2-M1 & C2-m1–m2** (`nonlinear-boundary.md` §7) | **RESOLVED** | Proposition D and Summary line 22 now state $L \ge 3$, $C_P$, tightness in density, and $v_p(q_n) \ge rsJ(n) - \omega(n)$ on density one for every $\omega(n) \to \infty$, with an airtight 1-line proof. Real-tail lower bound includes $1/(b-1)$, and $T_n \to 0$ in density at $r=d=2$ includes the Landau + Markov cutoff argument. |
| **C3-C1** (`multivariate-and-dense-allprime.md` §3) | **RESOLVED** | Uniform Lemma 2 replaced by the $L^1(K')$ Lebesgue-point localization: $E_0(|I|)$ cutoff with $p^{-\eta_1 E_0} \le |I|$ absorbed by the $+1$ inside $f \in L^1(K')$, GF-11 $n_*$-dimensional lattice count on $I^+ - S(w_{\rm hi})$ (including $O_{E_0}(1)$ for $n_*=1$), $\epsilon_M = \min(\epsilon_0, c_1/M)$, and simultaneous Lebesgue density point of $E$ and Lebesgue point of $f$. Sound. |
| **C3-C2** (`multivariate-and-dense-allprime.md` §§2–3) | **RESOLVED** | Target selection switched to pure lex-min of sorted order tuples; weighted peeling $(*)$ and $(**)$ verified at both free and bounded stages; sequential divisor-bound pigeonhole choice of $(g_j, a_j)$ with $B_{j-1} = \frac{s_m}{s_*}\sum_{i<j}g_i + e_{\rm prec}$ and $|M| \le r p^{d(g_j+1)}$ rigorously forces $M = 0 \implies w_j = y_j$ at every bounded coordinate and $q' = m_*$ at termination. Sound. |
| **C3-M1 & C3-m1–m5** | **RESOLVED** | $\epsilon \le \epsilon_0 = (2C_d)^{-1}p^{-C_g}$ forces $x=z$ even at $n_* = 1$; $r=1$, $r_*=1$ ($T=\{X_{a_*}\}$), $r=2$ ($q=3$), and degree-$1$ competitors ($r_* \ge 2$) all explicitly handled; undefined $e$ removed from $G_0$; $\kappa < \min(1/(2r), 1/(s_m+1))$ and $\lambda \le \kappa/(3s_m)^{n_*-1}$ verified; $\nu'_{a_*} = 0$ separated; $L_{\rm ET} = \lceil p^k H^{n_*+1}\rceil$ stated; Summary updated. |
| **C4-M1 & C4-m1–m5** (`multivariate-and-dense-allprime.md` §§5–8) | **RESOLVED** | Explicit hypothesis $n_{k+1}/n_k \to \infty$ added to Proposition 5.1 Part 3 (with monotone $\psi(k) \to \infty$ example); squarefree $\Lambda_k$ noted in `(P'_r)`; $(c_0\log p)/s < r/d$ and $O_{P,\eta}(N^{-\eta})$ for $\deg P = 1$ added to Theorem H; strictly increasing $k_j$ and $n < \sqrt{N}$ discard added to Theorem U; §8 table and "period bound" wording corrected. |

### Two Non-Blocking Polish Notes Spotted on Re-Read

1. **Corollary Q1 Step 3 (`nonlinear-boundary.md`, line 135):** The added tail `= O(n^{-rs/(2d)})` in $1/G_n \le p^{L+a_0+O(1)} n^{-rs/d} = O(n^{-rs/(2d)})$ is slightly imprecise pointwise when $n \ll N$ because $L = \lfloor c_0 \log N \rfloor$ depends on $N$, not $n$. The **averaged** mesh error $\frac{1}{N} \sum_{n < N} 1/G_n \ll p^L N^{-rs/d} = O(N^{-rs/(2d)})$ (using $rs/d < 1$ and $c_0 \log p < rs/(2d)$) is completely valid; wording line 135 as *"whose average over $n < N$ is $O(p^L N^{-rs/d}) = O(N^{-rs/(2d)})$"* makes it exact.
2. **Theorem M free-part dominance at $m = 1, s_1 = 1$ (`multivariate-and-dense-allprime.md`, line 48):** For $m \ge 2$ distinct orders, $s_m \ge 2$ holds automatically, so $h_{j+1} \ge s_m(\sum g_i + h_1 + \dots + h_j) + G_0$ yields $k_{\rm lo} \le \frac{1}{2} h_j$ and the per-step $B=0$ saving $p^{-h_j/3}$ on line 76. The single-order case $m = 1$ is already covered by GF-11 (line 37); using $\max(2, s_m)$ in line 48 also covers $m = 1, s_1 = 1$ verbatim.

### Updated Sub-Track Verdicts

| Sub-Track | Final Verdict |
|---|---|
| **C1** (`nonlinear-boundary.md` §§1–6, `PowerSumPeeling.lean`, `phase21_nonlinear.py`) | **ACCEPT** *(with 1 minor wording note on line 135)* |
| **C2** (`nonlinear-boundary.md` §7) | **ACCEPT** |
| **C3** (`multivariate-and-dense-allprime.md` §§1–3) | **ACCEPT** *(with 1 minor note on $m=1, s_1=1$ at line 48)* |
| **C4** (`multivariate-and-dense-allprime.md` §§4–8) | **ACCEPT** |

Every Critical and Major finding from the initial review is resolved without introducing any mathematical gap. Phase 21 Track C (C1–C4) is ready for integration (subject to confirming `NormalityChecker/PowerSumPeeling.lean` via `lake build` in an environment with `lake` installed).
