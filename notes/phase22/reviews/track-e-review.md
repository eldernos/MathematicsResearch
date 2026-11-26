# Independent Cross-Provider Mathematical Referee Review: Phase 22 Track E (E1–E3)

- **Reviewer**: Independent cross-provider review sub-agent (Gemini 4 Neon)
- **Date**: 2026-11-26
- **Audited files (read in full)**:
  1. [notes/phase22/classical-targets-and-recon.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md) (390 lines)
  2. [scripts/phase22_classical.py](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py) (860 lines)
- **Cross-checked against**: [papers/09-erdos-borwein-note/paper.tex](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/papers/09-erdos-borwein-note/paper.tex) (CC-49), [notes/phase21/classical-barriers.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md), and independent exact/interval Python checks.
- **Review status disclaimer**: **Cross-model review is not independent human peer review.** This report records an automated cross-provider audit and does not substitute for refereeing by independent human mathematicians.

---

## Verdicts

| Track | Verdict | Summary |
| --- | --- | --- |
| **Overall (Track E)** | **REVISE** | **0 Critical**, **5 Major**, **9 Minor**. Strong mathematical core, disciplined evidence separation, and clean scope hygiene (zero `"brief"` / process language). Five localized mathematical or certification errors need targeted fixes before acceptance. |
| **E1 & E1(a)** ($E$, $E_+$, $r_{\min} \ge 7$) | **REVISE** | Propositions 1.1–1.4, Lemma 1.5, Theorem 2.1, and the exact rational countermodels of Theorem 2.2 are mathematically sound; independent outward-rounded certification confirms $r_{\min}(D) \ge 7$ genuinely holds. Needs **M1** resolved (certify the 5 mod-4 inputs or qualify Cor. 2.3/status matrix as conditional, and round robustness radii downward) plus **m1–m5**. |
| **E2** ($\ln 2$, Kempner–Shallit barrier) | **REVISE** | Proposition 3.1, Corollary 3.2, and the Shallit (1979) attribution are rigorous; $D^+(\ln 2; 2) \le 0.9999$ is clearly kept open. Needs two prose misstatements fixed: **M4** ($\varepsilon > 0$ should be $0 < \varepsilon < 1$ on line 245) and **M5** (composite-period dichotomy fails on line 263), plus **m6**. |
| **E3** ($C$, $\psi$, $C(1/b)$, $\zeta(3)$, $C_1$) | **REVISE** | All five proposition statements (4.1, 4.3–4.6) are true, transcendence of $\psi$ is honestly kept open, and all digit statuses are open. Needs **M2** (false limit $|C - C_K| D_K^3 \to 1.5202$ on line 285: it oscillates between $L \approx 1.5202$ for odd $K$ and $1/L \approx 0.6578$ for even $K$) and **M3** (false carry bound $v_p\binom{2k}{k} \le 1$ at $p = 3, k = 5$ in Prop. 4.5's proof on line 338), plus **m7–m9**. |

---

## 1. Script Execution & Numerical Cross-Check

Running `python -B scripts/phase22_classical.py` in the worktree completed with **exit code 0**:

- `All 300745 checks passed in 4.7s.` (exact match with line 373's `300,745 checks; exits 0`).
- Every displayed table, decimal prefix, shell frequency, discrepancy value, partial quotient prefix, Sylvester order, and Apéry denominator rate matches the script output, **with two minor discrepancies** (**m3**: line 134 prints `0.198677` vs. script's `0.198676`; line 215 prints `E h(N_2) = 0.111493` vs. `section_E1a`'s computed `0.111490`) and one precision rounding artifact (**m8**: Catalan `bit_length()/(3n)`).
- Independent exact modular-convolution verification (`S_k = (2 S_{k-1} + C_k) mod 2^k` for $D \le 16$) confirmed all eight entries of the §1.6 threshold table (lines 154–155) including the unprinted entries ($E$ at $D = 14$, $E_+$ at $D = 10, 11$), verified zero overlap between positive and negative moved cells ($k_{\mathrm{pos}} + k_{\mathrm{neg}} \le 244 \ll 2^{13} = 8192$ at $D = 14$), and confirmed the unprinted $E_+$ carry probabilities of line 136 (`0.506445` on `0`, `0.258617` on `-1`, `0.113263` on `1`).
- Independent guard-bit enclosure checks confirmed that all binary/decimal digits computed in the script for $\ln 2$, $C$, $\psi$, and $C_1$ are free of carry-propagation ambiguity.
- **Scope hygiene**: Zero occurrences of `"brief"`, `"TODO"`, `"FIXME"`, `"TBD"`, or `"placeholder"` in either audited file; all three relative Markdown links in `classical-targets-and-recon.md` resolve to existing files.

---

## 2. Section-by-Section Mathematical Audit Summary

### E1 — $E$, $E_+$, Signed Knapsack, and Comparison Model (§1)
- **Scope & Mira Cult (§1.1, lines 17, 41–51)**: Cleanly scoped. Mira Cult's pinned result (`Mira-Cult/math` commit `1498319`) is neither dismissed nor claimed independently verified; the conditional implication (positive lower density of every fixed word on windows $H \ge N^{7/12+\varepsilon} \implies D^+(E; 2) < 1$, e.g., via the two separated cylinders $00$ and $10$) is valid. All CC-49 enclosures match `papers/09-erdos-borwein-note/paper.tex`.
- **Proposition 1.1 (lines 55–71)**: Sound. $E_+(b) = E(b) - 2 E(b^2) = E_{\rm odd}(b) - E(b^2)$, $a_+(n) = \sum_{d \mid n} (-1)^{d-1} = \tau(n) - 2[2 \mid n]\tau(n/2) = (1 - v_2(n))\tau_{\rm odd}(n)$, vanishing iff $n \equiv 2 \pmod 4$, odd iff $n$ is a square. Borwein (1991) irrationality attribution is accurate.
- **Proposition 1.2 (lines 75–87)**: Sound. $\sum a_+(n) n^{-s} = (1 - 2^{1-s})\zeta(s)^2 = \eta(s)\zeta(s)$, $\sum_{n \le X} a_+(n) = X \ln 2 + \Delta(X) - 2\Delta(X/2) = X \ln 2 + O(\sqrt X)$. Both $a_+^2$ and $\tau^2$ are multiplicative; at $p = 2$, $\sum_{e \ge 0} (1 - e)^2 2^{-e} = 1 + 0 + \frac{1}{2} \cdot 6 = 4$ vs. $\sum_{e \ge 0} (e + 1)^2 2^{-e} = 12$, giving ratio $1/3$ and $\sum_{n \le X} a_+(n)^2 \sim \frac{1}{3} \frac{X \log^3 X}{\pi^2}$.
- **Proposition 1.3 (lines 91–99)**: Sound (with minor slack $2/N$ vs. $1/N$, **m5**). Pseudometric triangle inequalities and $K_2 \subseteq K_4$ (Phase 21 Prop. 2.2) give both implications cleanly.
- **Signed digit identity & Proposition 1.4 (lines 103–121)**: Sound. Since $\lfloor y/M \rfloor = \lfloor \lfloor y \rfloor / M \rfloor$ holds for all real $y$ (including $y < 0$) and integers $M \ge 1$, the CC-49 digit identity transfers verbatim to signed column totals $C(t) \in \mathbb Z$ with nonnegative residues $\bmod 2^D$. The tail-mean calculation $\mu^{\rm pos} = \mu_{\rm odd}/2 \approx 0.70123$ and $\mu^{\rm neg} = \mu_{\rm odd} E_2 / 4 = \mu / 4 \approx 0.51908$ is rigorous ($V_+(m) \le \log_2 m$ and $|C^\pm(t)| \le \sum_{m \le 2t+3} \tau(m)$ handle the displacement strip and tail).
- **Signed model $Q_+$ & Lemma 1.5 (lines 123–160)**: The signed model $Q_+$ is clearly separated from proved theorems about $E_+$. Lemma 1.5 is airtight across all sign cases ($r \ge 2^{D-1}$; $r < 2^{D-1}, c \ge 0$; $r < 2^{D-1}, c < 0 \implies r + c < 0 \iff y^- - y^+ > r \implies y^- > r$). Note that the primal supremum $f_D^{\sup}$ is also attainable as $\varepsilon \to 0$ even under per-column constraints $\mathbb E C_d^\pm \le \mu^\pm$ by placing the single extra negative unit in a uniformly random column $M \in \{D+1, \dots, D+T\}$ and letting $T \to \infty$.

### E1(a) — Hostile Audit of the Order $\ge 7$ Barrier (§2)
- **Theorem 2.1 (lines 182–192)**: Both parts are mathematically sound. Weak duality (Part 1) is exact. Determinacy (Part 2) is rigorously proved: under $Q_\infty$, every odd mark $u \ge 1$ has strictly positive probability $\Pr(U_* = u) > 0$, so every coordinate $N_{d,c}$ is a strictly positive-rate Poisson variable and $Q_\infty$ assigns positive mass to every lattice point in $\{0, \dots, M\}^k$; hence any signed measure $\sigma$ supported on a finite box $S$ annihilating all degree-$\le r$ binomial polynomials yields valid probability laws $Q_\infty \pm \varepsilon \sigma \in \mathcal I_{D, r}$ (sampling exact marks conditionally given residue classes and leaving columns $d > D$ untouched). However, line 191 overstates what *non-polynomial* test functions can do to the witness (**m1**).
- **Theorem 2.2 & Corollary 2.3 (lines 196–221)**:
  - **Exact membership in $\mathcal I_{D, r}$ ($D \ge 2$)**: Independently verified in exact rational arithmetic. Both `COUNTERMODELS[5]` (17 unique positive rational atoms on $\{0,\dots,10\}^2$) and `COUNTERMODELS[6]` (25 unique positive rational atoms on $\{0,\dots,12\}^2$) sum to $1$ and match $\mathbb E\binom{N_1}{i}\binom{N_2}{j} = \frac{1}{i!\,j!}$ for every $i + j \le r$. Conditional multinomiality of $(N_{d,c})_c$ given $N_d$ ($d = 1, 2$) together with independence of columns $d \ge 3$ forces all mixed marked factorial moments of order $\le r$ on columns $1, \dots, D$ to match $Q_\infty$, and $\mathbb E C_d = \mu$ for $d > D$.
  - **Objective formula & sensitivity bound**: $f(1) = \frac{1}{2} - \frac{1}{2} \mathbb E[(-1)^{N_1} h(N_2)]$ is exact. For probability vectors with $|\Delta \pi_1| \le \delta$ and $|\Delta c_b| \le \delta$, $\lVert \Delta L_n \rVert_1 \le n \lVert \Delta p \rVert_1 \le 2n\delta$ and $\lVert \Delta c \rVert_1 \le 4\delta$, so $|\Delta h(n)| \le (2n+4)\delta$ and $|\Delta \mathrm{obj}| \le \mathbb E[(2N_2+4)\delta] = 6\delta$. Exact radii $-\mathrm{obj}/6$ are `0.00989066` ($r = 5$) and `0.00645705` ($r = 6$).
  - **Certification gap (M1)**: The note and script do **not** currently certify the five mod-4 model inputs, yet Corollary 2.3 (line 217), the status matrix (line 362), and script line 479 state $r_{\min}(D) \ge 7$ unconditionally. Independently, our outward-rounded integer certification (`S = 2^64`, `P = 4000`, `MMAX = 511`, `JMAX = 255`, depth `D = 18`, with $\Pr(c_2 \ne c_2^{(D)}) \le \mu p_0^D \le 7.79 \times 10^{-5}$) ran in `0.61s` and certified $\pi_1 \in [0.752169, 0.752294]$ and
    $$c_0 \in [0.353493, 0.356069],\ c_1 \in [0.342887, 0.345462],\ c_2 \in [0.200876, 0.203451],\ c_3 \in [0.100169, 0.102744],$$
    bounding the maximum possible deviation of the script's 5 values from the exact $Q_\infty$ inputs by `0.002246`, which certifies $f(1) \ge 0.522914$ ($\rho_5$) and $f(1) \ge 0.512613$ ($\rho_6$) strictly above $1/2$.
  - **Unnecessary open problem for $D \ge 17$ (m2)**: Reducing marks in columns $17, \dots, D$ modulo $2^d$ preserves the first digit pointwise and maps $\mathcal I_{D, r}$ into $\mathcal I_{16, r}$, giving $r_{\min}(D) \le r_{\min}(16) \le 92$ for all $D \ge 16$ immediately.

### E2 — $\ln 2$ and the Badly-Approximable Barrier (§3)
- **Proposition 3.1 & Corollary 3.2 (lines 233–246)**: Sound. Shallit (*J. Number Theory* **11** (1979), 209–217) explicitly gives the bounded partial quotients $a_1 = 1$, $a_n \in \{2, 4, 6\}$ ($n \ge 2$) for $\kappa = \sum_{k \ge 0} 2^{-2^k}$, and Lagrange's best-approximation theorem gives $\lVert q\kappa \rVert \ge \lVert q_k \kappa \rVert > \frac{1}{(a_{k+1}+2)q_k} \ge \frac{1}{8q}$ for all $q \ge 1$. The proof of $1 - D_N(\kappa; 2) \le (\log_2 N + 2)^2 / N$ ($N \ge 2$) holds at every step: $L = \lfloor \log_2 N \rfloor \le N \implies \log_2(N+L) + 1 \le \log_2 N + 2$, and $L(\log_2 N + 2) + 2 \le (\log_2 N + 2)^2$. Kempner (1916) transcendence and Marcovecchio (2009) $\mu(\ln 2) \le 3.5746$ are accurate. $D^+(\ln 2; 2) \le 0.9999$ and $\ln 2 \notin K_2$ are clearly recorded as open.
- **Errors found**: Line 245 has the wrong quantifier $\varepsilon > 0$ instead of $0 < \varepsilon < 1$ (**M4**); line 263 states a false dichotomy for composite-period base-2 logarithmic series (**M5**); line 259 has a factor-of-2 slip for $\ln(4/3)$ (**m6**). Note that Gregory's reduced denominator really does have asymptotic size $e^{(2+o(1))K}$ (for any fixed $m$ and large $p \in (2K/(2m+1), 2K/(2m-1))$, the alternating singular terms sum to $\pm \frac{1}{p} \sum_{j=0}^{m-1} \frac{(-1)^j}{2j+1} \not\equiv 0 \pmod p$).

### E3 — Five Benchmark Constants (§4)
- **§4.1 Cahen's constant (lines 271–288)**: Proposition 4.1(a)–(c) and its proof are completely rigorous for both parities of $K$ and composite $s_i$ ($P_K \equiv \pm 1 \pmod{s_i}$ when $K - i$ is odd guarantees $\gcd(P_K, s_i) = 1$, not merely $s_i \nmid P_K$). Davison–Shallit (1991) and Duverney–Shiokawa (2020) attributions are accurate. **Major error (M2)** on line 285: $|C - C_K| D_K^3$ oscillates between $1.520221\dots$ (odd $K$) and $0.657799\dots$ (even $K$) rather than converging to $1.5202$.
- **§4.2 Reciprocal Fibonacci $\psi$ (lines 289–307)**: Proposition 4.3 (Landau's identity) and its proof are rigorous ($r_2(2M) = r_2(M)$ for odd $M$, and $c(N) = r_2(N)/4$ for odd $N$, $\tau_{\rm odd}(N)$ for even $N$). André-Jeannin (1989) and Bundschuh–Väänänen (1994) attributions are accurate, and transcendence of $\psi$ is honestly marked as not established / open. Missing Proposition 4.2 (**m7**).
- **§4.3 Catalan values (lines 308–331)**: Proposition 4.4 and the exponential-mass carry-window obstruction ($T_n \sim \frac{4}{b-4} C_n$, $\log_b T_n = n \log_b 4 + O(\log n)$) are rigorous. Minor precision artifact in script's `bit_length()` approximation of $\log_8 T_n / n$ (**m8**).
- **§4.4 Apéry's $\zeta(3)$ (lines 332–341)**: Proposition 4.5's statement is true, and $\operatorname{den}(A_n) \mid \operatorname{lcm}(1..n)^3 \binom{2n}{n}$ holds for every $n \ge 1$ (since $3 v_p(k) + v_p\binom{2k}{k} \le 2\lfloor \log_p n \rfloor + \lfloor \log_p(2n) \rfloor$, and whenever $\lfloor \log_p(2n) \rfloor = \lfloor \log_p n \rfloor + 1$ the carry into $p^{\lfloor \log_p(2n) \rfloor}$ forces $v_p\binom{2n}{n} \ge 1$). **Major proof bug (M3)** on line 338: the proof asserts $v_p\binom{2k}{k} \le 1$ for $k \le n < 2p$, which fails at $p = 3, k = 5$ ($v_3\binom{10}{5} = 2$).
- **§4.5 $C_1 = [0; 1, 2, 3, \dots] = I_1(2)/I_0(2)$ (lines 342–357)**: Proposition 4.6 and its proof are completely rigorous (including the exact CF identity $|x - p_n/q_n| = 1/(q_n(q_{n+1} + q_n/x_{n+2}))$ and the exponent $-2 - (1+o(1))/n$). Siegel (1929) transcendence attribution is accurate; minor historical attribution looseness in calling the Bessel ratio "Lehmer's formula" (**m9**).

---

## 3. Detailed Findings

### Critical Findings

*None.*

---

### Major Findings

#### M1 — Uncertified Model Inputs Presented as an Unconditional Proved Barrier in Corollary 2.3 and Status Matrix (plus Upward Rounding of Robustness Radii)
- **Files**: [notes/phase22/classical-targets-and-recon.md:25](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L25), [notes/phase22/classical-targets-and-recon.md:213-219](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L213-L219), [notes/phase22/classical-targets-and-recon.md:362](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L362), [notes/phase22/classical-targets-and-recon.md:387](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L387); [scripts/phase22_classical.py:427-480](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L427-L480)
- **Finding**: Theorem 2.2(2) explicitly labels the objective values ($0.529672$ and $0.519371$) as `(model)`, and Open Question 2 (line 387) acknowledges that the five mod-4 inputs ($\Pr(U \equiv 1 \bmod 4)$ and the four carry-residue probabilities $\Pr(c_2 \equiv b \bmod 4)$) have not been certified in interval arithmetic. Indeed, `scripts/phase22_classical.py` computes them in uncertified floating point with ad-hoc truncations (`P = 3000`, `MMAX = 1023`, `j <= 300`, `w > 1e-17` leaving `1 - sum(cm) = 3.6e-5` unaccounted for, and no depth-truncation bound). Despite this, Corollary 2.3 (line 217), the Status matrix entry *"proved barrier here: ... $r_{\min} \ge 7$ on any number of columns (Cor. 2.3)"* (line 362), and script line 479 assert $r_{\min}(D) \ge 7$ unconditionally. Additionally, line 215 and script line 477 round the robustness radii $-\mathrm{obj}/6$ **upward** via `%.4f` (`0.00989066 -> 0.0099`, `0.00645705 -> 0.0065`), so *"below $0.0065$"* includes values in $[0.006457, 0.0065)$ where $6\delta > |\mathrm{obj}|$.
- **Actionable Fix**:
  1. **Preferred fix (<40 lines, <1 s)**: Add an outward-rounded integer certification (scale $2^{64}$, $P = 4000$, $M_{\max} = 511$, $J_{\max} = 255$, depth $D = 18$, bounding prime tails by $1/(2(P-1))$ and carry depth truncation by $\Pr(c_2 \ne c_2^{(D)}) \le \mu p_0^D$ via CC-49 Lemma `lem:trunc`) to `scripts/phase22_classical.py`. As verified above, this certifies all five mod-4 inputs to within `0.00225` (less than $35\%$ of the `0.00645` radius) in `0.6s`, making Theorem 2.2(2) and Corollary 2.3 genuinely certified (`f(1) >= 0.5126 > 1/2` for $\rho_6$).
  2. **Alternative fix**: Explicitly qualify Corollary 2.3, line 362, and script line 479 as conditional on certifying the five mod-4 inputs within the robustness radius.
  3. In either case, round the robustness radii **downward** (`0.0098` and `0.0064`), and include the `sum(cm)` missing-mass term in the sensitivity bound if the floating-point `cm` is kept.

#### M2 — False Convergence Claim $|C - C_K| D_K^3 \to 1.5202$ for Cahen's Constant
- **Files**: [notes/phase22/classical-targets-and-recon.md:285](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L285); [scripts/phase22_classical.py:594-600](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L594-L600)
- **Finding**: Line 285 asserts *"and $|C - C_K| D_K^3 \to 1.5202$."* This limit **does not exist**. From $D_K D_{K-1} = \prod_{j < K} s_j = s_K - 1$ and $s_{K+1} - 1 = s_K(s_K - 1)$, the ratio $r_K = D_K^3 / (s_{K+1} - 1) = D_K^2 / (s_K D_{K-1})$ satisfies the exact recurrence
  $$r_K r_{K-1} = \frac{D_K^2 D_{K-1}}{s_K s_{K-1} D_{K-2}} = \frac{D_K D_{K-1}}{s_K} = 1 - \frac{1}{s_K} \to 1.$$
  Thus $|C - C_K| D_K^3$ oscillates between two reciprocal parity limits:
  - **odd $K$**: $1.5194, 1.5202, 1.5202, 1.5202, \dots \to L \approx 1.520221\dots$,
  - **even $K$**: $0.6429, 0.6578, 0.6578, 0.6578, \dots \to 1/L \approx 0.657799\dots$.
  The script concealed the oscillation because lines 594–595 evaluated `ed3` only for `K in (3, 5, 7, 9)` (all odd, since `K < 10` excluded `K = 12`). (Proposition 4.1(c)'s statement $|C - C_K| = D_K^{-3+o(1)}$ remains unaffected.)
- **Actionable Fix**: Replace `$|C - C_K| D_K^3 \to 1.5202$` on line 285 with the parity oscillation ($|C - C_K| D_K^3 \to L \approx 1.5202$ along odd $K$ and $\to 1/L \approx 0.6578$ along even $K$, noting $r_K r_{K-1} = 1 - 1/s_K \to 1$). Update `scripts/phase22_classical.py` lines 594–600 to display both parities (computing `math.exp(3 * math.log(pred) - math.log(s[K + 1] - 1))` for large $K$ so `K = 11, 12` also print without float overflow).

#### M3 — Invalid Carry Bound at $p = 3, k = 5$ in the Proof of Proposition 4.5 (Apéry's Series)
- **File**: [notes/phase22/classical-targets-and-recon.md:338](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L338)
- **Finding**: In the proof of Proposition 4.5, line 338 claims: *"For $k \le n < 2p$, $k \ne p$: $p \nmid k$, and $k + k$ has at most one carry in base $p$, so $v_p\binom{2k}{k} \le 1$ and the term has valuation $\ge -1$."* This is **false for $p = 3$, $k = 5$** (which arises at $n = 5$, where $p = 3 \in (5/2, 5]$ satisfies $p \ge 3$): in base $3$, $5 = (12)_3$, so $5 + 5 = (101)_3$ produces **two** carries and $v_3\binom{10}{5} = v_3(252) = 2$, giving $3$-adic valuation $-2$ for the $k = 5$ term rather than $\ge -1$. (For all $p \ge 5$, writing $k = p + r$ with $1 \le r < p$ gives $p$-digit sum $1 + 1 + c_1 \le 3 < p$, so at most one carry occurs. Because $-2 > -3$, the unique minimum $-3$ at $k = 3$ still holds and Proposition 4.5's statement remains true.)
- **Actionable Fix**: Amend line 338 to state that for $k < p$ or $p \ge 5$ there is at most one carry in $k + k$ base $p$ ($v_p\binom{2k}{k} \le 1$), while at the sole remaining case $p = 3, k = 5$ one has $v_3\binom{10}{5} = 2$; hence every term $k \ne p$ has $p$-adic valuation $\ge -2 > -3$, preserving the unique minimum $-3$.

#### M4 — False Quantifier $\varepsilon > 0$ on Kempner Run Lengths
- **File**: [notes/phase22/classical-targets-and-recon.md:245](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L245)
- **Finding**: Line 245 asserts: *"For every $\varepsilon > 0$, all but $O_\varepsilon(\log N)$ of the first $N$ digits lie in runs of length at least $\varepsilon$ times their starting position."* This is **false for every $\varepsilon \ge 1$**: each zero-run of $\kappa = \sum_{k \ge 0} 2^{-2^k}$ occupies positions $2^k + 1, \dots, 2^{k+1} - 1$, having length $2^k - 1 < 2^k < 2^k + 1$, so **no** run of $\kappa$ has length $\ge 1$ times its starting position (nor can any sufficiently late run exceed $(1 + o(1))n$ because $\mu(\kappa) = 2$).
- **Actionable Fix**: Restrict the quantifier to *"For every $0 < \varepsilon < 1$"* and clarify *"lie in runs (of the binary expansion of $\kappa$) of length at least $\varepsilon$ times their starting position"* so truncation of the final run at $N$ is unambiguous.

#### M5 — False Composite-Period Dichotomy for Base-2 Periodic-Coefficient Logarithmic Series
- **File**: [notes/phase22/classical-targets-and-recon.md:263](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L263)
- **Finding**: Line 263 asserts for a rational combination $\sum u(k) 2^{-k}/k$ with periodic $u \pmod M$: *"Either it retains a positive proportion of top-band primes, or $u$ vanishes on every residue class coprime to its period, in which case it is a Taylor-type series in a radix $2^g$."* This is **false when $M$ has multiple prime factors** (and omits the zero combination $u \equiv 0$). Counterexample: for $M = 6$, put $u(1) = u(5) = u(0) = 0$ and $u(2) = u(3) = u(4) = 1$ (realizing $\frac{1}{2}\ln\frac{4}{3} + \frac{1}{3}\ln\frac{8}{7} - \frac{1}{3}\ln\frac{64}{63}$). Then $u$ vanishes on every residue class coprime to $6$, yet $\operatorname{supp}(u) = (2\mathbb Z \cup 3\mathbb Z) \setminus 6\mathbb Z$ is not contained in $g\mathbb Z$ for any $g > 1$, so it is not a single-radix $2^g$ Taylor-type series.
- **Actionable Fix**: Replace the dichotomy for any nonzero periodic $u \pmod M$ with: let $g = \min\{\gcd(r, M) : u(r) \ne 0\}$ and choose $r$ with $\gcd(r, M) = g$ and $u(r) \ne 0$. Then for every sufficiently large prime $p \in (N/(g+1), N/g]$ with $gp \equiv r \pmod M$, the index $k = gp$ is the unique multiple of $p$ in $[1, N]$ with $u(k) \ne 0$ (any $mp \le N$ has $m \le g$, and $m < g$ forces $\gcd(mp, M) = \gcd(m, M) < g$, so $u(mp) = 0$). Hence a positive proportion of primes in $(N/(g+1), N/g]$ divide the reduced denominator, keeping every nonzero combination inside the OP-11 obstruction.

---

### Minor Findings

#### m1 — Imprecise Claim That Non-Polynomial Test Functions Can Shorten the Moment Witness
- **File**: [notes/phase22/classical-targets-and-recon.md:191](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L191)
- **Finding**: Immediately after stating *"Non-polynomial one-sided test functions on $\Psi_{16}$ (rational, piecewise linear, smoothed) cannot lower $r_{\min}(16)$, and their expectations are not even determined by order-$r$ information"*, the next sentence says *"What they can do is shorten the witness: the interval $9 \le r_{\min}(16) \le 92$ is a gap between a countermodel bound and a particular polynomial witness (Bonferroni–Jordan truncation)."* Because *"they"* refers back to non-polynomial test functions—whose expectations are not determined in $\mathcal I_{16, r}$—this is misleading: closing $9 \le r_{\min}(16) \le 92$ requires an optimized **degree-$r$ polynomial majorant** (the dual of the multivariate moment LP), not a non-polynomial test function.
- **Actionable Fix**: Reword the second sentence to: *"What can shorten the witness is a better degree-$r$ polynomial majorant: the interval $9 \le r_{\min}(16) \le 92$ is a gap between a countermodel bound and a particular polynomial witness (Bonferroni–Jordan truncation)."*

#### m2 — Upper Bound $r_{\min}(D) \le r_{\min}(16) \le 92$ for All $D \ge 16$ Follows Immediately by Mod-$2^d$ Mark Projection
- **Files**: [notes/phase22/classical-targets-and-recon.md:217](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L217), [notes/phase22/classical-targets-and-recon.md:386](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L386)
- **Finding**: Line 217 correctly observes that $\mathcal I_{D,r} \not\subseteq \mathcal I_{16,r}$ as sets of marked column processes (because residue-class counts in columns $17 \dots D$ do not bound $\mathbb E C_d$), and line 386 leaves bounding $r_{\min}(D)$ above for $D \ge 17$ as an open problem. However, for any $D' > D \ge 1$, $r \ge 1$, and $Q \in \mathcal I_{D', r}$, projecting every odd mark $u$ in columns $d \in \{D+1, \dots, D'\}$ to $\tilde u = u \bmod 2^d \in \{1, 3, \dots, 2^d - 1\}$ shifts $\sum_{d \ge 2} C_d 2^{1-d}$ by an even integer, preserving the first digit pointwise ($f_{\tilde Q}(1) = f_Q(1)$) while yielding $\mathbb E_{\tilde Q}[\tilde C_d] = \sum_c c \, \nu_d(c) = \mathbb E[U_* \bmod 2^d] \le \mathbb E[U_*] = \mu$ for $D < d \le D'$ (using only $r \ge 1$). Hence $\tilde Q \in \mathcal I_{D, r}$, so $r_{\min}(D)$ is non-increasing in $D \ge 1$, and **$r_{\min}(D) \le r_{\min}(16) \le 92$ holds unconditionally for every $D \ge 16$**.
- **Actionable Fix**: Add this 4-line projection argument to Corollary 2.3 (improving the record for $D \ge 17$ to $7 \le r_{\min}(D) \le 92$) and trim Open Question 1 accordingly.

#### m3 — Two Minor Numerical Mismatches Between Note and Script Output (plus $\mu^{\rm neg} = \mu/4$)
- **Files**: [notes/phase22/classical-targets-and-recon.md:119](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L119), [notes/phase22/classical-targets-and-recon.md:134](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L134), [notes/phase22/classical-targets-and-recon.md:215](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L215)
- **Finding**:
  1. Line 134 prints `0.198677` for $\mathbb E(-1)^{c_1}$ of $E_+$, whereas `scripts/phase22_classical.py` prints `0.198676` (actual value `0.19867616`).
  2. Line 215 writes *"$\mathbb E h(N_2) = 0.111493$ reproduces CC-49's $\mathbb E(-1)^{c_1}$"*, whereas `section_E1a` computes `EH = 0.11149035` (`0.111490`, matching line 129; `0.111493` is CC-49's `crosscheck.py` reference value coded into the tolerance test on script line 457).
  3. On line 119, $\mu^{\rm neg} = \mu_{\rm odd} E_2 / 4$ simplifies directly to $\mu / 4$, immediately inheriting CC-49's certified enclosure $[0.5190648, 0.5190822]$.
- **Actionable Fix**: Change `0.198677` to `0.198676` on line 134, change `0.111493` to `0.111490` on line 215 (or print `EH` in the script and cite the printed value), and optionally note $\mu^{\rm neg} = \mu/4$ on line 119.

#### m4 — Off-by-1 Digit-Index Label on Binary Shells
- **Files**: [notes/phase22/classical-targets-and-recon.md:165](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L165); [scripts/phase22_classical.py:343-348](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L343-L348)
- **Finding**: The slice `bE[1 << sh : 1 << (sh + 1)]` indexes 0-based positions $2^s \dots 2^{s+1} - 1$, which correspond to shifts $n \in [2^s, 2^{s+1})$ and 1-based digits $2^s + 1 \dots 2^{s+1}$ (matching CC-49's shell convention), whereas line 165 and script line 343 label them *"digits $2^s..2^{s+1}-1$"*.
- **Actionable Fix**: Change the label to *"shifts $n \in [2^s, 2^{s+1})$ (digits $2^s+1..2^{s+1}$)"*.

#### m5 — Factor-of-2 Slack in the Shift Bound of Proposition 1.3(1)
- **File**: [notes/phase22/classical-targets-and-recon.md:93-97](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L93-L97)
- **Finding**: Proposition 1.3(1) states $|D_N(2x; 2) - D_N(x; 2)| \le 2/N$ because *"the two $N$-point sets differ in two points."* Because one point is dropped and one added, every interval's count changes by at most $1$, so $|D_N(2x; 2) - D_N(x; 2)| \le 1/N$ holds. (The stated bound $2/N$ is valid.)
- **Actionable Fix**: Optionally tighten $2/N$ to $1/N$ (or note *"differ by removing one point and adding one, changing any interval count by at most $1$"*).

#### m6 — Factor-of-2 Slip in the $\ln(4/3)$ Entry of the §3.4 Table
- **File**: [notes/phase22/classical-targets-and-recon.md:259](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L259)
- **Finding**: Row 3 pairs $\ln\frac{4}{3}$ with $B_{0,2} = \frac{1}{2}\sum 4^{-j}/j$. In fact $B_{0,2} = \frac{1}{2}\ln\frac{4}{3}$ (as line 263 correctly writes), while $\ln\frac{4}{3} = 2 B_{0,2} = \sum 4^{-j}/j$.
- **Actionable Fix**: Write `$2 B_{0,2} = \sum 4^{-j}/j$` in the second column of line 259.

#### m7 — Missing Proposition 4.2
- **Files**: [notes/phase22/classical-targets-and-recon.md:275](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L275), [notes/phase22/classical-targets-and-recon.md:293](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L293)
- **Finding**: Section 4 jumps from Proposition 4.1 directly to Proposition 4.3 (there is no Proposition 4.2).
- **Actionable Fix**: Renumber Propositions 4.3–4.6 to 4.2–4.5 and update cross-references (lines 29–32, 365–367, 378).

#### m8 — Two Minor Numerical/Comparison Imprecisions in §4.1 and §4.3
- **Files**: [notes/phase22/classical-targets-and-recon.md:287](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L287), [notes/phase22/classical-targets-and-recon.md:330](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L330); [scripts/phase22_classical.py:646](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L646), [scripts/phase22_classical.py:776](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L776)
- **Finding**:
  1. In §4.1, $\operatorname{ord}_{s_j}(2)$ is compared against `2 log_2 s_j`. Because $s_j$ first divides $D_{j+1}$ (not $D_j$), the partial sum $C_{j+1}$ tracks $2 \log_2 s_{j+1} \approx 4 \log_2 s_j$ bits (still vanishingly small compared to $\operatorname{ord}_{s_j}(2)$ for $j \ge 4$).
  2. In §4.3, line 330 reports *"exact: $\log_8 T_n / n = 0.633, 0.656, 0.662$ at $n = 100, 400, 1000$"*, which comes from `floor(T_n).bit_length() / 3 / n` on script line 776. Because `bit_length()` rounds $\log_2 \lfloor T_n \rfloor$ upward to the next integer, this shifts the $n = 100$ value by $+0.0028$; the true $\log_8 T_n / n$ values are `0.6305, 0.6552, 0.6614` (`0.631, 0.655, 0.661`).
- **Actionable Fix**: Compare $\operatorname{ord}_{s_j}(2)$ against $2 \log_2 s_{j+1} \approx 4 \log_2 s_j$ in §4.1 (or clarify the index), and compute `(math.log2(Tn.numerator) - math.log2(Tn.denominator)) / (3 * n)` in `scripts/phase22_classical.py` line 776 (updating line 330 to `0.631, 0.655, 0.661`).

#### m9 — Minor Attribution & Denominator-Cap Polish in §4.4–4.5
- **Files**: [notes/phase22/classical-targets-and-recon.md:340](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L340), [notes/phase22/classical-targets-and-recon.md:344](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L344)
- **Finding**:
  1. On line 344, referring to $[0; 1, 2, 3, \dots] = I_1(2)/I_0(2)$ as *"Lehmer's formula (Scripta Math. 29 (1973))"* is slightly imprecise historically: the Bessel-ratio continued fraction dates to Euler (1737/1744) and Gauss (1813), while Lehmer (1973) cataloged and generalized arithmetic-progression continued fractions.
  2. On line 340, while $\operatorname{den}(A_n) \mid \operatorname{lcm}(1..n)^3 \binom{2n}{n}$ is true (giving cap $3/\ln 2 + 2 \approx 6.33$ bits/term), the sharper divisor $\operatorname{lcm}(1..n)^2 \operatorname{lcm}(1..2n)$ gives the tight asymptotic cap $4/\ln 2 \approx 5.77$ bits/term, matching the observed $5.4\text{–}5.8$.
- **Actionable Fix**: Credit Euler/Gauss for the Bessel-ratio continued fraction alongside Lehmer (1973) for arithmetic-progression continued fractions, and optionally note the tighter $4/\ln 2 \approx 5.77$ denominator rate in §4.4.

---

## Post-Repair Verification

- **Date**: 2026-11-26
- **Re-audited files (read in full)**:
  1. [notes/phase22/classical-targets-and-recon.md](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md) (410 lines)
  2. [scripts/phase22_classical.py](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py) (987 lines)
- **Script re-run**: `python -B scripts/phase22_classical.py` exited with **code 0**: `All 301593 checks passed in 4.3s.` (matching line 393's `301,593 checks; exits 0`).
- **Scope hygiene & cross-references**: Zero occurrences of `"brief"`, `"TODO"`, `"FIXME"`, `"TBD"`, or `"placeholder"` in either file; all proposition numbers (`1.1`–`1.4`, `2.4`, `3.1`, `4.1`–`4.5`) and cross-references are consistent with zero stale references.
- **Review status disclaimer**: **Cross-model review is not independent human peer review.**

### Updated Verdicts

| Track | Post-Repair Verdict | Status |
| --- | --- | --- |
| **Overall (Track E)** | **ACCEPT** | All 5 Major (**M1–M5**) and all 9 Minor (**m1–m9**) findings are cleanly resolved; 0 Critical, 0 Major remaining. |
| **E1 & E1(a)** ($E$, $E_+$, $r_{\min} \ge 7$, Prop. 2.4) | **ACCEPT** | **M1**, **m1–m5** verified fixed; new scale-$2^{64}$ integer interval certificate and Proposition 2.4 audited line by line and confirmed sound. |
| **E2** ($\ln 2$, Kempner–Shallit barrier) | **ACCEPT** | **M4**, **M5**, **m6** verified fixed; $D^+(\ln 2; 2) \le 0.9999$ remains cleanly recorded as open. |
| **E3** ($C$, $\psi$, $C(1/b)$, $\zeta(3)$, $C_1$) | **ACCEPT** | **M2**, **M3**, **m7–m9** verified fixed; all five propositions and proofs are airtight. |

### Verification of New Material

1. **Closed form of $h(n)$ ([classical-targets-and-recon.md:215-221](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L215-L221), [phase22_classical.py:457-462](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L457-L462), [phase22_classical.py:564-590](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L564-L590))**:
   - Verified from scratch: $g(x) = \mathrm{Re}(i^x) + \mathrm{Im}(i^x)$ matches $(1, 1, -1, -1)$ on $\mathbb Z/4\mathbb Z$; odd marks satisfy $\mathbb E[i^{U}] = i(2\pi_1 - 1) = it$, so $\mathbb E[i^{S_n}] = t^n i^n$ and $h(n) = t^n \sum_{b=0}^3 \Pr(c_2 \equiv b \bmod 4) g(n + b) = t^n A_{n \bmod 4}$ with $A_2 = -A_0$, $A_3 = -A_1$.
   - The sign/parity grouping `polys[bb % 2][bb]` in `certified_f1_lower` matches $A_0 P_0(t) + A_1 P_1(t)$ across all four residue classes of `bb % 4`, and the script cross-checks the closed form against direct convolution to $< 10^{-12}$ for $n < 20$.

2. **Exact scale-$2^{64}$ outward-rounded integer interval certificate (`certify_mod4_inputs` & `certified_f1_lower`, [phase22_classical.py:501-590](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase22_classical.py#L501-L590), [classical-targets-and-recon.md:221-228](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L221-L228))**:
   - **Mark lower measure**: Every per-prime probability $\lfloor S(p-1)/p^{a+1} \rfloor / S$ and multiplicative convolution step (`px * pu // S`, dropping $y > 511$) rounds strictly downward. For primes $p > P = 4000$, telescoping $\frac{1}{n^2} < \frac{1}{2}(\frac{1}{n-1} - \frac{1}{n+1})$ over odd $n \ge P+1$ gives $\sum_{p > P} p^{-2} < \frac{1}{2P} < \frac{1}{2(P-1)}$, and `big = S - (-(-S // (2*(P-1)))) = floor(S(1 - 1/(2(P-1))))` rounds strictly downward. Thus `p1 <= pi1 <= p1 + miss_nu` is exact.
   - **Column law**: `em1` sums $k = 0 \dots 41$ (ending on a negative term), so `em1 < e^{-1}` rigorously; `b[0]` and every step of the monotone Panjer recursion `// (j * S)` round strictly downward.
   - **Carry & depth truncation**: All $T = 18$ carry steps round strictly downward; `low[b] <= Pr(c^(18) = b mod 4) <= low[b] + miss`. Depth truncation satisfies $\Pr(c \ne c^{(18)}) \le \mathbb E[\lfloor Y_{18} \rfloor] \max_r \Pr(R_{18} = r) \le \mu p_0^{18} < \frac{20763285}{10^7} \cdot (0.5677)^{18} = \delta$ via CC-49 Lemma "depth truncation" and CC-49's certified $\mu \le 2.0763285$ (with $e^{-2} = 0.135335\dots < 0.13534 \implies p_0 < 0.56767 < 0.5677$).
   - **Interval evaluation**: `certified_f1_lower` operates entirely in exact `Fraction` arithmetic over the exact rational intervals `(p_lo, p_hi)`, `(c_lo, c_hi)`. With $t_{\mathrm{lo}} > 0$ checked, splitting $P_m(t) = \mathrm{pos}(t) - \mathrm{neg}(t)$ yields valid monotone enclosures $[P_{\mathrm{lo}}, P_{\mathrm{hi}}]$, and taking the maximum over the four rectangle corners rigorously upper-bounds $A_m P_m(t)$.
   - **Headline bounds verified outward**: Independent exact check confirms exact `f_lo = 0.5289310503... >= 0.528931` ($r = 5$) and exact `f_lo = 0.5188264897... >= 0.518826` ($r = 6$), strictly outward-rounded downward.
   - *Non-blocking cosmetic note*: On lines 471–473 of `phase22_classical.py` (and line 227 of the note), the intermediate 6-decimal display intervals for $\Pr(U \equiv 1 \bmod 4)$ and carry residues use `%.6f` (round-to-nearest) rather than floor/ceil, rounding a few display digits inward by $< 5 \times 10^{-7}$ relative to the exact `Fraction` endpoints (e.g., `p_hi = 0.7522942454` printed as `0.752294`). This does **not** affect the certificate (`certified_f1_lower` uses the exact `Fraction` intervals directly, and the true $Q_\infty$ values sit $> 7 \times 10^{-4}$ inside every endpoint).

3. **Proposition 2.4 (monotonicity in $D$, [classical-targets-and-recon.md:233-237](file:///C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase22/classical-targets-and-recon.md#L233-L237))**:
   - Completely rigorous. Projecting odd marks $u \mapsto u \bmod 2^d \in \{1, 3, \dots, 2^d - 1\}$ in columns $d \in \{D+1, \dots, D'\}$ ($d \ge 2$) shifts $\sum_{d \ge 2} C_d 2^{1-d}$ by an even integer, preserving $c_1 \bmod 2$ and the first digit pointwise, keeping columns $1 \dots D$ and $d > D'$ untouched, and giving $\mathbb E \tilde C_d = \mathbb E[U_* \bmod 2^d] \le \mu$ from the $r \ge 1$ order-1 moment match. Hence $r_{\min}(D') \le r_{\min}(D)$ and $7 \le r_{\min}(D) \le 92$ for all $D \ge 16$.

### Repair Checklist (M1–M5, m1–m9)

| ID | Verification |
| --- | --- |
| **M1** | **Fixed.** Exact scale-$2^{64}$ integer/rational certificate added (`f(1) >= 0.528931` at $r=5$, `>= 0.518826` at $r=6$); robustness radii floored downward to `0.0098` and `0.0064`; Open Question 2 updated. |
| **M2** | **Fixed.** Line 305 states the two parity limits ($L \approx 1.520221$ for odd $K$, $1/L \approx 0.657799$ for even $K$) with $r_K r_{K-1} = 1 - 1/s_K$; script lines 702–718 verify both exact identities and display $K = 3, \dots, 12$. |
| **M3** | **Fixed.** Proposition 4.4's proof (line 358) handles $p = 3, k \in \{4, 5\}$ explicitly ($v_3\binom{10}{5} = 2$, valuation $-2 > -3$); script lines 924–936 check every $3 \le n \le 400$. |
| **M4** | **Fixed.** Line 265 restricts the quantifier to $0 < \varepsilon < 1$, clarifies runs of the infinite binary expansion of $\kappa$, and notes no late run exceeds $(1 + \varepsilon)n$. |
| **M5** | **Fixed.** Line 283 replaces the broken dichotomy with $g = \min\{\gcd(r, M) : u(r) \ne 0\}$ and primes $p \in (N/(g+1), N/g]$ with $p \equiv r_0/g \pmod{M/g}$, including the $M = 6$ composite-period example. |
| **m1** | **Fixed.** Line 191 reworded to *"What can shorten the witness is a better polynomial majorant of degree $r$"*. |
| **m2** | **Fixed.** Proposition 2.4 added (lines 233–237), upgrading $D \ge 17$ to $7 \le r_{\min}(D) \le 92$ across lines 25, 231, 382, 406. |
| **m3** | **Fixed.** Line 134 corrected to `0.198676`; line 229 and script line 465 aligned at `E h(N_2) = 0.111490`; $\mu^{\rm neg} = \mu/4 \in [0.5190648, 0.5190822]$ recorded on lines 21 and 119. |
| **m4** | **Fixed.** Note line 165 and script line 343 relabeled as `shifts n in [2^s, 2^(s+1)), digits 2^s+1..2^(s+1)`. |
| **m5** | **Fixed.** Proposition 1.3(1) (lines 93, 97) tightened to $|D_N(2x; 2) - D_N(x; 2)| \le 1/N$. |
| **m6** | **Fixed.** Line 279 corrected to $2 B_{0,2} = \sum 4^{-j}/j$. |
| **m7** | **Fixed.** Propositions renumbered cleanly to 4.1–4.5 with all references updated. |
| **m8** | **Fixed.** Cahen tracking updated to $2 \log_2 s_{j+1}$ (`5.6..346.2`, line 307 / script line 780); Catalan $\log_8 T_n / n$ computed directly via `log2(num) - log2(den)` (`0.631, 0.655, 0.661`, line 350 / script line 895). |
| **m9** | **Fixed.** Line 364 credits Euler and Gauss alongside Lehmer (1973); line 360 and script lines 912–923 verify $\operatorname{den}(A_n) \mid \operatorname{lcm}(1..n)^2 \operatorname{lcm}(1..2n)$ for all $n \le 400$ ($4/\ln 2 \approx 5.77$ bits/term). |
