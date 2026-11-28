# Phase 26 Track E — Independent Cross-Provider Referee Review (`E1`–`E5`)

**Audited material** (worktree `research/phase-26-arithmetic-amplification`, 2026-11-28):
- [`notes/phase26/constructive-normality-and-reciprocal-spectra.md`](../constructive-normality-and-reciprocal-spectra.md) (246 lines; "the note")
- [`scripts/phase26_constructive_spectra.py`](../../../scripts/phase26_constructive_spectra.py) (558 lines; "the script")
- Cross-references verified against primary repository files: [`notes/phase25/nonlinear-and-badly-approx.md`](../../phase25/nonlinear-and-badly-approx.md) (`GF-46` Lemma 2.2, Theorem 2.3, Theorem 2.4, Theorem 3.1), [`notes/phase25/partitions-and-reciprocals.md`](../../phase25/partitions-and-reciprocals.md) (`GF-45` Theorem E1.2), [`notes/phase23/convergent-reciprocals-and-schedules.md`](../../phase23/convergent-reciprocals-and-schedules.md) (`GF-34` Theorem 1, Prop. 1.3), and [`notes/phase26/reviews/audit-4-gf46.md`](audit-4-gf46.md) / [`notes/phase26/reviews/audit-3-gf45.md`](audit-3-gf45.md) (Audit III & IV context only; all mathematics was reconstructed independently).

**Reviewer.** Independent cross-provider review sub-agent (Gemini 4 Neon), running read-only except for this report. No other file was modified, nothing was committed, WSL was not used, and all Python checks ran directly on Windows (`python -B`).

> **Cross-model review is not independent human peer review.** This report is an automated cross-model audit by an AI model of work produced and previously audited by AI models. It does not replace independent refereeing by human specialists in metric number theory, thermodynamic formalism, Diophantine approximation, or computable analysis. Nothing in this review changes any benchmark status (`BC-01`…`BC-50` or `arithmetic-families.toml`).

---

## Verdict: **REVISE** (targeted revision of Theorem E1.3(2) & (4) only; headline result E2 and E1.1, E1.2, E1.3(1)/(3), E1.4–E1.6, E3–E5 are mathematically sound)

| Severity | Count | Summary |
|---|---:|---|
| **Critical** | 0 | — |
| **Major** | 1 | **M1:** Theorem E1.3(4) asserts *"a band operation that preserves $\delta_{r/D}$ never contracts $x$"*, which is **false** as stated: at $b = 3, D = 2, r = 1$ ($\delta_{1/2}$), $y_0 = 5/2, x_0 = 2/5$, the exact cyclotomic factor $G(u) = \Phi_6(u)/\Phi_3(u)$ has $S_j \equiv 1 \pmod 2$ for all $j$ (preserving $\delta_{1/2}$ on every band) yet strictly contracts $M(x)$ across multiple steps ($0.3000 \to 0.1975 \to 0.1590 \to 0.1401$). In addition, E1.3(2)'s "near-zero first moment" argument does not iterate when $|T_j| > 1$ (points exit $[0, 1/(2|T_j|)]$) and becomes vacuous if $\max_j |T_j^{(k)}| \ge \operatorname{den}(x_{k-1})$, and E1.3(4)'s fold-contraction conclusion omits the approximate-$\delta_{r/D}$ union bound. |
| **Minor** | 9 | Wrap-around imprecision in E1.2(a) displayed equations (`{...} = {...} + O(...)` vs circle distance) + unstated hypotheses; E1.2(b) converse wording; trivial $G = 1$ counted 5 times in the 11 rigidity instances + $x$-side not tested in E1.2(a) script; E1.6 $b = 2$ gap under the quoted $u \ge 3$ Shallit–Kmošek hypothesis; E1.5(2) $\alpha = 1$ and sub-progression fold-independence details; E2.1 supermultiplicativity proof & script checking only $s = 1$; E2.2(3) $1/10$ input caveat; E5 ($\Leftarrow$) direction needs Fischer's inequality or Hadamard equality + compactness, Szegő–Verblunsky–Kolmogorov–Krein attribution, and complex non-symmetric script coverage; minor Reproduction table omission (`E3 size computations: 6`). |

**Headline confirmation.** Every attempt to break **E2** — the lowered computable badly approximable polynomial-normal caps **`M = 14`** (elementary, $L = 344, s = 18/19$) and **`M = 8`** (Weil–Estermann, $L = 226, s = 46/51$) together with all three exact barriers (**`M ≤ 7`** Weil, **`M ≤ 12`** elementary, **`M ≤ 4`** for every $\rho \ge 0$) — **failed to find any error**. The transfer-operator normalization $\Sigma(M, L, s) = (\mathcal{L}_s^L \mathbf{1})(1)$ matches `GF-46` Lemma 2.2 identically with zero off-by-one or missing factors, all five transfer-operator certificates were independently re-certified from scratch in exact rational arithmetic with zero float contamination, and `E3`, `E4`, `E5` all pass full independent verification.

---

## 1. Script execution and float-isolation audit (Mandate 1)

Running `python -B scripts/phase26_constructive_spectra.py` on Windows (Python 3.13) exits **`0`** in **12.5 s** and prints:

> `All Phase 26 Track E exact finite certificates passed (12.5s).`

Every count in the note's Reproduction table (lines 217–235) matches the script output verbatim (`112 536`, `1 563`, `11`, `7`, `1`, `240`, `2 301`, `42`, `24`, `17`, `18`, `3 125`, `4 000`, `5`, `100`, `8`, `2`, `50 / 54 / 36`); the script also logs `E3 size computations: 6`, omitted from the table (m9).

**AST float audit.** I parsed `scripts/phase26_constructive_spectra.py` with Python's `ast` module and enumerated every `float` literal and `float(...)` call across all functions. The **only** occurrences are:
- `candidate_h` (lines 285, 292: `1.0`), which computes a float heuristic guess;
- `transfer_certificate` (line 304: `float(s)` passed exclusively to `candidate_h`);
- `finite_measurements` (line 536: `0.9`), which is purely descriptive (`[finite]`) and contains no assertions.

Immediately after `candidate_h` returns (line 305), `H = [Fr(round(v * 10 ** 12), 10 ** 12) for v in hf]` converts the candidate to exact `fractions.Fraction` objects. Thereafter `hf` and `lam_float` are never touched by any assertion: strict positivity/monotonicity (`H[i] > H[i+1] > 0`), piecewise-linear evaluation (`hev`), integer $Q$-th root bracketing (`pow_bounds` with self-certifying `assert pow(lo, Q) * den <= num <= pow(hi, Q) * den`), all 4,000 interval inequalities, and the even-$L$ check (`lam ** L * ratio > 1 and L % 2 == 0`) execute **strictly in exact `int` and `Fraction` arithmetic**. **Zero floats enter any exact theorem certificate.**

---

## 2. Audit of E2 — Headline caps `M = 14 / 8` and barriers `M ≤ 7 / 12 / 4` (Mandate 2)

### 2.1 Exact check of $\Sigma(M, L, s) = (\mathcal{L}_s^L \mathbf{1})(1)$ against `GF-46` Lemma 2.2

In [`notes/phase25/nonlinear-and-badly-approx.md`](../../phase25/nonlinear-and-badly-approx.md) (lines 19 and 237), for $\mathbf{u} = (a_1, \dots, a_L) \in \{1, \dots, M\}^L$:
$$
M_{\mathbf{u}} = \begin{pmatrix} 0 & 1 \\ 1 & a_1 \end{pmatrix} \cdots \begin{pmatrix} 0 & 1 \\ 1 & a_L \end{pmatrix} = \begin{pmatrix} p_{L-1}(\mathbf{u}) & p_L(\mathbf{u}) \\ q_{L-1}(\mathbf{u}) & q_L(\mathbf{u}) \end{pmatrix}, \qquad
\Sigma(M, L, s) := \sum_{\mathbf{u} \in \{1, \dots, M\}^L} \bigl(q_L(\mathbf{u}) + p_L(\mathbf{u})\bigr)^{-2s}.
$$

I re-derived both equalities in E2.1 from scratch:
1. **Reversal identity:** Every generator $A_a = \begin{pmatrix} 0 & 1 \\ 1 & a \end{pmatrix}$ is symmetric ($A_a^T = A_a$), so $M_{\mathbf{u}}^T = A_{a_L} \cdots A_{a_1} = M_{\mathbf{u}^{\mathrm{rev}}}$. Comparing the $(2,2)$ and $(1,2)$ entries of $M_{\mathbf{u}}$ with the $(2,2)$ and $(2,1)$ entries of $M_{\mathbf{u}^{\mathrm{rev}}}$ gives $(q_L(\mathbf{u}), p_L(\mathbf{u})) = (q_L(\mathbf{u}^{\mathrm{rev}}), q_{L-1}(\mathbf{u}^{\mathrm{rev}}))$ identically. Since $\mathbf{u} \mapsto \mathbf{u}^{\mathrm{rev}}$ bijects $\{1, \dots, M\}^L$ onto itself,
   $$
   \Sigma(M, L, s) = \sum_{\mathbf{v} \in \{1, \dots, M\}^L} \bigl(q_L(\mathbf{v}) + q_{L-1}(\mathbf{v})\bigr)^{-2s}.
   $$
2. **Transfer-operator iteration:** With $\tau_a(x) = 1/(a + x)$ and $(\mathcal{L}_s f)(x) = \sum_{a=1}^M (a + x)^{-2s} f(1/(a+x)) = \sum_{a=1}^M |\tau_a'(x)|^s f(\tau_a(x))$, induction on $L$ via $T_{(a_L, \dots, a_1)}(x) = (\tau_{a_L} \circ \cdots \circ \tau_{a_1})(x) = \frac{p_L(\mathbf{v}) + p_{L-1}(\mathbf{v}) x}{q_L(\mathbf{v}) + q_{L-1}(\mathbf{v}) x}$ and $|T_{\mathbf{v}}'(x)| = |\det M_{\mathbf{v}}| / (q_L(\mathbf{v}) + q_{L-1}(\mathbf{v}) x)^2 = (q_L(\mathbf{v}) + q_{L-1}(\mathbf{v}) x)^{-2}$ yields
   $$
   (\mathcal{L}_s^L f)(x) = \sum_{\mathbf{v} \in \{1, \dots, M\}^L} \bigl(q_L(\mathbf{v}) + q_{L-1}(\mathbf{v}) x\bigr)^{-2s} f\bigl(T_{\mathbf{v}}(x)\bigr) \qquad (x \in [0, 1]).
   $$
   Setting $f = \mathbf{1}$ and evaluating at $x = 1$ gives $(\mathcal{L}_s^L \mathbf{1})(1) = \sum_{\mathbf{v}} (q_L(\mathbf{v}) + q_{L-1}(\mathbf{v}))^{-2s} = \Sigma(M, L, s)$.

**Verdict on normalization:** **100% exact.** Zero off-by-one error, zero missing $(1 + 1/M)$ or $q(\mathbf{u})$ vs $q(\mathbf{u}) + p(\mathbf{u})$ discrepancy. Independently verified as an exact rational identity across all $2s \in \{1, 2, 3\}$, $M \in \{2, 3, 4\}$, $L \in \{1, 2, 3, 4\}$ with $M^L \le 256$.

3. **Supermultiplicativity:** From $M_{\mathbf{v}\mathbf{w}} = M_{\mathbf{v}} M_{\mathbf{w}}$, we have $q(\mathbf{vw}) + p(\mathbf{vw}) = (q_{\mathbf{v}} + p_{\mathbf{v}}) q_{\mathbf{w}} + (q'_{\mathbf{v}} + p'_{\mathbf{v}}) p_{\mathbf{w}} \le (q_{\mathbf{v}} + p_{\mathbf{v}})(q_{\mathbf{w}} + p_{\mathbf{w}})$ since $p'_{\mathbf{v}} \le p_{\mathbf{v}}$ and $q'_{\mathbf{v}} \le q_{\mathbf{v}}$ for all $L(\mathbf{v}) \ge 1$. Raising to $-2s < 0$ and summing gives $\Sigma(M, L_1 + L_2, s) \ge \Sigma(M, L_1, s)\Sigma(M, L_2, s)$. (Correct; adding the 2-line proof is Minor m6.)

### 2.2 Certificate lemma, interval monotonicity, and independent re-certification

**Certificate Lemma (lines 132–136).** For positive decreasing $h$ on $[0, 1]$, $h(x)/h(0) \le 1 \le h(x)/h(1)$ on $[0, 1]$. Positivity of $\mathcal{L}_s$ gives:
- $\mathcal{L}_s h \ge \lambda h$ on $[0, 1]$ ($\lambda > 0$) $\implies \Sigma(M, L, s) = (\mathcal{L}_s^L \mathbf{1})(1) \ge \frac{1}{h(0)} (\mathcal{L}_s^L h)(1) \ge \lambda^L \frac{h(1)}{h(0)}$;
- $\mathcal{L}_s h \le \lambda h$ on $[0, 1]$ $\implies \Sigma(M, L, s) = (\mathcal{L}_s^L \mathbf{1})(1) \le \frac{1}{h(1)} (\mathcal{L}_s^L h)(1) \le \frac{\lambda^L}{h(1)} h(1) = \lambda^L$ (the factor $h(1)$ cancels identically at $x = 1$).

**Interval monotonicity (lines 320–327 of script).** On $[x_i, x_{i+1}]$ ($x_i = i/K$):
- $x \mapsto (a + x)^{-2s}$ is strictly decreasing, so $(a + x_{i+1})^{-2s} \le (a + x)^{-2s} \le (a + x_i)^{-2s}$;
- $x \mapsto 1/(a + x)$ is decreasing and $h$ is decreasing, so their composition $x \mapsto h(1/(a + x))$ is **increasing**: $h(1/(a + x_i)) \le h(1/(a + x)) \le h(1/(a + x_{i+1}))$;
- $h(x_{i+1}) \le h(x) \le h(x_i)$.

Hence:
- Lower bound: $\sum_a \operatorname{lo}((K/(aK + i + 1))^{P/Q}) \cdot h(K/(aK + i)) \ge \lambda H[i] \implies (\mathcal{L}_s h)(x) \ge \lambda h(x)$ on $[x_i, x_{i+1}]$.
- Upper bound: $\sum_a \operatorname{hi}((K/(aK + i))^{P/Q}) \cdot h(K/(aK + i + 1)) \le \lambda H[i+1] \implies (\mathcal{L}_s h)(x) \le \lambda h(x)$ on $[x_i, x_{i+1}]$.

Both directions, all indices ($aK+i$ vs $aK+i+1$, $H[i]$ vs $H[i+1]$), the piecewise-linear interpolation `hev(y)` on $y \in (0, 1]$ (including $y = 1$ at $a = 1, i = 0$), and the self-certifying integer-root bracket `lo^Q * n^P <= D^Q * K^P <= hi^Q * n^P` are **100% exact**.

**Independent re-certification from scratch.** I wrote a completely independent verifier (not importing the repository script), using a different initial guess ($1/(1+x)$), a different rational rounding denominator ($10^{10}$ vs $10^{12}$), a binary-search integer $Q$-th root instead of Newton's method, and 60-bit power bounds (`Dbits = 60` vs `56`). All five certificates passed independently:

| Certificate | $(M, s)$ | Grid $K$ | Certified $\lambda$ | Independent result |
|---|---|---:|---|---|
| Lower (Regime A) | $(14, 18/19)$ | 1,500 | $501/500$ | **PASS**, even $L = 344$, $\lambda^L h(1)/h(0) \approx 1.001198 > 1$ |
| Lower (Regime B) | $(8, 46/51)$ | 1,500 | $1003/1000$ | **PASS**, even $L = 226$, $\lambda^L h(1)/h(0) \approx 1.003209 > 1$ |
| Barrier (Regime B) | $(7, 9/10)$ | 400 | $99/100 < 1$ | **PASS**, $\Sigma(7, L, 9/10) \le (99/100)^L \to 0$ |
| Barrier (Regime A) | $(12, 17/18)$ | 400 | $199/200 < 1$ | **PASS**, $\Sigma(12, L, 17/18) \le (199/200)^L \to 0$ |
| Barrier ($\forall \rho \ge 0$) | $(4, 5/6)$ | 200 | $19/20 < 1$ | **PASS**, $\Sigma(4, L, 5/6) \le (19/20)^L \to 0$ |

Direct small-$L$ brute-force cross-checks also confirmed $\Sigma(4, 2, 5/6) \le 0.668922 \le (19/20)^2 = 0.9025$, $\Sigma(4, 4, 5/6) \le 0.569671 \le (19/20)^4 = 0.814506$, and $\Sigma(7, 2, 9/10) \le 0.724977 \le (99/100)^2 = 0.9801$.

### 2.3 Compatibility with `GF-46` Theorem 2.3 & 2.4 and barrier completeness

- **Thresholds and parameters:** Eliminating $\beta, \theta$ in `GF-46` (2.5) gives $\frac{2(1-s)}{1-\rho} < s - \frac{1}{2} \iff s > s^*(\rho) := \frac{5-\rho}{2(3-\rho)} = \frac{1}{2} + \frac{1}{3-\rho}$, strictly increasing on $[0, 1)$, with $s^*(0) = 5/6$, $s^*(1/2) = 9/10$, $s^*(3/4) = 17/18$.
- **Exact hypothesis checks:**
  - Regime A: $s = 18/19 > 17/18$ ($324 > 323$), $L = 344$ is **even**, $(\alpha, \beta) = (33/76, 11/304)$.
  - Regime B: $s = 46/51 > 9/10$ ($460 > 459$), $L = 226$ is **even**, $(\alpha, \beta) = (27/68, 43/816)$.
  - Independently verified all five inequalities of `GF-46` (2.5), all five derived exponents $\gamma_1, \dots, \gamma_5 > 0$ of `GF-46` Step 5, and $0 < \eta_{r,s,\rho} < 1$ for $r \in \{1, 2, 3, 7, 20\}$ in exact `Fraction` arithmetic.
  - Checked `GF-46` Lemma 2.2(1),(4), Theorem 2.3, and Theorem 2.4 line by line: $L$ enters only through evenness, $B_{M,L} \le 2(M+1)^L$, and the block stopping-time independence. With the G1 fix from E3, `Theorem E2.2` holds unconditionally as stated (Regime A: no external inputs; Regime B: Weil 1948 + Estermann 1961), giving $q\|qx\| > 1/(M+2)$ ($1/16$ for $M = 14$, $1/10$ for $M = 8$).
- **Barrier deduction (E2.3):** Since $|I_{\mathbf{u}}| = \frac{1}{q_L(q_L + q_{L-1})} \le q_L^{-2}$ and $q_L + p_L \le 2 q_L$, we have $\sum_{\mathbf{u}} |I_{\mathbf{u}}|^s \le 2^{2s} \Sigma(M, L, s) \le 2^{2s} \lambda^L \to 0$ while $\max_{\mathbf{u}} |I_{\mathbf{u}}| \le \phi^{-2(L-1)} \to 0$, proving $\mathcal{H}^s(F_M) = 0$. Consequently no Borel probability measure $\mu$ on $F_{M'}$ ($M' \le M$) can satisfy $\mu(I) \le C |I|^s$ (otherwise $1 = \mu(F_{M'}) \le C \sum_{\mathbf{u}} |I_{\mathbf{u}}|^s \to 0$). All three bullets of **Theorem E2.3** are **completely airtight**. Prior-art framing (line 156) faithfully incorporates Audit IV G2/G4 and honestly marks priority as provisional.

---

## 3. Audit of E1 — Band-multiplier calculus, rigidity, and reciprocal extensions (Mandate 3)

### 3.1 What holds cleanly

- **E1.1 (Support lemma):** $\|Dt\| = D \operatorname{dist}_{\mathbb{T}}(t, (1/D)\mathbb{Z}/\mathbb{Z})$ is exact for all $D \ge 1$. Since $t \mapsto \|Dt\|$ is continuous, nonnegative, and vanishes precisely on $(1/D)\mathbb{Z}/\mathbb{Z}$, weak\* compactness of $\mathcal{P}(\mathbb{T})$ makes the equivalence airtight.
- **E1.2 $S*T = (j+1)$ & Kronecker classification (b)–(c):**
  - $S(u) T(u) = \frac{G(u)}{1-u} \cdot \frac{1}{(1-u)G(u)} = \frac{1}{(1-u)^2} = \sum_{j \ge 0} (j+1) u^j$ holds identically in $\mathbb{Z}\llbracket u \rrbracket$.
  - In (b), eventual periodicity gives $S = A/(1-u^N)$ and $T = B/(1-u^{N'})$ with $A, B \in \mathbb{Z}[u]$, whence $AB = \Pi_N \Pi_{N'}$. Unique factorization in $\mathbb{Z}[u]$ and $G(0) = 1$ give $A = \prod_{d \ge 2} \Phi_d^{a_d}$, $B = \prod_{d \ge 2} \Phi_d^{b_d}$ with $a_d + b_d = \mathbf{1}_{d \mid N} + \mathbf{1}_{d \mid N'}$, forcing $\varepsilon_d = a_d - \mathbf{1}_{d \mid N} = \mathbf{1}_{d \mid N'} - b_d \in \{-1, 0, 1\}$. The converse holds because distinct $\Phi_d$ ($d \ge 2$) are separable, pairwise coprime, and coprime to $1 - u$ (see Minor m2 for wording).
  - In (c), $\bar{S} = G(1)$, $\bar{T} = 1/G(1)$, $\mathrm{Op}(c, l)$ gives $S_j = \min(j+1, c)$ and $T_j = \mathbf{1}[c \mid j]$, and $T_1 = \dots = T_{c-1} = 0$ with $T_0 = 1$ forces $S_j = j + 1$ for $j < c$ from the triangular convolution.
- **E1.3(1) (Mod-$g$ rigidity):** In $(\mathbb{Z}/g\mathbb{Z})\llbracket u \rrbracket$, $S(u) \equiv (1-u)^{-1} \pmod g \iff G(u) \equiv 1 \pmod g \implies T(u) \equiv (1-u)^{-1} \pmod g$, so $T_j \equiv 1 \pmod g$ and $T_j \ne 0$ for all $j \ge 0$. **100% exact.**
- **E1.3(3) (Fold multipliers):** Modulo $1$ on clean fold bands $a \le s < d - H$, $b^{im+s} F + b^s F \equiv (1 + b^t) b^s F$ with $t = im \bmod P_F$, sweeping $g\mathbb{Z}/P_F\mathbb{Z}$ ($g = \gcd(m, P_F)$), which always contains $t = 0$. When $g = 1$, $(s, s+t)$ is uniform on $(\mathbb{Z}/P_F\mathbb{Z})^2$, yielding $\sigma * \sigma$; when $P_F \mid m$, $g = P_F$ yields $(\times 2)_* \sigma$. **100% exact.**
- **E1.4 (Adjacent-to-zero cylinder frequency sums):** For $b^L \ge 3$, $C_{0^L} \cup C_{(b-1)^L}$ is the circle arc $[-b^{-L}, b^{-L})$, whose boundary $\{\pm b^{-L}\}$ avoids $0$ and carries zero $\mu_\alpha$-mass; for $(b, L) = (2, 1)$, the union is $\mathbb{T}$ and $\alpha + 2(1-\alpha)2^{-1} = 1$. Portmanteau yields $f_N(0^L) + f_N((b-1)^L) \to \alpha + 2(1-\alpha)b^{-L}$ and $\liminf f_N(w) \ge (1-\alpha)b^{-L}$. The sign-crossing observation for fold bands ($-b^{s-d} F$ dominates the positive future tail $O(F b^{s-m})$ since $m > d + a$) is accurate.
- **E1.5 (Simultaneous radices $b$ and $b^k$):** $M_b = M_{b^k}$ is exact. In E1.5(2), choosing $L$ divisible by $k$ and coprime to $P_C$ (e.g. $L = k$) maintains $\gcd(q, k) = \gcd(m P_F, k) = \gcd(q, m P_F) = 1$ inductively. I additionally verified that on the progression $n = im + s \equiv 0 \pmod k$, the difference $im \bmod P_F$ depends only on $i$ (uniform by $\gcd(m, P_F) = 1$) while $s \bmod P_F$ is uniform for each fixed $i$ (by $\gcd(k, P_F) = 1$), so $((im+s) \bmod P_F, s \bmod P_F)$ covers $(\mathbb{Z}/P_F\mathbb{Z})^2$ uniformly (checked exhaustively across $k \in \{2, 3, 4, 5, 6\}$ and coprime $P_F, P_C$). See Minor m5 for the $\alpha = 1$ endpoint.
- **E1.6 (Approximation exponents):** $\mu(1/x) = \mu(x)$ is exact. Because every scale condition in `GF-45` is a lower bound on $m_{i+1}$ and $|x - x^{(i)}| \le C b^{-m_{i+1}}$ with $x$ irrational and $\operatorname{den}(x^{(i)}) \to \infty$, imposing $m_{i+1} \ge i \log_b \operatorname{den}(x^{(i)})$ produces Liouville witnesses ($\mu(x) = \mu(1/x) = \infty$) without altering the limit law. For $M_b \cap \mathrm{Bad} \ne \emptyset$, $\sum_{k \ge 0} u^{-2^k} \in M_u$ has $M_N = O((\log N)/N) \to 0$; see Minor m4 for $b = 2$.

### 3.2 Major Finding M1 — Counterexample to E1.3(4) and proof gap in E1.3(2) & E1.3(4)

**Location:** Note line 5 (headline), line 76 (Theorem E1.3(2)), and line 78 (Theorem E1.3(4)).

**Defect 1 — Concrete counterexample to E1.3(4)'s claim *"a band operation that preserves $\delta_{r/D}$ never contracts $x$"*:**
Take radix $b = 3$, $D = 2 \mid (b - 1)$, $r = 1$ (target $\delta_{1/2}$), $y_0 = 5/2$ (exact cycle law $\delta_{1/2}$, $P_y = 1$), and $x_0 = 2/5$ ($P_x = 4$, orbit $\{2/5, 1/5, 3/5, 4/5\}$, cycle mean $M(x_0) = 3/10 = 0.300000$). Apply the exact cyclotomic band factor
$$
G(u) = \frac{\Phi_6(u)}{\Phi_3(u)} = \frac{1 - u + u^2}{1 + u + u^2}, \qquad u = 3^{-l} \quad (4 \mid l).
$$
(This factor is itself one of the 7 $g = 2$ rigidity factors checked in `scripts/phase26_constructive_spectra.py`.)
- Its $y$-multipliers are $S = (1, -1, 1, 1, -1, 1, \dots)$, satisfying $S_j \equiv 1 \pmod 2$ for **all** $j \ge 0$. Thus $(\times S_j)_* \delta_{1/2} = \delta_{1/2}$ on every band, and $y_1 = y_0 G(3^{-l})$ preserves $\delta_{1/2}$ along all prefixes up to $O(1/l)$.
- Its $x$-multipliers are $T = (1, 3, 5, 5, 3, 1, \text{repeat})$, satisfying $T_j \equiv 1 \pmod 2$ for all $j \ge 0$. Yet on the $2/6 = 1/3$ of bands where $T_j = 5$, multiplication by $5$ annihilates $x_0 = 2/5 \pmod 1$!
- Exact integer-arithmetic cycle means confirm strict contraction across **multiple consecutive applications** of $G = \Phi_6/\Phi_3$:
  - $l_1 = 8 \implies M(x_1) = 0.197502 < 0.300000$ (factor $0.6583$; $\operatorname{avg}\|3^n y_1 - 1/2\| = 0.0880$);
  - $l_2 = 48 \implies M(x_2) = 0.159027 < M(x_1)$ (factor $0.8052$);
  - $l_3 = 288 \implies M(x_3) = 0.140055 < M(x_2)$ (factor $0.8807$);
  - at $l_1 = 12, l_2 = 72$: $M(x_0) = 0.300000 \to M(x_1) = 0.198333 \to M(x_2) = 0.150463$, while $\operatorname{avg}\|3^n y_1 - 1/2\| = 0.0586 \to 0$ as $l_1 \to \infty$.

**Defect 2 — Logical gap in E1.3(2)'s "near-zero first moment" proof:**
Line 76 argues: *"Every $x$-band then has $|T_j| \ge 1$. On the near-zero part, $\|T_j t\| = |T_j|\|t\|$ for $\|t\| \le 1/(2|T_j|)$. So the near-zero first moment of the $x$ cycle is multiplied by $\operatorname{avg}|T_j| \ge 1$, up to an error $O(b^{-H} + (a + H)/l)$. Tail errors introduced at any finite scale therefore persist, and no such sequence of operations reaches $M_b$."*

This argument has two gaps whenever $|T_j| > 1$:
1. **Non-invariance across iterations:** Let $M_\delta(x) := \int_{\|t\| \le \delta} \|t\|\, d\sigma_x(t)$ with $\delta = 1/(2 \max_j |T_j|)$. Averaging $\|T_j t\| = |T_j|\|t\|$ over $\|t\| \le \delta$ gives a lower bound on the **total** first moment $M(x') \ge (\operatorname{avg}|T_j|) M_\delta(x) - \text{err}$, **not** on $M_\delta(x')$. Points in $(\delta/|T_j|, \delta]$ are mapped *out* of $[0, \delta]$ by $\times T_j$, so $M_\delta$ can drop (and points pushed into $(\delta, 1/2]$ can later wrap around $1$). Only when $|T_j| = 1$ for all $j$ (so $\delta = 1/2$ and $M_\delta = M$) does this bound iterate cleanly as written.
2. **Vacuity for finite denominators / growing $|T_j^{(k)}|$:** For any rational $x_{k-1}$, every nonzero orbit point satisfies $\|t\| \ge 1/\operatorname{den}(x_{k-1})$. Whenever $\max_j |T_j^{(k)}| \ge \operatorname{den}(x_{k-1})$ (as in our counterexample where $\max|T_j| = 5 = \operatorname{den}(2/5)$), the near-zero region $\{0 < \|t\| \le 1/(2\max|T_j|)\}$ is **empty** and $M_\delta(x_{k-1}) = 0$, so the inequality yields only $M(x_k) \ge 0$.

**Defect 3 — Missing approximate-$\delta_{r/D}$ & interleaving argument in E1.3(4):**
In line 78, after a fold of ratio $\rho$, $y$ is no longer supported strictly on $\{r/D\}$, so in subsequent GF-45 coprime folds ($g = 1$), fold-band points sum two independent draws $b^{im+s} F + b^s F$ rather than literally doubling a single point. For pure GF-45 folds this is easy to close rigorously: if $p_j := \sigma_j(B_\eta(r/D))$ with $\eta < 1/(4D)$, then by the union bound both $b^{im+s} F$ and $b^s F$ lie in $B_\eta(r/D)$ on at least $1 - 2(1 - p_j)$ of the fold band, sending that mass into $B_{2\eta}(2r/D)$ (disjoint from $B_\eta(r/D)$), whence $p_{j+1} \le (1-\rho_j) p_j + 2\rho_j(1 - p_j) = p_j - \rho_j(3p_j - 2)$; if $p_j \to 1$ with $\sum \rho_j = \infty$, eventually $p_{j+1} \le p_j - \frac{1}{2}\rho_j$, contradiction. However, in the **interleaved** claim of E1.3(4), one cannot deduce that divergent total fold ratio is required from the broken single-step band non-contraction claim without first closing Defects 1–2.

**Exact algebraic repair path (recommended to the authors):**
Interestingly, a complete classification of cyclotomic factors $G = \prod_{d \ge 2} \Phi_d(u)^{\varepsilon_d}$ ($\varepsilon_d \in \{-1, 0, 1\}$, finitely many nonzero) satisfying $S_j \equiv 1 \pmod g$ ($\iff G(u) \equiv 1 \pmod g$) **completely repairs every case with $g \ge 3$** (covering all $b \ge 4$ in E1.3(2) and all $D \ge 3$ in E1.3(4)):
- **If an odd prime $p \mid g$:** For $p \nmid m$, $\Phi_{p^k m}(u) \equiv \Phi_m(u)^{(p-1)p^{k-1}} \pmod p$ ($k \ge 1$), and distinct $\Phi_m$ are pairwise coprime and separable over $\mathbb{F}_p$. Hence $G \equiv 1 \pmod p$ forces $\varepsilon_m + (p-1)\sum_{k \ge 1} \varepsilon_{p^k m} p^{k-1} = 0$ for every $m$ with $p \nmid m$. Modulo $p - 1 \ge 2$ with $|\varepsilon_m| \le 1$, $\varepsilon_m = 0$; then unique balanced $p$-ary representation forces $\varepsilon_{p^k m} = 0$ for all $k \ge 1$. Thus **$G = 1$ identically**.
- **If $4 \mid g$:** Modulo $2$, $\varepsilon_{2^k} = 0$ for $k \ge 1$, and for each odd $m \ge 3$, $\varepsilon_m + \varepsilon_{2m} + \sum_{k \ge 2} 2^{k-1} \varepsilon_{2^k m} = 0$ forces each nontrivial $m$-component $G_m$ to have the form $(\Phi_m(u^{2^{r-1}}) / \Phi_m(-u^{2^{r-1}}))^{\pm 1}$ ($r \ge 1$). Writing $\Phi_m(u) = P_m(u^2) + u Q_m(u^2)$, squarefreeness of $\Phi_m \bmod 2$ forces $Q_m \not\equiv 0 \pmod 2$, so $G_m \equiv 1 + 2 R_m(u) \pmod 4$ with nonzero $R_m \in \mathbb{F}_2(u)$ having poles solely at roots of $\Phi_m$. By partial fractions over $\overline{\mathbb{F}_2}$, distinct odd $m$ cannot cancel, so **$G = 1$ identically**.
- **Only $g = 2$** admits nontrivial cyclotomic factors (precisely finite products of $(\Phi_m(u^{2^{r-1}}) / \Phi_m(-u^{2^{r-1}}))^{\pm 1}$ over distinct odd $m \ge 3$, matching the script's 6 nontrivial $g = 2$ hits and our search over $d \le 15, k \le 3$ giving `{2: 8, 3: 0, 4: 0, 5: 0, 6: 0, 8: 0, 9: 0}`).

Using this classification:
1. For cyclotomic band operations with $g \ge 3$ (all $b \ge 4$ in E1.3(2) and all $D \ge 3$ in E1.3(4)), no nontrivial operation exists at all ($G = 1$).
2. For $g = 2$ (i.e. $b = 3$ or $D = 2$), revise E1.3(2) and E1.3(4) to: (a) state precisely what Part 1 gives universally (**no zero bands**, $T_j \ne 0$ for all $j$, excluding denominator-independent contraction as in GF-34 $\mathrm{Op}(c, l)$); (b) drop the false single-step claim *"a band operation that preserves $\delta_{r/D}$ never contracts $x$"* (acknowledging denominator-specific wrap-around such as $G = \Phi_6/\Phi_3$ on $x_0 = 2/5$); (c) either prove directly that no nontrivial cyclotomic factor has every $S_j$ a power of $3$ (for E1.3(2) at $b = 3$) or restrict E1.3(2)/(4)'s persistence claim to $|T_j| = 1$ (or supply a complete proof for general $g = 2$ sequences); and (d) insert the 2-line union-bound proof $p_{j+1} \le p_j - \rho_j(3p_j - 2)$ for GF-45 folds.

---

## 4. Audit of E3, E4, and E5 (Mandate 4)

### 4.1 E3 — G1 fix, regression, and complexity

- **G1 fix & regression:** Independently verified with binary-search integer roots (`bs_iroot`) on $M = 30, L = 2, s = 10/11$ ($P = 20, Q = 11$, $B_{30, 2} = 931$):
  - Naive rule (`sum(a) > D` without `min(a) >= 1`): $D = 14\,200$ is indeed the **exact least** $D$ with $\sum a_N > D$, giving $\sum a_N = 14\,206$ with **461 of 900** weights equal to $0$ (reproducing Audit IV G1).
  - Exact integer fix $D^Q \ge B_{M,L}^P$: least solution is **$D^* = 250\,087$** ($250086^{11} < 931^{20} \le 250087^{11}$), where $\min a_N = 1$, $\sum a_N = 256\,073 > 250\,087$, and every weight is positive and satisfies $a_N^Q N^P \le (D^*)^Q$.
  - For general $(M, L, s)$ with $\Sigma(M, L, s) > 1$, $a_N > D N^{-2s} - 1$ ensures $\sum a_N > D$ once $D(\Sigma - 1) \ge M^L$.
- **Alphabet and $B_{M,L}$ sizes:** Since $A_a = \begin{pmatrix} 0 & 1 \\ 1 & a \end{pmatrix}$ is entrywise nonnegative and increasing in $a$, $B_{M,L} = \max_{\mathbf{u}} (q_L + p_L)(\mathbf{u}) = (q_L + p_L)([M]^L)$ is exact. Independently confirmed all digit counts in line 182 (`(100, 52)`: 105 / 105; `(42, 4)`: 7 / 7; `(14, 4)`: 5 / 5; `(14, 344)`: 395 / 396; `(8, 226)`: 205 / 206).
- Complexity and non-effective rate remarks accurately reflect `GF-46` §7 Q4 and Audit IV m10.

### 4.2 E4 — Folding attribution and Representation Lemma

- Attribution of `GF-46` Theorem 3.1(1) to Mendès France (1973) and van der Poorten–Shallit (1992) resolves Audit IV G3.
- **Representation Lemma (line 189):** Fix $b \ge 2$, primes $\ell_1 < \ell_2 < \cdots$ with $\ell_n \nmid b$, and $S = \sum_{n \ge 1} \ell_n^{-1} b^{-n}$. For every $x \notin S + \mathbb{Z}[1/b]$, $\{x - S\}$ has a unique base-$b$ digit expansion $\sum_{n \ge 1} d_n b^{-n}$ ($d_n \in \{0, \dots, b-1\}$), giving $x = \lfloor x - S \rfloor + \sum_{n \ge 1} (d_n + 1/\ell_n) b^{-n}$.
  - Coefficients satisfy $0 < 1/\ell_n \le d_n + 1/\ell_n \le b - 1 + 1/2 < b$ (full density, strictly in $(0, b)$).
  - For the $N$-th shifted prefix $R_N = b^N \lfloor x - S \rfloor + \sum_{n=1}^N d_n b^{N-n} + \sum_{n=1}^N b^{N-n}/\ell_n$, each prime $\ell_m$ ($1 \le m \le N$) appears with exact $\ell_m$-adic valuation $-1$ in the $n = m$ term (since $\ell_m \nmid b$) and $\ge 0$ in every other term, while all primes $\ell \notin \{\ell_1, \dots, \ell_N\}$ have valuation $\ge 0$. Hence $\operatorname{den}(R_N) = \prod_{n=1}^N \ell_n$ identically.
  - Independently verified across $b \in \{2, 3, 6, 10\}$ and $N = 1, \dots, 12$. **100% sound.**

### 4.3 E5 — Toeplitz Gram matrices and the determinant sandwich

- **Exact formulas (item 1):** $T_r(\mu_\alpha) = (1 - \alpha) I + \alpha J$ has eigenvalues $1 - \alpha$ (multiplicity $r - 1$) and $1 + (r - 1)\alpha$ (multiplicity $1$), giving $\det G_r = (1 - \alpha)^{r-1}(1 + (r - 1)\alpha)$ and $(\det G_r)^{1/r} \to 1 - \alpha$. For $\mu = \sum c_j \pi_j + c_0 \lambda$, $T_r(\pi_j) \succeq 0 \implies T_r(\mu) \succeq c_0 I \implies \det T_r(\mu) \ge c_0^r$, and by the Verblunsky–Kolmogorov–Krein extension of Szegő's theorem the singular part drops out, leaving Szegő limit $c_0$. Purely atomic $\mu$ of support size $m$ gives $\operatorname{rank}(T_r(\mu)) \le m$, so $\det T_r(\mu) = 0$ for all $r > m$.
- **Sandwich inequality (item 2):** Let $E = T_r(\nu) - I$. Then $E$ is Hermitian with $\operatorname{tr}(E) = 0$ and $\|E\|_F^2 = 2 \sum_{k=1}^{r-1} (r - k)|\hat{\nu}(k)|^2 = 2 F_r(\nu)$. When $F_r(\nu) \le 1/8$, every eigenvalue $\lambda_m$ of $E$ satisfies $|\lambda_m| \le \|E\|_{\mathrm{op}} \le \|E\|_F = \sqrt{2 F_r(\nu)} \le 1/2$.
  - $f(\lambda) := \log(1+\lambda) - \lambda + \lambda^2$ has $f(0) = 0$ and $f'(\lambda) = \frac{\lambda(1+2\lambda)}{1+\lambda}$, which has the same sign as $\lambda$ on $[-1/2, 1/2]$, so $\log(1+\lambda) \ge \lambda - \lambda^2$.
  - $g(\lambda) := \lambda - \lambda^2/4 - \log(1+\lambda)$ has $g(0) = 0$ and $g'(\lambda) = \frac{\lambda(1-\lambda)}{2(1+\lambda)}$, which has the same sign as $\lambda$ on $[-1/2, 1/2]$, so $\log(1+\lambda) \le \lambda - \lambda^2/4$.
  - Summing over $\lambda_1, \dots, \lambda_r$ with $\sum \lambda_m = 0$ and $\sum \lambda_m^2 = 2 F_r(\nu)$ yields $-2 F_r(\nu) \le \log \det T_r(\nu) \le -F_r(\nu)/2$, i.e. $e^{-2 F_r(\nu)} \le \det T_r(\nu) \le e^{-F_r(\nu)/2}$. **100% exact.**
  - Checked the script's rational Taylor enclosures `exp_upper` / `exp_lower` (lines 463–470, 508–509): both round in the certified direction (`d * exp_upper(F/2) <= 1` and `d * exp_lower(2*F) >= 1`).
  - Independently tested **287 random complex non-symmetric probability measures** on $\mathbb{T}$ ($r \in \{2, 3, 4, 5, 6, 8\}$), including boundary instances at $F_r(\nu) = 1/8$: all passed (minimum $\det / e^{-2F} = 1.00123$, maximum $\det / e^{-F/2} = 0.99940$), together with Fischer's inequality $\det T_r \le 1 - |\hat{\nu}(k)|^2$.
- **Equivalence with normality (item 3):** True; see Minor m8 for justifying the ($\Leftarrow$) direction when $F_r(\nu_N)$ is not yet known to be $\le 1/8$.

---

## 5. Complete classified findings

### Critical
None.

### Major

- **M1 (Theorem E1.3(2) & E1.3(4) — Counterexample to single-step band non-contraction and proof gap for persistence/interleaving).** *Locations:* note lines 5, 76, 78.
  - *Issue:* (a) E1.3(4)'s claim *"a band operation that preserves $\delta_{r/D}$ never contracts $x$"* is false: $b = 3, D = 2, r = 1, y_0 = 5/2, x_0 = 2/5, G(u) = \Phi_6(u)/\Phi_3(u)$ has $S_j \equiv 1 \pmod 2$ for all $j$ (preserving $\delta_{1/2}$) yet strictly contracts $M(x)$ across 3 consecutive steps ($0.3000 \to 0.1975 \to 0.1590 \to 0.1401$). (b) E1.3(2)'s "near-zero first moment" proof does not iterate when $|T_j| > 1$ (points leave $[0, 1/(2|T_j|)]$) and is vacuous when $\max_j |T_j^{(k)}| \ge \operatorname{den}(x_{k-1})$. (c) E1.3(4)'s fold argument needs the union bound $p_{j+1} \le p_j - \rho_j(3p_j - 2)$ for approximate $\delta_{r/D}$ laws under coprime folds, and the interleaved conclusion must be aligned with the repaired band statement.
  - *Fix:* Use the complete cyclotomic classification mod $g$ given in §3.2 ($G = 1$ is the unique cyclotomic solution whenever $g \ge 3$), restrict or repair the $g = 2$ persistence statement (drop the false single-step non-contraction claim and state the exact zero-band obstruction $T_j \ne 0$), and include the 2-line union bound for GF-45 folds.

### Minor

1. **m1 — E1.2(a) band-tracking equations fail at $0/1$ wrap-around; missing hypotheses (note lines 50–64).** Writing `{b^n x / G(u)} = {T_j {b^n x}} + O(...)` fails as a real difference when $T_j\{b^n x\} \in \mathbb{Z}$ and the tail is negative (e.g. $b = 3, x = 2, G = 1+u, l = 4, n = 1$ gives real diff $0.9268$, circle distance $0.0732$). Replace with `≡ ... (mod 1)` or circle distance `\|·\|`. Also state boundedness of $h_i$ and preperiod $a$ for $x$, and reconcile $H$ in $a \le m < l - H$.
2. **m2 — E1.2(b) converse wording (note line 68).** Replace *"gives a finite product of simple-pole series"* by *"distinct $\Phi_d$ ($d \ge 2$) are separable, pairwise coprime, and coprime to $1 - u$, so the denominators of $S$ and $T$ divide $1 - u^N$ and $1 - u^{N'}$ respectively"*.
3. **m3 — Rigidity count transparency & $x$-side band-tracking check (script lines 116–134, 153–175; note line 220).** Note that 5 of the 11 "Mod-$g$ rigidity instances" are the trivial factor $G = 1$ (one per $g \in \{2, 3, 4, 6, 9\}$) and the 6 nontrivial instances are all at $g = 2$. Optionally add $x$-side tracking assertions in `e1_band_calculus`.
4. **m4 — E1.6 $M_b \cap \mathrm{Bad} \ne \emptyset$ at $b = 2$ (note line 103).** Line 103 quotes Shallit–Kmošek only for $u \ge 3$; add one clause noting $u = 4 \ge 3$ handles $b = 2$ via $M_2 = M_4$ from E1.5(1) (or cite Shallit 1979 for $u \ge 2$).
5. **m5 — E1.5(2) completeness for $\alpha = 1$ and sub-progression fold independence (note line 97).** Note that $\alpha = 1$ follows immediately from $M_b = M_{b^k}$, and include the 2-line check that $((im + s) \bmod P_F, s \bmod P_F)$ restricted to $im + s \equiv 0 \pmod k$ remains uniform on $(\mathbb{Z}/P_F\mathbb{Z})^2$ since $\gcd(m, P_F) = \gcd(k, P_F) = 1$.
6. **m6 — E2.1 supermultiplicativity proof and multi-$s$ transfer check (note line 130; script line 233).** Add the 2-line matrix proof of $(q+p)(\mathbf{vw}) \le (q+p)(\mathbf{v})(q+p)(\mathbf{w})$ in E2.1, and optionally check $\Sigma(M, L, s) = (\mathcal{L}_s^L \mathbf{1})(1)$ at $2s \in \{1, 2, 3\}$ in the script.
7. **m7 — E2.2(3) input label for $q\|qZ\| > 1/10$ (note line 152).** Specify *"under Regime B (or $> 1/16$ under Regime A with no external input)"* so the Weil–Estermann dependency of $1/10$ is explicit in part (3) as well as part (2).
8. **m8 — E5 ($\Leftarrow$) justification, Szegő attribution, and complex test coverage (note lines 196, 205; script lines 500–510).** In line 205, cite Fischer's inequality $\det T_r(\nu_N) \le 1 - |\hat{\nu}_N(k)|^2$ (or Hadamard's equality condition + weak\* compactness) for $\det T_r(\nu_N) \to 1 \implies$ normality, since the sandwich requires $F_r(\nu_N) \le 1/8$. In line 196, note that removing the singular discrete part in the Szegő limit uses the Verblunsky–Kolmogorov–Krein extension of Szegő's theorem. Optionally include complex non-symmetric Toeplitz instances in `e5_toeplitz`.
9. **m9 — Reproduction table omits `E3 size computations: 6` (note lines 217–235).** Minor completeness omission; all other 22 counters match identically.

---

## 6. Residual scope and disclaimer

This review audited the proofs and finite certificates in `notes/phase26/constructive-normality-and-reciprocal-spectra.md` and `scripts/phase26_constructive_spectra.py` against `GF-46`, `GF-45`, and `GF-34`. It did not independently re-verify external published inputs (Weil 1948, Estermann 1961, Shallit 1979, Kmošek 1979, Szegő/Verblunsky–Kolmogorov–Krein), did not perform specialist literature searches (Audit IV G4 remains open), and did not run on Hail (Track E constraints required direct Windows execution).

**Cross-model review is not independent human peer review.** This verdict is an automated cross-model audit and does not replace refereeing by human specialists.

---

## Post-Repair Verification

**Post-repair audit** (2026-11-28, worktree `research/phase-26-arithmetic-amplification`):
- Repaired note: [`notes/phase26/constructive-normality-and-reciprocal-spectra.md`](../constructive-normality-and-reciprocal-spectra.md) (334 lines)
- Repaired script: [`scripts/phase26_constructive_spectra.py`](../../../scripts/phase26_constructive_spectra.py) (955 lines)

### Post-Repair Verdict: **ACCEPT** (0 Critical, 0 Major, 0 Minor remaining)

Every finding from the initial review (**M1** and **m1**–**m9**) is completely resolved, all newly added theorems and proofs (`Theorem E1.3A`, `Example E1.3B`, `Lemma E1.3C`, `Proposition E1.3D`) have been checked line by line and independently spot-checked, no new mathematical errors or evidence-label regressions were introduced, and all 39 exact finite-certificate counters pass on Windows with zero float contamination.

### 1. Script execution and float-isolation re-check

- Running `python -B scripts/phase26_constructive_spectra.py` on Windows (Python 3.13) exits **`0`** in **18.6 s** (`All Phase 26 Track E exact finite certificates passed (18.6s).`).
- Every one of the **39 certificate counters** printed by the script matches the note's Reproduction table (lines 291–316) verbatim.
- **AST float and division audit:** Every `float` literal and `float(...)` call in the 955-line script remains strictly confined to `candidate_h` (lines 620, 627), `transfer_certificate` (line 639, passing `float(s)` solely to `candidate_h` before immediate rational conversion `H = [Fr(round(v * 10 ** 12), 10 ** 12) for v in hf]`), and `finite_measurements` (line 929, descriptive `[finite]` printout with zero assertions). Every `/` operator outside `candidate_h` and `finite_measurements` operates on `fractions.Fraction` objects, and `dec()` renders exact rationals via `round(Fr(...))` (which returns an exact Python `int`). **Zero floats enter any exact theorem certificate.**

### 2. Line-by-line audit of new results (`E1.3A`–`E1.3D`)

- **Theorem E1.3A (cyclotomic congruence, lines 76–100):** **Sound and complete.**
  - Writing $G = A/B$ with $\Phi_d(0) = 1$ ($d \ge 2$) gives $G \equiv 1 \pmod g \iff A \equiv B$ in $(\mathbb{Z}/g\mathbb{Z})[u]$, reducing $g \ge 3$ to odd prime $p$ and $g = 4$.
  - For prime $p$, the Frobenius identity $\Phi_{p^k m} \equiv \Phi_m^{(p-1)p^{k-1}} \pmod p$ ($p \nmid m, k \ge 1$) together with separability and pairwise coprimality of $\Phi_m$ ($p \nmid m$) over $\mathbb{F}_p$ yields $e_m = \varepsilon_m + (p-1)\sum_{k \ge 1} p^{k-1}\varepsilon_{p^k m} = 0$.
  - For odd $p$, $|\varepsilon_m| \le 1$ and $p - 1 \ge 2$ force $\varepsilon_m = 0$, and the least-term argument forces $\varepsilon_{p^k m} = 0$ for all $k \ge 1$, giving $G = 1$.
  - For $p = 2$, $m = 1$ forces $\varepsilon_{2^k} = 0$. For odd $m \ge 3$, Branch 1 ($\varepsilon_m + \varepsilon_{2m} = 0$) gives $(0, \dots)$ and $\pm(1, -1, 0, \dots)$ ($r = 1$), and Branch 2 ($\varepsilon_m = \varepsilon_{2m} = \pm 1$) solves $\sum_{k \ge 2} 2^{k-2}\varepsilon_{2^k m} = \mp 1$ uniquely digit-by-digit as $\pm(1, \dots, 1, -1)$ on $(m, 2m, \dots, 2^r m)$ ($r \ge 2$), independently verified for $N \le 8$. The cyclotomic identities $\prod_{k<r} \Phi_{2^k m}(u) = \Phi_m(u^{2^{r-1}})$ and $\Phi_{2^r m}(u) = \Phi_m(-u^{2^{r-1}})$ (independently checked for odd $m \le 25, r \le 4$) yield the exact classification $(\Phi_m(v)/\Phi_m(-v))^{\pm 1}$.
  - For $g = 4$, $R_m = \pm v Q_m(v^2)/\Phi_m(\mp v) \equiv (u Q_m(u^2)/\Phi_m(u))^{2^{r-1}} \pmod 2$ has $Q_m \not\equiv 0 \pmod 2$ (separability of $\Phi_m \bmod 2$) and $\deg(u Q_m(u^2)) < \varphi(m) = \deg \Phi_m$ (since $\varphi(m)$ is even), so each $R_m \bmod 2$ is a nonzero proper rational function with a pole at some root $\zeta$ of $\Phi_m$ in $\overline{\mathbb{F}_2}$ where every other $R_{m'}$ is regular; hence $\sum R_m \equiv 0 \pmod 2$ forces $\mathcal{M} = \emptyset$ and $G = 1$.
  - The script certifies all three ingredients (133 Frobenius congruences, 114 squarefreeness and 1,632 pairwise coprimality checks with 3 negative controls, 49 odd-part checks) plus an exhaustive search of all $3^9 = 19\,683$ exponent vectors on $d = 2, \dots, 10$ (unique $G = 1$ for $q \in \{3, 4, 5, 6, 7, 8, 9, 12\}$; exact 9 classified solutions mod 2).
- **Example E1.3B (lines 117–132):** **Sound and exact.** Reproduces the $b = 3, D = 2, G = \Phi_6/\Phi_3$ counterexample in exact rational arithmetic across schedules `(8, 48, 288)` and `(12, 72)`, verifying $P_x, P_y \mid l$ at every step, strict rational decreases in $M(x_k)$, the exact error-free band laws $(2/3)^k \sigma_{x_0} + (1 - (2/3)^k)\delta_0$, and honest **Open** status for the radix-3 $\delta_{1/2}$ target.
- **Lemma E1.3C (lines 134–144):** **Sound and exact.** For $D \ge 2$, $\gcd(r, D) = 1$, $0 < \eta < 1/(3D)$, $z, T_b^t z \in B \implies \|(z + T_b^t z) - 2r/D\| \le 2\eta$ while $\|2r/D - r/D\| = \|r/D\| \ge 1/D > 3\eta$, so $z + T_b^t z \notin B$. By $T_b$-invariance and the union bound, $\nu_F(B) \le 2(1 - p)$ for every offset $t$ (and for $\nu_F = \sigma * \sigma$), yielding $((1-\rho)\sigma + \rho\nu_F)(B) \le p - \rho(3p - 2)$. Cut mass $p/(1+\rho)$ (since $0 \notin B$) and $x$-mean lower bounds ($1/(1+\rho)$ and $1-\rho$) match `GF-45` Cycle Comparison identically. Certified on 396 discrete coprime folds and 644 rational cycle laws across all offsets $t$.
- **Proposition E1.3D (lines 146–152):** **Sound and exact.** For $D \mid b - 1$, $D \ge 3$, $\gcd(r, D) = 1$, Theorem E1.3A(1) forces all $\delta_{r/D}$-preserving periodic band steps to be trivial ($G = 1$). On the $x$ side, $\frac{1}{1+\rho_k} \ge 1 - \rho_k$ and the $2\varepsilon_k$ coupling bound give $M(x_k) \ge (1 - \rho_k - 2\theta_k) M(x_{k-1})$ with $\theta_k = \varepsilon_k / M(x_{k-1})$ summable, forcing $\sum \rho_k = \infty$ whenever $M(x_k) \to 0$. On the $y$ side, the telescoping radii $\zeta_K = 1/(4D)$, $\zeta_k = \zeta_{k-1} - \varepsilon_k \in (1/(6D), 1/(4D)]$ satisfy $\zeta_k + \varepsilon_k = \zeta_{k-1} < 1/(3D)$, so Lemma E1.3C applies cleanly at every step. Weak convergence $\sigma_{y_k} \to \delta_{r/D}$ forces $p_k \to 1$ (every $B_{\zeta_k}$ contains the open arc of radius $1/(6D)$); for $p_{k-1} \ge 5/6$ and $\rho_k < 1/3$, both the fold bound ($3p_{k-1} - 2 \ge 1/2$) and the cut bound ($p_{k-1} - p_{k-1}/(1+\rho_k) \ge \frac{5}{8}\rho_k > \frac{1}{2}\rho_k$) give $p_k \le p_{k-1} - \rho_k/2 + \varepsilon_k$, whence $\sum \rho_k < \infty$, contradiction.

### 3. Finding-by-finding resolution checklist

| ID | Status | Verification in repaired note & script |
|---|---|---|
| **M1** | **Resolved** | False non-contraction claim and flawed near-zero first-moment proof explicitly withdrawn (lines 5, 109, 113). `Theorem E1.3A` closes $b \ge 4$ in E1.3(2) and $D \ge 3$ in E1.3(4); `Example E1.3B` records the exact $g = 2$ contraction; E1.3(2) at $b = 3$ claims only zero-band rigidity plus an exact 798-factor `Finite certificate` (general question marked **Open**); `Lemma E1.3C` and `Proposition E1.3D` rigorously close the fold union bound and $D \ge 3$ interleaved impossibility. |
| **m1** | **Resolved** | E1.2(a) (lines 56–64) restated in circle distance $\|\cdot\|$ modulo 1 with explicit preperiod $a$, $|h_i| \le C_{1/G}$, and margin $H$; script checks 1,280 positions on both $y$ and $x$ sides plus the exact wrap-around example ($38/41$ vs $3/41$). |
| **m2** | **Resolved** | E1.2(b) converse (line 68) cleanly reworded via distinct irreducible $\Phi_d$ coprime to $1 - u$ and $\operatorname{lcm}$ denominators $1 - u^N, 1 - u^{N'}$. |
| **m3** | **Resolved** | Rigidity instances split transparently into 9 trivial ($G = 1$) and 6 nontrivial (all at $g = 2$, inside E1.3A(2)) in both script (lines 204–231) and Reproduction table (line 294); $x$-side band tracking verified. |
| **m4** | **Resolved** | E1.6 (line 177) explicitly handles $b = 2$ via $u = 4 \ge 3$ and $M_2 = M_4$ (E1.5(1)). |
| **m5** | **Resolved** | E1.5(2) (line 171) explicitly proves $\alpha = 1$ via $M_b = M_{b^k}$ and verifies fold-pair uniformity on progressions mod $k$ (plus 1,205 exact checks in script lines 530–547). |
| **m6** | **Resolved** | E2.1 (line 204) supplies the 2-line matrix proof of supermultiplicativity; script checks $\Sigma(M, L, s) = (\mathcal{L}_s^L \mathbf{1})(1)$ at $2s \in \{1, 2, 3\}$ (51 exact identities). |
| **m7** | **Resolved** | E2.2(3) (line 226) and E4 (line 263) explicitly separate $q\|qZ\| > 1/16$ (Regime A, no external input) from $q\|qZ\| > 1/10$ (Regime B, Weil–Estermann input). |
| **m8** | **Resolved** | E5 (lines 270, 279) attributes the singular-part Szegő limit to Verblunsky–Kolmogorov–Krein (`External input`), proves ($\Leftarrow$) via Fischer's inequality (plus Hadamard equality + compactness), and certifies 99 genuinely complex non-symmetric Hermitian Toeplitz instances over $\mathbb{Q}(i)$ (plus Fischer's bound on all 135 instances). |
| **m9** | **Resolved** | Reproduction table (lines 291–316) includes `E3 size computations: 6` and matches all 39 script counters without omission. |

### 4. Evidence-label integrity

All evidence labels (`Paper proof`, `Finite certificate`, `External input`, `Open`) remain strictly separated with zero regressions: `Theorem E1.3A` is unconditional `Paper proof` + `Finite certificate`; `Proposition E1.3D` explicitly states its comparison-regime scope; `Example E1.3B` and the 798-factor radix-3 check are labeled as exact finite computations / `Finite certificate` for a finite family only; `Shallit 1979`, `Kmošek 1979`, `Weil 1948`, `Estermann 1961`, and `Szegő–Verblunsky–Kolmogorov–Krein` are marked `External input`; and no benchmark status (`BC-01`…`BC-50` or `arithmetic-families.toml`) is altered.

> **Cross-model review is not independent human peer review.** This post-repair verification is an automated cross-model audit and does not replace independent refereeing by human specialists.
