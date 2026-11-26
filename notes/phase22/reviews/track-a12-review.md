# Cross-Provider Mathematical Referee Review: Phase 22 Track A (A1–A2)

**Audited files**
- Note: [`notes/phase22/simple-normality-and-signed-transfer.md`](../simple-normality-and-signed-transfer.md) (lines 1–623)
- Script: [`scripts/phase22_simple_normality.py`](../../../scripts/phase22_simple_normality.py) (lines 1–848)

**Verdicts**
- **Track A1 (Digit/word dichotomy in $K_b$ and binary criterion; Theorem A, §§1–4, §10 lines 530–563):** **ACCEPT WITH MINOR POLISH** — Zero Critical and zero Major findings. Lemmas 1.1–1.2, Lemmas 2.1–2.2, Propositions 2.3 and 3.1, Theorems 3.2, 3.4, and 4.1, Corollary 3.3, and Remark 3.5 are mathematically sound and complete. Minor polishes cover the trivial $r \ge \frac12$ branch in Proposition 2.3's proof, the `repunit` identifier clash and missing `open Classical` in §10's proposed Lean block, and vacuous/out-of-hypothesis prefixes in the script's Theorem 4.1(a) check.
- **Track A2 (Oriented-tail transfer, gap-exact signs, specializations, prescribed limits/intervals; Theorem B, §§5–8, §10 lines 564–609):** **REVISE** — Zero Critical findings; every core theorem and proof (Lemma 5.1, Theorems 5.2–5.3, Corollary 5.4(a)–(b), Propositions 6.1, 6.5, 6.6, Lemma 6.2, main displays of Theorem 6.3, Corollary 6.4 for $H \ge 1$, Theorem 6.7, Corollary 7.1, Theorems 7.2–7.3, Lemma 8.0, Theorems 8.1–8.2) is mathematically sound. Revision is requested to fix **2 localized Major findings** (an outright false $O$-bound in the §5 logarithmic-mass remark on line 268, and an unstated infinite-support / $N \le m_K$ hypothesis in the final sentence of Theorem 6.3 on line 325) together with Minor precision and script polishes.

> **Review scope caveat:** This is an automated cross-model mathematical audit, **not** independent human peer review.

---

## 1. Script Execution and Numerical Audit

- **Command:** `python -B scripts/phase22_simple_normality.py` (run from worktree root).
- **Result:** Exit code `0`; `ALL 3342577 CHECKS PASSED in 20.5s`, matching §9 line 507 ("runs in about 20 s, performs about $3.34\cdot10^6$ checks, and exits with status 0").
  - Section timings: `section1`: `0.0s`; `section2`: `3.7s`; `section3`: `0.4s`; `section5to7`: `9.5s`; `section7_identities`: `0.0s`; `section8`: `6.8s`.
- **Exact match with every displayed number and table in the note:**
  - §1 (line 68) & §9 (line 511): `220` interior cases ($3 \le b \le 12$, $1 \le m \le b-2$, $1 \le L \le 4$) — matches verbatim.
  - §2 (line 104), §9 (lines 512–515), §11 (line 617): `1060` prefixes, `922` meeting $\delta < \frac12 - \frac1N$, maximal ratio `0.9091` (independently traced to $b = 10$, $N = 4$, `fam_squares`, where ratio $\approx 0.90908\dots$); `398` dichotomy cases (`259` boundary, `139` interior); `116` binary prefixes (see **Minor 5**); `543` Proposition 3.1 cases — all match verbatim.
  - §6 (line 310): Lemma 6.2(d) sign reversal at $H = (b-1)b^{g-1}+1$ gives $J = 2, 2, 3$ for $g = 1, 2, 3$ in each base $b \in \{2, 3, 10\}$ — matches verbatim (and algebraically $J = \max(2, g)$ for every $b \ge 2$).
  - §7 **Table 7.1** (lines 433–449): all 15 rows × 6 numerical columns (90 entries) match script stdout verbatim.
  - §7 lacunary values (line 451): `0.66602`, `0.33301`, `0.66650`, `0.33325`, `0.66663` for $K = 10, \dots, 14$ in bases $2$ and $3$ — match verbatim.
  - §8 Theorem 8.1 & §9 (line 522): largest ratio `0.241` (attained at $\alpha = (\sqrt5-1)/2$) — matches verbatim.
  - §8 Theorem 8.2 (line 503): `0.75`, `0.234375`, `0.699711`, `0.200037` at $N = 4, 256, 2^{18}, 2^{32}$ — match verbatim (see **Minor 4** on exact vs. rounded phrasing).
- **Independent checks run during audit:**
  - Verified Lemma 2.2 on 464 additional adversarial rational orbits ($b \in \{2,3,4,5,10\}$, $N \in \{3,4,5,10\}$, $\delta = 0$, and perturbations of both signs near $0 \equiv 1$ and every $c_m$).
  - Verified Corollary 5.4(b) (not tested in `phase22_simple_normality.py`) on the polynomial-mass series $a(k^3) = (-1)^k k^4$ ($r = 2, C = 1, c_{2,2} = 6$, $N = 2000, L \in \{1,2,3\}$).
  - Verified Niederreiter's exact formula for unanchored extreme discrepancy in `deficit(Xs, Q)` (lines 318–325), including coincident points and $x_{(1)} = 0$, and verified `beatty_floor` / `golden_times` integer brackets.
  - Verified all relative links and anchors (`../phase19/geometry.md`, `../../NormalityChecker/SharpTranslation.lean`, `../phase20/euler-product.md#2-word-frequencies`, `../phase20/coefficient-transfer.md#11-integral-head-shadows-and-the-exact-mean-tail`) resolve accurately.
  - **Scope & process hygiene:** Confirmed zero occurrences of `"the brief"` or internal process/workflow language in either audited file.

---

## 2. Theorem-by-Theorem Audit Summary

| Component | Audit Outcome | Notes |
|---|---|---|
| **Theorem A & §0** (lines 1–50) | **Sound** (Minor 1, Minor 3) | Notation, cylinder conventions, $\widehat A(X)$ identity, and fixed-point lift $\widetilde F_b$ are exact. Line 30 prose for (0.1) should say $N f_w(N)$ *increases by $0$ or $1$* (not "changes by at most one"). Theorem B's $H$ bound needs $H \ge 1$ (Minor 3). |
| **§1 Lemmas 1.1–1.2** (lines 52–69) | **Sound** | Exact margins $m/((b-1)b^L)$ and $(b-1-m)/((b-1)b^L)$; $\eta_{m,L} < \min(c_m, 1-c_m)$ prevents circle wrap-around; non-enlargeability holds at both sides; boundary splitting in Lemma 1.2 holds even at $b=2, L=1$ (where $\|t\| < 1/2$ excludes $t = 1/2$). |
| **§2 Lemmas 2.1–2.2, Prop 2.3** (lines 70–105) | **Sound** (Minor 1) | Lemma 2.1 matches Lean `SharpTranslation.arc_le` and `interval_eq_arc_excess`. Lemma 2.2 is airtight: midpoint distance $\le \ell/2$ handles wrap-around around $0 \equiv 1$; $N-1-2eN > N-1-2\delta'N \ge 1$ guarantees a consecutive pair; nearest fixed point $c \in F_b$ has $|(b-1)s| \le \frac12$ so $\|(b-1)c'\| = (b-1)r$ unconditionally (even if $\frac{b+1}{2}\ell > \frac12$); constant $\frac12 + \frac{b+1}{2(b-1)} = \frac{b}{b-1}$ and finite-set limit $\delta'_j \downarrow \delta$ work even at $\delta = 0$. Prop 2.3 proof should split off $r \ge \frac12$ (Minor 1). |
| **§3 Prop 3.1, Thm 3.2, Cor 3.3, Thm 3.4, Rem 3.5** (lines 106–169) | **Sound** (Minor 1) | Prop 3.1 boundary cases ($\overline P_\varepsilon$ strict, $E^{\ge}_0$ weak, $b^{-L} \le \frac12$) are exact. Thm 3.2 at $N \ge 4$, $\delta < b^{-L-1} \le \frac14 \le \frac12 - \frac1N$ isolates $r < 1/((b-1)b^L) \le \eta_{m,L}, b^{-L}$ with exclusive alternatives. Cor 3.3 and Thm 3.4 persistence across $N \ge N_0$ and across $L$, limit measures, and non-simple-normality ($b \ge 3$) / non-normality ($b \ge 2$, via $0(b-1)$) are completely rigorous. Minor notation note for $\widetilde c_m$ in Rem 3.5. |
| **§4 Theorem 4.1** (lines 170–199) | **Sound** (Minor 5 in script) | Strict $2\delta < \varepsilon \le \frac12$ correctly bounds $\#\{\varepsilon \le x_n < \frac12\} \le E_0(N, 2\delta) \le \delta N$. Scale-independence in $\varepsilon \in (0, \frac12]$, equivalences (1)–(6), and impossibility of $2$-normality in $K_2$ are airtight. Script test checks 55 out-of-hypothesis prefixes (Minor 5). |
| **§5 Lemma 5.1, Thms 5.2–5.3, Cor 5.4** (lines 200–271) | **Core sound; Major 1, Minor 2** | $x_n = \{T_n\}$, exact zero tails $T_n = 0 \in P_L \cap \Gamma^+$, and boundary values $T_n = \pm b^{-L}$ are handled accurately in Thm 5.2. Thm 5.3 shadow and Markov tail bounds and Cor 5.4(a)–(b) rates are rigorous. **Major 1:** the unproved logarithmic-mass remark on line 268 states a false $O$-bound ($O(\rho_N \log\log N)$). |
| **§6 Prop 6.1, Lem 6.2, Thm 6.3, Cor 6.4, Props 6.5–6.6, Thm 6.7** (lines 272–366) | **Core sound; Major 2, Minor 3–4** | Prop 6.1, Lem 6.2 (with exact sharpness at $H > (b-1)b^{g-1}$), Prop 6.5 (strict $|V_k| \in (\frac1b, b)$ gives $|T_n| > b^{-L}$ so $B_L$ counts them), Prop 6.6 (two-digit alternating expansions), and Thm 6.7 are all sound. **Major 2:** final sentence of Thm 6.3 (line 325) fails for finite support when $N > m_K$. Cor 6.4 needs $H \ge 1$ (Minor 3). |
| **§7 Cor 7.1, Thms 7.2–7.3, Table 7.1** (lines 367–452) | **Sound** (Minor 4) | Cor 7.1, Thm 7.2 (Euler, Jacobi dominance $R^*_k \le \frac{2k+1}{3} + \frac89 < 2k+1$, two-progressions giving all rationals $t/s$, periodic squares), Thm 7.3 (Stolz–Cesàro + gap monotonicity + $\sum(-1)^k b^{-2^k}$ exact $\Gamma^+(2^K)$ and limit set $[\frac13, \frac23]$), and all 90 cells of Table 7.1 check out completely. |
| **§8 Lemma 8.0, Thms 8.1–8.2** (lines 453–504) | **Sound** (Minor 4) | Abel summation $|E| < 2K - 1$ holds strictly for all $\alpha \in \mathbb R, K \ge 1$; Thm 8.1 error $((L+4)\sqrt N + L)/N$ and Thm 8.2 phase-switching envelope $14\sqrt N$ and phase-end bounds are exact. |
| **§9 & Script** (lines 505–525; script lines 1–848) | **Mostly sound; Minor 5–7** | Certification math is solid for all executed families, but `Orbit.nonneg` has a latent bug at `eps_sign = 0` (Minor 6), Thm 4.1(a) check counts 55 out-of-hypothesis prefixes (Minor 5), and §9 overstates Thm 5.3's prefix coverage and float usage (Minor 7). |
| **§10 Lean cores & §11 Scope** (lines 526–623) | **Math sound; Minor 8** | All 12 Lean theorem statements are mathematically true (even at $L = 0, N = 0, K = 0$!). Two Lean 4 elaboration bugs: `def repunit` clashes with `Phase18Synthetic.repunit`, and two `filter` statements need `open Classical` (Minor 8). §11 scope separation is exemplary. |

---

## 3. Detailed Findings

### Critical Findings

None.

---

### Major Findings

#### Major 1 (A2, §5): False big-$O$ bound in the logarithmic-mass remark
- **File / line:** [`notes/phase22/simple-normality-and-signed-transfer.md:268`](../simple-normality-and-signed-transfer.md#L268)
- **Issue:** Line 268 states:
  > *"The logarithmic-mass hypothesis of `log_mass_sparse_tendsto_one` is handled the same way, with $b^k \ge (\log(N+2))^\gamma/\rho_N$. That gives $B'_L(N)/N = O(\rho_N\log\log N)$. This case is recorded as a remark, not proved here in detail."*
  1. **Algebraic slip:** Taking $k = \lceil \log_b((\log(N+2))^\gamma / \rho_N) \rceil$ gives $k = \gamma \log_b\log(N+2) + \log_b(1/\rho_N) + O(1)$, so inserting into Theorem 5.3 yields
     $$\frac{B'_L(N)}{N} = O\Bigl(\rho_N\bigl(\log\log(N+3) + \log(1/\rho_N)\bigr)\Bigr),$$
     **not** $O(\rho_N \log\log N)$. Whenever $\rho_N$ decays faster than $(\log N)^{-A}$ (e.g., $\rho_N = N^{-1/2}$ or $1/N$), the $\rho_N \log(1/\rho_N)$ term dominates $\rho_N \log\log N$.
  2. **The claimed bound $B'_L(N)/N = O(\rho_N \log\log N)$ is false in general** under the hypothesis $A(X) \le C X (\log(X+2))^\gamma$ of `GeneralMassTransfer.log_mass_sparse_tendsto_one`. Explicit counterexample: fix $N \ge 3$ and put $a(N+1) = \lfloor N (\log(N+2))^\gamma \rfloor$ with $a(m) = 0$ for all $m \ne N+1$. Then $A(X) = 0$ for $X \le N$ and $A(X) \le X (\log(X+2))^\gamma$ for all $X \ge N+1$ ($C = 1$ holds for every $X \ge 1$). Here $S(N-1) = 0$, so $\rho_N = 1/N$, yet for $b = 2, L = 1$,
     $$B'_1(N) = \#\{0 \le n < N : a(N+1) 2^{n-(N+1)} \ge \tfrac12\} = \lfloor \log_2 a(N+1) \rfloor + 1 \sim \log_2 N,$$
     giving $B'_1(N)/N \sim \rho_N \log_2 N \gg \rho_N \log\log N$. (Numerically, for $\gamma = 1$, $(B'_1(N)/N)/(\rho_N \log\log(N+3))$ grows from $5.87$ at $N = 10^2$ to $8.59$ at $N = 10^5$.)
  - Note: Although the remark is unproved and not used by any theorem in the paper, the stated $O$-bound is mathematically false. Importantly, the corrected bound $O(\rho_N(\log\log(N+3) + \log(1/\rho_N)))$ **still** tends to $0$ whenever $S(N)\log\log N = o(N)$ (because $\rho_N \log\log N \to 0 \implies \rho_N \to 0 \implies \rho_N \log(1/\rho_N) \to 0$), so the qualitative connection to `log_mass_sparse_tendsto_one` remains valid.
- **Actionable fix:** Replace `"$B'_L(N)/N = O(\rho_N\log\log N)$"` on line 268 with `"$B'_L(N)/N = O\bigl(\rho_N(\log(1/\rho_N) + \log\log(N+3))\bigr)$ (which tends to $0$ whenever $S(N)\log\log N = o(N)$, since $\rho_N \to 0$ implies $\rho_N \log(1/\rho_N) \to 0$)"` — or alternatively note that choosing $b^k \ge (\log(N+2))^{\gamma+1}$ (as in `GeneralMassTransfer.lean`) gives $O(\rho_N \log\log(N+3) + 1/\log(N+2))$.

#### Major 2 (A2, §6): Unstated infinite-support / $N \le m_K$ hypothesis in Theorem 6.3
- **File / line:** [`notes/phase22/simple-normality-and-signed-transfer.md:325`](../simple-normality-and-signed-transfer.md#L325)
- **Issue:** Section 6 explicitly allows the support of $a$ to be **finite or infinite** (lines 274 and 280, defining $G_{K+1} = \{n \ge m_K\}$ and $V_{K+1} = 0$ when the support has last element $m_K$). The final sentence of Theorem 6.3 (line 325) states without restriction:
  > *"Suppose dominance (Lemma 6.2(c)) holds for all $k > k_0$. Then $\mathbf 1[V_k \ge 0] = \mathbf 1[a(m_k) > 0]$ for these $k$, and $\Gamma^+(N)$ is within $m_{k_0}$ of the number of $n < N$ whose next nonzero coefficient is positive."*
  - When the support is **finite** with last element $m_K$ and $N > m_K$, every shift $n \in [m_K, N)$ has $T_n = 0 \ge 0$ (so it IS counted in $\Gamma^+(N)$), yet has **no** next nonzero coefficient (so it is NOT counted in $\#\{n < N : \text{next nonzero coefficient is positive}\}$). For example, if $a(1) = 1$ and $a(m) = 0$ for $m \ge 2$, dominance holds for all $k \ge 1$ ($k_0 = 0, m_0 = 0$), yet $\Gamma^+(N) = N$ while only $n = 0$ has a positive next nonzero coefficient — a difference of $N - 1$, not $\le m_0 = 0$.
- **Actionable fix:** Restrict line 325 to infinite support (or add `"for $N \le m_K$ when the support is finite with last point $m_K$"`), and clarify that in the finite-support case all $n \ge m_K$ have $T_n = 0$ and contribute to $\Gamma^+(N)$ via $G_{K+1}$.

---

### Minor Findings

#### Minor 1 (A1, §0 & §2–§3): Proof and wording polishes in Proposition 2.3, §0 (0.1), and Remark 3.5
- **Files / lines:**
  - [`notes/phase22/simple-normality-and-signed-transfer.md:30`](../simple-normality-and-signed-transfer.md#L30)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:102`](../simple-normality-and-signed-transfer.md#L102)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:168`](../simple-normality-and-signed-transfer.md#L168)
- **Issues:**
  1. **Proposition 2.3 (line 102):** The proof applies Lemma 2.1(a) to the arc $[c - r, c + r + \eta)$ of length $\ell = 2r + \eta$ and lets $\eta \downarrow 0$. Lemma 2.1 requires $0 \le \ell \le 1$, so this argument requires $r < \frac12$ (with $0 < \eta \le 1 - 2r$). For $r \ge \frac12$, the bound $\delta_N(z) \le 1 \le 2r + E_c(N, r)/N$ holds trivially.
  2. **Equation (0.1) prose (line 30):** Saying *"Since $N f_w(N)$ changes by at most one"* is slightly imprecise: a change of $-1$ from $N f_w(N) = N$ would give $f_w(N+1) - f_w(N) = -2/(N+1)$. Because $N f_w(N)$ *increases by $0$ or $1$* (so $f_w(N+1) - f_w(N) = (\epsilon - f_w(N))/(N+1)$ with $\epsilon \in \{0, 1\}$ and $f_w(N) \in [0, 1]$), the step is bounded by $1/(N+1)$.
  3. **Remark 3.5 (line 168):** $\widetilde c_m$ is written without prior definition (only $c_m$ and $\widetilde F_b = (b-1)^{-1}\mathbb Z$ were defined on lines 36 and 42); since $\{M_N \to 0\}$ is $\mathbb Z$-invariant, writing $c_m + \{M_N \to 0\}$ (or defining $\widetilde c_m = c_m + \mathbb Z$) is cleaner.
- **Actionable fix:** Add one clause splitting off $r \ge \frac12$ in Proposition 2.3; tighten line 30 to *"increases by $0$ or $1$"*; replace $\widetilde c_m$ with $c_m$ (or define it) on line 168.

#### Minor 2 (A2, §5): Empty final-group case in proof of Theorem 5.3
- **File / line:** [`notes/phase22/simple-normality-and-signed-transfer.md:244`](../simple-normality-and-signed-transfer.md#L244)
- **Issue:** Line 244 writes *"All $n < N$ without occupied index in $(n, N-1]$ share one next occupied index $m^* \ge N$, and lie in $[m^* - L', N-1]$."* When the support has no element $\ge N$ (e.g., finite support with $m_K < N$), no such $m^*$ exists; those shifts are not shadowed at all and contribute $0 \le L'$ to $W$.
- **Actionable fix:** Add `"(if any occupied index $\ge N$ exists; otherwise they contribute $0$ to $W$)"` on line 244.

#### Minor 3 (A2, Intro & §6): Missing $H \ge 1$ hypothesis in Theorem B and Corollary 6.4
- **Files / lines:**
  - [`notes/phase22/simple-normality-and-signed-transfer.md:12-18`](../simple-normality-and-signed-transfer.md#L12-L18)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:329-335`](../simple-normality-and-signed-transfer.md#L329-L335)
- **Issue:** Corollary 6.4 defines $\kappa_{b,H} = \lceil \log_b(bH/(b-1)) \rceil - 1$ and asserts in the proof (line 335) that *"Since $bH/(b-1) > 1$, $\kappa_{b,H} \ge 0$. Also $\kappa_{b,H} = 0$ iff $bH/(b-1) \le b$ iff $H \le b-1$."* If $H = 0$, $\log_b(0)$ is undefined (and for non-integer $0 < H \le (b-1)/b$, $bH/(b-1) \le 1$ gives $\kappa_{b,H} < 0$). Notably, the Lean signature `badTail_card_le` on line 598 already includes `(hH : 1 ≤ H)`.
- **Actionable fix:** State $H \ge 1$ (e.g., an integer $H \ge 1$) explicitly in Theorem B (line 12) and Corollary 6.4 (line 329), and likewise in Corollary 7.1 (line 375).

#### Minor 4 (A2, §§6–8): Small edge-case, citation, and wording polishes
- **Files / lines:**
  - [`notes/phase22/simple-normality-and-signed-transfer.md:280-296, 315-317`](../simple-normality-and-signed-transfer.md#L280-L296)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:365`](../simple-normality-and-signed-transfer.md#L365)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:375`](../simple-normality-and-signed-transfer.md#L375)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:503`](../simple-normality-and-signed-transfer.md#L503)
- **Issues:**
  1. **Finite-support trailing gap (lines 280–296, 316):** When the support is finite with last point $m_K$, $m_{K+1}$ and $g_{K+1}$ are undefined: Proposition 6.1's formula $T_n = b^{-(m_k - n)} V_k$ applies to $k \le K$ (on $G_{K+1}$, $T_n = 0$ directly); Lemma 6.2(b) assumes $m_{k+1}$ exists (for $k = K$, $R^*_K = 0$ trivially); and Theorem 6.3's display $\min(g_k, \lambda_k)$ implicitly uses $g_{K+1} = \infty$ with $\min(\infty, 0) = 0$. Also in Proposition 6.1 (line 288), $|T_n|$ is *nondecreasing* (strictly increasing iff $V_k \ne 0$).
  2. **Theorem 6.7 proof (line 365):** *"and the boundary case of Theorem 3.4 holds by Proposition 3.1(b)."* Proposition 3.1(b) gives an upper bound on $\sum_{\text{other}} f_w(N)$ in terms of $M_N(z)$ and is not needed here; the boundary case follows directly from $\sum_{w\text{ other}} f_w(N) \to 0$ (which already excludes the interior alternative $f_{m^L}(N) \to 1$).
  3. **Corollary 7.1 (line 375):** *"If $B'_L(N) = o(N)$, then $f_{0^L}(N) \to 1$ for every $L$"* — quantify *"for every $L$"* on the hypothesis $B'_L(N) = o(N)$ as well.
  4. **Section 8 prose (line 503):** *"the exact values are $\gamma^+(4) = 0.75$, $\gamma^+(256) = 0.234375$, $\gamma^+(2^{18}) = 0.699711$ and $\gamma^+(2^{32}) = 0.200037$."* The first two are exact decimals ($3/4$ and $15/64$), whereas the last two are 6-decimal roundings of exact rationals.
- **Actionable fix:** Add brief one-clause clarifications at each of the four locations.

#### Minor 5 (A1, Script & §9): Theorem 4.1(a) check runs on 55 out-of-hypothesis prefixes and 81 tautological $\varepsilon = \frac12$ cases
- **Files / lines:**
  - [`scripts/phase22_simple_normality.py:361-370`](../../../scripts/phase22_simple_normality.py#L361-L370)
  - [`notes/phase22/simple-normality-and-signed-transfer.md:514`](../simple-normality-and-signed-transfer.md#L514)
- **Issue:** Theorem 4.1(a) requires $2\delta < \varepsilon \le \frac12$ (which forces $\delta < \frac14$). In `check_lemma_and_theorem` (lines 361–370), the binary check runs for all prefixes with $\delta < \frac12 - \frac1N$ (`dn > 0`) and sets $\varepsilon = \frac12$ whenever $8\delta \ge 1$ (`8 * dn >= dd`), otherwise $\varepsilon = 4\delta$. Auditing the `116` reported binary prefixes shows:
  - **55** have $\delta \ge \frac14$ (so $2\delta \ge \frac12$, meaning Theorem 4.1(a)'s hypothesis $2\delta < \varepsilon \le \frac12$ is **not met**);
  - **81** (all 55 with $\delta \ge \frac14$ plus 26 with $\frac18 \le \delta < \frac14$) receive $\varepsilon = \frac12$, making `Peps == f0` identically and reducing the assertion to `0 <= 0 <= delta * N`;
  - only **35** prefixes test a nontrivial scale $\varepsilon < \frac12$ (and 61 meet $\delta < \frac14$).
- **Actionable fix:** Gate the Theorem 4.1(a) check on `4 * dn < dd` (i.e. $\delta < \frac14$), choose a strictly interior scale such as $\varepsilon = \frac12(2\delta + \frac12) = \delta + \frac14$ (or $\min(\frac14 + \delta, 4\delta)$, which satisfies $2\delta < \varepsilon < \frac12$ whenever $\delta < \frac14$), and update the prefix count in §9 line 514 accordingly.

#### Minor 6 (A2, Script): Latent exact-zero-tail bug in `Orbit.__init__` when `eps_sign = 0`
- **File / line:** [`scripts/phase22_simple_normality.py:206`](../../../scripts/phase22_simple_normality.py#L206)
- **Issue:** Line 206 computes `self.nonneg` ($T_n \ge 0$) as:
  ```python
  self.nonneg.append(W > 0 or (W == 0 and e > 0))
  ```
  When `eps_sign == 0` (exact finite truncation with no discarded tail), an exact zero tail $T_n = 0$ ($W = 0$) evaluates to `False` instead of `True`, contradicting §5 line 216 ("Exact zero tails belong to $P_L$") and inconsistent with lines 212 and 214 (which both use `>= 0`). This did not invalidate any test in the current run solely because every caller reading `orb.nonneg` passes `eps_sign = ±1`.
- **Actionable fix:** Change `e > 0` to `e >= 0` on line 206 (and similarly on line 577 if `analyse` is ever called with `sg = 0`), and optionally add a unit test with a finitely supported series at `eps_sign = 0` to exercise exact zero tails directly.

#### Minor 7 (A2, §9 & Script): Minor reporting and certification hygiene discrepancies
- **Files / lines:**
  - [`notes/phase22/simple-normality-and-signed-transfer.md:507, 516`](../simple-normality-and-signed-transfer.md#L507)
  - [`scripts/phase22_simple_normality.py:225-226, 260-266, 553-555, 711, 725, 775, 781`](../../../scripts/phase22_simple_normality.py#L553-L555)
- **Issues:**
  1. **§9 Table line 516:** Groups Theorems 5.2 and 5.3 as checked *"at **every** $N \le 10^4$"*. In `analyse`, Theorem 5.2 (lines 539–541) is indeed checked at every $N_{\mathrm{cur}} \le 10^4$, but Theorem 5.3 (lines 553–555) lies outside the `for n in range(N):` loop and is only checked at the final cutoff $N = 10^4$ (and $N = 2^{14}$ for lacunary).
  2. **§9 Prose line 507:** States that the script uses pure exact integer/rational arithmetic *"except for the two logarithms in Corollary 5.4"*, overlooking lines 775 and 781 in `section8`, which check Theorem 8.1 via `math.sqrt(Nc) + 1e-9` (whereas Theorem 8.2 on line 805 is squared into exact rational arithmetic).
  3. **Certification guards (lines 225–226, 260–266):** `Orbit.__init__` hardcodes `b ** 4` in the digit-boundary certificate (assuming `max(Ls) <= 4` and `(b - 1) * b ** 4 * err < Q`), and `truncate_before_support` loops over `nxt < m <= nxt + 400` without asserting `nxt + 400 <= top`. All three inequalities hold comfortably for every family tested in the script, but explicit `assert`s make the certificate self-enforcing.
  4. **Label typo (script lines 711 & 725):** The comment and stdout print `"Lemma 6.2(c) sign reversal"`, whereas the sharpness statement in the note is **Lemma 6.2(d)**.
- **Actionable fix:** Split Theorems 5.2 and 5.3 in the §9 table (or clarify Theorem 5.3 is checked at $N = 10^4$); square Theorem 8.1's check on lines 775 & 781 into exact rational arithmetic (or note the `sqrt` check on line 507); add the three `assert` guards in `Orbit`/`truncate_before_support`; and fix `Lemma 6.2(c)` → `Lemma 6.2(d)` on script lines 711 & 725.

#### Minor 8 (A1–A2, §10): Lean 4 elaboration issues in the recommended finite cores
- **File / lines:** [`notes/phase22/simple-normality-and-signed-transfer.md:530-608`](../simple-normality-and-signed-transfer.md#L530-L608)
- **Issues:** Every one of the 12 proposed Lean theorem statements is **mathematically true** (including at all omitted zero edge cases $L = 0$, $N = 0$, $K = 0$; notably `badTail_card_le` even holds at $L = 0$ because `abs_orientedTail_lt` gives $|T_n| < H/(b-1) \le 1 = b^0$ strictly!). However, the snippet will not elaborate as-is in Lean 4 for two mechanical reasons:
  1. **Ambiguous `repunit` identifier (lines 532, 538, 544, 562):** Line 532 opens `Phase18Synthetic`, which already defines [`NormalityChecker.Phase18Synthetic.repunit`](../../../NormalityChecker/Phase18Synthetic.lean#L52) with the exact same formula `∑ i ∈ range h, b ^ i`. Redefining `def repunit` on line 538 causes an ambiguous-identifier error on lines 544 and 562.
  2. **Missing `open Classical` for real-valued `Finset.filter` predicates (lines 555, 600):** Both `exists_fixed_center_of_deficit` (`¬ Near ...`) and `badTail_card_le` (`1 / (b : ℝ) ^ L ≤ |orientedTail ...|`) filter `range N` by non-decidable real predicates, requiring `open Classical` (or `open Classical in`) as used in `Phase18Synthetic.farCount` and `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far`.
- **Actionable fix:** Delete the duplicate `def repunit` on line 538 (reusing `Phase18Synthetic.repunit`), and add `open Classical in` before `exists_fixed_center_of_deficit` and `badTail_card_le` (or `open Classical` at the top of the namespace).

---

## 4. Summary of Required Actions Before Final Sign-Off

1. **Fix Major 1 (A2):** Correct the logarithmic-mass $O$-bound on line 268 from $O(\rho_N \log\log N)$ to $O(\rho_N(\log(1/\rho_N) + \log\log(N+3)))$ (or note the $b^k \ge (\log(N+2))^{\gamma+1}$ choice giving $O(\rho_N \log\log(N+3) + 1/\log(N+2))$).
2. **Fix Major 2 (A2):** Add the infinite-support (or $N \le m_K$ for finite support) condition to the final sentence of Theorem 6.3 on line 325.
3. **Apply Minor polishes (A1 & A2):** Address Minors 1–8 above (especially `H ≥ 1` in Theorem B / Corollary 6.4, $r \ge \frac12$ in Proposition 2.3, `Orbit.nonneg` at `e == 0`, the Theorem 4.1(a) script gate, §9 table accuracy for Theorem 5.3, and the `repunit` / `open Classical` fixes in §10), then re-run `python -B scripts/phase22_simple_normality.py` and refresh the binary-prefix count if modified.

---

## Post-Repair Verification

**Re-audited files**
- Note: [`notes/phase22/simple-normality-and-signed-transfer.md`](../simple-normality-and-signed-transfer.md) (lines 1–632)
- Script: [`scripts/phase22_simple_normality.py`](../../../scripts/phase22_simple_normality.py) (lines 1–873)

**Updated Verdicts**
- **Track A1:** **ACCEPT** — Zero Critical, zero Major, and zero remaining Minor findings.
- **Track A2:** **ACCEPT** — Zero Critical, zero Major, and zero remaining Minor findings.

> **Review scope caveat:** This post-repair check is an automated cross-model mathematical audit, **not** independent human peer review.

### Script Re-Execution
- **Command:** `python -B scripts/phase22_simple_normality.py`
- **Result:** Exit code `0`; `ALL 3344335 CHECKS PASSED in 19.6s`.
  - Section timings: `section1`: `0.0s`; `section2`: `3.1s`; `section3`: `0.3s`; `section5to7`: `10.2s`; `section7_identities`: `0.0s`; `section8`: `6.0s`.
- Every displayed number in [`simple-normality-and-signed-transfer.md`](../simple-normality-and-signed-transfer.md) (including all 90 cells of Table 7.1, the updated `61` binary prefixes for Theorem 4.1(a), the 5 prefix checkpoints for Theorem 5.3, the exact-zero-tail checks, and the `Lemma 6.2(d)` label) matches stdout verbatim.

### Repair-by-Repair Audit

| Finding | Resolution Verified | Location(s) Checked |
|---|---|---|
| **Major 1 (A2)** | **Verified fixed.** Line 268–274 now states the exact bound $B'_L(N)/N = O\bigl(\rho_N(\log(1/\rho_N) + \log\log(N+3))\bigr)$ from $k = \lceil \log_b((\log(N+2))^\gamma/\rho_N) \rceil$, explicitly explains via the single-term example $a(N+1) = \lfloor N\log(N+2) \rfloor$ why $\rho_N\log(1/\rho_N)$ cannot be dropped, and correctly concludes $B'_L(N)/N \to 0$ when $S(N)\log\log N = o(N)$. | [note:268–274](../simple-normality-and-signed-transfer.md#L268-L274) |
| **Major 2 (A2)** | **Verified fixed.** Theorem 6.3 now restricts the $m_{k_0}$ comparison to infinite support or finite support with $N \le m_K$, and states the exact error $m_{k_0} + N - m_K$ when support is finite and $N > m_K$ (accounting for the $N - m_K$ zero-tail shifts in $G_{K+1}$). | [note:331](../simple-normality-and-signed-transfer.md#L331) |
| **Minor 1 (A1)** | **Verified fixed.** Line 30 derives (0.1) from $(N+1)f_w(N+1) - Nf_w(N) = \epsilon \in \{0,1\}$; Proposition 2.3 splits off $r \ge \frac12$ before invoking Lemma 2.1(a) on $2r + \eta \le 1$; Remark 3.5 writes $c_m + \{w : M_N(w) \to 0\}$ and notes $\mathbb Z$-invariance. | [note:30, 102, 168](../simple-normality-and-signed-transfer.md#L102) |
| **Minor 2 (A2)** | **Verified fixed.** Theorem 5.3's proof explicitly handles the case where no occupied index $\ge N$ exists ($0$ contribution to $W$). | [note:244](../simple-normality-and-signed-transfer.md#L244) |
| **Minor 3 (A2)** | **Verified fixed.** Integer $H \ge 1$ is now stated explicitly in Theorem B, Corollary 6.4 (and its proof), and Corollary 7.1. | [note:12, 335, 341, 381](../simple-normality-and-signed-transfer.md#L335-L341) |
| **Minor 4 (A2)** | **Verified fixed.** Section 6 defines $g_{K+1} = \infty$, $\min(\infty, 0) = 0$, $R^*_K = 0$; Proposition 6.1 specifies $k \le K$, nondecreasing $|T_n|$ (strictly increasing when $V_k \ne 0$), and $T_n = 0$ on $G_{K+1}$; Lemma 6.2(b) notes $m_{k+1}$ existence; Theorem 6.7 excludes the interior case directly from $\sum_{\text{other}} f_w \to 0$; Corollary 7.1 quantifies $B'_L(N) = o(N)$ for every $L \ge 1$; §8 distinguishes exact decimals ($3/4$, $15/64$) from 6-decimal roundings ($\approx 0.699711$, $\approx 0.200037$). | [note:286–302, 371, 381, 509](../simple-normality-and-signed-transfer.md#L286-L302) |
| **Minor 5 (A1)** | **Verified fixed.** Script gates Theorem 4.1(a) on `4 * dn < dd` ($\delta < \frac14$), tests the strictly interior scale $\varepsilon = \delta + \frac14$ with an exact check `2 * dn * ed < en * dd and 2 * en < ed`, and §9 reports the resulting `61` valid binary prefixes. | [script:366–374](../../../scripts/phase22_simple_normality.py#L366-L374), [note:520](../simple-normality-and-signed-transfer.md#L520) |
| **Minor 6 (A2)** | **Verified fixed.** `Orbit.__init__` and `analyse` now use `e >= 0` / `sg >= 0` so exact zero tails ($T_n = 0$) belong to the nonnegative class, and a dedicated `eps_sign = 0` test (`a = {1: 1, 4: -1, 9: 1}`, $b \in \{2, 3, 10\}$) verifies both sign classification and Theorem 5.2. | [script:210, 587, 666–680](../../../scripts/phase22_simple_normality.py#L666-L680), [note:525](../simple-normality-and-signed-transfer.md#L525) |
| **Minor 7 (A2)** | **Verified fixed.** Theorem 5.3 is checked via exact integer arithmetic (`hat_A_parts`) at $N \in \{100, 1000, 2500, 5000, 10000\}$ and documented separately from Theorem 5.2 in §9; Theorem 8.1 assertions are squared into pure exact rational arithmetic (matching §9 line 513); `Orbit` and `truncate_before_support` enforce `max(Ls) <= 4`, `(b-1) * b^4 * b^(N-1) * Hcert < Q`, and `nxt + 400 <= top`; script labels now read `Lemma 6.2(d)`. | [script:175, 197–199, 265, 483–488, 523, 552–560, 736, 750, 800, 806](../../../scripts/phase22_simple_normality.py#L552-L560), [note:513, 522–524](../simple-normality-and-signed-transfer.md#L513-L524) |
| **Minor 8 (A1–A2)** | **Verified fixed.** §10 opens `Classical` for the real-valued `Finset.filter` predicates and removes the duplicate `def repunit`, reusing `Phase18Synthetic.repunit` cleanly. | [note:536–548](../simple-normality-and-signed-transfer.md#L536-L548) |

No regressions or new mathematical defects were introduced. Both Track A1 and Track A2 are ready for acceptance.
