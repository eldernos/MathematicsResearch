# Cross-Provider Referee Review — Phase 25 Track E

- **Reviewer:** Gemini 4 Neon (auditing Codex `gpt-6.2-astra`)
- **Files audited (read-only):**
  - [`notes/phase25/partitions-and-reciprocals.md`](../partitions-and-reciprocals.md) (282 lines)
  - [`scripts/phase25_partitions_reciprocals.py`](../../../scripts/phase25_partitions_reciprocals.py) (353 lines)
- **Independent script execution:** `python -B scripts/phase25_partitions_reciprocals.py` exited with code `0` using standard-library exact `int`/`Fraction` arithmetic only (zero floating-point operations):
  - `E1: 15 rational pads; composed contraction has 936 verified band positions.`
  - `E1.2: 15 coprime period updates in bases 2, 3, 4, 5, 10; exact pair multiplicities and couplings.`
  - `E2: 16 product denominators; exact grids, mean-square diagonal range and starting phases.`
  - `E3/E4: 152 reciprocal-separation instances and 16 actual Euler orbit windows.`
  - `Finite measurement: transitions among 256 certified digits: {'X(2,3)': 131, 'X(2,4)': 138, 'X(2,5)': 146, 'P(2)': 111}`
- **Reviewer-side auxiliary stress tests** (scratch code via `python -B -c`, nothing committed or written to the repository):
  1. Inspected every `lower` and `F(2,5)*lower/k - F(1,k)` value across all 16 Euler orbit windows (`b ∈ {2,3,5,10}`, `k ∈ {16,32,64,128}`) and located the positivity threshold for `b = 5` (`k ≈ 130`; positive at `k = 200`) and `b = 10` (`k ≳ 460`).
  2. Evaluated the **actual** complex orbit mean-square $T_k^{-1}\sum_{s<T_k}|W_a(N; b^s R_k)|^2$ directly for E2.3 across odd-only exponents `(1,3,5)` in base `3`, mixed exponents `(1,2,3)` in base `3`, base `4` (`p = 3`), composite bases `b = 6` (`p = 5`) and `b = 9` (`p = 2`), and negative harmonics `a = -1`, confirming exact $1/N$ equality for $N \le J$ and the $\le \sum_r c_r^2 / N^2$ upper bound for $N > J$.
  3. Simulated 20,000 rounds of the E1.2 Fourier dynamics targeting $\alpha = 1/\sqrt{2} \approx 0.707107$ (confirming $z \to 1/\sqrt{2}$ and $B \to 0$ at the expected $(j+8)^{-(1-\alpha)}$ rate), and verified all-prefix discrepancies across **every** intermediate $N \in [221, 900)$ for an actual base-3 cut-and-fold update (`max |D_N - old_D| = 0.0300 < ρ = 0.0679`; cut-side `max M_N = 0.0660 < old_B = 0.0684`) and across **every** $N \in [240, 750)$ for a dyadic pad of `5/56` (`max |D_N - old_D| = 0.0546`, `d/p = 0.0333`).
  4. Verified the E3 signed orbit recurrence $b^{M-s}(A X_{b,m} - b^s) = 1 + O_b(b^{-M})$ to 12+ digits for $(b,m,k) \in \{(2,3,4), (3,3,4), (5,4,4)\}$.
- **Scope notice:** This is an automated cross-model audit. **Cross-model review is not independent human peer review.**
- **Verdict:** **ACCEPT WITH MINOR POLISH** (0 Critical, 0 Major, 8 Minor).

---

## Executive Summary

Track E is mathematically sound across all four sub-tracks (E1.1, E1.2, E2, E3–E4), with **zero Critical and zero Major findings**. Its centerpiece — **Theorem E1.2**, establishing $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ in **every** integer radix $b \ge 2$ and realizing the exact limit measure $\mu_\alpha = \alpha\delta_0 + (1-\alpha)\lambda$ along **all** prefixes $N$ for irrational $x \in M_b \subset K_b$ (including every irrational target such as $1/\sqrt{2}$, computably for computable $\alpha$) — survived an exhaustive adversarial audit with zero logical gaps, zero transition-interval leakage, zero unreset-product pitfalls, and clean avoidance of Phase 24's Bugeaud–Corvaja–Zannier obstruction (`GF-38` C1.4).

The eight Minor findings are localized exposition, edge-case, label, and finite-certificate polishes: a factor-of-2 preperiod strip count in E1.1 contraction (`a+H` vs `2a+H`), a misnomer ("compactness argument" instead of trigonometric approximation) in E1.2, an inconsistent `Objective 1` tag on Proposition E2.3, vacuously negative RHS bounds in 12 of the 16 Euler finite-certificate windows in the script, minor explicit index/computability clarifications in E1.2/E3/E4, completeness of the external-input note, and adding a compact top-level summary table.

---

## Section-by-Section Adversarial Audit

### 1. Definitions, Scope, and Coupling Lemma (Lines 1–19) — **Verified**

- **Circle discrepancy and complement identity (line 7):** On $\mathbb{T} = \mathbb{R}/\mathbb{Z}$, the complement of a wrapping half-open arc $[a, 1) \cup [0, b)$ is the ordinary half-open interval $[b, a) \subset [0, 1)$, with $|\nu(I) - |I|| = |\nu(I^c) - |I^c||$. Hence $D(\nu)$ over circle arcs equals the standard $[0, 1)$ extreme interval discrepancy identically.
- **Coupling comparison (line 19):** Let $\pi$ couple $\nu_1, \nu_2$ on $\mathbb{T}^2$ with $\pi(\|x-y\| > h) \le s$. For mean distance to zero, $|\int \|x\| d\nu_1 - \int \|y\| d\nu_2| \le (1-s)h + \frac{1}{2}s \le h + s$. For discrepancy, for any half-open arc $I \subset \mathbb{T}$: if $|I| + 2h \ge 1$ then $\nu_1(I) - |I| \le 1 - |I| \le 2h \le D(\nu_2) + 2h + s$; if $|I| + 2h < 1$, enlarging $I$ by $h + \varepsilon$ at both ends yields a half-open arc $I^+$ with $\nu_1(I) \le \nu_2(I^+) + s$, giving $\nu_1(I) - |I| \le D(\nu_2) + 2h + 2\varepsilon + s$; letting $\varepsilon \downarrow 0$, applying the same argument to $I^c$ (which is also a half-open arc on $\mathbb{T}$), and reversing $\nu_1 \leftrightarrow \nu_2$ yields $|D(\nu_1) - D(\nu_2)| \le 2h + s$. Working on $\mathbb{T}$ cleanly eliminates $[0, 1)$ endpoint wrap-around.

### 2. Theorem E1 (E1.1, Dyadic $\mathcal{A}_{\mathrm{conv}}(2^e) = [0, 1]$, Lines 13–88) — **Verified (Minor m1)**

- **Padding (lines 23–47):**
  - CRT gives arbitrarily large $p$ with $P_v \mid p$ and $p \equiv 1 \pmod e$ since $\gcd(P_v, e) = 1$. For $0 < t < 1/4$, the interval $[\frac{t}{1-t}p, \frac{2t}{1-2t}p]$ has width $> t p$ and lies strictly inside $(0, p)$, so for large $p$ it contains multiples $d \equiv 0 \pmod{e P_u}$ with $p < q = p+d < 2p$, $t \le \theta = d/q \le 2t$, and $q \equiv 1 \pmod e$ (hence $\gcd(q, e) = 1$).
  - Exact rational identities: $u' = 1/v' = u + w/(2^p - 1)$ with $w = u(1 - 2^{-d})$, $2^{a+d} w = 2^a(2^d - 1)u \in \mathbb{Z}$, and $2^a(2^q - 1)v' = 2^d \cdot 2^a(2^p - 1)v \in \mathbb{Z}$, so $P_{v'} \mid q$ (preserving $\gcd(P_{v'}, e) = 1$).
  - Full-cycle coupling to $(1-\theta)\mu + \theta\delta_0$ is airtight: in $v' = \sum_{i \ge 0} 2^{-iq} v(1 - 2^{-p})$ at $n = iq + r$, earlier summands are integral once $r \ge a$ (indeed whenever $d + r \ge a$), current + tail tracks $2^r v$ within $2v \cdot 2^{-H}$ on $[a, p-H)$ and tracks $0$ within $v \cdot 2^{-H}$ on $[p+a, q-H)$, and trimming $< P_v$ sampled points per fragment yields exact copies of $\mu$ on every progression modulo $e$.
  - **All-prefix stability ($N \ge p$):** Checked explicitly for both $p \le N < q$ and $N \ge q$. The zero-piece fraction is at most $(d+e)/(p-e)$ or $2(d+e)/(q-e)$, which is $\le 4t + O_e(1/p)$ (even with an $e$-independent constant multiplying $t$), and strips/trimming cost $O_e((a+H+P_v+1)/p)$. On the $u'$ side, $u' - u = w\sum_{i \ge 1} 2^{-ip}$ leaves at most $a+d+H$ bad indices per $p$-block (only $H$ in block $0$), giving $M_N(u'; 2) \le B + 4t + O((a+H+P_u)/p) + 2u \cdot 2^{-H}$ uniformly for all $N \ge p$, and taking $N \to \infty$ gives the new cycle mean bound $B' \le B + O(t) + o(1)$.
- **Contraction (lines 49–64):**
  - For $l > a$ divisible by both periods, $2^n v^+ = 2^n v + 2^{n-l} v \equiv 2^{n+1} v \pmod 1$ for all $n \ge l + a$ (since $2^{n-l}(2^l - 1)v \in \mathbb{Z}$), so the eventual cycle of $v^+$ is **identically** $\mu$ with the same period.
  - **Minor m1 (line 55):** On $0 \le n < N$ ($N \ge l$), the initial preperiod $[0, a)$ must also be omitted alongside $[l - H, l + a)$, because $v$ acquires a nonzero binary preperiod after the first contraction; thus $2a + H$ binary times (not $a + H$) intervene. This remains $O(a + H) = o(l)$ and does not affect the proof.
  - On the $u^+$ side, $2^l u$ clears the $2$-power denominator so $\operatorname{den}(u^+) \mid (2^l - 1)(2^l + 1) = 2^{2l} - 1$ (purely periodic!). Both band identities are exact, geometric error per band is $< u$, cycle mean contracts to $\le B/2 + (2u + a + P_u)/(2l)$, and every prefix $N \ge l$ decomposes into whole/partial bands of length $l$ yielding $M_N(u^+; 2) \le B + O((a + P_u + u + 1)/l)$.
- **Steering, all-prefix convergence, irrationality, computability (lines 65–86):**
  - **Crucial adversarial check:** Padding can temporarily *decrease* $D_j$ (e.g., $\delta_{1/2}$ mixed with $\delta_0$), so $D_j$ need not be monotone. The proof does **not** assume monotonicity of $D_j$: it only maintains $D_{j+1} \le D_j + 2t_j + 2^{-j}t_j < \alpha$ (from TV change $\le \theta_j \le 2t_j$), uses $L_{j+1} \le (1-\theta_j)L_j + 2^{-j}t_j$ to deduce that $\sum t_j = \infty$ would force $L_j \to 0$ (since $2^{-k}t_k$ is summable) and hence $D_j \to 1 > \alpha$, contradiction. Therefore $\sum t_j < \infty \implies t_j \to 0 \implies D_j \to \alpha$, and $B_{j+1} \le B_j/2 + O(t_j + 2^{-j}) \implies B_j \to 0$. Completely rigorous!
  - **All-prefix convergence ($s_i \le N < s_{i+1}$):** With $s_i \ge i+3$ and $s_{i+1} > 2s_i$, both sequences stay in a fixed compact subset of $(0, \infty)$ and $|y - v^{(i)}|, |x - u^{(i)}| \le C 2^{-s_{i+1}}$. Discarding the last $\lceil\sqrt{N}\rceil$ binary indices leaves $2^n|y - v^{(i)}| \le C 2^{-\sqrt{N}}$, transferring the uniform prefix bounds of operation $i$ directly to $(x, y)$ across **all** intermediate $N$ (with no block-transition oscillation because $t_j \to 0$).
  - Irrationality at contractions (requiring $2^{-l_j}\operatorname{den}(v) < 1/j^2$ and next scale $p_{j+1}$ large enough that the uniform tail bound $2 C_0 2^{-p_{j+1}} < \frac{1}{2} v 2^{-l_j}$), computability via strict rational intervals for $\alpha - D_j > 0$, and endpoints $\alpha = 0$ (`GF-34` Thm 5) and $\alpha = 1$ (pure contractions from $u = v = 1$) all check out cleanly.

### 3. CRITICAL AUDIT: Theorem E1.2 (Every Radix $b \ge 2$, $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$, Lines 89–167) — **Verified (Minors m2, m5)**

This theorem resolves Phase 23–24 Open Problems #1–#2 completely across all radices $b \ge 2$ (prime and composite). Every component was audited line by line:

1. **Coprime-period cut-and-fold operation (lines 93–108):**
   - For any $C, F > 0$ with $CF = 1$ and $\gcd(P_C, P_F) = 1$, choosing $L \ge 2$ coprime to $P_C$, $d = (L P_F)^k$, and $m = P_C(1 + j L P_F)$ closest to $d/r$ gives $P_C \mid m$, $P_F \mid d$, $\gcd(m, d) = 1$, and $\rho = d/m \to r$ as $k \to \infty$.
   - Exact update $C' = C\frac{1-b^{-m}}{1-b^{-q}}$, $F' = F + \frac{w}{b^m - 1}$ with $q = m+d$ and $w = F(1-b^{-d})$ satisfies $b^a(b^q - 1)C' \in \mathbb{Z}$ and $b^{a+d}w \in \mathbb{Z}$.
   - **No LTE period-lifting pitfall:** Because $F'$ is written as a **sum** $F + w/(b^m - 1)$ rather than a product, its prime-to-$b$ denominator divides $\operatorname{lcm}(\operatorname{den}_{\perp b}(F),\, b^m - 1) \mid (b^{\operatorname{lcm}(m, P_F)} - 1)$ (taking the *maximum* of $p$-adic valuations rather than their sum). Since $\gcd(m, d) = 1$ and $P_F \mid d$, we have $\operatorname{lcm}(m, P_F) = m P_F$ and $\gcd(q, m P_F) = \gcd(m+d, m P_F) = 1$, so $\gcd(P_{C'}, P_{F'}) = 1$ holds unconditionally in every prime or composite radix $b \ge 2$.
2. **Exact convolution & all-prefix couplings (lines 110–126):**
   - On $P_F$ consecutive $m$-blocks past the preperiod $a+d < m$, for $n = im + s$ ($i \ge 1$): earlier terms ($1 \le j < i$) are integral once $m > d+a$, future tail is $< 2 F b^{s-m}$, and the current term $b^s F - b^{s-d} F$ yields $b^{im+s}F + b^s F + O(F b^{-H})$ on $a \le s < d - H$ and $b^{im+s}F + O(F b^{-H})$ on $d+a \le s < m - H$. Since $\gcd(m, P_F) = 1$, as $i$ runs over $P_F$ consecutive values for fixed $s$, $(im+s)\bmod P_F$ visits every residue mod $P_F$ exactly once independently of $s \bmod P_F$. Trimming $< P_F$ values of $s$ in $[a, d-H)$ gives an exact coupling to $(1-\rho)\mu + \rho(\mu * \mu)$ with displacement $O(F b^{-H})$ and exceptional mass $O((a+H+P_F)/m)$ (choosing $H$ first, then $m$).
   - **All-prefix bound ($N \ge m$) with zero transition-interval leakage:** On the folded side, block $i = 0$ discards only the last $H$ indices and each block $i \ge 1$ discards $s < d+a$ and $s \ge m-H$, giving discarded fraction $\le \frac{H + \lfloor N/m \rfloor(d+a+H)}{N} \le \rho + \frac{a+2H}{m}$ (plus $(a+P_F)/N$ to match $\nu_N(F; b)$ to $\mu$). On the cut side, for both $m \le N < q$ and $N \ge q$, the discarded fraction is $\le 2\rho + \frac{2(a+H+P_C)}{m}$. The coefficient multiplying $\rho$ is absolute ($\le 2$) for **every** $N \ge m$.
3. **Iteration, $x \in M_b$, and non-degenerate Fourier convergence (lines 127–161):**
   - Subadditivity $\|u+v\| \le \|u\|+\|v\|$ gives $B'_j \le (1+\rho_A)B_j + h_j^2$ and $B_{j+1} \le \frac{1+\rho_A}{1+\rho_B} B_j + 2h_j^2 = (1 - (1-\alpha)h_j + O(h_j^2))B_j + O(h_j^2)$. Since $1 - \alpha > 0$, $\sum h_j = \infty$, and $\sum h_j^2 < \infty$, both $B_j \to 0$ and $B'_j \to 0$.
   - Exact ideal Fourier factorization: $1 - T(z) = (1-c)(1-z)(1 + h z_A)$ where $c = \rho_A/(1+\rho_A)$ and $h = \rho_B$.
   - **Activation of every harmonic ($z \neq 1$):** Writing old $y = A/(b^a B)$ with $\gcd(B, b) = 1$, in $y' = A b^d(b^m-1)/(b^a B(b^q-1))$ the factors $b^d, b^a$ cannot cancel primes of $B(b^q-1)$, so the reduced prime-to-$b$ denominator of $y'$ is at least $\frac{B(b^q-1)}{A(b^m-1)} \ge \frac{b^q-1}{A(b^m-1)} > b^d / A \to \infty$ (even for $\alpha = 0$ where $\rho_A \in (h_j^2/2, h_j^2)$ is strictly positive at each fixed $j$). Thus $D_{y'} > j$ is always feasible, guaranteeing $\widetilde{z}_A \neq 1$ for every $1 \le k \le j$.
   - In Step B, $|1 + h\widetilde{z}_A| \ge 1 - h > 2/3$ while the coupling error is $\le h_j^2|1-\widetilde{z}_A|^2/100 \le \frac{2}{8100}|1-\widetilde{z}_A|$, so $|1 - z_{\mathrm{next}}| > 0$ persists inductively for all $j \ge k+1$.
   - On $\{|w| \le 1\}$, $g(w) = (1-h)w + h w^2$ has $|g'(w)| \le (1-h) + 2h = 1+h$ (exact Lipschitz constant), and $|1 - \widetilde{z}_A| \le (1 + \frac{2}{8100})|1 - z| \le 2|1-z|$, giving $|z_{\mathrm{next}} - T(z)| \le 0.06\, h_j^2|1-z|^2$.
   - Passing to $W = 1/(1-z)$: both $|1 - T(z)| \ge \frac{1}{2}|1-z|$ and $|1 - z_{\mathrm{next}}| \ge \frac{1}{3}|1-z|$ hold for all $j \ge k+1$, cancelling $|1-z|^2$ cleanly to give $|W_{\mathrm{next}} - \frac{1}{1-T(z)}| \le 0.36\, h_j^2$. Using $\frac{1}{1-c} = 1+\rho_A$, $|z_A - z| \le 2c$, and $zW = W-1$ yields $W_{\mathrm{next}} = (1 - (1-\alpha)h_j)W + h_j + O(h_j^2(1+|W|))$ in $\mathbb{C}$. Triangle-inequality induction bounds $|W_j|$, and subtracting $1/(1-\alpha)$ gives a summable-error contraction proving $W_j \to 1/(1-\alpha)$, hence $z_j \to \alpha$ (and intermediate $\widetilde{z}_A \to \alpha$) for every $k \ge 1$.
4. **All-prefix weak convergence, discrepancy convergence, word laws, irrationality, computability, and BCZ bypass (lines 162–166):**
   - For **every** $N \in [s_i, s_{i+1})$ ($s_i = m_i$, $s_{i+1} > 2s_i$), discarding the final $\lceil\sqrt{N}\rceil$ orbit points gives circle tracking to $O_b(b^{-\sqrt{N}})$ of $(x^{(i)}, y^{(i)})$, which by the all-prefix comparison is coupled to the cycle law of $(x^{(i-1)}, y^{(i-1)})$ with error $O(h_j)$ (displacement $\le h_j$, exceptional mass $O(h_j)$). Since both round-start and intermediate cycles satisfy $M(\mu_x) \to 0$ and $\widehat{\mu}_y(k) \to \alpha$, we get $M_N(x; b) \to 0$ ($x \in M_b \subset K_b$) and $\nu_N(y; b) \Rightarrow \mu_\alpha$ along **all** $N$, with zero oscillation inside either the cut or folded blocks.
   - Because extreme discrepancy on $\mathbb{T}$ is rotation-invariant, partitioning $\mathbb{T}$ into arcs of length $\le \varepsilon$ avoiding the sole atom $0$ (which are $\mu_\alpha$-continuity sets) yields a coupling with displacement $\le \varepsilon$ and unmatched mass $o(1)$, proving $D_N(y; b) \to D(\mu_\alpha) = \alpha$ despite the atom at $0$.
   - Cylinders whose closure misses $0$ are $\mu_\alpha$-continuity sets, giving exact limiting frequency $(1-\alpha)b^{-L}$; exhausting any cylinder interior by subarcs whose endpoints avoid $0$ (which are continuity sets, so $\nu_N \to \mu_\alpha$ on them) gives $\liminf f_w \ge (1-\alpha)b^{-L} > 0$, proving disjunctive nonnormality. The positive Lebesgue component $(1-\alpha)\lambda$ immediately rules out eventual periodicity, proving irrationality of $x$ and $y$.
   - Sharp constant check: $1 - \cos(2\pi t) = 2\sin^2(\pi t) \ge 8\|t\|^2$ holds with exact equality at $\|t\| = 1/2$, justifying the rational lower bound $1 - \Re z \ge 8/(P D^2)$ for computability.
   - **Clean bypass of Phase 24's Bugeaud–Corvaja–Zannier obstruction (`GF-38` C1.4):** Theorem C1.4 obstructs $+1$-inversion $v \mapsto v(1+b^{-l})$ because orbit preservation forces $2 \in \langle b \rangle \pmod D \implies D \mid \gcd(b^P-1, 2^P-1) = b^{o(P)}$. Theorem E1.2 never uses $+1$-inversion for $\alpha \in [0, 1)$: cut-and-fold produces additive convolution $\mu * \mu$ instead of doubling, imposing zero congruence condition on $2$ modulo $D$. At $\alpha = 1$, iterating $v(1+b^{-l})$ starting from integer $v_0 = 1$ stays at $2 \cdot 0 \equiv 0 \pmod 1$, so the congruence mod $1$ is empty in every radix $b \ge 2$.
   - See **Minors m2 and m5** for two small clarity polishes.

### 4. Section E2: Complete Period, Worst Start, and Averaged Incomplete Orbit (Lines 168–207) — **Verified (Minors m3, m4)**

- **Proposition E2.1 (lines 172–184):** Every prime case of the LTE calculation holds without exception:
  - For $s \mid Q'$ ($s \neq p$), lifting $(\mathbb{Z}/s^a\mathbb{Z})^\times \to (\mathbb{Z}/s\mathbb{Z})^\times$ adds only powers of $s$, so $v_p(\operatorname{ord}_{Q'}(b)) \le t = \max_{j \le k} v_p(m_j)$.
  - Taking $H = \operatorname{lcm}(2, \operatorname{ord}_{Q'}(b))$ forces $H$ even, so $b^2 \equiv 1 \pmod 4$ for $p = 2$, and exact LTE on $(b^2)^{H/2}$ handles **all** cases cleanly — including the delicate case $p = 2, t = 0$ (all $m_j$ odd), where $H/2$ is odd and $g = v_2(b^H - 1) = v_2(b^2 - 1) = v_2(b^2 - 1) + t$, as well as $p = 2, t \ge 1$ where $v_2(H/2) \le t - 1$.
  - $E \ge k c + t$ holds in all cases (for $p=2, b \equiv 3 \pmod 4, t \ge 1$, the term achieving $t$ has $v_2 \ge 3 + t - 1 > 1 + t$).
  - Since $g \ge 3$ at $p = 2$ and $g \ge 1$ at odd $p$, $\langle b^H \rangle \bmod Q_k$ is an exact uniform grid of size $G = p^{\max(0, E-g)}$ by CRT, and multiplication by any unit $A$ preserves the uniform spacing $1/G$, yielding $D(\mu(A/Q_k; b)) \le 1/G$.
  - Under $m_{k+1} \ge (1 - o(1))T_k$ on a subsequence, $0 < R - R_k \le C_b b^{-m_{k+1}}$, $N = \min(m_{k+1}, T_k) \to \infty$, mean displacement is $O_b(1/N)$, TV deletion error is $(T_k - N)/T_k = o(1)$, and Markov + coupling gives $D^-(R; b) = 0$.
- **Proposition E2.2 (lines 186–192):** Completely exact. For $0 \le n < L - h$, $b^n/Q \le b^{L-h-1}/b^L < b^{-h}$, giving $D_N(1/Q; b) \ge \min(N, L-h)/N - b^{-h}$. The shift $s = (-S_k) \bmod T_k$ recovers $b^s R_k \equiv 1/Q_k \pmod 1$, and $m_j \asymp a^j$ ($a > 1$) gives $\log_b Q_k = S_k + O_b(1) \asymp m_{k+1}$.
- **Proposition E2.3 (lines 194–205):** Mean-square expansion, grid orthogonality ($G \mid a(b^i - b^j) \iff J \mid (i - j)$ since $\gcd(G, b) = 1$), exact $1/N$ equality on $N \le J$, upper bound $\sum_r c_r^2 / N^2 \le \lceil N/J \rceil / N \le 1/N + 1/J$, divergence $J \to \infty$ for fixed $a \neq 0$, and the compactness + union-bound transfer to discrepancy-in-proportion are all completely rigorous (and confirmed directly in complex arithmetic by our auxiliary test #2). See **Minor m3** on the Objective 1 tag and `|a|`.
- **Conditional remark (line 206):** Properly labeled `Conditional`, accurately cites `GF-38` C2.3, and draws clean boundaries.

### 5. Section E3 & E4: Reciprocal Separation, Mahler $X_{b,m}$, and Euler $P_b$ (Lines 208–262) — **Verified (Minors m4, m6, m7)**

- **Reciprocal Separation Lemma (lines 212–218):**
  - $\gcd(A, b) = 1$ and $A > b - 1$ imply $(b-1)b^{n+s}/A \notin \mathbb{Z}$, so $\|(b-1)b^n/U\| \ge 1/A$.
  - The $b^{-s}$ cancels identically in $(b-1)b^n|Z - 1/U| \le \frac{(b-1)C b^{n-s-g}}{(A/b^s)V} = \frac{(b-1)C b^{n-g}}{AV} \le \frac{1}{2A}$ once $b^{g-n} \ge 2(b-1)C/V$.
  - A length-$h$ constant run of digit $d$ forces $|\{b^n Z\} - \frac{d}{b-1}| \le b^{-h}$ and hence $(b-1)b^{-h} \ge 1/(2A) = 1/(2U b^s) \implies h \le s + O(1)$ via compactness of $U$.
  - Since $\|t\| < \frac{1}{2b} \implies \|bt\| = b\|t\|$, iterating $R = \max(0, \lceil \log_b(A/b)\rceil) \le s + O(1)$ steps produces $j \in [n, n+s+O(1)]$ with $\|(b-1)b^j Z\| \ge \frac{1}{2b}$, equivalently $\operatorname{dist}_{\mathbb{T}}(b^j Z, F_b) \ge \frac{1}{2b(b-1)}$.
- **Theorem E3 ($X_{b,m}$, $m \ge 3$, lines 220–241):**
  - Exact gap $g_k = m^k - s_k = (m-2)s_k + 1$, tail $|U_k - Y_{b,m}| \le b^{-m^k}/(1 - b^{-1})$, minimal $k \ge 2$ with $g_k \ge n+c$ gives $s_k = m s_{k-1} + 1 \le \frac{m}{m-2}n + O_{b,m}(1)$, disjoint geometric windows give $\gg_{b,m} \log N$ transitions and escapes, and `GF-32` Lemma 5.3 ($1 - D_N \ge \frac{2}{5}\min_{c_0 \in F_b} M_N(z - c_0; b) - \frac{1}{N}$, verified in `notes/phase23/binary-partition-and-carry-complexity.md` lines 407–413) gives $1 - D_N(X_{b,m}; b) \gg_{b,m} (\log N)/N$.
  - Signed orbit recurrence $b^{M-s}(A X_{b,m} - b^s) = b^M(\prod_{j \ge k}(1 - b^{-m^j})^{-1} - 1) = 1 + O_b(b^{-M})$ is exact (since $m \ge 3 \implies mM > 2M$).
  - Prior-art links (`Phase 24, Theorem 1.6` in `simple-normality-and-word-laws.md` and `GF-38 C3`) were verified against the target files and match verbatim.
- **Theorem E4 ($P_b = 1/E_b$ and $R_k^{(E)}$, lines 242–260):**
  - Euler's pentagonal number theorem (`External input`, Andrews Ch. 1, evaluated at $|z| = 1/b < 1$) gives truncation $s_i = i(3i+1)/2$ with $A_i \equiv (-1)^i \pmod b$, next gap $g_i = 2i + 1$, tail constant $1/(1-b^{-1})$, and $i = \lceil(n+c)/2\rceil \implies s_i = \frac{3}{8}n^2 + O_b(n+1)$. Iterated squaring intervals $[n, C_b n^2]$ yield $\gg_b \log\log N$ transitions and escapes, and `GF-32` Lemma 5.3 gives $1 - D_N(P_b; b) \gg_b (\log\log N)/N$.
  - On $R_k^{(E)}$, $0 < P_b - R_k^{(E)} \le P_b b^{-k}/(b-1)$ gives $\sum_{j < k} b^j|P_b - R_k^{(E)}| \le P_b/(b-1)^2$; subtracting this $O_b(1)$ Lipschitz loss from $\sum_{j < k} \|b^j P_b - c_0\| \ge E(k)/(2b(b-1))$ for every $c_0 \in F_b$ and applying `GF-32` Lemma 5.3 at $N = k$ proves $1 - D_k(R_k^{(E)}; b) \gg_b (\log\log k)/k$. Completely airtight!
  - Cross-reference to `GF-38 C4.2 and C4.4` matches verbatim. See **Minor m6** for small-index bounds (`k >= 2`, `i >= 2`, `k, N >= 3`).

### 6. Script Verification (`scripts/phase25_partitions_reciprocals.py`) — **Verified (Minor m4)**

- Zero floating-point arithmetic; outward rounding throughout (`reciprocal_interval`, `fixed_distance_lower`, `transition_measurement`, and notably lines 336–338 properly certify `hi - r <= lo / ((b-1)*b**k)` and `error_sum <= lo / (b-1)**2` using `lo < P_b < hi` on the conservative side, avoiding the Phase 24 Track C `m13` pitfall).
- Every count printed by the script (`15`, `936`, `15`, `16`, `152`, `16`) matches note line 271 identically.
- `discrepancy(masses)` (lines 52–60) handles atoms at $0$, ties, and both sides of every atom exactly.
- See **Minor m4** regarding vacuous negative RHS values in 12 of the 16 Euler discrepancy-gap assertions (lines 333–344) and the scope of the E1/E2.3 finite checks.

### 7. Research-Note Checklist (10 Standard Elements, Evidence Labels, Prior Art)

| # | Element | Status | Notes |
|---|---|---|---|
| 1 | Definitions & notation | Present (lines 5–9) | Clean, matches `docs/research-objectives.md` and Phases 23–24. |
| 2 | Summary of results, evidence labels, standing objectives | Partial (lines 3, 9) | Inline labels are present and disciplined, except `Objective 1` on E2.3 (**m3**); adding a compact top-level summary table would match Phase 24–25 conventions (**m8**). |
| 3 | Complete statements & self-contained proofs | Present (lines 11–260) | All proofs verified sound (**m1**, **m2**, **m5**, **m6**). |
| 4 | Prior-art & attribution notes | Present (lines 87, 166, 184, 206, 230–232, 259, 261) | All internal (`GF-32`, `GF-34`, `GF-38`, Phase 24 Thm 1.6) and external citations checked and accurate. |
| 5 | External inputs stated & hypothesis-verified | Present (line 261) | Andrews Ch. 1 and Stone–Weierstrass verified; add Portmanteau & weak\* compactness on $\mathbb{T}$ plus provisional-priority note (**m7**). |
| 6 | Conditional statements marked | Present (line 206) | Properly separated and labeled `Conditional`. |
| 7 | Reproduction instructions & finite certificate summary | Present (lines 263–271) | Exact command, zero floats, counts match script (`exit 0`); clarify E4 positivity range (**m4**). |
| 8 | Strict separation of finite measurements | Present (line 273) | Properly separated; optionally quote the 4 printed counts (**m8**). |
| 9 | Explicit open questions & benchmark boundary | Present (lines 275–280) | Four sharp open problems; explicitly states no benchmark classification follows. |
| 10 | Cross-model review disclaimer | Present (line 282) | Explicitly states cross-model review is not independent human peer review. |

---

## Itemized Findings

### Critical
None.

### Major
None.

### Minor

1. **m1 — Preperiod strip count in E1.1 Contraction ([`notes/phase25/partitions-and-reciprocals.md:55`](../partitions-and-reciprocals.md#L55)):**
   - *Issue:* Line 55 states "Only $a+H$ times and at most two incomplete sampled cycles intervene" for $v^+$ prefixes $N \ge l$. However, $[0, a)$ lies in the binary preperiod of $v$ (which is genuinely nonzero at stages $j \ge 2$ after earlier contractions), so matching against the eventual cycle $\mu$ omits $[0, a) \cup [l - H, l + a)$, i.e., $2a + H$ binary times rather than $a + H$.
   - *Fix:* Replace "Only $a+H$ times" with "Only $2a+H$ times (the initial preperiod $[0, a)$ and the transition $[l-H, l+a)$)".

2. **m2 — Misnomer "compactness argument" in E1.2 ([`notes/phase25/partitions-and-reciprocals.md:164`](../partitions-and-reciprocals.md#L164)):**
   - *Issue:* Line 164 writes "The compactness argument identifies the limiting measure without requiring a convergence rate." E1.2 does not use compactness: it proves $\widehat{\nu}_N(k) \to \widehat{\mu}_\alpha(k)$ for every $k \in \mathbb{Z}$ and identifies $\mu_\alpha$ directly via uniform density of trigonometric polynomials in $C(\mathbb{T})$. (Compactness is used in E2.3, line 204.)
   - *Fix:* Reword to "Trigonometric approximation identifies the limiting measure directly from the Fourier coefficients without requiring a convergence rate."

3. **m3 — Objective 1 overclaim and signed harmonic notation in Proposition E2.3 ([`notes/phase25/partitions-and-reciprocals.md:194`](../partitions-and-reciprocals.md#L194)):**
   - *Issue:* Line 194 labels Proposition E2.3 `Objectives 1, 3 and 4`, conflicting with Line 9 (`Objectives 3 and 4`) and [`docs/research-objectives.md`](../../../docs/research-objectives.md) (averaging over shifts of finite rational cycles $R_k$ does not establish normality of any explicit real number along all $N$). Also, since $a \neq 0$ may be negative, writing $\gcd(G, |a|)$ (or restricting to $a \ge 1$ by conjugation) avoids ambiguity about the sign of $G/\gcd(G, a)$.
   - *Fix:* Change the label on line 194 to `(Paper proof; Objectives 3 and 4)` and write $J = \operatorname{ord}_{G/\gcd(G, |a|)} b$ (or "an integer harmonic $a \ge 1$").

4. **m4 — Vacuous negative RHS in 12 of 16 E4 finite-certificate windows and certificate scope ([`scripts/phase25_partitions_reciprocals.py:333-344`](../../../scripts/phase25_partitions_reciprocals.py#L333-L344), [`notes/phase25/partitions-and-reciprocals.md:271`](../partitions-and-reciprocals.md#L271)):**
   - *Issue:* In `check_partitions()`, the right-hand side `F(2,5)*lower/k - F(1,k)` is strictly positive in only 4 of the 16 Euler windows (`(b=2, k=64, 128)` and `(b=3, k=64, 128)`). In all 4 windows for $b = 5$ (where at $k = 128$, `lower = 2.4928 < 2.5`, turning positive near $k \approx 130$), all 4 windows for $b = 10$ (where positivity needs $k \gtrsim 460$), and `k = 16, 32` for $b = 2, 3$, the RHS is negative so `assert 1 - discrepancy(law(orbit_r)) >= F(2,5)*lower/k - F(1,k)` is vacuously true (and at `b = 2, k = 16, 32`, `lower < 0` makes `assert total >= lower` vacuous too). Separately, `check_grids()` lines 230–239 verify the combinatorial harmonic-divisibility count rather than complex Weyl sums (appropriate for a float-free script), and `check_padding()`/`cut_and_fold()` verify full-cycle couplings rather than intermediate prefixes $N \ge m$.
   - *Fix:* In the script, either add a larger $k$ window (e.g., $k = 160$ for $b = 5$) and assert `rhs > 0` on the nontrivial windows, or state explicitly in note line 271 which windows produce strictly positive discrepancy-gap bounds (`b = 2, 3` at `k = 64, 128`), and clarify that E2.3's finite check certifies the exact combinatorial diagonal/residue-class counts.

5. **m5 — Minor computability and initial-scale clarifications in E1.2 ([`notes/phase25/partitions-and-reciprocals.md:127,145,151,162`](../partitions-and-reciprocals.md#L127-L162)):**
   - *Issue:* For a rational $y$ with reduced prime-to-$b$ denominator $D$, every point of its eventual cycle has exact reduced denominator $D$, so the branch condition "with old $z \neq 1$" (line 145) is equivalent to $D \nmid k$ (manifestly decidable in exact integer arithmetic, and yielding $1 - \Re z \ge 8/D^2 \ge 8/(P D^2)$). Also, on line 127/162, noting that $0 < d_1 < m_1/3$ automatically forces $m_1 \ge 4$ (so $s_{i+1} > 2s_i$ gives uniform upper/lower bounds on both infinite products) closes a small visual gap compared with E1.1's explicit $s_i \ge i+3$.
   - *Fix:* Add one clause on line 145/151 stating "$z \neq 1 \iff D \nmid k$" and note "$m_1 \ge 4$" (or "$s_1 \ge 4$") on line 127.

6. **m6 — Explicit small-index bounds in Reciprocal Separation, E3, and E4 ([`notes/phase25/partitions-and-reciprocals.md:212,228,251-257`](../partitions-and-reciprocals.md#L212-L257)):**
   - *Issue:* In E3 (line 228), $A_1 = b - 1$ violates $A > b - 1$ of the Reciprocal Separation Lemma (which requires $k \ge 2$); in E4 (line 257), at $b = 2, i = 1$, $A_1 = 1 = b - 1$ likewise requires $i \ge 2$. In the lemma itself (line 212), $n \ge 0$ is implicit, and in E4 (lines 251–253), $\log\log k, \log\log N$ are positive for $k, N \ge 3$.
   - *Fix:* State $n \ge 0$ on line 212, note $k \ge 2$ on line 228, $i \ge 2$ on line 257, and $k, N \ge 3$ on lines 251–253.

7. **m7 — Completeness of external-input and provisional-priority disclosures ([`notes/phase25/partitions-and-reciprocals.md:261`](../partitions-and-reciprocals.md#L261)):**
   - *Issue:* Line 261 explicitly lists Andrews Ch. 1 and Stone–Weierstrass, but omits the standard Portmanteau characterization on continuity sets (used in E1.2 line 164) and sequential weak\* compactness of probability measures on $\mathbb{T}$ (Prokhorov/Helly, used in E2.3 line 204), as well as a one-line provisional-priority note per [`docs/research-objectives.md`](../../../docs/research-objectives.md) Rule 5.
   - *Fix:* Mention Portmanteau and weak\* compactness on $\mathbb{T}$ in the same sentence as Stone–Weierstrass on line 261, and note that novelty/priority claims are provisional.

8. **m8 — Compact top-level Evidence & Status Summary Table and printed finite-measurement values ([`notes/phase25/partitions-and-reciprocals.md:3-9,273`](../partitions-and-reciprocals.md#L3-L9)):**
   - *Issue:* Unlike Phase 24 Track C and Phase 25 Track F, the note lacks a top-level summary table consolidating every theorem, evidence label, standing objective, and finite-certificate anchor; and line 273 refers to "The reported transition counts in certified finite digit words" without printing the four script values `{'X(2,3)': 131, 'X(2,4)': 138, 'X(2,5)': 146, 'P(2)': 111}`.
   - *Fix:* Add a short Evidence & Status table after `## Definitions and scope`, and quote the four certified 256-digit transition counts explicitly under `Finite measurement.` on line 273.

---

## Verdict

**ACCEPT WITH MINOR POLISH.**

All mathematical proofs in Phase 25 Track E — including the flagship all-radix exact reciprocal discrepancy spectrum and limit-measure realization theorem **E1.2** ($\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ for every $b \ge 2$), the dyadic construction **E1**, the complete-period/worst-start/averaged-short-orbit results **E2.1–E2.3**, and the reciprocal-separation digit-transition and discrepancy-gap bounds **E3** ($X_{b,m}$) and **E4** ($P_b$ and $R_k^{(E)}$) — are rigorous and survive adversarial verification. Applying the eight Minor polishes **m1–m8** will make the note and finite certificate publication-grade and fully aligned with repository conventions.

**Cross-model review is not independent human peer review.** This audit was performed by one AI model (Gemini 4 Neon) on work drafted by another (Codex `gpt-6.2-astra`). Its conclusions rest on automated mathematical reasoning and finite auxiliary computations, and do not substitute for independent human refereeing or formal verification in Lean.
