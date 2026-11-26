# Cross-Provider Mathematical Referee Review: Phase 22 Track C (C1–C2)

**Audited files**
- Note: [`notes/phase22/nonlinear-equality-boundary.md`](../nonlinear-equality-boundary.md) (lines 1–286)
- Script: [`scripts/phase22_nonlinear_boundary.py`](../../../scripts/phase22_nonlinear_boundary.py) (lines 1–507)

**Verdicts**
- **Track C1 ($d = r = 2$):** **REVISE** — Zero Critical flaws; all core theorems (R1, R2, Lemma W, Wall's direction, R3, F, B for support runs, B′, M, U) are mathematically sound. Revision is requested to resolve **3 Major findings** (an unclosed bridge between support runs $\mathcal P_H$ in §4/§6 and collapsed rational-orbit runs $\mathcal P_H^{\mathrm{frac}}$ after Proposition M(2); an impossible example of "three level-1 pairs" in §5; and process language `"the brief"` plus a logical non-sequitur in §4 line 165) alongside Minor proof/script polishes.
- **Track C2 ($d = r = 3$):** **ACCEPT WITH MINOR POLISH** — Zero Critical and zero Major findings; R1, the linear mass bound, the conditional absorption analysis, external citations (Wooley 2015, DHL 2006), and finite measurements are sound and honestly scoped, with only minor precision polishes in §8.

> **Review scope caveat:** This is an automated cross-model mathematical audit, **not** independent human peer review.

---

## 1. Script Execution and Numerical Audit

- **Command:** `python -B scripts/phase22_nonlinear_boundary.py` (run from the worktree root).
- **Result:** Exit code `0`; internal timer `4.2 s` (~`5.9 s` wall-clock), matching §11 line 279 ("runs in about 4 seconds and exits 0").
- **Numerical consistency:** Every displayed numerical value across the Summary (line 31), §1 (lines 62, 72), §4 table (lines 167–175), §5 (line 197), §8 (lines 229–232), §9 table and prose (lines 249–255), and §11 (lines 279–284) matches the script stdout verbatim (within the displayed rounding).
  - Independently verified across all $1 \le N \le 2^{16}$ that $\min_{1 \le N \le 2^{16}} \delta_N(0) \approx 1.214141 > 1$ (attained at $N = 65522$), confirming line 255 ("$\delta_N(H) > 1$ for $N \le 2^{16}$").
  - Independently verified the exact interval arithmetic in `C_interval`, `power_interval`, and `frac_bits` (lines 282–319): rigorous. See **Minor 8** below regarding the hardcoded tail bound `1 << 14` in `integer_series_interval` (lines 322–328) and **Minor 2** regarding the threshold `Lq` in line 227.

---

## 2. Theorem-by-Theorem Audit Summary

| Component | Audit Outcome | Notes |
|---|---|---|
| **§1 Theorem R1 & Consequences 1–3** (lines 37–72) | **Sound** | Exact identity $p^{sH} C^r = X_H + Z_H$; Dirichlet integral mass bound $A_H(Y) \le p^{sH} V_{r,d} Y^{r/d}$ with $V_{2,2} = \pi/4$, $V_{3,3} = \Gamma(4/3)^3 \approx 0.7121$ holds without error term for all $Y \ge 0$ via disjoint unit cubes $\prod[i_j-1, i_j]$. Prefix identity and $q_n(Z_H) = q_n(C^r)/p^{\min(sH, v_p(q_n(C^r)))}$ are exact (note: $q_n(y)$ should be explicitly defined on first use at line 69). Total-level vs. max-valuation comparison (line 72) is exact. |
| **§2 Theorem R2** (lines 76–87) | **Sound** (Minor 1) | Constant $C = \pi p^{sH}/(4t)$ gives $4C/(b-1) = \pi p^{sH}/(t(b-1))$ in Phase 20 Theorem 1.5 (GF-02), and $2\log_b(1/\rho_N) = \log_b\log N + O(1)$ gives uniformity in $H$ since $\rho_N$ is independent of $H$. Line 86 should say support count is *at most* $S^+(\lfloor(N-1)/t\rfloor)$ and note monotonicity of $\rho \mapsto \rho(2\log_b(1/\rho)+K+3)$ on $(0,1]$ (valid since $3 > 2/\ln 2$). |
| **§2 Lemma W, Wall's Lemma, Corollary R3** (lines 88–114) | **Sound** | Both inequalities of Lemma W are airtight (arc concentration form $1-D_N = \inf_I(1-\mu_N(I)+|I|)$ handles $|I| < 1/M$ and $|I| \ge 1/M$ cleanly). Counterexample $x = 1/3$, $b = 2$ has $D_N(1/3;2) = 2/3$ for all $N \ge 2$ while $D_N(1;2) = 1$. Wall's ergodic proof and all three items of Corollary R3 are completely rigorous. |
| **§3 Proposition F** (lines 118–133) | **Sound** | Since $p \nmid b$, $p^{-s\ell} b^{n-tm} h \in \mathbb Z \iff p^{s\ell} \mid h \iff s\ell \le v_p(h)$. Item 2 inequality and $E_N^{(H)}(\varepsilon)/N \to 0$ for $H = o(\sqrt{\log N})$ hold by Phase 20 Theorem 1.4 with $L = \lceil\log_b(p^{sH}\log N)\rceil$. |
| **§4 Theorem B & Corollary B′** (lines 137–177) | **Sound for $\mathcal P_H$; Major 1–2, Minor 2–3** | Inclusion $p^{2k_H}\mathcal S^+ \subseteq \mathcal P_H \subseteq \mathcal S^+$ holds for every odd prime $p$. Hooley (1971, *Acta Math.* 127, 279–297) indeed gives $\sum_{s_{n+1}\le Y}(s_{n+1}-s_n)^\gamma \ll_\gamma Y(\log Y)^{(\gamma-1)/2}$ for $0 < \gamma < 5/3$, and Markov + $(\log Y)^{(\gamma-1)/2} \le (\log N)^{(\gamma-1)/2}$ yields the exact stated exponent. B(3) holds even when $v_p(q_n(C^2)) < sH$ because the RHS is then negative while $\log_b q_n(Z_H) \ge 0$. Growing-$H$ upper bound $\le (H+2)\frac{\pi}{4}p^{-(H+1)}Y$ is exact. Issues: Major 1 (bridge to collapsed rational-orbit runs), Major 2 (process language + non-sequitur on line 165), Minor 2–3. |
| **§5 Proposition M** (lines 179–199) | **Sound statement; Major 3, Minor 4** | Recursion $y_{k+1} = \{b^{\ell_k} y_k + z_0(m_{k+1})\}$ and equidistribution equivalence are sound. Line 197 gives an impossible example ("three level-1 pairs", Major 3); line 195 has a proof slip in the circle-perturbation step and uses undefined $\ell_{\max}(N)$ (Minor 4). |
| **§6 Lemma U & barrier conclusion** (lines 201–211) | **Lemma U sound; Major 1, Minor 5** | Lemma U is valid for integer $T \le \log_b(\varepsilon q)$ (and can be strengthened from $2\pi|h|\varepsilon T$ to $2\pi|h|\varepsilon/(b-1)$ via the geometric sum, Minor 5). Its application on line 211 to all short-orbit methods rests on Theorem B's support runs $\mathcal P_H$ rather than the collapsed rational-orbit runs $\mathcal P_H^{\mathrm{frac}}$ (Major 1). |
| **§7 Variants at $d = 2$** (lines 213–223) | **Mostly sound; Major 2, Minor 6** | $s \ge 1$, $p \nmid b$, sparse $A$, and mixed $i^2+j^3$ entries are accurate (and $v_p(i^2+j^2)=2\min(v_p(i),v_p(j))$ holds iff $p \equiv 3 \pmod 4$). Remove `"The brief's claim"` on line 218 (Major 2) and qualify Bernays / binary quadratic forms on line 219 (Minor 6). |
| **§8 Cubic boundary C2** (lines 225–243) | **Sound** (Minor 7) | R1, mass bound, Wooley (2015, *Acta Arith.* 170, $\gg Y^{0.91709477}$), upper bound $(\Gamma(4/3)^3/6+o(1))Y \approx 0.1187Y$, DHL (2006, ANTS VII, $\approx 0.0999$), $27^k\mathcal S_{3,3} \subseteq \mathcal P_H^{(3)} \subseteq \mathcal S_{3,3}$, Phase 21 Proposition D ($\le C(\log L)^{-3/2}$), and mod-9 check are all accurate. Three minor precision polishes (Minor 7). |
| **§9–§11 Measurements, Status, Checks** (lines 245–286) | **Sound** (Minor 8) | Clear separation between proved theorems, conditional statements, external inputs, finite measurements, and open problems. No overclaims on normality, simple normality, or $D^+ < 1$. |

---

## 3. Detailed Findings

### Critical Findings

None.

---

### Major Findings

#### Major 1 (C1): Unclosed bridge between support runs ($\mathcal P_H$) in §4/§6 and collapsed rational-orbit runs ($\mathcal P_H^{\mathrm{frac}}$) in §5
- **Files / lines:**
  - `notes/phase22/nonlinear-equality-boundary.md`, lines 137–157 (Theorem B), line 186 (Proposition M(2)), line 211 (§6).
- **Issue:**
  - Theorem B defines a *run* of $Z_H$ as a shift interval $[tm, tm')$ between consecutive elements of the coefficient support $\mathcal P_H = \{m \in \mathcal S^+ : z_H(m) > 0\}$, and proves the density-one short-run bound (length $< \varepsilon \log N$) solely from the inclusion $p^{2k_H}\mathcal S^+ \subseteq \mathcal P_H$ and Hooley's gap-moment theorem for $\mathcal S$.
  - However, Proposition M(2) (line 186) explicitly establishes that **integer jumps leave the rational orbit unchanged**: for any $H \ge 0$, the rational prefix orbit $\{b^n R_n(Z_H)\}$ only changes phase at positions in the strictly smaller set $\mathcal P_H^{\mathrm{frac}} := \{m \in \mathcal P_H : z_H(m) \notin \mathbb Z\}$. Because Proposition M(3) already reduces $D_N(Z_H)$ to the rational prefix orbit (up to $o(1)$, since $\tau_n \to 0$ in density), an attempt to apply a uniform short-orbit bound (e.g., Korobov's method) to the rational prefix orbit only needs runs between consecutive elements of $\mathcal P_H^{\mathrm{frac}}$, not $\mathcal P_H$.
  - Accidental integer jumps $z_H(m) \in \mathbb Z$ genuinely occur inside $\mathcal P_H$ **and** inside $p^{2k_H}\mathcal S^+$: for $C(2,3,1,2)^2$ ($p=3, s=1$), we verified that:
    - at $H = 0$, $67$ of the $62{,}264$ positions in $\mathcal P_0 \cap [1, 5\cdot 10^5]$ have $z_0(m) \in \mathbb Z$ (first examples: $m = 16810, 21853, 28090$, each with $z_0(m) = 2$);
    - at $H = 1$, $347$ elements of $9\mathcal S^+ \cap [1, 5\cdot 10^5]$ have $z_1(m) \in \mathbb Z$ (first example: $m = 450 = 9 \cdot 50$ with representations $(3,21), (15,15), (21,3)$, giving $z_1(450) = 3 \cdot \frac{1}{3} = 1$).
  - Thus $p^{2k_H}\mathcal S^+ \not\subseteq \mathcal P_H^{\mathrm{frac}}$. Removing even a small positive-relative-density subset from $\mathcal S$ is not automatically controlled by Hooley's moment bound on $\mathcal S$ alone (without an additional arithmetic/sieve argument preventing clustering of deleted points). Hence Theorem B + Lemma U rigorously rules out uniform short-orbit bounds on **support runs** of $Z_H$, but leaves a small logical gap if read (as line 211 suggests) as ruling them out on the **merged rational-orbit runs** between consecutive fractional jumps $\mathcal P_H^{\mathrm{frac}}$.
- **Actionable fix:** Either (a) explicitly qualify §4 (line 151) and §6 (line 211) as applying to the **support runs** of $Z_H$ (intervals where $R_n(Z_H)$ is constant, before merging across accidental integer jumps $z_H(m) \in \mathbb Z$) and note explicitly that proving the analogous gap-moment bound for the thinned set $\mathcal P_H^{\mathrm{frac}}$ would require a sieve/moment extension of Hooley (1971) to non-cancelling representations; or (b) supply a rigorous gap bound for $\mathcal P_H^{\mathrm{frac}}$.

#### Major 2 (C1): Process language (`"the brief"`) and logical non-sequitur in §4 line 165
- **Files / lines:**
  - `notes/phase22/nonlinear-equality-boundary.md`, lines 165 and 218.
  - `scripts/phase22_nonlinear_boundary.py`, line 218.
- **Issue:**
  1. **Process language:** Lines 165 (`"The brief counted pairs..."`) and 218 (`"The brief's claim that p \nmid m makes the jump integral is false..."`) in the note—and line 218 (`# the split by max(h1, h2) >= K proposed in the brief`) in the script—refer to an internal task brief that is unavailable to a mathematical reader.
  2. **Logical non-sequitur (line 165):** Line 165 states: *"Fixed-depth retirement multiplies the mean run length by a bounded factor, at most $\asymp p^{2k_H}$. It does not multiply it by $p^K$ asymptotically."* For the split $C = C_{<K} + C_{\ge K}$, the corresponding total-level depth is $H = 2K - 2$, for which $2k_H = 2K$ and hence $p^{2k_H} = p^{2K} > p^K$. An upper bound of $\asymp p^{2k_H}$ on the asymptotic ratio of mean run lengths does **not** logically imply that the ratio fails to reach $p^K$. (The claim is in fact true for a deeper reason not proved in the note—equidistribution of Gaussian prime factors in $(\mathbb Z[i]/(p^{H+1}))^\times$ puts a positive proportion of $\mathcal S^+$ independent of $H$ into $\mathcal P_H$—but Theorem B(1) does not establish this.)
- **Actionable fix:**
  - Remove all references to `"the brief"` in `notes/phase22/nonlinear-equality-boundary.md` (lines 165, 218) and `scripts/phase22_nonlinear_boundary.py` (line 218), recasting them as self-contained mathematical remarks (e.g., *"Pair counts versus distinct positions."* on line 165, and *"Note that $p \nmid m$ does not force the jump to be integral..."* on line 218).
  - Replace the unsupported sentence on line 165 with what Theorem B(1) actually proves: for any fixed $K$ (or $H$), retiring pairs with $\max(v_p(i),v_p(j)) < K$ (or level $\le H$) multiplies the mean run length by at most a bounded constant ($\le p^{2K}$ or $p^{2k_H}$), leaving the mean run length $\asymp_K \sqrt{\log N}$ and below $\varepsilon\log N$ on density one; reaching gap $\gg \log N$ via growing $K$ (such as $K = 2\log_p\log N$, where pair density gives $O(N/(\log N)^2)$ positions) falls in the second regime of Corollary B′ with multiplier $(\log N)^{2s}$.

#### Major 3 (C1): Impossible example in §5 (`"three level-1 pairs giving 3 · 1/3"`)
- **Files / lines:**
  - `notes/phase22/nonlinear-equality-boundary.md`, line 197.
- **Issue:** Line 197 states: *"Integrality can also come from cancellation, for example three level-1 pairs giving $3\cdot\frac13$."* This is **mathematically impossible**. An ordered pair $(i, j) \in \mathbb Z_{\ge 1}^2$ has level $v_p(i) + v_p(j) = 1$ if and only if $\{v_p(i), v_p(j)\} = \{0, 1\}$, which forces $i \ne j$. Consequently, the swap $(i, j) \mapsto (j, i)$ is a fixed-point-free involution on the ordered level-1 pairs at any position $m$, so every position $m$ has an **even** number of ordered level-1 pairs (never $3$).
- **Actionable fix:** Replace *"three level-1 pairs giving $3\cdot\frac13$"* with *"six level-1 pairs giving $6\cdot\frac13 = 2$ (e.g., $m = 16810$, whose six ordered representations are $(13,129), (41,123), (67,111)$ and their reversals)"* (or, if illustrating an odd multiplicity via a diagonal pair at $H = 1$, $m = 450$ with $(3,21), (15,15), (21,3)$ giving $z_1(450) = 3 \cdot \frac{1}{3} = 1$). Optionally replace *"cancellation"* with *"summing to an integer"* (since all terms are positive).

---

### Minor Findings

#### Minor 1 (C1, §2): Support-count equality vs. inequality and monotonicity in proof of Theorem R2
- **File / line:** `notes/phase22/nonlinear-equality-boundary.md`, line 86.
- **Issue:** Line 86 says *"Its support count up to $N-1$ is $S^+(\lfloor(N-1)/t\rfloor)$."* In fact, $a_H(m) = 0$ whenever all positive representations of $m \in \mathcal S^+$ have level $> H$ (e.g., $m = 18 = 3^2 + 3^2$ has unique positive representation $(3,3)$ of level $2$, so $a_0(18) = a_1(18) = 0$). Thus the support count $\tilde S(N-1)$ is **at most** $S^+(\lfloor(N-1)/t\rfloor)$, giving $\tilde\rho_N \le \rho_N \le 1$. Substituting $\rho_N$ for $\tilde\rho_N$ in Phase 20 Theorem 1.5 is valid because $f(\rho) = \rho(2\log_b(1/\rho) + K + 3)$ has $f'(\rho) = \frac{2}{\ln b}\ln(1/\rho) + (3 - \frac{2}{\ln b}) + K > 0$ on $(0, 1]$ for every $b \ge 2$ and $K \ge 0$ (since $3 > 2/\ln 2 \approx 2.8854$).
- **Actionable fix:** Change *"is $S^+(\lfloor(N-1)/t\rfloor)$"* to *"is at most $S^+(\lfloor(N-1)/t\rfloor)$"* and add one clause noting monotonicity of $\rho \mapsto \rho(2\log_b(1/\rho) + K + 3)$ on $(0,1]$ since $3 > 2/\ln 2$.

#### Minor 2 (C1, §4 & Script): Threshold `Lq` off by $1$ from its comment and held fixed across $H$
- **Files / lines:** `scripts/phase22_nonlinear_boundary.py`, lines 163, 226–233; `notes/phase22/nonlinear-equality-boundary.md`, lines 169–175.
- **Issue:**
  - Script line 226 comments `log_2(q/2) ~ log_2(X) - 1`, yet line 227 computes `Lq = log(T * X, 2) - 1 = log_2(2X) - 1 = log_2(X) ≈ 18.93` (instead of `log_2(X) - 1 ≈ 17.93`).
  - Moreover, at $n \le TX = 10^6$, the shell power is $3^{2J} \le 3^{10} = 59049$ ($\log_2(3^{10}/2) \approx 14.85$), and for $Z_H$ the denominator drops further by $3^H$ ($-H\log_2 3$ bits). Applying the fixed threshold $18.93$ across all $H$ simply duplicates `cover(gap >= 10)` from the previous table (since $2\cdot\text{gap} \ge 18.93 \iff \text{gap} \ge 10$).
  - Also in `gap_profile` (script line 163), the leading entry is `pos[0]` rather than `pos[0] - 1`, making gap lengths sum to $X + 1$ rather than $X$ (a $2 \times 10^{-6}$ effect, invisible at 3 decimals).
- **Actionable fix:** Either fix `Lq` to match the comment (or use the actual $H$-dependent threshold $\log_2(q_n(Z_H)/2)$) and refresh the table column, or relabel the table column accurately as `"shifts in runs >= log_2(X) ≈ 18.9 (position gap >= 10)"` and update the script comment on line 226. Fix `pos[0] - 1` in `gap_profile` if desired.

#### Minor 3 (C1, §4): Small technical omissions in Theorem B, its proof, and Corollary B′
- **File / lines:** `notes/phase22/nonlinear-equality-boundary.md`, lines 69, 142–163.
- **Issues:**
  1. **Line 69:** $q_n(y)$ is used before being explicitly defined as the reduced denominator of $b^n R_n(y)$.
  2. **Theorem B(2), line 148:** *"The same holds with $H = H(N)$ whenever $p^{H(N)} = o(\sqrt{\log N})$."* Because the preceding sentence gives only the $O$-bound (already uniform up to $p^{2k_H} \le N^{1/2}$) without writing `-> 0`, `"The same"` is imprecise; clarify that the proportion **tends to $0$** for fixed $H$ and whenever $p^{H(N)} = o(\sqrt{\log N})$ (for $N \ge (2t)^2$, or $N$ sufficiently large).
  3. **Proof of B(2), lines 155–157:**
     - A run $[tm, tm')$ of length $t(m'-m) \ge G$ already has position gap $m'-m \ge G/t$ (the `"-1"` and factor `1/2` in `g = eps log N / (2tQ)` are unnecessary).
     - Relating gaps of $\mathcal S^+$ to gaps of $\mathcal S$ on line 157 invokes Bambah–Chowla *"near $Y$"* (*"for large $Y$"*), which does not strictly cover small elements of $[1, Y]$. In fact, for **every** $k \ge 1$, $k^2 < k^2 + 1^2 < (k+1)^2$, so no two consecutive elements of $\mathcal S \cap [1, \infty)$ are both outside $\mathcal S^+$; thus every gap of $\mathcal S^+$ on $[2, \infty)$ is either one or two adjacent gaps of $\mathcal S$ unconditionally (and the factor $3$ can even be tightened to $2$).
     - The boundary gap has shift length $O(tQY^{1/4})$ (proportion $O(Y^{-3/4})$); adding one clause noting that it only contributes when $\varepsilon \log N \ll tQY^{1/4}$, in which case $Y^{-3/4} \ll Y^{-(\gamma-1)/4}(\log N)^{(\gamma-1)/2} \ll (tQ/\varepsilon)^{\gamma-1}(\log N)^{-(\gamma-1)/2}$ (since $(\gamma-1)/4 < 1/6 < 3/4$), closes uniformity in $\varepsilon$.
  4. **Theorem B(3), lines 149 & 161:** State $L \ge 3$ explicitly (inherited from Phase 21 Proposition D) and note $n \ge 1$ (so $\log_b(n/t)$ is defined); on line 161, add *"and then let $L \to \infty$"* after intersecting the sets of (2) and (3) to justify density one.
  5. **Corollary B′, line 163:** For varying $H(N)$ along a subsequence, write *"a proportion $1 - o(1)$ of shifts $n < N$"* rather than *"density one of shifts"*, and *"positive proportion of shifts in runs"* rather than *"positive proportion of runs"* (matches Theorem B(2) directly). In the opposite regime $p^H \gg H\log N$, write *"multiplier $\gg (H\log N)^s \gg (\log N)^s$"* (for large $N$) rather than *"$\ge (\log N)^s$"*.
- **Actionable fix:** Incorporate these brief clarifications directly into lines 69 and 142–163.

#### Minor 4 (C1, §5): Proof slip in circle-perturbation collars and undefined $\ell_{\max}(N)$ in Proposition M(3)
- **File / lines:** `notes/phase22/nonlinear-equality-boundary.md`, lines 190 and 195.
- **Issues:**
  1. Line 195 claims *"each interval count changes by at most the count in two $\varepsilon$-collars plus $G$, so $|D(z) - D(z')| \le 2\varepsilon + G/N$."* The **count** of points in two $\varepsilon$-collars is not bounded by $2\varepsilon N$ (all $N$ points could sit in one collar). The inequality $|D_N(z) - D_N(z')| \le 2\varepsilon + G/N$ is true, but follows by arc enlargement: for any circle arc $I$ and its $\varepsilon$-neighborhood $I^{+\varepsilon}$, $\mu_N(z; I) - |I| \le \mu_N(z'; I^{+\varepsilon}) - |I^{+\varepsilon}| + (|I^{+\varepsilon}| - |I|) + G/N \le D_N(z') + 2\varepsilon + G/N$, and likewise for $I^c$ and with $z, z'$ swapped.
  2. $\ell_{\max}(N)$ on line 190 is not defined (presumably $\max_{tm_k \le N} \ell_k$), nor is $\ell_{\max}(N) = o(N)$ stated (it is $O(\sqrt{N})$ trivially via $k^2 + 1^2$, or $O(N^{1/4})$ via Bambah–Chowla). Also, the concatenated sequence $\{b^j y_k\}_{k \ge 1, 0 \le j < \ell_k}$ starts at shift $tm_1 = 2t$ rather than $n = 0$; when truncated literally to $N$ terms, there is no incomplete-final-run discrepancy at all—only the $2t$ offset shifts at the endpoints, contributing at most $2t/N$ (whereas comparing to complete runs before $N$ introduces the $O(\ell_{\max}(N)/N)$ term).
- **Actionable fix:** Correct the one-line collar argument on line 195 via arc enlargement $I^{+\varepsilon}$, define $\ell_{\max}(N)$ (and note $\ell_{\max}(N) = o(N)$) or simplify to the exact $2t/N$ offset bound when truncating to $N$ terms.

#### Minor 5 (C1, §6): Strengthenable bound and integer-$T$ hypothesis in Lemma U
- **File / lines:** `notes/phase22/nonlinear-equality-boundary.md`, lines 203–209.
- **Issue:** Lemma U implicitly takes $T \in \mathbb Z_{\ge 1}$ (so $j < T \implies j \le T - 1 \implies b^j/q \le \varepsilon/b$). With the stated bound $2\pi|h|\varepsilon T$, the conclusion *"No bound ... beats the trivial one"* only becomes nontrivial once $2\pi|h|\varepsilon < 1$, rather than for all $0 < \varepsilon < 1$. Summing the geometric series directly gives
  $$\Bigl|\sum_{j=0}^{T-1} e(h b^j / q) - T\Bigr| \le 2\pi|h| \sum_{j=0}^{T-1} \frac{b^j}{q} = 2\pi|h|\frac{b^T - 1}{(b-1)q} < \frac{2\pi|h|\varepsilon}{b-1} \le 2\pi|h|\varepsilon,$$
  removing the factor $T$ completely and yielding $|\sum_{j<T} e(hb^j/q)| \ge T - O_h(1)$ for every $0 < \varepsilon < 1$.
- **Actionable fix:** State $T \in \mathbb Z_{\ge 1}$ and use the geometric sum bound $2\pi|h|\varepsilon/(b-1)$ (which also implies $2\pi|h|\varepsilon T$).

#### Minor 6 (C1, §7): Small caveats in §7 Variants table
- **File / lines:** `notes/phase22/nonlinear-equality-boundary.md`, lines 218–219.
- **Issues:**
  - Line 218: *"$(pa)^2 + j^2$ has level $\ge 1$ with $p \nmid m$"* requires $p \nmid j$.
  - Line 219: *"Other positive definite binary forms $tQ(i,j)$ | Positions are values of a binary form, again $\asymp X/\sqrt{\log X}$ (Bernays; literature input, not checked). Same barrier."* Note that only diagonal forms $ai^2 + cj^2$ arise as products of two one-variable series (general $Q$ is a bivariate series), and Bernays (1912) supplies only the support count $\asymp X/\sqrt{\log X}$ (hence mean run length $\asymp \sqrt{\log N}$); the full density-one barrier (analogues of Theorem B(2)–(3)) would additionally require a Hooley-type gap-moment bound for $Q(i,j)$ ($i,j\ge 1$) and a denominator-depth result for the corresponding series.
- **Actionable fix:** Add `"$p \nmid j$"` on line 218 and qualify `"Same barrier"` on line 219 as `"Same mean-gap barrier ($\asymp \sqrt{\log N}$); full density-one barrier would need a gap-moment bound for $Q$ and denominator depth (for diagonal $ai^2+cj^2$, products of two series)."`.

#### Minor 7 (C2, §8): Three small precision polishes in the $d = 3$ discussion
- **File / lines:** `notes/phase22/nonlinear-equality-boundary.md`, lines 230–232 and 238–239.
- **Issues:**
  1. **Line 230:** *"If the density is positive, $X_0$ is an integer-coefficient series with positive-density support."* Formally, unordered triples of level $\ge 1$ (at least one coordinate divisible by $3$) can cover density at most $\frac{19}{27} \cdot \frac{\Gamma(4/3)^3}{6} \approx 0.0835$. Thus positive density $\delta > 0$ of $\mathcal S_{3,3}$ forces $\operatorname{supp}(X_0)$ to have positive density when $\delta > 0.0835$ (in particular, under the DHL prediction $0.0999$), and for arbitrary $\delta > 0$ forces $\operatorname{supp}(X_H)$ to have positive density for all sufficiently large $H$ (since level-$>H$ triples have density $\to 0$ as $H \to \infty$), but does not logically force positive density of $\operatorname{supp}(X_0)$ at arbitrarily small $\delta > 0$.
  2. **Lines 231–232:** Positive *upper* density of $\mathcal P_H^{(3)}$ implies mean run length $O_H(1)$ along a subsequence ($\liminf$), not necessarily for all $N$ (which needs positive *lower* or natural density). On line 232, *"the runs are $O(1)$ conditionally"* should say *"the mean run length is $O(1)$ conditionally"*.
  3. **Lines 230 & 238:** On line 230, cite Hooley (1986) / Heath-Brown (1998) for the conditional $\gg Y^{1-\varepsilon}$ bound and write *"for certain Hasse–Weil $L$-functions"* (plural, a family of $L$-functions rather than a single one). On line 238, change *"Conditional on density zero (expected false)"* to *"Conditional on density zero (hypothesis expected false)"* to avoid misreading as asserting $X_H \notin K_b$.
- **Actionable fix:** Apply these three wording refinements in §8.

#### Minor 8 (Script): Docstring mismatch and hardcoded tail bound in `integer_series_interval`
- **File / lines:** `scripts/phase22_nonlinear_boundary.py`, lines 322–328.
- **Issue:** `integer_series_interval(coef, Q)` has docstring `exact floor plus tail bound 1` while actually adding `1 << 14` with `# generous bound for the omitted far tail`, without verifying the tail bound from `coef`. (Independent audit confirms soundness for the script's actual call $H \in \{0, 1\}$, $Q = 65728$: using $a_H(m) \le 3^H \rho_{2,2}(m) \le 3^H \tau(m) \le 2\cdot 3^H \sqrt{m}$, the omitted tail $2^Q \sum_{2m > Q} a_H(m) 2^{-2m}$ is rigorously $\le 365 < 2^{14} = 16384$.)
- **Actionable fix:** Update the docstring to state the actual tail bound parameter (or pass an explicit `tail_bound` computed from $2\cdot 3^H \sqrt{Q/2 + 1}/3 + 2\cdot 3^H$) so certification does not depend on an undocumented constant. Also remove unused locals `AH = 0`, `idx = 0` on lines 109–111.

---

## 4. Scope Honesty and Literature Audit

- **No overclaims on open problems:** The Summary (line 30), §8 (line 230), §9 (line 255), and §10 (lines 273–275) cleanly separate proved results, conditional statements, external inputs, finite measurements, and open questions. Normality, simple normality, $D^+ < 1$, and even $C^2 \notin K_b$ remain explicitly marked **Open**.
- **Process language:** Two instances of `"the brief"` in the note (lines 165, 218) and one in the script (line 218) should be removed (captured in **Major 2**).
- **External inputs checked:**
  - **Landau (1908):** $S(Y) \sim K_{\rm LR} Y / \sqrt{\log Y}$, $K_{\rm LR} \approx 0.7642$. Accurate.
  - **Bambah–Chowla (1947):** $s_{n+1} - s_n \ll s_n^{1/4}$ for sums of two squares. Accurate.
  - **Hooley (1971):** $\sum_{s_{n+1}\le Y}(s_{n+1} - s_n)^\gamma \ll_\gamma Y(\log Y)^{(\gamma-1)/2}$ for $0 < \gamma < 5/3$. Exact hypotheses and exponent verified.
  - **Bernays (1912):** $\asymp X/\sqrt{\log X}$ for positive definite binary quadratic forms. Accurate for counts (see **Minor 6**).
  - **Wooley (2015, *Sums of three cubes II*):** $|\mathcal S_{3,3}\cap[1,Y]| \gg Y^{0.91709477}$. Verified.
  - **Deshouillers–Hennecart–Landreau (2006):** Heuristic density $\approx 0.0999425\dots \approx 0.0999$ for sums of three cubes. Verified.
  - **Conditional $Y^{1-\varepsilon}$ for three cubes:** Hooley (1986) / Heath-Brown (1998) under GRH/automorphy for families of Hasse–Weil $L$-functions (see **Minor 7**).

---

## Post-Repair Verification

### 1. Re-run of Exact Checks
- **Command:** `python -B scripts/phase22_nonlinear_boundary.py` (run from the worktree root).
- **Result:** Exit code `0`, internal timer `5.1 s` (`5.5 s` wall-clock), matching §11 line 334 ("runs in about 5 seconds and exits 0").
- **Numerical audit:** Every updated constant and table cell matches script stdout verbatim:
  - §4 depth thresholds $\lambda_H = \log_2(3^{10-H}/2)$: `14.85, 13.26, 11.68, 10.09` ($H=0..3$) and `14.85` ($C^2$).
  - §4 table (lines 207–211): support-run coverages (`0.395, 0.751, 0.918, 0.988, 0.998`), integral jump counts (`67, 361 [347 in 9S^+], 4, 47`), $|\mathcal P_H^{\rm frac}|$ (`62197, 38742, 17045, 7589`), and fractional-run coverages (`0.752, 0.919, 0.988, 0.998`), differing by at most `0.001`.
  - §4 line 195: $|\mathcal F_3 \cap [1, 5\cdot 10^5]| = 31909$, and the inclusion $9^{k_H}\mathcal F_3 \subseteq \mathcal P_H^{\rm frac}$ is asserted exactly for $H \le 3$.
  - §5 line 243: `m = 16810` has the six asserted level-1 representations `[(13, 129), (41, 123), (67, 111), (111, 67), (123, 41), (129, 13)]` giving $z_0(16810) = 6/3 = 2$, and `m = 450` gives $z_1(450) = 3/3 = 1$.
  - §11 line 339: Lemma U geometric-sum check verified exactly for $q = 3^{20}, 3^{40}, 3^{80}$ ($T = 25, 57, 120$).
- **Process-language grep:** Zero remaining occurrences of `"brief"` in either audited file.

### 2. Audit of New Proposition B″ (lines 181–195)
Proposition B″ and its proof were checked adversarially line by line and are **sound**:
1. **Level exactness (line 189):** For $p \equiv 3 \pmod 4$, $m = p^{2k} n$ with $p \nmid n$ forces $p^k \mid i, j$ via $v_p(i^2+j^2) = 2\min(v_p(i),v_p(j))$. If $p \mid i'$ in $i'^2 + j'^2 = n$, then $n \equiv j'^2 \pmod p$ would force $(n/p) = +1$, contradicting $(n/p) = -1$. Hence every representation of $m$ has level exactly $2k = 2k_H > H$.
2. **Exact value of $z_H(p^{2k_H} n)$ (line 191):** Any squarefree $n \in \mathcal S^+$ satisfies $n > 1$, is not a square (so no zero-coordinate representations exist), and has no prime factor $\equiv 3 \pmod 4$. Thus the number of ordered positive representations is $r_2(n)/4 = \sum_{d \mid n} \chi_{-4}(d) = 2^{\omega_1(n)}$, which is coprime to the odd prime $p$. Since $s(2k_H - H) \ge 1$, $z_H(p^{2k_H}n) = 2^{\omega_1(n)} p^{-s(2k_H - H)} \notin \mathbb Z$ holds identically.
3. **Selberg–Delange asymptotic (line 193):** Because $p \equiv 3 \pmod 4$, the multiplicative function $g = \mu^2 \mathbf 1_{\mathcal S}$ vanishes whenever $p \mid n$, so $\mathbf 1_{\mathcal F_p}(n) = \frac{1}{2} g(n)(1 - \chi_p(n))$ holds for every $n \ge 1$ (including $n = 1$, where $\chi_p(1) = 1$). The Euler products satisfy
   $$\frac{\sum g(n)n^{-s}}{(\zeta(s)L(s,\chi_{-4}))^{1/2}} = (1+2^{-s})(1-2^{-s})^{1/2}\prod_{q\equiv 1(4)}(1-q^{-2s})\prod_{q\equiv 3(4)}(1-q^{-2s})^{1/2},$$
   $$\frac{\sum g(n)\chi_p(n)n^{-s}}{(L(s,\chi_p)L(s,\chi_p\chi_{-4}))^{1/2}} = (1+\chi_p(2)2^{-s})(1-\chi_p(2)2^{-s})^{1/2}\prod_{q\equiv 1(4)}(1-q^{-2s})\prod_{\substack{q\equiv 3(4)\\q\ne p}}(1-q^{-2s})^{1/2},$$
   both holomorphic and nonzero on $\operatorname{Re}(s) > 1/2$. Since $\chi_p$ and $\chi_p\chi_{-4}$ are real nonprincipal Dirichlet characters (conductors $p$ and $4p$), $L(s,\chi_p)L(s,\chi_p\chi_{-4})$ is holomorphic and nonvanishing in a classical zero-free region around $s=1$ (with positive value at $s=1$). Tenenbaum II.5 (Selberg–Delange) therefore gives $\sum_{n \le Y} g(n) \sim c Y / \sqrt{\log Y}$ ($c > 0$) and $\sum_{n \le Y} g(n)\chi_p(n) = o(Y/\sqrt{\log Y})$, whence $|\mathcal F_p \cap [1, Y]| \sim \frac{c}{2} Y/\sqrt{\log Y}$ and $|\mathcal P_H^{\rm frac} \cap [1, Y]| \asymp_H Y/\sqrt{\log Y}$.
4. **Scope honesty (line 195, §6, §10):** The note clearly separates what is proved (mean fractional-run length $\asymp_H \sqrt{\log N}$ for $p \equiv 3 \pmod 4$) from what remains unproved (density-one short fractional runs; anything on fractional runs for $p \equiv 1 \pmod 4$).

### 3. Finding-by-Finding Repair Checklist

| Original Finding | Verification Status | Notes |
|---|---|---|
| **Major 1** (Support runs $\mathcal P_H$ vs. fractional runs $\mathcal P_H^{\rm frac}$) | **Resolved** | Theorem B rescoped cleanly to support runs (lines 140–179); Proposition B″ added for fractional runs when $p \equiv 3 \pmod 4$ (lines 181–195); Summary, §6, §8, and §10 updated consistently. |
| **Major 2** (`"the brief"` + line 165 non-sequitur) | **Resolved** | All `"brief"` references removed in both files; lines 199–201 replace the unsupported $p^K$ sentence with the exact bound $(1+o(1))Q$ ($Q = p^{2K}$ or $p^{2k_H}$) from Theorem B(1). |
| **Major 3** (Impossible `"three level-1 pairs"` example) | **Resolved** | Replaced on line 243 with verified $m = 16810$ (six level-1 pairs, $z_0 = 2$), parity explanation ($v_p(i)\ne v_p(j) \implies i \ne j$), and diagonal example $m = 450$ ($z_1 = 1$), both asserted in script lines 254–262. |
| **Minor 1** (Theorem R2 support-count inequality & monotonicity) | **Resolved** | Lines 87–89 explicitly state *"at most"* (citing $m = 18$) and verify $f'(\rho) > 0$ on $(0,1]$ since $3 > 2/\ln 2$. |
| **Minor 2** (`Lq` threshold & `gap_profile`) | **Resolved** | Script lines 163–164 partition $[1, X]$ exactly (`sum(gaps) == X`); lines 218–258 and note lines 203–213 use the exact $H$-dependent top-shell threshold $\lambda_H = \log_2(3^{10-H}/2)$ and report both support and fractional runs. |
| **Minor 3** (Theorem B & Corollary B′ technical omissions) | **Resolved** | $q_n(y)$ defined at line 64; B(2) clarifies $\to 0$, drops unnecessary $-1$ and $1/2$, uses $k^2 < k^2+1^2 < (k+1)^2$ unconditionally with factor $2$, and verifies uniformity in $\varepsilon$ for the final partial gap; B(3) specifies $L \ge 3$, $n \ge t$, negative-RHS case, and $L \to \infty$; B′ uses *"proportion $1-o(1)$"*, *"shifts in support runs"*, explicit level count, and $\gg (H\log N)^s \gg (\log N)^s$. |
| **Minor 4** (Proposition M(3) collar proof & initial shift) | **Resolved** | Lines 223–241 use arc enlargement $I^{+\varepsilon}$ rigorously and state the exact $4t/N$ endpoint-shift bound without undefined $\ell_{\max}(N)$. |
| **Minor 5** (Lemma U geometric bound & integer $T$) | **Resolved** | Lines 249–255 and script lines 534–545 state integer $T \ge 1$ and prove/verify the sharper geometric-sum bound $2\pi|h|\varepsilon/(b-1)$. |
| **Minor 6** (§7 Variants caveats) | **Resolved** | Line 268 adds $p \nmid j$; line 269 distinguishes diagonal vs. bivariate forms and scopes Bernays to the mean-gap barrier. |
| **Minor 7** (§8 C2 precision polishes) | **Resolved** | Lines 280–293 cite Hooley (1986) / Heath-Brown (1998) for Hasse–Weil $L$-functions, include the exact $0.0835 Y$ threshold for $\operatorname{supp} X_0$ vs. $\operatorname{supp} X_H$, distinguish upper vs. lower density for mean run length $O_H(1)$, and clarify `(hypothesis expected false)`. |
| **Minor 8** (`integer_series_interval` tail bound & unused locals) | **Resolved** | Unused locals removed; script lines 363–377 prove and assert $a_H(m) \le 3^H \sqrt{m}$ and compute the explicit rigorous tail bound $3^H(\operatorname{isqrt}(Q/2+1)+1)$ (verified: $\sqrt{Q/2+u} \le \sqrt{Q/2+1}\sqrt{u}$ and $\sum_{u\ge 1}\sqrt{u}4^{-u} < 0.381 < 0.41 < 1$). |

### 4. Updated Verdicts
- **Track C1 ($d = r = 2$):** **ACCEPT** — All 3 Major and 7 C1-relevant Minor findings are resolved cleanly; the newly added Proposition B″ and explicit interval tail bound are mathematically rigorous and accurately scoped.
- **Track C2 ($d = r = 3$):** **ACCEPT** — All C2 Minor findings in §8 are resolved cleanly with zero remaining issues.

> **Review scope caveat:** This post-repair verification is an automated cross-model audit, **not** independent human peer review.
