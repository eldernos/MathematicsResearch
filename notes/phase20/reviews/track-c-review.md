# Independent Referee Review — Phase 20 Track C

**Reviewed files:**
- `notes/phase20/cubic-power-schedule.md` (Track C3)
- `notes/phase20/all-prime-polynomials.md` (Tracks C1 & C2)
- `NormalityChecker/ProtectedPole.lean` (Lean formalization for C1)
- `scripts/phase20_normality.py` (exact computational checks)

---

## Executive Summary & Verdicts

| Track | Result | Verdict | Summary |
|---|---|---|---|
| **C3** (`cubic-power-schedule.md`) | Polynomials of degree $r < d$ in $C(b,p,s,d)$ are normal | **REVISE (fixable gaps; no fatal obstruction)** | The core analytic engine (small-loss dominant anchors, Lemma 2 via reverse Fatou + Lebesgue density, $|B| < p^{-cH}$ vs. $|B| \ge p^{-cH}$ dichotomy, $\Phi_q$ derivative recurrence, Titchmarsh 5.13 + Erdős–Turán exponent bookkeeping, and real-orbit transfer) is **mathematically sound**. However, the $B = 0$ coincidence proof has a **genuine bug** (it assumes $k'_j \le k_j$ without deriving $x = z \implies v' = v$ and breaks literally when $p \le r$ allows $H' > H$), the $\beta < 1$ / all-$r$ exponent-covering proof is incomplete, and several analytic reduction steps are omitted. Every gap has an explicit, clean fix detailed below. |
| **C1** (`all-prime-polynomials.md` §§1–6) | $P(W)$ normal & Liouville with rate $\exp(-c(\log N)^{2/3})$ | **ACCEPT (minor polish)** | Completely sound. Window rule, pole dominance (Lemma 1), Kummer bound, Chebyshev/Erdős support estimate, surviving-grid loss, $b^c$-shift rational clearing, exact constant $c_0$, and Liouville proof all verify cleanly. |
| **C2** (`all-prime-polynomials.md` §7) | General protected-pole theorems (C2a, C2b, C2c) | **REVISE (one Major statement error in C2b; C2a/C2c accept with minor polish)** | C2a and C2c are sound. In **Theorem C2b**, algebraic independence and unrestricted joint uniform distribution are claimed under a fixed-$r$ period hypothesis (they require the period condition for *every* $r$, as correctly stated in C2a). |
| **Lean & Script** (`ProtectedPole.lean`, `phase20_normality.py`) | C1 kernel lemmas & exact controls | **ACCEPT (minor polish)** | `ProtectedPole.lean` is `sorry`-free and matches Lemma 1's $F_l(U,V)$ and gap conditions exactly. `scripts/phase20_normality.py` passes all checks (`exit 0`), with minor docstring/grid discrepancies noted below. |

---

## Part 1: Track C3 Audit (`notes/phase20/cubic-power-schedule.md`)

### Overall Technical Assessment

Every potential fatal obstruction was tested ruthlessly from first principles, and **the theorem and proof architecture survive**:
- **Anchor count & $\kappa$-scaling:** Restricting anchors to $h_1 \ge 1$, $h_2 \ge \max(2h_1 + 1, \lceil(\log H)^2\rceil)$, $h_j \ge 2(h_1 + \dots + h_{j-1}) + 1$ ($j \ge 3$), $k = \sum h_i \le \kappa H$, and $y_i \le \theta = (2r)^{-1/d}$ leaves $\gg_r (\kappa H)^{r-1}$ dominant loss vectors (e.g., the box $h_j \in [\frac{\kappa H}{2 \cdot 6^{r-1}} 6^{j-1}, \frac{2\kappa H}{2 \cdot 6^{r-1}} 6^{j-1}]$). Since $p \ge 3$ and $\theta = (2r)^{-1/d} \ge (2r)^{-1/(r+1)} \ge 4^{-1/3} > 0.629$, we have $\theta p^{h_i} > 1.88$ for every $h_i \ge 1$, guaranteeing $\in [(\frac{2}{9})^{r-1} p^k, p^k]$ anchors per loss vector and $\asymp_{d,p,K'} |I| p^v$ centres per anchor, hence $\gg_{r,d,p,K'} \kappa^{r-1} |I| H^{r-1} p^H$ centres in $I$. Crucially, for each anchor $y$ of loss $k$, the main-term collision weight $2 \eta_0 \cdot \#\{\text{comp} : S \in I^+\} \ll \epsilon p^{-k} H^{1-r} (|I^+| H^{r-1} p^H + H^{r-2} p^H) = \epsilon (|I^+| + H^{-1}) p^v$ scales linearly with that anchor's own centre count $\asymp |I| p^v$, so the main-term constant $C'$ in $C'\epsilon \cdot \#\text{centres}(I)$ is **independent of both $\kappa$ and $I$**.
- **Nonzero separation $|B| \ge p^{-dg}$ does NOT kill Titchmarsh 5.13:** The proof avoids $p^{-dg}$ blow-up cleanly via the dichotomy at $p^{-cH}$. For $0 < |B| < p^{-cH}$, Titchmarsh 5.13 is never invoked; instead $|B| \ge p^{-dg}$ forces $g > cH/d > \kappa H$, forcing $g$ into $w$, where $|w_m - \tilde w_m| \le (2 p^{-cH})^{1/d}$ leaves $\le 2^{1/d} p^{g - cH/d} + 1 < 3 p^{g - cH/d}$ lattice points (the $+1$ is absorbed because $g > cH/d \implies p^{g - cH/d} > 1$). For $|B| \ge p^{-cH}$, only the small constant $c$ enters $\gamma = c + 2\kappa(d(q-1) - q)$.
- **Derivative formula, $\Phi_q$ nonvanishing, and $D_{\min}/C$ bounds:** The recurrence for $\Phi_q(X, B)$, its homogeneity of degree $q - 2$, and its leading coefficient $(-1)^q (d+1)\cdots(d+q-2) \ne 0$ are exact. Neither $\Phi_q$ nor $\Phi_{q+1}$ can vanish identically. Factoring $\Phi_q(X, B) = L_q \prod_{m=1}^{q-2} (X - \zeta_m B)$, the set $\{x \ge 0 : |\Phi_q(x^d, B)| \le \eta^{d(q-2)}\}$ is covered by $\le q - 2$ intervals $\{|x^d - \zeta_m B| \le \eta^d\}$, each of $x$-diameter $\le (2\eta^d)^{1/d} = 2^{1/d}\eta$ **uniformly in $B$**. On colliding points, $S(w,x) \in I^+ \subset (1, p^d)$ and $B_y < 1/2$ force $x^d + B \in [1/4, p^d + 1]$ (for both $B > 0$ and $B < 0$) and $|B| \le r p^d$. Because $q \le r + 1 \le d$, $d - q \ge 0$, so BOTH the lower bound $D_{\min} \gg p^{-\gamma H}$ (with $\gamma = c + 2\kappa(d(q-1)-q)$) and the $B$-independent upper bound $|f_B^{(q)}| \le C$ hold (including at $q = d$).
- **Titchmarsh Theorem 5.13 & Erdős–Turán:** By induction from van der Corput's second-derivative test ($q = 2$, Graham–Kolesnik Theorem 2.2) via $(q-2)$ Weyl differencings, the bound
  $$\left|\sum_{m' \in P} e(g(m'))\right| \ll_q T \lambda^{\frac{1}{2K_q - 2}} + T^{1 - \frac{2}{K_q}} \lambda^{-\frac{1}{2K_q - 2}} \qquad (K_q = 2^{q-1})$$
  holds **unconditionally** for all $\lambda > 0$, all $T \ge 1$, and all subintervals $P$ of length $\le pT$ (the regimes $\lambda \ge 1$ and $T^{K_q - 1}\lambda \le 1$ are trivially dominated by the first and second terms respectively, and $1 - 2/K_q \ge 0$ allows replacing $|P|$ by $T$). With $\lambda = l D p^{H - k - qv'}$ and $L = \lceil p^k H^{r+1}\rceil$, the harmonic sums $\sum_{l=1}^L l^{-1 + 1/(2K_q - 2)} \asymp L^{1/(2K_q - 2)}$ (cancelling $p^{-k}$ from $p^v = p^{H-k}$) and $\sum_{l=1}^L l^{-1 - 1/(2K_q - 2)} = O_q(1)$ yield **exactly** the exponents $E_1$ and $E_2$ on lines 89–90.
- **Lemma 2 & Real-orbit transfer:** Lemma 2 (reverse Fatou + Lebesgue density) and the Section 1 transfer to real orbits ($O(N^{r/d})$ insertions for $d \ge r + 1$, uniform freezing at fixed precision $L$, lower degrees of depth $\le (r-1)sJ$, `normal_mul_nat_iff`) are sound.

However, the written proof contains **three Major findings** that must be fixed before publication, plus several Minor polish items.

---

### Major Findings (Needs Fix) — Track C3

#### C3-M1. Gap and false inequality in the $B = 0$ coincidence argument (lines 64 & 66)
1. **Unjustified deduction at line 64 ($B = 0, w = y$):** Line 64 asserts *"A collision forces $x = z$, so the competitor is the centre itself."* A collision only forces $|x^d - z^d| \le \delta_H$, hence $|x - z| \le \delta' = C_d \epsilon H^{1-r} p^{-H}$. To conclude $x = z$, one must invoke rational separation: since $v = H - k \le H$ and $v' \le H' \le H + \lfloor e_r/s \rfloor$, any $x \ne z$ satisfies
   $$|x - z| = \left|\frac{m'}{p^{v'}} - \frac{m}{p^v}\right| \ge p^{-\max(v, v')} \ge p^{-H - \lfloor e_r/s \rfloor},$$
   which strictly exceeds $\delta' = C_d \epsilon H^{1-r} p^{-H}$ for all sufficiently large $H$ (critically using $H^{1-r} \to 0$ when $p \le r$ so $\lfloor e_r/s \rfloor \ge 1$).
2. **Missing link and literally false bound at line 66 ($B = 0, w \ne y$):** Line 66 asserts *"and the remaining $w$ has total loss at most $k_j = h_1 + \cdots + h_j$. If two coordinates of $w$ had loss at least $h_j$, the total would exceed $2 h_j > k_j$."*
   - **Gap:** The text never explains why the competitor's coarse loss $k' = H' - v'$ is bounded in terms of the anchor loss $k = H - v$. A priori $k'$ can be as large as $\frac{r-1}{r} H' \gg \kappa H \ge k$ (in which case a competitor $w$ could easily have two coordinates of loss $g > h_{r-1}$ whose $d$-th powers cancel mod $p^{d(g - h_{r-1})}$, e.g. for any odd $d$ and any prime $p$, or for $d = 4, p = 17$, or for $r = 4, d = 6, p = 3$). The **only** reason $k'$ is tied to $k$ is the $x = z$ deduction above: since $p \nmid m, m'$, $x = z$ forces $v' = v$, which forces
     $$k' = H' - v' = H' - v = k + (H' - H) \le k + \lfloor e_r / s \rfloor.$$
   - **False inequality when $p \le r$:** When $p \le r$ (including the note's headline case $C(2, 3, 1, 4)$ where $p = 3, r = 3, s = 1, e_3 = 1$), competitors of level $H' = H + \lfloor e_r/s \rfloor > H$ are relevant, so $k'_j = k_j + (H' - H)$ **can exceed $k_j$** by up to $\lfloor e_r / s \rfloor$!
   - **Fix:** State the $x = z \implies v' = v \implies k' = k + (H' - H) \le k + \lfloor e_r / s \rfloor$ deduction explicitly for all $B = 0$ rows (for $H \ge H_0(p, r, d, s)$). Then in the peeling step for $j = r-1, \dots, 2$, dominance $h_j \ge 2 k_{j-1} + 1$ gives $k_j = k_{j-1} + h_j \le \frac{3}{2} h_j - \frac{1}{2}$, hence
     $$k'_j = k_j + (H' - H) \le \frac{3}{2} h_j - \frac{1}{2} + \lfloor e_r / s \rfloor < 2 h_j$$
     for all sufficiently large $H$, because $h_j \ge h_2 \ge \lceil(\log H)^2\rceil \to \infty$ while $\lfloor e_r/s \rfloor$ is fixed! Thus $w$ still cannot have two coordinates of loss $\ge h_j$; and since $v_p(\sum_{i \le j} y_i^d) = -d h_j$, $w$ cannot have a unique coordinate of loss $> h_j$ nor all coordinates of loss $< h_j$, so it must have a unique coordinate $c/p^{h_j}$ of loss $h_j$. The lower coordinates of $w$ then have total loss $k'_{j-1} \le k_{j-1} + \lfloor e_r/s \rfloor$, adding only a constant factor $p^{\lfloor e_r/s \rfloor} = O_{p,r}(1)$ to the lower-coordinate count. Finally, make the peeled-coordinate factor $p^{k - k_j}$ explicit so the exponent algebra $(k - k_j) + 2 k_{j-1} + \epsilon' d h_j = k - h_j + k_{j-1} + \epsilon' d h_j \le k - (\frac{1}{2} - \epsilon' d) h_j$ is transparent, and note that at $j = 1$ the equation $y_1^d = w_1^d$ forces $w_1 = y_1$ (and $H' = H$).

#### C3-M2. Incomplete proof of exponent coverage for $\beta < 1$, arbitrary $r \ge 3$, and $H' > H$ (lines 95–101)
Line 98 checks $E_1 < H$ and $E_2 < H$ only at $\beta = 1$, asserts without proof that *"$q = r + 1$ also works for $\alpha < 1/r$"*, verifies window overlap only by listing the first three windows $(1/4, 2), (1/5, 0.8), (1/6, 0.47)$, and cites the finite script for $\sigma_4, \sigma_5, \sigma_6$. Because Theorem C3 is claimed for **every** $r \ge 1$ and $d \ge r + 1$ and must cover **all** competitor levels $0 \le H' \le H + \lfloor e_r/s \rfloor$ (including $\beta < 1$ and $v' = 0$), an analytic proof for general $r$ and all $(\alpha, \beta)$ is required.

- **Fix (self-contained 6-line proof giving the exact $\sigma_r$ for all $r \ge 3$):**
  At $\kappa = \gamma = 0$, $E_1/H = \beta + \frac{1 - q\alpha}{2K_q - 2}$ and $E_2/H = \beta + \alpha\left(\frac{q}{2K_q - 2} - \frac{2}{K_q}\right) - \frac{1}{2K_q - 2}$.
  1. *All-$q$ window overlap at $\beta = 1$:* For every $q \ge 4$, the windows $\big(\frac{1}{q}, \frac{1}{q - 4 + 4/K_q}\big)$ and $\big(\frac{1}{q+1}, \frac{1}{q - 3 + 4/K_{q+1}}\big)$ overlap because $q - 3 + 4/K_{q+1} \le q - 3 + 1/4 < q$, with crossover point $\alpha_* \approx \frac{1}{q-1}$ giving margin $> \frac{1}{(q-1)(2K_q - 2)}$ (and $\ge \frac{1}{28}$ at $\alpha = 1, q = 4$).
  2. *Regime $\alpha \ge 1/r, 0 \le \beta \le 1$:* Both $E_1/H$ and $E_2/H$ have slope $+1$ in $\beta$, so decreasing $\beta$ from $1$ only increases both margins.
  3. *Regime $0 \le \alpha < 1/r, \beta \le r\alpha$ (including $\alpha = \beta = 0$):* Take $q = r + 1 \ge 4$. Substituting $\beta \le r\alpha$ yields
     $$\frac{E_1}{H} \le \frac{1}{2K_{r+1} - 2} + \alpha\left(r - \frac{r+1}{2K_{r+1}-2}\right), \qquad \frac{E_2}{H} \le \alpha\left(r + \frac{r - 3 + 4/K_{r+1}}{2K_{r+1}-2}\right) - \frac{1}{2K_{r+1}-2}.$$
     Both coefficients of $\alpha$ are positive for all $r \ge 3$, so both are maximized at $(\alpha, \beta) = (1/r, 1)$, giving the exact uniform margin
     $$\sigma_r = \frac{1}{r(2^{r+1} - 2)} > 0$$
     (with $1 - E_2/H = \frac{3 - 4/K_{r+1}}{r(2^{r+1}-2)} > \sigma_r$).
  4. *Perturbation & $H' > H$:* Since $c$ enters $E_2$ divided by $2K_q - 2 \ge 14$, taking $c < \sigma_r$ and $\kappa$ small enough (with $\kappa < \min(c/d, 1/(2r))$) keeps both perturbed exponents $\le (1 - \sigma_r/2)H$ for all $\beta \le 1$. The extra $H' - H \le \lfloor e_r/s \rfloor$ adds only a constant $O_{p,r}(1)$ to $E_1, E_2$, which is negligible against $(\sigma_r/2)H$.

#### C3-M3. Omitted steps in the exponential-sum and lattice-counting bounds (lines 86 & 105)
1. **Dropping $p \nmid m'$ for Titchmarsh 5.13 (line 86):** In the competitor set, $x = m'/p^{v'}$ requires $p \nmid m'$, whereas Titchmarsh Theorem 5.13 requires a sum over **consecutive** integers $m'$ in each monotonic dyadic piece. The proof should explicitly state that we drop $p \nmid m'$ in the $B \ne 0$ upper bound (which only increases the collision count and multiplies the main term $N_{\text{row}}$ by at most $p/(p-1)$, already compatible with the lattice-counting bound in line 105).
2. **Short pieces, $T = 1$, harmonic summation, and $L^{-1}$ term (lines 86–93):** State explicitly: (i) why Titchmarsh 5.13 with ambient $T = p^{v'}$ holds even on short pieces ($N_P \le pT$) and at $v' = 0$ ($T = 1$); (ii) how summing $\frac{1}{l}$ over $1 \le l \le L = \lceil p^k H^{r+1} \rceil$ produces $L^{1/(2K_q - 2)} \asymp p^{k/(2K_q - 2)} H^{(r+1)/(2K_q - 2)}$ in the first term (cancelling $p^{-k}$ from $p^v = p^{H-k}$) and $O_q(1)$ in the second; and (iii) that the $O(qH)$ pieces of a row are disjoint, so $\sum_{\text{pieces}} N_{\text{piece}}/L \le N_{\text{row}}/L$, which summed over all rows gives $O(H^{r-3} p^H) = o(H^{r-1} p^H)$.
3. **Proof of the $r$-dimensional lattice-counting error (line 105):** Line 105 asserts *"Lattice counting on each loss vector costs $O(p^{H' - \min h'})$, which sums to $O(H^{r-2} p^H)$"* without proof. Because $h'_j = 0$ is permitted (where $p^{H' - \min h'} = p^{H'}$), a reader will legitimately ask why $O(p^{H'})$ doesn't wreck the bound.
   - **Fix (4-line proof):** For $R_u = \{x \in (0, p)^r : \sum x_i^d \le u\}$ ($u \le p^d$) and grid $\Lambda = \prod_{j=1}^r p^{-h'_j}\mathbb Z_{>0}$, associating to each $x \in R_u \cap \Lambda$ the interior-disjoint lower box $\prod_j [x_j - p^{-h'_j}, x_j] \subset \overline{R_u}$ gives $\#(R_u \cap \Lambda) \le p^{H'} \operatorname{Vol}(R_u)$ directly; covering $R_u$ by upper boxes $\prod_j [x_j, x_j + p^{-h'_j}]$ based at $\Lambda_{\ge 0} \cap \overline{R_u}$ and bounding boundary points with some $x_j = 0$ gives $\#(R_u \cap \Lambda) \ge p^{H'} \operatorname{Vol}(R_u) - (p+1)^{r-1} \sum_{j=1}^r p^{H' - h'_j}$. Subtracting for the two endpoints of $I^+$ gives slab count $\le p^{H'}(\operatorname{Vol}(R_{u_2}) - \operatorname{Vol}(R_{u_1})) + (p+1)^{r-1} \sum_j p^{H' - h'_j}$. Summing $\sum_j p^{H' - h'_j}$ over all $\binom{H' + r - 1}{r - 1}$ loss vectors yields $r \sum_{m=0}^{H'} p^m \binom{m + r - 2}{r - 2} = O_{r,p}(H^{r-2} p^{H'})$.

---

### Minor Findings (Polish) — Track C3

- **C3-m1 (Domain of $r$ in Section 4):** State explicitly at the beginning of Section 4 that we assume $r \ge 3$ (the cases $r = 1, 2$ are already handled by Phases 18–19), since the anchor definition writes $h_2$.
- **C3-m2 (Distinctness of centres & disjointness of $G_H$, lines 39 & 56):** Explicitly note that $\kappa < 1/2$ ensures $v = H - k > k \ge h_{r-1}$, so $1 \le h_1 < \dots < h_{r-1} < v$. Consequently, no two distinct centres $(y, z)$ are permutations of each other; any two distinct isolated centres are relevant competitors for each other and thus separated by $> \delta_H$, making the radius-$\delta_H/2$ intervals in $G_H$ pairwise disjoint.
- **C3-m3 (Level cutoff in Section 1, line 21):** *"Only tuples of level at most $L/s$ affect $M_r \bmod p^L$"* is slightly loose (strictly, level $\le \lfloor(L-1)/s\rfloor$, since $sH = L$ already vanishes mod $p^L$).
- **C3-m4 (Row count wording, line 62):** *"there are at most $p^{k + H' - v' + 2r}$ rows"* holds for a *fixed* pair of loss tuples $(h, h')$; summing over all pairs of loss tuples introduces the $H^{O(r)}$ factor (already included in line 86, but missing from the displayed bound on line 68 for $0 < |B| < p^{-cH}$ and line 84 for removed points).
- **C3-m5 (Parameter inequality in line 84):** The bound $O(q p^{k + H' - v'}) = O(p^{H - \kappa H})$ uses $k + H' - v' \le (\kappa + 1 - 1/r) H + O(1) \le (1 - \kappa) H + O(1)$, which requires $\kappa < 1/(2r)$ (satisfied since $\kappa < c/d < \sigma_r/d$, but should be stated explicitly). Also state explicitly that $x^d + B \in [1/4, p^d + 1]$ on colliding points (for both signs of $B$).
- **C3-m6 (Consistency with `scripts/phase20_normality.py`, lines 101 & 571):** Line 101 of the note uses $q \in \{4, \dots, r + 1\}$, while `check_c3_exponents()` in `scripts/phase20_normality.py` scans `q in range(3, r + 2)` and prints `derivative orders 3..{r+1}`. Both give the same $\sigma_r$, but text and script should match. Also, in `check_c3_exponents()`, `alpha = Fraction(a, 1200)` misses $\alpha = 1/7$ for $r = 7$, reporting `0.00058` instead of the exact minimum $\sigma_7 = 1/1778 \approx 0.0005624$.

---

## Part 2: Track C1 & C2 Audit (`notes/phase20/all-prime-polynomials.md`)

### Audit of Track C1 (§§1–6)

Every step of Theorem C1 was checked line by line and is **sound**:
- **Window rule (§1):** For $n \in [n_k, n_{k+1}) \setminus \bigcup_{i=1}^r [i n_k, i n_k + r n_{k-1}]$ (with $k$ large enough that $r n_{k-1} < n_k$), $l = \min(r, \lfloor n/n_k \rfloor) \in \{1, \dots, r\}$ characterizes the exact present tuples, giving $b^{-n} R_n = F_l(U_{k-1}, V_k)$ with zero insertions outside the windows. Cumulative discarded mass through any cutoff $N$ in shell $K$ (including cutoffs inside a window) is $\le 2 r^2 n_{K-1} + r K + O_r(1)$, hence $O_r(2^{-3K^2 + 3K} + K/N)$ relative to $N \ge n_K$.
- **Pole dominance (§2, Lemma 1):** The identity $D(r, l) - D(d, i) = (r - d)e' + (l - i)(e - e') \ge \min(e', e - e')$ covers all competitors ($d < r$ with $i = l \le d$, $d < l$, and $d = r$ with $i < l$). Kummer's carry theorem confirms $v_p\binom{r}{l} \le \lfloor \log_p r \rfloor \le \log_p r$, so $v_p(q_n) = (r-l)(k-1)^2 + lk^2 - v_p(A) - v_p\binom{r}{l} \ge r(k-1)^2 + 2k - 1 - v_p(A) - \log_p r$ for $k \ge k_1(P)$.
- **Support, grid loss, and rational clearing (§3):** $q_n \mid p^{rk^2} \prod_{j \le k} \ell_j^r$ with $(q_n, b) = 1$, $\log q_n = O_P(k^2) = O_P((\log N)^{2/3})$, and $w_n \le a + \max_{j \le k} v_p(\ell_j - 1) = O(\log k)$ (with $\ell = 2$ contributing $0$ when $b$ is odd). Rational clearing $y = b^c P(W) = (b^c/M_b) P_1(W)/M'$ preserves the exact shifted-prefix structure with $(b^c/M_b) P_1 \in \mathbb Z[x]$, adds $v_p(M')$ to the $p$-depth, increases grid loss by at most $\max_{\ell \mid M'} v_p(\ell - 1)$, and satisfies $D_N(P(W)) \le D_{N-c}(y) + c/N$.
- **Explicit discrepancy rate $c_0$ (§4):** With $K = \lfloor (\log_2 N)^{1/3} \rfloor = (\log N / \log 2)^{1/3} + O(1)$, the window/early-shell term is $O_r(2^{-3K^2 + 3K}) = \exp(-3(\log 2)^{1/3}(\log N)^{2/3} + O((\log N)^{1/3}))$, the shell-$(K-1)$ mesh term is $p^{-r(K-2)^2 + O_P(\log K)} = \exp(-\frac{r \log p}{(\log 2)^{2/3}}(\log N)^{2/3} + O_P((\log N)^{1/3}))$, and the buffer, tail, and residual-period terms are exponentially smaller ($\ll \exp(-\frac{1}{2} \log N)$). This confirms $D_N(P(W); b) \ll_{P,c} \exp(-c(\log N)^{2/3})$ for every $c < c_0 = \min\big(3(\log 2)^{1/3}, \frac{r \log p}{(\log 2)^{2/3}}\big)$.
- **Liouville, transcendence, joint UD (§5):** $0 < U_k < W < 1$, $|P(W) - P(U_k)| \le \max_{[0,1]} |P'| \cdot 2 b^{-n_{k+1}}$, $\operatorname{den}(P(U_k)) \mid M D_k^r$ with $\log D_k = n_k \log b + O(k^2)$, and normality forces irrationality ($P(W) \ne P(U_k)$). Since $n_{k+1}/n_k \to \infty$, $P(W)$ is Liouville, $W$ is transcendental, and Weyl's criterion gives joint uniform distribution of $(W, \dots, W^r)$.

### Major Finding (Needs Fix) — Track C2

#### C2-M1. Unqualified algebraic independence and joint UD under a fixed-$r$ hypothesis in Theorem C2b (line 157)
Theorem C2b assumes $k(p^{\max_a e_{a,k}} \Lambda_k)^r = o(n_k)$ for a **fixed** $r$, yet its statement concludes unconditionally:
> *"The $X_a$ are algebraically independent, and distinct monomials have jointly uniformly distributed shifts."*

Under a fixed-$r$ period hypothesis, one only rules out polynomial relations of total degree $\le r$, and only obtains joint uniform distribution for distinct **nonconstant** monomials of total degree $\le r$. Full algebraic independence and unrestricted joint uniform distribution require the period hypothesis to hold for **every** $r \ge 1$ (e.g., $\log(p^{\max_a e_{a,k}} \Lambda_k) = o(\log n_k)$), exactly as Theorem C2a carefully specifies at line 147.
- **Fix:** Restrict the fixed-$r$ conclusion to "no nonzero polynomial relation of degree $\le r$, and distinct nonconstant monomials of total degree $\le r$ have jointly uniformly distributed shifts," and add the explicit quantifier "If $\log(p^{\max_a e_{a,k}} \Lambda_k) = o(\log n_k)$ (so the period hypothesis holds for every $r$), then $X_1, \dots, X_m$ are algebraically independent and any finite list of distinct nonconstant monomials has jointly uniformly distributed shifts." (The pole-dominance proof of C2b itself is completely valid.)

### Audit of C2a & C2c — Verified

- **Theorem C2a (§7a):** All four hypotheses (S), (D), (G), (P$_r$) and all five terms of the displayed discrepancy bound (lines 143–144) check out. In particular, (D) makes $e_k$ eventually strictly increasing so $\max_{k \le K} p^{re_k} \ll p^{re_K}$, (S) implies $K = O(\log N)$ so $K \log(2N)/N \to 0$ and the tail bound $O_P((\log N)^r b^{-H})$ works with $H = \lceil(r+1)\log_b(2N)\rceil$, and (P$_1$) yields $\log D_k = n_k \log b + o(n_k)$ for the Liouville argument.
- **Theorem C2c (§7c):** The CRT moduli $p_j \operatorname{rad}(m_{j,k})$ and $p_i^k$ ($i \ne j$) are pairwise coprime; since $A_{j,k} \equiv 1 \pmod{p_j}$ ($p_j \ge 3$), the least positive representative satisfies the strict inequality $0 < A_{j,k} < p_j \operatorname{rad}(m_{j,k}) \prod_{i \ne j} p_i^k \le p_j^{Ck} m_{j,k} \le p_j^{E_k} m_{j,k}$ (assuming $E'_k \ge 0$, see C2-m3 below), giving weight in $(0, 1)$, reduced denominator exactly $p_j^{E_k} m_{j,k}$, and $U_{j,k} \equiv \theta_{ij} \pmod{p_i^k}$ ($v_{p_i}(V_{j,k}) \ge k - 1$ for $k \ge 2$). The OP-17 leading-term argument at $p_i$ preserves depth $q E_{k-1} + t \Delta_k - g - v_{p_i}\binom{q}{t} \ge E_k - O_P(1)$, and other protected primes $p_{i'}^{E}$ contribute only the fixed constant $v_{p_i}(\operatorname{ord}_{p_{i'}} b)$ to the grid loss. The Pitfall warning on OP-17's $E_k = Ck + \lfloor \log_2 n_k \rfloor$ is accurate.

### Minor Findings (Polish) — Tracks C1 & C2

- **C1-m1 (Intermediate inequality in tail bound, lines 95 & 98):** Line 95 bounds the number of ordered $j$-tuples at position $s$ by $(1 + (\log_2 s)^{1/3})^j$, whereas line 98 writes $(2 + \log_2(N+u))^{r/3}$. Strictly speaking $(1 + x^{1/3})^r > (2 + x)^{r/3}$ for large $x$. Since $1 \le k_i \le (\log_2 s)^{1/3}$, the true bound is $(\log_2 s)^{j/3} \le (2 + \log_2(N+u))^{r/3}$ without the "$1 +$"; simply drop the "$1 +$" in line 95 so the chain of inequalities is literally valid.
- **C1-m2 (Window range & run count, lines 26 & 40):** In line 26, note $(r + 1)n_k \le n_{k+1}$ (in addition to $r n_{k-1} < n_k$) so all $r$ windows $\mathcal W_{k, i}$ stay inside $[n_k, n_{k+1})$. In line 40, the retained part of shell $k$ actually consists of at most $r$ runs (not $r + 1$), since $\mathcal W_{k, 1}$ begins at $n_k$.
- **C2-m1 (Positivity of $e_{a,k}$ in C2b, line 155):** Explicitly require $\gamma_a f_1 \ge 1$ (or $e_{a,k} = \max(1, \lfloor \gamma_a f_k \rfloor)$) so $e_{a,k} \ge 1$ holds from $k = 1$, matching the integrality conditions of C2a.
- **C2-m2 (Nonnegativity of $E'_k$ in C2c, line 165):** Specify $E'_k \ge 0$ (nonnegative nondecreasing) so that $E_k = Ck + E'_k \ge Ck$ holds for every $k \ge 1$ in the weight-size check on line 172.
- **C2-m3 (Slightly stronger hypothesis in C2c, line 174):** Because $q \ge 1$ and $t = \min(q, l) \ge 1$ on retained shifts, the winning pole depth satisfies $q E_{k-1} + t \Delta_k \ge E_k$, so $E_k - \lambda_k^{(i)} \to \infty$ already suffices (the stated $E_{k-1} - \lambda_k^{(i)} \to \infty$ is harmlessly stronger).

---

## Part 3: Audit of `NormalityChecker/ProtectedPole.lean` & `scripts/phase20_normality.py`

### `NormalityChecker/ProtectedPole.lean`

- **Soundness:** All 538 lines were read in full; there are zero `sorry`s, zero custom axioms, and every proof step is clean elementary number theory using Mathlib's `Nat.factorization` and `Rat`. (Note: `lake` is not on `PATH` in this review environment, so compilation was audited by full manual inspection rather than a fresh `lake build` invocation.)
- **Correspondence with C1 (`all-prime-polynomials.md`):**
  - `truncatedPoly` (line 336) matches $F_l(U, V)$ (line 37 of `all-prime-polynomials.md`) identically.
  - `truncated_poly_pole_dvd_den` (lines 347–536) matches Lemma 1's hypotheses (`1 ≤ l ≤ r`, `g < e₁`, `g < e₂ - e₁`, where `g = (a_r.natAbs * Nat.choose r l).factorization p`) and proves `p ^ (l * e₂ + (r - l) * e₁ - g) ∣ (truncatedPoly a r l U V).den`.
  - `shifted_prefix_protected_prime_pow_dvd_den` (lines 245–330) proves both lower and upper divisibility (`p^(e k) ∣ den ∧ ¬ p^(e k + 1) ∣ den`) for $W$'s shifted prefixes.
- **Minor observations:**
  1. **Docstring scope of `shifted_prefix_aux_prime_dvd_den` (lines 12–17):** The theorem proves `ℓ k ∣ (b^N * U_k).den` for the *newest* prime `ℓ k` at truncation `k`. To deduce that *every* earlier `ℓ i` (`1 ≤ i ≤ k`) divides `(b^N * U_k).den` simultaneously (supporting the docstring claim that denominators *"eventually contain every prime coprime to `b`"*), one needs `ℓ i ∣ (b^N * U_k).den` for arbitrary `i ∈ Icc 1 k` (identical proof, assuming pairwise distinctness `∀ j ∈ Icc 1 k, j ≠ i → ¬ ℓ i ∣ ℓ j`).
  2. **Comment in `all-prime-polynomials.md` line 213:** The note remarks that *"The exact-valuation statement above is the complement needed for the surviving-grid exponent."* In fact, because the surviving-grid size $G = p^{\max(0, e - w)}$ is nondecreasing in $e = v_p(q_n)$, the divisibility lower bound `p^(D - g) ∣ (truncatedPoly ...).den` already proved in `truncated_poly_pole_dvd_den` **is sufficient** for the surviving-grid lower bound (while the upper bound on $q_n$ comes from `q_n ∣ p^(r k^2) ∏ ℓ_j^r`). Adding `¬ p^(D - g + 1) ∣ den` to `truncated_poly_pole_dvd_den` would also be ~5 lines if exact equality is desired.

### `scripts/phase20_normality.py`

- **Execution:** Ran `python -B scripts/phase20_normality.py`; exited with code `0`, all assertions passed.
- **Minor discrepancies:**
  1. **`check_c1_bruteforce` (lines 197–201):** The docstring states *"Full-orbit grid structure for actual small prefixes of `W` and `3W^2 - W/2 + 1`"*, but all four test tuples on lines 200–201 use `P = [0, 1]` ($W$ itself); none tests `3W^2 - W/2 + 1`.
  2. **`check_c2_two_primes` (lines 335–336):** `Qfac[other] = val(q, other)` assumes `val(q, other) >= 1` (if a polynomial depended on only one variable, `val(q, other) == 0` would pass `f = 0` into `prime_power_order`). Safe for the current polynomial $X_1^2 X_2 - 7 X_2$, but worth guarding with `if val(q, other):`.
  3. **`check_c3_exponents` (lines 563–574):** Scans `q in range(3, r + 2)` rather than `range(4, r + 2)` (matching `cubic-power-schedule.md` line 101), and the grid denominator `1200` misses $\alpha = 1/7$ at $r = 7$ (reporting `0.00058` instead of exact $\sigma_7 = 1/1778 \approx 0.0005624$). Changing `1200` to `840` or `1680` (divisible by $3, 4, 5, 6, 7, 8$) hits every exact vertex $\alpha = 1/r$.
