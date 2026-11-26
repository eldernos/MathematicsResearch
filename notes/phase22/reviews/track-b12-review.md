# Independent Referee Review: Phase 22 Track B (B1–B2)

- **Audited note:** `notes/phase22/radix-thresholds-and-class-groups.md` (449 lines, read in full)
- **Audited script:** `scripts/phase22_radix_classgroups.py` (1,001 lines, read in full and executed)
- **Cross-checked context:** `notes/phase21/radix-lambert.md`, `notes/phase21/euler-square-and-forms.md`
- **Review notice:** This is an automated cross-model mathematical referee audit and **not** independent human peer review.

---

## Executive Verdicts

| Track | Verdict | Critical | Major | Minor |
|---|---|---:|---:|---:|
| **B1** (Even composite radices, run packing, run sandwich, isolation scale) | **Accept with minor revisions** | 0 | 0 | 3 |
| **B2** (General class groups, order-4 annihilation, Strassmann non-cancellation, unconditional $(V_q)$) | **Minor-to-moderate revision required (1 Major)** | 0 | 1 | 6 |

**Overall assessment.** Every headline result (Theorems B1, B1′, B2, B2′) is mathematically sound and survives hostile checking. The two novel engines of this note—the 2-adic run barrier + sharp run-packing functional $g_\beta$ in Track B1, and order-4 annihilation + $p$-adic Strassmann non-cancellation in Track B2—work as claimed, including for $s \ge 2$ radices (such as $b = 12$), for $\ell = 2$ (where $\exp_2$ converges on $4\mathcal O$), and for ramified odd primes $q \mid |G_{\rm odd}|$.

One **Major** proof gap occurs in **Proposition 2.10** (lines 346–358): the proof selects the random dominant kernel $K^*$ first and then applies Lemma 2.7 to $m_{c^*}$ conditioned on the remaining coordinates, overlooking that the event $\{K^* = K\}$ can depend on $m_{c^*}$ (e.g., in $\mathbb Z/3 \times \mathbb Z/3$ or $\mathbb Z/15$) and inverting the quantifier order between $H$ and $M$; the same proof also double-counts $p \le P_0$ in $\mathrm{val}_K$ and omits the $d = 1$ factor $\epsilon_1 = \frac{1}{2}$. This gap is cleanly repairable by union-bounding over the finitely many candidate kernels $K \in \mathcal K(\pi)$ *before* choosing $M$ and selecting the minimizer. Among the **Minor** findings, line 421 contains an outright false commentary claim about order-4 classes in $2$-groups that is contradicted by the $\Delta = -95$ ($\mathbb Z/8$) row eight lines above it.

---

## 1. Script Execution and Numerical Audit

Command executed in the worktree root:

```sh
python -B scripts/phase22_radix_classgroups.py
```

- **Exit code:** `0`
- **Runtime:** `8.7 s` internal (`9.06 s` wall clock), matching the note's "about 10 s" (lines 61, 429).
- **Exact assertions:** `3,104,830` checks passed, matching "about $3.1 \cdot 10^6$ checks" (lines 61, 429).
- **Numerical agreement across all tables and inline figures:**
  - Thresholds $\delta^* = 0.590616\ldots$ and $\delta^*_b$ for $b = 6, 10, 12$ (`0.701754`, `0.673632`, `0.765433`, line 26): exact match to 6 decimal places.
  - Unconditional constant table (§1.4, lines 144–151, all 6 rows × 8 columns): exact match to all 4 displayed decimal places.
  - Mean displacements $\mathbb E[V_b]$ for $L_{\chi_4}(b)$ at $N = 2^{16}$ (line 155: `1.41`, `0.06`, `0.002`, `0.05`, `0.001`, `0.006`): exact rounded match to B1.1 output (`1.4083`, `0.0597`, `0.0022`, `0.0468`, `0.0012`, `0.0057`).
  - Order-4 annihilation counts for 2-groups at $N = 5 \cdot 10^4$ (line 287: `12,538/17,219` for $-39$, `3,158/17,575` for $-95$, `13,865/19,988` for $-260$): exact match to B2.3 output.
  - Excess histograms at $N = 3 \cdot 10^4$ (line 360: `-47`, `-87`, `-71`): exact match to B2.4 output.
  - Finite-height form table (§2.6, lines 408–419, all 10 rows × 4 measured columns): exact match to B2.3 output.
  - Euler products $1 - \pi_{J,\ell}$ and radix-$2^k$ constants (lines 47–55): exact match to B2.5 output at $p \le 2 \cdot 10^5$. Independent verification to $p \le 10^6$ confirms the truncation tail is $< 10^{-7}$ for $\ell = 3$ (`-23`: `0.78363752` vs `0.78363744`, `-87`: `0.82728339` vs `0.82728331`) and $< 10^{-16}$ for $\ell = 5, 7$ (`-47`: `0.95938974`, `-71`: `0.99116750`), confirming line 55's tail claim ($< 10^{-6}$).
- **Scope hygiene:** Zero occurrences of `"the brief"`, `"prompt"`, `"TODO"`, or process-artifact phrasing in either file. All relative Markdown links resolve to existing files/anchors in `notes/phase21/` and `scripts/`.

---

## 2. Detailed Mathematical Audit

### 2.1 Track B1 (Even Composite Radices & Density Thresholds)

- **Proposition 1.1 (lines 73–79):** Verified. In Brun's pair sieve for $n, n+h \in \mathcal A$ with $z_0 = (\log N)^2$ and $1 \le h \le \sqrt N$, primes $q \mid h$ with $q > z_0$ number at most $\frac{\log N}{4\log\log N}$ and alter the Mertens product by $(1 - 2/(\log N)^2)^{-O(\log N/\log\log N)} = 1 + o(1)$, giving uniformity in $h$ and the claimed $o(S(N))$ bound for $H \le (\log N)^\kappa / (LL)^{2\kappa+1}$.
- **Lemma 1.2 (lines 85–97):** Verified for all $s \ge 1$ and odd $b' > 1$ (including $s \ge 2$ such as $b = 12$ and $b = 24$). Since $b \nmid U$ forces $b^J \nmid U$ for $J \ge 1$, both $r = U \bmod b^J$ and $b^J - r$ are positive multiples of $2^{sJ}$ whenever $sJ \le v_2(U)$. For $(b-1)$-runs, $b^J - r = b^{s_0} - (U \bmod b^{s_0})$ equals $1 < 2^{sJ}$ when $s_0 = 0$ (forcing $s_0 \ge 1$) and is strictly $< b^{s_0}$ when $s_0 \ge 1$ (since $b^{s_0} \nmid U$). Taking logarithms gives $\ell < s_0 / (\beta_b - 1)$ with $\beta_b - 1 = s\log 2 / \log b'$. (See Minor B1.1 for the implicit $\ell \ge 1$ assumption.)
- **Lemma 1.3 (lines 102–118):** Verified. Scaling sets $\kappa_0 = 1$; $g_\beta(y) = (y/\beta - 1)_+ + g_\beta(\gamma y)$ is nondecreasing and $1$-Lipschitz ($0 \le g'_\beta \le \sum_{i\ge 0} \gamma^i/\beta = 1$). Inducting on the rightmost interval $[s, s+\ell)$ gives $\ell < x/\beta$ and monotonicity of $\ell - 1 + g_\beta(x - \ell)$ yields the bound. The geometric family with tops $x_i = \gamma^i x$ and lengths $(1-\epsilon)x_i/\beta$ has $s_i = x_i(\gamma + \epsilon/\beta) > x_{i+1}$ (strictly disjoint) and $\ell_i < s_i/(\beta - 1)$, establishing sharpness.
- **Proof of Theorem B1 (§1.4, lines 120–141):** Verified. In condition (G7), the $-sV$ terms cancel cleanly between $v_2(U) \ge \omega_{\mathcal S,1} - sV$ and $su \le \omega_{\mathcal S,1} \frac{s\log 2}{\log b} + s(\log_b M + 1) - sV$, leaving $\omega_{\mathcal S,1} \frac{\log b'}{\log b} \ge s(\log_b M + 1)$, which holds off $o(S)$ indices by tightness of $M$ and the Rankin lower tail. Thus *every* digit of $U$ lies inside the $2$-adic barrier zone $[0, v_2(U)/s)$ for good sources. Carry check in marking: $j \ge \lambda' + 1$ gives $b^{-j}/2 < \eta$, hence $\|U/b^j\| < 2\eta \le b^{-\lambda'}$ strictly, forcing the $\lambda'$ digits below $j$ to be all $0$ or all $b-1$ with zero carry ambiguity. (See Minor B1.2 for noting Lipschitz continuity of $g_\beta$ in (137).)
- **Theorem 1.4 & Corollary 1.5 (§1.5, lines 157–195):** Verified in all radices (including $b = 2$, where maximal runs of $0$s and $1$s are still disjoint). In the upper bound, $k_+ = \lceil\log_b(2/\varepsilon)\rceil$ gives $\|U/b^j\| \le b^{-k_+} \le \varepsilon/2$ and $|A|b^{-j} \le \frac12 b^{-k_+} \le \varepsilon/4$, so $\|x_{t-j}\| \le \frac34\varepsilon < \varepsilon$ strictly (even for $s_0 = 0, j = k_+$). Overlapping bad windows do not break the subtraction of $\sum_{n \in G} E_{k_+}(|U(n)|)$ because $|(\mathcal U_{\rm good} \cup \mathcal U_{\rm bad}) \setminus Z| \le |\mathcal U_{\rm good}| - |Z| + |\mathcal U_{\rm bad}|$ holds unconditionally when every shift in $Z \subseteq \mathcal U_{\rm good}$ is genuinely not far. (See Minor B1.2.)
- **Proposition 1.6 (§1.6, lines 197–218):** Verified up to a missing $O(1)$ constant factor $C_{\mathcal S}^{z-1}$ in (212) (Minor B1.3). The orthogonality bound $\sum_{h=1}^{D-1} \exp(-8\delta LL\|h/D\|^2) \ll D/\sqrt{LL}$ is exact (using $1 - \cos 2\pi t \ge 8t^2$ on $[0, 1/2]$), and $\mathrm{ord}_{b'^j}(2) \gg_b b'^j$ holds for every odd composite $b' > 1$ via prime-power lcm.
- **Proposition 1.7 (§1.7, lines 219–235):** Verified. For $b \ge 3$ and $d \ge 1$, both shifts $x_{t+d-j}$ ($1 \le j \le \min(d, \lambda')$) and $x_{t-j}$ ($1 \le j \le \lambda'$) stay strictly below $\frac{1}{2}$ (at $b = 3, j = 1, d = 1$, $x_{t-1} = \frac{4}{9} + o(1) < \frac{1}{2}$), lie in disjoint intervals between consecutive pairs, and give the exact constant $\frac{1+\min(\theta,1)}{2}$. The (W2) violation threshold $2 + 4/\kappa$ matches Theorem 1 with $B = 0, \omega = 0$.

### 2.2 Track B2 (Class Groups & Unconditional $(V_q)$ via Strassmann)

- **Lemma 2.1 (Order-4 annihilation, lines 252–265):** **Airtight.** Checked specifically against ramified primes, square factors, and non-principal genera:
  - Ramified primes have $[\mathfrak p]^2 = 1$, hence $[\mathfrak p] \in G_2$ and $\pi_{\rm o}([\mathfrak p]) = 1$; even without this, $[\mathfrak p]^e \mapsto [\bar e_p^e] \otimes [c_{\rm o}^e]$ factors cleanly in $\mathbb Z[E \times G_{\rm odd}]$.
  - Square and higher prime-power factors are killed automatically whenever any single split $p \| n$ has $\chi(\mathfrak p) = \pm i$, since $\chi : \mathbb Z[G] \to \mathbb C$ is a ring homomorphism and $\lambda_\chi(p) = \pm i \mp i = 0$.
  - Non-principal genera work identically: in $E = G_2 / G_2^2$, $\bar e_p^{2i-e} = \bar e_p^e$ holds for every $i$, so $\bar X_n = [\bar e_n] \otimes Y_n$ regardless of whether $\bar C_2$ is trivial or nontrivial.
- **Lemma 2.2 & Theorem 2.3 (lines 267–287):** Verified. For $\chi \in \mathcal X_4$, split primes with $\chi(\mathfrak p) = \pm i$ form a nonempty union of pairs $\{C, C^{-1}\}$ of Chebotarev density $\delta_\chi = 1/\operatorname{ord}\chi > 0$, so Shiu gives $O(S_\Delta(N)(\log N)^{-\delta_\chi})$. In Theorem 2.3, Cauchy–Schwarz with the Rankin moment at $s = 1/LL$ yields $\sum_{\operatorname{supp} r_Q} (\log_b r_Q)^2 \ll (LL)^2 \sum a^{1/LL} \ll S(LL)^2$ (see Minor B2.6).
- **Lemmas 2.4–2.6 (lines 291–320):** **Airtight.** Since $|G_{\rm odd}|$ is odd, $2$ is unramified in $\mathbb Q(\zeta_{|G_{\rm odd}|})$, so $v_{\mathfrak P}(\psi(Y_n))$ is independent of $\mathfrak P \mid 2$ and equals $m_{\ker\psi}(n) + \sum_{p^e\|n,\, e \ge 2,\, \psi(\mathfrak p)=1} v_2(e+1)$. For split $p^e \| n$ with $\psi(\mathfrak p) \ne 1$ and $o \nmid e+1$, both $1 - \zeta^{2(e+1)}$ and $1 - \zeta^2$ have odd norms, hence are $2$-adic units; for $e = 1$, $\zeta + \zeta^{-1} = \zeta^{-1}(1-\zeta^4)/(1-\zeta^2)$ is a global cyclotomic unit, hence a $q$-adic unit for every prime $q$ (including ramified odd $q \mid |G_{\rm odd}|$).
- **Lemma 2.7 (lines 322–324):** The external Selberg–Delange input for products of Hecke $L$-functions of class-group characters is standard and properly cited (Tenenbaum II.5), and the exponent formula $\alpha_1(z) = \frac{1}{2h}\sum_{c \in G} z_c$ correctly handles both ambiguous and non-ambiguous classes. Two minor precision points in the proof (Minor B2.4): `\asymp` should be `\ll` because $\Gamma(\alpha_1(z))^{-1} = 0$ when $\alpha_1(z) = 0$ (e.g., when $z$ is a nontrivial genus character), and odd $M$ should be handled by reducing from $\mathrm{lcm}(2, M)$.
- **Lemma 2.8 (Strassmann, lines 326–328):** **Core argument verified for both $\ell = 2$ and odd (including ramified) $\ell = q$.** Taking $\nu = \lfloor e/(\ell - 1)\rfloor + 1$ (so $\nu = 2$, i.e., $1 + 4\mathcal O$, for unramified extensions of $\mathbb Q_2$, and $\nu = e + 1$ for ramified extensions of $\mathbb Q_2$), we have $e v_\ell(n!) = e \frac{n - s_\ell(n)}{\ell - 1} \le e\frac{n-1}{\ell-1} < (n-1)\nu$ for all $n \ge 2$, so $\exp : \mathfrak m^\nu \leftrightarrow 1 + \mathfrak m^\nu : \log$ are inverse isometries. With $T = |(\mathcal O/\mathfrak m^\nu)^\times|$, $L_i = \log \beta_i^T \in \mathfrak m^\nu$ are pairwise distinct (since $\beta_i/\beta_j$ is not a root of unity), and $F_{A, j_0}(k) = \sum_i A_i \beta_i^{j_0} \exp(k L_i) = \sum_{n \ge 0} c_n k^n$ satisfies $v_{\mathfrak m}(c_n) \ge n(\nu - e/(\ell-1)) \to \infty$, so $F_{A, j_0} \in \mathcal O\langle k \rangle$ is a convergent Tate-algebra series on $\mathbb Z_\ell$. The Vandermonde determinant prevents $c_0 = \dots = c_{r-1} = 0$, Strassmann gives finitely many zeros in $\mathbb Z_\ell$, local constancy mod $\mathfrak m^H$ gives continuity of $\phi_H$, and Dini's theorem gives uniformity on compact $\mathcal C \subset (\mathcal O \setminus \{0\})^r$. (See Minor B2.2 for the domain phrasing of the Haar measure.)
- **Lemma 2.9 (lines 330–332):** **Airtight.** Reality restricts roots of unity to $\pm 1$, $\eta_c^2 = \eta_{c^2} + 2$ together with bijectivity of squaring on $G_{\rm odd}$ reduces the first claim to Dedekind linear independence of characters, and for the second claim $\zeta^2$ remains primitive of odd order $d$, so $\zeta^2 + \zeta^{-2}$ generates $\mathbb Q(\zeta_d)^+$.
- **Proposition 2.10 (lines 334–359):** **Contains Major Finding 1** (detailed in §3 below). Once repaired by union-bounding over all candidate kernels $K \in \mathcal K(\pi)$ prior to choosing $M$, the $2$-adic non-cancellation bound is completely rigorous: for each fixed $K$ with $d > 1$, the coefficients $A_\tau = \tau(\psi^*(\eta_{C_{\rm o}}) w_{\psi^*}(\pi) \prod_{c \notin K, c \ne c^*} \psi^*(\eta_c)^{m_c})$ stay in the compact set $\prod_\tau (\tau(\psi^*(\eta_{C_{\rm o}}) w_{\psi^*}(\pi)) \cdot \mathcal O^\times) \subset (\mathcal O \setminus \{0\})^r$ because every $\tau(\psi^*(\eta_c))$ ($c \notin K$) is a $2$-adic unit.
- **Proof of Theorem B2 (§2.4, lines 368–390):** Verified (conditional on repairing Proposition 2.10). The exact exponent algebra works cleanly: $[G_{\rm odd} : \ker\psi] = \operatorname{ord}(\psi)$, so $\min_{\psi \in \mathsf S(n)} \frac{|\ker\psi|}{2|G_{\rm odd}|} = \frac{1}{2 d(n)}$, giving $u(n)/\lambda_N = (1 - 1/d(n))\log 2 + o(1)$ in probability, supported in $[0, (1 - |G_{\rm odd}|^{-1})\log 2] \subset [0, 1)$. On $\operatorname{supp} r_Q$ (which agrees with $\operatorname{supp} a \cap \operatorname{genus}(Q)$ up to $o(S_Q)$ by Bernays), the $1/g$ genus factors cancel in the finite-prime local laws, giving independent geometric $e_p$ with $\mathbb P(e_p = e) = (1 - 1/p)p^{-e}$ independent of $C$, and truncation at $P_0$ has total-variation cost $O(1/P_0)$. In the first-moment bound, $a_C(n) \le a(n)$ holds pointwise, and $\frac{1}{2d(n)} \le \frac{1}{2}$ bounds the bad-set contribution to $\sum v_2(a_C)$ by $o(S_Q LL)$. The mixture form of Phase 21 Theorem 1 (Remark 5) then yields the exact constant.
- **Proof of Theorem B2′ (§2.5, lines 392–402):** **Core argument verified** for every odd prime $q$, including $q \mid |G_{\rm odd}|$ (where $L/\mathbb Q_q$ is ramified, $\psi(\eta_c) \in \{2\} \cup \mathbb Z[\zeta_{|G_{\rm odd}|}]^\times \subset \mathcal O_L^\times$ are still $q$-adic units, and any $q$-divisible prime-power factors $e \ge 2$ are fixed and nonzero inside $w_\psi(\pi)$). Moreover, because $1 + \mathfrak m_L^\nu$ contains no nontrivial roots of unity, avoiding $\prod_c \psi(\eta_c)^{T w_c} = \prod_c \psi'(\eta_c)^{T w_c}$ genuinely forces $\beta_\psi(\mathbf w)/\beta_{\psi'}(\mathbf w)$ not to be a root of unity, and pinning $w_{c_1} = 1$ makes $(\mathbf u, j) \mapsto (0, \mathbf u) + j\mathbf w$ unimodular on $(\mathbb Z/M\mathbb Z)^k$ for every $M \ge 1$. Three minor expositional gaps are recorded in Minor B2.3.

---

## 3. Findings (Classified by Severity)

### Critical Findings

None.

---

### Major Findings

#### [Major 1] Proposition 2.10: Conditioning on the random minimizer $K^*$ leaks into $m_{c^*}$, inverted $(H, M)$ quantifier order, and co-located $p \le P_0$ / $d = 1$ slips
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 346–358.
- **Problem:**
  1. **Conditioning leakage:** Line 348 restricts to the event that a unique minimizer $K^*$ beats every other kernel $K'$ by $> 2H$. Line 358 then picks $c^* \in G_{\rm odd}$ with $\psi^*(c^*)$ primitive, conditions on all $m_c$ ($c \ne c^*$), and invokes Lemma 2.7 to conclude that $m_{c^*} \bmod M_{H'}$ is asymptotically uniform given the rest. However, $K^*$ is a *random* kernel determined by the counts $(m_c)$, and $c^*$ can belong to another surviving kernel $K' \ne K^*$ (for example, in $G_{\rm odd} = \mathbb Z/3 \times \mathbb Z/3$ with $K^* = \langle(0,1)\rangle$ and $c^* = (1,0) \in K' = \langle(1,0)\rangle$, or in $G_{\rm odd} = \mathbb Z/15$ with $K^* = 3\mathbb Z/15$ and $c^* = 5 \in 5\mathbb Z/15$). Hence the event $\{K^* = K\}$ depends on $m_{c^*}$, so Lemma 2.7 cannot be applied *after* conditioning on $\{K^* = K\}$.
  2. **Quantifier order:** Line 348 requires choosing $M$ large compared to $H$ (so $(4H+1)/M \ll \varepsilon$), while line 358 chooses $H'$ (and hence $H$) *after* line 348.
  3. **Double-counting $p \le P_0$ (lines 346, 350):** Line 346 sets $\mathrm{val}_K = m_K + v_2(w_\psi)$, whereas $m_K$ (defined at line 303) already counts split $p \| n$ with $p \le P_0$ and $[\mathfrak p]_{\rm o} \in K$, and $w_\psi(\pi)$ (line 343) *also* includes all $p \le P_0$. Thus $v_2(\psi(Y_n)) = m_K^{(> P_0)} + v_2(w_\psi(\pi))$, and line 350 should factor out $2^{m_{K^*}^{(> P_0)}}$ rather than $2^{m_{K^*}}$.
  4. **Missing $\epsilon_1 = \frac{1}{2}$ and $d = 1$ edge case (lines 353, 358):** When $K^* = G_{\rm odd}$ ($d = 1$, $\psi^* = 1$, e.g., J-type integers where every nontrivial character is killed), line 353 inserts $\psi^*(\eta_{C_{\rm o}}) = 2$ and overcounts the singleton orbit $\{1\}$ by a factor of $2$ (unlike line 397, which properly includes $\epsilon_1 = \frac{1}{2}$), and line 358 has no $c^* \notin K^*$. (For $d = 1$, $F_{G_{\rm odd}} = w_1(\pi)$ is fixed and nonzero, so $v_2(F_{G_{\rm odd}}) = O_\pi(1)$ holds deterministically without Strassmann.)
- **Actionable fix:** Restructure lines 346–358 in the following order for each fixed $\pi \in \Pi$, letting $\mathcal K(\pi) = \{\ker\psi : \psi \in \mathsf S_\pi\}$ and defining $\mathrm{val}_K = m_K^{(> P_0)} + v_2(w_\psi(\pi))$:
  1. For each *fixed* $K \in \mathcal K(\pi)$, define $F_K$ by factoring $2^{m_K^{(> P_0)}}$ out of the $K$-orbit sum (with $\epsilon_1 = \frac{1}{2}$ for $K = G_{\rm odd}$, where $F_{G_{\rm odd}} = w_1(\pi)$ is constant and $H'_{G_{\rm odd}} := v_2(w_1(\pi)) + 1$). For $d = [G_{\rm odd} : K] > 1$, apply Lemma 2.7 and Lemma 2.8 to $F_K$ *on the full fixed-$(\pi, \text{genus})$ set* (without conditioning on $K$ being the minimizer) to obtain $H'_K$ such that $\mathbb P(v_2(F_K) \ge H'_K \mid \pi, \text{genus}) \le \frac{\varepsilon}{4|\mathcal K(\pi)|}$ for large $N$.
  2. Set $H'(\pi) = \max_{K \in \mathcal K(\pi)} H'_K$ and $H = \max_{\pi \in \Pi}\bigl(H'(\pi) + \max_{\psi \in \mathsf S_\pi} (v_2(w_\psi(\pi)) - m_{\ker\psi}^{(\le P_0)})\bigr)$.
  3. *Now* choose $M$ large relative to $H$ and $\varepsilon$ so that by Lemma 2.7, $\mathbb P(\exists K \ne K' \in \mathcal K(\pi) : |\mathrm{val}_K - \mathrm{val}_{K'}| \le 2H \mid \pi, \text{genus}) \le \varepsilon/4$.
  4. Apply a union bound over the tie event and the $|\mathcal K(\pi)|$ events $\{v_2(F_K) \ge H'_K\}$: on the complement (conditional probability $\ge 1 - \varepsilon/2$), the unique minimizer $K^*$ beats every other $K'$ by $> 2H$ *and* satisfies $v_2(F_{K^*}) < H'_{K^*}$, yielding $v_2(a_C(n)) \le \min_{\psi \in \mathsf S(n)} m_{\ker\psi}(n) + H$.

---

### Minor Findings

#### [Minor B1.1] Implicit positivity $\ell \ge 1$ in Lemma 1.2(2), $\ell_i > 0$ in Lemma 1.3, and $0^0 = 1$ / $\omega \ge 1$ for odd $b$
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 9, 26, 88, 102.
- **Issue:** In Lemma 1.2(2), if $\ell = 0$ and $s_0 = 0$ then the conclusion "$s_0 \ge 1$ and $2^{s(s_0+\ell)} < b^{s_0}$" fails vacuously (and $r = U \bmod b^0 = 0$ is not positive). In Lemma 1.3, the induction step implicitly assumes $\ell_i > 0$ (empty intervals can be discarded). On line 9, $g_1(y) = (y-1)_+$ uses the convention $0^0 = 1$ at $\gamma = 0$; on line 26, "reduces to the Phase 21 value $2\kappa$" applies specifically for $\omega \ge 1$ (in general $\kappa(1 + \omega - (\omega-1)_+) = \kappa(1 + \min(\omega, 1))$).
- **Fix:** State $\ell \ge 1$ in Lemma 1.2(2), $\ell_i > 0$ in Lemma 1.3, and clarify $0^0 = 1$ (or $g_1(y) = (y-1)_+$) and "for $\omega \ge 1$" on line 26.

#### [Minor B1.2] Unstated Lipschitz step in (137) and overlapping-bad-window set inequality in Theorem 1.4
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 137–140 and line 181.
- **Issue:**
  - In line 137, since $\lambda' - 1 < \lambda_N$, (G6) gives $u/(\lambda' - 1) \le (\omega + \varepsilon)(1 + o(1))$ rather than $\le \omega + \varepsilon$; replacing $g_\beta((\omega+\varepsilon)(1+o(1)))$ by $g_\beta(\omega+\varepsilon) + o(1)$ uses the $1$-Lipschitz property of $g_\beta$ in addition to monotonicity (line 140 cites only monotonicity).
  - In line 181, windows of bad sources $m \notin G$ may overlap windows of good sources $n \in G$, so subtracting $\sum_{n \in G} E_{k_+}(|U(n)|)$ from the union bound uses the elementary set inequality $|(\mathcal U_{\rm good} \cup \mathcal U_{\rm bad}) \setminus Z| \le |\mathcal U_{\rm good}| - |Z| + |\mathcal U_{\rm bad}|$ together with the fact that shifts in $Z_n \subseteq \mathcal U_{\rm good}$ are genuinely not $\rho_N$-far (by isolation of $n \in G$).
- **Fix:** Mention "monotonicity and Lipschitz continuity of $g$" on line 140, and add one sentence on line 181 noting that overlapping bad windows cannot make shifts in $Z_n$ far, so $|(\mathcal U_{\rm good} \cup \mathcal U_{\rm bad}) \setminus Z| \le |\mathcal U_{\rm good}| - |Z| + |\mathcal U_{\rm bad}|$.

#### [Minor B1.3] Missing constant factor $C_{\mathcal S}^{z-1}$ in Proposition 1.6 display (212)
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 209–215.
- **Issue:** Line 209 defines $H(s, z)$ via $\sum_{c(n)>0} z^{r(n)} n^{-s} = \zeta_{\mathcal S}(s)^z H(s, z)$ where $\zeta_{\mathcal S}(s) = \zeta(s)^\delta \cdot g_{\mathcal S}(s)$ with $C_{\mathcal S} := g_{\mathcal S}(1) > 0$. Applying Tenenbaum II.5.2 to $\zeta(s)^{\delta z} (g_{\mathcal S}(s)^z H(s, z))$ produces $C_{\mathcal S}^{z-1} \frac{\Gamma(\delta) H(1, z)}{\Gamma(\delta z) H(1, 1)}$ in (212), not $\frac{\Gamma(\delta) H(1, z)}{\Gamma(\delta z) H(1, 1)}$. Because $|C_{\mathcal S}^{z-1}| = O(1)$ on $|z| \le 1$, the orthogonality bound on line 215 is completely unaffected.
- **Fix:** Include $C_{\mathcal S}^{z-1}$ in (212), or absorb $(\zeta_{\mathcal S}(s)/\zeta(s)^\delta)^z$ into $H(s, z)$ on line 209.

#### [Minor B2.1] False commentary claim about classes of order $4$ in $2$-groups (contradicted by $\Delta = -95$)
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, line 421 (cf. line 413).
- **Issue:** Line 421 states: *"For the classes of order $4$ in a $2$-group (for example $2x^2\pm xy+5y^2$ for $\Delta=-39$ and the four forms $3x^2\pm2xy+22y^2$, $6x^2\pm2xy+11y^2$ for $\Delta=-260$), the fraction is exactly $1$. Their genus is $\{C, C^{-1}\}$ and $a_C = a_{C^{-1}}$, so $a_C = a/2$ identically."* This is **false** for $\Delta = -95$ ($\mathrm{Cl}(-95) \cong \mathbb Z/8$): its order-$4$ classes $Q = 4x^2 \pm xy + 6y^2$ belong to the principal genus of size $h_0 = 4$ (not $\{C, C^{-1}\}$), and line 413 of the table directly above reports their fraction as `0.661`, not `1.000`. The identity $a_C = a/2$ holds for non-ambiguous classes whenever $h_0 = |G^2| = 2$ (which happens for $\mathbb Z/4$ and $\mathbb Z/2 \times \mathbb Z/4$, not for all $2$-groups).
- **Fix:** Replace "For the classes of order $4$ in a $2$-group" with "For the non-ambiguous classes when $h_0 = 2$ (for example, the classes of order $4$ in $\mathbb Z/4$ for $\Delta = -39$ and in $\mathbb Z/2 \times \mathbb Z/4$ for $\Delta = -260$)".

#### [Minor B2.2] Imprecise domain phrasing for the Haar measure in Lemma 2.8
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, line 326.
- **Issue:** The statement writes *"the Haar measure of $\{j \in \mathbb Z_\ell : v(f_A(j)) \ge H\}$ (with $j$ interpolated on residue classes modulo $T$)"*. Because $T = |(\mathcal O/\mathfrak m^\nu)^\times| = (q_K - 1) q_K^{\nu - 1}$ has a prime-to-$\ell$ factor $q_K - 1$, $j \bmod T$ is not determined by $j \in \mathbb Z_\ell$, so $f_A(j)$ is not well-defined on $\mathbb Z_\ell$ alone. What the proof actually establishes—and what Proposition 2.10 and §2.5 actually invoke—is uniform convergence to $0$ of the product Haar measure on $(\mathbb Z / T\mathbb Z) \times \mathbb Z_\ell$, equivalently $\frac{1}{T\ell^H}\#\{0 \le j < T\ell^H : v(f_A(j)) \ge H\} \to 0$ uniformly in $A \in \mathcal C$.
- **Fix:** State the conclusion for the Haar measure on $(\mathbb Z/T\mathbb Z) \times \mathbb Z_\ell$, or directly as $\sup_{A \in \mathcal C} \frac{1}{T\ell^H} \#\{j \bmod T\ell^H : v(f_A(j)) \ge H\} \to 0$.

#### [Minor B2.3] Minor precision gaps in the proof of Theorem B2′ (§2.5)
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 397–400.
- **Issue:** Three small details are compressed or slightly imprecise:
  1. Line 400 writes "a nonzero homomorphism $\mathbb Z^k \to \mathbb Q_q$ (via $\log$)". The values $\psi(\eta_c)$ lie in $\mathbb Q(\zeta_{|G_{\rm odd}|})^+$, so $\log$ maps into a finite extension $L/\mathbb Q_q$, not necessarily $\mathbb Q_q$ itself (e.g., $\mathbb Q_5(\sqrt 5)$ for $\mathbb Z/5, q = 5$).
  2. The affine-hyperplane argument ("with $w_{c_1} = 1$ ... finitely many such sets do not cover the affine lattice") needs $k = |G_{\rm odd}/\pm| \ge 2$ (noting $G_{\rm odd} = 1$ is already settled by Theorem 2.3), should note that $\ker\Lambda \cap \{w_{c_1} = 1\}$ is either empty or a coset of an infinite-index subgroup of $\mathbb Z^{k-1}$ (using torsion-freeness of $L$), should note that choosing $T$ first so $\psi(\eta_c)^T \in 1 + \mathfrak m_L^\nu$ ensures $\prod_c \psi(\eta_c)^{Tw_c} \ne \prod_c \psi'(\eta_c)^{Tw_c} \implies \beta_\psi/\beta_{\psi'}$ is not a root of unity (since $1 + \mathfrak m_L^\nu$ is torsion-free), and should mention that $w_{c_1} = 1$ makes $(\mathbf u, j) \mapsto (0, \mathbf u) + j\mathbf w$ unimodular on $(\mathbb Z/M\mathbb Z)^k$.
  3. In (397), $m_c(n)$ for $c \in G_{\rm odd}/\pm$ aggregates over $g_2 \in G_2$, whereas line 400's genus-independence claim ("The classes in $G_{\rm odd}$ do not affect the genus") varies only the principal-genus coordinates $(m_{(1, c)})_{c \in G_{\rm odd}/\pm}$ while holding all $g_2 \ne 1$ coordinates fixed and absorbing their $q$-adic unit contributions into the compact coefficient set $\mathcal C$.
- **Fix:** Replace $\mathbb Q_q$ by $L$, note $G_{\rm odd} \ne 1$ (since $G_{\rm odd} = 1$ is Theorem 2.3), state the torsion-freeness of $1 + \mathfrak m_L^\nu$ and unimodularity of $w_{c_1} = 1$, and explicitly separate the principal-genus coordinates $m_{(1,c)}$ from the conditioned $g_2 \ne 1$ coordinates.

#### [Minor B2.4] Lemma 2.7: `\asymp` vs `\ll` at $\alpha_1(z) = 0$ and odd-$M$ genus conditioning
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 322–324.
- **Issue:** Line 324 writes "gives a mean $\asymp S \cdot (\log N)^{\Re\alpha_1(z) - 1/2}$". When $\alpha_1(z) = 0$ (which actually occurs whenever $z_c = \psi_g(c)$ is a nontrivial genus character), $1/\Gamma(\alpha_1(z)) = 0$ and the leading term vanishes, so the mean is $\ll S \cdot (\log N)^{\Re\alpha_1(z) - 1/2}$ (indeed $O(S(\log N)^{-3/2})$), not $\asymp$. In addition, the genus is a linear function of $(m_c \bmod 2)$, which defines a coset in $(\mathbb Z/M\mathbb Z)^r$ directly when $2 \mid M$; for odd $M$, one applies the unconditioned statement modulo $2M$ to conclude that $(m_c \bmod M)$ is independent of the genus (uniform on all of $(\mathbb Z/M\mathbb Z)^r$). Also implicitly $\pi$ is admissible (even exponents at inert $p \le P_0$).
- **Fix:** Replace `\asymp` with `\ll` on line 324, note admissibility of $\pi$, and state that for odd $M$ one reduces from $\mathrm{lcm}(2, M)$.

#### [Minor B2.5] Scope of the explicit $\mathbb Z/5$ excess bound $\le 3$
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, lines 362–366.
- **Issue:** The Lucas formulas (363) and the claim *"the excess is at most $3$"* hold for squarefree $n$ (all $m_1 + m_2 \ge 0$ with $a_C > 0$) and for general $n$ whenever $m_1 + m_2 \ge 4$. However, if $m_1 + m_2 \le 3$ and $e = 2$ split prime powers occur, the excess can exceed $3$: e.g., $m_0 = 0, m_1 = 1, m_2 = 2$ together with four $e = 2$ split primes of class $\pm 1$ gives $5 a_0 = 2^3 \cdot 3^4 - 2 L_3 = 640$, so $a_0 = 128 = 2^7$ (excess $7$).
- **Fix:** Clarify on line 362/366 that (363) is for squarefree $n$ (and that the excess bound $\le 3$ persists for general $n$ once $m_1 + m_2 \ge 4$).

#### [Minor B2.6] Theorem 2.3 Rankin exponent choice and minor script polish / coverage gaps
- **Location:** `notes/phase22/radix-thresholds-and-class-groups.md`, line 282; `scripts/phase22_radix_classgroups.py`, lines 193, 817, 852, 878, 909–982.
- **Issue:**
  - On line 282, deducing $\sum_{n \in \operatorname{supp} r_Q, n \le N} (\log_b r_Q(n))^2 \ll S \cdot (LL)^2$ from the Rankin moments of Phase 21 (F2) uses the $N$-dependent exponent $s = 1/LL$ (or one can use any small fixed $s > 0$ with $2^{s-1} - \frac{1}{2} < c/2$ to get $o(S)$ directly, though not the displayed $S \cdot LL \cdot (\log N)^{-c/2}$).
  - In `scripts/phase22_radix_classgroups.py`: minor draft/cosmetic remnants (`# Lemma B1.A` line 193, `# Theorem B2.1` line 878, `"six/seven discriminants"` line 817, unused `n_annih = 0` line 852, `-260` omitted from B2.5's print loop line 980).
  - Coverage note: `section_b2_excess` only tests $|G_2^2| = 1$ discriminants (`-47, -87, -71`), and the script includes no finite measurement of odd-$q$ valuations $v_q(a_C)$ (Theorem B2′) or of a real discriminant with non-cyclic $G_{\rm odd}$ (e.g., $\Delta = -3299$ or $-4027$ with $\mathrm{Cl}(\Delta) \cong \mathbb Z/3 \times \mathbb Z/3$), although B2.2 tests abstract group-ring products in $\mathbb Z/3 \times \mathbb Z/3$.
- **Fix:** Optionally note $s = 1/LL$ on line 282 (or replace the bound with $S(\log N)^{-c/4}$ from a small fixed $s$), and tidy the script comments/print labels if revising the script.

---

## Post-Repair Verification

Post-repair audit performed on the updated `notes/phase22/radix-thresholds-and-class-groups.md` (473 lines) and `scripts/phase22_radix_classgroups.py` (1,020 lines). Reminder: cross-model verification is not independent human peer review.

### Re-run of Verification Script

```sh
python -B scripts/phase22_radix_classgroups.py
```

- **Exit code:** `0`
- **Runtime:** `8.5 s` internal (`8.58 s` wall clock)
- **Assertions:** `3,141,166` checks passed
- **New B2.4 outputs verified against note lines 378 & 463:**
  - $\Delta = -327$ (fundamental, $\mathrm{Cl}(-327) \cong \mathbb Z/12$, $|G_2^2| = 2$, filtered by order-4 annihilation): `P(excess=0)=0.869, P(excess=1)=0.124, P(excess=2)=0.008, max=2`; mean $v_3(a_C) = 0.0656$, mean $v_5(a_C) = 0.0048$. Matches lines 378 and 463.
  - $\Delta = -4027$ (fundamental, $\mathrm{Cl}(-4027) \cong \mathbb Z/3 \times \mathbb Z/3$, non-cyclic $G_{\rm odd}$): `P(excess=0)=0.963, P(excess=1)=0.037, max=1`; mean $v_3(a_C) = 0.0000$, mean $v_5(a_C) = 0.0000$. Matches lines 378 and 463.
  - Exact tail check confirms literally `0` supported pairs $(n, Q)$ with $n \le 3 \cdot 10^4$ have $v_3(a_C) \ge 3$ or $v_5(a_C) \ge 3$ across all five discriminants (`-47, -87, -71, -327, -4027`), matching line 463 verbatim.
  - All previously checked tables, constants, and B2.5 output (now including `-260`) continue to match.

### Item-by-Item Resolution Check

| Finding | Location in revised files | Verification | Status |
|---|---|---|---|
| **Major 1** (Prop. 2.10 conditioning, quantifier order, $p \le P_0$ split, $d=1$) | Note lines 346–376 | Rewritten cleanly into Steps 0–4: Step 0 cleanly splits $m_K = m^>_K + m^{\le}_K$ and defines $\mathrm{val}_K = m^>_K + v_K(\pi)$ and $F_{G_{\rm odd}} = w_1(\pi)$ (no spurious factor $2$ at $d = 1$); Step 1 treats each fixed candidate kernel $K \in \mathcal K(\pi)$ unconditionally on $(\pi, \text{genus})$ (varying only $g^* = \{(1,c^*),(1,c^{*-1})\} \subset G^2$), completely eliminating conditioning leakage; Step 2 fixes $H''(\pi), H_{\rm tie}, H$; Step 3 chooses $M$ *after* $H_{\rm tie}$ is fixed; Step 4 takes the union bound ($3\varepsilon/4 + o(1) < \varepsilon$) and applies the strict ultrametric inequality $v_2(T_{K^*}) < \mathrm{val}_{K^*} + H_{\rm tie} < v_2(T_K)$ for all $K \ne K^*$. Airtight. | **Resolved** |
| **Minor B1.1** ($\ell \ge 1$, $\ell_i > 0$, $0^0 = 1$, $\omega \ge 1$) | Note lines 12, 26, 88, 102 | All four precision clauses added cleanly. | **Resolved** |
| **Minor B1.2** ($1$-Lipschitz in (137), overlapping bad windows in Thm. 1.4) | Note lines 140, 181 | Both justifications stated explicitly with exact inequalities. | **Resolved** |
| **Minor B1.3** ($C_{\mathcal S}^{z-1}$ in Prop. 1.6) | Note line 209 | $(\zeta_{\mathcal S}(s)/\zeta(s)^\delta)^z$ cleanly absorbed into $H(s, z)$, making (212) exact. | **Resolved** |
| **Minor B2.1** (False order-4 claim for $2$-groups) | Note line 445 | Corrected to non-ambiguous classes when $h_0 = 2$ and explicitly contrasted with $\Delta = -95$ ($\mathbb Z/8$, $h_0 = 4$, fraction `0.661`). | **Resolved** |
| **Minor B2.2** (Haar-measure domain in Lemma 2.8) | Note lines 326–334 | Restated via finite-modulus density mod $T\ell^{a(H)}$ and equivalently Haar measure on $\mathbb Z/T\mathbb Z \times \mathbb Z_\ell$. | **Resolved** |
| **Minor B2.3** (§2.5 Theorem B2′ precision gaps) | Note lines 412–425 | Explicitly assumes $G_{\rm odd} \ne 1$ ($G_{\rm odd} = 1$ is Thm. 2.3), splits $m^{\rm o}_c = m_{(1,c)} + m^{\rm rest}_c$ with $k = (|G_{\rm odd}|+1)/2 \ge 2$, uses the completion $L/\mathbb Q_q$ (noting ramification when $q \mid |G_{\rm odd}|$), invokes torsion-freeness of $1 + \mathfrak m_L^\nu$ to exclude root-of-unity ratios, and notes unimodularity of $w_{c_1} = 1$ on $(\mathbb Z/M)^k$. Airtight. | **Resolved** |
| **Minor B2.4** (Lemma 2.7 `\asymp` vs `\ll`, odd $M$, admissibility) | Note lines 322–324 | Admissibility stated, `\asymp` replaced by `\ll` with $1/\Gamma(0) = 0$ explanation, and odd-$M$ case handled via reduction from $2M$. | **Resolved** |
| **Minor B2.5** ($\mathbb Z/5$ excess bound scope) | Note lines 378–384 | Restricted explicitly to squarefree $n$ (and general $n$ with $m_1 + m_2 \ge 4$), with the $m_1 + m_2 = 3$, $a_0 = 2^7$ counterexample recorded. | **Resolved** |
| **Minor B2.6** (Thm. 2.3 Rankin exponent & script polish/coverage) | Note line 279; script lines 193, 817, 852, 876, 907–1000 | Explicit $s = 1/LL$ and $y^2 \le 2e^y$ added to Theorem 2.3; script labels/unused variable tidied, `-260` added to B2.5, and B2.4 expanded with $\Delta = -327$ ($\mathbb Z/12$, annihilation-filtered), $\Delta = -4027$ ($\mathbb Z/3 \times \mathbb Z/3$), and odd-$q$ valuation measurements. | **Resolved** |

### Updated Verdicts

| Track | Updated Verdict | Open Critical | Open Major | Open Minor |
|---|---|---:|---:|---:|
| **B1** (Even composite radices, run packing, run sandwich, isolation scale) | **Accept** | 0 | 0 | 0 |
| **B2** (General class groups, order-4 annihilation, Strassmann non-cancellation, unconditional $(V_q)$) | **Accept** | 0 | 0 | 0 |
