# Cross-Provider Referee Review — Phase 22 Track D (D3–D4 + Complete Proof of Lemma S)

- **Audited files (read in full, unmodified):**
  - `notes/phase22/partitions-carry-and-lemma-s.md` (631 lines)
  - `scripts/phase22_partitions_carry.py` (1,122 lines)
- **Cross-checked references:** `notes/phase21/partitions-and-higher-modular.md`, `notes/phase21/euler-scalings-and-reciprocals.md`, `notes/phase20/euler-product.md`, `notes/phase19/geometry.md`, `NormalityChecker/CoefficientTransfer.lean`, `NormalityChecker/GeneralMassTransfer.lean`.
- **Disclaimer:** This is an automated cross-model mathematical referee review and is **not** independent human peer review.

---

## Executive Summary and Verdicts

| Component | Verdict | Summary |
| --- | --- | --- |
| **Lemma S & Theorem D1.5 (§1)** | **Accept with revisions** (1 Major, 3 Minor + scope hygiene) | The self-contained Selberg sieve (Lemmas S.1–S.4, Proposition S′, Theorem S) and the complete proof of Theorem D1.5 for odd prime denominators are mathematically sound and close the Phase 21 sketch gap uniformly up to $H \le N$. One boundary hypothesis error in Lemma S.1 ($\xi \ge 1$ vs. $\xi > 1$), one arithmetic slip ($7.07 \times 10^{-4}$ vs. $< 10^{-6}$), and `"the brief"` process language in §1.6 need repair. |
| **D3: Intermediate Euler products & Mahler (§2)** | **Accept with revisions** (3 Major, 4 Minor + scope hygiene) | The core theorems (Proposition D3.8, Proposition D3.9(a)–(d) as stated, Theorem D3.11, Corollary D3.12, Proposition D3.13, Proposition D3.14) are sound. However: (i) Lemma D3.10's fractional-digit agreement bound is false at $K = 1$ (explicit base-2 counterexample); (ii) the $2^{k^2}$ schedule in both note and script erroneously uses $m_4 = 16384 = 2^{14}$ instead of $65536 = 2^{16}$; (iii) the parity condition of Proposition D3.9(c) is dropped in the summary table, §2.5 phase diagram, and prose; and (iv) §2.5 contains `"the brief"` process language. |
| **D4: Signed digits & entropy–multiplicity wall (§3)** | **Accept with minor revisions** (1 Major [scope hygiene only], 3 Minor) | Every mathematical proof in §3—net transfer (Theorem D4.8), completeness and base-$2$/base-$b$ digit characterizations (Theorem D4.9, Corollary D4.9′), the quadratic-width example (E2), Lemmas D4.10–D4.12, the CM prime-value multiplicity bound (Lemma D4.15), and the signed-digit wall (Theorem D4.13, Corollary D4.14)—is mathematically airtight. Needs cleanup of `"the brief"` language in §3.7, a Vinogradov-notation self-contradiction (`W_U \gg N^2` vs. `\asymp N^2`), and minor editorial/script fixes. |

- **Critical findings:** **0**
- **Major findings:** **5** (4 mathematical/computational, 1 scope hygiene across four locations)
- **Minor findings:** **8**

---

## 1. Script Execution and Numerical Audit

Executed `python -B scripts/phase22_partitions_carry.py` in the worktree root:
- **Exit code:** `0`
- **Assertions:** `1,256,932 checks` passed (matches lines 5 and 602 of the note).
- **Runtime:** `5.7 s` internal / `6.2 s` wall time (matches "about 7 s" on lines 5 and 602).
- **Table/number match:** Every printed value in the script matches the corresponding displayed number or table entry in `notes/phase22/partitions-carry-and-lemma-s.md` to the stated rounding precision, **with three caveats**:
  1. The erroneous entry $m_4 = 16384$ (and ratio $1.6 \times 10^{-4}$) for $2^{k^2}$ at $K = 3$ is shared between `scripts/phase22_partitions_carry.py:779` and `notes/phase22/partitions-carry-and-lemma-s.md:371,375` (Major #2).
  2. The label/bound `6/(D_4+1) = 0.00453` for $M = \{1, 2, 3, 6, 252\}$ is shared between `scripts/phase22_partitions_carry.py:859,868` and `notes/phase22/partitions-carry-and-lemma-s.md:344`, whereas Theorem D3.11 proves `6/D_4 = 0.00454` (Minor #1).
  3. The Selberg remainder `21.0` quoted on line 244 is the $\lambda$-weighted remainder $\sum |\lambda_{d_1}\lambda_{d_2} r_{[d_1,d_2]}|$ computed on script line 554, whereas Lemma S.1 (line 66) displays the unweighted remainder $\sum |r_{[d_1,d_2]}|$ (which equals `77.1` on that instance; Minor #7).

---

## 2. Adversarial Audit by Section

### 2.1 Section 1 — Lemma S (Theorem S, Proposition S′, Lemmas S.1–S.4) & Theorem D1.5
- **Lemma S.1 (Selberg):** The diagonalization via $h(p) = (p - \rho(p))/\rho(p)$, Möbius inversion, Cauchy–Schwarz optimality $y_t = \mu(t) g(t)/G(\xi)$, and the injectivity proof of $|\lambda_d| \le 1$ via $g(d)/f(d) = \sum_{s \mid d} g(s)$ and $sk < \xi$ are completely valid for $\xi > 1$. Only the stated boundary $\xi \ge 1$ fails with strict $d < \xi$ (Major #4).
- **Lemma S.2 (lower bound for $G$):** Checked every step: $\kappa(p^k) \le \rho(p)^k$ for $\rho(p) \in \{1, 2\}$ ($k + 1 \le 2^k$); $g(e) \ge \sum_{\operatorname{rad} n = e} \kappa(n)/n$; convergence of $\sum_{\operatorname{rad} n \mid P} \kappa(n) n^{\delta-1}$ since $p^{\delta-1} \le e/5 < 1$ for $5 \le p \le z$; convexity $e^t - 1 \le (e - 1)t$ on $[0, 1]$; elementary Mertens bound $\sum_{p \le z} (\log p)/p \le \log z + \log 4 < \log z + 2$; and the arithmetic $2 \frac{e-1}{1 - e/5}(1 + 2/\log z) \le 15.0613 < 15.07$ for $\log z \ge 2$, giving $e^{-17 + 15.07} = e^{-1.93} \approx 0.145 < 1/2$. Airtight.
- **Lemma S.3:** Apostol *Introduction to Analytic Number Theory*, Theorem 7.3 gives $\sum_{p \le x,\, p \equiv a\,(12)} (\log p)/p = \frac{1}{4}\log x + O(1)$; partial summation over $a \in \{5, 7, 11\}$ and $(1 - 1/p)^2 \le e^{-2/p}$ yield the bound cleanly for $z \ge 5$.
- **Lemma S.4:** $g^2 \mid h$ (from $g^2 \mid 12h$ and $\gcd(g, 6) = 1$), unique CRT class modulo $L = v^2 v'^2/g^2$, linear forms $A_1 = 12v'^2/g^2, A_2 = 12v^2/g^2$, determinant $A_1 B_2 - A_2 B_1 = \frac{12}{g^2}(v'^2 B_2 - v^2 B_1) = 144h/g^2$, and $\rho(p) = 2 - [p \mid h]$ for $p \in \mathcal P_0, p \nmid vv'$ are all exact.
- **Proposition S′ & Theorem S:**
  - $V^4 = (\log N)^{12} \le N$ at $\log N \ge 200$ ensures $L \le N$ and $X \le N/L + 1 \le 2N/L$.
  - Class (i) uses $12(n+h)+1 \le 24N+1$ (valid for all $1 \le h \le N$) and $\sqrt{12N+1}+\sqrt{24N+1} \le 9\sqrt N$; minor caveat on non-integer $V$ in $\sum_{v > V} 1/v^2 \le 1/V$ (Minor #3).
  - Class (ii) remainder $\sum_{d_1, d_2 < \xi} \tau([d_1, d_2]) \le (\sum_{d < \xi} \tau(d))^2 \le \xi^2(1 + \log \xi)^2$ is exact.
  - Product split, factor $(\log z)^{-3/2} = 1000 (\log N)^{-3/2}$, injective reparametrization $(v, v') = (gw, gw')$ with $1/L = 1/(g^2 w^2 w'^2)$, exact Euler products for $C_5$ ($\zeta(2)\prod_p(1 + ((p/(p-1))^r - 1)p^{-2})$ for $r = 2, 4$), and $\sum_{h \le H} h/\varphi(h) \le \frac{\zeta(2)\zeta(3)}{\zeta(6)} H < 1.9436 H$ are all exact.
  - The remainder $R(N)(\log N)^{3/2}/N$ at $\log N = 200$ is $7.071 \times 10^{-4} < 1$ (sufficient for Proposition S′, though not $< 10^{-6}$ as claimed on line 215; Minor #2).
- **Theorem D1.5 (§1.7):** Complete and airtight. Step (i) properly combines coefficient transfer ($|\tau_n| > \varepsilon$ has density $0$) with $M_N(\frac{1}{\ell} E_b^2 - c') \to 0$ to pin $c' \equiv c/\ell \pmod 1$ with $bc \equiv c \pmod \ell$. Step (ii) correctly deduces run stability and non-adjacency of $c$-runs. Step (iii) uses Wirsing's asymptotic ($\sim$, not just $\asymp$, which is essential to keep $|S' \cap (N/2, N]| \ge \kappa N (\log N)^{-3/4}$ positive after differencing), correctly verifies $uv^2 \equiv 1 \pmod{12}$ automatically, applies Theorem S twice (at $n$ and $n - h \in [1, N]$ once $H < N/2$, with $0 \in S_\ell$ ensuring $n_{i-1}$ exists so $[n_i - H, n_i) \subseteq [n_{i-1}, n_i)$), and bounds stretch overlap by $2$.

### 2.2 Section 2 — D3 (Intermediate Euler Products & Mahler)
- **Proposition D3.8:** Sound (tiny wording tweak in (c); Minor #8).
- **Proposition D3.9:** All four parts (a)–(d) are rigorously proved as stated:
  - (a) $b^{T_K} > D_K \ge b^{\sum m_j} E_2 > b^{\sum m_j - 2}$ works for all $b \ge 2$ since $E_2 > 1/4 \ge b^{-2}$.
  - (b) $\Phi \equiv t \pmod{D_{K-1}}$ gives $T_K = m_K D_{K-1}$ cleanly whenever $T_{K-1} \mid m_K$.
  - (c) LTE applies to all primes $q \mid D_K$ under the parity condition ($b$ even $\implies 2 \nmid D_K$; $b \equiv 1 \pmod 4$ or $m_K$ even $\implies 4 \mid b^{m_K} - 1$). However, dropping this parity condition in the summary table, §2.5 table, and prose produces false claims for odd chains in bases $b \equiv 3 \pmod 4$ (Major #3).
  - (d) Exact for $b = 2$ via $\gcd(2^a - 1, 2^c - 1) = 1$ and CRT over $\prod \mathbb Z/m_j\mathbb Z$.
- **Lemma D3.10:** $b^{-m_{K+1}} \le P_b(M) - R_K \le 32 b^{-m_{K+1}}$ is exact for all $K \ge 1$ (even at the extreme $b = 2, K = 1, M = \mathbb N$, where $s = 1/2$ and $e^{2s} - 1 = e - 1 < 2 = 4s$). However, the fractional-digit agreement claim is **false** at $K = 1$ (Major #1).
- **Theorem D3.11 & Corollary D3.12:** Sound. The Erdős–Turán bound $6/D_{K-1}$ (using $H = D_{K-1} - 1$ and Phase 21 Lemma D2.2; trivial if $D_{K-1} = 1$), period splitting, circle perturbation $2\eta + B/N$, and upper-density-1 block construction all work (Minor #1 and Minor #8).
- **Proposition D3.13 (Mahler):** Functional equation (a), finite identity, growth bound $\beta(n) \le 4.7685 \cdot 2^{K(K-1)/2}$ (b), window asymptotics $L(N) = \frac{(\log N)^2}{2\log 2 \log b}(1+o(1))$ (c), chain period (d), transcendence via Mahler's theorem (e), and base-change equivalences (f) are all sound, modulo two minor proof blemishes in (b)–(c) (Minor #4) and the boundary-limit phrasing in (e) (Minor #6).
- **Proposition D3.14:** Exact; Meinardus constant $\log \mathrm{sc}(n) \sim \pi\sqrt{n/6}$ verified ($\sum_{m\ge1} (-1)^{m-1}/m^2 = \pi^2/12 \implies \log F(e^{-t}) \sim \pi^2/(24t) \implies 2\sqrt{\pi^2 n/24} = \pi\sqrt{n/6}$).

### 2.3 Section 3 — D4 (Signed Digits & Entropy–Multiplicity Wall)
- **Theorem D4.8:** Cleanly reduces rearranged net sequences $A_{\rm net}(t) - c$ to the kernel-verified transfer theorems in `CoefficientTransfer.lean` and `GeneralMassTransfer.lean`.
- **Theorem D4.9 & Corollary D4.9′:** Completely rigorous. For $I_t = \lfloor b^t w + \frac{1}{2} \rfloor$, telescoping, $|A(t)| \le \lfloor (b+1)/2 \rfloor$ (in fact $\le \lfloor b/2 \rfloor$ since $\varepsilon_t \in (-\frac{1}{2}, \frac{1}{2}]$ makes both endpoints strict), and $S_A(N) \le \#\{n < N : \|b^n w\| \ge 1/(2b)\}$ are exact. Both Corollary D4.9′ (base 2) and the general base-$b$ digit characterization on line 482 check out completely (in case (i), $j/(b-1)$ lies at distance $\ge \frac{1}{b(b-1)}$ from $\frac{j}{b}$ and $\frac{j+1}{b}$; in case (ii), every pair outside $\{(0,0), (b-1, b-1)\}$ forces $\|b^{n-1} x\| \ge b^{-2}$).
- **Examples (E1)–(E2):** (E1)'s telescoping to $[t=0] + [t \in \{2^s - s - 1 : s \ge 1\}]$ and (E2)'s $W_U(N) \sim N^2/4$ with $A_{\rm net}(t) = 1 + [t \in \{2^s : s \ge 0\}]$ are exact (Minor #5 for Vinogradov notation, Minor #8 for script `WU` at powers of 2).
- **Lemmas D4.10–D4.12:** Every step verified:
  - D4.10: $|x| \ge b^{e_1} - (b-1)\sum_{j=1}^{r-1} b^{e_1-j} = b^{e_1 - r + 1}$ (sharp).
  - D4.11: potential $\sum |c_e|$ drops by at least $(b-1)|q| \ge 1$ per normalization step.
  - D4.12: $E = \lfloor \log_b X \rfloor + k$ covers all exponents $e_1 \le \lfloor \log_b X \rfloor + k - 1$; $k \le E/2$ holds for $N \ge b^2, A \ge 1, k \le \frac{\theta}{40A}\log_b N$; monotonicity of $y \mapsto y H(k/y)$ and $c \mapsto c[\log_2(2b-2) + \log_2(e(1+A/c))]$ holds; numerical constants $\log_2(e(1 + 40 \cdot 2^{20})) \approx 26.765 < 26.8$ and $(28.8 + 2\log_2 A)/(40A) \le 28.8/40 = 0.72 < 1$ for all $A \ge 1$ are exact.
- **Theorem D4.13, Lemma D4.15, Corollary D4.14:** Completely rigorous.
  - In Lemma D4.15, $\mathcal O_F$ has class number 1 for $\mathbb Q(\sqrt{-3})$ and $\mathbb Q(i)$, all ramified/conductor primes divide the level ($36, 16, 9$), $a(p) \in \mathbb R \setminus \{0\}$ with $|\psi(\mathfrak p)| = |\psi(\bar{\mathfrak p})|$ forces $a(p) = 2\operatorname{Re}(\chi(\alpha)\alpha^{k-1})$ with $\chi$ factoring through $(\mathcal O_F/\mathfrak f)^\times$, $N(x + y\omega) \le Y \implies |x|, |y| \le \frac{2}{\sqrt 3}\sqrt Y < 2\sqrt Y$, $Q_\zeta(x, y)$ has exact degree $k - 1 \ge 1$, and the $2\delta(2R+1)$ zero bound holds (in fact $\delta(2R+1)$ holds).
  - In Corollary D4.14, (a) uses $n r_2(n) \le 4n\tau(n) \le 8 N^{3/2} \le N^2$ ($N \ge 64$) and $\mu \le \max_{m \le N} \tau(m) = N^{o(1)}$; (b) uses $n |a_2(n)| \le 2\sqrt{13} N^{3/2} \le N^2$ ($N \ge 52$) and Phase 20 Theorem 6(b); (c) uses Phase 21 Theorem D4.4's set $\mathcal T_f$ of size $\gg Y/\sqrt{\log Y}$, $\mu \le \sum_{m \le Y^{1/2}} C_g Y^{3/8} = C_g Y^{7/8}$, $A = k$ ($2 Y^{k/2} \le Y^k$ for $Y \ge 2$), and $\theta = \frac{1}{16}$ giving $\mu Y^\theta \le C_g Y^{15/16} = o(|\mathcal T_f|)$, pulling back bijectively along $m = (24n + r)/g_r$.

---

## 3. Detailed Findings

### Critical Findings

*None.*

---

### Major Findings

#### M1. Lemma D3.10 fractional-digit agreement bound is false as stated for $K = 1$
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:318–320`
- **Problem:** Lemma D3.10 claims for all $K \ge 1$ that "$P_b(M)$ and $R_K$ agree in at most $m_{K+1}$ fractional digits," citing Phase 21, Theorem D3.7(3). Unlike Theorem D3.7(3) (which explicitly proved $\lfloor P_b \rfloor = \lfloor r_K \rfloor$ for $K \ge 3$), Lemma D3.10 omits any check that $P_b(M)$ and $R_K$ share the same integer part. For $b = 2$ and $K = 1$, $P_2(M) - R_1$ can exceed $1$, allowing arbitrarily long agreement in fractional digits.
- **Counterexample:** Take $b = 2$, $K = 1$, and $M = \{1, 2, 4, 5, 6, 8, 9\}$ (or append $\{m \ge 1000\}$ to make $M$ infinite). Then $m_1 = 1$, $m_2 = 2$, $R_1 = 2 = 2.00000000000\ldots_2$, while
  $$P_2(M) = 3.00036444\ldots = 3.0000000000010111\ldots_2$$
  ($P_2(M) - 3 \approx 2^{-11.42}$). Thus $P_2(M)$ and $R_1$ agree in **11** fractional binary digits, contradicting the stated upper bound $m_2 = 2$.
- **Actionable fix:** Either add the hypothesis $b^{m_{K+1}} \ge 64$ (so $P_b(M) - R_K \le 32 b^{-m_{K+1}} \le \frac{1}{2}$, which forces $\lfloor P_b(M) \rfloor = \lfloor R_K \rfloor$ whenever at least one fractional digit agrees), or rephrase the conclusion as agreement in the **full** base-$b$ expansion (both integer part and at most $m_{K+1}$ fractional digits).

#### M2. Wrong term $m_4 = 16384$ (should be $65536 = 2^{4^2}$) in the $2^{k^2}$ schedule in both note and script
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:371,375`; `scripts/phase22_partitions_carry.py:779`
- **Problem:** For $m_k = 2^{k^2}$, the first four terms are $2^1 = 2$, $2^4 = 16$, $2^9 = 512$, and $2^{16} = 65536$. Line 779 of the script instead enters `[2, 16, 512, 16384]` ($16384 = 2^{14}$), producing the erroneous $K = 3$ ratio $m_4 / T_3 = 16384 / 100661760 \approx 1.6 \times 10^{-4}$ instead of $65536 / 100661760 \approx 6.5 \times 10^{-4}$ (which is also what line 375's own correct formula $2^{2K+1}/D_{K-1}$ evaluates to at $K = 3$).
- **Actionable fix:** Replace `16384` with `65536` in `scripts/phase22_partitions_carry.py:779`, re-run the script, and update `16384` $\to$ `65536` and `1.6\cdot10^{-4}` $\to$ `6.5\cdot10^{-4}` in `notes/phase22/partitions-carry-and-lemma-s.md:371,375`.

#### M3. Parity hypothesis of Proposition D3.9(c) omitted in summary table, §2.5 phase diagram, and prose
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:12,353,360,605`
- **Problem:** Proposition D3.9(c) (line 302) proves $T_K = m_K D_{K-1}$ for a divisibility chain under the condition that $b$ is even, $b \equiv 1 \pmod 4$, or $m_K$ is even. Lines 12 ("and for every divisibility chain"), 353 (`chains: {c^k}, ... | = m_K D_{K-1}`), 360 ("every super-exponential divisibility chain ... their periods are exactly $m_K D_{K-1}$"), and 605 ("on every chain") drop this condition.
- **Counterexample:** For $M = \{3^k : k \ge 1\}$ in base $b = 3$ or $b = 7$ ($b \equiv 3 \pmod 4$) at $K = 3$, $x = b^{27} \equiv 3 \pmod 4$ gives $v_2(x^2 - 1) \ge 3 = v_2(D_3)$, so $b^{m_3 D_2 / 2} \equiv 1 \pmod{D_3}$ and $T_3 \le m_3 D_2 / 2 < m_3 D_2$.
- **Actionable fix:** Restore the parity qualification of Proposition D3.9(c) on lines 12, 353, and 360 (noting that for odd $m_K$ and $b \equiv 3 \pmod 4$, $T_K$ can drop by a bounded power of $2$, namely at most $2^{v_2(b+1)-1}$, so the $m_{K+1}/T_K \to 0$ conclusion still holds), and specify "in base $2$" on line 605.

#### M4. Lemma S.1 boundary error: $\xi \ge 1$ with strict $d < \xi$ makes $G(1) = 0$
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:63,66,71`
- **Problem:** Lemma S.1 states its inequality "for every $\xi \ge 1$" while defining $G(\xi) = \sum_{d < \xi,\, d \mid P} g(d)$ with strict `<`. At $\xi = 1$, $G(1) = 0$ (division by zero in $X / G(\xi)$) and $d = 1$ fails $d < \xi$ in line 71 ("Let $\lambda_d$ ($d \mid P, d < \xi$) be real with $\lambda_1 = 1$").
- **Actionable fix:** Change `for every $\xi \ge 1$` to `for every $\xi > 1$` on line 63 (or change strict `< \xi` to `\le \xi` consistently across Lemmas S.1, S.2, and §1.4).

#### M5. Scope hygiene: `"the brief"` process language in four locations in the note
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:229,360,574,578` (and internal variable `brief50` in `scripts/phase22_partitions_carry.py:644–652`)
- **Problem:** The note contains explicit references to an internal task brief:
  - Line 229: `### 1.6 Corrections to the Phase 21 sketch and to the brief`
  - Line 360: `**Answer to the brief.** ... The brief's value $T_2=4(b^2-1)$...`
  - Line 574: `### 3.7 What the wall says, and corrections to the brief`
  - Line 578: `- **Brief's counting argument.** ...`
- **Actionable fix:** Remove all references to "the brief" and phrase lines 229, 360, 574, and 578 as self-contained mathematical exposition (comparing §1 against the Phase 21 sketch, stating the phase-diagram conclusion directly in §2.5, and explaining the exponent-range subtlety directly in §3.7). Optionally rename `brief50` in the script.

---

### Minor Findings

#### m1. Example in §2.4 and script quote `6/(D_4+1)` instead of Theorem D3.11's proved bound `6/D_4`
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:344`; `scripts/phase22_partitions_carry.py:859,868`
- **Problem:** Theorem D3.11 (lines 329, 334) takes $H = D_{K-1} - 1$ in Erdős–Turán to get $D_{T_K}(R_K) \le 6/D_{K-1}$ (one cannot take $H = D_{K-1}$ because $|\widehat C_5(D_4)| \approx 0.9866 \ne 0$). Line 344 and script lines 859/868 instead check/print `6/(D_4+1) = 0.00453` instead of `6/D_4 = 0.00454` ($6/1323 = 0.004535\ldots$).
- **Actionable fix:** Change `6/(D_4+1)` (`0.00453`) to `6/D_4` (`0.00454`) in line 344 and `6 / D4v` in script lines 859 and 868.

#### m2. Arithmetic slip in Proposition S′ remainder check at $\log N = 200$
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:215`
- **Problem:** Line 215 claims that at $\log N = 200$, the sum of the terms in $R(N)(\log N)^{3/2}/N$ is "below $10^{-6}$." The first term is $2 / (\log N)^{3/2} = 2 / 200^{3/2} \approx 7.071 \times 10^{-4}$ (the other two terms are $< 10^{-36}$). The proof only needs $\le 1$, so the theorem stands.
- **Actionable fix:** Replace `below $10^{-6}$` with `below $10^{-3}$` (about $7.1 \times 10^{-4} < 1$).

#### m3. Non-integer $V = (\log N)^3$ in Class (i) sum $\sum_{v > V} 1/v^2 \le 1/V$
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:166,171`
- **Problem:** For non-integer $V$, the unconstrained sum $\sum_{v > V} 1/v^2$ can exceed $1/V$ (e.g., at $V = m - \varepsilon$ it is $\approx (m - \frac{1}{2})^{-1} > 1/V$). The inequality holds here because line 171 sums only over $v$ coprime to $6$ (density $1/3$, giving $< 0.34/V$ for $V \ge 200^3$), but this is left implicit.
- **Actionable fix:** Either set $V = \lfloor (\log N)^3 \rfloor$ or note explicitly that $\sum_{v > V,\, \gcd(v,6)=1} 1/v^2 \le 1/V$ for $V \ge 10$.

#### m4. Proposition D3.13(c) tail constant at $b = 2$ and D3.13(b) rounding direction
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:400,411`
- **Problem:**
  1. In line 411, $\beta(2j) \le b^{j/2}$ for $j > N \ge j_0(b)$ yields $\sum_{j > N} b^{-j/2} = (\sqrt b - 1)^{-1} b^{-N/2}$. For $b = 2$, $(\sqrt 2 - 1)^{-1} = 1 + \sqrt 2 \approx 2.414 > 2$, which does not yield the stated $2 b^{-N/2}$ in line 400.
  2. In line 411, $\prod_{i \ge 1} (1 + 2^{-i}) = 2.384231029\ldots > 2.38423$, so writing `$\le 2 \cdot 2.38423 \cdot 2^{k(k-1)/2}$` rounds in the wrong direction (although $2 \times 2.384231029\ldots = 4.768462\ldots < 4.7685$ makes line 392's `4.7685` valid).
- **Actionable fix:** In line 411, use $\beta(2j) \le \frac{1}{2} b^{j/2}$ for $j \ge j_0(b)$ (or change $2 b^{-N/2}$ to $3 b^{-N/2}$ in line 400), and replace `2.38423` with `2.38424`.

#### m5. Self-contradictory use of Vinogradov notation $\gg$ on lines 496 and 580
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:496,580` (also line 353)
- **Problem:** Throughout §3 (lines 564, 566, 577, 579), $\gg$ denotes Vinogradov's $\Omega(\cdot)$. Writing "raw width $\gg N^2$ is impossible" (line 496) and "$W_U \gg N^2$ is impossible for a convergent series; $\asymp N^2$ is attained (E2)" (line 580) is self-contradictory under Vinogradov notation, since $W_U \asymp N^2$ implies $W_U \gg N^2$.
- **Actionable fix:** Replace `$\gg N^2$` on lines 496 and 580 with `super-quadratic ($W/N^2 \to \infty$)` or `$\omega(N^2)$` (and write `$m_{K+1}/(m_K b^{m_{K-1}}) \to \infty$` on line 353).

#### m6. Imprecise justification of transcendence of $f(z)$ over $\mathbb C(z)$ in Proposition D3.13(e)
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:407`
- **Problem:** Line 407 states that "$1/f$ vanishes at every root of unity of 2-power order," but $1/f(z) = \prod_{k \ge 0} (1 - z^{2^k})$ converges only on $|z| < 1$.
- **Actionable fix:** State that for every $2$-power root of unity $\zeta$ ($\zeta^{2^r} = 1$), $|f(\rho\zeta)| = f(\rho^{2^r}) / \prod_{j<r}|1 - (\rho\zeta)^{2^j}| \to \infty$ as $\rho \to 1^-$, so every $2$-power root of unity is a singularity of $f$ (unit circle is a natural boundary), ruling out algebraicity over $\mathbb C(z)$.

#### m7. Selberg numerical instance quotes the $\lambda$-weighted remainder while citing Lemma S.1's unweighted display
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:244`; `scripts/phase22_partitions_carry.py:553–554`
- **Problem:** Line 244 quotes $S = 662 \le 939.9 \le 939.6 + 21.0$ for "the Selberg inequality of Lemma S.1," where `21.0` is the weighted remainder $\sum |\lambda_{d_1}\lambda_{d_2} r_{[d_1,d_2]}|$ from line 74 of the proof; the unweighted sum $\sum |r_{[d_1,d_2]}|$ displayed in Lemma S.1 (line 66) is `77.1`. Separately, script line 553 checks `abs(rd) <= 2 ** len(pf(e))` with assertion message `"|r_d| <= omega(d)"`, which checks the looser bound $\tau(e)$ rather than $\rho(e)$ when $p \mid h$.
- **Actionable fix:** Note on line 244 that `21.0` is the $\lambda$-weighted remainder (and optionally report the unweighted remainder `77.1`), and tighten script line 553 to check `abs(rd) <= prod(omega[p] for p in pf(e))`.

#### m8. Editorial, indexing, and secondary-check slips
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:10,276,290,336,340,368,405,437,502,544,550`; `scripts/phase22_partitions_carry.py:1087`
- **Details & fixes:**
  - **Line 10:** Summary table references section `1.9` for Theorem D1.5; should be `1.7`.
  - **Lines 544 & 550:** Lemma D4.15 precedes Corollary D4.14 (numbering inversion); renumber or swap labels.
  - **Line 290 (Proof of D3.8(c)):** "For each $k$ choose a finite $F \subseteq M$ with $|F| = k$ and $\gcd F = 1$" requires $k$ at least the minimum size of a coprime subset; write "choose a finite $F \subseteq M$ with $|F| \ge 2$ and $\gcd F = 1$" (or "for sufficiently large $k$").
  - **Line 336 (Proof of D3.11):** `$|y_n - x_n| \le \eta$` should use circle distance `$\|y_n - x_n\| \le \eta$`.
  - **Line 340 (Corollary D3.12):** "Start from any finite set" should read "any nonempty finite set" so $K \ge 2$ and $m_{K+1} = K m_K D_{K-1} > m_K$.
  - **Lines 276 vs. 502; 368/405 vs. 379/437:** $\mathbb N$ denotes $\mathbb Z_{\ge 1}$ on line 276 and $\mathbb Z_{\ge 0}$ on line 502; `{2^k}` means $k \ge 1$ in §2.5/§2.6(d) and $k \ge 0$ in §2.6/§2.8. Make the index range explicit in each place.
  - **`scripts/phase22_partitions_carry.py:1087`:** `WU` for (E2) skips $m = 2^s$, omitting $u(2^s) = 1$ (12 digits total out of 2,248,500; displayed `0.2498` is unchanged). Add `+ sum(1 for m in range(1, MQ + 1) if (m & (m - 1)) == 0)`.
  - *(Optional remark on Theorem D4.9, line 470)*: Because $\varepsilon_t = I_t - b^t w \in (-\frac{1}{2}, \frac{1}{2}]$, the strict inequality $|\varepsilon_t - b\varepsilon_{t-1}| < (b+1)/2$ actually yields the slightly sharper bound $|A(t)| \le \lfloor b/2 \rfloor$ for all $b \ge 2$ (agreeing with $\lfloor (b+1)/2 \rfloor$ for even $b$ and tightening by $1$ for odd $b$).

---

## Post-Repair Verification

Re-audited `notes/phase22/partitions-carry-and-lemma-s.md` (637 lines) and `scripts/phase22_partitions_carry.py` (1,187 lines) in full and re-ran `python -B scripts/phase22_partitions_carry.py`.

### 1. Script Re-Execution
- **Command:** `python -B scripts/phase22_partitions_carry.py`
- **Exit code:** `0`
- **Assertions:** `1,256,966 checks` passed in `4.9 s` internal (`5.1 s` wall time), matching lines 5 and 608 of the note.
- **Output check:** All displayed numbers and tables in the revised note match the script output verbatim, including:
  - Selberg unweighted remainders $R = 77.1, 67.7, 81.1$ alongside weighted remainders $R_w = 21.0, 20.6, 30.2$ (line 244), with exact $|r_d| \le \rho(d)$ assertions;
  - $2^{k^2}$ at $K = 3$: $m_4 = 65536$ and $m_4 / T_3 = 6.5 \times 10^{-4}$ (lines 377, 381);
  - Lemma D3.10 $K = 1$ counterexample ($11$ agreeing digits) and $A < m_{K+1}$ checks under $b^{m_{K+1}} \ge 64$ (line 326);
  - Proposition D3.9(c′) verified by exact order tests across 18 cases in bases $3, 7, 11$ (line 318);
  - $M = \{1, 2, 3, 6, 252\}$ full-period discrepancy $0.00073 \le 6/D_4 = 0.00454$ (line 350);
  - Quadratic-width $W_U(3000)/N^2 = 0.2498$ now including the $u(2^s) = 1$ terms (script line 1152);
  - Base-3 canonical representation for $E_3^4$ asserting the tightened $|A(n)| \le 1 = \lfloor 3/2 \rfloor$ (line 600, script line 1174).
- **Scope hygiene:** `0` occurrences of `"brief"` (case-insensitive) in both `notes/phase22/partitions-carry-and-lemma-s.md` and `scripts/phase22_partitions_carry.py`.

### 2. Verification of Every Repair

| ID | Status | Verification Notes |
| --- | --- | --- |
| **M1** | **Verified fixed** | **Lemma D3.10** (lines 322–326) now requires $b^{m_{K+1}} \ge 64$. The proof is airtight: $0 < P_b(M) - R_K \le 32 b^{-m_{K+1}} \le \tfrac12$, so differing integer parts would force $\{R_K\} - \{P_b(M)\} = 1 - (P_b(M) - R_K) \ge \tfrac12 \ge 1/b$, incompatible with lying in the same half-open cell $[i/b, (i+1)/b)$ (even at the boundary $b = 2, \Delta = \tfrac12$). Thus the integer parts agree, giving $b^{-m_{K+1}} \le P_b(M) - R_K < b^{-A}$, hence $A < m_{K+1}$. The $K = 1$ counterexample is documented and script-verified. |
| **M2** | **Verified fixed** | `scripts/phase22_partitions_carry.py:785` and `notes/phase22/partitions-carry-and-lemma-s.md:377,381` now use $m_4 = 65536 = 2^{16}$ and $m_4/T_3 = 6.5 \cdot 10^{-4}$ (matching $2^{2K+1}/D_{K-1}$). |
| **M3** | **Verified fixed** *(1 trivial residual Minor below)* | **Proposition D3.9(c′)** (lines 304, 314) is rigorously proved and airtight: for $K \ge 2$, odd $m_1 \mid \cdots \mid m_K$, and $b \equiv 3 \pmod 4$, odd primes follow (c), $v_2(D_K) = K$, $v_2(D_{K-1}) = K - 1$, $v_2(x^t - 1) = 1 < K$ for odd $t$, and for even $t$ LTE on $x^2 \equiv 1 \pmod 8$ gives $v_2(x^t - 1) = v_2(x-1) + v_2(x+1) + v_2(t) - 1 = v_2(b+1) + v_2(t)$ (since $(b^{m_K}+1)/(b+1)$ has $m_K$ odd terms), forcing $v_2(t) \ge \max(1, K - v_2(b+1))$ and exact ratio $m_K D_{K-1}/T_K = 2^{\min(K-2,\,v_2(b+1)-1)}$. Script lines 861–880 verify exact orders (with `Tpr` equal to the exact prime support of $T$, since $v_2(T) \ge 1$). Summary table (line 12) and §4 (line 611) are accurate. *(See residual Minor r1 for lines 359 and 366.)* |
| **M4** | **Verified fixed** | **Lemma S.1** (line 63) now states $\xi > 1$, so $d = 1 < \xi$ is in range and $G(\xi) \ge 1 > 0$. |
| **M5** | **Verified fixed** | All `"the brief"` language removed from lines 229, 366, 580, 584, and `brief50` renamed to `avg_prod_1p2p` in script line 650. |
| **m1** | **Verified fixed** | Line 350 and script lines 923, 932 now use `6/D_4 = 0.00454`. |
| **m2** | **Verified fixed** | Line 215 now states `below 10^{-3}` with the exact dominant term $2/200^{3/2} \approx 7.1 \cdot 10^{-4}$ and remaining terms $< 10^{-36}$. |
| **m3** | **Verified fixed** | Line 171 now gives a clean, complete 2-line proof of $\sum_{v > V,\ \gcd(v,6)=1} v^{-2} \le 2\sum_{j \ge 0} (V+6j)^{-2} \le 2V^{-2} + 1/(3V) \le 1/V$ for all real $V \ge 3$. |
| **m4** | **Verified fixed** | Line 417 uses `2.38424` ($\ge \prod_{i \ge 1}(1+2^{-i}) = 2.384231\ldots$) for D3.13(b), and $\beta(2j) \le \tfrac12 b^{j/2}$ for $j \ge j_0(b)$ giving $\tfrac12(1+\sqrt 2) b^{-N/2} < 2 b^{-N/2}$ in D3.13(c) for all $b \ge 2$. |
| **m5** | **Verified fixed** | Lines 502 and 586 replace `$\gg N^2$` with `super-quadratic ($W/N^2 \to \infty$)` (and line 359 uses $m_{K+1}/(m_K b^{m_{K-1}}) \to \infty$). |
| **m6** | **Verified fixed** | Line 413 gives the rigorous radial-limit natural-boundary argument $|f(\rho\zeta)| = f(\rho^{2^r})/\prod_{j<r}|1-(\rho\zeta)^{2^j}| \to \infty$ as $\rho \to 1^-$ at every $2$-power root of unity $\zeta$. |
| **m7** | **Verified fixed** | Line 244 clearly reports both the $\lambda$-weighted remainder $21.0$ and the unweighted remainder $77.1$ (plus $67.7, 81.1$), and script lines 554–562 assert exact $|r_d| \le \rho(d)$ and both bounds. |
| **m8** | **Verified fixed** | Summary table cites `1.7` (line 10); Lemma D4.14 and Corollary D4.15 are properly ordered and cross-referenced throughout (lines 20, 550, 556, 572, 583, 585); D3.8(c) fixes $F_0$ and takes $k \ge \max(2, |F_0|)$ (line 290); D3.11 uses $\|y_n - x_n\|$ (line 342); Cor D3.12 specifies a nonempty starting set (line 346); $\mathbb Z_{\ge 1}$ and $\{2^k\}$ index ranges are disambiguated (lines 276, 372–377, 385, 443, 508); script line 1152 includes $u(2^s) = 1$; and **Theorem D4.9** (lines 476, 482) is rigorously tightened to $|A(t)| \le \lfloor b/2 \rfloor$ via strict inequalities on $\varepsilon_t - b\varepsilon_{t-1} \in (-\tfrac{b+1}{2}, \tfrac{b+1}{2})$. |

### 3. Residual Minor Finding Introduced by Repair

#### r1 (Minor). Combined chain lower bound `2^{v_2(b+1)-1}` in §2.5 fails at even $b$
- **Location:** `notes/phase22/partitions-carry-and-lemma-s.md:359,366`
- **Problem:** While Proposition D3.9(c′) itself (lines 304, 314) correctly restricts to $b \equiv 3 \pmod 4$ (where $v_2(b+1) \ge 2$), the combined summary phrases on line 359 (`always $\ge m_K D_{K-1}/2^{v_2(b+1)-1}$`) and line 366 (`in every case at least $m_K D_{K-1}/2^{v_2(b+1)-1}$`) omit the $b \equiv 3 \pmod 4$ qualifier. For every even $b$, $b + 1$ is odd so $v_2(b+1) = 0$ and $2^{v_2(b+1)-1} = \tfrac12$, making the expression read $T_K \ge 2 m_K D_{K-1}$, which is false since $T_K = m_K D_{K-1}$ by (c). (Note that column 3 of line 359 already uses $2^{v_2(b+1)} \ge 1$, which is valid for all $b$.)
- **Actionable fix:** Replace `2^{v_2(b+1)-1}` with `2^{\max(0,\,v_2(b+1)-1)}` (or `2^{v_2(b+1)}`) on lines 359 and 366.

### 4. Updated Verdicts

| Component | Updated Verdict | Remaining Findings |
| --- | --- | --- |
| **Lemma S & Theorem D1.5 (§1)** | **Accept** | 0 Critical, 0 Major, 0 Minor |
| **D3: Intermediate Euler products & Mahler (§2)** | **Accept** *(with 1 trivial Minor typo)* | 0 Critical, 0 Major, 1 Minor (`r1` on lines 359, 366) |
| **D4: Signed digits & entropy–multiplicity wall (§3)** | **Accept** | 0 Critical, 0 Major, 0 Minor |

*Reminder: Cross-model review is an automated audit and is not independent human peer review.*
