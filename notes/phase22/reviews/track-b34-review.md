# Cross-Provider Mathematical Referee Review: Phase 22 Track B (B3–B4)

- **Audited note:** `notes/phase22/odd-characters-and-kernel-quotient.md` (582 lines)
- **Audited script:** `scripts/phase22_characters_quotient.py` (1,095 lines)
- **Reviewer:** Independent cross-provider automated referee (Gemini 4 Neon)
- **Date:** 2026-11-26

> **Epistemic caveat:** This is an automated cross-model review and does **not** substitute for independent human peer review.

---

## Executive Verdicts

| Sub-track | Verdict | Summary |
| --- | --- | --- |
| **B3** (Cubic character mod 7 & universal disjunctivity) | **Accept with minor/editorial revisions (0 Critical, 2 Major, 6 Minor)** | All core theorems and proofs (Lemmas 1.1–1.2, Prop. 2.1, Lemma 2.2, Thm. 3.1, Props. 3.3–3.4, Lemmas 5.1–5.2, Thm. 5.3, Cor. 5.4) are mathematically sound. Theorem 5.3 withstands hostile audit across non-primitive $\Phi$, sign/carry edge cases, Landau–Page avoidance, and uniformity of the progression tail average. Two non-fatal **Major** issues require repair: a false convergence rate in Remark 3.2 ($O(X^{-1/2})$, not $(\log X)^{-1}$, for $k=2,4$) and an inaccurate phrasing in Corollary 5.4 ("integer combination" vs. "integer-valued linear combination"). |
| **B4** (Radix-power kernel tower) | **Accept with minor/editorial revisions (0 Critical, 2 Major, 5 Minor)** | All core theorems and proofs (Thm. 7.1, Thm. 8.1, Lemma 9.1, Thm. 9.2, Prop. 9.3, Cor. 10.1) are mathematically sound (modulo the explicitly acknowledged Phase 19 paper decomposition $K_b = F_b + M_b$). Two **Major** non-proof issues require repair: internal process language (`**Corrections to the brief.**` in §13) and two soundness/elaboration bugs in the §11 schematic Lean 4 signatures (`Fin d` coercion in `sampleDisc_sorted_eq` and missing summability hypothesis in `digit_window`). |

---

## 1. Script Execution & Numerical Cross-Check

Command executed in the worktree root:
```sh
python -B scripts/phase22_characters_quotient.py
```

- **Exit code:** `0`
- **Runtime:** `13.8 s` script-reported (`13.965 s` wall clock)
- **Assertions passed:** `252,793` (matches line 533: `252,793 assertions`)

### Table & Number Audit Against Script Output

| Note location | Claimed values | Script output | Status |
| --- | --- | --- | --- |
| §1 (line 83) | Exact match to $5\cdot 10^4$; 169 local factors | `n <= 50000`, `169 local factors` | Exact match |
| §2 (lines 105–115) | Least witnesses for $\lvert M\rvert \le 10$ ($c_+, c_-$); $c_+(n)=-19$ at $10\cdot 13^{18}=1124554069519573931290$ | All 42 table entries and $-19$ witness identical | Exact match |
| §3 (line 121) | $\delta \in [0.7503279, 0.7503287]$ | `[0.75032793, 0.75032868]` (outward rounding valid; tail $1-10^{-6}$ rigorous since $p > 999983 \implies p \ge 1000003 > 10^6$) | Exact match |
| §3 (line 139) | $X=10^6$: $S_-/S_+=0.6665$; class fractions $0.291, 0.209, 0.082, 0.043, 0.125, 0.252$; $c_+>0$ on $75.1\%$ | `0.6665`; `0.2906 0.2087 0.0817 0.0428 0.1245 0.2516`; sum $t\in\{0,1,5\} = 0.7509 \approx 75.1\%$ | Exact match |
| §3 (line 147) | $\mu_+=1.0754947610\ldots$, $\mu_-=-0.1215871326\ldots$, $L(1,\chi)=0.5377473805\ldots - 0.1052975456\ldots\,i$ | `1.075494761010`, `-0.121587132630`, $\frac{\sqrt 3}{2}\mu_- = -0.10529754563\ldots$ | Exact match (see Minor M7 on lines 12, 122) |
| §3 (lines 161, 165–169) | Square ratios `3.67, 3.55, 3.47`; finite data table at $10^4, 10^5, 10^6$ | All 21 table cells and all 3 ratios (`3.6675, 3.5514, 3.4690`) identical | Exact match |
| §5.1 (line 193) | Lemma 5.1 positions: `1196, 8318, 1202, 4368` | `1196, 8318, 1202, 4368` | Exact match |
| §5.4 (lines 321–327) | 5 displayed rows of 14 explicit instances | All 5 rows ($V_1, A$, kill primes, $7Q, N$) identical | Exact match |
| §6 (line 337) | Binary digits `49,981` (`[634,870]`) and `49,976` (`[456,1529]`); ternary `11,989` for both $L_+(3)$ and $L_-(3)$ | `L_+(3)` has `11989`, **`L_-(3)` has `11988`** | **Mismatch** (Minor M1) |
| §6 (line 338) | Discrepancies $D_N$ for $L_+(2), L_-(2), L_+(3)$ at $N=1000,2000,4000,8000$ | All 12 values identical | Exact match |
| §7 (line 369) | `3840` rational cases; equality for $3 \le b \le 6, k \le 5, N \le 10$ | `3840 (b, k, x, N) cases`, `largest ratio 1.0000`, equality confirmed | Exact match |
| §8–§9 (lines 18, 546) | `14,964 orbits` checked | `14964 values r in [1, b^k-2]` (triples $(b,k,r)$, not distinct orbits) | Wording slip (Minor M3) |
| §9 (lines 420–429) | 6-row table for $c+E_b$ at $N=3000$; deficits `0.174` and `0.112` | All 6 rows and deficits (`0.173616`, `0.111561`) match | Exact match |
| §10 (line 448) | `458` exceptions each for $\frac13+E_2$ and $\frac5{26}+E_3$; frequencies `0.49995/0.50005` and `0.33335/0.33330/0.33335`; run-length `0.50000`, `0.0099` | Frequencies and run-length (`0.00988`) match; **`458` is Markov-exceptional count, actual digit disagreements are `343` and `306`** (for $\lambda=1$ only) | Imprecise wording (Minor M2) |

---

## 2. Adversarial Proof Audit

### 2.1 Sub-track B3: Cubic character mod 7 & Theorem 5.3

- **§1 (Local structure, Lemmas 1.1–1.2):** Verified. Powers of $3 \bmod 7$ give $\chi = 1$ on $\{1,6\}$, $\omega$ on $\{3,4\}$, $\omega^2$ on $\{2,5\}$; $w_+ = \chi + \bar\chi$ and $w_- = (\chi-\bar\chi)/(i\sqrt 3)$ are even, zero-sum, and yield $c_+ = 2x - y$ and $c_- = y$ for $c = x + y\omega$. Local factors $1+\omega = e^{i\pi/3}$, $1+\omega^2 = e^{-i\pi/3}$, $1+\omega+\omega^2=0$, and the 6-entry table for $\varepsilon_\pm(t)$ are exact.
- **§2 (Value sets, Prop. 2.1, Lemma 2.2):** Verified. Every formula in Proposition 2.1 holds ($13 \equiv 6 \pmod 7$, $3, 11 \in \mathcal P'_+$, $2 \in \mathcal P'_-$). Lemma 2.2's reduction (stripping $7^{v_7}$, $p^{3q}$, and reducing $p^{3q+1}$ to $p$) and greedy prime assignment are airtight. In the script, `range(9)` for $(a,a')$ easily covers $\max_j S(j) = S(3) = 190$, and 12 kernel primes easily cover $\lfloor \log_2 20 \rfloor = 4$ factors.
- **§3 (Densities, Halász equidistribution, means, masses):**
  - **Theorem 3.1(1):** Elementary CRT + $E \to \infty$ truncation + tail $\sum_{p > y} p^{-2} \le 1/y$ is completely rigorous.
  - **Theorem 3.1(2):** $h_k(n) = \mathbf 1_{\mathcal S}(n) e^{i\pi k t(n)/3}$ is multiplicative with $|h_k| \le 1$. At $\theta = 0$, Mertens in progressions mod 7 gives $\beta_k = \frac13(1 + 2\cos(\pi k/3)) < 1$ for $k \not\equiv 0 \pmod 6$. At $\theta \ne 0$, partial summation from PNT in progressions with error $O(x/(\log x)^2)$ gives convergence of $\sum_{p\le x} \psi(p) p^{-1-i\theta}$ for every $\psi \bmod 7$ (including $\psi_0$, via $\int_{\log 2}^{\log x} u^{-1} e^{-i\theta u}\,du$), so $\sum_p (1 - \operatorname{Re} h_k(p) p^{-i\theta})/p = \infty$ for all $\theta \in \mathbb R$, and Halász's theorem unconditionally yields mean value $0$.
  - **Remark 3.2:** **FALSE rate for $k=2,4$** (see Major Finding J1 below).
  - **Proposition 3.3:** Hyperbola split at $y = \sqrt X$ with $B_+ = \|w_+\|_\infty = 2$, $B_- = \|w_-\|_\infty = 1$, and Abel summation $|\sum_{m > y} w(m)/m| \le 2B/(\lfloor y\rfloor + 1) < 2B/y$ gives $(4B + \|w\|_\infty)\sqrt X$, i.e. $10\sqrt X$ and $5\sqrt X$ for all $X \ge 1$. Log-sine DFT formula is exact.
  - **Proposition 3.4:** Wirsing applies to $|c|^2$ (prime mean $\frac13\cdot 4 + \frac23\cdot 1 = 2$, $(\nu+1)^2 \le 8(3/2)^\nu$). The injective map $\iota$ sending $t \in \{0,3\}$ to $3n$ on $\{n \in \mathcal S : 3 \nmid n\}$ gives $|c_-(\iota(n))| = |c(n)|$ and matching lower orders via Wirsing on $|c|^j \mathbf 1_{3\nmid n}$. Airtight.

#### Hostile Audit of Theorem 5.3 (Universal Character-Lambert Disjunctivity)

1. **Non-primitive $\Phi$ ($\Phi(\mathbb Z[\zeta_h]) = g\mathbb Z$ with $g \ge 2$, arbitrary sign, $\gcd(g, b) > 1$):**
   - **PASS.** Step 0 chooses $r_0, A_0$ with $\kappa = \Phi(c_\chi(A_0)(1+\chi(r_0))) \ne 0$ (valid for all nonprincipal $\chi$, primitive or imprimitive, since $1+\zeta_h \ne 0$ for $h \ge 3$ and $\{(1+\zeta_h)^j : 0 \le j < \varphi(h)\}$ is a $\mathbb Q$-basis of $\mathbb Q(\zeta_h)$; for $h=2$, $j=0$ gives $2\Phi(1) \ne 0$).
   - Writing $\kappa = b^f \kappa_1$ with $b \nmid \kappa_1$, Step 1 takes $b^e \ge |\kappa_1|$, $W' = W + e$, and $V_1 = \tau \kappa_1$ with $\tau \equiv 1 \pmod b$. Crucially, $\tau \equiv 1 \pmod b \implies V_1 \equiv \kappa_1 \not\equiv 0 \pmod b$ **even when $\gcd(\kappa_1, b) > 1$** (e.g., $b = 4, g = 2$).
   - The arithmetic progression $V_1 = (1 + kb)\kappa_1$ has step $b|\kappa_1| \le b^{e+1} = |I|$. For $\kappa_1 > 0$, $I = [M b^{e+1}, (M+1)b^{e+1})$ either contains $\kappa_1$ ($M=0$) or lies strictly to its right ($M \ge 1$); for $\kappa_1 < 0$, $I = [(Mb^e - b^{W'})b, ((M+1)b^e - b^{W'})b)$ either contains $\kappa_1$ ($M = b^W - 1$, where $-b^{e+1} < -b^e \le \kappa_1 < 0$) or lies strictly to its left ($M \le b^W - 2$, right endpoint $\le -b^{e+1} < \kappa_1$). In all cases, monotonicity with step $\le |I|$ guarantees a hit $V_1 \in I$, giving $b \nmid V_1$, $-b^{W'+1} \le V_1 < b^{W'+1}$, and $\lfloor V_1/b \rfloor \bmod b^{W'} \in [M b^e, (M+1)b^e)$ whose top $W$ digits spell $w$.
   - Lemma 5.1 is verified across every sign and boundary case (including $V_1 = -b^{W'+1}+1$, where $b^{W'} T_N = -b^{W'} + (1+\vartheta)/b \in (-b^{W'}, -b^{W'}+1)$ strictly, so $T_N \in (-1, 0)$ with zero boundary ambiguity).

2. **Single prime value position, zero block $L \approx 2\log_b \log Y$, Landau–Page (E1), and shifted-prime tail average:**
   - **PASS.** The proof avoids any delicate shifted-prime sieve or Shiu/Brun–Titchmarsh/Titchmarsh-divisor uniformity hypothesis in $q' = \exp(\Theta(\log\log Y \cdot \log\log\log Y))$ by averaging $R(u) = \sum_{k\ge 1} \tau(Au + L + k) b^{-k}$ over **all integers** $u \le Y$ in the progression $u \equiv a_0 \pmod{q'}$ using the completely elementary, completely uniform Lemma 5.2.
   - Paying one extra $\log Y$ factor in Markov's inequality is absorbed by setting $b^L \ge 5280\, C_\Phi \tau(A)\tau(q)(1 + \log 3AY)^2$, giving $L = 2\log_b \log Y + O_w(1)$.
   - The key uniformity trap in Lemma 5.2 is the $\tau(\gcd(Aa_0 + h, Aq'))$ factor, which could otherwise blow up like $(d+1)^s = e^{\Theta(L)}$. Step 2 & Step 5 kill this cleanly: since $Aa_0 + h \equiv p_j^{d-1} + (h-j) \equiv h - j \pmod{p_j}$ and $1 \le h - j \le L + k + W' + f$, choosing $p_j > P_0 = L + W' + f + \lceil 2s\log_2(d+1)\rceil + A_0 + \ell + q$ forces $E(L+k) = 0$ for all $k \le K_0 := P_0 - L - W' - f$, while for $k > K_0$ we have $(d+1)^s \le 2^{K_0/2} < 2^{k/2} \le b^{k/2}$, which is absorbed by $b^{-k}$ into the convergent series $\sum_{k\ge 1} k^2 2^{-k/2} < 48.05$.
   - All numerical constants in Steps 5–6 check out exactly: $4\sqrt 3 < 7$, $6(6 + 48.05) = 324.3 < 330$, and $\frac{2\cdot 330}{5280} = \frac{1}{8}$, leaving $\frac{Y}{8q'\log Y}$ for the $7\sqrt{AY}$ term (which is $o(Y^{2/3}/\log Y)$ since $q' \le Y^{1/3}$), yielding $\le \frac{Y}{4q'\log Y}$ bad integers against $\pi(Y; q', a_0) \ge \frac{Y}{2\varphi(q')\log Y} \ge \frac{Y}{2q'\log Y}$ primes from (E1).
   - For (E1) itself: $\log(q Q_\nu) \ll (\log\log Y)(\log\log\log Y) = o(\sqrt{\log Y})$ sits well inside $q' \le \min(Y^{1/3}, \exp(\frac{c_1}{2}\sqrt{\log Y}), T)$, and taking two disjoint prime families $\mathcal P_1, \mathcal P_2$ ensures $q_1 \mid qQ_1, qQ_2 \implies q_1 \mid q$, which is excluded for large $Y$ because the finitely many primitive real characters of conductor dividing $q$ are non-exceptional once $1/\sqrt{\log Y} < \min \delta_{\chi^*}$. (Small presentation gaps in Steps 4–7 are logged as Minor M4.)

3. **Irrationality of $L_\pm(b)$ as a corollary of disjunctivity (Corollary 5.4):**
   - **PASS** for the conclusion (a disjunctive real number is not eventually periodic in base $b$, hence irrational; $(\alpha, \beta) \ne (0,0) \implies \Phi(x+y\omega) = \alpha(2x-y)+\beta y \ne 0$).
   - **FAIL on one wording phrase** in the even-order $K_b$ remark (see Major Finding J2 below).

---

### 2.2 Sub-track B4: Complete radix-power tower classification

- **§7 (Theorem 7.1, $M_b = M_{b^k}$):** Verified. Subadditivity $\|my\| \le m\|y\|$ gives (i)–(iii) with exact constants, and (ii)'s constant $\frac{b^k - 1}{k(b-1)}$ is attained at $w = \frac{1}{b^k - 1}$ for all $b \ge 3$ and $N \ge 1$ (since $2b^{k-1} \le b^k - 1 \iff (b-2)b^{k-1} \ge 1$). Note that $w = b^{-k} \in M_b$ also attains exact equality in (ii) for all $b \ge 2$ (including $b = 2$) and all $N \ge 1$.
- **§8 (Theorem 8.1, $K_{b^k}/K_b \cong \mathbb Z/R\mathbb Z$):** Verified cleanly from Theorem 7.1 and Phase 19's $K_b = F_b + M_b$. $F_{b^k} \cap M_b = F_{b^k} \cap M_{b^k} = \mathbb Z$ follows immediately from $M_N(y; b^k) = \|y\|$ on $F_{b^k}$, giving both the isomorphism $\mathbb Z/R\mathbb Z \xrightarrow{\sim} K_{b^k}/K_b$ and uniqueness of $x = \frac{r}{b^k-1} + w$ ($0 \le r \le b^k - 2$, $w \in M_b$) with $x \in K_b \iff R \mid r$.
- **§9 (Lemma 9.1, Theorem 9.2, Proposition 9.3):**
  - **Lemma 9.1:** Exact formula $D(\mu) = \frac1d + \max_i z_i - \min_i z_i$ holds for all $0 \le y_1 < \dots < y_d < 1$, including $y_1 = 0$ and $d = 1$. Boundary domination ($z_j - z_0$ via $\min z \le z_d < 0$, and $z_{d+1} - z_i$ via $\max z \ge z_1 \ge -\frac1d$) and the strict bound $D(\mu) < 1$ for $d \ge 2$ are airtight. (Tiny wording slip at $y_1 = 0$: Minor M5.)
  - **Theorem 9.2:** (1)–(3) follow directly from `SharpTranslation` and $|\mu_N(I) - \mu_c(I)| \le \rho/N < d/N$. (4) is airtight: for $1 \le r \le b^k - 2$, every orbit point $r'/(b^k - 1)$ has $1 \le r' \le b^k - 2$ and $\gcd(b^\lambda, b^k - 1) = 1$, forcing $\eta_\lambda > 0$; $\|b^n w\| < \eta_\lambda$ prevents crossing any $b^{-\lambda}\mathbb Z$ boundary (including $0/1$), so the length-$\lambda$ digit blocks coincide, and Markov bounds exceptional shifts by $NM_N(w; b)/\eta_\lambda$.
  - **Proposition 9.3:** Pentagonal count $\le 2\sqrt{2N/3 + 1/36} \le 2\sqrt{2N/3} + 1/3 < 2\sqrt{2N/3} + 1$, and both pieces of the double sum contribute $\le 1$ per $m \le N$ and $\le (b-1)^{-2} \le 1$ for $m > N$, yielding $M_N(E_b; b) \le (2\sqrt{2N/3} + 2)/N$ cleanly.
- **§10 (Corollary 10.1):** All four parts verified.
  - (1) $r \ne 0 \implies$ period-$d$ frequencies miss at least one word of length $\lambda$ with $b^\lambda > d$; $r = 0 \implies D_N \to 1$.
  - (2) For $b \ge 3$: $r \ne 0$ gives constant digit $j$; $r = 0$ puts density-one shifts in $[0, 1/b) \cup [1-1/b, 1)$, excluding digit $1$ since $2/b \le 1 - 1/b \iff b \ge 3$.
  - (3) Alternating runs of lengths $1, 2, 3, \dots$ give $\|2^n x\| \le 2^{-\rho}$ away from $O(\rho\sqrt N)$ run boundaries, so $x \in M_2 = K_2$ (true since $F_2 = \mathbb Z \subseteq M_2$), and density of `1` is $\frac12 + O(N^{-1/2})$.
  - (4) $x \in K_{b^k} \setminus K_b \implies r \ne 0, d \ge 2$; digit frequencies are $n_j / k$, so simple normality forces $k = b n_j \implies b \mid k$. Conversely, repeating $(0\,1\,\cdots\,b-1)$ $k/b$ times has $1 \le r \le b^k - 2$, minimal period $b \ge 2$ (so $R \nmid r$), and equal digit counts $k/b$.
- **§11 (Schematic Lean 4 cores) & §13 (Scope hygiene):** Two **Major** findings identified below (J3 and J4).

---

## 3. Classified Findings & Actionable Fixes

### Critical Findings

None.

---

### Major Findings

#### [J1] False convergence rate for $k = 2, 4$ in Remark 3.2
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:139`
- **Issue:** Remark 3.2 claims that *"the split $t \equiv 0$ versus $t \not\equiv 0 \pmod 3$, which involves only $k = 2, 4$, converges at rate $(\log X)^{-1}$"*, invoking Selberg–Delange with $\beta_2 = 0$. However, the Selberg–Delange leading coefficient contains $1/\Gamma(\beta_k)$, which **vanishes** at $\beta_2 = 0$. In fact, $h_2(p) = \chi(p)$ for all $p \ne 7$, and computing local factors gives $h_2 = \chi * g_2$, where $g_2$ is multiplicative with $g_2(p) = 0$ ($p \ne 7$), $g_2(7^e) = 1$, and
  $$\sum_{e\ge 0} g_2(p^e) x^e = (1 - \omega x)\frac{1+\omega x}{1 - x^3} = \frac{1 - \omega^2 x^2}{1 - x^3} \quad (p \in \mathcal P'_+)$$
  (conjugate on $\mathcal P'_-$), and $g_2(p^e) = \mathbf 1_{e=0}$ on $p \equiv \pm 1 \pmod 7$. Thus $|g_2(d)| \le 1$ and $g_2$ is supported on $\{7^a m : m\text{ squarefull}\}$. Since $|\sum_{m \le Y} \chi(m)| \le 2$, we get the elementary bound
  $$\Bigl|\sum_{n \le X} h_2(n)\Bigr| \le 2 \sum_{d \le X} |g_2(d)| = O(X^{1/2})$$
  (and likewise for $h_4 = \overline{h_2}$). Consequently the split $t \equiv 0$ vs. $t \not\equiv 0 \pmod 3$ converges at rate $O(X^{-1/2})$, not $(\log X)^{-1}$ — which also explains why the script's observed error $|S_-/S_+ - 2/3|$ drops by $13\times$ between $X = 10^4$ ($0.0022$) and $X = 10^6$ ($0.00017$) rather than by $\approx 1.5\times$.
- **Fix:** Correct Remark 3.2 to note that at $k = 2, 4$ the Selberg–Delange leading term vanishes ($1/\Gamma(0) = 0$), and give the two-line factorization $h_2 = \chi * g_2 \implies \sum_{n\le X} h_2(n) = O(\sqrt X)$, yielding $O(X^{-1/2})$ convergence for the $t \equiv 0$ vs. $t \not\equiv 0 \pmod 3$ split.

#### [J2] Inaccurate algebraic claim in Corollary 5.4 ("integer combination" of Galois conjugates)
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:231`
- **Issue:** Corollary 5.4 justifies $F_b(\Phi \circ c_\chi) \in K_b$ for even-order $\chi$ by stating that *"$\Phi \circ c_\chi$ is an integer combination of the Galois conjugates of $c_\chi$"*. This is false in general: by nondegeneracy of the trace form on $\mathbb Q(\zeta_h)/\mathbb Q$, $\Phi(\alpha) = \sum_{\sigma \in \operatorname{Gal}(\mathbb Q(\zeta_h)/\mathbb Q)} \sigma(\gamma)\,\sigma(\alpha)$ with $\gamma$ in the inverse different $\mathfrak D_{\mathbb Q(\zeta_h)/\mathbb Q}^{-1}$, whose coefficients are generally non-integral (e.g., for $h = 4$ and $\Phi(x + yi) = x$, $\Phi \circ c_\chi = \frac12 c_\chi + \frac12 c_{\bar\chi}$ cannot be expressed with integer coefficients). The conclusion $F_b(\Phi \circ c_\chi) \in K_b$ still holds because Phase 21 Theorem 1.5 allows arbitrary $\lambda_j \in \mathbb C$ whenever the resulting sequence $a(n)$ is integer-valued.
- **Fix:** Replace *"is an integer combination of the Galois conjugates of $c_\chi$"* with *"is an integer-valued linear combination (over $\mathbb Q(\zeta_h)$) of the Galois conjugates of $c_\chi$, all of which have the same even order $h$"*.

#### [J3] Two soundness/elaboration bugs in the §11 schematic Lean 4 signatures
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:505` and `515–520`
- **Issue:**
  1. **Line 505 (`sampleDisc_sorted_eq`):** Writes `(y i - (i + 1 : ℝ) / d)` where `i : Fin d`. In Lean 4, `Fin d` has modular addition (`⟨d - 1, _⟩ + 1 = 0`) and no direct coercion `Fin d → ℝ`, so `(i + 1 : ℝ)` either fails to elaborate or wraps modulo `d`.
  2. **Lines 515–520 (`digit_window`):** Omits the summability/growth hypothesis on `a : ℕ → ℤ` from the theorem signature (mentioning it only in prose on line 525). Because Lean's `tsum` defaults to `0` on non-summable series, the stated signature is false as written for arbitrary `a : ℕ → ℤ` (if `a` is non-summable beyond `P`, `lambertValue b a = 0` and `tail b a P = 0` satisfy `htail` while the RHS `(V₁ / b) % b^W` can be nonzero).
- **Fix:**
  1. Replace `(i + 1 : ℝ) / d` on line 505 with `(((i : ℕ) + 1 : ℝ) / (d : ℝ))` (and `1 / (d : ℝ)`).
  2. Add an explicit summability hypothesis (e.g., `(ha : Summable fun n => (a (n + 1) : ℝ) / (b : ℝ) ^ (n + 1))` or `(ha : ∃ C : ℝ, ∀ n, |(a n : ℝ)| ≤ C * n)`) to `digit_window`, and optionally align `lambertValue` with the existing `CoefficientTransfer.coeffSeries`.

#### [J4] Scope hygiene violation: internal process language (`**Corrections to the brief.**`)
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:569–575` (and minor phrasing on line 556: `"No new Lean is part of this track."`)
- **Issue:** Section 13 contains a five-item `**Corrections to the brief.**` block framed around an internal task brief (*"not two thirds"*, *"not a maximal gap"*, etc.), violating standalone mathematical note hygiene.
- **Fix:** Replace `**Corrections to the brief.**` with a standalone heading (e.g., `**Key structural caveats.**` or fold each point into the relevant section) phrased purely in mathematical terms without referencing any brief; optionally tighten line 556 to `"Lean formalizations of the finite cores in §11 remain future work."`

---

### Minor Findings

#### [M1] Certified digit count for $L_-(3)$ reported as 11,989 instead of 11,988
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:337`
- **Issue:** States *"in the first 11,989 digits of $L_+(3)$ and of $L_-(3)$"*, whereas the script certifies `11,989` digits for $L_+(3)$ and `11,988` digits for $L_-(3)$.
- **Fix:** Write *"in the first 11,989 digits of $L_+(3)$ and the first 11,988 digits of $L_-(3)$"*.

#### [M2] Conflation of Markov-exceptional positions (458) with actual digit disagreements (343 / 306)
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:448` and `scripts/phase22_characters_quotient.py:1035–1041`
- **Issue:** Line 448 says *"blocks agree with those of $c$ except at 458 positions each"*, and script line 1041 prints *"digits agree with the block except at 458 of 20000 positions"*. In fact: (a) the script tests single digits ($\lambda = 1$), not general word blocks; (b) `exc = 458` counts positions failing the sufficient condition $\|b^n E_b\| < \eta$, whereas actual digit disagreements number `343` (for $\frac13 + E_2$) and `306` (for $\frac5{26} + E_3$).
- **Fix:** Report both counts cleanly (or clarify *"single digits agree with those of $c$ outside the 458 Markov-exceptional positions, with 343 and 306 actual disagreements respectively"*).

#### [M3] `"14,964 orbits"` vs. `14,964` $(b, k, r)$ triples
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:18, 546`
- **Issue:** Both lines say `14,964 orbits`, whereas `section_B4_quotient` tests all `14,964` triples $(b, k, r)$ with $2 \le b \le 6, 2 \le k \le 5, 1 \le r \le b^k - 2$ (distinct $r$ in the same cycle share one orbit).
- **Fix:** Replace `"14,964 orbits"` with `"14,964 triples $(b, k, r)$"` (matching the script output `"all 14964 values r in [1, b^k-2]"`).

#### [M4] Notation reuse and two tiny presentation gaps in the proof of Theorem 5.3
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:197, 282, 287, 305–307`
- **Issue:**
  1. Line 287 reuses $h = L + k$, clashing with $h = \operatorname{ord}\chi$ (lines 225, 272).
  2. Steps 4 and 7 implicitly need $m_0 + j \ge 1$ and $N = Au - W' - f - 1 \ge 0$. While this is actually automatic for $u \ge 1$ (since $N + 1 = Au - (W' + f) \equiv p_{-(W'+f)}^{d-1} \pmod{p_{-(W'+f)}^d}$ with $p_j > W' + f$ forces $N + 1 \ge p_j^{d-1} \ge 2$), it is not justified from $u > A$ alone when $A \le W' + f$.
  3. Lemma 5.2 is stated for integer $X \ge 1$ (line 197), while Step 7 sets $Y = X/A$ (possibly non-integer).
- **Fix:** Rename $h = L + k$ to $m = L + k$ (or $t = L + k$); restrict to $u > \max(A, W' + f)$ (or note why $N \ge 1$ is automatic); state Lemma 5.2 for real $X \ge 1$ or set $Y = \lfloor X/A \rfloor$ in Step 7.

#### [M5] Imprecise phrasing at $y_1 = 0$ in Lemma 9.1's proof
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:399`
- **Issue:** *"An interval containing exactly the points strictly between $y_i$ and $y_j$"* is slightly inaccurate when $y_1 = 0 = y_0$ and $i = 0$ (since $y_1$ is not strictly greater than $y_0$, yet $[0, y_j)$ contains $y_1, \dots, y_{j-1}$). The displayed formula and rest of the proof remain exact.
- **Fix:** Replace *"the points strictly between $y_i$ and $y_j$"* with *"the points $\{y_k : i < k < j\}$"*.

#### [M6] Loose attribution in Remark 5.4(2) ("Linnik's bound")
- **Location:** `notes/phase22/odd-characters-and-kernel-quotient.md:314`
- **Issue:** Labels $\pi(x; q', a) \gg x/(\varphi(q')\sqrt{q'}\log x)$ as *"Linnik's bound"*. Linnik's theorem concerns the least prime $p \ll q^L$; the $\sqrt{q'}$ loss in $\pi(x; q', a)$ comes from retaining a possible Siegel zero under Dirichlet's effective lower bound $1 - \beta_1 \gg q_1^{-1/2}(\log q_1)^{-2}$ (and even Siegel's ineffective bound $1 - \beta_1 \gg_\varepsilon q_1^{-\varepsilon}$ still loses $(q')^\varepsilon = e^{\Theta(\varepsilon L\log L)} \gg b^L$).
- **Fix:** Rephrase Remark 5.4(2) to *"Why a Siegel-zero loss is not enough"* (citing the effective Dirichlet/Page lower bound and Siegel's ineffective $q^{-\varepsilon}$ bound).

#### [M7] Small polish items (bounds, truncation ellipses, unused external input, script slack)
- **Locations & notes:**
  - `notes/phase22/odd-characters-and-kernel-quotient.md:12, 122`: Rounded digits followed by `...` (`-0.12159...` for `-0.121587...`, `0.50022...` for `0.500219...`); use truncated prefixes (`-0.12158...`, `0.50021...`) or drop the ellipsis.
  - `notes/phase22/odd-characters-and-kernel-quotient.md:80`: $|c_-(n)| \le \frac{2}{\sqrt 3}|c(n)|$ is true, though Lemma 1.2 immediately gives the sharper $|c_-(n)| \le |c(n)|$ (since $|\varepsilon_-(t)| \le 1$).
  - `notes/phase22/odd-characters-and-kernel-quotient.md:331`: *"The count is $o(X(\log X)^{-A})$"* — clarify *"This lower bound is $o(X(\log X)^{-A})$"* so it is not read as an upper bound on word occurrences.
  - `notes/phase22/odd-characters-and-kernel-quotient.md:369`: Note that $w = b^{-k} \in M_b$ gives exact equality in Theorem 7.1(ii) for **all** $b \ge 2$ (including $b = 2$) and all $N \ge 1$.
  - `notes/phase22/odd-characters-and-kernel-quotient.md:385`: Multiplication by $b$ on $K_{b^k}/K_b \cong \mathbb Z/R\mathbb Z$ has order **exactly** $k$ (not merely dividing $k$), since $R > b^j - 1$ for $1 \le j < k$.
  - `notes/phase22/odd-characters-and-kernel-quotient.md:562`: `Shiu (1980)` is listed under B3's external inputs, though B3's own proofs do not invoke Shiu (only Wirsing, Halász, PNT/Mertens, and (E1)); Shiu enters only transitively via Corollary 5.4's citation of Phase 21 Theorem 1.5.
  - `scripts/phase22_characters_quotient.py:685, 1012, 1042`: Line 685 truncates the tail bound at $k = 200$ (omitting $< 10^{-55}$, harmless; closed form is cleaner), and lines 1012/1042 assert the weaker $+4$ constant instead of Proposition 9.3's proved $+2$ constant (which also holds).


---

## Post-Repair Verification

- **Date:** 2026-11-26
- **Re-run command:** `python -B scripts/phase22_characters_quotient.py`
- **Result:** Exit code `0`, `10.7 s` script-reported (`10.858 s` wall clock), **`273,017` assertions passed** (matches `notes/phase22/odd-characters-and-kernel-quotient.md:574`).

> **Epistemic caveat:** This post-repair verification is an automated cross-model check and does **not** constitute independent human peer review.

### Repair-by-Repair Verification

| ID | Status | Verification Summary |
| --- | --- | --- |
| **[J1]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:139–171` and `scripts/phase22_characters_quotient.py:598–686`. The new proof of the $O(X^{-1/2})$ rate for $k = 2, 4$ is mathematically complete and verified line by line: $h_2(p) = \chi(p)$ ($p \ne 7$), local Dirichlet factorization $h_2 = \chi * g_2$ gives $g_2(7^e) = 1$, $g_2(p^e) = \mathbf 1_{e=0}$ ($p \equiv \pm 1 \pmod 7$), and $g_2(p^e) = 1, 0, -\omega^2$ ($e \equiv 0, 1, 2 \pmod 3$, $p \in \mathcal P'_+$; conjugate on $\mathcal P'_-$); every partial sum of $\chi \bmod 7$ has modulus $\in \{0, 1\}$ (verified explicitly in the script); $|g_2| \le 1$ supported on $7^a m$ ($m$ squarefull) yields $|\sum_{n\le X} h_2(n)| \le \#\{7^a m \le X : m\text{ squarefull}\} = O(\sqrt X)$; and orthogonality mod 3 gives $S_-(X) = \frac23 S_+(X) - \frac23\operatorname{Re}\sum_{n\le X} h_2(n)$, so $|S_-(X)/S_+(X) - 2/3| = O(X^{-1/2})$. The script checks $h_2 = \chi * g_2$ in $\mathbb Z[\omega]$ for $n \le 20{,}000$, and all 9 entries in the new table (`27.731, 242, 0.002175`; `75.020, 807, 0.000613`; `184.518, 2643, 0.000144`) match the script output verbatim. |
| **[J2]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:262`. Corollary 5.4 now accurately states that $\Phi \circ c_\chi$ is an integer-valued linear combination over $\mathbb Q(\zeta_h)$ of the Galois conjugates $c_{\chi^\sigma}$ via the trace form $\Phi(\alpha) = \sum_\sigma \sigma(\gamma)\sigma(\alpha)$ ($\gamma \in \mathfrak D^{-1}$), explicitly notes the non-integral $h = 4$ example $\frac12 c_\chi + \frac12 c_{\bar\chi}$, and cites Phase 21 Theorem 1.5's allowance of arbitrary complex coefficients. |
| **[J3]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:534–566`. (1) `sampleDisc_sorted_eq` (lines 536–537) now uses `1 / (d : ℝ)` and `(((i : ℕ) + 1 : ℕ) : ℝ) / (d : ℝ)`, eliminating the `Fin d` modular-addition/coercion bug. (2) `lambertValue` and `tail` are explicitly defined as `tsum`s (lines 548–551, cross-referencing `CoefficientTransfer.coeffSeries`), and `digit_window` (line 556) includes `(ha : ∃ C : ℝ, ∀ n, |(a n : ℝ)| ≤ C * (n + 1))`, which guarantees summability of both series without forcing `a 0 = 0` and holds for all divisor-bounded sequences. |
| **[J4]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:598, 611–617`. All `"brief"` process language has been removed; `**Corrections to the brief.**` is replaced by standalone `**Structural remarks.**`, and line 598 reads *"Lean formalizations of the finite cores in §11 remain future work."* |
| **[M1]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:368` now reports `11,989` certified digits for $L_+(3)$ and `11,988` for $L_-(3)$, matching the script output. |
| **[M2]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:479` and `scripts/phase22_characters_quotient.py:1129–1145`. Both note and script now specify single digits ($\lambda = 1$) and clearly separate the `458` Markov-exceptional positions from the `343` ($\frac13 + E_2$) and `306` ($\frac5{26} + E_3$) actual digit disagreements, asserting `dis <= exc <= (2 * sqrt(2 * Nd / 3) + 2) / eta`. |
| **[M3]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:18, 588` and `scripts/phase22_characters_quotient.py:1056` now accurately report `14,964 triples (b, k, r)`. |
| **[M4]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:228, 318–324, 336–338`. Lemma 5.2 is stated for real $X \ge 1$; Step 5 renames the shift to $H = L + k$ (no clash); Steps 6–7 restrict to $u \in (\max(A, W'+f+1), Y]$ (subtracting $A + W' + f + 2$), giving $N = Au - W' - f - 1 \ge u - W' - f - 1 \ge 1$ explicitly. |
| **[M5]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:430` now phrases Lemma 9.1's deficit case by index: *"the points $\{y_m : i < m < j\}$"*. |
| **[M6]** | **Verified fixed** | `notes/phase22/odd-characters-and-kernel-quotient.md:345` replaces the Linnik attribution with *"Why a Siegel-zero loss is not enough"*, citing both $1 - \beta_1 \gg q_1^{-1/2}(\log q_1)^{-2}$ and Siegel's ineffective $q_1^{-\varepsilon}$. |
| **[M7]** | **Verified fixed** | Truncation ellipses (`-0.12158...`, `0.50021...`, lines 12, 122); sharper $|c_-| \le |c|$ (lines 80, 190); `"This lower bound is o(X(log X)^{-A})"` (§6 line 362; the one-line summary table on line 15 still says `"the word count is..."` as shorthand, non-blocking); $w = b^{-k} \in M_b$ equality in Theorem 7.1(ii) added and checked for $2 \le b \le 6$ (line 400; script lines 973–982); exact order $k$ of $b \bmod R$ proved and checked (line 416; script line 1047); Shiu scope clarified (lines 604, 608); closed-form tail bound in Lemma 5.1 check (script lines 774–776, exact algebra verified) and tightened $+2$ constant in Proposition 9.3 checks (script lines 1111, 1145). |

### Updated Verdicts

| Sub-track | Post-Repair Verdict | Remaining Issues |
| --- | --- | --- |
| **B3** | **Accept** | 0 Critical, 0 Major, 0 blocking Minor |
| **B4** | **Accept** | 0 Critical, 0 Major, 0 blocking Minor |
