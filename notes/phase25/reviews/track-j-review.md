# Phase 25 Addendum Track J — cross-provider adversarial referee review

**Audited files.** [`notes/phase25/grh-lambert-windows.md`](../grh-lambert-windows.md) (658 lines) and [`scripts/phase25_grh_windows.py`](../../../scripts/phase25_grh_windows.py) (863 lines), authored by Claude Opus 5.5, on branch `research/phase-25-carry-correlations`.

**Reviewer.** Gemini 4 Neon (Google), a different provider from the author. The audit was strictly read-only on all existing repository files: no audited file was modified, archived Paper VI (`papers/06-multiplicative-lambert/`) was left completely untouched, no WSL commands were used, and nothing was committed.

> **Cross-model review is not independent human peer review.** This report is an adversarial machine reading by a model from another provider. It does not replace independent refereeing by human specialists in analytic number theory, sieve theory, or uniform distribution. None of its conclusions may be used to change a benchmark status, and conditional results never change a benchmark status.

## Verdict: **ACCEPT WITH MINOR POLISH**

| Severity | Count |
| --- | --- |
| Critical | 0 |
| Major | 0 |
| Minor | 11 |

**Executive assessment.** Every headline result across Addenda D, E, and F survives adversarial scrutiny with **zero Critical and zero Major findings**:

- **Audit D (Paper VI under GRH($q_0$) and Window Discrepancy):** The explicit-formula deduction of Theorem A (including the exact signs of $r(\chi,x)$ and $b(\chi)$ and the low-zero cancellation), Lemma A.1, Corollaries A.3 and A.2, and the line-by-line audit of `papers/06-multiplicative-lambert/paper.tex`'s `prop:planting` at $\nu_* = 1/2$ are mathematically sound. There is genuinely no hidden $a > 7/12$ requirement anywhere in `prop:planting` or §6. The new window discrepancy Proposition C and window translation Corollary C.2 correctly apply the kernel-verified Lean declarations (`one_sub_discrepancy_le_one_bits`, `one_sub_discrepancy_ge_of_separated_mass`, `sharp_translation_isGreatest`) to $y = \{2^N L\}$. Archived Paper VI has zero modifications (`git diff papers/06-multiplicative-lambert/` is empty).
- **Audit E (`GF-22` Moving Windows under Dirichlet GRH, Unconditional Byproduct, and Additivity Necessity):** Lemma E.2 (short-interval divisor sum in a progression), the factor-by-factor coprimality and $\tau(g_k)$ accounting, every numerical constant in Step 6′ ($4\sqrt 3 < 7$, $2(2 + 4 + 3\sqrt 2) = 20.485\dots < 21$, $42/512 < 1/8$), the carry-isolation verification against GF-22 Lemma 5.1, the unconditional three-family Landau–Page argument (Proposition D.2), and the non-additive $\Phi_{\rm ind}$ counterexamples (Proposition E, refuting the HEAD `04969b9` registry wording still displayed in `docs/results.md:3910`) are all mathematically sound.
- **Audit F (Mira Cult Short-Window Exponent Dependency Audit):** Lemma F.1's summed GRH error $\le 2C_0 Q\sqrt{2x}\log^2(4Qx)$ gives every level $0 < \rho < \vartheta - 1/2$ with a power saving, the dependency audit of P13 / P13-R confirms that every step runs for arbitrary fixed $\rho > 0$ (down to $a > 1/2$), the explanation of why Kumchev's $0.53$ minorant does not transfer is accurate, the Lean Fourier transfer (`erdosBorwein_window_fourier`) matches verbatim, and provenance / residual verification caveats from P13 are strictly preserved.
- **Evidence discipline:** Every GRH-dependent deduction (Theorem A, Corollaries A.2–A.3, Theorem B, Proposition C at $a > 1/2$, Theorem D, Lemma F.1, Audit conclusion F, and Appendix A `lem:grhfixed`/`thm:grh`) is explicitly and consistently labeled `Conditional` with the exact GRH hypothesis named, with zero overclaiming and zero benchmark status changes.

Eleven **Minor** findings are itemized below (exact/float tagging leak and column mislabeling in S6, two harmless constant/exponent slips in §3.3, one constant slip in Proposition C's upper bound when $\kappa > \log 2$, one constant slack in Proposition D.2's $\psi \to \pi$ step, Corollary A.3/A.2 numbering inversion, missing domain hypotheses $X \ge 2$ / $x \ge 4$, S5 gcd count 2,424 vs 4,000, a missing column in §5's table row 5, and minor wording polish). All eleven have concise one-line fixes.

---

## 1. Verifier run, exact vs floating-point separation, and script/note agreement

`python -B scripts/phase25_grh_windows.py` was executed from the worktree root on Windows. It exited with code **`0`** in **2.6 s** and passed **`ALL 86570 CHECKS PASSED`** (`exact 77462, cert 72, num 9036`), matching note §7 (line 506) verbatim.

**Exact vs floating-point separation.** The script declares three separate counters (`exact`, `cert`, `num`) and maintains clean separation across S1–S5 and S7–S10:
- S1, S3, S5, S7, S10 use pure `int` and `fractions.Fraction` arithmetic for every `"exact"` assertion. In S5 (`scripts/phase25_grh_windows.py:449`), `rhs_lower` uses `isqrt(X1)` and outward-rounded `ln_lower_int(X1)` (12-decimal `LN2_LO`), giving a rigorous rational lower bound on Lemma E.2's right-hand side.
- S8 (`certified_word_at`, lines 676–694) uses exact `int`/`Fraction` arithmetic throughout (Python 3 `math.floor` on `Fraction` invokes exact `Fraction.__floor__()`), deterministic 13-base Miller–Rabin (valid below $3.317 \times 10^{24}$; tested primes are $\approx 10^{17}$ and $\approx 5.9 \times 10^{15}$), and a verified tail bound: since $|c_+(m)| \le 2\tau(m) \le 4\sqrt m$, splitting $\sum_{j \ge 1}\sqrt{n+K+j}\,2^{-j}$ at $j = n - K \ge K + 10 \ge 10$ gives at most $4(\lfloor\sqrt{2n}\rfloor + 1) + 8\sum_{j \ge 11} j 2^{-j} = 4(\lfloor\sqrt{2n}\rfloor + 1) + 3/32 < 4(\lfloor\sqrt{2n}\rfloor + 1) + 1$.
- S9 (`s9_window_discrepancy`, lines 752–789) certifies $\ge 12{,}000$ binary digits of $L_{\chi_4}$ using the exact tail enclosure $[0, K + 2]$ (from $0 \le c_{\chi_4}(n) \le n$), computes the exact rational extreme discrepancy $\frac1H + \max_i g_i - \min_i g_i$ (valid with ties and for all $y_i \in [0, 1)$, since $\max_i g_i \ge 1 - y_{H-1} > 0$ and $\min_i g_i - 1/H \le -y_0 \le 0$), and pads the truncation error $2^{-32}$ with `slack = Fraction(2, 1 << 32) = 2^{-31}`.
- S2 (`num` checks) and S4 (`num` checks) are explicitly tagged `"num"` and described as finite measurements only.
- **One exact/float separation leak found (m1):** In S6 (`scripts/phase25_grh_windows.py:515-531`), `holds[a]` evaluates an *illustrative* (GRH constant $= 1$) inequality in floating-point arithmetic (`float(a)`, `math.log10(float(lnqN_hi))`), yet lines 530–531 assert `not by_E[100][a]` and `by_E[10**6][a]` under `check("exact", ...)` (and note line 515 calls them "The exact checks", contradicting note §6 line 497 which rightly puts the illustrative constant-1 check in `Numerical`). Moreover, `holds[a]` uses upper bounds (`dA`, `dq`, `lnqN_hi`, `+1`) so it is a *sufficient* condition for the inequality to hold; negating it at $E = 100$ is not formally a proof of failure (even though failure is obvious since $q' > 10^{270} > 10^{100}$).

**Independent verification and script/note agreement.** Independent read-only Python checks verified every numerical claim and certificate in the note:
- **S1:** Counts `1002, 942, 835` match note lines 246 and 510 (note `Fraction(1)` is duplicated once in `grid` for $\nu_* \in \{1/2, 53/100\}$; **m11**).
- **S2:** Independent fixed-point iteration for $(\nu - 1/2)L = 2\ln L$ gives $\log_{10} X = 632.6800, 93.2802, 49.3273, 39.0844, 11.3323$ for $\nu = 0.51, 0.55, 7/12, 0.6, 0.75$, matching note lines 236 and 511 (`632.7, 93.3, 49.3, 39.1, 11.3`).
- **S3 & S4:** `236` jump points, max ratio `0.00570` (`0.0057` in note line 513), and min $(\mathrm P_{0.55})$ ratio `1.579` match verbatim.
- **S5:** `2556` instances and max ratio `0.9814` (`0.981` in note line 344) match; however, the coprime gcd loop (`scripts/phase25_grh_windows.py:454-463`) skips non-coprime pairs and executes **`2,424`** checks, not `4000` as stated in note line 514 (**m8**).
- **S6:** All values of $L, s$, largest kill prime, and `digits(q')` match verbatim. However, note lines 326 and 517–523 mislabel the script's column `digits(q')/log10 N` (`len(str(q')) / E`) as `$\log q'/\log N$`: true $\log_{10}(q')/E$ is `22.097` ($E=10$), **`2.701`** vs note `2.71` ($E=100$), `0.3397` ($E=1000$), **`0.04042`** vs note `0.0405` ($E=10^4$), and **`0.0005564`** vs note `0.000557` ($E=10^6$) (**m1**).
- **S7:** Independent checks confirm first occurrences of `111` for $\chi_{-4}$ at 1-based position $8$ ($8, 9, 10$ are sums of two squares) and `1^7` for cubic mod 7 at 1-based position $37$.
- **S8:** Independent factorization and $p$-adic valuation checks confirmed both certified starts:
  - `00`: $n = 100000002495588146 \in [10^{17}, 10^{17} + 15848931925)$, $u = 100000002495588149$ prime $\equiv 3 \pmod 7$, $A = 1$, $v_p(m_0 + j) = 2$ for $(j,p) \in \{(-2,3),(-1,2),(1,5),(2,11)\}$, leading coefficients $c_+(n+1\dots n+6) = [0, 0, 1, 0, 0, 4]$.
  - `01`: $n = 1000000495022262146 \in [10^{18}, 10^{18} + 3981071705535)$, $u = 5917162692439421$ prime $\equiv 3 \pmod 7$, $A = 169$, $v_p(m_0 + j) = 2$ for all four kills, leading coefficients $[0, 0, 3, 0, 0, 2]$.
- **S9 & S10:** All printed values and parameter identities match.

---

## 2. Audit D: Paper VI under Dirichlet GRH and Window Discrepancy (§2.1–§2.4, Appendix A)

### 2.1 Theorem A, Lemma A.1, Corollaries A.3 and A.2 (§2.1–§2.2)

- **GRH($q$) equivalence (line 5):** Correct. By the Artin $L$-function factorization for the abelian extension $\mathbb Q(\zeta_q)/\mathbb Q$, $\zeta_{\mathbb Q(\zeta_q)}(s) = \prod_{\chi \bmod q} L(s, \chi^*)$ holds for every $q \ge 1$ (including $q \equiv 2 \pmod 4$, where no primitive character of conductor $q$ exists and the inducing primitive characters match the characters of $\operatorname{Gal}(\mathbb Q(\zeta_q)/\mathbb Q)$).
- **Explicit formula and signs (§2.1, lines 165–213):** Every step was verified from scratch:
  - Step 2 (imprimitive reduction, line 170): $\sum_{p \mid q}\sum_{p^k \le x}\log p \le \omega(q)\log x \le 2\log q\log x$ holds for all $q \ge 1$ since $2^{\omega(q)} \le q \implies \omega(q) \le (\log q)/\log 2 < 1.45\log q$.
  - Step 3 (residues and $b(\chi)$, lines 176–184): For primitive $\chi \bmod q^*$ ($q^* > 1$) of parity $\mathfrak a \in \{0, 1\}$, the trivial zeros lie at $s = \mathfrak a - 2m$ ($m \ge 1$) plus a simple zero at $s = 0$ when $\mathfrak a = 0$. The residue of $-\frac{L'}{L}(s,\chi)\frac{x^s}{s}$ at $s = \mathfrak a - 2m$ is $+x^{\mathfrak a - 2m}/(2m - \mathfrak a)$, and at $s = 0$ is $-(1 - \mathfrak a)\log x - b(\chi)$. Subtracting $\frac{L'}{L}(2,\chi) = O(1)$ via the Hadamard product gives $b(\chi) = -\sum_{|\gamma|<1}\rho^{-1} + O(\log q^*)$ for both parities. Every sign in lines 182–183 and the cancellation $-\sum_{|\gamma|<T} x^\rho/\rho - b(\chi) = -\sum_{1 \le |\gamma| < T} x^\rho/\rho - \sum_{|\gamma|<1}(x^\rho - 1)/\rho + O(\log q^*)$ in line 189 are exact. The Perron discontinuity term $\min(1, x/(T\langle x \rangle))\log x$ is uniformly $O(\log x)$.
  - Step 4 (GRH bound, lines 186–204): Under GRH, $|\rho| \ge 1/2 \implies |(x^\rho - 1)/\rho| \le 2(\sqrt x + 1)$, the trivial-zero sum is $\le \frac12\log 3 < 0.55 < 2$ for $x \ge 2$, the harmonic zero sum $\sum_{1 \le |\gamma| < T} |\gamma|^{-1} \ll \log^2(q^*T)$, and $T = \sqrt x \in [2, x]$ (for $x \ge 4$) satisfies $\log(q^*xT) \le \frac32\log(q^*x)$ for all $q^* \ge 1$.
  - Step 5 (lines 206–212): $2\log q\log x \le 2\sqrt x\log^2(qx)$ for all $q \ge 1, x \ge 2$. Subtracting at $X+H$ and $X$ yields line 93 (add the missing hypothesis $X \ge 2$ on line 90; **m7**).
- **Lemma A.1 and Corollary A.3 (lines 96–106, 216–224):** Sound. $P(x) \le \lfloor\sqrt x\rfloor + \lfloor x^{1/3}\rfloor\lfloor\log_2 x\rfloor$ is exact; for $X \ge 2, q \ge 1$, $\log(2qX) \ge \log 4 > 1$ so $\sqrt X\log X \le \sqrt X\log^2(2qX)$; partial summation $\int_{X^+}^{X+H} d\theta(t)/\log t$ has exact signs and $\int_X^{X+H} dt/(t\log^2 t) \le 1/\log X$. Note Theorem A applies directly for all $t \in [X, X+H]$ (including $0 \le t - X < 1$), so $|\Delta(t)| \le C_2\sqrt X\log^2(2qX)$ holds across the entire integration interval.
- **Corollary A.2 (lines 108–114, 226–236):** Sound. Uses **only** GRH($q_0$) (finitely many primitive characters of conductor dividing $q_0$: $\zeta(s)$ and $L(s, \chi_{-4})$ for $q_0 = 4$; the 4 $L$-functions mod $5$ for `ex:quarter`). For $X \ge 4$, $\log(2X) \le \frac32\log X$, and $\frac34 \cdot \frac23 = \frac12$ gives $c_P = 1/(2\varphi(q_0))$. Minor numbering inversion: Corollary A.3 is stated and proved before Corollary A.2 (**m6**).

### 2.2 Step-by-step audit of Paper VI `prop:planting` at $\nu_* = 1/2$ (Theorem B, §2.3)

Every line of `papers/06-multiplicative-lambert/paper.tex:775-916` was audited independently at $\nu_* = 1/2$ for $1/2 < a \le 1$:
1. **Statement compatibility (`paper.tex:776`):** `prop:planting` explicitly allows $1/2 \le \nu_* < 1$.
2. **Parameters (`paper.tex:787-790`):** $\theta = \min\{1/4, (a - 1/2)/2\} \in (0, 1/4]$; $a - \theta \ge (a + 1/2)/2 > 1/2$; $\nu = \frac12(1/2 + a - \theta) \in (1/2, a - \theta)$; $\beta = \frac12 + \frac{1}{4(a-\theta)} \in \left(\frac{1}{2(a-\theta)}, 1\right)$ so $(a-\theta)\beta = \frac{a-\theta}{2} + \frac14 > \frac12$.
3. **Small factors (`lem:small`, `paper.tex:647-671`):** Uses only $0 < \theta < 1/2$, (H1), and Mertens. Holds for $\theta \le 1/4$.
4. **Prime interval (`eq:Pm`, `paper.tex:795-808`):** $X = (N+j_0-1)/b \gg_w N^{1-\theta}$ (with $1-\theta \ge 3/4 > 1/2 \ge \theta$, so $p > X > b$ and $p > 2\sqrt{3N}$), $Y = H/b < X$ (since $H \le N < N + j_0 - 1$), $Y \gg_w N^{a-\theta} \ge (3N)^\nu \ge (X+Y)^\nu$. Uses only $(\mathrm P_\nu)$ at $q_0$ (supplied by Corollary A.2 under GRH($q_0$)).
5. **Nearby vanishing (I2) (`paper.tex:816-852`):** Selberg sieve `lem:selberg` on $(X, X+Y]$ with $z = Y^{1/4}$, $w_{\text{sieve}} = Y^{1/32} > z_0 = (\log N)^2$, remainder $Y^{1/2}(1+\log Y)^2$, and square-divisible error $Y/z_0 + z$. All require only $Y \ge N^c$ for some fixed $c > 0$; here $a - \theta > 1/2$.
6. **Far tail (I3) (`paper.tex:854-879`):** Brun–Titchmarsh (`thm:mv`) requires $d' \le 2\sqrt N \le Y^\beta < Y$, which holds because $(a-\theta)\beta > 1/2$, and $d' \le 2\sqrt N < X$ rules out non-coprime classes. For $j > N$, $|\mathcal P_m| \le Y + 1$ gives $O(YN2^{-N})$.
7. **Counting, injectivity, and §6 deduction (`paper.tex:881-916`):** Independent of $a$ and $\nu_*$; `prop:upper` holds unconditionally for all $0 < a \le 1$.

**Conclusion:** Zero hidden $a > 7/12$ requirement exists anywhere in Paper VI's planting proposition or §6. Remark B.1's observation that the far-tail step also hits a wall at $a = 1/2$ ($\theta \to 0$, $\beta \to 1$) is accurate.

### 2.3 Proposition C and Corollary C.2 (§2.4)

- **Lean declaration verification:** Checked directly against `NormalityChecker/Phase17DiscrepancyBounds.lean:98-101, 123-127` and `NormalityChecker/SharpTranslation.lean:386-388`. All three declarations hold for every real number; substituting $y = \{2^N L\}$ (where $\{2^n y\} = \{2^{n+N} L\} = x_{N+n}$) and $z = 2^N L$ is exact.
- **Upper bound (line 279):** Sound up to one minor constant slip: for $\ell = \lceil \kappa\log_2\log N \rceil$, line 279 writes $(\ell - 1)/H \le \log\log N / N^a$, which is false when $\kappa > \log 2 \approx 0.693$ (e.g., `ex:quarter`, $\kappa = 3/4$, where $\kappa/\log 2 \approx 1.082 > 1$). Replacing `<=` by `\le (\kappa/\log 2)\log\log N / N^a \ll \log\log N / N^a` fixes it (**m4**).
- **Lower bound (lines 281–290):** Every step 1–8 was checked:
  - $R = \lfloor \frac{\kappa}{2}\log_2\log N \rfloor < \frac{1}{2\log 2}\log\log N < \log\log N$, so $C_R = 1$ holds for every $\kappa \in (0, 1)$.
  - For $\nu_* < a' < a$, $N' = N + R$ and $H' = H - R$ satisfy $N'^{a'} \le H' \le N'$ for large $N$, and $n \in [N+R, N+H) \implies n - r \in [N, N+H)$ for $1 \le r \le R$.
  - `lem:isolated` for $w = 1$ gives $x_n \in [3/4, 7/8)$, $x_{n-r} \in [\frac34 2^{-R}, \frac7{16}) \subseteq [3\varepsilon, 1/2)$ with $\varepsilon = 2^{-R}/4 \le 1/8 \le 1/6$; pairwise disjointness of $\{n-1,\dots,n-R\}$ holds identically to Paper VI §7.
  - $\Delta = R|\mathcal G|/H \ll_a (\log\log N)/(\log N)^\kappa = o((\log N)^{-\kappa/2}) \le \varepsilon$, and Markov via `lem:oddpart`(c) and `lem:windows` gives $F_{N,H}(0, \varepsilon) \ge 1 - O_a((\log N)^{-\kappa/2}) \ge 1/2 \ge \Delta$.
  - `one_sub_discrepancy_ge_of_separated_mass` yields $1 - D_{N,H}(L) \ge \Delta \gg_a (\log\log N)/(\log N)^\kappa$.
- **Corollary C.2 (lines 132–138, 294–296):** Sound. As $x$ ranges over $\mathbb R$, $y = 2^N x$ ranges over $\mathbb R$ with $y = 0 \iff x = 0$, so `sharp_translation_isGreatest` applies directly.
- **Appendix A (lines 562–642):** Confirmed unapplied (`git diff papers/06-multiplicative-lambert/` is empty). Minor polish items noted in **m10**.

---

## 3. Audit E: `GF-22` Moving Windows under Dirichlet GRH, Unconditional Byproduct, and Additivity (§2.5–§2.7)

### 3.1 Theorem D: Short-interval divisor bound, Markov tail, and moving-window reconstruction (§2.5)

Every factor, constant, and carry-isolation step was independently re-derived:

1. **Deterministic kills and parameter sizing (Steps 0, 1, 2′, 4; lines 302–318):**
   - $A = \ell^{\tau - 1} A_0$ is coprime to $q$. Since $p_j > P_0 = L + W' + f + \lceil 2s\log_2(d+1) \rceil + A_0 + \ell + q$, we have $p_j > \max(A_0, \ell, q, |j|)$, so $A, q, Q = \prod_{j \in J} p_j^d$ are **pairwise coprime**, $A$ is invertible modulo $p_j^d$, and $p_j \nmid j$, ensuring $\gcd(a_0, q') = 1$ and $v_{p_j}(Au + j) = d - 1$ (hence $c_\Phi(Au+j) = 0$) for **every** integer $u \equiv a_0 \pmod{q'}$. Zero exceptional positions.
   - By PNT modulo the fixed $q$, $p_{\max} \ll_{q,h} s\log s$ with $s = W' + f + L = (2/\log b)\log\log N + O_w(1)$, giving $\log q' \le (d + o(1)) s\log s \sim \frac{2d}{\log b}\log\log N \cdot \log\log\log N$. Hence $q' = N^{o(1)}$, and the final count $H/(4Aq'\log 3N) \ge H\exp(-C_w\log\log N \cdot \log\log\log N)$ holds with $C_w$ independent of $a$ (indeed, for sufficiently large $N_0(w,a)$, any constant exceeding $2d/\log b$ suffices).
2. **Prime count on $[U, U+Y)$ (Step 5′, lines 320–326):**
   - $U = (N + W' + f + 1)/A$, $Y = H/A$, so $n(u) = Au - W' - f - 1 \in [N, N+H) \iff u \in [U, U+Y)$, and $Y < U$ always since $H \le N$.
   - Applying Corollary A.3's $\theta$-bound on $(U, U + Y - 1] \subset [U, U + Y)$ and dividing by $\log(2U)$ gives $|\mathcal U| \ge \frac{Y-1}{\varphi(q')\log 2U} - C_2\frac{\sqrt U \log^2(2q'U)}{\log U}$ with the exact constant $C_2$ of Corollary A.3 (worth stating the $(U, U+Y-1]$ step explicitly; **m11**). Since $q' = N^{o(1)}$ and $a > 1/2$, this is $\ge Y/(2\varphi(q')\log 2U)$ for $N \ge N_0(w, a)$.
3. **Lemma E.2 (short-interval divisor bound in progressions; lines 336–342):**
   - **Verified rigorously.** For $X_0 \ge 0$, $Z \ge 1$, $X_1 = X_0 + Z$, every $m \in (X_0, X_1]$ satisfies $m \ge 1$ and $\tau(m) \le 2\sum_{d \le \sqrt{X_1}} \mathbf 1_{d \mid m}$. Compatibility of $m \equiv c \pmod D$ and $d \mid m$ forces $e = \gcd(d, D) \mid g = \gcd(c, D)$ and gives a unique class modulo $dD/e$, which has at most $\lfloor Z e/(dD) \rfloor + 1 \le Ze/(dD) + 1$ integers in $(X_0, X_0 + Z]$ (valid for all real $X_0 \ge 0, Z \ge 1$ and also when $c = 0$, $g = D$). The $+1$ terms sum to $2\lfloor\sqrt{X_1}\rfloor \le 2\sqrt{X_1}$, and writing $d = e d'$ yields $\frac{2Z}{D}\sum_{e \mid g}\sum_{1 \le d' \le \sqrt{X_1}/e} \frac{1}{d'} \le \frac{2Z}{D}\tau(g)(1 + \frac12\log X_1)$.
4. **Markov tail step (Step 6′, lines 328–356) — every constant re-checked:**
   - For each $k \ge 1$, $m = Au + L + k$ runs injectively over the class $Aa_0 + L + k \bmod Aq'$ in the integer interval $(X_0, X_0 + H]$ with $X_0 = N + W' + f + L + k \ge 0$, $Z = H = AY$, and right endpoint $X_1 = X_0 + H < X_k = N + W' + f + 1 + L + k + H \le 3Nk$ (valid for all $k \ge 1$ once $N \ge W' + f + 2 + L$).
   - By pairwise coprimality of $A, q, Q$, $g_k = \gcd(Aa_0 + L + k, Aq') = \gcd(L + k, A)\gcd(Aa_0 + L + k, q)\gcd(Aa_0 + L + k, Q)$, giving $\tau(g_k) \le \tau(A)\tau(q)(d+1)^{E(L+k)}$. Because $Aa_0 + L + k \equiv p_j^{d-1} + (L + k - j) \pmod{p_j^d}$ with $1 \le k \le L + k - j \le L + k + W' + f$, divisibility $p_j \mid Aa_0 + L + k$ requires $p_j \le L + k + W' + f$, hence $k > P_0 - L - W' - f = K_0 > 2s\log_2(d+1)$. Thus $E(L+k) = 0$ for $k \le K_0$ and $(d+1)^s < 2^{k/2} \le b^{k/2}$ for $k \ge K_0$.
   - **Additive error:** $\sum_{k \ge 1} 2\sqrt{3N}\,k\,b^{-k} \le 2\sqrt{3N}\sum_{k \ge 1} k 2^{-k} = 4\sqrt 3\sqrt N = 6.9282\dots\sqrt N < 7\sqrt N$. Exact!
   - **Main term:** Using $1 + \frac12\log(3Nk) \le (1 + \log 3N)k$ (valid for all $k \ge 1, N \ge 1$) and $Z/(Aq') = Y/q'$ (crucially avoiding GF-22's prefix factor $3k$, which reduces $k^2$ to $k$ and $330$ to $21$):
     $$2\sum_{k < K_0} k 2^{-k} + 2\sum_{k \ge K_0} k 2^{-k/2} \le 2(2) + 2(4 + 3\sqrt 2) = 12 + 6\sqrt 2 = 20.48528\dots < 21.$$
     Exact!
   - **Markov bound (line 353):** With $b^L \ge K_* C_\Phi \tau(A)\tau(q)(1+\log 6AN)^2$ and $K_* = 512$:
     - First term: $\frac{2C_\Phi}{b^L} \cdot 7\sqrt N \le \frac{14}{512}\sqrt N < \sqrt N \le \frac{Y}{8\varphi(q')\log 2U}$ for $N \ge N_0(w,a)$ because $Y/\varphi(q') \ge N^{a - o(1)}$ and $a > 1/2$.
     - Second term: $\frac{42}{K_*}\frac{Y}{q'}\frac{1+\log 3N}{(1+\log 6AN)^2} \le \frac{42}{512}\frac{Y}{q'(1+\log 6AN)} \le \frac{Y}{8q'\log 2U}$ since $2U \le 6AN$ and $42 \cdot 8 = 336 \le 512$.
   - Since $\varphi(q') \le q'$, subtracting at most $\frac{Y}{8\varphi(q')\log 2U} + \frac{Y}{8q'\log 2U} \le \frac{Y}{4\varphi(q')\log 2U}$ from $|\mathcal U| \ge \frac{Y}{2\varphi(q')\log 2U}$ leaves $\ge \frac{Y}{4\varphi(q')\log 2U}$ good primes.
5. **Carry isolation (Step 7′, line 358):** All three hypotheses of GF-22 Lemma 5.1 (`odd-characters-and-kernel-quotient.md:214-220`) hold for $P = Au$ and $n(u) = Au - W' - f - 1 \in [N, N+H)$: offsets $-(W'+f),\dots,-1 \in J$ kill $c_\Phi(n+1),\dots,c_\Phi(n+W'+f)$; prime $u \ge U > A$ with $u \equiv r_0 \pmod q$ sets $c_\Phi(Au) = b^f V_1$; offsets $1,\dots,L \in J$ yield $T_{Au} = b^{-L} T_{Au+L}$ with $|T_{Au}| < 1/2$.

**Assessment of the $2\sqrt{X_1}$ threshold:** The table and analysis on lines 368–377 are completely accurate: no prefix exceptional set survives into the moving-window proof, and the sole additive error $2\sqrt{X_1}$ in Lemma E.2 is $o(Y/q')$ if and only if $H \ge N^{1/2+\varepsilon}$, matching GRH's prime-interval threshold $a > 1/2$ exactly.

### 3.2 Proposition D.2: Unconditional near-full windows via three-family Landau–Page (§2.6)

- **Three-family avoidance (line 383):** Sound. The $3s$ primes exceed $P_0 > q$, so $\gcd(qQ_\mu, qQ_\nu) = q$ for $\mu \ne \nu$. Any fixed primitive real character of conductor dividing $q$ ceases to be exceptional once $1/\sqrt{\log U}$ falls below its real zero-free margin. Hence each of $q_1(U)$ and $q_1(U+Y)$ divides at most one of $qQ_1, qQ_2, qQ_3$, leaving at least one $q' = qQ_\nu$ divisible by neither. Since $\log q' = O_w(\log\log N \cdot \log\log\log N) = o(\sqrt{\log U})$, $q' \le T(U) \le T(U+Y)$.
- **Window length $H \ge N\exp(-c_3\sqrt{\log N})$ (lines 386–389):** Sound. Subtracting (E1) at $U+Y \le 2U$ and $U$ incurs error $\le 3CU\exp(-c_1\sqrt{\log U}) \le 4CU\exp(-c_1\sqrt{\log U})$. Because $\varphi(q') = \exp(o(\sqrt{\log N}))$ and $\sqrt{\log U} = \sqrt{\log N} - O_w(1/\sqrt{\log N})$, any fixed $c_3 < c_1$ (in particular $c_3 = c_1/3$, depending solely on (E1)'s constant $c_1$) works for $N \ge N_0(w)$.
- **Minor constant polish (m5):** Line 386 stops at $\psi(U+Y) - \psi(U) \ge Y/(2\varphi(q'))$, so subtracting prime powers $O(\sqrt N \log N)$ and the possible right-endpoint prime at $U+Y$ and dividing by $\log(2U)$ gives $|\mathcal U| \ge Y/(2\varphi(q')\log 2U) - O(\sqrt N)$, slightly below Step 5′'s $Y/(2\varphi(q')\log 2U)$. Requiring $Y \ge 16C\varphi(q')U\exp(-c_1\sqrt{\log U})$ gives $\psi(U+Y) - \psi(U) \ge \frac34 Y/\varphi(q')$, yielding $|\mathcal U| \ge Y/(2\varphi(q')\log 2U)$ literally so Steps 6′–7′ apply verbatim.

### 3.3 Proposition E: Necessity of additivity in `GF-22` (§2.7)

- **Proof (lines 393–399):** Completely rigorous. For any nonprincipal $\chi$, picking prime $p \nmid q$ with $\chi(p)$ of order $d \ge 2$ gives $c_\chi(n) = 0$ on the full residue class $n \equiv p^{d-1} \pmod{p^d}$. Since $a(n) = \Phi_{\rm ind}(c_\chi(n)) \in \{0, 1\}$ vanishes infinitely often, $\sum_{n > m} a(n)b^{m-n} < 1$ for every $m$ and every $b \ge 2$, so no carries occur and $d_n(F_b(a)) = a(n)$ identically. Hence $1^{p^d}$ never occurs in any base $b \ge 2$ (and digit $2$ never occurs for $b \ge 3$). Specifically, for $\chi_{-4}$ every $n \equiv 3 \pmod 4$ has $r_2(n) = 0$, forbidding `1111`; for the cubic character mod 7, $p = 2$ has order $d = 3$, so $n \equiv 4 \pmod 8$ has $v_2(n) = 2$ and $c(n) = 0$, forbidding `1^8`.
- **Registry check (line 401):** Independently verified via `git show HEAD:docs/registry/GF.toml`, `docs/registry/GF.toml:394`, and `docs/results.md:3910`. The HEAD commit `04969b9` and generated `docs/results.md:3910` indeed still carry the false wording `"every nonzero integer-valued function Φ on the range of 1 ∗ χ with Φ(0) = 0"`, whereas the uncommitted working tree `docs/registry/GF.toml:394` already specifies `"every nonzero additive map Φ : ℤ[ζ_h] → ℤ"`.

---

## 4. Audit F: Mira Cult Short-Window Exponent Audit (§3)

Every step of §3 was cross-checked against `notes/phase13/erdos-borwein.md` (P13) and `notes/phase13/reviews/erdos-local-limit.md` (P13-R):

- **Lemma F.1 (lines 427–435):** Sound (add $x \ge 4$ so $z > x/2 \ge 2$ lies in Theorem A's domain; **m7**). Applying Theorem A pointwise at $z + h \le 2x$ and $z$ and summing over $q \le Q = x^\rho$ gives $\le 2C_0 Q\sqrt{2x}\log^2(2Qx) \le 2C_0 Q\sqrt{2x}\log^2(4Qx) \ll y x^{-(\vartheta - 1/2 - \rho)}\log^2 x \ll_B y(\log x)^{-B}$ for every $0 < \rho < \vartheta - 1/2$ and every $B$. Prime-power removal over $q \le X^\rho$ costs $O(X^{1/2+\rho}\log X)$ (bounded by $O(X^{1/2+\rho}\log^2 X)$), also saving a power for $\rho < \vartheta - 1/2$.
- **Exact $\rho$-dependence (§3.3, lines 437–450):** Confirmed against P13-R lines 41–115 that no step needs a uniform lower bound $\rho \ge \rho_0$:
  - Unconditionally, Huxley–Iwaniec already uses $\rho < 3\vartheta - 7/4 \to 0$ as $a \downarrow 7/12$.
  - With $c = \rho/[100D(R+1)]$, the later-bank exponent budget is $Dc\sum_{h=0}^{m-1} 2^{-h}(R+h) < Dc(2R+2) = \rho/50 < \rho/4$ for every $\rho > 0$; forces have size $\le X^{2\eta} = X^{\rho/8} < X^{\rho/4}$; $\eta/c = 100D(R+1)/16$ is independent of $\rho$, so the mean count $\log(\eta/(4c)) + O(1)$ of supplementary primes in $(X^c, X^{\eta/4}]$ depends only on $W$; omitted higher powers cost $O(X^{-\eta/2})$; the first-bank mass shift $\log(1/c) = O(\log(W/\rho))$ is fixed as $N \to \infty$; and the choice order $a \mapsto (a',\theta,\vartheta,\rho) \mapsto W(k,\rho) \mapsto (L, B_*, R) \mapsto N \to \infty$ absorbs all $\rho$-dependent constants before $N \to \infty$.
  - The dimension-two sieve / second-moment step needs only $a' - 2\theta > 0$ (satisfied since $\theta < a'/4 \implies a' - 2\theta > a'/2 > 1/4$), and the divisor-pairing tail needs only $\sqrt N / H \to 0$ ($a > 1/2$).
  - **Two minor precision slips in §3.3 (neither affecting the conclusion):**
    1. **m2 (lines 446, 532; `scripts/phase25_grh_windows.py:835`):** Because $X \asymp N/b$ with $b \le N^\theta$, the stripped form satisfies $L_j(p) \le bp + J \ll N \ll X^{1/(1-\theta)}$, NOT $X^{1+o(1)}$. Hence the deterministic multiplicity bound for factors $> X^{\eta/4}$ is $\le \frac{4}{\eta(1-\theta)}(1+o(1)) = \frac{64}{\rho(1-\theta)}(1+o(1))$ (at most $\frac{512}{7\rho}$ when $\theta \le 1/8$, or $\frac{256}{3\rho}$ for $\theta < 1/4$), not $\frac{4}{\eta}(1+o(1)) = \frac{64}{\rho}$. It remains $O(1/\rho)$, so nothing downstream changes.
    2. **m3 (line 449):** In P13-R line 81, $Z_j = C_a[(1+G)^2 + M_j^2 + P_j^2]$ bounds the *square* of the valuation/odd-part error $O(1/\rho + G + M_j + P_j)$, so $C_a$ grows like $O(1/\rho^2)$ rather than $O(1/\rho)$. For fixed $\rho > 0$, $O(C_a(1 + \log^2(W/\rho))/W) \to 0$ as $W \to \infty$ holds identically.
- **Why Kumchev 0.53 does not transfer (line 458):** Accurate. Kumchev's minorant $\lambda$ is signed ($\lambda(n) \le 0$ on composites) and supported on composites as well as primes, whereas Mira Cult's local-limit comparison requires two-sided equidistribution of a genuine nonnegative probability measure supported on primes (for Markov/Cauchy–Schwarz positivity, Bonferroni defect bounds, and the exact prime-factorization identity $\tau(bp) = 2^{\omega(m)+1}(2u+1)$).
- **Lean Fourier transfer (line 456):** Checked directly against `NormalityChecker/ErdosBorweinFourier.lean:89-94` (`erdosBorwein_window_fourier`). Dividing $(1 - c/2)H + 1$ by $H$ yields $1 + 1/H - c_{a,w}/2$ for odd $h$ and $w = 10^{k-1}$ with $2^k \ge 2\pi|h|$. Exact match.
- **Provenance and caveats (lines 407–409, 456):** Properly credits Mira Cult (claim 0002, commit `149831943806a656c9efaa14cacbd9c915b2a2ba`, noting GPT-6.2 Astra's drafting role per P13), clearly labels §3 as a dependency audit relying on P13/P13-R rather than a re-verification of Mira's source files, and preserves P13's residual verification burden.

---

## 5. Required research-note sections, evidence labels, and prior art

Checked against the 10 required research-note sections:

1. **Exact definitions:** Present — preamble (line 5) and §0 (lines 40–78).
2. **Precise statements:** Present — §1 (lines 82–152), §3.2 (Lemma F.1), §3.4 (Audit conclusion F).
3. **Complete proofs / explicit dependency audit:** Present — §2.1–§2.7 (lines 156–402) and §3.1–§3.4 (lines 405–459).
4. **Prior art and attribution:** Present — §4 (lines 462–469) and References (lines 644–658), with explicit search-scope disclaimer and recalled-not-rechecked flag on Guth–Maynard (2024).
5. **External inputs and exact hypothesis verification:** Present — §5 (lines 471–485). One broken 4-column Markdown row at line 479 (**m9**).
6. **Evidence labels and ledger:** Present — preamble (lines 7–18), Summary table (lines 26–34), §6 (lines 487–498). Every GRH deduction is strictly labeled `Conditional`; finite digit statistics are declared non-evidence; cross-model review is explicitly distinguished from independent human peer review (line 18); zero benchmark changes are claimed.
7. **Reproduction instructions:** Present — §7 (lines 500–506); verified verbatim.
8. **Exact finite tests:** Present — §8 (lines 508–532), covering S1–S10.
9. **Open questions:** Present — §9 (lines 534–543), 8 concrete open questions.
10. **Standing objectives advanced:** Present — §10 (lines 545–558), explicitly mapped to Objectives 1–4 and benchmark policy.

---

## 6. Itemized findings

### Critical
None.

### Major
None.

### Minor

| # | Location | Finding | Concrete fix |
| --- | --- | --- | --- |
| **m1** | `scripts/phase25_grh_windows.py:507-531`; `notes/phase25/grh-lambert-windows.md:326, 515-523` | **S6 exact/float separation leak and ratio mislabeling.** (i) `holds[a]` (script line 519) evaluates an illustrative GRH-constant-1 window inequality in floating-point (`float(a)`, `math.log10(float(lnqN_hi))`), yet lines 530–531 tag `not by_E[100][a]` and `by_E[10**6][a]` as `"exact"` (and note line 515 calls them "The exact checks", conflicting with §6 line 497). Moreover, `holds[a]` is a *sufficient* upper-bound test, so negating it does not formally certify failure. (ii) Note lines 326 and 517–523 label `dq / E` (`len(str(q')) / E`, printed as `digits(q')/log10 N` by the script) as `$\log q'/\log N$`, shifting the third significant digit at $E = 100$ (`2.71` vs true `2.701`), $E = 10^4$ (`0.0405` vs `0.0404`), and $E = 10^6$ (`0.000557` vs `0.000556`). | Change lines 530–531 to `check("num", ...)` (or verify $q' > N$ at $E=100$ and a pure-integer/Fraction sufficient bound at $E=10^6$ for `"exact"`), align note line 515 with §6 line 497, and either rename the note's column to `digits(q') / log10 N` or print true `math.log10(qprime) / E` (`22.10`, `2.701`, `0.340`, `0.0404`, `0.000556`). |
| **m2** | `notes/phase25/grh-lambert-windows.md:446, 532`; `scripts/phase25_grh_windows.py:835` | **Missing $1/(1-\theta)$ factor in §3.3 large-factor multiplicity bound.** Since $X \asymp N/b$ with $b \le N^\theta$, the stripped form has size $L_j(p) \ll N \ll X^{1/(1-\theta)}$ rather than $X^{1+o(1)}$, so the deterministic multiplicity of prime factors $> X^{\eta/4}$ is $\le \frac{4}{\eta(1-\theta)}(1+o(1)) = \frac{64}{\rho(1-\theta)}(1+o(1))$, not $\frac{4}{\eta}(1+o(1)) = \frac{64}{\rho}$. | Replace $4/\eta$ and $64/\rho$ with $\frac{4}{\eta(1-\theta)} = \frac{64}{\rho(1-\theta)}$ (noting $\frac{1}{1-\theta} < \frac{4}{3}$ since $\theta < 1/4$, so $\le \frac{256}{3\rho}(1+o(1)) = O(1/\rho)$). |
| **m3** | `notes/phase25/grh-lambert-windows.md:449` | **$C_a$ scaling in $\rho$.** Line 449 writes `$C_a \asymp 1/\rho$` in $Z_j = C_a[(1+G)^2 + M_j^2 + P_j^2]$. Because $Z_j$ bounds the *square* of the valuation/odd-part displacement $O(1/\rho + G + M_j + P_j)$, $C_a$ scales as $O(1/\rho^2)$ (or $Z_j$ carries an additive $O(1/\rho^2)$ constant term). The limit $W \to \infty$ at fixed $\rho$ is unaffected. | Change `$C_a \asymp 1/\rho$` to `$C_a \ll 1/\rho^2$` (or `$C_a = O(1/\rho^2)$`). |
| **m4** | `notes/phase25/grh-lambert-windows.md:279` | **Proposition C upper bound constant when $\kappa > \log 2$.** With $\ell = \lceil \kappa\log_2\log N \rceil$, line 279 asserts $(\ell - 1)/H \le \log\log N / N^a$, which fails when $\kappa > \log 2 \approx 0.693$ (e.g. `ex:quarter`, $\kappa = 3/4$, where $\kappa/\log 2 \approx 1.082 > 1$). | Replace `(\ell-1)/H \le \log\log N / N^a` with `(\ell-1)/H \le (\kappa/\log 2)\log\log N / N^a \ll \log\log N / N^a`. |
| **m5** | `notes/phase25/grh-lambert-windows.md:386-389` | **Proposition D.2 constant slack from $\psi$ to $|\mathcal U|$.** Line 386 proves $\psi(U+Y) - \psi(U) \ge Y/(2\varphi(q'))$, so subtracting prime powers $O(\sqrt N\log N)$ and the right endpoint $U+Y$ leaves $|\mathcal U|$ slightly below Step 5′'s $Y/(2\varphi(q')\log 2U)$, making "Steps 6′ and 7′ are unchanged" slightly imprecise. | Replace $8C$ by $16C$ in line 389 to obtain $\psi(U+Y;q',a_0) - \psi(U;q',a_0) \ge \frac{3Y}{4\varphi(q')}$; subtracting prime powers and the single endpoint $U+Y$ then yields $|\mathcal U| \ge \frac{Y}{2\varphi(q')\log 2U}$ literally. |
| **m6** | `notes/phase25/grh-lambert-windows.md:98, 108, 158, 226` | **Corollary numbering inversion.** Corollary A.3 is stated (line 98) and proved (§2.1, line 158) before Corollary A.2 (stated line 108, proved §2.2 line 226). | Swap the labels A.2 and A.3 throughout the note (and script comment on line 315) so Corollary A.2 precedes Corollary A.3. |
| **m7** | `notes/phase25/grh-lambert-windows.md:90, 427` | **Missing lower-bound domain hypotheses.** Theorem A's short-interval sentence (line 90) omits `$X \ge 2$` (needed for Theorem A at $x = X$), and Lemma F.1 (line 427) omits `$x \ge 4$` (needed for $z > x/2 \ge 2$) and `$0 \le h \le y$`. | Write "for $X \ge 2$ and $1 \le H \le X$" on line 90, and add "$x \ge 4$" and "$0 \le h \le y$" in Lemma F.1 (line 427–430). |
| **m8** | `notes/phase25/grh-lambert-windows.md:514`; `scripts/phase25_grh_windows.py:454-463` | **S5 gcd check count mismatch.** Note line 514 states "on 4000 instances", whereas the script loops 4,000 times and skips pairs with $\gcd(A, q') \ne 1$, executing **2,424** coprime checks. | Update line 514 to "on 2424 coprime pairs (out of 4000 sampled)" (or loop `while checked < 4000:` in the script). |
| **m9** | `notes/phase25/grh-lambert-windows.md:479` | **Malformed 4-column Markdown table row in §5.** Row 5 (`GF-22 (E1)`) of the 5-column External Inputs table is missing its `Statement used` cell, shifting three cells one column left. | Split the first cell into `\| GF-22 (E1) \| Landau–Page and PNT for $q' \le \exp(c_0\sqrt{\log x})$ with at most one exceptional modulus \| Proposition D.2 \| ... \|`. |
| **m10** | `notes/phase25/grh-lambert-windows.md:571-573, 628-642` | **Appendix A polish.** (i) Line 571–572 writes "all nontrivial zeros of $L(s, \chi)$" for $\chi \bmod q_0$ without specifying $0 < \Re s < 1$ or primitive $\chi^*$ (unlike main note line 5, leaving possible ambiguity about the $\Re s = 0$ Euler-factor zeros of imprimitive characters). (ii) Line 642 references a Conditional $a > 1/2$ label for Insert A5, whereas Insert A5 (lines 630–635) states only $0.53 < a \le 1$. | Change line 572 to `$L(s, \chi^*)$` (or specify `$0 < \Re s < 1$`), and either add the conditional `$a > 1/2$` sentence to Insert A5 or adjust line 642 to match Insert A5's stated scope. |
| **m11** | `notes/phase25/grh-lambert-windows.md:30, 31, 140, 246, 323, 482, 510`; `scripts/phase25_grh_windows.py:292-293, 393` | **Minor notation/housekeeping polish.** (i) Theorem D's moduli $q' = qQ(N)$ depend on $w$ as well as $N$: write $q' = qQ(N, w)$. (ii) Step 5′ (line 323) should note explicitly that Corollary A.3's $\theta$-bound is applied on $(U, U + Y - 1] \subset [U, U + Y)$ to explain both $Y - 1$ and the exact constant $C_2$. (iii) In §5 line 482 / Prop. C, briefly echo Paper VI's provenance note (`paper.tex:1171-1173`) that Kumchev (2002) was checked against the author's posted text rather than the printed journal version. (iv) In S1 (`scripts/phase25_grh_windows.py:292-293`), `Fraction(1)` is duplicated in `grid` for $\nu_* \in \{1/2, 53/100\}$, and `acc` on line 393 is unused. | Apply these four small clarifications when polishing the note and script. |
