# Phase 25 Track A — cross-provider adversarial referee review

**Audited files.** [`notes/phase25/e4-carry-correlations.md`](../e4-carry-correlations.md) (435 lines; SHA-256 `6E246740161B7F37649FB57F18EB3474C7A50F094B970206C37F930C6A0C1A35`) and [`scripts/phase25_e4_carries.py`](../../../scripts/phase25_e4_carries.py) (894 lines; SHA-256 `4DC58475108A3129149F8E15D7648051D51E708BD39AEC9AF6FF52E4DDB56679`), authored by Claude Opus 5.5 on branch `research/phase-25-carry-correlations`.

**Reviewer.** Gemini 4 Neon (XHigh), a different provider from the author. The audit was strictly read-only on all existing repository files; no audited file was modified, and nothing was committed.

> **Cross-model review is not independent human peer review.** This report is an adversarial second machine reading by a model from another provider. It does not replace independent human peer review by specialists in analytic number theory, uniform distribution or probabilistic number theory, and none of its conclusions may be used to change a benchmark status.

## Verdict: **REVISE**

| Severity | Count |
| --- | --- |
| Critical | 0 |
| Major | 2 |
| Minor | 14 |

**Executive summary.** The mathematical core of Phase 25 Track A is **genuinely strong and survives adversarial checking without structural failure**. In particular:

- The unconditional **stationarity bound** (Theorem 2.2), $\limsup f_1 \le \limsup \frac1N \sum_{j<N} \{R_W(j)/2^W\} + 2^{-W}\mu/k$, is completely airtight — verified both by the note's fractional-part proof (including exact telescoping $\frac1N \sum_{j<N} \{2^j x\} = f_1(N) + (\{2^N x\} - \{x\})/N$ and the dominated-convergence bound $\frac1N \sum_{j<N} J_{j+s} \le C(1+s)$) and independently via the carry identity $K^J(N) \ge K^{J,(W)}(N)$.
- The **3-column $E(4)$ criterion** ($B_3 \le 0.452881 < \tfrac12 < B_2$, Theorem 2.4) and **8-column $E(2)$ criterion** ($B_8 \le 0.497108 < \tfrac12 < B_7$, Remark 2.5) are real, independently reproduced by an unrelated characteristic-function/DFT calculation, and genuinely reconcile with CC-49's 16-column sharpness because CC-49's single-window countermodels are non-stationary and violate $\mathbb{E}[X] = \mathbb{P}(X \ge \tfrac12)$.
- The **locality barrier** (Theorem 2.3 via bivariate Erdős–Kac), the **base-4 identities and parity equidistribution** (Lemma 3.1, Theorems 3.2–3.3, Proposition 3.5 via Wirsing), the **$E^*(4)$ normality equivalence and conditional second-moment theorem** (Theorems 4.1–4.3), and the **exact rational countermodels** (Theorems 5.1–5.3) are all mathematically sound.

However, **two Major defects require revision** before acceptance or registration:

1. **M1 (False error term in Theorem 1.2, line 96):** The displayed equation states $f_1(N; E(4), 2) = \frac{C_{\rm true}}{2} - \frac{K(N)}{N} + O\bigl(\frac{\log^2 N}{N}\bigr)$. Replacing $\frac1N \sum_{n \le M} s_2(\tau(n))$ by $\frac{C_{\rm true}}{2}$ introduces an error that is **provably not** $O(\log^2 N / N)$ — in fact not even $O(N^{-1/2-\varepsilon})$ for any $\varepsilon > 0$ (proved below via analytic continuation of $D(s) - C_{\rm true}\zeta(s)$ to $s \to \tfrac12^+$). The correct error is $+o(1)$, with $O(\log^2 N / N)$ applying only to the intermediate sum $\frac1N \sum_{n \le M} s_2(\tau(n)) - \frac{K(N)}{N}$.
2. **M2 (Systematic inward rounding of certified intervals and a false margin bound in §§2, 11, 13 and Script §7):** The script computes rigorous `Fraction` bounds for $\mu$ and $B_W$, but prints them with round-to-nearest `float` formatting (`:.8f`, `:.6f`) without outward-rounded decimal formatters or endpoint assertions. Consequently:
   - **Theorem 2.6 ($\mu$):** both endpoints of $[2.07632554, 2.07632692]$ are inward-rounded (certified exact range $[2.0763255364\ldots, 2.0763269206\ldots]$; outward-rounded $[2.07632553, 2.07632693]$).
   - **Theorem 2.4 ($E(4)$, $W=4$):** both endpoints of $B_4 \in [0.424561, 0.424562]$ are inward-rounded (certified $[0.4245605199\ldots, 0.4245624529\ldots]$), making the stated consequence $\limsup f_1 \le 0.424562$, $D^- \ge 0.075438$ **uncertified** (outward-rounded: $B_4 \in [0.424560, 0.424563]$, $\limsup f_1 \le 0.424563$, $D^- \ge 0.075437$). Also $B_2$'s lower bound is inward-rounded (`0.52061577...` printed as `0.520616`).
   - **Remark 2.5 ($E(2)$, $W=7,8$):** $B_7$'s upper bound (`0.50209638...`) and $B_8$'s lower bound (`0.49709957...`) are inward-rounded, and the claimed margin $\tfrac12 - B_8 \ge 2.9 \times 10^{-3}$ (line 231) is **false** even for the exact value ($\tfrac12 - B_{8,\rm hi} = 2.8923\ldots \times 10^{-3} < 2.9 \times 10^{-3}$, and the DFT true value is $\approx 2.897 \times 10^{-3}$).
   - **§2 criterion table (lines 185–188) and Open Question 1 (line 417):** for $W=3$ and $W=4$, the stated sufficient thresholds `< 0.370230` and `< 0.435115` exceed $\tfrac12 - \mu 2^{-W-1}$ (`0.37022965...` and `0.43511482...`), so they do **not** guarantee RHS $< \tfrac12$ (must be `< 0.370229` and `< 0.435114`; similarly `< -0.019082` for $W=1$).

Both Major findings admit clean, localized fixes that leave every headline conclusion intact.

---

## 1. Script execution, exact vs floating-point separation, and numerical audit

### 1.1 Reproduction run

Running `python -B scripts/phase25_e4_carries.py` on Windows from the repository root exited with code **`0`** and printed:

```text
ALL CHECKS PASSED: 2513819 exact checks in 13 s
```

Every finite measurement in §9, every floating-point heuristic entry in §10, the window-error counts in Theorem 1.5 (`346, 5, 0`), the $N=490$ tail chain (`gap=9, ell=2, Z=8`, 22 values with `gap >= 8`), the $E^*(4)$ counts (`15679` mismatches, `7709` collision columns, `3886 = 3834 + 52` digit-3 positions), the $D$-local carry fractions (`0.112, 0.149, 0.172`), and the $\mathcal{C}_1$ fractions (`0.2090, 0.2117, 0.2111`) match the script's printed output.

### 1.2 Exact vs floating-point separation

The script separates exact integer/`Fraction` certificates (Sections 1–7) from finite measurements and floating-point heuristics (Section 8) **at the structural level**, but **three leaks** contradict line 3's claim that floating-point arithmetic appears only in §10 and Section 8:

1. **Section 8 floating-point checks are counted as "exact checks":** lines 888–891 call `check()` three times on floating-point `preds`, incrementing the global `CHECKS` counter reported as `2513819 exact checks` at line 894.
2. **Floating-point operations inside certificate checks in Sections 2 and 5:** lines 272, 274, and 275 use `math.log2`, and lines 496–497 use float division `cblk[W] = acc / len(offs)` before `check(cblk[W] <= ...)`. All four are easily replaced by exact integer comparisons.
3. **Round-to-nearest `float` printing of `Fraction` bounds in Section 7:** lines 637, 752, and 767–769 print `Fraction` certificates via `f"{float(...):.8f}"` / `:.6f`, directly causing Major Finding M2.

### 1.3 Independent cross-checks

Independent reviewer Python code (not sharing code with the verifier) confirmed:

- **$N = 490$ tail chain:** $T_{490} = 2 = (10)_2$ ($\ell = 2$), low 12 bits of $A_{490}$ are `001111111110`, low 12 bits of $\lfloor 2^{490} E(4) \rfloor$ are `010000000000`, producing $1 + 8 = 9$ carries and zero run $Z(490) = 8$.
- **Independent DFT check of $B_W$:** Computing the characteristic function $\exp(\lambda(\hat{\nu}(h) - 1))$ of $\mathrm{CP}(\lambda, \nu) \bmod 2^W$ (primes $\le 5000$) and multiplying across columns yields $B_1 = 0.677112$, $B_2 = 0.520616$, $B_3 = 0.452879$, $B_4 = 0.424560$ for $E(4)$, and $B_6 = 0.512436$, $B_7 = 0.502093$, $B_8 = 0.497103$ for $E(2)$, matching the certified intervals to 6 decimals. Under $Q_8^{(1)}$ for $E(2)$, the mass near $1$ is suppressed ($256\,Q_8(255) \approx 0.646$, $256\,Q_8(0) \approx 1.241$), explaining why $B_8 - p_* \approx 0.00465$ is significantly smaller than the uniform-residue heuristic $2^{-8}(\mu - p_*) \approx 0.00619$.
- **Exact Law B rational (Theorem 5.2):** Solving the 3-state chain directly gives $f_1(\text{Law B}) = \frac{92307439724609}{179643056000000} = 0.513838061876\ldots$, matching the note's `0.513838...`.
- **Exact decimal expansion of all Section 7 `Fraction` bounds:**

| Quantity | Exact certified `Fraction` interval (10–12 decimals) | Note text | Outward? | Required outward-rounded interval |
| --- | --- | --- | --- | --- |
| $\mu$ (Thm 2.6) | $[2.076325536414\ldots,\ 2.076326920643\ldots]$ | $[2.07632554,\ 2.07632692]$ | **NO (both ends)** | $[2.07632553,\ 2.07632693]$ |
| $E(4)\ B_1$ | $[0.6771113514\ldots,\ 0.6771119495\ldots]$ | $[0.677111,\ 0.677112]$ | Yes | $[0.677111,\ 0.677112]$ |
| $E(4)\ B_2$ | $[0.5206157738\ldots,\ 0.5206167027\ldots]$ | $[0.520616,\ 0.520617]$ | **NO (lower)** | $[0.520615,\ 0.520617]$ |
| $E(4)\ B_3$ | $[0.4528792357\ldots,\ 0.4528806450\ldots]$ | $[0.452879,\ 0.452881]$ | Yes | $[0.452879,\ 0.452881]$ |
| $E(4)\ B_4$ | $[0.4245605199\ldots,\ 0.4245624529\ldots]$ | $[0.424561,\ 0.424562]$ | **NO (both ends)** | $[0.424560,\ 0.424563]$ |
| $E(2)\ B_7$ | $[0.5020893775\ldots,\ 0.5020963881\ldots]$ | $[0.502089,\ 0.502096]$ | **NO (upper)** | $[0.502089,\ 0.502097]$ |
| $E(2)\ B_8$ | $[0.4970995751\ldots,\ 0.4971076117\ldots]$ | $[0.497100,\ 0.497108]$ | **NO (lower)** | $[0.497099,\ 0.497108]$ |
| $\tfrac12 - \mu/4$ ($W=1$) | $[-0.0190817302\ldots,\ -0.0190813842\ldots]$ | `< -0.019081` | **NO** | `< -0.019082` |
| $\tfrac12 - \mu/8$ ($W=2$) | $[0.2404591349\ldots,\ 0.2404593079\ldots]$ | `< 0.240459` | Yes | `< 0.240459` |
| $\tfrac12 - \mu/16$ ($W=3$) | $[0.3702295674\ldots,\ 0.3702296539\ldots]$ | `< 0.370230` | **NO** | `< 0.370229` |
| $\tfrac12 - \mu/32$ ($W=4$) | $[0.4351147837\ldots,\ 0.4351148269\ldots]$ | `< 0.435115` | **NO** | `< 0.435114` |

---

## 2. Section-by-section mathematical audit

### 2.1 A1: Carry framework (§§0–1, Lemma 1.1, Theorems 1.2–1.5, Corollary 1.6)

- **Lemma 1.1:** Verified completely, including on dyadic rationals (e.g., $a_1=0, a_j=1$ for $j\ge 2$ gives $x=1/2$, $c_0=0$, $c_j=1$ for $j\ge 1$, satisfying (a)–(e) with the non-$1^\infty$ convention). One missing assumption: $a_j \in \mathbb{Z}_{\ge 0}$ must be stated explicitly (lines 53, 73).
- **Theorem 1.2:**
  - The exact identities $S(N) = R(N) - K(N) + c_N = \sum_{j\le N} J_j - K^J(N) + c_N^J$ follow by summing Lemma 1.1(b) over $j=1,\dots,N$ with $c_0 = \lfloor E(4) \rfloor = 0$ (and $2n-i \ge 2$ for every bit of $\tau(n)$).
  - The boundary bounds $0 \le \varepsilon_N = O(\log^2 N)$, $\sum_{j\le N} J_j = \sum_{n\le M} o(n) + O(\sqrt{N}\log N)$, and $c_N^J \le 3\sqrt{N}$ all check (since $\sum_{i>N} J_i 2^{N-i} = \sum_{2n-v(n)>N} \tau(n) 2^{N-2n} \le \sum_{n>N/2} 2\sqrt{n}\,2^{N-2n} \le 2.47\sqrt{N} < 3\sqrt{N}$ for all $N \ge 1$).
  - **Major Finding M1 (line 96):** The claimed error $O(\frac{\log^2 N}{N})$ on $f_1(N; E(4), 2) = \frac{C_{\rm true}}{2} - \frac{K(N)}{N} + O(\frac{\log^2 N}{N})$ is **false** (detailed proof in §4 below).
  - **Minor Finding m1 (lines 93, 103, 128):** The arrival bound $r_i \le \frac32 + \frac14 \log_2 i$ is valid for all $i \ge 1$, but $\sum_{m\ge 1} r_{N+m} 2^{-m} = \frac32 + \frac14 \log_2 N + \frac14\sum_{m\ge 1} \log_2(1 + m/N) 2^{-m}$ gives a remainder exceeding $0.001$ for every $N \le 721$ (e.g., $0.3663$ at $N=1$ and $0.00144$ at $N=500$). The bound $c_N \le \frac32 + \frac14 \log_2 N + 0.001$ holds for all $N \ge 1$ only when combined with the finite check on $N \le 721$ (where $c_N \le 2$ and $c_1=c_2=c_3=0$).
- **Theorem 1.4:**
  - Part (a): $\kappa_{24}(N) = K(N) - c_N + s_2(T_N) - \varepsilon_N = K(N) + O(\log^2 N)$ is exact and confirms Phase 24 Theorem 9.1.
  - Parts (b)–(d): The Kummer carry chain of $A_N + T_N$ and its bound $\ell(T_N) + Z(N)$ are correct, as is the implication $f_1(N) \to \alpha > 0 \implies Z(N) = o(N)$. However, the convention "$d_j = 0$ for $j \le 0$" (line 65) makes $Z(N) = \infty$ whenever $d_1 = \dots = d_{N-\ell} = 0$ (Minor m2), and line 119 omits the condition that a carry actually enters bit $\ell(T_N)$ (Minor m3).
- **Theorem 1.5 & Corollary 1.6:** Sound. In Theorem 1.5, fix the typo "$o(N)$" -> "$o(1)$" on line 134 and clarify $W = W(N)$ with $W(N) - \ell(N) \to \infty$ plus the $[0,1]$ vs $\mathbb{R}/\mathbb{Z}$ topology on zero-charging limit measures (Minor m5). All five equivalences in Corollary 1.6 hold verbatim (using $+o(1)$ from the repaired Theorem 1.2).

### 2.2 A2: Stationarity bound, locality barrier, 3-column $E(4)$ & 8-column $E(2)$ criteria, and $\mu$ (§2)

- **Theorem 2.1 (reset witnesses):** Sound for both column-block resets (for $E(4)$, where $c_0 = 0$) and coefficient-group partitions.
- **Theorem 2.2 (stationarity bound) — verified in full detail:**
  - **Step (i):** Summing the exact digit identity $d_j = 2\{2^{j-1} x\} - \{2^j x\} = \{2^{j-1} x\} + (\{2^{j-1} x\} - \{2^j x\})$ over $j = 1, \dots, N$ yields $\frac1N \sum_{j=0}^{N-1} \{2^j x\} = f_1(N) + \frac{\{2^N x\} - \{x\}}{N} = f_1(N) + O(1/N)$ unconditionally for every $x \in \mathbb{R}$, and likewise on any dyadic window $[N, 2N)$. No hidden uniformity or shift-invariance assumption is needed: shift invariance is automatic in Cesàro averages along any real orbit.
  - **Step (ii):** For $E(2^k)$ ($k \ge 1$), every mark lands in column $kn - v(n) \ge 1$ (checked even at $k=1$: $2^{n-1} > n \ge \tau(n) \ge 2^{v(n)}$ for $n \ge 3$, and $1-0=1$, $2-1=1$). Thus $2^j x \equiv \sum_{i=1}^W J_{j+i} 2^{-i} + 2^{-W} Y_{j+W} \pmod 1$, and $\{a + t\} \le \{a\} + t$ holds for all $a \in \mathbb{R}$ and $t \ge 0$ without exception, giving $\{2^j x\} \le \{R_W(j)/2^W\} + 2^{-W} Y_{j+W}$.
  - **Step (iii):** For fixed $m \ge 1$, $\frac1N \sum_{j<N} J_{j+W+m} \to \mu/k$ (both on $[0, N)$ and on $[N, 2N)$). Uniformly in $N \ge 1$ and $s \ge 1$, every $n$ contributing to $\sum_{j<N} J_{j+s}$ satisfies $n \le 2(N + s) + 4$, so by Phase 24 Lemma 3.1 ($\sum_{n \le Y} o(n) \le H_o Y$), $\frac1N \sum_{j<N} J_{j+s} \le \frac{H_o(2N + 2s + 4)}{N} \le C(1 + s)$, justifying dominated convergence against $2^{-m}$ and giving $\frac1N \sum_{j<N} Y_{j+W} \to \mu/k$.
  - **Independent second derivation:** Since $c_j^{(W)}(J) = \sum_{i\le W} J_{j+i} 2^{-i} - \{R_W(j)/2^W\}$ and $K^J(N) \ge K^{J,(W)}(N)$, Theorem 1.2 gives $f_1(N) \le \frac{\mu}{k} - \frac{K^{J,(W)}(N)}{N} + o(1) = \frac{\mu}{k \cdot 2^W} + \frac1N \sum_{j<N} \{R_W(j)/2^W\} + o(1)$ directly from a finite sum of $W$ terms.
  - Every sign, every factor of $1/2$ (and $1/k$), and every boundary term check out completely.
- **Theorem 2.3 (locality barrier):** The reduction of fixed-shift collisions to $|v(n+d) - v(n) - 2d| \le \log_2 T$, the probability bound on $v(n) - \omega(n)$, the application of bivariate Erdős–Kac (EK2, LeVeque 1949 / Elliott 1980), and the uniform-integrability step via $\sum_{m \le Y} g(m) \mathbf{1}[s(m) > S] \le Y \sum_{s > S\ \rm sqfull} \tau(s)/s < \infty$ are all sound. (Minor m6: note that $|\beta - \beta'| \le \log_2 T$ requires excluding $\{o(n+d) > T\}$ alongside $\{o(n) > T\}$.)
- **Theorem 2.4 & Remark 2.5 (3-column $E(4)$ & 8-column $E(2)$ criteria):**
  - The certificate algorithm in Script §7 (`mark_law_mod`, Weierstrass bounds for $p \in (3000, 10^6]$, $1/(P_2 - 1)$ tail for $p > 10^6$, alternating series `exp_neg_lo` truncated at odd index $41$ for $0 < \lambda \le 1$, downward-rounded convolutions, and charging missing mass at $(2^W - 1)/2^W$) was audited line by line and is **100% rigorous** in `Fraction` arithmetic.
  - The reconciliation with CC-49 in Remark 2.5 is completely valid: $R_{16}(n) \equiv R_8(n+8) \pmod{2^8}$ is exact, so CC-49's distributional 16-column hypothesis $\mathcal{L}(R_{16}) \to Q_{16}$ implies $H_8^{(1)}$; CC-49's $D \le 15$ countermodels are non-stationary (they lift moved cells to $2^{D-1} = 10\cdots0_2$, violating $\mathbb{P}(d_1=1) = \mathbb{P}(d_2=1) = \mathbb{E}[X]$), which is why enforcing orbit stationarity cuts $D$ from $16$ to $8$ and boosts the margin by more than an order of magnitude.
  - **Major Finding M2:** Repair the inward-rounded decimal endpoints, the uncertified $W=4$ bound, the too-loose $W=3,4$ thresholds, and the false `>= 2.9 * 10^-3` margin inequality.
- **Theorem 2.6 ($\mu$ enclosure):** Every analytical step in Script lines 608–634 is rigorous: the local truncation bound $\sum_{e' \ge e} \mathrm{odd}(e'+1)(p-1)p^{-e'-1} \le (e+2)p^{-e}$ holds for all $p \ge 2$; $1 \le \ell(p) \le 1 + 2p^{-2} < 1 + 2p^{-2} + 5p^{-3}$ holds for all $p \ge 3$; the $p \equiv \pm 1 \pmod 6$ integral comparison gives $\sum_{p > P}(2p^{-2} + 5p^{-3}) < \frac{2}{3(P-6)} + \frac{1}{(P-6)^2} =: y$; and $e^y \le 1 + y + y^2$ holds for $0 \le y \le 1$. Only the final decimal printing (M2) and the Phase 14 vs Phase 17 attribution (m8) need fixing.

### 2.3 A3: Base 4 (§3, Lemma 3.1, Theorems 3.2–3.3, Corollary 3.4, Proposition 3.5)

- **Lemma 3.1:** $s_4(m) + s_4(2m) = 3 s_2(m)$ is exact and cleanly proved.
- **Theorem 3.2:** Factoring $n = st$ ($s$ squarefull, $t$ squarefree, $(s,t) = 1$) gives $(-1)^{v(n)} = (-1)^{v(s)} \mu(t)$ and $o(n) = o(s)$ exactly. Wirsing's theorem (1967) applies rigorously to $f_s(t) = \mu(t) \mathbf{1}_{(t,s)=1}$ (and to $(-1)^{\omega(n)}$ in part (c)), since both are real multiplicative with $|f| \le 1$ and $f(p) = -1$ at all but finitely many primes, so $\sum_p (1 - f(p))/p = \infty$. Dominated convergence with $|\sum_{t \le X/s, (t,s)=1} \mu(t)| \le X/s$ and $\sum_{s\ \rm sqfull} |F(o(s))|/s < \infty$ is airtight. Parts (a), (b) ($\frac32 C_{\rm true} \in [2.008654, 2.008674]$, outward-rounded correctly from $[2.0086545, 2.0086740]$), and (c) follow cleanly.
- **Theorem 3.3 & Corollary 3.4:** Independent re-derivation confirms $C_m = c_{2m}$, $C_{m-1} = \lfloor (a_m + C_m)/4 \rfloor$, $S_{\rm e} - S_{\rm o} = (R_{\rm e} - R_{\rm o}) + 3(E_M - O_M) - 2c_{2M}$, $\sum_{m \le M} D_m = 2 R_{\rm o} + R_{\rm e} - 3 E_M + 4 c_{2M}$, and their asymptotic consequences.
- **Proposition 3.5:** The exact decomposition of $r_{2m}$ and $r_{2m-1}$ is verified and genuinely refutes the brief's first-order low-bit deficit heuristic. (Minor m9, m10: unify $K_{\rm e}, K_{\rm o}$ vs $E_M, O_M$, and propagate the External input Wirsing label to Theorem 3.3 and Proposition 3.5.)

### 2.4 A4: $E^*(4)$ (§4, Theorems 4.1–4.3)

- **Theorem 4.1:** Parts (a)–(e) are all true. In (b), the sharpest bound proved by the argument is $\#\{1 \le j \le N : d_j^* \ne \mathbf{1}_Q(j)\} \le 2 K^*(N) + \mathbf{1}[c_N^* \ge 1] \le 2 K^*(N) + c_N^*$, whereas the script checks the looser `2*(Ks + cs[NB]) + 1` (Minor m11). In (d), the final conditional-density sentence holds because $K^*(N) = o(N)$ forces $\sum_{j \le N} (r_j^* - 1)^+ \le 2 K^*(N) = o(N)$, making $n \mapsto q(n)$ injective off $o(M)$ exceptions (Minor m11).
- **Theorem 4.2:** Sound (Minor m12 on the guard-column count `7709` vs `7701`).
- **Theorem 4.3:** Verified carefully. With $Z(n) = \sum_{1 \le d \le \sqrt{L}} \mathbf{1}[\omega(n+d) - \omega(n) = 2d]$ on $I = (x/2, x]$, LLB($c$) gives $\mathbb{E}[Z] \ge c \lfloor \sqrt{L} \rfloor / \sqrt{L} \ge c/2$ (for all $L \ge 1$, and indeed $c(1 - o(1))$ as $x \to \infty$), while PUB($C$) gives $\mathbb{E}[Z^2] = \mathbb{E}[Z] + 2 \sum_{1 \le d < d' \le \sqrt{L}} \mathbb{E}[\mathbf{1}_d \mathbf{1}_{d'}] \le \mathbb{E}[Z] + 2 \binom{\lfloor \sqrt{L} \rfloor}{2} \frac{C}{L} \le \mathbb{E}[Z] + C$ — the factors of $2$ and $1/2$ cancel cleanly. Cauchy–Schwarz gives $\mathbb{P}_I(Z \ge 1) \ge c^2 / (2c + 4C) = \delta_0$, dyadic summation yields lower density $\ge \delta_0$, and Phase 24 Prop 10.2 yields $D^-(E^*(4); 2) \ge \delta_0 / 4$. (Note: asymptotically one even obtains $c^2 / (c + C)$.)

### 2.5 A5: Barriers and countermodels (§5, Theorems 5.1–5.3)

- **Theorem 5.1:** Exact closed form $\pi_1 = t / (1 - \lambda + 2t)$, $f_1 = \lambda - t / (1 - \lambda + 2t)$ verified; all three regimes $t \in \{0, (2\lambda-1)/4, \lambda/2\}$ are valid probability laws for both endpoints of $C_{\rm true}/2$ and give $f_1 > \tfrac12$, $f_1 = \tfrac12$, $f_1 < \tfrac12$ respectively.
- **Theorem 5.2:** Verified in exact rationals; Law A and Law B share mass $1$, mean $\lambda = 1339103/2000000$, and second factorial moment $m_2 = \lambda - \tfrac12$, while $f_1(\text{Law A}) = \tfrac12$ and $f_1(\text{Law B}) = \frac{92307439724609}{179643056000000} \approx 0.513838$. (Minor m14: at $s=0$ the 3-state chain is unichain rather than irreducible, though continuity of the stationary distribution still holds.)
- **Theorem 5.3:** Holds for all i.i.d. $\mathbb{Z}_{\ge 0}$-valued $N$ with $\mathbb{E}[N] = \tfrac12$ (even with unbounded support): $\mathbb{E}[N] = \tfrac12$ ensures $\mathbb{P}(N = 0) \ge \tfrac12 > 0$ and $\mathbb{E}[c] < \infty$, and $N_1 \ge 2$ directly implies $c_0 = \lfloor (N_1 + c_1)/2 \rfloor \ge 1$, so $\pi(c \ge 1) \ge \mathbb{P}(N \ge 2) > 0$ and $f_1 = \tfrac12 - \mathbb{E}[c] < \tfrac12$.

---

## 3. Required research-note sections, evidence labels, and prior art

All 10 required research-note contents (Phase 25 brief §5, items 1–10) are present:

1. **Exact definitions:** §0 (lines 38–70).
2. **Precise statements:** Results at a glance + §§1–5.
3. **Complete proofs or explicit missing steps:** Proofs follow each statement; unconditional limits are stated bluntly in §2.7 (line 237), and blocking hypotheses ($H_W$, LLB, PUB) are named explicitly.
4. **Prior art:** §6 (lines 358–365).
5. **External inputs and hypothesis checks:** §7 (lines 366–375).
6. **Evidence labels:** Present in the summary table, theorem headers, §9, and §10. Heuristic compound-Poisson predictions (§10, line 24, line 401) and finite measurements (§9, line 390, line 200, line 285) are clearly marked as **non-evidence**. Cross-model review is explicitly distinguished from human peer review (line 3).
7. **Reproduction instructions:** Line 3 and §8 (lines 376–388), including a clear note on the Hail server rule.
8. **Exact finite tests:** §8 table (lines 380–388) and `scripts/phase25_e4_carries.py`.
9. **Open questions:** §11 (lines 415–424).
10. **Standing objectives mapped:** Summary table (`Objectives` column) + §12 (lines 426–431) + §13 proposed registry text (lines 433–435).

Minor label/attribution polish items (m8, m10, m14) are itemized below.

---

## 4. Itemized findings

### Critical
None.

### Major

#### M1. False $O(\log^2 N / N)$ error term in Theorem 1.2 (note line 96)

- **Location:** `notes/phase25/e4-carry-correlations.md`, line 96 (and implicit spillover to line 99).
- **Issue:** Theorem 1.2 displays
  ```math
  f_1(N;E(4),2)=\frac{C_{\rm true}}2-\frac{K(N)}N+O\Bigl(\frac{\log^2N}N\Bigr)=\frac\mu2-\frac{K^J(N)}N+o(1).
  ```
  Combining this with the exact identity $S(N) = \sum_{n \le M} s_2(\tau(n)) + \varepsilon_N - K(N) + c_N$ (where $\varepsilon_N + c_N = O(\log^2 N)$) is equivalent to claiming $\sum_{n \le M} (s_2(\tau(n)) - C_{\rm true}) = O(\log^2 M)$, which is **not proved** by the proof on line 109 (Phase 24 Lemma 3.2 gives only $o(1)$) and is **provably false**.
- **Disproof of $O(N^{-\alpha})$ for every $\alpha > \frac12$:** For $\operatorname{Re}(s) > 1$, factoring $n = r t$ ($r$ squarefull, $t$ squarefree, $(r,t) = 1$) gives
  $$D(s) := \sum_{n=1}^\infty \frac{s_2(\tau(n))}{n^s} = \frac{\zeta(s)}{\zeta(2s)} \sum_{r\ \rm sqfull} \frac{s_2(o(r))}{r^s \prod_{p \mid r}(1 + p^{-s})}.$$
  Since $s_2(o(r)) \le g(r) = \prod_{p^e \parallel r} s_2(e+1)$, the squarefull series converges absolutely on $\operatorname{Re}(s) > \frac12$, continuing $D(s) - C_{\rm true}\zeta(s)$ analytically to the real interval $(\frac12, \infty)$. For real $s \in (\frac12, 1)$, $\frac{D(s)}{\zeta(s)} = \mathbb{E}_s[s_2(o(r))]$, where under $\mathbb{P}_s$ the prime exponents are independent with $\mathbb{P}_s(e_p = 0) = 1 - p^{-2s}$ and $\mathbb{P}_s(e_p = e) = (1 - p^{-s}) p^{-es}$ ($e \ge 2$). On the event $\{e_p \in \{0, 2\}\ \forall p\}$ (whose probability is at least $\prod_p(1 - p^{-3s}) > 1/\zeta(\frac32) > 0.38$ uniformly for $s > \frac12$), $o(r) = 3^{K_s}$ with $K_s = \#\{p : e_p = 2\} \to \infty$ in probability as $s \to \frac12^+$. By Senge–Straus ($s_2(3^k) \to \infty$, already used in Phase 24 Theorem 5.1), $\mathbb{E}_s[s_2(o(r))] \to +\infty$ as $s \to \frac12^+$. Since $\zeta(\frac12) \approx -1.46035 < 0$, $D(s) - C_{\rm true}\zeta(s) \to -\infty$ as $s \to \frac12^+$. By partial summation, $\sum_{n \le X}(s_2(\tau(n)) - C_{\rm true}) = O(X^\theta)$ is impossible for every $\theta < \frac12$, ruling out $O(\log^2 N / N)$. (Numerically, $C_{\rm true} - \frac1X \sum_{n \le X} s_2(\tau(n)) \approx 1.8 / (\sqrt{X}\log X)$ for $X \le 5 \cdot 10^5$, consistent with $\mathbb{E}[s_2(3U) - s_2(U)] \approx 0.815$.)
- **Concrete fix:** Match Phase 24 Theorem 9.1 by splitting line 96 into
  ```math
  f_1(N;E(4),2)=\frac1N\sum_{n\le M}s_2(\tau(n))-\frac{K(N)}N+O\Bigl(\frac{\log^2N}N\Bigr)=\frac{C_{\rm true}}2-\frac{K(N)}N+o(1)=\frac\mu2-\frac{K^J(N)}N+o(1).
  ```
  (No downstream proof is affected, as Corollary 1.6 and Theorem 2.4 use only $+o(1)$.)

#### M2. Inward-rounded certified decimal endpoints, uncertified $W=4$ bound, too-loose $W=3,4$ thresholds, and false $E(2)$ margin inequality (note lines 17, 185–188, 213, 215, 229, 231, 233, 417, 435; script lines 637, 752, 767–769)

- **Location:** `scripts/phase25_e4_carries.py`, lines 637, 752, 767–769; `notes/phase25/e4-carry-correlations.md`, lines 17, 185–188, 213, 215, 229, 231, 233, 417, 435.
- **Issue:** Exact `Fraction` enclosures in Section 7 are printed using round-to-nearest `float` formatting (`:.8f`, `:.6f`) instead of directed outward decimal formatting, and the decimal endpoints cited in the note are never asserted by `check()`. This causes:
  1. **Theorem 2.6 (lines 17, 233, 435):** `MU_LO = 2.0763255364...`, `MU_HI = 2.0763269206...` are rounded inward to `[2.07632554, 2.07632692]`.
  2. **Theorem 2.4, $W=4$ (line 215):** `B_4 in [0.4245605199..., 0.4245624529...]` is rounded inward to `[0.424561, 0.424562]`, so the stated theorem bound $\limsup f_1 \le 0.424562$, $D^-(E(4);2) \ge 0.075438$ is **not certified** by the script.
  3. **Theorem 2.4, $W=2$ (line 213):** `B_2` lower end `0.52061577...` is rounded inward to `0.520616`.
  4. **Remark 2.5 (lines 229, 231):** `B_7` upper end `0.50209638...` is rounded inward to `0.502096`; `B_8` lower end `0.49709957...` is rounded inward to `0.497100`; and the margin inequality $\frac12 - B_8 \ge 2.9 \cdot 10^{-3}$ (line 231) is **false** ($\frac12 - B_{8,\rm hi} = 2.892388\ldots \times 10^{-3} < 2.9 \times 10^{-3}$, and the DFT true value is $\approx 2.897 \times 10^{-3}$).
  5. **Criterion table (lines 185–188) and Open Question 1 (line 417):** The sufficient thresholds for $W=1, 3, 4$ (`< -0.019081`, `< 0.370230`, `< 0.435115`) exceed $\frac12 - \mu_{\rm lo} 2^{-W-1}$ (`-0.01908138...`, `0.37022965...`, `0.43511482...`), so satisfying them does not guarantee RHS $< \frac12$. Also the "value under $Q_W^{(1/2)}$" column gives single round-to-nearest numbers (`0.261075` at $W=2$ lies below the certified lower bound `0.26107508...`) despite calling every entry certified.
- **Concrete fix:**
  1. Add exact `dec_lo(frac, digits)` and `dec_hi(frac, digits)` helpers in `scripts/phase25_e4_carries.py` (using exact integer floor/ceiling on `frac * 10**digits`) and add explicit `check()` assertions for every decimal endpoint cited in the note.
  2. Update the note to outward-rounded intervals:
     - $\mu \in [2.07632553, 2.07632693]$ (lines 17, 233, 435);
     - $B_2 \in [0.520615, 0.520617]$, $B_4 \in [0.424560, 0.424563]$ with $\limsup f_1 \le 0.424563$ and $D^-(E(4);2) \ge 0.075437$ (lines 213, 215);
     - $B_7 \in [0.502089, 0.502097]$, $B_8 \in [0.497099, 0.497108]$, and margin $\frac12 - B_8 \ge 2.89 \cdot 10^{-3}$ (lines 229, 231);
     - Sufficient thresholds `< -0.019082` ($W=1$), `< 0.240459` ($W=2$), `< 0.370229` ($W=3$, lines 187 and 417), `< 0.435114` ($W=4$, line 188), and report outward-rounded intervals (or certified upper bounds) in the $Q_W^{(1/2)}$ column.
  *(Note: The headline bounds $B_3 \le 0.452881$ / $D^- \ge 0.047119$ for $E(4)$ and $B_8 \le 0.497108$ for $E(2)$ are already valid outward bounds and remain unchanged.)*

### Minor

| # | Location | Finding | Concrete fix |
| --- | --- | --- | --- |
| m1 | Note 93, 103, 128 | The analytical proof $c_N \le \sum_{m \ge 1} r_{N+m} 2^{-m}$ gives remainder $\frac14 \sum_{m \ge 1} \log_2(1+m/N) 2^{-m} \le \frac{1}{2N\ln 2}$, which exceeds $0.001$ for all $N \le 721$ ($0.3663$ at $N=1$, $0.00144$ at $N=500$). The bound $c_N \le \frac32 + \frac14\log_2 N + 0.001$ holds for all $N \ge 1$, but only via the finite check on $N \le 721$. | State $c_N \le \frac32 + \frac14\log_2 N + \frac{1}{2N\ln 2}$ analytically (noting $\le +0.001$ for $N \ge 722$, and verified for $N \le 721$), or replace $+0.001$ by $+0.37$ in the uniform statement. |
| m2 | Note 65, 118–120, 126 | Setting "$d_j = 0$ for $j \le 0$" makes the backward zero-run length $Z(N)$ infinite whenever $d_1 = \dots = d_{N-\ell(T_N)} = 0$ (which occurs already at $N=1$ since $d_1(E(4)) = 0$), contradicting $Z(N) = o(N)$ and differing from the script (`zr[0] = 0`). | Define $Z(N)$ as the zero run within positive indices $1 \le j \le N - \ell(T_N)$ (with $Z(N) = 0$ if $\ell(T_N) \ge N$), noting that $A_N < 2^N$ prevents any carry chain from reaching bit $N$. |
| m3 | Note 119 | Theorem 1.4(c) states "Beyond bit $\ell(T_N)-1$ it equals the length of the run of 1-bits of $A_N$ that starts at bit $\ell(T_N)$," omitting the condition that a carry enters bit $\ell(T_N)$ (if no carry enters, the count is $0$; line 124 gets this right). | Add "when a carry enters bit $\ell(T_N)$ (and $0$ otherwise)". |
| m4 | Note 53, 73 | Definitions of true carries and Lemma 1.1 write only $a_j \ge 0$, omitting $a_j \in \mathbb{Z}_{\ge 0}$, which is needed for $2^j x - Y_j \in \mathbb{Z}$ and Lemma 1.1(b). | Replace "$a_j \ge 0$" by "$a_j \in \mathbb{Z}_{\ge 0}$". |
| m5 | Note 134 | Typo: "$K^{(W)}/N$ approximates $K/N$ to $o(N)$" should be "$o(1)$" (or "$K^{(W)}$ approximates $K$ to $o(N)$"). Also clarify that $W = W(N)$ must grow so $W(N) - \ell(N) \to \infty$ (since the a priori $\ell(N) \sim \log_2\log_2 N$ grows), and clarify that "no limit measure of the orbit charges $0$" refers to limit measures on $[0, 1]$ (on $\mathbb{R}/\mathbb{Z}$, mass at $1^-$ charges $0$ without raising $F_N([0, 2^{-m}))$, though the sufficient direction still holds). | Fix "$o(N)$" $\to$ "$o(1)$", write $W = W(N)$, and specify limit measures on $[0, 1]$. |
| m6 | Note 196, 198 | In Theorem 2.3(a), bounding $|\beta - \beta'| \le \log_2 T$ requires excluding $\{o(n+d) > T\}$ as well as $\{o(n) > T\}$ (total upper density $< 2\varepsilon$). In 2.3(b), line 198 omits "$s$ squarefull" under $\sum_{s > S} \tau(s)/s$. | Exclude $\{o(n) > T\} \cup \{o(n+d) > T\}$ and add "$s$ squarefull" to the sum. |
| m7 | Note 16, 229–231 | Remark 2.5 reuses the symbol $H_8$ (defined on line 202 with $Q_W^{(1/2)}$ for $E(4)$) for $E(2)$ (which uses $Q_8^{(1)}$). Also clarify that CC-49's distributional 16-column hypothesis $\mathcal{L}(R_{16}) \to Q_{16}$ (rather than the single scalar inequality on $\Psi_{16}$) implies $H_8^{(1)}$. | Parameterize $H_W^{(\lambda)}$ (or write $H_8^{(1)}$ using $Q_8^{(1)}$) and specify CC-49's distributional 16-column hypothesis. |
| m8 | Note 17, 235; Script 636 | The prior certified enclosure $\mu \in [2.0762592, 2.0763285]$ is attributed to "Phase 14". Phase 14 (`notes/phase14/erdos-borwein-frequencies.md` line 42) proved $\mu \le 5/2$ analytically; the certified enclosure `[2.0762592, 2.0763285]` is from Phase 17 / CC-49 (`notes/phase17/erdos-borwein-bias.md` line 72). | Replace "Phase 14's $[2.0762592, 2.0763285]$" with "Phase 17's (CC-49) $[2.0762592, 2.0763285]$". |
| m9 | Note 19, 34, 265–275, 435 | Lines 19, 34, and 435 write $K_{\rm e}, K_{\rm o}$ without defining them, while Theorem 3.3 and Corollary 3.4 define and use $E_M, O_M$. | Unify notation across summary, §3, and §13 (either $E_M, O_M$ or define $K_{\rm e}, K_{\rm o}$). |
| m10 | Note 20, 265, 277, 289, 370 | Theorem 3.3's asymptotic equations (line 271), Proposition 3.5's equal-mean conclusion (line 283), and Theorem 4.1(d)'s conditional-density clause (line 294) invoke Theorem 3.2(a)/(c), hence depend on Wirsing (External input), yet their theorem headers omit `with External input (Wirsing)` and §7 line 370 omits them from the `Where` column. Line 20 omits the name "Wirsing". | Add `with External input (Wirsing)` to those headers (or tag the asymptotic parts separately from the finite exact identities) and list Thm 3.3, Prop 3.5, Thm 4.1(d) in §7 line 370. |
| m11 | Note 292, 294, 303, 307; Script 435, 458 | Theorem 4.1(b) states the sharper bound $2 K^*(N) + c_N^*$ (in fact $2 K^*(N) + \mathbf{1}[c_N^* \ge 1]$), whereas Script line 435 tests `2*(Ks + cs[NB]) + 1` (with message `<= 2K*+1`) and Note line 307 reports `2(K*+c*_N)+1 = 15967` (the actual $2 K^* + c_N^*$ at $N=2^{17}$ is $15966$, since $K^* = 7983, c^*_{2^{17}} = 0$). Also, Theorem 4.1(d)'s final conditional-density sentence omits the two-line proof that $K^*(N) = o(N)$ implies $\sum_{j \le N}(r_j^* - 1)^+ \le 2K^*(N) = o(N)$, making $n \mapsto q(n)$ injective off $o(M)$ exceptions. | Check `mism <= 2 * Ks + cs[NB]` in Script line 435, update line 307 to `15966`, and add the two-line injectivity justification to the proof of Theorem 4.1(d). |
| m12 | Note 315; Script 442 | The `7709` collision columns checked in Script lines 439–448 range over all $n \le \text{NMAXN} = 65{,}594$ ($q \le 131{,}186$), including 8 columns in the guard region $q > 2^{17}$ (`7701` have $q \le 2^{17}$). | Write "All $7709$ collision columns from $n \le 65{,}594$" (or restrict to $q \le 2^{17}$ and report `7701`). |
| m13 | Note 3, 378; Script 272, 274–275, 482, 496–497, 888–891 | Three floating-point sanity assertions in Section 8 (lines 888–891) increment the `exact checks` counter, and Sections 2 and 5 use `math.log2` (lines 272, 274–275) and float `/` (line 496) inside certificate checks. Also script line 482 says `+ O(1)` where the proved bound is $+ s_2(T_N) = O(\log N)$. | Separate `CHECKS` from Section 8 float checks, replace `math.log2` and `/` in Sections 2 and 5 with exact integer checks (e.g. `acc <= len(offs) * Kpref[NB]`), and change `+ O(1)` to `+ O(log N)` in line 482. |
| m14 | Note 24, 326, 340, 363, 405, 408 | Small precision items: (i) line 326 heuristic $C \approx 1/(4\pi)$ treats the increments $\omega(n+d)-\omega(n)$ and $\omega(n+d')-\omega(n)$ as independent, whereas independent $\omega(n), \omega(n+d), \omega(n+d')$ give covariance $\begin{pmatrix} 2L & L \\ L & 2L \end{pmatrix}$ ($\det = 3L^2$) and $C \approx 1/(2\sqrt{3}\pi)$; (ii) line 340 invokes irreducibility at the boundary Law A ($s=0$), where the 3-state chain is unichain (state 2 transient), though continuity still holds; (iii) line 405 header $\mathbb{E} c^{(W)}$ reports mark/J-carries $\mathbb{E} c^{J,(W)}$ ($0.631$ for $E(4)$), not bit carries ($0.2649$ on line 413); (iv) line 408 base-4 probabilities sum to $0.9990$ ($E(2)$) / $0.9995$ ($E(4)$) due to `UM=127` truncation; (v) §6 line 363 can cite LeVeque (1949, *Trans. AMS* 66, 440–463) as the original source of bivariate Erdős–Kac alongside Elliott (1980). | Apply these five minor textual clarifications. |

---

## 5. Scope of review and residual risk

- **Inherited results not re-proved here (audited in earlier phases):** Phase 24 Theorem 4.1 ($C_{\rm true} \in [1.339103, 1.339116]$), Lemmas 3.1–3.2, Corollary 3.3, Proposition 2.4(5), Proposition 10.2; Phase 14 tail-mean identity on dyadic windows; Phase 17 (CC-49) $D=16$ certificate and countermodels.
- **External inputs checked at hypothesis level:** Wirsing's mean-value theorem (1967) and bivariate Erdős–Kac for fixed shifts (LeVeque 1949; Elliott 1980). Both are classical published theorems whose hypotheses are verified for every application in this note.
- **Platform:** Script executed on Windows (CPython) as pure Python standard library; no Lean or LaTeX build artefacts are part of Phase 25 Track A.
- **Cross-model review is not independent human peer review.**

---

## Post-Repair Verification

**Re-audited files.** [`notes/phase25/e4-carry-correlations.md`](../e4-carry-correlations.md) (454 lines; SHA-256 `BF11420CEB909FEBE85DC0543A190B44CC8F6FB5D7DE9A4255617FFB804466C8`) and [`scripts/phase25_e4_carries.py`](../../../scripts/phase25_e4_carries.py) (1025 lines; SHA-256 `A88A5351003E0AF5B29C654B102263E6C8EE4B6F2E19BAFBDAC0FC823B7A59F1`) on branch `research/phase-25-carry-correlations`.

**Post-Repair Verdict: ACCEPT** (0 Critical, 0 Major, 0 Minor remaining).

> **Cross-model review is not independent human peer review.** This post-repair verification is a second machine reading by a model from a different provider than the author. It does not replace independent human peer review, and none of its conclusions may be used to change a benchmark status.

### Script reproduction

Running `python -B scripts/phase25_e4_carries.py` exited with code **`0`** and printed:

```text
ALL CHECKS PASSED: 2513921 exact checks (plus 3 floating-point sanity checks of the heuristic model) in 9 s
```

No floating-point operation remains inside any `check()` assertion across Sections 1–7; the three Section 8 heuristic sanity checks are routed through `float_sanity()` with a separate counter.

### Finding closure summary

- **M1 (Closed):** Theorem 1.2 (lines 101–111, 127) now separates the explicit $O(\log^2 N / N)$ error on $\frac1N \sum_{n \le M} s_2(\tau(n)) - \frac{K(N)}{N}$ from the $+o(1)$ error when passing to $C_{\rm true}/2$ and $\mu/2$, and explicitly notes why $O(\log^2 N / N)$ (and any $O(X^\vartheta)$ for $\vartheta < \frac12$) is false.
- **M2 (Closed):** `scripts/phase25_e4_carries.py` adds exact integer floor/ceiling formatters `dec_lo`, `dec_hi`, and `quoted_interval` (lines 67–98) and asserts every decimal endpoint, threshold, and margin quoted in the note (lines 720, 849–855, 871–898). All previously inward-rounded intervals and thresholds in the note are now outward-rounded: $\mu \in [2.07632553, 2.07632693]$, $B_2 \in [0.520615, 0.520617]$, $B_4 \in [0.424560, 0.424563]$ ($\limsup f_1 \le 0.424563$, $D^- \ge 0.075437$), $B_7^{(1)} \in [0.502089, 0.502097]$, $B_8^{(1)} \in [0.497099, 0.497108]$, margin $\frac12 - B_8^{(1)} \ge 2.89 \cdot 10^{-3}$, criterion thresholds `< -0.019082`, `< 0.240459`, `< 0.370229`, `< 0.435114`, and certified outward-rounded $\mathbb{E}_{Q_W^{(1/2)}}[R/2^W]$ intervals.
- **m1–m14 (All Closed):**
  - **m1:** Theorem 1.2 (lines 96, 99, 118–121) and Theorem 1.5 (line 146) state the analytical remainder $\frac{1}{2N\ln 2}$ (noting $< 0.001$ for $N \ge 722$); `Bc = 5` is checked in exact integers via $J_0^{16} \le 2^{16(4B_c-2)-1}$ (script lines 334–341).
  - **m2:** §0 (line 65) and Theorem 1.4 proof (line 142) restrict $Z(N)$ to positive indices $1 \le j \le N - \ell(T_N)$ (with $Z(N) = 0$ if $\ell(T_N) \ge N$).
  - **m3:** Theorem 1.4(c) (line 137) specifies "when a carry enters bit $\ell(T_N)$, and $0$ otherwise."
  - **m4:** §0 (line 53) and Lemma 1.1 (line 73) explicitly require $a_j \in \mathbb{Z}_{\ge 0}$.
  - **m5:** Theorem 1.5 (line 152) fixes "$o(N)$" $\to$ "$o(1)$", writes $W = W(N)$ with $W(N) - \ell(N) \to \infty$, and specifies weak limits on $[0, 1]$ vs $\mathbb{R}/\mathbb{Z}$.
  - **m6:** Theorem 2.3 (lines 214, 216) excludes $\{o(n) > T\} \cup \{o(n+d) > T\}$ and adds "$s$ squarefull" to the tail sum.
  - **m7:** Theorem 2.4, Remark 2.5, §7, and §13 parameterize $H_W^{(\lambda)}$ ($H_8^{(1)}$ for $E(2)$) and specify CC-49's distributional 16-column hypothesis.
  - **m8:** Lines 17, 254, and script lines 716–719 attribute $[2.0762592, 2.0763285]$ to Phase 17 (CC-49) and note Phase 14 proved only $\mu \le 5/2$.
  - **m9:** Notation unified to $E_M, O_M$ across lines 19, 34, §3, and §13.
  - **m10:** `External input (Wirsing)` propagated to lines 19–21, Theorems 3.3 and 4.1(d), Corollary 3.4, Proposition 3.5, and §7 line 389.
  - **m11:** Theorem 4.1(b) and script line 506 assert the sharp bound $2K^*(N) + \mathbf{1}[c^*_N \ge 1] \le 2K^*(N) + c^*_N$ (note line 326 updated to `15966`), and Theorem 4.1(d) (line 322) includes the two-line injectivity proof.
  - **m12:** Note line 334 and script lines 514–536 distinguish all `7709` collision columns from $n \le 65{,}594$ from the `7701` with $q \le 2^{17}$.
  - **m13:** `FLOAT_CHECKS` / `float_sanity()` separated from `CHECKS` / `check()`; `math.log2` and float `/` removed from Sections 2 and 5 checks; script line 561 updated to `O(log N)`.
  - **m14:** All five precision items applied (lines 345, 359, 382, 422, 424).

*(Trivial cosmetic note, non-blocking: in the certificate method list on lines 245–246 of `notes/phase25/e4-carry-correlations.md`, raw item numbers `6.` and `5.` are transposed; Markdown renders the ordered list sequentially.)*
