# Phase 25 Addendum Track I — cross-provider adversarial referee review

- **Audited files (read-only):** [`notes/phase25/naf-geometric-transfer.md`](../naf-geometric-transfer.md) (657 lines) and [`scripts/phase25_naf_transfer.py`](../../../scripts/phase25_naf_transfer.py) (1,522 lines), authored by Gemini 4 Neon (Google), branch `research/phase-25-carry-correlations`.
- **Reviewer:** Claude Opus 5.5 (Anthropic), a different provider from the author. No audited file was modified, nothing was committed, WSL was not used. This file is the only file written.
- **Scope disclaimer.** This is an automated cross-model review. **Cross-model review is not independent human peer review** (`AGENTS.md`, `docs/research-objectives.md` rule 2). None of its conclusions may be used to change a benchmark status.

## Verdict: **REVISE**

| Severity | Count |
| --- | --- |
| Critical | 0 |
| Major | 2 |
| Minor | 16 |

**Summary.** I found no mathematical error. Every theorem I checked holds as stated, every certified bound is rounded in the right direction, and every number in the note is reproduced by the script or by my independent recomputation, with the exceptions listed under Minor findings. Specifically:

- Lemma A.1 is correct.
- Theorem A.2 is correct in all four parts, including negative $A$, integer-part digits, wraparound at $0$ and $1$, the truncation $M = sN + R$ and the multi-radix generalization.
- Theorems B.1 and B.2 are correct, including the DP-free majorants below $93/100$.
- Theorem B.3 is correct: $x_*$ is genuinely 3-normal, and $m_1, \dots, m_4$ are right.
- Lemma C.1 is correct. The factor $2/3$ is unconditional and needs no Selberg–Delange or Halász input.
- The cubic and dense-family bounds in Theorems C.2 and C.3 are correct.

The verdict is REVISE for **attribution and novelty** reasons. A sibling Phase 25 note on this branch already proves several headline results of Track I: [`notes/phase25/digit-complexity-and-lp-witnesses.md`](../digit-complexity-and-lp-witnesses.md) (Phase 25 Track D, reviewed in [`track-d-review.md`](track-d-review.md)). Track I does not cite it anywhere (Major M1). The "Track E" and "Track A" enclosures for $W_+$ are also misidentified; they are the Phase 24 results `GF-40` and `GF-36` (Major M2). Both fixes are text-only.

---

## 1. Reproduction record

- `python -B scripts/phase25_naf_transfer.py` (Python 3.13.13, Windows): **exit code 0**, `ALL CHECKS PASSED (418068 assertions: 417964 [exact], 95 [encl], 9 [finite]) in 28.34 s`. This matches note lines 3, 634–638 exactly.
- **Separation of evidence kinds.** Sections 1–5 use only `int`/`Fraction` arithmetic. Floats appear only in the `[finite]` display of Section 6b (lines 1505–1506), which is isolated and labeled.
- **Rounding.** Every certified lower bound is printed with `fmt_dn` and every upper bound with `fmt_up`; intervals use `fmt_iv`. The `GF-40` ratios are floored with `int()` of an exact `Fraction`, which is the safe direction. I found no rounding-direction bug in any printed bound.
- **Reviewer-side stress tests.** These were run from the session scratchpad; nothing was added to the repository.
  1. *Randomized Theorem A.2(1).* 4,000 random $(A, M)$ with $M \le 40$, $|A|$ up to $2^{M+6}$, negative $A$, $A = \pm(2^M - c)$ and $A \approx \pm(4^{m}-1)/3$, checked for $s \in \{1,2,3,4\}$ and $r \in \{1,2,3\}$: **48,000 count checks, 0 violations**, and the bound is attained with equality 2,048 times. The strict tail bound $|S_j| < \frac23 2^{-\ell}$ was checked at every zero block with $\ell \in \{1,2,3,5\}$: 0 violations.
  2. *Witness $x_*$.* $\max_{N \le 3720} |w_\pm(\lfloor 2^N x_*\rfloor) - N/4| = 3/4$, so $w_\pm = N/4 + O(1)$ at **every** $N$, not only at $N = S_M$. The 3-word deviation $\max_w |f_N(w) - \frac18|\sqrt N$ is between $0.50$ and $0.69$ for $N \in \{100, 1000, 3000, 3720\}$.
  3. *Witness $x_4$.* $\max_N |w_\pm - 5N/16| = 5/4$.
  4. *DP-free majorants, independent code.* $M_{\{2,3\}} \le 0.929153$ (mod-6 tail) and $0.929681$ (trivial tail); $M_{\{2,3,5\}} \le 0.924468$ and $0.928395$. All four reproduce exactly. With truncation $(40, 30)$, $L_{\{2,3\}} \in [0.857009, 0.857010]$; the note's $(18, 14)$ upper bound $0.857107$ is valid.
  5. *The LP of Theorem B.3(1), solved independently with SciPy/HiGHS.* It gives $0, \frac14, \frac14, \frac5{16}$ for $L = 1, \dots, 4$, unchanged when the carries are restricted to $\{-1, 0\}$. For $L \le 8$ it gives $\frac13(1 - 4^{-\lfloor L/2\rfloor})$, which is Track D's $\bar g_L$.
  6. *Finite sanity measurements only, bearing on no limit* (rule 1). For $n \le 10^6$: the mean of $w_\pm(a_+(n))$ is $0.90810$. Modulo 7, the mean of $w_\pm(c_+)$ is $0.75689$, the mean of $w_\pm(c_-)$ is $0.50442$ (ratio $0.66644$), and the twisted mean $|X^{-1}\sum \chi^\circ(n)\,w_\pm(c_+(n))|$ is $0.00029$.
  7. *Derived numbers.* I recomputed all of $17431/300000$, $11477/187500$, $11477/437500$, the ratios $247{,}942\times$, $261{,}201\times$ and $2{,}588\times$, every row of Table 8.1, every cubic bound in Theorem C.2, and the bounds for $E_{+,\rm odd}(16)$ and $F_{2^k,+}(\tau_r)$.

---

## 2. Checklist audit

### 2.1 Lemma A.1 (NAF existence, uniqueness, and $w_{\rm rec} = w_{\min} = w_{\rm NAF}$): **correct**

- **Step 1.** Termination uses $|(A-\varepsilon)/2| \le (|A|+1)/2 < |A|$ for odd $|A| \ge 3$. Non-adjacency holds because $4 \mid A - \varepsilon$. Symmetry under $A \mapsto -A$ holds. All three are correct.
- **Step 2 (uniqueness).** The mod-4 argument $e_0 \equiv A \equiv e'_0$ after $e_1 = e'_1 = 0$ is correct.
- **Step 3, parity monotonicity.** Both inequalities $w_{\rm rec}(2q) \le w_{\rm rec}(2q+1)$ and $w_{\rm rec}(2q+2) \le w_{\rm rec}(2q+1)$ follow from $|w_{\rm rec}(q+1) - w_{\rm rec}(q)| \le 1$. The induction branches are right: $n \equiv 1 \pmod 4$ selects $w(m)$, and $n \equiv 3 \pmod 4$ selects $w(m+1)$ with $m + 1 < 2m + 1$.
- **Lean names.** The cited lemmas exist in `NormalityChecker/DigitMassTransfer.lean`:
  - `signedWeight` (l. 426), whose recursion matches note l. 51–54;
  - `signedWeight_add_le` (l. 538) and `signedWeight_sub_le` (l. 543);
  - `signedWeight_succ_le` (l. 478, **private**).

  See Minor m11 for the "self-contained" wording.

### 2.2 Theorem A.2 (general and multi-radix transfer): **correct**

- **Part (1).**
  - The integer/fraction split at $r = M - j$ is exact for every sign of $A$ and every size of $|A|$.
  - The pairing $(\ell+1+2i, \ell+2+2i)$ uses non-adjacency correctly.
  - Strictness holds because only finitely many pairs are non-empty. Moreover $\frac23 2^{-\ell}$ is not dyadic, so the endpoint is never hit.
  - The sign cases $S_j \ge 0$ and $S_j < 0$ handle wraparound correctly: $\lfloor S_j\rfloor = -1$ when $S_j < 0$.
  - Each $u \in \mathcal S$ meets exactly $r$ multiples of $s$ in $[M-u-sr, M-u-1]$, and $j = sm < sN \le M$.
  - Integer-part digits $u \ge M$ never enter, as l. 315 says.
- **Part (2).**
  - $\delta_m < 2^{sm - M} \le 2^{-R-1}$ follows from $sm \le M - R - s$.
  - On $I_{sr,R}$ the shadow point lies in $(\frac23 2^{-sr} + 2^{-R-1},\, 1 - \frac23 2^{-sr})$, so it does not wrap.
  - $I_{sr,R}$ is non-empty because $\frac23 2^{-sr} + 2^{-R} \le \frac7{12} < \frac23$.
  - Passing to the limit along $M = sN + R$ gives the factor $s$, since $(sN + R)/N \to s$.
- **Part (3).**
  - The bound $\Theta_Q \le 2^{\varepsilon Q}/(2^{k-\varepsilon}-1) < 3 \cdot 2^{\varepsilon Q}$ is correct.
  - $|\tau_M| \le 2^{k-1}\Theta_Q$, and $w_\pm(\lfloor\tau_M\rfloor) \le \log_2(|\tau_M|+2) \le k + \log_2(1+\Theta_Q)$.
  - $Q/M \le 1/k$ then gives $\bar w_\pm(x) \le C/k$.
- **Part (4).**
  - $g_{\ell+1} - g_\ell = \frac23 2^{-\ell} - \rho$, with the stated maximizer intervals.
  - $1 - \sup_\ell g_\ell \le \rho\log_2(16/(3\rho))$.
  - Comparison with `GF-36`: at $\ell = 2(m-1)$ the intercept $1 - \frac13 2^{4-2m}$ exceeds $1 - 2^{1-m}$ exactly when $8 < 3 \cdot 2^m$.
  - The `GF-36` window bound $1 - 2^{1-m} - (m-1)\frac{2W}k$ matches `notes/phase24/dense-digit-mass-and-lambert.md`, Theorem 7.1 (l. 295–301).
- **Radix descent.** Lean `radixDiscrepancy_descent` (l. 2417) states $D_{kN}(x;b) \le \frac{b^k-1}{k(b-1)} D_N(x; b^k)$. This gives $D^-(x;8) \ge \frac37 D^-(x;2)$, the direction the note uses.

### 2.3 Theorems B.1–B.3: **correct** (attribution under M1 and M2)

- **$W_+$ enclosures.** The script independently reproduces $[0.907252, 0.912845]$ and $[0.908174, 0.908184]$. I traced the soundness of the "Track E" truncation: the lost-mass recursion, the bound $u_{\rm tail} = x^K(K + p/(p-1))$, and the identity $\sum_{e \ge K_2}(e-1)2^{-(e+1)} = K_2 2^{-K_2}$. Its three undocumented tail constants are valid; see m4.
- **Tail and DP engine.** The tail lemma in `CertifiedEulerProduct`, `tail_A` (both signs) and the frozen-state handling in `certified_model_dp` are all sound for $g(e) \le c(e+1)^d$ with $E \ge 3d$.
- **Derived bounds.**
  - $D^- \ge \frac23 - \frac23 W$ gives $17431/300000$ and $11477/187500$ exactly.
  - Radix descent gives $11477/437500 \ge 0.026233$.
  - For order 4: $[3/16, 13/16) \subset (1/6, 5/6)$ with margin $1/48 > 2^{-6}$. It is the union of 10 binary length-4 cylinders and of 10 base-4 length-2 cylinders. The bound $2W_+/3 \le 0.605456 < 0.625$ holds.
  - For $k \ge 4$: $2W_+/k \le 0.454092 < \frac12$ on $[\frac14, \frac34) \subset (\frac16, \frac56)$, and $3W_+/k \le 0.681138 < \frac34$ on $[\frac18, \frac78) \subset (\frac1{12}, \frac{11}{12})$. Both hold.
  - The Track B thresholds being lowered (base 4 at $k \ge 8$, base 8 at $k \ge 5$) match `generalized-lambert-and-eplus.md` l. 24 and l. 500.
- **Theorem B.2(1).** The floor $G \ge G_0$ for every multiplicative majorant is correct, and $G_0$ is itself a majorant by submultiplicativity. The value $[0.936414, 0.936415]$ is `GF-36` Thm 7.2; see M2.
- **Theorem B.2(2).**
  - The local factor $(1-x)\sum_e s_2(e+1)x^e = \sum_e (1 - v_2(e+1))x^e$ equals $(1-x^2)^{-1} - x^3 - 2x^7 - x^{11} - 3x^{15} - \cdots$, and every omitted coefficient is $\le 0$. Hence $B(p)$ is a valid local bound, matching Lean `local_kernel_le` (l. 1399) and `localBound` (l. 1629).
  - The telescoping tail $\sum_{m \ge M}\bigl((6m-1)^{-2} + (6m+1)^{-2}\bigr) < 1/(3(6M-7))$ is correct.
  - The tails $1/627$ (first tail prime $223 \ge 215$) and $1/141$ (first tail prime $53 = 6 \cdot 9 - 1$) are correct.
  - The trivial tails $600/599$ and $112/111$ match `sum_Ico_inv_sq_le`, which bounds $\sum_{[M,P)} n^{-2} \le 1/(M-1)$.
  - The moment identities $1$, $3/2$, $5/4$ and the tail identities are exact.
  - The Möbius kernel factors as $h_{2,3} \cdot h_{\ge5}$ with $h_{\ge 5}(p^e) = 1 - v_2(e+1)$, which is supported on squarefull numbers. This fits the hypothesis of `tendsto_average_of_summable_conv_mobius` (l. 1021–1023).
  - The prime count is wrong: **45 primes, not 44** (m1).
- **Theorem B.3, the focus question.**
  - $x_* = 0.\prod_{m\ge1}(\mathtt{0001})^m(\mathtt{1110})^m$ **is 3-normal**. The block $(\mathtt{0001})^m$ produces exactly $\{000, 001, \mathbf{010}, 100\}$, and $(\mathtt{1110})^m$ produces exactly $\{111, 110, \mathbf{101}, 011\}$. The two block boundaries per block add one extra $000$ and one extra $111$ and remove one $010$ and one $101$. The counts at $S_{40} = 6560$ are $[859, 820, 780, 820, 819, 780, 820, 860]$, a deviation of exactly $\pm M = \pm 40$, which is $O(\sqrt N)$. A partial block has length $< 8(M+1) = O(\sqrt N)$. So $f_N(w) = \frac18 + O(N^{-1/2})$ for all 8 words, including $010$ and $101$.
  - The closed-form NAF of $B_m$ is correct. The exponent gaps are $4, \dots, 4, 3, 5, 4, \dots, 4, 3$, and the gap between consecutive blocks is $5$. The weight is $2m$, so $w_\pm(\lfloor 2^{S_M}x_*\rfloor) = M(M+1) = S_M/4$ exactly.
  - At intermediate $N$ the deviation is at most $3/4$ (stress test 2), so the limit really is $\frac14$.
  - $x_4 = 2479/65535$ is the order-4 de Bruijn word $\mathtt{0000100110101111}$. Its NAF is $2^{11} + 2^9 - 2^6 - 2^4 - 1$, the wrap gap is $5$, and the weight is $5m$ on $16m$ bits.
  - The lower bounds $\frac14$ from $[\frac14, \frac34)$ and $\frac5{16}$ from $[\frac3{16}, \frac{13}{16})$ are correct, and the limitation corollary follows.
  - $m_1 = 0$ via $E_2$ is correct: `GF-03` shows $E_2$ is simply normal in base 2, and its runs cost $O(1)$ signed digits per block.
  - **These results duplicate Track D, Theorem 1.7**; see M1.

### 2.4 Lemma C.1 and Theorems C.2–C.3: **correct**

**Lemma C.1, step by step.**

- $\chi^\circ$ is completely multiplicative and never zero.
- The convolution identity $\sum_{n \le X}\chi^\circ G = \sum_{d \le X}\chi^\circ(d)H(d)\sum_{m \le X/d}\chi^\circ(m)$ is exact.
- Write $m = s \cdot m'$ with $s$ an $M$-smooth number and $\gcd(m', M) = 1$. This gives $\bigl|\sum_{m \le Y}\chi^\circ(m)\bigr| \le M \cdot \#\{M\text{-smooth } s \le Y\} \le M(\log_2 Y + 1)^{\omega(M)}$.
- Finally $\sum_{d \le X}|H(d)| \le X^\sigma\sum_d |H(d)|d^{-\sigma}$.

The displayed bound is correct.

**Why no Selberg–Delange is needed.** $G_\chi(p) = U_\chi(p) = 1$ at **every** prime, including $p \mid M$ and $\chi(p) \in \{\omega, \bar\omega\}$. Hence $H = G * \mu$ is supported on squarefull numbers, and $\sum|H(d)|d^{-3/4} < \infty$ because $|H(p^e)| \le e + 1$ and $\sum_p p^{-3/2} < \infty$. Bounded character sums then suffice. Selberg–Delange would be needed only if $G(p)$ took a value other than 1 on a set of primes of positive density.

**The phase table.**

- $c(p^e) \in \{1, e^{\pm i\pi/3}, 0\}$ at primes with $\chi(p) \in \{\omega, \bar\omega\}$.
- $e^{2\pi i t(n)/3} = \chi^\circ(n)$ on the support of $c$.
- $c_+/A \in \{2, 1, -1, -2, -1, 1\}$ and $c_-/A \in \{0, 1, 1, 0, -1, -1\}$.
- $\mathbf 1_{\chi^\circ \ne 1} = \frac23 - \frac13\chi^\circ - \frac13\overline{\chi^\circ}$.

All four are correct.

**Bounds by majorant.** The pointwise inequality $w_\pm(c_-) \le \mathbf 1_{\chi^\circ \ne 1}G_\chi$ plus Lemma C.1 for $G_\chi$ gives $\limsup X^{-1}\sum w_\pm(c_-) \le \frac23 W_\chi$, and similarly $\frac23 C_{\rm odd}$ using $w_\pm(A) \le s_2(A) \le \operatorname{odd}(A)$.

**The exact identity with $W_{\chi,\rm true}$.** This is also correct:

- $\rho$ has a summable kernel. Its kernel is $-1$ at primes $p \le y$, and at primes $p > y$ it is $-1$ at $p^2$ (when $\chi(p) = 1$) and $0$ at $p$.
- $F(mr) = F(m)$ for $y$-good integers.
- The sum over $y$-smooth $m$ of $F(m)m^{-\sigma}$ is finite.

The tail estimate as $y \to \infty$ is only sketched; see m13.

**Certified bounds, Theorem C.2.** All are reproduced:

- $L_-(4)$ and $L_+(8)$: $0.162063 / 0.162085$, $0.130323 / 0.130347$, $0.140457 / 0.140559$, and $0.150267$, $0.165885$ for moduli 19 and 37.
- $L_+(8)$ in base 8: $0.076428$ (direct), $0.055852$ and $0.060196$ (descent).
- $L_-(8)$: $0.330264$, $0.309104$, $0.315860$; in base 8, $0.328730$, $0.296989$, $0.307124$; via $W_{\rm true}$, $0.330279$, $0.309120$, $0.315928$.

The characters are correct:

- $\chi(3) = \omega \bmod 7$ with cube residues $\{\pm1\}$;
- $\chi(2) = \omega \bmod 9$, primitive, with cubes $\{\pm 1\}$;
- $\chi(2) = \omega \bmod 13$ with cubes $\{\pm1, \pm5\}$;
- for moduli 19, 37, 31 and 43, the cubic-residue subgroup.

The optimizer $\ell^* = 2$ is correct; for example, $\rho = \frac29 W_7 = 0.16820 > \frac16$.

**Theorem C.3.**

- The divisor-sum case analysis for $a_+^*$ and $a_{\rm alt,+}^*$ is correct, and the mean is exactly $\frac34$.
- At $k = 3$: $\rho = \frac14$ gives $\frac16$ in bases 2 and 4 and $\frac1{12}$ in base 8. At $k = 4$: $\frac7{24}$.
- $a_{+,\rm odd}(n) = (-1)^{n-1}\tau_{\rm odd}(n)$.
- For $F_{2^k,+}(\tau_r)$, multiplicativity holds because the sign depends only on the 2-part. The hockey-stick formula for $a(2^e)$ is correct, and the 2-adic tail $(E + r + 2)2^{-(E+1)}$ is correct.
- The thresholds $k \ge 4, 6, 8$ and the order "not 6-normal" at $k = 6$ are correct: $[11/64, 53/64)$ has length $0.65625 > 2\rho = 0.65295$.

### 2.5 Sections, labels, and prior art

- **Structure.** All 10 numbered sections are present, plus the Results table.
- **Labels and scope.**
  - The evidence labels follow the repository list. "Finite measurement" is used for §8.2, as in other Phase 25 notes.
  - The benchmark-stability statement (l. 12) and the cross-model disclaimer (l. 11) are present.
  - The open status of base-2 simple normality of $E_+(8)$ is stated correctly.
- **Literature.**
  - Reitwiesner (1960), *Advances in Computers* 1, 231–308, is credited correctly, as are Booth, Avizienis, Erdős, Borwein and Maxfield.
  - The `GF-31` Thm 4A attribution for $L_-(8)$ is honest: base-8 simple nonnormality is `GF-31` with Selberg–Delange, and the new content is the zero-external-input proof (l. 225, 474). This matches the `GF-31` registry entry and `GF-36` Prop 8.1 (phase24 note l. 336).
- **The defects.**
  - Phase 25 Track D is never cited (M1).
  - "Track A" and "Track E" are not identified as `GF-36` and `GF-40` (M2).
  - Smaller attribution slips appear in m9, m10 and m14.

---

## 3. Findings

### Critical

None.

### Major

**M1. Phase 25 Track D is not cited, and several novelty and priority claims duplicate it.**

[`digit-complexity-and-lp-witnesses.md`](../digit-complexity-and-lp-witnesses.md) is on the same branch and was reviewed in `track-d-review.md`. It already contains the following.

- **Theorem 1.2.** For every real $x$ and $N$: $-2 \le 2\sigma_1(x;N) - \#\{n < N : \{2^nx\} \in [\frac16, \frac56)\} \le 1$. This is a two-sided exact form of A.2(1)–(2) at $\ell \le 2$.
- **Theorem 1.7.** $\bar g_L = \frac13 - \frac13 4^{-\lfloor L/2\rfloor}$, and every $L$-normal $x$ satisfies $\bar g_L \le \liminf \sigma_1/N$.
  - The lower end is attained for $4 \le L \le 10$ by periodic (de Bruijn) $L$-normal numbers.
  - For $L \in \{2, 3\}$ it is attained by **the identical witness** $B_n = (0001)^n(1110)^n$, $x = 0.B_1B_2B_3\cdots$ (Track D l. 180).
  - $\sigma_1(x;N)$ and $w_\pm(\lfloor 2^N x\rfloor)$ differ by $O(1)$, so $m_L = \bar g_L$. This covers Track I's $m_1, \dots, m_4$.
- **Theorem 2.3 and Lemma 2.4.** $D^-(x;2) \ge 2(\frac13 - \limsup\sigma_1/N)$, together with the series transfer. This is Track I's $\ell = 2$ bound and the extension of the threshold from $\frac14$ to $\frac13$.
- **Theorem 2.5.**
  - $D^-(E_+(8);2) \ge 17431/300000$, and $\ge 0.061210$ with the `GF-36` mean.
  - $E_+(8)$ is not 4-normal in base 2 and not 2-normal in base 8.
  - $D^-(E_+(16);2) \ge 0.2125$.
  - **$L_+(8)$ is nonnormal in base 2**, with $D^- \ge 0.1620, 0.1303, 0.1404$, and is not 4-normal.
  - A Selberg–Delange-free proof of nonnormality of $L_-(8)$.
- **Track D l. 304.** The order-3 limitation: "not 4-normal is the strongest finite-order conclusion this input can give."

The following Track I passages are therefore wrong as priority claims:

- l. 20 ("extends the threshold from 1/4 to 1/3");
- l. 22 and l. 140 (the "$> 261{,}000\times$" boost as new);
- l. 24 (I.B3);
- l. 25 ("Classifies $L_+(8)$ (new at $k=3$)");
- l. 183 and l. 224 ("$L_+(8)$ … NEWLY CLASSIFIED!");
- l. 475 (provisional novelty: tail-bound transfer, order-4 nonnormality, the sharp order-3 barrier, $L_+(8)$);
- l. 646 ("First unconditional proof of binary order-4 nonnormality … of $E_+(8)$");
- l. 648 (Objective 4).

Open Question 5 (l. 656) is also partly settled already. Track D Thm 1.7(2) proves $m_L \ge \bar g_L$ for **all** $L$ and attainment for $L \le 10$; only attainment for $L > 10$ is open (Track D's own Question 2). My HiGHS run of Track I's own LP reproduces $\bar g_L$ for $L \le 8$.

**Fix.**

- Cite Track D (Thms 1.2, 1.7, 2.3, 2.5, 2.6, Lemma 2.4) in §4 and in the Results table.
- Recast Theorem B.3 as an independent NAF-language re-derivation of Track D Thm 1.7 for $L \le 4$, or reduce it to a remark.
- Remove "first", "NEW" and "NEWLY CLASSIFIED" for $E_+(8)$ order 4, the $\frac{11477}{187500}$ boost, $L_+(8)$, and the order-3 barrier.
- Restate OQ5 as attainment for $L > 10$.
- Restrict the novelty claims to what is genuinely added here:
  - Lemma C.1 and the elementary factor $2/3$;
  - $L_-(4)$ at $k = 2$ for moduli 7, 9, 13, 19, 37. Track D's route gives $\rho = W_\chi/2 > \frac13$ there and fails;
  - the sharpened $L_-(8)$ bounds ($\approx 0.33$) and its simple nonnormality in base 4;
  - the multi-radix $2^s$ transfer and simple nonnormality of $E_+(2^k)$ in bases 4 and 8 for $k \ge 4$;
  - the general-$\ell$ improvement for $\ell \ge 3$ at small $\rho$;
  - the DP-free majorants below $93/100$;
  - the families of Theorem C.3;
  - $E_+(8)$ not 2-normal in base 4.

**M2. The "Track E" and "Track A" enclosures are misidentified, and the Phase 24 sources are never named.**

- $W_+ \in [0.907252, 0.912845]$ is `GF-40`, Thm 3.1(a). This is *Phase 24* Track E, `notes/phase24/classical-constants-and-joint-numerators.md` l. 47 and l. 537.
- $W_+ \in [0.908174, 0.908184]$ and $W_+^{\rm maj} \in [0.936414, 0.936415]$ are `GF-36`, Thm 7.2. This is *Phase 24* Track A, `notes/phase24/dense-digit-mass-and-lambert.md` l. 307–312.
- The enclosures for $W_\chi$ in Theorem C.2(1) are `GF-36`, Prop 8.1 (l. 336).

In a Phase 25 note, "Track A" and "Track E" read as Phase 25 Tracks A and E, which are unrelated notes (Phase 25 Track A is `e4-carry-correlations.md`). The labels occur at l. 22, 134–135, 140, 376 and 637. Theorem B.2(1) presents $W_+^{\rm maj}$ as if newly certified.

**Fix.** Write "re-certification of `GF-40` Thm 3.1(a)" and "re-certification of `GF-36` Thm 7.2 / Prop 8.1", and keep the label "independent re-certification".

### Minor

| # | Location | Finding | Fix |
| --- | --- | --- | --- |
| m1 | Note l. 23, 158, 396, 600; script l. 686, 695, 751 | There are **45** primes with $5 \le p \le 211$, not 44. The computation uses all 45, so $0.929153$ is correct | Replace 44 with 45 |
| m2 | Script l. 705–706 | The comment says "27 primes $7 \le p \le 109$"; the count is 26, as l. 732 and the note say | Fix the comment |
| m3 | Script l. 569–570, l. 1126 | The assertions $W_+^{\rm maj} \le 0.936416$ and $W_{13} \le 0.789315$ are weaker than the note's claims $0.936415$ and $0.789314$. The printed `fmt_up` values do support the claims | Assert the endpoints the note states |
| m4 | Script l. 525–530, 539–543; note l. 376 | The Track E tail constants $\sum_{p>600}p^{-2} \le \frac1{1200}$, $\mathbb E[V\mathbf 1_{V\ne1}] \le \frac5{1200}$ and $\mathbb E[V] \le 1 + \frac2{600}$ are neither documented nor asserted. The only "tail" check (l. 525) tests an irrelevant inequality. I verified all three: telescoping over odd $n \ge 601$ gives the first; $\le 3.01/1200$ and $e^{2/1200}$ give the others | Document them and assert the actual telescoping inequality |
| m5 | Note Table 8.2, l. 588–591 | The $L_-(4)$ column $D^-(\cdot;8)$ ($0.06946$, $0.05586$, $0.06023$, $0.06440$, $0.08216$) is not produced by the script and mixes methods. Modulo 7, $0.06946$ (descent) is weaker than the direct $\frac56 - W_\chi \ge 0.076428$ used for $L_+(8)$ in the same table, although $\rho$ is identical | Compute it in the script and use $\max(\text{direct}, \text{descent})$ uniformly |
| m6 | Table 8.1 caption l. 568; Theorem C.2 l. 219–220 | Several lower bounds come from *unrounded* certified endpoints and exceed what the displayed 6-digit enclosure gives by $10^{-6}$. Examples: $k=4$ gives $0.212575$ vs $0.212574$ from $0.908184$; also $0.288423$, $0.070983$, $0.462575$, $0.086608$, $0.090514$, $0.091796$, $0.091816$; modulo 9, $0.130323$ vs $0.130322$; modulo 13 via $W_{\rm true}$, $0.140559$ vs $0.140558$. All are script-certified and valid | State "from the unrounded certified endpoint", as B.1(1) already does for $0.0612111$ |
| m7 | Note l. 621 | "consistent with our Theorem B.3 barrier" reads finite statistics against an asymptotic theorem | Delete the interpretive clause (rule 1) |
| m8 | §7, l. 503–560; l. 45 | Lean blueprint defects. `nafDigitAt` is undeclared. `erdosBorweinPlus` does not exist; only `erdosBorweinPlusCoeff` (`Phase22Cores.lean` l. 984) does. `localBound`, `local_kernel_le`, `sum_Ico_inv_sq_le`, `prod_one_add_mul_le` and `signedWeight_succ_le` are **private**, so a separate `NafGeometricTransfer.lean` cannot reuse them. In `naf_zero_block_tail_lt` the ℕ-subtraction `M - j - t` truncates to 0, which wrongly forces `nafDigitAt A 0 = 0` when $\ell > M - j$. `sum_Ioc_mul_zeta_eq_sum` is not in the repository. The "~250" and "~40 lines" figures are unsupported. `radixDiscrepancy` is in `BinaryDiscrepancy.lean` (l. 11), not `DigitMassTransfer.lean` | Correct the names; use ℤ indices; make the lemmas public or co-locate the code; drop the line-count estimates |
| m9 | l. 26, 242, 243 | "from $k \ge 5, 8, 10$ (`GF-36`)" and "`GF-36` Thm 7.1 required $k \ge 5$". `GF-36` treats only the *unsigned* $\tau_r$ and $E_{\rm odd}$ series (Thm 6.1–6.2). These thresholds are what the $\rho < \frac14$ criterion of `GF-36` would give with this note's majorants | Rephrase as "the `GF-36` Thm 7.1 criterion would require" |
| m10 | l. 25, 208 | "Resolves the previously open $k = 2$ constants $L_-(4)$". What `GF-31` lists as open is simple normality of $L_-(4)$ in base 4, which remains open (OQ2). What is new is nonnormality with $D^- > 0$ | "First proof of nonnormality ($D^- > 0$) of $L_-(4)$" |
| m11 | l. 8, 20, 263–264, 483 | "Completely self-contained": Step 3(2) relies on the kernel-verified `signedWeight_add_le` and `signedWeight_sub_le`, a non-trivial strong induction that is not reproduced. The sketch of the neighbor inequality in Step 3(3) is incomplete | Call it a repository (Lean) input, or give the paper induction |
| m12 | l. 176, 485 | The note never says why the LP of Theorem B.3 is a valid relaxation. It is: NAF conversion uses carries in $\{-1, 0\}$, and the empirical edge measures of prefix paths converge to stationary flows with uniform $L$-word marginals, so $\mathrm{LP}^* \le \liminf w_\pm/N$ | Add this argument, or label the LP as corroboration only |
| m13 | l. 449 | The $y \to \infty$ step for $W_{\chi,\rm true}$ is compressed. It needs $\sum_{n \le X,\, p^2 \mid n,\, p > y,\, \chi(p)=1}G_\chi(n) \ll X\sum_{p>y}p^{-2}$ uniformly in $X$ (from $\sum_{m \le Y}G_\chi(m) \le Y\sum_d |H(d)|/d$), and dominated convergence over $y$-smooth $m$. Both go through | Write the two estimates out |
| m14 | l. 469; §4 | "exact fixed-boundary means $\frac{\ell}{3} + \frac29$": that is the mean over uniform NAF strings of length $\ell$ (computed: $0.2219 \to \frac29$). Over integers in $[0, 2^\ell)$ the mean is $\frac{\ell}3 + \frac49$. Lemma C.1 is also an instance of a standard elementary convolution argument | Name the sample space; add a remark that the convolution technique is classical |
| m15 | l. 20, 636 | "10,656 dyadic cases; $A \in [-8192, 8192]$" conflates two ranges: the dyadic cases use $A \in [-512, 512]$ plus special values. "Brute-force minimality over all signed strings" covers only distinct-exponent strings on 8 positions | Separate the two ranges; reword |
| m16 | Table 8.2 l. 591; script l. 1198–1203 | "NOT 2-normal (b=4)" for moduli 19 and 37 is not checked by the script; only the base-2 order is checked. The claim follows trivially from the same interval | Add `lowest_excluded_order(..., s=2)` |

---

## 4. Required revisions before acceptance

1. M1: add the Track D citation, recast Theorem B.3 and Open Question 5, and correct the novelty statements in the Results table, l. 183, l. 224, §4, and §10.1.
2. M2: name `GF-40` Thm 3.1(a) and `GF-36` Thm 7.2 / Prop 8.1 for the re-certified means.
3. Minor findings m1–m16. All are text or assertion edits; none changes a theorem.

After these edits I would expect **ACCEPT WITH MINOR POLISH**. The mathematics and certificates are sound. The genuinely new contributions remain valuable:

- the elementary factor $\frac23$ that removes Selberg–Delange;
- nonnormality of $L_-(4)$ at $k = 2$ for moduli 7, 9, 13, 19, 37;
- simple nonnormality of $E_+(2^k)$ in bases 4 and 8 for $k \ge 4$;
- the DP-free majorants below $93/100$, ready for Lean;
- the new signed families of Theorem C.3.

*Cross-model review is not independent human peer review.*

---

## Post-Repair Verification

- **Re-audited files (read-only, not modified):** [`notes/phase25/naf-geometric-transfer.md`](../naf-geometric-transfer.md) (715 lines, SHA-256 `07690bb6…4cd3`) and [`scripts/phase25_naf_transfer.py`](../../../scripts/phase25_naf_transfer.py) (1,558 lines, SHA-256 `81689d2d…0829`), branch `research/phase-25-carry-correlations`.
- **Verifier:** Claude Opus 5.5 (Anthropic), a different provider from the author. Only this section was appended. All lines above it are unchanged byte-for-byte. Nothing was committed, and WSL was not used.
- **Scope disclaimer.** **Cross-model review is not independent human peer review.** This verification authorizes **no** benchmark status change (`AGENTS.md`, `docs/research-objectives.md`). The 50-constant roster `BC-01`…`BC-50` and `arithmetic-families.toml` stay as they are.

### Verdict: **ACCEPT**

| Severity | Original | Remaining after repair |
| --- | --- | --- |
| Critical | 0 | 0 |
| Major | 2 | **0** |
| Minor | 16 | **0** |
| New nits (non-blocking) | — | 5 (N1–N5 below) |

### V1. Reproduction (Windows, native Python 3.13.13; no WSL)

- `python -B scripts/phase25_naf_transfer.py` gives **exit code 0** and `ALL CHECKS PASSED (418091 assertions: 417978 [exact], 104 [encl], 9 [finite]) in 27.34 s`. These counts match note l. 3, l. 541–542 and l. 693–696 exactly. The note's timings (~29 s and ~28.7 s) agree with the run.
- **No floats before `# 6b. [finite]` (script l. 1517).** I parsed the script with Python's `ast` module and scanned everything before l. 1517 for float literals, `float(`/`round(` calls, `math.*` calls, and negative-exponent `**`. All four counts are **zero**. Every true-division node before l. 1517 (40 sites) has a `Fraction` operand: an explicit `Fraction(...)`, a `Fraction`-valued enclosure endpoint, or an entry of the exact-`Fraction` simplex tableau at l. 818–860. Hence no `int / int` division produces a float. Floats appear only in the isolated `[finite]` display of §6b.
- **Printed values match the note.** I compared every printed value with the note and found **no mismatch**:
  - `GF-40` and `GF-36` enclosures, $\frac{17431}{300000}$, $\frac{11477}{187500}$, and the ratios $247{,}942\times$ and $261{,}201\times$;
  - the $W_+^{\rm maj}$ interval $[0.936414, 0.936415]$ and the four DP-free majorants (0.929153, 0.929681, 0.924468, 0.928395, with prime counts 45, 107, 12 and 26);
  - all 9 rows × 7 columns of Table 8.1;
  - LP values $0, \frac14, \frac14, \frac5{16}$, the $x_*$ counts `[859, 820, 780, 820, 819, 780, 820, 860]`, and $x_4$;
  - every cubic enclosure and bound for moduli 7, 9, 13, 19, 37, 31 and 43, covering Theorem C.2(1)–(5) and Table 8.2. This includes the new base-8 column, for which I recomputed $\max(\frac56 - W_\chi,\ \frac37 D^-(\cdot;2))$ by hand for all five moduli. Direct wins at 7 and 37; descent wins at 9, 13 and 19;
  - the Theorem C.3 values (1.176328…, 1.157843…, 0.078501 and 0.087720, and the three $F_{2^k,+}(\tau_r)$ rows with thresholds 4, 6 and 8);
  - the 9 × 6 values of Table 8.2 §8.2.

### V2. Closure of Major findings

**M1: CLOSED.**

*Track D is now cited.* The sibling Track D note is cited with the requested theorem numbers (1.2, 1.7, 2.3, 2.5, 2.6, Lemma 2.4) in:
- the scope bullet (l. 8);
- the Results table (I.A1, I.B1, I.B3, I.C1; l. 20–25);
- the remark after Theorem A.2 (l. 130);
- Theorem B.1 (l. 140–147), the attribution paragraph of Theorem B.3 (l. 171), and Theorem C.2(3)–(4) (l. 230–231);
- §3.4 (l. 418) and the §4 lineage entry (l. 514);
- §10.1–10.2.

I checked each citation against `digit-complexity-and-lp-witnesses.md` and all are accurate:
- Thm 1.2 is the middle-interval formula.
- Thm 1.7(2) and (4) give $\bar g_L$, attainment for $4 \le L \le 10$, and the $B_n$ witness for $L \in \{2,3\}$.
- Thm 2.3 and Lemma 2.4 give the $2(\frac13 - \alpha)$ inequality and the series transfer.
- Thm 2.5 gives $\frac{17431}{300000}$ and $0.061210$; base-2 order-4 and base-8 order-2 nonnormality of $E_+(8)$ and $L_\pm(8)$; $L_+(8)$ as new; and the Selberg–Delange-free route for $L_-(8)$ with $0.162063$, $0.130322$, $0.140457$.
- Thm 2.6 and the §2.6 text give the order-3 limitation.

*Priority claims removed.* A grep for `NEW`, `NEWLY` and `first` shows that every surviving priority claim concerns a contribution Track D does not contain. I searched `notes/phase24/` and `notes/phase25/` for $L_-(4)$ and found no prior result. The old wording ("first unconditional proof … order-4 … $E_+(8)$", "$L_+(8)$ NEWLY CLASSIFIED", priority on the boost) is gone. Shared results are now worded as "independently recovers", and l. 141–142 and l. 230 credit Track D explicitly.

*Unique contributions stated accurately* (l. 515–520, l. 20–26):
- the elementary $\frac23$ factor (Lemma C.1);
- nonnormality of $L_-(4)$ at $k = 2$ for moduli 7, 9, 13, 19, 37, which needs the $\frac23$ factor; l. 213 states correctly that Track D's route gives $\rho = W_\chi/2 > \frac13$;
- base-4 order-2 nonnormality of $E_+(8)$;
- base-4 and base-8 simple nonnormality of $E_+(2^k)$ for $k \ge 4$;
- the DP-free majorants below $\frac{93}{100}$;
- the families of Theorem C.3;
- the sharpened $L_-(8)$ bounds of about 0.33.

*Theorem B.3 recast.* It is now an independent NAF-language re-derivation for $L \le 4$ that complements Track D Thm 1.7.

*Open Question 5 restated* as attainment for $L > 10$.

**M2: CLOSED.**

- No `Track A` or `Track E` label remains in the note.
- The two script comments now read "Phase 24 Track E" and "Phase 24 Track A" next to the `GF` identifiers (script l. 489, 570).
- The enclosures are attributed as follows:
  - "independent re-certification of Phase 24 `GF-40` Thm. 3.1(a)" for $[0.907252, 0.912845]$;
  - "Phase 24 `GF-36` Thm. 7.2" for $[0.908174, 0.908184]$ and for $W_+^{\rm maj}$ (Theorem B.2(1) no longer presents it as new);
  - "`GF-36` Prop. 8.1" for $W_\chi$.

  These appear at l. 22–25, 135–137, 151, 208, 388, 399, 513 and 695, all with links to the Phase 24 notes.
- I confirmed the `GF-36` values in `notes/phase24/dense-digit-mass-and-lambert.md`: Thm 7.2 at l. 307–318 (including the 0.04590…0.53443 row cited in Table 8.1) and Prop 8.1 at l. 336.

### V3. Closure of Minor findings

| # | Status | Evidence |
| --- | --- | --- |
| m1 | Closed | "45 primes" at note l. 23, 160, 411, 658 and 694. Script l. 705, 715 and 774, with the new assertion `len(ps_211) == 45` at l. 707. No "44" remains anywhere |
| m2 | Closed | The script comment now says 26 primes (l. 727). `len(ps_109) == 26` is asserted (l. 755) |
| m3 | Closed | Asserted $0.936414 \le W_+^{\rm maj}$ and $W_+^{\rm maj} \le 0.936415$ (l. 588–589), and $W_{13} \le 0.789314$ (l. 1149–1150) |
| m4 | Closed | The note (l. 388–391) documents all three tail constants with proofs, and I re-derived each by hand: $(1-\frac1p)\sum_{e\ge2} e p^{-e} = (2 + \frac1{p-1})p^{-2}$; $S_V < \frac{1201}{720000}$; $\mathbb E[V] \le \frac{720000}{718799} < 1 + \frac2{600}$; $\frac{1201}{718799} + \frac1{1200} < \frac5{1200}$. The script asserts the certified $\sum_{p>600}p^{-2} < \frac1{1200}$ and both derived bounds (l. 526–543). The irrelevant check is gone |
| m5 | Closed | The Table 8.2 base-8 column is computed in the script as $\max(\text{direct}, \text{descent})$ for both $W_\chi$ and $W_{\rm true}$ at moduli 7, 9, 13 (l. 1159–1170, 1183) and at 19, 37 (l. 1230–1233). The note uses this rule uniformly (l. 228, 491, 642–651), and the old mixed-method values are gone |
| m6 | Closed | "computed from the unrounded certified upper endpoint(s) and rounded down" is stated at l. 212, 219, 490, 626 and 642 |
| m7 | Closed | The interpretive clause is deleted (no "consistent with" remains). §8.2 ends with an explicit non-interpretation statement (l. 679) |
| m8 | Closed | `nafDigitAt` is declared with a ℤ index (l. 563–564). `erdosBorweinPlus` is defined explicitly, and `erdosBorweinPlusCoeff` l. 984 and `erdosBorweinPlus_eq_sub` l. 1345 are cited and verified. The visibility note lists all five private helpers with correct line numbers (verified: 478, 1399, 1588, 1602, 1629). `naf_zero_block_tail_lt` uses `((M : ℤ) - j - t)`. `sum_Ioc_mul_zeta_eq_sum` and the line-count estimates are removed. `radixDiscrepancy` is attributed to `BinaryDiscrepancy.lean` l. 11, and `frequency` and `shift` exist in `Basic.lean` with matching signatures |
| m9 | Closed | "the `GF-36` Thm. 7.1 criterion $\rho < \frac14$ would require" (l. 26, 247–249), noting that `GF-36` Thm 6.1 and 6.2 treat only the unsigned series |
| m10 | Closed | "first proof of nonnormality ($D^- > 0$) of $L_-(4)$". Base-4 simple normality of $L_-(4)$ is marked **Open** at l. 12, 25, 229 and 543 and in OQ2 |
| m11 | Closed | "Completely self-contained" is removed. The kernel-verified `signedWeight_add_le` and `signedWeight_sub_le` are labeled a repository Lean input (l. 8, 20, 269, 506, 529, 540). Step 3(3) now contains a complete strong induction for the neighbor inequality, with even and odd cases (l. 270–283). I checked it and it is correct |
| m12 | Closed | The LP relaxation is justified at l. 180 and l. 418: carries lie in $\{-1, 0\}$, flow conservation holds up to $O(1/N)$, a compactness argument gives a limiting flow with uniform $L$-word marginals, and hence $\mathrm{LP}^*_L \le \liminf w_\pm/N$ |
| m13 | Closed | Both estimates are written out (l. 467–487): the uniform-in-$X$ bound $\le 8K_1\sum_{p>y}p^{-2}$, which I checked, with equality $8$ at $p = 2$, and dominated convergence over $y$-smooth $m$ with summable majorant $G_\chi(m)/m$. I also checked $F(mr) = F(m)$ and the summability of $\rho * \mu$ at $\sigma = \frac34$ |
| m14 | Closed | The sample space is named at l. 507: uniform NAF strings give $\frac{\ell}3 + \frac29$, and uniform integers in $[0, 2^\ell)$ give $\frac{\ell}3 + \frac49$. l. 508 adds that the convolution technique is classical |
| m15 | Closed | The ranges are separated: $[-8192, 8192]$ for NAF equivalence, and $[-512, 512]$ plus special values for the 10,656 dyadic cases. Minimality is described as "over all $3^8$ distinct-exponent signed strings on 8 positions" (l. 20, 694; script output l. 2–4) |
| m16 | Closed | `lowest_excluded_order(W_hi / 3, s=2)` is asserted to return order 2 for moduli 19 and 37 (script l. 1236–1238). Moduli 7, 9 and 13 use the same `s=2` check (l. 1175, 1185) |

### V4. New errors introduced by the repair

I found **no new mathematical error** and no new inconsistency between the note and the script. In particular I re-checked:
- the four Track D attributions listed under V2;
- $\rho = W_\chi/3 \in (\frac14, \frac5{16})$ for all five moduli, and $\frac29 W_\chi \in (\frac16, \frac14)$;
- the base-8 rule for $L_-(8)$, $\frac56 - \frac23 W_\chi$;
- the $11477/437500$ descent value.

The following nits are non-blocking.

- **N1.** The heading of Lemma A.1 (l. 94) still says "zero external inputs" without the "(+ repository Lean input)" qualifier used at l. 20 and l. 540. This is consistent with the evidence taxonomy, because a repository lemma is not an External input, but the wording could be made uniform.
- **N2.** l. 171 asserts "$\sigma_1(x;N)$ and $w_\pm(\lfloor 2^N x\rfloor)$ differ by $O(1)$" without proof. The statement is true, but it should cite Track D Lemma 1.1 / Thm 1.2, or give the one-line carry argument.
- **N3.** The truncation step in the proof of B.3(2) (l. 424, "at most $O(1)$ boundary correction") is informal. This wording predates the repair. It is correct: Track D Thm 1.7(4) covers it, and my original stress test found a maximum deviation of $\frac34$.
- **N4.** OQ5 calls the question "Track D's Question 2". Track D's Question 2 actually asks whether *periodic* $L$-normal numbers attain $\bar g_L$ for every $L \ge 4$, and attainment for every $L$ is stated as Open in Track D's comparison paragraph after Thm 1.7. A light rewording would match it exactly.
- **N5 (informational; outside the two audited files).** The worktree contains an untracked [`NormalityChecker/NafGeometricTransfer.lean`](../../../NormalityChecker/NafGeometricTransfer.lean). Its header claims a `Kernel-verified` formalization of Lemma A.1, Theorem A.2(1)–(3), B.1(2) and B.2(1), with declaration names that differ from §7, for example `nafDigit` and `naf_dyadic_count_le`.
  - The note still conservatively calls §7 an "uncompiled blueprint" (l. 10, 549). That is the correct label until the module passes `lake build` and the axiom audit on `hail`.
  - I did not build or verify this file.
  - No evidence label in the note may be upgraded to `Kernel-verified` until that build is recorded. Once it is, §6, §7 and OQ6 should be updated.

### V5. Conclusion

0 Critical and 0 Major findings remain; M1, M2 and m1–m16 are all closed. The certificate reproduces exactly on Windows, with zero floats before §6b. **Verdict: ACCEPT.** N1–N4 are optional polish.

*Cross-model review is not independent human peer review. This verification authorizes no benchmark status change.*
