# Independent Cross-Provider Referee Review: Phase 26 Track F (`F1`–`F4`)

**Reviewed artifacts:**
- [`notes/phase26/classical-constants-and-nonlinear-boundaries.md`](../classical-constants-and-nonlinear-boundaries.md)
- [`scripts/phase26_classical_nonlinear.py`](../../../scripts/phase26_classical_nonlinear.py)

**Cross-checked dependencies:**
- [`notes/phase26/arithmetic-hankel-determinants.md`](../arithmetic-hankel-determinants.md) (Phase 26 Track B)
- [`notes/phase25/classical-constants-frontier.md`](../../phase25/classical-constants-frontier.md) (`GF-47`)
- [`notes/phase25/partitions-and-reciprocals.md`](../../phase25/partitions-and-reciprocals.md) (`GF-45`)
- [`notes/phase25/nonlinear-and-badly-approx.md`](../../phase25/nonlinear-and-badly-approx.md) (`GF-46`)

**Epistemic caveat:** This is an independent cross-model AI referee review. **Cross-model review is not independent human peer review.**

---

## Verdict: **REVISE**

**Executive assessment.** The flagship constructive and Diophantine theorems of Track F are mathematically sound and impressively clean:
- **F1:** Theorems 1.2 (full-denominator reset blocks for every $\rho < 1 + 1/\ln 2$), 1.3 (translate-robust dyadic measure $|2^M \ln 2 - x| \ge 2^{-(5.178813\ldots + o(1))M}$ for $\operatorname{den}(x) \mid L_M$), 1.4, and Corollary 1.5 ($\Theta(\log N)$ uniform reset threshold) all survive line-by-line verification.
- **F2:** Theorems 2.1–2.2 ($\mu(E_b) = \mu(P_b) \le 7/3$), Corollary 2.3 (linear runs $\le \frac{4}{3} N + 4.63\sqrt{N} + O_b(1)$, $\ge (0.818\ldots - o(1))\log_2 N$ transitions, and $1 - D_N(P_b; b) \gg_b (\log N)/N$), and Propositions 2.4–2.6 are mathematically solid (modulo a one-line fix for $n = 1$, general $b$ in Theorem 2.1(4) and a missing $b^N Z \ge 1$ hypothesis in Lemma 2.0(1)). Literature verification confirms that $\mu(E_b) \le 7/3$ is already established in published work (Bundschuh; Matala-aho 2008) and has been tightened to $2 + \frac{1}{3 + 2\sqrt{3}} \approx 2.1547$ for restricted rationals $d^s / N$ by Leinonen–Leinonen–Matala-aho (2016) — which directly matches the run-transfer shape $(b-1)b^N/A$ of Lemma 2.0(1).
- **F3:** Proposition 3.1, Theorem 3.2, Theorem 3.4 ($C_1(3)^3 \ne u/v$ for $1 \le v < 6.636192\ldots \times 10^{24}$ at $M = 3331$, $e_{3331} = 6$, with all 45 integers in $(3331, 3377)$ independently verified not to be sums of three positive cubes), and Theorem 3.5(1),(3) are sound.
- **F4:** Theorem 4.1 and Proposition 4.2 are sound.

However, the audit uncovered **1 Critical**, **2 Major**, and **8 Minor** findings that must be repaired before acceptance:
1. **[Critical]** The necessity statements in the **second half of Theorem 3.3** and **Theorem 3.5(2)** are **false as stated** (with explicit counterexamples on $C_1(3)^3$ itself, and a direct contradiction with Phase 25 `GF-46` Theorem 1.3(1),(3)), because they conflate exact-prefix packets $(R_{M^*}, \tau^*)$ with the denominator-only ($h = 0$) case of `GF-46` Theorem 1.3(1).
2. **[Major]** **Lemma 1.1** states the **false upper bound** $|\operatorname{Excl}_p(W)| \le |B_p(W)| \le (n_{\rm end} - n)/p + 1$ (explicit counterexample: $n = 9, n_{\rm end} = 11, p = 5$ gives $|\operatorname{Excl}_5(W)| = |B_5(W)| = 2 > 1.4$), and also omits the required hypothesis that $p$ is odd (counterexample at $n = 2, n_{\rm end} = 3, M = 2$).
3. **[Major]** **Lemma 2.0(1)** as stated for arbitrary irrational $y > 0$ is **false** when $Z = 1/y < b^{-N-L}$ (explicit counterexample: $b = 2, y = 100\sqrt{2}, N = 1, L = 6$ forces $A = 0$, and no integer $A \ge 1$ satisfies the stated inequality).

All defects admit clean, surgical repairs that preserve every headline result.

---

## 1. Companion Script Audit (`scripts/phase26_classical_nonlinear.py`)

- **Execution:** `python -B scripts/phase26_classical_nonlinear.py` on Windows exited with code `0` in `16.3s`, reporting **88,045 assertions** (`F1: 33,114`, `F2: 4,520`, `F3: 12,196`, `F4: 38,215`), matching §9 verbatim.
- **Zero-float AST audit:** An automated AST scan of `scripts/phase26_classical_nonlinear.py` verified:
  - **Zero** `float` literals anywhere in the file.
  - Only **one** `float()` conversion in the entire script, at line 356 (`float(max_scaled)`), strictly inside the isolated `FINITE` measurement dictionary and never inside any assertion.
  - Every `/` operator in the script (lines 128, 191, 382, 450) divides `Fraction` (or `int` by `Fraction`), yielding exact `Fraction` arithmetic.
  - Every rational enclosure (`E_enclosure`, `ln2_enclosure`, `T_lo`/`T_hi` at lines 326–329, and `T_hi` for $C_1(3)^3$ at line 447) rounds strictly outwards.
- **Verification coverage gaps (Minor — tied to the proof bugs below):**
  - Line 282 silently adds `or p < 3` (hiding the missing "odd prime" hypothesis in Lemma 1.1), and line 295 only checks `len(excl) <= len(bands)` (never checking Lemma 1.1's claimed `(n_end - n)/p + 1` bound).
  - Lines 160–163 only test `det != 0` for $b \in \{2, 3, 5, 10\}$ (matching the prose gap at $n = 1$ for general $b \ge 2$ in Theorem 2.1(4)).
  - Lines 460–465 only verify the algebraic identity $T_{M'} = B^{M'-M} T_M - \sum_{i=M+1}^{M'} c_i B^{M'-i}$, not the erroneous equivalence to Theorem 3.2 claimed in Theorem 3.3.

---

## 2. Detailed Findings by Severity

### Critical Findings

#### [C1] False necessity claims in Theorem 3.3 (second half) and Theorem 3.5(2) (lines 312–314, 333)
- **What IS true (and should be kept):** The first statement of Theorem 3.3 — that for $c_m \ge 0$,
  $$\bigcap_{M \in S} \bigl(R_M B^{-M},\ (R_M + \tau_M) B^{-M}\bigr] = \bigl(R_{M^*} B^{-M^*},\ (R_{M^*} + \tau^*) B^{-M^*}\bigr],$$
  so the joint information $\{(R_M, \tau_M)\}_{M \in S}$ excludes $X \in v^{-1}\mathbb{Z}$ if and only if the single packet $(R_{M^*}, \tau^*)$ does — is **completely true**.
- **What IS false:**
  1. Theorem 3.3 proceeds to claim (lines 312–314): *"and the best possible multi-packet certificate is the exact test of Theorem 3.2 at $M^*$. In particular, no combination of adjacent packets (determinants, joint numerators, collective cancellation) can exclude a denominator unless one single shift satisfies $T_{M^*} < 1/\operatorname{lcm}(\operatorname{den}(B^{M^*}u/v), p^{e_{M^*}})$."* Its proof cites `GF-46` Theorem 1.3(1).
  2. Theorem 3.5(2) then builds directly on this (line 333): *"By Theorem 3.3, a proof from prefixes and tail bounds that $C_s(3)^3 \notin v^{-1}\mathbb{Z}$ for every $v$ establishes exactly the condition in (1) [$\limsup_M(\gamma_M \log B - \log H_M - e_M \log p) = +\infty$], up to the bounded factor $\operatorname{den}(B^M u/v) \le v$."*
- **Why both claims are false (two independent flaws + explicit counterexamples on $C_1(3)^3$):**
  1. **Exact prefix $R_{M^*}$ (with $\lfloor R_{M^*} \rfloor$ known):** The single interval $(R_{M^*} B^{-M^*}, (R_{M^*} + \tau^*) B^{-M^*}]$ excludes $v^{-1}\mathbb{Z}$ if and only if
     $$v \tau^* B^{-M^*} < 1 - \{v R_{M^*} B^{-M^*}\} \qquad (\text{or } < 1 \text{ if } v R_{M^*} B^{-M^*} \in \mathbb{Z}).$$
     This can hold even when $T_{M^*} \gg 1/\operatorname{lcm}(v', p^{e_{M^*}})$ (where $v' = v/\gcd(v, B^{M^*})$).
     - *Explicit counterexample on the flagship cube $C_1(3)^3$:* At $M^* = 91$, exact computation gives $e_{91} = 3$, $c_{92} = 2$, hence $T_{91} \ge \frac{1}{2}$, whereas for $v = 10$ ($v' = 5$), $1/\operatorname{lcm}(5, 3^3) = \frac{1}{135} \ll \frac{1}{2} \le T_{91}$. Yet $X_{91} = R_{91} 4^{-91} \approx 0.01563$ and $T_{91} 4^{-91} < 4^{-90}$, so the single packet $(R_{91}, \tau_{91})$ easily excludes $C_1(3)^3 \in 10^{-1}\mathbb{Z}$.
     - More generally, for *any* irrational $X = \sum c_m B^{-m}$ (even with $e_M = 0$ and $T_M \asymp 1$), every fixed $v \ge 1$ is excluded by a single exact-prefix packet $(R_M, \tau_M)$ once $M$ is large enough that $\tau_M B^{-M} < \operatorname{dist}(X, v^{-1}\mathbb{Z})$.
  2. **Even with $\lfloor R_{M^*} \rfloor$ discarded and only $\{R_{M^*}\} = A_{M^*}/p^{e_{M^*}}$ known (`GF-46` Theorem 1.3(1) at $h = e_{M^*}$):** `GF-46` Theorem 1.3(1) does **not** give $\tau^* < 1/\operatorname{lcm}(v', p^{e_{M^*}})$ at $h = e_{M^*}$; it gives $\tau^* < r_{\min}(v', A_{M^*}, e_{M^*})/(v' p^{e_{M^*}})$, where $r_{\min} \in \{1, \dots, p^{e_{M^*}}\}$ is the unique residue $\equiv -v' A_{M^*} \pmod{p^{e_{M^*}}}$. Only at **$h = 0$** (denominator-only data, discarding *all* information about both $\lfloor R_{M^*} \rfloor$ and $A_{M^*}$) does `GF-46` Theorem 1.3(1) reduce to $\tau^* < 1/\operatorname{lcm}(v', p^{e_{M^*}})$.
     - *Explicit counterexample on $C_1(3)^3$ even under `GF-46` ($h = e_{M^*}$, unknown $\lfloor R_{M^*} \rfloor$):* At $M^* = 126$, $e_{126} = 3$, $\{R_{126}\} = \frac{1}{27}$, and $T_{126} \in [0.7500, 0.7970]$. For $v = 4$ ($v' = 1$), Theorem 3.2's threshold is $1/\operatorname{lcm}(1, 27) = \frac{1}{27} \approx 0.0370 \ll T_{126}$, whereas `GF-46` Theorem 1.3(1) at $h = 3$ gives $r_{\min} = 26$, threshold $\frac{26}{27} \approx 0.9630 > 0.7970 \ge T_{126}$, genuinely excluding $C_1(3)^3 \in 4^{-1}\mathbb{Z}$.
  3. **Direct contradiction with `GF-46` Theorem 1.3(3):** Phase 25 `GF-46` Theorem 1.3(3) (third bullet, line 148 of `nonlinear-and-badly-approx.md`) explicitly proves that knowing $\{R_{M_k}\}$ and tail bounds $T_{M_k} \le 60(\log T_k)^C B^{-K_k}$ on Ghidelli's sublogarithmic gaps ($K_k \gg \sqrt{\log M_k}/(\log\log M_k)^2$, where $K_k \log B - e_{M_k} \log p \to -\infty$ generically!) *suffices* for irrationality if $\limsup_k \{-v R_{M_k}\} B^{K_k} / (\log T_k)^C = \infty$ for every $v \ge 1$. This directly refutes Theorem 3.5(2) as stated.
- **Required repair:**
  1. In **Theorem 3.3**, separate the two levels cleanly:
     - *(Exact prefixes)* Multi-packet collapse $\bigcap_{M \in S} J_M = (R_{M^*} B^{-M^*}, (R_{M^*} + \tau^*) B^{-M^*}]$ is exact; it excludes $v^{-1}\mathbb{Z}$ iff $v \tau^* B^{-M^*} < 1 - \{v R_{M^*} B^{-M^*}\}$ (or $< 1$ if $v R_{M^*} B^{-M^*} \in \mathbb{Z}$).
     - *(Denominator-only / $h = 0$ certificates, i.e., ignoring $\lfloor R_{M^*} \rfloor$ and $A_{M^*}$)* If one knows only the innovations $c_i$ ($i \in (\min S, M^*]$), the denominators $p^{e_M}$, and the tail bounds $\tau_M$ (equivalently, `GF-46` Theorem 1.3(1) at $h = 0$), then the multi-packet data reduce to $(p^{e_{M^*}}, \tau^*)$ and exclude $v^{-1}\mathbb{Z}$ if and only if $\tau^* < 1/\operatorname{lcm}(v', p^{e_{M^*}})$ where $v' = v/\gcd(v, B^{M^*})$ (and also remove the unbound variable $u$ from $\operatorname{den}(B^{M^*} u/v)$).
  2. In **Theorem 3.5(2)**, restrict the necessity claim explicitly to **denominator-only ($h = 0$) truncation certificates** (or **low-residue $h \le (1-\varepsilon)e_M$ gap-envelope certificates** via `GF-46` Theorem 1.3(2)), and note explicitly that residue-boosted proofs using exact fractional parts $\{R_M\}$ (as in `GF-46` Theorem 1.3(3)) are *not* ruled out by the gap–mass–depth deficit. Update Summary row F3.2, §5 Limitation Ledger, and Theorem 3.2's trailing comment (line 302: *"at full residue precision $h = e$"* should be *"at zero residue precision $h = 0$"*!) accordingly.

---

### Major Findings

#### [M1] Lemma 1.1: false bound $|B_p(W)| \le (n_{\rm end} - n)/p + 1$ and missing "odd prime" hypothesis (lines 54–64)
1. **False band-count / exclusion-count bound (line 61):** Lemma 1.1 states
   $$|\operatorname{Excl}_p(W)| \le |B_p(W)| \le \frac{n_{\rm end} - n}{p} + 1.$$
   This is **false**. Writing $n = q p + r$ ($0 \le r \le p - 1$) and $L = n_{\rm end} - n \ge 1$, the maximum of $|B_p(W)| = \lfloor (n_{\rm end} - 1)/p \rfloor - \lfloor n/p \rfloor + 1 = \lfloor (r + L - 1)/p \rfloor + 1$ occurs at $r = p - 1$ and equals
   $$\left\lfloor \frac{L - 2}{p} \right\rfloor + 2 = \left\lceil \frac{L - 1}{p} \right\rceil + 1 < \frac{n_{\rm end} - n}{p} + 2.$$
   - *Explicit counterexample:* $n = 9$, $n_{\rm end} = 11$, $p = 5$ satisfies $p \le n$ and $p^2 = 25 > 10 = n_{\rm end} - 1$. Here $W = \{9, 10\}$, $B_5(W) = \{1, 2\}$, $5 \nmid A_1 A_2$, and $\operatorname{Excl}_5(W) = \{3, 4\}$, so $|\operatorname{Excl}_5(W)| = |B_5(W)| = 2 > \frac{11 - 9}{5} + 1 = 1.4$.
   - *Downstream impact:* **None** on Theorem 1.2, because the proof of Theorem 1.2 (line 78) already uses the valid bound $|B_p(W)| \le \rho n / p + 2$.
2. **Missing "odd" hypothesis on $p$ (line 54):** The statement allows any prime $p \le n$ with $p^2 > n_{\rm end} - 1$, permitting $p = 2$ when $n \in \{2, 3\}$ and $n_{\rm end} \in \{3, 4\}$, whereas `GF-47` Lemma 3.3 applies only to **odd** primes (and `scripts/phase26_classical_nonlinear.py` line 282 silently skips `p < 3`).
   - *Explicit counterexample:* $n = 2, n_{\rm end} = 3, M = 2$ ($p = 2 \le 2$, $2^2 = 4 > 2 = n_{\rm end} - 1$). Here $s_1 = 1$, $s_2 = 5/2$, $B_2(W) = \{1\}$, $A_1 = 1$ (odd), and $-2^{2-1} s_1 = -2 \equiv 0 \pmod 2$. Lemma 1.1 predicts $\bar a_2 = 1$ preserves the reduced denominator $Q_2 = 2$, yet $x_2 + \frac{1}{2} = \frac{5}{2} + \frac{1}{2} = 3 \equiv 0 \pmod 1$ has denominator $1 \ne 2$.
- **Required repair:** Restrict $M$ to a squarefree product of **odd** primes $p \le n$ with $p^2 > n_{\rm end} - 1$, and replace $(n_{\rm end} - n)/p + 1$ with $\lceil (n_{\rm end} - n - 1)/p \rceil + 1$ (or $(n_{\rm end} - n)/p + 2$). Also add the check `len(bands) <= (n_end - n) / p + 2` in `scripts/phase26_classical_nonlinear.py`.

#### [M2] Lemma 2.0(1): missing hypothesis $b^N Z \ge 1$ (or $Z \ge 1$) to guarantee $A \ge 1$ (lines 148–153)
- **Defect:** Lemma 2.0(1) states that for *any* irrational $y > 0$ and $Z = 1/y$, a constant run of length $L$ after position $N$ yields an integer $A$ with **$1 \le A \le (b-1)b^N Z + (b-1)$** and $|Ay - (b-1)b^N| \le (b-1) y b^{-L}$.
- **Explicit counterexample:** Take $b = 2$, $y = 100\sqrt{2}$, $Z = 1/(100\sqrt{2}) \approx 0.007071 < 2^{-7}$, $N = 1$, $L = 6$. Then $d_2(Z) = \dots = d_7(Z) = 0$. In the proof, $I = \lfloor 2 Z \rfloor = 0$ and $d = 0$, giving $A = (2-1)\cdot 0 + 0 = 0 < 1$. Moreover, **no** integer $A \ge 1$ satisfies $|A \cdot 100\sqrt{2} - 2| \le 100\sqrt{2} \cdot 2^{-6} \approx 2.21$ (the LHS is $\ge 100\sqrt{2} - 2 \approx 139.42$).
- **Downstream impact:** **None** on Corollary 2.3, because $Z = P_b = \prod_{j\ge 1}(1 - b^{-j})^{-1} > 1$, which ensures $I = \lfloor b^N P_b \rfloor \ge b^N \ge 1$ and $A \ge b - 1 \ge 1$ for every $N \ge 0$ (and similarly in Lemma 2.0(2), $(b-1)b^N P_b > b - 1 \ge 1$, so the nearest integer satisfies $A \ge 1$).
- **Required repair:** Add the hypothesis $b^N Z \ge 1$ (or $Z \ge 1$) to Lemma 2.0(1)–(2) (or state $0 \le A \le (b-1)b^N Z + (b-1)$ and note $A \ge 1$ whenever $b^N Z \ge 1$).

---

### Minor Findings

#### [m1] Proof gap in Theorem 2.1(4) at $n = 1$ for general $b \ge 2$ — trivial one-line fix (lines 173, 205–207)
- **Issue:** Theorem 2.1(4) states $Q_n P_{n+1} - P_n Q_{n+1} \ne 0$ for *every* $b \ge 2$ and *every* $n \ge 1$. However, the proof (line 207) only proves $n \ge 2$ analytically (since it cites Theorem 2.1(3)'s lower bound $|Q_{n+1}| \ge \frac{1}{2} b^{f(n+1)}$, which was only stated for $n + 1 \ge 3$), and asserts *"The case $n = 1$ and all $n \le 9$ for $b \in \{2, 3, 5, 10\}$ are certified exactly"*, leaving $n = 1$ for all $b \notin \{2, 3, 5, 10\}$ unproved. (Theorem 2.2 starts at $n_A \ge 2$ and is unaffected.)
- **One-line fix:** In the proof of Theorem 2.1(3) (line 205), for $0 \le r \le n - 1$ we actually have $3n + 1 - r \ge 2n + 2$ (not merely $2n + 1$), so $f(n) - f(r) = \frac{(n-r)(3n+1-r)}{2} \ge (n-r)(n+1)$ and the error ratio is at most $P_b/(b^{n+1} - 1)$. Already at **$n = 2$** and $b \ge 2$, $P_b/(b^3 - 1) \le P_2/7 < 3.463/7 = 0.4947 < \frac{1}{2}$! Thus $|Q_n| \ge \frac{1}{2} b^{2n^2+n}$ holds for **all $n \ge 2$ and all $b \ge 2$**, and the ratio bound of (4) immediately gives $|Q_2 \lambda_1| / |Q_1 \lambda_2| \ge \frac{13 E_2}{180} 2^{14} > 341 > 1$ for **all $b \ge 2$**, closing $n = 1$ completely analytically without any finite case check.

#### [m2] Prior art for $\mu(E_b) \le 7/3$ and connection to restricted $d^s/N$ bounds (lines 223, 418)
The note is commendably candid in §2.2 and §7 (*"We have not checked whether the bound $7/3$ for $\alpha = -q$ appears there... We make no claim that $\mu(E_b) \le 7/3$ is new to the literature"*). Literature verification now pins down the exact published status, which should be cited accurately in §2.2 and §7:
- **Unrestricted $\mu(E_b) \le 7/3$ is published prior art:**
  - **P. Bundschuh** established the classic irrationality exponent $7/3$ for values of the $q$-exponential function $E_q(z) = \prod_{k \ge 0} (1 + z q^k)$ (building on Bundschuh, *Invent. Math.* **9** (1970), 175–184; *Portugal. Math.* **33** (1974), 1–17; and **P. Bundschuh & K. Väänänen**, *"Arithmetical investigations of a certain infinite product"*, *Compositio Math.* **91**(2) (1994), 175–199, which also obtains $\mu(L_q(-1)) < 2.509$ for the logarithmic derivative $L_q$).
  - **T. Matala-aho**, *"On irrationality measures of $\sum_{l=0}^\infty d^l / \prod_{j=1}^l (1 + d^j r + d^{2j} s)$"*, *J. Number Theory* **128**(1) (2008), 1–16, explicitly obtains the effective irrationality measure **$7/3$** (and $7/2$) for this family of $q$-series; note that $(d, r, s) = (1/b, -1, 0)$ is literally Euler's partition identity $\sum_{l=0}^\infty b^{-l}/(b^{-1}; b^{-1})_l = P_b = 1/E_b$.
- **Sharper published bound for the exact restricted shape needed by Lemma 2.0(1):**
  - **L. Leinonen, M. Leinonen, and T. Matala-aho**, *"On approximation measures of $q$-exponential function"*, *Int. J. Number Theory* **12**(1) (2016), 287–303, explicitly quote **"Bundschuh's irrationality exponent $7/3$"** for $E_{1/d}(t)$ and improve it to
    $$2 + \frac{1}{3 + 2\sqrt{3}} = 1 + \frac{2}{\sqrt{3}} \approx 2.1547005\ldots$$
    when rational approximations are **restricted to the shape $d^s / N$**.
  - Remarkably, Track F's Lemma 2.0(1) / Proposition 2.6 reduces constant runs of $P_b = 1/E_b$ precisely to approximations of $E_b$ of the shape $\frac{(b-1)b^N}{A}$ (numerator a fixed constant times $b^N$, denominator $A$). Thus §2.2/§7 should cite Bundschuh, Bundschuh–Väänänen (1994), Matala-aho (2008), and Leinonen–Leinonen–Matala-aho (2016), clearly stating that Theorem 2.1–2.2 is a self-contained, certified reproof of the $7/3$ bound, while the explicit digit-run, transition, and finite-$N$ discrepancy transfer for $P_b$ (Corollary 2.3) is the repository's new application (and noting in §10 Open Question 3 that Leinonen–Leinonen–Matala-aho's restricted-shape method is a direct route to lower $4/3$ toward $\approx 1.1547$).

#### [m3] Track B §7 evidence-label consistency in §4.3 ledger (lines 375–376)
- In §4.3, the `*B* §7 Hankel status` column lists `"denominator balance fails"` for $\pi$ and `"positivity and balance fail"` for $\zeta(3)$ without qualification.
- However, Track B Theorems 7.1(3) and 7.3(3b) (`notes/phase26/arithmetic-hankel-determinants.md` lines 627–629, 672) explicitly classify the denominator-balance failure for both $\pi$ and $\zeta(3)$ as **`Heuristic / M = 0 benchmark comparison`** (not a paper proof of failure for prime-centered $M > 0$ windows; only the positivity failure for $\zeta(3)$ in Theorem 7.3(3a) is a paper proof).
- **Fix:** Qualify both entries in §4.3 (e.g., `v_p = -r; M = 0 balance benchmark fails (heuristic for M > 0)` and `v_p = -3r; positivity fails (proved), M = 0 balance fails (heuristic for M > 0)`).

#### [m4] Outward-rounding slips (lines 41, 136, 375, 452)
1. $1 + 1/\ln 2 = 2.4426950409\ldots < 2.4427$, so the interval $[2.4427, 6.1789]$ (lines 41, 136, 452) rounds the *lower* endpoint slightly *up* (inward). Use $[2.4426, 6.1789]$ or $[2.442695, 6.178814]$.
2. Zeilberger–Zudilin (2020) proved $\mu(\pi) \le 7.103205334137\ldots > 7.1032$, so line 375's `$\mu \le 7.1032$`, `$(6.1032 + o(1))N$`, and `$\ln 7.1032$` round the *upper* bound slightly *down* (inward). Use `7.1033` / `6.1033` (consistent with how Marcovecchio's `3.5745539` and Rhin–Viola's `5.513891` were outward-rounded to `3.5746` and `5.5139` on lines 376–377).

#### [m5] Notation and qualifier polish in F2 (lines 34, 231, 250, 270, 274)
1. **Summary row F2.2 (line 34):** Omits the qualifier "$n_A \ge 3$" for the second explicit lower bound $\frac{1}{6}(4A)^{-4/3} b^{-17n_A/3 - 3}$ (at $n_A = 2$, e.g. $b = 2, A = 1$, that formula is $16\times$ stricter than $\frac{1}{6} b^{-21}$ and is not proved by Theorem 2.2's chain).
2. **Corollary 2.3(1) (line 231):** Writes `= \frac{4}{3} N + 4.63\sqrt{N} + O_b(1)` with `=` instead of `\le` (the exact $\sqrt{N}$ coefficient is $\frac{17\sqrt{6}}{9} = 4.62681395\ldots < 4.63$).
3. **Proposition 2.4 proof (line 250):** When $b = 2$ and $g_{k+1} - g = 1$ with $\theta > 0$ (which happens whenever $g_{k+1} = i(3i-1)/2$ and $g_{k+2} = i(3i+1)/2$, as they share the same sign), $b^{-(g_{k+1}-g)}(1+\theta) = \frac{1}{2}(1+\theta) \in (\frac{1}{2}, \frac{3}{4}]$ wraps past $\frac{1}{2}$; adding one phrase noting $1 - \frac{1}{2}(1+\theta) = \frac{1}{2}(1-\theta) \ge \frac{1}{4} = \frac{1}{2} 2^{-1}$ makes the proof airtight. Note also that $g \ge 1 \implies g_{k+1} \ge 2 \implies g_{k+2} - g_{k+1} \ge 2$ holds for *every* $g \ge 1$, so no "finitely many small cases" exception is needed.
4. **Proposition 2.6 proof (line 270):** Mentions wrap-around at $d = b - 1$ (giving $0$s) but omits the mirror wrap-around at $d = 0, \eta < 0$ (giving $(b-1)$s); in fact all cases yield a run of length $L$, not just $L - 1$.
5. **Mahler remark (line 274):** From $(b-1)b^N X_{b,m} = b^{N+1} X_{b^m, m}$, a run of $X_{b,m}$ after $N$ becomes a run of $0$s or $(b-1)$s of $X_{b^m, m}$ *after* position $N+1$ (starting at digit $N+2$), rather than "at position $N+1$".

#### [m6] Minor completeness remark in Theorem 1.4 (line 130)
- The proof of Theorem 1.4 assumes $n_{i+1} < \infty$ exists for large $n_i$. Add one sentence ruling out finitely many resets ($n_{i+1} = \infty$): if no reset occurs after $n_i$, pick any large $M \ge \max(n_i, K_1, M_0(\eta))$ and apply the same argument on $[M, N)$ with $\delta'_M = 2^{M - n_i}\delta_i$ (whose denominator still divides $L_{n_i} \mid L_M$), yielding $N \le (6.178813 + o(1)) M$ for all $N > M$, contradiction.

#### [m7] Minor typo in Proposition 3.1 (line 288)
- Line 288 writes *"when $x^3 + y^3 + z^3 \le M$"* inside Proposition 3.1, which is stated for general $d$; write $x_1^d + \dots + x_d^d \le M$ (by AM–GM, $x_1 \cdots x_d \le M/d < M$ for every $d \ge 1$).

#### [m8] Minor note on Theorem 1.3 vs. Hankel form wording
- Theorem 1.3's proof (line 116) works directly with the 1-D Jacobi Padé form $\widetilde\Lambda = x P(3) - \sum_{j<r} c_j s_{M+j}$ from Track B Theorem 4.3, which is cleaner and avoids any Hankel determinant bookkeeping: $\operatorname{den}(x) \mid L_M \mid L_p \implies L_p \widetilde\Lambda \in \mathbb{Z}$, and $p > M \implies p \nmid L_M \implies x \in \mathbb{Z}_{(p)} \implies v_p(\widetilde\Lambda) = v_p(\Lambda_{M,r}(0)) = -1$. This is 100% rigorous (and we also checked that in the $r \times r$ Hankel formulation $m_{M+k} = 2^k x$, the row operations $\mathrm{row}_i - 2\,\mathrm{row}_{i-1}$ cancel $x$ identically in all rows $i \ge 1$, leaving $x$ only in row $0$ where $L_p$ already clears $L_M$).

---

## 3. Section-by-Section Independent Verification Log

| Section / Theorem | Status | Key Verification Checks |
| --- | --- | --- |
| **F1 — Lemma 1.1** | **REVISE [M1]** | CRT decoupling & band law algebra verified for odd $p$; counterexamples found for $p = 2$ ($n=2, n_{\rm end}=3$) and for $|B_p(W)| \le (n_{\rm end}-n)/p + 1$ ($n=9, n_{\rm end}=11, p=5$). |
| **F1 — Theorem 1.2** | **VERIFIED** | Size of $M_i$, drop-prime loss $O(\log^3 n)$ bits, sieve count $K(\frac{1}{2}+o(1))$, smallness $\|\tilde x_{n'}\| \to 0$, and $O(1)$ floor error in reset count all verified; ratio-2 block $[1000, 2000)$ certified with outward $T_{1000}$ enclosure. |
| **F1 — Theorem 1.3** | **VERIFIED** | $L_p \widetilde\Lambda \in \mathbb{Z}$, $v_p(\widetilde\Lambda) = -1$ ($p > M \implies x \in \mathbb{Z}_{(p)}$), $\alpha_* = 0.4428471667\ldots$, exponent $5.1788125440\ldots$, Marcovecchio comparison $7.731545\ldots$ all independently verified. |
| **F1 — Theorem 1.4 & Cor. 1.5** | **VERIFIED** (+[m4],[m6]) | $\limsup \|\tilde x_n\| < \frac{1}{4} \implies \|2^{n_i} y_i\| < 2^{-(n_{i+1}-n_i)-1}$ and reset constant $1/\log_2(6.1788125\ldots) = 0.3806146\ldots$ verified. Fix outward rounding of $2.4427 \to 2.4426$ and add 1-line note ruling out finitely many resets. |
| **F2 — Lemma 2.0** | **REVISE [M2]** | (2) verified; (1) fails for $Z < b^{-N-L}$ ($b=2, y=100\sqrt{2}, N=1, L=6$); unaffected on $Z = P_b > 1$. |
| **F2 — Theorem 2.1** | **VERIFIED** (+[m1]) | Independently reconstructed $c_i$, $Q_n, P_n \in \mathbb{Z}$, $\gcd(Q_n, b) = 1$, $T_k$, $|T_{k+1}/T_k| \le 2/15$, $e_n = \frac{(3n+2)(n+1)}{2}$, $|Q_n|$ bounds, and det ratio $\frac{13 E_b}{180} b^{7(n+1)}$; tested $b \in \{2,3,4,5,6,7,10,17\}$. Close $n=1$ general-$b$ gap in (4) via $f(n)-f(r) \ge (n-r)(n+1)$ giving $|Q_2| \ge \frac{1}{2} b^{10}$. |
| **F2 — Theorem 2.2** | **VERIFIED** (+[m2],[m5]) | $f(n+1) = \frac{4}{3} e_{n-1} + \frac{17}{3} n + 3$, quadratic bound on $n_A$, and $\mu(E_b) = \mu(P_b) \le 7/3$ verified. Add exact literature citations (Bundschuh; Bundschuh–Väänänen 1994; Matala-aho 2008; Leinonen–Leinonen–Matala-aho 2016) and "$n_A \ge 3$" in Summary row F2.2. |
| **F2 — Corollary 2.3** | **VERIFIED** (+[m5]) | $\frac{17\sqrt{6}}{9} = 4.626814\ldots < 4.63$, $1/\log_2(7/3) = 0.8180679\ldots$, escape contribution $1/(2b(b-1))$, and `[GF-32, Lemma 5.3]` transfer verified. Change `=` to `\le` before $4.63\sqrt{N}$. |
| **F2 — Propositions 2.4–2.6** | **VERIFIED** (+[m5]) | Pentagonal isolation $\frac{3}{8} N^2$, run-method ceiling $w_\lambda$, and $b$-adic Ridout equivalence verified. Minor clarifications noted in [m5]. |
| **F3 — Prop. 3.1 & Thm 3.2** | **VERIFIED** (+[m7]) | Depth recursion, $e_M \le s \log_p M$ via AM–GM, and rational-tail lower bound verified. |
| **F3 — Thm 3.3 & Thm 3.5(2)** | **REVISE [C1]** | Exact interval collapse to $(R_{M^*}, \tau^*)$ verified; second half of Thm 3.3 and Thm 3.5(2) refuted by explicit counterexamples on $C_1(3)^3$ ($M = 91, v = 10$; and under `GF-46` $h = e_M$, $M = 126, v = 4$) and by `GF-46` Thm 1.3(3). Restrict necessity to $h = 0$ / low-residue certificates. |
| **F3 — Theorem 3.4** | **VERIFIED** | Independently recomputed $S_3^+$ up to $3491$: confirmed $3331 \in S_3^+$, $3377 \in S_3^+$, all $45$ integers $3332\ldots 3376 \notin S_3^+$, $e_{3331} = 6$, $c_m \le m^{2/3} \le m$, tail bound $\sum_{j>J} (M+j)4^{-j} < 2(M+J+2)4^{-J}$, and $\lfloor V^* \rfloor = 6636192071781020039363335$. |
| **F3 — Theorem 3.5(1),(3)** | **VERIFIED** | Sufficient condition, $(3/m')^s \le c_{m'} \le H_M \le O(M)$, and Ghidelli exponent deficit $\frac{1}{2}$ vs $1$ verified. |
| **F4 — Thm 4.1, Prop. 4.2, §4.3** | **VERIFIED** (+[m3],[m4]) | Möbius invariance of $\mu$, bounded-remainder recursion for $\sqrt{D}$ and $\varphi$, and Bugeaud (2011) $\mu(X_{b,2}) = 2$ verified. Align $\pi$/$\zeta(3)$ B7 column with Track B's heuristic-vs-proof labels and outward-round $\pi$'s bound to `7.1033`/`6.1033`. |

---

## Post-Repair Verification

### Verdict: **ACCEPT**

**Epistemic caveat:** This post-repair check is an independent cross-model AI verification pass. **Cross-model review is not independent human peer review.**

### 1. Companion Script Re-Execution & Zero-Float Audit (`scripts/phase26_classical_nonlinear.py`)

- **Execution:** `python -B scripts/phase26_classical_nonlinear.py` on Windows exited with code `0` in `16.8s`, recording **179,335 exact assertions** (`F1: 109,874`, `F2: 8,295`, `F3: 22,951`, `F4: 38,215`), matching §9 of `notes/phase26/classical-constants-and-nonlinear-boundaries.md` verbatim.
- **Zero-float AST audit:**
  - **Zero** `float` literals in the entire script.
  - Only **one** `float()` call, at line 428 (`float(max_scaled)`), strictly inside the isolated `FINITE` measurement dictionary and never inside any assertion.
  - Every `/` operator (lines 128, 169, 170, 233, 454, 526, 559, 578) operates on `Fraction` (returning exact `Fraction`), and every `**` operator uses a non-negative integer exponent.
  - All rational enclosures — including the newly added Theorem 2.1(3)–(4) constant checks (lines 167–172) and Theorem 3.3 counterexample bounds (lines 569–588) — round strictly in the sound outward direction.

### 2. Finding-by-Finding Resolution Matrix

| ID | Original Finding | Repair Verification (`classical-constants-and-nonlinear-boundaries.md` & `phase26_classical_nonlinear.py`) | Status |
| --- | --- | --- | --- |
| **C1** | False necessity claims in Theorem 3.3 (second half) and Theorem 3.5(2); `h = e` typo after Theorem 3.2 | Theorem 3.2 comment (line 324) corrected to $h = 0$ and $v'_M = v/\gcd(v, B^M)$ (removing unbound $u$). Theorem 3.3 (lines 328–353) cleanly separates (1) exact-prefix interval collapse ($v\tau^*B^{-M^*} < 1 - \{vR_{M^*}B^{-M^*}\}$), (2) denominator-only ($h = 0$) necessity $\tau^* < 1/\operatorname{lcm}(v', p^{e_{M^*}})$, and (3) low-residue ($1 \le h \le e_{M^*}$) necessity $\tau^* < p^{h-e_{M^*}}$ (and $< p^{h-e_{M^*}}/v$ for $\gcd(v,pB)=1$), verified against `GF-46` Theorem 1.3(1). Explicitly adds both flagship-cube counterexamples ($M^*=91, v=10$; $M^*=126, v=4$, lines 348–349) and clarifies information-fed classification (line 351). Theorem 3.5(2) (lines 370, 373), Summary F3.1/F3.2/F3.4 (lines 42–45), §5 Ledger (lines 433–434), and §10 Q4 (line 494) restrict necessity to $h = 0$ and low-residue $h_M \le (1-\varepsilon)e_M$ certificates while explicitly preserving residue-boosted routes (`GF-46` Thm 1.3(3)). Script (lines 542–588) certifies the exact-prefix criterion, $h=0$ threshold, low-residue bound, and both counterexamples. | **RESOLVED** |
| **M1** | Lemma 1.1: false bound $\|B_p(W)\| \le (n_{\rm end}-n)/p + 1$ and missing odd-prime hypothesis | Lemma 1.1 (lines 54, 64, 67, 69) and Summary F1.1 (line 38) restrict $M$ to **odd** primes $p \le n$ with $p^2 > n_{\rm end} - 1$ and replace the upper bound with the sharp bound $\lceil (n_{\rm end}-n-1)/p \rceil + 1 < (n_{\rm end}-n)/p + 2$ (equality at $n \equiv -1 \pmod p$). Adds explicit remark (line 71) certifying all three counterexamples ($n=9, n_{\rm end}=11, p=5$ noting band 2 is a drop band; drop-free $n=13, n_{\rm end}=15, p=7$; and $p=2$ at $n=2, n_{\rm end}=3$). Theorem 1.2 (line 86) notes $p$ odd. Script (lines 325, 340–367) certifies the sharp bound, full grid $3 \le n < 80$ including equality cases, and all three counterexamples. | **RESOLVED** |
| **M2** | Lemma 2.0(1): missing $b^N Z \ge 1$ hypothesis for $A \ge 1$ | Lemma 2.0 (lines 160–167) adds $b^N Z \ge 1$ (e.g. $Z \ge 1$), verifies $I \ge 1 \implies A \ge b-1 \ge 1$ in (1) and $(b-1)b^N Z \ge 1 \implies A \ge 1$ in (2), documents the counterexample $b=2, y=100\sqrt{2}, N=1, L=6$ (line 167), and checks $b^N P_b > 1$ in Corollary 2.3 (line 258). Script (lines 184–190) certifies the counterexample and $P_b > 1$ for $b \in \{2,3,5,10\}$. | **RESOLVED** |
| **m1** | Theorem 2.1(4) proof gap at $n = 1$ for general $b \ge 2$ | Theorem 2.1(3) (lines 186, 219) sharpens $3n+1-r \ge 2n+2 \implies f(n)-f(r) \ge (n-r)(n+1)$ to establish $\|Q_n\| \ge \frac{1}{2}b^{2n^2+n}$ for all $n \ge 2$ and all $b \ge 2$ ($P_2/7 < 0.4948 < \frac{1}{2}$). Theorem 2.1(4) (line 221) then closes $n = 1$ analytically for every $b \ge 2$ via ratio $> \frac{13 \cdot 0.2887}{180} 2^{14} > 341 > 1$. Script (lines 156–183) certifies all analytic constants, exponent identities, and $n \in \{1, 2\}$ for $2 \le b \le 17$. | **RESOLVED** |
| **m2** | Prior art attribution for $\mu(E_b) \le 7/3$ and restricted $d^s/N$ bounds | Summary F2.2 (line 34), §2.2 Remark (lines 237–245), §4.3 (line 415), §6 (line 448), §7 (lines 456–457), §10 Q3 (line 493), and References (lines 502–511) accurately cite Bundschuh (1969/70, 1974), Bundschuh–Väänänen (1994), Borwein (1988), Matala-aho (2008), and Leinonen–Leinonen–Matala-aho (2016) (including $1 + 2/\sqrt{3}$ for $d^s/N$, matching $2^N/A$ at $b=2$), candidly stating scope of verification and separating the reproof of $7/3$ from Track F's digit-transfer results. | **RESOLVED** |
| **m3** | Track B §7 evidence-label consistency in §4.3 ledger | §4.3 ledger (lines 412–413, 419) explicitly distinguishes proved $v_p$ and $\zeta(3)$ positivity failure from the $M = 0$ denominator-balance benchmark (`Heuristic for prime-centered M > 0`), matching Track B Theorems 7.1(3) and 7.3(3a)–(3b). | **RESOLVED** |
| **m4** | Outward-rounding slips ($2.4427$, $\pi$'s $7.1032$) | $1 + 1/\ln 2$ lower endpoint rounded outward to `2.4426` in Summary F1.4 (line 41), Corollary 1.5(3) (line 148), and §10 Q1 (line 491); $\mu(\pi)$ upper bound rounded outward to `7.1033` / `6.1033` in §4.3 (line 412). | **RESOLVED** |
| **m5** | Notation and qualifier polish in F2 (5 items) | (1) Summary F2.2 (line 34) adds `when n_A >= 3`. (2) Corollary 2.3(1) (line 253) replaces `=` with `\le` before $4.63\sqrt{N}$. (3) Proposition 2.4 proof (line 272) handles $b=2, g_{k+1}-g=1, \theta>0$ wrap-around ($1-u = \frac{1}{2}(1-\theta) \ge \frac{1}{4}$) and notes $g_{k+2}-g_{k+1} \ge 2$ for all $g \ge 1$ (certified lines 215–217). (4) Proposition 2.6 proof (line 292) cleanly proves exact run length $L$ including both $d=0$ and $d=b-1$ wrap-around cases (certified lines 218–229). (5) Mahler remark (line 296) states `after position N+1, that is, starting at digit N+2`. | **RESOLVED** |
| **m6** | Theorem 1.4 completeness (ruling out finitely many resets) | Line 142 adds a clean, elementary proof ruling out finitely many resets: no reset after $n_i$ forces $\|2^K y_i\| = 2^{-(N-K)}\|2^N y_i\| < 2^{-(N-K)-2}$ for all $N \ge K$, hence $2^K y_i \in \mathbb{Z}$ and $\ln 2 \in \mathbb{Q}$, contradiction. | **RESOLVED** |
| **m7** | Proposition 3.1 general-$d$ typo | Line 310 corrected to $m = x_1^d + \dots + x_d^d \le M$, with AM–GM giving $x_1 \cdots x_d \le M/d \le M$. | **RESOLVED** |
| **m8** | Theorem 1.3 one-dimensional Jacobi–Padé vs. Hankel wording | Line 126 adds `*Remark (one-dimensional form).*` clarifying the direct 1-D proof and its equivalence to the $r \times r$ Hankel formulation via $\mathrm{row}_i - 2\,\mathrm{row}_{i-1}$. | **RESOLVED** |

### 3. Regression & Evidence-Label Audit

- **No new mathematical errors:** Every revised proof step (Lemma 1.1 band-count chain, Theorem 1.4 finitely-many-resets argument, Lemma 2.0 hypothesis check, Theorem 2.1(3)–(4) $n=1$ analytic closure, Proposition 2.4 wrap-around, Proposition 2.6 length-$L$ run proof, Theorem 3.3(1)–(3) and Theorem 3.5(2) separation) was independently re-checked and is sound.
- **No evidence-label regressions:** Scope statements (lines 25, 419), `[finite]` isolation (lines 361, 485), Open status of $C_1(3)^3$ and `BC-01`…`BC-50` benchmarks, heuristic labeling (lines 375, 412–413), and external-input citations (§6) remain strictly compliant with repository standards.
- **Conclusion:** All Critical, Major, and Minor findings are fully resolved. Track F is **ACCEPTED** (subject to the standing caveat that cross-model AI review is not independent human peer review).
