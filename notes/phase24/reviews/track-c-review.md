# Cross-Provider Referee Review — Phase 24 Track C

- **Reviewer:** Claude Opus 5.5 (auditing Gemini 4)
- **Files audited:**
  - `notes/phase24/partitions-and-reciprocal-spectra.md` (434 lines)
  - `scripts/phase24_partitions_reciprocals.py` (1,095 lines)
- **Independent script execution:** `python -B scripts/phase24_partitions_reciprocals.py` exited with code `0`: `30689 substantive exact checks + 136 float measurements = 30825 total (0.53 s)`. A second run produced byte-identical output apart from the timing line. Every highlight printed by the script matches §5 of the note.
- **Reviewer-side auxiliary computations** (scratch code, not committed to the repository):
  1. Lemma C1.2a extended from $k \le 20$ to $k \le 60$.
  2. The Proposition C1.3(3) search re-run with and without the script's divisor-count filter.
  3. A factor-free exact evaluation of $\ln T_k^{(E)}$, cross-validated against brute-force factorization for $k \le 14$ ($|\text{diff}| < 10^{-14}$) and then run to $k = 1200$.
- **Scope notice:** This is an automated cross-model audit. It is **not** independent human peer review.
- **Verdict:** **REVISE**. One Critical finding (Theorem C1.2) needs a withdrawal or downgrade and a re-check. Sub-tracks C2–C4 would be **ACCEPT AFTER REVISION** on their own.

---

## Executive Summary

The track contains a correct and elementary flagship. **Theorem C2.3, the universal doubly-exponential period-growth barrier, survived a line-by-line audit of every prime case.** This covers odd $p$, both $2$-adic regimes $b \equiv 1, 3 \pmod 4$, even $b$, degenerate factors $b^{m_j} - 1 = 1$, and the $p = 2$, $r \ge 3$ case of Lemma C2.2. No hidden divisibility, prime-power or LTE gap remains. The Lyapunov step reduces exactly to $(\theta - \varepsilon)(B_{k-1} - A_{k-1}) \ge 0$.

The following results are also correct as mathematics:

- Lemma C2.1
- Lemma C2.2
- the exact quadratic period asymptotic $\ln T_k^{(E)} = (\frac12 - \frac3{\pi^2})(\ln b)k^2 + O_b(k\ln^2 k)$ (Theorem C4.2). The primes are not double-counted across distinct $d$. Large-$k$ finite measurements drift toward $0.196036$.
- the Cartier automaticity and carry identities (Theorems C3.1–C3.2)
- the carry-valuation barrier (Theorem C3.3)
- the shadowing, pentagonal coupling and Weyl characterization results (Theorems C4.1, C4.3, C4.4)
- Theorem C1.1 (dense dyadic spectrum)
- Lemma C1.2a
- Proposition C1.3(1)–(2)
- Theorem C1.4

Each has only minor gaps.

Sub-track C1 has one serious problem. **Theorem C1.2, the claimed refutation of unreset infinite $P_{k_j}$-products, has an invalid proof.** Its tail estimate carries an unbounded multiplier product against a fixed small quantity. Phase 22 explicitly guarded against this kind of Lipschitz amplification with bounded rounds and $-1$ resets. The conclusion $\lim D_N(1/x; b) = 1$ is not established, and the mechanism suggests it may fail. In addition, **Proposition C1.3(3) is false as stated.** The script's search silently skips $L = 60$, and $L = 60$ contains a counterexample even to the weaker summary claim.

Counts: **1 Critical, 4 Major, 15 Minor.**

---

## 1. Sub-track C1 — Convergent reciprocal spectrum and obstructions

### 1.1 Theorem C1.1 (lines 73–85) — **verified, with minor gaps**

- **Part (1).** Inside the cyclic group $\langle 2 \rangle$ of order $t = \operatorname{ord}_D(2)$, the subgroup $\langle 2^e \rangle$ has index $\gcd(e, t)$. Hence $2 \in \langle 2^e \rangle \iff \gcd(e, t) = 1$. The orbit-permutation argument gives $\mu(r; 2^e) = \mu(r; 2)$. ✔
- **Part (2).** The words $w = 0^z w_{\mathrm{dB},m}$ end in $1$, so $A$ and $D$ are odd and $\gcd(2^e, AD) = 1$. The hypothesis $P \equiv 1 \pmod e$ together with $\operatorname{ord}_D(2) \mid P$ gives $\gcd(e, \operatorname{ord}_D 2) = 1$, so $2 \in \langle 2^e \rangle \pmod D$. That is exactly the hypothesis of Phase 23 Theorem 1 (`convergent-reciprocals-and-schedules.md`, line 18, which requires $\gcd(b, AD) = 1$ and $2 \in \langle b \rangle \pmod D$). The adjustment $z_0 \mapsto z$ costs at most $(e-1)/2^m$. ✔
- **Part (3).** Concatenating words that start with $0^{M-1}$ and end in $1$ preserves exact cyclic $M$-word counts. Base-$2^e$ $L$-cylinders coincide with base-$2$ $M$-cylinders. The even-$e$ obstruction is correct: $\gcd(e, t) = 1$ with $e$ even forces $t$ odd, while exact $L$-normality forces $2^{eL} \mid t$. ✔ One gap remains; see Minor m1.
- The script certifies the $b = 4, 8, 16$ spectra ($D \in [0.1189, 0.8401]$) and the base-$8$ $1$-normal reciprocals ($R \in \{1,2,4,5,7,8\}$). It does so exactly, including the step-$3$ permutation argument behind base-$8$ digit counts. ✔

### 1.2 Lemma C1.2a (lines 93–107) — **verified**

- **Multiplicity law.** $N_k(v)$ holds exactly for every $k \le 60$ in the reviewer's independent recomputation (script: $k \le 20$).
- **Mod-$p$ bound.** The arithmetic $2M(4k+4-pM-p) \ge 2(k/p)(k+4)$ uses $pM \le 2k$ and $p \le k$. The final inequality $8k^2 + 32k > 8k^2 + 12k + 4$ is correct. ✔ For $k \le 60$ the quantity $4p \cdot \mathbb P(p \mid S \mid S \ne 0)$ never drops below $2.08$, so the bound $1/(4p)$ holds with room to spare.
- **Conditional independence.** Conditioning on the product event $E_2^{(j)}$ leaves the band coordinates independent, each uniform on the nonzero bands. The binomial tail bound for $\mathbb P(p^{e_p} \nmid S^{(j)}_{\mathrm{tot}} \mid E_2^{(j)})$ is correct. ✔

### 1.3 Theorem C1.2 (lines 109–122) — **CRITICAL: proof invalid; conclusion not established** (finding **C-1**)

See §6, finding C-1.

### 1.4 Proposition C1.3 (lines 128–140)

- **Part (1).** $g(0^+) = \gamma + (1-\gamma)/p$ and $\inf g = g(0) = g(1^-) = 0$, so $D(\nu_\gamma) = \frac1p + \gamma(1 - \frac1p)$ for every integer $p \ge 2$. ✔ The invariance statement is about the *idealized* band recursion only; see Minor m4.
- **Part (2).** Any divisor $Q$ is $\pm$ a product of the factors $\Phi_{p^s}$, so its leading coefficient is a unit. Then $Q \equiv c(1-q)^{d} \pmod p$, and Lucas's theorem forces $p \mid \binom{N}{i}$ on the $p^{r-1}$ indices with $i_s = p-1$. These include the trailing zero bands $i > N$. ✔
- **Part (3)** is **false**; see Major M-1.

### 1.5 Theorem C1.4 (lines 142–150) — **verified**

- **Part (1)** is immediate. ✔
- **Part (2).** The external input is quoted correctly: Bugeaud–Corvaja–Zannier, *Math. Z.* 243 (2003), Thm. 1, $\gcd(a^n - 1, b^n - 1) < e^{\varepsilon n}$ for multiplicatively independent $a, b$. For $b$ not a power of $2$, the integers $b$ and $2$ are multiplicatively independent. The zero-run bound $b^z < D$ and the constant-digit variant with $|\{b^{n_0} r\} - d/(b-1)| \ge 1/((b-1)D)$ are correct. ✔ The scope claim ("blocks the $0^z w_{\mathrm{dB},m}$ route") is appropriately narrow.

---

## 2. Sub-track C2 — Universal doubly-exponential barrier (flagship)

### 2.1 Lemma C2.1 (lines 160–172) — **verified in every prime case**

- **Odd $p$.** Every factor $b^{m_j} - 1$ divisible by $p$ has $v_p \ge a_p$, so $e_p, f_p \ge a_p$. Also $\operatorname{ord}_{p^E}(b) = s_p\, p^{E - a_p}$ with $p \nmid s_p$. Hence $v_p(T_{k+1}) \ge e_p + f_p - a_p \ge f_p \ge \min(e_p, f_p)$. ✔
- **$p = 2$, $b \equiv 1 \pmod 4$.** Here $\operatorname{ord}_{2^E}(b) = 2^{\max(0, E - a_2)}$, and the same inequality follows. ✔
- **$p = 2$, $b \equiv 3 \pmod 4$.** I checked $v_2(b^n - 1) \in \{1,\ a_2 + v_2(n) - 1\}$. I also checked $\operatorname{ord}_{2^E}(b) = 1$ ($E = 1$), $= 2$ ($2 \le E \le a_2$) and $= 2^{1 + E - a_2}$ ($E \ge a_2$). The sub-case $v_2(G) = 1$ uses $4 \mid D_{k+1}$. The sub-case $v_2(G) \ge 2$ forces $m_{k+1}$ even, hence $f_2 \ge a_2$, hence $v_2(T_{k+1}) \ge e_2 + 1 > \min(e_2, f_2)$. ✔
- **$b$ even** gives $2 \nmid D_k$. Primes $p \mid b$ never divide $D_k$. Factors with $b^{m_j} - 1 = 1$ (that is, $b = 2$, $m_j = 1$) are harmless. ✔

### 2.2 Lemma C2.2 (lines 174–187) — **verified**

- **$L_k \mid T_k$.** For $b^{m} - 1 \ge 2$, $\operatorname{ord}_{b^m - 1}(b) = m$ because $0 < b^i - 1 < b^m - 1$ for $0 < i < m$. The degenerate modulus $1$ has order $1 = m$. ✔
- **Locating $p^r$.** $p^r \parallel g_k$ implies $p^r \mid m_j$ for some $j < k$, so $(b^{p^r} - 1) \mid G_k \mid T_k$ by Lemma C2.1. ✔ Lemma C2.1 is genuinely needed here: $q \mid D_k$ alone would not give $q \mid T_k$.
- **Size of $\Phi_{p^r}(b)$.** $\Phi_{p^r}(b) > b^{p^r - p^{r-1}} \ge b^{p^r/2}$. ✔
- **Primitive part.** Non-primitive prime divisors of $\Phi_{p^r}(b)$ equal $p$, with $v_p \le 1$. For $p = 2$ this needs $r \ge 3$, which follows from $2^r \ge 7$. Then $b^{2^{r-1}} \equiv 1 \pmod 8$ for odd $b$, and $\Phi_{2^r}(b)$ is odd for even $b$. ✔
- **Lower bound.** $f(x) = (\frac{\ln 2}{2} - \frac1{15})x - \ln x$ has $f(7) = 0.0135 > 0$ and $f' \ge 0.137$. ✔
- **Coprimality.** Distinct $p^r$ give disjoint prime supports, since the order $\operatorname{ord}_q(b) = p^r$ is determined by $q$. So the primitive parts are pairwise coprime. ✔
- **Counting.** $t(t+1)/2 \le S$, AM–GM, and the bound $t\ln(S/t) \le \sqrt{2S}\ln(S+2)$ (since $S \ge 7$ when $t \ge 1$) are correct. ✔
- **Small prime powers.** The prime powers $\le 6$ ($2, 3, 4, 5$) divide $60$. ✔

### 2.3 Theorem C2.3 (lines 193–211) — **verified, with one false corollary**

- **$T_k \to \infty$.** The dichotomy (one prime recurring, or infinitely many primes) is correct, and $T_k$ is monotone. ✔
- **Recursion.** $A_k = A_{k-1} + \ln m_k - \ln g_k$ and $A_k \le B_k$. ✔ Choosing $k_1$ so that the $g_k$ error is $\le \varepsilon B_k$ is legitimate, because $B_k \to \infty$ monotonically. ✔
- **Lyapunov step.** $(1+\varepsilon)(A + \theta B) - (1+\theta)(A + \varepsilon B) = (\theta - \varepsilon)(B - A) \ge 0$. ✔ Equality at $A = B$ shows the factor $(1+\theta)/(1+\varepsilon)$ is the best this functional gives.
- **Iteration and limit** $\varepsilon \downarrow 0$. ✔ The $m_k$ version follows from $\ln m_k \ge \theta B_{k-1}$. ✔
- **Example.** $m = (2, 4, 15)$ gives $T = (2, 12, 60)$ (reproduced). ✔
- **Part (2)'s "ultra-short-orbit regime" claim does not follow and is false in general.** See Major M-2.
- The "sharp" label is justified only at $\theta = 1$; see Minor m6.

---

## 3. Sub-track C3 — Mahler partition constants

### 3.1 Theorem C3.1 (lines 221–237) — **verified**

- **Cartier identity.** $(1-z)F(z) = F(z^m)$ and $(1-z)^{-1} = Q_m(z)/(1-z^m)$ give $\Phi_r F_k = U_{k+1,r} F_{k+1}$. The degree bound is $\deg U_{k+1,r} \le k$. Orthogonality of roots of unity gives $U_{s,r}(1) = m^{s-1}$. ✔
- **Automaticity.** The $\mathbb Z/m^L$-span of $F_0, \dots, F_L$ is closed under all $\Phi_r$. The modulus $p^e$ uses $k_0 = \lceil e/v \rceil$. The kernel sizes and the external input (Allouche–Shallit Thm. 6.6.2) are labelled correctly. ✔
- **$k = 1$ identity.** $U_{2,r}(y) = m - (m-1-r)(1-y)$ and $[z^n]F_1 = b_m(mn + r)$ give the stated identity. ✔ The attribution is off; see Minor m8.

### 3.2 Theorem C3.2 (lines 243–260) — **verified**

- **Part (1).** The floor formula follows from integrality of $\delta_n$ and $\{b^{n-1}X\} \in [0,1)$. The strict lower bound uses monotonicity of $b_m$. The upper asymptotic uses $b_m(r+m) - b_m(r) = b_m(\lfloor r/m \rfloor + 1)$ and $b_m(r+m) \le 2b_m(r)$. The tail is $O(n^{-\log_b(b^m/2)})$ relative to $b_m(n)$. ✔
- **Part (2).** The telescoping is correct. ✔
- **Part (3).** Since $\beta(k)$ is even for $k \ge 2$, $d_k = \delta_{k+1} \bmod 2$. ✔
- **Part (4)** follows from $b_m(k) - b_m(k-1) = [m \mid k]\, b_m(k/m)$. ✔ The script certifies $\delta_1, \dots, \delta_{11} = [1, 2, 3, 4, 5, 7, 8, 11, 13, 16, 18]$ and the parity law for $k \le 180$.

### 3.3 Theorem C3.3 (lines 268–284) — **verified**

The user asked for a careful check of $a(k) \ge b_m(k)$ and $F_m(a) \equiv z$.

- The digits $c_n$ of $\Delta' = \{z - \{X_{m,m}\}\} \in [0,1)$ are **nonnegative**. Hence $h(k) \ge 0$ and $a(k) \ge b_m(k) \ge 1$ for all $k$. ✔
- Because $L(n)$ is nondecreasing, $k(n) = n + L(n)$ is strictly increasing. So $h$ is well defined, and $\sum_k h(k) m^{-k} = \sum_n c_n m^{-n} = \Delta'$ exactly. Therefore $F_m(a) = X_{m,m} + \Delta' \equiv z \pmod 1$. ✔
- The valuation bound $v_m(h(k(n))) = L(n)$ (when $c_n \ne 0$; $c_n < m$) is correct. The conversion $L(n) = (\frac12 - \varepsilon)(\log_m k)^2 - O_\varepsilon(\log k)$ holds via $n = k - O((\log k)^2)$. ✔
- $L(n) \ge 1$ gives $m \mid h(k)$, which preserves parity when $m = 2$. Finitely many changes preserve automaticity. ✔
- The growth bound $h/b_m = O_\varepsilon(m^{-\frac{\varepsilon}{2}(\log_m k)^2})$ holds via GF-32 Cor. 2.2. ✔
- **Sharpness** holds relative to the growth normalization $|a - b_m| < b_m$. Under that normalization, valuations above $\log_m(2b_m(k))$ force $h(k) = 0$ eventually, so $F_m(a) \in X_{m,m} + \mathbb Q$. ✔ See Minor m12 for wording.

---

## 4. Sub-track C4 — Short-orbit bridge for $P_b = 1/E_b$

### 4.1 Theorem C4.1 (lines 294–304) — **verified, with minor wording issues**

- **Partition identity.** Two parts $\ge k+1$ would exceed $k + 1 + m$ when $m \le k$. ✔
- **Two-sided bounds.** These use $\prod(1 - x_j)^{-1} - 1 > \sum x_j$ and $1 - \prod(1 - x_j) < \sum x_j$. ✔ The strictness of the second inequality after $M \to \infty$ needs one line; see m9.
- **Shadowing.** The choice $k_b(N, \Delta)$ gives $b^n(P_b - R_k) < \frac{1}{2b}\, b^{-\Delta}$. ✔
- **Breakdown claim.** At $n_1$, $b^{n_1}(P_b - R_k) > 1$ via $R_k/P_b > 1 - S_k \ge 1/b$. ✔ But see m9: this breaks real-line shadowing, not necessarily mod-1 shadowing.

### 4.2 Theorem C4.2 (lines 310–334) — **verified, including the double-counting concern**

- **Part (1).** The formulas for $v_p(D_k^{(E)})$ in all three regimes and the threshold $\lfloor k/s_p \rfloor \ge \lfloor \log_p k \rfloor + 2$ are correct (every $q \ne p$ contributes $v_p(s_q) \le \log_p k$). ✔ The script certifies these for $b \in \{2,3,5,7\}$, $k \le 16$.
- **Part (2), Ramanujan bound.** $\ln \Phi_d(b) = \varphi(d)\ln b - \sum_r c_d(r)/(r b^r)$. Von Sterneck's formula gives $|c_d(r)| = \varphi(d)/\varphi(d/g) \le g = \gcd(d, r) \le r$. Hence the bound $1/(b-1)$, also valid for $d = 1$. ✔
- **Part (2), primitive factorization.** Möbius inversion of LTE gives $v_p(\Phi_d(b)) = [d/s_p = p^r]$. Every non-primitive prime is the largest prime factor of $d$, to the first power. The only exception is $d = 2$, $b \equiv 3 \pmod 4$, which is excluded correctly; the even-$d$ $2$-adic computation is also right. So $\Phi_d(b)/R(d) \mid d$. ✔ The script certifies this for $b \in \{2,3,5\}$, $d \le 24$.
- **Part (3), no double counting.** Each prime $p \mid D_k^{(E)}$ has a **unique** order $s_p = d \le k$, so grouping by $d$ partitions the primes. For $s_p = d$, the $p$-adic valuations satisfy $v_p(b^d - 1) = v_p(\Phi_d(b))$, because $p \mid \Phi_e(b)$ with $e < d$ would force $s_p \mid e$. Hence $\prod_{s_p = d} p^{e_0(p)} = R(d)$ *exactly*, and $\sum_p e_0(p)(\lfloor k/s_p \rfloor - 1)\ln p = \sum_{d \le k} (\lfloor k/d \rfloor - 1)\ln R(d)$, with no prime counted twice. ✔
- **Part (3), error terms.** $E_k \mid T_k \mid E_k \operatorname{lcm}(1, \dots, k)$. ✔ Factorial terms are $O(k\ln k)$ and vanish for $p > k$. ✔ $\ln R(d) = \varphi(d)\ln b + O(\ln d + 1)$, contributing $O(k\ln^2 k)$. ✔
- **Part (3), main term.** $\sum_d \lfloor k/d \rfloor \varphi(d) = k(k+1)/2$ and $\sum_{d \le k} \varphi(d) = \frac{3}{\pi^2}k^2 + O(k\ln k)$. ✔ The constant $\frac12 - \frac3{\pi^2}$ is right.
- **Independent finite measurement (not asymptotic evidence).** The reviewer's factor-free exact evaluation of $\ln T_k^{(E)}$ agrees with brute force to $10^{-14}$ for $k \le 14$. It gives these values of $\ln T_k^{(E)}/(k^2\ln b)$:

  | $b$ | $k = 100$ | $k = 200$ | $k = 400$ | $k = 600$ | $k = 1200$ |
  |---|---|---|---|---|---|
  | 2 | 0.20512 | 0.19908 | 0.19781 | 0.19728 | 0.19667 |
  | 3 | 0.20341 | 0.19808 | 0.19763 | 0.19702 | — |
  | 10 | 0.20196 | 0.19739 | 0.19731 | 0.19687 | — |

  The values decrease toward $0.196036$. The note's small-$k$ values ($0.2232$ at $k = 26$) are consistent with the $O(\ln^2 k/k)$ error term.

### 4.3 Theorem C4.3 (lines 340–349) — **verified**

- **Part (1).** $b^n E_b^{(K)} \in \mathbb Z$ for $n \ge \omega_K^+$. The tail satisfies $|E_b - E_b^{(K)}| < 2b^{-\omega_{K+1}^-}$, and the gap length is $2K+1$. ✔ The script's interval check is conservative: it uses $P_{\mathrm{lo}}$ on the right-hand side and adds the bracket radius on the left. ✔
- **Parts (2)–(3).** The proofs transfer from C3.2–C3.3. Hardy–Ramanujan gives $h/p = O_\varepsilon(b^{-\frac\varepsilon2\sqrt k})$ and $L(n) \ge (\frac{\pi\sqrt{2/3}}{\ln b} - \varepsilon)\sqrt k - O(1)$, using $\sqrt n = \sqrt k - O(1)$. ✔ The external input is labelled correctly.

### 4.4 Theorem C4.4 (lines 355–388) — **verified**

- **Part (1).** $|e(hu) - e(hv)| \le 2\pi h|u - v|$. ✔
- **Part (2).** $\|(b-1)y\| = (b-1)\operatorname{dist}(y, F_b)$, and $\operatorname{dist}(b^n x, F_b) \le \|b^n(x - c)\|$ because $b^n c \equiv c$ for $c \in F_b$. Together with $\operatorname{dist}^2 \le \frac12\operatorname{dist}$ this gives $\mu_N \ge (1 - \operatorname{Re} W_{b-1})/(\pi^2(b-1)^2)$. GF-32 Lemma 5.3 ($\frac25\mu_N - \frac1N \le 1 - D_N \le 2\sqrt{2\mu_N}$, confirmed at `binary-partition-and-carry-complexity.md` line 407) then gives part (2). ✔
- **Part (3).** $\sin(\pi u) \ge 2u$ and Cauchy–Schwarz give the constant $2^{3/4}$. ✔
- **Part (4).** The reverse bound $1 - |W_1| \le |e(c) - W_1| \le 2\pi\mu_N$ holds. For the forward bound I checked:
  - the exact identity $1 - |Z|^2 = \sum_{j<\ell} p_j p_\ell |e(\cdot) - e(\cdot)|^2$
  - the chord bound $4\sin^2(\pi/(b-1))$
  - $2\sum_{j<\ell} p_j p_\ell \ge 1 - \max p_j$
  - $1 - |Z|^2 \le 2(1 - |Z|)$
  - $\mu_N \le \delta_1 + \frac12(1 - p_*)$ ✔

  The equivalence $D^+ = 1 \iff \limsup \min(|W_1|, \operatorname{Re} W_{b-1}) = 1$ follows, and it reduces to (3) at $b = 2$. ✔
- **Base-3 counterexamples.** $x = 1/4$ has orbit $\{1/4, 3/4\}$, $W_2 \equiv -1$ and $D = 1/2$. The measure $\sigma = \frac12\delta_0 + \frac12\delta_{1/2}$ has $\operatorname{Re}\hat\sigma(2) = 1$, $\hat\sigma(1) = 0$ and $D = 1/2$. ✔ Both are counterexamples to the "$\Rightarrow$" direction only, which is the intended reading. See m11 for realizing $\sigma$ by an actual $x$.
- **Part (5).** Weyl's criterion plus part (1). ✔

---

## 5. Script audit (`scripts/phase24_partitions_reciprocals.py`)

- **Exact/float separation:** Clean. Part I uses only `int` and `Fraction`. Floats appear only in display conversions (`shadow_table`, printed discrepancies). Part II floats are labelled "NOT asymptotic evidence". The float counts reconcile: $116$ Ramanujan-bound checks $+ 10$ period ratios $+ 10$ Weyl checks $= 136$. ✔
- **Determinism and reproducibility:** Two runs were identical apart from the timing line. Runtime is $0.53$ s. ✔
- **Correct implementations:** I verified each of the following:
  - `exact_orbit_disc` uses the standard formula $\max((i+1)/n - x_i) - \min(i/n - x_i)$.
  - `certified_digits_from_series` uses rigorous intervals, with a tail majorant justified by $b_m(r + m) \le 2b_m(r)$.
  - `ord_mod` and the 2-adic order branches in F2 are correct.
  - The interval radius in the pentagonal check is handled correctly.
- **Defects:**
  - Lines 487–488 and 501–503 (see Major M-1).
  - Lines 854–857, lines 776–779 and lines 608–618 (see Minor m13–m15).
  - The comment at line 901 says $K = 1..9$, but the loop at line 918 is $K = 1..8$. The note correctly says $K \le 8$; only the comment is wrong.

---

## 6. Findings

### Critical

**C-1. Theorem C1.2's tail estimate is false; the "refutation" of unreset infinite $P_{k_j}$-products is not established.**
*Where:* the claim is stated at line 17 and in the evidence table at line 51, introduced at line 91, proved at lines 109–122 (specifically lines 115, 120 and 122), and relied on at Open Problem #1, line 419.

- **The failing bound (line 120).** On $E_2^{(j)}$ the proof bounds the tail of the telescoped identity (line 117) by $\sum_{v=1}^j O(M_j b^{-\widetilde T_{v-1}})$ and asserts that this tends to $0$. The symbol $M_j$ is never defined. To dominate the multipliers it must satisfy $M_j \ge \prod_{w \le j}(2k_w + 2)$, and this product tends to $\infty$ because $k_w \to \infty$.
- **Why it fails.** For $v = 1$, the factor $b^{-\widetilde T_0} = b^{-\operatorname{ord}_{D_0}(b)}$ is a fixed constant; for $D_0 = 3$, $b = 2$ it equals $1/4$. So the $v = 1$ term alone is $\asymp M_j b^{-\widetilde T_0}$, which tends to $\infty$.
  - More precisely, the level-$v$ tail has size $\asymp b^{-(m_v - r_v)}$ with $r_v$ uniform on $[0, m_v)$.
  - On $E_2^{(j)}$, which keeps mass $\to 1 - \alpha > 0$, this tail is multiplied by $\prod_{w = v+1}^j S_{i_w}^{(k_w)}$. The log-size of that product grows like $\sum_{w = v+1}^j \log k_w$, which tends to $\infty$.
  - So for every fixed $v$, the fraction of $E_2^{(j)}$ on which the amplified level-$v$ term exceeds any fixed $\delta$ tends to $1$.
  - Making the $m_v$ larger cannot help, because each $m_v$ is finite while the amplification is unbounded.
- **The same flaw on $E_1^{(j)}$ (line 115).** Phase 22 controlled $\Lambda_{u,d}$ with the edge width $L_s^* = \lceil \log_b(16M_s) \rceil + s + 2$, where $M_s$ is the **bounded** multiplier product of one finite round. It imposed $b^{m_{n_s}} - 1 \ge 2^s M_s^2$ and $-1$ resets precisely to cap this amplification (`normal-reciprocals-and-signs.md` §5.4, Step 1 and Step 2). The unreset product has no cap: $M_{u,j} \to \infty$ for every fixed $u$.
- **The forbidden Lipschitz step (line 122).** The inequality $W_1((S_i)_*\mu(R_{j-1}), \delta_0) \le |S_i|\, W_1(\mu(R_{j-1}), \delta_0) \to 0$ would need $W_1(\mu(R_{j-1}), \delta_0) = o(1/k_j)$, which is never shown. Phase 22 explicitly forbade this step: "Multiplying an established bound $W_1 \le 2^{-s}$ by an integer $S$ as large as $M_s$ would only give $M_s 2^{-s}$, so we argue directly." The parenthetical fallback on line 122 assumes the tail bound that fails above, so it is circular.
- **Why the $p$-adic collapse does not rescue it.** Grouping the first two terms gives $b^t R_j \equiv (\prod_{w \ge 2} S_{i_w})\, X_1 + (\text{levels} \ge 2)$, where $X_1 = \{b^{t_1}R_1\}$ has denominator $\operatorname{den}(R_1) = D_0 P_{k_1}(b^{m_1})$ (Phase 22 Lemma 5.2(1)).
  - The level-1 term vanishes mod $1$ only after the multipliers absorb every prime factor of $P_{k_1}(b^{m_1})$. By Bang–Zsigmondy, this includes primitive primes $q \equiv 1 \pmod{2(2k_1+1)m_1}$.
  - Since $|S| \le 2k_w + 2$, absorption needs $k_w \gtrsim q/2$.
  - Before that happens, the level-1 term is a nonzero point of $\frac{1}{\operatorname{den}'}\mathbb Z/\mathbb Z$. The next multiplier re-randomizes it; it is not near $0$.
  - Heuristically, a positive fraction of the mass re-spreads on long windows. So the asserted $\lim D_N(1/x; b) = 1$ is not merely unproven but doubtful for slowly growing $k_j$. This includes the "natural candidate" with $\sum 1/k_j < \infty$.
- **Repair.**
  1. Withdraw Theorem C1.2 as a theorem.
  2. Keep only the correct exact statement: by Lemma C1.2a and conditional independence, $D_0 \mid S_{\mathrm{tot}}^{(j)}$, so the *leading grid term* is an integer, on a $(1 - o(1))$-fraction of $E_2^{(j)}$. Say explicitly that this does not determine the orbit measure.
  3. Relabel the full refutation as `Open` (heuristic).
  4. Remove "refutation" and "provably fails" from lines 17, 51, 91 and 419.
  5. Restate Open Problem #1 as unresolved for unreset products.
  6. Do not register C1.2 in `docs/registry/GF.toml`.

  Lemma C1.2a is unaffected and may keep `Paper proof` + `Finite certificate`.

### Major

**M-1. Proposition C1.3(3) is false, and the weaker summary version fails at the $L = 60$ case the script skips.**
*Where:* the note at lines 18, 52, 133, 140 and 400; the script at lines 487–488 and 501–503.

- **The stated claim is false almost everywhere.** Line 133 says no divisor with $\deg Q < L/3$ has all $S_i \in \{0\} \cup \{\pm 2^a : a \ge 0\}$. In fact **487 of the 514** checked divisors have this property. For example, $Q = \Phi_2$ with $L = 4$ gives $S = (1, 0, 1, 0)$.
- **What the script tests is weaker.** It only asserts the implication "all $S_i \in \{0, \pm 2^a\}$ $\Rightarrow$ zero-density $\ge 1/3$". That is the summary's version (line 18).
- **Even the summary version is false at $L = 60$.** The filter `if len(divs) > 10: continue` silently drops $L = 60$, so the search covers $L \le 59$, not $L \le 60$. Re-running $L = 60$ gives the witness $Q = \Phi_3\Phi_4\Phi_{10}$: degree $8 < 20$, all $S_i \in \{-2, -1, 0, 1, 2\}$, and zero-density $18/60 = 3/10 < 1/3$.
- **Repair.**
  1. Restate (3) as a zero-density statement.
  2. Restrict it to $L \le 59$ and report the $L = 60$ counterexample, or drop the claim.
  3. Remove the divisor-count filter, or report its exclusions.
  4. Make the script assert exactly the stated claim.

  The certificate is motivational only; no theorem depends on it.

**M-2. The corollary in Theorem C2.3(2) (lines 26, 197, 211) overreaches: "every sub-doubly-exponential product is forced into $\lim \ln m_k/\ln T_{k-1} = 0$".**

- **What the theorem actually gives.** It only shows that $m_k \ge T_{k-1}^\theta$ fails infinitely often for each $\theta > 0$. That means $\liminf \ln m_k/\ln T_{k-1} = 0$, not $\lim = 0$.
- **Counterexample.** Take Phase 23's anchored schedule $(m'_i)$ in base $2$, with $\ln T'_i \sim c_* 2^i$ and $m'_i \ge T'_{i-1}$. Set $m_{i^2} := m'_i$ and $m_k := 1$ otherwise; in base $2$ each extra factor is $2^1 - 1 = 1$.
  - Then $T_k = T'_{\lfloor \sqrt k \rfloor}$, so $\ln m_k \le e^{O(\sqrt k)} = e^{o(k)}$.
  - But $\ln m_{i^2}/\ln T_{i^2 - 1} \ge 1$ for every $i$, so the limit is not $0$.
  - The three named examples ($X_{b,m}$, $\prod_p(1 - 2^{-p})^{-1}$, $P_b$) do satisfy $\lim = 0$, but by direct estimates, not by the theorem.
- **Repair.** Replace $\lim$ by $\liminf$ in the corollary. Verify the named examples separately (for instance, $\ln T_k^{(E)} \asymp k^2$ from C4.2).

**M-3. Theorem C1.2's hypotheses are inconsistent and its membership claim is unsupported (lines 17, 91, 109, 111).**

- The theorem assumes $\gcd(b, A_0 D_0) = 1$. But its advertised example $R_0 = \prod_{r=1}^2 (1 - b^{-n_r})^{-1}$ has numerator $b^{n_1 + n_2}$. The summary (line 17) states $\gcd(b, D_0) = 1$ instead.
- The parenthetical claim "$x \in M_b \subset K_b$" (line 111) is asserted without proof. Its growth hypothesis, $m_j/(L m_{j-1}) \ge b^{j^3}(2k_j + 3)^j$, is far weaker than Phase 22's $m_n \ge b^{n^3}\widetilde T_{n-1} C_n^n (d_n + 1)$, which is what Phase 22's proof that the product lies in $K_b$ uses.
- **Repair.** These points matter only if a corrected C1.2 is retained. In that case, drop $\gcd(b, A_0) = 1$ (it is never used), and either adopt Phase 22's growth condition or prove $x \in M_b$.

**M-4. The summary and evidence table present Theorem C1.2 as an established result with label `Paper proof` (lines 17, 51, 91, 419).**

This propagates C-1 into the evidence layer, in breach of the evidence-label discipline in `AGENTS.md`.

- **Repair.** Relabel the row as `Open` (heuristic) and keep Lemma C1.2a's row separate. Update Open Problem #1, which currently says "Theorem C1.2 rules out unreset infinite $P_{k_j}$-products".

### Minor

- **m1 (line 85).** In C1.1(3), adjusting $c_{\mathrm{ext}}$ alone cannot force $\gcd(e, P) = 1$ when $\gcd(e, R) > 1$. The bound on the change of mixture ratio, $O(e/(c_{\mathrm{ext}} + c_{\mathrm{dB}}))$, ignores the unequal segment lengths $R 2^M$ and $2^m$. *Fix:* choose $R \equiv 1 \pmod e$, and bound the change by $(e-1)R 2^M/P$.
- **m2 (line 50).** C1.1(3) also depends on Phase 23 Theorems 2 and 3(a). Cite them in the evidence row.
- **m3 (lines 18, 131–133).** The symbol $\rho$ is used in two senses: $\rho^{(p)} = \#\{p \mid S_i\}/L$, and zero-band density. For $\Phi_6$, the zero-density is $1/3$ but $\rho^{(2)} = 2/3$. Use distinct symbols.
- **m4 (lines 18, 131).** "Strictly invariant under every cyclotomic factor $Q(b^{-m})^{-1}$" is a statement about the idealized recursion $\mu \mapsto \frac1L\sum_i (S_i)_*\mu$. Transferring it to actual orbits is subject to the amplification problem in C-1. Say so.
- **m5 (notation).** Several symbols are overloaded or undefined:
  - $M_j$ is undefined (line 120).
  - $L_k$ means both $2(2k+1)(2k+3)$ (C1.2) and $\operatorname{lcm}(m_1, \dots, m_k)$ (C2).
  - $\Phi$ denotes Cartier operators, cyclotomic polynomials and the Lyapunov functional.
  - $P_b(p^r)$ (line 182) clashes with $P_b = 1/E_b$.
  - The example $R_0 = (1 - b^{-m_0})^{-1}(1 - b^{-m_1})^{-1}$ at line 91 reuses $m_1$.
- **m6 (lines 24, 26, 156, 193).** Three overstatements in C2:
  - "Sharp" is justified only at $\theta = 1$, via Phase 23. No construction attains $(1+\theta)$ for $\theta \ne 1$.
  - Line 156's "$\ln T_k \ge c\,(1+\theta)^k$" overstates the proof, which gives $\ln T_k \ge c_\varepsilon\, ((1+\theta)/(1+\varepsilon))^k$ for each $\varepsilon$.
  - "$\ln T_k \sim c_* 2^k$ is universally asymptotically optimal" should say the doubly-exponential *base* $2$ is optimal, not the constant $c_*$.
- **m7 (line 26).** "LTE-order recycling" is a nonstandard name for the example. There $G_3 = 1$, and the saving comes from $3 \mid \gcd(T_2, m_3)$, with the $3$ having entered $T_2$ via LTE at step 2. Explain the term in one sentence.
- **m8 (lines 29, 225–226).** The identity $b_m(m^2 n + m^2 - m) = m\sum_{j \le n} b_m(mj)$ is elementary. It is not the Churchhouse–Rødseth–Andrews congruence, which concerns $b_m(m^{r+1}n) - b_m(m^r n)$ modulo growing powers of $m$. Relabel it "CRA-type identity" or similar.
- **m9 (lines 36, 299, 304).** Two issues in C4.1:
  - At $n_1$ the proof shows $|b^{n_1}(P_b - R_k)| > 1$. That breaks real-line shadowing and digit certification, but not necessarily mod-1 proximity. Reword "fails" and "breaks down".
  - The strict inequality $1 - \prod_{j > k}(1 - b^{-j}) < S_k$ is not automatic in the limit $M \to \infty$. Add the one-line bound $\sum_{j \le M} x_j - A_M \ge x_1 x_2$.
- **m10 (line 317).** The shadowed period fraction $\exp(-(\frac12 - \frac3{\pi^2} + o(1))(\ln b)N^2)$ needs $\Delta = o(N)$. State this.
- **m11 (line 368).** $\sigma$ is a measure. For a statement about sequences, add one sentence exhibiting an $x$ that realizes it, for example a base-3 expansion alternating blocks of $0$s and $1$s whose lengths tend to infinity.
- **m12 (lines 31, 276, 344).** "Sharp" for C3.3 and C4.3 should say "sharp under the normalization $|a(k) - b_m(k)| < b_m(k)$". Line 275's "certified carry window $L_\tau(N) \sim \frac12(\log_m N)^2$" is neither defined nor proved here; cite GF-32 or delete it.
- **m13 (script lines 854–857).** The upper shadowing bound is certified as $P_{\mathrm{hi}} - R_k < P_{\mathrm{hi}} S_k$. That does not certify $P_b - R_k < P_b S_k$. Use $P_{\mathrm{lo}} S_k$ on the right-hand side; the margin is ample.
- **m14 (script lines 776–779; note line 58).** The 120-bit difference $(t - x) \bmod 2^{120}$ ignores the borrow from lower-order bits of $z - \{X_2\}$. It certifies a finite identity for truncated targets, not "three target realizations verified exactly". Reword the evidence row.
- **m15 (script lines 608–618 and 1017; note line 413).** Three reporting issues:
  - The 81 "algebraic Lyapunov" checks are tautologies that inflate the C2 count of 3,939. Report them separately or drop them.
  - At note line 413, $D_{120}$ is computed on the $P_b$ orbit, while $|W_1|$ and $\operatorname{Re} W_{b-1}$ are computed on the $R_k$ orbit. Label which is which.
  - The script uses $k = N + \Delta + 4$ rather than $k_b(N, \Delta)$. This is conservative, but state it.

---

## 7. Repair checklist (in priority order)

1. **(C-1, M-3, M-4)** Withdraw or downgrade Theorem C1.2 to `Open` (heuristic). Keep Lemma C1.2a and the leading-grid-term integrality statement. Purge the "refutation" language at lines 17, 51, 91 and 419. Do not register it.
2. **(M-1)** Restate Proposition C1.3(3) as a zero-density statement for $L \le 59$. Report the $L = 60$ witness $\Phi_3\Phi_4\Phi_{10}$ (zero-density $3/10$). Fix the script filter at lines 487–488 and the assertion at lines 501–503.
3. **(M-2)** In C2.3(2), replace $\lim$ by $\liminf$. Verify the three named examples directly.
4. Apply Minor fixes m1–m15. The most substantive are m1 (the $\gcd(e, R)$ gap), m6 (the scope of "sharp") and m13 (the certificate direction).
5. Re-run `python -B scripts/phase24_partitions_reciprocals.py`. Update the counts in lines 55, 65, 396 and 400–405.

---

## 8. Verdict

**REVISE.**

- **Sub-track C1:** REVISE. Theorem C1.2 must be withdrawn or downgraded, and Proposition C1.3(3) corrected.
- **Sub-track C2:** ACCEPT AFTER REVISION. The core barrier is correct and fully elementary. Fix the corollary in M-2 and the scope of "sharp".
- **Sub-track C3:** ACCEPT AFTER REVISION. The changes are minor wording and attribution fixes.
- **Sub-track C4:** ACCEPT AFTER REVISION. The changes are minor wording fixes and the certificate direction in m13. Theorem C4.2's asymptotic and the base-3 counterexamples are correct.

After C-1 and M-1 to M-4 are repaired, a focused re-check of the revised §1.2–§1.3, the summary, the evidence table and Open Problem #1 should suffice for ACCEPT AFTER REVISION overall.

**Cross-model review is not independent human peer review.** This audit was performed by one AI model (Claude Opus 5.5) on work drafted by another (Gemini 4). Its findings, including the independent computations listed above, are finite checks and reasoning by a model. They do not replace verification by human referees or by the Lean kernel.

---

## Post-Repair Verification

- **Reviewer:** Claude Opus 5.5 (focused re-check after repair)
- **Files re-audited:** `notes/phase24/partitions-and-reciprocal-spectra.md` (435 lines) and `scripts/phase24_partitions_reciprocals.py` (1,130 lines)
- **Script re-run:** `python -B scripts/phase24_partitions_reciprocals.py` exited with code `0`: `30586 substantive exact checks + 136 float measurements = 30722 total (0.90 s)`. Section counts are C1 `2,736`, C2 `3,831`, C3 `22,812`, C4 `1,207` and Part II `136` float. They match the note's §5 table and line 66.
- **Reviewer-side auxiliary check** (scratch code, not committed): an independent SymPy division of $(1 - q^{60})/(1 - q)$ by $\Phi_3\Phi_4\Phi_{10}$. It gives degree $8$, band values $\{-2, -1, 0, 1, 2\}$ and $18$ zero bands out of $60$, which confirms the $L = 60$ witness.

### Critical and Major findings

| Finding | Status | Evidence in the revised files |
|---|---|---|
| **C-1** (invalid refutation, $D_N \to 1$) | **Closed** | Theorem C1.2 is withdrawn. §1.2 now contains only Lemma C1.2a and the new **Proposition C1.2b**, which says that $\mathbb P(D_0 \mid S_{\mathrm{tot}}^{(j)} \mid E_2^{(j)}) \to 1$, so the *leading* grid term is an integer on a $(1 - o(1))$-fraction of $E_2^{(j)}$. The proof uses only Lemma C1.2a, conditional independence and the binomial tail; I re-checked it and it is correct. The Remark (line 120) states explicitly that this does **not** determine $\mu_N^{\mathrm{emp}}(1/x; b)$ or prove $D_N \to 1$. It names the unbounded tail amplification $\prod_{w > v} S_{i_w}^{(k_w)}$ and the unabsorbed primitive primes of $\operatorname{den}(R_1)$. The words "refutation" and "provably fails" no longer appear anywhere in the note. No C1.2 entry appears in `docs/registry/` or `docs/benchmarks/`. |
| **M-1** (C1.3(3) false; $L = 60$ silently skipped) | **Closed** | The `len(divs) > 10` filter is gone: the loop now runs over `range(2, 61)` with no exclusions (script lines 501–538). The script asserts the exact counts `514` ($L \le 59$, of which `487` lie in $\{0, \pm 2^a\}$) and `423` ($L = 60$, of which `297` lie in $\{0, \pm 2^a\}$), `937` in total. It also asserts that the $L = 60$ witness list equals exactly `[([3, 4, 10], 8, 18, [-2, -1, 0, 1, 2])]`. Note lines 18 and 131–133 restate (3) as a zero-band-density claim for $L \le 59$ and report the unique witness $\Phi_3\Phi_4\Phi_{10}$ with $\rho_0 = 3/10 < 1/3$. The false "no divisor has all $S_i \in \{0, \pm 2^a\}$" wording is removed. The added remark $\rho^{(p)} = \rho_0$ for odd $p$ is correct, since $|S_i| \le 2$. Open Problem #1 cites the witness. |
| **M-2** ($\lim$ vs. $\liminf$ in C2.3(2)) | **Closed** | Lines 26 and 197 now state $\liminf_{k\to\infty} \ln m_k / \ln T_{k-1} = 0$, and the proof (line 211) derives exactly that. The full limit is claimed only for the three named examples, each verified directly. For $P_b$, $\ln T_{k-1}^{(E)} \asymp_b k^2$ by C4.2. For $X_{b,m}$, $(b^{m^{k-2}} - 1) \mid G_{k-1} \mid T_{k-1}$ by Lemma C2.1. For $\prod_p (1 - 2^{-p})^{-1}$, $\ln T_{k-1} \ge \ln((k-1)!)$ via $L_{k-1} \mid T_{k-1}$, together with $p_k \le 2^k$. All three are correct. |
| **M-3** (inconsistent hypotheses; unproven $x \in M_b$) | **Closed** | Proposition C1.2b assumes only $\gcd(b, D_0) = 1$; the unused $\gcd(b, A_0) = 1$ is dropped. The example $R_0 = (1 - b^{-n_1})^{-1}(1 - b^{-n_2})^{-1}$ is consistent with this. The weak growth hypothesis and the claim "$x \in M_b \subset K_b$" are removed. The Remark says only that membership would require Phase 22's stronger growth condition. |
| **M-4** (C1.2 labelled `Paper proof`) | **Closed** | The evidence table now separates Lemma C1.2a with Proposition C1.2b (`Paper proof` + `Finite certificate`) from a new row "asymptotic orbit measure and discrepancy of unreset infinite $P_{k_j}$-products", labelled `Open` (line 52). The summary (lines 17 and 20) and Open Problem #1 (line 420) now say "unresolved (`Open`)". |

### Minor findings

| Finding | Status | Evidence |
|---|---|---|
| m1 | Closed | C1.1(3) now chooses $R \equiv 1 \pmod e$, so $\gcd(e, R 2^M) = 1$ for odd $e$, and bounds the mixture change by $(e - 1) R 2^M / P$ (line 86). |
| m2 | Closed | The evidence row (line 50) cites Phase 23 Thms 1, 2 and 3(a). |
| m3 | Closed | Two distinct symbols are used: $\rho^{(p)}(Q)$ and $\rho_0(Q)$. The $\Phi_6$ example gives $\rho_0 = 1/3$ and $\rho^{(2)} = 2/3$, and the script also asserts both values. |
| m4 | Closed | "*idealized* band-multiplier recursion", together with an explicit caveat about transfer to actual orbits (lines 18 and 129). |
| m5 | Closed | $M_j$ is removed. $\ell_k$ replaces the C1 use of $L_k$. Cartier operators are now $\mathcal C_r$ and the Lyapunov functional is now $\Psi_k$. $\Pi_b(p^r)$ replaces $P_b(p^r)$. The $R_0$ example uses $n_1, n_2$. |
| m6 | Closed | The theorem is called "sharp at $\theta = 1$" throughout. Line 156 states that sharpness for $\theta \ne 1$ is not established and gives the $c_\varepsilon((1+\theta)/(1+\varepsilon))^k$ form. The claim is now that the doubly-exponential **base** $2$ is optimal, not the constant $c_*$. |
| m7 | Closed | LTE-order recycling is defined in one sentence (lines 26 and 196). |
| m8 | Closed | The result is now called an "elementary CRA-type divisibility identity", explicitly distinguished from the Churchhouse–Rødseth–Andrews congruences (line 225). |
| m9 | Closed | The wording now says "real-line shadowing and digit certification break down … though mod-1 proximity could still recur". The strict upper bound is proved via $\sum_{j \le M} x_j - A_M \ge x_1 x_2$, which gives $\le S_k - b^{-(2k+3)}$ (line 304). |
| m10 | Closed | The hypothesis $\Delta = \Delta_N = o(N)$ is stated at lines 39, 317 and 423. |
| m11 | Closed | An explicit base-3 block number $x = 0.0^1 1^1 0^2 1^2 \dots_3$ realizes $\sigma$ (line 368). |
| m12 | Closed | "Sharp under $|a(k) - b_m(k)| < b_m(k)$" (respectively $|a(k) - p(k)| < p(k)$) appears at lines 31, 266, 268, 276 and 344. The undefined "$L_\tau(N)$ carry window" is deleted. |
| m13 | Closed | The script now sets `ub = P_lo / ((b - 1) * b**k)` and checks `P_hi - R_k < ub` (lines 880–883). This certifies $P_b - R_k < P_b S_k$ correctly. |
| m14 | Closed | The note (lines 59 and 402) and the script comment (lines 779–782) now describe the certificate as an exact finite-prefix identity for $120$-bit truncated differences that ignores lower-order borrow. |
| m15 | Closed | The 81 standalone tautological Lyapunov checks are removed. The C2 count falls from `3,939` to `3,831`. Line 414 labels $D_{120}(P_b)$ separately from $W$ on $R_{144}^{(E)}$. The conservative $k = N + \Delta + 4 = 144 \ge k_b(120, 20)$ is stated in the note and in the script output. *Residual nit (non-blocking):* the 9 remaining per-step checks at script lines 636–643 conjoin the identity $\operatorname{lcm} \cdot \gcd = L_{k-1} m_k$ with the substantive $L_k \mid T_k$. Only the second conjunct carries content. |
| Script comment ($K = 1..9$) | Closed | The comment at line 928 now reads $K = 1..8$, matching `range(1, 9)`. |

### Residual remarks (non-blocking)

- Proposition C1.2b's displayed telescoped expansion is imported from Phase 22 Lemma 5.2(2) under the stated admissibility divisibilities. Its new content, $D_0$-divisibility of the leading multiplier, is self-contained and correct. The note correctly claims nothing about the tail terms.
- Lemma C1.2a is still certified only for $k \le 20$ in the script. The reviewer's earlier extension to $k \le 60$ remains a scratch computation and is not part of the committed certificate.

### Post-repair verdict

**ACCEPT.** All 20 findings are closed: C-1, M-1 to M-4, and m1 to m15. The unreset $P_{k_j}$-product question is correctly downgraded to `Open`. The C1.3(3) certificate is exhaustive and honest about the $L = 60$ witness. The C2 corollary now claims exactly what the theorem proves. The script exits `0` with the reported `30,586` exact and `136` float checks. Sub-tracks C1–C4 are acceptable as revised. Their evidence labels follow the `AGENTS.md` discipline, and floating-point outputs remain finite measurements only.

**Cross-model review is not independent human peer review.** This re-check was performed by one AI model (Claude Opus 5.5) on revisions of work drafted by another model. Its conclusions rest on finite computations and model reasoning. They do not replace verification by human referees or by the Lean kernel.
