# Independent Referee Review: Phase 23, Track A3–A4

- **Audited files (read-only):**
  - `notes/phase23/rational-scalings-and-signed-special.md`
  - `scripts/phase23_rational_signed.py`
- **Verdict:** **ACCEPT AFTER REVISION**
- **Epistemic caveat:** Cross-model review is not independent human peer review.

---

## Executive Summary

Track A3–A4 presents a strong, largely rigorous body of results on rational scalings of the flagship $q$-series ($D^j E_b$, $D^j E_b^3$, $\Theta_3(1/b)$, $(a/2)E_b^2$) and signed $q$-digamma reflections ($a_{r,M} = \tau_{r,M} - \tau_{M-r,M}$). Every headline theorem is **mathematically true** and its core proof architecture survives adversarial scrutiny. Independent execution of `python -B scripts/phase23_rational_signed.py` exits with code `0` (`ALL CHECKS PASSED: 212640 checks in 4.7 s`), and independent exact-digit and algebraic spot checks confirm the underlying computations. Evidence classes (`Paper proof`, `Finite computation`, `Finite measurement`, `Conditional`, `Open`) are cleanly separated throughout.

However, the audit identified **0 Critical**, **5 Major**, and **9 Minor** findings that must be repaired before final acceptance:

1. **Major M1** — Sign/convention contradiction for $w_0^+ - w_0^-$ between §0.1/Theorem 1.1 and Theorems 2.2–2.3 (lines 104, 118).
2. **Major M2** — Wrong term period $\Lambda = \operatorname{lcm}(2t, d)$ for $D^j E_b$ ($j \ge 1$) when $d$ is even (note line 48; script line 138).
3. **Major M3** — False quantitative word-count bound $d(R+2)$ and omitted dependence on $(c_k, \operatorname{sgn}(R_k))$ in the proof of Proposition 5.4 for $\tfrac{a}{d}E_b$ (line 222).
4. **Major M4** — Incorrect witness $m = 7\cdot 199\cdot 307$ (should be $37\cdot 199\cdot 307$) for $M' = 27$ in the §9 table (line 304), contradicting both the script output and the theorem identity.
5. **Major M5** — Factual error in §3.5 (line 177) claiming base-10 $p=113$ realizes $t_p \equiv 2 \pmod 4$, whereas $t_{113} = 112 \equiv 0 \pmod 4$.

None of the Major findings invalidates any main theorem statement (M1–M3 and M5 are localized formula/proof/commentary errors, and M4 is a table transcription error); all five have straightforward repairs.

---

## Detailed Findings

### Critical Findings

*None.*

---

### Major Findings

#### M1. Sign / convention contradiction for $w_0^+ - w_0^-$ in Theorems 2.2 and 2.3
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, lines 104 and 118 (versus lines 48, 69–70, 110, 113, 121).
- **Problem:**
  - Line 48 defines $w_0^+$ and $w_0^-$ purely by the run sign $\sigma$ of $z$ (independent of $\operatorname{sgn}(a)$): *"split by the run sign into $w_0^+$ (word $0^L$ when $a > 0$) and $w_0^-$ (word $(b-1)^L$)."*
  - Theorem 1.1 (lines 69–70) uses this $a$-independent convention:
    $$f_{0^L} - f_{(b-1)^L} = \operatorname{sgn}(a)(w_0^+ - w_0^-), \qquad f_0\bigl(\tfrac{a}{d}z\bigr) = \tfrac{1}{2} + \operatorname{sgn}(a)(w_0^+ - w_0^-)/2.$$
  - Theorem 2.2 (line 104) instead writes $w_0^+ - w_0^- = \operatorname{sgn}(a)\frac{\Xi_b(d)}{3t}$ and then writes $f_0(\tfrac{a}{d}E_2) = \frac{1}{2} + \operatorname{sgn}(a)\frac{\Xi_2(d)}{6t}$ (line 110). Substituting line 104 into Theorem 1.1 cancels $\operatorname{sgn}(a)^2 = 1$ and yields the wrong sign for $a < 0$.
  - Theorem 2.3 (lines 118, 121) has the exact same contradiction: $w_0^+ - w_0^- = \operatorname{sgn}(a)\frac{\Xi_3(d)}{L}$ alongside $f_0(\tfrac{a}{d}E_2^3) = \frac{1}{2} + \operatorname{sgn}(a)\frac{\Xi_3(d)}{2L}$.
  - Note that the proof of Theorem 2.2 (line 113) correctly derives $w_0^+ - w_0^- = \Xi/(3t)$ without $\operatorname{sgn}(a)$, and `scripts/phase23_rational_signed.py` (lines 305, 326, 346) computes `zp - zm = 2 * S` independently of `sa` and multiplies by `sa` once in `f0`.
- **Repair:** Remove $\operatorname{sgn}(a)$ from the formulas for $w_0^+ - w_0^-$ on lines 104 and 118 (giving $w_0^+ - w_0^- = \Xi_b(d)/(3t)$ and $w_0^+ - w_0^- = \Xi_3(d)/L$), or explicitly write $f_{0^L} - f_{(b-1)^L} = \operatorname{sgn}(a)\Xi_b(d)/(3t)$ and $f_{0^L} - f_{(b-1)^L} = \operatorname{sgn}(a)\Xi_3(d)/L$.

#### M2. Incorrect term period $\Lambda = \operatorname{lcm}(2t, d)$ for $D^j E_b$ ($j \ge 1$) with even $d$
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 48; `scripts/phase23_rational_signed.py`, line 138.
- **Problem:**
  - Line 48 asserts that the term sequence $\mathrm{tm}(i) = (-1)^i P(i)^j q^{P(i)} \bmod d$ of $D^j E_b$ ($j \ge 1$) has period $\Lambda = \operatorname{lcm}(2t, d)$, with no oddness restriction on $d$ (and Theorems 0.1 and 1.1 are stated for all $d \ge 2$ coprime to $b$, which includes even $d$ when $b$ is odd).
  - Since $P(i + \Lambda) - P(i) = \frac{\Lambda}{2}(6i + 3\Lambda - 1)$ and $3\Lambda - 1$ is odd whenever $\Lambda$ is even, $v_2(P(i+\Lambda) - P(i)) = v_2(\Lambda) - 1$. Thus $P(i+\Lambda) \equiv P(i) \pmod d$ requires $2d \mid \Lambda$, not merely $d \mid \Lambda$.
  - Whenever $d$ is even and $v_2(d) > v_2(t)$ (e.g. $(b, d) = (3, 2), (3, 4), (5, 4), (3, 8)$), $\Lambda = \operatorname{lcm}(2t, d)$ fails to be a period of $\mathrm{tm}(i)$ (for $DE_3 \bmod 2$: $t=1$, $\operatorname{lcm}(2t, d) = 2$, $P(0) = 0 \not\equiv P(2) = 5 \pmod 2$).
  - The same bug is coded into `euler_law` at `scripts/phase23_rational_signed.py:138` (`Lam = 2 * t if j == 0 else lcm(2 * t, d)`). Because `section_r5` only invokes `j >= 1` for $b=2$ (where $d$ is odd), no reported check in the script was corrupted, but the function is silently wrong for even $d$. (By contrast, the cube period $2\operatorname{lcm}(t, d)$ already satisfies $2d \mid \Lambda$ and is correct for all $d$.)
- **Repair:** Replace $\operatorname{lcm}(2t, d)$ with $2\operatorname{lcm}(t, d)$ on line 48 of the note and `2 * lcm(t, d)` on line 138 of `scripts/phase23_rational_signed.py`. With $\Lambda = 2\operatorname{lcm}(t, d)$, both $2t \mid \Lambda$ and $2d \mid \Lambda$ hold for all $d \ge 2$, and the proofs of Theorems 0.1 and 1.1 hold in full generality.

#### M3. False quantitative bound $d(R+2)$ and missing sign cases in the proof of Proposition 5.4
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 222.
- **Problem:**
  - The proof of Proposition 5.4 claims: *"For large $k$, the word at a shift at distance $r$ before an insertion is determined by the atom and $r$ when $r \le R = L + \lceil\log_b(4|a|d)\rceil$, and by the atom alone when $r > R$. ... So at most $d(R+2)$ words of length $L$ occur infinitely often, and this is $< b^L$ for large $L$."*
  - For $\tfrac{a}{d}E_b$, the fractional part at distance $r$ before insertion $p_k$ is $\bigl\{\frac{\alpha_n}{d} + \frac{a c_k}{d b^r} + \frac{a R_k}{d b^r}\bigr\}$ with $c_k \in \{+1, -1\}$ and $\operatorname{sgn}(R_k) \in \{+1, -1\}$ (both signs of $R_k$ occur for each sign of $c_k$, since $P(K)$ is followed by $P(-K)$ with the same sign whereas $P(-K)$ is followed by $P(K+1)$ with the opposite sign).
  - Consequently, when $r \le R$, the word depends on $(\alpha_n, r, c_k, \operatorname{sgn}(R_k))$—not on $(\alpha_n, r)$ alone—and whenever $\alpha_n b^r + a c_k \equiv 0 \pmod d$ (e.g. $r \le L$ with $d = 1$), $\frac{\alpha_n}{d} + \frac{a c_k}{d b^r}$ sits on a length-$L$ cylinder boundary so $\operatorname{sgn}(R_k)$ genuinely splits the word.
  - Even for $E_2$ ($d=1, a=1, b=2, L=8$), $4L = 32$ words of length $8$ occur infinitely often (e.g. at $r=2$, the four words $010^{L-2}, 001^{L-2}, 110^{L-2}, 101^{L-2}$ all arise from the single pair $(\alpha_n, r) = (0, 2)$), which strictly violates the claimed upper bound $d(R+2) = 1 \cdot (8+2+2) = 12$.
  - The theorem statement (non-disjunctivity) remains true, because the corrected bound $4dR + d + 1$ (for $E_b$) and $dR + d$ (for $\Theta_3$) is still $O_{a,b,d}(L) < b^L$ for large $L$.
- **Repair:** State that for large $k$ (once $|a R_k| < b^{-L}$), the word at $r \le R$ is determined by $(\alpha_n, r, c_k, \operatorname{sgn}(R_k))$ (at most $4dR$ words for $E_b$, $dR$ for $\Theta_3$) and at $r > R$ by $(\alpha_n, \operatorname{sgn}(a c_k))$ (at most $d+1$ words), yielding at most $4dR + d + 1 = O_{a,b,d}(L) < b^L$ words occurring infinitely often for large $L$.

#### M4. Wrong flip witness $m = 7\cdot 199\cdot 307$ for $M' = 27$ in §9 table
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 304 (vs `scripts/phase23_rational_signed.py` output in section S3).
- **Problem:**
  - Line 304 prints `| 27 | 18 | $7\cdot199\cdot307$ | 151/920 |`, whereas the script constructs and verifies `m = 37^1*199^1*307^1` (with the same dominant share `151/920`).
  - Mathematically, $7 \cdot 199 \cdot 307$ is **wrong**: $\operatorname{ord}_{27}(7) = 9$, whereas $37 \equiv 199 \equiv 307 \equiv 10 \pmod{27}$ all have order $3$ modulo $27$ (giving $(1*\chi_0)(37\cdot 199\cdot 307) = (1+\omega)^3 = -1$). Substituting $7$ gives $(1+\zeta_9)(1+\omega)^2 \ne -1$, so the dominant-part sign flip fails for $m = 7\cdot 199\cdot 307$.
- **Repair:** Replace `$7\cdot199\cdot307$` with `$37\cdot199\cdot307$` on line 304.

#### M5. Factual error in §3.5 attributing $t_p \equiv 2 \pmod 4$ to $p = 113$ in base 10
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 177.
- **Problem:**
  - Line 177 writes: *"and an exceptional prime with $t_p \equiv 2 \pmod 4$ balances with positive conditional probability (base 10 realizes this at $p=113$)."*
  - However, for $p = 113$ in base $10$, $t_p = \operatorname{ord}_{113}(10) = 112 \equiv 0 \pmod 4$ (as stated in Example 3.4 on line 167), **not** $2 \pmod 4$. Here $h = 56$ is even, so $1 + (-1)^h z_h = 2$, and the balance $\Xi_{10}(113) = 0$ occurs because $A^-(k) \equiv 0 \pmod{113}$ holds at $k \in \{29, 56, 83, 112\}$ (the odd symmetric pair $\{29, 83\}$ cancels the even fixed points $\{56, 112\}$).
- **Repair:** Revise line 177 to state that an exceptional prime balances with positive conditional probability both for $t_p \equiv 2 \pmod 4$ (where $1 + (-1)^h z_h = 0$ already cancels the fixed points) and for $t_p \equiv 0 \pmod 4$ (via odd-indexed zeros, as base 10 realizes at $p = 113$ with $t_{113} = 112$).

---

### Minor Findings

#### m1. Imprecise characterization of $d_+ = d/d_-$ for even $d$
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 3.
- **Issue:** Line 3 defines $d_- = \gcd(d, \iota+1)$ and calls $d_+ = d/d_-$ "the part on which $\iota \equiv 1$" before restricting to odd $d$ in §§2–3. While $d_+ \mid (\iota-1)$ holds for all $d$, when $4 \mid d$ one can have $\gcd(d_+, d_-) = 2$ (e.g., $d=8, b=3 \implies \iota=3, d_-=4, d_+=2$) and $d_+ \ne \gcd(d, \iota-1)$ (e.g., $d=8, b=7 \implies d_-=8, d_+=1, \gcd(8, \iota-1)=2$). CRT splitting $\mathbb Z/d \cong \mathbb Z/d_+ \times \mathbb Z/d_-$ requires odd $d$.
- **Repair:** Add "for odd $d$, $\gcd(d_+, d_-) = 1$ and $d_+ = \gcd(d, \iota-1) = d/d_-$."

#### m2. Omitted coprimality hypothesis on $a$ in Theorem 1.1 statement
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 66.
- **Issue:** Theorem 1.1 explicitly repeats "$d \ge 2$ be coprime to $b$" while leaving "$\gcd(a, d) = 1$, $a \ne 0$" to the global convention in line 3. (If $d \mid a$, there are no nonzero atoms.)
- **Repair:** Add "and $a \ne 0$ coprime to $d$" to line 66 for self-containedness.

#### m3. Missing "$j = 0$" qualifier in Lemma 2.1(1)
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 94.
- **Issue:** Part (2) writes "(Cube, $j=0$)" while part (1) writes only "(Euler)", even though part (1) also requires $j = 0$ (period $2t$ does not hold for $D^j E_b$ with $j \ge 1$).
- **Repair:** Change `(Euler)` to `(Euler, $j=0$)` on line 94.

#### m4. Missing sign qualification $a > 0$ for the digit law in Example 3.5
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 175.
- **Issue:** Example 3.5 states that for $\frac{a}{5}E_3^3$, "The digit law is $(\frac{9}{20}, \frac{3}{10}, \frac{1}{4})$." That vector is for $a > 0$; for $a < 0$ it reverses to $(\frac{1}{4}, \frac{3}{10}, \frac{9}{20})$.
- **Repair:** Add "(for $a > 0$)" after "The digit law is $(\frac{9}{20}, \frac{3}{10}, \frac{1}{4})$."

#### m5. Understated content claim and unstated reduced-denominator corollary in §6
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, lines 226–232.
- **Issue:** Line 230 notes "For $j=1,2$ the content is exactly 3", whereas the $k=1$ coefficient of $D^j E^3$ is $-3 \cdot 1^j = -3$, so the content is **exactly 3 for every $j \ge 1$**. Also, the proof that $\frac{a}{d}D^j E_2^3$ ($j \ge 1$) is simply normal whenever $3 \parallel d$ and $\operatorname{ord}_{d/3}(2)$ is odd (e.g. $d = 21$) is given only informally in the Content paragraph rather than stated explicitly as a corollary of Theorem 6.1 (note that when $3 \nmid d'$, $3$ is invertible mod $d'$ so the proof of Theorem 6.1 transfers directly to $F = \frac{1}{3}D^j E_b^3$ mod $d'$).
- **Repair:** Note that the $k=1$ term is $-3$ (so content is $3$ for all $j \ge 1$), and state the $3 \parallel d$ reduced-denominator base-2 consequence explicitly as a short corollary of Theorem 6.1.

#### m6. Ambiguous pronoun in Theorem 8.1
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 254.
- **Issue:** "In those cases $f_{0^L} \to 1$ in every base $b$" immediately follows "In every other case $a_{r,M}(n) < 0$ for infinitely many $n$...", creating momentary grammatical ambiguity.
- **Repair:** Replace "In those cases" with "In the nonnegative cases".

#### m7. Missing "distinct" on auxiliary primes in Theorem 9.4 proof
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, line 288.
- **Issue:** Choosing $\zeta_1 \zeta_2 \zeta_3 = 1$ frequently uses $\zeta_1 = \zeta_2$ (e.g. order 3 or $\zeta, \zeta, \zeta^{-2}$), so the primes $q_1, q_2, q_3$ with $\chi(q_i) = \zeta_i$ must be chosen **distinct** for multiplicativity $(1*\chi)(\prod q_i^{e_i}) = \prod (1*\chi)(q_i^{e_i})$.
- **Repair:** Change "and primes $q_i$" to "and three distinct primes $q_1, q_2, q_3$".

#### m8. Minor gaps in Theorem 10.1 proof and notation in Theorem 10.2
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, lines 319 and 323.
- **Issue:**
  1. In Theorem 10.1 step (iv) (line 319), $V_0'$ restricts $\operatorname{supp}(1*\chi_0)$ to $\gcd(n, Q) = 1$, whereas $\mathcal D$ in Theorem 9.5 requires $\gcd(n, M') = 1$; $V_0'$ should exclude the primes dividing $Q M'$. Also worth stating in one clause that $\{\bar\chi_0(s) : s \in G\} = \mu_\varphi$ spans $\mathbb Q(\zeta_\varphi)$ over $\mathbb Q$ (justifying $\operatorname{Tr}(\bar\chi_0(s)z) \ne 0$ from nondegeneracy of the trace form) and that the $\Pi_g$ are pairwise distinct $Q$-smooth integers even when $\varphi = 4$ forces an exponent $e_i = 0$ (since $\Pi_g = 1$ iff $g = 1$).
  2. In Theorem 10.2 (line 323), the proportion formula writes $\chi(r) = 1$ after stating the hypothesis for the reduced pair $(M', r')$; write $\chi(r') = 1$ (with $\chi$ odd mod $M'$) so it applies cleanly when $\gcd(r, M) > 1$.
- **Repair:** Make the two one-line clarifications in lines 319 and 323.

#### m9. `any(res)` vs `all(res)` check in `section_r4` of the verification script
- **Location:** `scripts/phase23_rational_signed.py`, line 628.
- **Issue:** For $b \in \{3, 4, 5, 6, 7, 10\}$ and $d \le 80$, line 628 tests `if any(res): lst.append(d)` rather than `all(res)`, whereas the note (line 207) lists those $d$ without restricting $a$. Independent verification confirms that `all(res)` actually holds for all 15 listed pairs $(b, d)$, so no result in the note is wrong.
- **Repair:** Add `check(any(res) == all(res), ...)` (or require `all(res)`) at line 628 so the script verifies uniformity over all unit numerators and signs.

---

## Checklist-by-Checklist Verification Record

| Checklist Item | Verification Outcome | Notes / References |
| --- | --- | --- |
| **1a. Nonzero-atom reflection symmetry ($c \mapsto -c$) & base-2 equivalence $f_0 = \frac12 \iff w_0^+ = w_0^-$** | **Verified** (with **M2**, **m2**) | $A^-(-k)=-A^-(k)$, $A(-k)=-A(k-1)$, $u^-_{-k}=-b^k u^-_k$, $u^+_{-k}=-b^{2k-1}u^+_{k-1}$; cube $\mathrm{tm}_3(-1-i)=\mathrm{tm}_3(i)$, $V(-2-k)=-V(k)$, $v_{-2-k}=-b^{k+1}v_k$; theta $B(-1-k)=-B(k)$, $b^{(-1-k)^2}=b^{2k+1}b^{k^2}$. Coset-smearing algebra in `smear`/`masses` verified exact. Base-2 $f_0=\frac12+\operatorname{sgn}(a)(w_0^+-w_0^-)/2$ exact; $f_0=\frac12 \iff w_0^+=w_0^-$ exact. Fix $\Lambda = 2\operatorname{lcm}(t,d)$ for even $d$ (**M2**) and restate $\gcd(a,d)=1, a\ne0$ in Theorem 1.1 (**m2**). |
| **1b. Exact closed forms for $E_2, E_2^3$ & prime reduction for composite $d$** | **Verified** (with **M1**, **M5**, **m1**, **m3**) | Lemma 2.1 CRT induction verified for odd $d$ (both Euler and cube). Theorems 2.2–2.3 parity formulas verified (fix extra $\operatorname{sgn}(a)$ on $w_0^+-w_0^-$ in **M1**). **Prime reduction (Lemma 3.1 + Theorem 3.2) is airtight against composite cancellation:** for any prime $p \mid d_-$, $v_2(t_p) = v_2(t)$ and $v_2(L_p) = v_2(L)$, so $t/t_p$ and $L/L_p$ are odd, forcing $A^-(h) \equiv \pm A^-_p(t_p/2) \pmod p$ and $V(L/2-1) \equiv \pm V_p(L_p/2-1) \pmod p$. If *any* prime $p \mid d_-$ is non-exceptional, $A^-(h) \not\equiv 0 \pmod{d_-}$ (resp. $V(L/2-1) \not\equiv 0 \pmod{d_-}$), so $z_h = 0$ (resp. $y_{L/2-1}=0$), forcing $\Xi$ (resp. $\Xi_3$) to be **odd**, hence strictly nonzero—no cross-prime cancellation can make $\Xi = 0$. Both `euler_half` and `cube_half` algorithms audited line by line and confirmed exact. Fix $t_{113} \equiv 0 \pmod 4$ remark (**M5**). |
| **1c. $(a/113)E_{10}$ balanced split & complement-symmetric full word law** | **Verified** | Independently verified $t = \operatorname{ord}_{113}(10) = 112$, $A^-$ zeros in $[1, 112]$ are $\{29, 56, 83, 112\}$, $A^+$ zeros in $[1, 224]$ are $\{13, 18, 93, 98, 125, 130, 205, 210\}$, giving exact $w_0^+ = w_0^- = 1/56$. By Theorem 1.1, full word law is complement-symmetric for all $L$ and all $a$. Digit vector `(353/3136, ...)` confirmed both algebraically and against certified base-10 digits ($N=10{,}000$, max error $0.0088$). |
| **1d. $(a/d)\Theta_3(1/2)$ simply normal in base 2 for every odd $d$ with $3 \mid d$** | **Verified** | $\operatorname{ord}_3(2)=2 \mid t$ (even), $q \equiv -1 \pmod 3$, $q^{i^2} \equiv (-1)^i \pmod 3$, $G \equiv 0 \pmod 3 \implies 3 \mid g$, and $B(k) \equiv \pm 1 \pmod 3$ for all $k$, so $B(k) \not\equiv 0 \pmod g$ regardless of $3^2 \mid d$, and $w_0 = 0$ for all $a$ coprime to $d$ (both $a>0$ and $a<0$). Independently spot-checked on certified digits for $\frac13\Theta_3(1/2)$ and $-\frac19\Theta_3(1/2)$. |
| **1e. $(1/7)\Theta_3(1/3)$ in base 3, prime criterion (Theorem 5.3), $b=6,d=79$ & $b=7,d=71$** | **Verified** (with **M3**, **m9**) | Theorem 5.3 proof completely sound: $h = t/2$ odd gives $q^{(i+h)^2} = -q^{i^2} \implies G \equiv 0 \pmod p \implies g = p$, zero-freeness gives $w_0 = 0$, primitive root gives uniform law on $(\mathbb Z/p)^\times$, and $p = bm+1$ partitions $\{1,\dots,p-1\}$ into $b$ equal blocks of size $m$. Independently verified $(b,p) = (3,7), (6,79), (7,71)$ all satisfy $t = p-1 \equiv 2 \pmod 4$, $b \mid (p-1)$, $G = 0$, zero-free; certified base-3 digits of $\frac17\Theta_3(1/3)$ ($N=20{,}000$) give $(0.33335, 0.33570, 0.33095)$ and exact $D_\infty = 2/7$. Fix Proposition 5.4 proof bound (**M3**). |
| **1f. $3 \mid D^j E^3$ content & derivative scaling criterion** | **Verified** (with **m5**) | $3 \mid (2k+1)T_k^j$ for all $k \ge 1, j \ge 1$, and $k=1$ gives coefficient $-3$, so exact content is $3$ for all $j \ge 1$. Theorem 6.1 proof with $T = \operatorname{lcm}(t,d)$ odd is completely airtight. Reduced denominator $d' = d/\gcd(d,3)$ verified for $d \le 45$ (note **m5**). |
| **1g. $(a/2)E_b^2$ in odd base $b$: middle digit $2/3$, $\{0, b-1\}$ share $1/3$, $D_\infty = 2/3$** | **Verified** | Frobenius $E(q)^2 \equiv E(q^2) \pmod 2$ gives exact odd-parity intervals $n \in [2P(-k), 2P(k+1))$ of length $4k+2$ alternating with $[2P(k), 2P(-k))$ of length $2k$, density $2/3$. Cylinder localization exact: $\frac12$ is the exact midpoint of the $((b-1)/2)^L$ cylinder at distance $\frac12 b^{-L}$ from both endpoints, and $B_{L'}(N) = o(N)$ from F22 Theorem 4.3 suppresses $|\frac a2 \tau_n|$ below $\frac12 b^{-L}$. Independently verified $D_\infty = 2/3$ holds unconditionally even if the $0^+/1^-$ split of $1/3$ oscillates. |
| **1h. A4 nonnegativity classification (Theorem 8.1)** | **Verified** (with **m6**) | Constraint $1 \le r < M/2$ explicitly stated, excluding $r = M/2$ (where $a_{r,M} \equiv 0$) and forcing $M' = M/\gcd(r,M) \ge 3$ and $1 \le r' < M'/2$. Reduction $a_{r,M}(n) = a_{r',M'}(n/g)$, prime witness $p \equiv -r' \pmod{M'}$ for $r' \ne 1$, Carmichael classification $\lambda(M')=2 \iff M' \in \{3,4,6,8,12,24\}$ for $r'=1$, and recurrence $a(nq) = 2a(n)$ for $q \equiv 1 \pmod M$ all verified. Counts $59 + 811 = 870$ for $3 \le M \le 60$ verified. |
| **1i. A4 universal sign flip, dominant flip, positive sign densities, & conditional $(S_U)$** | **Verified** (with **M4**, **m7**, **m8**) | Lemma 9.1 and Theorems 9.2–9.5 verified (in fact Theorem 9.2's $n \mapsto n q_1^2 q_2^2$ flip is an elementary 9-term cancellation identity valid even without $\gcd(r,M)=1$, confirming the Lean blueprint statement `antisymLambert_flip` on lines 412–415). Theorem 10.1 (cyclic $\varphi \ge 4$) and Theorem 10.2 (real type) proofs via Wirsing's theorem verified—injectivity of $n \mapsto n\Pi_{rs^{-1}}$ holds even when $\varphi=4$ forces an $e_i=0$. Theorem 10.3's fixed-ratio window $(N/K, N]$, Markov bounds ($\kappa \le \frac12 < 1$), and tail decay $N(\log N)b^{-H} = o(N/(\log N)^\kappa)$ all check out, and its **Conditional** status on $(S_U)$ is prominently and accurately maintained. Fix $M'=27$ table typo (**M4**). |
| **1j. Lean blueprint (§12, lines 365–421)** | **Verified** | All 11 proposed theorem statements checked mathematically for edge cases ($X=0,1$, $p=1$, $\gcd(r,M)>1$, even $d$); all 11 are true as stated. Appropriately labeled as unwritten/unchecked blueprints. |
| **2. Script run & quoted numbers** | **Exit 0; 1 table mismatch (M4)** | `python -B scripts/phase23_rational_signed.py` exited 0 (`212,640` checks in `4.7 s`). Every quoted number in the note matches the script output except `M'=27` on line 304 (`7*199*307` vs `37*199*307`, **M4**). Exact vs finite-measurement separation is consistently respected. |

---

## Summary of Required Revisions Before Acceptance

1. **Fix M1** (lines 104, 118): remove the duplicate $\operatorname{sgn}(a)$ factor from $w_0^+ - w_0^-$ in Theorems 2.2 and 2.3.
2. **Fix M2** (note line 48; script line 138): change the $D^j E_b$ ($j \ge 1$) term period from $\operatorname{lcm}(2t, d)$ to $2\operatorname{lcm}(t, d)$.
3. **Fix M3** (line 222): correct the Proposition 5.4 word-count argument and upper bound from $d(R+2)$ to $4dR + d + 1$ (accounting for $c_k$ and $\operatorname{sgn}(R_k)$).
4. **Fix M4** (line 304): change `$7\cdot199\cdot307$` to `$37\cdot199\cdot307$` in the §9 table for $M' = 27$.
5. **Fix M5** (line 177): correct the §3.5 remark so $p = 113$ ($t_{113} = 112 \equiv 0 \pmod 4$) is not misattributed to $t_p \equiv 2 \pmod 4$.
6. *(Recommended)* Apply minor precision edits **m1–m9**.

---

## Post-Repair Verification

- **Audited files (read-only):**
  - `notes/phase23/rational-scalings-and-signed-special.md`
  - `scripts/phase23_rational_signed.py`
- **Script execution:** `python -B scripts/phase23_rational_signed.py` exited with code `0` (`ALL CHECKS PASSED: 214603 checks in 4.1 s`). Every quoted number, table entry, fraction, count, and witness in `notes/phase23/rational-scalings-and-signed-special.md` matches the script output verbatim.
- **Verdict:** **ACCEPT AFTER REVISION** (all original **M1–M5** and **m1–m4, m6–m9** are cleanly closed; one new **Major regression (M6)** was introduced in the newly added **Corollary 6.2** for **m5**, requiring a two-word hypothesis fix).
- **Epistemic caveat:** Cross-model review is not independent human peer review.

### Verification of Original Findings

| ID | Status | Verification Summary |
| --- | --- | --- |
| **M1** | **Closed** | Duplicate $\operatorname{sgn}(a)$ removed from $w_0^+ - w_0^-$ in Theorems 2.2–2.3 (lines 104, 118); lines 107, 110, 121 consistently state $f_{0^L}-f_{(b-1)^L} = \operatorname{sgn}(a)(w_0^+-w_0^-)$ and the base-2 $f_0$ formulas. |
| **M2** | **Closed** | Term period for $D^j E_b$ ($j \ge 1$) updated to $2\operatorname{lcm}(t, d)$ in note (line 48) and script (`euler_period`, lines 137–154), with 2-adic explanation and explicit tests in `section_r5` (lines 777–825) on 8 even-$d$ pairs with $v_2(d) > v_2(t)$ (192 laws, period-independence via `mult=2`, failure of $\operatorname{lcm}(2t,d)$, and `(1/2)DE_3` comparison). *(Tiny non-blocking wording note on line 48: "$P(i)^j$ is $\Lambda$-periodic mod $d$ only when $2d\mid\Lambda$" is exact for $j=1$, while for even $j \ge 2$ e.g. $P(i+4)^2 \equiv P(i)^2 \pmod 4$, $2d\mid\Lambda$ is sufficient rather than strictly necessary.)* |
| **M3** | **Closed** | Proposition 5.4 proof (lines 222–236) cleanly rewritten with $(\alpha_n, r, c_k, \operatorname{sgn} R_k)$ case split, valid distance inequalities for $r \le R$ and $r > R$, and corrected bounds $4dR + d + 1$ ($E_b$) and $dR + d$ ($\Theta_3$). Exact $E_2$ check ($4L - 4$ recurrent words; $28 \le 42$ at $L=8$) verified both analytically and against 20,000 certified bits in `section_r4` (lines 688–725). |
| **M4** | **Closed** | §9 table (line 328) corrected to `$37\cdot199\cdot307$` for $M' = 27$, matching both the script output (`37^1*199^1*307^1`, share `151/920`) and the theorem identity. |
| **M5** | **Closed** | §3.5 (line 177) now distinguishes $t_p \equiv 2 \pmod 4$ from $t_p \equiv 0 \pmod 4$, accurately attributing base-10 $p=113$ to $t_{113}=112\equiv0\pmod4$ with $A^-$ zeros $\{29,56,83,112\}$, verified in `section_r2` (lines 524–530). |
| **m1** | **Closed** | Line 3 clarifies that CRT splitting $\mathbb Z/d \cong \mathbb Z/d_+ \times \mathbb Z/d_-$ and $d_+ = \gcd(d,\iota-1)$ hold for odd $d$ (with even-$d$ counterexample $d=8, b=3$). |
| **m2** | **Closed** | Line 66 explicitly includes "and let $a \ne 0$ be coprime to $d$" in Theorem 1.1. |
| **m3** | **Closed** | Line 94 updated to `(Euler, $j=0$)`. |
| **m4** | **Closed** | Line 175 specifies the digit law of $\tfrac a5 E_3^3$ for both $a>0$ and $a<0$. |
| **m5** | **Partially closed (new Major M6)** | Content paragraph (line 244) cleanly establishes exact content $3$ for all $j \ge 1$ via the $k=1$ coefficient $-3$, and `section_r5` checks $j \le 6$ and $d \in \{3, 21, 69, 93\}$. However, the newly stated **Corollary 6.2** omits the hypothesis that $d$ is **odd** (see **M6** below). |
| **m6** | **Closed** | Line 278 replaces "In those cases" with "In the nonnegative cases". |
| **m7** | **Closed** | Line 312 requires "three distinct primes $q_1, q_2, q_3$" and explains why distinctness is needed. |
| **m8** | **Closed** | Theorem 10.1 proof (line 343) clarifies $\varphi=4$ ($e_i=0$) distinctness of $\Pi_g$, restricts $V_0'$ to $\gcd(n, QM')=1$, and notes trace-form nondegeneracy on $\operatorname{span}_{\mathbb Q}(\mu_\varphi) = \mathbb Q(\zeta_\varphi)$. Theorem 10.2 (line 347) now uses $\chi(r')=1$. |
| **m9** | **Closed** | `section_r4` (lines 649–651) asserts `check(any(res) == all(res), ...)` and uses `if all(res):`, confirming uniformity over all unit numerators and signs. |

### New Finding Introduced in Repair

#### M6. Missing oddness hypothesis on $d$ in newly added Corollary 6.2 (false for even $d$ with odd $b$)
- **Location:** `notes/phase23/rational-scalings-and-signed-special.md`, lines 246 and 252 (and Summary table line 21).
- **Problem:**
  - Corollary 6.2 states: *"Let $j\ge1$ and let $d$ be coprime to $b$ with $3\parallel d$. Put $d'=d/3$ and suppose $\operatorname{ord}_{d'}(b)$ is odd (with $\operatorname{ord}_1(b)=1$). Then the limit word law of $\tfrac adD^jE_b^3$ in base $b$ is complement-symmetric."*
  - For $d' \ge 2$, line 252 applies Theorem 6.1 and claims that $T = \operatorname{lcm}(\operatorname{ord}_{d'}(b), d')$ is an **odd** antiperiod. However, Theorem 6.1 requires **both** $d'$ and $\operatorname{ord}_{d'}(b)$ to be odd. When $b$ is odd, $\gcd(d, b) = 1$ allows $d$ (and hence $d'$) to be **even** while $\operatorname{ord}_{d'}(b)$ is odd.
  - **Explicit counterexample:** Take $b = 5$, $d = 6$, $j = 1$. Every stated hypothesis holds: $j \ge 1$, $\gcd(6, 5) = 1$, $3 \parallel 6$, $d' = 2$, and $\operatorname{ord}_2(5) = 1$ is odd. Yet $T = \operatorname{lcm}(1, 2) = 2$ is even, and exact computation via `cube_law(5, 6, 1)` gives `law = (2, 6, 12, [9, 0, 0, 3, 0, 0], 3, 6)`, so $w_0^+ = \tfrac14 \ne \tfrac12 = w_0^-$ and the base-5 digit law of $\tfrac16 DE_5^3$ is $(\tfrac14, 0, \tfrac14, 0, \tfrac12)$, which is **not** complement-symmetric ($f_0 = \tfrac14 \ne \tfrac12 = f_4$).
  - (The base-2 specialization is unaffected because $\gcd(d, 2) = 1$ forces $d$ odd.)
- **Repair:** Add "odd and" to line 246: *"Let $j\ge1$ and let $d$ be **odd and** coprime to $b$ with $3\parallel d$."* (And optionally reflect "odd $d$" on line 21 of the Summary table.) Once this two-word hypothesis is added, Corollary 6.2 and its proof are completely airtight, and the entire Track A3–A4 deliverable is ready for **ACCEPT**.

### Final Confirmation (M6)
- **M6 (Closed):** `notes/phase23/rational-scalings-and-signed-special.md` now includes the `odd` hypothesis on $d$ in Corollary 6.2 (line 246) and the Summary table (line 21), and line 48 cleanly separates sufficiency of $2d \mid \Lambda$ for all $j \ge 1$ from necessity for $j = 1$.
- **Verdict:** **ACCEPT** (all Major findings M1–M6 and Minor findings m1–m9 are closed).
- **Epistemic caveat:** Cross-model review is not independent human peer review.
