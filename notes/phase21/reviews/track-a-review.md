# Referee Review — Phase 21 Track A (A1–A4)

- **Reviewer:** Gemini 4 Neon (independent mathematical referee)
- **Files audited in full:**
  - `notes/phase21/radix-lambert.md` (Theorem 1, Tracks A1–A2, §6 Lean core)
  - `notes/phase21/euler-square-and-forms.md` (Tracks A3–A4)
  - `scripts/phase21_radix.py` (executed via `python -B scripts/phase21_radix.py`: exit 0, 124,989 assertions in 26.5 s)
- **Cross-checked references:** `notes/phase20/coefficient-transfer.md`, `notes/phase20/lambert-leading-constant.md`, `notes/phase20/euler-product.md`, `notes/phase20/theta-and-modular.md`, `notes/phase17/multiplicative-lambert.md`, and `NormalityChecker/CoefficientTransfer.lean`.

---

## Executive Verdicts

| Sub-track | Verdict | Summary |
|---|---|---|
| **A1** (`L_χ(b)` across all radices) | **REVISE** | Arithmetic (§2) and Theorem A1's statement and constants are completely sound, but A1 depends directly on Theorem 1 in the same file, whose lower-bound marking proof has a **Critical** gap (unbounded $u(n)$ in $G$) and whose §6 Lean core contains a **literally false** theorem (`card_far_in_gap_ge`). |
| **A2** (Prime-density class `δ`, threshold `δ*`) | **REVISE** | Inherits Theorem 1's **Critical** marking/Remark 2 bug; has two **Major** issues: (i) natural density + Phase 17 harmonic hypothesis does not imply $S(N)\sim C_f N/(\log N)^\kappa$ without convergent Mertens constant (plus Sathe–Selberg is inapplicable to general prime sets in Prop. 4.1, though an elementary Hardy–Ramanujan bound rescues it); (ii) missing factor of $\kappa$ in the $\zeta_b$ constant formula on line 318. |
| **A3** (Euler's square `E_b^2 ↔ η(12τ)^2`) | **ACCEPT WITH MINOR POLISH** | Every calculation in §1 of `euler-square-and-forms.md`—the Euler product for $C_\eta = 2.41852914\ldots$, all local factors at $p=2,3$ and $p\equiv 1,5,7,11\pmod{12}$, the $12n+1$ factor, the Selberg–Delange second-order term $\lambda_1/\lambda_0=0.43361$ calibrated against Shanks, signed two-sided isolation, and both constants $\frac{3C_\eta}{4\log b}$ and $\frac{C_\eta(3+\log 2)}{4\log b}$—is verified correct. Depends upstream on the Theorem 1 fix in `radix-lambert.md`. |
| **A4** (Binary quadratic forms `Θ_Q(1/b)`) | **REVISE** | Proposition 2.1 (complete lower bound for every $Q$), Proposition 2.2 (concentration), Lemma 2.3 ($\mathbb Z/3$ Jacobsthal structure), and the remarkable radix-$2^k$ constant $1+\frac23(1-\pi_J)\log 2 \approx 1.362117$ are all **mathematically true**. However, A4 has two **Major** issues—Theorem A4(3) omits "fundamental $\Delta$" (false for $\Delta=-16,-12$), and Theorem A4(5)'s non-$2^k$ proof (line 252) states an overstated intermediate bound and skips $P_1$-truncation and the $\sqrt{LL}$ window—plus the inherited Theorem 1 mixture-form truncation gap (line 248). |

**Bottom line:** Every main theorem statement (once "fundamental $\Delta$" is restored to Theorem A4(3) and convergent Mertens constant is added to Theorem A2) and every asymptotic constant—including the $\mathbb Z/3$ constant $1+\frac23(1-\pi_J)\log 2$—is **mathematically true**. All Critical and Major defects are cleanly repairable without weakening any main conclusion.

---

## Detailed Findings

### Critical Findings

#### C1. Theorem 1 lower-bound marking conflates union cardinality with maximum index, and recommended Lean theorem `card_far_in_gap_ge` is literally false
- **Locations:**
  - `notes/phase21/radix-lambert.md`, lines 97–103 (definition of $G$), lines 121–125 (*Marking*), line 134 (*Remark 2*), and lines 357–363 (`card_far_in_gap_ge`).
  - `notes/phase21/euler-square-and-forms.md`, line 248 (mixture form of Theorem 1).
- **Mathematical defect:**
  1. **Unbounded $u(n)$ in $G$ (lines 121–122):** The good set $G$ enforces (G5) $u(n)\ge(\omega-\varepsilon)\lambda_N$, with **no upper bound on $u(n)$**. Line 121–122 marks $1\le j\le\lambda'$ and $u+1\le j\le u+\lambda'-1$, notes that their union has cardinality $\min(u,\lambda')+\lambda'-1\le 2\lambda'\le R$, and concludes: *"All these shifts $t-j$ lie in the arrival-free interval $[t-R,t)$, so the sets belonging to distinct good sources are disjoint, and $t-j\ge n-H>0$."* This confuses the **cardinality** of the union ($\le 2\lambda'-1\le R$) with its **maximum index** $u+\lambda'-1$. Whenever $u(n) > R - \lambda' + 1$, the second interval $\{u+1,\dots,u+\lambda'-1\}$ leaves $[1, R]$, violating Lemma 3.1 ($j\le g_t$), violating pairwise disjointness of marked shift sets across distinct good sources, and even permitting $t-j < 0$.
  2. **False claim in Remark 2 (line 134):** *"the marking requires $R\ge(1+\min(\omega,1))\lambda_N$"* is false for $\omega>1$. Even for the sub-optimal lower bound $(1+\min(\omega,1))\rho_N\lambda_N = 2\rho_N\lambda_N$, the second marked interval $\{u+1,\dots,u+\lambda'-1\}$ sits at offset $u+\lambda'-1 \approx (1+\omega)\lambda_N$ before $t$. If $\omega>2$ and $R=2\lambda_N$, the second interval does not even intersect $[1, R]$ and one obtains only $\lambda_N$ marks (constant $1$), not $2\lambda_N$. Marking the upper interval always requires $R\ge(1+\omega+\varepsilon)\lambda_N$ (which Theorem 1's $R_N = \lceil (2+\omega)\lambda_N + (B+2)\ell_N \rceil$ does satisfy, and which the very next sentence of Remark 2 asserts).
  3. **False Lean specification `card_far_in_gap_ge` (lines 358–363):** The recommended theorem states
     ```lean
     min u lam + lam - 1 ≤
       ((Icc 1 (min u lam + lam - 1)).filter
         (fun j => η ≤ dist0 ((C + A) / (b : ℝ) ^ j))).card
     ```
     **Explicit counterexample** (verified computationally): take $b=2$, $C=513=2^9+1$ ($2\nmid C$), $u=10$ ($2^9\le 513 < 2^{10}$), $\mathrm{lam}=3$, $A=0$, $\eta=1/16$ ($2\eta b^{\mathrm{lam}}=1$). Then $\mathrm{LHS}=\min(10,3)+3-1=5$, whereas for $j\in\{1,2,3,4,5\}$ we have $\mathrm{dist}_0(513/2^j)=2^{-j}$, which is $\ge 1/16$ only for $j\in\{1,2,3,4\}$ ($\mathrm{RHS}=4 < 5$). More generally, for $C=2^{u-1}+1$ ($u\ge 2\lambda$), `Icc 1 (2*lam - 1)` contains only $\lambda+1$ far indices rather than $2\lambda-1$.
  4. **Mixture form (`euler-square-and-forms.md` line 248):** Inherits the same omission—without truncating $u(n)\le \lambda_N$ in the good set, sources with large $u(n)$ have second marked intervals exiting $[t-R,t)$.
- **Required fix:**
  - Add **(G6) $u(n)\le(\omega+\varepsilon)\lambda_N$** (or $u(n)\le R_N-\lambda'+1$) to $G$ in Theorem 1. By (W3), $W(N)\le(\omega+o(1))S(N)\lambda_N$ together with $\#\{u(n)<(\omega-\varepsilon')\lambda_N\}=o(S(N))$ implies $\#\{u(n)>(\omega+\varepsilon)\lambda_N\}=o(S(N))$ (indeed $u(n)/\lambda_N\to\omega$ in $L^1$; line 129 already notes this for the $\omega>1$ case). Then $u(n)+\lambda'-1 \le (1+\omega+\varepsilon)\lambda_N \le R_N$ for every $n\in G$, so all marked shifts lie in $[t-R_N,t)\subset (0,N)$.
  - In the mixture form (`euler-square-and-forms.md` line 248), add $u(n)\le\lambda_N$ to $G$ (discarding $o(S(N))$ sources since $\mu([0,1))=1$, and ensuring $u(n)+\lambda'-1 < 2\lambda_N \le R_N$).
  - In `card_far_in_gap_ge` (line 362), change `Icc 1 (min u lam + lam - 1)` to `Icc 1 (u + lam - 1)` (verified true for all $b\ge2$, $u,\lambda\in\mathbb N$; in the counterexample above the RHS becomes $7\ge 5$).
  - In Remark 2 (line 134), correct *"the marking requires $R\ge(1+\min(\omega,1))\lambda_N$"* to *"the marking requires $R\ge(1+\omega+\varepsilon)\lambda_N$"*.

---

### Major Findings

#### M1. Theorem A2's hypotheses do not guarantee $S(N)\sim C_f N/(\log N)^\kappa$, and Proposition 4.1 mis-cites Sathe–Selberg for general prime sets
- **Locations:** `notes/phase21/radix-lambert.md`, lines 23, 29–33, 41, 261, 292, 304, 410.
- **Mathematical defects:**
  1. **Missing Mertens-constant convergence for $C_f$:** Theorem A2 assumes $\mathcal S$ has natural density $\delta\in(0,1)$ plus the Phase 17 bounded-error harmonic sum $\sum_{p\le x,\,p\in\mathcal S}1/p = \delta\log\log x + O(1)$, and asserts $S(N)\sim C_f N/(\log N)^\kappa$ by Wirsing's theorem. However, Wirsing's Satz 1 (quoted in `notes/phase17/multiplicative-lambert.md` lines 69–70) gives $S(N)\sim \frac{e^{-\gamma\delta}}{\Gamma(\delta)}\frac{N}{\log N}\prod_{p\le N}(1+\sum_{e\ge1}\mathbf 1_{c(p^e)>0}p^{-e})$. **Explicit counterexample:** choose $\mathcal S$ with local prime density $\delta + \frac{\cos(\log\log\log x)}{\log\log x}$ (which tends to $\delta$, so $\mathcal S$ has natural density $\delta$). Then $\sum_{p\le x,\,p\in\mathcal S}1/p = \delta\log\log x + \sin(\log\log\log x) + O(1)$, satisfying Phase 17's harmonic hypothesis, yet $S(N) \sim c\,e^{\sin(\log\log\log N)} N/(\log N)^\kappa$, so no asymptotic constant $C_f$ exists.
     - *Fix:* Add the convergent Mertens constant hypothesis $\sum_{p\le x,\,p\in\mathcal S}1/p = \delta\log\log x + M_{\mathcal S} + o(1)$ (satisfied by arithmetic progressions, Chebotarev sets, and Phase 17's $\lfloor rj\rfloor$ construction), OR state parts 1–3 normalized by the true support count $\rho_N\log_b(1/\rho_N)$ (note line 41/271 already switches to the true support count for part 1, even though line 31 states part 1 with $\Phi_N$ containing $C_f$).
  2. **Sathe–Selberg cited for arbitrary $\mathcal S$ in §4.1–4.2 (lines 292, 304):** The Sathe–Selberg method (Tenenbaum II.6) requires analytic continuation of $\sum_{p\in\mathcal S}p^{-s}$ in a zero-free region (valid for Chebotarev/progression sets, not for arbitrary prime sets of natural density $\delta$).
     - *Fix (elementary rescue):* The required uniform upper bound $\mathbb P(\omega_{\mathcal S,1}=m\mid c>0)\ll 1/\sqrt{LL}$ actually holds **unconditionally** for every prime set $\mathcal S$ with $\sum_{p\le x,\,p\in\mathcal S}1/p = \delta\log\log x + O(1)$ and $S(N)\gg N/(\log N)^\kappa$ via Hardy–Ramanujan's elementary Chebyshev induction: writing $n=p_1\cdots p_m\cdot r$ ($r$ squarefull outside $q_0$), weighting by $\log(p_1\cdots p_m)$ yields $\#\{p_1<\dots<p_m\in\mathcal S:p_1\cdots p_m\le x\}\ll \frac{x}{\log x}\frac{E(x)^{m-1}}{(m-1)!}\ll \frac{x}{\log x}\frac{e^{E(x)}}{\sqrt{E(x)}}\ll \frac{x}{(\log x)^\kappa\sqrt{\log\log x}}$ uniformly in $m\ge1$, and summing over $r$ with $\sum 1/r<\infty$ proves the bound without Sathe–Selberg.
  3. **Uniform integrability for discarded sources in Proposition 4.1 (line 304):** The bound $\sum Z_t \le (2\varepsilon+o(1))(\omega+\varepsilon)S\lambda_N$ applies the pointwise cap $u\le(\omega+\varepsilon)\lambda_N$ even to the discarded sources ($M>M_0$ or $V_b>\varepsilon\lambda_N$). This is valid because (W3) gives $L^1$ convergence $u(n)/\lambda_N\to\omega$, hence $\sum_{n\in E} u(n)\le(\omega+\varepsilon)\lambda_N|E|+o(S\lambda_N)$ for any $E$, but this step should be stated explicitly.
  4. **Zero higher powers in §3 (line 261):** Under Phase 17 hypotheses ($0\le c(p^e)\le e+1$), $c(p^2)$ may vanish for $p\in\mathcal S$, so $\#\{n\le N:c(n)>0,\,p\|n\}$ need not equal $S(N/p)-S(N/p^2)$, only $\le S(N/p)$. Since Lemma 2.1's upper bound replaces each bracket by $S(N/p^e)$ anyway, and the lower bound uses $c(n)\ge 2^{\omega_{\mathcal S,1}(n)}$ with Shiu on $z^{\omega_{\mathcal S,1}}$, the argument remains valid once stated with $\le S(N/p^e)$.

#### M2. Missing factor of $\kappa$ in the beyond-threshold constant formula
- **Location:** `notes/phase21/radix-lambert.md`, line 318.
- **Mathematical defect:** Line 318 claims *"the exact constant is $(\kappa+\delta\log 2-\zeta_b)/\log b\cdot C_f$, where $\zeta_b=\lim (S\lambda_N)^{-1}\sum_G Z_t$ if this limit exists."* Since $\rho_N\lambda_N \sim \frac{\kappa C_f}{\log b}\frac{LL}{(\log N)^\kappa}$, expanding $(1+\omega-\zeta_b)\rho_N\lambda_N$ with $\kappa\omega=\delta\log 2$ gives
  $$\frac{\kappa(1+\omega-\zeta_b)}{\log b}\,C_f \;=\; \frac{\kappa+\delta\log 2-\kappa\zeta_b}{\log b}\,C_f.$$
  At the extremal value $\zeta_b = \omega - 1 = \frac{\delta\log 2}{\kappa}-1$, the true constant is $2\kappa C_f/\log b$, matching $\kappa+\delta\log 2-\kappa\zeta_b = 2\kappa$, whereas the printed formula gives $\kappa+\delta\log 2-\frac{\delta\log 2}{\kappa}+1$ (which becomes negative for small $\kappa$).
- **Required fix:** Write $(\kappa+\delta\log 2-\kappa\zeta_b)/\log b\cdot C_f$ (or define $\zeta_b = \lim (S\ell_N)^{-1}\sum_G Z_t$).

#### M3. Theorem A4(3) ("One class per genus") omits the hypothesis "fundamental $\Delta$"
- **Location:** `notes/phase21/euler-square-and-forms.md`, line 28 (and §2.3 line 197).
- **Mathematical defect:** Parts 2 and 4 explicitly assume fundamental $\Delta$, and §4 (line 301) acknowledges that non-fundamental exact constants are open, but Part 3 omits *"fundamental $\Delta$"*. For non-fundamental one-class-per-genus discriminants, both $r_Q=w(1*\chi_\Delta)\mathbf 1_{\rm genus}$ and $C_Q=C_{\chi_\Delta}/g$ are **false**:
  - $\Delta=-16=2^2(-4)$, $Q=x^2+4y^2$ ($h=g=h_0=1$, $w=2$): $r_Q(2)=0\ne 2=2(1*\chi_{-16})(2)$, and $Q$ misses all $n\equiv 2\pmod 4$, giving $C_Q=\frac34 K \ne K = C_{\chi_{-16}}$.
  - $\Delta=-12=2^2(-3)$, $Q=x^2+3y^2$ ($h=g=h_0=1$, $w=2$): $r_Q(4)=6\ne 2=2(1*\chi_{-12})(4)$.
- **Required fix:** Add *"fundamental $\Delta$"* to Theorem A4(3) and §2.3.

#### M4. Overstated intermediate bound and skipped steps in Theorem A4(5) ("Other radices")
- **Location:** `notes/phase21/euler-square-and-forms.md`, line 252.
- **Mathematical defect:** Line 252 writes:
  > *"Write $P=2^{M'}P_1$, where $P_1$ is tight. Then $q^H\mid P+\beta$ forces $M'$ into one residue class modulo $\mathrm{ord}_{q^H}(2)\gg q^H$. The Sathe–Selberg local law $\mathbb P(M'=m)\ll(LL)^{-1/2}$ then gives $\mathbb P(v_q(P+\beta)\ge H)\ll q^{-H}+(LL)^{-1/2}$."*

  This skips three necessary ingredients, and the intermediate bound $\ll q^{-H}+(LL)^{-1/2}$ does not follow from $\mathbb P(M'=m)\ll(LL)^{-1/2}$ as written:
  1. **Case $q\mid P_1$:** Because $q\ge 3$ is odd and $\beta\in\{\pm 1,\pm 2\}$, $q\mid P_1$ forces $q\nmid(P+\beta)$, so $v_q(P+\beta)=0$ directly; only $q\nmid P_1$ puts $M'$ in one class modulo $d_H=\mathrm{ord}_{q^H}(2)$.
  2. **Union bound over $(P_1,\beta)$:** The residue class $m_0(P_1,\beta)\pmod{d_H}$ depends on both $P_1$ and $\beta$. One must truncate to $P_1\le P_0$ (losing $\mathbb P(P_1>P_0)$) and union bound over at most $4P_0$ pairs $(P_1,\beta)$, multiplying the local-law bound by $P_0$.
  3. **Gaussian window width $\sqrt{LL}$ vs $LL$:** Summing $\mathbb P(M'=m)\ll(LL)^{-1/2}$ over $m\equiv m_0\pmod{d_H}$ across $m\le 2LL$ yields $(\frac{2LL}{d_H}+1)(LL)^{-1/2}\asymp \frac{\sqrt{LL}}{q^H}+\frac{1}{\sqrt{LL}}$, which diverges for fixed $H$ as $N\to\infty$. One must restrict $M'$ to $|M'-\frac13 LL|\le K\sqrt{LL}$ (outside which $\mathbb P(|M'-\frac13 LL|>K\sqrt{LL})\ll e^{-cK^2}$ by Rankin), where the arithmetic progression contains $\le \frac{2K\sqrt{LL}}{d_H}+1$ terms and summing gives $\ll_q \frac{K}{q^H}+\frac{1}{\sqrt{LL}}$.
- **Required fix:** Replace the claimed $\ll q^{-H}+(LL)^{-1/2}$ with the truncated tightness argument: for any $\varepsilon>0$, choose $P_0(\varepsilon)$ and $K(\varepsilon)$ so that $\mathbb P(P_1>P_0)+\mathbb P(|M'-\frac13 LL|>K\sqrt{LL})<\frac23\varepsilon$; note $q\mid P_1\implies v_q(P+\beta)=0$; union bound over $P_1\le P_0$ ($q\nmid P_1$) and $\beta\in\{\pm1,\pm2\}$ to obtain
  $$\mathbb P\bigl(v_q(P+\beta)\ge H\bigr) \;\le\; \frac{2\varepsilon}{3} + O_q\!\left(P_0\Bigl(\frac{K}{q^H}+\frac{1}{\sqrt{LL}}\Bigr)\right),$$
  which is $<\varepsilon$ for $H\ge H_0(\varepsilon)$ and large $N$. This rigorously establishes tightness of $V_b$, hence $(\mathrm V_q)$ and $\mu=\delta_{\log 2}$. (Note: Sathe–Selberg *does* legitimately apply here because nonprincipal split primes form a Chebotarev set in the Hilbert class field $H_K$, and the elementary Hardy–Ramanujan upper bound also suffices.)

---

### Minor Findings

#### `notes/phase21/radix-lambert.md`
1. **Line 78 (W4 forward reference):** "(W4) where $G$ is the good set of the proof" depends on the proof's arbitrary $\varepsilon$ (via (G5)) and is further restricted on line 129. Defining $G_0$ directly in the statement via (G1)–(G4) and $u\le(\omega+1)\lambda_N$ removes this circularity.
2. **Lines 110–113 (E4):** The bound $\widehat{\mathsf A}_C(M)\le\mathsf A(2M)+O(1)$ is true, because for $n>2M$ we have $t(n)>M$ and $|U(n)|b^{M-t(n)}=|a(n)|b^{M-n}\le n^{o(1)}b^{-n/2}$ (whose sum is $o(1)$), whereas the terse reason *"because $t(n)\ge n/2$"* omits the essential cancellation $|U(n)|b^{V(n)}=|a(n)|$. Also line 113 prints $\ll \rho_N N/\log N$ where the estimate actually gives $\ll \rho_N N/(\log N)^2$ (and even $\rho_N^{2+\omega}N/(\log N)^2$).
3. **Line 124 ($\omega=0$):** When $\omega=0$, $(\omega-\varepsilon)\lambda_N<0$; writing $\max(1,(\omega-\varepsilon)\lambda_N)$ inside $\min(\cdot,\lambda')$ is cleaner (the bound still holds since $\Delta\ge(1-\varepsilon-o(1))\rho_N\lambda_N$).
4. **Line 174 (Lemma 2.1):** Lower integration limit $\log 2/\log N$ corresponds to $y=2$ where $\log\log 2<0$; separating $p=2$ as $O(1)$ and integrating from $\log 3/\log N$ is cleaner.
5. **Line 220 (Lemma 2.3(2)):** *"So the radix displacement has bounded conditional mean. Its limit is the local law $\Lambda_q=\dots$"* — $\Lambda_q$ is the limiting conditional mean of $v_q(c(n))$, which equals the limit of $V_b(n)$ only when $b=q$ is an odd prime (for composite $b$ such as $b=6$ or $b=10$, $\Lambda_q$ is only an upper bound on $\mathbb E[V_b]$, as the script's own output `b=3: 0.0556` vs `b=6: 0.0507` illustrates).

#### `notes/phase21/euler-square-and-forms.md`
6. **Line 44 (dichotomy scope):** *"So the dichotomy between radix $2^k$ and other radices persists for every binary form"* slightly overstates what is proved: unconditionally it is established for fundamental $\Delta$ with $h_0=1$ or $\mathrm{Cl}\cong\mathbb Z/3$, and conditionally (under $(\mathrm V_q)$) for all fundamental $\Delta$ (since $1+(1-h_0^{-1})\log 2 < 1+\log 2$); for non-fundamental and imprimitive forms, only the order and lower value $1$ are proved here.
7. **Lines 81–84 (A3 character notation):** $\chi_{-4}$ and $\chi_{-3}$ denote imprimitive mod-12 characters on line 81 and primitive mod-4/mod-3 characters on line 84; distinguishing $\chi_{-4}^{(12)},\chi_{-3}^{(12)}$ makes the Euler factors $(1+3^{-s})$ and $(1+2^{-s})$ transparent. Also line 122: write $v_q(|a_2(n)|)$ since $a_2(n)$ is signed.
8. **Line 152 (F2, non-fundamental $\Delta_0$):** For non-fundamental $\Delta_0=f^2 D_K$ and $\gcd(m,f)>1$, the number of proper representations of $m$ by *primitive* classes of discriminant $\Delta_0$ is **at most** (not equal to) $w\cdot\#\{t\bmod 2m:t^2\equiv\Delta_0\pmod{4m}\}$, because some solutions $t$ yield imprimitive forms. The subsequent upper bounds $C_{\Delta_0}2^{\omega(m)}$ and $C\,2^{\omega_{\rm split}(m)}\prod_{p^e\|m}(\lfloor e/2\rfloor+1)$ remain completely valid.
9. **Line 175 (Proposition 2.1, (E2)):** Typo *"have $g\mid j'-j=:h'$ with $1\le h'\le H$"* — should read *"have $h':=j'-j$ with $1\le h'\le H/g\le H$"* ($g$ divides $gj'-gj$, not $j'-j$).
10. **Line 187 (Proposition 2.1):** Setting $\eta=\zeta+2\Delta^+$ where $\Delta^+$ is *"Phase 20's upper bound (Theorem 5)"* is slightly ambiguous since Theorem 5 is stated with $\ll$; setting $\eta=\zeta+2\rho_N\lambda_N$ directly guarantees $\zeta+\Delta<\eta$ without relying on an unspecified constant.
11. **Line 191:** $\sigma_2(j)$ is used without definition (evidently $\prod_{p^e\|j}(\lfloor e/2\rfloor+1)$ from (F2)).
12. **Line 229 (Theorem A4(4)):** Strictly applies only the **upper bound** of Theorem 1 (which needs only $W(N)$ and $|a(n)|\le n^{o(1)}$, not the lower tail of (W3)) paired with Proposition 2.1 for the lower bound.
13. **Line 244 (Lemma 2.3 proof):** States $\lambda_\psi(p^e)=\pm\omega^k$ for nonprincipal split $p$ ($e\not\equiv 2\pmod 3$); in fact $\lambda_\psi(p^e)=(-1)^{e\bmod 3}\in\{\pm 1\}$ is always real, so $\beta(n,C)\in\{\pm 2\}$ for principal $C$ and $\beta(n,C)\in\{\pm 1\}$ for nonprincipal $C$ (and $v_2(3a_C/s)$ is *exactly* $1$ for $C=1$ and $0$ for $C\ne 1$ whenever $4\mid P(n)$). Not an error, just sharper than stated.
14. **Line 251 (Theorem A4(5), radix $2^k$):** The parenthetical *"(upper bound, then $P_0\to\infty$)"* is unnecessary: the non-J set $\mathcal N$ is itself multiplicative ($n=p^em\in\mathcal N\iff m\in\mathcal N$ for nonprincipal split $p$ and $e\not\equiv 2\pmod 3$), so Lemma 2.1's decomposition applies directly to $S_{\mathcal N}(x)\sim(1-\pi_J)C_{\chi_\Delta}x/\sqrt{\log x}$. Also worth noting explicitly that $v_2(r_Q(n))\ge v_2(s(n))$ holds for *all* non-J $n$ (even when $4\nmid P(n)$, giving the $W(N)$ upper bound cleanly), while $4\nmid P(n)$ fails on only $o(S)$ indices (for the lower bound).
15. **Lines 42, 258–259 (6th-digit rounding for $\Delta=-23$):** The Euler product $\prod_{p\text{ np split}}(1-\frac{1}{p^2+p+1})$ truncated at $p\le 65{,}640$ in `scripts/phase21_radix.py` gives $1-\pi_J=0.78363775$, $\pi_J=0.21636225$, factor $1.36211753$ (reported as `0.783638`, `0.216362`, `1.362118`). Independent verification to $p\le 5\times 10^6$ (via splitting of the Hilbert class polynomial $x^3-x-1\bmod p$) gives $1-\pi_J = 0.78363742\ldots$, $\pi_J = 0.21636258\ldots$, and $1+\frac23(1-\pi_J)\log 2 = 1.36211738\ldots$, shifting the 6th decimal place by 1 unit (`0.783637`, `0.216363`, `1.362117`).
16. **Line 279 (table commentary):** *"All ratios drift towards $1$ between $N=2^{14}$ and $2^{16}$"* holds for 19 of the 20 form-radix pairs, but fails for $\Delta=-23$, $Q=x^2+xy+6y^2$, $b=2$, where the ratio moves from `0.984` ($2^{14}$) to `0.953` ($2^{16}$), away from $1$ (caused by $S_Q/S_\Delta=0.752$ at finite height).

#### `scripts/phase21_radix.py`
17. **Execution and independence:** Ran `python -B scripts/phase21_radix.py` in the worktree; exited 0 in 26.5 s with 124,989 assertions. Every table entry in both notes matches the script output verbatim. The assertions genuinely and independently test the finite identities (pentagonal convolution vs progression-sieve factorization for $E_b^2$ to $10^6$; Selberg–Delange second-order formula calibrated against Shanks; exact lattice-point counts vs $\mathbb Z[\mathrm{Cl}]$ group-ring products for 7 discriminants to 65,640; exhaustive Lemma 2.3 checks for $\Delta=-23$; two-carry digit certification and Lemma 3.3 / centered-arc discrepancy sandwiches). Minor code notes: (i) `one_minus_piJ` truncates at $X=65{,}640$ (see Minor #15); (ii) parameter `q` in `support_constant(chi, q, L1, flags)` is unused; (iii) no non-fundamental/imprimitive form or second $\mathbb Z/3$ discriminant (e.g. $\Delta=-31$) is numerically spot-checked.

---

## Checkpoint Verification Matrix

| Audit Target | Independent Check Result |
|---|---|
| **Theorem 1 upper bound** (`radix-lambert.md` §1) | Verified valid. Notably, $\sum_{\tilde t(n)>N+L} b^{N+L-\tilde t(n)} \le b\sum_{i\ge 1}|a(N+L+i)|b^{-i} \ll N^{o(1)} = o(S(N))$ holds via $|a(n)|\le n^{o(1)}$. |
| **Theorem 1 lower bound & (E1)–(E5)** | (E1)–(E5) valid (noting $|U|b^{V}=|a|$ on $n>2M$ in (E4)); **Marking** has **Critical Finding C1** (missing $u(n)\le(\omega+\varepsilon)\lambda_N$ in $G$, false Remark 2 clause, false Lean `card_far_in_gap_ge`). |
| **A1** (`L_χ(b)`, Lemmas 2.1–2.4) | Exact $\sum\log c$ identity, Rankin exponent $\frac12(2^t-1)$, $v_q(c(n))$ bounded mean (including composite $b=2^a m$), $b=2^k$ remainder $2^{k-1}\mathrm{odd}(c)$, Brun pair sieve, and both constants $\frac{C_\chi}{2\log b}$ and $\frac{C_\chi(1+\log 2)}{2\log b}$ all verified correct (for primitive and imprimitive real nonprincipal $\chi$). |
| **A2** (Prime-density $\delta$, $\delta^*$, §4) | $\delta^*=1/(1+\log 2)=0.590616\ldots$, $\omega=\delta\log 2/\kappa$, bounds $[2\kappa,\kappa+\delta\log 2]$, and Baker/Matveev/Yu/Stewart/Korobov obstruction analysis verified sound (including $\mathrm{ord}_{b'^j}(2)\gg_b b'^j$ for composite odd $b'$). **Major Findings M1 & M2** apply. |
| **A3** ($E_b^2$, $C_\eta$, signed isolation) | Independently recomputed $C_\eta = 2.4185291395$ ($p\le 5\times 10^6$ + tail), verified all 4 mod-12 character factors $(1-2^{-s})(1-3^{-s})(1+3^{-s})(1+2^{-s})$ and $\frac{\pi^2\log(2+\sqrt 3)}{54}$, verified every term of $D_S$ and $\lambda_1/\lambda_0=0.43361$, verified signed two-sided isolation and constants $\frac{3C_\eta}{4\log b}$ and $\frac{C_\eta(3+\log 2)}{4\log b}$. |
| **A4** (Binary quadratic forms & $\mathbb Z/3$) | Prop. 2.1 (all $Q$, primitive/imprimitive, fundamental/non-fundamental) verified complete; Prop. 2.2 (concentration) verified airtight; $2^{m_2}\mid a_C$ with density $\frac{1}{2h_0}$ verified; Lemma 2.3 ($\lambda_\psi(p^e)=(-1)^{e\bmod 3}$ for $e\not\equiv 2\pmod 3$, Jacobsthal structure $3a_C=s(P+\beta)$ with $v_2(P+\beta)\in\{0,1\}$ for $4\mid P$) verified exact; $1-\pi_J=\prod_{p\text{ np split}}(1-\frac{1}{p^2+p+1})=0.78363742\ldots$ and radix-$2^k$ factor $1+\frac23(1-\pi_J)\log 2=1.36211738\ldots$ verified exact; all 7 $C_Q$ values in table verified to 6 decimal places. **Major Findings M3 & M4** and **C1** (mixture truncation) apply. |
| **§6 Recommended Lean core** (`radix-lambert.md`) | 8 of 9 declarations (`dist0`, `dist0_div_pow_ge`, `dist0_div_pow_eq`, `card_large_tail_le`, `sum_log_eq_sum_primePow`, `padicVal_succ_pos_imp`, `width_law_upper`, `width_law_lower`) verified mathematically true; **`card_far_in_gap_ge` is FALSE** (Finding C1). |

---

## Post-Repair Verification

Re-read the repaired `notes/phase21/radix-lambert.md` (415 lines), `notes/phase21/euler-square-and-forms.md` (304 lines), and the newly formalized Lean module `NormalityChecker/RadixWidthLaw.lean` (480 lines) in full.

### Verification of Every Finding

- **C1 (Critical — Theorem 1 marking, Remark 2, mixture form, `card_far_in_gap_ge`): RESOLVED.**
  - `radix-lambert.md` lines 78, 97, 104, 118, 122–130: fixes $\varepsilon\in(0,1)$, defines $G_0$ explicitly in (W4) without $\varepsilon$-circularity, adds **(G6)** $u(n)\le(\omega+\varepsilon)\lambda_N$, proves $L^1$ convergence $u(n)/\lambda_N\to\omega$ cleanly from $\mathbb E[(X_n-\omega)_-]\to 0$ and $\mathbb E[X_n-\omega]\le o(1)$ (since $|y|=y+2y_-$), and bounds every marked shift by $1\le j\le u+\lambda'-1\le(1+\omega+\varepsilon)\lambda_N\le R_N$.
  - `radix-lambert.md` line 135 (Remark 2) now states $R\ge(1+\omega+\varepsilon)\lambda_N$; line 138 (Remark 5) and `euler-square-and-forms.md` line 248 state the mixture-form truncation $u(n)\le\lambda_N$, guaranteeing $u(n)+\lambda'-1<2\lambda_N\le R_N$.
  - `radix-lambert.md` lines 360–366 and `NormalityChecker/RadixWidthLaw.lean` lines 139–218 correct `card_far_in_gap_ge` to `Icc 1 (u + lam - 1)` (with `1 ≤ u`, `1 ≤ lam`), and `RadixWidthLaw.lean` provides a complete, sorry-free, axiom-clean proof (inspected line by line across all 480 lines; `lake` was not available on the local Windows PATH to re-invoke the Lean compiler from this shell).
- **M1 (Major — Theorem A2 Mertens constant & Prop. 4.1 local bound): RESOLVED.**
  - `radix-lambert.md` lines 23, 29, 41, 263 add the convergent Mertens constant hypothesis $\sum_{p\le x,\,p\in\mathcal S}1/p = \delta\log\log x + M_{\mathcal S} + o(1)$ for $S(N)\sim C_f N/(\log N)^\kappa$, note the true-support-count normalization $\rho_N\lambda_N$ under $+O(1)$, and note $\#\{n\le N:c(n)>0,\,p^e\|n\}\le S(N/p^e)$ when higher powers vanish.
  - `radix-lambert.md` lines 294, 306, 413 replace the Sathe–Selberg citation for general $\mathcal S$ with the self-contained Hardy–Ramanujan Chebyshev induction and explicitly invoke $L^1$ uniform integrability of $u(n)/\lambda_N$ for discarded sources in Proposition 4.1.
- **M2 (Major — missing $\kappa$ in beyond-threshold constant): RESOLVED.**
  - `radix-lambert.md` line 320 now reads $(\kappa+\delta\log 2-\kappa\zeta_b)/\log b\cdot C_f$ with $\zeta_b=\lim(S\lambda_N)^{-1}\sum_{G_0}Z_t$, matching $2\kappa$ at $\zeta_b=\omega-1$.
- **M3 (Major — missing "fundamental $\Delta$" in Theorem A4(3)): RESOLVED.**
  - `euler-square-and-forms.md` lines 28, 36, 197, 237 explicitly restrict Parts 3 and 5 to fundamental $\Delta$.
- **M4 (Major — overstated bound / skipped steps in Theorem A4(5), non-$2^k$ radices): RESOLVED.**
  - `euler-square-and-forms.md` lines 252–254 now give the complete truncated tightness proof: choose $P_0(\varepsilon), K(\varepsilon)$ with $\mathbb P(P_1>P_0)+\mathbb P(|M'-\frac13 LL|>K\sqrt{LL})<\frac23\varepsilon$, handle $q\mid P_1$ ($v_q(P+\beta)=0$) separately from $q\nmid P_1$, count at most $\frac{2K\sqrt{LL}}{d_H}+1$ residues inside the $K\sqrt{LL}$ window, and union bound over the at most $4P_0$ pairs $(P_1,\beta)$ to obtain $\mathbb P(v_q(P+\beta)\ge H)\le\frac23\varepsilon+O_q(P_0(K/q^H+1/\sqrt{LL}))<\varepsilon$.
- **Minor findings #1–#16: ALL RESOLVED** cleanly across both notes (including (E4) cancellation and $(\log N)^2$, $\max(1,(\omega-\varepsilon)\lambda_N)$, $p=2$ split in Lemma 2.1, $\Lambda_q$ scope in Lemma 2.3(2), A3 character notation $\chi_0^{(12)},\chi_{-4}^{(12)},\chi_{-3}^{(12)}$ and $v_q(|a_2(n)|)$, dichotomy scope on line 44, (F2) "at most" + $\sigma_2(m)$ definition, Prop. 2.1 $h':=j'-j$ and $\eta=\zeta+2\rho_N\lambda_N$, A4(4) Theorem 1 upper-bound clarification, Lemma 2.3 real $\lambda_\psi(p^e)=(-1)^{e\bmod 3}$ and $\beta\in\{\pm 2\}$ vs $\{\pm 1\}$, A4(5) direct multiplicative $\mathcal N$ and unconditional $v_2(r_Q)\ge v_2(s)$, $\Delta=-23$ 6-digit values to $5\cdot 10^6$, and the 19-of-20 drift note on line 281).

### Residual Trivial Doc-Sync Nits (non-blocking)
Inspection of `NormalityChecker/RadixWidthLaw.lean` against `radix-lambert.md` §6 and `euler-square-and-forms.md` §4 caught four trivial Markdown-only sync details (zero mathematical or Lean proof errors):
1. `radix-lambert.md` line 342 opens `namespace NormalityChecker.RadixWidthLaw`, while line 403 still closes `end NormalityChecker.Phase21Radix`.
2. `radix-lambert.md` lines 398–402 include `theorem width_law_lower` inside the `RadixWidthLaw` block, though `NormalityChecker/RadixWidthLaw.lean` does not declare it (as line 406 and §7 line 410 accurately state, `CoefficientTransfer.one_sub_discrepancy_ge_of_bulk_and_far` already supplies it directly).
3. `radix-lambert.md` line 390 shows the unused `(ha : Summable ...)` hypothesis in `width_law_upper`, which `NormalityChecker/RadixWidthLaw.lean` (lines 466–473) omitted.
4. `euler-square-and-forms.md` line 304 still links `[radix-lambert.md §6](radix-lambert.md#6-recommended-lean-finite-core)` ("recommended" + old anchor instead of `#6-kernel-verified-lean-finite-core`).

### Updated Verdicts

| Sub-track | Updated Verdict |
|---|---|
| **A1** (`L_χ(b)` across all radices) | **ACCEPT** |
| **A2** (Prime-density class `δ`, threshold `δ*`) | **ACCEPT** |
| **A3** (Euler's square `E_b^2 ↔ η(12τ)^2`) | **ACCEPT** |
| **A4** (Binary quadratic forms `Θ_Q(1/b)`) | **ACCEPT** |
