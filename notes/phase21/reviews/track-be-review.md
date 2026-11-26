# Independent Mathematical Referee Report — Phase 21 Tracks B1–B4 and E1–E3

**Reviewer:** Gemini 4 Neon (Independent Referee)  
**Target files audited in full:**
- [character-q-digamma.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md) (Tracks B1–B4)
- [classical-barriers.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md) (Tracks E1–E3)
- [phase21_characters_classical.py](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase21_characters_classical.py)

**Cross-checked against:**
- [GeneralMassTransfer.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/GeneralMassTransfer.lean)
- [AntisymmetricLambert.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/AntisymmetricLambert.lean)
- [CoefficientTransfer.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/CoefficientTransfer.lean), [CharacterLambertTransfer.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/CharacterLambertTransfer.lean), [SharpTranslation.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/SharpTranslation.lean), [DiscrepancyGeometry.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/DiscrepancyGeometry.lean)
- Phase 19/20 notes: [coefficient-transfer.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase20/coefficient-transfer.md), [theta-and-modular.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase20/theta-and-modular.md), [classical-transfers.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase20/classical-transfers.md), [taylor-periods.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase19/taylor-periods.md), [addition.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase19/addition.md)

---

## 1. Executive Summary and Sub-Track Verdicts

The overarching mathematical program of Tracks B1–B4 and E1–E3 is genuinely strong, mathematically true in all headline claims, and commendably honest about scope, external inputs, and open barriers. **No Critical flaws** (invalidating a headline theorem) were found. However, a strict line-by-line audit uncovered **4 Major findings** (two concrete proof bugs in B3's Lemma 3.5 and Proposition 3.6, one unproved multi-stratum claim in B3 §3.2, and one false formula plus quantifier/witness failure in E2's Proposition 2.2) alongside **11 Minor findings**. All 4 Major findings admit clean, elementary repairs.

| Sub-Track | Verdict | Critical | Major | Minor | Headline Assessment |
| --- | --- | :---: | :---: | :---: | --- |
| **B1** | **ACCEPT WITH MINOR POLISH** | 0 | 0 | 4 | Core character support/mass theory, Theorem 1.5, and Corollary 1.6 are sound (with Corollary 1.6's exactness relying on repaired Prop 3.6). Fix missing "nonprincipal" in Prop 1.4. |
| **B2** | **ACCEPT WITH MINOR POLISH** | 0 | 0 | 2 | Mod-$2^k$ group structure, $2k-3$ $k$-independent supports, exact identity, radix condition $t \mid k-1$, explicit Prop 2.4 constants, and Hypothesis (U) are all verified. Minor missing quantifiers ($r \not\equiv s$, $1 \le r < 2^k$). |
| **B3** | **REVISE** | 0 | 3 | 3 | Elementary odd-periodic vanishing and the sector dichotomy statement (Thm 3.4) are true and insightful, but **Prop 3.6** has a coprimality gap breaking both the trace formula and injectivity, **Lemma 3.5** has an inverted bound $\max_i Q_i^{-1}$ and a multiset/distinctness gap, and **§3.2** claims multi-stratum exactness without proof. |
| **B4** | **ACCEPT WITH MINOR POLISH** | 0 | 0 | 4 | Exact `+` sign in $q$-digamma reflection matches Lean (`GeneralMassTransfer`, `AntisymmetricLambert`) and 50-digit checks; even-sector linear forms, two-character non-modular sums, and $q$-polygamma failure are solid. Minor boundary/quantifier cleanups needed. |
| **E1** | **ACCEPT** | 0 | 0 | 1 | Lemma 1.1, Theorem 1.2, Corollary 1.3 (all four bounds including $L=0$), Proposition 1.5, and Proposition 1.6 are completely rigorous. |
| **E2** | **REVISE** | 0 | 1 | 1 | Core inequalities (Prop 2.1, Prop 2.2's $1 - D_N(x; b^k) \le k(1 - D_{kN}(x; b))$, Prop 2.3, Prop 2.4) are sound, but **Prop 2.2** gives a false formula $D_N(1/(b+1); b) = b/(b+1)$ for all $b \ge 3$ (true value: $(b-1)/(b+1)$) and claims strictness for $k \ge 1$ using a witness that fails at $k=1$ and all odd $k \ge 3$. |
| **E3** | **ACCEPT** | 0 | 0 | 1 | Kernel equivalence, normal splitting, Stoneham top-band prime survival, Lemma 3.3 ($q$-generic collapse), residue splitting, and scope honesty are completely solid. |

---

## 2. Detailed Findings

### Critical Findings

*None.* Every headline theorem and barrier conclusion holds mathematically once the Major proof/formula repairs below are applied.

---

### Major Findings

#### [M1] Track B3 — Proposition 3.6: Missing coprimality of $q_1, \dots, q_{\varphi(H)-1}$ and $n$ breaks both the trace identity and injectivity
- **Location:** [character-q-digamma.md:375-378](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L375-L378)
- **Issue:** In the proof of Proposition 3.6, $m_0 = \prod_{\chi \in X_w \setminus O} p_\chi$ kills every character outside the maximal-order Galois orbit $O$. Then the proof takes:
  - squarefree $n$ coprime to $m m_0$ with all prime factors outside $Z_{\chi^*}$, and
  - (for $H \ge 4$) distinct primes $q_1, \dots, q_{\varphi(H)-1}$ with $\chi^*(q_l) = \zeta_H$,
  and asserts both $(1*w)(m_0 n q_1 \cdots q_i) = \operatorname{Tr}_{\mathbb Q(\zeta_H)/\mathbb Q}(\beta \gamma (1+\zeta_H)^i)$ and injectivity of $(n, i) \mapsto m_0 n q_1 \cdots q_i$.
  
  Two coprimality hypotheses are omitted, and both omissions invalidate the proof as written:
  1. **$q_l$ is not required to be coprime to $m m_0$.** (Coprimality to $m$ follows from $\chi^*(q_l) = \zeta_H \ne 0$, but coprimality to $m_0$ does not!) If $q_l = p_\chi$ for some $\chi \in X_w \setminus O$ (which can occur whenever $p_\chi \in Z_\chi$ happens to satisfy $\chi^*(p_\chi) = \zeta_H$, since $\zeta_H \ne -1$ for $H \ge 4$), then for $i \ge l$ we have $p_\chi^2 \Vert m_0 n q_1 \cdots q_i$. Since $2$ is even, $c_\chi(p_\chi^2) = 1 + (-1) + (-1)^2 = 1 \ne 0$, resurrecting the killed character $\chi$; simultaneously $c_{\chi^*}(q_l^2) = 1 + \zeta_H + \zeta_H^2 \ne (1 + \zeta_H)^2$.
  2. **$n$ is not required to be coprime to $Q := q_1 \cdots q_{\varphi(H)-1}$.** Because $H \ge 4$, $\chi^*(q_1) = \zeta_H \ne -1$, so $q_1 \notin Z_{\chi^*}$. Thus $n = q_1$ is an admissible input (assuming $q_1 \nmid m m_0$). This produces an explicit counterexample to injectivity:
     $$(n, i) = (q_1, 0) \longmapsto m_0 q_1, \qquad (n, i) = (1, 1) \longmapsto m_0 \cdot 1 \cdot q_1 = m_0 q_1.$$
     Moreover, whenever $q_l \mid n$ with $l \le i$, $\gcd(n, q_1 \cdots q_i) > 1$ breaks multiplicativity of $c_{\chi^*}$: $c_{\chi^*}(q_l^2) = 1 + \zeta_H + \zeta_H^2 \ne (1+\zeta_H)^2$, so $(1*w)(m_0 n q_1 \cdots q_i)$ does not equal $\operatorname{Tr}(\beta \gamma (1+\zeta_H)^i)$.
- **Repair:** Choose distinct primes $q_1, \dots, q_{\varphi(H)-1}$ **coprime to $m m_0$** with $\chi^*(q_l) = \zeta_H$ (possible by Dirichlet's theorem since $\chi^*: (\mathbb Z/m)^\times \twoheadrightarrow \mu_H$ is surjective). Set $Q = \prod_{l=1}^{\varphi(H)-1} q_l$, and restrict admissible $n$ to squarefree integers **coprime to $m m_0 Q$** with all prime factors outside $Z_{\chi^*}$. Then:
  - $p_\chi \Vert m_0 n q_1 \cdots q_i$ remains odd for all $\chi \in X_w \setminus O$;
  - $m_0, n, q_1 \cdots q_i$ are pairwise coprime and squarefree, so $c_{\chi^*}(m_0 n q_1 \cdots q_i) = c_{\chi^*}(m_0) c_{\chi^*}(n) (1 + \zeta_H)^i$;
  - $m_0 n_1 q_1 \cdots q_i = m_0 n_2 q_1 \cdots q_j$ forces equality of the $Q$-smooth parts $q_1 \cdots q_i = q_1 \cdots q_j$ (hence $i = j$) and $n_1 = n_2$;
  - removing the finitely many prime factors of $m m_0 Q$ does not affect Wirsing's asymptotic $\gg X(\log X)^{-1/H}$ on $n \le X / (m_0 Q)$.

---

#### [M2] Track B3 — Lemma 3.5: False density formula $R^{-1} \max_i Q_i^{-1}$ and multiset/distinctness gap
- **Location:** [character-q-digamma.md:364-368](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L364-L368)
- **Issue:** Two defects in the proof of Lemma 3.5:
  1. **Inverted extremum in the lower density bound:** Line 368 asserts "Hence the set has lower density at least $R^{-1}\max_i Q_i^{-1}$ times the density of squarefree integers coprime to $M'\mathcal P$." As written without parentheses, $\max_i Q_i^{-1} = (\min_i Q_i)^{-1}$, which is **false**: if almost all admissible $n$ require the largest $Q_i$, the surviving count up to $X$ is $\sim (\max_i Q_i)^{-1} \delta_{\mathcal S} X$, which can be arbitrarily smaller than $R^{-1} (\min_i Q_i)^{-1} \delta_{\mathcal S} X$. The bound must be $(\max_i Q_i)^{-1} = \min_i Q_i^{-1}$ (and once $(n, i) \mapsto n Q_i$ is injective, $n \mapsto n Q_{i(n)}$ is directly injective on $n \le X / \max_i Q_i$, so the factor $R^{-1}$ is not even needed).
  2. **Multiset and global prime-distinctness omission:** Monomials spanning the algebra generated by $\{1 + \chi(h) : h \in G\}$ are products over **multisets** $B_i$, not subsets of $G$. To ensure both that $Q_i$ is squarefree (so $c_\chi(Q_i) = \prod_{h \in B_i} (1 + \chi(h)) = f_i(\chi)$) and that the $Q_i$ are pairwise distinct (so $(n, i) \mapsto n Q_i$ is injective on $n$ coprime to $\mathcal P$), the primes $q_{i,h} \equiv h \pmod m$ (coprime to $M'$) must be chosen pairwise distinct across **all** indices $(i, h)$ (including repeated elements of $B_i$ and across distinct $i$).
- **Repair (and substantial simplification):** Note that for $h = 1$, $1 + \chi(1) = 2$ is constant, so $\chi(h) = (1 + \chi(h)) - \frac{1}{2}(1 + \chi(1))$ already lies in the **linear span** of $\{1 + \chi(h) : h \in G\}$. Since the columns $\{\chi \mapsto \chi(h)\}_{h \in G}$ span $\mathbb C^{X_u}$ by character orthogonality, the degree-1 functions $f_i(\chi) = 1 + \chi(h_i)$ ($1 \le i \le R$) already form a basis! No algebra generation, products, or multisets are needed: simply pick $R$ distinct primes $q_1, \dots, q_R \nmid M'$ with $q_i \equiv h_i \pmod m$ (by Dirichlet's theorem), put $\mathcal P = \{q_1, \dots, q_R\}$, and for each squarefree $n \le X / \max_i q_i$ coprime to $M'\mathcal P$, pick $i(n)$ with $(1*u)(n q_{i(n)}) \ne 0$. Injectivity of $n \mapsto n q_{i(n)}$ immediately gives lower density at least $(\max_i q_i)^{-1}$ times the density of squarefree integers coprime to $M'\mathcal P$.

---

#### [M3] Track B3 — §3.2: Multi-stratum exact support exponent $1/H$ claimed without proof
- **Location:** [character-q-digamma.md:324](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L324)
- **Issue:** Line 324 states unconditionally: *"By the character expansion of each stratum, the support exponent of an odd weight is $1/H$, with $H$ the largest order of a character occurring in some stratum."* (Also implicitly requires $w \ne 0$.) However, Proposition 3.6 only states and proves the lower bound $\gg X(\log X)^{-1/H}$ for a **single stratum** (and Remark 4 of Theorem 1.5 at line 134 explicitly limits sharpness to single-stratum weights). For a general multi-stratum odd weight, $(1*w)(n) = \sum_{g \mid \gcd(n, M)} (1*\tilde w_g)(n/g)$ mixes strata, and the note gives no proof ruling out cancellation between strata that could lower the support below $X(\log X)^{-1/H}$.
- **Repair:** The multi-stratum claim is in fact **true** for every nonzero $w \in \mathcal E_M$, and can be proved cleanly by extending Proposition 3.6: pick $g_0 \mid M$ minimal under divisibility among all strata carrying a character $\chi^*$ (mod $M/g_0$) of maximal order $H$. For $n = g_0 n'$ with $\gcd(n', M) = 1$, Lemma 3.3 gives
  $$(1*w)(g_0 n') = (1*\tilde w_{g_0})(n') + \sum_{g \mid g_0,\ g < g_0} (1*\tilde w_g)\bigl((g_0/g) n'\bigr).$$
  Lift $\chi^*$ and every occurring character $\chi$ (mod $M/g$) across all $g \mid g_0$ to characters modulo $M$. By minimality of $g_0$, every character from $g < g_0$ has even order $< H$, hence strictly larger killing set modulo $M$ than $Z_{\chi^*}$ (mod $M$). Thus every character outside the Galois orbit of $\chi^*$ in stratum $g_0$ has a prime $p_\chi \nmid M$ in $Z_\chi \setminus Z_{\chi^*}$. With $m_0 = \prod p_\chi$ (coprime to $M$, hence coprime to $g_0/g$), all terms from $g < g_0$ and all non-orbit characters in $g_0$ vanish at $n' = m_0 m q_1 \cdots q_i$ (for $\gcd(m, M m_0 Q) = 1$), reducing to the repaired single-stratum trace rotation of Proposition 3.6. Alternatively, restrict the claim at line 324 to single-stratum odd weights (which suffices for $w = \mathbf 1_r - \mathbf 1_{-r}$ and Corollary 4.2).

---

#### [M4] Track E2 — Proposition 2.2: False discrepancy formula $D_N(1/(b+1); b) = b/(b+1)$ for $b \ge 3$, and quantifier/witness failure for strict inclusion $K_b \subsetneq K_{b^k}$
- **Location:** [classical-barriers.md:187-196](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md#L187-L196)
- **Issue:** While the main inequality $1 - D_N(x; b^k) \le k(1 - D_{kN}(x; b))$ and the inclusion $K_b \subseteq K_{b^k}$ are completely valid, the strictness claim and its proof contain two errors:
  1. **False discrepancy formula for every $b \ge 3$:** Line 195 claims that multiplication by $b$ swaps $1/(b+1)$ with $b/(b+1)$, *"giving $D_N = b/(b+1)$ for even $N$."* This holds **only at $b = 2$** ($D_N(1/3; 2) = 2/3$). For the 2-point symmetric distribution on $\left\{\frac{1}{b+1}, \frac{b}{b+1}\right\}$ (equal weights $1/2$), the two complementary circle gaps have lengths $\frac{b-1}{b+1}$ and $\frac{2}{b+1}$, so for every even $N$:
     $$D_N\left(\frac{1}{b+1};\, b\right) = \max\left(\frac{1}{2},\,\frac{2}{b+1},\,\frac{b-1}{b+1}\right) = \begin{cases}\dfrac{2}{3}, & b = 2,\\[6pt] \dfrac{b-1}{b+1}, & b \ge 3.\end{cases}$$
     For example, at $b = 3$, the orbit is $\{1/4, 3/4\}$ with $D_{2m}(1/4; 3) = 1/2 \ne 3/4$; at $b = 10$, $\{1/11, 10/11\}$ has $D_{2m}(1/11; 10) = 9/11 \ne 10/11$. (The value $b/(b+1)$ belongs to $1/(b^2 - 1)$ from Phase 20, whose orbit is $\{1/(b^2-1), b/(b^2-1)\}$ with gap $\frac{1}{b+1}$; the verification script only tested $b = 2$ at line 1459.) Since $\frac{b-1}{b+1} < 1$, $1/(b+1) \notin K_b$ still holds.
  2. **Quantifier and witness gap for $K_b \subsetneq K_{b^k}$:** Proposition 2.2 quantifies over $k \ge 1$ and asserts *"Hence $K_b \subseteq K_{b^k}$, and the inclusion is strict: $1/(b+1) \in K_{b^2} \setminus K_b$."* First, strictness requires $k \ge 2$ (equality holds at $k = 1$). Second, the witness $1/(b+1)$ fails for every odd $k \ge 3$: $b^k \equiv -1 \pmod{b+1}$, so multiplication by $b^k$ still swaps $1/(b+1)$ and $b/(b+1)$, giving $1/(b+1) \notin K_{b^k}$!
- **Repair:** State strictness for $k \ge 2$ and replace the witness with $x = \frac{1}{b^k - 1}$ (which is fixed mod 1 by multiplication by $b^k$, so $D_N(x; b^k) = 1$ and $x \in K_{b^k}$, whereas its base-$b$ orbit cycles periodically through the $k \ge 2$ distinct points $\{b^j/(b^k - 1) : 0 \le j < k\}$, so $D_N(x; b)$ stays strictly below $1$ by `DiscrepancyGeometry.sampleDisc_le_one_sub` and $x \notin K_b$). If keeping $1/(b+1)$ for the $k = 2$ case, correct its even-$N$ discrepancy to $\max\bigl(\frac{2}{b+1}, \frac{b-1}{b+1}\bigr)$ (i.e. $2/3$ for $b=2$ and $(b-1)/(b+1)$ for $b \ge 3$).

---

### Minor Findings

#### Track B1
1. **[m1] Missing "nonprincipal" in Proposition 1.4** ([character-q-digamma.md:103,105](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L103-L105)): Line 103 states *"Hence $A_{c_\chi}(X) = O(X)$ exactly for real $\chi$"*. The principal character $\chi_0$ (order $h = 1$) is a real character yet has $\kappa_1 = 2 \csc(\pi/2) = 2$ and $A_{c_{\chi_0}}(X) \asymp X \log X \ne O(X)$. Similarly, line 105 uses $|\sum_{j=0}^{h-1} (1+\zeta^j)| = h$, which holds for $h \ge 2$ (for $h=1$ it equals $2$). Fix: state *"exactly for nonprincipal real $\chi$ ($h=2$)"* (or assume $\chi$ nonprincipal in Proposition 1.4).
2. **[m2] Implicit $p \nmid q$ and $h \ge 4$ in §1.1** ([character-q-digamma.md:59,63](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L59-L63)): Line 59 writes "$d_p \ge 2$" without reminding that $p \nmid q$; line 63 writes "$e \ge h - 1 \ge 3$" for a primitive $h$-th root of unity without restricting to $h \ge 4$ (and before $h$ is formally introduced in §1.2).
3. **[m3] Asymptotic error in Lemma 1.2(2) vs. Theorem 1.3** ([character-q-digamma.md:70,88](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L70-L88)): Lemma 1.2(2) writes $\sum_{p \le x, \chi(p) = -1} 1/p = \frac{1}{h}\log\log x + O_\chi(1)$, whereas Theorem 1.3's proof uses the asymptotic form $+ c_\chi + o(1)$ from Mertens' theorem in progressions to get $\sim C' (\log x)^\tau$ rather than merely $\asymp$. Adding $+ c_\chi + o(1)$ in Lemma 1.2(2) makes the deduction self-contained.
4. **[m4] Calling the Wirsing lower bound "elementary" and implicit $J \ge 1$** ([character-q-digamma.md:91,111](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L91-L111)): Line 91 describes the Wirsing+PNT-in-progressions lower bound as "elementary" (slightly loose terminology). In Theorem 1.5, $J \ge 1$ is implicit for $H = \max_j h_j$.

#### Track B2
5. **[m5] Missing $r \not\equiv s \pmod{2^k}$ in Theorem 2.3(1)** ([character-q-digamma.md:223-225,236](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L223-L236)): Theorem 2.3(1) asserts *"The support exponent $1/H_k$ is exact"* for both $Z_{k,r}(b)$ and $A_{r,2^k}(b) - A_{s,2^k}(b)$ under *"Let $k \ge 2$ and let $r, s$ be odd"*, omitting $r \not\equiv s \pmod{2^k}$ (when $r \equiv s$, the difference is $0$ with empty support). Also, the proof on line 236 only verifies exactness for $a_{k,r}$ (not for the class difference, which relies on Corollary 1.6's argument).
6. **[m6] Positivity of $r$ and $\rho_k \le 1$ regime in Proposition 2.4** ([character-q-digamma.md:242-251](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L242-L251)): "all odd $r < 2^k$" should be "all odd $1 \le r < 2^k$" since $r$ appears in the denominator $2^{k-1}/r$. Also, for the displayed bound with $\rho_k$ to hold uniformly if $k$ varies with $N$, one needs $\rho_k \le 1/e$ (or $\min(1, \rho_k)$) and $N \ge 2^k$ (for fixed $k$ and "all large $N$" as stated, both hold automatically, since $\rho_k \to 0$ and the extra error in $\widehat A(2N)/N$ is $o(1) < 2\log 2$).

#### Track B3
7. **[m7] "rational function" wording in Lemma 3.5** ([character-q-digamma.md:360](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L360)): Change "rational function on $(\mathbb Z/m)^\times$" to "rational-valued function on $(\mathbb Z/m)^\times$" to avoid confusion with quotients of polynomials.
8. **[m8] Trivial stratum $M/g = 1$ notation in §3.3** ([character-q-digamma.md:334-340](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L334-L340)): Clarify explicitly that for $g = M$ ($M/g = 1$), $(\mathbb Z/1)^\times = \{0\}$ has size $1$, so the coset condition $\sum_{x \in C} w(Mx) = 0$ is $w(0) = 0$.
9. **[m9] Note on §6 schematic Lean signature `coset_sums_zero_iff`** ([character-q-digamma.md:613-615](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L613-L615)): Mathematically valid (and explicitly marked schematic). No mathematical error in any §6 signature.

#### Track B4
10. **[m10] Edge case $2r = M$ and definition of $M'$ in Corollary 4.2** ([character-q-digamma.md:462-464](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L462-L464)): Define $g = \gcd(r, M)$, $M' = M/g$, $r' = r/g$ unconditionally (not only under "If $g > 1$"), and restrict *"the support exponent is exact"* to $2r \ne M$ (when $2r = M$, $X_{b,M,r} = 0$ has empty support and $M' = 2$ does not satisfy Proposition 3.1's $M' \ge 3$).
11. **[m11] Proof citation in Corollary 4.3** ([character-q-digamma.md:476](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L476)): Says *"use Theorem 4.1 termwise"*; since $w \in \mathcal E_M$ need not be odd, it is cleaner to cite the series definition of $\psi_q$ directly (after cancelling $-\log(1-q)$ via $\sum c_r = 0$).
12. **[m12] Summation upper limit and $n \ge 2$ in §4.7 ($q$-polygamma)** ([character-q-digamma.md:514-515](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L514-L515)):
    - Line 514 writes $p^{ej} - \sum_{i \ge 1} p^{(e-i)j} > 0$; this must be the finite sum $\sum_{i=1}^e p^{(e-i)j}$ (for $p=2, j=1$, the finite sum gives $2^e - (2^e - 1) = 1 > 0$, whereas the infinite sum $\sum_{i \ge 1}$ equals $2^e$ and gives $0$).
    - Also, local nonvanishing of each individual $\mathrm{id}^j * \chi$ does not by itself prove dense support for a linear combination $s_j = \mathrm{id}^j * (\mathbf 1_r - \mathbf 1_{-r})$; the dominant-divisor bound in the next bullet (for $r \equiv \pm 1$, or least prime $q_0 \equiv r \pmod M$ for general $r$) is what establishes positive density.
    - Line 515's $|s_j(n)| \ge n^j - \tau(n)(n/P^-(n))^j$ requires $n \ge 2$ ($P^-(1)$ is undefined).
13. **[m13] Borwein $c(q)$ fractional power & script tolerance** ([character-q-digamma.md:542](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L542), [phase21_characters_classical.py:1287](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase21_characters_classical.py#L1287)):
    - Borwein's $c(q) = q^{1/3} \sum_{m,n} q^{m^2+mn+n^2+m+n}$ requires $q = b^{-3}$ (or removing $q^{1/3}$) to be a shifted-lattice integer series in base $b$.
    - In `phase21_characters_classical.py` line 1287, the assertion uses `D(10) ** -50 * 10` ($10^{-49}$) while reporting "50 digits" (actual error is $\sim 10^{-78}$, so tightening to `TOL50` passes trivially).

#### Track E1
14. **[m14] Minor $-1$ offset in §1.4 remark** ([classical-barriers.md:113](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md#L113)): $k \ge \log_2 \ln N$ gives $k - 1 \ge (\ln\ln N)/\ln 2 - 1$; the $-1$ changes $2^{-s(k-1)}$ only by the constant factor $\alpha = 1/\ln 2$ (and disappears once $k \ge \log_2 \ln N + 1$), so Proposition 1.5's asymptotic order is unaffected. Also note that in Corollary 1.3, Lean's `finite_sparse_mass_transfer` applies vacuously to $A_{r, 2^k}$ (whose mass is $\asymp X \log X$, not $O(X)$), which does not affect the validity of the corollary.

#### Track E2
15. **[m15] Deduction of the "In particular" clause in Proposition 2.4 for rapidly growing $I(N)$** ([classical-barriers.md:208-211](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md#L208-L211)): The displayed inequality
    $$1 - D_N(E(b^{2^I})) \le \rho_I\bigl(2 I \log_b 2 + \log_b(\log(4N) + 1) + 4\bigr), \qquad \rho_I \le 2^{-I} + \frac{1}{N},$$
    holds rigorously for all $b \ge 2, I \ge 1, N \ge 1$ (since $\rho = \frac{1 + \lfloor (N-1)/2^I \rfloor}{N} \ge 2^{-I}$ always, and $\widehat A(2N)/N \le \log(4N)+1$ for all $N \ge 1$). However, if $I(N) \gtrsim N$ (e.g. $I(N) = N$), then $2^{-I(N)} \log\log N \to 0$ holds while the displayed RHS stays $\ge \frac{1}{N} \cdot 2 I(N) \log_b 2 \ge 2 \log_b 2 \not\to 0$. The conclusion $D_N(E(b)) - D_N(E^{(I(N))}(b)) \to 0$ is nevertheless **true** for all $I(N)$ with $2^{-I(N)} \log\log N \to 0$, because $\rho \ge \max(2^{-I}, 1/N)$ allows replacing $2 I \log_b 2$ by $2 \min(I \log_b 2, \log_b N)$ in the displayed bound, which then tends to $0$ unconditionally.

#### Track E3
16. **[m16] Upper bound $\rho \le 1$ in Lemma 3.3** ([classical-barriers.md:259](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md#L259)): Write $1/2 < \rho \le 1$ (since $-\log(1-q)$ has radius of convergence $1$ and is not analytic on $|q| < \rho$ if $\rho > 1$; the equality on $(0, \rho)$ already implicitly constrains $\rho \le 1$).

---

## 3. Audit Verification Checklist

### 3.1 Verification of Key Calculations and Proofs (Passed)
- **Transfer (T) ([character-q-digamma.md:39-47](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L39-L47)):** Verified from Phase 20 Theorem 1.7. Monotonicity of $\rho \mapsto \rho(2\log_b(1/\rho) + M)$ holds on $(0, 1]$ since $M \ge 3 > 2/\ln 2$; the constant $(2\kappa + \beta + o(1)) C_1$ is exact.
- **B1 Theorem 1.3 (Shiu & Wirsing hypotheses):** Confirmed $g = \mathbf 1[c_\chi \ne 0] \in \{0, 1\}$ is multiplicative with $g(p) = \mathbf 1[p \notin Z_\chi]$, $\tau = 1 - 1/h \ge 1/2 > 0$, $g(p^\nu) \le 1$, satisfying both Shiu (1980, Thm 1) and Wirsing (1961, Satz 1); no Euler factor vanishes ($1 + \sum_{\nu \ge 1} g(p^\nu) p^{-\nu} \ge 1$), so $C_\chi > 0$. Odd-order squarefree-coprime density $\frac{6}{\pi^2}\prod_{p \mid q}\frac{p}{p+1}$ is exact.
- **B1 Proposition 1.4 ($\kappa_h$ closed forms):** Independently derived from $\frac{2}{h}\sum_{j=0}^{h-1} |\cos(\pi j/h)|$ via Lagrange/Dirichlet sums: $\frac{2}{h}\cot\frac{\pi}{2h}$ for even $h$ and $\frac{2}{h}\csc\frac{\pi}{2h}$ for odd $h$. Wirsing majorant $\nu + 1 \le 2(3/2)^\nu$ holds for all $\nu \ge 0$ with $B = 3/2 < 2$.
- **B1 Corollary 1.6:** Verified that elements of maximal order $\lambda(q)$ generate any finite abelian group (via invariant factor decomposition $C_{n_1} \times \dots \times C_{n_s}$, $e_i = (e_s + e_i) - e_s$), so they cannot all lie in the proper subgroup $\{\chi : \chi(r) = \chi(s)\}$ when $r \not\equiv s \pmod q$. Answers Phase 20 Open Question 2 affirmatively.
- **B2 Lemma 2.1, Theorems 2.2–2.3, Proposition 2.4, Hypothesis (U):**
  - Order counts $3$ and $2^j$ ($2 \le j \le k-2$), conductors $2^{j+2}$, Galois orbit count $3 + 2(k-3) = 2k-3$, and distinctness of supports via $\{xy^{-1}: x,y \in Z_\chi\} = \ker\chi$ are all airtight.
  - Radix condition $c = b^j / 2^{k-1} \in b^{\mathbb Z} \iff b = 2^t$ with $t \mid k-1$ is exact.
  - Explicit mass bounds $\sum_{n \le X} \tau_{r, 2^k}(n) \le X(\frac{1}{r} + \frac{1+\log X}{2^k})$ and $\sum_{n \le X} \tau_{\rm odd}(n) \le X(1 + \frac{1}{2}\log X)$ hold for all $X \ge 1$, giving $A_{a_{k,r}}(X) \le X(\frac{2^{k-1}}{r} + \frac{3}{2} + \log X)$ and the Theorem 1.7 insertion with additive $+4$ ($\log_b^+(2/(b-1)) + 3 \le 4$) for all large $N$.
  - Under Hypothesis (U), solving $k (\log N)^{-2^{2-k}} (k + \log_2 \log N) < 1$ yields $k \le \log_2\ln\ln N - \log_2\ln\ln\ln N + 2 - o(1)$, matching the stated $+O(1)$ and table. Moreover, Siegel–Walfisz on $t \in [\exp(q^{1/4}), N]$ with effective constants (since real primitive 2-power characters have conductor $\le 8$) + Shiu indeed supports the heuristic remark about (U).
- **B3 Proposition 3.1, Theorem 3.2, Lemma 3.3, Theorem 3.4, Corollary 3.7:**
  - Odd characters have even order, max order $\lambda(M)$; elementary vanishing at $p \equiv -1 \pmod M$ for odd exponents is completely elementary and agrees with `AntisymmetricLambert.dirichletOneConv_eq_zero_of_odd_padicVal`.
  - Sector characterization (2) $\Leftrightarrow$ (3) via pushforward to $G/P_2$ is exact; cubic mod-7 example $2^{a+1}\cos(\pi(b-c)/3) \ne 0$ verified (never zero since $2k \ne 3(2m+1)$); Corollary 3.7 verified.
- **B4 Theorem 4.1, Corollaries 4.2–4.3, Theorem 4.4:**
  - Exact `+` sign in $[\psi_q(r/M) - \psi_q(1-r/M)]/\log q = +(A_{r,M}(b) - A_{M-r,M}(b))$ at $q = b^{-M}$ confirmed analytically and cross-checked with `GeneralMassTransfer.qDigamma_reflection_eq_residueLambert` and `AntisymmetricLambert.qDigamma_reflection_eq_dirichletSeries`.
  - Reflection theta identity $-\frac{d}{dx}\log\sum_{n \in \mathbb Z} (-1)^n q^{n(n-1)/2 + nx}$, $q$-Gauss multiplication equivalence to $A_{r,M}(b) = \sum_{j=0}^{n-1} A_{r+jM, nM}(b)$, and two-character sum $\chi_{-4} * \chi_{-3}$ ($\psi\varphi = \chi_{12}$ even, non-modular) are all exact.
- **E1 Lemma 1.1, Theorem 1.2, Corollary 1.3, Propositions 1.5–1.6:**
  - Lemma 1.1 constant $A_{2^k - 1, 2^k}(2) \le 2^{1 - 2^k}(1 + \frac{58}{105} \cdot 2^{3 - 2^k}) < 2^{1 - 2^k}(1 + 2^{3 - 2^k})$ and $2^{N-1} A < 1$ for $N < 2^k$ verified for all $k \ge 2$.
  - Corollary 1.3 checked across all four listed raw-support bounds (both $L \ge 1$ and $L = 0$ via AM–GM and $\widehat A(N) \ge A(N) \ge A(N)/2 \ge S(N)/2$), including $N = 1$.
  - Proposition 1.5 Markov + Shiu bound for $\tau^s$ ($s = \log_2 \alpha$, $A_1 = \alpha$) yields the exact Cramér exponent $Q(\alpha) = \alpha \ln \alpha - \alpha + 1 > 0$.
  - Proposition 1.6(2): because of the extra factor $(k + \log_2 \log N)$, everywhere the transfer bound is $< 1$ one has $S_{a_{k,r}}(N)/N \ll 1/\log_2 \log N \to 0$, so Theorem 1.2 forces $\sigma_N(r, k) \to 1$.
- **E2 Proposition 2.1, Proposition 2.2 (main inequality), Proposition 2.3, Proposition 2.4:**
  - All three liminf/limsup inequalities of Proposition 2.1 and sharpness via OP-01 verified.
  - Main base-change inequality $1 - D_N(x; b^k) \le k(1 - D_{kN}(x; b))$ of Proposition 2.2 verified ($\mu_0(I) - |I| \ge k(\mu(I) - |I|) + (k-1)|I| - (k-1) \ge k(\mu(I) - |I|) - (k-1)$).
  - Proposition 2.3 and Proposition 2.4 constants verified for all $N \ge 1, I \ge 1, b \ge 2$ (subject to [m15] for $I(N) \gtrsim N$).
- **E3 Propositions 3.1–3.2, Stoneham splitting, Lemma 3.3, §3.4:**
  - All identities ($B_{1,2} = \frac{1}{2}\ln 3$, $B_{0,2} = \frac{1}{2}\ln(4/3)$, $B_{1,4} - B_{3,4} = \arctan\frac{1}{2}$, $\ln 2 = \frac{2}{3}\sum_{k \ge 0} 9^{-k}/(2k+1)$) and top-band prime valuation $v_p(2^N P_N) = -1$ for $p \in (N/2, N]$ ($p \ne c$ for $Z_c$; $p \equiv r \pmod M$ for $B_{r,M}$) are exact.

### 3.2 Script Execution and Non-Circularity Audit
Executed `python -B scripts/phase21_characters_classical.py` in the worktree root:
- **Exit status:** `0` (`All 374826 checks passed in 25.0 s.`)
- **Numerical agreement:** Every single tabulated number, density, discrepancy, error bound, and assertion count quoted in both `character-q-digamma.md` and `classical-barriers.md` was cross-checked against the live stdout and matched exactly.
- **Non-circularity & rigor of checks:**
  - Cyclotomic identities (`section_B1`, `section_B2`, `section_B3`, `section_B3_sectors`) reduce direct divisor/character histograms modulo exact cyclotomic polynomials $\Phi_L(x) \in \mathbb Z[x]$, providing genuinely non-circular exact algebraic verification.
  - Certified enclosures (`Num`, `from_coeffs`, `disc`) rigorously bound $|b^K x - S| \le \mathrm{tailC}\cdot(K+2)$ (valid for all $b \ge 2$), enforce `err < 1e-10`, and compute exact extreme discrepancy via Niederreiter's formula `hi - lo`, justifying the claimed $10^{-9}$ certification tolerance. The guard-bit enclosures for $\ln 2$ and $\alpha_{2,3}$ in `section_E3` are also sound.
  - $q$-digamma checks (`section_B4`) cross-verify three genuinely independent computations (4th-order numerical derivative of $\log \Gamma_q$, direct series, Lambert series) against exact `Fraction` sums `A_exact`, and `section_E3` computes $\pi$ independently by Machin's formula.
  - **One blind spot caught by the audit:** `section_E2` (line 1459) only tested the strictness witness $1/(b+1) \in K_{b^2} \setminus K_b$ at $b = 2$ ($1/3$), which missed the false formula $D_N(1/(b+1); b) = b/(b+1)$ for $b \ge 3$ and the odd-$k$ witness failure flagged in **[M4]**.

### 3.3 Lean Cross-Check
Cross-checked against [GeneralMassTransfer.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/GeneralMassTransfer.lean) and [AntisymmetricLambert.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/AntisymmetricLambert.lean):
- `GeneralMassTransfer.log_mass_sparse_tendsto_one` matches the qualitative logarithmic-mass transfer needed for $\beta \in \mathbb N$ (in particular $\beta = 1$ for divisor sums).
- `GeneralMassTransfer.qDigamma_reflection_eq_residueLambert` and `AntisymmetricLambert.qDigamma_reflection_eq_dirichletSeries` confirm the exact `+` sign of Theorem 4.1.
- `AntisymmetricLambert.dirichletOneConv_eq_zero_of_odd_padicVal` matches Theorem 3.2(2) via the divisor involution $d \mapsto p^{a - v_p(d)} (d / p^{v_p(d)})$.
- Scope/honesty notes in `character-q-digamma.md` (§0, §6, §7) accurately represent the Lean status and do not overclaim formalization.

---

## 4. Post-Repair Verification

All 4 Major findings (**M1–M4**) and all 16 Minor findings (**m1–m16**) have been re-audited in full against the revised [character-q-digamma.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md), [classical-barriers.md](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md), [phase21_characters_classical.py](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/scripts/phase21_characters_classical.py), and [ClassicalBarriers.lean](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/NormalityChecker/ClassicalBarriers.lean). Every finding is cleanly resolved with no newly introduced mathematical errors:

- **[M1] & [M3] (B3 Proposition 3.6 & §3.2):** Verified line by line. Proposition 3.6 now covers arbitrary nonzero multi-stratum $w \in \mathcal E_M$ via minimal $g_0 \mid M$ carrying order $H$, lifting all characters across $g \mid g_0$ to modulo $M$ (preserving order and Galois orbits, and using $c_\chi((g_0/g)n') = c_\chi(g_0/g) c_{\chi^{\rm lift}}(n')$ for $\gcd(n', M) = 1$). The trace-rotation primes $q_1, \dots, q_{\varphi(H)-1}$ are explicitly chosen pairwise distinct and coprime to $M m_0$, and admissible squarefree $n \le X / (g_0 m_0 Q)$ are restricted to $\gcd(n, M m_0 Q) = 1$ outside $Z_{\chi^*}$. Both the trace identity and injectivity of $n \mapsto g_0 m_0 n q_1 \cdots q_{i(n)}$ (via the $Q$-smooth part) are now completely airtight.
- **[M2] (B3 Lemma 3.5):** Verified line by line. The proof now uses the clean degree-1 linear span $\chi(h) = (1 + \chi(h)) - \frac{1}{2}(1 + \chi(1))$ to extract a basis $1 + \chi(h_i)$ ($1 \le i \le R$), picks $R$ pairwise distinct primes $q_i \nmid M'$ with $q_i \equiv h_i \pmod m$, restricts to squarefree $n \le X / \max_i q_i$ coprime to $M'\mathcal P$, and obtains the correct lower density bound $(\max_i q_i)^{-1}$ times the density of squarefree integers coprime to $M'\mathcal P$.
- **[M4] (E2 Proposition 2.2):** Verified both proof and script. Strict inclusion $K_b \subsetneq K_{b^k}$ is now scoped to $k \ge 2$ with the universal witness $1/(b^k - 1) \in K_{b^k} \setminus K_b$; for $k = 2$, the even-$N$ discrepancy of $1/(b+1)$ is corrected to $\max\bigl(\frac{2}{b+1}, \frac{b-1}{b+1}\bigr)$ ($2/3$ at $b = 2$ and $(b-1)/(b+1)$ for $b \ge 3$); and `ClassicalBarriers.one_sub_radixDiscrepancy_pow_le` was cross-checked directly. `phase21_characters_classical.py` (lines 1456–1467) now tests $b \in \{2, 3, 5\}$ and $k \in \{2, 3\}$.
- **[m1–m16]:** Every minor item is verified resolved: Prop 1.4 (`h = 1` vs nonprincipal real `h = 2`), §1.1 (`p \nmid q`, `h \ge 4`), Lemma 1.2(2) (`+ c_\chi + o(1)`), §1.3 & Thm 1.5 (`J \ge 1`), Thm 2.3(1) (`r \not\equiv s \pmod{2^k}` and proof), Prop 2.4 (`1 \le r < 2^k` and `N \ge 2^k, \rho_k \le 1/e`), §3.3 (`m = 1` coset convention), Lemma 3.5 (`rational-valued`), Cor 4.2 (unconditional `g, M', r'` and `2r \ne M`), Cor 4.3 (series definition of $\psi_q$), §4.7 (finite sum $\sum_{i=1}^e$, $n \ge 2$, dominant-divisor density), §4.9 (`q^{-1/3} c(q)`), script line 1287 (`TOL50`), E1 §1.4 (`\log_2 \ln N + 1` and `-1` offset), E2 Prop 2.4 (`2 \min(I \log_b 2, \log_b N)` from $\rho \ge \max(2^{-I}, 1/N)$), and E3 Lemma 3.3 ($1/2 < \rho \le 1$).
- **Live re-run:** Executed `python -B scripts/phase21_characters_classical.py` — exited `0`, `All 374840 checks passed in 34.0 s.`
- **Non-blocking cosmetic notes (no mathematical impact):**
  - The verification prose counts in [character-q-digamma.md:569](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L569) and [classical-barriers.md:289](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/classical-barriers.md#L289) still quote the pre-repair assertion count `374,826` (now `374,840`).
  - Minor LaTeX placement `(\widehat{\mathbb Z/2^k})^\times` in [character-q-digamma.md:236](C:/Users/chaos/.t3/worktrees/MathematicsResearch/research-phase-20-gener-b08235755636abff/notes/phase21/character-q-digamma.md#L236) (standard form: $\widehat{(\mathbb Z/2^k)^\times}$), and §6 line 584 still retains the older "has not checked that they build" phrasing relative to the updated §0 line 47.

### Updated Final Verdicts

| Sub-Track | Initial Verdict | Final Post-Repair Verdict |
| --- | --- | --- |
| **B1** | ACCEPT WITH MINOR POLISH | **ACCEPT** |
| **B2** | ACCEPT WITH MINOR POLISH | **ACCEPT** |
| **B3** | REVISE | **ACCEPT** |
| **B4** | ACCEPT WITH MINOR POLISH | **ACCEPT** |
| **E1** | ACCEPT | **ACCEPT** |
| **E2** | REVISE | **ACCEPT** |
| **E3** | ACCEPT | **ACCEPT** |
