# Cross-Provider Mathematical Referee Review: Phase 22 Track A (A3–A4)

**Audited files**
- Note: [`notes/phase22/flagship-digit-laws.md`](../flagship-digit-laws.md) (lines 1–524)
- Script: [`scripts/phase22_flagship_digits.py`](../../../scripts/phase22_flagship_digits.py) (lines 1–1039)

**Verdicts**
- **Track A3 (A3.1–A3.4 — flagship digit laws):** **REVISE** — **Zero Critical flaws.** Every main theorem statement (Lemmas 0.1–0.3, Theorem 1, Proposition 1.1, Corollary 1.2, Proposition 2.2, Theorem 2, Corollary 2.3, Theorem 2.4 disjunctivity, Proposition 3.1, Theorem 3.2 exact $M \mid 24$ iff criterion, Propositions 3.3–3.4, Theorem 3.5, Proposition 3.6 Landau-ratio limit, Propositions 4.1–4.2, Theorems 4.3–4.4) is mathematically true, and the flagship proofs of disjunctivity for $D^j E_b$ (Theorem 2.4), the $M \mid 24$ nonnegativity characterization (Theorem 3.2), the unweighted sign limit `0.53319` (Proposition 3.6), and the $E_b^2$ sign rule / positive lower frequencies (Proposition 4.1, Theorem 4.4) are sound. Revision is requested to fix **5 Major findings** affecting A3 and §6 (a false explicit inequality in Lemma 2.1; a false bounded-coefficient / $O(L/\sqrt N)$ remark for $E_b^3$ on line 170; an invalid deduction of $B_L(N)=o(N)$ from $\|b^n z\|$-concentration in the proofs of Theorems 3.5 and 4.3; an unjustified subfield step in the proof of Proposition 4.2; and two false recommended Lean target statements in §6) plus Minor polishes and updating Theorem 4.4's Lemma S citation to Phase 22 Track D3–D4.
- **Track A4 (§5 — rational-scaling signed automata):** **REVISE** — **Zero Critical flaws.** All theorems, corollaries, and proofs in §5 (Lemma 5.1, Theorem 5.2, Corollary 5.2.1, Theorem 5.3 odd-order complement symmetry for both $E_b$ and $E_b^3$, Proposition 5.4, and all worked cases) are completely sound and rigorously proved. Revision is requested solely to fix **1 Major factual error** in the post-Conjecture 5.5 remark on line 444 (`w_0^- = 0 whenever -1 \notin \langle 2 \rangle in the range checked`, refuted inside the checked range by $\frac{1}{35}E_2^3$ and by negative $a$) plus Minor presentation/counting polishes.

> **Review scope caveat:** This is an automated cross-model mathematical audit, **not** independent human peer review.

---

## 1. Script Execution and Numerical Audit

- **Command:** `python -B scripts/phase22_flagship_digits.py` (run from the worktree root).
- **Result:** Exit code `0`; internal timer `15.8 s` (`16.2 s` wall-clock); **`5,816,654` checks passed**, matching §7 line 507 (`"about 20 s, performs 5,816,654 checks and exits 0"`).
- **Numerical and code verification:**
  - Every displayed value in the tables and prose of §1 (line 113), §2 (lines 188–195), §3 (lines 227, 240, 257–260, 280–289), §4 (lines 26, 68, 317, 361–369), and §5 (lines 433–446, including independent verification of unprinted $L=2$ frequencies for $\frac{1}{23}E_2$: $w_0^+ = w_0^- = \frac{1}{22}$, $f_{00}=f_{11}=\frac{61}{242}$, $f_{01}=f_{10}=\frac{30}{121}$) matches the script output (and exact rational arithmetic), **except** for:
    1. the false catalogue remark on line 444 (**Major 5**),
    2. `"all 27 pairs"` on lines 235 and 511 where the script checks and prints **30** pairs (**Minor 3**),
    3. `"26 pairs (b,d)"` on line 513 where the script's `table` has **13** pairs $(b,d)$ tested with $a=\pm 1$ (**Minor 5**), and
    4. `0.0072` vs `0.00712` and the $L=3$ range qualification on line 448 (**Minor 5**).
  - **Certified digit bracketing** (`certified_digits`, lines 122–143, and inline A4 bracketing, lines 884–896): sound. Python's integer floor division `//` satisfies `(Z - B - 1) // sh <= floor((Z + tau_M) / sh) <= (Z + B) // sh` for all signs of $Z$, and `lo % b^N` extracts the exact first $N$ fractional base-$b$ digits whenever `lo == hi`. Verified that all hardcoded tail bounds (`10**6` in A3.1 lines 276 & 292; `4*isqrt(X)+8` in A3.3 line 586; `8*isqrt(24*(Ncert+1600))+8` in A3.4 line 739) rigorously dominate the true tails.
  - **Scope hygiene:** Grepped both files for process language (`brief`, `prompt`, `agent`, `sub-agent`, `deliverable`, `worktree`, `todo`, `fixme`, `reviewer`, `referee`, model names): **zero matches**. Evidence separation between paper proofs, external inputs, open problems, and finite measurements is disciplined and transparent throughout.
  - **Existing Lean citations (§6, lines 454–458):** All 9 cited declarations exist with matching names and namespaces across `CoefficientTransfer.lean`, `DerivativeTransfer.lean`, `AntisymmetricLambert.lean`, and `NormalReciprocalCore.lean` (plus Phase 18's `discrepancy_deficit_le`).

---

## 2. Theorem-by-Theorem Audit Summary

| Component | Audit Outcome | Notes |
|---|---|---|
| **§0 Lemmas 0.1–0.3** (lines 34–69) | **Sound** | Telescoping digit identity holds for all real $z$ (including $z < 0$); Lemmas 0.1–0.3 are completely rigorous. |
| **§1 Theorem 1, Prop. 1.1, Cor. 1.2** (lines 70–116) | **Sound** (Minor 1) | Markov exchange $A^*(N,R)$ is exact; $(1*\chi)(n)\ge0$ holds for every real $\chi$ via prime-power factorization; all five Corollary 1.2 families and rates are valid. Minor polishes: self-referential $R$ in Thm 1(2) line 81; $\kappa>0,\beta\ge0$ and summation-by-parts justification of $A^*(N,R)\ll N(\log N)^\beta$ (making $a(m)\ll m^C$ redundant) in Thm 1(1); hardcoded `64` in script line 255. |
| **§2.1 Lemma 2.1 & Prop. 2.2** (lines 119–155) | **Major 1** (Lemma 2.1); Prop. 2.2 **Sound** | Explicit bound $R_i \le (m_i+K)^j C_{b,j} b^{-K}$ on line 137 is **false** for $b\ge 3, j=0$ (and $b=10, j=1$) because $C_{b,j}=\sum_{k\ge1}(1+k)^j b^{-k}$ drops the $k=0$ ($\Delta=K$) term (fix: $1+C_{b,j}$). Qualitative $R_i\to 0$ and Prop. 2.2 (including $|c_l|\le T_l^{3/2}$ for $E_b^2 DE_b$) are sound. |
| **§2.2 Theorem 2 & Cor. 2.3** (lines 156–175) | **Thm 2 & Cor. 2.3 Sound; Major 2** (line 170), Minor 2 | Dominance, gap-sign balance, $O_{b,j}((L+\log N)/\sqrt N)$ error, and base-$b^k$ Corollary 2.3 are sound. Line 170 **falsely claims** bounded coefficients and $O(L/\sqrt N)$ rate for $j=0$ without restricting to $E_b$ (false for $E_b^3$, which has unbounded coefficients $2k+1$ and $O((L+\log N)/\sqrt N)$). |
| **§2.3 Theorem 2.4 (Disjunctivity)** (lines 176–196) | **Sound** (Minor 2) | Adversarial check of planted windows confirms zero carry corruption from the left ($b^\ell \mid b^g I_{m_{i-1}}$) and right ($|\tau_m|<1$ gives exact $\epsilon\in\{0,-1\}$ via $\lfloor b^m z\rfloor - b^\ell\lfloor b^{m-\ell}z\rfloor = \lfloor b^m z\rfloor\bmod b^\ell$); leading-digit ratio argument ($v_{K+2}/v_K\to 1$) covers every base-$b$ word infinitely often for $D^j E_b$ ($j\ge 1$), $D^j E_b^3$ ($j\ge 0$), and $E_b^2 DE_b$. |
| **§3.1 Prop. 3.1, Thm. 3.2, Props. 3.3–3.4** (lines 197–243) | **Sound** (Minor 3) | Exact iff $a_{1,M}\ge0 \iff \lambda(M)=2 \iff M\mid 24$ ($M\ge 3$) is completely rigorous: all 6 divisors $3,4,6,8,12,24$ follow from Prop. 3.1 + Prop. 1.1; Cases A and B cleanly cover every $M\ge 3$ with $\lambda(M)>2$ with zero edge-case loopholes. Hyperbola mass law Prop. 3.4 is exact. Fix `"27 pairs"` $\to$ `"30 pairs"` (lines 235, 511). |
| **§3.2 Theorem 3.5 & Prop. 3.6** (lines 244–294) | **Statements Sound; Major 3** (Thm 3.5 proof), Minor 3 | Prop. 3.6 ($K_{-8}/(K_{-4}+K_{-8})=0.53319$ and $0.51532$) is completely rigorous—all four Euler factors and $L(1,\chi)$ values ($\pi/4$, $\pi/(2\sqrt 2)$, $\pi/3$, $\pi/(2\sqrt 3)$) verified. Scope honesty on open gap-weighted limits and `(H_gap)` is exemplary. However, Thm 3.5's proof (line 252) uses a reversed/invalid deduction from $\|b^n z\|$-concentration to $B_L(N)=o(N)$ (**Major 3**). |
| **§4 Propositions 4.1–4.2** (lines 295–324) | **Prop. 4.1 Sound; Major 4** (Prop. 4.2 proof) | Prop. 4.1 ($c(p)=+2 \iff p=x^2+36y^2$, $-2 \iff p=4x^2+9y^2$) and the multiplicative sign formula (line 314) are completely airtight. Prop. 4.2's reduced-form count ($\operatorname{Cl}(-144)\cong C_4$, $\operatorname{Gal}(H/\mathbb Q)\cong D_4$) is exact, but its Bauer-theorem step (line 321) assumes without proof that an arbitrary congruence condition mod $Q$ corresponds to a subfield of $\mathbb Q(\zeta_Q)$ (**Major 4**). |
| **§4 Theorems 4.3–4.4** (lines 325–370) | **Statements Sound; Major 3** (Thm 4.3 proof), Minor 4 | Thm 4.3's proof (line 333) repeats **Major 3** (cites $\|b^n E_b^2\|$ bound without bounding $|\tau_n|$ directly). Thm 4.4 is mathematically sound: Wirsing (1967, Satz 1.1) gives unweighted balance; $A_2(N)/(\log N)^{1/3}\asymp N/(\log N)^{5/6}=o(N/(\log N)^{3/4})$; carry-flip count is $O(Nb^{-H})$; and $c=\eta\kappa'/5$ is genuinely independent of $b$ and $L$. Open status of binary simple normality of $E_2^2$ is properly stated. Update Lemma S status (lines 25, 335) to cite completed Theorem S in Track D3–D4 (`partitions-carry-and-lemma-s.md`, §1). |
| **§5 Lemma 5.1, Thm. 5.2, Cor. 5.2.1, Thm. 5.3, Prop. 5.4** (lines 371–449) | **All proofs Sound; Major 5** (line 444 remark), Minor 5 | Strict interiority $\ge 1/(db^L)$, $O(1/\sqrt N)$ vs $O(\log N/\sqrt N)$ rates, tighter $E_b^3$ period modulus $\operatorname{lcm}(t,2,d)$ (valid even for even $d$ since $(-1)^{k+d}(2(k+d)+1)\equiv(-1)^k(2k+1)\pmod d$), odd-order antisymmetry ($u_{k+t}=-u_k$ and $v_{k+T}=-v_k$ via $i\mapsto T-1-i$), binary simple normality when $\operatorname{ord}_d(2)$ is odd, $b^L\le d+1$ bound, and all worked cases are completely rigorous. Line 444 contains one false factual claim about $w_0^-=0$ in the checked catalogue (**Major 5**). |
| **§6–§8 Lean targets, verification, open problems** (lines 450–524) | **Major 6** (§6 Lean targets), Minor 3 & 5 | Targets 1–5 are true; **Targets 6 and 7** (`chi12_sq_sub_sq`, lines 490–492; `abs_sum_alt_pent_gaps_le`, lines 495–496) are **false as stated** with explicit counterexamples (**Major 6**). |

---

## 3. Detailed Findings

### Critical Findings

None.

---

### Major Findings

#### Major 1 (A3.2, §2.1): False explicit remainder inequality in Lemma 2.1
- **File / lines:** `notes/phase22/flagship-digit-laws.md`, lines 137 and 142 (cf. line 81).
- **Issue:** Line 137 states that for the pentagonal families with $m_i = P_K^\pm$,
  $$R_i \le \sum_{\Delta \ge K} (m_i + \Delta)^j b^{-\Delta} \le (m_i + K)^j C_{b,j} b^{-K},$$
  where $C_{b,j} = \sum_{k \ge 1} (1 + k)^j b^{-k}$ was defined on line 81. Putting $\Delta = K + r$ starts the index at **$r = 0$**, not $r = 1$:
  $$\sum_{\Delta \ge K} (m_i + \Delta)^j b^{-\Delta} \le (m_i + K)^j b^{-K} \sum_{r \ge 0} (1 + r)^j b^{-r} = (m_i + K)^j (1 + C_{b,j}) b^{-K}.$$
  Omitting the $r = 0$ term makes the displayed bound **literally false** whenever $C_{b,j} < 1$: for $E_3$ ($b = 3, j = 0$), $C_{3,0} = \frac{1}{2}$, whereas at $m_i = P_K^-$ the very first term of $R_i$ (at $m_{i+1} = P_K^+$) is $3^{-K}$, so $R_i > 3^{-K} > \frac{1}{2} \cdot 3^{-K} = (m_i + K)^0 C_{3,0} 3^{-K}$. Similarly, for $D E_{10}$ ($b = 10, j = 1$), $C_{10,1} = \frac{19}{81} < 1$, so the first term $(m_i + K) 10^{-K}$ already exceeds $(m_i + K) C_{10,1} 10^{-K}$. (The qualitative consequence $R_i \to 0$ and the existence of $i_0(b, j)$ are unaffected.)
- **Actionable fix:** Replace $C_{b,j}$ with $(1 + C_{b,j})$ on line 137:
  $$R_i \le \sum_{\Delta \ge K} (m_i + \Delta)^j b^{-\Delta} \le (m_i + K)^j (1 + C_{b,j}) b^{-K}.$$

#### Major 2 (A3.2, §2.2): False bounded-coefficient and $O(L/\sqrt N)$ claim for $E_b^3$ ($j = 0$)
- **File / line:** `notes/phase22/flagship-digit-laws.md`, line 170.
- **Issue:** Line 170 reads:
  > *"For $j=0$ the coefficients are bounded, $\ell_i=L+O(1)$, and the rate improves to $O(L/\sqrt N)$. This recovers Phase 20, Theorem 2 for $E_b$ and Theorem 7(b) for $E_b^3$."*
  This is **false for $E_b^3$** ($j = 0$): its coefficients are $(-1)^k(2k+1)$, which are unbounded, its window length is $\ell_k = L + \frac{1}{2}\log_b T_k + O(1)$ (as correctly noted on line 154), and Phase 20 Theorem 7(b) gives the error $O((L + \log N)/\sqrt N)$, not $O(L/\sqrt N)$. Only $E_b$ ($j = 0$) has bounded coefficients and the improved $O(L/\sqrt N)$ rate.
- **Actionable fix:** Rewrite line 170 as: *"For $E_b$ ($j=0$) the coefficients are bounded, $\ell_i=L+O(1)$, and the rate improves to $O(L/\sqrt N)$ (recovering Phase 20, Theorem 2); for $E_b^3$ ($j=0$) the coefficients $2k+1$ already grow like $\sqrt{T_k}$, and Theorem 2 recovers Phase 20, Theorem 7(b) with rate $O((L+\log N)/\sqrt N)$."*

#### Major 3 (A3.3 & A3.4, §3.2 & §4): Invalid deduction of $B_L(N) = o(N)$ from $\|b^n z\|$-concentration in the proofs of Theorems 3.5 and 4.3
- **File / lines:** `notes/phase22/flagship-digit-laws.md`, line 252 (proof of Theorem 3.5) and line 333 (proof of Theorem 4.3).
- **Issue:**
  - Line 252 argues: *"The Phase 21 transfer with mass $O(X\log X)$ bounds $\#\{n<N:\|b^nz\|>\varepsilon\}$ by $o(N)$, and $\|b^nz\|=|\tau_n|$ whenever $|\tau_n|<\frac12$. So $B_L(N)=o(N)$, and Lemma 0.2 applies."*
  - Line 333 similarly invokes only $\#\{n<N:\|b^n E_b^2\|>\varepsilon\} = O(N\log\log N/\sqrt{\log N})$ (Phase 20, Proposition 5) and immediately applies Lemmas 0.2–0.3.
  - This implication runs **backwards**: knowing $\|b^n z\| \le \varepsilon < b^{-L}$ does **not** imply $|\tau_n| < b^{-L}$, because $\tau_n$ could lie close to a nonzero integer. For example, taking $a(m) = -(b-1)$ for all $m \ge 1$ gives $z = -1$, $I_n = -(b^n-1)$, and $\tau_n = -1$ for every $n \ge 0$; here $\#\{n<N:\|b^n z\|>\varepsilon\} = 0$, yet $B_L(N) = N$ and $f_{0^L}(N) = 1 \ne 0 = \rho_+(N)$.
  - Both theorems are completely **true** (with quantitative rates), because the sparse-support/mass Markov argument of Theorem 1 applied to $|a(m)|$ bounds $|\tau_n|$ directly: shifts with $(n, n+R] \cap \operatorname{supp}(a) = \emptyset$ satisfy $|\tau_n| \le \sum_{m>n+R} |a(m)|b^{n-m}$, so
    $$B_L(N) \le R\,S(N+R-1) + \frac{b^{L-R}}{b-1}\sum_{m>R}|a(m)|b^{-(m-R-N)_+}.$$
    Choosing $R = L + \lceil(\kappa+\beta)\log_b\log N\rceil$ directly gives $B_L(N) = O_{a,b,L}(N\log\log N / (\log N)^\kappa) = o(N)$ (with $\kappa = 1/\lambda(M')$, $\beta = 1$ in Theorem 3.5, and $\kappa = 1/2$, $\beta = 0$ unconditionally in Theorem 4.3).
- **Actionable fix:** State the signed Markov tail bound $B_L(N) \le R S(N+R-1) + \frac{b^{L-R}}{b-1} A^*(N,R)$ directly (either as a brief remark after Lemma 0.2 or Theorem 1, replacing $a(m)$ by $|a(m)|$), and invoke it in the proofs of Theorems 3.5 (line 252) and 4.3 (line 333) instead of passing through $\|b^n z\|$.

#### Major 4 (A3.4, §4): Unjustified subfield step in the proof of Proposition 4.2
- **File / line:** `notes/phase22/flagship-digit-laws.md`, line 321.
- **Issue:** Line 321 argues:
  > *"Suppose the condition were a congruence condition modulo $Q$ on $p\equiv1\pmod{12}$. Then the set of primes splitting completely in $H$ would agree, up to finitely many primes, with the set splitting completely in the compositum of $\mathbb Q(i,\sqrt3)$ with a subfield of $\mathbb Q(\zeta_Q)$. By Bauer's theorem (Neukirch, Algebraic Number Theory, VII.13.10), $H$ would equal that abelian field. Contradiction."*
  An arbitrary congruence condition modulo $Q$ on $p \equiv 1 \pmod{12}$ specifies an arbitrary subset $S \subseteq (\mathbb Z/Q'\mathbb Z)^\times$ (with $Q' = \operatorname{lcm}(12, Q)$), **not** a priori a subgroup. A union of residue classes $\{p : p \bmod Q' \in S\}$ is the set of primes splitting completely in a subfield of $\mathbb Q(\zeta_{Q'})$ only when $S$ is a subgroup, which is never established.
- **Actionable fix:** Replace the last three sentences of line 321 with the standard direct Bauer-inclusion argument (which is both shorter and completely rigorous): put $Q' = \operatorname{lcm}(12, Q)$, so that for some subset $S \subseteq (\mathbb Z/Q'\mathbb Z)^\times$ and all large primes $p$, $p$ splits completely in $H$ iff $p \bmod Q' \in S$. Since $H\cdot\mathbb Q(\zeta_{Q'})$ is a finite Galois extension of $\mathbb Q$, infinitely many primes split completely in it; any such prime satisfies both $p \in \operatorname{Spl}(H)$ and $p \equiv 1 \pmod{Q'}$, forcing $1 \in S$. Hence $\operatorname{Spl}(\mathbb Q(\zeta_{Q'})) \subseteq \operatorname{Spl}(H)$ up to finitely many primes. By Bauer's theorem (Neukirch, VII.13.10), $H \subseteq \mathbb Q(\zeta_{Q'})$, contradicting that $\operatorname{Gal}(H/\mathbb Q) \cong D_4$ is nonabelian while $\operatorname{Gal}(\mathbb Q(\zeta_{Q'})/\mathbb Q)$ is abelian.

#### Major 5 (A4, §5): False empirical claim about $w_0^- = 0$ in the checked catalogue
- **File / line:** `notes/phase22/flagship-digit-laws.md`, line 444.
- **Issue:** Line 444 states:
  > *"In the even-order examples the zero-atom split is unbalanced (for instance $w_0^-=0$ whenever $-1\notin\langle2\rangle$ in the range checked), but no proof is offered."*
  This parenthetical claim is **false inside the checked range itself** on two counts:
  1. For $\frac{1}{35}E_2^3$ ($d = 35 < 46$, inside the checked range), $\operatorname{ord}_{35}(2) = 12$ is even and $-1 \equiv 34 \notin \langle 2 \rangle \pmod{35}$ ($2^6 \equiv 29 \not\equiv 34$), yet direct evaluation of `cube_runs(2, 35)` gives $w_0^+ = \frac{1}{140}$ and **$w_0^- = \frac{1}{70} \ne 0$**.
  2. The checked catalogue tests **both signs** of $a$, and replacing $a$ by $-a$ swaps $w_0^+$ and $w_0^-$, immediately giving $w_0^- > 0$ and $w_0^+ = 0$ whenever $a < 0$ (e.g. $-\frac{1}{15}E_2$ has $w_0^+ = 0, w_0^- = \frac{1}{12}$).
  3. Even for $E_2$ with $a > 0$, the pattern breaks just beyond the checked range at $d = 91 = 7\cdot 13$ ($\operatorname{ord}_{91}(2)=12$, $-1 \notin \langle 2 \rangle$, $w_0^+ = \frac{1}{36}$, $w_0^- = \frac{1}{18} \ne 0$).
  (Note: the primary claim that $w_0^+ \ne w_0^-$ in all checked even-order cases **is** true; we independently verified $w_0^+ \ne w_0^-$ for all odd even-order $d < 100$ for $E_2$ and $d < 60$ for $E_2^3$, and verified Conjecture 5.5 across all coprime $a$ in that extended range with zero counterexamples.)
- **Actionable fix:** Restrict and correct the parenthetical example on line 444, e.g.: *"(for instance, for $\frac{a}{d}E_2$ with $a > 0$ and $d < 64$, $w_0^- = 0$ at every even-order $d$ with $-1 \notin \langle 2 \rangle$, though $w_0^- > 0$ already occurs for $\frac{1}{35}E_2^3$ and for $\frac{1}{91}E_2$, and $a < 0$ swaps $w_0^+$ with $w_0^-$)"* — or simply drop the false `-1 \notin \langle 2 \rangle` generalization and cite concrete examples such as $w_0^+ = \frac16, w_0^- = 0$ for $\frac13 E_2$ and $w_0^+ = \frac{1}{140}, w_0^- = \frac{1}{70}$ for $\frac{1}{35}E_2^3$.

#### Major 6 (§6): Two of the seven recommended Lean target statements are false
- **File / lines:** `notes/phase22/flagship-digit-laws.md`, lines 490–492 (`chi12_sq_sub_sq`) and lines 495–496 (`abs_sum_alt_pent_gaps_le`).
- **Issue:** Although §6 appropriately marks these as unverified target statements, two of them have immediate counterexamples and cannot be proved as written:
  1. **`chi12_sq_sub_sq` (lines 490–492):** Hypothesis `h3 : u.val % 3 = 0 ∨ v.val % 3 = 0` is an *inclusive* disjunction, which permits $3 \mid u$ and $3 \mid v$ simultaneously. For all four pairs `(u, v) ∈ {(3, 0), (3, 6), (9, 0), (9, 6)}` in `ZMod 12`, `hu`, `hv`, and `h3` all hold, yet `u ^ 2 - v ^ 2 = 9`, so `chi12 (u ^ 2 - v ^ 2) = 0 ≠ 1 = (if v.val % 3 = 0 then 1 else -1)`.
  2. **`abs_sum_alt_pent_gaps_le` (lines 495–496):** The sum runs over `Finset.range (K + 1)`, which **includes $k = 0$**, adding $(-1)^0(3\cdot 0 - 1) = -1$ to every partial sum. For every odd $K = 2m + 1$, the sum equals $-(3m + 3)$, so the LHS is $3m + 3$, whereas the RHS `(3 * K + 2) / 2` is $3m + 2$ in $\mathbb Z$ (and $3m + 2.5$ in $\mathbb R$). For instance, at $K = 1$: `|-1 + (-2)| = 3 > 2 = (3 * 1 + 2) / 2`.
- **Actionable fix:**
  1. In `chi12_sq_sub_sq`, strengthen `h3` to exclusive divisibility by 3 (e.g. add `(h3' : ¬ (u.val % 3 = 0 ∧ v.val % 3 = 0))` or use `Xor`).
  2. In `abs_sum_alt_pent_gaps_le`, sum over `Finset.Icc 1 K` (or `k ∈ Finset.range K` with `k + 1` in place of `k`); then for $K = 2m + 1$ the LHS is $3m + 2 = (3K+2)/2$ (true even under integer division in `ℤ`).

---

### Minor Findings

#### Minor 1 (A3.1, §1 & Script): Precision polishes in Theorem 1, Corollary 1.2, and `section_a31`
- **Files / lines:** `notes/phase22/flagship-digit-laws.md`, lines 80–81, 87, 107; `scripts/phase22_flagship_digits.py`, line 255.
- **Issues:**
  1. **Theorem 1(1) (lines 80 & 87):** State $\kappa > 0$ and $\beta \ge 0$ explicitly. Also note that on line 87, $A^*(N, R) \ll N(\log N)^\beta$ does **not** follow from $a(m) \ll m^C$ on $m > N + R$ when $C > 1$ (which only gives $O(N^C)$); rather, since $a(m) \ge 0$ and $A(X) \ll X(\log X)^\beta$, summation by parts gives $\sum_{k \ge 1} a(N+R+k) b^{-k} \le (1 - b^{-1})\sum_{k \ge 1} A(N+R+k) b^{-k} \ll (N+R)(\log(N+R))^\beta$ directly, making the hypothesis $a(m) \ll m^C$ unnecessary.
  2. **Theorem 1(2) (line 81):** State $\gamma \ge 0$ explicitly, and fix the self-referential definition $R = L + \lceil \log_b(2 C_{b,\gamma}(N+R)^\gamma)\rceil + 1$ (where $R$ appears on both sides for $\gamma > 0$) by stating *"for any integer $R \ge L + \lceil \log_b(2 C_{b,\gamma}(N+R)^\gamma)\rceil + 1$"* (or giving an explicit closed choice such as $N+R \le 2N$ for $N \ge R$).
  3. **Script line 255:** `Nc + 64` hardcodes an upper bound on $R$; this is valid on the script's parameter grid (maximum $R = 39 \le 64$), and adding `check(R <= 64, ...)` makes the check self-certifying.
  4. **Corollary 1.2 (line 107):** For $\Theta_3(1/b)$ ($\gamma = 0$), Theorem 1(2) actually gives $R \le L + 2$ for every $b \ge 2$ (since $2C_{b,0} = \frac{2}{b-1} \le 2$); $L + 3$ is valid and conservative.
- **Actionable fix:** Incorporate these brief clarifications in lines 80–81, 87 and add `check(R <= 64, "R bound")` in script line 255.

#### Minor 2 (A3.2, §2 & Script): Minor notation and edge-case polishes in §2
- **Files / lines:** `notes/phase22/flagship-digit-laws.md`, lines 121, 164, 166, 182–184, 195; `scripts/phase22_flagship_digits.py`, lines 338–339.
- **Issues:**
  1. Line 121 writes *"for $j \ge 1$"*, while Lemma 2.1, Proposition 2.2, and Theorem 2 also include $j = 0$ (add one phrase noting that for $j = 0$ the $m = 0$ constant term $1$ does not affect $\tau_n$ for $n \ge 0$).
  2. Line 164 says *"the digits $1, \dots, b-2$ have frequency $O((L+\log N)/\sqrt N)$"* — since digits correspond to $L = 1$, drop $L$ or refer to nonconstant length-$L$ words.
  3. Line 166 writes $\sum_{m_i \le N+\ell}\ell_i + m_{i_0}$ with undefined $\ell$; cleaner to sum $\ell_i$ over all $i$ with $m_{i-1} < N$ (which includes at most one support point $m_{i^*} > N$, with $m_{i^*} = N + O(\sqrt N)$) and note that Theorem 2 holds trivially for $L \ge \sqrt N$ since the LHS is $\le 2$.
  4. In Theorem 2.4 (lines 182–184), add a one-line note that $m - \ell + 1 \ge m_{i-1} + 1 \ge 1$ (so the planted window stays in the fractional digits), that $v_K$ is strictly increasing in even $K$, and that for $v_k = c_k - 1$ even the edge case $c_k = b^{\ell-1}$ only prepends a single leading $0$ to the standard expansion of $v_k$, which still contains $1w$.
  5. Script lines 338–339 add `+ 1` slack (`abs(cnt0 - N / 2) <= exc + imb / 2 + 1`), whereas the exact triangle inequality quoted on line 195 holds without `+ 1`.
- **Actionable fix:** Tighten lines 121, 164, 166, 182–184 accordingly.

#### Minor 3 (A3.3, §3 & §7): Pair count `27` $\to$ `30` and small precision polishes in §3
- **File / lines:** `notes/phase22/flagship-digit-laws.md`, lines 235, 242, 262, 293, 511.
- **Issues:**
  1. **Pair count (lines 235 and 511):** There are **30** pairs $(M, r)$ with $3 \le M \le 12$ and $1 \le r < M/2$ ($1+1+2+2+3+3+4+4+5+5 = 30$), and the script checks and prints all 30 — not 27.
  2. **Line 242:** The fourth classification bullet (*"all the others. For example $a_{1,5}=\operatorname{Re}(1*\chi)$ and $a_{2,5}=\operatorname{Im}(1*\chi)$"*) includes $a_{1,5}$, which was already placed in the second bullet ($r'=1, \lambda(M')>2$).
  3. **Line 262:** *"and the nonzero value is $\ge\frac12$"* should read *"and $|a_{3,8}| \ge \frac12$"* (in fact $\ge 1$, since $a_{3,8} \in \mathbb Z$).
  4. **Line 293:** For general odd $M$-periodic integer weights $w$, exclude the degenerate case $w \equiv 0$, note that Theorem 3.5(1)–(2) (rather than item 3) hold verbatim, and clarify that Proposition 3.1's character expansion applies on each gcd stratum $g \mid M$ modulo $M/g$.
- **Actionable fix:** Change `27` to `30` on lines 235 and 511, and apply the three small wording fixes on lines 242, 262, and 293.

#### Minor 4 (A3.4, §4): Update Lemma S status to Track D3–D4 and clarify three small details in Theorems 4.3–4.4
- **File / lines:** `notes/phase22/flagship-digit-laws.md`, lines 25, 328, 335, 341, 349.
- **Issues:**
  1. **Lemma S status (lines 25 and 335):** Both lines still refer to Lemma S as *"sketched there"* (citing Phase 21 §4.2). Phase 22 Track D3–D4 ([`notes/phase22/partitions-carry-and-lemma-s.md`](../partitions-carry-and-lemma-s.md), §1, Theorem S) has now completed the full Selberg-sieve proof of Lemma S unconditionally (granting Phase 20 Theorem 6(a)). Updating lines 25 and 335 removes an obsolete caveat.
  2. **Line 328 (Theorem 4.3):** Write $m \in \operatorname{supp} a_2 \cap [1, \infty)$ (excluding $m = 0$, where $G_-(0)$ is undefined) and note that the strict inequality `> 0` coincides with Lemma 0.3's `>= 0` because $E_2^2 \notin \mathbb Q$ (so no tail sum vanishes).
  3. **Line 341 (Theorem 4.4):** $\sum_p (g(p) - \epsilon_p)/p$ uses $\epsilon_p$ outside $p \equiv 1 \pmod{12}$; write $\sum_p (g(p) - f(p))/p$ with $f(m) = \operatorname{sgn} c(m)$, and cite Wirsing (1967, Satz 1.1) specifically for real multiplicative $|f| \le g$ with $\sum_{p \le x} g(p)\log p \sim \tau x$ ($\tau > 0$).
  4. **Line 349 (Theorem 4.4):** Briefly justify the $O(Nb^{-H})$ bound for isolated $m$ with $|\tau_m| \ge 1$ via Markov's inequality on $\sum_{m' \le 5N} |V(m')| \ll N$ (using $m' \le 5N$ from primes $(p^2-1)/12$ and injectivity of $m \mapsto m'$ on isolated points), or directly via $\sum_{m \le N}\sum_{k>H}|a_2(m+k)|b^{-k} \ll Nb^{-H}$.
- **Actionable fix:** Update lines 25 and 335 to cite Track D3–D4 Theorem S, and add the three one-line clarifications to lines 328, 341, and 349.

#### Minor 5 (A4, §5 & §7): Scope/counting precision in Summary, Theorem 5.3, worked table, and §7
- **File / lines:** `notes/phase22/flagship-digit-laws.md`, lines 30, 407, 439–440, 444, 448, 513.
- **Issues:**
  1. **Line 30 (Summary):** *"no simply normal law for $b\in\{3,4,5,6,7,10\}$, $d\le 40$"* should specify *"for $\frac{a}{d}E_b$"* (matching line 446 and script lines 1004–1017; $E_b^3$ was not included in that $b \ge 3$ search).
  2. **Line 407 (Theorem 5.3):** *"for every numerator $a$"* should read *"for every nonzero numerator $a$"* (for $a = 0$ the number is $0$; for nonzero $a$ with $\gcd(a, d) > 1$, reduction to $d' = d/\gcd(a, d)$ preserves odd order or falls back to Theorem 2 when $d' = 1$).
  3. **Lines 439–440 (worked table):** The $w_0^+, w_0^-$ cells for $\frac14 E_3$ ($\frac16, 0$) and $\frac13 E_{10}$ ($\frac16, \frac16$) are left blank.
  4. **Line 444:** *"In that range this means $d\in\{7,23,31,47,49\}$"* is the list for $E_2$ ($d < 64$); for $E_2^3$ ($d < 46$) it is $\{7, 23, 31\}$.
  5. **Line 448:** For $\frac13 E_2$, the $L = 3$ deviation is `0.00712` (rounds to `0.0071`, not `0.0072`); and `"0.002–0.035 in the other cases"` describes the $L = 3$ maxima (`0.00211` to `0.03544`), whereas at $L = 1$ deviations go down to `0.00004` ($\frac37 E_2$).
  6. **Line 513 (§7):** *"Exact limit laws for 26 pairs $(b,d)$ and both series"* should read *"13 pairs $(b,d)$, both signs $a = \pm 1$, and both series (52 laws)"* (script lines 854–860).
- **Actionable fix:** Apply these brief precision edits across lines 30, 407, 439–440, 444, 448, and 513.

---

## Post-Repair Verification

Re-audited [`notes/phase22/flagship-digit-laws.md`](../flagship-digit-laws.md) (lines 1–536) and [`scripts/phase22_flagship_digits.py`](../../../scripts/phase22_flagship_digits.py) (lines 1–1081) in full after the author's revisions.

**Updated Verdicts**
- **Track A3 (A3.1–A3.4 — flagship digit laws):** **ACCEPT** — All 5 Major findings affecting A3 and §6 and all 4 Minor findings are resolved rigorously; zero Critical or Major issues remain.
- **Track A4 (§5 — rational-scaling signed automata):** **ACCEPT** — Major 5 and Minor 5 are resolved cleanly and verified by exact script assertions; zero Critical or Major issues remain.

> **Review scope caveat:** This post-repair check is an automated cross-model audit, **not** independent human peer review.

### 1. Re-execution of the Verification Script
- **Command:** `python -B scripts/phase22_flagship_digits.py`
- **Result:** Exit code `0`; **`5,817,206` checks passed** in **`16.6 s`** (`16.7 s` wall-clock), matching §7 line 519 verbatim.
- **New assertions verified in script:**
  - `check(R <= 64, ...)` in `section_a31` (line 256).
  - Exact triangle inequality `abs(cnt0 - N / 2) <= exc + imb / 2` (and `cntb`) without `+ 1` slack in `mechanism` (lines 339–340).
  - `check(len(table) == 13 and nlaws == 52, "law count")` (line 878).
  - Exact zero-atom splits `(w_0^+, w_0^-)` and `a -> -a` swap check for all 10 worked/cited examples including $\frac{1}{13}E_2$ (`1/36, 1/18`) and $\frac{1}{35}E_2^3$ (`1/140, 1/70`), plus $L = 2$ exact laws for $\frac17 E_2$, $\frac17 E_2^3$, and $\frac{1}{23}E_2$ (lines 880–902).
  - `check(wp != wm, ...)` across all 45 even-order denominators in the base-2 catalogue and explicit verification of the two simply normal denominator lists `E_2: [7, 23, 31, 47, 49]` and `E_2^3: [7, 23, 31]` (lines 1019–1042).
- **Scope hygiene:** Re-grepped both files for process language (`brief`, `prompt`, `agent`, `todo`, `fixme`, `reviewer`, `referee`, model names): **zero matches**.

### 2. Finding-by-Finding Closure Audit

| Finding | Status | Verification Notes |
|---|---|---|
| **Major 1** (Lemma 2.1, lines 146–154) | **Closed** | Replaced $C_{b,j}$ with $(1 + C_{b,j})$ on line 149 and explained the $\Delta = K$ ($r = 0$) summand on line 154. |
| **Major 2** ($j = 0$ remark, line 182) | **Closed** | Restricted bounded coefficients and $O(L/\sqrt N)$ to $E_b$ ($j=0$); accurately stated that $E_b^3$ ($j=0$) has coefficients $2k+1 \asymp \sqrt{T_k}$ and rate $O((L+\log N)/\sqrt N)$ (Phase 20, Theorem 7(b)). |
| **Major 3** (Lemma 0.4 & Thms 3.5, 4.3, lines 70–80, 264, 305, 345) | **Closed** | **Lemma 0.4** is completely sound: the sum exchange gives $\sum_{n<N} T_n \le b^{-R} A^*_{|a|}(N,R)/(b-1)$, Markov bounds $B_L(N)$ directly, and summation by parts ($\sum_{k\ge 1}|a(M+k)|b^{-k} \le (1-b^{-1})\sum_{k\ge 1} A(M+k)b^{-k} \ll M\log^\beta M$) holds cleanly without individual coefficient growth assumptions. Line 80 explicitly illustrates why $\|b^n z\|$-concentration alone fails ($a(m)=-(b-1)$). Theorems 3.5 (line 264), general odd periodic weights (line 305), and Theorem 4.3 (line 345) now apply Lemma 0.4 directly. |
| **Major 4** (Prop. 4.2, line 333) | **Closed** | The revised proof sets $Q' = \operatorname{lcm}(12, Q)$, notes $H \supseteq \mathbb Q(i, \sqrt 3)$ forces splitting primes to be $\equiv 1 \pmod{12}$, uses the infinitude of $\operatorname{Spl}(H\,\mathbb Q(\zeta_{Q'}))$ to force $1 \in S$, deduces $\operatorname{Spl}(\mathbb Q(\zeta_{Q'})) \subseteq \operatorname{Spl}(H)$ up to finitely many primes, and applies Bauer's theorem (Neukirch, VII.13.9–13.10) to obtain $H \subseteq \mathbb Q(\zeta_{Q'})$, contradicting nonabelianity of $\operatorname{Gal}(H/\mathbb Q) \cong D_4$. Completely rigorous. |
| **Major 5** (Catalogue remark, line 456) | **Closed** | Dropped the false `-1 \notin \langle 2 \rangle` claim; accurately states $w_0^+ \ne w_0^-$ across all 45 even-order cases, cites verified examples $(\frac16, 0)$ for $\frac13E_2$, $(\frac1{36}, \frac1{18})$ for $\frac1{13}E_2$, and $(\frac1{140}, \frac1{70})$ for $\frac1{35}E_2^3$, and notes that $a \mapsto -a$ swaps $w_0^+$ and $w_0^-$. |
| **Major 6** (§6 Lean targets, lines 501–509) | **Closed** | `chi12_sq_sub_sq` now uses `Xor' (u.val % 3 = 0) (v.val % 3 = 0)` and `abs_sum_alt_pent_gaps_le` sums over `Finset.Icc 1 K`. Both independently verified with zero counterexamples (exhaustively on `ZMod 12 × ZMod 12` and for all $0 \le K < 200$, plus general parity proof). |
| **Minor 1** (Thm 1, Cor. 1.2, script line 256) | **Closed** | Added $\kappa > 0, \beta \ge 0$, removed redundant $a(m) \ll m^C$, fixed self-referential $R$ in Thm 1(2) (line 93), tightened Cor. 1.2 $\Theta_3$ bound to $L+2$ (line 119), and added `check(R <= 64, ...)`. |
| **Minor 2** (§2 & script lines 339–340) | **Closed** | Clarified $j=0$ (line 133), removed stray $L$ for digits (line 176), replaced undefined $\ell$ and noted $L \ge \sqrt N$ trivial (line 178), added all three Theorem 2.4 boundary clarifications (line 194), and removed `+ 1` slack in script lines 339–340. |
| **Minor 3** (§3 & §7) | **Closed** | Fixed `27` $\to$ `30` pairs (lines 247, 523), resolved $a_{1,5}$ classification overlap (line 254), fixed $|a_{3,8}| \ge \frac12$ (line 274), and tightened general odd periodic weights (line 305). |
| **Minor 4** (§4) | **Closed** | Updated Theorem 4.4 (lines 25, 347, 361) to cite the completed Theorem S of [`partitions-carry-and-lemma-s.md`](../partitions-carry-and-lemma-s.md) (§1); added $m \ge 1$ and irrationality justification for `> 0` (lines 340, 343); fixed $g(p)-f(p)$ and Wirsing (1967) citation (line 353); gave the clean direct Markov bound $\sum_{m\le N}\sum_{k>H}|a_2(m+k)|b^{-k} \ll Nb^{-H}$ for isolated carry flips (line 361). |
| **Minor 5** (§5 & §7) | **Closed** | Qualified `no simply normal law (a/d)E_b` (line 30) and `nonzero numerator a coprime to d` (line 419); filled in $w_0^\pm$ for $\frac14E_3$ and $\frac13E_{10}$ (lines 451–452); separated $E_2$ and $E_2^3$ denominator lists (line 456); fixed `0.0071` and range `0.00004` to `0.035` (line 460); fixed `13 pairs (b,d), both signs a = ±1 and both series (52 laws)` (line 525). |

*(Trivial non-blocking note: line 46 still reads `"Lemmas 0.1–0.3"` rather than `"Lemmas 0.1–0.4"` after adding Lemma 0.4; no mathematical impact.)*
