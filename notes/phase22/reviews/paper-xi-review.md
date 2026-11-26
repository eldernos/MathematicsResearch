# Independent Cross-Provider Referee Review: Paper XI Candidate Draft

- **Manuscript audited:** *Digit Distribution of Arithmetic Generating Functions: Euler Products, Theta Values and Sparse Coefficient Transfer* (v1.0 candidate draft, 26 November 2026)
- **Audited files (read in full):**
  - `papers/11-generating-functions-digits/paper.tex` (2,551 lines)
  - `papers/11-generating-functions-digits/references.bib` (389 lines; 38 entries)
  - `papers/11-generating-functions-digits/VERIFICATION.md` (196 lines; 99 statement rows)
  - `papers/11-generating-functions-digits/LEDGER.md` (113 lines)
- **Pinned Lean commit cross-checked:** `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8` (all 54 cited Lean declarations and line numbers checked directly via `git show`)
- **Reviewer / Author:** Gemini 4 Neon (auditing Claude Opus 5.5)
- **Date:** 26 November 2026
- **Verdict:** **`REVISE`** (0 Critical, 7 Major, 8 Minor)

> **Peer-review disclaimer:** This document is an automated cross-provider AI manuscript audit. **Cross-model review is not independent human peer review.** No human specialist has refereed the written proofs, analytic number theory inputs, or priority comparisons.

---

## Executive Summary

The Paper XI candidate draft is an unusually disciplined, coherent, and mathematically substantive synthesis. Across 99 numbered statements (Theorems A–G and §§2–9), the core theorems are **mathematically sound** and the hardest technical arguments—the finite all-prefix transfer, the $2$-adic run barrier and sharp packing theorem (§5.2), the self-contained Selberg uniform pair sieve (§8), the signed rational-scaling automaton and odd-order complement symmetry (§7.5), and the completeness and entropy–multiplicity wall (§9.2–9.3)—withstood line-by-line checking and independent numerical/algebraic recomputation.

Equally strong are the manuscript's epistemic and repository hygiene:
- **Series vs. products honesty:** The distinction between Lean's coefficient-defined series (`eulerPentagonalSum`, `eulerCubeSum`) and the classical product identities of Euler and Jacobi (external input, not formalized), as well as the total absence of Lean formalization for $E_b^2$, is stated accurately and consistently across `paper.tex` (§1.1, §4.1, §11), `VERIFICATION.md`, and `LEDGER.md`.
- **Zero internal process language in `paper.tex`:** Automated and manual scans found zero occurrences of `"the brief"`, `"Phase 20/21/22"`, `"Track A/B/C/D/G"`, registry IDs (`GF-*`, `CC-*`, `SY-*`), or internal labels (`Lemma S`, `Theorem S`) in mathematical prose. The only `Phase18` string in `paper.tex` is the literal Lean module filename `Phase18Synthetic`.
- **Bibliographic and reference integrity:** All 38 entries in `references.bib` are cited in `paper.tex`, with zero missing keys and zero uncited entries. All `\cref`/`\ref`/`\eqref` targets resolve. All 54 `\leanP{File}{line}{decl}` references point to the exact declaration line at commit `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8`.
- **Archived release integrity:** `git status --short -- papers/` confirms no archived release file was modified; only the new untracked directories `papers/11-generating-functions-digits/` and `papers/07-synthetic-expansions-v2/` are present in `papers/`.
- **Honest priority handling in `LEDGER.md`:** Clearly discloses that no new literature search was performed, that MathSciNet/zbMATH/Google Scholar were not searched, that a failed search is not proof of novelty, and that the `CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality` comparison remains open.

Nevertheless, the audit identified **7 Major** and **8 Minor** defects that require targeted revision before acceptance:
- Two external-input theorem statements (Theorem 7.11 / Wirsing 1967, and Theorem 5.1(c) / Brun's sieve) omit load-bearing hypotheses and admit literal counterexamples as written.
- Theorem 3.12 (`thm:displacedwidth`) states too weak a regularity hypothesis ($\Lambda_N = o(N)$ instead of $o(P(N)\log_b(1/\pi_N))$) and leaves $L$ unquantified.
- Theorem F(ii) claims the full scope of Theorem A(iii), whereas Theorem 7.6 (`thm:nonneg`) only proves two narrower regimes.
- Theorem 6.9 cites the specialized $q$-digamma Lean declaration (`AntisymmetricLambert:525`) instead of the general bounded-convolution declaration (`AntisymmetricLambert:510`), and the §11 verification table miscounts `RadixWidthLaw` declarations (6 vs. 7) and omits 2 theorems and 3 declarations.
- Theorem 7.10 (`thm:squaredigits`) invokes Proposition 6.5 for the irrationality of $E_b^2$ without acknowledging that this depends on Nesterenko's transcendence theorem (an external input missing from `VERIFICATION.md:125`).
- The condensed proof of Theorem 5.14 (`thm:classgroups`) asserts an inaccurate `\log_2 a_C(n) = \omega_{\rm split}(n) + O(1)` for almost all $n$ and omits three load-bearing steps ($a_C \sim a/h_0$, the $G^2$-coordinate split, and the general-$G$ Rankin exceptional-set bound).

Every finding is local and straightforward to repair; none invalidates the main theorems. A targeted revision and quick post-repair re-check are recommended (**`REVISE`**).

---

## Audit Protocol Summary

| Check | Outcome | Details |
| --- | --- | --- |
| Theorems A–G vs. §§2–9 correspondence | **Findings** | Major-4 (Thm F(ii) vs. Thm 7.6); Minor-6 (Thm F(v)); Minor-7 (Thm C(iii), G(ii) conditional scope). |
| Euler/Jacobi product vs. series & $E_b^2$ formalization | **Pass** | Completely honest; zero overclaims on `eulerPentagonalSum`, `eulerCubeSum`, or $E_b^2$. |
| Mathematical proofs across §§2–9 | **Findings** | Major-1, Major-2, Major-3, Major-6, Major-7; Minor-3, Minor-4, Minor-5, Minor-6, Minor-7. |
| Lean declarations & evidence labels | **Findings** | All 54 line links exact at `347ec3fe`; Major-5 (Thm 6.9 wrong decl, §11 table omissions, `VERIFICATION.md:54`); Minor-2 (`Kernel-verified` scope in Lem 2.6, Lem 3.10, Thm 3.5, Prop 4.2). |
| Internal process language in `paper.tex` | **Pass** | Zero leaks in mathematical prose (`Phase18Synthetic` is only a Lean module name). |
| `VERIFICATION.md` completeness & formatting | **Findings** | All 99 statements matched 1-to-1 in numbering and label; Major-5, Major-6; Minor-1 (6 Markdown table rows broken by unescaped `\|`). |
| `LEDGER.md` priority honesty | **Pass (Minor)** | Thorough and candid; Minor-8 (`DNNS1996`, `Bertrand1997` missing from L113 unverified list). |
| Citations vs. `references.bib` | **Pass** | 38/38 exact match; 0 missing, 0 uncited, 0 broken `\cref`/`\ref`. |
| Archived release integrity | **Pass** | Zero modifications to any archived release file in `papers/`. |

---

## Critical Findings

None.

---

## Major Findings

### Major-1: Missing prime-power hypothesis in Theorem 7.11 (Wirsing 1967) — literal statement is false
- **Location:** `paper.tex:2048–2052` (`thm:wirsing67`).
- **Issue:** Theorem 7.11 states:
  > If $f$ is real multiplicative, $|f| \le g$ with $g \ge 0$ multiplicative, $\sum_{p\le x} g(p)\log p \sim \tau x$ with $\tau > 0$, and $\sum_p (g(p)-f(p))/p = \infty$, then $\sum_{n\le x} f(n) = o(\sum_{n\le x} g(n))$.

  With no growth hypothesis on $g$ at prime powers (or boundedness of $g$), this statement is **false**. Counterexample: define multiplicative $f, g$ by $g(2^k) = f(2^k) = 4^k$ ($k \ge 1$) and $g(p) = 1$, $f(p) = -1$, $g(p^k) = f(p^k) = 0$ ($k \ge 2$) for every odd prime $p$. All stated hypotheses hold ($\tau = 1 > 0$ and $\sum_p (g(p)-f(p))/p = \sum_{p\ge 3} 2/p = \infty$). Yet at $x = 2^K$, the $j = K$ and $j = K-1$ terms give $\frac{5}{4} 4^K$ while all $j \le K-3$ terms contribute at most $\sum_{j=0}^{K-3} 4^j 2^{K-j} < \frac{1}{4} 4^K$, so $\sum_{n\le 2^K} f(n) \ge 4^K \ge \frac{1}{2}\sum_{n\le 2^K} g(n)$, contradicting $o(\sum_{n\le x} g(n))$. (Theorem 7.12 applies Theorem 7.11 to $g = \mathbf{1}_{\mathcal S}$, which satisfies $0 \le g \le 1$, so the downstream proof is unaffected.)
- **Actionable fix:** Add Wirsing's standard prime and prime-power hypotheses—e.g. $g(p) \le C$ and $g(p^\nu) \le A B^\nu$ with $B < 2$ (or simply state Theorem 7.11 for $0 \le g(n) \le 1$, which is Wirsing 1967 Satz 1.1/1.2 and suffices for Theorem 7.12).

### Major-2: Missing $z$-range and $\omega(p)$-boundedness hypotheses in Theorem 5.1(c) (Brun's sieve)
- **Location:** `paper.tex:1225–1228` (`thm:meanvalues`(c)), and invocations at `paper.tex:1312–1314` (`lem:pairs`) and `paper.tex:1456–1458` (`thm:squareradix`).
- **Issue:** Theorem 5.1(c) claims that sifting $X$ integers by $\omega(p)$ classes modulo primes in a set of Dirichlet density $\kappa_0$ in $(z_0, z]$ with $|R_d| \le \omega(d)$ leaves $\ll X \prod_{z_0 < p \le z} (1 - \omega(p)/p)$ elements, with no upper bound on $z$ in terms of $X$ and no bound on $\omega(p)$ (such as $0 \le \omega(p) < p$, $\omega(p) \le A$). For fixed $X$ and any nonempty sifted set, letting $z \to \infty$ sends the RHS to $0$, making the statement literally false. Moreover, in Halberstam–Richert Theorem 2.2, the implied constant depends on the dimension $\kappa_0$ and the ratio $\log X / \log z$ (so $z \le X$ or $z \le X^c$ is required; in Lemma 5.5 and Theorem 5.10, sifting up to $z = x^{1/4}$ or $z = x^{1/2}$ gives the same $\ll x(\log z_0 / \log x)^{\dots}$ bound).
- **Actionable fix:** Add the conditions $z_0 < z \le X^{1/2}$ (or $z \le X$) and $0 \le \omega(p) < p$, $\omega(p) \le A$ to Theorem 5.1(c), and note that the implied constant depends on $\kappa_0$ and $A$.

### Major-3: Theorem 3.12 (`thm:displacedwidth`) states too weak a regularity condition ($\Lambda_N = o(N)$) and leaves $L$ unquantified
- **Location:** `paper.tex:648–651` and `paper.tex:660–664`.
- **Issue:** The asymptotic half of Theorem 3.12 assumes:
  > If $\sum_{1\le t(m)\le X}|U(m)|\le K_0 P(X)$ and the regularity conditions $\Lambda_N=o(N)$, $\widehat P(N+L)\le P(N)\pi_N^{-o(1)}$ hold, where $\pi_N=P(N)/N\to0$, then $1-D_N(F;b)\le(1+o(1))\pi_N\log_b(1/\pi_N)$.

  Three problems occur here:
  1. Dividing the finite inequality of Theorem 3.12 by $N$ gives the term $\Lambda_N / N$. Assuming only $\Lambda_N = o(N)$ yields $\Lambda_N / N = o(1)$, **not** $o(\pi_N \log_b(1/\pi_N))$; the proof needs $\Lambda_N = o(P(N)\log_b(1/\pi_N))$. (Interestingly, $\Lambda_N = o(P(N)\log_b(1/\pi_N))$ actually *follows* from $\sum_{1\le t(m)\le X} |U(m)| \le K_0 P(X)$ and $\widehat P(N+L) \le P(N)\pi_N^{-o(1)}$ when $P(N) \ge 1$, because every source with $t(m) \le t$ contributes $\ge b^{-1}\min(1, b^{N+L-t+1})$ to $\widehat P(N+L)$, forcing $u(m) - t + N \le \log_b(K_0 b \widehat P(N+L)) = \log_b P(N) + o(\log_b(1/\pi_N)) + O(1) = o(P(N)\log_b(1/\pi_N))$; however, the proof never makes this argument and instead states the insufficient condition $\Lambda_N = o(N)$.)
  2. The parameter $L$ inside the hypothesis $\widehat P(N+L) \le P(N)\pi_N^{-o(1)}$ is unquantified in the theorem statement.
  3. The term $L(1 + P(N))/N = L\pi_N + L/N$ equals $(1+o(1)) L\pi_N$ only when $P(N) \to \infty$ (if $P(N) = 0$ then $\log_b(1/\pi_N)$ is undefined; if $P(N)$ is bounded and positive then $F \in \Z[1/b]$ and $1 - D_N = O(1/N)$ trivially, which is not mentioned).
- **Actionable fix:** Assume $P(N) \to \infty$ (so $\pi_N > 0$ eventually), quantify $L$ explicitly (e.g., "for $L = \lceil(1+\eta_N)\log_b(1/\pi_N)\rceil$ with some $\eta_N \to 0$"), and replace $\Lambda_N = o(N)$ by $\Lambda_N = o(P(N)\log_b(1/\pi_N))$ (or drop $\Lambda_N$ from the hypotheses and prove $\Lambda_N = o(P(N)\log_b(1/\pi_N))$ in 3 lines from the other two conditions).

### Major-4: Theorem-to-proof scope gap between Theorem F(ii) and Theorem 7.6 (`thm:nonneg`)
- **Location:** `paper.tex:252–254` (`thm:F`(ii)) vs. `paper.tex:1941–1959` (`thm:nonneg`).
- **Issue:** Theorem F(ii) asserts: *"Every nonnegative integer series covered by Theorem A(iii) has $f_{0^L}(N)\to 1$,"* and line 1959 asserts *"This proves Theorem F(ii)."* However, Theorem 7.6 (`thm:nonneg`) only states and proves the result under two narrower hypotheses: (1) $S(X) \ll X(\log X)^{-\kappa}$ and $A(X) \ll X(\log X)^\beta$ ($\kappa > 0$, $\beta \ge 0$), and (2) support in the squares with $a(m) \le 2m^\gamma$. The three general qualitative regimes of Theorem A(iii)—especially $A(X)=O(X), S(X)=o(X)$ without logarithmic power saving, general polynomial mass $A(X) \le C(X+1)^k$ with $S(X)\log X = o(X)$, and general logarithmic mass $A(X) \le CX(\log(X+2))^\gamma$ with $S(X)\log\log X = o(X)$—are never proved in §7.2.
- **Actionable fix:** Add a first clause to Theorem 7.6 proving $f_{0^L}(N) \to 1$ under all three cases of Theorem A(iii). The proof is 3 lines from Lemma 7.5(b),(d) using $\rho_+(N) = 1$ (since $a \ge 0 \implies \tau_n \ge 0$) and taking $R \to \infty$ slowly with $R S(N+R) = o(N)$ in the linear case, $R = L + \lceil k\log_b N + \omega_N \rceil$ in the polynomial case, and $R = L + \lceil \gamma\log_b\log N + \omega_N \rceil$ in the logarithmic case (with $\omega_N \to \infty$ slowly), plus the trivial finite-support case.

### Major-5: Mis-cited Lean declaration in Theorem 6.9 and incomplete §11 / `VERIFICATION.md` Lean correspondence
- **Location:** `paper.tex:1770`, `paper.tex:2505–2527`, `VERIFICATION.md:54, 113–114`.
- **Issue:**
  1. In the proof of Theorem 6.9 (`thm:oddweights`, for general odd $M$-periodic integer weights $w$), `paper.tex:1770` cites `\leanP{AntisymmetricLambert}{525}{qDigamma_reflection_tendsto_one_of_sparse}` as "the reduction of membership to sparsity." At commit `347ec3fe`, line 525 of `AntisymmetricLambert.lean` is specialized to the $q$-digamma anti-indicator `antiIndicator M r` (Theorem 6.10). The actual general Lean declaration for bounded Dirichlet convolutions `dirichletOneConv f` is `AntisymmetricLambert.lean:510`, `bounded_dirichletOneConv_tendsto_one_of_sparse`, which is never cited! `VERIFICATION.md:113` repeats the same misplacement.
  2. In §11 (`paper.tex:2518`), the table reads `\texttt{RadixWidthLaw}: six declarations & \cref{lem:onesource,thm:widthlaw,lem:firstmoment}`. In fact, `paper.tex` cites **seven** declarations from `RadixWidthLaw` (`width_law_upper` at L663 in Thm 3.12; `dist0_div_pow_ge`, `dist0_div_pow_eq`, `card_far_in_gap_ge` at L693–696 in Lem 3.14; `card_large_tail_le` at L744 in Thm 3.15; `sum_log_eq_sum_primePow` at L1259 in Lem 5.2; and `padicVal_succ_pos_imp` at L1300 in Lem 5.4), and omits `\cref{thm:displacedwidth,lem:valuations}`.
  3. The §11 table also omits three other declarations cited in the text: `Phase18Synthetic.discrepancy_add_int` (L447, Lem 2.6), `CoefficientTransfer.not_dvd_radixUnit` (L622, Lem 3.10), and `NormalReciprocalCore.eulerAutomatonStep_bijective` (L2113, Thm 7.14).
  4. In `VERIFICATION.md:54` (row `Thm F`), column 3 notes `(Lean part: Proposition 7.7, Theorem 7.14)`, but column 4 lists only `as Proposition 7.7`, omitting Theorem 7.14.
- **Actionable fix:**
  - Replace `qDigamma_reflection_tendsto_one_of_sparse` at `paper.tex:1770` and `VERIFICATION.md:113` with `\leanP{AntisymmetricLambert}{510}{bounded_dirichletOneConv_tendsto_one_of_sparse}`, and cite `\leanP{AntisymmetricLambert}{525}{qDigamma_reflection_tendsto_one_of_sparse}` in Theorem 6.10 (`paper.tex:1797` and `VERIFICATION.md:114`).
  - Update `paper.tex:2511–2524` so `RadixWidthLaw` lists seven declarations and `\cref{thm:displacedwidth,lem:onesource,thm:widthlaw,lem:firstmoment,lem:valuations}`, `AntisymmetricLambert` lists four declarations (including both L510 and L525 for Thms 6.9–6.10), and `discrepancy_add_int`, `not_dvd_radixUnit`, and `eulerAutomatonStep_bijective` are included.
  - Update `VERIFICATION.md:54` column 4 to `as Proposition 7.7, Theorem 7.14`.

### Major-6: Undisclosed external input (Nesterenko's transcendence theorem) in Theorem 7.10 (`thm:squaredigits`)
- **Location:** `paper.tex:2037–2038, 2045` and `VERIFICATION.md:125`.
- **Issue:** Theorem 7.10 defines $\rho_+(N)$ as the gap-weighted proportion of support points with *strictly positive* oriented value $\sum_{m'\ge m} a_2(m') b^{m-m'} > 0$, and its proof (L2045) justifies excluding zero by: *"No oriented value vanishes because $E_b^2$ is irrational (\cref{prop:arith})."* However, the elementary irrationality criterion in Proposition 6.5 requires $a \ge 0$, which fails for $E_b^2$ (half of whose coefficients are negative). Irrationality of $E_b^2$ only follows from the transcendence of $E_b$ quoted in Proposition 6.5 via **Nesterenko's theorem** (an external input). Yet `VERIFICATION.md:125` lists only `Landau (via Prop 4.8)` under External inputs for Theorem 7.10, omitting Nesterenko (1996).
- **Actionable fix:** Either (cleanest, avoiding Nesterenko completely) state Theorem 7.10 with $\sum_{m'\ge m} a_2(m') b^{m-m'} \ge 0$ matching Lemma 7.5(c) directly, and add a remark that by Nesterenko's theorem $E_b^2$ is transcendental so $= 0$ never occurs; **or** keep `> 0`, rewrite L2045 to explicitly cite the transcendence of $E_b$ (Nesterenko, via Proposition 6.5), and add `Nesterenko 1996 (via Prop 6.5)` to `VERIFICATION.md:125`.

### Major-7: Inaccurate $O(1)$ claim and missing load-bearing steps in the condensed proof of Theorem 5.14 (`thm:classgroups`)
- **Location:** `paper.tex:1559–1593`.
- **Issue:** The manuscript condenses the proof from `notes/phase22/radix-thresholds-and-class-groups.md`, introducing three gaps in `paper.tex`:
  1. Line 1583 asserts: *"Since $\log_2 a_C(n) = \omega_{\rm split}(n) + O(1)$ for almost all $n$."* First, $\log_2 a(n) - \omega_{\rm split}(n) = \sum_{p^e\|n,\,e\ge 2}(\log_2(e+1)-1)$ is **tight** ($O_P(1)$), not uniformly $O(1)$ on a density-1 set (for every fixed $M$, a positive proportion of supported $n$ exceed $M$). Second, the step showing $a_C(n) = (1 + o(1)) a(n)/h_0$ in probability on the genus (using $|\psi(Y_n)|/a(n) \le \prod_{p\|n,\,\psi(\mathfrak p)\ne 1} |\cos(\arg\psi(\mathfrak p))| \to 0$ for nontrivial $\psi$) is omitted completely.
  2. In part (a) (`L1561–1569`), $\epsilon_\psi$ and $w_\psi$ are never defined, and $m_c(n)$ is introduced as counting split $p\|n$ in $\{c, c^{-1}\}$ (which mixes $G_2$-components and can change the genus) without noting the decomposition $m_c^{\rm o} = m_{(1,c)} + m_c^{\rm rest}$ where the non-$G^2$ coordinates $m_c^{\rm rest}$ are conditioned on and absorbed into the compact coefficient set so that moving along $(0,\mathbf u) + j\mathbf w$ in $G^2$-coordinates holds the genus fixed.
  3. In part (b) (`L1588–1592`), the Cauchy–Schwarz + Rankin estimate proving that the Lemma 5.12 exceptional set contributes $o(S_Q \lambda_N)$ to the total width is mentioned only under *"For $2$-groups"*, whereas it is required for **every** $G$ to verify the first-moment bound $W(N) \le (\mathbb E_\Delta[1-1/d]\log 2 + o(1)) S_Q \lambda_N$ needed by Remark 3.16.
- **Actionable fix:** Replace L1583 with $\log_2 a_C(n) = \log_2(a(n)/h_0) + o(1) = (\frac{1}{2}+o(1))LL$ in probability (noting the cosine-product decay of nontrivial characters and tightness of prime-square factors); define $\epsilon_\psi, w_\psi$ and state the conditioning on non-$G^2$ coordinates in part (a); and state explicitly before the $2$-group specialization that the Cauchy–Schwarz + Rankin bound controls the exceptional-set width for all $G$ (establishing the first-moment condition of Remark 3.16).

---

## Minor Findings

### Minor-1: Unescaped `|` inside backticks breaks 6 Markdown table rows in `VERIFICATION.md`
- **Location:** `VERIFICATION.md:61, 94, 95, 111, 133, 136`.
- **Issue:** In GitHub Flavored Markdown, unescaped pipe characters inside inline code spans still split table columns. Affected rows:
  - L61 (`Lemma 2.6`): `` `|D_N(x) − D_N(y)| ≤ k/N + Σ|c_i|(1 − D_N(z_i))` `` (11 pipes instead of 7)
  - L94 (`Lemma 5.4`): `` `q_0 | e+1` `` (8 pipes)
  - L95 (`Lemma 5.5`): `` `|h| ≤ √x` `` (9 pipes)
  - L111 (`Thm 6.7`): `` `E|tr|` `` (9 pipes)
  - L133 (`Lemma 8.2`): `` `|λ_d| ≤ 1` `` (9 pipes)
  - L136 (`Lemma 8.5`): `` `g^2 | h` `` (8 pipes)
- **Actionable fix:** Escape every literal pipe inside table cells as `\|` (or use `∣` U+2223 for divisibility and `\|` for absolute values).

### Minor-2: Strict `Kernel-verified` scope precision in Lemmas 2.6, 3.10, Theorem 3.5, and Proposition 4.2
- **Location:** `paper.tex:442` (`lem:linear`), `paper.tex:516` (`thm:leantransfer`), `paper.tex:616` (`lem:radixval`), `paper.tex:842` (`prop:leaneuler`).
- **Issue:** The manuscript defines `[Kernel-verified]` strictly: *"the complete statement is a Lean 4 declaration checked by the kernel"* (`paper.tex:350`). Four minor deviations occur:
  - `paper.tex:442` (Lem 2.6, `Kernel-verified`): *"In particular $K_b$ is a $\Z[1/b]$-module"* is a 1-line paper deduction not formalized in `CharacterLambertTransfer.lean` or `Phase18Synthetic.lean`.
  - `paper.tex:616` (Lem 3.10, `Kernel-verified`): *"factors uniquely as $b^V U$"* — `CoefficientTransfer.lean:588–613` proves existence (`radixVal_mul_radixUnit`, `not_dvd_radixUnit`) and `displaced_term_eq`, not uniqueness.
  - `paper.tex:516` (Thm 3.5, `Kernel-verified`): omits *"with an integer $k \ge 0$"* (Lean requires `k : ℕ`), whereas L517 properly specifies *"with an integer $\gamma \ge 0$"*.
  - `paper.tex:842` (Prop 4.2, `Kernel-verified`): writes `\sum_{m\le M}` instead of `\sum_{1\le m\le M}` (Lean's `absMass` sums over `Icc 1 M`; though the inequality with $m=0$ included is also true, `Icc 1 M` matches the Lean theorem verbatim).
- **Actionable fix:** Move *"In particular $K_b$ is a $\Z[1/b]$-module"* to prose immediately after Lemma 2.6; drop `uniquely` from Lemma 3.10 and mention uniqueness in prose after it; add *"with an integer $k \ge 0$"* at L516; change `\sum_{m\le M}` to `\sum_{1\le m\le M}` at L842.

### Minor-3: Theorem 7.4 (`thm:classification`) proof slip at $b = 3$ and $N_0 = 4$
- **Location:** `paper.tex:1892–1901`.
- **Issue:**
  1. Line 1900–1901 claims: *"for $b \ge 3$, the fact that some interior digit has frequency at most $\delta_N/(b-2)$ in either case."* This is **false** for $b = 3$ in case (ii): $m = 1$ is the unique interior digit, and its frequency satisfies $f_1(N) \ge 1 - \delta_N \to 1$. (Of course $z$ is still not simply normal since $f_1(N) \to 1 \ne 1/3$ and $f_0(N) \to 0$.)
  2. Lines 1892–1895 do not enforce $N_0 \ge 5$: Theorem 7.3 requires $N \ge 4$, and at $N = 4$ one has $\frac{7}{8} - \frac{1}{5} = \frac{27}{40} = 0.675 < \frac{7}{10}$. Taking $N_0 \ge 5$ gives $\frac{7}{8} - \frac{1}{6} = \frac{17}{24} > \frac{7}{10}$ and makes every displayed fraction valid.
- **Actionable fix:** Require $N_0 \ge 5$ at L1892; replace L1900–1901 by *"in case (i) the $b-2$ interior digits have total frequency at most $\delta_N$, while in case (ii) $f_m(N) \to 1 \ne 1/b$ (and $f_0(N) \to 0$)."*

### Minor-4: Head run omission in Corollary 4.4 and "Nonconstant words" wording in Theorem 4.5
- **Location:** `paper.tex:890–891` (`cor:missing`) and `paper.tex:925` (`thm:eulerwords`).
- **Issue:**
  1. In `0.(b-2)(b-1)00 B_1 B_2 ...`, position 2 is a maximal run of `b-1` of length $1$ (surrounded by `b-2` and `0`), which is not of the form $4j$ or $2j+1$ for $j \ge 1$.
  2. Line 925 calls words distinct from $0^L$ and $(b-1)^L$ *"Nonconstant words,"* which is inaccurate when $L = 1$ and $b \ge 3$ (the digits $1$ and $b-2$ are constant words of length $1$).
- **Actionable fix:** In Corollary 4.4, clarify *"Inside the blocks $B_j$ ($j \ge 1$), the maximal runs of zeros have lengths $2j$ and $4j+2$ ... and the maximal runs of $b-1$ have lengths $4j$ and $2j+1$ (preceded by a single $b-1$ and a pair $00$ in the four-digit head)."* At L925, replace `Nonconstant words` by `Words other than 0^L and (b-1)^L`.

### Minor-5: Factor-of-2 slip for even $b$ in Theorem 4.7(d)
- **Location:** `paper.tex:1018`.
- **Issue:** Line 1018 states: *"As $k$ runs over $K$ consecutive integers, each class modulo $b^r$ contains at most $K/b^r + 1$ of the odd numbers $2k+1$."* For even $b$, $2k+1$ only hits odd residue classes modulo $b^r$, and each odd class is hit up to $2K/b^r + 1$ times (e.g., for $b = 2, r = 1$, class $1 \bmod 2$ contains all $K$ values). Since at most half the classes are odd, the product bound $O(K(1 + t\log K))$ is unaffected.
- **Actionable fix:** Replace `K/b^r + 1` by `2K/b^r + 1` at `paper.tex:1018`.

### Minor-6: Minor domain, sign, and quantifier omissions across statements
- **Locations & fixes:**
  - `paper.tex:2344–2345` (`prop:washout`): *"Every real $u$ has a representation $u = \sum_m a^*(m) b^{-m}$ with integers $0 \le a^*(m) \le b^2 - 1$"* cannot represent $u < 0$ or $u > b(b+1)$ unless $m \ge 1$ and $u \in [0, 1)$ (or $u = \lfloor u \rfloor + \sum_{m\ge 1} a^*(m) b^{-m}$ with $0 \le a^*(m) \le b^2 - 1$ for $m \ge 1$).
  - `paper.tex:1183–1186` (unary quadratic series): requires $f(t)$ to be a *"positive integer"*, yet three of the four examples immediately listed ($\Theta_3(1/b)$, $\sum_{t\ge 0} b^{-t(t+1)}$, Rogers' false theta) have $f(0) = 0$. Change `positive integer` to `nonnegative integer`.
  - `paper.tex:1135` (`thm:polyscal`(a)): specify $j \ge 0$ and $q_i \in \Z$ in $P = b^{-j}\sum_{i\le 3} q_i x^i$.
  - `paper.tex:594` (`prop:counterexamples`(b)): specify $\gamma > 0$.
  - `paper.tex:482` (`lem:meantail`): clarify that the Abel summation identity $\Ahat(X) = (1 - b^{-1})\sum_{i\ge 0} b^{-i} A(X+i)$ holds for integer $X \ge 0$.
  - `paper.tex:670–675` (`lem:source`): note that infinitely many positive sources are assumed and that for the first positive source $t_1$ one sets $g_{t_1} = t_1$ (the distance to $0$).
  - `paper.tex:1366` (`lem:runbarrier`): specify $\ell \ge 1$.
  - `paper.tex:1945` (`thm:nonneg`): specify $\gamma \ge 0$ (needed for $(N+R+k)^\gamma \le (N+R)^\gamma(1+k)^\gamma$).
  - `paper.tex:261–264` (`thm:F`(v)): specify $a \ne 0$ with $\gcd(a, d) = 1$, and drop the redundant parenthetical `(and d is odd, for the cube)` inside the `In base 2` clause (since $d$ is already assumed coprime to $b = 2$; that parity clause applies only to general $b$ in Theorem 7.15).
  - `paper.tex:575` (`thm:largermass`): write `S(X) \le C_1 X(\log X)^{-\kappa}` explicitly so $C_1$ is named cleanly.

### Minor-7: Minor proof-step clarifications and conditional-scope parallelism
- **Locations & fixes:**
  - `paper.tex:742` (`thm:widthlaw` proof): `\sum_{s<M} |A(s)| \le (A(2M) + O(1))/(b-1)` omits the $m > M$ tail $\sum_{m>M}|a(m)| b^{M-m} = M^{o(1)}$ (since $|a(m)| = m^{o(1)}$). Replace `+ O(1)` by `+ O(M^{o(1)})` (or simply write `\ll M(\log M)^B`).
  - `paper.tex:754–760` (`thm:widthlaw` proof): Lemma 3.14 gives non-strict `\dist{x_{t-j}} \ge \eta`, while Lemma 2.5 requires strict `>`. Apply Lemma 2.5 with $\eta' = \frac{3}{2}(\rho_N + \Delta^+) < \eta$ (so $\dist{x_{t-j}} \ge \eta > \eta'$ and $\zeta + \Delta < \eta'$).
  - `paper.tex:1166` (`thm:polyscal`(b) proof): change `[T_K, T_{2K}]` to `[T_K, T_{2K+2}]`, since $k = 2K$ can choose the run $[T_{2K+1}, T_{2K+2})$.
  - `paper.tex:1777` (remark after `thm:oddweights`): asserts *"the support exponent is then exactly $1/\lambda(M)$"* without proving the matching support lower bound (Theorem 6.10 uses only the upper bound $S(X) \ll X/(\log X)^{1/\lambda(M)}$ from Theorem 6.8). Either write *"at least $1/\lambda(M)$"* or include the short Galois-orbit lower bound.
  - `paper.tex:1805` (`prop:residueclass`): variable `s` in `r, s \in \{1, 3, 5, 7\}` is unused in the proposition statement (drop `, s` or state the $A_r - A_s$ inequality as well).
  - `paper.tex:2330–2331` (`prop:thetapowers` proof): add a brief parenthetical explaining the `7/N` and unit coefficient on $1 - D_N(L)$ (shift $16 L^2 = 2^4 L^2$ by $4$ and $8L = 2^3 L$ by $3$, using Theorem 2.3 and Lemma 2.6, giving $4/N + 3/N = 7/N$).
  - `paper.tex:178` (`thm:C`(iii)) and `paper.tex:277` (`thm:G`(ii)): explicitly add *"granting the eigenform identification of (ii)"* for $r = 2$ (odd prime factors of $d$) in Theorem C(iii), and note the CM eigenform inputs (Theorems 4.9 and 9.9) in Theorem G(ii), matching Theorems C(ii), D(ii), F(iv), and `VERIFICATION.md:51, 55`.

### Minor-8: Two `unverified` bibliography entries omitted from the checklist in `LEDGER.md:113`
- **Location:** `LEDGER.md:113` vs. `references.bib:158, 170`.
- **Issue:** `DNNS1996` and `Bertrand1997` are marked `unverified` in `references.bib`, but `LEDGER.md:113` lists the other 11 unverified references and omits these two.
- **Actionable fix:** Add `Duverney–Nishioka–Nishioka–Shiokawa` and `Bertrand` to the parenthetical list in `LEDGER.md:113`.

---

## Section-by-Section Verification Log

- **Abstract & §1 (L36–359):** Clean prose, zero process leaks, explicit series-vs.-product warning (§1.1), explicit "What is not claimed" (§1.4), explicit AI/cross-model peer-review disclaimer (§1.5, §12). Theorems A–G match §§2–9 except Major-4 (Thm F(ii)), Minor-6 (Thm F(v)), and Minor-7 (Thm C(iii), G(ii)).
- **§2 Finite tools (L360–449):** Lemmas 2.1–2.6 and Theorem 2.3 verified against Lean (`SharpTranslation`, `Phase18Synthetic`, `CoefficientTransfer`, `CharacterLambertTransfer`). `Near` (`≤`) and `farCount` (`¬ Near`, i.e., `>`) match `paper.tex` conventions exactly. Only Minor-2 on Lemma 2.6's unformalized $\Z[1/b]$-module sentence.
- **§3 Sparse coefficient transfer (L450–797):** Lemmas 3.1–3.3 and Theorems 3.4–3.8, Propositions 3.7, 3.9 verified in full (sharpness of constant $2$, integer-case negation $L + 1/(b-1) > N \iff L \ge N$, counterexamples). Major-3 on Theorem 3.12 (`\Lambda_N = o(N)` and unquantified $L$). Theorem 3.15 (Sub-threshold width law), Remark 3.16 (mixture form), and Corollary 3.17 (squares and primes) verified in full (Minor-2 on Lem 3.10, Thm 3.5; Minor-6 on Lem 3.3, 3.13, Prop 3.9, Thm 3.8; Minor-7 on Thm 3.15 tail & strict inequality).
- **§4 Euler's product and its powers (L798–1207):** Series vs. product framing is exemplary. All 10 `EulerPentagonal` declarations match Proposition 4.2 (Minor-2 on lower index `1 \le m`). Exact digit blocks of $E_b$ and $E_b^3$ and all-prefix word bounds of Theorem 4.5 independently verified in exact arithmetic; sharp deficits $\sqrt{2/3}$ and $\sqrt 2$ verified (Minor-4 on Cor 4.4 & Thm 4.5; Minor-5 on Thm 4.7(d)). Theorem 4.10 ($E_b^2$, $\eta(12\tau)^2$, Nebentypus $\chi_{-4}$, Euler factors giving denominator $54$, $C_\eta = 2.418529\ldots$, $\Cl(-144) \cong \Z/4$, $D_4$ Galois group) independently verified. Theorems 4.11–4.12 verified (Minor-6 on Thm 4.11(a) and unary series; Minor-7 on L1166).
- **§5 Exact constants in every radix (L1208–1599):** Major-2 on Theorem 5.1(c). §5.1 ($L_\chi(b)$ constants, Landau–Ramanujan $K/(2\log 2)$, first moment, concentration, valuations, pairs) verified. §5.2 ($2$-adic run barrier Lemma 5.7, sharp packing Lemma 5.8, prime-density Theorem 5.9, thresholds $\delta_b^* = 0.590616, 0.701754, 0.673632, 0.765433$) verified in full (Minor-6 on $\ell \ge 1$). §5.3 ($E_b^2$ constants) verified. §5.4 (Proposition 5.11, order-4 annihilation Lemma 5.12, Strassmann Lemma 5.13, Theorem 5.14 Euler products independently recomputed to $p \le 2\cdot 10^5$: $1.3621174$, $1.5319986$, $1.5888785$, matching text) verified, with Major-7 on the condensed proof of Theorem 5.14.
- **§6 Theta values, weight-one forms and periodic weights (L1600–1824):** §6.1 (ellipse area, anisotropy, shifted-lattice identity $|\Delta|^2 f = Q(|\Delta|m+U, |\Delta|n+V) + E_0$, irrationality criterion) verified. §6.2 (weight-one newforms including bad primes $|a_g(p)| \le 1$ at $k=1$, involution proportions $3/4, 1/2, 1/4, 3/8, 1/4$, mean $|\tr| < 1$ over all binary polyhedral groups) verified. §6.3 (even-order characters $\kappa_h = \frac{2}{h}\cot\frac{\pi}{2h}$ verified to $10^{-16}$, odd periodic weights, $q$-digamma sign & reflection identity verified against Gasper–Rahman and `GeneralMassTransfer.lean`, mod-8 character identities verified against `CharacterLambertTransfer.lean`), with Major-5 on `AntisymmetricLambert:510` vs `525` and Minor-7 on L1777 & L1805.
- **§7 Digit frequencies in the kernel (L1825–2158):** §7.1 (Lemmas 7.1–7.2, Theorems 7.3–7.4) verified, with Minor-3 on Thm 7.4. §7.2 (Lemma 7.5, Theorem 7.6) verified, with Major-4 on Thm F(ii) vs. Thm 7.6 and Minor-6 on $\gamma \ge 0$. §7.3 (Proposition 7.7 verified against all 6 `DerivativeTransfer` declarations; Theorems 7.8–7.9 verified including negative values $D^j E_b < 0$ and base-$b^k$ frequency law). §7.4 (Theorems 7.10–7.12): Major-1 on Theorem 7.11 (Wirsing 1967), Major-6 on Theorem 7.10 (`E_b^2` irrationality / Nesterenko). §7.5 (Lemma 7.13, Theorems 7.14–7.15, Proposition 7.16): `eulerAutomatonStep` verified against `NormalReciprocalCore.lean:310–345`; odd-order cancellation identities $S_{k+t} = -S_k$ and $R_{k+T} = -R_k$ independently verified.
- **§8 Uniform pair sieve for Euler's square (L2159–2289):** Lemmas 8.2–8.5 and Theorems 8.1 and 8.6 verified line by line, including $|\lambda_d| \le 1$, Rankin exponent $15.0613 < 15.07$, determinant $144h/g^2$, constant $4000$, $\zeta(2)\zeta(3)/\zeta(6) = 1.943596 < 1.9436$, and the odd-prime scaling contradiction. Completely airtight.
- **§9 Limits of sparse and signed transfer (L2290–2479):** Propositions 9.1–9.4, Theorems 9.5–9.9, Lemma 9.7 (numerical constant `26.7646 < 26.8` and `28.8/40 = 0.72 < 1` checked), and Corollary 9.10 (including CM prime-multiplicity $Y^{7/8}$ and net-cancellation example $F$) verified in full, with Minor-6 on Prop 9.4 (`u \in [0, 1)`) and Minor-7 on Prop 9.3 (`7/N`).
- **§§10–12, `VERIFICATION.md`, `LEDGER.md`, `references.bib`:** Open problems (§10) are accurately scoped. AI disclosure (§12) is explicit and candid. Verification table (§11) needs Major-5 fixes; `VERIFICATION.md` needs Major-5, Major-6, and Minor-1 fixes; `LEDGER.md` needs Minor-8.

---

## Final Verdict

**`REVISE`** — Repair the 7 Major findings (and the 8 Minor polish items while editing) and run a brief re-check. None of the findings requires new mathematics or alters any main theorem; once repaired, the candidate draft will be in strong shape for pre-release checks (`lake build`, axiom audit, script reruns, and human specialist review).

*Reminder: cross-model AI review is not independent human peer review.*

---

## Post-Repair Verification

- **Date:** 26 November 2026
- **Reviewer:** Gemini 4 Neon (post-repair re-check of Claude Opus 5.5 revision)
- **Files re-checked:**
  - `papers/11-generating-functions-digits/paper.tex` (2,651 lines)
  - `papers/11-generating-functions-digits/references.bib` (389 lines; 38 entries)
  - `papers/11-generating-functions-digits/VERIFICATION.md` (198 lines; 99 statement rows)
  - `papers/11-generating-functions-digits/LEDGER.md` (113 lines)
- **Post-repair verdict:** **`ACCEPT`** (0 Critical, 0 Major, 0 Minor remaining)

> **Peer-review disclaimer:** This post-repair re-check is an automated cross-provider AI review. **Cross-model review is not independent human peer review.** Independent human specialist review remains required prior to formal publication or release.

### Verification of Major Repairs

| ID | Status | Verification details |
| --- | --- | --- |
| **Major-1** | **Resolved** | `paper.tex:2142–2146` (`thm:wirsing67`) now restricts to multiplicative $0 \le g(n) \le 1$, eliminating the unbounded prime-power counterexample while covering the indicator $g = \mathbf{1}_{\mathcal S}$ used in Theorem 7.12. Mirrored in `VERIFICATION.md:126`. |
| **Major-2** | **Resolved** | `paper.tex:1255–1260` (`thm:meanvalues`(c)) now states $z_0 < z \le X$, $0 \le \omega(p) \le \min(A, p-1)$, the Halberstam–Richert dimension inequality $\sum_{w\le p<w',\,p\in\mathcal P}\omega(p)\log p/p \le \kappa_0\log(w'/w)+A$, $\lvert R_d\rvert\le\omega(d)$, and implied constant $\ll_{\kappa_0,A}$. Mirrored in `VERIFICATION.md:91`. |
| **Major-3** | **Resolved** | `paper.tex:657–686` (`thm:displacedwidth`) now assumes $P(N)\to\infty$, $\pi_N\to 0$, $\Lambda_N = o(P(N)\log_b(1/\pi_N))$, and $\widehat P(N+L_N)\le P(N)\pi_N^{-\eta_N}$ for explicit $L_N = \lceil(1+\eta_N)\log_b(1/\pi_N)\rceil$ ($\eta_N\to 0$), with a complete term-by-term proof (L672–685). Mirrored in `VERIFICATION.md:73`. |
| **Major-4** | **Resolved** | `paper.tex:2013–2050` (`thm:nonneg`) adds part (a) proving $f_{0^L}(N)\to 1$ under all three mass/sparsity regimes of Theorem 3.5 / Theorem A(iii) via Lemma 7.5(b),(d) and Abel summation, matching Theorem F(ii) (`paper.tex:253–255`) 1-to-1. Mirrored in `VERIFICATION.md:121`. |
| **Major-5** | **Resolved** | Theorem 6.9 (`paper.tex:1836`, `VERIFICATION.md:113`) now cites `AntisymmetricLambert:510` (`bounded_dirichletOneConv_tendsto_one_of_sparse`); Theorem 6.10 (`paper.tex:1866`, `VERIFICATION.md:114`) cites `AntisymmetricLambert:525` (`qDigamma_reflection_tendsto_one_of_sparse`). The §11 table (`paper.tex:2609–2625`) now accurately lists all 7 `RadixWidthLaw` declarations and all 5 theorems (`thm:displacedwidth,lem:onesource,thm:widthlaw,lem:firstmoment,lem:valuations`), 4 `AntisymmetricLambert` declarations, `discrepancy_add_int`, `not_dvd_radixUnit`, and `eulerAutomatonStep_bijective`. `VERIFICATION.md:54` column 4 now lists `as Proposition 7.7, Theorem 7.14`. |
| **Major-6** | **Resolved** | Theorem 7.10 (`paper.tex:2125–2136`) uses the non-strict condition $\sum_{m'\ge m} a_2(m') b^{m-m'} \ge 0$ matching Lemma 7.5(c), eliminating the irrationality dependency; the separate remark (`paper.tex:2138–2140`) explicitly notes that vanishing is ruled out by Nesterenko's theorem (Prop 6.5) and that Theorem 7.10 itself does not use it. Mirrored in `VERIFICATION.md:125`. |
| **Major-7** | **Resolved** | Theorem 5.14 proof (`paper.tex:1584–1658`) now explicitly proves $a_C(n)=(1+o(1))a(n)/h_0$ in probability via orthogonality and cosine-product decay of nontrivial characters, notes tightness (not uniform boundedness) of the prime-square term $T(n)$, establishes the Cauchy–Schwarz + Rankin exceptional-set width bound for *every* $G$ (and applies it to Remark 3.16's first-moment hypothesis), and defines $\epsilon_\psi$, $w_\psi(\pi)$, and the $G^2$-coordinate split $m^{\rm o}_c = m_{(1,c)} + m^{\rm rest}_c$ with conditioning. Mirrored in `VERIFICATION.md:104`. |

### Verification of Minor Repairs & Global Integrity

- **Minor-1:** Automated pipe-count verification confirms every Markdown table row in `VERIFICATION.md` (including L61, 94, 95, 111, 133, 136) and `LEDGER.md` has exact column pipe counts with all inner `|` escaped (`\|` or `∣`).
- **Minor-2:** `Kernel-verified` scopes tightened strictly in Lemma 2.6 (`paper.tex:438–453`), Theorem 3.5 (`paper.tex:521`), Lemma 3.10 (`paper.tex:620–632`), and Proposition 4.2 (`paper.tex:868`), with matching updates in `VERIFICATION.md:61, 66, 71, 80`.
- **Minor-3:** Theorem 7.4 proof (`paper.tex:1962–1974`) enforces $N_0 \ge 5$ and repairs the $b \ge 3$ non-simple-normality argument cleanly for both cases (i) and (ii).
- **Minor-4:** Corollary 4.4 (`paper.tex:916–919`) accounts for the head runs (`b-1` of length $1$ and `00`), and Theorem 4.5 (`paper.tex:952`) replaces *"Nonconstant words"* by *"Words other than $0^L$ and $(b-1)^L$."*
- **Minor-5:** Theorem 4.7(d) (`paper.tex:1047`) corrected to $2K/b^r + 1$.
- **Minor-6:** All 10 domain/sign/quantifier fixes verified: Prop 9.4 (`paper.tex:2441–2449`), unary quadratic series (`paper.tex:1213`), Thm 4.11(a) (`paper.tex:1164`), Prop 3.9(b) (`paper.tex:598`), Lem 3.3 (`paper.tex:487`), Lem 3.13 (`paper.tex:695–696`), Lem 5.7 (`paper.tex:1398`), Thm 7.6(c) (`paper.tex:2021`), Thm F(v) (`paper.tex:262–265`), and Thm 3.8 (`paper.tex:580`).
- **Minor-7:** All 7 proof/scope clarifications verified: Thm 3.15 (`paper.tex:764–765, 783–785`), Thm 4.11(b) (`paper.tex:1195–1197`), remark after Thm 6.9 (`paper.tex:1843–1845` + `VERIFICATION.md:114`), Prop 6.11 (`paper.tex:1875`), Prop 9.3 (`paper.tex:2425–2428`), Thm C(iii) (`paper.tex:178–179`), and Thm G(ii) (`paper.tex:278–279`).
- **Minor-8:** `LEDGER.md:113` now includes `Duverney–Nishioka–Nishioka–Shiokawa, Bertrand` in the unverified-records checklist.
- **Global automated checks after revision:** 38/38 bibliography entries cited (0 missing, 0 uncited); 0 undefined `\cref`/`\ref`/`\eqref`; 68/68 `\leanP` line links exact at commit `347ec3fe631a3e7ab2ae25d53508a3a4c9ea9fa8`; 99/99 numbered statements matched cleanly between `paper.tex` and `VERIFICATION.md`; 0 internal process-language leaks in `paper.tex`; 0 modifications to any archived release file in `papers/`. Also verified that `VERIFICATION.md:153` honestly reports the uncommitted Lean modules without citing them in `paper.tex`.

### Final Post-Repair Verdict

**`ACCEPT`** — All 7 Major and 8 Minor findings are cleanly resolved with no regressions. The Paper XI candidate draft is accepted as a candidate manuscript ready for pre-release operational checks (`lake build`, axiom audit, script reruns) and independent human specialist peer review.

*Reminder: cross-model AI review is not independent human peer review.*
