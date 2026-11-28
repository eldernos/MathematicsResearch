# Phase 25 Track H2: Historical Provenance and Primary-Source Literature Search

Search and compilation date: 28 November 2026. This note provides a primary-source provenance audit for the generalized Erdős–Borwein and dense digit-mass transfer program (Phase 24 Track A, `notes/phase24/dense-digit-mass-and-lambert.md`, `papers/14-dense-digit-mass-lambert/paper.tex`, `NormalityChecker/DigitMassTransfer.lean` on commit `04969b91f0c897ce55d21cb62c6b2c5aa3affe97`, and registry entries `CC-20`, `CC-21`, `CC-46`, `CC-48`, `CC-49`), together with prior-art input on computable badly approximable normal numbers for Phase 25 Track F2.

**Methodological caveat.** No web or bibliographic search can prove novelty or historical priority. Throughout this document, "not located in the searches conducted" records a negative search outcome only and is never treated as proof of priority. Every provenance judgment below is provisional pending independent human specialist review; cross-model review is not independent human peer review.

**Reading labels** (matching the repository novelty ledgers):
- **[R]** primary text read directly (here or in an earlier pinned repository audit, as indicated);
- **[A]** abstract, publisher metadata, or bibliographic record verified;
- **[S]** theorem stated via a secondary source or search summary that was read;
- **[M]** our own mathematical comparison or deduction;
- **[U]** unverified bibliographic detail retained only for completeness.

---

## Summary Index of the Nine Search Topics

| # | Topic | Primary Precedents Located | Repository Overlap / Status |
| --- | --- | --- | --- |
| 1 | Erdős (1948) Lambert-series irrationality | Erdős (1948); Vandehey (2012) | Classical irrationality baseline; no normality/digit-frequency result |
| 2 | P. Borwein (1991, 1992) Lambert-series irrationality | P. B. Borwein (1991, 1992) | Irrationality and non-Liouville property for $\sum 1/(q^n \pm r)$; no digit-distribution theorem |
| 3 | Bailey, Borwein, Crandall, Pomerance (2001–2012) on $E(2)$ and binary theta values | Bailey–Crandall (2002); BBCP (2004, §9); Crandall (2012); Bailey–Borwein (2012) | `BBCP` Thm 9.4 already proves $\#(z^2, N) \sim C_0 N/\sqrt{\log N}$ for $\theta_3(1/2)^2$ and conjectures 2-normality for $z^3, z^4$; repo extends to $D_N$, short windows, and general $L_\chi$ (`CC-46`, `CC-48`) and proves $E(2^k)$ ($k\ge 3$) |
| 4 | Binary/base-$b$ digit sums of divisor functions $s_b(\tau(n))$ | Kummer (1852); Senge–Straus (1973); Stewart (1980); Wirsing (1967); Mauduit–Rivat (2009, 2010); Luca / Banks–Shparlinski | Senge–Straus & Stewart supply the non-dyadic barrier; exact mean $C_{\mathrm{true}} = \lim X^{-1}\sum s_2(\tau(n))$ was not located in searches conducted |
| 5 | Signed-digit complexity, NAF, Booth recoding, minimal-weight binary representations | Booth (1951); Reitwiesner (1960); Avizienis (1961); Morain–Olivos (1990); Solinas (2000); Bosma (2001); Heuberger–Prodinger (2001, 2006); Grabner–Heuberger–Prodinger (2004) | Infinite-word NAF weight density $1/3$ and fixed-length NAF mean $L/3 + 2/9 + O(2^{-L})$ are classical; free-boundary formula $A_L = \frac{1}{3} - \frac{7-(-1/2)^{L-1}}{18L}$ and its application to $D^-(E_+(8);2)$ were not located |
| 6 | Mira Cult on $E(2)$ positive lower word density | Mira Cult (Oct–Nov 2026, `Mira-Cult/math` Claim 0002 & S06 gist) | External paper theorem audited in `CC-21`; combined with repo Lean transfer in `CC-20`, `CC-35`; disjoint from $E(2^k)$ ($k\ge 3$) nonnormality |
| 7 | Captain Sude on $E(2)$ and generalized Lambert disjunctivity | Captain Sude (Sept 2026, 3 pinned Lean repos); Campbell (May 2026); Lambrinoudis (2026) | Unconditional Lean disjunctivity for $E(2)$ ($N\exp(-70000(\log\log N)^3)$) and nonnormal disjunctivity for $\sum(b^{m^r}-1)^{-1}$ ($r\ge 2$); does not cover linear exponent $r=1$, $q=2^k$ ($k\ge 3$) |
| 8 | Existing results on disjunctivity/nonnormality of $E(2^k)$ ($k\ge 3$) or $E_+(2^k)$ | None located beyond irrationality (Erdős 1948; Borwein 1991, 1992) and $E(2)$ / $r\ge 2$ / $L_\chi$ | Simple nonnormality of $E(2^k)$ ($k\ge 3$) and nonnormality of $E_+(2^k)$ ($k\ge 3$) remain provisional novelty claims (absence of search hit $\ne$ proof of priority) |
| 9 | Computable badly approximable (absolutely) normal numbers (input for Track F2) | Kaufman (1980, 1981); Queffélec–Ramaré (2003); Hochman–Shmerkin (2015); Jordan–Sahlsten; Korobov (1955); Levin (1999); Bugeaud (2002, 2012); Becher–Heiber–Slaman (2013, 2015); Becher–Bugeaud–Slaman (2015); Scheerer (2015, 2017); Aistleitner–Becher–Scheerer–Slaman (2017) | Non-constructive existence of badly approximable (absolutely) normal numbers is known (Kaufman, Queffélec–Ramaré, Hochman–Shmerkin); computable absolutely normal, normal Liouville, and CF-normal numbers are known (BHS, Scheerer, ABSS); an explicit computable badly approximable absolutely normal construction was not located in searches conducted |

---

## Topic 1: Erdős (1948) on Irrationality of Lambert Series $E(2)$ and $E(b)$

### Entry 1.1 — Irrationality of $E(t) = \sum_{n=1}^{\infty} 1/(t^n - 1)$
- **Exact theorem:** For every integer $t > 1$, the Lambert series $E(t) = \sum_{n=1}^{\infty} \frac{1}{t^n - 1} = \sum_{n=1}^{\infty} \frac{\tau(n)}{t^n}$ is irrational. Erdős's paper also states the result for integers $|t| > 1$ (resolving a problem of S. Chowla).
- **Author and date:** Paul Erdős, 1948.
- **Primary-source citation / link:** P. Erdős, *On arithmetical properties of Lambert series*, Journal of the Indian Mathematical Society (N.S.) **12** (1948), 63–66. Scan archived at [renyi.hu/~p_erdos/1948-04.pdf](https://users.renyi.hu/~p_erdos/1948-04.pdf). Reading label: **[R]** (p. 63 verified in the Paper IX ledger and `notes/phase13/erdos-borwein.md`; confirmed via web search).
- **Relevant hypotheses:** Integer $t > 1$ (the original positive-base proof uses the Chinese Remainder Theorem to force arbitrarily long blocks of zeros in the base-$t$ expansion while ruling out termination, using elementary prime-distribution estimates).
- **What this repository reproves:** Nothing of the irrationality proof itself; irrationality of $E(2^k)$ ($k \ge 3$) is a trivial corollary of our nonnormality bounds only if non-periodicity is checked separately, and `NormalityChecker/DigitMassTransfer.lean` proves the series identity $E(2^k) = \sum_{n \ge 1} \tau(n) 2^{-kn}$ (`erdosBorweinPow_eq_divisor_series`).
- **What this repository extends:** Moves from irrationality to quantitative digit distribution in base $2$ and every base $2^j$ ($j \ge 1$): for every $k \ge 3$, $\limsup_N f_1(N; E(2^k), 2) \le 29/(20k)$ (kernel-verified) and $\le C_{\mathrm{true}}/k$ (paper + finite certificate), establishing simple nonnormality and $D^-(E(2^k); 2) > 0$.
- **What remains a provisional novelty claim:** Quantitative simple nonnormality and lower discrepancy bounds for $E(2^k)$ ($k \ge 3$) in base $2$ and bases $2^j$. Absence of a hit in web search does not prove priority.

### Entry 1.2 — Re-examination of Erdős (1948) for Negative Bases
- **Exact theorem:** Identifies a gap in Erdős's 1948 extension to negative integers $t \le -2$ and supplies a corrected proof using the Alford–Granville–Pomerance (1994) estimate for primes in arithmetic progressions (formulated as Proposition 2.1).
- **Author and date:** Joseph Vandehey, 2012.
- **Primary-source citation / link:** J. Vandehey, *On an incomplete argument of Erdős on the irrationality of Lambert series*, [arXiv:1206.0340](https://arxiv.org/abs/1206.0340) (2012). Reading label: **[S]** (audited in `notes/phase13/erdos-borwein.md` and `notes/phase18/sources.md`).
- **Relevant hypotheses:** Integer $t \le -2$ (and AGP with $0 < \delta < 5/12$ for primes in progressions avoiding a bounded exceptional set of moduli).
- **What this repository reproves:** None.
- **What this repository extends:** Context only; our signed-series transfer handles $E_+(2^k) = \sum (2^{kn}+1)^{-1}$ rather than negative bases $E(-2^k)$, though the signed transition-count transfer (`Theorem 7.1`) applies to any signed series $x = \sum a(n) 2^{-kn}$ with $\log(1 + |a(n)|) = o(n)$ and finite mean $\wpm(a(n))$.
- **What remains a provisional novelty claim:** None here (cited purely as provenance).

---

## Topic 2: Peter Borwein (1991, 1992) on Irrationality of Lambert Series

### Entry 2.1 — Irrationality and Non-Liouville Property of $\sum 1/(q^n + r)$
- **Exact theorem:** Let $q \ge 2$ be an integer and $r \in \mathbb{Q} \setminus \{0\}$ with $r \neq -q^m$ for all $m \in \mathbb{Z}_{\ge 1}$. Then $\sum_{n=1}^{\infty} \frac{1}{q^n + r}$ is irrational and is not a Liouville number (settling questions of Erdős and Graham; in particular $E_+(q) = \sum_{n \ge 1} (q^n + 1)^{-1}$ and $E(q) = \sum_{n \ge 1} (q^n - 1)^{-1}$ are irrational and non-Liouville).
- **Author and date:** Peter B. Borwein, 1991.
- **Primary-source citation / link:** P. B. Borwein, *On the irrationality of $\sum(1/(q^n+r))$*, Journal of Number Theory **37** (1991), no. 3, 253–259, [DOI: 10.1016/S0022-314X(05)80041-1](https://doi.org/10.1016/S0022-314X(05)80041-1). Reading label: **[A/S]** (Crossref metadata verified in Paper IX ledger; theorem statement verified via search summaries).
- **Relevant hypotheses:** Integer $q > 1$, rational $r \neq 0$, $r \neq -q^m$ ($m \ge 1$).
- **What this repository reproves:** None.
- **What this repository extends:** Borwein's 1991 paper addresses irrationality and irrationality measure (non-Liouville property) only, not base-$b$ digit frequencies or normality. Our Phase 24 results establish that for $q = 2^k$ ($k \ge 3$), $E(2^k)$ is simply nonnormal in every base $2^j$ and $E_+(2^k)$ is nonnormal in every base $2^j$ (not $2$-normal for $k \ge 4$; $D^-(E_+(8); 2) \ge 2.34 \times 10^{-7}$ via the 4-state transducer).
- **What remains a provisional novelty claim:** Nonnormality and lower discrepancy bounds for $E_+(2^k)$ ($k \ge 3$) and simple nonnormality of $E(2^k)$ ($k \ge 3$). Absence of a search hit does not prove priority.

### Entry 2.2 — Extension to $|q| > 1$ and General Series via Contour Integrals
- **Exact theorem (Theorem 1):** Let $q$ be an integer with $|q| > 1$ and $r \in \mathbb{Q} \setminus \{0\}$ with $r \neq q^n$ for all $n \ge 1$. Then $\sum_{n=1}^{\infty} \frac{1}{q^n - r}$ is irrational and not a Liouville number (proved via Padé/contour-integral orthogonality methods, extending to negative $q$ and related $q$-series).
- **Author and date:** Peter B. Borwein, 1992.
- **Primary-source citation / link:** P. B. Borwein, *On the irrationality of certain series*, Mathematical Proceedings of the Cambridge Philosophical Society **112** (1992), no. 1, 141–146, [DOI: 10.1017/S030500410007081X](https://doi.org/10.1017/S030500410007081X). Reading label: **[A/S]** (Crossref metadata verified; Theorem 1 verified via Cambridge Core summary).
- **Relevant hypotheses:** Integer $|q| > 1$, nonzero rational $r \neq q^n$.
- **What this repository reproves:** None.
- **What this repository extends:** Digit-distribution and discrepancy results for $r = \pm 1$ at $q = 2^k$ ($k \ge 3$); Borwein (1992) contains no normality or digit-frequency theorems.
- **What remains a provisional novelty claim:** Same as Entry 2.1.

---

## Topic 3: Bailey, Borwein, Crandall, and Pomerance on Erdős–Borwein Normality and Binary Theta Values

### Entry 3.1 — Bailey–Crandall (2002) on $E(2)$ and "2-Density"
- **Exact theorem (Conjecture 5.3 & Theorem 5.5):** Binary normality of $E = E(2) = \sum_{k \ge 1} (2^k - 1)^{-1}$ is equivalent to equidistribution modulo $1$ of the fractional parts $\{(2^d - 1)\sum_{k=1}^d (2^k - 1)^{-1}\}$. Section 5 also raises the problem of **2-density** (whether the doubling orbit $\{2^n E\}$ is dense in $[0,1)$, i.e., binary disjunctivity).
- **Author and date:** David H. Bailey and Richard E. Crandall, 2002.
- **Primary-source citation / link:** D. H. Bailey and R. E. Crandall, *Random generators and normal numbers*, Experimental Mathematics **11** (2002), no. 4, 527–546, [DOI: 10.1080/10586458.2002.10504704](https://doi.org/10.1080/10586458.2002.10504704), [author PDF](https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf). Reading label: **[R]** (verified in `notes/phase13/erdos-borwein.md` and `notes/phase18/sources.md`).
- **Relevant hypotheses:** Applies to $E(2)$ (construction exponent $k = 1$).
- **What this repository reproves:** None directly; our `CC-28`–`CC-30` and `CC-49` study the $E(2)$ arrival process and finite-column carry statistics, while `Theorem 9.1` gives the exact carry-density equivalence for $E(2)$ and $E(4)$.
- **What this repository extends:** Resolves the nonnormality of the generalized constants $E(2^k)$ for all $k \ge 3$ (leaving $k = 1, 2$ open, consistent with Bailey–Crandall's open problem for $E(2)$).
- **What remains a provisional novelty claim:** Simple nonnormality of $E(2^k)$ ($k \ge 3$) and the exact carry-density characterization $\kappa_2(N)/N \to (C_{\mathrm{true}} - 1)/2$ for $E(4)$ (and $\kappa_1(N)/N \to C_{\mathrm{true}} - 1/2$ for $E(2)$). Absence of a search hit does not prove priority.

### Entry 3.2 — Crandall (2012) on the Binary Expansion of $E(2)$
- **Exact theorem / open questions:** Develops fast bit-extraction algorithms for $E = E(2)$ (computing far-out binary digits via divisor sums), audits finite digit statistics, and asks explicitly (§7) whether the binary block `11` occurs infinitely often and whether $E$ is 2-normal.
- **Author and date:** Richard E. Crandall, 2012.
- **Primary-source citation / link:** R. Crandall, *The Googol-th Bit of the Erdős–Borwein Constant*, Integers **12** (2012), A23, [PDF](https://math.colgate.edu/~integers/m23/m23.pdf). Reading label: **[R]** (audited in `notes/phase13/erdos-borwein.md` and `CC-49` / `notes/phase17/erdos-borwein-bias.md`).
- **Relevant hypotheses:** Focuses on $E(2)$ in base $2$.
- **What this repository reproves:** `CC-49` audits Crandall's 2012 digit tables and refines the finite-column carry-bias heuristic ($p_* \in [0.492450290, 0.492460864]$ under the independent Poisson arrival comparison law $Q_\infty$, which is a comparison model and not a proof of nonnormality of $E(2)$).
- **What this repository extends:** Rigorous finite-statistic obstructions for $E(2)$ (`CC-49`), unconditional localization of the $E(2)$ divisor Fourier sum (`CC-29`), and unconditional simple nonnormality of $E(2^k)$ for $k \ge 3$.
- **What remains a provisional novelty claim:** The carry-knapsack/Bonferroni/trigonometric degree barriers for $E(2)$ (`CC-49`) and the $E(2^k)$ ($k \ge 3$) digit-mass transfer classification. Absence of a search hit does not prove priority.

### Entry 3.3 — Bailey–Borwein–Crandall–Pomerance (2004, Section 9) on Binary Theta Values $\theta_3(1/2)^2$, $\theta_3(1/2)^3$, $\theta_3(1/2)^4$
- **Exact published theorems and conjectural remarks:**
  - **Main algebraic theorem (Theorem 1 / §1):** If $y \in \mathbb{R}$ is algebraic of degree $D > 1$, then the count $\#(|y|, N)$ of $1$-bits among the first $N$ binary digits satisfies $\#(|y|, N) > C N^{1/D}$ for a constant $C = C(y) > 0$ and all sufficiently large $N$.
  - **Section 9 ("Study of a 'borderline' number", pp. 505–512):** Sets $z = \sum_{n \ge 0} 2^{-n^2}$ and $z' = 2z - 1 = \sum_{n \in \mathbb{Z}} 2^{-n^2} = \theta_3(1/2)$, so that $z'^2 = \theta_3(1/2)^2 = \sum_{n \ge 0} r_2(n) 2^{-n} = 1 + 4 \sum_{m \ge 1} \chi_4(m)/(2^m - 1)$ (since $r_2(n) = 4(\chi_4 * 1)(n)$ for $n \ge 1$).
  - **Theorem 9.4 (p. 509):** *"Almost all bits of $z^2$ are 0's; in fact the 1's-count has asymptotic behavior $\#(z^2, N) \sim C_0 N / \sqrt{\log N}$ for an absolute constant $C_0 \approx 0.7996\ldots$ (we give a formula for $C_0$ in the proof)."* The following paragraph states explicitly: *"Incidentally the asymptotic density also holds for $z'^2$ as follows from a slight modification (actually simplification) of the proof."* (Here $C_0$ is an explicit sum over squarefull integers supported on primes $\equiv 1 \pmod 4$, weighting the binary digit sums of $r_2$; $C_0$ is distinct from the Landau–Ramanujan constant $K \approx 0.764223654\ldots$.)
  - **Lemma 9.5 (p. 509):** There is an absolute constant $c$ such that for all integers $N, B > 2$, the number of $n \le N$ with $r_2(z, n) > 0$ and $r_2(z, m) > 0$ for some $0 < |n - m| \le B$ is at most $c B N / \log N$.
  - **Lemma 9.6 (p. 509):** The number of $n \le N$ with $r_2(z, n) > B$ is at most $(\sqrt{N} + 1)^2 / B$.
  - **Conjectural remarks on $\theta_3(1/2)^3$ and $\theta_3(1/2)^4$ (p. 509):** BBCP observe that $r_3(n) > 0$ for a positive density $5/6$ of integers $n$ (by Legendre's three-square theorem, all $n$ not of the form $4^a(8b+7)$) and $r_4(n) > 0$ for every $n \ge 1$ (Lagrange's four-square theorem, with $r_4(n) = 8 \sum_{d \mid n,\, 4 \nmid d} d$). They note that interfering carries prevent their isolated-bit method from applying, and remark that higher powers $z^3$ ($\theta_3(1/2)^3$) and $z^4$ ($\theta_3(1/2)^4$) are *"likely"* to be $2$-normal (no proof is given for either).
  - **Transcendence remark (p. 506):** Cites Duverney–Nishioka–Nishioka–Shiokawa (1996) and Bertrand (1997) (via Nesterenko 1996) that $z$ and $z' = \theta_3(1/2)$ are transcendental, noting that transcendence does not decide binary digit density.
- **Author and date:** David H. Bailey, Jonathan M. Borwein, Richard E. Crandall, and Carl Pomerance, 2004.
- **Primary-source citation / link:** D. H. Bailey, J. M. Borwein, R. E. Crandall, and C. Pomerance, *On the binary expansions of algebraic numbers*, Journal de Théorie des Nombres de Bordeaux **16** (2004), no. 3, 487–518, [DOI: 10.5802/jtnb.457](https://doi.org/10.5802/jtnb.457) (Numdam scan). Reading label: **[R]** (Section 9, pp. 505–512, read directly in the Numdam PDF in `notes/phase20/literature.md` §3 and `papers/06-multiplicative-lambert/LEDGER.md`).
- **Relevant hypotheses:** Binary expansion ($b = 2$); $z = \sum_{n \ge 0} 2^{-n^2}$ and $z' = \theta_3(1/2)$.
- **What this repository reproves:** For $L_{\chi_4} = \sum \chi_4(m)/(2^m - 1) = (\theta_3(1/2)^2 - 1)/4$, the upper bound $\#_1(N) = O(N/\sqrt{\log N})$ and hence simple nonnormality and $D_N \to 1$ in `CC-46` and `CC-48` recover (at order level, without $C_0$) BBCP Theorem 9.4's consequence for $z'^2$.
- **What this repository extends:**
  1. `CC-46` and `CC-48` extend from the single constant $\theta_3(1/2)^2$ and the single digit `1` to general nonnegative multiplicative Lambert series $L_f = \sum c(n) 2^{-n}$ (including all nonprincipal real Dirichlet characters $\chi$ and index-4 families), proving two-sided short-window word counts $\#_w(N, H) \asymp_{w,a} H / (\log N)^{1-\delta}$ for **every** binary word $w \neq 0^k$ on $N^a \le H \le N$ ($7/12 < a \le 1$), base-$2$ disjunctivity, and the exact two-sided extreme discrepancy gap $1 - D_N(L_f; 2) \asymp (\log\log N)/(\log N)^{1-\delta}$ (sharpened in Phase 20 to the exact asymptotic constant $K / (2 \log 2)$ for $\theta_3(1/2)^2$, where $K$ is the Landau–Ramanujan constant rather than BBCP's $C_0$).
  2. Unlike BBCP's isolation argument for $z'^2$ (which relies on sparsity of sums of two squares), Phase 24's digit-mass transfer handles **full-density** series such as $E(2^k)$ ($k \ge 3$) where every coefficient $\tau(n) \ge 1$ is nonzero, by bounding carries monotonically via Kummer's identity instead of isolating bits.
- **What remains a provisional novelty claim:** Short-window all-word counts, exact discrepancy gap asymptotics for $L_f$ and $\theta_3(1/2)^2$, and full-density digit-mass transfer for $E(2^k)$ ($k \ge 3$). The conjectured $2$-normality of $\theta_3(1/2)^3$ and $\theta_3(1/2)^4$ remains open (and in fact $r_4(n) = 8 \sum_{d \mid n,\, 4 \nmid d} d$ has coefficients growing linearly in $n$, placing $\theta_3(1/2)^4$ outside bounded-digit-mass methods, just like $E(2)$). Absence of a search hit does not prove priority.

*(Note: Bailey and J. M. Borwein's 2012 paper, "Nonnormality of Stoneham constants", Ramanujan J. **29** (2012), 409–422, [DOI: 10.1007/s11139-012-9417-3](https://doi.org/10.1007/s11139-012-9417-3) **[R]** in Phase 18, proves nonnormality of $\alpha_{2,3}$ in base $6$; no Bailey–Borwein publication proving nonnormality of generalized Erdős–Borwein constants $E(2^k)$ ($k \ge 3$) was located in the searches conducted.)*

---

## Topic 4: Binary and Base-$b$ Digit Sums of Divisor Functions $s_2(\tau(n))$, $s_b(\tau(n))$, and Multiplicative Dependence

### Entry 4.1 — Kummer's Carry Identity (1852)
- **Exact theorem:** The $p$-adic valuation of $\binom{a+c}{a}$ equals the number of carries $\kappa_p(a, c)$ when adding $a$ and $c$ in base $p$; equivalently, $s_p(a + c) + (p - 1)\kappa_p(a, c) = s_p(a) + s_p(c)$ (and the same elementary column-carry identity holds in every integer base $b \ge 2$).
- **Author and date:** Ernst Eduard Kummer, 1852.
- **Primary-source citation / link:** E. E. Kummer, *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen*, J. Reine Angew. Math. **44** (1852), 93–146. Reading label: **[S]** (standard theorem; original 1852 scan not read).
- **Relevant hypotheses:** Base $b \ge 2$ (prime $p$ for the binomial-coefficient valuation identity; arbitrary integer $b \ge 2$ for the digit-sum carry identity).
- **What this repository reproves:** `DigitMassTransfer.lean` kernel-verifies the two-summand base-$b$ identity (`digitSum_add_add_carries`) and subadditivity/submultiplicativity (`digitSum_add_le`, `digitSum_mul_le`, `nonzeroDigits_add_le`, `nonzeroDigits_mul_le`). No novelty is claimed for these elementary lemmas; our contribution is their Lean 4 formalization and assembly into the transfer theorem.
- **What this repository extends:** Exact many-summand truncation/carry-tail transfer (`Theorem 2.2`) for $\sum a(n) b^{-kn}$ and its sharp carry-balance corollaries for $E(4)$ and $E^*(4)$.
- **What remains a provisional novelty claim:** None for Kummer's identity itself.

### Entry 4.2 — Senge–Straus (1973) and Stewart (1980) on Bounded Digit Sums in Two Bases
- **Exact theorem:**
  - **Senge–Straus (1973):** Let $a, b \ge 2$ be integers. The set of positive integers $n$ for which $s_a(n) + s_b(n) \le K$ (equivalently, both $s_a(n)$ and $s_b(n)$ are bounded) is finite for every $K$ **if and only if** $\log a / \log b \notin \mathbb{Q}$ (i.e., $a$ and $b$ are multiplicatively independent). Proved via Mahler's $p$-adic Thue–Siegel–Roth theorem (ineffective).
  - **Stewart (1980):** Gives an **effective** lower bound on $s_a(n) + s_b(n)$ for multiplicatively independent bases $a, b \ge 2$ using Baker's theory of linear forms in logarithms (building on Loxton–van der Poorten).
- **Author and date:** H. G. Senge and E. G. Straus, 1973; C. L. Stewart, 1980.
- **Primary-source citation / link:**
  - H. G. Senge and E. G. Straus, *PV-numbers and sets of multiplicity*, Periodica Mathematica Hungarica **3** (1973), 93–100, [DOI: 10.1007/BF02018464](https://doi.org/10.1007/BF02018464). Reading label: **[S]** (theorem statement verified via multiple secondary literature summaries and Stewart 1980 citation).
  - C. L. Stewart, *On the representation of an integer in two different bases*, J. Reine Angew. Math. **319** (1980), 63–72, [EuDML](https://eudml.org/doc/152267). Reading label: **[S]** (metadata and effective-Baker scope verified via search summaries).
- **Relevant hypotheses:** Integer bases $a, b \ge 2$ with $\log a / \log b \notin \mathbb{Q}$.
- **What this repository reproves:** Neither theorem is reproved; both are cited explicitly as **External input** (`Theorem 5.1`, `Theorem 6.2`).
- **What this repository extends:** Applies Senge–Straus to $a = r$ and $n = \tau_r(m) = r^{\omega(m)}$ on squarefree $m$ (combined with $\omega(m) \to \infty$ on density $1$) to prove the exact **$\tau_r$ digit-mass dichotomy**: $\limsup_X X^{-1}\sum_{n \le X} s_b(\tau_r(n)) < \infty$ if and only if $r$ and $b$ are multiplicatively dependent, and otherwise $X^{-1}\sum_{n \le X} w_b(\tau_r(n)) \to \infty$. In particular, for $r = 2$, digit-mass transfer for $E(b^k)$ in base $b$ is provably vacuous whenever $b$ is not a power of $2$.
- **What remains a provisional novelty claim:** The $\tau_r$ base-$b$ mean-digit-mass dichotomy and the resulting non-dyadic barrier for $E(b^k)$. Absence of a search hit does not prove priority.

### Entry 4.3 — Mean Value of $s_2(\tau(n))$ and Related Digit-Sum Literature (Luca, Mauduit–Rivat, Banks–Shparlinski, Wintner/Wirsing)
- **Exact theorem / literature landscape:**
  - **Mauduit–Rivat (2009, 2010):** Proved Gelfond's conjectures on the distribution of $s_q(n^2)$ (*Acta Math.* **203** (2009), 107–148) and $s_q(p)$ over primes (*Ann. of Math.* **171** (2010), 1591–1646) **[S]**.
  - **Luca, Banks, Conflitti, Shparlinski:** Extensive literature on arithmetic functions ($\phi, \sigma, \tau$) evaluated on integers with digital restrictions (repdigits, missing digits, restricted base-$q$ expansions) and on $s_q(\phi(n))$, $s_q(\sigma(n))$, or prime factors of integers with fixed digit sums **[S]**.
  - **Wintner-type convolution mean values & Wirsing (1967):** The elementary mean-value lemma (`Lemma 3.1`: if $h = G * \mu$ has $\sum |h(n)|/n < \infty$, then $X^{-1}\sum_{n \le X} G(n) \to \sum h(n)/n$) is classical Wintner/Axer-type analytic number theory (no novelty claimed). Wirsing (*Acta Math. Acad. Sci. Hungar.* **18** (1967), 411–467) gives mean value $0$ for real multiplicative functions $|f| \le 1$ with $\sum (1 - f(p))/p = \infty$ (used as **External input** in Proposition 7.2 of Paper XIV for direct base-$4$ transfer).
  - **Specific search for $s_2(\tau(n))$ / $s_2(d(n))$:** Dedicated web searches for `"sum of binary digits" "divisor function"`, `"s_2(d(n))"`, `"s_2(\tau(n))"`, `"average" "popcount" "divisors"`, and `"Luca" OR "Mauduit" OR "Rivat" OR "Shparlinski" "digit sum" "divisor function"` returned no published paper evaluating $C_{\mathrm{true}} = \lim_{X \to \infty} X^{-1}\sum_{n \le X} s_2(\tau(n))$ or its multiplicative majorant $C = \prod_p \sum_{j \ge 0} p/(p^{2^j} + 1)$.
- **Author and date:** Classical / contemporary (1967–2020s).
- **Primary-source citation / link:** C. Mauduit and J. Rivat, *Sur un problème de Gelfond: la somme des chiffres des nombres premiers*, Ann. of Math. **171** (2010), 1591–1646; E. Wirsing, *Das asymptotische Verhalten von Summen über multiplikative Funktionen. II*, Acta Math. Acad. Sci. Hungar. **18** (1967), 411–467. Reading label: **[S]**.
- **Relevant hypotheses:** Distinct problem domain (Mauduit–Rivat study $s_q$ on primes/squares; Luca/Banks–Shparlinski study $\tau$ on digitally restricted inputs or $s_q$ on $\phi, \sigma$).
- **What this repository reproves:** `DigitMassTransfer.lean` formalizes the Wintner-type convolution limit (`tendsto_average_of_summable_conv_mobius`) by dominated convergence without Tauberian input.
- **What this repository extends:** Proves existence and certified enclosures of $C_{\mathrm{true}} = \lim X^{-1}\sum_{n \le X} s_2(\tau(n)) \in [1.339103, 1.339116]$, the multiplicative majorant $C = \prod_p \sum_{j \ge 0} p/(p^{2^j} + 1) \in [1.4035953, 1.4035958]$ (with $C \le 29/20$ kernel-verified in Lean 4), the odd-divisor mean $C_{\mathrm{odd}}$, the $\tau_4, \tau_8, \tau_{16}$ means, the base-$b$ $\tau_b$ means $C_{[b]}$, and the signed NAF mean $W_+ = \lim X^{-1}\sum_{n \le X} w_\pm(a_+(n)) \in [0.908174, 0.908184]$.
- **What remains a provisional novelty claim:** Existence and exact numerical certification of $C_{\mathrm{true}}$, $C$, $W_+$, and the independent-exponent model (`Lemma 3.2`) applied to submultiplicative digit functionals of divisor functions. Absence of a hit in web search does not prove priority (especially since MathSciNet, zbMATH, and OEIS were not exhaustively searched).

---

## Topic 5: Signed-Digit Complexity, Non-Adjacent Form (NAF), Booth Recoding, and Minimal-Weight Binary Representations

### Entry 5.1 — Booth (1951), Reitwiesner (1960), and Avizienis (1961): Foundations of Signed-Digit Arithmetic and NAF
- **Exact theorem:**
  - **Booth (1951):** Introduces Booth recoding for two's-complement binary multiplication, converting runs of $1$-bits into pairs of signed transitions $+2^{j+1} - 2^i$.
  - **Reitwiesner (1960):** Proves that every integer $n$ has a unique **Non-Adjacent Form (NAF)** $n = \sum_i \varepsilon_i 2^i$ with $\varepsilon_i \in \{-1, 0, 1\}$ and $\varepsilon_i \varepsilon_{i+1} = 0$, and that the NAF minimizes the Hamming weight $\sum_i |\varepsilon_i|$ over all signed binary representations of $n$ (defining our $w_\pm(n)$).
  - **Avizienis (1961):** Formalizes general redundant signed-digit number systems enabling carry-free parallel addition.
- **Author and date:** A. D. Booth (1951); G. W. Reitwiesner (1960); A. Avizienis (1961).
- **Primary-source citation / link:**
  - A. D. Booth, *A signed binary multiplication technique*, Quart. J. Mech. Appl. Math. **4** (1951), 236–240. Reading label: **[S]**.
  - G. W. Reitwiesner, *Binary arithmetic*, in *Advances in Computers*, Vol. 1, Academic Press, New York (1960), 231–308. Reading label: **[S]** (bibliographic record verified; NAF existence/minimality used as **External input** in Lemma 6.6 of Paper XIV).
  - A. Avizienis, *Signed-digit number representations for parallel arithmetic*, IRE Trans. Electron. Comput. **EC-10** (1961), 389–400. Reading label: **[S]**.
- **Relevant hypotheses:** Finite integer representations in base $2$ with signed digit set $\{-1, 0, 1\}$.
- **What this repository reproves:** `DigitMassTransfer.lean` kernel-verifies the defining recursion for `signedWeight`, its subadditivity, submultiplicativity, $2$-shift invariance, and the two's-complement transition increment bound $|T(A \pm 2^m) - T(A)| \le 2$ (`transitions_add_two_pow`, `transitions_add_le`), which is closely allied in spirit to Booth's run-boundary interpretation of $1$-runs.
- **What this repository extends:** Uses `signedWeight` and `transitions` as a monotone transfer invariant for infinite signed binary series $\sum a(n) 2^{-kn}$ (`Theorem 7.1`, `Theorem 7.2`) and extends minimal signed-digit weight to infinite real expansions $\sigma_1(x; N)$ (`Definition 6.4` / `Theorem 6.8` in Paper XIV).
- **What remains a provisional novelty claim:** None for NAF existence, minimality, or Booth recoding themselves.

### Entry 5.2 — Asymptotic and Exact Average NAF Hamming Weight (Morain–Olivos 1990; Solinas 2000; Bosma 2001; Heuberger–Prodinger 2001, 2006; Grabner–Heuberger–Prodinger 2004)
- **Exact theorem:**
  - **Asymptotic density $1/3$ (classical):** Among random binary integers of length $\ell$ (or uniformly over $[0, 2^\ell)$), the average NAF Hamming weight is asymptotically $\ell/3 + O(1)$, i.e., nonzero digit density **$1/3$** (compared to $1/2$ in standard binary).
  - **Exact finite-length NAF mean (fixed-boundary integer NAF):** Using transfer operators, transducers, and generating functions (Bosma 2001; Heuberger–Prodinger 2001, 2006; Grabner–Heuberger–Prodinger 2004), the expected Hamming weight of the NAF of a length-$\ell$ integer satisfies
    $$\mathbb{E}[H_\ell^{\mathrm{NAF}}] = \frac{\ell}{3} + \frac{2}{9} + O(2^{-\ell})$$
    (with small boundary-dependent constants depending on whether averaging over $\{0, \dots, 2^\ell - 1\}$ or fixed NAF length $\ell$, and central limit theorems for joint sparse forms).
  - **Solinas (2000) & Morain–Olivos (1990):** Addition-subtraction chains and $\tau$-adic / width-$w$ NAF for elliptic curve cryptography.
- **Author and date:** F. Morain & J. Olivos (1990); J. A. Solinas (2000); W. Bosma (2001); C. Heuberger & H. Prodinger (2001, 2006); P. J. Grabner, C. Heuberger & H. Prodinger (2004).
- **Primary-source citation / link:**
  - F. Morain and J. Olivos, *Speeding up the computations on an elliptic curve using addition-subtraction chains*, RAIRO Inform. Théor. Appl. **24** (1990), 531–543 **[S]**.
  - J. A. Solinas, *Efficient arithmetic on Koblitz curves*, Designs, Codes and Cryptography **19** (2000), no. 2–3, 195–249 **[S]**.
  - W. Bosma, *Signed bits and fast exponentiation*, J. Théor. Nombres Bordeaux **13** (2001), no. 1, 27–41 **[S]**.
  - C. Heuberger and H. Prodinger, *On minimal expansions in redundant number systems: algorithms and quantitative analysis*, Computing **66** (2001), 377–393 **[S]**; *Analysis of alternative digit sets for nonadjacent representations*, Monatsh. Math. **147** (2006), 219–248 **[S]**.
  - P. J. Grabner, C. Heuberger, and H. Prodinger, *Distribution results for low-weight binary representations for pairs of integers*, Theoretical Computer Science **319** (2004), 307–331 **[S]**.
- **Relevant hypotheses:** Standard (zero-boundary) integer NAF representations of finite integers $0 \le n < 2^\ell$ or fixed-length NAF words, motivated by fast scalar multiplication in ECC.
- **What this repository reproves:** The infinite-word limit $\lim_{L \to \infty} A_L = 1/3$ of our free-boundary signed-digit weight recovers the classical NAF asymptotic density $1/3$.
- **What this repository extends:**
  - **Crucial boundary distinction:** Standard NAF fixes boundary carries to $0$ (yielding the positive $+2/9$ boundary overhead in $\ell/3 + 2/9 + O(2^{-\ell})$). In Paper XIV (§6.2, `Theorem 6.7`), because a subword $u = d_{m+1}\cdots d_{m+L}$ inside an infinite real expansion can both receive an arbitrary incoming carry $\delta_0 \in \{-1, 0, 1\}$ and emit an arbitrary outgoing carry $\delta_L \in \{-1, 0, 1\}$, we study the **free-boundary** minimal signed-digit weight $\sigma_{\mathrm{free}}(u)$, realized by a minimal 4-state deterministic transducer with stationary distribution $(1/6, 1/3, 1/3, 1/6)$ and exact uniform average per bit
    $$A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18L} \qquad (L \ge 1).$$
  - Notice the opposite sign of the $O(1/L)$ correction: free boundaries strictly *reduce* the mean weight below $1/3$ (approaching $1/3$ monotonically from below, e.g., $A_{16} = 324039/1048576 \approx 0.309028$), which is essential for turning finite-window word frequencies into a rigorous **lower** floor $\limsup_N \sigma_1(x; N)/N \ge A_L(1 - 2^L D^-(x; 2))$ (`Theorem 6.8`) that beats $W_+/3 \le 0.304282$ and proves nonnormality of $E_+(8)$ (`Theorem 6.10`).
- **What remains a provisional novelty claim:** Neither the exact free-boundary formula $A_L = \frac{1}{3} - \frac{7 - (-1/2)^{L-1}}{18L}$ (nor its 4-state transducer derivation) nor the signed-support floor linking $A_L$ to extreme discrepancy $D^-(x; 2)$ and nonnormality of real numbers (specifically $E_+(8)$) was located in the NAF literature searched. Absence of a search hit does not prove priority; the infinite-word limit $1/3$ itself is explicitly classical and must be credited to the NAF literature (Reitwiesner / Bosma / Heuberger–Prodinger).

---

## Topic 6: Mira Cult's Pinned Results on Erdős–Borwein Positive Lower Word Density

### Entry 6.1 — Short-Window Positive Lower Word Density for $E(2)$ (Claim 0002)
- **Exact theorem:** Fix a nonempty binary word $w$ and $7/12 < a \le 1$. In the binary expansion of the Erdős–Borwein constant $E = E(2) = \sum_{m \ge 1} (2^m - 1)^{-1}$, every sufficiently late window of length $H$ after digit $N$ with $N^a \le H \le N$ contains at least $c_{a,w} H$ wholly contained copies of $w$, for a constant $c_{a,w} > 0$. In particular, every finite binary word occurs in $E(2)$ with positive ordinary lower density.
- **Author and date:** Mira Cult (commit author `mira-emmy`; paper credits GPT-6.2 Astra with developing and drafting the proof under Mira's guidance), 23 November 2026. (Earlier October 2026 research gist S06, revision `41b5a780f79f7bdd275cd96e7e310b000a897d35`, gave the weaker sub-density bound $N \exp[-C_w (\log\log N)^2 \log\log\log N]$.)
- **Primary-source citation / link:**
  - `Mira-Cult/math`, Claim 0002: [README (`1498319438`)](https://github.com/Mira-Cult/math/blob/149831943806a656c9efaa14cacbd9c915b2a2ba/notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/README.md), first public commit [`a74afd540a`](https://github.com/Mira-Cult/math/commit/a74afd540a6401026e7789a3734ce1492f823065), public archive [`357d26a23f`](https://github.com/Mira-Cult/math/tree/357d26a23fbbee5c900098938744ab732b84d03a).
  - October 2026 gist S06: [`41b5a780f7`](https://gist.github.com/Mira-acc/79be9a5d4aa54a9df41e702c4f3113ea/41b5a780f79f7bdd275cd96e7e310b000a897d35).
  - Repository audit: `notes/phase13/erdos-borwein.md`, `notes/phase13/reviews/erdos-local-limit.md`, and registry entries `CC-20`, `CC-21`, `CC-35`. Reading label: **[R]** (public notes audited in Phase 13; note that `VERIFICATION.md` records internal nonauthor checks only, not independent peer review, and the repository's own audit flagged the uniform multi-bank force-weighted exact-atom induction as the step with the greatest remaining verification burden).
- **Relevant hypotheses:** Uses the Huxley–Iwaniec short-interval Bombieri–Vinogradov range ($7/12 < \vartheta \le 29/48$) as stated in Perelli–Pintz–Salerno (1984/1985), combined with a multi-bank conditional local-limit isolation argument for $E(2)$ ($k = 1$).
- **What this repository reproves:** `CC-21` records an independent written audit of the weighted local-limit reduction (`notes/phase13/reviews/erdos-local-limit.md`), explicitly attributing the analytic density theorem to Mira Cult.
- **What this repository extends:**
  1. `CC-20` (Lean 4) and `CC-35` (Lean + paper) combine Mira Cult's word count as an external input with kernel-verified Fourier/radial transfers to deduce a strict Fourier deficit and $D^+(E(2); 2) < 1$ on short windows.
  2. `CC-46` and `CC-48` adapt the Perelli–Pintz–Salerno + Selberg-sieve planting architecture to character Lambert series $L_\chi$ ($k = 1$, sparse support), obtaining two-sided short-window word counts $\asymp H/(\log N)^{1-\delta}$ together with nonnormality ($D_N \to 1$).
  3. Phase 24's digit-mass transfer addresses an **orthogonal** direction: unconditional **nonnormality** (upper bounds on $f_1$ and lower bounds on $D^-$) for $E(2^k)$ and $E_+(2^k)$ ($k \ge 3$), whereas Mira Cult's theorem addresses **lower** bounds on word occurrences (hence $D^+ < 1$) for $E(2)$ ($k = 1$). Neither result implies the other.
- **What remains a provisional novelty claim:** For Phase 24, the entire digit-mass transfer and $E(2^k), E_+(2^k)$ ($k \ge 3$) nonnormality theory is disjoint from Claim 0002 (which does not treat $k \ge 3$ or nonnormality). As verified in `notes/phase20/literature.md` §8 (tree scan at commit `cf9e57f`, 25 Nov 2026), `Mira-Cult/math/notes/number-theory/normal-numbers/` contained `0001-joint-digit-switches.md`, `0002-erdos-borwein-positive-word-density.md`, `normal-dovetails/`, and `stoneham-joint-normality.md` (a filename/README scan only; absence of a hit does not exclude unpublished or later notes).

---

## Topic 7: Captain Sude's Pinned Generalized Lambert / Erdős–Borwein Disjunctivity Results (and 2026 Contemporaries)

### Entry 7.1 — Captain Sude (Sept 2026) on $E(2)$ Disjunctivity (Conditional and Elementary Unconditional Lean 4 Releases)
- **Exact theorem:**
  - `erdos-borwein-disjunctivity` (7 Sept 2026, tag `v1.0.0`, `bd98789a177470cc4b3e33e6769e859f6144c906`): Lean 4 proof of binary disjunctivity of $E(2)$ conditional on `AGP` ($\delta = 1/4$) and `PrimeIntervalSupply`; companion TeX states prefix count $\ge N \exp[-C_w (\log\log N)^3]$.
  - `erdos-borwein-disjunctivity-elementary` (8 Sept 2026, `d51e93e91ff43efef6918efdd4258bbd43bad7aa`): **Unconditional** Lean 4 proof (`binaryDisjunctive_lambertE_unconditional` and `quantitative_occurrences_lambertE`) that every binary word of length $\ell$ occurs at least $N \exp[-70000(\log\log N)^3]$ times among the first $N$ starts of $E(2)$ for sufficiently large $N$.
- **Author and date:** Captain Sude (GitHub account / commit attribution), 7–8 September 2026.
- **Primary-source citation / link:** [`CaptainSude/erdos-borwein-disjunctivity`](https://github.com/CaptainSude/erdos-borwein-disjunctivity/tree/bd98789a177470cc4b3e33e6769e859f6144c906); [`CaptainSude/erdos-borwein-disjunctivity-elementary`](https://github.com/CaptainSude/erdos-borwein-disjunctivity-elementary/tree/d51e93e91ff43efef6918efdd4258bbd43bad7aa). Reading label: **[R]** (ZIP hashes, theorem types, and axiom reports audited in `notes/phase13/erdos-borwein.md` and `notes/phase18/sources.md` §7).
- **Relevant hypotheses:** Applies to $E(2)$ ($k = 1$); elementary squarefree cofactor construction without AGP.
- **What this repository reproves:** None; `CC-20` cites the elementary release as an external word-count input to its kernel-verified Fourier deficit transfer.
- **What this repository extends:** Distinct problem: Captain Sude proves disjunctivity (lower word counts of sub-linear order) for $E(2)$; Phase 24 proves simple nonnormality and positive lower discrepancy $D^- > 0$ for $E(2^k)$ ($k \ge 3$).
- **What remains a provisional novelty claim:** All Phase 24 nonnormality results for $E(2^k)$ and $E_+(2^k)$ ($k \ge 3$). Absence of a search hit does not prove priority.

### Entry 7.2 — Captain Sude (Sept 2026) on Generalized Power-Lambert Disjunctivity and Nonnormality
- **Exact theorem (`PowerLambert.powerLambert_full_theorem`):** For every integer base $b \ge 2$ and every integer power $r \ge 2$, the power-Lambert series $\sum_{m=1}^{\infty} (b^{m^r} - 1)^{-1}$ is base-$b$ disjunctive, every finite base-$b$ word has a positive limiting frequency (as recorded in `notes/phase13/erdos-borwein.md` from `PowerLambert/Results.lean`), and the number is **nonnormal** in base $b$. A separate repo (`reciprocal-Fermat-constant-Nonnormal`, 8 Sept 2026) proves nonnormality of the reciprocal Fermat constant.
- **Author and date:** Captain Sude, 13 September 2026 (and 8 September 2026).
- **Primary-source citation / link:** [`CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality`](https://github.com/CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality/blob/fe33be210446c6c0b127ca7757fc8f1182c5b541/lean/PowerLambert/Results.lean) (commit `fe33be210446c6c0b127ca7757fc8f1182c5b541`); [`CaptainSude/reciprocal-Fermat-constant-Nonnormal`](https://github.com/CaptainSude/reciprocal-Fermat-constant-Nonnormal). Reading label: **[R]** (statement checked in `notes/phase13/erdos-borwein.md` and `notes/phase18/sources.md` §7).
- **Relevant hypotheses:** Strictly requires nonlinear exponent $r \ge 2$ in $b^{m^r} - 1$ (so the underlying series has sparse $m^r$ support, where blocks are separated by growing gaps, unlike the linear-exponent dense series $r = 1$).
- **What this repository reproves:** None.
- **What this repository extends:** Crucially, the Erdős–Borwein family $E(q) = \sum (q^m - 1)^{-1}$ has $r = 1$, which is **outside** the hypothesis $r \ge 2$ of `PowerLambert`. For $r = 1$, every coefficient $\tau(n)$ is positive (full density $1$ of nonzero terms), so sparsity arguments fail and must be replaced by digit-mass transfer (`NormalityChecker/DigitMassTransfer.lean`).
- **What remains a provisional novelty claim:** Nonnormality of the dense linear-exponent ($r = 1$) Lambert series $E(2^k)$ and $E_+(2^k)$ for $k \ge 3$, as well as the base-$b$ $\tau_b$ and unitary families. Absence of a search hit does not prove priority.

### Entry 7.3 — Related 2026 Contemporaries on $E(2)$ (Campbell 2026; Lambrinoudis 2026)
- **Exact theorem:**
  - **John M. Campbell (22 May 2026):** Resolves Crandall's 2012 problem by proving that the binary word `11` occurs infinitely often in $E(2)$, using AGP ($\delta = 1/4$) to force $\tau(n+2) = 6$ with high $2$-adic divisibility at nearby sites (no lower frequency bound).
  - **Costa Lambrinoudis (2026):** Reports an AI-assisted, Lean-formalized proof that $E(2)$ is not a quadratic irrational (and related linear-independence results for Lambert series).
- **Author and date:** John M. Campbell (22 May 2026); Costa Lambrinoudis (2026).
- **Primary-source citation / link:** J. M. Campbell, *On the binary digits of the Erdős–Borwein constant*, [arXiv:2605.24160](https://arxiv.org/abs/2605.24160) **[R]** (audited in `notes/phase13/erdos-borwein.md`); C. Lambrinoudis (2026) **[S]** (cited via web search summaries; primary text not read).
- **Relevant hypotheses:** Both concern $E(2)$ ($k = 1$) only (occurrence of `11`; non-quadraticity).
- **What this repository reproves / extends:** Disjoint from Phase 24's digit-mass nonnormality of $E(2^k)$ ($k \ge 3$).
- **What remains a provisional novelty claim:** Same as Entries 7.1–7.2.

---

## Topic 8: Existing Results on Disjunctivity, Simple Nonnormality, or Nonnormality of $E(2^k)$ ($k \ge 3$) or $E_+(2^k)$

### Search Record and Assessment
- **Queries run (28 November 2026):** Web searches targeting `"Erdos-Borwein" "2^k" OR "1/(2^{kn}-1)" OR "1/(q^n-1)" OR "1/(q^n+1)" normal OR nonnormal OR "simply normal" OR disjunctive`, `"Bailey" "Borwein" "normal" "Erdos-Borwein" OR "1/(2^n - 1)" OR "Lambert series"`, plus cross-checks against the repository's pinned scans of `Mira-Cult/math` and `CaptainSude` GitHub repositories (`notes/phase18/sources.md`, `notes/phase20/literature.md`).
- **What was located:**
  1. **Irrationality & non-Liouville property** for $E(q)$ ($q \ge 2$) and $E_+(q)$ ($q \ge 2$): Erdős (1948), P. B. Borwein (1991, 1992), Vandehey (2012).
  2. **Disjunctivity & positive lower word density for $E(2)$ ($k = 1$):** Campbell (2026, `11` i.o.), Captain Sude (Sept 2026, Lean disjunctivity with $N\exp(-70000(\log\log N)^3)$), Mira Cult (Nov 2026, short-window positive lower word density on $N^a \le H \le N$, $7/12 < a \le 1$).
  3. **Nonnormality + disjunctivity for nonlinear power-Lambert series $\sum(b^{m^r}-1)^{-1}$ ($r \ge 2$):** Captain Sude (Sept 2026, `fe33be21`).
  4. **Nonnormality + disjunctivity for sparse character Lambert series $L_\chi = \sum \chi(m)/(2^m - 1)$:** BBCP (2004, Thm 9.4 for $\theta_3(1/2)^2 = 1 + 4 L_{\chi_4}$, one-bit count) and this repository (`CC-46`, `CC-48`, short-window all-word counts and discrepancy gap).
- **What was NOT located in the searches conducted:**
  - No published paper, preprint, or public Lean repository was located that proves simple nonnormality, non-$2$-normality, nonnormality, or positive lower discrepancy $D^- > 0$ for $E(2^k) = \sum (2^{km} - 1)^{-1}$ ($k \ge 3$) or $E_+(2^k) = \sum (2^{km} + 1)^{-1}$ ($k \ge 3$).
  - No published proof of disjunctivity of $E(2^k)$ ($k \ge 3$) or $E_+(2^k)$ ($k \ge 3$) was located either (note that our Phase 24 results prove nonnormality, not disjunctivity; whether $E(2^k)$ ($k \ge 3$) is disjunctive in base $2$ remains open).
- **Provisional novelty classification:** The kernel-verified simple nonnormality of $E(2^k)$ ($k \ge 3$) in every base $2^j$ (`DigitMassTransfer.lean`, commit `04969b91`), the sharp constant $C_{\mathrm{true}} \in [1.339103, 1.339116]$, the signed transition-count and 4-state transducer nonnormality of $E_+(2^k)$ ($k \ge 3$), and the base-$b$ Senge–Straus barrier remain **provisional novelty claims**. Because standard web search does not exhaust MathSciNet, zbMATH, conference proceedings, or unpublished preprints, absence of a hit does **not** prove priority.

---

## Topic 9: Computable Badly Approximable (Absolutely) Normal Numbers (Prior-Art Input for Track F2)

Because Phase 25 Track F2 investigates explicit/computable badly approximable normal numbers, we record the exact separation between **(A) non-constructive existence**, **(B) computable normal / absolutely normal constructions (without bad approximability)**, and **(C) computable badly approximable normal numbers**.

### Entry 9.1 — Non-Constructive Existence via Fourier Decay on Continued-Fraction Cantor Sets (Kaufman 1980, 1981; Queffélec–Ramaré 2003; Jordan–Sahlsten)
- **Exact theorem:**
  - **Kaufman (1980):** For the Cantor set $F_N$ of badly approximable numbers whose continued-fraction partial quotients lie in $\{1, \dots, N\}$, whenever $\dim_H(F_N) > 2/3$ (in particular $N \ge 3$), $F_N$ supports a probability measure $\mu$ whose Fourier–Stieltjes transform satisfies polynomial decay $|\widehat{\mu}(u)| \ll |u|^{-\eta}$ ($\eta > 0$). By the Davenport–Erdős–LeVeque criterion, $\mu$-almost every $x \in F_N$ is **absolutely normal** (normal in every integer base $b \ge 2$). Thus badly approximable absolutely normal numbers exist (with positive Fourier dimension).
  - **Kaufman (1981):** Constructs Rajchman measures with polynomial Fourier decay on Jarník–Besicovitch well-approximable sets $\|nx\| < n^{-1-\alpha}$.
  - **Queffélec–Ramaré (2003):** Lowers Kaufman's dimension threshold on $F_N$ from $2/3$ to $1/2$, extending polynomial Fourier decay (and hence existence of absolutely normal numbers) to $F_2$ (partial quotients in $\{1, 2\}$, which has $\dim_H(F_2) \approx 0.53128 > 1/2$).
  - **Jordan–Sahlsten (2016):** Establishes polynomial Fourier decay for Gibbs measures of the Gauss map with Hausdorff dimension $> 1/2$ **[S]**.
- **Author and date:** Robert Kaufman (1980, 1981); Martine Queffélec and Olivier Ramaré (2003); Thomas Jordan and Tuomas Sahlsten (2016).
- **Primary-source citation / link:**
  - R. Kaufman, *Continued fractions and Fourier transforms*, Mathematika **27** (1980), no. 2, 262–267 **[A/S]**; *On the theorem of Jarník and Besicovitch*, Acta Arithmetica **39** (1981), no. 3, 265–267 **[A/S]**.
  - M. Queffélec and O. Ramaré, *Analyse de Fourier des fractions continues à quotients restreints*, L'Enseignement Mathématique **49** (2003), 335–356 **[A/S]**.
- **Relevant hypotheses:** Partial quotients restricted to a finite alphabet $S \subset \mathbb{N}$ with $\dim_H(F_S) > 1/2$ (for Queffélec–Ramaré).
- **What this repository reproves / extends (relevance to Track F2):** Existence of badly approximable **absolutely normal** numbers is **already classical** (1980/2003). Track F2 must **never** claim novelty for mere existence; any contribution must be **computability / explicit construction / quantitative discrepancy** (or Lean formalization).
- **What remains a provisional novelty claim:** See Entry 9.4 below.

### Entry 9.2 — Existence in Arbitrary Continued-Fraction Cantor Sets (Hochman–Shmerkin 2015)
- **Exact theorem:** Every set of $S$-badly approximable numbers (continued fraction partial quotients in any finite subset $S \subset \mathbb{N}$ with $|S| \ge 2$, regardless of how small $\dim_H(F_S)$ is — e.g., $S = \{1, 100\}$) contains numbers normal to every integer base $b \ge 2$ (equidistribution from fractal measures via scenery flows and CP-chains).
- **Author and date:** Michael Hochman and Pablo Shmerkin, 2015.
- **Primary-source citation / link:** M. Hochman and P. Shmerkin, *Equidistribution from fractal measures*, Inventiones Mathematicae **202** (2015), 427–479, [arXiv:1302.5792](https://arxiv.org/abs/1302.5792). Reading label: **[A/S]** (verified via search summary).
- **Relevant hypotheses:** Any finite alphabet $S \subset \mathbb{N}$ with $|S| \ge 2$; non-constructive (measure-theoretic equidistribution on fractal measures).
- **What this repository reproves / extends (relevance to Track F2):** Removes the $\dim_H > 1/2$ barrier for *existence* of badly approximable absolutely normal numbers, but does not produce a computable example or discrepancy rate.
- **What remains a provisional novelty claim:** Explicit/computable realization (see Entry 9.4).

### Entry 9.3 — Computable Absolutely Normal Numbers, Discrepancy, Liouville and CF-Normal Constructions (Korobov 1955; Levin 1999; Bugeaud 2002, 2012; Becher–Heiber–Slaman 2013, 2015; Becher–Bugeaud–Slaman 2015; Scheerer 2015, 2017; Aistleitner–Becher–Scheerer–Slaman 2017; Madritsch–Scheerer–Tichy)
- **Exact theorems:**
  - **N. M. Korobov (1955):** *Numbers with bounded quotient and their applications to questions of Diophantine approximation*, Izv. Akad. Nauk SSSR Ser. Mat. **19** (1955), 361–380 **[S]** — applies bounded-partial-quotient (badly approximable) numbers to Diophantine approximation and low-discrepancy sequences (note: studies $(n\alpha \bmod 1)$ / Korobov nets, not base-$b$ normality of badly approximable numbers).
  - **M. B. Levin (1999):** *On the discrepancy estimate of normal numbers*, Acta Arith. **88** (1999), 99–111, [DOI: 10.4064/aa-88-2-99-111](https://doi.org/10.4064/aa-88-2-99-111) **[S]** — explicit base-$b$ normal numbers with extreme discrepancy $D_N = O((\log N)^2 / N)$ (recently shown sharp by Hofer–Larcher); not badly approximable.
  - **Y. Bugeaud (2002, 2012):** Existence of absolutely normal Liouville numbers (*C. R. Math.* **335**, 2002) and synthesis of Diophantine approximation vs. normality (*Distribution Modulo One and Diophantine Approximation*, CUP 2012, [DOI: 10.1017/CBO9781139017732](https://doi.org/10.1017/CBO9781139017732)) **[S]**.
  - **V. Becher, P. A. Heiber, T. A. Slaman (2013):** *A polynomial-time algorithm for computing absolutely normal numbers*, Information and Computation **232** (2013), 1–9 **[A/S]** — computes an absolutely normal number in slightly above quadratic time; does not control continued-fraction partial quotients.
  - **V. Becher, P. A. Heiber, T. A. Slaman (2015):** *A computable absolutely normal Liouville number*, Math. Comp. **84** (2015), 2939–2952, [DOI: 10.1090/mcom/2964](https://doi.org/10.1090/mcom/2964) **[A/S]** — opposite Diophantine extreme (Liouville, $\mu = \infty$, unbounded partial quotients).
  - **V. Becher, Y. Bugeaud, T. A. Slaman (2015/2016):** *The irrationality exponents of computable numbers*, Proc. Amer. Math. Soc. **144** (2016), 1509–1521 **[A/S]** — characterizes irrationality exponents of computable reals.
  - **A.-M. Scheerer (2015, 2017):** *Computable absolutely normal numbers and discrepancies*, [arXiv:1511.03582](https://arxiv.org/abs/1511.03582) (2015) **[A/S]**; *Computable absolutely normal and continued fraction normal numbers* (2017) **[S]** — constructs computable numbers that are simultaneously absolutely normal and **continued-fraction normal** (Gauss–Kuzmin distribution, which implies unbounded partial quotients, hence **not** badly approximable).
  - **C. Aistleitner, V. Becher, A.-M. Scheerer, T. A. Slaman (2017):** *On the construction of absolutely normal numbers*, Acta Arith. **180** (2017), 333–346, [DOI: 10.4064/aa170213-5-8](https://doi.org/10.4064/aa170213-5-8) **[A/S]** — computable absolutely normal numbers with discrepancy $O(N^{-1/2})$ in every base $b \ge 2$.
  - **M. G. Madritsch, A.-M. Scheerer, R. F. Tichy:** Computable absolutely Pisot-normal numbers **[A/S]**.
  - **S. Kristensen; D. Badziahin, Y. Bugeaud, M. Einsiedler, D. Kleinbock; A. Pollington, S. Velani; D. Simmons, B. Weiss:** Metric theory, Schmidt games, Hausdorff dimension, and fractal intersections for badly approximable numbers/vectors (non-constructive) **[S]**.
- **Author and date:** Various (1955–2020s), as cited above.
- **Relevant hypotheses:** Computable algorithms (Sierpiński / Turing / Schmidt / Becher–Heiber–Slaman nested-interval selection) use Lebesgue-measure or Gauss-measure large deviations on full intervals, which naturally yield typical (unbounded) partial quotients or Liouville behavior rather than staying inside a measure-zero Cantor set $F_N$.
- **What this repository reproves / extends (guidance for Track F2):**
  - If Track F2 constructs a **computable badly approximable (base-$b$ or absolutely) normal number**, the key mathematical obstruction relative to Becher–Heiber–Slaman / Scheerer is that Lebesgue measure gives $F_N$ measure $0$: one must replace Lebesgue measure in a Turing/Becher–Heiber–Slaman nested-interval algorithm by an **effectively computable** Rajchman measure $\mu$ supported on $F_N$ with explicit Fourier decay (an effectivized Kaufman 1980 or Queffélec–Ramaré 2003 measure, where the effective Davenport–Erdős–LeVeque / Weyl exponential-sum variance is computable on cylinder intervals of $F_N$).
- **What remains a provisional novelty claim:** In the web searches conducted, **no published construction of a computable badly approximable (absolutely) normal number** was located, though the non-constructive existence (Kaufman 1980; Queffélec–Ramaré 2003; Hochman–Shmerkin 2015) and the computable-normality framework (Becher–Heiber–Slaman 2013, 2015; Scheerer 2015, 2017; ABSS 2017) are both extensively developed. **Warning for Track F2:** before claiming any priority for a computable badly approximable normal number, a targeted search of MathSciNet/zbMATH for papers by Verónica Becher, Theodore Slaman, Yann Bugeaud, Adrian-Maria Scheerer, Manfred Madritsch, Mordechay Levin, Simon Kristensen, and Santiago Figueira (2015–2026) is mandatory; absence of a hit in web search does not prove priority.

---

## Consolidated Novelty & Provenance Ledger for Candidate Paper XIV

| Claim in Paper XIV / Phase 24 | Evidence Label | Closest Prior Art | Provisional Provenance Assessment |
| --- | --- | --- | --- |
| Kummer carry identity, subadditivity/submultiplicativity of $s_b, w_b$, Wintner convolution limit | Kernel-verified | Kummer (1852); Wintner-type mean values | **Classical** (no novelty claimed; Lean 4 formalization is ours) |
| Exact prefix decomposition & $O(\log N)$ carry-tail transfer (`Theorem 2.1–2.2`) | Kernel-verified (identity & prefix bound) / Paper proof | Standard truncation + Kummer | **Elementary assembly** (counterexample to "+1" tail bound is ours) |
| For all $k \ge 3$, $\limsup f_1(E(2^k); 2) \le 29/(20k)$, $D^- \ge 1/120$, simply nonnormal in every base $2^j$ | **Kernel-verified** (`DigitMassTransfer.lean`, commit `04969b91`) | Erdős (1948), Borwein (1991, 1992) for irrationality; Captain Sude (2026) for $r \ge 2$ power-Lambert | **Provisional novelty claim** (not located in searches conducted; absence of hit $\ne$ proof of priority) |
| Exact mean $C_{\mathrm{true}} = \lim X^{-1}\sum s_2(\tau(n)) \in [1.339103, 1.339116]$, majorant $C \in [1.4035953, 1.4035958]$, $D^-(E(2^k); 2) \to 1$ | Paper proof + Finite certificate | Independent-exponent Kubilius models (classical) | **Provisional novelty claim** for the constants and application to $E(2^k)$ |
| Non-dyadic Senge–Straus barrier & $\tau_r$ base-$b$ multiplicative-dependence dichotomy | Paper proof + External input (Senge–Straus 1973; Stewart 1980) | Senge–Straus (1973); Stewart (1980) | **Provisional new application / barrier** built directly on Senge–Straus |
| Signed transition transfer ($E_+(2^k)$ for $k \ge 4$, cubic $L_\pm(2^k)$) | Lean-supported paper proof + Finite certificate | Booth (1951); Reitwiesner (1960); Heuberger–Prodinger | **Provisional novelty claim** (uses Reitwiesner NAF minimality as external input) |
| 4-state free-boundary transducer $A_L = \frac{1}{3} - \frac{7-(-1/2)^{L-1}}{18L}$ & nonnormality of $E_+(8)$ ($D^- \ge 2.34 \times 10^{-7}$) | Paper proof + Finite certificate + External input (Reitwiesner) | Classical NAF mean density $1/3$ & fixed-boundary $\ell/3 + 2/9$ (Reitwiesner; Bosma; Heuberger–Prodinger) | Limit $1/3$ is **classical**; exact free-boundary $A_L$ and discrepancy floor for $E_+(8)$ are **provisional novelty claims** |
| Exact carry-density thresholds for $E(4)$ and $E^*(4)$ | Paper proof (+ Wirsing 1967 for direct base-4 obstruction; Conditional for $\mathcal{C}$) | Bailey–Crandall (2002) & Crandall (2012) on $E(2)$ | **Reformulations / obstructions**; $E(2), E(4), E^*(4), E_+(2), E_+(4)$ remain **Open** |
