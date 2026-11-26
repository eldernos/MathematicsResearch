# Changes from Paper VII, version 1.0

Version 2.0 (candidate draft of 26 November 2026), *Synthetic Arithmetic Expansions and Prescribed Discrepancy*, is intended to supersede [version 1.0](../07-synthetic-expansions/), released in `manuscripts-v2.0.0` and recorded on alphaXiv. Nothing in the version 1.0 directory, its release tag or its recorded PDF digest is changed. Older statement numbers below refer to the built version 1.0 PDF; newer numbers refer to a scratch build of this draft (48 pages after the revision at the end of this file). The full evidence map is [VERIFICATION.md](VERIFICATION.md) and the literature comparison is [LEDGER.md](LEDGER.md).

**What did not change.** Every verified theorem of version 1.0 is kept with its statement, proof and evidence label: Theorems A, B, C, E; Lemmas 2.1–2.5 and the quoted Theorem 2.6; Theorem 3.1 with its finite certificate; Section 4 (4.1–4.7); Sections 5 and 6 (5.1–5.3, 6.1–6.5); the quadratic-image theorem 7.1, Corollary 7.2 and its proof 7.4–7.8; Section 8 (8.1–8.5). Their numbers are unchanged, because the new numbered statements of Sections 2, 4 and 7 were placed after the old ones. Registry identifiers of version 1.0 (SY-01, SY-02, SY-03, SY-06, SY-07, SY-11, SY-13, SY-16, SY-19, OP-08, OP-09, OP-14) keep their meaning.

## Statement correspondence

| Version 1.0 | Version 2.0 | Change |
| --- | --- | --- |
| Abstract | Abstract | Rewritten for the new results; the infinite-sum theorem is kept in one sentence. |
| §1, Theorem D (total degree at most two, $d\ge3$) | §1, Theorem D | **Upgraded.** Total degree $r\le d-1$ in distinct orders, every $d\ge2$; for one order the rates $(\log\log N)^{-d/(d-1)}$ ($r\ge2$) and $N^{-\eta}$ ($r=1$); $D_N(\xi^2)\ll(\log\log N)^{-3/2}$; $C(2,3,1,4)$, its square and cube jointly normal; $C(b,p,s,d)$ not algebraic of degree less than $d$. |
| — | §1, Theorem F | **New.** All-prime polynomial normality: a universal Liouville example, polynomial schedules, finite irrationality exponent $\lambda$ (degree $\le r$) and $p$ (all degrees). |
| — | §1, Theorem G | **New.** The boundary $d=r$: tight depth, the denominator-only barrier, retirement of the integer part at $d=2$, the cubic obstruction. |
| §1, relation to earlier work | §1 | Adds the comparison with Manai (arXiv:2508.09319), Titchmarsh's test, Hooley, Landau, Bambah–Chowla, Selberg–Delange, Wooley and Deshouillers–Hennecart–Landreau; states that no priority is claimed for normal numbers with a prescribed irrationality exponent as such; relates Theorem F(iv) to Paper I v2.0, Theorem A and Mira Cult's S08. |
| §1, evidence labels | §1 | Adds the label *Finite certificate* and states that Lean-supported labels cover only the named finite steps. |
| — | §2.1, Lemma 2.7, Corollary 2.8, Lemma 2.9 | **New.** A short-orbit estimate on prime-power moduli uniform in the base (with a sharpness example), the splitting of a coprime modulus, and a bound for the largest auxiliary prime. |
| §4, Remark after Theorem 4.7 ("no rate outside $d\ge s+2$") | Remark 4.8 | **Updated.** A power saving holds for every $s\ge1$, $d\ge2$ (the case $r=1$ of Theorem 7.21), with a very small exponent; Theorem 4.7 remains the better bound for $d\ge s+2$. The unexecuted suggestion to apply Vandehey's Corollary 1.2 is replaced by this proof. |
| §7, title "Quadratic images" | §7, "Polynomial images below the schedule degree" | Retitled; §§7.1–7.4 keep the quadratic proof as the model case. |
| Remark 7.9 (scope; "normality of $\xi^3$ is open") | Remark 7.9 | **Updated.** Explains why one primitive family fails for $r\ge3$ and points to the new subsections; $\xi^3$ is located on the boundary $d=r$. |
| — | §7.5, Lemmas 7.10–7.11 | **New.** Freezing in degree $r$; reduction of normality to null zero sets of $M_r$ when $d\ge r+1$. |
| — | §7.6, Lemmas 7.12–7.16, Proposition 7.17 ($H\ge6$) | **New.** Dominant anchors and centres; the jump $r!p^{sH}$ at isolated centres (Lean `truncMass_jump_of_isolated`); Titchmarsh's $q$-th derivative test (external input); derivatives of $f_B$ and $\Phi_q$ (Lean degree and leading coefficient); exponent margins $\sigma_2=1/12$, $\sigma_r=1/(r(2^{r+1}-2))$; averaged isolation on unions of intervals (Lean peeling lemma and divisor bound); the counterexample to uniform isolation at $p=3$, $d=4$, $r=3$. |
| — | §7.7, Theorem 7.18 | **New.** Small-ball estimate $\lvert\{M_r\equiv w\bmod p^L\}\rvert\ll(\log L)^{-d/(d-1)}$ for all $r,d\ge2$. |
| — | §7.8, Theorems 7.19–7.20 | **New.** Normality in every degree below $d$ (one order), and for several distinct orders (lexicographic target, bounded anchors with sequentially chosen numerators, $L^1$ localization). |
| — | §7.9, Theorem 7.21, Corollary 7.22 | **New.** Effective rates for every $d\ge r+1$; the rate for $\xi^2$ and for $C(2,3,1,4)^3$. |
| — | §9 (Lemma 9.1 – Remark 9.12) | **New section.** Pole dominance (Lean lower bound); the universal all-prime Liouville theorem with exact denominators and rate; general protected poles; the lcm bound and denser schedules; several generators (remark, not used); all-prime polynomial schedules for every $d\ge r+1$; truncation separation; ratio-one schedules with **open** finiteness of the exponent; geometric schedules with $\mu=\lambda$; the Stoneham schedule with $\mu=p$; the quasi-polynomial schedule as a remark without proof, its exponent **open**. |
| — | §10 (Proposition 10.1 – Remark 10.11) | **New section.** Depth tight in density at $d\le r$; denominators do not determine digits; no uniform cancellation below $\log_b(\epsilon q)$; level filtration; a self-contained sparse integer transfer; absorption of the integer part at $d=r=2$; integer dilation and fixed-depth retirement; runs after retirement (Hooley); fractional jumps ($p\equiv3\bmod4$); the cubic boundary (conditional on density zero, which the DHL model predicts false); finite measurements (evidence only). |
| §9, Questions 9.1–9.3 | §11, Questions 11.1–11.6 | **Updated.** Q1: the rate for $\xi^2$ is now Theorem D; **normality of $\xi^3$ stays open**, joined by $C(b,p,s,2)^2$ and the weaker $\limsup D_N<1$ and $D_N\not\to1$. Q2: unchanged in substance (degree less than $d=3$ excluded). Q3: now asks for the true order of the nonlinear rates and whether a power of $\log N$ or of $N$ holds. New: finiteness of $\mu(W_H)$ and of the quasi-polynomial exponent (**open**); how early auxiliary primes can appear; rates for several orders. |
| §10, Formal verification | §12 | Adds the commit `347ec3f` for `ProtectedPole` and `PowerSumPeeling`, the exact scope of the new Lean declarations, the new scripts, and the finite certificate of Proposition 7.17. |
| §11, Use of AI tools | §13 | Adds that the new material rests on source arguments with one cross-provider model review each, repaired and re-read, and that the assembled manuscript has not been reviewed as a whole. |

## Mathematical additions, itemized

1. **Uniform short orbits** (Lemma 2.7): $\lvert\sum_{m<M}e(cG^m/p^e)\rvert\le9M_0^{1-\delta}$ uniformly in the principal unit $G$, under $A(G)\le\frac3{16}\log_pM_0-1$; necessity of such a bound (sharpness example). Corollary 2.8 and Lemma 2.9 transfer it to $b^jy$ with a growing coprime modulus.
2. **Every degree below the schedule degree** (Theorem 7.19): GF-11, previously a repository note, now proved in the manuscript; the qualitative statement is deduced from the small-ball theorem.
3. **Several orders** (Theorem 7.20): GF-14 item (4).
4. **Uniform isolation fails** (Proposition 7.17) and **averaged isolation** (Lemma 7.16).
5. **Small balls** (Theorem 7.18): GF-14 item (2), for all $r,d\ge2$.
6. **Effective rates for every $d\ge r+1$** (Theorem 7.21): removes the hypothesis $d>r(s+1)$ of the Phase 21 rate (GF-14) by Lemma 2.7.
7. **Universal all-prime Liouville polynomial normality** (Theorem 9.2, GF-10) and general protected poles (Theorem 9.3); denser schedules (Corollary 9.5, GF-15 part 1).
8. **All-prime polynomial schedules for every $d\ge r+1$** (Theorem 9.7), extending GF-15 part 2 from $d>r(s+1)$ and allowing auxiliary support controlled only through $\operatorname{ord}_{\Lambda_K^r}b$.
9. **Finite irrationality exponents** (Theorems 9.10 and 9.11): degree $\le r$ with $\mu=\lambda$ on geometric schedules; all degrees with $\mu=p$ on the Stoneham schedule.
10. **Limitations at $d=r$** (Section 10): Proposition 10.1 (GF-14 item (3)), Lemmas 10.2–10.3, Proposition 10.4, Lemma 10.5, Theorem 10.6, Lemma 10.7, Corollary 10.8, Theorem 10.9, Proposition 10.10.

## Upgraded theorems

- Theorem D: from total degree $\le2$ with $d\ge3$ and no rate, to total degree $<d$ for every $d\ge2$, with rates for one order.
- Remark 4.8: from "no rate outside $d\ge s+2$" to a proved power saving for every $d\ge2$.
- Question 1 of v1.0, first half ("give an explicit rate for $D_N(\xi^2;2)$"): answered by Corollary 7.22, $D_N(\xi^2)\ll(\log\log N)^{-3/2}$. The rate is weak and probably far from the truth.

## Open problems, updated

- **Kept open:** normality of $\xi^3$ (v1.0 Question 1, second half), now with the explanation of Section 10; normality of $C(b,p,s,2)^2$; even $\limsup D_N<1$ for these numbers; transcendence and Liouville status of $\xi$.
- **Newly recorded as open:** finiteness of the irrationality exponent and non-Liouville status of the polynomial-schedule series $W_H$ (Theorem 9.7, Proposition 9.9) and of the quasi-polynomial series (Remark 9.12); a power of $\log N$ or of $N$ in the nonlinear rates; rates for several orders; earlier introduction of auxiliary primes and a geometric construction with a new prime at every index; density-one short fractional runs at $d=2$ and anything for $p\equiv1\pmod4$; whether sums of three positive cubes have density zero (expected false).

## Editorial

- Byline `Version 2.0 (preprint draft) · 26 November 2026`; the release label is set locally to "candidate draft, not yet released", because the shared preamble names the release of version 1.0.
- Section titles containing mathematics use `\texorpdfstring`.
- No process language from the source notes is carried into the manuscript.
- Not yet produced for this directory: `paper.pdf`, `metadata.toml`, `submission/`, and a `papers.toml` and `manifest.toml` entry. These are release steps for the owner. The Phase 22 results are now registered as [GF-24](../../docs/results.md#gf-24) (the equality boundary, Section 10) and [GF-25](../../docs/results.md#gf-25) (Lemma 2.7, Theorem 7.21, Theorems 9.7, 9.10 and 9.11); `metadata.toml` should list them together with SY-01, SY-02, SY-03, SY-06, SY-07, SY-11, SY-13, SY-16, SY-19, OP-08, OP-09, OP-14, GF-10, GF-11, GF-14 and GF-15. The finite Lean cores listed under GF-24 are in `NormalityChecker/Phase22Cores.lean`, which is not yet committed; the manuscript does not link it (see [VERIFICATION.md](VERIFICATION.md)).

## Revision after cross-model review (26 November 2026)

The independent model review [`paper-vii-v2-review.md`](../../notes/phase22/reviews/paper-vii-v2-review.md) (ACCEPT AFTER REVISION; 0 Critical, 6 Major, 12 Minor) was answered in full. Cross-model review is not independent human peer review. Statement numbers are unchanged; the draft now has 48 pages.

**Major findings.**

- **M1.** Theorem 7.20, reduction: the freezing threshold is now $J\ge\max(L,\lceil L/s_1+L/d\rceil)$, and the proof says why monomials outside the top set vanish modulo $p^L$: they carry $p^{(S^*-s\cdot\nu)J}$ with $S^*-s\cdot\nu\ge1$.
- **M2.** Proposition 10.4 and §10.3: removed the spurious factor $b^n$; the identities now read $\{R_n(Z_H)\}=\{p^{sH}R_n(C^r)\}$ with the paper's shifted prefix $R_n$.
- **M3.** Abstract: the polynomial-schedule examples are stated for degree less than $d$, and the finite-exponent examples for degree $r<\lambda$ with $p>(r+1)!$.
- **M4.** Lemma 7.16 uses $\alpha=\min(1,v'/H)$, so Lemma 7.15 applies when $H'>H$; Theorem 7.18 bounds each of the two error terms by $xH^{r-1}p^H/(8A)$, so that $(1-\tfrac18-\tfrac14-\tfrac18)/A=1/(2A)$.
- **M5.** Evidence labels: §1 now introduces *finite certificate* as an additional label for statements with a certified finite part, and Proposition 7.17 carries *Paper proof; finite certificate*; Theorem 7.18 is *Lean-supported paper proof* (via Lemmas 7.12 and 7.16); §12 separates the paper proofs (7.1, 7.2, 7.21, 7.22) from the Lean-supported paper proofs (7.18–7.20); `VERIFICATION.md` records Paper I v2.0, Lemmas 2.2–2.4, as paper proofs there.
- **M6.** Proposition 7.17 is stated for $H\ge6$, where its target interval is nonempty and which matches the repository certificate (the interval is empty for $H=4,5$); §12 no longer cites an uncommitted computation; §13 is reduced to the disclosure that the proofs were checked only by AI models, that cross-model review is not independent human peer review, and that no human specialist has read the new proofs. The two Phase 22 scripts and `Phase22Cores.lean` must still be committed before release.

**Minor findings.**

1. Lemma 2.9: $\pi(x)-\omega(pb)-x^{2/3}\log_2b$ in place of $\pi(x)-2-\cdots$, with $\omega(pb)\le1+\log_2b$; the bound on $A(G)$ uses $\log(\operatorname{ord}_\Lambda b+3)$.
2. Theorem 10.6: $L=\max(1,\lceil\cdots\rceil)$; the cases $\rho\ge1$ and $L>N$ are shown to be trivial, so Lemma 10.5 is applied only with $\epsilon\in(0,1)$ and $1\le L\le N$.
3. Sharpness example after Lemma 2.7: restricted to $p^a\ge10$.
4. Corollary 2.8: requires $\gcd(M',pb)=1$; an empty maximum is $0$.
5. §7.6: "relevant" is defined directly; the box endpoints are renamed $\beta_j$, so that $a_j$ denotes only numerators.
6. §7.5: the mass $M_r(u)$ is defined for every real $u$, which removes boundary effects near $1$ and $p^d$ in Lemma 7.12.
7. Lemma 7.16: dropping $p\nmid m'$ is described as giving an upper bound (the incorrect factor $p/(p-1)$ is removed); pieces are cut where $f_B^{(q)}$ changes sign.
8. Theorem 7.21: the discarded failed runs are $O(N(\log L)^{-d/(d-1)})$ shifts.
9. Theorem 9.3: the Liouville step explains $\log\Lambda_k<\pi_k\log b=o(n_k)$ in the squarefree case, with the empty-maximum convention.
10. Lemma 10.3: stated for nonzero $h$.
11. Theorem G(iv) attributes the conditional statement to the sparse-series transfer; Proposition 10.1 absorbs $3\le L\le v_p(A)+2$ into $C_P$; §10.3 writes $\gg_{\epsilon,p,s}(\log N)^{s/2}$.
12. `S08` is replaced by a citation of Mira Cult's note; the unused macro `\Mr` is removed; the unverified DOI of Roth (1955) is removed; `PaperI` and `PaperIII` use the author field `Anderson, Christopher`, like the other companion entries.

**Length and a possible split.** The draft has 48 pages against 24 for version 1.0. The referee considers a single paper defensible. If the owner prefers to split before release, the referee recommends moving **§9 alone** (all-prime polynomial normality and irrationality exponents) to a companion Paper XII and keeping §10 with §7, because Section 10 reuses Lemma 7.10 and Theorem 7.18 and treats the boundary case left by Theorem D. This draft keeps one manuscript and leaves the decision to the owner.
