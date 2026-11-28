# Claim-to-source novelty ledger: Complete Reciprocal Discrepancy Spectra in Integer Radices (v1.0, candidate draft)

A search cannot prove novelty. "Not located in the sources examined" means only that the sources listed here, read as described, did not contain the statement. A failed search is recorded as a failed search and never as evidence of novelty. Every written proof and every comparison below has been checked only by AI models. **Cross-model review is not independent human peer review.** No human specialist has read the proofs.

Reading labels: **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[M]** our own deduction; **[U]** unverified.

## Scope

This ledger covers Candidate Paper XV (unreleased candidate draft). It assembles the Phase 25 Track E reciprocal discrepancy spectrum and partition-reciprocal results registered as `GF-45` (`notes/phase25/partitions-and-reciprocals.md`, committed at `c06c97dd7d942bdf46d727aa58309869af88d5e7`, reviewed in `notes/phase25/reviews/track-e-review.md` and independently audited in Phase 26 Stage 0.2 Audit III `notes/phase26/reviews/audit-3-gf45.md`: 0 Critical, 0 Major, passes Paper XV gate; neither is human peer review), together with the Toeplitz determinant-to-uniformity transfer and compound-symmetric control of Phase 26 Track A (`notes/phase26/toeplitz-determinants-and-uniformity.md`, Sections 1, 2, and 4) and the open non-zero Dirac rigidity question of Phase 26 Track E (`notes/phase26/constructive-normality-and-reciprocal-spectra.md`, Section E1.3 / Conjecture E1.C). No result in this manuscript is kernel-verified in Lean 4. Every priority judgment remains provisional pending independent human specialist literature review.

**Benchmark scope.** No statement in this draft changes the status of any entry of the repository's fixed 50-constant benchmark roster (`BC-01`…`BC-50`). Normality, simple normality, $D^+ < 1$, and $K_b$-membership of Mahler's $m$-ary partition constants $X_{b,m}$ and Euler's partition constant $P_b = 1/E_b$ remain **Open**. The cut-and-fold witnesses of Theorem A are built from rational ratios $(1 - b^{-m})/(1 - b^{-q})$ and lie outside the single-factor product family `BF-10`; attainment of intermediate $\alpha \in (0, 1)$ within `BF-10` remains **Open** (Question 7.4).

## Bibliography verification

| Key | Status |
| --- | --- |
| `KN` | L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences* (Wiley-Interscience, 1974). Standard reference for equivalence of base-$b$ normality with $D_N \to 0$ (Chapter 1) **[S]**. Matches Papers XI–XIV. |
| `deBruijn46` | N. G. de Bruijn, "A combinatorial problem", *Proc. Kon. Ned. Akad. Wetensch.* **49** (1946), 758–764. Classical existence of binary cyclic de Bruijn words (Eulerian circuits on $\{0, 1\}^{h-1}$), used for the initial seed of Theorem 2.3 **[S]**. Matches Paper XIII. |
| `BCZ03` | Y. Bugeaud, P. Corvaja, and U. Zannier, "An upper bound for the g.c.d. of $a^n - 1$ and $b^n - 1$", *Math. Z.* **243** (2003), 79–84. Bibliographic record from secondary repository notes (`notes/phase24/partitions-and-reciprocal-spectra.md`, Theorem C1.4); original not examined **[U]**. Cited **for context only** in Section 1 and Remark 2.4 to explain the non-dyadic $+1$-inversion barrier; no proof in this manuscript uses `BCZ03`. |
| `Andrews1976` | G. E. Andrews, *The Theory of Partitions* (Encyclopedia of Mathematics and Its Applications, Vol. 2, Addison-Wesley, 1976). Cited (Chapter 1) as standard textbook reference for Euler's pentagonal number theorem, used as **External input** in Theorem D(ii) / Theorem 6.4 at $z = 1/b$ inside its disk of absolute convergence **[S]**; print edition not directly examined in this draft. |
| `EulerE541` | L. Euler, *Evolutio producti infiniti $(1-x)(1-xx)(1-x^3)(1-x^4)(1-x^5)\mathrm{etc.}$ in seriem simplicem*, *Acta Acad. Sci. Imp. Petrop.* **1780** (1783), 47–55 (Eneström index E541). Classical primary source for the pentagonal number theorem; bibliographic record inherited from Paper XI (`papers/11-generating-functions-digits/references.bib`), original not examined **[U]**. |
| `Billingsley99` | P. Billingsley, *Convergence of Probability Measures*, 2nd ed. (Wiley, 1999). Standard textbook reference for the Portmanteau theorem on continuity sets and open sets (Theorems 3.2, 4.4) and sequential weak$^*$ compactness on compact metric spaces (Proposition 5.3) **[S]**; section numbers not independently checked against print edition. |
| `Rudin76` | W. Rudin, *Principles of Mathematical Analysis*, 3rd ed. (McGraw-Hill, 1976). Standard textbook reference for the Stone–Weierstrass theorem on $\mathbb{T}$ (uniform density of trigonometric polynomials in $C(\mathbb{T})$, used in Theorem 3.2 and Proposition 5.3) **[S]**; section numbers not independently checked against print edition. |
| `GrenanderSzego58` | U. Grenander and G. Szegő, *Toeplitz Forms and Their Applications* (Univ. California Press, 1958). Cited (Chapter 3) for historical context on Toeplitz determinant limits after Proposition 4.3 **[U]**; print edition not examined; not used as a black box since Proposition 4.3 proves the constant-density case self-containedly. |
| `Simon05` | B. Simon, *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory* (AMS Colloq. Publ., Vol. 54, 2005). Cited (Chapter 2) for historical context on the Szegő–Kolmogorov–Krein theorem after Proposition 4.3 **[U]**; print edition not examined; not used as a black box. |
| `PaperXIII` | C. Anderson, *The Radix-Power Discrepancy Kernel Tower and Reciprocals of Extreme-Discrepancy Numbers* (v1.0, unreleased candidate draft in `papers/13-reciprocals-and-kernel-tower`). Project work; not peer reviewed **[R]**. Cited for context on rational-orbit $+1$-inversion, density of $\mathcal{A}_{\mathrm{conv}}(2)$, and the anchored coprime normal reciprocal rate $O_{b,A}((\ln N)^{-A})$ at $\alpha = 0$. All theorems of the present manuscript are proved self-containedly without relying on `PaperXIII`. |

---

### Theorem A (Lemmas 2.1, 3.1, Proposition 2.2, Theorems 2.3, 3.2, Proposition 3.3, Remarks 2.4, 3.4): Complete all-radix reciprocal discrepancy spectrum $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ and limiting measures $\mu_\alpha$

- **Evidence.** **Paper proof** using **External input** (Stone–Weierstrass on $\mathbb{T}$ and Portmanteau theorem on continuity sets), backed by **Finite certificate** (`scripts/phase25_partitions_reciprocals.py`, 15 dyadic pads, 936 contraction band positions, 15 coprime cut-and-fold updates across bases $2, 3, 4, 5, 10$, exact pair multiplicities, and rational factorization identity). No Lean 4 formalization.
- **Closest results.**
  - Within this repository, Candidate Paper XIII (`PaperXIII`, `GF-34`) established $0, 1 \in \mathcal{A}_{\mathrm{conv}}(b)$, density of $\mathcal{A}_{\mathrm{conv}}(2)$ via rational-orbit $+1$-inversion, and localized oscillation intervals in every base via repunit factors; Phase 24 Track C (`GF-38`, Theorem C1.1 & C1.4) extended density to all dyadic bases $b = 2^e$ and proved via `BCZ03` that $+1$-inversion is blocked in every non-dyadic base **[R]**.
  - Outside this repository, no dedicated literature search (MathSciNet / zbMATH / arXiv) was run during the drafting of Paper XV for exact convergent reciprocal discrepancy spectra of elements in $K_b$ or for the coprime-period cut-and-fold additive convolution mechanism **[U]**.
- **Relation.** Strictly strengthens the earlier repository results from dyadic density to exact equality $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ and exact limiting orbit measures $\mu_\alpha = \alpha\delta_0 + (1-\alpha)\lambda$ in every integer radix $b \ge 2$ **[M]**. External priority is provisional pending specialist literature review.

### Theorem B (Propositions 4.1, 4.3, Lemma 4.2, Theorem 4.4): Toeplitz determinant spectra, determinant-to-uniformity transfer, and reciprocal sharpness

- **Evidence.** **Paper proof** (completely self-contained proof of the constant-density Szegő–Kolmogorov–Krein limit in Proposition 4.3; Portmanteau for open sets and standard measure theory on $\mathbb{T}$). Compound-symmetric determinant identity (Proposition 4.1) also checked on exact rational instances in the uncommitted working-tree script `scripts/phase26_toeplitz_uniformity.py`. No Lean 4 formalization.
- **Closest results.**
  - The compound-symmetric determinant formula $\det((1-\alpha)I_r + \alpha J_r) = (1-\alpha)^{r-1}(1 + (r-1)\alpha)$ is classical elementary linear algebra **[S]**; no novelty is claimed for the matrix identity itself.
  - The general Szegő–Kolmogorov–Krein theorem $\lim_m (\det T_m(\rho))^{1/m} = \exp\int \log w\,d\lambda$ is classical (`GrenanderSzego58`, `Simon05`) **[S]/[U]**; Proposition 4.3 gives a self-contained elementary proof of the constant-density case $w \equiv a$ needed for $T_b$-invariant measures **[M]**.
  - The determinant-to-uniformity transfer for growing Toeplitz Gram dimensions $r(N) \to \infty$ (Theorem 4.4 / Theorem B(ii)) and its arithmetic sharpness across $[0, 1]$ via the reciprocal witnesses $1/x(b, \alpha)$ of Theorem A (Theorem B(iii)) were **not located in the sources examined**; no exhaustive literature search on Toeplitz Gram criteria for normal numbers or partial Lebesgue components was conducted **[M]/[U]**.
- **Relation.** Connects classical Toeplitz-determinant theory to Theorem A's reciprocal witnesses, proving sharpness of the transfer bounds across the entire interval $[0, 1]$ **[M]**.

### Theorem C (Propositions 5.1–5.3, Remark 5.4): Prime-power shifted grids, worst-start obstruction, and averaged incomplete-orbit cancellation

- **Evidence.** **Paper proof**; Proposition 5.3 uses **External input** (weak$^*$ compactness and Stone–Weierstrass on $\mathbb{T}$); Remark 5.4 is **Conditional**. Backed by **Finite certificate** (`scripts/phase25_partitions_reciprocals.py`, 16 product denominators across bases $3, 4, 5, 7, 10$). No Lean 4 formalization.
- **Closest results.**
  - Proposition 5.1 extends the prime-power arithmetic-progression grid argument of `PaperXIII` (`GF-34` §5.4, there proved for consecutive exponents $1, \dots, k$) to arbitrary strictly increasing exponent schedules in every radix $b \ge 3$ **[M]**.
  - Proposition 5.2 (initial zero-run lower bound for $1/Q$) and Proposition 5.3 (mean-square cancellation averaged over starts of a single rational cycle using grid orthogonality) are elementary Fourier/number-theoretic arguments **[M]**; no literature search on short-orbit cancellation for minus-factor reciprocal products was run **[U]**.
- **Relation.** Pinpoints the incomplete-orbit gap for slow minus-factor schedules at the specific starting numerator $b^{S_k} \bmod Q_k$ **[M]**.

### Theorem D (Lemmas 6.1–6.2, Theorems 6.3–6.4): Reciprocal separation and transition/discrepancy-gap bounds for $X_{b,m}$ and $P_b$

- **Evidence.** **Paper proof**; Theorem 6.4 uses **External input** (Euler's pentagonal number theorem, `Andrews1976`, `EulerE541`). Backed by **Finite certificate** (`scripts/phase25_partitions_reciprocals.py`, 152 reciprocal-separation instances and 16 actual initial Euler orbit windows, 4 strictly positive and 12 vacuous). Table 1 contains **finite measurements only**. No Lean 4 formalization.
- **Closest results.**
  - Lemma 6.1 ($1 - D_N \ge \frac{2}{5}\min_{c_0 \in F_b} M_N(z - c_0; b) - 1/N$) is an earlier repository result (`notes/phase23/binary-partition-and-carry-complexity.md`, Lemma 5.3, `GF-32`) re-proved self-containedly here **[M]**.
  - Euler's pentagonal number theorem is classical (`Andrews1976`, `EulerE541`) **[S]/[U]**.
  - No exhaustive literature search was run on lower bounds for digit transitions or $1 - D_N$ of Mahler's $m$-ary partition constants $X_{b,m}$ ($m \ge 3$) or Euler's partition constant $P_b = 1/E_b$ (and its partial products $R_k^{(E)}$) **[U]**. Any priority claim is provisional pending specialist review.
- **Relation.** Unconditional quantitative gaps away from $D_N = 1$ (leaving normality, $D^+ < 1$, and $K_b$-membership open) **[M]**.

## Outstanding checks before release

1. Independent human specialist peer review of the proofs and of all provisional priority statements, including MathSciNet/zbMATH/arXiv searches for reciprocal discrepancy spectra of $K_b$, coprime-period cut-and-fold convolutions, Toeplitz Gram uniformity transfer, and digit-transition bounds for $X_{b,m}$ and $P_b$.
2. Primary-text bibliographic verification of entries marked **[S]** or **[U]** (`BCZ03`, `Andrews1976`, `EulerE541`, `Billingsley99`, `Rudin76`, `GrenanderSzego58`, `Simon05`).
3. Owner release authorization (`metadata.toml`, committing `paper.pdf` if desired, updating `papers/manifest.toml`, `papers/SHA256SUMS`, and `docs/registry/papers.toml`). Reproducible LaTeX compilation and PDF inspection have already been completed in `/tmp/paper15-build` on `hail` (see `VERIFICATION.md`).
