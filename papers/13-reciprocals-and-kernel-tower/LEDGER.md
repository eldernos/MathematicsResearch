# Claim-to-source novelty ledger: The Radix-Power Discrepancy Kernel Tower and Reciprocals of Extreme-Discrepancy Numbers (v1.0, candidate draft)

A search cannot prove novelty. "Not located in the sources examined" means only that the sources listed here, read as described, did not contain the statement. A failed search is recorded as a failed search and never as evidence of novelty. Every written proof and every comparison below has been checked only by AI models. **Cross-model review is not independent human peer review**, and no human specialist has read the proofs.

Reading labels: **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[M]** our own deduction; **[U]** unverified.

## Scope

This ledger covers the candidate Paper XIII unifying Phase 22/23 results on the radix-power discrepancy kernel tower (`GF-23`, Phase 23 Track A2, `RadixPowerTower.lean`, `HigherOrderTower.lean`) and reciprocals of discrepancy-kernel elements (`GF-16`, `GF-26` including Phase 23 Audit 2 repairs, and Phase 23 Track D1--D2--D4). **No dedicated new external literature search was run for this candidate draft** beyond the prior-art notes already recorded in the Phase 21--23 source notes; every priority question below is therefore marked conservatively.

## Bibliography verification

| Key | Status |
| --- | --- |
| `Bang1886` | A. S. Bang, *Tidsskrift for Mathematik* (5) **4** (1886), 70--80, 130--137. Classical primitive-divisor theorem cited via secondary literature **[S]**; primary text not read. |
| `Zsigmondy1892` | K. Zsigmondy, *Monatsh. Math. Phys.* **3** (1892), 265--284, doi:10.1007/BF01692444. Classical primitive-divisor theorem cited via secondary literature **[S]**; primary text not read. |
| `HullDobell62` | T. E. Hull and A. R. Dobell, *SIAM Review* **4** (1962), 230--254, doi:10.1137/1004061. Classical full-period LCG condition cited as context **[S]**; Theorem 3.1 gives a self-contained proof. |
| `deBruijn46` | N. G. de Bruijn, *Proc. Kon. Ned. Akad. Wetensch.* **49** (1946), 758--764. Classical source for binary de Bruijn cycles **[S]**. |
| `KN` | L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences* (1974). Standard reference for Weyl's criterion and Erd\H{o}s--Tur\'an **[S]**. |
| `Bugeaud12` | Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts in Math. **193** (2012). Standard reference for radix normality and cylinder discrepancy bounds **[S]**. |
| `HW08` | G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008). Standard reference for Wigert's divisor bound (Theorem 317) and repeating radix fractions (§9.12) **[S]**. |
| `BC02` | D. H. Bailey and R. E. Crandall, *Experimental Math.* **11** (2002), 527--546. Context for explicit arithmetic normal constructions **[S]**. |
| `BecherCarton19` | V. Becher and O. Carton, *J. Complexity* **54** (2019), 101403. Context for low-discrepancy normal numbers from nested perfect necklaces **[A]/[S]**. |
| `Lean4`, `Mathlib` | Standard Lean 4 and Mathlib references, matching Paper XII. |

---

### Theorem A (Theorems 2.1--2.8): radix-power kernel tower $K_{b^k}/K_b$, $b^L\mid k$ classification, and $L$-normal discrepancy spectrum

- **Evidence.** Theorems 2.1--2.5 are **Kernel-verified** in `RadixPowerTower.lean` and `HigherOrderTower.lean`; Propositions 2.6--2.7 and Theorem 2.8 are **Paper proofs** (`VERIFICATION.md`).
- **Closest results.**
  - Existence of base-$b$ de Bruijn cycles of order $L$ is classical (`deBruijn46`, Euler circuits of $G_{b,L}$) **[S]**.
  - The cylinder-rounding bound $D^+(x;b)\le 2/b^L$ is elementary folklore (cf.\ `Bugeaud12`, Ch. 4) **[S]**. We claim no novelty for the upper bound alone; our contribution here is its Lean~4 formalization together with the sharp attainment of $[0,2/b^L]$ and $(0,2/b^L]$, the exact finite-level tower spectrum \eqref{eq:finite-spectrum}, and the kernel-verified classification $K_{b^k}/K_b\cong\Z/R\Z$ and $b^L\mid k$ characterization.
  - Becher--Carton (`BecherCarton19`) study low-discrepancy normal numbers via nested perfect necklaces; here the finite order $L$ is fixed and discrepancy is measured over all intervals **[M]**.
- **Relation.** Not located in the sources examined; no exhaustive literature search on the discrepancy kernel $K_b$ was run.

### Theorem B (Theorems 3.1--3.6): exact reciprocal periods, balanced rates, and Hull--Dobell rigidity

- **Evidence.** **Lean-supported paper proof** (Theorems 3.1 and 3.3), **Paper proof** (Theorem 3.4), and **Paper proof + External input** (Bang 1886, Zsigmondy 1892 in Lemma 3.5 and Theorem 3.6).
- **Closest results.**
  - The Hull--Dobell full-period bijection (`HullDobell62`) and LTE order lifting are classical elementary number theory **[S]**; no novelty is claimed for the standalone LTE step.
  - Theorem 3.3--3.6 sharpen Phase 21's normal-reciprocal construction (`GF-16`), establish the balanced-multiplier rate and Koksma lower barrier, and characterize the relaxed Hull--Dobell family via Bang--Zsigmondy rigidity **[M]**.
- **Relation.** Not located in the sources examined; no search of the literature on normal numbers arising as reciprocals of lacunary products was run.

### Theorem C (Theorems 4.3--4.6, 5.2--5.4): sign classification, cyclotomic $P_k$ realizations, and rational-orbit inversion

- **Evidence.** **Paper proofs** (with `NormalReciprocalCore.signed_band_identity` and `RadixPowerTower.coprime_rat_cylinder_margin` as Lean-verified finite steps).
- **Closest results.**
  - Phase 21 (`GF-16`) showed $\limsup D_N\ge 1/2$ when $\varepsilon_k=+1$ infinitely often; Theorems 4.3--4.4 give the complete classification of all sign sequences, weak$^*$ limit sets, and oriented digit frequencies **[M]**.
  - Realizing prescribed discrepancy intervals or base-$2$ simple normality on reciprocals of $K_b$ elements via $P_k(q)$ (Theorem 4.6) and $+1$/repunit rational-seed inversion (Theorems 5.2--5.4) was not located in the sources examined **[M]**.

### Theorem D (Theorems 6.1--6.5): sharp $D_{\max}(b,L)=2b^{-L}$ and all-base $L$-normal nonnormal reciprocals

- **Evidence.** **Paper proofs** (with `coprime_rat_cylinder_margin` verified in Lean).
- **Closest results.**
  - Repeating-fraction uniformity of $1/p$ for primitive roots $p=kb^L+1$ (Proposition 6.4) is classical (`HW08` §9.12) **[S]**; no novelty is claimed for the elementary $1/p$ digit count or quadratic-reciprocity check itself, which are recorded to show why a more general construction is needed.
  - Attainment of $D_{\max}(b,L)=2b^{-L}$ via $G_{b,L}^*$ (Theorem 6.1) and simultaneous $L$-normality (indeed $(L+1)$-normality) of all multiples $sr$ ($1\le s<b$) via the refined Markov digraph $\mathcal G_{b,M}$ (Lemma 6.2, Theorem 6.3) were not located in the sources examined **[M]**.

### Theorem E (Theorems 7.1--7.5): non-tetration normal reciprocals, coprime CRT convolution, and $R_k^{(E)}$

- **Evidence.** **Paper proofs**.
- **Closest results.**
  - Breaking the tetration growth of Phase 21/22 divisible schedules via anchored coprime schedules $m_k=\omega_{k-1}T_{k-1}+s$ (Theorem 7.1) and fully coprime CRT convolution squaring (Theorem 7.4) was not located in the sources examined **[M]**.
  - Complete-period equidistribution of the prime-exponent product (Corollary 7.3) and $p$-adic grid equidistribution of $R_k^{(E)}=\prod_{j=1}^k(1-b^{-j})^{-1}$ (Theorem 7.5) use elementary CRT and LTE methods; whether equivalent complete-period discrepancy bounds for $\prod_{j=1}^k(1-b^{-j})^{-1}$ appear in the literature on rational approximations to Euler's function was not searched **[U]**.

## Outstanding checks before release

1. Conduct a targeted literature search on: (a) discrepancy kernels $K_b$ and radix-power quotients; (b) normal numbers obtained as reciprocals of lacunary or $K_b$ infinite products; (c) sharp attainment of $D_{\max}(b,L)=2b^{-L}$ for $L$-normal reals; and (d) complete-period discrepancy bounds for partial products of $\prod_{j\ge1}(1-b^{-j})^{-1}$.
2. Verify bibliographic details of `Bang1886`, `Zsigmondy1892`, `HullDobell62`, `deBruijn46`, `Bugeaud12`, and `BecherCarton19` against primary texts or Crossref.
3. Compile the PDF (`pdflatex` $\times 3$ + `bibtex`) and inspect numbering, layout, and overfull boxes.
4. Commit and pin `NormalityChecker/HigherOrderTower.lean`, `scripts/phase23_euler_tower.py`, `scripts/phase23_reciprocals_v2.py`, the Audit 2 repair of `scripts/phase22_reciprocals.py`, and the working-tree `GF-29`/`GF-34` registry entries.
