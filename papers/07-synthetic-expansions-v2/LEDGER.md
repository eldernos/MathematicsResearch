# Claim-to-source novelty ledger: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v2.0, candidate draft)

No search proves novelty. "Not located in the sources examined" means only that the sources listed here, read as described, did not contain the statement. A failed search is recorded as a failed search and never as evidence of novelty. Every written proof and every comparison below has been checked only by AI models; **cross-model review is not independent human peer review**, and no human specialist has read the proofs.

Reading labels: **[R]** primary text read; **[A]** abstract or bibliographic record only; **[S]** stated by a secondary source that was read; **[M]** our own deduction; **[U]** unverified.

## Scope of this ledger

- The entries of the [v1.0 ledger](../07-synthetic-expansions/LEDGER.md) for Theorem A (switch), Theorem 4.2 (exact denominators), Theorem B (complete-period rates), Corollary 4.6 (Liouville family), Theorem C (prescribed limits; classical realization by Colebrook and Sigmund, encoding of Remark 6.5), Theorem E (infinite sums) and Proposition 8.5 carry over **unchanged**, including their search records and outstanding checks. They are not repeated here.
- This ledger adds entries for the new and upgraded material: Theorem D (polynomial images below the schedule degree, with rates for one and for several orders), Lemma 2.7 (uniform short orbits) and Theorem F (the boundary $d=r$, formerly Theorem G, now including the irrationality of squares, the innovation law and the packet barrier). **Split, 27 November 2026:** the former Theorem F (all-prime polynomial normality and irrationality exponents) moved to the companion candidate draft [Paper XII](../12-all-prime-normality-exponents/), whose [ledger](../12-all-prime-normality-exponents/LEDGER.md) carries its entry; the former entry is kept below, marked as moved, for the record.
- **No new web or database search was run for this draft.** The literature positions below rest on (a) the v1.0 ledger (searches of 25 November 2026), (b) the fresh primary-source and public-repository review of 25 November 2026 recorded in [`notes/phase21/phase20-audit-and-paper-plans.md`](../../notes/phase21/phase20-audit-and-paper-plans.md) §2.2 (queries Q1–Q16, reads D1–D5, verbatim), and (c) the literature notes of the source notes, in particular [`notes/phase20/literature.md`](../../notes/phase20/literature.md). Outstanding checks are listed at the end.

## Bibliography verification for the entries new in v2.0

| Key | Status |
| --- | --- |
| `PaperIv2` | This project's manuscript, release `manuscripts-v2.0.0`, [`papers/01-stoneham-polynomials-v2`](../01-stoneham-polynomials-v2/); the statement of Theorem A was read in the source on 26 November 2026 **[R]**. After the split it is cited here only for that kernel-verified theorem; the use of its Lemmas 2.2–2.4 moved to Paper XII (Theorem 6.4 there). |
| `Manai25` | Moved with the all-prime material to Paper XII; no longer cited here. |
| `Titchmarsh86` | Standard reference for Theorem 5.13 (the $q$-th derivative test). Bibliographic data standard; the statement used (constants depending on $q$, $K=2^{q-1}$) agrees with the form audited in the Phase 20 and 21 model reviews **[S]**; the book was not re-read here. |
| `Hooley71` | C. Hooley, *Acta Math.* **127** (1971) 279–297. Volume, pages and the moment bound $\sum(s_{n+1}-s_n)^\gamma\ll Y(\log Y)^{(\gamma-1)/2}$, $0<\gamma<5/3$, as confirmed by the Phase 22 Track C1–C2 model review **[S]**; primary text not read. DOI omitted because it was not verified. |
| `Wooley15` | T. D. Wooley, *Sums of three cubes, II*, *Acta Arith.* **170** (2015). The exponent $0.91709477$ and the volume as quoted in the source note and confirmed by the same model review **[S]**; pages unverified **[U]**; primary text not read. |
| `DHL06` | J.-M. Deshouillers, F. Hennecart, B. Landreau, *On the density of sums of three cubes*, ANTS VII, LNCS 4076 (2006). The predicted density $\approx0.0999$ as quoted in the source note and confirmed by the model review **[S]**; pages unverified **[U]**. |
| `Landau08` | E. Landau (1908). Bibliographic data from secondary sources **[U]**; the asymptotic $S(Y)\sim K_{\rm LR}Y/\sqrt{\log Y}$ is classical and is used only as an upper bound $\ll Y/\sqrt{\log Y}$. |
| `BambahChowla47` | R. P. Bambah and S. Chowla (1947). Bibliographic data from secondary sources **[U]**; used only for gaps $O(Y^{1/4})$ between sums of two squares, a proportion $O(Y^{-3/4})$. |
| `Tenenbaum15` | G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., AMS GSM 163 (2015), Chapter II.5 (Selberg–Delange method). Chapter reference standard; not re-read **[S]**. |
| `HW08` | Hardy–Wright, 6th ed. (2008), Theorem 317 (maximal order of the divisor function). Standard **[S]**; not re-read. |
| `HR74` | Moved to Paper XII (Lemma 3.4 there); no longer cited here. |
| `Roth55` | Moved to Paper XII (Theorem 6.2 there); no longer cited here. |
| `DEKKM` | R. Dietmann, C. Elsholtz, A. Kalmynin, S. Konyagin and J. Maynard, *Longer gaps between values of binary quadratic forms*, IMRN, doi:10.1093/imrn/rnac130. Theorem 1 ($\limsup(\sigma_{n+1}-\sigma_n)/\log\sigma_n\ge390/449$, positive sums of two squares with zero coordinates allowed, natural logarithm) was checked against the five-author accepted manuscript in the Oxford Research Archive by the Phase 23 Track C review **[S]**. The general-discriminant Theorem 2 gives only about $0.2215$ at $D=-4$ and would not suffice. Volume, pages and the typeset theorem numbering are **[U]**; the author list was confirmed by web search on 27 November 2026. |
| `Ghidelli20` | L. Ghidelli, *Arbitrarily long gaps between the values of positive-definite cubic and biquadratic diagonal forms*, J. London Math. Soc., doi:10.1112/jlms.12312, arXiv:1910.05070. The title was confirmed from the arXiv listing on 27 November 2026. Theorem 1.1 (gaps of every length $K<\kappa_F\sqrt{\log N}/(\log\log N)^2$ below $N$ for positive diagonal cubic forms, nonnegative variables) was checked by the Phase 23 Track C review **[S]**. Volume and pages are **[U]**. |
| `PaperXII` | This project's companion candidate draft (unreleased), `papers/12-all-prime-normality-exponents`. |

The v1.0 entries (Stoneham, Korobov, Kano, Kano–Shiokawa, Wagner, Bailey–Crandall, Vandehey, Colebrook, Sigmund, DGS, Bugeaud, Becher–Heiber–Slaman, Levin, ABSS, Kuipers–Niederreiter, Graham–Kolesnik, Parthasarathy, Lean, Mathlib, Mira Cult, Captain Sude, the companion manuscripts) keep the verification status recorded in the v1.0 ledger, including the unverified notes on Colebrook (full text not read) and Wagner (full text not read).

---

### Theorem D (Theorems 7.19–7.24): polynomial images below the schedule degree, with rates

- **Statement and hypotheses:** $p\nmid b$ odd prime, $t=\operatorname{ord}_p(b)$, $d\ge2$, $X_a=C(b,p,a,d)$. Every nonconstant $P\in\mathbb Q[z_a:a\in S]$ of total degree $r\le d-1$ gives a number normal to base $b$; for one order, $D_N\ll(\log\log N)^{-d/(d-1)}$ when $r\ge2$ and $D_N\ll N^{-\eta}$ when $r=1$.
- **Evidence:** Lean-supported paper proof; see [VERIFICATION.md](VERIFICATION.md). Registry: [GF-11](../../docs/results.md#gf-11) (one order, qualitative), [GF-14](../../docs/results.md#gf-14) (several orders; small-ball bound; rate for $d>r(s+1)$), [OP-14](../../docs/results.md#op-14) (the v1.0 quadratic case). The rate for $r+1\le d\le r(s+1)$ comes from `notes/phase22/short-orbits-and-irrationality.md`, which has no registry entry yet.
- **Closest published results:**
  - Wagner (1995) and Kano–Shiokawa (1993, Theorem 5): explicit uncountable rings all of whose nonzero elements are normal to base $b$ and nonnormal to base $ab$; nonzero polynomial expressions in the generators are ring elements, so these are direct precedents for normality of polynomial images of suitable generators. As recorded in the v1.0 ledger, Wagner's text was not read (described via Kano 1993, §1, p. 910 **[R]**, and the Kano–Shiokawa preprint, p. 1 **[R]**). The generator hypotheses (rapidly separated exponents) have **not** been verified for the $X_a$, whose consecutive positions have ratio tending to one and whose weight exponents return to zero infinitely often. Theorem D does not produce a ring and is limited to total degree below $d$.
  - Kano (1993), Theorem 1; Bailey–Crandall (2002), Theorem 4.8; Vandehey (2019), Theorem 7.4: linear normality criteria for series with prescribed numerators or numerator one. As in v1.0, the insertion denominators $p^{-sv_p(k)}$ reset, so none applies term by term; none treats polynomial images.
  - Vandehey (2019), Corollary 1.2 and Theorem 5.1 (arXiv version): power-saving estimates for incomplete Korobov sums on moduli with **fixed** prime support. Lemma 2.7 is an elementary stride-differencing estimate on prime-power moduli whose point is uniformity in the **base** $G=b^\tau$ with $\tau$ growing; uniformity in a varying base is not stated in Vandehey's results as read in the Phase 13–14 audits **[S]**. With fixed support, Vandehey's Theorem 5.1 would give a better exponent $\delta$ in Theorem 7.21; Lemma 2.7 is used because Theorem 9.7 needs varying support. Korobov (1972) is the classical source of the $p$-adic method.
  - Graham–Kolesnik (1991) and Titchmarsh (1986, Theorem 5.13): the exponential-sum tests used, as external inputs.
  - Levin (1999) and Aistleitner–Becher–Scheerer–Slaman (2017): normal numbers with far smaller discrepancy. The rates of Theorem D are much weaker and concern specific arithmetic numbers.
- **Closest public-repository results:**
  - Mira Cult, S08 (*Polynomial normality and cyclotomic rank criteria for Stoneham-type values*, gist revision `41b5a780`, 7 October 2026, Theorem 1.1) **[R in v1.0]**: every nonconstant rational polynomial in $\sum_kq^{-k}b^{-c^k}$ is normal when $q>2$ and some prime divides $c$ and $q$ but not $b$, with a power saving for $(x,\ldots,x^m)$. Exponential schedule $c^k$, monotone weights, nonvanishing leading $p$-adic part. On the polynomial schedule $ti^d$ the leading residue vanishes on a set of shifts of positive lower density, so Theorem D needs null level sets and the small-ball estimate. Neither result contains the other **[M]**.
  - Mira Cult, joint normality of Stoneham series (commit `357d26a`): linear forms only. Captain Sude repositories: linear combinations only. The 25 November 2026 scan of `Mira-Cult/math` at commit `cf9e57f` (audit note §2.2, D3–D4) was a keyword scan of file names and contents for generating-function terms; it did not search for power-schedule polynomial normality, and the notes were not read in full.
- **Relation:** different family. Apparently not in the sources examined for these numbers: normality in every degree below $d$ on $ti^d$, several orders, the small-ball estimate, the refutation of uniform isolation, and the rate. Polynomial normality of suitable generators as such is known (Wagner; Kano–Shiokawa; S08 on exponential schedules; Paper I v2.0 Theorem A, kernel-verified, for Stoneham numbers).
- **Outstanding review:** a specialist should check Lemma 7.16 (the regular/irregular split, the uniformity of the exponential-sum errors over $N$ components, the capped case $q>d$), the recursion in Theorem 7.18, the $L^1$ localization in Theorem 7.20, and the freezing constraint $c_0(1+d/s)\log p<1/2$ in Theorem 7.21.

### Lemma 2.7 and Corollary 2.8: short orbits uniform in the base

- **Statement:** for an odd prime $p$, a principal unit $G\ne1$ with $A(G)\le\frac3{16}\log_pM_0-1$ and $p^{\theta e}\le M_0$, $\lvert\sum_{m<M}e(cG^m/p^e)\rvert\le9M_0^{1-\delta}$ with $\delta=2^{-\lceil2/\theta\rceil-3}$; an example shows some bound on $A(G)$ of order $\log_pM_0$ is necessary.
- **Evidence:** Paper proof (elementary). Exact identities checked by `scripts/phase22_short_orbits.py`.
- **Closest results:** Korobov (1972), Vandehey (2019, Theorem 5.1 and Corollary 1.2), and the kernel-verified qualitative fixed-support estimate `SmoothOrbit.fixed_support_orbit_estimate` (Lemma 4.3). The stride-differencing idea is that of `SmoothOrbit` made quantitative by tracking $A(G)$ **[M]**.
- **Relation:** a variant of known methods; we claim no novelty for the method, only for its use with growing auxiliary support. **Outstanding check:** whether an explicit base-uniform estimate of this kind appears in the literature on Korobov sums (Korobov, Vandehey, Bourgain-type prime-power estimates) was not searched for this draft.

### Former Theorem F (former Theorems 9.2, 9.7, 9.10, 9.11): moved to Paper XII

*This entry describes the 26 November draft and is kept for the record. The material is now Paper XII, Theorems A–C; the current entry is in the [Paper XII ledger](../12-all-prime-normality-exponents/LEDGER.md).*

- **Statement:** (i) $W=\sum p^{-k^2}\ell_k^{-1}b^{-2^{k^3}}$: exact denominators $p^{k^2}\ell_1\cdots\ell_k$; every nonconstant $P(W)$ normal and Liouville with rate $\exp(-c(\log N)^{2/3})$. (ii) Polynomial schedules $tk^d$, $d\ge r+1$: degree $\le r$. (iii) Geometric schedules: degree $\le r$, $\mu(W_G)=\lambda$. (iv) Stoneham schedule with auxiliary primes: all degrees, $\mu(W_S)=p$. For (ii) and for the quasi-polynomial schedule of Remark 9.12, **finiteness of the irrationality exponent and non-Liouville status are open**.
- **Evidence:** (i) Lean-supported paper proof (three `ProtectedPole` declarations, with the exact scope in [VERIFICATION.md](VERIFICATION.md)); (ii)–(iv) Paper proofs; (iv) uses Paper I v2.0, Lemmas 2.2–2.4, as an external input. Registry: [GF-10](../../docs/results.md#gf-10) for (i) and Remark 9.6, [GF-15](../../docs/results.md#gf-15) for Corollary 9.5 and for (ii) in the range $d>r(s+1)$; (ii) for $r+1\le d\le r(s+1)$ and (iii)–(iv) have no registry entry yet. Also related: [OP-09](../../docs/results.md#op-09) (the v1.0 all-odd-prime series, normal itself, rate $O(1/\log N)$) and [OP-08](../../docs/results.md#op-08) (the grid).
- **Closest published results:**
  - **Manai, arXiv:2508.09319** **[A]**: explicit numbers $x$ such that $p(x)$ is normal, indeed absolutely normal, for every nonconstant integer-valued polynomial $p$ ("transcendentally normal numbers"). Theorem F is different in kind: one fixed base; every rational polynomial; explicit series whose shifted prefix denominators acquire every prime not dividing $b$; explicit rates; and a Liouville or prescribed finite irrationality exponent. As far as can be told from the abstract, neither result contains the other. **The theorem of Manai was not read**; a reader comparing the two should consult it. Manai's later preprint arXiv:2609.24665 (normality-preserving operations) **[A]** concerns a different question.
  - Kano–Shiokawa (1993), Remark 2 (irrational ring elements are Liouville, per the Phase 18 source audit **[S]**), Bailey–Crandall (2002), Bugeaud (2002), Becher–Heiber–Slaman (2015): normal Liouville numbers, explicit or absolutely normal. Theorem F(i) adds polynomial normality of all images and the all-prime denominators for an explicit series.
  - Stoneham (1973); Mira Cult S08 **[R in v1.0]** and Paper I v2.0 Theorem A **[R]**: without auxiliary primes $W_S$ is $\alpha_{b,p}$, and its polynomial normality is that theorem. Theorem F(iv) adds the growing auxiliary support and the irrationality exponent.
  - **Irrationality exponents.** The computation $\mu=\lambda$ for lacunary series with geometric gaps is the classical truncation argument (Lemma 9.8). We make **no** priority claim for normal numbers with a prescribed irrationality exponent as such, and we did **not** search the literature on irrationality exponents of normal or Stoneham-type numbers for this draft (see outstanding checks).
- **Closest public-repository results:** none located in the scans of 25 November 2026 (audit note §2.2): `Mira-Cult/math` keyword scan; Captain Sude repository names and descriptions only (`Stoneham-sum-normal`, `stoneham-prime-support`, and others), contents not read.
- **Registry wording.** The registry entry [GF-25](../../docs/results.md#gf-25) describes Theorems 9.10–9.11 as "the first explicit non-Liouville all-prime polynomial normal numbers with exact finite irrationality exponents". No search supports a priority claim of that strength (outstanding check 2 below), and the manuscript does not make it.
- **Relation:** apparently not in the sources examined: all-prime polynomial normality on these schedules and its combination with Liouville or finite exponents. **Outstanding review:** the window rule and the run count in Theorem 9.2; the lexicographic structure and the tie bound $(r+1)!$ in Theorem 9.10; the transfer of pole retention modulo $p^l$ in Theorem 9.11.

### Theorem F (formerly G) and Section 9 (formerly 10): the boundary $d=r$

- **Statement:** at $d=r$ the $p$-adic depth defect is tight in density; denominator data cannot determine the digits on runs shorter than $\log_b(q/2)$, and no numerator-uniform orbit estimate beats the trivial bound below $\log_b(\epsilon q)$; at $d=2$ the integer part of the level filtration is absorbed ($X_H\in K_b$, uniformly in $H$) and $C^2$ is normal iff $Z_H$ is; almost every shift lies in a short support run of $Z_H$ (Hooley); for $p\equiv3\pmod4$ fractional jumps number $\asymp Y/\sqrt{\log Y}$; at $d=3$ absorption is conditional on density zero of sums of three cubes. **Normality of $\xi^3$ and of $C(b,p,s,2)^2$, and even $\limsup D_N<1$, remain open** (Question 10.1; v1.0 Question 1, second half).
- **Evidence:** Paper proofs with external inputs (Landau, Hooley, Bambah–Chowla, Selberg–Delange); the cubic paragraph rests on Wooley and on the DHL model and claims nothing. Registry: [GF-14](../../docs/results.md#gf-14) item (3) for Proposition 9.1 and Lemma 9.2; [GF-24](../../docs/results.md#gf-24) for 9.3–9.10; the Phase 23 statements 9.11–9.18 have no registry entry yet.
- **Closest results:**
  - **Hooley (1971):** moment bound for gaps between sums of two squares; used as an external input in Theorem 9.9.
  - **Wooley (2015):** sums of three positive cubes up to $Y$ number $\gg Y^{0.91709477}$ **[S]**; used only to show that the integer part at $d=3$ is not known to be sparse.
  - **Deshouillers–Hennecart–Landreau (2006):** probabilistic model predicting density $\approx0.0999$ for sums of three cubes **[S]**; if correct, the absorption argument fails at $d=3$.
  - Bailey–Borwein–Crandall–Pomerance (2004) separate one-bit counts from discrepancy for $\Theta_3(1/2)^2$ (per `notes/phase20/literature.md` **[S]**); context only.
- **Relation:** these are limitations of the method, proved for the specific numbers. Not located in the sources examined. **Outstanding:** a density-one statement for fractional runs (needs a Hooley-type bound for squarefree sums of two squares in a residue class), and anything for $p\equiv1\pmod4$.

### Theorem 7.24 and Lemma 7.23: rates for several orders

- **Statement:** for distinct orders $s_1<\cdots<s_m$ and every nonconstant rational $P$ of total degree $r<d$, $D_N(P(X_1,\ldots,X_m))\ll(\log\log N)^{-d/(d-1)}$; $N^{-\eta}$ if the largest weighted degree is carried by a single linear monomial.
- **Evidence:** Paper proof (Lemma 7.23 is Lean-supported through the peeling lemma and the divisor bound). The source is Phase 23 Track C3, accepted after review. The weighted isolation lemma is the standalone multivariate Lemma I that the review (m7) asked for. Not registered yet.
- **Closest results:** as for Theorem D. No rate for several orders was located in the sources examined; no new search was run.
- **Outstanding review:** a specialist should check the row exponents imported from Lemmas 7.15–7.16 under $H'\le H+C$, $v'\ge H'/r$, $q\le r+1\le d$. The Phase 23 review checked that substitution but did not re-derive the Titchmarsh 5.13 exponents.

### Theorem 9.12 and Section 9.4: irrational squares

- **Statement:** $C(b,p,s,2)^2$ is irrational when $s<(390/449)\,t\log b$, in particular for every $s=1$.
- **Evidence:** Paper proof using the **External input** DEKKM Theorem 1 (Theorem 9.11). Phase 23 Track C1, accepted; the review's Major finding M1 was the wrong theorem number, now corrected.
- **Closest results:** the method (a positive tail after a long gap in the support contradicts a bounded rational denominator) is classical; we claim novelty only for its application to these squares **[M]**. Irrationality of $C(b,p,s,2)^2$ for larger $s$, and of $\xi^3$, remains **open**. A logarithmic gap between sums of three positive cubes with constant above $2/(3\log2)$ would settle the cube (Proposition 9.18, **conditional**); Ghidelli's theorem gives only gaps of order $\sqrt{\log N}/(\log\log N)^2$.

### Theorem 9.13, Proposition 9.14, Lemma 9.15, Proposition 9.16: innovations and packets

- **Evidence:** Paper proofs. Theorem 9.13 uses Selberg–Delange with Legendre twists (Tenenbaum II.5) as an external input. Phase 23 Tracks C1–C2, accepted.
- **Relation:** these are limitations of the method, proved for the specific numbers. Not located in the sources examined. Proposition 9.16 concerns hypothetical continuations and asserts nothing about which numerators occur in the given series.

### Proposition 7.17: uniform isolation fails

- Finite and explicit; a limitation of the method of the Phase 20 note, not a statement about the literature. Certified by `scripts/phase21_nonlinear.py` for $H\in\{6,10,100,1000,4000\}$ and, for this draft, by a direct exact computation for $4\le H\le12$ (see [VERIFICATION.md](VERIFICATION.md)).

## Outstanding checks before release

1. (Moved to Paper XII.) Reading Manai, arXiv:2508.09319, now concerns Paper XII.
2. (Moved to Paper XII.) The literature search on irrationality exponents of normal numbers now concerns Paper XII, which makes no priority claim.
3. Search for base-uniform short-orbit estimates on prime-power moduli (Lemma 2.7).
4. Verify Hooley (1971), Wooley (2015), DHL (2006), Landau (1908), Bambah–Chowla (1947) and the Halberstam–Richert sieve statement against primary texts or Crossref, and add DOIs only when verified.
5. The v1.0 outstanding items remain: Colebrook and Wagner full texts; whether the Kano–Shiokawa or Wagner generator hypotheses could hold for some representation of the $X_a$; the Erdős–Turán theorem number in Kuipers–Niederreiter.
6. The normality converse for integer multipliers in Section 9 is a case of Wall's theorem (rational multiples of normal numbers are normal; Wall 1949, as quoted in later sources **[S]**). The manuscript proves the integer case directly and does not cite Wall; add a primary citation if one is verified.
7. `scripts/phase22_short_orbits.py`, `scripts/phase22_nonlinear_boundary.py` and `NormalityChecker/Phase22Cores.lean` were committed in `8ca4309`. Still to do: commit `scripts/phase23_nonlinear_short_orbits.py` (untracked) and the Audit 2 working-tree repair of `scripts/phase22_short_orbits.py`, and register the Phase 23 Track C material (Lemma 7.23, Theorem 7.24, 9.11–9.18).
8. Confirm the theorem numbering of DEKKM in the typeset IMRN version, and verify the DEKKM and Ghidelli bibliographic data (volume, pages) against Crossref.
9. Compile the PDF (`pdflatex`, `bibtex`; unavailable locally and on `hail`) and re-run the structural and portal checks.
