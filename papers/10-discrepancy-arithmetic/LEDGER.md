# Claim-to-source novelty ledger: The Arithmetic of Extreme Discrepancy (v1.0)

No search proves novelty. "Apparently new in the sources examined" means only that the sources listed here, read as described, did not contain the statement. Priority is provisional.

The searches combined:

1. The primary-source audit `notes/phase19/literature.md` (25 November 2026, at `c2c9da6`), in particular its "Executive priority warnings" on the five-vertex addition spectrum and on the distance $1-D$, and §§1, 4 and 5.
2. The checkpoint-18 audits `notes/phase18/sources.md` and `notes/phase18/reviews/classical-sources.md` (at `e4809cf`), and the earlier ledger of manuscript C, from which the translation and addition material moved.
3. New checks for this manuscript on 25 November 2026: the arXiv record and HTML of Bergelson–Downarowicz arXiv:2506.12929v1 (abstract page; §§2, 3, 4.1, 4.2 and 5 read in full text; §4.3–4.5 only through a model-extracted summary). During the revision of 25 November 2026 the arXiv PDF of v1 was read directly for Proposition 4.25, the remark on Kamae after Proposition 4.9, and Section 8 (Theorem 8.1, Theorem 8.11, Proposition 8.13, Corollary 8.14 and their proofs), web searches for the Ky Fan, Prokhorov and Kuiper records, and the reference trails below.

MathSciNet was not accessible. arXiv, zbMATH Open, Crossref and publishers' pages were used. Every written proof and every comparison below has been checked only by AI models; none has been checked by an independent human expert.

## Bibliography verification

- **Checked against Crossref or publisher metadata (title, authors, venue, volume, pages, year, DOI):** Rauzy 1976; Sigmund 1974; Kuiper 1960; Lévy 1939 (Crossref's volume field is inconsistent; volume 67 and pages 1–41 were taken from the Numdam record `BSMF_1939__67__1_0`, checked again in the revision of 25 November 2026); de Moura–Ullrich 2021; the mathlib Community 2020. These were verified for manuscript C on 25 November 2026 and reused. **Kamae 1976** (*Normal numbers and ergodic theory*, Lecture Notes in Mathematics 550, pp. 253–269, doi:10.1007/BFb0077494) was added in the revision: author, title, pages, year and DOI match the Crossref record; the volume number 550 and the Symposium title are as given in Bergelson–Downarowicz's reference list. The original was not read; the paper cites it only for the attribution that Bergelson–Downarowicz make (inequality (d) of their Proposition 4.9).
- **Ky Fan 1943, Prokhorov 1956, Dudley 2002:** bibliographic data and DOIs are those recorded as directly verified in `notes/phase19/literature.md` §4; they were not re-fetched for this manuscript. Dudley §11.3 is cited for the Lévy–Prokhorov metric following that note.
- **Kuipers–Niederreiter 1974:** publisher and the two theorem numbers cited were checked against a text copy for manuscript C.
- **Bergelson–Downarowicz:** arXiv abstract page (v1 only, submitted 15 June 2025, no journal reference) and HTML read on 25 November 2026. Verbatim text read for Definitions 3.2, 3.5, 3.10, Theorem 3.12, Proposition 4.9 and Corollary 4.10(1). In the revision the PDF text was also read for Proposition 4.25 (for every nonzero rational $q$, $\underline h(qx)=\underline h(x)$ and $\overline h(qx)=\overline h(x)$, so normality and determinism are preserved) and for Section 8. §4.3 (attainability, Examples 4.20–4.23) was read only through a summary of the HTML. **Section 8 uses ordinary binary digits throughout; the word "signed" does not occur in the paper.** Theorem 8.11: for the normal number $x$ of §8.2 (Definition 8.7, Theorem 8.8) and the deterministic number $y$ of §8.3 (binary digits the indicator function of $\{0\}\cup\mathsf{FS}((n_k))$, density zero of ones), the product $xy$ is deterministic, its binary expansion having density zero of switches ($01$ and $10$). Proposition 8.13: $1/y$ is deterministic; its expansion has density zero of ones. Corollary 8.14: $a=xy$ and $b=1/y$ are deterministic with $ab=x$ normal. An earlier version of this ledger and of the paper described these numbers as using signed sparse digits; that was an error inherited from a research note, and it is corrected here and in the paper.
- **Companion manuscripts** `CompanionC` and `CompanionLambert` are this project's manuscripts in the same release.
- **Unverified:** Wall's 1949 thesis (D. D. Wall, *Normal numbers*, Ph.D. thesis, Berkeley) is mentioned in the text only as "the classical theorem of Wall on normality quoted there", through Bergelson–Downarowicz's attribution; it was not consulted and is not in the bibliography.

---

### Theorem 3.1 (= Theorem A, first part), Proposition 4.1 and Proposition 4.2: sharp translation identity, discrepancy distance, concentration

- **Statement and hypotheses:** for every integer $b\ge2$, real $x,z$ and $N\ge1$: $\lvert D_N(x+z)-D_N(x)\rvert\le1-D_N(z)$, with equality at $x=0$. $d_N(x,y)=1-D_N(x-y)$ is a translation-invariant pseudometric equal to $\max_w\lvert D_N(w+x-y)-D_N(w)\rvert$, vanishing for $N\ge2$ exactly when $(b-1)(x-y)\in\mathbb Z$. For every probability measure $\mu$ on $\mathbb T$, $1-D(\mu)=\inf_l(1-Q_\mu(l)+l)=\inf_{c,r}(\mu(\lVert u-c\rVert>r)+2r)$ and $k(\mu)\le1-D(\mu)\le3k(\mu)$ for the Ky Fan distance $k$ to constants, with sharp constants.
- **Evidence:** 3.1 and 4.1 Kernel-verified (`SharpTranslation.*` at `e4809cf`, `DiscrepancyGeometry.*` at `c2c9da6`); 4.2 Paper proof.
- **Earliest relevant literature:** Lévy, *L'addition des variables aléatoires définies sur une circonférence*, Bull. SMF 67 (1939) 1–41, doi:10.24033/bsmf.1288 (circular concentration function). Ky Fan, Math. Z. 49 (1943) 681–683, doi:10.1007/BF01174225 (metric for convergence in probability). Kuiper, Indag. Math. 63 (1960) 38–47, doi:10.1016/S1385-7258(60)50006-0 (rotation-invariant statistic $V_N=D_N^++D_N^-$). Prokhorov, Theory Probab. Appl. 1 (1956) 157–214, doi:10.1137/1101016.
- **Closest published results:** Kuiper's $V_N$ equals the extreme discrepancy and is rotation invariant by design. $1-D$ is an exact rewriting of the concentration function. Up to a factor $3$ it is the Ky Fan (equivalently, for a point mass, Lévy–Prokhorov) distance to the nearest constant (`notes/phase19/literature.md` §4; the comparison is proved in Proposition 4.2). Perturbation bounds $\lvert D_N(x)-D_N(y)\rvert\le2\epsilon$ under $\lvert x_n-y_n\rvert\le\epsilon$ are standard; no theorem number was verified, so Lemma 2.2 is proved directly.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** different packaging of classical ingredients. No source examined states the exact supremum identity for paired radix orbits or names $1-D_N(x-y)$ as a pseudometric. The paper says explicitly that $d_N$ is not a new probability metric and places the contribution in the exact finite identity, the arithmetic realizations, the rates and the formal verification.
- **Search record:** "change of discrepancy under translation supremum"; "extreme discrepancy translation invariant sequence sum x_n + y_n"; "Kuiper statistic concentration function relation"; "Lévy concentration function circle discrepancy"; "Ky Fan metric point mass Prokhorov distance discrepancy". Databases: arXiv, zbMATH Open, web search. Trails: Kuipers–Niederreiter Ch. 2 §1; Drmota–Tichy LNM 1651 (table of contents only); Gibbs–Su, Int. Stat. Rev. 70 (2002) 419–435 (comparison of probability metrics; not cited).
- **Dependencies and outstanding review:** a specialist in uniform distribution should say whether the identity is folklore (for instance in exercises of Kuipers–Niederreiter Ch. 2 or Drmota–Tichy).

### Theorem 3.3 (= Theorem A, second part) and Remark 3.4: universal numerical discrepancy preservers

- **Statement:** $D_N(z)\to1$ if and only if $z=c+w$ with $(b-1)c\in\mathbb Z$ and $M_N(w)\to0$, if and only if translation by $z$ preserves both limiting discrepancies of every input (and four further equivalent forms). The class is a proper subgroup of Rauzy's class.
- **Evidence:** Lean-supported paper proof ((i)⇔(ii) is Theorem 3.1). The proof of (i)⇒(vi) given here avoids the connectedness of limit sets used in the earlier note; it uses only consecutive-sample comparison (suggested in `notes/phase19/reviews/geometry-periods.md`).
- **Earliest relevant literature:** Rauzy, Acta Arith. 29 (1976) 211–225, doi:10.4064/aa-29-3-211-225: $x+z$ is normal for every normal $x$ if and only if $z$ has zero noise (theorem number not verified; primary text inaccessible, as recorded for manuscript C). Spears–Maxfield (1969), per Bergelson–Downarowicz Remark 3.13.
- **Closest published results:** Bergelson–Downarowicz arXiv:2506.12929v1, Theorem 3.12: $\mathcal D(r)=\mathcal N^\perp(r)$ (deterministic numbers are exactly the normality-preserving translations), with Definitions 3.5 and 3.10. Corollary 4.10(2) (from the summary): $y$ is deterministic iff it preserves lower and upper point entropy of every $x$. None of these mentions numerical discrepancy.
- **Closest unpublished or public-repository results:** Manai, arXiv:2609.24665 (21 September 2026), translations preserving absolute normality (located for manuscript C; not cited).
- **Relation:** a different invariant; apparently new in the sources examined. The class preserving numerical discrepancy is strictly smaller than Rauzy's class ($z=1/3$ in base 2).
- **Search record:** "Rauzy deterministic numbers normality preserving translation"; "translation preserving discrepancy of every sequence"; "mean distance to nearest integer b^n z tends to zero". Trails: Bergelson–Downarowicz §§3–4.
- **Dependencies and outstanding review:** the eventual constancy of the nearest fixed point in (i)⇒(vi).

### Proposition 4.3, Theorem 4.5 and Proposition 4.6 (= Theorem C, second part): asymptotic kernel and rational scalars

- **Statement:** $K_b=\{z:D_N(z)\to1\}$ is the kernel of $d^+=\limsup d_N$ and a subgroup. For reduced $a/d$, $(a/d)K_b\subseteq K_b$ iff every prime of $d$ divides $b$. For $z\in K_b$ with limiting fixed point $c$, $(a/d)z\in K_b$ iff the integers $k_n$ nearest to $b^nz-c$ lie in one residue class modulo $d$ on a set of density one.
- **Evidence:** Proposition 4.3 and Theorem 4.5 are Lean-supported paper proofs: the triangle inequality, translation invariance and integer Lipschitz bound of $d^+$ are Lean declarations (`asymDist_triangle`, `asymDist_translate`, `asymDist_intMul_le`), and Theorem 4.5 uses from Lean only the subgroup property of $K_b$ that follows from them; the description of the kernel (Theorem 3.3), Lemma 4.4 and the valuation argument are written. Proposition 4.6 is a paper proof.
- **Earliest relevant literature:** Wall (1949 thesis) and Maxfield, Pacific J. Math. 3 (1953) 189–196, doi:10.2140/pjm.1953.3.189: rational multiples and translates of normal numbers are normal (per `notes/phase19/literature.md` §5; neither is cited in the paper, which cites Bergelson–Downarowicz Prop. 4.25 instead).
- **Closest published results:** Bergelson–Downarowicz Proposition 4.25 (read verbatim): for every nonzero rational $q$, $\underline h(qx)=\underline h(x)$ and $\overline h(qx)=\overline h(x)$, hence normality and determinism are preserved. Corollary 4.26 (from the summary): $x\mapsto qx+y$ with deterministic $y$ preserves entropy, normality and determinism. The paper cites Proposition 4.25 twice: in the introduction after Theorem D and in the remark after Proposition 4.6.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** apparently new in the sources examined. The contrast is the point: entropy is invariant under all nonzero rational scalings, while the numerical-discrepancy kernel is invariant exactly under $\mathbb Z[1/b]$.
- **Search record:** "rational multiples discrepancy normal numbers preservation"; "multiplication by rational preserves discrepancy radix orbit". Trails: Bergelson–Downarowicz §4.4 (summary).
- **Dependencies and outstanding review:** none beyond Theorem 3.3. The paper states the question for real scalars (Question 7.3).

### Theorems 5.1, 5.3 and 5.4 (= Theorem B): addition spectrum, cubic rate, effective independent witnesses

- **Statement:** triples of limits for $(x,y,x+y)$ are exactly $\max(0,\alpha+\beta-1)\le\gamma\le1-\lvert\alpha-\beta\rvert$; the inequality holds at every finite $N$. For an odd prime $p\nmid b$ each triple is realized on the schedule $tk^3$ by positive $p$-power coefficients with simultaneous error $\le C_{b,p}N^{-1/3}$; the witnesses can be algebraically independent and computed uniformly from names of a computable triple.
- **Evidence:** 5.1 Kernel-verified (`AdditionSpectrum.exact_addition_spectrum`, `finite_necessity`, `addSpectrum_eq`, `mixtureRealizable` at `c2c9da6`). 5.3 and 5.4 Lean-supported paper proofs (step: positive state programming, kernel-verified).
- **Earliest relevant literature:** Kamae, LNM 550 (1976) 253–269, doi:10.1007/BFb0077494: Bergelson–Downarowicz state (remark after Proposition 4.9) that Kamae introduced a notion of point entropy coinciding with their upper entropy and proved inequality (d), $\overline h(x+y)\le\min\{\log r,\overline h(x)+\overline h(y)\}$. Cited in the paper on that attribution only; Kamae's paper was not read.
- **Closest published results:** Bergelson–Downarowicz arXiv:2506.12929v1, **Proposition 4.9** (verbatim, no existence hypothesis): (a) $\max\{0,\underline h(x)-\overline h(y),\underline h(y)-\overline h(x)\}\le\underline h(x+y)$; (b) $\underline h(x+y)\le\min\{\log r,\underline h(x)+\overline h(y),\overline h(x)+\underline h(y)\}$; (c) $\max\{\lvert\underline h(x)-\underline h(y)\rvert,\lvert\overline h(x)-\overline h(y)\rvert\}\le\overline h(x+y)$; (d) $\overline h(x+y)\le\min\{\log r,\overline h(x)+\overline h(y)\}$. **Corollary 4.10(1)** (verbatim): if $h(x),h(y)$ exist, $\lvert h(x)-h(y)\rvert\le\underline h(x+y)\le\overline h(x+y)\le h(x)+h(y)$. §4.3 studies attainability (Examples 4.20–4.23, from the summary). In normalized coordinates these are the same triangle inequalities as the deficit form of Theorem 5.1, so the polytope coincides. Sigmund, Trans. AMS 190 (1974) 285–299: generic points for invariant measures under specification, which with the five vertex laws and weak continuity of $D$ gives the qualitative sufficiency (credited in the introduction).
- **Closest unpublished or public-repository results:** none located.
- **Relation:** a discrepancy counterpart of the entropy polytope, not independent of the Bergelson–Downarowicz precedent, which the paper credits in the introduction. The two observables agree on $\theta\delta_0+(1-\theta)\lambda$ and differ on periodic orbit measures. The finite-$N$ necessity, the one-prime cubic realization with a uniform all-prefix rate, effective algebraic independence and the formal proof appear new in the sources examined.
- **Search record:** "discrepancy of sum of two numbers base b limiting discrepancy triple"; "addition of normal numbers discrepancy polytope"; "point entropy addition inequality sharpness"; trails through Bergelson–Downarowicz §4 and `notes/phase19/literature.md` §1.
- **Dependencies and outstanding review:** the scheduler bound and summation by parts (Lemma 5.2 and the proof of 5.3); the certificate-preservation argument in 5.4.

### Theorem 5.5 and Proposition 5.6: several summands, six forms

- **Statement:** for $d$ summands the deficit vectors $(1-\delta_i)_{i\le d+1}$ are exactly those with each coordinate at most the sum of the others. $D_N(x+y)+D_N(x+z)+D_N(y+z)\le2+2\min(D_N(x),D_N(y),D_N(z))$.
- **Evidence:** 5.5 Lean-supported paper proof (realization by `mixtureRealizable`); 5.6 Paper proof.
- **Closest published results:** the polygon inequalities are the $d$-term analogue of Bergelson–Downarowicz Proposition 4.9(d) and its lower bounds; no $d$-term statement for entropy was checked.
- **Relation:** apparently new in the sources examined for extreme discrepancy. The $d$-summand rate claimed in `notes/phase19/addition.md` is not claimed in the paper.
- **Search record:** inherited from `notes/phase19/literature.md` §1.
- **Dependencies and outstanding review:** the convex-hull argument; the attainment remark in base 3 relies on Sigmund's theorem.

### Proposition 6.1 and Theorem 6.2 (= Theorem D): integer dilation

- **Statement:** $\max(0,1-\lvert m\rvert(1-D_N(x)))\le D_N(mx)\le\min(1,\lvert m\rvert D_N(x))$. If $D_N(mx)\to1$ then $\liminf D_N(x)\ge1/m_0$, and every $\delta\in[1/m_0,1]$ occurs, at rate $O(N^{-1/3})$.
- **Evidence:** Lean-supported paper proofs (lower bound `discDist_intMul_le`; programming lemma). In Theorem 6.2(b) the divisibility $\mathrm{den}\,c_k\mid m_0$ uses the written $\mathrm{lcm}$ remark after Lemma 2.5, because the Lean declaration `programCoeffs_den_dvd` gives only the product bound. An exact rational check of the cubic schedule is `papers/10-discrepancy-arithmetic/checks/cubic_boundary_check.py`.
- **Earliest relevant literature:** Wall (1949), Maxfield (1953) for qualitative invariance of normality (per `notes/phase19/literature.md` §5).
- **Closest published results:** the upper bound $D_N(mx)\le\lvert m\rvert D_N(x)$ is elementary and presumably folklore (`notes/phase19/literature.md` §5 classifies it so). Bergelson–Downarowicz Prop. 4.25: entropy is invariant under rational dilation.
- **Relation:** the exact boundary spectrum $[1/m_0,1]$ appears new in the sources examined. The inverse dilation estimate of `notes/phase19/geometry.md` is not included.
- **Search record:** "discrepancy of m x_n integer multiple sequence modulo one bound"; "dilation discrepancy normal numbers".
- **Dependencies and outstanding review:** part (a) uses Theorems 3.3 and 4.5.

### Proposition 6.3: a product of sparse preservers

- **Statement:** for the Moser–de Bruijn set $A$ and $r\ge2$, $U=\sum_{a\in A}b^{-ra}$, $V=\sum_{a\in A}b^{-2ra}$ are irrational elements of $K_b$ with $M_N\to0$ and translation rate $O(\log N/\sqrt N)$, and $UV=b^r/(b^r-1)\notin K_b$.
- **Evidence:** Paper proof.
- **Earliest relevant literature:** Moser (1962) and de Bruijn (1964) for the decomposition (per `notes/phase19/reviews/geometry-periods.md`; not cited).
- **Closest published results:** Bergelson–Downarowicz arXiv:2506.12929v1, Theorem 8.11, Proposition 8.13 and Corollary 8.14 (read in the arXiv text; ordinary binary digits): in base 2, a number $a=xy$ whose expansion has density zero of digit switches and a number $b=1/y$ whose expansion has density zero of ones, with $ab=x$ normal. Both lie in the mean-zero subgroup ($M_N\to0$), since each maximal constant run of digits, respectively each digit 1, contributes $O(1)$ to $\sum_{n<N}\lVert2^nw\rVert$; so their example is a stronger statement of the same kind in base 2, credited in the paper.
- **Relation:** an every-base example with an explicit rational product and an explicit rate for the factors, by a short Moser–de Bruijn argument; in base 2 it is weaker than the Bergelson–Downarowicz example. Neither uses signed digits. The sharp missing-digit rates $(\log N/N)^{1-\sigma}$ of the research note are not claimed.
- **Search record:** trails through Bergelson–Downarowicz §8, read in the arXiv text during the revision of 25 November 2026.
- **Dependencies and outstanding review:** none.

### Theorem 3.5 and Proposition 3.6: sparse translations

- **Statement:** adding $\sum2^{-k(k+1)}$ changes binary discrepancy by at most $4\cdot2^{-w}+w\lfloor\sqrt{N+w}\rfloor/N$ (kernel-verified), hence $O(N^{-1/2}\log N)$; the factorial remainder is Liouville with rate $O(N^{-1}\log^2N)$.
- **Evidence:** Lean-supported paper proofs.
- **Literature:** Rauzy (1976) for qualitative preservation; Spears–Maxfield (1969) for density-one periodic digit sequences (per Bergelson–Downarowicz Remark 3.13).
- **Relation:** quantitative refinements of qualitative facts; simple. These statements moved here from manuscript C; they are not stated in any other manuscript.
- **Search record:** "normal number plus sparse series discrepancy rate".

## Material assessed and not included

- Finite rational linear forms, polyhedral approximation of their joint spectra (`notes/phase19/addition.md`), joint box rates (`notes/phase19/joint-rate.md`): different techniques (word flows, multidimensional exponential sums); listed as further work in §5.3 and Question 7.2.
- The $d$-summand rate and the Haar-mixture rates (review O3 of `notes/phase19/reviews/addition.md` notes super-polynomial constants for a Liouville direction).
- Inverse dilation estimate, radix-power kernels $K_{a^r}\cap K_{a^s}$ (`notes/phase19/geometry.md`).
- Sharp missing-digit translation rates (`notes/phase19/products-of-remainders.md`).
