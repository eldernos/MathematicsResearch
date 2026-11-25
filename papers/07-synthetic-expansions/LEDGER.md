# Claim-to-source novelty ledger: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v1.0)

No search proves novelty. "Apparently new in the sources examined" means only that the sources listed here, read as described, did not contain the statement.

The searches combined three things:

1. Direct web and database queries made for this manuscript on 25 November 2026. Their exact formulations are listed under each item.
2. The primary-source audits in `notes/phase18/sources.md`, `notes/phase18/reviews/classical-sources.md` (both at `e4809cf`) and `notes/phase19/literature.md` (at `c2c9da6`).
3. Reference trails in Kano (1993), Bailey–Crandall (2002), Vandehey (2019, arXiv version), Bergelson–Downarowicz (2025) and Kuipers–Niederreiter (1974).

**Split of 25 November 2026.** The ledger entries for the sharp translation identity, the discrepancy pseudometric, the preserver classification, the addition spectrum and the sparse and Lambert remainders moved with those theorems to manuscript H (`papers/10-discrepancy-arithmetic/LEDGER.md`). This paper quotes the identity once (Theorem 2.6). The entry for the quadratic-image theorem (Section 7) is new.

MathSciNet was not accessible. zbMATH Open, arXiv, Crossref, Google-indexed web search, and the publishers' and repositories' pages were used. The Lean statements were checked at the pinned commits. Every written proof, and every comparison below, has been checked only by AI models; none has been checked by an independent human expert.

## Bibliography verification

**Verified against Crossref metadata** (title, authors, journal, volume, pages, year, DOI), on 25 November 2026:

- Stoneham 1973; Korobov 1972; Kano–Shiokawa 1993; Wagner 1995; Bailey–Crandall 2001 and 2002;
- Vandehey 2019 (journal record; the arXiv abstract page confirms v1 of 25 June 2016 with no journal reference);
- Colebrook 1970; Sigmund 1974; Denker–Grillenberger–Sigmund 1976; Bugeaud 2002;
- Becher–Heiber–Slaman 2015; Levin 1999; Aistleitner–Becher–Scheerer–Slaman 2017;
- Parthasarathy 1961 (Crossref omits pages; pages 648–656 are taken from `notes/phase19/literature.md`);
- de Moura–Ullrich 2021; the mathlib Community 2020.

**Verified by other means:**

- Kano 1993: the DOI `10.18910/10356` resolves to the Osaka institutional repository, whose PDF title page was read.
- Kuipers–Niederreiter 1974: the publisher (John Wiley & Sons, 1974) and the theorem numbers and pages were checked against a text copy of the book.
- Graham–Kolesnik 1991: publisher, series, volume, year and DOI 10.1017/CBO9780511661976 confirmed through the Cambridge catalogue record and a library record (ISBN 9780511661976); the numbering of Lemma 2.5 and Theorem 2.2 was confirmed only through a secondary citation (arXiv:2307.03562). The book text was not read.

**Public repositories:** the bibliography entries `SudeSum` (Captain Sude, `Stoneham-sum-normal` at commit `f4d3d1f0`) and `MiraJoint` (Mira Cult, `stoneham-joint-normality.md` at commit `357d26a2`) point to pinned commits. Both URLs returned HTTP 200 on 25 November 2026. They are cited in the introduction as related public work, not as inputs.

**Companion manuscripts:** the companion entries (`PaperI`, `PaperIII`, `CompanionH`) are this project's own manuscripts. `CompanionH` is in the same release.

**Unverified items:** the Erdős–Turán theorem number in Kuipers–Niederreiter (Ch. 2, Thm 2.5, p. 112) is the standard citation and was not re-checked against the text in this worktree. Sigmund's and Colebrook's theorem numbers were not verified either: AMS returned 403 and Project Euclid returned an empty page. The paper cites both only as related work, not as inputs. `notes/phase19/literature.md` reports that Sigmund (1974, p. 285) credits Colebrook.

---

### Theorem 4.5 (= Theorem A): normality switch

- **Statement and hypotheses:** $b\ge2$; $p$ prime with $p\nmid b$; $t=\mathrm{ord}_p(b)$; $s\ge0$ an integer; $(n_k)$ strictly increasing positive multiples of $t$ with $n_k\ge k^2$. Then $X_s=\sum_k p^{-sv_p(k)}b^{-n_k}$ has $D_N(X_0)\to1$, and $D_N(X_s)\to0$ for $s\ge1$.
- **Evidence:** Kernel-verified: `RetirementDenominator.discrepancy_switch`, `normal_iff_pos` and `polynomial_discrepancy_switch` at `e4809cf`.
- **Earliest relevant literature:** Stoneham, Acta Arith. 22 (1973) 277–286, doi:10.4064/aa-22-3-277-286. Korobov, Math. USSR-Sb. 18 (1972) 659–676, doi:10.1070/SM1972v018n04ABEH001870.
- **Closest published results:**
  - Kano, Osaka J. Math. 30 (1993) 909–919, Theorem 1: a normality criterion for series $\sum A_n/(a^{\mu_n}b^{\lambda_n})$ with growing $\mu_n,\lambda_n$. Its introduction records Stoneham's Theorem 1, which uses prescribed numerators $Z_n<a^n$.
  - Bailey–Crandall 2002, Theorem 4.8: normality of $(b,c,m,n)$-series under growth conditions on the increments.
  - Vandehey, arXiv:1606.07911, Theorem 7.4: $\sum 1/(c_kb^{m_k})$ is normal when the $c_k$ are supported on a fixed finite prime set, $c_k\mid c_{k+1}$, and the gaps satisfy $\exp((1+\epsilon)\log c_k/\log\log c_k)/\mu_k\to0$.
- **Closest unpublished or public-repository results:**
  - Mira Cult, joint normality of $\sum_j p^{-sj}b^{-p^j}$: [stoneham-joint-normality.md @357d26a](https://github.com/Mira-Cult/math/blob/357d26a23fbbee5c900098938744ab732b84d03a/notes/number-theory/normal-numbers/stoneham-joint-normality.md).
  - Captain Sude: [Stoneham-sum-normal @f4d3d1f](https://github.com/CaptainSude/Stoneham-sum-normal/tree/f4d3d1f01d00c57425c684409849053e58e42261) and [stoneham-prime-support @5919ad4](https://github.com/CaptainSude/stoneham-prime-support).
  - These concern classical Stoneham schedules $p^j$, not valuation weights on arbitrary schedules.
- **Relation:** different weights; specializes known machinery. Normality for $s\ge1$ on these schedules is close to the Korobov–Stoneham–Vandehey criteria, but the valuation weights $p^{-sv_p(k)}$ do not form a divisibility chain, and Theorem 7.4 of Vandehey does not apply verbatim. The sharp switch to $D_N\to1$ at $s=0$, for every schedule dominating $k^2$, together with the kernel proof, appears new in the sources examined. The mathematical content is modest.
- **Search record:**
  - Phrasings: "sparse series normal number valuation weight"; "Korobov type normal numbers $p$-adic valuation coefficient"; "Stoneham number generalization sparse exponent schedule normal"; "normal numbers of Korobov type general construction". The earlier Phase 18 searches are recorded in `notes/phase18/sources.md` §1–2.
  - Databases: arXiv, zbMATH Open, web search.
  - Trails followed: Kano's introduction; the reference list of Bailey–Crandall 2002; Vandehey §7.
- **Dependencies and outstanding review:** a specialist should confirm that the switch is not an immediate corollary of Kano's Theorem 1 or of Bailey–Crandall's Theorem 4.8 after regrouping. The internal assessment is that it is not, because the denominators $p^{s\lfloor\log_p K\rfloor}$ fail the chain and growth hypotheses.

### Theorem 4.2: exact reduced denominators

- **Statement and hypotheses:** for $n\ge n_K$, $\mathrm{den}(b^nU_K)=p^{s\lfloor\log_pK\rfloor}$.
- **Evidence:** Kernel-verified: `shiftedPrefix_den` and `fullPrefix_den`.
- **Earliest relevant literature:** Korobov (1972) and Stoneham (1973) on periods of rationals.
- **Closest published results:** none states this identity. It is an elementary counting argument modulo $p$.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** apparently new in the sources examined, and elementary.
- **Search record:** included in the searches for Theorem 4.5.
- **Dependencies and outstanding review:** none. The statement is fully formal.

### Theorems 3.1 and 4.7 (= Theorem B): complete-period rates

- **Statement and hypotheses:** for odd $p$, $s\ge1$ and $d\ge s+2$, $D_N(X_s)\ll N^{-s/d}+N^{-(d-s-1)/d}+N^{-(d-1)/d}\log N$; for $\xi=\sum 3^{-v_3(k)}2^{-2k^3}$, $D_N(\xi;2)\le200N^{-1/3}$.
- **Evidence:** Lean-supported paper proof (Theorem 4.2) for 4.7; paper proof for 3.1.
- **Earliest relevant literature:** Korobov (1972), *On the distribution of digits in periodic fractions*: complete- and incomplete-period digit counts.
- **Closest published results:**
  - Levin, Acta Arith. 88 (1999) 99–111: an explicit normal number with $D_N=O((\log N)^2/N)$.
  - Aistleitner–Becher–Scheerer–Slaman, Acta Arith. 180 (2017) 333–346: computable absolutely normal numbers with discrepancy of order $N^{-1/2}$ in every base (as stated in their abstract).
  - Vandehey's Corollary 1.2 gives power savings for incomplete Korobov sums, $\lvert\sum_{n\le N}e(ab^n/m)\rvert\le C m^{-\delta}N(1+\log m)$ for $N\ge m^\epsilon$, with $\delta=\delta(\epsilon)$ and $C=C(\epsilon,b,P)$. The arXiv text states that $K_1,K_2,K_3$ "depend only on $P$", although the displayed formulas contain $b$.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** much weaker rates than Levin and ABSS, for specific arithmetic numbers, by elementary means. Rates for these particular families appear new in the sources examined.
- **Search record:** "discrepancy estimate Stoneham number rate"; "normal number explicit discrepancy $N^{-1/3}$"; "Korobov sums complete periods discrepancy sparse series". Databases: arXiv and web search. Trails: Levin (1999) and ABSS (2017) references.
- **Dependencies and outstanding review:** check the constant $200$ (proof in §3), and check whether Vandehey's Corollary 1.2 gives a better rate for these families. The paper explicitly does not claim this; see the remark after Theorem 4.7.

### Corollary 4.6: normal Liouville family

- **Statement:** $\sum p^{-sv_p(k)}b^{-t(k+1)!}$ is normal for $s\ge1$, and it is a Liouville number.
- **Evidence:** Lean-supported paper proof.
- **Earliest relevant literature and closest results:**
  - Kano–Shiokawa, Israel J. Math. 84 (1993) 403–416: rings of normal numbers whose irrational elements are Liouville (Remark 2, per `notes/phase18/sources.md`).
  - Bailey–Crandall 2002, Theorem 4.8, which covers superexponential schedules.
  - Bugeaud, C. R. Math. 335 (2002) 117–120: absolutely normal Liouville numbers exist.
  - Becher–Heiber–Slaman, Math. Comp. 84 (2015) 2939–2952: a computable absolutely normal Liouville number.
  - Martin, Amer. Math. Monthly 108 (2001): a Liouville number that is normal in no base (contrast).
- **Relation:** inherited and specialized. This is a further explicit example; there is no novelty claim.
- **Search record:** inherited from `notes/phase18/sources.md` §4; also "normal Liouville number explicit construction".

### Theorems 5.3, 6.1 and 6.4 (= Theorem C): prescribed limits, pairs and limit sets

- **Statement:** every $\delta\in[0,1]$ is attained with error $C_{b,p}N^{-1/3}$, uniformly in $\delta$, by positive $p$-power-denominator coefficients on $tk^3$. Every pair $(\alpha,\beta)$ is attained. Every nonempty compact connected set of invariant measures is a limit set, realized on $k^3$.
- **Evidence:** Lean-supported paper proof (Lemma 5.1 is kernel-verified).
- **Earliest relevant literature:**
  - Volkmann, Math. Z. 68 (1957), per `notes/phase19/literature.md`.
  - Colebrook, Michigan Math. J. 17 (1970) 103–116.
  - Sigmund, Trans. AMS 190 (1974) 285–299.
  - Denker–Grillenberger–Sigmund, LNM 527 (1976).
- **Closest published results:**
  - Colebrook and Sigmund: every nonempty closed connected set of shift-invariant measures is the limit set of some point of the full shift or a specification system. The theorem numbers were not verified here; see the bibliography notes.
  - Parthasarathy 1961: periodic measures are dense.
  - Winkler, Math. Nachr. 186 (1997) 303–312: sets of distribution functions of arbitrary sequences.
  - By weak continuity of $D$ (Lemma 6.3), these results already give every $\delta$ and every pair qualitatively.
  - The repository's Paper III (v1.1) gives the restricted spectrum of signed Stoneham shells.
- **Closest unpublished or public-repository results:** none located beyond this project.
- **Relation:** strengthens the classical results in a different direction. They are qualitative symbolic realizations; what appears new in the sources examined is realization by positive rational coefficients on one arithmetic schedule with an explicit all-prefix rate, uniform in $\delta$.
- **Search record:** "numbers with prescribed limiting discrepancy"; "prescribed lower and upper discrepancy $b^nx$"; "limit set empirical measures radix expansion compact connected"; "Colebrook nonnormal numbers limit points measures". Databases: arXiv, web search and zbMATH. Trails: Sigmund (1974) references, and `notes/phase19/literature.md` §2–3.
- **Dependencies and outstanding review:** the summation-by-parts bound (2), and the chain construction in Theorem 6.4.

### Theorem 7.1 and Corollary 7.2 (= Theorem D): quadratic images

- **Statement and hypotheses:** $p\nmid b$ an odd prime, $t=\mathrm{ord}_p(b)$, $d\ge3$, $X_a=\sum_{i\ge1}p^{-av_p(i)}b^{-ti^d}$ for integers $a\ge1$. For every finite $S\subset\mathbb Z_{>0}$ and every nonconstant $P\in\mathbb Q[z_a:a\in S]$ of total degree at most two, $P((X_a))$ is normal to base $b$. Hence every rational quadratic in $X_s$ ($s\ge1$) is normal, the distinct nonconstant monomials of degree $\le2$ are jointly normal, $\xi^2$ is normal and $(\xi,\xi^2)$ is jointly normal for $\xi=X_1$ with $(b,p,d)=(2,3,3)$.
- **Evidence:** Paper proof (not formalized). Inputs: the all-prefix criterion (Proposition 4.4, Lean-supported through the kernel-verified short-orbit estimate), the exact denominator (Theorem 4.2, kernel-verified), the Weyl–van der Corput inequality and second-derivative test (Graham–Kolesnik, Lemma 2.5 and Theorem 2.2), the Erdős–Turán inequality (Kuipers–Niederreiter Ch. 2 Thm 2.5), the Lebesgue density theorem. Source: `notes/phase19/nonlinear.md` at `c2c9da6`; independent AI audit `notes/phase19/reviews/nonlinear.md` (verdict: all estimates close; presentation objections O1–O5, all addressed in the written proof; see `VERIFICATION.md`, "Audit of the quadratic-image proof").
- **Earliest relevant literature:** Kano–Shiokawa, *Rings of normal and nonnormal numbers*, Israel J. Math. 84 (1993) 403–416, doi:10.1007/BF02760950; Wagner, J. Number Theory 54 (1995) 211–231, doi:10.1006/jnth.1995.1114 (rings of numbers normal to one base). Their scope is taken from `notes/phase18/sources.md` §1 (Kano–Shiokawa Remark 2: irrational elements of their rings are Liouville); the publisher pages were behind a login on 25 November 2026 and were not re-read.
- **Closest published results:** Kano–Shiokawa and Wagner construct rings, closed under polynomial operations, by different generators and schedules; Paper I (this project, v1.1) treats polynomial images of the standard Stoneham numbers $\alpha_{b,p}$. Bailey–Crandall and Vandehey give linear normality criteria only. No source examined treats squares of valuation-weighted series on a polynomial schedule.
- **Closest unpublished or public-repository results:** Captain Sude, [xi-family @f0f9912](https://github.com/CaptainSude/xi-family/tree/f0f991216abd7fd5af9157f43281faca9671938a) (rational combinations in $\xi$-families, linear only); Mira Cult, joint normality of Stoneham series (linear forms). Neither treats products.
- **Relation:** apparently new in the sources examined, for these specific numbers. The result does not construct a ring and is limited to total degree two; cubes are open (Remark 7.9).
- **Search record:** "square of a normal number normal Stoneham"; "polynomial of normal number normal Korobov type"; "normal numbers ring polynomial closure Kano Shiokawa"; "joint normality x and x^2". Databases: arXiv, zbMATH Open, web search. Trails: `notes/phase18/sources.md` §1, `notes/phase19/literature.md`, the reference lists of Kano (1993) and Bugeaud (2012, monograph, table of contents only).
- **Dependencies and outstanding review:** a specialist should check (1) the collision bound (3) in Lemma 7.7, in particular the uniformity of the error terms in $I$ and the lattice count of the slab; (2) the third-derivative estimate in the regime $\lambda=lp^H\Lambda/p^{3v}$, $2H/5\le v\le H$; (3) the second-moment step in Proposition 7.8; (4) the freezing threshold and the failed-cell density in the proof of Theorem 7.1. The earlier finite bound $\limsup D_N(\xi^2)<2.94\cdot10^{-10}$ (registry SY-20) is superseded and appears only as a historical remark (7.3).

### Theorems 8.2–8.4 (= Theorem E): infinite sums

- **Statement:** $Y=\sum_{\ell\text{ odd prime}}\sum_j\ell^{-s_\ell j}2^{-16^{\ell^j}}$, with $s_3=2$, is normal and Liouville with $D_N\ll1/\log N$. Finite rational combinations of the components are normal. Positive rational multiples of the components can sum to any $R>0$.
- **Evidence:** Lean-supported paper proofs. The grid order and count steps are Lean (`SurvivingGrid.stride_order`, `PrimePowerGrid.crt_period_count` at `c2c9da6`), and the existence of the multipliers is Lean (`hasSum_positive_rational_multiples` at `e4809cf`).
- **Earliest relevant literature:**
  - Korobov (1972) on periods.
  - Kano (1993), Theorem 1: a fixed denominator base $a$.
  - Vandehey, Theorem 7.4: a fixed finite prime set.
  - Bailey–Crandall 2002, Theorem 4.8 (composite coprime $c$).
- **Closest published results:**
  - None of these allows the reduced prefix to acquire every odd prime.
  - Bailey–Borwein (2012) ask whether $\alpha_{b,c}+\alpha_{b,d}$ is normal; per `notes/phase18/sources.md`.
  - Boonstra–Kalle, arXiv:2402.14500 (located by search): digit-expansion constructions that permit infinite sums. Its scope was not examined in detail.
- **Closest unpublished or public-repository results:**
  - Captain Sude, [Stoneham-sum-normal](https://github.com/CaptainSude/Stoneham-sum-normal/tree/f4d3d1f01d00c57425c684409849053e58e42261): normality of $\alpha_{b,c}+\alpha_{b,d}$.
  - Captain Sude, [xi-family](https://github.com/CaptainSude/xi-family/tree/f0f991216abd7fd5af9157f43281faca9671938a): rational combinations in $\xi$-families on finite supports.
  - Mira Cult (link above): finite joint normality of Stoneham series. This overlaps Theorem 8.3 in spirit, but for different series.
- **Relation:** apparently new in the sources examined, for the all-odd-prime normal Liouville series with an explicit rate. The finite joint normality (8.3) has the same flavour as Mira Cult's and Captain Sude's results for Stoneham series, and is credited. The rational-total counterexample is elementary.
- **Search record:** "sum of infinitely many Stoneham numbers normal"; "normal number infinitely many denominator primes series"; trails in `notes/phase19/grids.md` §7 and `literature.md`.
- **Dependencies and outstanding review:** the bound $c\le1+J_3$ through $v_3(\ell-1)<\log_3L$, which is valid (no prime-5 argument is used); the elementary bound $\prod_{\ell\le x}\ell<4^x$; and the CRT Liouville argument.

### Proposition 8.5: consecutive tails

- **Statement:** for a convergent series of normal numbers with tails $E_k$, $\overline M(E_k)+\overline M(E_{k+1})\ge1/4$ and $\limsup_N(D_N(E_k)+D_N(E_{k+1}))\le1$.
- **Evidence:** Lean-supported paper proof; the second inequality uses the quoted kernel-verified Theorem 2.6 (manuscript H, Theorem 3.1).
- **Relation:** elementary. The second inequality replaces the base-2 statement of the earlier draft and holds in every base.

## Moved to manuscript H

Sharp translation identity, transfer corollary, discrepancy pseudometric, universal preservers and the comparison with Rauzy, addition spectrum with rate and $d$ summands, quadratic and factorial sparse remainders. Their ledger entries, extended by the novelty audit for manuscript H (Kuiper, Lévy, Ky Fan, Prokhorov; Bergelson–Downarowicz Prop. 4.9 and Cor. 4.10(1)), are in `papers/10-discrepancy-arithmetic/LEDGER.md`. The Lambert-remainder corollary was dropped: its content is Corollary 1.2 of the multiplicative Lambert manuscript (`papers/06-multiplicative-lambert`), so stating it here would duplicate a theorem.
