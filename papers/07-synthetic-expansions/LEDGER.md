# Claim-to-source novelty ledger: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v1.0)

No search proves novelty. "Apparently new in the sources examined" means only that the sources listed here, read as described, did not contain the statement.

The searches combined three things:

1. Direct web and database queries made for this manuscript on 25 November 2026. Their exact formulations are listed under each item.
2. The primary-source audits in `notes/phase18/sources.md`, `notes/phase18/reviews/classical-sources.md` (both at `e4809cf`) and `notes/phase19/literature.md` (at `c2c9da6`).
3. Reference trails in Kano (1993), Bailey–Crandall (2002), Vandehey (2019, arXiv version), Bergelson–Downarowicz (2025) and Kuipers–Niederreiter (1974).

MathSciNet was not accessible. zbMATH Open, arXiv, Crossref, Google-indexed web search, and the publishers' and repositories' pages were used. The Lean statements were checked at the pinned commits. Every written proof, and every comparison below, has been checked only by AI models; none has been checked by an independent human expert.

## Bibliography verification

**Verified against Crossref metadata** (title, authors, journal, volume, pages, year, DOI), on 25 November 2026:

- Stoneham 1973; Korobov 1972; Kano–Shiokawa 1993; Wagner 1995; Bailey–Crandall 2001 and 2002;
- Vandehey 2019 (journal record; the arXiv abstract page confirms v1 of 25 June 2016 with no journal reference);
- Rauzy 1976; Colebrook 1970; Sigmund 1974; Denker–Grillenberger–Sigmund 1976; Bugeaud 2002;
- Becher–Heiber–Slaman 2015; Levin 1999; Aistleitner–Becher–Scheerer–Slaman 2017;
- Kuiper 1960; Lévy 1939 (Crossref gives title, pages 1–41, year and DOI; its volume field is inconsistent, so the volume is omitted from the bibliography); Parthasarathy 1961 (Crossref omits pages; pages 648–656 are taken from `notes/phase19/literature.md`);
- de Moura–Ullrich 2021; the mathlib Community 2020.

**Verified by other means:**

- Kano 1993: the DOI `10.18910/10356` resolves to the Osaka institutional repository, whose PDF title page was read.
- Kuipers–Niederreiter 1974: the publisher (John Wiley & Sons, 1974) and the theorem numbers and pages were checked against a text copy of the book.
- Bergelson–Downarowicz: the arXiv record and the text of v1 were read, including Definitions 3.5 and 3.10 and Theorems 3.12, 8.1 and 8.2, and Corollary 8.14.

**Companion manuscripts:** the companion entries (`PaperI`, `PaperIII`, `CompanionLambert`) are this project's own manuscripts. `CompanionLambert` is not yet released, and its title is provisional.

**Unverified items:** Rauzy's internal theorem number. The primary text could not be accessed: the publisher's PDF returned HTTP 403, the EuDML certificate had expired, and the Numdam announcement is a scan without a text layer. The paper therefore cites Rauzy (1976) for the characterization without a theorem number, and gives Bergelson–Downarowicz Theorem 3.12 for the precise modern statement. Sigmund's and Colebrook's theorem numbers were not verified either: AMS returned 403 and Project Euclid returned an empty page. The paper cites both only as related work, not as inputs. `notes/phase19/literature.md` reports that Sigmund (1974, p. 285) credits Colebrook.

---

### Theorem 4.4 (= Theorem A): normality switch

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
- **Search record:** included in the searches for Theorem 4.4.
- **Dependencies and outstanding review:** none. The statement is fully formal.

### Theorems 3.1 and 4.6 (= Theorem B): complete-period rates

- **Statement and hypotheses:** for odd $p$, $s\ge1$ and $d\ge s+2$, $D_N(X_s)\ll N^{-s/d}+N^{-(d-s-1)/d}+N^{-(d-1)/d}\log N$; for $\xi=\sum 3^{-v_3(k)}2^{-2k^3}$, $D_N(\xi;2)\le200N^{-1/3}$.
- **Evidence:** Lean-supported paper proof (Theorem 4.2) for 4.6; paper proof for 3.1.
- **Earliest relevant literature:** Korobov (1972), *On the distribution of digits in periodic fractions*: complete- and incomplete-period digit counts.
- **Closest published results:**
  - Levin, Acta Arith. 88 (1999) 99–111: an explicit normal number with $D_N=O((\log N)^2/N)$.
  - Aistleitner–Becher–Scheerer–Slaman, Acta Arith. 180 (2017) 333–346: computable absolutely normal numbers with discrepancy of order $N^{-1/2}$ in every base (as stated in their abstract).
  - Vandehey's Corollary 1.2 gives power savings for incomplete Korobov sums, $\lvert\sum_{n\le N}e(ab^n/m)\rvert\le C m^{-\delta}N(1+\log m)$ for $N\ge m^\epsilon$, with $\delta=\delta(\epsilon)$ and $C=C(\epsilon,b,P)$. The arXiv text states that $K_1,K_2,K_3$ "depend only on $P$", although the displayed formulas contain $b$.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** much weaker rates than Levin and ABSS, for specific arithmetic numbers, by elementary means. Rates for these particular families appear new in the sources examined.
- **Search record:** "discrepancy estimate Stoneham number rate"; "normal number explicit discrepancy $N^{-1/3}$"; "Korobov sums complete periods discrepancy sparse series". Databases: arXiv and web search. Trails: Levin (1999) and ABSS (2017) references.
- **Dependencies and outstanding review:** check the constant $200$ (proof in §3), and check whether Vandehey's Corollary 1.2 gives a better rate for these families. The paper explicitly does not claim this; see the remark after Theorem 4.6.

### Corollary 4.5: normal Liouville family

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

### Theorem 7.1 (= Theorem D, first part) and Proposition 7.3: sharp translation identity and discrepancy distance

- **Statement:** $\sup_x\lvert D_N(x+z)-D_N(x)\rvert=1-D_N(z)$, attained at $0$. $d_N(x,y)=1-D_N(x-y)$ is a translation-invariant pseudometric, vanishing for $N\ge2$ exactly when $(b-1)(x-y)\in\mathbb Z$.
- **Evidence:** Kernel-verified (`SharpTranslation.*` at `e4809cf`; `DiscrepancyGeometry.*` at `c2c9da6`).
- **Earliest relevant literature:**
  - Lévy, Bull. SMF (1939) 1–41, doi:10.24033/bsmf.1288: the circular concentration function.
  - Kuiper, Indag. Math. 63 (1960) 38–47: the circular statistic $V_N$, which equals the extreme discrepancy.
- **Closest published results:**
  - The identity $1-D(\mu)=\inf_l(1-Q_\mu(l)+l)$ is an elementary reformulation in terms of Lévy's concentration function.
  - `notes/phase19/literature.md` shows that $1-D(\mu)$ is a sum-form Ky Fan or Lévy–Prokhorov distance to the nearest point mass, comparable within constant factors to $\inf_c\pi(\mu,\delta_c)$.
  - Gibbs and Su, Int. Stat. Rev. 70 (2002) 419–435, doi:10.1111/j.1751-5823.2002.tb00178.x, compare discrepancy and Prokhorov metrics; this was located by search but is not cited in the paper.
  - Perturbation bounds of the form $\lvert D_N(x)-D_N(y)\rvert\le2\epsilon$ when $\lvert x_n-y_n\rvert\le\epsilon$ are standard. No theorem number was verified, so the paper proves its Lemma 2.2 directly.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** different packaging of classical ingredients. No source examined states the sharp supremum identity for paired radix orbits, or names $1-D_N(x-y)$ as a pseudometric. This must not be presented as a new probability metric, and the paper presents it as an exact identity with a short proof.
- **Search record:** "discrepancy of x+z translation sup over x change of discrepancy"; "Lévy concentration function circle arc discrepancy relation Lévy–Prokhorov distance point mass". Databases: web search and arXiv. Trails: `notes/phase19/literature.md` "Executive priority warnings" item 2.
- **Dependencies and outstanding review:** a specialist in uniform distribution should say whether the identity is folklore, for instance in Kuipers–Niederreiter Ch. 2 exercises or the Drmota–Tichy LNM 1651.

### Theorem 7.4 (= Theorem D, second part): universal numerical discrepancy preservers

- **Statement:** $D_N(z)\to1$ if and only if $z=c+w$ with $(b-1)c\in\mathbb Z$ and $M_N(w)\to0$, and this is equivalent to preservation of both limiting discrepancies for every input.
- **Evidence:** paper proof.
- **Earliest relevant literature:** Rauzy, Acta Arith. 29 (1976) 211–225: $x+z$ is normal for every normal $x$ if and only if $z$ has zero noise. The theorem number is not verified; see the bibliography notes. Spears–Maxfield (1969), per Bergelson–Downarowicz Remark 3.13. Kamae (1973).
- **Closest published results:** Bergelson–Downarowicz arXiv:2506.12929v1:
  - Theorem 3.12: "A real number $y$ is deterministic in base $r$ if and only if, for any $x\in\mathcal N(r)$ one has $x+y\in\mathcal N(r)$".
  - Definitions 3.5 and 3.10 set up the entropy formulation.
  - Section 8: Theorem 8.1 gives normal $x$ and deterministic $y\ne0$ with $xy$ deterministic; Corollary 8.14 says that a product of deterministic numbers need not be deterministic.
  - The word "discrepancy" does not occur in the parts read.
  - Manai, arXiv:2609.24665 (21 September 2026), treats translations preserving absolute normality.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** a different invariant. Rauzy's class preserves normality; the class here preserves numerical discrepancy. It is a strictly smaller subgroup (Remark 7.5, $z=1/3$ in base 2). Apparently new in the sources examined.
- **Search record:** "Rauzy deterministic numbers normality preserving translation"; "preservation of discrepancy under addition normal numbers". Trails: Bergelson–Downarowicz §§3–4 and Manai §3.
- **Dependencies and outstanding review:** the connectedness argument in (i)⇒(vi).

### Theorems 8.1–8.3 (= Theorem E): addition spectrum

- **Statement:** the triples of limits for $(x,y,x+y)$ are exactly those with $\max(0,\alpha+\beta-1)\le\gamma\le1-\lvert\alpha-\beta\rvert$. Each is realized at rate $O(N^{-1/3})$ by one-prime cubic positive expansions. For $d$ summands the deficit vectors are exactly the "polygon" vectors.
- **Evidence:** Kernel-verified qualitative statement (`AdditionSpectrum.exact_addition_spectrum` at `c2c9da6`). The rate is a Lean-supported paper proof. The $d$-summand case is a Lean-supported paper proof, with realization by `mixtureRealizable`.
- **Earliest relevant literature:** Kamae, LNM 550 (1976) 253–269, doi:10.1007/BFb0077494, for subadditivity of upper point entropy (per Bergelson–Downarowicz §4.2).
- **Closest published results:**
  - Bergelson–Downarowicz arXiv:2506.12929v1, Proposition 4.9 and Corollary 4.10: $\lvert h(x)-h(y)\rvert\le\underline h(x+y)\le\overline h(x+y)\le\min(\log r,h(x)+h(y))$. In normalized coordinates these are the same triangle inequalities and give the same five-vertex polytope, with sharpness in §4.3. This statement is taken from `notes/phase19/literature.md` and the arXiv HTML; Proposition 4.9 itself was not re-read for this manuscript.
  - Entropy and $1-D$ coincide on the mixtures $\theta\delta_0+(1-\theta)\lambda$ but differ in general.
  - Sigmund's specification theorem gives qualitative generic points for every invariant torus law.
- **Closest unpublished or public-repository results:** none located.
- **Relation:** a discrepancy counterpart of the entropy polytope, by a different method. It is not independent of the Bergelson–Downarowicz precedent, which the paper cites in the introduction. The quantitative arithmetic realization appears new in the sources examined.
- **Search record:** inherited from `notes/phase19/literature.md` §1 (search of 25 November 2026); "discrepancy of sum of two numbers base b limiting discrepancy triple".
- **Dependencies and outstanding review:** the scheduler bound $[-4,1]$, and the convex-hull argument in Theorem 8.3.

### Theorems 9.1–9.3: sparse and Lambert remainders

- **Statement:** adding $\sum2^{-k(k+1)}$ changes binary discrepancy by at most $4\cdot2^{-w}+w\lfloor\sqrt{N+w}\rfloor/N$ (kernel-verified), hence by $O(N^{-1/2}\log N)$. A factorial version is Liouville. For Lambert numbers the maximal change is $1-D_N(L_\chi)$.
- **Evidence:** Lean-supported paper proofs (9.1, 9.2), and a paper proof with a companion input (9.3).
- **Literature:** Rauzy (1976) for the qualitative preservation; Spears–Maxfield (1969) for density-one periodic digit sequences. The Lambert deficit estimate is from the companion manuscript `papers/06-multiplicative-lambert` (owned there).
- **Closest unpublished or public-repository results:** Captain Sude's pinned theorem on $\sum(b^{m^r}-1)^{-1}$, [generalized-Lambert-disjunctivity-and-nonnormality @fe33be2](https://github.com/CaptainSude/generalized-Lambert-disjunctivity-and-nonnormality/blob/fe33be210446c6c0b127ca7757fc8f1182c5b541/lean/PowerLambert/Results.lean). This concerns nonnormality and disjunctivity, not translation rates.
- **Relation:** quantitative refinement of qualitative facts. The explicit rates appear new in the sources examined. They are simple.
- **Search record:** "normal number plus sparse series discrepancy rate"; trails through Bergelson–Downarowicz Remark 3.13.

### Theorems 10.2–10.4 (= Theorem F): infinite sums

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
  - Mira Cult (link above): finite joint normality of Stoneham series. This overlaps Theorem 10.3 in spirit, but for different series.
- **Relation:** apparently new in the sources examined, for the all-odd-prime normal Liouville series with an explicit rate. The finite joint normality (10.3) has the same flavour as Mira Cult's and Captain Sude's results for Stoneham series, and is credited. The rational-total counterexample is elementary.
- **Search record:** "sum of infinitely many Stoneham numbers normal"; "normal number infinitely many denominator primes series"; trails in `notes/phase19/grids.md` §7 and `literature.md`.
- **Dependencies and outstanding review:** the bound $c\le1+J_3$ through $v_3(\ell-1)<\log_3L$, which is valid (no prime-5 argument is used); the elementary bound $\prod_{\ell\le x}\ell<4^x$; and the CRT Liouville argument.

### Section 11 (not a claim of this paper): the flagship square

- **Status:** the binary shifts of $(\xi,\xi^2)$ are jointly uniformly distributed. This is a written proof in `notes/phase19/nonlinear.md` at `c2c9da6` (paper proof, no rate), with an independent AI audit in `notes/phase19/reviews/nonlinear.md`.
- **Relation and placement:** Paper I (v1.1) treats polynomial images of standard Stoneham numbers; Kano–Shiokawa and Wagner treat normal-number rings. The square theorem is deferred to the companion; see `COMPANION-ASSESSMENT.md`.
- **The earlier finite bound** $\limsup D_N(\xi^2)<2.94\cdot10^{-10}$ (Phase 18) is superseded and is not stated in the paper.
