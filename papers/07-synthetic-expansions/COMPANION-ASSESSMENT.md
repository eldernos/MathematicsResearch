# Do the nonlinear and polynomial-closure results justify a companion paper?

**Assessment: yes.** They justify one focused companion paper on *polynomial images of synthetic expansions*, built around the now-proved normality of the flagship square. That paper should not be written until a specialist has reviewed the priority comparison with normal-number rings and with Paper I, and has checked the analytic square proof. No paper was written here; this file records the assessment only.

The results in question are the Phase 18 algebra results (`notes/phase18/algebra.md` at `e4809cf`) and the Phase 19 nonlinear results (`notes/phase19/nonlinear.md` and `independent-axes.md` at `c2c9da6`). None of them is a theorem of Manuscript C. Manuscript C mentions the square theorem, without claiming it, in its Section 11.

## Inventory and evidence

| Result | Source | Evidence | Status for a companion |
| --- | --- | --- | --- |
| Rational affine combinations and joint normality across distinct primes and orders, under a common sparsity bound | P18 algebra E1 | Paper proof using the fixed-support criterion (the kernel-verified short-orbit estimate is an input) | Include. Must be compared with Mira Cult's joint-normality note and Captain Sude's results for the classical $p^j$ schedules. |
| Every rational polynomial of degree $r<d$ in $C(b,p,s,d)$ is normal when $s\ge r$; joint normality of $(X,\ldots,X^{\min(s,d-1)})$ | P18 algebra E2b | Paper proof; independent AI review found it correct and asked for a stated lateness threshold | Include. This is the core combinatorial layer lemma. |
| Universal polynomial normality on the factorial schedule (normal Liouville algebra) | P18 algebra | Paper proof | Include, compared with Kano–Shiokawa, whose rings consist of Liouville irrationals. |
| Products whose opposite-axis prefix stays a unit (affine modification) | P18 algebra E3 | Paper proof | Optional. The result is narrow because it modifies one factor. |
| **Square theorem:** every rational quadratic polynomial in $C(b,p,s,d)$, $d\ge3$, $s\ge1$, is normal. In particular $(C(2,3,1,3),C(2,3,1,3)^2)$ is jointly normal. The result extends to total degree two in finitely many orders. | P19 nonlinear | Paper proof without a rate; independently audited (AI); not kernel-verified | **Centerpiece.** This resolves what Phase 18 left open: the earlier certified bound $\limsup D_N<2.94\cdot10^{-10}$ is now superseded by normality. |
| Every polynomial on rapidly varying power schedules ($\log n_k\sim(\log k)^2$, $n_{k+1}/n_k\to1$) | P19 nonlinear | Paper proof, AI-reviewed | Include. It gives non-Liouville-type schedules, which contrast with Kano–Shiokawa. |
| Polynomial-normal algebras on separated depths or distinct retained primes | P19 nonlinear and independent-axes | Paper proof, AI-reviewed | Include as the algebra chapter. |
| Products of remainders (sparse preservers with a visible product) | P19 products-of-remainders | Paper proof | Possible appendix: it is multiplicative and fits the "operations" theme. |
| Rational scalar classification of the kernel of $\limsup(1-D_N(x-y))$; integer-dilation spectra | P19 geometry | Partly Lean, partly paper | Better suited to a later short note on operations; see below. |

## Reasons for a separate paper

1. **The method differs.** Manuscript C rests on the exact linear denominator identity (Theorem 4.2), on complete periods and on programmed states. The polynomial results need convolution layers, top-residue counts $M_r(u)\bmod p$, pole-loss lemmas and, for the square, an analytic argument: the localized jump count, the second moment and density points of the limiting $p$-adic mass. Adding them would roughly double the length of C and blur its theme, which is what can be prescribed by choosing rational states.
2. **The headline result is substantial and self-contained.** The joint normality of $(\xi,\xi^2)$ for $\xi=\sum3^{-v_3(k)}2^{-2k^3}$ is a natural main theorem. Its proof is long, has no rate, and deserves its own exposition and its own specialist review.
3. **The priority questions differ and are delicate.** Normal-number rings (Kano–Shiokawa 1993; Wagner 1995; Bailey–Crandall 2002) and the project's own Paper I (polynomial images of standard Stoneham numbers, v1.1) are the direct comparison points. A specialist must judge how much the finite-irrationality-exponent schedules and the valuation weights add. It is cleaner to make that comparison in one paper than to spread it across two.
4. **Duplicate publication is easy to avoid.** C cites the square theorem only as a result recorded with the source files, not as a theorem of C, and C contains none of the polynomial-image proofs. The companion would own all of them. It would cite C for the denominator identity (Theorem 4.2), the switch (Theorem 4.4) and the transfer lemmas.

## Conditions before drafting

- Specialist review of the square proof (`notes/phase19/nonlinear.md`), in particular the localized grid-intersection count and the frozen-prefix transfer. The AI audit found no error, but cross-model review is not peer review.
- A priority comparison with Kano–Shiokawa (Remark 2: irrational elements are Liouville), with Wagner (rings for bases $g$ and $gp$), and with Paper I. A rate for $\xi^2$ would strengthen the paper but is not required.
- A decision on Phase 18 E2b's lateness threshold (review objection O1). It should be stated explicitly.

## Other Phase 19 operations not placed in C

The following remain research-note material for now:

- finite linear-form spectra and their polyhedral approximation;
- joint box rates;
- the rational-scalar kernel classification;
- dilation spectra;
- algebraic independence of the addition witnesses.

Together with products of remainders, they could form a later short paper on discrepancy under arithmetic operations. They do not yet justify one, because several results are qualitative and their relation to the specification and entropy literature (Sigmund; Bergelson–Downarowicz §§4–8) needs a fuller comparison.

## Open status, stated plainly

- **The flagship square is no longer open.** $\xi^2$ is normal and $(\xi,\xi^2)$ is jointly normal, by a written proof that has been audited by AI only. Its discrepancy rate is open.
- Transcendence of $\xi$ is open; normality excludes only rationality.
- Normality of $\xi^3$ and of higher powers is open in the sources examined: the Phase 19 argument covers degree two, and the Phase 18 layer lemma needs $s\ge r$, whereas $s=1$ for $\xi$.
