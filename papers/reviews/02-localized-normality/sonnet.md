# Independent review of Paper II (localized normality)

- **Reviewer model:** Claude Sonnet 5.5 (`claude-sonnet-5-5`)
- **Input SHA:** `9796812804e0e22f6adb49436a8ff98cb8814c07` ("Author finite-prime localized normality manuscript and public Lean checks")
- **Material:** `papers/02-localized-normality/` (`paper.tex`, `paper.pdf`, `references.bib`, `Statements.lean`, `Check.lean`, `check.sh`, `REVIEW.md`, `figures/`), the notes it links (`notes/unsigned-finite-support.md`, `polynomial-masks.md`, `higher-order-joint.md`, `fixed-depth-question.md`), and the Lean declarations cited in Table 1 at the manuscript's pinned library revision `a09e011`.
- **Independence:** I read no other reviewer's report. I did not edit the paper.
- **HEAD note:** the working branch is at `4c59331`. Between `9796812` and `4c59331` nothing under `papers/02-localized-normality/` or in any module the paper cites changed (the diff touches only `StonehamJoint.lean` and `StonehamStatements.lean`).

## Verdict

**Mathematics: I found no error in any principal claim.** I re-derived the key arguments by hand and reproduced the finite computations. The Lean statement and proof entry point check cleanly at the stated axioms.

**Suitability for expert circulation: not yet.** The result is credible and the proof strategy is sound and interesting. The manuscript reads as a project artifact, not a paper, and there are four problems that an expert reader would hold against it:

1. The prose is full of repository-process language and a few promotional or cryptic sentences. The owner has asked for professional research-mathematics register, and several passages fall short of it (§F1).
2. The abstract and Appendix A claim more than Theorem A.1 delivers. In the unsigned case the appendix is asymptotically empty, and the paper never says so (§F2).
3. There is no author, and the principal comparison source is an anonymous GitHub PDF. Provenance of the AI assistance is stated in a way that does not tell a reader what was machine-written (§F3).
4. Several statements in the running text are asserted without a proof or a pointer a referee can follow (§F4).

All four can be fixed by editing. None needs new mathematics. I would circulate after one revision pass addressing F1–F5.

## Findings, ranked by severity

Severity: **Major** = fix before sending to experts. **Moderate** = fix in the same pass. **Minor** = polish. Line numbers refer to `paper.tex` at the input SHA.

### F1 (Major): the register is not that of a research paper

The owner's requirement is that manuscripts read like professional research mathematics. These are the concrete problems.

**Repository and process vocabulary inside the paper body.**

| Location | Text | Problem | Recommended action |
| --- | --- | --- | --- |
| l. 173 | "A second kernel-checked example with the same limit" | "Kernel-checked" is Lean-internal jargon; the example has no argument or pointer in the paper (see F4). | Say "A second example, $b=2$, $S=\{2\}$, $P=1/3$, has the same limit; the proof is the same and is formalized (declaration ...)." |
| l. 212 | "The project's separate paper argument treats one cofactor prime ... it invokes the Subspace Theorem and lies outside the kernel claims here." | "The project's", "kernel claims". The parse "one cofactor prime at all orders and sufficiently large orders for fixed $p$" is also ambiguous. | Rewrite as a plain remark with an honest status; see F4. |
| l. 284 | "has a separate order-one proof at the checkpoint" | "checkpoint" is a project term. | "has a separate proof at order one in the library revision cited above." |
| l. 284, 291–315 | "kernel-verified", "the checked library", "public classification proofs" | The same register problem. | Use "formalized in Lean" or "machine-checked". |
| l. 315–316 | "The reviewer guide supplies the commands for the exact finite residues, Figure 1 and the typeset manuscript." | A paper should not refer to a "reviewer guide". | Delete. |
| l. 315 | "From the repository root, run `lake build` followed by `papers/02-localized-normality/check.sh`." | Build instructions belong in a README or artifact appendix, not in a mathematical text. | Move to the archive's README. |
| l. 318 | "Authorship and submission decisions are reserved for the human project owner." | A statement about process, not a part of a paper. | See F3. |

**Promotional, cryptic or cute sentences.**

| Location | Text | Problem | Recommendation |
| --- | --- | --- | --- |
| l. 30 (abstract) | "An exact joint discrepancy formula accounts for cancellation at all orders through $s$." | Overstated and vague; see F2. | "We also show that the discrepancy at cutoff $N$ is asymptotic to the density of positions at which cancellation occurs simultaneously at every off-radix prime and every order $\le s$." |
| l. 216 | "For a given digit position, cancellation at order $s$ can expose a surviving denominator at one of the lower orders." | A cryptic lead-in, with nothing before it to refer to. | State the purpose directly: "Vanishing of the order-$s$ moment does not by itself clear the denominator; all orders $d\le s$ must be tested." |
| l. 281 | "For these unsigned series Theorem 4.1 evaluates the maximum completely. The formula uses the actual flow closure and assumes no independence of the reciprocals of three or more prime logarithms." | Unclear. It is actually a disclosure that Corollary A.3 has no content beyond Theorem 1.1 here (see F2). | "By Theorem 4.1 the maximum is $0$ when $J\ne\varnothing$ and $1$ when $J=\varnothing$. The corollary is therefore informative only as a statement about the structure of the failure set; no independence hypothesis on the logarithms of the primes is used." |
| l. 199 | "This is an exact density of certified windows." | An odd phrase with no content beyond the preceding formula. | Delete. |
| l. 201 | "Lemma 2.1 then applies verbatim." | "Verbatim" is a promise, not an argument; see F4. | Either state what changes or omit. |
| l. 204 | "Searching for $C_{p,s,L}=0$ is a different decision problem." | Terse to the point of cute. | "Termination of the search for $C_{p,s,L}=0$ is a separate question, treated below." |
| l. 65 | "At $b=10,\ S=\{2,3,5\}$ the single prime 3 suffices in every positive order despite both radix primes occurring in $S$." | "Suffices ... despite" is conversational. | "For $b=10$ and $S=\{2,3,5\}$ the prime $3\in J$ gives normality at every order although $2,5\in S$ divide $b$." |
| l. 107 | "Consequently, if a class of controlled positions forces uniformly growing denominators there, every retained block meeting the class has growing starting denominator" | "Controlled positions" and "class" are undefined; the sentence is a paraphrase of what the lemma should state. | Make it Corollary 2.2 with explicit hypotheses (see F4). |
| l. 133 | "Formula (3.5) bounds the missed share at every cutoff in the limit." | Vague. | Give the inequality $D_\infty(X_s)\le C_{p,s,L}$ and state the equation it follows from. |
| l. 127 | "It suffices to test mesh endpoints: on each cell the quotient is a constant plus a constant divided by $u$." | Terse; the real content is monotonicity on a cell. | "On each cell the quotient is monotone in $u$, so its maximum is attained at a cell endpoint." |
| l. 77 | "No uniformity in $S$ is asserted." | This is good and honest. Keep. | None. |

**Repeated filler.** The adjective "actual" is used as an intensifier five times: "actual $B$ shifts" (l. 91), "actual rationally weighted prefixes" (l. 168), "actual limit" (l. 173), "actual prefix" (l. 183) and "actual flow closure" (l. 281). It adds nothing. "Exact" is likewise used as an emphasis where it is not a mathematical claim ("An exact joint discrepancy formula", l. 30; "exact density", l. 199; the title of Appendix A).

**Order of exposition in Appendix A.** The order-two example (l. 234) appears before the lemma and theorem that explain it, and in the middle of a long paragraph that also contains the order-one derivation. It has the inelegant tail "This is an order-two example at scale exponent two and precision three. The following identity gives the general clearing condition." Phrases such as "For direct verification, the largest smooth index is 168 and summing the 38 shifted terms gives ..." and "The canonical unit is 1 mod 343" ("canonical" is not defined in the paper; it means $(b^{-1})^{p^{L-1}}\bmod p^L$) read as lab notes. Move the example to a numbered *Example* after Theorem A.1, say what it illustrates (the deepest order-$s$ residue vanishes mod $p^{k+1}$ yet $\operatorname{den}R=7$, so order-$s$ vanishing alone does not imply integrality), and then give the data.

**Normality $\Leftrightarrow D_N\to0$ (l. 46).** Four sentences reprove a classical fact. Replace by one sentence and a citation (Kuipers–Niederreiter, or Bailey–Crandall Thm 2.2, which the 2026 manuscript and Vandehey both cite). The phrase "using terminating expansions at radix rationals" is irrelevant, since rationals are not normal.

**Appendix B.** It is lettered as an appendix but is really a "Formalization" section; most of it is the table. Fold it into a short §7 before the bibliography and cut the commands.

### F2 (Major): the abstract and Appendix A overstate, and the appendix is asymptotically empty in the unsigned case

- **Abstract and Theorem A.1.** The abstract says "An exact joint discrepancy formula". Theorem A.1 proves
  $D_N(X_s)-\lambda(B_*\cap[1,N))/N\to0$, an asymptotic equivalence, not a formula for $D_N$. The title of Appendix A ("Exact joint failure and prefix discrepancy") has the same overstatement.
- **Vacuity.** For $J\ne\varnothing$, $B_*\subseteq\{y:t_p(y)\in Z_{p,s}\}$ for any $p\in J$, and $Z_{p,s}$ is null by Theorem 4.1. Hence $\lambda(B_*)=0$ (the set $\{y:t_p(y)\in Z_{p,s}\}$ is a union of scaled copies of a null set), and in particular $\lambda(B_*\cap[1,N))/N\to0$. So Theorem A.1 and Corollary A.3 reduce to $D_N\to0$, which Theorem 1.1 already gives by the shorter route of Lemma 3.1. The appendix is used nowhere in the classification. REVIEW.md says as much ("allows a referee to verify the classification using only the single-prime upper bound"), but the paper does not, and the abstract advertises it as a result. When $J=\varnothing$ the statement is trivial, and the case $2\in J$ gives $B_*=\varnothing$.
- **What the appendix does contain.** The integral principal-unit expansion (Lemma A.2) and its uniform coefficient bound (odd $p$), the all-orders clearing criterion, and the identification of the failure set with the cutoff-phase flow closure. These are independently interesting as structure, and they are what would be needed if Theorem 4.1 were unavailable (for example for restricted supports or weights). The paper should say this.
- **Recommendation.** Retitle ("Joint failure sets at all orders"), state in one sentence after Theorem A.1 that the right sides vanish when $J\ne\varnothing$ by Theorem 4.1, and remove or reword "exact formula" in the abstract. Alternatively shrink the appendix to Lemma A.2, the order-two example, and a remark.

### F3 (Major): provenance, authorship and citation of an anonymous source

- `\author{}` is empty and the PDF `Author` field is blank. An expert reader needs a named author, affiliation and contact. The closing note ("Authorship and submission decisions are reserved for the human project owner", l. 318) discloses the problem but does not solve it.
- The AI-assistance sentence reads "OpenAI Codex assisted with drafting, source comparison, figure preparation, and the Lean correspondence checks." It does not say whether the mathematical arguments and the Lean proofs themselves were machine-written (the Lean development is mentioned only as "correspondence checks"). Experts will ask. State plainly who wrote or verified what, and which parts a human has independently checked. This is a disclosure issue, not a mathematical one.
- Citation `localized` ("Binary normality of a localized logarithm", 2026) has no author, no date beyond the year, and points to a GitHub file in `CaptainSude/xi-normality` with `key = {Binary normality}`. This is the main comparison source, yet a reader cannot tell who wrote it or whether it is related to the present project. If it is by the same project, say so; if not, give authors. Either way archive a copy (e.g. a DOI archive) because a GitHub path is not a stable reference.

### F4 (Major): statements in the text that the reader cannot check

1. **Finite termination (l. 212).** The text asserts, by pointer to an unreviewed repository note, results using Schlickewei's Subspace Theorem: for odd $p$ and one cofactor prime $q$, every one-sided value of the $p$-adic moment is transcendental; and a large-order theorem for fixed $p$. I read the note (`notes/fixed-depth-question.md`) and the argument is plausible and written with care, but I did not verify it and it has had no external review. It reads in the paper as an established result ("treats ... at all orders") while being outside both the Lean development and the paper's own proofs. Either (a) delete it and keep the unresolved-question sentence, or (b) state it as an announced result with a precise statement and a pointer to a stable preprint, not "the project's separate paper argument".
2. **Quotient weights (l. 201).** The paragraph beginning "The same window estimate holds for weights $P(m)/(m^tQ(m))$" gives a condensed argument ("division by $Q(m)$ preserves the strict valuation comparison", "Lemma 2.1 then applies verbatim"). It is plausible: I checked that $Q(m)$ being a $p$-adic unit preserves the valuation comparison and that the exponents in $m^t|Q(m)|$ are $O(\log N)$. But two points are not in the text: the denominator primes now include primes outside $J$ (so Lemma 2.1(2) needs "prime to $b$, in a fixed finite set", which it does state, but the finite set is no longer $J\cup\operatorname{primes}(D_0)$), and $Q(m)\ne0$ at retained indices is only implicit. The Lean statement `quotient_window_bound` has the hypotheses `denSupport` and `unit` that make this precise. State them in the paper.
3. **Second 2/3 example (l. 173).** "A second kernel-checked example with the same limit occurs for $b=2,\ S=\{2\},\ P=1/3,\ s=1$." No argument, and neither declaration `thirds_discrepancy`/`dyadic_reciprocal_thirds` (`MaskThirds.lean`) is in Table 1. The notes contain the argument (a sum $(-1)^n\sum_j(-1)^{2^j+j}$ modulo 3 alternating between $1/3$ and $2/3$). Either supply two sentences or drop the example. (I checked it numerically; see below.)
4. **Lemma 2.1(3) (l. 91, 103–104).** The statement is informal: "In any collection of these blocks on which $q_u\to\infty$ uniformly, the discrepancy ... tends uniformly to zero." Quantifiers are not stated. It is the one place where the paper delegates to Vandehey, and the proof is a four-line sketch (Fourier coefficients → weak convergence → uniform interval convergence → contradiction). State it as: for every $\varepsilon>0$ there are $Q$ and $N_0$ such that every retained block at cutoff $N\ge N_0$ with $q_u\ge Q$ has interval discrepancy $\le\varepsilon$. The proof as sketched supports this.
5. **Theorem 5.1 (l. 183).** The proof compresses two cases into one paragraph and ends "Lemma 2.1 proves the bound." The main valuation computation is correct (I redid it), but the case split (window versus axis) and the final transfer deserve separate sentences. Also Corollary 5.2 does not restate "$P\ne0$, $r<s$, $p\in J$", so its "in particular ... normality in every odd radix" does not carry its hypotheses.
6. **Lemma 3.1 is stated for order $s$** and then used in the proof of Theorem 1.2 at order $t=s-r$ (l. 168). Say "applied with $t$ in place of $s$", or state the lemma for a generic order $d$.
7. **Corollary A.3 (l. 277–278).** The proof is a single dense paragraph ("The score is continuous ... The tail closure of the cutoff phases is $H$ ..."). The statement and the Lean theorem (`discrepancy_eq_log_flow_max`) agree. A referee will want this expanded or reduced to a remark, given F2.

### F5 (Moderate): correspondence and pinning

- **What the public statement covers.** `Statements.lean`/`Check.lean` prove only: the full-support unsigned classification (Theorem 1.1) and the full-support "normal $\iff r<s\wedge J\ne\varnothing$" half of Theorem 1.2. Everything else in the paper is linked only to internal declarations: the restriction clauses of Theorem 1.2 (nonnormality of every $X_A$ when $r\ge s$ or $J=\varnothing$, and $\liminf D_N\ge1/D_0$), Theorem 5.1, Corollary 5.2, the quotient extension, Theorem A.1, Corollary A.3. I read the Lean statements of `rational_boundary`, `rational_window_bound`, `axis_normal_iff`, `rational_pole_bound`, `quotient_window_bound`, `discrepancy_tracks_jointPhase`, `jointOrder_density_tendsTo_discrepancy`, `discrepancy_eq_log_flow_max`, `phase_prefix_identity` and found them consistent with the paper's statements, with these differences:
  - `rational_window_bound` and `axis_normal_iff` assume `P.eval 0 ≠ 0` and order $t>0$. The paper's Theorem 5.1 states $P\ne0$, $r<s$. The reduction is `masked_cancel` (`MaskGrid.lean:158`), which is not cited in Table 1 (the caption mentions it in prose only: "stated after cancellation of the common power of $X$").
  - `rational_boundary` yields $\exists L$ with $b\perp L$ and $1/L\le\liminf$; the paper asserts the specific $L=D_0$. This is consistent since any denominator works with a weaker bound, but the specialization is in the paper only.
  - `discrepancy_eq_persistent_max` requires every other support prime to divide $b$; the paper's "If $J=\{p\}$ and $s=1$" is the same condition, stated differently. Say so.
- **Table 1's caption** "Statement correspondence at the pinned revision" suggests a checked correspondence for every row. Only the two classification theorems are checked against a public statement. Reword ("Declarations supporting each assertion").
- **Pinned revision lacks the public files.** The paper pins the library to commit `a09e011`, and the section says the accompanying `Statements.lean`/`Check.lean`/`check.sh` prove the classification. Those files first appear in `9796812`; `git ls-tree a09e011 papers/02-localized-normality/` is empty. A reader following the pinned link cannot find them. Pin to the manuscript commit (or an archive) for the statement files. By my local `origin/main` ref (which may be stale), `9796812` is not on the remote; `a09e011` is, and the GitHub URLs I probed returned 200.
- **`tsum` junk value.** `value` is defined with `∑'`. If the series were not summable the definition would silently give $0$. It is summable, and the theorem proves substantive statements about it, so the statement is not vacuous, but a reader of the public statement cannot see this. Adding a `Summable` lemma to `Check.lean` (or a one-line remark) would close the gap.
- **Reading the statement.** `UnsignedClassification` and `PolynomialClassification` correspond to Theorem 1.1 and Theorem 1.2 as I read them: half-open intervals, shifts from $n=0$, words including leading zeros, $\mathrm{Smooth}$ including 1 for $S=\varnothing$ and excluding 0, index $m=i+1$, $s=0$ allowed in the polynomial statement, `rootMultiplicity 0 < s` for the pole condition. The two `Normal`/`discrepancy` definitions match the paper's. No mismatch found.

### F6 (Moderate): literature and priority

**What I checked against primary sources** (downloaded the Vandehey arXiv manuscript, the Bailey–Crandall author copy and the pinned 2026 PDF; Dibag only via the secondary description):

- *Bailey–Crandall, Cor. 4.9(i):* "generalized Stoneham numbers $\alpha_{b,c}=\sum 1/(c^ib^{c^i})$ are each $b$-normal" for coprime $b,c>1$. Matches the paper (the paper restricts to prime $c=p$, which is what the localized sum needs; the $1/b$ offset is correct).
- *Vandehey, Cor. 1.2:* for $P$ finite, $m\in\mathbb N_P$, $\gcd(a,m)=1$, $\gcd(m,b)=1$, $\epsilon>0$, there are $\delta(\epsilon),C(\epsilon,b,P)$ with $|\sum_{n\le N}e(ab^n/m)|\le Cm^{-\delta}N(1+\log m)$ for $N\ge m^\epsilon$. Matches the paper's use (with $q\le B^C$, $N=B\ge q^{1/C}$).
- *Vandehey, Thm 7.4:* $P$ finite coprime to $b$, $c_k$ strictly increasing with $c_k\mid c_{k+1}$ and prime divisors in $P$, $\mu_k=m_k-m_{k-1}$, and $\exp((1+\epsilon)\log c_k/\log\log c_k)/\mu_k\to0$ imply $\sum 1/(c_kb^{m_k})$ is normal. The paper's deduction for $m_i=p^{k_i}$, $c_i=p^{sk_i}$ is correct: $\log c_i=s\log m_i$, so the exponential is $m_i^{(1+\epsilon)s/\log\log c_i}=o(m_i)$, and $\mu_i\ge(1-1/p)m_i$.
- *The 2026 manuscript:* Thm 1.1 ($\xi=F_{\{2,3\}}(1/2)$ binary normal), Thm 4.1 (discrepancy $\ll M^{-1/2}(\log 2M)^3$), Thm 5.1 (normal for $P$ nonempty with all primes coprime to $b$, or $b=2$ and $3\in P$, using Vandehey's estimate), Section 6 (Lean proof covers only the qualitative $\xi$ theorem; the optimized estimate, the discrepancy theorem and the finite-prime extension are not formalized). The paper's description of it (l. 75) is accurate, including the formalization scope. The paper's use of the sign convention $F_P(z)=-L_P(-z)$ matches the 2026 text.
- *Dibag:* I could not obtain the original (the institutional link returns an HTML landing page). The attribution "Dibag introduced the localized logarithm" rests on the 2026 manuscript's description of Definitions 1.1–1.2. I flag it as unverified by me. The bibliographic data match the 2026 manuscript's reference.

**Priority versus formalization.** The paper keeps these separate and does not claim more than it should: it credits Bailey–Crandall for the singleton order-one case, Vandehey for the unsigned axis restriction at every order, and the 2026 manuscript for order-one supports wholly coprime to $b$ and binary supports containing 3. It states that the present theorems allow arbitrary overlap with radix primes, all positive orders, and polynomial weights. By my reading that comparison is accurate. The honest summary is:

| Result | Earliest source I can identify | Status |
| --- | --- | --- |
| Singleton order one, $p\perp b$ | Bailey–Crandall 2002 | Human proof |
| Unsigned, every order, infinite subset of one off-radix prime-power axis | Vandehey 2019 (Thm 7.4) | Human proof; the paper reproves it for polynomial weights |
| Order one, $\{2,3\}$ at $b=2$; nonempty supports coprime to $b$; binary supports $\ni3$ | 2026 manuscript | Human proof; Lean only for $\{2,3\}$ qualitative |
| Unsigned, arbitrary finite $S$, every $s\ge1$, any overlap with radix | This paper | Human proof (Sections 2–4) and Lean proof of the public statement |
| Rational polynomial weights of unbounded degree, full support | This paper | Human proof (Section 5) and Lean proof of the public statement |
| Masks, windows, quotient extension | This paper | Human proof sketched; Lean for the stated declarations |

The REVIEW.md remark that priority for mixed supports, unrestricted-degree weights and the recurrence argument "requires independent specialist review" is correct and should stay in the review record. I would add a short statement in the paper's introduction in the same register ("To our knowledge...") only if the owner is comfortable with that; the present neutral comparison is acceptable.

**Missing references an expert will expect.** Stoneham (1973) and Korobov (1972) are the origin of the constants and of the exponential-sum method the paper calls "Korobov-type", and both are cited by the 2026 manuscript. The notes also list Bailey–Borwein (doi 10.1007/s11139-012-9417-3), which I did not open; if it concerns Stoneham constants in other bases, as I believe, it is the natural comparison for the $J=\varnothing$ case and for the bases other than the defining one. Bourgain's work on short orbits, which the abstract of Vandehey's paper names, is the standard context for the exponential-sum estimate. The 2026 manuscript's Lagarias reference is the usual place to anchor "normality of natural constants."

### F7 (Moderate): notation collisions

A referee will lose time here.

| Symbol | Uses |
| --- | --- |
| $D$ | positive common denominator (Thm 1.2); also $D_N$, $D_\infty$ in the same displayed inequality; coefficient-denominator split $D=D_bD_0$ (l. 101) |
| $H$ | $\lceil\log_2(N+2B)\rceil$ (Lemma 2.1); row-gap bound (Thm 4.1); the polynomial $H(m)$ in $G(m)=G(0)+mH(m)$ (l. 168); closure of the flow (Cor A.3) |
| $t$ | $s-r$ (Thm 1.2 proof, Thm 5.1); the threshold variable in $U_{p,d}(t)$ (Sections 3–4, App. A) |
| $d$ | the order in $U_{p,d}$; also the number of cofactor primes $q_1,\dots,q_d$ in Thm 4.1 |
| $T$ | $M(S\setminus\{p\})$ (§3); $(p-1)p^a$ (Lemma A.2); phases $T_p$ (Cor A.3) |
| $L$ | precision; also the preperiod $L_j$ (Thm 4.1) |
| $B$ | block length; $B_p$, $B_*$ (App. A) |
| $C$ | exponent in Lemma 2.1; certificate $C_{p,d,L}$; constant in Lemma A.2 |

Rename at least the $D$, $H$, $t$ and $d$ collisions. The ones inside one proof (the $d$ in Theorem 4.1, where $U_{p,d}$ has just been defined) are the most confusing.

### F8 (Minor)

- l. 80: "set $R_n=\sum_{m\le n}a_mb^{n-m}$ for $m\ge1$." Should read "for $n\ge1$."
- **Figure 1** (l. 67–70). The entry is 1 exactly when every prime of the row's support divides the radix: it is determined by one line of text and carries no information. I would delete it and keep the $b=10$ remark (once, in plain language). It is also the only figure; REVIEW.md describes a generator, CSV and SVG for it, an apparatus out of proportion to its content.
- **Appendix A and Theorem A.1.** The second limit uses "at fixed $L$ the library may omit finitely many early cells" (l. 223): "the library" is again process language; say "we ignore finitely many initial scales."
- **Section 6.** "treats ... sufficiently large orders for fixed $p$" is ambiguous in l. 212; as written it can be read as "fixed small order" or "all large orders".
- **Abstract.** "We prove that persistent cancellation at a single off-radix prime has measure zero" is correct but would read better as "we prove that the set of thresholds at which cancellation at a given off-radix prime persists at every precision has measure zero".
- **Intro (l. 39).** "positive $s$ similarly localizes $\mathrm{Li}_s(b^{-1})$": "localizes" is undefined for a reader who does not know Dibag; one clause defining the localized sum would help.

## Claims I checked myself

**By hand (from the paper's text, not relying on the Lean files):**

- Section 1: empty support ($M(\varnothing)=\{1\}$, $X=1/b$, $D_N\to1$); the discrepancy bound $D_N\le1$; the equivalence of normality with $D_N\to0$.
- Lemma 2.1: smooth-index count, block discarding, clearing of radix primes ($m^s\mid(bc)^{sH}$ and $u-m\ge B>sH+\ell$), denominator bound $q_u\le B^C$, applicability of Vandehey Cor. 1.2.
- Section 3: Teichmüller lift and $b^{-p^jm}\equiv w^m\bmod p^L$ for $j\ge L-1$ (including $p=2$); the equality of $Z_{p,d}$ with the zero set of $U$; the mesh-endpoint form of $C_{p,d,L}$ and its monotonicity argument; the geometric-series count $\lambda(E)/(p-1)+\lambda(E\cap[1,u))$.
- **Lemma 3.1** (survival at fixed precision): the row decomposition, $k\ge2(L-1)$ condition and valuation bound.
- **Theorem 4.1 (nullity).** I checked every step: the scaling law $U(pt)=p^{-s}U(t)$; the passage to the log circle; eventual periodicity of $q_j^n\bmod(p-1)$ including $q_j\mid p-1$; Poincaré recurrence giving a positive multiple $a_j$ of $h_j$; invariance of the scaling law under the difference; reindexing to get $A(m)=\sum_{Q_I\mid m}(-1)^{|I|}w^{m/Q_I}$; the pairing argument making $A(m)=0$ when some $v_{q_j}(m)\ge L_j+a_j$ (the pairing is an involution, the divisibility conditions agree because the $q_i$ are distinct primes, and the exponents of $w$ agree modulo $p-1$ since division by $Q_I$ leaves $v_{q_j}$ unchanged); finitely many rays $cr^l$; the bare ray $A(r^l)=w^{r^l}$ is a unit because $a_j\ge1$; finiteness of the value set; the threshold uniqueness by $p$-adic valuation; the log-separation $\eta$ from finiteness of $c,c',a$ and $e$; density of $\{l\log_pr\}$; the "first nonzero jump row" argument with valuations $is+V<(i+H+1)s$; injectivity on each piece, hence finitely many zeros, contradicting positive measure. **I found no gap.** This is the part of the paper I would trust a specialist to find elegant.
- Theorem 1.1, $J=\varnothing$ case (frequency of $[\delta,1-\delta)$ is $o(1)$, so $D_N\to1$).
- Theorem 1.2: the dominance inequality $v-kt+L-1<-k(t-1)$; $G(m)=G(0)+mH(m)$ splitting; effect of dividing by $D$ ($v_p(x/D)\le v_p(x)$); the case $r\ge s$ (integer weights, grid $D_0^{-1}\mathbb Z$, interval $[\delta,1/D_0-\delta)$); the case $J=\varnothing$; the statement for $s=0$ (always nonnormal, consistent with the Lean statement).
- Example $P=X^2/3$, $b=2$, $S=\{3\}$, $s=1$: the arcs argument for $D=2/3$ is correct (an interval containing both of $1/3,2/3$ has length $>1/3$, error $\to2/3$; an interval avoiding both has error $\le1/3$; the wrapping-arc-complement step is valid).
- Theorem 5.1: the valuation comparison at $m=p^k$ for $k>v$ (cases $j\ge v$ and $j<v$), uniqueness of the minimum, and the axis case with "largest retained exponent". Corollary 5.2: the window density formula, the monotone-within-window argument locating the liminf at the window left endpoints, the bounded-gap bound, the periodic formula, and the $p=3$, $E=\{0,1\}$, $h=3$ value $g=\min(4,10)/26=2/13$ (so $D_\infty\le11/13$); unbounded gaps give $g=0$.
- **Lemma A.2 (identity).** Derivation of $b^{-n}R_{s,n}\equiv\sum_d c_{n,s-d}p^{-kd}U_{p,d}(t_p(y))$ in $\mathbb Q_p/\mathbb Z_p$: Newton polynomial integrality via $v_p(j!)\le j$, $w^{p^{k-i}r}=w^r$, equivalence of $r\le p^in/p^k$ and $r\le p^iy/p^k$ for $y\in[n,n+1)$ (an integer $r$ exceeds $p^in/p^k$ by at least $p^{i-k}$), and integrality of the rows $i>k$. The coefficient bound for odd $p$: $\Delta_T^hP_n(0)=(u^T-1)^h$, the divisibility $T^{h+1}$ of higher-degree contributions, $v_p(u^T-1)=v+a$ by lifting the exponent, $h(v+a)<(h+1)a$ for $h<s$.
- **Theorem A.1.** Both inequalities: the lower bound through integrality of $R_{s,n}$ at every $p\in J$ when $y\in B_*$; the upper bound through the largest nonvanishing order $d$ with valuation $\le C+L-kd<-k(d-1)$ for $k>C+L$; the case $2\in J$ where $B_*=\varnothing$ since the first row at $p=2$ contains only $m=1$; the second limit by the integer-mesh argument.
- Corollary A.3: identification of the prefix mass with the score at the cutoff phases, and the single-prime special case.

**By computation:**

- **Lean (scratch copy of `9796812`, toolchain v4.36.0, existing dependency cache copied from another worktree).** `lake build` succeeded; `papers/02-localized-normality/check.sh` printed `PaperII.unsignedClassification: [propext, Classical.choice, Quot.sound]` and `PaperII.polynomialClassification: [propext, Classical.choice, Quot.sound]`; `lake env lean Audit.lean` completed without error. `grep` for `sorry`, `^axiom`, `native_decide`, `ofReduceBool` in `NormalityChecker/` and the paper's Lean files found nothing. All 23 `\decl` links in Table 1 resolve to the stated declaration at the stated line of `a09e011`.
- **Order-two example.** In exact rational arithmetic ($b=36$, $S=\{2,3,7\}$, $s=2$, $n=186$): the number of smooth indices $\le186$ is 38, the largest is 168, $\operatorname{den}(R_{2,186})=7$, and $7^4b^{-186}R_{2,186}\equiv4\cdot7^3\bmod7^4$ (computed value $1372=4\cdot343$). I also checked row 0 and row 1 of the moment by hand ($49$ and $294$ mod 343). (For reference, the order-one denominator at the same $n$ is $49$.)
- **Finite order-one tests** (`scripts/localized_certificate.py`): $b=32$, $p=31$, $S=\{2,31\}$ gives bounds $1/2$, $31/960$, $0$ at $L=1,2,3$ and failed cells $[16,31)$, $[16,512/31)$, none, as stated in §6. The larger case ($b=82967135716$, $p=3$, $S=\{2,3,17,41,103,311,929\}$) gives $1569/32768$, $1569/32768$, $1937/49152$, $0$ at $L=9$–$12$, as claimed in REVIEW.md. I also ran $b=10$, $S=\{2,3,5\}$ ($p=3$, passes at $L=2$, and at order 2 passes at $L=1$) and $b=6$, $S=\{2,3,5\}$, $p=5$ (passes at $L=2$), confirming the mixed-support claim in the paper's l. 65.
- **Second 2/3 example.** For $b=2$, $S=\{3\}$, $P=X^2/3$, $s=1$, the exact series is $\sum_{k\ge0}3^{k-1}/2^{3^k}$. Using exact rational arithmetic I computed the extreme discrepancy of the first $N$ points $\{2^nx\}$: $0.608$ at $N=500$, $0.638$ at $1500$, $0.645$ at $2000$, $0.657$ at $6000$. This is consistent with a slow approach to $2/3$.
- **Figure data.** `figures/classification.csv`: 56 entries, each equal to 1 iff the support's primes all divide the radix, as the caption says.
- **PDF.** I rendered pages 2 and 10 and read the text of all 11 pages. I found no visible layout fault (the figure, the Lean table and the displays render correctly). I could not rebuild from source here because no LaTeX toolchain is installed, so I did not verify that `paper.pdf` was built from `paper.tex` at this SHA; the text I compared agrees.

**Not checked:**

- The original Dibag article (see F6).
- The Subspace-Theorem arguments in `notes/fixed-depth-question.md` (see F4).
- The Lean proofs of the cited declarations beyond reading their statements and running the axiom audit. I relied on kernel acceptance.
- The claim in REVIEW.md that the declaration directory has 776 entries (it concerns README tooling, not this paper).
- The finite exhaustive search of 756 cases in `unsigned-finite-support.md`, which is not used in the paper.

## Specific rewrite suggestions

1. **Abstract, last sentences.** Replace "An exact joint discrepancy formula accounts for cancellation at all orders through $s$. For restrictions of the support we give bounds in terms of retained prime powers and a complete criterion on one prime-power axis." with: "For the unsigned series we also show that the discrepancy at cutoff $N$ is asymptotic to the density of positions at which cancellation occurs simultaneously at every off-radix prime and every order up to $s$. For restricted supports, retained prime powers give upper bounds on the discrepancy, and on a single prime-power axis normality holds exactly when infinitely many powers are retained."
2. **Earlier results, l. 75, last sentence.** "On a support containing distinct primes $p,q$, the ordered list of smooth indices contains both $p$ and $q$; their powers $p^s,q^s$ cannot belong to one divisibility chain." → "Theorem 7.4 of [Vandehey] requires the denominators to form a divisibility chain, which fails on the full support of two primes, since $p^s$ and $q^s$ are incomparable."
3. **l. 212 (finite termination).** Either delete after "remains unresolved in this analysis", or: "Termination at a fixed order for a support with several cofactor primes is open. For one cofactor prime the author has an argument using the Subspace Theorem (preprint [X]); we do not use it here."
4. **l. 281 (Corollary A.3 remark).** See F1's table.
5. **l. 315–318.** Replace the last two paragraphs by one sentence on the machine-checked statement and a statement of the reproduction archive with DOI, then a precise AI-use paragraph (see F3).
6. **Table 1 caption.** "Lean declarations supporting each assertion at the cited revision. The public statements proved in `Statements.lean`/`Check.lean` are Theorems 1.1 and the full-support half of Theorem 1.2."

## Recommendation

Circulate to experts after one revision that (i) removes repository-process language and the cryptic or promotional sentences above, (ii) rescopes the abstract and Appendix A, (iii) adds authorship and a precise provenance statement and replaces the anonymous GitHub citation by a stable one, (iv) supplies or removes the unsupported claims in F4, and (v) fixes the pinned-revision and notation issues. The core results (Theorems 1.1 and 1.2 for full supports, and the nullity proof of Theorem 4.1) are, in my judgment, correct and the proof of Theorem 4.1 is a genuinely clean argument. The mathematical content does not need to change.
