# Resolution of referee reports 1 and 2 on Manuscript C (*Synthetic Arithmetic Expansions and Prescribed Discrepancy*, v1.0)

- **Reviser model:** Claude Opus 5.5 (Anthropic), Claude Code in T3 Code
- **Date:** 25 November 2026
- **Commits reviewed:** report 1 (GPT-6.2 Astra) at `758380b4e8eaf7c98994b55f0413d613ea319ba2`; report 2 (Gemini 4 Argon) at `9a64d5b3eb2a1f2a9545c8a8fc20c4bd4622b718`. The revision starts from `f65b1c745a5fee8dfef858f95a47024b1ca5d158` on `publication/wave-2` (worktree branch `t3/revise-synthetic-expansions`).
- **Status:** **AI model review and revision; not independent human peer review.**

Report 1 (verdict: major revision; 2 major, 4 minor, 1 editorial finding; no gap in Section 7) is `review-1.md`. Report 2 (verdict: accept with minor revisions; 4 minor, 2 editorial findings; no gap in Section 7) is `review-2.md`. Line numbers below refer to the revised `papers/07-synthetic-expansions/paper.tex`. The rebuilt PDF has 24 pages (22 before), no undefined references or citations, and PDF Author `Christopher Anderson`. The only new numbered statement is Remark 6.5, at the end of Section 6, so all other numbers are unchanged and the companion files stay consistent. All 22 pinned Lean anchors in the PDF were re-extracted with `pdfinfo -url` and checked with `git show`: each lands on the declaration line of the named theorem or definition at `e4809cf` or `c2c9da6`. No Lean file, `papers/common/`, `papers/0[1-5]-*`, the registry, the README or another manuscript was modified, and the `\bibliographystyle` line is unchanged.

## Summary of dispositions

| Report | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| 1 | 1. Raw denominator conclusion exceeds the kernel theorem (Prop. 4.1) | Major | Accepted |
| 1 | 2. Coefficient restriction adds no qualitative restriction; reframe Theorem C | Major | Accepted |
| 1 | 3. False numerical range after Theorem 3.1 | Minor | Accepted |
| 1 | 4. Ledger confuses two denominator sequences; Kano's exponent order | Minor | Accepted |
| 1 | 5. "Step function"; integrality and ranges of $d$; "positive lower density" | Minor | Accepted |
| 1 | 6. Grid of Lemma 2.4 versus the maximal-grid result; numerator hypothesis; conventions for $L=3,4$ | Minor | Accepted |
| 1 | 7. Public-facing package (offset, book pages, release links, summary, inquiries, packet) | Editorial | Accepted (release links partly: see entry) |
| 2 | 1. Cite Mira Cult's gist S08 beside Theorem 7.1 | Minor | Accepted |
| 2 | 2. Record verified open-access primary PDFs; mark unverified entries | Minor | Accepted |
| 2 | 3. Relax Lemma 2.4 to "$a$ prime to $p$" | Minor | Accepted |
| 2 | 4. AI disclosure in the reviewer-inquiry templates | Minor | Accepted |
| 2 | 5. Pin the `CompanionH` URL at release | Editorial | Declined here (deferred to the coordinator at release, as instructed) |
| 2 | 6. Hyperlink the Phase 19 scripts at `\phaseXIXcommit` | Editorial | Accepted |

---

## Report 1 (GPT-6.2 Astra)

### 1.1 Major: the raw denominator conclusion exceeds the kernel theorem. Accepted.

The referee is right. `raw_prime_support_infinite` (`Phase18Synthetic.lean:290`) proves that, when every $M$ divides some gap, every prime not dividing $b$ divides some gap repunit $\rho_{n_k-n_{k-1}}$ and infinitely many primes do. It says nothing about reduced raw coefficients. For general multipliers the conclusion is false: with $c_k=\rho_hb^{-h}$ every raw coefficient on the gap is $b^{-h}$.

- **Changes.** Proposition 4.1 now states exactly the Lean content (field identity, absolute convergence for bounded real multipliers, divisibility of the gap repunits and infinitude of their prime divisors), so the label *Kernel-verified* matches the statement (`paper.tex:421–434`). A new unnumbered paragraph after the proof (`paper.tex:447–455`) gives the written step for multipliers $1/m_k$ with $m_k$ a positive integer, which covers the valuation weights: $b-1\mid b^h-1$ gives the raw coefficient $1/(m_k\rho_h)$ with reduced denominator $m_k\rho_h$. It is marked as a written step, not formalized, and it records the referee's counterexample for general multipliers and the need for the gap hypothesis (a constant gap repeats one repunit). The subsection opening (`paper.tex:416–419`) now states the gap and numerator-one hypotheses instead of an unconditional claim. The data-availability section lists the written step among the non-formalized parts (`paper.tex:1375–1376`).
- **Companion files.** `VERIFICATION.md` row 4.1 and the "not kernel-verified" list; `submission/alphaxiv.md` (verification scope: "divisibility of the gap repunits (not the reduced raw coefficients, which need a written step)").

### 1.2 Major: the coefficient restriction adds no qualitative restriction. Accepted.

The referee's encoding is correct, and it makes the existence parts of Theorems 5.3, 6.1 and 6.4 consequences of classical realization. The paper now says so and states the restrictions its proofs actually achieve.

- **New Remark 6.5 (Qualitative content)** (`paper.tex:831–848`) proves the encoding. For any $y\in[0,1)$, any prime $p$ and any increasing schedule, $x=(1+y)b^{-m}$ has a greedy representation $\sum c_kb^{-n_k}$ with $c_k\in(0,1)$ of $p$-power denominator, and $b^mx\equiv y$. With Colebrook–Sigmund realization and Lemma 6.3 this gives every limit, every pair (via the segment $\{(1-\theta)\lambda+\theta\delta_0:\alpha\le\theta\le\beta\}$, on which $D=\theta$) and every limit set, even with a single denominator prime. The remark then names the content of the theorems: the uniform rate $O(N^{-1/3})$, the denominator bound $q_k\le pk$ with two explicit targets, the period bound $k$ on the state in Theorem 6.4, and the explicit arithmetic schedule of targets.
- **Statements strengthened to show these restrictions.** Theorem C (`paper.tex:94–107`): denominators divide $p^{1+\lfloor\log_pk\rfloor}\le pk$; the same schedule $tk^3$ throughout; $D_N=\Lambda_N/N+O(N^{-1/3})$ for the pairs; state period at most $k$ for the limit sets. Theorem 5.3 states $\mathrm{den}(c_k)\mid q_k\le pk$ and proves it from $q_{k-1}\mid q_k$ (`paper.tex:656–667`, `670–672`). Theorem 6.1 states the denominator bound, the two targets and the asymptotic formula (`paper.tex:711–717`).
- **Schedule factor $t$.** Theorem 6.4 is now stated and proved on $n_k=tk^3$ for every integer $t\ge1$ (`paper.tex:772–777`). The factor $t$ is carried through the construction (`paper.tex:805–812`: $n_k=tk^3$, $tK^3\le N<t(K+1)^3$, period bound $P_j\le K_j\le k$) and the limits ($N_j=tK_{j+1}^3$, stage weights at most $(K_j/K_{j+1})^3$; `paper.tex:816–818`).
- **Framing.** The introduction after Theorem C (`paper.tex:109–118`) now opens with "Qualitatively, Theorem C adds nothing to classical realization", credits Colebrook, Sigmund and DGS, and identifies the contribution as the uniform rate, the controlled denominators and the explicit schedule. The comparison with the signed spectrum says "with a uniform rate". The paragraph after Theorem 6.4 no longer claims that positive coefficients on $k^3$ "already suffice" as a result, and it cites Sigmund's Theorem 4.
- **Abstract and companion files.** Paper abstract (`paper.tex:22–43`), `metadata.toml`, `submission/abstract.txt` (244 words), `submission/alphaxiv.md` (abstract and scope), `submission/summary.md`, `submission/announcement.md` (forum paragraph; the X post already stated only the rate), `submission/reviewer-packet.md` §3 (new "Scope" paragraph), `LEDGER.md` (Theorem C entry: new "Encoding" bullet; relation changed to "inherited as existence statements", with the quantitative and arithmetic content listed), `VERIFICATION.md` (rows C, 5.3, 6.1, 6.4 and a new row 6.5).

### 1.3 Minor: the numerical range after the worked theorem is false. Accepted.

An exact enclosure confirms the referee: $N^{1/3}D_N(\xi)\approx7.0232$ at $N=2^{15}$, so "between 3 and 6" was false.

- **Changes.** New script `papers/07-synthetic-expansions/checks/xi_discrepancy.py` (standard library). It computes the binary expansion of $\xi$ exactly to $2^{18}+192$ bits, encloses each point by its 64-bit window, computes the extreme discrepancy of the windows exactly, and transfers it by Lemma 2.2 with error at most $2^{-62}$. The sentence after Theorem 3.1 (`paper.tex:398–401`) now gives the range $3.477$ ($N=2^{12}$) to $7.024$ ($N=2^{15}$) for $N=2^{10},\ldots,2^{18}$ and points to the script, which is listed in Section 10 (`paper.tex:1384–1386`). The full table is in `VERIFICATION.md` (new section "Finite certificate"). The value at $2^{10}$ reproduces the enclosure printed by `phase18_principal.py`. The constant 200 is unaffected.

### 1.4 Minor: the prior-art ledger confuses two denominator sequences. Accepted.

- **Kano's exponent order.** Checked against the primary scan (Osaka repository PDF, pp. 909–911). The general term is $A_n/(a^{\lambda_n}b^{\mu_n})$, and Theorem 1 is on p. 911 with hypotheses $\lambda_{n+1}>\lambda_n$, $\mu_{n+1}>\mu_n$, $a^{\lambda_n}\ll\mu_n$, $|A_n|\ll a^{\lambda_n}$ and $a^{\lambda_n-\lambda_{n-1}}\nmid A_n$. The paper (`paper.tex:166–168`) and the ledger now use this order and these hypotheses. (Report 2's table used the opposite order and p. 910; the scan settles this.)
- **Two sequences.** The introduction (`paper.tex:173–183`) distinguishes the insertion denominators $p^{sv_p(k)}$, which return to $1$, from the prefix denominators $p^{s\lfloor\log_pK\rfloor}$, which form a chain. It summarizes the regrouping test and states that the proof derives the positive side from a known exponential-sum estimate together with the exact prefix denominators, and does not apply a published series criterion. It also records the numerator-one and strict-chain hypotheses of Bailey–Crandall and Vandehey.
- **Ledger.** In the Theorem 4.5 entry the old reason is replaced by an explicit *Regrouping test* bullet, which reproduces the referee's argument and checks it against Kano's p. 911. The "Relation" bullet now separates derivation from application, and the outstanding-review item is narrowed to non-contiguous or unrelated representations. `submission/reviewer-packet.md` §1 and `reviewer-inquiry.md` Inquiry 1 were aligned.

### 1.5 Minor: qualify the central analytic object and its hypotheses. Accepted.

- "Step function" is replaced by "a function … with values in $\mathbb Z_p$, whose reduction modulo each power of $p$ is a finite step function" in the introduction (`paper.tex:137–139`), `submission/summary.md` and `reviewer-inquiry.md`. Section 7's own wording (`paper.tex:918`) already spoke of reductions.
- Integrality and ranges of $d$: the abstract now says "For an integer $d\ge2$" before the first use of $tk^d$ and "an integer $d\ge3$" for the quadratic theorem. Theorem D (`paper.tex:126`), the Section 7 standing hypothesis (`paper.tex:852`) and Theorem 4.5 ("any integer $d\ge2$") were updated, and so were `metadata.toml`, `abstract.txt`, `alphaxiv.md`, `summary.md`, the reviewer packet §4 and Inquiry 2.
- "Positive lower density" is kept in the introduction and now also in Inquiry 2 and the new comparison paragraph after Corollary 7.2.

### 1.6 Minor: distinguish the grid proved here from the maximal-grid result. Accepted.

- A paragraph after Lemma 2.4 (`paper.tex:310–313`) states that the lemma counts along one chosen admissible stride, that the $\tau$ progressions need not be distinct, and that $p^{e-c}$ need not be maximal. It also states that the exact period and the maximal grid are not used.
- `ARRANGEMENT.md` (§1 "kept" list and the OP-08 row) and `VERIFICATION.md` row 2.4 now describe the result as the stride count needed for Theorem 8.2, and record that the full Phase 19 statement ($\tau=\mathrm{lcm}(\mathrm{ord}_pb,\mathrm{ord}_Qb)$, $e<c$, exact period, largest equally spaced subset) is not included.
- Numerator hypothesis: Lemma 2.4 now asks only for $a$ prime to $p$ (see 2.3). The application in Theorem 8.2 (`paper.tex:1246–1247`) notes that the reduced prefixes have $a$ prime to $q$, a special case.
- Conventions: $\mathrm{ord}_1(2)=1$ and empty maximum $=0$ for $L\le4$ are stated in Theorem 8.2's proof (`paper.tex:1239–1241`).

### 1.7 Editorial: finish the public-facing package. Accepted (release links partly).

- **Periodic-word offset.** The comparison now uses $T^{o+j}y$ with $o$ the starting offset of the copy (`paper.tex:792–795`).
- **Book pages.** Graham–Kolesnik pages were read in the publisher's open-access Chapter 2 excerpt: Theorem 2.2 is on p. 8, and Lemma 2.5 with (2.3.2) on p. 10. Added in Lemma 7.6 (`paper.tex:998, 1001`) and in `VERIFICATION.md` (row 7.6, the GK91 note, external dependencies).
- **Release links.** `submission/alphaxiv.md` now links the manuscript directory, PDF, verification map, ledger and review directory at the planned release tag `manuscripts-v2.0.0`, the label in the byline. The file states that these links resolve once the tag is created. Partly accepted: no release commit exists yet, so the links cannot be pinned to a SHA in this worktree.
- **Summary.** `submission/summary.md` is now a single paragraph.
- **Inquiries.** Each template in `submission/reviewer-inquiry.md` now asks exactly one question. Inquiry 2's two questions were merged into the polynomial-schedule question.
- **Packet.** §3 now refers to the summation by parts as step 3 (inequality (2) of the paper). §5 requires a nonzero coefficient vector. §4 adds the prior art to weigh (2.1 below).
- **Declaration lists.** The Lean list in the proof of Theorem 4.5 was moved to the end of the proof, which also removed the underfull line the referee noted. The final LaTeX pass has no overfull or underfull boxes.

---

## Report 2 (Gemini 4 Argon)

### 2.1 Minor: cite Mira Cult's gist S08 beside Theorem 7.1. Accepted.

The gist was read at the pinned revision (raw file, 7 October 2026, *Normality research #2*). Note S08 is *Polynomial normality and cyclotomic rank criteria for Stoneham-type values*. Its Theorem 1.1: for $b,c,q\ge2$ with $q>2$ and a prime dividing $c$ and $q$ but not $b$, every nonconstant rational polynomial in $\sum_kq^{-k}b^{-c^k}$ is normal. The note calls its proofs conventional and not refereed or formally verified.

- **Changes.** New bibliography entry `MiraPoly`, pinned to the revision URL. A new paragraph "Comparison with exponential schedules" directly after Corollary 7.2 (`paper.tex:881–890`) contrasts S08's exponential schedule, monotone weight exponents and nonvanishing nonintegral algebraic tail with the polynomial valuation-weighted schedule, where the leading residue vanishes on a set of positive lower density, and states that neither result contains the other. The introduction's "Relation to earlier work" cites S08 and the ring precedents (`paper.tex:183–197`). `LEDGER.md` (Theorem 7.1 entry, "Closest unpublished or public-repository results") and `COMPANION-ASSESSMENT.md` ("Comparison with the normal-ring literature") credit S08 with the same contrast. The reviewer packet §4 lists it among the prior art.
- **Related strengthening, prompted by report 1's prior-art section.** The introduction and ledger now say that the normal rings of Wagner and Kano–Shiokawa (Theorem 5) are direct precedents for the normality of polynomial images of generators. They also say that the ring constructions' generator hypotheses were not verified for the numbers $X_a$. Wagner's content is reported only as described in Kano (1993, §1) and in the Kano–Shiokawa preprint (p. 1), both read; Wagner's own abstract could not be retrieved (HTTP 403). Nakai–Shiokawa is recorded in the ledger as a contrast (concatenation, not images).

### 2.2 Minor: record the verified open-access primary PDFs and mark unverified entries. Accepted.

- **Verified primary texts, recorded in `LEDGER.md` ("Verified against open-access primary texts").** Kano 1993 (Osaka scan, pp. 909–911, read for this revision). Kano–Shiokawa (Keio preprint KSTS/RR-91/006, p. 1, read for this revision; Theorems 4–5 and (15)–(16) as recorded in Paper I v2's ledger). Graham–Kolesnik (Cambridge excerpt, pp. 8 and 10, read for this revision). Sigmund 1974 (Theorem 4, pp. 293–295 and p. 285, from the checkpoint-18 primary-source audit `notes/phase18/reviews/classical-sources.md`; not re-read here). Mira Cult S08 (read).
- **Unverified entries.** `references.bib` now marks `Colebrook` and `Wagner95` with `note = {Unverified: bibliographic record checked; full text not read …}`. Both are listed under "Unverified items" in the ledger with the reason: Colebrook's publisher returned an access challenge, and Wagner's publisher and zbMATH returned HTTP 403. The Erdős–Turán theorem number in Kuipers–Niederreiter remains listed as not re-checked. `VERIFICATION.md` replaces the secondary confirmation of the Graham–Kolesnik numbering by the primary excerpt.

### 2.3 Minor: relax Lemma 2.4 to "$a$ prime to $p$". Accepted.

Lemma 2.4 now reads "for every integer $a$ prime to $p$ (not necessarily prime to $Q$)" (`paper.tex:282–283`). The proof states the two facts used: $a$ is a unit modulo $p^e$, and $ay^m\equiv a\pmod Q$ for every $a$ (`paper.tex:296–298`). The Lean citation notes that `crt_period_count` assumes only $p\nmid a'$ (`paper.tex:306–307`), which was checked at `c2c9da6:NormalityChecker/PrimePowerGrid.lean:333–339`. This matches the invocation in Theorem 8.2. `VERIFICATION.md` row 2.4 was updated.

### 2.4 Minor: AI disclosure in the inquiry templates. Accepted.

Both templates in `submission/reviewer-inquiry.md` now state that the manuscript was produced in an AI-assisted research project. They say which parts are kernel-checked in Lean 4 (Inquiry 1) or not formalized (Inquiry 2), and that the written proofs and literature comparisons have been checked only by AI models and await review by a human specialist.

### 2.5 Editorial: pin the `CompanionH` URL at release. Declined in this revision.

As instructed by the coordinator, the `CompanionH` entry in `references.bib` is unchanged. The coordinator pins it to `manuscripts-v2.0.0` at release, together with the global bibliography-style switch.

### 2.6 Editorial: hyperlink the Phase 19 scripts. Accepted.

`scripts/phase19_grids.py` and `scripts/phase19_nonlinear.py` are now hyperlinked at `\phaseXIXcommit` (`paper.tex:1380–1382`). Both files exist at `c2c9da6`.

---

## Questions reserved for a human specialist

1. **Theorem 4.5 versus the series criteria.** Is the normality switch a consequence of Kano (1993, Theorem 1), Bailey–Crandall (2002, Theorem 4.8) or Vandehey (2019, Theorem 7.4) under some representation of $X_s$ other than contiguous regrouping? The regrouping test in the ledger excludes only contiguous groupings on the cubic schedule.
2. **Section 7 (paper proof, not formalized).** The collision bound (3) in Lemma 7.7: its uniformity in $I$, the lattice count of the slab and the removal costs. Also the third-derivative regime $\lambda=lp^H\Lambda/p^{3v}$ with $2H/5\le v\le H$, the second-moment constants in Proposition 7.8, and the freezing threshold in Lemma 7.4. Two AI referees and an earlier AI audit found no gap, which is not peer review.
3. **Priority for Theorem 7.1.** Do the generator hypotheses of the normal rings of Wagner (1995) and Kano–Shiokawa (1993), or the method of Mira Cult's S08, cover the numbers $X_a$ on the polynomial schedule $ti^d$? Wagner's full text was not accessible to this revision.
4. **Remark 6.5 and Theorem C.** Is the encoding of an arbitrary orbit by positive $p$-power-denominator coefficients recorded in the literature (for example in work after Stoneham and Kano on prescribed numerators)? Is the rate $O(N^{-1/3})$, uniform in $\delta$, improvable for these arithmetic realizations?
5. **Theorem 8.2.** The loss bound $c\le1+J_3$ through $v_3(\ell-1)<\log_3L$, and the comparison with Korobov, Kano and Vandehey on moduli that acquire every odd prime.
6. **Bibliography.** Check Colebrook (1970) and Wagner (1995) against their full texts, and the Erdős–Turán numbering in Kuipers–Niederreiter (Ch. 2, Theorem 2.5, p. 112).
