# Specialist Reviewer Inquiry Templates — Paper IV (Version 2.0)

*Drafts for repository owner use only. Replace `[Name]` before any manual correspondence; do not send automatically.*

---

## Template 1: Analytic number theory / exponential sums and normal numbers

**Subject:** Question on overlap rigidity for smooth rational orbit models (preprint draft)

Dear Professor [Name],

I am writing as an independent researcher working on a preprint draft, *Arithmetic Certificates for Normality and Mathematical Limitations* (version 2.0), which includes a Lean 4 formalization of a qualitative form of Vandehey's short exponential-sum estimate on fixed smooth supports (*Differencing methods for Korobov-type exponential sums*, J. Anal. Math. 138 (2019), 405–439, Corollary 1.2) and uses it to establish a finite-overlap rigidity obstruction (Theorem 3.1 and Corollary 3.2).

Specifically, Theorem 3.1 shows that for coprime integers $b, c \ge 2$ and any $d \ge 0$, there exists $\gamma(b,c,d) > 0$ such that any two noncongruent rationals $y, z$ with $c$-supported reduced denominators at most $T^d$ incur combined mean circle error at least $\gamma$ against any real sequence $f_0,\dots,f_{T-1}$ on a segment of length $T$, forcing eventually constant denominators along any compatible overlapping chain. Because your published work on Korobov-type exponential sums and arithmetic normality constructions directly governs this fixed-support regime, I would be very grateful for a brief opinion on one question: have you seen this finite-overlap separation or denominator-constancy obstruction stated in the normal-numbers or exponential-sum literature?

Full disclosure: this preprint was produced in an AI-assisted project (with Lean 4 kernel checking of Theorem 1.2, Theorem 3.1, and the individual formal components listed in `VERIFICATION.md`, and cross-model AI review only — no independent human peer review yet). I can send the short reviewer packet (`reviewer-packet.md`) or PDF if you have time to glance at it.

Sincerely,  
Christopher Anderson  
Independent Researcher  
(Comments/issues: https://github.com/eldernos/MathematicsResearch/issues)

---

## Template 2: Computability and descriptive complexity of normal numbers

**Subject:** Question on a Lean-formalized two-limit promise reduction for binary normality

Dear Professor [Name],

I am an independent researcher preparing version 2.0 of a preprint draft, *Arithmetic Certificates for Normality and Mathematical Limitations*, and would welcome your perspective on the positioning of Section 7 (Theorems 7.3–7.4 and Corollary 7.5).

In your paper with Heiber and Slaman (*Normal numbers and the Borel hierarchy*, Fundamenta Mathematicae 226 (2014), 63–77, Theorem 3.2 and Corollaries 3.3–3.4, p. 67), you construct an effective reduction to normality in all bases versus in no base, establishing effective $\Pi^0_3$-completeness and boldface Borel $\boldsymbol{\Pi}^0_3$-completeness for absolute and fixed-base normality. In Section 7 of our draft, we use individually Lean 4 kernel-verified single-switch halting reductions over arbitrary digit-oracle codes `Nat.Partrec.Code` (`Names`) that enforce transcendence and the exact two-limit discrepancy promise $D_N^{(2)} \to 0$ or $1$ on every output, proving nondecidability, non-c.e., and non-co-c.e. under explicit endpoint hypotheses (discharged on paper by an elementary Liouville-normal construction in Proposition 7.2). We frame this strictly as an elementary formalizable two-limit promise reduction rather than any completeness claim.

Could I ask one focused question: is the distinction we draw between recognition on this narrower $\{0,1\}$-discrepancy promise over total bit-oracle names and the boldface Borel / unrestricted effective $\Pi^0_3$-completeness classifications of Ki–Linton (1994) and Becher–Heiber–Slaman (2014) accurate?

Full disclosure: this preprint was produced in an AI-assisted project; the Lean kernel checked the individual formal reduction and nonrecognizability declarations in Section 7 under explicit endpoint hypotheses, while the written proofs, endpoint construction, and literature positioning have so far been reviewed only by AI models and not by an independent human specialist.

Sincerely,  
Christopher Anderson  
Independent Researcher  
(Comments/issues: https://github.com/eldernos/MathematicsResearch/issues)
