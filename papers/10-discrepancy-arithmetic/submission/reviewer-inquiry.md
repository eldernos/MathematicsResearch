# Reviewer inquiry templates (drafts for the owner; not to be sent as is)

These drafts use placeholders only. Before sending, check that the cited paper is the addressee's own, and adjust the wording.

---

## Inquiry 1: the addition spectrum and point entropy

Dear [Name],

I am writing about a preprint draft, *The Arithmetic of Extreme Discrepancy: Translation, Addition Spectra and Rational Operations*. For the extreme discrepancy $D_N$ of the radix orbit in base $b$, it proves that the limits of $D_N(x)$, $D_N(y)$ and $D_N(x+y)$ are exactly the triples in $[0,1]^3$ with

$$\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|,$$

the inequalities holding already at each finite $N$; every triple is realized by explicit positive rational expansions with error $O(N^{-1/3})$.

Your Proposition 4.9 and Corollary 4.10(1) in [cite: *On preservation of normality and determinism under arithmetic operations*, arXiv:2506.12929] give the corresponding inequalities for lower and upper point entropy, and in normalized deficit coordinates the two polytopes coincide. The paper credits this and points out that the observables differ off the mixtures $\theta\delta_0+(1-\theta)\lambda$ (for instance on periodic orbits). Section 4.3 of your paper studies attainability of the entropy bounds.

**Question.** Is the full five-vertex polytope known to be the exact set of attainable entropy triples, so that the discrepancy statement should be presented as a parallel of a known complete description, or is completeness open on the entropy side?

The verification map and exact Lean statements are at [link to `papers/10-discrepancy-arithmetic/VERIFICATION.md` at the release commit].

With thanks,
Christopher Anderson

---

## Inquiry 2: the translation identity and Kuiper's statistic

Dear [Name],

A preprint draft of mine proves, for the extreme (Kuiper) discrepancy $D_N$ of the radix orbit, the finite identity

$$\sup_{x\in\mathbb R}\bigl|D_N(x+z)-D_N(x)\bigr|=1-D_N(z),$$

attained at $x=0$. The proof uses only rotation invariance and a one-paragraph comparison of paired samples; it gives $D(q)\le D(p)+1-D(r)$ for any paired samples with $q_n\equiv p_n\pm r_n$. The paper rewrites $1-D(\mu)$ as $\inf_l(1-Q_\mu(l)+l)$ with Lévy's concentration function $Q_\mu$, and compares it within a factor $3$ with the Ky Fan distance to constants. Your work on [cite: the addressee's paper on discrepancy, concentration functions or probability metrics] is the closest source I found.

**Question.** Is the paired-sample inequality $D(q)\le D(p)+1-D(r)$, or its sharp form above, recorded in the literature on Kuiper's statistic or on concentration functions, so that it can be cited rather than presented as a lemma?

With thanks,
Christopher Anderson
