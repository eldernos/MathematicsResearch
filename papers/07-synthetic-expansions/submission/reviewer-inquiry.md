# Reviewer inquiry templates (drafts for the owner; not to be sent as is)

These drafts use placeholders only. Before sending, check that the cited paper is the addressee's own, and adjust the wording.

---

## Inquiry 1: the normality switch and Korobov-type criteria

Dear [Name],

I am writing about a preprint draft, *Synthetic Arithmetic Expansions and Prescribed Discrepancy*. Its first theorem concerns the series

$$X_s=\sum_{k\ge1}p^{-s v_p(k)}\,b^{-n_k},$$

where $p\nmid b$ is prime, $t=\operatorname{ord}_p(b)$, and $(n_k)$ is any strictly increasing sequence of multiples of $t$ with $n_k\ge k^2$. The theorem says that $X_s$ is normal to base $b$ for every $s\ge1$, while its extreme discrepancy tends to one for $s=0$. After the $K$th insertion the reduced denominator of the shifted prefix is exactly $p^{s\lfloor\log_pK\rfloor}$. This statement and the switch have been checked in Lean 4; the written proof uses a fixed-support short-orbit estimate.

Your work [cite: e.g. *Differencing methods for Korobov-type exponential sums*, J. Anal. Math. 138 (2019), or the addressee's relevant paper] gives the closest results I found. In particular, Theorem 7.4 there treats series $\sum1/(c_kb^{m_k})$ with $c_k\mid c_{k+1}$ supported on a fixed finite set of primes. The valuation weights $p^{-sv_p(k)}$ do not form such a chain, so I have not been able to deduce the switch directly from that theorem or from Kano's Theorem 1 (Osaka J. Math. 1993).

**Question.** Is the switch, possibly after regrouping the series, a known consequence of the Korobov–Stoneham–Kano criteria or of your Corollary 1.2? If so, which reference should be cited?

The verification map and the exact Lean statements are at [link to `papers/07-synthetic-expansions/VERIFICATION.md` at the release commit].

With thanks,
Christopher Anderson

---

## Inquiry 2: the sharp translation identity and Rauzy's theorem

Dear [Name],

A preprint draft of mine, *Synthetic Arithmetic Expansions and Prescribed Discrepancy*, proves the finite identity

$$\sup_{x\in\mathbb R}\bigl|D_N(x+z;b)-D_N(x;b)\bigr|=1-D_N(z;b),$$

attained at $x=0$, for the extreme discrepancy $D_N$ of the radix orbit. It deduces that adding $z$ preserves the limiting discrepancies of every real number exactly when $z=c+w$, where $(b-1)c\in\mathbb Z$ and the mean of $\lVert b^nw\rVert$ tends to zero. This class is strictly smaller than Rauzy's class of normality-preserving translations; for example, $z=1/3$ in base 2 preserves normality but not numerical discrepancy. As a consequence, the possible limits of $D_N(x)$, $D_N(y)$ and $D_N(x+y)$ are exactly the triples with $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$. Your Proposition 4.9 and Corollary 4.10 in [cite: *On preservation of normality and determinism under arithmetic operations*, arXiv:2506.12929] give the same inequalities for point entropy.

**Question.** Is the finite identity above, or its consequence for the addition spectrum of discrepancy, recorded in the literature on concentration functions or on Kuiper's statistic? I would like to cite the earliest source correctly.

With thanks,
Christopher Anderson
