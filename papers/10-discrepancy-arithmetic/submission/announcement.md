# Announcement drafts (not to be posted without the owner's approval)

## Post for X (at most 280 characters)

Preprint draft: for base-b discrepancy, sup_x |D_N(x+z)-D_N(x)| = 1-D_N(z), and the limit triples for x, y, x+y are exactly max(0,α+β-1) ≤ γ ≤ 1-|α-β|. Lean-checked core; classical ingredients credited; written proofs await expert review.

## Paragraph for a mathematics forum

This preprint draft studies how the extreme discrepancy $D_N$ of the radix orbit $x,bx,b^2x,\ldots$ behaves under the arithmetic of $\mathbb R$. Translating by $z$ changes $D_N$ by at most $1-D_N(z)$, with equality at $x=0$; the translations that preserve the limiting discrepancies of every input are classified, and they form a strictly smaller class than Rauzy's normality-preserving translations. The limits of $D_N(x)$, $D_N(y)$ and $D_N(x+y)$ fill exactly the polytope $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$, realized by explicit positive rational expansions at rate $O(N^{-1/3})$. The same polytope appears in Bergelson and Downarowicz's inequalities for point entropy, a different quantity. The deficit $1-D_N(x-y)$ is a pseudometric built from classical ingredients (Kuiper's statistic, Lévy's concentration function, Ky Fan distance), whose kernel is preserved by exactly the rational scalars $\mathbb Z[1/b]$. The core identities are checked in Lean 4; the rates and classifications are written proofs checked only by AI models, and comments from specialists are very welcome.
