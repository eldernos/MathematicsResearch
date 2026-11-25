# Mathematical summary

For an integer base $b\ge2$ and a prime $p\nmid b$ with $t=\operatorname{ord}_p(b)$, the paper studies sums $\sum_kc_kb^{-n_k}$ whose shifted rational prefixes are controlled exactly.

**The valuation family.** With $c_k=p^{-sv_p(k)}$ and $t\mid n_k$, the reduced denominator after the $K$th insertion is exactly $p^{s\lfloor\log_pK\rfloor}$. Hence the number is normal for $s\ge1$, and has discrepancy tending to one for $s=0$, on every schedule with $n_k\ge k^2$; this is kernel-verified. For $n_k=tk^d$ with $d\ge s+2$, complete periods of $p$-power denominators give $D_N\ll N^{-s/d}+N^{-(d-s-1)/d}+N^{-(d-1)/d}\log N$; for the binary cubic example, $D_N\le200N^{-1/3}$.

**Prescribing the orbit.** Choosing $c_k\in(0,1]$ to force a prescribed rational state at each insertion, and retiring a weighted proportion of the gaps, realizes:

- every limiting discrepancy $\delta\in[0,1]$, at rate $O(N^{-1/3})$ uniformly in $\delta$;
- every pair of lower and upper limits;
- every nonempty compact connected set of invariant measures, as the limit set of the orbit measures.

**Addition.** The finite identity $\sup_x|D_N(x+z)-D_N(x)|=1-D_N(z)$ (kernel-verified) makes $1-D_N(x-y)$ a pseudometric. Its limit vanishes exactly for $z=c+w$ with $(b-1)c\in\mathbb Z$ and mean circular displacement of $w$ tending to zero; this class is strictly smaller than Rauzy's class of normality-preserving translations. The identity gives the necessary half of the exact addition spectrum $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$ for the limits of $D_N(x)$, $D_N(y)$ and $D_N(x+y)$. The qualitative spectrum is kernel-verified, and the cubic construction realizes every admissible triple at rate $O(N^{-1/3})$.

**Infinite support.** A distinguished prime $3$ with doubled order keeps a growing arithmetic grid in every reduced prefix. As a result, $\sum_{\ell\text{ odd}}\sum_j\ell^{-s_\ell j}2^{-16^{\ell^j}}$, with $s_3=2$ and $s_\ell=1$ otherwise, is normal and Liouville with $D_N=O(1/\log N)$. By contrast, positive rational multiples of its jointly normal components can sum to any positive rational.
