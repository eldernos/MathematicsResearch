# Reviewer packet: The Arithmetic of Extreme Discrepancy (v1.0)

**Author:** Christopher Anderson (Independent Researcher).

**Review status:** human specialist review is outstanding. Cross-model AI review is not peer review.

**Notation.** $b\ge2$, $\{y\}$ is the fractional part, $\lVert y\rVert$ the distance to $\mathbb Z$, and

$$D_N(x)=\sup_{0\le a<c\le1}\Bigl|\tfrac1N\#\{n<N:\{b^nx\}\in[a,c)\}-(c-a)\Bigr|.$$

$M_N(w)=N^{-1}\sum_{n<N}\lVert b^nw\rVert$, and $K_b=\{z:D_N(z)\to1\}$. Lean links: `E` = commit `e4809cf561573aef588e6ffc491a35cdb79fd9ec`, `P` = commit `c2c9da683666b3b9368e5d4b5cb858caccf528f5`.

## 1. Sharp translation identity (Theorem 3.1)

**Statement.** For all real $x,z$ and $N\ge1$, $|D_N(x+z)-D_N(x)|\le1-D_N(z)$, with equality at $x=0$.

**Proof.** $D$ of a sample equals the supremum of the excess $\mu(I)-|I|$ over half-open arcs, and is rotation invariant (complementation). For samples $u,v$ with $E$ indices at circle distance $>\epsilon$, $|D(u)-D(v)|\le E/N+2\epsilon$ (enlarge each arc by $\epsilon$). Given an arc $J$ of length $l$ and centre $c$ containing a proportion $1-e$ of the points $\{b^nz\}$, the sample $b^n(x+z)$ is within $l/2$ of the rotated sample $b^nx+c$ off a proportion $e$; hence the change is at most $e+l=1-(\mu^z_N(J)-l)$; take the infimum over $J$. $D_N(0)=1$ gives equality.

**Evidence.** Kernel-verified: `SharpTranslation.sharp_translation` (E, L343), `sharp_translation_zero` (L378), `sharp_translation_isGreatest` (L386).

## 2. Universal preservers (Theorem 3.3)

**Statement.** $D_N(z)\to1$ iff translation by $z$ preserves both limiting discrepancies of every input iff $z=c+w$ with $(b-1)c\in\mathbb Z$ and $M_N(w)\to0$.

**Proof sketch.** The first equivalence is Theorem 3.1 at $x=0$. If $D_N(z)\to1$, near-optimal arcs $J_N$ shrink and carry mass $\to1$; comparing $\{b^nz\}$ and $\{b^{n+1}z\}$, both in $J_N$ for most $n$, gives $\lVert(b-1)c_N\rVert\le(b+1)|J_N|$ for the centres $c_N$, so the centres approach the finite set of fixed points; consecutive empirical measures differ by $O(1/N)$, so the nearest fixed point is eventually constant. The converse uses Markov's inequality.

**Evidence.** Lean-supported paper proof (step: Theorem 3.1). **Review wanted:** the eventual constancy argument.

## 3. Addition spectrum and cubic rate (Theorems 5.1, 5.3, 5.4)

**Statement.** The triples of limits of $(D_N(x),D_N(y),D_N(x+y))$ are exactly the $(\alpha,\beta,\gamma)\in[0,1]^3$ with $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$. For an odd prime $p\nmid b$, $t=\operatorname{ord}_p b$, each triple is realized by $x=\sum c_kb^{-tk^3}$, $y=\sum d_kb^{-tk^3}$ with $c_k,d_k\in(0,1]$ of $p$-power denominator and error $\le C_{b,p}N^{-1/3}$, uniformly; the witnesses can be algebraically independent and computable from names.

**Proof sketch.** Necessity: two applications of Theorem 3.1. Sufficiency: convex weights $\sigma,\beta-\sigma,\alpha-\sigma,\gamma-\sigma,1-\alpha-\beta-\gamma+2\sigma$ ($\sigma=\max(0,(\alpha+\beta+\gamma-1)/2)$) on the five state pairs $(0,0),(u,0),(0,u),(u,-u),(u,u)$, $u=1/q_k$, $q_k=p^{1+\lfloor\log_pk\rfloor}$; a greedy deficit scheduler keeps overcounts in $[-4,1]$; the positive state recurrence (kernel-verified) sets the states; complete prime-power periods bound the active count error by $O(K^2)$; summation by parts gives $|Z-\delta N|\le t+17h_K$; real tails are geometric. Independence: overrides at blocks $k=2^j$ choose, among $(d_X+1)(d_Y+1)$ candidates with distinct coordinates, one where the next polynomial is nonzero, certified by interval arithmetic that survives all positive continuations.

**Evidence.** Theorem 5.1 Kernel-verified (`AdditionSpectrum.exact_addition_spectrum`, P L1486; `finite_necessity`, L248; `mixtureRealizable`, L1470). Theorems 5.3 and 5.4 Lean-supported paper proofs (positive state recurrence, `Phase18Synthetic.programState_fract`, E L383, and companions; the full-period prime-power count `PrimePowerGrid.primePower_period_count`, P L313, used through Lemma 2.4). **External inputs:** none. **Review wanted:** scheduler bounds and the certificate argument.

**Precedent.** Bergelson–Downarowicz, arXiv:2506.12929, Prop. 4.9 and Cor. 4.10(1): the same polytope for normalized point entropy, a different observable.

## 4. Rational scalars (Theorem 4.5, Proposition 4.6)

**Statement.** For reduced $a/d$, $(a/d)K_b\subseteq K_b$ iff every prime of $d$ divides $b$. For $z\in K_b$ with limiting fixed point $c$ and $k_n$ nearest to $b^nz-c$, $(a/d)z\in K_b$ iff some residue class modulo $d$ contains $k_n$ for a density-one set of $n$.

**Proof sketch.** A rational lies in $K_b$ iff its denominator divides $b^j(b-1)$. Test the multiplier on $1/(b-1)$. For the individual test, $b^nz/d$ lies near $(c+k_n)/d$, and the $d$ possible values are $1/d$-separated.

**Evidence.** Theorem 4.5 is a Lean-supported paper proof (Lean step: the subgroup property of $K_b$, from the kernel-verified triangle inequality for the asymptotic distance, `DiscrepancyGeometry.asymDist_triangle`, P L390); Lemma 4.4 and the valuation argument are written. Proposition 4.6 is a paper proof. **External input:** Bergelson–Downarowicz Prop. 4.25 (rational multiples preserve normality), used only for a remark.

## 5. Integer dilation (Theorem 6.2)

**Statement.** If $D_N(mx)\to1$, then $\liminf D_N(x)\ge1/m_0$ ($m_0$ the part of $|m|$ prime to $b$), and every $\delta\in[1/m_0,1]$ occurs, at rate $O(N^{-1/3})$.

**Proof sketch.** $m_0x\in K_b$, so the orbit of $x$ concentrates near an $m_0$-point grid; conversely program the invariant law $\theta\delta_0+(1-\theta)U_{m_0}$, whose discrepancy is $\theta+(1-\theta)/m_0$, by cycle types on the cubic schedule.

**Evidence.** Lean-supported paper proof.

## Reproduction

`papers/10-discrepancy-arithmetic/VERIFICATION.md` lists every Lean declaration with pinned links and the exact finite checks (`scripts/phase19_addition.py`, `notes/phase19/reviews/addition_check.py`, `notes/phase19/reviews/geometry-periods-check.py`).
