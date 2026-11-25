# Reviewer packet: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v1.0)

**Author:** Christopher Anderson (Independent Researcher).

**Review status:** human specialist review is outstanding. Cross-model AI review is not peer review.

**Notation.** $b\ge2$, $\{y\}$ is the fractional part, $\lVert y\rVert$ is the distance to $\mathbb Z$, and

$$D_N(x)=\sup_{0\le a<c\le1}\Bigl|\tfrac1N\#\{n<N:\{b^nx\}\in[a,c)\}-(c-a)\Bigr|.$$

Normality to base $b$ is equivalent to $D_N\to0$ (Kuipers–Niederreiter, Ch. 1 Thm 8.1, p. 70; Ch. 2 Thm 1.1, p. 89).

## 1. Normality switch (Theorem 4.4) and exact denominators (Theorem 4.2)

**Statement.** Let $p\nmid b$ be prime and $t=\operatorname{ord}_p b$, and let $(n_k)$ be strictly increasing multiples of $t$ with $n_k\ge k^2$. Put $X_s=\sum_kp^{-sv_p(k)}b^{-n_k}$. Then:

- for $n\ge n_K$, the reduced denominator of $b^n\sum_{k\le K}p^{-sv_p(k)}b^{-n_k}$ is $p^{s\lfloor\log_pK\rfloor}$;
- $D_N(X_0)\to1$, and $D_N(X_s)\to0$ for $s\ge1$.

**Evidence.** Kernel-verified, at commit `e4809cf`: `RetirementDenominator.shiftedPrefix_den` (L110), `discrepancy_switch` (L436) and `normal_iff_pos` (L444).

**Proof sketch.**

1. Modulo $p$, only the indices $k=p^Jm$ with $p\nmid m$ and $m<p$ survive in $p^{sJ}b^nU_K$. Each contributes $b^n$, and there are between 1 and $p-1$ of them.
2. For $s=0$ every prefix is an integer and the tail is $O(b^{-W})$ away from insertions, so the orbit concentrates at $0$.
3. For $s\ge1$, take blocks of length $N^{1/4}$. A fixed-support estimate (Lemma 4.3, kernel-verified, the qualitative form of Vandehey's Corollary 1.2) controls Weyl sums on blocks whose denominator is large and polynomially bounded.

**Review wanted.** Is the switch already a corollary of Kano (1993, Theorem 1), of Bailey–Crandall (2002, Theorem 4.8), or of Vandehey (Theorem 7.4) after regrouping?

## 2. Worked rate (Theorem 3.1)

**Statement.** $\xi=\sum_k3^{-v_3(k)}2^{-2k^3}$ satisfies $D_N(\xi;2)\le200N^{-1/3}$ for all $N\ge1$.

**Evidence.** Paper proof (Section 3).

**Proof sketch.**

1. By Step 1 above, the prefix has reduced denominator $3^J$ with $3^J\le k<3^{J+1}$ on block $k$.
2. Since 2 is a primitive root modulo $3^e$, a full period consists of two grids of mesh $3^{1-e}$. Hence any $L$ consecutive points have count error at most $3L/3^J+3^J$ (Corollary 2.5).
3. Summing over blocks gives $127K^2$. A buffer of $W=\lceil\log_2(K+1)\rceil+2$ positions before each insertion, together with Lemma 2.3, gives $67.5/K$.

**Review wanted.** Check the arithmetic constants in Step 4.

## 3. Every discrepancy limit (Theorem 5.3)

**Statement.** For odd $p\nmid b$ and $\delta\in[0,1]$, the positive coefficients defined in Lemma 5.1 from the targets $u_k\in\{0,1/q_k\}$, where $q_k=p^{1+\lfloor\log_pk\rfloor}$, with retirement mask $a_k=\lfloor k\delta\rfloor-\lfloor(k-1)\delta\rfloor$, satisfy $|D_N(x_\delta)-\delta|\le C_{b,p}N^{-1/3}$, uniformly in $\delta$.

**Evidence.** Lean-supported paper proof; the state recurrence is kernel-verified.

**Key steps.**

1. Proposition 5.2: $|D_N-Z/N|\le(H+(K+1)W)/N+2\frac b{b-1}b^{-W}$.
2. Corollary 2.5 bounds the active error $H$ by $(7tp^v+p)K(K+1)/2$.
3. Summation by parts gives $|Z-\delta N|\le t+3h_K$.

**Review wanted.** The summation by parts in (2), and uniformity in $\delta$.

## 4. Sharp translation identity (Theorem 7.1) and preservers (Theorem 7.4)

**Statement.** $\sup_x|D_N(x+z)-D_N(x)|=1-D_N(z)$, attained at $x=0$. Moreover $D_N(z)\to1$ if and only if $z=c+w$ with $(b-1)c\in\mathbb Z$ and $N^{-1}\sum_{n<N}\lVert b^nw\rVert\to0$, and this is equivalent to preservation of both limiting discrepancies for every $x$.

**Evidence.** The identity is kernel-verified (`SharpTranslation.sharp_translation_isGreatest`, L386). The classification is a paper proof.

**Proof sketch.**

- *Identity.* For an arc $J$ of length $l$ and centre $c$ containing a proportion $1-e$ of the orbit of $z$, the orbit of $x+z$ is within $l/2$ of the rotated orbit of $x$ off a proportion $e$. Lemma 2.2 then bounds the change by $e+l$. Taking the infimum over $J$ gives $1-D_N(z)$, and $D_N(0)=1$ gives equality.
- *Classification.* Nearly maximizing arcs shrink while carrying almost all the mass, so every limit measure is a point mass at a fixed point. The limit set is connected, so the fixed point is unique.

**Review wanted.** Is the identity folklore, for instance via Lévy's concentration function or Kuiper's statistic?

## 5. Addition spectrum (Theorems 8.1–8.3)

**Statement.** The limits $(\alpha,\beta,\gamma)$ of $D_N(x)$, $D_N(y)$ and $D_N(x+y)$ are exactly the triples with $\max(0,\alpha+\beta-1)\le\gamma\le1-|\alpha-\beta|$. They are realized at rate $O(N^{-1/3})$ by one-prime cubic positive expansions. For $d$ summands the deficits are exactly the vectors with $e_i\le\sum_{j\ne i}e_j$.

**Evidence.**

- The qualitative triple theorem is kernel-verified (`AdditionSpectrum.exact_addition_spectrum`, L1486, commit `c2c9da6`).
- The rate is a Lean-supported paper proof.
- The $d$-summand case is a Lean-supported paper proof; its realization step is `mixtureRealizable`.

**Proof sketch.**

- *Necessity:* two applications of the identity.
- *Sufficiency:* five types with state pairs $(0,0)$, $(u,0)$, $(0,u)$, $(u,-u)$, $(u,u)$ and weights $\sigma$, $\beta-\sigma$, $\alpha-\sigma$, $\gamma-\sigma$, $1-\alpha-\beta-\gamma+2\sigma$, where $\sigma=\max(0,(\alpha+\beta+\gamma-1)/2)$, chosen by a deficit scheduler.

**Prior work to compare.** Bergelson–Downarowicz (arXiv:2506.12929, Proposition 4.9 and Corollary 4.10) give the same inequalities for point entropy.

**Review wanted.** Is the discrepancy version a routine consequence of the entropy version? It should not be, because $1-D$ and normalized entropy differ off the mixtures $\theta\delta_0+(1-\theta)\lambda$.

## 6. Infinite sums (Theorems 10.2–10.4)

**Statement.** $Y=\sum_{\ell\ \mathrm{odd}}\sum_{j\ge1}\ell^{-s_\ell j}2^{-16^{\ell^j}}$, with $s_3=2$ and $s_\ell=1$ otherwise, is binary normal and Liouville with $D_N\ll1/\log N$. Finite rational combinations of the components are normal. Some positive rational multiples of the components sum to $1$.

**Evidence.** Lean-supported paper proof; the grid order and count steps are Lean, at `c2c9da6`.

**Proof sketch.**

1. The reduced prefix denominator is $q=3^{2J_3}Q$.
2. With $\tau=\operatorname{lcm}(2,\operatorname{ord}_Q2)$, the loss $c=v_3(2^\tau-1)=1+v_3(\operatorname{ord}_Q2)$ is at most $1+J_3$, so every full stride period contains grids of size at least $3^{J_3-1}>L/9$.
3. The periods are at most $q\le N^{1/2+o(1)}$, by $\prod_{\ell\le x}\ell<4^x$.
4. For the Liouville property, CRT gives long gaps between prime-power labels.

**Review wanted.**

- The loss bound in Step 2. It uses only $v_3(\ell-1)<\log_3L$; no lower bound on order valuations is used, so the prime-5 argument retracted from an earlier review plays no role.
- Comparison with Korobov (1972), Kano (1993) and Vandehey (Theorem 7.4) on varying moduli.

## Not claimed

- The normality of $\xi^2$ is mentioned in Section 11, with a pinned link to a written proof and its AI audit. It is not a claim of this paper.
- Rates for $d\le s+1$ are not claimed.
- A rate for the $d$-summand spectrum is not claimed.

**Reproduction.** See `VERIFICATION.md` (Reproduce) for the Lean and Python commands, and for the build command `wsl -d Ubuntu -- bash papers/wsl-build.sh 07-synthetic-expansions`.
