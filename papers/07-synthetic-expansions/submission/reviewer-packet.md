# Reviewer packet: Synthetic Arithmetic Expansions and Prescribed Discrepancy (v1.0)

**Author:** Christopher Anderson (Independent Researcher).

**Review status:** human specialist review is outstanding. Cross-model AI review is not peer review.

**Notation.** $b\ge2$, $\{y\}$ is the fractional part, $\lVert y\rVert$ is the distance to $\mathbb Z$, and

$$D_N(x)=\sup_{0\le a<c\le1}\Bigl|\tfrac1N\#\{n<N:\{b^nx\}\in[a,c)\}-(c-a)\Bigr|.$$

Normality to base $b$ is equivalent to $D_N\to0$ (Kuipers–Niederreiter, Ch. 1 Thm 8.1, p. 70; Ch. 2 Thm 1.1, p. 89).

## 1. Normality switch (Theorem 4.5) and exact denominators (Theorem 4.2)

**Statement.** Let $p\nmid b$ be prime and $t=\operatorname{ord}_p b$, and let $(n_k)$ be strictly increasing multiples of $t$ with $n_k\ge k^2$. Put $X_s=\sum_kp^{-sv_p(k)}b^{-n_k}$. Then:

- for $n\ge n_K$, the reduced denominator of $b^n\sum_{k\le K}p^{-sv_p(k)}b^{-n_k}$ is $p^{s\lfloor\log_pK\rfloor}$;
- $D_N(X_0)\to1$, and $D_N(X_s)\to0$ for $s\ge1$.

**Evidence.** Kernel-verified, at commit `e4809cf`: `RetirementDenominator.shiftedPrefix_den` (L110), `discrepancy_switch` (L436) and `normal_iff_pos` (L444).

**Proof sketch.**

1. Modulo $p$, only the indices $k=p^Jm$ with $p\nmid m$ and $m<p$ survive in $p^{sJ}b^nU_K$. Each contributes $b^n$, and there are between 1 and $p-1$ of them.
2. For $s=0$ every prefix is an integer and the tail is $O(b^{-W})$ away from insertions, so the orbit concentrates at $0$.
3. For $s\ge1$, apply the all-prefix criterion (Proposition 4.4): on blocks of length $N^{\eta/2}$ free of insertions, a fixed-support estimate (Lemma 4.3, kernel-verified, the qualitative form of Vandehey's Corollary 1.2) controls Weyl sums whenever the denominator is large and polynomially bounded.

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

## 4. Quadratic images (Theorem 7.1, Corollary 7.2)

**Statement.** Let $p\nmid b$ be an odd prime, $t=\operatorname{ord}_pb$, $d\ge3$, and $X_a=\sum_{i\ge1}p^{-av_p(i)}b^{-ti^d}$. For every finite set $S$ of positive integers and every nonconstant $P\in\mathbb Q[z_a:a\in S]$ of total degree at most two, $P((X_a))$ is normal to base $b$. In particular $\xi^2$ is normal and $(\xi,\xi^2)$ is jointly normal for $\xi=\sum_k3^{-v_3(k)}2^{-2k^3}$.

**Evidence.** Paper proof (Section 7), not formalized. External inputs: Graham–Kolesnik, *Van der Corput's Method of Exponential Sums* (1991), Lemma 2.5 and Theorem 2.2; Kuipers–Niederreiter Ch. 2 Thm 2.5 (Erdős–Turán, p. 112); the Lebesgue density theorem. Internal inputs: Proposition 4.4 (all-prefix criterion, resting on the kernel-verified short-orbit estimate) and Theorem 4.2 (kernel-verified exact denominator).

**Proof sketch.**

1. *Freezing (Lemma 7.4).* With $J=\lfloor\log_p\lfloor(n/t)^{1/d}\rfloor\rfloor$ and $u=n/(tp^{dJ})\in[1,p^d)$, the normalized prefix $p^{(a+c)J}b^{-n}R_n(X_aX_c)$ agrees modulo $p^L$ with $M_{a,c}(u)=\sum_{z^d+y^d\le u}p^{a\lambda(z)+c\lambda(y)}$ (sum over $z,y\in\{a'/p^h:p\nmid a'\}$, $\lambda$ = loss $h$) once $J\ge L(1+1/d)$, by lifting the exponent.
2. *Primitive jumps (Lemma 7.5).* In $x=(u-1)^{1/d}$, the pairs $(1,x_0)$ and $(x_0,1)$ jump at $x_0=c/p^H$, $p\nmid c$, by $A(p^{a_*H}+p^{(D-a_*)H})$, of valuation $a_*H+g$ ($p$ odd).
3. *Isolation (Lemmas 7.6, 7.7).* Competing endpoints $x=(z^d+y^d-1)^{1/d}$ of total loss $\le H$ within $\epsilon/(Hp^H)$ of $p^{-H}\mathbb Z$ number at most $C\epsilon|I|p^H+o(p^H)$: remove degenerate rows and points, split the rest into $O(\log H)$ pieces with $|f'''|\asymp\Lambda$, apply a third-derivative bound (derived from the Weyl–van der Corput inequality and the second-derivative test) and Erdős–Turán with $H^4$ frequencies, and count lattice points in the slab.
4. *Null level sets (Proposition 7.8).* With $G_H$ the union of radius-$\epsilon/(Hp^H)$ intervals about isolated centres, $|I\cap G_H|\gg\epsilon|I|/H$ and $|I\cap G_n\cap G_m|\ll|I|(\epsilon^2/(nm)+\epsilon p^{n-m}/m)$; since $\sum1/H=\infty$, Cauchy–Schwarz and the density theorem give a.e. point in infinitely many $G_H$; at such points one flank misses each level set.
5. *Transfer.* Small denominators force $u(n)$ into $E_L=\{M\equiv0\bmod p^L\}$, of upper density $\le p^d|E_L|/(p^d-1)\to0$; Proposition 4.4 gives normality.

**Review wanted.** The collision bound (3) in Lemma 7.7 (uniformity in $I$, the lattice count of the slab, the removal costs); the third-derivative regime $\lambda=lp^H\Lambda/p^{3v}$ with $2H/5\le v\le H$; the second-moment constants in Proposition 7.8; the freezing threshold. An independent AI audit (`notes/phase19/reviews/nonlinear.md`) found no error; human review is outstanding.

## 5. Infinite sums (Theorems 8.2–8.4)

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

- No rate for $D_N(\xi^2)$ and no statement for cubes or higher powers.
- Rates for $d\le s+1$ are not claimed.
- The translation identity (Theorem 2.6) is quoted from the companion manuscript *The Arithmetic of Extreme Discrepancy* and is not reproved; the addition spectrum and preserver classification are claims of that manuscript, not of this one.

**Reproduction.** See `VERIFICATION.md` (Reproduce) for the Lean and Python commands, and for the build command `wsl -d Ubuntu -- bash papers/wsl-build.sh 07-synthetic-expansions`.
