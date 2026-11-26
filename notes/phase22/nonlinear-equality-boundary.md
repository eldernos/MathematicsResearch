# The equality boundary $d=r$: depth retirement and its limits (Tracks C1–C2)

Let $b\ge2$, let $p$ be an odd prime with $p\nmid b$, put $t=\operatorname{ord}_pb$, and for $s\ge1$, $d\ge2$ let

$$
C=C(b,p,s,d)=\sum_{i\ge1}p^{-sv_p(i)}\,b^{-ti^d}.
$$

This note treats the two equality cases left open in [Phase 21 §7](../phase21/nonlinear-boundary.md): $C(b,p,s,2)^2$ (C1) and $C(2,3,1,3)^3$ (C2, Paper VII Question 1). Throughout, $D_N(x;b)$ is the extreme discrepancy of $\{b^nx\}$, $0\le n<N$, and $D^+(x;b)=\limsup_N D_N(x;b)$. $K_b=\{z: D_N(z;b)\to1\}$ is the translation kernel of [Phase 20](../phase20/coefficient-transfer.md), with the sharp translation identity $\sup_x|D_N(x+F)-D_N(x)|=1-D_N(F)$ (Lean `sharp_translation_isGreatest`). A shift $n$ is written $n=tp^{dJ}u$ with $1\le u<p^d$, as in Phase 21.

For an ordered $r$-tuple $(i_1,\dots,i_r)$ of positive integers the **level** is $\ell=v_p(i_1)+\dots+v_p(i_r)$ and the **position** is $m=i_1^d+\dots+i_r^d$. So

$$
C^r=\sum_{m\ge1}c(m)\,b^{-tm},\qquad c(m)=\sum_{\text{tuples at }m}p^{-s\ell}.
$$

## Summary

| Item | Result | Status |
|---|---|---|
| R1 Level filtration | $p^{sH}C^r=X_H+Z_H$ exactly, with $X_H$ the level-$\le H$ part (integer coefficients) and $Z_H$ the level-$>H$ part, for every $r,d\ge2$, $H\ge0$ | Proved (§1). Checked coefficientwise for $(r,d)=(2,2),(3,3)$ |
| R2 $K_b$ absorption at $d=r=2$ | $1-D_N(X_H)\le\rho_N\bigl(2\log_b\rho_N^{-1}+\log_b^+\frac{\pi p^{sH}}{t(b-1)}+3\bigr)\ll\frac{\log\log N+sH}{\sqrt{\log N}}$, uniformly in $H$ | Proved (§2), from GF-01/GF-02 and Landau |
| R3 Fixed-$H$ transfer | $C^2$ normal $\iff$ $Z_H$ normal. $D^+(p^{sH}C^2)=D^+(Z_H)$, and $1-D^+(C^2)\ge p^{-sH}(1-D^+(Z_H))$. For $H=0$ there is no multiplier: $D_N(C^2)=D_N(Z_0)+o(1)$ | Proved (§2) |
| F Frequency accounting | Level-$\ell$ terms are invisible to $e(h\,\cdot)$ iff $s\ell\le v_p(h)$. For $p\nmid h$ only level $0$ retires. For growing $H$ the transfer works only at frequencies $p^{sH}h$, or loses the factor $p^{sH}$ in the deficit | Proved (§3) |
| B Barrier after retirement (support runs) | For fixed $H$, $Z_H$ has $\asymp_H N/\sqrt{\log N}$ positions, and the proportion of shifts in support runs of length $\ge\varepsilon\log N$ is $\ll(tp^{2\lceil(H+1)/2\rceil}/\varepsilon)^{\gamma-1}(\log N)^{-(\gamma-1)/2}\to0$. The depth $\log_bq_n(Z_H)\ge s\log_bn-O_{H,L}(1)$ holds on density $\ge1-\varepsilon$. So the Phase 21 barrier applies to the support runs of $Z_H$ on density one | Proved (§4), using Hooley's moment bound (literature input) |
| B″ Fractional runs | Integral jumps do not move the rational orbit, so the rational orbit of $Z_H$ only restarts at the positions $\mathcal P_H^{\rm frac}$ where $z_H(m)\notin\mathbb Z$. For $p\equiv3\pmod4$, $p^{2k_H}\cdot\{n\in\mathcal S^+\text{ squarefree},\ (n/p)=-1\}\subseteq\mathcal P_H^{\rm frac}$, so there are $\asymp_HN/\sqrt{\log N}$ fractional jumps and the mean fractional run is $\asymp_H\sqrt{\log N}$. The density-one statement for fractional runs is **not** proved | Count proved (§4; Selberg–Delange input). Density one open |
| B′ Trade-off for growing $H$ | Support runs of $Z_{H(N)}$ of length $\ge\varepsilon\log N$ on a positive proportion of shifts force $p^{H(N)}\gg_\varepsilon\sqrt{\log N}$, hence a multiplier $p^{sH(N)}\gg(\log N)^{s/2}$ | Proved (§4) |
| M Multi-run structure | Arrival phases obey $y_{k+1}=\{b^{\ell_k}y_k+z_0(m_{k+1})\}$, and integer (level-0) jumps never move the rational orbit. Normality of $C^2$ $\iff$ equidistribution of the concatenated initial segments of the arrival phases | Proved (§5). Checked exactly for $n\le2^{16}$ |
| U Incomplete orbits | No estimate uniform in the numerator beats the trivial bound for orbit length $T\le\log_b(\varepsilon q)$. By B, density one of shifts lies in such support runs. On fractional runs this is proved only on average (B″) | Proved (§6), with the stated scope |
| C2 Cubic boundary | R1 holds. R2 at $d=3$ needs the sums of three positive cubes to have density zero. That is open, and the Deshouillers–Hennecart–Landreau model predicts a positive density (about $0.0999$). If positive density holds, the mean run length is $O(1)$ | Conditional (§8) |
| Normality, simple normality, $D^+<1$ at $d=r$ | **Open** for $C(b,p,s,2)^2$ and $C(2,3,1,3)^3$ | §10 |
| Finite data | 65 000+ certified bits of $C(2,3,1,2)^2$, $C(2,3,2,2)^2$, $C(2,3,1,3)^3$: block deviations $\le0.0021$ ($k\le4$), $D_{2^{16}}\le0.0037$ | Measurement only (§9) |

External inputs: Landau's theorem, Hooley's moment bound for gaps between sums of two squares, the Bambah–Chowla gap bound, the Selberg–Delange method (for the count in B″), and (for orientation in §7–§8) Bernays' count for binary forms, Wooley's lower bound and the Deshouillers–Hennecart–Landreau model. Everything else uses Phase 20–21 results. [Exact checks](../../scripts/phase22_nonlinear_boundary.py)

## 1. The level filtration (R1)

**Theorem R1 (retirement identity).** For every $r\ge1$, $d\ge2$, $s\ge1$ and $H\ge0$,

$$
p^{sH}C^r=X_H+Z_H,\qquad
X_H=\sum_m a_H(m)\,b^{-tm},\qquad
Z_H=\sum_m z_H(m)\,b^{-tm},
$$

where

$$
a_H(m)=\sum_{\text{tuples at }m,\ \ell\le H}p^{s(H-\ell)}\in\mathbb Z_{\ge0},\qquad
z_H(m)=\sum_{\text{tuples at }m,\ \ell>H}p^{-s(\ell-H)}.
$$

*Proof.* Expand $C^r$ as a sum over ordered tuples (absolutely convergent) and split by $\ell\le H$ and $\ell>H$. $\square$

Three exact consequences:

1. $X_H$ is supported on $\mathcal S_{r,d}=\{$sums of $r$ positive $d$-th powers$\}$, and $0\le a_H(m)\le p^{sH}\rho_{r,d}(m)$, where $\rho_{r,d}(m)$ counts ordered representations. Each lattice point $(i_1,\dots,i_r)$ owns the unit cube $\prod[i_j-1,i_j]$, which lies in $\{x\ge0:\sum x_j^d\le Y\}$. So the mass satisfies

   $$
   A_H(Y)=\sum_{m\le Y}a_H(m)\le p^{sH}\,V_{r,d}\,Y^{r/d},\qquad V_{r,d}=\frac{\Gamma(1+1/d)^r}{\Gamma(1+r/d)} .
   $$

   At $r=d$ this is linear: $V_{2,2}=\pi/4$ and $V_{3,3}=\Gamma(4/3)^3\approx0.7121$.
2. **Prefix identity.** Let $R_n(y)$ be the prefix of $y$ through $b^{-n}$, and let $q_n(y)$ be the reduced denominator of $b^nR_n(y)$, a power of $p$ for the series considered here. Then $b^nR_n(X_H)\in\mathbb Z$. Hence

   $$
   \{b^nR_n(Z_H)\}=\{p^{sH}\,b^nR_n(C^r)\},
   $$

   and the reduced denominators satisfy $q_n(Z_H)=q_n(C^r)/p^{\min(sH,\,v_p(q_n(C^r)))}$.
3. **Level $0$ needs no multiplier.** $C^r=X_0+Z_0$, where $X_0$ counts the tuples with every coordinate prime to $p$.

The filtration by **total level** is more economical than the split $C=C_{<K}+C_{\ge K}$ by individual valuations. For $r=2$ both $C_{<K}^2$ and $X_{2K-2}$ use the multiplier $p^{2s(K-1)}$. But the pairs left over number a fraction $2p^{-K}-p^{-2K}$ for the split, against $\asymp Kp^{-(2K-1)}$ for the filtration. Measured at $X=5\cdot10^5$, $p=3$: $0.2085$ against $0.1096$ ($K=2$), and $0.0711$ against $0.0158$ ($K=3$).

## 2. $K_b$ absorption at $d=r=2$ and the fixed-depth transfer (R2, R3)

Let $\mathcal S^+=\mathcal S_{2,2}$ be the set of sums of two **positive** squares and $S^+(Y)=|\mathcal S^+\cap[1,Y]|$. By Landau, $S^+(Y)\le S(Y)=(K_{\rm LR}+o(1))\,Y/\sqrt{\log Y}$, with $K_{\rm LR}=0.7642\ldots$ and $S(Y)$ the count of all sums of two squares.

**Theorem R2.** For $d=r=2$, every $H\ge0$ and every $N\ge1$, with $\rho_N=(1+S^+(\lfloor(N-1)/t\rfloor))/N$,

$$
1-D_N(X_H;b)\ \le\ \delta_N(H):=\rho_N\Bigl(2\log_b\frac1{\rho_N}+\log_b^+\frac{\pi p^{sH}}{t(b-1)}+3\Bigr).
$$

Consequently $1-D_N(X_H)\le(K_{\rm LR}/t+o(1))\,(\log_b\log N+sH\log_bp+O(1))/\sqrt{\log N}$, uniformly in $H$. In particular $X_H\in K_b$ for each fixed $H$, and $\delta_N(H(N))\to0$ whenever $H(N)=o(\sqrt{\log N})$.

*Proof.* As a series in $b^{-n}$, $X_H$ has coefficient $a_H(n/t)$ at $t\mid n$ and $0$ elsewhere. Its support count up to $N-1$ is **at most** $S^+(\lfloor(N-1)/t\rfloor)$. It can be smaller, since $a_H(m)=0$ when every representation of $m$ has level $>H$ (for example $m=18=3^2+3^2$, $H\le1$). By §1 its mass is at most $p^{sH}(\pi/4)(X/t)$. Apply [GF-02](../phase20/coefficient-transfer.md) (Theorem 1.5) with $C=\pi p^{sH}/(4t)$, so that $4C/(b-1)=\pi p^{sH}/(t(b-1))$.

This yields the bound with the true support density $\tilde\rho_N\le\rho_N$ in place of $\rho_N$. Replacing $\tilde\rho_N$ by $\rho_N$ is allowed because $f(\rho)=\rho(2\log_b\rho^{-1}+K+3)$ is increasing on $(0,1]$ for every $K\ge0$: $f'(\rho)=\frac{2}{\ln b}\ln\rho^{-1}+3-\frac{2}{\ln b}+K>0$, since $3>2/\ln2$. Landau's theorem gives $\rho_N\le(K_{\rm LR}+o(1))/(t\sqrt{\log N})$. $\square$

By sharp translation (with $x=Z_H$, $F=X_H$):

$$
|D_N(p^{sH}C^2)-D_N(Z_H)|\le\delta_N(H)\qquad(N\ge1,\ H\ge0). \tag{2.1}
$$

**Lemma W (multiplication by an integer).** For every point set $\{z_n\}\subset[0,1)$ and every integer $M\ge1$,

$$
D_N(\{Mz_n\})\le M\,D_N(\{z_n\}),\qquad 1-D_N(\{Mz_n\})\le M\bigl(1-D_N(\{z_n\})\bigr).
$$

*Proof.* The preimage of an interval $J$ under $z\mapsto Mz\bmod1$ consists of $M$ intervals of length $|J|/M$, each with error at most $D_N$. That gives the first inequality. For the second, use the concentration form $1-D_N=\inf_I(1-\mu_N(I)+|I|)$ over half-open circle arcs (Phase 20 §0). If $|I|<1/M$, the image $MI$ is an arc of length $M|I|$ with $\mu_N^{(M)}(MI)\ge\mu_N(I)$, so $1-D_N(\{Mz_n\})\le1-\mu_N(I)+M|I|\le M(1-\mu_N(I)+|I|)$. If $|I|\ge1/M$, then $1-\mu_N(I)+|I|\ge1/M\ge(1-D_N(\{Mz_n\}))/M$. $\square$

The converse of the second inequality fails. For $b=2$, $x=1/3$ has $D^+(x)=2/3$ while $3x=1$ has $D^+=1$.

**Lemma (Wall's direction $Mx$ normal $\Rightarrow$ $x$ normal).** Let $\mu$ be a weak-* limit of the empirical measures of $\{b^nx\}$ along some $N_k\to\infty$. Then $\mu$ is $T_b$-invariant and $M_*\mu=\lambda$. For a closed arc $I$ of length $<1/M$, $\mu(I)\le\mu(M^{-1}(MI))=\lambda(MI)=M|I|$. So $\mu\le M\lambda$, $\mu\ll\lambda$, and ergodicity of $\lambda$ under $T_b$ forces $\mu=\lambda$. The reverse direction is the first inequality of Lemma W. (This is Wall's theorem for integer multipliers. The argument uses a limit measure and gives no rate.)

**Corollary R3.** Let $H\ge0$ be fixed. Then:

1. $C(b,p,s,2)^2$ is normal in base $b$ if and only if $Z_H$ is normal in base $b$.
2. $D^+(p^{sH}C^2)=D^+(Z_H)$, and $1-D_N(C^2)\ge p^{-sH}\bigl(1-D_N(Z_H)-\delta_N(H)\bigr)$ for every $N$. In particular $D^+(Z_H)<1\Rightarrow D^+(C^2)<1$.
3. For $H=0$: $|D_N(C^2)-D_N(Z_0)|\le\delta_N(0)$. The discrepancy problem for $C^2$ is literally the problem for the level-$\ge1$ pairs, those with $p\mid i$ or $p\mid j$, for every odd $p\nmid b$.

*Proof.* Combine (2.1), Lemma W and Wall's direction. $\square$

The converse of item 2 for $C^2$ itself ($D^+(C^2)<1\Rightarrow D^+(Z_H)<1$) is not available, by the example after Lemma W.

## 3. Frequency accounting (F)

Write $e(x)=e^{2\pi ix}$ and $S_N(x;h)=\sum_{n<N}e(hb^nx)$. Normality is equivalent to $S_N(x;h)=o(N)$ for every fixed $h\ne0$.

**Proposition F.** At a shift $n\ge tm$, a tuple of level $\ell$ at position $m$ contributes $p^{-s\ell}b^{n-tm}$ to $b^nC^r$. This lies in $h^{-1}\mathbb Z$ for every such $n$ if and only if $s\ell\le v_p(h)$. Consequently:

1. For $p\nmid h$ only level $0$ is invisible to $e(h\,\cdot)$. The only retirement available is $|S_N(C^2;h)-S_N(Z_0;h)|\le2\pi|h|\varepsilon N+2E_N(\varepsilon)$, where $E_N(\varepsilon)$ is the far count of $X_0$ (Phase 20, Theorem 1.4).
2. For $H=H(N)$ and every $h$,

   $$
   |S_N(C^2;p^{sH}h)-S_N(Z_H;h)|\le\sum_{n<N}\min\bigl(2,\,2\pi|h|\,\|b^nX_H\|\bigr)\le2\pi|h|\varepsilon N+2E_N^{(H)}(\varepsilon),
   $$

   and $E_N^{(H)}(\varepsilon)/N\to0$ when $H=o(\sqrt{\log N})$, by Theorem 1.4 of Phase 20 and the support and mass bounds of §2.

*Proof.* $p^{-s\ell}b^{n-tm}h\in\mathbb Z$ for all $n\ge tm$ iff $p^{s\ell}\mid h$, since $p\nmid b$. Item 2 is $|e(a+c)-e(c)|=|e(a)-1|\le\min(2,2\pi\|a\|)$ applied to $p^{sH}b^nC^2=b^nX_H+b^nZ_H$. $\square$

**What growing $H$ buys.** Retirement to a depth $H(N)\to\infty$ controls $C^2$ only at the frequencies $p^{sH(N)}h$, which tend to infinity, or through Lemma W at the price $1-D_N(C^2)\ge p^{-sH(N)}(\cdots)$. The normality criterion needs every **fixed** frequency, including $h=1$, and by Proposition F a frequency prime to $p$ sees every level $\ge1$. Wall's argument is the only bridge from $p^{sH}x$ to $x$, and it is qualitative, using a limit measure for **fixed** $M$. So letting $H\to\infty$ cannot by itself reach normality or $D^+<1$. The exact deficit loss is the factor $p^{sH}$ of Lemma W.

## 4. The barrier survives retirement (B, B″, B′)

Let $\mathcal P_H=\{m:\ m=i^2+j^2$ with $i,j\ge1$ and $v_p(i)+v_p(j)>H\}$ be the positions of $Z_H$, and put $k_H=\lceil(H+1)/2\rceil$. A **support run** of $Z_H$ is a maximal shift interval $[tm,tm')$ between consecutive positions $m<m'$ of $\mathcal P_H$. Write

$$
\mathcal P_H^{\rm frac}=\{m\in\mathcal P_H:\ z_H(m)\notin\mathbb Z\}.
$$

A **fractional run** is a maximal shift interval between consecutive elements of $\mathcal P_H^{\rm frac}$. By §1 and §5, the rational orbit $\{b^nR_n(Z_H)\}$ is the orbit of a single rational along each fractional run. Support runs are finer, because an integral jump $z_H(m)\in\mathbb Z_{>0}$ still perturbs the real orbit through the tail on the $O(\log_b(z_H(m)/\varepsilon))$ shifts before $tm$, but it leaves the rational orbit unchanged. Integral jumps inside $\mathcal P_H$ do occur. For $C(2,3,1,2)^2$ up to $5\cdot10^5$ there are 67 of them for $H=0$ (the first is $m=16810$, §5) and 361 for $H=1$, of which 347 lie in $9\mathcal S^+$ (the first is $m=450=3^2+21^2=15^2+15^2$, with $z_1(450)=3\cdot\frac13=1$).

**Theorem B (support runs).** Let $d=r=2$ and $H\ge0$.

1. $p^{2k_H}\mathcal S^+\subseteq\mathcal P_H\subseteq\mathcal S^+$. Hence $|\mathcal P_H\cap[1,Y]|\asymp_HY/\sqrt{\log Y}$, and the mean support-run length of $Z_H$ up to $N$ is $\asymp_H\sqrt{\log N}$.
2. For every $\gamma\in(1,5/3)$ and $\varepsilon>0$, the proportion of shifts $n<N$ lying in support runs of $Z_H$ of length $\ge\varepsilon\log N$ is

   $$
   \ll_\gamma\Bigl(\frac{t\,p^{2k_H}}{\varepsilon}\Bigr)^{\gamma-1}(\log N)^{-(\gamma-1)/2},
   $$

   uniformly in $H$ and $\varepsilon$ for $p^{2k_H}\le N^{1/2}$. In particular the proportion tends to $0$ for each fixed $H$, and also for $H=H(N)$ whenever $p^{H(N)}=o(\sqrt{\log N})$ (since $p^{2k_H}\le p^{H+2}$).
3. Let $L\ge3$. For all shifts $n\ge t$ outside a set of upper density $\le C(\log L)^{-2}$,
   $\log_bq_n(Z_H)\ge s\log_b(n/t)-(2s+L+sH)\log_bp$.

Hence, for $\varepsilon<s/(2\ln b)$, density one of shifts $n<N$ lie in support runs of $Z_H$ of length $T<\log_b(q_n(Z_H)/2)$. On those runs the barrier lemma of Phase 21 §7.3 applies: every word of $T$ digits is the leading word of some $a/q_n$ with $p\nmid a$.

*Proof.* (1) If $m'=u^2+v^2$ with $u,v\ge1$, then $p^{2k_H}m'=(p^{k_H}u)^2+(p^{k_H}v)^2$ has a representation of level $\ge2k_H\ge H+1$. Since $S^+(Y)\ge S(Y)-\sqrt Y-1$, the lower bound follows from Landau, and the upper bound is trivial.

(2) A support run $[tm,tm')$ of length $t(m'-m)\ge G$ has $m'-m\ge G/t$. Since $p^{2k_H}\mathcal S^+\subseteq\mathcal P_H$, it lies in a gap of $Q\mathcal S^+$ ($Q=p^{2k_H}$) of length $\ge G/t$. Rescaling by $Q$, the proportion of shifts $n<N$ in such runs is at most the proportion of $[1,Y]$, $Y=N/(tQ)$, covered by gaps of $\mathcal S^+$ of length $\ge g=G/(tQ)$, plus the final partial gap.

Compare gaps of $\mathcal S^+$ with gaps of $\mathcal S$. The elements of $\mathcal S\setminus\mathcal S^+$ are perfect squares. For every $k\ge1$, $k^2<k^2+1^2<(k+1)^2$ and $k^2+1\in\mathcal S^+$. So a gap of $\mathcal S^+$ contains at most one point of $\mathcal S$ in its interior. Each gap of $\mathcal S^+$ is therefore either a gap of $\mathcal S$ or the union $g_1+g_2$ of two adjacent gaps of $\mathcal S$, and each gap of $\mathcal S$ is used once. Since $g_1+g_2\le2\max(g_1,g_2)$, the total length of gaps of $\mathcal S^+$ of length $\ge g$ is at most twice the total length of gaps of $\mathcal S$ of length $\ge g/2$. Hooley's theorem gives $\sum_{s_{n+1}\le Y}(s_{n+1}-s_n)^\gamma\ll_\gamma Y(\log Y)^{(\gamma-1)/2}$ for $0<\gamma<5/3$. With $G=\varepsilon\log N$, Markov's inequality then bounds the covered proportion by

$$
2(g/2)^{1-\gamma}Y^{-1}\sum(s_{n+1}-s_n)^\gamma\ll(tQ/\varepsilon)^{\gamma-1}(\log N)^{-(\gamma-1)/2},
$$

using $\log Y\le\log N$.

The final partial gap has shift length $O(tQY^{1/4})$ by Bambah–Chowla (gaps of $\mathcal S^+$ are at most twice those of $\mathcal S$). This is a proportion $O(Y^{-3/4})$, and it counts only when $\varepsilon\log N\ll tQY^{1/4}$. In that case $(tQ/\varepsilon)^{\gamma-1}(\log N)^{-(\gamma-1)/2}\gg Y^{-(\gamma-1)/4}(\log N)^{(\gamma-1)/2}\ge Y^{-3/4}$, because $(\gamma-1)/4<3/4$. So the bound is uniform in $\varepsilon$.

(3) By §1, $v_p(q_n(Z_H))=v_p(q_n(C^2))-sH$ when $v_p(q_n(C^2))\ge sH$; otherwise the right side of (3) is negative and the bound is trivial. Proposition D of Phase 21 (with $P(x)=x^2$, $d=r=2$, $L\ge3$) gives $v_p(q_n(C^2))\ge2sJ(n)-L$ off a set of upper density $\le C(\log L)^{-2}$. Also $p^{2J}>n/(tp^2)$ gives $2J>\log_p(n/t)-2$.

For the final claim, restrict to $n\ge\sqrt N$, where $\log_b(q_n/2)\ge(s/2)\log_bN-O_{H,L}(1)>\varepsilon\log N$. Intersect the sets of (2) and (3), and then let $L\to\infty$. $\square$

**Proposition B″ (fractional runs, $p\equiv3\pmod4$).** Let $p\equiv3\pmod4$, $H\ge0$, and let $\mathcal F_p$ be the set of squarefree $n\in\mathcal S^+$ with $(n/p)=-1$. Then $p^{2k_H}\mathcal F_p\subseteq\mathcal P_H^{\rm frac}$. More precisely, for $n\in\mathcal F_p$,

$$
z_H(p^{2k_H}n)=2^{\omega_1(n)}\,p^{-s(2k_H-H)}\notin\mathbb Z,
$$

where $\omega_1(n)$ is the number of primes $\equiv1\pmod4$ dividing $n$. Consequently $|\mathcal P_H^{\rm frac}\cap[1,Y]|\asymp_HY/\sqrt{\log Y}$, and the mean fractional-run length up to $N$ is $\asymp_H\sqrt{\log N}$.

*Proof.* Let $m=p^{2k}n$ with $k=k_H$ and $p\nmid n$. For $p\equiv3\pmod4$, $v_p(i^2+j^2)=2\min(v_p(i),v_p(j))$. So every representation $m=i^2+j^2$ has $p^k\mid i$ and $p^k\mid j$, and $i=p^ki'$, $j=p^kj'$ with $i'^2+j'^2=n$. If $p\mid i'$, then $n\equiv j'^2\pmod p$ would be a square modulo $p$. That is impossible for $(n/p)=-1$, and likewise for $j'$. So every representation of $m$ has level exactly $2k>H$.

Since $n>1$ is squarefree and lies in $\mathcal S$, it has no prime factor $\equiv3\pmod4$ and is not a square. So $n$ has no representation with a zero coordinate, and its number of ordered positive representations is $r_2(n)/4=\sum_{d\mid n}\chi_{-4}(d)=2^{\omega_1(n)}$, which is prime to $p$. Hence $z_H(m)=2^{\omega_1(n)}p^{-s(2k-H)}$ with $2k-H\ge1$.

For the count, the multiplicative function $g=\mu^2\mathbf 1_{\mathcal S}$ has $\sum_{n\le Y}g(n)\sim c\,Y/\sqrt{\log Y}$, and its twist by the Legendre symbol $(\cdot/p)$ contributes $o(Y/\sqrt{\log Y})$. Both follow from the Selberg–Delange method (Tenenbaum, *Introduction to analytic and probabilistic number theory*, II.5; literature input). The Dirichlet series of $g$ behaves like $\zeta(s)^{1/2}$ times a function holomorphic and nonzero near $s=1$, and the twist like $(L(s,\chi_p)L(s,\chi_p\chi_{-4}))^{1/2}$ times such a function. So $|\mathcal F_p\cap[1,Y]|\sim\frac c2Y/\sqrt{\log Y}$. The upper bound is $\mathcal P_H^{\rm frac}\subseteq\mathcal S^+$. $\square$

**What is not proved for fractional runs.** The density-one statement of Theorem B(2) for fractional runs would follow from a Hooley-type moment bound $\sum(f_{n+1}-f_n)^\gamma\ll Y(\log Y)^{(\gamma-1)/2}$, for some $\gamma>1$, for the consecutive elements $f_n$ of $\mathcal F_p$ (or of any subset of $\mathcal P_H^{\rm frac}$ of order $Y/\sqrt{\log Y}$). Hooley's theorem concerns $\mathcal S$ itself. Deleting a subset of positive relative density, here the integral jumps or the non-squarefree and residue elements, is not controlled by that theorem without an additional arithmetic argument against clustering. A short-interval result for sums of two squares restricted by squarefreeness and a residue condition modulo $p$ would suffice. It is not established here. For $p\equiv1\pmod4$ even the lower bound of Proposition B″ is not established here, because $p^{2k}n$ may have representations of smaller valuation. Finite measurement: up to $5\cdot10^5$, $|\mathcal F_3|=31909$, and the inclusion $9^{k_H}\mathcal F_3\subseteq\mathcal P_H^{\rm frac}$ holds for $H\le3$.

**Corollary B′ (trade-off).** Let $H=H(N)$. If $p^{H(N)}/\sqrt{\log N}\to0$ along a sequence of $N$, a proportion $1-o(1)$ of the shifts $n<N$ lie in support runs of $Z_{H(N)}$ shorter than $\varepsilon\log N$. So a positive proportion of shifts in support runs of length $\ge\varepsilon\log N$ requires $p^{H(N)}\ge c\sqrt{\log N}$, and then the transfer constant of Corollary R3 is $p^{sH(N)}\ge c^s(\log N)^{s/2}$. In the opposite regime $p^{H}\gg H\log N$, the level count gives at most $(H+2)\frac\pi4p^{-(H+1)}(N/t)$ positions, so the runs are long, but the multiplier is then $\gg(H\log N)^s\gg(\log N)^s$.

**Pair counts versus distinct positions.** The split $C=C_{<K}+C_{\ge K}$ leaves $2C_{<K}C_{\ge K}+C_{\ge K}^2$, which has $O(N/p^K)$ **pairs**. The run length is governed by **distinct positions**. These contain $p^{2K}\mathcal S^+$ (both coordinates divisible by $p^K$), so by the argument of Theorem B(1) they number $\asymp_KN/\sqrt{\log N}$ for every fixed $K$. Hence fixed-depth retirement, by $\max(v_p(i),v_p(j))<K$ or by level $\le H$, multiplies the mean run length by at most a factor bounded in $N$. Since $|\mathcal P_H\cap[1,Y]|\ge S^+(Y/Q)$, the ratio of mean gaps to those of $\mathcal S^+$ is at most $(1+o(1))Q$, with $Q=p^{2K}$ or $p^{2k_H}$ respectively. The mean run length therefore stays $\asymp_K\sqrt{\log N}$, and by Theorem B(2) almost every shift lies in a support run shorter than $\varepsilon\log N$.

Reaching runs $\gg\log N$ requires a growing depth. For example $K=2\log_p\log N$, where the pair count alone gives $O(N/(\log N)^2)$ positions, lies in the second regime of Corollary B′, with multiplier $(\log N)^{2s}$.

**Finite measurements** ($X=5\cdot10^5$, $p=3$, $t=2$, $s=1$). At shifts $n\le tX$ the top shell is $3^{2J}=3^{10}\le X$, and $q_n(Z_H)=q_n(C^2)/3^H$. So the column threshold is the depth scale $\lambda_H=\log_2(3^{10-H}/2)$: $14.85$, $13.26$, $11.68$, $10.09$ for $H=0,1,2,3$, and $14.85$ for $C^2$.

| $H$ | pairs of level $>H$ | $\lvert\mathcal P_H\rvert$ | mean gap | ratio to $\mathcal S^+$ | shifts in support runs $\ge\lambda_H$ | integral jumps in $\mathcal P_H$ | $\lvert\mathcal P_H^{\rm frac}\rvert$ | shifts in fractional runs $\ge\lambda_H$ |
|---|---|---|---|---|---|---|---|---|
| — ($C^2$) | 1 | 111065 | 4.50 | 1 | 0.395 | — | — | — |
| 0 | 0.5547 | 62264 | 8.03 | 1.78 | 0.751 | 67 | 62197 | 0.752 |
| 1 | 0.2579 | 39103 | 12.79 | 2.84 | 0.918 | 361 | 38742 | 0.919 |
| 2 | 0.1096 | 17049 | 29.33 | 6.51 | 0.988 | 4 | 17045 | 0.988 |
| 3 | 0.0435 | 7636 | 65.48 | 14.54 | 0.998 | 47 | 7589 | 0.998 |

At this range $Z_1,Z_2,Z_3$ already look sparse. Theorem B(2) says this is a finite-range effect for support runs: the bound becomes small only once $\sqrt{\log N}\gg tp^{2k_H}/\varepsilon$ (for $H=3$, $p^{2k_H}=81$, that is $\log N\gg10^4$). The barrier is asymptotic, and no finite computation can display it for $H\ge1$. The integral jumps are rare at this range, and the two coverage columns differ by at most $0.001$.

## 5. Multi-run structure (M)

Let $m_1<m_2<\cdots$ enumerate $\mathcal S^+$, let $\ell_k=t(m_{k+1}-m_k)$, and define the **arrival phase** $y_k=\{b^{tm_k}R_{tm_k}(C^2)\}$. Write $z_0(m)=\sum_{\text{pairs at }m,\ \ell\ge1}p^{-s\ell}$.

**Proposition M.**

1. For $tm_k\le n<tm_{k+1}$: $\{b^nR_n(C^2)\}=\{b^{\,n-tm_k}y_k\}$ and $\{b^nC^2\}=\{b^{\,n-tm_k}y_k+\tau_n\}$, where $\tau_n=b^n(C^2-R_n)\ge0$.
2. $y_{k+1}=\{b^{\ell_k}y_k+z_0(m_{k+1})\}$. The level-0 count $c(m)-z_0(m)\in\mathbb Z$ never enters, so $y_k=\{b^{tm_k}R_{tm_k}(Z_0)\}$. Integer jumps leave the rational orbit unchanged, and only the jumps with $z_0(m)\notin\mathbb Z$ move it.
3. Let $G_N(\varepsilon)=\{n<N:\tau_n\ge\varepsilon\}$. Then $|G_N(\varepsilon)|=o(N)$ for each $\varepsilon>0$ (Phase 21 §7.3 item 3). Let $w=(w_j)_{j\ge0}$ be the concatenation of the segments $(\{b^jy_k\})_{0\le j<\ell_k}$, $k=1,2,\dots$, so that $w_j=\{b^{\,tm_1+j}R_{tm_1+j}(C^2)\}$ with $tm_1=2t$. Then

   $$
   \bigl|D_N(C^2)-D_N(w_0,\dots,w_{N-1})\bigr|\le2\varepsilon+\frac{|G_N(\varepsilon)|}{N}+\frac{4t}{N}.
   $$

   Hence $C^2$ is normal if and only if $w$ is uniformly distributed. Likewise $D^+(C^2)<1$ if and only if $\limsup_ND_N(w_0,\dots,w_{N-1})<1$.

*Proof.* (1) and (2) are the definition of the prefix and the integrality of level-0 contributions.

For (3), first compare $z_n=\{b^nC^2\}$ with $z'_n=\{b^nR_n(C^2)\}$ for $n<N$. These satisfy $\|z_n-z'_n\|\le\varepsilon$ except for the $G=|G_N(\varepsilon)|$ indices with $\tau_n\ge\varepsilon$. For a circle arc $I$ let $I^{+\varepsilon}$ be its $\varepsilon$-neighbourhood, of length at most $|I|+2\varepsilon$. Then $\mu_N(z;I)\le\mu_N(z';I^{+\varepsilon})+G/N$, so

$$
\mu_N(z;I)-|I|\le\bigl(\mu_N(z';I^{+\varepsilon})-|I^{+\varepsilon}|\bigr)+2\varepsilon+G/N\le D_N(z')+2\varepsilon+G/N .
$$

Applying this to the complementary arc and exchanging $z$ and $z'$ gives $|D_N(z)-D_N(z')|\le2\varepsilon+G/N$. Phase 21 proves $\tau_n\to0$ in density for squares: the head $\sum_{u\le H}$ vanishes off the $o(N)$ shadows of the Landau-sparse support, and the far tail has mean $\ll b^{-H}$.

Finally $z'_n=0$ for $n<2t$ and $z'_n=w_{n-2t}$ for $n\ge2t$. So $(z'_n)_{n<N}$ and $(w_j)_{j<N}$ differ by removing $2t$ points and adding $2t$ points, which changes the discrepancy by at most $4t/N$. $\square$

The script verifies item 2 exactly for $n\le2^{16}$ ($C(2,3,1,2)^2$): the rational orbit of $C^2$ equals the rational orbit of the prefix of $Z_0$ at every shift. Among the 8268 positions $m\le2^{15}$, the jump $c(m)$ is integral at $44.1\%$, has denominator $3$ at $22.7\%$, denominator $9$ at $19.4\%$, and denominator $\ge27$ at $13.9\%$. A jump can be integral even when every pair at $m$ has level $\ge1$, because the positive terms can sum to an integer. For example $m=16810$ has exactly six ordered representations, $(13,129),(41,123),(67,111)$ and their reversals, all of level $1$, so $z_0(16810)=6\cdot\frac13=2$. Level-1 pairs always come in reversed couples ($v_p(i)\ne v_p(j)$ forces $i\ne j$), so their number at any $m$ is even. An odd count of equal terms needs a diagonal pair, as at $m=450=3^2+21^2=15^2+15^2$, where $z_1(450)=3\cdot\frac13=1$.

**What a fractional jump forces.** Suppose the orbit stays within $\varepsilon$ of $0$ before $tm$, and $z_0(m)\not\equiv0$. Then after the jump it follows the orbit of $z_0(m)+O(b\varepsilon)$ for about $\log_b(1/\varepsilon)$ steps, unless the preceding phase was already near $-z_0(m)$. Conversely, by the barrier lemma there are admissible phases that stay within $\varepsilon$ of $0$ except on $O(\log_b(1/\varepsilon)+\log_bp^{s\ell})$ shifts around the insertion. So any argument that uses only the jump values and the gaps, treating the phases as unknown, certifies at most $O_\varepsilon(1)$ shifts per insertion outside an $\varepsilon$-arc. With $\asymp N/\sqrt{\log N}$ insertions that is $o(N)$ for each fixed $\varepsilon$. Such an argument cannot give $D^+<1$. It does not rule out concentration at scale $\varepsilon_N\to0$ slower than $\exp(-c\sqrt{\log N})$.

## 6. Incomplete-orbit estimates (U)

**Lemma U.** Let $q=p^e$, $0<\varepsilon<1$, and let $T\ge1$ be an integer with $b^T\le\varepsilon q$. The numerator $a=1$ is admissible, and

$$
\Bigl|\sum_{j=0}^{T-1}e(hb^j/q)-T\Bigr|\le2\pi|h|\sum_{j=0}^{T-1}\frac{b^j}{q}=2\pi|h|\,\frac{b^T-1}{(b-1)q}<\frac{2\pi|h|\varepsilon}{b-1}.
$$

So $|\sum_{j<T}e(hb^j/q)|\ge T-2\pi|h|\varepsilon/(b-1)$, and no bound for $\sup_{p\nmid a}|\sum_{j<T}e(hab^j/q)|$ beats the trivial one by more than $O_h(1)$ at such $T$. $\square$

**Scope of the conclusion.** By Theorem B, at every fixed depth $H$ density one of shifts lie in **support runs** of $Z_H$ shorter than $\varepsilon\log N<\log_b(\varepsilon'q_n)$. On each support run the rational orbit is the orbit of one rational. So any argument that applies a short-orbit estimate uniform in the numerator on support runs is applied below its range on density one of shifts, **whatever its threshold**. This includes Korobov's $p$-adic method for prime-power moduli, and no comparison of exponents ($\exp(c(\log q)^{2/3})$ or otherwise) is needed, because the uniform statement is false below $\log_b(\varepsilon q)$.

An argument working with the rational orbit alone may instead merge support runs across integral jumps, that is, use **fractional runs**. For those, Proposition B″ proves only that their number is $\asymp N/\sqrt{\log N}$ (for $p\equiv3\pmod4$), so the mean fractional run is $\asymp\sqrt{\log N}\ll\log q_n$. The density-one statement for fractional runs is open (§4). Finite data: at $X=5\cdot10^5$ the two kinds of runs give the same coverage to within $0.001$.

In both readings, a proof would have to use the specific arrival phases $y_k$ of §5, that is, numerator information at resolution $b^{-\ell_k}$. This is the obstruction identified in Phase 21. It persists after retirement at every fixed depth: unconditionally on support runs, and on fractional runs on average.

## 7. Variants at $d=2$

| Variant | Effect |
|---|---|
| Other $s\ge1$ | Positions do not depend on $s$; R2, R3, B and U hold verbatim. $C(2,3,2,2)^2$ is measured in §9 |
| Other odd $p\nmid b$ | R1–R3, B and U hold for every such $p$. The rule $v_p(i^2+j^2)=2\min(v_p(i),v_p(j))$ (checked for $i,j<400$ at $p=3$) holds exactly when $p\equiv3\pmod4$. It is used for $p\mid m\Rightarrow$ level $\ge2$ and in Proposition B″. Even for $p\equiv3\pmod4$, $p\nmid m$ does not force the jump to be integral: $(pa)^2+j^2$ with $p\nmid j$ has level $\ge1$ and $p\nmid m$ |
| Other positive definite binary forms | Only diagonal forms $ai^2+cj^2$ arise as products of two one-variable series of the type $C$; a general form $Q(i,j)$ gives a bivariate series. Bernays' count (literature input, not checked) gives $\asymp X/\sqrt{\log X}$ values, hence the same **mean-gap** barrier ($\asymp\sqrt{\log N}$). The full density-one barrier would also need a Hooley-type gap-moment bound for the values $Q(i,j)$, $i,j\ge1$, and a denominator-depth result for the corresponding series. Neither is checked here |
| Sparse index sets $i\in A$, $\lvert A\cap[1,x]\rvert\le x^{1-\eta}$ | Insertions become $O(N^{1-\eta})$, so the Phase 18 criterion's sparsity hypothesis holds. This leaves the equality boundary. Normality would still need null level sets of the corresponding mass, which is not checked |
| Mixed products $C(b,p,s,2)\,C(b,p,s',3)$ | Positions $i^2+j^3$ number $O(N^{5/6})$: again off the boundary. The mixed mass and its level sets are not checked |

None of these variants proves $D^+<1$ for a number that is genuinely on the boundary $d=r$.

## 8. The cubic boundary $C(2,3,1,3)^3$ (C2)

Here $b=2$, $p=3$, $t=2$, $s=1$, $r=d=3$.

1. **Identity.** R1 holds: $3^HC^3=X_H+Z_H$, checked coefficientwise for $m\le30000$, $H\le2$. The mass bound is $A_H(Y)\le3^H\Gamma(4/3)^3Y$ (20106 ordered triples up to $3\cdot10^4$, against the bound 21362).
2. **Absorption is conditional.** GF-02 needs the support $\mathcal S_{3,3}$ (sums of three positive cubes) to have density zero. Known: $|\mathcal S_{3,3}\cap[1,Y]|\gg Y^{0.91709477}$ (Wooley, *Sums of three cubes II*, 2015), $\gg Y^{1-\varepsilon}$ conditionally on Riemann hypotheses for certain Hasse–Weil $L$-functions (Hooley 1986, Heath-Brown 1998, as quoted by Wooley), and $\le(\Gamma(4/3)^3/6+o(1))Y\approx0.1187Y$. Whether the density is positive is open. The model of Deshouillers, Hennecart and Landreau (2006) predicts density about $0.0999$. Literature inputs, not checked here. Measured: $0.1043Y$ at $Y=10^6$, with dyadic-window densities $0.1062,0.1047,0.1044,0.1032$ on $(Y,2Y]$, $Y=62500,\dots,5\cdot10^5$.

   **What positive density would force.** The ordered triples with some coordinate divisible by $3$ form a proportion $1-(2/3)^3=19/27$ of all triples, so they cover at most $\frac{19}{27}(\Gamma(4/3)^3/6+o(1))Y\approx0.0835Y$ positions. If $\mathcal S_{3,3}$ has lower density $\delta>0.0835$ (as under the Deshouillers–Hennecart–Landreau prediction), then $\operatorname{supp}X_0$ has positive lower density. For an arbitrary $\delta>0$, the triples of level $>H$ cover density $\to0$ as $H\to\infty$, so $\operatorname{supp}X_H$ has positive lower density for all large $H$. In either case Phase 20 transfer says nothing, and $X_H\in K_b$ becomes a digit question of its own. Positive density alone does not force $\operatorname{supp}X_0$ to have positive density when $\delta\le0.0835$.
3. **Positions after retirement.** $27^{k}\mathcal S_{3,3}\subseteq\mathcal P^{(3)}_H\subseteq\mathcal S_{3,3}$ with $k=\lceil(H+1)/3\rceil$, by the argument of Theorem B(1). So $Z_H$ has positive upper (lower) density of positions iff $\mathcal S_{3,3}$ does. Positive upper density gives mean run length $O_H(1)$ along a subsequence of $N$, and positive lower density gives it for all large $N$. Measured mean gaps at $5\cdot10^5$: $9.50$ ($C^3$), then $13.49$, $22.62$, $46.38$ for $Z_0,Z_1,Z_2$.
4. **Depth.** Phase 21 Proposition D gives $v_3(q_n)\ge3J(n)-L$ off upper density $\le C(\log L)^{-3/2}$. So $\log_2q_n\asymp\log N$, while the mean run length is $O(1)$ conditionally on positive lower density (measured mean $9.5$ positions, $19$ shifts). Unconditionally, consecutive positions are on average at most $O(N^{0.083})$ apart, by Wooley's bound.
5. **No analogue of the $p\equiv3\pmod4$ rule.** Cubes are $0,\pm1\bmod9$, so $m\not\equiv\pm4\pmod9$ (checked), but level $0$ does not force $3\nmid m$ ($1+1+1=3$). The level of a position is not read off from $v_3(m)$.

| | $d=r=2$ | $d=r=3$ |
|---|---|---|
| Distinct positions up to $Y$ | $\asymp Y/\sqrt{\log Y}$ (Landau) | between $Y^{0.917}$ and $0.1187Y$; density open |
| $X_H\in K_b$ | **Proved** for every $H$, rate $\ll(\log\log N+H)/\sqrt{\log N}$ | Conditional on density zero (hypothesis expected false) |
| Mean run of $Z_H$ | $\asymp_H\sqrt{\log N}$; support runs below $\varepsilon\log N$ on density one (Hooley); fractional runs $\asymp_H\sqrt{\log N}$ on average ($p\equiv3\bmod4$) | $O_H(1)$ if positive lower density |
| $\log_bq_n$ | $\asymp\log N$ on density $1-\varepsilon$ | $\asymp\log N$ on density $1-\varepsilon$ |
| Retirement gain | Bounded factor at fixed $H$ | Bounded factor at fixed $H$, and possibly no absorption at all |

The two boundaries differ in kind. At $d=2$ the integer part is provably negligible and the obstruction is the short runs of $Z_H$. At $d=3$ even the integer part is not known to be negligible.

## 9. Finite measurements (evidence only)

All digits are certified by exact interval arithmetic ($2^{Q}C$ bracketed by integers, then raised to the $r$-th power). The table covers the first $2^{16}$ shifts.

| Number | ones | transitions | max block dev. $k\le4$ | $D_N$, $N=2^{10},2^{12},2^{14},2^{16}$ |
|---|---|---|---|---|
| $C(2,3,1,2)^2$ | 0.5017 | 0.5000 | 0.0021 | 0.0453, 0.0144, 0.0103, 0.0037 |
| $C(2,3,2,2)^2$ | 0.5009 | 0.5000 | 0.0020 | 0.0531, 0.0122, 0.0073, 0.0025 |
| $C(2,3,1,3)^3$ | 0.4990 | 0.4998 | 0.0020 | 0.0833, 0.0285, 0.0090, 0.0035 |

For $C(2,3,1,2)^2$ at $N=2^{16}$: $D_N(X_0)=0.761$ and $D_N(X_1)=0.565$, against $D_N(Z_0)=0.0044$ and $D_N(3C^2)=0.0049$, $D_N(Z_1)=0.0041$. The inequality (2.1) holds on the actual orbits, but the $K_b$-ness of $X_H$ is invisible at this $N$: the mean of $\|2^nX_1\|$ is $0.117$, and $\delta_N(H)>1$ for $N\le2^{16}$. The Weyl transfer of Proposition F gives $|S_N(C^2;3)-S_N(Z_1;1)|/N=0.0011$, far below its bound $0.73$. The real tail lies in $[1/8,7/8]$ on $25.4\%$ of shifts. These numbers are consistent with normality and prove nothing asymptotic.

## 10. Status

**Proved.**

- The level filtration R1 for all $r,d$.
- $K_b$ absorption of every finite-depth integer part at $d=r=2$, with an explicit rate uniform in the depth (R2).
- The fixed-depth equivalences for normality and the one-sided $D^+$ transfer (R3, Lemma W, Wall).
- The frequency accounting F.
- The barrier after retirement B on support runs, and the trade-off B′ (Hooley input).
- The count of fractional jumps B″ for $p\equiv3\pmod4$ (Selberg–Delange input).
- The exact multi-run reformulation M.
- The impossibility of uniform short-orbit estimates U, on density one of support runs and on average for fractional runs.

**Conditional.** $K_b$ absorption at $d=r=3$, assuming sums of three positive cubes have density zero.

**Not established.** The density-one short-run statement for fractional runs, which needs a gap-moment bound for squarefree sums of two squares in a residue class modulo $p$, and anything about fractional runs for $p\equiv1\pmod4$.

**Finite.** All tables in §4, §5, §8 and §9.

**Open.** Normality, simple normality, and $D^+<1$ for $C(b,p,s,2)^2$ and $C(2,3,1,3)^3$. Even $C^2\notin K_b$ is not proved.

**What is missing.** By R3 and M, the precise missing input at $d=2$ is equidistribution, at resolution $b^{-\ell_k}$, of the arrival phases of $Z_0$ (equivalently of $Z_H$ for any fixed $H$). These phases are rationals of denominator $\asymp N^{s}$ driven by the affine recursion $y_{k+1}=\{b^{\ell_k}y_k+z_0(m_{k+1})\}$ with support runs $\ell_k\ll\varepsilon\log N$ on density one, and fractional runs of mean $\asymp\sqrt{\log N}$. Retirement changes the kicks, not the scale of the runs. Uniform orbit estimates cannot supply this input (U), and growing the depth trades it for a multiplier at least $(\log N)^{s/2}$ (B′).

## 11. Exact checks

`python -B scripts/phase22_nonlinear_boundary.py` runs in about 5 seconds and exits 0.

- **R.** The coefficientwise identity $p^{sH}c(m)=a_H(m)+z_H(m)$ against an independent convolution (Fractions) for $C(2,3,1,2)^2$, $C(2,3,2,2)^2$ ($m\le2\cdot10^4$, $H\le3$) and $C(2,3,1,3)^3$ ($m\le3\cdot10^4$, $H\le2$). It also checks integrality and support of $X_H$, the mass bound at every multiple of 1000, the prefix identity $\{b^nR_n(Z_H)\}=\{3^Hb^nR_n(C^2)\}$ for $n\le12000$, and the valuation rule for $p=3$.
- **G.** Pair and position counts by level up to $5\cdot10^5$, and the exact fractional parts of $z_H(m)$ for $H\le3$. It checks the inclusions $9^{k_H}\mathcal S^+\subseteq\mathcal P_H$ and $9^{k_H}\mathcal F_3\subseteq\mathcal P_H^{\rm frac}$ (squarefree, $\equiv2\bmod3$), the counts of integral jumps (67 for $H=0$; 361 for $H=1$, of which 347 in $9\mathcal S^+$), and the examples $m=16810$ (six level-1 pairs) and $m=450$. It also reports the split by $\max(v_p(i),v_p(j))$, the coverage by support and fractional runs at the depth threshold $\lambda_H=\log_2(3^{10-H}/2)$, and sums of three positive cubes up to $10^6$ (with the mod-9 check). Gap lengths partition $[1,X]$ exactly.
- **D.** Certified digits, frequencies, transitions, $D_N$; (2.1) on actual orbits; the Weyl transfer at frequency 3; exact equality of the rational orbits of $C^2$ and $Z_0$ for $n\le2^{16}$; jump classes. The far tail of $X_H$ is bounded explicitly by $3^H(\lfloor\sqrt{Q/2+1}\rfloor+1)$ units of $2^{-Q}$, from $a_H(m)\le3^H\sqrt m$.
- **W.** Lemma W on 1200 exact point sets and on the orbits $\{2^n/3^e\}$, and Lemma U in its geometric form (exact $\sum_{j<T}2^j/q<\varepsilon$ for the largest $T$ with $2^T\le q/64$) for $q=3^{20},3^{40},3^{80}$.

[Checker](../../scripts/phase22_nonlinear_boundary.py)
