# The nonlinear normality boundary (Tracks C1–C2)

Let $b\ge2$, let $p$ be an odd prime with $p\nmid b$, put $t=\operatorname{ord}_pb$ and $a_0=v_p(b^t-1)$, and for $s\ge1$, $d\ge2$ let

$$
 C=C(b,p,s,d)=\sum_{i\ge1}p^{-sv_p(i)}\,b^{-ti^d},\qquad
 M_r(u)=\sum_{\text{ordered } z:\ S(z)\le u}p^{\,s(h_1+\cdots+h_r)}\in\mathbb Z_p\quad(1\le u<p^d),
$$

with coordinates $z=a/p^h\in(0,p)$, $p\nmid a$, loss $h$, and $S(z)=\sum z_i^d$, exactly as in [GF-11](../phase20/cubic-power-schedule.md). A shift is written $n=tp^{dJ}u$ with $u\in[1,p^d)$.

## Summary

| Item | Result | Evidence |
|---|---|---|
| C1.1 Audit of GF-11 | The seven pressure points hold. No gap found. Two features are qualitative only: the coincidence error $p^{-(\log H)^2/3}$, and the dependence of $H_0(I)$ on the interval $I$, which is genuine | Paper audit, §1 |
| C1.2 Uniform chain | **False as proposed.** For $p=3$, $d=4$, $r=3$ there are intervals of length $\rho_H\asymp H^{-8/3}$ with no isolated centre. At $H=4000$ such an interval is longer than $3^{-\sigma_3H/3}$ | Proof, with the net certified exactly at $H=4000$ (§2) |
| C1.2 Effective small ball | **Theorem Q.** $\lvert\{u:M_r(u)\equiv w\bmod p^L\}\rvert\ll(\log L)^{-d/(d-1)}$ for every $r\ge2$, $d\ge2$, $w$ | Paper proof (§3–4) |
| C1.2 Effective rate | **Corollary Q1.** $D_N(P(C))\ll_P(\log\log N)^{-d/(d-1)}$ whenever $\deg P=r\ge2$ and $d>r(s+1)$ | Paper proof (§5) |
| C1.2 Conditional rate | $L^{-\eta}$ and $(\log N)^{-\eta}$ under a local count hypothesis (LC) | Conditional (§5) |
| C1.3 Lean core | Kernel-verified `NormalityChecker/PowerSumPeeling.lean` covers the divisor bound, $\Phi_q$ degree/leading coefficient/nonvanishing, dominant-loss peeling, and truncated-mass jump (`truncMass_sub`, `truncMass_jump_of_isolated`); support homogeneity and `iteratedDeriv_rpow_root` remain blueprint statements | Lean 4.36.0 + `leanchecker` (§6) |
| C2 Full depth at $d\le r$ | **Proposition D.** Level sets of $M_r$ are null for all $d\ge2$. At $d=r$ the $p$-depth defect $rsJ(n)-v_p(q_n)$ is tight in density (upper density $\le C_P(\log L)^{-d/(d-1)}$ for $L\ge3$), so $v_p(q_n)\ge rsJ(n)-\omega(n)$ on density one for every $\omega(n)\to\infty$ | Paper proof (§7.2). Numerics: depth $\ge rJ-1$ on 100% of sampled shifts in $[2\cdot10^5,4\cdot10^5]$ |
| C2 Normality at $d=r$ | **Open.** The runs are too short for their denominators, and an exact lemma shows that denominator data cannot determine the digits. No bound $D^+<1$ is proved | Proof of the barrier (§7) |

The only new external inputs are Landau's theorem on sums of two squares and Wooley's lower bound for sums of three cubes, both used only for orientation in §7. Everything else uses the inputs of GF-11: the Titchmarsh 5.13 derivative test, Erdős–Turán, the divisor bound, Lebesgue density, the Phase 18–19 freezing and prefix estimates, and the Phase 19 exact grid theorem. [Exact checks](../../scripts/phase21_nonlinear.py)

## 1. Audit of GF-11 (C1.1)

The proof in [cubic-power-schedule.md](../phase20/cubic-power-schedule.md) was rederived from Section 4 onward. Its three earlier repairs ([review](../phase20/reviews/track-c-review.md)) are in place.

| Pressure point | Verdict |
|---|---|
| (i) Exact coincidences $B=0$ | Sound. Rational separation forces $x=z$, then $v'=v$ and $k'=k+(H'-H)$. The valuation step gives a unique remaining coordinate of loss exactly $h_j$: none of loss $>h_j$ (valuation too negative) and not all below $h_j$ (valuation too large), because $k'_j<2h_j$. The count $\#\{(a,c):a^d-c^d=M\}\le\tau(\lvert M\rvert)$ uses $e=a-c\mid M$ and strict monotonicity of $(c+e)^d-c^d$ for $d\ge2$ |
| (ii) Small primes $p\le r$ | Sound. Precision $sH+e_r+1$, $e_r=v_p(r!)$. Tuples above level $H+\lfloor e_r/s\rfloor$ vanish since $e_r+1\le s(\lfloor e_r/s\rfloor+1)$. The $r!$ ordered tuples at a centre are distinct because the losses are distinct |
| (iii) Dominant peeling | Sound. $h_j\ge2k_{j-1}+1$ gives $k_j\le\frac32h_j-\frac12$, so the per-step saving is $p^{-(1/2-\epsilon'd)h_j}$ |
| (iv) Derivative test | Sound. The theorem quoted is Titchmarsh 5.13 (constants depending on $q$). The dyadic pieces have boundedly many components: after raising to the $d$-th power, $f^{(q)}=D$ becomes a polynomial equation in $x$ of degree $O(qd^2)$ that does not vanish identically (the two sides have different degrees) |
| (v) Uniformity over loss vectors | Sound. Every $(\alpha,\beta)$ with $\beta/r\le\alpha\le\beta\le1$ falls in case 2 ($\alpha\ge1/r$) or case 3 ($\beta\le r\alpha<1$). The $q$-windows tile $[1/r,1]$, and the margin $\sigma_r=1/(r(2^{r+1}-2))$ is attained at $(\alpha,\beta)=(1/r,1)$ |
| (vi) Null level sets | Sound. Reverse Fatou, then density $\le1-c$ of the complement at every point, then Lebesgue density. Flanks of radius $\delta_H$ carry distinct residues, so a level set misses a quarter of the interval of radius $2\delta_H$ about any point of $G_H$ |
| (vii) All-prefix transfer | Sound. The three hypotheses of the Phase 18 criterion hold for $d\ge r+1$. The measures of the failed cells decrease to $\lvert\{M_r=0\}\rvert$ by continuity from above |

**Features that are qualitative only.** Neither is an error, but both matter in §2–§4.

1. The coincidence error is $O(H^{O(r)}p^{H-(\log H)^2/3})$. It is $o(p^H)$, but only by a quasi-polynomial factor. A rate needs $h_2\ge\lambda H$, which keeps $\gg(\kappa H)^{r-1}$ loss vectors whenever $\lambda\le3\kappa/6^{r-1}$ (the box $h_j\in[a_j,2a_j]$, $a_j=\kappa H6^{j-1}/(2\cdot6^{r-1})$).
2. Section 6 obtains $|I\cap G_H|\ge c|I|$ only for $H\ge H_0(I)$. The proof shows why: the lattice error $O(H^{r-2}p^H)$ in the main term is compared with $|I|H^{r-1}p^H$. This dependence is real. Section 2 exhibits intervals of length $\asymp H^{-(r-1)d/(d-1)}$ with no isolated centre at all.

**Where $d\ge r+1$ enters.** Isolation uses it in only one place: the upper bound $\lvert f_B^{(q)}\rvert\le C$, which needs $q\le d$. The transfer needs it separately, because it requires sparse insertions. The upper bound can be replaced by the cap $x\ge\eta=p^{-2\kappa H}$, which is already imposed. For $q>d$ this gives $\lvert f_B^{(q)}\rvert\ll\eta^{d-q}=p^{2\kappa(q-d)H}$, while the lower bound $x^{d-q}\ge p^{d-q}$ gives $D_{\min}\gg p^{-\gamma H}$ with $\gamma=c+2\kappa d(q-2)$ (in place of GF-11's $c+2\kappa(d(q-1)-q)$). So $E_1$ gains $2\kappa(q-d)H/(2K_q-2)$ and $E_2$ uses $\gamma=c+2\kappa d(q-2)$, both absorbed for small $\kappa$. Also, for $d<r+1$ where $\theta=(2r)^{-1/d}$ can be small, require $h_1\ge h_{\min}(p,r,d):=\lceil\log_p(6/\theta)\rceil$ so every anchor coordinate has at least $(1-1/p)\theta p^{h_i}-2\ge(\theta/3)p^{h_i}$ admissible numerators (replacing $(2/9)p^{h_i}$). The script confirms positive margins for $(r,d)=(3,3),(2,2),(4,3),(3,2)$. For $r=2$, the order $q=3$ gives the exact margin $1/12$: $E_1/H\le\frac16+\frac34\beta$ and $E_2/H=\beta-\frac16$ on $\beta/2\le\alpha\le\beta$. Hence:

> **Isolation for all $d\ge2$.** For every $r\ge2$ and $d\ge2$ the anchor construction of GF-11 (with $h_1\ge h_{\min}(p,r,d)$) isolates a positive proportion of level-$H$ centres for $H\ge H_0(I)$. For $r=2$ the anchor is a single coordinate of loss $h_1\in[h_{\min},\kappa H]$ and the order is $q=3$; no dominance is needed and $B=0$ forces $w=y$. Every level set of $M_r$ is therefore null. This holds equally at $d=r$ and $d<r$, where only the transfer fails.

## 2. The uniform chain fails as proposed

The proposed argument assumed that at level $H$ every interval $I$ with $|I|\ge p^{-(\sigma_r/3)H}$ satisfies $|I\cap G_H|\ge c|I|$. All the pair-correlation errors of GF-11 are indeed $O(H^{O(r)}p^{(1-\mu)H})$ once $h_2\ge\lambda H$, so they allow such scales. The assumption fails because of the main term: the competitor count is not proportional to $|I|$ near sums of fewer coordinates.

**Proposition 2.1.** Let $p=3$, $d=4$, $r=3$, $\epsilon=\frac14$, $\delta_H=\epsilon/(H^2 3^H)$. Let $\rho_H=1/R_H$, where $R_H=\lceil(8(32H^2)^4)^{1/3}\rceil+1\asymp H^{8/3}$. Then for every $H\ge4$, every point of $(2+\rho_H,2+2\rho_H]$ lies within $\delta_H$ of a level-$H$ competitor sum $1^4+1^4+(a/3^H)^4$ with $3\nmid a$. Hence $G_H\cap(2+\rho_H+\delta_H,2+2\rho_H-\delta_H)=\emptyset$ for all $H\ge4$. For $H=4000$ one has $\rho_H>3^{-H/126}=3^{-\sigma_3H/3}$.

*Proof.* Consecutive admissible numerators differ by at most $2$. The gaps between the points $(a/3^H)^4$ increase with $a$, so all of them up to the first point above $2\rho_H$ are at most $(a_{\rm hi}^4-(a_{\rm hi}-2)^4)/3^{4H}$, where $a_{\rm hi}$ is two more than the least $a$ with $a^4\ge2\rho_H3^{4H}$. Since $a^4-(a-2)^4<8a^3$ and $a_{\rm hi}\le(2\rho_H)^{1/4}3^H+3$, the choice of $R_H$ makes $8a_{\rm hi}^3\le2\delta_H3^{4H}$ for every $H\ge5$ (and exact integer verification covers $H=4$ as well as $H=6,10,100,1000,4000$). The net starts below $2+\rho_H$ for $H\ge4$, since $\rho_H^{1/4}3^H\ge1$ gives an admissible $a\le\lfloor\rho_H^{1/4}3^H\rfloor$. A centre has three distinct positive losses, so it is never one of these tuples, and every centre in the interval has a competitor within $\delta_H$. The inequality $R_{4000}^{126}<3^{4000}$ is checked exactly. $\square$

The same mechanism works in general. Fix a sum $W$ of $r-1$ coordinates of coarse loss $g$. Competitors $(w,x)$ with $x$ small accumulate to the right of $W$, with density $\asymp p^{H-g}\rho^{1/d-1}$ at distance $\rho$, against the generic $H^{r-1}p^H$. So isolation fails on intervals of length $\asymp(p^{-g}H^{1-r})^{d/(d-1)}$ just above $W$. The level-6 counts in the script show this: in $(2,2+3^{-k}]$ they fall like $3^{-k/4}$, not like $3^{-k}$ (1497, 741, 432, 255 for $k=2,4,6,8$, against 573, 21, 6, 0 at $2.5$). Thus $I_{\min}(H)\gg H^{-(r-1)d/(d-1)}$ for any uniform statement. A matching upper bound is the hypothesis (LC) of §5.

The proposed exponent $L^{-\eta}$ therefore does not follow. What does follow is an averaged form of isolation, which survives because the inflated competitors have small total mass.

## 3. Isolation on unions of intervals

Fix $r\ge2$ and $d\ge2$, and set $K'=[1,p^d)$. The constraints used in GF-11 still hold for sums within $\delta_H$ of $K'$: $x^d+B\in[1/4,p^d+1]$, $z^d=S-B_y\in[1/2,p^d)$, and $z<p$. Modify the level-$H$ family in two respects. Require $h_1\ge h_{\min}(p,r,d):=\lceil\log_p(6/\theta)\rceil$ where $\theta=(2r)^{-1/d}$. For $r\ge3$, require $h_2\ge\max(2h_1+1,\lambda H)$ in place of $h_2\ge(\log H)^2$, with $\lambda=3\kappa/6^{r-1}$. For $r=2$, take the single anchor loss $h_1\in[h_{\min},\kappa H]$. Keep $\delta_H=\epsilon/(H^{r-1}p^H)$ and the precision $\pi_H=sH+e_r+1$, and allow $\epsilon$ to vary with $H$.

**Lemma I.** There are $A\ge1$, $\mu\in(0,1/d)$ and $H_*$, depending on $p,r,d,s,\kappa,c$, with the following property. Let $H\ge H_*$, $p^{-\mu H/8}\le\epsilon\le1$, $0<\tau\le1$, and let $X\subset K'$ be a union of $N$ disjoint intervals. Then

$$
 \#\{\text{centres in }X\}\ \ge\ A^{-1}|X|H^{r-1}p^H-ANH^Ap^{\kappa H},
$$

$$
 \#\{\text{non-isolated centres in }X\}\ \le\ A\epsilon\big(\tau^{1-d}|X|+\tau\big)H^{r-1}p^H+ANH^Ap^{(1-\mu)H}.
$$

*Proof.* Fix $\mu_0=1/(2r)$ and fix $\mu:=\frac12\min(\mu_{\rm GF11},\lambda/3,c/d-\kappa,\kappa,\mu_0,1/d)$ prior to imposing $\epsilon\ge p^{-\mu H/8}$ (here $\mu_{\rm GF11}>0$ is the GF-11 exponential-sum margin, or the $\eta$-capped margin of §1 when $q>d$). If $N=0$ then $X=\emptyset$ and both bounds are $0$; assume $N\ge1$.

**Centres.** Fix an anchor $y$. Each component $I_i$ of $X$ maps to a $z$-interval of length at least $|I_i|/(dp^{d-1})$, which contains at least $(1-1/p)p^v|I_i|/(dp^{d-1})-2$ admissible $z$. Since $h_i\ge h_{\min}$, each coordinate has at least $(1-1/p)\theta p^{h_i}-2\ge(\theta/3)p^{h_i}$ admissible numerators, so there are at least $(\theta/3)^{r-1}p^k$ anchors per loss vector and $\gg(\kappa H)^{r-1}$ loss vectors (for $H\ge H_*$), and at most $(\kappa H)^{r-1}p^{\kappa H}$ anchors in all.

**Collisions.** A non-isolated centre has a relevant competitor within $\delta_H$. We count the pairs exactly as in GF-11 §5, restricting the centres to $X$. Write $X^+$ for the $C_d\delta_H$-neighbourhood of $X$; it is a union of at most $N$ intervals.

- $B=0$. Exact coincidences do not depend on $X$. Peeling now gives savings $p^{-h_j/3}$ with $h_j\ge\lambda H$, for a total of $O(H^{O(r)}p^{(1-\lambda/3)H})$.
- $0<\lvert B\rvert<p^{-cH}$, and the removed points $x\le\eta$ or $\lvert\Phi_q\rvert\le\rho$. These contribute $O(H^{O(r)}p^{(1-\min(c/d-\kappa,\kappa))H})$, independent of $X$.
- $\lvert B\rvert\ge p^{-cH}$. Here $S(w,x)$ increases in $x$, so the points of a row with $S\in X^+$ form at most $N$ intervals. Intersecting these with the $O(qH)$ dyadic pieces gives at most $N+O(qH)$ pieces per row. Apply Erdős–Turán with $L_{\rm ET}=\lceil p^kH^{r+1}/\epsilon\rceil$ and Titchmarsh 5.13 to each piece. The extra factor $\epsilon^{-1/(2K_q-2)}\le p^{\mu H/16}$ in the harmonic sum is absorbed by our choice $\mu\le\mu_{\rm GF11}/2$. The first Titchmarsh term is linear in the piece length, so its total is unchanged. By concavity, the second term grows by at most $(N+O(qH))^{2/K_q}\ll_{q,d} N^{1/2}H^{1/2}\le N H^{O(1)}$. Pieces with fewer than two points cost at most $2(N+O(qH))$ per row. There are at most $H^{O(r)}p^{k+H'-v'}\le H^{O(r)}p^{(1-\kappa)H+O(1)}$ rows, using $\kappa\le1/(2r)$. With the margins of GF-11 (or of §1 when $q>d$), the errors total $O(N H^{O(r)}p^{(1-\mu)H})$.
- **Main term.** Erdős–Turán gives $\sum_y(2\eta_0+L_{\rm ET}^{-1})\operatorname{Comp}'(X^+)$, where $\operatorname{Comp}'(X^+)$ counts competitor tuples with $S\in X^+$ and $x$ running over all numerators (already dropping $p\nmid m'$). Since $\eta_0=C_d\epsilon p^{-k}H^{1-r}$, we get $\sum_y2\eta_0\le2C_d\epsilon\,\#\{\text{loss vectors}\}H^{1-r}\le2C_d\epsilon$ and $\sum_yL_{\rm ET}^{-1}\le\epsilon H^{-2}$.

**Counting competitors on $X^+$.** Put $\tilde\tau:=\max(\tau,p^{-\mu H})\in(0,1]$. Call a competitor *regular* if some coordinate $x_m\ge\tilde\tau$ has loss $g\ge\mu_0H$, and *irregular* otherwise.

For a regular competitor, fix the other coordinates (at most $p^{H'-g+r-1}$ choices) and vary $x_m$ over $p^{-g}\mathbb Z\cap[\tilde\tau,p)$. Since $\partial S/\partial x_m\ge d\tilde\tau^{d-1}$, at most $p^g|X^+|/(d\tilde\tau^{d-1})+N$ values have $S\in X^+$. Summing over loss vectors gives $O(\tilde\tau^{1-d}|X^+|H^{r-1}p^H)+O(NH^{r-1}p^{(1-\mu_0)H})$. Since $|X^+|\le|X|+2NC_d\delta_H$, $\tilde\tau^{1-d}\le\tau^{1-d}$, and $\mu<1/d$ (so $(d-1)\mu<1-\mu$), the boundary-difference contribution to the main term satisfies
$$
 2C_d\epsilon^2 N\tilde\tau^{1-d}\ \le\ 2C_d N p^{(d-1)\mu H}\ \le\ 2C_d N p^{(1-\mu)H},
$$
which is absorbed into the error term.

If an irregular competitor has $H'\ge r\mu_0H$, then some coordinate has loss at least $\mu_0H$, and every such coordinate is below $\tilde\tau$. So each loss vector carries at most $\tilde\tau p^{H'+r}$ irregular tuples, giving $O(\tilde\tau H^{r-1}p^H)$ in all. Multiplying by $O(\epsilon)$ yields $O(\epsilon\tau H^{r-1}p^H)+O(NH^{r-1}p^{(1-\mu)H})$ since $\tilde\tau\le\tau+p^{-\mu H}$ and $N\ge1$. Loss vectors with $H'<r\mu_0H$ carry $O(H^rp^{H/2})$ tuples. $\square$

The total count of irregular competitors is bounded with no localization. This works because their mass is a fraction $\tilde\tau$ of the whole, wherever $X$ lies. That is how the averaged form avoids the inflation of §2.

## 4. Effective small ball

**Theorem Q.** Let $r\ge2$ and $d\ge2$. There is $C$, depending on $p,r,d,s$, such that for every $w\in\mathbb Z_p$ and every $L\ge3$,

$$
 \big|\{u\in[1,p^d):\ M_r(u)\equiv w\pmod{p^L}\}\big|\ \le\ C(\log L)^{-d/(d-1)}.
$$

*Proof.* Put $E=\{M_r\equiv w\bmod p^L\}$ and $\Gamma=\lceil4/\mu\rceil+1$. Choose levels $H_0=H_*+\lceil C'\log\log L\rceil$ with $C'\ge24/(\mu\log p)$, and $H_{j+1}=\Gamma H_j$. We construct unions of intervals $X_0=K'\supset X_1\supset\cdots\supset E$ with $N_j$ components, maintaining $N_j\le A H_j^A p^{H_j}(j+1)$ (enlarging $A\ge\max(p^d,r-1)$). The levels used must satisfy $\pi_{H_j}\le L$, which allows $m(L)\ge\log(L/(2sH_0))/\log\Gamma-1\gg\log L$ steps.

*Step $j\to j+1$.* Let $x=|X_j|$ and $H=H_{j+1}$. If $x\le(\log L)^{-d/(d-1)}$, stop. Otherwise apply Lemma I with $\tau=(x/p^d)^{1/d}\le1$ and $\epsilon=x^{(d-1)/d}/(8p^dA^2)<1$. Since $x>(\log L)^{-d/(d-1)}\ge(\log L)^{-2}$ and $\epsilon>(\log L)^{-1}/(8p^dA^2)$, while $H\ge\Gamma C'\log\log L$, both $\epsilon\ge p^{-\mu H/8}$ and $x\ge p^{-\mu H/8}$ hold for all large $L$, so Lemma I applies. Since $\tau^{1-d}x+\tau\le2p^{d-1}x^{1/d}$, the main collision term is at most $2p^{d-1}A\epsilon x^{1/d}H^{r-1}p^H\le x H^{r-1}p^H/(4A)$. Since $N_j\le A H_j^{A}p^{H_j}(j+1)$ and $H_j\le\mu H/4$, every error term is at most $p^{(1-\mu/2)H}$. This is at most $xH^{r-1}p^H/(4A)$ because $x\ge p^{-\mu H/8}$. Hence at least $xH^{r-1}p^H/(2A)$ centres in $X_j$ are isolated.

Each isolated centre $\xi$ has two flanks $(\xi-\delta_H/2,\xi)$ and $(\xi,\xi+\delta_H/2)$. On each flank, $M_r\bmod p^{\pi_H}$ is constant, and the two residues differ by $r!p^{sH}\not\equiv0$. So one flank misses $\{M_r\equiv w\bmod p^{\pi_H}\}\supset E$. The flanks of distinct isolated centres are disjoint, since the centres are $\delta_H$-separated. At most $2N_j$ centres lie within $\delta_H/2$ of $\partial X_j$. Removing the missed open flanks increases the component count by at most $1$ per removed flank, and there are at most $p H^{r-1}p^H$ level-$H$ centres in $K'$, so $N_{j+1}\le N_j+p H^{r-1}p^H\le A H^A p^H(j+2)$ holds inductively. Removing the missed flanks gives $X_{j+1}\supset E$ with

$$
 |X_{j+1}|\le x-\Big(\frac{x H^{r-1}p^H}{2A}-2N_j\Big)\frac{\delta_H}{2}\le x\big(1-c_1x^{(d-1)/d}\big),\qquad c_1=\frac1{40p^dA^3}.
$$

*Recursion.* Put $a=(d-1)/d$ and $y_j=x_j^{-a}$. Bernoulli's inequality gives $y_{j+1}\ge y_j(1+ac_1x_j^a)=y_j+ac_1$. So $x_j\le(ac_1j)^{-d/(d-1)}$ as long as the process has not stopped. Taking $j=m(L)\gg\log L$ proves the bound. $\square$

The kill fraction per level is $\asymp|X_j|^{(d-1)/d}$, not a constant. This costs the exponent: it gives $(\log L)^{-d/(d-1)}$ in place of $L^{-\eta}$. The loss comes only from the irregular competitors, whose positions could not be controlled.

## 5. Effective discrepancy and what blocks more

**Corollary Q1.** Let $P\in\mathbb Q[x]$ have degree $r\ge2$, and suppose $d>r(s+1)$. Then

$$
 D_N(P(C);b)\ll_P(\log\log N)^{-d/(d-1)}.
$$

This upgrades the Phase 19 square theorem (OP-14) for $d\ge2s+3$ and GF-11 for $d\ge r(s+1)+1$ from qualitative normality to an explicit rate.

*Proof.* First clear denominators as in Phase 20 C1 §3, using the $b^c$ shift. Then apply the Phase 19 prefix estimate with its tail term replaced by $\sup\lvert b^nx-R_n\rvert$ outside the buffers. The coefficients are $O(m^{(r-1)/d})$, so $H=\lceil2\log_bN\rceil$ makes the tail $O(N^{-1})$. Take $L=\lfloor c_0\log N\rfloor$ with $c_0>0$ chosen small enough that $(c_0\log p)/s<r/d$, $c_0\log p<rs/(2d)$, and $c_0(1+d/s)\log p<1/2$.

1. *Freezing.* For $J\ge J_0(L)=\lceil L/s+L/d\rceil$, one has $p^{rsJ}b^{-n}R_n\equiv AM_r(u)\pmod{p^L}$. Indices of loss $h\le L/s$ satisfy $v_p(b^{ti^d}-1)=a_0+d(J-h)\ge L$, and lower degrees carry $p^{sJ}$. The script verifies this on the actual prefix of $C(2,3,1,4)^3$ at $J=4$, $L=3$, using all ordered triples. Shifts with $J<J_0(L)$ number $O(p^{d J_0(L)})=O(N^{1/2})$.
2. *Failed shifts.* These satisfy $u\in\{M_r\equiv0\bmod p^{L-v_p(A)}\}$. There are at most $CN(\log L)^{-d/(d-1)}$ of them by Theorem Q, plus a rounding error of $O(\log N\cdot L^{r-1}p^{L/s})=o(N^{r/d})$ from the cells.
3. *Mesh.* At the other shifts, $v_p(q_n)\ge rsJ-L+1$. The exact grid theorem then gives $1/G_n\le p^{L+a_0+O(1)}n^{-rs/d}$, whose average over $n<N$ is $O(p^L N^{-rs/d})=O(N^{-rs/(2d)})$ (since $c_0\log p<rs/(2d)$ and $rs/d<1$).
4. *Periods.* Since $(c_0\log p)/s<r/d$, the run count is $O(N^{r/d}+\log N\,L^{r-1}p^{L/s})=O(N^{r/d})$, and each run has period at most $q_n\ll N^{rs/d}$. Their residual cost is $O(N^{r(s+1)/d})=O(N^{1-\eta'})$, because $d>r(s+1)$.
5. *Buffers.* These cost $O(N^{r/d}\log N)$.

Every term except step 2 is $O(N^{-\eta''})$. $\square$

**The range $r+1\le d\le r(s+1)$.** Here runs are shorter than periods. The proof of GF-11 uses the fixed-support kernel `SmoothOrbit`, whose threshold is not explicit. Any short-orbit bound for $b^ja/p^e$ that is explicit for $T\ge p^{\theta e}$, such as a Korobov-type estimate for prime-power moduli, would extend Corollary Q1 to the whole range $d\ge r+1$. Such an input has not been checked here, so the extension is stated only as a conditional.

**Conditional power saving.** Consider the hypothesis

> (LC) For some $a>0$, every union $X\subset K'$ of $N$ intervals satisfies $\operatorname{Comp}(X^+)\le C_0(|X|+H^{-a})H^{r-1}p^H+NH^Ap^{(1-\mu)H}$.

Under (LC), Lemma I holds with a fixed $\epsilon$ (adding an $O(H^{-a}H^{r-1}p^H)$ term to the collision bound without cutting $X$ by a high-complexity set), and the recursion becomes $x_{j+1}\le(1-c)x_j+H_{j+1}^{-a}$. This gives $|E|\ll L^{-\eta}$ and $D_N\ll(\log N)^{-\eta}$ under the hypothesis of Corollary Q1. The heuristic of §2 suggests that the inflated competitors concentrate in right-neighbourhoods $(W,W+(p^{-g}H^{1-r})^{d/(d-1)})$ of sums $W$ of fewer coordinates, of total measure $\asymp H^{-(r-1)d/(d-1)}$. This is unproved.

## 6. Lean core (C1.3)

The following statements typecheck, with `sorry` proofs, against Lean 4.36.0 and the Mathlib snapshot of the Phase 20 build. Each is a finite statement used in §1–§4. None is proved yet, and no repository Lean file was changed.

```lean
namespace NormalityChecker.NonlinearCore
open Finset MvPolynomial

/-- Coincidence peeling: a sum of `d`-th powers of valuation `-(d h)` forces a unique
coordinate of loss `h` in any family of total loss below `2h`. -/
theorem unique_top_loss_of_eq_sum_pow {p : ℕ} [Fact p.Prime] {d h : ℕ} (hd : 0 < d)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (y : ι → ℚ) (w : κ → ℚ) (hw0 : ∀ j, w j ≠ 0)
    (hsum : ∑ i, y i ^ d = ∑ j, w j ^ d)
    (hval : padicValRat p (∑ i, y i ^ d) = -((d * h : ℕ) : ℤ))
    (hloss : ∑ j, (-padicValRat p (w j)).toNat < 2 * h) :
    ∃! j, padicValRat p (w j) = -(h : ℤ)

/-- Divisor bound for `a^d - c^d = M` (`d ≥ 2`); solutions satisfy `a ≤ M`. -/
theorem le_of_pow_sub_pow_eq {d a c M : ℕ} (hd : 2 ≤ d) (hca : c < a)
    (h : a ^ d - c ^ d = M) : a ≤ M
theorem card_pow_sub_pow_eq_le {d M : ℕ} (hd : 2 ≤ d) :
    ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
        (fun ac : ℕ × ℕ => 0 < ac.2 ∧ ac.2 < ac.1 ∧ ac.1 ^ d - ac.2 ^ d = M)).card
      ≤ M.divisors.card

/-- `Φ_q(X, B)` with `X = X 0`, `B = X 1`. -/
noncomputable def phi (d : ℕ) : ℕ → MvPolynomial (Fin 2) ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | q + 3 =>
      (C ((d : ℤ) - (q + 2)) * (X 0 + X 1) + C (1 - ((q : ℤ) + 2) * d) * X 0) * phi d (q + 2)
        + C (d : ℤ) * X 0 * (X 0 + X 1) * pderiv 0 (phi d (q + 2))
theorem phi_three (d : ℕ) : phi d 3 = C ((d : ℤ) - 2) * X 1 - C ((d : ℤ) + 1) * X 0
theorem phi_homogeneous (d : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    ∀ m ∈ (phi d q).support, m 0 + m 1 = q - 2
theorem coeff_phi_X_pow (d : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    (phi d q).coeff (Finsupp.single 0 (q - 2)) =
      (-1) ^ q * ∏ i ∈ Finset.Icc 1 (q - 2), ((d : ℤ) + i)
theorem iteratedDeriv_rpow_root {d q : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) {B x : ℝ} (hx : 0 < x)
    (hxB : 0 < x ^ d + B) :
    iteratedDeriv q (fun t : ℝ => (t ^ d + B) ^ ((1 : ℝ) / d)) x =
      ((d : ℝ) - 1) * B * x ^ ((d : ℤ) - q) * (x ^ d + B) ^ ((1 : ℝ) / d - q) *
        MvPolynomial.eval ![x ^ d, B] ((phi d q).map (Int.castRingHom ℝ))

/-- Truncated `r`-fold mass and its jump at an isolated centre. -/
def truncMass (r p s d Λ : ℕ) (coords : Finset ℚ) (loss : ℚ → ℕ) (u : ℚ) : ℤ :=
  ∑ z ∈ (Fintype.piFinset fun _ : Fin r => coords).filter
      (fun z => ∑ i, loss (z i) ≤ Λ ∧ ∑ i, z i ^ d ≤ u),
    (p : ℤ) ^ (s * ∑ i, loss (z i))
theorem truncMass_sub {r p s d Λ : ℕ} {coords : Finset ℚ} {loss : ℚ → ℕ} {u u' : ℚ}
    (h : u ≤ u') :
    truncMass r p s d Λ coords loss u' - truncMass r p s d Λ coords loss u =
      ∑ z ∈ (Fintype.piFinset fun _ : Fin r => coords).filter
          (fun z => ∑ i, loss (z i) ≤ Λ ∧ u < ∑ i, z i ^ d ∧ ∑ i, z i ^ d ≤ u'),
        (p : ℤ) ^ (s * ∑ i, loss (z i))
theorem truncMass_jump_of_isolated {r p s d Λ H : ℕ} {coords : Finset ℚ} {loss : ℚ → ℕ}
    {c : Fin r → ℚ} (hc : ∀ i, c i ∈ coords) (hinj : Function.Injective c)
    (hlev : ∑ i, loss (c i) = H) (hHΛ : H ≤ Λ) {δ : ℚ} (hδ : 0 < δ)
    (hiso : ∀ z : Fin r → ℚ, (∀ i, z i ∈ coords) → ∑ i, loss (z i) ≤ Λ →
      |∑ i, z i ^ d - ∑ i, c i ^ d| < δ → ∃ σ : Equiv.Perm (Fin r), z = c ∘ σ) :
    truncMass r p s d Λ coords loss (∑ i, c i ^ d + δ / 2)
        - truncMass r p s d Λ coords loss (∑ i, c i ^ d - δ / 2)
      = (r.factorial : ℤ) * (p : ℤ) ^ (s * H)
```

The imports are `Mathlib.NumberTheory.Padics.PadicVal.Basic`, `Mathlib.NumberTheory.Divisors`, `Mathlib.Algebra.MvPolynomial.PDeriv`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Analysis.Calculus.IteratedDeriv.Defs` and `Mathlib.Data.Fintype.Pi`. Homogeneity is stated through the support, because `RingTheory.MvPolynomial.Homogeneous` is not built in that snapshot. The derivative identity is the only analytic statement. The Erdős–Turán, Titchmarsh and measure-theoretic steps remain written deductions.

**Kernel-verified implementation in `NormalityChecker/PowerSumPeeling.lean`.** The repository module `NormalityChecker/PowerSumPeeling.lean` (compiled with zero warnings and kernel-replayed with `leanchecker`) provides `sorry`-free proofs of the divisor bound (`card_pow_diff_eq_le_divisors`), the degree, leading coefficient, and nonvanishing of $\Phi_q$ (`phiPoly_natDegree`, `phiPoly_leadingCoeff`, `phiPoly_ne_zero`, in $\mathbb Z[B][X]$), the dominant-loss $p$-adic peeling lemma (`dominant_loss_unique_top_coord`), and the exact truncated-mass jump (`truncMass_sub`, `truncMass_jump_of_isolated`). Two blueprint statements above remain unproved in Lean: `MvPolynomial` support homogeneity of $\Phi_q$ and the real iterated-derivative identity `iteratedDeriv_rpow_root`.

## 7. The boundary $d=r$ (C2)

### 7.1 Counts

At $d=r$ the ordered tuples with $\sum i_j^d\le X$ number $\sim\operatorname{vol}\cdot X$. For squares the constant is $\pi/4$ (784387 pairs up to $10^6$); for cubes it is $\Gamma(4/3)^3\approx0.712$ (698529 triples). The Phase 18 criterion needs $O(N^{1-\eta})$ insertions, so it fails. The distinct positions behave differently in the two cases.

- $r=d=2$: there are $\sim KX/\sqrt{\log X}$ sums of two positive squares, by Landau (215908 up to $10^6$, 1.05 times the leading term). So the distinct support has density zero, but it is not $O(X^{1-\eta})$.
- $r=d=3$: there are at most $(\Gamma(4/3)^3/6+o(1))X\approx0.119X$ distinct sums of three positive cubes (104252 up to $10^6$). Unconditional lower bounds are only of the form $X^{\beta}$ with $\beta<1$ (Wooley; a literature input, not checked here). Positive density is conjectural.

### 7.2 Full depth at $d=r$

**Proposition D.** Let $d\ge2$ and let $P$ have degree $r\ge2$; in particular $d=r$ is allowed. There is a constant $C_P$ such that for every $L\ge3$, the shifts $n\le N$ with $v_p(q_n)<rsJ(n)-L$ have upper density at most $C_P(\log L)^{-d/(d-1)}$. Hence $rsJ(n)-v_p(q_n)$ is tight in density (for every $\varepsilon>0$ there exists $L$ such that $v_p(q_n)\ge rsJ(n)-L$ on a set of shifts of lower density $\ge1-\varepsilon$), and for every function $\omega(n)\to\infty$, $v_p(q_n)\ge rsJ(n)-\omega(n)$ on a set of shifts of density one.

*Proof.* Freezing (§5, step 1) uses no sparsity. Theorem Q holds for all $d\ge2$ (§1, §4), with $C_P$ absorbing $L\le2+v_p(A)$. Integer sampling of the cells is as in §5, giving upper density $\le C_P(\log L)^{-d/(d-1)}$ for every fixed $L\ge3$. The density-one consequence for any $\omega(n)\to\infty$ follows immediately because $\{n\le N:v_p(q_n)<rsJ(n)-\omega(n)\}\subseteq\{n\le N:\omega(n)<L\}\cup\{n\le N:v_p(q_n)<rsJ(n)-L\}$ for every fixed $L\ge3$. $\square$

The script measures this exactly. Over shifts $2\cdot10^5$ to $4\cdot10^5$, the depth of $q_n$ is at least $rJ-1$ on every sampled shift, for both $C(2,3,1,2)^2$ and $C(2,3,1,3)^3$. It is at least $rJ$ on 82% and 100% respectively. For squares the defect occurs on that window exactly for $u<2$, where the level-0 count of $M_2$ is $0$ (note that across the full shell $[1,9)$, $\{M_2\equiv0\bmod3^L\}$ has positive measure for every fixed $L$, which is why the conclusion is tightness in density rather than a uniform $O(1)$ bound on density one).

### 7.3 Why the method stops

The p-adic half survives at $d=r$; the real half does not.

1. **Runs versus denominators.** The mean distance between insertions is $2\cdot(\text{mean gap})$: $O(\sqrt{\log N})$ for squares (8.7 measured) and $O(1)$ for cubes if positive density holds (18.7 measured). Meanwhile $\log q_n\asymp\log N$. Complete periods need runs at least as long as the period, and the kernel needs $q\le T^{D}$; both fail. Short-orbit estimates for prime-power moduli become nontrivial only for orbits much longer than $\log q$, and below $\log_b(q/2)$ item 2 rules out every estimate that uses denominators alone.
2. **Denominator data cannot determine the digits.** *Lemma.* If $q=p^e$ and $b^T\le q/2$, then every word of $T$ base-$b$ digits is the leading word of some $a/q$ with $p\nmid a$. *Proof:* consecutive admissible $a$ differ by at most $2$, so $\lfloor ab^T/q\rfloor$ advances by at most $1$. $\square$ (The script checks this for $q=3^e$, $e\le9$.) On a run of length $T\le\log_b(q/2)$, any statement depending only on $(q_n,\text{run lengths})$ is therefore compatible with every digit pattern. At $d=r$ almost every run is of this kind. Any proof must use numerator information at resolution $b^{-T}$. But $R_n=b^nx-T_n$, so that information is the distribution of $b^nx$ itself.
3. **The real tail is $O(1)$ on average.** One has $\frac1N\sum_{n<N}T_n\ge\frac1{(b-1)N}\sum_{m\le N}c_m(1-b^{-m})$ (since $\sum_{n=0}^{m-1}b^{n-m}=(1-b^{-m})/(b-1)$), and the cumulative weight per shift is $0.221$ (squares) and $0.150$ (cubes). For squares, $T_n\to0$ in density: split $T_n=\sum_{u\le H}c_{n+u}b^{-u}+\sum_{u>H}c_{n+u}b^{-u}$; the first sum vanishes off a set of density $0$ by Landau's bound, and the second has average $\frac1N\sum_{n<N}\sum_{u>H}c_{n+u}b^{-u}\ll b^{-H}$ (since $\sum_{m\le X}c_m=O(X)$), so Markov's inequality sends it to $0$ in density as $H\to\infty$. That is harmless, but the runs stay short. For cubes, 16.5% of the sampled shifts have $T_n\ge1/8$. A positive-proportion statement would need positive lower density of sums of three cubes, which is open.
4. **Low-depth layers and multipliers.** At shift $n$, a present tuple of depth $0$ contributes an integer, and a tuple of depth $m$ contributes an element of $p^{-sm}\mathbb Z/\mathbb Z$. So the depth-$\le M$ part of $R_n$ is a step process in a finite group that changes at density $\Theta(1)$. Multiplying $x$ by $p^{sM}$ makes those tuples integral, but it multiplies the tail by $p^{sM}$ and does not change normality. Letting $M\to\infty$ would mean a growing Weyl frequency, which the criterion does not allow. The sparse high-depth layer (depth $\ge rsJ-H$, $O(H^{r-1}p^H)$ tuples per shell) controls the denominator, as in Proposition D, but not the short-run digits.

**Proposed strategies at $d=r$.**

| Strategy | Verdict |
|---|---|
| Sparse high-depth layers (depth $\ge rsJ-H$, $O(H^{r-1}p^H)$ tuples per shell) | Correct and sparse. They fix the denominator (Proposition D), but they do not control digits on short runs (item 2) |
| Retirement of low-depth tuples | Correct: present depth-$0$ tuples are integers. Depth-$m$ tuples still arrive at density $\asymp m^{r-1}p^{-m}$ with denominator $p^{sm}$. That gives a finite-group step process of density $\Theta(1)$ (item 4) |
| Small real tail on gap windows | For squares, $T_n\to0$ in density by Landau. For cubes, a positive-proportion statement is open, and the numerics give $T_n\ge1/8$ on 16.5% of shifts. In neither case does it lengthen the runs |
| Multiplying by $p^{sM}$ | It changes neither normality nor the run structure, and it scales the tail. Sending $M\to\infty$ would need a growing Weyl frequency |
| Landau sparsity for $C(b,p,s,2)^2$ | The distinct positions have density zero but number $\gg N/\sqrt{\log N}$. Runs of length $O(\sqrt{\log N})$ against $\log q\asymp\log N$ fall under item 2 |
| A ceiling $D^+<1$ | Not proved. It would need numerator information, as explained below |

**What is proved at $d=r$.** Proposition D, the barrier lemma, and the exact counts. Normality of $C(2,3,1,3)^3$ and of $C(b,p,s,2)^2$, and even $\limsup D_N<1$, remain open. If $D_N\to1$ along a subsequence, almost all orbit points lie near a fixed point of $x\mapsto bx$, so the digits would be asymptotically constant in density. Excluding that would also need numerator information. Finite statistics are consistent with normality: in the first 20000 bits, the largest block-frequency deviation for $k\le3$ is $0.0076$ for $C(2,3,1,2)^2$ and $0.0082$ for $C(2,3,1,3)^3$, against $0.498$ for the unweighted $C(2,3,0,2)^2$. This is evidence only.

## 8. Exact checks

`python -B scripts/phase21_nonlinear.py` runs in about 6 seconds and exits 0. For C1–C2 it checks the following.

- **Freezing.** The actual prefix of $C(2,3,1,4)^3$, using all ordered triples, agrees with $M_3(u)\bmod 27$ at $J_0(3)=4$ on six random shifts.
- **The counterexample of §2.** The $\delta_H$-net is certified in exact integers for $H\in\{6,10,100,1000,4000\}$, and $\rho_{4000}>3^{-4000/126}$.
- **Inflation.** It counts level-6 competitors near $u=2$.
- **Margins.** The margin for $r=2$, $q=3$ is exactly $1/12$, and the capped cases $q>d$ have positive margins.
- **The boundary $d=r$.** It reports ordered and distinct counts up to $10^6$, the exact 3-adic depth of every shifted prefix up to $4\cdot10^5$, the real tail, run lengths, the barrier lemma, and digit statistics (evidence only).

The finite computations illustrate the mechanisms; the asymptotic statements rest on the written proofs above.
