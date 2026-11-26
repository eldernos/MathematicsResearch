# Several orders on one schedule, and denser all-prime families (Tracks C3–C4)

Notation follows [nonlinear-boundary.md](nonlinear-boundary.md) and [GF-11](../phase20/cubic-power-schedule.md): $b\ge2$, $p\nmid b$ an odd prime, $t=\operatorname{ord}_pb$, $a_0=v_p(b^t-1)$, coordinates $z=a/p^h\in(0,p)$ with loss $h$, and shifts $n=tp^{dJ}u$.

## Summary

| Item | Result | Evidence |
|---|---|---|
| C3 | **Theorem M.** For any distinct orders $s_1<\cdots<s_m$, every nonconstant $P\in\mathbb Q[X_1,\ldots,X_m]$ of total degree $r<d$ in $X_a=C(b,p,s_a,d)$ is normal. This includes ties of different degrees | Paper proof extending GF-11 (§1–3). Exact jumps at tied centres in the script |
| C3, the proposed lex rule | Pure lex-min of sorted order tuples works across mixed degrees (do not maximize degree first). The higher orders must sit on **bounded** losses with inductively chosen numerators; otherwise the relevant competitors grow by $p^{\text{excess}/s_*}$ and $B=0$ peeling fails. Loss-$0$ coordinates can cancel the leading jump | Proof, plus exact counts and the cancellation $X_1X_2X_4-X_1X_3^2$ |
| C4 refined protected pole | Every off-radix prime in $W$, with $W$ normal and Liouville, on $n_k=\lceil\exp(k(\log\log k)^2)\rceil$. Degree $\le r$ on $\exp((r-1+\epsilon)k\log k)$. All degrees on $\exp(k\log k\,\psi(k))$ with $\psi\to\infty$ | Paper (§5), refining Phase 20 C2a |
| C4 polynomial hybrid | **Theorem H.** On $n_k=tk^d$, with auxiliary primes at sparse indices prime to $p$ and $d>r(s+1)$: every $P$ of degree $\le r$ is normal, with $D_N\ll(\log\log N)^{-d/(d-1)}$, and every off-radix prime divides the prefix denominators of $W$ | Paper (§6). Exact denominators, residues and pollution in the script |
| C4 all degrees | **Theorem U.** The Phase 19 schedule with $\log n_i\sim(\log i)^2$ and delayed auxiliary primes gives all-degree, all-prime polynomial normality | Paper (§7) |
| C4 thresholds | Complete periods need the $j$-th prime to appear no earlier than position $\exp(cj\log j)$ for degree $\ge2$, and no earlier than $\exp(cj\log\log j\log\log\log j)$ for degree $1$. These thresholds are sufficient, not proved necessary | §5, §8 |

[Exact checks](../../scripts/phase21_nonlinear.py)

## 1. Several orders: the tied top-depth mass

Let $1\le s_1<\cdots<s_m$ and $X_a=C(b,p,s_a,d)$. Clear denominators, so that $P=\sum_\nu A_\nu X^\nu$ with integral $A_\nu$, total degree $r\le d-1$, and $P$ nonconstant. A monomial $X^\nu$ expands over *slot tuples*: for each $a$, an ordered $\nu_a$-tuple of indices. At scale $J$ its deepest pole is $p^{-(s\cdot\nu)J}$. Put

$$
 S^*=\max\{s\cdot\nu:\ A_\nu\ne0,\ \nu\ne0\},\qquad T=\{\nu:\ A_\nu\ne0,\ s\cdot\nu=S^*\}.
$$

Monomials outside $T$ carry at least $p^{J}$ after normalization by $p^{S^*J}$. A slot carrying variable $a$ with a coordinate of loss $h$ contributes weight $p^{s_ah}$. As in GF-11 §1, for $J\ge\lceil L/s_1+L/d\rceil$,

$$
 p^{S^*J}b^{-n}R_n\equiv M_P(u)=\sum_{\nu\in T}A_\nu M_\nu(u)\pmod{p^L},\qquad
 M_\nu(u)=\sum_{\text{slot tuples},\ S(z)\le u}p^{\sum_{\text{slots}}s_{a(\text{slot})}h(z_{\text{slot}})}.
$$

There are $O(N^{r/d})$ insertions and the denominators divide $p^{S^*J}M'$. So, exactly as in GF-11, $P(X)$ is normal once $\{M_P=0\}$ is null. The weighted level of a slot tuple is $\sum s_{a(\text{slot})}h$, and only tuples of weighted level $<L$ matter modulo $p^L$.

**Theorem M.** Under these hypotheses every level set of $M_P$ is null. Hence $P(X_1,\ldots,X_m)$ is normal in base $b$. In particular the $X_a$ satisfy no nonzero rational polynomial relation of total degree $<d$, and distinct nonconstant monomials of total degree $<d$ have jointly uniformly distributed shifts.

Phase 19 proved the case $r\le2$, and GF-11 the case $m=1$.

## 2. Choosing the centre

If $r=1$, then $T=\{X_{a_*}\}$ is a single linear variable, $M_P(u)=A M_1(u)$, every level-$H$ point $m/p^H$ is isolated at radius $p^{-H}$ (and $M_1(u)\equiv\lfloor u^{1/d}\rfloor\not\equiv0\pmod p$), so Theorem M is immediate. Assume now $r\ge2$ (note that $r=2$ is already covered by Phase 19, and also by the proof below using $q=3$ with margin $1/12$ from [nonlinear-boundary.md §1](nonlinear-boundary.md#1-audit-of-gf-11-c11)).

**The target monomial (pure lex-min).** For each $\nu\in T$, list its slot orders in nondecreasing order as $\mathbf o(\nu)=(o_1(\nu)\le\cdots\le o_{\deg\nu}(\nu))$. Distinct $\nu$ have distinct multisets $\mathbf o(\nu)$, and no $\mathbf o(\nu)$ can be a proper prefix of another (their entries all sum to $S^*$). Define $\nu^*\in T$ directly as the monomial with **lexicographically least** sorted order tuple $\mathbf o(\nu^*)$. Put $s_*=o_1(\nu^*)=s_{a_*}$, $n_*=\nu^*_{a_*}\ge1$, $r_*=\deg(\nu^*)$, $m_*=r_*-n_*$, and write $u(\nu^*)=(u_1\le\cdots\le u_{m_*})$ for the remaining higher orders ($u_i>s_*$). Pure lex-min automatically minimizes $s_*$ and maximizes $n_*=\max_{\nu\in T}\nu_{a_*}$ (note that maximizing degree before lex-min fails for mixed degrees such as $X_1X_3^4+X_1X_2^2X_4$, where a lower-degree competitor has smaller higher-slot orders). If $r_*=1$, then $T=\{X_{a_*}\}$ (since any other monomial in $T$ has $\nu_{a_*}\le1$ and all remaining orders $>s_*$, impossible if $\nu_{a_*}=1$ with total $S^*=s_*$), which is already handled above. Assume $r_*\ge2$.

**The centre.** Fix a constant $G_0>\max_{\nu\in T}v_p(A_\nu\prod_a\nu_a!)+2$ and put $e_{\rm prec}:=v_p(A_{\nu^*}\prod_a\nu^*_a!)+1<G_0$. Put $\theta=(2r)^{-1/d}$. The centre has three parts:

- A **bounded part** of $m_*$ fixed coordinates $y_1=a_1/p^{g_1},\dots,y_{m_*}=a_{m_*}/p^{g_{m_*}}\le\theta$ with $p\nmid a_j$ and $g_1<\cdots<g_{m_*}$, chosen **sequentially** (independent of $H$) as follows. Having chosen $(g_1,a_1),\dots,(g_{j-1},a_{j-1})$, set $B_{j-1}:=\frac{s_m}{s_*}\sum_{i<j}g_i+e_{\rm prec}$. Choose $g_j>\max(2B_{j-1}+C_0,\ s_m\sum_{i<j}g_i+G_0,\ \lceil\log_p(6/\theta)\rceil)$ large enough that the total number of $(q'-1)$-tuples $(w_l)$ (with $q'\le r$) of total unweighted loss $\le B_{j-1}$ multiplied by $2\max_{|M|\le r p^{d(g_j+1)}}\tau(|M|)$ (which is $\ll B_{j-1}^r p^{B_{j-1}+\epsilon' d g_j}\ll p^{(1/2+\epsilon' d)g_j}$) is strictly smaller than the number of admissible $a_j\in[1,\theta p^{g_j}]$ with $p\nmid a_j$ (which is $\ge(\theta/3)p^{g_j}$). Pick an admissible $a_j$ avoiding all solutions of $c^d-a_j^d=M\ne0$ where $M=p^{dg_j}(\sum_{i<j}y_i^d-\sum_l w_l^d)$ ranges over all such $(w_l)$.
- A **free part** of $n_*-1$ coordinates $b_j/p^{h_j}\le\theta$ with $p\nmid b_j$. Put $M_s:=\max(2,s_m)$ (so $M_s=s_m$ whenever $m\ge2$, and $M_s=2$ also covers $m=1,s_1=1$). Choose $\kappa<\min(\frac1{2r},\frac1{M_s+1})$ and $\lambda\le\kappa/(3M_s)^{n_*-1}$, and require $h_1\ge\max(\lambda H,\ M_s\sum_{i=1}^{m_*}g_i+G_0)$, $h_{j+1}\ge M_s(\sum_{i=1}^{m_*}g_i+h_1+\cdots+h_j)+G_0$, and $k:=\sum_{i=1}^{m_*}g_i+\sum_{j=1}^{n_*-1}h_j\le\kappa H$.
- A last coordinate $z=m/p^v$ with $p\nmid m$ and $v=H-k$.

All losses are distinct: $g_1<\cdots<g_{m_*}<h_1<\cdots<h_{n_*-1}<v$, and $v-s_m k\ge(1-(s_m+1)\kappa)H\ge G_0$ for large $H$.

**The jump.** At $\xi=S(\text{centre})$, the slot tuples with $S=\xi$ of weighted level $<\pi$ are, once the centre is isolated (§3), precisely the assignments of the $r_*$ centre coordinates to the slots of $\nu^*$. By the rearrangement inequality, the least weight puts the ascending orders on the descending losses. For $\nu^*$ this gives

$$
 w^*=s_*(v+h_1+\cdots+h_{n_*-1})+\sum_{i=1}^{m_*}u_i(\nu^*)\,g_{m_*+1-i},
$$

attained by exactly $\prod_a\nu^*_a!$ slot tuples. Every other assignment for $\nu^*$ moves a larger order onto a larger loss, which increases the weight by at least $G_0$ (using $g_j\ge s_m\sum_{i<j}g_i+G_0$, $h_1\ge s_m\sum g_i+G_0$, $h_{j+1}\ge s_m(\sum g_i+\sum_{l\le j}h_l)+G_0$, and $v\ge s_m k+G_0$). So at precision $\pi=w^*+e_{\rm prec}$ the jump is $A_{\nu^*}\prod_a\nu^*_a!\,p^{w^*}\not\equiv0\pmod{p^\pi}$.

**Relevant competitors.** Every variable in $T$ has order $\ge s_*$. Set $C_g:=\frac1{s_*}\sum_{i=1}^{m_*}(u_i(\nu^*)-s_*)g_{m_*+1-i}+e_{\rm prec}/s_*=O(1)$. A slot tuple of $\nu'\in T$ of weighted level $<\pi$ has unweighted level $H'<\pi/s_*=H+C_g$. The number of such tuples for $\nu'\in T$ is:

- $O(H^{r-1}p^{\frac{s_*}{s_*+1}H})=o(p^H)$ when $\nu'_{a_*}=0$ (every slot has order $\ge s_*+1$);
- $O(H^{\nu'_{a_*}-1}p^H\prod_{\text{higher slots}}\sum_{e\ge0}p^{e(1-o/s_*)})=O(H^{\nu'_{a_*}-1}p^H)$ when $\nu'_{a_*}\ge1$, which is $o(H^{n_*-1}p^H)$ whenever $\nu'_{a_*}<n_*$ and $O(H^{n_*-1}p^H)$ when $\nu'_{a_*}=n_*$.

The number of centres in an interval $I\subset K'$ is $\asymp(\kappa H)^{n_*-1}p^{H-\sum g_i}|I|$ (with bounded-part constant depending only on the fixed $g_i$). Put $\delta_H=\epsilon/(H^{n_*-1}p^H)$, where $\epsilon\le\epsilon_0:=(2C_d)^{-1}p^{-C_g}$. When $n_*=1$ there is no free part: $\asymp p^H|I|$ centres against $O(p^H)$ competitors.

## 3. Isolation, $L^1$ localization, and the corrections to the proposed rule

Isolation follows GF-11 §5, with two essential upgrades for $m_*\ge1$: weighted peeling of the inductively chosen bounded coordinates at $B=0$, and $L^1$ Lebesgue-point localization for the main term. Fix $\epsilon\in(0,\epsilon_0]$ and an interval $I\subset K'$.

- **$B=0$ (weighted peeling).** Because $\epsilon\le\epsilon_0=(2C_d)^{-1}p^{-C_g}$, we have $\delta'=C_d\epsilon H^{1-n_*}p^{-H}<p^{-H-C_g}\le p^{-\max(v,v')}$ even when $n_*=1$, so rational separation forces $x=z$ and $v'=v$. In $\nu'\in T$, the coordinate $x$ must sit in an order-$s_*$ slot (otherwise its weight alone is $\ge(s_*+1)v>\pi$ for large $H$). Cancelling $s_*v$ gives the weighted budget
  $$
   s_*\sum f_i+\sum o'_l e_l\ \le\ s_*(h_1+\cdots+h_{n_*-1})+\sum_{i=1}^{m_*}u_i(\nu^*)g_{m_*+1-i}+e_{\rm prec}. \tag{$*$}
  $$
  Peel the free coordinates $h_{n_*-1},\dots,h_1$ downward: at $h_j\ge\lambda H$, dividing $(*)$ by $s_*$ bounds the remaining total unweighted loss by $<2h_j$, forcing a unique competitor coordinate of loss $h_j$. If it does not match the anchor coordinate, the divisor bound saves $p^{-h_j/3}\le p^{-\lambda H/3}$. If it matches and peels off, it must occupy an order-$s_*$ slot (since $h_j\ge s_m(\sum g_i+\sum_{l<j}h_l)+G_0$ makes any order $\ge s_*+1$ slot exceed the RHS of $(*)$). Once all $n_*-1$ free coordinates peel off, $\nu'$ has used $n_*$ order-$s_*$ slots (so $\nu'_{a_*}=n_*$ by maximality of $n_*$), leaving $q'$ higher-order slots with orders $u_1(\nu')\le\cdots\le u_{q'}(\nu')$ satisfying
  $$
   \sum_{l=1}^{q'}u_l(\nu')e_l\ \le\ \sum_{i=1}^{m_*}u_i(\nu^*)g_{m_*+1-i}+e_{\rm prec}. \tag{$**$}
  $$
  Now peel the bounded coordinates downward for $j=m_*,\dots,1$. Inductively $u_i(\nu')=u_i(\nu^*)$ for all $i<m_*+1-j$, and since $\sum_{i\le j}y_i^d>0$ the competitor cannot have run out of coordinates, so pure lex-min gives $u_{m_*+1-j}(\nu')\ge u_{m_*+1-j}(\nu^*)$. Dividing the remaining $(**)$ by $u_{m_*+1-j}(\nu^*)$ gives $\sum e_l\le g_j+B_{j-1}<2g_j$, forcing a unique competitor coordinate $w_j=c/p^{g_j}$ of loss $g_j$. It must occupy a slot of order $u_{m_*+1-j}(\nu^*)$ (forcing $u_{m_*+1-j}(\nu')=u_{m_*+1-j}(\nu^*)$), because any strictly larger order exceeds the RHS of $(**)$ by at least $g_j-s_m\sum_{i<j}g_i-e_{\rm prec}>0$. The remaining competitor coordinates then have total unweighted loss $\le B_{j-1}$. By our inductive choice of $a_j$, $M=p^{dg_j}(\sum_{i<j}y_i^d-\sum_l w_l^d)=0$ is forced, hence $c=a_j$ and $w_j=y_j$ peels off. After $j=1$, any remaining competitor coordinates would have positive $d$-th power sum equal to $0$, impossible; hence $q'=m_*$, $\nu'=\nu^*$, and $w=y$ as multisets, which is already counted in the jump.
- **Small $B$, removed points, exponential sums.** Degree-$1$ competitors $\nu'\in T$ (which necessarily have order $o_1>s_*$ since $r_*\ge2$) number at most $O(p^{\frac{s_*}{o_1}H})=o(p^H)$ and are discarded directly. Competitors of degree $2\le j\le r$ satisfy $\alpha\ge\beta/j\ge\beta/r$, so the GF-11 margins $\sigma_r$ (for $r\ge3$, with $q\in\{4,\dots,r+1\}$, and $q=3$ with margin $1/12$ for $r=2$) apply with $q\le r+1\le d$ and Erdős–Turán cutoff $L_{\rm ET}=\lceil p^k H^{n_*+1}\rceil$ (giving $\sum_y L_{\rm ET}^{-1}\operatorname{Comp}'(I^+)=O(H^{n_*-3}p^H)=o(H^{n_*-1}p^H)$). The anchor loss is $k\le\kappa H$; the bounded part adds $O(1)$.
- **Main term and $L^1$ Lebesgue-point localization.** When $m_*\ge1$, fixed higher-slot coordinates $w_{\rm hi}$ with $u_0=S(w_{\rm hi})\in(1,p^d)$ leave $n_*<d$ order-$s_*$ slots, producing $H$-independent integrable power-law poles $(u-u_0)_+^{n_*/d-1}$ in the limiting competitor density (for example, for $P=X_1X_2$ at $p=3,d=3$, fixed intervals near $u_0=1$ have $I\cap G_H=\emptyset$ for all $H\ge4$). Thus GF-11 Lemma 2's uniform-$I$ hypothesis does not hold when $m_*\ge1$; instead we localize via an $L^1$ majorant.
  1. For any interval $I\subset K'$, discard competitors with $\nu'_{a_*}<n_*$ (at most $o(H^{n_*-1}p^H)$ globally). Among $\nu'\in T$ with $\nu'_{a_*}=n_*$, split by the weighted higher-slot sum $\sum o_j e_j$ at a cutoff $E_0=E_0(|I|)$: tuples with $\sum o_j e_j>E_0$ contribute $O(H^{n_*-1}p^H p^{-\eta_1 E_0})$ by convergence of $\prod\sum_{e_j}p^{e_j(1-o_j/s_*)}$; choose $E_0$ so $p^{-\eta_1 E_0}\le|I|$. For each of the finitely many remaining $w_{\rm hi}$, GF-11's $n_*$-dimensional lattice count on $I^+-S(w_{\rm hi})$ has error $O_{E_0}(H^{n_*-2}p^H)$ when $n_*\ge2$ and $O_{E_0}(1)=o(p^H)$ when $n_*=1$.
  2. Therefore, for every interval $I\subset K'$,
     $$
      \limsup_{H\to\infty}\frac{\operatorname{Comp}'(I^+)}{H^{n_*-1}p^H}\ \le\ C_P\int_I f(u)\,du,\qquad f(u):=1+\sum_{\substack{\nu'\in T\\ \nu'_{a_*}=n_*}}\sum_{w_{\rm hi}}p^{-\frac1{s_*}\sum o_j e_j}\frac{d}{du}\operatorname{Vol}_{n_*}\!\Big(\sum_{i=1}^{n_*}x_i^d\le(u-S(w_{\rm hi}))_+\Big).
     $$
     Because $n_*/d>0$ and $\prod_j\sum_{e_j\ge0}p^{e_j(1-o_j/s_*)}<\infty$, we have $f\in L^1(K')$.
  3. For each integer $M\ge1$, set $\epsilon_M=\min(\epsilon_0,c_1/M)$ with $c_1$ small enough that $2C_d\epsilon_M\cdot C_P M$ is at most half the centre-density constant. On every interval $I\subset K'$ with $\frac1{|I|}\int_I f\le M$, isolation holds for all $H\ge H_0(I,M)$, and reverse Fatou gives $|I\cap\limsup_H G_H(\epsilon_M)|\ge c_2\epsilon_M|I|$.
  4. As in GF-11 Lemma 2, no point of $\limsup_H G_H(\epsilon_M)$ is a Lebesgue density point of a level set $E=\{M_P=w\}$, so $|I\cap E|\le(1-c_2\epsilon_M)|I|$ whenever $\frac1{|I|}\int_I f\le M$. If $|E|>0$, choose $x_0\in E$ that is simultaneously a Lebesgue density point of $E$ and a Lebesgue point of $f\in L^1(K')$, and put $M=\lceil f(x_0)\rceil+1$: sufficiently small intervals $I$ around $x_0$ satisfy $\frac1{|I|}\int_I f\le M$, forcing $|I\cap E|/|I|\le1-c_2\epsilon_M<1$, a contradiction. Hence $|E|=0$.

This proves Theorem M. $\square$

**What the script shows about the proposed rule.**

1. *Smallest order on the largest loss.* Correct, by rearrangement. The leading jump of $X_1^2X_3+5X_1X_2^2$ at the centre $(3^{-1},a_2/9,m/27)$ is exactly $2\cdot3^{H+2g_1}$. The $X_1X_2^2$ term enters at valuation $H+g_1+h_1$.
2. *Pure lex-min tie-break.* Works across mixed degrees (unlike maximizing degree before lex-min, which fails for $X_1X_3^4+X_1X_2^2X_4$).
3. *Correction: bounded losses with inductively chosen numerators.* A fully dominant anchor with all losses growing puts the higher orders on losses of size $\asymp\kappa H$. The precision then rises by the excess $e=\sum(u_i-s_*)g_{\cdot}$, and the relevant competitors grow by $p^{e/s_*}$. At $H=16$, putting the order-$3$ slot of $X_1^2X_3$ on loss $H/4$ instead of loss $1$ multiplies the exact relevant count by $946>3^{H/2-2}$. Bounded losses keep the excess $O(1)$, and choosing their numerators $a_j$ sequentially avoids non-peeling $B=0$ coincidences.
4. *Correction: loss-$0$ coordinates can cancel.* Take $P=X_1X_2X_4-X_1X_3^2$ with orders $1,2,3,4$, both terms of depth $7$. At the centre $(1,1,z)$, both monomials contribute one tuple of weight $H$, so the leading jump is $1-1=0$. The exact jump has valuation $2H$, where the competitors of level $2H$ cannot be isolated. With bounded losses $g_1<g_2$, the weights become $v+2g_2+4g_1$ and $v+3g_2+3g_1$, and the jump is $p^{v+2g_2+4g_1}\ne0$.
5. *Mixed degrees.* For $X_1^3+7X_1X_2+11X_3$ with orders $1,2,3$, the target is $X_1^3$ ($n_*=3$, $m_*=0$, the GF-11 anchor). The jump is $6\cdot3^H$, nonzero modulo $3^{H+2}$. The other two monomials add only $O(p^H)$ and $O(p^{H/3})$ competitors.

The script computes these jumps exactly, with every relevant slot tuple near the centre enumerated. It also checks that no other relevant tuple sum coincides with the centre.

## 4. Denser all-prime families: the six costs

An *all-prime* family is $W=\sum_kc_kb^{-n_k}$, $c_k=u_k/(p^{e_k}\mu_k)$, such that every prime $\ell\nmid pb$ eventually divides the reduced denominators of the shifted prefixes of $W$. Write $\Lambda_K=\operatorname{lcm}_{k\le K}\mu_k$ and $A(L)=\operatorname{lcm}_{\ell\le L}(\ell-1)$. Phase 19 gives $\log A(L)\ll L\log\log L\log\log\log L/\log L$ ([Ford–Luca–Pomerance input](../phase19/grids.md#5-radices-selectable-depths-and-faster-insertions)).

| Cost | C1 ($2^{k^3}$) | Refined protected pole (§5) | Polynomial hybrid (§6) | Quasi-polynomial (§7) |
|---|---|---|---|---|
| Pole separation | Lemma 1, gap $\min(e_{k-1},e_k-e_{k-1})$ | Same | Atomless mass $M_r$, Theorem Q | Plateau estimate (3) of Phase 19 |
| Convolution collisions | at most $r$ runs per shell | at most $r$ runs per shell | $O(N^{r/d})$ insertions | $O(K^r)=N^{o(1)}$ insertions |
| Complementary order $\lambda$ | $O(\log k)$ | $\le\log_p\ell_k$ | $\le\log_p\ell_{\max}=o(\log K)$ | $O(\log\log K)$ |
| Complete periods | $\le q_n=e^{O(k^2)}$ | $\le tp^{re_k}\Lambda_k^{r-1}A(\ell_k)$ | $\le tp^{rsJ}\Lambda_K^r$ | $\le tp^{rsJ}\Lambda_K^r=N^{o(1)}$ |
| Real tail | $(\log N)^{r/3}b^{-H}$ | $(\log N)^rb^{-H}$ | $N^{(r-1)/d}b^{-H}$ | $N^{o(1)}b^{-H}$ |
| Boundary neighbourhoods | windows $[in_k,in_k+rn_{k-1}]$ | same | failed cells of $M_r\bmod p^L$ | $[jn_m,jn_m+rw_m]$ |

The script tabulates the gap between the primorial and $A(\ell_k)$ for the first $k$ off-radix primes. The values $(\log\text{primorial},\log A(\ell_k),k\log k)$ are $(517,141,461)$ at $k=100$, $(7828,1567,6908)$ at $k=1000$ and $(27254,4870,24019)$ at $k=3000$.

## 5. Dense introduction: one new prime per index

In Phase 20 C2a, the residual cost of a run is its period, not $q_n$. One has

$$
 \operatorname{ord}_{q_n}b\ \le\ t\,p^{re_k}\prod_{j\le k}\ell_j^{\,r-1}\,\operatorname{lcm}_{j\le k}\operatorname{ord}_{\ell_j}b\cdot\operatorname{ord}_{M'}b\ \le\ t\,p^{re_k}\Lambda_k^{\,r-1}A(\ell_k)\operatorname{ord}_{M'}b,
$$

because $\operatorname{ord}_{\ell^r}b\mid\ell^{r-1}\operatorname{ord}_\ell b$. So for squarefree $\Lambda_k$ (for general non-squarefree $m_j$ in C2a, replace $\Lambda_k^{r-1}$ by $\Lambda_k^r/\operatorname{rad}(\Lambda_k)$), (P$_r$) may be weakened to

$$
 (\mathrm P'_r)\qquad k\,p^{re_k}\Lambda_k^{\,r-1}A(\ell_k)=o(n_k),
$$

with the residual term in the C2a rate changed accordingly. Take $\mu_k=\ell_k$, the $k$-th prime not dividing $pb$, and $e_k=k\lceil\log\log(k+16)\rceil$. Then (D) and (G) hold, and $\log\Lambda_k=(1+o(1))k\log k$.

**Proposition 5.1.**

1. If $n_k=\lceil\exp(k(\log\log(k+16))^2)\rceil$, then $W$ is normal and Liouville, and every off-radix prime divides its prefix denominators from some point on.
2. If $n_k=\lceil\exp((r-1+\epsilon)k\log k)\rceil$ with $r\ge2$, then every $P(W)$ with $1\le\deg P\le r$ is normal and Liouville.
3. If $\log n_k/(k\log k)\to\infty$ and $n_{k+1}/n_k\to\infty$ (for example $n_k=\lceil\exp(k\log k\,\psi(k))\rceil$ with $\psi(k)\to\infty$ nondecreasing), then the conclusion of part 2 holds for all nonconstant $P$.

*Proof.* (S) ($n_{k+1}/n_k\to\infty$) holds in parts 1–2 directly and by hypothesis in part 3 (note that $\log n_k/(k\log k)\to\infty$ alone would allow staircase schedules violating (S)). In part 1, $\log A(\ell_k)\ll k\log\log k\log\log\log k$ and $e_k\log p=O(k\log\log k)$, both $o(\log n_k)$. In part 2, the exponent of the period bound is $(r-1)(1+o(1))k\log k+O(k\log\log k)$. Liouville needs $\log(p^{e_k}\Lambda_k)=o(n_k)$. $\square$

The proposed "exact threshold" $\exp(k\log^2k)$ is one admissible example of part 3. It is not a threshold, and for $W$ alone the requirement is much lower. Necessity is not proved for any degree. A lower bound for the period of $P(W)$ would need $\ell_j^r\mid q_n$ for older $j$, which can fail through cancellation; only the newest prime is controlled (Phase 20 C1 §3). It would also need $\operatorname{ord}_{\ell^r}b=\ell^{r-1}\operatorname{ord}_\ell b$, which fails at base-$b$ Wieferich primes. Unconditional control of those is not available.

## 6. The hybrid on a polynomial schedule

**Theorem H.** Let $s\ge1$, $r\ge1$ and $d>r(s+1)$. List the primes not dividing $pb$ as $\ell_1<\ell_2<\cdots$. Choose strictly increasing indices $k_j$ with $p\nmid k_j$ and $\log\Lambda_K=o(\log K)$, where $\Lambda_K=\prod_{k_j\le K}\ell_j$; for example $k_j=2^{2^{j-1}}$ when $p\ne2$. Put $\mu_{k_j}=\ell_j$, $\mu_k=1$ otherwise, and

$$
 W=\sum_{k\ge1}\frac{b^{-tk^d}}{p^{sv_p(k)}\mu_k}.
$$

1. Every off-radix prime divides the reduced shifted prefix denominators of $W$ from some point on. In fact $q_n=p^{s\lfloor\log_pK\rfloor}\Lambda_K$ exactly, where $K=\max\{k:tk^d\le n\}$.
2. For every $P\in\mathbb Q[x]$ with $1\le\deg P\le r$, $P(W)$ is normal in base $b$, and $D_N(P(W);b)\ll_P(\log\log N)^{-d/(d-1)}$ when $\deg P\ge2$.

*Proof.* (1) The index $k_j$ is the only one whose coefficient has $\ell_j$ in its denominator, and its numerator is an $\ell_j$-unit. For the $p$-part, the indices of top valuation $ap^{J}$, $a<p$, contribute $\equiv\#\{a\}\not\equiv0\bmod p$, because $b^{t(\cdot)}\equiv1$.

(2) *The $p$-adic part is unchanged.* At scale $J$, an auxiliary index has loss $J$, so a tuple containing it carries $p^{sJ}$ after normalization and vanishes modulo $p^L$. Hence $p^{rsJ}b^{-n}R_n\equiv AM_r(u)\pmod{p^L}$, exactly as for $C(b,p,s,d)$.

The hypothesis $p\nmid k_j$, or bounded $v_p(k_j)$, is essential. The proposed argument, that $\ell_j$ is a $p$-unit and so cannot pollute, is not enough. An auxiliary prime at an index $k$ with $v_p(k)=J$ multiplies the weights of loss-$0$ tuples by $\ell^{-1}\not\equiv1$, which changes the frozen residue throughout shell $J$. In the script, $\ell=5$ at index $27=3^3$ changes the residue of $W^2$ modulo $9$ at $J=3$.

*Failed shifts* have density $\ll(\log L)^{-d/(d-1)}$ by Theorem Q.

*Grid.* At the other shifts, $q_n=p^eQ$ with $e\ge rsJ-L+1$ and $Q\mid\Lambda_K^rM'$. The exact grid theorem gives $G\ge p^{e-a_0-\max_{\ell\mid Q}\log_p\ell-O(1)}\ge p^{rsJ-L}N^{-o(1)}$.

*Periods.* Choose $c_0$ small enough that $(c_0\log p)/s<r/d$ (as in [nonlinear-boundary.md §5](nonlinear-boundary.md#5-effective-discrepancy-and-what-blocks-more)). Then each period is $\le tp^{rsJ}\Lambda_K^r\operatorname{ord}_{M'}b\le N^{rs/d+o(1)}$, and there are $O(N^{r/d}+\log N\,L^{r-1}p^{L/s})=O(N^{r/d})$ runs. The residual cost is $N^{r(s+1)/d+o(1)}=o(N)$.

The tail and buffers are as in [nonlinear-boundary.md §5](nonlinear-boundary.md#5-effective-discrepancy-and-what-blocks-more). With $L=\lfloor c_0\log N\rfloor$ this gives the rate. For $\deg P=1$ the frozen residue modulo $p^{v_p(A)+1}$ is $A\lfloor u^{1/d}\rfloor$ with $1\le\lfloor u^{1/d}\rfloor<p$, so no shift fails (Phase 18), and the rate is $O_{P,\eta}(N^{-\eta})$ for every $\eta<\min(s/d,(d-s-1)/d)$ (due to $\Lambda_K=N^{o(1)}$). $\square$

The proposed bound "$t_{\rm comp}G\le\Lambda_Kp^{rsJ}$" is correct, but on its own it does not suffice. The complete-period budget also needs $d>r(s+1)$, because runs have length $N^{1-r/d}$ while $p^{rsJ}\asymp N^{rs/d}$. For $r+1\le d\le r(s+1)$, normality would need a short-orbit estimate that is uniform in the varying auxiliary modulus. The fixed-support kernel behind GF-11 does not provide this, so that range remains open.

## 7. All degrees on a quasi-polynomial schedule

**Theorem U.** Let $n_i=ti\lceil\exp((\log(i+1))^2)\rceil$, the universal schedule of [Phase 19 §2](../phase19/nonlinear.md#2-universal-polynomial-normality-with-consecutive-ratios-tending-to-one). Insert auxiliary primes $\ell_j$ at strictly increasing indices $k_j$ with $p\nmid k_j$ and $\log\Lambda_K=o((\log K)^2)$; for example $k_j$ the least integer $\ge e^j$ prime to $p$, for which $\log\Lambda_K\asymp\log K\log\log K$. Put $W=\sum_ip^{-sv_p(i)}\mu_i^{-1}b^{-n_i}$. Then $P(W)$ is normal for every nonconstant $P\in\mathbb Q[x]$, and every off-radix prime divides the prefix denominators of $W$ from some point on.

*Proof.* Three parts of Phase 19 §2 still hold.

- The plateau estimate (3). The limit $B(a)$ uses only indices of valuation $\ge v-O(1)$, and an auxiliary index contributes $p^{sv}\cdot(\text{unit})\to0$.
- The fixed-precision sparsification. Auxiliary indices have valuation $0<J-H$.
- The comparison with $p^{rsJ}F_l(U_{m-1},V_m)$. The last grid index has $v_p(m)\ge J-H\ge1$, so it is never auxiliary.

Hence $v_p(q_n)\ge rsJ-L+1$ off the discarded intervals, with $L$ fixed, and those intervals still have density zero. Phase 19 used the fixed-support all-prefix criterion for the transfer. Replace it with the prefix estimate and the exact grid theorem, discarding $n<\sqrt N$ (density $0$) so $1/G_n\to0$ uniformly across retained shifts:

- $q_n\mid p^{rsJ}\Lambda_K^rM'$ with $p^{rsJ}\le K^{rs}$ and $\Lambda_K=e^{o((\log K)^2)}=N^{o(1)}$, since $\log N\sim(\log K)^2$;
- $G\ge K^{rs-o(1)}$ (so $1/G_n\le\exp(-c\sqrt{\log N})$ for $n\ge\sqrt N$);
- there are $N^{o(1)}$ runs, each with period $N^{o(1)}$. $\square$

The bookkeeping indicates $D_N\ll_P\exp(-c_P\sqrt{\log N})$, dominated by the discarded intervals, whose relative size is $K^{-2p^{-H-1}}$. This is a sketch and is not claimed. The script shows the budget ratio $\log(\text{runs}\times\text{period})/\log n_K$ for $r=3$ falling: $1.29,0.77,0.45,0.26,0.14$ at $\log K=10,20,40,80,160$. Consecutive ratios satisfy $n_{i+1}/n_i\to1$, so the consecutive-gap Liouville proof no longer applies; whether $W$ is non-Liouville or has finite irrationality exponent is not proved by consecutive ratios alone and remains open here.

## 8. Where the primes can appear

The index schedules above are polynomial (§6) or quasi-polynomial (§7). The *positions* at which the $j$-th auxiliary prime may first appear are another matter.

| Construction | Position of the $j$-th prime |
|---|---|
| C1 | $2^{j^3}$ |
| §5, $W$ alone | $\exp(j(\log\log j)^2)$ |
| §5, degree $\le r$ | $\exp((r-1+\epsilon)j\log j)$ |
| §6 | $tk_j^d$ with $\log k_j\gg j\log j$, since $\log\Lambda_{k_j}=o(\log k_j)$ |
| §7 | $\exp(j^2)$ for the $k_j\approx e^j$ example (or $\exp(j\log j\,\psi(j))$ with $\log k_j=\sqrt{j\log j\,\psi(j)}$) |

In every complete-period construction of degree $\ge2$ the $j$-th prime appears at a position $n$ with $\log n\gg j\log j$. The reason is that a run must contain a period, and the period bound carries the factor $\prod_{i\le j}\ell_i^{r-1}$. For degree $1$, $A(\ell_j)$ replaces the primorial. Whether any method can introduce the primes earlier is open. A short-orbit theorem uniform over growing auxiliary support would be the natural input.

## 9. Exact checks

`python -B scripts/phase21_nonlinear.py` checks the following for C3–C4.

- **C3.** It enumerates every relevant slot tuple near each centre and verifies the exact jumps at eight tied centres. For $X_1^3+7X_1X_2+11X_3$ the jump is $6\cdot3^H$ modulo $3^{H+2}$, at four centres. For $X_1^2X_3+5X_1X_2^2$ it is $2\cdot3^{H+2g_1}$, at three centres. For $X_1X_2X_4-X_1X_3^2$, the leading jump cancels at the loss-$0$ centre (exact valuation $2H$) and is $3^{\pi-1}$ at the bounded-loss centre. It also gives the exact relevant-competitor counts for the excess comparison at $H=16$.
- **C4, denominators.** For the hybrid with $\ell_j$ at $k=2^{2^j}$ on $2k^5$, the reduced denominators $q_n=3^{\lfloor\log_3K\rfloor}\Lambda_K$ are exact at 12 random shifts.
- **C4, residues.** The 3-adic residues of $W^2$ and $C(2,3,1,5)^2$ agree at 8 shifts, and the auxiliary index $27$ pollutes.
- **C4, periods.** It computes exact denominators, depth defects and multiplicative orders of $W^2$ at $n=2K^5+7$.
- **C4, tables.** It prints the primorial versus $A(\ell_k)$ table and the quasi-polynomial budget.

These finite computations check the arithmetic mechanisms. The asymptotic statements rest on the written proofs.
