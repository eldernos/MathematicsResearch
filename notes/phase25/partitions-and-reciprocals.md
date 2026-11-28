# Partition constants and reciprocal discrepancy spectra

**Paper proof.** For every prescribed integer radix $b\ge2$ and every real $0\le\alpha\le1$, there is a positive irrational $x = x(b, \alpha) \in M_b$ (constructed computably whenever $\alpha$ is computable; parameter-dependent existence otherwise, with the witness depending on $b$) such that $D_N(1/x;b)\to\alpha$. For $0<\alpha<1$ the reciprocal orbit measures converge to $\alpha\delta_0+(1-\alpha)\lambda$, where $\lambda$ is normalized length on the circle. In particular, for each radix $b\ge2$, $1/\sqrt2$ occurs exactly via a radix-dependent witness $x(b, 1/\sqrt2)\in M_b$. Theorem E1 gives an elementary construction for dyadic radices. Theorem E1.2 uses coprime periods to handle every radix and prescribe the measure itself.

## Definitions and scope

Write $\|z\|=\min_{j\in\mathbb Z}|z-j|$, $T_bz=bz\bmod1$, and $\nu_N(z;b)=N^{-1}\sum_{n<N}\delta_{T_b^n z}$, where indices start at zero. For a circle probability $\nu$, let $D(\nu)=\sup_I|\nu(I)-|I||$, over half-open arcs. Taking complements gives the same supremum over ordinary intervals in $[0,1)$. Put $D_N=D(\nu_N)$, $M_N=\int\|t\|\,d\nu_N(t)$, $M_b=\{z:M_N(z;b)\to0\}$ and $K_b=\{z:D_N(z;b)\to1\}$. Concentration in an arbitrarily short arc around zero gives $M_b\subset K_b$. The set $\mathcal A_{\rm conv}(b)$ consists of the limits $D_N(1/x;b)$ for irrational $x\in K_b$. For a rational $v$, its cycle measure gives equal weight to the points of its eventual periodic orbit.

The results concern the four [standing objectives](../../docs/research-objectives.md). E1 gives exact spectra and kernel witnesses (Objectives 2 and 3), including the earlier normal endpoint (Objective 1). E2 distinguishes complete-period cancellation from a uniform incomplete-period estimate (Objectives 3 and 4). E3 and E4 give unconditional restrictions on the digits of two specific reciprocals and quantitative discrepancy gaps (Objective 3).

| Result | Scope | Evidence | Standing Objectives |
| --- | --- | --- | --- |
| Theorem E1 | $\mathcal{A}_{\mathrm{conv}}(2^e) = [0, 1]$ with witnesses in $M_{2^e}$ | `Paper proof` | Objectives 1, 2, 3 |
| Theorem E1.2 | $\mathcal{A}_{\mathrm{conv}}(b) = [0, 1]$ ($\forall b \ge 2$) via $\alpha\delta_0 + (1-\alpha)\lambda$ | `Paper proof` | Objectives 1, 2, 3 |
| Propositions E2.1–E2.3 | Prime-power grids, worst-start obstruction, averaged short-orbit mean square | `Paper proof` | Objectives 3, 4 |
| Theorem E3 | $X_{b,m}$ ($m \ge 3$): run bound, $\gg \log N$ transitions, $1 - D_N \gg (\log N)/N$ | `Paper proof` | Objective 3 |
| Theorem E4 | $P_b$ and $R_k^{(E)}$: run bound, $\gg \log\log N$ transitions, $1 - D_k(R_k^{(E)}; b) \gg (\log\log k)/k$ | `Paper proof` + `External input` (Euler pentagonal) | Objective 3 |

## E1. Reciprocal discrepancy spectra

### E1.1. A direct dyadic construction

**Theorem E1 (Paper proof).** $\mathcal A_{\rm conv}(2^e)=[0,1]$ for each $e\ge1$, with witnesses in $M_{2^e}$. For computable $0<\alpha<1$ the witness can be chosen computably.

We work in binary time. For a positive rational pair $u v=1$, take $a\ge0$ beyond both binary preperiods and write $P_u,P_v$ for their eventual binary periods (period one for a terminating number). Thus $2^a(2^{P_z}-1)z$ is integral. Maintain $\gcd(P_v,e)=1$. The cycle measure $\mu$ of $v$ is then the same on each progression of times modulo $e$, since addition of $e$ permutes the cycle transitively. Denote its discrepancy by $D$, and the binary cycle mean distance of $u$ by $B$.

We use the following elementary comparison throughout. If two probabilities can be coupled with circle distance at most $h$ outside mass $s$, then their discrepancies differ by at most $2h+s$, and their mean distances to zero differ by at most $h+s$. Enlarge a test arc by $h$ at each end, allowing the whole circle, and apply the same bound in reverse. Endpoints follow by enlargement by $h+\varepsilon$ and passage to the infimum. In particular a total-variation change of size $s$ changes discrepancy by at most $s$.

### Two rational operations

**Padding.** Fix $0<t<1/4$. Choose arbitrarily large $p<q<2p$ with

```math
 P_v\mid p,\qquad p\equiv1\pmod e,\qquad d=q-p\equiv0\pmod{eP_u},
 \qquad t\le\theta=d/q\le 2t .
```

The Chinese remainder theorem gives $p$ (for $e=1$ the congruence is empty). The allowed multiples for $d$ have fixed spacing, so one can even arrange $d/q\to t$ from above. Replace

```math
 v'=v\frac{1-2^{-p}}{1-2^{-q}},\qquad u'=1/v',\qquad
 u'-u=\frac{w}{2^p-1},\qquad w=u(1-2^{-d}).
```

The odd part of the denominator of $v'$ divides $2^q-1$. Its binary period divides $q$, which is coprime to $e$. Also $2^{a+d}w$ is an integer. These are exact finite-product identities.

For each fixed input and fixed $t$, the cycle of $v'$ can be coupled to

```math
 (1-\theta)\mu+\theta\delta_0
```

with both exceptional mass and displacement arbitrarily small as $p$ grows. Here are details for the cycle and for prefixes. Expand $v'=\sum_{i\ge0}2^{-iq}v(1-2^{-p})$. At $n=iq+r$, $0\le r<q$, earlier summands are integral for $r\ge a$, since $2^{a+p}v(1-2^{-p})$ is integral. On $a\le r<p-H$ the current term agrees with $2^r v$ on the circle to within $O(v2^{-H})$, including all later summands. On $p+a\le r<q-H$ the current term is integral and later summands are $O(v2^{-H})$. In a full block the omitted strips have length $O(a+H)$. Trimming at most $eP_v+O(e)$ times per fragment balances every sampled progression exactly. Consequently the cycle assertion holds by first choosing $H$ and then $p$. For **every** prefix of binary length $N\ge p$, on each progression the proportion in the zero pieces is $O_e(d/p)$, and the accumulated strips and trimming cost $O_e((a+H+P_v+1)/p)$. This follows by counting at most $N/q+1$ fragments of each kind and dividing by $N/e+O(1)$. Thus its sampled discrepancy differs from $D$ by $O_e(t)+o(1)$.

For $u'$, expand the difference as $w\sum_{i\ge1}2^{-ip}$. Outside the first $a+d$ times after each multiple $ip$ and the last $H$ times before it, all active summands are integral and the remaining tail is $O(u2^{-H})$. For all $N\ge p$ this costs $O((a+d+H+1)/p)$ in mean distance. The old prefix mean differs from $B$ by $O((a+P_u)/p)$. In particular the new cycle mean and all such prefix means are at most $B+O(t)+o(1)$. The constants multiplying $t$ here are absolute (or depend only on $e$ for progression counts). For $N<p$, the total displacement in either coordinate over $0\le n<N$ is $O((u+v)2^{N-p})$ by the geometric sum. All the little errors can be made as small as requested for the current input.

**Contraction.** Choose arbitrarily large $l$ divisible by both current periods, with $l>a$, and replace $v$ by $v^+=v(1+2^{-l})$ and $u$ by $u^+=u/(1+2^{-l})$. For $n\ge l+a$,

```math
 2^n v^+\equiv 2^{n+1}v\pmod1.
```

Thus the new reciprocal cycle is **exactly** $\mu$, with the same period. Before $l-H$ the sampled points track the old orbit to $O(v2^{-H})$. Only the strips $[0, a)$ and $[l - H, l + a)$ (at most $2a + H$ times) and at most two incomplete sampled cycles intervene, giving discrepancy $D+o(1)$ uniformly for $N\ge l$ on each progression as $l$ grows.

The denominator of $u^+$ divides $2^{2l}-1$ since $2^l$ clears the binary part and the old odd part divides $2^l-1$. In the first band $0\le r<l$, $2^r u^+=2^ru-2^ru/(2^l+1)$. In the second,

```math
 2^{l+r}u^+=2^r(2^l-1)u+2^r u/(2^l+1).
```

The first term on the right is integral for $r\ge a$. The sum of geometric errors per band is at most $u$. The new cycle mean is at most $B/2+O((a+P_u+u+1)/l)$. For any prefix $N\ge l$, the whole or partial first bands cost at most their lengths times $B$ plus $O(a+P_u+u+1)$ each, and the second bands cost only that error. Hence every such prefix mean is at most $B+o(1)$. Prefixes before $l$ obey the same geometric displacement bound as before padding, with $l$ in place of $p$.

### Steering the actual discrepancies

Start with a positive periodic rational $v$ of period coprime to $e$ and discrepancy less than $\alpha$. For example, take a binary cyclic de Bruijn word of order $h$, append fewer than $e$ zeros to make its length $1\bmod e$, and repeat. Such a cycle exists by an Euler circuit on binary words of length $h-1$, with one edge per length-$h$ word. The original cycle has exactly one point per binary cylinder of length $2^{-h}$, giving discrepancy at most $2^{1-h}$. At most $h+e$ starting positions are inserted or change their length-$h$ word, so the new discrepancies tend to zero. Set $u=1/v$.

At stage $j\ge1$, with actual cycle discrepancy $D_j<\alpha$, choose a rational

```math
 (\alpha-D_j)/16<t_j<(\alpha-D_j)/8.
```

Pad with this $t_j$, then contract once. Choose the padding scale so the discrepancy and mean-distance errors of its full-cycle mixture comparison are each at most $2^{-j}t_j$. Choose all other selectable prefix and cycle errors at most $2^{-j}$. Since the contraction preserves the actual reciprocal cycle, $D_{j+1}\le D_j+2t_j+2^{-j}t_j<\alpha$. If $L_j=\int\|z\|\,d\mu_j(z)$, then

```math
 L_{j+1}\le(1-\theta_j)L_j+2^{-j}t_j,\qquad t_j\le\theta_j\le2t_j.
```

If $\sum t_j=\infty$, the product of $1-\theta_j$ on every infinite tail vanishes. Iterating and using the summable error tail would give $L_j\to0$. Markov's inequality on the complement of a small arc about zero would give $D_j\to1$, contradicting $D_j<\alpha<1$. Therefore $t_j\to0$, hence $D_j\to\alpha$. The two cycle mean bounds give $B_{j+1}\le B_j/2+O(t_j)+O(2^{-j})$, so $B_j\to0$.

For clarity about the infinite limit, list the operation scales as $s_i=p_1,l_1,p_2,l_2,\ldots$. Each change in either real coordinate is $O(2^{-s_i})$ uniformly: take $s_i\ge i+3$, so both products and their inverses stay in a fixed compact subinterval of $(0,\infty)$. Choose $s_{i+1}>2s_i$ at each free choice. For $s_i\le N<s_{i+1}$ the real limits track the rational pair just after operation $i$ at time $n<N$ to within $C2^{n-s_{i+1}}$ on the circle. Outside the final $\lceil\sqrt N\rceil$ times this is $O(2^{-\sqrt N})$; the discarded fraction tends to zero on each progression. The uniform prefix estimates for operation $i$ now apply even when $N$ is close to the next scale. The binary mean of the limiting $x$ tends to zero, hence so does its mean on the progression $n\equiv0\pmod e$ by nonnegativity. Taking binary prefix lengths $eN$ proves the asserted base-$2^e$ discrepancy for its reciprocal.

At each contraction one may require $2^{-l}\operatorname{den}(v)<1/j^2$ for the rational immediately before it. The contraction changes $v$ by exactly $v2^{-l}>0$; choose the next scale large enough that the sum of all later changes is less than half this. If the limit had denominator $Q$, its nonzero distance from that rational would be at least $1/(Q\operatorname{den}(v))$, a contradiction as $j\to\infty$. This proves irrationality even for rational targets. All finite cycle comparisons can be made with rational arithmetic and strict slack by enumeration. A computable target allows strict rational choices of $t_j$; the geometric tails give a computable real. At $\alpha=0$ the all-base normal reciprocal construction is [GF-34, Theorem 5](../phase23/convergent-reciprocals-and-schedules.md). At $\alpha=1$, use just the binary contractions starting from $u=v=1$. The same mean contraction, zero reciprocal cycle, prefix bounds and irrationality argument apply. This finishes the proof.

**Attribution and boundary.** GF-34 introduced the synchronized plus-factor contraction for a fixed rational cycle. [GF-38, C1.1–C1.4](../phase24/partitions-and-reciprocal-spectra.md) proved dyadic density, the non-dyadic gcd obstruction, and loss of leading multipliers for unreset cyclotomic products. Padding changes the rational cycle itself, and the estimate uses the exact identity for $u'-u$. No unreset multiplier recursion is assumed. For general $b$, doubling need not preserve a radix cycle. The proof above uses the binary shift and coprimality with $e$ at exactly this point. The next proof replaces this identity by an average over independent pairs.

### E1.2. Independent pairs from two coprime periods

**Theorem E1.2 (Paper proof; Objectives 1–3).** For $b\ge2$ and $0<\alpha<1$ the orbit law $\alpha\delta_0+(1-\alpha)\lambda$ is realized by $1/x$ with an irrational $x\in M_b$. The construction is computable for computable $\alpha$. Together with the endpoints this gives $\mathcal A_{\rm conv}(b)=[0,1]$ in every radix. Every cylinder whose closure misses zero has limiting frequency $(1-\alpha)b^{-L}$ for a word of length $L$. Every length-$L$ word has lower frequency at least $(1-\alpha)b^{-L}$, so these reciprocals are disjunctive and nonnormal.

Let $C,F>0$ be rational reciprocals whose eventual base-$b$ periods $P_C,P_F$ are coprime. A terminating number has period one. Fix a common preperiod bound $a$, so $b^a(b^{P_z}-1)z$ is integral for $z=C,F$. For a small prescribed ratio $0<r<1/3$ take arbitrarily large $m,d$ with

```math
 P_C\mid m,\quad P_F\mid d,\quad \gcd(m,d)=1,\quad
 \rho=d/m\longrightarrow r.
```

For instance choose $L\ge2$ coprime to $P_C$, put $d=(LP_F)^k$, and take $m=P_C(1+j LP_F)$ closest to $d/r$ with $j\ge0$. Write $q=m+d$. The reciprocal pair is updated **exactly** by

```math
 C'=C\,\frac{1-b^{-m}}{1-b^{-q}},\qquad
 F'=F\,\frac{1-b^{-q}}{1-b^{-m}}
     =F+\frac{w}{b^m-1},\qquad w=F(1-b^{-d}).
```

Here $b^{a+d}w$ is an integer. The new periods divide $q$ and $\mathrm{lcm}(m,P_F)$, respectively: on the cut side $b^{a}(b^q-1)C'$ is integral; on the folded side use the displayed sum of two rationals. These period bounds are coprime, as $P_F\mid d$. Thus the operation can be repeated with either coordinate as $C$.

**Cycle comparison.** Denote the old cycle laws by $\sigma,\mu$ on the cut and folded coordinates. With the actual $\rho$, their new laws admit couplings arbitrarily accurate in mass and circle displacement to, respectively,

```math
 \frac{1}{1+\rho}\sigma+\frac{\rho}{1+\rho}\delta_0,\qquad
 (1-\rho)\mu+\rho(\mu*\mu).
```

Here $\mu*\mu$ is the distribution of the sum modulo one of two independent points of law $\mu$. On **every** prefix $N\ge m$, each empirical law can instead be coupled to its own old cycle with exceptional mass $O(\rho)+o(1)$ and displacement $o(1)$; the coefficient of $\rho$ is absolute. The selectable errors tend to zero with the scale, for fixed input and prescribed $r$.

*Proof of the comparison.* The cut-side expansion and estimates are the padding proof with radix $b$, $p=m$, and $e=1$. For the folded side expand $F'-F=w\sum_{j\ge1} b^{-jm}$. Write $n=im+s$, $0\le s<m$, and first take $i\ge1$. For $m>d+a$, earlier terms are integral. The future tail is $O(F b^{s-m})$. The current term is $b^sF-b^{s-d}F$, which is integral for $s\ge d+a$. For $a\le s<d-H$, the folded point therefore tracks

```math
 b^{im+s}F+b^s F \pmod 1
```

to within $O(Fb^{-H})$. For $d+a\le s<m-H$ it tracks $b^{im+s}F$ to the same accuracy. Use $P_F$ consecutive complete $m$-blocks after the preperiod, a multiple of the new period. For each fixed $s\ge a$, $i$ runs through a whole residue system modulo $P_F$, and $\gcd(m,P_F)=1$. Thus the first summand traverses exactly $\mu$ independently of the value of the second summand. Over a multiple of $P_F$ consecutive $s$'s, the second summand also traverses exactly $\mu$. Discarding strips of width $O(a+H+P_F)$ per block therefore proves the convolution formula with the claimed coupling. For a prefix, discard the entire exceptional portion $s<d+a$ in each block $i\ge1$ and the last $H$ times. In the first block only the future tail occurs. There are at most $1+N/m$ blocks; the surviving samples can be compared with the actual old orbit and its prefix law, which has at most $a+P_F$ unmatched times. This proves the uniform bound. In both coordinates choose $H$ first, then $m$. These estimates account for all rational tails before making the next update.

**Iteration.** Start from $x_0=y_0=1$, with period one in both coordinates (taking $m_1 \ge 4$ so every step has nontrivial scale). Set $h_j=1/(j+8)$. In round $j$ first cut $y$ and fold $x$ with ratio $\rho_A=\alpha h_j+O(h_j^2)>0$, then cut $x$ and fold $y$ with ratio $\rho_B=h_j+O(h_j^2)$. Choose each ratio within $h_j^2$ of its target (and positive), with scales more than twice their predecessors. All subsequent references to $x,y$ at a finite step mean the rational pair after the indicated update.

If $B_j$ is the cycle mean distance of $x$ at the start of a round, subadditivity of circle distance and the two cycle comparisons yield

```math
 B_{j+1}\le\frac{1+\rho_A}{1+\rho_B} B_j+O(h_j^2)
 =\bigl(1-(1-\alpha)h_j+O(h_j^2)\bigr)B_j+O(h_j^2).
```

Here and below choose the selectable errors at most $h_j^2$, with further restrictions given next. Since $\sum h_j=\infty$ and $\sum h_j^2<\infty$, iteration gives $B_j\to0$; the intermediate cycle means tend to zero as well.

For a fixed positive integer frequency $k$, write $z=\int e^{2\pi i k t}\,d\mu(t)$ for the coefficient of the old $y$ cycle. Put $c=\rho_A/(1+\rho_A)$, $h=\rho_B$. The ideal two-step map on this coefficient is

```math
 z_A=(1-c)z+c,\qquad T(z)=(1-h)z_A+h z_A^2,\qquad
 1-T(z)=(1-c)(1-z)(1+h z_A).
```

We spell out precision choices because $z=1$ is another fixed point. For $1\le k\le j$ with old $z\ne1$, choose the first comparison error in that coefficient at most $h_j^2 |1-z|^2/100$. Also require the prime-to-$b$ denominator of the **actual** new $y$ to exceed $j$. This is feasible: writing the old $y=A/(b^a B)$ with $B$ prime to $b$ (increasing $a$ if needed), the numerator in $y'=A b^{d}(b^m-1)/(b^a B(b^q-1))$ cancels at most $A(b^m-1)$ out of $b^q-1$. The remaining denominator grows at least as $(b^q-1)/(A(b^m-1))\to\infty$. Consequently its cycle coefficient $\widetilde z_A\ne1$ for every $1\le k\le j$: equality requires every point to have $k t$ integral, which for reduced prime-to-$b$ denominator $D$ holds if and only if $D \mid k$ (making $z \neq 1 \iff D \nmid k$ explicitly decidable). In the second comparison require error at most $h_j^2 |1-\widetilde z_A|^2/100$ for all these frequencies. The exact factor $1+h\widetilde z_A$ has magnitude at least $1-h$. Thus after the fold all these coefficients still differ from one. For each fixed $k$ the two-step recurrence from the next round onward satisfies

```math
 z_{\rm next}=T(z)+O(h_j^2 |1-z|^2).
```

Indeed $|1-\widetilde z_A|\le2|1-z|$, and the polynomial fold map on the unit disk is Lipschitz with constant $1+h$. Arbitrarily accurate couplings give the simultaneous finite precision requirements since $|e^{2\pi i k u}-e^{2\pi i k v}|\le 2\pi k\|u-v\|$. They can be imposed with rational comparisons: any nontrivial phase of denominator $D$ in a cycle of length $P$ gives $1-\Re z\ge 8/(P D^2)$ by $1-\cos(2\pi t)\ge8\|t\|^2$.

For $W=1/(1-z)$, the factorization and the error just proved imply

```math
 W_{\rm next}=\frac{W}{(1-c)(1+h z_A)}+O(h_j^2)
   =\bigl(1-(1-\alpha)h_j\bigr)W+h_j+O\bigl(h_j^2(1+|W|)\bigr).
```

For the first equality both denominators $1-z_{\rm next}$ and $1-T(z)$ have magnitude $\gg |1-z|$ for all large $j$. For the second use $c=\alpha h_j+O(h_j^2)$, $h=h_j+O(h_j^2)$, $|z_A-z|\le2c$, and $zW=W-1$. Taking absolute values first gives boundedness: for large $j$ the coefficient of $|W|$ is at most $1-(1-\alpha)h_j/2$ and the additive term is $O(h_j)$. Subtract $1/(1-\alpha)$ and iterate the resulting contraction with summable $O(h_j^2)$ errors. This gives $W\to1/(1-\alpha)$, hence $z\to\alpha$. The intermediate coefficients have the same limit since the cut changes them by $O(h_j)$.

All positive Fourier coefficients therefore tend to $\alpha$; the negative coefficients are conjugates and the zeroth is one. By uniform density of trigonometric polynomials in continuous circle functions, the $y$ cycle measures converge weakly to $\mu_\alpha=(1-\alpha)\lambda+\alpha\delta_0$. At each step the all-prefix comparison above has error $O(h_j)+o(1)$. Choose its selectable errors at most $h_j$. At binary or general radix scale $s_i=m_i$ the pair changes in real absolute value by $O_b(b^{-s_i})$ with a uniform constant because both products stay bounded above and away from zero by summability. For $s_i\le N<s_{i+1}$ discard the final $\lceil\sqrt N\rceil$ times as in E1: all remaining limiting orbit points track the pair after step $i$ to $O_b(b^{-\sqrt N})$. This proves weak convergence on **all** prefixes and $x\in M_b$.

Weak convergence here also gives discrepancy convergence despite the atom. Partition the circle into arcs of diameter at most $\varepsilon$ with endpoints avoiding the atom. Their masses converge individually; match mass within each arc leaving $o(1)$ unmatched. The arc comparison in E1 gives discrepancy error at most $2\varepsilon+o(1)$. Since $D(\mu_\alpha)=\alpha$ by shrinking an arc about zero, the prescribed limit follows. The exact word frequencies use continuity sets of $\mu_\alpha$. Exhausting each cylinder interior by closed subarcs with endpoints avoiding zero gives the lower frequency for every word. The positive Lebesgue component excludes eventual periodicity, so both limits are irrational. For a computable $\alpha$, rational approximations to the prescribed ratios, the rational error bounds above and a geometric tail modulus give a computable construction. Trigonometric approximation (Stone–Weierstrass on $\mathbb{T}$) identifies the limiting measure without requiring a convergence rate.

For $\alpha=0$ one can take the first ratio strictly between $h_j^2/2$ and $h_j^2$ in every round. It is positive, activates all the same harmonics, and equals $0\cdot h_j+O(h_j^2)$ as required by both recurrences. They give $B_j\to0$ and $W\to1$, hence a normal reciprocal. The earlier GF-34 Theorem 5 supplies this endpoint with an effective discrepancy rate for its own schedule. For $\alpha=1$ its Theorem 1 applies with rational seed $1$ (the congruence modulo one is empty); equivalently iterate the displayed contraction of E1 with $b$ in place of $2$ starting from integers, for which the reciprocal cycle remains zero. This finishes the every-radix spectrum.

## E2. A complete period and its worst starting point

Let $m_1<m_2<\cdots$ be positive integers, $S_k=\sum_{j\le k}m_j$, $Q_k=\prod_{j\le k}(b^{m_j}-1)$, $R_k=b^{S_k}/Q_k$, and $T_k=\operatorname{ord}_{Q_k}(b)$, with order one modulo one. The reciprocal of the minus-factor product is $R=\lim R_k$. All these fractions are reduced.

**Proposition E2.1 (Paper proof; Objectives 3 and 4).** For every $b\ge3$, every prime $p\mid b-1$ and every such schedule, the complete cycle of $A/Q_k$, for **every** unit numerator $A$, is an average of uniform shifted grids of size at least

```math
 p^{\max(0,k v_p(b-1)-v_p(b^2-1))}.
```

Its discrepancy is bounded by the reciprocal grid size. If $m_{k+1}\ge(1-o(1))T_k$ on an infinite subsequence, then $D^-(R;b)=0$. Consequently a convergent discrepancy for this simple product under that hypothesis must be zero, whatever declared target sequence one attaches to the stages.

*Proof.* Write $Q_k=p^E Q'$, $p\nmid Q'$, $H=\mathrm{lcm}(2,\operatorname{ord}_{Q'}b)$, $t=\max_{j\le k}v_p(m_j)$ and $c=v_p(b-1)$. For any prime $s\mid Q'$, the order modulo $s$ divides some $m_j$; lifting to $s^a$ multiplies the order by a power of $s$, by the kernel of reduction of the unit group. Hence $v_p(\operatorname{ord}_{Q'}b)\le t$. We have $E\ge kc+t$: every term contributes at least $c$ and the exponent with valuation $t$ contributes at least $c+t$. Also $g=v_p(b^H-1)\le v_p(b^2-1)+t$. For these valuation facts use the binomial expansion: raising $1+p^v u$ with $p\nmid u$ to a power prime to $p$ preserves $v$, and raising it to $p$ adds one for odd $p$ or $v\ge2$ at $p=2$. For the lower bound the first squaring of an odd $b$ adds at least one. For the upper bound apply the exact lifting rule to $(b^2)^{H/2}$, since $H$ is even.

Modulo $p^E$, the powers of $b^H$ exhaust the classes $1\bmod p^{\min(E,g)}$: lifting gives order $p^{\max(0,E-g)}$, the cardinality of that set. Modulo $Q'$ all are one. By the Chinese remainder theorem the subgroup, and each of its unit multiples, is an arithmetic grid modulo $Q_k$ with spacing $Q'p^{\min(E,g)}$. Partition the orbit into these cosets. Counting points of a shifted uniform grid in any arc proves the discrepancy bound.

The product inequality $1-\prod(1-a_i)\le\sum a_i$ for $0\le a_i\le1$ gives $0<R-R_k\le C_b b^{-m_{k+1}}$ (all factors are included at most once, so $R\le P_b<\infty$). At $N=\min(m_{k+1},T_k)$ the mean circle displacement is $O_b(1/N)$ by a geometric sum. Deleting $T_k-N=o(T_k)$ points changes the complete-cycle law by $o(1)$ in total variation. Now $T_k\to\infty$ by the grid bound. The comparison in E1 and Markov's inequality give the assertion. This extends the prime-power grid argument of GF-34 §5.4 from the consecutive schedule to arbitrary exponent spacing in $b\ge3$.

**Proposition E2.2 (Paper proof; Objective 4).** Let $Q\ge2$ be coprime to $b$, $L=\lfloor\log_b Q\rfloor$. For $0\le h<L$,

```math
 D_N(1/Q;b)\ \ge\ \frac{\min(N,L-h)}{N}-b^{-h}.
```

Indeed, for $0\le n<L-h$, $b^n/Q<b^{-h}$. Thus a discrepancy estimate tending to zero **uniformly over unit numerators**, or uniformly over starts on the actual cycle of $R_k$, requires $N/\log_b Q_k\to\infty$ as $Q_k,N\to\infty$. Take $h=\lfloor\sqrt L\rfloor$ on any subsequence with bounded ratio. The start with numerator one occurs at time $-S_k\bmod T_k$. In particular, for $m_j\asymp a^j$, $a>1$, one has $\log_b Q_k=S_k+O_b(1)\asymp m_{k+1}$. Even perfect complete-period cancellation cannot yield a start-uniform normality estimate on that window. This obstruction is sharp in its initial zero count: the first powers $b^n/Q<b^{-h}$ are given exactly by $n<\log_b Q-h$ before reduction. It does not assert sufficiency above that length.

**Proposition E2.3 (Paper proof; Objectives 3 and 4).** Fix $b\ge3$ and an integer harmonic $a\ne0$. For $W_a(N;z)=N^{-1}\sum_{n<N}\exp(2\pi i a b^nz)$, let $G=p^{\max(0,E-g)}$ be the actual grid size from E2.1 and put $J=\operatorname{ord}_{G/\gcd(G,|a|)}b$. For any $N\ge1$, on the **single cycle of the actual product** one has

```math
 \frac1{T_k}\sum_{s<T_k}|W_a(N;b^sR_k)|^2
 \le\frac{\sum_{r\bmod J}\#\{i<N:i\equiv r\bmod J\}^2}{N^2}
 \le\frac1N+\frac1J .
```

For $N\le J$ the mean square is **exactly $1/N$**. Thus on any prescribed lengths $N_k\to\infty$, even subperiodic lengths $N_k=o(\log Q_k)$, the proportion of starts with $D_{N_k}(b^sR_k;b)>\varepsilon$ tends to zero for each $\varepsilon>0$. E2.2 nevertheless exhibits a bad start for all these latter lengths.

*Proof.* Expand the square and average first over $s$. Each pair $i,j$ contributes the complete-cycle Fourier coefficient at $a(b^i-b^j)$. The geometric sum on each grid vanishes unless $G\mid a(b^i-b^j)$, equivalently $J\mid i-j$. Diagonal terms are exactly one, all other terms have absolute value at most one, and each residue class contains at most $N/J+1$ indices. This proves the inequalities and the equality range. By E2.1, $G\to\infty$; for fixed nonzero $a$, the orders $J\to\infty$ since bounded orders would force unbounded moduli to divide one fixed product of the integers $b^j-1$. Markov's inequality gives convergence to zero in proportion for each Fourier coefficient. For clarity, for any $\varepsilon>0$ there exist $H,\eta>0$ such that a probability with its first $H$ coefficients bounded by $\eta$ has discrepancy at most $\varepsilon$. Otherwise compactness gives a weak limit with all nonzero coefficients zero, hence length measure, contradicting the arc-partition comparison in E1.2. Apply the finite union bound. This argument locates the remaining incomplete-orbit problem at the actual unshifted numerator; it makes no random-start assumption about that numerator.

**Conditional.** A numerator-specific estimate $D_{m_{k+1}}(R_k;b)=o(1)$ transfers to those prefixes of $R$ by the geometric sum above. Full normality requires control between them, for instance the uniform bound $\sup_{m_k\le N\le m_{k+1}}D_N(R_k;b)=o(1)$. No such short-orbit bound is used here. GF-38 C2.3 proves $\liminf k^{-1}\log\log T_k\ge\log(1+\theta)$ under $m_k\ge T_{k-1}^{\theta}$ eventually, for fixed $\theta>0$. E1 uses different factors and makes no period-growth claim for these minus-factor schedules.

## E3 and E4. Digit transitions forced by reciprocal approximants

The radix digits are the canonical digits $d_1,d_2,\ldots$ obtained by flooring. A run after $n$ means that $d_{n+1},\ldots,d_{n+h}$ are all equal. Define $F_b=(b-1)^{-1}\mathbb Z/\mathbb Z$. We use distance from the **entire** fixed-point set, $\|(b-1)t\|/(b-1)$; this detects a departure from any long constant run in every radix.

**Reciprocal separation lemma (Paper proof).** Suppose $V>0$, $Z=1/V$, $U=A/b^s>0$, $\gcd(A,b)=1$, $A>b-1$, $U$ ranges in a compact subinterval of $(0,\infty)$, and $|U-V|\le C b^{-s-g}$. There is a constant $c$ depending only on these bounds and $b,V$ such that, for every integer $n \ge 0$ with $n+c\le g$,

```math
 \|(b-1)b^n Z\|\ \ge\ 1/(2A).
```

In fact $(b-1)b^{n+s}/A$ is nonintegral, with distance at least $1/A$. The reciprocal error multiplied by $(b-1)b^n$ is at most $(b-1)C b^{n-s-g}/(UV)$, hence at most $1/(2A)$ once $b^{g-n}\ge2(b-1)C/V$. This proves the claim. If the next $h$ digits are all $d$, the orbit differs from $d/(b-1)$ on the circle by at most $b^{-h}$ by summing the common digits. Thus $h\le s+O(1)$. Moreover some $j\in[n,n+s+O(1)]$ has $\|(b-1)b^j Z\|\ge1/(2b)$: as long as the norm is smaller, multiplication by $b$ multiplies it by exactly $b$.

**Theorem E3 (Paper proof; Objective 3).** Let $b\ge2,\ m\ge3$, $Y_{b,m}=\prod_{i\ge0}(1-b^{-m^i})$ and $X_{b,m}=1/Y_{b,m}$. Every constant run of $X_{b,m}$ after position $n$ has length at most

```math
 \frac{m}{m-2}n+O_{b,m}(1).
```

There are $\gg_{b,m}\log N$ digit transitions among its first $N$ digits and $\gg_{b,m}\log N$ times $j<N$ at distance at least $1/(2b(b-1))$ from $F_b$. In particular $1-D_N(X_{b,m};b)\gg_{b,m}(\log N)/N$.

*Proof.* Truncate the product before $m^k$ ($k \ge 2$), obtaining $U=A/b^s$ with $s=(m^k-1)/(m-1)$ and $A=\prod_{i<k}(b^{m^i}-1)$ prime to $b$. The next term and a geometric tail give $|U-Y_{b,m}|\le b^{-m^k}/(1-b^{-1})$. The compactness condition holds because the full product is positive. Here $g=m^k-s=(m-2)s+1$. The least sufficiently large $k$ with $g\ge n+c$ gives $s\le mn/(m-2)+O_{b,m}(1)$, since $s_k=ms_{k-1}+1$. Apply the separation lemma. Starting at any sufficiently large $n$, a transition and an escape from $F_b$ each occur by $C_{b,m}n$. Disjoint geometric windows give the counts.

For discrepancy we use the finite bound $1-D_N(z;b)\ge(2/5)\min_{c_0\in F_b}M_N(z-c_0;b)-1/N$, proved in [GF-32, Lemma 5.3](../phase23/binary-partition-and-carry-complexity.md). Its hypotheses are any real $z$, integer radix $b\ge2$, and $N\ge1$. As $c_0$ is fixed by $T_b$, each escape contributes at least $1/(2b(b-1))$ for every $c_0$. This gives the claimed gap.

The endpoint $s$ and the empty interval up to $m^k$ come from the signed support of the same Mahler product that gives the top-digit cluster interval $[1-1/m,1-1/(m(m-1))]$ for $Y_{b,m}$ in [Phase 24, Theorem 1.6](../phase24/simple-normality-and-word-laws.md). Its generating function satisfies $Y(z)=(1-z)Y(z^m)$; reciprocation generates the counts $b_m(n)$ of partitions into powers of $m$. GF-38 C3 proves automaticity of $b_m(n)\bmod m^L$ for fixed $L$ and identifies the carry at the right edge of a digit window. The separation proof retains the integer numerator $A$ of the product truncation. It needs neither a digit automaton for $X_{b,m}$ nor a hypothesized transfer of digit frequencies.

In fact the signed orbit recurrence here has an explicit first error term. With $A,s$ as in E3 and $M=m^k$,

```math
 b^{M-s}(A X_{b,m}-b^s)=1+O_b(b^{-M}).
```

Indeed $A X_{b,m}/b^s=\prod_{j\ge k}(1-b^{-m^j})^{-1}$. The first factor is $1+b^{-M}+O_b(b^{-2M})$ and the subsequent factors give $1+O_b(b^{-mM})$ by the product tail inequality. Since the integer $A$ is the product of $b^{m^i}-1$, expanding it gives a signed relation among $2^k$ binary-subset shifts of the radix orbit of $X_{b,m}$. The scaled distance can thus be read directly from the Mahler product even when its ordinary digit frequencies are unknown.

**Theorem E4 (Paper proof; Objective 3).** Set $E_b=\prod_{j\ge1}(1-b^{-j})$, $P_b=1/E_b$, $R_k^{(E)}=\prod_{j=1}^k(1-b^{-j})^{-1}$. Every constant run of $P_b$ after $n$ has length at most

```math
 \tfrac38 n^2+O_b(n+1).
```

There are $\gg_b\log\log N$ digit transitions ($N \ge 3$) and as many times away from $F_b$ by at least $1/(2b(b-1))$ before $N$. On the actual initial orbit of the rational approximant (starting numerator $b^{k(k+1)/2}$, $k \ge 3$),

```math
 1-D_k(R_k^{(E)};b)\gg_b\frac{\log\log k}{k},
 \qquad
 1-D_N(P_b;b)\gg_b\frac{\log\log N}{N}.
```

*Proof.* Euler's pentagonal number theorem gives
$E_b=1+\sum_{i\ge1}(-1)^i(b^{-i(3i-1)/2}+b^{-i(3i+1)/2})$. Take the truncation through $s=i(3i+1)/2$ ($i \ge 2$). Its numerator modulo $b$ is $(-1)^i$. The next exponent is $s+2i+1$, so $g=2i+1$ and the constant in the tail bound can be $1/(1-b^{-1})$. The truncations tend to a positive product. For $i=\lceil(n+c)/2\rceil$ large enough, $s=3n^2/8+O_b(n+1)$. The lemma gives the run bound and an escape by $n+s+O_b(1)$. Each interval $[n,C_bn^2]$ for large $n$ contains each type of event. Starting a new interval just beyond the last right endpoint gives $\gg_b\log\log N$ disjoint intervals by $N$, since the logarithms of their left endpoints grow at most geometrically.

The same finite discrepancy inequality as in E3 applies. For the rational orbit, the product tail gives $0<P_b-R_k^{(E)}\le P_b b^{-k}/(b-1)$. Therefore $\sum_{j<k} b^j|P_b-R_k^{(E)}|\le P_b/(b-1)^2$. The distance to each fixed point is 1-Lipschitz, so the total distance to that point on the rational prefix loses at most this constant. This proves the rational bound at precisely $N=k$. The argument transfers distances; equality of all $k$ radix digits would also require cylinder-boundary margins. The quadratic asymptotic $\log T_k^{(E)}=(1/2-3/\pi^2)k^2\log b+O_b(k\log^2 k)$ and the earlier Weyl characterization are GF-38 C4.2 and C4.4. The present bound uses the numerator at the prescribed start, independently of the complete-period estimate.

**External input.** Euler's pentagonal number theorem is used in E4 at $z=1/b$, inside its disk of absolute convergence. A reference is G. E. Andrews, *The Theory of Partitions*, chapter 1. E1.2 and E2.3 use classical trigonometric approximation on the compact circle (the Stone–Weierstrass theorem, applied to the conjugation-closed algebra of trigonometric polynomials containing constants and separating points), together with weak\* compactness of probability measures on $\mathbb{T}$ and the Portmanteau theorem for continuity sets. The finite discrepancy inequality and the normal endpoint cited above are earlier repository paper results. GF-38 invokes Bugeaud–Corvaja–Zannier for multiplicatively independent $b$ and $2$; E1 does not use that estimate. Any priority claim for the constructions in E1–E4 is provisional pending specialist literature review.

## Reproduction and outstanding questions

**Finite certificate.** From the repository root run

```sh
python -B scripts/phase25_partitions_reciprocals.py
```

The script checks rational padding, its terminating inverse correction, periodic discrepancy on sampled progressions, contraction on both bands, the multiplicities of every pair in the coprime-period convolution, prime-power grid cosets, combinatorial collision counts for the mean-square diagonal range, initial-zero intervals, and two-sided bounds on the actual Mahler and Euler values and their short orbits. Floors and ceilings round outwards; all comparisons use integers or fractions. Both the Windows invocation above and the same script streamed to Hail's Python 3 exited 0. The runs checked 15 dyadic pads, a composed 936-position contraction, 15 coprime-period updates across bases 2, 3, 4, 5 and 10, 16 product denominators, 152 reciprocal-separation instances and 16 actual Euler windows (the conservative lower bound `(2/5) lower/k - 1/k` is strictly positive on the 4 largest `b = 2, 3` windows `k = 64, 128` and vacuous on the remaining 12 smaller windows).

**Finite measurement.** The reported transition counts in certified 256-digit binary prefixes (`X(2, 3)`: `131`, `X(2, 4)`: `138`, `X(2, 5)`: `146`, `P(2)`: `111`) are descriptive finite measurements only. Neither these counts nor any finite orbit discrepancy establishes a limit. No floating-point measurements enter the proofs or the certificates.

**Open.**

1. Which further invariant orbit measures are attainable by a reciprocal with input in $M_b$? Theorem E1.2 settles all scalar discrepancy targets, including non-dyadic density. Attainment by the more restrictive product of single factors $1-b^{-m_j}$ at intermediate targets remains open outside E2.1's hypothesis.
2. Does a strictly increasing minus-factor schedule with sub-doubly-exponential period growth give $x\in M_b$ and a normal reciprocal? E2.2 rules out a numerator-uniform proof on geometric schedules. Cancellation at the particular start $S_k\bmod T_k$ remains unresolved.
3. Determine simple normality, digit automaticity or a positive limiting discrepancy gap for $X_{b,m}$. The long-run restriction allows transition density zero. The exact discrepancy limits of the unreset GF-38 C1.2b products are also open.
4. Does the ordinary partition reciprocal have a positive lower density of escapes from $F_b$, or $D^+(P_b;b)<1$? E4 supplies growing counts; their proven proportion tends to zero. No benchmark classification follows from these finite-scale lower bounds.

The proofs here have paper-proof status. Cross-model review is not independent human peer review.
