# Dyadic Stoneham classification: the least orbit order in every degree, a p-adic descent hierarchy, degree 128 and exact plateau spectra

Throughout, $b\ge3$ is an odd integer and $\alpha=\alpha_{b,2}=\sum_{j\ge1}2^{-j}b^{-2^j}$. Put $s=v_2(b^2-1)-1\ge2$. For $d\ge1$ and real $t$ the leading mass $M_d(t)$ is the 2-adically convergent sum of $2^{v_1+\cdots+v_d}$ over all $v\in\mathbb N^d$ with $\sum_i2^{-v_i}\le t$. It is an integer, and on the shell $1\le t<2$ it is the leading coefficient of the shifted prefix of $\alpha^d$. If $M_d$ has no zero on $[1,2)$, then $P(\alpha)$ is normal in base $b$ for every rational polynomial $P$ of degree $d$. This uses the Phase 14 transfer, under the same conditional Lean step as Phase 16. Write

```math
G(d)=\sum_{k=1}^{d}\lfloor\log_2k\rfloor=(d+1)R-2^{R+1}+2\qquad(2^R\le d<2^{R+1}).
```

A multiset of deficits is a finitely supported $c=(c_i)_{i\ge0}$, where $c_i$ coordinates equal $i$. Put $|c|=\sum_ic_i$, $K(c)=\sum_ic_i2^{-i}$ and $\Phi(c)=\sum_i\bigl(ic_i-v_2(c_i!)\bigr)$. The orbit of $c$ contributes $\binom{d}{c_0,c_1,\dots}2^{\sum_iic_i}$ to $M_d(t)$ when $K(c)\le t$, a term of 2-adic order $v_2(d!)+\Phi(c)$. [Phase 16 note](../phase16/dyadic-stoneham.md) · [Quadratic denominators](../phase14/quadratic-denominators.md) · [Plateau spectrum](../phase14/plateau-spectrum.md) · [Checker](../../scripts/phase17_dyadic_stoneham.py)

**Theorem 1 (least orbit order in every degree; paper proof).** For every $d\ge1$,

```math
\min\{\Phi(c):|c|=d,\ K(c)<2\}=G(d).
```

Write $2^r-1\le d\le2^{r+1}-2$ and $j=d-2^r+1$. For $j\ge1$ the minimum is attained by exactly two multisets, $\{(r-1)^{2^r-1-j},r^{2j}\}$ with $K=2-2^{1-r}$ and $\{(r-1)^{2^r-j},r^{2j-1}\}$ with $K=2-2^{-r}$. For $j=0$ it is attained only by $\{(r-1)^d\}$.

This proves the identity $F(d)=G(d)$ and the two-orbit structure conjectured in Phase 16 (B.4, open boundary 3) for all $d$. The proof is a short slack decomposition (§A1.1). The same argument gives the exact minimum for every Kraft budget $2^a$ (Theorem 3).

**Corollary 2 (least loss; nonvanishing on an interval of length about $1/d$, uniformly in $d$).** For every $d\ge2$, with $r,j$ as above, the minimum of $v_2(M_d(t))$ over $t\in[1,2)$ is $v_2(d!)+G(d)$. It is attained exactly on $J_d=[2-2^{1-r},\,2-2^{-r})$ if $j\ge1$, and on $J_d=[2-2^{1-r},2)$ if $j=0$. In particular $M_d$ has no zero on $J_d$, for every $d$.

**Theorem 4 (p-adic cyclic descent; paper proof).** Let $p$ be an odd prime and let $e,k\ge1$. Let $r\ge2k-2$, with $r\ge1$ when $k=1$. Put $Z_k=2^{p^{k-1}}$, and for $t\in[1,2)$ let $y=2^jt/p^{\,r-k+1}\in[1,2)$. Then

```math
M_{ep^r}(t)\equiv Z_k^{\,ep^{k-1}j}\,M^{(Z_k)}_{ep^{k-1}}(y)\pmod{p^k},
```

where $M^{(z)}_n$ is the leading mass with the weight 2 replaced by $z$ (§A1.6). The right side does not depend on $r$. For $k=1$ this is the Phase 16 cyclic descent. For $k=2$ the twisted masses vanish modulo $p^2$ at explicit cells for $(e,p)=(2,3),(2,5),(4,3),(3,5),(3,7),(3,11)$. So second-order descent certifies none of these pairs, including the even case $e=2$ that first-order descent cannot reach.

**Certificates 5 (exact finite computations).**

1. *Nine new infinite families.* The pairs $(3,65537)$, $(4,65537)$, $(3,131071)$, $(4,131071)$, $(3,524287)$, $(4,524287)$, $(5,524287)$, $(3,2^{31}-1)$ and $(4,2^{31}-1)$ are good: $M_e$ never vanishes modulo $p$ on $[1,2)$. Hence every rational polynomial of degree $ep^r$ ($r\ge0$) for these pairs has a normal value at $\alpha$. They include the first family with $e=5$ beyond $p=e$, namely $5\cdot524287^r$, and four new even families $4\cdot p^r$. The pairs $(5,8191)$, $(5,131071)$ and $(6,8191)$ are bad, with exact witnesses.
2. *Degree 128.* $M_{128}(t)\ne0$ for every $t\in[1,2)$. The maximal loss 906 is first attained at $t=1+2^{-5}+2^{-6}+2^{-7}+2^{-17}$, the least loss is $776=v_2(128!)+G(128)$, and the partition has 345 leaves. So **every rational polynomial of degree 128** has a normal value at $\alpha$. This is the first certified power of two $2^r$ with $r\ge7$.
3. *Global zero sets for $3\le a\le64$.* For each such $a$, the zero set of $M_a$ on $(0,\infty)$ is $[a-\tfrac12,a)$ if $a$ is even and empty if $a$ is odd. The top interval is a paper proof (Proposition 6). The rest is certified for every middle state of the digit automaton.

**Theorem 7 (resonant quadratics: exact plateau spectra; paper proofs from the kernel-checked plateau law).** Let $x=(A\alpha^2+B\alpha+C_0)/D$ with integers $A\ne0$, $B$, $C_0$, $D\ge1$ and $\gcd(D,b)=1$. Let $q_k=2^{h_k}$ be the upper-shell denominators. The three parts are proved as Theorems 10, 12 and 13 and Proposition 14 in Part A2.

1. For $X^2-2X$ the plateau point of shell $k$ is $\{-Z_kb^{2^{k-1}}/2^{2k-1}\}$, with the integers $Z_1=2-2b^2$ and $Z_{k+1}=2+2b^{2^k}(Z_k-1)$.
2. Let $D=1$ and $H=\liminf_kh_k$. If $b\equiv1\pmod4$, then exactly $\limsup_ND_N(x)=2^{-2-[H-s]_+}$. For every odd $b$, $\limsup_ND_N(x)=1/4$ if and only if $h_k\le v_2(b-1)$ for infinitely many $k$. For $X^2-2X$ this condition reads $v_2(Z_k)\ge2k-1-v_2(b-1)$ infinitely often.
3. In general the possible plateau cycles form an explicit finite union of classes for each $h$. This gives unconditional bounds strictly below Phase 14's $1/4$. For example, $\limsup_ND_N\bigl((\alpha^2-2\alpha+C_0)/3\bigr)\le\tfrac14\bigl(1-\tfrac1{3\cdot2^{v_2(b+1)}}\bigr)<\tfrac14$ for every $b\equiv2\pmod3$ and $C_0\not\equiv1\pmod3$. This is the exact supremum over admissible cycles. Also $\limsup_ND_N\bigl((\alpha^2-2\alpha)/9\bigr)\le5/72$ for $b=5$ (exact enumeration).

**Theorem 8 (joint normality from pivot degrees; paper proof).** Let $P_1,\dots,P_m\in\mathbb Q[X]$ be **linearly independent over $\mathbb Q$** and let $V\subset\mathbb Q[X]$ be their span. Assume every pivot degree of an echelon basis of $V$ is resolved (§A3.1) or equal to 2. If 2 is a pivot, assume also that 1 is not a pivot and that the degree-2 element is non-resonant. Then $(P_1(\alpha),\dots,P_m(\alpha))$ is jointly normal in base $b$.

**What remains open.** Nonvanishing of $M_d$ on $[1,2)$ for all $d\ge3$ remains open. Beyond degree 128, only the descent families are known. Normality of $\alpha^2-2\alpha$ for any fixed $b$ is also open. §A1.5–A1.8 and the failed-approach list record precisely where each tried invariant breaks.

## 0. Status of the results

| Result | Status | Evidence in the checker |
| --- | --- | --- |
| Theorem 1: $F(d)=G(d)$ and the exact minimizers | Paper proof | Slack identity on 2745 random multisets; dynamic programme and complete minimizer lists for $d\le300$ |
| Theorem 3: every Kraft budget $2^a$ | Paper proof | Dynamic programme for $a\le7$, $d\le150$; the explicit minimizers |
| Corollary 2: least loss, its location, nonvanishing on $J_d$ | Paper proof (Theorem 1 + Phase 16 Proposition B.6) | Exact integers at five or six points for $3\le d\le40$; Phase 16 tables $d\le120$; $d=128$ |
| Proposition 6: top automaton state | Paper proof | Exact integers, $a\le12$ |
| Middle states zero-free, $a\le64$; global zero sets | Finite certificate + Proposition 6 | Branch and bound: $a\le32$ by default (465 states), $a\le64$ with `--middle-max 64` (1953 states) |
| Lemma 9: odd twists never vanish; mod-3 reformulation | Paper proof | $K_U(-1)$, $K_U(3)$ odd at every cut with at most $d$ ones in positions $\le8$, $d\le7$ |
| Theorem 4: $p$-adic descent | Paper proof | 64 exact congruences for $k=2$ |
| Failure of $k=2$ for six pairs | Exact witnesses | Twisted masses modulo $p^2$; $M_{18}(27/16)\equiv0\pmod9$, $M_{75}(75/64)\equiv0\pmod{25}$ |
| Nine new good pairs; three new bad pairs | Finite certificate over $\mathbb F_p$ / exact witnesses | Exhaustive vector orbits; deterministic primality test; integer $M_e(y)\equiv0\pmod p$ |
| Minimized certificates; observable ranks | Finite computation | Intertwining identities over $\mathbb F_p$; ranks modulo $2^{61}-1$ |
| $M_{128}\ne0$; degree-128 normality | Finite certificate + Phase 14 transfer | Branch and bound at the sharp precision 907 (`--degree-128`); exact integers at the witness and the least-loss point (default) |
| Maximal-loss mechanism | Finite computation | Exact integers at the first maximal-loss point, $d\le60$ |
| Cycle point formula (Theorem 7.1 = Theorem 10) | Paper proof (Lean identity of Phase 16) | Direct rational prefixes, 28 cases |
| Discrepancy of dyadic cycles (Proposition 11) | Paper proof | 14,336 exact cycles |
| Exact $\limsup$ for $D=1$; attainment criterion (Theorem 7.2 = Theorem 12) | Paper proof from the Lean plateau law | Same cycle data |
| Admissible-cycle classification and bounds (Theorem 7.3 = Theorem 13) | Paper proof + exact finite enumeration | Tables of §A2.3; the residue sequences against direct prefixes |
| $D=3$, $b\equiv2\pmod3$: exact supremum $1-1/(3\cdot2^{v_2(b+1)})$ (Proposition 14) | Paper proof | Exact enumeration for every $b<100$, $C_0\in\{0,2\}$ |
| Theorem 8: joint normality | Paper proof (Weyl + per-degree theorems) | Echelon examples |

## Part A1. The leading mass

### A1.1 Proof of Theorem 1

Fix $c$ with $|c|=d$ and $K(c)<2$, and let $I$ be its top level. For $D\ge0$ put

```math
N_D=\sum_{i\le D}c_i,\qquad A_D=\sum_{i\le D}c_i2^{D-i},\qquad S_D=\sum_{i>D}\left\lfloor\frac{c_i}{2^{\,i-D}}\right\rfloor .
```

*Step 1 (three rewritings).* Since $i$ is the number of $D\ge0$ with $D<i$, we have $\sum_iic_i=\sum_{D\ge0}(d-N_D)$. Since $\lfloor\log_2k\rfloor$ counts the $D\ge0$ with $2^{D+1}\le k$, we have $G(d)=\sum_{D\ge0}\max(0,d+1-2^{D+1})$. Legendre's formula gives $v_2(c_i!)=\sum_{m\ge1}\lfloor c_i/2^m\rfloor$. The Kraft condition gives $c_i\le2^{i+1}-1$, so only $m\le i$ contribute. Reindexing by $D=i-m$ gives $\sum_iv_2(c_i!)=\sum_{D\ge0}S_D$.

*Step 2 (slack decomposition).* Combining the three,

```math
\Phi(c)-G(d)=\sum_{D\ge0}\bigl(\sigma_D-S_D\bigr),\qquad
\sigma_D=\min\bigl(d-N_D,\ 2^{D+1}-1-N_D\bigr).
```

*Step 3 ($\sigma_D\ge S_D$).* First, $d-N_D=\sum_{i>D}c_i\ge S_D$. Second, multiplying $K(c)<2$ by $2^D$ gives $A_D+\sum_{i>D}c_i2^{D-i}<2^{D+1}$. So the integer $2^{D+1}-A_D$ exceeds the integer $S_D$, and $2^{D+1}-1-N_D\ge2^{D+1}-1-A_D\ge S_D$, because $N_D\le A_D$. Hence $\Phi(c)\ge G(d)$.

*Step 4 (equality).* Equality forces $\sigma_D=S_D$ for every $D$. For $D<I$ the first branch is strict, because $d-N_D-S_D\ge c_I-\lfloor c_I/2\rfloor>0$. So the second branch must be an equality. That needs $A_D=N_D$, which means no deficit below $D$, together with $2^{D+1}-1-A_D=S_D$. At $D=I-1$ only the levels $I-1$ and $I$ remain. With $x=c_{I-1}$ and $y=c_I$ the condition reads $x+\lfloor y/2\rfloor=2^I-1$. At $D=I-1-m$ with $m\ge1$ it reads $\lfloor x/2^m\rfloor+\lfloor\lfloor y/2\rfloor/2^m\rfloor=2^{I-m}-1$. This holds automatically. Indeed $x$ and $\lfloor y/2\rfloor$ sum to $2^I-1$ without carries, so their binary digits are complementary. Conversely every such pair attains equality.

Solve $d=x+y=2^I-1+\lceil y/2\rceil$ with $y\ge1$ and $0\le x\le2^I-1$. The choice $I=r$ gives $y\in\{2j,2j-1\}$ and needs $j\ge1$. The choice $I=r-1$ forces $j=0$, $x=0$ and $y=d$. Every other $I$ is impossible. For $I=0$ the only case is $d=1$ with $c=\{0^1\}$. This is exactly the list in Theorem 1. ∎

Phase 16 recorded that natural relaxations fail. Charging each run of equal deficits the slack of its own sorted positions already breaks for one deficit-1 coordinate followed by four deficit-2 coordinates. Charging each dyadic level $D$ by its Kraft slack, as $S_D$ does, closes the argument exactly. Phase 16 had already verified $F(d)=G(d)$ for $d\le299$ by a dynamic programme. The checker repeats it to $d=300$ and confirms the complete minimizer lists. It also confirms the slack identity, with every $\sigma_D\ge S_D$, on 2745 random multisets.

### A1.2 Every Kraft budget

**Theorem 3 (paper proof).** For $a\ge0$ and $d\ge0$,

```math
\min\{\Phi(c):|c|=d,\ K(c)<2^a\}
=\sum_{k=1}^{d}\bigl[\lfloor\log_2k\rfloor+1-a\bigr]_+\;-\;\sum_{i=1}^{a-1}\min\Bigl(\Bigl\lfloor\frac d{2^i}\Bigr\rfloor,\ 2^{a-i}-1\Bigr).
```

For $2^{I+a-1}\le d<2^{I+a}$ the right side equals $I(d+1)-2^{I+a}+a+1$. For $d<2^a$ it equals $-v_2(d!)$.

*Proof.* The argument of A1.1 runs with $2^{D+a}$ in place of $2^{D+1}$. Now $c_i<2^{i+a}$, so Legendre's sum also contains the terms $S_{-i}=\sum_l\lfloor c_l/2^{l+i}\rfloor$ for $1\le i\le a-1$. Each is at most $\lfloor d/2^i\rfloor$, and also at most $2^{a-i}-1$, because $K(c)/2^i<2^{a-i}$. This gives the lower bound.

For the matching construction with $d\ge2^a$, choose the odd integer $y=2(d-2^{I+a-1})+1\ge1$ (so $\lceil y/2\rceil=d-2^{I+a-1}+1$ and $\lfloor y/2\rfloor=d-2^{I+a-1}$). Put $x=2^{I+a-1}-1-\lfloor y/2\rfloor=2^{I+a}-1-d\ge0$ and $c=\{(I-1)^x,I^y\}$. Then $K(c)<2^a$. The complementary digits of $x$ and $\lfloor y/2\rfloor$ give $\Phi(c)=I(d+1)-2^{I+a}+a+1$. For $d<2^a$ take $c=\{0^d\}$. ∎

The case $a=1$ is Theorem 1. The case $a=0$ gives $\sum_{k\le d}(\lfloor\log_2k\rfloor+1)$, the total length of the binary expansions of $1,\dots,d$. The bound applies to every automaton state $(a',n)$ with $n+1\le2^a$, because those cuts lie below $2^a$. It reproves the Phase 16 closed form, which had been checked for $a\le7$ and $d<200$, for all $a$ and $d$. The checker compares with the dynamic programme for $a\le7$ and $d\le150$.

### A1.3 Where the least loss sits: Corollary 2

By Phase 16, Proposition B.6, $M_d(t)$ is the 2-adically convergent sum of the orbit contributions with $K(c)\le t$. The contribution of $c$ has order $v_2(d!)+\Phi(c)$. Write $V=v_2(d!)+G(d)$.

- For $t<2-2^{1-r}$ no minimizer lies in $U_t$, so every contribution, and the sum, has order at least $V+1$.
- On $J_d$ exactly one minimizer lies in $U_t$, so the order is exactly $V$.
- For $j\ge1$ and $t\in[2-2^{-r},2)$ both minimizers lie in $U_t$. Their contributions are $2^V$ times odd integers, so the sum has order at least $V+1$.

This proves Corollary 2. ∎

It recovers the Phase 16 least-loss column for every $d\le120$. It also recovers $776$ for $d=128$. The checker confirms the exact valuation at five or six points on and off $J_d$ for every $3\le d\le40$.

Two consequences follow. First, in every degree where $M_d$ is zero-free, the largest leading denominator on shell $k$ (for $k\ge2L_d$) is exactly $2^{dk-v_2(d!)-G(d)}$. It is attained precisely for $n/2^k\in J_d$. Second, $M_d\ne0$ on $J_d$ for **every** $d$. This is the first nonvanishing statement on an interval of $[1,2)$ valid in every degree. It covers only an interval of length at least $2^{-r}$ ($2^{1-r}$ when $j=0$), about $1/d$. Phase 16 §B.6 explains why partial nonvanishing does not suffice for normality.

### A1.4 Automaton states and the global zero set

State $(a,n)$ of the Phase 16 automaton is the function $f\mapsto M_a(n+f)$ on $[0,1)$. The shell is state $(a,1)$. State $(a,0)$ is the shell rescaled, since $M_a(t)=2^{aj}M_a(2^jt)$ for $t<1$.

**Proposition 6 (top state; paper proof).** For $a\ge1$ and $f\in[2^{-W-1},2^{-W})$ with $W\ge0$,

```math
M_a(a-1+f)=(-1)^a-1-a\bigl(2^{W+1}-2\bigr),\qquad M_a(a-1)=(-1)^a-1+2a .
```

So the top state vanishes exactly on $[a-\tfrac12,a)$ when $a$ is even. It never vanishes when $a\ge3$ is odd.

*Proof.* A tuple outside $U_t$ with $t\ge a-1$ has at least $a-1$ zero coordinates. Indeed $z$ zeros give a Kraft sum at most $z+(a-z)/2$. Summing $2^{|v|}$ over the complement gives the formula. ∎

**Certificate.** For $3\le a\le64$ and $1\le n\le a-2$, branch and bound at precision $\lfloor1.6\,a\log_2a\rfloor+30$ leaves no zero residue on $[n,n+1)$. The truncation is after $a-s_2(n)$ one-bits of $f$, the binary weight bound for sums of $a$ powers of two. The largest loss among middle states is that of the shell, 395 at $a=64$. Within each degree, the loss decreases roughly with $n$.

Together with Proposition 6 and the rescaling, this gives the global zero set for $3\le a\le64$: $\{t>0:M_a(t)=0\}$ equals $[a-\tfrac12,a)$ for even $a$ and is empty for odd $a$. For $a=2$ it is $\bigcup_{j\ge0}2^{-j}[3/2,2)$.

**Conjecture A.** For every $a\ge3$, the zero set of $M_a$ on $(0,\infty)$ is $[a-\tfrac12,a)$ if $a$ is even and empty if $a$ is odd.

Conjecture A strengthens the principal target, which is the shell state $n=1$. It is the natural induction hypothesis for the zero-count recurrence $M_a(n+f)=\sum_mC(a,m)2^{a-m}M_{a-m}(2(n-m)+c+f')$, which feeds every state into lower ones. The top states then carry the only zero cells, and those are explicit. The recurrence still involves cancellation, as §A1.8 shows, so the conjecture is a target, not a proof.

### A1.5 Parity of odd twists and the mod-3 reformulation (where invariants of type (i) fail)

Let $K_U(z)\in\mathbb Z[z]$ be the orthant numerator of the upper set $U_t$, so $M_d(t)=(-1)^dK_{U_t}(2)$. For an integer $z$ with $1-z$ invertible where needed, put $M^{(z)}_d(t)=K_{U_t}(z)/(1-z)^d$.

**Lemma 9 (paper proof).** For $d\ge1$ and $t>0$, $K_{U_t}(1)=1$. Hence $K_{U_t}(z)$ is odd for every odd integer $z$, and the twisted masses $M^{(z)}_d(t)$ with odd $z\ne1$ never vanish. Since $2\equiv-1\pmod3$, we have $M_d(t)\equiv(-1)^dK_{U_t}(-1)\pmod3$.

*Proof.* A tuple outside $U_t$ has a Kraft sum above $t$, so some coordinate is at most $\lceil\log_2(d/t)\rceil$. The complement lies in finitely many slabs $\{v_i\le c\}$, whose Hilbert series have pole order at most $d-1$. So $(1-z)^dF_{U_t}(z)\to1$ as $z\to1$. Finally $K(z)\equiv K(1)\pmod2$ for odd $z$. ∎

This is the precise reason why positivity and parity invariants of the automaton cannot exclude zero cells. They see $K_U$ at odd arguments. At the even argument $z=2$, for $t<d$ (in particular $d\ge2$ on $[1,2)$) one only gets $K_U(2)\equiv K_U(0)=0\pmod2$. The reduction modulo 3 is the reduction of the never-vanishing $z=-1$ twist, and it does vanish. Among cuts with at most $d$ ones in positions $\le8$, the checker finds residues $0\bmod3$ for $d\in\{2,4,5,6,7\}$, for example $M_4(1)=2304\equiv0\pmod3$. It finds none for $d=3$, in line with the trivial good pair $(3,3)$.

More generally, if $\operatorname{ord}_p2=m$, then $M_d\bmod\mathfrak p$ equals $\pm K_U(\zeta_m)\bmod\mathfrak p$ for a prime $\mathfrak p\mid p$ of $\mathbb Z[\zeta_m]$. Since $K_U(1)=1$, we get $K_U(\zeta_m)\equiv1$ modulo the ideal $(1-\zeta_m)$. That ideal is the unit ideal unless $m$ is a prime power $\ell^k$, and then it lies above $\ell\ne p$, because $m\mid p-1$. So the congruence carries no information modulo $\mathfrak p$.

### A1.6 The p-adic cyclic descent hierarchy (Theorem 4) and its failure at second order

*Proof of Theorem 4.* Let $C_{p^r}$ rotate the $e$ blocks of length $p^r$ simultaneously, as in Phase 16. Tuples outside $\mathrm{Fix}(\rho^{p^{k-1}})$ lie in orbits of size at least $p^k$. So $F_{U_t}(z)\equiv\sum_{\mathrm{Fix}}z^{|v|}\pmod{p^k}$ coefficientwise. A fixed tuple repeats each block's first $p^{k-1}$ entries $p^{r-k+1}$ times. Its Kraft sum is $p^{r-k+1}\sum2^{-w}$ over $ep^{k-1}$ free entries, and its weight is $z^{p^{r-k+1}|w|}$. Hence, as polynomials modulo $p^k$,

```math
K_{U_t}(z)\,\bigl(1-z^{p^{r-k+1}}\bigr)^{ep^{k-1}}\equiv(1-z)^{ep^r}\,K_{U'}\bigl(z^{p^{r-k+1}}\bigr),\qquad U'=U^{(ep^{k-1})}_{t/p^{r-k+1}} .
```

Evaluate at $z=2$. The factor $1-2^{p^{r-k+1}}\equiv-1\pmod p$ is a unit. The order of 2 modulo $p^k$ divides $p^{k-1}(p-1)$, so $2^{p^m}\bmod p^k$ is constant for $m\ge k-1$. That gives $Z_k$ once $r\ge2k-2$. Finally, $t/p^{r-k+1}<1$, so the cut rescales to $y$ through $M^{(Z)}_n(x)=Z^nM^{(Z)}_n(2x)$ for $x<1$. ∎

The checker verifies 64 congruences for $k=2$. Here $(e,p,r)$ runs over $(1,3,2),(2,3,2),(2,3,3),(3,3,2),(4,3,2),(1,5,2),(2,5,2),(1,7,2)$, against exact integers $M_{ep^r}(t)$ with $d\le54$. It also checks $2^{p^{r-1}}\equiv2^p\pmod{p^2}$ for $p\le13$ and $2\le r\le5$.

**Second order fails.** Call $(e,p)$ $k$-good if $M^{(Z_k)}_{ep^{k-1}}$ has no zero modulo $p^k$ on $[1,2)$. Then every degree $ep^r$ with $r\ge2k-2$ has no zero cell. A first-order good pair is good at every order, so the hierarchy only helps for bad pairs. It does not help for these:

| $(e,p)$ | cell $y$ with $M^{(2^p)}_{ep}(y)\equiv0\pmod{p^2}$ | independent check at $r=2$ |
| --- | --- | --- |
| $(2,3)$ | $9/8$ | $M_{18}(27/16)\equiv0\pmod9$, $M_{18}(27/16)\ne0$ |
| $(2,5)$ | $1+2^{-6}$ | |
| $(4,3)$ | $9/8$ | |
| $(3,5)$ | $15/8$ | $M_{75}(75/64)\equiv0\pmod{25}$, $M_{75}(75/64)\ne0$ |
| $(3,7)$ | $1+2^{-1}+2^{-8}+2^{-9}$ | |
| $(3,11)$ | $11\cdot\frac{9135223889}{2^{33}}$ rescaled to $[1,2)$ | |

These are divisibilities, not zeros of $M_d$ (degrees 18 and 75 are certified zero-free). They show that $M_{ep^r}(t)\equiv0\pmod{p^2}$ at the corresponding cells for every $r\ge2$. In exploratory sampling the second-order zeros occur on the first-order zero cells at roughly the frequency $1/p$, as for random residues. So we expect no finite order to certify a bad pair. That expectation is not proved.

### A1.7 First-order descent: new good pairs and minimized certificates

The first-order search of Phase 16 used primes below $10^5$ with $\operatorname{ord}_p2\le25$. The checker exhausts the reachable vectors of the degree-$e$ automaton over $\mathbb F_p$ for the Fermat prime $65537$ ($\operatorname{ord}=32$) and the Mersenne primes $2^{17}-1$, $2^{19}-1$ and $2^{31}-1$. Primality is checked by a deterministic Miller–Rabin test.

| $(e,p)$ | reachable vectors | | $(e,p)$ | reachable vectors |
| --- | ---: | --- | --- | ---: |
| $(3,65537)$ | 1,953 | | $(4,65537)$ | 59,263 |
| $(3,131071)$ | 631 | | $(4,131071)$ | 11,422 |
| $(3,524287)$ | 781 | | $(4,524287)$ | 15,750 |
| $(5,524287)$ | 338,544 | | $(3,2^{31}-1)$ | 2,017 |
| $(4,2^{31}-1)$ | 65,367 | | | |

None of these orbits contains the value 0. The bad pairs come with witnesses $y$ for which the exact integer $M_e(y)$ is nonzero and divisible by $p$:

- $(5,8191)$ at $y=1051265/2^{20}$;
- $(5,131071)$ at $y=69258477569/2^{36}$;
- $(6,8191)$ at $y=104577/2^{16}$.

During this phase, $(6,131071)$, $(6,524287)$, $(7,131071)$ and $(8,8191)$ exceeded $1.5\cdot10^6$ vectors and remain undecided.

All known infinite families are now the odd prime powers (Phase 13) and $ep^r$ for the following 16 pairs:

```math
(e,p)\in\{(3,31),(3,127),(3,257),(3,337),(3,1801),(3,8191),(4,8191)\}\cup\{\text{the nine pairs above}\}.
```

*Minimized certificates.* Over $\mathbb F_p$, the future functionals $T_wV$ span a subspace of dimension $k$, much smaller than the $e(e+1)/2+1$ states. Choose a basis $o_1=V,o_2,\dots,o_k$ of such vectors. Solve $T_co_i=\sum_jX_c[i][j]\,o_j$, the intertwining identity. Iterate $s\mapsto X_cs$ from $s_0=(\mathrm{start}\cdot o_i)_i$. The value of a word is the first reduced coordinate. A closed reduced orbit avoiding first coordinate 0 is therefore a complete certificate.

| $(e,p)$ | states | reduced dimension | reduced orbit |
| --- | ---: | ---: | ---: |
| $(3,31)$ | 7 | 5 | 57 |
| $(3,127)$ | 7 | 5 | 110 |
| $(3,8191)$ | 7 | 5 | 364 |
| $(4,8191)$ | 11 | 7 | 4,850 |

Modulo the prime $2^{61}-1$, the observable rank of the degree-$e$ representation is $3,5,7,9,12,15,18,21,25$ for $e=2,\dots,10$, checked by the checker. The same computation during this phase gave $29,33,37,42,47$ for $e=11,\dots,15$. This is exploratory and not rerun by default. These data fit $r_{e+1}-r_e=\lceil e/4\rceil+1$, a quadratic growth about four times slower than the state count. Ranks modulo a large prime bound the rational rank from below. We did not compute the rational rank exactly.

### A1.8 Powers of two, degree 128 and the mechanism of the maximal loss

*Why powers of two resist every descent.* No odd prime divides $2^r$, so no odd-order block rotation has the required orbit sizes. Lucas–Sylow reduction modulo $p$ uses the base-$p$ digits of $2^r$, which change with $r$. The resulting block-weighted masses involve non-dyadic weights $p^i2^{-w}$, and they are not uniform in $r$.

The 2-group alternative is the swap of two halves. It gives

```math
M_{2e}(t)=\sum_{w\in U^{(e)}_{t/2}}4^{|w|}+2\sum_{\text{free orbits}}2^{|v|}.
```

The fixed part cannot separate $M_{2e}$ 2-adically across $[1,2)$: $M_{2e}$ is already divisible by $2^{v_2((2e)!)+G(2e)}$ (so reduction modulo 2 is trivial), and for $t>1$ free tuples with odd multiplicities can have strictly smaller weight than every fixed point (for instance, $\{1^3,2^1\}$ at $t=7/4$ for $2e=4$ has weight $5$ versus minimal fixed weight $6$, cancelling the factor of $2$ in front of the free sum).

*Degree 128.* With `--degree-128` the checker reruns branch and bound for $M_{128}$ at precision 907. This takes 689 nodes and about 26 seconds. It confirms the certificate of Certificates 5.2, with maximal loss $906=L_{128}-1$. The default run checks the exact integers at the witness ($v_2=906$) and at $2-2^{-6}\in J_{128}$ ($v_2=776$). The maximal losses of the powers of two exceed the Kraft weight $r2^r$ (Phase 16 Proposition B.8) by 0, 9, 3, 3, 11, 10 for $d=4,8,16,32,64,128$.

*Mechanism of the maximal loss.* On $[1,2)$, $M_d(t)=2^dM_d(2t)+d\,2^{d-1}M_{d-1}(2t-2)$. Take the first maximal-loss point $t$ for each $3\le d\le60$. There the one-zero term is strictly more divisible than the zero-free term, or vanishes at $t=1$. So the maximal loss equals $d+v_2(M_d(2t))$, a property of the middle state $(d,2)$. A uniform bound for the maximal loss would therefore follow from bounds on middle states. This supports Conjecture A as the right target.

Along $t=1+2^{-a}$, $M_d$ is an exponential polynomial $\sum_{e<d}c_{d,e}2^{ea}$ for $a\ge d-1$, with $c_{d,0}=M_d(1)$. This is checked for $d\le7$. For example,

```math
M_4(1+2^{-a})=2304-384\cdot2^a+96\cdot4^a+128\cdot8^a\qquad(a\ge3).
```

Archimedean dominance of the top coefficient excludes zeros only beyond a $d$-dependent $a$. The maximal loss often occurs at $a<d-1$, for example $a=18$ for $d=33$ and $d=37$.

*Inductive valuation comparison fails.* In the recurrence above, Theorem 3 with $a=2$ bounds the order of the first term from below by $d+v_2(d!)+m_2(d)$, where $m_2(d)$ is the minimum of Theorem 3 for the budget 4. That bound is far below the actual order of the second term. Cancellation between the two terms cannot be excluded from orbit orders alone.

### A1.9 Hypothetical zero cells and secondary denominators

No zero cell exists in any certified degree, so the secondary analysis of Phase 16 §B.6 is not needed there. If a zero cell existed in some degree $d$, Corollary 2 would place it outside $J_d$. On such a cell, the part of order $(d-1)k$ of the shifted prefix of $P(\alpha)=\sum_ic_i\alpha^i$ combines two terms: $c_d$ times the secondary pole of $\alpha^d$, and $c_{d-1}M_{d-1}(t)$. When $d-1$ is resolved, $M_{d-1}(t)\ne0$. Unbounded cancellation would then require the rational ratio $c_{d-1}/c_d$ to approximate, 2-adically, a quantity attached to the cell and the shell. This is the mechanism of resonance in degree 2. A vanishing leading mass would therefore create a resonance problem in degree $d$, not a proof of nonnormality. This remark is heuristic: we have not carried out the secondary analysis in general. Phase 16 §B.6 treats pure powers, where already the case $a=0$ becomes a 2-adic approximation problem.

## Part A2. Resonant quadratics

Write $x=(A\alpha^2+B\alpha+C_0)/D$ with $\gcd(D,b)=1$, and assume the resonance condition $v_2(2A+B)\ge v_2(2A)+s$. Otherwise Phase 14 already gives normality. Let $R_n$ be the shifted prefix of the numerator and $a_r=3\cdot2^r$, so shell $k=r+1$. The Lean-verified plateau law of Phase 14 states

```math
\limsup_{N\to\infty}D_N(x)=\frac14\limsup_{r\to\infty}\Delta_b(y_r),\qquad y_r=\Bigl\{\frac{R_{a_r}}{D}\Bigr\},
```

where $\Delta_b(y)$ is the extreme discrepancy of the uniform probability on the cycle of $y$ under $u\mapsto bu\bmod1$. [Plateau law](../../NormalityChecker/QuadraticPlateauSpectrum.lean) · [Integer recurrence](../../NormalityChecker/Phase16StonehamBounds.lean)

### A2.1 The cycle point

**Theorem 10 (paper proof).** For $X^2-2X$, $D=1$ and $n=3\cdot2^{k-1}$,

```math
\{R_n\}=\Bigl\{-\frac{Z_k\,b^{2^{k-1}}}{2^{2k-1}}\Bigr\},
```

whose reduced denominator is $q_k=2^{[2k-1-v_2(Z_k)]_+}$.

*Proof.* On the upper half, $b^{-n}R_n=I_k-2^{1-k}T_k$ with $I_k$ 2-integral (Phase 14). Lean's `quadZ_eq_cancellation` gives $T_k=Z_k/(2^kb^{2^k})$. Hence $R_n+2^{1-2k}Z_kb^{n-2^k}=b^nI_k$ lies in $\mathbb Z[1/2]\cap\mathbb Z_2=\mathbb Z$, and $n-2^k=2^{k-1}$. ∎

The checker compares with direct rational prefixes for $b\in\{3,5,7,9\}$ and $k\le7$. It also checks the elementary congruence $Z_k\equiv2\pmod b$.

### A2.2 Dyadic cycles and the exact limsup for $D=1$

**Proposition 11 (paper proof).** Let $u$ be odd and $h\ge1$, or $u=0$ and $h=0$.

1. The cycle of $u/2^h$ is a single point if and only if $h\le v_2(b-1)$.
2. If $b\equiv1\pmod4$, then $\Delta_b(u/2^h)=2^{-[h-s]_+}$, independent of $u$. Here $v_2(b-1)=s$, and the cycle is a full grid of $2^{h-s}$ points.
3. If $b\equiv3\pmod4$ and $h\ge2$, the cycle is two interleaved grids of spacing $g=2^{-[h-s-1]_+}$, and $\Delta_b(u/2^h)=g\max(\theta,1-\theta)<1$. For $2\le h\le s$ one has $\theta=2w/2^h$ with $w=\min\bigl(u\bmod 2^h,\,2^h-(u\bmod 2^h)\bigr)$. For $h\ge s+1$ one has $\theta=\bigl((2^{s-1}-u)\bmod2^s\bigr)/2^s$. The maximum over $u$ and over all $h\ge2$ is $1-2^{-s}$, attained at $h=s+1$.

*Proof.* The group $\langle b\rangle\subset(\mathbb Z/2^h)^\times$ is $1+2^s\mathbb Z$ when $b\equiv1\pmod4$. When $b\equiv3\pmod4$ it is $\{1,b\}\cdot(1+2^{s+1}\mathbb Z)$ with $b\equiv-1+2^s\pmod{2^{s+1}}$. A uniform grid of $N$ points has discrepancy $1/N$. Two interleaved grids with offset $\theta g$ have discrepancy $g\max(\theta,1-\theta)$. ∎

The checker verifies all formulas on 14,336 cycles, with 14 radices and $h\le10$. Its linear-time discrepancy routine is cross-checked against brute-force enumeration of the extremal intervals.

**Theorem 12 (paper proof from the plateau law).** Let $D=1$, let $(A,B)$ be resonant and $C_0\in\mathbb Z$. Let $h_k=\log_2q_k$ and $H=\liminf_kh_k\in\mathbb N\cup\{\infty\}$.

1. If $b\equiv1\pmod4$, then $\limsup_ND_N(x)=2^{-2-[H-s]_+}$, with $2^{-\infty}=0$.
2. For every odd $b$, $\limsup_ND_N(x)=1/4$ if and only if $h_k\le v_2(b-1)$ for infinitely many $k$. For $X^2-2X$ this is $v_2(Z_k)\ge2k-1-v_2(b-1)$ infinitely often.
3. If $b\equiv3\pmod4$ and $H\ge2$, then $\limsup_ND_N(x)\le\frac14(1-2^{-s})$. If $H\ge s+2$, then $\limsup_ND_N(x)\le\frac14\,2^{s+1-H}(1-2^{-s})$.

*Proof.* For $D=1$, $y_r=\{R_{a_r}\}$ has exact denominator $q_{r+1}$. For part 1, apply Proposition 11.2. Since $\Delta$ is non-increasing in $h$, $\limsup_k2^{-[h_k-s]_+}=2^{-[H-s]_+}$. For part 2, singletons give $\Delta=1$. Every non-singleton dyadic cycle has $\Delta\le1/2$ when $b\equiv1\pmod4$, and $\Delta\le1-2^{-s}$ when $b\equiv3\pmod4$ (Proposition 11), so the limsup of $\Delta$ is 1 exactly when singletons occur infinitely often. Part 3 is Proposition 11.3. ∎

So the exceptional discrepancy of a resonant quadratic with $D=1$ is not merely bounded by $1/4$. For $b\equiv1\pmod4$ it is the explicit function $2^{-2-[H-s]_+}$ of the single integer $H$ given in Theorem 12.1, a statement about the integers $Z_k$. Normality holds if and only if $H=\infty$; otherwise $\limsup D_N$ is at least $2^{-2-[H-s]_+}$ when $b\equiv1\pmod4$, and at least $2^{-3-[H-s-1]_+}$ when $b\equiv3\pmod4$ and $H\ge2$ (since $\max(\theta,1-\theta)\ge1/2$), a quantitative dichotomy.

### A2.3 Admissible cycles for general $D$, and bounds below $1/4$

Let $D=2^\delta D_1$ with $D_1$ odd. By the Chinese remainder theorem, $y_r$ splits into a $D_1$-component and a 2-component.

- *The $D_1$-component* is $\rho_k\cdot2^{-\delta}/D_1$ with $\rho_k=b^{n_k}Q_k\bmod D_1$, where $n_k=3\cdot2^{k-1}$ and $Q_k=A(S_k^2-L_k^2)+BS_k+C_0$. The triple $(S_k\bmod D_1,\,2^{-k}\bmod D_1,\,b^{2^{k-1}}\bmod D_1)$ evolves deterministically. So $\rho_k$ is eventually periodic, with computable preperiod $k_0$ and period $\Pi$.
- *The 2-component* has exact denominator $2^{h_k+\delta}$ when $h_k\ge1$, and denominator dividing $2^\delta$ when $h_k=0$. Its odd numerator depends on the unknown digits of $\kappa$ beyond the run, so we allow every value.
- *Admissible indices.* On any subsequence with bounded $h_k$, $v_2(k-\kappa)\to\infty$. So eventually $k\equiv\kappa\pmod{2^{v_2(\Pi)}}$, while $k\bmod\Pi_{\mathrm{odd}}$ is unrestricted.

Let $Y_h$ be the resulting finite set of admissible cycle points of level $h$.

**Theorem 13 (paper proof; exact finite enumeration).**

1. $\limsup_ND_N(x)\le\frac14\sup_{h\ge0}\max_{y\in Y_h}\Delta_b(y)$. The supremum is a finite maximum. Put $M=\operatorname{lcm}(\operatorname{ord}_{D_1}b,2)$ and $t_1=v_2(b^M-1)$. Then $\langle b^M\rangle$ fixes the $D_1$-component and acts on the 2-component as the full group $1+2^{t_1}\mathbb Z_2$. So for $h\ge1$ every cycle is a union of translates of the grid $2^{t_1-h-\delta}\mathbb Z/\mathbb Z$, and $\Delta_b(y)\le2^{t_1-h-\delta}$ once $h+\delta\ge t_1$.
2. (Dichotomy.) If $q_k\not\to\infty$, then $\limsup_ND_N(x)\ge\frac14\min_{y\in Y_H}\Delta_b(y)>0$ with $H=\liminf h_k$.
3. A singleton cycle, and with it $\limsup D_N=1/4$, is possible only if some admissible $y$ has $(b-1)y\in\mathbb Z$.

**Proposition 14 ($D=3$; paper proof).** Let $b\equiv2\pmod3$ and let $(A,B)$ be resonant. On admissible indices, $Q_k\equiv C_0-B$ when $\kappa$ is odd and $Q_k\equiv C_0-A$ when $\kappa$ is even, modulo 3. Suppose this residue is nonzero. Then the supremum of $\Delta_b$ over admissible cycles is exactly $1-1/(3\cdot2^{v_2(b+1)})$. Hence

```math
\limsup_{N\to\infty}D_N(x)\le\frac14\Bigl(1-\frac{1}{3\cdot2^{v_2(b+1)}}\Bigr)<\frac14 .
```

For $X^2-2X$, where $\kappa_0\equiv3\pmod4$, the condition is $C_0\not\equiv1\pmod3$.

*Proof.* Modulo 3, $L_j\equiv(-1)^j$ and $S_k\equiv-[k\text{ odd}]$, which gives the residues of $Q_k$. Admissible $k$ satisfy $k\equiv\kappa\pmod2$. An admissible point is $y=c/3+u/2^h$ with $c\in\{1,2\}$ fixed, $u$ odd for $h\ge1$, and $u=0$ for $h=0$.

- For $h=0$ the cycle is $\{1/3,2/3\}$, with $\Delta=2/3$.
- For $1\le h\le s+1=v_2(b^2-1)$ the cycle is $\{y,by\}$. Its two points have different 3-components, and $\Delta=1-\|(b-1)y\|$, where $\|\cdot\|$ is the distance to $\mathbb Z$. Now $(b-1)y=N/(3\cdot2^m)$ with $m\le h-v_2(b-1)\le v_2(b+1)$ and $N\equiv2^mc\not\equiv0\pmod3$. So $\|(b-1)y\|\ge1/(3\cdot2^{v_2(b+1)})$.
- For $h\ge s+2$ the group $\langle b^2\rangle$ fixes the 3-component and acts on the 2-component as $1+2^{s+1}\mathbb Z_2$. So the cycle is two grids of spacing $2^{s+1-h}\le1/2$, and $\Delta\le1/2$.

Equality is attained by a 2-cycle at $h=s+1$. Write $(b-1)u/2^h=u'/2^{v_2(b+1)}$ and choose $u$ so that $|2^{v_2(b+1)}c+3u'|=1$. ∎

The checker confirms the exact supremum by enumeration for every $b<100$ and $C_0\in\{0,2\}$.

The checker reproduces the following suprema $\sup\Delta$, with $\limsup D_N\le\sup\Delta/4$, listed for $C_0=0,1,\dots,D-1$:

| $b$ | $D$ | $\sup\Delta$ for $C_0=0,\dots,D-1$ |
| ---: | ---: | --- |
| 5 | 3 | 5/6, 1, 5/6 |
| 11 | 3 | 11/12, 1, 11/12 |
| 17 | 3 | 5/6, 1, 5/6 |
| 7 | 3 | 1, 1, 1 |
| 3 | 5 | 27/40, 1, 27/40, 27/40, 27/40 |
| 5 | 9 | 5/18, 1, 5/18, 5/18, 1, 5/18, 5/18, 1, 5/18 |
| 7 | 9 | 1/3, 1, 1/3, 1/3, 1, 1/3, 1/3, 1, 1/3 |
| 11 | 9 | 11/36, 1, 11/36, 11/36, 1, 11/36, 11/36, 1, 11/36 |

An entry 1 means that a singleton cycle is admissible, so no improvement on $1/4$ is possible by this method. For instance $\limsup_ND_N\bigl((\alpha^2-2\alpha)/9\bigr)\le5/72$ for $b=5$. For $b\equiv1\pmod3$ and $D=3$ singleton cycles are admissible for every $C_0$.

The checker also tests the residue sequences $\rho_k$ against direct prefixes for five triples $(b,D,C_0)$. It checks the parity rule on the second resonant pair $(A,B)=(1,6)$ for $b=5$, where $\kappa$ is even and singletons occur exactly for $C_0\equiv1\pmod3$.

These bounds are unconditional. They hold whether or not $x$ is normal. Whether any admissible cycle is actually attained is equivalent to the open 2-adic question.

### A2.4 Toward a fixed radix: what is and is not proved

- *Normality of $\alpha^2-2\alpha$ for a specified $b$.* There is no progress on the decisive question. The new information is quantitative. By Theorem 12, normality is equivalent to $\limsup D_N=0$. For $b\equiv1\pmod4$ the exceptional value is exactly $2^{-2-[H-s]_+}$, with $H$ read off from the integers $Z_k$. The admissible exceptional indices satisfy the known restrictions: $k\equiv\kappa_0\equiv-1+\lambda\pmod{2^{2s}}$, and consecutive ones satisfy the tower separation $2^{\,k-a-s-h}\mid k'-k$ of Phase 14. We found no further arithmetic restriction.
- *New provable resonant families.* None. Every resonant class has $\kappa=\kappa_0-\beta/\lambda$ with $\beta=(2A+B)/2A\in\mathbb Q$ and $v_2(\beta)\ge s$. Normality of the class is equivalent to $\kappa$ not being 2-adically Liouville in the extreme sense $v_2(k-\kappa)\ge k-c$ infinitely often. No resonant $\kappa$ is known to be algebraic, and Phase 16 A.5 explains why the standard transcendence methods stop. Two distinct resonant classes differ by $\kappa'-\kappa=\gamma/\lambda$ with $\gamma\in\mathbb Q^\times$. Joint exceptionality would make $\gamma-m\lambda$ 2-adically tiny for integers $m$. A $p$-adic inhomogeneous Baker bound would control this, but only when the exceptional indices of the two classes are comparable. We draw no conclusion from it.
- *Exceptional cycles.* Theorem 13 classifies the admissible ones for every $(A,B,C_0,D)$ with $\gcd(D,b)=1$. Singleton cycles are excluded in the explicit cases of Proposition 14. They are never forced: forcing any cycle would require bounded denominators along a subsequence, which is the open problem itself.

## Part A3. Formalization and joint normality

### A3.1 Joint normality from pivot degrees

Call $d\ne2$ resolved if $P(\alpha)$ is normal in base $b$ for every rational $P$ of degree $d$. By Phase 13, Phase 16 and this note, this holds for:

- $d=1$, since $\alpha$ is a Stoneham number with $\gcd(2,b)=1$ ([D. H. Bailey and R. E. Crandall, “Random generators and normal numbers,” *Experimental Mathematics* 11 (2002), 527–546](https://doi.org/10.1080/10586458.2002.10504704));
- $3\le d\le120$ and $d=128$;
- the odd prime powers;
- $ep^r$ for the 16 good pairs.

Degree 2 is resolved exactly for non-resonant quadratics (Phase 14).

**Proof of Theorem 8.** Real numbers $x_1,\dots,x_m$ are jointly normal in base $b$ when $(b^nx_i\bmod1)_i$ is uniformly distributed in $[0,1)^m$. By Weyl's criterion and Wall's theorem, this holds if and only if every nonzero integer combination $\sum t_ix_i$ is normal. By linear independence of $P_1,\dots,P_m$, $\sum t_iP_i$ is a nonzero element of $V$ whenever $t\in\mathbb Z^m\setminus\{0\}$.

Every nonzero element of $V$ has as its degree one of the pivot degrees of an echelon basis, namely its leading pivot. If that degree is resolved, the combination is normal. If it is 2, the element is $c\cdot P_{(2)}$, because no pivot 0 or 1 is present. That element is non-resonant, since resonance is invariant under scaling.

The hypotheses are sharp in two directions. A constant in $V$ is never normal. Pivots $\{1,2\}$ put $P_{(2)}+cP_{(1)}$ in $V$ for every $c\in\mathbb Q$, and some choice of $c$ makes it resonant, for example $\alpha^2-2\alpha$ from $\{\alpha^2,\alpha\}$. ∎

The checker runs the criterion on eight families. It accepts $\{\alpha^3,\alpha^5+\alpha^2,\alpha^{128}\}$, $\{\alpha,\alpha^3-\alpha^2\}$, $\{\alpha^2+\alpha,\alpha^7\}$ for $b=3$, and $\{\alpha^{3\cdot65537}\}$. It rejects $\{\alpha^2-2\alpha\}$, $\{\alpha^2,\alpha\}$, $\{\alpha^{122}+\alpha^3,\alpha^3\}$ (122 is unresolved) and $\{\alpha^3+1,\alpha^3\}$.

Both the monomial case (`jointUniform_of_established_degrees`) and the echelon-degree case (`jointUniform_of_echelon_degrees`, Theorem 8), together with the kernel-checked `(3, 31)` minimized closed-orbit nonvanishing certificate (`descent31Check_true`, `descent31_all_words_nonzero`), are kernel-verified in [Phase17DiscrepancyBounds.lean](../../NormalityChecker/Phase17DiscrepancyBounds.lean).

### A3.2 Lean-ready targets

Target L2 and the closed-orbit check half of L5 are now kernel-verified in [Phase17DiscrepancyBounds.lean](../../NormalityChecker/Phase17DiscrepancyBounds.lean); the remaining rows below are sketches for future Lean formalization.

| Target | Content | Status / Difficulty |
| --- | --- | --- |
| L1 | Theorem 1 and Theorem 3, as pure combinatorics on finitely supported `c : ℕ → ℕ`: Legendre via `padicValNat_factorial`, floors and finite sums | Moderate; self-contained |
| L2 | Echelon joint normality: `P : Fin m → ℤ[X]` with injective `natDegree`, hypothesis normality of all nonzero polynomials of those degrees, conclusion `JointUniform b (fun i => aeval α (P i))` | **Verified** in `Phase17DiscrepancyBounds.lean` (`jointUniform_of_echelon_degrees`) |
| L3 | Theorem 10, the cycle point $\{R_n\}=\{-Z_kb^{2^{k-1}}/2^{2k-1}\}$ | Easy from `quadZ_eq_cancellation` and the Phase 14 prefix lemmas |
| L4 | Proposition 11 and the grid lemma (an average of grid measures of spacing $g$ has discrepancy at most $g$), plus finite evaluations of $\Delta_b$ by `decide` | Moderate |
| L5 | Minimized cyclic-descent certificates (A3.3) | `(3, 31)` closed-orbit `decide` check & word induction **verified** in `Phase17DiscrepancyBounds.lean` (`descent31_all_words_nonzero`); intertwining + formal automaton recurrence remain |
| L6 | Proposition 6 and Theorem 4 | Need the formal mass and the orthant numerator; Theorem 4 also needs orbit counting for $C_{p^r}$ |

A statement sketch for L1:

```lean
theorem least_orbit_order (c : ℕ → ℕ) (I : ℕ) (hc : ∀ i, I < i → c i = 0)
    (hK : (∑ i ∈ Finset.range (I + 1), (c i : ℚ) / 2 ^ i) < 2) :
    (∑ k ∈ Finset.Icc 1 (∑ i ∈ Finset.range (I + 1), c i), (Nat.log 2 k : ℤ)) ≤
      ∑ i ∈ Finset.range (I + 1), (((i * c i : ℕ) : ℤ) - (padicValNat 2 (c i).factorial : ℤ))
```

### A3.3 A proof-producing certificate format for cyclic descent

For a good pair $(e,p)$ the certificate consists of:

1. the digit matrices $T_0,T_1$ over `ZMod p` of size $e(e+1)/2+1$, with the absorbed value as the last coordinate, the value vector $V$ and the start index;
2. the reduced basis columns $o_1=V,\dots,o_k$, the reduced matrices $X_0,X_1$, and the intertwining identities $T_co_i=\sum_jX_c[i][j]\,o_j$, a finite matrix identity;
3. the reduced orbit list $R$ with $R[0]=s_0$, and a successor table with $X_cR[i]=R[\mathrm{succ}(i,c)]$;
4. the check $R[i]_1\ne0$ for all $i$.

The theorem "for every finite digit word $w$, $\mathrm{start}\cdot T_w\cdot V\ne0$ in `ZMod p`" then follows by induction on $w$, with invariant $s(\mathrm{start}\,T_w)\in R$. Linking it to $M_e$ needs only the automaton recurrence (Phase 16 B.1). For $(3,31)$ the reduced representation has dimension 5 and a closed orbit of 57 vectors; `python -B scripts/phase17_dyadic_stoneham.py --emit-lean` prints `P`, `X0`, `X1`, the 57-vector `orbit`, `succ`, and the Boolean checker `check` (the basis $o_1,\dots,o_5$ and $T_0,T_1,V$ are verified in Python in the default run), and the closed-orbit check plus arbitrary-word induction are kernel-verified in [Phase17DiscrepancyBounds.lean](../../NormalityChecker/Phase17DiscrepancyBounds.lean) (`descent31Check_true`, `descent31_all_words_nonzero`). The case $(4,8191)$ has 4850 vectors in dimension 7. It is plausible for kernel `decide`, with `native_decide` as a fallback of weaker trust.

## Failed approaches, precisely

1. **Dominant orbit.** It proves nonvanishing only on $J_d$ (Corollary 2). Elsewhere minimal orbits tie, as in Phase 16 B.4: for $3\le d\le20$, between 20% and 63% of leaves lie above the least orbit order of their cut.
2. **Parity and positivity invariants.** They see only odd twists (Lemma 9). The even argument 2 gives no information. Modulo 3 the never-vanishing $z=-1$ twist reduces to zero for $d\in\{2,4,5,6,7\}$. $M_d(t)$ changes sign, for example $M_3(1)=32$ and $M_3(2^-)=-8$.
3. **Second-order descent.** It is valid (Theorem 4) but fails for $(2,3),(2,5),(4,3),(3,5),(3,7),(3,11)$, with explicit witnesses. It does not reach $2p^r$.
4. **Induction on the number of zero coordinates.** The recurrence feeds through the middle states, whose zero-freeness is Conjecture A. At the maximal-loss points the zero-free term carries the whole loss. Orbit-order bounds on the other term (Theorem 3) are far too weak to prevent cancellation.
5. **Powers of two.** No odd prime divides $2^r$. Base-$p$ digits of $2^r$ are not uniform in $r$. The swap involution does not separate 2-adically (§A1.8). Only the computational certificate for $d=128$ is new.
6. **Exponential polynomials along $1+2^{-a}$.** Archimedean dominance works only for $a\ge a_0(d)$, while maximal losses occur at smaller $a$.
7. **New resonant quadratic families.** None are provable (§A2.4).

## Open problems

1. Nonvanishing of $M_d$ on $[1,2)$ for every $d\ge3$, equivalently normality for every degree. Conjecture A is the stronger, induction-friendly form. It is verified for $a\le64$.
2. A uniform bound on $\max_tv_2(M_d(t))-(rd+2j)$. It is at most 14 for $d\le120$ and equals 10 at $d=128$. By §A1.8 it is equivalent to bounds for the middle state $(d,2)$ near $t=2$.
3. Whether any finite order of the $p$-adic hierarchy certifies a pair that is bad at first order, for example $(2,p)$.
4. The exact rational rank of the leading-mass representation, conjecturally with $r_{e+1}-r_e=\lceil e/4\rceil+1$.
5. Normality of $\alpha^2-2\alpha$ for a single radix. Equivalently, decide whether $H=\liminf_k[2k-1-v_2(Z_k)]_+$ is finite. Also, whether the bounds of Proposition 14 are attained.

## Reproduction

From the repository root:

```sh
python -B scripts/phase17_dyadic_stoneham.py                    # about 40 seconds
python -B scripts/phase17_dyadic_stoneham.py --degree-128       # adds the M_128 certificate (about 30 seconds)
python -B scripts/phase17_dyadic_stoneham.py --middle-max 64    # middle states through degree 64 (about 100 seconds)
python -B scripts/phase17_dyadic_stoneham.py --emit-lean        # minimized (3, 31) certificate as Lean data
```

The script uses only the Python standard library, with exact integer and rational arithmetic throughout. Its maximal-loss check reads the Phase 16 certificate table from `scripts/phase16_dyadic_stoneham.py`.
