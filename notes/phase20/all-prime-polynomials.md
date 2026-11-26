# Polynomial normality with every denominator prime

Fix an integer radix $b\ge2$ and an odd prime $p\nmid b$. List the other primes coprime to $b$ in increasing order as $\ell_1<\ell_2<\cdots$; when $b$ is odd, $\ell_1=2$. Put $n_k=2^{k^3}$ and

$$
 W=\sum_{k\ge1}\frac{1}{p^{k^2}\,\ell_k\,b^{\,n_k}} .
$$

**Theorem C1.** For every nonconstant $P\in\mathbb Q[x]$ the number $P(W)$ is normal in base $b$ and Liouville. Its all-prefix extreme discrepancy satisfies

$$
 D_N(P(W);b)\ll_{P,c}\exp\big(-c(\log N)^{2/3}\big)
 \qquad\text{for every } c<c_0=\min\Big(3(\log2)^{1/3},\ \frac{r\log p}{(\log 2)^{2/3}}\Big),
$$

where $r=\deg P$. In particular $W$ is transcendental and the shifts of $(W,W^2,\ldots,W^r)$ are jointly uniformly distributed in every dimension. For $n_k\le n<n_{k+1}$ the reduced denominator of the shifted prefix of $W$ is exactly $p^{k^2}\ell_1\cdots\ell_k$, so every prime coprime to $b$ divides all reduced shifted prefix denominators from some point on.

This is a written proof. Its inputs are the exact surviving-grid theorem and the prefix estimate of Phase 19, whose arithmetic core is kernel-verified, Chebyshev's bound for primes, and rational dilation, which is kernel-verified as `normal_mul_nat_iff`. Section 7 gives the general theorem (C2) for arbitrary schedules, protected depths and auxiliary primes, with one or several generators. [Grid theorem and prefix estimate](../phase19/grids.md) · [Lean grid core](../../NormalityChecker/SurvivingGrid.lean) · [Exact checks](../../scripts/phase20_normality.py)

## 1. Notation and the window rule

Write $e_k=k^2$, $V_k=b^{-n_k}/(p^{e_k}\ell_k)$ and $U_k=V_1+\cdots+V_k$, with $U_0=0$. The schedule satisfies $n_{k+1}/n_k=2^{3k^2+3k+1}\to\infty$, and the depths satisfy $e_k-e_{k-1}=2k-1\to\infty$.

Clear denominators: $P=P_1/M$ with $M\ge1$ and $P_1\in\mathbb Z[x]$ of degree $r\ge1$ and leading coefficient $A\ne0$. Write $P_1(x)=\sum_{j\le r}a_jx^j$. Then $P_1(W)=\sum a_j W^j$ expands as a sum over ordered tuples $\tau=(k_1,\ldots,k_j)$ of $a_j\prod_iV_{k_i}$, at position $|\tau|=n_{k_1}+\cdots+n_{k_j}$. The shifted prefix at $n$ is $R_n=\sum_{|\tau|\le n}a_\tau b^{\,n-|\tau|}$.

Fix a shell $n_k\le n<n_{k+1}$ with $k$ so large that $rn_{k-1}<n_k$ and $(r+1)n_k\le n_{k+1}$ (so all $r$ windows $\mathcal W_{k,i}$ below stay inside $[n_k,n_{k+1})$). A tuple using an index above $k$ has position at least $n_{k+1}>n$. A tuple on indices below $k$ has position at most $rn_{k-1}<n_k\le n$, so all such tuples, the case $l=0$, are already present. A tuple with exactly $i\ge1$ copies of $k$ has position in $[in_k,in_k+(r-i)n_{k-1}]$. Discard the windows

$$
 \mathcal W_{k,i}=[\,in_k,\ in_k+rn_{k-1}\,],\qquad 1\le i\le r .
$$

Outside them a tuple with $i$ copies of $k$ is present exactly when $in_k\le n$. With $l=\min(r,\lfloor n/n_k\rfloor)\ge1$, Taylor's formula $P_1(U+V)=\sum_i P_1^{(i)}(U)V^i/i!$ gives

$$
 b^{-n}R_n=F_l(U_{k-1},V_k),\qquad
 F_l(U,V)=\sum_{i=0}^{l}\frac{P_1^{(i)}(U)}{i!}V^i
          =\sum_{d\le r}a_d\sum_{i\le\min(d,l)}\binom di U^{d-i}V^i .
$$

**There are no insertions in a shell outside the windows.** Every tuple position in $[n_k,n_{k+1})$ lies in a window. Since $\mathcal W_{k,1}$ starts at $n_k$, the retained part of shell $k$ consists of at most $r$ runs, and on each run $R_{n+1}=bR_n$.

**Discarded mass.** Through any cutoff $N$ in shell $K$, including a cutoff inside a window, the discarded shifts number at most $\sum_{k\le K}r(rn_{k-1}+1)\le 2r^2n_{K-1}+rK$ plus a fixed initial segment. Relative to $N\ge n_K$ this is $O_r(2^{-3K^2+3K}+K/N)$.

## 2. The protected pole

**Lemma 1 (pole dominance).** Let $U,V\in\mathbb Q$ with $v_p(U)=-e'$ and $v_p(V)=-e$, where $0\le e'<e$. Let $P_1\in\mathbb Z[x]$ have degree $r$ and leading coefficient $A$, and let $1\le l\le r$. If

$$
 \min(e',\,e-e')>v_p(A)+v_p\tbinom rl ,
$$

then $v_p(F_l(U,V))=v_p(A)+v_p\binom rl-\big((r-l)e'+le\big)$.

*Proof.* Write $D(d,i)=(d-i)e'+ie$ for the depth of $U^{d-i}V^i$. The term $(d,i)=(r,l)$ has valuation exactly $v_p(A\binom rl)-D(r,l)$. Any other term has $d\le r$ and $i\le\min(d,l)$, an integer coefficient, and valuation at least $-D(d,i)$. The difference is

$$
 D(r,l)-D(d,i)=(r-d)e'+(l-i)(e-e')\ \ge\ \min(e',e-e'),
$$

because $(d,i)\ne(r,l)$ forces $r-d\ge1$ or $l-i\ge1$. This single identity covers every case raised in the brief: lower degree $d<r$ with $i=l\le d$ (loss $(r-d)e'$), $d<l$ (loss at least $e+(r-l)e'$), and same degree with fewer new copies (loss $e-e'$). The hypothesis makes every competitor strictly shallower, and the ultrametric inequality gives the claim. $\square$

Apply Lemma 1 with $U=U_{k-1}$ and $V=V_k$. The prefix $U_{k-1}$ has the unique deepest term $k-1$, so $v_p(U_{k-1})=-(k-1)^2$. Also $v_p(V_k)=-k^2$, because $\ell_k\ne p$ and $p\nmid b$. The gap is $\min((k-1)^2,2k-1)$, which exceeds $v_p(A)+\log_p r$ for all $k\ge k_1(P)$. Multiplying by the $p$-unit $b^n$ gives, at every retained shift of shell $k\ge k_1$,

$$
 v_p(q_n)=(r-l)(k-1)^2+lk^2-v_p(A)-v_p\tbinom rl\ \ge\ r(k-1)^2+2k-1-v_p(A)-\log_pr ,
$$

where $q_n$ is the reduced denominator of $R_n$.

## 3. Support, size and the surviving grid

Every present tuple has denominator dividing $p^{rk^2}\prod_{j\le k}\ell_j^{\,r}$, and the radix powers $b^{n-|\tau|}$ are integers. Hence

$$
 q_n\ \Big|\ p^{rk^2}\prod_{j\le k}\ell_j^{\,r},\qquad (q_n,b)=1 .
$$

Rosser's bound, or Chebyshev's elementary bound, gives $\ell_k\le p_{k+\omega(b)+1}\ll k\log k$. Erdős's bound $\prod_{\ell\le x}\ell<4^x$ then gives $\log\prod_{j\le k}\ell_j\le\ell_k\log4=O(k\log k)$. Thus $\log q_n\le rk^2\log p+O_r(k\log k)=O_{P}(k^2)$. Since $\log N\ge k^3\log2$, both $q_n$ and the period $\operatorname{ord}_{q_n}b<q_n$ are $\exp(O_P((\log N)^{2/3}))=N^{o(1)}$.

**Newest prime.** In the regime $l=r$, the coefficient of $V_k^r$ in $F_r$ is $A$, and every other term has fewer factors $V_k$ and an $\ell_k$-integral coefficient. So $\ell_k^{\,r}\,\|\,q_n$ whenever $\ell_k\nmid AM$. The older primes $\ell_j$, $j<k$, enter $P_1(U_{k-1})$ through cancellable sums, and **no persistence is claimed for them in $P(W)$** when $r\ge2$. For $W$ itself, with $r=1$, there are no windows. The prefix on shell $k$ is $b^nU_k$, each $\ell_j$ divides exactly one term, with an $\ell_j$-unit numerator, and $q_n=p^{k^2}\ell_1\cdots\ell_k$ exactly.

**Surviving grid.** Write $q_n=p^{e}Q_n$ with $p\nmid Q_n$, $t_0=\operatorname{ord}_pb$ and $a=v_p(b^{t_0}-1)$. By the Phase 19 exact grid theorem, every full period of $R_n$ is a union of equally spaced grids of size $G_n=p^{\max(0,e-w_n)}$, where

$$
 w_n=a+v_p(\operatorname{ord}_{Q_n}b)=a+\max_{\ell\mid Q_n}v_p(\operatorname{ord}_\ell b)
 \le a+\max_{j\le k}v_p(\ell_j-1)\le a+\log_p\ell_k=O(\log k).
$$

The prime $\ell=2$ contributes $0$. Therefore $G_n\ge p^{\,r(k-1)^2+2k-1-O_P(\log k)}\to\infty$, uniformly on the retained shifts of shell $k$.

**Rational coefficients.** Write $M=M_bM'$ with $M_b\mid b^{c}$ and $(M',b)=1$. Then $y=b^cP(W)=(b^c/M_b)P_1(W)/M'$ has shifted prefixes $(b^c/M_b)R_n/M'$. Their denominators divide $q_nM'$ and are prime to $b$. Their $p$-depth is $v_p(q_n)+v_p(M')$, and their grid loss grows by at most $\max_{\ell\mid M'}v_p(\ell-1)$. All bounds above therefore hold for $y$, and $D_N(P(W))\le D_{N-c}(y)+c/N$. Qualitative normality also follows directly from `normal_mul_nat_iff`, since $MP(W)=P_1(W)$.

## 4. Counting every prefix

Use the Phase 19 prefix estimate with its tail term replaced by $\tau_H=\sup|b^nx-R_n|$ over retained shifts outside the buffer. The proof there uses only this supremum. A buffer of length $H$ before each window costs at most $r(K+1)H$ shifts. Outside the windows and buffers every absent tuple has $|\tau|>n+H$. Since $1\le k_i\le(\log_2s)^{1/3}$, the number of ordered $j$-tuples at position $s$ is at most $(\log_2s)^{j/3}$, and every coefficient has modulus at most $1$. Therefore

$$
 \tau_H\le\Big(\sum_j|a_j|\Big)\sum_{u>H}\big(2+\log_2(N+u)\big)^{r/3}b^{-u}
       \ll_P(\log N)^{r/3}b^{-H}.
$$

Take $H=\lceil2\log_b(N+2)\rceil$, so that $\tau_H\ll(\log N)^{r/3}N^{-2}$. Write $K=\lfloor(\log_2N)^{1/3}\rfloor$ for the shell of $N$.

- **Windows and buffers:** $O_r(2^{-3K^2+3K})+O(K\log N/N)$.
- **Runs and residual periods:** there are at most $(r+1)(K+1)+O(1)$ runs, each residual is at most $\max q_n\le e^{O_P(K^2)}$, and the normalized cost is $e^{O_P(K^2)-K^3\log2}$.
- **Mesh:** shells below $K-1$ occupy at most $n_{K-1}$ shifts, while shells $K-1$ and $K$ cost $N(1/G_{K-1}+1/G_K)$, giving $O(2^{-3K^2+3K})+p^{-r(K-2)^2+O_P(\log K)}$.

Since $K\ge(\log_2N)^{1/3}-1$, the window and mesh terms are $\exp(-3(\log2)^{1/3}(\log N)^{2/3}+O((\log N)^{1/3}))$ and $\exp(-r\log p\,(\log2)^{-2/3}(\log N)^{2/3}+O((\log N)^{1/3}))$. This proves the rate in Theorem C1. The surviving grid gives the mesh term, so it does not rely on any fixed-support kernel theorem.

## 5. Liouville approximation, transcendence and joint distribution

Put $D_k=b^{n_k}p^{k^2}\ell_1\cdots\ell_k$, so that $\log D_k=n_k\log b+O(k^2)$. The rational number $P(U_k)$ has denominator dividing $MD_k^{\,r}$. Moreover $|P(W)-P(U_k)|\le\max_{[0,1]}|P'|\cdot2b^{-n_{k+1}}$. Normality makes $P(W)$ irrational, so these errors are nonzero. Because $n_{k+1}/n_k\to\infty$, for every $h$ the error is eventually below $(MD_k^r)^{-h}$. Hence $P(W)$ is a Liouville number. A polynomial relation $P(W)=0$ would contradict normality, so $W$ is transcendental. For an integer vector $h\ne0$, the combination $\sum h_jW^j$ is a nonconstant integral polynomial, hence normal, and Weyl's criterion gives joint uniform distribution of $(W,\ldots,W^r)$.

## 6. Checklist for the proposed proof

| Brief item | Verdict |
|---|---|
| $n_{k+1}/n_k=2^{3k^2+3k+1}$, $e_k-e_{k-1}=2k-1$ | Correct |
| Clearing denominators with OP-07 or `normal_mul_nat_iff` | Correct. The rate needs the $b^c$ shift of Section 3 so the grid theorem applies with $(q,b)=1$ |
| Window case $l=0$ | Complete at $n_k$ once $rn_{k-1}<n_k$. Cutoffs inside a window are counted in Section 1 |
| Pole depth, including lower degrees $l\le d<r$ | Lemma 1, by the single identity $(r-d)e'+(l-i)(e-e')$ |
| $q_n=N^{o(1)}$, period $\le q_n$ | Correct, with $\log q_n=O(k^2)$ |
| Grid loss $O(\log k)$, $G\to\infty$ | Correct |
| Number of runs | Stronger than the brief: at most $r+1$ per shell, not $O(k^r)$ |
| Rate $\exp(-c(\log N)^{2/3})$ | **Confirmed**, with the constant $c_0$ above |
| Liouville property | Correct |
| Every off-radix prime persists | Correct for $W$. For $P(W)$ only $p$ and, when $l=r$, the newest prime are controlled |

## 7. General protected-pole theorem (C2)

### (a) One generator

Let $b\ge2$ and let $p\nmid b$ be an odd prime. Let $n_k$ be strictly increasing positive integers and $e_k\ge1$ integers. Let $m_k\ge1$ be integers coprime to $pb$, and let $u_k$ be integers with $p\nmid u_k$ and $0<|u_k|\le p^{e_k}m_k$. Put $c_k=u_k/(p^{e_k}m_k)$ and $W=\sum c_kb^{-n_k}$. Let $\Lambda_k=\operatorname{lcm}(m_1,\ldots,m_k)$ and $\lambda_k=\max_{\ell\mid\Lambda_k}v_p(\operatorname{ord}_\ell b)\le\max_{\ell\mid\Lambda_k}\log_p\ell$. Assume

1. (S) $n_{k+1}/n_k\to\infty$;
2. (D) $e_k-e_{k-1}\to\infty$;
3. (G) $e_k-\lambda_k\to\infty$;
4. (P$_r$) $k\,(p^{e_k}\Lambda_k)^r=o(n_k)$.

**Theorem C2a.** Then $P(W)$ is normal in base $b$ and Liouville for every $P\in\mathbb Q[x]$ with $1\le\deg P\le r$. With $K=\max\{k:n_k\le N\}$,

$$
 D_N(P(W);b)\ll_P\frac{n_{K-1}}{n_K}+p^{\lambda_{K-1}-e_{K-1}}+p^{\lambda_K-e_K}
   +\frac{K(p^{e_K}\Lambda_K)^r}{n_K}+\frac{K\log(2N)}{N}.
$$

If $\log(p^{e_k}\Lambda_k)=o(\log n_k)$, then (P$_r$) holds for every $r$ and the conclusion holds for all nonconstant $P$. For $W$ itself, $v_\ell(q_n)=\max_{j\le k}v_\ell(m_j)$ on $[n_k,n_{k+1})$ whenever that maximum is attained at a single $j$ with $\ell\nmid u_j$.

*Proof.* Repeat Sections 1–5 with $e_k$ in place of $k^2$. (D) makes the deepest term of $U_{k-1}$ unique eventually and makes the Lemma 1 gap $\min(e_{k-1},e_k-e_{k-1})$ tend to infinity. The pole depth satisfies $v_p(q_n)\ge(r-1)e_{k-1}+e_k-O_P(1)$, and the loss satisfies $w_n\le a+\lambda_k+O_M(1)$, so (G) gives $G_n\to\infty$. Under (S) there are $O(rK)$ runs, with $K=O(\log N)$ because $n_k$ eventually grows faster than geometrically. The run residuals are controlled by (P$_r$), since $q_n\mid p^{re_k}\Lambda_k^rM'$. The tail is $O_P((\log N)^rb^{-H})$. The Liouville bound uses $\log D_k=n_k\log b+o(n_k)$, which follows from (P$_1$). $\square$

Theorem C1 is the case $e_k=k^2$, $m_k=\ell_k$, $u_k=1$. There, (P$_r$) reads $e^{O(k^2)}=o(2^{k^3})$, and (G) reads $k^2-O(\log k)\to\infty$. The hypothesis (D) cannot simply be dropped: with bounded depth increments the leading coefficient need not dominate. Phase 19 needed plateau arithmetic for that situation. [Plateau argument](../phase19/nonlinear.md#2-universal-polynomial-normality-with-consecutive-ratios-tending-to-one)

### (b) Several generators, shared prime: Variant 1

Let $\gamma_1,\ldots,\gamma_m>0$ be linearly independent over $\mathbb Q$, and let $f_k$ be real numbers with $\gamma_a f_1\ge1$ for all $a$, $\Delta_k=f_k-f_{k-1}\to\infty$, and $\Delta_k=o(f_k)$. Put $e_{a,k}=\lfloor\gamma_af_k\rfloor\ge1$ and $X_a=\sum_kc_{a,k}b^{-n_k}$ with $c_{a,k}=u_{a,k}/(p^{e_{a,k}}m_{a,k})$, under the integrality and size conditions of (a). Let $\Lambda_k$ be the lcm of all $m_{a,j}$ with $j\le k$. Assume (S), $\lambda_k=o(f_k)$, and $k(p^{\max_ae_{a,k}}\Lambda_k)^r=o(n_k)$.

**Theorem C2b.** Then every nonconstant $P\in\mathbb Q[z_1,\ldots,z_m]$ of total degree at most $r$ gives a normal Liouville number $P(X_1,\ldots,X_m)$. In particular, $X_1,\ldots,X_m$ satisfy no nonzero rational polynomial relation of total degree at most $r$, and distinct nonconstant monomials of total degree at most $r$ have jointly uniformly distributed shifts. If moreover $\log(p^{\max_ae_{a,k}}\Lambda_k)=o(\log n_k)$ (so the period hypothesis holds for every $r\ge1$), then $X_1,\ldots,X_m$ are algebraically independent over $\mathbb Q$ and any finite list of distinct nonconstant monomials has jointly uniformly distributed shifts.

*Proof.* The Phase 19 OP-16 argument goes through unchanged, because the auxiliary moduli are $p$-units. A choice of monomial $\nu$ and new-occurrence vector $j\le\nu$ has depth $f_{k-1}\gamma\cdot\nu+\Delta_k\gamma\cdot j+O(1)$. The maximal $\gamma\cdot\nu$ is positive and unique. Since $\Delta_k=o(f_{k-1})$, any other monomial loses $f_{k-1}(\gamma\cdot\nu^*-\gamma\cdot\nu)-\Delta_k\gamma\cdot\nu\to\infty$. Within $\nu^*$ the best allowed $j$ wins by a multiple of $\Delta_k\to\infty$. The winning depth is at least $\gamma_{\min}f_{k-1}-O(1)$, and the grid loss is at most $a+\lambda_k=a+o(f_k)$, so $G\to\infty$. The rest of the proof is that of (a). $\square$

For example, $f_k=k^2$, $n_k=2^{k^3}$, $\gamma=(1,\sqrt2)$ and $m_{a,k}=\ell_k$ satisfy every hypothesis (including $\log(p^{\max_a e_{a,k}}\Lambda_k)=o(\log n_k)$).

### (c) Distinct protected primes plus auxiliary primes: Variant 2

Let $p_1,\ldots,p_m$ be distinct **odd** primes not dividing $b$, and let $m_{j,k}$ be coprime to $b\prod_ip_i$. Let $\theta_{i,-i}\in\mathbb Z_{p_i}^{m-1}$ be algebraically independent tuples, as in OP-17. Choose $C$ with $p_j^{Ck}\ge p_j\prod_{i\ne j}p_i^k$ for all $j$ and $k$, and put $E_k=Ck+E'_k$ with $E'_k\ge0$ nondecreasing and $E'_k-E'_{k-1}\to\infty$. Take the least positive $A_{j,k}$ with

$$
 A_{j,k}\equiv1\ \bmod p_j\operatorname{rad}(m_{j,k}),\qquad
 A_{j,k}\equiv p_j^{E_k}m_{j,k}b^{n_k}(\theta_{ij}-U_{j,k-1})\ \bmod p_i^{k}\quad(i\ne j),
$$

and put $V_{j,k}=A_{j,k}b^{-n_k}/(p_j^{E_k}m_{j,k})$. The second congruence is defined because $U_{j,k-1}$ is a $p_i$-integer: its denominators involve only $p_j$, the $m$'s and $b$. **Size check:** $A_{j,k}<p_j\operatorname{rad}(m_{j,k})\prod_{i\ne j}p_i^k\le p_j^{Ck}m_{j,k}\le p_j^{E_k}m_{j,k}$, so every weight lies in $(0,1]$. The coefficient has reduced denominator exactly $p_j^{E_k}m_{j,k}$, and $U_{j,k}\equiv\theta_{ij}\bmod p_i^k$.

**Theorem C2c.** Assume (S), $E_k-\lambda^{(i)}_k\to\infty$ for each $i$ (for instance $E_{k-1}-\lambda^{(i)}_k\to\infty$), where $\lambda^{(i)}_k=\max_{\ell\mid\Lambda_k}v_{p_i}(\operatorname{ord}_\ell b)$, and $k(\prod_ip_i^{E_k}\Lambda_k)^r=o(n_k)$. Then every nonconstant rational polynomial of degree at most $r$ in $X_1,\ldots,X_m$ is normal and Liouville.

*Proof.* OP-17's leading-term argument at a protected prime $p_i$ of a variable occurring in $P$ uses only $p_i$-adic information, and the auxiliary moduli are $p_i$-units. On retained shifts ($q\ge1$, $t=\min(q,l)\ge1$), it gives depth at least $qE_{k-1}+t(E_k-E_{k-1})-O_P(1)\ge E_k-O_P(1)$. In the complementary modulus at $p_i$ the other protected primes appear to high powers, yet they cost only $v_{p_i}(\operatorname{ord}_{p_{i'}^E}b)=v_{p_i}(\operatorname{ord}_{p_{i'}}b)$, a constant, because the order modulo $p_{i'}^E$ divides $p_{i'}^{E-1}\operatorname{ord}_{p_{i'}}b$. Hence $w\le a_i+\max(O(1),\lambda^{(i)}_k)$ and the grid grows. The rest of the proof is that of (a). $\square$

**Pitfall.** OP-17 used $E_k=Ck+\lfloor\log_2n_k\rfloor$. That choice fails the period hypothesis, since $\prod_ip_i^{rE_k}\ge n_k^r$. With a varying auxiliary support, the fixed-support kernel theorem behind OP-17 is unavailable, and complete periods must be $o(n_k)$. A depth like $E'_k=k^2$ on $n_k=2^{k^3}$ works. The protected primes must be odd, because the surviving-grid theorem uses odd-prime lifting.

## 8. Lean formalization and remaining targets

The denominator-protection core of Section 2 is **kernel-verified** in [`NormalityChecker/ProtectedPole.lean`](../../NormalityChecker/ProtectedPole.lean):

- `prime_pow_dvd_rat_den_of_repr` and `not_prime_pow_succ_dvd_rat_den_of_repr`: exact prime-power denominator divisibility from rational representations;
- `shifted_prefix_aux_prime_dvd_den`: divisibility of the shifted prefix denominator of $W$ by the newest auxiliary prime $\ell_k$;
- `shifted_prefix_protected_prime_pow_dvd_den`: exact $p$-adic valuation ($p^{e_k} \mid \operatorname{den}$ and $p^{e_k+1} \nmid \operatorname{den}$) for shifted prefixes of $W$;
- `truncated_poly_pole_dvd_den`: Lemma 1's lower bound $p^{l e_2 + (r-l)e_1 - g} \mid (\operatorname{truncatedPoly}\ a\ r\ l\ U\ V).\operatorname{den}$ under $1\le l\le r$ and $g<\min(e_1,e_2-e_1)$. Because the surviving-grid size $G=p^{\max(0,e-w)}$ is nondecreasing in $e=v_p(q_n)$, this divisibility lower bound is already sufficient for the surviving-grid exponent (while the upper bound on $q_n$ comes from the common tuple denominator).

Additional helper lemmas recommended for future formalization (not yet in Lean):

```lean
namespace NormalityChecker.ProtectedPole

/-- Truncated Taylor polynomial ∑_{i ≤ l} (hasseDeriv i P)(U) · V^i. -/
noncomputable def truncTaylor (P : Polynomial ℤ) (l : ℕ) (U V : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (l + 1), ((P.hasseDeriv i).map (Int.castRingHom ℚ)).eval U * V ^ i

/-- Lemma 1: the protected pole is exact once the depth gap beats the leading valuation. -/
theorem padicValRat_truncTaylor {p : ℕ} [Fact p.Prime] {P : Polynomial ℤ} {r l e₁ e₂ : ℕ}
    (hdeg : P.natDegree = r) (hl : 1 ≤ l) (hlr : l ≤ r) (h12 : e₁ < e₂) {U V : ℚ}
    (hU : padicValRat p U = -e₁) (hV : padicValRat p V = -e₂)
    (hgap : padicValInt p (P.leadingCoeff * r.choose l) < min e₁ (e₂ - e₁)) :
    padicValRat p (truncTaylor P l U V) =
      padicValInt p (P.leadingCoeff * r.choose l) - ((r - l) * e₁ + l * e₂ : ℕ)

/-- Shifted prefixes have denominators dividing the common tuple denominator. -/
theorem den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) {D : ℕ}
    (h : ∀ i ∈ s, (f i).den ∣ D) : (∑ i ∈ s, f i).den ∣ D

/-- Grid loss from an auxiliary prime. -/
theorem padicValNat_orderOf_le {p ℓ b : ℕ} [Fact ℓ.Prime] (hp : p.Prime) (hb : ¬ ℓ ∣ b) :
    padicValNat p (orderOf (b : ZMod ℓ)) ≤ padicValNat p (ℓ - 1)

/-- The other protected primes cost a bounded loss at every depth. -/
theorem padicValNat_orderOf_primePow {p q b E : ℕ} [Fact q.Prime] (hp : p.Prime) (hpq : p ≠ q)
    (hb : ¬ q ∣ b) (hE : 1 ≤ E) :
    padicValNat p (orderOf (b : ZMod (q ^ E))) = padicValNat p (orderOf (b : ZMod q))
```

`Polynomial.hasseDeriv`, `padicValRat.add_eq_of_lt` and `ZMod.orderOf_dvd_card_sub_one` supply most of the work for these remaining helper lemmas. The prefix estimate, the tail bound and the Liouville argument stay as written deductions.

## 9. Exact checks

`python -B scripts/phase20_normality.py` performs the following checks.

- **Theorem C1.** It recomputes 270 retained shifted prefixes of four polynomials of degree 1–3, with rational coefficients and $v_3(A)=2$ in one case, for five radix/prime pairs over shells 2–4. The positions $2^{k^3}$ are exact integers. It checks the window rule, the support, the newest prime and the surviving-grid loss bound at every prefix, and the exact pole formula at the 222 prefixes past the explicit threshold $k_1$. It verifies $q_n=p^{k^2}\ell_1\cdots\ell_k$ for $W$, and checks four full orbits by brute force against the $t$ grids of size $G$.
- **Theorem C2.** For Variant 1 it finds the predicted winning pole at 18 prefixes with $\gamma=(1,\sqrt2)$ and auxiliary primes. For Variant 2 it checks the CRT numerators: weights in $(0,1]$, exact reduced denominators $p_j^{E_k}\ell_k$, the programmed congruences, exact poles at both protected primes, and bounded grid loss.

[Checker](../../scripts/phase20_normality.py)
