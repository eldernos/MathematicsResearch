# Digit frequencies in the numerical kernel and signed coefficient transfer

Fix an integer radix $b\ge2$. For a real number $z$ put $x_n=\{b^nz\}$ and let $d_1d_2d_3\cdots$ be its base-$b$ digits, so $d_{n+1}=\lfloor bx_n\rfloor$. Let $D_N(z)=D_N(z;b)$ be the extreme discrepancy of $x_0,\dots,x_{N-1}$ over half-open intervals, and write $\delta_N(z)=1-D_N(z)$ for the *deficit*. The numerical translation kernel is $K_b=\{z:\ D_N(z)\to1\}$ ([Phase 19](../phase19/geometry.md)).

**Theorem A (digits in the kernel).** Let $b\ge2$, $L\ge1$ and $N\ge4$. If $\delta_N(z)<b^{-L-1}$, then exactly one of the following holds:

1. the words of length $L$ other than $0^L$ and $(b-1)^L$ have total frequency at most $\delta_N(z)$ among the first $N$ starts;
2. for one $m$ with $1\le m\le b-2$, the word $m^L$ has frequency at least $1-\delta_N(z)$.

Consequently, for $b\ge3$ **no element of $K_b$ is simply normal in base $b$**. For every $z\in K_b$ there is a single alternative valid for all $L$ and all large $N$. In the interior alternative every limit of the length-$L$ word distribution is the point mass at $m^L$. In the boundary alternative the limits are exactly the measures $\alpha\,\delta_{0^L}+(1-\alpha)\,\delta_{(b-1)^L}$, where $\alpha$ runs through the closed interval of limit points of the frequency of the digit $0$. Every closed subinterval of $[0,1]$ occurs, in every base.

**Theorem B (oriented tails).** Let $z=\sum_{m\ge1}a(m)b^{-m}$ with integer coefficients and $\sum|a(m)|b^{-m}<\infty$. Put $T_n=\sum_{m>n}a(m)b^{n-m}$. Then $x_n=\{T_n\}$. Among the first $N$ starts, the number of occurrences of $0^L$ differs from $\#\{n<N:\ T_n\ge0\}$ by at most $B'_L(N)=\#\{n<N:\ |T_n|\ge b^{-L}\}$, and the same holds for $(b-1)^L$ and $\#\{n<N:\ T_n<0\}$. On the gap preceding the $k$-th support point $m_k$, the tail is exactly $T_n=b^{n-m_k}V_k$ with $V_k=\sum_{i\ge k}a(m_i)b^{m_k-m_i}$. Hence its sign is the sign of $a(m_k)$ whenever the dominance inequality $\sum_{i>k}|a(m_i)|b^{m_k-m_i}<|a(m_k)|$ holds, and this inequality is sharp. When $|a|\le H$ for an integer $H\ge1$,

```math
\Bigl|\,f_{0^L}(N)-\frac{1}{N}\#\{n<N:\ T_n\ge0\}\Bigr|\ \le\ \frac{(L+\kappa_{b,H})\,(1+S(N-1))}{N},
```

with $S$ the support counting function, provided the support is not cofinite; here $\kappa_{b,H}=0$ for $H\le b-1$ (Corollary 6.4).

Theorems A and B are proved in Sections 1–8. Every proof is a complete paper proof. The finite statements are checked by exact arithmetic in [`scripts/phase22_simple_normality.py`](../../scripts/phase22_simple_normality.py) (Section 9). Section 10 lists Lean statements suggested for formalization; none is kernel-checked yet.

## 0. Conventions

*Cylinders and frequencies.* A word $w=w_1\cdots w_L$ over $\{0,\dots,b-1\}$ has value $v(w)=\sum_iw_ib^{L-i}$ and cylinder $C_w=[v(w)b^{-L},(v(w)+1)b^{-L})$. The word read at shift $n$ is $d_{n+1}\cdots d_{n+L}$. It equals $w$ exactly when $x_n\in C_w$, since $\lfloor b^Lx_n\rfloor=\sum_{i=1}^Ld_{n+i}b^{L-i}$. For $N\ge1$ put

```math
f_w(N)=\frac1N\#\{0\le n<N:\ x_n\in C_w\}.
```

Thus $z$ is simply normal in base $b$ if $f_d(N)\to1/b$ for every digit $d$, and normal if $f_w(N)\to b^{-L}$ for every word. "Other words" of length $L$ means words different from $0^L$ and $(b-1)^L$. The repunit $R_L=(b^L-1)/(b-1)$ satisfies $v(m^L)=mR_L$ and $v((b-1)^L)=b^L-1$. Since $(N+1)f_w(N+1)-Nf_w(N)=\epsilon\in\{0,1\}$, one has $f_w(N+1)-f_w(N)=(\epsilon-f_w(N))/(N+1)$ with $0\le f_w(N)\le1$, so

```math
|f_w(N+1)-f_w(N)|\le\frac1{N+1}. \tag{0.1}
```

*Circle.* $\mathbb T=\mathbb R/\mathbb Z$, and $\|t\|$ is the distance to the nearest integer. Multiplication by $b$ fixes exactly the points of $F_b=\{c_m=m/(b-1):\ 0\le m\le b-2\}\subset\mathbb T$. Since $b^nc_m-c_m=m(b^n-1)/(b-1)\in\mathbb Z$, one has $\|x_n-c_m\|=\|b^n(z-c_m)\|$. For $c\in\mathbb T$ and $r\ge0$ put

```math
E_c(N,r)=\#\{n<N:\ \|x_n-c\|>r\},\qquad E^{\ge}_c(N,r)=\#\{n<N:\ \|x_n-c\|\ge r\},
```

and $M_N(w)=N^{-1}\sum_{n<N}\|b^nw\|$. Phase 19 proves $K_b=\widetilde F_b+\{w:\ M_N(w)\to0\}$, where $\widetilde F_b=(b-1)^{-1}\mathbb Z$ lifts $F_b$. The proofs below use this decomposition only in Remark 3.5. The finite results of Sections 2–3 do not depend on it.

*Coefficient series.* For $a:\mathbb N\to\mathbb Z$ with $\sum|a(m)|b^{-m}<\infty$, write $F_b(a)=\sum_{m\ge1}a(m)b^{-m}$ (the Lean `coeffSeries`, whose term $m=0$ is an integer and is irrelevant here). Also put $S(X)=\#\{1\le m\le X:\ a(m)\ne0\}$, $A(X)=\sum_{1\le m\le X}|a(m)|$, and

```math
\widehat A(X)=\sum_{m\ge1}|a(m)|\min\bigl(1,b^{X-m}\bigr)=\Bigl(1-\frac1b\Bigr)\sum_{i\ge0}b^{-i}A(X+i).
```

The second expression follows by inserting $A(X+i)=\sum_{m\le X+i}|a(m)|$ and summing the geometric series over $i\ge\max(0,m-X)$.

## 1. Cylinder geometry of the fixed points

**Lemma 1.1 (interior fixed points).** Let $b\ge3$, $1\le m\le b-2$, $L\ge1$, and $c_m=m/(b-1)$. Then $c_m\in C_{m^L}$, and

```math
c_m-\frac{mR_L}{b^L}=\frac{m}{(b-1)b^L},\qquad \frac{mR_L+1}{b^L}-c_m=\frac{b-1-m}{(b-1)b^L}.
```

Put $\eta_{m,L}=\min(m,b-1-m)/((b-1)b^L)$. Every $t\in[0,1)$ with $\|t-c_m\|<\eta_{m,L}$ lies in $C_{m^L}$. Moreover $\eta_{m,L}\ge1/((b-1)b^L)$, with equality exactly when $m\in\{1,b-2\}$. The radius $\eta_{m,L}$ cannot be enlarged.

*Proof.* $b^Lc_m=mb^L/(b-1)=mR_L+m/(b-1)$, and $0<m/(b-1)<1$, so $\lfloor b^Lc_m\rfloor=mR_L$ with fractional part $m/(b-1)$. Dividing by $b^L$ gives both margins. Both margins are positive, and $\eta_{m,L}<\min(c_m,1-c_m)$. Hence for $t\in[0,1)$ the condition $\|t-c_m\|<\eta_{m,L}$ forces $|t-c_m|<\eta_{m,L}$, so $t$ lies strictly between the two endpoints of $C_{m^L}$. The minimum of $\min(m,b-1-m)$ over $1\le m\le b-2$ is $1$, attained exactly at $m=1$ and $m=b-2$. Finally, a point slightly beyond the nearer endpoint is at distance slightly more than $\eta_{m,L}$ and lies outside $C_{m^L}$ (the right endpoint itself is excluded). $\square$

For $L=1$ the margin is $\min(m,b-1-m)/(b(b-1))$, so the interior fixed point $c_m$ sits strictly inside the digit cell $[m/b,(m+1)/b)$. At an interior fixed point the direction of approach is invisible: all nearby points read the digit $m$ and the word $m^L$.

**Lemma 1.2 (the boundary fixed point).** For $t\in[0,1)$, $t\in C_{0^L}$ iff $t<b^{-L}$, and $t\in C_{(b-1)^L}$ iff $t\ge1-b^{-L}$. In particular, if $\|t\|<b^{-L}$ then $t$ reads $0^L$ when $t<1/2$ (approach to $0$ from above) and $(b-1)^L$ when $t>1/2$ (approach to $1$ from below). $\square$

The point $0\in\mathbb T$ is the only fixed point lying on the discontinuity of the digit map. It is therefore the only one at which nearby orbit points can split their mass between two words. Lemmas 1.1–1.2 are checked exactly for $3\le b\le12$, $1\le m\le b-2$, $1\le L\le4$ (220 cases).

## 2. Localizing the deficit at a fixed point

**Lemma 2.1 (concentration).** Call $J=\{t:\ \{t-\alpha\}<\ell\}$, $0\le\ell\le1$, a half-open arc of length $\ell$, and let $\mu_N(J)$ be the proportion of $n<N$ with $x_n\in J$.

(a) For every arc, $\delta_N(z)\le1-\mu_N(J)+\ell$.

(b) For every $\delta'>\delta_N(z)$ there is an arc with $1-\mu_N(J)+\ell<\delta'$.

*Proof.* (a) is the arc bound $\mu_N(J)-\ell\le D_N$ (Lean [`SharpTranslation.arc_le`](../../NormalityChecker/SharpTranslation.lean)). For (b), $1-\delta'<D_N$, so some interval $[a,c)$ has $|\text{frequency}-(c-a)|>1-\delta'$. By `SharpTranslation.interval_eq_arc_excess` this absolute deviation equals $\mu_N(J)-\ell$ for some arc $J$. $\square$

**Lemma 2.2 (localization).** Let $b\ge2$, $N\ge3$, and suppose $\delta=\delta_N(z)<\tfrac12-\tfrac1N$. Then there is $c\in F_b$ with

```math
E_c\Bigl(N,\ \frac{b}{b-1}\,\delta\Bigr)\ \le\ \delta N .
```

*Proof.* Fix $\delta'$ with $\delta<\delta'\le\frac12-\frac1N$. By Lemma 2.1(b) there is an arc $J$ of length $\ell$ with $e+\ell<\delta'$, where $e=1-\mu_N(J)$. Then $\ell<\frac12$, and every point of $J$ is within $\ell/2$ of the midpoint $c'$ of $J$. Let $G=\{n<N:\ x_n\in J\}$. Among $n\in\{0,\dots,N-2\}$ at most $eN$ have $n\notin G$ and at most $eN$ have $n+1\notin G$. So at least $N-1-2eN>N-1-2\delta'N\ge1$ of them have $x_n,x_{n+1}\in J$. Fix such an $n$. Multiplication by $b$ is $b$-Lipschitz for $\|\cdot\|$ and $x_{n+1}=bx_n\bmod1$, so

```math
\|(b-1)c'\|=\|bc'-c'\|\le\|bc'-bx_n\|+\|x_{n+1}-c'\|\le\frac{b\ell}2+\frac\ell2 .
```

Let $c\in F_b$ be nearest to $c'$ and $r=\|c'-c\|\le\frac1{2(b-1)}$. Write $c'=c+s$ with $|s|=r$. Then $(b-1)c'\equiv(b-1)s$ and $|(b-1)s|\le\frac12$, so $\|(b-1)c'\|=(b-1)r$. Hence $r\le(b+1)\ell/(2(b-1))$. For $n\in G$,

```math
\|x_n-c\|\le\frac\ell2+\frac{(b+1)\ell}{2(b-1)}=\frac{b\,\ell}{b-1}<\frac{b\,\delta'}{b-1}.
```

Therefore $E_c(N,b\delta'/(b-1))\le eN<\delta'N$, for some $c=c(\delta')\in F_b$. Take $\delta'_j\downarrow\delta$. Since $F_b$ is finite, one $c$ occurs for infinitely many $j$. The sets $\{n:\|x_n-c\|>b\delta'_j/(b-1)\}$ increase to $\{n:\|x_n-c\|>b\delta/(b-1)\}$, and they are finite, so they are eventually equal. Hence $E_c(N,b\delta/(b-1))\le\delta'_jN$ for all large $j$, which gives the claim. $\square$

**Proposition 2.3 (converse).** For every $c\in\mathbb T$, $r\ge0$ and $N\ge1$: $\delta_N(z)\le2r+E_c(N,r)/N$.

*Proof.* If $r\ge\frac12$ the right side is at least $1\ge\delta_N(z)$. If $r<\frac12$, apply Lemma 2.1(a) to the arc $[c-r,c+r+\eta)$ of length $2r+\eta\le1$ (for $0<\eta\le1-2r$), which contains the closed ball of radius $r$, and let $\eta\downarrow0$. $\square$

Together, Lemma 2.2 and Proposition 2.3 identify small deficit with concentration near one **fixed** point, at every finite $N$. The script tests Lemma 2.2 on 1060 prefixes: sparse series in $M_b$, the same series translated by every $c_m$, and 700 random "burst" numbers made of long runs of constant digits with noise. The hypothesis holds in 922 of them. The smallest admissible radius never exceeds $0.9091$ times $b\delta/(b-1)$ (a finite observation; see Question 11.1).

## 3. The digit and word dichotomy in $K_b$

**Proposition 3.1 (far counts and mean distance).** Let $z\in\mathbb R$, $N,L\ge1$, and let $w$ be any real number with $w\equiv z-c$ modulo $\mathbb Z$ for the relevant $c$.

(a) If $b\ge3$ and $c=c_m$ with $1\le m\le b-2$, then

```math
1-f_{m^L}(N)\ \le\ \frac{E^{\ge}_{c_m}(N,\eta_{m,L})}{N}\ \le\ \frac{M_N(w)}{\eta_{m,L}}\ \le\ (b-1)\,b^L\,M_N(w).
```

(b) For $c=0$,

```math
\sum_{w'\text{ other}}f_{w'}(N)\ \le\ \frac{E^{\ge}_0(N,b^{-L})}{N}\ \le\ b^LM_N(z).
```

For $0<\varepsilon\le b^{-L}$, let $P_\varepsilon(N)=\#\{n<N:0\le x_n<\varepsilon\}$ and $\overline P_\varepsilon(N)=\#\{n<N:1-\varepsilon<x_n<1\}$. Then

```math
P_\varepsilon(N)\le Nf_{0^L}(N)\le P_\varepsilon(N)+E^{\ge}_0(N,\varepsilon),\qquad
\overline P_\varepsilon(N)\le Nf_{(b-1)^L}(N)\le \overline P_\varepsilon(N)+E^{\ge}_0(N,\varepsilon).
```

*Proof.* (a) By Lemma 1.1, a shift with $\|x_n-c_m\|<\eta_{m,L}$ reads $m^L$. Markov's inequality applied to $\|x_n-c_m\|=\|b^nw\|$ gives the middle bound. (b) By Lemma 1.2 a shift with $\|x_n\|<b^{-L}$ reads $0^L$ or $(b-1)^L$. For the last pair note $[0,\varepsilon)\subseteq C_{0^L}$, and a point of $[\varepsilon,b^{-L})$ satisfies $\|x_n\|\ge\varepsilon$ because $b^{-L}\le\frac12$. The case of $(b-1)^L$ is symmetric. $\square$

**Theorem 3.2 (finite dichotomy).** Let $b\ge2$, $L\ge1$, $N\ge4$, and $\delta=\delta_N(z)<b^{-L-1}$. Then exactly one of the following holds:

- **(i) boundary:** $\sum_{w\text{ other}}f_w(N)\le\delta$;
- **(ii) interior** (only if $b\ge3$): for some $1\le m\le b-2$, $1-f_{m^L}(N)\le\delta$.

*Proof.* Since $\delta<b^{-L-1}\le\frac14\le\frac12-\frac1N$, Lemma 2.2 gives $c\in F_b$ with $E_c(N,r)\le\delta N$ for $r=b\delta/(b-1)<b^{-L}/(b-1)$. If $c=0$, then $r<b^{-L}$, so every shift with $\|x_n\|\le r$ reads $0^L$ or $(b-1)^L$ by Lemma 1.2, and (i) follows. If $c=c_m$, then $r<1/((b-1)b^L)\le\eta_{m,L}$, so every shift with $\|x_n-c_m\|\le r$ reads $m^L$ by Lemma 1.1, and (ii) follows. The alternatives are exclusive. Suppose (i) and (ii) both hold for some $m$. Since $m^L$ is an other word, $1-\delta\le f_{m^L}(N)\le\delta$, which is impossible for $\delta<\frac12$. Two interior alternatives $m\ne m'$ would give $f_{m^L}+f_{m'^L}\ge2-2\delta>1$. $\square$

**Corollary 3.3 (finite failure of simple normality).** Let $b\ge3$, $N\ge4$ and $\delta_N(z)<b^{-2}$. Then at least $b-2$ digits have total frequency at most $\delta_N(z)$ among $d_1,\dots,d_N$. In particular

```math
\max_{d}\Bigl|f_d(N)-\frac1b\Bigr|\ \ge\ \frac1b-\frac{\delta_N(z)}{b-2}.
```

*Proof.* Apply Theorem 3.2 with $L=1$. In case (i) the digits $1,\dots,b-2$ are other words. In case (ii) all $b-1$ digits different from $m$ have total frequency at most $\delta_N(z)$. Some digit therefore has frequency at most $\delta_N(z)/(b-2)$. $\square$

**Theorem 3.4 (classification in $K_b$).** Let $z\in K_b$.

(a) There is a single alternative, either (i) or (ii) with one fixed $m$, which holds in Theorem 3.2 for every $L\ge1$ and every sufficiently large $N$ (depending on $L$).

(b) In case (ii), $f_{m^L}(N)\to1$ for every $L$. The only limit of the length-$L$ word distribution is the point mass at $m^L$.

(c) In case (i), for every $L$,

```math
\sum_{w\text{ other}}f_w(N)\to0,\qquad f_{0^L}(N)-f_0(N)\to0,\qquad f_{(b-1)^L}(N)-f_{b-1}(N)\to0,\qquad f_0(N)+f_{b-1}(N)\to1 .
```

Let $\alpha_-=\liminf f_0(N)$ and $\alpha_+=\limsup f_0(N)$. The limits of the length-$L$ word distribution along subsequences are exactly the measures $\alpha\,\delta_{0^L}+(1-\alpha)\,\delta_{(b-1)^L}$ with $\alpha\in[\alpha_-,\alpha_+]$. Along any subsequence the same $\alpha$ serves for all $L$.

(d) For $b\ge3$, $z$ is not simply normal in base $b$. For every $b\ge2$, $z$ is not normal in base $b$: the frequency of the word $0(b-1)$ tends to $0$.

*Proof.* Since $\delta_N(z)\to0$, fix $L$ and choose $N_0\ge5$ with $\delta_N(z)<\min(b^{-L-1},\frac18)$ for $N\ge N_0$. Let $\mathcal A(N)$ be the unique alternative of Theorem 3.2. Suppose $\mathcal A(N)=$ (ii) with $m$. Then $f_{m^L}(N)\ge\frac78$, so $f_{m^L}(N+1)\ge\frac N{N+1}\cdot\frac78\ge\frac7{10}$. Any other alternative at $N+1$ would force $f_{m^L}(N+1)\le\delta_{N+1}<\frac18$. Now suppose $\mathcal A(N)=$ (i) and $\mathcal A(N+1)=$ (ii) with $m$. Then $(N+1)f_{m^L}(N+1)\le Nf_{m^L}(N)+1$ gives $f_{m^L}(N+1)\le\frac18+\frac15<\frac78$, a contradiction. So $\mathcal A$ is constant for $N\ge N_0$.

The constant alternative does not depend on $L$. If level $L$ has (ii) with $m$, then $1-f_m\le1-f_{m^L}\le\delta_N$, so level $1$ has (ii) with $m$. If level $L$ has (i), every $L$-word beginning with an interior digit is other, so $f_m(N)\le\delta_N$ for $1\le m\le b-2$, and level $1$ cannot be interior. This proves (a), and (b) follows with $\delta_N\to0$.

For (c), a start reading a word beginning with $0$ but different from $0^L$ reads an other word. Hence $0\le f_0(N)-f_{0^L}(N)\le\sum_{\text{other}}f_w(N)\le\delta_N$, and similarly for $b-1$. Also $f_0+f_{b-1}\ge f_{0^L}+f_{(b-1)^L}\ge1-\delta_N$. The limit points of $f_0(N)$ form the closed interval $[\alpha_-,\alpha_+]$. Indeed, by (0.1) the steps $|f_0(N+1)-f_0(N)|$ tend to $0$, so every value strictly between $\alpha_-$ and $\alpha_+$ is crossed infinitely often by arbitrarily small steps and is therefore a limit point; the set of limit points is closed. Combining the four displayed limits gives the description of the limit measures. Part (d) follows from (b), (c) and Corollary 3.3. $\square$

**Remark 3.5.** The alternative of Theorem 3.4 identifies the limiting fixed point $c\in F_b$ of Phase 19. If $z\in c_m+\{w:\ M_N(w)\to0\}$ with $m\ge1$ (this set is invariant under integer translation, so the lift of $c_m$ is irrelevant), Proposition 3.1(a) forces case (ii) with this $m$; if $z\in\{w:\ M_N(w)\to0\}$, Proposition 3.1(b) forces case (i). Every interval $[\alpha_-,\alpha_+]\subseteq[0,1]$ occurs in case (i) in every base (Theorem 8.2). In case (ii) the limit is always $\delta_{m^L}$, whatever the approach to $c_m$.

## 4. The binary kernel

In base 2, $F_2=\{0\}$, so only the boundary alternative exists.

**Theorem 4.1.** (a) Let $N\ge3$, $\delta=\delta_N(z)<\frac12-\frac1N$, and $2\delta<\varepsilon\le\frac12$. Then

```math
0\ \le\ f_0(N)-\frac{P_\varepsilon(N)}{N}\ \le\ \delta,\qquad P_\varepsilon(N)=\#\{n<N:\ 0\le x_n<\varepsilon\}.
```

If moreover $N\ge4$ and $\delta<2^{-L-1}$, then $|f_{0^L}(N)-f_0(N)|\le\delta$ and $|f_{1^L}(N)-f_1(N)|\le\delta$.

(b) For $z\in K_2$ the following are equivalent:

1. $z$ is simply normal in base 2;
2. $P_\varepsilon(N)/N\to\frac12$ for some $\varepsilon\in(0,\frac12]$;
3. $P_\varepsilon(N)/N\to\frac12$ for every $\varepsilon\in(0,\frac12]$;
4. $f_{0^L}(N)\to\frac12$ for some $L\ge1$;
5. $f_{0^L}(N)\to\frac12$ and $f_{1^L}(N)\to\frac12$ for every $L\ge1$.

If $z=F_2(a)$ and $B'_1(N)=o(N)$ (Section 5), these are further equivalent to:

6. $\#\{n<N:\ T_n\ge0\}/N\to\frac12$.

No $z\in K_2$ is normal in base 2: $f_{01}(N)\to0$.

*Proof.* (a) $Nf_0(N)-P_\varepsilon(N)=\#\{n<N:\varepsilon\le x_n<\frac12\}\le E_0(N,2\delta)\le\delta N$, by Lemma 2.2 with $F_2=\{0\}$ and $\varepsilon>2\delta$. The second statement is the inequality $0\le f_0-f_{0^L}\le\sum_{\text{other}}f_w\le\delta$ from the proof of Theorem 3.4(c), together with Theorem 3.2(i). (b) For $z\in K_2$, $\delta_N\to0$, so (a) applies to every fixed $\varepsilon$ for large $N$. This gives (1)⇔(2)⇔(3), and (1)⇔(4)⇔(5) by Theorem 3.4(c). Item (6) is Theorem 5.2(c) below with $L=1$. The last claim is Theorem 3.4(d). $\square$

So inside $K_2$, simple normality is exactly the statement that, at every scale, the orbit approaches $0$ from above and from below equally often. Euler's $E_2=\prod(1-2^{-k})$ is such a number ([Phase 20](../phase20/euler-product.md#2-word-frequencies)). Theorem 8.1 gives such numbers with any prescribed limit $\alpha$.

## 5. Oriented tails

**Lemma 5.1.** Let $a:\mathbb N\to\mathbb Z$ with $\sum|a(m)|b^{-m}<\infty$, $z=F_b(a)$ and $T_n=\sum_{m>n}a(m)b^{n-m}$. Then

```math
b^nz=\sum_{1\le m\le n}a(m)b^{n-m}+T_n,\qquad x_n=\{T_n\},\qquad T_n=\frac{a(n+1)+T_{n+1}}{b}.
```

*Proof.* The first sum is an integer. The recursion is the split of the series at $m=n+1$. $\square$

For $N,L\ge1$ let

```math
P_L(N)=\#\{n<N:\ 0\le T_n<b^{-L}\},\qquad Q_L(N)=\#\{n<N:\ -b^{-L}\le T_n<0\},\qquad B_L(N)=N-P_L(N)-Q_L(N),
```

and $B'_L(N)=\#\{n<N:\ |T_n|\ge b^{-L}\}$ and $\Gamma^+(N)=\#\{n<N:\ T_n\ge0\}$, $\gamma^+(N)=\Gamma^+(N)/N$. Here $B_L$ counts $T_n\notin[-b^{-L},b^{-L})$, so $B_L\le B'_L$, with difference $\#\{T_n=-b^{-L}\}$. Exact zero tails belong to $P_L$: if $T_n=0$ then $x_n=0$ reads $0^L$.

**Theorem 5.2 (finite oriented-tail transfer).** For all $N,L\ge1$:

(a) every $n$ counted by $P_L(N)$ reads $0^L$, and every $n$ counted by $Q_L(N)$ reads $(b-1)^L$;

(b) the following hold, together with the exact identity below them:

```math
P_L\le Nf_{0^L}\le P_L+B_L,\qquad Q_L\le Nf_{(b-1)^L}\le Q_L+B_L,\qquad N\sum_{w\text{ other}}f_w\le B_L,
```

```math
\bigl(Nf_{0^L}-P_L\bigr)+\bigl(Nf_{(b-1)^L}-Q_L\bigr)+N\sum_{w\text{ other}}f_w=B_L ;
```

(c) $|Nf_{0^L}(N)-\Gamma^+(N)|\le B'_L(N)$ and $|Nf_{(b-1)^L}(N)-(N-\Gamma^+(N))|\le B'_L(N)$.

*Proof.* (a) If $0\le T_n<b^{-L}$ then $x_n=T_n\in C_{0^L}$. If $-b^{-L}\le T_n<0$ then $x_n=1+T_n\in[1-b^{-L},1)=C_{(b-1)^L}$. (b) By (a), the starts not counted by $P_L+Q_L$ are exactly the $B_L$ remaining ones, and each of them reads some word; this gives the identity and the three inequalities. (c) $\Gamma^+=P_L+\#\{T_n\ge b^{-L}\}$, so $0\le\Gamma^+-P_L\le B'_L$, while $0\le Nf_{0^L}-P_L\le B_L\le B'_L$. Two numbers in $[0,B'_L]$ differ by at most $B'_L$. The same argument with $N-\Gamma^+=Q_L+\#\{T_n<-b^{-L}\}$ gives the second inequality. $\square$

**Theorem 5.3 (bad-tail count).** For all $N,L\ge1$ and integers $k\ge0$,

```math
B'_L(N)\ \le\ (L+k)\bigl(1+S(N-1)\bigr)+\frac{\widehat A(N+L+k)}{(b-1)\,b^k}.
```

*Proof.* Put $L'=L+k$ and $\tau(n)=\sum_{j>L'}|a(n+j)|b^{-j}$. If $a(n+1)=\dots=a(n+L')=0$ then $|T_n|\le\tau(n)$. So $B'_L(N)$ is at most the number $W$ of $n<N$ whose next occupied index lies in $(n,n+L']$, plus $\#\{n<N:\tau(n)\ge b^{-L}\}$.

For an occupied index $m\le N-1$, the shifts whose next occupied index is $m$ lie in $[m-L',m-1]$. All $n<N$ without occupied index in $(n,N-1]$ share one next occupied index $m^*\ge N$, if an occupied index $\ge N$ exists, and then lie in $[m^*-L',N-1]$; if none exists, these shifts are not shadowed and contribute $0$ to $W$. Hence $W\le L'(S(N-1)+1)$.

Next, $\sum_{n<N}\tau(n)=\sum_m|a(m)|\sum_{n<N,\ n\le m-L'-1}b^{n-m}\le\sum_m|a(m)|\,b^{-\max(L',m-N)}/(b-1)=\widehat A(N+L')/((b-1)b^{L'})$. Markov's inequality gives $\#\{\tau\ge b^{-L}\}\le b^L\sum\tau\le\widehat A(N+L+k)/((b-1)b^k)$. $\square$

This is the Phase 20 transfer argument ([Lemmas 1.2–1.3](../phase20/coefficient-transfer.md#11-integral-head-shadows-and-the-exact-mean-tail)) applied to the signed quantity $|T_n|$ instead of $\|b^nz\|$.

**Corollary 5.4 (rates).** Let $\rho_N=(1+S(N-1))/N$.

(a) If $A(X)\le CX$ for all $X\ge1$, then for all $N,L\ge1$,

```math
\frac{B'_L(N)}N\ \le\ \rho_N\Bigl(L+1+\log_b\frac1{\rho_N}+\frac C{b-1}\Bigl(1+\frac{L+3+\log_bN}{N}\Bigr)\Bigr).
```

(b) If $A(X)\le C(X+1)^r$ for all $X\ge0$ with an integer $r\ge1$, let $c_{b,r}=(1-\frac1b)\sum_{i\ge0}(1+i)^rb^{-i}$ and $k=\lceil\log_b((N+1)^{r-1}/\rho_N)\rceil$. Then

```math
\frac{B'_L(N)}N\ \le\ \rho_N\Bigl(L+1+\log_b\frac{(N+1)^{r-1}}{\rho_N}+\frac{C\,c_{b,r}}{b-1}\Bigl(\frac{N+L+k+1}{N+1}\Bigr)^r\frac{N+1}N\Bigr).
```

In both cases $|f_{0^L}(N)-\gamma^+(N)|$ and $|f_{(b-1)^L}(N)-(1-\gamma^+(N))|$ obey the same bounds. They tend to $0$ when $S(N)=o(N)$ in case (a) and when $S(N)\log N=o(N)$ in case (b). These are the sparsity hypotheses of the Lean theorems `linear_mass_sparse_tendsto_one` and `poly_mass_sparse_tendsto_one`.

*Proof.* (a) $\widehat A(X)\le C(1-\frac1b)\sum_ib^{-i}(X+i)=C(X+\frac1{b-1})$. Take $k=\lceil\log_b(1/\rho_N)\rceil$, so $b^k\ge1/\rho_N$ and $k\le\log_b(1/\rho_N)+1\le\log_bN+1$. Then insert into Theorem 5.3, using $N+L+k+\frac1{b-1}\le N+L+3+\log_bN$. (b) Since $X+1+i\le(X+1)(1+i)$, $\widehat A(X)\le Cc_{b,r}(X+1)^r$. With $b^k\ge(N+1)^{r-1}/\rho_N$ the second term of Theorem 5.3 divided by $N$ is at most the displayed one, and $L+k\le L+1+\log_b((N+1)^{r-1}/\rho_N)$. The bound on $|f-\gamma^+|$ is Theorem 5.2(c). In (b), $k=O_r(\log N)$, so the parenthesis is $O_{b,r,C,L}(\log N)$. $\square$

The logarithmic-mass hypothesis $A(X)\le CX(\log(X+2))^\gamma$ of `log_mass_sparse_tendsto_one` is handled the same way, with $k=\lceil\log_b((\log(N+2))^\gamma/\rho_N)\rceil$. Then $k=\gamma\log_b\log(N+2)+\log_b(1/\rho_N)+O(1)$, and Theorem 5.3 gives

```math
\frac{B'_L(N)}N=O\Bigl(\rho_N\Bigl(\log\frac1{\rho_N}+\log\log(N+3)\Bigr)\Bigr).
```

The term $\rho_N\log(1/\rho_N)$ cannot be dropped in general. For $\gamma=1$, $b=2$ and $L=1$, the single coefficient $a(N+1)=\lfloor N\log(N+2)\rfloor$ satisfies the mass hypothesis with $C=1$ and has $\rho_N=1/N$, yet $B'_1(N)=\lfloor\log_2a(N+1)\rfloor+1\sim\log_2N$. The bound still tends to $0$ whenever $S(N)\log\log N=o(N)$, since then $\rho_N\to0$ and $\rho_N\log(1/\rho_N)\to0$. This case is recorded as a remark, with the computation only sketched.

*Representation dependence.* Every real number has many integer-coefficient representations; its own digits give $a(m)\in[0,b-1]$ and $T_n=x_n\ge0$. The word frequencies do not depend on the representation, while $\Gamma^+$ and $B'_L$ do. Theorem 5.2 says that any representation with few bad tails computes the frequencies of $0^L$ and $(b-1)^L$ from its signs. The sign information is useful only for sparse signed representations.

## 6. Gap-exact tails and sign determination

Let $m_1<m_2<\cdots$ be the support of $a$ (finite or infinite) and $m_0=0$. Put $G_k=\{n:\ m_{k-1}\le n<m_k\}$, $g_k=m_k-m_{k-1}$, and

```math
V_k=\sum_{i\ge k}a(m_i)\,b^{m_k-m_i}=a(m_k)+T_{m_k},\qquad R^*_k=\sum_{i>k}|a(m_i)|\,b^{m_k-m_i}.
```

If the support is finite with last point $m_K$, put $G_{K+1}=\{n\ge m_K\}$, $V_{K+1}=0$ and $g_{K+1}=\infty$, with $\min(\infty,0)=0$; then $T_n=0$ on $G_{K+1}$, and $R^*_K=0$. For $L\ge1$ let $\lambda_k=\max(0,\lfloor L+\log_b|V_k|\rfloor)$, with $\lambda_k=0$ when $V_k=0$.

**Proposition 6.1 (gap-exact tails).** For $n\in G_k$ with $k$ an index of a support point ($k\le K$ when the support has $K$ points),

```math
T_n=b^{-(m_k-n)}\,V_k .
```

Hence $T_n$ has the sign of $V_k$ throughout $G_k$, and $|T_n|$ is nondecreasing in $n$ (strictly increasing when $V_k\ne0$). On the trailing gap $G_{K+1}$ of a finite support, $T_n=0$. The shifts $n\in G_k$ with $|T_n|\ge b^{-L}$ are exactly those with $m_k-n\le\lambda_k$: they are the last $\min(g_k,\lambda_k)$ shifts of the gap.

*Proof.* For $n\in G_k$ the coefficients $a(m)$ with $n<m<m_k$ vanish, so $T_n=\sum_{i\ge k}a(m_i)b^{n-m_i}=b^{n-m_k}V_k$. With $j=m_k-n\in\{1,\dots,g_k\}$, $|T_n|\ge b^{-L}$ iff $|V_k|\ge b^{j-L}$ iff $j\le L+\log_b|V_k|$ iff $j\le\lambda_k$. $\square$

**Lemma 6.2 (dominance, with sharpness).** Fix $k$.

(a) $|V_k-a(m_k)|\le R^*_k$.

(b) Suppose $m_{k+1}$ exists (otherwise $R^*_k=0$). If $|a(m)|\le H$ for all $m>m_k$, then $R^*_k\le Hb^{1-g_{k+1}}/(b-1)$, with equality only if $|a(m)|=H$ for every $m\ge m_{k+1}$.

(c) If $R^*_k<|a(m_k)|$, then $V_k$ has the sign of $a(m_k)$ and $0<|V_k|<2|a(m_k)|$. This holds in particular if $Hb^{1-g_{k+1}}\le(b-1)|a(m_k)|$ and some $m\ge m_{k+1}$ has $|a(m)|<H$. For instance it holds at every $k$ when $|a|\le b-1$ and the support is not cofinite.

(d) The threshold in (c) is sharp. For every $b\ge2$, $g\ge1$ and integer $H>(b-1)b^{g-1}$ there is a finitely supported $a$ with $a(m_k)=1$, $g_{k+1}=g$, $|a|\le H$ and $V_k<0$. For $H=(b-1)b^{g-1}$ and $a(m)=-H$ for all $m\ge m_k+g$, one has $V_k=0$.

*Proof.* (a) is the triangle inequality. (b) The positions after $m_k$ are $m_k+j$ with $j\ge g_{k+1}$, so $R^*_k\le H\sum_{j\ge g_{k+1}}b^{-j}=Hb^{1-g_{k+1}}/(b-1)$, with equality iff every such position has $|a|=H$. (c) follows from (a), (b) and $|a(m_k)|\ge1$. (d) Put $a(m_k)=1$ and $a(m_k+g+i)=-H$ for $0\le i<J$. Then

```math
V_k=1-\frac{H\,b^{1-g}}{b-1}\bigl(1-b^{-J}\bigr),
```

which is negative for large $J$ because $Hb^{1-g}/(b-1)>1$. The case $J=\infty$, $H=(b-1)b^{g-1}$ gives $V_k=0$. $\square$

The script finds the sign reversal of (d) with $J=2,2,3$ for $g=1,2,3$ in each of the bases $2$, $3$ and $10$.

**Theorem 6.3 (gap-weighted frequency formula).** For all $N,L\ge1$,

```math
\Gamma^+(N)=\sum_{k\ge1}|G_k\cap[0,N)|\cdot\mathbf 1[V_k\ge0],\qquad
B'_L(N)\le\sum_{k\ge1,\ m_{k-1}<N}\min(g_k,\lambda_k),
```

with equality in the second relation when $N=m_K$ for some $K$. Consequently

```math
\Bigl|f_{0^L}(N)-\gamma^+(N)\Bigr|,\ \ \Bigl|f_{(b-1)^L}(N)-\bigl(1-\gamma^+(N)\bigr)\Bigr|,\ \ \sum_{w\text{ other}}f_w(N)\ \ \le\ \frac1N\sum_{k:\ m_{k-1}<N}\min(g_k,\lambda_k).
```

Suppose dominance (Lemma 6.2(c)) holds for all support indices $k>k_0$. Then $\mathbf 1[V_k\ge0]=\mathbf 1[a(m_k)>0]$ for these $k$. If the support is infinite, or finite with last point $m_K$ and $N\le m_K$, then $\Gamma^+(N)$ is within $m_{k_0}$ of the number of $n<N$ whose next nonzero coefficient is positive. If the support is finite and $N>m_K$, the $N-m_K$ shifts $n\in[m_K,N)$ have $T_n=0$; they are counted in $\Gamma^+(N)$ through $G_{K+1}$ but have no next nonzero coefficient, so the comparison holds with error $m_{k_0}+N-m_K$.

*Proof.* Combine Proposition 6.1 with Theorem 5.2(c). In a gap meeting $[0,N)$ only partially, the bad shifts in $[0,N)$ form a final segment of $G_k\cap[0,N)$ of length at most $\min(g_k,\lambda_k)$. Every gap below $m_K$ is complete when $N=m_K$. $\square$

**Corollary 6.4 (bounded coefficients).** Suppose $|a(m)|\le H$ for all $m$, with an integer $H\ge1$, and the support is not cofinite. Let $\kappa_{b,H}=\lceil\log_b(bH/(b-1))\rceil-1$, so that $\kappa_{b,H}=0$ exactly when $H\le b-1$. Then $\lambda_k\le L+\kappa_{b,H}$ for all $k$, and for all $N,L\ge1$,

```math
B'_L(N)\le(L+\kappa_{b,H})\,(1+S(N-1)),\qquad \Bigl|f_{0^L}(N)-\gamma^+(N)\Bigr|\le\frac{(L+\kappa_{b,H})(1+S(N-1))}N .
```

*Proof.* Some $m>m_k$ has $a(m)=0$, so Lemma 6.2(b) holds strictly, and $|V_k|<H+H/(b-1)=bH/(b-1)$. Hence $L+\log_b|V_k|<L+\kappa_{b,H}+1$ and $\lambda_k\le L+\kappa_{b,H}$. The gaps meeting $[0,N)$ are indexed by $m_{k-1}\in\{0\}\cup\{\text{support}\cap[1,N-1]\}$, which gives $1+S(N-1)$ of them. Since $H\ge1$, $bH/(b-1)>1$ and $\kappa_{b,H}\ge0$. Also $\kappa_{b,H}=0$ iff $bH/(b-1)\le b$ iff $H\le b-1$. $\square$

**Proposition 6.5 (exactness and sharpness of the rate).** (a) If $|T_n|<1-b^{-L}$ for all $n<N$, then

```math
Nf_{0^L}(N)=P_L(N),\qquad Nf_{(b-1)^L}(N)=Q_L(N),\qquad N\sum_{w\text{ other}}f_w(N)=B_L(N).
```

(b) Let $b\ge3$ and $a(m_k)=\pm1$ for all $k$. Then (a) applies for every $L\ge1$, and $L-1\le\lambda_k\le L$ for every $k$. Hence, for $N=m_K$,

```math
\sum_{k\le K}\min(g_k,L-1)\ \le\ N\sum_{w\text{ other}}f_w(N)\ \le\ \sum_{k\le K}\min(g_k,L).
```

In particular, when the gaps are eventually at least $L$, the other-word frequency at $N=m_K$ lies between $(L-1)(K-C)/N$ and $LK/N$ for a constant $C$, so it has exact order $S(N)/N$ for every $L\ge2$.

*Proof.* (a) A bad start has $T_n\in[b^{-L},1-b^{-L})$ or $T_n\in(-1+b^{-L},-b^{-L})$, so $x_n\in[b^{-L},1-b^{-L})$ reads an other word. The good starts read $0^L$ or $(b-1)^L$ by Theorem 5.2(a). (b) $|T_n|\le\sum_{j\ge1}b^{-j}=\frac1{b-1}\le\frac12<1-b^{-L}$. Also $|V_k|\in[1-\frac1{b-1},1+\frac1{b-1}]\subset(\frac1b,b)$, so $\log_b|V_k|\in(-1,1)$ and $\lambda_k\in\{L-1,L\}$. By (a), the other-word count is $B_L(N)$. A shift $n\in G_k$ with $m_k-n\le L-1$ has $|T_n|=|V_k|b^{-(m_k-n)}>b^{-L}$, so it is counted by $B_L$; this gives the lower bound. The upper bound is $B_L\le B'_L\le\sum_{k\le K}\min(g_k,\lambda_k)$ from Theorem 6.3. $\square$

**Proposition 6.6 (two-digit expansions).** Let the support be infinite with $|a(m_k)|=1$ and alternating signs, $a(m_{k+1})=-a(m_k)$ for all $k$. Assume $b\ge3$, or $b=2$ and the support is not cofinite. Then $0<|T_n|<b^{-1}$ for every $n\ge0$. Every digit of $z$ is $0$ or $b-1$, $d_{n+1}=0$ iff $T_n>0$, and $Nf_0(N)=\Gamma^+(N)$ exactly for every $N$.

*Proof.* By Lemma 6.2(c) with $H=1\le b-1$, $V_k$ has the sign of $a(m_k)$ for every $k$ (for $b\ge3$ directly, since $R^*_k\le\frac1{b-1}<1$). Then $T_{m_k}=b^{-g_{k+1}}V_{k+1}$ has the sign opposite to $a(m_k)$ and absolute value below $1$. Hence $|V_k|=1-|T_{m_k}|\in(0,1)$, and Proposition 6.1 gives $0<|T_n|<b^{-(m_k-n)}\le b^{-1}$ for $n\in G_k$. So $x_n\in(0,1/b)$ or $x_n\in(1-1/b,1)$ according to the sign of $T_n$. $\square$

**Theorem 6.7 (asymptotic transfer).** If $B'_L(N)=o(N)$ for every $L$, then $z\in K_b$ in the boundary case, and for every $L$,

```math
f_{0^L}(N)-\gamma^+(N)\to0,\qquad f_{(b-1)^L}(N)-\bigl(1-\gamma^+(N)\bigr)\to0,\qquad\sum_{w\text{ other}}f_w(N)\to0 .
```

The set of limit points of $f_{0^L}(N)$ equals that of $\gamma^+(N)$ for every $L$. In base 2, $z$ is simply normal iff $\gamma^+(N)\to\frac12$. The hypothesis holds under bounded coefficients and $S(X)=o(X)$ (Corollary 6.4), linear mass and $S(X)=o(X)$, or polynomial mass and $S(X)\log X=o(X)$ (Corollary 5.4).

*Proof.* The three limits are Theorem 5.2(c) and (b). The shifts with $|T_n|<b^{-L}$ satisfy $\|x_n\|<b^{-L}$, so $E^{\ge}_0(N,b^{-L})\le B'_L(N)=o(N)$ for each $L$. Proposition 2.3 then gives $\delta_N\to0$, so $z\in K_b$. Since $\sum_{w\text{ other}}f_w(N)\to0$, the interior alternative $f_{m^L}(N)\to1$ of Theorem 3.4 is excluded, and the boundary case holds. $\square$

## 7. Specializations

**Corollary 7.1 (nonnegative coefficients).** If $a(m)\ge0$ for all $m$, then $T_n\ge0$ for all $n$, and

```math
1-f_{0^L}(N)\ \le\ \frac{\#\{n<N:\ T_n\ge b^{-L}\}}{N}\ \le\ \frac{B'_L(N)}N .
```

If also $|a|\le H$ for an integer $H\ge1$ and the support is not cofinite, the right side is at most $(L+\kappa_{b,H})(1+S(N-1))/N$. If $B'_L(N)=o(N)$ for every $L\ge1$, then $f_{0^L}(N)\to1$ for every $L$, and $z$ is not simply normal in base $b$, for every $b\ge2$ including $b=2$.

*Proof.* $Nf_{0^L}\ge P_L=N-\#\{T_n\ge b^{-L}\}$ by Theorem 5.2(b). $\square$

Without a sparsity hypothesis nonnegativity says nothing: digit expansions are nonnegative representations of arbitrary numbers. The conclusion concerns the radix $b$ of the series only.

*Examples.* For $\Theta(1/b)-1=\sum_{k\ge1}b^{-k^2}$ and $b\ge3$, Proposition 6.5(a) applies, and $V_k\in[1,b/(b-1))$ gives $\lambda_k=L$ exactly. Hence at $N=K^2$

```math
1-f_{0^L}(K^2)=\frac1{K^2}\sum_{k\le K}\min(2k-1,L),\qquad f_{(b-1)^L}(K^2)=0,
```

for example $f_0(10^4)=0.99$ and $f_{000}(10^4)=1-298/10^4=0.9702$ (Table 7.1). The same rate $L(1+\lfloor\sqrt{N-1}\rfloor)/N$ holds in base 2 by Corollary 6.4. For $\Theta_3(1/b)-1=\sum2b^{-k^2}$ one has $H=2$, $\kappa_{2,2}=1$ and $\kappa_{b,2}=0$ for $b\ge3$. For the prime constant $\sum_pb^{-p}$, Corollary 7.1 gives $1-f_{0^L}(N)\le L(1+\pi(N-1))/N$.

**Theorem 7.2 (periodic signs, regularly growing gaps).** Assume $B'_L(N)=o(N)$ for every $L$, and that for some period $p\ge1$ and all large $k$:

- $V_k$ has sign $\varepsilon_{k\bmod p}\in\{\pm1\}$ (for example by Lemma 6.2(c) when $a(m_k)$ has sign $\varepsilon_{k\bmod p}$);
- $g_k=\theta_{k\bmod p}\,\varphi(k)+o(\varphi(k))$, where $\varphi>0$, $\varphi(k+1)/\varphi(k)\to1$, $\sum_k\varphi(k)=\infty$, $\theta_r\ge0$ and $\Theta=\sum_r\theta_r>0$.

Then, for every $L\ge1$,

```math
f_{0^L}(N)\ \longrightarrow\ \alpha=\frac{1}{\Theta}\sum_{r:\ \varepsilon_r=+1}\theta_r,\qquad f_{(b-1)^L}(N)\longrightarrow1-\alpha .
```

*Proof.* Let $\Phi(K)=\sum_{k\le K}\varphi(k)$. Since $\varphi(k+i)/\varphi(k)\to1$ for each fixed $i<p$, pairing $k\equiv r$ with $k+i\equiv r'$ shows that the residue sums $\sum_{k\le K,\ k\equiv r}\varphi(k)$ differ pairwise by $o(\Phi(K))+O(\max_{|k-K|\le p}\varphi(k))$. This is $o(\Phi(K))$, because $\varphi(K)\le(1+o(1))\varphi(K-j)$ for $j\le J$ gives $\varphi(K)=o(\Phi(K))$. As the residue sums add up to $\Phi(K)$, each equals $\Phi(K)/p+o(\Phi(K))$. Since $\Phi\to\infty$, the $o(\varphi(k))$ errors sum to $o(\Phi(K))$. Hence

```math
m_K=\frac{\Theta}{p}\Phi(K)+o(\Phi(K)),\qquad \Gamma^+(m_K)=\frac{\Phi(K)}{p}\sum_{\varepsilon_r=+1}\theta_r+o(\Phi(K)),
```

using Theorem 6.3 for the second sum, with the finitely many early gaps contributing $O(1)$. For $m_K\le N<m_{K+1}$, $|\Gamma^+(N)-\Gamma^+(m_K)|\le g_{K+1}=o(\Phi(K))$, so $\gamma^+(N)\to\alpha$. Theorem 6.7 completes the proof. $\square$

*Examples.*

1. **Euler's product.** $E_b-1=\sum_{k\ge1}(-1)^k(b^{-P_k^-}+b^{-P_k^+})$ with $P_k^\pm=k(3k\pm1)/2$. Index the support by $j$, with $m_{2k-1}=P_k^-$ and $m_{2k}=P_k^+$. Then $g_{2k-1}=2k-1$ and $g_{2k}=k$, so $\varphi(j)=j$ and $p=4$. The residues $j\equiv1,2,3,0\pmod4$ have $\theta=1,\frac12,1,\frac12$ and signs $-,-,+,+$. Hence $\alpha=\frac12$. Dominance holds at every $k$ for every $b\ge2$ by Lemma 6.2(c). This recovers the limiting frequencies of [Phase 20, Theorem 2](../phase20/euler-product.md#2-word-frequencies).
2. **Jacobi's cube.** $E_b^3-1=\sum_{k\ge1}(-1)^k(2k+1)b^{-k(k+1)/2}$, with $g_k=k$ and alternating signs, so $\alpha=\frac12$. Dominance holds at every $k\ge1$ and every $b\ge2$. Indeed $m_{k+j}-m_k\ge j(k+1)$, so $R^*_k\le\sum_{j\ge1}(2k+1+2j)4^{-j}=\frac{2k+1}3+\frac89<2k+1$. Here $A(X)\le4X$, so Corollary 5.4(a) applies.
3. **Signed two-progressions: every rational $\alpha\in(0,1)$.** For integers $0<t<s$ with $s\equiv t\pmod2$ put $u_k=(sk^2-tk)/2$ and $v_k=(sk^2+tk)/2$. Take $a(v_k)=+1$ and $a(u_k)=-1$. Then $v_k-u_k=tk$ and $u_{k+1}-v_k=(s-t)(2k+1)/2$, so $\theta_{\rm even}=t/2$ (sign $+$) and $\theta_{\rm odd}=(s-t)/2$ (sign $-$) with $\varphi(j)=j$. Hence

```math
f_{0^L}(N)\to\alpha=\frac ts .
```

Every rational $p/q\in(0,1)$ is $t/s$ with $t=2p$, $s=2q$. Consecutive signs alternate, so by Proposition 6.6 these numbers use only the digits $0$ and $b-1$, and $Nf_0(N)=\Gamma^+(N)$ exactly. The case $s=3$, $t=1$ is the pentagonal support with signs $+$ on $P_k^+$ and $-$ on $P_k^-$; it has $\alpha=\frac13$.
4. **Periodic signs on squares.** For $a(k^2)=\varepsilon_{k\bmod p}$, $g_k=2k-1$ and $\alpha$ is the proportion of $+1$ in one period. For example $(+,-,-)$ gives $\frac13$ and $(+,+,-,-,-)$ gives $\frac25$.

**Theorem 7.3 (geometric gaps).** Assume $B'_L(N)=o(N)$ for every $L$, $g_k=\theta\lambda^k(1+o(1))$ with $\theta>0$ and $\lambda>1$, and that the signs of $V_k$ alternate for large $k$. Then for every $L$ the set of limit points of $f_{0^L}(N)$ is

```math
\Bigl[\frac1{1+\lambda},\ \frac\lambda{1+\lambda}\Bigr].
```

*Proof.* By Stolz–Cesàro, $\sum_{k\le K}g_k\sim\theta\lambda^{K+1}/(\lambda-1)$ and $\sum_{k\le K,\ k\equiv K\ (2)}g_k\sim\theta\lambda^{K+2}/(\lambda^2-1)$. Thus $\gamma^+(m_K)\to\lambda/(1+\lambda)$ along the $K$ with $V_K>0$, and $\gamma^+(m_K)\to1/(1+\lambda)$ along those with $V_K<0$. On each gap $\gamma^+$ is monotone, since $\gamma^+(N+1)-\gamma^+(N)=(\mathbf 1[T_N\ge0]-\gamma^+(N))/(N+1)$ and the indicator is constant on the gap. So $\gamma^+$ stays between consecutive endpoint values. By (0.1), applied to $\gamma^+$, the limit set is the whole interval. Theorem 6.7 transfers it to $f_{0^L}$. $\square$

For example $\sum_{k\ge1}(-1)^kb^{-2^k}$ has $g_k=2^{k-1}$ for $k\ge2$, so $\lambda=2$. Exactly, $\Gamma^+(2^K)=(2^{K+1}-2)/3$ for even $K$ and $(2^K-2)/3$ for odd $K$. By Proposition 6.6 its digits are all $0$ or $b-1$, and $f_0(N)=\gamma^+(N)$, whose limit set is $[\frac13,\frac23]$, in every base.

**Table 7.1** (exact, $N=10^4$, certified for the infinite series; Section 9).

| series | $b$ | $\alpha$ | $f_0$ | $f_{b-1}$ | $f_{000}$ | $f_{(b-1)^3}$ | $\gamma^+$ | $B'_1/N$ |
|---|---|---|---|---|---|---|---|---|
| $\sum b^{-k^2}$ | 2 | 1 | 0.9900 | 0.0100 | 0.9702 | 0.0000 | 1.0000 | 0.0100 |
| $\sum b^{-k^2}$ | 10 | 1 | 0.9900 | 0.0000 | 0.9702 | 0.0000 | 1.0000 | 0.0100 |
| $\Theta_3(1/b)-1$ | 2 | 1 | 0.9901 | 0.0099 | 0.9703 | 0.0000 | 1.0000 | 0.0199 |
| $\Theta_3(1/b)-1$ | 3 | 1 | 0.9900 | 0.0100 | 0.9702 | 0.0000 | 1.0000 | 0.0100 |
| $E_b$ | 2 | 1/2 | 0.4999 | 0.5001 | 0.4798 | 0.4800 | 0.4998 | 0.0081 |
| $E_b$ | 3 | 1/2 | 0.4958 | 0.4961 | 0.4798 | 0.4800 | 0.4998 | 0.0081 |
| $E_b$ | 10 | 1/2 | 0.4958 | 0.4961 | 0.4798 | 0.4800 | 0.4998 | 0.0081 |
| $E_b^3$ | 2 | 1/2 | 0.5038 | 0.4962 | 0.4460 | 0.4455 | 0.4970 | 0.1011 |
| $E_b^3$ | 10 | 1/2 | 0.4812 | 0.4869 | 0.4647 | 0.4709 | 0.4970 | 0.0367 |
| two-progression $s=3,t=1$ | 2 | 1/3 | 0.3321 | 0.6679 | 0.3160 | 0.6518 | 0.3321 | 0.0000 |
| two-progression $s=3,t=1$ | 3 | 1/3 | 0.3321 | 0.6679 | 0.3160 | 0.6518 | 0.3321 | 0.0000 |
| two-progression $s=10,t=4$ | 2 | 2/5 | 0.3960 | 0.6040 | 0.3872 | 0.5952 | 0.3960 | 0.0000 |
| same, signs swapped | 2 | 3/5 | 0.6040 | 0.3960 | 0.5952 | 0.3872 | 0.6040 | 0.0000 |
| squares, signs $(+,-,-)$ | 2 | 1/3 | 0.3433 | 0.6567 | 0.3333 | 0.6435 | 0.3400 | 0.0033 |
| squares, signs $(+,+,-,-,-)$ | 2 | 2/5 | 0.3900 | 0.6100 | 0.3782 | 0.5960 | 0.3880 | 0.0060 |

The rows for the two-progressions have $B'_1=0$ and $f_0=\gamma^+$, as Proposition 6.6 predicts. For the lacunary series $\sum(-1)^kb^{-2^k}$, in bases 2 and 3, $\gamma^+(2^K)=f_0(2^K)$ equals $0.66602$, $0.33301$, $0.66650$, $0.33325$, $0.66663$ for $K=10,\dots,14$. These agree with the exact formula above.

## 8. Prescribed frequencies

For $\alpha\in[0,1]$ let $\beta_\alpha(k)=\lfloor k\alpha\rfloor-\lfloor(k-1)\alpha\rfloor\in\{0,1\}$ (the Beatty indicator).

**Lemma 8.0.** For every real $\alpha$ and $K\ge1$,

```math
\sum_{k=1}^K\beta_\alpha(k)(2k-1)=\alpha K^2+E,\qquad E=2\sum_{k=1}^{K-1}\{k\alpha\}-(2K-1)\{K\alpha\},\qquad |E|<2K-1 .
```

*Proof.* Abel summation with $B(k)=\lfloor k\alpha\rfloor$ gives $\sum_{k\le K}\beta_\alpha(k)(2k-1)=(2K-1)B(K)-2\sum_{k<K}B(k)$. Substitute $B(k)=k\alpha-\{k\alpha\}$. The first sum in $E$ lies in $[0,2K-2]$ and the second term in $[0,2K-1)$. $\square$

**Theorem 8.1 (prescribed limit).** Let $b\ge2$, $\alpha\in[0,1]$, and

```math
z_\alpha=\sum_{k\ge1}\varepsilon_k\,b^{-k^2},\qquad \varepsilon_k=2\beta_\alpha(k)-1 .
```

Then $z_\alpha\in K_b$, and for all $N,L\ge1$,

```math
\bigl|f_{0^L}(N)-\alpha\bigr|\le\frac{(L+4)\sqrt N+L}{N},\qquad \bigl|f_{(b-1)^L}(N)-(1-\alpha)\bigr|\le\frac{(L+4)\sqrt N+L}{N}.
```

In particular $z_{1/2}$ is simply normal in base 2 but not normal, and $z_\alpha$ is not simply normal in base $b\ge3$.

*Proof.* The coefficients are $\pm1$ and the support (the squares) is not cofinite. So Lemma 6.2(c) shows that $V_k$ has the sign of $\varepsilon_k$, and Corollary 6.4 with $\kappa_{b,1}=0$ gives $B'_L(N)\le L(1+\lfloor\sqrt{N-1}\rfloor)$. The gap $G_k=[(k-1)^2,k^2)$ has length $2k-1$. With $K=\lfloor\sqrt N\rfloor$, Lemma 8.0 gives $|\Gamma^+(K^2)-\alpha K^2|<2K-1$. Since $\Gamma^+(N)-\Gamma^+(K^2)=(N-K^2)\beta_\alpha(K+1)$ and $0\le N-K^2\le2K$, we get $|\Gamma^+(N)-\alpha N|<4K\le4\sqrt N$. Theorem 6.3 then gives the bounds. Membership in $K_b$ follows from bounded coefficients and $S(X)=\lfloor\sqrt X\rfloor=o(X)$ ([Phase 20](../phase20/coefficient-transfer.md); Lean `linear_mass_sparse_tendsto_one`), or from Theorem 6.7. $\square$

**Theorem 8.2 (prescribed interval of limit points).** Let $0\le\alpha_-\le\alpha_+\le1$, $b\ge2$, $K_0=0$ and $K_i=2^{i^2}$ for $i\ge1$. For $K_i<k\le K_{i+1}$ let $u(k)=\alpha_+$ if $i$ is even and $u(k)=\alpha_-$ if $i$ is odd. Put

```math
z=\sum_{k\ge1}\varepsilon_kb^{-k^2},\qquad \varepsilon_k=2\beta_{u(k)}(k)-1 .
```

Then $z\in K_b$, and for all $N,L\ge1$,

```math
\alpha_--\frac{14\sqrt N+L(1+\sqrt N)}N\ \le\ f_{0^L}(N)\ \le\ \alpha_++\frac{14\sqrt N+L(1+\sqrt N)}N .
```

At the phase ends, $\gamma^+(K_{i+1}^2)\ge\alpha_+-(K_i/K_{i+1})^2-4/K_{i+1}$ for even $i$, and $\gamma^+(K_{i+1}^2)\le\alpha_-+(K_i/K_{i+1})^2+4/K_{i+1}$ for odd $i$. Consequently, for every $L$, the set of limit points of $f_{0^L}(N)$ is exactly $[\alpha_-,\alpha_+]$.

*Proof.* As in Theorem 8.1, $V_k$ has the sign of $\varepsilon_k$ and $B'_L(N)\le L(1+\sqrt N)$. On a complete phase $(K_j,K_{j+1}]$, Lemma 8.0 applied at both ends gives $\sum\beta_{u_j}(k)(2k-1)=u_j(K_{j+1}^2-K_j^2)+E_j$ with $|E_j|\le4K_{j+1}$. Let $K=\lfloor\sqrt N\rfloor$ lie in phase $i$. The completed phases contribute errors at most $4\sum_{j\le i}K_j\le8K_i\le8K$, because $K_j/K_{j+1}\le\frac12$, and the current phase contributes at most $4K$. Since $u\le\alpha_+$ throughout,

```math
\Gamma^+(K^2)\le\alpha_+K^2+12K,\qquad \Gamma^+(N)-\alpha_+N\le12K+(1-\alpha_+)(N-K^2)\le14\sqrt N,
```

and symmetrically $\Gamma^+(N)-\alpha_-N\ge-14\sqrt N$. For even $i$, $\Gamma^+(K_{i+1}^2)\ge\alpha_+(K_{i+1}^2-K_i^2)-4K_{i+1}$, which gives the phase-end bound, and odd $i$ is symmetric with $\Gamma^+(K_i^2)\le K_i^2$. Hence $\limsup\gamma^+\ge\alpha_+$, $\liminf\gamma^+\le\alpha_-$, and all limit points lie in $[\alpha_-,\alpha_+]$. With (0.1) the limit set is the whole interval. Theorem 6.3 transfers this to $f_{0^L}$, with the extra error $B'_L(N)/N$. $\square$

For $[\alpha_-,\alpha_+]=[\frac15,\frac7{10}]$ in base 2, the script gives $\gamma^+(4)=3/4$ and $\gamma^+(256)=15/64=0.234375$ exactly, and exact rationals with 6-decimal roundings $\gamma^+(2^{18})\approx0.699711$ and $\gamma^+(2^{32})\approx0.200037$. The envelope of Theorem 8.2 is checked at every $N\le2^{15}$. The orbit-computed sign counts agree with the combinatorial counts at $N=4$ and $256$; the values at $2^{18}$ and $2^{32}$ are combinatorial counts justified by the dominance identity.

## 9. Finite verification

[`scripts/phase22_simple_normality.py`](../../scripts/phase22_simple_normality.py) uses only the standard library and exact integer or rational arithmetic in every assertion, except for the two logarithms in the Corollary 5.4(a) check; floating point is otherwise used only to print observed ratios. It runs in about 20 s, performs about $3.34\cdot10^6$ checks, and exits with status 0. Tested numbers are the truncations $z_M=c_m+\sum_{m\le M}a(m)b^{-m}$, which are real numbers to which the finite theorems apply verbatim. For values attributed to infinite series, $M$ is the last index before a support point beyond $N+70$. The sign of the discarded tail is certified by Lemma 6.2(c). Exact ties are broken by that sign, and every non-tie comparison is shown to have a margin larger than the truncation error.

| item | what is checked | outcome |
|---|---|---|
| Lemmas 1.1–1.2 | cylinder margins, equality cases, endpoints | 220 interior cases, all bases $2\le b\le12$ at $0$ |
| Lemma 2.2 | localization with radius $b\delta/(b-1)$ | 1060 prefixes, 922 meet the hypothesis; maximal needed radius ratio $0.9091$ |
| Theorem 3.2 | exclusive dichotomy at threshold $b^{-L-1}$ | 398 cases: 259 boundary, 139 interior |
| Theorem 4.1(a) | binary positive-side bound at the interior scale $\varepsilon=\delta+\frac14$, on prefixes with $\delta<\frac14$ | 61 prefixes |
| Proposition 3.1 | far-count and Markov bounds, $c=0$ and $c=c_m$ | 543 cases |
| Theorem 5.2 | all inequalities and the identity, at **every** $N\le10^4$, $L\le4$ | 15 families |
| Theorem 5.3 | bad-tail bound for $k\in\{0,1,2,4,8,12\}$, $L\le4$, at $N\in\{10^2,10^3,2500,5000,10^4\}$ | 15 families |
| Corollary 5.4(a) | linear-mass rate at $N=10^4$ | $E_b$ ($C=1$), $E_b^3$ ($C=4$) |
| exact zero tails | Theorem 5.2 and $T_n=0\Rightarrow$ positive class for exactly truncated finite series | $b\in\{2,3,10\}$ |
| Proposition 6.1, Theorem 6.3 | sign constant on gaps; bad count $=\min(g_k,\lambda_k)$, final position | every complete gap $\le10^4$ |
| Lemma 6.2 | dominance at every support point; sharpness (d) | all families; $b\in\{2,3,10\}$, $g\le3$ |
| Corollary 6.4, Proposition 6.5 | $B'_L\le(L+\kappa)(1+S)$ at every $N$; exactness; $L-1\le\lambda_k\le L$ | bounded families; $b=3,5,10$, $L=2,3,4$ |
| Theorem 7.3 | lacunary formula for $\Gamma^+(2^K)$ | $b=2,3$, $4\le K\le14$ |
| Lemma 8.0, Theorem 8.1 | Beatty identity and bound; prescribed limit at every $N\le6000$ | $\alpha\in\{\frac13,\frac25,\frac{\sqrt5-1}2\}$, $b\in\{2,3,10\}$; largest ratio to the bound $0.241$ |
| Theorem 8.2 | envelope at every $N\le2^{15}$; phase ends | $[\frac15,\frac7{10}]$ |
| gap identities | pentagonal, triangular, two-progression, geometric limits | $k\le20000$, $3000$, $5000$ |

## 10. Recommended Lean finite cores

The statements below build on `shift`, `radixDiscrepancy`, `Phase18Synthetic.Near`, `SharpTranslation.arc_le` and `interval_eq_arc_excess`, and on `CoefficientTransfer.coeffSeries` and `supportCount`. They need no analytic input beyond these. The block opens `Classical` because several `Finset.filter` predicates are real-valued, and it reuses `Phase18Synthetic.repunit`. They are recommendations, not kernel-checked results.

```lean
namespace NormalityChecker.SimpleNormality
open Finset CoefficientTransfer Phase18Synthetic SharpTranslation
open Classical

/-- Starts `n < N` at which the base-`b` word of length `L` with value `v` occurs. -/
noncomputable def wordCount (b L : ℕ) (x : ℝ) (v N : ℕ) : ℕ :=
  ((range N).filter fun n => ⌊(b : ℝ) ^ L * shift b x n⌋₊ = v).card

-- `repunit b L = ∑ i ∈ range L, b ^ i` is `Phase18Synthetic.repunit`, reused below.

/-- Lemma 1.1 (interior fixed points). -/
theorem floor_eq_repunit_of_near {b m L : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) (hmb : m + 2 ≤ b)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hnear : |t - (m : ℝ) / ((b : ℝ) - 1)| < 1 / (((b : ℝ) - 1) * (b : ℝ) ^ L)) :
    ⌊(b : ℝ) ^ L * t⌋₊ = m * repunit b L

/-- Lemma 1.2 (the boundary fixed point). -/
theorem floor_eq_zero_or_top_of_near {b L : ℕ} (hb : 2 ≤ b) {t ε : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : ε < 1 / (b : ℝ) ^ L) (hnear : Near t ε) :
    ⌊(b : ℝ) ^ L * t⌋₊ = 0 ∨ ⌊(b : ℝ) ^ L * t⌋₊ = b ^ L - 1

/-- Lemma 2.2 (localization; strict form, which avoids the limiting step). -/
theorem exists_fixed_center_of_deficit {b N : ℕ} (hb : 2 ≤ b) (hN : 3 ≤ N) (x : ℝ) {δ : ℝ}
    (hδ : 1 - radixDiscrepancy b x N < δ) (hδN : δ ≤ 1 / 2 - 1 / (N : ℝ)) :
    ∃ j : ℕ, j + 2 ≤ b ∧
      (((range N).filter fun n => ¬ Near (shift b x n - (j : ℝ) / ((b : ℝ) - 1))
          ((b : ℝ) * δ / ((b : ℝ) - 1))).card : ℝ) ≤ δ * N

/-- Theorem 3.2 (finite dichotomy; strict form). -/
theorem word_dichotomy_of_deficit {b N L : ℕ} (hb : 2 ≤ b) (hN : 4 ≤ N) (hL : 1 ≤ L)
    (x : ℝ) {δ : ℝ} (hδ : 1 - radixDiscrepancy b x N < δ) (hδL : δ < 1 / (b : ℝ) ^ (L + 1)) :
    (N : ℝ) - wordCount b L x 0 N - wordCount b L x (b ^ L - 1) N ≤ δ * N ∨
    ∃ m, 1 ≤ m ∧ m + 2 ≤ b ∧ (N : ℝ) - wordCount b L x (m * repunit b L) N ≤ δ * N

/-- The oriented tail `T_n`. -/
noncomputable def orientedTail (b : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, (a (n + 1 + j) : ℝ) / (b : ℝ) ^ (1 + j)

/-- Lemma 5.1. -/
theorem shift_coeffSeries_eq_fract_tail {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    shift b (coeffSeries b a) n = Int.fract (orientedTail b a n)

theorem orientedTail_succ {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) (n : ℕ) :
    orientedTail b a n = ((a (n + 1) : ℝ) + orientedTail b a (n + 1)) / b

/-- Theorem 5.2(a). -/
theorem floor_fract_eq_zero {b L : ℕ} (hb : 2 ≤ b) {T : ℝ} (h0 : 0 ≤ T)
    (h1 : T < 1 / (b : ℝ) ^ L) : ⌊(b : ℝ) ^ L * Int.fract T⌋₊ = 0
theorem floor_fract_eq_top {b L : ℕ} (hb : 2 ≤ b) {T : ℝ} (h0 : -(1 / (b : ℝ) ^ L) ≤ T)
    (h1 : T < 0) : ⌊(b : ℝ) ^ L * Int.fract T⌋₊ = b ^ L - 1

/-- Proposition 6.1 (iterating `orientedTail_succ` across zero coefficients). -/
theorem orientedTail_of_gap {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ}
    (hsum : Summable fun m => |(a m : ℝ)| / (b : ℝ) ^ m) {n g : ℕ} (hg : 1 ≤ g)
    (hgap : ∀ j ∈ Ioo 0 g, a (n + j) = 0) :
    orientedTail b a n = orientedTail b a (n + g - 1) / (b : ℝ) ^ (g - 1)

/-- Lemma 6.2(b),(c). -/
theorem abs_orientedTail_lt {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {n : ℕ} {H : ℝ}
    (hH : ∀ j, |(a (n + 1 + j) : ℝ)| ≤ H) (hlt : ∃ j, |(a (n + 1 + j) : ℝ)| < H) :
    |orientedTail b a n| < H / ((b : ℝ) - 1)
theorem sign_of_dominant {b : ℕ} {a : ℕ → ℤ} {m : ℕ}
    (hdom : |orientedTail b a m| < |(a m : ℝ)|) :
    (0 < (a m : ℝ) + orientedTail b a m ↔ 0 < a m)

/-- Corollary 6.4 with `H ≤ b - 1`. -/
theorem badTail_card_le {b H : ℕ} (hb : 2 ≤ b) (hH : 1 ≤ H) (hHb : H + 1 ≤ b) {a : ℕ → ℤ}
    (hbd : ∀ m, |a m| ≤ H) (hcoinf : ∀ M, ∃ m > M, a m = 0) (N L : ℕ) :
    ((range N).filter fun n => 1 / (b : ℝ) ^ L ≤ |orientedTail b a n|).card ≤
      L * (1 + supportCount a (N - 1))

/-- Lemma 8.0. -/
theorem beatty_odd_weight (α : ℝ) (K : ℕ) :
    |∑ k ∈ Icc 1 K, ((⌊(k : ℝ) * α⌋ - ⌊((k : ℝ) - 1) * α⌋ : ℤ) : ℝ) * (2 * k - 1) -
      α * (K : ℝ) ^ 2| ≤ 2 * K

end NormalityChecker.SimpleNormality
```

The proof of `exists_fixed_center_of_deficit` uses only `interval_eq_arc_excess` (Lemma 2.1(b)), the $b$-Lipschitz property of `shift`, and the nearest-point computation for $(b-1)^{-1}\mathbb Z$. The counting statement `badTail_card_le` iterates `orientedTail_succ` and needs no tail summation. Together with `floor_fract_eq_zero` and `floor_fract_eq_top`, it gives a kernel-checked proof of Theorem 8.1 for every $\alpha$ once `beatty_odd_weight` is available.

## 11. Scope and open questions

*Proved here.* Lemmas 1.1–2.2, Propositions 2.3–3.1, Theorems 3.2–3.4 and 4.1, Section 5, Section 6 and Section 7 are complete paper proofs. They use only the arc lemmas already in Lean, the Phase 20 counting argument (reproved in Theorem 5.3), and, for Remark 3.5, the Phase 19 decomposition of $K_b$. Theorems 8.1–8.2 are complete paper proofs that also cite the Lean theorem `linear_mass_sparse_tendsto_one` for membership in $K_b$, which also follows from Theorem 6.7. *Finite computations.* Table 7.1, the lacunary values, the phase-end values and the observed constants $0.9091$ and $0.241$ are exact finite computations. They are not used in any proof.

**Question 11.1.** Is the radius $b\delta/(b-1)$ in Lemma 2.2 optimal? The largest observed ratio is $0.9091$. Is the threshold $b^{-L-1}$ in Theorem 3.2 optimal?

**Question 11.2.** Proposition 6.5 shows that the rate $S(N)/N$ is sharp for $\pm1$ coefficients, $b\ge3$ and $L\ge2$. Determine the sharp constant in $|f_{0^L}(N)-\gamma^+(N)|$ for $L=1$ and for general bounded coefficients.

**Question 11.3.** For $E_b^2=\sum a_2(n)b^{-n}$, the coefficients come from the CM form $\eta(12\tau)^2$ ([Phase 20, Theorem C](../phase20/euler-product.md)). Does the gap-weighted positive fraction $\gamma^+(N)$ converge, and to what? By Theorem 6.7 this decides the limiting frequencies of $0^L$ and $(b-1)^L$ in the digits of $E_b^2$. The question concerns the distribution of signs of Hecke eigenvalues weighted by the gaps of their support.

**Question 11.4.** For multiplicatively independent $b,b'$, which pairs of limit sets of $f_0$ in the two bases occur for numbers lying in $K_b\cap K_{b'}$? Phase 19 decides rational elements of such intersections but does not classify irrational ones.
