# Rational combinations, polynomial images and products

Let $b\ge2$. For an odd prime $p\nmid b$, write $t_p=\operatorname{ord}_p(b)$, $w_{p,s}(k)=p^{-s v_p(k)}$, and

$$
X_{p,s}=\sum_{k\ge1} w_{p,s}(k)b^{-n_k}.
$$

The schedule consists of strictly increasing positive multiples of $t_p$. Unless indicated otherwise $s$ is a positive integer. Results here are paper proofs using the repository's fixed-support theorem. The strongest nonlinear conclusion is that **every nonconstant rational polynomial of the factorial-schedule $X_{p,s}$ is normal to base $b$**. The proof controls cutoffs between the different layers of a convolution. [Principal family and analytic criterion](principal.md) · [Fixed-support theorem](../../NormalityChecker/SmoothOrbit.lean#L207) · [Reproducible finite checks](../../scripts/phase18_principal.py)

## E1. Linear combinations and joint normality

Choose finitely many distinct primes $p$. At each $p$ use a single schedule for any finite set of distinct positive orders $s$. Schedules at different primes can be independent. If the union of insertion positions through $N$ is $O(N^{1-\eta})$ for some $\eta>0$, then every rational affine combination with at least one nonzero nonconstant coefficient is normal to base $b$. The vector of these numbers is jointly normal, meaning its simultaneous radix shifts are uniformly distributed on the torus.

For integral coefficients, choose a prime $p$ having a nonzero coefficient and let $s_*$ be its highest participating order, with multiplier $A\ne0$. For $J=\lfloor\log_p K_p(n)\rfloor$ the leading shifted prefix has $p$-valuation $v_p(A)-s_*J$ for every $K_p(n)\ge1$, including $J=0$. Its valuation becomes negative as $J$ grows. All terms at other primes and the constant are $p$-integral. The remaining $p$-axis terms have strictly larger valuation at all sufficiently late shifts. The unique least valuation survives. The entire denominator divides the product of the highest prime powers on the respective axes, bounded by a fixed power of $n+1$. This verifies the two denominator conditions of the all-prefix criterion in the principal note. Grouping coincidences in a finite linear combination leaves bounded coefficients.

For rational coefficients with common denominator $D$, factor $D=D_bD_0$ where $D_b\mid b^v$ for a fixed $v$ and $(D_0,b)=1$. Then $b^v x=Y/D_0$ with an integral combination $Y$ (including the constant). If the reduced denominator of a shifted prefix of $Y$ is $Q$, that of the corresponding prefix of $Y/D_0$ is a multiple of $Q$ dividing $D_0Q$. Enlarge the fixed support by primes dividing $D_0$. Shifting the orbit back by $v$ costs at most $v/N$ in discrepancy. Multidimensional Weyl now follows by applying the scalar result to every nonzero integer frequency vector. In particular $1$ and these generators are linearly independent over $\mathbb Q$. The argument at a shared prime depends on the common schedule, or more generally a strict eventual separation of the participating pole orders.

## E2. Polynomial schedules and the top residue of a convolution

Take a single $n_k=tk^d$, where $t=t_p$. For $P\in\mathbb Z[z]$ of degree $r\ge1$, the shifted prefix is obtained by expanding powers into **ordered** tuples with $\sum_i n_{k_i}\le n$. Constant terms are included. The number of tuple insertions through $N$ is $O_{P,t}(1+N^{r/d})$. At an exponent $m$ the sum of absolute coefficients is $O_P((m+1)^r)$, by counting all tuples with every $k_i\le m$. All shifted denominators divide $p^{rsJ}$ for $J=\lfloor\log_p((n/t)^{1/d})\rfloor$ at late $n$.

Put $u=n/(t p^{dJ})\in[1,p^d)$ and let $M_r(u)$ count the ordered tuples of positive integers $(a_1,\ldots,a_r)$ with $\sum a_i^d\le u$. For $J\ge1$ the leading coefficient $A$ of $P$ gives

$$
p^{rsJ}R_n(P(X_{p,s}))\equiv b^n A M_r(u)\pmod p.
$$

Indeed, the surviving degree-$r$ tuples have $k_i=p^J a_i$, with each $a_i<p$. Their radix phase after removing $b^n$ equals one modulo $p$. Lower degrees vanish at this precision. When $p\mid A$, instead use the normalization $p^{rsJ-v_p(A)}$ at sufficiently late $J$ and replace $A$ by its unit part in this congruence. This works because lower-degree poles are then strictly smaller. Thus an exact count of $M_r(u)\bmod p$ decides retention at the highest available degree-$r$ depth. A vanishing count can leave lower powers.

**An all-prefix discrepancy bound for $d>r$.** Set $\lambda=p^d$, $G=\{u\in[1,\lambda):p\nmid M_r(u)\}$, with $|\,\cdot\,|$ denoting length. Define

$$
\rho=\min_{1\le y\le\lambda}
\frac{|G|/(\lambda-1)+|G\cap[1,y)|}{y}.
$$

Then $\limsup_N D_N(P(X_{p,s});b)\le1-\rho$. The rational-coefficient reduction in E1 gives the same estimate for rational $P$. The set $G$ is explicitly finite-union since $a_i<p$. Previous full shells up to $t\lambda^J$ contribute $t\lambda^J|G|/(\lambda-1)+O(J+1)$ passing positions, by geometric summation and bounded rounding per shell. At cutoff $t\lambda^J y$ the current shell adds $t\lambda^J|G\cap[1,y)|+O(1)$. Hence the lower prefix density of passing positions is $\rho$. To obtain the discrepancy bound, use the block length of the principal-note criterion with $\eta=1-r/d$. In a clean block meeting $G$ at a late shift, the denominator is constant and large. The short-orbit theorem gives interval discrepancy $o(1)$ uniformly there, by applying Erdős–Turán at a fixed cutoff and then sending that cutoff to infinity. Any other clean block costs at most its full length and is contained in the complement of the passing positions. Boundary blocks and the real-tail buffer cost $o(N)$ as before. Thus the coefficient of the uncovered proportion is one.

In this regime $r<\lambda$ and $G$ contains $[r,\min(\lambda,r-1+2^d))$, where only the all-ones tuple fits. For the square of the flagship binary cubic-schedule number, $\lambda=27$ and $M_2$ jumps at $2,9,16$ to $1,3,4$. Thus $G=[2,9)\cup[16,27)$, with $\rho=9/26$ and $\limsup D_N\le17/26$ at precision one. For the cube with $(p,d)=(3,4)$ the respective counts at $3,18,33,48$ are $1,4,7,8$, giving $G=[3,81)$ and $\limsup D_N\le27/40$ at precision one.

### Full normality when the order is at least the degree

For **every $1\le r<d$ and $s\ge r$**, every rational polynomial of degree $r$ in $C(b,p,s,d)$ is normal to base $b$. In particular every quadratic is covered for $d\ge3$, $s\ge2$, and every cubic for $d\ge4$, $s\ge3$.

Reflect the indices about level $J$ by writing $k_i=p^{J-h_i}a_i$ with $h_i\ge0$, $p\nmid a_i$. The tuple is included precisely when $\sum_i(a_i/p^{h_i})^d\le u$. After clearing the nominal power $p^{rsJ}$ its weight is $p^{s\sum h_i}$ times the radix unit. Let $C_H(u)$ count the tuples of total loss $\sum h_i=H$, and let $H$ be the first nonempty layer. For large $J$ all layers of fixed depth occur with the same index ranges. We claim

$$
H\le r,\qquad 1\le C_H(u)<p^r .
$$

For $0\le j\le r$, the smallest normalized insertion at layer $j$ is $m_j=r-j+j/p^d$, attained with $j$ losses equal to one and the other losses zero, all $a_i=1$. Indeed $p^{-dh}\ge1-h(1-p^{-d})$ for integral $h\ge0$. Since $m_r=r/p^d<1$, some layer through $r$ fits. At $H=0$ each $1\le a_i<p$ and the upper bound follows. If $H>0$, then

$$
m_H\le u<m_{H-1}=r-H+1+(H-1)/p^d\le r.
$$

Every coordinate of zero loss has $a_i=1$ since $2^d>r$. If only $H-2$ or fewer coordinates had positive loss, the zero-loss coordinates would alone contribute at least $r-H+2>m_{H-1}$. Thus the losses consist either of $H$ ones, or of $H-2$ ones and one two.

In the first case the positive-loss coordinates satisfy $\sum a_i^d<p^d+H-1$. Each other summand is at least one, so all $a_i<p$. This gives at most $\binom rH(p-1)^H$ choices. In the second case, possible only for $H\ge2$, subtract the unit zero-loss coordinates and multiply by $p^d$. The $H-2$ first numerators and the distinguished numerator $c$ satisfy $\sum a_i^d+(c/p)^d<H-1$. Therefore each $a_i=1$ and $c<p$. The count is at most $\binom r{H-1}(H-1)(p-1)\le\binom r{H-1}(p-1)^{H-1}$, using $p\ge3$. For $H\ge2$ the two bounds are terms of $(1+(p-1))^r$ omitting at least its constant term. At $H=1$ the first bound alone is strictly below $p^r$. This proves the claim.

Put $a=v_p(b^t-1)$. A sufficient threshold for freezing the first nonempty layer is $J\ge r+\max(0,\lceil(s-a)/d\rceil)$. At that threshold each term on the first nonempty layer has $b^{-n_{k_i}}\equiv1\bmod p^s$ since $h_i\le r$ and $n_{k_i}=t p^{d(J-h_i)}a_i^d$. Indeed $v_p(b^{n_{k_i}}-1)=a+d(J-h_i)\ge s$ by lifting the exponent. After removing $p^{sH}$ the normalized degree-$r$ prefix is therefore $b^n C_H(u)\bmod p^s$, since subsequent layers are multiples of $p^s$. Since $0<C_H(u)<p^r\le p^s$, its valuation is at most $r-1$. The actual pole depth is at least $rsJ-sr-(r-1)$. A fixed leading coefficient costs at most its own valuation. All lower degrees have depth at most $(r-1)sJ$. Hence $sJ>sr+(r-1)+v_p(A)$, together with the freezing threshold, suffices for a leading coefficient $A\ne0$ to retain the top pole. Sparsity $r<d$ and the principal-note criterion prove the theorem, with the rational reduction of E1.

The first guaranteed shell can matter. For $(b,p,s,d)=(2,3,2,3)$ and $P(z)=z^2$, direct convolution gives maximum pole loss 6 at $J=2$ and 5 at $J=3$. The bound $sr+r-1=5$ applies from $J=3$.

Set $m=\min(s,d-1)$. The vector $(X,X^2,\ldots,X^m)$ with $X=C(b,p,s,d)$ is jointly normal to base $b$. Each nonzero integer frequency vector gives a nonconstant polynomial of degree at most $m$, so multidimensional Weyl applies. If $X$ were algebraic of degree at most $m$, its minimal polynomial would take the value zero, contradicting scalar normality. Thus an algebraic $X$ must have degree at least $m+1$.

### Refining the failed cells at smaller orders

For a fixed precision $L$, set $h_*=\lfloor(L-1)/s\rfloor$. The scaled monomial prefix $p^{rsJ}b^{-n}R_n(X^r)$ equals, modulo $p^L$ for all sufficiently large $J$,

$$
M_L(u)=\sum_{H=0}^{h_*}p^{sH} C_H(u).
$$

Explicitly $J\ge h_*+\max(0,\lceil(L-a)/d\rceil)$ ensures $h_i\le J$ and $v_p(b^{n_{k_i}}-1)=a+d(J-h_i)\ge L$ throughout the retained layers, uniformly in $u$. Higher layers vanish. For a polynomial with integral leading coefficient $A\ne0$, also taking $sJ>L-1+v_p(A)$ makes the pole at a passing cell strictly deeper than every lower degree. Every endpoint is an integer multiple of $p^{-d h_*}$. The nonzero cells give depth at least $rsJ-L+1$. A fixed leading coefficient and lower degrees preserve this growing pole. The preceding all-prefix bound applies with $G=\{M_L(u)\not\equiv0\bmod p^L\}$.

For squares, the script refines only failed half-open intervals. At total loss $j$ it counts pairs with individual losses $u,v$, $u+v=j$, $u\le v$, using multiplicity two for $u<v$. On the integer grid of denominator $p^{dj}$ an insertion has coordinate $(a p^{j-u})^d+c^d p^{d(j-v)}$. For each first numerator $a$ coprime to $p$, exact integer roots count every $c$ at or below the left endpoint and enumerate the new jumps strictly inside. Both numerators are positive and prime to $p$. The shell endpoint excludes coordinates $\ge p$ after scaling. Previous passing cells stay passing modulo higher powers. At each remaining failed-cell endpoint the script evaluates the all-prefix proportion, including all earlier complete shells.

For the flagship square $(b,p,s,d)=(2,3,1,3)$ the 14-layer calculation gives the rigorous bound

$$
\limsup_N D_N(C(2,3,1,3)^2;2)
\le\frac{10893289026421}{20594407551577180074}<5.3\cdot10^{-7}.
$$

The successive failed-cell counts are $2,2,3,4,6,9,7,11,8,15,15,15,11,13$. Continuing to 21 layers leaves 22 failed cells and gives the smaller bound $14035285166320179631/47872170047321719707829651794<2.94\cdot10^{-10}$. The fractions bound all real-orbit prefixes asymptotically by the theorem, while the cell enumeration is finite integer arithmetic. These precisions leave normality of the flagship square open. The same bounds hold for every quadratic with nonzero rational leading coefficient in this example.

Reproduce the 14-layer bound with `python -B scripts/phase18_principal.py` and the deeper one with `python -B scripts/phase18_principal.py --square-layers 21`. The script also compares the adaptive algorithm to direct ordered-tuple enumeration on whole shells at smaller precisions. [Exact certificate implementation](../../scripts/phase18_principal.py)

## Universal polynomial normality for fast schedules

Assume in addition that

1. $n_{k+1}/n_k\to\infty$.
2. Whenever $v_p(i)\to\infty$, $b^{-n_i}\to1$ in $\mathbb Z_p$. Equivalently, for each $L$ all $i$ with sufficiently large $v_p(i)$ satisfy $b^{n_i}\equiv1\bmod p^L$.

Then $P(X_{p,s})$ is base-$b$ normal for **every** nonconstant $P\in\mathbb Q[z]$. The factorial schedule $n_i=t i!$ satisfies condition 2 by lifting $b^t$ to powers of $p$. The conclusion applies to the factorial Liouville number itself, its square, its cube, and every fixed higher degree. It further gives joint uniform distribution of the shifts of $(X_{p,s},X_{p,s}^2,\ldots,X_{p,s}^r)$ for every finite $r$, by multidimensional Weyl.

All these nonconstant polynomial values are also Liouville. Indeed $X_{p,s}$ is transcendental by the positive truncation estimates in the principal note, so $P(X_{p,s})$ is transcendental. If $U_k$ has denominator $Q_k$, then $P(U_k)$ has denominator at most $D Q_k^r$ for a fixed coefficient denominator $D$, and boundedness of $P'$ near $X_{p,s}$ gives $|P(U_k)-P(X_{p,s})|\ll_P |U_k-X_{p,s}|$. The truncation errors beat every fixed power of $Q_k^{-1}$. The rational values $P(U_k)$ converge to an irrational, giving infinitely many distinct approximants with unbounded reduced denominators.

**Which partial products occur.** Clear rational coefficients as in E1 and take $P\in\mathbb Z[z]$ with leading coefficient $A\ne0$ and degree $r$. Set

$$
U=\sum_{i<k}w_{p,s}(i)b^{-n_i},\qquad V=w_{p,s}(k)b^{-n_k}.
$$

For $n_k\le n<n_{k+1}$ and late $k$, every tuple without $k$ is included, since $r n_{k-1}<n_k$. Tuples with $j$ copies of $k$ have their exponents in $[j n_k,j n_k+r n_{k-1}]$. Discard these intervals for $1\le j\le r$ within this shell. Through any $N$ in the $K$th shell their total length is $O_r(\sum_{k\le K}(n_{k-1}+1))=O_r(n_{K-1}+K)=o(N)$, using eventual growth by at least a factor two and then $n_{K-1}/n_K\to0$. Elsewhere the unshifted prefix equals, for some $0\le l\le r$,

$$
F_l(U,V)=\sum_{j=0}^l \frac{P^{(j)}(U)}{j!}V^j .
$$

The integer coefficients count the ordered tuples exactly, including collisions. We prove that the denominator after shifting retains depth $rs\lfloor\log_p k\rfloor-O(1)$ throughout these plateaus. Multiplication by $b^n$ preserves $p$-valuation.

**Unequal pole orders.** Write $v=v_p(k)$, $J=\lfloor\log_p k\rfloor$. If $J-v\to\infty$ along a subsequence, then $k$ is not a power of $p$ eventually. The principal denominator calculation gives $v_p(U)=-sJ$ and $v_p(V)=-sv$. The monomial $AU^r$ has strictly smaller valuation than all other monomials of $F_l$ eventually, uniformly over the finitely many $l$. Each degree-$r$ term involving $V$ loses at least $s(J-v)$ in pole depth. Each smaller degree loses at least $sJ$, up to fixed coefficient valuations. The resulting depth is exactly $rsJ-v_p(A)$.

**Bounded difference of pole orders.** On a subsequence with bounded $J-v$ and $k\to\infty$, pass to a further subsequence with $m=k/p^v$ and $l$ fixed. This is possible since $1\le m<p^{J-v+1}$. Here $p\nmid m$, $v\to\infty$, and $p^{sv}V\to1$ $p$-adically. The old prefix has the following rational limit in $\mathbb Q_p$, where $w(a)=p^{-s v_p(a)}$:

$$
p^{sv}U\longrightarrow
B(m)=\sum_{a=1}^{m-1}w(a)-m\lambda_s,\qquad
\lambda_s=\frac{(p-1)p^s}{p^{s+1}-1}.
$$

Indeed, the terms $i=a p^v<k$ give the finite displayed sum in the limit, using condition 2. For fixed $h\ge1$ there are exactly $m(p-1)p^{h-1}$ indices $i<k$ with $v_p(i)=v-h$ when $v\ge h$. Each normalized term equals $p^{sh}b^{-n_i}$ and the unit tends uniformly to one at fixed $h$. The layers with $h>H$ lie in $p^{s(H+1)}\mathbb Z_p$. The resulting geometric series over all $h\ge1$ sums $p$-adically to $m(p-1)p^s/(1-p^{s+1})=-m\lambda_s$.

The **ordinary real value** of this rational satisfies $-1<B(m)<0$. To see it set $\delta_h=p^{-s(h-1)}-p^{-sh}$ for $h\ge1$. These positive numbers sum to one. The identity $w(a)=1-\sum_{p^h\mid a}\delta_h$ gives

$$
\sum_{a=1}^m w(a)-m\lambda_s
=\sum_{h\ge1}\delta_h\{m/p^h\},
\qquad
\lambda_s=1-\sum_{h\ge1}\delta_h/p^h .
$$

The right side is strictly between zero and one. Since $w(m)=1$, subtracting this last term proves the assertion. Now multiply $F_l(U,V)$ by $p^{rsv}$. Lower-degree terms tend to zero and the degree-$r$ part tends to

$$
A\sum_{j=0}^l {r\choose j} B(m)^{r-j}.
$$

The polynomial in $B(m)$ after removing $A$ is monic with integer coefficients. Its rational roots are integers. Since $B(m)\in(-1,0)$, the limit is nonzero. Its $p$-valuation is therefore finite and is attained eventually along the subsequence. As $J-v$ is bounded, this gives depth $rsJ-O(1)$ there. If the asserted uniform bound failed, a sequence with unbounded loss tending to infinity would have either a subsequence with $J-v\to\infty$ or one with bounded $J-v$. The two arguments exclude both.

**Transfer.** All shifted denominators, including those in discarded intervals, divide $p^{rsJ}\le (n+1)^{rs}$ when $n_k\le n<n_{k+1}$. Outside a set of density zero their depth tends to infinity by the preceding proof. Since $n_k$ grows at least geometrically eventually, there are $O_r((1+\log N)^r)$ tuple insertions through $N$. At position $m$ the absolute sum of coefficients is $O_P((m+1)^r)$ as above. These verify the three hypotheses and the real-tail condition of the principal-note criterion. No limiting argument in $r$ or $s$ is needed.

## E3. A product whose opposite-axis prefix stays a unit

The two Stoneham axes at 3 and 5 can lose their top powers simultaneously. In the following construction only the **exponents** are chosen. Both coefficient sequences remain the original positive valuation weights. [Simultaneous loss at shift 106 for the Stoneham product](../phase13/independent-axes.md)

Fix distinct odd primes $p,q\nmid b$, with $b^{t_q}\not\equiv1\bmod p$, and positive orders $s,u$. Construct increasing positions $m_1,m_2,\ldots$ alternately for axes $X$ (odd) and $Y$ (even). Take $m_0=1$. At step $j$ require $m_j\ge(j+1)m_{j-1}$. For $X$ use the least eligible multiple of $t_p$. For the $i$th insertion on $Y$ use the least multiple of $t_q$ above or at the threshold for which

$$
Y_{i-1}+q^{-u v_q(i)} b^{-m_{2i}}\not\equiv0\pmod p,\qquad Y_0=0.
$$

Here $Y_i$ is the actual unshifted partial sum on this axis. These fractions are $p$-integral. Two consecutive candidate multiples of $t_q$ give distinct nonzero increments modulo $p$, so at most the first candidate needs to be skipped. The construction works for $(b,p,q)=(2,5,3)$ since $2^{t_3}=4\not\equiv1\bmod5$.

**Product theorem.** $XY$ is base-$b$ normal. For $m_j\le n<m_{j+1}$, all product terms whose indices occur through step $j$ have exponent at most $m_j+m_{j-1}$. Every term involving a later index has exponent $>n$. After discarding $[m_j,m_j+m_{j-1})$ the entire unshifted prefix is exactly the rectangle $X_{\lceil j/2\rceil}Y_{\lfloor j/2\rfloor}$. This includes equality at its upper endpoint. The discarded positions through any $N$ in the $J$th shell total $O(\sum_{j\le J}m_{j-1})=o(N)$. On the remaining positions the choice of $Y$ keeps its factor a $p$-unit, while the $X$ factor has exact $p$-pole $s\lfloor\log_p\lceil j/2\rceil\rfloor$. Hence the shifted rectangle retains this pole even where the $q$ side cancels. Its reduced denominator and those of intermediate partial rectangles divide the product of the two maximal powers at the current indices, polynomially bounded in $n+1$ and supported on $\{p,q\}$. Through $N$ there are $O(\log^2(2N))$ pairs. Their coefficients at a single position sum to at most $(m+1)^2$ at exponent $m$. Apply the all-prefix criterion. Both factors themselves and every nonzero rational linear combination are normal by E1. This product construction supplies no conclusion about the unmodified Stoneham product.

### Exact survival at every cutoff, including inside a partial rectangle

There is another choice that works for polynomial schedules. Keep the entire $p$-axis unchanged. On the opposite axis choose any increasing positive multiples $m_j$ of $t_q$, put $a=p/q^v$ for any $v$ with $q^v>p$, and set

$$
Y'=b^{-m_1}+a\sum_{j\ge2}q^{-u v_q(j)}b^{-m_j}
=aY+(1-a)b^{-m_1}.
$$

All weights are positive and at most one, with denominator supported on $q$. Every nonempty unshifted $Y'$ prefix is congruent to the **same unit** $b^{-m_1}\bmod p$. Write $K=\#\{i:n_i\le n-m_1\}$. For $K\ge1$, the shifted convolution prefix of $XY'$ has **exact** $p$-pole $s\lfloor\log_p K\rfloor$, including depth zero. Indeed, its unshifted form sums rows $w_{p,s}(i)b^{-n_i}Y'_{J_i}$ for $i\le K$, where $J_i=\#\{j:m_j\le n-n_i\}\ge1$. After clearing the predicted power, only the indices divisible by $p^{\lfloor\log_p K\rfloor}$ survive modulo $p$. Each surviving row contributes $b^{-m_1}$ because $t_p\mid n_i$. There are between one and $p-1$ such rows. Their endpoints $J_i$ need not agree. Multiplying by $b^n$ preserves the pole.

If $K_X(N)K_Y(N)=O(N^{1-\eta})$ for some $\eta>0$, it follows that $XY'$ is base-$b$ normal. This product bounds the number of ordered pairs, and the two maximum denominator powers, including the fixed factor $q^v$, are polynomial in $N$. Bounded weights give the polynomial coefficient bound even at collisions. The criterion applies with no denominator exceptions at late cutoffs. For schedules $t_p i^d,t_q j^e$ it suffices that $1/d+1/e<1$. For instance one can take $b=2$, $X=C(2,5,1,3)$, $Y=C(2,3,1,3)$ and $Y'=(5/9)Y+(4/9)2^{-2}$. This establishes normality for the indicated affine modification on the second axis.

One can also force every cutoff using **only exponent choices on the opposite axis** if the primary axis instead has weights $p^{-e_i}$ with strictly increasing positive $e_i$. Assume $b^{t_q}\not\equiv1\bmod p$ and choose the opposite exponents successively by the two-candidate $p$-unit test above. The primary insertion positions may be arbitrary strictly increasing positive integers, since their radix factors are units modulo $p$. In the row formula the last nonempty row now has uniquely largest depth $e_K$, so it survives at every cutoff. For the normality transfer one still needs $p^{e_i}$ bounded by a fixed power of $n_i+1$, the sparsity bound on pairs, and the same fixed support. For example use $e_i=i$, $n_i=t_p 2^i$, and opposite-axis positions within $2t_q$ of $j^3$ from above, increasing the finitely many initial thresholds if needed to preserve strict increase. This gives exact primary pole growth with both original positive coefficient sequences $p^{-i},q^{-u v_q(j)}$.
