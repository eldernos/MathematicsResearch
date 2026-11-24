# Gaussian prime bands for log 2 and residues of its binary prefixes

At a common binary cutoff, adding five copies of the zero identity below to the two-stride series for $\log 2$ gives reduced-denominator rate $5/12$. Five is the unique best rational multiplier of this identity, and two is the unique second best, with rate $13/30$. For the original two-stride prefix, each prescribed modular value occurs $O(T^{2/3})$ times in a window of $T\le p$ positions, including windows with several earlier poles. A zero-valued series satisfies the same counting estimate and has vanishing real Fourier deficit. The proofs and finite arithmetic checks below use the notation of the denominator manuscript at commit 944e0c4. [Baseline manuscript](../../../papers/05-classical-denominators/paper.tex)

## The cutoff and its error

Put $z=(1+i)/8$. The identities $(4/3)^2(9/8)=2$ and $(25/32)(9/8)=(15/16)^2$ give the target and the zero relation. Since $1-z=(7-i)/8$, the real logarithm of $25/32$ equals $2\Re\log(1-z)$. Define

$$
A_k(m)=\sum_{j=1}^m\frac{2^{-kj}}j,\qquad
B(m)=\sum_{j=1}^m\frac{(-1)^{j-1}8^{-j}}j,\qquad
G(m)=\sum_{j=1}^m\frac{\Re(z^j)}j.
$$

For real $x\ge0$ use $m_k=\lfloor x/k\rfloor$ and $g=\lfloor 2x/5\rfloor$ in the following formula. The rational $S_t(x)$ is the unshifted partial sum for multiplier $t\in\mathbb Q$.

$$
S_t(x)=2A_2(m_2)+(1+t)B(m_3)+2t A_4(m_4)-2t G(g).
$$

As $x\to\infty$ this tends to $\log 2$ for each fixed $t$. At integer position $N$ put $Y_{N,t}=2^N S_t(N)$ and let $Q_{N,t}$ be its positive reduced denominator. The rate means $\lim_{N\to\infty}N^{-1}\log Q_{N,t}$ with natural logarithms. The Gaussian powers satisfy $\Re(z^j)=w_j2^{-\lceil 5j/2\rceil}$, with $w_j$ repeating $1,0,-1,-1,-1,0,1,1$. Indeed $(1+i)^2=2i$. The condition $\lceil 5j/2\rceil\le N$ is exactly $j\le\lfloor 2N/5\rfloor$, including odd $N$. Writing $L_m=\mathrm{lcm}(1,\ldots,m)$ and $L_0=1$, we obtain $Q_{N,t}\mid \mathrm{den}(t)L_{\lfloor N/2\rfloor}$. In each series the omitted binary exponents are distinct integers exceeding $N$. Their shifted powers of two sum to at most one. With the indices evaluated at $N$, this gives the absolute error

$$
|2^N\log2-Y_{N,t}|
\le \frac{2}{m_2+1}+\frac{|1+t|}{m_3+1}
+\frac{2|t|}{m_4+1}+\frac{2|t|}{g+1}
=O_t((N+1)^{-1}).
$$

The raw estimate is one-sided because its grouped weights are nonnegative. The signed estimate above can overshoot. For example, $S_5(16)=3815831/5505024>\log2$, as one can check by summing $\sum_{j=1}^{20}2^{-j}/j$ and bounding its tail by $2^{-20}/21$.

## Which prime bands disappear

Let $p$ be an odd prime with $p\nmid\mathrm{den}(t)$ and $p^2>\lfloor N/2\rfloor$. Then $pY_{N,t}$ is integral at $p$, and

$$
pY_{N,t}\equiv 2^N S_t(N/p)\pmod p.
$$

Multiplication by $p$ leaves only the terms indexed by $j=pu$ in the respective series, with $u<p$. The new cutoffs are exactly the four cutoffs at $N/p$. Fermat preserves the dyadic bases and $(-1)^{pu-1}=(-1)^{u-1}$. In $\mathbb F_p[i]$, Frobenius sends $z$ to either $z$ or $\bar z$ since $i^p=(-1)^{(p-1)/2}i$. It therefore preserves the trace $z^u+\bar z^u$ for both classes of odd primes, including the split case. Division by two gives the asserted congruence for real parts. In lowest terms a nonzero residue says $v_p(Q_{N,t})=1$, and zero says $v_p(Q_{N,t})=0$.

Here are all the early values, with the left endpoint included in each row.

| Range of $x=N/p$ | Short sum $S_t(x)$ | $t=5$ | $t=2$ |
| --- | --- | ---: | ---: |
| $[0,2)$ | $0$ | $0$ | $0$ |
| $[2,5/2)$ | $1/2$ | $1/2$ | $1/2$ |
| $[5/2,3)$ | $1/2-t/4$ | $-3/4$ | $0$ |
| $[3,4)$ | $(5-t)/8$ | $0$ | $3/8$ |
| $[4,6)$ | $11/16$ | $11/16$ | $11/16$ |

The breakpoint at $x=5$ adds $\Re(z^2)=0$. For every $x\ge4$, $A_2\ge1/4$, $A_4\ge1/16$, and the alternating partial sums give $B\ge 1/8-1/128=15/128$. Also $G\le 1/8+\sum_{j\ge2}(1/4)^j/2=1/6$. Consequently $S_5(x)\ge 1/2+45/64+5/8-5/3=31/192>0$. The raw sum $S_0$ is positive for $x\ge2$, so $S_2=(3S_0+2S_5)/5$ is positive for $x\ge4$. In particular $S_5$ has one *negative* eligible band. That band contributes to the denominator rate.

A zero on $[u,v)$ deletes the first powers at $N/v<p\le N/u$. A nonzero short sum can still have a numerator divisible by an individual prime. At $N=44$, $p=11$ cancels on the positive $11/16$ band, and direct reduction gives $Q_{44,5}=101745$.

To count these exceptions put $K=\lceil N^{1/3}\rceil$. First powers up to $K^2$ cost $O(K^2)$ in logarithmic weight by Chebyshev's estimate. All powers beyond the first in $L_{\lfloor N/2\rfloor}$ cost $O(\sqrt N\log N)$ together. For $p>K^2$, the four cutoffs at $x=N/p<K$ change only $O(K)$ times. Each $S_t(x)$ has bounded absolute value for fixed $t$, and its denominator divides $\mathrm{den}(t)2^{\lceil K\rceil}L_{\lceil K\rceil}$. Each nonzero numerator thus has logarithm of its absolute value $O_t(K)$. Every exceptional large prime divides their product, at total cost $O_t(K^2)$. For integer $t=2,5$ this proves, with $I_{N,t}$ the respective deleted prime interval,

$$
\log Q_{N,t}=\log L_{\lfloor N/2\rfloor}
-\sum_{p\in I_{N,t}}\log p+O_t(N^{2/3}).
$$

The prime number theorem gives $\log L_{\lfloor N/2\rfloor}\sim N/2$ and a deleted mass $N(1/u-1/v)+o(N)$. The intervals are $(N/4,N/3]$ for $t=5$ and $(N/3,2N/5]$ for $t=2$. The rates are respectively $1/2-1/12=5/12$ and $1/2-1/15=13/30$. At $t=0$ the rate is $1/2$. The same calculation works for fixed rational $t$ after clearing its denominator. There are only finitely many deleted bands because $S_t(x)\to\log 2>0$. The earlier optimality theorem concerns finite sums of real dyadic logarithms $\log(1\pm2^{-k})$. [Baseline theorem and scope](../../strided-logarithm.md#why-half-is-optimal-in-this-class)

## Optimizing this one zero relation

For $2\le x<15$ the table below lists every multiplier for which $S_t(x)=0$. To reproduce each entry, write $R=S_0(x)$ and $D=B(m_3)+2A_4(m_4)-2G(g)$ at the left endpoint. If $D\ne0$ the entry is $-R/D$. For example at $x=6$ one gets $R=265/384$ and $D=-1/128$. The endpoints come from multiples of $2,3,4,5/2$, merging at a zero increment.

| Range of $x$ | Multiplier | Range of $x$ | Multiplier |
| --- | ---: | --- | ---: |
| $[2,5/2)$ | none | $[8,9)$ | $1063/2$ |
| $[5/2,3)$ | $2$ | $[9,10)$ | $1064$ |
| $[3,4)$ | $5$ | $[10,12)$ | $21292/5$ |
| $[4,6)$ | none | $[12,25/2)$ | $170341/15$ |
| $[6,15/2)$ | $265/3$ | $[25/2,14)$ | $170341/3$ |
| $[15/2,8)$ | $265/2$ | $[14,15)$ | $1192417/21$ |

All listed multipliers are distinct and below $57000$ in absolute value. For $x\ge15$ the four cutoffs are at least $7,5,3,6$, respectively. Put $E(r,m)=r^{m+1}/((m+1)(1-r))$. Using $|z|<9/50$ in the omitted Gaussian terms gives the rational bounds

$$
2E(1/4,7)+E(1/8,5)<1/10000,\qquad
E(1/8,5)+2E(1/16,3)+2E(9/50,6)<23/2000000.
$$

It follows that $|S_t(x)-\log2|<1/10000+57000(23/2000000)<2/3<\log2$ for every listed multiplier and all $x\ge15$. The last inequality follows from $\log 2=2\sum_{j\ge0}(1/3)^{2j+1}/(2j+1)$. Each listed multiplier therefore loses exactly its one band. The largest loss is $1/12$, the second is $1/15$, and each other listed loss is at most $1/30$. Every unlisted rational multiplier has total loss *strictly* below $1/15$, since any zeros lie in $[15,\infty)$ and all sufficiently late sums are positive. This proves uniqueness of the best and second-best rates within this one-parameter family.

The underlying Gaussian identity has a direct precedent. Harley's real-part formula in Bailey's compendium, §2, gives $2\Re\log(1-(1+i)/2^n)=(1-2n)\log2+\log(2^{2n-1}-2^n+1)$. Taking $n=3$ gives precisely $\log(25/32)$. Bailey also discusses adding rational multiples of BBP zero relations. On the imaginary side, write $A=\arctan(1/3)$ and $C=\arctan(1/7)$. Takahashi's equations (11)–(19) give $\pi/4=2A+C=\arctan(1/2)+A$, hence $\arctan(1/2)=A+C$. His equation (19) expands $C$ at the very same Gaussian argument. Adegoke, Oliver Lafont and Layeni give another complex-argument formula for $\log2$ in equations (28)–(29). These references concern the infinite series and digit extraction. The rate and the optimization above concern reduced denominators at the specified finite cutoff. [Bailey, §§1–3](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf) · [Takahashi](https://tsukuba.repo.nii.ac.jp/record/2001720/files/RJ_51-1-177.pdf) · [Adegoke, Oliver Lafont and Layeni](https://nntdm.net/papers/nntdm-17/NNTDM-17-4-18-32.pdf)

## Residues in an arbitrary prime window

For a periodic weight $U$ write $Y_N(U)=\sum_{1\le j\le N}2^{N-j}U(j)/j$. The two original components have weights $U_1=(0,4,0,4,0,4)$ and $U_2=(0,0,3,0,0,-3)$, indexed from 1 and repeated modulo 6. Their sum is the raw weight $W=(0,4,3,4,0,1)$. For $p>3$, every nonzero $\mathbb F_p$-linear combination is nonzero as a weight, by evaluation at 2 and 3.

More generally, fix $p>3$ and any six-periodic weight $U$ in the rationals integral at $p$ whose reduction is nonzero in at least one position. This includes any integral lifts of the two field coefficients. Let $I$ consist of $T\le p$ consecutive nonnegative integers in $[\ell p,(\ell+1)p)$, and delete all pole terms to form

$$
Z_N=\sum_{\substack{1\le j\le N\\p\nmid j}}\frac{2^{N-j}U(j)}j.
$$

Each prescribed value of $Z_N\bmod p$ occurs $O(T^{2/3})$ times on $I$. The same bound holds for each value of $p^eY_N(U)\bmod p^{e+1}$ for every fixed $e\ge0$ making those rationals integral at $p$ on $I$. For example $p^{e+1}>\max I$ suffices. The constants are absolute and uniform in the prime, lifts, window, target and $e$. A higher-digit statement uses actual chosen rational lifts. The reduced rational $Y_N=A_N/Q_N$ enters as $p^e A_N/Q_N$ in the local ring.

For $N,N+h\in I$ write $r=N\bmod 6$. No multiple of $p$ occurs in $N+1,\ldots,N+h$. The removed part propagates by multiplication by $2^h$, so **both** $Z_{N+h}-2^hZ_N$ and $Y_{N+h}-2^hY_N$ equal the value at $X=N$ of

$$
F_{r,h}(X)=\sum_{j=1}^h\frac{2^{h-j}U(r+j)}{X+j}.
$$

Fix the start phase, a gap $6\le h<p$, and an ordered pair of targets $c,d$. For $Z$ the pair prescribes $F_{r,h}(N)=d-2^hc\bmod p$. For $p^eY$ it first requires $d-2^hc\equiv0\bmod p^e$, then prescribes $F_{r,h}(N)=(d-2^hc)/p^e\bmod p$, independent of the lifts of $c,d$ modulo $p^{e+1}$. In either case call the prescribed field value $v$. Clear the $h$ distinct poles in $F_{r,h}(X)-v$. The polynomial has degree at most $h$. At $X=-j$ for any index with $U(r+j)\ne0\bmod p$, its value is $2^{h-j}U(r+j)\prod_{k\ne j}(k-j)\ne0$, with $1\le k\le h$ in the product. Such an index exists because the gap contains a full period. Thus there are at most $h$ admissible starts in the given phase, since the starts in $I$ are distinct modulo $p$. For gaps shorter than six some projected weights vanish throughout the gap. Clearing poles on such a phase can give the zero polynomial.

Partition $I$ into bins of at most $H+1$ consecutive positions, $H=\lfloor T^{1/3}\rfloor<p$. Within each bin keep the first occurrence of the target **in each phase**. Charge each further occurrence to its preceding occurrence in that phase and bin. Its gap is a positive multiple of six at most $H$. Summing the pair bound over phases and these gaps gives at most

$$
6\left\lceil\frac{T}{H+1}\right\rceil
+6\sum_{1\le k\le H/6}6k=O(T^{2/3}).
$$

This includes $p=5$ and $H<6$, when the sum is empty. The argument also allows subtraction of any geometric term $C2^N$ with the required integrality, since its difference vanishes. Splitting once at a multiple of $p$ extends the count to arbitrary $T\le p$ consecutive positions. The precision $p^{e+1}$ matters. On the initial window, $p^eY_N$ is identically zero modulo $p^e$ for $e\ge1$. [Single-series one-pole predecessor](../../dyadic-prefix-residues.md)

## A counterexample to a real Fourier inference

Set $V=W-1=(-1,3,2,3,-1,0)$ periodically. The constant weight 1 and $W$ both sum to $\log2$ in the unshifted series. Hence the series for $V$ sums to zero and $|Y_N(V)|\le3/(N+1)$ by the omitted geometric tail. Every modular bound just proved holds for $V$. In fact every nonzero field projection of the pair $(W,1)$ has the same bound, by evaluating its weight at 1 and 2. The denominators satisfy $\liminf N^{-1}\log\mathrm{den}(Y_N(V))\ge1/2$. For every prime $p>3$ in $(N/2,N]$ the only pole term has index $p$ and $V(p)=-1$ since $p\equiv1,5\bmod6$. Its factor $p$ survives, and the prime number theorem gives the lower bound.

The real deficit satisfies $1-\cos(2\pi Y_N(V))\le 18\pi^2/(N+1)^2$. Its mean tends to zero even on arbitrarily late windows. This example lies outside the span of the two original weights, which both vanish at 1. It shows that the modular counting theorem and exponential denominator growth together are compatible with real concentration at an integer.

Even within the original two-component family, finite modular data cannot force a positive real deficit uniformly over integer lifts of the coefficients. Fix a finite list of prefix residues at any primes and precisions realized by some pair $(a,b)$. There is a common positive integer $D$ such that replacing $(a,b)$ by $(a+Du,b+Dv)$ preserves all those data for all integers $u,v$. For example multiply a common denominator of all measured component prefixes by a common multiple of the moduli. Put $L=\log(4/3)$ and $M=\log(9/8)$. Their ratio is irrational, since valuations at 2 and 3 of $4/3$ and $9/8$ form an integer matrix of determinant one. Hence $D(\mathbb ZL+\mathbb ZM)$ is dense in $\mathbb R$. For any finite horizon $H$ and $\varepsilon>0$ one can choose such lifts with $0<|(a+Du)L+(b+Dv)M|<2^{-H}\varepsilon$. All real shifts through $H$ then have deficit at most $2\pi^2\varepsilon^2$. The coefficients in this construction depend on the horizon.

For the fixed raw $W$, $|Y_N(W)-2^N\log2|\le4/(N+1)$, so a real cosine deficit for the moving prefixes would transfer to the true orbit by the Lipschitz bound. Obtaining that deficit requires information about their real fractional parts beyond the modular counting theorem. [Real Fourier criterion](../../classical-discrepancy.md#one-fourier-frequency-on-dyadic-blocks)

## Independent finite checks

Through $N=500$ for $t=0,2,5$, doubling the previous shifted prefix and inserting just the new terms at each binary exponent agreed with direct rational summation using Gaussian integer powers. The denominator divided $L_{\lfloor N/2\rfloor}$ throughout. For all odd primes with $p\le\lfloor N/2\rfloor<p^2$, the Frobenius residue and the divisibility of the reduced denominator agreed in all 37,911 tests.

For each prime $5\le p\le31$, direct rational recurrence for the full and deleted prefixes checked the difference congruences at every gap for the coefficient choices $(1,b)$, $0\le b<p$, and $(0,1)$. The windows started at $\ell p$ for $\ell=0,1,2,2p$, with $e=0,1,1,2$ respectively. All 163,920 ordered-pair differences agreed in both precisions. As an example containing an actual denominator divisible by $5^2$, the five residues $25Y_N(W)\bmod125$ at $N=50,\ldots,54$ are $32,14,78,31,37$. The corresponding $Z_N\bmod5$ are $2,2,1,2,3$.
