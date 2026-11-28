# Equality-boundary numerators and badly approximable polynomial-normal numbers

Fix an integer $b\ge2$, an odd prime $p\nmid b$, $t=\operatorname{ord}_p b$, $B=b^t$, and integers $d\ge2,\ s\ge1$. Write

$$
C_s(d)=\sum_{i\ge1}p^{-s v_p(i)}B^{-i^d},\qquad X=C_s(d)^d.
$$

Here $v_p(i)$ is the exponent of $p$ in $i$. The numeral system for digits is base $b$, and $m$ counts blocks of $t$ digits. Normality means that every word of length $k$ has limiting frequency $b^{-k}$. Absolute normality means this holds in every integer base. $D_N(x;b)$ is the supremum, over intervals in $[0,1)$, of the absolute difference between their length and their frequency among $\{b^j x\}$, $0\le j<N$. Logarithms without a subscript are natural.

* **Paper proof, §§1–2.** At explicitly specified fractional arrivals of both the square and the cube, the actual reduced prefix numerators visit a computable translate of the image of the unit $d$-th powers under exponentiation. The number of different residues grows as a power of the position. A one-gap irrationality test uses the actual incoming residue and the discounted coefficient mass after the gap. The scaled phases are equidistributed on these samples in the limit. The localized gap criterion and the finite-window bridge give tests for irrationality.
* **Paper proof + External input, §1.** The square irrationality result for $s<(390/449)\log B$ restates Phase 23 Theorem 1 using DEKKM’s two-square gap bound. The refinement predicts exact digit blocks. For the cube, Ghidelli’s weighted mild gaps give arbitrarily long blocks determined up to a single carry.
* **Paper proof using external input, §3.** Almost every continued fraction sampled with independent fair partial quotients 1 and 2 satisfies $q\|qx\|>1/4$ for every $q\ge1$, and every nonconstant rational polynomial in $x$ is normal in every integer base. There is a full-density bounded positive expansion of such numbers with an explicitly prescribed new prime at every position. This is a metric construction.
* **Paper proof, §3, computable construction.** There is also a computable full-density all-prime example with every rational polynomial image of positive degree absolutely normal and $q\|qx\|\gg1/(1+\log\log(3q))$. One may replace the growing bound on the partial quotients by any prescribed computable nondecreasing unbounded integer sequence. The selection algorithm uses finite continued-fraction cylinders and effective estimates for word frequencies.
* **Paper proof, §4.** A separate deterministic construction admits either of two independently prescribed positive shell coefficients at every doubling stage. Every choice has full occupied density, permanent off-radix primes, polynomial normality in the given base, and a uniform irrationality measure. Non-eventually-constant choices change the value of the underlying sparse series by an irrational number. The proof uses exact geometric summation.

[Phase 23 definitions and arithmetic inputs](../phase23/nonlinear-multivariate-and-denser-mu.md) · [Exact verifier](../../scripts/phase24_nonlinear_approx.py)

## 1. What size of gap suffices?

**Paper proof.** Let $c_m$ be the sum of $p^{-s\sum_i v_p(x_i)}$ over ordered positive tuples with $\sum_{i=1}^d x_i^d=m$. Define the shifted prefix $R_M=\sum_{m\le M}c_m B^{M-m}$, its reduced denominator $q_M$, its numerator modulo this denominator $A_M\in[0,q_M)$, and $T_M=B^M X-R_M>0$. When $M+g$ is the first represented position strictly after $M$, put

$$
H_M=\sum_{j\ge0}c_{M+g+j}B^{-j}.
$$

Then $T_M=B^{-g}H_M$. If $QX\in\mathbb Z$, define $r_M(Q)\in\{1,\ldots,q_M\}$ by $r_M(Q)\equiv-QA_M\bmod q_M$, using $q_M$ for residue zero. Necessarily

$$
Qq_M B^{-g}H_M\ \in\ r_M(Q)+q_M\mathbb Z_{\ge0}.
\tag{1}
$$

Indeed $Q B^M X$ is an integer and the tail is strictly positive. Thus $B^g>Qq_M H_M/r_M(Q)$ excludes this $Q$. This is the exact first positive lattice threshold when only an upper bound for the tail is used. For example $r_M(Q)\ge\delta q_M$ removes the entire denominator from that threshold up to $1/\delta$. With no incoming residue information, $\liminf_M q_M H_MB^{-g}=0$ suffices for irrationality. Equivalently the margin $g\log B-\log q_M-\log H_M$ is unbounded above. This equivalence concerns the denominator-only test. Irrationality need not produce such gaps. Testing several gaps permits different witnesses $M$ for different $Q$.

AM–GM gives $\prod_i x_i\le m/d$. Consequently the prefix denominator divides $p^{s\lfloor\log_p(M/d)\rfloor}$ for $M\ge d$. It has order $M^s$ at $M=d p^{da}$ by the unique equal-coordinate tuple in §2. Thus the exponent $s$ in the global denominator bound is attained. If $c_m\ll_\epsilon m^{\alpha+\epsilon}$, with $\alpha\ge0$, then $H_M\ll_\epsilon M^{\alpha+\epsilon}$ for large $M$. Indeed $M+g=O_d(M)$ by using $x^d+(d-1)$, and the remaining polynomial factor in $j+1$ is summable with $B^{-j}$. In particular a sufficient gap-only condition is

$$
\limsup_{M\to\infty}\frac{g}{\log M}>\frac{s+\alpha}{\log B}.
\tag{2}
$$

For general $d$ one can take $\alpha=(d-1)/d$ by fixing all but the last coordinate. For the square one can take $\alpha=0$ by the two-square divisor bound $r_2(m)\le4\tau(m)\ll_\epsilon m^\epsilon$. For the cube one can take $\alpha=1/3$. After fixing $x$, $y+z$ divides $m-x^3$, and the sum and $yz=((y+z)^3-(m-x^3))/(3(y+z))$ determine the ordered pair up to interchange. If the actual post-gap mass is $M^{o(1)}$ on the test sequence, (2) uses $\alpha=0$ there, in either degree.

**External input.** Dietmann, Elsholtz, Kalmynin, Konyagin and Maynard give the constant $390/449$ for the limsup of the two-square gaps as a **lower bound**. Their integers allow zero coordinates. A gap between them is empty also for positive coordinates, and one may start the test at the left endpoint even if its positive-coordinate coefficient vanishes. Żmija also treats simultaneous discriminants. [DEKKM, Theorem 1](https://doi.org/10.1093/imrn/rnac130) · [Żmija, introduction](https://arxiv.org/html/2509.15365v1)

**Paper proof + External input.** In the square range $s<(390/449)\log B$, (2) and DEKKM recover [Phase 23 Theorem 1](../phase23/nonlinear-multivariate-and-denser-mu.md) with $B=b^t$. More precisely, for any $0<\lambda<((390/449)\log B-s)/\log b$, infinitely many shifts $tM$ have the following property. The next $\lfloor\lambda\log M\rfloor$ digits of $X$ agree exactly with the initial digits of $\{R_M\}$. For length $L$ the distance of $R_M$ to the *next strictly larger* $b^{-L}$-grid point is at least $1/(q_M b^L)$, also when $R_M$ lies on the grid. On the DEKKM subsequence $q_M b^L T_M<1$ by the strict margin. These blocks can be digits of nonintegral rational prefixes. A support gap alone does not make them runs of zero digits. Irrationality gives at least $L+1$ distinct length-$L$ words for every $L$. Indeed word counts strictly increase until two consecutive counts agree, at which point each occurring word has a unique right extension, and the finite succession of words is eventually periodic. A nonperiodic expansion uses at least two digits.

**External input.** For three nonnegative cubes Ghidelli gives gaps of length $\gg\sqrt{\log N}/(\log\log N)^2$ below $N$. The stronger information needed to bound the *tail* is in his theta-series paper. In the proof of Theorem 1.1, §8.1 sets $E=60\xi_3$ with $\xi_3=(\log T)^{C_3}$. Lemma 7.1(i)–(ii) gives $\log N\asymp T$ after the choice of $N$ in §8.1. Section 8.2 constructs mild gap starts (Definition 3.2) in $[0,N-K_2)$ for $T$ above a threshold independent of Ghidelli’s $q$ and $J$. These starts $n$ have lengths $K\gg\sqrt T/(\log T)^2$, and

$$
r(n)=\cdots=r(n+K-1)=0,\qquad
\sum_{j\ge0}r(n+K+j)2^{-j}\le 60(\log T)^{C}
$$

for the ordered nonnegative representation count $r$ and the unspecified absolute exponent $C=C_3$ from Ghidelli’s Waring estimates in Lemma 7.1. This second input controls the coefficients immediately following the gap. The general cubic gap theorem alone does not include that conclusion. Cubes mod 9 are $0,1,-1$, which excludes 4 and 5. Counting unordered triples gives an upper bound $\binom{\lfloor N^{1/3}\rfloor+3}{3}=N/6+O(N^{2/3})$. Neither fact settles the density of represented integers. [Ghidelli, cubic gap theorem](https://doi.org/10.1112/jlms.12312) · [Ghidelli, arXiv:1910.05076v1, Definition 3.2, Lemma 7.1 and §§8.1–8.2](https://arxiv.org/pdf/1910.05076v1) · [2026 survey of sums of three positive cubes](https://doi.org/10.1112/jlms.70554)

**Paper proof + External input.** At $M=n-1$, $T_M\le B^{-K-1}60(\log T)^C$, since $c_m\le r(m)$ and $B\ge2$. For every fixed $\epsilon\in(0,1)$ take $L=\lfloor(1-\epsilon)tK\rfloor$. Eventually $b^LT_M<1$, so the next $L$-digit word, read as an integer modulo $b^L$, is either $\lfloor b^L\{R_M\}\rfloor$ or its successor. This gives an unconditional two-word prediction for arbitrarily long cubic blocks for every $s$. Equation (1) would further exclude any fixed $Q$ if these starts had $r_M(Q)/q_M$ bounded below along a subsequence. The published lower bound for the gap length is sublogarithmic in $N$ and by itself does not pay the $M^s$ denominator. For $b=2,p=3,s=1$, (2) still gives the sufficient threshold $2/(3\log2)$.

**Open.** Irrationality of this flagship cube and of squares outside the stated range is unresolved by these arguments. No lower bound for a positive density of digit transitions, disjunctivity, or real equidistribution follows from the numerator residues below.

## 2. Actual numerators at consecutive and selected fractional arrivals

**Paper proof.** At rational phases we always take the numerator of the fractional part. For arbitrary consecutive fractional arrivals $u<v$, let $e_u,e_v$ be their reduced prefix depths and let $e$ dominate both and every intervening coefficient depth. The exact common-grid recurrence is

$$
p^{e-e_v}A_v\equiv B^{v-u}p^{e-e_u}A_u+
\sum_{i=u+1}^{v} B^{v-i}p^e c_i\pmod{p^e}.
\tag{3}
$$

It follows by shifting the prefix, and includes reductions in depth. Integer coefficients between fractional arrivals make zero contributions modulo $p^e$.

**Theorem.** Take $d=2$ or $3$, write $U=p^a$, $M=dU^d$, $E=sda$. For $h\ge1$, put $v=\lceil h/s\rceil\le a+1$ and $G=p^{d(a-v+1)}$. Throughout the integer interval $[M,M+G)$ every prefix denominator is exactly $p^E$. For every pair of its shifts, in particular for consecutive fractional arrivals, the actual numerators satisfy

$$
A_y\equiv B^{y-x}A_x\pmod{p^h}\qquad(M\le x\le y<M+G).
\tag{4}
$$

Here $h\le E$ is understood. Before $M$, AM–GM makes total valuation $da$ impossible. At $M$ only $(U,\ldots,U)$ attains it, so $A_M\equiv1\bmod p$. In the interval every coordinate is $<2U$ because $d+1\le 2^d$, hence its valuation is at most $a$. A tuple contributing nontrivially to $p^E c_m\bmod p^h$ has total valuation loss $\sum(a-v_p(x_i))\le v-1$. Each coordinate is divisible by $p^{a-v+1}$. Its position is therefore a multiple of $G$. The interval contains just the one multiple $M$. Now (3) and the fact that $B$ is a unit prove both claims. Formula (4) is a perfect correlation for the actual low residue digits, even though the numerators at modulus $p^E$ also receive nonzero innovations.

Put $J=\lfloor G/(d\,2^d U^{d-1})\rfloor$. For each $1\le j\le J,\ p\nmid j$, the position

$$
m_j=(d-1)U^d+(U+j)^d
$$

is a **fractional** arrival, for $s(d-1)a>v_p(d)$. Indeed $J\le U$, and the mean-value bound $d(2U)^{d-1}J\le G/2$ puts it in the interval. Since $m_j\equiv j^d\not\equiv0\pmod p$, at least one coordinate is a unit, so the greatest possible level is $(d-1)a$. To attain that level for $a\ge1$, the other coordinates must all be $U$. This gives exactly the $d$ permutations displayed above. If $p\nmid d$, the innovation has depth exactly $s(d-1)a$. When $d=p=3$, there are no diagonal triples at this position modulo 3. All triples split into cyclic orbits of length three, level by level. Dividing every level count by three before reduction shows that the depth is precisely $2sa-1$.

Let $w=v_p(B-1)$, $k=h-w>0$, and suppose $a\ge k$. Binomial expansion gives $v_p(B^n-1)=w+v_p(n)$ for $n\ge1$ (raising a principal unit to $p$ increases its depth by one, and a prime-to-$p$ power preserves depth). The order of $B\bmod p^h$ is $p^k$. By (4),

$$
A_{m_j}\equiv A_M B^{j^d}\pmod {p^h}.
$$

In each complete period of $p^k$ candidate indices the unit $j$'s therefore give precisely

$$
\frac{\varphi(p^k)}{\gcd(d,\varphi(p^k))}
\tag{5}
$$

distinct *actual* residues, each with multiplicity $\gcd(d,\varphi(p^k))$, by cyclicity of the units at an odd prime power. The terminal incomplete period changes each multiplicity by at most this gcd. Exactly, $J=\lfloor p^{a-d(v-1)}/(d2^d)\rfloor\ge p^{a-dh/s}/(d2^d)-1$. The floor can give $J=0$, as in the $s=1$ cube fixture at $a=3,h=2$. Taking $h=\lfloor\gamma a\rfloor$ with $0<\gamma<s/(s+d)$ gives $J\asymp p^{a-dh/s}\gg p^k$, with $J/p^k\to\infty$. Thus there are $M^{\gamma/d+o(1)}$ distinct residues with asymptotically equal relative multiplicities on this selected subsequence within each shell. The result uses a subset of fractional arrivals for the histogram and every arrival in the window for (4). Knowing low residue digits of $A_m$ leaves the leading base-$b$ digits of $A_m/p^E$ undetermined.

**Real distribution after scaling (Paper proof).** On the same selected arrivals the phases $\{p^{E-h}R_{m_j}\}$ are uniformly distributed in the limit $a\to\infty$, with interval discrepancy

$$
O_{p,d,B}\bigl(p^{-h}+p^k/J\bigr).
$$

To see this set $u=1+v_p(d)$ and take $k\ge u$. The set of unit $d$-th powers modulo $p^k$ contains every lift of each of its residues modulo $p^u$. Indeed the principal units $1\bmod p$ form a cyclic group of order $p^{k-1}$, and their $d$-th powers form the entire subgroup $1\bmod p^u$ by its order and the binomial valuation. Thus each exponent class lifts as $j^d\equiv z\bmod p^u$. Exponentiating, $B^{p^u}$ generates the subgroup $1\bmod p^{w+u}$ modulo $p^h$. Multiplication by the unit $A_M B^z$ gives all lifts of its residue modulo $p^{w+u}$. After division by $p^h$, each resulting class is a translated grid of spacing $p^{w+u-h}$. A full period from (5) is a mixture of these uniform grids, and the last incomplete period has relative weight $O_p(p^k/J)$. This proves the estimate. It concerns scaled phases with scale depending on the shell.

**A localized multi-gap criterion (Paper proof).** If $QX$ is integral, the proportion on this same sample for which $p^{E-h}T_{m_j}\le\eta$ is at most

$$
\min(1,Q\eta)+O_{p,d,B,Q}\bigl(p^{-h}+p^k/J\bigr)\qquad(\eta>0).
$$

In fact $Qp^{E-h}(R_{m_j}+T_{m_j})$ must be integral, so the scaled prefix times $Q$ is confined on those arrivals to a closed arc ending at zero, of length $Q\eta$ when $Q\eta<1$. Multiplication by $Q$ pulls an arc back to at most $Q+1$ intervals of the same total length; endpoints are covered by taking slightly larger intervals. In particular, if on a fixed positive proportion in infinitely many of these shells the gap immediately after $m_j$ exceeds $\lambda\log M$, then irrationality follows whenever

$$
\lambda>\frac{s+\alpha-\gamma/d}{\log B},\qquad 0<\gamma<s/(s+d).
$$

Indeed $p^{E-h}=M^{s-\gamma/d+o(1)}$ and $H_{m_j}\ll_\epsilon M^{\alpha+\epsilon}$. The strict margin permits $\eta\to0$. This saves $\gamma/d$ in the numerator of (2) at the cost of a new hypothesis on *where and how often* gaps occur. Neither cited gap theorem supplies this frequency at the selected arrivals.

**An exact finite-window bridge (Paper proof).** For any $Q\ge1$ compute

$$
Y_{m,L}(Q)=Q\left(A_m/q_m+\sum_{j=1}^L c_{m+j}B^{-j}\right)\pmod1 .
$$

Choose $L=\lceil(d+2)\log_B(m+2)\rceil$. Uniformly for fixed $Q$ its circular distance from $QB^mX\bmod1$ tends to zero, by the polynomial coefficient bound in §1 and the geometric tail. Then $X$ is irrational **if and only if**, for every $Q$, $\limsup_m\|Y_{m,L}(Q)\|\ge1/(B+1)$, where the norm is distance to the nearest integer. For if eventually $\|B^m QX\|\le c<1/(B+1)$, nearest integers $z_m$ satisfy $|Bz_m-z_{m+1}|\le(B+1)c<1$. Iteration forces $B^m QX=z_m$ from that point onward. Conversely for rational $X$ its denominator gives a vanishing limit. The escape constant is optimal for the single-orbit implication to eventual integrality, since $1/(B+1)$ has a two-cycle of exactly this distance. This criterion incorporates the actual numerator and the next logarithmically many innovations. Neither (4) nor (5) establishes this real-circle condition for the open cube.

## 3. Bad approximation and polynomial normality in every base

**Theorem (Paper proof using external input).** Draw independent fair $a_j\in\{1,2\}$ and take $x=[0;a_1,a_2,\ldots]$. With probability one every nonconstant $P\in\mathbb Q[X]$ has $P(x)$ normal in every integer base. All samples satisfy $q\|qx\|>1/4$ for all $q\ge1$.

**External input.** Hochman–Shmerkin, Theorem 1.4, gives pointwise normality in integer base $b$ for a quasi-product measure of a regular $C^{1+\epsilon}$ interval iterated function system under their hypothesis “there exists an $f\in I$ with $\lambda(f)\not\sim\beta$”, where $\beta=b$ and $\lambda(f)$ is the derivative at its fixed point. It gives the same for the pushforward under each fixed $C^1$ diffeomorphism. Their §1.3.3 treats the regular continued-fraction system of *pairs* of digits. [Hochman and Shmerkin, *Equidistribution from fractal measures*, Invent. Math. 202 (2015), 427–479](https://doi.org/10.1007/s00222-014-0573-5) · [Author’s version, Theorems 1.4 and 1.12, §1.3.3](https://math.huji.ac.il/~mhochman/preprints/normality.pdf)

**Proof.** The four maps $f_i\circ f_j$, $f_i(x)=1/(i+x)$, have disjoint cylinder interiors on $[0,1]$ and are smooth with $0<(f_i\circ f_j)'(x)=(i(j+x)+1)^{-2}\le1/4$. Paired fair digits give the product measure on the four branches. At the fixed point $\rho=(\sqrt5-1)/2$ of $f_1$, the derivative of $f_1^2$ is $\rho^4$. Its algebraic norm is 1, whereas the norm of $b^n$ in the quadratic field is $b^{2n}$. Thus $\log(\rho^4)/\log b\notin\mathbb Q$, or $\lambda(f_1\circ f_1)\not\sim b$ in their notation. This checks the hypothesis for every $b$.

Cover $\{x:P'(x)\ne0\}$ by countably many compact intervals contained in it. On each, $P$ or $-P$ extends to an increasing global $C^1$ diffeomorphism by continuing with the two endpoint tangent lines. Negation preserves uniform distribution modulo one. The measure assigns mass zero to the finitely many critical points since each length-$n$ digit cylinder has mass $2^{-n}$. Intersect the resulting full-measure sets over the intervals, polynomials and bases.

For completeness, for convergents $p_i/q_i$, with complete quotient $\alpha_{i+1}=[a_{i+1};a_{i+2},\ldots]$, the determinant identity gives

$$
q_i|q_ix-p_i|=\frac{1}{\alpha_{i+1}+q_{i-1}/q_i}>\frac14 .
$$

Here $q_{-1}=0,\ q_0=1$, $\alpha_{i+1}<3$, and $q_{i-1}\le q_i$. For $q_i\le q<q_{i+1}$ choose the last such $i$ if the initial denominators repeat. The best-approximation inequality $|qx-h|\ge|q_ix-p_i|$ follows by expanding $(h,q)=u(p_i,q_i)+v(p_{i+1},q_{i+1})$ in this unimodular basis. For $v=0$ the conclusion is immediate. Otherwise $u,v$ have opposite signs, $u\ne0$, and the two convergent errors have opposite signs. This proves the claimed constant, including $q=1$. Dirichlet approximation then gives $\mu(x)=2$.

### A different prime at every occupied position

**Paper proof.** Fix the requested radix $b$. Enumerate the primes away from $b$ in increasing order as $\ell_1,\ell_2,\ldots$, and set $S=\sum_{n\ge1}\ell_n^{-1}b^{-n}$. For the sample $x$ above let $d_n$ be the ordinary base-$b$ digits of $\{x-S\}$, taking the terminating expansion at an endpoint. Then

$$
Z=\sum_{n\ge1}(d_n+1/\ell_n)b^{-n}
   =S+\{x-S\}=x-\lfloor x-S\rfloor .
\tag{6}
$$

Thus $q\|qZ\|>1/4$. Integer translation preserves the conclusion for **all** rational polynomials by translating the polynomial argument. The extra fixed diffeomorphism $y\mapsto y-S$ in the same external theorem shows that the digit sequence $d_n$ is base-$b$ normal almost surely. In particular these integer coefficients vary on the scale of individual positions. Every coefficient in (6) is positive and less than $b$, with reduced denominator $\ell_n=O_b(n\log(2n))$ by the prime number theorem. Every position is occupied, $n_j=j$. The shifted prefix at $N$ has denominator exactly $\prod_{n\le N}\ell_n$, since each $\ell_n$ occurs in precisely one term and $b$ is a unit at it. Even after multiplication by this product, reduction at each prime leaves the unique nonzero summand. This example rules out a universal inference of unbounded partial quotients from persistent unbounded prime support in bounded positive expansions.

Equation (6) is an encoding of a continued-fraction sample. The prime weights supply the denominator property, while the measure theorem supplies the real arithmetic property. This produces a probability-one family with an explicit uniform constant. The following effective construction allows the partial quotients to grow.

**A forward choice of dense coefficients (Paper proof).** Alternatively fix the same $S$ and choose the $d_n$ independently and uniformly from $0,\ldots,b-1$ *before* forming (6)'s series. For this construction $Z$ is uniform on $[S,S+1]$, since every digit cylinder has its length as probability. Every nonconstant rational polynomial image of $Z$ is absolutely normal almost surely. Indeed outside the finitely many critical points the inverse on each compact monotone noncritical interval is Lipschitz. Pull back the Lebesgue-null exceptional sets for normality and use countable unions. Lebesgue-almost-everywhere normality follows, for instance, by applying the strong law to indicators of each word in the disjoint blocks of each fixed starting congruence class. For each $\epsilon>0$, the measure of points within $q^{-2-\epsilon}$ of some $h/q$ on this bounded interval is $O(q^{-1-\epsilon})$. Borel–Cantelli, followed by Dirichlet, proves $\mu(Z)=2$ almost surely. This construction has independent coefficient choices at all positions and changes the value. It does not give the bounded-partial-quotient conclusion for typical independent radix digits.

### A computable example with an arbitrarily slow growing bound on its partial quotients

**Theorem (Paper proof).** Let $A_i\ge2$ be any computable, nondecreasing, unbounded sequence of integers. One can compute $x=[0;a_1,a_2,\ldots]$ with $a_i\le A_i$ such that every nonconstant rational polynomial image of $x$ is absolutely normal. For a fixed $b$, the same construction makes $x-S$ base-$b$ normal for the computable $S$ of (6). Thus (6) gives a computable, genuinely varying, positive full-density coefficient sequence with every off-radix prime retained. Both $x$ and $Z$ satisfy

$$
q\|qx\|>\frac{1}{2+A_{\lfloor 2\log_2 q\rfloor+3}} .
\tag{7}
$$

In particular $A_i=\max(2,\lceil\log_2(i+1)\rceil)$ gives $q\|qx\|\gg1/(1+\log\log(3q))$. The growth of $A_i$ supplies an effective elementary proof here even though the fixed cap 2 already suffices for metric existence.

**1. Interval mass.** Give each allowed continued-fraction child its ordinary Lebesgue length relative to the surviving children, recursively starting on $[0,1]$. Denote the resulting probability by $\nu$. If a parent has convergent denominators $q,q'$ (current and previous) and $y=q'/q$, the relative Lebesgue length retained by the next cap $A$ is exactly $A/(A+1+y)$. Indeed the children have lengths $1/((j q+q')((j+1)q+q'))$, whose sum for $1\le j\le A$ telescopes. The parent has length $1/(q(q+q'))$. Every depth-$m$ cylinder $I$ therefore satisfies

$$
\nu(I)\le L_m |I|,\qquad L_m=\prod_{i=1}^m(1+2/A_i).
$$

All cylinder lengths are at most $2^{1-m}$ since $q_{i+2}\ge2q_i$. In particular this measure is nonatomic: $\log L_m\le2\sum_{i\le m}1/A_i=o(m)$, and any infinite path lies in shrinking cylinders. Infinite regular continued fractions with positive digits are irrational. If $E\subset[0,1]$ is a union of at most $K$ intervals, cover it by the depth-$m$ cylinders meeting it. Their union lies in its $2^{1-m}$-neighborhood, giving

$$
\nu(E)\le L_m\bigl(|E|+2K\,2^{1-m}\bigr).
\tag{8}
$$

The little-oh has an effective modulus: for any integer $j\le m$, $\log L_m\le 2j+2m/A_j$. Search until $A_j$ exceeds a required constant, then increase $m$ to absorb $2j$.

**2. Effective exceptional sets.** A test specifies an integer base $b_0$, a length-$k$ word, a positive rational tolerance $\epsilon$, and a map $P$ of degree $r\ge1$. Use every nonconstant rational polynomial and include the single computable translation $X-S$. A bad length-$N$ prefix has relative frequency among its $N-k+1$ possible word starts differing from $b_0^{-k}$ by more than $\epsilon$. On Lebesgue measure the union of these digit intervals has length at most

$$
2k\exp\{-2\epsilon^2\lfloor(N-k+1)/k\rfloor\}\qquad(N\ge2k).
$$

Indeed every residue class of starts modulo $k$ uses disjoint blocks and hence independent Bernoulli indicators. One class must violate the same tolerance. For a Bernoulli indicator the logarithm of its centered exponential moment has value and derivative zero at zero and second derivative at most $1/4$ (a Bernoulli variance after exponential tilting). Markov's inequality with parameter $4\epsilon$ and its negative gives the two tails. Enlarge each bad interval by $b_0^{-2N}$ on each side and use open intervals, allowing wraparound. Their number is $O(b_0^N)$ and the additional length is at most $2b_0^{-N}$. This open set covers even the ambiguous endpoints of bad cylinders.

Take the preimage under $P$ modulo one on $[0,1]$, denoting it by $E_N$. There are $O_P(1)$ translated copies in the bounded range of $P$, and at most $r$ monotonicity branches, hence $K=O_P(b_0^N)$ intervals. The total input length is bounded by $C_P u^{1/r}$ when the total target length in that range is $u\le1$. For $r=1$ divide by the absolute slope. For $r>1$, where $|P'|\ge\eta$ use change of variables on each branch to obtain $ru/\eta$. Where $|P'|<\eta$, the product formula for $P'$ puts the point within $(\eta/|r\,\mathrm{lc}(P)|)^{1/(r-1)}$ of some complex root of $P'$, giving total length at most twice $r-1$ times this radius. Choose $\eta=u^{(r-1)/r}$. These bounds have computable constants, using the sum of absolute coefficients to bound the range. For $X-S$ the slope is 1 and $0<S<1$.

In (8) use $m=2\lceil\log_2 b_0\rceil(N+2)$. The endpoint error before multiplication by $L_m$ is $O_P(b_0^{-N})$. Both terms in parentheses decay exponentially in $N$, with explicit bounds just given, whereas $\log L_m=o(N)$ effectively for the fixed test. Thus one can compute $N_0$ and a rational $\delta>0$ such that $\nu(E_N)\le 2^{-\delta N}$ for $N\ge N_0$. For example, first bound the parentheses by $2^{-2\delta N}$ with a strict exponent margin, then use the $j$-bound following (8) to absorb $L_m$. All estimates are uniform algorithms in the finite test data and the cap algorithm.

**3. Selecting one point.** Enumerate the tests by $e=1,2,\ldots$. For each compute $N_e$ with $\sum_{N\ge N_e}\nu(E_{e,N})<2^{-e-2}$, using the geometric bound. The complement $F$ of all these open events is closed and has $\nu(F)\ge3/4$. For any continued-fraction cylinder $I$, $\nu(F\cap I)$ is computable. To prescribed accuracy omit large $e$ by the budget, then large $N$ for the finitely many remaining tests by the geometric bounds. The remaining union has finitely many intervals whose endpoints for rational polynomials can be isolated by real polynomial root isolation. The affine translation uses the computable endpoints $S+\text{rational}$. Their masses are computable by refining the finite allowed-cylinder partitions and summing the rational masses of definitely interior cylinders. Each depth-$m$ cylinder has mass at most $L_m2^{1-m}$, which tends effectively to zero by the $j$-bound after (8). At most two closed cylinders meet a given endpoint. Choose $m$ so twice this mass bound per endpoint fits the error budget, then approximate each endpoint in a rational interval narrower than the minimum separation of distinct depth-$m$ partition boundaries. Each such interval meets at most two cylinders. Endpoint comparisons can equivalently use enclosing rational intervals of shrinking width, so coincident computable endpoints pose no decision problem.

Starting at the root, refine the mass estimates of its allowed children in parallel until some child is certified to have positive surviving mass, taking the first such child at that precision in digit order. Repeat within it. Finite additivity and positive parent mass ensure termination at every step. The nested closed cylinders shrink to a point of $F$, by compactness. This gives a computable continued fraction. For every tested word its tolerance eventually holds on every prefix. Enumerating tolerances $1/j$ yields the claimed normalities. In particular $x-S$ is irrational and its radix digits in (6) can be computed by interval refinement. This coefficient computation uses the selected limit and does not furnish independent random radix digits.

Finally for $q_i\le q<q_{i+1}$ the convergent estimate above gives $q\|qx\|>1/(A_{i+1}+2)$. The bound $q_i\ge2^{(i-1)/2}$ proves (7). Formula (6) changes $x$ only by an integer, so the very same estimate holds for the all-prime series. This construction obtains the slow measure by choosing the continued fraction, independently of the sparse folding method.

### Where folding loses quantitative information

**Paper proof.** For a reduced rational $u=a/q$, put $F(u)=\inf_{h/l\ne u,\ l\ge1}l^2|u-h/l|$. Phase 23 Lemma 5 proves $F(u+z/q^2)\ge\min(|z|,F(u)/(2c^2))$ for $z=c/d_z\ne0$ reduced. Thus if $H_k=-\log F(u_k)$, one step gives at most

$$
H_{k+1}\le\max\{\log(1/|z_k|),\, H_k+\log2+2\log|c_k^*|\},
\tag{9}
$$

where $c_k^*$ is the reduced numerator of the *scaled increment* $z_k$. The $O(k)$ logarithmic heights at the Phase 23 sparse dyadic steps give an $O(k^2)$ accumulated defect. At $k\asymp\log\log q$ this yields the measure in §4, stronger than the assertion of the exponent alone. Even the factor 2 at each step allows an $O(k)$ loss in this estimate with unit numerators. An upper bound for this loss cannot prove that the actual partial quotients grow.

There is a sharper obstruction for **literal positive reciprocal folds**. Suppose $u_{k+1}=u_k+1/(m_k q_k^2)$, $m_k\ge1$ integral, $q_1\ge2$, where $q_k=\operatorname{den}(u_k)$. The next denominator is exactly $q_{k+1}=m_k q_k^2$, since the numerator $a_km_k q_k+1$ is coprime to $m_kq_k$. In the limit $u$, successive increments after the first are at most one quarter their predecessor: their ratio is $1/(m_{k+1}m_k q_k^2)\le1/4$. Hence

$$
0<q_k^2(u-u_k)\le\frac{4}{3m_k}.
$$

If a fresh prime $\ell$ enters this denominator at that step, then $m_k\ge\ell$. In particular unbounded fresh primes force failure of bad approximation. The limit is irrational by rational separation and $q_k\to\infty$. For $m_k\ge3$, Legendre's convergent criterion applies to $u_k$, since $4/(3m_k)<1/2$. The complete quotient formula above implies its next partial quotient exceeds $3m_k/4-2$. This lower bound specifically uses the size of the true increment and a positive tail. Signed rational folds or the dense series (6) need not satisfy it.

## 4. Deterministic full-density series with freely prescribed shell values

**Theorem (Paper proof).** Use the sparse number $W=\sum_{k\ge1}c_k b^{-2^k}$ of Phase 23 Theorem 6. Explicitly, $\mu_{j^2}=\ell_j$ is the $j$-th prime away from $bp$, $\mu_k=1$ at other indices, and $c_k=u_k/(p^k\mu_k)$. Take the least positive solution of $u_k\equiv\mu_k b^{2^k}\bmod p^k,\ u_k\equiv1\bmod\operatorname{rad}(b)\mu_k$. For an arbitrary sequence $a_k\in\{1,2\}$ define

$$
V(a)=W+\sum_{k\ge1}a_k\sum_{2^k<n\le2^{k+1}} b^{-n}.
\tag{10}
$$

Every integer position $n\ge2$ is occupied. The coefficients are positive and at most $\operatorname{rad}(b)+2$. Every nonconstant $P(V(a))$, $P\in\mathbb Q[X]$, has a power-saving discrepancy in base $b$. There are constants $c,C>0$ depending only on $b,p$, such that for every choice and every $q\ge1$,

$$
\|q V(a)\|\ \ge\ \frac{c}{q}\exp\{-C(\log\log(3q))^2\}.
\tag{11}
$$

In particular $\mu(V(a))=2$. These conclusions include a concrete nonperiodic choice, for example $a_k=1+(v_2(k)\bmod2)$.

**Proof.** CRT gives $0<c_k\le\operatorname{rad}(b)$. At each raw shift from $2^k$ until $2^{k+1}-1$ the ordinary shifted prefix has exact denominator $D_k=p^k\prod_{j^2\le k}\ell_j$, by the unique deepest $p$-pole, unique auxiliary occurrences, and the integrality of all fillers. Its logarithm is $O_{b,p}(k)$, since the auxiliary contribution is $O_b(\sqrt k\log(2k))$. With $a_0=0$, summing each finite geometric series gives the second expansion

$$
V(a)=\sum_{k\ge1}d_k b^{-2^k},\qquad d_k=c_k+(a_k-a_{k-1})/(b-1).
\tag{12}
$$

Equation (12) uses the regrouping of Phase 23 Theorem 7 with $h_k\equiv1$ and shell multiplier $a_k$, so $\lambda_k=a_k/(b-1)$. The free binary choice preserves full occupancy and permits an irrational perturbation. Let $v_0=v_p(b-1)$. The bound $|d_k|\le\mathrm{rad}(b)+2/(b-1)$ fixes a common tail-buffer constant for each polynomial. The $d_k$ have depth exactly $k$ when $k>v_0$, and $p^k b^{-2^k}d_k\equiv1\bmod p^{k-v_0}$ in $\mathbb Z_p$. The prime-to-$bp$ part of the denominator of any degree-$r$ shifted polynomial prefix divides the prime-to-$bp$ part of $((b-1)\prod_{j^2\le k}\ell_j)^r$ times the fixed polynomial denominator (after a fixed clearing of radix primes). The logarithm of this common bound is $o(k)$. The factor $(b-1)^r$ introduced by the shell correction is fixed, so the complementary order bound is uniform in the labels.

For $2^k\le n<2^{k+1}$, normalize the degree-$r$ unshifted convolution prefix by $p^{rk}$. The potentially surviving tuples at any fixed precision $L$ have indices $k-h_i$ with $\sum h_i<L$, for $k\ge2L+v_0$. Indeed every early coefficient ($i\le v_0$) has depth at most $v_0$ for either label. Every surviving index has $i>k-L$, so its unit congruence has precision at least $L$. The residue is the sum of $p^{\sum h_i}$ on the upper set $\sum 2^{-h_i}\le n/2^k$ modulo $p^L$. The anchored-upper-set lemma of Phase 23 §7 supplies a uniform $L=L(p,r)$ making this residue nonzero. Lower degrees have depth at most $(r-1)k+O_P(1)$. Thus the reduced depth of a degree-$r$ prefix is $rk+O_P(1)$, uniformly in $a$. There are $O_r((1+\log N)^r)$ possible coefficient positions through $N$ in (12)'s convolution. These are exactly the hypotheses used in the sparse-case digit-transfer proof in Phase 23 §7: after logarithmic tail buffers, shifts below $\sqrt N$ and components shorter than $N^{1/3}$ are removed, the remaining runs have complementary order $N^{o(1)}$ and $p$-depth comparable to $\log N$. Its short-orbit estimate gives $D_N\ll_{P,b,p}N^{-\eta_P}$ for some $\eta_P>0$, uniformly in the choices. Signed coefficients in (12) satisfy the same absolute tail estimates. [Arithmetic and short-orbit inputs, Phase 23 Theorems 6–7](../phase23/nonlinear-multivariate-and-denser-mu.md)

For (11), put $U_k=\sum_{i\le k}d_i b^{-2^i}$, $q_k=\operatorname{den}(U_k)$ and $E_k=(b-1)D_k$, so $E_k d_i$ is integral for $i\le k$. For large $k$, $0<|E_kd_k|\ll_b E_k$. Over denominator $E_k b^{2^k}$ the numerator is congruent to $E_kd_k\bmod b^{2^{k-1}}$. At each prime of $b$ the two valuations agree, since $\log E_k=O_{b,p}(k)$. Hence the cancelled radix factor divides $|E_kd_k|$, and the cancelled off-radix factor divides $E_k$. Both numerator and denominator of $q_k/b^{2^k}$ in lowest terms are $\exp(O_{b,p}(k))$. The increment $z_k=d_{k+1}(q_k/b^{2^k})^2$ is nonzero with both heights $\exp(O_{b,p}(k))$. Equation (9) gives $F(U_k)\ge\exp(-O_{b,p}(k^2))$. At a fixed starting index there are only finitely many possible prefixes.

For large $q$, choose the first $2^k\ge4\log_b q$. Then $q_k>q$, $k=O_b(\log\log(3q))$, and $|V(a)-U_k|\ll_b b^{-2^{k+1}}\ll_b q^{-8}$. For every integer $h$, $|U_k-h/q|\ge F(U_k)/q^2$. Subtract the tail to obtain (11) for large $q$, uniformly. This already excludes rational limits by taking multiples of their denominators. For the finitely many small $q$, compactness of $\{1,2\}^{\mathbb N}$ and continuity of (10) give a positive minimum of each continuous function $\|qV(a)\|$. This proves the uniform claim.

Finally subtract the rational baseline $\sum_{n>2} b^{-n}$ from the filler in (10). Its ordinary digits on the $k$-th shell are $a_k-1$. If both choices occur infinitely often, this digit sequence has arbitrarily long constant blocks and infinitely many changes, which excludes eventual periodicity and proves the filler irrational. Distinct shell sequences give distinct values because the contribution at the first differing shell already strictly exceeds the total possible difference after that shell, even for $b=2$. There are consequently continuum many values modulo rational translation. The coefficients at different sites of a single shell are tied together. Their exact regrouping supplies the deterministic proof. The independently sampled individual sites and the bounded-continued-fraction samples of §3 have different proofs.

**Open.** Can one compute an $x$ with bounded partial quotients such that every nonconstant $P\in\mathbb Q[X]$ has $P(x)$ absolutely normal? Section 3 gives metric existence under a fixed cap. Its effective selection uses $A_i\to\infty$ for the subexponential bound on $L_m$.

**Open.** Estimate (11) for (10) does not attain a factor $(\log q)^{o(1)}$ in the denominator, nor bounded partial quotients. A specific computable sparse CRT example attaining either bound remains a separate problem.

## Verification and scope

Run `python -B scripts/phase24_nonlinear_approx.py` to reproduce the following checks with integer and rational arithmetic.

* **Finite measurement (certified).** For $b=2,p=3,s=1$, each of the square and cube enclosures fixes the first 8192 binary digits. Each prefix contains all 256 eight-bit words. For each power and each $Q\in\{1,2,3,5,7\}$, each of the four successive blocks of 20 shifts from $m=1$ through $80$ contains a window whose distance from an integer exceeds $1/5$ even after allowing for the omitted tail. These finite witnesses give no lower bound on the limsup. The verifier also checks the distance in the $1/5$ two-cycle.
* **Finite certificate.** For each power the closest fraction of denominator at most $2^{1024}$ to the enclosure midpoint lies farther away than its half-width, excluding all such rationals. The 529 gap-prefix tests check denominators, the residue lattice and tail bounds, and the one- or two-word prediction when its inequality applies. The script also enumerates the cubic residues modulo 9 and checks the rational margin in the DEKKM threshold using the analytic input $\log 2>2/3$.
* Six ordered-convolution fixtures check prefix numerators, innovation depths at selected arrivals, and the low-residue recurrence. The verifier includes every eligible $j$ in the exact window, which can extend beyond the conservative $J$. Four fixtures cover a full unit period and check its histogram. The square $(d,p,s,B,a,h)=(2,3,2,4,4,3)$ covers three of six units. The flagship cube $(3,3,1,4,3,2)$ has no selected arrivals. A separate exact triple count for that cube at $a=6,h=2,j=1$ checks the selected coefficient’s depth $2a-1=11$. The scaled-grid tests check all residues and multiplicities for 54 complete unions of translated grids.
* The continued-fraction checks cover 4608 denominator intervals and seven exact reciprocal folds. The growing-cap checks verify retained lengths, cylinder mass and diameter bounds, total mass, a two-interval cover, and both endpoints of every allowed child of the 648 depth-seven cylinders. The verifier also tests the word-frequency split by parity on all 4096 binary strings of length 12.
* Synthetic digits test the prime-product denominator and coefficient bounds at 120 individual-site prefixes. A separate rational translation checks the digit truncation for a finite prime sum. The shell checks cover 124 determinant folding inequalities and 192 shell sequences across three radices, including regrouping, depth and unit congruences, denominator heights when the size bound applies, and distinctness within each radix. At a shared shell endpoint the filler sum is tested before the next sparse coefficient is added.

The asymptotic results use the proofs and cited inputs above. Cross-model review is not independent human peer review.
