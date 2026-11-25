# Binary normality with every odd denominator prime

Let $s_3=2$ and $s_\ell=1$ for every prime $\ell>3$. The number

$$
 Y=\sum_{\ell\ {\rm odd\ prime}}\sum_{j\ge1}
       \frac{2^{-16^{\ell^j}}}{\ell^{s_\ell j}}
$$

is binary normal and Liouville. For **every** prefix of length $N\ge2$, its extreme interval discrepancy satisfies $D_N(Y;2)\ll 1/\log(2N)$. At shift $n\ge1$, put $L=\lfloor\log_{16}n\rfloor$. Its reduced rational prefix has every odd denominator prime up to $L$. Its largest equally spaced ternary grid has size $G(L)>L/9$ for $L\ge3$, and $\limsup G(L)/L=\infty$. A subgrid of size comparable to $L$ is always available.

The series, rates and growth statements below have paper proofs. Three finite arithmetic lemmas have Lean proofs. The exact computations at the end examine individual moduli and prefixes. [Lean statements](../../NormalityChecker/SurvivingGrid.lean) · [Exact controls](../../scripts/phase19_grids.py)

## 1. The largest grid at one prime

Write $T_b(x)=bx\bmod 1$. For $N>0$, $D_N$ is the supremum over half-open circle arcs $I$ of the absolute difference between the observed frequency in $I$ and its length $|I|$. This equals extreme discrepancy over ordinary intervals by complementation. Throughout, $b\ge2$, $\operatorname{ord}_m b$ is the multiplicative order for $(m,b)=1$, and $\operatorname{ord}_1 b=1$. All logarithms without a subscript are natural.

**Exact grid theorem.** Suppose $q=p^eQ$, $e\ge1$, $p$ an odd prime, $(p,Q)=1$ and $(b,q)=1$. For every unit numerator $A$ define

$$
 d=\operatorname{ord}_p b,\quad t=\operatorname{lcm}(d,\operatorname{ord}_Q b),
 \quad w=v_p(b^t-1),\quad G=p^{\max(0,e-w)}.
$$

The full period $P=\operatorname{ord}_q b$ is $tG$. The exponents in each class $i\bmod t$ visit exactly the residues

$$
 \{x\bmod q:x\equiv Ab^i\bmod (q/G)\}.
$$

After division by $q$, each class is an equally spaced grid of $G$ points. Every full period has discrepancy at most $1/G$, uniformly in $A$ and $Q$. Among all equally spaced subsets of the orbit whose size is a power of $p$, the largest size is exactly $G$.

**Proof.** Set $g=b^t$. It fixes $Q$ and is one modulo $p$. For positive $k$, odd-prime lifting gives $v_p(g^k-1)=w+v_p(k)$. One elementary proof expands $(1+u)^p-1$ for $v_p(u)\ge1$. The first term has valuation $1+v_p(u)$ and all the others have larger valuation, since $p$ is odd. Raising to an exponent coprime to $p$ preserves $v_p(u)$ by the same expansion. Hence $g^k\equiv1\bmod q$ precisely when $G\mid k$. Any return of $b$ fixes both $p$ and $Q$, so its exponent is a multiple of $t$. This proves the period formula, including $G=1$.

The powers of $g$ all equal one modulo $p^{\min(e,w)}Q=q/G$. There are exactly $G$ lifts of one to modulus $q$, and the first $G$ powers are distinct. Translation to any starting unit by multiplication gives all lifts of its residue. The $t$ grids are disjoint since equality modulo $pQ$ forces the exponents to agree modulo $t$. A grid of $G$ points has either $\lfloor G|I|\rfloor$ or $\lceil G|I|\rceil$ points in $I$, giving the discrepancy estimate.

For maximality, a grid of size $p^h$ drawn from residues divided by $q$ requires $p^h\mid q$. If $h=e$, its lifts modulo $Q$ include a nonunit at $p$. Otherwise all its elements agree modulo $pQ$, so they lie in a single one of the $t$ classes. This also proves maximality for grids whose first point is an arbitrary translate. The condition $e-w\to+\infty$ is necessary and sufficient for these $p$-grids to grow. For example, at $q=3\cdot5^k$, the binary $3$-grid always has size one, but the $5$-grid grows and full periods become uniform. [Return times, order and exhaustion of a residue class](../../NormalityChecker/SurvivingGrid.lean)

**Computing the loss.** Put $a=v_p(b^d-1)$. Since $d\mid p-1$, lifting from $d$ gives

$$
 w=a+v_p(\operatorname{ord}_Q b)
   =a+\max_{\ell\mid Q}v_p(\operatorname{ord}_\ell b)
   \le a+\max_{\ell\mid Q} v_p(\ell-1).
$$

An empty maximum is zero. Indeed the order modulo $\ell^f$ is a multiple of the order modulo $\ell$ and divides $\ell^{f-1}\operatorname{ord}_\ell b$, by reduction of units modulo $\ell$. Since $\ell\ne p$, the $p$-valuation is unchanged. CRT takes the lcm of the local orders. This includes $\ell=2$ for odd radices. Congruence $\ell\equiv1\bmod p^k$ alone supplies no lower bound of $k$ on the order valuation. For example, $31\equiv1\bmod3$ and $\operatorname{ord}_{31}2=5$.

**Combining primes.** For an arbitrary divisor $h\mid q$, the orbit contains an equally spaced $h$-grid if and only if $P=h\,\operatorname{ord}_{q/h} b$. Reduction modulo $q/h$ has equally sized orbit fibers of size $P/\operatorname{ord}_{q/h} b$, each contained in the $h$ available lifts. Equality fills every such fiber. Consequently, the possible grid sizes are precisely the divisors of a single largest size. Indeed an $h$-grid occurs exactly when addition of $q/h$ preserves the entire orbit as a residue set. Its translation stabilizer is a subgroup of the cyclic additive group modulo $q$. For odd $q$ the largest size is therefore the product of the exact $G_p$ above over $p\mid q$, each computed with its own complement. For even $q$ the order-ratio test remains valid. Substituting $p=2$ in the odd-prime lifting formula would fail already at $b=3$, $q=8$, where the orbit $\{1,3\}$ has no two-point equally spaced subset.

## 2. Counting every prefix

Consider a convergent expansion $x=\sum_{m\in\mathcal A}c_m b^{-m}$ at distinct positive integer positions with $|c_m|\le B$. Combine coincident coefficients before applying this hypothesis. At shift $n$ its rational prefix is $R_n=\sum_{m\le n}c_m b^{n-m}$. On a run of shifts with no new insertion, these models follow consecutive iterates of the starting rational point. Assume its reduced denominator is coprime to $b$.

**Prefix estimate.** From $[0,N)$ discard an initial segment or other unwanted positions of total size $E$. Partition the rest into consecutive runs with lengths $h_i$, reduced periods $P_i$ and full-period discrepancy bounds $1/G_i$ from Section 1. A trivial bound $G_i=1$ is always allowed. For integer $H\ge1$ let $B_H$ count retained shifts with an insertion in $(n,n+H]$. Then

$$
 D_N(x;b)\le \frac{E+B_H}{N}+\frac{2B b^{-H}}{b-1}
       +\frac1N\sum_i\left(\frac{h_i}{G_i}
          +\min\{r_i,(1+1/G_i)(P_i-r_i)\}\right),
 \qquad r_i=h_i\bmod P_i .
$$

For a fixed arc, count the complete periods and bound the residual count error by $r_i$. Alternatively complete the run to the next period and subtract its missing suffix, which costs at most $P_i-r_i$ plus the mesh allowance $(P_i-r_i)/G_i$. Both bounds hold for arbitrary starting phases. On each shift outside the buffer,
$|b^nx-R_n|\le B\sum_{j>H}b^{-j}=B b^{-H}/(b-1)$. Expand the tested arc, bounding saturation by the whole circle, then use its complement for the reverse inequality. All runs can be counted before discarding bad pairs. The last, possibly partial, run is included. This proves the estimate.

In particular, a rate $O(1/U(N))$ follows if the three count budgets $E+B_H$, $\sum_i h_i/G_i$, and the sum of the remainder costs are $O(N/U(N))$, and $B b^{-H}=O(1/U(N))$ for fixed $b$. One can use $H=\lceil\log_b U(N)\rceil$ for $U(N)\ge b$. With $J$ runs, charging each residual at its period gives the simpler worst-case allowance $J\max_iP_i=O(N/U(N))$. For example, $O(N^\theta)$ insertions through $2N$ and periods $O(N^\sigma)$ cost $O(N^{\theta+\sigma-1})$ in normalized fragments. A growing polynomial target also costs $O(N^{\theta-1}\log N)$ for buffers. The exact sum permits unequal periods, very short exceptional runs and runs ending on a period boundary. If every finished run has length divisible by its own period, the only period cost comes from the current run. Thus there is no universal fastest pointwise growth for a period or a support size inferred from this argument. The finite sum gives the actual budget of the complete-period proof. A fragment estimate can improve it further.

## 3. The binary series

At an insertion indexed by $\ell^j$ the new coefficient has strictly deeper $\ell$-pole than all earlier terms on that axis. The multiplier $2^{n-16^{\ell^j}}$ is always an $\ell$-unit. Other axes are integral at $\ell$. Thus with $J_\ell=\lfloor\log_\ell L\rfloor$ its reduced prefix denominator is exactly

$$
 q(L)=3^{J_3}\prod_{3\le\ell\le L,\ \ell\ {\rm prime}}\ell^{J_\ell},\qquad
 e=2J_3 .
$$

Here and below a missing axis has depth zero. Write $J=J_3$ and $M(L)=\max_{3<\ell\le L}v_3(\operatorname{ord}_\ell2)$ over primes. Since $d=2$, $a=1$, and $\ell-1<L$, the exact size for $L\ge3$ is

$$
 G(L)=3^{\max(0,2J-1-M(L))},\qquad M(L)\le J,\qquad
 G(L)\ge 3^{J-1}>L/9 .
$$

Subsampling each exact grid with stride $G/3^{J-1}$ gives grids of size $3^{J-1}\asymp L$.

For the period bound put $\psi(L)=\sum_{\ell^j\le L}\log\ell$ over all prime powers with $j\ge1$. Then $\log q=\psi(L)-J_2\log2+J_3\log3=L+o(L)$ by the prime number theorem. The number of insertions with label at most $L$ is $\pi(L)+O(\sqrt L\log L)\sim L/\log L$, since there are at most $\sqrt L$ possible bases and $O(\log L)$ exponents for higher powers. Even the bound $L$ suffices. [Hadamard's prime number theorem](https://www.numdam.org/articles/10.24033/bsmf.545/)

Discard $n<\lceil\sqrt N\rceil$. At all remaining shifts $L\asymp\log N$, so the normalized mesh cost is $O(1/\log N)$. With $H=\lceil\log_2 N\rceil$, at most $O((\log N)^2)$ shifts lie before nearby insertions (count insertions through $N+H$). Each coefficient is at most one and distinct prime powers give distinct positions. Every residual period, including the final one, costs at most $q(L)\le N^{1/\log16+o(1)}$. Their sum is $N^{1/\log16+o(1)}=o(N/\log N)$. Section 2 proves the claimed all-prefix bound. Uniform distribution of $T_2^nY$ is equivalent to binary normality by the binary cylinder intervals. No fixed-support orbit theorem or estimates uniform in the number of primes are needed beyond Section 1.

**Liouville property.** For arbitrarily large $h$, impose two distinct prime divisors on each of $z+1,\ldots,z+h$ using pairwise distinct primes and CRT. Solutions $z$ are arbitrarily large. Hence there are consecutive odd-prime-power labels $u<v$ with $v-u$ unbounded. The positive truncation at $n=16^u$ has unshifted denominator at most $2^n q(u)$ and the error is at most $2^{1-16^v}$. Now $\log_2 q(u)=O(u)=o(n)$ and $16^v/n=16^{v-u}$ is unbounded. This yields arbitrarily high rational approximation exponents, and normality already gives irrationality.

## 4. Why the exact size has no linear upper bound

From the exact formula, $G(L)=O(L)$ would be equivalent to $M(L)\ge \lfloor\log_3L\rfloor-O(1)$ for **every** large $L$. This would require a prime $\ell\le L$ at which the actual binary order is divisible by $3^{\lfloor\log_3L\rfloor-O(1)}$. Even the weaker requisite prime congruence fails at infinitely many scales.

**Missing-prime lemma.** For any prime $p$ and fixed integer $C\ge1$, there is an arithmetic progression of arbitrarily large exponents $k$ for which every $mp^k+1$, $1\le m\le C$, is composite.

Choose $h$ with $p^h>C$. Each $p^h+m$ has a prime factor $r_m\ne p$, since after removing $p^{v_p(m)}$ the remaining integer is greater than one and prime to $p$. Choose $k\equiv-h$ modulo $\operatorname{lcm}_{m\le C}\operatorname{ord}_{r_m}p$. Then $mp^k+1\equiv0\bmod r_m$ for every $m$. For all sufficiently large such $k$ these divisors are proper.

Apply the lemma with $p=3$, $C=3^j$, and $L=3^{k+j}$. No prime up to $L$ is one modulo $3^k$, so $M(L)\le k-1$. It follows that $G(L)/L\ge 3^j$. Taking arbitrarily large $j$ proves the asserted infinite limsup. For perspective, $M(L)$ itself does grow. For $k\ge1$, every prime divisor of $(2^{3^k}-1)/(2^{3^{k-1}}-1)$ has order $3^k$. Indeed this quotient is $x^2+x+1$, $x=2^{3^{k-1}}$, equals one modulo 3, and is coprime to $x-1$ since their gcd divides 3. Choosing $3^k\le\log_2 L$ puts such a prime below $L$. This yields $G(L)\ll L^2/\log L$. It does not supply the lower order valuation needed for a linear upper bound.

The [Phase 18 review](../phase18/reviews/translation-summation.md#scope-of-the-grid-theorem-accurate-worth-stating) inferred loss of the prime-5 grid from primes congruent to one modulo high powers of 5. Its Dirichlet argument alone does not control their binary orders. Even unbounded valuations would have to be compared with the increasing depth. On that restricted support the prime-5 depth is $\lfloor\log_5 L\rfloor$. The missing-prime lemma with $p=5$, $L=5^{k+j}$ bounds the complementary loss by $k-1$ and gives arbitrarily large prime-5 grids along a subsequence. The original Phase 18 uniform estimate from the distinguished prime 3 stands. [Original construction](../phase18/summation.md#a-normal-positive-sum-on-infinitely-many-denominator-primes)

## 5. Radices, selectable depths and faster insertions

Fix any integer radix $b\ge2$, any odd prime $p\nmid b$, and any set of primes $\mathcal S$ disjoint from the divisors of $b$ and containing $p$. Choose at each $\ell$ strictly increasing positive integer depths $E_\ell(j)$, $j\ge1$, and set $E_\ell(0)=0$. Let $F$ be a strictly increasing integer-valued schedule on positive integer labels. Insert $\ell^{-E_\ell(j)}$ at position $F(\ell^j)$. Write $L=\max\{u:F(u)\le n\}$, with $L=0$ initially. Distinct labels cannot coincide. After the first distinguished insertion, the unique deepest term on each axis gives

$$
 q(L)=\prod_{\ell\in\mathcal S,\ \ell\le L}\ell^{E_\ell(J_\ell)},\qquad
 G(L)=p^{\max(0,E_p(J_p)-a-M_b(L))},
 \quad M_b(L)=\max_{\substack{\ell\in\mathcal S,\ \ell\le L\\ \ell\ne p}}
             v_p(\operatorname{ord}_\ell b).
$$

The depths on the complementary axes have no effect on $M_b$ after their first insertions. They can increase the period and hence the fragment cost. For a target $U(L)>1$, the exact condition for $G(L)\ge U(L)$ is $E_p(J_p)\ge a+M_b(L)+\lceil\log_p U(L)\rceil$. For nondecreasing $U$ the worst requirement during a distinguished layer $J_p=j$ is at $L=p^{j+1}-1$. The formula specifies the necessary depth within this construction, subject also to strict increase across layers. One may conservatively replace $M_b(L)$ by $J_p$, since $\ell-1<L$. With $E_p(j)=s j$, integer $s\ge2$, this gives $G(L)\gg_{b,p,s}L^{s-1}$ uniformly over all choices of the other primes and depths.

For instance, if $E_\ell(j)\le S j$ on the complement for a fixed real $S\ge1$, then $\log q(L)\le S\psi(L)+O_{p,s}(\log L)$. Taking $F(u)=u+\lceil\exp(cu)\rceil$ for $c>S$ gives

$$
 D_N(x;b)\ll_{b,p,s,S,c}(\log(2N))^{1-s}.
$$

The proof is Section 3 with $P\le q\le N^{S/c+o(1)}$, $L\asymp\log N$ on $[\sqrt N,N)$, and at most $O(\log N)$ runs. All off-radix primes, including 2 when $b$ is odd, can participate.

**A schedule using the actual periods.** Given any such profile with $G(L)\gg L^\beta$, $\beta>0$, calculate $P(u)=\operatorname{ord}_{q(u)}b$ from the profile before specifying positions. The reduced denominator is independent of those positions. The periods are nondecreasing under divisibility. For an integer $K>\beta+1$ put $F(u)=u^K P(u)$. Then $D_N\ll L(N)^{-\beta}$ for the inverse cutoff $L(N)$ of $F$. Indeed, $N\ge L^KP(L)$ charges all residuals by $(L+1)P(L)$. Use $H=\lceil\log_b(2L^\beta)\rceil$. At most $L+H+1$ insertions occur through $N+H$, since beyond $N$ the positions are distinct. This controls the buffer. For the mesh term put the labels in dyadic ranges $v\le L(n)<2v$, using $v$ a power of two. In a range with $2v\le L$, the number of shifts is at most $F(2v)\le N(2v/L)^K$. The mesh cost there is $O(Nv^{-\beta}(2v/L)^K)$. Sum the geometric progression and bound the final range by $O(NL^{-\beta})$. Initial shifts cost a constant. This works even for sudden, arbitrarily large increases in complementary depths.

**Superpolynomial denominators on a fixed schedule.** There is a faster concrete choice when the complement has ordinary depths $E_\ell(j)=j$. For any fixed $0<\alpha<1$ use

$$
 F(u)=u+\left\lceil\exp\!\left(\frac{u}{(\log(2+u))^\alpha}\right)\right\rceil,
 \qquad E_p(j)=sj,\quad s\ge2 .
$$

For every $\mathcal S$ as above this gives

$$
 D_N(x;b)\ll_{b,p,s,\alpha}
    \big(\log N\,(\log\log N)^\alpha\big)^{1-s}\qquad(N\ge 3).
$$

For the full off-radix support, $\log q(L)=L+o(L)$. Thus $q$ exceeds every fixed power of the observation time, even though the periods are $N^{o(1)}$.

Here is the period estimate. All local orders divide $\ell^{E_\ell(J_\ell)-1}(\ell-1)$ at present primes. The factors $\ell^{J_\ell-1}$ contribute $O(\sqrt L\log L)$ to the log of their product, since only $\ell\le\sqrt L$ occur. The fixed distinguished prime adds $O_{p,s}(\log L)$. It remains to bound $A(L)=\operatorname{lcm}_{\ell\le L,\ \ell\ {\rm prime}}(\ell-1)$. Prime powers of exponent at least two contribute $O(\sqrt L\log L)$ to $\log A$. First powers $r\le L/\log L$ contribute $O(L/\log L)$ by the prime number theorem. Every larger prime $r\mid A$ occurs in a pair with $mr+1$ prime, where $1\le m<\log L$.

On $x<r\le2x$ the upper-bound sieve of Ford, Luca and Pomerance, Lemma 5.1 with $h=k=1$, gives

$$
 \#\{r:x<r\le2x,\ r,\ mr+1\ {\rm prime}\}
 \ll \frac{x\log\log(3m)}{(\log x)^2}.
$$

Indeed every prime $r>x$ passes their least-prime-factor restriction for $y=x^{1/12}$. Dyadically summing from $L/\log L$ to $L/m$, all logarithms $\log x$ are comparable to $\log L$. Multiplying by $\log L$ and summing $1/m$ up to $\log L$ yields, for sufficiently large $L$,

$$
 \log P(L)\ll_{p,s}
 \frac{L\log\log L\,\log\log\log L}{\log L}.
$$

This is $o(\log F(L))$ for each $\alpha<1$. Inverting $F$ gives $L(n)\sim\log n\,(\log\log n)^\alpha$, as one sees by substitution and monotonicity. Thus $L(n)\asymp L(N)$ on $[\sqrt N,N)$, there are $O(L(N))$ runs, and the sum of their residual periods is $N^{o(1)}$. The buffer and mesh estimates of Section 2 prove the claim. This sieve input is only used for the faster schedule. [Ford, Luca and Pomerance, Lemma 5.1](https://msp.org/ant/2014/8-8/ant-v8-n8-p08-s.pdf)

**How large can the denominator itself be?** For a grid of exact size $G$ and full period $P=tG$, one always has

$$
 q/G=p^{\min(e,w)}Q\mid b^t-1,\qquad q\le G(b^{P/G}-1).
$$

There are full-support constructions attaining this arithmetic upper bound. Take $t_j=d\,j!$, $G_j=p^j$ and $q_j=(b^{t_j}-1)G_j$. Put $w_j=v_p(b^{t_j}-1)=a+v_p(t_j)$ and $Q_j=(b^{t_j}-1)/p^{w_j}$. Since $p^{w_j}\le p^a t_j$, eventually $Q_j>b^{t_j/2}-1$. Its order divides $t_j$ and cannot be a proper divisor, since every proper divisor is at most $t_j/2$. Thus the exact stride, grid and period at $q_j$ are $t_j,G_j,P_j=t_jG_j$. Every prime off the radix eventually divides every $q_j$, since its order divides $t_j$ eventually.

These are denominators of an actual normal number. Insert at $n_j=j^3P_j$ a coefficient in $(0,1]$ congruent to $1/q_j-b^{n_j-n_{j-1}}/q_{j-1}\bmod 1$, starting with previous residue zero. Induction gives reduced shifted residue $1/q_j$ on arrival. For $n_j\le N<n_{j+1}$ there are at most $j+1$ runs and each period is at most $P_j$, apart from harmless initial terms. Their normalized period cost is $O(j^{-2})$. With $H=\lceil\log_b(j+2)\rceil$ the normalized buffer cost tends to zero, and the mean mesh tends to zero by first discarding finitely many early runs. The sum is base-$b$ normal. Along these arrivals $\log q_j\asymp t_j=n_j^{1-o(1)}$. More generally, for any prescribed $V(n)\to\infty$, one can successively take $t_j$ sufficiently large multiples of $d\,j!$ and $t_{j-1}$ that $V(n_j)\ge 2j^3G_j/\log b$. Then $\log q_j\ge n_j/V(n_j)$ eventually, with the same proof. This concerns growth at selected arrivals. The aggregate error in Section 2 still has to hold through every prefix.

## 6. Counterexamples and classical obstructions

- **Deep poles can lose the whole grid.** At $b=2,p=3$, use as complement a prime factor of $(2^{3^k}-1)/(2^{3^{k-1}}-1)$ from Section 4. Take $e=k+1$. Then $w=1+k$ and $G=1$ although $e\to\infty$. A numerator divisible by a denominator prime must also be reduced before applying the theorem.
- **A fine grid alone permits a rational sum.** Fix $p\nmid b$ odd and $n_j=2^j$ for $j\ge1$. Choose strictly increasing depths $e_j$ with $p^{e_j}>b^{n_{j+1}-n_j}$. Insert $1-p^{-e_1}$ at $n_1$, then $b^{n_j-n_{j-1}}p^{-e_{j-1}}-p^{-e_j}$ at $n_j$ for $j\ge2$. These coefficients are positive and at most one. The truncation after $j$ equals $b^{-n_1}-b^{-n_j}p^{-e_j}$ by telescoping. The sum is the terminating rational $b^{-n_1}$ and its discrepancy tends to one. Yet every late shifted prefix has denominator $p^{e_j}$ on its run and grid size $p^{e_j-a}\to\infty$. The model follows only an uncontrolled fragment of its period. This example even has sparse insertions and a bounded positive tail.
- **The raw logarithm has different scales.** In $\log 2=\sum_{m\ge1}2^{-m}/m$, every shift begins a new run. The mesh and period information of the last complete rational model would have to control single observations. The Taylor coefficients supply no doubled distinguished depth or compensating estimate for these starting numerators. Phase 18 also proves that the odd denominator at the original cutoffs has logarithm $n+o(n)$ even when completed dyadic groups are removed. Although the ordinary shifted Taylor tail is $O(1/n)$, tail accuracy alone cannot turn the run of length one into a complete period. [Phase 18 prime-delay result](../phase18/prime-delay.md)
- **Other classical expansions.** In the BBP formula for $\pi$, each hexadecimal index brings four signed fractions, and the positive-measure coverage by uniform reduced orbits of their combined prefixes remains unproved. The factorial expansion of $e$ gives fast rational approximation but supplies no family of long controlled radix-orbit fragments by this test. In the binary Lambert expansion $\sum_{m\ge1}\tau(m)2^{-m}$ of the Erdős–Borwein number, every raw shifted prefix is integral, so its grid size is one. None of these observations decides the normality of the classical constants. [BBP, formula (1.2)](https://doi.org/10.1090/S0025-5718-97-00856-9) · [Phase 18 classical synthesis](../phase18/classical.md)

## 7. Verification and historical scope

The Lean module proves the odd-prime return-time divisibility equivalence for a given stride, the resulting multiplicative order modulo $p^eQ$, and exhaustion of all lifts when the order equals their number. The orbit counting, real-tail argument, normality and Liouville assertions, sieve application and missing-prime lemma are paper deductions. With the module imported in a disposable overlay of the Phase 18 checkpoint, the full Lake build completed with 8,748 jobs and the axiom audit accepted all 1,596 declarations. All three new lemmas used only the project's permitted axioms. [Lean module](../../NormalityChecker/SurvivingGrid.lean)

The Python checker compares every claimed coset with its arithmetic progression in 240 full-orbit cases, including $Q=1$, $e\le w$, odd radices, and lifting depth $a>1$. On modulus $675=3^3\cdot5^2$ it independently finds a largest binary-orbit grid of 45 points. It verifies 325 actual insertion denominators across three radix/prime pairs through label 512, by updating the shifted fraction and testing its numerator for coprimality. It certifies $D_N(Y;2)<1/8$ for the four prefixes $N=16^{11}-1,16^{11},16^{11}+1,16^{11}+37$ using rational upper bounds on the infinite series. For the missing-prime lemma it checks certificates for $C=3,9,27$. For instance $k=417+420j$ excludes every prime $m3^k+1$ with $1\le m\le9$. [Reproducible controls](../../scripts/phase19_grids.py)

The local calculation uses classical CRT, order lifting, and exact counts on a finite grid. Korobov studied the digits of rational fractions over full and partial periods. Kano's Theorem 1 treats sparse normal expansions with powers of a fixed denominator base. Vandehey's Theorem 7.4 permits a fixed finite set of denominator primes. These theorems have different hypotheses from a reduced prefix acquiring every off-radix prime. The prior repository construction used the distinguished prime 3 and complementary primes $2\bmod 3$. The extension here permits complementary orders divisible by increasing powers of the distinguished prime, quantifies the exact loss, and enforces the required mesh for the explicit all-prime series. The historical comparison establishes the scope of those sources. Priority for normal constructions with varying moduli in general is unassessed. [Korobov, 1972](https://doi.org/10.1070/SM1972v018n04ABEH001870) · [Kano, Theorem 1](https://ir.library.osaka-u.ac.jp/repo/ouka/all/10356/ojm30_04_15.pdf) · [Vandehey, Theorem 7.4](https://arxiv.org/pdf/1606.07911) · [Phase 18 construction](../phase18/summation.md#a-normal-positive-sum-on-infinitely-many-denominator-primes)

The complementary order on genuine Taylor prefixes has a different scale: the many surviving prime divisors in a macroscopic interval force an order growing faster than every polynomial in the cutoff. [Taylor period lower bound](taylor-periods.md)

The finite interval bound for a full stride period with arbitrary admissible complement is also [kernel-verified](../../NormalityChecker/PrimePowerGrid.lean). The construction, all-prefix assembly and transcendence tests for the infinite sum remain written deductions.
