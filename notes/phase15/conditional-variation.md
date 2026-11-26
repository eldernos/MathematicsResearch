# Conditional variation, moving primes and inverse estimates for the binary digits of ln 2

This note continues Tracks E and F of [Phase 14](../phase14/README.md). Its conventions are those of [transition windows](../phase14/transition-windows.md). Write $b_n$ for the first bit of $\{2^n\ln 2\}$ and $\tau_t=1$ when $b_t\ne b_{t+1}$, that is, when $\{2^t\ln2\}\in[1/4,3/4)$. A dyadic shell is $[N,2N)$ with $N=2^k$. For $2\le T\le N$ put $m=T-1$, and let $C(n,T)$ count the transitions internal to the word $b_n,\ldots,b_{n+T-1}$. Write $e(t)=\exp(2\pi i t)$ and define the shell Weyl mean
```math
W_k=\frac1N\sum_{N\le n<2N}e(2^n\ln 2).
```

**Summary.** There are five results.

1. **Exact position weights.** These turn the Phase 14 cell count into words with a loss that is linear, not quadratic, in the mark density. If a quarter of the shell offsets are marked and $T=o(N)$, then about $N/7$ starts carry at least $m/8$ changes. Phase 14 obtained $N/128$ starts with $T/128$ changes.
2. **The lift model.** The mesh error of the Phase 14 lift model is relative, not additive. A counting argument shows that lifts preserving the upper band lose their only equidistribution input for word lengths beyond $T\approx(1/\log 2-1)N\approx0.4427N$.
3. **Rigidity.** The eventual upper-band residues, exact displacements and denominators determine ln 2 up to an additive **rational**, and every rational occurs. Positive lower transition density is not invariant under rational translation. An argument using only these data must therefore exclude asymptotic shadowing of every rational periodic orbit.
4. **Moving primes.** Classical and Bourgain–Chang estimates control a bounded number of moving upper-band primes. Any estimate that is uniform in the numerator fails once the product of the primes exceeds $2^{T+1}$, about $T/\log_2 N$ primes.
5. **Inverse statement.** A shell with few transitions forces the upper-band character to be the conjugate of the complementary character in mean square. Within a shell the deficit and transition proportion bound one another up to constants and an endpoint error. A uniform deficit on all late shells suffices for positive ordinary lower density. It has a logarithmic-density version that requires good shells only on a set of positive density.

The positive lower density of transitions of ln 2 remains open. The scope of each statement is marked: **Lean** (existing kernel proof), **paper** (proof given here), **exact** (integer or rational computation in the script), **float** (orientation only), **source** (external theorem, hypotheses as read).

Run `python3 -B scripts/phase15_variation.py` (shells through $2^{14}$) or add `--full` for true-bit shells through $2^{16}$ (about 90 seconds). [Script](../../scripts/phase15_variation.py)

## 1. The Fourier deficit controls transitions on each shell (Lean, specialized)

The Lean lemma `escape_step` proves, for every real $x$ and position $n$, with $F_n=1-\cos(2\pi2^nx)$,
```math
\tau_n\le F_n\le 4\tau_n+F_{n+1}-F_n .
```
Summing over one shell telescopes the right side. The shell count $\sum_{N\le n<2N}\tau_n$ therefore satisfies
```math
\frac{1-\operatorname{Re}W_k}{4}-\frac1{2N}\ \le\ \frac1N\sum_{N\le n<2N}\tau_n\ \le\ 1-\operatorname{Re}W_k .
```
The prefix form, together with its equivalence with strict limiting discrepancy, is `escapeAverage_transition_bounds` and `logTwo_discrepancy_lt_one_iff_escape`. The shell form is the same inequality summed over a different range. [FirstFrequency.lean](../../NormalityChecker/FirstFrequency.lean)

**Ordinary density (paper).** Suppose $\operatorname{Re}W_k\le1-c$ for all large $k$. Each completed shell then contributes at least $(c/4)2^k-1/2$ transitions. For $2^k\le M<2^{k+1}$ the earlier shells give at least $(c/4)2^k-O(k)$ transitions before $M$, so the lower transition density is at least $c/8$. Conversely, positive lower density forces $\limsup$ of the prefix mean of $\operatorname{Re}\,e(2^n\ln2)$ below one by the right inequality.

**Logarithmic density (paper).** Each position in shell $k$ has weight $1/n\ge2^{-k-1}$, and $\log 2^{K+1}=(K+1)\log2$. Write $\tau(k)$ for the shell proportion. The lower logarithmic transition density is therefore at least
```math
\frac{1}{2\log 2}\liminf_{K\to\infty}\frac1K\sum_{k<K}\tau(k)
\ \ge\ \frac{1}{8\log 2}\liminf_{K\to\infty}\frac1K\sum_{k<K}\bigl(1-\operatorname{Re}W_k\bigr).
```
Thus the logarithmic target needs $\operatorname{Re}W_k\le1-c$ only on a set of shell indices of positive lower density. A single good shell per bounded block of indices suffices. For ordinary lower density a bounded gap between such shells suffices, with a loss depending on that gap. The Phase 14 construction with alternating bits on $[A_j,3A_j)$, $A_{j+1}=A_j^3$, has upper density positive and lower density zero. Alternating bits on every shell except gap blocks of $j$ consecutive shells starting at $k=j^3$ have positive lower logarithmic density and zero lower ordinary density. Measured at the end of each gap, the earlier transitions are $o(M)$. [Phase 13 logarithmic versus ordinary density](../phase13/erdos-borwein.md)

**Interval certificate for the true shells (exact).** The script certifies the bits of ln 2 from an integer enclosure of $2\sum_k 1/(3(2k+1)9^k)$, independently of the Phase 14 enclosure, and checks agreement on 3,000 bits. The right inequality turns every exact shell count into a certified bound $\operatorname{Re}W_k\le1-\tau(k)$.

| Shell start | Transitions | Certified bound on Re *W* | Re *W* (float) | Least changes, *T* = √*N* | Least changes, *T* = *N* |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 141 | ≤ 0.4493 | −0.0506 | 4 | 130 |
| 1,024 | 520 | ≤ 0.4922 | −0.0253 | 10 | 519 |
| 4,096 | 2,100 | ≤ 0.4874 | −0.0127 | 21 | 1,967 |
| 16,384 | 8,209 | ≤ 0.4990 | 0.0018 | 43 | 8,040 |
| 32,768 | 16,407 | ≤ 0.4993 | 0.0004 | 63 | 16,229 |
| 65,536 | 32,605 | ≤ 0.5025 | 0.0026 | 98 | 32,592 |

All nine shells from $2^8$ to $2^{16}$ have between 0.488 and 0.551 of their positions as transitions. The smallest proportion is 4,001 out of 8,192 at $N=8{,}192$, where the certified bound is $\operatorname{Re}W_k\le0.5117$. The script also lists $2^9,2^{11},2^{13}$. These are finite facts and carry no asymptotic implication.

## 2. Exact position weights (paper; identity checked exactly)

**Identity.** For $2\le T\le N$ and every 0/1 sequence $\tau$,
```math
\sum_{N\le n<2N}C(n,T)=\sum_{j=0}^{N+m-2}w_j\,\tau_{N+j},\qquad
w_j=\min(j+1,\ m,\ N+m-1-j),\qquad \sum_j w_j=Nm .
```
Position $t=N+j$ is internal to the word at $n$ exactly when $\max(N,t-m+1)\le n\le\min(2N-1,t)$. Counting these $n$ gives $w_j$ in the three ranges $j<m$, $m-1\le j\le N-1$, $j\ge N-1$. The script verifies the identity for the true transitions and for the certified marks on every listed shell, at $T=\lfloor\sqrt N\rfloor$ and $T=N$.

**Linear transfer.** Suppose $H$ positions among offsets $0\le j<N$ are known transitions, for instance the Phase 14 marks. The weights on $[0,N)$ are nondecreasing, so placing the marks earliest minimizes the total:
```math
\sum_n C(n,T)\ \ge\ S(H,m)=\sum_{r=1}^{H}\min(r,m)=
\begin{cases} H(H+1)/2, & H\le m,\\ mH-m(m-1)/2, & H\ge m.\end{cases}
```
Fix $0<\theta<1$ and let $R$ be the number of starts with $C(n,T)\ge\theta m$. Since $C\le m$, the total is at most $Rm+(N-R)\theta m$, so
```math
R\ \ge\ \frac{S(H,m)/m-\theta N}{1-\theta}.
```
If $H\ge cN$ and $m\le cN$, this is at least $\bigl(c-\theta-m/(2N)\bigr)N/(1-\theta)$. For $T=o(N)$ the fraction of rich starts tends to $(c-\theta)/(1-\theta)$, linear in $c$. Phase 14 used $\min(r,m)\ge rm/N$ and obtained $c^2/8$. At $T=N$ the same identity gives $R\ge (c^2/2-\theta)N/(1-\theta)$. With $\theta=c^2/4$ this yields at least $c^2N/4$ starts with $c^2m/4$ changes, twice the Phase 14 constant at twice its threshold. The direct density bound $t(\ln2)\ge c/(2-c)$ of Phase 14 is unchanged. [Phase 14 incidence count](../phase14/transition-windows.md#a-joint-arithmetic-estimate-with-a-fixed-set-of-cells)

**Certified marks, worst-case transfer (exact).** Here $T=\lfloor\sqrt N\rfloor$. The last two columns are lower bounds for starts with at least $m/8$ and $m/4$ changes, from the worst-case minimum alone.

| *N* | Marks in [0,*N*) | *m* | Certified weighted incidence | Worst-case minimum *S* | Phase 14 (*N*/128 at *T*/128) | ≥ *m*/8 | ≥ *m*/4 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 79 | 15 | 1,181 | 1,080 | 2 | 46 | 11 |
| 1,024 | 335 | 31 | 10,467 | 9,920 | 8 | 220 | 86 |
| 4,096 | 1,287 | 63 | 81,088 | 79,128 | 32 | 851 | 310 |
| 16,384 | 5,110 | 127 | 649,084 | 640,969 | 128 | 3,428 | 1,268 |

## 3. The lift model: variance, Chernoff bound and the correct mesh error

Phase 14 fixed the actual upper-band residues $a$ and varied the complementary phase over the $M$-point grid $b/B+s/M$, where $M$ is the odd part of $L_N$. The four-bit cells $k_j$ of the complementary phase then use disjoint bits for offsets in a fixed class $j\bmod 4$. [Phase 14 conditional estimate](../phase14/transition-windows.md#what-simultaneous-upper-band-incidences-leave-undetermined)

**Mesh lemma (paper; checked exactly).** Let $G=\{\beta+s/M:0\le s<M\}$ modulo one, and let $E$ be a union of dyadic cylinders of level $K$. Then
```math
\left|\frac{\#(G\cap E)}{M}-\operatorname{Leb}(E)\right|\ \le\ \operatorname{Leb}(E)\,\frac{2^K}{M}.
```
Each cylinder of length $2^{-K}$ contains a number of grid points strictly between $M2^{-K}-1$ and $M2^{-K}+1$. There are $2^K\operatorname{Leb}(E)$ cylinders in $E$. At $K=N+3$, bounding $\operatorname{Leb}(E)$ by one recovers the Phase 14 absolute error bound. The Phase 14 argument is correct, and the relative form is never worse. The script enumerates all 177,147 points of a shifted grid against a one-bit refinement with $2^{14}$ cylinders for nine threshold events. The largest relative deviation is 0.0040, within the allowed 0.0925.

**Weighted second moment (paper).** Use the weights of Section 2 on all offsets $0\le j\le N+m-2$. These use complementary bits through $K=N+m+2$. Let $S=\sum_j w_jX_j$, where $X_j$ marks offset $j$. Under Lebesgue measure every $X_j$ is Bernoulli with mean exactly $5/16$ for each fixed upper cell. Marks whose offsets differ by at least 4 are independent. Hence
```math
\mathbb E S=\tfrac{5}{16}Nm,\qquad
\operatorname{Var}S\le\tfrac{55}{256}\sum_{|j-j'|\le3}w_jw_{j'}\le\tfrac{385}{256}\,m^2(N+m),
```
and Chebyshev gives a failure fraction $O(1/(\lambda^2N))$ for $S\le(5/16-\lambda)Nm$. Within each class mod 4 the marks are independent. Applying the exact Bernoulli Chernoff bound in each class gives exponential decay. If the total is at most a quarter of $Nm$, some class falls below a quarter of its own weight.

| *N* | *T* | Lebesgue bound for *S* ≤ *Nm*/4 | *K* | ⌊log₂ *M*⌋ | log₂ grid bound |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2,048 | 45 | 3.0·10⁻² | 2,094 | 2,933 | −5.0 |
| 4,096 | 64 | 2.3·10⁻⁴ | 4,161 | 5,912 | −12.1 |
| 8,192 | 90 | 1.4·10⁻⁸ | 8,283 | 11,783 | −26.1 |
| 16,384 | 128 | 5.1·10⁻¹⁷ | 16,513 | 23,658 | −54.1 |

The logarithms are floating evaluations of rigorous bounds. For $N=16{,}384$ and $T=128$ the analytic upper bound for failure of the threshold $Nm/4$ evaluates numerically to about $2^{-54.1}$. The quoted decimal is a floating-point evaluation. By Section 2 at least $N/7$ starts then have at least $m/8$ changes. No position loss occurs, because $S$ is itself the overlapping total. The statement concerns a measure on lifts and does not locate the actual lift $s=0$.

**A sharp limit for the model (paper).** The lifts that preserve **every** upper-band residue at the anchor form $B$ classes modulo one, where $B=L_{2N}/\prod_{N<p\le2N}p$. By the prime number theorem, $\log_2B=N/\log2+o(N)$. A family of $B$ phases cannot be equidistributed on cylinders of level $K$ once $2^K>B$: then at least $2^K-B$ cylinders are empty, and the total variation from uniform is at least $1-B/2^K$. Words of length $T$ from all shell starts read $K=N+T-1$ bits of the anchor phase. Relative approximation of every cylinder in this partition is therefore impossible for upper-band-preserving lifts once
```math
T\ >\ \Bigl(\frac{1}{\log 2}-1+o(1)\Bigr)N\approx0.4427\,N .
```
Below this threshold the $M$-grid and its multiplicative mesh give the bounds above. The Phase 14 variant for $T=N$ uses the odd part of $L_{2N}$ and necessarily changes some upper-band values. The weighted Lebesgue bound at $T=N$ is smaller, $1.5\cdot10^{-25}$ at $N=16{,}384$. Its mesh factor $2^{2N+1}/M$ is enormous, consistent with the threshold.

**Entropy budget (model calculation).** Take the uniform prior on numerators modulo $L$, so that $a$ and $b$ are independent and uniform. Fix $K<\log_2 M$ and put $\varepsilon=2^K/M$. Given any $a$, every $K$-bit window word has conditional probability in $2^{-K}(1\pm\varepsilon)$, by the mesh lemma applied to translated cylinders. The word has entropy at most $K$, and each conditional probability is at most $2^{-K}(1+\varepsilon)$. Its conditional entropy is therefore at least $K-\log_2(1+\varepsilon)$, giving mutual information at most $\log_2(1+\varepsilon)$. With $K=N+T+1$ and $T=\lfloor\sqrt N\rfloor$, the script gives less than $2^{-80}$ bits at $N=256$ and less than $2^{-7144}$ bits at $N=16{,}384$. An entropy-decrement argument in the style of Tao spends information carried by prime-indexed variables about the local block. In this model the prime-indexed variables carry essentially none. Given the upper band, the complementary residue determines the remaining randomness. This calculation for the uniform lift prior does not bound the mutual information of an actual prescribed logarithm orbit.

## 4. Rigidity of eventual upper-band data (paper; finite check)

Let $y_u$ be the diagonal model of [Phase 13](../phase13/corrected-numerators.md) and $\delta_u=y_{u+1}-2y_u$. Call a rational sequence $(y'_u)_{u\ge u_0}$ **data-equivalent** to $(y_u)$ if, for every $u\ge u_0$,

1. $L_{2u}\,y'_u\in\mathbb Z$;
2. $y'_{u+1}-2y'_u=\delta_u$;
3. $p\,y'_u\equiv p\,y_u\pmod p$ for every prime $u<p\le2u$.

**Theorem.** For an integer $u_0\ge1$, the data-equivalent sequences are exactly $y'_u=y_u+2^{u-u_0}q$ with $q\in L_{2u_0}^{-1}\mathbb Z$ and $v_p(q)\ge0$ for every prime $p>u_0$. Their real limits $\lim 2^{-u}y'_u$ are $\ln 2+2^{-u_0}q$. Letting $u_0$ vary, the eventual data determine ln 2 precisely modulo $\mathbb Q$, and every rational translate occurs for some $u_0$.

*Proof.* Condition 2 forces $y'_u-y_u=2^{u-u_0}q$ with $q=y'_{u_0}-y_{u_0}$. Since $v_p(L_{2u})=1$ for $u<p\le2u$, both $p y_u$ and $p y'_u$ are $p$-integral. Condition 3 is then $v_p(2^{u-u_0}q)\ge0$, that is $v_p(q)\ge0$. Every prime $p>u_0$ lies in some band $(u,2u]$ with $u\ge u_0$. Condition 1 at $u_0$ gives $q\in L_{2u_0}^{-1}\mathbb Z$. Conversely, such $q$ satisfy condition 1 at every later $u$, because $2^{u-u_0}L_{2u}/L_{2u_0}$ is an integer. For a given rational $r$, take $u_0$ exceeding every prime power in the odd part of its denominator and large enough for the dyadic part. $\square$

The script checks the three conditions exactly for $u_0=10\le u\le24$. They hold for $q=1/315$, $-7/48$ and $5/63$. The shifts $1/13$, $1/23$ and $2/33$ fail at $u=10$, by upper band, denominator and upper band respectively. Every Phase 14 zero-shell completion is of this form: its translation has denominator the odd part of $L_N$, so it is a single real number $\ln2+s/(2^NM)$ preserving all later data.

**Consequence for Track F.** Every property deduced from these eventual data alone holds for every $\ln2+r$, $r\in\mathbb Q$. Normality, irrationality exponent and transcendence are invariant under rational translation. Positive lower transition density can change under rational translation. For the sparse $K$ below, all but $o(N)$ of the first $N$ shifts are arbitrarily close to zero on the circle. Translating by $1/3$ puts those shifts arbitrarily close to $1/3$ or $2/3$, both interior transition points. Thus the transition frequencies tend to zero and one respectively. As a finite check, the first 4,095 gaps of $K=\sum_{j\ge0}2^{-2^j}$ contain 22 transitions, while those of $K+1/3$ contain 4,074. (Those of $\ln2+1/3$ contain 2,051.) The invariant strengthening needed is the following.

**Proposition (paper).** Suppose $x+r$ has lower transition density zero for a rational $r$. Then some limit point of the empirical measures of $(\{2^nx\})$ is the uniform measure on the eventual periodic orbit of $-r$ under doubling.

*Proof.* Along cutoffs with transition frequency tending to zero, any weak limit $\mu$ of the empirical measures of $x+r$ is doubling-invariant with $\mu((1/4,3/4))=0$. Then $\mu$ gives zero mass to every preimage of $(1/4,3/4)$. Every point except $0$ eventually enters this interval, because $1/4$ and $3/4$ map to $1/2$, so $\mu=\delta_0$. Hence $2^n(x+r)$ is within any fixed distance of an integer for all but $o(M)$ indices $n<M$. Uniform continuity transfers this to $2^nx$ and the periodic sequence $-2^nr$. $\square$

Excluding every rational periodic-orbit measure as a limit point of the empirical measures of ln 2 would therefore suffice for all its rational translates. The proposition gives only the indicated implication, since tracking an orbit as a set need not select its initial phase. Normality would exclude all of them. The Phase 14 cell test escapes this constraint because it uses the actual complementary residue $b_N$, which changes under translation.

**Other representations.** The displacement argument forces an initial rational difference to double. The admissible initial differences additionally depend on the representation's common denominators and observed prime bands. A Gaussian analogue requires checking them for its own cutoffs. [Phase 14 Gaussian representations](../phase14/gaussian-relations.md) The optimal reduced-denominator rate $5/12$ concerns denominators. It supplies no information on the residue $b$ beyond this class.

## 5. Moving primes

At shell $N$ the upper band is the set of primes $N<p\le2N$; these primes move with $N$. Its $p$-primary components double along the shell. [Phase 14 identification](../phase14/primary-components.md) · [Phase 14 review](../phase14/reviews/primary-characters.md)

**One prime, explicit (paper; float check).** Let $p$ be an odd prime, $t=\operatorname{ord}_p2$ and $p\nmid a$. Then for every $T\ge1$,
```math
\left|\sum_{0\le j<T}e_p(a2^j)\right|\ \le\ \sqrt p\,\Bigl(\Bigl\lfloor\frac Tt\Bigr\rfloor+2+\log t\Bigr).
```
Twisting a subgroup sum by a character $\psi$ of $H=\langle2\rangle$ averages Gauss sums over the extensions of $\psi$ to $\mathbb F_p^\times$, so it is at most $\sqrt p$. This bounds each complete period. For an incomplete period, expand the indicator of $[0,T')$ on $\mathbb Z/t$. The $\ell^1$ norm of its Fourier coefficients is less than $1+H_{\lfloor t/2\rfloor}\le2+\log t$. The script compares the bound with the exact maximum over all units for the first twelve primes above 256, at $T=16$ and $T=256$. The largest ratio occurs at $p=257$, $t=16$. For a power saving the displayed estimate needs both a sufficiently large order and a sufficiently long window. For example $t\ge p^{1/2+\epsilon}$ and $T\ge p^{1/2+\epsilon}$ suffice, with a logarithmic loss. The weaker cutoff $t>N^{1/3}$ requires the sum-product input even for some full shells.

**Bounded number of moving primes (source).** For distinct $p_1,\ldots,p_r$ in the band with $\operatorname{ord}_{p_i}2>N^{1/3}$, Bourgain–Chang Theorem 2.5 gives power cancellation of $\sum_{j\in I}e_Q(a2^j)$, $Q=\prod p_i$, uniformly in units $a$, in the choice of the primes and in windows of length at least $N^\delta$. The hypotheses are checked as in Phase 14, with $X$ replaced by $N$. For the separate standard Taylor band on $[N,3N/2]$, see the [conditional-variance transfer](pooled-prime-variance.md). Uniformity in the primes permits them to move. Bourgain–Glibichuk–Konyagin bounds **complete** sums over subgroups of size at least $p^\gamma$ in prime fields. Incomplete geometric progressions shorter than the order require Bourgain's or Bourgain–Chang's incomplete-sum theorems. Sampling 4,000 units for three pairs at $N=T=256$ gave largest means 0.15–0.17 (float). [Bourgain–Chang](https://doi.org/10.1016/j.crma.2004.08.007) · Bourgain–Glibichuk–Konyagin, *J. London Math. Soc.* (2) 73 (2006) 380–398

**Uniformity breaks at about $T/\log_2N$ primes (paper; exact).** Let $Q$ be a product of band primes with $Q>2^{T+1}$. The unit $a=1$ gives $\{2^j/Q\}<2^{j-T-1}\le1/4$ for $j<T$. Then the joint character mean is $1-O(1/T)$ and no transition occurs. Every estimate uniform in unit numerators fails beyond the least such $r$.

| *N* | *T* | Least *r* | Primes in (*N*, 2*N*] | Fraction |
| ---: | ---: | ---: | ---: | ---: |
| 1,024 | 32 | 4 | 137 | 0.029 |
| 1,024 | 256 | 26 | 137 | 0.190 |
| 16,384 | 128 | 10 | 1,612 | 0.006 |
| 16,384 | 4,096 | 291 | 1,612 | 0.181 |

The known theorems cover bounded $r$, and uniform statements are false beyond $r\approx(T+1)/\log_2N$. The real character involves all of the roughly $N/\log N$ band primes **and** the complementary factor. Any proof must therefore use the actual numerators, as the Phase 14 countermodels already indicated.

**Inverse statement (paper).** The diagonal error satisfies $2^N\ln2-y_N=\sum_{h\ge N}(-1)^hB(N,h)$, with $|\cdot|\le B(N,N)=N!^2/(2N+1)!$. This follows from the alternating expansion of $\int_0^1t^N/(2-t)\,dt$. With the CRT residues $a,b$ of Phase 14,
```math
\left|W_k-\frac1N\sum_{j<N}e\!\left(\frac{2^ja}{A}\right)e\!\left(\frac{2^jb}{B}\right)\right|\le\frac{2\pi\,2^N}{N}B(N,N).
```
If the shell has at most $\varepsilon N$ transitions, Section 1 and this comparison give
```math
\frac1N\sum_{j<N}\left|e\!\left(\frac{2^ja}{A}\right)-\overline{e\!\left(\frac{2^jb}{B}\right)}\right|^2\ \le\ 8\varepsilon+\frac4N+\frac{4\pi\,2^N}{N}B(N,N).
```
In mean square, few transitions are equivalent to the complementary orbit being the conjugate of the upper-band orbit. Bourgain–Chang equidistributes the upper-band orbit's projections onto any bounded set of primes. That fact does not constrain this full correlation, by the uniformity threshold above. Numerically the product mean reproduces $\operatorname{Re}W_k$ to five decimals at $N=256$, $1{,}024$ and $4{,}096$. Both marginal means are at most 0.05 there (float).

## 6. Literature: what the cited methods need

| Source | Statement as read, with hypotheses | Bearing on ln 2 |
| --- | --- | --- |
| Matomäki–Radziwiłł, *Ann. of Math.* 183 (2016) 1015–1056 | For real multiplicative $f$ with $\lvert f\rvert\le1$ and $h\to\infty$, short averages over $(x,x+h]$ match the long average for almost all $x\le X$. | Needs multiplicativity in the summation variable. The real factorization $e(Y_n)=\prod_{p}e(c_p(n))$ over primary components has every factor depending on $n$. It is not a multiplicative function of $n$. [arXiv:1501.04585](https://arxiv.org/abs/1501.04585) |
| Tao, *Forum Math. Pi* 4 (2016) e8 | Logarithmically averaged two-point Chowla and Elliott, via Matomäki–Radziwiłł–Tao and entropy decrement. The logarithmic weight makes $n\mapsto pn$ almost measure-preserving. | Section 3 shows that the prime-indexed variables carry negligible information on the digit window in the lift model. The only logarithmic analogue available is the shell-average criterion of Section 1. [arXiv:1509.05422](https://arxiv.org/abs/1509.05422) |
| Tao–Teräväinen, *Duke Math. J.* (2019) and *Algebra Number Theory* 13 (2019) | Structure of logarithmically averaged correlations, including odd-order logarithmic Chowla. Removal of the logarithmic average over the scale for all scales outside a set of zero logarithmic density. | Same multiplicativity requirement. The ordinary versus logarithmic distinction matches Section 1: the logarithmic target needs a positive density of good shells. [arXiv:1708.02610](https://arxiv.org/abs/1708.02610) · [arXiv:1809.02518](https://arxiv.org/abs/1809.02518) |
| Mauduit–Rivat, *Ann. of Math.* 171 (2010) 1591–1646 | $\sum_{p\le x}e(\alpha s_q(p))\ll x^{1-\sigma_q(\alpha)}$ when $(q-1)\alpha\notin\mathbb Z$. The method needs a carry property and uniformly small Fourier transforms of the truncated digital function. | The transition indicator has first Fourier coefficient $-1/\pi$, so the $L^\infty$ hypothesis fails. The summation runs over primes, not over the orbit of a fixed real. The analogue of the carry property is the cell certification. [Annals](https://doi.org/10.4007/annals.2010.171.1591) |
| Rivoal, *J. Aust. Math. Soc.* 85 (2008) 95–111 | If $x$ has finite irrationality exponent $\mu_x$, then the number of ones $B_n(x)\ge\log n/\log(\mu_x+\varepsilon)+O(1)$. Only denominators that are powers of 2 are used (§6). | Transition counts of logarithmic order only. Phase 13 records his Padé exponents for ln 2 with mixed denominators. [DOI](https://doi.org/10.1017/S1446788708000591) |
| Bailey–Borwein–Crandall–Pomerance (2004) | For algebraic irrational $\alpha$ of degree $d$: $B_n(\alpha)\ge c\,n^{1/d}$. | Algebraic only, and density zero. Cited via Rivoal. |
| Liu–Jiang–Zhang, arXiv:2610.10192v3 (5 Nov 2026) | Theorem 1: for each rational $r>0$, $r\ne1$, and each $\nu>2$, there is an ineffective $Q(r,\nu)$ with $\lvert\log r-p/q\rvert>q^{-\nu}$ for $q\ge Q$. Hence $\mu(\log r)=2$. The authors credit GPT-6 Astra and claim a Lean verification, which is not checked here. | A transition in $[m,(2+\epsilon)m)$ for large $m$ (Phase 14), so $\gg\log N$ transitions. [arXiv](https://arxiv.org/abs/2610.10192) |
| Mira-Cult/math, claim 0001 (main branch, read 24 Nov 2026) | For coprime $b,c\ge2$ and **every** irrational $x$, $S_b(N;x)+S_c(N;x)\ge c_{b,c}\log N\log\log N$ eventually, where $S_r$ counts adjacent unequal base-$r$ digits. The file says it applies to ln 2 in bases 2 and 3 jointly, gives no positive frequency and does not imply normality. | Joint two-base and $o(N)$. It gives no lower bound in base 2 alone. Not independently verified. [Repository](https://github.com/Mira-Cult/math/tree/main/notes/number-theory/normal-numbers) |
| Mira-Cult/math, claim 0002 and *Normal Dovetails* | Erdős–Borwein short-window word density for $7/12<a\le1$ (reviewed in Phase 13). Normality of constructed streams. The root README states that none proves normality of an unchanged classical constant. | No statement about ln 2 digits. [Phase 13 review](../phase13/erdos-borwein.md) |

No positive lower density of digit changes in base 2 is known for ln 2. To our reading of these sources, none is known for any of $e$, $\pi$ or $\sqrt2$ either.

## 7. Exact sufficient theorem, closest input, missing estimate

**Sufficient (paper, from the Lean shell inequality).** If $\operatorname{Re}W_k\le1-c$ for every large $k$, then ln 2 has lower transition density at least $c/8$, and its limiting interval discrepancy is below one. If this holds for a set of $k$ of lower density $d>0$, the lower logarithmic transition density is at least $cd/(8\log2)$. In the cell form of Phase 14, at least $cN$ marks on every late shell suffice. With the weights of Section 2, this gives about $(c-\theta)N/(1-\theta)$ starts with $\theta m$ changes for $T=o(N)$.

**Closest inputs.**
- The exponent-two theorem gives one transition per $[m,(2+\epsilon)m)$.
- Mira's claim gives $\log N\log\log N$ changes jointly in bases 2 and 3.
- Bourgain–Chang gives power cancellation for a bounded number of moving upper-band primes.
- In the lift model, the failure upper bound at $N=16{,}384$, $T=128$ evaluates numerically to about $2^{-54.1}$.
- The certified true shells $2^8$ through $2^{16}$ satisfy $\operatorname{Re}W_k\le0.512$ (the weakest is $N=8{,}192$, with 4,001 transitions).

**Missing estimate.** A bound $\operatorname{Re}W_k\le1-c$ on all late shells, or on a positive proportion of them for the logarithmic version. In CRT form this is
```math
\operatorname{Re}\frac1N\sum_{j<N}e\!\left(\frac{2^ja_N}{A_N}\right)e\!\left(\frac{2^jb_N}{B_N}\right)\le1-c .
```
Such an estimate must use the actual complementary residue $b_N$. By the countermodels, the entropy bound and the uniformity threshold, upper-band information is insufficient. An argument that uses only eventual upper-band data must also exclude every rational periodic orbit as a limit of the empirical measures (Section 4). In this sense the problem is the original one-frequency equidistribution question for ln 2.

**Scope.** The Lean statements are those cited from `FirstFrequency.lean`. Sections 2–5 are paper proofs with the stated exact checks. The literature rows report statements as read from primary sources on 24 November 2026. The external 2026 claims are unverified here. Historical priority for the weight identity, the rigidity theorem and the uniformity threshold has not been assessed.
