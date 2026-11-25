# What pooling the moving primes measures

Choose $n$ uniformly in a consecutive interval $I\subset[N,3N/2]$ and then choose $p$ uniformly among the odd primes of $(3N/4,N]$ with $\mathrm{ord}_p(2)>N^{1/3}$. These choices define a finite probability space. The standard shifted prefix is $Y_n=\sum_{k=1}^n2^{n-k}/k$, and $A_{p,n}=2^{n-p}/p\bmod1$ is its entire $p$-primary part since $p\le n<2p$. Put $B_{p,n}=Y_n-A_{p,n}\bmod1$. Each position has exactly the same weight as in the original window.

Partition the circle into $K$ equal half-open cells, for fixed $K\ge2$, and condition on the cell containing $B$. For a complex unit variable $Z$ define variance by $\mathbf E|Z-\mathbf EZ|^2$. Write $V$ for the expected conditional variance of $e(A)$, $m_I=|I|^{-1}\sum_{n\in I} e(Y_n)$ and $s_K=\sin(\pi/K)/(\pi/K)$. If $|I|\ge N^\delta$ for some fixed $\delta>0$, then for some $\eta=\eta(\delta)>0$,
$$
V=1-s_K^2 |m_I|^2+O_{K,\delta}(N^{-\eta}).
$$
The same estimate holds if $Y_n$ in both $B$ and $m_I$ is replaced by **any** prescribed sequence of targets. The error is uniform in those targets. The marginal cancellation input is external. The deduction below is a paper proof.

## Proof

At fixed $n$ let $d_n$ be the extreme interval discrepancy across $p$ of $A_{p,n}$. The moving-prime estimate gives $\mathbf E_n d_n\ll_\delta N^{-\eta}$. Here are the hypotheses needed for this application. Discarded primes divide the product of $2^j-1$ up to $N^{1/3}$, so their count is $O(N^{2/3}/\log N)$. The prime number theorem supplies $\asymp N/\log N$ primes before exclusion. For any pair of distinct good primes $p,q$, any $1\le h\le\sqrt N$, the character of $h(A_{p,n}-A_{q,n})$ is $e_{pq}(c2^{n-\min I})$ with a unit numerator $c$ (use $2^{n-p}\equiv 2^{n-1}\bmod p$ and absorb the first exponent into the unit coefficient; shifting the summation index by one multiplies it by a further unit). Both local orders exceed $N^{1/3}$, both factors exceed $(pq)^{1/4}$ eventually, and the length and orders exceed $(pq)^\epsilon$ for $\epsilon=\min(\delta,1/3)/3$. Bourgain–Chang's Theorem 2.5 gives a power saving for this incomplete sum. In the mean square of the prime-average character, the diagonal costs the reciprocal of the prime count. Erdős–Turán with $H=\lfloor\sqrt N\rfloor$ and Cauchy–Schwarz now give the stated bound after absorbing logarithms. This adapts Phase 14's two-prime estimate to the standard Taylor band. [Incomplete-sum theorem](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2004.08.007.pdf) · [Phase 14 proof and source audit](../phase14/reviews/primary-characters.md)

For a cell $C$, write $b_C=\Pr(B\in C)$ and $v_C=\mathbf E[e(A)1_{B\in C}]$. First integrate over $p$ at each fixed $n$. If $A$ had Lebesgue measure, translation and reflection would give the comparison values
$$
b_C^*=1/K,\qquad v_C^*=m_I\int_C e(-b)\,db .
$$
The interval for $A$ is $Y_n-C$ and may wrap or have reversed endpoint conventions. The same discrepancy bound holds for either endpoint convention by one-sided approximation (equivalently, use circular intervals and their complements). Integration by parts on up to two intervals bounds the error for the weighted indicator $e(a)1_{Y_n-C}(a)$ by $(4+2\pi)d_n$, using $|e'(a)|=2\pi$. The mass error is at most $2d_n$. Averaging over $n$ gives these bounds with $d_n$ replaced by its mean.

The variance is $1-\sum_C|v_C|^2/b_C$, with an empty cell contributing zero to the sum. For $|v|\le b$, the expression $|v|^2/b$ equals the supremum of $2\Re(\bar u v)-b|u|^2$ over $|u|\le1$, including the empty-cell convention. Its change is thus at most $2|v-v^*|+|b-b^*|$. Finally $|\int_C e(-b)\,db|=s_K/K$. Summing proves the formula. In particular the argument introduces no independence assumption between the true CRT components.

## A transfer before using prime equidistribution

There is also a finite implication for one prime, several jointly chosen primes, or conditioning on the prime label as well as the mesh. Use any sampling law with the specified uniform marginal on positions and put $Z=e(Y)$, $m=\mathbf E Z$, and $U=e(A)$. Each conditioning cell has $B$ in an arc of angular half-width $\theta=\pi/K\le\pi/2$ centered at $c$ (in turns). Conditional expectation minimizes mean square error among predictors constant on the conditioning classes. Try the predictor $m\cos(\theta)e(-c)$. Since $|e(-B)-\cos(\theta)e(-c)|\le\sin\theta$, Minkowski's inequality gives
$$
\sqrt{V}\ \le\ \|e(-B)(Z-m)\|_2+|m|\sin\theta
\ \le\ \sqrt{1-|m|^2}+\sin\theta.
$$
Thus $1-\Re m\ge \tfrac12(\sqrt V-\sin\theta)_+^2$. A persistent excess of $V$ above $\sin^2\theta$ suffices even without any independence or marginal equidistribution. The cutoff is sharp at $Z=1$ for arbitrary arrays: put equal mass near the two ends of one cell and take $A=-B$. The preceding pooled-prime theorem gives a smaller and exactly computable floor for its specified arithmetic sampling law.

## The mesh threshold

At $K=8$ the predicted floor is 0.050359 to six decimal places. On $[1024,1536]$ the measured pooled variances are 0.052358 for the zero target and 0.998751 for the Taylor prefix. The calculation selects cells by exact rational comparisons and evaluates the complex moments numerically. [Finite calculation](../../scripts/phase15_pooled_primes.py)

Even when $Y_n$ is identically zero, the limiting pooled variance equals $1-s_K^2>0$. Strict positivity by itself is automatic in this example. A positive excess over that **specific floor** is equivalent, up to the vanishing error, to a deficit of the modulus of the window character. The same calculation applies to a mesh whose origin is translated, or to each of any fixed finite list of translated meshes. Pooling more positions and primes in this particular statistic cannot by itself remove the unknown diagonal mean.

For the actual logarithm, $0<2^n\ln2-Y_n\le1/(n+1)$. Replacing the prefix by the true phase changes the window character by at most $2\pi/(N+1)$. On any sequence of growing consecutive windows the modulus of the true mean approaches one exactly when its real part approaches one. Indeed, for $W=e(2^n x)$ with $n$ uniform on the window and $m=\mathbf E W$, one has $|\mathbf E W^2-m|\le2/|I|$ by shifting and $|\mathbf E W^2-m^2|\le\mathbf E|W-m|^2=1-|m|^2$. Thus $|m|\,|1-m|\le1-|m|^2+2/|I|$. The statement applies to this binary orbit, while the variance formula itself holds for arbitrary target arrays. A uniform excess over the floor on $[N,3N/2]$ for every sufficiently late dyadic $N$ would give positive lower mean of the cosine escape $E(t)=1-\cos(2\pi t)$ on the full orbit, since disjoint complete segments in previous shells already occupy a fixed positive fraction of each prefix. The unresolved estimate is an excess bounded away from zero for the fixed arithmetic lift. [Conditional variation and finite tests](conditional-variation.md) · [Dyadic transfer](../classical-discrepancy.md)
