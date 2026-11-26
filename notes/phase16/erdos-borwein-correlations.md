# Two-source arrival correlations of the Erdős–Borwein constant

Let $`E=\sum_{m\ge1}(2^m-1)^{-1}=\sum_{m\ge1}\tau(m)2^{-m}`$, where $`\tau`$ counts divisors. As in [Phase 14](../phase14/erdos-borwein-frequencies.md), write $`\tau(m)=2^{V(m)}U(m)`$ with $`U(m)`$ odd. The term indexed by $`m`$ places the odd **mark** $`U(m)`$ at binary position $`t(m)=m-V(m)`$, and $`m`$ is called a source at $`t(m)`$. Let $`N(t)`$ be the number of sources at $`t`$ and $`C(t)=\sum_{t(m)=t}U(m)`$. A shift $`n`$ reads the fractional digits $`n+1,n+2,\dots`$. Throughout, $`T=\log\log N`$ and $`e(x)=\exp(2\pi ix)`$. Write $`f_\theta(m)=e(\theta V(m))`$. This is a 1-bounded multiplicative function with $`f_\theta(p)=e(\theta)`$ at every prime, since $`V`$ is additive. Let $`\nu`$ be the law of $`U_*`$ and $`Q_D`$ the marked Poisson comparison law of Phase 14.

For a window $`I=[N,N+H)`$ of positions, an integer $`b\ge0`$ and functions $`F,G`$ on the odd residues modulo $`2^r`$, let $`A_k(b)`$ be the set of $`m\ge1`$ with $`m+k\ge1`$, $`t(m)\in I`$ and $`V(m+k)-V(m)=k-b`$. The **two-source moment** is

```math
M_2(b)=\frac1H\sum_{k\ne0}\ \sum_{m\in A_k(b)}F(U(m))\,G(U(m+k)).
```

It counts ordered pairs of distinct sources at positions $`t`$ and $`t+b`$ with $`t\in I`$. The independent marked Poisson process has $`M_2(b)=\nu(F)\nu(G)`$ for every $`b\ge0`$.

## Summary

**The Poisson comparison law passes every two-source test that current methods can reach, and the standard random model predicts that it is the true limit.** If that prediction holds, $`E`$ is *not* simply normal in base two: its limiting frequency of ones would be the Phase 14 value $`p_*\in[0.492230,0.492685]`$.

| Result | Status | Section |
| --- | --- | --- |
| Spectral and decoupling identities for $`M_2(b)`$. The self-exclusion term is $`(4\pi T)^{-1/2}+O(T^{-1})`$. | Proved (uses the Phase 14 local limit) | [1](#1-exact-identities) |
| Exact $`p`$-adic joint law of $`(v_p(m),v_p(m+k))`$. Each local factor has Haar average exactly one over the gap $`k`$, and every factor tends to one in the pretentious range. | Proved | [2](#2-local-euler-factors) |
| The pair correlation is Poissonian on every mesoscopic scale $`L`$ with $`L\log\log T/\log T\to\infty`$. In the pretentious range the two-point characteristic function is a product of local factors. | Paper deduction from the two-form Kubilius comparison (external input K2) | [3](#3-the-kubilius-model-gives-mesoscopic-poisson-correlations) |
| At the lattice scale, $`M_2(b)\to\nu(F)\nu(G)`$ under a two-point Elliott bound with saving $`o(1/(A\sqrt T))`$ over the gaps $`\lvert k\rvert\le A\sqrt T`$. A ledger records what MRT, Tao, Helfgott–Radziwiłł, Pilatte and Tao–Teräväinen provide. | Conditional deduction | [4](#4-the-lattice-scale-and-the-square-root-of-t-ledger) |
| If the factorial moments are Poissonian along any infinite sequence of dyadic scales, then the shell one-frequency tends to $`p_*`$ along that sequence and $`E`$ is not simply normal. | Conditional deduction from Phase 14 | [5](#5-does-the-poisson-model-describe-the-limit) |
| Mira Cult's prime-conditioned isolation is a one-prime lower-bound sieve. Its bounds are $`\exp(-O(2^kk^2))`$ with an ineffective threshold, and it gives no upper bounds and no asymptotics. | Analysis of the [audited proof](../phase13/reviews/erdos-local-limit.md) | [6](#6-what-mira-cults-isolation-method-can-and-cannot-give) |
| Exact counts on $`[2^{12},2^{24})`$. They give finite-$`T`$ moments, the decomposition by $`k`$, total variation from $`Q_D`$, and checks of the local-factor model. Crandall's $`2^{43}`$ table appears to have its 0/1 labels interchanged. | Finite computation | [7](#7-finite-computations) |

## 1. Exact identities

**Theorem 1 (proved).** Let $`S_I=\{m\ge1:t(m)\in I\}`$.

1. For $`F=G=1`$ and $`b=0`$, $`M_2(0)=H^{-1}\sum_{t\in I}N(t)(N(t)-1)`$.
2. *(Spectral form.)* Expand $`F=\sum_\chi\widehat F(\chi)\chi`$ over the characters of $`(\mathbb Z/2^r\mathbb Z)^\times`$, and likewise $`G`$. Because $`S_I`$ is finite, $`A_k(b)`$ is empty for all sufficiently large $`\lvert k\rvert`$ (on $`I=[N,N+H)`$ with $`H\le N`$, $`V(m+k)-V(m)=k-b`$ forces $`\lvert k\rvert\le K_I:=2\log_2 N+b+2`$). Integrating termwise over the finite set $`0<\lvert k\rvert\le K_I`$ gives

   ```math
   M_2(b)=\sum_{\chi_1,\chi_2}\widehat F(\chi_1)\widehat G(\chi_2)\int_0^1 e(\theta b)\sum_{0<\lvert k\rvert\le K_I}e(-\theta k)\,c_k(\theta;\chi_1,\chi_2)\,d\theta,
   ```

   where $`c_k`$ is a shifted correlation of two 1-bounded multiplicative functions, each taking the value $`e(\mp\theta)`$ at every prime. Terms with $`m+k<1`$ are omitted.

   ```math
   c_k(\theta;\chi_1,\chi_2)=\frac1H\sum_{m\in S_I}\overline{f_\theta(m)}\,\chi_1(U(m))\cdot f_\theta(m+k)\,\chi_2(U(m+k)).
   ```

3. *(Decoupling.)* Take $`F=G=1`$. Let $`p_v`$ be the proportion of $`m\in S_I`$ with $`V(m)=v`$, put $`P^*_x=\sum_vp_vp_{v+x}`$, and let $`P_k(b)=H^{-1}\lvert A_k(b)\rvert`$. Then

   ```math
   M_2(b)=\frac{\lvert S_I\rvert}{H}\bigl(1-P^*_{-b}\bigr)+\sum_{k\ne0}\Bigl(P_k(b)-\frac{\lvert S_I\rvert}{H}P^*_{k-b}\Bigr).
   ```

4. On dyadic windows $`I=[N,2N)`$ we have $`\lvert S_I\rvert=H+O(\log N)`$ and, for fixed $`b`$, $`P^*_{-b}=(4\pi T)^{-1/2}+O_b(T^{-1})`$.

*Proof.* Item 1 follows from the definition and the identity $`t(m+k)-t(m)=k-(V(m+k)-V(m))`$. For item 2, insert $`\mathbf 1[x=0]=\int_0^1e(\theta x)\,d\theta`$ with $`x=V(m+k)-V(m)-k+b`$, then use orthogonality of characters. Item 3 holds because $`\sum_{k\in\mathbb Z}P^*_{k-b}=1`$. For item 4, the size of $`S_I`$ is Phase 14's reindexing, and $`S_I`$ differs from $`I`$ by $`O(\log N)`$ integers. Phase 14's dyadic local limit gives

```math
\Pr\nolimits_{m\in I}(V(m)=j)=L(j)+O(T^{-3/2}),\qquad L=p_T+\gamma q_T,
```

uniformly in $`j`$. Write $`\mu(j)`$ for the left side. Then

```math
\sum_j\mu(j)\mu(j-b)=\sum_jL(j)L(j-b)+O(T^{-3/2}),
```

because $`\sum_j\mu(j)=1`$ and $`\sum_j\lvert L(j)\rvert=O(1)`$. Next, $`\sum_jp_T(j)p_T(j-b)=e^{-2T}I_b(2T)=(4\pi T)^{-1/2}(1+O_b(T^{-1}))`$. The cross terms with $`q_T`$ are $`O(T^{-1})`$, since $`\max p_T\ll T^{-1/2}`$ and $`\sum_j\lvert q_T(j)\rvert\ll T^{-1/2}`$. $`\square`$

The first term in item 3 is the value for independent displacements. The quantity $`P^*_{-b}`$ is a **self-exclusion hole**: a source cannot be its own partner. Only the correlation excess $`\sum_k(P_k-P^*_{k-b})`$ can depend on the arithmetic. Since $`\sum_kP^*_{k-b}`$ is exactly one, a $`k`$-independent perturbation of the law of $`V(m+k)-V(m)`$ cannot change $`M_2`$. Only the $`k`$-dependence of that law matters.

## 2. Local Euler factors

Let $`p`$ be prime and fix $`k`$ with $`v_p(k)=\kappa\ge0`$. Let $`m`$ be Haar-distributed on $`\mathbb Z_p`$. Put $`a=v_p(m)`$ and $`a'=v_p(m+k)`$. For a weight $`w`$ on $`\{0,1,2,\dots\}`$ write $`\varphi(w)=\mathbb E\,w(a)`$.

**Theorem 2 (proved).**

1. If $`a<\kappa`$ then $`a'=a`$. If $`a>\kappa`$ then $`a'=\kappa`$. Conditionally on $`a=\kappa`$, the excess $`a'-\kappa`$ is $`0`$ with probability $`(p-2)/(p-1)`$. It equals $`i\ge1`$ with probability $`(1-1/p)p^{1-i}/(p-1)`$. The pair $`(a,a')`$ is exchangeable.
2. If $`\kappa=0`$ and $`w_1(0)=w_2(0)=1`$, then $`\mathbb E[w_1(a)w_2(a')]=\varphi(w_1)+\varphi(w_2)-1`$.
3. *(Haar average over the gap.)* For all bounded $`w_1,w_2`$,

   ```math
   \sum_{\kappa\ge0}(1-1/p)p^{-\kappa}\,\mathbb E_\kappa[w_1(a)w_2(a')]=\varphi(w_1)\varphi(w_2).
   ```

4. Let $`w_j(a)=e(\theta_jv_2(a+1))`$ and $`\phi_p(\theta)=\mathbb E\,e(\theta v_2(a+1))`$. Then $`\lvert\phi_p(\theta)\rvert\ge(p-1)/(p+1)\ge1/3`$. For every $`\kappa`$,

   ```math
   \bigl\lvert\mathbb E_\kappa[w_1(a)w_2(a')]-\phi_p(\theta_1)\phi_p(\theta_2)\bigr\rvert\le\frac{8\pi^2\lvert\theta_1\theta_2\rvert}p .
   ```

   When $`\kappa=0`$ the right side can be replaced by $`16\pi^2\lvert\theta_1\theta_2\rvert/p^2`$.
5. Define $`R_p=\mathbb E_\kappa[w_1w_2]/(\phi_p(\theta_1)\phi_p(\theta_2))`$ and $`\mathcal E_k(\theta_1,\theta_2)=\prod_pR_p`$ with $`\kappa=v_p(k)`$. This product converges absolutely. There is an absolute $`C`$ such that, whenever $`\lvert\theta_1\theta_2\rvert\le10^{-3}`$ and $`k\ne0`$,

   ```math
   \lvert\log\mathcal E_k(\theta_1,\theta_2)\rvert\le C\lvert\theta_1\theta_2\rvert\Bigl(1+\sum_{p\mid k}\frac1p\Bigr).
   ```

*Proof.* (1) Write $`m=p^\kappa x`$ and $`k=p^\kappa y`$ with $`y`$ a unit. If $`a<\kappa`$, then $`m+k`$ has the valuation of $`m`$. If $`a>\kappa`$, it has the valuation of $`k`$. If $`a=\kappa`$, then $`x`$ is a uniform unit, and $`x+y\equiv0\pmod p`$ for exactly one of the $`p-1`$ unit classes. Deeper congruences are uniform. Exchangeability follows because Haar measure is invariant under $`(m,m+k)\mapsto(m+k,m)`$ composed with $`k\mapsto-k`$. Alternatively, compare the probabilities case by case.

(2) For $`\kappa=0`$ the events $`a\ge1`$ and $`a'\ge1`$ are disjoint, each has the marginal law $`(1-1/p)p^{-j}`$, and $`\Pr(a=a'=0)=1-2/p`$.

(3) If $`k`$ is Haar-distributed independently of $`m`$, then $`(m,m+k)`$ is Haar-distributed on $`\mathbb Z_p^2`$. Also $`\Pr(v_p(k)=\kappa)=(1-1/p)p^{-\kappa}`$.

(4) The values of $`a`$ with $`v_2(a+1)=0`$ are the even $`a`$, with total mass $`p/(p+1)`$, which gives the lower bound for $`\lvert\phi_p\rvert`$. Since $`a'`$ has the law of $`a`$, the difference in item 4 is the covariance of $`w_1(a)`$ and $`w_2(a')`$. It is at most $`(\mathbb E\lvert w_1-1\rvert^2\,\mathbb E\lvert w_2-1\rvert^2)^{1/2}\le4\pi^2\lvert\theta_1\theta_2\rvert\,\mathbb E[v_2(a+1)^2]`$, and $`\mathbb E[v_2(a+1)^2]\le2/p`$. When $`\kappa=0`$, item 2 gives the exact difference $`-(\phi_p(\theta_1)-1)(\phi_p(\theta_2)-1)`$. Here $`\lvert\phi_p-1\rvert\le2\pi\lvert\theta\rvert\,\mathbb E\,v_2(a+1)\le4\pi\lvert\theta\rvert/p`$.

(5) Divide item 4 by $`\lvert\phi\phi\rvert\ge1/9`$. Then $`\lvert R_p-1\rvert\le1/2`$ in the stated range, and $`\lvert\log(1+x)\rvert\le2\lvert x\rvert`$. Sum over $`p\mid k`$ and over all $`p`$ with weight $`p^{-2}`$. $`\square`$

**Answer to question (a).** In the pretentious range $`\theta=O(A/\sqrt T)`$ the local factors at $`2`$ and at all small primes wash out pointwise in $`k`$. The factor $`\mathcal E_k(-\theta,\theta)`$ that multiplies the decoupled two-point characteristic function is $`1+O(A^2T^{-1}\log\log\log N)`$ for $`\lvert k\rvert\le N`$. **No persistent constant factor different from one survives.** The local factors persist only where the decoupled factor is already negligible. At a fixed frequency $`\theta\ne0`$, item 3 shows that the factors are bounded, genuinely $`k`$-dependent, and of mean exactly one. For $`\theta=1/2`$ the $`2`$-adic factor $`R_2`$ is

| $`v_2(k)`$ | $`0`$ | $`1`$ | $`2`$ | $`3`$ | $`4`$ |
| --- | --- | --- | --- | --- | --- |
| $`R_2`$ at $`\theta=1/2`$ | $`-0.39085`$ | $`+0.39085`$ | $`+4.35868`$ | $`+4.35868`$ | $`+4.35868`$ |

The full product $`\mathcal E_k(1/2,1/2)`$ is $`-0.077,+0.077,-0.445,+0.864`$ for $`k=1,2,3,4`$ and $`+4.964`$ for $`k=12`$. Its mean over $`k\le4096`$ is $`0.971`$. The limit of this mean as $`K\to\infty`$ is one: for any prime cutoff $`P`$, the truncated product $`\mathcal E_k^{(P)}=\prod_{p\le P}R_p`$ has mean $`1`$ by item 3 and the Chinese remainder theorem, while Theorem 2(4)–(5) gives $`\lvert R_p-1\rvert\ll p^{-1}`$ for $`p\mid k`$ and $`\ll p^{-2}`$ for $`p\nmid k`$, so the tail satisfies $`K^{-1}\sum_{k\le K}\lvert\mathcal E_k-\mathcal E_k^{(P)}\rvert\ll\sum_{p>P}p^{-2}\ll P^{-1}`$ uniformly in $`K`$ (using the uniform bound on $`\mathcal E_k^{(P)}`$ in $`L^2`$: $`\mathbb E[R_p^2]=1+O(p^{-2})`$). Letting $`K\to\infty`$ and then $`P\to\infty`$ yields mean $`1`$. Marks behave the same way at $`\theta=0`$. For $`F=\mathbf 1[U\equiv3\bmod4]`$ the local model predicts the following pointwise factors in $`\mathbb E[F(U(m))F(U(m+k))]/\nu(F)^2`$, and the integers on $`[2^{21},2^{22})`$ confirm them to three or four digits:

| $`k`$ | not divisible by $`4`$ or $`9`$ | $`4\Vert k`$ | $`8\mid k`$ | $`k=9`$ |
| --- | --- | --- | --- | --- |
| model | $`0.7780`$ | $`1.1707`$ | $`1.7895`$ | $`0.9880`$ |
| integers | $`0.7777`$–$`0.7790`$ | $`1.1700`$–$`1.1708`$ | $`1.7886`$ | $`0.9866`$ |

The mean of the model over $`k\le2048`$ is $`0.9995`$. These persistent mark factors disappear from $`M_2`$ only because the gaps that contribute are spread over a window of width about $`\sqrt{2T}`$.

## 3. The Kubilius model gives mesoscopic Poisson correlations

**External input K2 (Kubilius model for two shifted integers).** For $`y\ge2`$ let $`a_y(n)=\prod_{p\le y}p^{v_p(n)}`$. There is an absolute $`c>0`$ with the following property. The bound below holds uniformly for $`N\ge16`$, $`2\le u\le(\log N)^{1/3}`$, $`y=N^{1/u}`$, $`0<\lvert k\rvert\le N^{1/3}`$ and every set $`\mathcal A`$ of pairs of $`y`$-smooth integers:

```math
\Bigl\lvert\Pr\nolimits_{N\le m<2N}\bigl((a_y(m),a_y(m+k))\in\mathcal A\bigr)-P^{(y)}_k(\mathcal A)\Bigr\rvert\ll e^{-cu\log u}+N^{-c}.
```

Here $`P^{(y)}_k`$ is the product over $`p\le y`$ of the Haar laws of $`(p^{v_p(m)},p^{v_p(m+k)})`$ in Theorem 2. For one integer this is Kubilius' theorem; see Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Part III, the chapter on the Kubilius model. A direct route to the two-form case truncates both smooth parts to $`a_y(m),a_y(m+k)\le N^\eta`$, conditions on compatible residue pairs $`(d_1,d_2)`$ with $`\gcd(d_1,d_2)\mid k`$, and applies the fundamental lemma of the sieve in dimension two to the at most two forbidden classes per prime $`p\le y`$ (Halberstam–Richert, *Sieve Methods*, Theorem 2.5; Friedlander–Iwaniec, *Opera de Cribro*, Chapter 6). We take K2 as an external input and have not written out the full uniform total-variation proof here.

Fix $`A\ge1`$ and a smooth $`w\ge0`$ supported in $`[-A,A]`$. Put $`w_N(m)=w((V(m)-T)/\sqrt T)`$, which selects **typical** sources. For an integer interval $`J`$ let

```math
\Pi_N(J)=\frac1N\sum_{t(m)\in[N,2N)}\ \sum_{m'\ne m:\ t(m')-t(m)\in J}w_N(m)\,w_N(m').
```

**Theorem 3 (paper deduction from K2).** Let $`J_N\subset[-T,T]`$ be intervals whose lengths $`L_N`$ satisfy $`L_N\log\log T/\log T\to\infty`$. Then

```math
\Pi_N(J_N)=L_N\Bigl(\int w\,d\Gamma\Bigr)^2(1+o(1)),
```

where $`\Gamma`$ is the standard Gaussian measure. This is exactly the Poisson value for the typical sources.

*Proof (outline with the quantitative choices).*

0. Take $`u=\lceil C\log T/\log\log T\rceil`$ with $`C`$ large in terms of $`c`$, and $`y=N^{1/u}`$. Write $`n=a_y(n)r_y(n)`$. Every prime factor of $`r_y(n)<3N`$ exceeds $`y`$, so $`0\le V(r_y(n))\le\Omega(r_y(n))\le u`$. The support of $`w`$ and $`J_N\subset[-T,T]`$ force $`\lvert k\rvert\le2T`$. The set $`S_I`$ differs from $`[N,2N)`$ by $`O(\log N)`$ elements.
1. Let $`D_k=V(m+k)-V(m)`$ and $`D^y_k=V(a_y(m+k))-V(a_y(m))`$. Then $`\lvert D_k-D^y_k\rvert\le u`$, so $`\mathbf 1_J(k-D_k)`$ and $`\mathbf 1_J(k-D^y_k)`$ differ only when $`k-D^y_k`$ lies within $`u`$ of an endpoint of $`J`$. Replacing $`V`$ by $`V\circ a_y`$ inside $`w_N`$ changes each term by $`O(\lVert w'\rVert_\infty u/\sqrt T)`$ on the shifted support $`[-A-1,A+1]`$, so summing over $`k`$ (using the atom bound of step 3 below) changes $`\Pi_N(J_N)`$ by $`O(L_N\lVert w'\rVert_\infty u/\sqrt T)=o(L_N)`$ since $`u/\sqrt T\ll\log T/(\sqrt T\log\log T)\to0`$.
2. By K2, the remaining expectations, now functions of $`(a_y(m),a_y(m+k))`$, change by $`O(T\cdot e^{-cu\log u})=o(1)`$ in total over $`\lvert k\rvert\le2T`$ when the model $`P^{(y)}_k`$ is substituted.
3. Under $`P^{(y)}_k`$, $`D^y_k=\sum_{p\le y}X_p`$ with independent symmetric $`X_p`$ (Theorem 2(1)). For $`p\nmid k`$, Theorem 2(2) gives $`\mathbb E\,e(\theta X_p)=2\,\mathrm{Re}\,\phi_p(\theta)-1`$. Hence $`\lvert\mathbb E\,e(\theta D^y_k)\rvert\ll(\log T)^{O(1)}\exp(-2(1-\cos2\pi\theta)(T-\log u))`$. The variance is $`2T+O(\log u+\sum_{p\mid k}p^{-1})`$. Fourier inversion gives a local limit theorem with error $`(\log T)^{O(1)}T^{-3/2}`$. Exponential tilting gives the atom bound $`\Pr(D^y_k=x)\ll T^{-1/2}e^{-x^2/(5T)}`$ for $`\lvert x\rvert\le T`$. Summed over $`k`$, the boundary terms from step 1 therefore cost $`O(u)`$, which is $`o(L_N)`$.
4. Compare $`P^{(y)}_k`$ with the decoupled law $`P^*`$ of two independent copies. The two-variable characteristic function under $`P^{(y)}_k`$ is $`\Phi_y(\theta_1)\Phi_y(\theta_2)\mathcal E^{(y)}_k(\theta_1,\theta_2)`$. By Theorem 2(4)–(5), each joint atom differs from its decoupled value by $`\ll T^{-2}(\log T)^{O(1)}`$. On the region where $`\lvert\theta_1\theta_2\rvert>10^{-3}`$, the unnormalized product over $`p\nmid k`$ decays in both variables. For each $`j\in J`$ the weighted sum over $`(v,k)`$ has $`O(A^2T)`$ terms, so it changes by $`O(A^2T^{-1}(\log T)^{O(1)})`$. Under $`P^*`$ the sum over all $`k`$ is exactly $`(\mathbb E\,w)^2`$, and removing the term $`k=0`$ costs $`O(T^{-1/2})`$.
5. Finally $`\mathbb E\,w((V-T)/\sqrt T)\to\int w\,d\Gamma`$ by the central limit theorem for $`V`$ (Phase 14). $`\square`$

*Remarks (expected extensions).* Adding marks $`F(U(m))G(U(m'))`$ requires averaging the persistent mark factors of the primes $`p\le P`$ over $`k`$ weighted by the smooth-part density of $`D^y_k`$, using Theorem 2(3) together with equidistribution of the large-prime part modulo $`\prod_{p\le P}p^e`$ and an $`O(1/P)`$ tail bound for primes $`P<p\le y`$. Similarly, $`r`$-point mesoscopic Poisson correlations would use the $`r`$-form version of K2. We leave the weighted-averaging details of those extensions as remarks rather than proved clauses of Theorem 3. At accessible sizes $`\sqrt T<2`$, so the mesoscopic regime is empty in practice.

**Corollary 3.1 (pretentious-range characteristic function; paper deduction from K2).** Take $`0<\lvert k\rvert\le N^{1/3}`$ and $`\lvert\theta\rvert\le1/2`$, with $`u`$ and $`y`$ as above. Then

```math
\mathbb E_{N\le m<2N}\,e\bigl(\theta(V(m+k)-V(m))\bigr)=\lvert\Phi_y(\theta)\rvert^2\,\mathcal E^{(y)}_k(-\theta,\theta)+O\Bigl(\lvert\theta\rvert u+e^{-cu\log u}+N^{-c}\Bigr).
```

Here $`\lvert\Phi_y(\theta)\rvert^2=\exp(-2(1-\cos2\pi\theta)(T-\log u)+O(1))`$. Since $`2(1-\cos2\pi\theta)=4\pi^2\theta^2+O(\theta^4)`$, for $`\lvert\theta\rvert\le\sqrt{\log T/T}`$ Theorem 2(5) makes the right side

```math
e^{-4\pi^2\theta^2T(1+o(1))}\Bigl(1+O\bigl(\theta^2\log\log\log N\bigr)\Bigr)+O\Bigl(\frac{(\log T)^{3/2}}{\sqrt T}\Bigr).
```

This has the product-of-local-factors shape that Klurman's correlation theorem gives for fixed pretentious functions (Compositio 153 (2017) 1622–1657). Klurman's theorem itself does not apply. For fixed $`\theta\ne0`$, $`f_\theta`$ is not pretentious (Lemma 4.1). For $`\theta=\theta_N\to0`$ the family depends on $`N`$, which lies outside his fixed-function setting.

## 4. The lattice scale and the square-root-of-$`T`$ ledger

**Lemma 4.1 (non-pretentiousness).** For $`0<\lVert\theta\rVert\le1/2`$,

```math
\min_{\lvert t\rvert\le X^2}\ \sum_{p\le X}\frac{1-\mathrm{Re}\bigl(e(\theta)p^{-it}\bigr)}p\ \ge\ \min\Bigl(1-\cos2\pi\theta,\ \tfrac13-\epsilon\Bigr)\log\log X-O_\epsilon(1).
```

*Proof.* Consider three ranges of $`t`$. If $`\lvert t\rvert\le1/\log X`$, the sum is $`(1-\cos2\pi\theta)\log\log X+O(1)`$. If $`1/\log X\le\lvert t\rvert\le1`$, then $`\sum_{p\le X}p^{-1-it}=-\log\lvert t\rvert-\tfrac{i\pi}2\,\mathrm{sgn}\,t+O(1)`$. If $`\lvert t\rvert\ge1`$, the Vinogradov–Korobov zero-free region makes $`\sum_{z<p\le X}p^{-1-it}=O(1)`$ for $`z=\exp((\log\lvert t\rvert)^{2/3+\epsilon})`$, and $`\sum_{p\le z}1/p\le(\tfrac23+\epsilon)\log\log X+O(1)`$. $`\square`$

Twists by $`\chi\circ U`$ leave all prime values unchanged. We expect twists by Dirichlet characters of conductor $`(\log X)^{o(1)}`$ to behave in the same way, but we have not written out that argument. Thus $`f_\theta`$ is non-pretentious with distance squared $`\asymp\min(\theta^2,1)\,T`$. This grows, but only at the rate $`\log\log N`$.

**Hypothesis E.** There are $`L_N`$ with $`L_N\log\log T/\log T\to\infty`$ and $`A_N`$ with $`A_N/\sqrt{\log\log T}\to\infty`$ such that, uniformly for $`1/L_N\le\lVert\theta\rVert\le1/2`$, $`0<\lvert k\rvert\le A_N\sqrt T`$ and characters $`\chi_1,\chi_2`$ modulo $`2^r`$,

```math
\Bigl\lvert\frac1N\sum_{N\le m<2N}\overline{f_\theta(m)\chi_1(U(m))}\,f_\theta(m+k)\chi_2(U(m+k))\Bigr\rvert=o\Bigl(\frac1{A_N\sqrt T}\Bigr).
```

**Theorem 4 (conditional on K2 and Hypothesis E).** On dyadic windows, $`M_2(b)\to\nu(F)\nu(G)`$ for every fixed $`b\ge0`$ and all $`F,G`$ on the odd residues modulo $`2^r`$.

*Proof (outline).* Choose $`\psi`$ with $`\widehat\psi`$ smooth, equal to $`1`$ on $`[-1,1]`$ and supported in $`[-2,2]`$. Let $`\psi_L(x)=L^{-1}\check\psi(x/L)`$ with $`L=L_N/2`$, and split the lattice delta at $`b`$ as $`\psi_L+(\delta-\psi_L)`$. The $`\psi_L`$ part is a smoothed pair correlation at scale $`L`$. It is handled by the marked extension of Theorem 3 applied to Schwartz kernels; atypical sources are removed using the exponential-moment tail below. In the spectral form (Theorem 1(2)), the $`\delta-\psi_L`$ part involves only frequencies $`\lVert\theta\rVert\ge1/L_N`$. Over $`0<\lvert k\rvert\le A_N\sqrt T`$ it is at most $`2A_N\sqrt T`$ times the bound in Hypothesis E, which is $`o(1)`$. For the remaining gaps $`\lvert k\rvert>A_N\sqrt T`$, split at $`T/2`$ (for large $`N`$). On the intermediate range $`A_N\sqrt T<\lvert k\rvert\le T/2`$, K2 and the Gaussian atom bound of step 3 (valid for $`\lvert x\rvert\le T`$) give total contribution $`O(ue^{-A_N^2/6})+o(1)`$, which tends to zero since $`u=O(\log T)`$ and $`A_N/\sqrt{\log\log T}\to\infty`$. On the far range $`\lvert k\rvert>T/2`$, the exact incidence $`V(m+k)-V(m)=k-b`$ forces $`\max(V(m),V(m+k))\ge \lvert k\rvert/2-O(1)`$; the Shiu/Rankin exponential moment $`N^{-1}\sum_{N\le m<3N}2^{V(m)}\ll(\log N)^2=e^{2T}`$ gives $`\Pr(\max(V(m),V(m+k))\ge r)\ll e^{2T}2^{-r}`$, which summed over $`r\ge c_0 T`$ (taking the split at $`4T`$ rather than $`T/2`$, and using the Schwartz decay of $`\psi_L(k-b-D_k)`$ when $`\lvert k\rvert>4T`$) is $`O(e^{-c_1 T})=o(1)`$. $`\square`$

The factor $`A_N\sqrt T`$ is the whole difficulty. The $`\sqrt{\log\log T}`$ in $`A_N`$ only absorbs the rough-part shift $`u`$, and it is negligible next to $`\sqrt T`$. The gaps that contribute fill a window of width about $`\sqrt{2T}`$, each with unit weight in the spectral sum. So the needed saving is per gap, and summing over gaps costs $`\sqrt T`$. The available inputs compare as follows.

| Input | Averaging | Functions and shifts | Saving | Effect on $`\sum_{\lvert k\rvert\le K}\lvert c_k\rvert`$, $`K\asymp A\sqrt T`$ |
| --- | --- | --- | --- | --- |
| Matomäki–Radziwiłł–Tao, Algebra Number Theory 9 (2015), Thm 1.1 | natural density, average over $`h\le H`$ | $`\lambda`$; non-pretentious analogues | $`\frac{\log\log H}{\log H}+(\log X)^{-1/3000}`$ | $`\asymp K\log\log K/\log K\to\infty`$. **Insufficient.** Any saving that decays only logarithmically in $`H`$ fails. Menon (arXiv:2607.15574) widens a parameter range but keeps this shape. |
| Tao, Forum Math. Pi 4 (2016) | logarithmic | non-pretentious $`g_1`$; fixed $`h`$ | $`o(1)`$, no rate | Gives no bound for a growing number of gaps. **Insufficient.** |
| Helfgott–Radziwiłł, arXiv:2103.06853 | logarithmic (and natural average at almost all scales) | $`\lambda`$; $`h=1`$ | $`O((\log\log x)^{-1/2})`$ | $`O(A)`$ if transplanted. **Exactly borderline**, and proved only for $`\lambda`$. |
| Charamaras–Richter, arXiv:2412.17583 | logarithmic | $`a(\Omega(n))b(\Omega(n+1))`$ | double-logarithmic | Shift $`1`$ only. **Insufficient.** |
| Pilatte, arXiv:2310.19357 | logarithmic | $`\lambda`$; $`h=1`$ | $`(\log x)^{-c}`$ | Would suffice if it held uniformly for $`f_\theta\chi(U)`$ and $`\lvert h\rvert\le K`$. |
| Tao–Teräväinen, arXiv:2512.01739, Thm 3.1 & §4.1 | all scales outside a set of logarithmic density $`\ll\mathcal L^{-c}`$ | non-pretentious $`g_1`$ with $`e^{M}\gg\mathcal L`$; shifts $`O(\mathcal L^c)`$; residues modulo $`W\le\mathcal L^c`$ | $`\mathcal L^{-c}`$ | With $`\mathcal L=e^{M(\theta)/2}`$, Lemma 4.1 and their §4.1 route for Dirichlet twists (since $`f_\theta\chi(U)`$ agrees with $`f_\theta`$ on primes), a cutoff such as $`L_N\asymp T^{1/4}`$ gives saving $`o(T^{-1/2})`$ and covers $`\lvert k\rvert\le A\sqrt T`$. Uniformity across $`\theta`$ and exceptional scales remain to be checked. **Plausibly sufficient at almost all scales.** |

The last row is described from the paper's introduction and §4.1; we have not verified every formal hypothesis of their Theorem 3.1 for our moving family. The same paper proves, verbatim as its Theorem 1.6, $`\Pr(\omega(n)=\omega(n+1))=(1+O((\log\log x)^{-c}))/(2\sqrt{\pi\log\log x})`$ for all $`x`$ outside a set of logarithmic density $`\ll(\log\log X)^{-c}`$. This is the $`\omega`$-analogue of the single term $`k=1`$, $`b=1`$ of $`M_2`$. Their relative error $`T^{-c}`$ on an atom of size $`T^{-1/2}`$ is the strength that summing over $`\sqrt T`$ gaps requires.

**Answer to question (b).** MRT's averaging over $`k`$ cannot give $`M_2(b)`$ at the lattice scale. To do so, $`\sum_{\lvert k\rvert\le K}\lvert c_k\rvert`$ must be $`o(1)`$, a factor $`K`$ beyond "averaged correlation $`o(1)`$". The signed spectral sum is no better. Its Fejér-weighted version over $`\lvert k\rvert<K`$ is the normalized variance of sums of $`e(\theta t(m))`$ over intervals of length $`K`$ minus its diagonal value. So lattice-scale $`M_2`$ is a Good–Churchhouse-type variance statement for intervals of length about $`\sqrt{\log\log N}`$. Matomäki–Radziwiłł bound that variance only by $`K^2`$ times a logarithmic saving. Tao's logarithmic averaging gives no rate. On every dyadic window, the problem is a two-point Elliott estimate with an explicit $`o(T^{-1/2})`$ rate, uniform over $`\lvert k\rvert\le A\sqrt T`$; this is open. At almost all scales, the Pilatte–Tao–Teräväinen technology has the right strength. Verifying its hypotheses for $`f_\theta\chi(U)`$ is the most concrete next step. Unconditionally, Theorem 3 already reaches every scale with $`L\log\log T/\log T\to\infty`$.

## 5. Does the Poisson model describe the limit?

Under the Kubilius heuristic with Elliott-type cancellation, Theorem 1(3) splits $`M_2(b)-\nu(F)\nu(G)`$ into three pieces. All three tend to zero.

* The self-exclusion hole is $`-\nu(F)\nu(G)(4\pi T)^{-1/2}`$ to leading order. It makes the process *sub-Poissonian* at finite $`T`$.
* The local-factor terms oscillate in $`k`$ with Haar mean zero (Theorem 2(3)). In the pretentious range they tend to zero pointwise (Theorem 2(5), Corollary 3.1).
* The non-pretentious terms have a decoupled factor $`\lvert\mathbb E f_\theta\rvert^2\ll(\log N)^{-2(1-\cos2\pi\theta)}`$, by Selberg–Delange. At $`\theta=1/2`$ it is even $`O(e^{-c\sqrt{\log N}})`$, because $`\sum f_{1/2}(n)n^{-s}=\zeta(s)^{-1}H(s)`$ with $`H`$ analytic for $`\mathrm{Re}\,s>1/2`$.

No term tends to a nonzero limit, and nothing pushes the law toward the uniform law. **Answer to question (c): the asymptotic two-source moments match $`Q_D`$.** The local-factor model with Poisson$`(T)`$ displacements quantifies how slow the approach is:

| $`T`$ | $`2.68`$ | $`3.37`$ | $`5`$ | $`10`$ | $`20`$ | $`40`$ |
| --- | --- | --- | --- | --- | --- | --- |
| hole $`e^{-2T}I_0(2T)`$ | $`0.177`$ | $`0.157`$ | $`0.128`$ | $`0.090`$ | $`0.063`$ | $`0.045`$ |
| model $`M_2(0)`$ | $`0.814`$ | $`0.836`$ | $`0.867`$ | $`0.908`$ | $`0.936`$ | $`0.955`$ |

The values $`T=2.68`$ and $`T=3.37`$ correspond to $`N=2^{21}`$ and $`N=2^{43}`$. The relevant spread is in fact $`\mathrm{Var}\,V\approx T-1.4`$, which is $`1.29`$ at $`2^{21}`$, so the actual hole there is larger, $`0.247`$.

**Hypothesis P.** Take any $`D\ge1`$ and nonnegative integers $`r_{d,c}`$, for $`1\le d\le D`$ and $`c`$ an odd residue modulo $`2^D`$. Along a sequence $`N_j\to\infty`$ of dyadic windows,

```math
\mathbb E_{n\in[N_j,2N_j)}\prod_{d,c}\bigl(N_c(n+d)\bigr)_{r_{d,c}}\to\prod_{d,c}\nu(c)^{r_{d,c}}.
```

Here $`N_c(t)`$ counts sources at $`t`$ with $`U\equiv c\bmod2^D`$, $`(x)_r`$ is the falling factorial, and $`\nu(c)=\Pr(U_*\equiv c)`$.

**Theorem 5 (conditional on Hypothesis P).** Along $`N_j`$, the frequency of ones on $`[N_j,2N_j)`$ tends to $`p_*\in[0.492230,0.492685]`$. Every word frequency tends to the corresponding $`Q_\infty`$ cylinder mass. Hence, if Hypothesis P holds along any infinite sequence, $`E`$ is not simply normal in base two.

*Proof.* Convergence of all joint factorial moments to those of independent Poisson variables gives convergence in law of the count vector, since the multivariate Poisson law is determined by its moments. Now $`R_D(n)`$ is a function of $`(N_c(n+d))\bmod2^D`$. So $`d_{\rm TV}(\mathcal L(R_D),Q_D)\to0`$ for each $`D`$. Phase 14's carry inequality $`\lvert f_I-p_*\rvert\le\Delta_D+\epsilon_{D,s}+o(1)`$ then gives $`f_I\to p_*`$. Simple normality would force every dyadic-shell frequency to tend to $`1/2`$ (Phase 14). $`\square`$

Hypothesis P is the natural $`r`$-point extension of Hypothesis E. Theorem 3 proves its mesoscopic version for $`r=2`$. Only a subsequence of scales is needed, so almost-all-scales technology would suffice once it covers $`r`$-point correlations. For $`r\ge3`$ this requires higher-order Elliott estimates for the family $`f_\theta\chi(U)`$. These are available only in special cases; for example, logarithmic Chowla is known for $`\lambda`$ in odd orders and open in even orders $`\ge4`$. Disproving simple normality this way therefore needs new input at order three and beyond.

## 6. What Mira Cult's isolation method can and cannot give

The [audited theorem](../phase13/reviews/erdos-local-limit.md) gives, for each word $`w`$ of length $`k`$ and each $`7/12<a\le1`$, a proportion $`c_{a,w}>0`$ of occurrences on every sufficiently late window with $`N^a\le H\le N`$.

**Lower bounds: quantitative, but doubly exponential and with an ineffective threshold.** The parameters of the proof combine as follows.

1. The planted incidences $`n+j_0=bp`$, with $`b=4^{u_w}m\le N^\theta`$, have density $`\asymp\theta\,4^{-u_w}`$. Here $`u_w\le2^k-1`$ is the integer value of $`w`$.
2. The residual angular error on avoidance is $`O_a((1+\log^2W)/W)`$. It must be smaller than the half-chord $`\sin(\pi/2^{k+1})`$, which forces $`W\asymp_a2^kk^2`$.
3. The avoidance probability is at least $`P_0(b)/2\ge e^{-4W}/2`$.
4. Cauchy–Schwarz with $`\mathbb EF^2\ll\mathbb EF`$ gives a proportion of order $`\theta\,4^{-u_w}e^{-8W}`$.

Together these parameter scalings give a heuristic lower-bound order of $`\exp(-O_a(2^kk^2))`$; making this bound uniform over all words $`w`$ of length $`k`$ would additionally require tracking the explicit $`w`$-dependence of the angular error constants in the audited proof. The $`Q_\infty`$ masses are $`2^{-k}e^{O(k)}`$. The proof needs Perelli–Pintz–Salerno's short-interval Bombieri–Vinogradov estimate with arbitrary logarithmic savings, which rests on Siegel–Walfisz. So the threshold "sufficiently late" is ineffective. The cost doubles in the exponent because the angular cost of a source displaced by $`s`$ is controlled only as $`Z_j/(1+s^2)`$, not as $`2^{-s}`$. The valuation of the unplanted terms is known only up to the unknown large-prime part.

**Upper bounds: only by complementation.** The method gives $`\limsup f(w)\le1-\sum_{w'\ne w}c_{a,w'}`$, a margin of $`\exp(-O(2^kk^2))`$. It gives nothing of order $`2^{-k}`$. Starts with no planted incidence are never examined, and the remainder enters only through one-sided angular costs.

**Asymptotics: blocked by two structural barriers.** For the exact frequency we need

```math
\Pr(w\ \mathrm{at}\ n)=\sum_{\kappa}\Pr(\kappa\ \mathrm{at}\ n)\,\mathbf 1[\kappa\mapsto w].
```

The sum runs over all configurations $`\kappa`$ of sources and marks in the first $`D`$ columns, together with the carry. The indicator records whether $`\kappa`$ produces the word $`w`$. By inclusion–exclusion it is an alternating series in all lattice factorial moments, of which $`M_2`$ is the first.

1. *A single planted incidence versus all starts.* Mira examines only starts with one exact incidence, the term $`\tau(bp)=2\tau(b)`$ planted at the midpoint, with $`b\le N^\theta`$ and $`\theta`$ small. Covering all starts this way would need cofactors $`b`$ up to $`N^{1-\epsilon}`$, which is Elliott–Halberstam territory. Configurations with two or more exactly known sources would need several linear forms to be prime at once, a prime-tuples problem.
2. *Void probability versus the configuration sum.* The bound $`e^{-4W}`$ is the Poisson probability of an empty block of $`2W+1`$ positions, so Mira's estimate is consistent with $`Q_D`$. That estimate is a two-sided Bonferroni comparison for the *small-prime* bank counts (primes up to $`X^c`$), at fixed relative error $`e^{-2R}`$. Making it exact for the true $`V`$ requires the joint law of the large-prime counts of $`n+j_1,\dots,n+j_q`$ at lattice resolution. This is the parity barrier.

The method is the arithmetic analogue of a lower-bound sieve with one prime and upper-bound control of the rest. It can certify positive frequencies; it cannot identify them.

## 7. Finite computations

[`scripts/phase16_erdos_borwein.py`](../../scripts/phase16_erdos_borwein.py) uses the standard library only and runs in about 15 seconds. It sieves $`V`$ and $`U`$ exactly to $`2^{22}+512`$. It certifies the binary digits with integer carry bounds, checks that the column sum $`\sum_tC(t)2^{-t}`$ reproduces them, and reproduces the Phase 14 counts on $`[2^{18},2^{19})`$ ($`67135,63695,63696,67618`$, $`262145`$ arrivals, sign sum $`14434`$). It also tests every vectorised routine against direct loops. Probabilities below are exact rationals printed in decimal. The model columns use floating point. The rows $`s=22,23`$ come from `--smin 20 --smax 23` (about 36 seconds).

**Digits and columns** on the shell of shifts $`[2^s,2^{s+1})`$:

| $`s`$ | $`\mathrm{Var}\,V`$ | $`f(1)`$ | $`f(00)`$ | $`f(11)`$ | $`\mathbb EN(N-1)`$ | $`\mathbb E(-1)^N`$ | $`\prod_v(1-2p_v)`$ | $`\Pr(N=0)`$ | $`\mathrm{Var}\,C`$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 12 | 0.968 | 0.514404 | 0.23438 | 0.26294 | 0.72607 | 0.05127 | 0.04233 | 0.30933 | 9.23 |
| 15 | 1.082 | 0.510254 | 0.24536 | 0.26584 | 0.72131 | 0.04150 | 0.04954 | 0.30688 | 9.77 |
| 18 | 1.192 | 0.500923 | 0.25610 | 0.25794 | 0.73866 | 0.05506 | 0.05435 | 0.31218 | 10.34 |
| 21 | 1.293 | 0.493996 | 0.26054 | 0.24853 | 0.74614 | 0.05525 | 0.05796 | 0.31372 | 10.59 |
| 22 | | 0.493676 | 0.25960 | 0.24696 | 0.74880 | 0.05710 | 0.05900 | 0.31458 | 10.67 |
| 23 | | 0.493723 | 0.25915 | 0.24659 | 0.75090 | 0.05684 | 0.05997 | 0.31496 | 10.71 |
| Poisson | | 0.492435 | | | 1 | 0.13534 | $`\to e^{-2}`$ | 0.36788 | 12.15 |

The model value $`p_*=0.492435`$ is a floating-point evaluation inside the certified interval. The parity of the first column is explained by independent displacements: $`\prod_v(1-2p_v)`$ tracks $`\mathbb E(-1)^N`$ to within $`0.004`$ for $`s\ge16`$. As $`\max p_v\to0`$ this product tends to $`e^{-2}`$. The exact split $`(-1)^{\rm digit}=(-1)^{C(n+1)}(-1)^{c(n+1)}`$, with $`c`$ the carry from deeper columns, gives at $`s=21`$

```math
\mathbb E(-1)^{C}=0.05525,\qquad \mathbb E(-1)^{c}=-0.08046,\qquad \mathbb E(-1)^{\rm digit}=0.01201.
```

The Poisson values are $`0.13534`$, $`0.11149`$ and $`0.01509`$. So the measured one-frequency $`0.4940`$, close to $`p_*`$, arises from a quite different decomposition. It is not evidence for the limit. The shell frequency decreases through $`1/2`$ near $`s=18`$ and is flat at $`0.4937`$ for $`s=21,22,23`$.

**Two-source moments.** In the table, "ind" is $`1-\sum_vp_vp_{v+b}`$ and "loc" is the local-factor model $`\sum_k\int c_s(\theta)\mathcal E_k(\theta)e(-\theta(k-b))\,d\theta`$. Here $`c_s`$ is the shell's decoupled characteristic function, and the product $`\mathcal E_k`$ runs over $`p\le2000`$.

| $`s`$ | hole | $`b=0`$ act / ind / loc | $`b=1`$ act / ind / loc | $`b=2`$ act / ind / loc | $`b=3`$ act / ind / loc | marked $`b=0,1`$ |
| --- | --- | --- | --- | --- | --- | --- |
| 15 | 0.2692 | 0.7213 / 0.7308 / 0.7211 | 0.7813 / 0.7853 / 0.7737 | 0.8794 / 0.8911 / 0.8812 | 0.9654 / 0.9653 / 0.9648 | 0.584, 0.638 |
| 18 | 0.2569 | 0.7387 / 0.7431 / 0.7329 | 0.7825 / 0.7910 / 0.7798 | 0.8771 / 0.8875 / 0.8785 | 0.9617 / 0.9601 / 0.9594 | 0.591, 0.647 |
| 21 | 0.2471 | 0.7461 / 0.7529 / 0.7425 | 0.7865 / 0.7959 / 0.7851 | 0.8780 / 0.8850 / 0.8766 | 0.9560 / 0.9559 / 0.9550 | 0.610, 0.649 |
| 23 | 0.2414 | 0.7509 / 0.7586 / 0.7481 | 0.7899 / 0.7989 / 0.7882 | 0.8767 / 0.8837 / 0.8757 | 0.9540 / 0.9534 / 0.9524 | 0.616, 0.655 |

The marked column uses $`F=G=\mathbf 1[U\equiv3\bmod4]`$, divided by the squared share of such marks among the shell's sources, so its Poisson value is $`1`$. Its larger deficit is the persistent mark factor $`0.778`$ at the dominant gaps $`k=\pm1,\pm2,\pm3`$.

*Decomposition by $`k`$.* On $`[2^{21},2^{22})`$ the gaps that contribute are $`\lvert k\rvert\le7`$. The integers show a parity effect in $`k`$, which the local-factor model reproduces:

| | $`P_{\pm1}(0)`$ | $`P_{\pm3}(0)`$ | $`P_1(1)`$ | even-$`k`$ part of $`M_2(0)`$ | odd-$`k`$ part |
| --- | --- | --- | --- | --- | --- |
| integers | 0.19244 | 0.04872 | 0.22452 | 0.25910 | 0.48705 |
| independent | 0.20406 | 0.04413 | 0.24711 | 0.25289 | 0.50000 |
| local model | 0.18910 | 0.04960 | 0.21872 | | |

The diagonal $`\Pr(V(m+k)=V(m))`$ matches the local model to within $`1`$–$`3\%`$ for $`k\le12`$. The independent value $`0.2471`$ misses the dependence on $`k`$ completely. In the local-factor model, the even-$`k`$ share of $`M_2(0)`$ rises toward $`1/2`$ as $`T\to\infty`$: $`0.396,0.426,0.450,0.477`$ at $`T=2.68,5,10,40`$. This is the asymptotic flattening. The parity correlations $`\mathbb E(-1)^{V(m)+V(m+k)}`$ have size about $`H^{-1/2}`$ for $`s\ge18`$, for example $`\lvert\cdot\rvert\le0.0006`$ at $`s=23`$. That is consistent with square-root cancellation.

**Distance from the Poisson law.** The table gives $`d_{\rm TV}(\mathcal L(R_D(n)),Q_D)`$ on the shell. The floor is the expected distance for an independent sample of the same size drawn from $`Q_D`$ itself:

| $`s`$ | $`D=4`$ (floor) | $`D=8`$ (floor) | $`D=12`$ (floor) |
| --- | --- | --- | --- |
| 15 | 0.0555 (0.0085) | 0.0816 (0.0351) | 0.1661 (0.1405) |
| 18 | 0.0515 (0.0030) | 0.0659 (0.0124) | 0.0916 (0.0497) |
| 21 | 0.0500 (0.0011) | 0.0574 (0.0044) | 0.0667 (0.0176) |
| 23 | 0.0484 (0.0005) | 0.0531 (0.0022) | 0.0584 (0.0088) |

A path of the independent-displacement model resamples $`(V,U)`$ from the joint law on $`[2^{21},2^{22})`$. It gives $`f(1)=0.5022`$, compared with the actual $`0.4940`$, and $`d_{\rm TV}(R_{12}^{\rm actual},R_{12}^{\rm model})=0.0358`$, against a two-sample floor near $`0.025`$. The model is much closer to the integers than $`Q_{12}`$ is, but the local factors still have a measurable effect.

**Crandall's $`2^{43}`$ table.** Crandall reports Mitchell's counts for bits $`1`$ to $`2^{43}`$ (Integers 12 (2012) A23, §6). His table gives $`4359105565638`$ zeros and $`4436987456570`$ ones, a one-frequency of $`0.504427`$, and his non-overlapping base-4 and base-16 tables in §6 reproduce that binary count exactly. Phase 14 quoted the second number as the count of ones. Our certified prefix frequencies run the opposite way. On bits $`1`$ to $`2^{22}`$ the one-frequency is $`0.495743`$, and on bits $`1`$ to $`2^{24}`$ it is $`0.494216`$. Crandall's non-overlapping base-4 frequencies are $`(0.24569,0.25168,0.24808,0.25455)`$ for $`00,01,10,11`$, and his base-8 table makes $`000`$ the rarest block. Ours to $`2^{22}`$ are $`(0.25685,0.24394,0.25087,0.24834)`$, with $`000`$ the most common block, at $`0.135`$. Complementing the bits in Crandall's binary/base-4/base-16 tables simultaneously makes $`0`$ the more common digit, $`00`$ the most common pair and $`000`$ the most common triple, as in our certified data, and gives a one-frequency of $`0.4956`$. Because the base-4 and base-16 counts are internally consistent with the binary table, a bit-complement swap would have to affect all three encodings upstream (not just a single label typo). We have not computed beyond $`2^{24}`$, so this remains a hypothesis to verify against Mitchell's original output.

## 8. Scope and reproduction

The proved statements are Theorem 1, Theorem 2 and Lemma 4.1. Theorem 1(4) uses the Phase 14 local limit, and Lemma 4.1 uses Vinogradov–Korobov. Theorem 3 and Corollary 3.1 are paper deductions from the external input K2. Theorems 4 and 5 are conditional on Hypotheses E and P respectively. Section 6 analyses the parameter dependencies of the audited proof; it is not a new theorem. The Tao–Teräväinen route in Section 4 is a plausible route only, because we did not read the formal statement of their Theorem 3.1. All numbers in Section 7 are finite observations about the stated windows. None of them bears on the limit, since the approach to the Poisson law is at the rate $`(\log\log N)^{-1/2}`$. The literature statements were checked on 25 November 2026 against the arXiv records cited: [MRT](https://arxiv.org/abs/1503.05121), [Tao](https://arxiv.org/abs/1509.05422), [Helfgott–Radziwiłł](https://arxiv.org/abs/2103.06853), [Pilatte](https://arxiv.org/abs/2310.19357), [Charamaras–Richter](https://arxiv.org/abs/2412.17583), [Tao–Teräväinen](https://arxiv.org/abs/2512.01739), [Menon](https://arxiv.org/abs/2607.15574), [Klurman](https://arxiv.org/abs/1603.08453) and [Crandall](https://math.colgate.edu/~integers/m23/m23.pdf).

```sh
python -B scripts/phase16_erdos_borwein.py
python -B scripts/phase16_erdos_borwein.py --smin 20 --smax 23 --model-shells
```
