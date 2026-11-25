# Which finite statistics can certify the Erdős–Borwein digit bias?

Let $`E=\sum_{m\ge1}(2^m-1)^{-1}=\sum_{m\ge1}\tau(m)2^{-m}`$. As in [Phase 14](../phase14/erdos-borwein-frequencies.md) and [Phase 16](../phase16/erdos-borwein-correlations.md), write $`\tau(m)=2^{V(m)}U(m)`$ with $`U(m)`$ odd. The term $`m`$ places the odd mark $`U(m)`$ at binary position $`t(m)=m-V(m)`$. Let $`N(t)`$ be the number of sources at $`t`$ and $`C(t)`$ the sum of their marks. A shift $`n`$ reads the fractional digits $`n+1,n+2,\dots`$, and

```math
e(h2^nE)=e\Bigl(h\sum_{d\ge1}C(n+d)2^{-d}\Bigr)\qquad(h\in\mathbb Z)
```

exactly (Phase 14). For a dyadic window $`I=[N,2N)`$, let $`f_I`$ be the proportion of $`n\in I`$ whose digit $`n+1`$ is $`1`$. Simple normality forces $`f_I\to1/2`$ (Phase 14), and **an infinite sequence of windows with $`\limsup f_I<1/2`$ already disproves it.**

For $`D\ge1`$ put

```math
R_D(n)=\Bigl(\sum_{d=1}^{D}2^{D-d}C(n+d)\Bigr)\bmod 2^D,\qquad Y_D(n)=\sum_{d>D}C(n+d)2^{D-d}.
```

The digit $`n+1`$ is the top bit of $`(R_D+\lfloor Y_D\rfloor)\bmod 2^D`$. **Phase 14 proves unconditionally that $`\mathbb E_IY_D=\mu+o(1)`$**, where $`\mu=\mathbb EU_*`$ and $`U_*`$ is the odd part of $`\tau`$ at a random integer (law $`\nu`$). The comparison law $`Q_\infty`$ makes the columns independent copies of $`J=U_1+\dots+U_K`$, with $`K`$ Poisson of mean one and $`U_i\sim\nu`$. Its first digit is $`1`$ when $`X=\sum_dJ_d2^{-d}\bmod1`$ lies in $`[1/2,1)`$. Write $`Q_D`$ for the law of the packed residue of $`D`$ independent columns with no tail, and $`p_*=Q_\infty(X\ge1/2)`$.

## Summary

Phase 16's Hypothesis P assumes the joint factorial moments of every order. This note asks which **finite** pieces of the Poisson picture would already force $`\limsup f_I<1/2`$, and which provably cannot. The answer is sharp in the number of columns and bracketed elsewhere.

| Question | Answer | Status | § |
| --- | --- | --- | --- |
| Smallest number of columns $`D`$ such that the law of $`R_D`$ together with Phase 14's tail mean certifies the bias | $`D=16`$. One bounded statistic $`\Psi_{16}`$ of $`R_{16}`$ suffices. Every $`D\le15`$ admits an exact countermodel with $`f(1)\ge1/2`$; for $`D\le8`$ such countermodels reach $`f(1)=0.61`$. | Theorem (deduction from Phase 14) plus exact integer certificates | [1](#1-the-minimal-column-truncation) |
| Certified value of $`p_*`$ | $`p_*\in[0.492450290,\,0.492460864]`$, about 40 times narrower than Phase 14. The bias factors as $`\tfrac12 e^{-2}\,\mathbb E(-1)^{c_1}`$ with $`\mathbb E(-1)^{c_1}\in[0.11148,0.11151]`$. | Certified computation | [2](#2-the-comparison-value) |
| Do first and second moments suffice? Do exact one-column laws together with pairwise independence suffice? | No. For every $`k\le4`$, exact joint laws of all $`k`$-column subsets are compatible with $`f(1)=1/2`$ exactly and with $`f(1)>1/2`$. | Explicit countermodels, certified | [3](#3-the-column-hierarchy) |
| Lowest moment order $`r`$ | On any number of columns: $`r\le4`$ fails, through rational laws giving $`f(1)=1/2`$ exactly, while order 5 pins the parity of a column. At $`D=16`$: $`9\le r_{\min}\le92`$ (an explicit order-92 dual witness). At $`D=17`$: $`r_{\min}\ge7`$. | Theorem plus exact certificates | [4](#4-the-moment-hierarchy) |
| Lowest trigonometric degree $`M`$ | Degree $`116`$ certifies. No majorant of degree $`\le110`$ does. Numerically, $`116`$ is exact. Harmonic 1 carries 92% of the bias. | Floating-point certificates with explicit error radii | [5](#5-the-fourier-route) |
| What the minimal criteria demand arithmetically | Lattice-scale $`r`$-point correlations of $`e(\theta V)\chi(U)`$, with $`r\ge9`$ necessary at $`D=16`$. The Fourier route needs more, not less. | Analysis | [6](#6-arithmetic-audit) |
| Crandall's $`2^{43}`$ table | Leading bits, $`e_{10^{10}}`$ and $`e_{10^{20}}`$ agree with ours, and his tables are internally consistent. Whether the 0/1 labels are interchanged **cannot be decided** from data below $`2^{24}`$. | Finite computation | [7](#7-crandalls-table-and-our-digits) |
| Mira Cult's theorem and joint targets | Concrete one-sided and computational targets | Analysis | [8](#8-mira-cults-theorem-and-collaboration-targets) |

The script [`phase17_erdos_borwein_bias.py`](../../scripts/phase17_erdos_borwein_bias.py) uses the standard library only, runs in about 15 seconds and checks every number below with assertions. Comparison-law probabilities are enclosed by integer lower bounds at scale $`2^{64}`$. Every truncation and rounding loss is charged to an explicit error term. Moment laws and dual polynomials are exact fractions. Section 5 alone uses IEEE doubles, with explicit error radii and a further $`10^{-9}`$ safety margin.

## 1. The minimal column truncation

### 1.1 The single sufficient statistic

Let $`\lambda=1/557`$ and define a function of $`R_{16}`$ with values in $`[0,1]`$:

```math
\Psi_{16}=\mathbf 1[R_{16}\ge2^{15}]+\sum_{k=1}^{556}\Bigl(1-\frac{k}{557}\Bigr)\mathbf 1[R_{16}=2^{15}-k].
```

**Theorem 1.** *(a) (Deduction from Phase 14.) Along any sequence of dyadic windows,*

```math
\limsup f_I\le\limsup\mathbb E_I\Psi_{16}\bigl(R_{16}(n)\bigr)+\frac{\mu}{557}.
```

*Hence $`E`$ is not simply normal as soon as $`\limsup\mathbb E_I\Psi_{16}<0.4962723`$ along one sequence. The Poisson model gives $`\mathbb E_{Q_{16}}\Psi_{16}\le0.4960081`$, a margin of $`2.6\times10^{-4}`$. In particular, $`\mathcal L(R_D)\to Q_D`$ for any one $`D\ge16`$ implies $`\limsup f_I<1/2`$.*

*(b) (Sharpness.) For every $`D\le15`$ there is a law of a column process in which the first $`D`$ columns are independent copies of $`J`$, so that $`R_D\sim Q_D`$ exactly, every later column has mean at most $`\mu`$, $`\mathbb EY_D\le\mu`$, and $`f(1)\ge1/2`$. For $`D=15`$ one gets $`f(1)\ge0.502823`$.*

*Proof of (a).* Write $`c=\lfloor Y_D\rfloor\ge0`$, $`\mathbb E_Ic\le\mu+o(1)`$. A residue $`r<2^{D-1}`$ becomes a $`1`$ only if $`c\ge k_r=2^{D-1}-r`$; a residue $`r\ge2^{D-1}`$ can only lose its $`1`$. Hence

```math
\mathbf 1[\text{digit}=1]\le\mathbf 1[R_D\ge2^{D-1}]+\lambda c+\sum_{r<2^{D-1}}(1-\lambda k_r)^+\mathbf 1[R_D=r]
```

pointwise for every $`\lambda\ge0`$. Indeed, if a lower residue is lifted then $`\lambda c\ge\lambda k_r`$. Averaging gives (a), and $`\lambda=1/557`$ is the optimal dual variable of the fractional knapsack below. $`\square`$

This is the linear-programming dual of the exact problem "maximise $`f(1)`$ over joint laws of $`(R_D,c)`$ with $`R_D\sim Q_D`$, $`c\ge0`$ integral and $`\mathbb Ec\le\mu`$". The primal value is $`Q_D(R_D\ge2^{D-1})`$ plus a fractional knapsack: cell $`2^{D-1}-k`$ costs $`k`$ per unit of moved mass, and the budget is $`\mu`$.

*Proof of (b).* Fill the knapsack greedily, with a randomised last cell. On a moved cell put $`k_r`$ sources of mark 1 into **every** column beyond $`D`$, so that $`Y_D=k_r`$ exactly and the residue lands on $`2^{D-1}`$. Leave the tail empty elsewhere. Then $`\mathbb EY_D=\mathbb EC(t)\le\mu`$ for every tail column. The resulting law also serves every $`D'<D`$: columns $`1,\dots,D`$ stay independent, and $`\mathbb EY_{D-1}=(\mu+\mathbb EY_D)/2\le\mu`$. $`\square`$

*Remark (the full one-source information).* Phase 14 also fixes the **marked** first moment $`\nu(F)`$ of every tail column. The countermodel can be adjusted to respect these as well. Distribute marks over the moved cells, whose required carries run into the hundreds ($`k^*=389`$ at $`D=15`$) and leave ample room. Put the residual mark mass above $`k^*=389`$ (total mass $`\Pr(U_*>389)\approx3.7\times10^{-7}`$; marks above $`2^{D-2}`$ can flip the top bit, with negligible mass compared to the $`2.8\times10^{-3}`$ margin) on residues in $`[2^{D-1},3\cdot2^{D-2})`$. We have not certified this refinement in the script; the $`D=15`$ margin leaves ample room for it.

### 1.2 Certified values

All entries are certified and **outward-rounded** (`cert` rounded up, `cmod` rounded down). "cert" is an upper bound for the LP value, using budget $`\mu\le2.0763285`$. "cmod" is the value of an explicit countermodel, using budget $`\mu\ge2.0762592`$.

| $`D`$ | $`Q_D(\text{top bit }1)\ge`$ | cert $`\le`$ | cmod $`\ge`$ | critical cost $`k^*`$ |
| --- | --- | --- | --- | --- |
| 4 | 0.486398 | 0.958104 | 0.958093 | 8 |
| 6 | 0.491001 | 0.733276 | 0.733270 | 16 |
| 8 | 0.492113 | 0.614119 | 0.614114 | 32 |
| 10 | 0.492374 | 0.553082 | 0.553078 | 66 |
| 12 | 0.492435 | 0.522477 | 0.521878 | 129 |
| 14 | 0.492449 | 0.509093 | 0.505523 | 257 |
| **15** | 0.492451 | 0.502828 | **0.502823** | 389 |
| **16** | 0.492452 | **0.499736** | 0.499732 | 557 |
| 17 | 0.492453 | 0.498500 | 0.496678 | 513 |
| 20 | 0.492453 | 0.494499 | 0.493964 | 2049 |
| 23 | 0.492453 | 0.493205 | 0.492945 | 4097 |

The rows $`D=15,16`$ use exact cell masses for $`k\le1024`$. Other rows use exact cells for $`k\le2^7`$ or $`2^8`$ and dyadic blocks beyond, which explains the small cert–cmod gaps. For $`D\ge24`$, Phase 14's carry bound with $`s=664`$ gives $`p_*+(s+7)(3/5)^{24}+\mu/s\le0.49877`$. With the table, **every $`D\ge16`$ certifies and every $`D\le15`$ fails.** The cell masses come from a trie over the ten least significant columns, in which one integer convolution per node yields both children. They are completed by a backward transfer vector over the prescribed top digits.

**The answer to C1.2(a).** Phase 14's $`D=32`$ shrinks to $`D=16`$, and no further. Its $`\mu\le5/2`$ would not reach $`D=16`$, because the knapsack loss grows like $`\sqrt{2\mu2^{-D}}`$. The shift to $`D=16`$ comes from the exact knapsack replacing Phase 14's Markov-type step and from the certified $`\mu=2.07633`$. Truncations $`D=3,\dots,8`$ are hopeless: the countermodel moves between $`0.12`$ ($`D=8`$) and $`0.47`$ ($`D=4`$) of probability across $`1/2`$.

*Numerical remark (not certified).* Suppose one assumes the law of the integer column vector $`(C(n+1),\dots,C(n+D))`$ instead of residues. By shift invariance this also fixes every $`D`$-block of the tail. Coupling the model's tail carry law adversarially with $`R_D`$ then gives $`f(1)\le0.4969`$ at $`D=12`$ and $`0.5002`$ at $`D=11`$. So richer tail information buys about four columns. For non-normality instead of simple non-normality, the overlapping word $`11`$ has the largest model deviation among words of length at most 4, namely $`-0.0109`$. The same knapsack certifies $`f(11)<1/4`$ from $`D=15`$, with margin $`4.5\times10^{-4}`$ (floating point).

## 2. The comparison value

Under $`Q_\infty`$ the first column is independent of the carry $`c_1=\lfloor\sum_{d\ge2}J_d2^{1-d}\rfloor`$. Every mark is odd, so $`J\equiv K\pmod2`$ and $`\mathbb E(-1)^J=e^{-2}`$ exactly. Therefore

```math
p_*=\frac12-\frac12\,e^{-2}\,\mathbb E(-1)^{c_1}.
```

The bias is the product of an infinite-order Poisson parity statistic, $`e^{-2}=0.1353`$, and a carry-parity bias. A 48-column certified dynamic programme gives

```math
p_*\in[0.492450290,\ 0.492460864],\qquad \mathbb E(-1)^{c_1}\in[0.111481733,\ 0.111502881].
```

The missing mass of the certified mark law is at most $`2.21\times10^{-7}`$. Primes up to $`2^{12}`$ are convolved individually. Primes in $`(2^{12},2^{22}]`$ enter as one combined factor: either no exponent reaches 2, or exactly one equals 2. Primes above $`2^{22}`$ are charged $`\sum_{n>2^{22}\text{ odd}}n^{-2}`$. The depth-48 truncation is charged Phase 14's cylinder error $`2(\mu+1)p_0^{48}`$, with $`p_0=(1+e^{-2})/2`$. The interval sits inside Phase 14's $`[0.492230,0.492685]`$. The gap $`1/2-p_*`$ lies in $`[0.0075391,0.0075498]`$.

## 3. The column hierarchy

**Theorem 3.** *Let $`K\in\{2,3,4,5\}`$. The script lists explicit sets $`S_1,\dots,S_K\subset\{0,\dots,47\}`$. Put $`\pi_i=Q_\infty(J\in S_i)`$ and $`g_i=(\mathbf 1_{S_i}(C_i)-\pi_i)/\max(\pi_i,1-\pi_i)`$. For $`|\varepsilon|\le1`$,*

```math
dQ^\varepsilon=\Bigl(1+\varepsilon\prod_{i=1}^Kg_i(C_i)\Bigr)\,dQ_\infty
```

*is a probability law on marked column processes with these properties:*

1. *Every set of columns that omits at least one of $`1,\dots,K`$ keeps exactly its $`Q_\infty`$ joint law, marks included. In particular every $`(K-1)`$-column law and every window of $`K-1`$ consecutive columns is exact.*
2. *$`f^{\varepsilon}(1)=p_*+\varepsilon s_K`$, with certified lower bounds*

| $`K`$ | exact laws preserved | $`s_K\ge`$ |
| --- | --- | --- |
| 2 | all one-column laws | 0.102248 |
| 3 | all two-column laws (pairwise independence, exact marginals) | 0.055920 |
| 4 | all three-column laws | 0.038866 |
| 5 | all four-column laws | 0.015222 |

*Since $`s_K>1/2-p_*`$ in every row, some $`\varepsilon\in(0,1)`$ gives $`f(1)=1/2`$ exactly, and $`\varepsilon=1`$ gives $`f(1)>1/2`$.*

*Proof.* $`|g_i|\le1`$ gives positivity. Under $`Q_\infty`$ the columns are independent and each $`g_i`$ has mean zero. So integrating out any one perturbed column kills the perturbation, which proves item 1. Write $`s_K=\mathbb E_{Q_\infty}[\prod g_i\,\mathbf 1(\text{digit}=1)]`$. It expands into $`2^K`$ probabilities of the events $`\{C_i\in S_i\ (i\in T),\ \text{digit}=1\}`$, each certified by the dynamic programme. Interval arithmetic over $`\pi_i`$ and these events gives the table. $`\square`$

**Answers to C1.1.** First and second moments of the column totals, or of the marked counts, cannot certify a bias in either direction. Neither can exact marginal laws with all pairwise covariances, nor exact one-column laws with pairwise independence. In each case $`f(1)=1/2`$ and $`f(1)>1/2`$ remain attainable. Section 4.2 gives a fully rational finite countermodel with the same conclusion.

Alternating optimisation with $`\pm1`$-valued factors (numerical, a local optimum) gives at most $`s_6\approx0.0072<0.00754`$. Product perturbations therefore stop at four-column laws. Whether exact five-column laws certify is open. Exact sixteen-column laws do certify, by Theorem 1.

## 4. The moment hierarchy

### 4.1 Parity of a count with Poisson factorial moments

**Theorem 4.** *Let $`r\ge1`$ be odd. Over all laws of $`N`$ on $`\{0,1,2,\dots\}`$ with $`\mathbb E(N)_k=1`$ for $`1\le k\le r`$,*

```math
\min\ \mathbb E(-1)^N=e_r:=\sum_{k=0}^{r}\frac{(-2)^k}{k!}.
```

*The values are $`e_1=-1`$, $`e_3=-\tfrac13`$, $`e_5=\tfrac1{15}`$, $`e_7=\tfrac{41}{315}`$, $`e_9=\tfrac{383}{2835}`$ and $`e_{11}=\tfrac{21101}{155925}`$, increasing to $`e^{-2}`$. For even $`r`$, $`e_{r-1}`$ is a lower bound that is never attained, and for even $`r\le10`$ it is the infimum. In particular **$`\mathbb E(-1)^N>0`$ is forced exactly when $`r\ge5`$.***

*Proof.* (Primal.) The law $`w_n=\frac1{n!}\sum_{j=0}^{r-n}\frac{(-1)^j}{j!}`$ on $`\{0,\dots,r\}`$ is nonnegative, since alternating partial sums of $`e^{-1}`$ are nonnegative. By the Jordan inversion formula its binomial moments are $`1/k!`$ for $`k\le r`$. Since $`(-1)^n=\sum_k(-2)^k\binom nk`$, it has $`\mathbb E(-1)^N=e_r`$.

(Dual.) Let $`q_r(n)=\sum_{k\le r}(-2)^k\binom nk`$. It has degree $`r`$, so $`\mathbb Eq_r(N)=e_r`$ for every admissible law. Taylor's formula for $`(1+x)^n`$ at $`x=-2`$, with the substitution $`t=s-1`$ and $`r`$ odd, gives

```math
(-1)^n-q_r(n)=\frac{(n)_{r+1}}{r!}\int_{-1}^{1}(1+s)^r\,s^{\,n-r-1}\,ds\ \ge0 .
```

If $`n-r-1`$ is even the integrand is nonnegative. If it is odd, pair $`s`$ with $`-s`$; the integral becomes $`\int_0^1s^{n-r-1}[(1+s)^r-(1-s)^r]\,ds\ge0`$. Thus $`q_r\le(-1)^n`$ on $`\mathbb Z_{\ge0}`$, with equality exactly on $`\{0,\dots,r\}`$. (The pointwise integer inequality $`q_r(n)\le(-1)^n`$ is also kernel-verified in [`Phase17DiscrepancyBounds.lean`](../../NormalityChecker/Phase17DiscrepancyBounds.lean) via a two-step Pascal induction, `parity_bonferroni_dual_le`, together with Theorem 1(a)'s carry-knapsack dual `carry_knapsack_le`.) For even $`r`$, the order-$`(r-1)`$ bound applies. The laws on $`\{0,\dots,r-1\}\cup\{L\}`$ with the prescribed moments have $`w_L=1/(L)_r>0`$, $`w_{r-2}=1/((r-2)!(L-r+2))>0`$, and $`w_n\to w_n^{(r-1)}>0`$ for $`n\ne r-2`$, so they are nonnegative for all large $`L`$ and their parity tends to $`e_{r-1}`$ at rate $`O(1/L)`$ (verified in exact arithmetic in the script for even $`r\le10`$ at $`L=50{,}000`$, as well as $`(4,12),(6,40),(8,400)`$; for $`r=8`$ and $`L=400`$ the parity is $`0.1302228`$). Equality would need support in $`\{0,\dots,r-1\}`$, which contradicts $`\mathbb E(N)_r=1`$. $`\square`$

The dual polynomial is exactly the truncated binomial expansion of $`(1-2)^n`$. This is a parity analogue of the Bonferroni inequalities.

### 4.2 Order $`r\le4`$ fails on every number of columns

**Corollary 4.1.** *The rational laws*

```math
\rho_3^0=\Bigl\{0:\tfrac{13}{36},\ 1:\tfrac{19}{48},\ 2:\tfrac{5}{36},\ 3:\tfrac{7}{72},\ 5:\tfrac1{144}\Bigr\}=\tfrac16L_3+\tfrac56L_5,\qquad \rho_4^0=\tfrac{99}{404}L_4^{(12)}+\tfrac{305}{404}L_5
```

*satisfy $`\mathbb E(N)_k=1`$ for $`k\le3`$ (respectively $`k\le4`$) and $`\mathbb E(-1)^N=0`$. Here $`L_r`$ is the primal law above, and $`L_4^{(12)}`$, supported on $`\{0,1,2,3,12\}`$, has parity $`-61/297`$. Give column 1 the count law $`\rho_r^0`$ with marks i.i.d. $`\nu`$, and keep every other column compound Poisson, all independent. Then every mixed factorial moment of total order at most $`r`$ of the marked counts equals its Poisson value, on any number of columns. Yet*

```math
f(1)=\tfrac12-\tfrac12\,\mathbb E(-1)^{N_1}\,\mathbb E(-1)^{c_1}=\tfrac12\quad\text{exactly}.
```

*With $`L_3`$ itself, $`f(1)\ge0.51858`$.*

For the moments, i.i.d. marks give $`\mathbb E\prod_c(N_{1,c})_{r_c}=\mathbb E(N_1)_{\sum r_c}\prod_c\nu(c)^{r_c}`$. These are fully explicit finite countermodels with Poisson means, Poisson variances, zero covariances and a binary one-frequency of exactly $`1/2`$, or above $`1/2`$. **This answers C1.1 and the first half of C1.2(c): $`r=2`$ fails, $`r=3`$ fails, $`r=4`$ fails.**

### 4.3 At the minimal truncation the order must be higher

At $`D=16`$ the knapsack margin is only $`2.6\times10^{-4}`$. A column-1 law that lowers the parity from $`e^{-2}`$ to $`e_r`$ shifts $`Q_{16}(\text{top bit }1)`$ by about $`\tfrac12(e^{-2}-e_r)\cdot0.111`$, which is enough to break it.

**Theorem 4.2 (combined attack).** *Use column-1 count law $`L_7`$, or the order-8 law with far point 400, for $`D=16`$. Use $`L_5`$, or the order-6 law with far point 40, for $`D=17`$. Keep columns $`2,\dots,D`$ compound Poisson, and couple the tail to $`R_D`$ by the knapsack with budget $`\mu`$. These laws match every mixed factorial moment of order $`\le r`$ on the $`D`$ columns, satisfy $`\mathbb EY_D\le\mu`$, and have certified*

| $`D`$ | $`r`$ | $`\mathbb E(-1)^{N_1}`$ | $`f(1)\ge`$ |
| --- | --- | --- | --- |
| 16 | 7 | 41/315 | 0.5000161 |
| 16 | 8 | 0.1302228 | 0.5000126 |
| 17 | 5 | 1/15 | 0.5004691 |
| 17 | 6 | 0.0737841 | 0.5000762 |

*The same family is exhausted at $`(16,9)`$, where $`f(1)\le0.499749`$, and at $`(17,7)`$, where $`f(1)\le0.498786`$.*

The countermodel at $`(D,r)`$ also serves at every $`(D',r)`$ with $`D'<D`$, as in Theorem 1(b).

### 4.4 An explicit dual witness

**Theorem 4.3.** *Assume that, along a sequence of dyadic windows, every mixed factorial moment of total order at most $`92`$ of the marked counts $`N_{d,c}(n+d)`$ converges to its Poisson value. Here $`1\le d\le16`$ and $`c`$ runs over the odd residues modulo $`2^d`$; this is Phase 16's Hypothesis P truncated at order 92 on 16 columns. Then $`\limsup f_I\le0.499856<1/2`$.*

*Proof.* Let $`\vec N`$ be the count vector and $`K=|\vec N|`$. For a target configuration $`\vec n`$ and even $`t\ge0`$, let $`B_t(\vec n)`$ be the truncation at total degree $`|\vec n|+t`$ of Jordan's formula $`\mathbf 1[\vec N=\vec n]=\sum_{\vec k\ge\vec n}(-1)^{|\vec k-\vec n|}\binom{\vec k}{\vec n}\prod_i\binom{N_i}{k_i}`$. Vandermonde's identity collapses the inner sums to $`\sum_{j\le t}(-1)^j\binom Mj=(-1)^t\binom{M-1}{t}`$ with $`M=K-|\vec n|`$. Therefore, pointwise,

```math
B_t(\vec n)=\mathbf 1[\vec N=\vec n]+\prod_i\binom{N_i}{n_i}\binom{M-1}{t}\mathbf 1[M\ge1]\ \ge\ \mathbf 1[\vec N=\vec n].
```

So $`\Phi=\sum_{|\vec n|<92}\Psi_{16}(\vec n)B_{t(\vec n)}(\vec n)+\binom{K}{92}`$ is a polynomial of degree $`\le92`$, with $`t(\vec n)`$ the largest even integer at most $`92-|\vec n|`$, and $`\Phi\ge\Psi_{16}`$ pointwise. Its Poisson mean exceeds $`\mathbb E_{Q_{16}}\Psi_{16}`$ by at most

```math
\mathbb E\sum_{j<92}\binom Kj\binom{K-j-1}{t_j}+\frac{16^{92}}{92!}\le1.197\times10^{-4},\qquad K\sim\mathrm{Poisson}(16).
```

This is evaluated exactly up to $`K=360`$, with a $`4^K`$ tail bound beyond. Add $`\mu/557`$ (Theorem 1). $`\square`$

**Answer to C1.2(c).** Every dual witness built from the law of the first $`D`$ columns plus the tail mean needs $`D\ge16`$, whatever the order (Theorem 1(b)). At $`D=16`$ it needs order $`r\ge9`$ (Theorem 4.2). On any $`D`$ it needs $`r\ge5`$ (Corollary 4.1). A certified witness exists at $`(D,r)=(16,92)`$, so $`9\le r_{\min}(16)\le92`$. Bonferroni is wasteful here: its excess comes only from $`K\ge r`$, weighted like a Poisson variable of mean $`2\Lambda`$. Closing the bracket would need a genuinely multivariate moment LP over the 16-column count vector, which we have not attempted.

## 5. The Fourier route

### 5.1 Exact structure

Let $`\varphi(m)=\mathbb E_{Q_\infty}e(mX)`$ and $`A_I(m)=\mathbb E_{n\in I}e(m2^nE)`$.

**Proposition 5.1.**

1. $`\varphi(m)=\exp\kappa(m)`$ with $`\kappa(m)=\sum_{d\ge1}(\hat\nu(m/2^d)-1)`$. Stationarity gives $`\varphi(2m)=\varphi(m)`$. For the orbit, $`A_I(2m)=A_{I+1}(m)=A_I(m)+O(1/N)`$. **Only odd harmonics are independent statistics.**
2. For every atomless law of $`X`$, $`\Pr(X\ge1/2)=\tfrac12-\tfrac2\pi\sum_{m\text{ odd}}\operatorname{Im}\varphi(m)/m`$. The symmetric partial sums of the sawtooth series are uniformly bounded and converge off the endpoints.
3. The $`X`$-law of $`Q_\infty`$ is **singular continuous**. It is invariant and ergodic under doubling, being a factor of a Bernoulli shift, and it differs from Lebesgue measure since $`\varphi(1)\ne0`$. It is atomless by Phase 14. In particular $`\varphi(2^k)=\varphi(1)\not\to0`$, so the conjectured limiting digit law has no density.

Certified values, with radii below $`10^{-7}`$:

| $`m`$ | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $`\operatorname{Re}\varphi`$ | −0.0107990 | −0.0013615 | −0.0007238 | −0.0000018 | −0.0004260 | −0.0001772 | −0.0000917 | +0.0002019 |
| $`\operatorname{Im}\varphi`$ | +0.0109595 | +0.0018132 | +0.0006711 | +0.0006693 | +0.0000226 | +0.0002077 | +0.0001584 | +0.0002982 |
| $`\lvert\varphi\rvert`$ | 0.0153860 | 0.0022675 | 0.0009871 | 0.0006693 | 0.0004266 | 0.0002730 | 0.0001830 | 0.0003601 |

The even harmonics up to 16 repeat these values. For odd $`m`$, $`\kappa(m)`$ always contains the exact terms $`-2`$ (from $`d=1`$) and $`-1+i(\cdot)`$ (from $`d=2`$); for example $`\kappa(1)=-4.17429+2.34882i`$. The bias series has partial sums $`0.493023`$ ($`m=1`$), $`0.492638`$ ($`m\le3`$), $`0.492458`$ ($`m\le15`$) and $`0.492453`$ ($`m\le115`$). **Harmonic 1 alone carries $`92.4\%`$ of the bias:** $`(2/\pi)\operatorname{Im}\varphi(1)=0.006977`$ against $`1/2-p_*=0.007545`$.

### 5.2 The minimal degree

**Theorem 5.2.** *(a) The Selberg–Vaaler majorant $`S^+_{116}\ge\mathbf 1_{[1/2,1)}`$ has $`\mathbb E_{Q_\infty}S^+_{116}(X)\le0.4999592`$. If $`A_I(m)\to\varphi(m)`$ for the 58 odd $`m\le115`$ along a sequence of windows, then $`\limsup f_I\le0.49996<1/2`$.*

*(b) There is a positive measure $`\rho`$ with $`\hat\rho(m)=\varphi(m)`$ for every $`|m|\le110`$ and $`\rho([1/2,1])\ge0.500192`$. Hence every trigonometric polynomial $`P\ge\mathbf 1_{[1/2,1)}`$ of degree at most $`110`$ has $`\sum_m\hat P(m)\varphi(m)\ge0.500192`$. **No certificate of degree $`\le110`$ exists.***

*Proof.* (a) Vaaler's approximation $`\psi^*_N`$ to the sawtooth satisfies $`\lvert\psi-\psi^*_N\rvert\le K_N/(2N+2)`$, with $`K_N`$ the Fejér kernel. So $`S^+_N(x)=\tfrac12+\psi^*_N(x-1)-\psi^*_N(x-\tfrac12)+\tfrac{1}{2N+2}\bigl(K_N(x-1)+K_N(x-\tfrac12)\bigr)\ge\mathbf 1_{[1/2,1)}`$ (Vaaler, *Bull. AMS* 12 (1985); Montgomery, *Ten Lectures*, Ch. 1). Its coefficients are $`\tfrac{i}{\pi m}\hat J(\tfrac{|m|}{N+1})`$ for odd $`m`$ and $`\tfrac{1}{N+1}(1-\tfrac{|m|}{N+1})`$ for even $`m\ne0`$. Since $`f_I=\mathbb E_I\mathbf 1_{[1/2,1)}(2^nE)\le\sum_m\hat S^+(m)A_I(m)`$, the bound follows from the certified $`\varphi`$.

(b) A grid linear programme on $`8192`$ points gives a discrete measure $`\rho_0`$ with 221 atoms. It matches $`\varphi(m)`$ for $`|m|\le110`$ to within $`4.3\times10^{-13}`$ and has $`\rho_0([1/2,1])=0.5002921`$; the script embeds it. Put $`\rho=(1-t)\rho_0+t\rho_\psi`$ with $`t=2\times10^{-4}`$. Here $`\rho_\psi`$ is the $`221`$-node equally spaced quadrature measure whose coefficients are $`\psi(m)=(\varphi(m)-(1-t)\hat\rho_0(m))/t`$. Then $`\hat\rho=\varphi`$ exactly for $`|m|\le110`$, and the weights of $`\rho_\psi`$ are at least $`3.2\times10^{-3}>0`$. Finally $`\rho([1/2,1])\ge(1-t)\rho_0([1/2,1])`$. Any continuous $`P\ge\mathbf 1_{[1/2,1)}`$ is at least $`1`$ on $`[1/2,1]`$, so $`\mathbb E_{Q_\infty}P=\mathbb E_\rho P\ge\rho([1/2,1])`$. $`\square`$

Selberg values for other degrees: $`0.99651`$ ($`M=1`$), $`0.82580`$ ($`M=2`$), $`0.74138`$ ($`M=3`$), $`0.61459`$ ($`M=7`$), $`0.55210`$ ($`M=15`$), $`0.52149`$ ($`M=31`$), $`0.50656`$ ($`M=63`$) and $`0.500026`$ ($`M=115`$). The optimal value from the grid LP is $`0.501093`$, $`0.500292`$, $`0.500150`$, $`0.500012`$, $`0.500009`$ and $`0.499879`$ at $`M=100,110,112,114,115,116`$ (numerical). So the exact minimal degree is $`116`$: proved for $`\le110`$ and for $`116`$, numerical in $`111`$ to $`115`$. The margin at 116 is $`4.1\times10^{-5}`$.

**Answer to C1.2(b).** $`M=1,2,3`$ fail by enormous margins. The obstruction is the majorant excess, about $`1/(M+1)`$, set against a bias of $`0.0075`$, because $`Q_\infty`$ is close to uniform in low harmonics. The minimal degree is $`116`$, that is 58 odd harmonics.

## 6. Arithmetic audit

### 6.1 What Theorem 1 asks of the integers

Source $`m`$ enters column $`d`$ of shift $`n`$ exactly when $`m-V(m)=n+d`$. So $`R_{16}(n)`$ is a function of $`(V(n+j),\,U(n+j)\bmod2^{16})`$ over raw offsets $`j=d+V`$. Typically $`j\in T\pm O(\sqrt T)`$ with $`T=\log\log N`$. **The single needed inequality, $`\limsup\mathbb E_I\Psi_{16}<0.49627`$, is a lattice-resolution statement about the joint law of the 2-adic valuation and odd part of $`\tau`$ at about $`T`$ consecutive integers.** It must hold only along some infinite sequence of dyadic shells.

Through Theorem 4.3 it suffices to know all mixed factorial moments of order at most $`92`$. Each is a sum over $`r`$-tuples of distinct sources with prescribed displaced positions and mark classes. Fourier inversion, $`\mathbf 1[V=v]=\int_0^1e(\theta(V-v))\,d\theta`$, together with characters of $`(\mathbb Z/2^{16}\mathbb Z)^\times`$, turns each into an $`r`$-fold integral of $`r`$-point correlations

```math
\frac1N\sum_{N\le k<2N}\prod_{i=1}^{r}f_{\theta_i}(k+h_i)\,\chi_i(U(k+h_i)),\qquad f_\theta=e(\theta V),\quad h_i\le T+A\sqrt T .
```

The relative shifts $`h_i-h_1`$ fill windows of length about $`\sqrt T`$. Phase 16 showed that for $`r=2`$ one needs a saving $`o((A\sqrt T)^{-1})`$ uniformly in the shift (Hypothesis E). The same bookkeeping for $`r`$ points needs $`o((A\sqrt T)^{-(r-1)})`$ on the non-pretentious part, uniformly over $`r-1`$ relative shifts, $`\theta`$ away from the pretentious range, and characters modulo $`2^{16}`$. **Theorem 4.2 makes $`r\ge9`$ unavoidable at $`D=16`$; Corollary 4.1 makes $`r\ge5`$ unavoidable on any number of columns.**

### 6.2 The Fourier route does not lower the order

Exactly, $`A_I(m)=\mathbb E_{n\in I}\prod_{j\ge1}e\bigl(m\tau(n+j)2^{-j}\bigr)`$: a correlation of unboundedly many shifted functions of $`\tau`$. For odd $`m`$, the factor at displaced level $`d=1`$ is $`(-1)^{N(n+1)}`$. So every odd harmonic contains the parity of the number of sources at one position. By Theorem 4, no information of order $`\le4`$ controls that parity, and order 5 only bounds it below by $`1/15`$, against the true $`e^{-2}`$. In the expansion $`\mathbb E\prod(1+f)=\sum_k\frac1{k!}\int f^{\otimes k}d\rho_k`$ we have $`\lvert f\rvert=2`$ at $`d=1`$ and $`\int\lvert f\rvert\,d\rho_1\approx5.91`$. Pinning $`\varphi(1)\approx0.0154`$ to the needed absolute accuracy of about $`10^{-5}`$ needs correlations of order about 20 even in the Poisson case.

Quantitatively, truncating $`e(mX)`$ to $`D`$ columns costs $`2\pi m\mu2^{-D}`$. The Selberg weights up to $`116`$ then need about $`D\approx25`$ columns, and Bonferroni on $`\Lambda=24`$ to $`27`$ needs order about $`140`$ to $`155`$ at the margin $`4\times10^{-5}`$ (estimate). **The Fourier route is strictly more demanding than Theorem 1.** It needs 58 harmonics, each an infinite-order statistic, more columns and higher order. It runs into the same higher-order Elliott barrier: the probability generating functional of the marked point process at an $`O(1)`$ test function.

One advantage survives. By Weyl's criterion and Wall's theorem, $`\limsup\lvert A_I(1)\rvert>0`$ along any sequence of windows already proves that $`E`$ is **not normal**, with no precision requirement. The model predicts $`\lvert\varphi(1)\rvert=0.0154`$. A lower bound for a generating functional whose main term is $`1.5\%`$ of its trivial size is, however, no easier.

### 6.3 Ledger

| Input | Order reached | Scale | Rate | Enough for |
| --- | --- | --- | --- | --- |
| Phase 14 local limit (Selberg–Delange) | 1-point | lattice | $`O(T^{-3/2})`$ | the first moments, including the tail mean used in Theorem 1 |
| Phase 16 Theorem 3 (from K2) | 2-point | mesoscopic, $`L\log\log T/\log T\to\infty`$ | $`o(1)`$ | not lattice |
| Hypothesis E (Phase 16 §4) | 2-point | lattice | $`o(T^{-1/2})`$ per gap | $`M_2(b)`$ only; Theorem 3 shows two-column laws are insufficient |
| Logarithmic Chowla for $`\lambda`$ (odd orders), as recorded in Phase 16 §5 | odd $`r`$ for $`\lambda`$ | fixed shifts | none | not $`f_\theta\chi(U)`$, not uniform in $`\sqrt T`$ shifts, no rate |
| Needed by Theorem 1 | $`9\le r\le92`$ | lattice, shifts $`\lesssim\sqrt T`$ | saving $`o(T^{-(r-1)/2})`$ | along one infinite sequence of shells |

Only a subsequence of scales is needed. So technology of the Tao–Teräväinen almost-all-scales type (arXiv:2512.01739, Phase 16 §4) would suffice once it covers $`r`$-point correlations with polynomial savings in $`T`$. We know of no such result for $`r\ge3`$. The gap between current methods and the weakest criterion found here is therefore the passage from $`r=2`$ to $`r\ge9`$ at lattice resolution. No literature claims beyond Phase 16's checked ledger are made here.

## 7. Crandall's table and our digits

Crandall, *The googol-th bit of the Erdős–Borwein constant*, Integers 12 (2012) A23, was read from the journal PDF, text extracted with `pdftotext`.

**Verified agreements.**

1. Our certified digits start $`1.1001101101010000010111111\ldots`$, **identical to Crandall's abstract**. They are recomputed here from an independent $`\tau`$ table up to $`2^{20}`$. The first 512 bits also agree with a direct evaluation of $`\sum1/(2^m-1)`$ with certified carries. Hex: $`1.9b505f9e43f22437f372c52812463bc1\ldots`$. Decimal: $`1.60669515241529176378\ldots`$.
2. Crandall's Table 1 gives $`e_{10^{10}}=0`$ and $`e_{10^{20}}=0`$. Our remote-bit computation agrees on both. It uses $`e_Q=(\tau(Q)+\lfloor\sum_{j\ge1}\tau(Q+j)2^{-j}\rfloor)\bmod2`$, full factorisations of $`Q+j`$ (Brent's rho, with deterministic Miller–Rabin below $`3.3\times10^{24}`$, Sorenson–Webster) and a certified carry. So the constant, the bit indexing (bit $`Q`$ is position $`Q`$ to the right of the point) and the digit convention all agree.
3. The §6 tables, as transcribed, are internally consistent. They sum to $`2^{43}/\lambda`$ (rounded down in base 8). The base-4 and base-16 tables reproduce the binary count of ones, $`4436987456570`$, exactly. The base-8 table gives one fewer, consistent with the two leftover bits.

**The discrepancy.** As labelled, the table has one-frequency $`0.504427`$ on bits $`1`$ to $`2^{43}`$ ("too many 1s"). Our certified prefix frequencies are $`0.500678`$ at $`2^{20}`$, $`0.495743`$ at $`2^{22}`$ and $`0.494216`$ at $`2^{24}`$, the last two from Phase 16. The shell frequencies fall from $`0.514`$ ($`s=12`$) to a plateau of $`0.4937`$ ($`s=21,22,23`$). As labelled, the bits in $`(2^{24},2^{43}]`$, half of them in shell 42, would have to average $`0.50443`$, a rise of about $`+0.0107`$ above the plateau. Read complemented, they would average $`0.49557`$, a rise of about $`+0.0019`$. Both readings need an upward drift. The Poisson limit $`p_*=0.49245`$ lies below both, but the approach to it is at rate $`(\log\log N)^{-1/2}`$ and need not be monotone.

In an auxiliary correlation check against Phase 16's certified $`2^{22}`$ digit run (not rerun in the $`2^{20}`$-bit default script), popcount-corrected block residuals give $`+0.74`$ complemented against $`-0.63`$ as labelled in base 4, $`+0.59`$ against $`+0.45`$ in base 8, and $`+0.26`$ against $`+0.34`$ in base 16. This is inconclusive. Crandall's §7 longest runs (47 zeros, 41 ones) do not discriminate either.

**Conclusion.** Phase 16's sentence that the table "appears to have its 0/1 labels interchanged" should be read as an unverified hypothesis. Crandall reports that the stored bits passed remote-bit checks at "the first 1 billion random bit positions". If so, a complement would have to sit in the counting step, not in the stored bits. Settling the question needs either Mitchell's output or certified shell frequencies to $`s\approx30`$. The latter is a segmented-sieve computation of the kind Crandall describes, taking about a day for $`2^{43}`$ in 2012. **We make no claim about which reading is correct.**

## 8. Mira Cult's theorem and collaboration targets

Mira's theorem (Phase 13 audit; Phase 16 §6) gives every fixed word a positive lower density on all late windows $`N^a\le H\le N`$ with $`7/12<a\le1`$. The bounds are $`\exp(-O(2^kk^2))`$ with an ineffective threshold. It is compatible with $`f(1)=1/2`$ and with $`f(1)=p_*`$. The weakest criteria found here demand the opposite kind of information: two-sided asymptotics at small relative error. Theorem 1 needs $`\mathbb E_I\Psi_{16}`$ to within $`2.6\times10^{-4}`$ of its model value $`0.4960`$, a relative precision of $`5\times10^{-4}`$. That is a lower-bound sieve set against an asymptotic, the parity barrier of Phase 16 §6.

Concrete targets:

1. **Upper-bound sieve at fixed relative error.** $`\Psi_{16}`$ is a nonnegative combination of cylinder indicators of $`R_{16}`$. So $`\limsup P_I(R_{16}\in B)\le(1+\eta)Q_{16}(B)`$ for the 556 cells ($`k=1,\dots,556`$) and the top half (557 sets in total), with $`\eta<5.3\times10^{-4}`$, implies Theorem 1's conclusion. Mira's planted-incidence framework gives lower bounds; an upper-bound analogue, even with $`\eta`$ moderate on a subfamily, would be the first two-sided control of a multi-column statistic.
2. **One harmonic.** $`\limsup\lvert A_I(1)\rvert>0`$ disproves normality (Section 6.2). Any method that could show the parity statistic $`\mathbb E_I(-1)^{N(n+1)}`$ stays away from 0 would isolate the factor $`e^{-2}`$ of Section 2.
3. **Computation.** Certified shell frequencies to $`s\approx30`$ would test Crandall's table (Section 7). They would also show whether the plateau $`0.4937`$ drifts towards $`p_*=0.49245`$.
4. **Two-point input at almost all scales.** Verify the formal hypotheses of the Tao–Teräväinen theorem for $`e(\theta V)\chi(U)`$, as proposed in Phase 16. Section 3 shows that two-point information alone cannot decide the bias, so this is a first step only.

## 9. Scope and reproduction

- **Proved (unconditional):** Theorem 1(a) as a deduction from Phase 14's tail mean. Theorem 4 and its dual proof. The identities of Proposition 5.1. Theorem 5.2(a) as a deduction from Vaaler's majorant.
- **Certified computations:** every table in Sections 1, 2 and 3, Theorem 4.2, the $`1.197\times10^{-4}`$ Bonferroni excess, and the remote bits. These use exact integers and fractions. The Fourier values and the dual measure of Theorem 5.2(b) use doubles with explicit radii.
- **Countermodels:** Theorem 1(b), Theorem 3, Corollary 4.1 and Theorem 4.2.
- **Conditional:** each sufficiency statement assumes its finite hypothesis along one sequence of windows. These are the inequality for $`\Psi_{16}`$ (Theorem 1), order-92 moments on 16 columns (Theorem 4.3), and 58 harmonics (Theorem 5.2(a)).
- **Numerical only:** the grid-LP degrees $`111`$ to $`115`$, the product-perturbation search at $`K=6`$, the integer-column-law remark ($`D=12`$), the word-$`11`$ remark ($`D=15`$), and the Fourier-route Bonferroni estimate.
- **Open arithmetic inputs:** lattice-scale $`r`$-point correlations of $`e(\theta V)\chi(U)`$ for $`r\ge9`$ (Section 6). The actual limiting one-frequency remains unknown.

```sh
python -B scripts/phase17_erdos_borwein_bias.py
```
