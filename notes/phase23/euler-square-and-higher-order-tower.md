# Euler's square, finite-order normality and the radix-power tower

Write $T_bx=\{bx\}$, and count words at all overlapping starts $0\le n<N$ in the canonical base-$b$ expansion. A length-$L$ word of integer value $v$ corresponds to $T_b^nx\in[v/b^L,(v+1)/b^L)$. Denote its frequency by $f_v(N;x,b)$. A real is *$L$-normal* if all these frequencies tend to $b^{-L}$. The *extreme interval discrepancy* $D_N(x;b)$ is the supremum, over $0\le a<c\le1$, of the absolute difference between the empirical mass and length of $[a,c)$. Write $D^+=\limsup D_N$ and use $D_\infty$ for the limit when it exists. Put $K_b=\{x:D_N(x;b)\to1\}$.

* **Paper proof from external inputs (Serre; Wirsing; Matomäki–Radziwiłł Cor. 1.2(ii)), §§1–2.** In the binary expansion of $E_2^2$, the digit imbalance equals, up to $o(1)$, the signed sum of **preceding** gap lengths of the nonzero coefficients divided by $N$. A short-interval theorem removes the carry correction in this weighted average. Equation (5) gives a necessary and sufficient shifted-correlation test. Both digits have lower frequency at least $1/40000$, with a stronger product bound below. **Open:** whether the imbalance tends to zero.
* **Paper proof (building on Phase 19 kernel decomposition, Phase 22 Thm 9.2, and `RadixPowerTower.lean`), §§3–4.** For $b,k\ge2$ and $L\ge1$, an $L$-normal element of $K_{b^k}\setminus K_b$ exists exactly when $b^L\mid k$. Each admissible level contains explicit irrational witnesses of exact order $L$. Formula (9) computes the entire finite spectrum and its sharp extrema for the specified $b,k,L$.
* **Paper proof, §5.** Over all $L$-normal reals the sharp maximum of $D^+$ is $2/b^L$. The limiting discrepancies fill $[0,2/b^L]$, and those of reals of exact order $L$ fill $(0,2/b^L]$. Tower witnesses of exact order $L$ have discrepancies dense in the closed interval as the tower level varies.

## 1. The signed coefficients

Let $E(q)=\prod_{j\ge1}(1-q^j)$, $E_b=E(1/b)$, $a(n)=[q^n]E(q)^2$ and $c(m)=[q^m]\eta(12\tau)^2$, where $q=e^{2\pi i\tau}$. Then $a(n)=c(12n+1)$. Put $U=\{n\ge0:a(n)\ne0\}$ and $s(n)=\operatorname{sgn}a(n)$, including $s(n)=0$ outside $U$. In particular $0\in U$. The multiplicative variable is $m=12n+1$.

**External input.** The weight-one CM eigenform identification gives multiplicativity of $c$, determinant character $\chi_{-4}$ away from $6$, and zero coefficients at multiples of $2$ or $3$. For $p\equiv1\bmod12$, write $p=x^2+y^2$ with $x$ odd and $y$ even. Then $c(p)=2\epsilon_p$, where $\epsilon_p=1$ if $3\mid y$ and $\epsilon_p=-1$ if $3\mid x$. The two signs correspond to $x^2+36y^2$ and $4x^2+9y^2$, respectively, after changing variables. Indeed the pentagonal theta identity gives $c(p)=2\chi_{12}(x^2-y^2)$, and $x^2-y^2\equiv1\bmod4$. For the other primes $p\nmid6$, $c(p)=0$. [Serre, *Sur la lacunarité des puissances de η*](https://doi.org/10.1017/S0017089500006194) · [Prime-power formulas](../phase20/euler-product.md#5-the-square-of-eulers-product) · [Prime signs and the ring class field](../phase22/flagship-digit-laws.md#4-eulers-square)

**An explicit ideal character.** For an ideal of $\mathbb Z[i]$ prime to $6$, choose a generator $x+iy$ with $x$ odd and $y$ even. Exactly two associates satisfy this convention, differing by $-1$. Products preserve it. In $\mathbb F_9=\mathbb F_3[i]$, $1+i$ has order eight, since $(1+i)^2=-i$ and $(1+i)^4=-1$. Map $1+i$ to the complex fourth root $i$. This character kills $-1$, so evaluation on the generator modulo $3$ gives a well-defined multiplicative ideal character $\psi$. It factors through residues modulo $6$ after the unit normalization. Conjugation in $\mathbb F_9$ is cubing, so conjugate ideals have inverse character values.

For a split $p\equiv1\bmod12$ its generator has norm one modulo $3$ and is $\pm1$ or $\pm i$ there, giving $\psi=\epsilon_p$ on both primes above $p$. For a split $p\equiv5\bmod12$ its norm is $-1$ modulo $3$, so the character values are $i,-i$. For an inert $p\equiv3\bmod4$, $p\nmid6$, the ideal $(p)$ has norm $p^2$ and character one. Summing the resulting geometric series over all powers of each prime ideal gives

```math
c(m)=\sum_{\substack{N\mathfrak a=m\\(\mathfrak a,6)=1}}\psi(\mathfrak a).
```

Indeed these Euler factors give the stated prime traces and the eigenform recurrence $c(p^{e+1})=c(p)c(p^e)-\chi_{-4}(p)c(p^{e-1})$ at every $p\nmid6$. Uniqueness of factorization of ideals proves coefficientwise equality, including ramified-level indices. In particular $c(p^e)=(e+1)\epsilon_p^e$ at the split primes $1\bmod12$. At the other $p\nmid6$, odd powers give zero and even powers give $c(p^{2e})=(-\chi_{-4}(p))^e$. Thus $n\in U$ iff every prime outside $1\bmod12$ dividing $12n+1$ has even exponent.

**Sign reversal, including repeated prime factors.** If $p\equiv1\bmod12$, let $n'=pn+(p-1)/12$ and $e=v_p(12n+1)$. Then

```math
 a(n')=\epsilon_p\frac{e+2}{e+1}a(n),\qquad s(n')=\epsilon_p s(n). \tag{1}
```

This follows by removing the full $p$-part before applying multiplicativity. In particular $p=13=4+9$ reverses every nonzero sign. The image of an empty gap under $n\mapsto n'$ controls only one residue class modulo $p$ inside the enlarged gap.

Write $A_N=(\log N)^{3/4}$, $S(N)=|U\cap[1,N]|$, and define $C_\eta$ by $S(N)\sim C_\eta N/A_N$. The two sign counts $S_\pm(N)$ are each asymptotic to $C_\eta N/(2A_N)$. Here the support asymptotic follows from its multiplicative indicator and Wirsing's theorem. For signed cancellation relative to the support, the negative prime class has Chebotarev density $1/8$ in the ring class field of discriminant $-144$, so its reciprocal-prime sum diverges. The real signed form of Wirsing's theorem applied to $\operatorname{sgn} c$ relative to $\mathbf1_{c\ne0}$ then gives $\sum_{n\le N}s(n)=o(N/A_N)$. These are **published inputs and paper deductions** as in the [Phase 22 proof of Theorem 4.4](../phase22/flagship-digit-laws.md#4-eulers-square).

## 2. Removing the carry weight and isolating the open correlation

List $U$ as $0=m_0<m_1<\cdots$ and set $g(m_i)=m_i-m_{i-1}$ for $i\ge1$. Define

```math
 T_n=\sum_{m>n}a(m)2^{n-m},\qquad V_m=a(m)+T_m .
```

The integral head of $2^nE_2^2$ leaves the tail $T_n$. At $m_{i-1}\le n<m_i$, $T_n=2^{n-m_i}V_{m_i}$. Its sign uses the **right endpoint** of the gap, and $V_m\ne0$ by irrationality of $E_2^2$ (transcendental by Nesterenko; [Phase 20 §4](../phase20/euler-product.md)). For $|T_n|<2^{-L}$ the next $L$ digits are $0^L$ or $1^L$ according as $T_n$ is positive or negative. The number of exceptional shifts $n<N$ is $O_L(N\log\log N/A_N)$ by signed coefficient transfer, using $S(N)\ll N/A_N$ and $\sum_{m\le N}|a(m)|\ll N$. The latter bound also follows by counting pairs of generalized pentagonal numbers up to $N$. [Oriented transfer and mass bound](../phase22/flagship-digit-laws.md#0-oriented-tails) · [Gap identities](../phase22/simple-normality-and-signed-transfer.md)

**Gap moments (external input applied to the exact support).** For every fixed $1<\gamma<3/2$,

```math
 \sum_{0<m\le N,\ m\in U}g(m)^\gamma\ll_\gamma N A_N^{\gamma-1}. \tag{2}
```

To check the hypotheses of Matomäki–Radziwiłł, take the multiplicative subset $\mathcal N=\{m:c(m)\ne0\}$ of the positive integers. All its elements are $1\bmod12$, so it is *exactly* $12U+1$. Its primes are precisely $1\bmod12$. Partial summation of the prime number theorem in this fixed progression gives, uniformly for $2\le w\le z$, $\sum_{w<p\le z,p\in\mathcal N}1/p=\frac14\sum_{w<p\le z}1/p+O(1/\log w)$. Thus hypothesis (2) of their paper ($\sum_{w<p\le z,p\in\mathcal N}1/p > \alpha\sum_{w<p\le z}1/p - O(1/\log w)$ for all $w\le z\le X^\alpha$) holds, for instance with $\alpha=1/8$. Their product $\delta(\mathcal N;X)=\prod_{p\le X,p\notin\mathcal N}(1-1/p)$ is comparable to $(\log X)^{-3/4}$ by Mertens in progressions. Apply Corollary 1.2(ii) with $X=12N+1$. Each gap counted on the left of (2) is $1/12$ of a gap in their sum, whose left endpoint is at most $X$. This proves (2). [Matomäki and Radziwiłł, *Multiplicative functions in short intervals II*, Corollary 1.2(ii)](https://arxiv.org/abs/2007.04290)

**Negligible total weight of carry flips (paper proof).** Let $\mathcal B_N$ consist of the supported indices $1\le m\le N$ with $\operatorname{sgn}V_m\ne s(m)$. Let $C_0$ be any valid absolute constant in Theorem S, so the number of pairs $n,n+h\in U$, $1\le n\le N$, $1\le h\le R_0$, is at most $C_0 R_0 N/A_N^2$. Then, for $1\le R_0\le N$,

```math
 |\mathcal B_N|\ll R_0 N/A_N^2+N2^{-R_0}.
```

Indeed a flip requires $|T_m|\ge1$. Ends with another support point in $(m,m+R_0]$ are covered by the pair bound. On the remaining ends, summing the absolute tail gives at most $\sum_{j>R_0}2^{-j}\sum_{m\le N}|a(m+j)|\ll(N+R_0)2^{-R_0}$. Take $R_0=\lceil3\log_2 A_N\rceil$ for large $N$. By Hölder and (2), with $\theta=1-1/\gamma$,

```math
 \frac1N\sum_{m\in\mathcal B_N}g(m)
 \ll_\gamma \left(\frac{\log A_N}{A_N}\right)^\theta,
 \qquad 0<\theta<1/3. \tag{3}
```

This bound concerns the preceding gap even though isolation for detecting a flip concerns the following coefficients. The moments connect these two directions. [Theorem S and its constant](../phase22/partitions-carry-and-lemma-s.md)

**Digit law (paper proof).** For every fixed $L\ge1$ and $0<\theta<1/3$,

```math
 f_{0^L}(N;E_2^2,2)-f_{1^L}(N;E_2^2,2)
 =\frac1N\sum_{0<m\le N,\ m\in U}s(m)g(m)
 +O_{L,\theta}\left((\log A_N/A_N)^\theta\right). \tag{4}
```

The complete gaps contribute their lengths times $\operatorname{sgn}V_m$, up to twice the number of exceptional shifts. The incomplete gap meeting $N$ costs $O(\sqrt N)$: all $n=3j^2+j$ belong to $U$ since $12n+1=(6j+1)^2$, and consecutive such indices differ by $6j+4$. Replacing the oriented sign costs at most twice (3). All nonconstant words of fixed length have frequency $o(1)$. Thus (4) determines their two complementary constant-word frequencies, including both single digits. With $m_i$ increasing, a forward-gap expression must use $s(m_{i+1})(m_{i+1}-m_i)$. Replacing its sign by $s(m_i)$ would require an additional correlation identity.

**Exact remaining test.** Given a positive integer $H$, let

```math
 B_N(H)=\sum_{j=0}^{H-1}\ \sum_{\substack{1\le m\le N\\m>j}}
 s(m)\prod_{h=1}^{j}(1-\mathbf1_U(m-h)).
```

The $j=0$ product is one. At $m\in U$ the inner condition counts exactly $\min(g(m),H)$ choices of $j$, including the initial gap at $0$. Hence the difference from the numerator of (4) has magnitude at most $\sum_{g(m)>H}g(m)\ll_\gamma N(A_N/H)^{\gamma-1}$ by (2). In particular with $H_N=\lceil A_N\log\log N\rceil$ for large $N$,

```math
 E_2^2\text{ simply normal in base }2
 \quad\Longleftrightarrow\quad B_N(H_N)=o(N). \tag{5}
```

This works for any $H_N/A_N\to\infty$. For $1\le H\le N$, the difference between $B_N(H)$ and $H\sum_{1\le m\le N}s(m)$ is bounded by $H+C_0 H(H-1)N/(2A_N^2)$. In layer $j$ a discarded end has a previous support point within $j$. Its preceding point is either $0$ (at most one end) or yields a pair in Theorem S. Thus every $H=o(A_N)$ gives $B_N(H)=o(N)$, yet discarding the longer gaps at this scale has no vanishing bound from (2). Wirsing controls layer zero. The sign-changing dilation (1) and the unsigned moment (2) do not evaluate the survival indicators at mean-gap scale. **Conditional:** cancellation in (5) gives binary simple normality. **Open:** cancellation, a nonzero limiting bias, and nonconvergence remain undecided here.

**Unconditional bounds.** For $\sigma=+,-$, let $W_\sigma$ sum $g(m)$ at the corresponding ends $m\le N$. Summing the layer estimate without signs gives

```math
 W_\sigma\ge H S_\sigma(N)-H-\frac{C_0H(H-1)N}{2A_N^2}.
```

At $H=\lfloor t A_N\rfloor$, using $S_\sigma(N)\sim C_\eta N/(2A_N)$ (§1), the lower bound after division by $N$ tends in its main terms to $t C_\eta/2-C_0t^2/2$. Its maximum is $\kappa=C_\eta^2/(8C_0)$ at $t=C_\eta/(2C_0)$. Consequently

```math
 \kappa\le\liminf f_0\le\limsup f_0\le1-\kappa,
 \qquad \limsup |f_0-1/2|\le1/2-\kappa. \tag{6}
```

Here $W_++W_-=N+O(\sqrt N)$, and (4) transfers the same bounds to every fixed constant word of either sign. Formula (6) optimizes the displayed pair-sieve bound. The true endpoints for this number are unknown. This constant uses the support normalization in §1 and the one-sided pair count in Theorem S.

**An absolute numerical consequence.** Taking $C_0=(K_*+\varepsilon)C_\eta^2$ in (6) (valid for large $N$, as proved below) yields $\kappa\ge 1/(8K_*) > 1/40000$. The following product bound also gives a stronger constant without choosing numerical Mertens constants. Let $\mathcal P$ consist of primes $5,7,11\bmod12$ and put

```math
 \Pi_{\mathcal P}(z)=\prod_{\substack{p\le z\\p\in\mathcal P}}(1-1/p),\qquad
 \mathcal W=\frac{4 e^{3\gamma_E/4}}{\Gamma(1/4)}
       \prod_{p\in\mathcal P}(1-p^{-2})^{-1},\qquad
 J_a=\sum_{(n,6)=1}\frac{(n/\varphi(n))^a}{n^2}.
```

Here $\gamma_E$ is Euler's constant. Wirsing's product formula for the nonnegative indicator of $\mathcal N$ has prefactor $e^{-\gamma_E/4}X/(\Gamma(1/4)\log X)$. The local series at $p$ are $(1-p^{-1})^{-1}$ for $p\equiv1\bmod12$, $(1-p^{-2})^{-1}$ on $\mathcal P$, and one at $2,3$. Extracting Mertens' full product contributes $e^{\gamma_E}\log X$. Removing its factors at $2,3$ contributes $1/3$, and the variable $12n+1$ contributes the factor $12$. In particular $\Pi_{\mathcal P}(z)\sim(C_\eta/\mathcal W)(\log z)^{-3/4}$.

Here are the changes of parameters needed in the proof of Theorem S to track this constant. Write $P_h(N)$ for its pair count, take $V=(\log N)^3$, $z=N^\beta$ for any fixed $0<\beta<1/34$, and $\xi=z^{17}$. Ends with a square divisor $v^2$ from the primes of $\mathcal P$ and $v>V$ cost $O(N/V+\sqrt N)$, uniformly for $h\le N$. For $v,v'\le V$ the two square conditions give one admissible progression of modulus $d=\mathrm{lcm}(v^2,v'^2)$ when compatible. Its length is at most $(1+o(1))N/d$ uniformly since $d\le V^4$. Lemmas S.1–S.4 bound the sifted main term, at each such pair, by

```math
 (2+o(1))\,\frac{N}{d} \Pi_{\mathcal P}(z)^2
   (v/\varphi(v))^2(v'/\varphi(v'))^2 h/\varphi(h).
```

Indeed the sieve has two roots at ordinary primes, loses at most one at divisors of $h$, omits divisors of $vv'$, and $G(\xi)\ge\frac12\prod_{p\in\mathcal Q}(1-1/p)^{-\rho(p)}$ by Lemma S.2, where $\mathcal Q=\{p\in\mathcal P:p\le z,\ p\nmid vv'\}$. The sum of its remainders is $O(V^2\xi^2(1+\log\xi)^2)=o(N/A_N^2)$. On writing $v=gw$, $v'=gw'$, with $g=(v,v')$, the sum of $(v/\varphi(v))^2(v'/\varphi(v'))^2/d$ is at most $J_4 J_2^2$: $d=g^2w^2w'^2$, and each of $g,w,w'$ is coprime to $6$. Finally $\sum_{h\le H}h/\varphi(h)\le R_{\rm tot}H$ with $R_{\rm tot}=\prod_p(1+1/(p(p-1)))<2$. This is the divisor-sum identity in the proof of Theorem S. [Selberg sieve lemmas and progression count](../phase22/partitions-carry-and-lemma-s.md)

Consequently the limsup, uniform for $1\le H\le N$, of $A_N^2\sum_{h\le H}P_h(N)/(HNC_\eta^2)$ is at most $2\beta^{-3/2}J_4J_2^2 R_{\rm tot}/\mathcal W^2$. Let $\beta\uparrow1/34$ **after** taking the limsup and call the resulting upper bound $K_*$. The layer proof gives $\min(\liminf f_0,\liminf f_1)\ge1/(8K_*)$, by first using any larger constant in the pair bound. To obtain the displayed numerical consequence, $\mathcal W>4/5$ since $\Gamma(1/4)<4+e^{-1}<5$. For $a=2,4$,

```math
 J_a=\tfrac23\zeta(2)\prod_{p\ge5}
 \left(1+\frac{(1-1/p)^{-a}-1}{p^2}\right)<\tfrac32 .
```

Indeed $(1-u)^{-4}\le1+8u$ on $[0,1/5]$ by convexity and the endpoint values, and $\sum_{n\ge5}n^{-3}\le1/32$. Hence the product is at most $e^{1/4}<4/3$; $\zeta(2)<5/3$ follows by summing through $6$ and bounding the tail by $1/6$. Thus $K_*<2\cdot36^{3/2}(3/2)^3\cdot2(5/4)^2<5000$. This proves $1/40000\le\liminf f_0\le\limsup f_0\le39999/40000$, and $\limsup|f_0-1/2|\le19999/40000$. The numerical bounds are deductions from inequalities, independent of the digit sample in §7.

## 3. The tower at order L

Fix $b,k\ge2$, $L\ge1$, and put $M=b^L$, $Q=b^k-1$. Let $\|t\|$ denote distance to the nearest integer, $m_N(u)=N^{-1}\sum_{n<N}\|b^nu\|$, and $M_b=\{u:m_N(u)\to0\}$. The Phase 19 kernel decomposition is $K_b=(b-1)^{-1}\mathbb Z+M_b$, and the zero-orbit subgroups satisfy $M_b=M_{b^k}$. If $y\in Q^{-1}\mathbb Z\cap M_{b^k}$, then $\|b^{kn}y\|=\|y\|$ for every $n$, so $y\in\mathbb Z$. Applying the decomposition in radix $b^k$ therefore gives a unique representation

```math
 z=r/Q+u,\quad 0\le r<Q,\quad u\in M_b,\qquad
 z\in K_b\ \Longleftrightarrow\ Q\mid(b-1)r. \tag{7}
```

For the reverse membership test, subtract the two fixed-point parts in a putative decomposition in $K_b$: their difference lies in $Q^{-1}\mathbb Z\cap M_b=\mathbb Z$. [Kernel decomposition and quotient, Theorem 8.1](../phase22/odd-characters-and-kernel-quotient.md#8-the-quotient) · [Kernel-verified zero-orbit subgroup identity](../../NormalityChecker/RadixPowerTower.lean)

For $r\ne0$, the orbit of $c=r/Q$ comprises rotations of the $k$-digit block of $r$, including leading zeros. Its least period $d$ divides $k$. At any shift the numerator is some $0<r'<Q$, since $\gcd(b,Q)=1$. For every length $\ell$ its distance to the entire $b^{-\ell}$ grid is at least $1/(Qb^\ell)$: the numerator of $|r'/Q-j/b^\ell|$ over the common denominator is a nonzero integer. Choose a signed nearest-integer representative of $b^nu$. When its magnitude is below that margin, both $c+u$ and $c$ read the same $\ell$-word, including near $0$ and $1$. The fraction of the remaining starts is at most $Qb^\ell m_N(u)$. Thus every finite word has exactly its limiting frequency in the periodic expansion of $c$. This uses the signed margin on both sides, as in the existing Lean theorem. [RadixPowerTower.coprime_rat_cylinder_stable](../../NormalityChecker/RadixPowerTower.lean#L1012)

**Necessity.** Outside $K_b$ we have $r\ne0$. If $z$ is $L$-normal then in a full least period each $L$-word occurs exactly $d/M$ times. Thus $M\mid d\mid k$.

**Sufficiency and exact next-order law.** Form the directed graph with $(L-1)$-word vertices and an edge for each $L$-word, directed from prefix to suffix. For $L=1$ use one vertex and $b$ labelled loops. Every vertex has $b$ incoming and $b$ outgoing edges, and appending a target vertex's digits gives a path to it. An Euler circuit therefore exists. For a deterministic choice, start at the zero vertex and use the lexicographically first full tour in the traversal of §4. Reading the appended digits yields a cyclic word $W$ of length $M$ whose $L$-windows use each edge once. Its least period is $M$, since a smaller period would repeat an $L$-word. When $M\mid k$, repeat $W$ exactly $k/M$ times to form the block of $r$. Then $c=r/Q$ has orbit size $M\ge2$; equivalently $Q\nmid(b-1)r$. In every translate $c+u$, $u\in M_b$, a length-$(L+1)$ word with prefix $v$ has frequency $1/M$ if its last digit is the unique follower of $v$ in $W$, and zero for the other $b-1$ followers. This proves exact order $L$.

An explicit irrational choice is $u=\sum_{j\ge1}b^{-2^j}$. Its digits have infinitely many ones separated by unbounded zero runs, which precludes eventual periodicity. For a fixed $J$, outside the $J$ positions before each of $O(\log(N+J))$ ones, the next $J$ digits are zero. Thus $\limsup_N m_N(u)\le b^{-J}$, and $J\to\infty$ gives $u\in M_b$. Adding the rational $c$ preserves irrationality.

**Including the smaller kernel.** For $b\ge3$, $K_b$ has no simply normal element: the zero-orbit summand at the boundary gives total frequency one to the two end digits, and an interior fixed point gives frequency one to its own digit. In $K_2=M_2$ the mixed length-two words have total frequency zero, so no element is $2$-normal. Summing extension frequencies shows that $L$-normality implies every lower order. For $(b,L)=(2,1)$, alternating binary runs of lengths $1,2,3,\ldots$ have frequency $1/2$ of either digit and belong to $M_2$: at most $O(J\sqrt N)$ starts approach a run end within $J$ places. Thus existence in all of $K_{b^k}$ is equivalent to $M\mid k$ **or** $(b,L)=(2,1)$, while the difference of kernels always requires $M\mid k$. [GF-19 declarations](../../NormalityChecker/SimpleNormalityKernel.lean) · [Phase 22 simple-normal tower theorem](../phase22/odd-characters-and-kernel-quotient.md#10-simple-normality-in-the-tower)

## 4. Exact tower discrepancies and sharp fixed-level bounds

For $d$ distinct sorted atoms $y_0<\cdots<y_{d-1}$ of equal mass, the extreme discrepancy is $1/d+\max_i(y_i-i/d)-\min_i(y_i-i/d)$. Indeed it is the oscillation of the cumulative mass minus position, including both sides of each jump. The extrema occur immediately before or after an atom, with the two sides of the circle seam identified (a wrapping circle arc's excess equals the deficit of the complementary interval in $[0,1)$, so extreme interval discrepancy and circle-arc discrepancy coincide). The same formula holds for a sorted multiset of size $k$: within a tie the corresponding pre- and post-jump extremes come from the first and last ranks. For $z=c+u$ in (7), the sharp translation inequality gives $|D_N(z;b)-D_N(c;b)|\le1-D_N(u;b)\to0$. The periodic sample differs from its cycle by at most $d/N$ in discrepancy. Thus these atomic computations include all the irrational translates above. [Equal-atom formula and translation, Theorem 9.2](../phase22/odd-characters-and-kernel-quotient.md)

**A de Bruijn cycle.** Sort its $M$ orbit points $y_j$. The unique point in cell $j$ has the form $(j+t_j)/M$, and $t_j=\{b^L y_j\}$ permutes the orbit by a shift of $L$ places. Therefore

```math
 D_\infty=\frac{1+\max y_j-\min y_j}{M},\qquad
 \frac{2}{M+1}\ \le D_\infty\le\
 \frac{2}{M}\left(1-\frac{1}{bM-1}\right). \tag{8}
```

The equality formula was already obtained in the repository. To prove the two refinements, put $x=\min y_j$ and $z=1-\max y_j$. The constant extreme prefixes give $Mx\le1-z$ and $Mz\le1-x$. The second inequality follows by complementing all digits. Thus $(M+1)(x+z)\le2$. The digit after the unique $0^L$ must be nonzero, since otherwise $0^L$ repeats, even cyclically. Consequently $bMx\ge1+x$, and complementation gives $bMz\ge1+z$. Insert both bounds into $D_\infty=(2-x-z)/M$. In particular $M D_\infty\to2$ uniformly over the choice of cycles as $L\to\infty$ for fixed $b$. The sharp finite extrema for each $b,L$ are given by (9) with $k=M$; (8) gives a closed-form envelope. [Earlier de Bruijn discrepancy calculation](../translated-shells.md#de-bruijn-translations)

**An integer formula for the sharp extrema and the whole spectrum at a fixed level.** If $M\nmid k$ the spectrum in the difference of kernels is empty. Otherwise write $t=k/M$. In the graph in §3 put $t$ copies of each edge. Start at the all-zero vertex, taking a remaining edge at each step. Keep the closed tours of length $k$; parallel copies with identical labels are indistinguishable. For each resulting digit string form its integer $r$, then form and sort the $k$ integers $b^j r\bmod Q$ for $0\le j<k$, with multiplicities, as $v_0,\ldots,v_{k-1}$. Compute $h_i=k v_i-i Q$. The exact finite set is

```math
 \mathcal S_{b,L,k}=
 \left\{\frac{Q+\max_i h_i-\min_i h_i}{kQ}:
     \text{one output of the edge traversal above}\right\}. \tag{9}
```

In particular the sharp upper bound for $D^+$ is $(Q+\max_{\rm tours}(\max_i h_i-\min_i h_i))/(kQ)$, and the sharp lower bound uses the minimum of the same integer ranges. This terminates in at most $b^k$ labelled paths, involving only integer operations before the final division. For exact order $L$, discard tours that are $(L+1)$-balanced, i.e., in which every length-$(L+1)$ word occurs exactly $k/(bM)$ times (possible only when $bM\mid k$). Repetitions of shorter periods are retained. Every $L$-balanced cyclic block yields one of the tours by starting it at a visit to the zero vertex, and every tour yields such a block. Equations (7) and the multiset formula prove equality in (9); every output is attained by an irrational. The all-$K_{2^k}$ spectrum for $b=2,L=1$ adds the value $1$ for the smaller kernel.

All fixed-level outputs satisfy $D_\infty\le 2/M-2/(MQ)<2/M$. Indeed each of the $t$ points of cell $j$ is between $j/M+1/(MQ)$ and $(j+1)/M-1/(MQ)$. For ranks $i=jt+s$, $0\le s<t$, insert these bounds into $1/k+\operatorname{osc}_i(v_i/Q-i/k)$. The exact fixed-level maximum can be strictly smaller than this estimate.

## 5. The spectrum over all reals

**Universal bound.** For an $L$-normal real the vector of masses of the $M$ cells converges to $(1/M,\ldots,1/M)$. For any interval, rounding its endpoints outwards to that grid costs at most $2/M$ in length and bounds its excess. Rounding inwards bounds its deficit, including the case of empty interior rounding. The total absolute error in the $M$ cell counts is $o(1)$, uniformly over unions of cells. Thus $D^+\le2/M$. More generally, for a grid of mesh $1/B$ the discrepancy restricted to grid endpoints is within $2/B$ of unrestricted discrepancy for **every** empirical measure.

**All intermediate discrepancies, including the upper endpoint.** On infinite digit strings let $\nu$ choose an $L$-word uniformly then repeat it forever. Rotation permutes the words, so $\nu$ is shift-invariant with uniform $L$-marginal. Its symbolic masses at $0^\infty$ and $(b-1)^\infty$ are each $1/M$; on the circle both approach the seam. Let $\lambda$ denote uniform independent digits and $0\le t\le1$. We first construct a single digit string with every finite word frequency equal to that of $(1-t)\lambda+t\nu$.

For $0<t<1$, at stage $j$ append $j$ copies of each $L$-word consecutively, in lexicographic order by word ($w^j$ for each $w$). Follow this by the next $\lfloor jML(1-t)/t\rfloor$ consecutive digits from one fixed normal expansion, continuing that stream at the next stage. The fraction of digits in the periodic pieces tends to $t$. At any fixed test length $\ell$, each $w^j$ has exactly its periodic phase counts up to $O(\ell)$ lost starts, because its length is a multiple of $L$. Averaging over $w$ gives $\nu$. The normal portions together are an initial segment of a normal expansion up to $O(\ell)$ boundary starts per stage. Through stage $J$ the boundary error is $O_{b,L,\ell}(J)$ against total length of order $J^2$, and an unfinished stage also costs $O_{b,L,t}(J)$. This proves the full-prefix claim. At $t=1$ omit the normal pieces, and at $t=0$ use the normal expansion itself. The positive frequency of distinct digits ensures these strings represent their canonical expansions.

On the grid of $B=b^\ell$ cells, $\ell\ge L$, the limiting mass of each cell is its symbolic word probability. Every grid-interval discrepancy is at most $2t/M$: the uniform component cancels exactly, and rounding to the $M$-grid bounds the discrepancy of $\nu$ by $2/M$. The interval $[1/B,1-1/B)$ has deficit exactly $2t(1/M-1/B)$, since only the two constant $L$-words give the corresponding outermost length-$\ell$ cells under $\nu$. First let $N\to\infty$ on the finite grid, then $\ell\to\infty$ in the $2/B$ rounding bound. This proves $D_N\to2t/M$, including $t=1$. Symbolic cell counts avoid any appeal to continuity of a cylinder through the seam atom. Also

```math
 f_{0^{L+1}}\ \longrightarrow\ \frac{1-t}{bM}+\frac tM .
```

Hence $t>0$ realizes exact order $L$. Conversely $D_N\to0$ forces the correct frequencies for every cylinder, so zero is excluded for exact order $L$. This proves the asserted two real spectra.

**Density across tower levels.** The finite spectra in (9) are countable in union and bounded strictly between $0$ and $2/M$. Their closure is $[0,2/M]$, even with the exact-order filter. Here is a construction that gives every $L$-word exactly the same count before taking any limit. For $J\ge L+1$ take $P$ copies of an order-$J$ de Bruijn cycle as a single closed walk in the graph of §3. It visits every length-$L$ edge exactly $P b^{J-L}$ times. Partition the $L$-words into cyclic rotation orbits. Each orbit of size $d$ is a closed walk of $d$ edges in that graph, traversing each member once. Insert $q$ laps of each such walk at one occurrence of its base vertex on the original walk. Every $L$-edge now occurs $P b^{J-L}+q$ times. At fixed $J$, the fraction of inserted digits is $q/(P b^{J-L}+q)$. Choose integers $P,q\to\infty$ so this ratio tends to $t$ (endpoint ratios can also be approached).

For $J$-word counts the junctions affect at most one junction pair per rotation orbit, hence at most $2M(J-1)=O(JM)$ affected starts, independently of $P,q$. Before insertion the $J$-word law is exactly uniform; the inserted walks in aggregate have law $\nu$ up to the junction error, since they give each $L$-word the same number of periodic phases. The extended cycle therefore approximates the mixture on this fixed grid to arbitrary accuracy. Applying the same grid bounds as above and then $J\to\infty$ gives discrepancies tending to $2t/M$. For $t>0$ the limiting $0^{L+1}$ excess is positive, so the approximants eventually have exact order $L$; take $t\downarrow0$ for the remaining closure endpoint. In particular $2/M$ is the sharp supremum over tower levels. It can also be approached through *every* large multiple $k$ of $M$ by starting with one order-$L$ circuit and inserting $k/M-1$ laps of each rotation orbit: for each fixed test length the bounded number of junctions has vanishing frequency, giving the $t=1$ law.

## 6. Lean 4 formalization blueprint

The target module is `NormalityChecker/HigherOrderTower.lean`. The pseudocode signatures below use the existing `SimpleNormalityKernel.wordFreq` and `RadixPowerTower.zeroOrbitSubgroup` (with Lean 4.36 `module` / `public import` headers; proofs are supplied separately in the Lean module).

```lean
module

public import NormalityChecker.SimpleNormalityKernel
public import NormalityChecker.RadixPowerTower

@[expose] public section

namespace NormalityChecker.HigherOrderTower
open Filter Finset SimpleNormalityKernel RadixPowerTower
open scoped Topology

def OrderNormal (b L : ℕ) (x : ℝ) : Prop :=
  ∀ v < b ^ L, Tendsto (wordFreq b L x v) atTop (𝓝 (1 / (b : ℝ) ^ L))

def Kernel (b : ℕ) : Set ℝ :=
  {x | Tendsto (radixDiscrepancy b x) atTop (𝓝 1)}

def cyclicCount (b k L r v : ℕ) : ℕ :=
  let q := b ^ k - 1
  ((range k).filter fun j => b ^ L * (b ^ j * r % q) / q = v).card

-- Blueprint targets (pseudocode; formalized separately in HigherOrderTower.lean).
theorem wordFreq_tower_limit {b k L r : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hr : 0 < r) (hr' : r < b ^ k - 1)
    {u : ℝ} (hu : u ∈ zeroOrbitSubgroup b) (v : ℕ) :
    Tendsto (wordFreq b L ((r : ℝ) / ((b : ℝ) ^ k - 1) + u) v)
      atTop (𝓝 ((cyclicCount b k L r v : ℝ) / k)) := by sorry

theorem exists_balanced_block {b L : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) :
    ∃ r : ℕ, 0 < r ∧ r < b ^ (b ^ L) - 1 ∧
      (∀ v < b ^ L, cyclicCount b (b ^ L) L r v = 1) ∧
      (∀ v < b ^ (L + 1), cyclicCount b (b ^ L) (L + 1) r v ≤ 1) := by sorry

theorem tower_iff {b k L : ℕ} (hb : 2 ≤ b) (hk : 2 ≤ k) (hL : 1 ≤ L) :
    (∃ x, x ∈ Kernel (b ^ k) \ Kernel b ∧ OrderNormal b L x) ↔ b ^ L ∣ k := by sorry

theorem tower_irrational_exact_iff {b k L : ℕ}
    (hb : 2 ≤ b) (hk : 2 ≤ k) (hL : 1 ≤ L) :
    (∃ x, Irrational x ∧ x ∈ Kernel (b ^ k) \ Kernel b ∧
      OrderNormal b L x ∧ ¬ OrderNormal b (L + 1) x) ↔ b ^ L ∣ k := by sorry

end NormalityChecker.HigherOrderTower
end
```

Formalize the kernel decomposition (7) for both radices, including the fixed-center stabilization from Phase 19. The subgroup equality alone supplies only the perturbation step. For `wordFreq_tower_limit` use `coprime_rat_cylinder_stable` at a signed lift, Markov's finite counting bound and division of $N$ into $k$-blocks. For `exists_balanced_block` use labelled directed edges, retaining the $b$ distinct loops at $L=1$. Encode the recorded digit string as a natural with leading zeros implicit in its specified block length. Then use uniqueness of limits and clear denominators for necessity, repeat the block for sufficiency, and prove irrationality of the sparse perturbation by eventual periodicity of rational digits. A subsequent finite discrepancy lemma can take a sorted `Fin k → ℕ` listing of the rotations and assert (9) for the rational orbit on one period. Its integers $h_i$ need signed casts before subtraction.

## 7. Finite certificates, measurements and prior art

Run `python -B scripts/phase23_euler_tower.py`. The verifier uses integer and rational arithmetic. For Euler's square it compares pentagonal convolution, enumeration of Gaussian generators, and the prime-power coefficient formula at every computed index. Let $P_{\rm end}$ be the final index computed. Each $|a(m)|\le m+1$ by convolution, so $|T_{P_{\rm end}}|\le\sum_{j\ge1}(P_{\rm end}+j+1)2^{-j}=P_{\rm end}+3$. Outward dyadic interval rounding in $T_n=(a(n+1)+T_{n+1})/2$ certifies each sign and digit used. A separate integer evaluation of $2^{P_{\rm end}}\sum_{m\le P_{\rm end}}a(m)2^{-m}$ certifies the whole binary prefix against the same tail bound. [Exact verifier](../../scripts/phase23_euler_tower.py)

**Finite measurements of the infinite binary expansion.** The two positive-weight columns count starts in $[0,N)$, clipping the last gap to the prefix. The flipped weight counts starts in $[0,N)$ in gaps whose right endpoint has different oriented and coefficient signs. The unweighted columns count supported indices in $[1,N]$. (At these finite scales the empirical difference between $f_0 - f_1$ and $\frac{1}{N}\sum s(m)g(m)$ reflects the slowly decaying error $(\log A_N/A_N)^\theta$.)

| $N$ | Supported ends | Positive ends | Zero digits | Positive oriented weight | Positive coefficient weight | Flipped weight |
|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 1762 | 884 | 2119 | 2106 | 2076 | 90 |
| 16384 | 6376 | 3190 | 8304 | 8275 | 8216 | 323 |
| 32768 | 12187 | 6095 | 16545 | 16510 | 16422 | 686 |

**Finite certificates for periodic spectra.** In the following examples every value listed is a limiting discrepancy by the periodicity proof (all $L$-normal elements; with the exact-order-$L$ filter, $(2,1,4)$ has the single value $2/3$, while the other four rows are unchanged). The extrema and cardinalities were computed by (9).

| $(b,L,k)$ | Number of values | Minimum | Maximum |
|---|---:|---:|---:|
| $(2,1,2)$ | 1 | $2/3$ | $2/3$ |
| $(2,1,4)$ | 2 | $2/5$ | $2/3$ |
| $(2,2,4)$ | 1 | $2/5$ | $2/5$ |
| $(2,3,8)$ | 1 | $229/1020$ | $229/1020$ |
| $(3,2,9)$ | 12 | $17789/88569$ | $6226/29523$ |

The script compares integer traversal spectra with brute enumeration of all binary blocks through period length nine and ternary blocks through length six for the stated test orders. It independently tests arc excess at every ordered pair of orbit locations, including coincident endpoints, signed cylinder perturbations, the unique follower condition, the bounds (8), complete and clipped gap counts, the shifted-void identity, and finite instances of the mixtures and spliced tours. The finite Euler data establish no asymptotic sign cancellation.

**Prior art.** N. G. de Bruijn's 1946 paper is a historical source for the binary cycles. The Euler-circuit proof in §3 treats every radix and every order. Becher and Carton study low-discrepancy normal numbers obtained from nested perfect necklaces. Bailey and Crandall establish full normality for particular arithmetic constructions. Here the finite order is fixed and the discrepancy is taken over all intervals. The repository's earlier de Bruijn discrepancy identity and its order-one kernel tower theorem are cited in §§3–4. [De Bruijn, *A combinatorial problem*](https://research.tue.nl/en/publications/a-combinatorial-problem/) · [Becher and Carton, *Normal numbers and nested perfect necklaces*](https://doi.org/10.1016/j.jco.2019.03.003) · [Bailey and Crandall, *Random generators and normal numbers*](https://doi.org/10.1080/10586458.2002.10504704)
