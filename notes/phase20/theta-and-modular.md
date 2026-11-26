# Theta values of binary forms and weight-one modular forms in the numerical kernel

Phase 20, Tracks A3 and A4. Fix an integer radix $b\ge2$, let $D_N(z)=D_N(z;b)$ be the extreme discrepancy of $\{b^nz\}$, $0\le n<N$, and let $K_b=\{z:D_N(z)\to1\}$. For an integer sequence $a$ write $F_b(a)=\sum_{m\ge0}a(m)b^{-m}$,

```math
S(X)=\#\{1\le m\le X:\ a(m)\ne0\},\qquad A(X)=\sum_{1\le m\le X}|a(m)| .
```

**Theorem A (binary theta values).** Let $Q(m,n)=am^2+b_0mn+cn^2$ be any positive definite integral binary quadratic form, with $\Delta=b_0^2-4ac<0$, and put $\Theta_Q(1/b)=\sum_{(m,n)\in\mathbb Z^2}b^{-Q(m,n)}$. Then for every $b\ge2$

```math
\Theta_Q(1/b)\in K_b,\qquad 1-D_N(\Theta_Q(1/b))\ll_{Q,b}\frac{\log\log N}{\sqrt{\log N}} .
```

The same holds for integral shifted lattices, for congruence subsums (rational translates), for bounded weights, and for finite $\mathbb Z[1/b]$-combinations (§2.2). A matching lower bound $\gg\log\log N/\sqrt{\log N}$ holds by the Phase 17 sieve method (Proposition 6). Every $\Theta_Q(1/b)$ is irrational by an elementary digit argument and transcendental by Nesterenko's theorem through the Hamieh–Murty corollary.

**Theorem B (weight one).** Let $f=\sum_{n\ge0}a(n)q^n$ be a holomorphic modular form of weight one on some $\Gamma_1(M)$ with $a(n)\in\mathbb Z$. Then for every $b\ge2$

```math
f(1/b)\in K_b,\qquad 1-D_N(f(1/b))\ll_{f,b}\frac{\log\log N}{(\log N)^{\alpha_f}} .
```

Here $\alpha_f>0$ is the least, over the newform and Eisenstein constituents of $f$, of the density of primes at which the constituent has vanishing coefficient. The conclusion covers dihedral (CM) forms and exotic forms with projective image $A_4$, $S_4$ or $A_5$, and also arithmetic-progression subsequences $n\mapsto a(Mn+r)$, such as $E_b^2$.

**Theorem C (weight two and higher).** For Serre's lacunary eta powers $\eta^r$, $r\in\{4,6,8,10,14,26\}$, the coefficient-transfer method fails for a structural reason. Lacunarity of Fourier coefficients does not prevent overlaps of their radix expansions. Numerically $E_2^r$ looks equidistributed (§4).

Scope. Lemma 1 below is proved here and, when $A(X)\le CX$, is kernel-checked as `CoefficientTransfer.finite_sparse_mass_transfer` (Track B1). Theorems A and B are paper proofs from Lemma 1 and published theorems: Bernays/Landau, Halberstam–Richert or Shiu, Deligne–Serre and Chebotarev. Proposition 6 is a paper proof outline using the same published sieve inputs as the [Phase 17 lower bound](../phase17/multiplicative-lambert.md#5-word-frequencies-and-finite-discrepancy). Numerics come from the [verification script](../../scripts/phase20_euler_theta.py).

## 1. Coefficient transfer

**Lemma 1 (finite coefficient transfer).** Let $z=F_b(a)$ with $a(m)\in\mathbb Z$ and $\sum|a(m)|b^{-m}<\infty$. For integers $N,L\ge1$ and real $\varepsilon>0$,

```math
1-D_N(z)\ \le\ 2\varepsilon+\frac{L\,S(N+L-1)}N+\frac{b^{-L}A^*(N,L)}{(b-1)\,\varepsilon N},
\qquad A^*(N,L)=\sum_{m>L}|a(m)|\,b^{-(m-L-N)_+}.
```

*Proof.* By `Phase18Synthetic.discrepancy_deficit_le`, $1-D_N\le2\varepsilon+F(\varepsilon)/N$, where $F(\varepsilon)$ counts $n<N$ with $\|b^nz\|>\varepsilon$. The head $\sum_{m\le n}a(m)b^{n-m}$ is an integer, so $\|b^nz\|\le\bigl|\sum_{m>n}a(m)b^{n-m}\bigr|$.

- Shifts whose window $(n,n+L]$ contains a nonzero coefficient number at most $L\,S(N+L-1)$, since each such $m$ serves the $L$ shifts $m-L\le n<m$.
- For the other shifts, $\|b^nz\|\le T_n:=\sum_{m>n+L}|a(m)|b^{n-m}$. Exchanging the sums gives $\sum_{n<N}T_n\le\sum_{m>L}|a(m)|\,b^{\min(N,m-L)-m}/(b-1)=b^{-L}A^*(N,L)/(b-1)$, and Markov's inequality bounds the number with $T_n>\varepsilon$. $\square$

When $A(X)\le CX$ for all $X$, one has $A^*(N,L)\le C(N+L+2)\cdot b/(b-1)$, and Lemma 1 reduces to the kernel-checked [`finite_sparse_mass_transfer`](../../NormalityChecker/CoefficientTransfer.lean).

**Corollary 2.** Suppose $S(X)\ll X/(\log X)^{\kappa}$ with $\kappa>0$ and $A(X)\ll X(\log X)^{\beta}$ with $\beta\ge0$, and suppose $|a(m)|\ll m^{C}$ for some $C$, which controls the tail of $A^*$. Then

```math
1-D_N(F_b(a))\ll\frac{\log\log N}{(\log N)^{\kappa}}.
```

*Proof.* Take $\varepsilon=(\log N)^{-\kappa}$ and $L=\lceil(2\kappa+\beta)\log_b\log N\rceil+1$. Then the Markov term is $\ll(\log N)^{-2\kappa-\beta}(\log N)^{\beta}(\log N)^{\kappa}=(\log N)^{-\kappa}$ and the support term is $\ll(\log\log N)(\log N)^{-\kappa}$. $\square$

The mass exponent $\beta$ enters only through $L=O(\log\log N)$. A mass growing like any fixed power of $\log X$ costs nothing beyond the constant, while a mass growing like a power of $X$ makes the method fail (§4).

## 2. Theta series of binary quadratic forms

Let $g=\gcd(a,b_0,c)$ and $Q=gQ_0$ with $Q_0$ primitive of discriminant $\Delta_0=\Delta/g^2$. Write $r_Q(j)=\#\{(m,n):Q(m,n)=j\}$, so that $\Theta_Q(1/b)=F_b(r_Q)$.

**Lemma 3 (lattice points).** $\sum_{j\le X}r_Q(j)=\dfrac{2\pi}{\sqrt{|\Delta|}}X+O_Q(\sqrt X)$, and $r_Q(j)\le2\bigl(2\sqrt{4aj/|\Delta|}+1\bigr)$.

*Proof.* The ellipse $\{Q\le X\}$ has area $\pi X/\sqrt{ac-b_0^2/4}=2\pi X/\sqrt{|\Delta|}$. Unit squares centred at its lattice points lie between the ellipses shrunk and enlarged by $\sqrt2/2$, whose areas differ from it by $O(\sqrt X)$. For the pointwise bound, $Q(m,n)\ge(|\Delta|/4a)n^2$, and each $n$ admits at most two values of $m$. $\square$

The script finds $\sum_{j\le2^{18}}r_Q(j)-2\pi X/\sqrt{|\Delta|}\in\{-76.7,+41.8,-28.6,-65.6\}$ for $m^2+n^2$, $m^2+mn+n^2$, $m^2+2n^2$ and $m^2+5n^2$.

**Lemma 4 (Bernays).** Let $B_Q(X)=\#\{1\le j\le X:r_Q(j)>0\}$. For primitive $Q_0$, Bernays (1912) proved $B_{Q_0}(X)\sim C_{Q_0}X/\sqrt{\log X}$, extending Landau's 1908 theorem for $m^2+n^2$. In general $B_Q(X)=B_{Q_0}(X/g)$. The upper bound $B_Q(X)\ll_QX/\sqrt{\log X}$, which is all that Theorem A needs, is elementary.

*Proof of the upper bound.* Suppose $(\Delta_0/p)=-1$. Then $Q_0$ is anisotropic modulo $p$, so $p\mid Q_0(m,n)$ forces $p\mid m$ and $p\mid n$. By induction $v_p(Q_0(m,n))$ is even.

To see anisotropy for odd $p$, use $4aQ_0=(2am+b_0n)^2-\Delta_0n^2$ when $p\nmid a$, and the analogous identity with $c$ when $p\mid a$, $p\nmid c$. If $p$ divided both $a$ and $c$, then $\Delta_0\equiv b_0^2$ would be a square modulo $p$. For $p=2$, the condition $\Delta_0\equiv5\pmod8$ forces $b_0$, $a$ and $c$ odd, and $m^2+mn+n^2$ has no nontrivial zero over $\mathbb F_2$.

Hence the represented set lies in $M_{\Delta_0}=\{j:v_p(j)\text{ even whenever }(\Delta_0/p)=-1\}$, whose indicator is multiplicative with prime density $1/2$ by Dirichlet's theorem. The Halberstam–Richert inequality $\sum_{n\le x}h(n)\ll(x/\log x)\exp\sum_{p\le x}h(p)/p$ for multiplicative $0\le h\le1$ gives $\ll x/\sqrt{\log x}$. $\square$

The script checks the even-exponent property for all $j\le2^{16}$ and all four forms, and records $S(X)\sqrt{\log X}/X$ at $X=2^{18}$ as $0.810$, $0.677$, $0.927$ and $0.576$. Brink, Moree and Osburn (2011) survey the constants. [Brink–Moree–Osburn, arXiv:1003.1094](https://arxiv.org/abs/1003.1094)

**Theorem 5.** For every positive definite integral binary $Q$ and every $b\ge2$, $\Theta_Q(1/b)\in K_b$ and $1-D_N(\Theta_Q(1/b))\ll_{Q,b}\log\log N/\sqrt{\log N}$.

*Proof.* Lemma 4 gives $\kappa=1/2$, Lemma 3 gives $\beta=0$ and $r_Q(j)\ll\sqrt j$, and Corollary 2 applies. $\square$

**Proposition 6 (matching lower bound; outline).** $1-D_N(\Theta_Q(1/b))\gg_{Q,b}\log\log N/\sqrt{\log N}$.

*Outline.* Follow the proof of Theorem 6(c) in the [Euler note](euler-product.md#5-the-square-of-eulers-product). The four ingredients are:

1. $B_Q(N)\gg N/\sqrt{\log N}$ (Bernays).
2. The pair bound $\#\{j\le N:r_Q(j)r_Q(j+h)>0\}\ll_hN/\log N$, with polynomial dependence on $h$. It follows from an upper-bound sieve on $j$ and $j+h$ in $M_{\Delta_0}$ (dimension $2\cdot\tfrac12$), as in Phase 17, §4. For $m^2+n^2$ it is Lemma 9.5 of Bailey, Borwein, Crandall and Pomerance (2004).
3. Markov bounds for tails.
4. Control of large coefficients.

The representation number is not multiplicative for general $Q$, so ingredient 4 uses the multiplicative majorant $r^*(j)\ge r_Q(j)$, the total over all classes of discriminant $\Delta_0$. For small $\lambda>0$, Shiu's theorem gives

```math
\sum_{j\le N}r^*(j)^{\lambda}\ll N(\log N)^{2^{\lambda-1}-1},
```

so all but $o(N/\sqrt{\log N})$ supported $j$ have $r_Q(j)\le(\log N)^{\theta}$ for any fixed $\theta>(\ln2)/2$. Each isolated $j$ then contributes at least $(\tfrac12-\theta-o(1))\log_b\log N$ separated far shifts. With Lemma 0(b) of the Euler note this gives the bound. $\square$

### 2.1 Arithmetic nature: four distinct properties

1. **Nonnormality** ($D_N\to1$) holds for every $Q$ and $b$ (Theorem 5).
2. **Irrationality** follows from the digits alone. A rational element of $K_b$ has an eventually periodic orbit ending in a fixed point (Phase 19). The bulk of the samples concentrates at 0, so a rational $\Theta_Q(1/b)$ would lie in $\mathbb Z[1/b]$, and the positive tails $\tau_n=\sum_{m>n}r_Q(m)b^{n-m}$ would be integers $\ge1$ for all large $n$. But among $n\le X$ at least $X-L\,B_Q(X+L)\ge X/2$ have no support in $(n,n+L]$, and their tails average $\ll b^{-L}$ by Markov. Hence some $\tau_n\in(0,1)$, a contradiction. This argument works for every $F_b(a)$ with $a\ge0$, density-zero support, $A(X)=O(X)$ and infinitely many nonzero terms.
3. **Transcendence** is established, and no novelty is claimed. $\Theta_Q(\tau)$ is a weight-one modular form on $\Gamma_0(|\Delta|)$ with character $\chi_\Delta$ and integer coefficients, and $q=1/b$ corresponds to $\tau=i\log b/(2\pi)$. By Hamieh and Murty (2016, Theorem 3.1), a consequence of Nesterenko's theorem, a nonzero modular form with algebraic Fourier coefficients takes transcendental values at points with $e^{2\pi i\tau}$ algebraic. Since $\Theta_Q(1/b)>1$, it is transcendental. For $\Theta_3$ this goes back to Duverney, Ke. Nishioka, Ku. Nishioka and Shiokawa (1996) and Bertrand (1997). The same corollary gives transcendence of every nonzero value $f(1/b)$ in Theorem B. [Hamieh–Murty, Int. J. Number Theory **12** (2016)][hm] · [Bertrand 1997][bertrand]
4. **Disjunctivity** is a separate question. $\Theta_{m^2+n^2}(1/2)=1+4L_{\chi_4}$, and $4L_{\chi_4}$ has the binary digits of $L_{\chi_4}$ shifted by two places, so it is disjunctive by Phase 17. For a general form and base this is open here. Residue restrictions on the support do **not** by themselves remove any word: every nonzero coefficient spreads over about $\log_b r_Q(j)$ digits, and overlapping neighbours add with carries. The planting argument of Phase 17, §4 needs multiplicativity of $r_Q/w$, which holds for forms of class number one such as $m^2+n^2$, $m^2+mn+n^2$ and $m^2+2n^2$. For $m^2+n^2$ in base $b$ one plants the value $8(2u+1)$ instead of dividing out powers of 2. We have not carried this out.

**A caution on exact constants.** The heuristic for an exact asymptotic is $1-D_N\approx\min_\delta[2\delta+(S(N)/N)(\log_b(1/\delta)+W)]$, where $W$ is the mean **effective width** of a supported coefficient: the number of its base-$b$ digits after removing its trailing zeros. Shifts that read trailing zeros of $r_Q(j)$ stay near 0. Shifts that read its other digits are spread around the circle, as in the $\gamma$-term of $E_b^3$. The optimum $\delta\asymp S(N)/N$ gives $\tfrac12\log_b\log N$ from the first part. In base 2 the representation numbers of $m^2+n^2$ are $4\prod_{p\equiv1\,(4)}(e_p+1)$, almost a power of 2, and $W$ is bounded: the script finds a mean of $0.110$, $0.103$ and $0.096$ for $\log_2(r(j)/2^{v_2(r(j))})$ over the support at $X=2^{12},2^{15},2^{18}$. In base 3 the same quantity is $2.010$, $2.123$, $2.207$; it grows like $\tfrac12\log_3 2\cdot\ln\ln X$, because a typical supported $j$ has about $\tfrac12\ln\ln X$ split prime factors. So a constant depending only on the support density is plausible in base 2 for these forms. In other bases the width term changes the constant: heuristically by the factor $1+\ln2$ for $m^2+n^2$ in base 3. Any exact-constant statement must account for the $b$-adic structure of the coefficients. This remark is heuristic; Theorem 5 and Proposition 6 claim only the order.

### 2.2 Extensions

1. **Integral shifted lattices.** Let $f(m,n)=Q(m,n)+l_1m+l_2n+l_0$ with integer $l_i$. With $U=2cl_1-b_0l_2$, $V=2al_2-b_0l_1$ and $u=U/|\Delta|$, $v=V/|\Delta|$, one has $Q(m+u,n+v)=Q(m,n)+l_1m+l_2n+Q(u,v)$, hence

```math
|\Delta|^2f(m,n)=Q(|\Delta|m+U,\ |\Delta|n+V)+E_0,\qquad E_0=|\Delta|^2l_0-Q(U,V)\in\mathbb Z .
```

Thus the values of $f$ lie in the affine image $(\text{represented}-E_0)/|\Delta|^2$, with count $\le B_Q(|\Delta|^2X+|E_0|)\ll X/\sqrt{\log X}$. The total mass is $\#\{f\le X\}=O(X)$ by area, and the finitely many nonpositive values contribute integers. So $\sum_{m,n}b^{-f(m,n)}\in K_b$ with the same rate.

2. **Rational translates.** For $v=(r/D,s/D)$ the exponents $Q(x+v)$ are not integers. The radix object is the scaled series $\sum_{x\in\mathbb Z^2}b^{-D^2Q(x+v)}=\sum_{(m,n)\equiv(r,s)\,(D)}b^{-Q(m,n)}$, a congruence subsum of $\Theta_Q$. Its coefficients are at most $r_Q(j)$ on the same support, so Theorem 5 applies.

3. **Bounded weights.** For $\chi:\mathbb Z^2\to\mathbb Z$ with $|\chi|\le B$ (characters, signs $(-1)^{m+n}$, congruence conditions), $\sum\chi(m,n)b^{-Q(m,n)}$ has coefficients bounded by $B\,r_Q(j)$ on the same support. Harmonic polynomial weights of degree $\nu\ge1$ are a different matter. They give cusp forms of weight $1+\nu$ with coefficients of size $j^{\nu/2}$, so $A(X)\asymp X^{1+\nu/2}$ and Lemma 1 fails, for the reason explained in §4.

4. **Finite $\mathbb Z[1/b]$-combinations.** $K_b$ is a $\mathbb Z[1/b]$-module, and deficits add after scaling by the integer numerators, plus $j/N$ for division by $b^j$.

Numerically, at $N=2^{18}$ in base 2, $1-D_N(\Theta_Q(1/2))$ equals $0.5840$, $0.7328$, $0.6441$ and $0.5044$ for the four forms above. The ratios to $\log\log N/\sqrt{\log N}$ drift slowly, from $0.94$ to $0.82$ for $m^2+n^2$ between $N=2^{10}$ and $2^{18}$; finite data cannot pin down the exponent. The finite transfer inequality is valid but still vacuous at these $N$ (about $2.0$).

## 3. Weight-one modular forms

**Theorem 7 (= Theorem B).** Let $f=\sum a(n)q^n\in M_1(\Gamma_1(M))$ with $a(n)\in\mathbb Z$. Then $S_f(X)\ll X/(\log X)^{\alpha_f}$ and $A_f(X)\ll X\log X$. Hence $f(1/b)\in K_b$ with $1-D_N\ll\log\log N/(\log N)^{\alpha_f}$.

*Proof.* **Basis.** $M_1(\Gamma_1(M))$ is spanned by the oldforms $g(t\tau)$ of weight-one newforms $g$ of level $M'\mid M$, $t\mid M/M'$, and by the Eisenstein series $E_1^{\psi,\varphi}(t\tau)$ with $\psi\varphi$ odd (Diamond–Shurman, Theorems 4.8.1 and 5.8.3). Write $f$ as a finite combination with algebraic coefficients.

**Newforms.** By Deligne–Serre, $g$ corresponds to an odd irreducible Artin representation $\rho:\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)\to GL_2(\mathbb C)$ with finite image $G$, and $a_g(p)=\operatorname{tr}\rho(\mathrm{Frob}_p)$ for $p\nmid M'$. The Frobenius eigenvalues are roots of unity, so $|a_g(p^e)|\le e+1$; at $p\mid M'$, $|a_g(p)|\le1$. Hence $|a_g(n)|\le\tau(n)$.

Complex conjugation has eigenvalues $1$ and $-1$, so its trace is $0$. Let $P_0(g)$ be the set of primes with trace-zero Frobenius. By Chebotarev it has density $\delta_0(g)=\#\{h\in G:\operatorname{tr}h=0\}/\#G>0$, with the bounded-error harmonic sum supplied by the effective prime ideal theorem for the fixed splitting field. For $p\in P_0(g)$ the recursion $a(p^{e+1})=a(p)a(p^e)-\chi(p)a(p^{e-1})$ kills all odd powers. Thus $\operatorname{supp}a_g\subseteq\{n:v_p(n)\text{ even for all }p\in P_0(g)\}$, a multiplicative set of prime density $1-\delta_0$, of size $\ll x/(\log x)^{\delta_0}$ by Halberstam–Richert. Serre (1981, Théorème 18) gives the exact asymptotic $\sim c\,x/(\log x)^{\lambda}$, where $\lambda=\delta_0$ is the proportion of involutions in the projective image.

**Eisenstein series.** The coefficients are $\sigma(n)=\sum_{d\mid n}\psi(n/d)\varphi(d)$, so $\sigma(p)=\psi(p)(1+\omega(p))$ with $\omega=\varphi\bar\psi$. Since $\psi\varphi$ is odd and $\psi(-1)=\pm1$, $\omega(-1)=-1$. Hence $\omega$ has even order $m$, and $\omega(p)=-1$ on a set of primes of Dirichlet density $1/m$. There $\sigma(p^{2e+1})=\psi(p)^{2e+1}\sum_{i=0}^{2e+1}(-1)^i=0$. So **every weight-one Eisenstein series is lacunary**, with support $\ll x/(\log x)^{1/m}$, and $|\sigma(n)|\le\tau(n)$.

**Combination.** The support of $a_f$ lies in the finite union of the translates $t\cdot\operatorname{supp}$, so $S_f(X)\ll X/(\log X)^{\alpha_f}$, where $\alpha_f$ is the minimum of the $\delta_0(g)$ and the $1/m$. Moreover $|a_f(n)|\le C_f\tau(n)$, so $A_f(X)\ll X\log X$. Since $a(n)\in\mathbb Z$, the heads are integers, and Corollary 2 with $\kappa=\alpha_f$, $\beta=1$ concludes. $\square$

**Does $A(X)=O(X)$ always hold? No, but it does not matter.** By Shiu's theorem with Chebotarev, a newform has $A_g(X)\ll X(\log X)^{\mathbb E|\operatorname{tr}|-1}$, where $\mathbb E|\operatorname{tr}|$ is the mean of $|\operatorname{tr}h|$ over $G$. Since $|\operatorname{tr}|$ is unchanged by scalars, this mean can be computed on the binary polyhedral group lifting the projective image. The script enumerates those groups as unit quaternions:

| projective image | binary group order | $\mathbb E\lvert\mathrm{tr}\rvert$ | $\lambda=P(\mathrm{tr}=0)$ |
|---|---|---|---|
| $D_2$ (Klein four) | 8 | 0.5000 | 0.7500 |
| $D_3$ | 12 | 0.6667 | 0.5000 |
| $D_4$ | 16 | 0.6036 | 0.6250 |
| $D_5$ | 20 | 0.6472 | 0.5000 |
| $D_6$ | 24 | 0.6220 | 0.5833 |
| $A_4$ | 24 | 0.8333 | 0.2500 |
| $S_4$ | 48 | 0.7702 | 0.3750 |
| $A_5$ | 120 | 0.8139 | 0.2500 |

The dihedral values tend to $2/\pi$. Every finite type has $\mathbb E|\operatorname{tr}|<1$, so **every weight-one newform has $A_g(X)=o(X)$.** In contrast, an Eisenstein series $E_1^{\psi,\varphi}$ has $\mathbb E|1+\omega|=\frac1m\sum_j|1+e^{2\pi ij/m}|$, which equals $1$ for $m=2$ (the case of $r_2/4$) and is $1.2071$, $1.2440$, $1.2568$ for $m=4,6,8$, tending to $4/\pi$. For such series $A(X)\asymp X(\log X)^{\mathbb E|1+\omega|-1}$ is not $O(X)$, and integer-coefficient combinations of Galois-conjugate pairs can inherit this. Corollary 2 absorbs any power of $\log X$, so Theorem 7 needs only the trivial bound $A\ll X\log X$.

**Examples.**

- $\Theta_Q$ has $\alpha=1/2$ (genus Eisenstein part with $m=2$, and dihedral cusp part with $\lambda\ge1/2$), recovering Theorem 5.
- $L_\chi(1/b)=\sum(\chi*1)(n)b^{-n}$ for odd real $\chi$ also has $\alpha=1/2$. Its coefficients are integers, so it lies in $K_b$ in every base; Phase 17 treated the binary case with an exact order.
- $E_b^2$ is the progression $n\mapsto c(12n+1)$ of $\eta(12\tau)^2$, of type $D_2$ with $\alpha=3/4$.
- A hypothetical integral form of type $A_4$ or $A_5$ would have $\alpha=1/4$; of type $S_4$, $\alpha=3/8$.

Integrality is used only to make the heads integral. A rational form $f$ with denominator $d$ has $d\,f(1/b)\in K_b$, and $f(1/b)$ itself is then decided by the Phase 19 residue test.

## 4. Serre's lacunary eta powers and the failure at weight two

Let $E_b^r=\sum_na_r(n)b^{-n}$, where $\eta(24\tau)^r=\sum a_r(n)q^{24n+r}$. Serre (1985, Théorème 1) proved that for even $r$, $\eta^r$ is lacunary exactly when $r\in\{2,4,6,8,10,14,26\}$. For odd $r$ only $r=1,3$ are known (Euler and Jacobi), and Serre reports that computations make other odd values improbable. [Serre, Glasgow Math. J. **27** (1985), 203–221][serre85]

- $r=1,2,3$: $E_b$ (weight $\tfrac12$), $E_b^2$ (weight 1) and $E_b^3$ (weight $\tfrac32$) all lie in $K_b$ ([Euler note](euler-product.md)).
- $r\in\{4,6,8,10,14,26\}$, weight $k=r/2\ge2$. These are CM forms, with support $\asymp X/\sqrt{\log X}$ by Serre (1981, Théorème 17). On a positive proportion of split primes the coefficients have size $\asymp p^{(k-1)/2}$: $a(p)=\psi(\pi)+\psi(\bar\pi)$ with $|\psi(\pi)|=p^{(k-1)/2}$, and the angles equidistribute by Hecke. Hence $A(X)\gg X^{(k+1)/2}/(\log X)^{1/2}$, and the Markov term of Lemma 1 is small only if $L\ge\frac{k-1}2\log_bN$. But then $L\,S(N)/N\gg\frac{k-1}2\log_bN/\sqrt{\log N}\to\infty$, so the bound is vacuous.

The obstruction is geometric, not an artefact of the proof. A coefficient at index $m$ occupies a *footprint* of about $\frac{k-1}2\log_bm$ digits to its left. The expected number of other supported indices inside the footprint is about $\frac{k-1}{2\ln b}\cdot c\sqrt{\log m}\to\infty$. Neighbouring coefficients therefore add with carries, and lacunarity of the Fourier coefficients does not prevent overlap of the radix expansions. Weight one is exactly the threshold where $|a(n)|\le\tau(n)=n^{o(1)}$, so the typical footprint is $O(1)$.

The script gives these values, with $N=X=2^{14}$ in base 2:

| $r$ | weight | zero density | $D_N$ | freq(1) | width·density |
|---|---|---|---|---|---|
| 1 | 0.5 | 0.9873 | 0.9094 | 0.4985 | 0 |
| 2 | 1 | 0.6108 | 0.1093 | 0.4932 | 0 |
| 3 | 1.5 | 0.9890 | 0.8380 | 0.4948 | 0.04 |
| 4 | 2 | 0.4294 | 0.0093 | 0.4978 | 3.99 |
| 5 | 2.5 | 0.0015 | 0.0110 | 0.4990 | 10.48 |
| 6 | 3 | 0.5280 | 0.0067 | 0.4990 | 6.61 |
| 8 | 4 | 0.5970 | 0.0143 | 0.4995 | 8.46 |
| 10 | 5 | 0.4108 | 0.0082 | 0.5040 | 16.50 |
| 14 | 7 | 0.4470 | 0.0089 | 0.4980 | 23.23 |
| 26 | 13 | 0.2462 | 0.0093 | 0.4960 | 63.32 |

At $N=2^{18}$, $\sqrt N\,D_N$ is $1.057$ for $r=4$ and $1.254$ for $r=6$, the size expected for independent uniform samples. For $r\ge4$, $E_2^r$ shows no sign of concentration, while $r\le3$ shows $D_N$ near 1. (For $r=2$, $D_N=0.109$ at $2^{14}$ reflects the very slow $\log$-power rate: $1-D_N\to0$ only like $\log\log N/(\log N)^{3/4}$.) The "width·density" column is $\frac{r-2}4\log_2X$ times the support density; it is 0 below weight 1 and grows with the weight. $E_b^5$ is not lacunary in this range: only $0.15\%$ of its first $2^{14}$ coefficients vanish. We conjecture that $E_b^r$ is normal in base $b$ for every $r\ge4$; nothing here proves it.

## 5. Verification

```sh
python -B scripts/phase20_euler_theta.py
```

For this note the script:

- certifies $2^{18}+60$ digits of each $\Theta_Q(1/2)$;
- checks the lattice-point counts, the even-exponent property and Lemma 1 at every reported cutoff;
- computes the effective widths;
- builds the binary dihedral, tetrahedral, octahedral and icosahedral groups as unit quaternions, asserting their orders 8–24, 24, 48 and 120;
- computes $E_2^r$ by the recurrence $nf_n=\sum_ke_k((r+1)k-n)f_{n-k}$, cross-checked against direct products for $r=2,3,4$.

The whole run checks 534,917 assertions and exits 0.

## 6. Lean recommendations and open problems

Lean. The finite transfer with a logarithmic mass,

```lean
theorem finite_sparse_logmass_transfer {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℤ} {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hmass : ∀ X : ℕ, absMass a X ≤ C * X * (Real.log (X + 2)) ^ β)
    {N : ℕ} (hN : 0 < N) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      1 - radixDiscrepancy b (coeffSeries b a) N ≤
        2 * ε + ((L * supportCount a (N + L) : ℕ) : ℝ) / N +
          K * C * (N + L + 2) * (Real.log (N + L + 2)) ^ β / (N * ε * (b : ℝ) ^ L)
```

is a routine extension of `finite_sparse_mass_transfer`. It needs the bound $|a(m)|\le Cm\log^\beta m$ for the tail, which follows from the mass hypothesis. The shifted-lattice identity of §2.2 and the anisotropy lemma behind Lemma 4 are finite algebra suitable for Lean. Bernays, Chebotarev and Deligne–Serre are external inputs and should enter as hypotheses on $S$ and $A$.

Open problems:

1. Exact constants in Theorem 5, including the base-dependent width term above.
2. Disjunctivity of $\Theta_Q(1/b)$ for general $Q$ and $b$.
3. Matching lower bounds for weight-one forms whose constituents cancel on part of the support.
4. Normality of $E_b^r$ for $r\ge4$, and of $\Theta_3(1/b)^3$, which Bailey, Borwein, Crandall and Pomerance (2004, p. 509) already expected to be normal.
5. Whether some positive definite $Q$ and radix $b$ give a non-disjunctive $\Theta_Q(1/b)$.

[hm]: https://doi.org/10.1142/S1793042116500494
[bertrand]: https://doi.org/10.1023/a:1009749608672
[serre85]: https://doi.org/10.1017/S0017089500006194
